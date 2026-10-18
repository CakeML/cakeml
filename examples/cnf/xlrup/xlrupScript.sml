(*
  Specification of an XLRUP checker for CNF + XOR
*)
Theory xlrup
Ancestors
  cnf ccnf syntax_helper xor xlrup_cnf mlstring mlvector sptree
Libs
  preamble

(* The checker state pairs the clause and XOR databases.

  Clauses are indexed by the original variable numbering, but XORs are
  bitstrings indexed by a dense renaming tn of the variables that actually
  occur in an XOR. The two index spaces are related by restore_fn below. *)
Type tname = ``:num sptree$num_map # num``;

Overload isat_xfml = ``satisfies_fml_gen isat_strxor``;

Definition isat_fml_def:
  isat_fml w f (cfml,xfml) ⇔
  satisfies_vcfml w cfml ∧
  isat_xfml (w o f) xfml
End

(* Literal 0 is reserved as the constant summand of an XOR bitstring, so
  neither a clause nor a raw XOR may contain it. *)
Definition nz_ilits_def:
  nz_ilits (C:ilit list) ⇔ ¬ MEM 0 C
End

Definition wf_cfml_def:
  wf_cfml (cfml:num |-> vcclause) ⇔
  ∀C. C ∈ FRANGE cfml ⇒ nz_ilits (toList C)
End

(* For fast parsing, XORs are represented "raw" using int lists *)
Datatype:
  xlrup =
  | Del (num list) (* Clauses to delete *)
  | RUP num vcclause (num list)
    (* RUP n C hints : derive clause C by RUP using hints *)

  | XOrig num cmsxor
    (* XOrig n X : add XOR X from the original formula at ID n *)
  | XAdd num rawxor (num list) (num list)
    (* XAdd n X hints rhints : derive XOR X by adding the XORs at hints,
      then unit propagating with the clauses at rhints *)
  | XDel (num list) (* XORs to delete *)
  | CFromX num cclause (num list)
    (* Derive a clause from hint XORs *)
  | XFromC num rawxor (num list)
    (* Derive an XOR from hint clauses *)
End

(* XOrig lines carry num lits, the rest carry ilits, so the same
  non-zeroness condition appears as EVERY nz_lit and as nz_ilits.
  nz_lit_mk_lit relates the two. *)
Definition wf_xlrup_def:
  (wf_xlrup (RUP n C i0) ⇔ nz_ilits (toList C)) ∧
  (wf_xlrup (CFromX n C i0) ⇔ nz_ilits C) ∧
  (wf_xlrup (XFromC n X i0) ⇔ nz_ilits X) ∧
  (wf_xlrup (XOrig n rX) ⇔ EVERY nz_lit rX) ∧
  (wf_xlrup _ ⇔ T)
End

(* Add together XORs *)
Definition add_xors_aux_def:
  (add_xors_aux fml [] s = SOME s) ∧
  (add_xors_aux fml (i::is) s =
  case FLOOKUP fml i of NONE => NONE
  | SOME x =>
    add_xors_aux fml is (strxor s x))
End

(* Unit propagation of the literal l on an XOR.
  Variables are looked up in the dense renaming t. *)
Definition unit_prop_xor_def:
  unit_prop_xor t s l =
  case lookup (Num (ABS l)) t of NONE => s
  | SOME n =>
  if n < 8 * strlen s then
    if l > 0 then
      (if get_bit s n then
        flip_bit (set_bit s n F) 0
      else s)
    else set_bit s n F
  else s
End

(* Extracts unit clauses in REVERSE order *)
Definition get_units_def:
  (get_units fml [] cs = SOME cs) ∧
  (get_units fml (i::is) cs =
  case FLOOKUP fml i of
    SOME v =>
      if length v = 1
      then get_units fml is (sub v 0::cs)
      else NONE
  | NONE => NONE)
End

Definition unit_props_xor_def:
  unit_props_xor fml t ls s =
  case get_units fml ls [] of NONE => NONE
  | SOME cs =>
    SOME (FOLDL (unit_prop_xor t) s cs)
End

Definition is_xor_def:
  is_xor def fml is cfml cis t s =
  let r = extend_s «» def in
  case add_xors_aux fml is (strxor r s)
    of NONE => F
  | SOME x =>
    case unit_props_xor cfml t cis x of
      NONE => F
    | SOME y => is_emp_xor y
End

Definition conv_rawxor_def:
  conv_rawxor mv x =
  let s = extend_s «» (MAX 1 mv) in
  let s = flip_bit s 0 in
  conv_xor_aux s x
End

Definition strxor_imp_cclause_def:
  strxor_imp_cclause mv s c =
  let t = conv_rawxor mv c in
  is_emp_xor (strxor s t)
End

Definition is_cfromx_def:
  is_cfromx def fml is c =
  let r = extend_s «» def in
  case add_xors_aux fml is r of NONE => F
  | SOME x =>
    strxor_imp_cclause def x c
End

Definition get_constrs_def:
  (get_constrs fml [] = SOME []) ∧
  (get_constrs fml (i::is) =
    case FLOOKUP fml i of
      NONE => NONE
    | SOME Ci =>
      (case get_constrs fml is of NONE => NONE
      | SOME Cs => SOME (toList Ci::Cs)))
End

(* The CNF encoding of an XOR: all clauses with an even number of
  negated literals *)
Definition clauses_from_rawxor_def:
  (clauses_from_rawxor [] b =
    if b then [[]] else []) ∧
  (clauses_from_rawxor (l::ls) b =
    MAP (λxs. l::xs) (clauses_from_rawxor ls b) ++
    MAP (λxs. (-l:int)::xs) (clauses_from_rawxor ls (~b)))
End

(* clause c implies d *)
Definition imp_cclause_def:
  imp_cclause c d ⇔
  EVERY (λl. MEM l d) c
End

Definition check_rawxor_imp_def:
  check_rawxor_imp ds rx =
  let cs = clauses_from_rawxor rx T in
  EVERY (λc. EXISTS (λd. imp_cclause d c) ds) cs
End

Definition is_xfromc_def:
  is_xfromc fml is rx =
  case get_constrs fml is of NONE => F
  | SOME ds =>
    check_rawxor_imp ds rx
End

Definition conv_xor_mv_def:
  conv_xor_mv mv x =
  conv_rawxor mv (MAP to_ilit x)
End

(* The dense renaming *)
Definition get_name_def:
  get_name ((t,n):tname) (v:num) =
  case lookup v t of
    NONE => (n, (insert v n t, n+(1:num)))
  | SOME m => (m, (t,n))
End

Definition ren_int_ls_def:
  (ren_int_ls tn [] (acc:int list) = (REVERSE acc, tn)) ∧
  (ren_int_ls tn (i::is) acc =
    let v = Num (ABS i) in
    let (m,tn) = get_name tn v in
    let vv = if i < (0:int) then -&m else &m in
    ren_int_ls tn is (vv::acc))
End

Definition ren_lit_ls_def:
  (ren_lit_ls tn [] (acc:cmsxor) = (REVERSE acc, tn)) ∧
  (ren_lit_ls tn (i::is) acc =
    case i of
      Pos v =>
      let (m,tn) = get_name tn v in
        ren_lit_ls tn is (Pos m::acc)
    | Neg v =>
      let (m,tn) = get_name tn v in
        ren_lit_ls tn is (Neg m::acc))
End

(* Note: in CFromX, the clause is renamed for checking against the
  XORs, but the original clause is the one stored *)
Definition check_xlrup_def:
  check_xlrup xorig xlrup cfml xfml tn def =
  case xlrup of
    Del cl =>
    SOME (delete_ids cfml cl, xfml, tn, def)
  | RUP n C i0 =>
    if is_rup cfml C i0 then
      SOME (insert_vcc cfml n C, xfml, tn, def)
    else NONE
  | XOrig n rX =>
    if MEM rX xorig
    then
      let (mX,tn) = ren_lit_ls tn rX [] in
      let X = conv_xor_mv def mX in
      SOME (cfml, xfml |+ (n,X), tn, MAX def (strlen X))
    else NONE
  | XAdd n rX i0 i1 =>
    let (mX,tn) = ren_int_ls tn rX [] in
    let X = conv_rawxor def mX in
    if is_xor def xfml i0 cfml i1 (FST tn) X then
      SOME (cfml, xfml |+ (n,X), tn, MAX def (strlen X))
    else NONE
  | XDel xl =>
    SOME (cfml, delete_ids xfml xl, tn, def)
  | CFromX n C i0 =>
    let (mC,tn) = ren_int_ls tn C [] in
    if is_cfromx def xfml i0 mC then
      SOME (insert_vcc cfml n (Vector C), xfml, tn, def)
    else NONE
  | XFromC n rX i0 =>
    if is_xfromc cfml i0 rX then
      let (mX,tn) = ren_int_ls tn rX [] in
      let X = conv_rawxor def mX in
      SOME (cfml, xfml |+ (n,X), tn, MAX def (strlen X))
    else NONE
End

Definition check_xlrups_def:
  (check_xlrups xorig [] cfml xfml tn def =
    SOME (cfml,xfml,tn,def)) ∧
  (check_xlrups xorig (x::xs) cfml xfml tn def =
  case check_xlrup xorig x cfml xfml tn def of
    NONE => NONE
  | SOME (cfml',xfml',tn',def') =>
    check_xlrups xorig xs cfml' xfml' tn' def')
End

Definition check_xlrups_unsat_def:
  check_xlrups_unsat xorig xlrups cfml xfml tn def =
  case check_xlrups xorig xlrups cfml xfml tn def of
    NONE => F
  | SOME (cfml',_) => contains_emp cfml'
End

(*** Proofs ***)

Theorem add_xors_aux_acc:
  ∀is s t.
  add_xors_aux fml is s = SOME t ⇒
  add_xors_aux fml is (strxor s u) = SOME (strxor t u)
Proof
  Induct>>rw[add_xors_aux_def]>>
  gvs[AllCaseEqs()]>>
  qmatch_asmsub_rename_tac`strxor s z`>>
  `strxor (strxor s u) z = strxor (strxor s z) u` by
    metis_tac[strxor_comm,strxor_assoc]>>
  pop_assum SUBST_ALL_TAC>>
  simp[]
QED

Theorem add_xors_aux_imp:
  ∀is s.
  isat_xfml w (FRANGE fml) ∧
  isat_strxor w s ∧
  add_xors_aux fml is s = SOME t ⇒
  isat_strxor w t
Proof
  Induct>>rw[add_xors_aux_def]>>fs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  first_x_assum (irule_at Any)>>
  match_mp_tac isat_strxor_strxor>>
  simp[]>>
  fs[satisfies_fml_gen_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem wf_cfml_delete_ids:
  wf_cfml fml ⇒
  wf_cfml (delete_ids fml ls)
Proof
  rw[wf_cfml_def]>>
  metis_tac[FRANGE_delete_ids_SUBSET,SUBSET_DEF]
QED

Theorem wf_cfml_insert:
  wf_cfml fml ∧ nz_ilits (toList v) ⇒
  wf_cfml (insert_vcc fml n v)
Proof
  rw[wf_cfml_def,insert_vcc_def]>>
  metis_tac[FRANGE_DOMSUB_SUBSET,SUBSET_DEF]
QED

Theorem wf_cfml_check_xlrup:
  wf_cfml cfml ∧ wf_xlrup xlrup ∧
  check_xlrup xorig xlrup cfml xfml tn def =
    SOME (cfml',xfml',tn',def') ⇒
  wf_cfml cfml'
Proof
  rw[check_xlrup_def]>>gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>gvs[]>>
  fs[wf_xlrup_def]>>
  metis_tac[wf_cfml_delete_ids,wf_cfml_insert,toList_thm]
QED

Theorem conv_xor_aux_cclause_sound:
  ∀ls s.
  nz_ilits ls ∧
  isat_strxor w (conv_xor_aux s ls) ⇒
  (isat_strxor w s ∨ satisfies_cclause w ls)
Proof
  Induct>>fs[conv_xor_aux_def]>>rw[]
  >- (
    fs[satisfies_cclause_CONS,nz_ilits_def]>>
    first_x_assum drule>>
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >-
      simp[strlen_extend_s]>>
    simp[isat_strxor_extend_s]>>
    `satisfies_ilit w h = w (Num (ABS h))` by
      (gvs[satisfies_ilit_def]>>AP_TERM_TAC>>intLib.ARITH_TAC)>>
    metis_tac[])>>
  fs[satisfies_cclause_CONS,nz_ilits_def]>>
  first_x_assum drule>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[strlen_extend_s,isat_strxor_extend_s]>>
  CONJ_TAC >- (
    assume_tac (strlen_extend_s |> Q.GEN `a` |> Q.SPEC `Num (ABS h)`)>>
    simp[])>>
  `Num (ABS h) = Num (-h)` by intLib.ARITH_TAC>>
  gvs[satisfies_ilit_def]>>
  metis_tac[]
QED

Theorem strxor_imp_cclause_sound:
  nz_ilits c ∧
  strxor_imp_cclause mv s c ∧
  isat_strxor w s ⇒
  satisfies_cclause w c
Proof
  rw[strxor_imp_cclause_def]>>
  drule isat_strxor_is_emp_xor>>
  disch_then (qspec_then `w` assume_tac)>>
  `isat_strxor w (strxor (conv_rawxor mv c) (strxor s s))` by
    metis_tac[isat_strxor_strxor,strxor_assoc,strxor_comm] >>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[isat_strxor_add_is_emp_xor]>>simp[strxor_self]>>
  rw[conv_rawxor_def]>>
  drule conv_xor_aux_cclause_sound>>
  disch_then drule>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[isat_strxor_extend_s]>>
  CONJ_TAC>-
    rw[extend_s_def]>>
  EVAL_TAC
QED

Theorem is_cfromx_sound:
  nz_ilits C ∧
  isat_xfml w (FRANGE fml) ∧
  is_cfromx def fml is C ⇒
  satisfies_cclause w C
Proof
  rw[is_cfromx_def]>>
  every_case_tac>>fs[]>>
  match_mp_tac (GEN_ALL strxor_imp_cclause_sound)>>
  fs[]>>
  first_x_assum (irule_at Any)>>
  drule add_xors_aux_imp>>
  disch_then match_mp_tac>>
  first_x_assum (irule_at Any)>>
  simp[isat_strxor_extend_s]>>
  EVAL_TAC
QED

Theorem isat_strxor_conv_xor_aux:
  isat_strxor w (conv_xor s (MAP mk_lit ls)) ⇒
  isat_strxor w (conv_xor_aux s ls)
Proof
  rw[conv_xor_def,MAP_MAP_o,o_DEF,to_ilit_mk_lit]
QED

Theorem clauses_from_rawxor_sound:
  ∀rx b.
  nz_ilits rx ∧
  EVERY (satisfies_cclause w)
    (clauses_from_rawxor rx b) ⇒
  (sat_cmsxor w (MAP mk_lit rx) ⇔ b)
Proof
  Induct>>rw[clauses_from_rawxor_def]
  >-
    fs[sat_cmsxor_def,satisfies_cclause_def]
  >-
    fs[sat_cmsxor_def,satisfies_cclause_def]>>
  gvs[EVERY_MAP,satisfies_cclause_CONS,nz_ilits_def]>>
  `satisfies_lit w (mk_lit h) = satisfies_ilit w h` by
    metis_tac[satisfies_lit_mk_lit]>>
  Cases_on`satisfies_ilit w h`>>fs[]
  >- (
    gvs[satisfies_ilit_neg]>>
    first_x_assum(qspec_then`~b` mp_tac)>>
    simp[]>>
    metis_tac[ETA_AX])>>
  first_x_assum(qspec_then`b` mp_tac)>>
  metis_tac[ETA_AX]
QED

Theorem imp_cclause_imp:
  imp_cclause c d ∧
  satisfies_cclause w c ⇒
  satisfies_cclause w d
Proof
  rw[imp_cclause_def,satisfies_cclause_def,EVERY_MEM]>>
  metis_tac[]
QED

Theorem satisfies_vcfml_get_constrs:
  ∀is xs x.
  satisfies_vcfml w (FRANGE fml) ∧
  get_constrs fml is = SOME xs ∧
  MEM x xs ⇒
  satisfies_cclause w x
Proof
  Induct>>rw[get_constrs_def]>>
  gvs[AllCaseEqs()]>>
  fs[satisfies_vcfml_def,satisfies_fml_gen_def,
    satisfies_vcclause_def,IN_FRANGE_FLOOKUP,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem is_xfromc_sound:
  nz_ilits rX ∧
  satisfies_vcfml w (FRANGE fml) ∧
  is_xfromc fml is rX ⇒
  sat_cmsxor w (MAP mk_lit rX)
Proof
  rw[is_xfromc_def]>>
  gvs[AllCasePreds()]>>
  qspecl_then [`rX`,`T`] mp_tac clauses_from_rawxor_sound>>
  simp[]>>
  disch_then match_mp_tac>>
  fs[check_rawxor_imp_def,EVERY_MEM]>>
  rw[]>>first_x_assum drule>>
  rw[EXISTS_MEM]>>
  metis_tac[satisfies_vcfml_get_constrs,imp_cclause_imp]
QED

(*** The dense renaming and its inverse ***)

Definition tn_inv_def:
  tn_inv ((t,n):tname) ⇔
    0 < n ∧ ∀i v. lookup i t = SOME v ⇒ v ≠ 0:num ∧ v < n ∧
    (∀n1 n2 k.
       lookup n1 t = SOME k ∧
       lookup n2 t = SOME k ⇒ n1 = n2)
End

Definition restore_fn_def:
  restore_fn ((t,n):tname) v =
    case (some k. lookup k t = SOME v) of
    | NONE => 0
    | SOME k => k
End

Definition restore_lit_def:
  restore_lit tn (Pos n) = Pos (restore_fn tn n) ∧
  restore_lit tn (Neg n) = Neg (restore_fn tn n)
End

Definition restore_int_def:
  restore_int tn i =
  if i > 0
  then
    (&restore_fn tn (Num (ABS i))):int
  else
    -&restore_fn tn (Num (ABS i))
End

Definition can_restore_def:
  can_restore ((t,n):tname) v ⇔ ∃k. lookup k t = SOME (v:num)
End

Definition can_restore_lit_def:
  (can_restore_lit tn (Pos n) ⇔ can_restore tn n) ∧
  (can_restore_lit tn (Neg n) ⇔ can_restore tn n)
End

Definition can_restore_int_def:
  can_restore_int tn i ⇔ can_restore tn (Num (ABS i))
End

Definition tn_submap_def:
  tn_submap tn tn' ⇔
    (∀k. can_restore tn k ⇒
         can_restore tn' k ∧
         restore_fn tn' k = restore_fn tn k)
End

Definition can_restore_str_def:
  can_restore_str tn (s:strxor) ⇔
    ∀i. i ≠ 0 ∧ i < LENGTH (string_to_bits s) ∧
        EL i (string_to_bits s) ⇒
        can_restore tn i
End

Theorem tn_submap_refl:
  tn_submap tn tn
Proof
  gvs [tn_submap_def]
QED

Theorem tn_submap_trans:
  tn_submap tn1 tn2 ∧ tn_submap tn2 tn3 ⇒ tn_submap tn1 tn3
Proof
  gvs [tn_submap_def]
QED

Theorem tn_inv_get_name:
  get_name tn n = (m,tn') ∧ tn_inv tn ⇒
  m ≠ 0 ∧
  tn_inv tn' ∧
  can_restore tn' m ∧
  restore_fn tn' m = n ∧
  tn_submap tn tn'
Proof
  PairCases_on ‘tn’>>
  gvs [get_name_def,AllCaseEqs(),tn_inv_def,tn_submap_def]>>rw []>>
  gvs [tn_inv_def,lookup_insert,can_restore_def,tn_submap_def]>>rw []>>
  res_tac>>gvs [restore_fn_def,tn_submap_def,lookup_insert]
  >-
   (CCONTR_TAC>>
    Cases_on ‘n1 = i’>>gvs []>>
    Cases_on ‘n2 = i’>>gvs []>>
    res_tac>>gvs [])
  >-
   (CCONTR_TAC>>
    Cases_on ‘n1 = n’>>gvs []>>
    Cases_on ‘n2 = n’>>gvs []>>
    res_tac>>gvs [])
  >- metis_tac []
  >- (DEEP_INTRO_TAC some_intro>>fs []>>rw []
      >- (Cases_on ‘lookup x tn0’>>gvs []>>res_tac>>gvs [])>>
      gvs [AllCaseEqs()]>>metis_tac [])
  >- (simp [AllCaseEqs()]>>metis_tac [optionTheory.NOT_NONE_SOME])
  >-
   (DEEP_INTRO_TAC some_intro>>fs []>>rw []
    >- (DEEP_INTRO_TAC some_intro>>fs []>>rw []>>
        gvs [AllCaseEqs()]>>metis_tac [])>>
    DEEP_INTRO_TAC some_intro>>fs []>>rw []>>
    CCONTR_TAC>>Cases_on ‘x = n’>>gvs []>>metis_tac [])
  >- metis_tac []
  >-
    (DEEP_INTRO_TAC some_intro>>fs []>>rw []>>
     res_tac>>gvs [])>>
  metis_tac []
QED

Theorem ren_lit_ls_nz_lit:
  ∀tn xs acc ys tn'.
    ren_lit_ls tn xs acc = (ys,tn') ∧ EVERY nz_lit xs ∧
    EVERY nz_lit acc ∧ tn_inv tn ⇒
    EVERY nz_lit ys
Proof
  Induct_on ‘xs’>>gvs [ren_lit_ls_def]>>
  Cases>>fs [ren_lit_ls_def]>>rw []>>
  pairarg_tac>>gvs []>>
  first_x_assum $ drule_then $ irule>>gvs []>>
  drule tn_inv_get_name>>gvs []
QED

Theorem ren_lit_ls_tn_inv:
  ∀tn xs acc ys tn'.
    ren_lit_ls tn xs acc = (ys,tn') ∧ tn_inv tn ⇒
    tn_inv tn'
Proof
  Induct_on ‘xs’>>gvs [ren_lit_ls_def]>>
  Cases>>fs [ren_lit_ls_def]>>rw []>>
  pairarg_tac>>gvs []>>
  first_x_assum $ drule_then $ irule>>gvs []>>
  drule tn_inv_get_name>>gvs []
QED

Theorem every_can_restore_lit_submap:
  tn_submap tn tn' ∧
  EVERY (can_restore_lit tn) acc ⇒
  EVERY (can_restore_lit tn') acc
Proof
  Induct_on ‘acc’>>fs []>>
  Cases>>fs [can_restore_lit_def]>>
  gvs [tn_submap_def]
QED

Theorem ren_lit_ls_restore_acc:
  ∀tn xs acc ys tn'.
    ren_lit_ls tn xs acc = (ys,tn') ∧ tn_inv tn ∧
    EVERY (can_restore_lit tn) acc
    ⇒
    MAP (restore_lit tn') ys = MAP (restore_lit tn') (REVERSE acc) ++ xs ∧
    EVERY (can_restore_lit tn') ys ∧
    tn_submap tn tn'
Proof
  Induct_on ‘xs’>>
  fs [ren_lit_ls_def,tn_submap_refl]>>
  Cases>>gvs []>>rpt gen_tac>>strip_tac>>
  pairarg_tac>>gvs []>>
  last_x_assum drule>>
  drule_all tn_inv_get_name>>strip_tac>>gvs []>>
  gvs [can_restore_lit_def,restore_lit_def]>>
  drule_all every_can_restore_lit_submap>>fs []>>
  gvs [tn_submap_trans,SF SFY_ss]>>gvs [tn_submap_def]
QED

Theorem ren_lit_ls_restore:
  ∀tn xs ys tn'.
    ren_lit_ls tn xs [] = (ys,tn') ∧ tn_inv tn ⇒
    MAP (restore_lit tn') ys = xs ∧
    EVERY (can_restore_lit tn') ys ∧
    tn_submap tn tn'
Proof
  rpt gen_tac>>strip_tac>>
  drule ren_lit_ls_restore_acc>>fs []
QED

Theorem ren_int_ls_tn_inv:
  ∀tn xs acc ys tn'.
    ren_int_ls tn xs acc = (ys,tn') ∧ tn_inv tn ⇒
    tn_inv tn'
Proof
  Induct_on ‘xs’>>gvs [ren_int_ls_def]>>
  Cases>>fs [ren_int_ls_def]>>rw []>>
  pairarg_tac>>gvs []>>
  first_x_assum $ drule_then $ irule>>gvs []>>
  drule tn_inv_get_name>>gvs []
QED

Theorem every_can_restore_int_submap:
  tn_submap tn tn' ∧
  EVERY (can_restore_int tn) acc ⇒
  EVERY (can_restore_int tn') acc
Proof
  Induct_on ‘acc’>>fs []>>
  Cases>>fs [can_restore_int_def]>>
  gvs [tn_submap_def]
QED

Theorem restore_int_simps:
  m ≠ 0 ⇒
  restore_int tn (&m) = &restore_fn tn m ∧
  restore_int tn (-&m) = -&restore_fn tn m
Proof
  rw[restore_int_def]>>
  intLib.ARITH_TAC
QED

Theorem ren_int_ls_restore_acc:
  ∀tn xs acc ys tn'.
    ren_int_ls tn xs acc = (ys,tn') ∧ tn_inv tn ∧
    EVERY (can_restore_int tn) acc
    ⇒
    MAP (restore_int tn') ys =
      MAP (restore_int tn') (REVERSE acc) ++ xs ∧
    EVERY (can_restore_int tn') ys ∧
    tn_submap tn tn'
Proof
  Induct_on ‘xs’>>
  fs [ren_int_ls_def,tn_submap_refl]>>
  Cases>>gvs []>>rpt gen_tac>>strip_tac>>
  pairarg_tac>>gvs []>>
  last_x_assum drule>>
  drule_all tn_inv_get_name>>
  strip_tac>>gvs []>>
  gvs [can_restore_int_def,can_restore_def,restore_fn_def,o_DEF,
          GSYM EVERY_MAP]>>
  drule_all every_can_restore_int_submap>>fs []>>
  drule restore_int_simps>>
  gvs [tn_submap_trans,SF SFY_ss]>>gvs [tn_submap_def]
QED

Theorem ren_int_ls_restore:
  ∀tn xs ys tn'.
    ren_int_ls tn xs [] = (ys,tn') ∧ tn_inv tn ⇒
    MAP (restore_int tn') ys = xs ∧
    EVERY (can_restore_int tn') ys ∧
    tn_submap tn tn'
Proof
  rpt gen_tac>>strip_tac>>
  drule ren_int_ls_restore_acc>>fs []
QED

Theorem ren_int_ls_nz_ilits:
  ∀tn xs acc ys tn'.
    ren_int_ls tn xs acc = (ys,tn') ∧ nz_ilits xs ∧
    nz_ilits acc ∧ tn_inv tn ⇒
    nz_ilits ys
Proof
  Induct_on ‘xs’>>gvs [ren_int_ls_def,nz_ilits_def]>>
  Cases>>fs [ren_int_ls_def]>>rw []>>
  pairarg_tac>>gvs []>>
  first_x_assum $ drule_then $ irule>>gvs []>>
  drule tn_inv_get_name>>gvs []
QED

Theorem can_restore_str_flip_bit_0:
  can_restore_str tn s ⇒
  can_restore_str tn (flip_bit s 0)
Proof
  rw[can_restore_str_def,flip_bit_def]>>
  gvs[string_to_bits_set_bit,EL_LUPDATE]
QED

Theorem can_restore_str_flip_bit:
  n < LENGTH (string_to_bits s) ∧
  can_restore_str tn s ∧
  can_restore tn n ⇒
  can_restore_str tn (flip_bit s n)
Proof
  rw[can_restore_str_def,flip_bit_def]>>
  gvs[string_to_bits_set_bit,EL_LUPDATE]>>
  every_case_tac>>fs[]
QED

Theorem can_restore_str_extend_s:
  can_restore_str tn s ⇒
  can_restore_str tn (extend_s s n)
Proof
  rw[can_restore_str_def,string_to_bits_extend_s,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  qpat_x_assum`EL _ _` mp_tac>>
  DEP_REWRITE_TAC[EL_REPLICATE]>>
  fs[extend_s_def]>>
  every_case_tac>>fs[]
QED

Theorem can_restore_str_conv_xor_aux:
  ∀ls tn s.
  can_restore_str tn s ∧
  EVERY (can_restore tn) (MAP (λl. Num (ABS l)) ls)
  ⇒
  can_restore_str tn (conv_xor_aux s ls)
Proof
  Induct>>rw[conv_xor_aux_def]>>
  first_x_assum match_mp_tac>>simp[]
  >- (
    match_mp_tac can_restore_str_flip_bit>>
    simp[can_restore_str_extend_s,strlen_extend_s])>>
  match_mp_tac can_restore_str_flip_bit_0>>
  match_mp_tac can_restore_str_flip_bit>>
  simp[strlen_extend_s,can_restore_str_extend_s]
QED

Theorem can_restore_str_conv_xor_mv:
  EVERY (can_restore_lit tn) mX ⇒
  can_restore_str tn (conv_xor_mv def mX)
Proof
  rw[conv_xor_mv_def, conv_rawxor_def]>>
  match_mp_tac can_restore_str_conv_xor_aux>>
  rw[]
  >- (
    match_mp_tac can_restore_str_flip_bit_0>>
    match_mp_tac can_restore_str_extend_s>>
    EVAL_TAC>>rw[])>>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>rw[]>>
  first_x_assum drule>>
  Cases_on`y`>>fs[to_ilit_def,can_restore_lit_def]
QED

Theorem can_restore_str_conv_rawxor:
  EVERY (can_restore tn) (MAP (λl. Num (ABS l)) mX) ⇒
  can_restore_str tn (conv_rawxor def mX)
Proof
  rw[conv_rawxor_def]>>
  match_mp_tac can_restore_str_conv_xor_aux>>
  rw[]>>
  match_mp_tac can_restore_str_flip_bit_0>>
  match_mp_tac can_restore_str_extend_s>>
  EVAL_TAC>>rw[]
QED

Theorem sat_cmsxor_restore_fn:
  sat_cmsxor (w ∘ restore_fn tn) mX = sat_cmsxor w (MAP (restore_lit tn) mX)
Proof
  fs [sat_cmsxor_def,GSYM MAP_MAP_o]>>
  rpt AP_TERM_TAC>>
  Induct_on ‘mX’>>fs []>>
  Cases>>gvs [restore_lit_def,satisfies_lit_def]
QED

Theorem can_restore_str_submap:
  tn_submap tn tn' ∧ can_restore_str tn s ⇒ can_restore_str tn' s
Proof
  fs [can_restore_str_def,tn_submap_def]
QED

Theorem isat_strxor_restore_str_submap:
  tn_submap tn tn' ∧
  can_restore_str tn C ∧
  isat_strxor (w ∘ restore_fn tn) C ⇒
  isat_strxor (w ∘ restore_fn tn') C
Proof
  gvs [isat_strxor_def,sum_bitlist_alt]>>rw []>>
  pop_assum mp_tac>>
  pop_assum mp_tac>>
  rewrite_tac [can_restore_str_def]>>
  qabbrev_tac ‘x = string_to_bits C’>>
  rw []>>
  pop_assum mp_tac>>
  match_mp_tac (METIS_PROVE [] “b = x ⇒ (b ⇒ x)”)>>
  AP_TERM_TAC>>
  AP_TERM_TAC>>
  pop_assum mp_tac>>
  pop_assum kall_tac>>
  Induct_on ‘x’ using SNOC_INDUCT >- gvs []>>
  gvs [SNOC_APPEND,indexedListsTheory.MAPi_APPEND]>>
  rw []
  >-
   (first_x_assum irule>>rw []>>first_x_assum irule>>fs []>>
    metis_tac [rich_listTheory.EL_APPEND1])>>
  first_x_assum $ qspec_then ‘LENGTH x’ mp_tac>>
  gvs [rich_listTheory.EL_LENGTH_APPEND]>>
  Cases_on`x`>>simp[]>>
  gvs [tn_submap_def,SF CONJ_ss]
QED

Theorem isat_xfml_restore_str_submap:
  tn_submap tn tn' ∧
  (∀s. s ∈ FRANGE xfml ⇒ can_restore_str tn s) ∧
  isat_xfml (w ∘ restore_fn tn) (FRANGE xfml) ⇒
  isat_xfml (w ∘ restore_fn tn') (FRANGE xfml)
Proof
  rw[satisfies_fml_gen_def]>>
  match_mp_tac isat_strxor_restore_str_submap>>
  metis_tac[]
QED

Theorem unit_prop_xor_sound:
  tn_inv (t,n) ∧
  satisfies_ilit w l ⇒
  (isat_strxor (w o restore_fn (t,n)) (unit_prop_xor t X l) ⇔
    isat_strxor (w o restore_fn (t,n)) X)
Proof
  rw[unit_prop_xor_def]>>
  TOP_CASE_TAC>>fs[]>>
  qmatch_goalsub_rename_tac`v < 8 * strlen X`>>
  `restore_fn (t,n) v = Num (ABS l) ∧ v ≠ 0` by
    (simp[restore_fn_def]>>
    DEEP_INTRO_TAC some_intro>>fs[tn_inv_def]>>
    rw[]>>first_x_assum drule>>
    metis_tac[])>>
  rw[]>>
  gs[satisfies_ilit_ABS]
  >- (
    DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
    CONJ_TAC >- (
      rw[set_bit_def,set_char_def]>>
      intLib.ARITH_TAC)>>
    fs[isat_strxor_def]>>
    DEP_REWRITE_TAC[string_to_bits_set_bit,sum_bitlist_LUPDATE]>>
    fs[get_bit_string_to_bits,of_bool_def]>>
    DEP_REWRITE_TAC [EVEN_SUB]>>
    simp[sum_bitlist_alt]>>
    match_mp_tac SUM_MEM_bound>>
    simp[MEM_MAPi]>>
    asm_exists_tac>>simp[of_bool_def])>>
  fs[isat_strxor_def]>>
  DEP_REWRITE_TAC[string_to_bits_set_bit,sum_bitlist_LUPDATE]>>
  fs[get_bit_string_to_bits,of_bool_def]
QED

Theorem get_units_sound:
  ∀ls cs.
  satisfies_vcfml w (FRANGE fml) ∧
  EVERY (satisfies_ilit w) cs ∧
  get_units fml ls cs = SOME cs' ⇒
  EVERY (satisfies_ilit w) cs'
Proof
  Induct>>rw[get_units_def]>>gvs[AllCaseEqs()]>>
  first_x_assum irule>>
  first_x_assum (irule_at Any)>>
  gvs[satisfies_vcfml_def,satisfies_fml_gen_def,
    IN_FRANGE_FLOOKUP,PULL_EXISTS]>>
  first_x_assum drule>>
  simp[satisfies_vcclause_length_1]
QED

Theorem unit_props_xor_sound:
  ∀is X Y.
  tn_inv (t,n) ∧
  satisfies_vcfml w (FRANGE fml) ∧
  unit_props_xor fml t is X = SOME Y ⇒
  (isat_strxor (w ∘ restore_fn (t,n)) X ⇔
    isat_strxor (w ∘ restore_fn (t,n)) Y)
Proof
  rw[unit_props_xor_def]>>
  gvs[AllCaseEqs()]>>
  drule get_units_sound>>
  disch_then (drule_at Any)>>
  simp[]>>
  pop_assum kall_tac>>
  qid_spec_tac`cs`>>
  ho_match_mp_tac SNOC_INDUCT>>rw[]>>
  gvs[EVERY_SNOC,FOLDL_SNOC]>>
  match_mp_tac (GSYM unit_prop_xor_sound)>>
  gvs[]
QED

Theorem is_xor_sound:
  tn_inv tn ∧
  isat_xfml (w ∘ restore_fn tn) (FRANGE fml) ∧
  satisfies_vcfml w (FRANGE cfml) ∧
  is_xor def fml is cfml cis (FST tn) X ⇒
  isat_strxor (w ∘ restore_fn tn) X
Proof
  rw[is_xor_def]>>
  every_case_tac>>fs[]>>
  qmatch_asmsub_rename_tac`add_xors_aux fml is _ = SOME sx`>>
  drule add_xors_aux_acc>>
  disch_then (qspec_then `strxor (extend_s «» def) X` assume_tac)>>
  drule add_xors_aux_imp>>
  disch_then (drule_at Any)>>
  impl_tac >-
    metis_tac[isat_strxor_is_emp_xor,strxor_self]>>
  `isat_strxor (w ∘ restore_fn tn) sx` by
    (Cases_on`tn`>>fs[]>>
    drule_all unit_props_xor_sound>>
    metis_tac[isat_strxor_is_emp_xor])>>
  strip_tac>>
  `is_emp_xor (extend_s «» def)` by
    rw[extend_s_def,is_emp_xor_def]>>
  `isat_strxor (w ∘ restore_fn tn)
    (strxor (strxor sx sx) (strxor (extend_s «» def) X))` by
    (simp[strxor_assoc]>>
    match_mp_tac isat_strxor_strxor>>simp[])>>
  metis_tac[isat_strxor_add_is_emp_xor,strxor_comm,
    isat_strxor_extend_s,strxor_self]
QED

Theorem satisfies_cclause_restore_fn:
  nz_ilits (MAP (restore_int tn) mC) ∧
  satisfies_cclause (w ∘ restore_fn tn) mC ⇒
  satisfies_cclause w (MAP (restore_int tn) mC)
Proof
  rw[satisfies_cclause_def,MEM_MAP,PULL_EXISTS]>>
  first_assum (irule_at Any)>>
  `restore_int tn i ≠ 0` by
    (fs[nz_ilits_def,MEM_MAP]>>metis_tac[])>>
  gvs[satisfies_ilit_ABS,restore_int_def]>>
  qabbrev_tac`r = restore_fn tn (Num (ABS i))`>>
  `Num (ABS (&r:int)) = r ∧ Num (ABS (-&r:int)) = r` by
    intLib.ARITH_TAC>>
  Cases_on`i > 0`>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem sat_cmsxor_restore_fn_2:
  nz_ilits (MAP (restore_int tn) mX) ∧
  sat_cmsxor w (MAP mk_lit (MAP (restore_int tn) mX)) ⇒
  sat_cmsxor (w ∘ restore_fn tn) (MAP mk_lit mX)
Proof
  rw[sat_cmsxor_restore_fn]>>
  qsuff_tac`MAP (restore_lit tn) (MAP mk_lit mX) =
    MAP mk_lit (MAP (restore_int tn) mX)`
  >- (rw[]>>gvs[])>>
  simp[MAP_MAP_o,MAP_EQ_f]>>rw[]>>
  `restore_int tn e ≠ 0` by
    (fs[nz_ilits_def,MEM_MAP]>>metis_tac[])>>
  Cases_on`e > 0`>>
  gvs[mk_lit_def,restore_int_def,restore_lit_def]>>
  rw[]>>
  `F` by intLib.ARITH_TAC
QED

(*** Soundness of the checker ***)

Theorem check_xlrup_sound:
  wf_xlrup xlrup ∧
  wf_cfml cfml ∧
  check_xlrup xorig xlrup cfml xfml tn def =
    SOME (cfml',xfml',tn',def') ∧ tn_inv tn ∧
  satisfies_xfml w (set xorig) ∧
  (∀s. s ∈ FRANGE xfml ⇒ can_restore_str tn s) ∧
  isat_fml w (restore_fn tn) (FRANGE cfml, FRANGE xfml)
  ⇒
  (∀s. s ∈ FRANGE xfml' ⇒ can_restore_str tn' s) ∧
  isat_fml w (restore_fn tn') (FRANGE cfml', FRANGE xfml')
Proof
  simp[check_xlrup_def]>>strip_tac>>
  gvs[AllCaseEqs()]
  >- suspend "Del"
  >- suspend "RUP"
  >- suspend "XOrig"
  >- suspend "XAdd"
  >- suspend "XDel"
  >- suspend "CFromX"
  >- suspend "XFromC"
QED

Resume check_xlrup_sound[Del]:
  fs[isat_fml_def,satisfies_vcfml_def]>>
  metis_tac[satisfies_fml_gen_delete_ids]
QED

Resume check_xlrup_sound[RUP]:
  qmatch_asmsub_rename_tac`is_rup cfml C i0`>>
  gvs[isat_fml_def]>>
  `satisfies_vcclause w C` by
    metis_tac[is_rup_sound]>>
  fs[satisfies_vcfml_def,insert_vcc_def]>>
  metis_tac[SRULE [] satisfies_fml_gen_insert]
QED

Resume check_xlrup_sound[XOrig]:
  pairarg_tac>>gvs[]>>
  drule_all ren_lit_ls_restore>>strip_tac>>gvs[]>>
  fs[isat_fml_def,PULL_EXISTS]>>
  CONJ_ASM1_TAC >- (
    rw[]
    >- (
      match_mp_tac can_restore_str_conv_xor_mv>>
      simp[])>>
    gvs[IN_FRANGE_FLOOKUP,DOMSUB_FLOOKUP_THM]>>
    metis_tac[can_restore_str_submap])>>
  `isat_strxor (w ∘ restore_fn tn') (conv_xor_mv def mX)` by (
    drule_all satisfies_xfml_MEM>>
    strip_tac>>
    gvs[wf_xlrup_def]>>
    rw[conv_xor_mv_def,conv_rawxor_def,GSYM conv_xor_def]>>
    DEP_REWRITE_TAC [conv_xor_sound, isat_strxor_flip_bit]>>
    simp[isat_strxor_extend_s]>>
    drule ren_lit_ls_nz_lit>>
    rw[]
    >- (EVAL_TAC>>simp[MAX_DEF])>>
    simp[isat_strxor_def,string_to_bits_def,sum_bitlist_def,
      sat_cmsxor_restore_fn])>>
  `isat_xfml (w ∘ restore_fn tn') (FRANGE xfml)` by
    metis_tac[isat_xfml_restore_str_submap]>>
  metis_tac[SRULE [] satisfies_fml_gen_insert]
QED

Resume check_xlrup_sound[XAdd]:
  pairarg_tac>>gvs[]>>
  fs[isat_fml_def]>>
  drule ren_int_ls_restore>>strip_tac>>gvs[]>>
  CONJ_ASM1_TAC >- (
    rw[]
    >- (
      match_mp_tac can_restore_str_conv_rawxor>>
      gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,can_restore_int_def])>>
    gvs[IN_FRANGE_FLOOKUP,DOMSUB_FLOOKUP_THM]>>
    metis_tac[can_restore_str_submap])>>
  `isat_xfml (w ∘ restore_fn tn') (FRANGE xfml)` by
    metis_tac[isat_xfml_restore_str_submap]>>
  `tn_inv tn'` by
    metis_tac[ren_int_ls_tn_inv]>>
  `isat_strxor (w ∘ restore_fn tn') (conv_rawxor def mX)` by
    metis_tac[is_xor_sound]>>
  metis_tac[SRULE [] satisfies_fml_gen_insert]
QED

Resume check_xlrup_sound[XDel]:
  fs[isat_fml_def,satisfies_vcfml_def]>>
  CONJ_TAC >-
    metis_tac[FRANGE_delete_ids_SUBSET,SUBSET_DEF]>>
  metis_tac[satisfies_fml_gen_delete_ids]
QED

Resume check_xlrup_sound[CFromX]:
  pairarg_tac>>gvs[]>>
  fs[isat_fml_def,wf_xlrup_def]>>
  drule ren_int_ls_restore>>strip_tac>>gvs[]>>
  `isat_xfml (w ∘ restore_fn tn') (FRANGE xfml)` by
    metis_tac[isat_xfml_restore_str_submap]>>
  `nz_ilits ([]:ilit list)` by
    simp[nz_ilits_def]>>
  `nz_ilits mC` by
    metis_tac[ren_int_ls_nz_ilits]>>
  `satisfies_cclause (w ∘ restore_fn tn') mC` by
    metis_tac[is_cfromx_sound]>>
  `satisfies_cclause w (MAP (restore_int tn') mC)` by
    metis_tac[satisfies_cclause_restore_fn]>>
  CONJ_TAC >- (
    rw[]>>
    metis_tac[can_restore_str_submap])>>
  `satisfies_vcclause w (Vector (MAP (restore_int tn') mC))` by
    simp[satisfies_vcclause_def,toList_thm]>>
  fs[satisfies_vcfml_def,insert_vcc_def]>>
  metis_tac[SRULE [] satisfies_fml_gen_insert]
QED

Resume check_xlrup_sound[XFromC]:
  fs[isat_fml_def]>>
  pairarg_tac>>gvs[]>>
  drule ren_int_ls_restore>>strip_tac>>gvs[]>>
  fs[wf_xlrup_def]>>
  `nz_ilits ([]:ilit list)` by
    simp[nz_ilits_def]>>
  `nz_ilits mX` by
    metis_tac[ren_int_ls_nz_ilits]>>
  `isat_xfml (w ∘ restore_fn tn') (FRANGE xfml)` by
    metis_tac[isat_xfml_restore_str_submap]>>
  `sat_cmsxor (w ∘ restore_fn tn') (MAP mk_lit mX)` by
    metis_tac[is_xfromc_sound,sat_cmsxor_restore_fn_2]>>
  `EVERY nz_lit (MAP mk_lit mX)` by (
    gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,nz_ilits_def]>>
    metis_tac[nz_lit_mk_lit])>>
  qsuff_tac`isat_strxor (w ∘ restore_fn tn') (conv_rawxor def mX)`
  >- (
    strip_tac>>
    CONJ_TAC >- (
      rw[]
      >- (
        match_mp_tac can_restore_str_conv_rawxor>>
        gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,can_restore_int_def])>>
      gvs[IN_FRANGE_FLOOKUP,DOMSUB_FLOOKUP_THM]>>
      metis_tac[can_restore_str_submap])>>
    metis_tac[SRULE [] satisfies_fml_gen_insert])>>
  rw[conv_rawxor_def]>>
  match_mp_tac isat_strxor_conv_xor_aux>>
  DEP_REWRITE_TAC[conv_xor_sound]>>
  simp[]>>
  DEP_REWRITE_TAC[isat_strxor_flip_bit]>>
  simp[isat_strxor_extend_s]>>
  CONJ_TAC >- (EVAL_TAC>>rw[])>>
  EVAL_TAC
QED

Finalise check_xlrup_sound;

Theorem check_xlrup_tn_inv:
  check_xlrup xorig xlrup cfml xfml tn def =
    SOME (cfml',xfml',tn',def') ∧ tn_inv tn ⇒
  tn_inv tn'
Proof
  rw[check_xlrup_def]>>
  gvs[AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs [])
  >- (drule ren_lit_ls_tn_inv>>fs [])>>
  drule ren_int_ls_tn_inv>>fs []
QED

(* The main operational theorem about check_xlrups *)
Theorem check_xlrups_sound:
  ∀ls cfml xfml def def' tn tn'.
  EVERY wf_xlrup ls ∧ wf_cfml cfml ∧ tn_inv tn ∧
  check_xlrups xorig ls cfml xfml tn def =
    SOME (cfml', xfml', tn', def') ∧
  (∀s. s ∈ FRANGE xfml ⇒ can_restore_str tn s) ∧
  satisfies_xfml w (set xorig) ⇒
  (isat_fml w (restore_fn tn) (FRANGE cfml, FRANGE xfml) ⇒
   isat_fml w (restore_fn tn') (FRANGE cfml', FRANGE xfml'))
Proof
  Induct>>simp[check_xlrups_def]>>
  rw[]>>
  every_case_tac>>fs[]>>
  rw[]>>
  drule check_xlrup_sound>>
  disch_then drule>>
  strip_tac>>
  first_x_assum drule_all>>
  rw[]>>
  drule_all wf_cfml_check_xlrup>>
  drule_all check_xlrup_tn_inv>>
  metis_tac[]
QED

(* Main theorem *)
Theorem check_xlrups_unsat_sound:
  EVERY wf_xlrup xlrups ∧
  EVERY nz_ilits cfml ∧
  check_xlrups_unsat xorig xlrups
    (build_cfml cid (MAP Vector cfml)) FEMPTY (LN,1) def ⇒
  ¬ ∃w.
    satisfies_cfml w (set cfml) ∧
    satisfies_xfml w (set xorig)
Proof
  rw[check_xlrups_unsat_def]>>
  gvs[AllCasePreds()]>>
  CCONTR_TAC>>gvs[]>>
  `tn_inv (LN,1)` by simp[tn_inv_def]>>
  `wf_cfml (build_cfml cid (MAP Vector cfml))` by
    gvs[wf_cfml_def,range_build_cfml,MEM_MAP,PULL_EXISTS,EVERY_MEM,
      toList_thm]>>
  PairCases_on`v2`>>
  drule check_xlrups_sound>>
  rpt(disch_then drule)>>
  simp[]>>
  qexists_tac`w`>>
  CONJ_TAC >- (
    CONJ_TAC >- metis_tac[]>>
    simp[isat_fml_def,range_build_cfml,satisfies_vcfml_def,
      satisfies_fml_gen_def,MEM_MAP,PULL_EXISTS,
      satisfies_vcclause_def,toList_thm]>>
    gvs[satisfies_cfml_def,satisfies_fml_gen_def])>>
  simp[isat_fml_def]>>
  metis_tac[contains_emp_unsat]
QED

(*** Converting a parsed formula into the checker's representation ***)

(* The checker's guarantee, phrased on the parsed formula rather than on
  the checker's internal representation *)
Theorem check_xlrups_unsat_conv_sound:
  EVERY (EVERY nz_lit) cfml ∧
  EVERY wf_xlrup xlrups ∧
  check_xlrups_unsat xfml xlrups
    (build_cfml cid (conv_cfml cfml)) FEMPTY (LN,1) def ⇒
  sols (cfml,xfml) = {}
Proof
  strip_tac>>
  `¬ ∃w.
    satisfies_cfml w (set (MAP to_cclause cfml)) ∧
    satisfies_xfml w (set xfml)` by (
    irule check_xlrups_unsat_sound>>
    CONJ_TAC >- (
      gvs[EVERY_MAP,EVERY_MEM,nz_ilits_def,to_cclause_def,MEM_MAP]>>
      metis_tac[to_ilit_NEQ_0])>>
    qexists_tac`cid`>>qexists_tac`def`>>qexists_tac`xlrups`>>
    gvs[conv_cfml_def,MAP_MAP_o,o_DEF])>>
  simp[EXTENSION,sols_def,sat_fml_def]>>
  CCONTR_TAC>>gvs[]>>
  qmatch_asmsub_rename_tac`satisfies_xfml w (set xfml)`>>
  drule conv_cfml_sound>>
  disch_then (qspec_then`w` mp_tac)>>
  gvs[satisfies_vcfml_eq,conv_cfml_def,LIST_TO_SET_MAP,IMAGE_IMAGE,
    o_DEF,toList_thm,satisfies_cnf_def,satisfies_fml_gen_def]>>
  metis_tac[]
QED
