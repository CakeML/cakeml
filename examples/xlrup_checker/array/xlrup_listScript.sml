(*
  This refines the checker to a fixed-size, list-based implementation
*)
open preamble basis xlrupTheory;

val _ = new_theory "xlrup_list"

Definition w8z_def:
  w8z = (0w:word8)
End

Definition w8o_def:
  w8o = (1w:word8)
End

Definition list_lookup_def:
  list_lookup ls default k =
  if LENGTH ls ≤ k then default
  else EL k ls
End

Definition index_def:
  index (i:int) =
  if i ≤ 0 then
    2 * Num(-i)
  else
    2 * Num(i) - 1
End

(* optimized for is_rup step *)
Definition delete_literals_sing_list_def:
  (delete_literals_sing_list Clist [] = SOME 0) ∧
  (delete_literals_sing_list Clist (c::cs) =
  if list_lookup Clist (w8z) (index c) = w8o
  then delete_literals_sing_list Clist cs
  else (* c should be the only literal left *)
    if EVERY (λi. list_lookup Clist w8z (index i) = w8o) cs
    then SOME (~c)
    else NONE)
End

Definition is_rup_list_aux_def:
  (is_rup_list_aux fml [] C Clist = NONE) ∧
  (is_rup_list_aux fml (i::is) C Clist =
  case list_lookup fml NONE i of
    NONE => NONE
  | SOME Ci =>
  case delete_literals_sing_list Clist Ci of
    NONE => NONE
  | SOME nl =>
    if nl = 0 then SOME (C, Clist)
    else is_rup_list_aux fml is (nl::C) (update_resize Clist w8z w8o (index nl)))
End

Definition set_list_def:
  (set_list Clist v [] = Clist) ∧
  (set_list Clist v (c::cs) =
    set_list (update_resize Clist w8z v (index c)) v cs)
End

Definition is_rup_list_def:
  is_rup_list fml ls c Clist =
  let Clist = set_list Clist w8o c in
  case is_rup_list_aux fml ls c Clist of
    NONE => NONE
  | SOME (c, Clist) => SOME (set_list Clist w8z c)
End

Definition add_xors_aux_c_list_def:
  (add_xors_aux_c_list fml [] s = SOME s) ∧
  (add_xors_aux_c_list fml (i::is) s =
  case list_lookup fml NONE i of NONE => NONE
  | SOME x =>
    add_xors_aux_c_list fml is (strxor_c s x))
End

(* Maybe needs speedup? *)
Definition is_emp_xor_list_def:
  is_emp_xor_list ls =
  EVERY ($= w8z) ls
End

Definition flip_bit_word_def:
  flip_bit_word w n =
  let b = ¬ (w ' n) in
  if b then
    w ‖ 1w ≪ n
  else
    w && ¬(1w ≪ n)
End

Definition flip_bit_list_def:
  flip_bit_list s n =
  let q = n DIV 8 in
  let r = n MOD 8 in
  let b = flip_bit_word (EL q s) r in
  LUPDATE b q s
End

Definition get_bit_list_def:
  get_bit_list (s:'a word list) n =
  let q = n DIV 8 in
  let r = n MOD 8 in
  EL q s ' r
End

Definition set_bit_word_def:
  set_bit_word w n b =
  if b then
    w ‖ 1w ≪ n
  else
    w && ¬(1w ≪ n)
End

Definition set_bit_list_def:
  set_bit_list s n b =
  let q = n DIV 8 in
  let r = n MOD 8 in
  let b = set_bit_word (EL q s) r b in
  LUPDATE b q s
End

Definition unit_prop_xor_list_def:
  unit_prop_xor_list t s l =
  let n = Num (ABS l) in
  case lookup n t of NONE => s
  | SOME n =>
  if n < 8 * LENGTH s then
    if l > 0 then
      (if get_bit_list s n then
        flip_bit_list (set_bit_list s n F) 0
      else s)
    else set_bit_list s n F
  else s
End

Definition get_units_list_def:
  (get_units_list fml [] cs = SOME cs) ∧
  (get_units_list fml (i::is) cs =
  case list_lookup fml NONE i of
  | SOME [l] =>
    get_units_list fml is (l::cs)
  | _ => NONE)
End

Definition unit_props_xor_list_def:
  unit_props_xor_list fml t ls s =
  case get_units_list fml ls [] of NONE => NONE
  | SOME cs =>
    SOME (FOLDL (unit_prop_xor_list t) s cs)
End

Definition is_xor_list_def:
  is_xor_list def fml is cfml cis t s =
  let r = REPLICATE def w8z in
  let r = strxor_c r s in
  case add_xors_aux_c_list fml is r of NONE => F
  | SOME x =>
    case unit_props_xor_list cfml t cis x of
      NONE => F
    | SOME y => is_emp_xor_list y
End

Definition list_delete_list_def:
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))
End

(*Might want to rename to MAX_LIST_index*)
Definition list_max_index_def:
  list_max_index C = 2* MAX_LIST (MAP (λc. Num (ABS c)) C) + 1
End

(* bump up the length to a large number *)
Definition resize_Clist_def:
  resize_Clist C Clist =
  if LENGTH Clist ≤ list_max_index C then
    REPLICATE (2 * (list_max_index C )) w8z
  else Clist
End

Definition extend_s_list_def:
  extend_s_list s n =
  if n < LENGTH s then s
  else
    s ++ REPLICATE (n - LENGTH s) (0w :word8)
End

Definition conv_xor_aux_list_def:
  (conv_xor_aux_list s [] = s) ∧
  (conv_xor_aux_list s (x::xs) =
  let v = Num (ABS x) in
  let s = extend_s_list s (v DIV 8 + 1) in
  if x > 0 then
    conv_xor_aux_list (flip_bit_list s v) xs
  else
    conv_xor_aux_list (flip_bit_list (flip_bit_list s v) 0) xs)
End

Definition conv_rawxor_list_def:
  conv_rawxor_list mv x =
  let r = REPLICATE (MAX 1 mv) w8z in
  let r = flip_bit_list r 0 in
    implode (MAP fromByte (conv_xor_aux_list r x))
End

(* TODO: There is a minor optimization here if we inline
  conv_rawxor into the addition in is_cfromx_list
  so that the byte array is allocated only once *)
Definition strxor_imp_cclause_list_def:
  strxor_imp_cclause_list mv s c =
  let t = conv_rawxor_list mv c in
  is_emp_xor_list (strxor_c s t)
End

Definition is_cfromx_list_def:
  is_cfromx_list def fml is c =
  let r = REPLICATE def w8z in
  case add_xors_aux_c_list fml is r of NONE => F
  | SOME x => strxor_imp_cclause_list def x c
End

Definition get_constrs_list_def:
  (get_constrs_list fml [] = SOME []) ∧
  (get_constrs_list fml (i::is) =
    case list_lookup fml NONE i of
      NONE => NONE
    | SOME Ci =>
      (case get_constrs_list fml is of NONE => NONE
      | SOME Cs => SOME (Ci::Cs)))
End

Definition is_xfromc_list_def:
  is_xfromc_list fml is rx =
  case get_constrs_list fml is of NONE => F
  | SOME ds =>
    check_rawxor_imp ds rx
End

Definition conv_xor_mv_list_def:
  conv_xor_mv_list mv x =
  conv_rawxor_list mv (MAP conv_lit x)
End

(* just making it easier to translate *)
Definition do_check_ibnn_def:
  do_check_ibnn bnn cs c =
  let ls = MAP (λl. -l) cs ++ c in
    check_ibnn bnn (mk_strict ls)
End

Definition is_cfromb_list_def:
  is_cfromb_list c cfml bfml ib i0 =
  case list_lookup bfml NONE ib of
    NONE => F
  | SOME bnn =>
  case get_units_list cfml i0 [] of NONE => F
  | SOME cs =>
    do_check_ibnn bnn cs c
End

Definition is_bnn_list_def:
  is_bnn_list rB cfml bfml ib i0 ⇔ T
End

Definition check_xlrup_list_def:
  check_xlrup_list xorig borig xlrup
    cfml xfml bfml tn def Clist =
  case xlrup of
    Del cl =>
    SOME (list_delete_list cl cfml, xfml, bfml, tn, def, Clist)
  | RUP n c i0 =>
    let Clist = resize_Clist c Clist in
    (case is_rup_list cfml i0 c Clist of
      NONE => NONE
    | SOME Clist =>
      SOME (update_resize cfml NONE (SOME c) n, xfml, bfml,
        tn, def, Clist))
  | XOrig n rx =>
    if MEM rx xorig
    then
      let (mx,tn) = ren_lit_ls tn rx [] in
      let X = conv_xor_mv_list def mx in
      SOME (cfml, update_resize xfml NONE (SOME X) n, bfml,
        tn, MAX def (strlen X), Clist)
    else NONE
  | XAdd n rx i0 i1 =>
    let (mx,tn) = ren_int_ls tn rx [] in
    let X = conv_rawxor_list def mx in
    if is_xor_list def xfml i0 cfml i1 (FST tn) X then
      SOME (cfml, update_resize xfml NONE (SOME X) n, bfml,
        tn, MAX def (strlen X), Clist)
    else NONE
  | XDel xl =>
    SOME (cfml, list_delete_list xl xfml, bfml, tn, def, Clist)
  | CFromX n c i0 =>
    let (mc,tn) = ren_int_ls tn c [] in
    let Clist = resize_Clist c Clist in
    if is_cfromx_list def xfml i0 mc then
      SOME (update_resize cfml NONE (SOME c) n, xfml, bfml,
        tn, def, Clist)
    else NONE
  | XFromC n rx i0 =>
    if is_xfromc_list cfml i0 rx then
      let (mx,tn) = ren_int_ls tn rx [] in
      let X = conv_rawxor_list def mx in
      SOME (cfml, update_resize xfml NONE (SOME X) n, bfml,
        tn, MAX def (strlen X), Clist)
    else NONE
  | BOrig n rB =>
    if MEM rB borig
    then
      let B = conv_bnn rB in
        SOME (cfml, xfml, update_resize bfml NONE (SOME B) n, tn, def, Clist)
    else NONE
  | BAdd n rB ib i0 =>
    if is_bnn_list rB cfml bfml ib i0 then
      let B = conv_bnn rB in
        SOME (cfml, xfml, update_resize bfml NONE (SOME B) n, tn, def, Clist)
    else NONE
  | BDel bl =>
    SOME (cfml, xfml, list_delete_list bl bfml, tn, def, Clist)
  | CFromB n c ib i0 =>
    let Clist = resize_Clist c Clist in
    if is_cfromb_list c cfml bfml ib i0 then
      SOME (update_resize cfml NONE (SOME c) n, xfml, bfml,
        tn, def, Clist)
    else NONE
End

(* semantic *)
Definition check_xlrups_list_def:
  (check_xlrups_list xorig borig [] cfml xfml bfml tn def Clist =
    SOME (cfml, xfml, bfml, tn, def)) ∧
  (check_xlrups_list xorig borig (x::xs) cfml xfml bfml tn def Clist =
    case check_xlrup_list xorig borig x cfml xfml bfml tn def Clist of
      NONE => NONE
    | SOME (cfml', xfml', bfml', tn', def', Clist') =>
      check_xlrups_list xorig borig xs cfml' xfml' bfml' tn' def' Clist')
End

(* Search backwards through the IDs *)
Definition contains_emp_list_aux_def:
  contains_emp_list_aux fml i =
  if i = 0 then F
  else
    let i1 = i - 1 in
    case list_lookup fml NONE i1 of
      NONE => contains_emp_list_aux fml i1
    | SOME c =>
      if c = [] then T
      else contains_emp_list_aux fml i1
End

Definition contains_emp_list_def:
  contains_emp_list fml =
  contains_emp_list_aux fml (LENGTH fml)
End

Definition check_xlrups_unsat_list_def:
  check_xlrups_unsat_list xorig borig xlrups
    cfml xfml bfml tn def Clist =
  case check_xlrups_list xorig borig xlrups
    cfml xfml bfml tn def Clist of
    NONE => F
  | SOME (cfml', xfml', bfml', tn', def') =>
    contains_emp_list cfml'
End

(* prove that check_xlrup_list implements check_xlrup *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x.
  if x < LENGTH fmlls then
    lookup x fml = EL x fmlls
  else
    lookup x fml = NONE
End

Theorem fml_rel_list_lookup:
  fml_rel fml fmlls ⇒
  list_lookup fmlls NONE i = lookup i fml
Proof
  rw[fml_rel_def,list_lookup_def]>>
  first_x_assum(qspec_then`i` mp_tac)>>
  rw[]
QED

(* Require that the lookup table matches a clause exactly *)
Definition lookup_rel_def:
  lookup_rel C Clist ⇔
  (* elements are either 0 or 1 *)
  (∀i. MEM i Clist ⇒ i = w8z ∨ i = w8o) ∧
  (* where 1 indicates membership in C *)
  (∀i. list_lookup Clist w8z (index i) = w8o ⇔ MEM i C)
End

Theorem delete_literals_sing_list_correct:
  ∀ls.
  lookup_rel C Clist ∧ wf_clause ls ⇒
  case delete_literals_sing_list Clist ls of
    NONE => LENGTH (delete_literals ls C) > 1
  | SOME 0 => delete_literals ls C = []
  | SOME l => delete_literals ls C = [-l]
Proof
  Induct>>simp[delete_literals_sing_list_def,delete_literals_def]>>
  ntac 2 strip_tac>>fs[lookup_rel_def,wf_clause_def]>>
  IF_CASES_TAC>>simp[]
  >-
    fs[delete_literals_def]
  >>
  IF_CASES_TAC>>simp[]
  >-
    simp[FILTER_EQ_NIL]
  >>
  Cases_on`FILTER (λx. ¬MEM x C) ls` >>
  pop_assum mp_tac>> simp[FILTER_EQ_NIL,o_DEF]
QED

Theorem MEM_update_resize:
  MEM i (update_resize ls def v x) ⇒
  i = def ∨ MEM i ls ∨ i = v
Proof
  rw[update_resize_def,MEM_LUPDATE]
  >- metis_tac[MEM_EL]>>
  rw[EL_APPEND_EQN]>- metis_tac[MEM_EL]>>
  simp[EL_REPLICATE]
QED

Theorem list_lookup_update_resize:
  list_lookup (update_resize ls def v x) def y =
  if y = x then v
  else
    list_lookup ls def y
Proof
  simp[update_resize_def]>>
  IF_CASES_TAC
  >-
    (simp[list_lookup_def,EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[list_lookup_def,EL_LUPDATE,EL_APPEND_EQN,REPLICATE]>>
  IF_CASES_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  simp[EL_REPLICATE]
QED

Theorem index_11:
  index i = index x ⇔ i = x
Proof
  rw[index_def,EQ_IMP_THM]>>
  intLib.ARITH_TAC
QED

Theorem index_onto:
  ∃i. index i = k
Proof
  rw[index_def]>>
  qexists_tac`if k MOD 2 = 0 then -&(k DIV 2) else &((k+1) DIV 2)`>>
  rw[]>>fs[]>>simp[bitTheory.DIV_MULT_THM2]>>
  intLib.ARITH_TAC
QED

Theorem lookup_rel_cons:
  lookup_rel C Clist ⇒
  lookup_rel (x::C) (update_resize Clist w8z w8o (index x))
Proof
  rw[lookup_rel_def]
  >-
   (drule MEM_update_resize >>
   metis_tac[])>>
  simp[list_lookup_update_resize,index_11]>>
  IF_CASES_TAC>>metis_tac[]
QED

Theorem lookup_rel_REVERSE:
  lookup_rel (REVERSE C) Clist ⇔ lookup_rel C Clist
Proof
  rw[lookup_rel_def]
QED

Theorem fml_rel_is_rup_list_aux:
  ∀ls C Clist.
  fml_rel fml fmlls ∧ wf_cfml fml ∧
  lookup_rel C Clist ⇒
  case is_rup_list_aux fmlls ls C Clist of
    SOME (C', Clist') =>
    is_rup fml ls C ∧ lookup_rel C' Clist'
  | NONE => ¬ is_rup fml ls C (* Not required but should be true *)
Proof
  Induct>>fs[is_rup_list_aux_def,is_rup_def]>>rw[]>>
  DEP_REWRITE_TAC[fml_rel_list_lookup]>>simp[]>>
  Cases_on`lookup h fml`>>simp[]>>
  `wf_clause x` by
    (fs[wf_cfml_def,range_def]>>metis_tac[])>>
  drule delete_literals_sing_list_correct>>
  disch_then drule>>
  TOP_CASE_TAC>>simp[]
  >-
    (every_case_tac>>fs[]) >>
  IF_CASES_TAC>>simp[]>>
  qmatch_goalsub_abbrev_tac`is_rup_list_aux _ _ aaa bbb`>>
  first_x_assum(qspecl_then[`aaa`,`bbb`] mp_tac)>>
  impl_tac >-
    (unabbrev_all_tac>>simp[lookup_rel_cons])>>
  TOP_CASE_TAC>>simp[]
QED

Theorem lookup_rel_set_list_lookup_rel:
  ∀D ls C.
  lookup_rel C ls ⇒
  lookup_rel (C++D) (set_list ls w8o D)
Proof
  Induct>>rw[set_list_def]>>
  `C ++ h::D = (C++[h])++D` by simp[]>>
  pop_assum SUBST_ALL_TAC>>
  first_x_assum match_mp_tac>>
  `C++[h] = REVERSE (h::REVERSE C)` by fs[]>>
  metis_tac[lookup_rel_REVERSE,lookup_rel_cons]
QED

Theorem empty_set_list_lookup_rel:
  EVERY ($= w8z) Clist ⇒
  lookup_rel C (set_list Clist w8o C)
Proof
  rw[]>>
  `lookup_rel [] Clist` by
    (fs[lookup_rel_def,EVERY_MEM,list_lookup_def]>>
    rw[]>>fs[w8z_def,w8o_def]>>
    first_x_assum(qspec_then`EL (index i) Clist` mp_tac)>>
    impl_tac>-
      simp[EL_MEM]>>
    simp[])>>
  drule lookup_rel_set_list_lookup_rel>>
  simp[]
QED

Theorem list_lookup_set_list:
  ∀is ls.
  list_lookup (set_list ls v is) w8z x =
  if ∃y. x = index y ∧ MEM y is then v
  else
    list_lookup ls w8z x
Proof
  Induct>>simp[set_list_def]>>
  ntac 2 strip_tac>>
  IF_CASES_TAC>-
    (fs[]>>
    metis_tac[])>>
  simp[list_lookup_update_resize]>>
  fs[]>>
  metis_tac[]
QED

Theorem lookup_rel_set_list_empty:
  ∀C.
  lookup_rel C Clist ⇒
  EVERY ($= w8z) (set_list Clist w8z C)
Proof
  rw[EVERY_EL]>>
  `list_lookup (set_list Clist w8z C) w8z n = w8z` by
    (simp[list_lookup_set_list]>>
    rw[]>>fs[lookup_rel_def,PULL_EXISTS]>>
    `?k. index k = n` by fs[index_onto]>>
    first_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    first_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    fs[list_lookup_def]>>
    rw[]>>fs[]>>
    first_x_assum(qspec_then `EL (index k) Clist` mp_tac)>>
    impl_tac>-
      (simp[MEM_EL]>>
      qexists_tac`index k`>>simp[])>>
    metis_tac[])>>
  rfs[list_lookup_def]
QED

Theorem fml_rel_is_rup_list:
  EVERY ($= w8z) Clist ∧ (* the array is always zero-ed before and after *)
  wf_cfml fml ∧
  fml_rel fml fmlls ⇒
  (case is_rup_list fmlls ls (C:cclause) Clist of
    SOME Clist' => is_rup fml ls C ∧ EVERY ($= w8z) Clist'
  | NONE => ¬is_rup fml ls C)
Proof
  rw[is_rup_list_def]>>
  drule fml_rel_is_rup_list_aux>>
  simp[]>>
  drule empty_set_list_lookup_rel>>
  disch_then(qspec_then`C` assume_tac)>>
  disch_then drule>>
  disch_then(qspec_then`ls` assume_tac)>>
  every_case_tac>>fs[]>>
  metis_tac[lookup_rel_set_list_empty]
QED

Theorem list_delete_list_FOLDL:
  ∀l fmlls.
  list_delete_list l fmlls =
  FOLDL (\fml i.
    if LENGTH fml ≤ i then fml else LUPDATE NONE i fml) fmlls l
Proof
  Induct>>rw[list_delete_list_def]
QED

Theorem LENGTH_list_delete_list[simp]:
  ∀l.
  LENGTH (list_delete_list l fmlls) = LENGTH fmlls
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]
QED

Theorem fml_rel_list_delete_list:
  ∀l fml fmlls fmlls'.
  fml_rel fml fmlls ∧
  list_delete_list l fmlls = fmlls' ⇒
  fml_rel (FOLDL (\a b. delete b a) fml l) fmlls'
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]>>
  first_x_assum drule>>
  rw[fml_rel_def]
  >- (
    first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    simp[lookup_delete])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE,lookup_delete]>>
    IF_CASES_TAC>>fs[])>>
  simp[lookup_delete]
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert n v fml) (update_resize fmlls NONE (SOME v) n)
Proof
  rw[update_resize_def,fml_rel_def,EL_LUPDATE]>>
  IF_CASES_TAC>> rw[lookup_insert]
  >- metis_tac[]
  >- metis_tac[]
  >-
    (first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
    fs[EL_APPEND_EQN]>>
    rw[]>>fs[EL_REPLICATE,LENGTH_REPLICATE])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]
QED

Theorem flip_bit_word_set_get:
  flip_bit_word w n =
  toByte (set_bit_char (fromByte w) n (¬get_bit_char (fromByte w) n))
Proof
  rw[set_bit_char_def,get_bit_char_def,flip_bit_word_def]
QED

Theorem EL_explode:
  EL n (explode s) =
  strsub s n
Proof
  Cases_on`s`>>simp[]
QED

Theorem strsub_implode:
  strsub (implode s) n =
  EL n s
Proof
  fs[strsub_def,implode_def]
QED

Theorem flip_bit_list_flip_bit:
  n DIV 8 < LENGTH ls ⇒
  flip_bit_list ls n =
  MAP toByte (explode (flip_bit (implode (MAP fromByte ls)) n))
Proof
  rw[flip_bit_list_def,flip_bit_word_set_get]>>
  rw[LIST_EQ_REWRITE]>>
  simp[EL_MAP,flip_bit_def,set_bit_def,get_bit_def,EL_explode]>>
  simp[set_char_def,get_char_def,strsub_implode]>>
  rw[EL_LUPDATE,EL_MAP]
QED

Theorem extend_s_list_extend_s:
  extend_s_list s n =
  MAP toByte (explode (extend_s (implode (MAP fromByte s)) n))
Proof
  rw[extend_s_list_def,extend_s_def]>>fs[MAP_MAP_o,o_DEF]>>
  EVAL_TAC
QED

Theorem conv_xor_aux_list_conv_xor_aux:
  ∀x ls.
  conv_xor_aux_list ls x =
  MAP toByte (explode (conv_xor_aux (implode (MAP fromByte ls)) x))
Proof
  Induct>>rw[conv_xor_aux_def,conv_xor_aux_list_def]
  >-
    simp[MAP_MAP_o,o_DEF]>>
  DEP_REWRITE_TAC[flip_bit_list_flip_bit,extend_s_list_extend_s]>>
  simp[MAP_MAP_o,o_DEF]>>
  rw[extend_s_def]
QED

Theorem conv_rawxor_list_conv_rawxor:
  conv_rawxor_list mv x = conv_rawxor mv x
Proof
  rw[conv_rawxor_list_def,conv_rawxor_def]>>
  simp[conv_xor_aux_list_conv_xor_aux]>>
  simp[flip_bit_list_flip_bit,MAP_MAP_o,o_DEF]>>
  simp[extend_s_def]>>
  rpt(AP_THM_TAC ORELSE AP_TERM_TAC)>>
  EVAL_TAC
QED

Theorem conv_xor_mv_list_conv_xor_mv:
  conv_xor_mv_list mv x = conv_xor_mv mv x
Proof
  rw[conv_xor_mv_list_def,conv_xor_mv_def,conv_rawxor_list_conv_rawxor]
QED

Theorem add_xors_aux_c_list_add_xors_aux_c:
  ∀is x y.
  fml_rel fml fmlls ∧
  add_xors_aux_c_list fmlls is x = SOME y ⇒
  add_xors_aux_c fml is x = SOME y
Proof
  Induct>>rw[add_xors_aux_c_def,add_xors_aux_c_list_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum (irule_at Any)>>
  metis_tac[fml_rel_list_lookup]
QED

Theorem is_emp_xor_list_is_emp_xor:
  is_emp_xor_list x =
  is_emp_xor (implode (MAP fromByte x))
Proof
  rw[is_emp_xor_list_def,is_emp_xor_def,EVERY_MAP]>>
  match_mp_tac EVERY_CONG>>rw[]>>
  EVAL_TAC>>
  `w2n x' < dimword(:8)` by
    metis_tac[w2n_lt]>>
  fs[]
QED

Theorem get_bit_list_get_bit:
  n DIV 8 < LENGTH ls ⇒
  get_bit_list ls n =
  get_bit (implode (MAP fromByte ls)) n
Proof
  rw[get_bit_list_def,get_bit_def,get_char_def,get_bit_char_def]>>
  simp[strsub_implode,toByte_def,EL_MAP,fromByte_def]
QED

Theorem set_bit_word_set_bit:
  set_bit_word w n b =
  toByte (set_bit_char (fromByte w) n b)
Proof
  rw[set_bit_char_def,set_bit_word_def]
QED

Theorem set_bit_list_set_bit:
  n DIV 8 < LENGTH ls ⇒
  set_bit_list ls n b =
  MAP toByte (explode (set_bit (implode (MAP fromByte ls)) n b))
Proof
  rw[set_bit_list_def,set_bit_word_set_bit,set_bit_def,set_char_def]>>
  rw[LIST_EQ_REWRITE]>>
  simp[EL_MAP]>>
  rw[EL_LUPDATE,EL_MAP,get_char_def,toByte_def,fromByte_def,strsub_implode]
QED

Theorem strlen_set_bit[simp]:
  strlen (set_bit s n b) = strlen s
Proof
  rw[set_bit_def,set_char_def]
QED

Theorem unit_prop_xor_list_unit_prop_xor:
  implode (MAP fromByte (unit_prop_xor_list t x l)) =
  unit_prop_xor t (implode (MAP fromByte x)) l
Proof
  rw[unit_prop_xor_def,unit_prop_xor_list_def]>>
  TOP_CASE_TAC>>
  IF_CASES_TAC>>fs[]>>
  `x' DIV 8 < LENGTH x` by
    (DEP_REWRITE_TAC[DIV_LT_X]>>simp[])>>
  rw[]>>
  gvs[get_bit_list_get_bit]>>
  simp[set_bit_list_set_bit]>>
  DEP_REWRITE_TAC[flip_bit_list_flip_bit]>>simp[]>>
  simp[MAP_MAP_o,o_DEF]
QED

Theorem get_units_list_get_units:
  ∀is acc.
  fml_rel fml fmlls ⇒
  get_units_list fmlls is acc = get_units fml is acc
Proof
  Induct>>rw[get_units_list_def,get_units_def]>>
  drule fml_rel_list_lookup>>rw[]>>gvs[]
QED

Theorem unit_props_xor_list_unit_props_xor:
  ∀is x y .
  fml_rel fml fmlls ∧
  unit_props_xor_list fmlls t is x = SOME y ⇒
  unit_props_xor fml t is (implode (MAP fromByte x)) =
    SOME (implode (MAP fromByte y))
Proof
  rw[]>>drule get_units_list_get_units>>
  gvs[unit_props_xor_def,unit_props_xor_list_def,AllCaseEqs()]>>rw[]>>
  gvs[]>>
  rpt (pop_assum kall_tac)>>
  qid_spec_tac`x`>>
  qid_spec_tac`cs`>>
  ho_match_mp_tac SNOC_INDUCT>>rw[]>>
  simp[FOLDL_SNOC,GSYM unit_prop_xor_list_unit_prop_xor]
QED

Theorem is_xor_list_is_xor:
  fml_rel fml fmlls ∧
  fml_rel cfml cfmlls ∧
  is_xor_list def fmlls is cfmlls cis t x ⇒
  is_xor def fml is cfml cis t x
Proof
  rw[is_xor_list_def]>>
  every_case_tac>>fs[]>>
  drule_all add_xors_aux_c_list_add_xors_aux_c>>
  rw[is_xor_def]>>
  drule add_xors_aux_c_add_xors_aux>>
  simp[strxor_aux_c_strxor_aux,MAP_MAP_o,o_DEF]>>
  `implode (REPLICATE def (fromByte w8z)) =
    extend_s (strlit "") def` by
    (rw[extend_s_def]>>fs[]>>
    EVAL_TAC)>>
  rw[]>>
  drule_all unit_props_xor_list_unit_props_xor>>
  fs[is_emp_xor_list_is_emp_xor]
QED

Theorem strxor_imp_cclause_list_strxor_imp_cclause:
  strxor_imp_cclause_list def x c =
  strxor_imp_cclause def (implode (MAP fromByte x)) c
Proof
  rw[strxor_imp_cclause_list_def,strxor_imp_cclause_def]>>
  simp[is_emp_xor_list_is_emp_xor,strxor_aux_c_strxor_aux]>>
  simp[MAP_MAP_o,o_DEF,conv_rawxor_list_conv_rawxor]
QED

Theorem is_cfromx_list_is_cfromx:
  fml_rel fml fmlls ∧
  is_cfromx_list def fmlls is c ⇒
  is_cfromx def fml is c
Proof
  rw[is_cfromx_list_def]>>
  every_case_tac>>fs[]>>
  drule_all add_xors_aux_c_list_add_xors_aux_c>>
  rw[is_cfromx_def]>>
  drule add_xors_aux_c_add_xors_aux>>
  simp[]>>
  `implode (REPLICATE def (fromByte w8z)) =
    extend_s (strlit "") def` by
    (rw[extend_s_def]>>fs[]>>
    EVAL_TAC)>>
  rw[]>>
  fs[strxor_imp_cclause_list_strxor_imp_cclause]
QED

Theorem fml_rel_get_constrs_list:
  ∀is.
  fml_rel fml fmlls ⇒
  get_constrs_list fmlls is =
  get_constrs fml is
Proof
  Induct>>rw[get_constrs_def,get_constrs_list_def]>>
  gvs[]>>every_case_tac>>
  drule fml_rel_list_lookup>>rw[]>>gs[]>>
  metis_tac[option_CLAUSES]
QED

Theorem is_xfromc_list_is_xfromc:
  fml_rel fml fmlls ∧
  is_xfromc_list fmlls is rx ⇒
  is_xfromc fml is rx
Proof
  rw[is_xfromc_list_def,is_xfromc_def]>>
  every_case_tac>>
  fs[]>>
  metis_tac[fml_rel_get_constrs_list,option_CLAUSES]
QED

Theorem is_cfromb_list_is_cfromb:
  fml_rel cfml cfmlls ∧
  fml_rel bfml bfmlls ∧
  is_cfromb_list c cfmlls bfmlls ib ls ⇒
  is_cfromb c cfml bfml ib ls
Proof
  strip_tac>>
  gvs[AllCasePreds(),is_cfromb_list_def,is_cfromb_def]>>
  drule fml_rel_list_lookup>>
  drule get_units_list_get_units>>
  rw[]>>gvs[do_check_ibnn_def]
QED

Theorem fml_rel_check_xlrup_list:
  fml_rel cfml cfmlls ∧
  fml_rel xfml xfmlls ∧
  fml_rel bfml bfmlls ∧
  EVERY ($= w8z) Clist ∧
  wf_cfml cfml ⇒
  case check_xlrup_list xorig borig xlrup
    cfmlls xfmlls bfmlls tn def Clist of
    SOME (cfmlls', xfmlls', bfmlls', tn', def', Clist') =>
    EVERY ($= w8z) Clist' ∧
    ∃cfml' xfml' bfml'.
    check_xlrup xorig borig xlrup cfml xfml bfml tn def =
      SOME (cfml',xfml',bfml',tn',def') ∧
    fml_rel cfml' cfmlls' ∧
    fml_rel xfml' xfmlls' ∧
    fml_rel bfml' bfmlls'
  | NONE => T
Proof
  simp[check_xlrup_def,check_xlrup_list_def]>>
  strip_tac>>
  Cases_on`xlrup`>>simp[]
  >- (* Del *)
    metis_tac[fml_rel_list_delete_list]
  >- ( (* RUP *)
    every_case_tac>>fs[]>>
    `EVERY ($= w8z) (resize_Clist l Clist)` by
      rw[resize_Clist_def]>>
    drule_all fml_rel_is_rup_list>>
    disch_then (qspecl_then [`l0`,`l`] assume_tac)>>
    every_case_tac>>gvs[]>>
    metis_tac[fml_rel_update_resize])
  >- ( (* XOrig *)
    every_case_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    fs[conv_xor_mv_list_conv_xor_mv]>>
    metis_tac[fml_rel_update_resize])
  >- ( (* XAdd *)
    every_case_tac>>fs[]>>
    pairarg_tac>>gvs[]>>
    drule_all is_xor_list_is_xor>>
    fs[conv_rawxor_list_conv_rawxor]>>
    metis_tac[fml_rel_update_resize])
  >- (* XDel *)
    metis_tac[fml_rel_list_delete_list]
  >- ( (* CFromX *)
    every_case_tac>>fs[]>>
    pairarg_tac>>gvs[]>>
    CONJ_TAC >-
      rw[resize_Clist_def]>>
    CONJ_TAC >-
      metis_tac[is_cfromx_list_is_cfromx]>>
    metis_tac[fml_rel_update_resize])
  >- ( (* XFromC *)
    every_case_tac>>fs[conv_rawxor_list_conv_rawxor]>>
    pairarg_tac>>gvs[]>>
    CONJ_TAC >-
      metis_tac[is_xfromc_list_is_xfromc]>>
    metis_tac[fml_rel_update_resize])
  >- ( (* BOrig *)
    every_case_tac>>gvs[]>>
    metis_tac[fml_rel_update_resize]
  )
  >- (
    rw[] >- cheat>>
    metis_tac[fml_rel_update_resize])
  >- (* BDel *)
    metis_tac[fml_rel_list_delete_list]
  >- (
    (* CFromB *)
    every_case_tac>>gvs[]>>
    `EVERY ($= w8z) (resize_Clist l Clist)` by
      rw[resize_Clist_def]>>
    irule_at Any fml_rel_update_resize>>simp[]>>
    drule_all is_cfromb_list_is_cfromb>>
    simp[])
QED

Theorem contains_emp_list_aux:
  ∀n.
  n <= LENGTH fml ⇒
  (contains_emp_list_aux fml n ⇔
  MEM (SOME []) (TAKE n fml))
Proof
  Induct>>rw[Once contains_emp_list_aux_def]>>
  every_case_tac>>rw[]>>
  `n < LENGTH fml` by fs[]>>
  drule SNOC_EL_TAKE>>
  disch_then sym_sub_tac>>
  fs[list_lookup_def]
QED

Theorem fml_rel_contains_emp_list:
  fml_rel fml fmlls ⇒
  (contains_emp_list fmlls <=> contains_emp fml)
Proof
  simp[contains_emp_list_def]>>
  DEP_REWRITE_TAC[contains_emp_list_aux]>>
  rw[contains_emp_def,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
  fs[fml_rel_def,MEM_EL]>>
  eq_tac>>rw[]
  >- (
    first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
    metis_tac[])>>
  rename1`lookup n fml`>>
  first_x_assum(qspec_then`n` assume_tac)>>rfs[]>>
  metis_tac[]
QED

Theorem fml_rel_check_xlrups_list:
  ∀xlrups cfml cfmlls xfml xfmlls bfml bfmlls
    cfmlls' xfmlls' bfmlls' tn tn' def def' Clist.
  fml_rel cfml cfmlls ∧
  fml_rel xfml xfmlls ∧
  fml_rel bfml bfmlls ∧
  EVERY ($= w8z) Clist ∧ wf_cfml cfml ∧
  EVERY wf_xlrup xlrups ∧
  check_xlrups_list xorig borig xlrups cfmlls xfmlls bfmlls
    tn def Clist =
    SOME (cfmlls', xfmlls', bfmlls', tn', def') ⇒
  ∃cfml' xfml' bfml'.
    check_xlrups xorig borig xlrups cfml xfml bfml tn def =
      SOME (cfml',xfml',bfml',tn',def') ∧
    fml_rel cfml' cfmlls' ∧
    fml_rel xfml' xfmlls' ∧
    fml_rel bfml' bfmlls'
Proof
  Induct>>fs[check_xlrups_list_def,check_xlrups_def]>>
  rw[]>>gvs[AllCaseEqs()]>>
  drule  fml_rel_check_xlrup_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`xorig`,`h`,`tn`,`def`,`borig`] mp_tac)>>
  simp[PULL_EXISTS]>>
  rw[]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]>>
  metis_tac[wf_cfml_check_xlrup]
QED

val _ = export_theory();
