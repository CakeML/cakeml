(*
   Basic specification of an xlrup checker (minimal optimization)
*)
open preamble miscTheory mlstringTheory cnf_xorTheory;

val _ = new_theory "xlrup";

(* Internal representations *)
Type cclause = ``:int list``;
Type strxor = ``:mlstring``;

Definition values_def:
  values s = {v | ∃n. lookup n s = SOME v}
End

(* Satisfiability for clauses is defined by interpreting into the
  top-level semantics *)
Definition interp_lit_def:
  interp_lit (l:int) =
  if l > 0 then Pos (Num (ABS l))
  else Neg (Num (ABS l))
End

Definition isat_cclause_def:
  isat_cclause w ls ⇔
  ∃l. MEM l ls ∧ l ≠ 0 ∧ sat_lit w (interp_lit l)
End

Definition isat_cfml_def:
  isat_cfml w cfml ⇔ (∀C. C ∈ cfml ⇒ isat_cclause w C)
End

(* Dummy definition *)
Definition DO_NOT_EXPAND:
  isat_strxor w x = T
End

Definition isat_xfml_def:
  isat_xfml w xfml ⇔ (∀C. C ∈ xfml ⇒ isat_strxor w C)
End

Definition isat_fml_def:
  isat_fml w (cfml,xfml) ⇔
  isat_cfml w cfml ∧ isat_xfml w xfml
End



(* Connection to the top-level semantics *)
Definition conv_lit_def:
  (conv_lit (Pos n) = (&n):int) ∧
  (conv_lit (Neg n) = -(&n):int)
End

Definition conv_cfml_def:
  conv_cfml cfml = MAP (MAP conv_lit) cfml
End

Definition nz_lit_def[simp]:
  (nz_lit (Pos n) <=> n ≠ (0:num)) ∧
  (nz_lit (Neg n) <=> n ≠ 0)
End

Theorem interp_lit_conv_lit:
  nz_lit y ⇒
  interp_lit (conv_lit y) = y
Proof
  Cases_on`y`>>rw[conv_lit_def,interp_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem nz_lit_conv_lit:
  nz_lit y ⇒ conv_lit y ≠ 0
Proof
  Cases_on`y`>>rw[conv_lit_def]
QED

Theorem issat_cclause_MAP_conv_lit:
  EVERY nz_lit C ⇒
  (isat_cclause w (MAP conv_lit C) ⇔
  sat_clause w C)
Proof
  rw[isat_cclause_def,sat_clause_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  metis_tac[interp_lit_conv_lit,nz_lit_conv_lit]
QED

Theorem conv_cfml_sound:
  EVERY (EVERY nz_lit) cfml ⇒
  (isat_cfml w (set (conv_cfml cfml)) ⇔
  (∀C. C ∈ set cfml ⇒ sat_clause w C))
Proof
  rw[isat_cfml_def,conv_cfml_def,MEM_MAP,PULL_EXISTS,EVERY_MEM]>>
  metis_tac[issat_cclause_MAP_conv_lit,EVERY_MEM]
QED

(* TODO: for XOR... *)
Definition toByte_def:
  toByte c = (n2w (ORD c)):word8
End

(* Get n-th bit from a string *)
Definition get_bit_char_def:
  get_bit_char c n =
  toByte c ' n
End

Definition get_bit_def:
  get_bit (s:strxor) n =
  let q = n DIV 8 in
  let r = n MOD 8 in
  get_bit_char (strsub s q) r
End

(* Implementation *)
Datatype:
  xlrup =
  | Del (num list) (* Clauses to delete *)
  | RUP num cclause (num list)
    (* RUP n C hints : derive clause C by RUP using hints *)
  | XAdd num strxor (num list)
    (* Xadd n C hints derive XOR C by adding XORs using hints *)
  | XDel (num list) (* XORs to delete *)
  | CFromX num cclause (num list)
    (* Derive clause from hint XORs *)
  | XFromC num strxor (num list)
    (* Derive XOR from hint clauses *)
End

val delete_literals_def = Define`
  delete_literals (C:cclause) (D:cclause) =
  FILTER (λx. ¬MEM x D) C`

(*
  Checking for RUP
*)
Definition is_rup_def:
  (is_rup fml [] (C:cclause) = F) ∧
  (is_rup fml (i::is) C =
  case lookup i fml of
    NONE => F
  | SOME Ci =>
  case delete_literals Ci C of
    [] => T
  | [l] => is_rup fml is (-l :: C)
  | _ => F)
End

Definition check_xlrup_def:
  check_xlrup xlrup cfml xfml =
  case xlrup of
    Del cl => SOME (FOLDL (\a b. delete b a) cfml cl, xfml)
  | RUP n C i0 =>
    if is_rup cfml i0 C then
      SOME (insert n C cfml, xfml)
    else NONE
  | XDel xl => SOME (cfml, FOLDL (\a b. delete b a) xfml xl)
  | _ => NONE
End

Definition check_xlrups_def:
  (check_xlrups [] cfml xfml = SOME (cfml,xfml)) ∧
  (check_xlrups (x::xs) cfml xfml =
  case check_xlrup x cfml xfml of
    NONE => NONE
  | SOME (cfml',xfml') => check_xlrups xs cfml' xfml')
End

Definition contains_emp_def:
  contains_emp fml =
  let ls = MAP SND (toAList fml) in
  MEM [] ls
End

Definition check_xlrups_unsat_def:
  check_xlrups_unsat xlrups cfml xfml =
  case check_xlrups xlrups cfml xfml of
    NONE => F
  | SOME (cfml',xfml') => contains_emp cfml'
End

(* Proofs *)
Theorem interp_lit_eq:
  interp_lit x = interp_lit y ⇒
  x = y
Proof
  rw[interp_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem set_delete_literals:
  set (delete_literals C D)  =
  set C DIFF set D
Proof
  simp[delete_literals_def]>>
  fs[EXTENSION,MEM_MAP]>>
  rw[EQ_IMP_THM]>>
  fs[MEM_FILTER]>>
  metis_tac[interp_lit_eq]
QED

Theorem is_rup_sound:
  ∀is C.
  is_rup fml is C ∧
  isat_cfml w (values fml) ⇒
  isat_cclause w C
Proof
  Induct>>fs[is_rup_def]>>
  ntac 3 strip_tac>>
  every_case_tac>>fs[]>>
  `set x DIFF set C =
   set (delete_literals x C)` by
   metis_tac[set_delete_literals]>>
  gvs[]
  >- (
    fs[isat_cfml_def,PULL_EXISTS,values_def]>>
    first_x_assum drule>>
    rw[isat_cclause_def]>>
    first_x_assum (irule_at Any)>>
    rfs[EXTENSION,MEM_MAP]>>
    metis_tac[])
  >- (
    first_x_assum (drule_at Any)>>
    gvs[isat_cclause_def,EXTENSION]>>
    reverse (rw[])
    >- metis_tac[]>>
    fs[isat_cfml_def,PULL_EXISTS,values_def]>>
    first_x_assum drule>>
    rw[isat_cclause_def]>>
    Cases_on`MEM l C`
    >- metis_tac[] >>
    first_x_assum (qspec_then`l` mp_tac)>>
    simp[]>>
    rw[]>>
    `h' = 0` by (
      gvs[sat_lit_def,interp_lit_def]>>
      every_case_tac>>gvs[]>>
      intLib.ARITH_TAC))
QED

Theorem delete_preserves_isat_cfml:
  isat_cfml w (values C) ⇒
  isat_cfml w (values (delete n C))
Proof
  rw[isat_cfml_def]>>
  fs[values_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem delete_preserves_isat_xfml:
  isat_xfml w (values x) ⇒
  isat_xfml w (values (delete n x))
Proof
  rw[isat_xfml_def]>>
  fs[values_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem delete_clauses_sound:
  ∀l fml.
  isat_fml w (values fml,x) ⇒
  isat_fml w (values (FOLDL (λa b. delete b a) fml l),x)
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_cfml,isat_fml_def]
QED

Theorem delete_xors_sound:
  ∀l x.
  isat_fml w (fml,values x) ⇒
  isat_fml w (fml, values (FOLDL (λa b. delete b a) x l))
Proof
  Induct>>simp[]>>
  rw[]>>
  metis_tac[delete_preserves_isat_xfml,isat_fml_def]
QED

Theorem isat_cfml_insert:
  isat_cfml w (values cfml) ∧
  isat_cclause w c ⇒
  isat_cfml w (values (insert n c cfml))
Proof
  rw[isat_cfml_def,values_def,lookup_insert]>>
  gvs[AllCaseEqs()]>>
  metis_tac[]
QED

Theorem check_xlrup_sound:
  check_xlrup xlrup cfml xfml = SOME (cfml',xfml') ∧
  isat_fml w (values cfml, values xfml) ⇒
  isat_fml w (values cfml', values xfml')
Proof
  rw[check_xlrup_def]>>
  gvs[AllCaseEqs()]
  >- (* deleting clauses by ID *)
    metis_tac[delete_clauses_sound]
  >- ( (* RUP *)
    fs[isat_fml_def]>>
    match_mp_tac isat_cfml_insert>>
    simp[]>>
    match_mp_tac (GEN_ALL is_rup_sound)>>gvs[]>>
    asm_exists_tac>>simp[])
  >- (* deleting XORs by ID *)
    metis_tac[delete_xors_sound]
QED

(* The main operational theorem about check_xlrups *)
Theorem check_xlrups_sound:
  ∀ls cfml xfml.
  check_xlrups ls cfml xfml = SOME (cfml',xfml') ⇒
  (isat_fml w (values cfml, values xfml) ⇒
   isat_fml w (values cfml', values xfml'))
Proof
  Induct>>simp[check_xlrups_def]>>
  ntac 4 strip_tac>>
  every_case_tac>>fs[]>>
  strip_tac>>
  drule check_xlrup_sound>>
  disch_then drule>>
  strip_tac>>
  first_x_assum drule_all>>
  rw[]
QED

(* Build a sptree from a list *)
Definition build_fml_def:
  (build_fml (id:num) [] = LN) ∧
  (build_fml id (cl::cls) =
    insert id cl (build_fml (id+1) cls))
End

Theorem lookup_build_fml:
  ∀ls n acc i.
  lookup i (build_fml n ls) =
  if n ≤ i ∧ i < n + LENGTH ls
  then SOME (EL (i-n) ls)
  else NONE
Proof
  Induct>>rw[build_fml_def,lookup_def,lookup_insert]>>
  `i-n = SUC(i-(n+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem values_build_fml:
  ∀ls id. values (build_fml id ls) = set ls
Proof
  Induct>>fs[build_fml_def,values_def,lookup_def]>>
  fs[EXTENSION]>>
  rw[lookup_insert]>>
  rw[EQ_IMP_THM]
  >- (
    every_case_tac>>fs[]>>
    metis_tac[])
  >- metis_tac[] >>
  first_x_assum(qspecl_then[`id+1`,`x`] mp_tac)>>
  rw[]>>
  fs[lookup_build_fml]>>
  qexists_tac`n`>>simp[]
QED

Definition wf_clause_def:
  wf_clause (C:cclause) ⇔ ¬ MEM 0 C
End

Definition wf_cfml_def:
  wf_cfml cfml ⇔
  ∀C. C ∈ values cfml ⇒ wf_clause C
End

Definition wf_xlrup_def:
  (wf_xlrup (RUP n C i0) = wf_clause C) ∧
  (wf_xlrup _ = T)
End

Theorem wf_cfml_delete_clauses:
  ∀l fml.
  wf_cfml fml ⇒
  wf_cfml (FOLDL (λa b. delete b a) fml l)
Proof
  simp[FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>
  rw[]>>first_x_assum drule>>
  rw[wf_cfml_def]>>
  fs[values_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem wf_cfml_insert:
  wf_cfml fml ∧ wf_clause l ⇒
  wf_cfml (insert n l fml)
Proof
  fs[wf_cfml_def]>>rw[]>>
  gvs[values_def,lookup_insert,AllCaseEqs()]>>
  metis_tac[]
QED

Theorem wf_cfml_check_xlrup:
  wf_cfml cfml ∧ wf_xlrup xlrup ∧
  check_xlrup xlrup cfml xfml = SOME (cfml',xfml') ⇒
  wf_cfml cfml'
Proof
  rw[check_xlrup_def]>>gvs[AllCaseEqs()]
  >-
    metis_tac[wf_cfml_delete_clauses]
  >- (
    fs[wf_xlrup_def]>>
    metis_tac[wf_cfml_insert])
QED

val _ = export_theory ();
