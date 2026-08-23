(*
  Parsing CNFs and convert into npbc
*)
Theory cnf_to_pb
Ancestors
  pbc pbc_normalise lpr_parsing
Libs
  preamble

(* Convert CNF in int list list representation to pbc *)
Definition clause_to_pbc_def:
  clause_to_pbc cl =
  let ls = MAP (λl.
    if l > 0 then
      (1,Pos (Num (ABS l)))
    else
      (1:int,Neg (Num (ABS l)))) cl in
  (PGe,ls,1:int)
End

Definition fml_to_pbf_def:
  fml_to_pbf fml =
  let pbf = MAP clause_to_pbc fml in
  normalise pbf
End

Theorem iSUM_one_coeff:
  (∀l. MEM l ls ⇒ FST l = 1) ⇒
  iSUM (MAP (eval_term w) ls) ≥ 0
Proof
  Induct_on`ls`>>rw[iSUM_def]>>
  Cases_on`h`>>rw[]>>
  gvs[DISJ_IMP_THM,FORALL_AND_THM]>>
  Cases_on`r`>>simp[]>>
  Cases_on`w a`>>simp[]>>
  intLib.ARITH_TAC
QED

Theorem eval_lin_term_coeff_1:
  (∀l. MEM l ls ⇒ FST l = 1) ⇒
  (eval_lin_term w ls ≥ 1 ⇔
  ∃l. MEM l ls ∧ eval_term w l = 1)
Proof
  simp[eval_lin_term_def]>>
  Induct_on`ls`>>rw[iSUM_def]>>
  Cases_on`h`>>rw[eval_term_def]>>
  gvs[DISJ_IMP_THM,FORALL_AND_THM]>>
  `b2i (lit w r) = 1 ∨ b2i (lit w r) = 0` by (Cases_on`lit w r`>>simp[])
  >- (
    eq_tac>>rw[]
    >- (qexists_tac`(1,r)`>>gvs[eval_term_def])>>
    drule iSUM_one_coeff>>
    disch_then(qspec_then`w` assume_tac)>>
    intLib.ARITH_TAC)>>
  gvs[eval_term_def]>>
  eq_tac>>rw[]>>
  gvs[eval_term_def]>>
  metis_tac[]
QED

Theorem clause_to_pbc_sound:
  wf_clause cl ⇒
  (satisfies_clause w (interp_cclause cl) ⇔
  satisfies_pbc w (clause_to_pbc cl))
Proof
  rw[clause_to_pbc_def,satisfies_pbc_def]>>
  DEP_REWRITE_TAC[eval_lin_term_coeff_1]>>
  rw[MEM_MAP]
  >-
    (IF_CASES_TAC>>simp[])>>
  simp[satSemTheory.satisfies_clause_def,lprTheory.interp_cclause_def,lprTheory.interp_lit_def,PULL_EXISTS]>>
  eq_tac>>rw[]
  >- (
    asm_exists_tac>>simp[]>>
    rw[]>>fs[]>>
    fs[satSemTheory.satisfies_literal_def])>>
  asm_exists_tac>>fs[lprTheory.wf_clause_def]>>
  CONJ_TAC >- metis_tac[]>>
  rw[]>>
  fs[satSemTheory.satisfies_literal_def]>>
  Cases_on`w (Num (ABS l'))`>>fs[]
QED

Theorem FST_clause_to_pbc[simp]:
  FST (clause_to_pbc x) = PGe
Proof
  rw[clause_to_pbc_def]
QED

Theorem fml_to_pbf_sound:
  EVERY wf_clause fml ⇒
  (satisfies w (interp fml) ⇔
  satisfies w (set (fml_to_pbf fml)))
Proof
  rw[fml_to_pbf_def,normalise_thm]>>
  gvs[EVERY_MEM]>>
  rw[pbcTheory.satisfies_def,lprTheory.interp_def,satSemTheory.satisfies_def,
    PULL_EXISTS,MEM_MAP]>>
  metis_tac[clause_to_pbc_sound]
QED

Theorem fml_to_pbf_parse_dimacs:
  parse_dimacs strs = SOME fml ⇒
  (satisfies w (interp fml) ⇔
  satisfies w (set (fml_to_pbf fml)))
Proof
  metis_tac[ fml_to_pbf_sound,parse_dimacs_wf]
QED

