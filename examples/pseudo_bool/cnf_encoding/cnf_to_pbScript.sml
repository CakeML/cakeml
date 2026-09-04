(*
  Parsing CNFs and convert into npbc
*)
Theory cnf_to_pb
Ancestors
  pbc pbc_normalise cnf syntax_helper dimacs
Libs
  preamble

(* cnf and pbc both name their literal constructors Pos/Neg, so every
  literal below is written with its theory qualifier. *)
Definition to_pblit_def:
  (to_pblit (cnf$Pos v) = pbc$Pos v) ∧
  (to_pblit (cnf$Neg v) = pbc$Neg v)
End

Theorem eval_term_to_pblit[simp]:
  eval_term w (1:int,to_pblit l) = 1 ⇔ satisfies_lit w l
Proof
  `∀b:bool. b2i b = 1 ⇔ b` by (Cases>>simp[])>>
  Cases_on`l`>>simp[to_pblit_def,satisfies_lit_def]
QED

(* A clause is canonicalised before it is encoded, so a literal repeated
  in the clause contributes only one term to the constraint *)
Definition clause_to_pbc_def:
  clause_to_pbc cl =
  let ls = MAP (λl. (1:int, to_pblit l)) (canon_clause cl) in
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
  satisfies_clause w cl ⇔
  satisfies_pbc w (clause_to_pbc cl)
Proof
  rw[clause_to_pbc_def]>>
  DEP_REWRITE_TAC[eval_lin_term_coeff_1]>>
  rw[MEM_MAP,satisfies_clause_def,PULL_EXISTS]
QED

Theorem FST_clause_to_pbc[simp]:
  FST (clause_to_pbc x) = PGe
Proof
  rw[clause_to_pbc_def]
QED

Theorem fml_to_pbf_sound:
  satisfies_cnf w (set fml) ⇔
  satisfies w (set (fml_to_pbf fml))
Proof
  rw[fml_to_pbf_def,normalise_thm]>>
  rw[pbcTheory.satisfies_def,satisfies_cnf_def,satisfies_fml_gen_def,
    PULL_EXISTS,MEM_MAP]>>
  metis_tac[clause_to_pbc_sound]
QED

(* Canonicalisation happens before the encoding, so a clause written with
  a repeated literal yields only one term for it *)
Theorem clause_to_pbc_test[local]:
  clause_to_pbc (THE (parse_lits 5 (toks «2 2 4 0»))) =
  (PGe,[(1,pbc$Pos 4); (1,pbc$Pos 2)],1)
Proof
  EVAL_TAC
QED
