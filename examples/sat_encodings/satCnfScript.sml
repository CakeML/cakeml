(*
  CNF construction helpers for the SAT encoders
*)
Theory satCnf
Ancestors
  cnf ASCIInumbers
Libs
  preamble

Type name = “:num”;
Type literal = “:num lit”;

Definition ClauseEmpty_def:
  ClauseEmpty = ([]:num clause)
End

Definition ClauseLit_def:
  ClauseLit l = [l:num lit]
End

Definition ClauseOr_def:
  ClauseOr (c1:num clause) c2 = c1 ++ c2
End

Definition CnfEmpty_def:
  CnfEmpty = ([]:num clause list)
End

Definition CnfClause_def:
  CnfClause (c:num clause) = [c]
End

Definition CnfAnd_def:
  CnfAnd (c1:num clause list) c2 = c1 ++ c2
End

Theorem satisfies_clause_constructors:
  ¬ satisfies_clause w ClauseEmpty ∧
  (satisfies_clause w (ClauseLit l) ⇔ satisfies_lit w l) ∧
  (satisfies_clause w (ClauseOr c1 c2) ⇔
    satisfies_clause w c1 ∨ satisfies_clause w c2)
Proof
  rw[ClauseEmpty_def, ClauseLit_def, ClauseOr_def,
     satisfies_clause_def, MEM_APPEND] >>
  metis_tac[]
QED

Theorem satisfies_cnf_constructors:
  satisfies_cnf w (set CnfEmpty) ∧
  (satisfies_cnf w (set (CnfClause c)) ⇔ satisfies_clause w c) ∧
  (satisfies_cnf w (set (CnfAnd c1 c2)) ⇔
    satisfies_cnf w (set c1) ∧ satisfies_cnf w (set c2))
Proof
  rw[CnfEmpty_def, CnfClause_def, CnfAnd_def, satisfies_cnf_def,
     satisfies_fml_gen_def] >>
  metis_tac[]
QED

Theorem satisfies_clause_append:
  satisfies_clause w (xs ++ ys) ⇔
    satisfies_clause w xs ∨ satisfies_clause w ys
Proof
  rw[satisfies_clause_def, MEM_APPEND] >>
  metis_tac[]
QED

Definition negate_literal_def:
  negate_literal (Pos x) = Neg x ∧
  negate_literal (Neg x) = Pos x
End
