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

Definition eval_literal_sem_def:
  eval_literal (w:num assignment) l ⇔ satisfies_lit w l
End

Theorem eval_literal_def:
  eval_literal w (Pos x) = w x ∧
  eval_literal w (Neg x) = ¬w x
Proof
  rw[eval_literal_sem_def, satisfies_lit_def]
QED

Definition eval_clause_sem_def:
  eval_clause (w:num assignment) (c:num clause) ⇔ satisfies_clause w c
End

Definition eval_cnf_sem_def:
  eval_cnf (w:num assignment) (c:num clause list) ⇔
    satisfies_cnf w (set c)
End

Theorem eval_clause_def:
  eval_clause w ClauseEmpty = F ∧
  eval_clause w (ClauseLit l) = eval_literal w l ∧
  eval_clause w (ClauseOr c1 c2) =
    (eval_clause w c1 ∨ eval_clause w c2)
Proof
  rw[eval_clause_sem_def, eval_literal_sem_def, ClauseEmpty_def,
     ClauseLit_def, ClauseOr_def, satisfies_clause_def,
     satisfies_lit_def, MEM_APPEND] >>
  metis_tac[]
QED

Theorem eval_cnf_def:
  eval_cnf w CnfEmpty = T ∧
  eval_cnf w (CnfClause c) = eval_clause w c ∧
  eval_cnf w (CnfAnd c1 c2) =
    (eval_cnf w c1 ∧ eval_cnf w c2)
Proof
  rw[eval_cnf_sem_def, eval_clause_sem_def, CnfEmpty_def,
     CnfClause_def, CnfAnd_def, satisfies_cnf_def,
     satisfies_fml_gen_def] >>
  metis_tac[]
QED

Theorem eval_cnf_list:
  eval_cnf w [] ∧
  (eval_cnf w (c::cs) ⇔ eval_clause w c ∧ eval_cnf w cs)
Proof
  rw[eval_cnf_sem_def, eval_clause_sem_def, satisfies_cnf_def,
     satisfies_fml_gen_def] >>
  metis_tac[]
QED

Theorem eval_cnf_append:
  eval_cnf w (xs ++ ys) ⇔ eval_cnf w xs ∧ eval_cnf w ys
Proof
  rw[eval_cnf_sem_def, satisfies_cnf_def,
     satisfies_fml_gen_def] >>
  metis_tac[]
QED

Theorem eval_clause_append:
  eval_clause w (xs ++ ys) ⇔
    eval_clause w xs ∨ eval_clause w ys
Proof
  rw[eval_clause_sem_def, satisfies_clause_def, MEM_APPEND] >>
  metis_tac[]
QED

Definition unsat_cnf_sem_def:
  unsat_cnf c ⇔ unsatisfiable_cnf (set c)
End

Theorem unsat_cnf_def:
  unsat_cnf c ⇔ ∀w. ¬ eval_cnf w c
Proof
  rw[unsat_cnf_sem_def, unsatisfiable_cnf_def, satisfiable_cnf_def,
     eval_cnf_sem_def]
QED

Definition negate_literal_def:
  negate_literal (Pos x) = Neg x ∧
  negate_literal (Neg x) = Pos x
End
