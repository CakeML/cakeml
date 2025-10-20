(*
  Syntax and semantics of CNF
*)
Theory cnf
Ancestors
  misc
Libs
  preamble

Datatype:
  lit = Pos 'a | Neg 'a
End

(* Clauses and their semantics *)
Type clause = ``:'a lit list``;
Type assignment = ``:'a -> bool``;

Definition satisfies_lit_def:
  satisfies_lit (w:'a assignment) l ⇔
  (case l of Pos x => w x | Neg x => ¬w x)
End

Definition satisfies_clause_def:
  satisfies_clause w (c:'a clause) ⇔
  (∃l. l ∈ set c ∧ satisfies_lit w l)
End

Definition satisfies_fml_gen_def:
  satisfies_fml_gen sem w fml ⇔
  (∀c. c ∈ fml ⇒ sem w c)
End

Definition satisfies_cnf_def:
  satisfies_cnf = satisfies_fml_gen satisfies_clause
End

Definition satisfiable_cnf_def:
  satisfiable_cnf fml ⇔
  (∃w. satisfies_cnf w fml)
End

Definition unsatisfiable_cnf_def:
  unsatisfiable_cnf fml ⇔
  ¬ satisfiable_cnf fml
End

(* Free variables *)
Definition lit_var_def:
  (lit_var (Pos v) = v) ∧
  (lit_var (Neg v) = v)
End

Definition clause_vars_def:
  (clause_vars (c:'a clause) = set (MAP lit_var c))
End

(* Helpers *)
Theorem satisfies_fml_gen_lookup:
  lookup h fml = SOME c ∧
  satisfies_fml_gen sem w (range fml) ⇒
  sem w c
Proof
  rw[satisfies_fml_gen_def,range_def]>>
  metis_tac[]
QED

Theorem satisfies_fml_gen_delete:
  satisfies_fml_gen sem w (range C) ⇒
  satisfies_fml_gen sem w (range (delete n C))
Proof
  rw[satisfies_fml_gen_def]>>
  fs[range_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

