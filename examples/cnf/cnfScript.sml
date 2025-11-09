(*
  Syntax and semantics of CNF
*)
Theory cnf
Ancestors
  misc
Libs
  preamble

(* TODO: misc? *)
Theorem range_map:
  misc$range (map f fml) =
  IMAGE f (range fml)
Proof
  rw[miscTheory.range_def,EXTENSION,lookup_map]>>
  metis_tac[]
QED

Theorem map_I:
  ∀t.
  sptree$map I t = t
Proof
  Induct>>rw[map_def]
QED

Theorem NOT_NONE_SOME_EXISTS:
  x ≠ NONE ⇔ ?y. x = SOME y
Proof
  Cases_on`x`>>rw[]
QED

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
  satisfies_fml_gen sem w (range fml) ⇒
  satisfies_fml_gen sem w (range (delete n fml))
Proof
  rw[satisfies_fml_gen_def]>>
  fs[range_def,lookup_delete,PULL_EXISTS]>>
  metis_tac[]
QED

Definition delete_ids_def:
  delete_ids fml ls =
  FOLDL (\a b. sptree$delete b a) fml ls
End

Theorem satisfies_fml_gen_delete_ids:
  satisfies_fml_gen f w (range fml) ⇒
  satisfies_fml_gen f w (range (delete_ids fml ls))
Proof
  simp[delete_ids_def]>>
  qid_spec_tac`fml`>>
  Induct_on`ls`>>rw[]>>
  first_x_assum irule>>
  metis_tac[satisfies_fml_gen_delete]
QED

Theorem satisfies_fml_gen_insert:
  satisfies_fml_gen f w (range fml) ∧
  f w vc ⇒
  satisfies_fml_gen f w (range (insert n vc fml))
Proof
  rw[satisfies_fml_gen_def]>>
  gvs[range_def,PULL_EXISTS,lookup_insert,AllCaseEqs()]>>
  metis_tac[]
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

Theorem range_build_fml:
  ∀ls id. range (build_fml id ls) = set ls
Proof
  Induct>>fs[build_fml_def,range_def,lookup_def]>>
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


