(*
  Semantics of CNFs and general clausal proofs
*)
open preamble miscTheory;

val _ = new_theory "satSem";

(*** Semantics ***

  A literal is drawn from the sum 'a + 'a with the left projection being positive
  and the right projection being negative

  A clause is a set of literals (understood disjunctively)

  A CNF is a set of clauses (understood conjunctively)

  An assignment is a map from 'a to T/F

  A clause is satisfied by an assignment if there is at least one of its literals assigned to true
  A CNF is satisfied by an assignment if all its clauses are satisfied

*)

Type clause = ``:('a + 'a) set``;
Type cnf = ``:'a clause set``;
Type assignment = ``:'a -> bool``;

val negate_literal_def = Define`
  negate_literal l=
  case l of
    INL x => INR x
  | INR x => INL x`

val satisfies_literal_def = Define`
  satisfies_literal (w:'a assignment) l ⇔
  case l of
    INL x => w x
  | INR x => ¬w x`

val satisfies_clause_def = Define`
  satisfies_clause (w:'a assignment) (C:'a clause) ⇔
  ∃l. l ∈ C ∧ satisfies_literal w l`

val satisfies_def = Define`
  satisfies (w:'a assignment) (fml:'a cnf) ⇔
  ∀C. C ∈ fml ⇒ satisfies_clause w C`

val satisfiable_def = Define`
  satisfiable fml ⇔ ∃w. satisfies w fml`

val unsatisfiable_def = Define`
  unsatisfiable fml ⇔ ¬satisfiable fml`

(*** Proofs about the semantics ***)

(* Empty clauses are unsat *)
Theorem empty_clause_imp_unsatisfiable:
  {} ∈ fml ⇒
  unsatisfiable fml
Proof
  rw[unsatisfiable_def,satisfiable_def,satisfies_def,satisfies_clause_def]>>
  asm_exists_tac>>fs[]
QED

Theorem negate_negate[simp]:
  negate_literal(negate_literal l) = l
Proof
  Cases_on`l`>>fs[negate_literal_def]
QED

Theorem negate_negate_o[simp]:
  (negate_literal o negate_literal) = I
Proof
  simp[FUN_EQ_THM]
QED

Theorem negate_literal_11[simp]:
  negate_literal a = negate_literal b ⇔
  a = b
Proof
  Cases_on`a`>>Cases_on`b`>>fs[negate_literal_def]
QED

(* l , -l are duals *)
Theorem satisfies_literal_exclusive:
  (satisfies_literal w l ⇔  ¬satisfies_literal w (negate_literal l))
Proof
  rw[EQ_IMP_THM,satisfies_literal_def]>>
  every_case_tac>>fs[negate_literal_def]>>
  rfs[]
QED

Theorem unsat_negate_satisfies_literal:
  unsatisfiable ({negate_literal l} INSERT fml) ∧
  satisfies w fml ⇒
  satisfies_literal w l
Proof
  rw[unsatisfiable_def,satisfies_def,satisfiable_def]>>
  first_x_assum(qspec_then`w` assume_tac)>>
  fs[]
  >-
    (rw[]>>fs[satisfies_clause_def]>>
    metis_tac[satisfies_literal_exclusive])
  >>
    metis_tac[]
QED

Theorem satisfies_clause_INSERT:
  satisfies_clause w (l INSERT C) ⇔ satisfies_literal w l ∨ satisfies_clause w C
Proof
  rw[satisfies_clause_def]>>
  metis_tac[]
QED

Theorem satisfies_INSERT:
  satisfies w (C INSERT fml) ⇔ satisfies_clause w C ∧ satisfies w fml
Proof
  rw[satisfies_def]>>
  metis_tac[]
QED

Theorem satisfies_SUBSET:
  fml' ⊆ fml ⇒
  satisfies w fml ⇒ satisfies w fml'
Proof
  rw[satisfies_def]>>
  metis_tac[SUBSET_DEF]
QED

Theorem satisfiable_SUBSET:
  fml' ⊆ fml ⇒
  satisfiable fml ⇒ satisfiable fml'
Proof
  fs[satisfiable_def]>>
  metis_tac[satisfies_SUBSET]
QED

Theorem satisfies_union:
  satisfies w (A ∪ B) ⇔ satisfies w A ∧ satisfies w B
Proof
  rw[satisfies_def]>>
  metis_tac[]
QED

Theorem satisfiable_DIFF:
  satisfiable fml ⇒
  satisfiable (fml DIFF clauses)
Proof
  fs[satisfiable_def,satisfies_def]>>
  metis_tac[]
QED

Theorem sing_satisfies_literal:
  {l} ∈ fml ∧
  satisfies w fml ⇒
  satisfies_literal w l
Proof
  rw[satisfies_def]>>
  first_x_assum drule>>
  fs[satisfies_clause_def]
QED

Theorem satisfies_clause_union:
  satisfies_clause w (A ∪ B) ⇔ satisfies_clause w A ∨ satisfies_clause w B
Proof
  fs[satisfies_clause_def]>>
  metis_tac[]
QED

Theorem satisfies_clause_SUBSET:
  C ⊆ C' ∧
  satisfies_clause w C ⇒ satisfies_clause w C'
Proof
  rw[satisfies_clause_def]>>
  metis_tac[SUBSET_DEF]
QED

Theorem UNION_INSERT_EQ:
  A ∪ (B INSERT C) = B INSERT (A ∪ C)
Proof
  fs[EXTENSION]>>metis_tac[]
QED

(*** Clausal proof systems ***
  A clausal proof system is based on the notion of
  redundancy and satisfiability equivalence
*)

val redundant_def = Define`
  redundant fml C ⇔
  (satisfiable fml ⇒ satisfiable (C INSERT fml))`

(*
  par s fml does a partial assignment of s onto fml
  - It filters out all clauses E in fml already satisfied
  - For all remaining clauses, it removes the negated literals in s
  - Note that the partial assignment s should not be contradictory
*)
val par_def = Define`
  par s fml =
  {D | ∃E. E ∈ fml ∧ E ∩ s = {} ∧ D = E DIFF (IMAGE negate_literal s)}`

val consistent_par_def = Define`
  consistent_par s ⇔ s ∩ IMAGE negate_literal s = {}`

val sat_implies_def = Define`
  sat_implies fml fml' ⇔
  ∀w. satisfies w fml ⇒ satisfies w fml'`

(* rules out empty clause and contradictory clauses *)
val satisfiable_clause_def = Define`
  satisfiable_clause C ⇔ ∃w. satisfies_clause w C`

Theorem consistent_par_negate_literals[simp]:
  consistent_par (IMAGE negate_literal s) ⇔
  consistent_par s
Proof
  rw[consistent_par_def,IMAGE_IMAGE]>>
  simp[INTER_COMM]
QED

Theorem consistent_par_sing[simp]:
  consistent_par {l}
Proof
  rw[consistent_par_def,EXTENSION]>>
  Cases_on`l`>>EVAL_TAC
QED

Theorem satisfiable_par:
  satisfiable (par s fml) ⇒
  consistent_par s ⇒
  satisfiable fml
Proof
  rw[satisfiable_def]>>
  (* Follow the new assignment for any new literal *)
  qexists_tac` λl. if INL l ∈ s then T
                   else if INR l ∈ s then F
                   else w l`>>
  fs[satisfies_def]>>rw[]>>
  Cases_on`C DIFF (IMAGE negate_literal s) ∈ par s fml`
  >- (
    first_x_assum drule>>
    strip_tac>>
    fs[satisfies_clause_def]>>
    qexists_tac`l`>>rw[]>>
    fs[satisfies_literal_def]>>
    TOP_CASE_TAC>>fs[]
    >-
      (first_x_assum(qspec_then`INR x` assume_tac)>>rfs[negate_literal_def])
    >>
      (first_x_assum(qspec_then`INL y` assume_tac)>>rfs[negate_literal_def]))
  >>
  last_x_assum (qspec_then`ARB` kall_tac)>>
  fs[par_def]>>
  first_x_assum (qspec_then`C` assume_tac)>>rfs[]>>
  fs[EXTENSION,satisfies_clause_def]>>
  asm_exists_tac>>simp[satisfies_literal_def]>>
  Cases_on`x`>>
  fs[consistent_par_def,EXTENSION]>>
  first_x_assum(qspec_then`INR y` assume_tac)>>rfs[]>>
  pop_assum(qspec_then`INL y` assume_tac)>>fs[negate_literal_def]
QED

Theorem satisfies_par_sub:
  (∀l. l ∈ s ⇒ satisfies_literal w l) ∧
  satisfies w fml ⇒
  satisfies w (par s fml)
Proof
  rw[satisfies_def,par_def]>>
  first_x_assum drule>>
  rw[satisfies_clause_def]>>
  qexists_tac`l`>>simp[]>>
  rw[]>>
  Cases_on`x ∈ s`>>fs[]>>
  first_x_assum drule>>
  metis_tac[satisfies_literal_exclusive]
QED

Theorem par_redundant:
  ∀s.
  consistent_par s ∧ (* s is a partial assignment -- it cannot double assign a literal contradictorily *)
  s ∩ C ≠ {} ∧ (* s satisfies C *)
  sat_implies (par (IMAGE negate_literal C) fml) (par s fml) (* sat implication F|a |= F|w *)
  ⇒
  redundant fml C
Proof
  rw[redundant_def,satisfiable_def]>>
  Cases_on`satisfies_clause w C`
  >-
    metis_tac[satisfies_INSERT]
  >>
  imp_res_tac satisfies_par_sub>>
  pop_assum(qspec_then`IMAGE negate_literal C` mp_tac)>>
  impl_tac >-
    (fs[satisfies_clause_def]>>
    metis_tac[satisfies_literal_exclusive])>>
  fs[sat_implies_def]>>
  rw[]>>first_x_assum drule>>
  rw[]>>
  qexists_tac` λl. if INL l ∈ s then T
                   else if INR l ∈ s then F
                   else w l`>>
  simp[satisfies_INSERT]>>
  rw[]
  >- (
    fs[EXTENSION]>>
    simp[satisfies_clause_def]>>
    asm_exists_tac>>simp[satisfies_literal_def]>>
    TOP_CASE_TAC>>
    fs[consistent_par_def,EXTENSION]>>
    first_x_assum(qspec_then`INR y` assume_tac)>>rfs[]>>
    pop_assum(qspec_then`INL y` mp_tac)>>simp[negate_literal_def])
  >>
  qpat_x_assum `satisfies _ _` mp_tac>>
  ntac 2 (qpat_x_assum `satisfies _ _` kall_tac)>>
  rw[satisfies_def]>>
  Cases_on`C' DIFF (IMAGE negate_literal s) ∈ par s fml`
  >- (
    first_x_assum drule>>
    strip_tac>>
    fs[satisfies_clause_def]>>
    qexists_tac`l`>>rw[]>>
    fs[satisfies_literal_def]>>
    TOP_CASE_TAC>>fs[]
    >-
      (first_x_assum(qspec_then`INR x` assume_tac)>>rfs[negate_literal_def])
    >>
      (first_x_assum(qspec_then`INL y` assume_tac)>>rfs[negate_literal_def]))
  >>
  last_x_assum (qspec_then`ARB` kall_tac)>>
  fs[par_def]>>
  first_x_assum (qspec_then`C'` assume_tac)>>rfs[]>>
  fs[EXTENSION,satisfies_clause_def]>>
  asm_exists_tac>>simp[satisfies_literal_def]>>
  TOP_CASE_TAC>>
  fs[consistent_par_def,EXTENSION]>>
  last_x_assum(qspec_then`INR y` assume_tac)>>rfs[]>>
  pop_assum(qspec_then`INL y` assume_tac)>>fs[negate_literal_def]
QED

Theorem satisfies_extract_par:
  satisfies w fml ⇒
  ∃s.
  consistent_par s ∧
  ∀C. C ∈ fml ⇒ C ∩ s ≠ {}
Proof
  rw[]>>
  (* construct an assignment *)
  qexists_tac` IMAGE (λx. if w x then INL x else INR x) UNIV`>>
  rw[]
  >- (
    simp[consistent_par_def,IMAGE_IMAGE,o_DEF]>>
    CCONTR_TAC>>
    fs[EXTENSION]>>
    every_case_tac>>fs[negate_literal_def]>>
    rw[]>>fs[])
  >>
  fs[satisfies_def]>>first_x_assum drule>>
  fs[satisfies_clause_def]>>rw[EXTENSION]>>
  asm_exists_tac>>simp[]>>
  fs[satisfies_literal_def]>>
  Cases_on`l`>>fs[]
QED

(* converse direction *)
Theorem redundant_par:
  C ≠ {} ∧ consistent_par C ∧
  redundant fml C ⇒
  ∃s.
    consistent_par s ∧
    s ∩ C ≠ {} ∧
    sat_implies (par (IMAGE negate_literal C) fml) (par s fml)
Proof
  rw[redundant_def]>>
  reverse (Cases_on`satisfiable (par (IMAGE negate_literal C) fml)`)
  >- (
    fs[sat_implies_def,satisfiable_def,EXTENSION]>>
    qexists_tac`{x}`>>simp[consistent_par_def,EXTENSION]>>
    Cases_on`x`>>simp[negate_literal_def])
  >>
  drule satisfiable_par>>
  rw[]>>fs[]>>
  ntac 2 (pop_assum kall_tac)>>
  fs[satisfiable_def]>>
  drule satisfies_extract_par>>
  rw[]>>
  asm_exists_tac>>simp[]>>
  rw[]>-
    metis_tac[INTER_COMM]>>
  `par s fml = {}` by
    (simp[par_def,Once EXTENSION]>>
    CCONTR_TAC>>fs[]>>
    metis_tac[])>>
  simp[sat_implies_def,satisfies_def]
QED

(*
  Definition of asymmetric tautologies, roughly:
  fml |- C
*)
val asymmetric_tautology_def = Define`
  asymmetric_tautology fml C ⇔
  unsatisfiable (fml ∪ (IMAGE (λl. {negate_literal l}) C))`

Theorem list_unsat_negate_satisfies_literal:
  ∀ls.
  unsatisfiable (fml ∪ (IMAGE (λl. {negate_literal l}) C)) ∧
  satisfies w fml ⇒
  satisfies_clause w C
Proof
  rw[unsatisfiable_def,satisfiable_def,satisfies_union]>>
  first_x_assum(qspec_then`w` assume_tac)>>
  rfs[]>>
  fs[satisfies_def]>>rw[]>>fs[satisfies_clause_def]>>
  metis_tac[satisfies_literal_exclusive]
QED

(*
  NOTE: asymmetric tautologies are slightly stronger in that they
   actually preserve equivalence
*)
Theorem asymmetric_tautology_satisfies:
  ∀C fml.
  asymmetric_tautology fml C ⇒
  satisfies w fml ⇒
  satisfies w (C INSERT fml)
Proof
  rw[asymmetric_tautology_def]>>
  drule list_unsat_negate_satisfies_literal>>
  disch_then drule>>
  metis_tac[satisfies_INSERT]
QED

Theorem asymmetric_tautology_redundant:
  ∀C fml.
  asymmetric_tautology fml C ⇒
  redundant fml C
Proof
  rw[satisfiable_def,redundant_def]>>
  metis_tac[asymmetric_tautology_satisfies]
QED

Theorem tautology_asymmetric_tautology:
  l ∈ C ∧ negate_literal l ∈ C
  ⇒
  asymmetric_tautology fml C
Proof
  rw[asymmetric_tautology_def,unsatisfiable_def,satisfiable_def,satisfies_def,MEM_MAP]>>
  Cases_on`satisfies_literal w l`
  >-
    (qexists_tac`{negate_literal l}`>>fs[satisfies_clause_def]>>
    metis_tac[satisfies_literal_exclusive])
  >>
    qexists_tac`{l}`>>fs[satisfies_clause_def]>>
    DISJ2_TAC>>
    qexists_tac`negate_literal l`>>simp[]
QED

val delete_literal_def = Define`
  delete_literal l (C:'a clause) = C DIFF {l}`

Theorem delete_literal_preserves_satisfies_clause_imp:
  satisfies_clause w (delete_literal (negate_literal l) C) ⇒
  satisfies_clause w C
Proof
  fs[delete_literal_def,satisfies_clause_def]>>
  metis_tac[]
QED

Theorem delete_literal_preserves_satisfies_clause:
  satisfies_literal w l ⇒
  (satisfies_clause w C ⇔ satisfies_clause w (delete_literal (negate_literal l) C))
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[delete_literal_def,satisfies_clause_def]>>
    metis_tac[satisfies_literal_exclusive]
  )
  >>
    fs[delete_literal_def,satisfies_clause_def]>>
    metis_tac[]
QED

Theorem delete_unit_preserves_satisfies:
  {l} ∈ fml ⇒
  (satisfies w (C INSERT fml) ⇔ satisfies w ((delete_literal (negate_literal l) C) INSERT fml))
Proof
  fs[satisfies_INSERT]>>
  metis_tac[delete_literal_preserves_satisfies_clause,sing_satisfies_literal]
QED

Theorem delete_unit_preserves_satisfiable:
  {l} ∈ fml ⇒
  (satisfiable (C INSERT fml) ⇔ satisfiable ((delete_literal (negate_literal l) C) INSERT fml))
Proof
  fs[satisfiable_def]>>
  metis_tac[delete_unit_preserves_satisfies]
QED

(* Definition of resolution asymmetric tautology, roughly:
  For some l ∈ C, for all D containing ~l,
    fml |- C ∪ (D - {~l})
 *)
val resolution_asymmetric_tautology_def = Define`
  resolution_asymmetric_tautology fml C ⇔
  ∃l. l ∈ C ∧
  ∀D. D ∈ fml ∧ negate_literal l ∈ D ⇒
    asymmetric_tautology fml (C ∪ delete_literal (negate_literal l) D)`

Theorem not_consistent_par_redundant:
  ¬consistent_par C ⇒
  redundant fml C
Proof
  rw[consistent_par_def]>>
  rw[redundant_def,satisfiable_def,satisfies_INSERT]>>
  fs[EXTENSION]>>
  qexists_tac`w`>>simp[]>>
  simp[satisfies_clause_def]>>
  metis_tac[satisfies_literal_exclusive]
QED

Theorem consistent_par_DIFF_INSERT:
  consistent_par C ⇒
  consistent_par (l INSERT IMAGE negate_literal (C DIFF {l}))
Proof
  simp[consistent_par_def]>>
  CCONTR_TAC>>fs[EXTENSION]>>
  rw[]>>fs[]
  >-
    (Cases_on`l`>>fs[negate_literal_def])
  >>
  metis_tac[]
QED

Theorem asymmetric_tautology_union_clause:
  consistent_par C ∧
  asymmetric_tautology fml (C ∪ D) ∧
  D ∩ IMAGE negate_literal C = {} ⇒
  asymmetric_tautology (par (IMAGE negate_literal C) fml) D
Proof
  rw[asymmetric_tautology_def,unsatisfiable_def,satisfiable_def,satisfies_def]>>
  first_x_assum(qspec_then
    `λl. if INL l ∈ IMAGE negate_literal C then T
         else if INR l ∈ IMAGE negate_literal C then F
         else w l` assume_tac) >>
  fs[]
  >- (
    qexists_tac`C' DIFF C`>>rw[]
    >-
      (DISJ1_TAC>>simp[par_def]>>asm_exists_tac>>simp[IMAGE_IMAGE]>>
      fs[satisfies_clause_def,EXTENSION]>>
      rw[]>>fs[]>>
      first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
      Cases_on`x`>>fs[satisfies_literal_def]>>
      cheat)
    >>
    fs[satisfies_clause_def]>>rw[]>>
    first_x_assum(qspec_then`l` assume_tac)>>fs[]>>
    Cases_on`l`>>fs[satisfies_literal_def]>>
    fs[consistent_par_def,EXTENSION]>>
    (* contradict consistent_par *)
    cheat)
  >-
    (rfs[satisfies_clause_def,Once satisfies_literal_exclusive]>>
    pop_assum mp_tac>>
    Cases_on`l`>>simp[satisfies_literal_def]>>
    rw[]>>fs[]>>
    (* discard goal: contradict consistent_par *)
    cheat)
  >>
    qexists_tac`C'`>>simp[]>>
    rfs[satisfies_clause_def,Once satisfies_literal_exclusive]>>
    Cases_on`l`>>fs[satisfies_literal_def]>>
    fs[EXTENSION]>>
    metis_tac[]
QED

Theorem asymmetric_tautology_union_clause2:
  consistent_par C ∧
  asymmetric_tautology fml (C ∪ D) ∧
  D ∩ IMAGE negate_literal C = {} ⇒
  asymmetric_tautology (par (IMAGE negate_literal C) fml) (D DIFF C)
Proof
  rw[]>>
  match_mp_tac asymmetric_tautology_union_clause>>fs[]>>
  `C ∪ (D DIFF C) = C ∪ D` by
    (fs[EXTENSION]>>
    metis_tac[])>>
  simp[]>>
  simp[DIFF_INTER]
QED

Theorem resolution_asymmetric_tautology_redundant:
  ∀C fml.
  resolution_asymmetric_tautology fml C ⇒
  redundant fml C
Proof
  rw[]>>
  fs[resolution_asymmetric_tautology_def]>>
  reverse (Cases_on`consistent_par C`)
  >-
    metis_tac[not_consistent_par_redundant]
  >>
  match_mp_tac par_redundant>>
  qexists_tac`l INSERT (IMAGE negate_literal (C DIFF {l}))`>>
  rw[]
  >-
    metis_tac[consistent_par_DIFF_INSERT]
  >-
    (simp[EXTENSION]>>
    qexists_tac`l`>>simp[])
  >>
  rw[sat_implies_def]>>
  fs[satisfies_def]>>
  rw[par_def]>>
  reverse (Cases_on`negate_literal l ∈ E`)
  >- (
    first_x_assum match_mp_tac>>
    simp[par_def]>>
    asm_exists_tac>>
    rw[]
    >-
      (fs[EXTENSION]>>
      CCONTR_TAC>>fs[]>>
      first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
      rw[]>>fs[])
    >>
      simp[IMAGE_IMAGE]>>
      simp[EXTENSION]>>
      rw[]>>simp[]>>
      rw[EQ_IMP_THM]>>fs[EXTENSION]>>
      metis_tac[])
  >>
  first_x_assum drule>>
  strip_tac>>rfs[]>>
  simp[IMAGE_IMAGE]>>
  drule asymmetric_tautology_union_clause2>>
  disch_then drule>>
  impl_tac >- (
    fs[delete_literal_def,EXTENSION]>>
    metis_tac[])>>
  strip_tac>>
  drule asymmetric_tautology_satisfies>>
  simp[satisfies_def]>>
  disch_then drule>>
  strip_tac>>
  first_x_assum match_mp_tac>>
  DISJ1_TAC>>
  simp[delete_literal_def,EXTENSION]>>
  rw[EQ_IMP_THM]>>
  fs[EXTENSION]>>
  metis_tac[]
QED

val _ = export_theory ();
