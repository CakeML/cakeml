(*
   Verification of longest common subsequence algorithms.
*)
open preamble miscTheory;

val _ = new_theory "lrat";

(*** Implementation ***

  The concrete notion of a literal is an integer
  To reduce symmetries the literal "0" is just lumped in as well although it doesn't have a -0

  A clause is a list of literals and a formula is a set of clauses

*)
val _ = type_abbrev("clause" , ``:int list``);

(* NOTE: not efficient! *)
val delete_literal_def = Define`
  delete_literal l (C:clause) =
    FILTER (λi. i  <> l) C `

val _ = Datatype`
  lratstep =
    Delete (num list) (* Clauses to delete *)
  | RAT num clause (num list)`
    (* TODO: For now, an Asymmetric Tautology step
      AT n C i0
      i0 is a list of clause IDs
      n is the new id of the clause C
    *)

val _ = type_abbrev("lrat" , ``:lratstep list``);

val delete_clauses_def = Define`
  delete_clauses cl fml =
    FOLDR delete fml cl`

(* asymmetric tautology step *)
val is_AT_def = Define`
  (is_AT fml [] (C:clause) = F) ∧
  (is_AT fml (i::is) C =
  case lookup i fml of
    NONE => F
  | SOME Ci =>
  let D = FILTER (λx. ¬ MEM x C) Ci
  in
  case D of
    [] => T
  | [d] => is_AT fml is (-d::C)
  | _ => F)`

val wf_clause_def = Define`
  wf_clause (C:clause) ⇔ ¬MEM 0 C`

(* Run the LRAT checker on fml, returning an  *)
val check_lrat_def = Define`
  (check_lrat [] fml = SOME fml) ∧
  (check_lrat (step::steps) fml =
    case step of
      Delete cl =>
      check_lrat steps (delete_clauses cl fml)
    | RAT n C cl =>
      if wf_clause C ∧ is_AT fml cl C
      (* Are overwrites allowed???
      if n ∈ domain fml then NONE
      else *)
      (* TODO: insert check that it is indeed okay *)
      then check_lrat steps (insert n C fml)
      else NONE)`

(*** Semantics ***

  For now, the semantics is rather low level
  It would be worth defining a more abstract notion of this that doesn't mess
  concretely with -1,1 etc.

  An assignment is a map from the natural numbers (including 0) to T/F

  A clause is satisfied if there is at least one literal assigned to true

  A CNF is satisfied if there is at all clauses are satisfied

*)

val _ = type_abbrev("cnf" , ``:clause set``);
val _ = type_abbrev("assignment" , ``:num -> bool``);

val satisfies_literal_def = Define`
  satisfies_literal (w:assignment) l ⇔
  if l ≥ 0 then w (Num (ABS l))
  else ~w (Num (ABS l))`

val satisfies_clause_def = Define`
  satisfies_clause (w:assignment) (C:clause) ⇔
  ∃l. MEM l C ∧ satisfies_literal w l`

val satisfies_def = Define`
  satisfies (w:assignment) (fml:cnf) ⇔
  ∀C. C ∈ fml ⇒ satisfies_clause w C`

val satisfiable_def = Define`
  satisfiable fml ⇔ ∃w. satisfies w fml`

val unsatisfiable_def = Define`
  unsatisfiable fml ⇔ ¬satisfiable fml`

(*** Proofs about abstract notion ***)

(* Empty clauses are unsat *)
Theorem empty_clause_imp_unsatisfiable:
  [] ∈ fml ⇒
  unsatisfiable fml
Proof
  rw[unsatisfiable_def,satisfiable_def,satisfies_def,satisfies_clause_def]>>
  qexists_tac`[]`>> simp[]
QED

(* Deleting any set of clauses preserves satisfiability *)
Theorem satisfies_literal_exclusive:
  l ≠ 0 ⇒
  (satisfies_literal w l ⇔  ¬satisfies_literal w (-l))
Proof
  rw[EQ_IMP_THM,satisfies_literal_def]>>
  fs[] >> `F` by intLib.ARITH_TAC
QED

(* Asymmetric tautologies *)
val asymmetric_tautology_def = Define`
  asymmetric_tautology fml C ⇔
  ¬MEM 0 C ∧
  unsatisfiable (fml ∪ set (MAP (λl. [-l]) C))`

Theorem unsat_negate_satisfies_literal:
  l ≠ 0 ∧ unsatisfiable ([-l] INSERT fml) ∧
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

Theorem satisfies_union:
  satisfies w (A ∪ B) ⇔ satisfies w A ∧ satisfies w B
Proof
  rw[satisfies_def]>>
  metis_tac[]
QED

Theorem satisfies_INSERT:
  satisfies w (C INSERT fml) ⇔ satisfies_clause w C ∧ satisfies w fml
Proof
  rw[satisfies_def]>>
  metis_tac[]
QED

Theorem satisfiable_SUBSET:
  fml' ⊆ fml ⇒
  satisfiable fml ⇒ satisfiable fml'
Proof
  fs[satisfiable_def,satisfies_def]>>
  metis_tac[SUBSET_DEF]
QED

Theorem list_unsat_negate_satisfies_literal:
  ∀ls.
  ¬MEM 0 ls ∧ unsatisfiable (fml ∪ set (MAP (λl. [-l]) ls)) ∧
  satisfies w fml ⇒
  satisfies_clause w ls
Proof
  rw[unsatisfiable_def,satisfiable_def,satisfies_union]>>
  first_x_assum(qspec_then`w` assume_tac)>>
  rfs[]>>
  fs[satisfies_def,MEM_MAP]>>rw[]>>fs[satisfies_clause_def]>>
  metis_tac[satisfies_literal_exclusive]
QED

Theorem asymmetric_tautology_satisfiable:
  ∀C fml.
  asymmetric_tautology fml C ⇒
  satisfiable fml ⇒
  satisfiable (C INSERT fml)
Proof
  rw[satisfiable_def,asymmetric_tautology_def]>>
  drule list_unsat_negate_satisfies_literal>>
  disch_then drule>>
  metis_tac[satisfies_INSERT]
QED

Theorem satisfiable_DIFF:
  satisfiable fml ⇒
  satisfiable (fml DIFF clauses)
Proof
  fs[satisfiable_def,satisfies_def]>>
  metis_tac[]
QED

Theorem delete_literal_preserves_satisfies_clause:
  l ≠ 0 ∧ satisfies_literal w l ⇒
  (satisfies_clause w C ⇔ satisfies_clause w (delete_literal (-l) C))
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[delete_literal_def,satisfies_clause_def,MEM_FILTER]>>
    metis_tac[satisfies_literal_exclusive]
  )
  >>
    fs[delete_literal_def,satisfies_clause_def,MEM_FILTER]>>
    metis_tac[]
QED

Theorem sing_satisfies_literal:
  [l] ∈ fml ∧
  satisfies w fml ⇒
  satisfies_literal w l
Proof
  rw[satisfies_def]>>
  first_x_assum drule>>
  fs[satisfies_clause_def]
QED

Theorem delete_unit_preserves_satisfies:
  l ≠ 0 ∧ [l] ∈ fml ⇒
  (satisfies w (C INSERT fml) ⇔ satisfies w ((delete_literal (-l) C) INSERT fml))
Proof
  fs[satisfies_INSERT]>>
  metis_tac[delete_literal_preserves_satisfies_clause,sing_satisfies_literal]
QED

Theorem delete_unit_preserves_satisfiable:
  l ≠ 0 ∧ [l] ∈ fml ⇒
  (satisfiable (C INSERT fml) ⇔ satisfiable ((delete_literal (-l) C) INSERT fml))
Proof
  fs[satisfiable_def]>>
  metis_tac[delete_unit_preserves_satisfies]
QED

val values_def = Define`
  values s = {v | ∃n. lookup n s = SOME v}`

val wf_fml_def = Define`
  wf_fml fml ⇔ ∀C. C ∈ values fml ⇒ wf_clause C`

Theorem filter_unit_preserves_unsatisfiable:
  ∀C.
  wf_clause (C:clause) ∧
  set (MAP (λl. [-l]) C) ⊆ fml ⇒
  (unsatisfiable (D INSERT fml) ⇔ unsatisfiable ((FILTER (λx. ¬MEM x C) D) INSERT fml))
Proof
  Induct>>rw[]>>
  fs[wf_clause_def]>>
  simp[GSYM FILTER_FILTER,GSYM delete_literal_def]>>
  `-h ≠ 0` by fs[]>>
  drule delete_unit_preserves_satisfiable>>
  disch_then drule>>
  simp[]>>
  metis_tac[unsatisfiable_def]
QED

Theorem UNION_INSERT_EQ:
  A ∪ (B INSERT C) = B INSERT (A ∪ C)
Proof
  fs[EXTENSION]>>metis_tac[]
QED

(* Implementation *)
Theorem is_AT_imp_asymmetric_tautology:
  ∀is fml C.
  wf_fml fml ∧ wf_clause C ⇒
  is_AT fml is C ⇒
  asymmetric_tautology (values fml) C
Proof
  Induct>>fs[is_AT_def]>>
  ntac 4 strip_tac>>
  drule filter_unit_preserves_unsatisfiable>>
  every_case_tac>>fs[]
  >-
    (fs[asymmetric_tautology_def]>>
    rw[] >- fs[wf_clause_def]>>
    qmatch_goalsub_abbrev_tac`unsatisfiable fml'`>>
    `fml' = x INSERT fml'` by
      (match_mp_tac (GSYM ABSORPTION_RWT)>>
      fs[Abbr`fml'`,values_def]>>
      metis_tac[])>>
    pop_assum SUBST1_TAC>>
    first_x_assum(qspecl_then[`fml'`,`x`] mp_tac)>>
    impl_tac
    >-
      simp[Abbr`fml'`]
    >>
    simp[]>>disch_then kall_tac>>
    match_mp_tac empty_clause_imp_unsatisfiable>>
    fs[])
  >>
    strip_tac>>last_x_assum drule>>
    `wf_clause (-h'::C)` by
      (fs[wf_clause_def,wf_fml_def]>>
      fs[values_def,PULL_EXISTS]>>
      first_x_assum drule>>
      `MEM h' (FILTER (λx. ¬MEM x C) x )` by fs[]>>
      rw[]>>`h' ≠ 0` by metis_tac[MEM_FILTER]>>
      intLib.ARITH_TAC)>>
    disch_then drule>>simp[]>>
    simp[asymmetric_tautology_def]>>
    rw[]>>fs[]>>
    qmatch_goalsub_abbrev_tac`unsatisfiable fml'`>>
    first_x_assum(qspec_then `fml'` mp_tac)>>
    disch_then(qspec_then`x` mp_tac)>> impl_tac>- simp[Abbr`fml'`]>>
    `x INSERT fml' = fml'` by
      (match_mp_tac ABSORPTION_RWT>>
      fs[Abbr`fml'`,values_def]>>
      metis_tac[])>>
    simp[]>>
    fs[Abbr`fml'`]>>
    disch_then kall_tac>>
    fs[UNION_INSERT_EQ]
QED

(* Deletion preserves sat: if C is satisfiable, then deleting clauses from C keeps satisfiability *)
Theorem values_delete:
  values (delete h v) ⊆ values v
Proof
  simp[values_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem delete_preserves_satisfiable:
   satisfiable (values C) ⇒ satisfiable (values (delete n C))
Proof
  match_mp_tac satisfiable_SUBSET>>
  metis_tac[values_delete]
QED

Theorem delete_clauses_sound:
  ∀l fml. satisfiable (values fml) ⇒
  satisfiable (values (delete_clauses l fml))
Proof
  simp[delete_clauses_def]>>
  Induct>>simp[]>>
  metis_tac[delete_preserves_satisfiable]
QED

Theorem wf_fml_delete_clauses:
  ∀l fml.
  wf_fml fml ⇒
  wf_fml (delete_clauses l fml)
Proof
  simp[delete_clauses_def]>>
  Induct>>simp[]>>
  fs[wf_fml_def]>>rw[]>>
  first_x_assum drule>>
  `C ∈ values (FOLDR delete fml l)` by
    metis_tac[values_delete,SUBSET_DEF]>>
  fs[]
QED

Theorem values_insert:
  C ∈ values (insert n l fml) ⇒ C ∈ values fml ∨ C = l
Proof
  fs[values_def,lookup_insert]>>
  rw[]>>
  every_case_tac>>fs[]>>
  metis_tac[]
QED

Theorem values_insert2:
  values (insert n l fml) ⊆ l INSERT values fml
Proof
  rw[SUBSET_DEF]>>
  metis_tac[values_insert]
QED

Theorem wf_fml_insert:
  wf_fml fml ∧ wf_clause l ⇒
  wf_fml (insert n l fml)
Proof
  fs[wf_fml_def]>>rw[]>>
  drule values_insert>>
  metis_tac[]
QED

(* The main theorem *)
Theorem check_lrat_sound:
  ∀lrat fml fml'.
  wf_fml fml ∧
  check_lrat lrat fml = SOME fml' ⇒
  satisfiable (values fml) ⇒ satisfiable (values fml')
Proof
  Induct >> fs[check_lrat_def]>>
  Cases
  >- (
    simp[]>>
    metis_tac[delete_clauses_sound,wf_fml_delete_clauses])
  >>
    rw[]>>
    drule wf_fml_insert>> disch_then drule>>
    disch_then(qspec_then`n`assume_tac)>>
    first_x_assum drule>>
    disch_then drule>>
    disch_then match_mp_tac>>
    last_x_assum assume_tac>>
    drule is_AT_imp_asymmetric_tautology>>
    disch_then drule>>
    disch_then drule>>
    strip_tac>>drule (GEN_ALL asymmetric_tautology_satisfiable)>>
    disch_then drule>>
    match_mp_tac satisfiable_SUBSET>>
    metis_tac[values_insert2]
QED

val _ = export_theory ();
