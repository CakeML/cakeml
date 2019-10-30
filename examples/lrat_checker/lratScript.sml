(*
   Verification of LRAT checker
*)
open preamble miscTheory;

val _ = new_theory "lrat";

(*** Semantics ***

  For now, the semantics is rather low level
  It would be worth defining a more abstract notion of this that doesn't mess
  concretely with -1,1 etc.

  A clause is a list of literals (ints)
  A CNF is a set of clauses

  An assignment is a map from the natural numbers (including 0) to T/F

  A clause is satisfied by an assignment if there is at least one of its literals assigned to true
  A CNF is satisfied by an assignment if all its clauses are satisfied
*)

Type clause = ``:int list``;
Type cnf = ``:clause set``;
Type assignment = ``:num -> bool``;

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

(*** Proofs about the semantics ***)

(* General stuff about satisfiability *)

(* Empty clauses are unsat *)
Theorem empty_clause_imp_unsatisfiable:
  [] ∈ fml ⇒
  unsatisfiable fml
Proof
  rw[unsatisfiable_def,satisfiable_def,satisfies_def,satisfies_clause_def]>>
  qexists_tac`[]`>> simp[]
QED

(* l , -l are duals *)
Theorem satisfies_literal_exclusive:
  l ≠ 0 ⇒
  (satisfies_literal w l ⇔  ¬satisfies_literal w (-l))
Proof
  rw[EQ_IMP_THM,satisfies_literal_def]>>
  fs[] >> `F` by intLib.ARITH_TAC
QED

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
  [l] ∈ fml ∧
  satisfies w fml ⇒
  satisfies_literal w l
Proof
  rw[satisfies_def]>>
  first_x_assum drule>>
  fs[satisfies_clause_def]
QED

Theorem satisfies_clause_append:
  satisfies_clause w (A++B) ⇔ satisfies_clause w A ∨ satisfies_clause w B
Proof
  fs[satisfies_clause_def]>>
  metis_tac[]
QED

Theorem satisfies_clause_SUBSET:
  (∀l. MEM l (C:clause) ⇒ MEM l C') ⇒
  satisfies_clause w C ⇒ satisfies_clause w C'
Proof
  rw[satisfies_clause_def]>>
  metis_tac[]
QED

Theorem UNION_INSERT_EQ:
  A ∪ (B INSERT C) = B INSERT (A ∪ C)
Proof
  fs[EXTENSION]>>metis_tac[]
QED

val wf_clause_def = Define`
  wf_clause (C:clause) ⇔ ¬MEM 0 C`

(* Definition of asymmetric tautologies *)
val asymmetric_tautology_def = Define`
  asymmetric_tautology fml C ⇔
  wf_clause C ∧
  unsatisfiable (fml ∪ set (MAP (λl. [-l]) C))`

Theorem list_unsat_negate_satisfies_literal:
  ∀ls.
  wf_clause ls ∧
  unsatisfiable (fml ∪ set (MAP (λl. [-l]) ls)) ∧
  satisfies w fml ⇒
  satisfies_clause w ls
Proof
  rw[unsatisfiable_def,satisfiable_def,satisfies_union,wf_clause_def]>>
  first_x_assum(qspec_then`w` assume_tac)>>
  rfs[]>>
  fs[satisfies_def,MEM_MAP]>>rw[]>>fs[satisfies_clause_def]>>
  metis_tac[satisfies_literal_exclusive]
QED

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

Theorem asymmetric_tautology_satisfiable:
  ∀C fml.
  asymmetric_tautology fml C ⇒
  satisfiable fml ⇒
  satisfiable (C INSERT fml)
Proof
  rw[satisfiable_def]>>
  metis_tac[asymmetric_tautology_satisfies]
QED

Theorem asymmetric_tautology_set_satisfies:
  ∀Cs fml.
  (∀C. C ∈ Cs ⇒ asymmetric_tautology fml C) ⇒
  satisfies w fml ⇒
  satisfies w (Cs ∪ fml)
Proof
  rw[satisfies_union]>>
  rw[satisfies_def]>>
  first_x_assum drule>>
  strip_tac>>
  drule asymmetric_tautology_satisfies>>
  disch_then drule>>
  simp[satisfies_INSERT]
QED

Theorem tautology_asymmetric_tautology:
  wf_clause C ∧
  MEM l C ∧ MEM (-l) C
  ⇒
  asymmetric_tautology fml C
Proof
  rw[asymmetric_tautology_def,unsatisfiable_def,satisfiable_def,satisfies_def,MEM_MAP]>>
  `l ≠ 0` by metis_tac[wf_clause_def]>>
  Cases_on`satisfies_literal w l`
  >-
    (qexists_tac`[-l]`>>fs[satisfies_clause_def]>>
    metis_tac[satisfies_literal_exclusive])
  >>
    qexists_tac`[l]`>>fs[satisfies_clause_def]>>
    DISJ2_TAC>>
    qexists_tac`-l`>>simp[]
QED

(* TODO: NOT efficient *)
val delete_literal_def = Define`
  delete_literal l (C:clause) =
    FILTER (λi. i  <> l) C `

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

(* Definition of resolution asymmetric tautology *)
val resolution_asymmetric_tautology_def = Define`
  resolution_asymmetric_tautology fml C ⇔
  ¬MEM 0 C ∧
  (asymmetric_tautology fml C ∨
  ∃l. MEM l C ∧
  ∀D. D ∈ fml ∧ MEM (-l) D ⇒
    asymmetric_tautology fml (C ++ delete_literal (-l) D))`

(* soundness of resolution step *)
Theorem resolution_sound:
  l ≠ 0 ∧ (l::xs) ∈ fml ∧ ((-l)::ys) ∈ fml ⇒
  (satisfies w fml ⇔ satisfies w ((xs++ys) INSERT fml))
Proof
  simp[EQ_IMP_THM]>>strip_tac>>strip_tac
  >- (
    rw[satisfies_INSERT]>>
    fs[satisfies_def]>>
    first_assum drule>>
    first_x_assum(qspec_then `l::xs` mp_tac)>>fs[]>>
    rw[satisfies_clause_def,MEM_FILTER]>>
    metis_tac[satisfies_literal_exclusive])
  >>
    match_mp_tac satisfies_SUBSET>>
    fs[SUBSET_DEF]
QED

Theorem resolution_sound1:
  l ≠ 0 ∧ xs ∈ fml ∧ ys ∈ fml ∧
  MEM l xs ∧ MEM (-l) ys ⇒
  (satisfies w fml ⇔ satisfies w ((xs++delete_literal (-l) ys) INSERT fml))
Proof
  simp[EQ_IMP_THM]>>strip_tac>>strip_tac
  >- (
    rw[satisfies_INSERT]>>
    fs[satisfies_def]>>
    first_assum drule>>
    first_x_assum(qspec_then `xs` mp_tac)>>fs[]>>
    rw[satisfies_clause_def]>>
    metis_tac[satisfies_literal_exclusive])
  >>
    match_mp_tac satisfies_SUBSET>>
    fs[SUBSET_DEF]
QED

val flip_literal_def = Define`
  flip_literal l (w:assignment) =
  λv. if v = Num (ABS l) then ¬w (Num (ABS l)) else w v`

Theorem flip_literal_eq_neg:
  flip_literal l w = flip_literal (-l) w
Proof
  simp[flip_literal_def]
QED

Theorem flip_literal_flips:
  l ≠ 0 ⇒
  (satisfies_literal w l ⇔ ¬(satisfies_literal (flip_literal l w) l))
Proof
  rw[satisfies_literal_def,flip_literal_def]
QED

Theorem flip_literal_unaffected:
  l ≠ 0 ∧
  satisfies_literal w l ∧
  satisfies_clause w C ∧ ¬ MEM l C ⇒
  satisfies_clause (flip_literal l w ) C
Proof
  rw[satisfies_clause_def,satisfies_literal_def]>>
  asm_exists_tac>>fs[]>>rw[]>>fs[]>>
  fs[flip_literal_def]>>
  `l ≠ l'` by metis_tac[]>>
  intLib.ARITH_TAC
QED

Theorem resolution_asymmetric_tautology_satisfiable:
  ∀C fml w.
  resolution_asymmetric_tautology fml C ⇒
  satisfiable fml ⇒
  satisfiable (C INSERT fml)
Proof
  rw[resolution_asymmetric_tautology_def]
  >-
    metis_tac[asymmetric_tautology_satisfiable]
  >>
  fs[satisfiable_def]>>
  Cases_on`satisfies_clause w C`
  >-
    metis_tac[satisfies_INSERT]>>
  qabbrev_tac`Ds = IMAGE (λD. C ++ delete_literal (-l) D) { D | D ∈ fml∧  MEM (-l) D}`>>
  `∀D. D ∈ Ds ⇒ asymmetric_tautology fml D` by
    (rw[]>>fs[Abbr`Ds`])>>
  drule asymmetric_tautology_set_satisfies >>
  disch_then drule>>
  strip_tac>>
  fs[satisfies_union]>>
  qabbrev_tac`w' = flip_literal l w`>>
  qexists_tac`w'` >> rw[satisfies_INSERT]>>
  `l ≠ 0` by metis_tac[]
  >- (
    `satisfies_literal w' l` by
      (simp[Abbr`w'`]>>
      metis_tac[flip_literal_flips,satisfies_clause_def])>>
    metis_tac[satisfies_clause_def])
  >>
    `fml = { D | D ∈ fml ∧ ¬MEM (-l) D} ∪ { D | D ∈ fml ∧ MEM (-l) D}` by
      (simp[EXTENSION]>>
      metis_tac[])>>
    pop_assum SUBST1_TAC>>
    rw[satisfies_union]
    >- (
      fs[satisfies_def]>>rw[]>>
      fs[Abbr`w'`]>>
      simp[Once flip_literal_eq_neg]>>
      `-l ≠ 0` by fs[]>>
      drule flip_literal_unaffected>>
      disch_then match_mp_tac>> simp[]>>
      metis_tac[satisfies_literal_exclusive,satisfies_clause_def])
    >>
      fs[satisfies_def]>>rw[]>>
      `C ++ delete_literal (-l) C' ∈ Ds` by
        (fs[Abbr`Ds`]>>
        qexists_tac`C'`>>fs[])>>
      first_x_assum drule>> disch_then kall_tac>>
      first_x_assum drule>>
      simp[satisfies_clause_append]>>
      strip_tac>>
      `satisfies_clause w' (delete_literal (-l) C')` by
        (simp[Abbr`w'`]>>
        simp[Once flip_literal_eq_neg]>>
        `-l ≠ 0` by fs[]>>
        drule flip_literal_unaffected>>
        disch_then match_mp_tac>>
        fs[delete_literal_def,MEM_FILTER]>>
        metis_tac[satisfies_literal_exclusive,satisfies_clause_def])>>
      pop_assum mp_tac>>
      match_mp_tac satisfies_clause_SUBSET>>
      fs[delete_literal_def,MEM_FILTER]
QED

(* More implementationy stuff *)

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

Theorem values_delete:
  values (delete h v) ⊆ values v
Proof
  simp[values_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
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

(*** Implementation ***)
val _ = Datatype`
  lratstep =
    Delete (num list) (* Clauses to delete *)
  | RAT num clause (num list) ((num list) spt)`
    (* RAT step:
      AT n C i0 (ik id ~> ik)
      n is the new id of the new clause C
      i0 is a list of clause IDs for the AT part
      ik is a sptree mapping clause IDs to their hints
    *)

Type lrat = ``:lratstep list``

val delete_clauses_def = Define`
  delete_clauses cl fml =
    FOLDR delete fml cl`

(*
  Checking for asymmetric tautology via unit propagation using the given hints
  NONE == Error
  SOME (INL ()) == C is an AT
  SOME (INR C) == hints were insufficient, but C is now extended with units
*)
val is_AT_def = Define`
  (is_AT fml [] (C:clause) = SOME (INR C)) ∧
  (is_AT fml (i::is) C =
  case lookup i fml of
    NONE => NONE
  | SOME Ci =>
  let D = FILTER (λx. ¬ MEM x C) Ci in
  case D of
    [] => SOME (INL ())
  | [d] => is_AT fml is (-d::C)
  | _ => NONE)`

val find_tauto_def = Define`
  (find_tauto p C [] = F) ∧
  (find_tauto (p:int) C (c::cs) =
    if c = -p then find_tauto p C cs
    else
      if MEM (-c) C then T
      else find_tauto p C cs
  )`

(*
  Resolution Asymmetric Tautology
*)
val is_RAT_aux_def = Define`
  (is_RAT_aux fml p C ik [] = T) ∧
  (is_RAT_aux fml p C ik (iCi::iCs) =
  case iCi of (i,Ci) =>
    if MEM (-p) Ci then
      case lookup i ik of
        NONE => F
      | SOME is =>
        case is of [] =>
        (* Step 5.2: can be made more efficient *)
          if find_tauto p C Ci then
            is_RAT_aux fml p C ik iCs
          else
            F
        | _ =>
        (* Step 5.3-5.5 *)
        if is_AT fml is (C ++ delete_literal (-p) Ci) = SOME (INL ()) then
          is_RAT_aux fml p C ik iCs
        else
          F
    else
      is_RAT_aux fml p C ik iCs)`

val is_RAT_def = Define`
  is_RAT fml (C:clause) i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT fml i0 C of
    NONE => F
  | SOME (INL ()) => T
  | SOME (INR D) =>
  (* First, do the asymmetric tautology check *)
  case C of
    [] => F
  | (p::C) =>
  let iCs = toAList fml in
    is_RAT_aux fml p D ik iCs`

(* Run the LRAT checker on fml, returning an option *)
val check_lrat_def = Define`
  (check_lrat [] fml = SOME fml) ∧
  (check_lrat (step::steps) fml =
    case step of
      Delete cl =>
      check_lrat steps (delete_clauses cl fml)
    | RAT n C i0 ik =>
      if wf_clause C then
      if is_RAT fml C i0 ik then
        check_lrat steps (insert n C fml)
      else NONE
      else NONE)`

val check_lrat_unsat_def = Define`
  check_lrat_unsat lrat fml =
  case check_lrat lrat fml of
    NONE => F
  | SOME fml' =>
    let ls = MAP SND (toAList fml') in
    MEM [] ls`

(* Implementation *)
Theorem is_AT_imp_asymmetric_tautology:
  ∀is fml C.
  wf_fml fml ∧ wf_clause C ∧
  is_AT fml is C = SOME (INL ()) ⇒
  asymmetric_tautology (values fml) C
Proof
  Induct>>fs[is_AT_def]>>
  ntac 4 strip_tac>>
  drule filter_unit_preserves_unsatisfiable>>
  every_case_tac>>fs[]
  >-
    (fs[asymmetric_tautology_def]>>
    rw[]>>
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

Theorem is_AT_imp_sat_preserving:
  ∀is fml C D.
  wf_fml fml ∧ wf_clause C ∧
  is_AT fml is C = SOME (INR D) ⇒
  ∃E.
    D = E ++ C ∧ wf_clause D ∧
    ∀w.
    satisfies w (D INSERT values fml) ⇒
    satisfies w (C INSERT values fml)
Proof
  Induct>>fs[is_AT_def] >>
  rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  `wf_clause (-h'::C)` by
    (fs[wf_clause_def,wf_fml_def]>>
    fs[values_def,PULL_EXISTS]>>
    first_x_assum drule>>
    `MEM h' (FILTER (λx. ¬MEM x C) x )` by fs[]>>
    rw[]>>`h' ≠ 0` by metis_tac[MEM_FILTER]>>
    intLib.ARITH_TAC)>>
  disch_then drule>>
  disch_then drule>>rw[]>>
  qexists_tac`E++[-h']`>>fs[]>>
  rw[]>>
  first_x_assum drule>>
  simp[satisfies_INSERT]>>
  Cases_on`satisfies_clause w C`>>simp[]>>
  Cases_on`satisfies w (values fml)`>> fs[] >>
  `satisfies_clause w x` by
    (fs[satisfies_def,values_def]>>metis_tac[])>>
  `satisfies_literal w h'` by
    (fs[satisfies_clause_def]>>
    `¬MEM l C` by metis_tac[]>>
    `MEM l (FILTER (λx. ¬MEM x C) x)` by
      fs[MEM_FILTER]>>
    rfs[]>>
    metis_tac[])>>
  PURE_REWRITE_TAC [Once CONS_APPEND]>>
  simp[satisfies_clause_append,satisfies_clause_def]>>
  `h' ≠ 0` by
    (fs[wf_clause_def]>>
    intLib.ARITH_TAC)>>
  metis_tac[satisfies_literal_exclusive]
QED

Theorem find_tauto_correct:
  ∀ls p C.
  find_tauto p C ls ⇒
  ∃l. MEM l ls ∧ MEM (-l) C ∧ l ≠ -p
Proof
  Induct>>rw[find_tauto_def]>>metis_tac[]
QED

Theorem is_RAT_aux_imp:
  ∀iCs fml p C ik.
  is_RAT_aux fml p C ik iCs ∧
  wf_fml fml ∧
  EVERY (λ(i,Ci). wf_clause Ci) iCs ∧
  wf_clause C ⇒
  ∀i Ci. MEM (i,Ci) iCs ∧ MEM (-p) Ci ⇒
    asymmetric_tautology (values fml) (C ++ delete_literal (-p) Ci)
Proof
  Induct>>Cases>>fs[is_RAT_aux_def]>>
  ntac 5 strip_tac >>
  rw[]
  >- (
    last_x_assum kall_tac>> fs[]>>
    every_case_tac>>fs[]
    >-
      (drule find_tauto_correct>>
      rw[]>>
      match_mp_tac (GEN_ALL tautology_asymmetric_tautology)>>
      qexists_tac`l`>>simp[delete_literal_def,MEM_FILTER]>>
      fs[wf_clause_def,MEM_FILTER])>>
    match_mp_tac is_AT_imp_asymmetric_tautology>> fs[]>>
    qexists_tac`h::t`>>fs[wf_clause_def]>>
    fs[delete_literal_def,MEM_FILTER])
  >>
    fs[PULL_FORALL,AND_IMP_INTRO]>>
    first_x_assum match_mp_tac>>fs[]>>
    every_case_tac>>fs[]>>metis_tac[]
QED

Theorem is_RAT_imp_resolution_asymmetric_tautology:
  ∀fml C i0 ik.
  wf_fml fml ∧ wf_clause C ∧
  is_RAT fml C i0 ik ⇒
  satisfiable (values fml) ⇒ satisfiable (C INSERT values fml)
Proof
  rw[is_RAT_def]>>
  ntac 2 (pop_assum mp_tac)>> ntac 2 TOP_CASE_TAC>>fs[]
  >-
    (drule is_AT_imp_asymmetric_tautology>>
    rpt (disch_then drule)>>
    metis_tac[asymmetric_tautology_satisfiable]) >>
  TOP_CASE_TAC>>fs[]>>
  strip_tac>>
  drule is_AT_imp_sat_preserving>>
  disch_then drule>>
  disch_then drule>>rw[]>>
  qmatch_asmsub_abbrev_tac`wf_clause y`>>
  drule is_RAT_aux_imp>> simp[]>>
  `EVERY (λ(i,Ci). wf_clause Ci) (toAList fml)` by
    (fs[EVERY_MEM,MEM_toAList,FORALL_PROD,wf_fml_def,values_def]>>
    metis_tac[])>>
  simp[MEM_toAList]>>
  strip_tac>>
  `resolution_asymmetric_tautology (values fml) y` by
    (simp[resolution_asymmetric_tautology_def]>>
    fs[wf_clause_def]>>
    `MEM h y` by fs[Abbr`y`]>>
    fs[values_def,PULL_EXISTS]>>
    metis_tac[])>>
  drule resolution_asymmetric_tautology_satisfiable>>
  metis_tac[satisfiable_def]
QED

(* Deletion preserves sat: if C is satisfiable, then deleting clauses from C keeps satisfiability *)
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
  every_case_tac>>fs[]>>
  drule wf_fml_insert>> disch_then drule>>
  disch_then(qspec_then`n`assume_tac)>>
  first_x_assum drule>>
  disch_then drule>>
  disch_then match_mp_tac>>
  last_x_assum assume_tac>>
  drule is_RAT_imp_resolution_asymmetric_tautology>>
  disch_then drule>>
  disch_then drule>>
  disch_then drule>>
  match_mp_tac satisfiable_SUBSET>>
  metis_tac[values_insert2]
QED

Theorem check_lrat_unsat_sound:
  ∀lrat fml fml'.
  wf_fml fml ∧
  check_lrat_unsat lrat fml ⇒
  unsatisfiable (values fml)
Proof
  rw[check_lrat_unsat_def]>>
  every_case_tac>>fs[MEM_MAP]>>
  `unsatisfiable (values x)` by
    (match_mp_tac empty_clause_imp_unsatisfiable>>
    fs[values_def]>>
    metis_tac[MEM_toAList,PAIR])>>
  drule check_lrat_sound>>
  disch_then drule>>
  metis_tac[unsatisfiable_def]
QED

(* Try on an example *)
val fml = rconc (EVAL ``insert 1 [ 1;  2; -3] (
  insert 2 [-1; -2;  3] (
  insert 3 [ 2;  3; -4] (
  insert 4 [-2; -3;  4] (
  insert 5 [-1; -3; -4] (
  insert 6 [ 1;  3;  4] (
  insert 7 [-1;  2;  4] (
  insert 8 [ (1:int); -2; -4] LN)))))))``)

val lrat =
``[
  Delete [];
  RAT 9 [-1] [] (insert 1 [5;7] (insert 6 [2;7] (insert 8 [5;2] LN)));
  Delete [7;5;2] ;
  RAT 10 [2] [9;1;6;3] LN;
  Delete [1;3;0] ;
  RAT 12 [] [9;10;8;4;6] LN
]``;

  (* result contains the empty clause *)
val res = EVAL``check_lrat_unsat ^(lrat) ^(fml)``

val _ = export_theory ();
