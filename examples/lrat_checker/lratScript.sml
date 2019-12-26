(*
   Basic specification of an LRAT checker
   - No optimizations
*)
open preamble miscTheory mlstringTheory satSemTheory;

val _ = new_theory "lrat";

(*
  Bridging implementation and semantics

  Clauses are lists of integers where positive (>0) integers map to INL and negative (<0) map to INR

  In implementation, clauses must not contain 0
*)
Type lit = ``:int``;
Type cclause = ``:lit list``;
Type ccnf = ``:cclause spt``;

val values_def = Define`
  values s = {v | ∃n. lookup n s = SOME v}`

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

val interp_lit_def = Define`
  interp_lit (l:lit) =
  if l > 0 then INL (Num (ABS l))
  else INR (Num (ABS l))`

val interp_cclause_def = Define`
  interp_cclause (ls:cclause) =
  IMAGE interp_lit (set ls DIFF {0})`

val interp_def = Define`
  interp (fml:ccnf) = IMAGE interp_cclause (values fml)`

(* Implementation *)
val _ = Datatype`
  lratstep =
    Delete (num list) (* Clauses to delete *)
  | PR num cclause (cclause option) (num list) ((num list) spt)`
    (* PR step:
      PR n C wopt i0 (ik id ~> ik)
      n is the new id of the clause C
      wopt is a witnessing assignment (represented as a list of literals)
        if w is NONE, then this reduces to RAT
      i0 is a list of clause IDs for the AT part
      ik is a sptree mapping clause IDs to their hints
    *)

Type lrat = ``:lratstep list``

val delete_literals_def = Define`
  delete_literals (C:cclause) (D:cclause) =
  FILTER (λx. ¬MEM x D) C`

(*
  Checking for asymmetric tautology via unit propagation using the given hints.
  Returns:
  NONE => Error
  SOME (INL ()) => C is an AT
  SOME (INR C) => hints were insufficient, but C is now extended with units
*)
val is_AT_def = Define`
  (is_AT fml [] (C:cclause) = SOME (INR C)) ∧
  (is_AT fml (i::is) C =
  case lookup i fml of
    NONE => NONE
  | SOME Ci =>
  case delete_literals Ci C of
    [] => SOME (INL ())
  | [l] => is_AT fml is (-l :: C)
  | _ => NONE)`

(* Check if Ci overlaps with a list of assignments *)
val check_overlap_def = Define`
  (check_overlap Ci [] = F) ∧
  (check_overlap Ci (a::as) =
    (MEM a Ci ∨ check_overlap Ci as))`

(* flips a clause/assignment.
  for a clause, this yields its blocked assignment *)
val flip_def = Define`
  flip (C:cclause) = MAP (λi. -i) C`

(* Construct the overlapping assignment
  { w ∪ negate (C) }
  where w overrides everything in negate(C)
*)
val overlap_assignment_def = Define`
  overlap_assignment w C =
    w ++ flip (delete_literals C w)`

(* The (L)RAT check (no witnesses) *)
val check_RAT_def = Define`
  check_RAT fml p C ik (i,Ci) =
  (* Step 5.1: if Ci contains -p do work, else skip *)
  if check_overlap Ci [-p] then
    (* Lookup the hint *)
    case lookup i ik of
      NONE => F
    | SOME is =>
    case is of
      (* Step 5.2: Ci is satisfied by p ∪ negate (C) *)
      [] => check_overlap Ci (overlap_assignment [p] C)
    | _ =>
      (* Step 5.3-5.5: Otherwise, use full hints *)
      is_AT fml is (C ++ (delete_literals Ci [-p])) = SOME (INL ())
  else
    T`

(* The (L)PR check (witness given) *)
val check_PR_def = Define`
  check_PR fml p C w ik (i,Ci) =
  (* Step 5.1: if Ci is touched by w do work, else skip *)
  if check_overlap Ci (flip w) then
    (* Lookup the hint *)
    case lookup i ik of
      NONE =>
      (* Step 5.2.1: Ci is satisfied by w *)
      check_overlap Ci w
    | SOME is =>
    case is of
      (* Step 5.2.2: Ci is satisfied by w ∪ negate (C) *)
      [] => check_overlap Ci (overlap_assignment w C)
    | _ =>
      (* Step 5.3-5.5: Otherwise use full hints *)
      is_AT fml is (C ++ (delete_literals Ci (flip (overlap_assignment w C)))) = SOME (INL ())
  else
    T`

val is_PR_def = Define`
  is_PR fml p (C:cclause) wopt i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT fml i0 C of
    NONE => F
  | SOME (INL ()) => T
  | SOME (INR D) =>
  if p ≠ 0 then
    let iCs = toAList fml in
    case wopt of
      NONE => EVERY (check_RAT fml p D ik) iCs
    | SOME w =>
      ¬(check_overlap w (flip w)) ∧
      EVERY (check_PR fml p D w ik) iCs
  else
     F`

val check_lrat_step_def = Define`
  check_lrat_step step fml =
  case step of
    Delete cl => SOME (FOLDL (\a b. delete b a) fml cl)
  | PR n C w i0 ik =>
    let p = case C of [] => 0 | (x::xs) => x in
    if is_PR fml p C w i0 ik
    then SOME (insert n C fml)
    else NONE`

val is_unsat_def = Define`
  is_unsat fml =
  let ls = MAP SND (toAList fml) in
  MEM [] ls`

(* Run the LRAT checker on fml, returning an option *)
val check_lrat_def = Define`
  (check_lrat [] fml = SOME fml) ∧
  (check_lrat (step::steps) fml =
    case check_lrat_step step fml of
      NONE => NONE
    | SOME fml' => check_lrat steps fml')`

val check_lrat_unsat_def = Define`
  check_lrat_unsat lrat fml =
  case check_lrat lrat fml of
    NONE => F
  | SOME fml' => is_unsat fml'`

(* Proofs *)
val wf_clause_def = Define`
  wf_clause (C:cclause) ⇔ ¬ MEM 0 C`

val wf_fml_def = Define`
  wf_fml (fml:ccnf) ⇔
  ∀C. C ∈ values fml ⇒ wf_clause C`

Theorem filter_unit_preserves_satisfies:
  ∀C.
  (IMAGE (λl. {negate_literal l}) C) ⊆ fml ∧
  satisfies w (D INSERT fml) ⇒
  satisfies w ( (D DIFF C) INSERT fml)
Proof
  rw[satisfies_def]
  >-
    (first_assum(qspec_then`D` assume_tac)>>fs[satisfies_clause_def]>>
    `l ∉ C` by
      (CCONTR_TAC>>
      fs[SUBSET_DEF]>>
      last_x_assum(qspec_then`{negate_literal l}` mp_tac)>>
      impl_tac >-
        metis_tac[]>>
      strip_tac>>
      first_x_assum(qspec_then`{negate_literal l}` assume_tac)>>rfs[]>>
      metis_tac[satisfies_literal_exclusive])>>
    metis_tac[])
  >>
    metis_tac[]
QED

Theorem filter_unit_preserves_unsatisfiable:
  ∀C.
  (IMAGE (λl. {negate_literal l}) C) ⊆ fml ∧
  unsatisfiable ((D DIFF C) INSERT fml) ⇒
  unsatisfiable (D INSERT fml)
Proof
  rw[unsatisfiable_def,satisfiable_def]>>
  metis_tac[filter_unit_preserves_satisfies]
QED

Theorem interp_lit_eq:
  x ≠ 0 ∧
  interp_lit x = interp_lit y ⇒
  x = y
Proof
  rw[interp_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem interp_cclause_delete_literals:
  interp_cclause (delete_literals C D) =
  interp_cclause C DIFF interp_cclause D
Proof
  simp[delete_literals_def]>>
  fs[interp_cclause_def]>>
  fs[EXTENSION]>>
  rw[EQ_IMP_THM]>>
  fs[MEM_FILTER]>>
  metis_tac[interp_lit_eq]
QED

Theorem negate_literal_interp_lit:
  h ≠ 0 ⇒
  negate_literal (interp_lit h) = interp_lit (-h)
Proof
  rw[negate_literal_def,interp_lit_def]>>
  intLib.ARITH_TAC
QED

Theorem interp_cclause_negate_literal:
  h ≠ 0 ⇒
  IMAGE (λl. {negate_literal l}) (interp_cclause [-h]) =
  {interp_cclause [h]}
Proof
  simp[interp_cclause_def]>>
  simp[negate_literal_interp_lit]
QED

Theorem interp_cclause_empty[simp]:
  interp_cclause [] = {}
Proof
  fs[interp_cclause_def]
QED

Theorem wf_cclause_empty[simp]:
  wf_clause []
Proof
  fs[wf_clause_def]
QED

Theorem interp_cclause_append:
  interp_cclause (A++B) = interp_cclause A ∪ interp_cclause B
Proof
  fs[interp_cclause_def,EXTENSION]>>
  metis_tac[]
QED

Theorem interp_cclause_cons:
  interp_cclause (h::C) =
  interp_cclause [h] ∪ interp_cclause C
Proof
  rw[interp_cclause_def]>>
  metis_tac[INSERT_SING_UNION]
QED

(* is_AT is correct in the INL case *)
Theorem is_AT_imp_asymmetric_tautology:
  ∀is fml C.
  wf_fml fml ∧ wf_clause C ∧
  is_AT fml is C = SOME (INL ()) ⇒
    asymmetric_tautology (interp fml) (interp_cclause C)
Proof
  Induct>>fs[is_AT_def]>>
  ntac 4 strip_tac>>
  every_case_tac>>fs[]>>
  `interp_cclause x DIFF interp_cclause C = interp_cclause (delete_literals x C)` by
    fs[interp_cclause_delete_literals]
  >-
    (fs[asymmetric_tautology_def]>>
    qmatch_goalsub_abbrev_tac`unsatisfiable fml'`>>
    `fml' = (interp_cclause x) INSERT fml'` by
      (match_mp_tac (GSYM ABSORPTION_RWT)>>
      fs[Abbr`fml'`,values_def,interp_def]>>
      metis_tac[])>>
    pop_assum SUBST1_TAC>>
    match_mp_tac filter_unit_preserves_unsatisfiable>>
    qexists_tac`interp_cclause C`>>rw[]
    >-
      fs[Abbr`fml'`]
    >>
    match_mp_tac empty_clause_imp_unsatisfiable>>
    simp[interp_cclause_def])
  >>
  `wf_clause x` by
    (fs[wf_fml_def,values_def]>>
    metis_tac[])>>
  `MEM h' (delete_literals x C)` by fs[]>>
  `-h' ≠ 0` by
    (fs[wf_clause_def,delete_literals_def,MEM_FILTER]>>
    metis_tac[])>>
  last_x_assum drule>>
  disch_then (qspec_then`(-h')::C` mp_tac)>>simp[]>>
  impl_tac >-
    (fs[wf_clause_def]>>
    intLib.ARITH_TAC)>>
  simp[asymmetric_tautology_def]>>
  rw[]>>fs[]>>
  qmatch_goalsub_abbrev_tac`unsatisfiable fml'`>>
  `(interp_cclause x) INSERT fml' = fml'` by
    (match_mp_tac ABSORPTION_RWT>>
    fs[Abbr`fml'`,values_def,interp_def]>>
    metis_tac[])>>
  pop_assum (SUBST1_TAC  o SYM)>>
  match_mp_tac filter_unit_preserves_unsatisfiable>>
  qexists_tac`interp_cclause C`>>rw[]
  >-
    simp[Abbr`fml'`]
  >>
    fs[Abbr`fml'`]>>
    pop_assum mp_tac>>
    simp[Once interp_cclause_cons]>>
    simp[interp_cclause_negate_literal]>>
    metis_tac[UNION_INSERT_EQ,INSERT_SING_UNION]
QED

Theorem satisfies_clause_DIFF:
  satisfies_clause w C ∧
  ¬satisfies_clause w D ⇒
  satisfies_clause w (C DIFF D)
Proof
  fs[satisfies_clause_def]>>
  metis_tac[]
QED

Theorem is_AT_imp_sat_implies:
  ∀is fml C D.
  wf_fml fml ∧ wf_clause C ⇒
  is_AT fml is C = SOME (INR D) ⇒
  ∃E.
    interp_cclause D = E ∪ interp_cclause C ∧
    wf_clause D ∧
    sat_implies
      (interp_cclause D INSERT interp fml)
      (interp_cclause C INSERT interp fml)
Proof
  Induct>>fs[is_AT_def]>>
  rw[]
  >-
    (qexists_tac`{}`>>simp[sat_implies_def])>>
  every_case_tac>>fs[]>>
  `interp_cclause x DIFF interp_cclause C = interp_cclause (delete_literals x C)` by
    fs[interp_cclause_delete_literals]>>
  `wf_clause x` by
    (fs[wf_fml_def,values_def]>>
    metis_tac[])>>
  `MEM h' (delete_literals x C)` by fs[]>>
  `-h' ≠ 0` by
    (fs[wf_clause_def,delete_literals_def,MEM_FILTER]>>
    metis_tac[])>>
  first_x_assum drule>>
  disch_then(qspecl_then [`-h'::C`,`D`] mp_tac)>>simp[]>>
  impl_tac >-
    (fs[wf_clause_def]>>
    intLib.ARITH_TAC)>>
  strip_tac>>
  qexists_tac`E ∪ interp_cclause [-h']`>> simp[]>>
  simp[Once interp_cclause_cons,UNION_ASSOC]>>
  rw[sat_implies_def]>>fs[sat_implies_def]>>
  qpat_x_assum` _ D = _` SUBST_ALL_TAC>>
  first_x_assum drule>>
  strip_tac>>
  fs[satisfies_INSERT]>>
  `satisfies_clause w (interp_cclause x)` by
    (fs[satisfies_def,interp_def,values_def]>>
    metis_tac[])>>
  CCONTR_TAC >> fs[]>>
  `interp_cclause x DIFF interp_cclause C = interp_cclause [h']` by
    fs[]>>
  `satisfies_clause w (interp_cclause [h'])` by
    metis_tac[satisfies_clause_DIFF]>>
  fs[satisfies_clause_union]>>
  qpat_x_assum`h' ≠ 0` mp_tac>>
  rpt (qpat_x_assum`satisfies_clause w _` mp_tac)>>
  PURE_REWRITE_TAC [Once interp_cclause_cons,Once satisfies_clause_union]>>
  strip_tac>>
  pop_assum mp_tac>>
  rpt( pop_assum kall_tac)>>
  rw[interp_cclause_def]>>
  fs[satisfies_clause_def]>>
  metis_tac[negate_literal_interp_lit,satisfies_literal_exclusive]
QED

Theorem check_overlap_eq:
  ∀D.
  check_overlap C D  ⇔
  ∃x. MEM x C ∧ MEM x D
Proof
  Induct>>rw[check_overlap_def]>>
  metis_tac[]
QED

(* Some sanity checks:
  is_AT in INL() case is independent of ordering
*)

(* TODO: these antitone theorems can be stated more precisely *)
Theorem delete_literals_antitone:
  ∀ls.
  (∀x. MEM x D ⇒ MEM x C) ⇒
  (∀y. MEM y (delete_literals ls C) ⇒ MEM y (delete_literals ls D))
Proof
  rw[delete_literals_def,MEM_FILTER]>>
  metis_tac[]
QED

Theorem delete_literals_antitone_LENGTH:
  ∀ls.
  (∀x. MEM x D ⇒ MEM x C) ⇒
  LENGTH (delete_literals ls C) ≤ LENGTH (delete_literals ls D)
Proof
  rw[delete_literals_def]>>
  match_mp_tac LENGTH_FILTER_LEQ_MONO>>
  metis_tac[]
QED

Theorem is_AT_INL_reorder:
  ∀is C D.
  (∀x. MEM x D ⇒ MEM x C) /\ is_AT fml is D = SOME (INL ()) ⇒
  is_AT fml is C = SOME (INL ())
Proof
  Induct>> rw[is_AT_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
  >- (
    drule delete_literals_antitone_LENGTH>>
    disch_then(qspec_then`x` assume_tac)>>rfs[]>>
    every_case_tac>>fs[]>>
    `h'=h''` by
      (drule delete_literals_antitone>>
      disch_then(qspec_then`x` assume_tac)>>rfs[])>>
    rw[]>>
    metis_tac[MEM])
  >>
  drule delete_literals_antitone_LENGTH>>
  disch_then(qspec_then`x` assume_tac)>>rfs[]>>
  every_case_tac>>fs[]
QED

(* Converse is true assuming p and ¬p are not both in Ci *)
Theorem check_RAT_imp_check_PR:
  check_RAT fml p C ik (i,Ci) ==>
  check_PR fml p C [p] ik (i,Ci)
Proof
  rw[check_RAT_def,check_PR_def]>>
  fs[flip_def,overlap_assignment_def]>>
  every_case_tac>>fs[]>>
  fs[check_overlap_eq]>>
  rw[]>>fs[]>>
  match_mp_tac is_AT_INL_reorder>>
  HINT_EXISTS_TAC>>fs[]>>
  simp[MAP_MAP_o,o_DEF]>>
  rw[delete_literals_def,MEM_FILTER]>>
  metis_tac[]
QED

(*
  The witnessing assignment is
    interp_cclause w ∪ (IMAGE negate_literal (interp_cclause C DIFF interp_cclause w))
*)
Theorem DIFF_ID:
  A DIFF B = A ⇔ A ∩ B = {}
Proof
  rw[EXTENSION]>>
  metis_tac[]
QED

Theorem INTER_UNION_EMPTY:
  A ∩ (B ∪ C) = {} ⇔
  A ∩ B = {} ∧ A ∩ C = {}
Proof
  rw[EXTENSION]>>
  metis_tac[]
QED

Theorem MEM_overlap_assignment:
  MEM x (overlap_assignment w C) =
  (MEM x w ∨ MEM (-x) C ∧ ¬MEM (-x) w)
Proof
  rw[overlap_assignment_def,flip_def,MEM_MAP,delete_literals_def,MEM_FILTER]>>
  Cases_on`MEM x w`>>simp[]>>
  rw[EQ_IMP_THM]>>fs[]>>
  qexists_tac`-x`>> simp[]
QED

Theorem interp_cclause_flip:
  interp_cclause (flip C) = IMAGE negate_literal (interp_cclause C)
Proof
  rw[interp_cclause_def,flip_def,EXTENSION,MEM_MAP,EQ_IMP_THM]
  >- (
    qexists_tac`interp_lit i`>>
    `i ≠ 0` by fs[]>>
    simp[negate_literal_interp_lit]>>
    metis_tac[])
  >>
  qexists_tac`-x''`>>
  simp[negate_literal_interp_lit]
QED

Theorem check_PR_sat_implies:
  check_PR fml p C w ik (i,Ci) ∧ Ci ∈ values fml ∧
  wf_fml fml ∧ wf_clause C ∧ consistent_par (interp_cclause C) ⇒
  sat_implies (par (IMAGE negate_literal (interp_cclause C)) (interp fml))
    (par
      (interp_cclause w ∪ (IMAGE negate_literal (interp_cclause C DIFF interp_cclause w)))
      {interp_cclause Ci})
Proof
  simp[check_PR_def]>>
  reverse (Cases_on`check_overlap Ci (flip w)`)
  >- (
    (* 5.1: Ci not touched by w *)
    rw[sat_implies_def,par_def,satisfies_def]>>
    simp[DIFF_UNION]>>
    `interp_cclause Ci DIFF IMAGE negate_literal (interp_cclause w) = interp_cclause Ci` by
      (simp[DIFF_ID,interp_cclause_def,EXTENSION]>>
      rw[]>>CCONTR_TAC>>fs[check_overlap_eq,flip_def,MEM_MAP]>>
      metis_tac[interp_lit_eq,negate_literal_interp_lit])>>
    fs[INTER_UNION_EMPTY,IMAGE_IMAGE]>>
    first_x_assum match_mp_tac>>
    simp[PULL_EXISTS,interp_def]>>
    fs[EXTENSION]>>
    metis_tac[]) >>
  simp[]>>
  strip_tac>>
  `wf_clause Ci` by
    fs[wf_fml_def]>>
  Cases_on`lookup i ik`>>
  simp[]
  >- (
    (* 5.2.1: Ci already satisfied by w *)
    rw[sat_implies_def,par_def,satisfies_def]>>
    fs[INTER_UNION_EMPTY,check_overlap_eq]>>
    `interp_lit x' ∈ interp_cclause Ci ∩ interp_cclause w` by
      (fs[wf_clause_def]>>
      simp[interp_cclause_def]>>
      metis_tac[])>>
    fs[EXTENSION]>>
    metis_tac[])>>
  Cases_on`x`>>fs[]
  >- (
    (* 5.2.2: Ci already satisfied by w ∪ alpha+ *)
    rw[sat_implies_def,par_def,satisfies_def]>>
    fs[INTER_UNION_EMPTY,check_overlap_eq]>>
    qmatch_asmsub_abbrev_tac `A = {}`>>
    qsuff_tac`interp_lit x' ∈ A`
    >- fs[EXTENSION]>>
    simp[Abbr`A`]>>
    CONJ_ASM1_TAC >- (
      fs[interp_cclause_def,wf_clause_def]>>
      metis_tac[])>>
    fs[MEM_overlap_assignment]
    >- (
      `interp_lit x' ∈ interp_cclause w` by
        (fs[wf_clause_def]>>
        simp[interp_cclause_def]>>
        metis_tac[])>>
      fs[EXTENSION]>>
      metis_tac[])>>
    qexists_tac`interp_lit (-x')`>>
    `-x' ≠ 0` by (fs[wf_clause_def] >> metis_tac[])>>
    simp[negate_literal_interp_lit]>>
    fs[wf_clause_def,interp_cclause_def]>>
    metis_tac[interp_lit_eq])>>
  (* 5.3 *)
  rw[sat_implies_def]>>
  simp[satisfies_def,par_def]>>
  strip_tac>>
  drule is_AT_imp_asymmetric_tautology>>
  qmatch_asmsub_abbrev_tac`is_AT _ _ D = SOME _`>>
  disch_then(qspecl_then[`h::t`,`D`] mp_tac)>>
  simp[]>>
  impl_tac >-
    (simp[Abbr`D`,delete_literals_def]>>
    fs[wf_clause_def,MEM_FILTER])>>
  simp[Abbr`D`,interp_cclause_append]>>
  simp[overlap_assignment_def,interp_cclause_delete_literals,interp_cclause_flip,interp_cclause_append,IMAGE_IMAGE]>>
  strip_tac>>
  drule asymmetric_tautology_union_clause2 >>
  disch_then drule>>
  impl_tac >-
    (fs[EXTENSION]>> metis_tac[])>>
  strip_tac>>
  drule asymmetric_tautology_satisfies>>
  disch_then drule>>
  simp[satisfies_INSERT,interp_cclause_delete_literals,interp_cclause_flip]>>
  simp[overlap_assignment_def,interp_cclause_append,interp_cclause_flip,IMAGE_IMAGE,interp_cclause_delete_literals]>>
  qmatch_goalsub_abbrev_tac`_ _ A ==> _ _ B`>>
  qsuff_tac`A=B` >- fs[]>>
  unabbrev_all_tac>>fs[EXTENSION]>>
  metis_tac[]
QED

Theorem redundant_sat_implies:
  sat_implies (D INSERT fml) (C INSERT fml) ∧
  redundant fml D
  ⇒
  redundant fml C
Proof
  rw[sat_implies_def,redundant_def]>>
  fs[]>>
  metis_tac[satisfiable_def]
QED

Theorem sat_implies_values:
  (∀C. C ∈ values fml ⇒ sat_implies A (par w {interp_cclause C})) ⇒
  sat_implies A (par w (interp fml))
Proof
  rw[sat_implies_def,satisfies_def,interp_def,par_def]>>
  metis_tac[]
QED

Theorem consistent_par_union:
  consistent_par A ∧
  consistent_par B ∧
  A ∩ B = {} ⇒
  consistent_par (A ∪ IMAGE negate_literal B)
Proof
  rw[consistent_par_def,IMAGE_IMAGE]>>
  simp[INTER_UNION_EMPTY,INTER_UNION]>>
  fs[EXTENSION]>>
  metis_tac[negate_literal_11]
QED

Theorem consistent_par_DIFF:
  consistent_par A ⇒ consistent_par (A DIFF B)
Proof
  rw[consistent_par_def,EXTENSION]>>
  metis_tac[]
QED

Theorem check_overlap_flip_consistent_par:
  ¬check_overlap x (flip x) ⇒
  consistent_par (interp_cclause x)
Proof
  rw[consistent_par_def,interp_cclause_def,EXTENSION,check_overlap_eq,flip_def,MEM_MAP]>>
  CCONTR_TAC>>fs[]>>
  rename1 `MEM A x`>>
  qpat_x_assum`MEM _ _` mp_tac>>
  rename1 `MEM B x`>>
  first_x_assum(qspec_then`A` assume_tac)>>rfs[]>>
  first_x_assum(qspec_then`B` assume_tac)>>rfs[]>>
  `B ≠ -A` by intLib.ARITH_TAC>>
  metis_tac[interp_lit_eq,negate_literal_interp_lit]
QED

Theorem is_PR_redundant:
  wf_clause C ∧ wf_fml fml ∧
  (p ≠ 0 ⇒ MEM p C ∧
    case w of SOME ww =>
      MEM p ww
    | NONE => T) ∧
  is_PR fml p C w i0 ik  ⇒
  redundant (interp fml) (interp_cclause C)
Proof
  simp[is_PR_def]>>
  strip_tac>>
  pop_assum mp_tac>>
  ntac 2 (TOP_CASE_TAC>>fs[])
  >-
    metis_tac[is_AT_imp_asymmetric_tautology,asymmetric_tautology_redundant]
  >>
  strip_tac>>
  drule is_AT_imp_sat_implies>>
  disch_then drule>>
  disch_then drule>>
  strip_tac>>
  drule redundant_sat_implies>>
  disch_then match_mp_tac>>
  reverse (Cases_on`consistent_par (E ∪ interp_cclause C)`)
  >-
    metis_tac[not_consistent_par_redundant]>>
  reverse (Cases_on`w`)>>fs[]
  >- (
    (* PR *)
    match_mp_tac par_redundant>>
    qexists_tac`(interp_cclause x ∪
               IMAGE negate_literal (E ∪ interp_cclause C DIFF interp_cclause x))`>>
               simp[]>>
    CONJ_TAC >- (
      match_mp_tac consistent_par_union>>
      rw[]
      >-
        metis_tac[check_overlap_flip_consistent_par]
      >-
        metis_tac[consistent_par_DIFF]
      >>
        simp[EXTENSION]>>
        metis_tac[])>>
    CONJ_TAC >- (
      `interp_lit p ∈ interp_cclause x ∧ interp_lit p ∈ interp_cclause C` by
        fs[interp_cclause_def]>>
      simp[EXTENSION]>>
      metis_tac[])>>
    match_mp_tac sat_implies_values>>
    rw[values_def]>>fs[EVERY_MEM,MEM_toAList,FORALL_PROD]>>
    first_x_assum drule>>
    strip_tac>>
    drule check_PR_sat_implies>>
    simp[]>>
    impl_tac >-
      (fs[values_def]>>
      metis_tac[])>>
    simp[])
  >>
    (* RAT *)
    match_mp_tac par_redundant>>
    qexists_tac`({interp_lit p} ∪
               IMAGE negate_literal (E ∪ interp_cclause C DIFF {interp_lit p}))`>>
               simp[]>>
    CONJ_TAC >- (
      match_mp_tac consistent_par_union>>
      rw[]
      >-
        metis_tac[consistent_par_DIFF]
      >>
        simp[EXTENSION]>>
        metis_tac[])>>
    CONJ_TAC >- (
      `interp_lit p ∈ interp_cclause C` by
        fs[interp_cclause_def]>>
      simp[EXTENSION]>>
      metis_tac[])>>
    match_mp_tac sat_implies_values>>
    rw[values_def]>>fs[EVERY_MEM,MEM_toAList,FORALL_PROD]>>
    first_x_assum drule>>
    strip_tac>>
    drule check_RAT_eq_check_PR>>
    rw[]>>
    drule check_PR_sat_implies>>
    simp[]>>
    impl_tac >-
      (fs[values_def]>>
      metis_tac[])>>
    simp[interp_cclause_def]
QED

(* Deletion preserves sat: if C is satisfiable, then deleting clauses from C keeps satisfiability *)
Theorem delete_preserves_satisfiable:
  satisfiable (interp C) ⇒ satisfiable (interp (delete n C))
Proof
  match_mp_tac satisfiable_SUBSET>>
  simp[interp_def]>>
  match_mp_tac IMAGE_SUBSET>>
  metis_tac[values_delete]
QED

Theorem delete_clauses_sound:
  ∀l fml. satisfiable (interp fml) ⇒
  satisfiable (interp (FOLDL (λa b. delete b a) fml l))
Proof
  Induct>>simp[]>>
  rw[]>>metis_tac[delete_preserves_satisfiable]
QED

Theorem interp_insert:
  interp (insert n p fml) ⊆ interp_cclause p INSERT interp fml
Proof
  simp[interp_def,SUBSET_DEF,PULL_EXISTS]>>
  rw[]>>drule values_insert>>rw[]>>
  metis_tac[]
QED

Theorem check_lrat_step_sound:
  ∀lrat fml fml'.
  wf_fml fml ∧
  (* TODO: should assume that PR never has 0s in the clause and prove in parser *)
  check_lrat_step lrat fml = SOME fml' ⇒
  (satisfiable (interp fml) ⇒ satisfiable (interp fml'))
Proof
  rw[check_lrat_step_def]>>
  qpat_x_assum `_ = SOME _`mp_tac>>
  TOP_CASE_TAC>>fs[]
  >-
    (simp[]>>
    metis_tac[delete_clauses_sound])
  >>
  rw[]>>
  `redundant (interp fml) (interp_cclause l)` by
    (match_mp_tac (GEN_ALL is_PR_redundant)>>
    simp[]>>
    PURE_REWRITE_TAC[Once CONJ_ASSOC]>>
    PURE_REWRITE_TAC[Once CONJ_COMM]>>
    asm_exists_tac>>
    simp[]>>
    Cases_on`l`>>simp[]>>
    cheat)>>
  fs[redundant_def]>>
  first_x_assum drule>>
  match_mp_tac satisfiable_SUBSET>>
  simp[interp_insert]
QED

Theorem wf_fml_delete_clauses:
  ∀l fml.
  wf_fml fml ⇒
  wf_fml (FOLDL (λa b. delete b a) fml l)
Proof
  simp[FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>
  rw[]>>first_x_assum drule>>
  rw[wf_fml_def]>>
  `C ∈ values (FOLDR (\b a . delete b a) fml ll)` by
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

Theorem check_lrat_step_wf_fml:
  ∀lrat fml fml'.
  wf_fml fml ∧
  check_lrat_step lrat fml = SOME fml' ⇒
  wf_fml fml'
Proof
  rw[check_lrat_step_def]>>
  qpat_x_assum `_ = SOME _`mp_tac>>
  TOP_CASE_TAC>>fs[]
  >-
    (simp[]>>
    metis_tac[wf_fml_delete_clauses])
  >>
  strip_tac>>
  rveq>>fs[]>>
  match_mp_tac wf_fml_insert>>fs[]>>
  cheat
QED

(* The main theorem *)
Theorem check_lrat_sound:
  ∀lrat fml.
  wf_fml fml ⇒
  check_lrat lrat fml = SOME fml' ⇒
  wf_fml fml' ∧
  (satisfiable (interp fml) ⇒ satisfiable (interp fml'))
Proof
  Induct >> simp[check_lrat_def]>>
  ntac 3 strip_tac>>
  every_case_tac>>fs[]>>
  strip_tac>>
  drule check_lrat_step_sound>>
  rpt (disch_then drule)>>
  cheat
  (*drule check_lrat_step_wf_fml>>
  rpt (disch_then drule)>>
  strip_tac>>
  strip_tac>>
  first_x_assum(qspec_then`x` mp_tac)>> simp[] *)
QED

Theorem is_unsat_sound:
  ∀fml.
  is_unsat fml ⇒
  unsatisfiable (interp fml)
Proof
  rw[is_unsat_def]>>
  match_mp_tac empty_clause_imp_unsatisfiable>>
  fs[MEM_MAP]>>Cases_on`y`>>fs[MEM_toAList,interp_def,values_def]>>
  qexists_tac`r`>>simp[interp_cclause_def]>>
  rw[]>>
  metis_tac[]
QED

Theorem check_lrat_unsat_sound:
  ∀lrat fml fml'.
  wf_fml fml ⇒
  check_lrat_unsat lrat fml ⇒
  unsatisfiable (interp fml)
Proof
  rw[check_lrat_unsat_def]>>
  every_case_tac>>fs[]>>
  drule is_unsat_sound>>
  drule check_lrat_sound>>
  metis_tac[unsatisfiable_def]
QED

(* Try on an example
val fml = rconc (EVAL
``insert 1 [ -3;  1;  2] (
  insert 2 [ -2; -1;  3] (
  insert 3 [ -4;  2;  3] (
  insert 4 [ -3; -2;  4] (
  insert 5 [ -4; -3; -1] (
  insert 6 [  1;  3;  4] (
  insert 7 [ -1;  2;  4] (
  insert 8 [ -4; -2; (1:int)] LN))))))) :ccnf``)

val lrat =
``[
  Delete [];
  PR 9 [-1] NONE [] (insert 1 [5;7] (insert 6 [2;7] (insert 8 [5;2] LN)));
]``;

(* result contains the empty clause *)
  val res = EVAL``check_lrat ^(lrat) ^(fml)``
*)

val _ = export_theory ();
