(*
   Basic specification of an LPR checker (minimal optimization)
*)
open preamble miscTheory mlstringTheory satSemTheory;

val _ = new_theory "lpr";

val _ = set_grammar_ancestry ["mlstring","satSem","sptree","integer","misc"];

(*
  Bridging implementation and semantics

  Clauses are lists of integers where positive (>0) integers map to INL and negative (<0) map to INR

  In implementation, clauses must not contain 0

  The ccnf type is the concrete "list"-based CNF representation

  The tccnf type is the concrete "sptree"-based CNF representation used by LRAT/LPR checking
  which adds an id to each clause
*)
Type lit = ``:int``;
Type cclause = ``:lit list``;
Type ccnf = ``:cclause list``;
Type tccnf = ``:cclause spt``;

Definition interp_lit_def:
  interp_lit (l:lit) =
  if l > 0 then INL (Num (ABS l))
  else INR (Num (ABS l))
End

Definition interp_cclause_def:
  interp_cclause (ls:cclause) =
  IMAGE interp_lit (set ls DIFF {0})
End

Definition interp_def:
  interp (fml:ccnf) =
  IMAGE interp_cclause (set fml)
End

Definition interp_spt_def:
  interp_spt (fml:tccnf) = IMAGE interp_cclause (range fml)
End

(* Implementation *)
val _ = Datatype`
  lprstep =
  | Delete (num list) (* Clauses to delete *)
  | PR num cclause (cclause option) (num list) ((num,(num list)) alist)`
    (* PR step:
      PR n C wopt i0 (ik id ~> ik)
      n is the new id of the clause C
      wopt is a witnessing assignment (represented as a list of literals)
        if w is NONE, then this reduces to RAT
      i0 is a list of clause IDs for the AT part
      ik is a alist mapping clause IDs to their hints
    *)

Type lpr = ``:lprstep list``

Definition delete_literals_def:
  delete_literals (C:cclause) (D:cclause) =
  FILTER (λx. ¬MEM x D) C
End

(*
  Checking for asymmetric tautology via unit propagation using the given hints.
  Returns:
  NONE => Error
  SOME (INL ()) => C is an AT
  SOME (INR C) => hints were insufficient, but C is now extended with units
*)
Definition is_AT_def:
  (is_AT fml [] (C:cclause) = SOME (INR C)) ∧
  (is_AT fml (i::is) C =
  case sptree$lookup i fml of
    NONE => NONE
  | SOME Ci =>
  case delete_literals Ci C of
    [] => SOME (INL ())
  | [l] => is_AT fml is (-l :: C)
  | _ => NONE)
End

(* Check if Ci overlaps with a list of assignments *)
Definition check_overlap_def:
  (check_overlap Ci [] = F) ∧
  (check_overlap Ci (a::as) =
    (MEM a Ci ∨ check_overlap Ci as))
End

(* flips a clause/assignment.
  for a clause, this yields its blocked assignment *)
Definition flip_def:
  flip (C:cclause) = MAP (λi. -i) C
End

(* Construct the overlapping assignment
  { w ∪ negate (C) }
  where w overrides everything in negate(C)
*)
Definition overlap_assignment_def:
  overlap_assignment w C =
    w ++ flip (delete_literals C w)
End

(* The (L)RAT check (no witnesses) *)
Definition check_RAT_def:
  check_RAT fml p C ik (i,Ci) =
  (* Step 5.1: if Ci contains -p do work, else skip *)
  if check_overlap Ci [-p] then
    (* Lookup the hint *)
    case ALOOKUP ik i of
      NONE => F
    | SOME is =>
    case is of
      (* Step 5.2: Ci is satisfied by p ∪ negate (C) *)
      [] => check_overlap Ci (overlap_assignment [p] C)
    | _ =>
      (* Step 5.3-5.5: Otherwise, use full hints *)
      is_AT fml is (C ++ (delete_literals Ci [-p])) = SOME (INL ())
  else
    T
End

(* Adding debug messages
open mlintTheory

Definition guard_def:
  guard P s =
  if P then P else
  (let _ = empty_ffi s in F)
End

guard (check_overlap Ci w) (strlit "5.2.1 failed: " ^ mlint$toString (&i))
guard (check_overlap Ci (overlap_assignment w C)) (strlit "5.2.2 failed: " ^ mlint$toString (&i))
guard (is_AT fml is (C ++ (delete_literals Ci (flip (overlap_assignment w C)))) = SOME (INL ()))
*)

(* The (L)PR check (witness given) *)
Definition check_PR_def:
  check_PR fml w C ik (i,Ci) =
  (* Step 5.1: if Ci is touched by w do work, else skip *)
  if check_overlap Ci (flip w) then
    (* Lookup the hint *)
    case ALOOKUP ik i of
      NONE =>
      (* Step 5.2.1: Ci is satisfied by w *)
      check_overlap Ci w
    | SOME is =>
    case is of
      (* Step 5.2.2: Ci is satisfied by w ∪ negate (C) *)
      [] =>
      check_overlap Ci (overlap_assignment w C)
    | _ =>
      (* Step 5.3-5.5: Otherwise use full hints *)
      is_AT fml is (C ++ (delete_literals Ci (flip (overlap_assignment w C)))) = SOME (INL ())
  else
    T
End

Definition is_PR_def:
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
    | SOME w => ¬(check_overlap w (flip w)) ∧ EVERY (check_PR fml w D ik) iCs
  else
     F
End

(*
  Deletions and updates can only happen above position index mindel
  By convention, setting mindel = 0 enables all deletions
  (clauses are 1-indexed by the parser)
*)
Definition check_lpr_step_def:
  check_lpr_step mindel step fml =
  case step of
    Delete cl =>
      if EVERY ($< mindel) cl then
        SOME (FOLDL (\a b. delete b a) fml cl)
      else
        NONE
  | PR n C w i0 ik =>
    let p = case C of [] => 0 | (x::xs) => x in
    if is_PR fml p C w i0 ik ∧ mindel < n then
      SOME (insert n C fml)
    else NONE
End

(* Run the LPR checker on fml, returning an option *)
Definition check_lpr_def:
  (check_lpr mindel [] fml = SOME fml) ∧
  (check_lpr mindel (step::steps) fml =
    case check_lpr_step mindel step fml of
      NONE => NONE
    | SOME fml' => check_lpr mindel steps fml')
End

(* Checking that the final formula contains a list of clauses *)

(* Canonical form for a clause, making transformation proofs easier to check *)
Definition sorted_dup_def:
  (sorted_dup (x::y::xs) =
  if x = (y:int) then sorted_dup (x::xs)
  else x::(sorted_dup (y::xs))) ∧
  (sorted_dup ls = ls)
End

Definition canon_clause_def:
  canon_clause cl = sorted_dup (QSORT (λi j. i ≤ (j:int)) cl)
End

Theorem set_sorted_dup:
  ∀cl.
  set (sorted_dup cl) = set cl
Proof
  ho_match_mp_tac (fetch "-" "sorted_dup_ind")>>
  rw[sorted_dup_def]
QED

Theorem set_QSORT:
  set (QSORT R ls) = set ls
Proof
  rw[EXTENSION,QSORT_MEM]
QED

Theorem canon_clause_interp:
  interp_cclause (canon_clause cl) = interp_cclause cl
Proof
  rw[canon_clause_def,interp_cclause_def]>>
  simp[set_sorted_dup,set_QSORT]
QED

Definition contains_clauses_def:
  contains_clauses fml cls =
  let ls = MAP (canon_clause o SND) (toAList fml) in
  EVERY (λcl. MEM (canon_clause cl) ls) cls
End

(* Checking unsatisfiability *)
Definition check_lpr_unsat_def:
  check_lpr_unsat lpr fml =
  case check_lpr 0 lpr fml of
    NONE => F
  | SOME fml' => contains_clauses fml' [[]]
End

(* Checking satisfiability equivalence after adding clauses *)
Definition check_lpr_sat_equiv_def:
  check_lpr_sat_equiv lpr fml mindel cls =
  case check_lpr mindel lpr fml of
    NONE => F
  | SOME fml' => contains_clauses fml' cls
End

(* Proofs *)
Definition wf_clause_def:
  wf_clause (C:cclause) ⇔ ¬ MEM 0 C
End

Definition wf_fml_def:
  wf_fml (fml:tccnf) ⇔
  ∀C. C ∈ range fml ⇒ wf_clause C
End

Definition wf_lpr_def:
  (wf_lpr (Delete _) = T) ∧
  (wf_lpr (PR n C wopt i0 ik) =
    (wf_clause C ∧
    case C of [] => T
    | h::t => case wopt of SOME w => MEM h w | _ => T)
  )
End

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
    asymmetric_tautology (interp_spt fml) (interp_cclause C)
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
      fs[Abbr`fml'`,range_def,interp_spt_def]>>
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
    (fs[wf_fml_def,range_def]>>
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
    fs[Abbr`fml'`,range_def,interp_spt_def]>>
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
      (interp_cclause D INSERT interp_spt fml)
      (interp_cclause C INSERT interp_spt fml)
Proof
  Induct>>fs[is_AT_def]>>
  rw[]
  >-
    (qexists_tac`{}`>>simp[sat_implies_def])>>
  every_case_tac>>fs[]>>
  `interp_cclause x DIFF interp_cclause C = interp_cclause (delete_literals x C)` by
    fs[interp_cclause_delete_literals]>>
  `wf_clause x` by
    (fs[wf_fml_def,range_def]>>
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
    (fs[satisfies_def,interp_spt_def,range_def]>>
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
  check_PR fml [p] C ik (i,Ci)
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
  check_PR fml w C ik (i,Ci) ∧ Ci ∈ range fml ∧
  wf_fml fml ∧ wf_clause C ∧ consistent_par (interp_cclause C) ⇒
  sat_implies (par (IMAGE negate_literal (interp_cclause C)) (interp_spt fml))
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
    simp[PULL_EXISTS,interp_spt_def]>>
    fs[EXTENSION]>>
    metis_tac[]) >>
  simp[]>>
  strip_tac>>
  `wf_clause Ci` by
    fs[wf_fml_def]>>
  Cases_on`ALOOKUP ik i`>>
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

Theorem sat_implies_range:
  (∀C. C ∈ range fml ⇒ sat_implies A (par w {interp_cclause C})) ⇒
  sat_implies A (par w (interp_spt fml))
Proof
  rw[sat_implies_def,satisfies_def,interp_spt_def,par_def]>>
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
  redundant (interp_spt fml) (interp_cclause C)
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
    match_mp_tac sat_implies_range>>
    rw[range_def]>>fs[EVERY_MEM,MEM_toAList,FORALL_PROD]>>
    first_x_assum drule>>
    strip_tac>>
    drule check_PR_sat_implies>>
    simp[]>>
    impl_tac >-
      (fs[range_def]>>
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
    match_mp_tac sat_implies_range>>
    rw[range_def]>>fs[EVERY_MEM,MEM_toAList,FORALL_PROD]>>
    first_x_assum drule>>
    strip_tac>>
    drule check_RAT_imp_check_PR>>
    rw[]>>
    drule check_PR_sat_implies>>
    simp[]>>
    impl_tac >-
      (fs[range_def]>>
      metis_tac[])>>
    simp[interp_cclause_def]
QED

(* Deletion preserves sat: if C is satisfiable, then deleting clauses from C keeps satisfiability *)
Theorem delete_preserves_satisfiable:
  satisfiable (interp_spt C) ⇒ satisfiable (interp_spt (delete n C))
Proof
  match_mp_tac satisfiable_SUBSET>>
  simp[interp_spt_def]>>
  match_mp_tac IMAGE_SUBSET>>
  metis_tac[range_delete]
QED

Theorem delete_clauses_sound:
  ∀l fml. satisfiable (interp_spt fml) ⇒
  satisfiable (interp_spt (FOLDL (λa b. delete b a) fml l))
Proof
  Induct>>simp[]>>
  rw[]>>metis_tac[delete_preserves_satisfiable]
QED

Theorem interp_insert:
  interp_spt (insert n p fml) ⊆ interp_cclause p INSERT interp_spt fml
Proof
  simp[interp_spt_def,SUBSET_DEF,PULL_EXISTS]>>
  rw[]>>
  drule range_insert_2>>
  rw[]>>
  metis_tac[]
QED

Theorem check_lpr_step_sound:
  ∀mindel lpr fml fml'.
  wf_fml fml ∧ wf_lpr lpr ∧
  check_lpr_step mindel lpr fml = SOME fml' ⇒
  (satisfiable (interp_spt fml) ⇒ satisfiable (interp_spt fml'))
Proof
  rw[check_lpr_step_def]>>
  qpat_x_assum `_ = SOME _`mp_tac>>
  TOP_CASE_TAC>>fs[]
  >-
    (simp[]>>
    metis_tac[delete_clauses_sound])
  >>
  rw[]>>
  `redundant (interp_spt fml) (interp_cclause l)` by
    (match_mp_tac (GEN_ALL is_PR_redundant)>>
    simp[]>>
    PURE_REWRITE_TAC[Once CONJ_ASSOC]>>
    PURE_REWRITE_TAC[Once CONJ_COMM]>>
    asm_exists_tac>>
    simp[]>>
    Cases_on`l`>>
    fs[wf_lpr_def])>>
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
  `C ∈ range (FOLDR (\b a . delete b a) fml ll)` by
    metis_tac[range_delete,SUBSET_DEF]>>
  fs[]
QED

Theorem wf_fml_insert:
  wf_fml fml ∧ wf_clause l ⇒
  wf_fml (insert n l fml)
Proof
  fs[wf_fml_def]>>rw[]>>
  drule range_insert_2>>
  metis_tac[]
QED

Theorem check_lpr_step_wf_fml:
  ∀mindel lpr fml fml'.
  wf_fml fml ∧ wf_lpr lpr ∧
  check_lpr_step mindel lpr fml = SOME fml' ⇒
  wf_fml fml'
Proof
  rw[check_lpr_step_def]>>
  qpat_x_assum `_ = SOME _`mp_tac>>
  TOP_CASE_TAC>>fs[]
  >-
    (simp[]>>
    metis_tac[wf_fml_delete_clauses])
  >>
  strip_tac>>
  rveq>>fs[]>>
  match_mp_tac wf_fml_insert>>fs[wf_lpr_def]
QED

(* The main operational theorem about check_lpr *)
Theorem check_lpr_sound:
  ∀mindel lpr fml.
  wf_fml fml ∧ EVERY wf_lpr lpr ⇒
  check_lpr mindel lpr fml = SOME fml' ⇒
  wf_fml fml' ∧
  (satisfiable (interp_spt fml) ⇒ satisfiable (interp_spt fml'))
Proof
  Induct_on`lpr` >> simp[check_lpr_def]>>
  ntac 3 strip_tac>>
  every_case_tac>>fs[]>>
  strip_tac>>
  drule check_lpr_step_sound>>
  rpt (disch_then drule)>>
  drule check_lpr_step_wf_fml>>
  rpt (disch_then drule)>>
  strip_tac>>
  strip_tac>>
  strip_tac>>
  first_x_assum drule>> simp[]>>
  metis_tac[]
QED

(* Theorems about mindel *)
Theorem lookup_FOLDL_delete':
  ∀l fml.
  lookup n fml = SOME c ∧
  EVERY ($< mindel) l ∧ n ≤ mindel ⇒
  lookup n (FOLDL (λa b. delete b a) fml l) = SOME c
Proof
  Induct>>rw[]>>fs[]>>
  first_x_assum match_mp_tac>>
  rw[lookup_delete]>>
  CCONTR_TAC>>fs[]
QED

Theorem check_lpr_step_mindel:
  check_lpr_step mindel lpr fml = SOME fml' ⇒
  ∀n c. n ≤ mindel ∧
    lookup n fml = SOME c ⇒
    lookup n fml' = SOME c
Proof
  rw[check_lpr_step_def]>>
  every_case_tac>>fs[]>>rw[lookup_insert]>>
  match_mp_tac lookup_FOLDL_delete'>>
  fs[EVERY_MEM]
QED

Theorem check_lpr_mindel:
  ∀mindel lpr fml.
  check_lpr mindel lpr fml = SOME fml' ⇒
  ∀n c. n ≤ mindel ∧
    lookup n fml = SOME c ⇒
    lookup n fml' = SOME c
Proof
  Induct_on`lpr`>> rw[check_lpr_def]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  disch_then drule>>
  disch_then match_mp_tac>>
  drule check_lpr_step_mindel>>
  disch_then drule>>
  disch_then match_mp_tac>>
  metis_tac[]
QED

(* Build a tccnf from a ccnf *)
Definition build_fml_def:
  (build_fml (id:num) [] = LN:tccnf) ∧
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

Theorem interp_build_fml:
  interp_spt (build_fml id fml) = interp fml
Proof
  simp[interp_spt_def,range_build_fml,interp_def]
QED

Theorem wf_fml_build_fml:
  EVERY wf_clause ls ⇒
  wf_fml (build_fml id ls)
Proof
  simp[wf_fml_def,range_build_fml,EVERY_MEM]
QED

(* Connect theorems to ccnf representation *)
Theorem check_lpr_unsat_sound:
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧
  check_lpr_unsat lpr (build_fml id fml) ⇒
  unsatisfiable (interp fml)
Proof
  rw[check_lpr_unsat_def]>>
  every_case_tac>>fs[]>>
  `unsatisfiable (interp_spt x)` by (
    match_mp_tac empty_clause_imp_unsatisfiable>>
    fs[contains_clauses_def]>>
    fs[MEM_MAP]>>Cases_on`y`>>fs[MEM_toAList,interp_spt_def,range_def]>>
    qexists_tac`r`>>
    simp[]>>
    `canon_clause [] = [] ∧ interp_cclause [] = {}` by
      (simp[interp_cclause_def]>>
      EVAL_TAC)>>
    metis_tac[canon_clause_interp,interp_cclause_def])>>
  drule wf_fml_build_fml>>
  disch_then (qspec_then`id` assume_tac)>>
  drule check_lpr_sound>>
  metis_tac[unsatisfiable_def,interp_build_fml]
QED

(* This theorem is unused *)
Theorem check_lpr_sat_equiv_add:
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧
  id + LENGTH fml ≤ mindel ∧
  check_lpr_sat_equiv lpr (build_fml id fml) mindel cls ⇒
  satisfiable (interp fml) ⇒
  satisfiable (interp (fml ++ cls))
Proof
  rw[check_lpr_sat_equiv_def]>>
  every_case_tac>>fs[contains_clauses_def]>>
  drule wf_fml_build_fml>>
  disch_then (qspec_then`id` assume_tac)>>
  drule check_lpr_sound>>
  rpt (disch_then drule)>>
  fs[interp_build_fml]>>rw[]>>
  `interp_spt (build_fml id fml) ⊆ interp_spt x` by (
    drule check_lpr_mindel>>
    simp[lookup_build_fml]>>
    rw[interp_build_fml,interp_def]>>
    simp[interp_spt_def,range_def,SUBSET_DEF]>>
    rw[]>>
    fs[MEM_EL]>>
    first_x_assum(qspec_then `n+id` mp_tac)>>simp[]>>
    metis_tac[])>>
  `IMAGE interp_cclause (set cls) ⊆ interp_spt x` by (
    rw[SUBSET_DEF]>>
    fs[EVERY_MEM,MEM_toAList,EXISTS_PROD,MEM_MAP]>>
    first_x_assum drule>>rw[]>>
    fs[interp_spt_def,range_def]>>
    metis_tac[canon_clause_interp])>>
  qpat_x_assum`satisfiable _` mp_tac>>
  match_mp_tac (satisfiable_SUBSET)>>
  fs[interp_build_fml, interp_def]
QED

Theorem check_lpr_sat_equiv_fml:
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧
  check_lpr_sat_equiv lpr (build_fml id fml) mindel fml2 ⇒
  satisfiable (interp fml) ⇒
  satisfiable (interp fml2)
Proof
  rw[check_lpr_sat_equiv_def]>>
  every_case_tac>>fs[contains_clauses_def]>>
  drule wf_fml_build_fml>>
  disch_then (qspec_then`id` assume_tac)>>
  drule check_lpr_sound>>
  rpt (disch_then drule)>>
  fs[interp_build_fml]>>
  rw[]>>
  `IMAGE interp_cclause (set fml2) ⊆ interp_spt x` by (
    rw[SUBSET_DEF]>>
    fs[EVERY_MEM,MEM_toAList,EXISTS_PROD,MEM_MAP]>>
    first_x_assum drule>>rw[]>>
    fs[interp_spt_def,range_def]>>
    metis_tac[canon_clause_interp])>>
  qpat_x_assum`satisfiable _` mp_tac>>
  match_mp_tac (satisfiable_SUBSET)>>
  fs[interp_def]
QED

(* Top-level DRAT-style proofs, i.e., every line is a clause that is either deleted or added *)
val _ = Datatype`
  step =
    Del cclause (* Clause to delete *)
  | Add cclause` (* Clause to add *)

Type proof = ``:step list``

(* Run the top-level proof operations on a formula *)
Definition run_proof_step_def:
  (run_proof_step fml (Del cl) = FILTER ($≠ cl) fml) ∧
  (run_proof_step fml (Add cl) = fml ++ [cl])
End

Definition run_proof_def:
  run_proof fml pf = FOLDL run_proof_step fml pf
End

(* Del case not technically necessary, but useful for parsing *)
Definition wf_proof_def:
  (wf_proof (Del C) = wf_clause C) ∧
  (wf_proof (Add C) = wf_clause C)
End

(* As a first step towards verification, define a version operating over sptrees *)
Definition run_proof_step_spt_def:
  (run_proof_step_spt (fml,n) (Del cl) =
    let kv = toAList fml in
    let l = MAP FST (FILTER (λ(k,v). cl = v) kv) in
      (FOLDL (\a b. delete b a) fml l, n)) ∧
  (run_proof_step_spt (fml,n:num) (Add cl) =
    (insert n cl fml,n+1))
End

Definition run_proof_spt_def:
  run_proof_spt fmln pf = FOLDL run_proof_step_spt fmln pf
End

Definition check_lpr_range_def:
  check_lpr_range lpr fml n pf i j =
  if i ≤ j then
    let (fml1,n1) = run_proof_spt (fml,n) (TAKE i pf) in
    let (fml2,n2) = run_proof_spt (fml1,n1) (DROP i (TAKE j pf)) in
    let vals = MAP SND (toAList fml2) in
    check_lpr_sat_equiv lpr fml1 0 vals
  else F
End

Theorem lookup_FOLDL_delete:
  ∀l k fml.
  lookup k (FOLDL (\a b. delete b a) fml l) =
  if MEM k l then NONE
  else lookup k fml
Proof
  Induct>>rw[]>>fs[lookup_delete]
QED

Theorem wf_run_proof_spt:
  ∀pf fml n fml' n'.
  run_proof_spt (fml,n) pf = (fml',n') ∧
  EVERY wf_proof pf ∧
  wf_fml fml ⇒
  wf_fml fml'
Proof
  Induct>>fs[run_proof_spt_def]>>
  Cases>>simp[run_proof_step_spt_def,wf_proof_def]>>
  rw[]>>
  first_x_assum drule>>
  rpt(disch_then drule)>>
  disch_then match_mp_tac>>
  fs[wf_fml_def]
  >- (
    fs[range_def,lookup_FOLDL_delete,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList]>>
    metis_tac[])>>
  metis_tac[range_insert_2]
QED

Theorem MAP_ALL_DISTINCT_FILTER:
  ALL_DISTINCT (MAP f ls) ⇒
  ALL_DISTINCT (MAP f (FILTER P ls))
Proof
  Induct_on`ls`>>rw[MEM_FILTER,MEM_MAP]
QED

Theorem run_proof_spt_interp:
  ∀pf fmlspt n fmlspt' n' fml.
  run_proof_spt (fmlspt,n) pf = (fmlspt',n') ∧
  range fmlspt = set fml ∧
  (∀x. x ∈ domain fmlspt ⇒ x < n)
  ⇒
  range fmlspt' = set (run_proof fml pf) ∧
  (∀x. x ∈ domain fmlspt' ⇒ x < n')
Proof
  Induct>>fs[run_proof_def,run_proof_spt_def]>>
  Cases>>simp[run_proof_step_spt_def,run_proof_step_def]>>
  ntac 6 strip_tac>>
  first_x_assum drule>>
  disch_then match_mp_tac
  >- (
    fs[range_def,domain_lookup,lookup_FOLDL_delete,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList]>>
    fs[domain_lookup]>>
    reverse CONJ_TAC >- metis_tac[]>>
    pop_assum kall_tac>>
    last_x_assum kall_tac>>
    fs[EXTENSION,MEM_MAP,MEM_FILTER,MEM_toAList,range_def,EXISTS_PROD]>>
    metis_tac[SOME_11])
  >>
    DEP_REWRITE_TAC [range_insert]>>
    CONJ_TAC>-
      (CCONTR_TAC>>rw[]>>first_x_assum drule>>simp[])>>
    CONJ_TAC>-
      (fs[EXTENSION]>>metis_tac[])>>
    rw[]>>fs[]>>
    first_x_assum drule>>simp[]
QED

Theorem run_proof_APPEND:
  run_proof fml (pf1++pf2) = run_proof (run_proof fml pf1) pf2
Proof
  simp[run_proof_def,FOLDL_APPEND]
QED

Theorem check_lpr_range_sound:
  EVERY wf_clause fml ∧ EVERY wf_lpr lpr ∧ EVERY wf_proof pf ∧
  id + LENGTH fml ≤ n ∧
  check_lpr_range lpr (build_fml id fml) n pf i j ⇒
  satisfiable (interp (run_proof fml (TAKE i pf))) ⇒
  satisfiable (interp (run_proof fml (TAKE j pf)))
Proof
  rw[check_lpr_range_def]>>
  rpt(pairarg_tac>>fs[])>>
  fs[check_lpr_sat_equiv_def]>>
  every_case_tac>>fs[]>>
  drule wf_fml_build_fml>> disch_then(qspec_then `id` assume_tac)>>
  qpat_x_assum` _ = (fml1,n1)` assume_tac>>
  drule wf_run_proof_spt>>
  simp[EVERY_TAKE]>>
  strip_tac>>
  drule check_lpr_sound>>
  rpt (disch_then drule)>>
  strip_tac>>
  drule run_proof_spt_interp>>
  disch_then(qspec_then`fml` mp_tac)>>
  impl_tac>-
    simp[range_build_fml,domain_lookup,lookup_build_fml]>>
  rw[]>>
  qpat_x_assum` _ ⇒ _` mp_tac>>
  impl_tac >-
    fs[interp_def,interp_spt_def]>>
  qpat_x_assum` _ = (fml2,n2)` assume_tac>>
  drule run_proof_spt_interp>>
  disch_then drule>>
  simp[GSYM run_proof_APPEND]>>
  rw[]>>
  `TAKE i pf ++ DROP i (TAKE j pf) = TAKE j pf` by
    (simp[DROP_TAKE]>>
    metis_tac[take_drop_partition])>>
  simp[]>>
  `interp (run_proof fml (TAKE j pf)) ⊆ interp_spt x` by (
    fs[contains_clauses_def,EVERY_MEM,MEM_toAList,EXISTS_PROD,MEM_MAP,interp_def]>>
    qpat_x_assum`value _ = set _` sym_sub_tac>>
    rw[SUBSET_DEF,range_def]>>
    fs[PULL_EXISTS]>>
    first_x_assum drule>>rw[]>>
    fs[interp_spt_def,range_def]>>
    metis_tac[canon_clause_interp])>>
  qpat_x_assum`satisfiable _` mp_tac>>
  match_mp_tac (satisfiable_SUBSET)>>
  fs[interp_def]
QED

val _ = export_theory ();
