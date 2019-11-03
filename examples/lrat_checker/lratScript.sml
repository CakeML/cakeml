(*
   Verification of LRAT checker
*)
open preamble miscTheory mlstringTheory;

val _ = new_theory "lrat";

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

(* General stuff about satisfiability *)

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

Theorem satisfies_clause_append:
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

(* Definition of asymmetric tautologies *)
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

(* Definition of resolution asymmetric tautology *)
val resolution_asymmetric_tautology_def = Define`
  resolution_asymmetric_tautology fml C ⇔
  (asymmetric_tautology fml C ∨
  ∃l. l ∈ C ∧
  ∀D. D ∈ fml ∧ negate_literal l ∈ D ⇒
    asymmetric_tautology fml (C ∪ delete_literal (negate_literal l) D))`

(* soundness of resolution step *)
(*
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
*)

val flip_literal_def = Define`
  flip_literal l (w:'a assignment) =
  case l of
    INL x =>
    λv. if v = x then ¬w x else w v
  | INR x =>
    λv. if v = x then ¬w x else w v`

Theorem flip_literal_eq_neg:
  flip_literal l w = flip_literal (negate_literal l) w
Proof
  simp[flip_literal_def]>>
  TOP_CASE_TAC>>fs[negate_literal_def]
QED

Theorem flip_literal_flips:
  (satisfies_literal w l ⇔ ¬(satisfies_literal (flip_literal l w) l))
Proof
  rw[satisfies_literal_def,flip_literal_def]>>
  TOP_CASE_TAC>>fs[]
QED

Theorem flip_literal_unaffected:
  satisfies_literal w l ∧
  satisfies_clause w C ∧ l ∉ C ⇒
  satisfies_clause (flip_literal l w ) C
Proof
  rw[satisfies_clause_def,satisfies_literal_def]>>
  asm_exists_tac>>fs[]>>rw[]>>fs[]>>
  every_case_tac>>fs[flip_literal_def]>>
  metis_tac[]
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
  qabbrev_tac`Ds = IMAGE (λD. C ∪ delete_literal (negate_literal l) D) { D | D ∈ fml ∧  (negate_literal l) ∈  D}`>>
  `∀D. D ∈ Ds ⇒ asymmetric_tautology fml D` by
    (rw[]>>fs[Abbr`Ds`])>>
  drule asymmetric_tautology_set_satisfies >>
  disch_then drule>>
  strip_tac>>
  fs[satisfies_union]>>
  qabbrev_tac`w' = flip_literal l w`>>
  qexists_tac`w'` >> rw[satisfies_INSERT]
  >- (
    `satisfies_literal w' l` by
      (simp[Abbr`w'`]>>
      metis_tac[flip_literal_flips,satisfies_clause_def])>>
    metis_tac[satisfies_clause_def])
  >>
    `fml = { D | D ∈ fml ∧ ¬(negate_literal l ∈  D)} ∪ { D | D ∈ fml ∧ (negate_literal l ∈  D)}` by
      (simp[EXTENSION]>>
      metis_tac[])>>
    pop_assum SUBST1_TAC>>
    rw[satisfies_union]
    >- (
      fs[satisfies_def]>>rw[]>>
      fs[Abbr`w'`]>>
      simp[Once flip_literal_eq_neg]>>
      match_mp_tac flip_literal_unaffected>>
      metis_tac[satisfies_literal_exclusive,satisfies_clause_def])
    >>
      fs[satisfies_def]>>rw[]>>
      `C ∪ delete_literal (negate_literal l) C' ∈ Ds` by
        (fs[Abbr`Ds`]>>
        qexists_tac`C'`>>fs[])>>
      first_x_assum drule>> disch_then kall_tac>>
      first_x_assum drule>>
      simp[satisfies_clause_append]>>
      strip_tac>>
      `satisfies_clause w' (delete_literal (negate_literal l) C')` by
        (simp[Abbr`w'`]>>
        simp[Once flip_literal_eq_neg]>>
        match_mp_tac flip_literal_unaffected>>
        fs[delete_literal_def]>>
        metis_tac[satisfies_literal_exclusive,satisfies_clause_def])>>
      metis_tac[delete_literal_preserves_satisfies_clause_imp]
QED

(* Bridging implementation and semantics

  Clauses are represented by two sptree sets
  The left set corresponds to the "INL" and right to INR
*)
Type cclause = ``:num_set # num_set``;
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

val interp_cclause_def = Define`
  interp_cclause ((L,R):cclause) =
  IMAGE INL (domain L) ∪
  IMAGE INR (domain R)`

val interp_def = Define`
  interp (fml:ccnf) = IMAGE interp_cclause (values fml)`

(*** Implementation ***)
val _ = Datatype`
  lratstep =
    Delete (num list) (* Clauses to delete *)
  | RAT num (num + num) cclause (num list) ((num list) spt)`
    (* RAT step:
      RAT n p C i0 (ik id ~> ik)
      n is the new id of the new clause C
      p is the pivot (first element of C in the input)
      i0 is a list of clause IDs for the AT part
      ik is a sptree mapping clause IDs to their hints
    *)

Type lrat = ``:lratstep list``

val list_delete_def = Define`
  list_delete cl fml = FOLDR delete fml cl`

(* C - D *)
val delete_literals_def = Define`
  delete_literals (C:cclause) (D:cclause) =
  let dl = (MAP FST (toAList (FST D))) in
  let dr = (MAP FST (toAList (SND D))) in
  (list_delete dl (FST C), list_delete dr (SND C))`

val insert_literal_def = Define`
  insert_literal l b C =
  if b then (insert l () (FST C),SND C)
  else (FST C, insert l () (SND C))`

(*
  Checking for asymmetric tautology via unit propagation using the given hints
  NONE == Error
  SOME (INL ()) == C is an AT
  SOME (INR C) == hints were insufficient, but C is now extended with units
*)
val is_AT_def = Define`
  (is_AT fml [] (C:cclause) = SOME (INR C)) ∧
  (is_AT fml (i::is) C =
  case lookup i fml of
    NONE => NONE
  | SOME Ci =>
  let (Dl,Dr) = delete_literals Ci C in
  let Dll = toAList Dl in
  let Drr = toAList Dr in
  case (Dll,Drr) of
    ([],[])  => SOME (INL ())
  | ([l,_],[]) => is_AT fml is (insert_literal l F C)
  | ([],[l,_]) => is_AT fml is (insert_literal l T C)
  | _ => NONE)`

val has_literal_def = Define`
  has_literal l C =
  case l of
    INL x => lookup x (FST C) = SOME ()
  | INR x => lookup x (SND C) = SOME ()`

val has_neg_literal_def = Define`
  has_neg_literal l C =
  case l of
    INL x => lookup x (SND C) = SOME ()
  | INR x => lookup x (FST C) = SOME ()`

val delete_neg_literal_def = Define`
  delete_neg_literal l C =
  case l of
    INL x => (FST C, delete x (SND C))
  | INR x => (delete x (FST C), SND C)`

val find_exists_def = Define`
  (find_exists s [] = F) ∧
  (find_exists s (x::xs) = (lookup (FST x) s = SOME () ∨ find_exists s xs))`

val find_tauto_def = Define`
  find_tauto (LC,RC) (LD,RD) =
  (find_exists LC (toAList RD) ∨ find_exists RC (toAList LD))`

val cclause_union_def = Define`
  cclause_union (L1,R1) (L2,R2) =
  (union L1 L2, union R1 R2)`

(*
  Resolution Asymmetric Tautology
*)
val is_RAT_aux_def = Define`
  (is_RAT_aux fml p C ik [] = T) ∧
  (is_RAT_aux fml p C ik (iCi::iCs) =
  case iCi of (i,Ci) =>
    if has_neg_literal p  Ci then
      case lookup i ik of
        NONE => F
      | SOME is =>
        case is of [] =>
        (* Step 5.2: can be made more efficient *)
          if find_tauto C (delete_neg_literal p Ci) then
            is_RAT_aux fml p C ik iCs
          else
            F
        | _ =>
          (* Step 5.3-5.5 *)
          if is_AT fml is (cclause_union C (delete_neg_literal p Ci)) = SOME (INL ()) then
            is_RAT_aux fml p C ik iCs
          else
            F
    else
      is_RAT_aux fml p C ik iCs)`

val is_RAT_def = Define`
  is_RAT fml p (C:cclause) i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT fml i0 C of
    NONE => F
  | SOME (INL ()) => T
  | SOME (INR D) =>
  if has_literal p C then
    let iCs = toAList fml in
      is_RAT_aux fml p D ik iCs
  else
     F`

(* Run the LRAT checker on fml, returning an option *)
val check_lrat_def = Define`
  (check_lrat [] fml = SOME fml) ∧
  (check_lrat (step::steps) fml =
    case step of
      Delete cl =>
      let _ = empty_ffi (strlit ("Deleting: ")) in
      check_lrat steps (list_delete cl fml)
    | RAT n p C i0 ik =>
      let _ = empty_ffi (strlit ("RAT size: " )) in
      if is_RAT fml p C i0 ik then
        check_lrat steps (insert n C fml)
      else NONE)`

val check_lrat_unsat_def = Define`
  check_lrat_unsat lrat fml =
  let _ = empty_ffi (strlit ("Starting LRAT check")) in
  case check_lrat lrat fml of
    NONE => F
  | SOME fml' =>
    let _ = empty_ffi (strlit ("Checking unsatisfiability")) in
    let ls = MAP SND (toAList fml') in
    MEM (LN,LN) ls`

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

(*
val wf_clause_def = Define`
  wf_clause (C:cclause) ⇔
  lookup cmp 0 C = NONE ∧
  map_ok C`

val wf_fml_def = Define`
  wf_fml (f:ccnf) ⇔ ∀C. C ∈ values f ⇒ wf_clause C`
*)

Theorem list_delete_correct:
  ∀ls sp x v.
  lookup x (list_delete ls sp) = SOME v ⇔
  lookup x sp = SOME v ∧ ¬MEM x ls
Proof
  Induct>>fs[list_delete_def,lookup_delete]>>
  metis_tac[]
QED

Theorem list_delete_domain:
  domain (list_delete ls sp) =
  domain sp DIFF set ls
Proof
  rw[EXTENSION,domain_lookup]>>
  metis_tac[list_delete_correct]
QED

Theorem delete_literals_correct:
  interp_cclause (delete_literals C D) =
  interp_cclause C DIFF interp_cclause D
Proof
  Cases_on`C`>>Cases_on`D`>>
  simp[delete_literals_def]>>
  fs[interp_cclause_def,list_delete_domain]>>
  fs[EXTENSION,toAList_domain]>>
  rw[EQ_IMP_THM]>>
  metis_tac[]
QED

Theorem interp_cclause_toAList:
  interp_cclause (L,R) =
  set (MAP (INL o FST) (toAList L)) ∪
  set (MAP (INR o FST) (toAList R))
Proof
  rw[interp_cclause_def,EXTENSION,GSYM MAP_MAP_o]>>
  simp[Once MEM_MAP,toAList_domain]>>
  simp[Once MEM_MAP,toAList_domain]
QED

Theorem interp_cclause_insert_literal:
  (interp_cclause (insert_literal q T C) = INL q INSERT interp_cclause C) ∧
  (interp_cclause (insert_literal q F C) = INR q INSERT interp_cclause C)
Proof
  Cases_on`C`>>rw[interp_cclause_def,insert_literal_def,EXTENSION]>>
  metis_tac[]
QED

(* Implementation *)
Theorem is_AT_imp_asymmetric_tautology:
  ∀is fml C.
  (* wf_fml fml ∧ wf_clause C ∧ *)
  is_AT fml is C = SOME (INL ()) ⇒
  asymmetric_tautology (interp fml) (interp_cclause C)
Proof
  Induct>>fs[is_AT_def]>>
  ntac 4 strip_tac>>
  every_case_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  `interp_cclause x DIFF interp_cclause C = interp_cclause (Dl,Dr)` by
    metis_tac[delete_literals_correct]>>
  every_case_tac>>fs[]
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
    `interp_cclause (Dl,Dr) = {}` by
      fs[interp_cclause_toAList]>>
    simp[]>>
    match_mp_tac empty_clause_imp_unsatisfiable>>
    fs[])
  >>
    (last_x_assum drule>>
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
      fs[interp_cclause_toAList,interp_cclause_insert_literal,Abbr`fml'`]>>
      fs[UNION_INSERT_EQ,negate_literal_def])
QED

Theorem satisfies_clause_DIFF:
  satisfies_clause w C ∧
  ¬satisfies_clause w D ⇒
  satisfies_clause w (C DIFF D)
Proof
  fs[satisfies_clause_def]>>
  metis_tac[]
QED

Theorem is_AT_imp_sat_preserving:
  ∀is fml C D.
  is_AT fml is C = SOME (INR D) ⇒
  ∃E.
    interp_cclause D = E ∪ interp_cclause C ∧
    ∀w.
    satisfies w (interp_cclause D INSERT interp fml) ⇒
    satisfies w (interp_cclause C INSERT interp fml)
Proof
  Induct>>fs[is_AT_def]
  >-
    (rw[]>>qexists_tac`{}`>>fs[])>>
  rw[]>>
  every_case_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  `interp_cclause x DIFF interp_cclause C = interp_cclause (Dl,Dr)` by
    metis_tac[delete_literals_correct]>>
  every_case_tac>>fs[]
  >-
    (first_x_assum drule>>strip_tac>>
    fs[interp_cclause_insert_literal]>>
    qexists_tac`E ∪ {INR q}`>>
    CONJ_ASM1_TAC>-
      metis_tac[UNION_ASSOC,INSERT_SING_UNION]>>
    pop_assum SUBST_ALL_TAC>>
    qpat_x_assum`_ D = _` SUBST_ALL_TAC>>
    rw[]>>fs[]>>
    first_x_assum drule>>
    strip_tac>>
    fs[satisfies_INSERT]>>
    `satisfies_clause w (interp_cclause x)` by
      (fs[satisfies_def,interp_def,values_def]>>
      metis_tac[])>>
    Cases_on`satisfies_clause w (interp_cclause C)`>>fs[]>>
    `interp_cclause x DIFF interp_cclause C = {INL q}` by
      fs[interp_cclause_toAList]>>
    `satisfies_clause w {INL q}` by
      metis_tac[satisfies_clause_DIFF]>>
     pop_assum mp_tac>> simp[satisfies_clause_def]>>
     simp[Once (satisfies_literal_exclusive),negate_literal_def]>>
     fs[satisfies_clause_INSERT])
  >>
    (first_x_assum drule>>strip_tac>>
    fs[interp_cclause_insert_literal]>>
    qexists_tac`E ∪ {INL q}`>>
    CONJ_ASM1_TAC>-
      metis_tac[UNION_ASSOC,INSERT_SING_UNION]>>
    pop_assum SUBST_ALL_TAC>>
    qpat_x_assum`_ D = _` SUBST_ALL_TAC>>
    rw[]>>fs[]>>
    first_x_assum drule>>
    strip_tac>>
    fs[satisfies_INSERT]>>
    `satisfies_clause w (interp_cclause x)` by
      (fs[satisfies_def,interp_def,values_def]>>
      metis_tac[])>>
    Cases_on`satisfies_clause w (interp_cclause C)`>>fs[]>>
    `interp_cclause x DIFF interp_cclause C = {INR q}` by
      fs[interp_cclause_toAList]>>
    `satisfies_clause w {INR q}` by
      metis_tac[satisfies_clause_DIFF]>>
     pop_assum mp_tac>> simp[satisfies_clause_def]>>
     simp[Once (satisfies_literal_exclusive),negate_literal_def]>>
     fs[satisfies_clause_INSERT])
QED

Theorem find_exists_mem:
  ∀ls. find_exists s ls ⇒ ∃k v. (k ∈ domain s ∧ MEM (k,v) ls)
Proof
  Induct>>fs[find_exists_def]>>Cases>>fs[]>>
  rw[]>>fs[domain_lookup]>>metis_tac[]
QED

Theorem find_tauto_correct:
  ∀C D.
  find_tauto C D ⇒
  ∃l. l ∈ interp_cclause C ∧ negate_literal l ∈ interp_cclause D
Proof
  Cases>>Cases>>rw[find_tauto_def]>>
  drule find_exists_mem>>
  rw[]>>fs[MEM_toAList]>>
  fs[interp_cclause_def,domain_lookup]
  >-
    (qexists_tac`INL k`>>simp[negate_literal_def])
  >>
    qexists_tac`INR k`>>simp[negate_literal_def]
QED

Theorem interp_cclause_cclause_union:
  interp_cclause (cclause_union C D)=
  interp_cclause C ∪ interp_cclause D
Proof
  Cases_on`C`>>Cases_on`D`>>fs[cclause_union_def,interp_cclause_def]>>
  simp[domain_union]>>
  metis_tac[UNION_COMM,UNION_ASSOC]
QED

Theorem is_RAT_aux_imp:
  ∀iCs fml p C ik.
  is_RAT_aux fml p C ik iCs ⇒
  ∀i Ci. MEM (i,Ci) iCs ∧ has_neg_literal p Ci ⇒
    asymmetric_tautology (interp fml) (interp_cclause C ∪ interp_cclause (delete_neg_literal p Ci))
Proof
  Induct>>Cases>>fs[is_RAT_aux_def]>>
  ntac 4 strip_tac >>
  reverse IF_CASES_TAC>>fs[]
  >-
    (* 5.1 *)
    (strip_tac>>fs[PULL_FORALL,AND_IMP_INTRO]>>
    rw[]>>first_x_assum match_mp_tac>>fs[]>>
    metis_tac[])
  >>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>-
    (strip_tac>>first_x_assum drule>> simp[]>>
    reverse (rw[]) >- metis_tac[]>>
    match_mp_tac (GEN_ALL tautology_asymmetric_tautology)>>
    drule find_tauto_correct>>
    rw[]>>qexists_tac`l`>>simp[])
  >>
  (* 5.3 *)
  reverse (rw[]>>fs[])
  >- metis_tac[]
  >>
  last_x_assum kall_tac>> fs[]>>
  drule is_AT_imp_asymmetric_tautology>>
  metis_tac[interp_cclause_cclause_union]
QED

Theorem delete_literal_negate_literal:
  delete_literal (negate_literal p) (interp_cclause x) = interp_cclause (delete_neg_literal p x)
Proof
  Cases_on`p`>>
  Cases_on`x`>>
  simp[delete_literal_def,delete_neg_literal_def,interp_cclause_def,EXTENSION,negate_literal_def]>>
  rw[EQ_IMP_THM]
QED

Theorem has_literal_literal:
  has_literal p x ⇔ p ∈ interp_cclause x
Proof
  Cases_on`x`>>Cases_on`p`>>simp[has_literal_def,interp_cclause_def]>>
  simp[domain_lookup]
QED

Theorem has_neg_literal_negate_literal:
  has_neg_literal p x ⇔ negate_literal p ∈ interp_cclause x
Proof
  Cases_on`x`>>Cases_on`p`>>simp[has_neg_literal_def,negate_literal_def,interp_cclause_def]>>
  simp[domain_lookup]
QED

Theorem is_RAT_imp_resolution_asymmetric_tautology:
  ∀fml p C i0 ik.
  is_RAT fml p C i0 ik ⇒
  satisfiable (interp fml) ⇒ satisfiable ((interp_cclause C) INSERT interp fml)
Proof
  rw[is_RAT_def]>>
  ntac 2 (pop_assum mp_tac)>> ntac 2 TOP_CASE_TAC>>fs[]
  >-
    (drule is_AT_imp_asymmetric_tautology>>
    rpt (disch_then drule)>>
    metis_tac[asymmetric_tautology_satisfiable]) >>
  drule is_AT_imp_sat_preserving>>
  rw[]>>
  drule is_RAT_aux_imp>>
  fs[has_literal_literal]>>
  simp[MEM_toAList]>>
  strip_tac>>
  `resolution_asymmetric_tautology (interp fml) (interp_cclause y)` by
    (simp[resolution_asymmetric_tautology_def]>>
    DISJ2_TAC>>
    qexists_tac`p`>>fs[interp_def,PULL_EXISTS,values_def]>>
    fs[delete_literal_negate_literal,has_neg_literal_negate_literal]>>
    metis_tac[])>>
  drule resolution_asymmetric_tautology_satisfiable>>
  metis_tac[satisfiable_def]
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
  satisfiable (interp (list_delete l fml))
Proof
  simp[list_delete_def]>>
  Induct>>simp[]>>
  rw[]>>metis_tac[delete_preserves_satisfiable]
QED

(*
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
*)
Theorem interp_insert:
  interp (insert n p fml) ⊆ interp_cclause p INSERT interp fml
Proof
  simp[interp_def,SUBSET_DEF,PULL_EXISTS]>>
  rw[]>>drule values_insert>>rw[]>>
  metis_tac[]
QED

(* The main theorem *)
Theorem check_lrat_sound:
  ∀lrat fml.
  check_lrat lrat fml = SOME fml' ⇒
  satisfiable (interp fml) ⇒ satisfiable (interp fml')
Proof
  Induct >> fs[check_lrat_def]>>
  Cases
  >- (
    simp[]>>
    metis_tac[delete_clauses_sound])
  >>
  rw[]>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  disch_then match_mp_tac>>
  fs[has_literal_literal]>>
  drule is_RAT_imp_resolution_asymmetric_tautology>>
  disch_then drule>>
  match_mp_tac satisfiable_SUBSET>>
  metis_tac[interp_insert]
QED

Theorem check_lrat_unsat_sound:
  ∀lrat fml fml'.
  check_lrat_unsat lrat fml ⇒
  unsatisfiable (interp fml)
Proof
  rw[check_lrat_unsat_def]>>
  every_case_tac>>fs[MEM_MAP]>>
  `unsatisfiable (interp x)` by
    (match_mp_tac empty_clause_imp_unsatisfiable>>
    Cases_on`y`>>fs[interp_def,values_def,MEM_toAList]>>
    `interp_cclause r = {}` by
      rw[interp_cclause_def]>>
    metis_tac[])>>
  drule check_lrat_sound>>
  metis_tac[unsatisfiable_def]
QED

(* Try on an example
val fml = rconc (EVAL ``insert 1 [ 1;  2; -3] (
  insert 2 [-1; -2;  3] (
  insert 3 [ 2;  3; -4] (
  insert 4 [-2; -3;  4] (
  insert 5 [-1; -3; -4] (
  insert 6 [ 1;  3;  4] (
  insert 7 [-1;  2;  4] (
  insert 8 [ (1:int); -2; -4] LN))))))) :ccnf``)

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
 *)

val _ = export_theory ();
