(*
  This refines the LPR checker to a fixed-size, list-based implementation

  These fixed-size arrays are used in two places:
  1) Storing the formula
  2) (TODO) handling assignments
*)
open preamble basis lratTheory;

val _ = new_theory "lrat_list"

val list_lookup_def = Define`
  list_lookup fml k =
  if LENGTH fml ≤ k then NONE
  else EL k fml`

val is_AT_list_def = Define`
  (is_AT_list fml [] (C:cclause) = SOME (INR C)) ∧
  (is_AT_list fml (i::is) C =
  case list_lookup fml i of
    NONE => NONE
  | SOME Ci =>
  case delete_literals Ci C of
    [] => SOME (INL ())
  | [l] => is_AT_list fml is ((-l)::C)
  | _ => NONE)`

(* TODO: perhaps lookup trees can be replaced by alists since they're fairly short? *)
val check_RAT_list_def = Define`
  check_RAT_list fml p C ik (i,Ci) =
  if check_overlap Ci [-p] then
    case sptree$lookup i ik of
      NONE => F
    | SOME is =>
    case is of
      [] => check_overlap Ci (overlap_assignment [p] C)
    | _ =>
      is_AT_list fml is (C ++ (delete_literals Ci [-p])) = SOME (INL ())
  else
    T`

val check_PR_list_def = Define`
  check_PR_list fml p C w ik (i,Ci) =
  if check_overlap Ci (flip w) then
    case sptree$lookup i ik of
      NONE =>
      check_overlap Ci w
    | SOME is =>
    case is of
      [] => check_overlap Ci (overlap_assignment w C)
    | _ =>
      is_AT_list fml is (C ++ (delete_literals Ci (flip (overlap_assignment w C)))) = SOME (INL ())
  else
    T`

(* Clean up the index list *)
val reindex_def = Define`
  (reindex fml [] = ([],[])) ∧
  (reindex fml (i::is) =
  case list_lookup fml i of
    NONE => reindex fml is
  | SOME v =>
    let (l,r) = reindex fml is in
      (i::l, v::r))`

val is_PR_list_def = Define`
  is_PR_list fml inds p (C:cclause) wopt i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT_list fml i0 C of
    NONE => (inds, F)
  | SOME (INL ()) => (inds, T)
  | SOME (INR D) =>
  if p ≠ 0 then
    let (inds,vs) = reindex fml inds in
    case wopt of
      NONE => (inds, EVERY (check_RAT_list fml p D ik) (ZIP (inds,vs)))
    | SOME w =>
      (inds,
        ¬(check_overlap w (flip w)) ∧
        EVERY (check_PR_list fml p D w ik) (ZIP (inds,vs)))
  else
     (inds, F)`

val list_delete_list_def = Define`
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))`

val safe_hd_def = Define`
  safe_hd ls = case ls of [] => (0:int) | (x::xs) => x`

val list_insert_def = Define`
  list_insert fml k =
  if LENGTH fml ≤ k then NONE
  else EL k fml`

(* This version doubles size on each iteration
val resize_update_def = tDefine "resize_update" `
  resize_update v n fml =
  if n < LENGTH fml
  then
    LUPDATE v n fml
  else
    resize_update v n (fml++REPLICATE (LENGTH fml+1) NONE)`
  (WF_REL_TAC `measure ( λx. FST (SND x) + 1- LENGTH (SND (SND x)))`>>
  rw[])
*)

(* This version directly sets the size to double the input + 1 *)
val resize_update_def = Define`
  resize_update v n fml =
  if n < LENGTH fml
  then
    LUPDATE v n fml
  else
    LUPDATE v n (fml ++ REPLICATE (n * 2 + 1 - LENGTH fml) NONE)`

val check_lrat_step_list_def = Define`
  check_lrat_step_list step fml inds =
  case step of
    Delete cl =>
      (list_delete_list cl fml, SOME inds)
  | PR n C w i0 ik =>
    let p = safe_hd C in
    let (inds,b) = is_PR_list fml inds p C w i0 ik in
    if b then
      (resize_update (SOME C) n fml, SOME (n::inds))
    else
      (fml,NONE)`

val is_unsat_list_def = Define`
  is_unsat_list fml inds =
  case reindex fml inds of
    (_,inds') => MEM [] inds'`

val check_lrat_list_def = Define`
  (check_lrat_list [] fml inds = (fml, SOME inds)) ∧
  (check_lrat_list (step::steps) fml inds =
    case check_lrat_step_list step fml inds of
      (fml', NONE) => (fml', NONE)
    | (fml', SOME inds') => check_lrat_list steps fml' inds')`

val check_lrat_unsat_list_def = Define`
  check_lrat_unsat_list lrat fml inds =
  case check_lrat_list lrat fml inds of
    (fml', NONE) => F
  | (fml', SOME inds') => is_unsat_list fml' inds'`

(* prove that check_lrat_step_list implements check_lrat_step *)
val fml_rel_def = Define`
  fml_rel fml fmlls ⇔
  ∀x.
  if x < LENGTH fmlls then
    lookup x fml = EL x fmlls
  else
    lookup x fml = NONE`

Theorem fml_rel_is_AT_list:
  ∀ls C.
  fml_rel fml fmlls ⇒
  is_AT_list fmlls ls (C:cclause) =
  is_AT fml ls (C:cclause)
Proof
  Induct>>fs[is_AT_list_def,is_AT_def]>>rw[]>>
  fs[fml_rel_def,list_lookup_def]>>
  pop_assum(qspec_then`h` mp_tac)>>IF_CASES_TAC>>fs[]
QED

Theorem fml_rel_check_RAT_list:
  fml_rel fml fmlls ⇒
  check_RAT_list fmlls p C ik (i,Ci)  =
  check_RAT fml p C ik (i,Ci)
Proof
  rw[check_RAT_list_def,check_RAT_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  metis_tac[fml_rel_is_AT_list]
QED

Theorem fml_rel_check_PR_list:
  fml_rel fml fmlls ⇒
  check_PR_list fmlls p C w ik (i,Ci)  =
  check_PR fml p C w ik (i,Ci)
Proof
  rw[check_PR_list_def,check_PR_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  metis_tac[fml_rel_is_AT_list]
QED

(* It must be the case that everything that is SOME is in inds *)
val ind_rel_def = Define`
  ind_rel fmlls inds ⇔
  ∀x. x < LENGTH fmlls ∧
  IS_SOME (EL x fmlls) ⇒
  MEM x inds`

Theorem reindex_characterize:
  ∀inds inds' vs.
  reindex fmlls inds = (inds',vs) ⇒
  inds' = FILTER (λx. IS_SOME (list_lookup fmlls x)) inds ∧
  vs = MAP (λx. THE (list_lookup fmlls x)) inds'
Proof
  Induct>>fs[reindex_def] >>
  ntac 3 strip_tac>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  pairarg_tac>>fs[]>>rw[]>>
  simp[]
QED

Theorem ind_rel_filter:
  ind_rel fmlls inds ⇒
  ind_rel fmlls (FILTER (λx. IS_SOME (list_lookup fmlls x)) inds)
Proof
  rw[ind_rel_def]>>
  simp[MEM_FILTER,list_lookup_def]
QED

Theorem ind_rel_reindex:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  reindex fmlls inds = (inds',vs) ⇒
  LENGTH inds' = LENGTH vs ∧
  (∀x. MEM x (toAList fml) ⇔ MEM x (ZIP (inds',vs))) ∧
  ind_rel fmlls inds'
Proof
  strip_tac>> drule reindex_characterize>> simp[]>>
  simp[FORALL_PROD,MEM_toAList]>>rw[]
  >-
    (simp[ZIP_MAP,MEM_MAP,MEM_FILTER]>>
    fs[fml_rel_def]>>first_x_assum(qspec_then`p_1` mp_tac)>>fs[]>>
    IF_CASES_TAC>>simp[list_lookup_def]>>
    rw[EQ_IMP_THM]>>fs[IS_SOME_EXISTS]>>
    fs[ind_rel_def])
  >>
  metis_tac[ind_rel_filter]
QED

Theorem fml_rel_is_PR_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ⇒
  ∃inds'.
  is_PR_list fmlls inds p C w i0 ik = (inds',is_PR fml p C w i0 ik) ∧
  ind_rel fmlls inds'
Proof
  rw[is_PR_list_def,is_PR_def]>>
  dep_rewrite.DEP_REWRITE_TAC [fml_rel_is_AT_list]>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  pairarg_tac>>fs[]>>
  imp_res_tac ind_rel_reindex>> simp[]>>
  TOP_CASE_TAC>>simp[]>>
  simp[EVERY_MEM,FORALL_PROD]>>
  metis_tac[fml_rel_check_RAT_list,fml_rel_check_PR_list]
QED

Theorem list_delete_list_FOLDL:
  ∀l fmlls.
  list_delete_list l fmlls =
  FOLDL (\fml i.
    if LENGTH fml ≤ i then fml else LUPDATE NONE i fml) fmlls l
Proof
  Induct>>rw[list_delete_list_def]
QED

Theorem ind_rel_list_delete_list:
  ∀l fmlls fmlls'.
  ind_rel fmlls inds ∧
  list_delete_list l fmlls = fmlls' ⇒
  ind_rel fmlls' inds
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>
  rw[]>>fs[]>>
  first_x_assum drule>>
  rw[ind_rel_def,EL_LUPDATE]>>
  pop_assum mp_tac>> IF_CASES_TAC>>fs[]
QED

Theorem LENGTH_list_delete_list[simp]:
  ∀l.
  LENGTH (list_delete_list l fmlls) = LENGTH fmlls
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]
QED

Theorem fml_rel_list_delete_list:
  ∀l fml fmlls fmlls'.
  fml_rel fml fmlls ∧
  list_delete_list l fmlls = fmlls' ⇒
  fml_rel (FOLDL (\a b. delete b a) fml l) fmlls'
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]>>
  first_x_assum drule>>
  rw[fml_rel_def]
  >- (
    first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    simp[lookup_delete])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE,lookup_delete]>>
    IF_CASES_TAC>>fs[])>>
  simp[lookup_delete]
QED

(* For the doubling version

Theorem ind_rel_resize_update:
  ∀x n fmlls inds.
  ind_rel fmlls inds ⇒
  ind_rel (resize_update x n fmlls) (n::inds)
Proof
  ho_match_mp_tac (theorem "resize_update_ind")>>
  rw[]>>
  simp[Once resize_update_def]>>
  IF_CASES_TAC>>
  fs[]
  >-
    (fs[ind_rel_def,EL_LUPDATE]>>rw[]>>every_case_tac>>fs[])
  >>
  first_x_assum match_mp_tac>>
  fs[ind_rel_def]>>rw[]>>
  fs[IS_SOME_EXISTS,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  rfs[EL_REPLICATE,LENGTH_REPLICATE]
QED

Theorem fml_rel_resize_update:
  ∀vv n fmlls v.
  fml_rel fml fmlls ∧ vv = SOME v ⇒
  fml_rel (insert n v fml) (resize_update vv n fmlls)
Proof
  ho_match_mp_tac (theorem "resize_update_ind")>>
  rw[]>>
  simp[Once resize_update_def]>>
  IF_CASES_TAC>>
  fs[]
  >- (
    fs[fml_rel_def]>>
    rw[lookup_insert,EL_LUPDATE]
    >-
      metis_tac[]>>
    first_x_assum(qspec_then`x` assume_tac)>>rfs[])
  >>
  first_x_assum match_mp_tac>>
  fs[fml_rel_def]>>
  rw[EL_APPEND_EQN]
  >-
    metis_tac[]
  >-
    (fs[EL_REPLICATE]>>
    first_x_assum(qspec_then`x` assume_tac)>>rfs[])
  >>
    first_x_assum(qspec_then`x` assume_tac)>>rfs[]
QED
*)

Theorem ind_rel_resize_update:
  ind_rel fmlls inds ⇒
  ind_rel (resize_update x n fmlls) (n::inds)
Proof
  rw[resize_update_def,ind_rel_def,EL_LUPDATE]>>every_case_tac>>fs[]>>
  fs[ind_rel_def]>>rw[]>>
  fs[IS_SOME_EXISTS,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  rfs[EL_REPLICATE,LENGTH_REPLICATE]
QED

Theorem fml_rel_resize_update:
  fml_rel fml fmlls ⇒
  fml_rel (insert n v fml) (resize_update (SOME v) n fmlls)
Proof
  rw[resize_update_def,fml_rel_def,EL_LUPDATE]>>
  IF_CASES_TAC>> rw[lookup_insert]
  >- metis_tac[]
  >- metis_tac[]
  >-
    (first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
    fs[EL_APPEND_EQN]>>
    rw[]>>fs[EL_REPLICATE,LENGTH_REPLICATE])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]
QED

Theorem fml_rel_check_lrat_step_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  check_lrat_step_list step fmlls inds = (fmlls', SOME inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lrat_step step fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  simp[check_lrat_step_def,check_lrat_step_list_def]>>
  strip_tac>>
  TOP_CASE_TAC>>fs[]
  >- (
    CONJ_TAC >- metis_tac[ind_rel_list_delete_list]>>
    metis_tac[fml_rel_list_delete_list])>>
  pairarg_tac>>fs[]>>
  qpat_x_assum `_= (_ , SOME _)` mp_tac>>
  IF_CASES_TAC>>fs[]>>strip_tac>>
  drule (GEN_ALL fml_rel_is_PR_list)>>
  disch_then drule>>
  qmatch_asmsub_abbrev_tac`_ _ _ aa bb cc dd ee`>>
  disch_then (qspecl_then [`cc`,`aa`,`ee`,`dd`,`bb`] assume_tac)>>
  rfs[]>>
  unabbrev_all_tac>>fs[safe_hd_def]>>
  metis_tac[ind_rel_resize_update, fml_rel_resize_update]
QED

Theorem fml_rel_is_unsat_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  is_unsat_list fmlls inds ⇒
  is_unsat fml
Proof
  simp[is_unsat_list_def,is_unsat_def,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
  TOP_CASE_TAC>>rw[]>>
  drule reindex_characterize>>
  rw[]>>
  fs[MEM_MAP,MEM_FILTER,list_lookup_def]>>
  IF_CASES_TAC>>fs[]>>
  fs[fml_rel_def]>>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
  fs[IS_SOME_EXISTS]>>
  metis_tac[]
QED

(* NOTE: converse direction is true as well (but not needed) *)

val _ = export_theory();
