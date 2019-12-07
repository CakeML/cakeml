(*
  This manually proves the correctness of an array implementation of the
  LRAT checker.

  This is done in two steps:
  1) The LRAT checker implementation is turned into a "list-based" approximation
  2) The array is verified to implement the list-based version
*)
open preamble basis lratTheory parsingTheory;

val _ = new_theory "lrat_arrayProg"

(* List-based implementation *)
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
  | [l] => is_AT_list fml is (sorted_insert (-l) C)
  | _ => NONE)`

val is_RAT_aux_list_def = Define`
  (is_RAT_aux_list fml (p:int) C ik [] = T) ∧
  (is_RAT_aux_list fml p C ik (iCi::iCs) =
  case iCi of (i,Ci) =>
    if sorted_mem Ci (-p)then
      case sptree$lookup i ik of
        NONE => F
      | SOME is =>
        case is of [] =>
          (* Step 5.2: can be made more efficient *)
          if find_tauto p C Ci then
            is_RAT_aux_list fml p C ik iCs
          else
            F
        | _ =>
          (* Step 5.3-5.5 *)
          if is_AT_list fml is (sorted_union C (sorted_delete (-p) Ci)) = SOME (INL ()) then
            is_RAT_aux_list fml p C ik iCs
          else
            F
    else
      is_RAT_aux_list fml p C ik iCs)`

(* Clean up the index list *)
val reindex_def = Define`
  (reindex fml [] = ([],[])) ∧
  (reindex fml (i::is) =
  case list_lookup fml i of
    NONE => reindex fml is
  | SOME v =>
    let (l,r) = reindex fml is in
      (i::l, v::r))`

val is_RAT_list_def = Define`
  is_RAT_list fml inds p (C:cclause) i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT_list fml i0 C of
    NONE => (inds, F)
  | SOME (INL ()) => (inds, T)
  | SOME (INR D) =>
  if p ≠ 0 then
    let (inds,vs) = reindex fml inds in
      (inds, is_RAT_aux_list fml p D ik (ZIP (inds,vs)))
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

val filter_sort_def = Define`
  filter_sort C = QSORT $<= (FILTER (λx. x ≠ 0:int) C)`

val list_insert_def = Define`
  list_insert fml k =
  if LENGTH fml ≤ k then NONE
  else EL k fml`

val check_lrat_step_list_def = Define`
  check_lrat_step_list step fml inds =
  case step of
    Delete cl =>
      (list_delete_list cl fml, SOME inds)
  | RAT n C i0 ik =>
    let p = safe_hd C in
    let C = filter_sort C in
    let (inds,b) = is_RAT_list fml inds p C i0 ik in
    if b ∧ n < LENGTH fml then
      (LUPDATE (SOME C) n fml, SOME (n::inds))
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

Theorem fml_rel_is_RAT_aux_list:
  ∀ls.
  fml_rel fml fmlls ⇒
  is_RAT_aux_list fmlls p C ik ls =
  is_RAT_aux fml p C ik ls
Proof
  Induct>>fs[is_RAT_aux_list_def,is_RAT_aux_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  metis_tac[fml_rel_is_AT_list]
QED

Theorem is_RAT_aux_EVERY:
  ∀ls.
  is_RAT_aux fml p C ik ls <=>
  EVERY (λiCi.
    case iCi of (i,Ci) =>
    ¬(sorted_mem Ci (-p)) ∨
    case lookup i ik of
      NONE => F
    | SOME is =>
      case is of [] =>
        find_tauto p C Ci
      | _ =>
        is_AT fml is (sorted_union C (sorted_delete (-p) Ci)) = SOME (INL ())
  ) ls
Proof
  Induct>>fs[is_RAT_aux_def]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
QED

Theorem is_RAT_aux_MEM:
  (∀x. MEM x ls ⇔ MEM x rs) ⇒
  (is_RAT_aux fml p C ik ls <=>
  is_RAT_aux fml p C ik rs)
Proof
  rw[is_RAT_aux_EVERY,EVERY_MEM]
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

Theorem fml_rel_is_RAT_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ⇒
  ∃inds'.
  is_RAT_list fmlls inds p C i0 ik = (inds',is_RAT fml p C i0 ik) ∧
  ind_rel fmlls inds'
Proof
  rw[is_RAT_list_def,is_RAT_def]>>
  dep_rewrite.DEP_REWRITE_TAC [fml_rel_is_AT_list]>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  IF_CASES_TAC>>fs[]>>
  pairarg_tac>>fs[]>>
  imp_res_tac ind_rel_reindex>> simp[]>>
  drule is_RAT_aux_MEM>>
  metis_tac[fml_rel_is_RAT_aux_list]
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
  fml_rel (list_delete l fml) fmlls'
Proof
  simp[list_delete_list_FOLDL,list_delete_def,FOLDL_FOLDR_REVERSE]>>
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

Theorem ind_rel_LUPDATE:
  ind_rel fmlls inds ⇒
  ind_rel (LUPDATE x n fmlls) (n::inds)
Proof
  rw[ind_rel_def,EL_LUPDATE]>>
  every_case_tac>>fs[]
QED

Theorem fml_rel_LUPDATE:
  fml_rel fml fmlls ∧
  n < LENGTH fmlls ⇒
  fml_rel (insert n v fml) (LUPDATE (SOME v) n fmlls)
Proof
  rw[fml_rel_def,lookup_insert,EL_LUPDATE]>>
  every_case_tac>>fs[]
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
  drule (GEN_ALL fml_rel_is_RAT_list)>>
  disch_then drule>>
  qmatch_asmsub_abbrev_tac`_ _ _ aa bb _ _`>>
  disch_then (qspecl_then [`aa`,`s`,`l0`,`bb`] assume_tac)>>
  rfs[]>>
  unabbrev_all_tac>>fs[filter_sort_def,safe_hd_def]>>
  rw[]>>
  metis_tac[ind_rel_LUPDATE, fml_rel_LUPDATE]
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

(* Now implemented with an array *)
val _ = translation_extends"basisProg";

(* Pure translation of LRAT checker *)
val _ = register_type``:lratstep``;
val _ = register_type``:'a spt``;

val _ = translate mk_BS_def;
val _ = translate mk_BN_def;
val _ = translate delete_def;
val _ = translate lookup_def;
val _ = translate lrnext_def;
val _ = translate foldi_def;
val _ = translate toAList_def;
val _ = translate insert_def;

val _ = translate sorted_mem_def;
val _ = translate delete_literals_def;
val _ = translate sorted_insert_def;

val is_AT_arr = process_topdecs`
  fun is_AT_arr fml ls c =
    case ls of
      [] => Some (Inr c)
    | (i::is) =>
    if Array.length fml <= i then None
    else
    case Array.sub fml i of
      None => None
    | Some ci =>
      case delete_literals ci c of
        [] => Some (Inl ())
      | [l] => is_AT_arr fml is (sorted_insert (~l) c)
      | _ => None` |> append_prog

Theorem is_AT_arr_spec:
  ∀ls lsv c cv fmlv fmlls fml.
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_AT_arr" (get_ml_prog_state()))
    [fmlv; lsv; cv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(OPTION_TYPE (SUM_TYPE UNIT_TYPE (LIST_TYPE INT))) (is_AT_list fmlls ls c) resv *
      ARRAY fmlv fmllsv)
Proof
  Induct>>rw[is_AT_list_def]>>
  xcf "is_AT_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- (xcon >>xsimpl)>>
    xcon>>
    simp[OPTION_TYPE_def,SUM_TYPE_def]>>
    xsimpl)
  >>
  xmatch>>
  xlet_auto>- xsimpl>>
  xlet_auto>- xsimpl>>
  simp[list_lookup_def]>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def,SUM_TYPE_def]) >>
  xlet_auto >- xsimpl>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (xcon >> xsimpl)>>
  xlet_auto >- xsimpl>>
  Cases_on`delete_literals x c`
  >-(
    fs[LIST_TYPE_def]>>
    xmatch>>
    xlet_auto>- (xcon>>xsimpl)>>
    xlet_auto>- (xcon>>xsimpl)>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def,SUM_TYPE_def]) >>
  reverse (Cases_on`t`)>> fs[LIST_TYPE_def]
  >- (
    xmatch>> xcon>>
    xsimpl>>
    simp[OPTION_TYPE_def,SUM_TYPE_def])
  >>
  xmatch>>
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  xapp>> xsimpl
QED

val _ = translate sorted_union_def;
val _ = translate sorted_delete_def;
val _ = translate find_tauto_def;

(* TODO: get rid of the lookup_1 *)
val is_RAT_aux_arr = process_topdecs`
  fun is_RAT_aux_arr fml p c ik ls =
  case ls of
    [] => True
  | ici::ics =>
  case ici of (i,ci) =>
    if sorted_mem ci (~p) then
      case lookup_1 i ik of
        None => False
      | Some is =>
        case is of [] =>
          if find_tauto p c ci then
            is_RAT_aux_arr fml p c ik ics
          else
            False
        | _ =>
          case is_AT_arr fml is (sorted_union c (sorted_delete (~p) ci)) of
            Some (Inl ()) => is_RAT_aux_arr fml p c ik ics
          | _ => False
    else
      is_RAT_aux_arr fml p c ik ics` |> append_prog

Theorem is_RAT_aux_arr_spec:
  ∀ls lsv c cv pp ppv ik ikv fmlv fmlls fml.
  (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT))) ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_RAT_aux_arr" (get_ml_prog_state()))
    [fmlv; ppv; cv; ikv ; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (is_RAT_aux_list fmlls pp c ik ls) resv) *
      ARRAY fmlv fmllsv)
Proof
  Induct>>rw[is_RAT_aux_list_def]>>
  xcf "is_RAT_aux_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon >> xsimpl) >>
  xmatch>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto>- xsimpl>>
  xlet_auto>- xsimpl>>
  reverse IF_CASES_TAC >>
  xif>>asm_exists_tac>>xsimpl
  >- (xapp>>xsimpl) >>
  xlet_auto >- xsimpl>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (xmatch>>xcon>>xsimpl)>>
  xmatch>>
  TOP_CASE_TAC>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- xsimpl>>
    Cases_on`find_tauto pp c r`>>
    xif>>asm_exists_tac>>xsimpl
    >- (xapp>>xsimpl) >>
    xcon>>xsimpl)
  >>
  xmatch>>
  rpt (xlet_auto >- (TRY(xcon) >> xsimpl))>>
  qmatch_goalsub_abbrev_tac`is_AT_list _ lss cc`>>
  xlet `POSTv resv.
    &(OPTION_TYPE (SUM_TYPE UNIT_TYPE (LIST_TYPE INT))) (is_AT_list fmlls lss cc) resv *
    ARRAY fmlv fmllsv`
  >- (
    xapp>>xsimpl>>
    fs[Abbr`lss`,LIST_TYPE_def])
  >>
  Cases_on`is_AT_list fmlls lss cc`>>fs[OPTION_TYPE_def]
  >- (xmatch>>
    xcon>>xsimpl)
  >>
  Cases_on`x`>>fs[SUM_TYPE_def]
  >- (
    fs[UNIT_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl)>>
  xmatch>>
  xcon>> xsimpl
QED

val reindex_arr = process_topdecs`
  fun reindex_arr fml ls =
  case ls of
    [] => ([],[])
  | (i::is) =>
  if Array.length fml <= i then reindex_arr fml is
  else
  case Array.sub fml i of
    None => reindex_arr fml is
  | Some v =>
  case reindex_arr fml is of
    (l,r) => (i::l,v::r)` |> append_prog

Theorem reindex_arr_spec:
  ∀ls lsv fmlv fmlls.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_arr" (get_ml_prog_state()))
    [fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(
      (PAIR_TYPE
        (LIST_TYPE NUM)
        (LIST_TYPE (LIST_TYPE INT)))
       (reindex fmlls ls) resv) *
      ARRAY fmlv fmllsv)
Proof
  Induct>>rw[reindex_def]>>
  xcf "reindex_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- (xcon>> xsimpl)>>
    xlet_auto >- (xcon>> xsimpl)>>
    xcon >> xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def])>>
  xmatch>>
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  simp[list_lookup_def]>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (xapp >> xsimpl)>>
  xlet_auto >- xsimpl>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (
    xmatch>> xapp>>
    xsimpl)
  >>
  xmatch>>
  xlet_auto >- xsimpl>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto >- (xcon >> xsimpl)>>
  xlet_auto >- (xcon >> xsimpl)>>
  xcon>>xsimpl>>
  simp[LIST_TYPE_def]
QED

val is_RAT_arr = process_topdecs`
    fun is_RAT_arr fml inds p c i0 ik =
    case is_AT_arr fml i0 c of
      None => (inds, False)
    | Some (Inl ()) => (inds, True)
    | Some (Inr d) =>
    if p <> 0 then
    case reindex_arr fml inds of
      (inds,vs) =>
       (inds, is_RAT_aux_arr fml p d ik (List.zip (inds,vs)))
    else
      (inds, False)` |> append_prog

Theorem is_RAT_arr_spec:
  (LIST_TYPE NUM) ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  (LIST_TYPE NUM) i0 i0v ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_RAT_arr" (get_ml_prog_state()))
    [fmlv; lsv ; ppv; cv; i0v; ikv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &((PAIR_TYPE (LIST_TYPE NUM) BOOL) (is_RAT_list fmlls ls pp c i0 ik) resv) *
      ARRAY fmlv fmllsv)
Proof
  rw[is_RAT_list_def]>>
  xcf "is_RAT_arr" (get_ml_prog_state ())>>
  xlet_auto >- xsimpl>>
  Cases_on`is_AT_list fmlls i0 c`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- (xcon>>xsimpl)>>
    xcon>> xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)>>
  Cases_on`x`>>fs[SUM_TYPE_def]
  >- (
    fs[UNIT_TYPE_def]>>
    xmatch>>
    xlet_auto>- (xcon >> xsimpl)>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)>>
  xmatch>>
  xlet_auto >- xsimpl>>
  reverse IF_CASES_TAC >>
  xif>>asm_exists_tac>>xsimpl>>fs[]
  >- (
    xlet_auto>>xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)
  >>
  xlet_auto>- xsimpl>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto >- (xcon >> xsimpl)>>
  xlet `POSTv resv.
    &(LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) (ZIP (inds,vs)) resv) *
    ARRAY fmlv fmllsv`
  >-
    (xapp_spec (ListProgTheory.zip_v_thm |> INST_TYPE [alpha |-> ``:num``, beta |-> ``:int list``])>>
    xsimpl>>
    qexists_tac`(inds,vs)`>>simp[PAIR_TYPE_def]>>
    asm_exists_tac>> simp[]>>
    asm_exists_tac>> simp[])
  >>
  xlet_auto >- xsimpl>>
  xcon >> xsimpl
QED

val list_delete_arr = process_topdecs`
  fun list_delete_arr ls fml =
    case ls of
      [] => ()
    | (i::is) =>
      if Array.length fml <= i then list_delete_arr is fml
      else
        (Array.update fml i None; list_delete_arr is fml)` |> append_prog

Theorem list_delete_arr_spec:
  ∀ls lsv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_delete_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (list_delete_list ls fmlls) fmllsv') )
Proof
  Induct>>
  rw[]>>simp[list_delete_list_def]>>
  xcf "list_delete_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl) >>
  xmatch>>
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (xapp >> xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto >- xsimpl>>
  xapp>>xsimpl>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]
QED

val _ = translate safe_hd_def;
val _ = translate filter_sort_def;

val check_lrat_step_arr = process_topdecs`
  fun check_lrat_step_arr step fml ls =
  case step of
    Delete cl =>
      (list_delete_arr cl fml; Some ls)
  | Rat n c i0 ik =>
    let val p = safe_hd c
        val c = filter_sort c in
      case is_RAT_arr fml ls p c i0 ik of
        (ls,True) =>
          if n < Array.length fml then
            (Array.update fml n (Some c);
            Some (n::ls))
          else
            None
      | _ => None
    end` |> append_prog

val LRAT_LRATSTEP_TYPE_def = fetch "-" "LRAT_LRATSTEP_TYPE_def";

Theorem check_lrat_step_arr_spec:
  LRAT_LRATSTEP_TYPE step stepv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lrat_step_arr" (get_ml_prog_state()))
    [stepv; fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(OPTION_TYPE (LIST_TYPE NUM) (SND (check_lrat_step_list step fmlls ls)) resv) *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST (check_lrat_step_list step fmlls ls)) fmllsv') )
Proof
  rw[check_lrat_step_list_def]>>
  xcf "check_lrat_step_arr" (get_ml_prog_state ())>>
  TOP_CASE_TAC>>fs[LRAT_LRATSTEP_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- xsimpl>>
    xcon >> xsimpl>>
    simp[OPTION_TYPE_def])>>
  xmatch >>
  rpt(xlet_auto >- xsimpl)>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  reverse (Cases_on`b`)>>fs[BOOL_def]
  >- (
    xmatch>>
    xcon >> xsimpl>>
    simp[OPTION_TYPE_def])>>
  xmatch >>
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  reverse IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >-
    (xcon>>xsimpl>>simp[OPTION_TYPE_def])>>
  xlet_auto >- (xcon >> xsimpl)>>
  xlet_auto >- xsimpl>>
  xlet_auto >- (xcon >> xsimpl)>>
  xcon >> xsimpl>>
  simp[OPTION_TYPE_def,LIST_TYPE_def]>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]
QED

val is_unsat_arr = process_topdecs`
    fun is_unsat_arr fml ls =
    case reindex_arr fml ls of
      (ls,vs) =>
       List.member [] vs` |> append_prog

Theorem is_unsat_arr_spec:
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_unsat_arr" (get_ml_prog_state()))
    [fmlv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (is_unsat_list fmlls ls) resv) *
      ARRAY fmlv fmllsv)
Proof
  rw[is_unsat_list_def]>>
  xcf "is_unsat_arr" (get_ml_prog_state ())>>
  xlet_auto >- xsimpl >>
  TOP_CASE_TAC>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto >- (xcon >> xsimpl)>>
  xapp_spec (ListProgTheory.member_v_thm |> INST_TYPE [alpha |-> ``:int list``])>>
  xsimpl>>
  qexists_tac`r`>> qexists_tac`[]`>>
  HINT_EXISTS_TAC >>
  simp[MEMBER_INTRO]>>
  simp[EqualityType_LIST_TYPE,EqualityType_NUM_BOOL]>>
  EVAL_TAC
QED

val _ = translate blanks_def;
val _ = translate parse_until_zero_def;
val _ = translate parse_until_nn_def;

val parse_until_nn_side_def = theorem "parse_until_nn_side_def"

val parse_until_nn_side = Q.prove(`
  !x y. parse_until_nn_side x y ⇔ T`,
  Induct>>
  simp[parse_until_nn_def,Once parse_until_nn_side_def]>>
  rw[]>>fs[]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_RAT_hint_def;
val _ = translate lit_from_int_def;

val lit_from_int_side_def = fetch "-" "lit_from_int_side_def"

val lit_from_int_side = Q.prove(`
  !x. lit_from_int_side x ⇔ T`,
  rw[lit_from_int_side_def]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_lratstep_def;

(* Hooking up to the parser and stuff *)
val parse_and_run_list_def = Define`
  parse_and_run_list fml inds l =
  case parse_lratstep (tokens blanks l) of
    NONE => (fml,NONE)
  | SOME lrat =>
    check_lrat_step_list lrat fml inds`

val parse_and_run_arr = process_topdecs`
  fun parse_and_run_arr fml ls l =
  case parse_lratstep (String.tokens blanks l) of
    None => None
  | Some lrat =>
    check_lrat_step_arr lrat fml ls` |> append_prog

Theorem parse_and_run_arr_spec:
  STRING_TYPE l lv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_and_run_arr" (get_ml_prog_state()))
    [fmlv; lsv; lv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(OPTION_TYPE (LIST_TYPE NUM) (SND (parse_and_run_list fmlls ls l)) resv) *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST (parse_and_run_list fmlls ls l)) fmllsv') )
Proof
  rw[parse_and_run_list_def]>>
  xcf "parse_and_run_arr" (get_ml_prog_state ())>>
  xlet`POSTv v. &((LIST_TYPE STRING_TYPE) (tokens blanks l) v) * ARRAY fmlv fmllsv`
  >-
    (xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    metis_tac[fetch "-" "blanks_v_thm"])
  >>
  xlet_auto >- xsimpl>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch>>xsimpl
  >-
    (xcon>>xsimpl)
  >>
  xapp>>xsimpl
QED

val notfound_string_def = Define`
  notfound_string f = concat[strlit"cake_lrat: ";f;strlit": No such file or directory\n"]`;

val r = translate notfound_string_def;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"cake_lrat: ";f;strlit": Unable to parse in format:"; s;strlit"\n"]`;

val r = translate noparse_string_def;

val nocheck_string_def = Define`
  nocheck_string = strlit "cake_lrat: Checking failed."`;

val r = translate nocheck_string_def;

val check_unsat'' = process_topdecs `
  fun check_unsat'' fd fml ls =
    case TextIO.inputLine fd of
      None => (Some ls)
    | Some l =>
    case parse_and_run_arr fml ls l of
      None => (TextIO.output TextIO.stdErr nocheck_string;None)
    | Some ls' => check_unsat'' fd fml ls'` |> append_prog;

(* This says what happens to the STDIO *)
val check_unsat''_def = Define`
  (check_unsat'' fd fml inds fs [] = STDIO (fastForwardFD fs fd)) ∧
  (check_unsat'' fd fml inds fs (ln::ls) =
   case parse_and_run_list fml inds ln of
    (fml',NONE) =>
      STDIO (add_stderr (lineForwardFD fs fd) nocheck_string)
   | (fml',SOME inds') =>
      check_unsat'' fd fml' inds' (lineForwardFD fs fd) ls)`

(* This says what happens to fml and ls *)
val parse_and_run_file_list_def = Define`
  (parse_and_run_file_list [] fml inds = (fml, SOME inds)) ∧
  (parse_and_run_file_list (x::xs) fml inds =
    case parse_and_run_list fml inds x of
      (fml, NONE) => (fml, NONE)
    | (fml', SOME inds') => parse_and_run_file_list xs fml' inds')`

Theorem parse_and_run_file_list_eq:
  ∀ls fml inds.
  ∃fml'.
  parse_and_run_file_list ls fml inds =
  case parse_lrat ls of
    NONE => (fml', NONE)
  | SOME lrat =>
    check_lrat_list lrat fml inds
Proof
  Induct>>fs[parse_and_run_list_def,parse_lrat_def,parse_and_run_file_list_def,check_lrat_list_def]>>
  rw[]>>
  every_case_tac>>fs[]>>
  simp[check_lrat_list_def]
QED

Theorem linesFD_cons:
  lineFD fs fd = SOME x ⇒
  linesFD fs fd = x::linesFD (lineForwardFD fs fd) fd
Proof
  Cases_on`linesFD fs fd`>>
  fs[linesFD_nil_lineFD_NONE]>>
  drule linesFD_cons_imp>>
  fs[]
QED

Theorem check_unsat''_spec:
  !fs fd fdv fmlls fmllsv ls lsv.
  INSTREAM fd fdv ∧
  IS_SOME (get_file_content fs fd) ∧ get_mode fs fd = SOME ReadMode ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; fmlv; lsv]
    (STDIO fs * ARRAY fmlv fmllsv)
    (POSTv resv.
      &(OPTION_TYPE (LIST_TYPE NUM)
        (SND (parse_and_run_file_list (MAP implode (linesFD fs fd)) fmlls ls)) resv) *
      (check_unsat'' fd fmlls ls fs (MAP implode (linesFD fs fd))) *
      SEP_EXISTS fmllsv'.
        ARRAY fmlv fmllsv' *
        &(LIST_REL (OPTION_TYPE (LIST_TYPE INT))
          (FST (parse_and_run_file_list (MAP implode (linesFD fs fd)) fmlls ls)) fmllsv'))
Proof
  ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fs fd)` >>
  rw [] >>
  xcf "check_unsat''" (get_ml_prog_state ()) >>
  `validFD fd fs` by metis_tac[get_file_content_validFD,IS_SOME_EXISTS,PAIR] \\
  xlet_auto >- xsimpl \\
  Cases_on `lineFD fs fd` >>
  fs [OPTION_TYPE_def] >>
  xmatch
  >- (
    xcon>>xsimpl>>
    drule lineFD_NONE_lineForwardFD_fastForwardFD>> strip_tac>>
    fs[GSYM linesFD_nil_lineFD_NONE,OPTION_TYPE_def,check_unsat''_def,parse_and_run_file_list_def]>>
    xsimpl)>>
  xlet_auto >- xsimpl>>
  drule linesFD_cons>>strip_tac>>
  fs[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xlet `POSTv u. ARRAY fmlv fmllsv' * STDIO (add_stderr (lineForwardFD fs fd) nocheck_string)`
    >-
      (xapp_spec output_stderr_spec>>xsimpl>>
      qexists_tac`ARRAY fmlv fmllsv' `>>qexists_tac`nocheck_string`>>
      qexists_tac`lineForwardFD fs fd`>>
      xsimpl>>
      fs[fetch "-" "nocheck_string_v_thm"]) >>
    xcon>> xsimpl)>>
  xapp>>
  `IS_SOME (get_file_content (lineForwardFD fs fd) fd)` by
    fs[IS_SOME_get_file_content_lineForwardFD]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  xsimpl
QED

(* WE don't really care about the STDIO afterwards long as it gets closed *)
Theorem check_unsat''_eq:
∀ls fd fml inds fs.
∃n.
  check_unsat'' fd fml inds fs ls =
  case parse_and_run_file_list ls fml inds of
   (_ , NONE) => STDIO (add_stderr (forwardFD fs fd n) nocheck_string)
 | ( _ , SOME fml') => STDIO (fastForwardFD fs fd)
Proof
  Induct>>rw[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
  >-
    metis_tac[lineForwardFD_forwardFD]>>
  first_x_assum(qspecl_then[`fd`,`q`,`x`,`lineForwardFD fs fd`] strip_assume_tac)>>
  simp[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  qspecl_then [`fs`,`fd`] strip_assume_tac lineForwardFD_forwardFD>>
  simp[forwardFD_o]>>
  metis_tac[]
QED

val check_unsat' = process_topdecs `
  fun check_unsat' fml ls fname =
  let
    val fd = TextIO.openIn fname
    val chk = check_unsat'' fd fml ls
    val cls = TextIO.closeIn fd;
  in
    case chk of
      None => ()
    | Some ls' =>
      if is_unsat_arr fml ls' then
        TextIO.print "UNSATISFIABLE\n"
      else
        TextIO.output TextIO.stdErr nocheck_string
  end
  handle TextIO.BadFileName =>
  TextIO.output TextIO.stdErr (notfound_string fname)` |> append_prog;

(* TODO: COPIED from readerProg, should be moved *)
Theorem fastForwardFD_ADELKEY_same[simp]:
   forwardFD fs fd n with infds updated_by ADELKEY fd =
   fs with infds updated_by ADELKEY fd
Proof
  fs [forwardFD_def, IO_fs_component_equality]
QED

(* TODO: COPIED from readerProg, should be moved *)
Theorem validFileFD_forwardFD:
   validFileFD fd (forwardFD fs x y).infds <=> validFileFD fd fs.infds
Proof
  rw [forwardFD_def, validFileFD_def, AFUPDKEY_ALOOKUP]
  \\ PURE_TOP_CASE_TAC \\ fs []
  \\ rename1 `_ = SOME xx` \\ PairCases_on `xx` \\ rw []
QED

Theorem check_unsat'_spec:
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  FILENAME f fv ∧
  hasFreeFD fs
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [fmlv; lsv; fv]
  (STDIO fs * ARRAY fmlv fmllsv)
  (POSTv uv.
  &UNIT_TYPE () uv *
  STDIO (
    if inFS_fname fs f then
      (case parse_lrat (all_lines fs f) of
       SOME lrat =>
         if check_lrat_unsat_list lrat fmlls ls then
           add_stdout fs (strlit "UNSATISFIABLE\n")
         else
           add_stderr fs nocheck_string
      | NONE => add_stderr fs nocheck_string)
    else
     add_stderr fs (notfound_string f)) *
  SEP_EXISTS fmllsv'. ARRAY fmlv fmllsv')
Proof
  xcf"check_unsat'"(get_ml_prog_state())
  \\ reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull)
  \\ reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse IF_CASES_TAC
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs *
      SEP_EXISTS fmllsv'. ARRAY fmlv fmllsv'`
    >-
      (xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xapp_spec output_stderr_spec  >> xsimpl>>
      qexists_tac`ARRAY fmlv fmllsv'`>>
      qexists_tac`notfound_string f`>>
      qexists_tac`fs`>>xsimpl)
  >>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME openIn_STDIO_spec) \\ xsimpl >>
  (* bunch of useful stuff to know about f *)
  drule ALOOKUP_inFS_fname_openFileFS_nextFD>>
  disch_then drule>>
  fs[inFS_fname_def]>>
  disch_then(qspecl_then [`0`,`ReadMode`] mp_tac)>>fs[]>>
  impl_tac >-
    (match_mp_tac nextFD_leX>>
    fs[])>>
  strip_tac>>
  `inFS_fname fs f ∧ nextFD fs ≤ fs.maxFD` by
    (conj_tac >-
      fs[inFS_fname_def]>>
    match_mp_tac nextFD_leX>> fs[])>>
  imp_res_tac STD_streams_nextFD>>
  xlet_auto >- (
    qexists_tac`emp`>>xsimpl>>
    rw[]>- (
      match_mp_tac IS_SOME_get_file_content_openFileFS_nextFD>>
      fs[inFS_fname_def]>>
      match_mp_tac nextFD_leX>>
      fs[]) >>
    simp[get_mode_def])>>
  `openFileFS f fs ReadMode 0 with infds updated_by ADELKEY (nextFD fs) = fs` by
    metis_tac[openFileFS_ADELKEY_nextFD]>>
  qmatch_goalsub_abbrev_tac`check_unsat'' a _ _ b c`>>
  qspecl_then [`c`,`a`,`fmlls`,`ls`,`b`] strip_assume_tac check_unsat''_eq>>
  simp[]>>
  unabbrev_all_tac>>
  qmatch_asmsub_abbrev_tac`parse_and_run_file_list lss fmlls ls`>>
  `lss = all_lines fs f` by
    (simp[Abbr`lss`]>>
    drule linesFD_openFileFS_nextFD>>
    rpt (disch_then drule)>>
    disch_then (qspec_then`ReadMode` assume_tac)>>
    simp[MAP_MAP_o,o_DEF])>>
  qspecl_then [`lss`,`fmlls`,`ls`] strip_assume_tac parse_and_run_file_list_eq>>
  fs[]>>rw[]>>
  Cases_on`parse_lrat (all_lines fs f)`>>
  fs[]
  >- (
    xlet_auto_spec (SOME closeIn_STDIO_spec)>>xsimpl
    >-
      (rw[]>>simp[validFileFD_forwardFD]>>
      simp[validFileFD_def])>>
    xmatch>>fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xcon>> xsimpl>>
    qmatch_goalsub_abbrev_tac`add_stderr fs' _ with infds updated_by _`>>
    `2 ≠ nextFD fs` by fs []>>
    drule (GEN_ALL add_stdo_ADELKEY)>>
    disch_then
      (qspecl_then [`nocheck_string`,`"stderr"`,`fs'`] sym_sub_tac)>>
    simp[Abbr`fs'`] >>
    xsimpl)>>
  simp[check_lrat_unsat_list_def] >>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]
  >- (
    xlet_auto_spec (SOME closeIn_STDIO_spec)>>xsimpl
    >-
      (rw[]>>simp[validFileFD_forwardFD]>>
      simp[validFileFD_def])>>
    xmatch>>fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xcon>> xsimpl>>
    qmatch_goalsub_abbrev_tac`add_stderr fs' _ with infds updated_by _`>>
    `2 ≠ nextFD fs` by fs []>>
    drule (GEN_ALL add_stdo_ADELKEY)>>
    disch_then
      (qspecl_then [`nocheck_string`,`"stderr"`,`fs'`] sym_sub_tac)>>
    simp[Abbr`fs'`] >>
    xsimpl) >>
  (* TODO: why does xlet_auto find a weird instance here?? *)
  xlet`
    (POSTv u.
     ARRAY fmlv fmllsv' *
     STDIO
       ((fastForwardFD (openFileFS f fs ReadMode 0) (nextFD fs))
         with infds updated_by ADELKEY (nextFD fs)) *
     &(UNIT_TYPE () u))`
    >-
      (xapp_spec closeIn_STDIO_spec>>xsimpl>>
      qmatch_goalsub_abbrev_tac`STDIO fs'`>>
      qexists_tac`ARRAY fmlv fmllsv'`>>qexists_tac`fs'`>>
      qexists_tac`nextFD fs`>>simp[Abbr`fs'`]>>xsimpl>>
      simp[validFileFD_def])
  >>
  xmatch>>fs[OPTION_TYPE_def]>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  xlet_auto
  >-
    (xsimpl>>simp[EqualityType_NUM_BOOL])
  >>
  xif>>fs[check_lrat_unsat_def]
  >- (
    xapp_spec print_spec >> xsimpl>>
    qexists_tac`ARRAY fmlv fmllsv'`>>qexists_tac`fs`>>xsimpl)
  >>
    xapp_spec output_stderr_spec \\ xsimpl >>
    qexists_tac`ARRAY fmlv fmllsv'`>> qexists_tac`nocheck_string`>>
    qexists_tac`fs`>>
    xsimpl>>fs[fetch "-" "nocheck_string_v_thm"]
QED

Theorem abs_compute:
  ABS (i:int) = if i < 0 then -i else i
Proof
  intLib.ARITH_TAC
QED

val _ = translate abs_compute;

val _ = translate max_lit_def;
val _ = translate print_line_def;

val _ = translate spt_center_def;
val _ = translate spt_centers_def;
val _ = translate spt_right_def;
val _ = translate spt_left_def;
val _ = translate aux_alist_def;
val _ = translate toSortedAList_def;

val _ = translate print_dimacs_def;

(* Pure translation of parsing things *)
val _ = translate parse_header_line_def;
val _ = translate parse_clause_def;

(* NOTE: inefficient-ish version that reads all lines at once *)
val _ = translate parsingTheory.build_fml_def;
val _ = translate parse_dimacs_def;

val usage_string_def = Define`
  usage_string = strlit"Usage: cake_lrat <DIMCAS formula file> <Optional: LRAT proof file> <Size of LRAT array (if proof file given)>\n"`;

val r = translate usage_string_def;

val fill_arr = process_topdecs`
  fun fill_arr arr ls =
    case ls of [] => True
    | (x::xs) =>
    case x of (i,v) =>
      if Array.length arr <= i then False
      else
        (Array.update arr i (Some v) ; fill_arr arr xs)` |> append_prog;

Theorem fill_arr_spec:
  ∀ls lsv arrls arrlsv.
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv bv.
  &BOOL (EVERY (λ(i,v). i < LENGTH arrlsv) ls) bv *
  SEP_EXISTS arrlsv'. ARRAY arrv arrlsv' *
    &(
      if EVERY (λ(i,v). i < LENGTH arrlsv) ls then
        LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FOLDL (λacc (i,v).  LUPDATE (SOME v) i acc) arrls ls) arrlsv'
      else
        T))
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xcon >> xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto >- xsimpl>>
  xlet_auto >- xsimpl>>
  xif
  >- (xcon>>xsimpl)>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto >-
    xsimpl>>
  xapp>>
  xsimpl>>
  qexists_tac`LUPDATE (SOME r)  q arrls`>>
  xsimpl>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[OPTION_TYPE_def]
QED

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
    case CommandLine.arguments () of
        (f1::f2::f3::[]) =>
          (case TextIO.inputLinesFrom f1 of
            None => TextIO.output TextIO.stdErr (notfound_string f1)
          | Some lines1 =>
            (case parse_dimacs lines1 of
              None => TextIO.output TextIO.stdErr (noparse_string f1 "DIMACS")
            | Some fml =>
                (case Int.fromNatString f3 of
                  None => TextIO.output TextIO.stdErr (noparse_string f3 "Number")
                | Some n =>
                  let val ls = tosortedalist fml
                      val arr = Array.array n None
                  in
                    if fill_arr arr ls
                    then check_unsat' arr (List.map fst ls) f2
                    else TextIO.output TextIO.stdErr nocheck_string
                  end
            )))
      |  (f1::[]) =>
          (case TextIO.inputLinesFrom f1 of
            None => TextIO.output TextIO.stdErr (notfound_string f1)
          | Some lines1 =>
            (case parse_dimacs lines1 of
              None => TextIO.output TextIO.stdErr (noparse_string f1 "DIMACS")
            | Some fml => TextIO.print_list (print_dimacs fml)))
      | _ => TextIO.output TextIO.stdErr usage_string`;

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs =
  if (LENGTH cl = 4) then
    if inFS_fname fs (EL 1 cl) then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
        SOME fml =>
          (case fromNatString (EL 3 cl) of
            SOME sz =>
              let fmlls = toSortedAList fml in
              if EVERY (λi. i < sz) (MAP FST fmlls) then
                if inFS_fname fs (EL 2 cl) then
                  case parse_lrat (all_lines fs (EL 2 cl)) of
                    SOME lrat =>
                    let base = REPLICATE sz NONE in
                    let upd = FOLDL (λacc (i,v).  LUPDATE (SOME v) i acc) base fmlls in
                    if check_lrat_unsat_list lrat upd (MAP FST fmlls) then
                      add_stdout fs (strlit "UNSATISFIABLE\n")
                    else
                      add_stderr fs nocheck_string
                  | NONE => add_stderr fs nocheck_string
                else
                  add_stderr fs (notfound_string (EL 2 cl))
              else
                add_stderr fs nocheck_string
          | NONE => add_stderr fs (noparse_string (EL 3 cl) (strlit "Number"))
          )
       | NONE => add_stderr fs (noparse_string (EL 1 cl) (strlit "DIMACS"))
     else
       add_stderr fs (notfound_string (EL 1 cl))
  else if (LENGTH cl = 2) then
    if inFS_fname fs (EL 1 cl) then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
        SOME fml =>
          add_stdout fs (concat (print_dimacs fml ))
      | NONE => add_stderr fs (noparse_string (EL 1 cl) (strlit "DIMACS"))
    else
       add_stderr fs (notfound_string (EL 1 cl))
  else
    add_stderr fs usage_string`;

val st = get_ml_prog_state();

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * STDIO (check_unsat_sem cl fs))
Proof
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >-
    (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  xlet_auto >- (xcon >> xsimpl)>>
  xlet_auto >- (qexists_tac`STDIO fs` >> xsimpl)>>
  Cases_on `cl` >- fs[wfcl_def] >>
  Cases_on `t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_unsat_sem_def]>>
    xmatch \\ xapp_spec output_stderr_spec \\ xsimpl
    \\ CONV_TAC SWAP_EXISTS_CONV
    \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
    \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl) >>
  Cases_on `t'` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    (* Only 1 argument on command line: prints the parsed formula *)
    xmatch>>
    xlet_auto_spec(SOME inputLinesFrom_spec) >-
      (xsimpl>>fs[wfcl_def,validArg_def])>>
    simp[check_unsat_sem_def]>>
    reverse IF_CASES_TAC >>
    xmatch >> fs[]
    >- (
      fs[OPTION_TYPE_def]>>
      reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
      xlet_auto >- xsimpl>>
      xapp_spec output_stderr_spec \\ xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`COMMANDLINE [h;h']`>> qexists_tac`fs`>>
      xsimpl)>>
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xlet_auto >- xsimpl>>
    xmatch \\ Cases_on `parse_dimacs (all_lines fs h')`
    >- (
      fs[OPTION_TYPE_def]>>
      reverse conj_tac >-
        (strip_tac >> EVAL_TAC)>>
      xlet_auto >- xsimpl>>
      xapp_spec output_stderr_spec  >> xsimpl>>
      asm_exists_tac>>xsimpl>>
      qexists_tac`COMMANDLINE [h;h']`>> qexists_tac`fs`>>
      xsimpl)
    >>
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xlet_auto>- xsimpl>>
    xapp_spec print_list_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h;h']`>> qexists_tac`fs`>>
    xsimpl)>>
  Cases_on`t` \\ fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_unsat_sem_def]>>
    xmatch \\ xapp_spec output_stderr_spec \\ xsimpl
     \\ CONV_TAC SWAP_EXISTS_CONV
     \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
     \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl) >>
  reverse (Cases_on`t'`)>> fs[ml_translatorTheory.LIST_TYPE_def]
  >- (
    simp[check_unsat_sem_def]>>
    xmatch \\ xapp_spec output_stderr_spec \\ xsimpl
     \\ CONV_TAC SWAP_EXISTS_CONV
     \\ qexists_tac `usage_string` \\ simp [theorem "usage_string_v_thm"]
     \\ CONV_TAC SWAP_EXISTS_CONV \\ qexists_tac `fs` \\ xsimpl) >>
  (* 3 arguments on command line *)
  qmatch_goalsub_rename_tac `COMMANDLINE [_ ; cnf_f ; lrat_f ; n_s]`>>
  xmatch>>
  xlet_auto_spec(SOME inputLinesFrom_spec) >-
    (xsimpl>>fs[wfcl_def,validArg_def])>>
  simp[check_unsat_sem_def]>>
  reverse IF_CASES_TAC >>
  xmatch >> fs[]
  >- (
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
    xlet_auto >- xsimpl>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h; cnf_f ; lrat_f ; n_s]`>> qexists_tac`fs`>>
    xsimpl)>>
  fs[OPTION_TYPE_def]>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  xlet_auto >- xsimpl>>
  xmatch \\ Cases_on `parse_dimacs (all_lines fs cnf_f)`
  >- (
    fs[OPTION_TYPE_def]>>
    reverse conj_tac >-
      (strip_tac >> EVAL_TAC)>>
    xlet_auto >- xsimpl>>
    xapp_spec output_stderr_spec  >> xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h;cnf_f; lrat_f;n_s]`>> qexists_tac`fs`>>
    xsimpl)>>
  fs[OPTION_TYPE_def]>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  reverse conj_tac >- (strip_tac >> EVAL_TAC)>>
  xlet_auto >- xsimpl >>
  Cases_on`fromNatString n_s`>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xlet_auto >- xsimpl>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE [h; cnf_f ; lrat_f ; n_s]`>> qexists_tac`fs`>>
    xsimpl)>>
  xlet_auto >- (xsimpl>> simp[EqualityType_NUM_BOOL,EqualityType_LIST_TYPE])>>
  xlet_auto >- (xcon>>xsimpl)>>
  xlet_auto >- xsimpl>>
  xlet`
    (POSTv bv.
    &BOOL (EVERY (λ(i,v). i < x') (toSortedAList x)) bv *
    STDIO fs *  COMMANDLINE [h; cnf_f; lrat_f; n_s] *
    SEP_EXISTS arrlsv'. ARRAY av arrlsv' *
      &(
        if EVERY (λ(i,v). i < x') (toSortedAList x) then
          LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FOLDL (λacc (i,v).  LUPDATE (SOME v) i acc) (REPLICATE x' NONE)(toSortedAList x)) arrlsv'
        else
          T))`
  >-
    (xapp>>xsimpl>>
    HINT_EXISTS_TAC>>xsimpl>>
    qexists_tac`REPLICATE x' NONE`>>
    CONJ_TAC >-
      simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
    rw[]>>simp[])>>
  reverse xif
  >- (
    (* this is a really bad default rewrite *)
    `¬ (EVERY (λi. i < x') (MAP FST (toSortedAList x)))` by
      fs[EXISTS_MAP,LAMBDA_PROD,o_DEF]>>
    simp[]>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    qexists_tac`COMMANDLINE [h; cnf_f; lrat_f; n_s] * ARRAY av arrlsv'`>>
    qexists_tac`nocheck_string`>>
    qexists_tac`fs`>>xsimpl>>
    fs[fetch "-" "nocheck_string_v_thm"]) >>
  simp[EVERY_MAP,LAMBDA_PROD]>>
  xlet`
    POSTv lv.
    STDIO fs * COMMANDLINE [h; cnf_f; lrat_f; n_s] * ARRAY av arrlsv' *
    &(LIST_TYPE NUM (MAP FST (toSortedAList x)) lv)`
  >- (
    xapp_spec (ListProgTheory.map_1_v_thm |> INST_TYPE [alpha |-> ``:num``, beta |-> ``:num # int list``])>>
    xsimpl>>
    asm_exists_tac >>simp[]>>
    qexists_tac`FST`>>
    qexists_tac`NUM`>>simp[fst_v_thm])>>
  xapp_spec (GEN_ALL check_unsat'_spec)>>
  xsimpl>>
  simp[GSYM CONJ_ASSOC]>>
  fs[FILENAME_def,validArg_def,check_unsat_sem_def,wfcl_def] >>
  rpt(asm_exists_tac>>simp[])>>
  qexists_tac` COMMANDLINE [h; cnf_f; lrat_f; n_s] ` >> xsimpl
QED

val st = get_ml_prog_state();

Theorem check_unsat_whole_prog_spec:
   hasFreeFD fs ⇒
   whole_prog_spec ^(fetch_v"check_unsat"st) cl fs NONE ((=) (check_unsat_sem cl fs))
Proof
  rw[whole_prog_spec_def]
  \\ qexists_tac`check_unsat_sem cl fs`
  \\ reverse conj_tac
  >- (
    rw[check_unsat_sem_def]>>
    every_case_tac>>simp[GSYM add_stdo_with_numchars,with_same_numchars])
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
  \\ xsimpl
QED

val name = "check_unsat"
val (sem_thm,prog_tm) = whole_prog_thm st name (UNDISCH check_unsat_whole_prog_spec)
val check_unsat_prog_def = Define`check_unsat_prog = ^prog_tm`;

val check_unsat_semantics = save_thm("check_unsat_semantics",
  sem_thm |> REWRITE_RULE[GSYM check_unsat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO]);

val _ = export_theory();
