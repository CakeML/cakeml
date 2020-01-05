(*
  This refines lrat_list to use arrays
*)
open preamble basis lratTheory lrat_listTheory parsingTheory;

val _ = new_theory "lrat_arrayProg"

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

val _ = translate (delete_literals_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);

val index_array_def = Define`
  index_array (i:int) =
  if i < 0 then
    2 * Num(-i)
  else
    2 * Num(i) + 1`

val w8zero_def = Define`
  w8zero = (0w:word8)`

val w8one_def = Define`
  w8one = (1w:word8)`

val _ = translate index_array_def;

val index_array_side_def = fetch "-" "index_array_side_def"

val index_array_side = Q.prove(`
  !x. index_array_side x ⇔ T`,
  simp[index_array_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val _ = translate w8zero_def;
val _ = translate w8one_def;

val delete_literals_arr = process_topdecs`
  fun delete_literals_arr carr cs =
  case cs of [] => []
  | (c::cs) =>
    if Word8Array.sub carr (index_array c) = w8zero then
      (c::delete_literals_arr carr cs)
    else
      delete_literals_arr carr cs` |> append_prog

val is_AT_arr_aux = process_topdecs`
  fun is_AT_arr_aux fml ls c carr =
    case ls of
      [] => Inr c
    | (i::is) =>
    case Array.sub fml i of
      None => raise Fail
    | Some ci =>
      case delete_literals_arr carr ci of
        [] => Inl c
      | [l] =>
        (Word8Array.update carr (index_array (~l)) w8one;
        is_AT_arr_aux fml is ((~l)::c) carr)
      | _ => raise Fail` |> append_prog

val set_array = process_topdecs`
  fun set_array carr v cs =
  case cs of [] => ()
  | (c::cs) =>
    (Word8Array.update carr (index_array c) v;
    set_array carr v cs)` |> append_prog

val is_AT_arr = process_topdecs`
  fun is_AT_arr fml ls c carr =
    (set_array carr w8one c;
    case is_AT_arr_aux fml ls c carr of
      Inl c => (set_array carr w8zero c; Inl c)
    | Inr c => (set_array carr w8zero c; Inr c))` |> append_prog

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

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
    xlet_autop>>
    xcon>>
    simp[OPTION_TYPE_def,SUM_TYPE_def]>>
    xsimpl)
  >>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  simp[list_lookup_def]>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def,SUM_TYPE_def]) >>
  xlet_autop>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (xcon >> xsimpl)>>
  xlet_autop>>
  Cases_on`delete_literals x c`
  >-(
    fs[LIST_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def,SUM_TYPE_def]) >>
  reverse (Cases_on`t`)>> fs[LIST_TYPE_def]
  >- (
    xmatch>> xcon>>
    xsimpl>>
    simp[OPTION_TYPE_def,SUM_TYPE_def])
  >>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xapp>> xsimpl>>
  simp[LIST_TYPE_def]
QED

val _ = translate (check_overlap_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO] |> INST_TYPE [alpha |-> ``:int``]);
val _ = translate flip_def;
val _ = translate overlap_assignment_def;

val check_RAT_arr = process_topdecs`
  fun check_RAT_arr carr fml p c ik (i,ci) =
  if check_overlap ci [~p] then
    case lookup_1 i ik of
      None => False
    | Some is =>
    case is of
      [] => check_overlap ci (overlap_assignment [p] c)
    | _ =>
      case is_AT_arr fml is (c @ delete_literals ci [~p]) carr of
        Inl d => True
      | _ => False
  else True` |> append_prog

Theorem check_RAT_arr_spec:
  ∀ici iciv c cv pp ppv ik ikv fmlv fmlls fml.
  (PAIR_TYPE NUM (LIST_TYPE INT)) ici iciv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_RAT_arr" (get_ml_prog_state()))
    [fmlv; ppv; cv; ikv ; iciv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (check_RAT_list fmlls pp c ik ici) resv) *
      ARRAY fmlv fmllsv)
Proof
  Cases>>rw[check_RAT_list_def]>>
  xcf "check_RAT_arr" (get_ml_prog_state ())>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt(xlet_autop)>>
  xlet `POSTv resv. &BOOL (check_overlap r [-pp]) resv * ARRAY fmlv fmllsv`
  >- (
    xapp>>xsimpl>>
    metis_tac[LIST_TYPE_def])>>
  reverse xif >- (xcon>>xsimpl)>>
  xlet_autop >>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (xmatch>>xcon>>xsimpl)>>
  xmatch >>
  TOP_CASE_TAC >> fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt(xlet_autop)>>
    xlet `POSTv resv. &LIST_TYPE INT (overlap_assignment [pp] c) resv * ARRAY fmlv fmllsv`
    >- (
      xapp>>xsimpl>>
      metis_tac[LIST_TYPE_def])>>
    xapp>>xsimpl>>
    metis_tac[])>>
  xmatch >>
  rpt(xlet_autop)>>
  xlet `POSTv resv. &LIST_TYPE INT (delete_literals r [-pp]) resv * ARRAY fmlv fmllsv`
  >- (
    xapp>>xsimpl>>
    metis_tac[LIST_TYPE_def])>>
  rpt (xlet_autop)>>
  qmatch_goalsub_abbrev_tac`is_AT_list _ lss cc`>>
  xlet `POSTv resv.
    &(OPTION_TYPE (SUM_TYPE UNIT_TYPE (LIST_TYPE INT))) (is_AT_list fmlls lss cc) resv *
    ARRAY fmlv fmllsv`
  >- (
    xapp>>xsimpl>>
    fs[Abbr`lss`,LIST_TYPE_def])
  >>
  Cases_on`is_AT_list fmlls lss cc`>>fs[OPTION_TYPE_def]
  >- (xmatch>> xcon>>xsimpl)
  >>
  Cases_on`x`>>fs[SUM_TYPE_def]
  >- (
    fs[UNIT_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl)>>
  xmatch>>
  xcon>> xsimpl
QED

val check_PR_arr = process_topdecs`
  fun check_PR_arr carr fml p c w ik (i,ci) =
  if check_overlap ci (flip_1 w) then
    case lookup_1 i ik of
      None => check_overlap ci w
    | Some is =>
    case is of
      [] => check_overlap ci (overlap_assignment w c)
    | _ =>
      case is_AT_arr fml is (c @ delete_literals ci (flip_1 (overlap_assignment w c))) carr of
        Inl d => True
      | _ => False
  else True` |> append_prog

Theorem check_PR_arr_spec:
  ∀ici iciv c cv w wv pp ppv ik ikv fmlv fmlls fml.
  (PAIR_TYPE NUM (LIST_TYPE INT)) ici iciv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  (LIST_TYPE INT) w wv ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_PR_arr" (get_ml_prog_state()))
    [fmlv; ppv; cv; wv; ikv ; iciv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (check_PR_list fmlls pp c w ik ici) resv) *
      ARRAY fmlv fmllsv)
Proof
  Cases>>rw[check_PR_list_def]>>
  xcf "check_PR_arr" (get_ml_prog_state ())>>
  fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt(xlet_autop)>>
  reverse xif >- (xcon>>xsimpl)>>
  xlet_autop >>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (xmatch>> xapp>>xsimpl>> metis_tac[])>>
  xmatch >>
  TOP_CASE_TAC >> fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt(xlet_autop)>>
    xapp>> xsimpl>> metis_tac[])>>
  xmatch >>
  rpt(xlet_autop)>>
  qmatch_goalsub_abbrev_tac`is_AT_list _ lss cc`>>
  xlet `POSTv resv.
    &(OPTION_TYPE (SUM_TYPE UNIT_TYPE (LIST_TYPE INT))) (is_AT_list fmlls lss cc) resv *
    ARRAY fmlv fmllsv`
  >- (
    xapp>>xsimpl>>
    fs[Abbr`lss`,LIST_TYPE_def])
  >>
  Cases_on`is_AT_list fmlls lss cc`>>fs[OPTION_TYPE_def]
  >- (xmatch>> xcon>>xsimpl)
  >>
  Cases_on`x`>>fs[SUM_TYPE_def]
  >- (
    fs[UNIT_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl)>>
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
    xmatch>> rpt(xlet_autop)>>
    xcon >> xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def])>>
  xmatch>> rpt(xlet_autop)>>
  simp[list_lookup_def]>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  IF_CASES_TAC >> fs[]>>
  xif>> asm_exists_tac>> xsimpl
  >- (xapp >> xsimpl)>>
  xlet_autop >>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (xmatch>> xapp>> xsimpl)
  >>
  xmatch>>
  xlet_autop>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  rpt(xlet_autop)>>
  xcon>>xsimpl>>
  simp[LIST_TYPE_def]
QED

(* Lift the definitions of check_{RAT|PR}_arr so they are not higher order *)
val every_check_RAT_arr = process_topdecs`
  fun every_check_RAT_arr carr fml p d ik ls =
  case ls of [] => True
  | (x::xs) =>
  if check_RAT_arr carr fml p d ik x then every_check_RAT_arr carr fml p d ik xs else False` |> append_prog

Theorem every_check_RAT_arr_spec:
  ∀ls lsv c cv pp ppv ik ikv fmlv fmlls fml.
  (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT))) ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_check_RAT_arr" (get_ml_prog_state()))
    [fmlv; ppv; cv; ikv ; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (EVERY (check_RAT_list fmlls pp c ik) ls) resv) *
      ARRAY fmlv fmllsv)
Proof
  Induct>>
  xcf "every_check_RAT_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch >- (xcon>>xsimpl)>>
  xlet_autop >>
  xif >-
    (xapp>>xsimpl)>>
  xcon>>xsimpl
QED

val every_check_PR_arr = process_topdecs`
  fun every_check_PR_arr carr fml p d w ik ls =
  case ls of [] => True
  | (x::xs) =>
  if check_PR_arr carr fml p d w ik x then every_check_PR_arr carr fml p d w ik xs else False` |> append_prog

Theorem every_check_PR_arr_spec:
  ∀ls lsv c cv w wv pp ppv ik ikv fmlv fmlls fml.
  (LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT))) ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  (LIST_TYPE INT) w wv ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_check_PR_arr" (get_ml_prog_state()))
    [fmlv; ppv; cv; wv; ikv ; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(BOOL (EVERY (check_PR_list fmlls pp c w ik) ls) resv) *
      ARRAY fmlv fmllsv)
Proof
  Induct>>
  xcf "every_check_PR_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch >- (xcon>>xsimpl)>>
  xlet_autop >>
  xif >-
    (xapp>>xsimpl)>>
  xcon>>xsimpl
QED

(* the inner-most if-then-else is just to make this easier to verify *)
val is_PR_arr = process_topdecs`
  fun is_PR_arr carr fml inds p c wopt i0 ik =
  case is_AT_arr fml i0 c carr of
    (Inl d) => (inds, True)
  | (Inr d) =>
  if p <> 0 then
    case reindex_arr fml inds of (inds,vs) =>
    case wopt of
      None => (inds, every_check_RAT_arr carr fml p d ik (List.zip (inds,vs)))
    | Some w =>
      if check_overlap w (flip_1 w) then (inds,False)
      else
      (inds, every_check_PR_arr carr fml p d w ik (List.zip (inds,vs)))
  else
    (inds, False)` |> append_prog

Theorem is_PR_arr_spec:
  (LIST_TYPE NUM) ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  OPTION_TYPE (LIST_TYPE INT) wopt woptv ∧
  (LIST_TYPE NUM) i0 i0v ∧
  (SPTREE_SPT_TYPE (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_PR_arr" (get_ml_prog_state()))
    [fmlv; lsv ; ppv; cv; woptv; i0v; ikv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &((PAIR_TYPE (LIST_TYPE NUM) BOOL) (is_PR_list fmlls ls pp c wopt i0 ik) resv) *
      ARRAY fmlv fmllsv)
Proof
  rw[is_PR_list_def]>>
  xcf "is_PR_arr" (get_ml_prog_state ())>>
  xlet_autop >>
  TOP_CASE_TAC >>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- (xcon>>xsimpl)>>
    xcon>> xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    fs[UNIT_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)>>
  xmatch>>
  xlet_autop>>
  reverse IF_CASES_TAC >>
  xif>>asm_exists_tac>>xsimpl>>fs[]
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)
  >>
  xlet_autop >>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (
    xmatch>> rpt(xlet_autop)>>
    xlet `POSTv resv.
      &(LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) (ZIP (inds,vs)) resv) *
      ARRAY fmlv fmllsv`
    >-
      (xapp_spec (ListProgTheory.zip_v_thm |> INST_TYPE [alpha |-> ``:num``, beta |-> ``:int list``])>>
      xsimpl>>
      qexists_tac`(inds,vs)`>>simp[PAIR_TYPE_def]>>
      asm_exists_tac>> simp[]>>
      asm_exists_tac>> simp[]) >>
    xlet_autop >>
    xcon >> xsimpl>>
    simp[PAIR_TYPE_def])
  >>
  xmatch>> rpt(xlet_autop)>>
  xif
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>EVAL_TAC)>>
  xlet_autop >>
  xlet `POSTv resv.
    &(LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) (ZIP (inds,vs)) resv) *
    ARRAY fmlv fmllsv`
  >-
    (xapp_spec (ListProgTheory.zip_v_thm |> INST_TYPE [alpha |-> ``:num``, beta |-> ``:int list``])>>
    xsimpl>>
    qexists_tac`(inds,vs)`>>simp[PAIR_TYPE_def]>>
    asm_exists_tac>> simp[]>>
    asm_exists_tac>> simp[]) >>
  xlet_autop >>
  xcon >> xsimpl >>
  simp[PAIR_TYPE_def]
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

val resize_update_arr = process_topdecs`
  fun resize_update_arr v n fml =
  if n < Array.length fml then
    (Array.update fml n v ; fml)
  else
    let val fml' = Array.array (2*n+1) None
        val u = Array.copy fml fml' 0
        val u = Array.update fml' n v
    in
      fml'
    end` |> append_prog

Theorem resize_update_arr_spec:
  OPTION_TYPE (LIST_TYPE INT) v vv ∧
  NUM n nv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_update_arr" (get_ml_prog_state()))
    [vv; nv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update v n fmlls) fmllsv') )
Proof
  rw[] >>
  xcf "resize_update_arr" (get_ml_prog_state ())>>
  rpt (xlet_autop) >>
  xif
  >- (
    xlet_autop >>
    xvar>>xsimpl>>
    `LENGTH fmlls = LENGTH fmllsv` by
      metis_tac[LIST_REL_LENGTH]>>
    simp[resize_update_def]>>
    match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def])
  >>
  rpt (xlet_autop) >>
  xlet`POSTv uv. (* TODO: probably should be added to the basis spec for Array.copy: &UNIT_TYPE () uv * *)
    ARRAY av (fmllsv ++ REPLICATE (2*n+1-LENGTH fmllsv) (Conv (SOME (TypeStamp "None" 2)) []))`
  >- (
    xapp>>xsimpl>>
    qexists_tac`REPLICATE (LENGTH fmllsv) (Conv (SOME (TypeStamp "None" 2)) [])`>>
    simp[]>>
    simp[REPLICATE_APPEND])
  >>
  xlet_autop >>
  xvar >>xsimpl>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  simp[resize_update_def]>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]>>
  match_mp_tac EVERY2_APPEND_suff>>simp[]>>
  simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]
QED

val _ = translate safe_hd_def;

val check_lrat_step_arr = process_topdecs`
  fun check_lrat_step_arr carr step fml ls =
  case step of
    Delete cl =>
      (list_delete_arr cl fml; (fml, Some ls))
  | Pr n c w i0 ik =>
    let val p = safe_hd c in
      case is_PR_arr carr fml ls p c w i0 ik of
        (ls,True) =>
          (resize_update_arr (Some c) n fml, Some(n::ls))
      | _ => (fml, None)
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
      SEP_EXISTS resv1 resv2.
      &(resv = Conv NONE [resv1; resv2]) *
      &(OPTION_TYPE (LIST_TYPE NUM) (SND (check_lrat_step_list step fmlls ls)) resv2) *
      SEP_EXISTS fmllsv'.
      ARRAY resv1 fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST (check_lrat_step_list step fmlls ls)) fmllsv') )
Proof
  rw[check_lrat_step_list_def]>>
  xcf "check_lrat_step_arr" (get_ml_prog_state ())>>
  TOP_CASE_TAC>>fs[LRAT_LRATSTEP_TYPE_def]
  >- (
    xmatch>>
    xlet_autop >>
    xlet_autop >>
    xcon >> xsimpl>>
    simp[OPTION_TYPE_def])>>
  xmatch >>
  rpt (xlet_autop)>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  reverse (Cases_on`b`)>>fs[BOOL_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon >> xsimpl>>
    simp[OPTION_TYPE_def])>>
  xmatch >>
  rpt (xlet_autop) >>
  xlet`(POSTv resv.
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update (SOME l) n fmlls) fmllsv'))`
  >-
    (xapp >> xsimpl>>
    fs[OPTION_TYPE_def])
  >>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def,LIST_TYPE_def]
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

val _ = translate parse_PR_hint_def;
val _ = translate lit_from_int_def;

val lit_from_int_side_def = fetch "-" "lit_from_int_side_def"

val lit_from_int_side = Q.prove(`
  !x. lit_from_int_side x ⇔ T`,
  rw[lit_from_int_side_def]>>
  intLib.ARITH_TAC) |> update_precondition

val _ = translate parse_until_k_def;
val _ = translate parse_clause_witness_def;

val _ = translate parse_lratstep_def;

(* Hooking up to the parser and stuff *)
val parse_and_run_list_def = Define`
  parse_and_run_list fml inds l =
  case parse_lratstep (tokens blanks l) of
    NONE => (fml,NONE)
  | SOME lrat =>
    check_lrat_step_list lrat fml inds`

val parse_and_run_arr = process_topdecs`
  fun parse_and_run_arr carr fml ls l =
  case parse_lratstep (String.tokens blanks l) of
    None => (fml,None)
  | Some lrat =>
    check_lrat_step_arr carr lrat fml ls` |> append_prog

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
      SEP_EXISTS resv1 resv2.
      &(resv = Conv NONE [resv1; resv2]) *
      &(OPTION_TYPE (LIST_TYPE NUM) (SND (parse_and_run_list fmlls ls l)) resv2) *
      SEP_EXISTS fmllsv'.
      ARRAY resv1 fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST (parse_and_run_list fmlls ls l)) fmllsv'))
Proof
  rw[parse_and_run_list_def]>>
  xcf "parse_and_run_arr" (get_ml_prog_state ())>>
  xlet`POSTv v. &((LIST_TYPE STRING_TYPE) (tokens blanks l) v) * ARRAY fmlv fmllsv`
  >-
    (xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    metis_tac[fetch "-" "blanks_v_thm"])
  >>
  xlet_autop >>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch>>xsimpl
  >- (
    xlet_autop>>
    xcon>>xsimpl)
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
  fun check_unsat'' fd carr fml ls =
    case TextIO.b_inputLine fd of
      None => (fml, Some ls)
    | Some l =>
    case parse_and_run_arr carr fml ls l of
      (fml,None) => (TextIO.output TextIO.stdErr nocheck_string; (fml,None))
    | (fml,Some ls') => check_unsat'' fd carr fml ls'` |> append_prog;

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
  !fs fd fdv fmlv fmlls fmllsv ls lsv.
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
      (check_unsat'' fd fmlls ls fs (MAP implode (linesFD fs fd))) *
      SEP_EXISTS resv1 resv2.
      &(resv = Conv NONE [resv1; resv2]) *
      &(OPTION_TYPE (LIST_TYPE NUM)
        (SND (parse_and_run_file_list (MAP implode (linesFD fs fd)) fmlls ls)) resv2) *
      SEP_EXISTS fmllsv'.
      ARRAY resv1 fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT))
          (FST (parse_and_run_file_list (MAP implode (linesFD fs fd)) fmlls ls)) fmllsv'))
Proof
  ntac 2 strip_tac >>
  completeInduct_on `LENGTH (linesFD fs fd)` >>
  rw [] >>
  xcf "check_unsat''" (get_ml_prog_state ()) >>
  `validFD fd fs` by metis_tac[get_file_content_validFD,IS_SOME_EXISTS,PAIR] >>
  xlet_autop>>
  Cases_on `lineFD fs fd` >>
  fs [OPTION_TYPE_def] >>
  xmatch
  >- (
    xlet_autop>>
    xcon>>xsimpl>>
    drule lineFD_NONE_lineForwardFD_fastForwardFD>> strip_tac>>
    fs[GSYM linesFD_nil_lineFD_NONE,OPTION_TYPE_def,check_unsat''_def,parse_and_run_file_list_def]>>
    xsimpl)>>
  xlet_autop >>
  drule linesFD_cons>>strip_tac>>
  fs[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xlet `POSTv u. ARRAY resv1 fmllsv' * STDIO (add_stderr (lineForwardFD fs fd) nocheck_string)`
    >-
      (xapp_spec output_stderr_spec>>xsimpl>>
      qexists_tac`ARRAY resv1 fmllsv' `>>qexists_tac`nocheck_string`>>
      qexists_tac`lineForwardFD fs fd`>>
      xsimpl>>
      fs[fetch "-" "nocheck_string_v_thm"]) >>
    xlet_autop >>
    xcon>> xsimpl)>>
  xapp>>
  `IS_SOME (get_file_content (lineForwardFD fs fd) fd)` by
    fs[IS_SOME_get_file_content_lineForwardFD]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  xsimpl
QED

(* We don't really care about the STDIO afterwards long as it gets closed *)
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
    val fd = TextIO.b_openIn fname
    val carr = Word8Array.array 16777216 w8zero
    val chk = check_unsat'' fd carr fml ls
    val cls = TextIO.b_closeIn fd;
  in
    case chk of
      (fml, None) => ()
    | (fml, Some ls') =>
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
     add_stderr fs (notfound_string f)))
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
    conj_tac >- (EVAL_TAC \\ simp [] \\ EVAL_TAC) >>
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
    conj_tac >- (EVAL_TAC \\ simp [] \\ EVAL_TAC) >>
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
     ARRAY resv1 fmllsv' *
     STDIO
       ((fastForwardFD (openFileFS f fs ReadMode 0) (nextFD fs))
         with infds updated_by ADELKEY (nextFD fs)) *
     &(UNIT_TYPE () u))`
    >-
      (xapp_spec closeIn_STDIO_spec>>xsimpl>>
      qmatch_goalsub_abbrev_tac`STDIO fs'`>>
      qexists_tac`ARRAY resv1 fmllsv'`>>qexists_tac`fs'`>>
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
    qexists_tac`ARRAY resv1 fmllsv'`>>qexists_tac`fs`>>xsimpl)
  >>
    xapp_spec output_stderr_spec \\ xsimpl >>
    qexists_tac`ARRAY resv1 fmllsv'`>> qexists_tac`nocheck_string`>>
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
  usage_string = strlit"Usage: cake_lrat <DIMCAS formula file> <Optional: LRAT proof file> <Optional: Size of clause array (if proof file given)>\n"`;

val r = translate usage_string_def;

val fill_arr = process_topdecs`
  fun fill_arr arr ls =
    case ls of [] => arr
    | (x::xs) =>
    case x of (i,v) =>
      fill_arr (resize_update_arr (Some v) i arr) xs` |> append_prog

Theorem fill_arr_spec:
  ∀ls lsv arrv arrls arrlsv.
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) arrls arrlsv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_arr"(get_ml_prog_state()))
  [arrv; lsv]
  (ARRAY arrv arrlsv)
  (POSTv resv.
  SEP_EXISTS arrlsv'. ARRAY resv arrlsv' *
    & LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FOLDL (λacc (i,v).  resize_update (SOME v) i acc) arrls ls) arrlsv')
Proof
  Induct>>rw[]>>
  xcf "fill_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop >>
  xlet`(POSTv resv.
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update (SOME r) q arrls) fmllsv') )`
  >- (
    xapp >> xsimpl>>
    simp[OPTION_TYPE_def] )
  >>
  xapp>>
  xsimpl
QED

(*
  Checker takes 1, 2 or 3 arguments.
  The third argument is default
*)
val parse_arguments_def = Define`
  (parse_arguments ls =
  case ls of
    [f1] => SOME(f1, NONE)
  | [f1; f2] => SOME(f1, SOME (f2, 2000000))
  | [f1; f2; f3] =>
    (case mlint$fromNatString f3 of
      NONE => NONE
    | SOME n => SOME(f1, SOME (f2, n)))
  | _ => NONE)`

val _ = translate parse_arguments_def;

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
    case parse_arguments (CommandLine.arguments ()) of
      None => TextIO.output TextIO.stdErr usage_string
    | Some (f1, rest) =>
      (case TextIO.b_inputLinesFrom f1 of
        None => TextIO.output TextIO.stdErr (notfound_string f1)
      | Some lines1 =>
        (case parse_dimacs lines1 of
          None => TextIO.output TextIO.stdErr (noparse_string f1 "DIMACS")
        | Some fml =>
        case rest of
          None => TextIO.print_list (print_dimacs fml)
        | Some (f2, n) =>
           let val ls = tosortedalist fml
               val arr = Array.array n None
               val arr = fill_arr arr ls
           in
             check_unsat' arr (List.map fst ls) f2
           end
        ))`

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs =
  case parse_arguments (TL cl) of
    NONE => add_stderr fs usage_string
  | SOME (f1, rest) =>
    if inFS_fname fs f1 then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
      SOME fml =>
        (case rest of
          NONE => add_stdout fs (concat (print_dimacs fml ))
        | SOME(f2,sz) =>
            let fmlls = toSortedAList fml in
            if inFS_fname fs (EL 2 cl) then
              case parse_lrat (all_lines fs (EL 2 cl)) of
                SOME lrat =>
                let base = REPLICATE sz NONE in
                let upd = FOLDL (λacc (i,v). resize_update (SOME v) i acc) base fmlls in
                if check_lrat_unsat_list lrat upd (MAP FST fmlls) then
                  add_stdout fs (strlit "UNSATISFIABLE\n")
                else
                  add_stderr fs nocheck_string
              | NONE => add_stderr fs nocheck_string
            else
              add_stderr fs (notfound_string (EL 2 cl)))
       | NONE => add_stderr fs (noparse_string (EL 1 cl) (strlit "DIMACS"))
    else
      add_stderr fs (notfound_string f1)`;

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
  xlet_autop >>
  xlet_autop >>
  xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  fs[]>>
  simp[check_unsat_sem_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec >> xsimpl>>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `fs` >> xsimpl) >>
  TOP_CASE_TAC>> fs[PAIR_TYPE_def]>>
  `q = HD t ∧ LENGTH t ≥ 1` by
    (fs[parse_arguments_def]>>every_case_tac>>fs[])>>
  fs[]>>
  reverse IF_CASES_TAC >> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_auto
    >- (
      xsimpl>>
      Cases_on`t`>>fs[wfcl_def]>>
      fs[validArg_def])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE (h::t)`>> qexists_tac`fs`>>
    xsimpl)>>
  xmatch >>
  xlet_auto
  >- (
    xsimpl>>
    Cases_on`t`>>fs[wfcl_def]>>
    fs[validArg_def]) >>
  fs[OPTION_TYPE_def]>>
  xmatch >>
  xlet_autop >>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def] >>
  xmatch
  >- (
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE (h::t)`>> qexists_tac`fs`>>
    xsimpl)
  >>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xapp_spec print_list_spec>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE (h::t)`>> qexists_tac`fs`>>
    xsimpl)>>
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_auto >-
    (xsimpl>>
    simp[EqualityType_NUM_BOOL,EqualityType_LIST_TYPE])>>
  rpt(xlet_autop)>>
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE r NONE)
        (REPLICATE r (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  xlet_autop >>
  xlet`
    POSTv lv.
    ARRAY resv arrlsv' * STDIO fs * COMMANDLINE (h::t) *
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
  qexists_tac` COMMANDLINE (h::t)` >> xsimpl>>
  `q' = EL 1 t ∧ LENGTH t ≥ 2` by
    (fs[parse_arguments_def]>>every_case_tac>>fs[]>>rw[])>>
  simp[GSYM PULL_EXISTS] >>
  CONJ_TAC >- fs[EVERY_EL,validArg_def]>>
  asm_exists_tac>> simp[]>>
  asm_exists_tac>> simp[]>>
  xsimpl
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
