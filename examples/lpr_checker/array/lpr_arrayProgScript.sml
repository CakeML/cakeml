(*
  This refines lpr_list to use arrays
*)
open preamble basis UnsafeProgTheory UnsafeProofTheory lprTheory lpr_listTheory parsingTheory;

val _ = new_theory "lpr_arrayProg"

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"UnsafeProg";

(* Pure translation of LPR checker *)
val _ = register_type``:lprstep``;
val _ = register_type``:'a spt``;

val _ = translate insert_def;

(* TODO: make sure these get inlined! *)
val _ = translate w8z_def;
val _ = translate w8o_def;
val _ = translate index_def;

val w8z_v_thm = fetch "-" "w8z_v_thm";
val w8o_v_thm = fetch "-" "w8o_v_thm";

val index_side_def = fetch "-" "index_side_def"

val index_side = Q.prove(`
  !x. index_side x ⇔ T`,
  simp[index_side_def]>>
  intLib.ARITH_TAC) |> update_precondition;

val _ = process_topdecs `
  exception Fail string;
` |> append_prog

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``"Fail"``

val Fail_exn_def = Define `
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)`

val eq_w8o_def = Define`
  eq_w8o v ⇔ v = w8o`

val _ = translate (eq_w8o_def |> SIMP_RULE std_ss [w8o_def]);

val every_one_arr = process_topdecs`
  fun every_one_arr carr cs =
  case cs of [] => True
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then every_one_arr carr cs
    else False` |> append_prog

val format_failure_def = Define`
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val _ = translate format_failure_def;

val unwrap_TYPE_def = Define`
  unwrap_TYPE P x y =
  ∃z. x = SOME z ∧ P z y`

val delete_literals_sing_arr_def = process_topdecs`
  fun delete_literals_sing_arr lno carr cs =
  case cs of
    [] => 0
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then
      delete_literals_sing_arr lno carr cs
    else
      if every_one_arr carr cs then ~c
      else raise Fail (format_failure lno "clause not empty or singleton after reduction")` |> append_prog

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

Theorem list_lookup_eq_EL[simp]:
  LENGTH Clist > index h ⇒
  list_lookup Clist w8z (index h) = EL (index h) Clist
Proof
  rw[list_lookup_def]
QED

Theorem resize_update_list_LUPDATE[simp]:
  LENGTH Clist > index h ⇒
  resize_update_list Clist w8z v (index h) = LUPDATE v (index h) Clist
Proof
  rw[resize_update_list_def]
QED

Theorem every_one_arr_spec:
  ∀ls lsv.
  (LIST_TYPE INT) ls lsv ∧
  EVERY ($> (LENGTH Clist) o index) ls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_one_arr" (get_ml_prog_state()))
    [Carrv; lsv]
    (W8ARRAY Carrv Clist)
    (POSTv v.
      W8ARRAY Carrv Clist *
      &BOOL (EVERY (λi. list_lookup Clist w8z (index i) = w8o) ls) v)
Proof
  Induct>>xcf "every_one_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >-
    (xmatch>>xcon>>xsimpl)
  >>
  xmatch>>
  rpt xlet_autop>>
  fs[eq_w8o_def]>>
  xif
  >-
    (xapp>>xsimpl)
  >>
  xcon>> xsimpl
QED

Theorem delete_literals_sing_arr_spec:
  ∀ls lsv lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE INT) ls lsv ∧
  EVERY ($> (LENGTH Clist) o index) ls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "delete_literals_sing_arr" (get_ml_prog_state()))
    [lnov; Carrv; lsv]
    (W8ARRAY Carrv Clist)
    (POSTve
      (λv. W8ARRAY Carrv Clist *
        &unwrap_TYPE INT (delete_literals_sing_list Clist ls) v)
      (λe. &(Fail_exn e ∧ delete_literals_sing_list Clist ls = NONE)))
Proof
  Induct>>simp[delete_literals_sing_list_def]>>
  xcf "delete_literals_sing_arr" (get_ml_prog_state ())
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>>
    xlit
    >- (
      simp[unwrap_TYPE_def]>>
      xsimpl)>>
    xsimpl)>>
  fs[LIST_TYPE_def]>> xmatch>>
  rpt xlet_autop >>
  fs[eq_w8o_def]>>
  IF_CASES_TAC>>fs[] >- (
    xif>>instantiate>>
    xapp>>xsimpl>>
    metis_tac[])>>
  xif>>instantiate>>
  xlet_auto>>
  xif
  >- (
    xapp>>xsimpl>>simp[unwrap_TYPE_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  IF_CASES_TAC>-
    metis_tac[NOT_EVERY]>>
  simp[unwrap_TYPE_def,Fail_exn_def]>>
  metis_tac[]
QED

val is_AT_arr_aux = process_topdecs`
  fun is_AT_arr_aux lno fml ls c carr =
    case ls of
      [] => Inr c
    | (i::is) =>
    if Array.length fml <= i then
      raise Fail (format_failure lno ("clause index out of bounds: " ^ Int.toString i))
    else
    case Unsafe.sub fml i of
      None => raise Fail (format_failure lno ("clause index already deleted: " ^ Int.toString i))
    | Some ci =>
      let val nl = delete_literals_sing_arr lno carr ci in
      if nl = 0 then Inl c
      else
        (Unsafe.w8update carr (index nl) w8o;
        is_AT_arr_aux lno fml is (nl::c) carr)
      end` |> append_prog

(* For every literal in every clause and their negations,
  the index is bounded above by n *)
val bounded_fml_def = Define`
  bounded_fml n fmlls ⇔
  EVERY (λCopt.
    case Copt of
      NONE => T
    | SOME C => EVERY ($> n o index) C ∧ EVERY ($> n o index o $~) C
    ) fmlls`

Theorem delete_literals_sing_list_MEM:
  ∀C.
  delete_literals_sing_list ls C = SOME x ∧ x ≠ 0
  ⇒
  MEM (-x) C
Proof
  Induct>>rw[delete_literals_sing_list_def] >> simp[] >>
  CCONTR_TAC >> fs [] >> rw []
QED

Theorem is_AT_arr_aux_spec:
  ∀ls lsv c cv fmlv fmlls fml Carrv Clist lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_AT_arr_aux" (get_ml_prog_state()))
    [lnov; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
        (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &unwrap_TYPE ($= o SND) (is_AT_list_aux fmlls ls c Clist) Clist'
        ) *
        &unwrap_TYPE
          (SUM_TYPE (LIST_TYPE INT) (LIST_TYPE INT) o FST)
          (is_AT_list_aux fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ is_AT_list_aux fmlls ls c Clist = NONE)))
Proof
  Induct>>xcf "is_AT_arr_aux" (get_ml_prog_state ())>>
  simp[is_AT_list_aux_def]
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>> xcon
    >- (
      xsimpl>>simp[unwrap_TYPE_def]>>
      simp[SUM_TYPE_def])>>
    xsimpl)>>
  fs[LIST_TYPE_def]>>
  xmatch>>
  rpt xlet_autop>>
  xif
  >- (
    rpt (xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    `list_lookup fmlls NONE h = NONE` by
      (simp[list_lookup_def]>>
      metis_tac[LIST_REL_LENGTH])>>
    simp[unwrap_TYPE_def]>>
    metis_tac[])>>
  xlet_autop>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC
  >- (
    fs[list_lookup_def]>>
    reverse (Cases_on`EL h fmlls`)>-
      (fs[IS_SOME_DEF]>>metis_tac[LIST_REL_LENGTH])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    rpt(xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  fs[list_lookup_def,OPTION_TYPE_def]>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` mp_tac)>>simp[])
  >- (
    xsimpl>>rw[]>> simp[]>>
    metis_tac[])>>
  fs[unwrap_TYPE_def]>>
  xlet_autop>>
  xif
  >- (
    xcon>>xsimpl>>
    simp[SUM_TYPE_def])>>
  rpt xlet_autop>>
  `index z < LENGTH Clist ∧ WORD8 w8o w8o_v` by
    (fs[w8o_v_thm]>>
    fs[bounded_fml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` assume_tac)>>rfs[]>>
    drule delete_literals_sing_list_MEM>>fs[]>>
    simp[MEM_EL]>>
    rw[]>>
    pop_assum mp_tac>>
    rpt (first_x_assum drule)>>
    rw[]>>
    pop_assum sym_sub_tac>>fs[])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  qexists_tac`fmlls`>>qexists_tac`z::c`>>
  simp[LIST_TYPE_def]>>
  metis_tac[]
QED

val set_array = process_topdecs`
  fun set_array carr v cs =
  case cs of [] => ()
  | (c::cs) =>
    (Unsafe.w8update carr (index c) v;
    set_array carr v cs)` |> append_prog

Theorem set_array_spec:
  ∀c cv Carrv Clist.
  (LIST_TYPE INT) c cv ∧
  WORD8 v vv ∧
  EVERY ($> (LENGTH Clist) o index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "set_array" (get_ml_prog_state()))
    [Carrv; vv; cv]
    (W8ARRAY Carrv Clist)
    (POSTv uv.
          W8ARRAY Carrv (set_list Clist v c))
Proof
  Induct>>
  xcf "set_array" (get_ml_prog_state ())>>
  rw[set_list_def]>>
  fs[LIST_TYPE_def]
  >- (xmatch>>xcon>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xapp>>
  xsimpl
QED

val is_AT_arr = process_topdecs`
  fun is_AT_arr lno fml ls c carr =
    (set_array carr w8o c;
    case is_AT_arr_aux lno fml ls c carr of
      Inl c => (set_array carr w8z c; Inl ())
    | Inr c => (set_array carr w8z c; Inr c))` |> append_prog

Theorem LENGTH_set_list_bound[simp]:
  ∀c Clist.
  EVERY ($> (LENGTH Clist) ∘ index) c ⇒
  LENGTH (set_list Clist v c) = LENGTH Clist
Proof
  Induct>>simp[set_list_def]
QED

(* a version of this is true even if x, h are not bounded *)
Theorem resize_update_list_twice:
  index x < LENGTH Clist ∧ index h < LENGTH Clist ⇒
  resize_update_list (resize_update_list Clist w8z w8o (index x)) w8z w8o (index h) =
  resize_update_list (resize_update_list Clist w8z w8o (index h)) w8z w8o (index x)
Proof
  rw[resize_update_list_def]>>
  Cases_on`x=h`>>simp[]>>
  `index x ≠ index h` by metis_tac[index_11]>>
  metis_tac[LUPDATE_commutes]
QED

Theorem set_list_resize_update_list:
  ∀c Clist.
  index x < LENGTH Clist ∧ EVERY ($> (LENGTH Clist) ∘ index) c ⇒
  set_list Clist w8o (x::c) =
  resize_update_list (set_list Clist w8o c) w8z w8o (index x)
Proof
  Induct>>rw[]>>fs[set_list_def]>>
  Cases_on`x=h`>>simp[]
  >-
    (first_x_assum (qspec_then` LUPDATE w8o (index h) Clist` mp_tac)>>
    simp[])
  >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[LUPDATE_commutes]>>
  simp[index_11]
QED

Theorem is_AT_list_aux_length_bound:
  ∀ls c Clist.
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c ∧
  is_AT_list_aux fmlls ls c (set_list Clist w8o c) = SOME(q,r) ⇒
  case q of
    INL d => r = set_list Clist w8o d ∧ LENGTH r = LENGTH Clist ∧ EVERY ($> (LENGTH Clist) ∘ index) d
  | INR d => r = set_list Clist w8o d ∧ LENGTH r = LENGTH Clist ∧ EVERY ($> (LENGTH Clist) ∘ index) d
Proof
  Induct>>rw[is_AT_list_aux_def,set_list_def]
  >-
    simp[]
  >>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  IF_CASES_TAC>-
    (rw[]>>simp[])>>
  strip_tac>>
  first_x_assum irule>>
  drule delete_literals_sing_list_MEM>> simp[]>>
  strip_tac>>
  fs[bounded_fml_def,EVERY_MEM,list_lookup_def]>>
  first_x_assum(qspec_then`EL h fmlls` mp_tac)>>
  impl_tac>-
    (`h < LENGTH fmlls` by fs[]>>
    metis_tac[MEM_EL])>>
  simp[]>>strip_tac>>
  qexists_tac`x'::c`>>
  CONJ_TAC >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[set_list_resize_update_list]>>
    simp[EVERY_MEM]>>
    pop_assum drule>>
    simp[]) >>
  simp[]>>
  rw[]
  >- (
    pop_assum drule>>
    simp[])>>
  metis_tac[]
QED

Theorem is_AT_arr_spec:
  ∀ls lsv c cv fmlv fmlls Carrv Clist lno lnov.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_AT_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; cv; Carrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' * (* TODO: actually Clist' = Clist, but not needed? *)
          &(unwrap_TYPE ($= o SND) (is_AT_list fmlls ls c Clist) Clist' ∧
            LENGTH Clist = LENGTH Clist')
          ) *
        &unwrap_TYPE
          (SUM_TYPE UNIT_TYPE (LIST_TYPE INT) o FST)
          (is_AT_list fmlls ls c Clist) v)
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ is_AT_list fmlls ls c Clist = NONE)))
Proof
  xcf "is_AT_arr" (get_ml_prog_state ())>>
  `WORD8 w8z w8z_v ∧ WORD8 w8o w8o_v` by
    simp[w8z_v_thm,w8o_v_thm]>>
  xlet_autop>>
  xlet_auto
  >- (
    xsimpl>>fs[])
  >- (
    simp[is_AT_list_def]>>
    xsimpl>>
    rw[]>>simp[]>>
    metis_tac[])>>
  fs[unwrap_TYPE_def]>>
  simp[is_AT_list_def]>>
  rw[]>>fs[]>>rw[]>>
  TOP_CASE_TAC>>fs[]>>
  drule is_AT_list_aux_length_bound>>
  rpt (disch_then drule)>>
  strip_tac>>Cases_on`q`>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xlet_auto >- (xsimpl>>rw[]>>fs[])>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[LENGTH_set_list_bound] )>>
  xmatch>>
  xlet_auto >- (xsimpl>>rw[]>>fs[])>>
  xcon>>xsimpl>>
  simp[LENGTH_set_list_bound]
QED

val _ = translate (check_overlap_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO] |> INST_TYPE [alpha |-> ``:int``]);
val _ = translate flip_def;
val _ = translate (delete_literals_def |> SIMP_RULE (srw_ss()) [MEMBER_INTRO]);
val _ = translate overlap_assignment_def;

val _ = translate overlap_assignment_def;

val check_RAT_arr = process_topdecs`
  fun check_RAT_arr lno fml carr np c ik i ci =
  (
  if List.member np ci then
    case Alist.lookup ik i of
      None => raise Fail (format_failure lno ("clause index has no reduction sequence: " ^ Int.toString i))
    | Some is =>
    case is of
      [] => if check_overlap ci (overlap_assignment [~np] c)
            then ()
            else raise Fail (format_failure lno ("clause index not satisfied but is reduced by witness: " ^ Int.toString i))
    | _ =>
      case is_AT_arr lno fml is (c @ delete_literals ci [np]) carr of
        Inl d => ()
      | _ => raise Fail (format_failure lno ("clause index not reduced to empty clause: " ^ Int.toString i))
  else ())` |> append_prog

Theorem check_RAT_arr_spec:
  ∀i iv ci civ c cv pp ppv ik ikv fmlv fmlls fml lno lnov.
  NUM lno lnov ∧
  NUM i iv ∧
  LIST_TYPE INT ci civ ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c ∧
  EVERY ($> (LENGTH Clist) ∘ index) ci
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_RAT_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; ppv; cv; ikv ; iv ; civ]
    (ARRAY fmlv fmllsv * (W8ARRAY Carrv Clist))
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(check_RAT_list fmlls Clist pp c ik i ci = SOME Clist' ∧ LENGTH Clist = LENGTH Clist')
          ))
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ check_RAT_list fmlls Clist pp c ik i ci = NONE)))
Proof
  simp[check_RAT_list_def]>>  xcf "check_RAT_arr" (get_ml_prog_state ())>>
  fs[MEMBER_INTRO]>>
  xlet_autop>>
  reverse xif
  >- (xcon>>xsimpl) >>
  xlet_autop>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt (xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  xmatch >>
  TOP_CASE_TAC >> fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt(xlet_autop)>>
    xlet `POSTv resv. &LIST_TYPE INT (overlap_assignment [-pp] c) resv * ARRAY fmlv fmllsv * W8ARRAY Carrv Clist`
    >- (
      xapp>>xsimpl>>
      metis_tac[LIST_TYPE_def])>>
    xlet_autop>>
    xif >- (xcon>>xsimpl)>>
    rpt(xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[]) >>
  xmatch >>
  rpt xlet_autop >>
  xlet `POSTv resv. &LIST_TYPE INT (delete_literals ci [pp]) resv * ARRAY fmlv fmllsv * W8ARRAY Carrv Clist`
  >- (
    xapp>>xsimpl>>
    metis_tac[LIST_TYPE_def])>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`is_AT_list _ lss cc`>>
  xlet`(POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(unwrap_TYPE ($= o SND) (is_AT_list fmlls lss cc Clist) Clist' ∧
            LENGTH Clist = LENGTH Clist')
          ) *
        &unwrap_TYPE
          (SUM_TYPE UNIT_TYPE (LIST_TYPE INT) o FST)
          (is_AT_list fmlls lss cc Clist) v)
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ is_AT_list fmlls lss cc Clist = NONE)))`
  >- (
    xapp>>
    unabbrev_all_tac>>simp[LIST_TYPE_def]>>
    simp[delete_literals_def,EVERY_MEM,MEM_FILTER]>>rw[]>>
    fs[EVERY_MEM]>>
    metis_tac[])
  >- (
    xsimpl>> rw[]>>
    simp[] >> metis_tac[]) >>
  fs[unwrap_TYPE_def]>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    xmatch>>xcon>>
    xsimpl>>
    rw[])>>
  xmatch>>
  rpt (xlet_autop)>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  metis_tac[]
QED

val check_PR_arr = process_topdecs`
  fun check_PR_arr lno fml carr nw c ik i ci =
  if check_overlap ci nw then
    case Alist.lookup ik i of
      None => if check_overlap ci (flip_1 nw) then () else raise Fail (format_failure lno ("clause index has no reduction sequence but is not satisfied by witness: " ^ Int.toString i))
    | Some is =>
    (case is of
      [] => if check_overlap ci (overlap_assignment (flip_1 nw) c) then () else raise Fail (format_failure lno ("clause index not satisfied but is reduced by witness: " ^ Int.toString i))
    | _ =>
      (case is_AT_arr lno fml is (c @ delete_literals ci (flip_1 (overlap_assignment (flip_1 nw) c))) carr of
        Inl d => True
      | _ => raise Fail (format_failure lno ("clause index not reduced to empty clause: " ^ Int.toString i))))
  else True` |> append_prog

Theorem check_PR_arr_spec:
  ∀i iv ci civ c cv w wv ik ikv fmlv fmlls fml lno lnov.
  NUM lno lnov ∧
  NUM i iv ∧
  LIST_TYPE INT ci civ ∧
  (LIST_TYPE INT) w wv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c ∧
  EVERY ($> (LENGTH Clist) ∘ index) ci
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_PR_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; wv; cv; ikv ; iv ; civ]
    (ARRAY fmlv fmllsv * (W8ARRAY Carrv Clist))
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(check_PR_list fmlls Clist w c ik i ci = SOME Clist' ∧ LENGTH Clist = LENGTH Clist')
          ))
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ check_PR_list fmlls Clist w c ik i ci = NONE)))
Proof
  xcf "check_PR_arr" (get_ml_prog_state ())>>
  simp[check_PR_list_def]>>
  xlet_autop>>
  reverse xif
  >- (xcon >> xsimpl)>>
  xlet_autop>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xif >- (xcon >> xsimpl)>>
    xsimpl>>
    rpt (xlet_autop) >>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[]) >>
  xmatch>>
  TOP_CASE_TAC>>fs[LIST_TYPE_def]>>
  xmatch
  >- (
    rpt xlet_autop>>
    xif >- (xcon>>xsimpl)>>
    xsimpl >>
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  qmatch_goalsub_abbrev_tac`is_AT_list _ lss cc`>>
  xlet`(POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' * (* TODO: actually Clist' = Clist, but not needed? *)
          &(unwrap_TYPE ($= o SND) (is_AT_list fmlls lss cc Clist) Clist' ∧
            LENGTH Clist = LENGTH Clist')
          ) *
        &unwrap_TYPE
          (SUM_TYPE UNIT_TYPE (LIST_TYPE INT) o FST)
          (is_AT_list fmlls lss cc Clist) v)
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ is_AT_list fmlls lss cc Clist = NONE)))`
  >- (
    xapp>>
    unabbrev_all_tac>>simp[LIST_TYPE_def]>>
    fs[EVERY_MEM,delete_literals_def,MEM_FILTER]>>
    metis_tac[])
  >- (
    xsimpl>> rw[]>>
    simp[] >> metis_tac[]) >>
  fs[unwrap_TYPE_def]>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    xmatch>>xcon>>
    xsimpl>>
    rw[]) >>
  xmatch>>
  rpt xlet_autop>>
  xraise>>xsimpl>>
  simp[Fail_exn_def]>>
  metis_tac[]
QED

val reindex_arr = process_topdecs`
  fun reindex_arr fml ls =
  case ls of
    [] => ([],[])
  | (i::is) =>
  if Array.length fml <= i then reindex_arr fml is
  else
  case Unsafe.sub fml i of
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

(*
val reindex_partial_arr = process_topdecs`
  fun reindex_partial_arr fml mini ls =
  case ls of
    [] => ([],([],[]))
  | (i::is) =>
  if i >= mini then
    if Array.length fml <= i then reindex_partial_arr fml mini is
    else
    case Unsafe.sub fml i of
      None => reindex_partial_arr fml mini is
    | Some v =>
    case reindex_partial_arr fml mini is of
      (l,(r,rest)) => (i::l,(v::r,rest))
  else
    ([],([],i::is))` |> append_prog

Theorem reindex_partial_arr_spec:
  ∀ls lsv fmlv fmlls mini miniv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  NUM mini miniv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_partial_arr" (get_ml_prog_state()))
    [fmlv; miniv; lsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(
      (PAIR_TYPE (LIST_TYPE NUM)
      (PAIR_TYPE
          (LIST_TYPE (LIST_TYPE INT))
          (LIST_TYPE NUM)
      ))
      (reindex_partial fmlls mini ls) resv) *
      ARRAY fmlv fmllsv)
Proof
  Induct>>rw[reindex_partial_def]>>
  xcf "reindex_partial_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>> rpt(xlet_autop)>>
    xcon >> xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def])>>
    xmatch>> rpt(xlet_autop)
  >- (
    xif>>asm_exists_tac>>xsimpl>>
    simp[list_lookup_def]>>
    `LENGTH fmlls = LENGTH fmllsv` by
      metis_tac[LIST_REL_LENGTH]>>
    ntac 2 xlet_autop >>
    IF_CASES_TAC >> fs[]>>
    xif>> asm_exists_tac>> xsimpl
    >- (xapp >> xsimpl)>>
    xlet_autop>>
    `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
      fs[LIST_REL_EL_EQN]>>
    TOP_CASE_TAC >> fs[OPTION_TYPE_def]
    >- (xmatch>> xapp>> xsimpl) >>
    xmatch>>
    xlet_autop>>
    pairarg_tac>>fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt(xlet_autop)>>
    xcon>>xsimpl>>
    simp[LIST_TYPE_def] )
  >>
    xif>>asm_exists_tac>>xsimpl>>
    rpt(xlet_autop)>>
    xcon>>
    xsimpl>>
    simp[PAIR_TYPE_def,LIST_TYPE_def]
QED
*)

(*
  Lift the definitions of check_{RAT|PR}_arr so they are not higher order
  NOTE: The underspecification of pattern match does not matter since ls rs will always
  be the same length
*)
(* val res = translate filter_reindex_def;
val res = translate filter_reindex_full_def; *)

val res = translate min_opt_def;

val list_min_opt_arr = process_topdecs`
  fun list_min_opt_arr min earr ls =
  case ls of [] => min
  | (i::is) =>
    let val ii = index i in
    if Array.length earr <= ii then
      list_min_opt_arr min earr is
    else
      list_min_opt_arr (min_opt min (Unsafe.sub earr ii)) earr is
    end` |> append_prog

Theorem list_min_opt_arr_spec:
  ∀ls lsv earliest earliestv min minv Earrv.
  (LIST_TYPE INT) ls lsv ∧
  (OPTION_TYPE NUM) min minv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_min_opt_arr" (get_ml_prog_state()))
    [minv; Earrv; lsv]
    (ARRAY Earrv earliestv)
    (POSTv v.
      ARRAY Earrv earliestv *
      &OPTION_TYPE NUM (list_min_opt min (MAP (list_lookup earliest NONE o index) ls)) v)
Proof
  Induct>>rw[list_min_opt_def]>>
  xcf "list_min_opt_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>> xsimpl)>>
  rpt(xlet_autop)>>
  drule LIST_REL_LENGTH>>
  strip_tac>>
  xif
  >- (
    xapp>>xsimpl>>
    fs[list_lookup_def,min_opt_def]>>
    TOP_CASE_TAC>>simp[]) >>
  xlet_autop>>
  xlet`(POSTv v. ARRAY Earrv earliestv * &OPTION_TYPE NUM (min_opt min (EL (index h) earliest)) v)`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>
    simp[GSYM index_def]>>
    fs[LIST_REL_EL_EQN]>>
    first_x_assum(qspec_then`index h` assume_tac)>>
    rfs[]>>
    asm_exists_tac>>
    simp[])>>
  xapp>>
  xsimpl>>
  simp[list_lookup_def]
QED

val res = translate REV_DEF;

val every_check_RAT_inds_arr = process_topdecs`
  fun every_check_RAT_inds_arr lno fml carr np d ik mini ls acc =
  case ls of [] => List.rev acc
  | (i::is) =>
  if i >= mini then
    (if Array.length fml <= i then every_check_RAT_inds_arr lno fml carr np d ik mini is acc
    else
    case Unsafe.sub fml i of
      None => every_check_RAT_inds_arr lno fml carr np d ik mini is acc
    | Some y =>
       (check_RAT_arr lno fml carr np d ik i y ;
       every_check_RAT_inds_arr lno fml carr np d ik mini is (i::acc)))
  else
    rev_1 acc (i::is)
    ` |> append_prog

Theorem every_check_RAT_inds_arr_spec:
  ∀ls lsv lno lnov pp ppv c cv ik ikv mini miniv fmlls fmllsv fmlv acc accv Carrv Clist.
  NUM lno lnov ∧
  LIST_TYPE NUM ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) ik ikv ∧
  NUM mini miniv ∧
  LIST_TYPE NUM acc accv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_check_RAT_inds_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; ppv; cv; ikv ; miniv; lsv ; accv]
    (ARRAY fmlv fmllsv * (W8ARRAY Carrv Clist))
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS inds' Clist'.
          W8ARRAY Carrv Clist' *
          &(every_check_RAT_inds_list fmlls Clist pp c ik mini ls acc = SOME (inds',Clist') ∧
            LIST_TYPE NUM inds' v ∧
            LENGTH Clist = LENGTH Clist')
          ))
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ every_check_RAT_inds_list fmlls Clist pp c ik mini ls acc = NONE)))
Proof
  Induct>>
  xcf "every_check_RAT_inds_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,every_check_RAT_inds_list_def]>>
  xmatch >- (
    xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [alpha |-> ``:num``])>>
    xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  reverse xif
  >- (
    xlet_autop>>
    xapp_spec (fetch "-" "rev_1_v_thm" |> INST_TYPE [alpha |-> ``:num``])>>
    xsimpl>>simp[]>>
    rpt(asm_exists_tac>>simp[])>>
    qexists_tac`h::ls`>>simp[LIST_TYPE_def])>>
  xlet_autop>>
  drule LIST_REL_LENGTH >>
  strip_tac>>simp[list_lookup_def]>>
  xlet_autop>>
  xif
  >- (
    xapp>>xsimpl>>
    metis_tac[])>>
  xlet_autop>>
  rveq>>simp[]>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>> xapp>>
    xsimpl>> metis_tac[])>>
  xmatch>>
  xlet_auto >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    last_x_assum(qspec_then`h` assume_tac)>>rfs[])
  >- xsimpl>>
  xlet_autop >>
  xapp>>
  xsimpl>>
  qpat_x_assum`_ = LENGTH _` sym_sub_tac>>
  rpt(asm_exists_tac>> simp[])>>
  qexists_tac`ik`>>simp[]>>
  qexists_tac`h::acc`>>
  simp[LIST_TYPE_def]
QED

val every_check_PR_inds_arr = process_topdecs`
  fun every_check_PR_inds_arr lno fml carr nw d ik mini ls acc =
  case ls of [] => List.rev acc
  | (i::is) =>
  if i >= mini then
    (if Array.length fml <= i then every_check_PR_inds_arr lno fml carr nw d ik mini is acc
    else
    case Unsafe.sub fml i of
      None => every_check_PR_inds_arr lno fml carr nw d ik mini is acc
    | Some y =>
       (check_PR_arr lno fml carr nw d ik i y ;
       every_check_PR_inds_arr lno fml carr nw d ik mini is (i::acc)))
  else
  rev_1 acc (i::is)
  ` |> append_prog

Theorem every_check_PR_inds_arr_spec:
  ∀ls lsv lno lnov w wv c cv ik ikv mini miniv fmlls fmllsv fmlv acc accv Carrv Clist.
  NUM lno lnov ∧
  LIST_TYPE NUM ls lsv ∧
  (LIST_TYPE INT) w wv ∧
  (LIST_TYPE INT) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) ik ikv ∧
  NUM mini miniv ∧
  LIST_TYPE NUM acc accv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_check_PR_inds_arr" (get_ml_prog_state()))
    [lnov; fmlv; Carrv; wv; cv; ikv ; miniv; lsv ; accv]
    (ARRAY fmlv fmllsv * (W8ARRAY Carrv Clist))
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          (SEP_EXISTS inds' Clist'.
          W8ARRAY Carrv Clist' *
          &(every_check_PR_inds_list fmlls Clist w c ik mini ls acc = SOME (inds',Clist') ∧
            LIST_TYPE NUM inds' v ∧
            LENGTH Clist = LENGTH Clist')
          ))
      (λe. ARRAY fmlv fmllsv * &(Fail_exn e ∧ every_check_PR_inds_list fmlls Clist w c ik mini ls acc = NONE)))
Proof
  Induct>>
  xcf "every_check_PR_inds_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,every_check_PR_inds_list_def]>>
  xmatch >- (
    xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [alpha |-> ``:num``])>>
    xsimpl>>
    metis_tac[])>>
  rpt xlet_autop>>
  reverse xif
  >- (
    xlet_autop>>
    xapp_spec (fetch "-" "rev_1_v_thm" |> INST_TYPE [alpha |-> ``:num``])>>
    xsimpl>>simp[]>>
    rpt(asm_exists_tac>>simp[])>>
    qexists_tac`h::ls`>>simp[LIST_TYPE_def])>>
  xlet_autop>>
  drule LIST_REL_LENGTH >>
  strip_tac>>simp[list_lookup_def]>>
  xlet_autop>>
  xif
  >- (
    xapp>>xsimpl>>
    metis_tac[])>>
  xlet_autop>>
  rveq>>simp[]>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by
    fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>> xapp>>
    xsimpl>> metis_tac[])>>
  xmatch>>
  xlet_auto >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    last_x_assum(qspec_then`h` assume_tac)>>rfs[])
  >- xsimpl>>
  xlet_autop >>
  xapp>>
  xsimpl>>
  qpat_x_assum`_ = LENGTH _` sym_sub_tac>>
  rpt(asm_exists_tac>> simp[])>>
  qexists_tac`ik`>>simp[]>>
  qexists_tac`h::acc`>>
  simp[LIST_TYPE_def]
QED

val is_PR_arr = process_topdecs`
  fun is_PR_arr lno fml inds carr earr p c wopt i0 ik =
  case is_AT_arr lno fml i0 c carr of
    (Inl d) => inds
  | (Inr d) =>
  if p <> 0 then
    case wopt of
      None =>
      (let val miniopt = list_min_opt_arr None earr [~p] in
        case miniopt of None => inds
        | Some mini => (every_check_RAT_inds_arr lno fml carr (~p) d ik mini inds [])
      end)
    | Some w =>
      if check_overlap w (flip_1 w) then raise Fail (format_failure lno "witness overlaps its own negation")
      else
      (let val miniopt = list_min_opt_arr None earr (flip_1 w) in
        case miniopt of None => inds
        | Some mini => (every_check_PR_inds_arr lno fml carr (flip_1 w) d ik mini inds [])
      end)
  else
    raise Fail (format_failure lno "pivot must be non-zero")` |> append_prog

Theorem is_PR_arr_spec:
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  INT pp ppv ∧
  (LIST_TYPE INT) c cv ∧
  OPTION_TYPE (LIST_TYPE INT) wopt woptv ∧
  (LIST_TYPE NUM) i0 i0v ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  bounded_fml (LENGTH Clist) fmlls ∧
  EVERY ($> (LENGTH Clist) ∘ index) c
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "is_PR_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv ; Carrv; Earrv; ppv; cv; woptv; i0v; ikv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv)
    (POSTve
      (λv. ARRAY fmlv fmllsv *
          ARRAY Earrv earliestv *
          (SEP_EXISTS Clist'.
          W8ARRAY Carrv Clist' *
          &(unwrap_TYPE ($= o SND) (is_PR_list fmlls ls Clist earliest pp c wopt i0 ik) Clist' ∧
            LENGTH Clist' = LENGTH Clist)
          ) *
        &unwrap_TYPE
          ((LIST_TYPE NUM) o FST)
          (is_PR_list fmlls ls Clist earliest pp c wopt i0 ik) v)
      (λe. ARRAY fmlv fmllsv * ARRAY Earrv earliestv *
        &(Fail_exn e ∧ is_PR_list fmlls ls Clist earliest pp c wopt i0 ik = NONE)))
Proof
  rw[is_PR_list_def]>>
  xcf "is_PR_arr" (get_ml_prog_state ())>>
  xlet_autop
  >- (
    xsimpl>> rw[]>>simp[]>>
    metis_tac[])>>
  fs[unwrap_TYPE_def]>>
  TOP_CASE_TAC>>
  TOP_CASE_TAC>>fs[SUM_TYPE_def]
  >- (
    xmatch>>
    xvar>>xsimpl>>
    rw[])>>
  xmatch>>
  xlet_autop>>
  reverse xif>>simp[]
  >- (
    rpt xlet_autop>>xraise>>
    xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    (* RAT *)
    rpt (xlet_autop)>>
    xlet`(POSTv v.
             ARRAY fmlv fmllsv * W8ARRAY Carrv Clist' * ARRAY Earrv earliestv *
             &OPTION_TYPE NUM (list_lookup earliest NONE (index (-pp))) v)`
    >- (
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      qexists_tac`NONE`>>simp[OPTION_TYPE_def]>>
      qexists_tac `[-pp]`>>simp[LIST_TYPE_def]>>
      simp[list_min_opt_def,min_opt_def])>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      xvar>>xsimpl>>
      rw[])>>
    rpt xlet_autop>>
    xapp >>
    rw[]>>fs[]>>
    `EVERY ($> (LENGTH r) ∘ index) y` by
      (fs[is_AT_list_def]>>every_case_tac>>fs[]>>
      qpat_x_assum`LENGTH _ = LENGTH r` (assume_tac o SYM)>>
      fs[]>>
      drule is_AT_list_aux_length_bound>>
      rpt (disch_then drule)>>simp[])>>
    simp[PULL_EXISTS]>>rpt(asm_exists_tac>>simp[])>>
    qexists_tac`ARRAY Earrv earliestv`>>xsimpl>>
    qexists_tac`ls`>>
    qexists_tac`ik` >>
    qexists_tac`[]`>>xsimpl>>
    simp[LIST_TYPE_def])>>
  (* PR *)
  rpt(xlet_autop)>>
  xif >-(
    rpt xlet_autop>>
    xraise>> xsimpl>>
    simp[Fail_exn_def]>>
    metis_tac[])>>
  rpt xlet_autop>>
  xlet`(POSTv v.
         ARRAY fmlv fmllsv * W8ARRAY Carrv Clist' * ARRAY Earrv earliestv *
         &OPTION_TYPE NUM (list_min_opt NONE (MAP (list_lookup earliest NONE ∘ index) (flip x))) v)`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    qexists_tac`NONE`>>simp[OPTION_TYPE_def]>>
    qexists_tac `flip x`>>simp[LIST_TYPE_def])>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xvar>>xsimpl>>
    rw[])>>
  rpt xlet_autop>>
  xapp >> xsimpl>>
  rw[]>>fs[]>>
  `EVERY ($> (LENGTH r) ∘ index) y` by
    (fs[is_AT_list_def]>>every_case_tac>>fs[]>>
    qpat_x_assum`LENGTH _ = LENGTH r` (assume_tac o SYM)>>
    fs[]>>
    drule is_AT_list_aux_length_bound>>
    rpt (disch_then drule)>>simp[])>>
  simp[PULL_EXISTS]>>rpt(asm_exists_tac>>simp[])>>
  qexists_tac`ls`>>
  qexists_tac`ik` >>
  qexists_tac`[]`>>xsimpl>>
  simp[LIST_TYPE_def]
QED

val list_delete_arr = process_topdecs`
  fun list_delete_arr ls fml =
    case ls of
      [] => ()
    | (i::is) =>
      if Array.length fml <= i then list_delete_arr is fml
      else
        (Unsafe.update fml i None; list_delete_arr is fml)` |> append_prog

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
    (Unsafe.update fml n v ; fml)
  else
    let val fml' = Array.array (2*n+1) None
        val u = Array.copy fml fml' 0
        val u = Unsafe.update fml' n v
    in
      fml'
    end` |> append_prog

Theorem resize_update_arr_spec:
  OPTION_TYPE vty v vv ∧
  NUM n nv ∧
  LIST_REL (OPTION_TYPE vty) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_update_arr" (get_ml_prog_state()))
    [vv; nv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' *
      &(LIST_REL (OPTION_TYPE vty) (resize_update_list fmlls NONE v n) fmllsv') )
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
    simp[resize_update_list_def]>>
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
  simp[resize_update_list_def]>>
  match_mp_tac EVERY2_LUPDATE_same>> simp[OPTION_TYPE_def]>>
  match_mp_tac EVERY2_APPEND_suff>>simp[]>>
  simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]
QED

val _ = translate safe_hd_def;

val _ = translate list_max_def;
val _ = translate list_max_index_def;

(* bump up the length to a large number *)
val resize_carr = process_topdecs`
  fun resize_carr c carr =
  let val lm = list_max_index c in
    if Word8Array.length carr <= lm
    then Word8Array.array (2*lm) w8z
    else carr
  end` |> append_prog

Theorem resize_carr_spec:
  (LIST_TYPE INT) c cv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "resize_carr" (get_ml_prog_state()))
    [cv; Carrv]
    (W8ARRAY Carrv Clist)
    (POSTv carrv.
      W8ARRAY carrv (resize_Clist c Clist))
Proof
  xcf "resize_carr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  simp[resize_Clist_def]>>xif
  >- (
    xlet_autop>>xapp>>
    xsimpl>>
    metis_tac[w8z_v_thm])>>
  xvar>>
  xsimpl
QED

val update_earliest_arr = process_topdecs`
  fun update_earliest_arr earr v ls =
  case ls of [] => earr
  | n::ns =>
    let val updmin = list_min_opt_arr (Some v) earr [n] in
      update_earliest_arr (resize_update_arr updmin (index n) earr) v ns
    end` |> append_prog

Theorem update_earliest_arr_spec:
  ∀cs csv earliest earliestv Earrv v vv.
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  NUM v vv ∧
  LIST_TYPE INT cs csv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "update_earliest_arr" (get_ml_prog_state()))
    [Earrv; vv; csv]
    (ARRAY Earrv earliestv)
    (POSTv Earrv'.
        SEP_EXISTS earliestv'.
          ARRAY Earrv' earliestv' *
          &(LIST_REL (OPTION_TYPE NUM) (update_earliest earliest v cs) earliestv'))
Proof
  Induct>>rw[update_earliest_def]>>
  xcf "update_earliest_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch >>xvar>>
    xsimpl)>>
  xmatch >>
  rpt (xlet_autop)>>
  xlet`(POSTv rv.
    ARRAY Earrv earliestv *
    &OPTION_TYPE NUM (min_opt (SOME v) (list_lookup earliest NONE (index h))) rv)`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`SOME v`>>
    simp[OPTION_TYPE_def]>>
    qexists_tac`[h]`>>
    simp[LIST_TYPE_def]>>
    simp[list_min_opt_def])>>
  rpt xlet_autop>>
  xapp>> simp[]>>
  fs[min_opt_def]>>
  TOP_CASE_TAC>>fs[MIN_COMM]
QED

val result = translate sorted_insert_def;

val check_earliest_arr = process_topdecs`
  fun check_earliest_arr fml x old new is =
  case is of
    [] => True
  | (i::is) =>
    if i >= old then
      (if i < new
      then
        (if Array.length fml <= i then check_earliest_arr fml x old new is
        else
          case Unsafe.sub fml i of
            None => check_earliest_arr fml x old new is
          | Some ci =>
            not(List.member x ci) andalso check_earliest_arr fml x old new is)
      else
        check_earliest_arr fml x old new is)
    else True` |> append_prog;

Theorem check_earliest_arr_spec:
  ∀is isv new newv old oldv x xv fmlls fmllsv fmlv.
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  INT x xv ∧
  NUM old oldv ∧
  NUM new newv ∧
  LIST_TYPE NUM is isv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_earliest_arr" (get_ml_prog_state()))
    [fmlv; xv; oldv; newv; isv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
       ARRAY fmlv fmllsv *
       &(BOOL (check_earliest fmlls x old new is) v))
Proof
  Induct>>xcf "check_earliest_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,check_earliest_def]
  >- (
    xmatch>>xcon>>
    xsimpl)
  >>
  xmatch>>
  rpt xlet_autop>>
  reverse (Cases_on`h ≥ old`)>>fs[]
  >- (
    xif>>asm_exists_tac>>xsimpl>>
    xcon>>xsimpl>>fs[])>>
  xif>>asm_exists_tac>>fs[]>>
  xlet_autop>>
  reverse xif>>fs[]
  >- (xapp>>xsimpl)>>
  xlet_autop>>
  xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  xif
  >- (
    simp[list_lookup_def]>>
    xapp>>xsimpl)>>
  xlet_autop>>
  simp[list_lookup_def]>>
  `OPTION_TYPE (LIST_TYPE INT) (EL h fmlls) (EL h fmllsv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >-
    (xmatch >> xapp>>xsimpl)>>
  xmatch>>
  xlet_autop>>
  xlet_autop>>
  xlog>>
  IF_CASES_TAC>>fs[MEMBER_INTRO]>>xsimpl>>
  xapp>>xsimpl
QED

val _ = translate list_min_aux_def;

val _ = translate list_min_def;

val hint_earliest_arr = process_topdecs`
  fun hint_earliest_arr c w ik fml inds earr =
  case w of
    None =>
    let val lm = list_min ik in
    if lm = 0 then earr
    else
      let val p = safe_hd c
          val ip = index (~p) in
          if Array.length earr <= ip then earr
          else
          (case Unsafe.sub earr ip of
            None => earr
          | Some mini =>
            if check_earliest_arr fml (~p) mini lm inds
            then
              resize_update_arr (Some lm) ip earr
            else
              earr)
      end
    end
  | Some u => earr` |> append_prog

Theorem hint_earliest_arr_spec:
  LIST_TYPE INT c cv ∧
  OPTION_TYPE (LIST_TYPE INT) w wv ∧
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE NUM)) ik ikv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "hint_earliest_arr" (get_ml_prog_state()))
    [cv; wv; ikv; fmlv; lsv; Earrv]
    (ARRAY fmlv fmllsv * ARRAY Earrv earliestv)
    (POSTv Earrv'.
        ARRAY fmlv fmllsv *
        SEP_EXISTS earliestv'.
          ARRAY Earrv' earliestv' *
          &(LIST_REL (OPTION_TYPE NUM) (hint_earliest c w ik fmlls ls earliest) earliestv'))
Proof
  rw[]>>xcf "hint_earliest_arr" (get_ml_prog_state ())>>
  fs[hint_earliest_def]>>
  reverse TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xif
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  simp[list_lookup_def]>>
  `LENGTH earliest = LENGTH earliestv` by metis_tac[LIST_REL_LENGTH]>>
  xif>>fs[]
  >- (xvar>>xsimpl)>>
  xlet_autop>>
  `OPTION_TYPE NUM (EL (index (-safe_hd c)) earliest) (EL (index (-safe_hd c)) earliestv)` by fs[LIST_REL_EL_EQN]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >-
    (xvar>>xsimpl)>>
  rpt xlet_autop>>
  reverse xif>>fs[]
  >- (xvar>>xsimpl)>>
  xlet_autop>>
  xapp_spec (resize_update_arr_spec |> Q.GEN `vty` |> ISPEC ``NUM``)>>
  xsimpl>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`SOME (list_min ik)`>>
  simp[OPTION_TYPE_def]
QED

val check_lpr_step_arr = process_topdecs`
  fun check_lpr_step_arr lno step fml ls carr earr =
  case step of
    Delete cl =>
      (list_delete_arr cl fml; (fml, ls, carr, earr))
  | Pr n c w i0 ik =>
    let val p = safe_hd c
        val carr = resize_carr c carr
        val earr = hint_earliest_arr c w ik fml ls earr
        val ls = is_PR_arr lno fml ls carr earr p c w i0 ik
        val earr = update_earliest_arr earr n c in
        (resize_update_arr (Some c) n fml, sorted_insert n ls, carr, earr)
    end` |> append_prog

val LPR_LPRSTEP_TYPE_def = fetch "-" "LPR_LPRSTEP_TYPE_def";

Theorem bounded_fml_list_delete_list:
  ∀l fmlls. bounded_fml n fmlls ⇒
  bounded_fml n (list_delete_list l fmlls)
Proof
  Induct>>rw[list_delete_list_def]>>
  first_x_assum match_mp_tac>>
  fs[bounded_fml_def,EVERY_EL,EL_LUPDATE]>>
  rw[]>>fs[]
QED

Theorem list_max_index_bounded_clause:
  ∀l.
  list_max_index l < n ⇒
  EVERY ($> n o index) l ∧ EVERY ($> n o index o $~) l
Proof
  simp[list_max_index_def]>>
  Induct>>rw[list_max_def,index_def]>>
  intLib.ARITH_TAC
QED

Theorem bounded_fml_resize_update_list:
  bounded_fml m fmlls ∧
  EVERY ($> m o index) l ∧ EVERY ($> m o index o $~) l ⇒
  bounded_fml m (resize_update_list fmlls NONE (SOME l) n)
Proof
  rw[bounded_fml_def,EVERY_MEM]>>
  drule MEM_resize_update_list>>rw[]>>simp[]
QED

Theorem LENGTH_resize_Clist:
  LENGTH Clist ≤ LENGTH (resize_Clist l Clist)
Proof
  rw[resize_Clist_def]
QED

Theorem bounded_fml_leq:
  bounded_fml n fmlls ∧ n ≤ m ⇒
  bounded_fml m fmlls
Proof
  rw[bounded_fml_def,EVERY_MEM]>>
  first_x_assum drule>>every_case_tac>>simp[]>>
  rw[]>>rpt(first_x_assum drule)>>fs[]
QED

Theorem EVERY_index_resize_Clist:
  EVERY ($> (LENGTH (resize_Clist ls Clist)) ∘ index) ls ∧
  EVERY ($> (LENGTH (resize_Clist ls Clist)) ∘ index o $~) ls
Proof
  rw[]>>
  simp[resize_Clist_def,list_max_index_def]>>
  qmatch_goalsub_abbrev_tac`list_max lss`>>
  qspec_then `lss` assume_tac list_max_max>>
  fs[EVERY_MEM,Abbr`lss`,MEM_MAP,PULL_EXISTS]>>
  ntac 2 strip_tac>>first_x_assum drule>>
  rw[]>>simp[index_def]>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem check_lpr_step_arr_spec:
  NUM lno lnov ∧
  LPR_LPRSTEP_TYPE step stepv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lpr_step_arr" (get_ml_prog_state()))
    [lnov; stepv; fmlv; lsv; Carrv; Earrv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv)
    (POSTve
      (λv.
        SEP_EXISTS v1 v2 v3 v4.
          &(v = Conv NONE [v1; v2; v3; v4]) *
          (* v1 is a pointer to the formula array *)
          (SEP_EXISTS fmllsv' Clist' earliestv'.
            ARRAY v1 fmllsv' *
            W8ARRAY v3 Clist' *
            ARRAY v4 earliestv' *
            &(
              unwrap_TYPE
                (λv fv.
                  bounded_fml (LENGTH Clist') (FST v) ∧
                  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                (check_lpr_step_list step fmlls ls Clist earliest) fmllsv' ∧
            unwrap_TYPE ($= o FST o SND o SND) (check_lpr_step_list step fmlls ls Clist earliest) Clist' ∧
            unwrap_TYPE (LIST_REL (OPTION_TYPE NUM) o SND o SND o SND) (check_lpr_step_list step fmlls ls Clist earliest) earliestv' ∧
            LENGTH Clist ≤ LENGTH Clist'
            ))
        * (* v2 is the indexing list *)
          &unwrap_TYPE (λa b. LIST_TYPE NUM (FST (SND a)) b) (check_lpr_step_list step fmlls ls Clist earliest) v2
      )
      (λe. ARRAY fmlv fmllsv * (SEP_EXISTS Earrv earliestv. ARRAY Earrv earliestv) * &(Fail_exn e ∧ check_lpr_step_list step fmlls ls Clist earliest = NONE)))
Proof
  rw[check_lpr_step_list_def]>>
  xcf "check_lpr_step_arr" (get_ml_prog_state ())>>
  TOP_CASE_TAC>>fs[LPR_LPRSTEP_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop >>
    xcon >> xsimpl>>
    simp[unwrap_TYPE_def]>>
    metis_tac[bounded_fml_list_delete_list])>>
  xmatch >>
  rpt (xlet_autop)>>
  xlet_auto
  >- (xsimpl>>
    metis_tac[bounded_fml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist])
  >- (xsimpl>> rw[] >> simp[] >>
    qexists_tac`Earrv'`>> qexists_tac`earliestv'`>>
    xsimpl)>>
  fs[unwrap_TYPE_def]>>
  TOP_CASE_TAC>>fs[]>>
  rpt xlet_autop>>
  xlet`(POSTv resv.
      W8ARRAY carrv Clist' *
      ARRAY Earrv'' earliestv'' *
      SEP_EXISTS fmllsv'.
      ARRAY resv fmllsv' *
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update_list fmlls NONE (SOME l) n) fmllsv'))`
  >- (
    xapp_spec (resize_update_arr_spec |> Q.GEN `vty` |> ISPEC ``(LIST_TYPE INT)``)>>
    xsimpl>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`SOME l`>>simp[OPTION_TYPE_def])
  >>
  rw[]>>fs[]>>xcon>>xsimpl>>
  simp[OPTION_TYPE_def,LIST_TYPE_def]>>rw[]
  >-
    metis_tac[bounded_fml_resize_update_list,bounded_fml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist]>>
  simp[LENGTH_resize_Clist]
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

open mlintTheory;

(* TODO: Mostly copied from mlintTheory *)
val result = translate fromChar_unsafe_def;

val fromChars_range_unsafe_tail_def = Define`
  fromChars_range_unsafe_tail l 0       str mul acc = acc ∧
  fromChars_range_unsafe_tail l (SUC n) str mul acc =
    fromChars_range_unsafe_tail l n str (mul * 10)  (acc + fromChar_unsafe (strsub str (l + n)) * mul)`;

Theorem fromChars_range_unsafe_tail_eq:
  ∀n l s mul acc.
  fromChars_range_unsafe_tail l n s mul acc = (fromChars_range_unsafe l n s) * mul + acc
Proof
  Induct>>rw[fromChars_range_unsafe_tail_def,fromChars_range_unsafe_def]
QED

Theorem fromChars_range_unsafe_alt:
  fromChars_range_unsafe l n s = fromChars_range_unsafe_tail l n s 1 0
Proof
  rw[fromChars_range_unsafe_tail_eq]
QED

val result = translate fromChars_range_unsafe_tail_def;
val result = translate fromChars_range_unsafe_alt;

val res = translate_no_ind (mlintTheory.fromChars_unsafe_def
  |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]>>
  fs[padLen_DEC_eq,ADD1]
  )
  |> update_precondition;

val result = translate parsingTheory.fromString_unsafe_def;

val fromstring_unsafe_side_def = definition"fromstring_unsafe_side_def";
val fromchars_unsafe_side_def = theorem"fromchars_unsafe_side_def";
val fromchars_range_unsafe_tail_side_def = theorem"fromchars_range_unsafe_tail_side_def";
val fromchars_range_unsafe_side_def = fetch "-" "fromchars_range_unsafe_side_def";

Theorem fromchars_unsafe_side_thm:
   ∀n s. n ≤ LENGTH s ⇒ fromchars_unsafe_side n (strlit s)
Proof
  completeInduct_on`n` \\ rw[]
  \\ rw[Once fromchars_unsafe_side_def,fromchars_range_unsafe_side_def,fromchars_range_unsafe_tail_side_def]
QED

val fromString_unsafe_side = Q.prove(
  `∀x. fromstring_unsafe_side x = T`,
  Cases
  \\ rw[fromstring_unsafe_side_def]
  \\ Cases_on`s` \\ fs[mlstringTheory.substring_def]
  \\ simp_tac bool_ss [ONE,SEG_SUC_CONS,SEG_LENGTH_ID]
  \\ match_mp_tac fromchars_unsafe_side_thm
  \\ rw[]) |> update_precondition;

val _ = translate blanks_def;
val _ = translate tokenize_def;

val _ = translate tokenize_fast_def;

val tokenize_fast_side = Q.prove(
  `∀x. tokenize_fast_side x = T`,
  EVAL_TAC >> fs[]) |> update_precondition;

val _ = translate toks_def;
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
(* val _ = translate lit_from_int_def;

val lit_from_int_side_def = fetch "-" "lit_from_int_side_def"

val lit_from_int_side = Q.prove(`
  !x. lit_from_int_side x ⇔ T`,
  rw[lit_from_int_side_def]>>
  intLib.ARITH_TAC) |> update_precondition *)

val _ = translate parse_until_k_def;
val _ = translate parse_clause_witness_def;

val _ = translate parse_lprstep_def;
val parse_lprstep_side_def = definition"parse_lprstep_side_def";

val parse_lprstep_side = Q.prove(
  `∀x. parse_lprstep_side x = T`,
  rw[parse_lprstep_side_def] >>
  fs[integerTheory.int_ge]) |> update_precondition;

(* Hooking up to the parser and stuff *)
val parse_and_run_list_def = Define`
  parse_and_run_list fml inds Clist earliest l =
  case parse_lprstep l of
    NONE => NONE
  | SOME lpr =>
    check_lpr_step_list lpr fml inds Clist earliest`

val parse_and_run_arr = process_topdecs`
  fun parse_and_run_arr lno fml ls carr earr l =
  case parse_lprstep l of
    None => raise Fail (format_failure lno "failed to parse line")
  | Some lpr =>
    check_lpr_step_arr lno lpr fml ls carr earr` |> append_prog

Theorem parse_and_run_arr_spec:
  NUM lno lnov ∧
  LIST_TYPE (SUM_TYPE STRING_TYPE INT) l lv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "parse_and_run_arr" (get_ml_prog_state()))
    [lnov; fmlv; lsv; Carrv; Earrv; lv]
    (ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv)
    (POSTve
      (λv.
         SEP_EXISTS v1 v2 v3 v4.
          &(v = Conv NONE [v1; v2; v3; v4]) *
          (SEP_EXISTS fmllsv' Clist' earliestv'.
            ARRAY v1 fmllsv' *
            W8ARRAY v3 Clist' *
            ARRAY v4 earliestv' *
            &(
              unwrap_TYPE
                (λv fv.
                bounded_fml (LENGTH Clist') (FST v) ∧
                LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                   (parse_and_run_list fmlls ls Clist earliest l) fmllsv' ∧
            unwrap_TYPE ($= o FST o SND o SND) (parse_and_run_list fmlls ls Clist earliest l) Clist' ∧
            unwrap_TYPE (LIST_REL (OPTION_TYPE NUM) o SND o SND o SND) (parse_and_run_list fmlls ls Clist earliest l) earliestv' ∧
            LENGTH Clist ≤ LENGTH Clist'
            )
          ) *
          &unwrap_TYPE (λa b. LIST_TYPE NUM (FST (SND a)) b) (parse_and_run_list fmlls ls Clist earliest l) v2)
      (λe. ARRAY fmlv fmllsv * (SEP_EXISTS Earrv' earliestv'. ARRAY Earrv' earliestv') * &(Fail_exn e ∧ parse_and_run_list fmlls ls Clist earliest l = NONE)))
Proof
  rw[parse_and_run_list_def]>>
  xcf "parse_and_run_arr" (get_ml_prog_state ())>>
  assume_tac (fetch "-" "blanks_v_thm")>>
  rpt xlet_autop >>
  TOP_CASE_TAC >> fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    simp[unwrap_TYPE_def,Fail_exn_def]>>
    qexists_tac`Earrv`>> qexists_tac`earliestv`>>xsimpl>>
    metis_tac[])>>
  xapp>>fs[]>>
  metis_tac[]
QED

val notfound_string_def = Define`
  notfound_string f = concat[strlit"c Input file: ";f;strlit" no such file or directory\n"]`;

val r = translate notfound_string_def;

val noparse_string_def = Define`
  noparse_string f s = concat[strlit"c Input file: ";f;strlit" unable to parse in format: "; s;strlit"\n"]`;

val r = translate noparse_string_def;

(*
val nocheck_string_def = Define`
  nocheck_string = strlit "cake_lpr: LPR checking failed.\n"`;

val r = translate nocheck_string_def;
*)

(* TODO: possibly make this dump every 10000 lines or so *)
val check_unsat'' = process_topdecs `
  fun check_unsat'' fd lno fml ls carr earr =
    case TextIO.b_inputLineTokens fd blanks tokenize_fast of
      None => (fml, ls)
    | Some l =>
    case parse_and_run_arr lno fml ls carr earr l of
      (fml',ls',carr',earr') => check_unsat'' fd (lno+1) fml' ls' carr' earr'` |> append_prog;

(* This says what happens to the STDIO *)
val check_unsat''_def = Define`
  (check_unsat'' fd fml inds Clist earliest fs [] = STDIO (fastForwardFD fs fd)) ∧
  (check_unsat'' fd fml inds Clist earliest fs (ln::ls) =
    case parse_and_run_list fml inds Clist earliest (toks_fast ln) of
      NONE => STDIO (lineForwardFD fs fd)
    | SOME (fml', inds', Clist', earliest') =>
      check_unsat'' fd fml' inds' Clist' earliest' (lineForwardFD fs fd) ls)`

(* This says what happens to fml, inds *)
val parse_and_run_file_list_def = Define`
  (parse_and_run_file_list [] fml inds Clist earliest = SOME (fml, inds)) ∧
  (parse_and_run_file_list (x::xs) fml inds Clist earliest =
    case parse_and_run_list fml inds Clist earliest (toks_fast x) of
      NONE => NONE
    | SOME (fml', inds', Clist', earliest') => parse_and_run_file_list xs fml' inds' Clist' earliest')`

Theorem parse_and_run_file_list_eq:
  ∀ls fml inds Clist earliest.
  parse_and_run_file_list ls fml inds Clist earliest =
  case parse_lpr ls of
    NONE => NONE
  | SOME lpr => check_lpr_list lpr fml inds Clist earliest
Proof
  Induct>>fs[parse_and_run_list_def,parse_lpr_def,parse_and_run_file_list_def,check_lpr_list_def]>>
  rw[]>>
  every_case_tac>>fs[toks_fast_def]>>
  simp[check_lpr_list_def]
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

val blanks_v_thm = theorem "blanks_v_thm";
val tokenize_v_thm = theorem "tokenize_v_thm";
val tokenize_fast_v_thm = theorem "tokenize_fast_v_thm";

val b_inputLineTokens_specialize =
  b_inputLineTokens_spec_lines
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize_fast`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_fast_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> SIMP_RULE std_ss [blanks_v_thm,tokenize_fast_v_thm,blanks_def] ;

Theorem check_unsat''_spec:
  !fd fdv lines fs fmlv fmlls fmllsv ls lsv Clist Carrv lno lnov Earrv earliest earliestv.
  NUM lno lnov ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_unsat''" (get_ml_prog_state()))
    [fdv; lnov; fmlv; lsv; Carrv; Earrv]
    (STDIO fs * ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv * INSTREAM_LINES fd fdv lines fs)
    (POSTve
      (λv.
         SEP_EXISTS k v1 v2.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
           &(v = Conv NONE [v1; v2]) *
           (SEP_EXISTS fmllsv'.
            ARRAY v1 fmllsv' *
            &(unwrap_TYPE
              (λv fv.
              LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                 (parse_and_run_file_list lines fmlls ls Clist earliest) fmllsv')) *
          &(unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
            (parse_and_run_file_list lines fmlls ls Clist earliest) v2)
      )
      (λe.
         SEP_EXISTS k fmlv fmllsv Earrv earliestv lines'.
           STDIO (forwardFD fs fd k) * INSTREAM_LINES fd fdv lines' (forwardFD fs fd k) *
           ARRAY fmlv fmllsv *
           ARRAY Earrv earliestv *
           &(Fail_exn e ∧ parse_and_run_file_list lines fmlls ls Clist earliest = NONE)))
Proof
  ntac 2 strip_tac
  \\ Induct \\ rw []
  \\ xcf "check_unsat''" (get_ml_prog_state ())
  THEN1 (
    xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv [] (forwardFD fs fd k) *
                &OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) NONE v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv’
      \\ qexists_tac ‘[]’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ fs[OPTION_TYPE_def])
    \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
    \\ xmatch \\ fs []
    \\ xcon \\ xsimpl
    \\ fs [parse_and_run_file_list_def]
    \\ qexists_tac ‘k’ \\ xsimpl
    \\ fs [unwrap_TYPE_def])
  \\ xlet ‘(POSTv v.
            SEP_EXISTS k.
                ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv *
                STDIO (forwardFD fs fd k) *
                INSTREAM_LINES fd fdv lines (forwardFD fs fd k) *
                & OPTION_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)) (SOME (toks_fast h)) v)’
    THEN1 (
      xapp_spec b_inputLineTokens_specialize
      \\ qexists_tac ‘ARRAY fmlv fmllsv * W8ARRAY Carrv Clist * ARRAY Earrv earliestv ’
      \\ qexists_tac ‘h::lines’
      \\ qexists_tac ‘fs’
      \\ qexists_tac ‘fd’ \\ xsimpl \\ fs []
      \\ rw [] \\ qexists_tac ‘x’ \\ xsimpl
      \\ simp[toks_fast_def])
  \\ fs [std_preludeTheory.OPTION_TYPE_def] \\ rveq \\ fs []
  \\ xmatch \\ fs []
  \\ xlet_auto >- (
    xsimpl>>simp[unwrap_TYPE_def]>>rw[]>>
    qexists_tac`x`>> qexists_tac`x'`>>xsimpl)
  >- (
    xsimpl>>
    simp[parse_and_run_file_list_def]>>
    xsimpl>>
    rw[]>>
    qexists_tac ‘k’>>
    qexists_tac`fmlv`>>qexists_tac`fmllsv`>>
    xsimpl>>
    qexists_tac`x`>>qexists_tac`x'`>>
    qexists_tac ‘lines’>>
    xsimpl>>
    metis_tac[])>>
  rveq \\ fs [] >>
  xmatch>>
  xlet_autop >>
  xapp>>xsimpl>>
  fs [unwrap_TYPE_def]>>
  goal_assum (first_assum o mp_then (Pos (el 2)) mp_tac)>>simp[]>>
  rfs []>> rveq \\ fs [] >>
  asm_exists_tac \\ fs []>>
  qexists_tac ‘emp’>>
  asm_exists_tac \\ fs []>>
  asm_exists_tac \\ fs []>>
  qexists_tac ‘(forwardFD fs fd k)’>> xsimpl>>
  simp[parse_and_run_file_list_def]>>
  PairCases_on ‘a’ \\ fs [] >>
  rveq \\ fs []>>
  rw[]>>fs[] >>
  qexists_tac ‘k+x’ \\ fs [GSYM fsFFIPropsTheory.forwardFD_o] >> xsimpl >>
  qexists_tac`x'`>>
  qexists_tac`x''` >>
  qexists_tac ‘x'''’ \\ xsimpl >>
  qexists_tac ‘x'''''’ \\ xsimpl >>
  metis_tac[]
QED

(* We don't really care about the STDIO afterwards long as it gets closed *)
Theorem check_unsat''_eq:
∀ls fd fml inds fs Clist earliest.
∃n.
  check_unsat'' fd fml inds Clist earliest fs ls =
  case parse_and_run_file_list ls fml inds Clist earliest of
   NONE => STDIO (forwardFD fs fd n)
 | SOME _ => STDIO (fastForwardFD fs fd)
Proof
  Induct>>rw[check_unsat''_def,parse_and_run_file_list_def]>>
  TOP_CASE_TAC
  >-
    metis_tac[lineForwardFD_forwardFD]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  first_x_assum(qspecl_then[`fd`,`q`,`q'`,`lineForwardFD fs fd`,`q''`,`r`] strip_assume_tac)>>
  simp[]>>
  TOP_CASE_TAC>>fs[]>>
  qspecl_then [`fs`,`fd`] strip_assume_tac lineForwardFD_forwardFD>>
  simp[forwardFD_o]>>
  metis_tac[]
QED

val check_unsat' = process_topdecs `
  fun check_unsat' fml ls earr fname n =
  let
    val fd = TextIO.b_openIn fname
    val carr = Word8Array.array n w8z
    val chk = Inr (check_unsat'' fd 0 fml ls carr earr)
      handle Fail s => Inl s
    val cls = TextIO.b_closeIn fd;
  in
    case chk of
      Inl s => TextIO.output TextIO.stdErr s
    | Inr res =>
      case res of (fml, ls') =>
      (if is_unsat_arr fml ls' then
        TextIO.print "s VERIFIED UNSAT\n"
      else
        TextIO.output TextIO.stdErr "c empty clause not derived at end of proof\n")
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

Theorem check_unsat'_spec:
  NUM n nv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  FILENAME f fv ∧
  hasFreeFD fs ∧
  bounded_fml n fmlls
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"check_unsat'"(get_ml_prog_state()))
  [fmlv; lsv; Earrv; fv; nv]  (STDIO fs * ARRAY fmlv fmllsv * ARRAY Earrv earliestv)
  (POSTv uv.
  &UNIT_TYPE () uv *
  SEP_EXISTS err.
  STDIO (
    if inFS_fname fs f then
      (case parse_lpr (all_lines fs f) of
       SOME lpr =>
         if check_lpr_unsat_list lpr fmlls ls (REPLICATE n w8z) earliest then
           add_stdout fs (strlit "s VERIFIED UNSAT\n")
         else
           add_stderr fs err
      | NONE => add_stderr fs err)
    else
      add_stderr fs err))
Proof
  xcf"check_unsat'"(get_ml_prog_state()) >>
  reverse (Cases_on `STD_streams fs`)
  >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`)
  >- (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  reverse (Cases_on `inFS_fname fs f`) >> simp[]
  >- (
    xhandle`POSTe ev.
      &BadFileName_exn ev *
      &(~inFS_fname fs f) *
      STDIO fs *
      ARRAY Earrv earliestv *
      SEP_EXISTS fmllsv'. ARRAY fmlv fmllsv'`
    >-
      (xlet_auto_spec (SOME b_openIn_STDIO_spec) \\ xsimpl)
    >>
      fs[BadFileName_exn_def]>>
      xcases>>rw[]>>
      xlet_auto>>xsimpl>>
      xapp_spec output_stderr_spec  >> xsimpl>>
      qexists_tac`ARRAY Earrv earliestv * ARRAY fmlv fmllsv'`>>
      qexists_tac`notfound_string f`>>
      qexists_tac`fs`>>xsimpl >>
      rw[] >>
      qexists_tac`notfound_string f`>>
      xsimpl)>>
  qmatch_goalsub_abbrev_tac`$POSTv Qval`>>
  xhandle`$POSTv Qval` \\ xsimpl >>
  qunabbrev_tac`Qval`>>
  xlet_auto_spec (SOME b_openIn_spec_lines) \\ xsimpl >>
  `WORD8 w8z w8z_v` by fs[w8z_v_thm]>>
  xlet_autop >>
  qmatch_goalsub_abbrev_tac`STDIO fss`>>
  qabbrev_tac`Clist = REPLICATE n w8z`>>
  xlet`POSTv resv.
         SEP_EXISTS v0 v1 v2 fmllsv' fmlv' earliestv Earrv k rest.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY fmlv' fmllsv' *
          &(
            case
              parse_and_run_file_list (all_lines fs f) fmlls ls (REPLICATE n w8z) earliest
            of
              NONE => resv = Conv (SOME (TypeStamp "Inl" 23)) [v0] ∧ ∃s. STRING_TYPE s v0
            | SOME(fmlls',inds') =>
              resv = Conv (SOME (TypeStamp "Inr" 23)) [Conv NONE [v1; v2]] ∧
              v1 = fmlv' ∧
              LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls' fmllsv' ∧ LIST_TYPE NUM inds' v2
          )`
  >- (
    simp[]>>
    TOP_CASE_TAC
    >- (
      xhandle`POSTe e.
        SEP_EXISTS fmlv fmllsv rest k.
          STDIO (forwardFD fss (nextFD fs) k) *
          INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
          ARRAY fmlv fmllsv *
          &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) fmlls ls Clist earliest = NONE)`
      >- (
        (* this used to be an xauto_let .. sigh *)
        xlet `POSTe e.
         SEP_EXISTS k fmlv fmllsv lines'.
           STDIO (forwardFD fss (nextFD fs) k) *
           INSTREAM_LINES (nextFD fs) is lines' (forwardFD fss (nextFD fs) k) *
           ARRAY fmlv fmllsv *
           &(Fail_exn e ∧ parse_and_run_file_list (all_lines fs f) fmlls ls Clist earliest = NONE)`
        THEN1
         (xapp_spec check_unsat''_spec
          \\ xsimpl
          \\ qexists_tac `emp`
          \\ xsimpl \\ fs [Abbr`Clist`]
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ qexists_tac `all_lines fs f`
          \\ qexists_tac `fss`
          \\ qexists_tac `nextFD fs`
          \\ xsimpl \\ fs [unwrap_TYPE_def]
          \\ rpt strip_tac
          \\ qexists_tac `x`
          \\ rename [`ARRAY a1 a2`]
          \\ qexists_tac `a1`
          \\ qexists_tac `a2`
          \\ qexists_tac `x'''''`
          \\ xsimpl)>>
        fs[unwrap_TYPE_def]>>
        xsimpl>>
        rw[]>>
        rename [`ARRAY a1 a2`] >>
        qexists_tac `a1` >>
        qexists_tac `a2` >>
        xsimpl>>
        qexists_tac `x'''` >>
        qexists_tac `x` >> xsimpl) >>
      fs[Fail_exn_def]>>
      xcases>>
      xcon>>xsimpl>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>> simp[]>>
      rename [`ARRAY a1 a2`] >>
      qexists_tac `a2` >>
      qexists_tac `a1` >>
      qexists_tac `k` >>
      qexists_tac `rest` >> xsimpl)
    >>
    xhandle`(POSTv v.
        SEP_EXISTS v1 v2 k rest.
         STDIO (forwardFD fss (nextFD fs) k) *
         INSTREAM_LINES (nextFD fs) is rest (forwardFD fss (nextFD fs) k) *
         &(v = Conv (SOME (TypeStamp "Inr" 23)) [Conv NONE [v1; v2]]) *
         (SEP_EXISTS fmllsv'.
           ARRAY v1 fmllsv' *
           &(unwrap_TYPE
             (λv fv. LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FST v) fv)
                (parse_and_run_file_list (all_lines fs f) fmlls ls Clist earliest) fmllsv')) *
         &unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
           (parse_and_run_file_list (all_lines fs f) fmlls ls Clist earliest) v2)`
    >- (
        xlet `POSTv v.
                   SEP_EXISTS k v1 v2.
                       STDIO (forwardFD fss (nextFD fs) k) *
                       INSTREAM_LINES (nextFD fs) is [] (forwardFD fss (nextFD fs) k) *
                       &(v = Conv NONE [v1; v2]) *
                       (SEP_EXISTS fmllsv'.
                            ARRAY v1 fmllsv' *
                            &unwrap_TYPE
                              (λv fv.
                                   LIST_REL (OPTION_TYPE (LIST_TYPE INT))
                                     (FST v) fv)
                              (parse_and_run_file_list (all_lines fs f) fmlls ls Clist earliest)
                              fmllsv') *
                       &unwrap_TYPE (λa b. LIST_TYPE NUM (SND a) b)
                         (parse_and_run_file_list (all_lines fs f) fmlls ls Clist earliest) v2`
        THEN1
         (xapp_spec check_unsat''_spec
          \\ xsimpl \\ qexists_tac `emp`
          \\ xsimpl \\ fs [Abbr`Clist`]
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ asm_exists_tac \\ fs []
          \\ qexists_tac `all_lines fs f`
          \\ qexists_tac `fss`
          \\ qexists_tac `nextFD fs`
          \\ xsimpl \\ fs [unwrap_TYPE_def]
          \\ rpt strip_tac
          \\ qexists_tac `x'`
          \\ xsimpl) >>
        fs[unwrap_TYPE_def]>>
        xcon >>
        xsimpl>>
        rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
        rename [`INSTREAM_LINES _ _ rr`] \\ qexists_tac `rr` \\ xsimpl) >>
      xsimpl>>simp[unwrap_TYPE_def]>>
      Cases_on`x`>>fs[]>>rw[]>>xsimpl >>
      rename [`forwardFD _ _ k`] \\ qexists_tac `k` >>
      rename [`INSTREAM_LINES _ _ rr`] \\ qexists_tac `rr` \\ xsimpl)>>
  qmatch_asmsub_abbrev_tac`parse_and_run_file_list lss _ _ Clist`>>
  `lss = all_lines fs f` by
    (simp[Abbr`lss`]>>
    drule linesFD_openFileFS_nextFD>>
    rpt (disch_then drule)>>
    disch_then (qspec_then`ReadMode` assume_tac)>>
    simp[MAP_MAP_o,o_DEF])>>
  qspecl_then [`lss`,`fmlls`,`ls`,`Clist`] strip_assume_tac parse_and_run_file_list_eq>>
  fs[]>>rw[]>>
  pop_assum kall_tac >>
  xlet `POSTv v. STDIO fs * ARRAY fmlv' fmllsv'`
  THEN1
   (xapp_spec b_closeIn_spec_lines >>
    rename [`ARRAY a1 a2`] >>
    qexists_tac `ARRAY a1 a2` >>
    qexists_tac `rest` >>
    qexists_tac `forwardFD fss (nextFD fs) k` >>
    qexists_tac `nextFD fs` >>
    conj_tac THEN1
     (fs [forwardFD_def,Abbr`fss`]
      \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
      \\ imp_res_tac fsFFIPropsTheory.STD_streams_nextFD \\ fs []) >>
    `validFileFD (nextFD fs) (forwardFD fss (nextFD fs) k).infds` by
      (simp[validFileFD_forwardFD]>> simp[Abbr`fss`]
       \\ imp_res_tac fsFFIPropsTheory.nextFD_ltX \\ fs []
       \\ match_mp_tac validFileFD_nextFD \\ fs []) >>
    xsimpl >> rw [] >>
    imp_res_tac (DECIDE ``n<m:num ==> n <= m``) >>
    imp_res_tac fsFFIPropsTheory.nextFD_leX \\ fs [] >>
    drule fsFFIPropsTheory.openFileFS_ADELKEY_nextFD >>
    fs [Abbr`fss`] \\ xsimpl) >>
  Cases_on`parse_lpr (all_lines fs f)`>> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec \\ xsimpl >>
    asm_exists_tac>>xsimpl>>
    qexists_tac`ARRAY fmlv' fmllsv'`>>
    qexists_tac`fs`>>
    xsimpl>>
    rw[]>> qexists_tac`s`>>xsimpl)>>
  simp[check_lpr_unsat_list_def] >>
  TOP_CASE_TAC>>fs[]
  >- (
    Cases_on `check_lpr_list x fmlls ls Clist earliest` \\ fs []
    \\ rename [`_ = SOME xx`] \\ PairCases_on `xx` \\ fs []
    \\ rveq \\ fs [] \\ xmatch
    \\ rveq \\ fs [] \\ xmatch
    \\ xlet_autop
    \\ xif
    \\ asm_exists_tac \\ fs []
    \\ xapp_spec print_spec >> xsimpl
    \\ qexists_tac`ARRAY fmlv' fmllsv'`
    \\ qexists_tac`fs`>>xsimpl)
  \\ Cases_on `check_lpr_list x fmlls ls Clist earliest` \\ fs [] \\ rveq \\ fs []
  THEN1
   (rveq \\ fs [] \\ xmatch >>
    xapp_spec output_stderr_spec \\ xsimpl >>
    asm_exists_tac>>xsimpl>>
    qexists_tac`ARRAY fmlv' fmllsv'`>>
    qexists_tac`fs`>>
    xsimpl>>
    rw[]>>qexists_tac`s`>>xsimpl)
  \\ rename [`_ = SOME xx`] \\ PairCases_on `xx` \\ fs []
  THEN1
   (rveq \\ fs [] \\ xmatch
    \\ rveq \\ fs [] \\ xmatch
    \\ xlet_autop
    \\ xif
    \\ asm_exists_tac \\ fs [] >>
    xapp_spec output_stderr_spec \\ xsimpl >>
    qexists_tac`ARRAY fmlv' fmllsv'`>>
    qexists_tac`fs`>>
    xsimpl>>
    rw[]>>
    qmatch_goalsub_abbrev_tac`_ fs lss`>>
    qexists_tac`lss`>>xsimpl)
QED

Theorem abs_compute:
  ABS (i:int) = if i < 0 then -i else i
Proof
  intLib.ARITH_TAC
QED

val _ = translate abs_compute;

val _ = translate max_lit_def;
val _ = translate toChar_def;

val tochar_side_def = definition"tochar_side_def";
val tochar_side = Q.prove(
  `∀x. tochar_side x <=> (~(x < 10) ==> x < 201)`,
  rw[tochar_side_def])
  |> update_precondition;

val _ = translate zero_pad_def
val _ = translate simple_toChars_def

val simple_toChars_side = Q.prove(
  `∀x y z. simple_tochars_side x y z = T`,
  ho_match_mp_tac simple_toChars_ind \\ rw[]
  \\ rw[Once (theorem"simple_tochars_side_def")])
  |> update_precondition;

val _ = save_thm("toChars_ind",
   toChars_ind |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);
val _ = add_preferred_thy "-";
val _ = translate
  (toChars_def |> REWRITE_RULE[maxSmall_DEC_def,padLen_DEC_eq]);

val toStdString_v_thm = translate
  (toStdString_def |> REWRITE_RULE[maxSmall_DEC_def])
val tostdstring_side = Q.prove(
  `∀x. tostdstring_side x = T`,
  rw[definition"tostdstring_side_def"]
  \\ intLib.COOPER_TAC)
  |> update_precondition;

val _ = translate print_clause_def;

val _ = translate spt_center_def;
val _ = translate apsnd_cons_def;
val _ = translate spt_centers_def;
val _ = translate spt_right_def;
val _ = translate spt_left_def;
val _ = translate combine_rle_def;
val _ = translate spts_to_alist_def;
val _ = translate toSortedAList_def;

val _ = translate print_header_line_def;

val _ = translate print_dimacs_def;

val print_dimacs_side = Q.prove(
  `∀x. print_dimacs_side x = T`,
  rw[definition"print_dimacs_side_def"]>>
  `0 ≤ 0:int` by fs[]>> drule max_lit_max_1>>
  simp[])
  |> update_precondition;

val _ = translate parse_header_line_def;

val parse_header_line_side = Q.prove(`
   ∀x. parse_header_line_side x= T`,
  rw[definition"parse_header_line_side_def"]>>
  intLib.ARITH_TAC)
  |> update_precondition;

val _ = translate parse_clause_aux_def;
val _ = translate parse_clause_def;

(* NOTE: inefficient-ish version that reads all lines at once *)
val _ = translate parsingTheory.build_fml_def;
val _ = translate nocomment_line_def;
val _ = translate parse_dimacs_toks_def;
(* val _ = translate parse_dimacs_def; *)

val usage_string_def = Define`
  usage_string = strlit"Usage: cake_lpr <DIMACS formula file> <Optional: LPR proof file> <Optional: Size of clause array (if proof file given)>\n"`;

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
    & LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (FOLDL (λacc (i,v).  resize_update_list acc NONE (SOME v) i) arrls ls) arrlsv')
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
      &(LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (resize_update_list arrls NONE (SOME r) q) fmllsv') )`
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

Theorem all_distinct_map_fst_rev:
  ALL_DISTINCT (MAP FST ls) ⇔ ALL_DISTINCT (MAP FST (REVERSE ls))
Proof
  fs[MAP_REVERSE]
QED

Theorem LENGTH_FOLDR_resize_update_list1:
  ∀ll.
  LENGTH (FOLDR (λx acc. (λ(i,v). resize_update_list acc NONE (SOME v) i) x) (REPLICATE n NONE) ll) ≥ n
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once resize_update_list_def]
QED

Theorem LENGTH_FOLDR_resize_update_list2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). resize_update_list acc NONE (SOME v) i) x) (REPLICATE n NONE) ll)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once resize_update_list_def]
  >- (
    first_x_assum drule>>
    simp[])>>
  first_x_assum drule>>simp[]
QED

Theorem FOLDL_resize_update_list_lookup:
  ∀ls.
  ALL_DISTINCT (MAP FST ls) ⇒
  ∀x.
  x < LENGTH (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  =
  ALOOKUP ls x
Proof
  simp[Once (GSYM EVERY_REVERSE), Once (GSYM MAP_REVERSE)]>>
  simp[FOLDL_FOLDR_REVERSE]>>
  simp[GSYM alookup_distinct_reverse]>>
  simp[Once all_distinct_map_fst_rev]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE ls`>>
  pop_assum kall_tac>>
  Induct_on`ll`>-
    simp[EL_REPLICATE]>>
  simp[FORALL_PROD]>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once resize_update_list_def]>>
  strip_tac>>
  simp[Once resize_update_list_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC >> simp[]>>
  simp[EL_APPEND_EQN]>>rw[]>>
  simp[EL_REPLICATE]>>
  CCONTR_TAC>>fs[]>>
  Cases_on`ALOOKUP ll x`>>fs[]>>
  drule ALOOKUP_MEM>>
  strip_tac>>
  drule LENGTH_FOLDR_resize_update_list2>>
  simp[]>>
  metis_tac[]
QED

Theorem ALL_DISTINCT_MAP_FST_toSortedAList:
  ALL_DISTINCT (MAP FST (toSortedAList t))
Proof
  `SORTED $< (MAP FST (toSortedAList t))` by
    simp[SORTED_toSortedAList]>>
  pop_assum mp_tac>>
  match_mp_tac SORTED_ALL_DISTINCT>>
  simp[irreflexive_def]
QED

val fill_earliest = process_topdecs`
  fun fill_earliest earr ls =
    case ls of [] => earr
    | (x::xs) =>
    case x of (n,c) =>
      fill_earliest (update_earliest_arr earr n c) xs` |> append_prog

Theorem fill_earliest_spec:
  ∀ls lsv earliest earliestv Earrv.
  LIST_TYPE (PAIR_TYPE NUM (LIST_TYPE INT)) ls lsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv
  ⇒
  app (p:'ffi ffi_proj) ^(fetch_v"fill_earliest"(get_ml_prog_state()))
  [Earrv; lsv]
  (ARRAY Earrv earliestv)
  (POSTv resv.
  SEP_EXISTS earliestv'. ARRAY resv earliestv' *
    &(LIST_REL (OPTION_TYPE NUM) (FOLDL (λacc (i,v). update_earliest acc i v) earliest ls) earliestv'))
Proof
  Induct>>rw[]>>
  xcf "fill_earliest" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>>xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop >>
  xapp>>
  simp[]
QED

val check_unsat = (append_prog o process_topdecs) `
  fun check_unsat u =
    case parse_arguments (CommandLine.arguments ()) of
      None => TextIO.output TextIO.stdErr usage_string
    | Some (f1, rest) =>
      (case TextIO.b_inputAllTokensFrom f1 blanks tokenize of
        None => TextIO.output TextIO.stdErr (notfound_string f1)
      | Some lines1 =>
        (case parse_dimacs_toks lines1 of
          None => TextIO.output TextIO.stdErr (noparse_string f1 "DIMACS")
        | Some (mv,fml) =>
        case rest of
          None => TextIO.print_list (print_dimacs fml)
        | Some (f2, n) =>
           let val ls = tosortedalist fml
               val arr = Array.array n None
               val arr = fill_arr arr ls
               val bnd = 2*mv + 3
               val earr = Array.array bnd None
               val earr = fill_earliest earr ls
           in
             check_unsat' arr (List.rev (List.map fst ls)) earr f2 bnd
           end
        ))`

val check_unsat_sem_def = Define`
  check_unsat_sem cl fs err =
  case parse_arguments (TL cl) of
    NONE => add_stderr fs err
  | SOME (f1, rest) =>
    if inFS_fname fs f1 then
      case parse_dimacs (all_lines fs (EL 1 cl)) of
      SOME (mv,fml) =>
        (case rest of
          NONE => add_stdout fs (concat (print_dimacs fml ))
        | SOME(f2,sz) =>
            let fmlls = toSortedAList fml in
            if inFS_fname fs (EL 2 cl) then
              case parse_lpr (all_lines fs (EL 2 cl)) of
                SOME lpr =>
                let base = REPLICATE sz NONE in
                let bnd = 2*mv+3 in
                let upd = FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) base fmlls in
                let earliest = FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) fmlls in
                if check_lpr_unsat_list lpr upd (REVERSE (MAP FST fmlls)) (REPLICATE bnd w8z) earliest then
                  add_stdout fs (strlit "s VERIFIED UNSAT\n")
                else
                  add_stderr fs err
              | NONE => add_stderr fs err
            else
              add_stderr fs err)
       | NONE => add_stderr fs err
    else
      add_stderr fs err`;

val b_inputAllTokensFrom_spec_specialize =
  b_inputAllTokensFrom_spec
  |> Q.GEN `f` |> Q.SPEC`blanks`
  |> Q.GEN `fv` |> Q.SPEC`blanks_v`
  |> Q.GEN `g` |> Q.ISPEC`tokenize`
  |> Q.GEN `gv` |> Q.ISPEC`tokenize_v`
  |> Q.GEN `a` |> Q.ISPEC`SUM_TYPE STRING_TYPE INT`
  |> REWRITE_RULE [blanks_v_thm,tokenize_v_thm,blanks_def] ;

Theorem check_unsat_spec:
   hasFreeFD fs
   ⇒
   app (p:'ffi ffi_proj) ^(fetch_v"check_unsat"(get_ml_prog_state()))
     [Conv NONE []]
     (COMMANDLINE cl * STDIO fs)
     (POSTv uv. &UNIT_TYPE () uv *
     COMMANDLINE cl * SEP_EXISTS err. STDIO (check_unsat_sem cl fs err))
Proof
  xcf"check_unsat"(get_ml_prog_state())>>
  reverse(Cases_on`wfcl cl`) >- (fs[COMMANDLINE_def] \\ xpull)>>
  reverse (Cases_on `STD_streams fs`) >- (fs [TextIOProofTheory.STDIO_def] \\ xpull) >>
  reverse (Cases_on`consistentFS fs`) >-
    (fs [STDIO_def,IOFS_def,wfFS_def,consistentFS_def] \\ xpull \\ metis_tac[]) >>
  rpt xlet_autop >>
  Cases_on `cl` >- fs[wfcl_def] >>
  fs[]>>
  simp[check_unsat_sem_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp_spec output_stderr_spec >> xsimpl>>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac `usage_string` >> simp [theorem "usage_string_v_thm"] >>
    CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `fs` >> xsimpl>>
    rw[] >>
    qexists_tac`usage_string`>>xsimpl)>>
  TOP_CASE_TAC>> fs[PAIR_TYPE_def]>>
  `q = HD t ∧ LENGTH t ≥ 1` by
    (fs[parse_arguments_def]>>every_case_tac>>fs[])>>
  fs[]>>
  reverse (Cases_on`inFS_fname fs (HD t)`)>> fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
            (if inFS_fname fs (HD t) then
               SOME(MAP (MAP tokenize o tokens blanks) (all_lines fs (HD t)))
             else NONE) sv * STDIO fs * COMMANDLINE (h::t))`
    >- (
      xapp_spec b_inputAllTokensFrom_spec_specialize >>
      xsimpl>>
      qexists_tac` COMMANDLINE (h::t)`>>
      qexists_tac`fs`>>simp[]>>
      qexists_tac`HD t`>>xsimpl>>
      Cases_on`t`>>fs[]>>rw[]>>
      fs[wfcl_def,FILENAME_def,validArg_def])>>
    fs[OPTION_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE (h::t)`>> qexists_tac`fs`>>
    xsimpl>>
    rw[]>>
    qmatch_goalsub_abbrev_tac`_ fs lss`>>
    qexists_tac`lss`>>xsimpl) >>
  xmatch >>
  xlet`(POSTv sv. &OPTION_TYPE (LIST_TYPE (LIST_TYPE (SUM_TYPE STRING_TYPE INT)))
        (if inFS_fname fs (HD t) then
           SOME(MAP (MAP tokenize o tokens blanks) (all_lines fs (HD t)))
         else NONE) sv * STDIO fs * COMMANDLINE (h::t))`
  >- (
    xapp_spec b_inputAllTokensFrom_spec_specialize >>
    xsimpl>>
    qexists_tac` COMMANDLINE (h::t)`>>
    qexists_tac`fs`>>simp[]>>
    qexists_tac`HD t`>>xsimpl>>
    Cases_on`t`>>fs[]>>rw[]>>
    fs[wfcl_def,FILENAME_def,validArg_def])>>
  fs[OPTION_TYPE_def]>>
  xmatch >>
  xlet_autop >>
  fs[parse_dimacs_def,toks_def]>>
  `toks = (MAP tokenize ∘ tokens blanks)` by
    metis_tac[toks_def,ETA_AX,o_DEF]>>
  simp[]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xapp_spec output_stderr_spec \\ xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`COMMANDLINE (h::t)`>> qexists_tac`fs`>>
    xsimpl>>
    rw[]>>
    qmatch_goalsub_abbrev_tac`_ fs lss`>>
    qexists_tac`lss`>>xsimpl)>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
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
  xlet_auto >-(
    xsimpl>>
    simp[EqualityType_NUM_BOOL,EqualityType_LIST_TYPE])>>
  rpt(xlet_autop)>>
  `LIST_REL (OPTION_TYPE (LIST_TYPE INT)) (REPLICATE r NONE)
        (REPLICATE r (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  rpt (xlet_autop) >>
  `LIST_REL (OPTION_TYPE NUM) (REPLICATE (2 * q' + 3) NONE)
          (REPLICATE (2 * q' + 3) (Conv (SOME (TypeStamp "None" 2)) []))` by
    simp[LIST_REL_REPLICATE_same,OPTION_TYPE_def]>>
  xlet_autop>>
  xlet`
    POSTv lv.
    ARRAY resv' earliestv' * ARRAY resv arrlsv' * STDIO fs * COMMANDLINE (h::t) *
    &(LIST_TYPE NUM (MAP FST (toSortedAList r')) lv)`
  >- (
    xapp_spec (ListProgTheory.map_1_v_thm |> INST_TYPE [alpha |-> ``:num``, beta |-> ``:num # int list``])>>
    xsimpl>>
    asm_exists_tac >>simp[]>>
    qexists_tac`FST`>>
    qexists_tac`NUM`>>simp[fst_v_thm])>>
  xlet_autop >>
  xapp_spec (GEN_ALL check_unsat'_spec)>>
  xsimpl>>
  simp[GSYM CONJ_ASSOC]>>
  fs[FILENAME_def,validArg_def,check_unsat_sem_def,wfcl_def] >>
  rpt(asm_exists_tac>>simp[])>>
  qexists_tac` COMMANDLINE (h::t)` >> xsimpl>>
  `q'' = EL 1 t ∧ LENGTH t ≥ 2` by
    (fs[parse_arguments_def]>>every_case_tac>>fs[]>>rw[])>>
  simp[GSYM PULL_EXISTS] >>
  CONJ_TAC >- fs[EVERY_EL,validArg_def]>>
  asm_exists_tac>> simp[]>>
  `parse_dimacs (all_lines fs (HD t)) = SOME (q',r')` by
    simp[parse_dimacs_def]>>
  drule (parse_dimacs_wf_bound)>>
  strip_tac>>
  simp[Once (METIS_PROVE [] ``P ∧ Q ∧ C ⇔ Q ∧ C ∧ P``)]>>
  asm_exists_tac>> simp[]>>
  simp[PULL_EXISTS]>>
  asm_exists_tac>> simp[]>>
  asm_exists_tac>> simp[]>>
  reverse CONJ_TAC>- (
    rw[bounded_fml_def,EVERY_EL]>>
    `ALL_DISTINCT (MAP FST (toSortedAList r'))` by metis_tac[ALL_DISTINCT_MAP_FST_toSortedAList]>>
    drule FOLDL_resize_update_list_lookup>>
    disch_then drule>>
    strip_tac>>simp[]>>
    TOP_CASE_TAC>>fs[]>>
    drule ALOOKUP_MEM>>
    simp[MEM_toSortedAList]>>
    fs[values_def,PULL_EXISTS]>>
    strip_tac>>
    first_x_assum drule>>
    simp[EVERY_EL]>>
    rw[]>>first_x_assum drule>>simp[index_def]>>rw[]>>
    intLib.ARITH_TAC)>>
  xsimpl>>
  ntac 3 strip_tac>>
  qexists_tac`x`>>
  xsimpl
QED

Theorem check_unsat_whole_prog_spec2:
   hasFreeFD fs ⇒
   whole_prog_spec2 check_unsat_v cl fs NONE (λfs'. ∃err. fs' = check_unsat_sem cl fs err)
Proof
  rw[basis_ffiTheory.whole_prog_spec2_def]
  \\ match_mp_tac (MP_CANON (DISCH_ALL (MATCH_MP app_wgframe (UNDISCH check_unsat_spec))))
  \\ xsimpl
  \\ rw[PULL_EXISTS]
  \\ qexists_tac`check_unsat_sem cl fs x`
  \\ qexists_tac`x`
  \\ xsimpl
  \\ rw[check_unsat_sem_def]
  \\ every_case_tac
  \\ simp[GSYM add_stdo_with_numchars,with_same_numchars]
QED

local

val name = "check_unsat"
val (sem_thm,prog_tm) =
  whole_prog_thm (get_ml_prog_state()) name (UNDISCH check_unsat_whole_prog_spec2)
val check_unsat_prog_def = Define`check_unsat_prog = ^prog_tm`;

in

Theorem check_unsat_semantics =
  sem_thm
  |> REWRITE_RULE[GSYM check_unsat_prog_def]
  |> DISCH_ALL
  |> SIMP_RULE(srw_ss())[GSYM CONJ_ASSOC,AND_IMP_INTRO];

end

Theorem fml_rel_check_lpr_list:
  ∀steps fml fmlls inds fmlls' inds' Clist earliest.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧
  earliest_rel fmlls earliest ∧
  EVERY wf_lpr steps ∧
  check_lpr_list steps fmlls inds Clist earliest = SOME (fmlls', inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lpr steps fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lpr_list_def,check_lpr_def]>>
  ntac 8 strip_tac>>
  ntac 4 (TOP_CASE_TAC>>fs[])>>
  strip_tac>>
  drule  fml_rel_check_lpr_step_list>>
  rpt (disch_then drule)>>
  disch_then (qspec_then `h` mp_tac)>> simp[]>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  qexists_tac`r`>>fs[]>>
  match_mp_tac check_lpr_step_wf_fml>>
  metis_tac[]
QED

Theorem fml_rel_FOLDL_resize_update_list:
  fml_rel x
  (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
Proof
  rw[fml_rel_def]>>
  reverse(rw[])
  >- (
    CCONTR_TAC>>fs[]>>
    `?y. lookup x' x = SOME y` by
      (Cases_on`lookup x' x`>>fs[])>>
    fs[GSYM MEM_toSortedAList]>>
    fs[FOLDL_FOLDR_REVERSE]>>
    `MEM (x',y) (REVERSE (toSortedAList x))` by
      fs[MEM_REVERSE]>>
    drule LENGTH_FOLDR_resize_update_list2>>
    simp[]>>
    metis_tac[])>>
  `ALL_DISTINCT (MAP FST (toSortedAList x))` by
    fs[ALL_DISTINCT_MAP_FST_toSortedAList]>>
  drule FOLDL_resize_update_list_lookup>>
  simp[ALOOKUP_toSortedAList]
QED

Theorem ind_rel_FOLDL_resize_update_list:
  ind_rel
  (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
  (REVERSE (MAP FST (toSortedAList x)))
Proof
  simp[ind_rel_def,FOLDL_FOLDR_REVERSE]>>
  `∀z. MEM z (MAP FST (toSortedAList x)) ⇔ MEM z (MAP FST (REVERSE (toSortedAList x)))` by
    simp[MEM_MAP]>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`MAP FST ls`>>
  rpt(pop_assum kall_tac)>>
  Induct_on`ls`>>rw[]
  >-
    metis_tac[EL_REPLICATE]>>
  Cases_on`h`>>fs[]>>
  fs[IS_SOME_EXISTS]>>
  pop_assum mp_tac>>
  simp[Once resize_update_list_def]>>
  pop_assum mp_tac>>
  simp[Once resize_update_list_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    strip_tac>>
    IF_CASES_TAC>>simp[])
  >>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC>>simp[EL_APPEND_EQN]>>
  IF_CASES_TAC>>simp[]>>
  simp[EL_REPLICATE]
QED

Theorem list_lookup_update_earliest:
  ∀cl ls x y.
  index y = x ⇒
  list_lookup (update_earliest ls v cl) NONE x =
  case list_lookup ls NONE x of
    NONE => if MEM y cl then SOME v else NONE
  | SOME k =>
    if MEM y cl then SOME (MIN k v) else SOME k
Proof
  Induct>>simp[update_earliest_def]
  >-
    (rw[]>>TOP_CASE_TAC>>simp[])>>
  rw[]>>
  qmatch_goalsub_abbrev_tac`list_lookup (update_earliest lss _ _)_ _`>>
  simp[]
  >- (
    first_x_assum(qspecl_then[`lss`,`index h`,`h`] mp_tac)>>
    simp[Abbr`lss`,list_lookup_resize_update_list]>>
    strip_tac>>
    IF_CASES_TAC>>simp[]>>
    Cases_on`list_lookup ls NONE (index h)`>>simp[min_opt_def,MIN_DEF])
  >- (
    first_x_assum(qspecl_then[`lss`,`index y`,`y`] mp_tac)>>
    simp[Abbr`lss`,list_lookup_resize_update_list]>>
    strip_tac>>
    IF_CASES_TAC>>simp[]>>
    Cases_on`list_lookup ls NONE (index h)`>>simp[min_opt_def,MIN_DEF])>>
  fs[]>>
  first_x_assum(qspecl_then[`lss`,`y`] mp_tac)>>
  simp[Abbr`lss`,list_lookup_resize_update_list]>>
  `index y ≠ index h` by fs[index_11]>>
  simp[]
QED

Theorem earliest_rel_FOLDL_resize_update_list:
  earliest_rel
  (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
  (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (toSortedAList x))
Proof
  simp[FOLDL_FOLDR_REVERSE]>>
  qpat_abbrev_tac`lss = REVERSE _`>>
  pop_assum kall_tac>> Induct_on`lss`
  >- (
    fs[earliest_rel_def]>>rw[]>>
    TOP_CASE_TAC>>simp[EL_REPLICATE])>>
  simp[]>>strip_tac>>pairarg_tac>>simp[]>>
  metis_tac[earliest_rel_resize_update_list0,earliest_rel_resize_update_list1,earliest_rel_resize_update_list2]
QED

Theorem SORTED_REVERSE:
  transitive P ⇒
  (SORTED P (REVERSE ls) ⇔ SORTED (λx y. P y x)  ls)
Proof
  rw[]>>
  DEP_REWRITE_TAC [SORTED_EL_LESS]>>
  fs[]>>
  CONJ_TAC>- (
    fs[transitive_def]>>
    metis_tac[])>>
  simp[EL_REVERSE]>>
  rw[EQ_IMP_THM]
  >- (
    first_x_assum (qspecl_then [`LENGTH ls-n-1`,`LENGTH ls-m-1`] mp_tac)>>
    simp[GSYM ADD1])>>
  first_x_assum match_mp_tac>>
  simp[]>>
  intLib.ARITH_TAC
QED

Theorem check_lpr_unsat_list_sound:
  check_lpr_unsat_list lpr
    (FOLDL (λacc (i,v). resize_update_list acc NONE (SOME v) i) (REPLICATE n NONE) (toSortedAList x))
    (REVERSE (MAP FST (toSortedAList x)))
    Clist
    (FOLDL (λacc (i,v). update_earliest acc i v) (REPLICATE bnd NONE) (toSortedAList x)) ∧
  wf_fml x ∧ EVERY wf_lpr lpr ∧ EVERY ($= w8z) Clist ⇒
  unsatisfiable (interp x)
Proof
  rw[check_lpr_unsat_list_def]>>
  every_case_tac>>fs[]>>
  assume_tac (fml_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac (ind_rel_FOLDL_resize_update_list |> INST_TYPE [alpha |-> ``:int list``])>>
  assume_tac earliest_rel_FOLDL_resize_update_list>>
  drule fml_rel_check_lpr_list>>
  `SORTED $>= (REVERSE (MAP FST (toSortedAList x)))` by
    (DEP_REWRITE_TAC [SORTED_REVERSE]>>
    simp[transitive_def]>>
    `SORTED $< (MAP FST (toSortedAList x))` by fs[SORTED_toSortedAList]>>
    drule SORTED_weaken>> disch_then match_mp_tac>>
    simp[])>>
  simp[]>>
  rpt(disch_then drule)>>
  strip_tac>>
  drule check_lpr_sound>>
  rpt(disch_then drule)>>
  drule fml_rel_is_unsat_list  >>
  rpt(disch_then drule)>>
  metis_tac[is_unsat_sound,satSemTheory.unsatisfiable_def]
QED

val _ = export_theory();
