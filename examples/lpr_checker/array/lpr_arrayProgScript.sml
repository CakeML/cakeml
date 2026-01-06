(*
  This refines lpr_list to use arrays
*)
Theory lpr_arrayProg
Ancestors
  md5Prog lpr_composeProg UnsafeProof lpr lpr_list HashtableProof
Libs
  preamble basis

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]
val _ = set_trace "BasicProvers.var_eq_old" 1

val _ = translation_extends"lpr_composeProg";

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

val fail = get_exn_conv ``«Fail»``

Definition Fail_exn_def:
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)
End

Definition eq_w8o_def:
  eq_w8o v ⇔ v = w8o
End

val _ = translate (eq_w8o_def |> SIMP_RULE std_ss [w8o_def]);

val every_one_arr = process_topdecs`
  fun every_one_arr carr cs =
  case cs of [] => True
  | c::cs =>
    if eq_w8o (Unsafe.w8sub carr (index c)) then every_one_arr carr cs
    else False` |> append_prog

Definition format_failure_def:
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"
End

val _ = translate format_failure_def;

Definition unwrap_TYPE_def:
  unwrap_TYPE P x y =
  ∃z. x = SOME z ∧ P z y
End

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

Theorem any_el_eq_EL[simp]:
  LENGTH Clist > index h ⇒
  any_el (index h) Clist w8z = EL (index h) Clist
Proof
  rw[any_el_ALT]
QED

Theorem update_resize_LUPDATE[simp]:
  LENGTH Clist > index h ⇒
  update_resize Clist w8z v (index h) = LUPDATE v (index h) Clist
Proof
  rw[update_resize_def]
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
      &BOOL (EVERY (λi. any_el (index i) Clist w8z = w8o) ls) v)
Proof
  Induct>>rw[]>>
  xcf "every_one_arr" (get_ml_prog_state ())>>
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
  rpt strip_tac>>
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
  gvs[unwrap_TYPE_def,Fail_exn_def]>>
  metis_tac[]
QED

val is_AT_arr_aux = process_topdecs`
  fun is_AT_arr_aux lno fml ls c carr =
    case ls of
      [] => Inr c
    | (i::is) =>
    case Array.lookup fml None i of
      None => raise Fail (format_failure lno ("clause index unavailable: " ^ Int.toString i))
    | Some ci =>
      let val nl = delete_literals_sing_arr lno carr ci in
      if nl = 0 then Inl c
      else
        (Unsafe.w8update carr (index nl) w8o;
        is_AT_arr_aux lno fml is (nl::c) carr)
      end` |> append_prog

(* For every literal in every clause and their negations,
  the index is bounded above by n *)
Definition bounded_fml_def:
  bounded_fml n fmlls ⇔
  EVERY (λCopt.
    case Copt of
      NONE => T
    | SOME C => EVERY ($> n o index) C ∧ EVERY ($> n o index o $~) C
    ) fmlls
End

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
  Induct>>rw[]>>
  xcf "is_AT_arr_aux" (get_ml_prog_state ())>>
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
  `OPTION_TYPE (LIST_TYPE INT) (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt(xlet_autop)>>
    xraise>>xsimpl>>
    simp[Fail_exn_def,unwrap_TYPE_def]>>
    metis_tac[])>>
  xmatch>>
  xlet_auto
  >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` mp_tac)>>
    fs[any_el_ALT])
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
  `index z < LENGTH Clist ∧ WORD8 w8o w8o_v` by (
    fs[w8o_v_thm]>>
    fs[bounded_fml_def,EVERY_EL]>>
    first_x_assum(qspec_then`h` assume_tac)>>rfs[]>>
    drule delete_literals_sing_list_MEM>>fs[]>>
    fs[LIST_REL_EL_EQN]>>
    fs[any_el_ALT]>>
    `h < LENGTH fmllsv` by fs[LIST_REL_EL_EQN]>>
    fs[]>>rfs[LIST_REL_EL_EQN]>>
    fs[MEM_EL]>>rw[]>>
    rpt (first_x_assum drule)>>
    rw[]>>
    qpat_x_assum`-z = _` sym_sub_tac>>fs[])>>
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
  rw[]>>
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
Theorem update_resize_twice:
  index x < LENGTH Clist ∧ index h < LENGTH Clist ⇒
  update_resize (update_resize Clist w8z w8o (index x)) w8z w8o (index h) =
  update_resize (update_resize Clist w8z w8o (index h)) w8z w8o (index x)
Proof
  rw[update_resize_def]>>
  Cases_on`x=h`>>simp[]>>
  `index x ≠ index h` by metis_tac[index_11]>>
  metis_tac[LUPDATE_commutes]
QED

Theorem set_list_update_resize:
  ∀c Clist.
  index x < LENGTH Clist ∧ EVERY ($> (LENGTH Clist) ∘ index) c ⇒
  set_list Clist w8o (x::c) =
  update_resize (set_list Clist w8o c) w8z w8o (index x)
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
  fs[bounded_fml_def,EVERY_MEM,any_el_ALT]>>
  first_x_assum(qspec_then`EL h fmlls` mp_tac)>>
  impl_tac>-
    (`h < LENGTH fmlls` by fs[]>>
    metis_tac[MEM_EL])>>
  simp[]>>strip_tac>>
  qexists_tac`x'::c`>>
  CONJ_TAC >- (
    dep_rewrite.DEP_ONCE_REWRITE_TAC[set_list_update_resize]>>
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
  rw[]>>
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
  simp[check_RAT_list_def]>>
  rpt strip_tac>>
  xcf "check_RAT_arr" (get_ml_prog_state ())>>
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
  rw[]>>
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
    list_min_opt_arr (min_opt min (Array.lookup earr None (index i))) earr is` |> append_prog

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
      &OPTION_TYPE NUM (list_min_opt min (MAP (λx. any_el (index x) earliest NONE) ls)) v)
Proof
  Induct>>rw[list_min_opt_def]>>
  xcf "list_min_opt_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>
  xmatch
  >- (xvar>> xsimpl)>>
  drule LIST_REL_LENGTH>>
  strip_tac>>
  rpt(xlet_autop)>>
  xlet_auto>>
  xlet`(POSTv v. ARRAY Earrv earliestv * &OPTION_TYPE NUM (min_opt min (any_el (index h) earliest NONE)) v)`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>
    simp[GSYM index_def]>>
    fs[any_el_ALT]>>rw[]>>
    fs[LIST_REL_EL_EQN]
    >- (
      first_x_assum(qspec_then`index h` assume_tac)>>
      rfs[]>>
      asm_exists_tac>>
      simp[])>>
    qexists_tac`NONE`>>xsimpl>>
    simp[OPTION_TYPE_def])>>
  xapp>>
  xsimpl
QED

val res = translate REV_DEF;

val every_check_RAT_inds_arr = process_topdecs`
  fun every_check_RAT_inds_arr lno fml carr np d ik mini ls acc =
  case ls of [] => List.rev acc
  | (i::is) =>
  if i >= mini then
    case Array.lookup fml None i of
      None => every_check_RAT_inds_arr lno fml carr np d ik mini is acc
    | Some y =>
       (check_RAT_arr lno fml carr np d ik i y ;
       every_check_RAT_inds_arr lno fml carr np d ik mini is (i::acc))
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
  rw[]>>
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
  rpt xlet_autop>>
  drule LIST_REL_LENGTH >>
  strip_tac>>
  `OPTION_TYPE (LIST_TYPE INT) (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[])>>
  xmatch>>
  xlet_auto >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    last_x_assum(qspec_then`h` assume_tac)>>rfs[any_el_ALT])
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
    case Array.lookup fml None i of
      None => every_check_PR_inds_arr lno fml carr nw d ik mini is acc
    | Some y =>
       (check_PR_arr lno fml carr nw d ik i y ;
       every_check_PR_inds_arr lno fml carr nw d ik mini is (i::acc))
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
  rw[]>>
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
  strip_tac>>
  xlet_autop>>
  `OPTION_TYPE (LIST_TYPE INT) (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[])>>
  xmatch>>
  xlet_auto >- (
    xsimpl>>
    fs[bounded_fml_def,EVERY_EL]>>
    last_x_assum(qspec_then`h` assume_tac)>>rfs[any_el_ALT])
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
             &OPTION_TYPE NUM (any_el (index (-pp)) earliest NONE) v)`
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
         &OPTION_TYPE NUM (list_min_opt NONE (MAP (λx. any_el (index x) earliest NONE) (flip x))) v)`
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

val _ = translate safe_hd_def;

val _ = translate MAX_LIST_def;
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
  rw[]>>
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
      update_earliest_arr (Array.updateResize earr None (index n) updmin) v ns
    end` |> append_prog

Theorem LIST_REL_update_resize:
  LIST_REL R a b ∧ R a1 b1 ∧ R a2 b2 ⇒
  LIST_REL R (update_resize a a1 a2 n) (update_resize b b1 b2 n)
Proof
  rw[update_resize_def]
  >- (
    match_mp_tac EVERY2_LUPDATE_same>>
    fs[])
  >- fs[LIST_REL_EL_EQN]
  >- fs[LIST_REL_EL_EQN]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[]>>
  match_mp_tac EVERY2_APPEND_suff>>
  fs[LIST_REL_EL_EQN]>>rw[]>>
  fs[EL_REPLICATE]
QED

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
    &OPTION_TYPE NUM (min_opt (SOME v) (any_el (index h) earliest NONE)) rv)`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    qexists_tac`SOME v`>>
    simp[OPTION_TYPE_def]>>
    qexists_tac`[h]`>>
    simp[LIST_TYPE_def]>>
    simp[list_min_opt_def])>>
  rpt xlet_autop>>
  rename1` nonev = _`>>
  xlet`POSTv v. ARRAY v (update_resize earliestv nonev rv (index h))`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[])>>
  xapp>> simp[]>>
  fs[min_opt_def]>>
  TOP_CASE_TAC>>fs[MIN_COMM]>>
  match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def]
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
        case Array.lookup fml None i of
          None => check_earliest_arr fml x old new is
        | Some ci =>
          not(List.member x ci) andalso check_earliest_arr fml x old new is
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
  Induct>>rw[]>>
  xcf "check_earliest_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def,check_earliest_def]
  >- (
    xmatch>>xcon>>
    xsimpl) >>
  xmatch>>
  xlet_autop>>
  reverse (Cases_on`h ≥ old`)>>fs[]
  >- (
    xif>>asm_exists_tac>>xsimpl>>
    xcon>>xsimpl>>fs[])>>
  xif>>asm_exists_tac>>fs[]>>
  xlet_autop>>
  reverse xif>>fs[]
  >- (xapp>>xsimpl)>>
  rpt xlet_autop>>
  xlet_auto>>
  `LENGTH fmlls = LENGTH fmllsv` by metis_tac[LIST_REL_LENGTH]>>
  `OPTION_TYPE (LIST_TYPE INT) (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xapp>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
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
          (case Array.lookup earr None ip of
            None => earr
          | Some mini =>
            if check_earliest_arr fml (~p) mini lm inds
            then
              Array.updateResize earr None ip (Some lm)
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
  `LENGTH earliest = LENGTH earliestv` by metis_tac[LIST_REL_LENGTH]>>
  `OPTION_TYPE NUM (any_el (index (-safe_hd c)) earliest NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >-
    (xvar>>xsimpl)>>
  rpt xlet_autop>>
  reverse xif>>fs[]
  >- (xvar>>xsimpl)>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  asm_exists_tac>>xsimpl>>
  match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def]
QED

Definition every_less_def:
  every_less (mindel:num) cls ⇔ EVERY ($< mindel) cls
End

val _ = translate every_less_def;

val check_lpr_step_arr = process_topdecs`
  fun check_lpr_step_arr lno mindel step fml ls carr earr =
  case step of
    Delete cl =>
      if every_less mindel cl then
        (list_delete_arr cl fml; (fml, ls, carr, earr))
      else
        raise Fail (format_failure lno ("Deletion not permitted for clause index <= " ^ Int.toString mindel))
  | Pr n c w i0 ik =>
    if mindel < n then
      let val p = safe_hd c
          val carr = resize_carr c carr
          val earr = hint_earliest_arr c w ik fml ls earr
          val ls = is_PR_arr lno fml ls carr earr p c w i0 ik
          val earr = update_earliest_arr earr n c in
            (Array.updateResize fml None n (Some c), sorted_insert n ls, carr, earr) end
    else
      raise Fail (format_failure lno ("Overwrite not permitted for clause index <= " ^ Int.toString mindel))
    ` |> append_prog

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
  Induct>>rw[] >>
  fs[MAX_LIST_def,MAX_DEF,index_def]>>
  rw[] >>
  intLib.ARITH_TAC
QED

Theorem bounded_fml_update_resize:
  bounded_fml m fmlls ∧
  EVERY ($> m o index) l ∧ EVERY ($> m o index o $~) l ⇒
  bounded_fml m (update_resize fmlls NONE (SOME l) n)
Proof
  rw[bounded_fml_def,EVERY_MEM]>>
  drule MEM_update_resize>>rw[]>>simp[]
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
  qmatch_goalsub_abbrev_tac`MAX_LIST lss`>>
  qspec_then `lss` assume_tac MAX_LIST_PROPERTY>>
  fs[EVERY_MEM,Abbr`lss`,MEM_MAP,PULL_EXISTS]>>
  ntac 2 strip_tac>>first_x_assum drule>>
  rw[]>>simp[index_def]>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem check_lpr_step_arr_spec:
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  LPR_LPRSTEP_TYPE step stepv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  LIST_REL (OPTION_TYPE NUM) earliest earliestv ∧
  bounded_fml (LENGTH Clist) fmlls
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lpr_step_arr" (get_ml_prog_state()))
    [lnov; mindelv; stepv; fmlv; lsv; Carrv; Earrv]
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
                (check_lpr_step_list mindel step fmlls ls Clist earliest) fmllsv' ∧
            unwrap_TYPE ($= o FST o SND o SND) (check_lpr_step_list mindel step fmlls ls Clist earliest) Clist' ∧
            unwrap_TYPE (LIST_REL (OPTION_TYPE NUM) o SND o SND o SND) (check_lpr_step_list mindel step fmlls ls Clist earliest) earliestv' ∧
            LENGTH Clist ≤ LENGTH Clist'
            ))
        * (* v2 is the indexing list *)
          &unwrap_TYPE (λa b. LIST_TYPE NUM (FST (SND a)) b) (check_lpr_step_list mindel step fmlls ls Clist earliest) v2
      )
      (λe. ARRAY fmlv fmllsv * (SEP_EXISTS Earrv earliestv. ARRAY Earrv earliestv) * &(Fail_exn e ∧ check_lpr_step_list mindel step fmlls ls Clist earliest = NONE)))
Proof
  rw[check_lpr_step_list_def]>>
  xcf "check_lpr_step_arr" (get_ml_prog_state ())>>
  TOP_CASE_TAC>>fs[LPR_LPRSTEP_TYPE_def]
  >- (
    xmatch>>
    xlet_autop >>
    xif
    >- (
      xlet_autop>>
      xcon >> xsimpl>>
      simp[unwrap_TYPE_def]>>
      fs[every_less_def]>>
      metis_tac[bounded_fml_list_delete_list,NOT_EVERY])
    >>
      rpt xlet_autop>>
      xraise>>xsimpl>> simp[unwrap_TYPE_def,Fail_exn_def]>>
      fs[every_less_def]>>
      CONJ_TAC >- (
        qexists_tac`Earrv`>>
        qexists_tac`earliestv`>>
        xsimpl>>metis_tac[])>>
      metis_tac[NOT_EVERY]) >>
  xmatch>>
  xlet_autop>>
  reverse xif
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>> simp[unwrap_TYPE_def,Fail_exn_def]>>
    every_case_tac>>simp[]>>
    qexists_tac`Earrv`>>
    qexists_tac`earliestv`>>
    xsimpl>>metis_tac[])>>
  rpt(xlet_autop)>>
  xlet_auto
  >- (xsimpl>>
    metis_tac[bounded_fml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist])
  >- (xsimpl>> rw[] >> simp[] >>
    qexists_tac`Earrv'`>> qexists_tac`earliestv'`>>
    xsimpl)>>
  fs[unwrap_TYPE_def]>>
  TOP_CASE_TAC>>fs[]>>
  rpt xlet_autop>>
  xcon>>xsimpl>>
  simp[OPTION_TYPE_def,LIST_TYPE_def]>>rw[]
  >- (
    fs[]>>
    metis_tac[bounded_fml_update_resize,bounded_fml_leq,LENGTH_resize_Clist,EVERY_index_resize_Clist])
  >-
    (match_mp_tac LIST_REL_update_resize>>simp[OPTION_TYPE_def])>>
  fs[]>>
  metis_tac[LENGTH_resize_Clist]
QED

(* A version of contains_clauses_list that returns an error clause (if any) *)
Definition contains_clauses_list_err_def:
  contains_clauses_list_err fml inds cls =
  case reindex fml inds of
    (_,inds') =>
  let inds'' = MAP canon_clause inds' in
  oHD (FILTER (λcl. ¬MEM (canon_clause cl) inds'') cls)
End

Theorem contains_clauses_list_err:
  contains_clauses_list fml inds cls ⇔
  ¬IS_SOME (contains_clauses_list_err fml inds cls)
Proof
  simp[contains_clauses_list_def,contains_clauses_list_err_def]>>
  TOP_CASE_TAC>>simp[]>>
  pop_assum kall_tac>>
  simp[oHD_def,option_CLAUSES]>>
  every_case_tac>>fs[FILTER_EQ_NIL]>>
  CCONTR_TAC>>
  imp_res_tac LENGTH_FILTER_EXISTS >>
  fs[o_DEF]
QED

(* SOME cls indicates failure to detect clause cls *)
Definition contains_clauses_sing_list_def:
  (contains_clauses_sing_list fml [] cls ccls = SOME cls) ∧
  (contains_clauses_sing_list fml (i::is) cls ccls =
  case any_el i fml NONE of
    NONE => contains_clauses_sing_list fml is cls ccls
  | SOME v =>
    if canon_clause v = ccls then NONE
    else contains_clauses_sing_list fml is cls ccls)
End

Theorem contains_clauses_sing_list_eq:
  ∀inds fml cls.
  contains_clauses_sing_list fml inds cls (canon_clause cls) =
  contains_clauses_list_err fml inds [cls]
Proof
  simp[contains_clauses_list_err_def]>>
  Induct>>rw[contains_clauses_sing_list_def,reindex_def]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  pairarg_tac>>fs[]>>
  rw[] >> fs[]
QED

val _ = translate sorted_dup_def;
val _ = translate canon_clause_def;

(* Optimized combination of reindex and contains_clauses
  for checking that a single clause
  is contained in the formula (usually cls is the empty clause []) *)
val contains_clauses_sing_arr =  (append_prog o process_topdecs)`
  fun contains_clauses_sing_arr fml ls cls ccls =
  case ls of
    [] => Some cls
  | (i::is) =>
  case Array.lookup fml None i of
    None => contains_clauses_sing_arr fml is cls ccls
  | Some v =>
    if canon_clause v = ccls then None
    else contains_clauses_sing_arr fml is cls ccls`

Theorem contains_clauses_sing_arr_spec:
  ∀ls lsv fmlv fmlls fmllsv cls clsv ccls cclsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  (LIST_TYPE INT) cls clsv ∧
  (LIST_TYPE INT) ccls cclsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "contains_clauses_sing_arr" (get_ml_prog_state()))
    [fmlv; lsv; clsv; cclsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(OPTION_TYPE (LIST_TYPE INT) (contains_clauses_sing_list fmlls ls cls ccls) resv) *
      ARRAY fmlv fmllsv)
Proof
  Induct>>rw[contains_clauses_sing_list_def]>>
  xcf "contains_clauses_sing_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>> rpt(xlet_autop)>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def])>>
  xmatch>> rpt(xlet_autop)>>
  xlet_auto>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  `OPTION_TYPE (LIST_TYPE INT) (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (xapp>>xsimpl)>>
  rpt xlet_autop>>
  xif>- (
    xcon>>
    xsimpl>>simp[OPTION_TYPE_def])>>
  xapp>>
  simp[]
QED

val hash_ins = (append_prog o process_topdecs)`
  fun hash_ins ht k v =
  case Hashtable.lookup ht k of
    None => Hashtable.insert ht k [v]
  | Some ls => Hashtable.insert ht k (v::ls)`

(* reindex that creates a hash table of the values
  canon flag decides whether to canonicalize clauses along the way *)
val reindex_hash = (append_prog o process_topdecs)`
  fun reindex_hash fml canon ls ht =
  case ls of
    [] => ()
  | (i::is) =>
  case Array.lookup fml None i of
    None => reindex_hash fml canon is ht
  | Some v =>
    (hash_ins ht (if canon then canon_clause v else v) i;
    reindex_hash fml canon is ht)`

(* badly named, but hash_contains returns an option with the first clause it fails to find *)
val hash_contains = (append_prog o process_topdecs)`
  fun hash_contains hash clss =
  case clss of
    [] => None
  | (i::is) =>
  (case Hashtable.lookup hash (canon_clause i) of
    None => Some i
  | Some u =>
    hash_contains hash is)`

(* Magic number 7 for base of rolling hash *)
Definition hash_func_def:
  (hash_func [] = 0n) ∧
  (hash_func (i::is) =
    index i + 7 * (hash_func is))
End

Definition order_lists_def:
  (order_lists [] [] = Equal) ∧
  (order_lists [] (y::ys) = Less) ∧
  (order_lists (x::xs) [] = Greater) ∧
  (order_lists (x::xs) (y::ys) =
    if (x:int) < y then Less
    else if x > y then Greater else order_lists xs ys)
End

val _ = translate hash_func_def;
val _ = translate order_lists_def;

val contains_clauses_arr =  (append_prog o process_topdecs)`
  fun contains_clauses_arr fml ls cls =
  case cls of
    [] => None
  | [cl] => contains_clauses_sing_arr fml ls cl (canon_clause cl)
  | clss =>
    let
      val ht = Hashtable.empty (2 * List.length ls) hash_func order_lists
      val u1 = reindex_hash fml True ls ht
    in
      hash_contains ht clss
    end`

val order_lists_ind = fetch "-" "order_lists_ind";

Theorem order_lists_refl:
  ∀x y.
  order_lists x y = Equal ⇔ x = y
Proof
  ho_match_mp_tac order_lists_ind>>
  rw[order_lists_def]>>
  fs[]
  >- (
    CCONTR_TAC>>
    pop_assum kall_tac>>
    intLib.ARITH_TAC)>>
  `x=y` by
    intLib.COOPER_TAC>>
  simp[]
QED

Theorem order_lists_flip:
  ∀x y.
  order_lists x y = Less ⇔ order_lists y x = Greater
Proof
  ho_match_mp_tac order_lists_ind>>
  rw[order_lists_def]>>
  TRY(intLib.ARITH_TAC)>>
  CCONTR_TAC>>pop_assum kall_tac>>
  intLib.ARITH_TAC
QED

Theorem order_lists_trans:
  ∀x z y.
  order_lists x y = Less ∧ order_lists y z = Less ⇒
  order_lists x z = Less
Proof
  ho_match_mp_tac order_lists_ind>>
  rw[order_lists_def]
  >- (Cases_on`y`>>fs[order_lists_def])
  >- (Cases_on`y`>>fs[order_lists_def])
  >- (
    Cases_on`y'`>>fs[order_lists_def]>>
    every_case_tac>>fs[]>>
    TRY(intLib.ARITH_TAC)>>
    CCONTR_TAC>>pop_assum kall_tac>>
    intLib.ARITH_TAC)
  >- (
    Cases_on`y'`>>fs[order_lists_def]>>
    `x=y` by intLib.ARITH_TAC>>
    rw[]>>
    every_case_tac>>fs[]>>
    TRY( CCONTR_TAC>>pop_assum kall_tac>>
    intLib.ARITH_TAC)>>
    metis_tac[])
QED

Theorem order_lists_TotOrd:
  TotOrd order_lists
Proof
  simp[totoTheory.TotOrd]>>
  metis_tac[order_lists_refl,order_lists_trans,order_lists_flip]
QED

Theorem hash_ins_spec:
  (LIST_TYPE INT) k kv ∧
  NUM v vv ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "hash_ins" (get_ml_prog_state()))
    [hv; kv; vv]
    (HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h hv)
    (POSTv uv.
      &(UNIT_TYPE () uv) *
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
       (hash_insert h k v) hv)
Proof
  rw[hash_insert_def]>>
  xcf "hash_ins" (get_ml_prog_state ())>>
  xlet_auto
  >-
    (qexists_tac`emp`>>qexists_tac`h`>>xsimpl)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >- (
    rpt xlet_autop>>
    xapp>>xsimpl>>
    simp[LIST_TYPE_def])>>
  xlet_autop>>
  xapp>>
  simp[LIST_TYPE_def]
QED

Theorem reindex_hash_spec:
  ∀ls lsv h hv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv ∧
  BOOL canon canonv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_hash" (get_ml_prog_state()))
    [fmlv; canonv; lsv; hv]
    (HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h hv * ARRAY fmlv fmllsv)
    (POSTv uv.
      &(UNIT_TYPE () uv) *
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
       ((λ(xs,ys). hash_clauses_aux (if canon then MAP canon_clause ys else ys) xs) (reindex fmlls ls) h) hv *
      ARRAY fmlv fmllsv)
Proof
  Induct>>rw[reindex_def]>>
  xcf "reindex_hash" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>xvar>>
    simp[hash_clauses_aux_def]>>
    xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  `LENGTH fmlls = LENGTH fmllsv` by
    metis_tac[LIST_REL_LENGTH]>>
  `OPTION_TYPE (LIST_TYPE INT) (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  Cases_on`any_el h fmlls NONE` >>fs[OPTION_TYPE_def]>>
  xmatch
  >- (
    xapp>> xsimpl>>
    qexists_tac`emp`>>qexists_tac`h'`>>xsimpl)>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  xlet`POSTv v. &(LIST_TYPE INT (if canon then canon_clause x else x) v) * ARRAY fmlv fmllsv *
           HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h' hv`
  >- (
    IF_CASES_TAC>>xif>>asm_exists_tac>>fs[]
    >- (
      xapp>> xsimpl>> asm_exists_tac>>
      metis_tac[])>>
    xvar>>xsimpl)>>
  xlet`POSTv uv. &UNIT_TYPE () uv *
    HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
      (hash_insert h' (if canon then canon_clause x else x) h) hv * ARRAY fmlv fmllsv`
  >- (
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>qexists_tac`h'`>>xsimpl)>>
  xapp>>xsimpl>>
  rw[]>>simp[hash_clauses_aux_def]
  >- (
    qexists_tac`emp`>>qexists_tac`(hash_insert h' (canon_clause x) h)`>>
    xsimpl)>>
  qexists_tac`emp`>>qexists_tac`(hash_insert h' x h)`>>
  xsimpl
QED

Theorem hash_contains_spec:
  ∀cls clsv h hv.
  LIST_TYPE (LIST_TYPE INT) cls clsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "hash_contains" (get_ml_prog_state()))
    [hv; clsv]
    (HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists h hv)
    (POSTv bv.
      &(OPTION_TYPE (LIST_TYPE INT)
        (oHD (FILTER (λcl. canon_clause cl ∉ FDOM h) cls))
    bv))
Proof
  Induct>>rw[]>>
  xcf "hash_contains" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    simp[OPTION_TYPE_def])
  >- (
    xmatch>>
    xlet_autop>>
    xlet_auto
    >- (qexists_tac`emp`>> xsimpl)>>
    Cases_on`FLOOKUP h' (canon_clause h)`>>fs[FDOM_FLOOKUP,OPTION_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl)>>
  xmatch>>
  xlet_autop>>
  xlet_auto
  >- (qexists_tac`emp`>> xsimpl)>>
  Cases_on`FLOOKUP h' (canon_clause h)`>>fs[FDOM_FLOOKUP,OPTION_TYPE_def]>>
  xmatch>>
  xapp>>
  fs[]
QED

Theorem FDOM_hash_clauses_aux:
  ∀xs ys h.
  LENGTH xs = LENGTH ys ⇒
  FDOM (hash_clauses_aux xs ys h) = set xs ∪ FDOM h
Proof
  Induct>>rw[hash_clauses_aux_def]>>
  Cases_on`ys`>>fs[hash_clauses_aux_def]>>
  simp[hash_insert_def]>>
  every_case_tac>>fs[EXTENSION]>>
  metis_tac[]
QED

Theorem contains_clauses_arr_spec:
  (LIST_TYPE (LIST_TYPE INT)) cls clsv ∧
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE (LIST_TYPE INT)) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "contains_clauses_arr" (get_ml_prog_state()))
    [fmlv; lsv; clsv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &(OPTION_TYPE (LIST_TYPE INT) (contains_clauses_list_err fmlls ls cls) resv) *
      ARRAY fmlv fmllsv)
Proof
  rw[contains_clauses_list_err_def]>>
  xcf "contains_clauses_arr" (get_ml_prog_state ())>>
  Cases_on`cls`>>fs[LIST_TYPE_def]
  >- (
    xmatch>> xcon>>
    xsimpl>> every_case_tac>>simp[OPTION_TYPE_def])>>
  Cases_on`t`>>fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xapp>>xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    rw[]>>every_case_tac>>fs[contains_clauses_sing_list_eq,contains_clauses_list_err_def])>>
  xmatch>>
  rpt xlet_autop>>
  xlet`POSTv v. HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists FEMPTY v * ARRAY fmlv fmllsv`
  >- (
    xapp_spec (HashtableProofTheory.hashtable_empty_spec|>INST_TYPE[alpha|->``:int list``,beta |-> ``:num list``])>>
    assume_tac order_lists_TotOrd>>
    asm_exists_tac>>simp[]>>
    simp[PULL_EXISTS]>>
    asm_exists_tac>>simp[]>>
    assume_tac (theorem "order_lists_v_thm")>>
    asm_exists_tac>>simp[]>>
    qexists_tac`ARRAY fmlv fmllsv`>>xsimpl>>
    qexists_tac`hash_func`>>
    qexists_tac`LIST_TYPE NUM`>>xsimpl>>
    simp[theorem "hash_func_v_thm"])>>
  xlet_autop>>
  xlet`(POSTv uv.
      &(UNIT_TYPE () uv) *
      HASHTABLE (LIST_TYPE INT) (LIST_TYPE NUM) hash_func order_lists
       ((λ(xs,ys). hash_clauses_aux (MAP canon_clause ys) xs) (reindex fmlls ls) FEMPTY) v *
      ARRAY fmlv fmllsv)`
  >- (
    xapp>>xsimpl>>
    qexists_tac`emp`>>xsimpl>>
    `BOOL T (Conv (SOME (TypeStamp «True» 0)) [])` by EVAL_TAC>>
    rpt (asm_exists_tac>>simp[])>>
    qexists_tac`FEMPTY`>>xsimpl)>>
  xapp>>
  qexists_tac`ARRAY fmlv fmllsv`>>xsimpl>>
  qmatch_goalsub_abbrev_tac` _ _ _ _ _ hh v` >>
  qexists_tac`hh`>>
  xsimpl>>
  qexists_tac`h::h'::t'`>>simp[LIST_TYPE_def]>>
  simp[Abbr`hh`]>>
  Cases_on`reindex fmlls ls`>>
  simp[]>>
  DEP_REWRITE_TAC[FDOM_hash_clauses_aux]>>
  simp[EVERY_MEM,SUBSET_DEF]>>
  drule reindex_characterize>>fs[]>>
  simp[MEM_MAP]
QED
