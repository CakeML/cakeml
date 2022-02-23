(*
  Refine pb_list to pb_array
*)
open preamble basis pb_listTheory;

val _ = new_theory "pb_array"

val _ = translation_extends"basisProg";

val xlet_autop = xlet_auto >- (TRY( xcon) >> xsimpl)

val _ = process_topdecs `
  exception Fail string;
` |> append_prog

fun get_exn_conv name =
  EVAL ``lookup_cons (Short ^name) ^(get_env (get_ml_prog_state ()))``
  |> concl |> rand |> rand |> rand

val fail = get_exn_conv ``"Fail"``

val Fail_exn_def = Define `
  Fail_exn v = (∃s sv. v = Conv (SOME ^fail) [sv] ∧ STRING_TYPE s sv)`

val _ = register_type ``:constr``
val _ = register_type ``:pbpstep ``
val _ = register_type ``:'a pbpres``

val format_failure_def = Define`
  format_failure (lno:num) s =
  strlit "c Checking failed at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val r = translate format_failure_def;

(* Implements list_lookup... probably name it something better *)
val lookup_arr = process_topdecs`
  fun lookup_arr arr default n =
  if n < Array.length arr then
    Array.sub arr n
  else
    default` |> append_prog

Theorem lookup_arr_spec:
  ty default defaultv ∧
  NUM n nv ∧
  LIST_REL ty ls arrlsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "lookup_arr" (get_ml_prog_state()))
    [arrv; defaultv; nv]
    (ARRAY arrv arrlsv)
    (POSTv v.
      ARRAY arrv arrlsv *
      &(ty (list_lookup ls default n) v))
Proof
  xcf "lookup_arr" (get_ml_prog_state ())>>
  xlet_autop>>
  xlet_autop>>
  imp_res_tac LIST_REL_LENGTH>>
  rw[list_lookup_def]>>
  xif>>fs[]>>asm_exists_tac>>simp[]
  >- (
    xapp>>xsimpl>>
    metis_tac[LIST_REL_EL_EQN])>>
  xvar>>
  xsimpl
QED

val check_cutting_arr = process_topdecs`
  fun check_cutting_arr lno fml constr =
  case constr of
    Id n =>
    (case lookup_arr fml None n of
      None =>
        raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some c => c)` |> append_prog

val PB_CHECK_CONSTR_TYPE_def = fetch "-" "PB_CHECK_CONSTR_TYPE_def";

val PB_CONSTRAINT_NPBC_TYPE_def  = theorem "PB_CONSTRAINT_NPBC_TYPE_def"

Theorem check_cutting_arr_spec:
  PB_CHECK_CONSTR_TYPE constr constrv ∧
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cutting_arr" (get_ml_prog_state()))
    [lnov; fmlv; constrv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case check_cutting_list fmlls constr of NONE => F
          | SOME x => PB_CONSTRAINT_NPBC_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (check_cutting_list fmlls constr = NONE)))
Proof
  xcf"check_cutting_arr"(get_ml_prog_state ())>>
  rpt (pop_assum mp_tac)>>
  qid_spec_tac`constrv`>>
  Induct_on`constr`
  >- ( (* Id *)
    rw[check_cutting_list_def]>>
    fs[PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet`POSTv v.
      ARRAY fmlv fmllsv *
      &(OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (list_lookup fmlls NONE n) v)`
    >- (
      assume_tac (lookup_arr_spec |> Q.GEN`ty` |> Q.ISPEC`OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE` |> GEN_ALL)>>
      xapp>>
      simp[OPTION_TYPE_def])>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl)>>
    xvar>>xsimpl)>>
  cheat
QED

val result = translate sorted_insert_def;

val check_pbpstep_arr = process_topdecs`
  fun check_pbpstep_arr lno step fml inds id =
  case step of
    Cutting constr =>
    let val c = check_cutting_arr lno fml constr in
      (Cont () (id+1), fml, sorted_insert id inds)
    end
  and check_pbpsteps_arr lno steps fml inds id =
  case steps of
    [] => (Cont () id, fml, inds)` |> append_prog

val PB_CHECK_PBPSTEP_TYPE_def = theorem "PB_CHECK_PBPSTEP_TYPE_def";

Theorem check_pbpstep_arr_spec:
  (∀step fmlls inds id stepv lno lnov idv indsv fmlv fmllsv.
  PB_CHECK_PBPSTEP_TYPE step stepv ∧
  NUM lno lnov ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_pbpstep_arr" (get_ml_prog_state()))
    [lnov; stepv; fmlv; indsv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(case check_pbpstep_list step fmlls inds id of
          (Fail,_) => F
        | res => T
          (* TODO relate the results ... *)
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (FST (check_pbpstep_list step fmlls inds id) = Fail)))) ∧
  (∀steps fmlls inds id stepsv lno lnov idv indsv fmlv fmllsv.
  LIST_TYPE PB_CHECK_PBPSTEP_TYPE steps stepsv ∧
  NUM lno lnov ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_pbpsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; fmlv; indsv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(case check_pbpsteps_list steps fmlls inds id of
          (Fail,_) => F
          (* TODO relate the results ... *)
        | res => T))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (FST(check_pbpsteps_list steps fmlls inds id) = Fail))))
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]>>fs[]
  >- (
    xcfs ["check_pbpstep_arr","check_pbpsteps_arr"] (get_ml_prog_state ())>>
    simp[Once check_pbpstep_list_def]>>
    Cases_on`step`
    >- (* Contradiction *) cheat
    >- (* Delete *) cheat
    >-  ((* Cutting *)
      fs[PB_CHECK_PBPSTEP_TYPE_def]>>
      xmatch>>
      xlet_auto
      >- (
        xsimpl>>
        simp[check_pbpstep_list_def]>>
        rw[]>>qexists_tac`fmlv`>>qexists_tac`fmllsv`>>
        xsimpl)>>
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        every_case_tac>>fs[]>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>
        xsimpl)>>
      simp[check_pbpstep_list_def]>>
      every_case_tac>>fs[])>>
    cheat)>>
  cheat
QED

val _ = export_theory();
