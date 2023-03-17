(*
  Refine npbc_list to npbc_array
*)
open preamble basis npbcTheory npbc_listTheory;

val _ = new_theory "npbc_arrayProg"

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
val _ = register_type ``:lstep ``
val _ = register_type ``:sstep ``

val format_failure_def = Define`
  format_failure (lno:num) s =
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val r = translate format_failure_def;

val r = translate OPTION_MAP2_DEF;

(* Translate steps in check_cutting *)
val r = translate listTheory.REV_DEF;
val r = translate offset_def;
val r = translate add_terms_def;
val r = translate add_lists'_def;
val r = translate add_lists'_thm;
val r = translate add_def;

val r = translate multiply_def;

val r = translate IQ_def;
val r = translate div_ceiling_def;
val r = translate arithmeticTheory.CEILING_DIV_def ;
val r = translate divide_def;

val divide_side = Q.prove(
  `∀x y. divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  intLib.ARITH_TAC
  ) |> update_precondition

val r = translate abs_min_def;
val r = translate saturate_def;

val r = translate weaken_aux_def;
val r = translate weaken_def;

val check_cutting_arr = process_topdecs`
  fun check_cutting_arr lno fml constr =
  case constr of
    Id n =>
    (case Array.lookup fml None n of
      None =>
        raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some c => c)
  | Add c1 c2 =>
    add (check_cutting_arr lno fml c1) (check_cutting_arr lno fml c2)
  | Mul c k =>
    multiply (check_cutting_arr lno fml c) k
  | Div_1 c k =>
    if k <> 0 then
      divide (check_cutting_arr lno fml c) k
    else raise Fail (format_failure lno ("divide by zero"))
  | Sat c =>
    saturate (check_cutting_arr lno fml c)
  | Lit l =>
    (case l of
      Pos v => ([(1,v)], 0)
    | Neg v => ([(~1,v)], 0))
  | Weak c var =>
    weaken (check_cutting_arr lno fml c) var` |> append_prog

Definition constraint_TYPE_def:
  constraint_TYPE = PAIR_TYPE
    (LIST_TYPE (PAIR_TYPE INT NUM))
    NUM
End

val NPBC_CHECK_CONSTR_TYPE_def = fetch "-" "NPBC_CHECK_CONSTR_TYPE_def";
val PBC_LIT_TYPE_def = fetch "-" "PBC_LIT_TYPE_def"

Theorem check_cutting_arr_spec:
  ∀constr constrv lno lnov fmlls fmllsv fmlv.
  NPBC_CHECK_CONSTR_TYPE constr constrv ∧
  NUM lno lnov ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cutting_arr" (get_ml_prog_state()))
    [lnov; fmlv; constrv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
      ARRAY fmlv fmllsv *
        &(case check_cutting_list fmlls constr of NONE => F
          | SOME x => constraint_TYPE x v))
      (λe.
      ARRAY fmlv fmllsv *
        & (Fail_exn e ∧ check_cutting_list fmlls constr = NONE)))
Proof
  Induct_on`constr` >> rw[]>>
  xcf "check_cutting_arr" (get_ml_prog_state ())
  >- ( (* Id *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet_auto>>
    `OPTION_TYPE constraint_TYPE (any_el n fmlls NONE) v'` by (
      rw[any_el_ALT]>>
      fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    qpat_x_assum`v' = _` (assume_tac o SYM)>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def])>>
    xvar>>xsimpl)
  >- ( (* Add *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    fs[constraint_TYPE_def]>>
    metis_tac[])
  >- ( (* Mul *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    fs[constraint_TYPE_def]>>
    metis_tac[])
  >- ( (* Div *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    reverse IF_CASES_TAC>>xif>>asm_exists_tac>>fs[]
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>metis_tac[])>>
    xlet_autop>- xsimpl>>
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    fs[constraint_TYPE_def]>>
    metis_tac[])
  >- ( (* Sat *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp_spec
    (fetch "-" "saturate_v_thm" |> INST_TYPE [alpha|->``:num``])>>
    xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    fs[constraint_TYPE_def]>>
    metis_tac[])
  >- ( (* Lit *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    Cases_on`l`>>
    fs[PBC_LIT_TYPE_def]>>xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[constraint_TYPE_def,LIST_TYPE_def,PAIR_TYPE_def])
  >> ( (* Weak *)
    fs[check_cutting_list_def,NPBC_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp_spec
    (fetch "-" "weaken_v_thm" |> INST_TYPE [alpha|->``:num``])>>
    xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    first_x_assum (irule_at Any)>>fs[constraint_TYPE_def]>>
    metis_tac[EqualityType_NUM_BOOL])
QED

(* Translation for pb checking *)

val r = translate (lslack_def |> SIMP_RULE std_ss [MEMBER_INTRO, o_DEF]);
val r = translate (check_contradiction_def |> SIMP_RULE std_ss[LET_DEF]);

(* TODO:  can use Unsafe.update instead of Array.update *)
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
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_delete_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE constraint_TYPE) (list_delete_list ls fmlls) fmllsv') )
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

val every_less_def = Define`
  every_less (mindel:num) core cls ⇔
  EVERY (λid. mindel ≤ id ∧ lookup id core = NONE) cls`

val res = translate lookup_def;

val _ = translate every_less_def;

Definition mk_ids_def:
  mk_ids id_start (id_end:num) =
  if id_start < id_end then id_start::mk_ids (id_start+1) id_end else []
Termination
  WF_REL_TAC `measure (λ(a,b). b-a)`
End

val _ = translate mk_ids_def;

val rollback_arr = process_topdecs`
  fun rollback_arr fml id_start id_end =
  list_delete_arr (mk_ids id_start id_end) fml` |> append_prog

Theorem mk_ids_MAP_COUNT_LIST:
  ∀start end.
  mk_ids start end =
  MAP ($+ start) (COUNT_LIST (end − start))
Proof
  ho_match_mp_tac mk_ids_ind>>rw[]>>
  simp[Once mk_ids_def]>>rw[]>>gs[]>>
  Cases_on`end-start`>>fs[COUNT_LIST_def]>>
  `end-(start+1) = n` by fs[]>>
  simp[MAP_MAP_o,MAP_EQ_f]
QED

Theorem rollback_arr_spec:
  NUM start startv ∧
  NUM end endv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rollback_arr" (get_ml_prog_state()))
    [fmlv;startv; endv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE constraint_TYPE) (rollback fmlls start end) fmllsv') )
Proof
  xcf"rollback_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xapp>>
  asm_exists_tac>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  rw[]>>fs[rollback_def]>>
  metis_tac[mk_ids_MAP_COUNT_LIST]
QED

val res = translate not_def;
val res = translate sorted_insert_def;

val check_contradiction_fml_arr = process_topdecs`
  fun check_contradiction_fml_arr fml n =
  case Array.lookup fml None n of
    None => False
  | Some c => check_contradiction c
` |> append_prog

Theorem check_contradiction_fml_arr_spec:
  NUM n nv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_contradiction_fml_arr" (get_ml_prog_state()))
    [fmlv; nv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
        ARRAY fmlv fmllsv *
        &(
        BOOL (check_contradiction_fml_list fmlls n) v))
Proof
  rw[check_contradiction_fml_list_def]>>
  xcf"check_contradiction_fml_arr"(get_ml_prog_state ())>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el n fmlls NONE) v'` by (
     rw[any_el_ALT]>>
     fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
  xmatch
  >- (xcon>>xsimpl)>>
  xapp>>xsimpl>>
  metis_tac[constraint_TYPE_def]
QED

(* TODO: copied *)
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

val check_lstep_arr = process_topdecs`
  fun check_lstep_arr lno step core fml inds mindel id =
  case step of
    Check n c =>
    (case Array.lookup fml None n of
      None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some c' =>
      if c = c' then (fml, (id, inds))
      else raise Fail (format_failure lno ("constraint id check failed")))
  | Noop => (fml, (id, inds))
  | Delete ls =>
      if every_less mindel core ls then
        (list_delete_arr ls fml; (fml, (id, inds)))
      else
        raise Fail (format_failure lno ("Deletion not permitted for core constraints and constraint index < " ^ Int.toString mindel))
  | Cutting constr =>
    let val c = check_cutting_arr lno fml constr
        val fml' = Array.updateResize fml None id (Some c) in
      (fml', (id+1,sorted_insert id inds))
    end
  | Con c pf n =>
    let val fml_not_c = Array.updateResize fml None id (Some (not_1 c)) in
      (case check_lsteps_arr lno pf core fml_not_c (sorted_insert id inds) id (id+1) of
        (fml', (id' ,inds')) =>
          if check_contradiction_fml_arr fml' n then
            let val u = rollback_arr fml' id id' in
              (Array.updateResize fml' None id' (Some c), ((id'+1), sorted_insert id' inds))
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n)))
    end
  | _ => raise Fail (format_failure lno ("Proof step not supported"))
  and check_lsteps_arr lno steps core fml inds mindel id =
  case steps of
    [] => (fml, (id, inds))
  | s::ss =>
    case check_lstep_arr lno s core fml inds mindel id of
      (fml', (id', inds')) =>
        check_lsteps_arr lno ss core fml' inds' mindel id'
` |> append_prog

val NPBC_CHECK_LSTEP_TYPE_def = fetch "-" "NPBC_CHECK_LSTEP_TYPE_def"

Theorem ARRAY_refl:
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv) ∧
  (ARRAY fml fmllsv ==>> ARRAY fml fmllsv * GC)
Proof
  xsimpl
QED

Theorem check_lstep_arr_spec_aux:
  (∀step core fmlls inds mindel id stepv lno lnov idv indsv fmlv fmllsv mindelv corev.
  NPBC_CHECK_LSTEP_TYPE step stepv ∧
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lstep_arr" (get_ml_prog_state()))
    [lnov; stepv; corev; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lstep_list step core fmlls inds mindel id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE NUM (LIST_TYPE NUM)) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
        check_lstep_list step core fmlls inds mindel id = NONE)))) ∧
  (∀steps core fmlls inds mindel id stepsv lno lnov idv indsv fmlv fmllsv mindelv corev.
  LIST_TYPE NPBC_CHECK_LSTEP_TYPE steps stepsv ∧
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_lsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; corev; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_lsteps_list steps core fmlls inds mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE NUM (LIST_TYPE NUM)) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧ check_lsteps_list steps core fmlls inds mindel id = NONE))))
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]>>fs[]
  >- (
    xcfs ["check_lstep_arr","check_lsteps_arr"] (get_ml_prog_state ())>>
    simp[Once check_lstep_list_def]>>
    Cases_on`step`
    >- ( (* Delete *)
      fs[NPBC_CHECK_LSTEP_TYPE_def]>>
      xmatch>>
      xlet_auto
      >- (
        xsimpl>>
        simp[ml_translatorTheory.EqualityType_NUM_BOOL])>>
      fs[every_less_def]>>
      reverse IF_CASES_TAC >>
      gs[]>>xif>>
      asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_lstep_list_def]>>
        xraise>>xsimpl>>
        simp[Fail_exn_def]>>
        metis_tac[ARRAY_refl])>>
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      simp[check_lstep_list_def])
    >- ((* Cutting *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      xlet_auto >- (
        xsimpl>>
        metis_tac[ARRAY_refl])>>
      rpt xlet_autop>>
      xlet_auto >>
      rpt xlet_autop>>
      every_case_tac>>fs[]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ lss`>>
      qexists_tac`lss`>>xsimpl>>
      simp[Abbr`lss`]>>
      match_mp_tac LIST_REL_update_resize>>simp[]>>
      fs[constraint_TYPE_def]>>
      EVAL_TAC>>
      metis_tac[])
    >- ( (* Con *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet_auto>>
      rpt xlet_autop>>
      (* for some reason xapp doesn't work?? *)
      first_x_assum drule>>
      qpat_x_assum`NUM lno lnov` assume_tac>>
      rpt(disch_then drule)>>
      `LIST_REL (OPTION_TYPE constraint_TYPE)
        (update_resize fmlls NONE (SOME (not p')) id)
        (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
                (Conv (SOME (TypeStamp "Some" 2)) [v]) id)` by
        (
        match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def]>>
        fs[constraint_TYPE_def])>>
      disch_then drule>>
      disch_then drule>>
      strip_tac>>
      xlet_auto >- xsimpl
      >- (
        xsimpl>>
        metis_tac[ARRAY_refl])>>
      pop_assum mp_tac>> TOP_CASE_TAC>>
      fs[]>>
      PairCases_on`x`>>fs[PAIR_TYPE_def]>>
      rw[]
      >- (
        (* successful contradiciton *)
        xmatch>>
        rpt xlet_autop>>
        xif>>asm_exists_tac>>xsimpl>>
        rpt xlet_autop>>
        xlet_auto>>
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        qmatch_goalsub_abbrev_tac`ARRAY _ ls`>>
        qexists_tac`ls`>>xsimpl>>
        simp[Abbr`ls`]>>
        match_mp_tac LIST_REL_update_resize>>
        simp[OPTION_TYPE_def]>>
        fs[constraint_TYPE_def])>>
      xmatch>>
      rpt xlet_autop>>
      xif>>asm_exists_tac>>xsimpl>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])
    >- ( (* Check *)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet_auto>>
      `OPTION_TYPE constraint_TYPE (any_el n fmlls NONE) v'` by (
         rw[any_el_ALT]>>
         fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
      qpat_x_assum`v' = _` (assume_tac o SYM)>>
      Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]>>
      xmatch
      >- (
        rpt xlet_autop>>
        xraise>> xsimpl>>
        metis_tac[Fail_exn_def,ARRAY_refl]) >>
      fs[constraint_TYPE_def]>>
      xlet_autop>>
      xif>>rpt xlet_autop
      >- (
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      xraise>>
      xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])
    >- ( (*No Op*)
      fs[NPBC_CHECK_LSTEP_TYPE_def,check_lstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl))
  >- (
    xcfs ["check_lstep_arr","check_lsteps_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    simp[Once check_lstep_list_def]>>
    xcon>>xsimpl
    >- (
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl)>>
    simp[Once check_lstep_list_def])
  >- (
    xcfs ["check_lstep_arr","check_lsteps_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop
    >- (
      xsimpl>>
      rw[]>>simp[Once check_lstep_list_def]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    xmatch>>
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    rw[]>>simp[Once check_lstep_list_def]
    >- (
      every_case_tac>>fs[]>>asm_exists_tac>>
      xsimpl)>>
    metis_tac[ARRAY_refl])
QED

Theorem check_lstep_arr_spec = CONJUNCT1 check_lstep_arr_spec_aux
Theorem check_lsteps_arr_spec = CONJUNCT2 check_lstep_arr_spec_aux

val reindex_aux_arr = process_topdecs `
  fun reindex_aux_arr fml ls iacc vacc =
  case ls of
    [] => (List.rev iacc, vacc)
  | (i::is) =>
  case Array.lookup fml None i of
    None => reindex_aux_arr fml is iacc vacc
  | Some v =>
    (reindex_aux_arr fml is (i::iacc) (v::vacc))` |> append_prog;

val reindex_arr = process_topdecs `
  fun reindex_arr fml is = reindex_aux_arr fml is [] []`
  |> append_prog;

Theorem reindex_aux_spec:
  ∀inds indsv fmlls fmlv iacc iaccv vacc vaccv.
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  (LIST_TYPE NUM) iacc iaccv ∧
  (LIST_TYPE constraint_TYPE) vacc vaccv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_aux_arr" (get_ml_prog_state()))
    [fmlv; indsv; iaccv; vaccv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE) (reindex_aux fmlls inds iacc vacc) v))
Proof
  Induct>>
  xcf"reindex_aux_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[reindex_aux_def,LIST_TYPE_def,PAIR_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[reindex_aux_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >-
    (xapp>>simp[])>>
  rpt xlet_autop>>
  xapp>>
  fs[LIST_TYPE_def]
QED

Theorem reindex_arr_spec:
  ∀inds indsv fmlls fmlv.
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_arr" (get_ml_prog_state()))
    [fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE constraint_TYPE) (reindex fmlls inds) v))
Proof
  xcf"reindex_arr"(get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  simp[reindex_def]>>
  metis_tac[LIST_TYPE_def]
QED

val res = translate is_Pos_def;
val res = translate subst_aux_def;
val res = translate partition_def;
val res = translate clean_up_def;
val res = translate subst_lhs_def;
val res = translate subst_def;

val res = translate obj_constraint_def;
val res = translate npbc_checkTheory.subst_fun_def;
val res = translate subst_subst_fun_def;

val extract_clauses_arr = process_topdecs`
  fun extract_clauses_arr lno s fml rsubs pfs acc =
  case pfs of [] => List.rev acc
  | cpf::pfs =>
    case cpf of
      (None,pf) =>
        extract_clauses_arr lno s fml rsubs pfs ((None,pf)::acc)
    | (Some (Inl n,i),pf) =>
      (case Array.lookup fml None n of
        None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
      | Some c => extract_clauses_arr lno s fml rsubs pfs ((Some ([not_1(subst_subst_fun s c)],i),pf)::acc))
    | (Some (Inr u,i),pf) =>
      if u < List.length rsubs then
        extract_clauses_arr lno s fml rsubs pfs ((Some (List.nth rsubs u,i),pf)::acc)
      else raise Fail (format_failure lno ("invalid #proofgoal id: " ^ Int.toString u))
` |> append_prog;

Theorem extract_clauses_arr_spec:
  ∀pfs pfsv s sv fmlls fmlv fmllsv rsubs rsubsv acc accv lno lnov.
  NUM lno lnov ∧
  (SPTREE_SPT_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))) s sv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) rsubs rsubsv ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) pfs pfsv ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) acc accv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extract_clauses_arr" (get_ml_prog_state()))
    [lnov; sv; fmlv; rsubsv; pfsv; accv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        &(case extract_clauses_list s fmlls rsubs pfs acc of
            NONE => F
          | SOME res =>
            LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧
          extract_clauses_list s fmlls rsubs pfs acc = NONE)))
Proof
  Induct>>
  xcf"extract_clauses_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [alpha |-> ``:((npbc list # num) option # lstep list) ``])>>
    xsimpl>>
    asm_exists_tac>>rw[]>>
    simp[extract_clauses_list_def])>>
  xmatch>>
  simp[Once extract_clauses_list_def]>>
  Cases_on`h`>>fs[]>>
  Cases_on`q`>>fs[PAIR_TYPE_def,OPTION_TYPE_def]
  >- (
    xmatch>>
    rpt xlet_autop>>
    xapp>>xsimpl>>
    rpt(asm_exists_tac>>xsimpl)>>
    first_x_assum (irule_at Any)>>
    qexists_tac`(NONE,r)::acc`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def])>>
  Cases_on`x`>> Cases_on`q`>>
  fs[PAIR_TYPE_def,SUM_TYPE_def]>>xmatch
  >- (
    (* INL *)
    xlet_autop>>
    xlet_auto>>
    `OPTION_TYPE constraint_TYPE (any_el x fmlls NONE) v'` by (
       rw[any_el_ALT]>>
       fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    qpat_x_assum`v' = _` (assume_tac o SYM)>>
    Cases_on`any_el x fmlls NONE`>>fs[OPTION_TYPE_def]
    >- (
      xmatch>>
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[extract_clauses_list_def]>>
      metis_tac[Fail_exn_def])>>
    xmatch>>
    fs[constraint_TYPE_def]>>
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    qmatch_goalsub_abbrev_tac`extract_clauses_list _ _ _ _ acc'`>>
    qexists_tac`acc'`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,Abbr`acc'`])>>
  (* INR *)
  fs[constraint_TYPE_def]>>
  rpt xlet_autop>>
  IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
  >- (
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    qmatch_goalsub_abbrev_tac`extract_clauses_list _ _ _ _ acc'`>>
    qexists_tac`acc'`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def,Abbr`acc'`]>>
    fs[mllistTheory.nth_def])>>
  rpt xlet_autop>>
  xraise>>
  xsimpl>>
  simp[extract_clauses_list_def,Fail_exn_def]>>
  metis_tac[]
QED

val res = translate subst_opt_aux_acc_def;
val res = translate imp_def;
val res = translate subst_opt_def;
val res = translate subst_opt_subst_fun_def;

val subst_indexes_arr = process_topdecs`
  fun subst_indexes_arr s fml is =
  case is of [] => []
  | (i::is) =>
    (case Array.lookup fml None i of
      None => subst_indexes_arr s fml is
    | Some res =>
    (case subst_opt_subst_fun s res of
      None => subst_indexes_arr s fml is
    | Some c => (i,c)::subst_indexes_arr s fml is))`
    |> append_prog;

Theorem subst_indexes_arr_spec:
  ∀is isv s sv fmlls fmllsv fmlv.
  (SPTREE_SPT_TYPE (SUM_TYPE BOOL (PBC_LIT_TYPE NUM))) s sv ∧
  LIST_TYPE NUM is isv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "subst_indexes_arr" (get_ml_prog_state()))
    [sv; fmlv; isv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) (subst_indexes s fmlls is) v))
Proof
  Induct>>
  xcf"subst_indexes_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    simp[subst_indexes_def,LIST_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  simp[subst_indexes_def]>>
  Cases_on`any_el h fmlls NONE`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>xapp>>
    metis_tac[])>>
  xmatch>>
  fs[constraint_TYPE_def]>>
  xlet_autop>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>xapp>>
    metis_tac[])>>
  xmatch>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  simp[LIST_TYPE_def,PAIR_TYPE_def]
QED

val list_insert_arr = process_topdecs`
  fun list_insert_arr ls id fml inds =
    case ls of
      [] => (id,(fml,inds))
    | (c::cs) =>
      list_insert_arr cs (id+1)
      (Array.updateResize fml None id (Some c))
      (sorted_insert id inds)` |> append_prog

Theorem list_insert_arr_spec:
  ∀ls lsv fmlv fmlls fmllsv id idv inds indsv.
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_insert_arr" (get_ml_prog_state()))
    [lsv; idv; fmlv; indsv;]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      SEP_EXISTS fmlv' fmllsv'.
      ARRAY fmlv' fmllsv' *
      &(PAIR_TYPE NUM
          (PAIR_TYPE (λl v.
          LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
          v = fmlv') (LIST_TYPE NUM)) (list_insert_list ls id fmlls inds) resv))
Proof
  Induct>>
  rw[]>>simp[list_insert_list_def]>>
  xcf "list_insert_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  rpt xlet_autop>>
  xapp>>simp[]>>
  match_mp_tac LIST_REL_update_resize>>
  simp[OPTION_TYPE_def]
QED

val check_subproofs_arr = process_topdecs`
  fun check_subproofs_arr lno pfs core fml inds mindel id =
  case pfs of
    [] => (fml,id)
  | (cnopt,pf)::pfs =>
    (case cnopt of
      None =>
      (case check_lsteps_arr lno pf core fml inds mindel id of
        (fml', (id', inds')) =>
          check_subproofs_arr lno pfs core fml' inds' mindel id')
    | Some (cs,n) =>
      case list_insert_arr cs id fml inds of
        (cid, (cfml, cinds)) =>
        (case check_lsteps_arr lno pf core cfml cinds id cid of
          (fml', (id', inds')) =>
          if check_contradiction_fml_arr fml' n then
            let val u = rollback_arr fml' id id' in
              check_subproofs_arr lno pfs core fml' inds' mindel id'
            end
          else
            raise Fail (format_failure lno ("Subproof did not derive contradiction from index:" ^ Int.toString n))))` |> append_prog

Theorem check_subproofs_arr_spec:
  ∀pfs fmlls inds mindel id pfsv lno lnov idv indsv fmlv fmllsv mindelv core corev.
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) pfs pfsv ∧
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_subproofs_arr" (get_ml_prog_state()))
    [lnov; pfsv; corev; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_subproofs_list pfs core fmlls inds mindel id of
            NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') NUM res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_subproofs_list pfs core fmlls inds mindel id = NONE)))
Proof
  Induct>>
  rw[]>>simp[check_subproofs_list_def]>>
  xcf "check_subproofs_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    asm_exists_tac>>
    xsimpl)>>
  Cases_on`h`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  simp[check_subproofs_list_def]>>
  Cases_on`q`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xlet_autop
    >- (
      xsimpl>>
      rw[]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[])>>
  Cases_on`x`>>fs[PAIR_TYPE_def]>>
  xmatch>>
  drule list_insert_arr_spec>>
  rpt (disch_then drule)>>
  strip_tac>>
  xlet_autop>>
  pairarg_tac>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xlet_autop
  >- (
    xsimpl>>rw[]>>
    metis_tac[ARRAY_refl])>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  PairCases_on`x`>>simp[PAIR_TYPE_def]>>
  strip_tac>>xmatch>>
  xlet_autop>>
  reverse IF_CASES_TAC>>xif>>asm_exists_tac>>xsimpl
  >- (
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_refl])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  metis_tac[]
QED

val res = translate insert_def;
val res = translate npbc_checkTheory.extract_pids_def;

Definition do_rso_def:
  do_rso ord s c obj =
  red_subgoals ord (subst_fun s) c obj
End

val res = translate list_list_insert_def;
val res = translate npbcTheory.dom_subst_def;
val res = translate npbc_checkTheory.red_subgoals_def;
val res = translate do_rso_def;

val res = translate npbc_checkTheory.list_pair_eq_def;
val res = translate npbc_checkTheory.equal_constraint_def;
val res = translate npbc_checkTheory.mem_constraint_def;

val res = translate hash_pair_def;
val res = translate (hash_list_def |> REWRITE_RULE [splim_def]);
val res = translate (hash_constraint_def |> REWRITE_RULE [splim_def]);

(* TODO: can use Unsafe.update instead *)
val mk_hashset_arr = process_topdecs`
  fun mk_hashset_arr ps acc =
  case ps of [] => ()
  | p::ps =>
  let val h = hash_constraint p in
    Array.update acc h (p::(Array.sub acc h));
    mk_hashset_arr ps acc
  end` |> append_prog;

Theorem hash_constraint_splim:
  hash_constraint h < splim
Proof
  Cases_on`h`>>fs[hash_constraint_def]>>
  match_mp_tac MOD_LESS>>
  EVAL_TAC
QED

Theorem mk_hashset_arr_spec:
  ∀ls lsv hs hsv.
  (LIST_TYPE constraint_TYPE) ls lsv ∧
  LENGTH hsv = splim ∧
  LIST_REL (LIST_TYPE constraint_TYPE) hs hsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "mk_hashset_arr" (get_ml_prog_state()))
    [lsv; hspv]
    (ARRAY hspv hsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS hsv'.
      ARRAY hspv hsv' *
      &(LIST_REL (LIST_TYPE constraint_TYPE) (mk_hashset ls hs) hsv') )
Proof
  Induct>>
  rw[]>>simp[mk_hashset_def]>>
  xcf "mk_hashset_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl) >>
  xmatch>>
  fs[constraint_TYPE_def]>>
  rpt xlet_autop>>
  xlet_auto>- (
    xsimpl>>
    simp[hash_constraint_splim])>>
  rpt xlet_autop>>
  xlet_auto>- (
    xsimpl>>
    simp[hash_constraint_splim])>>
  xapp>>simp[]>>
  match_mp_tac EVERY2_LUPDATE_same>>
  simp[LIST_TYPE_def]>>
  fs[LIST_REL_EL_EQN]>>
  first_x_assum match_mp_tac>>
  gs[hash_constraint_splim]
QED

val in_hashset_arr = process_topdecs`
  fun in_hashset_arr p hs =
  let val h = hash_constraint p in
    mem_constraint p (Array.sub hs h)
  end` |> append_prog;

Theorem in_hashset_arr_spec:
  constraint_TYPE c cv ∧
  LENGTH hsv = splim ∧
  LIST_REL (LIST_TYPE constraint_TYPE) hs hsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "in_hashset_arr" (get_ml_prog_state()))
    [cv; hspv]
    (ARRAY hspv hsv)
    (POSTv resv.
      ARRAY hspv hsv *
      &BOOL (in_hashset c hs) resv)
Proof
  rw[]>>simp[in_hashset_def]>>
  xcf "in_hashset_arr" (get_ml_prog_state ())>>
  fs[constraint_TYPE_def]>>
  xlet_autop>>
  xlet_auto
  >- (xsimpl>>simp[hash_constraint_splim])>>
  xapp>>
  xsimpl>>
  first_x_assum (irule_at Any)>>
  qexists_tac`EL (hash_constraint c) hs`>>simp[]>>
  fs[LIST_REL_EL_EQN]>>
  first_x_assum match_mp_tac>>
  gs[hash_constraint_splim]
QED

val r = translate splim_def;

val every_snd_hs = process_topdecs`
  fun every_snd_hs hs ls =
  case ls of [] => True
  | l::ls =>
    in_hashset_arr (snd l) hs andalso
    every_snd_hs hs ls` |> append_prog

Theorem every_snd_hs_spec:
  ∀ls lsv.
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) ls lsv ∧
  LENGTH hsv = splim ∧
  LIST_REL (LIST_TYPE constraint_TYPE) hs hsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_snd_hs" (get_ml_prog_state()))
    [hspv; lsv]
    (ARRAY hspv hsv)
    (POSTv resv.
      ARRAY hspv hsv *
      &BOOL (EVERY (λ(i,c). in_hashset c hs) ls) resv)
Proof
  Induct>>rw[]>>
  fs[LIST_TYPE_def]>>
  xcf "every_snd_hs" (get_ml_prog_state ())>>
  xmatch
  >- (xcon>>xsimpl)>>
  rpt xlet_autop>>
  xlog>>
  xsimpl>>rw[]
  >- (
    xapp>>xsimpl>>
    pairarg_tac>>fs[])>>
  pairarg_tac>>fs[]
QED

val hash_check = process_topdecs`
  fun hash_check fmlls proved lf =
  case lf of
    [] => True
  | _ =>
  let
    val hs = Array.array splim []
    val u = mk_hashset_arr proved hs
    val u = mk_hashset_arr fmlls hs
  in
    every_snd_hs hs lf
  end` |> append_prog

Theorem LENGTH_mk_hashset[simp]:
  ∀x ls.
  LENGTH (mk_hashset x ls) = LENGTH ls
Proof
  Induct>>rw[mk_hashset_def]
QED

Theorem hash_check_spec:
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) ls lsv ∧
  LIST_TYPE constraint_TYPE x xv ∧
  LIST_TYPE constraint_TYPE y yv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "hash_check" (get_ml_prog_state()))
    [xv; yv; lsv]
    emp
    (POSTv resv.
      &BOOL (
        let hs = mk_hashset x
          (mk_hashset y (REPLICATE splim [])) in
          EVERY (λ(i,c). in_hashset c hs) ls) resv)
Proof
  rw[]>>
  xcf "hash_check" (get_ml_prog_state ())>>
  Cases_on`ls`
  >- (
    fs[LIST_TYPE_def]>>
    xmatch>>
    xcon>>xsimpl)>>
  fs[LIST_TYPE_def]>>
  xmatch>>
  xlet_autop>>
  assume_tac (fetch "-" "splim_v_thm")>>
  xlet_auto>>
  qmatch_goalsub_abbrev_tac`ARRAY av hsv`>>
  `LIST_REL (LIST_TYPE constraint_TYPE) (REPLICATE splim []) hsv` by
    simp[Abbr`hsv`,LIST_REL_REPLICATE_same,LIST_TYPE_def]>>
  qmatch_asmsub_abbrev_tac`LIST_REL _ hs _`>>
  xlet`POSTv resv.
    &UNIT_TYPE () resv *
    SEP_EXISTS hsv'.
    ARRAY av hsv' *
    &LIST_REL (LIST_TYPE constraint_TYPE) (mk_hashset y hs) hsv'`
  >-
    (xapp>>unabbrev_all_tac>>fs[])>>
  xlet_auto
  >- (
    xsimpl>>
    fs[LIST_REL_EL_EQN,Abbr`hs`])>>
  xapp>>xsimpl>>
  first_assum (irule_at Any)>>
  qexists_tac`h::t`>>simp[LIST_TYPE_def]>>
  unabbrev_all_tac>>fs[LIST_REL_EL_EQN]
QED

Definition red_cond_check_def:
  red_cond_check indfml (pfs:(( ((num + num) # num) option, (lstep list)) alist)) (rsubs:((int # num) list # num) list list) goals =
  let (l,r) = extract_pids pfs LN LN in
  split_goals_hash indfml l goals ∧
  EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs))
End

Definition red_cond_check_pure_def:
  red_cond_check_pure (pfs:(( ((num + num) # num) option, (lstep list)) alist)) (rsubs:((int # num) list # num) list list) (goals:(num # (int # num) list # num) list) =
  let (l,r) = extract_pids pfs LN LN in
  if
    EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs))
  then
  let (lp,lf) =
      PARTITION (λ(i,c). lookup i l ≠ NONE) goals in
    let proved = MAP SND lp in
    SOME (proved,lf)
  else NONE
End

Theorem red_cond_check_eq:
  red_cond_check indfml pfs rsubs goals =
  case red_cond_check_pure pfs rsubs goals of
    NONE => F
  | SOME (x,ls) =>
    let hs = mk_hashset indfml (mk_hashset x (REPLICATE splim [])) in
    EVERY (λ(i,c). in_hashset c hs) ls
Proof
  rw[red_cond_check_def,red_cond_check_pure_def]>>
  pairarg_tac>>fs[split_goals_hash_def]>>
  IF_CASES_TAC>>fs[]>>
  rpt (pairarg_tac>>fs[])
QED

val res = translate COUNT_LIST_AUX_def;
val res = translate COUNT_LIST_compute;
val res = translate PART_DEF;
val res = translate PARTITION_DEF;

val res = translate red_cond_check_pure_def;

val red_cond_check = process_topdecs`
  fun red_cond_check indfml pfs rsubs goals =
  case red_cond_check_pure pfs rsubs goals of
    None => False
  | Some (x,ls) =>
    hash_check indfml x ls` |> append_prog

Theorem red_cond_check_spec:
  LIST_TYPE constraint_TYPE a av ∧
  LIST_TYPE
     (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (SUM_TYPE NUM NUM) NUM))
        (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) b bv ∧
  LIST_TYPE (LIST_TYPE constraint_TYPE) c cv ∧
  LIST_TYPE (PAIR_TYPE NUM constraint_TYPE) d dv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "red_cond_check" (get_ml_prog_state()))
    [av; bv; cv; dv]
    emp
    (POSTv resv.
      &BOOL (red_cond_check a b c d) resv)
Proof
  rw[]>>
  xcf "red_cond_check" (get_ml_prog_state ())>>
  fs[constraint_TYPE_def]>>
  xlet_autop>>
  simp[red_cond_check_eq]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  TOP_CASE_TAC>>fs[PAIR_TYPE_def]>>
  xmatch>>
  xapp>>
  xsimpl>>
  fs[constraint_TYPE_def]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

(* Definition print_subgoal_def:
  (print_subgoal (INL n) = (toString (n:num))) ∧
  (print_subgoal (INR n) = (strlit"#" ^ toString (n:num)))
End

Definition print_subproofs_def:
  (print_subproofs ls =
    concatWith (strlit " ") (MAP print_subgoal ls))
End *)

Definition print_expected_subproofs_def:
  (print_expected_subproofs rsubs (si: (num # 'a) list) =
    strlit ("#[1-") ^
    toString (LENGTH rsubs) ^ strlit "] and " ^
    concatWith (strlit" ") (MAP (toString o FST) si))
End

Definition print_subproofs_err_def:
  print_subproofs_err rsubs si =
  strlit"Expected: " ^
  print_expected_subproofs rsubs si
  (* ^
  strlit " Got: " ^
  print_subproofs pfs *)
End

(* val res = translate print_subgoal_def;
val res = translate print_subproofs_def; *)
val res = translate print_expected_subproofs_def;
val res = translate print_subproofs_err_def;

val format_failure_2_def = Define`
  format_failure_2 (lno:num) s s2 =
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit " Reason: " ^ s
  ^ strlit " Info: " ^ s2 ^ strlit"\n"`

val r = translate format_failure_2_def;

val check_sstep_arr = process_topdecs`
  fun check_sstep_arr lno step ord obj core fml inds id =
  case step of
    Lstep lstep =>
    check_lstep_arr lno lstep core fml inds 0 id
  | Red c s pfs idopt =>
    ( case reindex_arr fml inds of (rinds,fmlls) =>
      let val rsubs = do_rso ord s c obj
         val cpfs = extract_clauses_arr lno s fml rsubs pfs []
         val fml_not_c = Array.updateResize fml None id (Some (not_1 c)) in
         case check_subproofs_arr lno cpfs core fml_not_c (sorted_insert id rinds) id (id+1) of
           (fml', id') =>
         (case idopt of
           None =>
           let val u = rollback_arr fml' id id'
               val goals = subst_indexes_arr s fml' rinds in
               if red_cond_check fmlls pfs rsubs goals
               then
                 (Array.updateResize fml' None id' (Some c), ((id'+1), sorted_insert id' rinds))
               else raise Fail (format_failure_2 lno ("Redundancy subproofs did not cover all subgoals.") (print_subproofs_err rsubs goals))
           end
        | Some cid =>
          if check_contradiction_fml_arr fml' cid then
            let val u = rollback_arr fml' id id' in
              (Array.updateResize fml' None id' (Some c), ((id'+1), sorted_insert id' rinds))
            end
          else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
    end)
  ` |> append_prog

val NPBC_CHECK_SSTEP_TYPE_def = theorem "NPBC_CHECK_SSTEP_TYPE_def";

Definition spo_TYPE_def:
  spo_TYPE =
    (PAIR_TYPE
      (LIST_TYPE constraint_TYPE)
      (PAIR_TYPE (LIST_TYPE NUM) (LIST_TYPE NUM)))
End

Definition ord_TYPE_def:
  ord_TYPE =
  OPTION_TYPE
     (PAIR_TYPE spo_TYPE (LIST_TYPE NUM))
End

Theorem check_sstep_arr_spec:
  ∀step fmlls inds id stepv lno lnov idv indsv fmlv fmllsv obj objv core corev ord ordv.
  NPBC_CHECK_SSTEP_TYPE step stepv ∧
  NUM lno lnov ∧
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  OPTION_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) obj objv ∧
  ord_TYPE ord ordv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_sstep_arr" (get_ml_prog_state()))
    [lnov; stepv; ordv; objv; corev; fmlv; indsv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_sstep_list step ord obj core fmlls inds id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE NUM (LIST_TYPE NUM)) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_sstep_list step ord obj core fmlls inds id = NONE)))
Proof
  rw[]>>
  xcf "check_sstep_arr" (get_ml_prog_state ())>>
  rw[check_sstep_list_def]>>
  Cases_on`step`>>fs[NPBC_CHECK_SSTEP_TYPE_def]
  >- ((* lstep *)
    xmatch>>
    xapp>>
    xsimpl>>
    metis_tac[])
  >- ((*Red*)
    xmatch>>
    pairarg_tac>>gs[]>>
    xlet_autop>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    fs[spo_TYPE_def,ord_TYPE_def,constraint_TYPE_def]>>
    rpt xlet_autop>>
    qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
    xlet`(POSTve
      (λv.
        ARRAY aa vv *
        &(case extract_clauses_list s fmlls (do_rso ord s p' obj) l [] of
            NONE => F
          | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
    (λe.
      ARRAY aa vv *
      & (Fail_exn e ∧ extract_clauses_list s fmlls (do_rso ord s p' obj) l [] = NONE)))`
    >- (
      xapp>>xsimpl>>
      fs[constraint_TYPE_def,LIST_TYPE_def]>>
      metis_tac[])
    >- (
      xsimpl>>
      fs[do_rso_def]>>
      metis_tac[ARRAY_refl])>>
    fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>gvs[]>>
    strip_tac>>
    fs[do_rso_def]>>
    rpt xlet_autop>>
    xlet_auto>>
    rpt xlet_autop>>
    rename1`_ (not n) vvv`>>
    `LIST_REL (OPTION_TYPE constraint_TYPE)
      (update_resize fmlls NONE (SOME (not n)) id)
      (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
              (Conv (SOME (TypeStamp "Some" 2)) [vvv]) id)` by
      (match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def,constraint_TYPE_def])>>
    xlet_autop
    >- (
      xsimpl>>rw[]>>
      fs[do_rso_def]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    Cases_on`x'`>>simp[PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    rename1`OPTION_TYPE NUM idopt _`>>
    Cases_on`idopt`>>fs[OPTION_TYPE_def,do_red_check_def]>>xmatch
    >- (
      rpt xlet_autop>>
      fs[GSYM constraint_TYPE_def]>>
      xlet_autop>>
      fs[do_red_check_def]>>
      reverse xif
      >- (
        rpt xlet_autop>>
        fs[red_cond_check_def]>>
        pairarg_tac>>fs[]>>
        xraise>>
        xsimpl>>
        rw[]>>fs[]>>
        metis_tac[ARRAY_refl,NOT_EVERY,Fail_exn_def]) >>
      fs[red_cond_check_def]>>
      pairarg_tac>>fs[]>>
      rpt xlet_autop>>
      xlet_auto>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ vvvv`>>
      qexists_tac`vvvv`>>xsimpl>>
      simp[Abbr`vvvv`]>>
      match_mp_tac LIST_REL_update_resize>>
      fs[OPTION_TYPE_def,constraint_TYPE_def])>>
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      rw[]>>fs[]>>
      metis_tac[ARRAY_refl,NOT_EVERY,Fail_exn_def]) >>
    rpt xlet_autop>>
    xlet_auto>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    qmatch_goalsub_abbrev_tac`ARRAY _ vvvv`>>
    qexists_tac`vvvv`>>xsimpl>>
    simp[Abbr`vvvv`]>>
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,constraint_TYPE_def])
QED

val read_coref_arr = process_topdecs`
  fun read_coref_arr ls fml =
  case ls of [] => []
  | i::is =>
    case Array.lookup fml None i of
      None => (i,([],0))::read_coref_arr is fml
    | Some res => (i,res) :: read_coref_arr is fml` |> append_prog

Theorem read_coref_arr_spec:
  ∀ls lsv.
  LIST_TYPE NUM ls lsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "read_coref_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * &(
        LIST_TYPE (PAIR_TYPE NUM constraint_TYPE)
          (read_coref_list ls fmlls) v
      ))
Proof
  Induct>>rw[read_coref_list_def]>>
  xcf "read_coref_arr" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]>>xmatch
  >-
    (xcon>>xsimpl)>>
  xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  TOP_CASE_TAC>>gs[OPTION_TYPE_def]>>
  xmatch
  >- (
    first_x_assum drule>>
    rw[]>>
    rpt xlet_autop>>
    xcon>>
    xsimpl>>
    fs[LIST_TYPE_def,PAIR_TYPE_def,constraint_TYPE_def])>>
  first_x_assum drule>>
  rw[]>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  fs[LIST_TYPE_def,PAIR_TYPE_def,constraint_TYPE_def]
QED

val res = translate lrnext_def;
val res = translate foldi_def;
val res = translate toAList_def;

val res = translate fromAList_def;

Definition mapfsttoalist_def:
  mapfsttoalist c = MAP FST (toAList c)
End

val res = translate mapfsttoalist_def;

val coref_arr = process_topdecs`
  fun coref_arr core fml =
  let val ids = mapfsttoalist core in
  fromalist (read_coref_arr ids fml)
  end` |> append_prog

Theorem coref_arr_spec:
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "coref_arr" (get_ml_prog_state()))
    [corev; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * &(
        SPTREE_SPT_TYPE constraint_TYPE
          (coref_list core fmlls) v
      ))
Proof
  xcf "coref_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xapp_spec (fetch "-" "fromalist_v_thm" |> INST_TYPE [alpha|->``:npbc``])>>
  asm_exists_tac>>xsimpl>>
  rw[coref_list_def]>>
  fs[mapfsttoalist_def]
QED

Definition all_core_every_def:
  all_core_every (core:num_set) (inds:num list) =
  (EVERY (λn. lookup n core ≠ NONE) inds)
End

val res = translate all_core_every_def;

val all_core_arr_def = process_topdecs `
  fun all_core_arr fml inds core =
  let val inds' = fst (reindex_arr fml inds) in
    (all_core_every core inds',inds')
  end` |> append_prog

Theorem all_core_arr_spec:
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  LIST_TYPE NUM inds indsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "all_core_arr" (get_ml_prog_state()))
    [fmlv; indsv; corev]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv * &(
        PAIR_TYPE BOOL (LIST_TYPE NUM)
          (all_core fmlls inds core) v
      ))
Proof
  xcf "all_core_arr" (get_ml_prog_state ())>>
  rpt xlet_autop>>
  xcon>>
  xsimpl>>
  fs[all_core_def,all_core_every_def,PAIR_TYPE_def]
QED

val _ = register_type ``:cstep ``

val res = translate npbc_checkTheory.trans_subst_def;
val res = translate npbc_checkTheory.build_fml_def;
val res = translate EL;

val el_side_def = theorem "el_side_def";
val el_side = Q.prove(
  `∀n ls. el_side n ls ⇔ n < LENGTH ls`,
  Induct>>
  rw[Once el_side_def]>>
  Cases_on`ls`>>simp[]
) |> update_precondition

val res = translate npbc_checkTheory.extract_clauses_def;

val res = translate FOLDL;
val res = translate mk_BN_def;
val res = translate mk_BS_def;
val res = translate delete_def;
val res = translate npbc_checkTheory.check_cutting_def;
val res = translate npbc_checkTheory.check_contradiction_fml_def;
val res = translate npbc_checkTheory.check_lstep_def;
val res = translate npbc_checkTheory.list_insert_def;
val res = translate npbc_checkTheory.check_subproofs_def;
val res = translate
  (npbc_checkTheory.check_transitivity_def |> REWRITE_RULE [MEMBER_INTRO]);

val res = translate (npbc_checkTheory.check_good_ord_def |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate (npbc_checkTheory.check_ws_def |> REWRITE_RULE [MEMBER_INTRO]);

Definition check_storeorder_def:
  check_storeorder spo ws pfs ⇔
  check_good_ord spo ∧ check_ws spo ws ∧
  check_transitivity spo ws pfs
End

val res = translate check_storeorder_def;

Definition do_transfer_def:
  do_transfer core ls =
  FOLDL (λa b. insert b () a) core ls
End

val res = translate do_transfer_def;

val every_transfer_check = process_topdecs`
  fun every_transfer_check fml ls =
  case ls of
    [] => True
  | (id::ls) =>
    (case Array.lookup fml None id of
      None => False
    | Some u => every_transfer_check fml ls)` |> append_prog

Theorem every_transfer_check_spec:
  ∀ls lsv fmlv fmlls fmllsv.
  (LIST_TYPE NUM) ls lsv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "every_transfer_check" (get_ml_prog_state()))
    [fmlv; lsv;]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      ARRAY fmlv fmllsv *
      &(BOOL (EVERY (λid. any_el id fmlls NONE ≠ NONE) ls) resv))
Proof
  Induct>>
  rw[]>>
  xcf "every_transfer_check" (get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl)>>
  xmatch>>
  rpt xlet_autop>>
  xlet_auto>>
  `OPTION_TYPE constraint_TYPE (any_el h fmlls NONE) v'` by (
    rw[any_el_ALT]>>
    fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  Cases_on`any_el h fmlls NONE`>>fs[OPTION_TYPE_def]>>
  xmatch >- (xcon>>xsimpl)>>
  xapp>>simp[]
QED

val res = translate npbcTheory.b2n_def;
val res = translate npbcTheory.eval_lit_def;
val res = translate npbcTheory.eval_term_def;
val res = translate npbcTheory.eval_obj_def;
val res = translate npbc_checkTheory.opt_lt_def;
val res = translate npbcTheory.satisfies_npbc_def;
val res = translate npbc_checkTheory.check_obj_def;

val res = translate npbc_checkTheory.model_improving_def;

(* Pure part of checked_del chk=T *)
Definition checked_del_pure_chk_def:
  checked_del_pure_chk cf pfs ord obj core id inds ls bound orders =
  case check_del pfs ord obj core cf id of
    NONE => NONE
  | SOME id' =>
  let pids = MAP FST pfs in (* optimize and change later *)
  if EVERY (λid. MEM id pids) ls then
    SOME (inds, id',
          FOLDL (λa b. delete b a) core ls,
          bound, ord, orders)
  else
    NONE
End

Definition do_dso_def:
  do_dso spo s c obj =
  dom_subgoals spo (subst_fun s) c obj
End

val res = translate npbc_checkTheory.neg_dom_subst_def;
val res = translate npbc_checkTheory.dom_subgoals_def;
val res = translate do_dso_def;

Definition core_subgoals_def:
  core_subgoals s cf =
  toAList (map_opt (subst_opt (subst_fun s)) cf)
End

val res = translate npbc_checkTheory.map_opt_def;
val res = translate core_subgoals_def;

Definition do_core_del_def:
  do_core_del (core:num_set) ls =
  FOLDL (λa b. delete b a) core ls
End

val res = translate do_core_del_def;
val res = translate core_from_inds_def;

val check_cstep_arr = process_topdecs`
  fun check_cstep_arr lno cstep chk ord obj bound
    core fml inds id orders =
  case cstep of
    Dom c s pfs idopt =>
    (case ord of None =>
      raise Fail (format_failure lno "no order loaded for dominance")
    | Some spo =>
    case reindex_arr fml inds of (rinds,fmlls) =>
    let
        val cf = coref_arr core fml
        val dsubs = do_dso spo s c obj
        val cpfs = extract_clauses_arr lno s fml dsubs pfs []
        val fml_not_c = Array.updateResize fml None id (Some (not_1 c)) in
         case check_subproofs_arr lno cpfs core fml_not_c (sorted_insert id rinds) id (id+1) of
           (fml', id') =>
           (case idopt of
             None =>
             let val u = rollback_arr fml' id id'
                 val goals = core_subgoals s cf in
                 if red_cond_check fmlls pfs dsubs goals
                 then
                   (Array.updateResize fml' None id' (Some c),
                   (sorted_insert id' rinds,
                   (id'+1, (core, (bound, (ord,orders))))))
                 else raise Fail (format_failure_2 lno ("Dominance subproofs did not cover all subgoals") (print_subproofs_err dsubs goals))
             end
           | Some cid =>
             if check_contradiction_fml_arr fml' cid then
               let val u = rollback_arr fml' id id' in
                 (Array.updateResize fml' None id' (Some c),
                   (sorted_insert id' rinds,
                   (id'+1, (core, (bound, (ord,orders))))))
               end
             else raise Fail (format_failure lno ("did not derive contradiction from index:" ^ Int.toString cid)))
    end)
  | Loadorder nn xs =>
    let val inds' = fst (reindex_arr fml inds) in
    case Alist.lookup orders nn of
      None =>
        raise Fail (format_failure lno ("no such order: " ^ nn))
    | Some ord' =>
      if List.length xs = List.length (fst (snd ord')) then
        (fml,(inds',(id,(core_from_inds inds',(bound,(Some (ord',xs),orders))))))
      else
        raise Fail (format_failure lno ("invalid order instantiation"))
    end
  | Unloadorder =>
    (case ord of None =>
     raise Fail (format_failure lno ("no order loaded"))
    | Some spo =>
      (fml,(inds,(id,(core,(bound,(None, orders)))))))
  | Storeorder nn spo ws pfs => (
    if check_storeorder spo ws pfs then
      (fml,(inds,(id,(core,(bound,(ord,((nn,spo)::orders)))))))
    else
     raise Fail (format_failure lno ("invalid order definition")))
  | Transfer ls => (
    if every_transfer_check fml ls
    then
      (fml, (inds, (id,
       (do_transfer core ls,
       (bound, (ord, orders))))))
    else
     raise Fail (format_failure lno ("core transfer invalid ids")))
  | Checkeddelete ls pfs => (
    if all_core_every core ls then
    (
      if chk then
        raise Fail (format_failure lno ("core del with explicit subproofs not yet supported"))
      else
      if ord = None then
        (list_delete_arr ls fml;
          (fml, (inds, (id,
                (do_core_del core ls,
                (bound, (ord, orders)))))))
      else
        case all_core_arr fml inds core of (ac,inds') =>
        if ac then
          (list_delete_arr ls fml;
            (fml, (inds', (id,
                  (do_core_del core ls,
                  (bound, (ord, orders)))))))
        else
           raise Fail (format_failure lno ("not all constraints in core")))
    else
      raise Fail (format_failure lno ("not all core del ids in core"))
    )
    | Sstep sstep => (
    case check_sstep_arr lno sstep ord obj core fml inds id of
      (fml',(id',inds')) =>
      (fml',(inds',(id',(core,(bound,(ord,orders)))))))
  | Obj w => (
    case check_obj obj bound w (coref_arr core fml) of
      None =>
       raise Fail (format_failure lno ("supplied assignment did not satisfy constraints or did not improve objective"))
    | Some new =>
      let val c = model_improving obj new in
        (Array.updateResize fml None id (Some c),
         (sorted_insert id inds,
         (id+1,
         (insert_1 id () core,
         (Some new, (ord, orders))))))
      end
    )`
  |> append_prog;

val NPBC_CHECK_CSTEP_TYPE_def = theorem "NPBC_CHECK_CSTEP_TYPE_def";

Theorem EqualityType_OPTION_TYPE:
  EqualityType a ⇒
  EqualityType (OPTION_TYPE a)
Proof
  EVAL_TAC>>
  rw[]>>
  Cases_on`x1`>>fs[OPTION_TYPE_def]>>
  TRY(Cases_on`x2`>>fs[OPTION_TYPE_def])>>
  EVAL_TAC>>
  metis_tac[]
QED

Theorem EqualityType_ord_TYPE:
  EqualityType ord_TYPE
Proof
  rw[ord_TYPE_def,spo_TYPE_def,constraint_TYPE_def]>>
  metis_tac[EqualityType_OPTION_TYPE,EqualityType_PAIR_TYPE,EqualityType_LIST_TYPE,EqualityType_NUM_BOOL]
QED

Theorem check_cstep_arr_spec:
  NPBC_CHECK_CSTEP_TYPE cstep cstepv ∧
  NUM lno lnov ∧
  BOOL chk chkv ∧
  ord_TYPE ord ordv ∧
  OPTION_TYPE (LIST_TYPE (PAIR_TYPE INT NUM)) obj objv ∧
  OPTION_TYPE NUM bound boundv ∧
  SPTREE_SPT_TYPE UNIT_TYPE core corev ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE constraint_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv ∧
  LIST_TYPE (PAIR_TYPE STRING_TYPE spo_TYPE) orders ordersv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_cstep_arr" (get_ml_prog_state()))
    [lnov; cstepv; chkv; ordv; objv; boundv; corev;
      fmlv; indsv; idv; ordersv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_cstep_list cstep chk ord obj bound core fmlls inds id orders of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE constraint_TYPE) l fmllsv' ∧
              v = fmlv')
              (PAIR_TYPE (LIST_TYPE NUM)
                (PAIR_TYPE NUM
                (PAIR_TYPE (SPTREE_SPT_TYPE UNIT_TYPE)
                (PAIR_TYPE (OPTION_TYPE NUM)
                (PAIR_TYPE ord_TYPE
                  (LIST_TYPE (PAIR_TYPE STRING_TYPE spo_TYPE)))))))
              res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧
          check_cstep_list cstep chk ord obj bound core fmlls inds id orders = NONE)))
Proof
  rw[]>>
  xcf "check_cstep_arr" (get_ml_prog_state ())>>
  rw[check_cstep_list_def]>>
  Cases_on`cstep`>>fs[NPBC_CHECK_CSTEP_TYPE_def]
  >- ( (* Dom*)
    xmatch>>
    Cases_on`ord`>>fs[ord_TYPE_def,OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    pairarg_tac>>xlet_autop>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    fs[spo_TYPE_def,ord_TYPE_def,constraint_TYPE_def]>>
    rpt xlet_autop>>
    rename1`do_dso spo _ _ _`>>
    xlet`(POSTve
      (λv.
        ARRAY fmlv fmllsv *
        &(case extract_clauses_list s fmlls (do_dso spo s p' obj) l [] of
            NONE => F
          | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE (PAIR_TYPE (LIST_TYPE constraint_TYPE) NUM)) (LIST_TYPE NPBC_CHECK_LSTEP_TYPE)) res v))
    (λe.
      ARRAY fmlv fmllsv *
      & (Fail_exn e ∧ extract_clauses_list s fmlls (do_dso spo s p' obj) l [] = NONE)))`
    >- (
      xapp>>xsimpl>>
      simp[LIST_TYPE_def,constraint_TYPE_def]>>
      metis_tac[])
    >- (
      xsimpl>>
      simp[do_dso_def]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>TOP_CASE_TAC>>simp[]>>
    fs[do_dso_def]>>
    strip_tac>>
    rpt xlet_autop>>
    xlet_auto>>
    rpt xlet_autop>>
    fs[GSYM constraint_TYPE_def]>>
    rename1`_ (not n) vvv`>>
    `LIST_REL (OPTION_TYPE constraint_TYPE)
      (update_resize fmlls NONE (SOME (not n)) id)
      (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
              (Conv (SOME (TypeStamp "Some" 2)) [vvv]) id)` by
      (match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def,constraint_TYPE_def])>>
    xlet_autop
    >- (
      xsimpl>>rw[]>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    Cases_on`x'`>>simp[PAIR_TYPE_def]>>
    strip_tac>>
    xmatch>>
    rename1`do_dom_check idopt _`>>
    Cases_on`idopt`>>
    fs[OPTION_TYPE_def,do_dom_check_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      fs[constraint_TYPE_def]>>
      xlet_autop>>
      fs[GSYM constraint_TYPE_def]>>
      xlet_autop>>
      reverse xif>>gs[]
      >- (
        rpt xlet_autop>>
        fs[red_cond_check_def]>>pairarg_tac>>fs[core_subgoals_def]>>
        xraise>>xsimpl>>
        fs[red_cond_check_def]>>rw[]>>
        metis_tac[ARRAY_refl,Fail_exn_def,NOT_EVERY])>>
      rpt xlet_autop>>
      xlet_auto>>
      pairarg_tac>>fs[red_cond_check_def,core_subgoals_def]>>
      xcon>>
      xsimpl>>rw[]>>
      fs[PAIR_TYPE_def,OPTION_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
      qexists_tac`A`>>xsimpl>>
      unabbrev_all_tac>>
      match_mp_tac LIST_REL_update_resize>>
      fs[OPTION_TYPE_def,constraint_TYPE_def])>>
    rpt xlet_autop>>
    reverse xif
    >- (
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      rw[]>>fs[]>>
      metis_tac[ARRAY_refl,NOT_EVERY,Fail_exn_def]) >>
    rpt xlet_autop>>
    xlet_auto>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def]>>
    qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
    qexists_tac`A`>>xsimpl>>
    unabbrev_all_tac>>
    fs[OPTION_TYPE_def,constraint_TYPE_def]>>
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,constraint_TYPE_def])
  >- ( (* LoadOrder*)
    xmatch>>
    rpt xlet_autop>>
    Cases_on`ALOOKUP orders m`>>fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    fs[spo_TYPE_def]>>
    rpt xlet_autop>>
    reverse(IF_CASES_TAC)>>gs[]>>
    xif>>asm_exists_tac>>simp[]
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,ord_TYPE_def,OPTION_TYPE_def,spo_TYPE_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* UnloadOrder *)
    xmatch>>
    Cases_on`ord`>>fs[OPTION_TYPE_def,ord_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def,ARRAY_refl])>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    fs[PAIR_TYPE_def,ord_TYPE_def,OPTION_TYPE_def,spo_TYPE_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* StoreOrder *)
    xmatch>>
    xlet_autop>>
    simp[GSYM check_storeorder_def]>>
    IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      fs[PAIR_TYPE_def,ord_TYPE_def,OPTION_TYPE_def,spo_TYPE_def,LIST_TYPE_def,constraint_TYPE_def,check_storeorder_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xraise >> xsimpl>>
    fs[check_storeorder_def,Fail_exn_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* Transfer *)
    xmatch>>
    xlet_autop>>
    IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
    >- (
      reverse CONJ_TAC >-
        metis_tac[NOT_EXISTS,NOT_EVERY]>>
      rpt xlet_autop>>
      xcon>> xsimpl>>
      fs[PAIR_TYPE_def,ord_TYPE_def,OPTION_TYPE_def,spo_TYPE_def,LIST_TYPE_def,constraint_TYPE_def,do_transfer_def]>>
      metis_tac[ARRAY_refl,NOT_EXISTS,NOT_EVERY])>>
    rw[]>>
    rpt xlet_autop>>
    xraise >> xsimpl>>
    fs[Fail_exn_def]>>
    metis_tac[ARRAY_refl])
  >- ( (* CheckedDelete*)
    xmatch>>
    xlet_autop>>
    reverse(xif>>fs[all_core_every_def])
    >- (
      rpt xlet_autop>>
      qpat_x_assum`EXISTS _ _` mp_tac>>
      REWRITE_TAC [GSYM NOT_EVERY]>>
      strip_tac>>
      simp[]>>
      xraise >> xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    xif
    >- (
      rpt xlet_autop>>
      xraise >> xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xlet`POSTv v. ARRAY fmlv fmllsv * &(BOOL (ord = NONE) v)`
    >- (
      xapp_spec (mlbasicsProgTheory.eq_v_thm |> INST_TYPE [alpha |-> ``:((((int # num) list # num) list # num list # num list) # num list) option``])>>
      xsimpl>>
      first_x_assum (irule_at Any)>>
      qexists_tac`NONE`>>simp[OPTION_TYPE_def]>>
      rw[] >- metis_tac[EqualityType_ord_TYPE]>>
      EVAL_TAC)>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      fs[do_core_del_def,ord_TYPE_def,ord_TYPE_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    pairarg_tac>>fs[PAIR_TYPE_def]>>
    xmatch>>
    xif
    >- (
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      fs[do_core_del_def,ord_TYPE_def,ord_TYPE_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    xraise>>xsimpl>>
    metis_tac[Fail_exn_def,ARRAY_refl]
  )
  >- ( (* Sstep *)
    xmatch>>
    xlet_autop
    >- (
      xsimpl>>
      metis_tac[ARRAY_refl])>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x`>>simp[PAIR_TYPE_def]>>rw[]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl)
  >- ( (* Obj *)
    xmatch>>
    xlet_autop>>
    fs[constraint_TYPE_def]>>
    rpt xlet_autop>>
    Cases_on`check_obj obj bound s (coref_list core fmlls)`>>
    fs[OPTION_TYPE_def]>>xmatch
    >- (
      rpt xlet_autop>>
      xraise >> xsimpl>>
      fs[Fail_exn_def]>>
      metis_tac[ARRAY_refl])>>
    rpt xlet_autop>>
    fs[constraint_TYPE_def]>>
    xlet_auto>>
    xcon>>xsimpl>>
    simp[PAIR_TYPE_def,OPTION_TYPE_def]>>
    qmatch_goalsub_abbrev_tac`ARRAY _ A`>>
    qexists_tac`A`>>xsimpl>>
    unabbrev_all_tac>>
    match_mp_tac LIST_REL_update_resize>>
    fs[OPTION_TYPE_def,constraint_TYPE_def])
QED

val _ = export_theory();
