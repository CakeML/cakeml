(*
  Refine pb_list to pb_array
*)
open preamble basis pb_constraintTheory pb_listTheory;

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

val r = translate OPTION_MAP2_DEF;

val r = translate get_var_def;
val r = translate term_lt_def;
val r = translate add_terms_def;
val r = translate add_lists_def;
val r = translate add_def;

val r = translate OPTION_MAP_DEF;

val r = translate pb_constraintTheory.multiply_def;

val mul_k_def = Define`
  mul_k k c = multiply c k`

val r = translate mul_k_def;

val r = translate pb_constraintTheory.div_ceiling_def;
val r = translate pb_constraintTheory.divide_def;

val divide_side = Q.prove(
  `∀x y. divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]) |> update_precondition

val r = translate pb_constraintTheory.saturate_def;

val r = translate pb_constraintTheory.weaken_aux_def;
val r = translate pb_constraintTheory.weaken_def;

val check_cutting_arr = process_topdecs`
  fun check_cutting_arr lno fml constr =
  case constr of
    Id n =>
    (case Array.lookup fml None n of
      None =>
        raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some c => c)
  | Add_1 c1 c2 =>
    add (check_cutting_arr lno fml c1) (check_cutting_arr lno fml c2)
  | Mul c k =>
    multiply (check_cutting_arr lno fml c) k
  | Div_1 c k =>
    if k <> 0 then
      divide (check_cutting_arr lno fml c) k
    else raise Fail (format_failure lno ("divide by zero"))
  | Sat c =>
    saturate (check_cutting_arr lno fml c)
  | Lit_1 l => Pbc [(1,l)] 0
  | Weak c var =>
    weaken (check_cutting_arr lno fml c) var` |> append_prog

val PB_CHECK_CONSTR_TYPE_def = fetch "-" "PB_CHECK_CONSTR_TYPE_def";

val PB_CONSTRAINT_NPBC_TYPE_def  = theorem "PB_CONSTRAINT_NPBC_TYPE_def"

Theorem check_cutting_arr_spec:
  ∀constr constrv lno lnov fmlls fmllsv fmlv.
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
  Induct_on`constr`>>
  xcf"check_cutting_arr"(get_ml_prog_state ())
  >- ( (* Id *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    xlet_auto>>
    `OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (any_el n fmlls NONE) v'` by (
      rw[any_el_ALT]>>
      fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    qpat_x_assum`v' = _` (assume_tac o SYM)>>
    TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>
    xmatch
    >- (
      rpt xlet_autop>>
      xraise>> xsimpl)>>
    xvar>>xsimpl)
  >- ( (* Add *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >- ( (* Mul *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop >- xsimpl>>
    last_x_assum kall_tac>>
    every_case_tac>>fs[]>>
    xapp>>xsimpl>>
    metis_tac[])
  >- ( (* Div *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>>
    reverse IF_CASES_TAC>>xif>>asm_exists_tac>>fs[]
    >- (
      rpt xlet_autop>>
      xraise>>xsimpl)>>
    xlet_autop>- xsimpl>>
    xapp>>xsimpl>>
    asm_exists_tac>>simp[]>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    metis_tac[])
  >- ( (* Sat *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp>> xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    metis_tac[])
  >- ( (* Lit *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    xcon>>xsimpl>>
    simp[PB_CONSTRAINT_NPBC_TYPE_def,LIST_TYPE_def,PAIR_TYPE_def])
  >> ( (* Weak *)
    fs[check_cutting_list_def,PB_CHECK_CONSTR_TYPE_def]>>
    xmatch>>
    xlet_autop>- xsimpl>>
    xapp>>xsimpl>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[]>>
    metis_tac[])
QED

val result = translate sorted_insert_def;

val r = translate pb_constraintTheory.negate_def;
val r = translate (pb_constraintTheory.lslack_def |> SIMP_RULE std_ss [MEMBER_INTRO]);
val r = translate (pb_constraintTheory.check_contradiction_def |> SIMP_RULE std_ss[LET_DEF]);

val check_pbpstep_arr = process_topdecs`
  fun check_pbpstep_arr lno step fml inds mindel id =
  case step of
    Contradiction n =>
      (case Array.lookup fml None n of
        None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
      | Some c =>
        if check_contradiction c
        then (fml, (True, (id, inds)))
        else raise Fail (format_failure lno ("constraint id not a contradiction")))
  | Check n c =>
    (case Array.lookup fml None n of
      None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
    | Some c' =>
      if c = c' then (fml, (False, (id, inds)))
      else raise Fail (format_failure lno ("constraint id check failed")))
  | Noop => (fml, (False, (id, inds)))
  | Cutting constr =>
    let val c = check_cutting_arr lno fml constr
        val fml' = Array.updateResize fml None id (Some c) in
      (fml', (False, (id+1,sorted_insert id inds)))
    end
  and check_pbpsteps_arr lno steps fml inds mindel id =
  case steps of
    [] => (fml, (False, (id, inds)))
  | s::ss =>
    case check_pbpstep_arr lno s fml inds mindel id of
      (fml', (False, (id', inds'))) =>
        check_pbpsteps_arr lno ss fml' inds' mindel id'
    | res => res` |> append_prog

val PB_CHECK_PBPSTEP_TYPE_def = theorem "PB_CHECK_PBPSTEP_TYPE_def";

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

Theorem check_pbpstep_arr_spec:
  (∀step fmlls inds mindel id stepv lno lnov idv indsv fmlv fmllsv mindelv.
  PB_CHECK_PBPSTEP_TYPE step stepv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_pbpstep_arr" (get_ml_prog_state()))
    [lnov; stepv; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_pbpstep_list step fmlls inds mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE BOOL (PAIR_TYPE NUM (LIST_TYPE NUM))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (check_pbpstep_list step fmlls inds mindel id = NONE)))) ∧
  (∀steps fmlls inds mindel id stepsv lno lnov idv indsv fmlv fmllsv mindelv.
  LIST_TYPE PB_CHECK_PBPSTEP_TYPE steps stepsv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_pbpsteps_arr" (get_ml_prog_state()))
    [lnov; stepsv; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_pbpsteps_list steps fmlls inds mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE BOOL (PAIR_TYPE NUM (LIST_TYPE NUM))) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (check_pbpsteps_list steps fmlls inds mindel id = NONE))))
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]>>fs[]
  >- (
    xcfs ["check_pbpstep_arr","check_pbpsteps_arr"] (get_ml_prog_state ())>>
    simp[Once check_pbpstep_list_def]>>
    Cases_on`step`
    >- ((* Contradiction *)
      fs[PB_CHECK_PBPSTEP_TYPE_def]>>
      xmatch>>
      xlet_autop>>
      xlet_auto>>
      `OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (any_el n fmlls NONE) v'` by (
         rw[any_el_ALT]>>
         fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
      qpat_x_assum`v' = _` (assume_tac o SYM)>>
      Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]
      >- (
        xmatch>>
        rpt xlet_autop>>
        simp[check_pbpstep_list_def]>>
        xraise>>xsimpl>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)>>
      xmatch >>
      xlet_autop>>
      reverse IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_pbpstep_list_def]>>
        xraise>>xsimpl>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)>>
      rpt xlet_autop>>
      simp[check_pbpstep_list_def]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,BOOL_def]>>
      asm_exists_tac>>xsimpl>>
      EVAL_TAC)
    >- (* Delete *) cheat
    >- ((* Cutting *)
      fs[PB_CHECK_PBPSTEP_TYPE_def,check_pbpstep_list_def]>>
      xmatch>>
      xlet_auto >- (
        xsimpl>>
        rw[]>>qexists_tac`fmlv`>>qexists_tac`fmllsv`>>
        xsimpl)>>
      rpt xlet_autop>>
      xlet_auto>>
      rpt xlet_autop>>
      every_case_tac>>fs[]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      qmatch_goalsub_abbrev_tac`ARRAY _ lss`>>
      qexists_tac`lss`>>xsimpl>>
      simp[Abbr`lss`]>>
      match_mp_tac LIST_REL_update_resize>>simp[]>>
      EVAL_TAC>>
      metis_tac[])
    >- ( (* Con *) cheat)
    >- ( (* Red *) cheat)
    >- ( (* Check *)
      fs[PB_CHECK_PBPSTEP_TYPE_def,check_pbpstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet_auto>>
      `OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (any_el n fmlls NONE) v'` by (
         rw[any_el_ALT]>>
         fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
      qpat_x_assum`v' = _` (assume_tac o SYM)>>
      Cases_on`any_el n fmlls NONE`>>fs[OPTION_TYPE_def]>>
      xmatch
      >- (
        rpt xlet_autop>>
        xraise>>
        xsimpl>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)>>
      xlet_auto >-
        (xsimpl>>
        (* prove equality type *)
        cheat)>>
      xif>>rpt xlet_autop
      >- (
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      xraise>>
      xsimpl>>
      qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl)
    >- ( (*No Op*)
      fs[PB_CHECK_PBPSTEP_TYPE_def,check_pbpstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl))
  >- (
    xcfs ["check_pbpstep_arr","check_pbpsteps_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop>>
    simp[Once check_pbpstep_list_def]>>
    xcon>>xsimpl
    >- (
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl)>>
    simp[Once check_pbpstep_list_def])
  >>
    xcfs ["check_pbpstep_arr","check_pbpsteps_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_autop
    >- (
      xsimpl>>
      rw[]>>simp[Once check_pbpstep_list_def]>>
      qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
    pop_assum mp_tac>>TOP_CASE_TAC>>strip_tac>>
    PairCases_on`x`>>fs[PAIR_TYPE_def]>>
    rename1`BOOL _ bv`>>
    `x1 ∧ bv = Conv (SOME (TypeStamp "True" 0)) [] ∨ ¬x1 ∧ bv = Conv (SOME (TypeStamp "False" 0)) []` by
      (qpat_x_assum`BOOL _ _` mp_tac>>
      Cases_on`x1`>>EVAL_TAC>>simp[])
    >- (
      xmatch>>xvar>>xsimpl>>
      simp[Once check_pbpstep_list_def,PAIR_TYPE_def]>>
      xsimpl )>>
    xmatch>>
    xapp>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    rw[]>>simp[Once check_pbpstep_list_def]
    >- (
      every_case_tac>>fs[]>>asm_exists_tac>>
      xsimpl)>>
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl
QED

val _ = export_theory();
