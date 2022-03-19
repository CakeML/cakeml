(*
  Refine pb_list to pb_array
*)
open preamble basis pb_constraintTheory pb_listTheory;

val _ = new_theory "pb_arrayProg"

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
        & (Fail_exn e ∧ check_cutting_list fmlls constr = NONE)))
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
      xraise>> xsimpl>>
      metis_tac[Fail_exn_def])>>
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
      xraise>>xsimpl>>
      simp[Fail_exn_def]>>metis_tac[])>>
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
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "list_delete_arr" (get_ml_prog_state()))
    [lsv; fmlv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) (list_delete_list ls fmlls) fmllsv') )
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
  every_less (mindel:num) cls ⇔ EVERY ($<= mindel) cls`

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
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "rollback_arr" (get_ml_prog_state()))
    [fmlv;startv; endv]
    (ARRAY fmlv fmllsv)
    (POSTv resv.
      &UNIT_TYPE () resv *
      SEP_EXISTS fmllsv'.
      ARRAY fmlv fmllsv' *
      &(LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) (rollback fmlls start end) fmllsv') )
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
  | Delete ls =>
      if every_less mindel ls then
        (list_delete_arr ls fml; (fml, (False, (id, inds))))
      else
        raise Fail (format_failure lno ("Deletion not permitted for constraint index < " ^ Int.toString mindel))
  | Con_1 c pf =>
    let val fml_not_c = Array.updateResize fml None id (Some (not_1 c)) in
      (case check_pbpsteps_arr lno pf fml_not_c inds id (id+1) of
        (fml', (True, (id' ,inds'))) =>
          let val u = rollback_arr fml' id id' in
            (Array.updateResize fml' None id' (Some c), (False, ((id'+1), sorted_insert id' inds')))
          end
      | _ => raise Fail (format_failure lno ("Subproof did not derive contradiction")))
    end
  | Cutting constr =>
    let val c = check_cutting_arr lno fml constr
        val fml' = Array.updateResize fml None id (Some c) in
      (fml', (False, (id+1,sorted_insert id inds)))
    end
  | _ => raise Fail (format_failure lno ("Proof step not supported"))
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

val PB_PRECONSTRAINT_LIT_TYPE_def = fetch "-" "PB_PRECONSTRAINT_LIT_TYPE_def";
val PB_CONSTRAINT_NPBC_TYPE_def = fetch "-" "PB_CONSTRAINT_NPBC_TYPE_def";

Theorem NUM_no_closures:
  (NUM n v ⇒ no_closures v) ∧
  (NUM n v ∧ NUM n' v' ⇒ (n=n' ⇔ v=v')) ∧
  (NUM n v ∧ NUM n' v' ⇒ types_match v v')
Proof
  mp_tac EqualityType_NUM_BOOL>>
  EVAL_TAC>>
  simp[]
QED

Theorem EqualityType_PB_PRECONSTRAINT_LIT_TYPE:
  EqualityType PB_PRECONSTRAINT_LIT_TYPE
Proof
  EVAL_TAC>>
  rw[]
  >- (
    Cases_on`x1`>>
    fs[PB_PRECONSTRAINT_LIT_TYPE_def]>>
    simp[no_closures_def]>>
    metis_tac[NUM_no_closures])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[PB_PRECONSTRAINT_LIT_TYPE_def]>>
    metis_tac[NUM_no_closures])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[PB_PRECONSTRAINT_LIT_TYPE_def]>>
    EVAL_TAC>>
    metis_tac[NUM_no_closures])
QED

Theorem LIST_TYPE_no_closures:
  (LIST_TYPE (PAIR_TYPE NUM PB_PRECONSTRAINT_LIT_TYPE) n v ⇒ no_closures v) ∧
  (LIST_TYPE (PAIR_TYPE NUM PB_PRECONSTRAINT_LIT_TYPE) n v ∧
   LIST_TYPE (PAIR_TYPE NUM PB_PRECONSTRAINT_LIT_TYPE) n' v' ⇒ (n=n' ⇔ v=v')) ∧
  (LIST_TYPE (PAIR_TYPE NUM PB_PRECONSTRAINT_LIT_TYPE) n v ∧
   LIST_TYPE (PAIR_TYPE NUM PB_PRECONSTRAINT_LIT_TYPE) n' v' ⇒ types_match v v')
Proof
  `EqualityType (LIST_TYPE (PAIR_TYPE NUM PB_PRECONSTRAINT_LIT_TYPE))` by
    (match_mp_tac EqualityType_LIST_TYPE>>
    metis_tac[EqualityType_PAIR_TYPE, EqualityType_NUM_BOOL,EqualityType_PB_PRECONSTRAINT_LIT_TYPE])>>
  pop_assum mp_tac>>
  EVAL_TAC>>simp[]>>
  metis_tac[]
QED

Theorem EqualityType_PB_CONSTRAINT_NPBC_TYPE:
  EqualityType PB_CONSTRAINT_NPBC_TYPE
Proof
  EVAL_TAC>>rw[]
  >- (
    Cases_on`x1`>>
    fs[PB_CONSTRAINT_NPBC_TYPE_def]>>
    simp[no_closures_def]>>
    metis_tac[NUM_no_closures, LIST_TYPE_no_closures])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[PB_CONSTRAINT_NPBC_TYPE_def]>>
    metis_tac[NUM_no_closures, LIST_TYPE_no_closures])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[PB_CONSTRAINT_NPBC_TYPE_def]>>
    EVAL_TAC>>
    metis_tac[NUM_no_closures, LIST_TYPE_no_closures])
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
        & (Fail_exn e ∧ check_pbpstep_list step fmlls inds mindel id = NONE)))) ∧
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
        & (Fail_exn e ∧ check_pbpsteps_list steps fmlls inds mindel id = NONE))))
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
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
        simp[Fail_exn_def]>>metis_tac[])>>
      xmatch >>
      xlet_autop>>
      reverse IF_CASES_TAC>>xif>>asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_pbpstep_list_def]>>
        xraise>>xsimpl>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
        simp[Fail_exn_def]>>metis_tac[])>>
      rpt xlet_autop>>
      simp[check_pbpstep_list_def]>>
      xcon>>xsimpl>>
      simp[PAIR_TYPE_def,BOOL_def]>>
      asm_exists_tac>>xsimpl>>
      EVAL_TAC)
    >- ( (* Delete *)
      fs[PB_CHECK_PBPSTEP_TYPE_def]>>
      xmatch>>
      xlet_autop>>
      fs[every_less_def]>>
      reverse IF_CASES_TAC >>
      gs[]>>xif>>
      asm_exists_tac>>simp[]
      >- (
        rpt xlet_autop>>
        simp[check_pbpstep_list_def]>>
        xraise>>xsimpl>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
        simp[Fail_exn_def]>>metis_tac[])>>
      rpt xlet_autop>>
      xcon>>xsimpl
      >- (
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      simp[check_pbpstep_list_def])
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
    >- ( (* Con *)
      fs[PB_CHECK_PBPSTEP_TYPE_def,check_pbpstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xlet_auto>>
      rpt xlet_autop>>
      (* for some reason xapp doesn't work?? *)
      first_x_assum drule>>
      qpat_x_assum`NUM lno lnov` assume_tac>>
      rpt(disch_then drule)>>
      `LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE)
        (update_resize fmlls NONE (SOME (not n)) id)
        (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
                (Conv (SOME (TypeStamp "Some" 2)) [v]) id)` by
        (match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def])>>
      rpt (disch_then drule)>>
      strip_tac>>
      xlet_autop
      >- (
        xsimpl>>
        rw[]>>xsimpl>>
        qexists_tac`x`>>qexists_tac`x'`>>
        xsimpl)>>
      pop_assum mp_tac>> TOP_CASE_TAC>>
      fs[]>>
      PairCases_on`x`>>fs[PAIR_TYPE_def]>>
      rw[] >> rename1`BOOL _ bv`
      >- (
        `bv = Conv (SOME (TypeStamp "True" 0)) []` by
          (qpat_x_assum`BOOL _ _` mp_tac>>
          EVAL_TAC>>simp[])>>
        xmatch>>
        rpt xlet_autop>>
        xlet_auto>>
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        qmatch_goalsub_abbrev_tac`ARRAY _ ls`>>
        qexists_tac`ls`>>xsimpl>>
        simp[Abbr`ls`]>>
        match_mp_tac LIST_REL_update_resize>>simp[OPTION_TYPE_def])>>
      `bv = Conv (SOME (TypeStamp "False" 0)) []` by
        (qpat_x_assum`BOOL _ _` mp_tac>>
        EVAL_TAC>>simp[])>>
      xmatch>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      qexists_tac`fmlv'`>>qexists_tac`fmllsv'`>>xsimpl>>
      metis_tac[Fail_exn_def])
    >- ( (* Red *)
      fs[PB_CHECK_PBPSTEP_TYPE_def,check_pbpstep_list_def]>>
      xmatch>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
      metis_tac[Fail_exn_def])
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
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
        simp[Fail_exn_def]>>metis_tac[])>>
      xlet_auto >-
        (xsimpl>>
        simp[EqualityType_PB_CONSTRAINT_NPBC_TYPE])>>
      xif>>rpt xlet_autop
      >- (
        xcon>>xsimpl>>
        simp[PAIR_TYPE_def]>>
        asm_exists_tac>>xsimpl)>>
      xraise>>
      xsimpl>>
      qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
      metis_tac[Fail_exn_def])
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
