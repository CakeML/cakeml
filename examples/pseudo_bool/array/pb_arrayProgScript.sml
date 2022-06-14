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
  strlit "c Checking failed for top-level proof step starting at line: " ^ toString lno ^ strlit ". Reason: " ^ s ^ strlit"\n"`

val r = translate format_failure_def;

val r = translate OPTION_MAP2_DEF;

val r = translate get_var_def;
val r = translate listTheory.REV_DEF;
val r = translate term_lt_def;

val r = translate offset_def;
val r = translate add_terms_def;
val r = translate add_lists'_def;
val r = translate add_lists'_thm;
val r = translate add_def;

val r = translate OPTION_MAP_DEF;

val r = translate pb_constraintTheory.multiply_def;

val mul_k_def = Define`
  mul_k k c = multiply c k`

val r = translate mul_k_def;

val r = translate IQ_def;

val r = translate pb_constraintTheory.div_ceiling_def;

val r = translate arithmeticTheory.CEILING_DIV_def ;
val r = translate pb_constraintTheory.divide_def;

val divide_side = Q.prove(
  `∀x y. divide_side x y ⇔ y ≠ 0`,
  Cases>>
  EVAL_TAC>>
  rw[EQ_IMP_THM]>>
  intLib.ARITH_TAC
  ) |> update_precondition

val r = translate pb_constraintTheory.abs_min_def;
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
      Pos v => (Pbc [(1,v)] 0)
    | Neg v => (Pbc [(~1,v)] 0))
  | Weak c var =>
    weaken (check_cutting_arr lno fml c) var` |> append_prog

val PB_CHECK_CONSTR_TYPE_def = fetch "-" "PB_CHECK_CONSTR_TYPE_def";

val PB_CONSTRAINT_NPBC_TYPE_def  = theorem "PB_CONSTRAINT_NPBC_TYPE_def"
val PB_PRECONSTRAINT_LIT_TYPE_def = fetch "-" "PB_PRECONSTRAINT_LIT_TYPE_def";

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
  Induct_on`constr` >> rw[]>>
  xcf "check_cutting_arr" (get_ml_prog_state ())
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
    Cases_on`l`>>fs[PB_PRECONSTRAINT_LIT_TYPE_def]>>xmatch>>
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
val r = translate (pb_constraintTheory.lslack_def |> SIMP_RULE std_ss [MEMBER_INTRO, o_DEF]);
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

val reindex_arr = process_topdecs `
  fun reindex_arr fml ls =
  case ls of
    [] => []
  | (i::is) =>
  case Array.lookup fml None i of
    None => reindex_arr fml is
  | Some v =>
    (i :: reindex_arr fml is)` |> append_prog;

Theorem reindex_arr_spec:
  ∀inds indsv fmlls fmlv.
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "reindex_arr" (get_ml_prog_state()))
    [fmlv; indsv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE NUM (reindex fmlls inds) v))
Proof
  Induct>>
  xcf"reindex_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xcon>>xsimpl>>
    simp[reindex_def,LIST_TYPE_def])>>
  xmatch>>
  xlet_auto>- (xcon>>xsimpl)>>
  xlet_auto>>
  `OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  rw[]>>
  simp[reindex_def]>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]>>xmatch
  >-
    (xapp>>simp[])>>
  xlet_autop>>
  xcon>>xsimpl>>
  simp[LIST_TYPE_def]
QED

val res = translate pb_constraintTheory.is_Pos_def;
val res = translate pb_constraintTheory.subst_aux_def;
val res = translate pb_constraintTheory.partition_def;
val res = translate pb_constraintTheory.clean_up_def;
val res = translate pb_constraintTheory.subst_def;
val res = translate lookup_def;
val res = translate pb_checkTheory.subst_fun_def;
val res = translate subst_subst_fun_def;

val extract_clauses_arr = process_topdecs`
  fun extract_clauses_arr lno s def fml pfs acc =
  case pfs of [] => List.rev acc
  | cpf::pfs =>
    case cpf of
      (None,pf) => extract_clauses_arr lno s def fml pfs ((None,pf)::acc)
    | (Some (Inl n),pf) =>
      (case Array.lookup fml None n of
        None => raise Fail (format_failure lno ("invalid constraint id: " ^ Int.toString n))
      | Some c => extract_clauses_arr lno s def fml pfs ((Some (subst_subst_fun s c),pf)::acc))
    | (Some (Inr u),pf) =>
      extract_clauses_arr lno s def fml pfs ((Some (subst_subst_fun s def),pf)::acc)` |> append_prog;

Theorem extract_clauses_arr_spec:
  ∀pfs pfsv s sv def defv fmlls fmlv fmllsv acc accv lno lnov.
  NUM lno lnov ∧
  (SPTREE_SPT_TYPE (SUM_TYPE BOOL PB_PRECONSTRAINT_LIT_TYPE)) s sv ∧
  PB_CONSTRAINT_NPBC_TYPE def defv ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)) pfs pfsv ∧
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)) acc accv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "extract_clauses_arr" (get_ml_prog_state()))
    [lnov; sv; defv; fmlv; pfsv; accv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        ARRAY fmlv fmllsv *
        &(case extract_clauses_list s def fmlls pfs acc of
            NONE => F
          | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)) res v))
      (λe.
        ARRAY fmlv fmllsv *
        & (Fail_exn e ∧ extract_clauses_list s def fmlls pfs acc = NONE)))
Proof
  Induct>>
  xcf"extract_clauses_arr"(get_ml_prog_state ())>>
  fs[LIST_TYPE_def]
  >- (
    xmatch>>
    xapp_spec (ListProgTheory.reverse_v_thm |> INST_TYPE [alpha |-> ``:(npbc option # pbpstep list) ``])>>
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
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    asm_exists_tac>>xsimpl>>
    first_x_assum (irule_at Any)>>simp[]>>
    qexists_tac`(NONE,r)::acc`>>
    simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def])>>
  Cases_on`x`>>fs[SUM_TYPE_def]>>xmatch
  >- (
    xlet_autop>>
    xlet_auto>>
    `OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (any_el x' fmlls NONE) v'` by (
       rw[any_el_ALT]>>
       fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
    qpat_x_assum`v' = _` (assume_tac o SYM)>>
    Cases_on`any_el x' fmlls NONE`>>fs[OPTION_TYPE_def]
    >- (
      xmatch>>
      rpt xlet_autop>>
      xraise>>
      xsimpl>>
      simp[extract_clauses_list_def]>>
      metis_tac[Fail_exn_def])>>
    xmatch>>
    rpt xlet_autop>>
    xapp>>
    xsimpl>>
    rpt(asm_exists_tac>>simp[])>>
    first_x_assum (irule_at Any)>>simp[]>>
    qexists_tac`(SOME (subst_subst_fun s x),r)::acc`>>simp[extract_clauses_list_def]>>
    simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def])>>
  rpt xlet_autop>>
  xapp>>
  xsimpl>>
  asm_exists_tac>>xsimpl>>
  asm_exists_tac>>xsimpl>>
  first_x_assum (irule_at Any)>>simp[]>>
  first_x_assum (irule_at Any)>>simp[]>>
  qexists_tac`(SOME (subst_subst_fun s def),r)::acc`>>simp[extract_clauses_list_def]>>
  simp[LIST_TYPE_def,PAIR_TYPE_def,OPTION_TYPE_def]
QED

val res = translate subst_opt_aux_def;
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
    | Some c => i::subst_indexes_arr s fml is))` |> append_prog;

Theorem subst_indexes_arr_spec:
  ∀is isv s sv fmlls fmlv.
  (SPTREE_SPT_TYPE (SUM_TYPE BOOL PB_PRECONSTRAINT_LIT_TYPE)) s sv ∧
  LIST_TYPE NUM is isv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "subst_indexes_arr" (get_ml_prog_state()))
    [sv; fmlv; isv]
    (ARRAY fmlv fmllsv)
    (POSTv v.
      ARRAY fmlv fmllsv *
      &(LIST_TYPE NUM (subst_indexes s fmlls is) v))
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
  `OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE (any_el h fmlls NONE) v'` by (
   rw[any_el_ALT]>>
   fs[LIST_REL_EL_EQN,OPTION_TYPE_def])>>
  qpat_x_assum`v' = _` (assume_tac o SYM)>>
  simp[subst_indexes_def]>>
  Cases_on`any_el h fmlls NONE`>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>xapp>>
    metis_tac[])>>
  xmatch>>
  xlet_autop>>
  TOP_CASE_TAC>>fs[OPTION_TYPE_def]
  >- (
    xmatch>>xapp>>
    metis_tac[])>>
  xmatch>>
  xlet_autop>>
  xcon>>
  xsimpl>>
  simp[LIST_TYPE_def]
QED

val res = translate pb_checkTheory.is_pol_con_def;

Definition all_goals_def:
  all_goals pids ls ⇔
  EVERY (λid. MEM (SOME (INL id)) pids) ls
End

val res = translate (all_goals_def |> SIMP_RULE std_ss [MEMBER_INTRO]);

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
  | Con c pf =>
    let val fml_not_c = Array.updateResize fml None id (Some (not_1 c)) in
      (case check_pbpsteps_arr lno pf fml_not_c (sorted_insert id inds) id (id+1) of
        (fml', (True, (id' ,inds'))) =>
          let val u = rollback_arr fml' id id' in
            (Array.updateResize fml' None id' (Some c), (False, ((id'+1), sorted_insert id' inds)))
          end
      | _ => raise Fail (format_failure lno ("Subproof did not derive contradiction")))
    end
  | Red c s pfs =>
    (let val rinds = reindex_arr fml inds
         val cpfs = extract_clauses_arr lno s c fml pfs []
         val fml_not_c = Array.updateResize fml None id (Some (not_1 c)) in
         case check_redundancy_arr lno cpfs fml_not_c (sorted_insert id rinds) id (id+1) of
           (fml', (id', inds')) =>
           let val u = rollback_arr fml' id id'
               val pids = List.map fst pfs in
               if List.member (Some (Inr ())) pids andalso
                 all_goals pids (subst_indexes_arr s fml' rinds)
               then
                 (Array.updateResize fml' None id' (Some c), (False, ((id'+1), sorted_insert id' rinds)))
               else raise Fail (format_failure lno ("Redundancy subproofs did not cover all subgoals"))
           end
    end)
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
    | res => res
  and check_redundancy_arr lno pfs fml inds mindel id =
  case pfs of
    [] => (fml,(id,inds))
  | cpf::pfs => case cpf of (copt,pf) =>
    (case copt of
      None =>
      (if not (List.all is_pol_con pf) then
        raise Fail (format_failure lno ("Redundancy subproof steps must be satisfiability preserving."))
      else
      case check_pbpsteps_arr lno pf fml inds mindel id of
        (fml', (False, (id', inds'))) => check_redundancy_arr lno pfs fml' inds' mindel id'
      | res => raise Fail (format_failure lno ("Shared subproof steps ended in contradiction.")))
    | Some c =>
      let val cfml = Array.updateResize fml None id (Some (not_1 c)) in
        case check_pbpsteps_arr lno pf cfml (sorted_insert id inds) id (id+1) of
          (fml', (True, (id', inds'))) =>
          let val u = rollback_arr fml' id id' in
            check_redundancy_arr lno pfs fml' inds' mindel id'
          end
        | _ =>  raise Fail (format_failure lno ("Subproof did not derive contradiction."))
      end)
  ` |> append_prog

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
  (LIST_TYPE (PAIR_TYPE INT NUM) n v ⇒ no_closures v) ∧
  (LIST_TYPE (PAIR_TYPE INT NUM) n v ∧
   LIST_TYPE (PAIR_TYPE INT NUM) n' v' ⇒ (n=n' ⇔ v=v')) ∧
  (LIST_TYPE (PAIR_TYPE INT NUM) n v ∧
   LIST_TYPE (PAIR_TYPE INT NUM) n' v' ⇒ types_match v v')
Proof
  `EqualityType (LIST_TYPE (PAIR_TYPE INT NUM))` by
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

Theorem EqualityType_OPTION_TYPE:
  EqualityType t ⇒
  EqualityType (OPTION_TYPE t)
Proof
  EVAL_TAC>>rw[]
  >- (
    Cases_on`x1`>>fs[OPTION_TYPE_def]>>
    simp[no_closures_def]>>
    metis_tac[])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[OPTION_TYPE_def])>>
  Cases_on`x1`>>Cases_on`x2`>>
  fs[OPTION_TYPE_def]>>
  EVAL_TAC>>
  metis_tac[]
QED

Theorem EqualityType_SUM_TYPE:
  EqualityType t1 ∧ EqualityType t2 ⇒
  EqualityType (SUM_TYPE t1 t2)
Proof
  EVAL_TAC>>rw[]
  >- (
    Cases_on`x1`>>fs[SUM_TYPE_def]>>
    simp[no_closures_def]>>
    metis_tac[])
  >- (
    Cases_on`x1`>>Cases_on`x2`>>
    fs[SUM_TYPE_def])>>
  Cases_on`x1`>>Cases_on`x2`>>
  fs[SUM_TYPE_def]>>
  EVAL_TAC>>
  metis_tac[]
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
        & (Fail_exn e ∧ check_pbpsteps_list steps fmlls inds mindel id = NONE)))) ∧
  (∀pfs fmlls inds mindel id pfsv lno lnov idv indsv fmlv fmllsv mindelv.
  LIST_TYPE (PAIR_TYPE (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)) pfs pfsv ∧
  NUM lno lnov ∧
  NUM mindel mindelv ∧
  NUM id idv ∧
  LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) fmlls fmllsv ∧
  (LIST_TYPE NUM) inds indsv
  ⇒
  app (p : 'ffi ffi_proj)
    ^(fetch_v "check_redundancy_arr" (get_ml_prog_state()))
    [lnov; pfsv; fmlv; indsv; mindelv; idv]
    (ARRAY fmlv fmllsv)
    (POSTve
      (λv.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        &(
          case check_redundancy_list pfs fmlls inds mindel id of NONE => F
          | SOME res =>
            PAIR_TYPE (λl v.
              LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) l fmllsv' ∧
              v = fmlv') (PAIR_TYPE NUM (LIST_TYPE NUM)) res v
          ))
      (λe.
        SEP_EXISTS fmlv' fmllsv'.
        ARRAY fmlv' fmllsv' *
        & (Fail_exn e ∧ check_redundancy_list pfs fmlls inds mindel id = NONE))))
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]>>fs[]
  >- (
    xcfs ["check_pbpstep_arr","check_pbpsteps_arr","check_redundancy_arr"] (get_ml_prog_state ())>>
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
      disch_then drule>>
      disch_then drule>>
      strip_tac>>
      xlet_auto
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
      xlet_auto>>
      rpt xlet_autop>>
      qmatch_goalsub_abbrev_tac`ARRAY aa vv`>>
      xlet`(POSTve
      (λv.
        ARRAY aa vv *
        &(case extract_clauses_list s n fmlls l [] of
            NONE => F
          | SOME res => LIST_TYPE (PAIR_TYPE (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) (LIST_TYPE PB_CHECK_PBPSTEP_TYPE)) res v))
      (λe.
        ARRAY aa vv *
        & (Fail_exn e ∧ extract_clauses_list s n fmlls l [] = NONE)))`
      >- (
        xapp>>xsimpl>>
        simp[LIST_TYPE_def]>>metis_tac[])
      >- (
        xsimpl>>
        rw[]>>
        qexists_tac`aa`>>qexists_tac`fmllsv`>>xsimpl)>>
      rpt xlet_autop>>
      xlet_auto>>
      rpt xlet_autop>>
      Cases_on`extract_clauses_list s n fmlls l []` >> fs[]>>
      first_x_assum drule>>
      disch_then(qspecl_then[`lno`,`lnov`] mp_tac)>>
      rpt (disch_then drule)>>
      rename1`PB_CONSTRAINT_NPBC_TYPE (not n) vvv`>>
      `LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE)
        (update_resize fmlls NONE (SOME (not n)) id)
        (update_resize fmllsv (Conv (SOME (TypeStamp "None" 2)) [])
                (Conv (SOME (TypeStamp "Some" 2)) [vvv]) id)` by
        (match_mp_tac LIST_REL_update_resize>>fs[OPTION_TYPE_def])>>
      disch_then drule>>
      disch_then drule>>
      strip_tac>>
      xlet`(POSTve
               (λv.
                    SEP_EXISTS fmlv' fmllsv'.
                      ARRAY fmlv' fmllsv' *
                      &case
                        check_redundancy_list x
                          (update_resize fmlls NONE (SOME (not n)) id)
                          (sorted_insert id (reindex fmlls inds)) id (id + 1)
                      of
                        NONE => F
                      | SOME res =>
                        PAIR_TYPE
                          (λl v.
                               LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE)
                                 l fmllsv' ∧ v = fmlv')
                          (PAIR_TYPE NUM (LIST_TYPE NUM)) res v)
               (λe.
                    SEP_EXISTS fmlv' fmllsv'.
                      ARRAY fmlv' fmllsv' *
                      &(Fail_exn e ∧
                       check_redundancy_list x
                         (update_resize fmlls NONE (SOME (not n)) id)
                         (sorted_insert id (reindex fmlls inds)) id (id + 1) =
                       NONE)))`
      >-
        (xapp>>xsimpl)
      >- (
        xsimpl>>
        rw[]>>simp[]>>
        qexists_tac`x'`>>qexists_tac`x''`>>xsimpl)>>
      pop_assum mp_tac>>
      TOP_CASE_TAC>>simp[]>>
      rename1`PAIR_TYPE _ _ xx _`>>
      PairCases_on`xx`>>fs[PAIR_TYPE_def]>>
      strip_tac>>fs[]>>
      xmatch>>
      rpt xlet_autop>>
      xlet`POSTv v. ARRAY fmlv' fmllsv'' * &LIST_TYPE (OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE)) (MAP FST l) v`
      >- (
        xapp_spec (ListProgTheory.map_1_v_thm |> INST_TYPE [alpha |-> ``:(num + unit) option``, beta |-> ``:(num + unit) option # pbpstep list``])>>
        xsimpl>>
        asm_exists_tac>>xsimpl>>
        qexists_tac`FST`>>qexists_tac`(OPTION_TYPE (SUM_TYPE NUM UNIT_TYPE))`>>
        rw[]>>
        simp[fst_v_thm])>>
      rpt xlet_autop>>
      xlet`POSTv v. ARRAY fmlv' fmllsv'' * &BOOL (MEM (SOME (INR ())) (MAP FST l)) v`
      >- (
        xapp_spec (ListProgTheory.member_v_thm |> INST_TYPE [alpha |-> ``:(num + unit) option``])>>
        xsimpl>>simp[MEMBER_INTRO]>>
        first_x_assum (irule_at Any)>>simp[OPTION_TYPE_def]>>
        qexists_tac`SOME (INR ())`>>simp[OPTION_TYPE_def,SUM_TYPE_def]>>
        match_mp_tac EqualityType_OPTION_TYPE>>
        match_mp_tac  EqualityType_SUM_TYPE>>
        fs[EqualityType_NUM_BOOL])>>
      xlet`POSTv v. ARRAY fmlv' fmllsv'' * &BOOL (MEM (SOME (INR ())) (MAP FST l) ∧
                        EVERY (λid. MEM (SOME (INL id)) (MAP FST l))
                          (subst_indexes s (rollback xx0 id xx1)
                             (reindex fmlls inds))) v`
      >- (
        xlog>>rw[]>>fs[]>>xsimpl>>
        rpt xlet_autop>>
        xapp_spec (fetch "-" "all_goals_v_thm" |> INST_TYPE [alpha |-> ``:num``, beta |-> ``:unit``])>>
        xsimpl>>
        first_x_assum (irule_at Any)>>xsimpl>>
        first_x_assum (irule_at Any)>>xsimpl>>
        simp[EqualityType_NUM_BOOL,all_goals_def])>>
      IF_CASES_TAC>>fs[]
      >- (
        xif>>asm_exists_tac>>xsimpl>>
        rpt xlet_autop>>
        xlet_auto>>
        xcon>>xsimpl
        >- (
          simp[PAIR_TYPE_def]>>
          qmatch_goalsub_abbrev_tac`ARRAY _ vvvv`>>
          qexists_tac`vvvv`>>xsimpl>>
          simp[Abbr`vvvv`]>>
          match_mp_tac LIST_REL_update_resize>>
          simp[OPTION_TYPE_def])>>
        rw[]>>
        metis_tac[NOT_EXISTS,NOT_EVERY])
      >- (
        xif>>asm_exists_tac>>xsimpl>>
        rpt xlet_autop>>
        xraise>>xsimpl>>
        rw[]>>
        qexists_tac`fmlv'`>>qexists_tac`fmllsv''`>>xsimpl>>metis_tac[Fail_exn_def])>>
      xif>>asm_exists_tac>>xsimpl>>
      rw[]
      >- metis_tac[NOT_EXISTS,NOT_EVERY]>>
      rpt xlet_autop>>
      xraise>>xsimpl>>
      rw[]>>
      qexists_tac`fmlv'`>>qexists_tac`fmllsv''`>>xsimpl>>metis_tac[Fail_exn_def])
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
  >- (
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
    qexists_tac`x`>>qexists_tac`x'`>>xsimpl)
  >- (
    xcfs ["check_pbpsteps_arr","check_redundancy_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    rpt xlet_auto >>
    simp[Once check_pbpstep_list_def]>>
    xcon>>xsimpl
    >- (
      simp[PAIR_TYPE_def]>>
      asm_exists_tac>>xsimpl)>>
    simp[Once check_pbpstep_list_def])
  >- (
    xcfs ["check_pbpsteps_arr","check_redundancy_arr"] (get_ml_prog_state ())>>
    fs[LIST_TYPE_def]>>
    xmatch>>
    fs[PAIR_TYPE_def]>>
    xmatch>>
    simp[Once check_pbpstep_list_def]>>
    Cases_on`copt`>>fs[OPTION_TYPE_def]
    >- (
      xmatch>>
      xlet`POSTv v. &BOOL (EVERY is_pol_con steps') v * ARRAY fmlv fmllsv`
      >- (
        xapp_spec (ListProgTheory.every_v_thm |> INST_TYPE [alpha |-> ``:pbpstep``])>>
        xsimpl>>
        asm_exists_tac>>qexists_tac`is_pol_con`>>simp[fetch "-" "is_pol_con_v_thm"])>>
      xlet_autop>>
      IF_CASES_TAC
      >- (
        fs[]>> xif>>
        asm_exists_tac>>simp[]>>
        rpt xlet_autop>>
        xraise>>xsimpl>>
        simp[Once check_pbpstep_list_def]>>
        qexists_tac`fmlv`>>qexists_tac`fmllsv`>>xsimpl>>
        metis_tac[Fail_exn_def])>>
      fs[]>>xif>>
      asm_exists_tac>>simp[]>>
      rw[]
      >- metis_tac[NOT_EXISTS]>>
      fs[o_DEF,ETA_AX]>>
      xlet_auto >- simp[]
      >- (
        xsimpl>>
        simp[Once check_pbpstep_list_def]>>
        rw[]>>
        qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
      pop_assum mp_tac>>
      TOP_CASE_TAC>>
      rw[]>>
      PairCases_on`x`>>fs[PAIR_TYPE_def]>>
      rename1`BOOL x1 bvv`>>
      `x1 ∧ bvv = Conv (SOME (TypeStamp "True" 0)) [] ∨ ¬x1 ∧ bvv = Conv (SOME (TypeStamp "False" 0)) []` by
        (qpat_x_assum`BOOL _ _` mp_tac>>
        Cases_on`x1`>>EVAL_TAC>>simp[])
      >- (
        xmatch>>
        rpt xlet_autop>>
        xraise>>
        xsimpl>>
        simp[Once check_pbpstep_list_def]>>
        qexists_tac`fmlv'`>>qexists_tac`fmllsv'`>>xsimpl>>
        metis_tac[Fail_exn_def])>>
      xmatch>>
      fs[]>>
      xapp>>
      simp[PULL_EXISTS]>>
      asm_exists_tac>>simp[]>>
      qexists_tac`emp`>>qexists_tac`fmllsv'`>>xsimpl>>
      simp[Once check_pbpstep_list_def]>>
      rw[]>>
      qexists_tac`x`>>qexists_tac`x'`>>xsimpl)>>
    xmatch>>
    rpt xlet_autop>>
    xlet_auto>>
    rpt xlet_autop>>
    first_x_assum drule>>
    disch_then(qspec_then`lno` mp_tac)>>
    rpt (disch_then drule)>>
    rename1`LIST_TYPE _ (sorted_insert _ _) sindsv`>>
    disch_then(qspecl_then [`sindsv`] mp_tac)>>
    qmatch_goalsub_abbrev_tac`ARRAY afmlv afml`>>
    disch_then(qspecl_then [`afmlv`,`afml`] mp_tac)>>
    impl_tac>- (
      unabbrev_all_tac>>simp[]>>
      match_mp_tac LIST_REL_update_resize>>simp[OPTION_TYPE_def])>>
    strip_tac>>
    xlet`(POSTve
             (λv.
                  SEP_EXISTS fmlv' fmllsv'.
                    ARRAY fmlv' fmllsv' *
                    &case
                      check_pbpsteps_list steps'
                        (update_resize fmlls NONE (SOME (not x)) id)
                        (sorted_insert id inds) id (id + 1)
                    of
                      NONE => F
                    | SOME res =>
                      PAIR_TYPE
                        (λl v.
                             LIST_REL (OPTION_TYPE PB_CONSTRAINT_NPBC_TYPE) l
                               fmllsv' ∧ v = fmlv')
                        (PAIR_TYPE BOOL (PAIR_TYPE NUM (LIST_TYPE NUM))) res
                        v)
             (λe.
                  SEP_EXISTS fmlv' fmllsv'.
                    ARRAY fmlv' fmllsv' *
                    &(Fail_exn e ∧
                     check_pbpsteps_list steps'
                       (update_resize fmlls NONE (SOME (not x)) id)
                       (sorted_insert id inds) id (id + 1) = NONE)))`
    >-
      xapp
    >- (
      xsimpl>>
      rw[]>>simp[Once check_pbpstep_list_def]>>
      qexists_tac`x'`>>qexists_tac`x''`>>xsimpl)>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>
    PairCases_on`x'`>>simp[PAIR_TYPE_def]>>
    strip_tac>>
    rename1`BOOL x1 bvv`>>
    `x1 ∧ bvv = Conv (SOME (TypeStamp "True" 0)) [] ∨ ¬x1 ∧ bvv = Conv (SOME (TypeStamp "False" 0)) []` by
      (qpat_x_assum`BOOL _ _` mp_tac>>
      Cases_on`x1`>>EVAL_TAC>>simp[])
    >- (
      xmatch>>
      xlet_autop>>
      xapp>>xsimpl>>
      asm_exists_tac>>simp[]>>
      simp[Once check_pbpstep_list_def]>>
      rw[]>>
      qexists_tac`x'`>>qexists_tac`x''`>>xsimpl)>>
    xmatch>>
    rpt xlet_autop>>
    xraise>>
    xsimpl>>
    simp[Once check_pbpstep_list_def]>>
    qexists_tac`fmlv'`>>qexists_tac`fmllsv'`>>xsimpl>>
    metis_tac[Fail_exn_def])
QED

val _ = export_theory();
