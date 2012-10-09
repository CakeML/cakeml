open HolKernel bossLib boolLib countableLib countableTheory MiniMLTheory MiniMLTerminationTheory CompileTheory compileTerminationTheory lcsymtacs

val _ = new_theory"count_exp"

val [count_error_aux_inj_rwt]        = mk_count_aux_inj_rwt [``:error``]
val [count_lit_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:lit``]
val [count_error_result_aux_inj_rwt] = mk_count_aux_inj_rwt [``:error_result``]
val [count_result_aux_inj_rwt]       = mk_count_aux_inj_rwt [``:α result``]
val [count_opn_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:opn``]
val [count_opb_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:opb``]
val [count_op_aux_inj_rwt]           = mk_count_aux_inj_rwt [``:op``]
val [count_log_aux_inj_rwt]          = mk_count_aux_inj_rwt [``:log``]
val [count_pat_aux_inj_rwt] = let
  val tys  = [``:pat``]
  val ttac = SOME (
    WF_REL_TAC `measure pat_size` >>
    gen_tac >> Induct >>
    rw[pat_size_def] >>
    res_tac >> DECIDE_TAC )
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_exp_aux_inj_rwt] = let
  val tys = [``:exp``]
  val ttac = SOME (
    WF_REL_TAC `measure exp_size` >>
    srw_tac[ARITH_ss][exp1_size_thm,exp4_size_thm,exp6_size_thm] >>
    map_every (fn q => TRY (Q.ISPEC_THEN q IMP_RES_TAC listTheory.SUM_MAP_MEM_bound))
      [`exp2_size`,`exp_size`,`exp5_size`] >>
    fsrw_tac[ARITH_ss][exp_size_def])
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_v_aux_inj_rwt] = let
  val tys  = [``:v``]
  val ttac = SOME (
    WF_REL_TAC `measure v_size` >>
    srw_tac[ARITH_ss][v1_size_thm,v3_size_thm] >>
    map_every (fn q => TRY (Q.ISPEC_THEN q IMP_RES_TAC listTheory.SUM_MAP_MEM_bound))
      [`v2_size`,`v_size`] >>
    fsrw_tac[ARITH_ss][v_size_def] )
in mk_count_aux_inj_rwt_ttac tys ttac end

val [count_Cpat_aux_inj_rwt] = let
  val tys = [``:Cpat``]
  val ttac = SOME (
    WF_REL_TAC `measure Cpat_size` >>
    gen_tac >> Induct >>
    rw[Cpat_size_def] >>
    res_tac >> DECIDE_TAC )
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_Cprim2_aux_inj_rwt] = mk_count_aux_inj_rwt [``:Cprim2``]
val [count_Clprim_aux_inj_rwt] = mk_count_aux_inj_rwt [``:Clprim``]
val [count_Cexp_aux_inj_rwt] = let
  val tys = [``:Cexp``]
  val ttac = SOME (
    WF_REL_TAC `measure Cexp_size` >>
    srw_tac[ARITH_ss][Cexp5_size_thm,Cexp1_size_thm,Cexp3_size_thm] >>
    map_every (fn q => TRY (Q.ISPEC_THEN q IMP_RES_TAC listTheory.SUM_MAP_MEM_bound)) [`Cexp4_size`,`Cexp_size`,`Cexp2_size`] >>
    fsrw_tac[ARITH_ss][Cexp_size_def] )
in mk_count_aux_inj_rwt_ttac tys ttac end
val [count_Cv_aux_inj_rwt] = let
  val tys = [``:Cv``]
  val ttac = SOME (
    WF_REL_TAC `measure Cv_size` >>
    srw_tac[ARITH_ss][Cv1_size_thm,Cv3_size_thm] >>
    map_every (fn q => TRY (Q.ISPEC_THEN q IMP_RES_TAC listTheory.SUM_MAP_MEM_bound)) [`Cv2_size`,`Cv_size`] >>
    fsrw_tac[ARITH_ss][Cv_size_def] )
in mk_count_aux_inj_rwt_ttac tys ttac end

val countable_v = save_thm("countable_v",inj_rwt_to_countable count_v_aux_inj_rwt)
val countable_Cv = save_thm("countable_Cv",inj_rwt_to_countable count_Cv_aux_inj_rwt)

val _ = export_theory()
