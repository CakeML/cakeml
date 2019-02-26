(*
  Tactics for reasoning about divergent programs
*)
structure cfDivLib =
struct

open cfTacticsLib cfNormaliseTheory cfDivTheory;

fun xcf_div_FFI_full name st =
  let
    val f_def = fetch_def name st
  in
    rpt strip_tac
    \\ simp[f_def]
    \\ match_mp_tac(GEN_ALL IMP_app_POSTd)
    (* TODO: we could look at the goal state and generate a fresh name instead*)
    \\ qmatch_goalsub_abbrev_tac `make_stepfun_closure highly_improbable_name`
    \\ CONV_TAC(QUANT_CONV(PATH_CONV "l" EVAL))
    \\ qunabbrev_tac `highly_improbable_name`
    \\ qmatch_goalsub_abbrev_tac `highly_improbable_name = _`
    \\ qexists_tac `highly_improbable_name`
    \\ conj_tac >- MATCH_ACCEPT_TAC(Q.REFL `highly_improbable_name`)
    \\ conj_tac >- EVAL_TAC
    \\ qunabbrev_tac `highly_improbable_name`
    \\ CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "rrl" (DEPTH_CONV naryClosure_repack_conv)))
    \\ CONSEQ_CONV_TAC(
          DEPTH_CONSEQ_CONV(
            ONCE_CONSEQ_REWRITE_CONV
              ([],[GEN_ALL(REWRITE_RULE [AND_IMP_INTRO] app_of_cf)],[])))
    \\ CONV_TAC(
          STRIP_QUANT_CONV(
            PATH_CONV "rrlr" (
              QUANT_CONV(
                RATOR_CONV(SIMP_CONV list_ss [])
                          THENC PURE_REWRITE_CONV [AND_CLAUSES]
                          THENC SIMP_CONV (srw_ss()) [cf_def,is_bound_Fun_def,astTheory.op_case_def,
                                                      dest_opapp_def]))))
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  end

fun xcf_div name st =
  let
    val f_def = fetch_def name st
  in
    rpt strip_tac
    \\ simp[f_def]
    \\ match_mp_tac(GEN_ALL IMP_app_POSTd_one_FFI_part)
    (* TODO: we could look at the goal state and generate a fresh name instead*)
    \\ qmatch_goalsub_abbrev_tac `make_stepfun_closure highly_improbable_name`
    \\ CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "l" EVAL))
    \\ qunabbrev_tac `highly_improbable_name`
    \\ qmatch_goalsub_abbrev_tac `highly_improbable_name = _`
    \\ qexists_tac `highly_improbable_name`
    (* TODO: give an error if 'limited_parts' is not present *)
    \\ qmatch_assum_abbrev_tac `limited_parts another_highly_improbable_name _`
    \\ qexists_tac `another_highly_improbable_name`
    \\ conj_tac >- MATCH_ACCEPT_TAC(Q.REFL `highly_improbable_name`)
    \\ conj_tac >- EVAL_TAC
    \\ conj_tac >- fs []
    \\ qunabbrev_tac `highly_improbable_name`
    \\ qunabbrev_tac `another_highly_improbable_name`
    \\ CONV_TAC(STRIP_QUANT_CONV(PATH_CONV "rrl" (DEPTH_CONV naryClosure_repack_conv)))
    \\ CONSEQ_CONV_TAC(
          DEPTH_CONSEQ_CONV(
            ONCE_CONSEQ_REWRITE_CONV
              ([],[GEN_ALL(REWRITE_RULE [AND_IMP_INTRO] app_of_cf)],[])))
    \\ CONV_TAC(
          STRIP_QUANT_CONV(
            PATH_CONV "rrlr" (
              QUANT_CONV(
                RATOR_CONV(SIMP_CONV list_ss [])
                          THENC PURE_REWRITE_CONV [AND_CLAUSES]
                          THENC SIMP_CONV (srw_ss()) [cf_def,is_bound_Fun_def,astTheory.op_case_def,
                                                      dest_opapp_def]))))
    \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  end

end
