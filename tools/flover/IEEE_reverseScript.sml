(**
  Connect FloVer's idealized machine semantics to 64-bit
  IEEE-754 floating-point semantics
**)
open machine_ieeeTheory binary_ieeeTheory lift_ieeeTheory realTheory RealArith
                        realLib;
open MachineTypeTheory ExpressionsTheory RealSimpsTheory FloverTactics
     CertificateCheckerTheory FPRangeValidatorTheory IntervalValidationTheory
     ExpressionAbbrevsTheory
     ExpressionSemanticsTheory FloverMapTheory RealRangeArithTheory
     TypeValidatorTheory ErrorValidationTheory IntervalArithTheory AbbrevsTheory
     CommandsTheory ssaPrgsTheory EnvironmentsTheory FloverMapTheory IEEE_connectionTheory;
open preambleFloVer;

val _ = new_theory "IEEE_reverse";

Overload abs[local] = “real$abs”

Definition toFlExp_def:
  toFlExp ((Var v):real expr) = Var v ∧
  toFlExp (Const m c) = Const m (real_to_fp64 dmode c) ∧
  toFlExp (Unop u e1) = Unop u (toFlExp e1) ∧
  toFlExp (Binop b e1 e2) = Binop b (toFlExp e1) (toFlExp e2) ∧
  toFlExp (Fma e1 e2 e3) = Fma (toFlExp e1) (toFlExp e2) (toFlExp e3) ∧
  toFlExp (Downcast m e1) = Downcast m (toFlExp e1)
End

Definition toFlCmd_def:
  toFlCmd (Let m x e g) = Let m x (toFlExp e) (toFlCmd g) ∧
  toFlCmd (Ret e) = Ret (toFlExp e)
End

Definition toFlEnv_def:
  toFlEnv (E:num -> real option) :num -> word64 option =
    λ x. case E x of
         | NONE => NONE
         | SOME v => SOME (real_to_fp64 dmode v)
End

Theorem float_to_real_round_robin:
  !(f:('a,'b) float).
     float_is_finite f ⇒
     float_to_real ((real_to_float dmode (float_to_real f)):('a,'b) float) =
     (float_to_real f)
Proof
  rpt strip_tac
  \\ fs[dmode_def, real_to_float_def, float_round_def]
  \\ reverse $ Cases_on ‘float_is_zero f’
  >- gs[round_finite_normal_float_id]
  \\ ‘∃ s e m. f = <|Sign := s; Exponent := e; Significand := m |>’
    by (Cases_on ‘f’ \\ gs[float_component_equality])
  \\ ‘float_to_real f = 0’
    by (rveq \\ gs[float_tests, float_to_real_def])
  \\ simp[]
  (* Just for simplicity, could also prove that condition is true... *)
  \\ TOP_CASE_TAC \\ gs[]
QED

(** Some eval test
EVAL “float_to_real ((real_to_float roundTiesToEven (float_to_real <|Sign := 1w; Exponent := 0w:word11; Significand := 0w:52 word |>)):(52,11) float”
|> CONV_RULE (RHS_CONV $ RAND_CONV $ binary_ieeeLib.float_round_CONV)
**)

Theorem eval_expr_gives_IEEE_reverse:
  !(e:real expr) E1 E2 Gamma vR A fVars dVars.
    validTypes e Gamma /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars (toREnv E2) /\
    validRanges e A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorbound e Gamma A dVars /\
    FPRangeValidator e A Gamma dVars /\
    eval_expr (toREnv E2) (toRExpMap Gamma) e vR M64 /\
    domain (usedVars e) DIFF domain dVars ⊆ domain fVars ∧
    is64BitEval e /\
    is64BitEnv Gamma /\
    noDowncast e /\
    (∀v.
      v ∈ domain dVars ⇒
      ∃vF m.
      ((toREnv E2) v = SOME vF ∧ FloverMapTree_find (Var v) Gamma = SOME m ∧
      validFloatValue vF m)) ==>
    ?v.
      eval_expr_float (toFlExp e) E2 = SOME v /\
      eval_expr (toREnv E2) (toRExpMap Gamma) e (fp64_to_real v) M64
Proof
  Induct_on `e` \\ rw[toFlExp_def]
  \\ inversion `eval_expr _ _ _ _ _` eval_expr_cases
  \\ once_rewrite_tac [eval_expr_float_def]
  \\ fs[noDowncast_def]
  >- gs [toREnv_def, eval_expr_cases, fp64_to_real_def,
         real_to_fp64_def, fp64_to_float_float_to_fp64,
         CaseEq"option"]
  >- (
    simp[eval_expr_cases, fp64_to_real_def, real_to_fp64_def,
         fp64_to_float_float_to_fp64, real_to_float_def, dmode_def,
         float_round_def, float_is_zero_to_real]
    \\ gs[perturb_def]
    \\ ‘eval_expr (toREnv E2) (toRExpMap Gamma) (Const M64 v) v M64’
      by (gs[eval_expr_cases]
          \\ qexists_tac ‘0’ \\ gs[perturb_def, mTypeToR_pos])
    \\ ‘validFloatValue v M64’
       by (drule FPRangeValidator_sound
           \\ disch_then $ qspecl_then [‘Const M64 v’, ‘v’, ‘M64’] mp_tac
           \\ gs[eval_expr_cases] \\ impl_tac \\ gs[]
           \\ qexists_tac ‘0’ \\ gs[perturb_def, mTypeToR_pos])
    \\ first_x_assum $ assume_tac o SIMP_RULE std_ss [validFloatValue_def]
    \\ gs[]
    >- (
      ‘normalizes (:52 # 11) v’ by gs[normalValue_implies_normalization]
      \\ imp_res_tac relative_error
      \\ qexists_tac ‘e’ \\ simp[float_is_zero_to_real]
      \\ ‘~ (v = 0 ∨ 1 + e = 0)’
        by (CCONTR_TAC \\ gs[] \\ rveq
            >- (gs[normalizes_def]
                \\ ‘0 < inv (2 pow 1022)’ by gs[]
                \\ ‘0 < 0’ suffices_by gs[]
                \\ irule REAL_LTE_TRANS \\ first_assum $ irule_at Any
                \\ gs[])
            \\ ‘e = -1’ by (pop_assum $ mp_tac \\ REAL_ARITH_TAC)
            \\ ‘1 /2 pow 53 < 1’ by (
              irule REAL_LTE_TRANS \\ qexists_tac ‘1/1’
              \\ reverse conj_tac >- gs[]
              \\ rewrite_tac [real_div]
              \\ irule REAL_LT_LMUL_IMP \\ reverse conj_tac >- gs[]
              \\ irule REAL_LT_INV \\ gs[]
              \\ irule REAL_LT_TRANS \\ qexists_tac ‘&53’
              \\ gs[POW_2_LT])
            \\ ‘1 < 1:real’ suffices_by gs[]
            \\ irule REAL_LET_TRANS \\ first_x_assum $ irule_at Any
            \\ gs[])
      \\ gs[perturb_def]
      \\ imp_res_tac normal_not_denormal \\ gs[]
      \\ fs[REAL_INV_1OVER, mTypeToR_def, isCompat_def])
    >- (
      gs[perturb_def, mTypeToR_def, float_is_zero_to_real]
      \\ qspec_then ‘v’ mp_tac (Q.INST_TYPE [‘:'t’|->‘:52’,‘:'w’|->‘:11’] absolute_error_denormal)
      \\ impl_tac
      >- (‘abs v < 2 / 2 pow (INT_MAX (:11) - 1)’ by (
           fs[denormalTranslatedValue_implies_finiteness,
              float_is_finite, denormal_def, minValue_pos_def]
           \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
           \\ irule REAL_LT_TRANS
           \\ first_assum $ irule_at Any
           \\ fs[minExponentPos_def])
          \\ rpt conj_tac >- gs[]
          >~ [‘1 < INT_MAX (:11)’] >- gs[]
          \\ irule REAL_LET_TRANS \\ qexists_tac ‘2 / 2 pow (INT_MAX (:11) - 1)’
          \\ reverse conj_tac
          >- (pop_assum $ mp_tac \\ REAL_ARITH_TAC)
          \\ gs[threshold_def]
          \\ rewrite_tac [REAL_INV_1OVER] \\ EVAL_TAC)
      \\ rpt strip_tac \\ qexists_tac ‘e’ \\ gs[]
      \\ TOP_CASE_TAC \\ gs[minExponentPos_def])
    >- (gvs[denormal_def] \\ qexists_tac ‘0’ \\ gs[mTypeToR_pos])
  )
  >- (
    gs[eval_expr_float_def, eval_expr_cases]
    \\ qpat_x_assum ‘validTypes _ _’ $ assume_tac o ONCE_REWRITE_RULE [validTypes_def]
    \\ gs[]
    \\ first_x_assum $ drule_then drule
    \\ qpat_x_assum ‘validRanges _ _ _ _’ $ assume_tac o ONCE_REWRITE_RULE [validRanges_def]
    \\ gs[]
    \\ qpat_x_assum ‘validErrorbound _ _ _ _’ $ assume_tac o ONCE_REWRITE_RULE [validErrorbound_def]
    \\ gs[]
    \\ ‘FPRangeValidator e A Gamma dVars’ by (
      qpat_x_assum ‘FPRangeValidator _ _ _ _’ $ assume_tac o ONCE_REWRITE_RULE [FPRangeValidator_def]
      \\ gs[])
    \\ gs[]
    \\ ‘m' = M64’ by (Cases_on ‘m'’ \\ gs[isCompat_def])
    \\ gvs[]
    \\ disch_then drule \\ impl_tac
    >- (gs[Once usedVars_def, Once is64BitEval_def] \\ metis_tac[])
    \\ strip_tac \\ gs[eval_expr_float_def]
    \\ simp[Once eval_expr_cases]
    \\ first_x_assum $ irule_at Any \\ gs[isCompat_def]
    \\ gs[fp64_negate_def, fp64_to_real_def, fp64_to_float_float_to_fp64,
          evalUnop_def, float_to_real_negate])
  >- (
    qpat_x_assum ‘validErrorbound _ _ _ _’ $
      mp_tac o ONCE_REWRITE_RULE [validErrorbound_def]
    \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
  >- (
    gs[eval_expr_float_def, eval_expr_cases]
    \\ qpat_x_assum ‘validTypes _ _’ $ assume_tac o ONCE_REWRITE_RULE [validTypes_def]
    \\ gs[]
    \\ first_x_assum $ drule_then drule
    \\ qpat_x_assum ‘validRanges _ _ _ _’ $ assume_tac o ONCE_REWRITE_RULE [validRanges_def]
    \\ gs[]
    \\ qpat_x_assum ‘validErrorbound _ _ _ _’ $ assume_tac o ONCE_REWRITE_RULE [validErrorbound_def]
    \\ gs[]
    \\ Cases_on ‘FloverMapTree_find e A’ \\ gs[] \\ PairCases_on ‘x’ \\ gs[]
    \\ ‘FPRangeValidator e A Gamma dVars’ by (
      qpat_x_assum ‘FPRangeValidator _ _ _ _’ $ assume_tac o ONCE_REWRITE_RULE [FPRangeValidator_def]
      \\ gs[])
    \\ gs[]
    \\ ‘m1 = M64’ by (Cases_on ‘m1’ \\ gs[isCompat_def])
    \\ gvs[] \\ disch_then drule \\ impl_tac
    >- (gs[Once usedVars_def, Once is64BitEval_def] \\ metis_tac[])
    \\ strip_tac \\ gs[eval_expr_float_def]
    \\ first_assum $ irule_at Any \\ gs[isCompat_def]
    \\ gs[fp64_to_real_def, fp64_sqrt_def, fp64_to_float_float_to_fp64,
          dmode_def, evalUnop_def]
    \\ ‘validFloatValue (float_to_real (fp64_to_float v)) M64’
       by (drule FPRangeValidator_sound
           \\ rpt $ disch_then drule \\ impl_tac
           >- gs[Once usedVars_def]
           \\ gs[])
    \\ qpat_assum ‘validRanges e _ _ _’ $ mp_then Any strip_assume_tac validRanges_single
    \\ rename [‘eval_expr E1 _ (toREval e) vR_e REAL’, ‘FloverMapTree_find e A = SOME (iv_e, err_e)’]
    \\ ‘contained (float_to_real (fp64_to_float v))
        (widenInterval (FST iv_e, SND iv_e) err_e)’
      by (
        irule distance_gives_iv
        \\ qexists_tac `vR_e` \\ gvs[contained_def]
        \\ drule validErrorbound_sound
        \\ disch_then drule \\ gs[eval_Real_def, eval_Fin_def]
        \\ disch_then $ qspec_then ‘vR_e’ mp_tac \\ impl_tac
        >- gs[Once usedVars_def]
        \\ strip_tac
        \\ first_x_assum irule
        \\ qexists_tac `M64`  \\ gs[])
    \\ ‘0 < FST (widenInterval (FST iv_e, SND iv_e) err_e)’
      by (
      qpat_x_assum ‘validErrorbound _ _ _ _’
      (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
      \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ ‘0 < float_to_real (fp64_to_float v)’
      by (gs[contained_def, widenInterval_def] \\ irule REAL_LTE_TRANS
            \\ asm_exists_tac \\ gs[])
    \\ ‘(fp64_to_float v).Sign = 0w’
      by imp_res_tac zero_lt_sign_zero
    \\ ‘validFloatValue (evalUnop Sqrt (float_to_real (fp64_to_float v))) M64’
      by (
        drule FPRangeValidator_sound
        \\ disch_then
           (qspecl_then
            [`Unop Sqrt e`,
             `evalUnop Sqrt (float_to_real (fp64_to_float v))`, `M64`]
            irule)
        \\ gvs[]
        \\ qexists_tac ‘e’ \\ fs[]
        \\ rpt conj_tac
        >- (simp[Once validTypes_def, isCompat_def] \\ first_x_assum MATCH_ACCEPT_TAC)
        >- simp[Once validErrorbound_def]
        >- (simp[Once validRanges_def] \\ asm_exists_tac \\ fs[]
            \\ fs[] \\ rveq \\ fs[])
        \\ irule Unop_sqrt'
        \\ qexistsl_tac [‘0’, `M64`, ‘M64’, `float_to_real (fp64_to_float v)`]
        \\ fs[perturb_def, evalUnop_def, mTypeToR_pos, isCompat_def])
    \\ qpat_x_assum `validFloatValue (evalUnop _ _) M64` $
                    assume_tac o SIMP_RULE std_ss [validFloatValue_def]
    \\ gs[]
    (* normal sqrt *)
    >- (
      Q.ISPEC_THEN `(fp64_to_float v):(52,11) float`
                                      impl_subgoal_tac
                                      float_sqrt_relative
    >- (rpt conj_tac
        \\ fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization,
              GSYM float_is_zero_to_real, float_is_finite, evalUnop_def,
              sqrtable_def,
              normalizes_def])
        \\ gvs[dmode_def] \\ qexists_tac ‘e'’
        \\ fs[perturb_def, evalUnop_def]
        \\ imp_res_tac normal_not_denormal \\ simp[]
        \\ simp[REAL_INV_1OVER, mTypeToR_def, isCompat_def])
    (* denormal sqrt *)
    >- (
      Q.ISPEC_THEN `(fp64_to_float v):(52,11) float`
                                      impl_subgoal_tac
                                      float_sqrt_relative_denorm
      >- (
        rpt conj_tac
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalUnop_def]
        >- fs[sqrtable_def]
        >- (
          fs[normalTranslatedValue_implies_finiteness,
             denormalTranslatedValue_implies_finiteness,
             normalValue_implies_normalization, float_is_finite,
             GSYM float_is_zero_to_real, evalUnop_def, denormal_def, minValue_pos_def]
          \\ irule REAL_LT_TRANS
          \\ qexists_tac ‘abs (sqrt (float_to_real (fp64_to_float v)))* &(2 ** minExponentPos M64)’
          \\ gs[] \\ EVAL_TAC)
        >- (
          irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
          \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
          \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
          \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW, evalUnop_def]
          \\ EVAL_TAC)
        \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ gvs[dmode_def] \\ qexists_tac ‘e'’
      \\ fs[perturb_def, evalUnop_def]
      \\ simp[REAL_INV_1OVER, mTypeToR_def, minExponentPos_def])
    (* sqrt 0 *)
    \\ ‘0 < sqrt (float_to_real (fp64_to_float v))’ by (irule SQRT_POS_LT \\ gs[])
    \\ gs[evalUnop_def])
  >~ [‘Binop b e1 e2’]
  >- (
    imp_res_tac validRanges_single
    \\ rw_thm_asm `validTypes _ _` validTypes_def
    \\ rw_thm_asm `validRanges _ _ _ _` validRanges_def
    \\ fs[eval_expr_float_def, optionLift_def]
    \\ imp_res_tac validTypes_exec
    \\ rveq
    \\ `m1 = M64 /\ m2 = M64`
      by (fs[is64BitEnv_def]
          \\ conj_tac \\ first_x_assum irule \\ find_exists_tac \\ fs[])
    \\ rveq
    \\ rw_thm_asm `is64BitEval _` is64BitEval_def \\ fs[]
    \\ ntac 2
      (first_x_assum
       (qspecl_then [`E1`, `E2`, `Gamma`] assume_tac))
    \\ first_x_assum (qspecl_then [`v1`, `A`, `fVars`, `dVars`] destruct)
    >- (
      rpt conj_tac \\ fs[]
      >- (
        qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
      >- (
        rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
        \\ fs[] \\ rveq
        \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) A = _`
        \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) Gamma = _`)
      \\ rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
      \\ fs[domain_union, DIFF_DEF, SUBSET_DEF, Once usedVars_def]
      \\ rpt strip_tac \\ first_x_assum irule \\ simp[Once usedVars_def])
    \\ first_x_assum (qspecl_then [`v2`, `A`, `fVars`, `dVars`] destruct)
    >- (
      rpt conj_tac \\ fs[]
      >- (
        qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
      >- (
        rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
        \\ fs[] \\ rveq
        \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) A = _`
        \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) Gamma = _`)
      \\ rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
      \\ fs[domain_union, DIFF_DEF, SUBSET_DEF])
    \\ fs[]
    \\ rename1 `eval_expr_float (toFlExp e1) _ = SOME vF1`
    \\ rename1 `eval_expr_float (toFlExp e2) _ = SOME vF2`
    \\ imp_res_tac validRanges_single
    \\ rename1 `FloverMapTree_find e2 A = SOME (iv2, err2)`
    \\ rename1 `FloverMapTree_find e1 A = SOME (iv1, err1)`
    \\ rename1 `eval_expr E1 _ (toREval e2) nR2 REAL`
    \\ rename1 `eval_expr E1 _ (toREval e1) nR1 REAL`
    (* Obtain evaluation for E2 *)
    \\ ‘!vF2 m2. eval_expr (toREnv E2) (toRExpMap Gamma) e2 vF2 m2 ==>
       abs (nR2 - vF2) <= err2’
      by (qspecl_then [`e2`, `E1`, `toREnv E2`, `A`,`nR2`,
                       `err2`, `FST iv2`, `SND iv2`, `fVars`,
                       `dVars`,`Gamma`] destruct validErrorbound_sound
          \\ rpt conj_tac \\ fs[]
          >- (fs [DIFF_DEF, SUBSET_DEF]
              \\ rpt strip_tac \\ first_x_assum irule
              \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
        \\ qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
      \\ `contained (float_to_real (fp64_to_float vF2))
            (widenInterval (FST iv2, SND iv2) err2)`
        by (irule distance_gives_iv
            \\ qexists_tac `nR2` \\ fs [contained_def]
            \\ first_x_assum irule
            \\ qexists_tac `M64` \\ gs[fp64_to_real_def])
    \\ `b = Div ==> float_to_real (fp64_to_float vF2) <> 0`
      by (strip_tac \\ rveq
          \\ qpat_x_assum ‘validErrorbound _ _ _ _’
            (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
          \\ fs[widenInterval_def, contained_def, noDivzero_def]
          \\ rpt strip_tac
          >- (CCONTR_TAC \\ fs[] \\ rveq
              \\ `0 < 0:real`
                by (irule REAL_LET_TRANS
                    \\ qexists_tac `SND iv2 + err2` \\ fs[])
              \\ fs[])
          >- (CCONTR_TAC \\ fs[] \\ rveq
              \\ `0 < 0:real`
                by (irule REAL_LTE_TRANS
                    \\ qexists_tac `FST iv2 - err2` \\ fs[])
              \\ fs[])
          >- (CCONTR_TAC \\ fs[] \\ rveq
              \\ `0 < 0:real`
                by (irule REAL_LET_TRANS
                    \\ qexists_tac `SND iv2 + err2` \\ fs[])
              \\ fs[])
          \\ CCONTR_TAC \\ fs[] \\ rveq
          \\ `0 < 0:real`
            by (irule REAL_LTE_TRANS
                \\ qexists_tac `FST iv2 - err2` \\ fs[])
          \\ fs[])
      \\ `validFloatValue
            (evalBinop b (float_to_real (fp64_to_float vF1))
             (float_to_real (fp64_to_float vF2))) M64`
          by (drule FPRangeValidator_sound
              \\ disch_then
                   (qspecl_then
                     [`Binop b e1 e2`,
                      `evalBinop b (float_to_real (fp64_to_float vF1))
                        (float_to_real (fp64_to_float vF2))`,
                      `M64`] irule)
               \\ fs[]
               \\ qexistsl_tac [`e1`, `e2`] \\ fs[]
               \\ rpt conj_tac
               >- (simp[Once validTypes_def] \\ first_x_assum MATCH_ACCEPT_TAC)
               >- (simp[Once validRanges_def] \\ asm_exists_tac \\ fs[]
                   \\ fs[] \\ rveq \\ fs[])
              \\ irule Binop_dist'
              \\ qexistsl_tac [‘0’, `M64`, `M64`, ‘M64’, `float_to_real (fp64_to_float vF1)`,
                                `float_to_real (fp64_to_float vF2)`]
              \\ Cases_on `b`
              \\ fs[perturb_def, evalBinop_def, mTypeToR_pos, fp64_to_real_def])
      \\ `validFloatValue (float_to_real (fp64_to_float vF1)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`e1`, `float_to_real (fp64_to_float vF1)`,
                         `M64`] irule)
               \\ fs[]
               \\ qexistsl_tac [`e1`] \\ fs[]
               \\ rpt conj_tac
               >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
                   \\ fs[domain_union, DIFF_DEF, SUBSET_DEF, Once usedVars_def])
               >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
                   \\ fs[] \\ rveq
                   \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) A = _`
                   \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) Gamma = _`)
               >- (
                qpat_x_assum ‘validErrorbound _ _ _ _’
                (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
                \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
               \\ gs[fp64_to_real_def])
      \\ `validFloatValue (float_to_real (fp64_to_float vF2)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`e2`, `float_to_real (fp64_to_float vF2)`,
                         `M64`] irule)
               \\ fs[]
               \\ qexists_tac `e2` \\ fs[]
               \\ rpt conj_tac
               >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
                   \\ fs[domain_union, DIFF_DEF, SUBSET_DEF])
               >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
                   \\ fs[] \\ rveq
                   \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) A = _`
                   \\ rw_asm_star `FloverMapTree_find (Binop _ _ _) Gamma = _`)
               >- (
                qpat_x_assum ‘validErrorbound _ _ _ _’
                (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
                \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
               \\ gs[fp64_to_real_def])
    \\ qpat_x_assum `validFloatValue (evalBinop _ _ _) M64`
                    $ assume_tac o SIMP_RULE std_ss [validFloatValue_def]
    (** Case distinction for operator **)
    \\ Cases_on `b` \\ fs[GSYM noDivzero_def, optionLift_def, PULL_EXISTS]
    \\ simp[Once eval_expr_cases]
    (* Addition, result normal *)
    >- (
      fs[fp64_add_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_add_relative
      >- (
        rpt conj_tac
        \\ fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization,
              GSYM float_is_zero_to_real, float_is_finite, evalBinop_def])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def]
      \\ imp_res_tac normal_not_denormal
      \\ simp[REAL_INV_1OVER, mTypeToR_def, fp64_to_real_def, fp64_to_float_float_to_fp64]
      \\ gs[fp64_to_real_def])
      (* addition, result denormal *)
    >- (
      fs[fp64_add_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                        `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_add_relative_denorm
      >- (
        rpt conj_tac
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- (
          fs[normalTranslatedValue_implies_finiteness,
             denormalTranslatedValue_implies_finiteness,
             normalValue_implies_normalization, float_is_finite,
             GSYM float_is_zero_to_real, evalBinop_def, denormal_def, minValue_pos_def]
          \\ irule REAL_LT_TRANS
          \\ qpat_x_assum ‘abs _  * _ < 1’ $ irule_at Any
          \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def])
        >- (
          irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
          \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
          \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
          \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
          \\ EVAL_TAC)
        \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def]
      \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER, fp64_to_real_def,
            fp64_to_float_float_to_fp64])
      (* result = 0 *)
      >- (IMP_RES_TAC validValue_gives_float_value
          \\ fs[REAL_LNEG_UNIQ, evalBinop_def]
          \\ fs[fp64_add_def, dmode_def, fp64_to_float_float_to_fp64]
          \\ fs[float_add_def, float_round_with_flags_def]
          \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                           `float_to_real (fp64_to_float vF2)`, `0:real`]
          \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
          \\ `2 * abs (0:real) <= ulp (:52 #11)`
            by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
                \\ once_rewrite_tac [real_div]
                \\ irule REAL_LE_MUL \\ fs[]
                \\ irule REAL_LE_INV \\ fs[])
          \\ fs[float_to_real_round_zero_is_zero, fp64_to_real_def,
                fp64_to_float_float_to_fp64])
      (* Subtraction, normal value *)
    >- (
      fs[fp64_sub_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                                             `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_sub_relative
      >- (
        rpt conj_tac
        \\ fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization,
              GSYM float_is_zero_to_real, float_is_finite, evalBinop_def])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def]
      \\ imp_res_tac normal_not_denormal
      \\ simp[REAL_INV_1OVER, mTypeToR_def, fp64_to_real_def, fp64_to_float_float_to_fp64]
      \\ gs[fp64_to_real_def])
      (* Subtraction, denormal value *)
    >- (
      fs[fp64_sub_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                                             `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_sub_relative_denorm
      >- (
        rpt conj_tac
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- (
          fs[normalTranslatedValue_implies_finiteness,
             denormalTranslatedValue_implies_finiteness,
             normalValue_implies_normalization, float_is_finite,
             GSYM float_is_zero_to_real, evalBinop_def, denormal_def, minValue_pos_def]
          \\ irule REAL_LT_TRANS
          \\ qpat_x_assum ‘abs _ * _ < 1’ $ irule_at Any
          \\ gs[] \\ EVAL_TAC)
        >- (
          irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
          \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
          \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
          \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
          \\ EVAL_TAC)
        \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def, fp64_to_real_def, fp64_to_float_float_to_fp64]
      \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
      (* subtraction, result = 0 *)
    >- (
      fs[evalBinop_def]
      \\ qpat_x_assum `float_to_real (fp64_to_float _) = _` MP_TAC
      \\ simp[real_sub, REAL_LNEG_UNIQ, evalBinop_def]
      \\ fs[fp64_sub_def, dmode_def, fp64_to_float_float_to_fp64]
      \\ fs[float_sub_def]
      \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
      \\ fs[validValue_gives_float_value, float_round_with_flags_def]
      \\ strip_tac
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `0:real`]
      \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
      \\ fs[validValue_gives_float_value, float_round_with_flags_def]
      \\ `2 * abs (0:real) <= ulp (:52 #11)`
        by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
            \\ once_rewrite_tac [real_div]
            \\ irule REAL_LE_MUL \\ fs[]
            \\ irule REAL_LE_INV \\ fs[])
      \\ fs[ float_to_real_round_zero_is_zero, fp64_to_real_def, fp64_to_float_float_to_fp64])
    (* Multiplication, normal result *)
    >- (
      fs[fp64_mul_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                        `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_mul_relative
      >- (
        rpt conj_tac
        \\ fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization,
              GSYM float_is_zero_to_real, float_is_finite, evalBinop_def])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def]
      \\ imp_res_tac normal_not_denormal
      \\ fs[mTypeToR_def, REAL_INV_1OVER, fp64_to_real_def, fp64_to_float_float_to_fp64])
    (* Multiplication, denormal result *)
    >- (
      fs[fp64_mul_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                        `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_mul_relative_denorm
      >- (
        rpt conj_tac
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- (
          fs[normalTranslatedValue_implies_finiteness,
             denormalTranslatedValue_implies_finiteness,
             normalValue_implies_normalization, float_is_finite,
             GSYM float_is_zero_to_real, evalBinop_def, denormal_def, minValue_pos_def]
          \\ irule REAL_LT_TRANS
          \\ qpat_x_assum ‘abs _ * _ < 1’ $ irule_at Any
          \\ gs[minExponentPos_def]
          \\ irule REAL_LET_TRANS
          \\ qexists_tac ‘1 * abs (float_to_real (fp64_to_float vF1) * float_to_real (fp64_to_float vF2)) ’
          \\ reverse conj_tac >- gs[]
          \\ irule REAL_LT_RMUL_IMP \\ fs[float_is_zero_def]
          \\ imp_res_tac validValue_gives_float_value \\ gvs[])
        >- (
          irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
          \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
          \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
          \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
          \\ EVAL_TAC)
        \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def, fp64_to_real_def, fp64_to_float_float_to_fp64]
      \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
    (* multiplication, result = 0 *)
    >- (
      fs[evalBinop_def, REAL_ENTIRE, fp64_mul_def, float_mul_def,
         GSYM float_is_zero_to_real, float_is_zero_def]
      THENL [ Cases_on `float_value (fp64_to_float vF1)`,
              Cases_on `float_value (fp64_to_float vF2)`]
      \\ fs[validValue_gives_float_value]
      \\ fs[float_round_with_flags_def, dmode_def,
            fp64_to_float_float_to_fp64, perturb_def]
      \\ Cases_on `(fp64_to_float vF1).Sign ≠ (fp64_to_float vF2).Sign`
      \\ `2 * abs (0:real) <= ulp (:52 #11)`
        by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
            \\ once_rewrite_tac [real_div]
            \\ irule REAL_LE_MUL \\ fs[]
            \\ irule REAL_LE_INV \\ fs[])
      \\ fs [round_roundTiesToEven_is_plus_zero,
             round_roundTiesToEven_is_minus_zero, zero_to_real,
             fp64_to_real_def, fp64_to_float_float_to_fp64
             ]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `0:real`]
      \\ rveq
      \\ fs[GSYM float_is_zero_to_real, float_is_zero_def,
            mTypeToR_pos, perturb_def])
      (* Division, normal result *)
    >- (
      fs[fp64_div_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                        `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_div_relative
      >- (rpt conj_tac
          \\ fs[validFloatValue_def,
                normalTranslatedValue_implies_finiteness,
                denormalTranslatedValue_implies_finiteness,
                normalValue_implies_normalization,
                GSYM float_is_zero_to_real, float_is_finite, evalBinop_def])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def, fp64_to_real_def, fp64_to_float_float_to_fp64]
      \\ imp_res_tac normal_not_denormal
      \\ gs[mTypeToR_def] \\ rewrite_tac[REAL_INV_1OVER]
      \\ qpat_x_assum ‘_ ≤ 1’ mp_tac \\ simp[])
      (* Division, denormal result *)
    >- (
      fs[fp64_div_def, fp64_to_float_float_to_fp64, evalBinop_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                        `(fp64_to_float vF2):(52,11) float`]
          impl_subgoal_tac
          float_div_relative_denorm
      >- (
        rpt conj_tac
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- (
          fs[normalTranslatedValue_implies_finiteness,
             denormalTranslatedValue_implies_finiteness,
             normalValue_implies_normalization, float_is_finite,
             GSYM float_is_zero_to_real, evalBinop_def, denormal_def, minValue_pos_def]
          \\ irule REAL_LT_TRANS
          \\ qpat_x_assum ‘_ < 1’ $ irule_at Any \\ gs[]
          \\ EVAL_TAC)
        >- (
          irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
          \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
          \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
          \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
          \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
          >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
              \\ fs[POW_2_LE1])
          \\ fs[POW_2_LE1] \\ EVAL_TAC)
        \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ fs[dmode_def]
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `e`]
      \\ fs[perturb_def, evalBinop_def, fp64_to_real_def, fp64_to_float_float_to_fp64]
      \\ gs[mTypeToR_def, minExponentPos_def] \\ rewrite_tac[REAL_INV_1OVER]
      \\ qpat_x_assum ‘_ ≤ 1’ mp_tac \\ simp[])
    (* division, result = 0 *)
    >- (
      fs[fp64_div_def, dmode_def, fp64_to_float_float_to_fp64,
         float_div_def, evalBinop_def]
      \\ `float_to_real (fp64_to_float vF1) = 0`
        by (imp_res_tac div_eq0_general)
      \\ rw_thm_asm `float_to_real (fp64_to_float vF1) = 0` (GSYM float_is_zero_to_real)
      \\ fs[float_is_zero_def]
      \\ Cases_on `float_value (fp64_to_float vF1)`
      \\ fs[validValue_gives_float_value]
      \\ simp [float_round_with_flags_def]
      \\ Cases_on `(fp64_to_float vF1).Sign ≠ (fp64_to_float vF2).Sign`
      \\ `2 * abs (0:real) <= ulp (:52 #11)`
        by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
            \\ once_rewrite_tac [real_div]
            \\ irule REAL_LE_MUL \\ fs[]
            \\ irule REAL_LE_INV \\ fs[])
      \\ fs [round_roundTiesToEven_is_plus_zero,
             round_roundTiesToEven_is_minus_zero, zero_to_real]
      \\ rveq
      \\ `float_to_real (fp64_to_float vF1) = 0:real`
          by (fs[GSYM float_is_zero_to_real, float_is_zero_def])
      \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                       `float_to_real (fp64_to_float vF2)`, `0:real`]
      \\ fs[perturb_def, mTypeToR_pos, float_to_real_round_zero_is_zero]
      \\ gs[fp64_to_real_def, fp64_to_float_float_to_fp64]))
  >~ [‘Fma e1 e2 e3’]
  >- (
    imp_res_tac validRanges_single
    \\ rw_thm_asm `validTypes _ _` validTypes_def
    \\ rw_thm_asm `validRanges _ _ _ _` validRanges_def
    \\ fs[eval_expr_float_def, optionLift_def]
    \\ IMP_RES_TAC validTypes_exec
    \\ rveq \\ first_x_assum kall_tac
    \\ `m1 = M64 /\ m2 = M64 /\ m3 = M64`
      by (fs[is64BitEnv_def]
          \\ rpt conj_tac \\ first_x_assum irule \\ find_exists_tac \\ fs[])
    \\ rveq
    \\ rw_thm_asm `is64BitEval _` is64BitEval_def \\ fs[]
    \\ ntac 3
            (first_x_assum
             (qspecl_then [`E1`, `E2`, `Gamma`] assume_tac))
    \\ first_x_assum (qspecl_then [`v1`, `A`, `fVars`, `dVars`] destruct)
    >- (
      rpt conj_tac \\ fs[]
      >- (
        qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq]
        \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
      >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
          \\ fs[] \\ rveq
          \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) A = _`
          \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) Gamma = _`)
      \\ rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
      \\ fs[domain_union, DIFF_DEF, SUBSET_DEF, Once usedVars_def]
      \\ rpt strip_tac \\ first_x_assum irule \\ simp[Once usedVars_def])
    \\ first_x_assum (qspecl_then [`v2`, `A`, `fVars`, `dVars`] destruct)
    >- (
      rpt conj_tac \\ fs[]
      >- (
        qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq]
        \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
      >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
          \\ fs[] \\ rveq
          \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) A = _`
          \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) Gamma = _`)
      \\ rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
      \\ fs[domain_union, DIFF_DEF, SUBSET_DEF])
    \\ first_x_assum (qspecl_then [`v3`, `A`, `fVars`, `dVars`] destruct)
    >- (
      rpt conj_tac \\ fs[]
      >- (
        qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq]
        \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
      >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
          \\ fs[] \\ rveq
          \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) A = _`
          \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) Gamma = _`)
      \\ rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
      \\ fs[domain_union, DIFF_DEF, SUBSET_DEF])
      \\ rename1 ‘eval_expr_float (toFlExp e1) E2 = SOME vF1’
      \\ rename1 ‘eval_expr_float (toFlExp e2) E2 = SOME vF2’
      \\ rename1 ‘eval_expr_float (toFlExp e3) E2 = SOME vF3’
      \\ `validFloatValue
            (evalFma (float_to_real (fp64_to_float vF1))
             (float_to_real (fp64_to_float vF2))
             (float_to_real (fp64_to_float vF3))) M64`
          by (drule FPRangeValidator_sound
              \\ disch_then
                   (qspecl_then
                     [`Fma e1 e2 e3`,
                      `evalFma (float_to_real (fp64_to_float vF1))
                      (float_to_real (fp64_to_float vF2))
                      (float_to_real (fp64_to_float vF3))`,
                      `M64`] irule)
               \\ fs[]
               \\ qexistsl_tac [`e1`, `e2`, ‘e3’] \\ fs[]
               \\ rpt conj_tac
               >- (simp[Once validTypes_def] \\ first_x_assum MATCH_ACCEPT_TAC)
               >- (simp[Once validRanges_def] \\ find_exists_tac \\ fs[]
                   \\ fs[] \\ rveq \\ fs[])
               \\ simp[Once eval_expr_cases]
               \\ qexistsl_tac [`M64`, `M64`, ‘M64’, `float_to_real (fp64_to_float vF1)`,
                                `float_to_real (fp64_to_float vF2)`,
                                `float_to_real (fp64_to_float vF3)`, `0:real`]
               \\ fs[perturb_def, evalFma_def, mTypeToR_pos, fp64_to_real_def])
      \\ `validFloatValue (float_to_real (fp64_to_float vF1)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`e1`, `float_to_real (fp64_to_float vF1)`,
                         `M64`] irule)
               \\ fs[]
               \\ qexistsl_tac [`e1`] \\ fs[]
               \\ rpt conj_tac
               >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
                   \\ fs[domain_union, DIFF_DEF, SUBSET_DEF, Once usedVars_def])
               >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
                   \\ fs[] \\ rveq
                   \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) A = _`
                   \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) Gamma = _`)
               >- (
                qpat_x_assum ‘validErrorbound _ _ _ _’
                (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
                \\ fs[option_case_eq]
                \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
               \\ fs[fp64_to_real_def])
      \\ `validFloatValue (float_to_real (fp64_to_float vF2)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`e2`, `float_to_real (fp64_to_float vF2)`,
                         `M64`] irule)
               \\ fs[]
               \\ qexists_tac `e2` \\ fs[]
               \\ rpt conj_tac
               >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
                   \\ fs[domain_union, DIFF_DEF, SUBSET_DEF])
               >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
                   \\ fs[] \\ rveq
                   \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) A = _`
                   \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) Gamma = _`)
               >- (
                qpat_x_assum ‘validErrorbound _ _ _ _’
                (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
                \\ fs[option_case_eq]
                \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
               \\ gs[fp64_to_real_def])
      \\ `validFloatValue (float_to_real (fp64_to_float vF3)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`e3`, `float_to_real (fp64_to_float vF3)`,
                         `M64`] irule)
               \\ fs[]
               \\ qexists_tac `e3` \\ fs[]
               \\ rpt conj_tac
               >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def
                   \\ fs[domain_union, DIFF_DEF, SUBSET_DEF])
               >- (rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
                   \\ fs[] \\ rveq
                   \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) A = _`
                   \\ rw_asm_star `FloverMapTree_find (Fma _ _ _) Gamma = _`)
               >- (
                qpat_x_assum ‘validErrorbound _ _ _ _’
                (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
                \\ fs[option_case_eq]
                \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
               \\ gs[fp64_to_real_def])
    \\ qpat_x_assum ‘validFloatValue (evalFma _ _ _) _’
                    (assume_tac o SIMP_RULE std_ss [validFloatValue_def])
    \\ fs[optionLift_def]
    \\ simp[Once eval_expr_cases, PULL_EXISTS]
    \\ rewrite_tac [CONJ_ASSOC]
    \\ ntac 3 (once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs[])
    \\ fs[evalFma_def, evalBinop_def, fp64_mul_add_def, fp64_to_real_def,
          fp64_to_float_float_to_fp64]
    >- (
      Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                     `(fp64_to_float vF2):(52,11) float`,
                     `(fp64_to_float vF3):(52,11) float`]
      impl_subgoal_tac
      float_mul_add_relative
      >- (
        rpt conj_tac
        \\ fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization,
              GSYM float_is_zero_to_real, float_is_finite, evalFma_def, evalBinop_def])
      \\ fs[dmode_def]
      \\ fs[perturb_def]
      \\ qexistsl_tac [`e`]
      \\ pop_assum (rewrite_tac o single)
      \\ fs[perturb_def, evalBinop_def]
      \\ imp_res_tac normal_not_denormal
      \\ fs[mTypeToR_def, REAL_INV_1OVER])
      (* result denormal *)
    >- (
      fs[fp64_mul_add_def, fp64_to_float_float_to_fp64, evalFma_def]
      \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                        `(fp64_to_float vF2):(52,11) float`,
                        `(fp64_to_float vF3):(52,11) float`]
          impl_subgoal_tac
          float_mul_add_relative_denorm
      >- (
        rpt conj_tac
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- fs[validFloatValue_def,
              normalTranslatedValue_implies_finiteness,
              denormalTranslatedValue_implies_finiteness,
              normalValue_implies_normalization, float_is_finite,
              GSYM float_is_zero_to_real, evalBinop_def]
        >- (
          fs[normalTranslatedValue_implies_finiteness,
             denormalTranslatedValue_implies_finiteness,
             normalValue_implies_normalization, float_is_finite,
             GSYM float_is_zero_to_real, evalBinop_def, denormal_def, minValue_pos_def]
          \\ irule REAL_LT_TRANS
          \\ qpat_x_assum ‘_ < 1’ $ irule_at Any \\ gs[]
          \\ EVAL_TAC)
        >- (
          irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
          \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
          \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
          \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
          \\ EVAL_TAC)
        \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ fs[dmode_def] \\ qexists_tac ‘e’
      \\ fs[perturb_def, evalFma_def]
      \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
      (* result = 0 *)
    >- (
      imp_res_tac validValue_gives_float_value
      \\ fs[REAL_LNEG_UNIQ, evalFma_def, evalBinop_def]
      \\ fs[fp64_add_def, dmode_def, fp64_mul_def, fp64_to_float_float_to_fp64]
      \\ fs[float_mul_add_def, float_round_with_flags_def]
      \\ qexists_tac `0:real`
      \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
      \\ fs[float_is_nan_def, float_is_infinite_def]
      \\ `2 * abs (0:real) <= ulp (:52 #11)`
        by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
            \\ once_rewrite_tac [real_div]
            \\ irule REAL_LE_MUL \\ fs[]
            \\ irule REAL_LE_INV \\ fs[])
      \\ fs[float_to_real_round_zero_is_zero]))
QED

(** The below does not work because of double-rounding **)
(*
Theorem bstep_gives_IEEE:
  !(f:real cmd) E1 E2 Gamma vR vF A fVars dVars outVars.
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 /\
    ssa f (union fVars dVars) outVars /\
    validTypesCmd f Gamma /\
    validRangesCmd f A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorboundCmd f Gamma A dVars /\
    FPRangeValidatorCmd f A Gamma dVars /\
    bstep (toREvalCmd f) E1 (toRTMap (toRExpMap Gamma)) vR REAL /\
    bstep f E2 (toRExpMap Gamma) vF M64 /\
    domain (freeVars f) DIFF domain dVars ⊆ domain fVars ∧
    is64BitBstep f /\
    is64BitEnv Gamma /\
    noDowncastFun f /\
    (∀ x v. E2 x = SOME v ⇒ float_to_real ((real_to_float dmode v):(52,11) float) = v) ∧
    (∀v.
      v ∈ domain dVars ⇒
      ∃vF m.
      (E2 v = SOME vF ∧ FloverMapTree_find (Var v) Gamma = SOME m ∧
      validFloatValue vF m)) ==>
    ?v.
      bstep_float (toFlCmd f) (toFlEnv E2) = SOME v /\
      bstep f E2 (toRExpMap Gamma)
        (fp64_to_real v) M64
Proof
  reverse $ Induct_on `f`
  \\ simp [toFlCmd_def, Once toREvalCmd_def, is64BitBstep_def,
                 noDowncastFun_def]
  \\ rpt strip_tac
  \\ rpt (inversion `bstep (Let _ _ _ _) _ _ _ _` bstep_cases)
  \\ inversion `ssa _ _ _` ssa_cases
  \\ once_rewrite_tac [bstep_float_def]
  \\ fs[noDowncast_def]
  \\ qpat_x_assum ‘validErrorboundCmd _ _ _ _’
     (fn thm => mp_tac (ONCE_REWRITE_RULE[validErrorboundCmd_def] thm))
  \\ fs[option_case_eq]
  >- (
    strip_tac \\ fs[bstep_cases, bstep_float_def]
    \\ irule eval_expr_gives_IEEE_reverse
    \\ rpt conj_tac
    \\ fs[Once validTypesCmd_def]
    >- first_x_assum $ irule_at Any
    \\ gs[getRetExp_def, freeVars_def]
    \\ rpt $ first_x_assum $ irule_at Any
    \\ conj_tac
    \\ fs[freeVars_def, Once FPRangeValidatorCmd_def, validRangesCmd_def])
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ gvs[]
  \\ `?v_e. eval_expr_float (toFlExp e) (toFlEnv E2) = SOME v_e /\
     eval_expr E2 (toRExpMap Gamma) e (fp64_to_real v_e) M64`
    by (irule eval_expr_gives_IEEE_reverse \\ rpt conj_tac \\ fs[]
        >- fs[Once validTypesCmd_def]
        >- first_x_assum $ irule_at Any
        \\ qexistsl_tac [`A`, `E1`, `dVars`, `fVars`]
        \\ rpt conj_tac \\ fs[]
        >- (fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF]
            \\ rpt strip_tac
            \\ `x IN domain fVars \/  x IN domain dVars`
              by (first_x_assum irule \\ fs[]))
        >- (fs [Once FPRangeValidatorCmd_def])
        \\ fs[Once validRangesCmd_def])
  \\ fs[Once validRangesCmd_def]
  \\ imp_res_tac validRanges_single
  \\ imp_res_tac validRangesCmd_single
  \\ fs[Once validTypesCmd_def]
  (* prove validity of errorbound for floating-point value *)
  \\ qspecl_then
     [`e`, `E1`, `E2`, `A`, `v'`, `r`,
      `FST iv`, `SND iv`, `fVars`, `dVars`, `Gamma`]
     impl_subgoal_tac
     validErrorbound_sound
  >- (
    fs[DIFF_DEF, SUBSET_DEF]
    \\ rpt strip_tac \\ first_x_assum irule
    \\ fs[Once freeVars_def, domain_union]
    \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[]
    \\ `n IN domain fVars \/ n IN domain dVars`
      by (first_x_assum irule \\ fs[]))
  \\ fs[]
  \\ imp_res_tac meps_0_deterministic \\ rveq
  \\ rename1 `FST iv <= vR_e`
  \\ rename1 ‘FloverMapTree_find (getRetExp (Let M64 n e f)) A =
              SOME (ivR,errR)’
  \\ rename1 `FST iv_e <= vR_e`
  \\ rename1 `abs (vR_e - nF) <= err_e`
  \\ `abs (vR_e - (fp64_to_real v_e)) <= err_e`
    by (first_x_assum irule \\ fs[]
        \\ first_x_assum $ irule_at Any)
  \\ fs[getRetExp_def]
  \\ rename1 `FloverMapTree_find (getRetExp f) A = SOME (iv_f, err_f)`
  (* Now construct a new evaluation according to our big-step semantics
           using lemma validErrorboundCmd_gives_eval *)
  \\ qspecl_then
     [ `f`, `A`, `updEnv n vR_e E1`,
       `updEnv n (fp64_to_real v_e) E2`,
       `outVars`, `fVars`, `insert n () dVars`, `vR`, `FST iv_f`, `SND iv_f`,
       `err_f`, `M64`, `Gamma`]
     impl_subgoal_tac
     validErrorboundCmd_gives_eval
  >- (
    fs[] \\ rpt conj_tac
    >- (
      irule approxEnvUpdBound
      \\ fs[lookup_NONE_domain, toRExpMap_def])
    >- (
      irule ssa_equal_set
      \\ qexists_tac `insert n () (union fVars dVars)`
      \\ conj_tac \\ TRY (fs[] \\ FAIL_TAC "")
      \\ rewrite_tac [domain_union, domain_insert]
      \\ rewrite_tac [UNION_DEF, INSERT_DEF]
      \\ fs[EXTENSION]
      \\ rpt strip_tac
      \\ metis_tac[])
    >- (
      fs[DIFF_DEF, domain_insert, SUBSET_DEF]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs[Once freeVars_def]
      \\ simp[Once freeVars_def, domain_union]))
  \\ fs[optionLift_def]
  (* Instantiate IH with newly obtained evaluation, to get the conclusion *)
  \\ first_x_assum
     (qspecl_then [`updEnv n vR_e E1`,
                   `updEnv n (fp64_to_real v_e) E2`,
                   `Gamma`, `vR`, `vF'`, `A`, `fVars`,
                   `insert n () dVars`, `outVars`]
      impl_subgoal_tac)
  >- (
    simp[Once validErrorboundCmd_def]
    \\ fs [Once FPRangeValidatorCmd_def, Once validTypesCmd_def,
           Once validRangesCmd_def]
    \\ rpt conj_tac
    >- (
      drule approxEnvUpdBound
      \\ rpt $ disch_then drule
      \\ fs[domain_lookup, lookup_NONE_domain, toRExpMap_def])
    >- (
      irule ssa_equal_set
      \\ qexists_tac `insert n () (union fVars dVars)`
      \\ conj_tac \\ TRY (fs[] \\ FAIL_TAC "")
      \\ rewrite_tac [domain_union, domain_insert]
      \\ rewrite_tac [UNION_DEF, INSERT_DEF]
      \\ fs[EXTENSION]
      \\ rpt strip_tac
      \\ metis_tac[])
    >- first_x_assum MATCH_ACCEPT_TAC
    >- (
      reverse (sg `m' = M64`)
      >- (rveq \\ fs[])
      \\ irule bstep_Gamma_det \\ rpt (find_exists_tac \\ fs[]))
    >- (
      fs[DIFF_DEF, domain_insert, SUBSET_DEF]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ fs[Once freeVars_def]
      \\ simp[Once freeVars_def, domain_union])
    >- (rpt strip_tac \\ Cases_on ‘x = n’ \\ gs[]
        >- (rveq \\ simp[fp64_to_real_def]
            \\ ‘float_is_finite (fp64_to_float v_e)’
              by (gs[float_is_finite_def]
                  \\‘validFloatValue (float_to_real (fp64_to_float v_e)) M64’
                  suffices_by (gs[validValue_gives_float_value])
                  \\ irule FPRangeValidator_sound
                  \\ rpt $ first_x_assum $ irule_at Any
                  \\ gs[fp64_to_real_def]
                  \\ fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF]
                  \\ rpt strip_tac \\ first_x_assum irule \\ fs[]
                  \\ CCONTR_TAC \\ fs[]
                  \\ rveq \\ fs[]
                  \\ metis_tac [])
            \\ simp[float_to_real_round_robin])
        \\ first_x_assum irule \\ first_x_assum $ irule_at Any)
    >- (
      rpt strip_tac \\ simp[updEnv_def]
      \\ rveq \\ fs[]
      >- (
        irule FPRangeValidator_sound
        \\ rpt $ first_x_assum $ irule_at Any \\ conj_tac
        \\ fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF]
        \\ rpt strip_tac \\ first_x_assum irule \\ fs[]
        \\ CCONTR_TAC \\ fs[]
        \\ rveq \\ fs[]
        \\ metis_tac [])
      \\ IF_CASES_TAC \\ fs[]
      \\ irule FPRangeValidator_sound
      \\ rpt $ first_x_assum $ irule_at Any \\ conj_tac
      \\ fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF])
    \\ fs[]
    (** DOUBLE ROUNDING HERE.... **)
    \\ ‘updFlEnv n v_e (toFlEnv E2) = toFlEnv (updEnv n (fp64_to_real v_e) E2)’
      by (gs[updFlEnv_def, toFlEnv_def, FUN_EQ_THM]
          \\ strip_tac \\ Cases_on ‘x = n’
          \\
          \\ gs[real_to_fp64_def, fp64_to_real_def]
    \\ irule let_b \\ fs[toRExpMap_def] \\ find_exists_tac
        \\ fs[] \\ irule bstep_eq_env
        \\ find_exists_tac \\ fs[]
        \\ strip_tac \\ fs[toREnv_def, updEnv_def, updFlEnv_def]
        \\ IF_CASES_TAC \\ fs[])
QED
*)

val found_tac = TRY (last_x_assum irule \\ find_exists_tac \\ fs[] \\ FAIL_TAC "")
  \\ first_x_assum irule \\ find_exists_tac \\ fs[];

Theorem IEEE_connection_expr:
  !(e:real expr) (A:analysisResult) (P:precond) E1 E2 defVars fVars Gamma.
      is64BitEval e /\
      is64BitEnv defVars /\
      noDowncast e /\
      fVars_P_sound fVars E1 P /\
      (domain (usedVars e)) SUBSET (domain fVars) /\
      CertificateChecker e A P defVars = SOME Gamma /\
      approxEnv E1 (toRExpMap Gamma) A fVars LN (toREnv E2) ⇒
        ?iv err vR vF. (* m, currently = M64 *)
          FloverMapTree_find e A = SOME (iv, err) /\
          eval_expr E1 (toRTMap (toRExpMap Gamma)) (toREval e) vR REAL /\
          eval_expr_float (toFlExp e) E2 = SOME vF /\
          eval_expr (toREnv E2) (toRExpMap Gamma) e (fp64_to_real vF) M64 /\
          abs (vR - (fp64_to_real vF)) <= err
Proof
  simp [CertificateChecker_def]
  \\ rpt strip_tac
  \\ Cases_on `getValidMap defVars e FloverMapTree_empty` \\ fs[]
  \\ rveq \\ imp_res_tac getValidMap_top_correct
  \\ `validTypes e Gamma`
    by (first_x_assum irule
        \\ fs[FloverMapTree_empty_def, FloverMapTree_mem_def, FloverMapTree_find_def])
  \\ `! e m. FloverMapTree_find e Gamma = SOME m ==> m = M64`
      by (rpt strip_tac \\ irule getValidMap_preserving
          \\ qexistsl_tac [`FloverMapTree_empty`, `defVars`, `e`, `e'`, `Gamma`]
          \\ rpt conj_tac \\ rpt strip_tac
          \\ fs[FloverMapTree_empty_def, FloverMapTree_find_def , is64BitEnv_def]
          \\ first_x_assum irule \\ find_exists_tac \\ fs[])
  \\ drule validIntervalbounds_sound
  \\ rpt $ disch_then drule
  \\ disch_then (qspecl_then [`fVars`,`E1`, `Gamma`] destruct)
  \\ fs[dVars_range_valid_def, fVars_P_sound_def]
  \\ drule validErrorbound_sound
  \\ rpt $ disch_then drule
  \\ imp_res_tac validRanges_single
  \\ disch_then (qspecl_then [`vR`, `err`, `FST iv`, `SND iv`] destruct)
  \\ fs[]
  \\ qspecl_then [`e`, `E1`, `E2`, `Gamma`, `nF`, `A`, `fVars`, `LN`]
       destruct
       eval_expr_gives_IEEE_reverse
  >- (
    rpt conj_tac \\ fs[]
    >- (
      `FloverMapTree_find e Gamma = SOME M64`
         by (irule typing_expr_64bit \\ fs[is64BitEnv_def]
             \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ `m = M64`
        by (irule validTypes_exec \\ rpt (find_exists_tac \\ fs[]))
      \\ rveq \\ fs[])
    \\ fs[is64BitEnv_def] \\ first_x_assum MATCH_ACCEPT_TAC)
  \\ rpt $ first_assum $ irule_at Any
QED

(** Does not work because of let-bindings **)
(*
Theorem IEEE_connection_cmds:
  ! (f:word64 cmd) (A:analysisResult) (P:precond) E1 E2 defVars (fVars:num_set)
      Gamma.
      is64BitBstep (toRCmd f) /\
      is64BitEnv defVars /\
      noDowncastFun (toRCmd f) /\
      fVars_P_sound fVars E1 P /\
      (domain (freeVars (toRCmd f))) SUBSET (domain fVars) /\
      CertificateCheckerCmd (toRCmd f) A P defVars = SOME Gamma /\
      approxEnv E1 (toRExpMap Gamma) A (freeVars (toRCmd f)) LN (toREnv E2) ==>
        ?iv err vR vF. (* m, currently = M64 *)
          FloverMapTree_find (getRetExp (toRCmd f)) A = SOME (iv, err) /\
          bstep (toREvalCmd (toRCmd f)) E1 (toRTMap (toRExpMap Gamma)) vR REAL /\
          bstep_float f E2 = SOME vF /\
          bstep (toRCmd f) (toREnv E2) (toRExpMap Gamma)
            (float_to_real (fp64_to_float vF)) M64 /\
          abs (vR - (float_to_real (fp64_to_float vF))) <= err
Proof
  simp [CertificateCheckerCmd_def]
  \\ rpt strip_tac
  \\ Cases_on `getValidMapCmd defVars (toRCmd f) FloverMapTree_empty` \\ fs[]
  \\ rveq \\ IMP_RES_TAC getValidMapCmd_correct
  \\ `validTypesCmd (toRCmd f) Gamma`
    by (first_x_assum irule
        \\ fs[FloverMapTree_empty_def, FloverMapTree_mem_def, FloverMapTree_find_def])
  \\ `! e m. FloverMapTree_find e Gamma = SOME m ==> m = M64`
    by (rpt strip_tac \\ irule getValidMapCmd_preserving
        \\ qexistsl_tac [`FloverMapTree_empty`, `defVars`, `e`, `toRCmd f`, `Gamma`]
        \\ rpt conj_tac \\ rpt strip_tac
        \\ fs[FloverMapTree_empty_def, FloverMapTree_find_def , is64BitEnv_def]
        \\ first_x_assum irule \\ find_exists_tac \\ fs[])
  \\ `?outVars. ssa (toRCmd f) (freeVars (toRCmd f)) outVars`
      by (match_mp_tac validSSA_sound \\ fs[])
  \\ qspecl_then
       [`toRCmd f`, `A`, `E1`, `freeVars (toRCmd f)`, `LN`, `outVars`, `P`, `Gamma`]
       destruct validIntervalboundsCmd_sound
  \\ fs[dVars_range_valid_def, fVars_P_sound_def]
  >- (rpt strip_tac \\ first_x_assum irule \\ fs[SUBSET_DEF])
  \\ IMP_RES_TAC validRangesCmd_single
  \\ qspecl_then
       [`toRCmd f`, `A`, `E1`, `toREnv E2`, `outVars`, `freeVars (toRCmd f)`, `LN`, `vR`, `FST iv_e`,
        `SND iv_e`, `err_e`, `M64`, `Gamma`]
        destruct validErrorboundCmd_gives_eval
  \\ fs[]
  \\ rpt (find_exists_tac \\ fs[])
  \\ qspecl_then
      [`f`, `E1`, `E2`, `toREnv E2`, `Gamma`, `vR`, `vF`, `A`, `freeVars (toRCmd f)`, `LN`, `outVars`]
      destruct
      bstep_gives_IEEE
  >- (fs[is64BitEnv_def]
      \\ conj_tac
      >- (`FloverMapTree_find (getRetExp (toRCmd f)) Gamma = SOME M64`
          by (irule typing_cmd_64bit
              \\ fs[is64BitEnv_def] \\ first_x_assum MATCH_ACCEPT_TAC)
          \\ `m = M64`
          by (drule validTypesCmd_single
              \\ disch_then assume_tac \\ fs[]
              \\ fs[] \\ rveq \\ fs[]
              \\ first_x_assum irule
              \\ qexistsl_tac [`toREnv E2`, `Gamma`, `vF`] \\ fs[])
          \\ rveq \\ fs[])
      \\ first_x_assum MATCH_ACCEPT_TAC)
  \\ find_exists_tac \\ fs[]
  \\ drule validErrorboundCmd_sound
  \\ rpt (disch_then drule)
  \\ rename1 `bstep (toRCmd f) (toREnv E2) _ vF2 m2`
  \\ disch_then
      (qspecl_then
        [`outVars`, `vR`, `vF2`, `FST iv_e`, `SND iv_e`, `err_e`, `m2`] destruct)
  \\ fs[]
QED
*)

val _ = export_theory ();
