(**
  Connect FloVer's idealized machine semantics to 64-bit
  IEEE-754 floating-point semantics
**)
open machine_ieeeTheory binary_ieeeTheory lift_ieeeTheory realTheory RealArith;
open MachineTypeTheory ExpressionsTheory RealSimpsTheory FloverTactics
     CertificateCheckerTheory FPRangeValidatorTheory IntervalValidationTheory
     ExpressionAbbrevsTheory
     ExpressionSemanticsTheory FloverMapTheory RealRangeArithTheory
     TypeValidatorTheory ErrorValidationTheory IntervalArithTheory AbbrevsTheory
     CommandsTheory ssaPrgsTheory EnvironmentsTheory FloverMapTheory;
open preambleFloVer;

val _ = new_theory "IEEE_connection";

Overload abs[local] = “realax$abs”

val _ = diminish_srw_ss ["RMULCANON_ss","RMULRELNORM_ss"]

(** FloVer assumes rounding with ties to even, thus we exprlicitly define
    a rounding mode here **)
Definition dmode_def :
  dmode = roundTiesToEven
End

Definition optionLift_def:
  (optionLift (SOME v) some_cont none_cont = some_cont v) /\
  (optionLift (NONE) some_cont none_cont = none_cont)
End

Definition updFlEnv_def:
  updFlEnv x v E = \ y. if y = x then SOME v else E y
End

Definition eval_expr_float_def:
  (eval_expr_float (Var n) E = E n) /\
  (eval_expr_float (Const m v) E = SOME v) /\
  (eval_expr_float (Unop Neg e) E =
    case eval_expr_float e E of
      | SOME v =>  SOME (fp64_negate v)
      | _ => NONE) ∧
  (eval_expr_float (Unop Inv e) E = NONE) ∧
  (eval_expr_float (Unop Sqrt e) E =
    case eval_expr_float e E of
      | SOME v =>  SOME (fp64_sqrt dmode v)
      | _ => NONE) ∧
  (eval_expr_float (Binop b e1 e2) E =
    (case (eval_expr_float e1 E), (eval_expr_float e2 E) of
       | SOME v1, SOME v2 =>
             (case b of
                | Plus => SOME (fp64_add dmode v1 v2)
                | Sub => SOME (fp64_sub dmode v1 v2)
                | Mult => SOME (fp64_mul dmode v1 v2)
                | Div => SOME (fp64_div dmode v1 v2))
       | _, _ => NONE)) /\
  (eval_expr_float (Fma e1 e2 e3) E =
    (case (eval_expr_float e1 E), (eval_expr_float e2 E), (eval_expr_float e3 E) of
    | SOME v1, SOME v2, SOME v3 => SOME (fp64_mul_add roundTiesToEven v1 v2 v3)
    | _, _, _ => NONE)) /\
  (eval_expr_float (Downcast m e) E = NONE)
End

Definition bstep_float_def:
  (bstep_float (Let m x e g) E :word64 option=
     optionLift (eval_expr_float e E)
       (\ v. bstep_float g (updFlEnv x v E))
       NONE) /\
  (bstep_float (Ret e) E = eval_expr_float e E)
End

Definition toRExp_def:
  (toRExp ((Var v):word64 expr) = Var v) /\
  (toRExp (Const m c) = Const m (float_to_real (fp64_to_float c))) /\
  (toRExp (Unop u e1) = Unop u (toRExp e1)) /\
  (toRExp (Binop b e1 e2) = Binop b (toRExp e1) (toRExp e2)) /\
  (toRExp (Fma e1 e2 e3) = Fma (toRExp e1) (toRExp e2) (toRExp e3)) /\
  (toRExp (Downcast m e1) = Downcast m (toRExp e1))
End

Definition toRCmd_def:
  (toRCmd (Let m x e g) = Let m x (toRExp e) (toRCmd g)) /\
  (toRCmd (Ret e) = Ret (toRExp e))
End

Definition toREnv_def:
  toREnv (E:num -> word64 option) (x:num):real option =
    case E x of
      | NONE => NONE
      | SOME v => SOME (float_to_real (fp64_to_float v))
End

Definition toWordEnv_def:
  toWordEnv E = \x. case E x of
                    | SOME v => SOME (float_to_fp64 (real_to_float dmode v))
                    | NONE => NONE
End

Definition Binop_to_Rop_def:
  Binop_to_Rop (b:binop) :real->real->real =
    case b of
      | Plus => $+
      | Sub => $-
      | Mult => $*
      | Div => $/
End

Theorem real_div_pow:
  ! a n m. a <> 0 /\ n >= m ==> a pow n / a pow m = a pow (n - m)
Proof
  Induct_on `n` \\ rpt strip_tac
  >- (Cases_on `m` \\ fs[pow])
  \\ fs[pow]
  \\ Cases_on `m` \\ fs[pow]
  \\ `n >= n'` by (fs[])
  \\ res_tac
  \\ first_x_assum (qspec_then `a` (fn thm => rewrite_tac[(GSYM thm)]))
  \\ qspecl_then [`a`, `a pow n'`] destruct REAL_INV_MUL
  >- (conj_tac \\ fs[]
      \\ Cases_on `n'` \\ fs[pow, POW_ZERO_EQ])
  \\ fs[real_div, REAL_MUL_ASSOC]
  \\ `a * a pow n * inv a * inv (a pow n') = a * inv a * a pow n * inv (a pow n')`
      by (REAL_ASM_ARITH_TAC)
  \\ pop_assum (fn thm => once_rewrite_tac [thm])
  \\ fs[REAL_MUL_RINV]
QED

Theorem zero_lt_sign_zero:
  0 < float_to_real fp ⇒
  fp.Sign = 0w
Proof
  rpt strip_tac \\ CCONTR_TAC
  \\ ‘fp.Sign = 1w’ by (Cases_on ‘fp.Sign’ \\ gs[])
  \\ gs[float_to_real_def]
  \\ ‘0 < 0:real’ suffices_by gs[]
  \\ irule REAL_LTE_TRANS
  \\ asm_exists_tac \\ gs[REAL_MUL_LNEG]
  \\ Cases_on ‘fp.Exponent = 0w’ \\ gs[real_div]
  >- (
    irule realTheory.REAL_LE_MUL \\ conj_tac
    \\ irule realTheory.REAL_LE_MUL \\ gs[] )
  \\ gs[real_div] \\ irule REAL_LE_MUL \\ conj_tac
  \\ TRY (irule REAL_LE_MUL \\ gs[])
  \\ irule REAL_LE_ADD \\ conj_tac \\ gs[]
  \\ irule REAL_LE_MUL \\ conj_tac \\ gs[]
QED

Theorem pow_simp1[local] = Q.prove (`2 pow 2047 / 2 pow 1023 = 2 pow 1024`,
  qspecl_then [`2`, `2047`,`1023`] destruct real_div_pow \\ fs[]);

Theorem pow_simp2[local] = Q.prove (`2 pow 2046 / 2 pow 1023 = 2 pow 1023`,
  qspecl_then [`2`, `2046`,`1023`] destruct real_div_pow \\ fs[]);

Theorem threshold_64_bit_lt_maxValue:
  maxValue M64 < threshold (:52 # 11)
Proof
  rewrite_tac[threshold_def, maxValue_def, maxExponent_def, GSYM REAL_OF_NUM_POW]
  \\ simp[pow_simp2]
  \\ once_rewrite_tac [GSYM REAL_MUL_RID]
  \\ once_rewrite_tac [GSYM REAL_MUL_ASSOC]
  \\ irule REAL_LT_LMUL_IMP \\ fs[]
  \\ once_rewrite_tac [real_sub]
  \\ once_rewrite_tac [GSYM REAL_LT_ADDNEG2]
  \\ once_rewrite_tac [REAL_NEGNEG]
  \\ once_rewrite_tac [RealArith.REAL_ARITH ``2:real = 1+1``]
  \\ irule REAL_LT_IADD \\ fs[]
  \\ once_rewrite_tac [GSYM REAL_INV1]
  \\ irule REAL_LT_INV \\ fs[]
  \\ `1 = 2 pow 0` by (fs[pow])
  \\ pop_assum (fn thm => once_rewrite_tac [thm])
  \\ irule REAL_POW_MONO_LT \\ fs[]
QED

Theorem normalValue_implies_normalization:
  !v.
    normal v M64 ==>
    normalizes (:52 #11) v
Proof
  rewrite_tac[normal_def, minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
  \\ rpt strip_tac
  \\ fs[normalizes_def, wordsTheory.INT_MAX_def, minExponentPos_def,
        wordsTheory.INT_MIN_def, wordsTheory.dimindex_11,
        wordsTheory.UINT_MAX_def, wordsTheory.dimword_11]
  \\ irule REAL_LET_TRANS
  \\ qexists_tac `maxValue M64` \\ fs[threshold_64_bit_lt_maxValue, GSYM REAL_OF_NUM_POW, maxValue_def]
QED

Theorem normalValue_implies_finiteness:
  !v.
    normal v M64 ==>
    float_is_finite ((real_to_float dmode v):(52 , 11) float)
Proof
  rpt strip_tac
  \\ fs [real_to_float_def, normal_def, dmode_def]
  \\ irule float_round_finite
  \\ irule REAL_LET_TRANS
  \\ qexists_tac `maxValue M64` \\ fs[threshold_64_bit_lt_maxValue]
QED

Theorem denormalValue_implies_finiteness:
  !v.
    denormal v M64 ==>
    float_is_finite ((real_to_float dmode v):(52 , 11) float)
Proof
  rpt strip_tac
  \\ fs [real_to_float_def, denormal_def, dmode_def]
  \\ irule float_round_finite
  \\ irule REAL_LT_TRANS
  \\ qexists_tac `minValue_pos M64` \\ fs[]
  \\ irule REAL_LET_TRANS \\ qexists_tac `maxValue M64`
  \\ `minValue_pos M64 <= 1`
        by (fs[minValue_pos_def, minExponentPos_def]
            \\ once_rewrite_tac [GSYM REAL_INV1]
            \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[])
  \\ fs[threshold_64_bit_lt_maxValue]
  \\ irule REAL_LE_TRANS \\ qexists_tac `1`
  \\ fs[maxValue_def, maxExponent_def]
QED

Theorem normal_value_is_float_value:
  ∀ ff.
    normal (float_to_real ((ff):(52,11) float)) M64 ⇒
    float_value ff = Float (float_to_real ff)
Proof
  rpt strip_tac
  \\ rewrite_tac[float_value_def]
  \\ rw_thm_asm `normal _ _` normal_def
  \\ fs[float_to_real_def]
  \\ every_case_tac
  \\ fs [maxValue_def, maxExponent_def, minValue_pos_def, minExponentPos_def,
         GSYM REAL_OF_NUM_POW, pow_simp1, REAL_DIV_LZERO]
  >-(Cases_on `ff.Sign` \\ fs[]
    \\ Cases_on `n` \\ fs[pow]
    >- (fs[GSYM POW_ABS, abs, REAL_OF_NUM_POW])
    \\ Cases_on `n'` \\ fs[pow,REAL_ABS_MUL, abs, REAL_OF_NUM_POW])
  \\ qpat_x_assum `abs _ <= _` MP_TAC
  \\ qmatch_abbrev_tac `abs (cst1 * cst2) <= cst3 ==> _`
  \\ strip_tac
  \\ Cases_on `ff.Sign` \\ fs[]
  \\ Cases_on `n` \\ fs[pow]
  >- (unabbrev_all_tac
      \\ fs[ABS_MUL, GSYM POW_ABS]
      \\ `abs 2 = 2` by (fs[abs]) \\ fs[]
      \\ `abs (1 + &w2n ff.Significand / 2 pow 52) = 1 + &w2n ff.Significand / 2 pow 52`
          by (rewrite_tac [ABS_REFL]
              \\ irule REAL_LE_ADD \\ fs[])
      \\ qpat_x_assum `abs (1 + _) = _` (fn thm => fs[thm])
      \\ `2 pow 1024 <= 2 pow 1023`
        by (irule REAL_LE_TRANS \\ find_exists_tac \\ fs[]
            \\ rewrite_tac [REAL_LDISTRIB, REAL_MUL_RID]
            \\ qabbrev_tac `res = 2 pow 1024 + 2 pow 1024 * (&w2n ff.Significand / 2 pow 52)`
            \\ qspec_then `2 pow 1024` (fn thm => once_rewrite_tac [GSYM thm]) REAL_ADD_RID
            \\ unabbrev_all_tac
            \\ irule REAL_LE_LADD_IMP
            \\ irule REAL_LE_MUL \\ fs[])
      \\ fs[REAL_OF_NUM_POW])
  \\ Cases_on `n'` \\ fs[]
  \\ Cases_on `ff.Significand` \\ fs[]
  \\ Cases_on `n` \\ fs[pow]
  \\ `abs (cst1 * cst2) = -(cst1 * cst2)`
    by (
    fs[abs]
    \\ ‘~ (0 ≤ cst1 * cst2)’ suffices_by (fs[])
    \\ unabbrev_all_tac
    \\ once_rewrite_tac [REAL_NOT_LE]
    \\ simp [GSYM REAL_NEG_LT0]
    \\ rewrite_tac [GSYM REAL_MUL_ASSOC, GSYM REAL_NEG_MINUS1]
    \\ fs[REAL_NEG_LT0]
    \\ once_rewrite_tac [REAL_MUL_LNEG] \\ fs[REAL_NEG_LT0]
    \\ irule REAL_LT_MUL \\ fs[]
    \\ irule REAL_LT_ADD \\ fs[]
    \\ irule REAL_LT_DIV \\ fs[])
  \\ rw_asm_star `abs _ = _`
  \\ `- cst1 <= cst3`
      suffices_by (unabbrev_all_tac \\ fs[REAL_NEG_LMUL, REAL_NEGNEG, REAL_OF_NUM_POW])
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `- (cst1 * cst2)` \\ conj_tac \\ TRY (unabbrev_all_tac \\ fs[]\\ FAIL_TAC "")
  \\ once_rewrite_tac [RealArith.REAL_ARITH ``-cst1:real = -cst1 * 1``]
  \\ once_rewrite_tac [RealArith.REAL_ARITH ``- (cst1 * cst2) * 1 = - cst1 * cst2:real``]
  \\ irule REAL_LE_LMUL_IMP
  \\ unabbrev_all_tac \\ fs[]
  \\ once_rewrite_tac [REAL_LE_ADDR]
  \\ rewrite_tac [GSYM REAL_NEG_MINUS1]
  \\ fs[REAL_NEG_LT0]
QED

Theorem denormal_value_is_float_value:
  ∀ ff:(52,11) float.
      denormal (float_to_real ff) M64 ==>
      float_value ff = Float (float_to_real ff)
Proof
  rpt strip_tac
  \\ rewrite_tac[float_value_def]
  \\ rw_thm_asm `denormal _ _` denormal_def
  \\ TOP_CASE_TAC \\ fs[]
  \\ rw_thm_asm `abs _ < _` float_to_real_def
  \\ fs[]
  \\ `ff.Exponent <> 0w` by fs[] \\ fs[]
  \\ Cases_on `ff` \\ fs[]
  \\ `w2n (-1w:word11) = 2047` by EVAL_TAC
  \\ `w2n c0 = 2047` by fs[] \\ fs[]
  \\ TOP_CASE_TAC \\ fs[minValue_pos_def, minExponentPos_def]
  \\ fs[REAL_ABS_MUL, POW_M1]
  >- (
    qpat_x_assum ‘_ < inv _’ mp_tac
    \\ qmatch_goalsub_abbrev_tac ‘_ < inv cst1 ⇒ _’
    \\ strip_tac
    \\ `inv cst1 <= inv 1`
        by (unabbrev_all_tac \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[])
    \\ fs[pow_simp1, REAL_DIV_LZERO, ABS_1, REAL_OF_NUM_POW, abs]
    \\ qpat_x_assum ‘_ < inv cst1’ mp_tac
    \\ qmatch_goalsub_abbrev_tac ‘cst2 < inv cst1’ \\ strip_tac
    \\ `cst2 < inv 1`
      by (unabbrev_all_tac \\ irule REAL_LTE_TRANS \\ asm_exists_tac \\ fs[])
    \\ unabbrev_all_tac \\ fs[REAL_INV1])
  \\ Cases_on `c1` \\ fs[]
  \\ `1 < abs (1 + &n / 4503599627370496)`
    by (fs[abs]
        \\ `0:real <= 1 + &n / 4503599627370496`
               by (irule REAL_LE_TRANS
                   \\ qexists_tac `1` \\ fs[]
                   \\ irule REAL_LE_DIV \\ fs[])
        \\ fs[]
        \\ once_rewrite_tac [GSYM REAL_ADD_RID]
        \\ once_rewrite_tac [GSYM REAL_ADD_ASSOC]
        \\ fs[]
        \\ irule REAL_LT_DIV \\ fs[])
  \\ qpat_x_assum ‘_ < inv _’ mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘_ < inv cst1 ⇒ _’
  \\ `inv cst1 <=  inv 1`
    by (unabbrev_all_tac \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[])
  \\ strip_tac
  \\ fs[pow_simp1, REAL_DIV_LZERO, ABS_1, REAL_OF_NUM_POW, abs]
  \\ qpat_x_assum ‘_ < inv cst1’ mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘(cst2 * _) < inv cst1’
  \\ strip_tac
  \\ `cst2 < inv 1`
    by (unabbrev_all_tac \\ irule REAL_LTE_TRANS \\ once_rewrite_tac[CONJ_COMM]
        \\ rewrite_tac[REAL_INV1] \\ asm_exists_tac \\ fs[]
        \\ qmatch_goalsub_abbrev_tac `cst1 < cst2`
        \\ `0 <= (1:real) + &n / 4503599627370496`
          by (irule REAL_LE_ADD \\ fs[real_div]
              \\ irule REAL_LE_MUL \\ fs[]
              \\ irule REAL_LE_INV \\ fs[])
        \\ fs[]
        \\ irule REAL_LT_TRANS \\ qexists_tac `cst1 * (1 + &n / 4503599627370496)`
        \\ fs[]
        \\ once_rewrite_tac [GSYM REAL_MUL_RID]
        \\ once_rewrite_tac [GSYM REAL_MUL_ASSOC] \\ irule REAL_LT_LMUL_IMP
        \\ fs[]
        \\ unabbrev_all_tac \\ fs[])
  \\ unabbrev_all_tac \\ fs[REAL_INV1]
QED

Theorem validValue_gives_float_value:
  !ff:(52,11) float.
      validFloatValue (float_to_real ff) M64 ==>
      float_value ff = Float (float_to_real ff)
Proof
  rpt strip_tac \\ fs[validFloatValue_def]
  >- (irule normal_value_is_float_value \\ fs[])
  >- (irule denormal_value_is_float_value \\ fs[])
  \\ fs[GSYM float_is_zero_to_real, float_is_zero_def]
  \\ every_case_tac \\ fs[]
QED

Theorem normalTranslatedValue_implies_finiteness:
  !ff:double.
      normal (float_to_real ff) M64 ==>
      float_is_finite ff
Proof
  rpt strip_tac
  \\ fs[float_is_finite_def]
  \\ qspec_then `ff` impl_subgoal_tac normal_value_is_float_value
  \\ fs[]
QED

Theorem denormalTranslatedValue_implies_finiteness:
  !ff:double.
    denormal (float_to_real ff) M64 ==>
    float_is_finite ff
Proof
  rpt strip_tac
  \\ fs[float_is_finite_def]
  \\ qspec_then `ff` impl_subgoal_tac denormal_value_is_float_value
  \\ fs[]
QED

Theorem zero_value_implies_finiteness:
  !v. v= 0 ==> float_is_finite ((real_to_float dmode v))
Proof
  rpt strip_tac \\ rveq
  \\ fs[real_to_float_def, dmode_def]
  \\ irule float_round_finite
  \\ fs[threshold_is_positive]
QED

Theorem finite_float_implies_threshold:
  !f:(α , β) float.
    float_is_finite f ==>
    ~(float_to_real f ≤ -threshold (:α # β)) /\
    ~(float_to_real f ≥ threshold (:α # β))
Proof
  rpt strip_tac
  \\ drule lift_ieeeTheory.float_to_real_threshold
  \\ simp[realTheory.abs]
  \\ every_case_tac
  \\ strip_tac \\ RealArith.REAL_ASM_ARITH_TAC
QED

Theorem round_float_to_real_id:
  !f.
    float_is_finite f /\
    float_is_normal f /\
    ~ float_is_zero f ==>
    round roundTiesToEven (float_to_real f) = f
Proof
  rw[]
  \\ qpat_assum `float_is_finite _` mp_tac
  \\ qpat_assum `float_is_normal _` mp_tac
  \\ rewrite_tac [float_is_finite_def, float_is_normal_def]
  \\ rewrite_tac [float_value_def]
  \\ simp[]
  \\ strip_tac
  \\ once_rewrite_tac [round_def]
  \\ fs[finite_float_implies_threshold]
  \\ once_rewrite_tac [closest_such_def]
  \\ SELECT_ELIM_TAC
  \\ rw[]
  >- (qexists_tac `f`
      \\ rw[is_closest_def, IN_DEF, realTheory.ABS_POS]
      \\ Cases_on `f = b` \\ fs[]
      \\ first_x_assum (qspec_then `f` mp_tac)
      \\ fs[realTheory.REAL_SUB_REFL]
      \\ strip_tac
      \\ fs[float_to_real_eq]
      \\ rfs[])
  \\ CCONTR_TAC
  \\ fs[is_closest_def, IN_DEF]
  \\ qpat_x_assum `!x._ ` mp_tac
  \\ first_x_assum (qspec_then `f` mp_tac)
  \\ fs[realTheory.REAL_SUB_REFL]
  \\ rpt strip_tac
  \\ fs[float_to_real_eq]
  \\ rfs[]
QED

Theorem real_to_float_id:
  !f.
     float_is_finite f /\
     float_is_normal f /\
     ~ float_is_zero f ==>
     real_to_float dmode (float_to_real f) = f
Proof
  rpt strip_tac
  \\ fs[dmode_def, real_to_float_def, float_round_def, round_float_to_real_id]
QED

Theorem real_to_float_float_id:
  !f.
    fp64_isFinite f /\
    fp64_isNormal f /\
    ~ fp64_isZero f ==>
    float_to_fp64 (real_to_float dmode (float_to_real (fp64_to_float f))) = f
Proof
  rpt strip_tac
  \\ fs[fp64_isFinite_def, fp64_isZero_def, fp64_isNormal_def]
  \\ fs[real_to_float_id]
  \\ fs[float_to_fp64_fp64_to_float]
QED

Theorem float_to_real_real_to_float_zero_id:
  float_to_real (real_to_float roundTiesToEven 0) = 0
Proof
  once_rewrite_tac[real_to_float_def]
  \\ `float_round roundTiesToEven F 0 = (float_plus_zero(:α#β))`
       by  (irule round_roundTiesToEven_is_plus_zero
            \\ fs[ulp_def, ULP_def, real_div]
            \\ irule REAL_LE_MUL \\ fs[pow]
            \\ irule REAL_LE_INV \\ irule POW_POS \\ fs[])
  \\ fs[float_to_real_def, float_plus_zero_def]
QED

Theorem div_eq0_general:
  !a b:real. b <> 0 ==> (a / b = 0 <=> a = 0)
Proof
  rpt strip_tac \\ Cases_on `0 < b` \\ fs[div_eq0]
  \\ `0 < -b` by RealArith.REAL_ASM_ARITH_TAC
  \\ `a/ -b = 0 <=> a = 0` by fs[div_eq0]
  \\ fs[real_div]
  \\ Cases_on `a = 0` \\ fs[]
  \\ Cases_on `inv b = 0` \\ fs[REAL_INV_NZ]
QED

Theorem float_to_real_round_zero_is_zero:
  !ff P.
    2 * abs ff <=  ulp ((:α#β) :(α#β) itself) ==>
    float_to_real ((float_round roundTiesToEven P ff):(α, β) float) = 0
Proof
  rpt strip_tac \\ Cases_on `P`
  \\ fs [round_roundTiesToEven_is_plus_zero,
         round_roundTiesToEven_is_minus_zero, zero_to_real]
QED

Definition noDowncast_def:
  (noDowncast (Var v) = T) /\
  (noDowncast (Const _ _) = T) /\
  (noDowncast (Unop _ e) = noDowncast e) /\
  (noDowncast (Binop b e1 e2) = (noDowncast e1 /\ noDowncast e2)) /\
  (noDowncast (Fma e1 e2 e3) = (noDowncast e1 /\ noDowncast e2 /\ noDowncast e3)) /\
  (noDowncast (Downcast _ _) = F)
End

Definition noDowncastFun_def:
  (noDowncastFun (Let m x e g) = (noDowncast e /\ noDowncastFun g)) /\
  (noDowncastFun (Ret e) = noDowncast e)
End

Definition is64BitEval_def:
  (is64BitEval ((Const m c):real expr) = (m = M64)) /\
  (is64BitEval (Unop _ e) = is64BitEval e) /\
  (is64BitEval (Binop b e1 e2) = (is64BitEval e1 /\ is64BitEval e2)) /\
  (is64BitEval (Fma e1 e2 e3) = (is64BitEval e1 /\ is64BitEval e2 /\ is64BitEval e3)) /\
  (is64BitEval (Downcast m e) = ((m = M64) /\ is64BitEval e)) /\
  (is64BitEval ((Var v):real expr) = T)
End

Definition is64BitBstep_def:
  (is64BitBstep (Let m x e g) = ((m = M64) /\ is64BitEval e /\ is64BitBstep g)) /\
  (is64BitBstep (Ret e) = is64BitEval e)
End

Definition is64BitEnv_def:
  is64BitEnv Gamma =
  ! e m. FloverMapTree_find e Gamma = SOME m ==> m = M64
End

Theorem typing_expr_64bit:
  !e Gamma.
    is64BitEnv Gamma /\
    validTypes e Gamma ==>
    FloverMapTree_find e Gamma = SOME M64
Proof
  Cases_on `e` \\ fs[Once validTypes_def, is64BitEnv_def]
  \\ rpt strip_tac \\ fs[]
  \\ res_tac
QED

Theorem typing_cmd_64bit:
  !f Gamma.
    is64BitEnv Gamma /\
    validTypesCmd f Gamma ==>
    FloverMapTree_find (getRetExp f) Gamma = SOME M64
Proof
  Cases_on `f` \\ fs[Once validTypes_def, Once validTypesCmd_def, is64BitEnv_def]
  \\ rpt strip_tac \\ fs[]
  \\ res_tac
QED

Theorem eval_expr_gives_IEEE:
  !(e:word64 expr) E1 E2 E2_real Gamma vR A fVars dVars.
    (!x. (toREnv E2) x = E2_real x) /\
    validTypes (toRExp e) Gamma /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2_real /\
    validRanges (toRExp e) A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorbound (toRExp e) Gamma A dVars /\
    FPRangeValidator (toRExp e) A Gamma dVars /\
    eval_expr (toREnv E2) (toRExpMap Gamma) (toRExp e) vR M64 /\
    domain (usedVars (toRExp e)) DIFF domain dVars ⊆ domain fVars ∧
    is64BitEval (toRExp e) /\
    is64BitEnv Gamma /\
    noDowncast (toRExp e) /\
    (∀v.
      v ∈ domain dVars ⇒
      ∃vF m.
      (E2_real v = SOME vF ∧ FloverMapTree_find (Var v) Gamma = SOME m ∧
      validFloatValue vF m)) ==>
    ?v.
      eval_expr_float e E2 = SOME v /\
      eval_expr (toREnv E2) (toRExpMap Gamma) (toRExp e)
      (float_to_real (fp64_to_float v)) M64
Proof
  Induct_on `e` \\ rewrite_tac[toRExp_def] \\ rpt strip_tac
  \\ inversion `eval_expr _ _ _ _ _` eval_expr_cases
  \\ once_rewrite_tac [eval_expr_float_def]
  \\ fs[noDowncast_def]
  >- (once_rewrite_tac [toREnv_def]
      \\ fs[validFloatValue_def]
      \\ rveq
      \\ fs[eval_expr_cases, fp64_to_float_float_to_fp64, dmode_def,
            float_to_real_real_to_float_zero_id]
      \\ fs[toREnv_def]
      \\ fs[eval_expr_float_def, optionLift_def]
      \\ Cases_on `E2 n` \\ fs[optionLift_def])
  >- (rveq \\ fs[eval_expr_cases]
      \\ fs[optionLift_def, minValue_pos_def,
            minExponentPos_def, REAL_LT_INV_EQ]
      \\ qexists_tac `0:real`
      \\ fs[mTypeToR_pos, perturb_def, fp64_to_float_float_to_fp64,
            zero_to_real])
  >- (fs[Once validTypes_def]
      \\ ‘M64 = mG’
        by (first_x_assum irule
            \\ qexistsl_tac [‘toREnv E2’, ‘Gamma’, ‘vR’] \\ rveq \\ fs[eval_expr_cases]
            \\ qexistsl_tac [‘m'’, ‘v1’] \\ fs[])
      \\ ‘m' = M64’ by (Cases_on ‘m'’ \\ fs[isCompat_def])
      \\ ‘me = M64’ by (Cases_on ‘me’ \\ fs[isCompat_def])
      \\ rveq \\ fs[isCompat_def] \\ rpt (qpat_x_assum ‘T’ kall_tac)
      \\ fs[eval_expr_float_def]
      \\ first_x_assum
          (qspecl_then
            [`E1`, `E2`, `E2_real`, `Gamma`, `v1`, `A`, `fVars`, `dVars`]
           destruct)
      >- (
       fs[] \\ rpt conj_tac
       >- (fs[Once validTypes_def])
       >- (rveq \\ rpt strip_tac
           \\ drule validTypes_single \\ strip_tac \\ rfs[] \\ rveq
           \\ first_x_assum irule
           \\ find_exists_tac \\ fs[]
           \\ asm_exists_tac \\ fs[])
       >- (fs[Once validRanges_def])
       >- (
         qpat_x_assum ‘validErrorbound _ _ _ _’
         (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
         \\ fs[option_case_eq]
         \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
       >- (
         rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
         \\ fs[]
         \\ Cases_on `FloverMapTree_find (Unop Neg (toRExp e)) A` \\ fs[]
         \\ PairCases_on `x` \\ fs[]
         \\ rw_asm_star `FloverMapTree_find (Unop _ _) Gamma = _`)
       >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def \\ fs[])
       \\ rw_thm_asm `is64BitEval _` is64BitEval_def
       \\ fs[])
      \\ fs[fp64_negate_def, fp64_to_float_float_to_fp64]
      \\ once_rewrite_tac [float_to_real_negate]
      \\ once_rewrite_tac [eval_expr_cases]
      \\ fs[] \\ once_rewrite_tac [CONJ_COMM]
      \\ qexists_tac ‘M64’ \\ fs[isCompat_def]
      \\ asm_exists_tac \\ fs[evalUnop_def])
  >- (
    qpat_x_assum ‘validErrorbound _ _ _ _’
    (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
    \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
  >- (
    fs[Once validTypes_def] \\ rveq
    \\ imp_res_tac validTypes_single
    \\ ‘M64 = m1’
      by (qpat_x_assum ‘isCompat m1 _’ mp_tac \\ Cases_on ‘m1’
          \\ simp[isCompat_def])
    \\ rveq
    \\ ‘M64 = mG’
      by (qpat_x_assum ‘toRExpMap _ _ = SOME _’ mp_tac
          \\ qpat_x_assum ‘FloVerMapTree_find _ _ = SOME mG’ mp_tac
          \\ simp[toRExpMap_def])
    \\ ‘me = M64’
      by (qpat_x_assum ‘isCompat me _’ mp_tac \\ rveq \\ Cases_on ‘me’
          \\ simp[isCompat_def])
    \\ rveq \\ fs[isCompat_def] \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ rveq
    \\ fs[eval_expr_float_def]
    \\ first_x_assum
       (qspecl_then
        [`E1`, `E2`, `E2_real`, `Gamma`, `v1`, `A`, `fVars`, `dVars`]
        destruct)
    >- (
      fs[] \\ rpt conj_tac
      >- (fs[Once validTypes_def])
      >- (rveq \\ rpt strip_tac
          \\ drule validTypes_single \\ strip_tac \\ rfs[] \\ rveq
          \\ first_x_assum irule
          \\ find_exists_tac \\ fs[]
          \\ asm_exists_tac \\ fs[])
      >- (fs[Once validRanges_def])
      >- (
        qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => assume_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq]
        \\ pop_assum mp_tac \\ rpt (TOP_CASE_TAC \\ fs[]))
      >- (
        rw_thm_asm `FPRangeValidator _ _ _ _` FPRangeValidator_def
        \\ fs[]
        \\ Cases_on `FloverMapTree_find (Unop Sqrt (toRExp e)) A` \\ fs[]
        \\ PairCases_on `x` \\ fs[]
        \\ rw_asm_star `FloverMapTree_find (Unop _ _) Gamma = _`)
      >- (rw_thm_asm `domain (usedVars _) DIFF _ SUBSET _` usedVars_def \\ fs[])
      \\ rw_thm_asm `is64BitEval _` is64BitEval_def \\ fs[])
    \\ fs[fp64_sqrt_def, fp64_to_float_float_to_fp64]
    \\ qpat_x_assum `validRanges _ _ _ _` mp_tac
    \\ simp[Once validRanges_def] \\ rpt strip_tac
    \\ imp_res_tac validRanges_single
    \\ rename1 ‘FloverMapTree_find (toRExp e) A = SOME (iv1, err1)’
    \\ ‘0 < IVlo iv1’ by (res_tac \\ gs[IVlo_def])
    \\ rename1 ‘IVlo iv1 ≤ vR1’
    (* Obtain evaluation for E2_real*)
    \\ ‘!vF1 m1. eval_expr E2_real (toRExpMap Gamma) (toRExp e) vF1 m1 ==>
       abs (vR1 - vF1) <= err1’
      by (qspecl_then [`toRExp e`, `E1`, `E2_real`, `A`,`vR1`,
                       `err1`, `IVlo iv1`, `IVhi iv1`, `fVars`,
                       `dVars`,`Gamma`] destruct validErrorbound_sound
          \\ rpt conj_tac \\ fs[]
          >- (fs [DIFF_DEF, SUBSET_DEF]
              \\ rpt strip_tac \\ first_x_assum irule
              \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
        \\ qpat_x_assum ‘validErrorbound _ _ _ _’
        (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
        \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ ‘validFloatValue (float_to_real (fp64_to_float v)) M64’
       by (drule FPRangeValidator_sound
           \\ disch_then $ qspecl_then [‘toRExp e’, ‘fp64_to_real v’, ‘M64’] mp_tac
           \\ gs[] \\ impl_tac
           >- (rpt conj_tac
               >- (drule eval_eq_env
                   \\ rpt $ disch_then drule \\ gs[fp64_to_real_def])
               >- (
                qpat_x_assum ‘validErrorbound _ _ _ _’
                (fn thm => mp_tac (ONCE_REWRITE_RULE [validErrorbound_def] thm))
                \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
               >- (
                qpat_x_assum ‘FPRangeValidator _ _ _ _’
                (fn thm => mp_tac (ONCE_REWRITE_RULE [FPRangeValidator_def] thm))
                \\ fs[option_case_eq] \\ rpt (TOP_CASE_TAC \\ fs[]))
               \\ fs [DIFF_DEF, SUBSET_DEF]
               \\ rpt strip_tac \\ first_x_assum irule
               \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
           \\ simp[fp64_to_real_def])
    \\ ‘contained (float_to_real (fp64_to_float v))
        (widenInterval (FST iv1, SND iv1) err1)’
      by (
        irule distance_gives_iv
        \\ qexists_tac `vR1` \\ fs [contained_def]
        \\ first_x_assum irule
        \\ qexists_tac `M64`
        \\ drule eval_eq_env
        \\ rpt (disch_then drule) \\ fs[])
    \\ ‘0 < FST (widenInterval (FST iv1, SND iv1) err1)’
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
            [`Unop Sqrt (toRExp e)`,
             `evalUnop Sqrt (float_to_real (fp64_to_float v))`, `M64`]
            irule)
        \\ fs[]
        \\ qexists_tac ‘e’ \\ fs[]
        \\ rpt conj_tac
        >- (simp[Once validTypes_def, isCompat_def] \\ first_x_assum MATCH_ACCEPT_TAC)
        >- (simp[Once validRanges_def] \\ asm_exists_tac \\ fs[]
            \\ fs[] \\ rveq \\ fs[])
        \\ irule eval_eq_env
        \\ qexists_tac ‘toREnv E2’ \\ rpt conj_tac >- fs[]
        \\ irule Unop_sqrt'
        \\ qexistsl_tac [‘0’, `M64`, ‘M64’, `float_to_real (fp64_to_float v)`]
        \\ fs[perturb_def, evalUnop_def, mTypeToR_pos, isCompat_def])
    \\ qpat_x_assum `validFloatValue (evalUnop _ _) M64` (assume_tac o SIMP_RULE std_ss [validFloatValue_def])
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
        \\ fs[dmode_def] \\ simp[Once eval_expr_cases]
        \\ qexistsl_tac [`M64`, `float_to_real (fp64_to_float v)`, ‘e'’]
        \\ fs[perturb_def, evalUnop_def]
        \\ imp_res_tac normal_not_denormal
        \\ fs[REAL_INV_1OVER, mTypeToR_def, isCompat_def])
    (* denormal sqrt *)
    >- (
      Q.ISPEC_THEN `(fp64_to_float v):(52,11) float`
                                      impl_subgoal_tac
                                      float_sqrt_relative_denorm
      >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
          >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW, evalUnop_def]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
          \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
      \\ gs[dmode_def] \\ simp[Once eval_expr_cases]
      \\ qexistsl_tac [`M64`, `float_to_real (fp64_to_float v)`, ‘e'’]
      \\ fs[perturb_def, evalUnop_def]
      \\ fs[REAL_INV_1OVER, mTypeToR_def, isCompat_def, minExponentPos_def])
    (* sqrt 0 *)
    \\ ‘0 < sqrt (float_to_real (fp64_to_float v))’ by (irule SQRT_POS_LT \\ gs[])
    \\ gs[evalUnop_def])
  >- (
    rename1 `Binop b (toRExp e1) (toRExp e2)` \\ rveq
    \\ IMP_RES_TAC validRanges_single
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
       (qspecl_then [`E1`, `E2`,`E2_real`, `Gamma`] assume_tac))
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
    \\ rename1 `eval_expr_float e1 _ = SOME vF1`
    \\ rename1 `eval_expr_float e2 _ = SOME vF2`
    \\ imp_res_tac validRanges_single
    \\ rename1 `FloverMapTree_find (toRExp e2) A = SOME (iv2, err2)`
    \\ rename1 `FloverMapTree_find (toRExp e1) A = SOME (iv1, err1)`
    \\ rename1 `eval_expr E1 _ (toREval (toRExp e2)) nR2 REAL`
    \\ rename1 `eval_expr E1 _ (toREval (toRExp e1)) nR1 REAL`
    (* Obtain evaluation for E2_real*)
    \\ ‘!vF2 m2. eval_expr E2_real (toRExpMap Gamma) (toRExp e2) vF2 m2 ==>
       abs (nR2 - vF2) <= err2’
      by (qspecl_then [`toRExp e2`, `E1`, `E2_real`, `A`,`nR2`,
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
            \\ qexists_tac `M64`
            \\ drule eval_eq_env
            \\ rpt (disch_then drule) \\ fs[])
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
                     [`(Binop b (toRExp e1) (toRExp e2))`,
                      `evalBinop b (float_to_real (fp64_to_float vF1))
                        (float_to_real (fp64_to_float vF2))`,
                      `M64`] irule)
               \\ fs[]
               \\ qexistsl_tac [`e1`, `e2`] \\ fs[]
               \\ rpt conj_tac
               >- (simp[Once validTypes_def] \\ first_x_assum MATCH_ACCEPT_TAC)
               >- (simp[Once validRanges_def] \\ asm_exists_tac \\ fs[]
                   \\ fs[] \\ rveq \\ fs[])
               \\ irule eval_eq_env
              \\ qexists_tac ‘toREnv E2’ \\ rpt conj_tac >- fs[]
              \\ irule Binop_dist'
              \\ qexistsl_tac [‘0’, `M64`, `M64`, ‘M64’, `float_to_real (fp64_to_float vF1)`,
                                `float_to_real (fp64_to_float vF2)`]
              \\ Cases_on `b`
              \\ fs[perturb_def, evalBinop_def, mTypeToR_pos])
      \\ `validFloatValue (float_to_real (fp64_to_float vF1)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`toRExp e1`, `float_to_real (fp64_to_float vF1)`,
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
               \\ irule eval_eq_env
               \\ find_exists_tac \\ fs[])
      \\ `validFloatValue (float_to_real (fp64_to_float vF2)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`toRExp e2`, `float_to_real (fp64_to_float vF2)`,
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
               \\ irule eval_eq_env
               \\ find_exists_tac \\ fs[])
    \\ qpat_x_assum `validFloatValue (evalBinop _ _ _) M64` (assume_tac o SIMP_RULE std_ss [validFloatValue_def])
    (** Case distinction for operator **)
    \\ Cases_on `b` \\ fs[optionLift_def, PULL_EXISTS]
    \\ simp[Once eval_expr_cases]
    (* Addition, result normal *)
    >- (fs[fp64_add_def, fp64_to_float_float_to_fp64, evalBinop_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
            impl_subgoal_tac
            float_add_relative
        >- (rpt conj_tac
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
        \\ fs[REAL_INV_1OVER, mTypeToR_def])
      (* addition, result denormal *)
    >- (fs[fp64_add_def, fp64_to_float_float_to_fp64, evalBinop_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
            impl_subgoal_tac
            float_add_relative_denorm
        >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
            >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
            \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
        \\ fs[dmode_def]
        \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                         `float_to_real (fp64_to_float vF2)`, `e`]
        \\ fs[perturb_def, evalBinop_def]
        \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
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
          \\ fs[float_to_real_round_zero_is_zero])
      (* Subtraction, normal value *)
      >- (fs[fp64_sub_def, fp64_to_float_float_to_fp64, evalBinop_def]
          \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                               `(fp64_to_float vF2):(52,11) float`]
                 impl_subgoal_tac
                 float_sub_relative
          >- (rpt conj_tac
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
          \\ fs[mTypeToR_def, REAL_INV_1OVER])
      (* Subtraction, denormal value *)
    >- (fs[fp64_sub_def, fp64_to_float_float_to_fp64, evalBinop_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
            impl_subgoal_tac
            float_sub_relative_denorm
        >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
            >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
            \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
        \\ fs[dmode_def]
        \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                         `float_to_real (fp64_to_float vF2)`, `e`]
        \\ fs[perturb_def, evalBinop_def]
        \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
      (* subtraction, result = 0 *)
      >- (fs[evalBinop_def]
          \\ qpat_x_assum `float_to_real (fp64_to_float _) = _` MP_TAC
          \\ simp[real_sub, REAL_LNEG_UNIQ, evalBinop_def]
          \\ fs[fp64_sub_def, dmode_def, fp64_to_float_float_to_fp64]
          \\ fs[float_sub_def]
          \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
          \\ fs[validValue_gives_float_value, float_round_with_flags_def]
          \\ strip_tac
          \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`, `float_to_real (fp64_to_float vF2)`, `0:real`]
          \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
          \\ fs[validValue_gives_float_value, float_round_with_flags_def]
          \\ `2 * abs (0:real) <= ulp (:52 #11)`
            by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
                \\ once_rewrite_tac [real_div]
                \\ irule REAL_LE_MUL \\ fs[]
                \\ irule REAL_LE_INV \\ fs[])
          \\ fs[ float_to_real_round_zero_is_zero])
      (* Multiplication, normal result *)
      >- (fs[fp64_mul_def, fp64_to_float_float_to_fp64, evalBinop_def]
          \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                            `(fp64_to_float vF2):(52,11) float`]
               impl_subgoal_tac
               float_mul_relative
           >- (rpt conj_tac
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
               \\ fs[mTypeToR_def, REAL_INV_1OVER])
      (* Multiplication, denormal result *)
    >- (fs[fp64_mul_def, fp64_to_float_float_to_fp64, evalBinop_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
            impl_subgoal_tac
            float_mul_relative_denorm
        >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
            >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
            \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
        \\ fs[dmode_def]
        \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                         `float_to_real (fp64_to_float vF2)`, `e`]
        \\ fs[perturb_def, evalBinop_def]
        \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
       (* multiplication, result = 0 *)
      >- (fs[evalBinop_def, REAL_ENTIRE, fp64_mul_def, float_mul_def,
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
                    round_roundTiesToEven_is_minus_zero, zero_to_real]
             \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                    `float_to_real (fp64_to_float vF2)`, `0:real`]
             \\ rveq
             \\ fs[GSYM float_is_zero_to_real, float_is_zero_def,
                   mTypeToR_pos, perturb_def])
      (* Division, normal result *)
      >- (fs[fp64_div_def, fp64_to_float_float_to_fp64, evalBinop_def]
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
               \\ fs[perturb_def, evalBinop_def]
               \\ imp_res_tac normal_not_denormal
               \\ fs[mTypeToR_def, REAL_INV_1OVER])
      (* Division, denormal result *)
    >- (fs[fp64_div_def, fp64_to_float_float_to_fp64, evalBinop_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
            impl_subgoal_tac
            float_div_relative_denorm
        >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
            >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
            \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
        \\ fs[dmode_def]
        \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                         `float_to_real (fp64_to_float vF2)`, `e`]
        \\ fs[perturb_def, evalBinop_def]
        \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
      (* division, result = 0 *)
       >- (fs[fp64_div_def, dmode_def, fp64_to_float_float_to_fp64,
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
         \\ fs[perturb_def, mTypeToR_pos, float_to_real_round_zero_is_zero])
      (* division, result normal *)
      >- (fs[fp64_div_def, fp64_to_float_float_to_fp64, evalBinop_def]
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
               \\ fs[perturb_def, evalBinop_def]
               \\ imp_res_tac normal_not_denormal
               \\ fs[mTypeToR_def, REAL_INV_1OVER])
       (* division, result denormal *)
    >- (fs[fp64_div_def, fp64_to_float_float_to_fp64, evalBinop_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`]
            impl_subgoal_tac
            float_div_relative_denorm
        >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
            >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
            \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
        \\ fs[dmode_def]
        \\ qexistsl_tac [`M64`, `M64`, `float_to_real (fp64_to_float vF1)`,
                         `float_to_real (fp64_to_float vF2)`, `e`]
        \\ fs[perturb_def, evalBinop_def]
        \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
       (* division, result = 0 *)
       >- (fs[fp64_div_def, dmode_def, fp64_to_float_float_to_fp64,
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
         \\ fs[perturb_def, mTypeToR_pos, float_to_real_round_zero_is_zero]))
  >- (rename1 `Fma (toRExp e1) (toRExp e2) (toRExp e3)`
      \\ IMP_RES_TAC validRanges_single
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
            (qspecl_then [`E1`, `E2`,`E2_real`, `Gamma`] assume_tac))
      \\ first_x_assum (qspecl_then [`v1`, `A`, `fVars`, `dVars`] destruct)
      >- (rpt conj_tac \\ fs[]
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
      >- (rpt conj_tac \\ fs[]
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
      >- (rpt conj_tac \\ fs[]
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
      \\ rename1 ‘eval_expr_float e1 E2 = SOME vF1’
      \\ rename1 ‘eval_expr_float e2 E2 = SOME vF2’
      \\ rename1 ‘eval_expr_float e3 E2 = SOME vF3’
      \\ `validFloatValue
            (evalFma (float_to_real (fp64_to_float vF1))
             (float_to_real (fp64_to_float vF2))
             (float_to_real (fp64_to_float vF3))) M64`
          by (drule FPRangeValidator_sound
              \\ disch_then
                   (qspecl_then
                     [`(Fma (toRExp e1) (toRExp e2) (toRExp e3))`,
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
               \\ irule eval_eq_env \\ asm_exists_tac
               \\ conj_tac >- fs[]
               \\ simp[Once eval_expr_cases]
               \\ qexistsl_tac [`M64`, `M64`, ‘M64’, `float_to_real (fp64_to_float vF1)`,
                                `float_to_real (fp64_to_float vF2)`,
                                `float_to_real (fp64_to_float vF3)`, `0:real`]
               \\ fs[perturb_def, evalFma_def, mTypeToR_pos])
      \\ `validFloatValue (float_to_real (fp64_to_float vF1)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`toRExp e1`, `float_to_real (fp64_to_float vF1)`,
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
               \\ irule eval_eq_env \\ asm_exists_tac \\ fs[])
      \\ `validFloatValue (float_to_real (fp64_to_float vF2)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`toRExp e2`, `float_to_real (fp64_to_float vF2)`,
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
               \\ irule eval_eq_env \\ asm_exists_tac \\ fs[])
      \\ `validFloatValue (float_to_real (fp64_to_float vF3)) M64`
           by (drule FPRangeValidator_sound
               \\ disch_then
                    (qspecl_then
                       [`toRExp e3`, `float_to_real (fp64_to_float vF3)`,
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
               \\ irule eval_eq_env \\ asm_exists_tac \\ fs[])
      \\ qpat_x_assum ‘validFloatValue (evalFma _ _ _) _’
                      (assume_tac o SIMP_RULE std_ss [validFloatValue_def])
      \\ fs[optionLift_def]
      \\ simp[Once eval_expr_cases, PULL_EXISTS]
      \\ rewrite_tac [CONJ_ASSOC]
      \\ ntac 3 (once_rewrite_tac [CONJ_COMM] \\ asm_exists_tac \\ fs[])
      \\ fs[evalFma_def, evalBinop_def, fp64_mul_add_def, fp64_to_float_float_to_fp64]
      >- (
        Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`,
                          `(fp64_to_float vF3):(52,11) float`]
                         impl_subgoal_tac
               float_mul_add_relative
        >- (rpt conj_tac
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
      (* result denormal MARKER *)
    >- (fs[fp64_mul_add_def, fp64_to_float_float_to_fp64, evalFma_def]
        \\ Q.ISPECL_THEN [`(fp64_to_float vF1):(52,11) float`,
                          `(fp64_to_float vF2):(52,11) float`,
                          `(fp64_to_float vF3):(52,11) float`]
            impl_subgoal_tac
            float_mul_add_relative_denorm
        >- (rpt conj_tac
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
             \\ rewrite_tac [INT_MAX_def, INT_MIN_def, dimindex_11, EVAL “2 ** (11 - 1) - 1 - 1”]
             \\ irule REAL_LT_TRANS
             \\ asm_exists_tac \\ fs[GSYM REAL_OF_NUM_POW, minExponentPos_def]
             \\ irule REAL_LET_TRANS \\ qexists_tac ‘1 * inv (2 pow 1022)’
             \\ conj_tac
             >- (rewrite_tac[real_div] \\ irule REAL_LT_RMUL_IMP \\ fs[])
             \\ fs[])
            >- (irule REAL_LT_TRANS \\ qexists_tac ‘maxValue M64’
                \\ fs[threshold_64_bit_lt_maxValue, denormal_def]
                \\ irule REAL_LTE_TRANS \\ qexists_tac ‘minValue_pos M64’
                \\ fs[minValue_pos_def, maxValue_def, GSYM REAL_OF_NUM_POW]
                \\ irule REAL_LE_TRANS \\ qexists_tac ‘1’ \\ conj_tac
                >- (once_rewrite_tac[GSYM REAL_INV1] \\ irule REAL_INV_LE_ANTIMONO_IMPR
                    \\ fs[POW_2_LE1])
                \\ fs[POW_2_LE1])
            \\ fs[INT_MAX_def, INT_MIN_def, dimindex_11])
        \\ fs[dmode_def] \\ qexists_tac ‘e’
        \\ fs[perturb_def, evalFma_def]
        \\ fs[mTypeToR_def, minExponentPos_def, REAL_INV_1OVER])
      (* result = 0 *)
      >- (IMP_RES_TAC validValue_gives_float_value
          \\ fs[REAL_LNEG_UNIQ, evalFma_def, evalBinop_def]
          \\ fs[fp64_add_def, dmode_def, fp64_mul_def, fp64_to_float_float_to_fp64]
          \\ fs[float_mul_add_def, float_round_with_flags_def]
          \\ qexistsl_tac [`0:real`]
          \\ fs[perturb_def, mTypeToR_pos, evalBinop_def]
          \\ fs[float_is_nan_def, float_is_infinite_def]
          \\ `2 * abs (0:real) <= ulp (:52 #11)`
            by (fs[REAL_ABS_0, ulp_def, ULP_def, REAL_OF_NUM_POW]
                \\ once_rewrite_tac [real_div]
                \\ irule REAL_LE_MUL \\ fs[]
                \\ irule REAL_LE_INV \\ fs[])
          \\ fs[float_to_real_round_zero_is_zero]))
QED

Theorem bstep_gives_IEEE:
  !(f:word64 cmd) E1 E2 E2_real Gamma vR vF A fVars dVars outVars.
    (!x. (toREnv E2) x = E2_real x) /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2_real /\
    ssa (toRCmd f) (union fVars dVars) outVars /\
    validTypesCmd (toRCmd f) Gamma /\
    validRangesCmd (toRCmd f) A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorboundCmd (toRCmd f) Gamma A dVars /\
    FPRangeValidatorCmd (toRCmd f) A Gamma dVars /\
    bstep (toREvalCmd (toRCmd f)) E1 (toRTMap (toRExpMap Gamma)) vR REAL /\
    bstep (toRCmd f) (toREnv E2) (toRExpMap Gamma) vF M64 /\
    domain (freeVars (toRCmd f)) DIFF domain dVars ⊆ domain fVars ∧
    is64BitBstep (toRCmd f) /\
    is64BitEnv Gamma /\
    noDowncastFun (toRCmd f) /\
    (∀v.
      v ∈ domain dVars ⇒
      ∃vF m.
      (E2_real v = SOME vF ∧ FloverMapTree_find (Var v) Gamma = SOME m ∧
      validFloatValue vF m)) ==>
    ?v.
      bstep_float f E2 = SOME v /\
      bstep (toRCmd f) (toREnv E2) (toRExpMap Gamma)
        (float_to_real (fp64_to_float v)) M64
Proof
  Induct_on `f`
  \\ simp [toRCmd_def, Once toREvalCmd_def, is64BitBstep_def,
                 noDowncastFun_def]
  \\ rpt strip_tac
  \\ rpt (inversion `bstep (Let _ _ _ _) _ _ _ _` bstep_cases)
  \\ inversion `ssa _ _ _` ssa_cases
  \\ once_rewrite_tac [bstep_float_def]
  \\ fs[noDowncast_def]
  \\ qpat_x_assum ‘validErrorboundCmd _ _ _ _’
     (fn thm => mp_tac (ONCE_REWRITE_RULE[validErrorboundCmd_def] thm))
  \\ fs[option_case_eq]
  >- (rpt (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq \\ fs[]
      \\ `?v_e. eval_expr_float e E2 = SOME v_e /\
         eval_expr (toREnv E2) (toRExpMap Gamma) (toRExp e)
           (float_to_real (fp64_to_float v_e)) M64`
        by (irule eval_expr_gives_IEEE \\ rpt conj_tac \\ fs[]
            >- (fs[Once validTypesCmd_def])
            >- (find_exists_tac \\ fs[])
            \\ qexistsl_tac [`A`, `E1`, `E2_real`, `dVars`, `fVars`]
            \\ rpt conj_tac \\ fs[]
            >- (fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF]
                \\ rpt strip_tac
                \\ `x IN domain fVars \/  x IN domain dVars`
                     by (first_x_assum irule \\ fs[]))
            >- (fs [Once FPRangeValidatorCmd_def])
            \\ fs[Once validRangesCmd_def])
        \\ fs[Once validRangesCmd_def]
        \\ IMP_RES_TAC validRanges_single
        \\ IMP_RES_TAC validRangesCmd_single
        \\ fs[Once validTypesCmd_def]
        (* prove validity of errorbound for floating-point value *)
        \\ qspecl_then
             [`toRExp e`, `E1`, `E2_real`, `A`, `v'`, `r`,
              `FST iv`, `SND iv`, `fVars`, `dVars`, `Gamma`]
             impl_subgoal_tac
             validErrorbound_sound
        >- (fs[DIFF_DEF, SUBSET_DEF]
            \\ rpt strip_tac \\ first_x_assum irule
            \\ fs[Once freeVars_def, domain_union]
            \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[]
            \\ `n IN domain fVars \/ n IN domain dVars`
              by (first_x_assum irule \\ fs[]))
        \\ fs[]
        \\ IMP_RES_TAC meps_0_deterministic \\ rveq
        \\ rename1 `FST iv <= vR_e`
        \\ rename1 ‘FloverMapTree_find (getRetExp (Let M64 n (toRExp e) (toRCmd f))) A =
                    SOME (ivR,errR)’
        \\ rename1 `FST iv_e <= vR_e`
        \\ rename1 `abs (vR_e - nF) <= err_e`
        \\ `abs (vR_e - (float_to_real (fp64_to_float v_e))) <= err_e`
             by (first_x_assum irule \\ fs[]
                 \\ qexists_tac `M64`
                 \\ irule eval_eq_env \\ asm_exists_tac \\ fs[])
        \\ fs[getRetExp_def]
        \\ rename1 `FloverMapTree_find (getRetExp (toRCmd f)) A = SOME (iv_f, err_f)`
        (* Now construct a new evaluation according to our big-step semantics
           using lemma validErrorboundCmd_gives_eval *)
        \\ qspecl_then
             [ `toRCmd f`, `A`, `updEnv n vR_e E1`,
               `updEnv n (float_to_real (fp64_to_float v_e)) E2_real`,
               `outVars`, `fVars`, `insert n () dVars`, `vR`, `FST iv_f`, `SND iv_f`,
               `err_f`, `M64`, `Gamma`]
             impl_subgoal_tac
             validErrorboundCmd_gives_eval
        >- (fs[] \\ rpt conj_tac
            >- (irule approxEnvUpdBound
                \\ fs[lookup_NONE_domain, toRExpMap_def])
            >- (irule ssa_equal_set
                \\ qexists_tac `insert n () (union fVars dVars)`
                \\ conj_tac \\ TRY (fs[] \\ FAIL_TAC "")
                \\ rewrite_tac [domain_union, domain_insert]
                \\ rewrite_tac [UNION_DEF, INSERT_DEF]
                \\ fs[EXTENSION]
                \\ rpt strip_tac
                \\ metis_tac[])
            >- (fs[DIFF_DEF, domain_insert, SUBSET_DEF]
                \\ rpt strip_tac \\ first_x_assum irule
                \\ fs[Once freeVars_def]
                \\ simp[Once freeVars_def, domain_union]))
        \\ fs[optionLift_def]
        (* Instantiate IH with newly obtained evaluation, to get the conclusion *)
        \\ first_x_assum
             (qspecl_then [`updEnv n vR_e E1`, `updFlEnv n v_e E2`,
                           `updEnv n (float_to_real (fp64_to_float v_e)) E2_real`,
                           `Gamma`, `vR`, `vF'`, `A`, `fVars`,
                           `insert n () dVars`, `outVars`]
             impl_subgoal_tac)
        >- (simp[Once validErrorboundCmd_def]
            \\ fs [Once FPRangeValidatorCmd_def, Once validTypesCmd_def,
                   Once validRangesCmd_def]
            \\ rpt conj_tac
            >- (strip_tac \\ fs[updFlEnv_def, updEnv_def, toREnv_def]
                \\ IF_CASES_TAC \\ fs[])
            >- (drule approxEnvUpdBound
                \\ disch_then
                     (qspecl_then
                        [`M64`, `v'`, `float_to_real (fp64_to_float v_e)`, `n`]
                        irule)
                \\ fs[domain_lookup, lookup_NONE_domain, toRExpMap_def])
            >- (irule ssa_equal_set
                \\ qexists_tac `insert n () (union fVars dVars)`
                \\ conj_tac \\ TRY (fs[] \\ FAIL_TAC "")
                \\ rewrite_tac [domain_union, domain_insert]
                \\ rewrite_tac [UNION_DEF, INSERT_DEF]
                \\ fs[EXTENSION]
                \\ rpt strip_tac
                \\ metis_tac[])
            >- (first_x_assum MATCH_ACCEPT_TAC)
            >- (irule bstep_eq_env
                \\ qexists_tac `updEnv n (float_to_real (fp64_to_float v_e)) E2_real`
                \\ conj_tac
                >- (strip_tac \\ fs[updEnv_def, toREnv_def, updFlEnv_def]
                    \\ IF_CASES_TAC \\ fs[])
                \\ reverse (sg `m' = M64`)
                >- (rveq \\ fs[])
                \\ irule bstep_Gamma_det \\ rpt (find_exists_tac \\ fs[]))
            >- (fs[DIFF_DEF, domain_insert, SUBSET_DEF]
                \\ rpt strip_tac \\ first_x_assum irule
                \\ fs[Once freeVars_def]
                \\ simp[Once freeVars_def, domain_union])
            >- (rpt strip_tac \\ simp[updEnv_def]
                \\ rveq \\ fs[]
                >- (irule FPRangeValidator_sound
                    \\ qexistsl_tac [`A`, `E1`, `E2_real`, `Gamma`, `dVars`,
                                     `toRExp e`, `fVars`]
                    \\ fs[]
                    \\ rpt conj_tac \\ TRY (first_x_assum MATCH_ACCEPT_TAC)
                    >- (fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF]
                        \\ rpt strip_tac \\ first_x_assum irule \\ fs[]
                        \\ CCONTR_TAC \\ fs[]
                        \\ rveq \\ fs[]
                        \\ metis_tac [])
                    \\ irule eval_eq_env
                    \\ asm_exists_tac \\ fs[])
                \\ IF_CASES_TAC \\ fs[]
                \\ irule FPRangeValidator_sound
                \\ qexistsl_tac [`A`, `E1`, `E2_real`, `Gamma`, `dVars`,
                                `toRExp e`, `fVars`]
                \\ fs[]
                \\ rpt conj_tac \\ TRY (first_x_assum MATCH_ACCEPT_TAC)
                >- (fs[Once freeVars_def, domain_union, DIFF_DEF, SUBSET_DEF]
                    \\ rpt strip_tac \\ first_x_assum irule \\ fs[]
                    \\ CCONTR_TAC \\ fs[]
                    \\ rveq \\ fs[]
                    \\ metis_tac [])
                \\ irule eval_eq_env
                \\ asm_exists_tac \\ fs[]))
        \\ fs[]
        \\ irule let_b \\ fs[toRExpMap_def] \\ find_exists_tac
        \\ fs[] \\ irule bstep_eq_env
        \\ find_exists_tac \\ fs[]
        \\ strip_tac \\ fs[toREnv_def, updEnv_def, updFlEnv_def]
        \\ IF_CASES_TAC \\ fs[])
  >- (strip_tac \\ fs[bstep_cases] \\ drule eval_expr_gives_IEEE
      \\ disch_then irule \\ rpt conj_tac
      \\ fs[Once validTypesCmd_def]
      >- (find_exists_tac \\ fs[])
      \\ qexistsl_tac [`A`, `E1`, `dVars`, `fVars`]
      \\ rpt conj_tac
      \\ fs[freeVars_def, Once FPRangeValidatorCmd_def, validRangesCmd_def])
QED

val found_tac = TRY (last_x_assum irule \\ find_exists_tac \\ fs[] \\ FAIL_TAC "")
  \\ first_x_assum irule \\ find_exists_tac \\ fs[];

Theorem getValidMap_preserving:
  ∀ e defVars akk res.
    (∀ e m. FloverMapTree_find e akk = SOME m ==> m = M64) /\
    is64BitEval e /\
    getValidMap defVars e akk = Succes res /\
    (∀ e m. FloverMapTree_find e defVars = SOME m ==> m = M64) ==>
    ∀ e m. FloverMapTree_find e res = SOME m ==> m = M64
Proof
  Induct_on `e` \\ once_rewrite_tac[getValidMap_def] \\ rpt strip_tac
  >- (fs[] \\ Cases_on `FloverMapTree_mem (Var n) akk` \\ fs[]
      >- (rveq \\ found_tac)
      \\ EVERY_CASE_TAC \\ fs[]
      \\ rveq \\ fs[map_find_add]
      \\ Cases_on `e = Var n` \\ fs[]
      \\ rveq \\ found_tac)
  >- (fs[] \\ Cases_on `FloverMapTree_mem (Const m v) akk` \\ fs[]
      >- (rveq \\ found_tac)
      \\ Cases_on `FloverMapTree_find (Const m v) defVars` \\ fs[isMonotone_def]
      >- (rveq \\ fs[map_find_add]
          \\ Cases_on `e = Const m v` \\ fs[] \\ rveq
          >- (fs[is64BitEval_def])
          \\ found_tac)
      \\ Cases_on `x = m` \\ fs[]
      \\ rveq \\ fs[map_find_add]
      \\ Cases_on `e = Const m v` \\ fs[] \\ rveq
      >- (fs[is64BitEval_def])
      \\ found_tac)
  >- (fs[is64BitEval_def]
      \\ Cases_on `FloverMapTree_mem (Unop u e) akk` \\ fs[] \\ rveq
      >- (res_tac)
      \\ Cases_on `getValidMap defVars e akk` \\ fs[]
      \\ fs[option_case_eq]
      \\ Cases_on `isFixedPoint m_e1` \\ fs[option_case_eq]
      >- (Cases_on `isCompat m_e1 mFix` \\ fs[addMono_def, option_case_eq]
          \\ rveq \\ fs[map_find_add]
          \\ Cases_on `e' = Unop u e` \\ fs[] \\ rveq
          >- (found_tac)
          \\ res_tac)
      \\ Cases_on `FloverMapTree_find (Unop u e) defVars` \\ fs[isMonotone_def]
      >- (fs[addMono_def, option_case_eq] \\ rveq \\ fs[map_find_add]
          \\ Cases_on `e' = Unop u e` \\ fs[] \\ rveq
          >- (last_x_assum irule \\ fs[]
              \\ qexistsl_tac [`akk`, `defVars`, `e`, `a`]
              \\ fs[] \\ conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
          \\ res_tac)
      \\ Cases_on `x = m_e1` \\ fs[addMono_def, option_case_eq] \\ rveq \\ fs[map_find_add]
      \\ Cases_on `e' = Unop u e` \\ fs[] \\ rveq
      >- (last_x_assum irule \\ fs[]
          \\ qexistsl_tac [`akk`, `defVars`, `e`, `a`]
          \\ fs[] \\ conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ res_tac)
  >- (fs[is64BitEval_def]
      \\ rename1 `Binop b e1 e2`
      \\ Cases_on `FloverMapTree_mem (Binop b e1 e2) akk` \\ fs[] \\ rveq
      >- (res_tac)
      \\ Cases_on `getValidMap defVars e1 akk` \\ fs[]
      \\ Cases_on `getValidMap defVars e2 a` \\ fs[]
      \\ last_x_assum (qspecl_then [`defVars`, `akk`, `a`] destruct)
      >- (fs[] \\ conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ last_x_assum (qspecl_then [`defVars`, `a`, `a'`] destruct)
      >- (fs[] \\ conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ fs[option_case_eq]
      \\ qpat_x_assum `_ = Succes res` mp_tac
      \\ TOP_CASE_TAC \\ pop_assum kall_tac \\ fs[option_case_eq]
      >- (rpt strip_tac \\ qpat_x_assum `_ = Succes res` mp_tac
          \\ TOP_CASE_TAC \\ fs[addMono_def, option_case_eq]
          \\ rpt strip_tac \\ rveq \\ fs[map_find_add]
          \\ Cases_on `e'' =  Binop b e1 e2` \\ fs[]
          >- (rveq \\ metis_tac[])
          \\ metis_tac[])
      \\ TOP_CASE_TAC \\ fs[]
      >- (TOP_CASE_TAC \\ fs[] \\ res_tac \\ fs[])
      >- (TOP_CASE_TAC \\ fs[] \\ res_tac \\ fs[])
      \\ rpt strip_tac \\ qpat_x_assum `_ = Succes res` mp_tac
      \\ ntac 2 (TOP_CASE_TAC \\ fs[addMono_def, option_case_eq])
      \\ rpt strip_tac \\ rveq \\ fs[map_find_add]
      \\ Cases_on `e'' = Binop b e1 e2` \\ fs[]
      >- (rveq
          \\ `t1 = M64` by (metis_tac[])
          \\ `t2 = M64` by (metis_tac[]) \\ rveq \\ fs[join_fl_def])
      \\ metis_tac[])
  >- (fs[is64BitEval_def]
      \\ rename1 `Fma e1 e2 e3`
      \\ qpat_x_assum `_ = Succes res` mp_tac
      \\ TOP_CASE_TAC
      >- (strip_tac \\ rveq \\ res_tac)
      \\ Cases_on `getValidMap defVars e1 akk`
      \\ rewrite_tac [ResultsTheory.result_bind_def] \\ BETA_TAC
      \\ TRY (rpt (first_x_assum kall_tac) \\ strip_tac \\ fs[] \\ FAIL_TAC "")
      \\ Cases_on `getValidMap defVars e2 a`
      \\ rewrite_tac [ResultsTheory.result_bind_def] \\ BETA_TAC
      \\ TRY (rpt (first_x_assum kall_tac) \\ strip_tac \\ fs[] \\ FAIL_TAC "")
      \\ Cases_on `getValidMap defVars e3 a'`
      \\ rewrite_tac [ResultsTheory.result_bind_def] \\ BETA_TAC
      \\ TRY (rpt (first_x_assum kall_tac) \\ strip_tac \\ fs[] \\ FAIL_TAC "")
      \\ last_x_assum (qspecl_then [`defVars`, `akk`, `a`] destruct)
      >- (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ last_x_assum (qspecl_then [`defVars`, `a`, `a'`] destruct)
      >- (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ last_x_assum (qspecl_then [`defVars`, `a'`, `a''`] destruct)
      >- (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ fs[option_case_eq] \\ strip_tac \\ fs[]
      \\ qpat_x_assum `_ = Succes res` mp_tac
      \\ TOP_CASE_TAC \\ pop_assum kall_tac \\ fs[option_case_eq]
      >- (rpt strip_tac \\ qpat_x_assum `_ = Succes res` mp_tac
          \\ TOP_CASE_TAC \\ fs[addMono_def, option_case_eq]
          \\ rpt strip_tac \\ rveq \\ fs[map_find_add]
          \\ Cases_on `e''' =  Fma e1 e2 e3` \\ fs[]
          >- (rveq \\ metis_tac[])
          \\ metis_tac[])
      \\ TOP_CASE_TAC \\ fs[]
      >- (TOP_CASE_TAC \\ fs[] \\ res_tac \\ fs[])
      >- (TOP_CASE_TAC \\ fs[] \\ res_tac \\ fs[])
      >- (TOP_CASE_TAC \\ fs[] \\ res_tac \\ fs[])
      \\ ntac 2 (TOP_CASE_TAC \\ fs[option_case_eq, addMono_def])
      \\ rpt strip_tac \\ rveq \\ fs[map_find_add]
      \\ Cases_on `e''' = Fma e1 e2 e3` \\ fs[]
      >- (rveq
          \\ `t1 = M64` by (metis_tac[])
          \\ `t2 = M64` by (metis_tac[])
          \\ `t3 = M64` by (metis_tac[]) \\ rveq \\ fs[join_fl3_def, join_fl_def])
      \\ metis_tac[])
  \\ qpat_x_assum `_ = Succes res` mp_tac
  \\ TOP_CASE_TAC \\ fs[]
  >- (strip_tac \\ rveq \\ res_tac)
  \\ Cases_on `getValidMap defVars e akk` \\ fs[option_case_eq]
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ fs[is64BitEval_def]
  \\ first_x_assum (qspecl_then [`defVars`, `akk`, `a`] destruct)
  >- (rpt conj_tac \\ first_x_assum MATCH_ACCEPT_TAC)
  \\ TOP_CASE_TAC \\ pop_assum kall_tac \\ fs[option_case_eq]
  >- (rpt strip_tac \\ pop_assum mp_tac
      \\ TOP_CASE_TAC \\ fs[addMono_def, option_case_eq]
      \\ strip_tac \\ rveq \\ fs[map_find_add]
      \\ Cases_on `e' = Downcast m e` \\ fs[] \\ rveq \\ metis_tac[])
  \\ TOP_CASE_TAC \\ fs[addMono_def, option_case_eq]
  \\ strip_tac \\ rveq \\ fs[map_find_add]
  \\ Cases_on `e' = Downcast M64 e` \\ fs[] \\ rveq
  \\ res_tac
QED

Theorem getValidMapCmd_preserving:
  ! f defVars akk res.
    (! e m. FloverMapTree_find e akk = SOME m ==> m = M64) /\
    is64BitBstep f /\
    getValidMapCmd defVars f akk = Succes res /\
    (! e m. FloverMapTree_find e defVars = SOME m ==> m = M64) ==>
    ! e m. FloverMapTree_find e res = SOME m ==> m = M64
Proof
  Induct_on `f` \\ once_rewrite_tac [getValidMapCmd_def]
  \\ rpt strip_tac \\ fs[]
  >- (Cases_on `getValidMap defVars e akk` \\ fs[option_case_eq]
      \\ Cases_on `m = m_e` \\ fs[addMono_def]
      \\ Cases_on `FloverMapTree_find (Var n) a` \\ fs[]
      \\ rveq
      \\ first_x_assum
          (qspecl_then [`defVars`, `FloverMapTree_insert (Var n) m a`, `res`] destruct)
      >- (fs[is64BitBstep_def] \\ conj_tac
          >- (rpt strip_tac \\ fs[map_find_add]
              \\ Cases_on `e'' = Var n` \\ fs[]
              \\ irule getValidMap_preserving
              \\ qexistsl_tac [`akk`, `defVars`, `e`, `e''`, `a`]
              \\ rpt conj_tac \\ fs[])
          \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ first_x_assum irule
      \\ find_exists_tac \\ fs[])
  \\ irule getValidMap_preserving
  \\ qexistsl_tac [`akk`, `defVars`, `e`, `e'`, `res`]
  \\ rpt conj_tac \\ fs[is64BitBstep_def]
QED

Theorem IEEE_connection_expr:
  !(e:word64 expr) (A:analysisResult) (P:precond) E1 E2 defVars fVars Gamma.
      is64BitEval (toRExp e) /\
      is64BitEnv defVars /\
      noDowncast (toRExp e) /\
      fVars_P_sound fVars E1 P /\
      (domain (usedVars (toRExp e))) SUBSET (domain fVars) /\
      CertificateChecker (toRExp e) A P defVars = SOME Gamma /\
      approxEnv E1 (toRExpMap Gamma) A fVars LN (toREnv E2) ==>
        ?iv err vR vF. (* m, currently = M64 *)
          FloverMapTree_find (toRExp e) A = SOME (iv, err) /\
          eval_expr E1 (toRTMap (toRExpMap Gamma)) (toREval (toRExp e)) vR REAL /\
          eval_expr_float e E2 = SOME vF /\
          eval_expr (toREnv E2) (toRExpMap Gamma) (toRExp e)
            (float_to_real (fp64_to_float vF)) M64 /\
          abs (vR - (float_to_real (fp64_to_float vF))) <= err
Proof
  simp [CertificateChecker_def]
  \\ rpt strip_tac
  \\ Cases_on `getValidMap defVars (toRExp e) FloverMapTree_empty` \\ fs[]
  \\ rveq \\ IMP_RES_TAC getValidMap_top_correct
  \\ `validTypes (toRExp e) Gamma`
    by (first_x_assum irule
        \\ fs[FloverMapTree_empty_def, FloverMapTree_mem_def, FloverMapTree_find_def])
  \\ `! e m. FloverMapTree_find e Gamma = SOME m ==> m = M64`
      by (rpt strip_tac \\ irule getValidMap_preserving
          \\ qexistsl_tac [`FloverMapTree_empty`, `defVars`, `toRExp e`, `e'`, `Gamma`]
          \\ rpt conj_tac \\ rpt strip_tac
          \\ fs[FloverMapTree_empty_def, FloverMapTree_find_def , is64BitEnv_def]
          \\ first_x_assum irule \\ find_exists_tac \\ fs[])
  \\ drule validIntervalbounds_sound
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`fVars`,`E1`, `Gamma`] destruct)
  \\ fs[dVars_range_valid_def, fVars_P_sound_def]
  \\ drule validErrorbound_sound
  \\ rpt (disch_then drule)
  \\ IMP_RES_TAC validRanges_single
  \\ disch_then (qspecl_then [`vR`, `err`, `FST iv`, `SND iv`] destruct)
  \\ fs[]
  \\ qspecl_then [`e`, `E1`, `E2`, `toREnv E2`, `Gamma`, `nF`, `A`, `fVars`, `LN`]
       destruct
       eval_expr_gives_IEEE
  >- (rpt conj_tac \\ fs[]
      >- (`FloverMapTree_find (toRExp e) Gamma = SOME M64`
          by (irule typing_expr_64bit \\ fs[is64BitEnv_def]
              \\ first_x_assum MATCH_ACCEPT_TAC)
          \\ `m = M64`
            by (irule validTypes_exec \\ rpt (find_exists_tac \\ fs[]))
          \\ rveq \\ fs[])
      \\ fs[is64BitEnv_def] \\ first_x_assum MATCH_ACCEPT_TAC)
  \\ rpt (find_exists_tac \\ fs[])
  \\ first_x_assum irule \\ find_exists_tac \\ fs[]
QED

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

val _ = export_theory ();
