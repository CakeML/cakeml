(**
  Floating-Point range validator

  The Floating-Point range validator computes an overapproximation of what the
  value of an operation may be using its real-valued range +- the error bound.

  This soundly proves that the runtime value of the exprression must be a valid
  value according to IEEE 754.

**)
open machine_ieeeTheory binary_ieeeTheory lift_ieeeTheory realTheory RealArith;
open AbbrevsTheory MachineTypeTheory TypeValidatorTheory RealSimpsTheory
     RealRangeArithTheory IntervalArithTheory ExpressionsTheory
     ExpressionAbbrevsTheory ExpressionSemanticsTheory FloverTactics
     IntervalValidationTheory ErrorValidationTheory CommandsTheory
     EnvironmentsTheory ssaPrgsTheory;
open preambleFloVer;

val _ = new_theory "FPRangeValidator";

Overload abs[local] = “realax$abs”

Definition FPRangeValidator_def:
  FPRangeValidator (e:real expr) A typeMap dVars =
    case FloverMapTree_find e A, FloverMapTree_find e typeMap of
      | SOME (iv_e, err_e), SOME m =>
        let iv_e_float = widenInterval iv_e err_e in
        let recRes =
            case e of
              | Binop b e1 e2 =>
                FPRangeValidator e1 A typeMap dVars /\
                FPRangeValidator e2 A typeMap dVars
              | Fma e1 e2 e3 =>
                FPRangeValidator e1 A typeMap dVars /\
                FPRangeValidator e2 A typeMap dVars /\
                FPRangeValidator e3 A typeMap dVars
              | Unop u e =>
                FPRangeValidator e A typeMap dVars
              | Downcast m e => FPRangeValidator e A typeMap dVars
              | _ =>  T
        in
        let normal_or_zero =
              ((normal (IVlo iv_e_float) m \/ (IVlo iv_e_float) = 0) /\
              (normal (IVhi iv_e_float) m \/ (IVhi iv_e_float) = 0))
        in
            (case e of
              | Var v =>
                  if (lookup v dVars = SOME ())
                  then T
                  else
                      if (validValue (IVhi iv_e_float) m /\
                          validValue (IVlo iv_e_float) m)
                      then normal_or_zero /\ recRes
                      else
                          F
              | _ => if (validValue (IVhi iv_e_float) m /\
                          validValue (IVlo iv_e_float) m)
                      then normal_or_zero /\ recRes
                      else
                          F)
      | _, _ => F
End

Definition normalOrZero_def:
  normalOrZero iv_e_float m =
    ((normal (IVlo iv_e_float) m \/ (IVlo iv_e_float) = 0) /\
     (normal (IVhi iv_e_float) m \/ (IVhi iv_e_float) = 0))
End

Definition FPRangeValidatorCmd_def:
  (FPRangeValidatorCmd ((Let m x e g):real cmd) A typeMap dVars =
     if FPRangeValidator e A typeMap dVars
     then FPRangeValidatorCmd g A typeMap (insert x () dVars)
     else F) /\
  (FPRangeValidatorCmd (Ret e) A typeMap dVars =
   FPRangeValidator e A typeMap dVars)
End

Theorem enclosure_to_abs:
  !a b c.
     a <= b /\ b <= c /\
    (0 < a \/ c < 0 ) ==>
    (abs a <= abs b /\ abs b <= abs c) \/
    (abs c <= abs b /\ abs b <= abs a)
Proof
  rpt strip_tac \\ fs[]
  >- (`0 < b` by REAL_ASM_ARITH_TAC
      \\ `0 <= a /\ 0 <= b` by REAL_ASM_ARITH_TAC
      \\ `abs a = a` by (fs[ABS_REFL])
      \\ `abs b = b` by (fs[ABS_REFL])
      \\ `0 <= c` by REAL_ASM_ARITH_TAC
      \\ `abs c = c` by (fs[ABS_REFL])
      \\ fs[realTheory.abs])
  >- (`~ (0 <= b)` by REAL_ASM_ARITH_TAC
      \\ `~ (0 <= a)` by REAL_ASM_ARITH_TAC
      \\ `~ (0 <= c)` by REAL_ASM_ARITH_TAC
      \\ fs[realTheory.abs])
QED

fun assume_all l =
  case l of
      t :: ls => assume_tac t \\ assume_all ls
    | NIL =>  ALL_TAC;

Theorem normal_enclosing:
  !v m vHi vLo.
      (0 < vLo \/ vHi < 0) /\
      normal vLo m /\
      normal vHi m /\
      vLo <= v /\ v <= vHi ==>
      normal v m
Proof
  rpt gen_tac
  \\ disch_then (fn thm => assume_all (CONJ_LIST 4  thm))
  \\ `(abs vLo <= abs v /\ abs v <= abs vHi) \/ (abs vHi <= abs v /\ abs v <= abs vLo)`
       by (irule enclosure_to_abs \\ fs[])
  \\ qpat_x_assum `0 < _ \/ _ < 0` kall_tac
  \\ fs[normal_def]
  \\ rveq
  \\ fs[]
  \\ RealArith.REAL_ASM_ARITH_TAC
QED

val solve_tac =
  rpt (qpat_x_assum `!x. _` kall_tac)
  \\ Cases_on `v = 0` \\ TRY(every_case_tac \\ fs[] \\ FAIL_TAC"")
  \\ Cases_on `denormal v m` \\ TRY (every_case_tac \\ fs[] \\ FAIL_TAC "")
  \\ Cases_on `normal v m` \\ TRY (every_case_tac \\ fs[] \\ FAIL_TAC"")
  \\ fs[normal_def, denormal_def, validFloatValue_def, validValue_def] \\ rveq \\ fs[]
  \\ every_case_tac  \\ fs[]
  \\ `abs v <= abs (FST (widenInterval iv_e err_e)) \/
        abs v <= abs (SND (widenInterval iv_e err_e))`
        by (fs[widenInterval_def, IVlo_def, IVhi_def] \\ RealArith.REAL_ASM_ARITH_TAC)
  \\ TRY (every_case_tac \\ RealArith.REAL_ASM_ARITH_TAC);

Theorem FPRangeValidator_sound:
  ∀ e E1 E2 Gamma v m A fVars (dVars:num_set).
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ∧
    eval_expr E2 (toRExpMap Gamma) e v m ∧
    validTypes e Gamma ∧
    validRanges e A E1 (toRTMap (toRExpMap Gamma)) ∧
    validErrorbound e Gamma A dVars ∧
    FPRangeValidator e A Gamma dVars ∧
    domain (usedVars e) DIFF (domain dVars) SUBSET (domain fVars) ∧
    (∀(v:num).
       v IN domain dVars ==>
       (?vF m.
         E2 v = SOME vF ∧ FloverMapTree_find (Var v) Gamma = SOME m ∧
         validFloatValue vF m)) ==>
      validFloatValue v m
Proof
  rpt strip_tac
  \\ IMP_RES_TAC validTypes_single
  \\ `m = mG`
    by (first_x_assum irule
        \\ qexistsl_tac [`E2`, `Gamma`, `v`] \\ fs[])
  \\ rveq
  \\ once_rewrite_tac [validFloatValue_def]
  \\ IMP_RES_TAC validRanges_single \\ fs[]
  \\ rename1 `FloverMapTree_find e A = SOME (iv_e, err_e)` \\ fs[]
  \\ drule validErrorbound_sound
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`vR`, `err_e`, `FST iv_e`, `SND iv_e`] destruct)
  \\ fs[]
  \\ qspecl_then [`vR`, `v`, `err_e`, `iv_e`]
       impl_subgoal_tac
       (SIMP_RULE std_ss [contained_def, widenInterval_def] distance_gives_iv)
  \\ fs[]
  >- (first_x_assum irule \\ qexists_tac `m` \\ fs[])
  \\ Cases_on `e` \\ fs[Once FPRangeValidator_def]
  >- (fs[validFloatValue_def, domain_lookup] \\ res_tac
      \\ fs[] \\ rveq \\ fs[]
      \\ rpt (inversion `eval_expr E2 _ _ _ _` eval_expr_cases)
      \\ fs[] \\ rveq \\ fs[])
  \\ solve_tac
QED

Theorem FPRangeValidatorCmd_sound:
  ∀ f E1 E2 Gamma v vR m A fVars dVars outVars.
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 ∧
    ssa f (union fVars dVars) outVars /\
    bstep (toREvalCmd f) E1 (toRTMap (toRExpMap Gamma)) vR m /\
    bstep f E2 (toRExpMap Gamma) v m ∧
    validTypesCmd f Gamma /\
    validRangesCmd f A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorboundCmd f Gamma A dVars ∧
    FPRangeValidatorCmd f A Gamma dVars ∧
    domain (freeVars f) DIFF domain dVars ⊆ domain fVars ∧
    (!(v:num). v IN domain dVars ==>
      (?vF m. E2 v = SOME vF /\ FloverMapTree_find (Var v) Gamma = SOME m
        /\ validFloatValue vF m)) ==>
    validFloatValue v m
Proof
  Induct
  \\ simp[Once toREvalCmd_def, Once FPRangeValidatorCmd_def,
          Once freeVars_def]
  \\ rpt strip_tac
  >- (
  qpat_x_assum ‘validErrorboundCmd _ _ _ _’
    (mp_tac o SIMP_RULE std_ss [Once validErrorboundCmd_def]) \\ fs[]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[]) \\ strip_tac \\ rveq
  \\ rpt (inversion `bstep (Let _ _ _ _) _ _ _ _` bstep_cases) \\ rveq
  \\ rename1 `bstep (toREvalCmd f) (updEnv n vR_e E1) _ _ mR`
  \\ rename1 `bstep f (updEnv n vF E2) _ _ mF`
  \\ rename1 ‘FloverMapTree_find e A = SOME (iv_e, err_e)’
  \\ fs[Once validTypesCmd_def]
  \\ imp_res_tac validTypes_single
  \\ `m = mG`
    by (first_x_assum irule
        \\ qexistsl_tac [`E2`, `Gamma`, `vF`] \\ fs[])
  \\ rveq
  \\ inversion `ssa _ _ _` ssa_cases
  \\ drule validErrorbound_sound
  \\ disch_then drule
  \\ disch_then
     (qspecl_then [`vR_e`, `err_e`, `FST iv_e`, `SND iv_e`]
      impl_subgoal_tac)
  >- (
    fs[Once validRangesCmd_def]
    \\ fs[DIFF_DEF, SUBSET_DEF] \\ rpt strip_tac \\ first_x_assum irule
    \\ fs[domain_union]
    \\ CCONTR_TAC \\ fs[] \\ rveq
    \\ first_x_assum (qspec_then `n` assume_tac)
    \\ `n IN domain fVars \/  n IN domain dVars`
      suffices_by (fs[])
    \\ fs[])
  \\ fs[Once validRangesCmd_def]
  \\ imp_res_tac validRanges_single
  \\ imp_res_tac meps_0_deterministic \\ rveq \\ fs[]
  \\ rename1 `vR_e <= SND _`
  \\ first_x_assum
     (qspecl_then [`updEnv n vR_e E1`, `updEnv n vF E2`, `Gamma`, `v`, `vR`,
                   `mF`, `A`, `fVars`, `insert n () dVars`, `outVars`]
      impl_subgoal_tac)
  >- (
    fs[] \\ rpt conj_tac
    >- (
      irule approxEnvUpdBound \\ fs[lookup_NONE_domain]
      \\ first_x_assum (qspecl_then [`vF`, `m`] irule)
      \\ qexists_tac `m` \\ fs[])
    >- (
      irule ssa_equal_set
      \\ qexists_tac `insert n () (union fVars dVars)`
      \\ conj_tac \\ TRY (fs[] \\ FAIL_TAC "")
      \\ rewrite_tac [domain_union, domain_insert]
      \\ rewrite_tac [UNION_DEF, INSERT_DEF]
      \\ fs[EXTENSION]
      \\ rpt strip_tac
      \\ metis_tac[])
    >- fs[Once validTypesCmd_def]
    >- (
      imp_res_tac validTypesCmd_single
      \\ find_exists_tac \\ fs[]
      \\ first_x_assum MATCH_ACCEPT_TAC)
    >- (fs[Once validRangesCmd_def])
    >- (
      `validRangesCmd f A (updEnv n vR_e E1) (toRTMap (toRExpMap Gamma))`
         by (first_x_assum irule \\ fs[])
      \\ imp_res_tac validRangesCmd_single
      \\ rpt (find_exists_tac \\ fs[]))
    >- (
      fs[DIFF_DEF, domain_insert, SUBSET_DEF]
      \\ rpt strip_tac \\ first_x_assum irule
      \\ simp[Once freeVars_def]
      \\ once_rewrite_tac [domain_union]
      \\ fs[]
      \\ rw_thm_asm `x IN domain (freeVars f)` freeVars_def
      \\ fs[])
    \\ rpt strip_tac
    \\ fs[updEnv_def] \\ rveq \\ fs[]
    >- (qpat_x_assum `eval_expr E2 _ e nF _` kall_tac
        \\ drule FPRangeValidator_sound
        \\ rpt (disch_then drule)
        \\ disch_then irule \\ fs[]
        \\ fs[DIFF_DEF, domain_insert, SUBSET_DEF]
        \\ rpt strip_tac \\ first_x_assum irule
        \\ simp[Once freeVars_def]
        \\ once_rewrite_tac [domain_union]
        \\ fs[]
        \\ CCONTR_TAC \\ fs[] \\ rveq
        \\ first_x_assum (qspec_then `n` assume_tac)
        \\ res_tac)
    \\ TOP_CASE_TAC \\ fs[]
    \\ qpat_x_assum `eval_expr E2 _ e nF _` kall_tac
    \\ drule FPRangeValidator_sound
    \\ rpt (disch_then drule)
    \\ disch_then irule \\ fs[]
    \\ fs[DIFF_DEF, domain_insert, SUBSET_DEF]
    \\ rpt strip_tac \\ first_x_assum irule
    \\ simp[Once freeVars_def]
    \\ once_rewrite_tac [domain_union]
    \\ fs[]
    \\ CCONTR_TAC \\ fs[] \\ rveq
    \\ first_x_assum (qspec_then `n` assume_tac)
    \\ res_tac)
  \\ fs[])
  \\ qpat_x_assum ‘validErrorboundCmd _ _ _ _’
                  (assume_tac o SIMP_RULE std_ss [Once validErrorboundCmd_def]) \\ fs[]
  \\ rpt (inversion `bstep (Ret _) _ _ _ _` bstep_cases)
  \\ drule FPRangeValidator_sound
  \\ rpt (disch_then drule)
  \\ fs[Once validTypesCmd_def, Once validRangesCmd_def]
QED

val _ = export_theory();
