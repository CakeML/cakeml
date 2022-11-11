(**
    Interval arithmetic checker and its soundness proof.
    The function validIntervalbounds checks wether the given analysis result is
    a valid range arithmetic for each sub term of the given exprression e.
    The computation is done using our formalized interval arithmetic.
    The function is used in CertificateChecker.v to build the full checker.
**)
open simpLib realTheory realLib RealArith pred_setTheory sptreeTheory
     sptreeLib;
open AbbrevsTheory ExpressionsTheory RealSimpsTheory FloverTactics
     ExpressionAbbrevsTheory IntervalArithTheory CommandsTheory ssaPrgsTheory
     MachineTypeTheory FloverMapTheory TypeValidatorTheory RealRangeArithTheory
     ExpressionSemanticsTheory sqrtApproxTheory;
open preambleFloVer;

val _ = new_theory "IntervalValidation";

val _ = temp_delsimps ["RMUL_LEQNORM"]

val _ = Parse.hide "delta"; (* so that it can be used as a variable *)

Overload abs[local] = “realax$abs”
Overload max[local] = “realax$max”
Overload min[local] = “realax$min”

(** Define a global iteration count for square roots **)
Definition ITERCOUNT_def:
  (ITERCOUNT:num) = 4
End

Definition validIntervalbounds_def:
  validIntervalbounds f (absenv:analysisResult) (P:precond) (validVars:num_set) =
  case (FloverMapTree_find f absenv) of
  | SOME (intv, _) =>
    (case f of
     | Var v =>
       if (lookup v validVars = SOME ())
       then T
       else (isSupersetInterval (P v) intv /\ IVlo (P v) <= IVhi (P v))
     | Const m n => isSupersetInterval (n,n) intv
     | Unop op f1 =>
       (case (FloverMapTree_find f1 absenv) of
        | SOME (iv, _) =>
            (if validIntervalbounds f1 absenv P validVars then
              case op of
              | Neg =>
                  let new_iv = negateInterval iv in
                    isSupersetInterval new_iv intv
              | Inv =>
                  if IVhi iv < 0 \/ 0 < IVlo iv then
                    let new_iv = invertInterval iv in
                      isSupersetInterval new_iv intv
                  else F
              (* Sqrt is transcendental -> We cannot directly compute it
                 thus we do a newton approximation of the lower and upper bounds *)
              | Sqrt =>
                  if 0 < IVlo iv then
                    let sqrtLo = newton ITERCOUNT (IVlo iv * 0.99) (IVlo iv * 0.99);
                        sqrtHi = newton ITERCOUNT (IVhi iv * 1.01) (IVhi iv * 1.01);
                        new_iv = (sqrtLo, sqrtHi)
                    in
                      if (validate_newton_down sqrtLo (IVlo iv) ∧
                          validate_newton_up sqrtHi (IVhi iv)) then
                      isSupersetInterval new_iv intv
                      else F
                  else F
             else F)
        | _ => F)
     | Downcast m f1 =>
       (case (FloverMapTree_find f1 absenv) of
        | SOME (iv1, _) =>
            (if (validIntervalbounds f1 absenv P validVars) then
               ((isSupersetInterval intv iv1) /\ (isSupersetInterval iv1 intv))
             else F)
        | _ => F)
     | Binop op f1 f2 =>
       (if (validIntervalbounds f1 absenv P validVars /\
            validIntervalbounds f2 absenv P validVars) then
          (case (FloverMapTree_find f1 absenv, FloverMapTree_find f2 absenv) of
           | (SOME (iv1, _), SOME (iv2, _)) =>
             (case op of
              | Plus =>
                  let new_iv = addInterval iv1 iv2 in
                    isSupersetInterval new_iv intv
              | Sub =>
                  let new_iv = subtractInterval iv1 iv2 in
                    isSupersetInterval new_iv intv
              | Mult =>
                  let new_iv = multInterval iv1 iv2 in
                    isSupersetInterval new_iv intv
              | Div =>
                  if (IVhi iv2 < 0 \/ 0 < IVlo iv2) then
                    let new_iv = divideInterval iv1 iv2 in
                      isSupersetInterval new_iv intv
                  else F)
           | _ => F)
        else F)
     | Fma f1 f2 f3 =>
       (if (validIntervalbounds f1 absenv P validVars /\
            validIntervalbounds f2 absenv P validVars /\
            validIntervalbounds f3 absenv P validVars) then
          case FloverMapTree_find f1 absenv, FloverMapTree_find f2 absenv,
               FloverMapTree_find f3 absenv of
          | SOME (iv1, _), SOME (iv2, _), SOME (iv3, _) =>
            let new_iv = addInterval (multInterval iv1 iv2) iv3 in
              isSupersetInterval new_iv intv
          | _, _, _ => F
        else F))
  | _ => F
End

Theorem validIntervalbounds_eq =
  SIMP_CONV flover_ss [Once validIntervalbounds_def] (Parse.Term ‘validIntervalbounds e A P v’)

Definition validIntervalboundsCmd_def:
  validIntervalboundsCmd (f:real cmd) (absenv:analysisResult) (P:precond) (validVars:num_set) =
    case f of
     | Let m x e g =>
       (case (FloverMapTree_find e absenv, FloverMapTree_find (Var x) absenv) of
          | SOME (iv_e,_), SOME (iv_x, _) =>
              if (validIntervalbounds e absenv P validVars /\ (iv_e = iv_x))
              then validIntervalboundsCmd g absenv P (insert x () validVars)
              else F
          |_,_ => F)
   | Ret e =>
     (validIntervalbounds e absenv P validVars)
End

Theorem validIntervalboundsCmd_eq =
  SIMP_CONV flover_ss [Once validIntervalboundsCmd_def] (Parse.Term ‘validIntervalboundsCmd f A P v’)

Theorem cond_simpl:
  ∀ a b. (if a then T else b) <=> (a \/ (~ a /\ b))
Proof
  rpt strip_tac \\ metis_tac[]
QED

val real_prove =
  rpt (qpat_x_assum `!x. _` kall_tac)
  \\ rpt (qpat_x_assum `_ ==> ! x. _` kall_tac)
  \\ REAL_ASM_ARITH_TAC;

Theorem newton_method_pos:
  ∀ x m.
    0 ≤ m ∧
    0 ≤ x ⇒ 0 ≤ newton n x m
Proof
  Induct_on ‘n’ >> gs[newton_def]
  >> rpt strip_tac
  >> first_x_assum irule >> rewrite_tac[real_div] >> gs[]
  >> irule REAL_LE_MUL >> gs[]
  >> irule REAL_LE_ADD >> gs[]
  >> irule REAL_LE_MUL >> gs[]
QED

Theorem newton_method_lt_pos:
  ∀ x m.
    0 < m ∧
    0 < x ⇒ 0 < newton n m x
Proof
  Induct_on ‘n’ >> gs[newton_def]
  >> rpt strip_tac
  >> first_x_assum irule >> rewrite_tac[real_div] >> gs[]
  >> irule REAL_LT_ADD >> gs[]
  >> irule REAL_LT_MUL >> gs[nonzerop_def]
  >> COND_CASES_TAC >> gs[]
QED

Theorem validIntervalbounds_sound:
  ∀ (f:real expr) (A:analysisResult) (P:precond) (fVars:num_set)
   (dVars:num_set) E Gamma.
     validIntervalbounds f A P dVars /\ (* The checker succeeded *)
     (* All defined vars have already been analyzed *)
     dVars_range_valid dVars E A /\
     (((domain (usedVars f)) DIFF (domain dVars)) SUBSET (domain fVars)) /\
     fVars_P_sound fVars E P /\
     validTypes f Gamma ==>
     validRanges f A E (toRTMap (toRExpMap Gamma))
Proof
  Induct_on `f` \\ rpt strip_tac
  \\ qpat_x_assum ‘domain (usedVars _) DIFF _ SUBSET _’
                  (assume_tac o (SIMP_RULE flover_ss [Once usedVars_def]))
  \\ qpat_x_assum ‘validIntervalbounds _ _ _ _’
                  (assume_tac o (ONCE_REWRITE_RULE [validIntervalbounds_eq]))
  \\ fs[]
  (* Defined variable case *)
  >- (rw_thm_asm `dVars_range_valid _ _ _` dVars_range_valid_def
      \\ specialize `!v. v IN domain dVars ==> _` `n`
      \\ first_x_assum destruct
      >- (fs [domain_lookup])
      \\ fs[validRanges_def]
      \\ qexists_tac `vR` \\ fs[] \\ rveq \\ fs[toREval_def]
      \\ irule Var_load \\ TRY (fs[])
      \\ fs[toRExpMap_def, toRTMap_def, domain_lookup, validTypes_def])
  (* Free variable case *)
  >- (rw_thm_asm `fVars_P_sound _ _ _` fVars_P_sound_def
      \\ specialize `!v. v IN domain fVars ==> _` `n`
      \\ `lookup n dVars = NONE` by (Cases_on `lookup n dVars` \\ fs [])
      \\ first_x_assum destruct
      >- (fs[usedVars_def, lookup_NONE_domain])
      \\ simp[validRanges_def]
      \\ qexists_tac `vR`
      \\ fs [isSupersetInterval_def, toREval_def]
      \\ rpt conj_tac
      >- (irule Var_load \\ TRY (fs[])
          \\ fs[toRExpMap_def, toRTMap_def, domain_lookup, validTypes_def])
      \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ fs[] \\ rveq \\ fs[])
  (* Const case *)
  >- (simp[validRanges_def]
      \\ qexists_tac `v` \\ fs[toREval_def, isSupersetInterval_def]
      \\ irule Const_dist' \\ fs[perturb_def, mTypeToR_def])
  (* Unary operator case *)
  >- (rw_thm_asm `validTypes _ _` validTypes_def
      \\ first_x_assum
          (qspecl_then [`A`, `P`, `fVars`, `dVars`, `E`, `Gamma`] destruct)
      \\ fs[] \\ rveq
      \\ IMP_RES_TAC validRanges_single
      \\ simp[Once validRanges_def] \\ Cases_on `u` \\ simp[]
      (* Negation case *)
      >- (qexists_tac `- vR` \\ fs[negateInterval_def, isSupersetInterval_def]
          \\ rveq \\ Cases_on `iv` \\ fs[]
          \\ rpt conj_tac \\ fs[toREval_def] \\ TRY real_prove
          \\ irule Unop_neg' \\ qexistsl_tac [`REAL`, `REAL`, `vR`]
          \\ fs[evalUnop_def, isCompat_def, toRTMap_def])
      (* Inversion case *)
      >- (
        qexists_tac `1 / vR`
        \\ conj_tac
        >- (
         simp[toREval_def]
         \\ irule Unop_inv' \\ gs[] \\ qexistsl_tac [`0`, `REAL`, `vR`]
         \\ simp[evalUnop_def, mTypeToR_def, perturb_def, REAL_INV_1OVER,
                 mTypeToR_pos, isCompat_def, toRTMap_def]
         \\ CCONTR_TAC \\ fs[] \\ rveq
         \\ `0 < 0:real` by (real_prove)
         \\ fs[])
        \\ conj_tac
        \\ fs[invertInterval_def, isSupersetInterval_def] \\ rveq
        \\ Cases_on `iv` \\ fs[]
        >- (irule REAL_LE_TRANS \\ qexists_tac `1 / r` \\ conj_tac \\ fs[]
            \\ fs[GSYM REAL_INV_1OVER] \\ irule REAL_INV_LE_ANTIMONO_IMPL \\ fs[]
            \\ real_prove)
        >- (irule REAL_LE_TRANS \\ qexists_tac `1 / r` \\ conj_tac \\ fs[]
            \\ fs[GSYM REAL_INV_1OVER] \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[]
            \\ real_prove)
        >- (irule REAL_LE_TRANS \\ qexists_tac `1 / q` \\ conj_tac \\ fs[]
            \\ fs[GSYM REAL_INV_1OVER] \\ irule REAL_INV_LE_ANTIMONO_IMPL \\ fs[]
            \\ real_prove)
        \\ irule REAL_LE_TRANS \\ qexists_tac `1/q` \\ conj_tac \\ fs[]
        \\ fs[GSYM REAL_INV_1OVER] \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ fs[]
        \\ real_prove)
      (* Sqrt case *)
      \\ conj_tac >- gs[]
      \\ qexists_tac `sqrt vR`
      \\ conj_tac
      >- (
        simp[toREval_def]
        \\ irule Unop_sqrt' \\ gs[] \\ qexistsl_tac [`0`, `REAL`, `vR`]
        \\ simp[evalUnop_def, mTypeToR_def, perturb_def, REAL_INV_1OVER,
                 mTypeToR_pos, isCompat_def, toRTMap_def]
        \\ CCONTR_TAC \\ fs[] \\ rveq
        \\ `0 < 0:real` by (real_prove)
        \\ fs[])
      \\ gs[] \\ rveq
      \\ qpat_x_assum `validate_newton_down _ _` $ mp_then Any mp_tac validate_newton_lb_valid
      \\ impl_tac
      >- (conj_tac
          >- (irule newton_method_pos \\ conj_tac \\ irule REAL_LE_MUL \\ gs[] \\ real_prove)
          \\ real_prove)
      \\ strip_tac
      \\ ‘0 < SND iv ’
         by (
           irule REAL_LTE_TRANS \\ qexists_tac ‘FST iv’ \\ gs[]
           \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[])
      \\ qpat_x_assum `validate_newton_up _ _` $ mp_then Any mp_tac validate_newton_ub_valid
      \\ impl_tac
      >- (conj_tac
          >- (irule newton_method_pos \\ conj_tac \\ irule REAL_LE_MUL \\ gs[] \\ real_prove)
          \\ real_prove)
      \\ strip_tac
      \\ conj_tac
      \\ fs[isSupersetInterval_def] \\ rveq
      >- (
         irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[]
         \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[]
         \\ irule SQRT_MONO_LE \\ real_prove)
      \\ irule REAL_LE_TRANS \\ qexists_tac ‘sqrt (SND iv)’ \\ conj_tac
      >- (
        irule SQRT_MONO_LE \\ gs[]
        \\ irule REAL_LE_TRANS \\ qexists_tac ‘FST iv’ \\ real_prove)
      \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[])
  (* Binary operator case *)
  >- (rename1 `Binop b f1 f2` \\ simp[Once validRanges_def, toREval_def]
      \\ rw_thm_asm `validTypes _ _` validTypes_def \\ fs[]
      \\ rpt (
           first_x_assum
               (qspecl_then [`A`, `P`, `fVars`, `dVars`, `E`, `Gamma`] destruct)
               \\ fs[domain_union, UNION_DEF, DIFF_DEF, SUBSET_DEF])
      \\ rveq
      \\ IMP_RES_TAC validRanges_single
      \\ rename1 `eval_expr E _ (toREval f1) vR1 REAL`
      \\ rename1 `eval_expr E _ (toREval f2) vR2 REAL`
      \\ conj_tac >- (rpt strip_tac \\ fs[])
      \\ qexists_tac `evalBinop b vR1 vR2`
      \\ conj_tac
      >- (irule Binop_dist' \\ fs[mTypeToR_def]
          \\ qexistsl_tac [`REAL`, `REAL`, `vR1`, `vR2`]
          \\ fs[isJoin_def, isFixedPoint_def, join_fl_def, mTypeToR_pos,
                perturb_def, toRTMap_def]
          \\ strip_tac \\ rveq \\ fs[]
          \\ CCONTR_TAC \\ fs[] \\ rveq
          \\ `0 < 0:real` by (real_prove)
          \\ fs[])
      \\ fs[] \\ rveq
      \\ rename1 `FloverMapTree_find f1 A = SOME (iv1, err1)`
      \\ rename1 `FloverMapTree_find f2 A = SOME (iv2, err2)`
      \\ Cases_on `b` \\ simp[evalBinop_def]
     (* Plus case *)
     >- (fs[evalBinop_def, isSupersetInterval_def, absIntvUpd_def,
            addInterval_def]
         \\ qspecl_then [`iv1`, `iv2`, `vR1`, `vR2`]
              assume_tac
              (REWRITE_RULE
                   [validIntervalAdd_def,
                    addInterval_def,
                    absIntvUpd_def,
                    contained_def] interval_addition_valid)
         \\ fs[] \\ res_tac
         \\ real_prove)
     (* Sub case *)
     >- (fs[evalBinop_def, isSupersetInterval_def, absIntvUpd_def,
            subtractInterval_def, addInterval_def, negateInterval_def]
         \\ qspecl_then [`iv1`, `iv2`, `vR1`, `vR2`]
              assume_tac
              (REWRITE_RULE
                   [validIntervalSub_def,
                    subtractInterval_def,
                    addInterval_def,
                    negateInterval_def,
                    absIntvUpd_def,
                    contained_def] interval_subtraction_valid)
         \\ fs[] \\ real_prove)
     (* Mult case *)
     >- (fs[evalBinop_def, isSupersetInterval_def, absIntvUpd_def,
            multInterval_def]
         \\ qspecl_then [`iv1`, `iv2`, `vR1`, `vR2`]
            assume_tac
            (REWRITE_RULE
                 [validIntervalAdd_def,
                  multInterval_def,
                  absIntvUpd_def,
                  contained_def] interval_multiplication_valid)
         \\ fs[] \\ real_prove)
     (* Div case *)
     \\ fs[evalBinop_def, isSupersetInterval_def, absIntvUpd_def,
           divideInterval_def, multInterval_def, invertInterval_def,
           GSYM REAL_INV_1OVER]
     \\ qspecl_then [`iv1`, `iv2`, `vR1`, `vR2`]
          assume_tac
          (REWRITE_RULE
               [validIntervalSub_def, divideInterval_def,
                multInterval_def, invertInterval_def,
                absIntvUpd_def, contained_def,
                GSYM REAL_INV_1OVER]
               interval_division_valid)
     \\ fs[] \\ real_prove)
  (* FMA case *)
  >- (rename1 `Fma f1 f2 f3`
      \\ rw_thm_asm `validTypes _ _` validTypes_def \\ fs[]
      \\ rpt (
           first_x_assum
               (qspecl_then [`A`, `P`, `fVars`, `dVars`, `E`, `Gamma`] destruct)
               \\ fs[domain_union, UNION_DEF, DIFF_DEF, SUBSET_DEF])
      \\ IMP_RES_TAC validRanges_single
      \\ rename1 `eval_expr E _ (toREval f1) vR1 REAL`
      \\ rename1 `eval_expr E _ (toREval f2) vR2 REAL`
      \\ rename1 `eval_expr E _ (toREval f3) vR3 REAL`
      \\ simp[Once validRanges_def, toREval_def]
      \\ qexists_tac `evalFma vR1 vR2 vR3`
      \\ conj_tac
      >- (irule Fma_dist'
          \\ qexistsl_tac [`0:real`, `REAL`, `REAL`, `REAL`, `REAL`, `vR1`, `vR2`, `vR3`]
          \\ fs [mTypeToR_def, perturb_def, evalFma_def, evalBinop_def,
                 toRTMap_def, isJoin3_def, join_fl3_def, join_fl_def,
                 isFixedPoint_def])
      \\ fs[] \\ rveq
      \\ rename1 `FloverMapTree_find f1 A = SOME (iv_f1, err1)`
      \\ rename1 `FloverMapTree_find f2 A = SOME (iv_f2, err2)`
      \\ rename1 `FloverMapTree_find f3 A = SOME (iv_f3, err3)`
      \\ qspecl_then [`iv_f1`, `iv_f2`, `vR1`, `vR2`]
           destruct
         (REWRITE_RULE
              [validIntervalAdd_def,
               multInterval_def,
               absIntvUpd_def,
               contained_def] interval_multiplication_valid)
      \\ fs[]
      \\ qspecl_then [`multInterval iv_f1 iv_f2`, `iv_f3`, `vR1 * vR2`, `vR3`]
           destruct
          (REWRITE_RULE
              [validIntervalAdd_def,
                  addInterval_def,
                  multInterval_def,
                  absIntvUpd_def,
                  contained_def] interval_addition_valid)
      \\ fs[multInterval_def, absIntvUpd_def, isSupersetInterval_def,
            addInterval_def, multInterval_def, absIntvUpd_def, evalFma_def,
            evalBinop_def]
      \\ real_prove)
  (* Downcast case *)
  >- (rw_thm_asm `validTypes _ _` validTypes_def
      \\ fs[]
      \\ first_x_assum
          (qspecl_then [`A`, `P`, `fVars`, `dVars`, `E`, `Gamma`] destruct)
      \\ fs[] \\ rveq
      \\ simp[Once validRanges_def]
      \\ IMP_RES_TAC validRanges_single
      \\ fs[] \\ rveq
      \\ qexists_tac `vR`
      \\ fs[Downcast_dist', toREval_def, isSupersetInterval_def]
      \\ `FST iv = FST intv` by (metis_tac [REAL_LE_ANTISYM])
      \\ `SND iv = SND intv` by (metis_tac [REAL_LE_ANTISYM])
      \\ fs[])
QED

Theorem validIntervalboundsCmd_sound:
  ∀ f A E fVars dVars outVars P Gamma.
    ssa f (union fVars dVars) outVars /\
    dVars_range_valid dVars E A /\
    fVars_P_sound fVars E P /\
    (((domain (freeVars f)) DIFF (domain dVars)) SUBSET (domain fVars)) /\
    validIntervalboundsCmd f A P dVars /\
    validTypesCmd f Gamma ==>
    validRangesCmd f A E (toRTMap (toRExpMap Gamma))
Proof
  Induct_on `f` \\ simp[Once validIntervalboundsCmd_eq]
  \\ once_rewrite_tac [toREvalCmd_def, getRetExp_def, validTypesCmd_def]
  \\ rpt strip_tac
  >- (
    inversion `ssa _ _ _` ssa_cases \\ rveq
    \\ drule validIntervalbounds_sound
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [`fVars`, `Gamma`] destruct)
    >- (
      fs [SUBSET_DEF, domain_union]
      \\ rpt strip_tac \\ res_tac)
    \\ imp_res_tac validRanges_single
    \\ rename1 `FloverMapTree_find e A = SOME (iv_e, err_e)`
    \\ first_x_assum
       (qspecl_then [`A`, `updEnv n vR E`, `fVars`, `insert n () dVars`,
                     `outVars`, `P`, `Gamma`]
        destruct)
    >- (
      fs [domain_insert]
      \\ rpt conj_tac
      >- (
        irule ssa_equal_set
        \\ qexists_tac `(insert n () (union fVars dVars))`
        \\ fs [domain_union,  domain_insert]
        \\ once_rewrite_tac [UNION_COMM]
        \\ fs [INSERT_UNION_EQ, UNION_COMM])
      >- (
        fs[dVars_range_valid_def]
        \\ rpt strip_tac \\ fs[updEnv_def]
        >- (rveq \\ fs[])
        \\ rename1 `v2 IN domain dVars`
        \\ Cases_on `v2 = n` \\ fs[]
        \\ rveq \\ fs [domain_union])
      >- (
        fs[fVars_P_sound_def]
        \\ rpt strip_tac \\ fs[updEnv_def]
        \\ rename1 `v2 IN domain fVars`
        \\ Cases_on `v2 = n` \\ rveq \\ fs[domain_union])
      \\ fs [domain_insert, SUBSET_DEF]
      \\ rpt strip_tac
      \\ first_x_assum match_mp_tac
      \\ once_rewrite_tac [freeVars_def, domain_union]
      \\ fs [domain_union])
    \\ simp[Once validRangesCmd_def]
    \\ conj_tac
    >- (
      rpt strip_tac
      \\ `vR = vR'` by (metis_tac [meps_0_deterministic])
      \\ rveq \\ fs[])
    \\ imp_res_tac validRangesCmd_single
    \\ fs[getRetExp_def]
    \\ find_exists_tac \\ simp[Once toREvalCmd_def]
    \\ irule let_b \\ fs[toRTMap_def, toRExpMap_def] \\ find_exists_tac \\ fs[])
  \\ inversion `ssa _ _ _` ssa_cases
  \\ drule validIntervalbounds_sound
  \\ rpt (disch_then drule)
  \\ disch_then (qspecl_then [`fVars`, `Gamma`] destruct)
  >- (fs [freeVars_def])
  \\ simp[Once validRangesCmd_def]
  \\ IMP_RES_TAC validRanges_single
  \\ simp[Once getRetExp_def, Once toREvalCmd_def]
  \\ fs[] \\ find_exists_tac \\ fs[ret_b]
QED

Theorem validIntervalbounds_validates_iv:
  !(f:real expr) (A:analysisResult) (P:precond) (dVars:num_set).
    (!v. v IN domain dVars ==>
         ? iv err. FloverMapTree_find (Var v) A = SOME (iv,err) /\
         valid iv) /\
    validIntervalbounds f A P dVars ==>
    ? iv err.
    FloverMapTree_find f A = SOME (iv, err) /\
    valid iv
Proof
  Induct_on `f` \\ simp[Once validIntervalbounds_eq]
  \\ rpt strip_tac
  >- (first_x_assum (qspecl_then [`n`] destruct)
      \\ fs[domain_lookup, valid_def, isSupersetInterval_def, validIntervalbounds_def]
      \\ rveq \\ fs[])
  >- (fs[isSupersetInterval_def, valid_def, validIntervalbounds_def]
      \\ irule REAL_LE_TRANS
      \\ asm_exists_tac \\ conj_tac \\ fs[IVlo_def, IVhi_def]
      \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ fs[])
  >- (fs[isSupersetInterval_def, valid_def, IVlo_def, IVhi_def]
      \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ fs[])
  >- (first_x_assum (qspecl_then [`A`, `P`, `dVars`] destruct)
      \\ fs[]
      \\ rveq \\ Cases_on `u`
      >- (`valid (negateInterval iv)`
            by (irule iv_neg_preserves_valid \\ fs[])
          \\ fs[valid_def, isSupersetInterval_def]
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs[]
          \\ irule REAL_LE_TRANS
          \\ find_exists_tac \\ fs[])
      >- (`valid (invertInterval iv)`
            by (irule iv_inv_preserves_valid \\ fs[])
          \\ fs[valid_def, isSupersetInterval_def]
          >- (irule REAL_LE_TRANS
              \\ asm_exists_tac \\ fs[]
              \\ irule REAL_LE_TRANS
              \\ find_exists_tac \\ fs[invertInterval_def])
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs[]
          \\ irule REAL_LE_TRANS
          \\ find_exists_tac \\ fs[invertInterval_def])
      \\ gs[valid_def, isSupersetInterval_def]
      \\ irule REAL_LE_TRANS
      \\ asm_exists_tac \\ gs[]
      \\ irule REAL_LE_TRANS \\ once_rewrite_tac [CONJ_COMM]
      \\ asm_exists_tac \\ gs[]
      \\ qpat_x_assum `validate_newton_down _ _` $ mp_then Any mp_tac validate_newton_lb_valid
      \\ impl_tac
      >- (conj_tac
          >- (irule newton_method_pos \\ conj_tac \\ irule REAL_LE_MUL \\ gs[] \\ real_prove)
          \\ real_prove)
      \\ strip_tac
      \\ ‘0 < SND iv ’
         by (irule REAL_LTE_TRANS \\ qexists_tac ‘FST iv’ \\ gs[])
      \\ qpat_x_assum `validate_newton_up _ _` $ mp_then Any mp_tac validate_newton_ub_valid
      \\ impl_tac
      >- (conj_tac
          >- (irule newton_method_pos \\ conj_tac \\ irule REAL_LE_MUL \\ gs[] \\ real_prove)
          \\ real_prove)
      \\ strip_tac
      \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[]
      \\ irule REAL_LE_TRANS \\ qexists_tac ‘sqrt(SND iv)’\\ gs[]
      \\ irule SQRT_MONO_LE \\ real_prove)
  >- (rename1 `Binop b f1 f2`
      \\ rpt (first_x_assum (qspecl_then [`A`, `P`, `dVars`] destruct) \\ fs[])
      \\ rveq \\ fs[]
      \\ rename1 `FloverMapTree_find f1 A = SOME (iv_f1, err_f1)`
      \\ rename1 `FloverMapTree_find f2 A = SOME (iv_f2, err_f2)`
      \\ fs[]
      \\ Cases_on `b`
      >- (`valid (addInterval iv_f1 iv_f2)`
            by (irule iv_add_preserves_valid \\ fs[])
          \\ fs[valid_def, isSupersetInterval_def]
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs []
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs [])
      >- (`valid (subtractInterval iv_f1 iv_f2)`
            by (irule iv_sub_preserves_valid \\ fs[])
          \\ fs[valid_def, isSupersetInterval_def]
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs []
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs [])
      >- (`valid (multInterval iv_f1 iv_f2)`
            by (irule iv_mult_preserves_valid \\ fs[])
          \\ fs[valid_def, isSupersetInterval_def]
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs []
          \\ irule REAL_LE_TRANS
          \\ asm_exists_tac \\ fs [])
      >- (`valid (divideInterval iv_f1 iv_f2)`
            by (match_mp_tac iv_div_preserves_valid \\ fs[])
          \\ fs[valid_def, isSupersetInterval_def]
          \\ match_mp_tac REAL_LE_TRANS
          \\ asm_exists_tac \\ fs []
          \\ match_mp_tac REAL_LE_TRANS
          \\ asm_exists_tac \\ fs []))
  >- (rename1 `Fma f1 f2 f3`
      \\ rpt (first_x_assum (qspecl_then [`A`, `P`, `dVars`] destruct) \\ fs[])
      \\ rveq \\ fs[]
      \\ rename1 `FloverMapTree_find f1 A = SOME (iv_f1, err_f1)`
      \\ rename1 `FloverMapTree_find f2 A = SOME (iv_f2, err_f2)`
      \\ rename1 `FloverMapTree_find f3 A = SOME (iv_f3, err_f3)`
      \\ fs[]
      \\ `valid (addInterval (multInterval iv_f1 iv_f2) iv_f3)`
            by (irule iv_add_preserves_valid \\ fs[]
                \\ irule iv_mult_preserves_valid \\ fs[])
      \\ fs[valid_def, isSupersetInterval_def]
      \\ irule REAL_LE_TRANS
      \\ asm_exists_tac \\ fs []
      \\ irule REAL_LE_TRANS
      \\ asm_exists_tac \\ fs [])
 >- (first_x_assum (qspecl_then [`A`, `P`, `dVars`] destruct) \\ fs[]
      \\ fs[isSupersetInterval_def, IVlo_def, IVhi_def]
      \\ rveq
      \\ `FST iv = FST intv` by (metis_tac[REAL_LE_ANTISYM])
      \\ `SND iv = SND intv` by (metis_tac[REAL_LE_ANTISYM])
      \\ fs[valid_def, IVlo_def, IVhi_def])
QED

Theorem validIntervalbounds_noDivzero_real:
  !(f1 f2:real expr) A (P:precond) (dVars:num_set).
      validIntervalbounds (Binop Div f1 f2) A P dVars ==>
      ?iv err.
      FloverMapTree_find f2 A = SOME (iv,err) /\
      noDivzero (SND iv) (FST iv)
Proof
  rpt strip_tac \\ fs[Once validIntervalbounds_eq]
  \\ fs[noDivzero_def, IVhi_def, IVlo_def]
QED

Theorem validRanges_validates_iv:
  ! e Gamma E A.
    validRanges e A E Gamma ==>
      ? iv err.
        FloverMapTree_find e A = SOME (iv, err) /\
        valid iv
Proof
  Induct_on `e` \\ simp[Once validRanges_def]
  \\ rpt strip_tac
  \\ fs[valid_def] \\ real_prove
QED

val _ = export_theory();
