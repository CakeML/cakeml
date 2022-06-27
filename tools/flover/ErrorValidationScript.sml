(**
   This file contains the HOL4 implementation of the error bound validator as well
   as its soundness proof. The function validErrorbound is the Error bound
   validator from the certificate checking process. Under the assumption that a
   valid range arithmetic result has been computed, it can validate error bounds
   encoded in the analysis result. The validator is used in the file
   CertificateChecker.v to build the complete checker.
 **)
open simpLib realTheory realLib RealArith pred_setTheory;
open AbbrevsTheory ExpressionsTheory ExpressionSemanticsTheory RealSimpsTheory
     RealRangeArithTheory FloverTactics MachineTypeTheory
     ExpressionAbbrevsTheory ErrorBoundsTheory IntervalArithTheory
     TypeValidatorTheory IntervalValidationTheory EnvironmentsTheory
     CommandsTheory ssaPrgsTheory FloverMapTheory sqrtApproxTheory;
open preambleFloVer;

val _ = new_theory "ErrorValidation";

val _ = Parse.hide "delta"; (* so that it can be used as a variable *)

Overload abs[local] = “realax$abs”

val _ = realLib.prefer_real();

val triangle_tac =
  irule triangle_trans \\ fs[REAL_ABS_TRIANGLE];

fun real_rewrite t =
  rewrite_tac [REAL_ARITH (Parse.Term t)];

val real_prove =
  rpt (qpat_x_assum `!x. _` kall_tac)
  \\ rpt (qpat_x_assum `_ ==> ! x. _` kall_tac)
  \\ REAL_ASM_ARITH_TAC;

Definition validErrorbound_def:
  validErrorbound e (typeMap: typeMap) (A:analysisResult) (dVars:num_set)=
    case FloverMapTree_find e A, FloverMapTree_find e typeMap of
    | NONE, _ => F
    | _, NONE => F
    | SOME (intv, err), SOME m =>
      (if (0 <= err) then
        case e of
        | Var v =>
          if (lookup v dVars = SOME ()) then T
          else computeError (maxAbs intv) m <= err
        | Const _ n => (computeError (maxAbs intv) m <= err)
        | Unop Neg e1 =>
          if (validErrorbound e1 typeMap A dVars) then
            case (FloverMapTree_find e1 A) of
            | SOME (_, err1) =>  err = err1
            | _ => F
          else F
        | Unop Sqrt e1 =>
          if (validErrorbound e1 typeMap A dVars) then
            case (FloverMapTree_find e1 A) of
            | SOME (iv1, err1) =>
                let errIve1 = widenInterval iv1 err1;
                    sqrtRealLo = newton ITERCOUNT (IVlo iv1 * 0.99) (IVlo iv1 * 0.99);
                    sqrtRealHi = newton ITERCOUNT (IVhi iv1 * 1.01) (IVhi iv1 * 1.01);
                    sqrtRealIv = (sqrtRealLo, sqrtRealHi);
                    sqrtFinLo= newton ITERCOUNT (IVlo errIve1 * 0.99) (IVlo errIve1 * 0.99);
                    sqrtFinHi = newton ITERCOUNT (IVhi errIve1 * 1.01) (IVhi errIve1 * 1.01);
                    sqrtFinIv = (sqrtFinLo, sqrtFinHi);
                    propError = err1 * sqrtFinHi * inv ((IVlo iv1 - err1) * 2);
                    mAbs = maxAbs sqrtFinIv
                in
                  if (validate_newton_down sqrtRealLo (IVlo iv1) ∧
                      validate_newton_up sqrtRealHi (IVhi iv1) ∧
                      validate_newton_down sqrtFinLo (IVlo errIve1) ∧
                      validate_newton_up sqrtFinHi (IVhi errIve1) ∧
                      0 < IVlo errIve1) then
                    propError + computeError mAbs m <= err
                  else F
            | _ => F
          else F
        | Unop Inv e1 => F
        | Binop op e1 e2 =>
          (if (validErrorbound e1 typeMap A dVars /\ validErrorbound e2 typeMap A dVars)
           then
             case FloverMapTree_find e1 A, FloverMapTree_find e2 A of
             | NONE, _ => F
             | _, NONE => F
             | SOME (ive1, err1), SOME (ive2, err2) =>
               let errIve1 = widenInterval ive1 err1 in
               let errIve2 = widenInterval ive2 err2 in
               let upperBoundE1 = maxAbs ive1 in
               let upperBoundE2 = maxAbs ive2 in
                (case op of
                 | Plus =>
                   let mAbs = maxAbs (addInterval errIve1 errIve2) in
                     err1 + err2 + computeError mAbs m <= err
                 | Sub =>
                   let mAbs = maxAbs (subtractInterval errIve1 errIve2) in
                     err1 + err2 + computeError mAbs m <= err
                 | Mult =>
                   let mAbs = maxAbs (multInterval errIve1 errIve2);
                       eProp = upperBoundE1 * err2 + upperBoundE2 * err1 + err1 * err2 in
                     eProp + computeError mAbs m <= err
                 | Div =>
                   (if (noDivzero (IVhi errIve2) (IVlo errIve2))
                     then
                       let upperBoundInvE2 = maxAbs (invertInterval ive2);
                           minAbsIve2 = minAbsFun (errIve2);
                           errInv = (1 / (minAbsIve2 * minAbsIve2)) * err2;
                           mAbs = maxAbs (divideInterval errIve1 errIve2);
                           eProp = upperBoundE1 * errInv + upperBoundInvE2 * err1 + err1 * errInv in
                        eProp + computeError mAbs m <= err
                   else F))
              else F)
        | Fma e1 e2 e3 =>
          (if (validErrorbound e1 typeMap A dVars /\
                validErrorbound e2 typeMap A dVars /\
                validErrorbound e3 typeMap A dVars) then
              case (FloverMapTree_find e1 A,
                    FloverMapTree_find e2 A,
                    FloverMapTree_find e3 A) of
                | SOME (ive1, err1), SOME (ive2, err2), SOME (ive3, err3) =>
                  let errIve1 = widenInterval ive1 err1;
                      errIve2 = widenInterval ive2 err2;
                      errIve3 = widenInterval ive3 err3;
                      upperBoundE1 = maxAbs ive1;
                      upperBoundE2 = maxAbs ive2;
                      upperBoundE3 = maxAbs ive3;
                      errIntv_prod = multInterval errIve1 errIve2;
                      mult_error_bound = (upperBoundE1 * err2 + upperBoundE2 * err1 + err1 * err2);
                      mAbs = maxAbs (addInterval errIntv_prod errIve3 ) in
                   mult_error_bound + err3 + computeError mAbs m <= err
                  |_, _, _ => F
            else F)
        | Downcast m1 e1 =>
          if (validErrorbound e1 typeMap A dVars)
          then
            case FloverMapTree_find e1 A of
              | NONE => F
              | SOME (ive1, err1) =>
                let errIve1 = widenInterval ive1 err1;
                    mAbs = maxAbs errIve1 in
                err1 + computeError mAbs m1 <= err
           else F
       else F)
End

Theorem validErrorbound_eq =
  SIMP_CONV flover_ss [Once validErrorbound_def] (Parse.Term ‘validErrorbound e Gamma A dVars’)

Definition validErrorboundCmd_def:
  validErrorboundCmd (f:real cmd) (typeMap: (real expr # mType) binTree)
                    (A:analysisResult) (dVars:num_set) =
    case f of
      | Let m x e g  =>
        (case FloverMapTree_find e A, FloverMapTree_find (Var x) A of
           | SOME (iv_e, err_e), SOME (iv_x, err_x) =>
             if (validErrorbound e typeMap A dVars /\ err_e = err_x)
             then validErrorboundCmd g typeMap A (insert x () dVars)
             else F
           | _ , _ => F)
      | Ret e =>
        validErrorbound e typeMap A dVars
End

Theorem validErrorboundCmd_eq =
  SIMP_CONV flover_ss [Once validErrorboundCmd_def] (Parse.Term ‘validErrorboundCmd f Gamma A dVars’)

Definition eval_Real_def:
  eval_Real E1 Gamma e nR =
    eval_expr E1 (toRTMap (toRExpMap Gamma)) (toREval e) nR REAL
End

Definition eval_Fin_def:
  eval_Fin E2 Gamma e nF m =
    eval_expr E2 (toRExpMap Gamma) e nF m
End

val _ = export_rewrites ["eval_Real_def", "eval_Fin_def"]

Theorem err_always_positive:
  ∀ (e:real expr) (A:analysisResult) (iv:interval) (err:real) dVars tmap.
    (validErrorbound e tmap A dVars) /\
    (FloverMapTree_find e A = SOME (iv,err)) ==>
    0 <= err
Proof
  rpt strip_tac \\ Cases_on `e`
  \\ qpat_x_assum `validErrorbound _ _ _ _` mp_tac
  \\ simp[Once validErrorbound_def] \\ TOP_CASE_TAC \\ strip_tac
QED

Theorem validErrorboundCorrectVariable_eval:
  ∀ E1 E2 A v e nR nlo nhi P fVars dVars Gamma.
    eval_Real E1 Gamma (Var v) nR /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 /\
    validTypes (Var v) Gamma /\
    validRanges (Var v) A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorbound (Var v) Gamma A dVars /\
    (domain (usedVars ((Var v):real expr)) DIFF (domain dVars)) SUBSET (domain fVars) /\
    FloverMapTree_find (Var v) A = SOME ((nlo,nhi),e) ==>
    ∃ nF m.
      eval_Fin E2 Gamma (Var v) nF m
Proof
  rpt strip_tac
  \\ IMP_RES_TAC validRanges_single \\ fs[]
  \\ IMP_RES_TAC meps_0_deterministic \\ rveq
  \\ fs[toREval_def]
  \\ inversion `eval_expr E1 _ _ _ _` eval_expr_cases
  \\ rveq
  \\ qspecl_then [`E1`, `E2`, `v`, `nR`, `fVars`, `dVars`, `A`, `toRExpMap Gamma`]
      destruct approxEnv_gives_value
  \\ fs[domain_union, domain_lookup, usedVars_def]
  >- (Cases_on `lookup v dVars` \\ fs[domain_lookup])
  \\ fs[eval_expr_cases, toRExpMap_def, toRTMap_def, option_case_eq]
QED

Theorem validErrorboundCorrectVariable:
  ∀ (E1 E2:env) A fVars dVars  (v:num) (nR nF err nlo nhi:real) (P:precond) m
    Gamma.
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 /\
    eval_Real E1 Gamma (Var v) nR /\
    eval_Fin E2 Gamma (Var v) nF m /\
    validTypes (Var v) Gamma /\
    validRanges (Var v) A E1 (toRTMap (toRExpMap Gamma)) /\
    validErrorbound (Var v) Gamma A dVars /\
    (domain (usedVars ((Var v):real expr)) DIFF (domain dVars)) SUBSET (domain fVars) /\
    FloverMapTree_find (Var v) A = SOME ((nlo,nhi),err) ==>
    abs (nR - nF) <= err
Proof
  rpt strip_tac
  \\ IMP_RES_TAC validRanges_single \\ fs[]
  \\ IMP_RES_TAC meps_0_deterministic \\ rveq
  \\ fs[toREval_def]
  \\ rpt (inversion `eval_expr _ _ _ _ _` eval_expr_cases)
  \\ qpat_x_assum `validErrorbound _ _ _ _` mp_tac
  \\ simp[Once validErrorbound_eq]
  \\ rpt strip_tac \\ fs[]
  >- (drule approxEnv_dVar_bounded
      \\ rpt (disch_then drule) \\ rveq
      \\ disch_then (qspecl_then [`m`, `(nlo,nhi)`, `err`] irule)
      \\ fs[domain_lookup])
  \\ rveq
  \\ fs[usedVars_def,domain_lookup]
  \\ irule REAL_LE_TRANS \\ find_exists_tac \\ fs[]
  \\ drule approxEnv_fVar_bounded
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then  `m` assume_tac)
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `computeError nR m`
  \\ conj_tac \\ TRY (first_x_assum irule \\ fs[domain_lookup])
  \\ fs[toRExpMap_def] \\ rveq
  \\ irule computeError_up \\ fs[]
  \\ irule contained_leq_maxAbs \\ fs[contained_def, IVlo_def, IVhi_def]
QED

Theorem validErrorboundCorrectConstant_eval:
  !(E:env) (n nR:real) m Gamma.
    validTypes (Const m n) Gamma ==>
    ? nF m1.
      eval_Fin E Gamma (Const m n) nF m1
Proof
  rpt strip_tac \\ fs[validTypes_def]
  \\ qexistsl_tac [`perturb n m (mTypeToR m n)`,`m`] \\ irule Const_dist'
  \\ fs[]
  \\ qexists_tac `mTypeToR m n` \\ conj_tac \\ fs[realTheory.abs, mTypeToR_pos]
QED

Theorem validErrorboundCorrectConstant:
  ∀(E1 E2:env) (A:analysisResult) (n nR nF e nlo nhi:real) dVars m Gamma.
    eval_Real E1 Gamma (Const m n) nR /\
    eval_Fin E2 Gamma (Const m n) nF m /\
    validTypes (Const m n) Gamma /\
    validErrorbound (Const m n) Gamma A dVars /\
    (nlo <= nR /\ nR <= nhi) /\
    FloverMapTree_find (Const m n) A = SOME ((nlo,nhi),e) ==>
    (abs (nR - nF)) <= e
Proof
  rpt strip_tac \\ fs[Once validErrorbound_eq, toREval_def]
  \\ rveq \\ fs[validTypes_def] \\ rveq
  \\ irule REAL_LE_TRANS
  \\ find_exists_tac \\ fs[]
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `computeError nR m`
  \\ inversion `eval_expr _ _ _ _ REAL` eval_expr_cases
  \\ `nR = n` by (rveq \\ irule delta_REAL_deterministic \\ fs[])
  \\ rveq \\ conj_tac
  >- (irule const_abs_err_bounded
      \\ qexistsl_tac [`E1`, `E2`, `toRExpMap Gamma`]
      \\ inversion `eval_expr _ _ _ _ m` eval_expr_cases \\ rveq
      \\ conj_tac \\ irule Const_dist' \\ fs[]
      \\ find_exists_tac \\ fs[])
  \\ irule computeError_up
  \\ fs[maxAbs_def] \\  irule maxAbs \\ fs[]
QED

Theorem validErrorboundCorrectAddition:
  ∀ (E1 E2:env) (A:analysisResult) (e1:real expr) (e2:real expr)
     (nR nR1 nR2 nF nF1 nF2:real) (e err1 err2:real)
     (alo ahi e1lo e1hi e2lo e2hi :real) dVars m m1 m2 Gamma.
    eval_Real E1 Gamma e1 nR1 /\
    eval_Real E1 Gamma e2 nR2 /\
    eval_Real E1 Gamma (Binop Plus e1 e2) nR /\
    eval_Fin E2 Gamma e1 nF1 m1 /\
    eval_Fin E2 Gamma e2 nF2 m2 /\
    eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
              (updDefVars (Binop Plus (Var 1) (Var 2)) m
               (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma))))
              (Binop Plus (Var 1) (Var 2)) nF m /\
    validErrorbound (Binop Plus e1 e2) Gamma A dVars /\
    (e1lo <= nR1 /\ nR1 <= e1hi) /\
    (e2lo <= nR2 /\ nR2 <= e2hi) /\
    FloverMapTree_find e1 A = SOME ((e1lo, e1hi), err1) /\
    FloverMapTree_find e2 A = SOME ((e2lo, e2hi), err2) /\
    FloverMapTree_find (Binop Plus e1 e2) A = SOME ((alo, ahi), e) /\
    FloverMapTree_find (Binop Plus e1 e2) Gamma = SOME m /\
    abs (nR1 - nF1) <= err1 /\
    abs (nR2 - nF2) <= err2 ==>
    abs (nR - nF) <= e
Proof
  rpt strip_tac \\ simp[Once toREval_def]
  \\ fs[Once validErrorbound_eq] \\ rveq
  \\ fs[toRExpMap_def]
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `err1 + err2 + (computeError (nF1 + nF2) m)`
  \\ conj_tac
  >- (irule add_abs_err_bounded
      \\ rpt (find_exists_tac \\ fs[]))
  \\ irule REAL_LE_TRANS \\ find_exists_tac
  \\ conj_tac \\ fs[]
  \\ qmatch_abbrev_tac `_ <= computeError (maxAbs iv) _`
  \\ PairCases_on `iv` \\ irule computeError_up
  \\ unabbrev_all_tac \\ fs[maxAbs_def]
  \\ irule maxAbs
  \\ `contained nF1 (widenInterval (e1lo,e1hi) err1)`
        by (irule distance_gives_iv
            \\ qexists_tac `nR1` \\ conj_tac
            \\ simp[contained_def])
  \\ `contained nF2 (widenInterval (e2lo,e2hi) err2)`
       by (irule distance_gives_iv
           \\ qexists_tac `nR2` \\ conj_tac
           \\ simp[contained_def])
  \\ assume_tac (REWRITE_RULE [validIntervalAdd_def, contained_def] interval_addition_valid)
  \\ fs[contained_def, widenInterval_def]
QED

Theorem validErrorboundCorrectSubtraction:
  !(E1 E2:env) (A:analysisResult) (e1:real expr) (e2:real expr)
               (nR nR1 nR2 nF nF1 nF2:real) (e err1 err2:real)
               (alo ahi e1lo e1hi e2lo e2hi:real) dVars m m1 m2 Gamma.
    eval_Real E1 Gamma e1 nR1 /\
    eval_Real E1 Gamma e2 nR2 /\
    eval_Real E1 Gamma (Binop Sub e1 e2) nR /\
    eval_Fin E2 Gamma e1 nF1 m1 /\
    eval_Fin E2 Gamma e2 nF2 m2 /\
    eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
              (updDefVars (Binop Sub (Var 1) (Var 2)) m
               (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma))))
              (Binop Sub (Var 1) (Var 2)) nF m /\
    validErrorbound (Binop Sub e1 e2) Gamma A dVars /\
    (e1lo <= nR1 /\ nR1 <= e1hi) /\
    (e2lo <= nR2 /\ nR2 <= e2hi) /\
    FloverMapTree_find e1 A = SOME ((e1lo, e1hi), err1) /\
    FloverMapTree_find e2 A = SOME ((e2lo, e2hi), err2) /\
    FloverMapTree_find (Binop Sub e1 e2) A = SOME ((alo, ahi), e) /\
    FloverMapTree_find (Binop Sub e1 e2) Gamma = SOME m /\
    abs (nR1 - nF1) <= err1 /\
    abs (nR2 - nF2) <= err2 ==>
    abs (nR - nF) <= e
Proof
  rpt strip_tac \\ simp[Once toREval_def]
  \\ fs[Once validErrorbound_eq] \\ rveq
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `err1 + err2 + computeError (nF1 - nF2) m`
  \\ conj_tac
     >- (irule subtract_abs_err_bounded
         \\ rpt (find_exists_tac \\ fs[]))
  \\ irule REAL_LE_TRANS \\ find_exists_tac
  \\ conj_tac \\ fs[]
  \\ qmatch_abbrev_tac `_ <= computeError (maxAbs iv) _`
  \\ PairCases_on `iv` \\ irule computeError_up
  \\ unabbrev_all_tac \\ fs[maxAbs_def]
  \\ irule maxAbs
  \\ `contained nF1 (widenInterval (e1lo,e1hi) err1)`
        by (irule distance_gives_iv
            \\ qexists_tac `nR1` \\ conj_tac
            \\ simp[contained_def])
  \\ `contained nF2 (widenInterval (e2lo,e2hi) err2)`
       by (irule distance_gives_iv
           \\ qexists_tac `nR2` \\ conj_tac
           \\ simp[contained_def])
  \\ assume_tac (REWRITE_RULE [validIntervalSub_def, contained_def] interval_subtraction_valid)
  \\ fs[contained_def, widenInterval_def]
QED

local
  val trivial_up_tac =
    irule REAL_LE_LADD_IMP (* remove lhs of addition *)
    (* Try first proving by transitivity only *)
    \\ TRY (
       irule REAL_LE_RMUL_IMP \\ fs[] \\ NO_TAC)
    (* Try first proving by transitivity only *)
    \\ TRY (
       irule REAL_LE_LMUL_IMP \\ fs[] \\ NO_TAC)
    (* Try proving by removing negation and simplification first *)
    \\ TRY (
         rewrite_tac [GSYM REAL_NEG_RMUL, GSYM REAL_NEG_LMUL]
         \\ fs [REAL_LE_NEG] (* invert inequality with negation *)
         \\ irule REAL_LE_ADD_FLIP \\ simp[real_sub] (* by assumption *)
         \\ NO_TAC)
    (* If the above fails, we may be able to prove it by "exploiting a negation" *)
    \\ TRY (
        (qmatch_goalsub_abbrev_tac `a * - b <= - (c * b)`
        \\ real_rewrite `(a * - b ≤ - (c * b)) = (a * - b ≤ (c:real) * - b)`)
        ORELSE
        (qmatch_goalsub_abbrev_tac `a * - b <= - (b * c)`
        \\ real_rewrite `(a * - b ≤ - (b * c)) = (a * - b ≤ (c:real) * - b)`)
        ORELSE
        (qmatch_goalsub_abbrev_tac `a * b <= b * c`
        \\ real_rewrite `(a * b ≤ b * c) = (a * b ≤ (c:real) * b)`)
       ORELSE
       (qmatch_goalsub_abbrev_tac `- (a * b) <= a * - c`
       \\ real_rewrite `(- (a * b) <= a * - c) = (a:real * - b <= a * - c)`
       \\ once_rewrite_tac [REAL_MUL_COMM])
       \\ irule REAL_LE_RMUL_IMP
       \\ unabbrev_all_tac \\ fs[] \\ metis_tac[REAL_LE_ADD_FLIP, real_sub]
       \\ NO_TAC);
in
Theorem multiplicationErrorBounded:
  !(nR1 nR2 nF1 nF2: real) (err1 err2: real) (e1lo e1hi e2lo e2hi: real).
    e1lo ≤ nR1 /\ nR1 ≤ e1hi /\
    e2lo ≤ nR2 /\ nR2 ≤ e2hi /\
    abs (nR1 − nF1) ≤ err1 /\
    abs (nR2 − nF2) ≤ err2 /\
    0 ≤ err1 /\ 0 ≤ err2 ==>
    abs (nR1 * nR2 − nF1 * nF2) ≤
        maxAbs (e1lo,e1hi) * err2 + maxAbs (e2lo,e2hi) * err1 + err1 * err2
Proof
  rpt strip_tac
  \\`nR1 <= maxAbs (e1lo, e1hi)`
    by (irule contained_leq_maxAbs_val
        \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `nR2 <= maxAbs (e2lo, e2hi)`
       by (irule contained_leq_maxAbs_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\`-nR1 <= maxAbs (e1lo, e1hi)`
       by (irule contained_leq_maxAbs_neg_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `-nR2 <= maxAbs (e2lo, e2hi)`
       by (irule contained_leq_maxAbs_neg_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `nR1 * err2 <= maxAbs (e1lo, e1hi) * err2`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `-nR1 * err2 <= maxAbs (e1lo, e1hi) * err2`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `nR2 * err1 <= maxAbs (e2lo, e2hi) * err1`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `-nR2 * err1 <= maxAbs (e2lo, e2hi) * err1`
       by (irule REAL_LE_RMUL_IMP \\ fs[])
  \\ `- (err1 * err2) <= err1 * err2`
       by (once_rewrite_tac[REAL_NEG_LMUL] \\ irule REAL_LE_RMUL_IMP \\ REAL_ASM_ARITH_TAC)
  \\ `0 <= maxAbs (e1lo, e1hi) * err2` by REAL_ASM_ARITH_TAC
  \\ `maxAbs (e1lo, e1hi) * err2 <= maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       by REAL_ASM_ARITH_TAC
  \\ `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1 <=
        maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1 + err1 * err2`
          by REAL_ASM_ARITH_TAC
  \\ `! (x:real). ((abs x = x) /\ 0 < x) \/ ((abs x = - x) /\ x <= 0)`
      by REAL_ASM_ARITH_TAC
  (* Large case distinction for
     a) different cases of the value of Rabs (...) and
     b) wether arguments of multiplication in (nf1 * nF2) are < or >= 0  *)
 \\ qpat_assum `!x. (A /\ B) \/ C` (qspecl_then [`nR1 - nF1` ] assume_tac)
 \\ qpat_assum `!x. (A /\ B) \/ C` (qspecl_then [`nR2 - nF2` ] assume_tac)
 \\ fs[] \\ rfs[realTheory.abs] \\ fs[]
  (* All positive *)
 >- (
   `nF1 <= nR1 + err1` by (irule err_up \\ simp[REAL_LE_ABS_TRANS])
   \\ `nF2 <= nR2 + err2` by (irule err_up \\ simp[REAL_LE_ABS_TRANS])
   \\ qpat_assum `!x. (A /\ B) \/ C` (qspecl_then [`nR1 * nR2 - nF1 * nF2` ] assume_tac)
   \\ fs[real_sub]
   (* Absolute value positive *)
   >-(
     qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nF1 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + nF1 * (- (nR2 + err2))` \\ conj_tac
       >- (fs[REAL_NEG_RMUL])
       \\ qspecl_then [`- (nR2 + err2)`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
       (* -(nR2 + err2) < 0 *)
       >- (
         irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + (nR1 - err1) * - (nR2 + err2)` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite
              `nR1 * nR2 + (nR1 - err1) * - (nR2 + err2) = - nR1 * err2 + nR2 * err1 + err1 * err2`
         \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[])
       (* 0 ≤ -(nR2 + err2) *)
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2)` \\ conj_tac
       >- (irule REAL_LE_LADD_IMP
           \\ irule REAL_LE_RMUL_IMP \\ fs[])
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2) = - nR1 * err2 + - nR2 * err1 + - err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ TRY(simp[GSYM REAL_NEG_LMUL])
       \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
    (* 0 ≤ nF1 *)
    >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `nR1 * nR2 + nF1 * - (nR2 - err2)` \\ conj_tac
     >- (irule REAL_LE_LADD_IMP \\ once_rewrite_tac [REAL_NEG_RMUL]
         \\ irule REAL_LE_LMUL_IMP \\ fs[real_sub]
         \\ qpat_x_assum ‘∀ x. _’ kall_tac \\ REAL_ASM_ARITH_TAC)
     \\ qspecl_then [`- (nR2 - err2)`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* -(nR2 - err2) < 0 *)
     >- (irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + (nR1 - err1) * - (nR2 - err2)` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite
              `nR1 * nR2 + (nR1 - err1) * - (nR2 - err2) = nR1 * err2 + nR2 * err1 + - err1 * err2`
         \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\simp[]
         \\ simp[GSYM REAL_NEG_LMUL]
         \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
     (* 0 ≤ -(nR2 - err2) *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - (nR2 - err2)` \\ conj_tac
       >- (irule REAL_LE_LADD_IMP \\ irule REAL_LE_RMUL_IMP \\ fs[])
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - (nR2 - err2) = nR1 * err2 + - nR2 * err1 + err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL])))
   (* Absolute value negative *)
   \\ simp [REAL_NEG_ADD]
   \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nF1 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + nF1 * (nR2 - err2)` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`nR2 - err2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nR2 - err2 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `-(nR1 * nR2) + (nR1 - err1) * (nR2 - err2)` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `-(nR1 * nR2) + (nR1 - err1) * (nR2 - err2) = - nR1 * err2 + - nR2 * err1 + err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[])
     (* 0 ≤ nR2 - err2 *)
     >- (irule REAL_LE_TRANS
          \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * (nR2 - err2)` \\ conj_tac
          >- trivial_up_tac
          \\ real_rewrite
               `-(nR1 * nR2) + (nR1 + err1) * (nR2 - err2) = - nR1 * err2 + nR2 * err1 + - err1 * err2`
          \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ TRY(simp[GSYM REAL_NEG_LMUL])
          \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL]))
   (* 0 ≤ nF1 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + nF1 * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ qspecl_then [`nR2 + err2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nR2 + err2 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + (nR1 - err1) * (nR2 + err2)` \\ conj_tac
     >- trivial_up_tac
     \\ real_rewrite
          `-(nR1 * nR2) + (nR1 - err1) * (nR2 + err2) = nR1 * err2 + - nR2 * err1 + - err1 * err2`
     \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL]
     \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
   (* 0 ≤ nR2 + err2 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ real_rewrite
        `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2) = nR1 * err2 + nR2 * err1 + err1 * err2`
   \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL])

  (* First positive, second negative *)
 >- (
   `nF1 <= nR1 + err1` by (irule err_up \\ simp[REAL_LE_ABS_TRANS])
   \\ `nF2 <= nR2 + err2`
     by (once_rewrite_tac[REAL_ADD_COMM] \\ simp [GSYM REAL_LE_SUB_RADD]
         \\ once_rewrite_tac [REAL_ADD_COMM, GSYM REAL_NEG_SUB] \\ simp[] )
   \\ qpat_assum `!x. (A /\ B) \/ C` (qspecl_then [`nR1 * nR2 - nF1 * nF2` ] assume_tac)
   \\ fs[real_sub]
   \\ qpat_assum `nR2 + - nF2 <= _ `
        (fn thm => assume_tac (SIMP_RULE bool_ss [GSYM real_sub, REAL_LE_SUB_RADD, REAL_ADD_LID] thm))
   (* Absolute value positive *)
   >-(
     qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nF1 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + nF1 * (- (nR2 + err2))` \\ conj_tac
       >- (fs[REAL_NEG_RMUL])
       \\ qspecl_then [`- (nR2 + err2)`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
       (* -(nR2 + err2) < 0 *)
       >- (
         irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + (nR1 - err1) * - (nR2 + err2)` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite
              `nR1 * nR2 + (nR1 - err1) * - (nR2 + err2) = - nR1 * err2 + nR2 * err1 + err1 * err2`
         \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[])
       (* 0 ≤ -(nR2 + err2) *)
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2)` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2) = - nR1 * err2 + - nR2 * err1 + - err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ TRY(simp[GSYM REAL_NEG_LMUL])
       \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
    (* 0 ≤ nF1 *)
    >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `nR1 * nR2 + nF1 * -nR2` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`- nR2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* -nR2 < 0 *)
     >- (irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + (nR1 - err1) * - nR2` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite
              `nR1 * nR2 + (nR1 - err1) * - nR2 = nR2 * err1`
         \\ simp[] \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e2lo,e2hi) * err1` \\ conj_tac \\ simp[]
         \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
         \\ conj_tac \\ simp[]
         \\ once_rewrite_tac [REAL_ADD_COMM]
         \\ simp [REAL_LE_ADDR])
     (* 0 ≤ - nR2 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - nR2` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - nR2 = - nR2 * err1`
       \\ simp[] \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e2lo,e2hi) * err1` \\ conj_tac \\ simp[]
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[]
       \\ once_rewrite_tac [REAL_ADD_COMM]
       \\ simp [REAL_LE_ADDR])))
   (* Absolute value negative *)
   \\ simp [REAL_NEG_ADD]
   \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nF1 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + nF1 * nR2` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`nR2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nR2 - err2 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `-(nR1 * nR2) + (nR1 - err1) * nR2` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `-(nR1 * nR2) + (nR1 - err1) * nR2 = - nR2 * err1`
       \\ simp[] \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e2lo,e2hi) * err1` \\ conj_tac \\ simp[]
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[]
       \\ once_rewrite_tac [REAL_ADD_COMM]
       \\ simp [REAL_LE_ADDR])
     (* 0 ≤ nR2 - err2 *)
     >- (irule REAL_LE_TRANS
          \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * nR2` \\ conj_tac
          >- trivial_up_tac
          \\ real_rewrite
               `-(nR1 * nR2) + (nR1 + err1) * nR2 = nR2 * err1`
          \\ simp[] \\ irule REAL_LE_TRANS
          \\ qexists_tac `maxAbs (e2lo,e2hi) * err1` \\ conj_tac \\ simp[]
          \\ irule REAL_LE_TRANS
          \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
          \\ conj_tac \\ simp[]
          \\ once_rewrite_tac [REAL_ADD_COMM]
          \\ simp [REAL_LE_ADDR]))
   (* 0 ≤ nF1 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + nF1 * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ qspecl_then [`nR2 + err2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nR2 + err2 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + (nR1 - err1) * (nR2 + err2)` \\ conj_tac
     >- trivial_up_tac
     \\ real_rewrite
          `-(nR1 * nR2) + (nR1 - err1) * (nR2 + err2) = nR1 * err2 + - nR2 * err1 + - err1 * err2`
     \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL]
     \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
   (* 0 ≤ nR2 + err2 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ real_rewrite
        `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2) = nR1 * err2 + nR2 * err1 + err1 * err2`
   \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL])

  (* First negative, second positive *)
 >- (
   `nF1 <= nR1 + err1`
     by (once_rewrite_tac[REAL_ADD_COMM] \\ simp [GSYM REAL_LE_SUB_RADD]
         \\ once_rewrite_tac [REAL_ADD_COMM, GSYM REAL_NEG_SUB] \\ simp[])
   \\ `nF2 <= nR2 + err2` by (irule err_up \\ simp[])
   \\ qpat_assum `!x. (A /\ B) \/ C` (fn thm => qspecl_then [`nR1 * nR2 - nF1 * nF2` ] DISJ_CASES_TAC thm)
   \\ fs[real_sub]
   (* Absolute value positive *)
   >-(
     qpat_x_assum `nR1 + - nF1 <= _ `
        (fn thm => assume_tac (SIMP_RULE bool_ss [GSYM real_sub, REAL_LE_SUB_RADD, REAL_ADD_LID] thm))
     \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nF1 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + nF1 * - (nR2 + err2)` \\ conj_tac
       >- (fs[REAL_NEG_RMUL])
       \\ qspecl_then [`- (nR2 + err2)`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
       (* -(nR2 + err2) < 0 *)
       >- (
         irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + nR1 * - (nR2 + err2)` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite `nR1 * nR2 + nR1 * - (nR2 + err2) = - nR1 * err2`
         \\ simp[] \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
         \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
         \\ conj_tac \\ simp[])
       (* 0 ≤ -(nR2 + err2) *)
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2)` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2) = - nR1 * err2 + - nR2 * err1 + - err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ TRY(simp[GSYM REAL_NEG_LMUL])
       \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
    (* 0 ≤ nF1 *)
    >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `nR1 * nR2 + nF1 * - (nR2 - err2)` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`- (nR2 - err2)`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* -(nR2 - err2) < 0 *)
     >- (irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + nR1 * - (nR2 - err2)` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite `nR1 * nR2 + nR1 * - (nR2 - err2) = nR1 * err2`
         \\ simp[] \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
         \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
         \\ conj_tac \\ simp[])
     (* 0 ≤ -(nR2 - err2) *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - (nR2 - err2)` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - (nR2 - err2) = nR1 * err2 + - nR2 * err1 + err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL])))
   (* Absolute value negative *)
   \\ qpat_x_assum `nR1 + - nF1 <= _ `
        (fn thm => assume_tac (SIMP_RULE bool_ss [GSYM real_sub, REAL_LE_SUB_RADD, REAL_ADD_LID] thm))
   \\ simp [REAL_NEG_ADD]
   \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nF1 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + nF1 * (nR2 - err2)` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`nR2 - err2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nR2 - err2 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `-(nR1 * nR2) + nR1 * (nR2 - err2)` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite `-(nR1 * nR2) + nR1 * (nR2 - err2) = - nR1 * err2`
       \\ simp[] \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[])
     (* 0 ≤ nR2 - err2 *)
     >- (irule REAL_LE_TRANS
          \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * (nR2 - err2)` \\ conj_tac
          >- trivial_up_tac
          \\ real_rewrite
               `-(nR1 * nR2) + (nR1 + err1) * (nR2 - err2) = - nR1 * err2 + nR2 * err1 + - err1 * err2`
          \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ TRY(simp[GSYM REAL_NEG_LMUL])
          \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL]))
   (* 0 ≤ nF1 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + nF1 * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ qspecl_then [`nR2 + err2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nR2 + err2 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + nR1 * (nR2 + err2)` \\ conj_tac
     >- trivial_up_tac
     \\ real_rewrite `-(nR1 * nR2) + nR1 * (nR2 + err2) = nR1 * err2`
     \\ simp[] \\ irule REAL_LE_TRANS
     \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
     \\ irule REAL_LE_TRANS
     \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
     \\ conj_tac \\ simp[])
   (* 0 ≤ nR2 + err2 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ real_rewrite
        `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2) = nR1 * err2 + nR2 * err1 + err1 * err2`
   \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL])

  (* Both negative *)
 >- (
  `nF1 <= nR1 + err1`
    by (once_rewrite_tac[REAL_ADD_COMM]
        \\ simp [GSYM REAL_LE_SUB_RADD]
        \\ once_rewrite_tac [REAL_ADD_COMM, GSYM REAL_NEG_SUB] \\ simp[])
  \\ `nF2 <= nR2 + err2`
    by (once_rewrite_tac[REAL_ADD_COMM]
        \\ simp [GSYM REAL_LE_SUB_RADD]
        \\ once_rewrite_tac [REAL_ADD_COMM, GSYM REAL_NEG_SUB] \\ simp[])
  \\ `nR1 <= nF1`
    by (qpat_x_assum `nR1 - nF1 <= _ `
        (fn thm =>
         assume_tac
         (SIMP_RULE bool_ss [GSYM real_sub, REAL_LE_SUB_RADD, REAL_ADD_LID] thm))
        \\ simp[])
  \\ `nR2 <= nF2`
    by (qpat_x_assum `nR2 - nF2 <= _ `
        (fn thm =>
         assume_tac (SIMP_RULE bool_ss [GSYM real_sub, REAL_LE_SUB_RADD, REAL_ADD_LID] thm))
        \\ simp[])
  \\ qpat_assum `!x. (A /\ B) \/ C`
                  (fn thm => qspecl_then [`nR1 * nR2 - nF1 * nF2` ] DISJ_CASES_TAC thm)
  \\ fs[real_sub]
   (* Absolute value positive *)
   >-(
     qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nF1 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + nF1 * - (nR2 + err2)` \\ conj_tac
       >- (fs[REAL_NEG_RMUL])
       \\ qspecl_then [`- (nR2 + err2)`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
       (* -(nR2 + err2) < 0 *)
       >- (
         irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + nR1 * - (nR2 + err2)` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite `nR1 * nR2 + nR1 * - (nR2 + err2) = - nR1 * err2`
         \\ simp[] \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
         \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
         \\ conj_tac \\ simp[])
       (* 0 ≤ -(nR2 + err2) *)
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2)` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - (nR2 + err2) = - nR1 * err2 + - nR2 * err1 + - err1 * err2`
       \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ TRY(simp[GSYM REAL_NEG_LMUL])
       \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[REAL_NEG_LMUL])
    (* 0 ≤ nF1 *)
    >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `nR1 * nR2 + nF1 * -nR2` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`- nR2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* -nR2 < 0 *)
     >- (irule REAL_LE_TRANS
         \\ qexists_tac `nR1 * nR2 + nR1 * - nR2` \\ conj_tac
         >- trivial_up_tac
         \\ real_rewrite `nR1 * nR2 + nR1 * - nR2 = 0`
         \\ simp[] \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2`
         \\ conj_tac \\ simp[]
         \\ irule REAL_LE_TRANS
         \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
         \\ conj_tac \\ simp[])
     (* 0 ≤ - nR2 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `nR1 * nR2 + (nR1 + err1) * - nR2` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite
            `nR1 * nR2 + (nR1 + err1) * - nR2 = - nR2 * err1`
       \\ simp[] \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e2lo,e2hi) * err1` \\ conj_tac \\ simp[]
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[]
       \\ once_rewrite_tac [REAL_ADD_COMM]
       \\ simp [REAL_LE_ADDR])))
   (* Absolute value negative *)
   \\ simp [REAL_NEG_ADD]
   \\ qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nF1 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + nF1 * nR2` \\ conj_tac
     >- trivial_up_tac
     \\ qspecl_then [`nR2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
     (* nR2 < 0 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `-(nR1 * nR2) + nR1 * nR2 ` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite `-(nR1 * nR2) + nR1 * nR2 = 0`
       \\ simp[] \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[])
     (* 0 ≤ nR2 - err2 *)
     >- (
       irule REAL_LE_TRANS
       \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * nR2` \\ conj_tac
       >- trivial_up_tac
       \\ real_rewrite `-(nR1 * nR2) + (nR1 + err1) * nR2 = nR2 * err1`
       \\ simp[] \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[]
       \\ irule REAL_LE_TRANS
       \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
       \\ conj_tac \\ simp[]
       \\ once_rewrite_tac [REAL_ADD_COMM]
       \\ simp[REAL_LE_ADDR]))
   (* 0 ≤ nF1 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + nF1 * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ qspecl_then [`nR2 + err2`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
   (* nR2 + err2 < 0 *)
   >- (
     irule REAL_LE_TRANS
     \\ qexists_tac `-(nR1 * nR2) + nR1 * (nR2 + err2)` \\ conj_tac
     >- trivial_up_tac
     \\ real_rewrite `-(nR1 * nR2) + nR1 * (nR2 + err2) = nR1 * err2`
     \\ simp[] \\ irule REAL_LE_TRANS
     \\ qexists_tac `maxAbs (e1lo, e1hi) * err2` \\ conj_tac \\ simp[]
     \\ irule REAL_LE_TRANS
     \\ qexists_tac `maxAbs (e1lo, e1hi) * err2 + maxAbs (e2lo, e2hi) * err1`
     \\ conj_tac \\ simp[])
   (* 0 ≤ nR2 + err2 *)
   \\ irule REAL_LE_TRANS
   \\ qexists_tac `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2)` \\ conj_tac
   >- trivial_up_tac
   \\ real_rewrite
        `-(nR1 * nR2) + (nR1 + err1) * (nR2 + err2) = nR1 * err2 + nR2 * err1 + err1 * err2`
   \\ simp[] \\ irule REAL_LE_ADD2 \\ conj_tac \\ simp[GSYM REAL_NEG_LMUL])
QED
end

Theorem validErrorboundCorrectMult:
  !(E1 E2:env) (A:analysisResult) (e1:real expr) (e2:real expr)
               (nR nR1 nR2 nF nF1 nF2:real) (e err1 err2:real)
               (alo ahi e1lo e1hi e2lo e2hi :real) dVars m m1 m2 Gamma.
    eval_Real E1 Gamma e1 nR1 /\
    eval_Real E1 Gamma e2 nR2 /\
    eval_Real E1 Gamma (Binop Mult e1 e2) nR /\
    eval_Fin E2 Gamma e1 nF1 m1 /\
    eval_Fin E2 Gamma e2 nF2 m2 /\
    eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
              (updDefVars (Binop Mult (Var 1) (Var 2)) m
               (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma))))
              (Binop Mult (Var 1) (Var 2)) nF m /\
    validErrorbound (Binop Mult e1 e2) Gamma A dVars /\
    (e1lo <= nR1 /\ nR1 <= e1hi) /\
    (e2lo <= nR2 /\ nR2 <= e2hi) /\
    FloverMapTree_find e1 A = SOME ((e1lo, e1hi), err1) /\
    FloverMapTree_find e2 A = SOME ((e2lo, e2hi), err2) /\
    FloverMapTree_find (Binop Mult e1 e2) A = SOME ((alo, ahi), e) /\
    FloverMapTree_find (Binop Mult e1 e2) Gamma = SOME m /\
    abs (nR1 - nF1) <= err1 /\
    abs (nR2 - nF2) <= err2 ==>
    abs (nR - nF) <= e
Proof
  rpt strip_tac \\ simp[Once toREval_def]
  \\ fs[Once validErrorbound_eq] \\ rveq
  \\ `0 <= err1`
       by (irule err_always_positive
           \\ qexistsl_tac [`A`, `dVars`, `e1`, `(e1lo,e1hi)`, `Gamma`]
           \\ fs[])
  \\ `0 <= err2`
       by (drule err_always_positive
           \\ rpt (disch_then drule)
           \\ fs[])
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `abs (nR1 * nR2 - nF1 * nF2) + computeError (nF1 * nF2) m`
  \\ conj_tac
  >- (irule mult_abs_err_bounded \\ rpt conj_tac
      \\ rpt (find_exists_tac \\ fs[]))
  \\ irule REAL_LE_TRANS \\ find_exists_tac
  \\ conj_tac \\ fs[]
  \\ irule REAL_LE_ADD2 \\ conj_tac
  >- (
   real_rewrite `err2 * maxAbs (e1lo, e1hi) + err1 * maxAbs (e2lo,e2hi) + err1 * err2 =
                maxAbs (e1lo, e1hi) * err2 +  maxAbs (e2lo,e2hi) * err1 + err1 * err2`
   \\ irule multiplicationErrorBounded \\ fs[])
  \\ qmatch_abbrev_tac `_ <= computeError (maxAbs iv) _`
  \\ PairCases_on `iv` \\ irule computeError_up
  \\ unabbrev_all_tac \\ fs[maxAbs_def]
  \\ irule maxAbs
  \\ `contained nF1 (widenInterval (e1lo,e1hi) err1)`
        by (irule distance_gives_iv
            \\ qexists_tac `nR1` \\ conj_tac
            \\ simp[contained_def])
  \\ `contained nF2 (widenInterval (e2lo,e2hi) err2)`
       by (irule distance_gives_iv
           \\ qexists_tac `nR2` \\ conj_tac
           \\ simp[contained_def])
  \\ assume_tac (REWRITE_RULE [contained_def] interval_multiplication_valid)
  \\ fs[contained_def, widenInterval_def]
QED

val _ = diminish_srw_ss ["RMULCANON_ss","RMULRELNORM_ss"]

Theorem divisionErrorBounded:
  !(e1lo e1hi nR1 e2lo e2hi nR2 nF1 nF2 err1 err2:real).
    (e1lo <= nR1) /\ (nR1 <= e1hi) /\
    (e2lo <= nR2) /\ (nR2 <= e2hi) /\
    abs (nR1 − nF1) <= err1 /\
    abs (nR2 − nF2) <= err2 /\
    0 <= err1 /\
    0 <= err2 /\
    contained nF1 (widenInterval (e1lo,e1hi) err1) /\
    contained nF2 (widenInterval (e2lo,e2hi) err2) /\
    noDivzero e2hi e2lo /\
    noDivzero (SND (widenInterval (e2lo,e2hi) err2))
    (FST (widenInterval (e2lo,e2hi) err2)) ==>
    abs (nR1 / nR2 − nF1 / nF2) ≤
    maxAbs (e1lo,e1hi) *
         (1 /
          (minAbsFun (widenInterval (e2lo,e2hi) err2) *
           minAbsFun (widenInterval (e2lo,e2hi) err2)) * err2) +
         maxAbs (invertInterval (e2lo,e2hi)) * err1 +
         err1 *
         (1 /
          (minAbsFun (widenInterval (e2lo,e2hi) err2) *
           minAbsFun (widenInterval (e2lo,e2hi) err2)) * err2)
Proof
  rpt strip_tac
  \\ `contained (inv nR2) (invertInterval (e2lo, e2hi))`
       by (match_mp_tac interval_inversion_valid \\ conj_tac
           \\ fs[contained_def, IVlo_def, IVhi_def, noDivzero_def])
  \\ `contained (inv nF2) (invertInterval (widenInterval (e2lo, e2hi) err2))`
       by (match_mp_tac interval_inversion_valid \\ conj_tac
           \\ fs[contained_def, IVlo_def, IVhi_def, noDivzero_def])
  \\ `nR1 <= maxAbs (e1lo, e1hi)`
       by (match_mp_tac contained_leq_maxAbs_val
            \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `inv nR2 <= maxAbs (invertInterval(e2lo, e2hi))`
       by (match_mp_tac contained_leq_maxAbs_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `-nR1 <= maxAbs (e1lo, e1hi)`
       by (match_mp_tac contained_leq_maxAbs_neg_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `- inv nR2 <= maxAbs (invertInterval (e2lo, e2hi))`
       by (match_mp_tac contained_leq_maxAbs_neg_val
           \\ fs[contained_def, IVlo_def, IVhi_def])
  \\ `nR1 * err2 <= maxAbs (e1lo, e1hi) * err2`
       by (match_mp_tac REAL_LE_RMUL_IMP \\ fs[])
  \\ `-nR1 * err2 <= maxAbs (e1lo, e1hi) * err2`
       by (match_mp_tac REAL_LE_RMUL_IMP \\ fs[])
  \\ `inv nR2 * err1 <= maxAbs (invertInterval(e2lo, e2hi)) * err1`
       by (match_mp_tac REAL_LE_RMUL_IMP \\ fs[])
  \\ `- inv nR2 * err1 <= maxAbs (invertInterval(e2lo, e2hi)) * err1`
       by (match_mp_tac REAL_LE_RMUL_IMP \\ fs[])
  \\ `- (err1 * err2) <= err1 * err2`
        by (fs[REAL_NEG_LMUL] \\ match_mp_tac REAL_LE_RMUL_IMP
            \\ REAL_ASM_ARITH_TAC)
  \\ `0 <= maxAbs (e1lo, e1hi) * err2` by REAL_ASM_ARITH_TAC
  \\ `0 <= maxAbs (invertInterval (e2lo, e2hi)) * err1` by REAL_ASM_ARITH_TAC
  \\ `maxAbs (e1lo, e1hi) * err2 <=
      maxAbs (e1lo, e1hi) * err2 + maxAbs (invertInterval (e2lo, e2hi)) * err1`
       by (REAL_ASM_ARITH_TAC)
  \\ `maxAbs (e1lo, e1hi) * err2 + maxAbs (invertInterval(e2lo, e2hi)) * err1 <=
      maxAbs (e1lo, e1hi) * err2 + maxAbs (invertInterval (e2lo, e2hi)) * err1 + err1 * err2`
       by REAL_ASM_ARITH_TAC
   (* Case distinction for divisor range
      positive or negative in float and real valued execution *)
  \\ fs [IVlo_def, IVhi_def, widenInterval_def, contained_def, noDivzero_def]
  (* The range of the divisor lies in the range from -infinity until 0 *)
  >- (`abs (inv nR2 - inv nF2) <= err2 * inv ((e2hi + err2) * (e2hi + err2))`
        by (match_mp_tac err_prop_inversion_neg \\ qexists_tac `e2lo` \\simp[])
      \\ fs [widenInterval_def, IVlo_def, IVhi_def]
      \\ `minAbsFun (e2lo - err2, e2hi + err2) = - (e2hi + err2)`
           by (match_mp_tac minAbs_negative_iv_is_hi \\ REAL_ASM_ARITH_TAC)
      \\ simp[]
      \\ qpat_x_assum `minAbsFun _ = _ ` kall_tac
      \\ `nF1 <= err1 + nR1` by REAL_ASM_ARITH_TAC
      \\ `nR1 - err1 <= nF1` by REAL_ASM_ARITH_TAC
      \\ `(nR2 - nF2 > 0 /\ nR2 - nF2 <= err2) \/ (nR2 - nF2 <= 0 /\ - (nR2 - nF2) <= err2)`
           by REAL_ASM_ARITH_TAC
      (* Positive case for abs (nR2 - nF2) <= err2 *)
      >- (`nF2 < nR2` by REAL_ASM_ARITH_TAC
          \\ qpat_x_assum `nF2 < nR2` (fn thm => assume_tac (ONCE_REWRITE_RULE [GSYM REAL_LT_NEG] thm))
          \\ `inv (- nF2) < inv (- nR2)` by (match_mp_tac REAL_LT_INV \\ REAL_ASM_ARITH_TAC)
          \\ `inv (- nF2) = - (inv nF2)` by (match_mp_tac (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC)
          \\ `inv (- nR2) = - (inv nR2)` by (match_mp_tac (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC)
          \\ rpt (qpat_x_assum `inv (- _) = - (inv _)`
                   (fn thm => rule_assum_tac (fn hyp => REWRITE_RULE [thm] hyp)))
          \\ `inv nR2 < inv nF2` by REAL_ASM_ARITH_TAC
          \\ qpat_x_assum `- _ < - _` kall_tac
          \\ `inv nR2 - inv nF2 < 0` by REAL_ASM_ARITH_TAC
          \\ `- (nR2⁻¹ − nF2⁻¹) ≤ err2 * ((e2hi + err2) * (e2hi + err2))⁻¹`
               by REAL_ASM_ARITH_TAC
          \\ `inv nF2 <= inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2))`
               by REAL_ASM_ARITH_TAC
          \\ `inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)) <= inv nF2`
               by REAL_ASM_ARITH_TAC
          (* Next do a case distinction for the absolute value *)
          \\ `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC
          \\ qpat_x_assum `!x. A /\ B \/ C`
               (fn thm =>
                   qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)`
                     DISJ_CASES_TAC thm)
          \\ fs[realTheory.abs]
          (* Case 1: Absolute value positive *)
          >- (fs[real_sub, real_div, REAL_NEG_LMUL]
              \\ qspecl_then [`-nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
              (* -nF1 < 0 *)
              >- (match_mp_tac REAL_LE_TRANS
                  \\ qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)))`
                  \\ conj_tac
                  >- (fs[REAL_LE_LADD]
                      \\ match_mp_tac REAL_MUL_LE_COMPAT_NEG_L
                      \\ conj_tac \\ REAL_ASM_ARITH_TAC)
                  >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)`
                      \\ qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                      >- (match_mp_tac REAL_LE_TRANS
                          \\ qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)`
                          \\ conj_tac
                          >- (fs [REAL_LE_ADD]
                              \\ once_rewrite_tac [REAL_MUL_COMM]
                              \\ match_mp_tac REAL_MUL_LE_COMPAT_NEG_L
                              \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
                              \\ fs [REAL_LE_NEG])
                          >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                               nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                                by REAL_ASM_ARITH_TAC
                              \\ simp[REAL_NEG_MUL2]
                              \\ qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                                   (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM
                              \\ qunabbrev_tac `err_inv`
                              \\ match_mp_tac REAL_LE_ADD2
            \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
            \\ match_mp_tac REAL_LE_ADD2
            \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
            \\ match_mp_tac REAL_LE_RMUL_IMP
            \\ conj_tac \\ REAL_ASM_ARITH_TAC))
          >- (match_mp_tac REAL_LE_TRANS
                          \\ qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)`
                          \\ conj_tac
        >- (fs [REAL_LE_ADD]
                              \\ match_mp_tac REAL_LE_RMUL_IMP
            \\ conj_tac \\ REAL_ASM_ARITH_TAC)
        >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
             nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                                by REAL_ASM_ARITH_TAC
                               \\ simp[REAL_NEG_MUL2]
             \\ qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM
                               \\ qunabbrev_tac `err_inv`
                               \\ simp [real_sub]
             \\ match_mp_tac REAL_LE_ADD2
             \\ conj_tac
             >- (match_mp_tac REAL_LE_ADD2
                                   \\ conj_tac \\ TRY REAL_ASM_ARITH_TAC
           \\ match_mp_tac REAL_LE_RMUL_IMP
           \\ conj_tac \\ REAL_ASM_ARITH_TAC)
             >- (simp [REAL_NEG_LMUL]
                                   \\ match_mp_tac REAL_LE_RMUL_IMP
           \\ conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (match_mp_tac REAL_LE_TRANS
                  \\ qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2)))`
                  \\ conj_tac
      >- (fs[REAL_LE_LADD]
                      \\ match_mp_tac REAL_LE_LMUL_IMP
                      \\ conj_tac \\ REAL_ASM_ARITH_TAC)
      >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)`
                      \\ qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                      >- (match_mp_tac REAL_LE_TRANS
                          \\ qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)`
                          \\ conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                        - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp[real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (simp [REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                        - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)))))
            (* Case 2: Absolute value negative *)
            >- (fs[real_sub, real_div, REAL_NEG_LMUL, REAL_NEG_ADD] \\
              qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
              (* nF1 < 0 *)
              >- (match_mp_tac REAL_LE_TRANS \\
                qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                       once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                       - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((-e2hi + -err2) * (-e2hi + -err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                       - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((-e2hi + -err2) * (-e2hi + -err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp [real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))))
              (* 0 <= - nF1 *)
              >- (match_mp_tac REAL_LE_TRANS \\
                qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  match_mp_tac REAL_LE_LMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((-e2hi + -err2) * (-e2hi + -err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp[real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL, REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((-e2hi + -err2) * (-e2hi + -err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC))))))
          (* Negative case for abs (nR2 - nF2) <= err2 *)
          >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
            `nR2 <= nF2` by REAL_ASM_ARITH_TAC \\
            qpat_x_assum `nR2 <= nF2` (fn thm => assume_tac (ONCE_REWRITE_RULE [GSYM REAL_LE_NEG] thm)) \\
            `inv (- nR2) <= inv (- nF2)` by (match_mp_tac REAL_INV_LE_ANTIMONO_IMPR \\ REAL_ASM_ARITH_TAC) \\
            `inv (- nR2) = - (inv nR2)` by (match_mp_tac (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC) \\
            `inv (- nF2) = - (inv nF2)` by (match_mp_tac (GSYM REAL_NEG_INV) \\ REAL_ASM_ARITH_TAC) \\
            rpt (
                  qpat_x_assum `inv (- _) = - (inv _)`
                (fn thm => rule_assum_tac (fn hyp => REWRITE_RULE [thm] hyp))) \\
            `inv nF2 <= inv nR2` by REAL_ASM_ARITH_TAC \\
            qpat_x_assum `- _ <= - _` kall_tac \\
            `0 <= inv nR2 - inv nF2` by REAL_ASM_ARITH_TAC \\
            `(nR2⁻¹ − nF2⁻¹) ≤ err2 * ((e2hi + err2) * (e2hi + err2))⁻¹` by REAL_ASM_ARITH_TAC \\
            `inv nF2 <= inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2))` by REAL_ASM_ARITH_TAC \\
            `inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)) <= inv nF2` by REAL_ASM_ARITH_TAC \\
            (* Next do a case distinction for the absolute value *)
            `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC \\
            qpat_x_assum `!x. A /\ B \/ C`
              (fn thm => qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)` DISJ_CASES_TAC thm) \\
            fs[real_sub, real_div, REAL_NEG_LMUL, REAL_NEG_ADD, realTheory.abs]
            (* Case 1: Absolute value positive *)
            >- (qspecl_then [`-nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
              (* -nF1 < 0 *)
              >- (match_mp_tac REAL_LE_TRANS \\
                qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                        nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
                        nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp [real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (simp [REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))))
              (* 0 <= - nF1 *)
              >- (match_mp_tac REAL_LE_TRANS \\
                qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  match_mp_tac REAL_LE_LMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                        - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp[real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (simp [REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                        - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)))))
            (* Case 2: Absolute value negative *)
            >- (qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
              (* nF1 < 0 *)
              >- (match_mp_tac REAL_LE_TRANS \\
                qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                       once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                       - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                       - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp [real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))))
              (* 0 <= - nF1 *)
              >- (match_mp_tac REAL_LE_TRANS \\
                qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2hi + err2) * (e2hi + err2)))` \\
                conj_tac
                >- (fs[REAL_LE_LADD] \\
                  match_mp_tac REAL_LE_LMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (qabbrev_tac `err_inv = (err2 * ((e2hi + err2) * (e2hi + err2))⁻¹)` \\
                  qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      once_rewrite_tac [REAL_MUL_COMM] \\
                      match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      fs [REAL_LE_NEG])
                    >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      simp[real_sub] \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac
                      >- (match_mp_tac REAL_LE_ADD2 \\
                        conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)
                      >- (fs [REAL_NEG_LMUL] \\
                        match_mp_tac REAL_LE_RMUL_IMP \\
                        conj_tac \\ REAL_ASM_ARITH_TAC)))
                  >- (match_mp_tac REAL_LE_TRANS \\
                    qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
                    conj_tac
                    >- (fs [REAL_LE_ADD] \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)
                    >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                        nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                          by REAL_ASM_ARITH_TAC \\
                      simp[REAL_NEG_MUL2] \\
                      qspecl_then [`inv ((e2hi + err2) * (e2hi + err2))`,`err2`]
                        (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                      qunabbrev_tac `err_inv` \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_ADD2 \\
                      conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                      match_mp_tac REAL_LE_RMUL_IMP \\
                      conj_tac \\ REAL_ASM_ARITH_TAC)))))))
  >- (CCONTR_TAC \\
      rule_assum_tac (fn thm => REWRITE_RULE[IVlo_def, IVhi_def, widenInterval_def] thm) \\
      `e2lo <= e2hi` by REAL_ASM_ARITH_TAC \\
      `e2lo <= e2hi + err2` by REAL_ASM_ARITH_TAC \\
      `e2lo <= e2hi + err2` by REAL_ASM_ARITH_TAC \\
      REAL_ASM_ARITH_TAC)
  >- (CCONTR_TAC \\
      rule_assum_tac (fn thm => REWRITE_RULE[IVlo_def, IVhi_def, widenInterval_def] thm) \\
      `e2lo <= e2hi` by REAL_ASM_ARITH_TAC \\
      `e2lo - err2 <= e2hi` by REAL_ASM_ARITH_TAC \\
      REAL_ASM_ARITH_TAC)
(* The range of the divisor lies in the range from 0 to infinity *)
  >- (rule_assum_tac
      (fn thm =>
                REWRITE_RULE[IVlo_def, IVhi_def, widenInterval_def, contained_def, invertInterval_def] thm) \\
     `abs (inv nR2 - inv nF2) <= err2 * (inv ((e2lo - err2) * (e2lo -err2)))`
               by (match_mp_tac err_prop_inversion_pos \\
                   qexists_tac `e2hi` \\ rpt(conj_tac) \\
                   fs[contained_def, IVlo_def, IVhi_def]) \\
     fs [widenInterval_def, IVlo_def, IVhi_def, invertInterval_def] \\
     `minAbsFun (e2lo - err2, e2hi + err2) = (e2lo - err2)`
               by (match_mp_tac minAbs_positive_iv_is_lo \\ REAL_ASM_ARITH_TAC) \\
     simp[] \\
     qpat_x_assum `minAbsFun _ = _ ` kall_tac \\
     `nF1 <= err1 + nR1` by REAL_ASM_ARITH_TAC \\
     `nR1 - err1 <= nF1` by REAL_ASM_ARITH_TAC \\
     `(nR2 - nF2 > 0 /\ nR2 - nF2 <= err2) \/ (nR2 - nF2 <= 0 /\ - (nR2 - nF2) <= err2)`
               by REAL_ASM_ARITH_TAC
    (* Positive case for abs (nR2 - nF2) <= err2 *)
    >- (`nF2 < nR2` by REAL_ASM_ARITH_TAC \\
      `inv nR2 < inv nF2` by (match_mp_tac REAL_LT_INV \\ TRY REAL_ASM_ARITH_TAC) \\
      `inv nR2 - inv nF2 < 0` by REAL_ASM_ARITH_TAC \\
      `nR2⁻¹ − nF2⁻¹ ≤ err2 * ((e2lo - err2) * (e2lo - err2))⁻¹` by REAL_ASM_ARITH_TAC \\
      `inv nF2 <= inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2))` by REAL_ASM_ARITH_TAC \\
      `inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)) <= inv nF2` by REAL_ASM_ARITH_TAC \\
      (* Next do a case distinction for the absolute value *)
      `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC \\
      qpat_x_assum `!x. A /\ B \/ C`
        (fn thm => qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)` DISJ_CASES_TAC thm)
      \\ fs[realTheory.abs]
      (* Case 1: Absolute value positive *)
      >- (fs[real_sub, real_div, REAL_NEG_LMUL] \\
        qspecl_then [`-nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* -nF1 < 0 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + - err2) * (e2lo + - err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp[GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)))))
      (* Case 2: Absolute value negative *)
      >- (fs[real_sub, real_div, REAL_NEG_LMUL, REAL_NEG_ADD] \\
        qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* nF1 < 0 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                 once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))))))
    (* Negative case for abs (nR2 - nF2) <= err2 *)
    >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
      `nR2 <= nF2` by REAL_ASM_ARITH_TAC \\
      `inv nF2 <= inv nR2` by (match_mp_tac REAL_INV_LE_ANTIMONO_IMPR \\ REAL_ASM_ARITH_TAC) \\
      `0 <= inv nR2 - inv nF2` by REAL_ASM_ARITH_TAC \\
      `(nR2⁻¹ − nF2⁻¹) ≤ err2 * ((e2lo - err2) * (e2lo - err2))⁻¹` by REAL_ASM_ARITH_TAC \\
      `inv nF2 <= inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2))` by REAL_ASM_ARITH_TAC \\
      `inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)) <= inv nF2` by REAL_ASM_ARITH_TAC \\
      (* Next do a case distinction for the absolute value *)
      `! (x:real). ((abs x = x) /\ 0 <= x) \/ ((abs x = - x) /\ x < 0)` by REAL_ASM_ARITH_TAC \\
      qpat_x_assum `!x. A /\ B \/ C`
        (fn thm => qspec_then `(nR1:real / nR2:real) - (nF1:real / nF2:real)` DISJ_CASES_TAC thm) \\
      fs[real_sub, real_div, REAL_NEG_LMUL, REAL_NEG_ADD, realTheory.abs]
      (* Case 1: Absolute value positive *)
      >- (qspecl_then [`-nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* -nF1 < 0 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 - err_inv) =
                  nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `nR1 * inv nR2 + - nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`nR1 * inv nR2 + - (nR1 + err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (simp [REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`nR1 * inv nR2 + - (nR1 + - err1) * (inv nR2 + err_inv) =
                  - nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)))))
      (* Case 2: Absolute value negative *)
      >- (qspecl_then [`nF1`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
        (* nF1 < 0 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 - err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_MUL_LE_COMPAT_NEG_L \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 - err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                 once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + - (inv nR2) * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 - err_inv) =
                 - nR1 * err_inv + inv nR2 * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp [real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [GSYM REAL_NEG_ADD, REAL_NEG_MUL2, REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))))
        (* 0 <= - nF1 *)
        >- (match_mp_tac REAL_LE_TRANS \\
          qexists_tac `- nR1 * inv nR2 + nF1 * (inv nR2 + err2 * inv ((e2lo - err2) * (e2lo - err2)))` \\
          conj_tac
          >- (fs[REAL_LE_LADD] \\
            match_mp_tac REAL_LE_LMUL_IMP \\
            conj_tac \\ REAL_ASM_ARITH_TAC)
          >- (qabbrev_tac `err_inv = (err2 * ((e2lo - err2) * (e2lo - err2))⁻¹)` \\
            qspecl_then [`inv nR2 + err_inv`, `0`] DISJ_CASES_TAC REAL_LTE_TOTAL
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `-nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                once_rewrite_tac [REAL_MUL_COMM] \\
                match_mp_tac REAL_MUL_LE_COMPAT_NEG_L\\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                fs [REAL_LE_NEG])
              >- (`- nR1 * inv nR2 + (nR1 - err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + - (inv nR2) * err1 - err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                simp[real_sub] \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac
                >- (match_mp_tac REAL_LE_ADD2 \\
                  conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)
                >- (fs [REAL_NEG_LMUL] \\
                  match_mp_tac REAL_LE_RMUL_IMP \\
                  conj_tac \\ REAL_ASM_ARITH_TAC)))
            >- (match_mp_tac REAL_LE_TRANS \\
              qexists_tac `- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv)` \\
              conj_tac
              >- (fs [REAL_LE_ADD] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)
              >- (`- nR1 * inv nR2 + (nR1 + err1) * (inv nR2 + err_inv) =
                  nR1 * err_inv + inv nR2 * err1 + err1 * err_inv`
                    by REAL_ASM_ARITH_TAC \\
                simp[REAL_NEG_MUL2] \\
                qspecl_then [`inv ((e2lo + -err2) * (e2lo + -err2))`,`err2`]
                  (fn thm => once_rewrite_tac [thm]) REAL_MUL_COMM \\
                qunabbrev_tac `err_inv` \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                match_mp_tac REAL_LE_ADD2 \\
                conj_tac \\ TRY REAL_ASM_ARITH_TAC \\
                simp [GSYM real_sub] \\
                match_mp_tac REAL_LE_RMUL_IMP \\
                conj_tac \\ REAL_ASM_ARITH_TAC)))))))
QED

Theorem validErrorboundCorrectDiv:
  !(E1 E2:env) (A:analysisResult) (e1:real expr) (e2:real expr)
               (nR nR1 nR2 nF nF1 nF2:real) (e err1 err2:real)
               (alo ahi e1lo e1hi e2lo e2hi :real) dVars m m1 m2 Gamma.
    eval_Real E1 Gamma e1 nR1 /\
    eval_Real E1 Gamma e2 nR2 /\
    eval_Real E1 Gamma (Binop Div e1 e2) nR /\
    eval_Fin E2 Gamma e1 nF1 m1 /\
    eval_Fin E2 Gamma e2 nF2 m2 /\
    eval_expr (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv))
              (updDefVars (Binop Div (Var 1) (Var 2)) m
               (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma))))
              (Binop Div (Var 1) (Var 2)) nF m /\
    validErrorbound (Binop Div e1 e2) Gamma A dVars /\
    (e1lo <= nR1 /\ nR1 <= e1hi) /\
    (e2lo <= nR2 /\ nR2 <= e2hi) /\
    noDivzero e2hi e2lo /\
    FloverMapTree_find e1 A = SOME ((e1lo, e1hi), err1) /\
    FloverMapTree_find e2 A = SOME ((e2lo, e2hi), err2) /\
    FloverMapTree_find (Binop Div e1 e2) A = SOME ((alo, ahi), e) /\
    FloverMapTree_find (Binop Div e1 e2) Gamma = SOME m /\
    abs (nR1 - nF1) <= err1 /\
    abs (nR2 - nF2) <= err2 ==>
    abs (nR - nF) <= e
Proof
  rpt strip_tac \\ simp[Once toREval_def]
  \\ fs[Once validErrorbound_def] \\ rveq
  \\ `0 <= err1`
       by (irule err_always_positive
           \\ qexistsl_tac [`A`, `dVars`, `e1`, `(e1lo,e1hi)`, `Gamma`]
           \\ fs[])
  \\ `0 <= err2`
       by (drule err_always_positive
           \\ rpt (disch_then drule)
           \\ fs[])
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `abs (nR1 / nR2 - nF1 / nF2) + computeError (nF1 / nF2) m`
  \\ conj_tac
  >- (irule div_abs_err_bounded \\ rpt conj_tac
      \\ rpt (find_exists_tac \\ fs[]))
  \\ irule REAL_LE_TRANS \\ find_exists_tac
  \\ conj_tac \\ fs[]
  \\ `contained nF1 (widenInterval (e1lo,e1hi) err1)`
        by (irule distance_gives_iv
            \\ qexists_tac `nR1` \\ conj_tac
            \\ simp[contained_def])
  \\ `contained nF2 (widenInterval (e2lo,e2hi) err2)`
       by (irule distance_gives_iv
           \\ qexists_tac `nR2` \\ conj_tac
           \\ simp[contained_def])
  \\ irule REAL_LE_ADD2 \\ conj_tac
  >- (irule divisionErrorBounded
     \\ fs[widenInterval_def])
  \\ qmatch_abbrev_tac `_ <= computeError (maxAbs iv) _`
  \\ PairCases_on `iv` \\ irule computeError_up
  \\ unabbrev_all_tac \\ fs[maxAbs_def]
  \\ irule maxAbs
  \\ assume_tac (REWRITE_RULE [contained_def] interval_division_valid)
  \\ fs[contained_def, widenInterval_def, noDivzero_def]
QED

Theorem validErrorboundCorrectFma:
  !(E1 E2:env) (A:analysisResult) (e1:real expr) (e2:real expr) (e3: real expr)
   (nR nR1 nR2 nR3 nF nF1 nF2 nF3:real) (e err1 err2 err3:real)
   (alo ahi e1lo e1hi e2lo e2hi e3lo e3hi :real) dVars m m1 m2 m3 Gamma.
     eval_Real E1 Gamma e1 nR1 /\
     eval_Real E1 Gamma e2 nR2 /\
     eval_Real E1 Gamma e3 nR3 /\
     eval_Real E1 Gamma (Fma e1 e2 e3) nR /\
     eval_Fin E2 Gamma e1 nF1 m1 /\
     eval_Fin E2 Gamma e2 nF2 m2 /\
     eval_Fin E2 Gamma e3 nF3 m3 /\
     eval_expr (updEnv 3 nF3 (updEnv 2 nF2 (updEnv 1 nF1 emptyEnv)))
        (updDefVars (Fma (Var 1) (Var 2) (Var 3)) m
          (updDefVars (Var 3) m3
            (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma)))))
              (Fma (Var 1) (Var 2) (Var 3)) nF m /\
     validErrorbound (Fma e1 e2 e3) Gamma A dVars /\
     (e1lo <= nR1 /\ nR1 <= e1hi) /\
     (e2lo <= nR2 /\ nR2 <= e2hi) /\
     (e3lo <= nR3 /\ nR3 <= e3hi) /\
     FloverMapTree_find e1 A = SOME ((e1lo, e1hi), err1) /\
     FloverMapTree_find e2 A = SOME ((e2lo, e2hi), err2) /\
     FloverMapTree_find e3 A = SOME ((e3lo, e3hi), err3) /\
     FloverMapTree_find (Fma e1 e2 e3) A = SOME ((alo, ahi), e) /\
     FloverMapTree_find (Fma e1 e2 e3) Gamma = SOME m /\
     abs (nR1 - nF1) <= err1 /\
     abs (nR2 - nF2) <= err2 /\
     abs (nR3 - nF3) <= err3 ==>
     abs (nR - nF) <= e
Proof
  fs [toREval_def]
  \\ rpt strip_tac \\ simp[Once toREval_def]
  \\ fs[Once validErrorbound_eq] \\ rveq
  \\ `0 <= err1`
       by (irule err_always_positive
           \\ rpt (asm_exists_tac  \\ fs[]))
  \\ `0 <= err2`
       by (irule err_always_positive
           \\ rpt (asm_exists_tac  \\ fs[]))
  \\ `0 <= err3`
       by (irule err_always_positive
           \\ rpt (asm_exists_tac  \\ fs[]))
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `abs ((nR1 * nR2 - nF1 * nF2) + (nR3 - nF3)) +
      computeError (nF1 * nF2 + nF3) m`
  \\ conj_tac
  >- (irule fma_abs_err_bounded \\ rpt conj_tac
      \\ rpt (find_exists_tac \\ fs[toREval_def]))
  \\ irule REAL_LE_TRANS \\ find_exists_tac
  \\ conj_tac \\ fs[]
  \\ irule REAL_LE_ADD2 \\ rpt conj_tac
  >- (irule triangle_trans \\ fs[REAL_ABS_TRIANGLE]
      \\ irule REAL_LE_ADD2 \\ fs[]
      \\ irule multiplicationErrorBounded \\ fs[])
  \\ `contained nF1 (widenInterval (e1lo,e1hi) err1)`
      by (irule distance_gives_iv
          \\ qexists_tac `nR1` \\ conj_tac
          \\ simp[contained_def, IVlo_def, IVhi_def])
  \\ `contained nF2 (widenInterval (e2lo,e2hi) err2)`
      by (irule distance_gives_iv
          \\ qexists_tac `nR2` \\ conj_tac
          \\ simp[contained_def, IVlo_def, IVhi_def])
  \\ `contained nF3 (widenInterval (e3lo,e3hi) err3)`
       by (irule distance_gives_iv
           \\ qexists_tac `nR3` \\ conj_tac
           \\ simp[contained_def, IVlo_def, IVhi_def])
  \\ `contained (nF1 * nF2)
        (multInterval (widenInterval (e1lo, e1hi) err1)
                      (widenInterval (e2lo, e2hi) err2))`
      by (irule
              (ONCE_REWRITE_RULE [validIntervalMult_def] interval_multiplication_valid)
          \\ conj_tac \\ simp[])
  \\ qmatch_abbrev_tac `_ <= computeError (maxAbs iv) _`
  \\ PairCases_on `iv` \\ irule computeError_up
  \\ unabbrev_all_tac \\ fs[maxAbs_def]
  \\ irule maxAbs
  \\ assume_tac (REWRITE_RULE [validIntervalAdd_def, contained_def] interval_addition_valid)
  \\ fs[contained_def, widenInterval_def, IVlo_def, IVhi_def, noDivzero_def]
QED

Theorem validErrorboundCorrectRounding:
  !(E1 E2:env) (A:analysisResult) (e:real expr)
               (nR nF nF1:real) (err err1:real) (alo ahi elo ehi:real) dVars m mEps Gamma.
    eval_Real E1 Gamma e nR /\
    eval_Fin E2 Gamma e nF1 m /\
    eval_expr (updEnv 1 nF1 emptyEnv)
              (updDefVars (Downcast mEps (Var 1)) mEps
               (updDefVars (Var 1) m (toRExpMap Gamma)))
              (Downcast mEps (Var 1)) nF mEps /\
    validErrorbound (Downcast mEps e) Gamma A dVars /\
    elo <= nR /\ nR <= ehi /\
    FloverMapTree_find e A = SOME ((elo, ehi), err1) /\
    FloverMapTree_find (Downcast mEps e) A = SOME ((alo, ahi), err) /\
    FloverMapTree_find (Downcast mEps e) Gamma = SOME mEps /\
    abs (nR - nF1) <= err1 ==>
    abs (nR - nF) <= err
Proof
  fs [toREval_def] \\ rpt strip_tac
  \\ fs[Once validErrorbound_eq] \\ rveq
  \\ irule REAL_LE_TRANS
  \\ qexists_tac `err1 + computeError nF1 mEps` \\ fs []
  \\ conj_tac
  >- (irule round_abs_err_bounded \\ fs[]
      \\ rpt (asm_exists_tac \\ fs[]))
  \\ irule REAL_LE_TRANS \\ find_exists_tac \\ fs[]
  \\ qmatch_abbrev_tac `_ <= computeError (maxAbs iv) _`
  \\ PairCases_on `iv` \\ irule computeError_up
  \\ unabbrev_all_tac \\ fs[maxAbs_def]
  \\ irule maxAbs
  \\ assume_tac (REWRITE_RULE [contained_def] distance_gives_iv)
  \\ fs[widenInterval_def]
  \\ res_tac
  \\ ntac 2 (first_x_assum (qspec_then `(elo, ehi)` assume_tac))
  \\ rpt (first_x_assum (destruct) \\ fs[])
QED

Theorem validErrorboundCorrectSqrt:
  ∀(E1 E2:env) (A:analysisResult) (e:real expr)
    (nR nR1 nF nF1:real) (err err1:real) (alo ahi elo ehi:real) dVars m m1 Gamma.
    eval_Real E1 Gamma e nR1 ∧
    eval_Fin E2 Gamma e nF1 m1 ∧
    eval_Real E1 Gamma (Unop Sqrt e) nR ∧
    eval_expr (updEnv 1 nF1 emptyEnv)
              (updDefVars (Unop Sqrt (Var 1)) m
               (updDefVars (Var 1) m1 (toRExpMap Gamma)))
              (Unop Sqrt (Var 1)) nF m /\
    validErrorbound (Unop Sqrt e) Gamma A dVars ∧
    elo <= nR1 ∧ nR1 <= ehi ∧
    0 < elo ∧
    FloverMapTree_find e A = SOME ((elo, ehi), err1) ∧
    FloverMapTree_find (Unop Sqrt e) A = SOME ((alo, ahi), err) ∧
    FloverMapTree_find (Unop Sqrt e) Gamma = SOME m ∧
    abs (nR1 - nF1) <= err1 ⇒
    abs (nR - nF) <= err
Proof
  fs [toREval_def] \\ rpt strip_tac
  \\ fs[Once validErrorbound_eq] \\ rveq
  \\ irule REAL_LE_TRANS
  \\ qexists_tac ‘abs (sqrt nR1 - sqrt nF1) + computeError (sqrt nF1) m’
  \\ conj_tac
  >- (
    drule sqrt_abs_err_bounded \\ rpt $ disch_then drule
    \\ disch_then $ qspecl_then [‘nR’, ‘nF’, ‘err1’, ‘m’] mp_tac
    \\ gs[toREval_def])
  \\ ‘contained nF1 (widenInterval (elo, ehi) err1)’
    by (irule distance_gives_iv \\ find_exists_tac \\ gs[contained_def])
  \\ rpt (
    qpat_x_assum `validate_newton_down _ _` $ mp_then Any mp_tac validate_newton_lb_valid
    \\ impl_tac
      >- (conj_tac
          >- (irule newton_method_pos \\ conj_tac \\ irule REAL_LE_MUL \\ gs[] \\ real_prove)
          \\ real_prove)
    \\ strip_tac)
  \\ ‘0 < ehi’
    by (
    irule REAL_LTE_TRANS \\ qexists_tac ‘elo’ \\ gs[]
    \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[])
  \\ ‘0 < SND (widenInterval (elo, ehi) err1)’
    by (
    irule REAL_LTE_TRANS \\ qexists_tac ‘FST (widenInterval (elo, ehi) err1)’ \\ gs[widenInterval_def]
    \\ REAL_ASM_ARITH_TAC)
  \\ rpt (
    qpat_x_assum `validate_newton_up _ _` $ mp_then Any mp_tac validate_newton_ub_valid
    \\ impl_tac
      >- (conj_tac
          >- (irule newton_method_pos \\ conj_tac \\ irule REAL_LE_MUL \\ gs[] \\ real_prove)
          \\ real_prove)
    \\ strip_tac)
  \\ irule REAL_LE_TRANS \\ once_rewrite_tac[CONJ_COMM] \\ asm_exists_tac \\ gs[]
  \\ irule REAL_LE_ADD2 \\ conj_tac
  (* Prove propagation error *)
  >- (
    irule sqrt_diff_ub_concrete \\ gs[widenInterval_def]
    \\ imp_res_tac err_always_positive \\ gs[PULL_EXISTS]
    \\ qexists_tac ‘ehi’ \\ gs[]
    \\ imp_res_tac distance_gives_iv
    \\ first_x_assum $ qspec_then ‘(elo, ehi)’ mp_tac
    \\ gs[contained_def, widenInterval_def])
  (* New error *)
  \\ irule computeError_up
  \\ irule contained_leq_maxAbs
  \\ gs[contained_def] \\ conj_tac \\ irule REAL_LE_TRANS
  >- (asm_exists_tac \\ gs[] \\ irule SQRT_MONO_LE \\ real_prove)
  \\ once_rewrite_tac[CONJ_COMM] \\ asm_exists_tac \\ gs[]
  \\ irule SQRT_MONO_LE \\ gs[] \\ REAL_ASM_ARITH_TAC
QED

(**
   Soundness theorem for the error bound validator.
   Proof is by induction on the expression e.
   Each case requires the application of one of the soundness lemmata proven before
 **)
Theorem validErrorbound_sound:
  ∀ (e:real expr) (E1 E2:env) (A:analysisResult) (nR err:real)
    (elo ehi:real) (fVars:num_set) dVars Gamma.
    validTypes e Gamma /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 /\
    ((domain (usedVars e)) DIFF (domain dVars)) SUBSET (domain fVars) /\
    eval_Real E1 Gamma e nR /\
    validErrorbound e Gamma A dVars /\
    validRanges e A E1 (toRTMap (toRExpMap Gamma)) /\
    FloverMapTree_find e A = SOME ((elo,ehi),err) ==>
    (?nF m.
      eval_Fin E2 Gamma e nF m) /\
    (! nF m.
      eval_Fin E2 Gamma e nF m ==>
      abs (nR - nF) <= err)
Proof
  Induct_on `e`
  \\ rpt gen_tac
  \\ rpt (disch_then assume_tac)
  >- (conj_tac
      >- (irule validErrorboundCorrectVariable_eval \\ fs[]
          \\ rpt (find_exists_tac \\ fs[]))
      \\ rpt strip_tac
      \\ irule validErrorboundCorrectVariable \\ fs[]
      \\ rpt (find_exists_tac \\ fs[]))
  >- (conj_tac \\ rpt strip_tac
      >- (irule validErrorboundCorrectConstant_eval
          \\ fs[])
      \\ rename1 `eval_Fin E2 Gamma (Const m v) nF mF`
      \\ irule validErrorboundCorrectConstant \\ fs[]
      \\ `m = mF` by (fs [Once eval_expr_cases_old]) \\ rveq
      \\ rpt (find_exists_tac \\ fs[])
      \\ IMP_RES_TAC validRanges_single \\ fs[]
      \\ `vR = nR` by (metis_tac [meps_0_deterministic])
      \\ rveq \\ fs[]
      \\ rpt (find_exists_tac \\ fs[]))
  >- (fs[] \\  rveq
      \\ qpat_x_assum `validErrorbound _ _ _ _` mp_tac
      \\ simp[Once validErrorbound_eq] \\ strip_tac
      \\ Cases_on `u` \\ fs[toREval_def] \\ rveq
      >- (
       rw_thm_asm `(domain _) DIFF _ SUBSET _` usedVars_def
       \\ inversion `eval_expr E1 _ _ _ _` eval_expr_cases \\ fs[]
       \\ `m' = REAL` by (irule toRTMap_eval_REAL \\ find_exists_tac \\ fs[])
       \\ PairCases_on `v4` \\ fs[] \\ rveq
       \\ rename1 `FloverMapTree_find e A = SOME ((e_lo, e_hi) , err)`
       \\ once_rewrite_tac [eval_expr_cases] \\ fs[]
       \\ first_x_assum
          (qspecl_then
           [`E1`, `E2`, `A`, `v1`, `err`, `e_lo`, `e_hi`, `fVars`,
            `dVars`, `Gamma`]
           destruct)
       >- (fs[Once validTypes_def, Once validRanges_def])
       \\ fs[Once validTypes_def, toRExpMap_def] \\ conj_tac \\ rpt strip_tac
       >- (qexistsl_tac [`me`, `nF`] \\ fs[]
           \\ `m' = me`
             by (irule validTypes_exec
                 \\ rpt (find_exists_tac \\ fs[toRExpMap_def]))
           \\ rveq \\ fs[])
       \\ fs[evalUnop_def]
       \\ once_rewrite_tac [real_sub]
       \\ rewrite_tac [GSYM REAL_NEG_ADD, ABS_NEG, GSYM real_sub]
       \\ first_x_assum drule
       \\ rpt (disch_then drule)
       \\ disch_then assume_tac \\ fs[]
       \\ first_x_assum irule \\ asm_exists_tac \\ fs[])
      \\ rw_thm_asm `(domain _) DIFF _ SUBSET _` usedVars_def
      \\ inversion `eval_expr E1 _ _ _ _` eval_expr_cases \\ fs[]
      \\ `m1 = REAL` by (irule toRTMap_eval_REAL \\ find_exists_tac \\ fs[])
      \\ PairCases_on `iv1` \\ fs[] \\ rveq
      \\ rename1 `FloverMapTree_find e A = SOME ((e_lo, e_hi) , err1)`
      \\ once_rewrite_tac [eval_expr_cases] \\ fs[]
      \\ first_x_assum
          (qspecl_then
           [`E1`, `E2`, `A`, `v1`, `err1`, `e_lo`, `e_hi`, `fVars`,
            `dVars`, `Gamma`]
           destruct)
       >- (fs[Once validTypes_def, Once validRanges_def])
      \\ qpat_x_assum `validRanges _ _ _ _` mp_tac
      \\ qpat_x_assum `validTypes _ _` mp_tac
      \\ simp[Once validRanges_def, Once validTypes_def]
      \\ rpt $ disch_then strip_assume_tac
      \\ imp_res_tac validRanges_single
      \\ imp_res_tac meps_0_deterministic \\ rveq
      \\ gs[] \\ rveq \\ gs[]
      \\ fs[toRExpMap_def] \\ conj_tac \\ rpt strip_tac
      >- (qexistsl_tac [`me`, `nF`, ‘0’] \\ fs[]
          \\ `m' = me`
            by (irule validTypes_exec
                \\ rpt (find_exists_tac \\ fs[toRExpMap_def]))
          \\ rveq \\ fs[] \\ conj_tac
          >- (irule mTypeToR_pos)
          \\ res_tac \\ first_x_assum $ mp_then Any mp_tac distance_gives_iv
          \\ gs[contained_def]
          \\ disch_then $ qspec_then ‘(e_lo, e_hi)’ mp_tac \\ gs[]
          \\ strip_tac \\ irule REAL_LTE_TRANS
          \\ qexists_tac ‘FST (widenInterval (e_lo, e_hi) err')’ \\ gs[])
      \\ rveq \\ res_tac
      \\ irule validErrorboundCorrectSqrt
      \\ qexistsl_tac [‘A’, ‘E1’, ‘E2’, ‘Gamma’, ‘ehi’, ‘elo’, ‘dVars’, ‘e’,
                       ‘e_hi’, ‘e_lo’, ‘err'’, ‘m’, ‘m1’, ‘v1'’, ‘v1’]
      \\ gs[toRExpMap_def] \\ rpt conj_tac
      >- (gs[perturb_def, toRExpMap_def, toREval_def]
          \\ ‘vR = evalUnop Sqrt v1’
             by (
            inversion `eval_expr E1 _ (Unop Sqrt _) _ _` eval_expr_cases \\ fs[]
            \\ Cases_on ‘m1'’ \\ gs[isCompat_def, perturb_def]
            \\ ‘v1'' = v1’ suffices_by gs[]
            \\ irule meps_0_deterministic
            \\ qexistsl_tac [‘E1’, ‘λ e. FloverMapTree_find e Gamma’, ‘e’]
            \\ gs[])
          \\ rveq \\ gs[])
      >- simp[Once validErrorbound_def]
      \\ irule Unop_sqrt' \\ fsrw_tac [SATISFY_ss] [updDefVars_def]
      \\ qexistsl_tac [‘delta'’, ‘m1’, ‘v1'’] \\ gs[]
      \\ simp[Once eval_expr_cases] \\ gs[updDefVars_def])
  >- (rename1 `Binop op e1 e2` \\ fs[]
      \\ qpat_x_assum `validErrorbound _ _ _ _` mp_tac
      \\ simp[Once validErrorbound_eq] \\ strip_tac
      \\ fs[toREval_def] \\ rveq
      \\ inversion `eval_expr E1 _ _ _ _` eval_expr_cases \\ fs[]
      \\ `m1 = REAL /\ m2 = REAL`
        by (conj_tac \\ irule toRTMap_eval_REAL \\ find_exists_tac \\ fs[])
      \\ rveq \\ fs[]
      \\ first_x_assum
           (qspecl_then
             [`E1`, `E2`, `A`, `v2`, `err2`, `FST ive2`, `SND ive2`,
              `fVars`, `dVars`, `Gamma`]
             destruct)
      \\ fs[]
      >- (fs[DIFF_DEF, SUBSET_DEF, Once validTypes_def, Once validRanges_def]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
      \\ first_x_assum
           (qspecl_then
             [`E1`, `E2`, `A`, `v1`, `err1`, `FST ive1`, `SND ive1`,
              `fVars`, `dVars`, `Gamma`]
           destruct)
      \\ fs[]
      >- (fs[DIFF_DEF, SUBSET_DEF, Once validTypes_def, Once validRanges_def]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
      \\ fs[Once validRanges_def, Once validTypes_def]
      \\ IMP_RES_TAC validRanges_single
      \\ IMP_RES_TAC meps_0_deterministic \\ rveq
      \\ fs[] \\ rveq \\ fs[]
      \\ rename1 `FloverMapTree_find e1 A = SOME (iv1, err1)`
      \\ rename1 `FloverMapTree_find e2 A = SOME (iv2, err2)`
      \\ IMP_RES_TAC validTypes_exec \\ rveq
      \\ rename1 `eval_expr E2 _ e1 nF1 m1`
      \\ rename1 `eval_expr E2 _ e2 nF2 m2`
      \\ `contained nF1 (widenInterval iv1 err1)`
           by (irule distance_gives_iv
               \\ qexists_tac `v1` \\ fs[contained_def]
               \\ fs[]
               \\ first_x_assum irule
               \\ qexists_tac `m1` \\ fs[])
      \\ `contained nF2 (widenInterval iv2 err2)`
           by (irule distance_gives_iv
               \\ qexists_tac `v2` \\ fs [contained_def]
               \\ first_x_assum irule
               \\ qexists_tac `m2` \\ fs[])
      \\ `op = Div ==> nF2 <> 0`
           by (strip_tac
               \\ rveq
               \\ fs[widenInterval_def, contained_def]
               \\ CCONTR_TAC \\ fs[] \\ rveq
               \\ fs[noDivzero_def] \\ TRY REAL_ASM_ARITH_TAC
               \\ `0 < 0:real` suffices_by (fs[])
               \\ TRY (irule REAL_LET_TRANS \\ qexists_tac `SND iv2 + err2`
                       \\ fs[] \\ FAIL_TAC "")
               \\ irule REAL_LTE_TRANS \\ qexists_tac `FST iv2 - err2` \\ fs[])
      \\ conj_tac \\ rpt strip_tac
      >- (qexistsl_tac [`perturb (evalBinop op nF1 nF2) m 0`, `m`]
          \\ irule Binop_dist'
          \\ qexistsl_tac [`0`, `m`, `m1`, `m2`, `nF1`, `nF2`]
          \\ fs[ABS_0, mTypeToR_pos, toRExpMap_def])
      \\ ‘m' = m’
        by (first_x_assum irule \\ simp[Once validTypes_def]
            \\ conj_tac
            >- (rpt strip_tac \\ first_x_assum irule
                \\ rpt (find_exists_tac \\ fs[]))
            \\ find_exists_tac \\ fs[])
      \\ rveq
      \\ `perturb (evalBinop op nR1 nR2) REAL delta = evalBinop op nR1 nR2`
           by (irule delta_0_deterministic \\ fs[mTypeToR_def])
      \\ fs[]
      \\ qpat_assum `eval_expr E2 _ (Binop op e1 e2) _ _` assume_tac
      \\ inversion `eval_expr E2 _ (Binop op e1 e2) _ _` eval_expr_cases
      \\ rename1 `abs delta2 <= mTypeToR mF _`
      \\ rveq
      \\ `m2' = m2`
        by (irule validTypes_exec
            \\ qexistsl_tac [`E2`, `Gamma`, `e2`, `v2'`] \\ fs[])
      \\ `m1' = m1`
        by (irule validTypes_exec
            \\ qexistsl_tac [`E2`, `Gamma`, `e1`, `v1'`] \\ fs[])
      \\ rveq
      \\ `eval_expr (updEnv 2 v2' (updEnv 1 v1' emptyEnv))
            (updDefVars (Binop op (Var 1) (Var 2)) mF
              (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma))))
           (Binop op (Var 1) (Var 2)) (perturb (evalBinop op v1' v2') mF delta2) mF`
             by (irule binary_unfolding \\ fs[] \\ rpt conj_tac
                 \\ rpt (find_exists_tac \\ fs[]))
      \\ Cases_on `op` \\ rveq
      THENL [irule validErrorboundCorrectAddition,
             irule validErrorboundCorrectSubtraction,
             irule validErrorboundCorrectMult,
             irule validErrorboundCorrectDiv]
      \\ fs [GSYM noDivzero_def]
      \\ find_exists_tac \\ fs[]
      \\ qexistsl_tac [`A`, `E1`, `E2`, `ehi`, `elo`, `dVars`, `SND iv1`,
                       `FST iv1`, `SND iv2`, `FST iv2`, `err1`, `err2`, `m1`,
                       `m2`, `v1'`, `v2'`, `v1`, `v2`]
      \\ fs[toREval_def]
      \\ rpt conj_tac \\ TRY (first_x_assum irule \\ asm_exists_tac \\ fs[])
      \\ TRY (irule Binop_dist'
              \\ qexistsl_tac [`0`, `REAL`, `REAL`, `REAL`, `v1`, `v2`]
              \\ fs[perturb_def, mTypeToR_pos])
      \\ simp[Once validErrorbound_eq])
  >- (rename1 `Fma e1 e2 e3` \\ fs[]
      \\ qpat_x_assum ‘validErrorbound _ _ _ _’ mp_tac \\ simp[Once validErrorbound_eq]
      \\ strip_tac
      \\ rveq \\ fs[toREval_def]
      \\ inversion `eval_expr E1 _ _ _ _` eval_expr_cases
      \\ `m1 = REAL /\ m2 = REAL /\ m3 = REAL`
          by (rpt conj_tac \\ irule toRTMap_eval_REAL \\ find_exists_tac \\ fs[])
      \\ rveq
      \\ first_x_assum
           (qspecl_then
                [`E1`, `E2`, `A`, `v3`, `err3`, `FST ive3`, `SND ive3`,
                 `fVars`, `dVars`, `Gamma`]
              destruct)
      \\ fs[]
      >- (fs[DIFF_DEF, SUBSET_DEF, Once validTypes_def, Once validRanges_def]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
      \\ first_x_assum
           (qspecl_then
                [`E1`, `E2`, `A`, `v2`, `err2`, `FST ive2`, `SND ive2`,
                 `fVars`, `dVars`, `Gamma`]
              destruct)
      \\ fs[]
      >- (fs[DIFF_DEF, SUBSET_DEF, Once validTypes_def, Once validRanges_def]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
      \\ first_x_assum
           (qspecl_then
                [`E1`, `E2`, `A`, `v1`, `err1`, `FST ive1`, `SND ive1`,
                 `fVars`, `dVars`, `Gamma`]
              destruct)
      \\ fs[]
      >- (fs[DIFF_DEF, SUBSET_DEF, Once validTypes_def, Once validRanges_def]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
      \\ fs[Once validTypes_def, Once validRanges_def]
      \\ IMP_RES_TAC validTypes_exec \\ rveq
      \\ rename1 `eval_expr E2 _ e3 nF3 m3`
      \\ rename1 `eval_expr E2 _ e2 nF2 m2`
      \\ rename1 `eval_expr E2 _ e1 nF1 m1`
      \\ IMP_RES_TAC validRanges_single
      \\ IMP_RES_TAC meps_0_deterministic \\ rveq
      \\ rename1 `eval_expr E1 _ (toREval e3) nR3 _`
      \\ rename1 `eval_expr E1 _ (toREval e2) nR2 _`
      \\ rename1 `eval_expr E1 _ (toREval e1) nR1 _`
      \\ fs[] \\ rveq \\ fs[] \\ rpt (qpat_x_assum `T` kall_tac)
      \\ rename1 `FloverMapTree_find e1 A = SOME (iv1, err1)`
      \\ rename1 `FloverMapTree_find e2 A = SOME (iv2, err2)`
      \\ rename1 `FloverMapTree_find e3 A = SOME (iv3, err3)`
      \\ `contained nF1 (widenInterval iv1 err1)`
           by (irule distance_gives_iv
               \\ qexists_tac `nR1` \\ fs[contained_def]
               \\ first_x_assum irule
               \\ qexists_tac `m1` \\ fs[])
      \\ `contained nF2 (widenInterval iv2 err2)`
           by (irule distance_gives_iv
               \\ qexists_tac `nR2` \\ fs [contained_def, IVlo_def, IVhi_def]
               \\ first_x_assum irule
               \\ qexists_tac `m2` \\ fs[])
      \\ `contained nF3 (widenInterval iv3 err3)`
           by (irule distance_gives_iv
               \\ qexists_tac `nR3` \\ fs [contained_def, IVlo_def, IVhi_def]
               \\ first_x_assum irule
               \\ qexists_tac `m3` \\ fs[])
      \\ conj_tac
      >- (qexistsl_tac [`perturb (evalFma nF1 nF2 nF3) m 0`, `m`]
          \\ irule Fma_dist'
          \\ qexistsl_tac [`0`, `m`, `m1`, `m2`, `m3`, `nF1`, `nF2`, `nF3`]
          \\ fs[mTypeToR_pos,toRExpMap_def])
      \\ rpt strip_tac
      \\ `perturb (evalFma nR1 nR2 nR3) REAL delta = evalFma nR1 nR2 nR3`
           by (irule delta_0_deterministic \\ fs[mTypeToR_def])
      \\ fs[]
      \\ qpat_assum `eval_expr E2 _ (Fma e1 e2 e3) _ _` assume_tac
      \\ inversion `eval_expr E2 _ (Fma e1 e2 e3) _ _` eval_expr_cases
      \\ `m1' = m1`
        by (irule validTypes_exec
            \\ qexistsl_tac [`E2`, `Gamma`, `e1`, `v1`] \\ fs[])
      \\ `m2' = m2`
        by (irule validTypes_exec
            \\ qexistsl_tac [`E2`, `Gamma`, `e2`, `v2`] \\ fs[])
      \\ `m3' = m3`
        by (irule validTypes_exec
            \\ qexistsl_tac [`E2`, `Gamma`, `e3`, `v3`] \\ fs[])
      \\ rveq
      \\ rename1 `abs delta2 <= mTypeToR mF _`
      \\ `mF = m`
        by (irule validTypes_exec
            \\ qexistsl_tac [`E2`, `Gamma`, `Fma e1 e2 e3`,
                             `perturb (evalFma v1 v2 v3) mF delta2`]
            \\ simp[Once validTypes_def]
            \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ rveq
      \\ `eval_expr (updEnv 3 v3 (updEnv 2 v2 (updEnv 1 v1 emptyEnv)))
            (updDefVars (Fma (Var 1) (Var 2) (Var 3)) m
              (updDefVars (Var 3) m3
                (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 (toRExpMap Gamma)))))
           (Fma (Var 1) (Var 2) (Var 3)) (perturb (evalFma v1 v2 v3) m delta2) m`
             by (irule fma_unfolding \\ conj_tac \\ fs[]
                 \\ rpt (find_exists_tac \\ fs[]))
      \\ irule validErrorboundCorrectFma
      \\ find_exists_tac \\ fs[]
      \\ qexistsl_tac [`A`, `E1`, `E2`, `ehi`, `elo`, `dVars`, `SND iv1`,
                       `FST iv1`, `SND iv2`, `FST iv2`, `SND iv3`, `FST iv3`,
                       `err1`, `err2`, `err3`, `m1`, `m2`, `m3`, `v1`, `v2`,
                       `v3`, `nR1`, `nR2`, `nR3`]
      \\ fs[]
      \\ rpt conj_tac \\ TRY (first_x_assum irule \\ asm_exists_tac \\ fs[])
      >- (simp [Once toREval_def]
          \\ irule Fma_dist'
          \\ qexistsl_tac [`0`, `REAL`, `REAL`, `REAL`, `REAL`, `nR1`, `nR2`, `nR3`]
          \\ fs[perturb_def, mTypeToR_pos])
      \\ once_rewrite_tac [validErrorbound_def] \\ fs[widenInterval_def])
  >- (rename1 `Downcast m1 e1` \\ fs[]
      \\ qpat_x_assum ‘validErrorbound _ _ _ _’ mp_tac \\ simp[Once validErrorbound_eq]
      \\ strip_tac
      \\ rveq \\ fs[toREval_def]
      \\ inversion `eval_expr E1 _ _ _ _` eval_expr_cases \\ fs[]
      \\ first_x_assum
           (qspecl_then
             [`E1`, `E2`, `A`, `nR`, `err1`, `FST ive1`, `SND ive1`,
              `fVars`, `dVars`, `Gamma`]
             destruct)
      \\ fs[]
      >- (fs[DIFF_DEF, SUBSET_DEF, Once validTypes_def, Once validRanges_def]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ once_rewrite_tac [usedVars_def] \\ fs[domain_union])
      \\ fs[Once validRanges_def, Once validTypes_def]
      \\ IMP_RES_TAC validTypes_exec \\ rveq
      \\ IMP_RES_TAC validRanges_single
      \\ IMP_RES_TAC meps_0_deterministic \\ rveq
      \\ rename1 `eval_expr E1 _ (toREval e1) nR1 _`
      \\ fs[] \\ rveq \\ fs[] \\ rpt (qpat_x_assum `T` kall_tac)
      \\ rename1 `FloverMapTree_find e1 A = SOME (iv1, err1)`
      \\ `contained nF (widenInterval iv1 err1)`
           by (irule distance_gives_iv
               \\ qexists_tac `nR1` \\ fs[contained_def]
               \\ first_x_assum irule
               \\ qexists_tac `m'` \\ fs[])
      \\ conj_tac \\ rpt strip_tac
      >- (qexistsl_tac [`perturb nF m 0`, `m`]
          \\ irule Downcast_dist' \\ fs[toRExpMap_def]
          \\ qexistsl_tac [`0`, `m'`, `nF`]
          \\ fs[mTypeToR_pos, isMorePrecise_morePrecise])
      \\ inversion `eval_expr E2 _ (Downcast m1 e1) _ _` eval_expr_cases
      \\ rveq
      \\ irule validErrorboundCorrectRounding
      \\ find_exists_tac \\ fs[]
      \\ qexistsl_tac [`A`, `E1`, `E2`, `ehi`, `elo`, `dVars`, `SND iv1`,
                       `FST iv1`, `err1`, `m1'`, `v1`]
      \\ fs[]
      \\ rpt conj_tac
      >- (first_x_assum irule \\ asm_exists_tac \\ fs[])
      >- (once_rewrite_tac [validErrorbound_def] \\ fs[widenInterval_def])
      \\ irule Downcast_dist' \\ fs[updDefVars_def]
      \\ find_exists_tac \\ fs[]
      \\ qexistsl_tac [`delta`, `v1`]
      \\ fs[]
      \\ irule Var_load
      \\ fs[updDefVars_def, updEnv_def])
QED

Theorem validErrorboundCmd_gives_eval:
  !(f:real cmd) (A:analysisResult) (E1 E2:env)
    (outVars fVars dVars:num_set) (vR elo ehi err:real)
    (m:mType) Gamma.
    validTypesCmd f Gamma /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 /\
    ssa f (union fVars dVars) outVars /\
    ((domain (freeVars f)) DIFF (domain dVars)) SUBSET (domain fVars) /\
    bstep (toREvalCmd f) E1 (toRTMap (toRExpMap Gamma)) vR REAL /\
    validErrorboundCmd f Gamma A dVars /\
    validRangesCmd f A E1 (toRTMap (toRExpMap Gamma)) /\
    FloverMapTree_find (getRetExp f) A = SOME ((elo,ehi),err) ==>
    ?vF m.
    bstep f E2 (toRExpMap Gamma) vF m
Proof
  Induct_on `f`
  \\ simp[Once validErrorboundCmd_eq, Once toREvalCmd_def]
  \\ rpt strip_tac
  >- (inversion `bstep _ _ _ _ _` bstep_cases
      \\ inversion `ssa _ _ _` ssa_cases
      \\ fs[Once validTypesCmd_def, Once validRangesCmd_def, getRetExp_def]
      \\ `validRangesCmd f A (updEnv n v E1) (toRTMap (toRExpMap Gamma))`
        by (first_x_assum irule \\ fs[])
      \\ IMP_RES_TAC validRangesCmd_single
      \\ fs[] \\ rveq \\ fs[]
      \\ qspecl_then
          [`e`, `E1`, `E2`, `A`, `v`, `err_x`, `FST iv_e`, `SND iv_e`, `fVars`,
           `dVars`, `Gamma`] destruct validErrorbound_sound
      \\ fs[]
      >- (rw_thm_asm `domain (freeVars _) DIFF _ SUBSET _` freeVars_def
          \\ fs[]
          \\ fs[SUBSET_DEF, domain_union]
          \\ rpt strip_tac \\ first_x_assum irule \\ fs[]
          \\ CCONTR_TAC \\ fs[] \\ rveq
          \\ `n IN domain fVars \/ n IN domain dVars` by (first_x_assum irule \\ fs[])
          )
      \\ rename1 `eval_expr E2 (toRExpMap Gamma) e vF mF`
      \\ `approxEnv (updEnv n v E1) (toRExpMap Gamma) A fVars
                    (insert n () dVars) (updEnv n vF E2)`
           by (irule approxEnvUpdBound \\ fs[lookup_NONE_domain]
               \\ conj_tac
               >- (qexists_tac `m` \\ fs[toRExpMap_def])
               \\ first_x_assum irule \\ find_exists_tac \\ fs[])
      \\ `m = mF`
        by (irule (GSYM validTypes_exec)
            \\ qexistsl_tac [`E2`, `Gamma`, `e`, `vF`] \\ fs[])
      \\ fs[] \\ rveq \\ fs[]
      \\ `?vF_res m_res.
            bstep f (updEnv n vF E2) (toRExpMap Gamma) vF_res m_res`
           by (first_x_assum irule
               \\ rpt conj_tac
               >- (fs[getRetExp_def] \\ res_tac
                   \\ IMP_RES_TAC validTypesCmd_single
                   \\ fs[] \\ rveq \\ fs[])
               >- (fs[Once validTypesCmd_def])
               \\ qexistsl_tac [`A`, `updEnv n v E1`, `insert n () dVars`,
                                `ehi`, `elo`, `err`, `fVars`, `outVars`, `vR''`]
               \\ fs[getRetExp_def]
               \\ rpt conj_tac
               >- (find_exists_tac \\ fs[])
               >- (fs[Once validRangesCmd_def])
               >- (fs[DIFF_DEF, domain_insert, SUBSET_DEF]
                   \\ rpt strip_tac \\ first_x_assum irule
                   \\ fs[Once freeVars_def]
                   \\ simp[Once freeVars_def, domain_union])
               >- (irule ssa_equal_set
                   \\ qexists_tac `insert n () (union fVars dVars)`
                   \\ conj_tac \\ TRY (fs[] \\ FAIL_TAC "")
                   \\ rewrite_tac [domain_union, domain_insert]
                   \\ rewrite_tac [UNION_DEF, INSERT_DEF]
                   \\ fs[EXTENSION]
                   \\ rpt strip_tac
                   \\ metis_tac[])
               \\ fs[Once toREvalCmd_def])
           \\ qexistsl_tac [`vF_res`, `m_res`]
           \\ fs[bstep_cases]
           \\ qexists_tac `vF` \\ rveq \\ fs[toRExpMap_def])
  >- (fs[getRetExp_def]
      \\ inversion `ssa _ _ _` ssa_cases
      \\ inversion `bstep _ _ _ _ _` bstep_cases
      \\ once_rewrite_tac [bstep_cases]
      \\ `(?vF m. eval_expr E2 (toRExpMap Gamma) e vF m) /\
          (!vF m. eval_expr E2 (toRExpMap Gamma) e vF m ==> abs (vR - vF) <= err)`
           by (irule (REWRITE_RULE [eval_Fin_def] validErrorbound_sound)
               \\ fs[validTypesCmd_def, validRangesCmd_def, freeVars_def]
               \\ rpt (find_exists_tac \\ fs[]))
      \\ qexistsl_tac [`vF`, `m`] \\ fs[])
QED

Theorem validErrorboundCmd_sound:
  !(f:real cmd) (A:analysisResult) (E1 E2:env)
    (outVars fVars dVars:num_set) (vR vF elo ehi err:real) (m:mType) Gamma.
    validTypesCmd f Gamma /\
    approxEnv E1 (toRExpMap Gamma) A fVars dVars E2 /\
    ssa f (union fVars dVars) outVars /\
    ((domain (freeVars f)) DIFF (domain dVars)) SUBSET (domain fVars) /\
    bstep (toREvalCmd f) E1 (toRTMap (toRExpMap Gamma)) vR REAL /\
    bstep f E2 (toRExpMap Gamma) vF m /\
    validErrorboundCmd f Gamma A dVars /\
    validRangesCmd f A E1 (toRTMap (toRExpMap Gamma)) /\
    FloverMapTree_find (getRetExp f) A = SOME ((elo,ehi),err) ==>
    abs (vR - vF) <= err
Proof
  Induct_on `f`
  \\ simp[Once validErrorboundCmd_eq, Once toREvalCmd_def] \\ rpt strip_tac
  >- (inversion `bstep _ _ _ _ REAL` bstep_cases \\ rveq
      \\ inversion `bstep _ _ _ _ m'` bstep_cases \\ rveq
      \\ inversion `ssa _ _ _` ssa_cases \\ rveq
      \\ rename1 `eval_expr _ _ _ vr REAL`
      \\ rename1 `eval_expr _ _ _ vf m`
      \\ first_x_assum irule
      \\ qexistsl_tac [`A`, `updEnv n vr E1`, `updEnv n vf E2`, `Gamma`,
                       `insert n () dVars`, `ehi`, `elo`,`fVars`, `m'`,
                       `outVars`]
      \\ fs [Once getRetExp_def, Once validTypesCmd_def, Once validRangesCmd_def]
      \\ rpt conj_tac
      >- (fs[DIFF_DEF, domain_insert, SUBSET_DEF]
          \\ rpt strip_tac \\ first_x_assum irule
          \\ fs[Once freeVars_def]
          \\ simp[Once freeVars_def, domain_union])
      >- (irule ssa_equal_set
          \\ qexists_tac `insert n () (union fVars dVars)` \\ fs [ domain_union]
          \\ once_rewrite_tac [UNION_COMM]
          \\ fs [INSERT_UNION_EQ])
      >- (irule approxEnvUpdBound \\ rpt conj_tac
          \\ fs[]
          >- (Cases_on `lookup n (union fVars dVars)` \\ fs [domain_lookup])
          \\ qspecl_then
               [`e`, `E1`, `E2`, `A`, `vr`, `err_x`, `FST (iv_e)`,
                `SND (iv_e)`, `fVars`, `dVars`, `Gamma`]
               destruct validErrorbound_sound
          \\ fs [Once freeVars_def, domain_union, SUBSET_DEF]
          >- (rpt strip_tac \\ first_x_assum irule \\ fs[]
              \\ CCONTR_TAC \\ fs[] \\ rveq
              \\ `n IN domain fVars \/ n IN domain dVars` by metis_tac[])
         \\ first_x_assum irule
         \\ asm_exists_tac \\ fs[]))
  >- (inversion `bstep _ _ _ _ REAL` bstep_cases \\ rveq
      \\ inversion `bstep _ _ _ _ m` bstep_cases \\ rveq
      \\ qspecl_then
           [`e`, `E1`, `E2`, `A`, `vR`, `err`, `elo`, `ehi`, `fVars`,
            `dVars`, `Gamma`]
           destruct validErrorbound_sound
      \\ fs[freeVars_def, getRetExp_def, Once validTypesCmd_def, Once validRangesCmd_def]
      \\ first_x_assum irule \\ fs[]
      \\ find_exists_tac \\ fs[])
QED

val _ = export_theory();
