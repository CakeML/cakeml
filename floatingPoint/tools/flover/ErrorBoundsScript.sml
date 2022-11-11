(**
Proofs of general bounds on the error of arithmetic Expressions.
This shortens soundness proofs later.
Bounds are exprlained in section 5, Deriving Computable Error Bounds
**)
open simpLib realTheory realLib RealArith
open AbbrevsTheory ExpressionsTheory ExpressionSemanticsTheory RealSimpsTheory
     FloverTactics MachineTypeTheory ExpressionAbbrevsTheory EnvironmentsTheory;
open preambleFloVer;

val _ = new_theory "ErrorBounds";

val _ = Parse.hide "delta"; (* so that it can be used as a variable *)

Overload abs[local] = “realax$abs”

val triangle_tac =
  irule triangle_trans \\ rpt conj_tac \\ TRY (fs[REAL_ABS_TRIANGLE] \\ NO_TAC);

Theorem const_abs_err_bounded:
  ∀ (n:real) (nR:real) (nF:real) (E1 E2:env) (m:mType) Gamma.
    eval_expr E1 (toRTMap Gamma) (Const REAL n) nR REAL ∧
    eval_expr E2 Gamma (Const m n) nF m ⇒
    abs (nR - nF) <= computeError n m
Proof
  rpt strip_tac
  \\ fs[eval_expr_cases, mTypeToR_def, perturb_def] \\ rveq
  \\ Cases_on `m` \\ fs[Excl "RMUL_LEQNORM", perturb_def, computeError_def]
  \\ TRY COND_CASES_TAC \\ fs[Excl "RMUL_LEQNORM", Rabs_err_simpl, REAL_ABS_MUL, mTypeToR_def]
  \\ TRY (REAL_ASM_ARITH_TAC)
  \\ irule REAL_LE_RMUL_IMP \\ rewrite_tac[GSYM REAL_INV_1OVER] \\ fs[REAL_ABS_POS]
QED

val float_add_tac =
  rewrite_tac [GSYM REAL_ADD_ASSOC, computeError_def]
  \\ COND_CASES_TAC \\ simp[]
  >- (
    ‘e1R + (e2R + - (e1F + (e2F + deltaF))) = (e1R - e1F) + ((e2R - e2F) - deltaF)’
    by REAL_ASM_ARITH_TAC
    \\ pop_assum (rewrite_tac o single)
    \\ triangle_tac
    \\ irule REAL_LE_ADD2 \\ conj_tac \\ fs[]
    \\ ‘e2R - e2F - deltaF = e2R - e2F + - deltaF’ by REAL_ASM_ARITH_TAC
    \\ pop_assum (rewrite_tac o single)
    \\ triangle_tac
    \\ irule REAL_LE_ADD2 \\ conj_tac \\ fs[])
  \\ `e1R + (e2R + -((e1F + e2F) * (1 + deltaF))) =
      (e1R + - e1F) + ((e2R + - e2F) + - (e1F + e2F) * deltaF)`
        by REAL_ASM_ARITH_TAC
  \\ pop_assum (fn thm => once_rewrite_tac [thm])
  \\ triangle_tac
  \\ irule REAL_LE_ADD2 \\ conj_tac
  >- fs[GSYM real_sub]
  \\ triangle_tac
  \\ irule REAL_LE_ADD2 \\ conj_tac
  >- fs[GSYM real_sub]
  \\ once_rewrite_tac [REAL_ABS_MUL]
  \\ simp[computeError_def]
  \\ metis_tac [REAL_ABS_POS, REAL_LE_LMUL_IMP, REAL_MUL_COMM];

Theorem add_abs_err_bounded:
  !(e1:real expr) (e1R:real) (e1F:real) (e2:real expr) (e2R:real) (e2F:real)
     (err1:real) (err2:real) (vR:real) (vF:real) (E1 E2:env) (m m1 m2:mType)
     (Gamma: real expr -> mType option).
       eval_expr E1 (toRTMap Gamma) (toREval e1) e1R REAL /\
       eval_expr E2 Gamma e1 e1F m1 /\
       eval_expr E1 (toRTMap Gamma) (toREval e2) e2R REAL /\
       eval_expr E2 Gamma e2 e2F m2 /\
       eval_expr E1 (toRTMap Gamma) (toREval (Binop Plus e1 e2)) vR REAL /\
       eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
        (updDefVars (Binop Plus (Var 1) (Var 2)) m
          (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma)))
         (Binop Plus (Var 1) (Var 2)) vF m /\
       abs (e1R - e1F) <= err1 /\
       abs (e2R - e2F) <= err2 ==>
       abs (vR - vF) <= err1 + err2 + (computeError (e1F + e2F) m)
Proof
  rpt strip_tac \\ fs[toREval_def]
  \\ inversion `eval_expr E1 _ (Binop Plus _ _) _ _` eval_expr_cases
  \\ rename1 `vR = perturb (evalBinop Plus v1R v2R) REAL deltaR`
  \\ rename1 `isJoin m1R m2R REAL`
  \\ inversion `eval_expr _ _ (Binop Plus (Var 1) (Var 2)) _ _` eval_expr_cases
  \\ rename1 `vF = perturb (evalBinop Plus v1F v2F) mF deltaF`
  \\ `(m1R = REAL) /\ (m2R = REAL)`
       by (conj_tac \\ irule toRTMap_eval_REAL \\ qexistsl_tac [`E1`, `Gamma`]
           THENL [qexistsl_tac [`e1`, `v1R`], qexistsl_tac [`e2`, `v2R`]]
           \\ fs[])
  \\ `v1R = e1R` by metis_tac [meps_0_deterministic]
  \\ `v2R = e2R` by metis_tac [meps_0_deterministic]
  \\ rveq \\ fs [perturb_def]
  \\ rpt (inversion `eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv)) _ _ _ _`
                    eval_expr_cases)
  \\ fs [updEnv_def] \\ rveq
  \\ once_rewrite_tac[real_sub]
  \\ Cases_on `mF` \\ fs[perturb_def, evalBinop_def]
  >- (`e1R + e2R + -(e1F + e2F) = (e1R + - e1F) + ((e2R + - e2F))`
           by REAL_ASM_ARITH_TAC
      \\ simp[computeError_def]
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `abs (e1R + - e1F) + abs (e2R + - e2F)`
      \\ fs[REAL_ABS_TRIANGLE]
      \\ REAL_ASM_ARITH_TAC)
  >- float_add_tac
  >- (float_add_tac)
  >- (float_add_tac)
  \\ simp[computeError_def]
  \\ `e1R + e2R + - (e1F + e2F + deltaF) = (e1R + - e1F) + (e2R + - e2F + - deltaF)`
      by (REAL_ASM_ARITH_TAC)
  \\ simp[]
  \\ triangle_tac
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ irule REAL_LE_ADD2  \\ fs[real_sub]
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ triangle_tac
  \\ irule REAL_LE_ADD2 \\ fs[real_sub]
  \\ REAL_ASM_ARITH_TAC
QED

val float_sub_tac =
  rewrite_tac [GSYM REAL_ADD_ASSOC, computeError_def]
  \\ COND_CASES_TAC \\ simp[]
  >- (‘e1R + (-e2R + -(e1F + (-e2F + deltaF))) = (e1R - e1F) + (-(e2R - e2F) + - deltaF)’
      by REAL_ASM_ARITH_TAC
      \\ pop_assum (rewrite_tac o single)
      \\ triangle_tac \\ irule REAL_LE_ADD2 \\ conj_tac
      >- fs[GSYM real_sub]
      \\ triangle_tac \\ irule REAL_LE_ADD2 \\ conj_tac
      >- fs[GSYM real_sub]
      \\ fs[ABS_NEG, mTypeToR_def, real_sub])
  \\ `e1R + (-e2R + -((e1F + -e2F) * (1 + deltaF))) =
    (e1R + - e1F) + ((- e2R + e2F) + - (e1F + - e2F) * deltaF)`
      by REAL_ASM_ARITH_TAC
   \\ pop_assum (once_rewrite_tac o single)
   \\ triangle_tac
   \\ irule REAL_LE_ADD2 \\ conj_tac
   >- fs[GSYM real_sub]
   \\ triangle_tac
   \\ irule REAL_LE_ADD2 \\ conj_tac
   >- REAL_ASM_ARITH_TAC
   \\ rewrite_tac [REAL_ABS_MUL, ABS_NEG]
   \\ irule REAL_LE_LMUL_IMP \\ fs[mTypeToR_def, real_sub];

Theorem subtract_abs_err_bounded:
  !(e1:real expr) (e1R:real) (e1F:real) (e2:real expr) (e2R:real) (e2F:real)
     (err1:real) (err2:real) (vR:real) (vF:real) (E1 E2:env) (m m1 m2:mType)
     (Gamma: real expr -> mType option).
       eval_expr E1 (toRTMap Gamma) (toREval e1) e1R REAL /\
       eval_expr E2 Gamma e1 e1F m1 /\
       eval_expr E1 (toRTMap Gamma) (toREval e2) e2R REAL /\
       eval_expr E2 Gamma e2 e2F m2 /\
       eval_expr E1 (toRTMap Gamma) (toREval (Binop Sub e1 e2)) vR REAL /\
       eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
        (updDefVars (Binop Sub (Var 1) (Var 2)) m
          (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma)))
        (Binop Sub (Var 1) (Var 2)) vF m /\
       abs (e1R - e1F) <= err1 /\
       abs (e2R - e2F) <= err2 ==>
       abs (vR - vF) <= err1 + err2 + computeError (e1F - e2F) m
Proof
  rpt strip_tac \\ fs[toREval_def]
  \\ inversion `eval_expr E1 _ (Binop Sub _ _) _ _` eval_expr_cases
  \\ rename1 `vR = perturb (evalBinop Sub v1R v2R) REAL deltaR`
  \\ rename1 `isJoin m1R m2R REAL`
  \\ inversion `eval_expr _ _ (Binop Sub (Var 1) (Var 2)) _ _` eval_expr_cases
  \\ rename1 `vF = perturb (evalBinop Sub v1F v2F) mF deltaF`
  \\ `(m1R = REAL) /\ (m2R = REAL)`
       by (conj_tac \\ irule toRTMap_eval_REAL \\ qexistsl_tac [`E1`, `Gamma`]
           THENL [qexistsl_tac [`e1`, `v1R`], qexistsl_tac [`e2`, `v2R`]]
           \\ fs[])
  \\ `v1R = e1R` by metis_tac[meps_0_deterministic]
  \\ `v2R = e2R` by metis_tac[meps_0_deterministic]
  \\ rveq \\ fs[perturb_def]
  \\ rpt (inversion `eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv)) _ _ _ _`
      eval_expr_cases)
  \\ fs [updEnv_def] \\ rveq
  \\ Cases_on `mF`
  \\ fs[perturb_def, evalBinop_def, computeError_def]
  \\ rewrite_tac[real_sub]
  >- (`e1R - e2R + - (e1F - e2F) = e1R + - e1F + (- e2R + e2F)`
        by REAL_ASM_ARITH_TAC
      \\ simp[]
      \\ irule REAL_LE_TRANS
      \\ qexists_tac `abs (e1R + - e1F) + abs (-e2R + e2F)`
      \\ fs[REAL_ABS_TRIANGLE]
      \\ REAL_ASM_ARITH_TAC)
  >- (float_sub_tac)
  >- (float_sub_tac)
  >- (float_sub_tac)
  \\ `e1R + - e2R + - (e1F + - e2F + deltaF) = (e1R + - e1F) + (- e2R + e2F + - deltaF)`
      by (REAL_ASM_ARITH_TAC)
  \\ simp[]
  \\ triangle_tac
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ irule REAL_LE_ADD2  \\ fs[real_sub]
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ triangle_tac
  \\ irule REAL_LE_ADD2 \\ fs[real_sub]
  \\ REAL_ASM_ARITH_TAC
QED

val float_mul_tac =
  COND_CASES_TAC \\ simp[]
  >- (‘e1R * e2R + - (e1F * e2F + deltaF) = (e1R * e2R + - (e1F * e2F)) + - deltaF’
      by REAL_ASM_ARITH_TAC
      \\ pop_assum (rewrite_tac o single)
      \\ triangle_tac \\ irule REAL_LE_ADD2 \\ fs[computeError_def])
  \\ `e1R * e2R + -(e1F * e2F * (1 + deltaF)) =
    (e1R * e2R + - (e1F * e2F)) + - (e1F * e2F * deltaF)`
      by REAL_ASM_ARITH_TAC
  \\ pop_assum (once_rewrite_tac o single)
  \\ triangle_tac \\ irule REAL_LE_ADD2 \\ conj_tac >- fs[]
  \\ rewrite_tac [ABS_NEG, computeError_def, REAL_ABS_MUL]
  \\ fs[]
  \\ ‘abs deltaF * abs e1F * abs e2F = abs e1F * abs e2F * abs deltaF’
    by fs[]
  \\ pop_assum (rewrite_tac o single)
  \\ metis_tac [REAL_LE_LMUL_IMP, REAL_ABS_MUL, REAL_ABS_POS];

Theorem mult_abs_err_bounded:
  ∀ (e1:real expr) (e1R:real) (e1F:real) (e2:real expr) (e2R:real) (e2F:real)
    (err1:real) (err2:real) (vR:real) (vF:real) (E1 E2 :env) (m m1 m2:mType)
    (Gamma: real expr -> mType option).
      eval_expr E1 (toRTMap Gamma) (toREval e1) e1R REAL /\
      eval_expr E2 Gamma e1 e1F m1 /\
      eval_expr E1 (toRTMap Gamma) (toREval e2) e2R REAL /\
      eval_expr E2 Gamma e2 e2F m2 /\
      eval_expr E1 (toRTMap Gamma) (toREval (Binop Mult e1 e2)) vR REAL /\
      eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
       (updDefVars (Binop Mult (Var 1) (Var 2)) m
         (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma)))
       (Binop Mult (Var 1) (Var 2)) vF m /\
      abs (e1R - e1F) <= err1 /\
      abs (e2R - e2F) <= err2 ==>
      abs (vR - vF) <= abs (e1R * e2R - e1F * e2F) + computeError (e1F * e2F) m
Proof
  rpt strip_tac \\ fs[toREval_def]
  \\ inversion `eval_expr E1 _ (Binop Mult _ _) _ _` eval_expr_cases
  \\ rename1 `vR = perturb (evalBinop Mult v1R v2R) REAL deltaR`
  \\ rename1 `isJoin m1R m2R REAL`
  \\ inversion `eval_expr _ _ (Binop Mult (Var 1) (Var 2)) _ _` eval_expr_cases
  \\ rename1 `vF = perturb (evalBinop Mult v1F v2F) mF deltaF`
  \\ `(m1R = REAL) /\ (m2R = REAL)`
       by (conj_tac \\ irule toRTMap_eval_REAL \\ qexistsl_tac [`E1`, `Gamma`]
           THENL [qexistsl_tac [`e1`, `v1R`], qexistsl_tac [`e2`, `v2R`]]
           \\ fs[])
  \\ `v1R = e1R` by metis_tac[meps_0_deterministic]
  \\ `v2R = e2R` by metis_tac[meps_0_deterministic]
  \\ rveq \\ fs[perturb_def, evalBinop_def]
  \\ rpt (inversion `eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv)) _ _ _ _`
      eval_expr_cases)
  \\ fs [updEnv_def] \\ rveq
  \\ rewrite_tac [real_sub]
  \\ Cases_on `mF` \\ fs[perturb_def]
  >- (rewrite_tac [REAL_LE_ADDR] \\ fs[computeError_def])
  >- (float_mul_tac)
  >- (float_mul_tac)
  >- (float_mul_tac)
  \\ `e1R * e2R + - (e1F * e2F + deltaF) =
      (e1R * e2R + - (e1F * e2F)) + - deltaF`
      by REAL_ASM_ARITH_TAC
  \\ simp[]
  \\ triangle_tac
  \\ fs[ABS_NEG, computeError_def]
QED

Theorem REAL_LE_MUL_SWAP:
  ∀ (a b c:real).
    a * b ≤ a * c ⇒ b * a ≤ a * c
Proof
 rpt strip_tac \\ fs[]
QED

val float_div_tac =
  COND_CASES_TAC \\ simp[]
  >- (‘e1R / e2R + - (e1F / e2F + deltaF) = (e1R / e2R + - (e1F / e2F)) + - deltaF’
      by REAL_ASM_ARITH_TAC
      \\ pop_assum (rewrite_tac o single)
      \\ triangle_tac \\ irule REAL_LE_ADD2 \\ fs[computeError_def])
  \\ `e1R / e2R + -(e1F * inv e2F * (1 + deltaF)) =
    (e1R / e2R + - (e1F * inv e2F)) + - (e1F * inv e2F * deltaF)`
      by REAL_ASM_ARITH_TAC
  \\ pop_assum (once_rewrite_tac o single)
  \\ triangle_tac \\ irule REAL_LE_ADD2 \\ conj_tac >- fs[real_div]
  \\ fs[real_div, ABS_NEG, computeError_def, REAL_ABS_MUL]
  \\ ‘abs deltaF * abs e1F = abs e1F * abs deltaF’
    by fs[]
  \\ pop_assum (rewrite_tac o single)
  \\ metis_tac [REAL_LE_LMUL_IMP, REAL_ABS_MUL, REAL_ABS_POS];

Theorem div_abs_err_bounded:
  !(e1:real expr) (e1R:real) (e1F:real) (e2:real expr) (e2R:real) (e2F:real)
     (err1:real) (err2:real) (vR:real) (vF:real) (E1 E2 :env) (m m1 m2:mType)
     (Gamma: real expr -> mType option).
       eval_expr E1 (toRTMap Gamma) (toREval e1) e1R REAL /\
       eval_expr E2 Gamma e1 e1F m1 /\
       eval_expr E1 (toRTMap Gamma) (toREval e2) e2R REAL /\
       eval_expr E2 Gamma e2 e2F m2 /\
       eval_expr E1 (toRTMap Gamma) (toREval (Binop Div e1 e2)) vR REAL /\
       eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv))
        (updDefVars (Binop Div (Var 1) (Var 2)) m
          (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma)))
        (Binop Div (Var 1) (Var 2)) vF m /\
       abs (e1R - e1F) <= err1 /\
       abs (e2R - e2F) <= err2 ==>
       abs (vR - vF) <= abs (e1R / e2R - e1F / e2F) + computeError (e1F / e2F) m
Proof
  rpt strip_tac \\ fs[toREval_def]
  \\ inversion `eval_expr E1 _ (Binop Div _ _) _ _` eval_expr_cases
  \\ rename1 `vR = perturb (evalBinop Div v1R v2R) REAL deltaR`
  \\ rename1 `isJoin m1R m2R REAL`
  \\ inversion `eval_expr _ _ (Binop Div (Var 1) (Var 2)) _ _` eval_expr_cases
  \\ rename1 `vF = perturb (evalBinop Div v1F v2F) mF deltaF`
  \\ `(m1R = REAL) /\ (m2R = REAL)`
       by (conj_tac \\ irule toRTMap_eval_REAL \\ qexistsl_tac [`E1`, `Gamma`]
           THENL [qexistsl_tac [`e1`, `v1R`], qexistsl_tac [`e2`, `v2R`]]
           \\ fs[])
  \\ `v1R = e1R` by metis_tac[meps_0_deterministic]
  \\ `v2R = e2R` by metis_tac[meps_0_deterministic]
  \\ rveq \\ fs[perturb_def, evalBinop_def]
  \\ rpt (inversion `eval_expr (updEnv 2 e2F (updEnv 1 e1F emptyEnv)) _ _ _ _`
      eval_expr_cases)
  \\ fs [updEnv_def] \\ rveq
  \\ rewrite_tac [real_sub]
  \\ Cases_on `mF` \\ fs[perturb_def]
  >- (rewrite_tac [REAL_LE_ADDR] \\ fs[computeError_def])
  >- (float_div_tac)
  >- (float_div_tac)
  >- (float_div_tac)
  \\ `e1R / e2R + - (e1F / e2F + deltaF) =
      (e1R / e2R + - (e1F / e2F)) + - deltaF`
      by REAL_ASM_ARITH_TAC
  \\ simp[]
  \\ triangle_tac
  \\ fs[ABS_NEG, computeError_def]
QED

val float_fma_tac =
  COND_CASES_TAC \\ simp[]
>- (‘e1R * e2R + e3R + - (e1F * e2F + e3F + deltaF) =
      (e1R * e2R + - (e1F * e2F)) + (e3R + - e3F) + - deltaF’ by REAL_ASM_ARITH_TAC
    \\ pop_assum (rewrite_tac o single)
    \\ triangle_tac \\ irule REAL_LE_ADD2 \\ fs[])
  \\ `e1R * e2R + e3R + -((1 + deltaF) * (e1F * e2F + e3F)) =
    (e1R * e2R + e3R + -(e1F * e2F + e3F)) + (- (e1F * e2F + e3F) * deltaF)`
      by REAL_ASM_ARITH_TAC
  \\ simp[]
  \\ triangle_tac
  \\ irule REAL_LE_ADD2 \\ conj_tac
  \\ TRY (REAL_ASM_ARITH_TAC)
  \\ rewrite_tac[REAL_ABS_MUL, ABS_NEG]
  \\ metis_tac [REAL_LE_LMUL_IMP, REAL_MUL_COMM, REAL_ABS_POS, REAL_LE_MUL_SWAP];

Theorem fma_abs_err_bounded:
  !(e1:real expr) (e1R:real) (e1F:real) (e2:real expr) (e2R:real) (e2F:real)
     (e3:real expr) (e3R:real) (e3F:real) (err1:real) (err2:real) (err3:real)
     (vR:real) (vF:real) (E1 E2 :env) (m m1 m2 m3:mType)
     (Gamma: real expr -> mType option).
       eval_expr E1 (toRTMap Gamma) (toREval e1) e1R REAL /\
       eval_expr E2 Gamma e1 e1F m1 /\
       eval_expr E1 (toRTMap Gamma) (toREval e2) e2R REAL /\
       eval_expr E2 Gamma e2 e2F m2 /\
       eval_expr E1 (toRTMap Gamma) (toREval e3) e3R REAL /\
       eval_expr E2 Gamma e3 e3F m3 /\
       eval_expr E1 (toRTMap Gamma) (toREval (Fma e1 e2 e3)) vR REAL /\
       eval_expr (updEnv 3 e3F (updEnv 2 e2F (updEnv 1 e1F emptyEnv)))
        (updDefVars (Fma (Var 1) (Var 2) (Var 3)) m
          (updDefVars (Var 3) m3
          (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma))))
        (Fma (Var 1) (Var 2) (Var 3)) vF m /\
       abs (e1R - e1F) <= err1 /\
       abs (e2R - e2F) <= err2 /\
       abs (e3R - e3F) <= err3 ==>
       abs (vR - vF) <=
        abs ((e1R * e2R - e1F * e2F) + (e3R - e3F)) +
        computeError (e1F * e2F + e3F) m
Proof
  rpt strip_tac \\ fs[toREval_def]
  \\ inversion `eval_expr E1 _ (Fma _ _ _) _ _` eval_expr_cases
  \\ rename1 `vR = perturb (evalFma v1R v2R v3R) REAL deltaR`
  \\ rename1 `isJoin3 m1R m2R m3R REAL`
  \\ inversion `eval_expr _ _ (Fma (Var 1) (Var 2) (Var 3)) _ _` eval_expr_cases
  \\ rename1 `vF = perturb (evalFma v1F v2F v3F) mF deltaF`
  \\ `(m1R = REAL) /\ (m2R = REAL) /\ (m3R = REAL)`
       by (rpt conj_tac \\ irule toRTMap_eval_REAL \\ qexistsl_tac [`E1`, `Gamma`]
           THENL [qexistsl_tac [`e1`, `v1R`],
                  qexistsl_tac [`e2`, `v2R`],
                  qexistsl_tac [`e3`, `v3R`]]
           \\ fs[])
  \\ `v1R = e1R` by metis_tac[meps_0_deterministic]
  \\ `v2R = e2R` by metis_tac[meps_0_deterministic]
  \\ `v3R = e3R` by metis_tac[meps_0_deterministic]
  \\ rveq \\ fs[evalFma_def, evalBinop_def]
  \\ rpt (inversion `eval_expr
            (updEnv 3 e3F (updEnv 2 e2F (updEnv 1 e1F emptyEnv))) _ _ _ _`
            eval_expr_cases)
  \\ fs [updEnv_def] \\ rveq
  \\ Cases_on `mF`
  \\ fs[computeError_def, perturb_def]
  \\ rewrite_tac[real_sub]
  >- (`e1R * e2R + e3R + - (e1F * e2F + e3F) =
        (e1R * e2R + - (e1F * e2F) + (e3R + - e3F))`
        by REAL_ASM_ARITH_TAC
      \\ simp[])
  >- (float_fma_tac)
  >- (float_fma_tac)
  >- (float_fma_tac)
  \\ `e1R * e2R + e3R + -(e1F * e2F + e3F + deltaF) =
      (e1R * e2R + e3R + - (e1F * e2F + e3F)) + - deltaF`
      by REAL_ASM_ARITH_TAC
  \\ simp[]
  \\ triangle_tac
  \\ irule REAL_LE_ADD2
  \\ REAL_ASM_ARITH_TAC
QED

Theorem round_abs_err_bounded:
  !(e:real expr) (nR:real) (nF1:real) (nF:real) (E1:env) (E2:env) (err:real)
     (m1:mType) (m:mType) (Gamma: real expr -> mType option).
       eval_expr E1 (toRTMap Gamma) (toREval e) nR REAL /\
       eval_expr E2 Gamma e nF1 m /\
       eval_expr (updEnv 1 nF1 emptyEnv)
            (updDefVars (Downcast m1 (Var 1)) m1
              (updDefVars (Var 1) m Gamma))
            (Downcast m1 (Var 1)) nF m1 /\
       abs (nR - nF1) <= err ==>
       abs (nR - nF) <= err + computeError nF1 m1
Proof
  rpt strip_tac
  \\ `nR - nF = (nR - nF1) + (nF1 - nF)` by REAL_ASM_ARITH_TAC
  \\ fs []
  \\ triangle_tac
  \\ irule REAL_LE_ADD2 \\ fs[]
  \\ inversion `eval_expr (updEnv _ _ _) _ _ _ _` eval_expr_cases
  \\ inversion `eval_expr (updEnv _ _ _) _ _ _ _` eval_expr_cases
  \\ fs [updEnv_def] \\ rveq \\ fs[]
  \\ Cases_on `m1` \\ fs[perturb_def, computeError_def]
  \\ once_rewrite_tac [REAL_LDISTRIB]
  \\ simp[real_sub, REAL_NEG_ADD, REAL_ADD_ASSOC, ABS_NEG, ABS_MUL]
  \\ COND_CASES_TAC \\ fs[REAL_NEG_ADD, REAL_ADD_ASSOC]
  \\ ‘delta * nF1 = nF1 * delta’ by fs[] \\ pop_assum (rewrite_tac o single)
  \\ rewrite_tac [ABS_MUL] \\ irule REAL_LE_LMUL_IMP \\ fs[]
QED

Theorem sqrt_abs_err_bounded:
  !(e:real expr) (nR:real) nR1 (nF1:real) (nF:real) (E1:env) (E2:env) (err:real)
     (m1 m:mType) (Gamma: real expr -> mType option).
       eval_expr E1 (toRTMap Gamma) (toREval e) nR1 REAL /\
       eval_expr E2 Gamma e nF1 m1 /\
       eval_expr E1 (toRTMap Gamma) (toREval (Unop Sqrt e)) nR REAL /\
       eval_expr (updEnv 1 nF1 emptyEnv)
            (updDefVars (Unop Sqrt (Var 1)) m
              (updDefVars (Var 1) m1 Gamma))
            (Unop Sqrt (Var 1)) nF m /\
       abs (nR1 - nF1) <= err ⇒
       abs (nR - nF) <= abs (sqrt nR1 - sqrt nF1) + computeError (sqrt nF1) m
Proof
  rpt strip_tac
  \\ inversion `eval_expr (updEnv _ _ _) _ _ _ _` eval_expr_cases \\ gs[]
  \\ inversion `eval_expr (updEnv _ _ _) _ _ _ _` eval_expr_cases \\ gs[]
  \\ rveq \\ gs[toREval_def, updDefVars_def] \\ rveq
  \\ inversion `eval_expr _ _ (Unop Sqrt _) _ _` eval_expr_cases \\ gs[]
  \\ rveq \\ gs[]
  \\ ‘m1' = REAL’ by (Cases_on ‘m1'’ \\ gs[isCompat_def])
  \\ rveq \\ gs[perturb_def]
  \\ ‘v1 = nR1’ by (imp_res_tac meps_0_deterministic \\ gs[])
  \\ rveq
  \\ Cases_on ‘m’ \\ gs[perturb_def, evalUnop_def, computeError_pos, real_sub]
  \\ TRY (COND_CASES_TAC \\ gs[])
  \\ rewrite_tac [REAL_NEG_ADD, REAL_ADD_ASSOC, REAL_ADD_LDISTRIB]
  \\ triangle_tac \\ gs[computeError_def, REAL_ABS_MUL]
  \\ irule REAL_LE_TRANS THENL [
    qexists_tac ‘mTypeToR M16 (sqrt nF1) * abs (sqrt nF1)’,
    qexists_tac ‘mTypeToR M32 (sqrt nF1) * abs (sqrt nF1)’,
    qexists_tac ‘mTypeToR M64 (sqrt nF1) * abs (sqrt nF1)’]
  \\ conj_tac
  \\ TRY (irule REAL_LE_RMUL_IMP \\ gs[])
  \\ gs[REAL_MUL_COMM, mTypeToR_def]
QED

Theorem nonzerop_EQ1_I'[simp]:
  0 < r ⇒ (nonzerop r = 1)
Proof
  rw[nonzerop_def]
QED

Theorem err_prop_inversion_pos:
  ∀ (nF:real) (nR:real) (err:real) (elo:real) (ehi:real).
    0 < elo - err  ∧ 0 < elo ∧
    abs (nR - nF) ≤ err ∧
    elo ≤ nR ∧ nR ≤ ehi ∧
    elo - err ≤ nF ∧ nF ≤ ehi + err ∧
    0 ≤ err ⇒
    abs (inv nR - inv nF) ≤ err * inv ((elo - err) * (elo - err))
Proof
  rpt strip_tac
  \\ ‘nR ≠ 0’ by REAL_ASM_ARITH_TAC
  \\ ‘-nF ≠ 0’ by REAL_ASM_ARITH_TAC
  \\ ‘inv nR - inv nF = - ((nR - nF) / (nR * nF))’
     by (gs[real_div, real_sub] \\ rewrite_tac[realTheory.REAL_LDISTRIB, REAL_NEG_ADD]
         \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
         \\ gs[REAL_MUL_LINV] \\ REAL_ASM_ARITH_TAC)
  \\ pop_assum $ gs o single
  \\ gs[real_div, Once REAL_ABS_MUL]
  \\ irule REAL_LE_TRANS \\ qexists_tac ‘abs (inv nF * inv nR) * err’
  \\ conj_tac  \\ gs[] \\ irule REAL_LE_LMUL_IMP \\ gs[]
  \\ ‘abs (inv nF * inv nR) = inv (abs (nF * nR))’ by gs[GSYM REAL_INV_MUL, ABS_INV]
  \\ pop_assum $ rewrite_tac o single
  \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ rewrite_tac [POW_2] \\ rpt conj_tac
  >- gs[]
  >- (irule REAL_LT_MUL \\ gs[])
  \\ rewrite_tac [ABS_MUL]
  \\ irule REAL_LE_MUL2 \\ gs[]
  \\ rpt conj_tac
  >- (irule REAL_LE_TRANS \\ qexists_tac ‘nF’ \\ gs[ABS_LE])
  >- (irule REAL_LE_TRANS \\ qexists_tac ‘elo’ \\ conj_tac \\ REAL_ASM_ARITH_TAC)
  \\ REAL_ASM_ARITH_TAC
QED

Theorem err_prop_inversion_neg:
  !(nF:real) (nR:real) (err:real) (elo:real) (ehi:real).
      ehi + err < 0  /\ ehi < 0 /\
      abs (nR - nF) <= err /\
      elo <= nR /\
      nR <= ehi /\
      elo - err <= nF /\
      nF <= ehi + err /\
      0 <= err ==>
      abs (inv nR - inv nF) <= err * inv ((ehi + err) * (ehi + err))
Proof
  rpt strip_tac
  \\ ‘0 < (-ehi) + -err’ by REAL_ASM_ARITH_TAC
  \\ qspecl_then [‘-nF’, ‘-nR’, ‘err’, ‘-ehi’, ‘-elo’] mp_tac err_prop_inversion_pos
  \\ impl_tac
  >- (
    rpt conj_tac \\ TRY (gs[real_sub] \\ NO_TAC)
    >- (gs[real_sub] \\ REAL_ASM_ARITH_TAC)
    \\ REAL_ASM_ARITH_TAC)
  \\ strip_tac
  \\ ‘nR ≠ 0 ∧ nF ≠ 0’ by REAL_ASM_ARITH_TAC
  \\ ‘abs (inv nR - inv nF) = abs (inv (-nR) - inv (- nF))’
     by (gs[GSYM REAL_NEG_INV, real_sub] \\ REAL_ASM_ARITH_TAC)
  \\ pop_assum $ rewrite_tac o single
  \\ irule REAL_LE_TRANS \\ asm_exists_tac \\ gs[]
  \\ irule REAL_LE_LMUL_IMP \\ gs[]
  \\ irule REAL_INV_LE_ANTIMONO_IMPR \\ rpt conj_tac
  >- (rewrite_tac[REAL_POW_POS] \\ DISJ2_TAC \\ DISJ1_TAC \\ gs[real_sub])
  >- (rewrite_tac[REAL_POW_POS] \\ DISJ2_TAC \\ DISJ2_TAC \\ gs[])
  \\ ‘-ehi - err = -1 * (ehi + err)’ by REAL_ASM_ARITH_TAC
  \\ pop_assum $ rewrite_tac o single
  \\ rewrite_tac [POW_MUL] \\ gs[POW_MINUS1]
QED

val _  = export_theory();
