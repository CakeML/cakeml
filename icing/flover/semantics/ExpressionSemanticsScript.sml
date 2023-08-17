(**
  Formalization of the base expression language for the flover framework
 **)
open realTheory realLib sptreeTheory;
open AbbrevsTheory MachineTypeTheory ExpressionsTheory;
open ExpressionAbbrevsTheory;
open preambleFloVer;

val _ = new_theory "ExpressionSemantics";

Overload abs = “realax$abs”

(**
  Define a perturbation function to ease writing of basic definitions
**)
Definition perturb_def:
  (* The Real-type has no error *)
  perturb (rVal:real) (REAL) (delta:real) = rVal /\
  (* Fixed-point numbers have an absolute error *)
  perturb rVal (F w f s) delta = rVal + delta /\
  (* Floating-point numbers have a relative error in the normal range, and an
     absolute error in the subnormal range *)
  perturb rVal m delta = if (denormal rVal m)
                         then rVal + delta
                         else rVal * (1 + delta)
End

(**
Define exprression evaluation relation parametric by an "error" epsilon.
The result value exprresses float computations according to the IEEE standard,
using a perturbation of the real valued computation by (1 + delta), where
|delta| <= machine epsilon.
**)
Inductive eval_expr:
  (!E Gamma m x v.
     Gamma (Var x) = SOME m /\
     E x = SOME v ==>
     eval_expr E Gamma (Var x) v m) /\
  (!E Gamma m n delta.
      abs delta <= (mTypeToR m) n ==>
     eval_expr E Gamma (Const m n) (perturb n m delta) m) /\
  (!E Gamma m mN f1 v1.
     Gamma (Unop Neg f1) = SOME mN /\
     isCompat m mN /\
     eval_expr E Gamma f1 v1 m ==>
     eval_expr E Gamma (Unop Neg f1) (evalUnop Neg v1) mN) /\
  (!E Gamma m m1 f1 v1 delta.
     Gamma (Unop Inv f1) = SOME m /\
     isCompat m1 m /\
     abs delta <= (mTypeToR m) (evalUnop Inv v1) /\
     eval_expr E Gamma f1 v1 m1 /\
     (v1 <> 0) ==>
     eval_expr E Gamma (Unop Inv f1) (perturb (evalUnop Inv v1) m delta) m) /\
  (!E Gamma m m1 f1 v1 delta.
     Gamma (Unop Sqrt f1) = SOME m /\
     isCompat m1 m /\
     abs delta <= (mTypeToR m) (evalUnop Sqrt v1) /\
     eval_expr E Gamma f1 v1 m1 /\
     (* leq would be fine here, but IEEE semantics are currently broken, thus we need lt *)
     (0 < v1) ==>
     eval_expr E Gamma (Unop Sqrt f1) (perturb (evalUnop Sqrt v1) m delta) m) /\
  (!E Gamma m m1 f1 v1 delta.
     Gamma (Downcast m f1) = SOME m /\
     isMorePrecise m1 m /\
     abs delta <= (mTypeToR m) v1 /\
     eval_expr E Gamma f1 v1 m1 ==>
     eval_expr E Gamma (Downcast m f1) (perturb v1 m delta) m) /\
  (!E Gamma m1 m2 m op f1 f2 v1 v2 delta.
     Gamma (Binop op f1 f2) = SOME m /\
     isJoin m1 m2 m /\
     abs delta <= (mTypeToR m) (evalBinop op v1 v2) /\
     eval_expr E Gamma f1 v1 m1 /\
     eval_expr E Gamma f2 v2 m2 /\
     ((op = Div) ==> (v2 <> 0)) ==>
     eval_expr E Gamma (Binop op f1 f2) (perturb (evalBinop op v1 v2) m delta) m) /\
  (!E Gamma m1 m2 m3 m f1 f2 f3 v1 v2 v3 delta.
     Gamma (Fma f1 f2 f3) = SOME m /\
     isJoin3 m1 m2 m3 m /\
     abs delta <= (mTypeToR m) (evalFma v1 v2 v3) /\
     eval_expr E Gamma f1 v1 m1 /\
     eval_expr E Gamma f2 v2 m2 /\
     eval_expr E Gamma f3 v3 m3 ==>
     eval_expr E Gamma (Fma f1 f2 f3) (perturb (evalFma v1 v2 v3) m delta) m)
End

Theorem eval_expr_cases_old = eval_expr_cases

(**
  Generate a better case lemma
**)
Theorem eval_expr_cases =
  map (GEN_ALL o SIMP_CONV (srw_ss()) [Once eval_expr_cases])
    [``eval_expr E Gamma (Var v) res m``,
     ``eval_expr E Gamma (Const m1 n) res m2``,
     ``eval_expr E Gamma (Unop u e) res m``,
     ``eval_expr E Gamma (Binop n e1 e2) res m``,
     ``eval_expr E Gamma (Fma e1 e2 e3) res m``,
     ``eval_expr E Gamma (Downcast m1 e1) res m2``] |> LIST_CONJ

val [Var_load, Const_dist, Unop_neg, Unop_inv, Unop_sqrt, Downcast_dist, Binop_dist, Fma_dist] =
  CONJ_LIST 8 eval_expr_rules;

Theorem Var_load = Var_load
Theorem Const_dist = Const_dist
Theorem Unop_neg = Unop_neg
Theorem Unop_inv = Unop_inv
Theorem Binop_dist = Binop_dist
Theorem Fma_dist = Fma_dist
Theorem Downcast_dist = Downcast_dist

(**
  Show some simpler (more general) rule lemmata
**)
Theorem Const_dist':
  ∀ m n delta v m' E Gamma.
    abs delta <= mTypeToR m n /\
    v = perturb n m delta /\
    m' = m ==>
    eval_expr E Gamma (Const m n) v m'
Proof
  fs [Const_dist]
QED

Theorem Unop_neg':
  ∀ m f1 v1 v m' mN E Gamma.
    eval_expr E Gamma f1 v1 m /\
    v = evalUnop Neg v1 /\
    Gamma (Unop Neg f1) = SOME mN /\
    isCompat m mN /\
    m' = mN ==>
    eval_expr E Gamma (Unop Neg f1) v m'
Proof
  rpt strip_tac \\ rveq \\ irule Unop_neg \\ fs[]
  \\ asm_exists_tac \\ fs[]
QED

Theorem Unop_inv':
  ∀ m f1 v1 delta v mN m1 E Gamma fBits.
    (abs delta) <= mTypeToR m (evalUnop Inv v1) /\
    eval_expr E Gamma f1 v1 m1 /\
    (v1 <> 0) /\
    v = perturb (evalUnop Inv v1) m delta /\
    Gamma (Unop Inv f1) = SOME mN /\
    isCompat m1 mN /\
    m = mN ==>
    eval_expr E Gamma (Unop Inv f1) v m
Proof
  rpt strip_tac \\ rveq \\ irule Unop_inv \\ fs[]
  \\ asm_exists_tac \\ gs[]
QED

Theorem Unop_sqrt':
  ∀ m f1 v1 delta v m1 mN E Gamma fBits.
    (abs delta) <= mTypeToR m (evalUnop Sqrt v1) /\
    eval_expr E Gamma f1 v1 m1 /\
    (0 < v1) /\
    v = perturb (evalUnop Sqrt v1) mN delta /\
    Gamma (Unop Sqrt f1) = SOME mN /\
    isCompat m1 mN /\
    m = mN ==>
    eval_expr E Gamma (Unop Sqrt f1) v m
Proof
  rpt strip_tac \\ rveq \\ irule Unop_sqrt \\ fs[]
  \\ asm_exists_tac \\ gs[]
QED

Theorem Downcast_dist':
  ∀ m m1 f1 v1 delta v m' E Gamma fBits.
    isMorePrecise m1 m /\
    (abs delta) <= mTypeToR m v1 /\
    eval_expr E Gamma f1 v1 m1 /\
    v = perturb v1 m delta /\
    Gamma (Downcast m f1) = SOME m /\
    m' = m ==>
    eval_expr E Gamma (Downcast m f1) v m'
Proof
  rpt strip_tac
  \\ rw []
  \\ irule Downcast_dist
  \\ fs[] \\ qexists_tac `m1` \\ fs[]
QED

Theorem Binop_dist':
  ∀ m1 m2 op f1 f2 v1 v2 delta v m m' E Gamma fBit.
    abs delta <= mTypeToR m' (evalBinop op v1 v2) /\
    eval_expr E Gamma f1 v1 m1 /\
    eval_expr E Gamma f2 v2 m2 /\
    ((op = Div) ==> (v2 <> 0)) /\
    v = perturb (evalBinop op v1 v2) m' delta /\
    Gamma (Binop op f1 f2) = SOME m /\
    isJoin m1 m2 m /\
    m = m' ==>
    eval_expr E Gamma (Binop op f1 f2) v m'
Proof
  rpt strip_tac \\ rveq
  \\ irule Binop_dist \\ fs[]
  \\ asm_exists_tac \\ fs[]
QED

Theorem Fma_dist':
  ∀ m1 m2 m3 f1 f2 f3 v1 v2 v3 delta v m m' E Gamma fBit.
    abs delta <= mTypeToR m' (evalFma v1 v2 v3) /\
    eval_expr E Gamma f1 v1 m1 /\
    eval_expr E Gamma f2 v2 m2 /\
    eval_expr E Gamma f3 v3 m3 /\
    v = perturb (evalFma v1 v2 v3) m' delta /\
    Gamma (Fma f1 f2 f3) = SOME m /\
    isJoin3 m1 m2 m3 m /\
    m' = m ==>
    eval_expr E Gamma (Fma f1 f2 f3) v m'
Proof
  rpt strip_tac \\ rveq
  \\ irule Fma_dist \\ fs[]
  \\ asm_exists_tac \\ fs[]
QED

Theorem Gamma_det:
  ∀ e1 e2 E1 E2 Gamma v1 v2 m1 m2.
    eval_expr E1 Gamma e1 v1 m1 /\
    e1 = e2 /\
    eval_expr E2 Gamma e2 v2 m2 ==>
    m1 = m2
Proof
  Induct_on `e1` \\ rpt strip_tac \\ fs[eval_expr_cases]
  \\ rveq \\ fs[eval_expr_cases]
  \\ fs[]
QED

Theorem toRTMap_eval_REAL:
  ∀ e v E Gamma m.
    eval_expr E (toRTMap Gamma) (toREval e) v m ==> m = REAL
Proof
  Induct_on `e` \\ rpt strip_tac \\ fs[toREval_def, Once eval_expr_cases]
  \\ fs[toRTMap_def, option_case_eq]
  \\ res_tac \\ fs[]
QED

(**
  If |delta| <= 0 then perturb v delta is exactly v.
**)
Theorem delta_0_deterministic:
  ∀ (v:real) (m:mType) (delta:real).
    abs delta <= 0 ==> perturb v m delta = v
Proof
  Cases_on `m` \\
  fs [perturb_def,ABS_BOUNDS,REAL_LE_ANTISYM]
QED

Theorem delta_REAL_deterministic:
  ∀ (v:real) (m:mType) (delta:real).
    abs delta <= mTypeToR REAL v ==> perturb v m delta = v
Proof
  Cases_on `m` \\ fs[mTypeToR_def, delta_0_deterministic]
QED

(**
Evaluation with 0 as machine epsilon is deterministic
**)
Theorem meps_0_deterministic:
  ∀ (f: real expr) v1:real v2:real E defVars fBits.
    eval_expr E (toRTMap defVars) (toREval f) v1 REAL /\
    eval_expr E (toRTMap defVars) (toREval f) v2 REAL ==>
    v1 = v2
Proof
  Induct_on `f` \\ fs[toREval_def] \\ rpt strip_tac \\ fs[eval_expr_cases]
  \\ rveq \\ fs[delta_REAL_deterministic]
  >- (IMP_RES_TAC toRTMap_eval_REAL \\ rveq \\ res_tac \\ fs[])
  >- (IMP_RES_TAC toRTMap_eval_REAL \\ rveq \\ res_tac
      \\ fs[delta_REAL_deterministic])
  >- (IMP_RES_TAC toRTMap_eval_REAL \\ rveq \\ res_tac
      \\ fs[delta_REAL_deterministic])
  >- (IMP_RES_TAC toRTMap_eval_REAL \\ rveq \\ res_tac
      \\ fs[delta_REAL_deterministic])
  \\ IMP_RES_TAC toRTMap_eval_REAL \\ rveq \\ res_tac
  \\ fs[delta_REAL_deterministic]
QED

(**
Helping lemmas. Needed in soundness proof.
For each evaluation of using an arbitrary epsilon, we can replace it by
evaluating the subExpressions and then binding the result values to different
variables in the Environment.
**)
Theorem binary_unfolding:
  ∀ (b:binop) (f1:(real)expr) (f2:(real)expr) E Gamma v1 v2 m1 m2 delta m.
    (b = Div ==> (v2 <> 0)) /\
    (abs delta) <= (mTypeToR m) (evalBinop b v1 v2) /\
    eval_expr E Gamma f1 v1 m1 /\
    eval_expr E Gamma f2 v2 m2 /\
    eval_expr E Gamma (Binop b f1 f2) (perturb (evalBinop b v1 v2) m delta) m ==>
    eval_expr (updEnv 2 v2 (updEnv 1 v1 emptyEnv))
              (updDefVars (Binop b (Var 1) (Var 2)) m
               (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma)))
              (Binop b (Var 1) (Var 2)) (perturb (evalBinop b v1 v2) m delta) m
Proof
  fs [updEnv_def,updDefVars_def,join_fl_def,eval_expr_cases,APPLY_UPDATE_THM,PULL_EXISTS]
  \\ rpt strip_tac
  \\ qexists_tac `delta` \\ fs[]
  \\ IMP_RES_TAC Gamma_det \\ fs[]
QED

Theorem fma_unfolding:
  ∀(f1:(real)expr) (f2:(real)expr) (f3:(real)expr) E Gamma (v:real) v1 v2 v3
     m1 m2 m3 delta m.
    (abs delta) <= (mTypeToR m) (evalFma v1 v2 v3) /\
    eval_expr E Gamma f1 v1 m1 /\
    eval_expr E Gamma f2 v2 m2 /\
    eval_expr E Gamma f3 v3 m3 /\
    eval_expr E Gamma (Fma f1 f2 f3) (perturb (evalFma v1 v2 v3) m delta) m ==>
    eval_expr (updEnv 3 v3 (updEnv 2 v2 (updEnv 1 v1 emptyEnv)))
              (updDefVars (Fma (Var 1) (Var 2) (Var 3)) m
               (updDefVars (Var 3) m3
                (updDefVars (Var 2) m2 (updDefVars (Var 1) m1 Gamma))))
              (Fma (Var 1) (Var 2) (Var 3)) (perturb (evalFma v1 v2 v3) m delta) m
Proof
  fs [updEnv_def,updDefVars_def,join_fl3_def,join_fl_def,eval_expr_cases,APPLY_UPDATE_THM,PULL_EXISTS]
  \\ rpt strip_tac
  \\ qexists_tac `delta` \\ fs[]
  \\ IMP_RES_TAC Gamma_det \\ fs[]
QED

Theorem eval_eq_env:
  ∀ e E1 E2 Gamma v m.
    (!x. E1 x = E2 x) /\
    eval_expr E1 Gamma e v m ==>
    eval_expr E2 Gamma e v m
Proof
  Induct \\ rpt strip_tac \\ fs[eval_expr_cases]
  >- (`E1 n = E2 n` by (first_x_assum irule)
      \\ fs[])
  >- (qexists_tac `delta` \\ fs[])
  >- (rveq \\ qexistsl_tac [`m'`, `v1`] \\ fs[]
      \\ first_x_assum drule \\ disch_then irule \\ fs[])
  >- (rveq \\ qexistsl_tac [`m1`, `v1`] \\ fs[]
      \\ qexists_tac `delta` \\ fs[]
      \\ first_x_assum drule \\ disch_then irule \\ fs[])
  >- (rveq \\ qexistsl_tac [`m1`, `v1`] \\ fs[]
      \\ qexists_tac `delta` \\ fs[]
      \\ first_x_assum drule \\ disch_then irule \\ fs[])
  >- (rveq \\ qexistsl_tac [`m1`, `m2`, `v1`, `v2`, `delta`]
      \\ fs[] \\ conj_tac \\ first_x_assum irule \\ asm_exists_tac \\ fs[])
  >- (rveq \\ qexistsl_tac [`m1`, `m2`, `m3`, `v1`, `v2`, `v3`, `delta`]
      \\ fs[] \\ prove_tac [])
  >- (rveq \\ qexistsl_tac [`m1'`, `v1`, `delta`] \\ fs[]
      \\ first_x_assum drule \\ disch_then irule \\ fs[])
QED

Theorem swap_Gamma_eval_expr:
  ∀ e E vR m Gamma1 Gamma2.
      (!e. Gamma1 e = Gamma2 e) /\
      eval_expr E Gamma1 e vR m ==>
      eval_expr E Gamma2 e vR m
Proof
  Induct_on `e` \\ fs[eval_expr_cases] \\ rpt strip_tac
  \\ metis_tac[]
QED

val _ = export_theory();
