(**
  An inductive relation relating real-numbered environments with
  an environment with "errors", i.e. where variables are bound to
  finite-precision values
**)
open simpLib realTheory realLib RealArith sptreeTheory;
open AbbrevsTheory ExpressionAbbrevsTheory RealSimpsTheory CommandsTheory
     FloverTactics FloverMapTheory MachineTypeTheory;
open preambleFloVer;

val _ = new_theory "Environments";

Overload abs[local] = “realax$abs”

Definition approxEnv_def:
  approxEnv E1 Gamma absEnv (fVars:num_set) (dVars:num_set) E2 =
    ((* No variable defined twice *)
    domain fVars INTER domain dVars = EMPTY ∧
    (* environments are only defined for the domain *)
    (∀ x. ~ (x IN (domain fVars UNION domain dVars)) ⇒
       E1 x = NONE ∧ E2 x = NONE) ∧
    (* All free variables are bounded in error by their machine epsilon *)
    (∀ x. x IN domain fVars ⇒
       ∃ m v1 v2.
         Gamma (Var x) = SOME m ∧
         E1 x = SOME v1 ∧
         E2 x = SOME v2 ∧
         abs (v1 - v2) ≤ computeError v1 m) ∧
    (* All bound variables are bounded in error by their inferred bound *)
    (∀ x. x IN domain dVars ⇒
      ∃ m iv err v1 v2.
        Gamma (Var x) = SOME m ∧
        E1 x = SOME v1 ∧
        E2 x = SOME v2 ∧
        FloverMapTree_find (Var x) absEnv = SOME (iv, err) ∧
        abs (v1 - v2) ≤ err))
End

Theorem approxEnvRefl:
  approxEnv emptyEnv Gamma A LN LN emptyEnv
Proof
  simp[approxEnv_def]
QED

Theorem approxEnvUpdFree:
(!(E1:env) (E2:env) (Gamma: real expr -> mType option) (A:analysisResult)
    (fVars:num_set) (dVars:num_set) v1 v2 x.
      approxEnv E1 Gamma A fVars dVars E2 /\
      (Gamma (Var x) = SOME m) /\
      (abs (v1 - v2) <= computeError v1  m) /\
      (lookup x (union fVars dVars) = NONE) ==>
      approxEnv (updEnv x v1 E1)
                Gamma A (insert x () fVars) dVars
                (updEnv x v2 E2))
Proof
  rw[] \\ fs[approxEnv_def] \\ rpt conj_tac
  >- (
   fs[EXTENSION, lookup_union, option_case_eq]
   \\ CCONTR_TAC \\ fs[] \\ rveq
   \\ metis_tac[domain_lookup])
  >- (
   rpt strip_tac \\ rveq \\ res_tac
   \\ fsrw_tac [SATISFY_ss] []
   \\ ‘x' ≠ x’
      by (CCONTR_TAC \\ fs[] \\ rveq
          \\ fs[lookup_union, option_case_eq, domain_lookup])
   \\ fs[])
  \\ rpt strip_tac \\ res_tac \\ fsrw_tac [SATISFY_ss] []
   \\ ‘x' ≠ x’
      by (CCONTR_TAC \\ fs[] \\ rveq
          \\ fs[lookup_union, option_case_eq, domain_lookup])
   \\ fs[]
QED

Theorem approxEnvUpdBound:
  ∀ (E1:env) (E2:env) (Gamma: real expr -> mType option) (A:analysisResult)
    (fVars:num_set) (dVars:num_set) v1 v2 x iv err.
      approxEnv E1 Gamma A fVars dVars E2 /\
      Gamma (Var x) = SOME m /\
      FloverMapTree_find (Var x) A = SOME (iv,err) /\
      abs (v1 - v2) <= err /\
      (lookup x (union fVars dVars) = NONE) ==>
      approxEnv (updEnv x v1 E1)
                Gamma A fVars (insert x () dVars)
                (updEnv x v2 E2)
Proof
  rw[] \\ fs[approxEnv_def] \\ rpt conj_tac
  >- (
   fs[EXTENSION, lookup_union, option_case_eq]
   \\ CCONTR_TAC \\ fs[] \\ rveq
   \\ metis_tac[domain_lookup])
  >- (
   rpt strip_tac \\ rveq \\ res_tac
   \\ fsrw_tac [SATISFY_ss] []
   \\ ‘x' ≠ x’
      by (CCONTR_TAC \\ fs[] \\ rveq
          \\ fs[lookup_union, option_case_eq, domain_lookup])
   \\ fs[])
  \\ rpt strip_tac \\ res_tac \\ fsrw_tac [SATISFY_ss] []
   \\ ‘x' ≠ x’
      by (CCONTR_TAC \\ fs[] \\ rveq
          \\ fs[lookup_union, option_case_eq, domain_lookup])
   \\ fs[]
QED

Theorem approxEnv_rules = LIST_CONJ [approxEnvRefl, approxEnvUpdFree, approxEnvUpdBound]

Theorem approxEnv_gives_value:
  !E1 E2 x v (fVars:num_set) (dVars:num_set) absenv Gamma.
    approxEnv E1 Gamma absenv fVars dVars E2 /\
    E1 x = SOME v /\
    x IN ((domain fVars) UNION (domain dVars)) ==>
    ?v2. E2 x = SOME v2
Proof
  rw[approxEnv_def] \\ res_tac \\ fsrw_tac [SATISFY_ss] []
QED

Theorem approxEnv_fVar_bounded:
  !E1 Gamma absenv fVars dVars E2 x v v2 m.
      approxEnv E1 Gamma absenv fVars dVars E2 /\
      E1 x = SOME v /\
      E2 x = SOME v2 /\
      x IN (domain fVars) /\
      Gamma (Var x) = SOME m ==>
      abs (v - v2) <= computeError v m
Proof
  rw[approxEnv_def] \\ res_tac \\ fs[]
  \\ metis_tac[]
QED

Theorem approxEnv_dVar_bounded:
  !E1 (Gamma:real expr -> mType option) (A:analysisResult) fVars dVars E2 x v v2 m iv e.
      approxEnv E1 Gamma A fVars dVars E2 /\
      E1 x = SOME v /\
      E2 x = SOME v2 /\
      x IN (domain dVars) /\
      Gamma (Var x) = SOME m /\
      FloverMapTree_find (Var x) A = SOME (iv, e) ==>
      abs (v - v2) <= e
Proof
  rw[approxEnv_def] \\ res_tac \\ fs[]
  \\ metis_tac[]
QED

Theorem approxEnv_refl:
  ∀ fVars dVars E1 Gamma A.
  (domain fVars INTER domain dVars = EMPTY) ∧
  (∀ x. x IN (domain fVars) UNION (domain dVars) ⇒
   ∃ v. E1 x = SOME v) ∧
  (∀ x. ~ (x IN (domain fVars) UNION (domain dVars)) ⇒
   E1 x = NONE) ∧
  (∀ x. x IN (domain dVars) ⇒ ∃ err iv. FloverMapTree_find (Var x) A = SOME (iv, err) ∧ 0 ≤ err) ∧
  (∀ x. x IN (domain fVars) UNION (domain dVars) ⇒
   ∃ m. Gamma (Var x) = SOME m) ⇒
  approxEnv E1 Gamma A fVars dVars E1
Proof
  rw[approxEnv_def] \\ res_tac \\ fsrw_tac [SATISFY_ss] []
  \\ Cases_on ‘m’ \\ fs[mTypeToR_pos]
  \\ irule computeError_pos
QED

val _ = export_theory ();;
