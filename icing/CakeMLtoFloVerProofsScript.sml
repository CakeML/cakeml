(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open compilerTheory;
(* FloVer *)
open ExpressionsTheory CommandsTheory;
(* Icing *)
open CakeMLtoFloVerTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVerProofs";

Theorem isFloVerExps_toFloVerExp_succeeds:
  ∀ es.
    isFloVerExps es ⇒
    ∀ e. MEM e es ⇒
      ∀ ids freshId.
        ∃ ids2 freshId2 fexp.
        toFloVerExp ids freshId e = SOME (ids2, freshId2, fexp)
Proof
  ho_match_mp_tac isFloVerExps_ind
  \\ rpt strip_tac \\ rfs [] \\ rveq \\ TRY (fs[isFloVerExps_def]\\NO_TAC)
  >- (fs[isFloVerExps_def, toFloVerExp_def, lookupCMLVar_def]
      \\ rpt (TOP_CASE_TAC \\ fs[]))
  \\ Cases_on ‘op’ \\ fs[isFloVerExps_def, quantHeuristicsTheory.LIST_LENGTH_3]
  \\ rveq \\ fs[]
  >- (
    Cases_on ‘f’ \\ fs[] \\ rveq \\ fs[]
    \\ simp[toFloVerExp_def]
    \\ first_x_assum (qspecl_then [‘ids’,‘freshId’] assume_tac) \\ fs[])
  >- (
     simp[toFloVerExp_def]
     \\ first_assum (qspec_then ‘e1’ assume_tac)
     \\ first_x_assum (qspec_then ‘e2’ assume_tac)
     \\ fs[]
     \\ last_x_assum (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
     \\ last_x_assum (qspecl_then [‘ids2’, ‘freshId2’] assume_tac) \\ fs[])
  \\ simp[toFloVerExp_def]
  \\ first_assum (qspec_then ‘e1’ assume_tac)
  \\ first_assum (qspec_then ‘e2’ assume_tac)
  \\ first_x_assum (qspec_then ‘e3’ assume_tac)
  \\ fs[]
  \\ last_x_assum (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
  \\ last_x_assum (qspecl_then [‘ids2’, ‘freshId2’] assume_tac) \\ fs[]
  \\ rename1 ‘toFloVerExp ids2 freshId2 e2 = SOME (ids3, freshId3, fexp2)’
  \\ last_x_assum (qspecl_then [‘ids3’, ‘freshId3’] assume_tac) \\ fs[]
QED

Theorem isFloVerCmd_toFloVerCmd_succeeds:
  ∀ e ids freshId.
    isFloVerCmd e ⇒
    ∃ ids2 f.
      toFloVerCmd ids freshId e = SOME (ids2, f)
Proof
  ho_match_mp_tac isFloVerCmd_ind
  \\ rpt strip_tac \\ fs[isFloVerCmd_def, toFloVerCmd_def]
  >- (
   Cases_on ‘so’ \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
   \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
   \\ disch_then (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
   \\ first_x_assum (qspecl_then [‘appendCMLVar (Short x) freshId2 ids2’, ‘freshId2 + 1’] assume_tac)
   \\ fs[])
  >- (
   drule isFloVerExps_toFloVerExp_succeeds
    \\ disch_then (qspecl_then [‘App op exps’,‘ids’, ‘freshId’] assume_tac) \\ fs[])
  \\ fs[toFloVerExp_def]
  \\ Cases_on ‘lookupCMLVar x ids’ \\ fs[]
  \\ Cases_on ‘x'’ \\ fs[]
QED

(*
Theorem CakeML_Flover_real_imp:
  ∀ e ids f env st r st2.
  isFloVerCmd e ∧
  toFloVerCmd [] 0 e = SOME(ids, f) ∧
  evaluate st env [toRealExp e] = (st2, Rval [Real r]) ⇒
  bstep f (toFloVerEnv env ids) (λ e. SOME REAL) r REAL
Proof
  ho_match_mp_tac terminationTheory.evaluate_ind
QED

local
  val bstep_goal =
  “(λ f E Gamma r t.
    ∀ e ids st env st2.
    bstep f E Gamma r t ∧
    E = (toFloVerEnv env ids) ∧
    Gamma = (λ e. SOME REAL) ∧
    t = REAL ∧
    isFloVerCmd e ∧
    toFloVerCmd [] 0 e = SOME(ids, f) ⇒
    evaluate st env [toRealExp e] = (st2, Rval [Real r]))”
in
Theorem Flover_CakeML_real_imp:
  ∀ f E Gamma r t.
   (^bstep_goal) f E Gamma r t
Proof

Theorem FloVerExp_CakeML_real_imp:
  ∀ es f r ids ids2 freshId freshId2 st env.
  isFloVerExps es ⇒
  ∀ e. MEM e es ∧
  eval_expr (toFloVerEnv env ids) (λ e. SOME REAL) f r REAL ∧
  st.fp_state.real_sem ∧
  toFloVerExp ids freshId e = SOME(ids2, freshId2, f) ⇒
  ∃ st2.
  evaluate st env [toRealExp e] = (st2, Rval [Real r])
Proof
  ho_match_mp_tac isFloVerExps_ind \\ rpt strip_tac \\ TRY (fs[isFloVerExps_def] \\ NO_TAC)
  >- (
   fs[isFloVerExps_def] \\ rveq \\ fs[toFloVerExp_def]
   \\ Cases_on  ‘∃ v y. lookupCMLVar x ids = SOME (v,y)’ \\ fs[] \\ fs[] \\ rveq
   >- (
    fs[toRealExp_def, terminationTheory.evaluate_def, toFloVerEnv_def,
       ExpressionSemanticsTheory.eval_expr_cases, lookupFloVerVar_def,
       lookupCMLVar_def]
    \\ ‘FIND (λ (m,i). y = i) ids = SOME (v,y)’
      by (pop_assum mp_tac \\ rpt (pop_assum kall_tac)
          \\ Induct_on ‘ids’ \\ fs[updateTheory.FIND_def]
          \\ rpt strip_tac \\ Cases_on ‘h’ \\ fs[]
          \\ Cases_on ‘x = q’ \\ fs[]
          \\ cheat (*TODO: ids 1-1 *))
    \\ fs[]
    \\ ‘v = x’ by (cheat) \\ rveq
    \\ TOP_CASE_TAC \\ fs[] \\ Cases_on ‘x’ \\ fs[] \\ rveq)
   \\ ‘lookupCMLVar x ids = NONE’
     by (CCONTR_TAC
         \\ Cases_on ‘lookupCMLVar x ids’ \\ fs[] \\ Cases_on ‘x'’ \\ fs[])
   \\ fs[] \\ rveq
   \\ fs[ExpressionSemanticsTheory.eval_expr_cases, toFloVerEnv_def,
         lookupFloVerVar_def, lookupCMLVar_def]
   \\ (* id is fresh! *) cheat)
  >- (
   fs[] \\ rveq \\ Cases_on ‘op’ \\ fs[isFloVerExps_def]
   >- (
    rename1 ‘App (FP_uop uop) es’
    \\ Cases_on ‘uop’ \\ fs[quantHeuristicsTheory.LIST_LENGTH_1] \\ rveq
    \\ fs[toFloVerExp_def]
    \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
    \\ disch_then (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
    \\ fs[] \\ rveq \\ fs[ExpressionSemanticsTheory.eval_expr_cases]
    \\ rveq
    \\ rename1 ‘eval_expr (toFloVerEnv env ids) (λ e. SOME REAL) fexp v1 m1’
    \\ ‘m1 = REAL’ by (Cases_on ‘m1’ \\ fs[MachineTypeTheory.isCompat_def])
    \\ rveq \\ first_x_assum drule
    \\ rpt (disch_then drule)
    \\ disch_then assume_tac \\ fs[]
    \\ imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv
    \\ fs[toRealExp_def, terminationTheory.evaluate_def,
          astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def,
          realOpsTheory.real_uop_def, getRealUop_def,
          ExpressionsTheory.evalUnop_def])
   >- (
    rename1 ‘App (FP_bop bop) es’
    \\ Cases_on ‘bop’ \\ fs[quantHeuristicsTheory.LIST_LENGTH_2] \\ rveq
    \\ fs[toFloVerExp_def]
    \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
    \\ disch_then (qspecl_then [‘e1’, ‘ids’, ‘freshId’] assume_tac) \\ fs[]
    \\ fs[]
    \\ rename1 ‘toFloVerExp ids freshId e1 = SOME (ids1, freshId1, fexp1)’
    \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
    \\ disch_then (qspecl_then [‘e2’, ‘ids1’, ‘freshId1’] assume_tac) \\ fs[]
    \\ fs[] \\ rveq
    \\ rename1 ‘eval_expr (toFloVerEnv env ids) (λ e. SOME REAL) (Binop (fpBopToFloVer _) fexp1 fexp2) r REAL’
    \\ fs[ExpressionSemanticsTheory.eval_expr_cases]
    \\ ‘m1 = REAL ∧ m2 = REAL’
      by (Cases_on ‘m1’ \\ Cases_on ‘m2’
          \\ fs[MachineTypeTheory.isJoin_def, MachineTypeTheory.isFixedPoint_def, MachineTypeTheory.join_fl_def] MachineTypeTheory.morePrecise_def, MachineTypeTheory.join_fl_def]

Theorem FloverCmd_CakeML_real_imp:
  ∀ e f r ids ids2 freshId st env st2.
    isFloVerCmd e ∧
    bstep f (toFloVerEnv env ids) (λ e. SOME REAL) r REAL ∧
    toFloVerCmd ids freshId e = SOME(ids2, f) ⇒
    evaluate st env [toRealExp e] = (st2, Rval [Real r])
Proof
  ho_match_mp_tac isFloVerCmd_ind \\ rpt strip_tac \\ fs[isFloVerCmd_def]
  >- (
   Cases_on ‘so’ \\ fs[toFloVerCmd_def]
   \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
   \\ disch_then (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[] \\ fs[]
   \\ drule isFloVerCmd_toFloVerCmd_succeeds \\ fs[]
   \\ disch_then (qspecl_then [‘appendVar (Short x) freshId2 ids2'’, ‘freshId2 + 1’] assume_tac)
   \\ fs[] \\ fs[] \\ rveq
   \\ fs[bstep_cases]
   \\ simp[toRealExp_def, terminationTheory.evaluate_def]

 mp_tac (bstep_ind |> SPEC bstep_goal) \\ reverse impl_tac
 >- (
   rpt strip_tac \\ fs[] \\ rpt strip_tac \\ first_x_assum drule
   \\ rpt (disch_then drule) \\ fs[])
 \\ rpt strip_tac \\ fs[]

Theorem CakeML_FloVer_real_equiv:
! e (st st2:'a semanticPrimitives$state) env e r.
  (* the CakeML code can be translated into FloVer input *)
  isFloVerCmd e ==>
  ? ids f.
    (* the translation to FloVer does not fail *)
    toFloVerCmd [] 0 e = SOME (ids, f) /\
    (* evaluation on reals in CakeML is equivalent to evaluation in FloVer *)
    (evaluate st env [toRealExp e] = (st2, Rval [Real r]) <=>
     bstep f (toFloVerEnv env ids) (λ e. SOME M64) r REAL)
Proof
  rpt strip_tac
  \\ imp_res_tac isFloVerCmd_toFloVerCmd_succeeds
  \\ first_x_assum (qspecl_then [‘[]’, ‘0’] assume_tac) \\ fs[]
  \\ EQ_TAC \\ rpt (pop_assum mp_tac)
QED
*)

Definition env_rel_def:
  env_rel env E (ids: ((string, string) id # num) list) =
  (∀ (x:string) v w fp.
   nsLookup env (Short x) = SOME v ∧
    (v = Litv (Word64 w) ∨ v = FP_WordTree fp) ⇒
    ∃ n r.
    lookupCMLVar (Short x) ids = SOME (Short x,n) ∧
    E n = SOME r ∧
    case v of
    | FP_WordTree fp => fp64_to_real (compress_word fp) = r
    | Litv (Word64 w) => fp64_to_real w = r
    | _ => F)
End

(*
Theorem CakeML_FloVer_infer_error:
  ∀ e (st st2:'a semanticPrimitives$state) env e Gamma P analysisResult.
  (* the CakeML code can be translated into FloVer input *)
  isFloVerCmd e ∧
  (* the free variables of the program are bound and sound with respect to P *)
  (∀ x.
   x IN vars e ⇒
   nsLookup x = SOME v ∧
   nsLookup x = SOME (Litv (Word64 w)) ⇒
   fst (P x) ≤ fp64_to_real w ∧ fp64_to_real w ≤ snd (P x) ∧
   nsLookup x = SOME (FP_WordTree fp) ⇒
   fst (P x) ≤ fp64_to_real (compress_word fp) ∧ fp64_to_real (compress_word fp) ≤ snd (P x)) ∧
  (* translating to FloVer, running the pipeline succeeds *)
  getErrorbounds e Gamma P = SOME analysisResult ==>
  ? ids f iv err w r.
    (* the translation to FloVer does not fail *)
    toFloVerCmd [] 0 e = SOME (ids, f) /\
    (* the analysis result returned contains an error bound *)
    FloverMapTree_find (getRetExp f) analysisResult = SOME (iv,err) /\
    (* we can evaluate with a real-valued semantics *)
    evaluate st env [toRealExp e] = (st2, Rval [Real r]) /\
    (* the CakeML code returns a valid floating-point word *)
    evaluate st env [e] = (st2, Rval [FP_WordTree w]) /\
    (* the roundoff error is sound *)
    real$abs ((fp64_to_real (case (compress (FP_WordTree w)) of Litv (Word64 w) => w) - r))
      <= err
Proof
  rpt strip_tac
  \\ imp_res_tac isFloVerCmd_toFloVerCmd_succeeds
  \\ first_x_assum (qspecl_then [‘[]’, ‘0’] assume_tac)
  \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.compress_def]
  \\ qpat_x_assum ‘getErrorbounds _ _ _ = _’ mp_tac
  \\ simp[getErrorbounds_def]
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ fs[] \\ rveq
  \\ imp_res_tac CertificateCheckerTheory.CertificateCmd_checking_is_sound
  \\ first_x_assum (qspec_then ‘freeVars f’ assume_tac) \\ fs[]
  \\ ‘∃ E1. env_rel (env.v) E1 ids2’ by (cheat)
  \\ first_x_assum (qspec_then ‘E1’ mp_tac)
  \\ impl_tac
  >- (
   rpt strip_tac (* should follow from soundness of P for CakeML *)
   \\ cheat)
  \\ disch_then (qspec_then ‘E1’ assume_tac) \\ fs[]
  \\ pop_assum mp_tac
  \\ impl_tac
  >- (
   irule EnvironmentsTheory.approxEnv_refl \\ fs[]
   \\ cheat)
  \\ disch_then assume_tac \\ fs[]
  \\ cheat
QED
*)

val _ = export_theory ();
