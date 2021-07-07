(*
  Define some nicer versions of definitions for pretty printing with the munger
*)
open semanticPrimitivesTheory terminationTheory;
open source_to_sourceProofsTheory CakeMLtoFloVerTheory CakeMLtoFloVerProofsTheory optPlannerProofsTheory;
open FloverMapTheory;
open realTheory;
open bossLib preamble;

val _ = new_theory "pretty"

Overload reverse = “REVERSE”

Definition compress_bool_def:
  compress_bool fpOpt =
  case fpOpt of
  | Rval (FP_BoolTree fv) => Rval (Boolv (fpSem$compress_bool fv))
  | Rval v => Rval v
  | Rerr e => Rerr e
End

Definition isMarzipanOp_def:
  isMarzipanOp op = (getOpClass op = Icing)
End

Definition applyOptimizations_def:
  applyOptimizations r choices rws =
  case do_fprw r choices rws of
  | NONE => r
  | SOME r_opt => r_opt
End

Definition nextChoice_def:
  nextChoice (fpS:fpState) = fpS.opts 0
End

Definition canOptimize_def:
  canOptimize (fpS:fpState) = (fpS.canOpt = FPScope Opt)
End

Definition realsAllowed_def:
  realsAllowed (fpS) = fpS.real_sem
End

Definition updateState_def:
  updateState st refs ffi = st with <| refs:=refs; ffi := ffi |>
End

Definition advanceOracle_def:
  advanceOracle st = shift_fp_opts st
End

Theorem foo:
  (let
   fp_opt =
   if canOptimize st.fp_state then applyOptimizations r (nextChoice st.fp_state) st.fp_state.rws else r;
   stN = if canOptimize st.fp_state then shift_fp_opts st else st;
   fp_res = if isFpBool op then compress_bool fp_opt else fp_opt
   in (stN with <| refs:=refs; ffi:=ffi|>, list_result fp_res)) =
  let
  (stN, r_opt) =
  if canOptimize st.fp_state then
  (shift_fp_opts st, applyOptimizations r (nextChoice st.fp_state) st.fp_state.rws)
  else (st, r);
  fp_res = if isFpBool op then compress_bool r_opt else r_opt
   in (stN with <| refs:=refs; ffi:=ffi|>, list_result fp_res)
Proof
  fs[] \\ TOP_CASE_TAC \\ fs[]
QED

Definition optimizeIfApplicable_def:
  optimizeIfApplicable st r =
  if canOptimize st.fp_state then
  (shift_fp_opts st, applyOptimizations r (nextChoice st.fp_state) st.fp_state.rws)
  else (st, r)
End

Overload toBool = “compress_bool”

Theorem evaluate_App_Marzipan =
  List.nth (CONJ_LIST 17 terminationTheory.evaluate_def, 8)
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss()) [ASSUME “getOpClass op = Icing”]
  |> SIMP_RULE (srw_ss()) [GSYM compress_bool_def, GSYM applyOptimizations_def,
                            GSYM nextChoice_def, GSYM canOptimize_def,
                            INST_TYPE [“:'b” |-> “:'ffi”] foo,
                           GSYM optimizeIfApplicable_def]
  |> REWRITE_RULE [GSYM updateState_def, GSYM advanceOracle_def];

Theorem evaluate_App_Reals =
  List.nth (CONJ_LIST 17 terminationTheory.evaluate_def, 8)
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss()) [ASSUME “getOpClass op = Reals”]
  |> SIMP_RULE (srw_ss()) [GSYM realsAllowed_def, GSYM updateState_def,
                           GSYM advanceOracle_def];

Theorem evaluate_App_Simple =
  List.nth (CONJ_LIST 17 terminationTheory.evaluate_def, 8)
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss()) [ASSUME “getOpClass op = Simple”]
  |> SIMP_RULE (srw_ss()) [GSYM realsAllowed_def, GSYM updateState_def,
                           GSYM advanceOracle_def];

Definition updateOptFlaglocal_def:
    updateOptFlaglocal st annot = if st.fp_state.canOpt = Strict then st.fp_state else st.fp_state with canOpt := FPScope annot
End

Definition resetOptFlag_def:
  resetOptFlag st1 st2 = st1 with fp_state := st1.fp_state with canOpt := st2.fp_state.canOpt
End

Definition addAnnot_def:
  addAnnot annot vs = do_fpoptimise annot vs
End

Definition updateOptFlag_def:
  updateOptFlag st annot = st with fp_state := updateOptFlaglocal st annot
End

Theorem evaluate_fpOptimize =
  List.nth (CONJ_LIST 19 terminationTheory.evaluate_def, 16)
  |> SIMP_RULE (srw_ss()) [GSYM updateOptFlaglocal_def, GSYM resetOptFlag_def, GSYM addAnnot_def, LET_THM, GSYM updateOptFlag_def]

Definition noRealsAllowed_def:
  noRealsAllowed fps = ~ fps.real_sem
End

Definition noStrictExecution_def:
  noStrictExecution fps = (fps.canOpt ≠ Strict)
End

Definition appendOptsAndOracle_def:
  appendOptsAndOracle st rws fpOpts choices = st with fp_state := st.fp_state with <| rws := st.fp_state.rws ++ rws; opts := fpOpts; choices := choices |>
End

Overload is_rewrite_correct = “is_rewriteFPexp_correct”
Overload freeVarsBound = “freeVars_fp_bound”

Theorem rewrite_correct_def:
  K T ^(is_rewriteFPexp_correct_def
  |> SIMP_RULE (srw_ss()) [GSYM canOptimize_def, GSYM noRealsAllowed_def,
                           GSYM appendOptsAndOracle_def] |> SPEC_ALL |> concl |> rhs)
Proof
  simp[K_DEF]
QED

Definition freeVars_fine_exp_def:
  freeVars_fine_exp canOpt (st1:'a semanticPrimitives$state) e env path =
  ∀ (st1:'a semanticPrimitives$state) st2. freeVars_arithExp_bound st1 st2 env canOpt path e
End

Overload freeVarsPathBound = “freeVars_fine_exp canOpt”

Overload is_performRewrites_correct = “is_perform_rewrites_correct”

Overload performRewrites = “perform_rewrites”
Overload rewrite = “rewriteFPexp”

Overload is_optimiseWithPlan_correct = “is_optimise_with_plan_correct”


Definition notInStrictMode_def:
  notInStrictMode fps = (fps.canOpt ≠ Strict)
End

Definition flagAndScopeAgree_def:
  flagAndScopeAgree flag fps = (flag.canOpt <=> fps.canOpt = FPScope Opt)
End

Theorem performRewrites_correct_def:
  K T ^(is_perform_rewrites_correct_def
        |> SIMP_RULE (srw_ss()) [GSYM noRealsAllowed_def, GSYM canOptimize_def,
                                 GSYM appendOptsAndOracle_def, GSYM notInStrictMode_def,
                                 GSYM flagAndScopeAgree_def,
                                 GSYM freeVars_fine_exp_def]
        |> REWRITE_RULE [GSYM freeVars_fine_exp_def]
        |> SPEC_ALL
        |> GEN “cfg:source_to_source$config” |> SPEC “canOpt:source_to_source$config” |> concl |> rhs)
Proof
  simp[K_DEF]
QED

Definition optimizeWithPlan_def:
  optimizeWithPlan cfg plan exps = MAP (λ e. FST (optimise_with_plan cfg plan e)) exps
End

Definition getRws_def:
  getRws plan = FLAT (MAP (λ x. case x of |Apply (_, rws) => rws |_ => []) plan)
End

Definition freeVars_fine_def:
  freeVars_fine canOpt (st1:'a semanticPrimitives$state) exps env plan =
  (∀ e. MEM e exps ⇒ ∀ (st1:'a semanticPrimitives$state) st2. freeVars_plan_bound st1 st2 env canOpt plan e)
End

Overload freeVarsPlanBound = “freeVars_fine canOpt”

Theorem optimize_with_plan_correct:
  K T ^(is_optimise_with_plan_correct_def
        |> SIMP_RULE (srw_ss()) [GSYM noRealsAllowed_def, GSYM canOptimize_def,
                                 GSYM appendOptsAndOracle_def, GSYM notInStrictMode_def,
                                 GSYM flagAndScopeAgree_def, GSYM optimizeWithPlan_def,
                                 GSYM getRws_def, LET_THM,
                                 GSYM freeVars_fine_def]
        |> REWRITE_RULE [GSYM freeVars_fine_def]
        |> SIMP_RULE (srw_ss()) []
        |> SPEC_ALL
        |> GEN “cfg:source_to_source$config” |> SPEC “canOpt:source_to_source$config”
        |> concl |> rhs)
Proof
  simp[K_DEF]
QED

Theorem rewrite_correct_chaining =
  rewriteExp_compositional;

Overload is_rewrite_correct = “is_rewriteFPexp_list_correct”

Definition elemOfPlan_def:
  elemOfPlan (path,opts) plan = MEM (Apply (path, opts)) plan
End

Theorem optimize_with_plan_correct_lift:
  ∀plan.
    (∀ path opts.
       elemOfPlan (path,opts) plan ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
         is_performRewrites_correct opts st1 st2 env cfg e r path) ⇒
    ∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
      is_optimise_with_plan_correct plan st1 st2 env cfg exps r
Proof
  simp[elemOfPlan_def] \\ rpt strip_tac \\ irule is_optimise_with_plan_correct_lift
  \\ rpt strip_tac \\ gs[]
QED

Theorem perform_rewrites_correct_lift =
  is_rewriteFPexp_correct_lift_perform_rewrites |> GEN_ALL |> SPEC “opts:(fp_pat # fp_pat) list” |> GEN_ALL |> SIMP_RULE std_ss [];

Theorem optPlanner_correct =
optPlanner_correct_float_single
        |> SIMP_RULE (srw_ss()) [is_optimise_with_plan_correct_def, GSYM noRealsAllowed_def, GSYM canOptimize_def,
                                 GSYM appendOptsAndOracle_def, GSYM notInStrictMode_def,
                                 GSYM flagAndScopeAgree_def, GSYM optimizeWithPlan_def,
                                 GSYM getRws_def, LET_THM,
                                 GSYM freeVars_fine_def]
        |> REWRITE_RULE [GSYM freeVars_fine_def]

Theorem optPlanner_real_id =
optPlanner_correct_real_single
        |> SIMP_RULE (srw_ss()) [floatToRealProofsTheory.is_real_id_optimise_with_plan_def, GSYM noRealsAllowed_def, GSYM canOptimize_def,
                                 GSYM appendOptsAndOracle_def, GSYM notInStrictMode_def,
                                 GSYM flagAndScopeAgree_def,
                                 GSYM freeVars_fine_exp_def]
        |> REWRITE_RULE [GSYM freeVars_fine_exp_def]

Overload noOpts = “no_optimisations cfg”

Definition nooptsApplied_def:
  noOptsApplied fps = fps with <| opts := (λ x. []); rws := []; canOpt := FPScope NoOpt; choices := 0|>
End

Definition nooptsAppliedWithChoices_def:
  noOptsAppliedWithChoices fps choices = fps with <| opts := (λ x. []); rws := []; canOpt := FPScope NoOpt; choices := choices|>
End

Theorem env_simp:
  (env:v sem_env) with v := env.v = env
Proof
  fs[sem_env_component_equality]
QED

Overload noOptSim = “noopt_sim”

Theorem noopt_correct =
  no_optimisations_eval_sim
  |> SPEC_ALL
  |> GEN “choices:num” |> Q.SPEC ‘0’
  |> GEN “fpScope:fp_opt” |> Q.SPEC ‘NoOpt’
  |> GEN_ALL
  |> SIMP_RULE std_ss [GSYM nooptsApplied_def, GSYM nooptsAppliedWithChoices_def, env_simp]

(*
Theorem toFloVerExp_definition =
  toFloVerExp_def

Theorem toFloVerCmd_definition =
  toFloVerCmd_def
*)

(*
Definition noSubnormalsInEval_def:
  noSubnormalsInEval st env theVars vs body =
  evaluate_fine st (env with v := extend_env_with_vars (REVERSE theVars) (REVERSE vs) env.v)
  [body]
End

Definition hasRoundoffError_def:
  hasRoundoffError theCmd theBounds (iv,err) ⇔
  FloverMapTree_find (getRetExp (toRCmd theCmd)) theBounds = SOME (iv,err)
End

Definition realEvaluates_to_def:
  realEvaluates_to body env r ⇔
  evaluate (empty_state with fp_state :=
            empty_state.fp_state with <| real_sem := T; canOpt := FPScope NoOpt |>) env [body] =
  (empty_state with fp_state := empty_state.fp_state with <| real_sem := T; canOpt := FPScope NoOpt |>,
   Rval [Real r])
End

Definition floatEvaluates_to_def:
  floatEvaluates_to body env fp ⇔
  evaluate (empty_state with fp_state := empty_state.fp_state with canOpt := FPScope NoOpt) env [body] =
  (empty_state with fp_state := empty_state.fp_state with canOpt := FPScope NoOpt, Rval [FP_WordTree fp])
End

Definition envWithRealVars_def:
  envWithRealVars env vars vs = env with v := toRspace (extend_env_with_vars (REVERSE vars) (REVERSE vs) env.v)
End

Definition envWithFloatVars_def:
  envWithFloatVars env vars vs = env with v := (extend_env_with_vars (REVERSE vars) (REVERSE vs) env.v)
End

Definition valueTree2real_def:
  valueTree2real fp = fp64_to_real (compress_word fp)
End

Overload abs = “real$abs”

Theorem CakeMLtoFloVer_infer_error =
  CakeML_FloVer_sound_error
  |> SIMP_RULE std_ss [GSYM noSubnormalsInEval_def, GSYM hasRoundoffError_def,
                       GSYM realEvaluates_to_def, GSYM floatEvaluates_to_def,
                       GSYM envWithRealVars_def, GSYM envWithFloatVars_def,
                       GSYM valueTree2real_def]

Definition doppler_real_fun_spec:
  doppler_real_spec (c1,c2,c3) = doppler_real_fun c1 c2 c3
End

Overload fpToReal= “fp64_to_real”

Theorem doppler_semantics_final =
  doppler_semantics_final
  |> GEN “fname:mlstring” |> Q.SPEC ‘doppler’
  |> SIMP_RULE std_ss
    [GSYM doppler_real_fun_spec]
 (*
    ASSUME “doppler_float_returns:(word64#word64#word64)->word64->bool = float_returns dopplerBody”,
    ASSUME “doppler_real_spec:word64#word64#word64->real = real_returns dopplerBody”] *)

Definition nn1Layer_float_spec:
  nnController_float_spec (c1,c2,c3,c4) = nn1Layer_float_returns (c1,c2,c3,c4)
End

Definition nn1Layer_real_fun_spec:
  nnController_real_spec (c1,c2,c3,c4) = nn1Layer_real_fun c1 c2 c3 c4
End

Overload nnLayer_semantics_side = “nn1Layer_semantics_side”

Overload nnLayer_prog = “nn1Layer_prog”

Theorem nn1Layer_semantics_final =
  nn1Layer_semantics_final
  |> GEN “fname:mlstring” |> Q.SPEC ‘nnController’
  |> SIMP_RULE std_ss [GSYM nn1Layer_real_fun_spec, GSYM nn1Layer_float_spec]

(** FIXME: Use "real" type from semanticPrimitivesTheory if this is "unsatisfactory" **)
Type optimization[pp] = “:(fp_pat # fp_pat)”
Type scopeAnnotation = “:optChoice”
Type rewriteApp[pp] = “:rewrite_app”

Datatype:
  fpState =
  <| rewrites : optimization list;
     opts : num -> rewriteApp list;
     canOpt : scopeAnnotation;
     choices : num |>
End
**)

val _ = export_theory();
