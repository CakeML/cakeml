(*
  Define some nicer versions of definitions for pretty printing with the munger
*)
open semanticPrimitivesTheory terminationTheory;
open source_to_sourceProofsTheory CakeMLtoFloVerTheory CakeMLtoFloVerProofsTheory;
open bossLib preamble;

val _ = new_theory "pretty"

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

Definition applyOptimisations_def:
  applyOptimisations r choices rws =
  case do_fprw r choices rws of
  | NONE => r
  | SOME r_opt => r_opt
End

Definition nextChoice_def:
  nextChoice (fpS:fpState) = fpS.opts 0
End

Definition canOptimise_def:
  canOptimise (fpS:fpState) = (fpS.canOpt = FPScope Opt)
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
   if canOptimise st.fp_state then applyOptimisations r (nextChoice st.fp_state) st.fp_state.rws else r;
   stN = if canOptimise st.fp_state then shift_fp_opts st else st;
   fp_res = if isFpBool op then compress_bool fp_opt else fp_opt
   in (stN with <| refs:=refs; ffi:=ffi|>, list_result fp_res)) =
  let
  (stN, fp_opt) =
  if canOptimise st.fp_state then
  (shift_fp_opts st, applyOptimisations r (nextChoice st.fp_state) st.fp_state.rws)
  else (st, r);
  fp_res = if isFpBool op then compress_bool fp_opt else fp_opt
   in (stN with <| refs:=refs; ffi:=ffi|>, list_result fp_res)
Proof
  fs[] \\ TOP_CASE_TAC \\ fs[]
QED

Theorem evaluate_App_Marzipan =
  List.nth (CONJ_LIST 17 terminationTheory.evaluate_def, 8)
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss()) [ASSUME “getOpClass op = Icing”]
  |> SIMP_RULE (srw_ss()) [GSYM compress_bool_def, GSYM applyOptimisations_def,
                            GSYM nextChoice_def, GSYM canOptimise_def,
                            INST_TYPE [“:'b” |-> “:'ffi”] foo]
  |> REWRITE_RULE [GSYM updateState_def, GSYM advanceOracle_def]
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) [GSYM isMarzipanOp_def]
  |> GEN_ALL;

Theorem evaluate_App_Reals =
  List.nth (CONJ_LIST 17 terminationTheory.evaluate_def, 8)
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss()) [ASSUME “getOpClass op = Reals”]
  |> SIMP_RULE (srw_ss()) [GSYM realsAllowed_def, GSYM updateState_def,
                           GSYM advanceOracle_def]
  |> DISCH_ALL;

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

Theorem evaluate_fpOptimise =
  List.nth (CONJ_LIST 19 terminationTheory.evaluate_def, 16)
  |> SIMP_RULE (srw_ss()) [GSYM updateOptFlaglocal_def, GSYM resetOptFlag_def, GSYM addAnnot_def, LET_THM, GSYM updateOptFlag_def]

Definition noRealsAllowed_def:
  noRealsAllowed fps = ~ fps.real_sem
End

Definition noStrictExecution_def:
  noStrictExecution fps = (fps.canOpt ≠ Strict)
End

Definition appendOptsAndOracle_def:
  appendOptsAndOracle fps rws fpOpts = fps with <| rws := fps.rws ++ rws; opts := fpOpts |>
End

Overload is_rewrite_correct = “is_rewriteFPexp_correct”

Theorem rewrite_correct_definition =
  is_rewriteFPexp_correct_def
  |> SIMP_RULE (srw_ss()) [GSYM canOptimise_def, GSYM noRealsAllowed_def,
                           GSYM appendOptsAndOracle_def];

Definition cfgAndScopeAgree_def:
  cfgAndScopeAgree cfg fps = (cfg.canOpt <=> fps.canOpt = FPScope Opt)
End

Definition optimise_def:
  optimise cfg exps = MAP (source_to_source$optimise cfg) exps
End

Theorem optimise_correct =
  is_optimise_correct_def
  |> SIMP_RULE (srw_ss()) [GSYM noRealsAllowed_def, GSYM noStrictExecution_def,
                           GSYM cfgAndScopeAgree_def,
                           GSYM appendOptsAndOracle_def,
                           GSYM optimise_def
                          ];

Theorem rewrite_correct_chaining =
  rewriteExp_compositional;

Overload is_rewrite_correct = “is_rewriteFPexp_list_correct”

Theorem optimise_correct_lift =
  is_optimise_correct_lift |> GEN_ALL |> SIMP_RULE std_ss [];

Overload noopts = “no_optimisations cfg”

Definition nooptsApplied_def:
  nooptsApplied fps = fps with <| opts := (λ x. []); rws := []; canOpt := FPScope NoOpt; choices := 0|>
End

Definition nooptsAppliedWithChoices_def:
  nooptsAppliedWithChoices fps choices = fps with <| opts := (λ x. []); rws := []; canOpt := FPScope NoOpt; choices := choices|>
End

Theorem noopt_correct =
  no_optimisations_eval_sim
  |> SPEC_ALL
  |> GEN “choices:num” |> Q.SPEC ‘0’
  |> GEN “fpScope:fp_opt” |> Q.SPEC ‘NoOpt’
  |> GEN_ALL
  |> SIMP_RULE std_ss [GSYM nooptsApplied_def, GSYM nooptsAppliedWithChoices_def]

Theorem toFloVerExp_definition =
  toFloVerExp_def

Theorem toFloVerCmd_definition =
  toFloVerCmd_def

Theorem CakeMLtoFloVer_infer_error = CakeML_FloVer_infer_error;

(** FIXME: Use "real" type from semanticPrimitivesTheory if this is "unsatisfactory" **)
Type optimisation[pp] = “:(fp_pat # fp_pat)”
Type scopeAnnotation = “:optChoice”
Type rewriteApp[pp] = “:rewrite_app”

Datatype:
  fpState =
  <| rewrites : optimisation list;
     opts : num -> rewriteApp list;
     canOpt : scopeAnnotation;
     choices : num |>
End

val _ = export_theory();
