(*
  Main connection theorem relating FloVer's roundoff error bound
  to CakeML floating-point kernel executions
*)
(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open fpValTreeTheory fpSemTheory realOpsTheory semanticPrimitivesTheory
     evaluateTheory ml_translatorTheory;
(* Icing *)
open floatToRealTheory FloVerToCakeMLTheory CakeMLtoFloVerProofsTheory;
(* FloVer *)
open ResultsTheory ExpressionsTheory ExpressionSemanticsTheory CommandsTheory
     EnvironmentsTheory IEEE_connectionTheory IEEE_reverseTheory
     FloverMapTheory TypeValidatorTheory MachineTypeTheory;
open preamble;

val _ = new_theory "FloVerToCakeMLProofs";

Definition usedVars_P_sound_def:
  usedVars_P_sound e (env:(string,string,v) namespace) P =
   ∀ x.
     x IN domain (usedVars e) ⇒
     ∃ fp.
       nsLookup env (Short ("x" ++ (toString x))) = SOME (FP_WordTree fp) ∧
       fp64_isFinite (compress_word fp) ∧
       FST (P x) ≤ fp64_to_real (compress_word fp) ∧
       fp64_to_real (compress_word fp) ≤ SND (P x)
End

Definition toFloVerEnv_def:
  toFloVerEnv (env:(string,string,v) namespace) e =
  λ (n:num).
    case lookup n (usedVars e) of
      NONE => NONE
    | SOME () =>
        case nsLookup env $ Short ("x" ++ (toString n)) of
       | NONE => NONE
       | SOME $ FP_WordTree fp => SOME $ compress_word fp
       | SOME _ => NONE
End

Theorem validTypes_usedVars:
  ∀ e Gamma x.
    validTypes e Gamma ∧
    x IN domain (usedVars e) ⇒
  ∃ m. toRExpMap Gamma (Var x) = SOME m
Proof
  ho_match_mp_tac validTypes_ind >> rpt strip_tac
  >> Cases_on ‘e’ >> gs[]
  >- gs[validTypes_def, ExpressionAbbrevsTheory.toRExpMap_def, Once usedVars_def]
  >- gs[Once usedVars_def]
  >- (
    first_x_assum irule
    >> gs[Once validTypes_def, Once usedVars_def])
  >~ [‘Binop b e1 e2’]
  >- (
    qpat_x_assum ‘validTypes _ _’ mp_tac
    >> simp[Once validTypes_def] >> strip_tac >> gs[]
    >> ‘x IN domain (usedVars e1) ∨ x IN domain (usedVars e2)’
      by (qpat_x_assum ‘x IN domain _’ mp_tac >> simp[Once usedVars_def, domain_union])
    >> gs[])
  >~ [‘Fma e1 e2 e3’]
  >- (
    qpat_x_assum ‘validTypes _ _’ mp_tac
    >> simp[Once validTypes_def] >> strip_tac >> gs[]
    >> ‘x IN domain (usedVars e1) ∨ x IN domain (usedVars e2) ∨ x IN domain (usedVars e3)’
      by (qpat_x_assum ‘x IN domain _’ mp_tac >> simp[Once usedVars_def, domain_union])
    >> gs[])
  >> first_x_assum irule
  >> gs[Once usedVars_def, Once validTypes_def]
QED

Theorem approxEnv_toFloVerEnv:
  ∀ (e:real expr) env P Gamma (A:analysisResult).
  validTypes e Gamma ∧
  usedVars_P_sound (e:real expr) env P ⇒
  approxEnv (toREnv (toFloVerEnv env e)) (toRExpMap Gamma) A (usedVars e) LN (toREnv (toFloVerEnv env e))
Proof
  rpt strip_tac >> irule approxEnv_refl >> rw [toFloVerEnv_def, toREnv_def]
  >- (
    CASE_TAC >> gs[domain_lookup]
    >- (CASE_TAC >> gs[])
    >> Cases_on ‘lookup x (usedVars e)’ >> gs[])
  >- (drule validTypes_usedVars >> gs[])
  >> gs[domain_lookup, usedVars_P_sound_def]
 >> res_tac >> gs[]
QED

Theorem usedVars_P_sound_fVars_P_sound:
  usedVars_P_sound e flEnv P ⇒
  fVars_P_sound (usedVars e) (toREnv (toFloVerEnv flEnv e)) P
Proof
  rw[usedVars_P_sound_def, RealRangeArithTheory.fVars_P_sound_def,
     toFloVerEnv_def, toREnv_def]
  >> res_tac >> gs[domain_lookup, fp64_to_real_def]
QED

Definition real_env_rel_def:
  real_env_rel (E:num -> word64 option) env vars =
  ∀ x.
    x IN vars ⇒
    ∃ fp.
      nsLookup env (Short $ STRCAT "x" (toString x)) = SOME (FP_WordTree fp) ∧
      E x = SOME (compress_word fp)
End

Theorem FloVer_to_CML_real_sim:
  ∀ e eReal prog st E env flEnv Gamma r fVars.
    eReal = ratExp2realExp e ∧
    SOME prog = toCmlRealExp e ∧
    st.fp_state.real_sem ∧
    real_env_rel E flEnv fVars ∧
    domain $ usedVars e SUBSET fVars ∧
    eval_expr (toREnv E) (toRTMap $ toRExpMap Gamma) (toREval eReal) r REAL ⇒
    evaluate st (env with v := toRspace (nsAppend flEnv env.v)) [prog] =
      (st, Rval [Real r])
Proof
  ho_match_mp_tac toCmlRealExp_ind >> rw[toCmlRealExp_def, ratExp2realExp_def]
  >> gs[eval_expr_cases, toREval_def]
  >> simp[Once evaluate_def]
  >- (
    gvs[real_env_rel_def, toREnv_def, CaseEqs["option", "v", "lit"]]
    >> ‘i IN fVars’ by gs[Once usedVars_def, SUBSET_DEF]
    >> res_tac
    >> gvs[toRspace_def, namespacePropsTheory.nsLookup_nsMap,
            namespacePropsTheory.nsLookup_nsAppend_some, fp64_to_real_def])
  >- gvs[perturb_def, evaluate_def, do_app_def, state_component_equality]
  >- (
    gvs[CaseEq"option", evaluate_def]
    >> rename1 ‘isCompat mR REAL’
    >> Cases_on ‘mR’ >> gs[isCompat_def]
    >> ‘domain (usedVars e) SUBSET fVars’ by (
      qpat_x_assum ‘domain _ SUBSET _’ mp_tac
      >> simp[Once usedVars_def])
    >> last_x_assum $ drule_then drule
    >> rpt $ disch_then drule
    >> disch_then $ qspec_then ‘env’ assume_tac
    >> gs[do_app_def, real_uop_def, getRealUop_def, evalUnop_def,
          state_component_equality])
  >- (
    gvs[CaseEq"option", evaluate_def]
    >> rename1 ‘isJoin mR1 mR2 REAL’
    >> ‘mR1 = REAL ∧ mR2 = REAL’
       by (
         conj_tac >> irule eval_expr_real
         >> once_rewrite_tac[CONJ_COMM] >> asm_exists_tac >> fs[]
         >> rpt strip_tac
         >> Cases_on ‘x’
         >> fs[ExpressionAbbrevsTheory.toRTMap_def, option_case_eq])
    >> rveq
    >> rename1 ‘domain (usedVars (Binop bop e1 e2)) SUBSET fVars’
    >> ‘domain (usedVars e1) SUBSET fVars ∧
        domain (usedVars e2) SUBSET fVars’ by (
      qpat_x_assum ‘domain _ SUBSET _’ mp_tac
      >> simp[Once usedVars_def, domain_union])
    >> rename1 ‘abs deltaOp ≤ mTypeToR REAL _’
    >> ‘deltaOp = 0’ by gs[mTypeToR_def]
    >> gvs[]
    >> ntac 2 (
      last_x_assum $ drule_then drule
      >> rpt $ disch_then drule >> disch_then $ qspec_then ‘env’ assume_tac)
    >> simp[Once evaluate_def, do_app_def, state_component_equality]
    >> Cases_on ‘bop’
    >> simp[real_bop_def, bopToRealBop_def, perturb_def, evalBinop_def])
  >- (
    gvs[CaseEq"option", evaluate_def]
    >> rename1 ‘isJoin3 mR1 mR2 mR3 REAL’
    >> ‘mR1 = REAL ∧ mR2 = REAL ∧ mR3 = REAL’
       by (
         rpt conj_tac >> irule eval_expr_real
         >> once_rewrite_tac[CONJ_COMM] >> asm_exists_tac >> fs[]
         >> rpt strip_tac
         >> Cases_on ‘x’
         >> fs[ExpressionAbbrevsTheory.toRTMap_def, option_case_eq])
    >> rveq
    >> rename1 ‘domain (usedVars (Fma e1 e2 e3)) SUBSET fVars’
    >> ‘domain (usedVars e1) SUBSET fVars ∧ domain (usedVars e2) SUBSET fVars ∧
        domain (usedVars e3) SUBSET fVars’ by (
      qpat_x_assum ‘domain _ SUBSET _’ mp_tac
      >> simp[Once usedVars_def, domain_union])
    >> rename1 ‘abs deltaOp ≤ mTypeToR REAL _’
    >> ‘deltaOp = 0’ by gs[mTypeToR_def]
    >> gvs[]
    >> ntac 3 (
      last_x_assum $ drule_then drule
      >> rpt $ disch_then drule >> disch_then $ qspec_then ‘env’ assume_tac)
    >> simp[evaluate_def, do_app_def, state_component_equality, real_bop_def,
            bopToRealBop_def, perturb_def, evalFma_def, evalBinop_def])
QED

Definition float_env_rel_def:
  float_env_rel (E:num -> word64 option) env vars =
  ∀ x v.
    x IN vars ∧
    E x = SOME v ⇒
    ∃ fp.
      nsLookup env (Short $ STRCAT "x" (toString x)) = SOME (FP_WordTree fp) ∧
      v = compress_word fp
End

Theorem FloVer_to_CML_float_sim:
  ∀ e prog st E env flEnv vF fVars.
    SOME prog = toCmlFloatExp e ∧
    st.fp_state.canOpt ≠ FPScope Opt ∧
    domain $ usedVars e SUBSET fVars ∧
    float_env_rel E flEnv fVars ∧
    eval_expr_float (toFlExp e) E = SOME vF ⇒
    ∃ fp.
      evaluate st (env with v := nsAppend flEnv env.v) [prog] =
      (st, Rval [FP_WordTree fp]) ∧
      compress_word fp = vF
Proof
  ho_match_mp_tac toCmlFloatExp_ind >> rw[toCmlFloatExp_def]
  >> gs[eval_expr_float_def, toFlExp_def]
  >> simp[Once evaluate_def]
  >- (
    gvs[toFlEnv_def, float_env_rel_def, CaseEq"option"]
    >> ‘i IN fVars’ by gs[Once usedVars_def, SUBSET_DEF]
    >> res_tac
    >> gvs[namespacePropsTheory.nsLookup_nsMap,
            namespacePropsTheory.nsLookup_nsAppend_some])
  >- gvs[perturb_def, evaluate_def, do_app_def, state_component_equality,
         compress_word_def, real_to_fp64_def]
  >- (
    gvs[CaseEq"option", evaluate_def, astTheory.isFpBool_def]
    >> ‘domain (usedVars e) SUBSET fVars’ by (
      qpat_x_assum ‘domain _ SUBSET _’ mp_tac
      >> simp[Once usedVars_def])
    >> last_x_assum $ drule_then drule
    >> rpt $ disch_then drule
    >> disch_then $ qspec_then ‘env’ strip_assume_tac
    >> gs[do_app_def, real_uop_def, getRealUop_def, evalUnop_def,
          state_component_equality, semanticPrimitivesTheory.fp_translate_def,
          compress_word_def, fp_uop_def, fp_uop_comp_def])
  >- (
    gvs[CaseEq"option", evaluate_def, astTheory.isFpBool_def]
    >> rename1 ‘domain (usedVars (Binop bop e1 e2)) SUBSET fVars’
    >> ‘domain (usedVars e1) SUBSET fVars ∧
        domain (usedVars e2) SUBSET fVars’ by (
      qpat_x_assum ‘domain _ SUBSET _’ mp_tac
      >> simp[Once usedVars_def, domain_union])
    >> ntac 2 (
      last_x_assum $ drule_then drule
      >> rpt $ disch_then drule >> disch_then $ qspec_then ‘env’ strip_assume_tac)
    >> simp[do_app_def, state_component_equality, fp_translate_def]
    >> Cases_on ‘bop’
    >> gvs[fp_bop_def, fp_bop_comp_def, bopTofpBop_def, compress_word_def,
           dmode_def])
  >- (
    gvs[CaseEq"option", evaluate_def, astTheory.isFpBool_def]
    >> rename1 ‘domain (usedVars (Fma e1 e2 e3)) SUBSET fVars’
    >> ‘domain (usedVars e1) SUBSET fVars ∧ domain (usedVars e2) SUBSET fVars ∧
        domain (usedVars e3) SUBSET fVars’ by (
      qpat_x_assum ‘domain _ SUBSET _’ mp_tac
      >> simp[Once usedVars_def, domain_union])
    >> ntac 3 (
      last_x_assum $ drule_then drule
      >> rpt $ disch_then drule >> disch_then $ qspec_then ‘env’ assume_tac)
    >> gvs[evaluate_def, do_app_def, state_component_equality, fp_translate_def,
           compress_word_def, fp_top_def, fp_top_comp_def, fpfma_def])
QED

Theorem FloVer_to_CML_float_sim_strong:
  ∀ e prog st E env flEnv vF fVars.
    SOME prog = toCmlFloatProg e ∧
    domain $ usedVars e SUBSET fVars ∧
    float_env_rel E flEnv fVars ∧
    eval_expr_float (toFlExp e) E = SOME vF ⇒
    ∃ fp.
      evaluate st (env with v := nsAppend flEnv env.v) [prog] =
      (st, Rval [FP_WordTree fp]) ∧
      compress_word fp = vF
Proof
  rw[CaseEq"option", toCmlFloatProg_def]
  >> simp[Once evaluate_def]
  >> last_x_assum $ assume_tac o GSYM
  >> drule FloVer_to_CML_float_sim
  >> qmatch_goalsub_abbrev_tac ‘evaluate stN _ [p]’
  >> ‘stN.fp_state.canOpt ≠ FPScope Opt’
    by (unabbrev_all_tac >> COND_CASES_TAC >> gs[])
  >> rpt $ disch_then $ drule
  >> disch_then $ qspec_then ‘env’ strip_assume_tac >> gvs[]
  >> unabbrev_all_tac >> gvs[state_component_equality, fpState_component_equality]
  >> COND_CASES_TAC >> gvs[do_fpoptimise_def, compress_word_def]
QED

Theorem usedVars_ratExp2realExp:
  ∀ e. usedVars e = usedVars $ ratExp2realExp e
Proof
  ho_match_mp_tac usedVars_ind >> rw[]
  >> Cases_on ‘e’ >> gs[ratExp2realExp_def]
  >- simp[usedVars_def]
  >- (Cases_on ‘v’ >> simp[ratExp2realExp_def]
      >> simp[usedVars_def])
  >> simp[Once usedVars_def] >> EVAL_TAC
QED

Theorem FloVer_CakeML_sound_error:
  ∀ e eReal progReal progFloat flEnv A P defVars Gamma env
      (st:'ffi semanticPrimitives$state).
    eReal = ratExp2realExp e ∧
    SOME progReal = toCmlRealExp e ∧
    SOME progFloat = toCmlFloatProg eReal ∧
    is64BitEval eReal ∧ noDowncast eReal ∧
    is64BitEnv defVars ∧
    CertificateChecker eReal A P defVars = SOME Gamma ∧
    usedVars_P_sound eReal flEnv P ⇒
  ∃ r fp err iv.
    FloverMapTree_find eReal A = SOME (iv,err) ∧
    (* the CakeML code returns a valid floating-point word *)
    evaluate (empty_state with fp_state :=
                empty_state.fp_state with
                  <| real_sem := T; canOpt := FPScope NoOpt |>)
             (env with v := toRspace (nsAppend flEnv env.v))
             [progReal] =
    (empty_state with fp_state :=
       empty_state.fp_state with <| real_sem := T; canOpt := FPScope NoOpt |>,
     Rval [Real r]) /\
    evaluate st (env with v := (nsAppend flEnv env.v)) [progFloat] =
      (st, Rval [FP_WordTree fp]) /\
    (* the roundoff error is sound *)
     real$abs (r - fp64_to_real (compress_word fp)) ≤ err
Proof
  rpt strip_tac
  >> first_assum $ mp_then Any assume_tac usedVars_P_sound_fVars_P_sound
  >> ‘validTypes eReal Gamma’ by (
    qpat_x_assum ‘CertificateChecker _ _ _ _ = _’ mp_tac
    >> simp[CertificateCheckerTheory.CertificateChecker_def]
    >> TOP_CASE_TAC >> rw[]
    >> irule getValidMap_top_correct
    >> first_x_assum $ irule_at Any >> rpt strip_tac
    >> gs[FloverMapTree_mem_def, FloverMapTree_empty_def, FloverMapTree_find_def])
  >> drule IEEE_reverseTheory.IEEE_connection_expr
  >> rpt $ disch_then drule >> gs[SUBSET_REFL]
  >> disch_then drule
  >> disch_then $ qspec_then ‘toFloVerEnv flEnv eReal’ mp_tac
  >> impl_tac
  >- (drule_then drule approxEnv_toFloVerEnv >> gs[])
  >> rpt strip_tac
  >> first_x_assum $ irule_at Any
  >> qmatch_goalsub_abbrev_tac ‘evaluate newSt (env with v := toRspace _) [_]’
  >> ‘newSt.fp_state.real_sem’ by (unabbrev_all_tac >> gs[])
  >> drule $ INST_TYPE [alpha |-> “:unit”] FloVer_to_CML_real_sim
  >> rpt $ disch_then drule
  >> disch_then $
       qspecl_then [‘toFloVerEnv flEnv (ratExp2realExp e)’, ‘env’, ‘flEnv’,
                    ‘Gamma’, ‘vR'’, ‘domain (usedVars e)’] mp_tac
  >> impl_tac
  >- (
    rpt conj_tac >> gs[real_env_rel_def]
    >> rpt strip_tac >> gs[usedVars_P_sound_def, usedVars_ratExp2realExp]
    >> res_tac >> first_assum $ irule_at Any
    >> gs[toFloVerEnv_def, domain_lookup])
  >> disch_then $ irule_at Any
  >> drule $ INST_TYPE [alpha|-> “:'ffi”] FloVer_to_CML_float_sim_strong
  >> disch_then $ qspecl_then [‘st’,‘toFloVerEnv flEnv (ratExp2realExp e)’, ‘env’,
                               ‘flEnv’, ‘vF’, ‘domain $ usedVars (ratExp2realExp e)’] mp_tac
  >> impl_tac
  >- (
    unabbrev_all_tac
    >> rw[float_env_rel_def, toFloVerEnv_def, CaseEqs["option", "v"]]
    >> first_assum $ irule_at Any >> gs[])
  >> strip_tac
  >> gvs[]
QED

val _ = export_theory();
