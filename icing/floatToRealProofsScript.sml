(*
  Proofs about translation from float computations to real number computations
*)
open icing_rewriterTheory source_to_sourceTheory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory pureExpsTheory floatToRealTheory
     evaluatePropsTheory terminationTheory fpSemPropsTheory mllistTheory;
     local open ml_progTheory in end;
open icingTacticsLib preamble;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "floatToRealProofs";

(** Real-valued identitites preserve real semantics **)

Definition is_real_id_exp_def:
  is_real_id_exp rws (st1:'a semanticPrimitives$state) st2 env e r =
    (evaluate st1 env [realify (rewriteFPexp rws e)] = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = T ⇒
    ∃ choices.
      evaluate st1 env [realify e] =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Definition is_real_id_list_def:
  is_real_id_list rws (st1:'a semanticPrimitives$state) st2 env exps r =
    (evaluate st1 env (MAP realify (MAP (rewriteFPexp rws) exps)) = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = T ⇒
    ∃ choices.
      evaluate st1 env (MAP realify exps) =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Theorem empty_rw_real_id:
   ∀ (st1 st2:'a semanticPrimitives$state) env e r.
     is_real_id_exp [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_real_id_exp_def, rewriteFPexp_def]
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

Definition is_real_id_perform_rewrites_def:
  is_real_id_perform_rewrites rws (st1:'a semanticPrimitives$state) st2 env cfg e r path ⇔
    (evaluate st1 env [realify (perform_rewrites cfg path rws e)] = (st2, Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    st1.fp_state.real_sem ⇒
    ∃ choices.
      evaluate st1 env [realify e] =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Definition is_real_id_optimise_with_plan_def:
  is_real_id_optimise_with_plan plan (st1:'a semanticPrimitives$state) st2 env cfg exps r =
  (evaluate st1 env
   (MAP realify (MAP (λ e. FST (optimise_with_plan cfg plan e)) exps)) = (st2, Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    st1.fp_state.real_sem ⇒
    ∃ choices.
      evaluate st1 env (MAP realify exps) =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Definition is_real_id_stos_pass_with_plan_def:
  is_real_id_stos_pass_with_plans plans (st1:'a semanticPrimitives$state) st2 env cfg exps r =
    (evaluate st1 env
             (MAP realify (MAP FST (stos_pass_with_plans cfg plans exps))) = (st2, Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    st1.fp_state.real_sem ⇒
    ∃ choices.
      evaluate st1 env (MAP realify exps) =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Theorem real_valued_id_compositional:
  ∀ rws opt.
   (∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_real_id_exp rws st1 st2 env e r) ∧
   (∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_real_id_exp [opt] st1 st2 env e r) ⇒
  ∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_real_id_exp ([opt] ++ rws) st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ PairCases_on `opt` \\ simp[rewriteFPexp_def]
  \\ reverse TOP_CASE_TAC \\ fs[]
  >- (fs[fpState_component_equality, semState_comp_eq])
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ strip_tac
  \\ last_x_assum (first_assum o mp_then Any mp_tac) \\ fs[]
  \\ strip_tac
  \\ rename [‘matchesFPexp src e [] = SOME subst’, ‘appFPexp tgt subst = SOME eOpt’]
  \\ ‘eOpt = rewriteFPexp [(src,tgt)] e’ by (fs[rewriteFPexp_def])
  \\ rveq
  \\ last_x_assum (first_assum o mp_then Any mp_tac) \\ fs[]
QED

Theorem lift_real_id_exp_list:
  ∀rws.
    (∀ (st1 st2: 'a semanticPrimitives$state) env e r.
      is_real_id_exp rws st1 st2 env e r) ⇒
  ∀exps (st1 st2:'a semanticPrimitives$state) env r.
    is_real_id_list rws st1 st2 env exps r
Proof
  strip_tac>>strip_tac>>
  simp[is_real_id_list_def]>>Induct
  >- (
    simp[evaluate_def]>>
    rw[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality])>>
  rw[]>>
  fs[Once evaluate_cons]>>
  qpat_x_assum`_ = (st2,_)` mp_tac>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  strip_tac>>rveq>>
  fs[is_real_id_exp_def]>>
  last_x_assum drule>>fs[]>>
  strip_tac>>simp[]>>
  first_x_assum drule>>
  impl_tac >-
    (drule (CONJUNCT1 evaluate_fp_opts_inv)>>simp[])>>
  strip_tac>>fs[]>>
  drule (CONJUNCT1 evaluate_add_choices)>>
  disch_then(qspec_then`choices` assume_tac)>>simp[]>>
  rw[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
QED

Theorem lift_real_id_exp_list_strong:
  ∀rws.
    (∀ (st1 st2: 'a semanticPrimitives$state) env e r.
      is_real_id_exp rws st1 st2 env e r) ⇒
    ∀ (st1 st2:'a semanticPrimitives$state) env exps r.
  is_real_id_list rws st1 st2 env exps r
Proof
  metis_tac[lift_real_id_exp_list]
QED

val path_goal = “(λ path.
       ∀ rws.
         (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
            is_real_id_list rws st1 st2 env exps r) ⇒
         (∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
            is_real_id_perform_rewrites rws st1 st2 env (cfg with optimisations := rws) e r path)) ”
val num_path_goal =
“(λ (n:num, path).
    ∀ rws.
      (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
         is_real_id_list rws st1 st2 env exps r) ⇒
      (∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
         is_real_id_perform_rewrites rws st1 st2 env (cfg with optimisations := rws) e r path)) ”

val simple_goal_tac =
  qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[evaluate_def]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ fs[is_real_id_perform_rewrites_def]
  \\ pop_assum (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th) \\ assume_tac th)
  \\ impl_tac \\ fs[]
  \\ strip_tac \\ fs[]
  \\ TRY (TOP_CASE_TAC \\ fs[])
  \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
  \\ disch_then (fn th => mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices) th ORELSE
                 mp_then Any assume_tac (CONJUNCT2 evaluate_add_choices) th)
  \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality];

val trivial_goal_tac =
  qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[evaluate_def]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ fs[is_real_id_perform_rewrites_def]
  \\ strip_tac
  \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
  \\ impl_tac \\ fs[]
  \\ imp_res_tac evaluate_fp_opts_inv \\ fs[];

val quick_tac =
  res_tac \\ fs[is_real_id_perform_rewrites_def]
  \\ res_tac
\\ fs[realify_def,
      semanticPrimitivesTheory.state_component_equality,
      semanticPrimitivesTheory.fpState_component_equality];

Theorem is_real_id_list_perform_rewrites_lift:
  (∀ rws.
     (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
        is_real_id_list rws st1 st2 env exps r) ⇒
     (∀ path (st1:'a semanticPrimitives$state) st2 env cfg e r.
        is_real_id_perform_rewrites rws st1 st2 env (cfg with optimisations := rws) e r path))
Proof
  mp_tac (Q.SPECL [‘^path_goal’, ‘^num_path_goal’] opt_path_induction)
  \\ impl_tac
  >- (
    conj_tac
    \\ rpt strip_tac \\ res_tac
    \\ rw[is_real_id_perform_rewrites_def]
    \\ Cases_on ‘e’ \\ fs[Once perform_rewrites_def, realify_def]
    \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ fs[is_real_id_perform_rewrites_def]
    \\ pop_assum (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th) \\ assume_tac th)
    \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ disch_then (mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices))
    \\ fs[semanticPrimitivesTheory.state_component_equality,
          semanticPrimitivesTheory.fpState_component_equality])
    >- simple_goal_tac
    >- simple_goal_tac
    >- simple_goal_tac
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ fs[is_real_id_perform_rewrites_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ rveq \\ fs[]
    \\ qpat_x_assum `do_log _ _ _ = SOME _` mp_tac
    \\ simp[do_log_def] \\ TOP_CASE_TAC \\ fs[] \\ rveq \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                  (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
    \\ impl_tac \\ fs[]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ fs[is_real_id_perform_rewrites_def]
    \\ TOP_CASE_TAC \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[]
    \\ qpat_x_assum `do_if _ _ _ = SOME _` mp_tac
    \\ simp[do_if_def] \\ TOP_CASE_TAC \\ fs[] \\ rveq \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                  (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
    \\ impl_tac \\ fs[]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
    >- trivial_goal_tac
    >- trivial_goal_tac
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ fs[is_real_id_perform_rewrites_def]
    \\ TOP_CASE_TAC \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[]
    \\ qpat_x_assum `do_if _ _ _ = SOME _` mp_tac
    \\ simp[do_if_def] \\ TOP_CASE_TAC \\ fs[] \\ rveq \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ fsrw_tac [SATISFY_ss] [semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                  (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
    \\ impl_tac \\ fs[]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ res_tac
    \\ TOP_CASE_TAC \\ fs[is_real_id_perform_rewrites_def]
    \\ rpt strip_tac \\ rveq
    \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                  (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
    \\ impl_tac \\ fs[]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ res_tac \\ fs[is_real_id_perform_rewrites_def]
    \\ rpt strip_tac \\ rveq
    \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                  (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
    \\ impl_tac \\ fs[])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[evaluate_def]
    \\ res_tac \\ fs[is_real_id_perform_rewrites_def]
    \\ rpt strip_tac \\ rveq
    \\ qpat_assum ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
                  (fn th => first_x_assum (fn ithm => mp_then Any mp_tac ithm th))
    \\ impl_tac \\ fs[])
    >- (trivial_goal_tac
        \\ strip_tac
        \\ fs[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ Cases_on ‘p’ \\ fs[perform_rewrites_def, realify_def]
    \\ simp[evaluate_def]
    \\ ntac 4 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    (* Needs lifting lemma *)
    \\ cheat)
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ Cases_on ‘p’ \\ fs[perform_rewrites_def, realify_def]
    \\ Cases_on ‘o'’ \\ fs[]
    \\ simp[evaluate_def, astTheory.getOpClass_def]
    \\ cheat
    (* Needs lifting lemma
    \\ ntac 5 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ cheat) *))
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ Cases_on ‘p’ \\ fs[perform_rewrites_def, realify_def]
    \\ simp[evaluate_def]
    \\ ntac 3 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    (* Needs lifting lemma *)
    \\ cheat)
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ TOP_CASE_TAC
    \\ fs[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ strip_tac \\ fs[is_real_id_list_def]
    \\ first_x_assum $ qspecl_then [‘st1’, ‘st2’, ‘env’, ‘[Lit l]’, ‘r’] mp_tac
    \\ impl_tac \\ fs[])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ TOP_CASE_TAC \\ fs[realify_def]
    \\ fs[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ strip_tac \\ fs[is_real_id_list_def]
    \\ first_x_assum $ qspecl_then [‘st1’, ‘st2’, ‘env’, ‘[Var i]’, ‘r’] mp_tac
    \\ impl_tac \\ fs[realify_def])
    >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ TOP_CASE_TAC \\ fs[realify_def]
    \\ fs[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
    \\ strip_tac \\ fs[is_real_id_list_def]
    \\ first_x_assum $ qspecl_then [‘st1’, ‘st2’, ‘env’, ‘[App o' l]’, ‘r’] mp_tac
    \\ impl_tac \\ fs[realify_def])
    >- (
    res_tac \\ fs[is_real_id_perform_rewrites_def]
    \\ res_tac
    \\ fs[realify_def, semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality])
    \\ quick_tac)
  \\ rpt strip_tac \\ fs[]
QED

Theorem is_real_id_perform_rewrites_optimise_with_plan_lift_sing:
  ∀ plan.
  (∀ rws pth.
     MEM (Apply (pth, rws)) plan ⇒
     (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
        is_real_id_perform_rewrites rws st1 st2 env cfg exps r pth)) ⇒
  (∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
     is_real_id_optimise_with_plan plan st1 st2 env cfg [e] r)
Proof
  Induct_on ‘plan’ \\ fs[]
  >- fs[is_real_id_optimise_with_plan_def, optimise_with_plan_def,
         semanticPrimitivesTheory.state_component_equality,
         semanticPrimitivesTheory.fpState_component_equality]
  \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ fs[is_real_id_optimise_with_plan_def]
  >~ [‘Label s’]
  >- (fs[optimise_with_plan_def]
      \\ rpt strip_tac \\ res_tac
      \\ fs[semanticPrimitivesTheory.state_component_equality,
         semanticPrimitivesTheory.fpState_component_equality])
  >~ [‘Expected e’]
  >- (fs[optimise_with_plan_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ fs[semanticPrimitivesTheory.state_component_equality,
         semanticPrimitivesTheory.fpState_component_equality])
  >~ [‘Apply p’]
  \\ Cases_on ‘p’ \\ fs[optimise_with_plan_def]
  \\ COND_CASES_TAC \\ fs[]
  \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality]
  \\ COND_CASES_TAC \\ fs[]
  >- (
    rpt strip_tac \\ fs[is_real_id_perform_rewrites_def] \\ res_tac
    \\ fs[])
  \\ Cases_on ‘(optimise_with_plan cfg plan
                      (perform_rewrites (cfg with optimisations := r') q r' e))’
  \\ fs[] \\ COND_CASES_TAC
  \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality]
  \\ rpt strip_tac
  \\ first_x_assum $
       qspecl_then [‘st1’, ‘st2’, ‘env’, ‘cfg’,
                    ‘perform_rewrites (cfg with optimisations := r') q r' e’, ‘r’]
       mp_tac
  \\ fs[] \\ strip_tac
  \\ first_x_assum $ qspecl_then [‘r'’, ‘q’] mp_tac
  \\ impl_tac \\ fs[]
  \\ strip_tac \\ fs[is_real_id_perform_rewrites_def]
  \\ res_tac \\ fs[]
QED

Theorem is_real_id_perform_rewrites_optimise_with_plan_lift:
  ∀ plan.
  (∀ rws pth.
     MEM (Apply (pth, rws)) plan ⇒
     (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
        is_real_id_perform_rewrites rws st1 st2 env cfg exps r pth)) ⇒
  (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
     is_real_id_optimise_with_plan plan st1 st2 env cfg exps r)
Proof
  ntac 2 strip_tac
  \\ Induct_on ‘exps’ \\ fs[is_real_id_optimise_with_plan_def]
  >- fs[optimise_with_plan_def,
        semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality]
  \\ drule is_real_id_perform_rewrites_optimise_with_plan_lift_sing
  \\ rpt strip_tac
  \\ simp[Once evaluate_cons]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ $ mp_tac
  \\ simp[Once evaluate_cons, CaseEq"prod", CaseEq"result"]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum (qspecl_then [‘st1’, ‘s'’, ‘env’, ‘cfg’, ‘h’, ‘vs’] strip_assume_tac)
  \\ first_x_assum (qspecl_then [‘s'’, ‘s''’, ‘env’, ‘cfg’, ‘vs'’] strip_assume_tac)
  \\ fs[is_real_id_optimise_with_plan_def]
  \\ rfs[] \\ fs[]
  \\ pop_assum mp_tac  \\ impl_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ strip_tac
  \\ qpat_x_assum ‘evaluate _ _ (MAP realify exps) = _’
                  (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ disch_then (qspec_then ‘choices’ assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem stos_pass_with_plans_correct:
  ∀ plans.
    (∀ plan.
    MEM plan plans ⇒
      ∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
         is_real_id_optimise_with_plan plan st1 st2 env cfg exps r) ⇒
  ∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
   is_real_id_stos_pass_with_plans plans st1 st2 env cfg exps r
Proof
  cheat
QED

(*
local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
      is_real_id_list rws st1 st2 env exps r) ⇒
    (∀ (st1:'a semanticPrimitives$state) st2 env cfg r.
      is_real_id_optimise rws st1 st2 env cfg [e] r)”
  (* P4: string * exp -> bool *)
  val P4 =
  Parse.Term (‘λ (s:string, e). ^P0 e’);
  (* P2: string * string * exp -> bool *)
  val P2 =
  Parse.Term (‘λ (s1:string, s2:string, e). ^P0 e’);
  (* Letrec goal *)
  val P1 =
  Parse.Term (‘λ (l:(string # string # exp) list).
  ∀ p. MEM p l ⇒ ^P2 p’)
  (* P5: pat * exp -> bool *)
  val P5 =
  Parse.Term (‘λ (p:pat, e). ^P0 e’)
  (* P3: pat * exp list -> bool *)
  val P3 =
  Parse.Term (‘λ (l:(pat # exp) list).
    ∀(st1:'a semanticPrimitives$state) env v cfg err_v st2 r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
    evaluate_match st1 env v
      (MAP (λ (p,e). (p,realify (optimise (cfg with optimisations := rws) e))) l) err_v =
      (st2,Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ⇒
    ∃choices.
      evaluate_match st1 env v (MAP (λ(p,e). (p,realify e)) l) err_v =
      (st2 with fp_state := st2.fp_state with choices := choices, Rval r)’);
  (* P6: exp list -> bool *)
  val P6 =
    Parse.Term (‘λ (es:ast$exp list). ∀ e. MEM e es ⇒ ^P0 e’);
  val ind_thm =
    astTheory.exp_induction |> SPEC P0 |> SPEC P1 |> SPEC P2 |> SPEC P3
    |> SPEC P4 |> SPEC P5 |> SPEC P6;
in

Triviality lift_P6_REVERSE:
  ∀ es.
    ^P6 es ⇒
    ∀(st1:'a semanticPrimitives$state) env cfg st2 r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
    evaluate st1 env
      (MAP (realify o optimise (cfg with optimisations := rws)) (REVERSE es)) =
      (st2,Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ⇒
    ∃choices.
      evaluate st1 env
        (MAP realify (REVERSE es)) =
        (st2 with fp_state := st2.fp_state with choices := choices, Rval r)
Proof
  simp[] \\
  Induct_on ‘es’ \\ rpt strip_tac
  >- fs[semState_comp_eq, fpState_component_equality]>>
  fs[evaluate_append]>>
  qpat_x_assum `_ = (st2, _)` mp_tac>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  rfs[]>>
  first_x_assum drule>>
  simp[]>>
  strip_tac>>simp[]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  strip_tac>> rveq>>fs[]>>
  first_x_assum(qspec_then`h` mp_tac)>>simp[is_real_id_optimise_def]>>
  disch_then drule>>
  impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
  strip_tac>>
  drule (CONJUNCT1 evaluate_add_choices)>>
  disch_then(qspec_then`choices` assume_tac)>>
  simp[semState_comp_eq, fpState_component_equality]
QED

Triviality lift_P6:
  ∀ es.
    ^P6 es ⇒
    ∀(st1:'a semanticPrimitives$state) env cfg st2 r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
    evaluate st1 env
      (MAP (realify o optimise (cfg with optimisations := rws)) es) =
      (st2,Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ⇒
    ∃choices.
      evaluate st1 env
        (MAP realify es) =
        (st2 with fp_state := st2.fp_state with choices := choices, Rval r)
Proof
  simp[] \\
  Induct_on ‘es’ \\ rpt strip_tac
  >- fs[semState_comp_eq, fpState_component_equality]>>
  fs[Once evaluate_cons]>>
  qpat_x_assum `_ = (st2, _)` mp_tac>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  first_x_assum(qspec_then`h` mp_tac)>>simp[is_real_id_optimise_def]>>
  disch_then drule >>
  simp[]>>
  strip_tac>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  strip_tac>> rveq>>fs[]>>
  first_x_assum drule>>
  impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
  strip_tac>>
  drule (CONJUNCT1 evaluate_add_choices)>>
  disch_then(qspec_then`choices` assume_tac)>>
  simp[semState_comp_eq, fpState_component_equality]
QED

Theorem is_real_id_list_optimise_lift1:
  (∀ e. ^P0 e) ∧ (∀ l. ^P1 l) ∧ (∀ p. ^P2 p) ∧ (∀ l. ^P3 l) ∧ (∀ p. ^P4 p)
  ∧ (∀ p. ^P5 p) ∧ (∀ l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[is_real_id_optimise_def,optimise_def] \\ rpt strip_tac
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac)
  \\ TRY( (* 15 subogals after *)
    simp[realify_def,evaluate_def]>>
    strip_tac>>
    first_x_assum drule>>
    rpt (disch_then drule)>>simp[] >> NO_TAC)
  >- (
    (* If *)
    simp[evaluate_def, realify_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    imp_res_tac evaluate_sing \\ rveq \\ fs[] \\ rveq >>
    simp[do_if_def]>>
    rpt (IF_CASES_TAC >>simp[])>>
    (* two subgoals *)
    (strip_tac>> first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac >> simp[]>>
    first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac >> simp[]>>
    pop_assum kall_tac>>
    drule (CONJUNCT1 evaluate_add_choices)>>
    disch_then(qspec_then`choices'` assume_tac)>>
    simp[semState_comp_eq, fpState_component_equality]))
  >- (
    (* Log *)
    simp[evaluate_def, realify_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    simp[do_log_def]>>
    IF_CASES_TAC>>simp[]
    >- (
      first_x_assum drule>>
      impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
      strip_tac >> simp[]>>
      strip_tac >> simp[]>>
      first_x_assum drule>>
      impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
      strip_tac >>simp[]>>
      drule (CONJUNCT1 evaluate_add_choices)>>
      disch_then(qspec_then`choices` assume_tac)>>
      simp[semState_comp_eq, fpState_component_equality])>>
    IF_CASES_TAC>>simp[] >> strip_tac>> rveq>>
    first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac >>simp[semState_comp_eq, fpState_component_equality])
  >- (
    (* Let *)
    simp[evaluate_def, realify_def]>>
    ntac 2 (TOP_CASE_TAC >> simp[])>>
    last_x_assum drule >> disch_then drule>>
    simp[]>>
    strip_tac >> simp[]>>
    strip_tac>>
    first_x_assum drule>>
    disch_then drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac>>
    drule (CONJUNCT1 evaluate_add_choices)>>
    disch_then(qspec_then`choices` assume_tac)>>
    simp[semState_comp_eq, fpState_component_equality] )
  >- (
    (* Handle *)
    simp[realify_def,evaluate_def]>>fs[]>>
    ntac 2 (TOP_CASE_TAC>>simp[])
    >- simp[semState_comp_eq, fpState_component_equality]>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ( (* Mat *)
    simp[realify_def,evaluate_def]>>fs[]>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    first_x_assum drule>>simp[]>>
    strip_tac>>simp[]>>
    IF_CASES_TAC>> fs[MAP_MAP_o,LAMBDA_PROD,o_DEF]>>
    strip_tac>> first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac>>
    drule (CONJUNCT2 evaluate_add_choices)>>
    disch_then(qspec_then`choices` assume_tac)>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ((* FpOptimise *)
    simp[realify_def,evaluate_def]>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    strip_tac>>rveq>>
    qmatch_asmsub_abbrev_tac`optimise ccfg e`>>
    `ccfg = ccfg with optimisations := rws` by
      fs[Abbr`ccfg`]>>
    qpat_x_assum`_ = (q,_)` mp_tac>>
    pop_assum SUBST1_TAC>>
    strip_tac>>
    first_x_assum drule>> disch_then drule>>
    impl_tac>-
      simp[Abbr`ccfg`]>>
    strip_tac>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ( (* Fun *)
    simp[realify_def,evaluate_def]>>
    fs[semState_comp_eq, fpState_component_equality])
  >- ( (* Raise *)
    simp[realify_def,evaluate_def]>>
    every_case_tac>>simp[])
  >- ( (* Var *)
    simp[realify_def,evaluate_def]>>
    every_case_tac>>simp[semState_comp_eq, fpState_component_equality])
  >- ((* App *)
    fs[]>>
    qspec_then `l` mp_tac (lift_P6_REVERSE |> SIMP_RULE std_ss [is_real_id_optimise_def])>>
    impl_tac >- (
      simp[]>>
      metis_tac[] )>>
    simp[]>>
    strip_tac>>
    IF_CASES_TAC>>simp[]>>
    fs[is_real_id_list_def]
    >- (
      qmatch_goalsub_abbrev_tac`_ rws exp`>>
      strip_tac>>
      first_x_assum(qspecl_then [`st1`,`st2`,`env`,`[exp]`,`r`] mp_tac)>>
      simp[]>>
      strip_tac>>
      qpat_x_assum`_ = (st2,Rval r)`kall_tac>>
      pop_assum mp_tac>>
      fs[Abbr`exp`,realify_def]>>
      Cases_on`o'`>>simp[evaluate_def,astTheory.getOpClass_def]>>
      TRY( (* 50 cases *)
      ntac 2(TOP_CASE_TAC>>simp[])>>
      fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
      first_x_assum drule>>simp[]>>
      strip_tac>>simp[]>>
      `(λa. realify a) = realify` by
        fs[ETA_AX]>>
      simp[]>>
      rpt(TOP_CASE_TAC>>simp[])>>
      simp[semState_comp_eq, fpState_component_equality]>> NO_TAC)
      >- (
        strip_tac>>
        TOP_CASE_TAC>>fs[]
        >- simp[semState_comp_eq, fpState_component_equality,dec_clock_def]>>
        TOP_CASE_TAC>>fs[]
        >- (
          pop_assum mp_tac>> fs[evaluate_def]>>
          TOP_CASE_TAC>>simp[]>>
          TOP_CASE_TAC>>simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          first_x_assum drule>> simp[]>>
          strip_tac>>simp[]>>
          ntac 4 (TOP_CASE_TAC>>simp[])>>
          simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
        TOP_CASE_TAC>>fs[]
        >- (
          qpat_x_assum`_ = (_ , Rval r)` mp_tac>>
          simp[Once evaluate_def]>>
          ntac 2 (TOP_CASE_TAC>>simp[])>>
          first_x_assum drule >> simp[]>>
          strip_tac>> simp[evaluate_def]>>
          simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          ntac 4 (TOP_CASE_TAC>>simp[])>>
          simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
        TOP_CASE_TAC>>fs[]
        >- (
          pop_assum mp_tac>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          every_case_tac>>simp[]>>strip_tac>>rveq>>fs[]>>
          rveq>>fs[]>>
          first_assum(qspec_then`h` mp_tac)>>
          first_assum(qspec_then`h'` mp_tac)>>
          first_x_assum(qspec_then`h''` mp_tac)>>
          simp[]>>
          ntac 3 strip_tac>>
          first_x_assum drule >> simp[] >> strip_tac>>
          simp[evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          last_x_assum drule >>
          impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
          strip_tac>>
          drule (CONJUNCT1 evaluate_add_choices)>>
          disch_then(qspec_then`choices'` assume_tac)>>
          fs[]>>
          last_x_assum drule >>
          impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
          strip_tac>>
          drule (CONJUNCT1 evaluate_add_choices)>>
          disch_then(qspec_then` choices' + choices'' − q.fp_state.choices` assume_tac)>>
          fs[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])
        >>
        pop_assum mp_tac>>
        fs[evaluate_def, MAP_REVERSE,MAP_MAP_o,o_DEF]>>
        ntac 2 (TOP_CASE_TAC>>simp[])>>
        simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        first_x_assum drule>>
        simp[]>>
        strip_tac>>
        `(λa. realify a) = realify` by
          fs[ETA_AX]>>
        simp[]>>
        rpt (TOP_CASE_TAC>>simp[])>>
        simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])
      >>
      ntac 2(TOP_CASE_TAC>>simp[])>>
      fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
      first_x_assum drule>>simp[]>>
      strip_tac>>simp[]>>
      `(λa. realify a) = realify` by
        fs[ETA_AX]>>
      simp[]>>
      rpt(TOP_CASE_TAC>>simp[])>>
      simp[dec_clock_def]>> strip_tac>>
      drule (CONJUNCT1 evaluate_add_choices)>>
      disch_then(qspec_then`choices'` assume_tac)>>
      fs[]>>
      simp[semState_comp_eq, fpState_component_equality])
    >>
    simp[realify_def]>>
    Cases_on`o'`>>simp[evaluate_def,astTheory.getOpClass_def]>>
    (* 50 cases *)
    TRY(
    ntac 2(TOP_CASE_TAC>>simp[])>>
    fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
    first_x_assum drule>>simp[]>>
    strip_tac>>simp[]>>
    `(λa. realify a) = realify` by
      fs[ETA_AX]>>
    simp[]>>
    rpt(TOP_CASE_TAC>>simp[])>>
    simp[semState_comp_eq, fpState_component_equality]>> NO_TAC)
    >- (
      strip_tac>>
      TOP_CASE_TAC>>fs[]
      >- simp[semState_comp_eq, fpState_component_equality,dec_clock_def]>>
      TOP_CASE_TAC>>fs[]
      >- (
        pop_assum mp_tac>> fs[evaluate_def]>>
        TOP_CASE_TAC>>simp[]>>
        TOP_CASE_TAC>>simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        first_x_assum drule>> simp[]>>
        strip_tac>>simp[]>>
        ntac 4 (TOP_CASE_TAC>>simp[])>>
        simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
      TOP_CASE_TAC>>fs[]
      >- (
        qpat_x_assum`_ = (_ , Rval r)` mp_tac>>
        simp[Once evaluate_def]>>
        ntac 2 (TOP_CASE_TAC>>simp[])>>
        first_x_assum drule >> simp[]>>
        strip_tac>> simp[evaluate_def]>>
        simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        ntac 4 (TOP_CASE_TAC>>simp[])>>
        simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
      TOP_CASE_TAC>>fs[]
      >- (
        pop_assum mp_tac>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        every_case_tac>>simp[]>>strip_tac>>rveq>>fs[]>>
        rveq>>fs[]>>
        first_assum(qspec_then`h` mp_tac)>>
        first_assum(qspec_then`h'` mp_tac)>>
        first_x_assum(qspec_then`h''` mp_tac)>>
        simp[]>>
        ntac 3 strip_tac>>
        first_x_assum drule >> simp[] >> strip_tac>>
        simp[evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        last_x_assum drule >>
        impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
        strip_tac>>
        drule (CONJUNCT1 evaluate_add_choices)>>
        disch_then(qspec_then`choices` assume_tac)>>
        fs[]>>
        last_x_assum drule >>
        impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
        strip_tac>>
        drule (CONJUNCT1 evaluate_add_choices)>>
        disch_then(qspec_then` choices + choices' − q.fp_state.choices` assume_tac)>>
        fs[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])
      >>
      pop_assum mp_tac>>
      fs[evaluate_def, MAP_REVERSE,MAP_MAP_o,o_DEF]>>
      ntac 2 (TOP_CASE_TAC>>simp[])>>
      simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
      first_x_assum drule>>
      simp[]>>
      strip_tac>>
      `(λa. realify a) = realify` by
        fs[ETA_AX]>>
      simp[]>>
      rpt (TOP_CASE_TAC>>simp[])>>
      simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
    ntac 2(TOP_CASE_TAC>>simp[])>>
    fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
    first_x_assum drule>>simp[]>>
    strip_tac>>simp[]>>
    `(λa. realify a) = realify` by
      fs[ETA_AX]>>
    simp[]>>
    rpt(TOP_CASE_TAC>>simp[])>>
    simp[dec_clock_def]>> strip_tac>>
    drule (CONJUNCT1 evaluate_add_choices)>>
    disch_then(qspec_then`choices` assume_tac)>>
    fs[]>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ((* Con *)
    simp[realify_def,evaluate_def]>>
    IF_CASES_TAC>>simp[]>>
    ntac 2(TOP_CASE_TAC>>simp[])>>
    qspec_then `l` mp_tac (lift_P6_REVERSE |> SIMP_RULE std_ss [is_real_id_optimise_def])>>
    impl_tac >- (
      simp[]>>
      metis_tac[] )>>
    disch_then drule>>
    fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
    disch_then drule>>
    simp[]>>
    strip_tac>>
    TOP_CASE_TAC>> simp[] >>
    strip_tac>> rveq>>
    `(λa. realify a) = realify` by
      fs[ETA_AX]>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ( (* Letrec *)
    simp[realify_def,evaluate_def]>>
    IF_CASES_TAC>>simp[]>>
    strip_tac>> first_x_assum drule>>
    disch_then drule >> simp[])
  >- (* Lit *)
    simp[semState_comp_eq, fpState_component_equality]
  >- (
    pairarg_tac>>fs[evaluate_def]>>
    every_case_tac>>fs[]
    >- (
      first_x_assum drule>>
      simp[] )>>
    last_x_assum drule >> simp[])>>
  simp[semState_comp_eq, fpState_component_equality]
QED
end;

Theorem is_real_id_list_optimise_lift:
  (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
  (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
    is_real_id_optimise rws st1 st2 env cfg exps r)
Proof
  rw[]>>
  assume_tac is_real_id_list_optimise_lift1>>
  fs[]>>
  pop_assum(qspec_then `exps` assume_tac)>>
  assume_tac lift_P6>>
  fs[]>>
  pop_assum(qspec_then `exps` assume_tac)>>
  rfs[]>>
  simp[is_real_id_optimise_def]>>
  strip_tac>>
  fs[MAP_MAP_o]>>
  first_x_assum drule>>
  simp[]
QED
*)

Theorem isPureExp_no_optimisations:
  (∀e.
    isPureExp e ⇒
    isPureExp ((no_optimisations cfg) e)) ∧
  (∀es.
    isPureExpList es ⇒
    isPureExpList (MAP (no_optimisations cfg) es)) ∧
  (∀pes.
    isPurePatExpList pes ⇒
    isPurePatExpList (MAP (λ(p,e). (p,(no_optimisations cfg) e)) pes))
Proof
  ho_match_mp_tac isPureExp_ind>>
  rw[isPureExp_def, source_to_sourceTheory.no_optimisations_def]>>fs[] >>
  `(λa. (no_optimisations cfg) a) = (no_optimisations cfg)` by
      simp[FUN_EQ_THM]>>
  simp[]
QED

Theorem realify_no_optimisations_commutes_IMP:
  ∀ e cfg e2.
  realify (no_optimisations cfg e) = e2 ⇒
  no_optimisations cfg (realify e) = e2
Proof
  ho_match_mp_tac realify_ind \\ rpt strip_tac \\ fs[realify_def, no_optimisations_def]
  \\ rveq \\ fs[no_optimisations_def]
  >- (
   Induct_on ‘pes’ \\ fs[]
   \\ rpt strip_tac
   >- (Cases_on ‘h’ \\ fs[realify_def, no_optimisations_def])
   \\ first_x_assum irule
   \\ strip_tac \\ metis_tac [])
  >- (Induct_on ‘exps’ \\ fs[])
  >- (Cases_on ‘op’ \\ fs[realify_def, no_optimisations_def, CaseEq"list"]
      \\ TRY (Induct_on ‘exps’ \\ fs[no_optimisations_def] \\ NO_TAC)
      \\ Cases_on ‘exps’ \\ fs[no_optimisations_def]
      \\ Cases_on ‘t’ \\ fs[no_optimisations_def]
      \\ Cases_on ‘t'’ \\ fs[no_optimisations_def]
      \\ Cases_on ‘t’ \\ fs[no_optimisations_def]
      \\ Induct_on ‘t'’ \\ fs[no_optimisations_def]
      \\ rpt strip_tac \\ first_x_assum irule \\ metis_tac[])
  \\ Induct_on ‘pes’ \\ fs[] \\ rpt strip_tac
  >- (Cases_on ‘h’ \\ fs[realify_def, no_optimisations_def])
  \\ first_x_assum irule
  \\ strip_tac \\ metis_tac []
QED

Theorem isPureExp_realify:
  (∀e.
    isPureExp e ⇒
    isPureExp (realify e)) ∧
  (∀es.
    isPureExpList es ⇒
    isPureExpList (MAP realify es)) ∧
  (∀pes.
    isPurePatExpList pes ⇒
    isPurePatExpList (MAP (λ(p,e). (p,realify e)) pes))
Proof
  ho_match_mp_tac isPureExp_ind>>
  rw[isPureExp_def, realify_def]>>fs[]
  >-
    (Cases_on`e`>>simp[isPureExp_def, realify_def])
  >- (
    `(λa. realify a) = realify` by
        fs[ETA_AX]>>
    simp[])>>
  TOP_CASE_TAC>>
  `(λa. realify a) = realify` by fs[ETA_AX]>>
  fs[isPureExp_def,isPureOp_def]>>
  every_case_tac>>fs[isPureOp_def,isPureExp_def]>>
  simp[isPureOp_def]
QED

Theorem realify_no_optimisations_comm:
  realify (no_optimisations cfg e) = no_optimisations cfg (realify e)
Proof
  metis_tac [realify_no_optimisations_commutes_IMP]
QED

val _ = export_theory();
