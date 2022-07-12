(*
  Proofs about translation from floating-point computations to real-number
  computations. Needed to prove simulations in the end-to-end correctness
  theorems.
*)
open icing_rewriterTheory source_to_source2Theory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory pureExpsTheory floatToRealTheory
     evaluatePropsTheory fpSemPropsTheory mllistTheory;
     local open ml_progTheory in end;
open icingTacticsLib preamble;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "floatToRealProofs";

(** Real-valued identitites preserve real semantics **)

Definition freeVars_real_bound_def:
  freeVars_real_bound e env =
    ∀ x. x IN FV e ⇒ ∃ r. nsLookup env.v x = SOME (Real r)
End

Definition is_real_id_exp_def:
  is_real_id_exp rws (st1:'a semanticPrimitives$state) st2 env e r =
    (evaluate st1 env [realify (rewriteFPexp rws e)] = (st2, Rval r) ∧
     freeVars_real_bound e env ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = T ⇒
    ∃ choices.
      evaluate st1 env [realify e] =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Definition freeVars_list_real_bound_def:
  freeVars_list_real_bound es env =
  ∀ x. x IN FV_list es ⇒ ∃ r. nsLookup env.v x = SOME (Real r)
End

Definition is_real_id_list_def:
  is_real_id_list rws (st1:'a semanticPrimitives$state) st2 env exps r =
    (evaluate st1 env (MAP realify (MAP (rewriteFPexp rws) exps)) = (st2, Rval r) ∧
     freeVars_list_real_bound exps env ∧
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

Definition freeVars_realExp_bound_def:
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
    Here (Lit l) =
      T ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
                          Here  (App op exps) =
    (if isFpArithExp (App op exps) then freeVars_real_bound (App op exps) env
    else T) ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
                          Here  (Var x) = T ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
                          Here  e = T ∧
  (* If we are not at the end of the path, further navigate through the AST *)
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg (Left _)
                           (Lit l) = T ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg (Left _)
                           (Var x) = T ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg (Center path)
                           (Raise e) =
    freeVars_realExp_bound st1 st2 env cfg path  e ∧
  (* We cannot support "Handle" expressions because we must be able to reorder exceptions *)
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg path
                           (Handle e pes) = T ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (ListIndex (i, path)) (Con mod exps) =
  (EVERYi (λ n e. if (n = i)
                  then (freeVars_realExp_bound st1 st2 env cfg path  e)
                  else T) exps) ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left _)  (Fun s e) = T ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (ListIndex (i, path)) (App op exps) =
  (EVERYi (λ n e. if (n = i)
                  then (freeVars_realExp_bound st1 st2 env cfg path  e)
                  else T) exps) ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (Log lop e2 e3) =
    freeVars_realExp_bound st1 st2 env cfg path  e2 ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Right path) (Log lop e2 e3) =
    freeVars_realExp_bound st1 st2 env cfg path  e3 ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (If e1 e2 e3) =
    freeVars_realExp_bound st1 st2 env cfg path  e1 ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (If e1 e2 e3) =
    freeVars_realExp_bound st1 st2 env cfg path  e2 ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Right path) (If e1 e2 e3) =
    freeVars_realExp_bound st1 st2 env cfg path  e3 ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (Mat e pes) =
    freeVars_realExp_bound st1 st2 env cfg path  e ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (ListIndex (i, path)) (Mat e pes) =
  EVERYi (λ n (p, e').
           if (n = i) then
             ∀ v env_v.
               pmatch env.c st1.refs p (HD v) [] = Match env_v ⇒
               ∀ st1 st2. freeVars_realExp_bound st1 st2
                 (env with v := nsAppend (alist_to_ns env_v) env.v) cfg path e'
           else T) pes ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (Let so e1 e2) =
    (freeVars_realExp_bound st1 st2 env cfg path  e1) ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Right path)  (Let so e1 e2) =
  (∀ r.
     evaluate st1 env [realify e1] = (st2, Rval r) ⇒
     (∀ st1 st2.
        freeVars_realExp_bound st1 st2 (env with v := nsOptBind so (HD r) env.v)
                                       cfg path e2)) ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (Letrec ses e) =
  (ALL_DISTINCT (MAP (λ(x,y,z). x) (MAP (λ (x,y,e). (x,y,realify e)) ses)) ⇒
   freeVars_realExp_bound st1 st2 (env with v :=
                                   build_rec_env (MAP (λ (x,y,e). (x,y,realify e)) ses) env env.v)
                          cfg path e) ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (Tannot e t) =
    freeVars_realExp_bound st1 st2 env cfg path e ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (Lannot e l) =
    freeVars_realExp_bound st1 st2 env cfg path e ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (FpOptimise sc e) =
    freeVars_realExp_bound st1 st2 env (cfg with canOpt := if sc = Opt then T else F) path e ∧
  freeVars_realExp_bound (st1:'a semanticPrimitives$state) st2 env cfg _ e = T
End

Definition is_real_id_perform_rewrites_def:
  is_real_id_perform_rewrites rws (st1:'a semanticPrimitives$state) st2 env cfg e r path ⇔
    (evaluate st1 env [realify (perform_rewrites cfg path rws e)] = (st2, Rval r) ∧
     (∀ (st1:'a semanticPrimitives$state) st2. freeVars_realExp_bound st1 st2 env cfg path e) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt ≠ Strict ∧
     st1.fp_state.real_sem ⇒
     ∃ choices.
       evaluate st1 env [realify e] =
       (st2 with fp_state := st2.fp_state with
                                <| choices := choices|>, Rval r))
End

Definition freeVars_realPlan_bound_def:
  freeVars_realPlan_bound (st1:'a semanticPrimitives$state) st2 env cfg [] e = T ∧
  freeVars_realPlan_bound (st1:'a semanticPrimitives$state) st2 env cfg (Label s :: realPlan) e =
    freeVars_realPlan_bound st1 st2 env cfg realPlan e ∧
  freeVars_realPlan_bound (st1:'a semanticPrimitives$state) st2 env cfg (Expected e_opt :: realPlan) e =
    freeVars_realPlan_bound (st1:'a semanticPrimitives$state) st2 env cfg realPlan e ∧
  freeVars_realPlan_bound (st1:'a semanticPrimitives$state) st2 env cfg (Apply (path, rewrites)::rest) e =
    (freeVars_realExp_bound st1 st2 env cfg path e ∧
    freeVars_realPlan_bound st1 st2 env cfg rest (perform_rewrites cfg path rewrites e))
End

Definition is_real_id_optimise_with_plan_def:
  is_real_id_optimise_with_plan plan (st1:'a semanticPrimitives$state) st2 env cfg exps r =
  (evaluate st1 env
   (MAP realify (MAP (λ e. FST (optimise_with_plan cfg plan e)) exps)) = (st2, Rval r) ∧
   (∀ e. MEM e exps ⇒
         (∀ (st1:'a semanticPrimitives$state) st2. freeVars_realPlan_bound st1 st2 env cfg plan e)) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    st1.fp_state.real_sem ⇒
    ∃ choices.
      evaluate st1 env (MAP realify exps) =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Theorem is_real_id_perform_rewrites_empty:
  ∀ rws path.
    MEM (Apply (path, rws)) [] ⇒
    ∀ st1 st2 env cfg exps r.
      is_real_id_perform_rewrites rws st1 st2 env cfg exps r path
Proof
  fs[]
QED

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
  \\ fs[fpState_component_equality, semState_comp_eq]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ strip_tac
  \\ last_x_assum (first_assum o mp_then Any mp_tac) \\ fs[]
  \\ impl_tac
  >- (
    gs[freeVars_real_bound_def]
    \\ qspecl_then [‘opt1’, ‘opt0’, ‘e’, ‘x'’, ‘x’, ‘[]’,
                    ‘λ x. ∃ r. nsLookup env.v x = SOME (Real r)’]
                   mp_tac icing_rewriterProofsTheory.match_preserves_FV
    \\ impl_tac \\ gs[substLookup_def])
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
  impl_tac >- (gs[freeVars_list_real_bound_def, freeVars_real_bound_def]) >>
  strip_tac>>simp[]>>
  first_x_assum drule>>
  impl_tac >-
   (fs[freeVars_list_real_bound_def]
    >> drule (CONJUNCT1 evaluate_fp_opts_inv)>>simp[])>>
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

val no_change_tac =
  (qpat_x_assum ‘evaluate _ _ [_] = _’ (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
   \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] strip_assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality]
   \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’, ‘st2.fp_state.opts’, ‘st2.fp_state.choices’]
   \\ imp_res_tac (CONJUNCT1 evaluate_add_choices)
   \\ fs[semState_comp_eq, fpState_component_equality]);

fun ext_eval_tac t rws opts =
  qpat_x_assum t $ mp_then Any (qspecl_then [rws, opts] strip_assume_tac)
             (CONJUNCT1 evaluate_fp_rws_append);
fun ext_evalm_tac t rws opts =
  qpat_x_assum t $ mp_then Any (qspecl_then [rws, opts] strip_assume_tac)
             (CONJUNCT2 evaluate_fp_rws_append);
fun ext_choices_tac t choices =
      qpat_x_assum t $ mp_then Any (qspec_then choices assume_tac) (CONJUNCT1 evaluate_add_choices)
fun ext_choicesm_tac t choices =
      qpat_x_assum t $ mp_then Any (qspec_then choices assume_tac) (CONJUNCT1 $ CONJUNCT2 evaluate_add_choices)
fun ext_choicesd_tac t choices =
      qpat_x_assum t $ mp_then Any (qspec_then choices assume_tac) (CONJUNCT2 $ CONJUNCT2 evaluate_add_choices)

fun get_IH t =
  qpat_x_assum t (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))

Theorem perform_rewrites_lift_reverse_real:
  ∀ exps (st1:'a semanticPrimitives$state) st2 env vs cfg path rws i.
  (∀ (st1:'a semanticPrimitives$state) st2.
    EVERYi
      (λn e. n = i ⇒ freeVars_realExp_bound st1 st2 env cfg path e)
      exps) ∧
  (∀ e. MEM e exps ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env r.
         (∀ (st1:'a semanticPrimitives$state) st2. freeVars_realExp_bound st1 st2 env cfg path e) ∧
         (cfg.canOpt ⇔
            st1.fp_state.canOpt = FPScope Opt) ∧
         st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ∧
         evaluate st1 env [realify (perform_rewrites cfg path rws e)] = (st2,Rval r) ⇒
         ∃ choices.
           evaluate st1 env [realify e] =
           (st2 with fp_state := st2.fp_state with choices := choices, Rval r)) ∧
  (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
  st1.fp_state.canOpt ≠ Strict ∧
  st1.fp_state.real_sem ∧
  evaluate st1 env
           (REVERSE (MAPi
                     ($o (λ a. realify a) o
                     λn e. if n = i then perform_rewrites cfg path rws e else e)
                     exps)) = (st2,Rval vs) ⇒
  ∃ choices.
    evaluate st1 env (REVERSE (MAP realify exps)) =
    (st2 with fp_state := st2.fp_state with choices := choices, Rval vs)
Proof
  Induct_on ‘exps’
  >- (simp[evaluate_def] \\ rpt strip_tac
    \\ gs[semState_comp_eq, fpState_component_equality])
  \\ rpt strip_tac \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[Once evaluate_cons, Once evaluate_append]
  (* Case split where we optimise *)
  \\ Cases_on ‘i = 0’ \\ gs[]
  >~ [‘i = 0’]
  >- (
    rveq
    \\ ‘$o (λ a. realify a) o (λ n e. if n = 0 then perform_rewrites cfg path rws e else e) o SUC =
        λ n e. realify e’
       by (fs[FUN_EQ_THM])
    \\ pop_assum (gs o single)
    \\ simp[CaseEq"result", CaseEq"prod"]
    \\ rpt strip_tac \\ rveq \\ gs[] \\ rveq
    \\ gs[EVERYi_def]
    \\ rename1 ‘evaluate st2 env [realify (perform_rewrites cfg path rws e1)] = (st3, Rval v1)’
    \\ first_x_assum $ qspec_then ‘e1’ mp_tac
    \\ simp[] \\ disch_then (fn ith => first_assum (fn th => mp_then Any mp_tac ith th))
    \\ impl_tac
    >- (
      rpt conj_tac
      >- (
        rpt strip_tac
        \\ first_x_assum $ qspecl_then [‘st1'’, ‘st2'’] assume_tac \\ gs[])
      \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ strip_tac \\ simp[Once evaluate_append]
    \\ ‘MAPi (λ n e. realify e) exps = MAP realify exps’
       by (AP_THM_TAC \\ gs[FUN_EQ_THM] \\ rpt $ pop_assum kall_tac
           \\ Induct_on ‘x’ \\ gs[]
           \\ ‘(λ n e. realify e) o SUC = λ n e. realify e’ by gs[FUN_EQ_THM]
           \\ pop_assum $ gs o single)
    \\ pop_assum $ gs o single
    \\ gs[semState_comp_eq, fpState_component_equality])
  \\ ‘$o (λ e. realify e) o (λ n e. if n = i then perform_rewrites cfg path rws e else e) o SUC =
      $o (λ e. realify e) o (λ n e. if n = (i-1) then perform_rewrites cfg path rws e else e)’
     by (fs[FUN_EQ_THM] \\ rpt strip_tac \\ COND_CASES_TAC \\ gs[])
  \\ pop_assum (once_rewrite_tac o single)
  \\ simp[CaseEq"result", CaseEq"prod"]
  \\ rpt strip_tac \\ rveq \\ gs[] \\ rveq
  \\ gs[EVERYi_def]
  \\ qpat_x_assum ‘evaluate _ _ (REVERSE _) = _’
                  (fn th => last_x_assum (fn ith => mp_then Any mp_tac ith th))
  \\ impl_tac
  >- (
    gs[] \\ rpt strip_tac
    \\ first_x_assum (qspecl_then [‘st1'’, ‘st2’] assume_tac)
    \\ ‘(λ n e. n = i - 1 ⇒ freeVars_realExp_bound st1' st2 env cfg path e) =
          (λ n e. n = i ⇒ freeVars_realExp_bound st1' st2 env cfg path e) o SUC’
       suffices_by (pop_assum (gs o single))
    \\ gs[FUN_EQ_THM] \\ rpt strip_tac \\ gs[] \\ EQ_TAC
    \\ rpt strip_tac \\ gs[])
  \\ strip_tac
  \\ simp[Once evaluate_append]
  \\ ext_choices_tac ‘evaluate _ _ [realify h] = _’ ‘choices’
  \\ gs[semState_comp_eq, fpState_component_equality]
QED

Theorem perform_rewrites_lift_match:
  ∀ pes (st1:'a semanticPrimitives$state) st2 env vs cfg path rws i v.
  (∀ (st1:'a semanticPrimitives$state) st2.
  EVERYi (λ n (p, e').
           n = i ⇒
           ∀ v env_v.
             pmatch env.c st1.refs p (HD v) [] = Match env_v ⇒
             ∀ (st1:'a semanticPrimitives$state) st2.
               freeVars_realExp_bound st1 st2
               (env with v := nsAppend (alist_to_ns env_v) env.v) cfg path e') pes) ∧
  (∀ p e. MEM (p,e) pes ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env r.
         (∀ (st1:'a semanticPrimitives$state) st2. freeVars_realExp_bound st1 st2 env cfg path e) ∧
         (cfg.canOpt ⇔
            st1.fp_state.canOpt = FPScope Opt) ∧
         st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ∧
         evaluate st1 env [realify (perform_rewrites cfg path rws e)] = (st2,Rval r) ⇒
         ∃ choices.
           evaluate st1 env [realify e] =
           (st2 with
            fp_state := st2.fp_state with choices := choices, Rval r)) ∧
  (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
  st1.fp_state.canOpt ≠ Strict ∧
  st1.fp_state.real_sem ∧
  evaluate_match st1 env (HD v)
                 (MAPi
                  ($o (λ (p,e). (p, realify e)) o
                   (λn (p,e). if n = i then (p, perform_rewrites cfg path rws e) else (p,e)))
            pes) bind_exn_v = (st2,Rval vs) ⇒
  ∃ choices.
    evaluate_match st1 env (HD v) (MAP (λ (p, e). (p, realify e)) pes) bind_exn_v =
    (st2 with fp_state :=
     st2.fp_state with choices := choices, Rval vs)
Proof
  Induct_on ‘pes’
  >- (simp[evaluate_def] \\ rpt strip_tac
    \\ gs[semState_comp_eq, fpState_component_equality])
  \\ rpt strip_tac \\ qpat_x_assum `evaluate_match _ _ _ _ _= _` mp_tac
  \\ Cases_on ‘h’
  (* Case split where we optimise *)
  \\ Cases_on ‘i = 0’ \\ gs[]
  >~ [‘i = 0’]
  >- (
    rveq \\ simp[SimpL “$==>”, Once evaluate_def]
    \\ ‘$o (λ (p, e). (p, realify e)) o
        (λ n (p:pat, e). if n = 0 then (p, perform_rewrites cfg path rws e) else (p, e)) o SUC =
        λ n (p,e). (p, realify e)’
       by (fs[FUN_EQ_THM] \\ rpt strip_tac \\ Cases_on ‘x’ \\ gs[])
    \\ pop_assum (gs o single)
    \\ COND_CASES_TAC \\ gs[]
    \\ simp[CaseEq"match_result"] \\ rpt strip_tac
    (* Optimised but did not match *)
    >- (
      simp[Once evaluate_def]
      \\ ‘MAPi (λ n (p,e). (p, realify e)) pes = MAP (λ (p, e). (p, realify e)) pes’
         by (rpt $ pop_assum kall_tac \\ Induct_on ‘pes’ \\ gs[]
             \\ pop_assum (gs o single o GSYM)
             \\ AP_THM_TAC \\ AP_TERM_TAC \\ gs[FUN_EQ_THM])
      \\ pop_assum (gs o single)
      \\ gs[semState_comp_eq, fpState_component_equality])
    \\ first_x_assum $ qspecl_then [‘q’, ‘r’] mp_tac \\impl_tac \\ gs[]
    \\ strip_tac
    \\ get_IH ‘evaluate _ _ _ = _’
    \\ impl_tac
    >- (
      gs[EVERYi_def] \\ rpt strip_tac
      \\ first_x_assum (qspecl_then [‘st1’] strip_assume_tac)
      \\ first_x_assum irule \\ asm_exists_tac \\ gs[])
    \\ strip_tac
    \\ gs[Once evaluate_def, semState_comp_eq, fpState_component_equality])
  \\ ‘$o (λ (p:pat, e). (p, realify e)) o
      (λ n (p:pat,e). if n = i then (p, perform_rewrites cfg path rws e) else (p,e)) o SUC =
     $o (λ (p:pat, e). (p, realify e)) o (λ n (p,e). if n = i-1 then (p, perform_rewrites cfg path rws e) else (p,e))’
    by (gs[FUN_EQ_THM] \\ gs[] \\ rpt strip_tac
        \\ Cases_on ‘x'’  \\ gs[] \\ COND_CASES_TAC \\ gs[])
  \\ pop_assum (gs o single)
  \\ simp[SimpL “$==>”, evaluate_def]
  \\ COND_CASES_TAC \\ gs[]
  \\ simp[CaseEq"match_result"] \\ rpt strip_tac
  (* First pattern did not match *)
  >- (
    get_IH ‘evaluate_match _ _ _ _ _ = _’ \\ impl_tac
    >- (
      gs[] \\ conj_tac
        >- (
          rpt strip_tac
          \\ ‘(λ n (p,e).
                n = i - 1 ⇒
                ∀ v env_v.
                  pmatch env.c st1'.refs p (HD v) [] = Match env_v ⇒
                 ∀(st1:'a semanticPrimitives$state) st2.
                   freeVars_realExp_bound st1 st2
                     (env with v := nsAppend (alist_to_ns env_v) env.v) cfg
                     path e) =
              (λ n (p,e). n = i ⇒
                ∀ v env_v.
                  pmatch env.c st1'.refs p (HD v) [] = Match env_v ⇒
                 ∀(st1:'a semanticPrimitives$state) st2.
                   freeVars_realExp_bound st1 st2
                     (env with v := nsAppend (alist_to_ns env_v) env.v) cfg
                     path e) o SUC’
             by (gs[FUN_EQ_THM] \\ Cases_on ‘x’ \\ gs[] \\ rpt strip_tac \\ gs[] \\ EQ_TAC
                 \\ rpt strip_tac
                 >- (‘n = i-1’ by gs[] \\ res_tac \\ first_x_assum irule)
                 \\ ‘SUC n = i’ by gs[] \\ res_tac \\ first_x_assum irule)
          \\ pop_assum $ once_rewrite_tac o single
          \\ gs[EVERYi_def])
      \\ rpt strip_tac \\ first_x_assum $ qspecl_then [‘p’, ‘e’] mp_tac
      \\ impl_tac \\ gs[])
    \\ strip_tac
    \\ fsrw_tac [SATISFY_ss][evaluate_def, semState_comp_eq, fpState_component_equality])
  (* First pattern did match *)
  \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality]
QED

Theorem evaluate_case_case:
  (case
  (case evaluate st1 env es of
   | (st2, Rval r) => f st2 r
   | (st2, Rerr e) => (st2, Rerr e)) of
  | (st2, Rval r) => g st2 r
  | (st2, Rerr e) => (st2, Rerr e)) =
  case evaluate st1 env es of
  | (st2, Rerr e) => (st2, Rerr e)
  | (st2, Rval r) =>
  (case f st2 r of
   | (st2, Rerr e) => (st2, Rerr e)
   | (st2, Rval r) =>
   g st2 r)
Proof
  TOP_CASE_TAC \\ pop_assum mp_tac
  \\ ntac 2 TOP_CASE_TAC \\ fs[]
  \\ strip_tac \\ rveq \\ fs[]
QED

Theorem st_simps = CONJ semState_comp_eq fpState_component_equality

Theorem do_eval_res_fp_state:
  ∀ vs st st2 env decs choices.
    do_eval_res vs st:'a semanticPrimitives$state # (v sem_env # dec list, v) result = (st2, Rval (env, decs)) ⇒
    do_eval_res vs (st with fp_state := st.fp_state with choices := choices):'a semanticPrimitives$state # (v sem_env # dec list, v) result =
      (st2 with fp_state := st2.fp_state with choices := choices, Rval (env, decs))
Proof
  rw[do_eval_res_def, st_simps, CaseEq"option", CaseEq"prod"]
QED

(** TODO: Needs to incorporate somehow the Eval primitive **)
Theorem perform_rewrites_real_id_correct:
  ∀ cfg path rws e (st1:'a semanticPrimitives$state) st2 env r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
       is_real_id_list rws st1 st2 env exps r) ∧
    (∀ (st1:'a semanticPrimitives$state) st2.
        freeVars_realExp_bound st1 st2 env cfg path e) ∧
     (cfg.canOpt <=> st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt <> Strict ∧
     st1.fp_state.real_sem ∧
     evaluate st1 env [realify (perform_rewrites cfg path rws e)] = (st2, Rval r) ⇒
    ∃ choices.
      evaluate st1 env [realify e]=
        (st2 with fp_state := st2.fp_state with choices := choices, Rval r)
Proof
  ho_match_mp_tac perform_rewrites_ind \\ rpt strip_tac \\ fs[perform_rewrites_def]
  \\ TRY (no_change_tac \\ NO_TAC)
  >- (
    reverse (Cases_on ‘cfg.canOpt’) \\ fs[]
    >- no_change_tac
    \\ fs[freeVars_realExp_bound_def]
    \\ Cases_on ‘rewriteFPexp rws (App op exps) = App op exps’
    >- (pop_assum $ fs o single
        \\ no_change_tac)
    \\ ‘isFpArithExp (App op exps)’
      by (imp_res_tac icing_rewriterProofsTheory.isFpArithExp_rewrite_preserved)
    \\ res_tac \\ fs[is_real_id_list_def]
    \\ first_x_assum (qspecl_then [‘st1’, ‘st2’, ‘env’, ‘[App op exps]’, ‘r’] mp_tac)
    \\ impl_tac >- fs[freeVars_list_real_bound_def, freeVars_real_bound_def]
    \\ strip_tac \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ COND_CASES_TAC \\ fs[CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ strip_tac \\ rveq
    \\ fs[freeVars_realExp_bound_def]
    \\ qpat_x_assum `evaluate _ _ (REVERSE _) = _` $ mp_then Any mp_tac perform_rewrites_lift_reverse_real
    \\ impl_tac >- gs[]
    \\ strip_tac \\ simp[Once evaluate_def]
    \\ ‘(λ a. realify a) = realify’ by gs[FUN_EQ_THM]
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[realify_def] \\ Cases_on ‘op’
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", CaseEq"op_class", astTheory.getOpClass_def, CaseEq"list"]
    \\ strip_tac \\ rveq
    \\ fs[freeVars_realExp_bound_def]
    \\ TRY (‘st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv  \\ gs[]))
    \\ gs[CaseEq"option", CaseEq"prod"]
    \\ TRY(
      qpat_x_assum `evaluate _ _ (REVERSE _) = _` $ mp_then Any mp_tac perform_rewrites_lift_reverse_real
      \\ impl_tac \\ gs[]
      \\ strip_tac \\ simp[Once evaluate_def, astTheory.getOpClass_def]
      \\ ‘(λ a. realify a) = realify’ by gs[FUN_EQ_THM]
      \\ gs[semState_comp_eq, fpState_component_equality]
      \\ gs[])
    >- (
      pop_assum mp_tac
      \\ Cases_on ‘exps’ \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality]
      \\ Cases_on ‘t’ \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality]
      \\ Cases_on ‘t'’ \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality]
      \\ reverse (Cases_on ‘t’) >- gs[evaluate_def, semState_comp_eq, fpState_component_equality]
      \\ gs[]
      \\ simp[SimpL“$==>”, evaluate_def, evaluate_case_case, CaseEq"result", CaseEq"prod",
             astTheory.getOpClass_def]
      \\ rpt strip_tac \\ rveq \\ gs[]
      \\ ‘st'3'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
      \\ gs[CaseEq"option", CaseEq"prod"] \\ rveq \\ gs[]
      \\ Cases_on ‘i=0’ \\ gs[]
      >- (
        get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
        \\ impl_tac >- gs[EVERYi_def]
        \\ rpt strip_tac \\ simp[evaluate_def, astTheory.getOpClass_def]
        \\ ext_choices_tac ‘evaluate _ _ [realify h''] = _’ ‘choices’
        \\ gs[semState_comp_eq, fpState_component_equality]
        \\ ext_choices_tac ‘evaluate _ _ [realify h'] = _’
                           ‘choices + st''.fp_state.choices - st'.fp_state.choices’
        \\ imp_res_tac evaluate_sing \\ rveq \\ gs[] \\ rveq
        \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"]
        \\ rveq \\ gs[]
        \\ Cases_on ‘v'3'’
        \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"])
      \\ Cases_on ‘i = 1’ \\ gs[]
      >- (
        get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
        \\ impl_tac >- (gs[EVERYi_def] \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
        \\ rpt strip_tac \\ fs[evaluate_def, astTheory.getOpClass_def, do_app_def]
        \\ imp_res_tac evaluate_sing \\ rveq \\ gs[] \\ rveq
        \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"]
        \\ rveq \\ gs[]
        \\ Cases_on ‘v'3'’
        \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"])
      \\ Cases_on ‘i = 2’ \\ gs[]
      >- (
        get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
        \\ impl_tac >- (gs[EVERYi_def] \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
        \\ rpt strip_tac \\ fs[evaluate_def, astTheory.getOpClass_def, do_app_def]
        \\ imp_res_tac evaluate_sing \\ rveq \\ gs[] \\ rveq
        \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"]
        \\ rveq \\ gs[]
        \\ ext_choices_tac ‘evaluate _ _ [realify h'] = _’ ‘choices’
        \\ gs[]
        \\ Cases_on ‘v'3'’
        \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"])
      \\ fs[evaluate_def, astTheory.getOpClass_def, do_app_def]
      \\ imp_res_tac evaluate_sing \\ rveq \\ gs[] \\ rveq
      \\ gs[semState_comp_eq, fpState_component_equality, do_app_def, CaseEq"v"])
    >- (
      Cases_on ‘st'.clock = 0’ \\ gs[dec_clock_def]
      \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘choices’
      \\ gs[semState_comp_eq, fpState_component_equality])
    \\ imp_res_tac do_eval_res_fp_state
    \\ first_x_assum $ qspec_then ‘choices’ $ assume_tac
    \\ gs[]
    \\ COND_CASES_TAC \\ gs[dec_clock_def, CaseEq"prod", CaseEq"result", CaseEq"option", CaseEq"error_result"]
    \\ ext_choicesd_tac ‘evaluate_decs _ _ _ = _’ ‘choices’
    \\ gs[st_simps] \\ rveq \\ gs[]
    \\ pop_assum mp_tac \\ qmatch_goalsub_abbrev_tac ‘evaluate_decs _ _ _ = (st2N, _)’
    \\ rpt strip_tac
    \\ qexists_tac ‘st2N.fp_state.choices’ \\ qexists_tac ‘st2N’ \\ unabbrev_all_tac
    \\ gs[st_simps])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac \\ Cases_on ‘v1'’ \\ gs[evaluate_def]
    >- (
      ext_choices_tac ‘evaluate _ _ [e'] = _’ ‘choices’
      \\ gs[semState_comp_eq, fpState_component_equality])
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ Cases_on ‘v1'’ \\ gs[evaluate_def] \\ rveq \\ gs[]
    >- (
      ‘e' = realify (perform_rewrites cfg path rws e)’
       by (
         qpat_x_assum `do_log _ _ _ = _` mp_tac
         \\ gs[do_log_def] \\ COND_CASES_TAC \\ gs[])
      \\ pop_assum (gs o single)
      \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
      \\ impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ gs[])
      \\ strip_tac \\ gs[do_log_def] \\ COND_CASES_TAC
      \\ gs[semState_comp_eq, fpState_component_equality])
    \\ gs[do_log_def] \\ COND_CASES_TAC
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ ext_choices_tac ‘evaluate _ _ [e'] = _’ ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ gs[do_if_def] \\ Cases_on ‘HD v = Boolv T’ \\ gs[]
    >- (
      rveq
      \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
      \\ impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ gs[])
      \\ strip_tac
      \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def, do_if_def])
    \\ rveq
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def, do_if_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ gs[do_if_def] \\ reverse (Cases_on ‘HD v = Boolv T’) \\ gs[]
    >- (
      rveq
      \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
      \\ impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ gs[])
      \\ strip_tac
      \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def, do_if_def])
    \\ rveq
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def, do_if_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ pop_assum mp_tac \\ COND_CASES_TAC \\ gs[]
    \\ strip_tac
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ ext_choicesm_tac ‘evaluate_match _ _ _ _ _ = _’ ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ pop_assum mp_tac \\ COND_CASES_TAC \\ gs[] \\ strip_tac
    \\ pop_assum $ mp_then Any mp_tac perform_rewrites_lift_match
    \\ impl_tac
    >- (
      gs[] \\ rpt conj_tac
      >- (
        rpt strip_tac \\ first_x_assum (qspecl_then [‘p’, ‘e'’] mp_tac)
        \\ gs[])
      \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ strip_tac \\ simp[evaluate_def]
    \\ ‘can_pmatch_all env.c st'.refs (MAP FST (MAP (λ (p,e). (p, realify e)) pes)) (HD v)’
      by (‘$o FST o
           $o (λ (p:pat, e). (p, realify e)) o
           (λ n (p:pat,e). if n = i then (p, perform_rewrites cfg path rws e) else (p, e)) =
           $o FST o (λ n (p, e). (p,realify e))’
            by (gs[FUN_EQ_THM] \\ rpt strip_tac \\ Cases_on ‘x = i’ \\ gs[]
                \\ Cases_on ‘x'’ \\ gs[])
          \\ pop_assum (gs o single)
          \\ ‘MAP FST (MAP (λ (p,e). (p, realify e)) pes) =
              MAPi ($o FST o (λ n (p,e). (p,realify e))) pes’
             by (rpt $ pop_assum kall_tac \\ Induct_on ‘pes’
                 \\ gs[] \\ rpt strip_tac
                 \\ AP_THM_TAC \\ AP_TERM_TAC \\ gs[FUN_EQ_THM])
          \\ gs[])
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ ext_choices_tac ‘evaluate _ _ [realify e2] = _’ ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac
    >- (
      gs[] \\ rpt conj_tac
      >- (res_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ strip_tac
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ COND_CASES_TAC \\ gs[]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify(perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
    \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality])
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", realify_def]
  \\ gs[freeVars_realExp_bound_def] \\ strip_tac \\ rveq
  \\ get_IH ‘evaluate _ _ [realify (perform_rewrites _ _ _ _)] = _’
  \\ impl_tac >- gs[]
  \\ strip_tac
  \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality]
QED

Theorem is_real_id_list_perform_rewrites_lift:
  (∀ rws.
     (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
        is_real_id_list rws st1 st2 env exps r) ⇒
     (∀ path (st1:'a semanticPrimitives$state) st2 env cfg e r.
        is_real_id_perform_rewrites rws st1 st2 env cfg e r path))
Proof
  rpt strip_tac
  \\ gs[is_real_id_perform_rewrites_def]
  \\ rpt strip_tac \\ imp_res_tac perform_rewrites_real_id_correct
  \\ fsrw_tac[SATISFY_ss][semState_comp_eq, fpState_component_equality]
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
            semanticPrimitivesTheory.fpState_component_equality,
            freeVars_realPlan_bound_def])
  >~ [‘Expected e’]
  >- (fs[optimise_with_plan_def]
      \\ TOP_CASE_TAC \\ fs[]
      \\ rpt strip_tac \\ res_tac
      \\ fs[semanticPrimitivesTheory.state_component_equality,
            semanticPrimitivesTheory.fpState_component_equality,
            freeVars_realPlan_bound_def])
  >~ [‘Apply p’]
  \\ Cases_on ‘p’ \\ fs[optimise_with_plan_def]
  \\ COND_CASES_TAC \\ fs[]
  \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality]
  \\ COND_CASES_TAC \\ fs[freeVars_realPlan_bound_def]
  >- (
    rpt strip_tac \\ fs[is_real_id_perform_rewrites_def] \\ res_tac
    \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality])
  \\ Cases_on ‘(optimise_with_plan cfg plan
                      (perform_rewrites cfg q r' e))’
  \\ fs[] \\ COND_CASES_TAC
  \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality]
  \\ rpt strip_tac
  \\ first_x_assum $
       qspecl_then [‘st1’, ‘st2’, ‘env’, ‘cfg’,
                    ‘perform_rewrites cfg q r' e’, ‘r’]
       mp_tac
  \\ fs[] \\ strip_tac
  \\ first_x_assum $ qspecl_then [‘r'’, ‘q’] mp_tac
  \\ impl_tac \\ fs[]
  \\ strip_tac \\ fs[is_real_id_perform_rewrites_def]
  \\ res_tac
  \\ fs[semanticPrimitivesTheory.state_component_equality,
        semanticPrimitivesTheory.fpState_component_equality]
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
  rw[isPureExp_def, source_to_source2Theory.no_optimisations_def]>>fs[] >>
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

(* Lemmas needed to automate proof generation *)
Theorem is_perform_rewrites_id_empty_plan:
  ! rws path.
    MEM (Apply (path, rws)) [] ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_perform_rewrites_correct_cons_real_id:
  ! rwsNew pathNew plan.
  (! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rwsNew st1 st2 env cfg e r pathNew) ==>
  (! rws path.
     MEM (Apply (path, rws)) plan ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path) ==>
  (! rws path.
     MEM (Apply (path, rws)) (Apply (pathNew, rwsNew)::plan) ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_perform_rewrites_correct_label_real_id:
  ! s plan.
  (! rws path.
     MEM (Apply (path, rws)) plan ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path) ==>
  (! rws path.
     MEM (Apply (path, rws)) (Label s::plan) ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_perform_rewrites_correct_expected_real_id:
  ! e plan.
  (! rws path.
     MEM (Apply (path, rws)) plan ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path) ==>
  (! rws path.
     MEM (Apply (path, rws)) (Expected e::plan) ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_real_id_perform_rewrites rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_optimise_with_plan_correct_sing_real_id:
  ! sing_plan.
    (! (st1:'a semanticPrimitives$state) st2 env cfg exps r.
    is_real_id_optimise_with_plan sing_plan st1 st2 env cfg exps r) ==>
    (! plan.
       MEM plan [sing_plan] ==>
       ! exps (st1:'a semanticPrimitives$state) st2 env cfg r.
       is_real_id_optimise_with_plan plan st1 st2 env cfg exps r)
Proof
  rpt strip_tac \\ fs[]
QED

val _ = export_theory();
