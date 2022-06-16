(*
  Overall correctness proofs for optimisation functions
  defined in source_to_source2Script.sml.
  To prove a particular run correct, they are combined
  using the automation in icing_optimisationsLib.sml with
  the local correctness theorems from icing_optimisationProofsScript.sml.
*)
open icing_rewriterTheory icing_rewriterProofsTheory source_to_source2Theory
     fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory pureExpsTheory floatToRealTheory
     floatToRealProofsTheory evaluatePropsTheory namespaceTheory
     fpSemPropsTheory mllistTheory optPlannerTheory;
     local open ml_progTheory in end;
open icingTacticsLib preamble;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"];

val _ = new_theory "source_to_source2Proofs";

(**
  Helper theorems and definitions
**)
val choice_mono =
  (CONJUNCT1 evaluate_fp_opts_inv) |> SPEC_ALL |> UNDISCH |> CONJUNCTS |> el 3 |> DISCH_ALL;

(* TODO: Move *)
Theorem nsMap_nsBind:
  nsMap f (nsBind x v env) = nsBind x (f v) (nsMap f env)
Proof
  Cases_on ‘env’ \\ gs[namespaceTheory.nsBind_def, nsMap_def]
QED

(* TODO: Move *)
Theorem list_result_rw:
  ∀ schedule st1 fp.
    list_result (
      case do_fprw (Rval (FP_WordTree fp)) schedule st1.fp_state.rws
      of
        NONE => Rval (FP_WordTree fp)
      | SOME r_opt => r_opt) =
    Rval [FP_WordTree
          (case rwAllWordTree schedule st1.fp_state.rws fp of
             NONE => fp
           | SOME r_opt => r_opt)]
Proof
  rpt strip_tac \\ gs[semanticPrimitivesTheory.do_fprw_def, CaseEq"option"]
  \\ Cases_on ‘rwAllWordTree schedule st1.fp_state.rws fp’ \\ gs[]
QED

(* TODO: Move *)
Theorem result_cond_rw:
  ∀ schedule st fp.
      (if st.fp_state.canOpt = FPScope Opt then
         case do_fprw (Rval (FP_WordTree fp)) schedule st.fp_state.rws
      of
        NONE => Rval (FP_WordTree fp)
      | SOME r_opt => r_opt else Rval (FP_WordTree fp)) =
      Rval (FP_WordTree
            (if st.fp_state.canOpt = FPScope Opt then
               (case rwAllWordTree schedule st.fp_state.rws fp of
                  NONE => fp
                | SOME r_opt => r_opt)
             else fp))
Proof
  rpt strip_tac \\ gs[semanticPrimitivesTheory.do_fprw_def, CaseEq"option"]
  \\ COND_CASES_TAC \\ gs[]
  \\ Cases_on ‘rwAllWordTree schedule st.fp_state.rws fp’ \\ gs[]
QED

(* TODO: Move *)
Theorem list_result_cond_rw:
  ∀ schedule st1 fp.
    list_result (
      if st1.fp_state.canOpt = FPScope Opt then
      (case do_fprw (Rval (FP_WordTree fp)) schedule st1.fp_state.rws
      of
        NONE => Rval (FP_WordTree fp)
      | SOME r_opt => r_opt)
      else Rval (FP_WordTree fp)) =
    Rval [FP_WordTree
          (if st1.fp_state.canOpt = FPScope Opt then
            (case rwAllWordTree schedule st1.fp_state.rws fp of
               NONE => fp
             | SOME r_opt => r_opt)
          else fp)]
Proof
  rpt strip_tac \\ gs[semanticPrimitivesTheory.do_fprw_def]
  \\ COND_CASES_TAC \\ gs[CaseEq"option"]
  \\ Cases_on ‘rwAllWordTree schedule st1.fp_state.rws fp’ \\ gs[]
QED

Theorem fp_state_opts_eq[local]:
  fps with <| rws := rwsN; opts := fps.opts |> = fps with <| rws := rwsN |>
Proof
  Cases_on `fps` \\ fs[fpState_component_equality]
QED

Theorem do_app_fp_inv:
  do_app (refs, ffi) (FP_bop op) [v1; v2] = SOME ((refs2, ffi2), r) ==>
    ? w1 w2.
      fp_translate v1 = SOME (FP_WordTree w1) /\ fp_translate v2 = SOME (FP_WordTree w2) /\
      r = Rval (FP_WordTree (fp_bop op w1 w2))
Proof
  Cases_on `op` \\ every_case_tac \\ fs[do_app_def] \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq \\ fs[]
QED

Theorem nth_len:
  nth (l ++ [x]) (LENGTH l + 1) = SOME x
Proof
  Induct_on `l` \\ fs[fpOptTheory.nth_def, ADD1]
QED

Definition freeVars_fp_bound_def:
  freeVars_fp_bound e env =
    ∀ x. x IN FV e ⇒
         ∃ fp. nsLookup env.v x = SOME (FP_WordTree fp)
End

(* Correctness definition for rewriteFPexp
 We need to handle the case where the expression returns an error, but we cannot
 preserve the exact error, as reordering may change which error is returned *)
Definition is_rewriteFPexp_correct_def:
  is_rewriteFPexp_correct rws (st1:'a semanticPrimitives$state) st2 env e r =
    (evaluate st1 env [rewriteFPexp rws e] = (st2, Rval r) /\
     freeVars_fp_bound e env ∧
     st1.fp_state.canOpt = FPScope Opt /\
     st1.fp_state.real_sem = F ==>
     ? fpOpt choices fpOptR choicesR.
      evaluate
        (st1 with fp_state := st1.fp_state with
           <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env [e] =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r))
End

Definition freeVars_list_fp_bound_def:
  freeVars_list_fp_bound exps env =
    ∀ x. x IN FV_list exps ⇒
         ∃ fp. nsLookup env.v x = SOME (FP_WordTree fp)
End

Definition is_rewriteFPexp_list_correct_def:
  is_rewriteFPexp_list_correct rws (st1:'a semanticPrimitives$state) st2 env exps r =
    (evaluate st1 env (MAP (rewriteFPexp rws) exps) = (st2, Rval r) /\
     freeVars_list_fp_bound exps env ∧
     st1.fp_state.canOpt = FPScope Opt /\
     st1.fp_state.real_sem = F ==>
     ? fpOpt choices fpOptR choicesR.
       evaluate
         (st1 with fp_state := st1.fp_state with
            <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env exps =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r))
End

Theorem empty_rw_correct:
   ! (st1 st2:'a semanticPrimitives$state) env e r.
     is_rewriteFPexp_correct [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_rewriteFPexp_correct_def, rewriteFPexp_def]
  \\ rpt strip_tac \\ qexists_tac `st1.fp_state.opts`
  \\ qexists_tac ‘st1.fp_state.choices’
  \\ `st1 = st1 with fp_state := st1.fp_state with
          <| rws := st1.fp_state.rws; opts := st1.fp_state.opts; choices := st1.fp_state.choices |>`
      by (fs[semState_comp_eq, fpState_component_equality])
  \\ pop_assum (fn thm => fs[GSYM thm])
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

Theorem choices_simp:
  st.fp_state with choices := st.fp_state.choices = st.fp_state
Proof
  fs[fpState_component_equality]
QED

Theorem rewriteExp_compositional:
  ! rws opt.
   (! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct rws st1 st2 env e r) /\
   (! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct [opt] st1 st2 env e r) ==>
  ! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct ([opt] ++ rws) st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ PairCases_on `opt` \\ simp[rewriteFPexp_def]
  \\ reverse TOP_CASE_TAC
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)] ++ rws`, `g`] strip_assume_tac)
    \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ fs[semState_comp_eq, fpState_component_equality, choices_simp])
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
    \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
    \\ fs[fpState_component_equality]
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘choices’
    \\ fs[semState_comp_eq, fpState_component_equality])
  \\ TOP_CASE_TAC \\ fs[]
  >- (
   rpt strip_tac
   \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
   \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
   \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
   \\ fs[fpState_component_equality] \\ asm_exists_tac \\ fs[]
   \\ TOP_CASE_TAC \\ fs[]
   \\ qexists_tac ‘fpOptR’ \\ fs[semState_comp_eq, fpState_component_equality])
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum drule \\ fs[state_component_equality, fpState_component_equality]
  \\ fs[PULL_EXISTS] \\ rpt gen_tac
  \\ impl_tac
  >- (fs[freeVars_fp_bound_def]
      \\ qspecl_then [‘opt1’, ‘opt0’, ‘e’, ‘x'’, ‘x’, ‘[]’,
                      ‘λ x. ∃ fp. nsLookup env.v x = SOME (FP_WordTree fp)’]
                     mp_tac match_preserves_FV
      \\ impl_tac \\ fs[substLookup_def])
  \\ strip_tac \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate st1N env [_] = (st2N, Rval r2)`
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [`st1N`, `st2N`, `env`, `e`, `r2`] assume_tac)
  \\ fs[rewriteFPexp_def] \\ rfs[]
  \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
  \\ first_x_assum impl_subgoal_tac \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_up)))
  \\ first_x_assum (qspec_then `st1.fp_state.rws  ++ [(opt0, opt1)] ++ rws` impl_subgoal_tac)
  >- (fs[SUBSET_DEF] \\ rpt strip_tac \\ fs[])
  \\ fs[] \\ qexists_tac `fpOpt''` \\ qexists_tac ‘choices'’ \\ fs[]
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
QED

Theorem lift_rewriteFPexp_correct_list_strong:
  ! rws (st1 st2:'a semanticPrimitives$state) env exps r.
    (! (st1 st2: 'a semanticPrimitives$state) env e r.
      is_rewriteFPexp_correct rws st1 st2 env e r) ==>
  is_rewriteFPexp_list_correct rws st1 st2 env exps r
Proof
  Induct_on `exps`
  \\ fs[is_rewriteFPexp_correct_def, is_rewriteFPexp_list_correct_def]
  >- (rpt strip_tac \\ qexists_tac ‘st1.fp_state.opts’
      \\ fs[semState_comp_eq, fpState_component_equality])
  \\ rpt strip_tac \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ simp[Once evaluate_cons]
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ first_assum (qspecl_then [`st1`, `q`, `env`, `h`, `a`] impl_subgoal_tac)
  \\ simp[Once evaluate_cons] \\ fs[] \\ rveq
  >- (fs[freeVars_fp_bound_def, freeVars_list_fp_bound_def])
  \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then assume_tac \\ fs[]
  \\ first_x_assum impl_subgoal_tac
  >- (conj_tac
      >- (fs[freeVars_fp_bound_def, freeVars_list_fp_bound_def])
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ first_x_assum (qspec_then `fpOpt'` assume_tac) \\ fs[]
  \\ qexists_tac `optUntil (choicesR - choices) fpOpt fpOpt'`
  \\ qexists_tac ‘choices’ \\ fs[]
  \\ qpat_x_assum `evaluate _ _ exps = _`
                  (mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices))
  \\ first_x_assum (qspec_then ‘choicesR’ assume_tac)
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

Theorem lift_rewriteFPexp_correct_list:
  ! rws.
    (! (st1 st2: 'a semanticPrimitives$state) env e r.
      is_rewriteFPexp_correct rws st1 st2 env e r) ==>
    ! (st1 st2:'a semanticPrimitives$state) env exps r.
    is_rewriteFPexp_list_correct rws st1 st2 env exps r
Proof
  rpt strip_tac \\ drule lift_rewriteFPexp_correct_list_strong
  \\ disch_then irule
QED

Theorem fpState_upd_id:
  ! s.
    s with fp_state :=
      s.fp_state with <| rws := s.fp_state.rws; opts := s.fp_state.opts |> = s
Proof
  rpt strip_tac
  \\ ‘s.fp_state with <| rws := s.fp_state.rws; opts := s.fp_state.opts |> = s.fp_state’
     by (fs[fpState_component_equality])
  \\ pop_assum (rewrite_tac o single)
  \\ fs[semanticPrimitivesTheory.state_component_equality]
QED

Triviality MAP_MAP_triple:
  ! l f. MAP (λ (x,y,z). x) (MAP (λ (s1,s2,e). (s1,s2,f e)) l) = MAP (λ (x,y,z). x) l
Proof
  Induct_on ‘l’ \\ fs[] \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ fs[] \\ Cases_on ‘r’ \\ fs[]
QED

Theorem MEM_for_all_MAPi:
  ! (P: 'a -> 'a -> bool) (f: 'a -> 'a) (g: 'a -> 'a) l l'.
    (!x. MEM x l ==> P (f x) x) /\ (!x. P (g x) x) ==>
    MAPi (λn e. if n = i then (f e) else (g e)) l = l' ==>
    (!i. (i: num) < LENGTH l ==> P (EL i l') (EL i l))
Proof
  rpt strip_tac
  \\ imp_res_tac (INST_TYPE[alpha |-> beta] EL_MAPi)
  \\ pop_assum ( Q.ISPEC_THEN ‘(λ (n :num) (e :'a). if n = (i :num) then ((f :'a -> 'a) e) else (g :'a -> 'a) e): num -> 'a -> 'a’ strip_assume_tac )
  \\ fs[EVAL “(λn e. if n = i then f e else g e) i' (EL i' l)”]
  \\ Cases_on ‘i = i'’ \\ rveq  \\ fs[]
  \\ qpat_x_assum ‘! x. MEM x l ==> P (f x) x’ (qspec_then ‘(EL i l)’ assume_tac)
  \\ Q.ISPECL_THEN [‘l’, ‘(EL i l)’] strip_assume_tac MEM_EL
  \\ last_assum ( (assume_tac o snd) o EQ_IMP_RULE ) \\ fs[]
  \\ ‘EL i l = EL i l’ by fs[]
  \\ first_x_assum irule
  \\ qexists_tac ‘i’
  \\ fs[]
QED

Theorem MAPi_EL_nested:
  ! l n. n < LENGTH l ==> EL n (MAPi (λ n e. (n, e)) l) = EL n (MAPi (λ n e. (n, (EL n l))) l)
Proof
  rpt strip_tac
  \\ qspecl_then [‘(λ n e. (n, e))’, ‘n’, ‘l’] imp_res_tac EL_MAPi
  \\ qspecl_then [‘(λ n e. (n, (EL n l)))’, ‘n’, ‘l’] imp_res_tac EL_MAPi
  \\ fs[EVAL “(λn e. (n,e)) n (EL n l)”, EVAL “(λn e. (n,EL n l)) n (EL n l)”]
QED

Theorem MAPi_EL_no_fun:
  ! l. MAPi (λ n e. (n, e)) l = MAPi (λ n e. (n, (EL n l))) l
Proof
  rpt strip_tac
  \\ qspecl_then [‘MAPi (λ n e. (n, e)) l’, ‘MAPi (λ n e. (n, (EL n l))) l’] strip_assume_tac LIST_EQ
  \\ ‘LENGTH (MAPi (λ n e. (n, e)) l) = LENGTH (MAPi (λ n e. (n, (EL n l))) l)’ by fs[LENGTH_MAPi]
  \\ fs[]
QED

Theorem MAPi_EL_list_quant:
  ! f l. MAPi (λ n e. f n e) l = MAPi (λ n e. f n (EL n l)) l
Proof
  rpt strip_tac
  \\ qspecl_then [‘MAPi (λ n e. f n e) l’, ‘MAPi (λ n e. f n (EL n l)) l’] strip_assume_tac LIST_EQ
  \\ pop_assum irule
  \\ rpt strip_tac \\ fs[LENGTH_MAPi]
QED

Theorem MAPi_EL_list:
  MAPi (λ n e. f n e) l = MAPi (λ n e. f n (EL n l)) l
Proof
  fs[MAPi_EL_list_quant]
QED

Theorem MAPi_same_EL_quant:
  ! exps. MAPi (λ n e. (EL n exps)) exps = exps
Proof
  strip_tac
  \\ qspecl_then [‘λ n e. e’, ‘exps’] assume_tac MAPi_EL_list_quant
  \\ fs[]
QED

Theorem MAPi_same_EL:
  MAPi (λ n e. (EL n exps)) exps = exps
Proof
  fs[MAPi_same_EL_quant]
QED

local
val rewrites_no_effect =
  “λ cfg path plan e. perform_rewrites cfg path plan e = e”
in
Theorem perform_rewrites_no_plan_same:
  ! cfg path plan e. plan = [] ==> ^rewrites_no_effect cfg path plan e
Proof
  ho_match_mp_tac perform_rewrites_ind
  \\ fs[perform_rewrites_def]
  \\ strip_tac
  >- (
  rpt strip_tac
  \\ Cases_on ‘cfg.canOpt’
  \\ fs[rewriteFPexp_def]
  )
  >- (
  rpt strip_tac
  \\ Cases_on ‘cfg.canOpt’
  \\ fs[rewriteFPexp_def]
  \\ irule LIST_EQ
  \\ fs[LENGTH_MAPi]
  \\ rpt strip_tac
  \\ Cases_on ‘x = i’
  \\ fs[]
  \\ TRY (
    qpat_x_assum ‘!e. MEM e exps ==> _’ (qspec_then ‘EL i exps’ assume_tac)
    \\ fs[MEM_EL]
    \\ pop_assum irule
    \\ qexists_tac ‘i’ \\ fs[]
    )
  \\ TRY (
    Cases_on ‘EL i pes’ \\ fs[]
    \\ qpat_x_assum ‘! p e. MEM (p, e) pes ==> _’ (qspecl_then [‘q’, ‘r’] assume_tac)
    \\ fs[MEM_EL]
    \\ pop_assum irule
    \\ qexists_tac ‘i’ \\ fs[]
    )
  \\ TRY (
    Cases_on ‘EL x pes’ \\ fs[]
    )
  )
QED
end

Theorem perform_rewrites_no_plan_simple:
  perform_rewrites cfg path [] e = e
Proof
  qspecl_then [‘cfg’, ‘path’, ‘[]’, ‘e’] strip_assume_tac perform_rewrites_no_plan_same
  \\ fs[]
QED

Theorem enumerate_append:
  ! l l' n. enumerate n (l ++ l') = (enumerate n l) ++ (enumerate (n + LENGTH l) l')
Proof
  Induct_on ‘l'’ \\ fs[miscTheory.enumerate_def]
  \\ Induct_on ‘l’ \\ fs[miscTheory.enumerate_def]
QED

Definition freeVars_arithExp_bound_def:
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
    Here (Lit l) =
      T ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
                          Here  (App op exps) =
    (if isFpArithExp (App op exps) then freeVars_fp_bound (App op exps) env
    else T) ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
                          Here  (Var x) = T ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env (cfg: config)
                          Here  e = T ∧
  (* If we are not at the end of the path, further navigate through the AST *)
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg (Left _)
                           (Lit l) = T ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg (Left _)
                           (Var x) = T ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg (Center path)
                           (Raise e) =
    freeVars_arithExp_bound st1 st2 env cfg path  e ∧
  (* We cannot support "Handle" expressions because we must be able to reorder exceptions *)
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg path
                           (Handle e pes) = T ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (ListIndex (i, path)) (Con mod exps) =
  (EVERYi (λ n e. if (n = i)
                  then (freeVars_arithExp_bound st1 st2 env cfg path  e)
                  else T) exps) ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left _)  (Fun s e) = T ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (ListIndex (i, path)) (App op exps) =
  (EVERYi (λ n e. if (n = i)
                  then (freeVars_arithExp_bound st1 st2 env cfg path  e)
                  else T) exps) ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (Log lop e2 e3) =
    freeVars_arithExp_bound st1 st2 env cfg path  e2 ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Right path) (Log lop e2 e3) =
    freeVars_arithExp_bound st1 st2 env cfg path  e3 ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (If e1 e2 e3) =
    freeVars_arithExp_bound st1 st2 env cfg path  e1 ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (If e1 e2 e3) =
    freeVars_arithExp_bound st1 st2 env cfg path  e2 ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Right path) (If e1 e2 e3) =
    freeVars_arithExp_bound st1 st2 env cfg path  e3 ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (Mat e pes) =
    freeVars_arithExp_bound st1 st2 env cfg path  e ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (ListIndex (i, path)) (Mat e pes) =
  EVERYi (λ n (p, e').
           if (n = i) then
             ∀ v env_v.
               pmatch env.c st1.refs p (HD v) [] = Match env_v ⇒
               ∀ st1 st2. freeVars_arithExp_bound st1 st2
                 (env with v := nsAppend (alist_to_ns env_v) env.v) cfg path e'
           else T) pes ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Left path) (Let so e1 e2) =
    (freeVars_arithExp_bound st1 st2 env cfg path  e1) ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Right path)  (Let so e1 e2) =
  (∀ r.
     evaluate st1 env [e1] = (st2, Rval r) ⇒
     (∀ st1 st2.
        freeVars_arithExp_bound st1 st2 (env with v := nsOptBind so (HD r) env.v)
                                       cfg path e2)) ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (Letrec ses e) =
  (ALL_DISTINCT (MAP (λ(x,y,z). x) ses) ⇒
  freeVars_arithExp_bound st1 st2 (env with v := build_rec_env ses env env.v) cfg path e) ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (Tannot e t) =
    freeVars_arithExp_bound st1 st2 env cfg path  e ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (Lannot e l) =
    freeVars_arithExp_bound st1 st2 env cfg path  e ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg
                          (Center path) (FpOptimise sc e) =
    freeVars_arithExp_bound st1 st2 env (cfg with canOpt := if sc = Opt then T else F) path e ∧
  freeVars_arithExp_bound (st1:'a semanticPrimitives$state) st2 env cfg _ e = T
End

Theorem rewriteFPexp_freeVars_fp_bound:
  ∀ rws e env.
    rewriteFPexp rws e ≠ e ∧
    freeVars_fp_bound e env ⇒
    freeVars_fp_bound (rewriteFPexp rws e) env
Proof
  Induct_on ‘rws’ \\ fs[rewriteFPexp_def]
  \\ rpt strip_tac \\ fs[freeVars_fp_bound_def]
  \\ imp_res_tac isFpArithExp_rewrite_preserved
  \\ Cases_on ‘h’ \\ fs[rewriteFPexp_def]
  \\ COND_CASES_TAC \\ fs[]
  \\ TOP_CASE_TAC \\ fs[]
  >- res_tac
  \\ TOP_CASE_TAC \\ fs[]
  >- res_tac
  \\ qspecl_then [‘r’, ‘q’, ‘e’, ‘x'’, ‘x’, ‘[]’,
                  ‘λ x. ∃ fp. nsLookup env.v x = SOME (FP_WordTree fp)’] mp_tac match_preserves_FV
  \\ impl_tac \\ fs[substLookup_def]
  \\ rpt strip_tac
  \\ Cases_on ‘rewriteFPexp rws x' = x'’ \\ fs[]
  \\ first_x_assum drule
  \\ rpt (disch_then drule) \\ gs[]
QED

Definition isDoubleExp_def:
  isDoubleExp (Var x) = T ∧
  isDoubleExp (Lit l) = F ∧
  isDoubleExp (Let x e1 e2) = (isDoubleExp e1 ∧ isDoubleExp e2) ∧
  isDoubleExp (App FpFromWord [Lit (Word64 w)]) = T ∧
  isDoubleExp (App op exps) =
    (case op of
    | FP_uop _ => isDoubleExpList exps
    | FP_bop _ => isDoubleExpList exps
    | FP_top _ => isDoubleExpList exps
    | _ => F) ∧
  isDoubleExp (FpOptimise sc e) = isDoubleExp e ∧
  isDoubleExp _ = F
  ∧
  isDoubleExpList [] = T ∧
  isDoubleExpList (e1::es) = (isDoubleExp e1 ∧ isDoubleExpList es)
Termination
  wf_rel_tac ‘measure (λ x. case x of |INL e => exp_size e |INR es => exp6_size es)’
End

Theorem isDoubleExp_evaluates:
  (∀ e env (st1:'a semanticPrimitives$state) st2 r.
     isDoubleExp e ∧
     freeVars_fp_bound e env ∧
     evaluate st1 env [e] = (st2, Rval r) ⇒
     ∃ fp. r = [FP_WordTree fp])
  ∧
  (∀ exps env (st1:'a semanticPrimitives$state) st2 r.
     isDoubleExpList exps ∧
     freeVars_list_fp_bound exps env ⇒
     ∀ e. MEM e exps ⇒
     evaluate st1 env [e] = (st2, Rval r) ⇒
     ∃ fp. r = [FP_WordTree fp])
Proof
  ho_match_mp_tac isDoubleExp_ind
  \\ rpt strip_tac \\ fs[isDoubleExp_def]
  >- (gs[evaluate_def, freeVars_fp_bound_def] \\ rveq \\ gs[])
  >- (
    qpat_x_assum `evaluate _ _ _ = _` mp_tac
    \\ gs[evaluate_def, CaseEq"result", CaseEq"prod"]
    \\ rpt strip_tac \\ rveq
    \\ last_x_assum (qspecl_then [‘env’, ‘st1’, ‘st'’, ‘v’] mp_tac)
    \\ impl_tac >- gs[freeVars_fp_bound_def]
    \\ strip_tac \\ rveq
    \\ qpat_x_assum `evaluate _ (env with v := _) _ = _`
         (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ impl_tac
    >- (
      Cases_on ‘x’ \\ gs[namespaceTheory.nsOptBind_def, freeVars_fp_bound_def]
      \\ rpt strip_tac \\ rename1 ‘nsBind y _ env.v’ \\ rename1 ‘x IN FV e2’
      \\ Cases_on ‘x = Short y’ \\ gs[ml_progTheory.nsLookup_nsBind_compute])
    \\ strip_tac \\ gs[])
  >- (
    gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
       astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ rveq \\ gs[])
  >~ [‘FpOptimise sc e’]
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
          astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"]
    \\ strip_tac \\ gs[freeVars_fp_bound_def] \\ rveq
    \\ qpat_x_assum `evaluate _ _ _ = _`
         (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ impl_tac
    >- (gs[])
    \\ strip_tac \\ gs[do_fpoptimise_def])
  >~ [‘freeVars_list_fp_bound (e::exps)’, ‘evaluate st1 env [e2] = (st2, Rval r)’]
  >- (
    rveq \\ res_tac \\ pop_assum mp_tac \\ gs[freeVars_fp_bound_def, freeVars_list_fp_bound_def])
  >~ [‘freeVars_list_fp_bound (e::exps)’, ‘MEM e2 exps’]
  >- (
    ‘freeVars_list_fp_bound exps env’ by (gs[freeVars_list_fp_bound_def])
    \\ res_tac \\ gs[])
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
       astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"]
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ gs[CaseEq"prod"]
  \\ pop_assum (fn th => rpt strip_tac \\ mp_tac th)
  \\ rpt (TOP_CASE_TAC \\ gs[]) \\ rpt strip_tac \\ rveq
  \\ gs[result_cond_rw] \\ rveq \\ gs[]
QED

Theorem isDoubleExp_evaluates_real:
  (∀ e env (st1:'a semanticPrimitives$state) st2 r.
     isDoubleExp e ∧
     freeVars_real_bound e env ∧
     evaluate st1 env [realify e] = (st2, Rval r) ⇒
     ∃ rn. r = [Real rn])
  ∧
  (∀ exps env (st1:'a semanticPrimitives$state) st2 r.
     isDoubleExpList exps ∧
     freeVars_list_real_bound exps env ⇒
     ∀ e. MEM e exps ⇒
     evaluate st1 env [realify e] = (st2, Rval r) ⇒
     ∃ rn. r = [Real rn])
Proof
  ho_match_mp_tac isDoubleExp_ind
  \\ rpt strip_tac \\ fs[isDoubleExp_def, realify_def]
  >- (gs[evaluate_def, freeVars_real_bound_def] \\ rveq \\ gs[])
  >- (
    qpat_x_assum `evaluate _ _ _ = _` mp_tac
    \\ gs[evaluate_def, CaseEq"result", CaseEq"prod"]
    \\ rpt strip_tac \\ rveq
    \\ last_x_assum (qspecl_then [‘env’, ‘st1’, ‘st'’, ‘v’] mp_tac)
    \\ impl_tac >- gs[freeVars_real_bound_def]
    \\ strip_tac \\ rveq
    \\ qpat_x_assum `evaluate _ (env with v := _) _ = _`
         (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ impl_tac
    >- (
      Cases_on ‘x’ \\ gs[namespaceTheory.nsOptBind_def, freeVars_real_bound_def]
      \\ rpt strip_tac \\ rename1 ‘nsBind y _ env.v’ \\ rename1 ‘x IN FV e2’
      \\ Cases_on ‘x = Short y’ \\ gs[ml_progTheory.nsLookup_nsBind_compute])
    \\ strip_tac \\ gs[])
  >- (
    gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
       astTheory.getOpClass_def, astTheory.isFpBool_def]
    \\ Cases_on ‘st1.fp_state.real_sem’ \\ gs[]
    \\ rveq \\ gs[])
  >~ [‘FpOptimise sc e’]
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
          astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"]
    \\ strip_tac \\ gs[freeVars_real_bound_def] \\ rveq
    \\ qpat_x_assum `evaluate _ _ _ = _`
         (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ impl_tac
    >- gs[]
    \\ strip_tac \\ gs[do_fpoptimise_def])
  >~ [‘freeVars_list_real_bound (e::exps)’, ‘evaluate st1 env [realify e2] = (st2, Rval r)’]
  >- (
    rveq \\ res_tac \\ pop_assum mp_tac \\ gs[freeVars_real_bound_def, freeVars_list_real_bound_def])
  >~ [‘freeVars_list_real_bound (e::exps)’, ‘MEM e2 exps’]
  >- (
    ‘freeVars_list_real_bound exps env’ by (gs[freeVars_list_real_bound_def])
    \\ res_tac \\ gs[])
  >~ [‘freeVars_real_bound (App (FP_top t_op) exps) env’]
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
          astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"]
    \\ TOP_CASE_TAC \\ gs[CaseEq"prod"]
    >- (gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
           astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"])
    \\ TOP_CASE_TAC \\ gs[CaseEq"prod"]
    >- (gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
           astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"])
    \\ TOP_CASE_TAC \\ gs[CaseEq"prod"]
    >- (gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
           astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"])
    \\ TOP_CASE_TAC \\ gs[CaseEq"prod"]
    \\ gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
          astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"]
    \\ rpt strip_tac \\ rveq \\ gs[]
    \\ pop_assum mp_tac \\ COND_CASES_TAC \\ gs[]
    \\ TOP_CASE_TAC \\ gs[]
    \\ pop_assum (fn th => rpt strip_tac \\ mp_tac th)
    \\ rpt (TOP_CASE_TAC \\ gs[]) \\ rpt strip_tac \\ rveq
    \\ qpat_x_assum ‘(if _ then _ else _)= (_, Rval _)’ mp_tac
    \\ COND_CASES_TAC \\ gs[]
    \\ TOP_CASE_TAC \\ gs[]
    \\ pop_assum (fn th => rpt strip_tac \\ mp_tac th)
    \\ rpt (TOP_CASE_TAC \\ gs[]) \\ rpt strip_tac \\ rveq
    \\ gs[])
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ gs[evaluate_def, CaseEq"prod", CaseEq"result", do_app_def,
       astTheory.getOpClass_def, astTheory.isFpBool_def, CaseEq"list"]
  \\ rpt strip_tac \\ pop_assum mp_tac
  \\ ntac 2 (TOP_CASE_TAC \\ gs[CaseEq"prod"])
  \\ pop_assum (fn th => rpt strip_tac \\ mp_tac th)
  \\ rpt (TOP_CASE_TAC \\ gs[]) \\ rpt strip_tac \\ rveq
  \\ gs[result_cond_rw] \\ rveq \\ gs[]
QED

Theorem EVERYi_T:
  EVERYi (λ n x. T) ls
Proof
  Induct_on ‘ls’ \\ gs[EVERYi_def]
  \\ ‘(λ n x. T) o SUC = λ n x. T’ by gs[FUN_EQ_THM]
  \\ pop_assum $ gs o single
QED

Theorem EVERYi_lift_MEM:
  ∀ exps cfg (st2:'a semanticPrimitives$state) st1 path cfg.
  (∀ e.
     MEM e exps ⇒
     ∀ (st2:'a semanticPrimitives$state) st1 path cfg.
       freeVars_arithExp_bound st1 st2 env cfg path e) ⇒
  ∀ i.
    EVERYi (λ n e. n = i ⇒ freeVars_arithExp_bound st1 st2 env cfg path e) exps
Proof
  Induct_on ‘exps’ \\ gs[EVERYi_def]
  \\ rpt strip_tac \\ gs[]
  \\ Cases_on ‘i = 0’ \\ gs[]
  >- (
    ‘(λ n e. n = i ⇒ freeVars_arithExp_bound st1 st2 env cfg path e) o SUC = (λ n e. T)’
     by (rveq \\ gs[FUN_EQ_THM])
    \\ rveq
    \\ pop_assum (simp o single) \\ gs[EVERYi_T])
  \\ ‘(λ n e. n = i ⇒ freeVars_arithExp_bound st1 st2 env cfg path e) o SUC =
     (λ n e. n = i-1 ⇒ freeVars_arithExp_bound st1 st2 env cfg path e)’
     by (gs[FUN_EQ_THM] \\ rpt strip_tac \\ EQ_TAC \\ gs[]
         \\ rpt strip_tac \\ rveq \\ gs[])
  \\ pop_assum $ gs o single
QED

Theorem EVERYi_lift_MEM_real:
  ∀ exps cfg (st2:'a semanticPrimitives$state) st1 path cfg.
  (∀ e.
     MEM e exps ⇒
     ∀ (st2:'a semanticPrimitives$state) st1 path cfg.
       freeVars_realExp_bound st1 st2 env cfg path e) ⇒
  ∀ i.
    EVERYi (λ n e. n = i ⇒ freeVars_realExp_bound st1 st2 env cfg path e) exps
Proof
  Induct_on ‘exps’ \\ gs[EVERYi_def]
  \\ rpt strip_tac \\ gs[]
  \\ Cases_on ‘i = 0’ \\ gs[]
  >- (
    ‘(λ n e. n = i ⇒ freeVars_realExp_bound st1 st2 env cfg path e) o SUC = (λ n e. T)’
     by (rveq \\ gs[FUN_EQ_THM])
    \\ rveq
    \\ pop_assum (simp o single) \\ gs[EVERYi_T])
  \\ ‘(λ n e. n = i ⇒ freeVars_realExp_bound st1 st2 env cfg path e) o SUC =
     (λ n e. n = i-1 ⇒ freeVars_realExp_bound st1 st2 env cfg path e)’
     by (gs[FUN_EQ_THM] \\ rpt strip_tac \\ EQ_TAC \\ gs[]
         \\ rpt strip_tac \\ rveq \\ gs[])
  \\ pop_assum $ gs o single
QED

Theorem isDoubleExp_freeVars_arithExp_bound:
  (∀ e env.
     isDoubleExp e ∧
     freeVars_fp_bound e env ⇒
     ∀ (st1:'a semanticPrimitives$state) st2 cfg path.
       freeVars_arithExp_bound st1 st2 env cfg path e)
  ∧
  (∀ exps env.
     isDoubleExpList exps ∧
     freeVars_list_fp_bound exps env ⇒
     ∀ e. MEM e exps ⇒
          ∀ (st1:'a semanticPrimitives$state) st2 cfg path.
            freeVars_arithExp_bound st1 st2 env cfg path e)
Proof
  ho_match_mp_tac isDoubleExp_ind
  \\ rpt strip_tac \\ gs[isDoubleExp_def]
  >- (Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def])
  >~ [‘Let x e1 e2’]
  >- (
    Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def]
    >- (first_x_assum irule \\ gs[freeVars_fp_bound_def])
    \\ rpt strip_tac \\ first_x_assum irule
    \\ gs[freeVars_fp_bound_def]
    \\ last_x_assum $ qspec_then ‘env’ mp_tac
    \\ impl_tac >- gs[]
    \\ rpt strip_tac
    \\ Cases_on ‘x’ \\ gs[namespaceTheory.nsOptBind_def]
    \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
    \\ rename1 ‘y IN FV e2’
    \\ Cases_on ‘y’ \\ gs[ml_progTheory.nsLookup_nsBind_compute]
    \\ COND_CASES_TAC \\ gs[] \\ rveq
    \\ last_x_assum $ mp_then Any drule (CONJUNCT1 isDoubleExp_evaluates)
    \\ gs[] \\ disch_then irule
    \\ gs[freeVars_fp_bound_def])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_arithExp_bound_def, EVERYi_def]
    \\ rpt strip_tac \\ Cases_on ‘r’ \\ gs[freeVars_arithExp_bound_def])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_arithExp_bound_def]
    \\ ‘freeVars_list_fp_bound exps env’
      by gs[freeVars_fp_bound_def, freeVars_list_fp_bound_def]
    \\ res_tac \\ gs[EVERYi_lift_MEM])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_arithExp_bound_def]
    \\ ‘freeVars_list_fp_bound exps env’
      by gs[freeVars_fp_bound_def, freeVars_list_fp_bound_def]
    \\ res_tac \\ gs[EVERYi_lift_MEM])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_arithExp_bound_def]
    \\ ‘freeVars_list_fp_bound exps env’
      by gs[freeVars_fp_bound_def, freeVars_list_fp_bound_def]
    \\ res_tac \\ gs[EVERYi_lift_MEM])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_arithExp_bound_def]
    \\ first_x_assum irule \\ gs[freeVars_fp_bound_def])
  >- (
    rveq \\ gs[]
    \\ last_x_assum irule
    \\ gs[freeVars_fp_bound_def, freeVars_list_fp_bound_def])
  \\ ‘freeVars_list_fp_bound exps env’ by gs[freeVars_list_fp_bound_def]
  \\ res_tac \\ first_x_assum irule
QED

Theorem isDoubleExp_freeVars_realExp_bound:
  (∀ e env.
     isDoubleExp e ∧
     freeVars_real_bound e env ⇒
     ∀ (st1:'a semanticPrimitives$state) st2 cfg path.
       freeVars_realExp_bound st1 st2 env cfg path e)
  ∧
  (∀ exps env.
     isDoubleExpList exps ∧
     freeVars_list_real_bound exps env ⇒
     ∀ e. MEM e exps ⇒
          ∀ (st1:'a semanticPrimitives$state) st2 cfg path.
            freeVars_realExp_bound st1 st2 env cfg path e)
Proof
  ho_match_mp_tac isDoubleExp_ind
  \\ rpt strip_tac \\ gs[isDoubleExp_def]
  >- (Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def])
  >~ [‘Let x e1 e2’]
  >- (
    Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def]
    >- (first_x_assum irule \\ gs[freeVars_real_bound_def])
    \\ rpt strip_tac \\ first_x_assum irule
    \\ gs[freeVars_real_bound_def]
    \\ last_x_assum $ qspec_then ‘env’ mp_tac
    \\ impl_tac >- gs[]
    \\ rpt strip_tac
    \\ Cases_on ‘x’ \\ gs[namespaceTheory.nsOptBind_def]
    \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
    \\ rename1 ‘y IN FV e2’
    \\ Cases_on ‘y’ \\ gs[ml_progTheory.nsLookup_nsBind_compute]
    \\ COND_CASES_TAC \\ gs[] \\ rveq
    \\ last_x_assum $ mp_then Any drule (CONJUNCT1 isDoubleExp_evaluates_real)
    \\ gs[] \\ disch_then irule
    \\ gs[freeVars_real_bound_def])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_realExp_bound_def, EVERYi_def]
    \\ rpt strip_tac \\ Cases_on ‘r’ \\ gs[freeVars_realExp_bound_def])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_realExp_bound_def]
    \\ ‘freeVars_list_real_bound exps env’
      by gs[freeVars_real_bound_def, freeVars_list_real_bound_def]
    \\ res_tac \\ gs[EVERYi_lift_MEM_real])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_realExp_bound_def]
    \\ ‘freeVars_list_real_bound exps env’
      by gs[freeVars_real_bound_def, freeVars_list_real_bound_def]
    \\ res_tac \\ gs[EVERYi_lift_MEM_real])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def]
    \\ Cases_on ‘p’ \\ gs[freeVars_realExp_bound_def]
    \\ ‘freeVars_list_real_bound exps env’
      by gs[freeVars_real_bound_def, freeVars_list_real_bound_def]
    \\ res_tac \\ gs[EVERYi_lift_MEM_real])
  >- (
    Cases_on ‘path’ \\ gs[freeVars_realExp_bound_def]
    \\ first_x_assum irule \\ gs[freeVars_real_bound_def])
  >- (
    rveq \\ gs[]
    \\ last_x_assum irule
    \\ gs[freeVars_real_bound_def, freeVars_list_real_bound_def])
  \\ ‘freeVars_list_real_bound exps env’ by gs[freeVars_list_real_bound_def]
  \\ res_tac \\ first_x_assum irule
QED

Definition is_perform_rewrites_correct_def:
  is_perform_rewrites_correct rws (st1:'a semanticPrimitives$state) st2 env cfg e r path <=>
    evaluate st1 env [perform_rewrites cfg path rws e] = (st2, Rval r) /\
    (∀ (st1:'a semanticPrimitives$state) st2. freeVars_arithExp_bound st1 st2 env cfg path e) ∧
    (cfg.canOpt <=> st1.fp_state.canOpt = FPScope Opt) /\
    st1.fp_state.canOpt <> Strict /\
    (~ st1.fp_state.real_sem) ==>
    ? fpOpt choices fpOptR choicesR.
      evaluate (st1 with fp_state :=
                  st1.fp_state with
                     <| rws := st1.fp_state.rws ++ rws;
                        opts := fpOpt;
                        choices := choices |>) env [e] =
      (st2 with fp_state :=
         st2.fp_state with
            <| rws := st2.fp_state.rws ++ rws;
               opts := fpOptR;
               choices := choicesR |>,
       Rval r)
End

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
             (CONJUNCT1 $ CONJUNCT2 evaluate_fp_rws_append);
fun ext_evald_tac t rws opts =
  qpat_x_assum t $ mp_then Any (qspecl_then [rws, opts] strip_assume_tac)
             (CONJUNCT2 $ CONJUNCT2 evaluate_fp_rws_append);
fun ext_choices_tac t choices =
      qpat_x_assum t $ mp_then Any (qspec_then choices assume_tac) (CONJUNCT1 evaluate_add_choices)
fun ext_choicesm_tac t choices =
      qpat_x_assum t $ mp_then Any (qspec_then choices assume_tac) (CONJUNCT1 $ CONJUNCT2 evaluate_add_choices)
fun ext_choicesd_tac t choices =
      qpat_x_assum t $ mp_then Any (qspec_then choices assume_tac) (CONJUNCT2 $ CONJUNCT2 evaluate_add_choices)

fun get_IH t =
  qpat_x_assum t (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))

Theorem perform_rewrites_lift_reverse:
  ∀ exps (st1:'a semanticPrimitives$state) st2 env vs cfg path rws i.
  (∀ (st1:'a semanticPrimitives$state) st2.
    EVERYi
      (λn e. n = i ⇒ freeVars_arithExp_bound st1 st2 env cfg path e)
      exps) ∧
  (∀ e. MEM e exps ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env r.
         (∀ (st1:'a semanticPrimitives$state) st2. freeVars_arithExp_bound st1 st2 env cfg path e) ∧
         (cfg.canOpt ⇔
            st1.fp_state.canOpt = FPScope Opt) ∧
         st1.fp_state.canOpt ≠ Strict ∧ ¬st1.fp_state.real_sem ∧
         evaluate st1 env [perform_rewrites cfg path rws e] = (st2,Rval r) ⇒
         ∃ fpOpt choices fpOptR choicesR.
           evaluate
           (st1 with
            fp_state :=
            st1.fp_state with
                <|rws := st1.fp_state.rws ++ rws; opts := fpOpt;
                  choices := choices|>) env [e] =
           (st2 with
            fp_state :=
            st2.fp_state with
               <|rws := st2.fp_state.rws ++ rws; opts := fpOptR;
                 choices := choicesR|>,Rval r)) ∧
  (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
  st1.fp_state.canOpt ≠ Strict ∧
  (~ st1.fp_state.real_sem) ∧
  evaluate st1 env (REVERSE
                    (MAPi
                     (λn e. if n = i then perform_rewrites cfg path rws e else e)
                     exps)) = (st2,Rval vs) ⇒
  ∃ fpOpt choices fpOptR choicesR.
    evaluate
    (st1 with
     fp_state :=
     st1.fp_state with
        <|rws := st1.fp_state.rws ++ rws; opts := fpOpt;
          choices := choices|>) env (REVERSE exps) =
    (st2 with
     fp_state :=
     st2.fp_state with
        <|rws := st2.fp_state.rws ++ rws; opts := fpOptR;
          choices := choicesR|>,Rval vs)
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
    \\ ‘(λ n e. if n = 0 then perform_rewrites cfg path rws e else e) o SUC = λ n e. e’
       by (fs[FUN_EQ_THM])
    \\ pop_assum (gs o single)
    \\ simp[CaseEq"result", CaseEq"prod"]
    \\ rpt strip_tac \\ rveq \\ gs[] \\ rveq
    \\ gs[EVERYi_def]
    \\ rename1 ‘evaluate st2 env [perform_rewrites cfg path rws e1] = (st3, Rval v1)’
    \\ first_x_assum $ qspec_then ‘e1’ mp_tac
    \\ simp[] \\ disch_then (fn ith => first_assum (fn th => mp_then Any mp_tac ith th))
    \\ impl_tac
    >- (
      rpt conj_tac
      >- (
        rpt strip_tac
        \\ first_x_assum $ qspecl_then [‘st1'’, ‘st2'’] assume_tac \\ gs[])
      \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ strip_tac
    \\ qpat_x_assum ‘evaluate _ _ (REVERSE _) = _’ $ mp_then Any assume_tac (CONJUNCT1 evaluate_fp_rws_append)
    \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] strip_assume_tac)
    \\ first_x_assum $ mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices)
    \\ first_x_assum (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
    \\ gs[semState_comp_eq, fpState_component_equality]
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ simp[Once evaluate_append]
    \\ qpat_x_assum `evaluate _ _ [e1] = _` $ mp_then Any
                    (qspec_then ‘st2.fp_state.choices’ strip_assume_tac)
                    (CONJUNCT1 evaluate_add_choices)
    \\ gs[semState_comp_eq, fpState_component_equality])
  \\ ‘(λ n e. if n = i then perform_rewrites cfg path rws e else e) o SUC =
     λ n e. if n = (i-1) then perform_rewrites cfg path rws e else e’
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
    \\ ‘(λ n e. n = i - 1 ⇒ freeVars_arithExp_bound st1' st2 env cfg path e) =
          (λ n e. n = i ⇒ freeVars_arithExp_bound st1' st2 env cfg path e) o SUC’
       suffices_by (pop_assum (gs o single))
    \\ gs[FUN_EQ_THM] \\ rpt strip_tac \\ gs[] \\ EQ_TAC
    \\ rpt strip_tac \\ gs[])
  \\ strip_tac
  \\ rename1 ‘evaluate st2 env [e1] = (st3, Rval v1)’
  \\ qpat_x_assum `evaluate _ _ [e1] = _` $ mp_then Any assume_tac (CONJUNCT1 evaluate_fp_rws_append)
  \\ pop_assum $ qspecl_then [‘rws’, ‘st3.fp_state.opts’] strip_assume_tac
  \\ pop_assum $ mp_then Any (qspec_then ‘choicesR’ strip_assume_tac) (CONJUNCT1 evaluate_add_choices)
  \\ simp[Once evaluate_append]
  \\ qpat_x_assum `evaluate _ _ (REVERSE _) = _` $ mp_then Any assume_tac (CONJUNCT1 evaluate_fp_rws_append)
  \\ pop_assum $ qspecl_then [‘[]’, ‘fpOpt'’] strip_assume_tac
  \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’
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
               freeVars_arithExp_bound st1 st2
               (env with v := nsAppend (alist_to_ns env_v) env.v) cfg path e') pes) ∧
  (∀ p e. MEM (p,e) pes ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env r.
         (∀ (st1:'a semanticPrimitives$state) st2. freeVars_arithExp_bound st1 st2 env cfg path e) ∧
         (cfg.canOpt ⇔
            st1.fp_state.canOpt = FPScope Opt) ∧
         st1.fp_state.canOpt ≠ Strict ∧ ¬st1.fp_state.real_sem ∧
         evaluate st1 env [perform_rewrites cfg path rws e] = (st2,Rval r) ⇒
         ∃ fpOpt choices fpOptR choicesR.
           evaluate
           (st1 with
            fp_state :=
            st1.fp_state with
                <|rws := st1.fp_state.rws ++ rws; opts := fpOpt;
                  choices := choices|>) env [e] =
           (st2 with
            fp_state :=
            st2.fp_state with
               <|rws := st2.fp_state.rws ++ rws; opts := fpOptR;
                 choices := choicesR|>,Rval r)) ∧
  (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
  st1.fp_state.canOpt ≠ Strict ∧
  (~ st1.fp_state.real_sem) ∧
  evaluate_match st1 env (HD v)
                 (MAPi
                  (λn (p,e). if n = i then (p, perform_rewrites cfg path rws e) else (p,e))
            pes) bind_exn_v = (st2,Rval vs) ⇒
  ∃ fpOpt choices fpOptR choicesR.
    evaluate_match
    (st1 with
     fp_state :=
     st1.fp_state with
        <|rws := st1.fp_state.rws ++ rws; opts := fpOpt;
          choices := choices|>) env (HD v) pes bind_exn_v =
    (st2 with
     fp_state :=
     st2.fp_state with
        <|rws := st2.fp_state.rws ++ rws; opts := fpOptR;
          choices := choicesR|>,Rval vs)
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
    \\ ‘(λ n (p:pat, e). if n = 0 then (p, perform_rewrites cfg path rws e) else (p, e)) o SUC =
        λ n (p,e). (p,e)’
       by (fs[FUN_EQ_THM])
    \\ pop_assum (gs o single)
    \\ COND_CASES_TAC \\ gs[]
    \\ simp[CaseEq"match_result"] \\ rpt strip_tac
    (* Optimised but did not match *)
    >- (
      simp[Once evaluate_def]
      \\ ‘MAPi (λ n (p,e). (p,e)) pes = pes’
        by (rpt $ pop_assum kall_tac \\ Induct_on ‘pes’ \\ gs[]
            \\ rpt strip_tac >- (Cases_on ‘h’ \\ gs[])
            \\ ‘(λ n (p:pat,e:exp). (p, e)) o SUC = λ n (p,e). (p, e)’
               by (gs[FUN_EQ_THM])
            \\ pop_assum $ gs o single)
      \\ pop_assum $ gs o single
      \\ ext_evalm_tac ‘evaluate_match _ _ _ pes _ = _’ ‘rws’ ‘st2.fp_state.opts’
      \\ ext_choicesm_tac ‘evaluate_match _ _ _ _ _ = _’ ‘st1.fp_state.choices’
      \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘st1.fp_state.choices’
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
    \\ gs[Once evaluate_def] \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  \\ ‘(λ n (p:pat,e). if n = i then (p, perform_rewrites cfg path rws e) else (p,e)) o SUC =
     λ n (p,e). if n = i-1 then (p, perform_rewrites cfg path rws e) else (p,e)’
    by (gs[FUN_EQ_THM] \\ Cases_on ‘x’ \\ gs[] \\ rpt strip_tac
        \\ COND_CASES_TAC \\ gs[])
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
                   freeVars_arithExp_bound st1 st2
                     (env with v := nsAppend (alist_to_ns env_v) env.v) cfg
                     path e) =
              (λ n (p,e). n = i ⇒
                ∀ v env_v.
                  pmatch env.c st1'.refs p (HD v) [] = Match env_v ⇒
                 ∀(st1:'a semanticPrimitives$state) st2.
                   freeVars_arithExp_bound st1 st2
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
    \\ strip_tac \\ fsrw_tac [SATISFY_ss][evaluate_def])
  (* First pattern did match *)
  \\ ext_eval_tac ‘evaluate _ _ _ = _’ ‘rws’ ‘st2.fp_state.opts’
  \\ ext_choices_tac ‘evaluate _ _ _ = _’ ‘st1.fp_state.choices’
  \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ gs[evaluate_def, semState_comp_eq, fpState_component_equality]
QED

Theorem perform_rewrites_correct:
  ∀ cfg path rws e (st1:'a semanticPrimitives$state) st2 env r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
       is_rewriteFPexp_list_correct rws st1 st2 env exps r) ∧
    (∀ (st1:'a semanticPrimitives$state) st2.
        freeVars_arithExp_bound st1 st2 env cfg path e) ∧
     (cfg.canOpt <=> st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt <> Strict ∧
     ~st1.fp_state.real_sem ∧
     evaluate st1 env [perform_rewrites cfg path rws e] = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env [e]=
        (st2 with fp_state := st2.fp_state with
                                 <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)
Proof
  ho_match_mp_tac perform_rewrites_ind \\ rpt strip_tac \\ fs[perform_rewrites_def]
  \\ TRY (no_change_tac \\ NO_TAC)
  >- (
    reverse (Cases_on ‘cfg.canOpt’) \\ fs[]
    >- no_change_tac
    \\ fs[freeVars_arithExp_bound_def]
    \\ Cases_on ‘rewriteFPexp rws (App op exps) = App op exps’
    >- (pop_assum $ fs o single
        \\ no_change_tac)
    \\ ‘isFpArithExp (App op exps)’
      by (imp_res_tac icing_rewriterProofsTheory.isFpArithExp_rewrite_preserved)
    \\ res_tac \\ fs[is_rewriteFPexp_list_correct_def]
    \\ first_x_assum (qspecl_then [‘st1’, ‘st2’, ‘env’, ‘[App op exps]’, ‘r’] mp_tac)
    \\ impl_tac >- fs[freeVars_list_fp_bound_def, freeVars_fp_bound_def]
    \\ strip_tac \\ asm_exists_tac \\ fs[])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ COND_CASES_TAC \\ fs[CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ strip_tac \\ rveq
    \\ fs[freeVars_arithExp_bound_def]
    \\ qpat_x_assum `evaluate _ _ (REVERSE _) = _` $ mp_then Any mp_tac perform_rewrites_lift_reverse
    \\ impl_tac >- gs[]
    \\ strip_tac \\ simp[Once evaluate_def]
    \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ [_] = _’ (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ pop_assum (qspecl_then [‘rws'’, ‘st2.fp_state.opts’] strip_assume_tac)
    \\ fs[semState_comp_eq, fpState_component_equality]
    \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’, ‘st2.fp_state.opts’, ‘st2.fp_state.choices’]
    \\ imp_res_tac (CONJUNCT1 evaluate_add_choices)
    \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result", CaseEq"op_class"]
    \\ strip_tac \\ rveq
    \\ fs[freeVars_arithExp_bound_def]
    \\ qpat_x_assum `evaluate _ _ (REVERSE _) = _` $ mp_then Any mp_tac perform_rewrites_lift_reverse
    \\ impl_tac >- gs[]
    \\ strip_tac \\ simp[Once evaluate_def]
    >- (
      Cases_on ‘st1'.clock = 0’ \\ gs[]
      \\ gs[CaseEq"prod", CaseEq"result", CaseEq"option", CaseEq"error_result",
            dec_clock_def]
      \\ rveq \\ gs[]
      \\ ext_evald_tac ‘evaluate_decs _ _ _ = _’ ‘rws’ ‘st2'.fp_state.opts’
      \\ ext_eval_tac ‘evaluate _ _ _ = _’ ‘[]’ ‘fpOpt'’
      \\ gs[st_simps]
      \\ ext_choicesd_tac ‘evaluate_decs _ _ _ = _’ ‘choicesR’
      \\ gs[st_simps]
      \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’ \\ gs[]
      \\ gs[do_eval_res_def, CaseEq"option", CaseEq"prod"]
      \\ rveq \\ gs[] \\ gs[st_simps])
    >- (
      Cases_on ‘st'.clock = 0’ \\ gs[]
      \\ ext_eval_tac ‘evaluate _ _ [e] = _’ ‘rws’ ‘st2.fp_state.opts’
      \\ ext_eval_tac ‘evaluate _ _ (REVERSE exps) = _’ ‘[]’ ‘fpOpt'’
      \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘choicesR’
      \\ gs[st_simps]
      \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’
      \\ gs[st_simps, dec_clock_def])
    >- (
      qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
      \\ gs[semState_comp_eq, fpState_component_equality])
    >- (
      ext_eval_tac ‘evaluate _ _ (REVERSE exps) = _’ ‘[]’
      ‘λ x. if (x = 0) then
              if st'.fp_state.canOpt = FPScope Opt then
                case do_fprw r' (st'.fp_state.opts 0) st'.fp_state.rws of
                  NONE => []
                | SOME r_opt => st'.fp_state.opts 0
              else []
            else []’
      \\ gs[semState_comp_eq, fpState_component_equality]
      \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘choices’
      \\ gs[semState_comp_eq, fpState_component_equality]
      \\ TOP_CASE_TAC \\ gs[shift_fp_opts_def]
      \\ COND_CASES_TAC \\ gs[]
      \\ Cases_on ‘do_fprw r' (st'.fp_state.opts 0) st'.fp_state.rws’
      \\ gs[do_fprw_def]
      \\ Cases_on ‘r'’ \\ gs[] \\ Cases_on ‘a’ \\ gs[]
      \\ rveq \\ gs[rwAllWordTree_def, rwAllBoolTree_def]
      \\ pop_assum mp_tac \\ simp[CaseEq"option"]
      \\ strip_tac \\ rveq
      \\ imp_res_tac rwAllWordTree_append_opt
      \\ imp_res_tac rwAllBoolTree_append_opt
      \\ first_x_assum (qspec_then ‘rws’ assume_tac) \\ gs[]
      \\ rveq \\ gs[])
    >- (‘~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ gs[])
        \\ gs[]))
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac \\ Cases_on ‘v1'’ \\ gs[]
    >- (
      ext_eval_tac ‘evaluate _ _ [e'] = _’ ‘rws’ ‘st2.fp_state.opts’
      \\ ext_eval_tac ‘evaluate _ _ [e] = _’ ‘[]’ ‘fpOpt'’
      \\ ext_choices_tac ‘evaluate _ _ [e'] = _’ ‘choicesR’
      \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
      \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’
      \\ gs[semState_comp_eq, fpState_component_equality])
    \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ Cases_on ‘v1'’ \\ gs[]
    >- (
      ‘e' = perform_rewrites cfg path rws e’
       by (
         qpat_x_assum `do_log _ _ _ = _` mp_tac
         \\ gs[do_log_def] \\ COND_CASES_TAC \\ gs[])
      \\ pop_assum (gs o single)
      \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
      \\ impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ gs[])
      \\ strip_tac
      \\ ext_eval_tac ‘evaluate _ _ [e2] = _’ ‘rws’ ‘fpOpt’
      \\ ext_choices_tac ‘evaluate _ _ [e2] = _’ ‘st1.fp_state.choices’
      \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘st'.fp_state.choices’
      \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
      \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
      \\ gs[semState_comp_eq, fpState_component_equality]
      \\ ‘do_log lop (HD v1) e = SOME (Exp e)’
        by (gs[do_log_def] \\ COND_CASES_TAC \\ gs[])
      \\ pop_assum (gs o single)
      \\ gs[semState_comp_eq, fpState_component_equality])
    \\ ext_eval_tac ‘evaluate _ _ [e2] = _’ ‘rws’ ‘st2.fp_state.opts’
    \\ ext_choices_tac ‘evaluate _ _ [e2] = _’ ‘st1.fp_state.choices’
    \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ gs[do_log_def] \\ COND_CASES_TAC
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ ext_eval_tac ‘evaluate _ _ [e'] = _’ ‘rws’ ‘st2.fp_state.opts’
    \\ ext_eval_tac ‘evaluate _ _ [e] = _’ ‘[]’ ‘fpOpt'’
    \\ ext_choices_tac ‘evaluate _ _ [e'] = _’ ‘choicesR’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ gs[do_if_def] \\ Cases_on ‘HD v = Boolv T’ \\ gs[]
    >- (
      rveq
      \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
      \\ impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ gs[])
      \\ strip_tac
      \\ ext_eval_tac ‘evaluate _ _ [e1] = _’ ‘rws’ ‘fpOpt’
      \\ ext_choices_tac ‘evaluate _ _ [e1] = _’ ‘st1.fp_state.choices’
      \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
      \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘st'.fp_state.choices’
      \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
      \\ gs[semState_comp_eq, fpState_component_equality, do_if_def])
    \\ rveq
    \\ ext_eval_tac ‘evaluate _ _ [e'] = _’ ‘rws’ ‘st2.fp_state.opts’
    \\ ext_eval_tac ‘evaluate _ _ [e1] = _’ ‘rws’ ‘fpOpt’
    \\ ext_choices_tac ‘evaluate _ _ [e1] = _’ ‘st1.fp_state.choices’
    \\ ext_choices_tac ‘evaluate _ _ [e'] = _’ ‘st'.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality]
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def, do_if_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ gs[do_if_def] \\ Cases_on ‘HD v = Boolv T’ \\ gs[]
    >- (
      rveq
      \\ ext_eval_tac ‘evaluate _ _ [e'] = _’ ‘rws’ ‘st2.fp_state.opts’
      \\ ext_eval_tac ‘evaluate _ _ [e1] = _’ ‘rws’ ‘fpOpt’
      \\ ext_choices_tac ‘evaluate _ _ [e1] = _’ ‘st1.fp_state.choices’
      \\ ext_choices_tac ‘evaluate _ _ [e'] = _’ ‘st'.fp_state.choices’
      \\ gs[semState_comp_eq, fpState_component_equality]
      \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
      \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def, do_if_def])
    \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ strip_tac
    \\ ext_eval_tac ‘evaluate _ _ [e1] = _’ ‘rws’ ‘fpOpt’
    \\ ext_choices_tac ‘evaluate _ _ [e1] = _’ ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘st'.fp_state.choices’
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality, do_if_def])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ pop_assum mp_tac \\ COND_CASES_TAC \\ gs[]
    \\ strip_tac
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ ext_evalm_tac ‘evaluate_match _ _ _ pes _ = _’ ‘rws’ ‘st2.fp_state.opts’
    \\ ext_eval_tac ‘evaluate _ _ [e] = _’ ‘[]’ ‘fpOpt'’
    \\ ext_choicesm_tac ‘evaluate_match _ _ _ pes _ = _’ ‘choicesR’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
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
    \\ ext_eval_tac ‘evaluate _ _ [e] = _’ ‘rws’ ‘fpOpt’
    \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘st1.fp_state.choices’
    \\ ext_choicesm_tac ‘evaluate_match _ _ _ _ _ = _’ ‘st'.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality]
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality]
    \\ ‘can_pmatch_all env.c st'.refs (MAP FST pes) (HD v)’
      by (‘$o FST o (λ n (p:pat,e). if n = i then (p, perform_rewrites cfg path rws e) else (p, e)) = $o FST o (λ n (p, e). (p,e))’
            by (gs[FUN_EQ_THM] \\ rpt strip_tac \\ Cases_on ‘x = i’ \\ gs[]
                \\ Cases_on ‘x'’ \\ gs[])
          \\ pop_assum (gs o single)
          \\ ‘MAP FST pes = MAPi ($o FST o (λ n (p,e). (p,e))) pes’
             by (rpt $ pop_assum kall_tac \\ Induct_on ‘pes’
                 \\ gs[] \\ rpt strip_tac >- (Cases_on ‘h’ \\ gs[])
                 \\ AP_THM_TAC \\ AP_TERM_TAC \\ gs[FUN_EQ_THM])
          \\ gs[])
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ ext_eval_tac ‘evaluate _ _ [e2] = _’ ‘rws’ ‘st2.fp_state.opts’
    \\ ext_eval_tac ‘evaluate _ _ [e] = _’ ‘[]’ ‘fpOpt'’
    \\ ext_choices_tac ‘evaluate _ _ [e2] = _’ ‘choicesR’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ qexists_tac ‘fpOpt''’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac
    >- (
      gs[] \\ rpt conj_tac
      >- (res_tac \\ first_x_assum MATCH_ACCEPT_TAC)
      \\ imp_res_tac evaluate_fp_opts_inv \\ gs[])
    \\ strip_tac
    \\ ext_eval_tac ‘evaluate _ _ [e1] = _’ ‘rws’ ‘fpOpt’
    \\ ext_choices_tac ‘evaluate _ _ [e] = _’ ‘st'.fp_state.choices’
    \\ ext_choices_tac ‘evaluate _ _ [e1] = _’ ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality, evaluate_def]
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ COND_CASES_TAC \\ gs[]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ simp[evaluate_def] \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ simp[evaluate_def] \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  >- (
    qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
    \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
    \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
    \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
    \\ impl_tac >- gs[]
    \\ strip_tac
    \\ simp[evaluate_def] \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
    \\ gs[semState_comp_eq, fpState_component_equality])
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[Once evaluate_def, CaseEq"option", CaseEq"prod", CaseEq"result"]
  \\ gs[freeVars_arithExp_bound_def] \\ strip_tac \\ rveq
  \\ get_IH ‘evaluate _ _ [perform_rewrites _ _ _ _] = _’
  \\ impl_tac >- gs[]
  \\ strip_tac
  \\ simp[evaluate_def] \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
  \\ gs[semState_comp_eq, fpState_component_equality]
QED

Theorem is_rewriteFPexp_correct_lift_perform_rewrites:
  ! rws.
    (! (st1 st2:'a semanticPrimitives$state) env e r.
       is_rewriteFPexp_list_correct rws st1 st2 env e r) ==>
    (! path (st1 st2:'a semanticPrimitives$state) env cfg e r.
       is_perform_rewrites_correct rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac
  \\ simp[is_perform_rewrites_correct_def]
  \\ assume_tac perform_rewrites_correct
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [‘cfg’, ‘path’, ‘rws’, ‘e’, ‘st1’, ‘st2’, ‘env’, ‘r’] mp_tac)
  \\ impl_tac
  >- (rpt conj_tac \\ fs[miscTheory.enumerate_def, freeVars_arithExp_bound_def])
  \\ rpt strip_tac \\ fsrw_tac [SATISFY_ss] []
QED

Theorem REVERSE_no_optimisations:
  REVERSE (MAP (\e. no_optimisations cfg e) exps) =
  MAP (no_optimisations cfg) (REVERSE exps)
Proof
  Induct_on `exps` \\ fs[]
QED

Definition freeVars_plan_bound_def:
  freeVars_plan_bound (st1:'a semanticPrimitives$state) st2 env cfg [] e = T ∧
  freeVars_plan_bound (st1:'a semanticPrimitives$state) st2 env cfg (Label s :: plan) e =
    freeVars_plan_bound st1 st2 env cfg plan e ∧
  freeVars_plan_bound (st1:'a semanticPrimitives$state) st2 env cfg (Expected e_opt :: plan) e =
    freeVars_plan_bound (st1:'a semanticPrimitives$state) st2 env cfg plan e ∧
  freeVars_plan_bound (st1:'a semanticPrimitives$state) st2 env cfg (Apply (path, rewrites)::rest) e =
    (freeVars_arithExp_bound st1 st2 env cfg path e ∧
    freeVars_plan_bound st1 st2 env cfg rest (perform_rewrites cfg path rewrites e))
End

Definition isDoubleExpPlan_def:
  isDoubleExpPlan e cfg [] = T ∧
  isDoubleExpPlan e cfg (Label s :: plan) = isDoubleExpPlan e cfg plan ∧
  isDoubleExpPlan e cfg (Expected _:: plan) = isDoubleExpPlan e cfg plan ∧
  isDoubleExpPlan e cfg (Apply (path, rewrites)::plan) =
    (isDoubleExp e ∧ isDoubleExpPlan (perform_rewrites cfg path rewrites e) cfg plan)
End

Theorem freeVars_MAPi_perform_rewrites:
  ∀ exps x i cfg path rws e.
    (∀ e. MEM e exps ⇒ ∀ x. x IN FV (perform_rewrites cfg path rws e) ⇒ x IN FV e) ∧
    x IN FV_list (MAPi (λ n e. if n = i then perform_rewrites cfg path rws e else e) exps) ⇒
    x IN FV_list exps
Proof
  Induct_on ‘exps’ \\ gs[]
  \\ rpt strip_tac
  >- (Cases_on ‘i=0’ \\ gs[])
  \\ Cases_on ‘i = 0’ \\ rveq \\ gs[]
  >- (
    ‘(λ n e. if n = 0 then perform_rewrites cfg path rws e else e) o SUC = λ n e. e’
     by (gs[FUN_EQ_THM])
    \\ pop_assum $ gs o single)
  \\ ‘(λ n e. if n = i then perform_rewrites cfg path rws e else e) o SUC =
      λ n e. if n = i-1 then perform_rewrites cfg path rws e else e’
      by (gs[FUN_EQ_THM] \\ rpt strip_tac \\ COND_CASES_TAC \\ gs[])
  \\ pop_assum $ gs o single
  \\ DISJ2_TAC
  \\ res_tac
  \\ first_x_assum irule \\ gs[]
QED

Theorem freeVars_MAPi_perform_rewrites_pes:
  ∀ pes x i cfg path rws e.
    (∀ p e. MEM (p,e) pes ⇒ ∀ x. x IN FV (perform_rewrites cfg path rws e) ⇒ x IN FV e) ∧
    x IN FV_pes (MAPi (λ n (p,e). if n = i then (p,perform_rewrites cfg path rws e) else (p,e)) pes) ⇒
    x IN FV_pes pes
Proof
  Induct_on ‘pes’ \\ gs[]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ gs[]
  \\ Cases_on ‘i = 0’ \\ rveq \\ gs[]
  >- (
    ‘(λ n (p:pat,e). if n = 0 then (p,perform_rewrites cfg path rws e) else (p,e)) o SUC = λ n (p,e). (p,e)’
     by (gs[FUN_EQ_THM])
    \\ pop_assum $ gs o single
    \\ DISJ2_TAC
    \\ ‘MAPi (λ n (p,e). (p,e)) pes = pes’
       by (rpt $ pop_assum kall_tac \\ Induct_on ‘pes’ \\ gs[] \\ rpt strip_tac \\ gs[FUN_EQ_THM]
           >- (Cases_on ‘h’ \\ gs[])
           \\ pop_assum (fn th => simp [SimpR “$=”, Once (GSYM th)])
           \\ AP_THM_TAC \\ AP_TERM_TAC \\ gs[FUN_EQ_THM])
    \\ pop_assum $ gs o single)
  \\ ‘(λ n (p:pat,e). if n = i then (p, perform_rewrites cfg path rws e) else (p,e)) o SUC =
      λ n (p:pat,e). if n = i-1 then (p, perform_rewrites cfg path rws e) else (p,e)’
      by (gs[FUN_EQ_THM] \\ rpt strip_tac \\ Cases_on ‘x'’ \\ gs[] \\ COND_CASES_TAC \\ gs[])
  \\ pop_assum $ gs o single
  \\ DISJ2_TAC
  \\ res_tac
  \\ first_x_assum irule \\ gs[]
  \\ rpt strip_tac \\ res_tac
QED

Theorem perform_rewrites_freeVars:
  ∀ cfg path rws e x. x IN FV (perform_rewrites cfg path rws e) ⇒ x IN FV e
Proof
  ho_match_mp_tac perform_rewrites_ind
  \\ rpt strip_tac \\ gs[perform_rewrites_def]
  >- (
    Cases_on ‘cfg.canOpt’ \\ gs[]
    \\ qspecl_then [‘rws’, ‘App op exps’, ‘rewriteFPexp rws (App op exps)’,
                    ‘λ x. x IN FV (App op exps)’]
                   mp_tac
                   rewrite_preserves_FV
    \\ impl_tac \\ gs[])
  >- (imp_res_tac freeVars_MAPi_perform_rewrites)
  >- (imp_res_tac freeVars_MAPi_perform_rewrites)
  \\ imp_res_tac freeVars_MAPi_perform_rewrites_pes
  \\ gs[]
QED

Theorem isDoubleExpPlan_freeVars_plan_bound_def:
  ∀ plan e env cfg.
    freeVars_fp_bound e env ∧
    isDoubleExpPlan e cfg plan ⇒
    ∀ (st1:'a semanticPrimitives$state) st2.
      freeVars_plan_bound st1 st2 env cfg plan e
Proof
  Induct_on ‘plan’ \\ gs[freeVars_plan_bound_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ gs[freeVars_plan_bound_def, isDoubleExpPlan_def]
  \\ Cases_on ‘p’ \\ gs[freeVars_plan_bound_def, isDoubleExpPlan_def]
  \\ conj_tac
  >- (drule (CONJUNCT1 isDoubleExp_freeVars_arithExp_bound)
      \\ disch_then drule \\ gs[])
  \\ qmatch_goalsub_abbrev_tac ‘freeVars_plan_bound _ _ _ _ _ e_opt’
  \\ first_x_assum $ qspec_then ‘e_opt’ mp_tac
  \\ disch_then (qspecl_then [‘env’, ‘cfg’] mp_tac)
  \\ impl_tac
  >- (
    gs[freeVars_fp_bound_def] \\ rpt strip_tac \\ unabbrev_all_tac
    \\ imp_res_tac perform_rewrites_freeVars
    \\ res_tac \\ gs[])
  \\ strip_tac \\ gs[]
QED

Theorem isDoubleExpPlan_freeVars_realPlan_bound_def:
  ∀ plan e env cfg.
    freeVars_real_bound e env ∧
    isDoubleExpPlan e cfg plan ⇒
    ∀ (st1:'a semanticPrimitives$state) st2.
      freeVars_realPlan_bound st1 st2 env cfg plan e
Proof
  Induct_on ‘plan’ \\ gs[freeVars_realPlan_bound_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ gs[freeVars_realPlan_bound_def, isDoubleExpPlan_def]
  \\ Cases_on ‘p’ \\ gs[freeVars_realPlan_bound_def, isDoubleExpPlan_def]
  \\ conj_tac
  >- (drule (CONJUNCT1 isDoubleExp_freeVars_realExp_bound)
      \\ disch_then drule \\ gs[])
  \\ qmatch_goalsub_abbrev_tac ‘freeVars_realPlan_bound _ _ _ _ _ e_opt’
  \\ first_x_assum $ qspec_then ‘e_opt’ mp_tac
  \\ disch_then (qspecl_then [‘env’, ‘cfg’] mp_tac)
  \\ impl_tac
  >- (
    gs[freeVars_real_bound_def] \\ rpt strip_tac \\ unabbrev_all_tac
    \\ imp_res_tac perform_rewrites_freeVars
    \\ res_tac \\ gs[])
  \\ strip_tac \\ gs[]
QED

Definition is_optimise_with_plan_correct_def:
  is_optimise_with_plan_correct plan (st1:'a semanticPrimitives$state) st2 env cfg exps r =
  (evaluate st1 env
   (MAP (λ e. FST (optimise_with_plan cfg plan e)) exps) = (st2, Rval r) /\
   (∀ e. MEM e exps ⇒
         (∀ (st1:'a semanticPrimitives$state) st2. freeVars_plan_bound st1 st2 env cfg plan e)) ∧
   (cfg.canOpt <=> st1.fp_state.canOpt = FPScope Opt) /\
   st1.fp_state.canOpt <> Strict /\
   (~ st1.fp_state.real_sem) ==>
   let theRws = FLAT (MAP (λ x. case x of |Apply (_, rws) => rws |_ => []) plan) in
   ? fpOpt choices fpOptR choicesR.
     evaluate (st1 with fp_state := st1.fp_state with
                                       <| rws := st1.fp_state.rws ++ theRws;
                                          opts := fpOpt; choices := choices |>) env exps =
     (st2 with fp_state := st2.fp_state with
                              <| rws := st2.fp_state.rws ++ theRws;
                                 opts := fpOptR; choices := choicesR |>, Rval r))
End

Theorem Map_FST_optimise_with_plan:
  MAP FST (MAP (\ (p, e). (p, optimise_with_plan cfg plan e)) l) = MAP FST l
Proof
  Induct_on ‘l’ \\ fs[] \\ rpt strip_tac \\ PairCases_on ‘h’ \\ fs[]
QED

Theorem optimise_with_plan_empty_sing:
  ! cfg e. optimise_with_plan cfg [] e = (e, Success)
Proof
  fs[optimise_with_plan_def]
QED

Theorem optimise_with_plan_empty:
  ! exps cfg. MAP (λ e. FST (optimise_with_plan cfg [] e)) exps = exps
Proof
  Induct_on ‘exps’ \\ rpt strip_tac
  >- (EVAL_TAC)
  \\ rpt strip_tac \\ fs[optimise_with_plan_def, optimise_with_plan_empty_sing]
QED

Theorem optimise_with_plan_pat_empty:
  ! pl cfg. MAP (λ (p,e). (p, FST (optimise_with_plan cfg [] e))) pl = pl
Proof
  Induct_on ‘pl’ \\ rpt strip_tac >- (EVAL_TAC)
  \\ fs[] \\ Cases_on ‘h’ \\ fs[optimise_with_plan_empty_sing]
QED

Theorem is_optimise_with_plan_correct_lift_sing:
  ∀ plan.
    (∀ rws path.
       MEM (Apply (path, rws)) plan ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
         is_perform_rewrites_correct rws st1 st2 env cfg e r path) ==>
    (! (st1:'a semanticPrimitives$state) st2 env cfg e r.
       is_optimise_with_plan_correct plan st1 st2 env cfg [e] r)
Proof
  Induct_on ‘plan’
  \\ rpt strip_tac
  \\ simp[is_optimise_with_plan_correct_def]
  >- (
    rpt strip_tac
    \\ fs[optimise_with_plan_def]
    \\ qexistsl_tac [‘st1.fp_state.opts’, ‘st1.fp_state.choices’,
                     ‘st2.fp_state.opts’, ‘st2.fp_state.choices’]
    \\ ‘st1 with
        fp_state :=
        st1.fp_state with
           <|rws := st1.fp_state.rws; opts := st1.fp_state.opts;
             choices := st1.fp_state.choices|> = st1’ by simp[semState_comp_eq, fpState_component_equality]
    \\ ‘st2 with
        fp_state :=
        st2.fp_state with
           <|rws := st2.fp_state.rws; opts := st2.fp_state.opts;
             choices := st2.fp_state.choices|> = st2’ by simp[semState_comp_eq, fpState_component_equality]
    \\ simp[semState_comp_eq, fpState_component_equality])
  \\ Cases_on ‘h’
  \\ simp[optimise_with_plan_def]
  >~ [‘Expected e’]
  >- (
    Cases_on ‘optimise_with_plan cfg plan e'’ \\ gs[freeVars_plan_bound_def]
    \\ COND_CASES_TAC \\ rveq \\ fs[is_optimise_with_plan_correct_def]
    \\ rpt strip_tac
    >- (res_tac \\ gs[] \\ asm_exists_tac \\ fs[])
    \\ first_assum $ mp_then Any assume_tac (CONJUNCT1 (prep evaluate_fp_rws_up))
    \\ pop_assum $ qspec_then ‘st1.fp_state.rws ++ FLAT (MAP (λ x. case x of |Apply (_, rws) => rws |_ => []) plan)’ strip_assume_tac
    \\ pop_assum mp_tac \\ impl_tac >- fs[]
    \\ strip_tac
    \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ first_x_assum $ mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices)
    \\ first_x_assum (qspec_then ‘st1.fp_state.choices’ assume_tac)
    \\ rfs[semState_comp_eq, fpState_component_equality]
    \\ asm_exists_tac \\ fs[])
  >~ [‘Label s’]
  >- (gs[is_optimise_with_plan_correct_def, freeVars_plan_bound_def] \\ rpt strip_tac
      \\ res_tac \\ asm_exists_tac \\ fs[])
  >~ [‘Apply p’]
  \\ Cases_on ‘p’
  \\ simp[optimise_with_plan_def]
  \\ Cases_on ‘optimise_with_plan cfg plan e’ \\ gs[]
  \\ COND_CASES_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_assum $ mp_then Any assume_tac (CONJUNCT1 (prep evaluate_fp_rws_up))
    \\ pop_assum $ qspec_then ‘st1.fp_state.rws ++ r' ++ FLAT (MAP (λ x. case x of |Apply (_, rws) => rws |_ => []) plan)’ strip_assume_tac
    \\ pop_assum mp_tac \\ impl_tac >- (fs[SUBSET_DEF] \\ strip_tac \\ metis_tac[])
    \\ strip_tac
    \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ first_x_assum $ mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices)
    \\ first_x_assum (qspec_then ‘st1.fp_state.choices’ assume_tac)
    \\ rfs[semState_comp_eq, fpState_component_equality]
    \\ asm_exists_tac \\ fs[])
  \\ COND_CASES_TAC \\ fs[]
  >- (
    rpt strip_tac \\ rfs[is_perform_rewrites_correct_def] \\ rveq
    \\ qpat_assum `evaluate _ _ _ = _` (fn th => first_x_assum (fn thm => mp_then Any assume_tac thm th))
    \\ gs[freeVars_plan_bound_def] \\ asm_exists_tac \\ fs[])
  \\ Cases_on ‘optimise_with_plan cfg plan (perform_rewrites cfg q r' e)’
  \\ fs[freeVars_plan_bound_def]
  \\ COND_CASES_TAC \\ rveq
  >- (
    rpt strip_tac
    \\ first_assum $ mp_then Any assume_tac (CONJUNCT1 (prep evaluate_fp_rws_up))
    \\ pop_assum $ qspec_then ‘st1.fp_state.rws ++ r' ++ FLAT (MAP (λ x. case x of |Apply (_, rws) => rws |_ => []) plan)’ strip_assume_tac
    \\ pop_assum mp_tac \\ impl_tac >- fs[SUBSET_DEF]
    \\ strip_tac
    \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ first_x_assum $ mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices)
    \\ first_x_assum (qspec_then ‘st1.fp_state.choices’ assume_tac)
    \\ rfs[semState_comp_eq, fpState_component_equality]
    \\ asm_exists_tac \\ fs[])
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [‘r'’, ‘q’] mp_tac) \\ impl_tac >- fs[]
  \\ strip_tac
  \\ last_x_assum $ qspecl_then [‘st1’, ‘st2’, ‘env’, ‘cfg’,
                                 ‘perform_rewrites cfg q r' e’, ‘r’] mp_tac
  \\ simp[is_optimise_with_plan_correct_def]
  \\ impl_tac >- gs[]
  \\ strip_tac
  \\ fs[is_perform_rewrites_correct_def]
  \\ pop_assum (fn th => first_x_assum (fn thm => mp_then Any mp_tac thm th)
                \\ assume_tac th)
  \\ impl_tac
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ strip_tac
  \\ qspecl_then [‘(st1 with
                    fp_state :=
                    st1.fp_state with
                       <|rws := st1.fp_state.rws ++
                                FLAT (MAP (λ x. case x of
                                                |Apply (_, rws) => rws
                                                |_ => []) plan) ++ r';
                           opts := fpOpt'; choices := choices'|>)’,
                    ‘env’, ‘[e]’] strip_assume_tac (CONJUNCT1 evaluate_fp_rws_up)
  \\ fs[]
  \\ rfs[]
  \\ pop_assum (qspec_then ‘st1.fp_state.rws ++ r' ++
                             FLAT (MAP (λ x. case x of
                                             |Apply (_, rws) => rws
                                             |_ => []) plan)’
                mp_tac)
  \\ impl_tac
  \\ fs[GSYM UNION_ASSOC, CONJUNCT1 SUBSET_UNION, Once UNION_COMM, SUBSET_DEF]
  \\ disch_then strip_assume_tac
  \\ qexistsl_tac [‘fpOpt''’, ‘choices'’, ‘fpOpt2’, ‘choicesR'’]
  \\ simp[semState_comp_eq, fpState_component_equality]
  \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
QED

Theorem is_optimise_with_plan_correct_lift:
  ! plan.
    (! rws path.
       MEM (Apply (path, rws)) plan ==>
       ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
         is_perform_rewrites_correct rws st1 st2 env cfg e r path) ==>
    (! (st1:'a semanticPrimitives$state) st2 env cfg exps r.
       is_optimise_with_plan_correct plan st1 st2 env cfg exps r)
Proof
  ntac 2 strip_tac
  \\ Induct_on ‘exps’
  \\ simp[is_optimise_with_plan_correct_def]
  \\ rpt strip_tac
  >- (rveq \\ simp[semState_comp_eq, fpState_component_equality])
  \\ drule is_optimise_with_plan_correct_lift_sing
  \\ strip_tac
  \\ simp[Once evaluate_cons]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ ( assume_tac o SIMP_RULE bool_ss [Once evaluate_cons, CaseEq"prod", CaseEq"result"] )
  \\ fs[] \\ rveq
  \\ first_x_assum (qspecl_then [‘st1’, ‘s'’, ‘env’, ‘cfg’, ‘h’, ‘vs’] mp_tac)
  \\ simp[is_optimise_with_plan_correct_def]
  \\ strip_tac
  \\ first_x_assum (qspecl_then [‘s'’, ‘s''’, ‘env’, ‘cfg’, ‘vs'’] mp_tac)
  \\ simp[is_optimise_with_plan_correct_def] \\ impl_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ strip_tac
  \\ optUntil_tac ‘evaluate _ _ [h] = _’ ‘fpOpt'’
  \\ qexistsl_tac [‘optUntil (choicesR - choices) fpOpt fpOpt'’, ‘choices’] \\ fs[]
  \\ qpat_x_assum ‘evaluate _ _ exps = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ disch_then (qspec_then ‘choicesR’ assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem stos_pass_with_plans_sing_exists:
  ! e plan. ? e_opt res. HD (stos_pass_with_plans cfg [plan] [e]) = (e_opt, res)
Proof
  rpt strip_tac \\ measureInduct_on ‘exp_size e’ \\ Cases_on ‘e’
  \\ simp[stos_pass_with_plans_def]
  >~ [‘Fun s e’]
  >- (
    fs[astTheory.exp_size_def]
    \\ first_x_assum $ qspec_then ‘e’ mp_tac
    \\ impl_tac \\ fs[] \\ strip_tac
    \\ fs[])
  \\ qmatch_goalsub_abbrev_tac ‘optimise_with_plan cfg plan e_inp’
  \\ Cases_on ‘optimise_with_plan cfg plan e_inp’ \\ fsrw_tac [SATISFY_ss] []
QED

Theorem stos_pass_with_plans_sing[simp]:
  [ HD (stos_pass_with_plans cfg [plan] [e]) ] = stos_pass_with_plans cfg [plan] [e]
Proof
  Cases_on ‘e’
  >~ [‘Fun s e’]
  >- (rewrite_tac[Once stos_pass_with_plans_def]
      \\ qspecl_then [‘e’, ‘plan’] strip_assume_tac stos_pass_with_plans_sing_exists
      \\ asm_rewrite_tac [Once stos_pass_with_plans_def]
      \\ simp[])
  \\ fs[stos_pass_with_plans_def, astTheory.exp_size_def]
QED

Theorem stos_pass_with_plans_empty:
  ! e. stos_pass_with_plans cfg [] [e] = [(e, Success)]
Proof
  strip_tac \\ measureInduct_on ‘exp_size e’ \\ Cases_on ‘e’
  \\ fs[stos_pass_with_plans_def]
  \\ rename [‘Fun s e’]
  \\ first_x_assum $ qspec_then ‘e’ mp_tac \\ impl_tac \\ fs[astTheory.exp_size_def]
QED

Theorem stos_pass_with_plans_cons:
  ! plan1 plans e1 es cfg.
  stos_pass_with_plans cfg (plan1::plans) (e1::es) =
  stos_pass_with_plans cfg [plan1] [e1] ++ stos_pass_with_plans cfg plans es
Proof
  rpt strip_tac \\ Cases_on ‘plans’ \\ fs[stos_pass_with_plans_def]
  \\ Cases_on ‘es’ \\ fs[stos_pass_with_plans_def, stos_pass_with_plans_empty]
QED

Theorem stos_pass_with_plans_decs_cons:
  stos_pass_with_plans_decs cfg (p1::ps) [e1] =
  stos_pass_with_plans_decs cfg [p1] [e1] ++ stos_pass_with_plans_decs cfg ps []
Proof
  Cases_on ‘ps’ \\ fs[stos_pass_with_plans_decs_def]
QED

Theorem opt_pass_with_plans_decs_unfold:
  no_opt_decs cfg (
    MAP FST (
      stos_pass_with_plans_decs cfg plans [Dlet loc p e])) =
  [(Dlet loc p (HD (no_optimise_pass cfg ([FST (HD (stos_pass_with_plans cfg plans [e]))]))))]
Proof
  Cases_on ‘plans’
  \\ simp[stos_pass_with_plans_decs_def, no_opt_decs_def, HD,
          Once stos_pass_with_plans_decs_cons, no_optimise_pass_def, HD,
          stos_pass_with_plans_def, stos_pass_with_plans_empty]
  \\ qspecl_then [‘e’, ‘h’] strip_assume_tac stos_pass_with_plans_sing_exists
  \\ fs[Once stos_pass_with_plans_cons, stos_pass_with_plans_def]
  \\ simp[no_opt_decs_def]
QED

Theorem stos_pass_with_plans_fun_unfold:
  no_optimise_pass cfg [FST (HD (stos_pass_with_plans cfg plans [Fun s e]))] =
  [Fun s (HD (no_optimise_pass cfg [FST (HD (stos_pass_with_plans cfg plans [e]))]))]
Proof
  Cases_on ‘plans’
  \\ simp[stos_pass_with_plans_def, no_optimise_pass_def,Once  optimise_with_plan_def,
          Once stos_pass_with_plans_cons,
          stos_pass_with_plans_sing, stos_pass_with_plans_empty]
  \\ qspecl_then [‘h’, ‘t’,‘e’, ‘[]’, ‘cfg’] assume_tac stos_pass_with_plans_cons
  \\ pop_assum (rewrite_tac o single)
  \\ fs[stos_pass_with_plans_def]
  \\ qspecl_then [‘e’, ‘h’] strip_assume_tac stos_pass_with_plans_sing_exists
  \\ fs[no_optimise_pass_def]
QED

Theorem optimise_with_plan_scope:
  ! cfg plan sc e x. optimise_with_plan cfg plan (FpOptimise sc e) = x ==>
  ?e' res. x = (FpOptimise sc e', res)
Proof
  Induct_on ‘plan’
  >- fs[optimise_with_plan_empty_sing]
  >- (
    rpt strip_tac
    \\ Cases_on ‘h’
    >~ [‘Apply opt’]
    >- (
      Cases_on ‘opt’ \\ fs[optimise_with_plan_def]
      \\ pop_assum mp_tac
      \\ COND_CASES_TAC \\ strip_tac \\ rveq \\ fsrw_tac [SATISFY_ss] []
      \\ COND_CASES_TAC \\ rveq \\ TRY (Cases_on ‘q’
                                        \\ fsrw_tac [SATISFY_ss] [perform_rewrites_def])
      \\ first_x_assum $ qspecl_then [‘cfg’, ‘sc’, ‘perform_rewrites (cfg with canOpt := (sc = Opt)) o' r e’] strip_assume_tac
      \\ fs[]
      \\ COND_CASES_TAC \\ rveq \\ fsrw_tac [SATISFY_ss] [])
    \\ fs[optimise_with_plan_def] \\ metis_tac[])
QED

Theorem opt_pass_with_plans_scope_unfold:
  no_optimise_pass cfg [FST (HD (stos_pass_with_plans cfg plans [FpOptimise sc e]))] =
  [no_optimisations cfg (FST (optimise_with_plan cfg (case plans of |[] => [] | _ => HD plans) (FpOptimise sc e)))]
Proof
  Cases_on ‘plans’
  >- fs[optimise_with_plan_empty_sing, stos_pass_with_plans_empty,
        no_optimise_pass_def]
  \\ simp[Once stos_pass_with_plans_cons, stos_pass_with_plans_def]
  \\ qspecl_then [‘cfg’, ‘h’, ‘sc’, ‘e’] strip_assume_tac
                 (SIMP_RULE std_ss [PULL_EXISTS] optimise_with_plan_scope)
  \\ fs[no_optimise_pass_def]
QED

Theorem genlist_is_all_distinct:
  ! f i. (! a b. a <> b ==> f a <> f b) ==> ALL_DISTINCT (GENLIST f i)
Proof
  fs[ALL_DISTINCT_GENLIST]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘! a b. _ ==> _’ (qspecl_then [‘m1’, ‘m2’] strip_assume_tac)
  \\ qspecl_then [‘m1 <> m2’, ‘f m1 <> f m2’] strip_assume_tac (GEN_ALL MONO_NOT_EQ) \\ fs[]
QED

Theorem FIND_exists:
  ! P l. (? x. MEM x l /\ P x) ==> FIND P l <> NONE
Proof
  Induct_on ‘l’ \\ fs[]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘!P. _ ==> _’ (qspec_then ‘P’ assume_tac)
  \\ fs[FIND_thm] \\ rveq
  \\ Cases_on ‘P h’ \\ fs[]
  \\ qpat_x_assum ‘_ ==> _’ imp_res_tac
QED

Theorem longer_and_distinct_exists:
  ! l l'. ALL_DISTINCT l /\ LENGTH l > LENGTH l' ==> ? x. MEM x l /\ ~ MEM x l'
Proof
  rpt strip_tac
  \\ qspec_then ‘set l'’ strip_assume_tac LESS_CARD_DIFF \\ fs[]
  \\ pop_assum (qspec_then ‘set l’ strip_assume_tac) \\ fs[]
  \\ rfs[Once ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ qspec_then ‘l'’ strip_assume_tac (GEN_ALL CARD_LIST_TO_SET)
  \\ fs[]
  \\ ‘CARD (set l') < LENGTH l’ by fs[]
  \\ fs[]
  \\ ‘CARD (set l) - CARD (set l INTER set l') = CARD ((set l) DIFF (set l'))’ by fs[CARD_DIFF_EQN]
  \\ ‘0 < CARD (set l DIFF set l')’ by fs[]
  \\ ‘(set l DIFF set l') <> {} ’ by (
    qspec_then ‘set l DIFF set l'’ strip_assume_tac CARD_EQ_0
    \\ ‘FINITE (set l DIFF set l')’ by fs[FINITE_DIFF]
    \\ qpat_x_assum ‘FINITE _ ==> _’ imp_res_tac
    \\ Cases_on ‘set l DIFF set l' = {} ’ \\ simp[]
    \\ qpat_x_assum ‘set l DIFF set l' = {} ==> CARD (set l DIFF set l') = 0’ imp_res_tac
    \\ pop_assum mp_tac \\ qpat_x_assum ‘0 < CARD (set l DIFF set l')’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ rpt strip_tac
    \\ pop_assum (assume_tac o GSYM)
    \\ decide_tac
    )
  \\ qspec_then ‘set l DIFF set l'’ imp_res_tac CHOICE_DEF
  \\ fs[DIFF_applied]
  \\ qexists_tac ‘CHOICE (set l DIFF set l')’
  \\ fs[]
QED

Theorem all_distinct_MEM_FIND:
  ! l l'. ALL_DISTINCT l /\ LENGTH l > LENGTH l' ==> FIND (λ x. ~MEM x l') l = v ==> v <> NONE
Proof
  rpt strip_tac
  \\ qspecl_then [‘(λ x. ~MEM x l')’, ‘l’] strip_assume_tac FIND_exists
  \\ fs[]
  \\ qspecl_then [‘l’, ‘l'’] imp_res_tac longer_and_distinct_exists
  \\ qpat_x_assum ‘_ ==> _’ imp_res_tac
QED

Theorem FIND_result_fulfills:
  ! P l v. FIND P l = SOME v ==> P v
Proof
  Induct_on ‘l’ \\ fs[]
  \\ fs[FIND_thm]
  \\ rpt strip_tac
  \\ Cases_on ‘P h’ \\ fs[] \\ rveq \\ fs[]
QED

Triviality v_size_ALOOKUP:
  ! ls n v.
  ALOOKUP ls n = SOME v ==>
  v_size v + 1 < v4_size ls + c
Proof
  Induct_on ‘ls’ \\ fs[ALOOKUP_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ fs[ALOOKUP_def]
  \\ Cases_on ‘q = n’ \\ fs[] \\ rveq
  \\ fs[semanticPrimitivesTheory.v_size_def]
  \\ res_tac
  \\ fs[]
QED

Triviality v3_size_ALOOKUP:
  ! ls s env.
  ALOOKUP ls s = SOME env ==>
  v3_size env < v5_size ls + c
Proof
  Induct_on ‘ls’ \\ fs[ALOOKUP_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ fs[ALOOKUP_def]
  \\ Cases_on ‘q = s’ \\ fs[] \\ rveq
  \\ fs[semanticPrimitivesTheory.v_size_def]
  \\ res_tac
  \\ fs[]
QED

Theorem env_size_decreasing:
  ! env x v.
  nsLookup env x = SOME v ==>
  v_size v + 1 < v3_size env
Proof
  ho_match_mp_tac namespaceTheory.nsLookup_ind
  \\ rpt strip_tac
  \\ fs[namespaceTheory.nsLookup_def, semanticPrimitivesTheory.v_size_def, CaseEq"option"]
  >- (imp_res_tac v_size_ALOOKUP \\ metis_tac[])
  \\ res_tac \\ fs[]
  \\ imp_res_tac v3_size_ALOOKUP
  \\ first_x_assum (qspec_then ‘v4_size env + 1’ assume_tac) \\ fs[]
QED

Definition v_sim_def[simp]:
  (v_sim [] [] <=> T)/\
  (v_sim (x1::y1::z1) (x2::y2::z2) <=> (v_sim [x1] [x2] /\ v_sim (y1::z1) (y2::z2))) /\
  (v_sim [FP_WordTree fp1] [FP_WordTree fp2] <=> compress_word fp1 = compress_word fp2)/\
  (v_sim [FP_BoolTree fp1] [FP_BoolTree fp2] <=> compress_bool fp1 = compress_bool fp2)/\
  (v_sim [Conv ts1 vs1] [Conv ts2 vs2] <=> (ts1 = ts2) /\ v_sim vs1 vs2 )/\
  (v_sim [Vectorv vs1] [Vectorv vs2] <=> v_sim vs1 vs2 )/\
  (v_sim [Closure env s e] [Closure env2 s2 e2] <=> e = e2 /\ s = s2 /\ env_sim (env.v) (env2.v)) /\
  (v_sim [Recclosure env1 defs1 n1] [Recclosure env2 defs2 n2] <=>
            defs1 = defs2 /\ n1 = n2 /\ env_sim (env1.v) (env2.v)) /\
  (v_sim v1 v2 <=>  v1 = v2)
  /\
  env_sim env1 env2 =
    ((! (x:(string,string) id) v1.
      nsLookup env1 x = SOME v1 ==>
      ? v2. nsLookup env2 x = SOME v2 /\
      v_sim [v1] [v2]) /\
    (! x. nsLookup env1 x = NONE ==> nsLookup env2 x = NONE))
Termination
  wf_rel_tac ‘measure (λ x. case x of | INR p => ((v3_size o FST) p)+2 | INL p => (v1_size o FST) p)’
  \\ fs[] \\ conj_tac
  >- (rpt strip_tac \\ Cases_on ‘env’ \\ fs[semanticPrimitivesTheory.v_size_def])
  \\ conj_tac
  >- ( Cases_on`env1` \\ simp[semanticPrimitivesTheory.v_size_def] )
  \\ rpt strip_tac
  \\ imp_res_tac env_size_decreasing
  \\ fs[semanticPrimitivesTheory.v_size_def]
End

val v_sim_ind = theorem"v_sim_ind";

Definition v_sim1_def[simp]:
  (v_sim1 (FP_WordTree fp1) (FP_WordTree fp2) <=> compress_word fp1 = compress_word fp2)/\
  (v_sim1 (FP_BoolTree fp1) (FP_BoolTree fp2) <=> compress_bool fp1 = compress_bool fp2)/\
  (v_sim1 (Conv ts1 vs1) (Conv ts2 vs2) <=> (ts1 = ts2) /\ v_sim vs1 vs2 )/\
  (v_sim1 (Vectorv vs1) (Vectorv vs2) <=> v_sim vs1 vs2 ) /\
  (v_sim1 (Closure env s e) (Closure env2 s2 e2) <=> e = e2 /\ s = s2 /\ env_sim (env.v) (env2.v)) /\
  (v_sim1 (Recclosure env1 defs1 n1) (Recclosure env2 defs2 n2) <=>
            defs1 = defs2 /\ n1 = n2 /\ env_sim (env1.v) (env2.v)) /\
  (v_sim1 v1 v2 <=> (v1 = v2))
End

Theorem v_sim_LIST_REL:
  (!v1 v2. v_sim v1 v2 <=> LIST_REL v_sim1 v1 v2) /\
  (! env1 env2. env_sim env1 env2 ==> T)
Proof
  ho_match_mp_tac v_sim_ind \\ rw[] \\ Cases_on`v6` \\ rw[]
QED

Theorem v_sim_empty_r:
  ! xs ys. v_sim xs ys /\ ys = [] ==> xs = []
Proof
  rw[v_sim_LIST_REL] \\ fs[]
QED

Theorem v_sim_empty_l:
  ! xs ys. v_sim xs ys /\ xs = [] ==> ys = []
Proof
  rw[v_sim_LIST_REL] \\ fs[]
QED

Definition noopt_sim_def[simp]:
  noopt_sim (Rerr (Rraise v1)) (Rerr (Rraise v2)) = v_sim1 v1 v2 /\
  noopt_sim ((Rerr e1):(v list, v) semanticPrimitives$result) v2 = (v2 = Rerr e1) /\
  noopt_sim (Rval vs1) (Rval vs2) = v_sim vs1 vs2 /\
  noopt_sim _ _ = F
End

Theorem noopt_sim_val[simp]:
  noopt_sim (Rval vs1) v2 ==>
  ? vs2. v2 = Rval vs2
Proof
  Cases_on ‘v2’ \\ simp[noopt_sim_def]
QED

Theorem noopt_sim_val_fp[simp]:
  noopt_sim (Rval [FP_WordTree fp1]) (Rval vs2) ==>
  ? fp2. vs2 = [FP_WordTree fp2] /\ compress_word fp1 = compress_word fp2
Proof
  simp[noopt_sim_def]
  \\ Cases_on`vs2` \\ simp[]
  \\ Cases_on`t` \\ simp[]
  \\ Cases_on`h` \\ simp[]
QED

Theorem v_sim_cons:
  v_sim (x::xs) (y::ys) <=> v_sim [x] [y] /\ v_sim xs ys
Proof
  rw[v_sim_LIST_REL]
QED

Theorem v_sim_refl[simp]:
  ! vs. v_sim vs vs /\ ! env. env_sim env env
Proof
  `(!vs1 vs2. vs1 = vs2 ==> v_sim vs1 vs2) /\ (! env1 env2. env1 = env2 ==> env_sim env1 env2)` suffices_by rw[]
  \\ ho_match_mp_tac v_sim_ind \\ rw[]
  \\ res_tac \\ fs[]
QED

Theorem v_sim1_refl[simp]:
  !v. v_sim1 v v
Proof
  `!v1 v2. (v1 = v2) ==> v_sim1 v1 v2` suffices_by rw[]
  \\ recInduct v_sim1_ind \\ rw[]
QED

Theorem noopt_sim_refl[simp]:
  noopt_sim r r
Proof
  Cases_on ‘r’ \\ simp[noopt_sim_def]
  \\ Cases_on`e` \\ simp[]
QED

Theorem noopt_sim_rerr_rval[simp]:
  ~noopt_sim (Rerr x) (Rval y) /\
  ~noopt_sim (Rval z) (Rerr w)
Proof
  Cases_on`x` \\ Cases_on`w` \\ simp[]
QED

Theorem v_sim_fpoptimise:
  (! vs1 vs2.
  v_sim vs1 vs2 ==>
  v_sim (do_fpoptimise annot1 vs1) (do_fpoptimise annot2 vs2))
  /\
  (! env1 env2.
   env_sim env1 env2 ==> T)
Proof
  ho_match_mp_tac v_sim_ind
  \\ fs[v_sim_def, do_fpoptimise_def, fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  \\ fs[v_sim_LIST_REL, LIST_REL_APPEND_suff]
QED

Theorem do_log_v_sim1:
  !v1 v2.
  v_sim1 v1 v2 ==>
  ! e1 e2.
    do_log l v2 e2 =
    case do_log l v1 e1 of
    | NONE => NONE
    | SOME (Val v) => SOME (Val v)
    | SOME (Exp _) => SOME (Exp e2)
Proof
  simp[do_log_def, Boolv_def]
  \\ Cases \\ Cases \\ simp[]
  \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs[]
  \\ Cases_on`l'` \\ Cases_on`l''` \\ fs[v_sim_LIST_REL]
  \\ rw[]
QED

Theorem pmatch_v_sim1:
  (!envC refs p v env.
     !v2 env2.  v_sim1 v v2 /\ MAP FST env = MAP FST env2 /\ v_sim (MAP SND env) (MAP SND env2)  ==>
     case pmatch envC refs p v env of
     | Match_type_error => pmatch envC refs p v2 env2 = Match_type_error
     | No_match => pmatch envC refs p v2 env2 = No_match
     | Match env3 => ?env4. pmatch envC refs p v2 env2 = Match env4 /\
                            MAP FST env3 = MAP FST env4 /\ v_sim (MAP SND env3) (MAP SND env4)) /\
  (!envC refs ps vs env.
     !vs2 env2. v_sim vs vs2 /\ MAP FST env = MAP FST env2 /\ v_sim (MAP SND env) (MAP SND env2)  ==>
     case pmatch_list envC refs ps vs env of
     | Match_type_error => pmatch_list envC refs ps vs2 env2 = Match_type_error
     | No_match => pmatch_list envC refs ps vs2 env2 = No_match
     | Match env3 => ?env4. pmatch_list envC refs ps vs2 env2 = Match env4 /\
                            MAP FST env3 = MAP FST env4 /\ v_sim (MAP SND env3) (MAP SND env4))
Proof
  ho_match_mp_tac pmatch_ind
  \\  rw[pmatch_def] \\  rw[pmatch_def]
  \\ TRY(Cases_on`v2` \\ fs[pmatch_def])
  \\ rveq \\ fs[pmatch_def]
  \\ imp_res_tac v_sim_LIST_REL \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[pmatch_def]
  \\ TRY(fs[v_sim_LIST_REL] \\ NO_TAC)
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[v_sim_LIST_REL] \\ rfs[]
  \\ fs[GSYM v_sim_LIST_REL] \\ res_tac \\ fs[] \\ rfs[]
QED

Theorem can_pmatch_all_v_sim1:
  !envC refs ps v1 v2.
    v_sim1 v1 v2 ==>
      can_pmatch_all envC refs ps v1 = can_pmatch_all envC refs ps v2
Proof
  Induct_on`ps`
  \\ rw[can_pmatch_all_def]
  \\ drule (CONJUNCT1 pmatch_v_sim1)
  \\ disch_then(qspecl_then[`envC`,`refs`,`h`,`[]`,`[]`]mp_tac)
  \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ strip_tac \\ simp[]
QED

val _ = augment_srw_ss[rewrites[fp_translate_def]];

Theorem fp_translate_v_sim1:
  v_sim1 v1 v2 ==>
    case fp_translate v1 of
    | NONE => fp_translate v2 = NONE
    | SOME w1 => ?w2. fp_translate v2 = SOME w2 /\ v_sim1 w1 w2
Proof
  Cases_on`v1` \\ Cases_on`v2` \\ rw[]
  \\ Cases_on`l` \\ rw[]
QED

(* TODO: move *)
Theorem do_eq_refl:
  (!v1 v2.  v1 = v2 ==> do_eq v1 v2 = Eq_val T) /\
  (!v1 v2 .  v1 = v2 ==> do_eq_list v1 v2 = Eq_val T)
Proof
  ho_match_mp_tac do_eq_ind \\ rw[do_eq_def]
QED

Theorem do_eq_v_sim1:
  (!v1 v2 v3 v4.
     v_sim1 v1 v2 /\ v_sim1 v3 v4 ==>
       do_eq v1 v3 = do_eq v2 v4) /\
  (!v1 v2 v3 v4.
    v_sim v1 v2 /\ v_sim v3 v4 ==>
      do_eq_list v1 v3 = do_eq_list v2 v4)
Proof
  ho_match_mp_tac do_eq_ind \\ rw[do_eq_def]
  \\ Cases_on`v3` \\ Cases_on`v4` \\ fs[do_eq_def, Boolv_def] \\ rw[]
  \\ rw[] \\ fs[v_sim_LIST_REL] \\ rfs[] \\ fs[]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
  \\ TRY(Cases_on`l1` \\ fs[do_eq_def] \\ NO_TAC)
  \\ TRY (qmatch_assum_rename_tac`v_sim1 v3 v4`
          \\ Cases_on`v3` \\ Cases_on`v4` \\ fs[do_eq_def] \\ NO_TAC)
  \\ TRY(Cases_on`l` \\ fs[do_eq_def] \\ NO_TAC)
  \\ res_tac \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ first_x_assum irule \\ rw[]
  \\ `do_eq v2 v2 = Eq_val T` suffices_by metis_tac[v_sim1_refl]
  \\ rw[do_eq_refl]
QED

Theorem v_to_char_list_v_sim1:
  !x y. v_sim1 x y ==> v_to_char_list x = v_to_char_list y
Proof
  recInduct v_to_char_list_ind
  \\ rw[v_to_char_list_def]
  \\ TRY(Cases_on`y`) \\ fs[]
  \\ rveq \\ fs[v_to_char_list_def, v_sim_LIST_REL]
  \\ rveq \\ fs[]
  \\ TRY(Cases_on`y`) \\ fs[CaseEq"option", v_to_char_list_def]
  \\ TRY(Cases_on`v`) \\ fs[ v_to_char_list_def]
  \\ rveq \\ fs[]
  \\ qmatch_assum_rename_tac`v_sim l1 l2`
  \\ qmatch_goalsub_rename_tac`Conv name l1`
  \\ first_x_assum(qspec_then`Conv name l2` mp_tac)
  \\ simp[v_to_char_list_def]
  \\ metis_tac[option_CASES]
QED

Theorem v_to_list_v_sim1:
  !x y. v_sim1 x y ==>
    case v_to_list x of
    NONE => v_to_list y = NONE
    | SOME v2 => ?v3. v_to_list y = SOME v3 /\ v_sim v2 v3
Proof
  recInduct v_to_list_ind
  \\ rw[v_to_list_def]
  \\ TRY(Cases_on`y`) \\ fs[]
  \\ rveq \\ fs[v_to_list_def, v_sim_LIST_REL]
  \\ rveq \\ fs[]
  \\ first_x_assum drule
  \\ fs[CaseEq"option"]
  \\ TOP_CASE_TAC \\ fs[]
  \\ strip_tac \\ fs[]
QED

Theorem vs_to_string_v_sim:
  !x y. v_sim x y ==> vs_to_string x = vs_to_string y
Proof
  recInduct vs_to_string_ind
  \\ rw[vs_to_string_def]
  \\ TRY(Cases_on`y`) \\ fs[]
  \\ rveq \\ fs[vs_to_string_def, v_sim_LIST_REL]
  \\ rveq \\ fs[vs_to_string_def]
  \\ TRY(Cases_on`h`) \\ fs[vs_to_string_def]
  \\ first_x_assum drule \\ fs[]
QED

Theorem list_to_v_v_sim1:
  !l1 l2.
  v_sim l1 l2
  ==>
  v_sim1 (list_to_v l1) (list_to_v l2)
Proof
  Induct \\ rw[list_to_v_def]
  \\ fs[v_sim_LIST_REL, list_to_v_def]
QED

Triviality sv_rel_v_sim1_refl:
  LIST_REL (sv_rel v_sim1) x x
Proof
  irule EVERY2_refl \\ rw[]
QED

val _ = augment_srw_ss[rewrites[sv_rel_v_sim1_refl]];

Theorem do_app_v_sim:
  v_sim v1 v2 ==>
    case do_app x op v1 of
    | NONE => do_app x op v2 = NONE
    | SOME ((sv1, y), r1) =>
      ? sv2 r2.
        do_app x op v2 = SOME ((sv2, y), r2) /\
        LIST_REL (sv_rel v_sim1) sv1 sv2 /\ (isPureOp op ==> sv1 = sv2) /\
        noopt_sim (list_result r1) (list_result r2)
Proof
  rw[v_sim_LIST_REL]
  \\ TOP_CASE_TAC
  >- (
    pop_assum mp_tac
    \\ rename1 ‘do_app sffi op v1’
    \\ Cases_on `sffi`
    \\ simp[Once do_app_def]
    \\ strip_tac
    \\ fs[CaseEq"list"] \\ rveq \\ fs[] \\ rveq \\ fs[]
    >- rw[do_app_def]
    \\ fs[CaseEq"list", CaseEq"option", CaseEq"op"] \\ rveq \\ fs[] \\ rveq
    \\ TRY (simp[do_app_def] \\ NO_TAC)
    \\ fs[CaseEq"v", CaseEq"list", CaseEq"lit", CaseEq"word_size", CaseEq"eq_result", CaseEq"option"]
    \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ TRY (simp[do_app_def]
            \\ TRY(qmatch_assum_rename_tac`fp_translate fpv = _` \\ Cases_on`fpv` \\ fs[] \\ rveq
                   \\ TRY(qmatch_assum_rename_tac`fp_translate (Litv l) = _` \\ Cases_on`l`)
                   \\ fs[] \\ rveq)
            \\ rpt(qmatch_assum_rename_tac`v_sim1 (_ _) v2` \\ Cases_on`v2` \\ fs[] \\ rveq)
            \\ NO_TAC)
    \\ TRY (CHANGED_TAC(imp_res_tac do_eq_v_sim1) \\ rw[do_app_def] \\ fs[] \\ NO_TAC)
    \\ TRY (CHANGED_TAC(imp_res_tac fp_translate_v_sim1) \\ rfs[] \\ rw[do_app_def]
            \\ TOP_CASE_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[] \\ NO_TAC)
    >- ( fs[do_app_def, store_assign_def, store_v_same_type_def] )
    >- ( fs[do_app_def, store_alloc_def] )
    >- ( fs[do_app_def, CaseEq"option"] \\ imp_res_tac v_to_char_list_v_sim1 \\ fs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[]
         \\ imp_res_tac vs_to_string_v_sim \\ fs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[v_sim_LIST_REL]
         \\ imp_res_tac LIST_REL_LENGTH
         \\ TOP_CASE_TAC \\ fs[] )
    >- ( fs[do_app_def, store_alloc_def] \\ TOP_CASE_TAC \\ fs[] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[store_alloc_def]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ fs[v_sim_LIST_REL] )
    >- ( fs[do_app_def, store_alloc_def])
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ fs[store_assign_def, store_v_same_type_def] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ fs[store_assign_def, store_v_same_type_def] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ Cases_on ‘y’ \\ gs[v_sim1_def] \\ rpt (TOP_CASE_TAC \\ gs[v_sim_def])))
  \\ ntac 2 TOP_CASE_TAC
  \\ Cases_on`x`
  \\ pop_assum(strip_assume_tac o REWRITE_RULE[semanticPrimitivesPropsTheory.do_app_cases])
  \\ rveq \\ fs[] \\ simp[do_app_def] \\ rveq \\ fs[]
  \\ TRY(rpt (TOP_CASE_TAC \\ rfs[]) \\ NO_TAC)
  >- ( imp_res_tac do_eq_v_sim1 \\ fs[] )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_cmp_def, fpSemTheory.compress_bool_def]  )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_uop_def, fpSemTheory.compress_word_def]  )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_bop_def, fpSemTheory.compress_word_def]  )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_top_def, fpSemTheory.compress_word_def]  )
  >- (
    fs[store_assign_def, store_v_same_type_def]
    \\ rveq \\ fs[isPureOp_def]
    \\ irule EVERY2_LUPDATE_same \\ fs[] )
  >- (
    fs[store_alloc_def, isPureOp_def] \\ rveq
    \\ irule LIST_REL_APPEND_suff \\ fs[] )
  >- ( imp_res_tac v_to_char_list_v_sim1 \\ fs[] )
  >- (
    imp_res_tac v_to_list_v_sim1 \\ rfs[]
    \\ imp_res_tac vs_to_string_v_sim \\ fs[] )
  >- ( imp_res_tac v_to_list_v_sim1 \\ rfs[] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[v_sim_LIST_REL]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    fs[store_alloc_def, isPureOp_def] \\ rveq
    \\ irule LIST_REL_APPEND_suff \\ fs[]
    \\ simp[LIST_REL_REPLICATE_same] )
  >- (
    fs[store_alloc_def, isPureOp_def] \\ rveq
    \\ irule LIST_REL_APPEND_suff \\ fs[])
  >- (
    fs[store_assign_def, store_v_same_type_def, isPureOp_def] \\ rveq
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_refl \\ fs[])
  >- (
    fs[store_assign_def, store_v_same_type_def, isPureOp_def] \\ rveq
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_refl \\ fs[])
  \\ imp_res_tac v_to_list_v_sim1
  \\ rfs[]
  \\ fs[v_sim_LIST_REL]
  \\ irule list_to_v_v_sim1
  \\ fs[v_sim_LIST_REL]
  \\ irule LIST_REL_APPEND_suff
  \\ fs[]
QED

Theorem build_conv_v_sim:
  v_sim v1 v2 ==>  OPTREL v_sim1 (build_conv envc x v1 ) (build_conv envc x v2)
Proof
  rw[build_conv_def]
  \\ TOP_CASE_TAC \\ simp[OPTREL_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
QED

(** Proofs about no_optimisations **)
local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
   ! st env cfg st2 r choices fpScope.
   evaluate st env [no_optimisations cfg e] = (st2, r) /\
   st.fp_state.canOpt <> FPScope Opt /\
   isPureExp e ==>
     ! env2.
       env_sim (env.v) env2 ==>
       ? choices2 r2.
         evaluate
           (st with fp_state :=
            st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices |>)
        (env with v := env2) [e] =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) /\ noopt_sim r r2”
  (* P4: string * exp -> bool *)
  val P4 =
  Parse.Term (‘λ (s:string, e). ^P0 e’);
  (* P2: string * string * exp -> bool *)
  val P2 =
  Parse.Term (‘λ (s1:string, s2:string, e). ^P0 e’);
  (* Letrec goal *)
  val P1 =
  Parse.Term (‘λ (l:(string # string # exp) list).
  ! p. MEM p l ==> ^P2 p’)
  (* P5: pat * exp -> bool *)
  val P5 =
  Parse.Term (‘λ (p:pat, e). ^P0 e’)
  (* P3: pat * exp list -> bool *)
  val P3 =
  Parse.Term (‘λ (pes:(pat # exp) list).
  ! st env v cfg err_v st2 r cfg choices fpScope.
  evaluate_match st env v (MAP (λ (p,e). (p, no_optimisations cfg e)) pes) err_v = (st2, r) /\
  st.fp_state.canOpt <> FPScope Opt /\
  isPurePatExpList pes ==>
    ! env2 v2 err_v2. env_sim env.v env2 /\ v_sim1 v v2 /\ v_sim1 err_v err_v2 ==>
    ? choices2 r2.
      evaluate_match
        (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices|>)
      (env with v := env2) v2 pes err_v2 =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) /\ noopt_sim r r2’);
  (* P6: exp list -> bool *)
  val P6 =
    Parse.Term (‘λ (es:ast$exp list). ! e. MEM e es ==> ^P0 e’);
  val ind_thm =
    astTheory.exp_induction |> SPEC P0 |> SPEC P1 |> SPEC P2 |> SPEC P3
    |> SPEC P4 |> SPEC P5 |> SPEC P6;
in

Triviality lift_P6_noopt_REVERSE:
  ! es.
    ^P6 es ==>
   ! (st:'a semanticPrimitives$state) env cfg st2 r choices fpScope.
   evaluate st env (MAP (no_optimisations cfg) es) = (st2, r) /\
   st.fp_state.canOpt <> FPScope Opt /\
   isPureExpList es ==>
     ! env2.
     env_sim env.v env2 ==>
     ? choices2 r2.
       evaluate
         (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices |>)
        (env with v := env2) es =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) /\
        noopt_sim r r2
Proof
  Induct \\ fs[]
  >- rw[semanticPrimitivesTheory.state_component_equality,fpState_component_equality]
  \\ srw_tac[DNF_ss][]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ rw[Once evaluate_cons]
  \\ rw[Once evaluate_cons]
  \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- metis_tac[])
  \\ strip_tac \\ fs[]
  \\ fs[CaseEq"prod"]
  \\ last_x_assum (first_assum o mp_then Any (qspecl_then[`choices`, `fpScope`]strip_assume_tac))
  \\ ntac 2 (first_x_assum (first_assum o mp_then Any assume_tac))
  \\ fs[isPureExp_def] \\ rfs[]
  \\ reverse(fs[CaseEq"result"] \\ rveq \\ Cases_on`r2` \\ fs[noopt_sim_def])
  >- rw[semanticPrimitivesTheory.state_component_equality,fpState_component_equality]
  \\ fs[CaseEq"prod"]
  \\ first_x_assum (first_assum o mp_then Any (qspecl_then[`choices2`, `fpScope`]strip_assume_tac))
  \\ ntac 2 (first_x_assum (first_assum o mp_then Any assume_tac)) \\ fs[]
  \\ ‘s'.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`evaluate s1 envA es`
  \\ qmatch_goalsub_abbrev_tac`evaluate s11 envA es`
  \\ `s1 = s11` by (
    rw[Abbr`s1`, Abbr`s11`, semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[FUN_EQ_THM])
  \\ fs[Abbr`s1`, Abbr`s11`]
  \\ Cases_on`r2` \\ fs[noopt_sim_def]
  \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
  \\ rw[semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv \\ fs[FUN_EQ_THM]
  \\ fs[v_sim_LIST_REL, LIST_REL_APPEND_suff]
QED

Theorem no_optimisations_backwards_sim:
  (! e. ^P0 e) /\ (! l. ^P1 l) /\ (! p. ^P2 p) /\ (! l. ^P3 l) /\ (! p. ^P4 p)
  /\ (! p. ^P5 p) /\ (! l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[]
  \\ rpt strip_tac
  \\ (qpat_x_assum ‘evaluate _ _ _  = _’ mp_tac
      ORELSE qpat_x_assum ‘evaluate_match _ _ _ _ _ = _’ mp_tac
     ORELSE ALL_TAC)
  \\ fs[isPureExp_def]
  \\ simp[no_optimisations_def, Once evaluate_def]
  >- (
   ntac 2 (reverse TOP_CASE_TAC  \\ fs[])
   \\ res_tac
   \\ ntac 2 (first_x_assum (first_assum o mp_then Any strip_assume_tac))
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] strip_assume_tac)
   >- (
    Cases_on`r2` \\ strip_tac \\ rveq \\ fs[]
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq, noopt_sim_def])
   \\ imp_res_tac noopt_sim_val \\ rveq \\ fs[noopt_sim_def, do_if_def]
   \\ imp_res_tac evaluate_sing \\ rveq \\ fs[v_sim_LIST_REL, v_sim1_def] \\ rveq
   \\ rename1 ‘v1 = Boolv T’
   \\ Cases_on ‘v1 = Boolv T’ \\ rveq \\ fs[Boolv_def] \\ rveq
   >- (
    rpt strip_tac
    \\ Cases_on ‘v’ \\ fs[v_sim1_def] \\ rveq
    \\ ‘q.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ res_tac
    \\ rpt (first_x_assum (qspecl_then [‘fpScope’, ‘choices2’] assume_tac))
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq,
          noopt_sim_def, do_if_def, Boolv_def]
    \\ Cases_on ‘l’ \\ fs[v_sim_def]
    \\ ‘st.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope|> =
       q.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope |>’
     by (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
    \\ pop_assum (fs o single)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
   \\ TOP_CASE_TAC \\ fs[]
   >- (
    strip_tac \\ rveq \\ fs[evaluate_def, do_if_def]
    \\ Cases_on ‘v = Boolv T’ \\ fs[v_sim1_def]
    >- (‘v1 = Boolv T’ suffices_by (rveq \\ fs[Boolv_def])
        \\ Cases_on ‘v1’ \\ fs[v_sim1_def, Boolv_def]
        \\ imp_res_tac v_sim_empty_r \\ fs[] \\ rveq)
    \\ Cases_on ‘v = Boolv F’ \\ fs[v_sim1_def]
    >- (‘v1 = Boolv F’ suffices_by (rveq \\ fs[Boolv_def])
        \\ Cases_on ‘v1’ \\ fs[v_sim1_def, Boolv_def]
        \\ imp_res_tac v_sim_empty_r \\ fs[] \\ rveq)
    \\ fs[fpState_component_equality, semState_comp_eq])
    \\ rpt strip_tac
    \\ Cases_on ‘v’ \\ fs[v_sim1_def] \\ rveq
    \\ ‘q.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ res_tac
    \\ rpt (first_x_assum (qspecl_then [‘fpScope’, ‘choices2’] assume_tac))
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq,
          noopt_sim_def, do_if_def, Boolv_def]
    \\ Cases_on ‘l’ \\ fs[v_sim_def]
    \\ ‘st.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope|> =
        q.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope |>’
      by (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
    \\ pop_assum (fs o single)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ last_x_assum (first_x_assum o mp_then Any assume_tac)
    \\ pop_assum (first_assum o mp_then Any (qspecl_then[`choices`,`fpScope`]strip_assume_tac))
    \\ pop_assum (first_assum o mp_then Any strip_assume_tac)
    \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
    \\ ‘st.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length
    \\ fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[v_sim_LIST_REL]
    \\ drule do_log_v_sim1
    \\ disch_then(qspecl_then[`l`,`no_optimisations cfg e0`,`e0`]strip_assume_tac)
    \\ simp[] \\ rveq \\ fs[]
    \\ fs[CaseEq"option", CaseEq"exp_or_val"] \\ rveq \\ fs[] \\ rfs[]
    \\ TRY (rw[semState_comp_eq, fpState_component_equality, noopt_sim_def] \\ PROVE_TAC[])
    \\ `e' = no_optimisations cfg e0` by (fs[do_log_def, CaseEq"bool"] \\ rveq \\ fs[Boolv_def])
    \\ rveq \\ fs[]
    \\ last_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`]strip_assume_tac))
    \\ rpt (pop_assum (first_assum o mp_then Any strip_assume_tac))
    \\ qmatch_asmsub_abbrev_tac`evaluate s1 envA [e0]`
    \\ qmatch_goalsub_abbrev_tac`evaluate s11 envA [e0]`
    \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rveq \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`]strip_assume_tac))
    \\ ntac 2 (pop_assum (first_assum o mp_then Any strip_assume_tac))
    \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
    \\ ‘st.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length
    \\ fs[LENGTH_EQ_NUM_compute] \\ rveq \\ fs[v_sim_LIST_REL]
    \\ rveq \\ fs[]
    \\ last_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`]strip_assume_tac))
    \\ qmatch_asmsub_abbrev_tac`evaluate s1 _ [e0]`
    \\ qmatch_goalsub_abbrev_tac`evaluate s11 _ [e0]`
    \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rveq \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rename1 ‘nsOptBind so v env2’
    \\ first_x_assum (qspec_then ‘nsOptBind so v env2’ mp_tac)
    \\ impl_tac
    >- (Cases_on ‘so’ \\ fs[namespaceTheory.nsOptBind_def]
        \\ fs[v_sim_def]
        \\ rpt strip_tac \\ Cases_on ‘x''’
        \\ TRY (fs[ml_progTheory.nsLookup_nsBind_compute]
                \\ TOP_CASE_TAC \\ fs[])
        \\ fs[namespaceTheory.nsBind_def])
    \\ strip_tac
    \\ fs[sem_env_component_equality, semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
  >- (
   rpt strip_tac \\ rveq \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] strip_assume_tac)
   \\ fs[ semState_comp_eq, fpState_component_equality])
  >- (
   rpt strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] strip_assume_tac)
   \\ fs[ semState_comp_eq, fpState_component_equality])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ simp[Once evaluate_def]
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- simp[] \\ strip_tac
    \\ reverse(fs[CaseEq"result", CaseEq"error_result"] \\ rveq \\ fs[noopt_sim_def])
    \\ ‘st.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length \\ fs[LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs[v_sim_LIST_REL] \\ rveq
    \\ drule can_pmatch_all_v_sim1
    \\ strip_tac \\ fs[]
    \\ reverse(fs[CaseEq"bool", MAP_MAP_o, o_DEF, UNCURRY, ETA_AX])
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 $ CONJUNCT2 evaluate_fp_opts_inv))
    \\ qmatch_assum_rename_tac`v_sim1 v1 v2`
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`,`env2`, `v2`, `bind_exn_v`]mp_tac))
    \\ impl_tac >- simp[] \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`evaluate_match s1 _ v2`
    \\ qmatch_goalsub_abbrev_tac`evaluate_match s11 _ v2`
    \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rw[]
    \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
  >- (
   rpt gen_tac
   \\ simp[no_optimisations_def, Once evaluate_def] \\ strip_tac
   \\ res_tac \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac) \\ fs[]
   \\ simp[evaluate_def, fpState_component_equality, semState_comp_eq])
  >- (
   rpt gen_tac
   \\ simp[no_optimisations_def, Once evaluate_def]
   \\ strip_tac \\ fs[CaseEq"prod"]
   \\ first_x_assum(first_x_assum o mp_then Any (qspecl_then[`choices`,`f`,`env2`]mp_tac))
   \\ simp[] \\ strip_tac
   \\ Cases_on`st.fp_state.canOpt = Strict` \\ fs[CaseEq"result"] \\ rveq \\ fs[]
   \\ Cases_on`r2` \\ fs[]
   \\ rw[semState_comp_eq, fpState_component_equality, v_sim_fpoptimise])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
   TOP_CASE_TAC \\ fs[] \\ rpt strip_tac
   \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality]
   \\ rveq \\ res_tac
   \\ fs[noopt_sim_def, semState_comp_eq, fpState_component_equality])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ fsrw_tac[ETA_ss][GSYM MAP_REVERSE]
    \\ qspec_then`REVERSE l`mp_tac lift_P6_noopt_REVERSE
    \\ simp[PULL_FORALL]
    \\ disch_then(first_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac
    >- (
      simp[] \\ rpt gen_tac \\ rpt strip_tac
      \\ first_x_assum drule \\ disch_then drule
      \\ disch_then match_mp_tac \\ simp[] )
    \\ strip_tac \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"result"]) \\ Cases_on`r2` \\ fs[] \\ rveq \\ fs[]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ fs[CaseEq"op_class"]
    >- (Cases_on ‘o'’ \\ fs[astTheory.getOpClass_def, isPureOp_def])
    >- (Cases_on ‘o'’ \\ fs[astTheory.getOpClass_def, isPureOp_def])
    \\ `v_sim (REVERSE vs) (REVERSE a)` by fs[v_sim_LIST_REL]
    \\ drule do_app_v_sim
    \\ qmatch_asmsub_abbrev_tac`do_app x op`
    \\ disch_then(qspecl_then[`x`,`op`]mp_tac)
    \\ map_every qunabbrev_tac[`x`,`op`]
    \\ TRY (
      fs[CaseEq"bool",CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
      \\ TRY(strip_tac \\ fs[])
      \\ rw[semState_comp_eq, fpState_component_equality, shift_fp_opts_def]
      \\ Cases_on`st.fp_state.real_sem` \\ fs[noopt_sim_def]
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
      \\ NO_TAC )
    \\ TOP_CASE_TAC \\ fs[]
    >- ( rw[semState_comp_eq, fpState_component_equality] )
    \\ fs[CaseEq"prod"] \\ strip_tac \\ fs[]
    \\ rveq \\ fs[]
    \\ ‘st'.fp_state.canOpt <> FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on ‘fpScope = Opt’
    \\ fs[do_fprw_def, rwAllWordTree_def, rwAllBoolTree_def, shift_fp_opts_def,
          semState_comp_eq, fpState_component_equality]
    \\ Cases_on ‘isFpBool o'’ \\ fs[]
    \\ Cases_on ‘r'’ \\ Cases_on ‘r2’ \\ fs[noopt_sim_def]
    \\ fs[v_sim_LIST_REL]
    \\ Cases_on ‘a'’ \\ Cases_on ‘a''’ \\ fs[v_sim1_def])
  >- (
    strip_tac \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"bool"])
    >- simp[semState_comp_eq, fpState_component_equality]
    \\ fs[CaseEq"prod"]
    \\ fsrw_tac[ETA_ss][GSYM MAP_REVERSE]
    \\ qspec_then`REVERSE l`mp_tac lift_P6_noopt_REVERSE
    \\ simp[PULL_FORALL]
    \\ disch_then(first_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- (
      simp[] \\ rpt gen_tac \\ rpt strip_tac
      \\ first_x_assum drule \\ disch_then drule
      \\ disch_then match_mp_tac \\ simp[] )
    \\ strip_tac \\ simp[]
    \\ reverse(fs[CaseEq"result"]) \\ Cases_on`r2` \\ fs[] \\ rveq \\ fs[]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ `v_sim (REVERSE vs) (REVERSE a)` by fs[v_sim_LIST_REL]
    \\ drule build_conv_v_sim
    \\ qmatch_goalsub_rename_tac`build_conv env.c xx _`
    \\ disch_then(qspecl_then[`xx`,`env.c`]mp_tac)
    \\ simp[OPTREL_def] \\ strip_tac \\ fs[] \\ rveq \\ fs[]
    \\ rw[semState_comp_eq, fpState_component_equality]
    \\ fs[v_sim_LIST_REL])
  >- (rpt strip_tac \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality])
  >- (
    Cases_on`p`
    \\ simp[Once evaluate_def]
    \\ strip_tac
    \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"bool"])
    >- simp[semState_comp_eq, fpState_component_equality]
    \\ last_assum (mp_then Any mp_tac (CONJUNCT1 pmatch_v_sim1))
    \\ disch_then (qspecl_then[`env.c`,`st.refs`,`q`,`[]`,`[]`]mp_tac)
    \\ simp[]
    \\ reverse(fs[CaseEq"match_result"])
    \\ TRY(simp[semState_comp_eq, fpState_component_equality]
           \\ rveq \\ fsrw_tac[DNF_ss][] \\ NO_TAC)
    >- (
      strip_tac \\ fs[]
      \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
      \\ qmatch_goalsub_abbrev_tac`evaluate _ (env with v := env22)`
      \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env22`]mp_tac))
      \\ impl_tac >- (
        fs[isPureExp_def]
        \\ qmatch_assum_rename_tac`MAP FST env1 = MAP FST env4`
        \\ qmatch_goalsub_abbrev_tac `nsLookup env11`
        \\ `!x. case nsLookup env11 x  of
                | NONE => nsLookup env22 x = NONE
                | SOME v1 => ?v2. nsLookup env22 x = SOME v2 /\ v_sim1 v1 v2` suffices_by (
              rw[]
              \\ first_x_assum(qspec_then`x`mp_tac) \\ rw[]
              \\ rw[v_sim_LIST_REL] )
        \\ gen_tac
        \\ simp[Abbr`env22`, Abbr`env11`]
        \\ TOP_CASE_TAC \\ fs[namespacePropsTheory.nsLookup_nsAppend_none]
        \\ fs[namespacePropsTheory.nsLookup_alist_to_ns_none, ALOOKUP_FAILS]
        \\ TRY (Cases_on`p1` \\ fs[namespacePropsTheory.nsLookupMod_alist_to_ns] \\ NO_TAC)
        >- (
          rw[]
          \\ `!x. MEM x (MAP FST env1) = MEM x (MAP FST env4)` by simp[]
          \\ fs[MEM_MAP, EXISTS_PROD]
          \\ metis_tac[] )
        \\ reverse(fs[namespacePropsTheory.nsLookup_nsAppend_some])
        \\ fs[namespacePropsTheory.nsLookup_alist_to_ns_some,
              namespacePropsTheory.nsLookup_alist_to_ns_none]
        >- (
          res_tac \\ fs[v_sim_LIST_REL]
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ simp[]
          \\ disj2_tac
          \\ conj_tac
          >- (
            fs[ALOOKUP_FAILS]
            \\ `!x. MEM x (MAP FST env1) = MEM x (MAP FST env4)` by simp[]
            \\ fs[MEM_MAP, EXISTS_PROD]
            \\ metis_tac[] )
          \\ Cases \\ simp[] )
        \\ fs[ALOOKUP_LEAST_EL]
        \\ rfs[]
        \\ rveq
        \\ simp[]
        \\ fs[v_sim_LIST_REL]
        \\ fs[LIST_REL_EL_EQN]
        \\ first_x_assum match_mp_tac
        \\ numLib.LEAST_ELIM_TAC
        \\ fs[MEM_EL]
        \\ conj_tac >- metis_tac[]
        \\ CCONTR_TAC \\ fs[]
        \\ `n < n'` by simp[]
        \\ metis_tac[] )
      \\ rw[] )
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 $ CONJUNCT2 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ fs[isPureExp_def] )
  >- (rpt strip_tac \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality] \\ rw[])
QED
end;

Theorem no_optimisations_eval_sim =
  CONJUNCT1 (SIMP_RULE std_ss [] no_optimisations_backwards_sim)
  |> SPEC_ALL
  |> GEN “es:ast$exp list”
  |> SPEC “[e:ast$exp]”
  |> UNDISCH_ALL
  |> SPEC “(env:v sem_env).v”
  |> DISCH_ALL
  |> SIMP_RULE std_ss [MAP, v_sim_refl]
  |> GEN_ALL ;

Theorem do_foptimise_cons:
  !y x .
  do_fpoptimise f (x::y) = (do_fpoptimise f [x]) ++ (do_fpoptimise f y)
Proof
  Induct>>EVAL_TAC>>simp[]
QED

Theorem evaluate_no_optimisations:
  ! fpScope choices.
  evaluate st env [realify (no_optimisations cfg e)] = (st, Rval [Real r]) /\
  (st.fp_state.canOpt <> FPScope Opt /\ isPureExp e) ==>
  ? st2.
    evaluate
      (st with fp_state := st.fp_state with
         <| rws := []; opts := (λ x. []); choices:= choices; canOpt := FPScope fpScope|>)
      env [realify e] = (st2, Rval [Real r])
Proof
  rpt strip_tac \\ fs[realify_no_optimisations_comm]
  \\ last_x_assum
     (mp_then Any mp_tac
      (SIMP_RULE std_ss [] no_optimisations_backwards_sim |> CONJUNCT1))
  \\ fs[isPureExp_realify]
  \\ disch_then (qspecl_then [‘choices’, ‘fpScope’, ‘env.v’] mp_tac)
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ imp_res_tac noopt_sim_val \\ rveq
  \\ fs[noopt_sim_def, v_sim_LIST_REL]
QED

Inductive res_sim:
  (! (e1:v error_result) (e2:v error_result) (cfg:config) (st1:'a semanticPrimitives$state).
   res_sim (Rerr e1) (Rerr e2) cfg st1)
  /\
  (! (vs1:v list) (vs2:v list) (cfg:config) (st1:'a semanticPrimitives$state).
   v_list_sim vs1 vs2 cfg st1 ==>
   res_sim (Rval vs1) (Rval vs2) cfg st1)
  /\
  (! (cfg:config) (st1:'a semanticPrimitives$state).
   v_list_sim [] [] cfg st1) /\
  (! v1 v2 vs1 vs2 cfg st1 .
   v_list_sim vs1 vs2 cfg st1 /\
   v1 = v2 ==>
   v_list_sim (v1::vs1) (v2::vs2) cfg st1)
  /\
  (! v1 v2 vs1 vs2 cfg env s e (st1:'a semanticPrimitives$state) plan.
    rws = FLAT (MAP (λ x. case x of |Apply (_, rws) => rws | _ => []) plan) ∧
   v_list_sim vs1 vs2 cfg st1 /\
   v2 = Closure env s e /\
   v1 = Closure env s (FST (HD (stos_pass_with_plans cfg [plan] [e]))) /\
   (! st r1 (st2:'a semanticPrimitives$state).
    st1.fp_state.rws = st.fp_state.rws ==>
    evaluate st env (MAP FST (stos_pass_with_plans cfg [plan] [e])) = (st2, Rval r1) /\
    (cfg.canOpt <=> st.fp_state.canOpt = FPScope Opt) /\
    (st.fp_state.canOpt <> Strict) /\
    (~ st.fp_state.real_sem) ==>
    ? fpOpt choices fpOptR choicesR r2.
    (evaluate (st with fp_state := st.fp_state with
               <| rws := st.fp_state.rws ++ rws ; opts := fpOpt; choices := choices |>) env [e] =
     (st2 with fp_state := st2.fp_state with
      <| rws := st2.fp_state.rws ++ rws ; opts := fpOptR; choices := choicesR |>, Rval r2)) /\
    res_sim (Rval r1) (Rval r2) cfg st1) ==>
   v_list_sim (v1::vs1) (v2::vs2) cfg st1)
End

Theorem v_list_sim_append:
  v_list_sim (vs1 ++ vs2) (vs1 ++ vs3) cfg st1 =
  v_list_sim vs2 vs3 cfg st1
Proof
  Induct_on ‘vs1’ \\ fs[res_sim_rules]
  \\ rpt strip_tac \\ EQ_TAC
  >- (
   rpt strip_tac
   \\ last_x_assum (rewrite_tac o single o GSYM)
   \\ pop_assum (assume_tac o (SIMP_RULE std_ss [Once res_sim_cases]))
   \\ fs[])
  \\ rpt strip_tac
  \\ last_x_assum (fs o single o GSYM)
  \\ drule (List.nth (CONJ_LIST 5 res_sim_rules, 3))
  \\ disch_then (qspecl_then [‘h’, ‘h’] mp_tac) \\ fs[]
QED

Definition is_stos_pass_with_plans_correct_def :
  is_stos_pass_with_plans_correct plans (st1:'a semanticPrimitives$state) st2 env cfg exps r1 =
    (evaluate st1 env
             (MAP FST (stos_pass_with_plans cfg plans exps)) = (st2, Rval r1) /\
     (* (∀ (st1:'a semanticPrimitives$state) st2.freeVars_list_arithExp_bound st1 st2 exps env) ∧ *)
     (cfg.canOpt <=> st1.fp_state.canOpt = FPScope Opt) /\
     (st1.fp_state.canOpt <> Strict) /\
     (~ st1.fp_state.real_sem) ==>
     let theRws = FLAT (MAP (λ stp. case stp of |Apply (pth, rws) => rws | _ => []) (FLAT plans)) in
    ? fpOpt choices fpOptR choicesR r2.
      (evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ theRws; opts := fpOpt; choices := choices |>) env exps =
      (st2 with fp_state := st2.fp_state with
       <| rws := st2.fp_state.rws ++ theRws; opts := fpOptR; choices := choicesR |>, Rval r2)) /\
      res_sim (Rval r1) (Rval r2) cfg st1)
End

Theorem res_sim_swap:
  (! vs1 vs2 cfg (st1:'a semanticPrimitives$state).
  res_sim vs1 vs2 cfg st1 ==>
  ! (st2:'a semanticPrimitives$state).
  st1.fp_state.rws = st2.fp_state.rws /\
  (st1.fp_state.canOpt = FPScope Opt <=> st2.fp_state.canOpt = FPScope Opt) /\
  (st1.fp_state.canOpt <> Strict) /\
  (~ st1.fp_state.real_sem) ==>
  res_sim vs1 vs2 cfg st2)
  /\
  (! vs1 vs2 cfg (st1:'a semanticPrimitives$state).
  v_list_sim vs1 vs2 cfg st1 ==>
  ! (st2:'a semanticPrimitives$state).
  st1.fp_state.rws = st2.fp_state.rws /\
  (st1.fp_state.canOpt = FPScope Opt <=> st2.fp_state.canOpt = FPScope Opt) /\
  (st1.fp_state.canOpt <> Strict) /\
  (~ st1.fp_state.real_sem) ==>
  v_list_sim vs1 vs2 cfg st2)
Proof
  ho_match_mp_tac res_sim_ind \\ rpt conj_tac \\ rpt strip_tac
  \\ simp[Once res_sim_cases]
  \\ DISJ2_TAC \\ qexists_tac ‘plan’ \\ fs[]
  \\ qmatch_goalsub_abbrev_tac ‘FLAT (MAP getRws_from_plan plan)’
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [‘st’, ‘r1’, ‘st2'’] mp_tac)
  \\ impl_tac \\ fs[]
  \\ strip_tac \\ rveq \\ qexistsl_tac [‘fpOpt’, ‘choices’]
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem res_sim_refl:
  res_sim (Rval vs1) (Rval vs1) cfg st
Proof
  irule (CONJUNCT1 (CONJUNCT2 res_sim_rules))
  \\ Induct_on ‘vs1’ \\ fs[res_sim_rules]
QED

Theorem MAP_FST_Success:
  MAP FST (MAP (λ e. (e, Success)) exps) = exps
Proof
  Induct_on ‘exps’ \\ fs[]
QED

val simple_case_tac =
  ntac 4 (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac
  \\ rveq \\ fs[MAP_FST_Success]
  \\ qexistsl_tac [‘st1.fp_state.opts’, ‘st1.fp_state.choices’]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1New _ _’
  \\ ‘st1New = st1’ by (unabbrev_all_tac \\ fs[semState_comp_eq, fpState_component_equality])
  \\ rveq \\ simp[Once evaluate_cons]
  \\ fs[semState_comp_eq, fpState_component_equality, res_sim_refl];

Theorem stos_pass_with_plans_correct_empty:
  ! exps (st1:'a semanticPrimitives$state) st2 env cfg r.
   is_stos_pass_with_plans_correct [] st1 st2 env cfg exps r
Proof
  Cases_on ‘exps’ \\ rpt strip_tac
  \\ fs[is_stos_pass_with_plans_correct_def, stos_pass_with_plans_def]
  >- (
  rpt strip_tac \\ fs[] \\ rveq
  \\ fs[res_sim_rules, semState_comp_eq, fpState_component_equality])
  \\ Cases_on ‘h’ \\ fs[stos_pass_with_plans_def, Once evaluate_cons]
  \\ simple_case_tac
QED

Theorem stos_pass_with_plans_sing_exists:
  ∃ e_opt res. stos_pass_with_plans cfg [h][e] = [(e_opt, res)]
Proof
  measureInduct_on ‘exp_size e’\\ Cases_on ‘e’ \\ fs[stos_pass_with_plans_def]
  \\ TRY (qmatch_goalsub_abbrev_tac ‘optimise_with_plan _ _ (eOld)’
          \\ Cases_on ‘optimise_with_plan cfg h eOld’ \\ fs[])
  \\ first_x_assum (qspec_then ‘e'’ mp_tac) \\ fs[astTheory.exp_size_def]
  \\ strip_tac \\ fs[]
QED

Theorem MAP_FST_Fun:
  MAP FST ((λ (e_opt, res). [(Fun s e_opt, res)])(HD (stos_pass_with_plans cfg [h][e]))) =
  [Fun s (FST (HD (stos_pass_with_plans cfg [h][e])))]
Proof
  qspec_then ‘e’ assume_tac (GEN “e:ast$exp”stos_pass_with_plans_sing_exists)
  \\ fs[]
QED

(*
val solve_tac =
  qpat_assum `evaluate _ _ [FST (optimise_with_plan _ _ _)] = _`
       (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
  \\ impl_tac \\ fs[Once freeVars_arithExp_bound_def]
  \\ TRY(fs[Once freeVars_arithExp_bound_def] \\ NO_TAC)
  \\ strip_tac \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_fp_rws_append))
  \\ disch_then (qspec_then ‘FLAT_plans’ assume_tac)
  \\ first_x_assum (qspec_then ‘LENGTH t + exp6_size t'’ mp_tac)
  \\ impl_tac >- fs[astTheory.exp_size_def]
  \\ disch_then (qspec_then ‘(t',t)’ mp_tac) \\ impl_tac >- fs[]
  \\ rewrite_tac[is_stos_pass_with_plans_correct_def]
  \\ disch_then (fn ith => last_assum (mp_then Any mp_tac ith))
  \\ impl_tac \\ fs[]
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ strip_tac \\ pop_assum mp_tac
  \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 (prep evaluate_fp_rws_up)))
  \\ disch_then (qspec_then ‘q.fp_state.rws ++ FLAT_h ++ FLAT_plans’ mp_tac) \\ impl_tac
  >- (fs [SUBSET_DEF] \\ metis_tac[])
  \\ strip_tac \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ disch_then (qspec_then ‘choicesR’ assume_tac)
  \\ first_x_assum (qspec_then ‘fpOpt'’ assume_tac)
  \\ strip_tac \\ fs[]
  \\ simp[Once evaluate_cons]
  \\ qexistsl_tac [‘fpOpt''’, ‘choices’] \\ fs[]
  \\ fs[semState_comp_eq, fpState_component_equality] \\ conj_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[Once res_sim_cases] \\ fs[v_list_sim_append]
  \\ irule (CONJUNCT2 res_sim_swap)
  \\ qexists_tac ‘q’ \\ fs[] \\ imp_res_tac evaluate_fp_opts_inv \\ fs[];

Theorem stos_pass_with_plans_correct_aux:
  ∀ p.
    (∀ plan.
    MEM plan (SND p) ⇒
      ∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
         is_optimise_with_plan_correct plan st1 st2 env cfg exps r) ⇒
  ∀ (st1:'a semanticPrimitives$state) st2 env cfg r.
   is_stos_pass_with_plans_correct (SND p) st1 st2 env cfg (FST p) r
Proof
  completeInduct_on ‘(exp6_size (FST p) + LENGTH (SND (p:exp list # opt_step list list)))’
  \\ strip_tac \\ strip_tac \\ rveq \\ Cases_on ‘p’
  \\ rename1 ‘SND (exps, plans)’ \\ Cases_on ‘plans’
  \\ fs[stos_pass_with_plans_correct_empty]
  \\ rpt strip_tac \\ Cases_on ‘exps’
  \\ simp[is_stos_pass_with_plans_correct_def, stos_pass_with_plans_def,
          res_sim_rules, semState_comp_eq, fpState_component_equality,
          Once stos_pass_with_plans_cons, Once evaluate_append]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ first_assum (qspec_then ‘h’ mp_tac) \\ impl_tac
  \\ rewrite_tac[is_optimise_with_plan_correct_def]
  \\ disch_then (qspec_then ‘[h']’ assume_tac)
  \\ Cases_on ‘h'’ \\ fs[stos_pass_with_plans_def]
  \\ qmatch_goalsub_abbrev_tac ‘st1.fp_state with <|
                                  rws := st1.fp_state.rws ++ FLAT_h ++ FLAT_plans;
                                  opts := _; choices := _ |>’
  >~ [‘Fun s e’]
  >- (
  fs[MAP_FST_Fun]
  \\ qpat_x_assum ‘evaluate _ _ [Fun _ _] = _’ mp_tac
  \\ simp[Once evaluate_def] \\ rpt strip_tac \\ rveq
  \\ simp[Once evaluate_cons, evaluate_def]
  \\ first_assum (qspec_then ‘LENGTH t + exp6_size t'’ mp_tac) \\ impl_tac
  >- (fs[astTheory.exp_size_def])
  \\ disch_then (qspec_then ‘(t',t)’ mp_tac) \\ simp[]
  \\ rewrite_tac[is_stos_pass_with_plans_correct_def]
  \\ disch_then (fn ith => last_assum (mp_then Any mp_tac ith))
  \\ impl_tac \\ fs[]
  >- (rpt strip_tac \\ fs[freeVars_arithExp_bound_def])
  \\ strip_tac \\ pop_assum mp_tac
  \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 (prep evaluate_fp_rws_up)))
  \\ disch_then (qspec_then ‘q.fp_state.rws ++ FLAT_h ++ FLAT_plans’ mp_tac) \\ impl_tac
  >- (fs [SUBSET_DEF] \\ metis_tac[])
  \\ rpt strip_tac
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ qexistsl_tac[‘fpOpt'’, ‘choices’]
  \\ fs[semState_comp_eq, fpState_component_equality] \\ conj_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ ntac 2 (simp [Once res_sim_cases])
  \\ DISJ2_TAC
  \\ qexists_tac ‘h’ \\ rpt conj_tac >- fs[]
  >- (pop_assum mp_tac \\ simp[Once res_sim_cases])
  \\ rpt strip_tac
  \\ last_x_assum (qspec_then ‘LENGTH [h] + exp6_size [e]’ mp_tac) \\ impl_tac
  >- (fs[astTheory.exp_size_def])
  \\ disch_then (qspec_then ‘([e], [h])’ mp_tac) \\ impl_tac >- fs[]
  \\ impl_tac
  >- (last_x_assum (qspec_then ‘h’ mp_tac) \\ fs[])
  \\ rewrite_tac [is_stos_pass_with_plans_correct_def]
  \\ rpt (disch_then (fn ith => first_assum $ mp_then Any mp_tac ith))
  \\ impl_tac \\ fs[freeVars_arithExp_bound_def]
  \\ strip_tac \\ qexistsl_tac [‘fpOpt’, ‘choices'’]
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ fs[Once res_sim_cases]
  \\ irule (CONJUNCT2 res_sim_swap)
  \\ qexists_tac ‘st’ \\ fs[] \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
  >- solve_tac
  >- solve_tac
  >- (
    qpat_assum `evaluate _ _ [FST (optimise_with_plan _ _ _)] = _`
      (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ impl_tac \\ fs[freeVars_arithExp_bound_def])
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
  >- solve_tac
QED

Theorem stos_pass_with_plans_correct:
  ∀ plans.
    (∀ plan.
    MEM plan plans ⇒
      ∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
         is_optimise_with_plan_correct plan st1 st2 env cfg exps r) ⇒
  ∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
   is_stos_pass_with_plans_correct plans st1 st2 env cfg exps r
Proof
  rpt strip_tac
  \\ qspec_then ‘(exps, plans)’ assume_tac stos_pass_with_plans_correct_aux
  \\ fs[]
QED
*)

(* Lemmas needed to automate proof generation *)
Theorem is_perform_rewrites_correct_empty_plan:
  ! rws path.
    MEM (Apply (path, rws)) [] ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_perform_rewrites_correct_cons:
  ! rwsNew pathNew plan.
  (! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rwsNew st1 st2 env cfg e r pathNew) ==>
  (! rws path.
     MEM (Apply (path, rws)) plan ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path) ==>
  (! rws path.
     MEM (Apply (path, rws)) (Apply (pathNew, rwsNew)::plan) ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_perform_rewrites_correct_label:
  ! s plan.
  (! rws path.
     MEM (Apply (path, rws)) plan ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path) ==>
  (! rws path.
     MEM (Apply (path, rws)) (Label s::plan) ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_perform_rewrites_correct_expected:
  ! e plan.
  (! rws path.
     MEM (Apply (path, rws)) plan ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path) ==>
  (! rws path.
     MEM (Apply (path, rws)) (Expected e::plan) ==>
    ! (st1:'a semanticPrimitives$state) st2 env cfg e r.
      is_perform_rewrites_correct rws st1 st2 env cfg e r path)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem is_optimise_with_plan_correct_sing:
  ! sing_plan.
    (! (st1:'a semanticPrimitives$state) st2 env cfg exps r.
    is_optimise_with_plan_correct sing_plan st1 st2 env cfg exps r) ==>
    (! plan.
       MEM plan [sing_plan] ==>
       ! exps (st1:'a semanticPrimitives$state) st2 env cfg r.
       is_optimise_with_plan_correct plan st1 st2 env cfg exps r)
Proof
  rpt strip_tac \\ fs[]
QED

val _ = export_theory ();
