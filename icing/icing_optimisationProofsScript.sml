(*
  Correctness proofs for Icing optimisations supported by CakeML
*)
open bossLib;
open semanticPrimitivesTheory evaluatePropsTheory;
open fpValTreeTheory fpSemPropsTheory fpOptTheory fpOptPropsTheory icing_optimisationsTheory
     icing_rewriterTheory source_to_sourceProofsTheory terminationTheory;

open preamble;

val _ = new_theory "icing_optimisationProofs";

Theorem fp_comm_gen_cases:
  !e fpBop.
    (? e1 e2.
      e = (App (FP_bop fpBop) [e1; e2]) /\
      isPureExp e /\
      rewriteFPexp [fp_comm_gen fpBop] (App (FP_bop fpBop) [e1; e2]) =
        App (FP_bop fpBop) [e2; e1]) \/
    (rewriteFPexp [fp_comm_gen fpBop] e = e)
Proof
  rpt gen_tac \\ Cases_on `e`
  \\ fs[fp_comm_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[isPureOp_def]
  \\ Cases_on ‘isPureExpList els’ \\ fs[]
  \\ Cases_on ‘els’ \\ fs[]
  \\ Cases_on ‘t’ \\ fs[]
  \\ Cases_on ‘t'’ \\ fs[]
  \\ Cases_on `fpBop = f` \\ fs[isPureExp_def] \\ EVAL_TAC
QED

local
  val fp_rws_append_comm =
    SIMP_RULE std_ss [] evaluate_fp_rws_append
    |> CONJ_LIST 2
    |> map (SPEC_ALL) |> map (GEN ``(opts:(fp_pat #fp_pat) list)``)
    |> map (Q.SPEC `[fp_comm_gen fpBop]`) |> map GEN_ALL
    |> LIST_CONJ;
  val eval_fp_opt_inv =
    SIMP_RULE std_ss [] fpSemPropsTheory.evaluate_fp_opts_inv
    |> CONJ_LIST 2 |> hd;
  val isPureExp_ignores_state =
    EVAL_RULE isPureExpList_swap_ffi
    |> CONJ_LIST 2
    |> hd
in
Theorem fp_comm_gen_correct:
  ! fpBop (st1 st2:'a semanticPrimitives$state) env e res.
  is_rewriteFPexp_correct [fp_comm_gen fpBop] st1 st2 env e (Rval res)
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspecl_then [`e`, `fpBop`] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_comm_gen_cases)
  \\ fs[]
  >- (
    pop_assum (fn thm => fs[thm])
    \\ imp_res_tac fp_rws_append_comm
    \\ first_x_assum (qspecl_then [`g`, `fpBop`] assume_tac) \\ fs[]
    \\ first_x_assum (mp_then Any (qspec_then `g` assume_tac) (CONJUNCT1 optUntil_evaluate_ok))
    \\ fs[fpState_component_equality]
    \\ asm_exists_tac \\ fs[])
  \\ fs[evaluate_def] \\ rveq
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ rename [`evaluate st1 env [e1]`]
  \\ Cases_on `evaluate st1 env [e1]` \\ fs[]
  \\ rename [`evaluate st1 env [e1] = (st2, r)`]
  \\ Cases_on `r` \\ fs[]
  \\ rename [`evaluate st1 env [e1] = (st2, Rval r)`]
  \\ rename [`evaluate st2 env [e2]`]
  \\ Cases_on `evaluate st2 env [e2]` \\ fs[]
  \\ rename [`evaluate st2 env [e2] = (st3, r)`] \\ Cases_on `r` \\ fs[]
  \\ rename [`evaluate st2 env [e2] = (st3, Rval r)`]
  \\ fs[astTheory.getOpClass_def, astTheory.isFpBool_def]
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ `st3.fp_state.canOpt = FPScope Opt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ `st2 = st1 with fp_state := st2.fp_state /\ st3 = st1 with fp_state := st3.fp_state`
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[shift_fp_opts_def]
  \\ rename [`evaluate st1 env [e1] = (st2, Rval [r1])`, `evaluate st2 env [e2] = (st3, Rval [r2])`]
  \\ Cases_on `do_app (st3.refs, st3.ffi) (FP_bop fpBop) [r2; r1]` \\ fs[]
  \\ PairCases_on `x` \\ fs[]
  \\ imp_res_tac do_app_fp_inv \\ rveq \\ fs[]
  \\ rpt strip_tac \\ rveq
  \\ ntac 2 (first_x_assum (fn thm => (mp_then Any assume_tac isPureExp_evaluate_change_oracle thm) \\ mp_tac thm))
  \\ rpt (disch_then assume_tac)
  \\ first_x_assum
      (qspecl_then
        [`fp_comm_gen fpBop`,
         `st1 with fp_state := st2.fp_state with choices := st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices)`,
         `\x. if (x = 0)
              then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
                (case do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2))) (st3.fp_state.opts x) st3.fp_state.rws of | NONE => [] | SOME r_opt => st3.fp_state.opts x)
              else g (x - 1)`]
      impl_subgoal_tac)
  >- (fs[isPureExp_def]
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ first_x_assum (qspecl_then [`fp_comm_gen fpBop`, `st1`, `oracle`] impl_subgoal_tac)
  >- (fs[isPureExp_def]
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ `st1.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ qexists_tac `oracle'` \\ fs[]
  \\ `st1 with fp_state  := st2.fp_state with
        <| rws := st2.fp_state.rws ++ [fp_comm_gen fpBop];
           opts := oracle;
           choices := st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices) |> =
      st1 with fp_state := st1.fp_state with
        <| rws := st2.fp_state.rws ++ [fp_comm_gen fpBop];
           opts := oracle;
           choices := st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices) |>`
    by (fs[fpState_component_equality, state_component_equality]
        \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
        \\ simp[FUN_EQ_THM])
  \\ pop_assum (fs o single)
  \\ `st2.fp_state.canOpt = FPScope Opt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ imp_res_tac isPureOp_same_ffi \\ fs[isPureOp_def]
  \\ first_x_assum (qspecl_then [`st1.refs`, `st1.ffi`] assume_tac)
  \\ fs[do_app_def, shift_fp_opts_def, fpState_component_equality]
  \\ qexists_tac `\x. g x`
  \\ rpt conj_tac
  >- (imp_res_tac evaluate_fp_opts_inv
      \\ fs[fpState_component_equality, state_component_equality, FUN_EQ_THM])
  \\ fs[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ fs[EVAL ``rwFp_pathWordTree (fp_comm_gen fpBop) Here (fp_bop fpBop w2 w1)``,
        instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws (fp_bop fpBop w1 w2)` \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_comm_gen fpBop]` assume_tac)
  \\ `st3.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
QED
end

Theorem fp_assoc_gen_cases:
  !e fpBop.
    (? e1 e2 e3.
      e = (App (FP_bop fpBop) [App (FP_bop fpBop) [e1; e2]; e3]) /\
      isPureExp e /\
      rewriteFPexp [fp_assoc_gen fpBop] (App (FP_bop fpBop) [App (FP_bop fpBop) [e1; e2]; e3]) =
      App (FP_bop fpBop) [e1; (App (FP_bop fpBop) [e2; e3])]) \/
    (rewriteFPexp [fp_assoc_gen fpBop] e = e)
Proof
  rpt gen_tac \\ Cases_on `e`
  \\ fs[fp_assoc_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[isPureOp_def]
  \\ Cases_on ‘els’ \\ fs[]
  \\ Cases_on ‘t’ \\ fs[]
  \\ Cases_on ‘t'’ \\ fs[]
  \\ Cases_on ‘fpBop = f’ \\ fs[]
  \\ Cases_on ‘isPureExpList [h;h']’ \\ fs[isPureExp_def]
  \\ Cases_on ‘h’ \\ fs[]
  \\ Cases_on ‘o'’ \\ fs[]
  \\ Cases_on ‘l’ \\ fs[]
  \\ Cases_on ‘t’ \\ fs[]
  \\ Cases_on ‘t'’ \\ fs[]
  \\ fs[isPureExp_def]
  \\ Cases_on ‘f = f'’ \\ fs[] \\ rveq
  \\ EVAL_TAC
QED

val state_eqs = [state_component_equality, fpState_component_equality];

val fp_inv_tac = imp_res_tac evaluate_fp_opts_inv \\ fs[];

Theorem evaluate_append_rws:
  ∀ opts st1 env es st2 r.
  evaluate st1 env es = (st2, r) ⇒
  ∃ fpOpt fpOptR.
    evaluate
    (st1 with fp_state := st1.fp_state with <|rws := st1.fp_state.rws ++ opts; opts := fpOpt |>)
    env es =
    (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ opts; opts := fpOptR |>, r)
Proof
  rpt strip_tac
  \\ imp_res_tac (SIMP_RULE std_ss [] evaluate_fp_rws_up)
  \\ first_x_assum (qspec_then ‘st1.fp_state.rws ++ opts’ mp_tac)
  \\ impl_tac \\ fs[]
  \\ strip_tac \\ qexists_tac ‘fpOpt’
  \\ fs state_eqs
  \\ fp_inv_tac
QED

(*
fun extend_eval_tac t rws =
  qpat_assum t (mp_then Any (fn thm => Q.SPEC_THEN rws mp_tac thm) evaluate_append_rws);

fun optUntil_tac t1 t2 =
  qpat_x_assum t1 (mp_then Any mp_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ disch_then (qspec_then t2 assume_tac) \\ fs[];

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

Theorem fp_assoc_gen_correct:
  ∀ fpBop st1 st2 env e r.
    is_rewriteFPexp_correct [fp_assoc_gen fpBop] st1 st2 env e r
Proof
  simp[is_rewriteFPexp_correct_def] \\ rpt strip_tac
  \\ qspecl_then [‘e’, ‘fpBop’] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_assoc_gen_cases)
  \\ fs[]
  >- (
   pop_assum (fs o single)
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_assoc_gen fpBop]’
   \\ strip_tac \\ qexists_tac ‘fpOpt’ \\ fs state_eqs
   \\ fp_inv_tac)
  \\ rveq \\ pop_assum (fs o single)
  \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by fp_inv_tac
  \\ qpat_x_assum ‘evaluate st1 _ _ = _’
                  (fn thm => mp_tac (SIMP_RULE std_ss [evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def] thm))
  \\ fs[Once evaluate_cons]
  \\ simp[GEN_ALL evaluate_case_case]
  \\ disch_then (fn thm => mp_tac (SIMP_RULE std_ss [evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def] thm))
  \\ fs[Once evaluate_cons, GEN_ALL evaluate_case_case]
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ extend_eval_tac ‘evaluate st1 env [e3] = _’ ‘[fp_assoc_gen fpBop]’
  \\ strip_tac
  >- (
   rpt strip_tac \\ rveq
   \\ qexists_tac ‘fpOpt’
   \\ rfs ([evaluate_def, GEN_ALL evaluate_case_case] @ state_eqs))
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ extend_eval_tac ‘evaluate _ env [e2] = _’ ‘[fp_assoc_gen fpBop]’
  \\ strip_tac
  >- (
   rpt strip_tac \\ rveq
   \\ optUntil_tac ‘evaluate _ env [e3] = _’ ‘fpOpt'’
   \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
   \\ rfs ([evaluate_def, GEN_ALL evaluate_case_case] @ state_eqs)
   \\ ‘q'.fp_state.rws = q.fp_state.rws’ by fp_inv_tac
   \\ pop_assum (fs o single) \\ fs state_eqs)
  \\ imp_res_tac evaluate_sing \\ fs[] \\ rveq
  \\ optUntil_tac ‘evaluate _ env [e3] = _’ ‘fpOpt'’
  \\ simp[do_app_def]
  \\ Cases_on ‘fp_translate v’ \\ Cases_on ‘fp_translate v'’ \\ fs[]
  \\ TRY (
     rpt strip_tac
     \\ rveq \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
     \\ rfs ([evaluate_def, GEN_ALL evaluate_case_case] @ state_eqs)
     \\ ‘q'.fp_state.rws = q.fp_state.rws’ by fp_inv_tac
     \\ pop_assum (fs o single) \\ fs state_eqs
     \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])


  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ extend_eval_tac ‘evaluate _ env [e1] = _’ ‘[fp_assoc_gen fpBop]’
*)

val _ = export_theory ();
