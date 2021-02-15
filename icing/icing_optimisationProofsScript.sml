(*
  Correctness proofs for Icing optimisations supported by CakeML
  Each optimisation is defined in icing_optimisationsScript.
  This file proves the low-level correctness theorems for a single
  application of the optimisation, as well as that optimisations
  are real-valued identities.
  The overall correctness proof for a particular run of the optimiser
  from source_to_sourceScript is build using the automation in
  icing_optimisationsLib and the general theorems from
  source_to_sourceProofsScript.
*)
open bossLib ml_translatorLib;
open semanticPrimitivesTheory evaluatePropsTheory;
open fpValTreeTheory fpSemPropsTheory fpOptTheory fpOptPropsTheory
     icing_optimisationsTheory icing_rewriterTheory source_to_sourceProofsTheory
     floatToRealTheory floatToRealProofsTheory
     pureExpsTheory terminationTheory binary_ieeeTheory;

val _ = temp_delsimps ["lift_disj_eq", "lift_imp_disj"]

open preamble;

val _ = new_theory "icing_optimisationProofs";

val state_eqs = [state_component_equality, fpState_component_equality];

(** Automatically prove trivial goals about fp oracle **)
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

(** Extend evaluate statement t with rewrites in rws **)
fun extend_eval_tac t rws =
  qpat_assum t (mp_then Any (fn thm => Q.SPEC_THEN rws mp_tac thm)
                evaluate_append_rws);

(** replace the fp oracle choice function in t1 with such that it ends with the
    oracle t2 **)
fun optUntil_tac t1 t2 =
  qpat_x_assum t1 (mp_then Any mp_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ disch_then (qspec_then t2 assume_tac) \\ fs[];

(** Automatically proves the cases theorem for rewrite r **)
fun prove_cases_thm r =
  rpt gen_tac \\ simp[r, DefnBase.one_line_ify NONE rewriteFPexp_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ fs[matchesFPexp_def, appFPexp_def,
        CaseEq"option", CaseEq"exp", CaseEq "op",CaseEq "list"]
  \\ rpt strip_tac
  \\ rveq \\ fs[] \\ rpt (pop_assum mp_tac)
  \\ EVAL_TAC \\ fs[];

(** Automatically proves the cases theorem for rewrite r that is defined as the reverse of rewrite r_rev **)
fun prove_cases_reverse_thm r r_rev =
  fs[r, reverse_tuple_def, r_rev]
  \\ prove_cases_thm r

Theorem rwAllWordTree_comp_left:
  ! b v1 v2 vres insts rws.
    rwAllWordTree insts rws v1 = SOME vres ==>
    rwAllWordTree (MAP (λ inst. case inst of |RewriteApp p id => RewriteApp (Left p) id) insts) rws (Fp_bop b v1 v2) =
        SOME (Fp_bop b vres v2)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v2`, `b`] assume_tac)
  \\ fs[]
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
QED

Theorem rwAllWordTree_comp_right:
  ! b v1 v2 vres insts rws.
    rwAllWordTree insts rws v2 = SOME vres ==>
    rwAllWordTree (MAP (λ inst. case inst of |RewriteApp p id => RewriteApp (Right p) id) insts) rws (Fp_bop b v1 v2) =
        SOME (Fp_bop b v1 vres)
Proof
  Induct_on `insts` \\ rpt strip_tac
  \\ fs[rwAllWordTree_def]
  \\ Cases_on `h` \\ fs[rwAllWordTree_def, option_case_eq]
  \\ res_tac
  \\ first_x_assum (qspecl_then [`v1`, `b`] assume_tac)
  \\ fs[]
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, maybe_map_def]
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

(**
  Case theorems for application of each rewrite
  They allow to do a case-distinction on whether the rewrite fired or not in the
  simulation proofs, thus reducing a case split over the AST of the expression
  to a case split of whether the rewrite fired or not
**)

Theorem fp_comm_gen_cases:
  !e fpBop.
    (? e1 e2.
      e = (App (FP_bop fpBop) [e1; e2]) /\
      isPureExp e /\
      rewriteFPexp [fp_comm_gen fpBop] (App (FP_bop fpBop) [e1; e2]) =
        App (FP_bop fpBop) [e2; e1]) \/
    (rewriteFPexp [fp_comm_gen fpBop] e = e)
Proof
  prove_cases_thm fp_comm_gen_def
QED

Theorem fp_assoc_gen_cases:
  !e fpBop.
    (? e1 e2 e3.
      e = (App (FP_bop fpBop) [App (FP_bop fpBop) [e1; e2]; e3]) /\
      isPureExp e /\
      rewriteFPexp [fp_assoc_gen fpBop] (App (FP_bop fpBop) [App (FP_bop fpBop) [e1; e2]; e3]) =
      App (FP_bop fpBop) [e1; (App (FP_bop fpBop) [e2; e3])]) \/
    (rewriteFPexp [fp_assoc_gen fpBop] e = e)
Proof
  prove_cases_thm fp_assoc_gen_def
QED

Theorem fp_assoc2_gen_cases:
  ∀ e fpBop.
    (∃ e1 e2 e3.
       e = (App (FP_bop fpBop) [e1; (App (FP_bop fpBop) [e2; e3])]) ∧
       isPureExp e ∧
       rewriteFPexp [fp_assoc2_gen fpBop] (App (FP_bop fpBop) [e1; (App (FP_bop fpBop) [e2; e3])]) =
       (App (FP_bop fpBop) [App (FP_bop fpBop) [e1; e2]; e3])) ∨
    (rewriteFPexp [fp_assoc2_gen fpBop] e = e)
Proof
  rpt gen_tac \\ Cases_on `e`
  \\ fs[fp_assoc2_gen_def, reverse_tuple_def, fp_assoc_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[isPureOp_def]
  \\ Cases_on ‘isPureExpList els ∧
      isFpArithPat (Binop fpBop (Var 0) (Binop fpBop (Var 1) (Var 2))) ∧
      isFpArithPat (Binop fpBop (Binop fpBop (Var 0) (Var 1)) (Var 2)) ∧
      isFpArithExp (App (FP_bop f) els)’ \\ fs[]
  \\ Cases_on ‘els’ \\ fs[]
  \\ Cases_on ‘t’ \\ fs[]
  \\ Cases_on ‘t'’ \\ fs[]
  \\ Cases_on ‘fpBop = f’ \\ fs[]
  \\ Cases_on ‘isPureExpList [h;h']’ \\ fs[isPureExp_def]
  \\ fs[substLookup_def]
  \\ Cases_on ‘h'’ \\ fs[]
  \\ Cases_on ‘o'’ \\ fs[]
  \\ Cases_on ‘l’ \\ fs[]
  \\ Cases_on ‘t’ \\ fs[]
  \\ Cases_on ‘t'’ \\ fs[]
  \\ fs[isPureExp_def]
  \\ Cases_on ‘f = f'’ \\ fs[] \\ rveq
  \\ EVAL_TAC
QED

Theorem fp_fma_intro_cases:
  ∀ e.
    (∃ e1 e2 e3.
      e = (App (FP_bop FP_Add) [App (FP_bop FP_Mul) [e1; e2]; e3]) ∧
      isPureExp e ∧
      rewriteFPexp [fp_fma_intro] (App (FP_bop FP_Add) [App (FP_bop FP_Mul) [e1; e2]; e3]) =
      App (FP_top FP_Fma) [e3;e1;e2]) ∨
    (rewriteFPexp [fp_fma_intro] e = e)
Proof
  prove_cases_thm fp_fma_intro_def
QED

Theorem fp_sub_add_cases:
  ∀ e.
    (∃ e1 e2.
      e = (App (FP_bop FP_Sub) [e1; e2]) ∧
      isPureExp e ∧
      rewriteFPexp [fp_sub_add] (App (FP_bop FP_Sub) [e1; e2])  =
        App (FP_bop FP_Add) [e1; App (FP_uop FP_Neg) [e2]]) ∨
    (rewriteFPexp [fp_sub_add] e = e)
Proof
  prove_cases_thm fp_sub_add_def
QED

Theorem fp_add_sub_cases:
∀ e.
    (∃ e1 e2.
      e = App (FP_bop FP_Add) [e1; App (FP_uop FP_Neg) [e2]] ∧
      isPureExp e ∧
      rewriteFPexp [fp_add_sub] (App (FP_bop FP_Add) [e1; App (FP_uop FP_Neg) [e2]])  =
        App (FP_bop FP_Sub) [e1; e2]) ∨
    (rewriteFPexp [fp_add_sub] e = e)
Proof
  prove_cases_reverse_thm fp_add_sub_def fp_sub_add_def
QED

Theorem fp_neg_push_mul_r_cases:
  ∀ e.
    (∃ e1 e2 e3.
      e = (App (FP_bop FP_Add) [App (FP_uop FP_Neg) [App (FP_bop FP_Mul) [e1; e2]]; e3]) ∧
      isPureExp e ∧
      rewriteFPexp [fp_neg_push_mul_r]
        (App (FP_bop FP_Add) [App (FP_uop FP_Neg) [App (FP_bop FP_Mul) [e1; e2]]; e3]) =
        (App (FP_bop FP_Add) [App (FP_bop FP_Mul) [e1; App (FP_uop FP_Neg) [e2]]; e3])) ∨
    (rewriteFPexp [fp_neg_push_mul_r] e = e)
Proof
  prove_cases_thm fp_neg_push_mul_r_def
QED

Theorem fp_times_zero_cases:
  ∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 0w)]]) ∧
      isPureExp (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 0w)]]) ∧
      isFpArithExp e ∧
      rewriteFPexp [fp_times_zero] e =
        (App FpFromWord [Lit (Word64 0w)])) ∨
    (rewriteFPexp [fp_times_zero] e = e)
Proof
  prove_cases_thm fp_times_zero_def
  \\ rpt strip_tac
  \\ fs[CaseEq"option", CaseEq"prod", CaseEq"list", CaseEq"lit"]
  \\ fs[NULL_EQ]
QED

Theorem fp_times_one_cases:
  ∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 4607182418800017408w)]]) ∧
      isPureExp (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 4607182418800017408w)]]) ∧
      isFpArithExp e ∧
      rewriteFPexp [fp_times_one] e = e1) ∨
    (rewriteFPexp [fp_times_one] e = e)
Proof
  prove_cases_thm fp_times_one_def
  \\ rpt strip_tac
  \\ fs[CaseEq"option", CaseEq"prod", CaseEq"list", CaseEq"lit"]
  \\ fs[NULL_EQ]
  \\ fs[substAdd_def, substUpdate_def] \\ rveq
  \\ fs[substLookup_def]
QED

Theorem fp_times_one_reverse_cases:
  ∀ e.
    (∃ e1.
      e = e1 ∧
      isPureExp e ∧
      isFpArithExp e ∧
      rewriteFPexp [fp_times_one_reverse] e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 4607182418800017408w)]])) ∨
    (rewriteFPexp [fp_times_one_reverse] e = e)
Proof
  prove_cases_reverse_thm fp_times_one_reverse_def fp_times_one_def
QED

Theorem fp_times_minus_one_neg_cases:
  ∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]]) ∧
      isPureExp (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]]) ∧
      rewriteFPexp [fp_times_minus_one_neg] e = App (FP_uop FP_Neg) [e1]) ∨
    (rewriteFPexp [fp_times_minus_one_neg] e = e)
Proof
  prove_cases_thm fp_times_minus_one_neg_def
  \\ rpt strip_tac
  \\ fs[CaseEq"option", CaseEq"prod", CaseEq"list", CaseEq"lit"]
  \\ fs[NULL_EQ]
  \\ fs[substAdd_def, substUpdate_def] \\ rveq
  \\ fs[substLookup_def]
QED

Theorem fp_neg_times_minus_one_cases:
  ∀ e.
    (∃ e1.
      e = App (FP_uop FP_Neg) [e1] ∧
      isPureExp (App (FP_uop FP_Neg) [e1]) ∧
      rewriteFPexp [fp_neg_times_minus_one] e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]])) ∨
    (rewriteFPexp [fp_neg_times_minus_one] e = e)
Proof
  prove_cases_reverse_thm fp_neg_times_minus_one_def fp_times_minus_one_neg_def
QED

Theorem fp_times_two_to_add_cases:
  ∀ e.
    (∃ e1 e2.
       e = App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 4611686018427387904w)]] ∧
       isPureExp e ∧
       rewriteFPexp [fp_times_two_to_add] e  =
       App (FP_bop FP_Add) [e1; e1]) ∨
    (rewriteFPexp [fp_times_two_to_add] e = e)
Proof
  prove_cases_thm fp_times_two_to_add_def
  \\ rpt strip_tac
  \\ fs[CaseEq"option", CaseEq"prod", CaseEq"list", CaseEq"lit"]
  \\ fs[NULL_EQ]
  \\ fs[substAdd_def, substUpdate_def] \\ rveq
  \\ fs[substLookup_def]
QED

Theorem fp_times_three_to_add_cases:
  ∀ e.
    (∃ e1 e2.
       e = App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 4613937818241073152w)]] ∧
       isPureExp e ∧
       rewriteFPexp [fp_times_three_to_add] e  =
       App (FP_bop FP_Add) [App (FP_bop FP_Add) [e1; e1]; e1]) ∨
    (rewriteFPexp [fp_times_three_to_add] e = e)
Proof
  prove_cases_thm fp_times_three_to_add_def
  \\ rpt strip_tac
  \\ fs[CaseEq"option", CaseEq"prod", CaseEq"list", CaseEq"lit"]
  \\ fs[NULL_EQ]
  \\ fs[substAdd_def, substUpdate_def] \\ rveq
  \\ fs[substLookup_def]
QED

Theorem fp_plus_zero_cases:
  ∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Add) [e1; App FpFromWord [Lit (Word64 0w)]]) ∧
      isPureExp e ∧
      rewriteFPexp [fp_plus_zero] e = e1) ∨
    (rewriteFPexp [fp_plus_zero] e = e)
Proof
  prove_cases_thm fp_plus_zero_def
  \\ rpt strip_tac
  \\ fs[CaseEq"option", CaseEq"prod", CaseEq"list", CaseEq"lit"]
  \\ rveq
  \\ fs[NULL_EQ]
  \\ fs[substLookup_def, substAdd_def, substUpdate_def]
QED

Theorem fp_times_into_div_cases:
    ∀ e.
    (∃ e1 e2 e3.
      e = App (FP_bop FP_Mul) [ App (FP_bop FP_Div) [e1; e2]; e3] ∧
      isPureExp e ∧
      rewriteFPexp [fp_times_into_div] e = App (FP_bop FP_Div) [ App (FP_bop FP_Mul) [e1; e3]; e2]) ∨
    (rewriteFPexp [fp_times_into_div] e = e)
Proof
  prove_cases_thm fp_times_into_div_def
QED

Theorem fp_same_sub_cases:
∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Sub) [e1; e1]) ∧
      isPureExp e ∧
      rewriteFPexp [fp_same_sub] e = App FpFromWord [Lit (Word64 0w)]) ∨
    (rewriteFPexp [fp_same_sub] e = e)
Proof
  prove_cases_thm fp_same_sub_def
QED

Theorem fp_same_div_cases:
∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Div) [e1; e1]) ∧
      isPureExp e ∧
      rewriteFPexp [fp_same_div] e = App FpFromWord [Lit (Word64 4607182418800017408w)]) ∨
    (rewriteFPexp [fp_same_div] e = e)
Proof
  prove_cases_thm fp_same_div_def
QED

Theorem fp_distribute_gen_cases:
∀ e fpBopInner fpBopOuter.
    (∃ e1 e2 e3.
      e = App (FP_bop fpBopOuter) [ App (FP_bop fpBopInner) [e1; e2]; App (FP_bop fpBopInner) [e3; e2]] ∧
      isPureExp e ∧
      rewriteFPexp [fp_distribute_gen fpBopInner fpBopOuter] e = App (FP_bop fpBopInner) [ App (FP_bop fpBopOuter) [e1; e3]; e2]) ∨
    (rewriteFPexp [fp_distribute_gen fpBopInner fpBopOuter] e = e)
Proof
  prove_cases_thm fp_distribute_gen_def
QED

Theorem fp_undistribute_gen_cases:
∀ e fpBopInner fpBopOuter.
    (∃ e1 e2 e3.
      e = App (FP_bop fpBopInner) [ App (FP_bop fpBopOuter) [e1; e3]; e2] ∧
      isPureExp e ∧
      rewriteFPexp [fp_undistribute_gen fpBopInner fpBopOuter] e = App (FP_bop fpBopOuter) [ App (FP_bop fpBopInner) [e1; e2]; App (FP_bop fpBopInner) [e3; e2]]) ∨
    (rewriteFPexp [fp_undistribute_gen fpBopInner fpBopOuter] e = e)
Proof
  prove_cases_reverse_thm fp_undistribute_gen_def fp_distribute_gen_def
QED

(** Define some simplified versions of theorems that make it
    easier to prove simulations **)
val eval_fp_opt_inv =
    SIMP_RULE std_ss [] fpSemPropsTheory.evaluate_fp_opts_inv
    |> CONJ_LIST 2 |> hd;
val isPureExp_ignores_state =
    EVAL_RULE isPureExpList_swap_ffi
    |> CONJ_LIST 2
    |> hd;

(** t should be one of the optimisations from icing_optimisationsTheory **)
fun fp_rws_append_opt t =
    SIMP_RULE std_ss [] evaluate_fp_rws_append
    |> CONJ_LIST 2
    |> map (SPEC_ALL) |> map (GEN ``(opts:(fp_pat #fp_pat) list)``)
    |> map (Q.SPEC `[^t]`) |> map GEN_ALL
    |> LIST_CONJ;

Theorem fp_times_one_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_one] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_times_one_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_times_one]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ imp_res_tac evaluate_sing
  \\ pop_assum (fs o single)
  \\ ‘∃ fp. v = FP_WordTree fp’
     by (fs[freeVars_fp_bound_def]
         \\ mp_tac (GEN_ALL icing_rewriterProofsTheory.rewriteFPexp_returns_fp)
         \\ disch_then $ qspecl_then [‘st1’, ‘st2’, ‘e’, ‘FST(fp_times_one)’,
                                      ‘SND(fp_times_one)’, ‘env’, ‘e1’, ‘v’]
                       mp_tac
         \\ impl_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ qpat_x_assum `_ = App _ _` (fs o single)
  \\ qpat_x_assum `_ = e1` (fs o single)
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once terminationTheory.evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ‘st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ ntac 2 (simp[Once terminationTheory.evaluate_def, evaluate_case_case, astTheory.getOpClass_def])
  \\ simp[Once do_app_def]
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_times_one’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices’,
       ‘λ x. if (x = 0)
        then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)]
        else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ simp state_eqs
  \\ strip_tac \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1New _ _ = _’
  \\ strip_tac
  \\ qexistsl_tac [‘oracle’, ‘st1.fp_state.choices’]
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _’
  \\ ‘st1New = st1Upd’
     by (unabbrev_all_tac \\ fs state_eqs)
  \\ pop_assum (fs o single)
  \\ unabbrev_all_tac \\ imp_res_tac evaluate_sing
  \\ rveq
  \\ fs ([do_app_def, fp_translate_def, do_fprw_def, shift_fp_opts_def])
  \\ rveq \\ fs state_eqs
  \\ rpt conj_tac
  >- fp_inv_tac
  >- fp_inv_tac
  >- (fp_inv_tac \\ fs[FUN_EQ_THM])
  >- fp_inv_tac
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_times_one Here
                 (fp_bop FP_Mul fp (Fp_const 0x3FF0000000000000w))``,
        instWordTree_def, substLookup_def]
QED

Theorem fp_times_one_correct_unfold =
        REWRITE_RULE [fp_times_one_def] fp_times_one_correct;

(**
  Optimisation simulation proofs
  In combination with the automation from icing_optimisationsLib and the
  correctness proofs from source_to_sourceProofs, we automatically
  construct backwards simulation proofs for a run of the optimiser
**)

Theorem fp_comm_gen_correct:
  ∀ fpBop (st1 st2:'a semanticPrimitives$state) env e res.
  is_rewriteFPexp_correct [fp_comm_gen fpBop] st1 st2 env e res
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`, `fpBop`] strip_assume_tac  fp_comm_gen_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_comm_gen fpBop]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ simp[do_app_def, CaseEq"option", CaseEq"v", CaseEq"prod"]
  \\ rpt strip_tac \\ rveq \\ fs[] \\ rveq
  \\ rename [‘evaluate st1 env [e1] = (st2, Rval [v1])’,
             ‘evaluate st2 env [e2] = (st3, Rval [v2])’]
  \\ ‘st3.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ fs[]
  \\ ‘st2 = st1 with fp_state := st2.fp_state ∧
      st3 = st1 with fp_state := st3.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_comm_gen fpBop’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices)’,
       ‘λ x. if (x = 0)
        then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
        (case do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2)))
         (st3.fp_state.opts 0) st3.fp_state.rws of
         | NONE => [] | SOME r_opt => st3.fp_state.opts x)
        else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e2] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_comm_gen fpBop’,
       ‘st1’, ‘oracle’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ ‘st2.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
  \\ qexists_tac ‘oracle'’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ simp[evaluate_def]
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ fs state_eqs
  \\ simp([do_app_def, shift_fp_opts_def] @ state_eqs)
  \\ rpt conj_tac
  >- fp_inv_tac
  >- (fp_inv_tac \\ fs[FUN_EQ_THM])
  >- fp_inv_tac
  \\ qpat_x_assum `_ = Rval _` (fs o single o GSYM)
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree (fp_comm_gen fpBop) Here (fp_bop fpBop w2 w1)``,
        instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws (fp_bop fpBop w1 w2)`
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_comm_gen fpBop]` assume_tac)
  \\ `st3.fp_state.rws = st1.fp_state.rws` by fp_inv_tac
  \\ fs[]
QED

Theorem fp_comm_gen_correct_unfold = REWRITE_RULE [fp_comm_gen_def] fp_comm_gen_correct;
Theorem fp_comm_gen_correct_unfold_add = REWRITE_RULE [icing_optimisationsTheory.fp_comm_gen_def] (Q.SPEC ‘FP_Add’ fp_comm_gen_correct);
Theorem fp_comm_gen_correct_unfold_mul = REWRITE_RULE [icing_optimisationsTheory.fp_comm_gen_def] (Q.SPEC ‘FP_Mul’ fp_comm_gen_correct);

fun rename_each [] = ALL_TAC
| rename_each [first] = qmatch_asmsub_rename_tac first \\ qpat_x_assum first mp_tac \\ strip_tac
| rename_each (first::rest) = qmatch_asmsub_rename_tac first \\ qpat_x_assum first mp_tac \\ rename_each rest \\ strip_tac

Theorem fp_assoc_gen_correct:
  ∀ fpBop st1 st2 env e r.
    is_rewriteFPexp_correct [fp_assoc_gen fpBop] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [‘e’, ‘fpBop’] strip_assume_tac fp_assoc_gen_cases)
  >- (
  fs[] \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_assoc_gen fpBop]’
  \\ strip_tac
  \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
  \\ fsrw_tac [SATISFY_ss] []
  )
  \\ rveq \\ fs[]
  \\ qpat_x_assum ‘_ = (_, _)’ (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[] \\ rveq
  \\ rename1 ‘evaluate st1 env [e3] = (st1N, Rval [v3])’
  \\ ‘st1N.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ simp[Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[] \\ rveq
  \\ rename1 ‘evaluate st1N env [e2] = (st2N, Rval [v2])’
  (* Previously, v3 is renamed to v' by one of the rveq. We rename it back. *)
  \\ qpat_x_assum ‘evaluate _ _ [e2] = (_, _)’ mp_tac
  \\ rename1 ‘evaluate st1 env [e3] = (st1N, Rval [v3])’
  \\ disch_then assume_tac
  \\ simp[do_app_def, CaseEq"option", CaseEq"v", CaseEq"prod", CaseEq"result"]
  \\ rpt strip_tac \\ rveq \\ fs[] \\ rveq
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rename1 ‘evaluate _ env [e1] = (st3N, Rval [v1])’ \\ rveq
  (* Do the renaming dance again *)
  \\ rename1 ‘evaluate st1N env [e2] = (st2N, Rval [v2])’
  \\ qpat_x_assum ‘evaluate _ _ [e2] = (_, _)’ mp_tac
  \\ rename1 ‘evaluate st1 env [e3] = (st1N, Rval [v3])’
  \\ disch_then assume_tac
  \\ fs[CaseEq"option", CaseEq"v", CaseEq"prod", CaseEq"result"]
  \\ rveq \\ fs[]
  \\ ‘st2N.fp_state.canOpt = FPScope Opt’ by fp_inv_tac \\ fs[]
  \\ fs[shift_fp_opts_def]
  \\ ‘st3N.fp_state.canOpt = FPScope Opt’ by fp_inv_tac \\ fs[]
  \\ ‘st1N = st1 with fp_state := st1N.fp_state’ by (
    imp_res_tac isPureExp_same_ffi
    \\ fs[isPureExp_def]
    \\ res_tac
    \\ fs[state_component_equality]
    )
  \\ ‘st2N = st1 with fp_state := st2N.fp_state’ by (
    imp_res_tac isPureExp_same_ffi
    \\ fs[isPureExp_def]
    \\ res_tac
    \\ fs[state_component_equality]
    )
  \\ ‘st3N = st1 with fp_state := st3N.fp_state’ by (
    imp_res_tac isPureExp_same_ffi
    \\ fs[isPureExp_def]
    \\ res_tac
    \\ fs[state_component_equality]
    )
  \\ fs[]
  (*
  rename_each requires that the names we assign in individual steps do not intersect with existing names.
  Therefore, we introduce these temporary names and then set the final names in a next step.
  *)
  \\ rename_each [‘fp_translate v2Op3 = SOME (FP_WordTree w2Op3_temp)’,
                  ‘fp_translate v1 = SOME (FP_WordTree w1_temp)’,
                  ‘fp_translate v3 = SOME (FP_WordTree w3_temp)’,
                  ‘fp_translate v2 = SOME (FP_WordTree w2_temp)’]
  \\ rename_each [‘fp_translate v2Op3 = SOME (FP_WordTree w2Op3)’,
                  ‘fp_translate v1 = SOME (FP_WordTree w1)’,
                  ‘fp_translate v3 = SOME (FP_WordTree w3)’,
                  ‘fp_translate v2 = SOME (FP_WordTree w2)’]
  \\ qpat_assum ‘evaluate _ _ [e1] = _’
                  (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
     qspecl_then [
         ‘fp_assoc_gen fpBop’,
         ‘st1 with fp_state := st1.fp_state with
                                  <| opts := st1N.fp_state.opts;
                                     choices :=
                                     st1.fp_state.choices +
                                     (st1N.fp_state.choices - st1.fp_state.choices) +
                                     (st1.fp_state.choices + (st2N.fp_state.choices - st1N.fp_state.choices)) - st1.fp_state.choices |>’,
         ‘λ x. if (x = 1) then
                 [RewriteApp Here (LENGTH st1.fp_state.rws + 1)]
                 ++
                 (case
                 do_fprw (Rval (FP_WordTree (fp_bop fpBop w2 w3)))
                         (st2N.fp_state.opts 0) st2N.fp_state.rws of
                 | NONE => []
                 | SOME _ =>
                     (MAP (λ x. case x of | RewriteApp p id => RewriteApp (Right p) id) (st2N.fp_state.opts 0)))
                 ++
                 (case
                 do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2Op3)))
                         (st3N.fp_state.opts 0) st3N.fp_state.rws
                 of
                 | NONE => []
                 | SOME _ => st3N.fp_state.opts 0)
               else []’
       ] mp_tac)
  \\ fs[isPureExp_def]
  \\ impl_tac >- (fp_inv_tac \\ fs[shift_fp_opts_def])
  \\ strip_tac
  \\ qpat_assum ‘evaluate _ _ [e2] = _’
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
    qspecl_then [
        ‘fp_assoc_gen fpBop’,
        ‘st1’,
        ‘oracle’] mp_tac)
  \\ fs[isPureExp_def]
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum ‘evaluate _ _ [e3] = _’
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
    qspecl_then [
        ‘fp_assoc_gen fpBop’,
        ‘st1’,
        ‘oracle'’] mp_tac)
  \\ fs[isPureExp_def]
  \\ strip_tac
  \\ pop_assum (mp_then Any (qspec_then ‘st1.fp_state.choices’ assume_tac) (CONJUNCT1 evaluate_add_choices))
  \\ qexists_tac ‘oracle''’
  \\ qexists_tac ‘st1.fp_state.choices’
  \\ simp[evaluate_def]
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ fs (shift_fp_opts_def :: state_eqs)
  \\ pop_assum kall_tac
  \\ ‘st1.fp_state.rws = st1N.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ first_x_assum (mp_then Any (qspec_then ‘st1.fp_state.choices + (st1N.fp_state.choices - st1.fp_state.choices)’ assume_tac)
                    (CONJUNCT1 evaluate_add_choices))
  \\ fs state_eqs
  \\ pop_assum kall_tac
  \\ ‘st1N.fp_state.rws = st2N.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ simp[do_app_def]
  \\ pop_assum kall_tac
  \\ simp[Once do_fprw_def, rwAllWordTree_def, fp_translate_def]
  \\ simp[Once do_fprw_def, rwAllWordTree_def, fp_translate_def]
  \\ fs state_eqs
  \\ rpt conj_tac
  >- fp_inv_tac
  >- (fp_inv_tac \\ fs[FUN_EQ_THM])
  >- fp_inv_tac
  \\ qpat_x_assum ‘_ = Rval _’ (fs o single o GSYM)
  \\ simp[Once do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL “rwFp_pathWordTree (fp_assoc_gen fpBop) Here (fp_bop fpBop (fp_bop fpBop w1 w2) w3)”,
        instWordTree_def, substLookup_def]
  \\ Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop fpBop w2 w3)))
               (st2N.fp_state.opts 0) st2N.fp_state.rws’ \\ fs[]
  >- (
  Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2Op3)))
            (st3N.fp_state.opts 0) st3N.fp_state.rws’ \\ fs[]
  >- (
    simp[rwAllWordTree_def, fp_bop_def] \\ rveq
    \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def, fp_translate_def]
    )
  >- (
    fs[do_fprw_def, CaseEq "option"] \\ rveq
    \\ Cases_on ‘rwAllWordTree (st3N.fp_state.opts 0)
                 (st2N.fp_state.rws ++ [fp_assoc_gen fpBop])
                 (Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’
    \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def, fp_translate_def] \\ rveq
    \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
    \\ pop_assum (fs o single)
    \\ imp_res_tac rwAllWordTree_append_opt
    \\ pop_assum (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac) \\ fs []
    )
  )
  >- (
  Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2Op3)))
            (st3N.fp_state.opts 0) st3N.fp_state.rws’
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def, fp_translate_def]
  \\ REVERSE (Cases_on ‘rwAllWordTree
               (MAP
                (λx. case x of RewriteApp p id => RewriteApp (Right p) id)
                (st2N.fp_state.opts 0))
               (st2N.fp_state.rws ++ [fp_assoc_gen fpBop])
               (Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’)
  \\ fs[] \\ rveq
  \\ fs[do_fprw_def, CaseEq "option"] \\ rveq
  >- (
    qpat_x_assum ‘rwAllWordTree (st2N.fp_state.opts 0) _ _ = _’ (mp_then Any assume_tac rwAllWordTree_comp_right)
    \\ pop_assum (qspecl_then [ ‘fpBop’, ‘w1’ ] assume_tac)
    \\ fs [fp_translate_def] \\ rveq
    \\ first_x_assum (mp_then Any (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac) rwAllWordTree_append_opt) \\ fs[]
    )
  >- (
    fs [do_fprw_def]
    \\ Cases_on ‘rwAllWordTree (st2N.fp_state.opts 0) st2N.fp_state.rws
             (Fp_bop fpBop w2 w3)’ \\ fs[]
    \\ Cases_on ‘rwAllWordTree (st3N.fp_state.opts 0) st3N.fp_state.rws
             (Fp_bop fpBop w1 w2Op3)’ \\ fs[] \\ rveq
    \\ fs[fp_translate_def] \\ rveq
    \\ qpat_x_assum ‘rwAllWordTree _ _ _ = SOME w2Op3’ (mp_then Any (qspecl_then [ ‘fpBop’, ‘w1’ ] assume_tac) rwAllWordTree_comp_right)
    \\ first_x_assum (mp_then Any (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac) rwAllWordTree_append_opt) \\ fs[]
    )
  >- (
    fs[]
    \\ Cases_on ‘rwAllWordTree
                 (MAP
                  (λx. case x of RewriteApp p id => RewriteApp (Right p) id)
                  (st2N.fp_state.opts 0) ++ st3N.fp_state.opts 0)
                 (st2N.fp_state.rws ++ [fp_assoc_gen fpBop])
                 (Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’
    \\ fs[do_fprw_def]
    \\ Cases_on ‘rwAllWordTree (st2N.fp_state.opts 0) st2N.fp_state.rws
             (Fp_bop fpBop w2 w3)’ \\ fs[]
    \\ Cases_on ‘rwAllWordTree (st3N.fp_state.opts 0) st3N.fp_state.rws
             (Fp_bop fpBop w1 w2Op3)’ \\ fs[] \\ rveq
    \\ fs[fp_translate_def] \\ rveq
    >- (
      qpat_x_assum ‘rwAllWordTree _ st2N.fp_state.rws _ = SOME _’ (mp_then Any assume_tac rwAllWordTree_comp_right)
      \\ pop_assum (qspecl_then [ ‘fpBop’, ‘w1’ ] assume_tac)
      \\ first_x_assum (mp_then Any (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac) rwAllWordTree_append_opt)
      \\ fs[fp_translate_def] \\ rveq
      \\ qpat_x_assum ‘rwAllWordTree _ st3N.fp_state.rws _ = SOME _’ (mp_then Any assume_tac rwAllWordTree_append_opt)
      \\ first_x_assum (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac)
      \\ ‘st3N.fp_state.rws = st2N.fp_state.rws’ by fp_inv_tac
      \\ pop_assum (fs o single)
      \\ fs[fp_translate_def] \\ rveq
      \\ assume_tac rwAllWordTree_chaining_exact
      \\ pop_assum ( qspecl_then [ ‘(Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’,
                                   ‘(Fp_bop fpBop w1 fv_opt)’,
                                   ‘fv_opt'’,
                                   ‘(MAP λinst. case inst of RewriteApp p id => RewriteApp (Right p) id) (st2N.fp_state.opts 0)’,
                                   ‘(st3N.fp_state.opts 0)’,
                                   ‘st2N.fp_state.rws ++ [fp_assoc_gen fpBop]’
                                   ] assume_tac ) \\ fs []
    )
    >- (
      qpat_x_assum ‘rwAllWordTree _ st2N.fp_state.rws _ = SOME fv_opt’ (mp_then Any assume_tac rwAllWordTree_comp_right)
      \\ pop_assum (qspecl_then [ ‘fpBop’, ‘w1’ ] assume_tac)
      \\ pop_assum (mp_then Any (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac) rwAllWordTree_append_opt)
      \\ qpat_x_assum ‘rwAllWordTree _ st3N.fp_state.rws _ = SOME _’ (mp_then Any assume_tac rwAllWordTree_append_opt)
      \\ first_x_assum (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac)
      \\ ‘st3N.fp_state.rws = st2N.fp_state.rws’ by fp_inv_tac
      \\ pop_assum (fs o single)
      \\ assume_tac rwAllWordTree_chaining_exact
      \\ pop_assum ( qspecl_then [ ‘(Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’,
                                 ‘(Fp_bop fpBop w1 fv_opt)’,
                                 ‘fv_opt'’,
                                 ‘(MAP (λinst. case inst of RewriteApp p id => RewriteApp (Right p) id) (st2N.fp_state.opts 0))’,
                                 ‘st3N.fp_state.opts 0’,
                                 ‘st2N.fp_state.rws ++ [fp_assoc_gen fpBop]’ ] assume_tac ) \\ fs[]
    )
  )
  >- (
    Cases_on ‘rwAllWordTree
              (MAP (λx. case x of RewriteApp p id => RewriteApp (Right p) id)
               (st2N.fp_state.opts 0) ++ st3N.fp_state.opts 0)
              (st2N.fp_state.rws ++ [fp_assoc_gen fpBop])
              (Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’
    \\ fs[fp_translate_def] \\ rveq
    \\ qpat_x_assum ‘rwAllWordTree _ st2N.fp_state.rws _ = SOME fv_opt’ (mp_then Any assume_tac rwAllWordTree_comp_right)
    \\ pop_assum (qspecl_then [ ‘fpBop’, ‘w1’ ] assume_tac)
    \\ pop_assum (mp_then Any (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac) rwAllWordTree_append_opt)
    \\ qpat_x_assum ‘rwAllWordTree _ st3N.fp_state.rws _ = SOME _’ (mp_then Any assume_tac rwAllWordTree_append_opt)
    \\ first_x_assum (qspec_then ‘[fp_assoc_gen fpBop]’ assume_tac)
    \\ assume_tac rwAllWordTree_chaining_exact
    \\ pop_assum ( qspecl_then [ ‘(Fp_bop fpBop w1 (Fp_bop fpBop w2 w3))’,
                                 ‘(Fp_bop fpBop w1 fv_opt)’,
                                 ‘fv_opt'’,
                                 ‘(MAP (λinst. case inst of RewriteApp p id => RewriteApp (Right p) id) (st2N.fp_state.opts 0))’,
                                 ‘st3N.fp_state.opts 0’,
                                 ‘st2N.fp_state.rws ++ [fp_assoc_gen fpBop]’ ] assume_tac ) \\ fs[]
    )
  )
QED

Theorem fp_assoc_gen_correct_unfold = REWRITE_RULE [fp_assoc_gen_def] fp_assoc_gen_correct;
Theorem fp_assoc_gen_correct_unfold_add = REWRITE_RULE [icing_optimisationsTheory.fp_assoc_gen_def] (Q.SPEC ‘FP_Add’ fp_assoc_gen_correct);
Theorem fp_assoc_gen_correct_unfold_mul = REWRITE_RULE [icing_optimisationsTheory.fp_assoc_gen_def] (Q.SPEC ‘FP_Mul’ fp_assoc_gen_correct);

Theorem fp_fma_intro_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_fma_intro] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspec_then ‘e’ strip_assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_fma_intro_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_fma_intro]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def]
  \\ disch_then (mp_tac o SIMP_RULE std_ss [evaluate_def, evaluate_case_case])
  \\ ntac 6 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ simp[do_app_def, CaseEq"option", CaseEq"v", CaseEq"prod"]
  \\ rpt strip_tac \\ rveq \\ fs[] \\ rveq
  \\ rename [‘evaluate st1 _ [e2] = (st2, Rval[v2])’,
             ‘evaluate st2 _ [e1] = (st3, Rval [v1])’,
             ‘evaluate st3 _ [e3] = (st4, Rval [v3])’]
  \\ ‘st4.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ fs[]
  \\ ‘st2 = st1 with fp_state := st2.fp_state ∧
      st3 = st1 with fp_state := st3.fp_state ∧
      st4 = st1 with fp_state := st4.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ qpat_assum `evaluate _ _ [e1] = _` (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_fma_intro’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices + (st4.fp_state.choices - st3.fp_state.choices) + (st2.fp_state.choices - st1.fp_state.choices)’,
       ‘λ x. if (x = 1)
             then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)]
                  ++
                  (case do_fprw (Rval (FP_WordTree (fp_top FP_Fma w1 w2 w3))) (st4.fp_state.opts (x-1)) st4.fp_state.rws
                   of
                   | NONE => []
                   | SOME r_opt => st4.fp_state.opts (x-1))
             else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e2] = _` (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_fma_intro’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices + (st4.fp_state.choices - st3.fp_state.choices)’, ‘oracle’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e3] = _` (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (qspecl_then [‘fp_fma_intro’, ‘st1’, ‘oracle'’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ ‘st3.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ ‘st2.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ qexists_tac ‘oracle''’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ first_x_assum (mp_then Any (qspec_then ‘st1.fp_state.choices’ assume_tac) (CONJUNCT1 evaluate_add_choices))
  \\ fs([evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def, evaluate_case_case] @ state_eqs)
  \\ simp[do_app_def, Once do_fprw_def, rwAllWordTree_def, do_fprw_def, fp_translate_def, shift_fp_opts_def]
  \\ fs state_eqs
  \\ rpt conj_tac
  >- fp_inv_tac
  >- (fp_inv_tac \\ fs[FUN_EQ_THM])
  >- fp_inv_tac
  \\ qpat_x_assum `_ = Rval _` (fs o single o GSYM)
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL “rwFp_pathWordTree (fp_fma_intro) Here (fp_bop FP_Add (fp_bop FP_Mul w2 w3) w1)”,
        instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st4.fp_state.opts 0) st4.fp_state.rws (fp_top FP_Fma w1 w2 w3)`
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_top_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_fma_intro]` assume_tac)
  \\ `st4.fp_state.rws = st1.fp_state.rws` by fp_inv_tac
  \\ fs[]
QED

Theorem fp_fma_intro_correct_unfold = REWRITE_RULE [fp_fma_intro_def] fp_fma_intro_correct;

Theorem fp_sub_add_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_sub_add] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspecl_then [`e`] strip_assume_tac
                 (ONCE_REWRITE_RULE [DISJ_COMM] fp_sub_add_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_sub_add]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ rename1 ‘evaluate st1 env [e2] = (st1N, Rval v2)’
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ ‘st1N.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ fs[]
  \\ simp[do_app_def, CaseEq"option", CaseEq"v", CaseEq"prod", CaseEq"result"]
  \\ rpt strip_tac \\ rveq \\ fs[] \\ rveq
  \\ ntac 2 (pop_assum mp_tac)
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rveq
  \\ simp[CaseEq"option",CaseEq"v"]
  \\ rename [‘evaluate
              (shift_fp_opts st1N with <| refs := st1N.refs; ffi:=st1N.ffi|>)
              env [e1] = (st2N, Rval [v1])’,
             ‘evaluate st1 env [e2] = (st1N, Rval [v2])’]
  \\ rpt strip_tac \\ rveq \\ fs[]
  \\ ‘st2N.fp_state.canOpt = FPScope Opt’ by (fp_inv_tac \\ fs[shift_fp_opts_def])
  \\ fs[]
  \\ ‘st1N = st1 with fp_state := st1N.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ ‘st2N = st1 with fp_state := st2N.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality, shift_fp_opts_def])
  \\ qpat_assum ‘evaluate _ _ [e1] = _’
                  (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
     qspecl_then [
       ‘fp_sub_add’,
       ‘st1 with fp_state := st1.fp_state with
        <| opts := st1N.fp_state.opts;
        choices := st1.fp_state.choices + (st1N.fp_state.choices - st1.fp_state.choices) |>’,
       ‘λ x. if (x = 0) then
          [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
          (case
           do_fprw (Rval (FP_WordTree (fp_uop FP_Neg w1)))
             (st1N.fp_state.opts 0) st1N.fp_state.rws
         of
           NONE => []
           | SOME r_opt =>
           (MAP (λ x. case x of |RewriteApp p id => RewriteApp (Right p) id) ((st1N.fp_state.opts 0)))) ++
          (case do_fprw (Rval (FP_WordTree (fp_bop FP_Add w1' w2)))
           (st2N.fp_state.opts 0) st2N.fp_state.rws of
           | NONE => []
           | SOME r_opt => st2N.fp_state.opts x)
        else []’]
     mp_tac)
  \\ fs[isPureExp_def]
  \\ impl_tac >- (fp_inv_tac \\ fs[shift_fp_opts_def])
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e2] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
     qspecl_then [
       ‘fp_sub_add’,
       ‘st1’,
       ‘oracle’] mp_tac)
  \\ fs[isPureExp_def]
  \\ strip_tac
  \\ pop_assum (mp_then Any (qspec_then ‘st1.fp_state.choices’ assume_tac) (CONJUNCT1 evaluate_add_choices))
  \\ qexists_tac ‘oracle'’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ simp[evaluate_def]
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ fs (shift_fp_opts_def :: state_eqs)
  \\ ‘st1.fp_state.rws = st1N.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ simp[do_app_def]
  \\ fs state_eqs
  \\ rpt conj_tac
  >- fp_inv_tac
  >- (fp_inv_tac \\ fs[FUN_EQ_THM])
  >- fp_inv_tac
  \\ qpat_x_assum `_ = Rval _` (fs o single o GSYM)
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_sub_add Here (fp_bop FP_Sub w1' w1)``,
        instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st1N.fp_state.opts 0) st1N.fp_state.rws (fp_uop FP_Neg w1)`
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_uop_def]
  >- (
   fs[do_fprw_def] \\ rveq
   \\ fs[fp_translate_def] \\ rveq
   \\ Cases_on ‘rwAllWordTree (st2N.fp_state.opts 0) st2N.fp_state.rws
              (fp_bop FP_Add w1' (Fp_uop FP_Neg w1))’
   \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
   \\ imp_res_tac rwAllWordTree_append_opt
   \\ first_x_assum (qspec_then `[fp_sub_add]` assume_tac)
   \\ `st1N.fp_state.rws = st2N.fp_state.rws` by fp_inv_tac
   \\ fs[])
  \\ imp_res_tac rwAllWordTree_comp_right
  \\ first_x_assum (qspecl_then [‘w1'’, ‘FP_Add’] assume_tac)
  \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_append_opt)
  \\ first_x_assum (qspec_then `[fp_sub_add]` assume_tac)
  \\ fs[do_fprw_def] \\ rveq
  \\ fs[fp_translate_def] \\ rveq
  \\ Cases_on ‘rwAllWordTree (st2N.fp_state.opts 0) st2N.fp_state.rws
               (fp_bop FP_Add w1' w2)’
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ pop_assum (mp_then Any mp_tac rwAllWordTree_append_opt)
  \\ disch_then (qspec_then ‘[fp_sub_add]’ mp_tac)
  \\ `st1N.fp_state.rws = st2N.fp_state.rws` by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_chaining_exact)
  \\ disch_then (fn th => first_x_assum (fn ithm => mp_then Any assume_tac ithm th))
  \\ fs[]
QED

Theorem fp_sub_add_correct_unfold = REWRITE_RULE [fp_sub_add_def] fp_sub_add_correct;

Theorem fp_times_minus_one_neg_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_minus_one_neg] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_times_minus_one_neg_correct_unfold =
        REWRITE_RULE [fp_times_minus_one_neg_def] fp_times_minus_one_neg_correct;

Theorem fp_neg_times_minus_one_correct_unfold = REWRITE_RULE [fp_neg_times_minus_one_def] fp_neg_times_minus_one_correct;

Theorem fp_neg_push_mul_r_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_neg_push_mul_r] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspecl_then [`e`] strip_assume_tac
                 (ONCE_REWRITE_RULE [DISJ_COMM] fp_neg_push_mul_r_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_neg_push_mul_r]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rename1 ‘evaluate st1 env [e3] = (st1N, Rval [v3])’
  \\ ‘st1N.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ simp[Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rename1 ‘evaluate st1N env [e2] = (st2N, Rval [v2])’
  \\ simp[do_app_def, CaseEq"option", CaseEq"v", CaseEq"prod", CaseEq"result"]
  \\ rpt strip_tac \\ rveq \\ fs[] \\ rveq
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rename1 ‘evaluate _ env [e1] = (st3N, Rval [v1])’
  \\ fs[CaseEq"option", CaseEq"v", CaseEq"prod", CaseEq"result"]
  \\ rveq \\ fs[]
  \\ ‘st2N.fp_state.canOpt = FPScope Opt’
     by (fp_inv_tac \\ fs[shift_fp_opts_def])
  \\ fs[]
  \\ ‘st3N.fp_state.canOpt = FPScope Opt’
     by (fp_inv_tac \\ fs[shift_fp_opts_def])
  \\ fs[shift_fp_opts_def]
  \\ ‘st1N = st1 with fp_state := st1N.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ ‘st2N = st1 with fp_state := st2N.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality, shift_fp_opts_def])
  \\ ‘st3N = st1 with fp_state := st3N.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality, shift_fp_opts_def])
  \\ qpat_assum ‘evaluate _ _ [e1] = _’
                  (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
     qspecl_then [
       ‘fp_neg_push_mul_r’,
       ‘st1 with fp_state := st1.fp_state with
        <| opts := st1N.fp_state.opts;
        choices :=
          st1.fp_state.choices +
          (st1N.fp_state.choices - st1.fp_state.choices) +
          (st1.fp_state.choices + (st2N.fp_state.choices - st1N.fp_state.choices)) -
          st1.fp_state.choices |>’,
       ‘λ x. if (x = 2) then
          [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
          (case
           do_fprw (Rval (FP_WordTree (fp_uop FP_Neg w1)))
           (st2N.fp_state.opts 0) st2N.fp_state.rws of
           | NONE => []
           | SOME _ =>
             MAP (λ x. case x of |RewriteApp p id => RewriteApp (Left p) id)
             (MAP (λ x. case x of |RewriteApp p id => RewriteApp (Right p) id) (st2N.fp_state.opts 0))) ++
          (case
           do_fprw (Rval (FP_WordTree (fp_bop FP_Mul w1' w2)))
             (st3N.fp_state.opts 0) st3N.fp_state.rws
           of
           NONE => []
           | SOME r_opt => MAP (λ x. case x of |RewriteApp p id => RewriteApp (Left p) id) (st3N.fp_state.opts 0)) ++
          (case
           do_fprw (Rval (FP_WordTree (fp_bop FP_Add w1'' w2')))
             (st3N.fp_state.opts 1) st3N.fp_state.rws
           of
           NONE => []
           | SOME r_opt => st3N.fp_state.opts 1)
        else []’]
     mp_tac)
  \\ fs[isPureExp_def]
  \\ impl_tac >- (fp_inv_tac \\ fs[shift_fp_opts_def])
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e2] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
     qspecl_then [
       ‘fp_neg_push_mul_r’,
       ‘st1’,
       ‘oracle’] mp_tac)
  \\ fs[isPureExp_def]
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e3] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ disch_then (
     qspecl_then [
       ‘fp_neg_push_mul_r’,
       ‘st1’,
       ‘oracle'’] mp_tac)
  \\ fs[isPureExp_def]
  \\ strip_tac
  \\ pop_assum (mp_then Any (qspec_then ‘st1.fp_state.choices’ assume_tac) (CONJUNCT1 evaluate_add_choices))
  \\ qexists_tac ‘oracle''’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ simp[evaluate_def]
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ fs (shift_fp_opts_def :: state_eqs)
  \\ pop_assum kall_tac
  \\ ‘st1.fp_state.rws = st1N.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ first_x_assum (mp_then Any (qspec_then ‘st1.fp_state.choices + (st1N.fp_state.choices - st1.fp_state.choices)’ assume_tac) (CONJUNCT1 evaluate_add_choices))
  \\ fs state_eqs
  \\ pop_assum kall_tac
  \\ ‘st1N.fp_state.rws = st2N.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ simp[do_app_def]
  \\ pop_assum kall_tac
  \\ simp[Once do_fprw_def, rwAllWordTree_def, fp_translate_def]
  \\ simp[Once do_fprw_def, rwAllWordTree_def, fp_translate_def]
  \\ fs state_eqs
  \\ rpt conj_tac
  >- fp_inv_tac
  >- (fp_inv_tac \\ fs[FUN_EQ_THM])
  >- fp_inv_tac
  \\ qpat_x_assum `_ = Rval _` (fs o single o GSYM)
  \\ simp[Once do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_neg_push_mul_r Here
               (fp_bop FP_Add (fp_uop FP_Neg (fp_bop FP_Mul w1' w1)) w2')``,
        instWordTree_def, substLookup_def]
  \\ Cases_on ‘do_fprw (Rval (FP_WordTree (fp_uop FP_Neg w1)))
                     (st2N.fp_state.opts 0) st2N.fp_state.rws’
  \\ fs[]
  >- (
   rveq
   \\ Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop FP_Mul w1' w2)))
                     (st3N.fp_state.opts 0) st3N.fp_state.rws’
   \\ fs[]
   >- (
    rveq
    \\ Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop FP_Add w1'' w2')))
                 (st3N.fp_state.opts 1) st3N.fp_state.rws’
    \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def, fpValTreeTheory.fp_uop_def, fp_translate_def]
    \\ fs[do_fprw_def, CaseEq "option"]
    \\ qpat_x_assum `rwAllWordTree _ _ _ = SOME _`
                    (mp_then Any assume_tac rwAllWordTree_append_opt)
    \\ first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac)
    \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
    \\ pop_assum (fs o single))
   \\ fs[do_fprw_def, CaseEq "option"] \\ rveq
   \\ imp_res_tac rwAllWordTree_comp_left
   \\ first_x_assum (qspecl_then [‘w2'’, ‘FP_Add’] assume_tac)
   \\ pop_assum (mp_then Any assume_tac rwAllWordTree_append_opt)
   \\ first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac)
   \\ Cases_on ‘rwAllWordTree (st3N.fp_state.opts 1) st3N.fp_state.rws
                     (fp_bop FP_Add w1'' w2')’
   \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def, fpValTreeTheory.fp_uop_def, fp_translate_def]
   >- (
    rveq \\ fs[fp_translate_def] \\ rveq
    \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
    \\ pop_assum (fs o single))
   \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_append_opt)
   \\ first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac)
   \\ DISJ2_TAC \\ irule rwAllWordTree_chaining_exact
   \\ once_rewrite_tac [CONJ_COMM] \\ qexists_tac ‘Fp_bop FP_Add w1'' w2'’
   \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
   \\ pop_assum (fs o single)
   \\ rveq \\ fs[fp_translate_def])
  \\ Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop FP_Mul w1' w2)))
                     (st3N.fp_state.opts 0) st3N.fp_state.rws’
  \\ Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop FP_Add w1'' w2')))
                    (st3N.fp_state.opts 1) st3N.fp_state.rws’
  \\ fs[do_fprw_def, CaseEq "option"] \\ rveq \\ fs[]
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def, fpValTreeTheory.fp_uop_def, fp_translate_def]
  \\ rveq \\ fs[fp_translate_def] \\ rveq
  >- (
   imp_res_tac rwAllWordTree_comp_right
   \\ first_x_assum (qspecl_then [‘w1'’, ‘FP_Mul’] assume_tac)
   \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_comp_left)
   \\ first_x_assum (qspecl_then [‘FP_Add’, ‘w2'’] assume_tac)
   \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
   \\ pop_assum (fs o single)
   \\ imp_res_tac rwAllWordTree_append_opt
   \\ rpt (first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac))
   \\ fs[])
  >- (
   last_x_assum (mp_then Any assume_tac rwAllWordTree_comp_right)
   \\ first_x_assum (qspecl_then [‘FP_Mul’, ‘w1'’] assume_tac)
   \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_comp_left)
   \\ first_x_assum (qspecl_then [‘FP_Add’, ‘w2'’] assume_tac)
   \\ DISJ2_TAC
   \\ irule rwAllWordTree_chaining_exact
   \\ imp_res_tac rwAllWordTree_append_opt
   \\ rpt (first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac))
   \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
   \\ pop_assum (fs o single))
  >- (
   last_x_assum (mp_then Any assume_tac rwAllWordTree_comp_right)
   \\ first_x_assum (qspecl_then [‘FP_Mul’, ‘w1'’] assume_tac)
   \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_comp_left)
   \\ first_x_assum (qspecl_then [‘FP_Add’, ‘w2'’] assume_tac)
   \\ last_x_assum (mp_then Any assume_tac rwAllWordTree_comp_left)
   \\ first_x_assum (qspecl_then [‘FP_Add’, ‘w2'’] assume_tac)
   \\ DISJ2_TAC
   \\ irule rwAllWordTree_chaining_exact
   \\ imp_res_tac rwAllWordTree_append_opt
   \\ rpt (first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac))
   \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
   \\ pop_assum (fs o single))
  \\ last_x_assum (mp_then Any assume_tac rwAllWordTree_comp_right)
  \\ first_x_assum (qspecl_then [‘FP_Mul’, ‘w1'’] assume_tac)
  \\ first_x_assum (mp_then Any assume_tac rwAllWordTree_comp_left)
  \\ first_x_assum (qspecl_then [‘FP_Add’, ‘w2'’] assume_tac)
  \\ last_x_assum (mp_then Any assume_tac rwAllWordTree_comp_left)
  \\ first_x_assum (qspecl_then [‘FP_Add’, ‘w2'’] assume_tac)
  \\ DISJ2_TAC
  \\ irule rwAllWordTree_chaining_exact
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ rpt (first_x_assum (qspec_then ‘[fp_neg_push_mul_r]’ assume_tac))
  \\ ‘st2N.fp_state.rws = st3N.fp_state.rws’ by fp_inv_tac
  \\ pop_assum (fs o single)
  \\ once_rewrite_tac [CONJ_COMM]
  \\ asm_exists_tac \\ fs[]
  \\ irule rwAllWordTree_chaining_exact
  \\ fs[]
QED

Theorem fp_neg_push_mul_r_correct_unfold =
        REWRITE_RULE [fp_neg_push_mul_r_def] fp_neg_push_mul_r_correct;

Theorem fp_times_two_to_add_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_two_to_add] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_times_two_to_add_correct_unfold =
        REWRITE_RULE [fp_times_two_to_add_def] fp_times_two_to_add_correct;

Theorem fp_times_three_to_add_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_three_to_add] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_times_three_to_add_correct_unfold =
        REWRITE_RULE [fp_times_three_to_add_def] fp_times_three_to_add_correct;

Theorem fp_plus_zero_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_plus_zero] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_plus_zero_correct_unfold =
        REWRITE_RULE [fp_plus_zero_def] fp_plus_zero_correct;

Theorem fp_distribute_gen_correct:
  ∀ fpBop1 fpBop2 st1 st2 env e r.
   is_rewriteFPexp_correct [fp_distribute_gen fpBop1 fpBop2] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_distribute_gen_correct_unfold =
        REWRITE_RULE [fp_distribute_gen_def] fp_distribute_gen_correct;
Theorem fp_distribute_gen_correct_unfold_add = REWRITE_RULE [icing_optimisationsTheory.fp_distribute_gen_def] (Q.SPECL [‘FP_Mul’, ‘FP_Add’] fp_distribute_gen_correct);

val _ = export_theory ();
