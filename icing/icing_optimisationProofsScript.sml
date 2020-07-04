(*
  Correctness proofs for Icing optimisations supported by CakeML
*)
open bossLib;
open semanticPrimitivesTheory evaluatePropsTheory;
open fpValTreeTheory fpSemPropsTheory fpOptTheory fpOptPropsTheory
     icing_optimisationsTheory icing_rewriterTheory source_to_sourceProofsTheory
     terminationTheory;

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

Theorem fp_comm_gen_real_id:
  ∀ fpBop st1 st2 env e r.
  is_real_id_exp [fp_comm_gen fpBop] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_assoc_gen_real_id:
  ∀ fpBop st1 st2 env e r.
  is_real_id_exp [fp_assoc_gen fpBop] st1 st2 env e r
Proof
  cheat
QED

Theorem fma_intro_real_id:
  ∀ st1 st2 env e r.
   is_real_id_exp [fp_fma_intro] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_sub_add_real_id:
  ∀ st1 st2 env e r.
   is_real_id_exp [fp_sub_add] st1 st2 env e r
Proof
  cheat
QED

Theorem fp_neg_push_mul_r_real_id:
  ∀ st1 st2 env e r.
   is_real_id_exp [fp_neg_push_mul_r] st1 st2 env e r
Proof
  cheat
QED


Theorem fp_comm_gen_correct:
  ∀ fpBop (st1 st2:'a semanticPrimitives$state) env e res.
  is_rewriteFPexp_correct [fp_comm_gen fpBop] st1 st2 env e res
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspecl_then [`e`, `fpBop`] strip_assume_tac
                 (ONCE_REWRITE_RULE [DISJ_COMM] fp_comm_gen_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_comm_gen fpBop]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
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
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
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
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def]
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
        then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
        (case do_fprw (Rval (FP_WordTree (fp_top FP_Fma w1 w2 w3))) (st4.fp_state.opts (x-1)) st4.fp_state.rws of | NONE => [] | SOME r_opt => st4.fp_state.opts (x-1))
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
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
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
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
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
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rename1 ‘evaluate st1 env [e3] = (st1N, Rval [v3])’
  \\ ‘st1N.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ simp[Once evaluate_cons, evaluate_case_case]
  \\ disch_then (mp_tac o (SIMP_RULE std_ss [evaluate_def]))
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
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
  \\ simp[REVERSE, astTheory.getOpClass_def, astTheory.isFpBool_def,
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

val _ = export_theory ();

(** UNUSED:
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

(*
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
*) **)
