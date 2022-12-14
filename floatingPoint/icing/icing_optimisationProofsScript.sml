(*
  Correctness proofs for peephole optimisations supported by PrincessCake
  Each optimisation is defined in icing_optimisationsScript.sml.
  This file proves the low-level correctness theorems for a single
  application of the optimisation.
  Real-valued identity proofs are in icing_realIdProofsScript.sml.
  The overall correctness proof for a particular run of the optimiser
  from source_to_source2Script is build using the automation in
  icing_optimisationsLib and the general theorems from
  source_to_source2ProofsScript.
*)
open bossLib ml_translatorLib;
open semanticPrimitivesTheory evaluatePropsTheory;
open fpValTreeTheory fpSemPropsTheory fpOptTheory fpOptPropsTheory
     icing_optimisationsTheory icing_rewriterTheory source_to_source2ProofsTheory
     floatToRealTheory floatToRealProofsTheory evaluateTheory
     pureExpsTheory binary_ieeeTheory;

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
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, option_map_def]
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
  \\ fs[rwAllWordTree_def, rwFp_pathWordTree_def, option_map_def]
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
       isPureExp e ∧ isFpArithExp e ∧
       rewriteFPexp [fp_assoc2_gen fpBop] (App (FP_bop fpBop) [e1; (App (FP_bop fpBop) [e2; e3])]) =
       (App (FP_bop fpBop) [App (FP_bop fpBop) [e1; e2]; e3])) ∨
    (rewriteFPexp [fp_assoc2_gen fpBop] e = e)
Proof
  rpt gen_tac \\ Cases_on `e`
  \\ fs[fp_assoc2_gen_def, reverse_tuple_def, fp_assoc_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[isPureOp_def]
  \\ Cases_on ‘isPureExpList els ∧
      isFpArithPat (Binop fpBop (PatVar 0) (Binop fpBop (PatVar 1) (PatVar 2))) ∧
      isFpArithPat (Binop fpBop (Binop fpBop (PatVar 0) (PatVar 1)) (PatVar 2)) ∧
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

Theorem fp_times_minus_one_neg_cases:
  ∀ e.
    (∃ e1.
      e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]]) ∧
      isPureExp (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]]) ∧
      isFpArithExp (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]]) ∧
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
      isFpArithExp (App (FP_uop FP_Neg) [e1]) ∧
      rewriteFPexp [fp_neg_times_minus_one] e = (App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 13830554455654793216w)]])) ∨
    (rewriteFPexp [fp_neg_times_minus_one] e = e)
Proof
  prove_cases_reverse_thm fp_neg_times_minus_one_def fp_times_minus_one_neg_def
QED

Theorem fp_times_two_to_add_cases:
  ∀ e.
    (∃ e1 e2.
       e = App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 4611686018427387904w)]] ∧
       isPureExp e ∧ isFpArithExp e ∧
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
       isPureExp e ∧ isFpArithExp e ∧
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
      isPureExp e ∧ isFpArithExp e ∧
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
      isPureExp e ∧ isFpArithExp e ∧
      rewriteFPexp [fp_same_sub] e = App FpFromWord [Lit (Word64 0w)]) ∨
    (rewriteFPexp [fp_same_sub] e = e)
Proof
  prove_cases_thm fp_same_sub_def
QED

Theorem fp_distribute_gen_cases:
∀ e fpBopInner fpBopOuter.
    (∃ e1 e2 e3.
      e = App (FP_bop fpBopOuter) [ App (FP_bop fpBopInner) [e1; e2]; App (FP_bop fpBopInner) [e3; e2]] ∧
      isPureExp e ∧ isFpArithExp e ∧
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

Theorem evaluate_rewrite_hoisting:
  (∀ e1 (st1:'a semanticPrimitives$state) env st2 v fp.
     st1.fp_state.canOpt = FPScope Opt ∧
    evaluate st1 env [e1] = (st2, Rval [v]) ∧
    fp_translate v = SOME (FP_WordTree fp) ∧
    isPureExp e1 ∧ isFpArithExp e1 ⇒
    ∃ vUnOpt fpUnOpt sched choices.
      evaluate (st1 with fp_state:= st1.fp_state with opts:= λ x. []) env [e1] =
      (st2 with fp_state := st2.fp_state with <| opts := λ x. []; choices := choices |>, Rval [vUnOpt]) ∧
      fp_translate vUnOpt = SOME (FP_WordTree fpUnOpt) ∧
      do_fprw (Rval (FP_WordTree fpUnOpt)) sched st1.fp_state.rws = SOME (Rval (FP_WordTree fp))) ∧
  (∀ es env fps.
    isPureExpList es ∧ isFpArithExpList es ⇒
    ∀ (st1:'a semanticPrimitives$state) st2 e v fp.
      MEM e es ⇒
      st1.fp_state.canOpt = FPScope Opt ∧
      evaluate st1 env [e] = (st2, Rval [v]) ∧
      fp_translate v = SOME (FP_WordTree fp)⇒
      ∃ vUnOpt fpUnOpt sched choices.
        evaluate (st1 with fp_state:= st1.fp_state with opts:= λ x. []) env [e] =
        (st2 with fp_state := st2.fp_state with <| opts := λ x. []; choices := choices |>, Rval [vUnOpt]) ∧
        fp_translate vUnOpt = SOME (FP_WordTree fpUnOpt) ∧
        do_fprw (Rval (FP_WordTree fpUnOpt)) sched st1.fp_state.rws = SOME (Rval (FP_WordTree fp)))
Proof
  ho_match_mp_tac isFpArithExp_ind \\ rpt strip_tac
  \\ TRY (qpat_x_assum `isPureExp _` mp_tac \\ simp[isPureExp_def])
  \\ TRY (qpat_x_assum `isFpArithExp _` mp_tac \\ simp[isFpArithExp_def])
  >- (
    fs[evaluate_def, CaseEq"option"] \\ rveq
    \\ fs state_eqs \\ qexistsl_tac [‘[]’] \\ fs[do_fprw_def, rwAllWordTree_def])
  >- (
    fs[evaluate_def, CaseEq"option", astTheory.getOpClass_def,
       do_app_def]
    \\ rveq \\ rpt strip_tac
    \\ fs state_eqs \\ qexistsl_tac [‘[]’] \\ fs[do_fprw_def, rwAllWordTree_def])
  >- (
  fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rpt strip_tac \\ rveq
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[evaluate_def, CaseEq"option",
          astTheory.getOpClass_def, do_app_def, CaseEq"result"]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ strip_tac \\ fs[CaseEq"option", CaseEq"prod", CaseEq"v", astTheory.isFpBool_def]
  \\ rveq
  \\ rename1 ‘evaluate st1 env [_] = (st2, _)’
  \\ ‘st2.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[PULL_EXISTS]
  \\ first_x_assum  (fn ith => qpat_x_assum `evaluate _ _ _ = _`
                      (fn th => mp_then Any mp_tac ith th))
  \\ rpt (disch_then drule) \\ strip_tac
  \\ fs ([shift_fp_opts_def] @ state_eqs)
  \\ rveq
  \\ qexists_tac ‘FP_WordTree (fp_uop e1 fpUnOpt)’
  \\ qexists_tac ‘fp_uop e1 fpUnOpt’ \\ fs[fp_translate_def, GSYM PULL_EXISTS]
  \\ fs[do_fprw_def, CaseEq "option"]
  \\ first_x_assum $ mp_then Any assume_tac rwAllWordTree_comp_unop
  \\ first_x_assum $ qspec_then ‘e1’ strip_assume_tac
  \\ qexists_tac ‘insts_new ++ (case do_fprw
                                 (Rval (FP_WordTree (fp_uop e1 w1))) (st2.fp_state.opts 0)
                                 st2.fp_state.rws of
                            | NONE => []
                            | SOME _ => (st2.fp_state.opts 0))’(* TODO *)
  \\ qexists_tac ‘st2 with
         fp_state :=
           st2.fp_state with <|opts := (λx. []); choices := choices|>’
  \\ fs state_eqs
  \\ fs[do_fprw_def, rwAllWordTree_def]
  \\ Cases_on ‘rwAllWordTree (st2.fp_state.opts 0) st2.fp_state.rws (fp_uop e1 w1)’
  \\ fs[] \\ rveq \\ fs[fp_uop_def, fp_translate_def]
  \\ irule rwAllWordTree_chaining_exact
  \\ asm_exists_tac \\ fs[] \\ rveq  \\ fs[rwAllWordTree_def]
  \\ fp_inv_tac)
  >- (
  fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rpt strip_tac \\ rveq
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[evaluate_def, CaseEq"option",
          astTheory.getOpClass_def, do_app_def, CaseEq"result", evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ strip_tac \\ fs[CaseEq"option", CaseEq"prod", CaseEq"v", astTheory.isFpBool_def]
  \\ rveq
  \\ rename1 ‘evaluate st1 env [e2] = (st2, _)’
  \\ rename1 ‘evaluate st2 env [e1] = (st3, _)’
  \\ ‘st2.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ ‘st3.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[]
  \\ first_assum  (fn ith => qpat_x_assum `evaluate _ _ _ = _`
                      (fn th => mp_then Any mp_tac ith th))
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘w1’ mp_tac) \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ first_assum  (fn ith => qpat_x_assum `evaluate _ _ [e2] = _`
                      (fn th => mp_then Any mp_tac ith th))
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘w2’ mp_tac) \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ fs ([shift_fp_opts_def] @ state_eqs)
  \\ fs[PULL_EXISTS]
  \\ qexists_tac ‘FP_WordTree (fp_bop v1 fpUnOpt fpUnOpt')’
  \\ qexists_tac ‘fp_bop v1 fpUnOpt fpUnOpt'’
  \\ fs[fp_translate_def, do_fprw_def, CaseEq"option"]
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ disch_then (qspecl_then [‘v1’, ‘fpUnOpt'’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_e2 _ (Fp_bop v1 _ _) = _’
  \\ strip_tac
  \\ disch_then (qspecl_then [‘v1’, ‘w1’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_e1 _ (Fp_bop v1 _ _) = _’
  \\ strip_tac \\ rveq \\ gs[]
  \\ rveq \\ gs[]
  \\ qexists_tac ‘sched_e2 ++ sched_e1 ++
                  (case rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws
                                      (fp_bop v1 w1 w2) of
                   | NONE => []
                   | SOME _ => (st3.fp_state.opts 0))’
  \\ qpat_x_assum `evaluate _ _ [e1] = _` $ mp_then Any mp_tac $ CONJUNCT1 evaluate_add_choices
  \\ disch_then (qspec_then ‘choices'’ assume_tac)
  \\ fs state_eqs
  \\ qexists_tac ‘choices + choices' - st2.fp_state.choices +1’ (* TODO *)
  \\ qexists_tac ‘st2 with
         fp_state :=
           st2.fp_state with <|opts := (λx. []); choices := choices'|>’
  \\ rpt conj_tac
  \\ fs state_eqs
  \\ fs[rwAllWordTree_def]
  \\ irule rwAllWordTree_chaining_exact
  \\ qexists_tac ‘Fp_bop v1 w1 w2’ \\ conj_tac
  \\ TRY (irule rwAllWordTree_chaining_exact \\ fs[fp_bop_def]
          \\ fp_inv_tac \\ NO_TAC)
  \\ TOP_CASE_TAC \\ fs[fp_bop_def, rwAllWordTree_def, fp_translate_def]
  \\ rveq \\ fs[fp_translate_def] \\ fp_inv_tac)
  >- (
  fs[quantHeuristicsTheory.LENGTH_TO_EXISTS_CONS] \\ rpt strip_tac \\ rveq
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, evaluate_def, CaseEq"option",
          astTheory.getOpClass_def, do_app_def, CaseEq"result", evaluate_case_case]
  \\ ntac 6 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ simp[SimpL “$==>”, CaseEq"option", CaseEq"prod", CaseEq"v", astTheory.isFpBool_def]
  \\ rpt strip_tac
  \\ rveq
  \\ rename [‘evaluate st1 env [e3] = (st2, _)’,
             ‘evaluate st2 env [e2] = (st3, _)’,
             ‘evaluate st3 env [e1] = (st4, _)’]
  \\ ‘st2.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ ‘st3.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ ‘st4.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[]
  \\ first_assum  (fn ith => qpat_x_assum `evaluate _ _ _ = _`
                      (fn th => mp_then Any mp_tac ith th))
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘w1’ mp_tac) \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ first_assum  (fn ith => qpat_x_assum `evaluate _ _ [e2] = _`
                      (fn th => mp_then Any mp_tac ith th))
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘w2’ mp_tac) \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ first_assum  (fn ith => qpat_x_assum `evaluate _ _ [e3] = _`
                      (fn th => mp_then Any mp_tac ith th))
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then ‘w3’ mp_tac) \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ fs ([shift_fp_opts_def] @ state_eqs)
  \\ fs[PULL_EXISTS]
  \\ qexists_tac ‘FP_WordTree (fp_top v2 fpUnOpt fpUnOpt' fpUnOpt'')’
  \\ qexists_tac ‘fp_top v2 fpUnOpt fpUnOpt' fpUnOpt''’
  \\ rpt (qpat_x_assum ‘do_fprw _ _ _ = _’ mp_tac)
  \\ simp[fp_translate_def, do_fprw_def, CaseEq"option"] \\ rveq
  \\ rpt strip_tac
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_terop_r
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_terop_c
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_terop_l
  \\ disch_then $ qspecl_then [‘fpUnOpt'’, ‘fpUnOpt''’, ‘v2’]
                $ qx_choose_then ‘sched1’ assume_tac
  \\ disch_then $ qspecl_then [‘w1’, ‘fpUnOpt''’, ‘v2’]
                $ qx_choose_then ‘sched2’ assume_tac
  \\ disch_then $ qspecl_then [‘w1’, ‘w2’, ‘v2’]
                $ qx_choose_then ‘sched3’ assume_tac
  \\ rveq \\ gs[]
  \\ qexists_tac ‘sched1 ++ sched2 ++ sched3 ++
                  (case do_fprw (Rval (FP_WordTree (fp_top v2 w1 w2 w3)))
             (st4.fp_state.opts 0) st4.fp_state.rws of
                   | NONE => []
                   | SOME _ => (st4.fp_state.opts 0))’
  \\ simp[evaluate_def, astTheory.getOpClass_def, do_app_def]
  \\ qpat_x_assum `evaluate _ _ [e2] = _` $ mp_then Any mp_tac $ CONJUNCT1 evaluate_add_choices
  \\ disch_then (qspec_then ‘choices''’ assume_tac)
  \\ fs state_eqs
  \\ qpat_x_assum `evaluate _ _ [e1] = _` $ mp_then Any mp_tac $ CONJUNCT1 evaluate_add_choices
  \\ disch_then (qspec_then ‘choices' + choices'' - st2.fp_state.choices’ assume_tac)
  \\ fs state_eqs \\ rewrite_tac [CONJ_ASSOC]
  \\ conj_tac
  >- (conj_tac
      \\ fs[shift_fp_opts_def, do_fprw_def, astTheory.isFpBool_def, rwAllWordTree_def])
  \\ irule rwAllWordTree_chaining_exact
  \\ qexists_tac ‘Fp_top v2 w1 w2 w3’ \\ conj_tac
  >- (irule rwAllWordTree_chaining_exact
      \\ qexists_tac ‘fp_top v2 w1 w2 fpUnOpt''’ \\ fs[fp_top_def]
      \\ irule rwAllWordTree_chaining_exact
      \\ qexists_tac ‘fp_top v2 w1 fpUnOpt' fpUnOpt''’ \\ fs[fp_top_def]
      \\ ‘st1.fp_state.rws = st3.fp_state.rws ∧ st2.fp_state.rws = st1.fp_state.rws’
         by fp_inv_tac
      \\ gs[])
  \\ TOP_CASE_TAC \\ fs[fp_top_def, rwAllWordTree_def, fp_translate_def]
  \\ rveq \\ fs[do_fprw_def, CaseEq"option"] \\ rveq
  \\ fs[fp_translate_def] \\ rveq \\ fp_inv_tac)
  >- (fs[])
  \\ fs[]
  >- (rveq \\ res_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ fs[isFpArithExp_def, isPureExp_def]
QED

(**
  Optimisation simulation proofs
  In combination with the automation from icing_optimisationsLib and the
  correctness proofs from source_to_source2Proofs, we automatically
  construct backwards simulation proofs for a run of the optimiser
**)

Theorem fp_times_zero_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_zero] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_times_zero_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_times_zero]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def, do_app_def]
  \\ rpt strip_tac \\ rveq
  \\ simp[evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def, do_app_def, evaluate_case_case]
  \\ ‘isFpArithExp e1’ by (gs[isFpArithExp_def])
  \\ drule (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates)
  \\ disch_then $ qspecl_then [‘env’, ‘st1’] mp_tac
  \\ impl_tac
  >- gs[freeVars_fp_bound_def]
  \\ rpt strip_tac \\ rveq
  \\ ‘st2.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ ‘st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac
        \\ fs[state_component_equality, shift_fp_opts_def, CaseEq"option", CaseEq"v"])
  \\ qpat_x_assum ‘evaluate _ _ [e1] = _’ $ mp_then Any mp_tac isPureExp_evaluate_change_oracle
  \\ disch_then $ qspecl_then [‘fp_times_zero’, ‘st1’,
                               ‘λ x.
                                 if (x = 0)
                                 then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)]
                                 else []’] mp_tac
  \\ impl_tac
  >- (rpt conj_tac \\ gs[isPureExp_def])
  \\ rpt strip_tac
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1N _ [e1] = _’
  \\ strip_tac
  \\ qexists_tac ‘oracle’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ [e1]’
  \\ ‘st1N = st1Upd’
     by (unabbrev_all_tac \\ gs[state_component_equality, fpState_component_equality])
  \\ rveq
  \\ gs[fp_translate_def, shift_fp_opts_def, state_component_equality,
        fpState_component_equality, do_fprw_def]
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL “rwFp_pathWordTree fp_times_zero Here
                 (fp_bop FP_Mul fp (Fp_const 0w))”,
          instWordTree_def, substLookup_def]
QED

Theorem fp_same_sub_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_same_sub] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_same_sub_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_same_sub]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ pop_assum $ gs o single
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[SimpL “$==>”, evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def, do_app_def]
  \\ rpt strip_tac \\ rveq
  \\ simp[evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def, do_app_def, evaluate_case_case]
  \\ ‘isFpArithExp e1’ by (gs[isFpArithExp_def])
  \\ drule (CONJUNCT1 icing_rewriterProofsTheory.isFpArithExp_matched_evaluates)
  \\ disch_then $ qspecl_then [‘env’, ‘st1’] mp_tac
  \\ impl_tac
  >- gs[freeVars_fp_bound_def]
  \\ rpt strip_tac \\ rveq
  \\ ‘st2.fp_state.canOpt = FPScope Opt ∧ ~st2.fp_state.real_sem’ by fp_inv_tac
  \\ ‘st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac
        \\ fs[state_component_equality, shift_fp_opts_def, CaseEq"option", CaseEq"v"])
  \\ qpat_assum `evaluate _ _ [e1] = _` $ mp_then Any mp_tac isPureExp_evaluate_change_oracle
  \\ disch_then $ qspecl_then [‘fp_same_sub’, ‘st1’] mp_tac
  \\ gs[GSYM PULL_FORALL]
  \\ impl_tac >- gs[isPureExp_def]
  \\ strip_tac
  \\ first_assum $ qspec_then ‘λ x.
                                if (x = 0)
                                then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)]
                                else []’ strip_assume_tac
  \\ first_x_assum $ qspec_then ‘oracle’ strip_assume_tac
  \\ gs[state_component_equality, fpState_component_equality]
  \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1N _ _ = _’ \\ strip_tac
  \\ qexists_tac ‘st1N.fp_state.opts’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _’
  \\ ‘st1N = st1Upd’
     by (unabbrev_all_tac \\ gs[state_component_equality, fpState_component_equality])
  \\ rveq \\ gs[]
  \\ qpat_x_assum ‘evaluate st1N _ _ = _’ kall_tac
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ $ mp_then Any mp_tac $ CONJUNCT1 evaluate_add_choices
  \\ disch_then $ qspec_then ‘st1.fp_state.choices + (st2.fp_state.choices - st1.fp_state.choices)’ mp_tac
  \\ gs[state_component_equality, fpState_component_equality]
  \\ strip_tac
  \\ gs[fp_translate_def, shift_fp_opts_def, state_component_equality, fpState_component_equality]
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL “rwFp_pathWordTree fp_same_sub Here
                 (fp_bop FP_Sub fp fp)”,
          instWordTree_def, substLookup_def]
QED

Theorem fp_add_sub_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_add_sub] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ qspecl_then [`e`] strip_assume_tac
                 (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_sub_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_add_sub]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` (mp_tac o SIMP_RULE std_ss [evaluate_def])
  \\ simp[REVERSE_DEF, astTheory.isFpBool_def, Once evaluate_cons,
          evaluate_case_case]
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
  \\ qpat_assum `evaluate _ _ [e2] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_add_sub’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices + (st3.fp_state.choices - st2.fp_state.choices)’,
       ‘λ x. if (x = 0)
        then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
        (case do_fprw (Rval (FP_WordTree (fp_bop FP_Sub w1 w2)))
         (st3.fp_state.opts 0) st3.fp_state.rws of
         | NONE => [] | SOME r_opt => st3.fp_state.opts x)
        else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_add_sub’,
       ‘st1’, ‘λ x . if x = 0 then [] else oracle (x-1)’] mp_tac)
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
  \\ simp[Once do_fprw_def, rwAllWordTree_def]
  \\ qpat_x_assum `evaluate _ _ [e2] = _` $ mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
  \\ disch_then $ qspec_then ‘st1.fp_state.choices + (st2.fp_state.choices - st1.fp_state.choices) + 1’ assume_tac
  \\ gs state_eqs \\ pop_assum mp_tac
  \\  qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’ \\ rpt strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1New _ _’
  \\ ‘st1Upd = st1New’ by (unabbrev_all_tac \\ gs (FUN_EQ_THM :: state_eqs))
  \\ pop_assum $ gs o single
  \\ gs (fp_translate_def :: state_eqs) \\ unabbrev_all_tac
  \\ rpt conj_tac
  >- fp_inv_tac
  >- fp_inv_tac
  \\ qpat_x_assum `_ = Rval _` (fs o single o GSYM)
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree (fp_add_sub) Here (fp_bop FP_Add w1 (fp_uop FP_Neg w2))``,
        instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws (fp_bop FP_Sub w1 w2)`
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_add_sub]` assume_tac)
  \\ `st3.fp_state.rws = st1.fp_state.rws` by fp_inv_tac
  \\ fs[]
QED

Theorem fp_add_sub_correct_unfold =
        REWRITE_RULE [fp_add_sub_def, reverse_tuple_def, fp_sub_add_def] fp_add_sub_correct;

Theorem fp_neg_times_minus_one_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_neg_times_minus_one] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_neg_times_minus_one_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_neg_times_minus_one]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ gs[]
  \\ imp_res_tac evaluate_sing
  \\ pop_assum (fs o single)
  \\ ‘∃ fp. v = FP_WordTree fp’
     by (fs[freeVars_fp_bound_def]
         \\ mp_tac (GEN_ALL icing_rewriterProofsTheory.rewriteFPexp_returns_fp)
         \\ disch_then $ qspecl_then [‘st1’, ‘st2’, ‘e’, ‘FST(fp_neg_times_minus_one)’,
                                      ‘SND(fp_neg_times_minus_one)’, ‘env’,
                                      ‘App (FP_bop FP_Mul) [e1; App FpFromWord [Lit (Word64 0xBFF0000000000000w)]]’,
                                      ‘v’]
                       mp_tac
         \\ impl_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (simp[Once evaluate_def, astTheory.isFpBool_def, astTheory.getOpClass_def, do_app_def])
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq
  \\ fs[do_app_def] \\ Cases_on ‘fp_translate v’ \\ gs[]
  \\ Cases_on ‘x’ \\ gs[fp_translate_def]
  \\ ‘q.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[] \\ rpt strip_tac \\ rveq
  \\ rename1 ‘evaluate _ env [e1] = (st2, Rval [v])’
  \\ ‘~ st2.fp_state.real_sem’ by fp_inv_tac
  \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by fp_inv_tac
  \\ ‘st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac
        \\ fs[state_component_equality, shift_fp_opts_def, CaseEq"option", CaseEq"v"])
  \\ ntac 2(simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
                 Once evaluate_def, Once evaluate_cons,
                 evaluate_case_case, do_app_def])
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_neg_times_minus_one’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices’,
       ‘λ x. if (x = 0)
        then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
             (case do_fprw
               (Rval
                (FP_WordTree (fp_bop FP_Mul f (Fp_const 0xBFF0000000000000w))))
             (st2.fp_state.opts 0) st2.fp_state.rws of
              | NONE => [] | SOME r_opt => st2.fp_state.opts x)
        else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac \\ gs state_eqs
  \\ qexists_tac ‘oracle’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ gs[shift_fp_opts_def]
  \\ simp state_eqs
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_neg_times_minus_one Here
                 (fp_uop FP_Neg f)``,
          instWordTree_def, substLookup_def]
  \\ fs[do_fprw_def, CaseEq"option"] \\ rveq
  \\ gs[rwAllWordTree_def, fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_neg_times_minus_one]` assume_tac)
  \\ gs[]
QED

Theorem fp_neg_times_minus_one_correct_unfold =
        REWRITE_RULE [fp_neg_times_minus_one_def, reverse_tuple_def,
                      fp_times_minus_one_neg_def] fp_neg_times_minus_one_correct;

Theorem fp_distribute_gen_correct:
  ∀ fpBop1 fpBop2 st1 st2 env e r.
   is_rewriteFPexp_correct [fp_distribute_gen fpBop1 fpBop2] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ reverse (qspecl_then [‘e’, ‘fpBop1’, ‘fpBop2’] strip_assume_tac fp_distribute_gen_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_distribute_gen fpBop1 fpBop2]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq \\ gs[]
  \\ qpat_x_assum ‘evaluate _ _ _ = (_, _)’ mp_tac
  \\ simp[SimpL “$==>”, evaluate_def, REVERSE_DEF, astTheory.getOpClass_def,
          astTheory.isFpBool_def, Once evaluate_cons, evaluate_case_case,
          CaseEq"result", CaseEq"prod"]
  \\ rpt strip_tac \\ rveq \\ gs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[] \\ rveq
  \\ ntac 2 (qpat_x_assum ‘case do_app _ _ _ of |_ => _’mp_tac)
  \\ simp[do_app_def, Once (CaseEq"option"), CaseEq"prod"]
  \\ ntac 2 (simp [Once (CaseEq"option"), CaseEq"v"])
  \\ strip_tac \\ rveq \\ gs[]
  \\ ntac 3 (simp [Once (CaseEq"option"), CaseEq"v", CaseEq"prod"])
  \\ strip_tac \\ rveq \\ gs (shift_fp_opts_def :: state_eqs)
  \\ rename [‘evaluate st1 env [e2] = (st2, Rval [v2])’,
             ‘evaluate st2 env [e3] = (st3, Rval [v3])’,
             ‘evaluate st3 env [e1] = (st4, Rval [v1])’]
  \\ ‘st4.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ ‘st4.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ ‘~ st4.fp_state.real_sem’ by fp_inv_tac
  \\ gs[]
  \\ ‘st2 = st1 with fp_state := st2.fp_state ∧
      st3 = st1 with fp_state := st3.fp_state ∧
      st4 = st1 with fp_state := st4.fp_state’ by (
    imp_res_tac isPureExp_same_ffi
    \\ fs[isPureExp_def]
    \\ res_tac
    \\ fs[state_component_equality])
  \\ ntac 3 (qpat_x_assum ‘evaluate _ _ _ = _’ $ mp_then Any mp_tac (CONJUNCT1 evaluate_rewrite_hoisting))
  \\ rename1 ‘fp_translate v3 = SOME (FP_WordTree w3)’
  \\ rename1 ‘fp_translate v2 = SOME (FP_WordTree w2)’
  \\ rename1 ‘fp_translate v1 = SOME (FP_WordTree w1)’
  \\ disch_then $ qspec_then ‘w2’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ disch_then $ qspec_then ‘w3’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ disch_then $ qspec_then ‘w1’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  (* Construct a new rewrite schedule that we apply at the end *)
  \\ rveq \\ gs[]
  \\ rename1 ‘do_fprw (Rval (FP_WordTree fpUnOpt1)) _ st3.fp_state.rws = SOME (Rval (FP_WordTree w1))’
  \\ rename1 ‘do_fprw (Rval (FP_WordTree fpUnOpt2)) _ _ = SOME (Rval (FP_WordTree w2))’
  \\ rename1 ‘do_fprw (Rval (FP_WordTree fpUnOpt3)) _ _ = SOME (Rval (FP_WordTree w3))’
  \\ rpt (qpat_x_assum ‘do_fprw _ _ _ = SOME _’ mp_tac)
  \\ simp[do_fprw_def, CaseEq"option"] \\ rpt strip_tac
  \\ qpat_x_assum `rwAllWordTree _ _ fpUnOpt1 = _` $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ disch_then (qspecl_then [‘fpBop2’, ‘fpUnOpt3’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched1 _ _ = _’
  \\ qpat_x_assum `rwAllWordTree _ _ fpUnOpt3 = _` $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ disch_then (qspecl_then [‘fpBop2’, ‘w1’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched3 _ _ = _’
  \\ rpt strip_tac
  \\ ‘rwAllWordTree (sched1 ++ sched3 ++ case do_fprw (Rval (FP_WordTree (fp_bop fpBop2 w1 w3)))
                                                      (st4.fp_state.opts 0) st1.fp_state.rws of
                                         | NONE => []
                    | SOME _ => st4.fp_state.opts 0) st1.fp_state.rws (Fp_bop fpBop2 fpUnOpt1 fpUnOpt3) =SOME w1'’
     by (irule rwAllWordTree_chaining_exact
         \\ qexists_tac ‘Fp_bop fpBop2 w1 w3’ \\ conj_tac
         >- (irule rwAllWordTree_chaining_exact
             \\ ‘st1.fp_state.rws = st2.fp_state.rws ∧
                 st1.fp_state.rws = st3.fp_state.rws’
               by fp_inv_tac
             \\ qexists_tac ‘Fp_bop fpBop2 w1 fpUnOpt3’ \\ gs[])
         \\ fs[do_fprw_def, CaseEq"option", rwAllWordTree_def] \\ rveq
         \\ fs[fp_translate_def] \\ rveq \\ fs[fp_bop_def])
  \\ pop_assum $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ disch_then $ qspecl_then [‘fpBop1’, ‘fpUnOpt2’] mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_comb _ _’
  \\ strip_tac
  \\ qpat_x_assum ‘rwAllWordTree _ _ fpUnOpt2 = _’ $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ disch_then $ qspecl_then [‘fpBop1’, ‘w1'’] mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched2 _ _’ \\ strip_tac
  \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ (fn th => mp_then Any mp_tac (CONJUNCT1 evaluate_fp_opts_inv) th \\ mp_tac th))
  \\ simp state_eqs \\ rpt strip_tac
  \\ simp[evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def,
          Once evaluate_cons, evaluate_case_case]
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_distribute_gen fpBop1 fpBop2’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices’,
       ‘λ x. if (x = 1) then
                ([RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++ sched_comb ++ sched2 ++
             case do_fprw (Rval (FP_WordTree (fp_bop fpBop1 w1' w2)))
                          (st4.fp_state.opts 1) st4.fp_state.rws of
             | NONE => []
             | SOME _ => st4.fp_state.opts 1)
             else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e2] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ simp[isPureExp_def]
  \\ disch_then (fn th =>
                   mp_tac th
     \\ qspecl_then [
       ‘fp_distribute_gen fpBop1 fpBop2’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices’,
       ‘oracle’] mp_tac th)
  \\ impl_tac >- fs state_eqs
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e3] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ simp[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_distribute_gen fpBop1 fpBop2’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices’,
       ‘λ x. if x = 0 then [] else oracle' (x-1)’] mp_tac)
  \\ impl_tac >- fs state_eqs
  \\ strip_tac
  \\ disch_then (
     qspecl_then [
       ‘fp_distribute_gen fpBop1 fpBop2’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices’,
       ‘oracle''’] mp_tac)
  \\ impl_tac >- fs state_eqs
  \\ strip_tac \\ gs state_eqs
  \\ qexists_tac ‘oracle'3'’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ gs[]
  \\ pop_assum kall_tac (* evaluate e2 not needed anymore *)
  \\ pop_assum $ mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘st1.fp_state.choices + (choices - st1.fp_state.choices)’ assume_tac)
  \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by fs[]
  \\ gs[do_app_def, do_fprw_def, rwAllWordTree_def, shift_fp_opts_def]
  \\ qpat_x_assum ‘evaluate _ _ [e3] = _’ kall_tac
  \\ qmatch_goalsub_abbrev_tac ‘st1.fp_state with <| rws := _; opts := new_oracle;
                                                     choices := new_choices |>’
  \\ ‘new_oracle = oracle'’ by (unabbrev_all_tac \\ fs[FUN_EQ_THM])
  \\ qpat_x_assum ‘evaluate _ _ [e2] = _’ $ mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘new_choices’ assume_tac)
  \\ pop_assum mp_tac \\ qmatch_goalsub_abbrev_tac ‘evaluate st1N _ _ = _’
  \\ strip_tac
  \\ ‘st1N with <| refs := st1.refs; ffi := st1.ffi |> = st1N’ by (unabbrev_all_tac \\ simp state_eqs)
  \\ gs[]
  \\ qpat_x_assum ‘evaluate _ _ [e2] = _’ kall_tac
  \\ qpat_x_assum ‘evaluate _ _ [e1] = _’ $ mp_then Any (qspec_then ‘choices + new_choices - st1.fp_state.choices’ mp_tac)
                  (CONJUNCT1 evaluate_add_choices)
  \\ simp state_eqs
  \\ ‘st2.fp_state.rws = st3.fp_state.rws’ by fs[]
  \\ simp[]
  \\ disch_then kall_tac \\ simp ([Once rwAllWordTree_def, fp_translate_def, fp_bop_def] @ state_eqs)
  \\ rveq \\ qpat_x_assum ‘_ = Rval v'5'’ mp_tac
  \\ simp[CaseEq"option"] \\ strip_tac \\ rveq
  \\ simp[rwAllWordTree_def, nth_len, EVAL “rwFp_pathWordTree (fp_distribute_gen fpBop1 fpBop2) Here
             (Fp_bop fpBop2 (Fp_bop fpBop1 fpUnOpt1 fpUnOpt2)
                (Fp_bop fpBop1 fpUnOpt3 fpUnOpt2))”, instWordTree_def, substLookup_def]
  \\ fs[fp_bop_def]
  >- (DISJ2_TAC
      \\ irule rwAllWordTree_chaining_exact
      \\ qexists_tac ‘Fp_bop fpBop1 w1' fpUnOpt2’ \\ gs[]
      \\ imp_res_tac rwAllWordTree_append_opt
      \\ rpt (first_x_assum (qspec_then `[fp_distribute_gen fpBop1 fpBop2]` assume_tac))
      \\ gs[])
  \\ DISJ2_TAC
  \\ irule rwAllWordTree_chaining_exact
  \\ qexists_tac ‘Fp_bop fpBop1 w1' w2’ \\ conj_tac
  \\ TRY (irule rwAllWordTree_chaining_exact
          \\ qexists_tac ‘Fp_bop fpBop1 w1' fpUnOpt2’ \\ gs[])
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ rpt (first_x_assum (qspec_then `[fp_distribute_gen fpBop1 fpBop2]` assume_tac))
  \\ gs[]
QED

Theorem fp_distribute_gen_correct_unfold =
        REWRITE_RULE [fp_distribute_gen_def] fp_distribute_gen_correct;
Theorem fp_distribute_gen_correct_unfold_add =
        REWRITE_RULE [icing_optimisationsTheory.fp_distribute_gen_def]
                     (Q.SPECL [‘FP_Mul’, ‘FP_Add’] fp_distribute_gen_correct);

Theorem fp_times_two_to_add_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_two_to_add] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_times_two_to_add_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_times_two_to_add]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ imp_res_tac evaluate_sing
  \\ pop_assum (fs o single)
  \\ ‘∃ fp. v = FP_WordTree fp’
     by (fs[freeVars_fp_bound_def]
         \\ mp_tac (GEN_ALL icing_rewriterProofsTheory.rewriteFPexp_returns_fp)
         \\ disch_then $ qspecl_then [‘st1’, ‘st2’, ‘e’, ‘FST(fp_times_two_to_add)’,
                                      ‘SND(fp_times_two_to_add)’, ‘env’, ‘App (FP_bop FP_Add) [e1; e1]’, ‘v’]
                       mp_tac
         \\ impl_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ qpat_x_assum `_ = App _ _` (fs o single)
  \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq
  \\ fs[do_app_def] \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ ‘q.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[] \\ rpt strip_tac
  \\ gs[CaseEq"prod"] \\ rveq
  \\ rename [‘evaluate st1 env [e1] = (st2, Rval [v])’,
             ‘evaluate st2 env [e1] = (st3, Rval v2)’]
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[REVERSE_DEF, APPEND]
  \\ rveq
  \\ rename [‘evaluate st1 env [e1] = (st2, Rval [v1])’,
             ‘evaluate st2 env [e1] = (st3, Rval [v2])’]
  \\ ‘st3 = st1 with fp_state := st3.fp_state ∧
      st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac
        \\ fs[state_component_equality, shift_fp_opts_def, CaseEq"option", CaseEq"v"])
  \\ ‘st3.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[]
  \\ Cases_on ‘fp_translate v1’ \\ gs[CaseEq"v"] \\ rveq
  \\ Cases_on ‘fp_translate v2’ \\ gs[CaseEq"v"] \\ rveq
  \\ ntac 2 (qpat_x_assum ‘evaluate _ _ [e1] = _’ $ mp_then Any mp_tac (CONJUNCT1 evaluate_rewrite_hoisting))
  \\ disch_then $ qspec_then ‘w2’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ disch_then $ qspec_then ‘w1’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ rpt $ qpat_x_assum ‘evaluate _ _ [e1] = _’ mp_tac
  \\ qpat_assum ‘st3 = _’ (once_rewrite_tac o single )
  \\ qpat_assum ‘st2 = _’ (once_rewrite_tac o single)
  \\ simp state_eqs \\ rpt strip_tac
  \\ ‘st2.fp_state.rws = st1.fp_state.rws’ by (fp_inv_tac)
  \\ ‘vUnOpt = vUnOpt'’
     by (rpt $ qpat_x_assum ‘evaluate _ _ [e1] = _’ mp_tac
         \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’
         \\ strip_tac
         \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd2 _ _ = _’
         \\ strip_tac
         \\ pop_assum $ mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
         \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
         \\ ‘st1Upd2 with fp_state := st1Upd2.fp_state with choices :=
             st1.fp_state.choices = st1Upd’
            by (unabbrev_all_tac \\ fs state_eqs
                \\ fp_inv_tac \\ fs[FUN_EQ_THM])
         \\ gs[])
  \\ rveq
  \\ ntac 2 $ qpat_x_assum ‘do_fprw _ _ _ = _’ mp_tac
  \\ simp[do_fprw_def, CaseEq"option"]
  \\ rpt strip_tac
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ disch_then (qspecl_then [‘FP_Add’, ‘w1’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched2 _ _ = SOME _’
  \\ strip_tac
  \\ disch_then (qspecl_then [‘FP_Add’, ‘fpUnOpt’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched1 _ _ = SOME _’
  \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_times_two_to_add’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices’,
       ‘λ x. if (x = 0)
             then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++ sched1 ++ sched2 ++
             case do_fprw (Rval (FP_WordTree (fp_bop FP_Add w1 w2)))
                          (st3.fp_state.opts 0) st3.fp_state.rws of
             | NONE => []
             | SOME _ => st3.fp_state.opts 0
             else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac \\ fs state_eqs
  \\ simp[evaluate_def, astTheory.isFpBool_def, astTheory.getOpClass_def,
         semanticPrimitivesTheory.do_app_def]
  \\ qexists_tac ‘oracle’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ pop_assum mp_tac \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’
  \\ strip_tac
  \\ ‘st1Upd = st1Upd with <| refs := st1.refs; ffi := st1.ffi|>’
    by (unabbrev_all_tac \\ fs state_eqs)
  \\ pop_assum (rewrite_tac o single o GSYM)
  \\ fs state_eqs
  \\ fs([fp_translate_def, shift_fp_opts_def] @ state_eqs) \\ rveq
  \\ rpt conj_tac
  >- (unabbrev_all_tac \\ fp_inv_tac)
  >- fp_inv_tac
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_times_two_to_add Here
                 (fp_bop FP_Mul fpUnOpt (Fp_const 0x4000000000000000w))``,
          instWordTree_def, substLookup_def]
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree (sched1 ++ sched2 ++ sched3) _’
  \\ ‘rwAllWordTree (sched1 ++ sched2 ++ sched3)
      (st1.fp_state.rws ++ [fp_times_two_to_add]) (Fp_bop FP_Add fpUnOpt fpUnOpt) =
      SOME fp’ suffices_by gs[]
  \\ irule rwAllWordTree_chaining_exact
  \\ qexists_tac ‘Fp_bop FP_Add w1 w2’ \\ conj_tac
  >- (irule rwAllWordTree_chaining_exact
      \\ qexists_tac ‘Fp_bop FP_Add w1 fpUnOpt’ \\ conj_tac
      \\ imp_res_tac rwAllWordTree_append_opt
      \\ rpt (first_x_assum (qspec_then `[fp_times_two_to_add]` assume_tac))
      \\ fs[])
  \\ unabbrev_all_tac \\ fs[do_fprw_def, CaseEq"option"] \\ rveq
  \\ gs[rwAllWordTree_def, fp_bop_def]
  \\ ‘st1.fp_state.rws = st3.fp_state.rws’ by fp_inv_tac
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_times_two_to_add]` assume_tac)
  \\ gs[]
QED

Theorem fp_times_two_to_add_correct_unfold =
        REWRITE_RULE [fp_times_two_to_add_def] fp_times_two_to_add_correct;

Theorem fp_times_three_to_add_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_three_to_add] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_times_three_to_add_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_times_three_to_add]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ imp_res_tac evaluate_sing
  \\ pop_assum (fs o single)
  \\ ‘∃ fp. v = FP_WordTree fp’
     by (fs[freeVars_fp_bound_def]
         \\ mp_tac (GEN_ALL icing_rewriterProofsTheory.rewriteFPexp_returns_fp)
         \\ disch_then $ qspecl_then [‘st1’, ‘st2’, ‘e’, ‘FST(fp_times_three_to_add)’,
                                      ‘SND(fp_times_three_to_add)’, ‘env’, ‘App (FP_bop FP_Add) [App (FP_bop FP_Add) [e1; e1]; e1]’, ‘v’]
                       mp_tac
         \\ impl_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ qpat_x_assum `_ = App _ _` (fs o single)
  \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq
  \\ fs[do_app_def]
  \\ rename [‘evaluate st1 env [e1] = (st2, Rval [v1])’,
             ‘evaluate st2 env [e1] = (st3, Rval [v2])’,
             ‘evaluate st3 env [e1] = (st4, Rval [v3])’]
  \\ ‘st4.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ ‘~ st4.fp_state.real_sem’ by fp_inv_tac
  \\ ‘st4 = st1 with fp_state := st4.fp_state ∧
      st3 = st1 with fp_state := st3.fp_state ∧
      st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac
        \\ fs[state_component_equality, shift_fp_opts_def, CaseEq"option", CaseEq"v"])
  \\ Cases_on ‘fp_translate v3’ \\ gs[] \\ Cases_on ‘x’ \\ gs[]
  \\ Cases_on ‘fp_translate v2’ \\ gs[] \\ Cases_on ‘x’ \\ gs[]
  \\ qmatch_goalsub_abbrev_tac ‘list_result opt_check1’
  \\ Cases_on ‘list_result opt_check1’ \\ fs[]
  \\ Cases_on ‘fp_translate v’ \\ gs[] \\ Cases_on ‘x’ \\ gs[]
  \\ Cases_on ‘fp_translate v1’ \\ gs[] \\ Cases_on ‘x’ \\ gs[]
  \\ gs[shift_fp_opts_def] \\ rpt strip_tac
  \\ ntac 3
          (qpat_x_assum ‘evaluate _ _ [e1] = _’ $
           mp_then Any mp_tac (CONJUNCT1 evaluate_rewrite_hoisting))
  \\ disch_then $ qspec_then ‘f'3'’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ disch_then $ qspec_then ‘f'’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ disch_then $ qspec_then ‘f’ mp_tac \\ impl_tac
  >- (fp_inv_tac \\ fs[isPureExp_def, isFpArithExp_def])
  \\ strip_tac
  \\ rpt $ qpat_x_assum ‘evaluate _ _ [e1] = _’ mp_tac
  \\ qpat_assum ‘st4 = _’ (once_rewrite_tac o single )
  \\ qpat_assum ‘st3 = _’ (once_rewrite_tac o single )
  \\ qpat_assum ‘st2 = _’ (once_rewrite_tac o single)
  \\ simp state_eqs \\ rpt strip_tac
  \\ ‘st4.fp_state.rws = st1.fp_state.rws ∧
      st3.fp_state.rws = st1.fp_state.rws ∧
      st2.fp_state.rws = st1.fp_state.rws’ by (fp_inv_tac)
  \\ ‘vUnOpt = vUnOpt' ∧ vUnOpt = vUnOpt''’
     by (rpt $ qpat_x_assum ‘evaluate _ _ [e1] = _’ mp_tac
         \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’
         \\ strip_tac
         \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd2 _ _ = _’
         \\ strip_tac
         \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd3 _ _ = _’
         \\ strip_tac
         \\ qpat_x_assum ‘evaluate st1Upd3 _ _ = _’ $
                         mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
         \\ qpat_x_assum ‘evaluate st1Upd2 _ _ = _’ $
                         mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
         \\ ntac 2 (disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac))
         \\ ‘st1Upd2 with fp_state := st1Upd2.fp_state with choices :=
             st1.fp_state.choices = st1Upd’
            by (unabbrev_all_tac \\ fs state_eqs
                \\ fp_inv_tac \\ fs[FUN_EQ_THM])
         \\ ‘st1Upd3 with fp_state := st1Upd3.fp_state with choices :=
             st1.fp_state.choices = st1Upd’
            by (unabbrev_all_tac \\ fs state_eqs
                \\ fp_inv_tac \\ fs[FUN_EQ_THM])
         \\ gs[])
  \\ rveq
  \\ ntac 3 $ qpat_x_assum ‘do_fprw _ _ _ = _’ mp_tac
  \\ simp[do_fprw_def, CaseEq"option"]
  \\ rpt strip_tac
  \\ ‘fpUnOpt = fpUnOpt' ∧ fpUnOpt = fpUnOpt''’ by gs[]
  \\ rveq
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ first_x_assum $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ rename1 ‘fp_translate v3 = SOME (FP_WordTree w3)’
  \\ rename1 ‘fp_translate v2 = SOME (FP_WordTree w2)’
  \\ rename1 ‘fp_translate v1 = SOME (FP_WordTree w1)’
  \\ disch_then (qspecl_then [‘FP_Add’, ‘w3’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched3 _ _ = SOME _’
  \\ strip_tac
  \\ disch_then (qspecl_then [‘FP_Add’, ‘fpUnOpt’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched2 _ _ = SOME _’
  \\ strip_tac
  \\ ‘rwAllWordTree (sched2 ++ sched3 ++
                     case do_fprw (Rval (FP_WordTree (fp_bop FP_Add w3 w2)))
                                  (st4.fp_state.opts 0) st4.fp_state.rws
                     of
                       NONE => []
                     | SOME _ => st4.fp_state.opts 0) st1.fp_state.rws (Fp_bop FP_Add fpUnOpt fpUnOpt) = SOME f''’
    by (Cases_on ‘do_fprw (Rval (FP_WordTree (fp_bop FP_Add w3 w2)))
                  (st4.fp_state.opts 0) st4.fp_state.rws’ \\ gs[]
        \\ rveq
        >- (
         irule rwAllWordTree_chaining_exact
         \\ qexists_tac ‘Fp_bop FP_Add w3 fpUnOpt’ \\ fs[fp_translate_def, fp_bop_def])
        \\ irule rwAllWordTree_chaining_exact
        \\ pop_assum mp_tac
        \\ simp[do_fprw_def, CaseEq"option"]
        \\ strip_tac \\ qexists_tac ‘fp_bop FP_Add w3 w2’
        \\ rveq \\ gs[fp_bop_def, fp_translate_def]
        \\ irule rwAllWordTree_chaining_exact
        \\ qexists_tac ‘Fp_bop FP_Add w3 fpUnOpt’ \\ fs[fp_translate_def, fp_bop_def])
  \\ pop_assum $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ disch_then $ qspecl_then [‘FP_Add’, ‘fpUnOpt’] mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_comb _ _’ \\ strip_tac
  \\ qpat_x_assum ‘rwAllWordTree sched _ fpUnOpt = SOME w1’
                  $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ disch_then $ qspecl_then [‘FP_Add’, ‘f''’] mp_tac
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched1 _ _’ \\ strip_tac
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_times_three_to_add’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices’,
       ‘λ x. if (x = 0)
             then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++ sched_comb ++ sched1 ++
             case do_fprw (Rval (FP_WordTree (fp_bop FP_Add f'' w1)))
             (st4.fp_state.opts 1) st1.fp_state.rws of
             | NONE => []
             | SOME _ => st4.fp_state.opts 1
             else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac \\ fs state_eqs
  \\ simp[evaluate_def, astTheory.isFpBool_def, astTheory.getOpClass_def,
         semanticPrimitivesTheory.do_app_def]
  \\ qexists_tac ‘oracle’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ pop_assum mp_tac \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’
  \\ strip_tac
  \\ ‘st1Upd = st1Upd with <| refs := st1.refs; ffi := st1.ffi|>’
    by (unabbrev_all_tac \\ fs state_eqs)
  \\ pop_assum (rewrite_tac o single o GSYM)
  \\ simp([fp_translate_def, shift_fp_opts_def] @ state_eqs)
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_times_three_to_add Here
                 (fp_bop FP_Mul fpUnOpt (Fp_const 0x4008000000000000w))``,
          instWordTree_def, substLookup_def]
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree (sched_comb ++ sched1 ++ sched4) _ _ ’
  \\ ‘rwAllWordTree (sched_comb ++ sched1 ++ sched4)
      (st1.fp_state.rws ++ [fp_times_three_to_add])
      (Fp_bop FP_Add (Fp_bop FP_Add fpUnOpt fpUnOpt) fpUnOpt) =
      SOME fp’ suffices_by gs[]
  \\ irule rwAllWordTree_chaining_exact
  \\ qexists_tac ‘fp_bop FP_Add f'' w1’ \\ conj_tac
  >- (irule rwAllWordTree_chaining_exact
      \\ qexists_tac ‘Fp_bop FP_Add f'' fpUnOpt’ \\ conj_tac
      \\ imp_res_tac rwAllWordTree_append_opt
      \\ rpt (first_x_assum (qspec_then `[fp_times_three_to_add]` assume_tac))
      \\ fs[fp_bop_def])
  \\ unabbrev_all_tac
  \\ fs[do_fprw_def, CaseEq"option"] \\ rveq
  \\ simp[rwAllWordTree_def, fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ rpt (first_x_assum (qspec_then `[fp_times_three_to_add]` assume_tac))
  \\ gs[fp_bop_def]
QED

Theorem fp_times_three_to_add_correct_unfold =
        REWRITE_RULE [fp_times_three_to_add_def] fp_times_three_to_add_correct;

Theorem fp_plus_zero_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_plus_zero] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_plus_zero_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_plus_zero]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ imp_res_tac evaluate_sing
  \\ pop_assum (fs o single)
  \\ ‘∃ fp. v = FP_WordTree fp’
     by (fs[freeVars_fp_bound_def]
         \\ mp_tac (GEN_ALL icing_rewriterProofsTheory.rewriteFPexp_returns_fp)
         \\ disch_then $ qspecl_then [‘st1’, ‘st2’, ‘e’, ‘FST(fp_plus_zero)’,
                                      ‘SND(fp_plus_zero)’, ‘env’, ‘e1’, ‘v’]
                       mp_tac
         \\ impl_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ qpat_x_assum `_ = App _ _` (fs o single)
  \\ qpat_x_assum `_ = e1` (fs o single)
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ‘st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ ntac 2 (simp[Once evaluate_def, evaluate_case_case, astTheory.getOpClass_def])
  \\ simp[Once do_app_def]
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ disch_then (
     qspecl_then [
       ‘fp_plus_zero’,
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
  >- fp_inv_tac
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_plus_zero Here
                 (fp_bop FP_Add fp (Fp_const 0w))``,
        instWordTree_def, substLookup_def]
QED

Theorem fp_plus_zero_correct_unfold =
        REWRITE_RULE [fp_plus_zero_def] fp_plus_zero_correct;

Theorem fp_times_minus_one_neg_correct:
  ∀ st1 st2 env e r.
   is_rewriteFPexp_correct [fp_times_minus_one_neg] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [`e`] strip_assume_tac fp_times_minus_one_neg_cases)
  >- (
   fs[]
   \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_times_minus_one_neg]’
   \\ strip_tac
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ fsrw_tac [SATISFY_ss] [])
  \\ imp_res_tac evaluate_sing
  \\ pop_assum (fs o single)
  \\ ‘∃ fp. v = FP_WordTree fp’
     by (fs[freeVars_fp_bound_def]
         \\ mp_tac (GEN_ALL icing_rewriterProofsTheory.rewriteFPexp_returns_fp)
         \\ disch_then $ qspecl_then [‘st1’, ‘st2’, ‘e’, ‘FST(fp_times_minus_one_neg)’,
                                      ‘SND(fp_times_minus_one_neg)’, ‘env’, ‘App (FP_uop FP_Neg) [e1]’, ‘v’]
                       mp_tac
         \\ impl_tac \\ gs[isFpArithExp_def, isPureExp_def])
  \\ qpat_x_assum `_ = App _ _` (fs o single)
  \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ imp_res_tac evaluate_sing \\ rveq
  \\ fs[do_app_def] \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ ‘q.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[] \\ rpt strip_tac
  \\ rename1 ‘evaluate st1 env [e1] = (st3, Rval [v])’
  \\ ‘st3 = st1 with fp_state := st3.fp_state ∧
      st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac
        \\ fs[state_component_equality, shift_fp_opts_def, CaseEq"option", CaseEq"v"])
  \\ ntac 3(simp[REVERSE_DEF, astTheory.getOpClass_def, astTheory.isFpBool_def,
                 Once evaluate_def, Once evaluate_cons,
                 evaluate_case_case, do_app_def])
  \\ qpat_assum `evaluate _ _ [e1] = _`
                (mp_then Any mp_tac isPureExp_evaluate_change_oracle)
  \\ fs[isPureExp_def]
  \\ Cases_on ‘fp_translate v’ \\ gs[CaseEq"v"] \\ rveq
  \\ disch_then (
     qspecl_then [
       ‘fp_times_minus_one_neg’,
       ‘st1 with fp_state := st1.fp_state with choices :=
          st1.fp_state.choices’,
       ‘λ x. if (x = 0)
        then [RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++
             (case do_fprw (Rval (FP_WordTree (fp_uop FP_Neg w1)))
                           (st3.fp_state.opts 0) st3.fp_state.rws of
              | NONE => [] | SOME r_opt => st3.fp_state.opts x)
        else []’] mp_tac)
  \\ impl_tac >- fp_inv_tac
  \\ strip_tac \\ fs state_eqs
  \\ qexists_tac ‘oracle’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ pop_assum mp_tac \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’
  \\ strip_tac
  \\ ‘st1Upd = st1Upd with <| refs := st1.refs; ffi := st1.ffi|>’
    by (unabbrev_all_tac \\ fs state_eqs)
  \\ pop_assum (rewrite_tac o single o GSYM)
  \\ fs state_eqs
  \\ fs([fp_translate_def, shift_fp_opts_def] @ state_eqs) \\ rveq
  \\ rpt conj_tac
  >- fp_inv_tac
  >- fp_inv_tac
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_times_minus_one_neg Here
          (fp_bop FP_Mul w1 (Fp_const 0xBFF0000000000000w))``,
          instWordTree_def, substLookup_def]
  \\ ‘st1.fp_state.rws = st3.fp_state.rws’ by fp_inv_tac
  \\ fs[do_fprw_def, CaseEq"option"] \\ rveq
  \\ gs[rwAllWordTree_def, fp_uop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_times_minus_one_neg]` assume_tac)
  \\ gs[]
QED

Theorem fp_times_minus_one_neg_correct_unfold =
        REWRITE_RULE [fp_times_minus_one_neg_def] fp_times_minus_one_neg_correct;

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
         Once evaluate_def, Once evaluate_cons, evaluate_case_case]
  \\ ‘st2 = st1 with fp_state := st2.fp_state’
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[state_component_equality])
  \\ ntac 2 (simp[Once evaluate_def, evaluate_case_case, astTheory.getOpClass_def])
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
  >- fp_inv_tac
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree fp_times_one Here
                 (fp_bop FP_Mul fp (Fp_const 0x3FF0000000000000w))``,
        instWordTree_def, substLookup_def]
QED

Theorem fp_times_one_correct_unfold =
        REWRITE_RULE [fp_times_one_def] fp_times_one_correct;

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

Theorem fp_assoc2_gen_correct:
  ∀ fpBop st1 st2 env e r.
    is_rewriteFPexp_correct [fp_assoc2_gen fpBop] st1 st2 env e r
Proof
  rw[is_rewriteFPexp_correct_def]
  \\ REVERSE (qspecl_then [‘e’, ‘fpBop’] strip_assume_tac fp_assoc2_gen_cases)
  >- (
    fs[] \\ extend_eval_tac ‘evaluate st1 _ _ = _’ ‘[fp_assoc2_gen fpBop]’
    \\ strip_tac
    \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
    \\ fsrw_tac [SATISFY_ss] [])
  \\ rveq
  \\ pop_assum (fs o single)
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[SimpL “$==>”, Once evaluate_def, Once evaluate_cons,
          astTheory.isFpBool_def, astTheory.getOpClass_def, do_app_def,
          CaseEq"prod", CaseEq"v", CaseEq"result"]
  \\ rpt strip_tac \\ rveq
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ rveq \\ gs[CaseEq"option", CaseEq"v"] \\ rveq
  \\ gs[]
  \\ rename1 ‘evaluate st1 env [e3] = (st1N, Rval [v3])’
  \\ qpat_x_assum ‘evaluate st1N env _ = _’ mp_tac
  \\ simp[SimpL “$==>”, Once evaluate_def, Once evaluate_cons,
          astTheory.isFpBool_def, astTheory.getOpClass_def, do_app_def,
          CaseEq"prod", CaseEq"v", CaseEq"result"]
  \\ rpt strip_tac \\ rveq \\ gs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ gs[]
  \\ rveq \\ gs[CaseEq"option", CaseEq"v"] \\ rveq
  \\ gs[]
  \\ rename1 ‘evaluate st1N env [e2] = (st2N, Rval [v2])’
  \\ rename1 ‘evaluate st2N env [e1] = (st2, Rval [v1])’
  \\ rveq \\ gs (shift_fp_opts_def :: state_eqs)
  \\ ‘st2.fp_state.canOpt = FPScope Opt’ by fp_inv_tac
  \\ gs[]
  \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ $ mp_then Any mp_tac (CONJUNCT1 evaluate_rewrite_hoisting))
  \\ disch_then $ qspec_then ‘w2’ mp_tac
  \\ impl_tac \\ gs[isPureExp_def, isFpArithExp_def]
  \\ strip_tac \\ impl_tac
  >- fp_inv_tac
  \\ strip_tac \\ impl_tac
  >- fp_inv_tac
  \\ strip_tac
  \\ ‘st2.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ ‘~ st2.fp_state.real_sem’ by fp_inv_tac
  \\ ‘st1N.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ ‘st2N.fp_state.rws = st1.fp_state.rws’ by fp_inv_tac
  \\ gs[]
  \\ ‘st2 = st1 with fp_state := st2.fp_state ∧
      st2N = st1 with fp_state := st2N.fp_state ∧
      st1N = st1 with fp_state := st1N.fp_state’ by (
    imp_res_tac isPureExp_same_ffi
    \\ fs[isPureExp_def]
    \\ res_tac
    \\ fs[state_component_equality])
  \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac)
  \\ ntac 3 $ pop_assum $ once_rewrite_tac o single
  \\ rpt strip_tac
  (* evaluation order in conclusion: e3 -> e2 -> App Fp_bop e2 e3 -> e1 -> App FP_bop *)
  \\ rpt $ qpat_x_assum `do_fprw _ _ _ = SOME _` mp_tac
  \\ simp[do_fprw_def, CaseEq"option"] \\ rpt strip_tac
  \\ qpat_x_assum ‘rwAllWordTree _ _ fpUnOpt'' = _’ $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ qpat_x_assum ‘rwAllWordTree _ _ fpUnOpt' = _’ $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ disch_then (qspecl_then [‘fpBop’, ‘fpUnOpt''’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_e2 _ _ = _’
  \\ strip_tac
  \\ disch_then (qspecl_then [‘fpBop’, ‘w2'’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_e1 _ _ = _’
  \\ strip_tac
  \\ ‘rwAllWordTree (sched_e2 ++ sched_e1 ++
                     (case
                     do_fprw (Rval (FP_WordTree (fp_bop fpBop w1' w2')))
                             (st2.fp_state.opts 0) st1.fp_state.rws
                     of
                       NONE => []
                     | SOME r_opt => st2.fp_state.opts 0))
      st1.fp_state.rws (Fp_bop fpBop fpUnOpt'' fpUnOpt') = SOME w1’
     by (irule rwAllWordTree_chaining_exact
         \\ qexists_tac ‘Fp_bop fpBop w1' w2'’ \\ conj_tac
         >- (irule rwAllWordTree_chaining_exact
             \\ qexists_tac ‘Fp_bop fpBop fpUnOpt'' w2'’ \\ gs[])
         \\ TOP_CASE_TAC \\ gs[fp_bop_def, rwAllWordTree_def, do_fprw_def, CaseEq"option"]
         \\ rveq \\ gs[fp_translate_def])
  \\ pop_assum $ mp_then Any mp_tac rwAllWordTree_comp_left
  \\ disch_then $ qspecl_then [‘fpBop’, ‘fpUnOpt’] mp_tac
  \\ unabbrev_all_tac \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_comb _ _ = _’
  \\ strip_tac
  \\ qpat_x_assum `rwAllWordTree _ _ fpUnOpt = _` $ mp_then Any mp_tac rwAllWordTree_comp_right
  \\ disch_then (qspecl_then [‘fpBop’, ‘w1’] mp_tac)
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree sched_e3 _ _ = _’
  \\ strip_tac
  \\ qpat_x_assum ‘evaluate _ _ [e1] = _’ $ mp_then Any mp_tac isPureExp_evaluate_change_oracle
  \\ disch_then (
     qspecl_then [
       ‘fp_assoc2_gen fpBop’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices’,
       ‘λ x. if (x = 0) then
                ([RewriteApp Here (LENGTH st1.fp_state.rws + 1)] ++ sched_comb ++ sched_e3 ++
                 (case
                 do_fprw (Rval (FP_WordTree (fp_bop fpBop w1 w2)))
                         (st2.fp_state.opts 1) st1.fp_state.rws of
             | NONE => []
             | SOME _ => st2.fp_state.opts 1))
             else []’] mp_tac)
  \\ simp state_eqs \\ impl_tac
  >- fp_inv_tac
  \\ strip_tac
  \\ qpat_x_assum ‘evaluate _ _ [e2] = _’ $ mp_then Any mp_tac isPureExp_evaluate_change_oracle
  \\ disch_then (
     qspecl_then [
       ‘fp_assoc2_gen fpBop’,
       ‘st1 with fp_state := st1.fp_state with choices := st1N.fp_state.choices’,
       ‘λ x. if x = 0 then [] else oracle (x-1)’ ] mp_tac)
  \\ simp state_eqs \\ impl_tac
  >- fp_inv_tac
  \\ strip_tac
  \\ qpat_x_assum ‘evaluate _ _ [e3] = _’ $ mp_then Any mp_tac isPureExp_evaluate_change_oracle
  \\ disch_then (
     qspecl_then [
       ‘fp_assoc2_gen fpBop’,
       ‘st1 with fp_state := st1.fp_state with choices := st1.fp_state.choices’,
       ‘oracle'’ ] mp_tac)
  \\ simp state_eqs \\ rpt strip_tac
  \\ simp[evaluate_def, astTheory.getOpClass_def, astTheory.isFpBool_def]
  \\ qexists_tac ‘oracle''’ \\ qexists_tac ‘st1.fp_state.choices’
  \\ gs[]
  \\ qpat_x_assum `evaluate _ _ [e2] = _` $ mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices)
  \\ pop_assum $ qspec_then ‘st1.fp_state.choices + (choices - st1.fp_state.choices)’ assume_tac
  \\ gs[do_app_def]
  \\ simp[Once do_fprw_def, Once rwAllWordTree_def, Once evaluateTheory.list_result_def, shift_fp_opts_def]
  \\ ‘(λ x. oracle x) = oracle’ by (gs[FUN_EQ_THM])
  \\ qmatch_goalsub_abbrev_tac ‘st1.fp_state with <| rws := _; opts := _; choices := choicesN|>’
  \\ qpat_x_assum ‘evaluate _ _ [e1] = _’ $ mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)
  \\ disch_then $ qspec_then ‘choicesN’ mp_tac
  \\ simp state_eqs
  \\ qmatch_goalsub_abbrev_tac ‘evaluate st1Upd _ _ = _’
  \\ strip_tac
  \\ ‘st1Upd = st1Upd with <| refs := st1.refs; ffi := st1.ffi |>’
     by (unabbrev_all_tac \\ simp state_eqs)
  \\ pop_assum (once_rewrite_tac o single o GSYM)
  \\ gs[]
  \\ simp (fp_translate_def :: state_eqs)
  \\ simp[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ simp[EVAL ``rwFp_pathWordTree (fp_assoc2_gen fpBop) Here
                 (fp_bop fpBop fpUnOpt'' (fp_bop fpBop fpUnOpt' fpUnOpt))``,
        instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st2.fp_state.opts 1) st1.fp_state.rws
                      (fp_bop fpBop w1 w2)`
  \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  >- (
     gs[do_fprw_def] \\ rveq
     \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree schedule rws exp’
     \\ ‘rwAllWordTree schedule rws exp = SOME (Fp_bop fpBop w1 w2)’
        suffices_by (simp[])
     \\ ntac 3 (pop_assum (gs o single o GSYM))
     \\ irule rwAllWordTree_chaining_exact
     \\ qexists_tac ‘Fp_bop fpBop w1 fpUnOpt’ \\ gs[]
     \\ imp_res_tac rwAllWordTree_append_opt
     \\ rpt $ first_x_assum $ qspec_then ‘[fp_assoc2_gen fpBop]’ assume_tac
     \\ gs[])
  \\ gs[do_fprw_def] \\ rveq
  \\ qmatch_goalsub_abbrev_tac ‘rwAllWordTree schedule rws exp’
  \\ ‘rwAllWordTree schedule rws exp = SOME x’
     suffices_by (simp[])
  \\ ntac 3 (pop_assum (gs o single o GSYM))
  \\ irule rwAllWordTree_chaining_exact
  \\ qexists_tac ‘Fp_bop fpBop w1 w2’ \\ conj_tac
  >- (
    irule rwAllWordTree_chaining_exact
    \\ qexists_tac ‘Fp_bop fpBop w1 fpUnOpt’
    \\ imp_res_tac rwAllWordTree_append_opt
    \\ rpt $ first_x_assum $ qspec_then ‘[fp_assoc2_gen fpBop]’ assume_tac
    \\ gs[])
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ rpt $ first_x_assum $ qspec_then ‘[fp_assoc2_gen fpBop]’ assume_tac
  \\ gs[]
QED

Theorem fp_assoc2_gen_correct_unfold =
        REWRITE_RULE [reverse_tuple_def, fp_assoc2_gen_def, fp_assoc_gen_def]
                     fp_assoc2_gen_correct;
Theorem fp_assoc2_gen_correct_unfold_add =
        REWRITE_RULE [reverse_tuple_def, fp_assoc2_gen_def, fp_assoc_gen_def]
                     (Q.SPEC ‘FP_Add’ fp_assoc2_gen_correct);
Theorem fp_assoc2_gen_correct_unfold_mul =
        REWRITE_RULE [reverse_tuple_def, fp_assoc2_gen_def, fp_assoc_gen_def]
                     (Q.SPEC ‘FP_Mul’ fp_assoc2_gen_correct);

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

val _ = export_theory ();
