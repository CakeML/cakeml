(*
  Correctness proofs for floating-point optimizations
*)
open source_rewriterTheory source_to_sourceTheory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory
     evaluatePropsTheory terminationTheory fpSemPropsTheory;
open preamble;

val _ = new_theory "source_to_sourceProofs";

(**
  Helper theorems and definitions
**)
val isPureOp_simp =
  LIST_CONJ (map (fn (t, c) => EVAL (``isPureOp ^t``))
    (isPureOp_def |> concl |> dest_forall |> snd
                  |> dest_eq |> snd |> TypeBase.dest_case |> #3));

(* TODO: Move, from Konrad Slind *)

Theorem do_if_cases:
  do_if x e1 e2 = SOME e ==> e = e1 \/ e = e2
Proof
  fs[do_if_def] \\ TOP_CASE_TAC \\ fs[]
QED

Theorem isPureExpList_app[simp]:
  ! es1 es2. isPureExpList (es1 ++ es2) = (isPureExpList es1 /\ isPureExpList es2)
Proof
  Induct_on `es1` \\ fs[isPureExp_def]
  \\ rpt gen_tac
  \\ EQ_TAC \\ fs[]
QED

Theorem isPureExpList_reverse[simp]:
  isPureExpList (REVERSE es) = isPureExpList es
Proof
  Induct_on `es` \\ fs[isPureExp_def]
  \\ rpt gen_tac \\ EQ_TAC \\ simp[]
QED

(**
  First, we prove that pure expressions ignore their FFI.
  This allows to swap out the FFI with an arbitrary different one
  and get the same one back from evaluating
**)

Theorem isPureOp_same_ffi:
  ! refs1 (ffi1 ffi2 : 'a ffi_state) op vl refs2 r.
    isPureOp op /\
    do_app (refs1, ffi1) op vl = SOME ((refs2,ffi2), r) ==>
    ! refs (ffi:'a ffi_state).
      do_app (refs, ffi) op vl = SOME ((refs, ffi), r)
Proof
  Cases_on `op` \\ rpt gen_tac
  \\ fs[isPureOp_simp, do_app_def] \\ rpt (TOP_CASE_TAC \\ fs[])
QED

local
  val pmatch_goal =
    ``\ env refs1 p v vl.
        ! r.
        pmatch env refs1 p v vl = r ==>
        isPurePat p ==>
        ! refs2. pmatch env refs2 p v vl = r``
  val pmatch_list_goal =
    ``\ env refs1 pl v vl.
        ! r.
        pmatch_list env refs1 pl v vl = r ==>
        isPurePatList pl ==>
        ! refs2. pmatch_list env refs2 pl v vl = r``
  val indThm = pmatch_ind |> ISPEC pmatch_goal |> SPEC pmatch_list_goal
in
Theorem isPurePat_ignores_ref:
  (! env refs1 p v vl.
    ^pmatch_goal env refs1 p v vl)
  /\
  (! env refs1 pl v vl.
    ^pmatch_list_goal env refs1 pl v vl)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac
  \\ fs[isPurePat_def, pmatch_def] \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ fs[]
QED
end

val semState_comp_eq = semanticPrimitivesTheory.state_component_equality;

local
  val eval_goal =
    ``\ (s1:'a semanticPrimitives$state) env expl.
        ! s2 r.
          evaluate s1 env expl = (s2, r) ==>
          isPureExpList expl /\
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'a semanticPrimitives$state).
            s.fp_state.rws = s1.fp_state.rws /\
            s.fp_state.canOpt = s1.fp_state.canOpt /\
            (! x. x <= (s2.fp_state.choices - s1.fp_state.choices) ==>
              s.fp_state.opts x = s1.fp_state.opts x) ==>
            ? fpOpts.
              evaluate s env expl =
                (s with <| fp_state := s.fp_state with
                  <| opts := fpOpts; choices := s.fp_state.choices + (s2.fp_state.choices - s1.fp_state.choices)|> |>, r)``;
  val eval_match_goal =
    ``\ (s1:'a semanticPrimitives$state) env v pl err_v.
        ! s2 r.
          isPurePatExpList pl /\
          evaluate_match s1 env v pl err_v = (s2, r) ==>
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'a semanticPrimitives$state).
            s.fp_state.rws = s1.fp_state.rws /\
            s.fp_state.canOpt = s1.fp_state.canOpt /\
            (! x. x <= (s2.fp_state.choices - s1.fp_state.choices) ==>
              s.fp_state.opts x = s1.fp_state.opts x) ==>
              ? fpOpts.
              evaluate_match s env v pl err_v =
                (s with <| fp_state := s.fp_state with
                  <| opts := fpOpts; choices := s.fp_state.choices + (s2.fp_state.choices - s1.fp_state.choices)|> |>, r)``;
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal
  val isPureExpList_single_thm =
    SIMP_RULE std_ss [] (EVAL ``isPureExpList [e] = isPureExp e``);
  val isPureExpList_Cons_thm =
    SIMP_RULE std_ss [] (EVAL ``isPureExpList (e::es) = (isPureExp e /\ isPureExpList es)``);
  val resolve_simple =
    fn thm => mp_tac thm \\ rpt (disch_then (fn dThm => first_assum (mp_then Any mp_tac dThm)));
  val fp_inv_tac =
    rpt strip_tac
    \\ imp_res_tac evaluate_fp_opts_inv \\ rveq
    \\ rpt (qpat_x_assum `! x. _ x = _ x` (fn thm => fs[GSYM thm]));
  val trivial =
    rpt strip_tac \\ rveq \\ fs[]
    \\ res_tac
    \\ qexists_tac `fpOpts'`
    \\ fs[fpState_component_equality, semState_comp_eq];
in
Theorem isPureExpList_swap_ffi:
  (! s1 env expl.
    ^eval_goal s1 env expl) /\
  (! s1 env v pl err_v.
    ^eval_match_goal s1 env v pl err_v)
Proof
  irule indThm \\ rpt gen_tac \\ rpt conj_tac
  \\ rpt gen_tac \\ rpt strip_tac \\ fs[]
  \\ simp[evaluate_def, isPureExp_def]
  \\ rpt strip_tac
  \\ fs[isPureExpList_single_thm]
  \\ TRY (first_x_assum irule \\ fs[Once isPureExp_def] \\ NO_TAC)
  \\ TRY (fs[fpState_component_equality, semState_comp_eq] \\ NO_TAC)
  \\ TRY (qpat_x_assum `_ = (_, _)` mp_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac
    \\ last_x_assum (qspec_then `s` resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ fs[]
    \\ rename [`do_if (HD r) e2 e3 = SOME eR`]
    \\ `isPureExp eR` by (imp_res_tac do_if_cases \\ fs[])
    \\ res_tac \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew env [_]`
    \\ first_x_assum (qspec_then `s_fpNew` resolve_simple)
    \\ unabbrev_all_tac \\ fs[semState_comp_eq]
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ trivial)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspec_then `s` impl_subgoal_tac)
    \\ TRY (rpt conj_tac \\ fp_inv_tac \\ NO_TAC)
    \\ fs[]
    \\ rpt (first_x_assum (fn ithm => first_x_assum (fn thm => mp_then Any assume_tac thm ithm)))
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew env _`
    \\ first_x_assum (qspecl_then [`s_fpNew`] resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspecl_then [`s`] resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- (rpt conj_tac \\ fp_inv_tac)
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate_match s_fpNew env _ _ _`
    \\ first_x_assum impl_subgoal_tac >- fs[]
    \\ first_x_assum (qspecl_then [`s_fpNew`] resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[]
        \\ first_x_assum drule
        \\ disch_then (qspecl_then
            [`s with fp_state := s.fp_state with canOpt := case annot of Opt => T | NoOpt => F`] impl_subgoal_tac)
        >- (fs[fpState_component_equality])
        \\ fs[fpState_component_equality, semState_comp_eq])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ res_tac
    \\ last_x_assum (qspecl_then [`s with fp_state := s.fp_state with canOpt := case annot of Opt => T | NoOpt => F`] assume_tac)
    \\ fs[fpState_component_equality]
    \\ res_tac \\ fs[fpState_component_equality, semState_comp_eq])
  >- (TOP_CASE_TAC \\ rpt strip_tac \\ rveq
      \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ impl_tac \\ fs[]
    \\ TRY (fp_inv_tac \\ NO_TAC)
    \\ disch_then assume_tac \\ fs[fpState_component_equality, semState_comp_eq]
    \\ rename [`do_log lop (HD v) e2 = SOME (Exp eR)`]
    \\ `eR = e2`
        by (qpat_x_assum `do_log _ _ _ = SOME (Exp eR)` mp_tac
            \\ fs[do_log_def]
            \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ rveq
    \\ first_x_assum drule \\ disch_then assume_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew env _ = _`
    \\ first_x_assum (qspecl_then [`s_fpNew`] impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- (fs[] \\ fp_inv_tac)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    >- (rveq \\ fs[isPureOp_def])
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    \\ imp_res_tac isPureOp_same_ffi
    \\ first_x_assum (qspecl_then [`s`] assume_tac)
    \\ rename [`evaluate st env (REVERSE es) = (s2, Rval _)`]
    \\ TOP_CASE_TAC \\ Cases_on `s.fp_state.canOpt` \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
    \\ first_x_assum impl_subgoal_tac
    \\ TRY (fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[shift_fp_opts_def, semState_comp_eq, fpState_component_equality]
    \\ rpt (qpat_x_assum `! x. _ x = _ x` ( fn thm => fs[GSYM thm])))
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum drule \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ fs[]
    \\ first_x_assum (qspecl_then [`s`] impl_subgoal_tac)
    >- fp_inv_tac
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate s_fpNew _ _ = _`
    \\ first_x_assum impl_subgoal_tac \\ fs[]
    \\ first_x_assum (qspecl_then [`s_fpNew`] impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- fp_inv_tac
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ fs[]
    \\ imp_res_tac (hd (CONJ_LIST 2 (EVAL_RULE isPurePat_ignores_ref)))
    \\ fs[])
QED
end

Theorem isPureExp_same_ffi:
  ! st1 st2 env fps1 fps2 e r.
    isPureExp e /\
    r <> Rerr (Rabort Rtype_error) /\
    evaluate st1 env [e] = (st2, r) ==>
    st2 = st1 with fp_state := st2.fp_state
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac (CONJUNCT1 (SIMP_RULE std_ss [] isPureExpList_swap_ffi)))
  \\ first_x_assum (qspecl_then [`st1`] impl_subgoal_tac)
  \\ fs[isPureExp_def] \\ fs[fpState_component_equality, semState_comp_eq]
QED

val prep = fn thm => SIMP_RULE std_ss [] thm;

(**
  Putting it all together: For a pure expression that returns a value,
  we can a) change to an arbitrary state,
  b) append an optimization,
  c) pick an arbitrary oracle to return in the end
  This is the key lemma for proving correctness of Icing optimizations
**)
Theorem isPureExp_evaluate_change_oracle:
  ! (st1 st2:'a semanticPrimitives$state) env e r.
    isPureExp e /\
    evaluate st1 env [e] = (st2, Rval r) ==>
    ! opt (stN1:'a semanticPrimitives$state) g.
      (stN1.fp_state.canOpt <=> st1.fp_state.canOpt) ==>
      ? oracle.
        evaluate (stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := oracle |>) env [e] =
          (stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := g; choices := stN1.fp_state.choices + (st2.fp_state.choices - st1.fp_state.choices) |>, Rval r)
Proof
  rpt strip_tac
  (* This will come in handy later to finish the proof
     The final fs call will not conclude without this assumption being proven! *)
  \\ `st1.fp_state.choices <= st2.fp_state.choices`
      by (imp_res_tac (CONJUNCT1 evaluate_fp_opts_inv)
          \\ fs[fpState_component_equality])
  (* Append the optimization *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
  \\ first_x_assum (qspecl_then [`[opt]`, `g`] assume_tac) \\ fs[]
  (* Change the global state *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 isPureExpList_swap_ffi)))
  \\ fs[isPureExp_def]
  \\ first_x_assum (qspecl_then [`stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := fpOpt |>`] impl_subgoal_tac)
  \\ fs[]
  (* Change the resulting opts function to an arbitrary one *)
  \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ fs[fpState_component_equality]
  \\ qexists_tac `optUntil (st2.fp_state.choices - st1.fp_state.choices) fpOpt g`
  \\ first_x_assum (qspec_then `g` assume_tac)
  \\ imp_res_tac (CONJUNCT1 evaluate_fp_opts_inv)
  \\ fs[fpState_component_equality]
QED

Theorem fp_add_comm_cases:
  ! e fpBop.
    (? e1 e2.
      e = (App (FP_bop fpBop) [e1; e2]) /\
      isPureExp e /\
      rewriteFPexp [fp_comm_gen fpBop] (App (FP_bop fpBop) [e1; e2]) =
        App (FP_bop fpBop) [e2; e1]) \/
    (rewriteFPexp [fp_comm_gen fpBop] e = e)
Proof
  rpt gen_tac \\ Cases_on `e`
  \\ fs[fp_comm_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def, matchesFPcexp_def]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[isPureOp_def]
  \\ Cases_on `fpBop` \\ fs[] \\ EVAL_TAC
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

(* Correctness definition for rewriteFPexp *)
Definition is_rewriteFPexp_correct_def:
  is_rewriteFPexp_correct rws (st1:'a semanticPrimitives$state) st2 env e r =
      ((evaluate st1 env [rewriteFPexp rws e] = (st2, r) /\
        st1.fp_state.canOpt) ==>
      ? fpOpt fpOptR.
        evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env [e] =
          (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r))
End

Definition is_rewriteFPexp_list_correct_def:
  is_rewriteFPexp_list_correct rws (st1:'a semanticPrimitives$state) st2 env exps r =
      ((evaluate st1 env (MAP (rewriteFPexp rws) exps) = (st2, r) /\
       st1.fp_state.canOpt)==>
      ? fpOpt fpOptR.
        evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
          (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r))
End

Theorem empty_rw_correct:
   ! (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_rewriteFPexp_correct_def, rewriteFPexp_def]
  \\ rpt strip_tac \\ qexists_tac `st1.fp_state.opts` \\ qexists_tac `st2.fp_state.opts`
  \\ `st1 = st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws; opts := st1.fp_state.opts |>`
      by (fs[semState_comp_eq, fpState_component_equality])
  \\ pop_assum (fn thm => fs[GSYM thm])
  \\ fs[semState_comp_eq, fpState_component_equality]
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
  \\ qspecl_then [`e`, `fpBop`] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_comm_cases)
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
  \\ fs[astTheory.isFpOp_def, astTheory.isFpBool_def]
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ `st3.fp_state.canOpt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ `st2 = st1 with fp_state := st2.fp_state /\ st3 = st1 with fp_state := st3.fp_state`
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[semState_comp_eq])
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
    by (fs[fpState_component_equality, semState_comp_eq]
        \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
        \\ simp[FUN_EQ_THM])
  \\ pop_assum (fn thm => fs[thm])
  \\ `st2.fp_state.canOpt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ imp_res_tac isPureOp_same_ffi \\ fs[isPureOp_def]
  \\ first_x_assum (qspecl_then [`st1.refs`, `st1.ffi`] assume_tac)
  \\ fs[list_result_def]
  \\ fs[do_app_def, shift_fp_opts_def, fpState_component_equality]
  \\ qexists_tac `\x. g x`
  \\ rpt conj_tac
  >- (imp_res_tac evaluate_fp_opts_inv
      \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
  \\ fs[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ fs[EVAL ``rwFp_pathWordTree (fp_comm_gen fpBop) Here (fp_bop fpBop w2 w1)``, instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws (fp_bop fpBop w1 w2)` \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_comm_gen fpBop]` assume_tac)
  \\ `st3.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
QED
end

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
  \\ reverse TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)] ++ rws`, `g`] assume_tac) \\ fs[]
    \\ asm_exists_tac \\ fs[])
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    TOP_CASE_TAC \\ fs[]
    >- (
      rpt strip_tac
      \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
      \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
      \\ fs[fpState_component_equality] \\ asm_exists_tac \\ fs[])
    \\ TOP_CASE_TAC \\ fs[]
    >- (
      rpt strip_tac
      \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
      \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
      \\ fs[fpState_component_equality] \\ asm_exists_tac \\ fs[])
    \\ rpt strip_tac \\ fs[]
    \\ first_x_assum drule \\ fs[state_component_equality, fpState_component_equality]
    \\ disch_then assume_tac \\ fs[] \\ pop_assum mp_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate st1N env [_] = (st2N, r)`
    \\ disch_then assume_tac
    \\ first_x_assum (qspecl_then [`st1N`, `st2N`, `env`, `e`, `r`] assume_tac)
    \\ fs[rewriteFPexp_def] \\ rfs[]
    \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
    \\ first_x_assum impl_subgoal_tac \\ fs[]
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_up)))
    \\ first_x_assum (qspec_then `st1.fp_state.rws  ++ [(opt0, opt1)] ++ rws` impl_subgoal_tac)
    >- (fs[SUBSET_DEF] \\ rpt strip_tac \\ fs[])
    \\ fs[] \\ qexists_tac `fpOpt''` \\ qexists_tac `fpOpt2`
    \\ fs[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_fp_opts_inv)
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `g`] assume_tac) \\ fs[]
    \\ first_x_assum drule \\ fs[fpState_component_equality])
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum drule \\ fs[state_component_equality, fpState_component_equality]
  \\ disch_then assume_tac \\ fs[] \\ pop_assum mp_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate st1N env [_] = (st2N, r)`
  \\ disch_then assume_tac
  \\ first_x_assum (qspecl_then [`st1N`, `st2N`, `env`, `e`, `r`] assume_tac)
  \\ fs[rewriteFPexp_def] \\ rfs[]
  \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
  \\ first_x_assum impl_subgoal_tac \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_up)))
  \\ first_x_assum (qspec_then `st1.fp_state.rws  ++ [(opt0, opt1)] ++ rws` impl_subgoal_tac)
  >- (fs[SUBSET_DEF] \\ rpt strip_tac \\ fs[])
  \\ fs[] \\ qexists_tac `fpOpt''` \\ qexists_tac `fpOpt2`
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv
QED

Theorem lift_rewriteFPexp_correct_list:
  ! rws (st1 st2:'a semanticPrimitives$state) env exps r.
    (! (st1 st2: 'a semanticPrimitives$state) env e r.
      is_rewriteFPexp_correct rws st1 st2 env e r) ==>
  is_rewriteFPexp_list_correct rws st1 st2 env exps r
Proof
  Induct_on `exps` \\ fs[is_rewriteFPexp_correct_def, is_rewriteFPexp_list_correct_def, semState_comp_eq, fpState_component_equality]
  \\ rpt strip_tac \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ simp[Once evaluate_cons]
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  >- (rpt strip_tac \\ rveq
      \\ first_x_assum (qspecl_then [`st1`, `q`, `env`, `h`, `Rerr e`] impl_subgoal_tac)
      \\ simp[Once evaluate_cons]
      \\ fs[]  \\ qexists_tac `fpOpt` \\ fs[]
      \\ qexists_tac `fpOptR` \\ fs[])
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ first_assum (qspecl_then [`st1`, `q`, `env`, `h`, `Rval a`] impl_subgoal_tac)
  \\ simp[Once evaluate_cons] \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then assume_tac \\ fs[]
  \\ first_x_assum impl_subgoal_tac
  \\ TRY (imp_res_tac evaluate_fp_opts_inv\\ NO_TAC)
  \\ fs[]
  \\ first_x_assum (qspec_then `fpOpt'` assume_tac) \\ fs[]
  \\ qexists_tac `optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'` \\ qexists_tac `fpOptR` \\ fs[]
QED

Definition is_optimise_correct_def:
  is_optimise_correct rws (st1:'a semanticPrimitives$state) st2 env cfg exps r =
    (evaluate st1 env (MAP (optimise (cfg with optimisations := rws)) exps) = (st2, r) ==>
    ? fpOpt fpOptR.
      evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
        (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r))
End

local
  val eval_goal =
  ``\ (st1: 'ffi semanticPrimitives$state) env exps.
    ! cfg rws st2 r expsN.
      evaluate st1 env exps = (st2, r) /\
      (! st1 st2 env exps r. is_rewriteFPexp_list_correct rws st1 st2 env exps r) /\
      exps = MAP (optimise (cfg with optimisations := rws)) expsN ==>
      ? fpOpt fpOptR.
      evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env expsN =
        (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r)``
  val eval_match_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env v pl err_v.
      ! cfg rws st2 r plN.
        evaluate_match st1 env v pl err_v = (st2, r) /\
        (! st1 st2 env exps r. is_rewriteFPexp_list_correct rws st1 st2 env exps r) /\
        pl = MAP (\ (p, e). (p, optimise (cfg with optimisations := rws) e)) plN ==>
        ? fpOpt fpOptR.
        evaluate_match (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env v plN err_v =
        (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r)``
in
Theorem foo:
  (! st1 env exps.
    ^eval_goal st1 env exps) /\
  (! (st1:'ffi semanticPrimitives$state) env v pl err_v.
      ^eval_match_goal st1 env v pl err_v)
Proof
  ho_match_mp_tac (terminationTheory.evaluate_ind |> ISPEC eval_goal |> SPEC eval_match_goal)
  \\ rpt strip_tac \\ fs[semState_comp_eq, fpState_component_equality] \\ rpt strip_tac
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac)
  (* e1::e2::en *)
  >- (
    Cases_on `expsN` \\ fs[]
    \\ Cases_on `t` \\ fs[] \\ rveq
    \\ simp [Once evaluate_cons]
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[PULL_EXISTS]
        \\ first_x_assum drule
        \\ disch_then (qspecl_then [`cfg`, `h`] impl_subgoal_tac) \\ fs[]
        \\ qexists_tac `fpOpt` \\ qexists_tac `fpOptR` \\ simp[Once evaluate_cons])
    \\ ntac 2 (TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ last_x_assum drule
    \\ disch_then (qspecl_then [`cfg`, `h`] impl_subgoal_tac) \\ fs[]
    \\ first_x_assum (mp_then Any mp_tac (CONJUNCT1 optUntil_evaluate_ok))
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`cfg`, `h'::t'`] impl_subgoal_tac) \\ fs[optimise_def]
    \\ disch_then (qspec_then `fpOpt'` assume_tac)
    \\ qexists_tac `optUntil (q.fp_state.choices - st.fp_state.choices) fpOpt fpOpt'` \\ simp[Once evaluate_cons]
    \\ fs[semState_comp_eq, fpState_component_equality])
  (* Lit l *)
  >- (
    rveq \\ Cases_on `x0` \\ fs[optimise_def] \\ rveq
    >- (rpt strip_tac \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
    \\ Cases_on `cfg.canOpt` \\ fs[]
    (* by assumption *) \\ cheat)
  (* Raise e *)
  >- (
    rveq \\ Cases_on `x0` \\ fs[optimise_def] \\ rveq
    >- (
      fs[evaluate_def, semState_comp_eq, fpState_component_equality, PULL_EXISTS]
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq
      \\ res_tac \\ fs[]
      \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
      \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
    \\ Cases_on `cfg.canOpt` \\ fs[]
    (* by assumption *) \\ cheat )
  (* Handle e pl *)
  >- (
    rveq \\ Cases_on `x0` \\ fs[optimise_def] \\ rveq
    >- (
      fs[evaluate_def, semState_comp_eq, fpState_component_equality, PULL_EXISTS]
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      >- (
        rpt strip_tac \\ rveq
        \\ res_tac \\ fs[]
        \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
        \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
      \\ reverse TOP_CASE_TAC \\ fs[]
      >- (
        rpt strip_tac \\ rveq
        \\ res_tac \\ fs[]
        \\ first_x_assum (qspecl_then [`e'`, `cfg`] impl_subgoal_tac) \\ fs[]
        \\ qexists_tac `fpOpt` \\ fs[semState_comp_eq, fpState_component_equality])
      \\ rpt strip_tac
      \\ qpat_x_assum `! st1 st2 env exps r. is_rewriteFPexl_list_correct rws _ _ _ _ _` (fn thm => rpt (first_x_assum (fn ithm => mp_then Any assume_tac ithm thm)))
      \\ first_x_assum (qspecl_then [`cfg`, `e'`] impl_subgoal_tac) \\ fs[]
      \\ first_x_assum (fn ithm => first_x_assum (fn thm => mp_then Any assume_tac ithm thm ))
      \\ first_x_assum (qspecl_then [`cfg`, `l`] impl_subgoal_tac) \\ fs[]
      \\ first_x_assum (mp_then Any (fn thm => thm |> Q.SPEC `fpOpt'` |> assume_tac) (CONJUNCT1 optUntil_evaluate_ok))
      \\ fs[]
      \\ qexists_tac `optUntil (q.fp_state.choices - st.fp_state.choices) fpOpt fpOpt'`
      \\ fs[semState_comp_eq, fpState_component_equality])
    \\ Cases_on `cfg.canOpt` \\ fs[]
    \\ (* by assumption *) cheat)
  (* Con *)
  >- (cheat)
  (* Var *)
  >- (cheat)
  (* Fun *)
  >- (cheat)
  (* App *)
  >- (cheat)
  (* Log *)
  >- (cheat)
  (* If *)
  >- (cheat)
  (* Mat *)
  >- (cheat)
  (* Let *)
  >- (cheat)
  (* Letrec *)
  >- (cheat)
  (* Tannot *)
  >- (cheat)
  (* Lannot *)
  >- (cheat)
  (* FpOptimise *)
  >- (cheat)
  (* eval_match empty *)
  >- (cheat)
  (* eval-match list *)
  \\ cheat
QED
end

Theorem compile_exp_correct:
  ! st1 env c e st2 res.
    evaluate st1 env [compile c e] = (st2, Rval res) ==>
    ? (fp_opts:num -> rewrite_app list) g.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ c.optimisations;
                   opts := fp_opts |>)
               env [e] =
        (st2 with fp_state := st2.fp_state with
          <| rws := st2.fp_state.rws ++ c.optimisations; opts := g |>,
        Rval res)
Proof
  rw[compile_def, no_optimisations_def, optimise_def]
  \\ imp_res_tac (CONJUNCT1 (prep evaluate_fp_rws_append))
  \\ cheat
  (* \\ first_x_assum (qspec_then `c.rws` assume_tac)
  \\ fs[] \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2`
  \\ fs[semState_comp_eq, fpState_component_equality] *)
QED

Definition is_fp_stable_def:
  is_fp_stable e st1 st2 env r =
    (evaluate st1 env [e] = (st2, r) ==>
    ! (fpS:fpState).
      evaluate (st1 with fp_state := fpS) env [e] = (st2 with fp_state := fpS, r))
End

Theorem REVERSE_no_optimisations:
  REVERSE (MAP (\e. no_optimisations cfg e) exps) =
  MAP (no_optimisations cfg) (REVERSE exps)
Proof
  Induct_on `exps` \\ fs[]
QED

Theorem do_opapp_is_unoptimisable:
  evaluate (st1 with fp_state := fpS) env (MAP (no_optimisations cfg) (REVERSE l)) =
    (st2 with fp_state := fpS, Rval r) /\
  do_opapp (REVERSE r) = SOME (st3, r2) ==>
  ? e. r2 = no_optimisations cfg e
Proof
  rw[semanticPrimitivesPropsTheory.do_opapp_cases]
  \\ Cases_on `r` \\ fs[] \\ rveq
  \\ imp_res_tac evaluate_length
  \\ Cases_on `l` \\ fs[]
  \\ Cases_on `t` \\ fs[] \\ rveq \\ fs[]
  \\ qpat_x_assum `evaluate _ _ _ = (_, _)` mp_tac
  \\ fs[Once evaluate_cons]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ fs[]
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[] \\ rveq
  (* TODO *)
QED

local
  val eval_goal =
  ``\ (st1: 'ffi semanticPrimitives$state) env exps.
    ! cfg st2 r expsN.
      evaluate st1 env exps = (st2, r) /\
      exps = MAP (no_optimisations cfg) expsN ==>
      ! fpS.
      evaluate (st1 with fp_state := fpS) env exps =
        (st2 with fp_state := fpS, r)``
  val eval_match_goal =
    ``\ (st1: 'ffi semanticPrimitives$state) env v pl err_v.
      ! cfg st2 r plN.
        evaluate_match st1 env v pl err_v = (st2, r) /\
        pl = MAP (\ (p, e). (p, no_optimisations cfg e)) plN ==>
        ! fpS.
        evaluate_match (st1 with fp_state := fpS) env v pl err_v =
        (st2 with fp_state := fpS, r)``
in
Theorem no_optimisations_is_fp_stable:
  (! st1 env exps.
    ^eval_goal st1 env exps) /\
  (! st1 env v pl err_v.
    ^eval_match_goal st env v pl err_v)
Proof
  mp_tac (terminationTheory.evaluate_ind |> ISPEC eval_goal |> SPEC eval_match_goal)
  \\ impl_tac \\ fs[] \\ rpt strip_tac
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac) \\ simp[evaluate_def]
  >- (
    Cases_on `expsN` \\ fs[no_optimisations_def] \\ Cases_on `t` \\ fs[no_optimisations_def]
    \\ rveq
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt strip_tac \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `h`] mp_tac) \\ fs[])
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[evaluate_def]
    \\ first_x_assum (qspecl_then [`cfg`, `h`] mp_tac) \\ fs[]
    \\ disch_then assume_tac
    \\ first_x_assum (qspecl_then [`cfg`, `h'::t'`] mp_tac) \\ fs[])
  >- (
    Cases_on `expsN` \\ fs[no_optimisations_def] \\ rveq
    \\ Cases_on `h` \\ fs[no_optimisations_def] \\ rveq
    \\ rw[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ ntac 2 (TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] mp_tac) \\ fs[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ ntac 2 (TOP_CASE_TAC \\ fs[PULL_EXISTS])
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum (qspecl_then [`cfg`, `e'`] mp_tac) \\ fs[evaluate_def]
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum drule
    \\ disch_then (qspecl_then [`cfg`, `l`, `fpS`] mp_tac) \\ fs[])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ reverse TOP_CASE_TAC \\ fs[evaluate_def]
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt strip_tac \\ rveq
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
        \\ fs[REVERSE_no_optimisations])
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
    \\ fs[REVERSE_no_optimisations])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ TOP_CASE_TAC \\ fs[]
    \\ rw[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ rw[evaluate_def])
  >- (
    Cases_on `expsN` \\ Cases_on `x0` \\ fs[no_optimisations_def] \\ rveq
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[PULL_EXISTS])
    >- (rpt strip_tac \\ rveq
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
        \\ fs[REVERSE_no_optimisations, evaluate_def])
    \\ TOP_CASE_TAC \\ fs[]
    >- (TOP_CASE_TAC \\ fs[]
        >- (rpt strip_tac \\ rveq \\ fs[evaluate_def]
            \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
            \\ fs[REVERSE_no_optimisations])
        \\ ntac 2 (TOP_CASE_TAC \\ fs[])
        \\ rpt strip_tac \\ rveq \\ fs[evaluate_def]
        \\ first_x_assum (qspecl_then [`cfg`, `REVERSE l`] mp_tac)
        \\ fs[REVERSE_no_optimisations]
        \\ rpt strip_tac
        >- (            \\ )
        \\ first_x_assum

(* TODO: optimise_dec *)

(*
Theorem compile_correct:
  compile c prog = progN ==>
  let (s,env) = THE (prim_sem_env (ffi:'ffi ffi_state)) in
  ¬semantics_prog s env prog Fail ==>
  (* TODO: Side conditions???
   backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧ mc_init_ok c mc ∧
   installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names ffi (heap_regs c.stack_conf.reg_names) mc ms ⇒ *)
  ! x.
    x IN semantics_prog s env prog ==>
    ? fpOpt.
      x IN semantics_prog (s with fp_state := s.fp_state with <| rws := (c.rws); opts := fpOpt |>) env prog
Proof
  rw[compile_def, no_optimisations_def, optimise_def, primSemEnvTheory.prim_sem_env_eq]
  \\ Cases_on `x` \\ fs[]
  \\ fs[semantics_prog_def]
  \\ qexists_tac `no_fp_opts` \\ fs[]
  \\ cheat
QED
*)

val _ = export_theory ();
