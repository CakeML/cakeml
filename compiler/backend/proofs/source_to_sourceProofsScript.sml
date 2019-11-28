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

(**
  Next, we prove that it is always fine to append optimization by changing the
  oracle. We cannot use the same oracle as before.
  This is because do_fprw accesses the rewrites from the state when executing
  the schedule. If the previous schedule failed because the rewriter was not in
  the list, the new execution must do the same to be semantics preserving.
  Theorem do_fprw_append_opt in fpOptPropsTheory is critical for this proof.
**)
local
  val eval_goal =
    ``\ (st1:'a semanticPrimitives$state) env el.
        ! res st2 opts.
          evaluate st1 env el = (st2, res) ==>
          ? fpOpt fpOpt2.
          evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ opts; opts := fpOpt |>) env el =
            (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ opts; opts := fpOpt2 |>, res)``
  val eval_match_goal =
    ``\ (st1:'a semanticPrimitives$state) env v pl err_v.
        ! res st2 opts.
          evaluate_match st1 env v pl err_v = (st2, res) ==>
          ? fpOpt fpOpt2.
          evaluate_match (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ opts; opts := fpOpt |>) env v pl err_v =
            (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ opts; opts := fpOpt2|>, res)``
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal
  val eval_step =  ntac 2 (reverse TOP_CASE_TAC \\ fs[]);
  val solve_simple =
    rpt strip_tac \\ rveq \\ fs[] \\ first_x_assum (qspec_then `opts` assume_tac) \\ fs[]
    \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2` \\ fs[];
  val solve_complex =
    rpt (qpat_x_assum `evaluate _ _ _ = _` kall_tac ORELSE
            qpat_x_assum `evaluate_match _ _ _ _ _ = _` kall_tac)
    \\ rpt (last_x_assum (qspec_then `opts` assume_tac)) \\ fs[]
    \\ (rename [`evaluate (st1 with fp_state := st1.fp_state with <| rws := _; opts := fpOpt1N |>) env [e1] =
                  (st2 with fp_state := st2.fp_state with <| rws := _; opts := _ |>, _)`,
                `evaluate (st2 with fp_state := st2.fp_state with <| rws := _; opts := fpOpt2N |>) _ _ =
                  (st3 with fp_state := st3.fp_state with <| rws := _; opts := fpOpt3N |>, _)`]
        ORELSE
      rename [`evaluate (st1 with fp_state := st1.fp_state with <| rws := _; opts := fpOpt1N |>) env [e1] =
                  (st2 with fp_state := st2.fp_state with <| rws := _; opts := _ |>, _)`,
               `evaluate_match (st2 with fp_state := st2.fp_state with <| rws := _; opts := fpOpt2N |>) env _ _ _=
                  (st3 with fp_state := st3.fp_state with <| rws := _; opts := fpOpt3N |>, _)`]
      ORELSE
      rename [`evaluate (st1 with fp_state := st1.fp_state with <| rws := _; opts := fpOpt1N |>) env (REVERSE es) =
                  (st2 with fp_state := st2.fp_state with <| rws := _; opts := _ |>, _)`,
               `evaluate (st2 with <| clock := st2.clock - 1; fp_state := st2.fp_state with <| rws := _; opts := fpOpt2N |> |>) _ _ =
                  (st3 with fp_state := st3.fp_state with <| rws := _; opts := fpOpt3N|>, _)`])
    \\ qexists_tac `optUntil (st2.fp_state.choices - st1.fp_state.choices) fpOpt1N fpOpt2N`
    \\ rpt (first_x_assum (fn thm => (mp_then Any assume_tac optUntil_evaluate_ok thm) \\ mp_tac thm))
    \\ rpt (first_x_assum (qspec_then `fpOpt2N` assume_tac))
    \\ fs[fpState_component_equality, semState_comp_eq];
in
Theorem evaluate_fp_rws_append:
  (! (st1:'a semanticPrimitives$state) env el.
    ^eval_goal st1 env el) /\
  (! (st1:'a semanticPrimitives$state) env v pl err_v.
    ^eval_match_goal st1 env v pl err_v)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac \\ fs[evaluate_def] \\ rpt strip_tac \\ rveq \\ fs[fpState_component_equality]
  \\ TRY (qexists_tac `\ x. []` \\ fs[fpState_component_equality, semState_comp_eq] \\ NO_TAC)
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  (* e1 :: e2 :: es *)
  >- (
    eval_step >- solve_simple
    \\ ntac 2 (TOP_CASE_TAC)
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ solve_complex)
  (* Raise e *)
  >- (eval_step \\ solve_simple)
  (* match *)
  >- (
    ntac 2 (TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ rpt strip_tac \\ fs[]
    \\ solve_complex)
  (* do_con_check *)
  >- (
      reverse TOP_CASE_TAC \\ fs[]
      >- (rpt strip_tac \\ rveq \\ fs[fpState_component_equality, semState_comp_eq])
      \\ eval_step >- solve_simple
      \\ TOP_CASE_TAC \\ solve_simple)
  (* Variable lookup *)
  >- (TOP_CASE_TAC \\ fs[fpState_component_equality, semState_comp_eq])
  (* do_app *)
  >- (
    eval_step >- solve_simple
    \\ TOP_CASE_TAC \\ fs[]
    >- (TOP_CASE_TAC \\ fs[] >- solve_simple
        \\ ntac 2 (TOP_CASE_TAC \\ fs[]) >- solve_simple
        \\ strip_tac \\ fs[dec_clock_def]
        \\ solve_complex)
    \\ TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
    \\ first_x_assum (qspec_then `opts` assume_tac) \\ fs[]
    \\ rename [`evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ opts; opts := fpOpt1 |>) env (REVERSE es) =
                  (st2 with fp_state := _, _)`]
    \\ Cases_on `st2.fp_state.canOpt` \\ fs[]
    >- (rpt strip_tac \\ rveq
        \\ fs[shift_fp_opts_def, fpState_component_equality]
        \\ first_x_assum (mp_then Any assume_tac optUntil_evaluate_ok)
        \\ Cases_on `do_fprw r (st2.fp_state.opts 0) st2.fp_state.rws`
        \\ imp_res_tac do_fprw_append_opt
        \\ first_x_assum (qspec_then `opts` assume_tac) \\ fs[]
        \\ first_x_assum (qspec_then `\x. sched2` assume_tac)
        \\ qexists_tac `optUntil (st2.fp_state.choices - st1.fp_state.choices) fpOpt1 (\x. sched2)`
        \\ fs[fpState_component_equality, semState_comp_eq])
    \\ rpt strip_tac \\ rveq
    \\ qexists_tac `fpOpt1` \\ fs[fpState_component_equality, semState_comp_eq])
  (* Log_op *)
  >- (
    eval_step >- solve_simple
    \\ TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ rpt strip_tac \\ fs[]
    \\ solve_complex)
  (* do_if *)
  >- (
    eval_step >- solve_simple
    \\ TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ rpt strip_tac \\ fs[]
    \\ solve_complex)
  (* match bind_exn_v *)
  >- (
    eval_step >- solve_simple
    \\ rpt strip_tac \\ fs[]
    \\ solve_complex)
  (* let binding *)
  >- (
    eval_step >- solve_simple
    \\ rpt strip_tac \\ fs[]
    \\ solve_complex)
  (* ALL_DISTINCT *)
  >- (
    reverse TOP_CASE_TAC >- fs[fpState_component_equality, semState_comp_eq]
    \\ strip_tac \\ fs[])
  (* FpOptimise *)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ rpt strip_tac \\ fs[] \\ rveq
    \\ first_x_assum (qspec_then `opts` assume_tac)
    \\ fs[] \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2`
    \\ fs[])
  (* ALL_DISTINCT (pat_bindings) *)
  >- (
    rpt (reverse TOP_CASE_TAC \\ fs[fpState_component_equality, semState_comp_eq]))
QED
end

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
  \\ first_x_assum (qspec_then `[opt]` assume_tac) \\ fs[]
  (* Change the global state *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 isPureExpList_swap_ffi)))
  \\ fs[isPureExp_def]
  \\ first_x_assum (qspecl_then [`stN1 with fp_state := stN1.fp_state with <| rws := st1.fp_state.rws ++ [opt]; opts := fpOpt |>`] impl_subgoal_tac)
  \\ fs[]
  (* Change the resulting opts function to an arbitrary one *)
  \\ first_x_assum (mp_then Any assume_tac optUntil_evaluate_ok)
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
  \\ fs[fp_comm_gen_def, rewriteFPexp_def, isPureExp_def, matchesFPexp_def]
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
    st1.fp_state.canOpt /\
    evaluate st1 env [rewriteFPexp [fp_comm_gen fpBop] e] = (st2, Rval res) ==>
    ! g. ? (fp_opts:num -> rewrite_app list).
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ [fp_comm_gen fpBop];
                   opts := fp_opts |>)
               env [e] =
        (st2 with fp_state := st2.fp_state with
          <| rws := st2.fp_state.rws ++ [fp_comm_gen fpBop]; opts := g |>,
        Rval res)
Proof
  rpt strip_tac
  \\ qspecl_then [`e`, `fpBop`] assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_comm_cases)
  \\ fs[]
  >- (
    pop_assum (fn thm => fs[thm])
    \\ imp_res_tac fp_rws_append_comm
    \\ first_x_assum (qspec_then `fpBop` assume_tac) \\ fs[]
    \\ first_x_assum (mp_then Any (qspec_then `g` assume_tac) optUntil_evaluate_ok)
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
  \\ `st2 = st1 with fp_state := st2.fp_state /\ st3 = st1 with fp_state := st3.fp_state`
    by (imp_res_tac isPureExp_same_ffi \\ fs[isPureExp_def]
        \\ res_tac \\ fs[semState_comp_eq])
  \\ imp_res_tac evaluate_sing \\ rveq \\ fs[]
  \\ rename [`evaluate st1 env [e1] = (st2, Rval [r1])`, `evaluate st2 env [e2] = (st3, Rval [r2])`]
  \\ Cases_on `do_app (st3.refs, st3.ffi) (FP_bop fpBop) [r2; r1]` \\ fs[]
  \\ PairCases_on `x` \\ fs[]
  \\ imp_res_tac do_app_fp_inv \\ rveq \\ fs[]
  \\ `st3.fp_state.canOpt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
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
  \\ rpt conj_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq]
      \\ conj_tac \\ simp[FUN_EQ_THM])
  \\ fs[do_fprw_def, rwAllWordTree_def, nth_len]
  \\ fs[EVAL ``rwFp_pathWordTree (fp_comm_gen fpBop) Here (fp_bop fpBop w2 w1)``, instWordTree_def, substLookup_def]
  \\ Cases_on `rwAllWordTree (st3.fp_state.opts 0) st3.fp_state.rws (fp_bop fpBop w1 w2)` \\ fs[rwAllWordTree_def, fpValTreeTheory.fp_bop_def]
  \\ imp_res_tac rwAllWordTree_append_opt
  \\ first_x_assum (qspec_then `[fp_comm_gen fpBop]` assume_tac)
  \\ `st3.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
QED
end

Theorem compile_exp_correct:
  ! st1 env c e st2 res.
    evaluate st1 env [compile c e] = (st2, Rval res) ==>
    ? (fp_opts:num -> rewrite_app list) g.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ c.rws;
                   opts := fp_opts |>)
               env [e] =
        (st2 with fp_state := st2.fp_state with
          <| rws := st2.fp_state.rws ++ c.rws; opts := g |>,
        Rval res)
Proof
  rw[compile_def, no_optimizations_def, optimize_def]
  \\ imp_res_tac (CONJUNCT1 (prep evaluate_fp_rws_append))
  \\ first_x_assum (qspec_then `c.rws` assume_tac)
  \\ fs[] \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2`
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

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
  rw[compile_def, no_optimizations_def, optimize_def, primSemEnvTheory.prim_sem_env_eq]
  \\ Cases_on `x` \\ fs[]
  \\ fs[semantics_prog_def]
  \\ qexists_tac `no_fp_opts` \\ fs[]
  \\ cheat
QED

val _ = export_theory ();
