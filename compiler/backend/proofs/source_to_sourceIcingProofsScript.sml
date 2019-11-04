(*
  Correctness proofs for floating-point optimizations
*)

open source_to_sourceIcingTheory fpOptPropsTheory semanticPrimitivesTheory evaluateTheory
     terminationTheory fpSemPropsTheory;
open preamble;

val _ = new_theory "source_to_sourceIcingProofs";

(* TODO: Move *)
fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;

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

Theorem triple_case_eq[local]:
  (case a of |Rval c1 => (x,y,f c1) | Rerr c2 => (x,y,g c2)) = (x,y,case a of | Rval c1 => f c1 | Rerr c2 => g c2)
Proof
  Cases_on `a` \\ fs[]
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

local
  val eval_goal =
    ``\ (s1:'a state) env fps1 expl.
        ! s2 fps2 r.
          evaluate s1 env fps1 expl = (s2, fps2, r) ==>
          isPureExpList expl /\
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'a state) (fps3:fp_state).
            fps3.rws = fps1.rws /\
            fps3.canOpt = fps1.canOpt /\
            (! x. x <= (fps2.choices - fps1.choices) ==>
              fps3.opts x = fps1.opts x) ==>
            ? fpOpts.
              evaluate s env fps3 expl =
                (s, fps2 with <| opts := fpOpts; choices := fps3.choices + (fps2.choices - fps1.choices) |>, r)``;
  val eval_match_goal =
    ``\ (s1:'a state) env fps1 v pl err_v.
        ! s2 fps2 r.
          isPurePatExpList pl /\
          evaluate_match s1 env fps1 v pl err_v = (s2, fps2, r) ==>
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'a state) (fps3:fp_state).
            fps3.rws = fps1.rws /\
            fps3.canOpt = fps1.canOpt /\
            (! x. x <= (fps2.choices - fps1.choices) ==>
              fps3.opts x = fps1.opts x) ==>
              ? fpOpts.
              evaluate_match s env fps3 v pl err_v =
                (s, fps2 with <| opts := fpOpts; choices := fps3.choices + (fps2.choices - fps1.choices) |>, r)``;
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
    \\ first_x_assum (qspec_then `s` assume_tac)
    \\ fs[fp_state_component_equality];
in
Theorem isPureExpList_swap_ffi:
  (! s1 env fps1 expl.
    ^eval_goal s1 env fps1 expl) /\
  (! s1 env fps1 v pl err_v.
    ^eval_match_goal s1 env fps1 v pl err_v)
Proof
  irule indThm \\ rpt gen_tac \\ rpt conj_tac
  \\ rpt gen_tac \\ rpt strip_tac \\ fs[]
  \\ simp[evaluate_def, isPureExp_def]
  \\ rpt strip_tac
  \\ fs[isPureExpList_single_thm]
  \\ TRY (first_x_assum irule \\ fs[Once isPureExp_def] \\ NO_TAC)
  \\ TRY (fs[fp_state_component_equality] \\ NO_TAC)
  \\ TRY (qpat_x_assum `_ = (_, _, _)` mp_tac)
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac
    \\ last_x_assum (qspec_then `s` resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ fs[]
    \\ rename [`do_if (HD r) e2 e3 = SOME eR`]
    \\ `isPureExp eR` by (imp_res_tac do_if_cases \\ fs[])
    \\ res_tac \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate _ env fpsNew [_]`
    \\ first_x_assum (qspec_then `fpsNew` resolve_simple)
    \\ unabbrev_all_tac \\ fs[state_component_equality]
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ trivial)
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 3 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspecl_then [`s`, `fps3`] impl_subgoal_tac)
    \\ TRY (rpt conj_tac \\ fp_inv_tac \\ NO_TAC)
    \\ fs[]
    \\ rpt (first_x_assum (fn ithm => first_x_assum (fn thm => mp_then Any assume_tac thm ithm)))
    \\ qmatch_goalsub_abbrev_tac `evaluate _ env fpsNew _`
    \\ first_x_assum (qspecl_then [`s`, `fpsNew`] resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[fp_state_component_equality])
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspecl_then [`s`, `fps3`] resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- (rpt conj_tac \\ fp_inv_tac)
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate_match _ env fpsNew _ _ _`
    \\ first_x_assum impl_subgoal_tac >- fs[]
    \\ first_x_assum (qspecl_then [`s`, `fpsNew`] resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ fs[fp_state_component_equality]
    \\ fp_inv_tac)
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[]
        \\ first_x_assum drule
        \\ disch_then (qspecl_then [`s`, `fps3 with canOpt := T`] assume_tac)
        \\ fs[fp_state_component_equality]
        \\ res_tac  \\ fs[fp_state_component_equality])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ res_tac
    \\ last_x_assum (qspecl_then [`s`, `fps3 with canOpt := T`] assume_tac)
    \\ fs[fp_state_component_equality]
    \\ res_tac \\ fs[fp_state_component_equality])
  >- (TOP_CASE_TAC \\ TRY trivial
      \\ rpt strip_tac \\ rveq
      \\ fs[fp_state_component_equality])
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ disch_then (qspec_then `s` impl_subgoal_tac)
    \\ TRY (fp_inv_tac \\ NO_TAC)
    \\ fs[fp_state_component_equality]
    \\ rename [`do_log lop (HD v) e2 = SOME (Exp eR)`]
    \\ `eR = e2`
        by (qpat_x_assum `do_log _ _ _ = SOME (Exp eR)` mp_tac
            \\ fs[do_log_def]
            \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ rveq
    \\ first_x_assum drule \\ disch_then assume_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate _ env fpsNew _ = _`
    \\ first_x_assum (qspecl_then [`s`, `fpsNew`] impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- (fs[] \\ fp_inv_tac)
    \\ fs[fp_state_component_equality]
    \\ fp_inv_tac)
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    >- (rveq \\ fs[isPureOp_def])
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    \\ imp_res_tac isPureOp_same_ffi
    \\ first_x_assum (qspecl_then [`s`, `fps3`] assume_tac)
    \\ rename [`evaluate st env fps (REVERSE es) = (s2, fps1, Rval _)`]
    \\ TOP_CASE_TAC \\ Cases_on `fps1.canOpt` \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
    \\ first_x_assum impl_subgoal_tac
    \\ TRY (fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[shift_fp_opts_def, state_component_equality, fp_state_component_equality]
    \\ rpt (qpat_x_assum `! x. _ x = _ x` ( fn thm => fs[GSYM thm])))
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum drule \\ disch_then (qspec_then `s` impl_subgoal_tac)
    >- fp_inv_tac
    \\ fs[fp_state_component_equality])
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ fs[]
    \\ first_x_assum (qspecl_then [`s`, `fps3`] impl_subgoal_tac)
    >- fp_inv_tac
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate _ _ fpsNew _ = _`
    \\ first_x_assum impl_subgoal_tac \\ fs[]
    \\ first_x_assum (qspecl_then [`s`, `fpsNew`] impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- fp_inv_tac
    \\ fs[fp_state_component_equality]
    \\ fp_inv_tac)
  >- (
    ntac 3 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ fs[]
    \\ imp_res_tac (hd (CONJ_LIST 2 (EVAL_RULE isPurePat_ignores_ref)))
    \\ fs[]
    \\ res_tac \\ fs[fp_state_component_equality]
    \\ fp_inv_tac)
QED
end

(**
  Next, we prove that it is always fine to append optimization by changing the
  oracle.
**)
local
  val eval_goal =
    ``\ (ffi:'a state) env fps el.
        ! res ffi2 fps2 opt.
          evaluate ffi env fps el = (ffi2, fps2, res) ==>
          ? fpOptN fpOptN2.
          evaluate ffi env (fps with <| rws := fps.rws ++ [opt]; opts := fpOptN |> ) el =
            (ffi2, fps2 with <| rws := fps2.rws ++ [opt]; opts := fpOptN2 |>, res)``
  val eval_match_goal =
    ``\ (ffi:'a state) env fps v pl err_v.
        ! res ffi2 fps2 opt.
          evaluate_match ffi env fps v pl err_v = (ffi2, fps2, res) ==>
          ? fpOptN fpOptN2.
          evaluate_match ffi env (fps with <| rws := fps.rws ++ [opt]; opts := fpOptN |>) v pl err_v =
            (ffi2, fps2 with <| rws := fps2.rws ++ [opt]; opts := fpOptN2 |>, res)``
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal
  val eval_step =  ntac 3 (reverse TOP_CASE_TAC \\ fs[]);
  val solve_simple =
    rpt strip_tac \\ rveq \\ fs[] \\ first_x_assum (qspec_then `opt` assume_tac) \\ fs[]
    \\ qexists_tac `fpOptN` \\ qexists_tac `fpOptN2` \\ fs[];
  val solve_complex =
    rpt (qpat_x_assum `evaluate _ _ _ _ = _` kall_tac ORELSE
            qpat_x_assum `evaluate_match _ _ _ _ _ _ = _` kall_tac)
    \\ rpt (last_x_assum (qspec_then `opt` assume_tac)) \\ fs[]
    \\ (rename [`evaluate st1 env (fps1 with <| rws := _; opts := fpOpt1N |>) [e1] =
                  (st2, fps2 with <| rws := _; opts := fps2opt |>, _)`,
               `evaluate st2 _ (fps2 with <| rws := _; opts := fpOpt2N |>) _ =
                  (st3, fps3 with <| rws := _; opts := fps3opt |>, _)`]
        ORELSE
      rename [`evaluate st1 env (fps1 with <| rws := _; opts := fpOpt1N |>) [e1] =
                  (st2, fps2 with <| rws := _; opts := fps2opt |>, _)`,
               `evaluate_match st2 env (fps2 with <| rws := _; opts := fpOpt2N |>) _ _ _=
                  (st3, fps3 with <| rws := _; opts := fps3opt |>, _)`]
      ORELSE
      rename [`evaluate st1 env (fps1 with <| rws := _; opts := fpOpt1N |>) (REVERSE es) =
                  (st2, fps2 with <| rws := _; opts := fps2opt |>, _)`,
               `evaluate (dec_clock st2) _ (fps2 with <| rws := _; opts := fpOpt2N |>) _ =
                  (st3, fps3 with <| rws := _; opts := fps3opt |>, _)`])
    \\ qexists_tac `optUntil (fps2.choices - fps1.choices) fpOpt1N fpOpt2N`
    \\ last_x_assum (mp_then Any assume_tac optUntil_evaluate_ok)
    \\ first_x_assum (qspec_then `fpOpt2N` assume_tac)
    \\ fs[fp_state_component_equality];
in
Theorem evaluate_fp_rws_append:
  (! (ffi:'a state) env fps el.
    ^eval_goal ffi env fps el) /\
  (! (ffi:'a state) env fps v pl err_v.
    ^eval_match_goal ffi env fps v pl err_v)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac \\ fs[evaluate_def] \\ rpt strip_tac \\ rveq \\ fs[]
  \\ TRY (qexists_tac `\ x. []` \\ fs[fp_state_component_equality] \\ NO_TAC)
  \\ qpat_x_assum `_ = (_, _, _)` mp_tac
  (* e1 :: e2 :: es *)
  >- (
    eval_step >- solve_simple
    \\ ntac 2 (TOP_CASE_TAC) \\ fs[triple_case_eq] \\ rpt strip_tac \\ rveq
    \\ solve_complex)
  (* Raise e *)
  >- (eval_step \\ solve_simple)
  (* match *)
  >- (
    ntac 3 (TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ rpt strip_tac \\ fs[]
    \\ solve_complex)
  (* do_con_check *)
  >- (
      reverse TOP_CASE_TAC \\ fs[]
      >- (rpt strip_tac \\ fs[fp_state_component_equality])
      \\ eval_step >- solve_simple
      \\ TOP_CASE_TAC  \\ solve_simple)
  (* Variable lookup *)
  >- (TOP_CASE_TAC \\ fs[fp_state_component_equality])
  (* do_app *)
  >- (
    eval_step >- solve_simple
    \\ TOP_CASE_TAC \\ fs[]
    >- (TOP_CASE_TAC \\ fs[] >- solve_simple
        \\ ntac 2 (TOP_CASE_TAC \\ fs[]) >- solve_simple
        \\ strip_tac \\ fs[]
        \\ solve_complex)
    \\ TOP_CASE_TAC \\ fs[] >- solve_simple
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ qpat_x_assum `evaluate _ _ _ _ = _` kall_tac
    \\ first_x_assum (qspec_then `opt` assume_tac) \\ fs[]
    \\ rename [`evaluate st1 env (fps1 with <| rws := _; opts := fpOpt1N |>) (REVERSE es) =
                  (st2, fps2 with <| rws := _; opts := fps2opt |>, _)`]
    \\ Cases_on `fps2.canOpt` \\ fs[]
    >- (rpt strip_tac \\ rveq
        \\ fs[shift_fp_opts_def, fp_state_component_equality]
        \\ first_x_assum (mp_then Any assume_tac optUntil_evaluate_ok)
        \\ Cases_on `do_fprw r (fps2.opts 0) fps2.rws`
        \\ imp_res_tac do_fprw_append_opt
        \\ first_x_assum (qspec_then `[opt]` assume_tac) \\ fs[]
        \\ first_x_assum (qspec_then `\x. sched2` assume_tac)
        \\ qexists_tac `optUntil (fps2.choices - fps1.choices) fpOpt1N (\x. sched2)`
        \\ fs[fp_state_component_equality])
    \\ rpt strip_tac \\ rveq
    \\ qexists_tac `fpOpt1N` \\ fs[fp_state_component_equality])
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
    reverse TOP_CASE_TAC >- fs[fp_state_component_equality]
    \\ strip_tac \\ fs[])
  >- (
    eval_step \\ strip_tac \\ rveq
    \\ first_x_assum (qspec_then `opt'` assume_tac) \\ fs[]
    \\ qexists_tac `fpOptN` \\ fs[fp_state_component_equality])
  (* ALL_DISTINCT (pat_bindings) *)
  >- (
    rpt (reverse TOP_CASE_TAC \\ fs[fp_state_component_equality]))
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
  ! (st1 st2:'a state) env fps1 fps2 e r.
    isPureExp e /\
    evaluate st1 env fps1 [e] = (st2, fps2, Rval r) ==>
    ! opt (stN1:'a state) fps3 g.
      (fps3.canOpt <=> fps1.canOpt) ==>
      ? oracle.
        evaluate stN1 env (fps3 with <| rws := fps1.rws ++ [opt]; opts := oracle |>) [e] =
          (stN1, fps3 with <| rws := fps1.rws ++ [opt]; opts := g; choices := fps3.choices + (fps2.choices - fps1.choices) |>, Rval r)
Proof
  rpt strip_tac
  (* This will come in handy later to finish the proof
     The final fs call will not conclude without this assumption being proven! *)
  \\ `fps1.choices <= fps2.choices`
      by (imp_res_tac (CONJUNCT1 evaluate_fp_opts_inv)
          \\ fs[fp_state_component_equality])
  (* Append the optimization *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
  \\ first_x_assum (qspec_then `opt` assume_tac) \\ fs[]
  (* Change the global state *)
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 isPureExpList_swap_ffi)))
  \\ fs[isPureExp_def]
  \\ first_x_assum (qspecl_then [`stN1`, `fps3 with <| rws := fps1.rws ++ [opt]; opts := fpOptN |>`] impl_subgoal_tac)
  \\ fs[]
  (* Change the resulting opts function to an arbitrary one *)
  \\ first_x_assum (mp_then Any assume_tac optUntil_evaluate_ok)
  \\ fs[fp_state_component_equality]
  \\ qexists_tac `optUntil (fps2.choices - fps1.choices) fpOptN g`
  \\ first_x_assum (qspec_then `g` assume_tac)
  \\ imp_res_tac (CONJUNCT1 evaluate_fp_opts_inv)
  \\ fs[fp_state_component_equality]
QED

Theorem fp_add_comm_cases:
  ! e.
    (? e1 e2.
      e = (App (FP_bop FP_Add) [e1; e2]) /\
      isPureExp e /\
      rewriteFPexp [fp_add_comm] (App (FP_bop FP_Add) [e1; e2]) =
        App (FP_bop FP_Add) [e2; e1]) \/
    (rewriteFPexp [fp_add_comm] e = e)
Proof
  rpt gen_tac \\ fs[rewriteFPexp_def, fp_add_comm_def, matchesFPexp_def]
  \\ Cases_on `e` \\ fs[]
  \\ rename1 `App op els`
  \\ Cases_on `op` \\ fs[]
  \\ Cases_on `f` \\ fs[] \\ EVAL_TAC
QED

Theorem fp_state_opts_eq[local]:
  fps with <| rws := rwsN; opts := fps.opts |> = fps with <| rws := rwsN |>
Proof
  Cases_on `fps` \\ fs[fp_state_component_equality]
QED

local
  val fp_rws_append_comm =
    SIMP_RULE std_ss [] evaluate_fp_rws_append
    |> CONJ_LIST 2
    |> map (SPEC_ALL) |> map (GEN ``(opt:fp_pat #fp_pat)``)
    |> map (Q.SPEC `fp_add_comm`) |> map GEN_ALL
    |> LIST_CONJ;
  val eval_fp_opt_inv =
    SIMP_RULE std_ss [] fpSemPropsTheory.evaluate_fp_opts_inv
    |> CONJ_LIST 2 |> hd;
  val isPureExp_ignores_state =
    EVAL_RULE isPureExpList_swap_ffi
    |> CONJ_LIST 2
    |> hd
in
Theorem fp_add_comm_correct:
  ! (ffi1 ffi2:'a state) env (fps1 fps2:fp_state) e res.
    fps1.canOpt /\
    evaluate ffi1 env fps1 [rewriteFPexp [fp_add_comm] e] = (ffi2, fps2, Rval res) ==>
    ! g.
    ? (fp_opts:num -> rewrite_app list).
        evaluate ffi1 env
          (fps1 with <| rws := fps1.rws ++ [fp_add_comm]; opts := fp_opts |>) [e] =
          (ffi2, fps2 with <| rws := fps2.rws ++ [fp_add_comm]; opts := g |>, Rval res)
Proof
  rpt strip_tac
  \\ qspec_then `e` assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_comm_cases)
  \\ fs[]
  >- (
    pop_assum (fn thm => fs[thm])
    \\ imp_res_tac fp_rws_append_comm
    \\ first_x_assum (mp_then Any (qspec_then `g` assume_tac) optUntil_evaluate_ok)
    \\ fs[fp_state_component_equality]
    \\ asm_exists_tac \\ fs[])
  \\ fs[evaluate_def] \\ rveq
  \\ qpat_x_assum `_ = (_, _, _)` mp_tac
  \\ rename [`evaluate ffi1 env fps1 [e1]`]
  \\ Cases_on `evaluate ffi1 env fps1 [e1]` \\ fs[]
  \\ rename [`evaluate ffi1 env fps1 [e1] = (ffi2, r)`]
  \\ PairCases_on `r` \\ fs[]
  \\ rename [`evaluate ffi1 env fps1 [e1] = (ffi2, fps2, r)`]
  \\ Cases_on `r` \\ fs[]
  \\ rename [`evaluate ffi2 env fps2 [e2]`]
  \\ Cases_on `evaluate ffi2 env fps2 [e2]` \\ fs[]
  \\ rename [`evaluate ffi2 env fps2 [e2] = (ffi3, r)`] \\ PairCases_on `r` \\ fs[]
  \\ rename [`evaluate ffi2 env fps2 [e2] = (ffi3, fps3, r)`]
  \\ Cases_on `r` \\ fs[]
  \\ fs[astTheory.isFpOp_def, astTheory.isFpBool_def]
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ `fps3.canOpt` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ rpt strip_tac \\ rveq
  \\ ntac 2 (first_x_assum (mp_then Any assume_tac isPureExp_evaluate_change_oracle))
  \\ first_x_assum (qspecl_then [`fp_add_comm`, `ffi1`, `fps2`, `\x. if (x = (fps3.choices - fps1.choices) + 1) then [RewriteApp Here (LENGTH fps1.rws)] ++ fps3.opts x else g x`] impl_subgoal_tac)
  >- (fs[isPureExp_def]
      \\ cheat)
  \\ fs[]
  \\ first_x_assum (qspecl_then [`fp_add_comm`, `ffi1`, `fps1`, `oracle`] impl_subgoal_tac)
  >- (fs[isPureExp_def] \\ cheat)
  \\ fs[]
  \\ `fps1.rws = fps2.rws` by (cheat)
  \\ qexists_tac `oracle'` \\ fs[]

QED
(*
  \\ ntac 2 (first_x_assum
      (fn thm => mp_then Any assume_tac isPureExp_ignores_state thm \\ mp_tac thm))
  \\ rpt strip_tac
  \\ `isPureExp e1 /\ isPureExp e2` by (fs[isPureExp_def])
  \\ fs[shift_fp_opts_def]
  \\ qexists_tac
      `\x.
        if (x + fps2.choices < fps3.choices)
        then fps2.opts x
        else if (x + fps1.choices <= fps3.choices)
        then fps1.opts (x - (fps3.choices - fps2.choices))
        else if (x = (fps3.choices - fps1.choices) + 1)
        then [RewriteApp Here (LENGTH fps1.rws)] ++ fps1.opts x
        else fps3.opts x`
  \\ qmatch_goalsub_abbrev_tac `evaluate ffi1 env (fps1 with <| rws := rws_comm; opts := opts_comm |>) [e2]`
  \\ last_x_assum (qspecl_then [`ffi1`, `fps1 with <| opts := opts_comm |>`] impl_subgoal_tac)
  >- (unabbrev_all_tac
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[isPureExp_def] \\ rveq \\ fs[]
      \\ cheat (* either invariant or get rid of it *))
  \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (hd (CONJ_LIST 2 fp_rws_append_comm)))
  \\ fs[fp_state_component_equality]
  \\ `fps3.rws = fps1.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ rveq
  \\ qpat_x_assum `Abbrev (rws_comm = _)` (fn thm => fs[thm] \\ assume_tac thm)
  \\ imp_res_tac evaluate_fp_opts_inv
  \\ fs[fp_state_component_equality]
  \\ first_x_assum (qspecl_then [`ffi1`, `fps3 with <| opts := fpOpts |>`] impl_subgoal_tac)
  >- (unabbrev_all_tac
      \\ imp_res_tac evaluate_fp_opts_inv
      \\ rpt conj_tac
      >- (fs[isPureExp_def])
      >- (fs[])
      >- (cheat (* either invariant or get rid of it *))
      \\ rpt strip_tac
      \\ simp[fp_state_component_equality]
      \\ qpat_x_assum `!x. _ x = fpOpts x` (fn thm => rewrite_tac[GSYM thm])
      \\ `~(x + fps3.choices - fps2.choices + fps2.choices < fps3.choices)`
          by (simp[])
      \\ BETA_TAC
      \\ pop_assum (fn thm => once_rewrite_tac [thm])
      \\ `x + fps3.choices - fps2.choices + fps1.choices <= fps3.choices`
        by (irule LESS_EQ_TRANS
            \\ qexists_tac `(fps2.choices - fps1.choices) + fps3.choices - fps2.choices + fps1.choices`
            \\ conj_tac \\ simp[])
      \\ simp[])
  \\ qpat_x_assum `Abbrev (opts_comm = _)` (fn thm => fs[fp_state_component_equality] \\ assume_tac thm)
  \\ first_x_assum (mp_then Any assume_tac (hd (CONJ_LIST 2 fp_rws_append_comm)))
  \\  (* need theorem to change num of choices... *)
  \\ `evaluate ffi1 env (fps3 with <| rws := rws_comm; opts := fpOpts; choices := fps1.choices + fps3.choices - fps2.choices |>) [e1] =
        (ffi1, fps3 with <| rws := rws_comm; opts := fpOpts'; choices := fps3.choices |>, Rval a)`
      by (cheat)
  \\ pop_assum (fn thm => rewrite_tac[thm])
  \\ qpat_x_assum `do_app _ _ _ = _` mp_tac
  \\ simp[do_app_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ rpt strip_tac \\ rveq
  \\ `REVERSE a = [h']` by (cheat)
  \\ `HD a' = h` by (cheat)
  \\ simp[fp_state_component_equality]
  \\ rpt conj_tac
  >- (cheat) (* from pure exp *)
  >- (cheat) (*arith + invariant of fp opts *)
  \\ cheat (* from invariant *) *)

val _ = export_theory ();
