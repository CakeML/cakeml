(*
  Properties of floating-point value tree semantics
*)

open preamble fpSemTheory fpOptPropsTheory fpValTreeTheory semanticPrimitivesTheory evaluateTheory;
open terminationTheory;

val _ = new_theory "fpSemProps";

(*
Theorem eqWordTree_eq:
  ! fp1 fp2. eqWordTree fp1 fp2 <=> fp1 = fp2
Proof
  Induct_on `fp1` \\ Cases_on `fp2` \\ fs[eqWordTree_def]
QED

Theorem eqBoolTree_eq:
  ! fp1 fp2. eqBoolTree fp1 fp2 <=> fp1 = fp2
Proof
  Induct_on `fp1` \\ Cases_on `fp2` \\ fs[eqBoolTree_def, eqWordTree_eq]
QED
*)

Theorem do_fpoptimise_cons:
  do_fpoptimise sc (v1 :: vs) =
    do_fpoptimise sc [v1] ++ do_fpoptimise sc vs
Proof
  Cases_on `vs` \\ fs[do_fpoptimise_def]
QED

Theorem fp_opts_mono[local]:
  ! (fps1 fps2 fps3:fpState) n m.
    (! x. fps1.opts (n + x) = fps2.opts x) /\
    (! x. fps2.opts (m + x) = fps3.opts x) ==>
    ! x. fps1.opts ((m+n) + x) = fps3.opts x
Proof
  rpt strip_tac \\ fs[]
  \\ qpat_x_assum `! x. _ _ = fps3.opts _` (qspec_then `x` (fn thm => fs[GSYM thm]))
  \\ qpat_x_assum `! x. _ _ = fps2.opts _` (qspec_then `m + x` (fn thm => fs[GSYM thm]))
QED

Theorem fp_opts_add_1[local]:
  ! (fps1 fps2:fpState) n m.
    (! x. fps1.opts (n + x) = fps2.opts x) ==>
    ! x. fps1.opts ((n + 1) + x) = fps2.opts (x + 1)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem evaluate_fp_opts_inv:
  (! (s1:'a state) env e s2 r.
    evaluate s1 env e = (s2, r) ==>
    (! x. s1.fp_state.opts (x + (s2.fp_state.choices - s1.fp_state.choices)) = s2.fp_state.opts x) /\
    s1.fp_state.rws = s2.fp_state.rws /\
    s1.fp_state.choices <= s2.fp_state.choices /\
    (s1.fp_state.canOpt <=> s2.fp_state.canOpt) /\
    (s1.fp_state.real_sem <=> s2.fp_state.real_sem) /\
    (! a b c. s1.fp_state.assertions a b c = s2.fp_state.assertions a b c)) /\
  (! (s1:'a state) env v pes errv s2 r.
    evaluate_match s1 env v pes errv = (s2, r) ==>
    (! x. s1.fp_state.opts (x + (s2.fp_state.choices - s1.fp_state.choices)) = s2.fp_state.opts x) /\
    s1.fp_state.rws = s2.fp_state.rws /\
    s1.fp_state.choices <= s2.fp_state.choices /\
    (s1.fp_state.canOpt <=> s2.fp_state.canOpt) /\
    (s1.fp_state.real_sem <=> s2.fp_state.real_sem) /\
    (! a b c. s1.fp_state.assertions a b c = s2.fp_state.assertions a b c))
Proof
  ho_match_mp_tac evaluate_ind \\ rw[]
  \\ rfs[evaluate_def] \\ rveq
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ res_tac \\ fs[dec_clock_def, shift_fp_opts_def]
  \\ imp_res_tac fp_opts_mono
  \\ imp_res_tac fp_opts_add_1
  \\ rpt (qpat_x_assum `! x. _ = _.opts x`
            ( fn thm => once_rewrite_tac [GSYM thm])
          \\ fs[])
QED

Theorem fpOp_determ:
  ! op refs refsN (ffi1 ffi2:'a ffi_state) (ffi3:'b ffi_state) r vl.
    getOpClass op = Icing /\
    do_app (refs, ffi1) op vl = SOME ((refsN, ffi2), r) ==>
    do_app (refs, ffi3) op vl = SOME ((refsN, ffi3), r)
Proof
  rpt strip_tac \\ Cases_on `op` \\ fs[astTheory.getOpClass_def]
  \\ rpt (qpat_x_assum `do_app _ _ _ = _` mp_tac)
  \\ fs[do_app_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
QED

Theorem evaluate_fp_stable:
  ! (s1 s2) env exps r.
    s1.fp_state.choices = s2.fp_state.choices /\
    evaluate s1 env exps = (s2, r) ==>
    s1.fp_state = s2.fp_state
Proof
  rpt strip_tac
  \\ imp_res_tac evaluate_fp_opts_inv
  \\ fs[fpState_component_equality, state_component_equality, FUN_EQ_THM] \\ rveq
  \\ qpat_x_assum `! x. _ x = _ x` (fn thm => fs[GSYM thm])
QED

Theorem evaluate_decs_fp_opts_inv:
  !s1 env decls s2 r.
    evaluate_decs s1 env decls = (s2, r) ==>
    (!x. s1.fp_state.opts (x + (s2.fp_state.choices - s1.fp_state.choices)) = s2.fp_state.opts x) /\
    s1.fp_state.rws = s2.fp_state.rws /\
    s1.fp_state.choices <= s2.fp_state.choices /\
    (s1.fp_state.canOpt <=> s2.fp_state.canOpt) /\
    (s1.fp_state.real_sem <=> s2.fp_state.real_sem) /\
    (! a b c. s1.fp_state.assertions a b c = s2.fp_state.assertions a b c)
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt gen_tac
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rpt (disch_then assume_tac) \\ rpt gen_tac
  \\ fs[evaluate_decs_def]
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      >- (rpt strip_tac \\ fs[])
      \\ TOP_CASE_TAC \\ fs[]
      \\ rpt strip_tac \\ fs[] \\ rveq \\ fs[]
      \\ rpt (qpat_x_assum `! x. _ _ = _ _` (fn thm => fs[GSYM thm])))
  >- (pop_assum mp_tac
      \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ imp_res_tac evaluate_fp_opts_inv \\ rpt strip_tac \\ rveq \\ fs[])
  >- (pop_assum mp_tac
      \\ TOP_CASE_TAC \\ rpt strip_tac \\ rveq \\ fs[])
  >- (rpt strip_tac \\ rveq \\ fs[])
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      >- (rpt strip_tac \\ fs[])
      \\ rpt strip_tac \\ fs[]
      \\ rpt (qpat_x_assum `! x. _ _ = _ _` (fn thm => fs[GSYM thm])))
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ fs[]
      \\ rpt (qpat_x_assum `! x. _ _ = _ _` (fn thm => fs[GSYM thm])))
QED

Theorem evaluate_decs_fp_stable:
  ! s1 env decls s2 r.
    evaluate_decs s1 env decls = (s2, r)  /\
    s1.fp_state.choices = s2.fp_state.choices ==>
    s1.fp_state = s2.fp_state
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt strip_tac \\ fs[evaluate_decs_def]
  \\ TRY (qpat_x_assum `_ = (_, _)` mp_tac)
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      \\ rename [`evaluate_decs s1 env [d1] = (s2, Rval r)`]
      \\ TOP_CASE_TAC \\ fs[]
      \\ rpt strip_tac \\ rveq
      \\ imp_res_tac evaluate_decs_fp_opts_inv \\ fs[])
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ imp_res_tac evaluate_fp_opts_inv
      \\ imp_res_tac evaluate_fp_stable
      \\ rpt strip_tac \\ rveq
      \\ first_x_assum irule \\ fs[])
  >- (TOP_CASE_TAC \\ fs[state_component_equality])
  >- (fs[state_component_equality])
  >- (TOP_CASE_TAC \\ fs[])
  >- (ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ fs[]
      \\ imp_res_tac evaluate_decs_fp_opts_inv \\ fs[])
QED

local
  val eval_goal =
    ``\st1 env xs.
      ! st2 r k h.
        evaluate st1 env xs = (st2, r) /\
        (* analogous to fps2.choices - fps1.choices < k but easier to use *)
        st2.fp_state.choices <= k + st1.fp_state.choices /\
        (! m. m < k ==> h m = st1.fp_state.opts m) ==>
          ? hN.
            evaluate (st1 with fp_state := (st1.fp_state with opts := h)) env xs =
              (st2 with fp_state := st2.fp_state with opts := hN, r)``;
  val eval_match_goal =
    ``\st1 env v pl err_v.
        ! st2 r k h.
          evaluate_match st1 env v pl err_v = (st2, r) /\
          st2.fp_state.choices <= k + st1.fp_state.choices /\
          (! m. m < k ==> h m = st1.fp_state.opts m) ==>
            ? hN.
              evaluate_match (st1 with fp_state := (st1.fp_state with opts := h)) env v pl err_v =
                (st2 with fp_state := st2.fp_state with opts := hN, r)``;
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal;
  val eval_fp_opt_invs = evaluate_fp_opts_inv;
  val eval_fp_opt_inv = hd (CONJ_LIST 2 evaluate_fp_opts_inv);
  val evalmatch_fp_opt_inv = hd (tl (CONJ_LIST 2 evaluate_fp_opts_inv));
  val solve_simple =
    rpt strip_tac \\ rveq \\ fs[fpState_component_equality, state_component_equality] \\ first_x_assum drule \\ rpt (disch_then drule)
    \\ disch_then assume_tac \\ fs[state_component_equality, fpState_component_equality];
    (* \\ rename1 `evaluate (st with fp_opts := _) _ _ = (st2, _)`
        ORELSE rename1 `evaluate_match (st with fp_opts := _) _ _ _ _ = (st2, _)`
    \\ qexists_tac `st2` \\ fs[];*)
  val solve_complex =
    rpt strip_tac \\ rveq
    \\ imp_res_tac eval_fp_opt_invs
    \\ (rename [`evaluate stA env [e1] = (stB, Rval r)`,
            `evaluate stB _ _ = (stC, _)`]
      ORELSE
        rename [`evaluate stA env (REVERSE es) = (stB, Rval r)`,
            `evaluate (dec_clock stB) _ _ = (stC, _)`]
      ORELSE
      rename [`evaluate stA env _ = (stB, _)`,
            `evaluate_match stB _ _ _ _ = (stC, _)`])
    \\ fs[dec_clock_def]
    \\ `stB.fp_state.choices <= k + stA.fp_state.choices` by (fs[])
    \\ last_x_assum (qspecl_then [`k`, `h`] drule)
    \\ rpt (disch_then drule) \\ disch_then assume_tac \\ fs[]
    \\ `! x. x < (k - (stB.fp_state.choices - stA.fp_state.choices)) ==> hN x = stB.fp_state.opts x`
      by (first_x_assum (mp_then Any assume_tac eval_fp_opt_inv) \\ fs[]
          \\ rveq \\ rpt strip_tac
          \\ qpat_x_assum `! x. h _ = hN _` (fn thm => fs[GSYM thm]))
    \\ `stC.fp_state.choices <= (k - (stB.fp_state.choices - stA.fp_state.choices)) + stB.fp_state.choices` by fs[]
    \\ res_tac \\ fs[state_component_equality, fpState_component_equality]
in
Theorem evaluate_fp_opt_add_bind:
  (! (st1:'a state) env xs.
    ^eval_goal st1 env xs) /\
  (! (st1:'a state) env v pl err_v.
    ^eval_match_goal st1 env v pl err_v)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac \\ fs[evaluate_def]
  \\ rpt strip_tac \\ fs[fpState_component_equality, state_component_equality] \\ rveq
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ solve_complex)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ rpt strip_tac \\ rveq
    \\ res_tac \\ fs[state_component_equality, fpState_component_equality])
  >- (
    ntac 2 (TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ solve_complex)
  >- (
    reverse TOP_CASE_TAC \\ fs[]
    >- (rpt strip_tac \\ fs[state_component_equality, fpState_component_equality])
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ rpt strip_tac \\ rveq
    \\ imp_res_tac eval_fp_opt_invs
    \\ res_tac \\ fs[]
    \\ fs[state_component_equality, fpState_component_equality])
  >- (
    reverse TOP_CASE_TAC \\ fs[state_component_equality, fpState_component_equality])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- solve_simple
    \\ TOP_CASE_TAC \\ fs[]
    >- (TOP_CASE_TAC \\ fs[]
        >- solve_simple
        \\ ntac 2 (TOP_CASE_TAC \\ fs[])
        >- solve_simple
        \\ solve_complex)
    >- (
     TOP_CASE_TAC \\ fs[]
     >- solve_simple
     \\ ntac 2 (TOP_CASE_TAC \\ fs[]) \\ solve_simple)
    >- (
      TOP_CASE_TAC \\ fs[]
      >- solve_simple
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ fs[] \\ rename [`evaluate st env (REVERSE es) = (s2, Rval r)`]
      \\ Cases_on `s2.fp_state.canOpt` \\ fs[] \\ rveq
      \\ rpt strip_tac \\ fs[shift_fp_opts_def]
      \\ imp_res_tac eval_fp_opt_invs
      \\ rename [`evaluate st1 env (REVERSE _) = (st2, _)`]
      \\ rveq \\ fs[fpState_component_equality, state_component_equality]
      \\ `st2.fp_state.choices <= k + st1.fp_state.choices` by (fs[dec_clock_def])
      \\ last_x_assum (qspecl_then [`k`, `h`] drule)
      \\ rpt (disch_then drule) \\ disch_then assume_tac
      \\ fs[fpState_component_equality, state_component_equality]
      \\ `hN 0 = st2.fp_state.opts 0` suffices_by fs[]
      \\ first_x_assum (mp_then Any assume_tac eval_fp_opt_inv) \\ fs[]
      \\ rveq \\ rpt strip_tac
      \\ qpat_x_assum `! x. h _ = hN _` (fn thm => fs[GSYM thm])
      \\ qpat_x_assum `!x. fps1.opts _ = fps2.opts _` (fn thm => fs[GSYM thm]))
    \\ reverse TOP_CASE_TAC \\ fs[shift_fp_opts_def]
    >- (rpt strip_tac \\ rveq
        \\ fs[fpState_component_equality, state_component_equality]
        \\ last_x_assum (qspecl_then [`k`, `h`] mp_tac)
        \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ fs[fpState_component_equality, state_component_equality])
    \\ TOP_CASE_TAC \\ fs[shift_fp_opts_def]
    >- (rpt strip_tac \\ rveq
        \\ fs[fpState_component_equality, state_component_equality]
        \\ last_x_assum (qspecl_then [`k`, `h`] mp_tac)
        \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ fs[fpState_component_equality, state_component_equality])
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ fs[fpState_component_equality, state_component_equality]
    \\ last_x_assum (qspecl_then [`k`, `h`] mp_tac)
    \\ impl_tac \\ fs[]
    \\ rpt strip_tac
    \\ fs[fpState_component_equality, state_component_equality])
  >- (
      ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (
      ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (
      ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (
      ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ solve_complex)
  >- (
      reverse TOP_CASE_TAC \\ fs[fpState_component_equality, state_component_equality]
      \\ rpt strip_tac \\ rveq \\ res_tac \\ fs[fpState_component_equality, state_component_equality])
  >- (
      rpt strip_tac \\ last_x_assum match_mp_tac
      \\ fs[] \\ asm_exists_tac \\ fs[])
  >- (
      rpt strip_tac \\ last_x_assum match_mp_tac
      \\ fs[] \\ asm_exists_tac \\ fs[])
  >- (
      ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      >- (
          rpt strip_tac \\ rveq
          \\ first_x_assum (qspecl_then [`k`, `h`] assume_tac)
          \\ fs[]
          \\ res_tac \\ fs[]
          \\ qexists_tac `hN` \\ fs[state_component_equality, fpState_component_equality])
      \\ rpt strip_tac \\ rveq \\ fs[state_component_equality, fpState_component_equality]
      \\ res_tac \\ fs[state_component_equality, fpState_component_equality])
  >- (reverse TOP_CASE_TAC \\ fs[state_component_equality, fpState_component_equality]
      \\ TOP_CASE_TAC \\ fs[state_component_equality, fpState_component_equality]
      \\ rpt strip_tac \\ res_tac \\ asm_exists_tac \\ fs[])
QED

  local
    val eval_fp_opt_add_bind = hd (CONJ_LIST 2 (SIMP_RULE std_ss [] evaluate_fp_opt_add_bind));
    val eval_match_fp_opt_add_bind = hd (tl (CONJ_LIST 2 (SIMP_RULE std_ss [] evaluate_fp_opt_add_bind)));
  in
Theorem evaluate_fp_opt_add_bind_preserving:
  (! (st1 st2:'a state) env xs r k h.
    evaluate st1 env xs = (st2, r) /\
    st2.fp_state.choices <= k + st1.fp_state.choices /\
    (! m. m < k ==> h m = st1.fp_state.opts m) ==>
    ? hN.
      evaluate (st1 with fp_state := (st1.fp_state with opts := h)) env xs =
        (st2 with fp_state := (st2.fp_state with opts := hN), r) /\
      (! m. m < (k - (st2.fp_state.choices - st1.fp_state.choices)) ==> hN m = st2.fp_state.opts m) /\
      (hN (k - (st2.fp_state.choices - st1.fp_state.choices)) = h k))
  /\
  ! (st1 st2:'a state) env v pl err_v xs r k h.
    evaluate_match st1 env v pl err_v = (st2, r) /\
    st2.fp_state.choices <= k + st1.fp_state.choices /\
    (! m. m < k ==> h m = st1.fp_state.opts m) ==>
    ? hN.
      evaluate_match (st1 with fp_state := (st1.fp_state with opts := h)) env v pl err_v =
        (st2 with fp_state := (st2.fp_state with opts := hN), r) /\
      (! m. m < (k - (st2.fp_state.choices - st1.fp_state.choices)) ==> hN m = st2.fp_state.opts m) /\
      (hN (k - (st2.fp_state.choices - st1.fp_state.choices)) = h k)
Proof
  rpt strip_tac
  THENL [first_assum (mp_then Any assume_tac eval_fp_opt_add_bind),
         first_assum (mp_then Any assume_tac eval_match_fp_opt_add_bind)]
  \\ pop_assum (fn asm => last_assum (mp_then Any assume_tac asm)) \\ fs[]
  \\ res_tac \\ fs[state_component_equality, fpState_component_equality]
  \\ (first_assum (mp_then Any assume_tac eval_fp_opt_inv) ORELSE
      first_assum (mp_then Any assume_tac evalmatch_fp_opt_inv))
  \\ (last_assum (mp_then Any assume_tac eval_fp_opt_inv) ORELSE
      last_assum (mp_then Any assume_tac evalmatch_fp_opt_inv))
  \\ fs[] \\ conj_tac \\ rpt strip_tac
  \\ rpt (qpat_x_assum `! x. _ = _` (fn thm => fs[GSYM thm]))
QED
  end;
end;

Definition optUntil_def:
  optUntil (k:num) f g = \x. if x < k then f x else g (x - k)
End

Theorem optUntil_evaluate_ok:
  (! st1 st2 env exps r g.
    evaluate st1 env exps = (st2, r) ==>
    ? fpOpt.
      evaluate (st1 with fp_state := st1.fp_state with opts := optUntil (st2.fp_state.choices-st1.fp_state.choices) st1.fp_state.opts g) env exps =
        (st2 with fp_state := (st2.fp_state with opts := g), r)) /\
  (! st1 st2 env v pl err_v r g.
    evaluate_match st1 env v pl err_v = (st2, r) ==>
    ? fpOpt.
      evaluate_match (st1 with fp_state := st1.fp_state with opts := optUntil (st2.fp_state.choices-st1.fp_state.choices) st1.fp_state.opts g) env v pl err_v =
        (st2 with fp_state := (st2.fp_state with opts := g), r))
Proof
  rpt strip_tac \\ imp_res_tac evaluate_fp_opt_add_bind_preserving
  \\ first_x_assum (qspecl_then [`st2.fp_state.choices - st1.fp_state.choices `, `optUntil (st2.fp_state.choices - st1.fp_state.choices) st1.fp_state.opts g`] impl_subgoal_tac)
  \\ TRY (fs[optUntil_def] \\ NO_TAC)
  \\ pop_assum impl_subgoal_tac \\ fs[state_component_equality, fpState_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv
  \\ rewrite_tac [FUN_EQ_THM]
  \\ fs[]
  \\ rpt (qpat_x_assum `! x. _ x = _ x` (fn thm => rewrite_tac[GSYM thm]))
  \\ fs[optUntil_def]
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
          evaluate st1 env el = (st2, res) /\
          set (st1.fp_state.rws) SUBSET set (opts) ==>
          ? fpOpt fpOpt2.
          evaluate (st1 with fp_state := st1.fp_state with <| rws := opts; opts := fpOpt |>) env el =
            (st2 with fp_state := st2.fp_state with <| rws := opts; opts := fpOpt2 |>, res)``
  val eval_match_goal =
    ``\ (st1:'a semanticPrimitives$state) env v pl err_v.
        ! res st2 opts.
          evaluate_match st1 env v pl err_v = (st2, res) /\
          set (st1.fp_state.rws) SUBSET set (opts) ==>
          ? fpOpt fpOpt2.
          evaluate_match (st1 with fp_state := st1.fp_state with <| rws := opts; opts := fpOpt |>) env v pl err_v =
            (st2 with fp_state := st2.fp_state with <| rws := opts; opts := fpOpt2|>, res)``
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal
  val eval_step =  ntac 2 (reverse TOP_CASE_TAC \\ fs[]);
  val semState_comp_eq = semanticPrimitivesTheory.state_component_equality;
  val solve_simple =
    rpt strip_tac \\ rveq \\ fs[] \\ first_x_assum (qspec_then `opts` impl_subgoal_tac) \\ fs[]
    \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2` \\ fs[];
  val solve_complex =
    rpt (last_x_assum (qspec_then `opts` impl_subgoal_tac))
    \\ TRY (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality] \\ NO_TAC)
    \\ rpt (qpat_x_assum `evaluate _ _ _ = _` kall_tac ORELSE
            qpat_x_assum `evaluate_match _ _ _ _ _ = _` kall_tac) \\ fs[]
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
    \\ rpt (first_x_assum (fn thm => (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok) thm) \\ mp_tac thm))
    \\ rpt (first_x_assum (qspec_then `fpOpt2N` assume_tac))
    \\ fs[fpState_component_equality, semState_comp_eq];
in
Theorem evaluate_fp_rws_up:
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
    (* FunApp *)
    >- (TOP_CASE_TAC \\ fs[] >- solve_simple
        \\ ntac 2 (TOP_CASE_TAC \\ fs[]) >- solve_simple
        \\ strip_tac \\ fs[dec_clock_def]
        \\ solve_complex)
    (* Simple *)
    >- (
      TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ ntac 2 (TOP_CASE_TAC \\ fs[]) \\ solve_simple)
    (* Icing *)
    >- (
      TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rename [`evaluate st1 env (REVERSE es) = (st2,Rval res)`]
      \\ `set st2.fp_state.rws SUBSET set opts`
        by (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality])
      \\ qpat_x_assum `evaluate _ _ _ = _` kall_tac
      \\ first_x_assum (qspec_then `opts` impl_subgoal_tac) \\ fs[]
      \\ rename [`evaluate (st1 with fp_state := st1.fp_state with <| rws := opts; opts := fpOpt1 |>) env (REVERSE es) =
                 (st2 with fp_state := _, _)`]
      \\ Cases_on `st2.fp_state.canOpt` \\ fs[]
      >- (rpt strip_tac \\ rveq
        \\ fs[shift_fp_opts_def, fpState_component_equality]
        \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
        \\ Cases_on `do_fprw r (st2.fp_state.opts 0) st2.fp_state.rws`
        \\ imp_res_tac do_fprw_up
        \\ first_x_assum (qspec_then `\x. sched2` assume_tac)
        \\ qexists_tac `optUntil (st2.fp_state.choices - st1.fp_state.choices) fpOpt1 (\x. sched2)`
        \\ fs[fpState_component_equality, semState_comp_eq])
      \\ rpt strip_tac \\ rveq
      \\ qexists_tac `fpOpt1` \\ fs[fpState_component_equality, semState_comp_eq])
    (* Reals *)
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- (rpt strip_tac \\ rveq
        \\ res_tac \\ qexists_tac `fpOpt` \\ fs[shift_fp_opts_def]
        \\ qexists_tac `(\ x. fpOpt2 (x + 1))`
        \\ fs[fpState_component_equality, semState_comp_eq])
    \\ TOP_CASE_TAC \\ fs[shift_fp_opts_def]
    >- (rpt strip_tac \\ rveq
        \\ res_tac \\ qexists_tac `fpOpt` \\ fs[]
        \\ qexists_tac `(\ x. fpOpt2 (x + 1))`
        \\ fs[fpState_component_equality, semState_comp_eq])
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ res_tac \\ qexists_tac `fpOpt` \\ fs[]
    \\ qexists_tac `(\ x. fpOpt2 (x + 1))`
    \\ fs[fpState_component_equality, semState_comp_eq])
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
    \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
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
    \\ first_x_assum (qspec_then `opts` impl_subgoal_tac)
    \\ fs[] \\ qexists_tac `fpOpt` \\ qexists_tac `fpOpt2`
    \\ fs[])
  (* ALL_DISTINCT (pat_bindings) *)
  >- (
    rpt (reverse TOP_CASE_TAC \\ fs[fpState_component_equality, semState_comp_eq]))
QED
end

Theorem evaluate_fp_rws_append:
  (! (st1:'a semanticPrimitives$state) env el res st2 opts.
    evaluate st1 env el = (st2, res) ==>
    ! g.
    ? fpOpt.
    evaluate (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ opts; opts := fpOpt |>) env el =
      (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ opts; opts := g |>, res)) /\
  ! (st1:'a semanticPrimitives$state) env v pl err_v res st2 opts.
    evaluate_match st1 env v pl err_v = (st2, res) ==>
    ! g.
    ? fpOpt.
    evaluate_match (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ opts; opts := fpOpt |>) env v pl err_v =
      (st2 with fp_state := st2.fp_state with <| rws := st2.fp_state.rws ++ opts; opts := g |>, res)
Proof
  rpt strip_tac \\ imp_res_tac (SIMP_RULE std_ss [] evaluate_fp_rws_up)
  \\ first_x_assum (qspec_then `st1.fp_state.rws ++ opts` impl_subgoal_tac) \\ fs[]
  THENL [first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok)),
         first_x_assum (mp_then Any assume_tac (CONJUNCT2 optUntil_evaluate_ok))]
  \\ first_x_assum (qspec_then `g` assume_tac) \\ fs[]
  \\ `st1.fp_state.rws = st2.fp_state.rws` by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ asm_exists_tac
  \\ fs[fpState_component_equality, state_component_equality]
QED

(** UNUSED STUFF BEGINS HERE

Theorem compress_word_valid:
  ! v.
    isFpWordOp v ==>
    ? w. compress v =  (Rval (Litv (Word64 w)))
Proof
  Induct_on `v` \\ fs[isFpWordOp_def, compress_def] \\ rpt strip_tac
  \\ res_tac \\ fs[]
QED

Theorem compress_bool_valid:
  ! v.
    isFpBoolOp v ==>
    ? b. compress v = (Rval (Boolv b))
Proof
  Induct_on `v` \\ fs[isFpBoolOp_def, compress_def] \\ rpt strip_tac
  \\ imp_res_tac compress_word_valid \\ fs[]
  >- (qexists_tac `fp_pred_comp f0 w` \\ fs[])
  \\ rename [`fp_cmp_comp f1 w1 w2`]
  \\ qexists_tac `fp_cmp_comp f1 w1 w2` \\ fs[]
QED
**)

val _ = export_theory();
