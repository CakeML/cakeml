(*
  Properties of floating-point value tree semantics
*)

open preamble fpSemTheory fpValTreeTheory semanticPrimitivesTheory evaluateTheory;
open terminationTheory;

val _ = new_theory "fpSemProps";

Theorem fp_opts_mono[local]:
  ! (fps1 fps2 fps3:fp_state) n m.
    (! x. fps1.opts (n + x) = fps2.opts x) /\
    (! x. fps2.opts (m + x) = fps3.opts x) ==>
    ! x. fps1.opts ((m+n) + x) = fps3.opts x
Proof
  rpt strip_tac \\ fs[]
  \\ qpat_x_assum `! x. _ _ = fps3.opts _` (qspec_then `x` (fn thm => fs[GSYM thm]))
  \\ qpat_x_assum `! x. _ _ = fps2.opts _` (qspec_then `m + x` (fn thm => fs[GSYM thm]))
QED

Theorem fp_opts_add_1[local]:
  ! (fps1 fps2:fp_state) n m.
    (! x. fps1.opts (n + x) = fps2.opts x) ==>
    ! x. fps1.opts ((n + 1) + x) = fps2.opts (x + 1)
Proof
  rpt strip_tac \\ fs[]
QED

Theorem evaluate_fp_opts_inv:
  (! (s1:'a state) env (fps1:fp_state) e s2 fps2 r.
    evaluate s1 env fps1 e = (s2, fps2, r) ==>
    (! x. fps1.opts (x + (fps2.choices - fps1.choices)) = fps2.opts x) /\
    fps1.rws = fps2.rws /\
    fps1.choices <= fps2.choices /\
    (fps1.canOpt <=> fps2.canOpt)) /\
    (* (?c. 0 <= c /\ c = s2.fp_choices - s1.fp_choices)) /\ *)
  (! (s1:'a state) env (fps1:fp_state) v pes errv s2 fps2 r.
    evaluate_match s1 env fps1 v pes errv = (s2, fps2, r) ==>
    (! x. fps1.opts (x + (fps2.choices - fps1.choices)) = fps2.opts x) /\
    fps1.rws = fps2.rws /\
    fps1.choices <= fps2.choices /\
    (fps1.canOpt <=> fps2.canOpt))
 (* /\
    (?c. 0 <= c /\ c = s2.fp_choices - s1.fp_choices)) *)
Proof
  ho_match_mp_tac evaluate_ind \\ rw[]
  \\ rfs[evaluate_def] \\ rveq
  \\ TRY (qexists_tac `0` \\ fs[] \\ NO_TAC)
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs[fix_clock_def])
  \\ rpt strip_tac \\ rveq
  \\ res_tac \\ fs[dec_clock_def, shift_fp_opts_def]
  \\ imp_res_tac fp_opts_mono
  \\ imp_res_tac fp_opts_add_1
  \\ TRY (asm_exists_tac \\ fs[])
  \\ rpt (qpat_x_assum `! x. _ = _.opts x`
            ( fn thm => once_rewrite_tac [GSYM thm])
          \\ fs[])
QED

local
  val eval_goal =
    ``\ st1 env fps1 xs.
      ! st2 fps2 r k h.
        evaluate st1 env fps1 xs = (st2, fps2, r) /\
        (* analogous to fps2.choices - fps1.choices < k but easier to use *)
        fps2.choices <= k + fps1.choices /\
        (! m. m < k ==> h m = fps1.opts m) ==>
          ? hN.
            evaluate st1 env (fps1 with opts := h) xs = (st2, fps2 with opts := hN, r)``;
  val eval_match_goal =
    `` \ st1 env fps1 v pl err_v.
        ! st2 fps2 r k h.
          evaluate_match st1 env fps1 v pl err_v = (st2, fps2, r) /\
          fps2.choices <= k + fps1.choices /\
          (! m. m < k ==> h m = fps1.opts m) ==>
            ? hN.
              evaluate_match st1 env (fps1 with opts := h) v pl err_v = (st2, fps2 with opts := hN, r)``;
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal;
  val eval_fp_opt_invs = evaluate_fp_opts_inv;
  val eval_fp_opt_inv = hd (CONJ_LIST 2 evaluate_fp_opts_inv);
  val evalmatch_fp_opt_inv = hd (tl (CONJ_LIST 2 evaluate_fp_opts_inv));
  val solve_simple =
    rpt strip_tac \\ rveq \\ first_x_assum drule \\ rpt (disch_then drule)
    \\ disch_then assume_tac \\ fs[fp_state_component_equality];
    (* \\ rename1 `evaluate (st with fp_opts := _) _ _ = (st2, _)`
        ORELSE rename1 `evaluate_match (st with fp_opts := _) _ _ _ _ = (st2, _)`
    \\ qexists_tac `st2` \\ fs[];*)
  val solve_complex =
    rpt strip_tac \\ rveq
    \\ imp_res_tac eval_fp_opt_invs
    \\ (rename [`evaluate _ env fpA [e1] = (_, fpB, Rval r)`,
            `evaluate _ _ fpB _ = (_, fpC , _)`]
      ORELSE
        rename [`evaluate _ env fpA (REVERSE es) = (_, fpB, Rval r)`,
            `evaluate (dec_clock _) _ fpB _ = (_, fpC, _)`]
      ORELSE
      rename [`evaluate _ env fpA _ = (_, fpB, _)`,
            `evaluate_match _ _ fpB _ _ _ = (_ , fpC, _)`])
    \\ fs[dec_clock_def]
    \\ `fpB.choices <= k + fpA.choices` by (fs[])
    \\ last_x_assum (qspecl_then [`k`, `h`] drule)
    \\ rpt (disch_then drule) \\ disch_then assume_tac \\ fs[]
    \\ `! x. x < (k - (fpB.choices - fpA.choices)) ==> hN x = fpB.opts x`
      by (first_x_assum (mp_then Any assume_tac eval_fp_opt_inv) \\ fs[]
          \\ rveq \\ rpt strip_tac
          \\ qpat_x_assum `! x. h _ = hN _` (fn thm => fs[GSYM thm]))
    \\ `fpC.choices <= (k - (fpB.choices - fpA.choices)) + fpB.choices` by fs[]
    \\ res_tac \\ fs[fp_state_component_equality]
in
Theorem evaluate_fp_opt_add_bind:
  (! (st1:'a state) env fps1 xs.
    ^eval_goal st1 env fps1 xs) /\
  (! (st1:'a state) env fps1 v pl err_v.
    ^eval_match_goal st1 env fps1 v pl err_v)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac \\ fs[evaluate_def]
  \\ rpt strip_tac \\ fs[fp_state_component_equality] \\ rveq
  \\ qpat_x_assum `_ = (_,_,_)` mp_tac
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ ntac 3 (TOP_CASE_TAC \\ fs[])
    \\ solve_complex)
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ rpt strip_tac \\ rveq
    \\ res_tac \\ fs[fp_state_component_equality])
  >- (
    ntac 3 (TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ solve_complex)
  >- (
    reverse TOP_CASE_TAC \\ fs[]
    >- (rpt strip_tac \\ fs[fp_state_component_equality])
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ rpt strip_tac \\ rveq
    \\ imp_res_tac eval_fp_opt_invs
    \\ res_tac \\ fs[]
    \\ fs[fp_state_component_equality])
  >- (
    reverse TOP_CASE_TAC \\ fs[fp_state_component_equality])
  >- (
    ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    >- solve_simple
    \\ TOP_CASE_TAC \\ fs[]
    >- (TOP_CASE_TAC \\ fs[]
        >- solve_simple
        \\ ntac 2 (TOP_CASE_TAC \\ fs[])
        >- solve_simple
        \\ solve_complex)
    \\ TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    >- (solve_simple)
    \\ fs[] \\ rename [`evaluate st env fps (REVERSE es) = (s2, fps2, Rval r)`]
    \\ Cases_on `fps2.canOpt` \\ fs[] \\ rveq
    \\ rpt strip_tac \\ fs[shift_fp_opts_def]
    \\ imp_res_tac eval_fp_opt_invs
    \\ rename [`evaluate _ env fps1 (REVERSE _) = (_, fps2, _)`]
    \\ rveq \\ fs[fp_state_component_equality]
    \\ `fps2.choices <= k + fps1.choices` by (fs[dec_clock_def])
    \\ last_x_assum (qspecl_then [`k`, `h`] drule)
    \\ rpt (disch_then drule) \\ disch_then assume_tac \\ fs[fp_state_component_equality]
    \\ `hN 0 = fps2.opts 0` suffices_by fs[]
    \\ first_x_assum (mp_then Any assume_tac eval_fp_opt_inv) \\ fs[]
    \\ rveq \\ rpt strip_tac
    \\ qpat_x_assum `! x. h _ = hN _` (fn thm => fs[GSYM thm])
    \\ qpat_x_assum `!x. fps1.opts _ = fps2.opts _` (fn thm => fs[GSYM thm]))
  >- (
      ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (
      ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (
      ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ solve_complex)
  >- (
      ntac 3 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ solve_complex)
  >- (
      reverse TOP_CASE_TAC \\ fs[fp_state_component_equality]
      \\ rpt strip_tac \\ rveq \\ res_tac \\ fs[fp_state_component_equality])
  >- (
      rpt strip_tac \\ last_x_assum match_mp_tac
      \\ fs[] \\ asm_exists_tac \\ fs[])
  >- (
      rpt strip_tac \\ last_x_assum match_mp_tac
      \\ fs[] \\ asm_exists_tac \\ fs[])
  >- (
      ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      >- (
          rpt strip_tac \\ rveq
          \\ first_x_assum (qspecl_then [`k`, `h`] assume_tac)
          \\ fs[]
          \\ res_tac \\ fs[]
          \\ qexists_tac `hN` \\ fs[fp_state_component_equality])
      \\ rpt strip_tac \\ rveq \\ fs[fp_state_component_equality]
      \\ res_tac \\ fs[fp_state_component_equality])
  >- (reverse TOP_CASE_TAC \\ fs[fp_state_component_equality]
      \\ TOP_CASE_TAC \\ fs[fp_state_component_equality] \\ solve_simple)
QED

  local
    val eval_fp_opt_add_bind = hd (CONJ_LIST 2 (SIMP_RULE std_ss [] evaluate_fp_opt_add_bind));
  in
Theorem evaluate_fp_opt_add_bind_preserving:
  ! (st1 st2:'a state) env fps1 fps2 xs r k h.
    evaluate st1 env fps1 xs = (st2, fps2, r) /\
    fps2.choices <= k + fps1.choices /\
    (! m. m < k ==> h m = fps1.opts m) ==>
    ? hN.
      evaluate st1 env (fps1 with opts := h) xs =
        (st2, fps2 with opts := hN, r) /\
      (! m. m < (k - (fps2.choices - fps1.choices)) ==> hN m = fps2.opts m) /\
      (hN (k - (fps2.choices - fps1.choices)) = h k)
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac eval_fp_opt_add_bind)
  \\ pop_assum (fn asm => last_assum (mp_then Any assume_tac asm)) \\ fs[]
  \\ res_tac \\ fs[fp_state_component_equality]
  \\ first_assum (mp_then Any assume_tac eval_fp_opt_inv)
  \\ last_assum (mp_then Any assume_tac eval_fp_opt_inv)
  \\ fs[] \\ conj_tac \\ rpt strip_tac
  \\ rpt (qpat_x_assum `! x. _ = _` (fn thm => fs[GSYM thm]))
QED
  end;
end;

Theorem fpOp_determ:
  ! op refs refsN (ffi1 ffi2:'a ffi_state) (ffi3:'b ffi_state) r vl.
    isFpOp op /\
    do_app (refs, ffi1) op vl = SOME ((refsN, ffi2), r) ==>
    do_app (refs, ffi3) op vl = SOME ((refsN, ffi3), r)
Proof
  rpt strip_tac \\ Cases_on `op` \\ fs[astTheory.isFpOp_def]
  \\ rpt (qpat_x_assum `do_app _ _ _ = _` mp_tac)
  \\ fs[do_app_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
QED

Theorem evaluate_fp_stable:
  ! s1 env fps1 exps s2 fps2 r.
    fps1.choices = fps2.choices /\
    evaluate s1 env fps1 exps = (s2, fps2, r) ==>
    fps1 = fps2
Proof
  rpt strip_tac
  \\ imp_res_tac evaluate_fp_opts_inv \\ Cases_on `fps1` \\ Cases_on `fps2`
  \\ fs[] \\ rveq
  \\ `! x. f x = f' x` by (fs[])
  \\ pop_assum (fn thm => assume_tac (EXT thm))
  \\ fs[]
QED

Theorem evaluate_decs_fp_opts_inv:
  ! s1 env fps1 decls s2 fps2 r.
    evaluate_decs s1 env fps1 decls = (s2, fps2, r) ==>
    ((! x. fps1.opts (x + (fps2.choices - fps1.choices)) = fps2.opts x) /\
    fps1.rws = fps2.rws /\
    fps1.choices <= fps2.choices /\
    (fps1.canOpt <=> fps2.canOpt))
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt gen_tac
  \\ rpt conj_tac \\ rpt gen_tac
  \\ rpt (disch_then assume_tac) \\ rpt gen_tac
  \\ fs[evaluate_decs_def]
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      >- (rpt strip_tac \\ fs[])
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ fs[] \\ rveq
      \\ fs[]
      \\ rpt (qpat_x_assum `! x. _ _ = _ _` (fn thm => fs[GSYM thm])))
  >- (pop_assum mp_tac
      \\ ntac 4 (reverse TOP_CASE_TAC \\ fs[])
      \\ imp_res_tac evaluate_fp_opts_inv \\ rpt strip_tac \\ rveq \\ fs[])
  >- (pop_assum mp_tac
      \\ TOP_CASE_TAC \\ fs[])
  >- (ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq \\ fs[])
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      >- (rpt strip_tac \\ fs[])
      \\ rpt strip_tac \\ fs[]
      \\ rpt (qpat_x_assum `! x. _ _ = _ _` (fn thm => fs[GSYM thm])))
QED

Theorem evaluate_decs_fp_stable:
  ! s1 env fps1 decls s2 fps2 r.
    evaluate_decs s1 env fps1 decls = (s2, fps2, r)  /\
    fps1.choices = fps2.choices ==>
    fps1 = fps2
Proof
  ho_match_mp_tac evaluate_decs_ind \\ rpt strip_tac \\ fs[evaluate_decs_def]
  \\ qpat_x_assum `_ = (_, _, _)` mp_tac
  >- (ntac 3 (reverse TOP_CASE_TAC \\ fs[])
      \\ rename [`evaluate_decs s1 env fps1 [d1] = (s2, fps3, Rval r)`]
      \\ ntac 2 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ rveq
      \\ `fps1.choices = fps3.choices`
          by (imp_res_tac evaluate_decs_fp_opts_inv \\ fs[])
      \\ fs[])
  >- (ntac 4 (reverse TOP_CASE_TAC \\ fs[])
      \\ imp_res_tac evaluate_fp_opts_inv
      \\ imp_res_tac evaluate_fp_stable
      \\ rpt strip_tac \\ rveq
      \\ first_x_assum irule \\ fs[])
  >- (TOP_CASE_TAC \\ fs[])
  >- (ntac 2 (TOP_CASE_TAC \\ fs[]))
  >- (ntac 3 (TOP_CASE_TAC \\ fs[])
      \\ rpt strip_tac \\ fs[]
      \\ imp_res_tac evaluate_decs_fp_opts_inv \\ fs[])
QED

Definition optUntil_def:
  optUntil (k:num) f g = \x. if x < k then f x else g (x - k)
End

(* TODO: Move *)
fun impl_subgoal_tac th =
  let
    val hyp_to_prove = lhand (concl th)
  in
    SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
  end;

Theorem optUntil_evaluate_ok:
  ! st1 st2 env fps1 fps2 exps r g.
    evaluate st1 env fps1 exps = (st2, fps2, r) ==>
    ? fpOpt.
      evaluate st1 env (fps1 with opts := optUntil (fps2.choices-fps1.choices) fps1.opts g) exps =
        (st2, fps2 with <| opts := g |>, r)
Proof
  rpt strip_tac \\ imp_res_tac evaluate_fp_opt_add_bind_preserving
  \\ first_x_assum (qspecl_then [`fps2.choices - fps1.choices `, `optUntil (fps2.choices - fps1.choices) fps1.opts g`] impl_subgoal_tac)
  >-  (rpt strip_tac \\ fs[optUntil_def])
  \\ pop_assum impl_subgoal_tac \\ fs[fp_state_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv
  \\ rewrite_tac [FUN_EQ_THM]
  \\ fs[]
  \\ rpt (qpat_x_assum `! x. _ x = _ x` (fn thm => rewrite_tac[GSYM thm]))
  \\ fs[optUntil_def]
QED

(*
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
*)

val _ = export_theory();
