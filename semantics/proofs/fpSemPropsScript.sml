(*
  Properties of floating-point value tree semantics
*)

open preamble fpSemTheory fpValTreeTheory semanticPrimitivesTheory evaluateTheory;
open terminationTheory;

val _ = new_theory "fpSemProps";

Theorem fp_opts_mono[local]:
  ! (s1 s2 s3:'a state) n m.
    (! x. s1.fp_opts (n + x) = s2.fp_opts x) /\
    (! x. s2.fp_opts (m + x) = s3.fp_opts x) ==>
    ? k. ! x. s1.fp_opts (k + x) = s3.fp_opts x
Proof
  rpt strip_tac \\ qexists_tac `n+m`
  \\ qpat_x_assum `! x. _ _ = s3.fp_opts _` (qspec_then `x` (fn thm => fs[GSYM thm]))
  \\ qpat_x_assum `! x. _ _ = s2.fp_opts _` (qspec_then `m + x` (fn thm => fs[GSYM thm]))
QED

Theorem fp_opts_add_1[local]:
  ! (s1 s2:'a state) n m.
    (! x. s1.fp_opts (n + x) = s2.fp_opts x) ==>
    ? k. ! x. s1.fp_opts (k + x) = s2.fp_opts (x + 1)
Proof
  rpt strip_tac
  \\ qexists_tac `n+1` \\ fs[]
QED

Theorem evaluate_fp_opts_inv:
  (! (s1:'a state) env e s2 r.
    evaluate s1 env e = (s2, r) ==>
    (! x. s1.fp_opts (x + (s2.fp_choices - s1.fp_choices)) = s2.fp_opts x) /\
    s1.fp_rws = s2.fp_rws /\
    s1.fp_choices <= s2.fp_choices /\
    (?c. 0 <= c /\ c = s2.fp_choices - s1.fp_choices)) /\
  (! (s1:'a state) env v pes errv s2 r.
    evaluate_match s1 env v pes errv = (s2, r) ==>
    (! x. s1.fp_opts (x + (s2.fp_choices - s1.fp_choices)) = s2.fp_opts x) /\
    s1.fp_rws = s2.fp_rws /\
    s1.fp_choices <= s2.fp_choices /\
    (?c. 0 <= c /\ c = s2.fp_choices - s1.fp_choices))
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
  \\ rpt (qpat_x_assum `! x. _ = _.fp_opts x`
            ( fn thm => once_rewrite_tac [GSYM thm])
          \\ fs[])
QED

(* Write this in terms of +, not -, st2.fp_choices < k + st1.fp_choices *)
local
  val eval_goal =
    ``\ st1 env xs.
      ! st2 r k h.
        evaluate st1 env xs = (st2, r) /\
        st2.fp_choices - st1.fp_choices < k /\
        (! m. m < k ==> h m = st1.fp_opts m) ==>
          ? hN.
            evaluate (st1 with fp_opts := h) env xs = (st2 with fp_opts := hN, r)``;
  val eval_match_goal =
    `` \ st1 env v pl err_v.
        ! st2 r k h.
          evaluate_match st1 env v pl err_v = (st2, r) /\
          st2.fp_choices - st1.fp_choices < k /\
          (! m. m < k ==> h m = st1.fp_opts m) ==>
            ? hN.
              evaluate_match (st1 with fp_opts := h) env v pl err_v = (st2 with fp_opts := hN, r)``;
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal;
  val eval_fp_opt_invs = evaluate_fp_opts_inv;
  val eval_fp_opt_inv = hd (CONJ_LIST 2 evaluate_fp_opts_inv);
  val evalmatch_fp_opt_inv = hd (tl (CONJ_LIST 2 evaluate_fp_opts_inv));
  val solve_simple =
    rpt strip_tac \\ rveq \\ first_x_assum drule \\ rpt (disch_then drule)
    \\ disch_then assume_tac \\ fs[state_component_equality];
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
    \\ `stB.fp_choices < k + stA.fp_choices` by (fs[])
    \\ last_x_assum (qspecl_then [`k`, `h`] drule)
    \\ rpt (disch_then drule) \\ disch_then assume_tac \\ fs[]
    \\ `! x. x < (k - (stB.fp_choices - stA.fp_choices)) ==> hN x = stB.fp_opts x`
      by (first_x_assum (mp_then Any assume_tac eval_fp_opt_inv) \\ fs[]
          \\ rveq \\ rpt strip_tac
          \\ qpat_x_assum `! x. h _ = hN _` (fn thm => fs[GSYM thm]))
    \\ `stC.fp_choices < (k -(stB.fp_choices - stA.fp_choices)) + stB.fp_choices` by fs[]
    \\ `0 < k - (stB.fp_choices - stA.fp_choices)` by  fs[]
    \\ res_tac \\ fs[state_component_equality];
in
Theorem evaluate_fp_opt_add_bind:
  (! (st1:'a state) env xs.
    ^eval_goal st1 env xs) /\
  (! (st1:'a state) env v pl err_v.
    ^eval_match_goal st1 env v pl err_v)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac \\ fs[evaluate_def]
  \\ rpt strip_tac \\ fs[state_component_equality] \\ rveq
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ solve_complex)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ rpt strip_tac \\ rveq
    \\ res_tac \\ fs[state_component_equality])
  >- (
    ntac 2 (TOP_CASE_TAC \\ fs[]) >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ solve_complex)
  >- (
    reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- solve_simple
    \\ reverse TOP_CASE_TAC \\ fs[]
    >- solve_simple
    \\ rpt strip_tac \\ rveq
    \\ imp_res_tac eval_fp_opt_invs
    \\ res_tac \\ fs[]
    \\ fs[state_component_equality])
  >- (
    reverse TOP_CASE_TAC \\ fs[]
    \\ solve_simple)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[])
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
    \\ rpt strip_tac \\ fs[shift_fp_opts_def]
    \\ imp_res_tac eval_fp_opt_invs
    \\ rename [`evaluate st1 env (REVERSE _) = (st2, _)`]
    \\ rveq \\ fs[state_component_equality]
    \\ `st2.fp_choices < k + st1.fp_choices` by (fs[dec_clock_def])
    \\ last_x_assum (qspecl_then [`k`, `h`] drule)
    \\ rpt (disch_then drule) \\ disch_then assume_tac \\ fs[state_component_equality]
    \\ `hN 0 = st2.fp_opts 0` suffices_by fs[]
    \\ first_x_assum (mp_then Any assume_tac eval_fp_opt_inv) \\ fs[]
    \\ rveq \\ rpt strip_tac
    \\ qpat_x_assum `! x. h _ = hN _` (fn thm => fs[GSYM thm])
    \\ qpat_x_assum `!x. st1.fp_opts _ = st2.fp_opts _` (fn thm => fs[GSYM thm]))
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ reverse TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ solve_complex)
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ solve_complex)
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- solve_simple
      \\ solve_complex)
  >- (reverse TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ rpt strip_tac \\ rveq \\ res_tac \\ fs[state_component_equality])
  >- (rpt strip_tac \\ last_x_assum match_mp_tac
      \\ fs[] \\ asm_exists_tac \\ fs[])
  >- (rpt strip_tac \\ last_x_assum match_mp_tac
      \\ fs[] \\ asm_exists_tac \\ fs[])
  >- (ntac 2 (reverse TOP_CASE_TAC \\ fs[])
      >- (rpt strip_tac \\ rveq
          \\ first_x_assum (qspecl_then [`k`, `h`] assume_tac)
          \\ fs[]
          \\ res_tac \\ fs[]
          \\ qexists_tac `hN` \\ fs[state_component_equality])
      \\ rpt strip_tac \\ rveq \\ fs[state_component_equality]
      \\ res_tac \\ fs[state_component_equality])
  >- (reverse TOP_CASE_TAC \\ fs[] >- solve_simple
      \\ TOP_CASE_TAC \\ fs[] \\ solve_simple)
QED

  local
    val eval_fp_opt_add_bind = hd (CONJ_LIST 2 (SIMP_RULE std_ss [] evaluate_fp_opt_add_bind));
  in
Theorem evaluate_fp_opt_add_bind_preserving:
  ! (st1 st2:'ffi state) env xs r k h.
    evaluate st1 env xs = (st2, r) /\
    st2.fp_choices - st1.fp_choices < k /\
    (! m. m < k ==> h m = st1.fp_opts m) ==>
    ? hN.
      evaluate (st1 with fp_opts := h) env xs =
        (st2 with fp_opts := hN, r) /\
      (! m. m < (k - (st2.fp_choices - st1.fp_choices)) ==> hN m = st2.fp_opts m) /\
      (hN (k - (st2.fp_choices - st1.fp_choices)) = h k)
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac eval_fp_opt_add_bind)
  \\ pop_assum (fn asm => first_assum (mp_then Any assume_tac asm)) \\ fs[]
  \\ res_tac
  \\ ntac 2 (pop_assum kall_tac) \\ fs[state_component_equality]
  \\ first_assum (mp_then Any assume_tac eval_fp_opt_inv)
  \\ last_assum (mp_then Any assume_tac eval_fp_opt_inv)
  \\ fs[] \\ conj_tac \\ rpt strip_tac
  \\ rpt (qpat_x_assum `! x. _ = _` (fn thm => fs[GSYM thm]))
QED
  end;
end;

Theorem fpOp_determ:
  ! op refs refsN (ffi1 ffi1':'a ffi_state) (ffi2:'b ffi_state) r vl.
    isFpOp op /\
    do_app (refs, ffi1) op vl = SOME ((refsN, ffi1'), r) ==>
    do_app (refs, ffi2) op vl = SOME ((refsN, ffi2), r)
Proof
  rpt strip_tac \\ Cases_on `op` \\ fs[astTheory.isFpOp_def]
  \\ rpt (qpat_x_assum `do_app _ _ _ = _` mp_tac)
  \\ fs[do_app_def]
  \\ rpt (TOP_CASE_TAC \\ fs[])
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
