(*
  Correctness proofs for floating-point optimizations
*)

open source_to_sourceIcingTheory fpOptPropsTheory semanticPrimitivesTheory evaluateTheory
     terminationTheory;
open preamble;

val _ = new_theory "source_to_sourceIcingProofs";

Theorem isFFIstable_swap_ffi:
  ! e.
    isFFIstable e ==>
      ! ffi1 env ffi2 r.
        evaluate ffi1 env [e] = (ffi2, r) ==>
        ? fpOpts.
          ffi2 = ffi1 with fp_opts := fpOpts
Proof
  cheat (* FIXME *)
QED

Theorem no_match_word_cond:
  ! w e s1 s2.
    matchesFPcexp (Word w) e s1 = SOME s2 ==> F
Proof
  rpt strip_tac
  \\ Cases_on `e` \\ fs[matchesFPcexp_def]
  \\ rename [`App op l`]
  \\ Cases_on `l` \\ fs[matchesFPcexp_def]
  \\ Cases_on `t` \\ fs[matchesFPcexp_def]
QED

Theorem no_match_var_cond:
  ! n e s1 s2.
    matchesFPcexp (Var n) e s1 = SOME s2 ==> F
Proof
  rpt strip_tac
  \\ Cases_on `e` \\ fs[matchesFPcexp_def]
  \\ rename [`App op l`]
  \\ Cases_on `l` \\ fs[matchesFPcexp_def]
  \\ Cases_on `t` \\ fs[matchesFPcexp_def]
QED

Theorem matchExpr_preserving:
  ! p.
    (! e s1 s2.
     matchesFPexp p e s1 = SOME s2 ==>
      substMonotone s1 s2)
  /\
    (! ce s1 s2.
      matchesFPcexp p ce s1 = SOME s2 ==>
      substMonotone s1 s2)
Proof
  Induct_on `p`
  \\ simp[no_match_word_cond, no_match_var_cond]
  \\ rpt gen_tac \\ TRY conj_tac
  \\ simp[Once matchesFPexp_def, option_case_eq]
  \\ simp[Once matchesFPcexp_def]
  \\ TRY (fs[substMonotone_def] \\ rpt strip_tac \\ imp_res_tac substLookup_substUpdate \\ rveq \\ fs[] \\ NO_TAC)
  \\ rpt gen_tac
  \\ rpt (TOP_CASE_TAC \\ fs[substMonotone_def]) \\ rpt strip_tac \\ fs[substMonotone_def]
  \\ rpt res_tac
QED

Theorem appFPexp_weakening:
  ! p.
    (! e s1 s2.
      substMonotone s1 s2 /\
      appFPexp p s1 = SOME e ==>
      appFPexp p s2 = SOME e) /\
    (! ce s1 s2.
      substMonotone s1 s2 /\
      appFPcexp p s1 = SOME ce ==>
      appFPcexp p s2 = SOME ce)
Proof
  Induct_on `p`
  \\ rpt strip_tac \\ fs[]
  \\ fs[appFPexp_def, appFPcexp_def, pair_case_eq, option_case_eq, substMonotone_def]
  \\ res_tac \\ fs[]
QED

val exprSolve_tac =
  (let
    val thms = CONJ_LIST 2 (SIMP_RULE std_ss [FORALL_AND_THM] appFPexp_weakening)
  in
  (irule (hd thms) ORELSE irule (hd (tl thms)))
  end)
  \\ asm_exists_tac \\ fs[substMonotone_def]
  \\ rpt strip_tac
  \\ imp_res_tac matchExpr_preserving \\ fs[substMonotone_def];

Theorem subst_pat_is_exp:
  ! p.
    (! e s1 s2.
      matchesFPexp p e s1 = SOME s2 ==>
      appFPexp p s2 = SOME e) /\
    (! ce s1 s2.
      matchesFPcexp p ce s1 = SOME s2 ==>
      appFPcexp p s2 = SOME ce)
Proof
  Induct_on `p` \\ rpt gen_tac \\ conj_tac
  \\ rpt gen_tac
  \\ simp[Once matchesFPexp_def]
  \\ simp[Once matchesFPcexp_def, option_case_eq]
  \\ rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ rveq
  \\ fs[Once appFPexp_def, Once appFPcexp_def]
  \\ TRY (imp_res_tac substLookup_substUpdate \\ fs[])
  \\ res_tac \\ fs[]
  \\ rpt conj_tac \\ exprSolve_tac
QED

local
  val eval_goal =
    ``\ (ffi:'ffi state) env el.
        ! res ffi2 opt.
          evaluate ffi env el = (ffi2, res) ==>
          evaluate (ffi with fp_rws := ffi.fp_rws ++ [opt]) env el =
            (ffi2 with fp_rws := ffi2.fp_rws ++ [opt], res)``
  val eval_match_goal =
    ``\ (ffi:'ffi state) env v pl err_v.
        ! res ffi2 opt.
          evaluate_match ffi env v pl err_v = (ffi2, res) ==>
          evaluate_match (ffi with fp_rws := ffi.fp_rws ++ [opt]) env v pl err_v =
            (ffi2 with fp_rws := ffi2.fp_rws ++ [opt], res)``
  val indThm = terminationTheory.evaluate_ind
    |> ISPEC eval_goal |> SPEC eval_match_goal
in
Theorem evaluate_fp_rws_append:
  (! (ffi:'ffi state) env el.
    ^eval_goal ffi env el) /\
  (! (ffi:'ffi state) env v pl err_v.
    ^eval_match_goal ffi env v pl err_v)
Proof
  match_mp_tac indThm
  \\ rpt strip_tac \\ fs[evaluate_def] \\ rpt strip_tac \\ rveq \\ fs[]
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ TRY (rpt (TOP_CASE_TAC \\ fs[]) \\ NO_TAC)
  \\ TRY (rpt (TOP_CASE_TAC \\ fs[]) \\ rpt strip_tac \\ rveq
          \\ fs[state_component_equality] \\ NO_TAC)
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ Cases_on `op = Opapp` \\ fs[]
  >- (rveq \\ rpt (TOP_CASE_TAC \\ fs[dec_clock_def]))
  \\ ntac 3 (TOP_CASE_TAC \\ fs[])
  \\ Cases_on `isFpOp op` \\ fs[]
  >- (rpt strip_tac \\ rveq \\ fs[state_component_equality, list_result_def, shift_fp_opts_def]
      \\ Cases_on `isFpBool op` \\ fs[]
      >- (Cases_on `do_fprw r (q.fp_opts 0) q.fp_rws` \\ fs[]
          >- (`do_fprw r (q.fp_opts 0) (q.fp_rws ++ [opt]) = NONE` by (cheat)
              \\ fs[])
          \\ `do_fprw r (q.fp_opts 0) (q.fp_rws ++ [opt]) = SOME x` by (cheat)
          \\ fs[])
      \\ Cases_on `do_fprw r (q.fp_opts 0) q.fp_rws` \\ fs[]
      >- (`do_fprw r (q.fp_opts 0) (q.fp_rws ++ [opt]) = NONE` by (cheat)
          \\ fs[])
      \\ `do_fprw r (q.fp_opts 0) (q.fp_rws ++ [opt]) = SOME x` by (cheat)
      \\ fs[])
  \\ rpt strip_tac \\ fs[state_component_equality]
QED
end

Theorem fp_add_comm_cases:
  ! e.
    (? e1 e2.
      e = (App (FP_bop FP_Add) [e1; e2]) /\
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

Theorem ffi_eq_fp_opts[local]:
  ffi with <| fp_rws := rws |> =
    ffi with <| fp_rws := rws; fp_opts := ffi.fp_opts |>
Proof
  fs[state_component_equality]
QED

local
  val fp_rws_append_comm =
    SIMP_RULE std_ss [Once ffi_eq_fp_opts] evaluate_fp_rws_append
    |> CONJ_LIST 2
    |> map (SPEC_ALL) |> map (GEN ``(opt:fp_pat #fp_pat)``)
    |> map (Q.SPEC `fp_add_comm`) |> map GEN_ALL
    |> LIST_CONJ;
  val eval_fp_opt_inv =
    SIMP_RULE std_ss [] fpSemPropsTheory.evaluate_fp_opts_inv
    |> CONJ_LIST 2 |> hd;
  fun impl_subgoal_tac th =
    let
      val hyp_to_prove = lhand (concl th)
    in
      SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
    end;
in
Theorem fp_add_comm_correct:
  ! (ffi1 ffi2:'ffi state) env e res.
    evaluate ffi1 env [rewriteFPexp [fp_add_comm] e] = (ffi2, Rval res) ==>
    ? (fp_opts:num -> rewrite_app list).
      evaluate
        (ffi1 with <| fp_rws := ffi1.fp_rws ++ [fp_add_comm]; fp_opts := fp_opts |>)
        env [e] =
        (ffi2 with <| fp_rws := ffi2.fp_rws ++ [fp_add_comm] |>, Rval res)
Proof
  rpt strip_tac
  \\ qspec_then `e` assume_tac fp_add_comm_cases
  \\ fs[]
  >- (
    fs[evaluate_def] \\ rveq
    \\ qpat_x_assum `_ = (_, _)` mp_tac
    \\ rename [`evaluate ffi1 env [e1]`]
    \\ Cases_on `evaluate ffi1 env [e1]` \\ fs[]
    \\ rename [`evaluate ffi1 env [e1] = (ffi2, r)`] \\ Cases_on `r` \\ fs[]
    \\ rename [`evaluate ffi2 env [e2]`]
    \\ Cases_on `evaluate ffi2 env [e2]` \\ fs[]
    \\ rename [`evaluate ffi2 env [e2] = (ffi3, r)`] \\ Cases_on `r` \\ fs[]
    \\ ntac 3 (TOP_CASE_TAC \\ fs[])
    \\ fs[astTheory.isFpOp_def, astTheory.isFpBool_def]
    \\ rpt strip_tac \\ rveq
    \\ fs[shift_fp_opts_def]
    \\ `isFFIstable e1 /\ isFFIstable e2` by (cheat)
    \\ `? fpOpts. ffi2 = ffi1 with fp_opts := fpOpts`
      by (imp_res_tac isFFIstable_swap_ffi)
    \\ imp_res_tac eval_fp_opt_inv
    \\ imp_res_tac fp_rws_append_comm
    \\ qexists_tac
        `\x.
          if (x = (ffi3.fp_choices - ffi1.fp_choices) + 1)
          then [RewriteApp Here (LENGTH ffi1.fp_rws)] ++ ffi1.fp_opts x
          else ffi1.fp_opts x`
    \\ qmatch_goalsub_abbrev_tac `evaluate ffi1upd env [e2]`
    \\ qpat_x_assum `evaluate ffi1 _ _ = _` kall_tac
    \\ qpat_x_assum `evaluate ffi2 _ _ = _` kall_tac
    \\ last_x_assum (mp_then Any assume_tac fpSemPropsTheory.evaluate_fp_opt_add_bind_preserving)
    \\ first_x_assum (qspecl_then [`(ffi3.fp_choices - ffi1.fp_choices) +1`, `ffi1upd.fp_opts`] impl_subgoal_tac)
    >- (rpt conj_tac \\ fs[state_component_equality]
        \\ rpt strip_tac \\ unabbrev_all_tac
        \\ qpat_x_assum `! x. _ = ffi2.fp_opts _` (fn thm => fs[GSYM thm])
 \\ fs[state_component_equality])
    \\ unabbrev_all_tac
    \\ fs[state_component_equality]
    \\ qpat_assum `ffi2.fp_rws = ffi3.fp_rws` (fn thm => fs[GSYM thm])
    \\ qpat_assum `ffi1.fp_rws = ffi2.fp_rws` (fn thm => fs[GSYM thm])
    \\ disch_then impl_subgoal_tac

    \\ cheat (* qexists_tac `` fp_opts should 1. do decisions of ffi1, then ffi2, then ffi3 + comm *)
    )
  \\ fs[]
  \\ qexists_tac `ffi1.fp_opts` \\ fs[state_component_equality]
  \\ imp_res_tac fp_rws_append_comm
QED

val _ = export_theory ();
