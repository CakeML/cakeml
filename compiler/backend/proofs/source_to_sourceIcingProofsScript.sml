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

val isPureOp_simp =
  LIST_CONJ (map (fn (t, c) => EVAL (``isPureOp ^t``))
    (isPureOp_def |> concl |> dest_forall |> snd
                  |> dest_eq |> snd |> TypeBase.dest_case |> #3));

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
    ``\ (s1:'ffi state) env expl.
        ! s2 r.
          evaluate s1 env expl = (s2, r) ==>
          isPureExpList expl /\
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'ffi state).
            s.fp_rws = s1.fp_rws /\
            (! x. x <= (s2.fp_choices - s1.fp_choices) ==> s.fp_opts x = s1.fp_opts x) ==>
            ? fpOpts.
              evaluate s env expl =
                (s with <| fp_opts := fpOpts; fp_choices := s.fp_choices + (s2.fp_choices - s1.fp_choices) |>, r)``;
  val eval_match_goal =
    ``\ (s1:'ffi state) env v pl err_v.
        ! s2 r.
          isPurePatExpList pl /\
          evaluate_match s1 env v pl err_v = (s2, r) ==>
          r <> Rerr (Rabort Rtype_error) ==>
          ! (s:'ffi state).
            s.fp_rws = s1.fp_rws /\
            (! x. x <= (s2.fp_choices - s1.fp_choices) ==> s.fp_opts x = s1.fp_opts x) ==>
              ? fpOpts.
              evaluate_match s env v pl err_v =
                (s with <| fp_opts := fpOpts; fp_choices := s.fp_choices + (s2.fp_choices - s1.fp_choices) |>, r)``;
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
    \\ res_tac \\ fs[state_component_equality];
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
  \\ TRY (fs[state_component_equality] \\ NO_TAC)
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
    \\ qmatch_goalsub_abbrev_tac `evaluate sNew env [_]`
    \\ first_x_assum (qspec_then `sNew` resolve_simple)
    \\ unabbrev_all_tac \\ fs[state_component_equality]
    \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ first_x_assum impl_subgoal_tac
    >- fp_inv_tac
    \\ imp_res_tac evaluate_fp_opts_inv \\ rveq \\ fs[state_component_equality])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspec_then `s` impl_subgoal_tac)
    \\ TRY (rpt conj_tac \\ fp_inv_tac \\ NO_TAC)
    \\ fs[]
    \\ rpt (first_x_assum (fn ithm => first_x_assum (fn thm => mp_then Any assume_tac thm ithm)))
    \\ qmatch_goalsub_abbrev_tac `evaluate sNew env _`
    \\ first_x_assum (qspec_then `sNew` resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ fs[state_component_equality])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspec_then `s` resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- (rpt conj_tac \\ fp_inv_tac)
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate_match sNew env _ _ _`
    \\ first_x_assum impl_subgoal_tac >- fs[]
    \\ first_x_assum (qspec_then `sNew` resolve_simple)
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ fs[state_component_equality]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[]
        \\ first_x_assum drule
        \\ disch_then (qspec_then `s with fp_canOpt := T` assume_tac)
        \\ fs[state_component_equality]
        \\ res_tac  \\ fs[state_component_equality])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ res_tac
    \\ last_x_assum (qspec_then `s with fp_canOpt := T` assume_tac)
    \\ fs[state_component_equality]
    \\ res_tac \\ fs[state_component_equality])
  >- (TOP_CASE_TAC \\ trivial)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[]
    \\ first_x_assum drule
    \\ disch_then impl_subgoal_tac
    \\ TRY (fp_inv_tac \\ NO_TAC)
    \\ fs[state_component_equality]
    \\ rename [`do_log lop (HD v) e2 = SOME (Exp eR)`]
    \\ `eR = e2`
        by (qpat_x_assum `do_log _ _ _ = SOME (Exp eR)` mp_tac
            \\ fs[do_log_def]
            \\ rpt (TOP_CASE_TAC \\ fs[]))
    \\ rveq
    \\ first_x_assum drule \\ disch_then assume_tac
    \\ qmatch_goalsub_abbrev_tac `evaluate sNew env _ = _`
    \\ first_x_assum (qspec_then `sNew` impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- (fs[] \\ fp_inv_tac)
    \\ fs[state_component_equality]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    >- (rveq \\ fs[isPureOp_def])
    \\ ntac 3 (reverse TOP_CASE_TAC \\ fs[])
    \\ imp_res_tac isPureOp_same_ffi \\ rveq
    \\ first_x_assum (qspec_then `s` assume_tac)
    \\ TOP_CASE_TAC \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
    \\ first_x_assum impl_subgoal_tac
    \\ TRY (fp_inv_tac)
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[shift_fp_opts_def, state_component_equality]
    \\ rpt (qpat_x_assum `! x. _ x = _ x` ( fn thm => fs[GSYM thm])))
  >- (
    TOP_CASE_TAC \\ fs[]
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq
    \\ first_x_assum drule \\ disch_then impl_subgoal_tac
    >- fp_inv_tac
    \\ fs[state_component_equality])
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[]) >- trivial
    \\ rpt strip_tac \\ fs[]
    \\ first_x_assum (qspec_then `s` impl_subgoal_tac)
    >- fp_inv_tac
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate sNew _ _ = _`
    \\ first_x_assum impl_subgoal_tac \\ fs[]
    \\ first_x_assum (qspec_then `sNew` impl_subgoal_tac)
    \\ unabbrev_all_tac
    >- fp_inv_tac
    \\ fs[state_component_equality]
    \\ fp_inv_tac)
  >- (
    ntac 2 (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ fs[]
    \\ imp_res_tac (hd (CONJ_LIST 2 (EVAL_RULE isPurePat_ignores_ref)))
    \\ fs[]
    \\ res_tac \\ fs[state_component_equality]
    \\ fp_inv_tac)
QED
end

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
  val isPureExp_ignores_state =
    EVAL_RULE isPureExpList_swap_ffi
    |> CONJ_LIST 2
    |> hd
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
  \\ qspec_then `e` assume_tac (ONCE_REWRITE_RULE [DISJ_COMM] fp_add_comm_cases)
  \\ fs[]
  >- (
    qexists_tac `ffi1.fp_opts` \\ fs[state_component_equality]
    \\ imp_res_tac fp_rws_append_comm)
  \\ fs[evaluate_def] \\ rveq
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
  \\ ntac 2 (first_x_assum
      (fn thm => mp_then Any assume_tac isPureExp_ignores_state thm \\ mp_tac thm))
  \\ rpt strip_tac
  \\ fs[shift_fp_opts_def, isPureExp_def]
  \\ rpt (qpat_x_assum `isPureExp _` (fn thm => first_x_assum (fn ithm => mp_then Any assume_tac ithm thm) \\ mp_tac thm))
  \\ first_x_assum (qspec_then `ffi2 with fp_opts := ffi1.fp_opts` assume_tac)
  \\ first_x_assum (qspec_then `ffi1 with fp_opts := ffi2.fp_opts` assume_tac)
  \\ first_x_assum impl_subgoal_tac
  >- (unabbrev_all_tac
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[] \\ rveq \\ fs[])
  \\ first_x_assum impl_subgoal_tac
  >- (unabbrev_all_tac
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[] \\ rveq \\ fs[])
  \\ fs[]
  (* changing state once more for each execution *)
  \\ ntac 2 (first_x_assum
      (fn thm => mp_then Any assume_tac isPureExp_ignores_state thm \\ mp_tac thm))
  \\ rpt strip_tac
  \\ fs[shift_fp_opts_def, isPureExp_def]
  \\ rpt (qpat_x_assum `isPureExp _` (fn thm => first_x_assum (fn ithm => mp_then Any assume_tac ithm thm)))
  \\ qexists_tac
      `\x.
        if (x = (ffi3.fp_choices - ffi1.fp_choices) + 1)
        then [RewriteApp Here (LENGTH ffi1.fp_rws)] ++ ffi1.fp_opts x
        else
        if (x <= ffi3.fp_choices - ffi2.fp_choices)
        then ffi2.fp_opts x
        else ffi1.fp_opts x`
  \\ qmatch_goalsub_abbrev_tac `evaluate (ffi1 with <| fp_rws := fp_rws_comm; fp_opts := fp_opts_comm |>) env [e2]`
  \\ last_x_assum (qspec_then `ffi1 with <| fp_opts := fp_opts_comm |>` impl_subgoal_tac)
  >- (unabbrev_all_tac
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[] \\ rveq \\ fs[])
  \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (hd (CONJ_LIST 2 fp_rws_append_comm)))
  \\ unabbrev_all_tac
  \\ fs[state_component_equality]

  \\ last_x_assum (qspec_then `ffi1 with fp_opts := fp_opts_comm` impl_subgoal_tac)
  >- (fs[] \\ unabbrev_all_tac
      \\ imp_res_tac evaluate_fp_opts_inv \\ rveq \\ rpt conj_tac \\ fs[])
      \\ rpt strip_tac
      \\ rpt (qpat_x_assum `! x. _ x = _ x` (fn thm => fs[GSYM thm]))
      \\ imp_res_tac fp_
























  \\ `? fpOpts. ffi2 = ffi1 with fp_opts := fpOpts`
    by (imp_res_tac isFFIstable_swap_ffi \\ fs[state_component_equality])
  \\ `? fpOpts. ffi3 = ffi1 with fp_opts := fpOpts`
    by (imp_res_tac isFFIstable_swap_ffi \\ fs[state_component_equality])
  \\ rveq

  \\ imp_res_tac eval_fp_opt_inv
  \\ imp_res_tac fp_rws_append_comm

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
