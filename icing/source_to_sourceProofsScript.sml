(*
  Correctness proofs for floating-point optimizations
*)
open icing_rewriterTheory source_to_sourceTheory fpOptTheory fpOptPropsTheory
     fpSemPropsTheory semanticPrimitivesTheory evaluateTheory
     semanticsTheory semanticsPropsTheory
     evaluatePropsTheory terminationTheory fpSemPropsTheory mllistTheory;
     local open ml_progTheory in end;
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
load "Unify";
fun join_hyps th =
 let open pairSyntax
     val (asl,c) = dest_thm th
     val frozen = free_varsl asl
     val ants = fst(strip_imp (snd (strip_forall c)))
     val eqns = filter is_eq ants
     val (L,R) = unzip (map dest_eq eqns)
     val theta = Unify.simp_unify_terms frozen
                        (list_mk_pair L) (list_mk_pair R)
 in
   SIMP_RULE std_ss [] (GEN_ALL (INST theta (SPEC_ALL th)))
 end

val choice_mono =
  (CONJUNCT1 evaluate_fp_opts_inv) |> SPEC_ALL |> UNDISCH |> CONJUNCTS |> el 3 |> DISCH_ALL;

(* TODO: might be available somewhere *)
Theorem evaluate_add_choices:
  (! (s1:'a semanticPrimitives$state) env e s2 r choices.
    evaluate s1 env e = (s2, r) ==>
    evaluate (s1 with fp_state := s1.fp_state with choices := choices) env e =
      (s2 with fp_state:=s2.fp_state with choices:= choices + s2.fp_state.choices - s1.fp_state.choices,r)) ∧
  (! (s1:'a semanticPrimitives$state) env v pes errv s2 r choices.
    evaluate_match s1 env v pes errv = (s2, r) ==>
     evaluate_match (s1 with fp_state := s1.fp_state with choices := choices) env v pes errv =
      (s2 with fp_state:=s2.fp_state with choices:= choices + s2.fp_state.choices - s1.fp_state.choices,r))
Proof
  ho_match_mp_tac evaluate_ind \\ rw[]
  \\ rfs[evaluate_def] \\ rveq
  \\ qpat_x_assum `_ = (_,_)` mp_tac
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ simp[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
  \\ imp_res_tac choice_mono \\ simp[]
  \\ res_tac \\ fs[dec_clock_def, shift_fp_opts_def]
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

(**
  First, we prove that pure expressions ignore their FFI.
  This allows to swap out the FFI with an arbitrary different one
  and get the same one back from evaluating
**)

Theorem isPureOp_same_ffi:
  ! refs1 (ffi1 ffi2 : 'a ffi_state) op vl refs2 r.
    isPureOp op /\
    do_app (refs1, ffi1) op vl = SOME ((refs2,ffi2), r) ==>
    ! refs (ffi:'b ffi_state).
      do_app (refs, ffi) op vl = SOME ((refs, ffi), r)
Proof
  Cases_on `op` \\ rpt gen_tac \\ strip_tac
  \\ fs[isPureOp_simp, do_app_def, CaseEq"list", CaseEq"lit", CaseEq"option", CaseEq"v",
        PULL_EXISTS, CaseEq"bool", CaseEq"word_size", CaseEq"eq_result"]
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

Theorem can_pmatch_all_same_ffi:
  isPurePatExpList pes /\
  can_pmatch_all env refs (MAP FST pes) v ==>
  ! refs2. can_pmatch_all env refs2 (MAP FST pes) v
Proof
  Induct_on `pes` \\ fs[can_pmatch_all_def]
  \\ rpt gen_tac \\ rpt (disch_then assume_tac)
  \\ Cases_on `h` \\ fs[isPureExp_def]
  \\ metis_tac [isPurePat_ignores_ref]
QED

local
  val eval_goal =
    ``\ (s1:'a semanticPrimitives$state) env expl.
        ! s2 r.
          evaluate s1 env expl = (s2, r) ⇒
          isPureExpList expl ∧
          r <> Rerr (Rabort Rtype_error) ⇒
          ! (s:'b semanticPrimitives$state).
            s.fp_state.rws = s1.fp_state.rws ∧
            s.fp_state.canOpt = s1.fp_state.canOpt ∧
            s.fp_state.real_sem = s1.fp_state.real_sem ∧
            (! x. x <= (s2.fp_state.choices - s1.fp_state.choices) ⇒
              s.fp_state.opts x = s1.fp_state.opts x) ⇒
            ? fpOpts.
              evaluate s env expl =
                (s with <| fp_state := s.fp_state with
                  <| opts := fpOpts; choices := s.fp_state.choices + (s2.fp_state.choices - s1.fp_state.choices)|> |>, r)``;
  val eval_match_goal =
    ``\ (s1:'a semanticPrimitives$state) env v pl err_v.
        ! s2 r.
          isPurePatExpList pl ∧
          evaluate_match s1 env v pl err_v = (s2, r) ⇒
          r <> Rerr (Rabort Rtype_error) ⇒
          ! (s:'b semanticPrimitives$state).
            s.fp_state.rws = s1.fp_state.rws ∧
            s.fp_state.canOpt = s1.fp_state.canOpt ∧
            s.fp_state.real_sem = s1.fp_state.real_sem ∧
            (! x. x <= (s2.fp_state.choices - s1.fp_state.choices) ⇒
              s.fp_state.opts x = s1.fp_state.opts x) ⇒
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
    \\ TOP_CASE_TAC \\ fs[]
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ first_x_assum (qspecl_then [`s`] resolve_simple)
    \\ disch_then impl_subgoal_tac
    >- (rpt conj_tac \\ fp_inv_tac)
    \\ fs[]
    \\ qmatch_goalsub_abbrev_tac `evaluate_match s_fpNew env _ _ _`
    \\ first_x_assum impl_subgoal_tac >- fs[]
    \\ first_x_assum (qspecl_then [`s_fpNew`] resolve_simple)
    \\ imp_res_tac can_pmatch_all_same_ffi \\ fs[]
    \\ unabbrev_all_tac
    \\ disch_then impl_subgoal_tac
    \\ TRY (rpt conj_tac \\ fp_inv_tac)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ fp_inv_tac)
  >- (
    ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    >- (rpt strip_tac \\ rveq \\ fs[]
        \\ first_x_assum drule
        \\ disch_then (qspec_then
            `s with fp_state := if st.fp_state.canOpt = Strict then s.fp_state else s.fp_state with canOpt := FPScope annot` impl_subgoal_tac)
        >- (fs[fpState_component_equality]
            \\ Cases_on ‘st.fp_state.canOpt = Strict’ \\ fs[])
        \\ fs[fpState_component_equality, semState_comp_eq]
        \\ Cases_on ‘st.fp_state.canOpt = Strict’ \\ fs[])
    \\ rpt strip_tac \\ rveq \\ fs[isPureExpList_Cons_thm]
    \\ res_tac
    \\ last_x_assum (qspec_then
         `s with fp_state := if st.fp_state.canOpt = Strict then s.fp_state else s.fp_state with canOpt := FPScope annot` assume_tac)
    \\ Cases_on ‘st.fp_state.canOpt = Strict’ \\ fs[fpState_component_equality]
    \\ res_tac \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
   TOP_CASE_TAC \\ rpt strip_tac \\ rveq
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
    \\ Cases_on ‘getOpClass op = FunApp’ \\ fs[]
    >- (Cases_on ‘op’ \\ fs[astTheory.getOpClass_def, isPureOp_def])
    \\ ntac 5 (reverse TOP_CASE_TAC \\ fs[])
    \\ imp_res_tac isPureOp_same_ffi
    \\ first_x_assum (qspecl_then [`s`] assume_tac)
    \\ rename [`evaluate st env (REVERSE es) = (s2, Rval _)`]
    \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
    (* Reals *)
    >- (
      first_x_assum impl_subgoal_tac >- fp_inv_tac
      \\ imp_res_tac evaluate_fp_opts_inv
      \\ fs[shift_fp_opts_def, semState_comp_eq, fpState_component_equality]
      \\ rpt (qpat_x_assum `! x. _ x = _ x` ( fn thm => fs[GSYM thm])))
    (* Icing 1 *)
    >- (
     fs[]
     \\ TOP_CASE_TAC \\ Cases_on `s.fp_state.canOpt = FPScope Opt`
     \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
     \\ first_x_assum impl_subgoal_tac
     THENL [fp_inv_tac, ALL_TAC, fp_inv_tac, ALL_TAC]
     \\ imp_res_tac evaluate_fp_opts_inv
     \\ fs[shift_fp_opts_def, semState_comp_eq, fpState_component_equality])
    (* Icing 2 *)
    >- (
     fs[]
     \\ TOP_CASE_TAC \\ Cases_on `s.fp_state.canOpt = FPScope Opt`
     \\ fs[] \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
     \\ first_x_assum impl_subgoal_tac
     THENL [fp_inv_tac, ALL_TAC, fp_inv_tac, ALL_TAC]
     \\ imp_res_tac evaluate_fp_opts_inv
     \\ fs[shift_fp_opts_def, semState_comp_eq, fpState_component_equality]
     \\ rpt (qpat_x_assum `! x. _ x = _ x` ( fn thm => fs[GSYM thm])))
    (* Simple case *)
    \\ TOP_CASE_TAC
    \\ first_x_assum impl_subgoal_tac >- fp_inv_tac
    \\ imp_res_tac evaluate_fp_opts_inv
    \\ fs[shift_fp_opts_def, semState_comp_eq, fpState_component_equality])
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
  ! st1 st2 env e r.
    isPureExp e /\
    r <> Rerr (Rabort Rtype_error) /\
    evaluate st1 env [e] = (st2, r) ==>
    st2 = st1 with fp_state := st2.fp_state
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac
       (INST_TYPE[beta|->alpha](CONJUNCT1 (SIMP_RULE std_ss [] isPureExpList_swap_ffi))))
  \\ first_x_assum (qspecl_then [`st1`] impl_subgoal_tac)
  \\ fs[isPureExp_def] \\ fs[fpState_component_equality, semState_comp_eq]
QED

val prep = fn thm => SIMP_RULE std_ss [] thm;

val optUntil_tac =
  fn t1 => fn t2 =>
    qpat_x_assum t1 (mp_then Any mp_tac (CONJUNCT1 optUntil_evaluate_ok))
    \\ disch_then (qspec_then t2 assume_tac) \\ fs[];

val optUntil_match_tac =
  fn t1 => fn t2 =>
    qpat_x_assum t1 (mp_then Any mp_tac (CONJUNCT2 optUntil_evaluate_ok))
    \\ disch_then (qspec_then t2 assume_tac) \\ fs[];

Theorem isPureExpList_swap_state:
  ∀ s1 env expl r.
    evaluate s1 env expl = (s1, r) ⇒
    ~ s1.fp_state.real_sem ∧
    s1.fp_state.canOpt = FPScope Opt ∧
    isPureExpList expl ∧
    r ≠ Rerr (Rabort Rtype_error) ⇒
    ∀ (s:'b semanticPrimitives$state).
      evaluate s env expl = (s, r)
Proof
  simp[] \\ rpt strip_tac
  \\ last_x_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_fp_intro_canOpt_true))
  \\ fs[]
  \\ disch_then (qspec_then ‘s.fp_state’ assume_tac)
  \\ first_x_assum (mp_then Any mp_tac (CONJUNCT1 (prep isPureExpList_swap_ffi)))
  \\ disch_then (qspec_then ‘s’ mp_tac)
  \\ fs[fpState_component_equality, semState_comp_eq]
  \\ rpt strip_tac
  \\ optUntil_tac ‘evaluate s env expl = _’ ‘s.fp_state.opts’
  \\ fs[optUntil_def, fpState_component_equality, semState_comp_eq]
  \\ ‘(λ x. s.fp_state.opts x) = s.fp_state.opts’ by fs[FUN_EQ_THM]
  \\ pop_assum (fs o single)
  \\ ‘s with fp_state := s.fp_state with opts := s.fp_state.opts = s’
     by (fs[fpState_component_equality, semState_comp_eq])
  \\ pop_assum (fs o single)
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

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
    (stN1.fp_state.canOpt = st1.fp_state.canOpt) ∧
    (stN1.fp_state.real_sem ⇔ st1.fp_state.real_sem) ==>
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
  \\ first_x_assum (mp_then Any assume_tac (INST_TYPE[beta|->alpha](prep (CONJUNCT1 isPureExpList_swap_ffi))))
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

Definition isRealValuedID_rewriteFPexp_def:
  isRealValuedID_rewriteFPexp ((s,t):fp_pat#fp_pat) (st1:'a semanticPrimitives$state) st2 env e r ⇔
  evaluate st1 env [realify (rewriteFPexp [(s,t)] e)] = (st2, Rval [Real r]) ⇒
  evaluate st1 env [realify e] = (st2, Rval [Real r])
End

(* Correctness definition for rewriteFPexp
 We need to handle the case where the expression returns an error, but we cannot
 preserve the exact error, as reordering may change which error is returned *)
Definition is_rewriteFPexp_correct_def:
  is_rewriteFPexp_correct rws (st1:'a semanticPrimitives$state) st2 env e r =
    (evaluate st1 env [rewriteFPexp rws e] = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = F ⇒
     ∃ fpOpt choices fpOptR choicesR.
      evaluate
        (st1 with fp_state := st1.fp_state with
           <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env [e] =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r))
End

Definition is_rewriteFPexp_list_correct_def:
  is_rewriteFPexp_list_correct rws (st1:'a semanticPrimitives$state) st2 env exps r =
    (evaluate st1 env (MAP (rewriteFPexp rws) exps) = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = F ⇒
     ∃ fpOpt choices fpOptR choicesR.
       evaluate
         (st1 with fp_state := st1.fp_state with
            <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env exps =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r))
End

Theorem empty_rw_correct:
   ∀ (st1 st2:'a semanticPrimitives$state) env e r.
     is_rewriteFPexp_correct [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_rewriteFPexp_correct_def, rewriteFPexp_def]
  \\ rpt strip_tac \\ qexists_tac `st1.fp_state.opts`
  \\ qexists_tac ‘st1.fp_state.choices’
  \\ `st1 = st1 with fp_state := st1.fp_state with
          <| rws := st1.fp_state.rws; opts := st1.fp_state.opts; choices := st1.fp_state.choices |>`
      by (fs[semState_comp_eq, fpState_component_equality])
  \\ pop_assum (fn thm => fs[GSYM thm])
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

Theorem choices_simp:
  st.fp_state with choices := st.fp_state.choices = st.fp_state
Proof
  fs[fpState_component_equality]
QED

Theorem rewriteExp_compositional:
  ∀ rws opt.
   (∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct rws st1 st2 env e r) ∧
   (∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_rewriteFPexp_correct [opt] st1 st2 env e r) ⇒
  ∀ (st1 st2:'a semanticPrimitives$state) env e r.
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
    \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘st1.fp_state.choices’
    \\ fs[semState_comp_eq, fpState_component_equality, choices_simp])
  \\ TOP_CASE_TAC \\ fs[]
  >- (
    rpt strip_tac
    \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
    \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
    \\ fs[fpState_component_equality]
    \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘choices’
    \\ fs[semState_comp_eq, fpState_component_equality])
  \\ TOP_CASE_TAC \\ fs[]
  >- (
   rpt strip_tac
   \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
   \\ first_x_assum (qspecl_then [`[(opt0, opt1)]`, `\x. []`] assume_tac) \\ fs[]
   \\ first_x_assum (fn thm => (first_x_assum (fn ithm => mp_then Any impl_subgoal_tac ithm thm)))
   \\ fs[fpState_component_equality] \\ asm_exists_tac \\ fs[]
   \\ TOP_CASE_TAC \\ fs[]
   \\ qexists_tac ‘fpOptR’ \\ fs[semState_comp_eq, fpState_component_equality])
  \\ rpt strip_tac \\ fs[]
  \\ first_x_assum drule \\ fs[state_component_equality, fpState_component_equality]
  \\ fs[PULL_EXISTS] \\ rpt gen_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate st1N env [_] = (st2N, Rval r2)`
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [`st1N`, `st2N`, `env`, `e`, `r2`] assume_tac)
  \\ fs[rewriteFPexp_def] \\ rfs[]
  \\ unabbrev_all_tac \\ fs[state_component_equality, fpState_component_equality]
  \\ first_x_assum impl_subgoal_tac \\ fs[]
  \\ first_x_assum (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_up)))
  \\ first_x_assum (qspec_then `st1.fp_state.rws  ++ [(opt0, opt1)] ++ rws` impl_subgoal_tac)
  >- (fs[SUBSET_DEF] \\ rpt strip_tac \\ fs[])
  \\ fs[] \\ qexists_tac `fpOpt''` \\ qexists_tac ‘choices'’ \\ fs[]
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
QED

Theorem lift_rewriteFPexp_correct_list_strong:
  ∀ rws (st1 st2:'a semanticPrimitives$state) env exps r.
    (∀ (st1 st2: 'a semanticPrimitives$state) env e r.
      is_rewriteFPexp_correct rws st1 st2 env e r) ⇒
  is_rewriteFPexp_list_correct rws st1 st2 env exps r
Proof
  Induct_on `exps`
  \\ fs[is_rewriteFPexp_correct_def, is_rewriteFPexp_list_correct_def]
  >- (rpt strip_tac \\ qexists_tac ‘st1.fp_state.opts’
      \\ fs[semState_comp_eq, fpState_component_equality])
  \\ rpt strip_tac \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ simp[Once evaluate_cons]
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ first_assum (qspecl_then [`st1`, `q`, `env`, `h`, `a`] impl_subgoal_tac)
  \\ simp[Once evaluate_cons] \\ fs[] \\ rveq
  \\ first_x_assum (mp_then Any assume_tac (CONJUNCT1 optUntil_evaluate_ok))
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then assume_tac \\ fs[]
  \\ first_x_assum impl_subgoal_tac
  \\ TRY (imp_res_tac evaluate_fp_opts_inv \\ fs[] \\ NO_TAC)
  \\ fs[]
  \\ first_x_assum (qspec_then `fpOpt'` assume_tac) \\ fs[]
  \\ qexists_tac `optUntil (choicesR - choices) fpOpt fpOpt'`
  \\ qexists_tac ‘choices’ \\ fs[]
  \\ qpat_x_assum `evaluate _ _ exps = _`
                  (mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices))
  \\ first_x_assum (qspec_then ‘choicesR’ assume_tac)
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

Theorem lift_rewriteFPexp_correct_list:
  ∀ rws.
    (∀ (st1 st2: 'a semanticPrimitives$state) env e r.
      is_rewriteFPexp_correct rws st1 st2 env e r) ⇒
    ∀ (st1 st2:'a semanticPrimitives$state) env exps r.
    is_rewriteFPexp_list_correct rws st1 st2 env exps r
Proof
  rpt strip_tac \\ drule lift_rewriteFPexp_correct_list_strong
  \\ disch_then irule
QED

Definition is_optimise_correct_def:
  is_optimise_correct rws (st1:'a semanticPrimitives$state) st2 env cfg exps r =
    (evaluate st1 env
             (MAP (optimise (cfg with optimisations := rws)) exps) = (st2, Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    (~ st1.fp_state.real_sem) ==>
    ∃ fpOpt choices fpOptR choicesR.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env exps =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r))
End

Definition is_optimise_with_plan_correct_def:
  is_optimise_with_plan_correct (st1:'a semanticPrimitives$state) st2 env cfg plan exps r =
  (evaluate st1 env
   (MAP (optimise_with_plan cfg plan) exps) = (st2, Rval r) ∧
   (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
   st1.fp_state.canOpt ≠ Strict ∧
   (~ st1.fp_state.real_sem) ⇒
   ∃ fpOpt choices fpOptR choicesR.
     evaluate (st1 with fp_state := st1.fp_state with
                                       <| rws := st1.fp_state.rws ++ FLAT (MAP SND plan);
                                          opts := fpOpt; choices := choices |>) env exps =
     (st2 with fp_state := st2.fp_state with
                              <| rws := st2.fp_state.rws ++ FLAT (MAP SND plan);
                                 opts := fpOptR; choices := choicesR |>, Rval r))
End

Theorem MAP_FST_optimise:
  MAP FST (MAP (\ (p, e). (p, optimise cfg e)) l) = MAP FST l
Proof
  Induct_on `l` \\ fs[] \\ rpt strip_tac \\ PairCases_on `h` \\ fs[]
QED

Theorem Map_FST_optimise_with_plan:
  MAP FST (MAP (\ (p, e). (p, optimise_with_plan cfg plan e)) l) = MAP FST l
Proof
  Induct_on ‘l’ \\ fs[] \\ rpt strip_tac \\ PairCases_on ‘h’ \\ fs[]
QED

Theorem optimise_empty_sing:
  ∀ cfg e. optimise (cfg with optimisations := []) e = e
Proof
  ho_match_mp_tac optimise_ind
  \\ rpt strip_tac \\ fs[optimise_def]
                        (*
  >- (
   Induct_on ‘pes’ \\ fs[optimise_def]
   \\ rpt strip_tac \\ fs[]
   >- (Cases_on ‘h’ \\ fs[])
   \\ first_x_assum irule
   \\ rpt strip_tac \\ res_tac) *)
  >- (Induct_on `exps` \\ fs[optimise_def])
  >- (
   fs[rewriteFPexp_def]
   \\ Induct_on `exps` \\ fs[optimise_def])
  >- (
   Induct_on ‘pes’ \\ fs[optimise_def]
   \\ rpt strip_tac \\ fs[]
   >- (Cases_on ‘h’ \\ fs[])
   \\ first_x_assum irule
   \\ rpt strip_tac \\ res_tac)
QED
(*
  \\ Induct_on ‘ses’ \\ fs[optimise_def]
  \\ rpt strip_tac \\ fs[]
  >- (Cases_on ‘h’ \\ Cases_on ‘r’ \\ fs[])
  \\ first_x_assum irule \\ rpt strip_tac
  \\ res_tac
QED *)

Theorem optimise_with_plan_empty_sing:
  ∀ cfg e. optimise_with_plan cfg [] e = e
Proof
  fs[optimise_with_plan_def]
QED

Theorem optimise_empty:
  ∀ exps cfg. MAP (optimise (cfg with optimisations := [])) exps = exps
Proof
  Induct_on ‘exps’ \\ rpt strip_tac
  >- (EVAL_TAC)
  \\ rpt strip_tac \\ fs[optimise_def, optimise_empty_sing]
QED

Theorem optimise_with_plan_empty:
  ∀ exps cfg. MAP (optimise_with_plan cfg []) exps = exps
Proof
  Induct_on ‘exps’ \\ rpt strip_tac
  >- (EVAL_TAC)
  \\ rpt strip_tac \\ fs[optimise_with_plan_def, optimise_with_plan_empty_sing]
QED

Theorem optimise_pat_empty:
  ∀ pl cfg. MAP (λ (p,e). (p, optimise (cfg with optimisations := []) e)) pl = pl
Proof
  Induct_on ‘pl’ \\ rpt strip_tac >- (EVAL_TAC)
  \\ fs[] \\ Cases_on ‘h’ \\ fs[optimise_empty_sing]
QED

Theorem optimise_with_plan_pat_empty:
  ∀ pl cfg. MAP (λ (p,e). (p, optimise_with_plan cfg [] e)) pl = pl
Proof
  Induct_on ‘pl’ \\ rpt strip_tac >- (EVAL_TAC)
  \\ fs[] \\ Cases_on ‘h’ \\ fs[optimise_with_plan_empty_sing]
QED

Theorem fpState_upd_id:
  ∀ s.
    s with fp_state :=
      s.fp_state with <| rws := s.fp_state.rws; opts := s.fp_state.opts |> = s
Proof
  rpt strip_tac
  \\ ‘s.fp_state with <| rws := s.fp_state.rws; opts := s.fp_state.opts |> = s.fp_state’
     by (fs[fpState_component_equality])
  \\ pop_assum (rewrite_tac o single)
  \\ fs[semanticPrimitivesTheory.state_component_equality]
QED

Triviality MAP_MAP_triple:
  ∀ l f. MAP (λ (x,y,z). x) (MAP (λ (s1,s2,e). (s1,s2,f e)) l) = MAP (λ (x,y,z). x) l
Proof
  Induct_on ‘l’ \\ fs[] \\ rpt strip_tac
  \\ Cases_on ‘h’ \\ fs[] \\ Cases_on ‘r’ \\ fs[]
QED

local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
     ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r.
     (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
       is_rewriteFPexp_list_correct rws st1 st2 env exps r) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt ≠ Strict ∧
     ~st1.fp_state.real_sem ∧
     evaluate st1 env [optimise (cfg with optimisations := rws) e] = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env [e]=
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)”
  (* P4: string * exp -> bool *)
  val P4 =
  Parse.Term (‘λ (s:string, e). ^P0 e’);
  (* P2: string * string * exp -> bool *)
  val P2 =
  Parse.Term (‘λ (s1:string, s2:string, e). ^P0 e’);
  (* Letrec goal *)
  val P1 =
  Parse.Term (‘λ (l:(string # string # exp) list).
  ∀ p. MEM p l ⇒ ^P2 p’)
  (* P5: pat * exp -> bool *)
  val P5 =
  Parse.Term (‘λ (p:pat, e). ^P0 e’)
  (* P3: pat * exp list -> bool *)
  val P3 =
  Parse.Term (‘λ (l:(pat # exp) list).
     ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r v err_v.
     (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
       is_rewriteFPexp_list_correct rws st1 st2 env exps r) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt ≠ Strict ∧
     ~st1.fp_state.real_sem ∧
     evaluate_match st1 env v (MAP (λ (p,e). (p, optimise (cfg with optimisations := rws) e)) l) err_v = (st2, Rval r) ⇒
     ∃ fpOpt choices fpOptR choicesR.
       evaluate_match
         (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>)
         env v l err_v =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)’);
  (* P6: exp list -> bool *)
  val P6 =
    Parse.Term (‘λ (es:ast$exp list). ∀ e. MEM e es ⇒ ^P0 e’);
  val ind_thm =
    astTheory.exp_induction |> SPEC P0 |> SPEC P1 |> SPEC P2 |> SPEC P3
    |> SPEC P4 |> SPEC P5 |> SPEC P6;
  val trivial_tac =
    rpt strip_tac \\ rveq
    \\ last_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ qexists_tac ‘fpOpt’
    \\ fs[state_component_equality, fpState_component_equality]
    \\ rveq
    \\ qexists_tac ‘fpOptR’ \\ fs[];
  val get_ext_eval_tac = fn t =>
    qpat_x_assum t (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ rpt (disch_then drule)
    \\ strip_tac
  val arith_case_tac = fn t =>
     rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac t \\ rfs[]
     \\ TOP_CASE_TAC \\ fs[];
in

Triviality lift_P6_REVERSE:
  ∀ es.
    ^P6 es ⇒
    ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
      is_rewriteFPexp_list_correct rws st1 st2 env exps r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    ~st1.fp_state.real_sem ∧
    evaluate st1 env (MAP (λ e. optimise (cfg with optimisations := rws) e) (REVERSE es)) = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate
        (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>)
        env (REVERSE es) =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)
Proof
  simp[] \\ Induct_on ‘es’ \\ rpt strip_tac
  >- (fs[evaluate_def] \\ qexists_tac ‘st2.fp_state.opts’
      \\ fs[semState_comp_eq, fpState_component_equality])
  \\ fs[evaluate_append]
  \\ pop_assum mp_tac
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ get_ext_eval_tac ‘evaluate st1 env (MAP _ _) = _’
  \\ pop_assum mp_tac \\ impl_tac
  >- (rpt strip_tac \\ fs[]
      \\ qpat_x_assum ‘∀ e. (e = h ∨ MEM e es) ⇒ _’ mp_tac
      \\ disch_then (qspec_then ‘e’ mp_tac) \\ impl_tac \\ fs[]
      \\ rpt (disch_then drule) \\ strip_tac
      \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
      \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq])
  \\ strip_tac
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum (qspec_then ‘h’ mp_tac) \\ fs[] \\ rveq
  \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧
      q.fp_state.canOpt ≠ Strict ∧ ~ q.fp_state.real_sem’
    by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ rpt (disch_then drule) \\ strip_tac
  \\ optUntil_tac ‘evaluate _ _ (REVERSE es) = _’ ‘fpOpt'’
  \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
  \\ qexists_tac ‘choices’
  \\ qpat_x_assum `evaluate _ _ [h] = _`
                  (mp_then Any assume_tac (CONJUNCT1 evaluate_add_choices))
  \\ first_x_assum (qspec_then ‘choicesR’ assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Triviality lift_P6:
  ∀ es.
    ^P6 es ⇒
    ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
      is_rewriteFPexp_list_correct rws st1 st2 env exps r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    ~st1.fp_state.real_sem ∧
    evaluate st1 env (MAP (λ e. optimise (cfg with optimisations := rws) e) es) = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate
        (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>)
        env es =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)
Proof
  simp[] \\ Induct_on ‘es’ \\ rpt strip_tac
  >- (fs[evaluate_def] \\ qexists_tac ‘st2.fp_state.opts’
      \\ fs[semState_comp_eq, fpState_component_equality])
  \\ pop_assum mp_tac
  \\ simp[Once evaluate_cons]
  \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
  \\ first_assum (qspec_then ‘h’ mp_tac)
  \\ impl_tac \\ fs[]
  \\ rpt (disch_then drule) \\ strip_tac
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ simp[Once evaluate_cons]
  \\ last_x_assum mp_tac  \\ impl_tac
  >- (
   rpt strip_tac \\ fs[]
   \\ qpat_x_assum ‘∀ e. (e = h ∨ MEM e es) ⇒ _’ mp_tac
   \\ disch_then (qspec_then ‘e’ mp_tac) \\ impl_tac \\ fs[]
   \\ rpt (disch_then drule) \\ strip_tac
   \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘choices'’
   \\ fs[semState_comp_eq, fpState_component_equality])
  \\ strip_tac
  \\ get_ext_eval_tac ‘evaluate q env (MAP _ _) = _’
  \\ pop_assum mp_tac \\ impl_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ rveq \\ strip_tac
  \\ optUntil_tac ‘evaluate _ _ [h] = _’ ‘fpOpt'’
  \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
  \\ qexists_tac ‘choices’
  \\ qpat_x_assum ‘evaluate _ _ es = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ disch_then (qspec_then ‘choicesR’ assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem optimise_correct:
  (∀ e. ^P0 e) ∧ (∀ l. ^P1 l) ∧ (∀ p. ^P2 p) ∧ (∀ l. ^P3 l) ∧ (∀ p. ^P4 p)
  ∧ (∀ p. ^P5 p) ∧ (∀ l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[optimise_def] \\ rpt strip_tac
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac)
  \\ TRY (simp[evaluate_def] \\ trivial_tac \\ NO_TAC)
  >- (
   simp[evaluate_def]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ get_ext_eval_tac ‘evaluate _ _ [optimise _ e] = _’
   \\ imp_res_tac evaluate_sing \\ rveq \\ fs[] \\ rveq
   \\ simp[do_if_def]
   \\ Cases_on ‘v = Boolv T’ \\ fs[]
   >- (
    strip_tac
    \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧
        q.fp_state.canOpt ≠ Strict ∧ ~ q.fp_state.real_sem’
       by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ last_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
    \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
    \\ qexists_tac ‘choices’
    \\ qpat_x_assum ‘evaluate _ _ [e0] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ disch_then (qspec_then ‘choicesR’ assume_tac)
    \\ fs[semState_comp_eq, fpState_component_equality])
   \\ Cases_on ‘v = Boolv F’ \\ fs[]
   \\ strip_tac
   \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧
       q.fp_state.canOpt ≠ Strict ∧ ~ q.fp_state.real_sem’
     by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ strip_tac
   \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
   \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
   \\ qexists_tac ‘choices’
   \\ qpat_x_assum ‘evaluate _ _ [e1] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘choicesR’ assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   simp[evaluate_def]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ get_ext_eval_tac ‘evaluate st1 _ [optimise _ e] = _’
   \\ fs[do_log_def]
   \\ Cases_on ‘l = And ∧ HD a = Boolv T ∨ l = Or ∧ HD a = Boolv F’ \\ fs[]
   \\ rveq \\ fs[]
   \\ TRY (
      rpt strip_tac
      \\ qpat_x_assum `evaluate q env [optimise _ e0] = _`
                      (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
      \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧
          q.fp_state.canOpt ≠ Strict ∧ ~ q.fp_state.real_sem’
        by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
      \\ rfs[]
      \\ rpt (disch_then drule)
      \\ strip_tac
      \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
      \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
      \\ qexists_tac ‘choices’
      \\ fs[]
      \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)))
      \\ rpt (disch_then (qspec_then ‘choicesR’ assume_tac))
      \\ fs[semState_comp_eq, fpState_component_equality])
   \\ Cases_on ‘l = Or ∧ HD a = Boolv T’ \\ Cases_on ‘l = And ∧ HD a = Boolv F’
   \\ fs[]
   \\ rpt strip_tac \\ rveq \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
   \\ fs[] \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   simp[evaluate_def]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ get_ext_eval_tac ‘evaluate st1 env [optimise _ e] = _’
   \\ strip_tac
   \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧
        q.fp_state.canOpt ≠ Strict ∧ ~ q.fp_state.real_sem’
      by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
   \\ first_x_assum drule \\ rpt (disch_then drule)
   \\ strip_tac
   \\ optUntil_tac ‘evaluate _ env [e] = _’ ‘fpOpt'’
   \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
   \\ qexists_tac ‘choices’ \\ fs[]
   \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)))
   \\ rpt (disch_then (qspec_then ‘choicesR’ assume_tac))
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   rpt strip_tac \\ rveq
   \\ last_x_assum irule \\ fsrw_tac [SATISFY_ss] [])
  >- (
   rpt strip_tac
   \\ imp_res_tac (CONJUNCT1 (prep evaluate_fp_rws_append))
   \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac)
   \\ fs[]
   \\ first_x_assum irule \\ fsrw_tac [SATISFY_ss] [])
  >- (
   rpt strip_tac
   \\ imp_res_tac (CONJUNCT1 (prep evaluate_fp_rws_append))
   \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac)
   \\ fs[]
   \\ pop_assum (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
   \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
   \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘st1.fp_state.choices’
   \\ fs[fpState_component_equality, semState_comp_eq])
  >- (
   simp[evaluate_def]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ simp[MAP_FST_optimise]
   \\ TOP_CASE_TAC \\ fs[]
   \\ get_ext_eval_tac ‘evaluate st1 env [optimise _ e] = _’
   \\ strip_tac
   \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧
        q.fp_state.canOpt ≠ Strict ∧ ~ q.fp_state.real_sem’
      by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
   \\ first_x_assum drule \\ rpt (disch_then drule)
   \\ strip_tac
   \\ optUntil_tac ‘evaluate _ env [e] = _’ ‘fpOpt'’
   \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
   \\ qexists_tac ‘choices’ \\ fs[]
   \\ rpt (qpat_x_assum ‘evaluate_match _ _ _ _ _ = _’ (mp_then Any mp_tac (CONJUNCT2 evaluate_add_choices)))
   \\ rpt (disch_then (qspec_then ‘choicesR’ assume_tac))
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   simp[evaluate_def]
   \\ rpt strip_tac \\ first_x_assum irule
   \\ fsrw_tac [SATISFY_ss] [])
  >- (
   simp[evaluate_def]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ rveq \\ fs[]
   \\ fs[]
   \\ ‘<| optimisations := rws; canOpt := (f = Opt) |>.canOpt ⇔
       (st1 with fp_state := st1.fp_state with canOpt := FPScope f).fp_state.canOpt = FPScope Opt’
     by (Cases_on ‘f’ \\ fs[semState_comp_eq, fpState_component_equality])
   \\ ‘~ (st1 with fp_state := st1.fp_state with canOpt := FPScope f).fp_state.real_sem’
        by (fs[semState_comp_eq, fpState_component_equality])
   \\ ‘(st1 with fp_state := st1.fp_state with canOpt := FPScope f).fp_state.canOpt ≠ Strict’
        by (fs[semState_comp_eq, fpState_component_equality])
   \\ first_x_assum drule \\ rpt (disch_then drule)
   \\ disch_then (qspecl_then [‘q’, ‘env’, ‘a’] mp_tac)
   \\ impl_tac
   \\ fs[] \\ strip_tac
   \\ qexists_tac ‘fpOpt’
   \\ qexists_tac ‘choices’
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   rpt strip_tac \\ first_x_assum irule
   \\ fsrw_tac [SATISFY_ss] [])
  >- (
   simp[evaluate_def]
   \\ rpt strip_tac \\ rveq
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   simp[evaluate_def]
   \\ rpt strip_tac \\ first_x_assum irule
   \\ fsrw_tac [SATISFY_ss] [])
  >- (
   rpt strip_tac \\ first_x_assum irule
   \\ fsrw_tac [SATISFY_ss] [])
  >- (
   simp [evaluate_def]
   \\ ntac 2 (TOP_CASE_TAC \\ fs[]))
  >- (
   simp [evaluate_def]
   \\ TOP_CASE_TAC \\ fs[]
   \\ rpt strip_tac \\ rveq
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   qpat_x_assum ‘∀ e. MEM e l ⇒ _’
     (fn thm => (mp_then Any assume_tac (SIMP_RULE std_ss [] lift_P6_REVERSE) thm))
   \\ Cases_on ‘st1.fp_state.canOpt = FPScope Opt’ \\ fs[]
   >- (
    qpat_assum ‘∀ st1 st2 env exps r.
                is_rewriteFPexp_list_correct rws st1 st2 env _ _’ mp_tac
    \\ once_rewrite_tac[is_rewriteFPexp_list_correct_def]
    \\ rpt strip_tac
    \\ ‘st1.fp_state.rws = st2.fp_state.rws’
      by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ first_x_assum
       (qspecl_then
        [‘st1’, ‘st2’, ‘env’,
         ‘[App o' (MAP (λ a. optimise (cfg with optimisations := rws) a )l)]’, ‘r’]
        mp_tac)
    \\ impl_tac \\ fs[]
    \\ qpat_x_assum `evaluate _ _ [rewriteFPexp _ _ ] = _` kall_tac
    \\ rpt strip_tac
    \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
    \\ qmatch_goalsub_abbrev_tac ‘evaluate st1_ext env _’
    \\ ‘(cfg.canOpt ⇔ st1_ext.fp_state.canOpt = FPScope Opt) ∧
        st1_ext.fp_state.canOpt ≠ Strict ∧ ~ st1_ext.fp_state.real_sem’
       by (unabbrev_all_tac \\ fs[semState_comp_eq, fpState_component_equality])
    \\ disch_then (fn thm => mp_tac (REWRITE_RULE [Once evaluate_def] thm))
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    \\ fs[GSYM MAP_REVERSE]
    \\ qpat_x_assum ‘evaluate st1_ext _ _ = _’
                    ( fn thm => first_x_assum (fn ithm => mp_then Any mp_tac ithm thm))
    \\ impl_tac \\ fs[]
    \\ strip_tac \\ unabbrev_all_tac
    \\ imp_res_tac (SIMP_RULE std_ss [] (CONJUNCT1 evaluate_fp_rws_up))
    \\ first_x_assum (qspec_then ‘st1.fp_state.rws ++ rws’ mp_tac) \\ impl_tac
    >- (unabbrev_all_tac \\ fs[semState_comp_eq, fpState_component_equality])
    \\ strip_tac \\ fs[fpState_component_equality]
    \\ rename1 ‘getOpClass op’ \\ Cases_on ‘getOpClass op’ \\ fs[]
    >- (
     TOP_CASE_TAC \\ fs[]
     \\ ntac 2 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac
     \\ qpat_x_assum ‘evaluate (dec_clock _) _ _ = _’
                     (mp_then Any assume_tac (SIMP_RULE std_ss [] (CONJUNCT1 evaluate_fp_rws_up)))
     \\ first_x_assum (qspec_then ‘st1.fp_state.rws ++ rws’ mp_tac)
     \\ impl_tac
     >- (fs[dec_clock_def] \\ imp_res_tac evaluate_fp_opts_inv \\ rfs[]
         \\ qpat_x_assum `st2.fp_state.rws ++ _ = _` (rewrite_tac o single o GSYM)
         \\ fs[])
     \\ strip_tac
     \\ optUntil_tac ‘evaluate _ _ (REVERSE l) = _’ ‘fpOpt’
     \\ ‘st2.fp_state.rws = st1.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ pop_assum (fs o single)
     \\ qexists_tac ‘optUntil (choicesR' - choices') fpOpt'' fpOpt’
     \\ qexists_tac ‘choices'’ \\ simp[evaluate_def]
     \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)))
     \\ rpt (disch_then (qspec_then ‘choicesR'’ assume_tac))
     \\ fs[semState_comp_eq, fpState_component_equality, dec_clock_def])
    >- (
     TOP_CASE_TAC \\ fs[]
     \\ ntac 2 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac ‘fpOpt''’\\ qexists_tac ‘choices'’ \\ fs[]
     \\ rveq \\ rfs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    >- (
     ‘q.fp_state.canOpt = FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[]
     \\ ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
     \\ optUntil_tac ‘evaluate _ _ (REVERSE _) = _’ ‘q.fp_state.opts’
     \\ rfs[fpState_component_equality]
     \\ qexists_tac ‘optUntil (choicesR' − choices') fpOpt'' q.fp_state.opts’
     \\ qexists_tac ‘choices'’
     \\ simp[evaluate_def]
     \\ fs[] \\ TOP_CASE_TAC
     \\ ‘q.fp_state.rws = st2.fp_state.rws ++ rws’
        by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[shift_fp_opts_def]
     \\ fs[semState_comp_eq, fpState_component_equality])
    \\ fs[] \\ rveq \\ fs[]
    \\ ‘~q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[shift_fp_opts_def])
   \\ rpt strip_tac
   \\ ‘st1.fp_state.rws = st2.fp_state.rws’
     by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
    \\ disch_then (fn thm => mp_tac (REWRITE_RULE [Once evaluate_def] thm))
    \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
    \\ fs[GSYM MAP_REVERSE]
    \\ qpat_x_assum ‘evaluate _ _ _ = _’
                    ( fn thm => first_x_assum (fn ithm => mp_then Any mp_tac ithm thm))
    \\ impl_tac \\ fs[]
    \\ strip_tac
    \\ rename1 ‘getOpClass op’ \\ Cases_on ‘getOpClass op’ \\ fs[]
    >- (
     ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac
     \\ qpat_x_assum ‘evaluate (dec_clock _) _ _ = _’
                     (mp_then Any assume_tac (SIMP_RULE std_ss [] (CONJUNCT1 evaluate_fp_rws_up)))
     \\ first_x_assum (qspec_then ‘st1.fp_state.rws ++ rws’ mp_tac)
     \\ impl_tac
     >- (fs[dec_clock_def]
         \\ imp_res_tac evaluate_fp_opts_inv \\ rfs[])
     \\ strip_tac
     \\ optUntil_tac ‘evaluate _ _ (REVERSE l) = _’ ‘fpOpt'’
     \\ ‘st2.fp_state.rws = st1.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ ‘q.fp_state.rws = st1.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ ntac 2(pop_assum (fs o single))
     \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
     \\ qexists_tac ‘choices’ \\ simp[evaluate_def]
     \\ rpt (qpat_x_assum ‘evaluate _ _ _ = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices)))
     \\ rpt (disch_then (qspec_then ‘choicesR’ assume_tac))
     \\ fs[semState_comp_eq, fpState_component_equality, dec_clock_def])
    >- (
     ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’ \\ fs[]
     \\ rveq \\ rfs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    >- (
     ‘q.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[]
     \\ ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’ \\ fs[]
     \\ rveq \\ rfs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    \\ fs[] \\ rveq \\ fs[]
    \\ ‘~q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[shift_fp_opts_def])
  >- (
   qpat_x_assum ‘∀ e. MEM e l ⇒ _’
     (fn thm => (mp_then Any assume_tac (SIMP_RULE std_ss [] lift_P6_REVERSE) thm))
   \\ simp [evaluate_def]
   \\ reverse TOP_CASE_TAC \\ fs[]
   \\ ntac 2 (TOP_CASE_TAC \\ fs[GSYM MAP_REVERSE])
   \\ first_x_assum drule
   \\ rpt (disch_then drule) \\ strip_tac
   \\ rpt (TOP_CASE_TAC \\ fs[]) \\ strip_tac \\ rveq \\ fs[]
   \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   fs[evaluate_def, MAP_MAP_triple]
   \\ reverse TOP_CASE_TAC \\ fs[]
   \\ rpt strip_tac
   \\ first_x_assum drule
   \\ rpt (disch_then drule)
   \\ strip_tac
   \\ asm_exists_tac \\ fs[])
  >- (
   fs[evaluate_def] \\ rpt strip_tac \\ rveq
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   qpat_x_assum `evaluate_match _ _ _ _ _ = _` mp_tac
   \\ Cases_on ‘p’ \\ simp[evaluate_def]
   \\ reverse TOP_CASE_TAC \\ fs[]
   \\ TOP_CASE_TAC \\ fs[]
   >- (
    strip_tac
    \\ first_x_assum drule \\ rpt (disch_then drule)
    \\ disch_then irule)
   \\ strip_tac
   \\ get_ext_eval_tac ‘evaluate st1 _ [optimise _ r'] = _’
   \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
   \\ fs[semState_comp_eq, fpState_component_equality])
  \\ fs[evaluate_def]
QED
end;


Theorem MEM_for_all_MAPi:
  ∀ (P: α -> α -> bool) (f: α -> α) (g: α -> α) l l'.
    (∀x. MEM x l ⇒ P (f x) x) ∧ (∀x. P (g x) x) ⇒
    MAPi (λn e. if n = i then (f e) else (g e)) l = l' ⇒
    (∀i. (i: num) < LENGTH l ⇒ P (EL i l') (EL i l))
Proof
  rpt strip_tac
  \\ imp_res_tac (INST_TYPE[alpha |-> beta] EL_MAPi)
  \\ pop_assum ( Q.ISPEC_THEN ‘(λ (n :num) (e :α). if n = (i :num) then ((f :α -> α) e) else (g :α -> α) e): num -> α -> α’ strip_assume_tac )
  \\ fs[EVAL “(λn e. if n = i then f e else g e) i' (EL i' l)”]
  \\ Cases_on ‘i = i'’ \\ rveq  \\ fs[]
  \\ qpat_x_assum ‘∀ x. MEM x l ⇒ P (f x) x’ (qspec_then ‘(EL i l)’ assume_tac)
  \\ Q.ISPECL_THEN [‘l’, ‘(EL i l)’] strip_assume_tac MEM_EL
  \\ last_assum ( (assume_tac o snd) o EQ_IMP_RULE ) \\ fs[]
  \\ ‘EL i l = EL i l’ by fs[]
  \\ first_x_assum irule
  \\ qexists_tac ‘i’
  \\ fs[]
QED

Theorem MAPi_EL_nested:
  ∀ l n. n < LENGTH l ⇒ EL n (MAPi (λ n e. (n, e)) l) = EL n (MAPi (λ n e. (n, (EL n l))) l)
Proof
  rpt strip_tac
  \\ qspecl_then [‘(λ n e. (n, e))’, ‘n’, ‘l’] imp_res_tac EL_MAPi
  \\ qspecl_then [‘(λ n e. (n, (EL n l)))’, ‘n’, ‘l’] imp_res_tac EL_MAPi
  \\ fs[EVAL “(λn e. (n,e)) n (EL n l)”, EVAL “(λn e. (n,EL n l)) n (EL n l)”]
QED

Theorem MAPi_EL_no_fun:
  ∀ l. MAPi (λ n e. (n, e)) l = MAPi (λ n e. (n, (EL n l))) l
Proof
  rpt strip_tac
  \\ qspecl_then [‘MAPi (λ n e. (n, e)) l’, ‘MAPi (λ n e. (n, (EL n l))) l’] strip_assume_tac LIST_EQ
  \\ ‘LENGTH (MAPi (λ n e. (n, e)) l) = LENGTH (MAPi (λ n e. (n, (EL n l))) l)’ by fs[LENGTH_MAPi]
  \\ fs[]
QED

Theorem MAPi_EL_list_quant:
  ∀ f l. MAPi (λ n e. f n e) l = MAPi (λ n e. f n (EL n l)) l
Proof
  rpt strip_tac
  \\ qspecl_then [‘MAPi (λ n e. f n e) l’, ‘MAPi (λ n e. f n (EL n l)) l’] strip_assume_tac LIST_EQ
  \\ pop_assum irule
  \\ rpt strip_tac \\ fs[LENGTH_MAPi]
QED

Theorem MAPi_EL_list:
  MAPi (λ n e. f n e) l = MAPi (λ n e. f n (EL n l)) l
Proof
  fs[MAPi_EL_list_quant]
QED

Theorem MAPi_same_EL_quant:
  ∀ exps. MAPi (λ n e. (EL n exps)) exps = exps
Proof
  strip_tac
  \\ qspecl_then [‘λ n e. e’, ‘exps’] assume_tac MAPi_EL_list_quant
  \\ fs[]
QED

Theorem MAPi_same_EL:
  MAPi (λ n e. (EL n exps)) exps = exps
Proof
  fs[MAPi_same_EL_quant]
QED

local
val rewrites_no_effect = “
 λ cfg path plan e. perform_rewrites cfg path plan e = e
”
in
Theorem perform_rewrites_no_plan_same:
  ∀ cfg path plan e. plan = [] ⇒ ^rewrites_no_effect cfg path plan e
Proof
  ho_match_mp_tac perform_rewrites_ind
  \\ fs[perform_rewrites_def]
  \\ strip_tac
  >- (
  rpt strip_tac
  \\ Cases_on ‘cfg.canOpt’
  \\ fs[rewriteFPexp_def]
  )
  >- (
  rpt strip_tac
  \\ Cases_on ‘cfg.canOpt’
  \\ fs[rewriteFPexp_def]
  \\ irule LIST_EQ
  \\ fs[LENGTH_MAPi]
  \\ rpt strip_tac
  \\ Cases_on ‘x = i’
  \\ fs[]
  \\ TRY (
    qpat_x_assum ‘∀e. MEM e exps ⇒ _’ (qspec_then ‘EL i exps’ assume_tac)
    \\ fs[MEM_EL]
    \\ pop_assum irule
    \\ qexists_tac ‘i’ \\ fs[]
    )
  \\ TRY (
    Cases_on ‘EL i pes’ \\ fs[]
    \\ qpat_x_assum ‘∀ p e. MEM (p, e) pes ⇒ _’ (qspecl_then [‘q’, ‘r’] assume_tac)
    \\ fs[MEM_EL]
    \\ pop_assum irule
    \\ qexists_tac ‘i’ \\ fs[]
    )
  \\ TRY (
    Cases_on ‘EL x pes’ \\ fs[]
    )
  )
QED
end

Theorem perform_rewrites_no_plan_simple:
  perform_rewrites cfg path [] e = e
Proof
  qspecl_then [‘cfg’, ‘path’, ‘[]’, ‘e’] strip_assume_tac perform_rewrites_no_plan_same
  \\ fs[]
QED

Theorem enumerate_append:
  ∀ l l' n. enumerate n (l ++ l') = (enumerate n l) ++ (enumerate (n + LENGTH l) l')
Proof
  Induct_on ‘l'’ \\ fs[miscTheory.enumerate_def]
  \\ Induct_on ‘l’ \\ fs[miscTheory.enumerate_def]
QED

local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
     ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r path.
     (∀ (st1:'a semanticPrimitives$state) st2 env exps r part.
       (∀x. MEM x part ⇒ MEM x rws) ⇒ is_rewriteFPexp_list_correct part st1 st2 env exps r) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt ≠ Strict ∧
     ~st1.fp_state.real_sem ∧
     evaluate st1 env [perform_rewrites (cfg with optimisations := rws) path rws e] = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env [e]=
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)”
  (* P4: string * exp -> bool *)
  val P4 =
  Parse.Term (‘λ (s:string, e). ^P0 e’);
  (* P2: string * string * exp -> bool *)
  val P2 =
  Parse.Term (‘λ (s1:string, s2:string, e). ^P0 e’);
  (* Letrec goal *)
  val P1 =
  Parse.Term (‘λ (l:(string # string # exp) list).
  ∀ p. MEM p l ⇒ ^P2 p’)
  (* P5: pat * exp -> bool *)
  val P5 =
  Parse.Term (‘λ (p:pat, e). ^P0 e’)
  (* P3: pat * exp list -> bool *)
  val P3 =
  Parse.Term (‘λ (l:(pat # exp) list).
     ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r v err_v path i.
     (∀ (st1:'a semanticPrimitives$state) st2 env exps r part.
        (∀x. MEM x part ⇒ MEM x rws) ⇒ is_rewriteFPexp_list_correct part st1 st2 env exps r) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     st1.fp_state.canOpt ≠ Strict ∧
     ~st1.fp_state.real_sem ∧
     evaluate_match st1 env v (MAPi (λ n (p,e). if (n = i) then
                                                  (p, perform_rewrites (cfg with optimisations := rws) path rws e)
                                                else (p, e)) l) err_v = (st2, Rval r) ⇒
     ∃ fpOpt choices fpOptR choicesR.
       evaluate_match
         (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>)
         env v l err_v =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)’);
  (* P6: exp list -> bool *)
  val P6 =
    Parse.Term (‘λ (es:ast$exp list). ∀ e. MEM e es ⇒ ^P0 e’);
  val ind_thm =
    astTheory.exp_induction |> SPEC P0 |> SPEC P1 |> SPEC P2 |> SPEC P3
    |> SPEC P4 |> SPEC P5 |> SPEC P6;
  val trivial_tac =
    rpt strip_tac \\ rveq
    \\ last_x_assum drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ qexists_tac ‘fpOpt’
    \\ fs[state_component_equality, fpState_component_equality]
    \\ rveq
    \\ qexists_tac ‘fpOptR’ \\ fs[];
  val get_ext_eval_tac = fn t =>
    qpat_x_assum t (fn th => first_x_assum (fn ith => mp_then Any mp_tac ith th))
    \\ rpt (disch_then drule)
    \\ strip_tac
  val arith_case_tac = fn t =>
     rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac t \\ rfs[]
     \\ TOP_CASE_TAC \\ fs[];
in

val no_change_tac = fn t =>
  (qpat_x_assum ‘evaluate _ _ [^(Parse.Term t)] = _’ (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
   \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] strip_assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality]
   \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’, ‘st2.fp_state.opts’, ‘st2.fp_state.choices’]
   \\ imp_res_tac (CONJUNCT1 evaluate_add_choices)
   \\ fs[semState_comp_eq, fpState_component_equality]);

Triviality lift_P6_perform_rws_REVERSE:
  ∀ es.
    ^P6 es ⇒
    ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r path i m.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r part.
       (∀x. MEM x part ⇒ MEM x rws) ⇒ is_rewriteFPexp_list_correct part st1 st2 env exps r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    ~st1.fp_state.real_sem ∧
    evaluate st1 env (REVERSE (MAP (λ (n, e). if (n = i) then
                                     perform_rewrites (cfg with optimisations := rws) path rws e
                                   else e) (enumerate m es))) = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate
        (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>)
        env (REVERSE es) =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)
Proof
  simp[] \\ Induct_on ‘es’ \\ rpt strip_tac
  >- (fs[evaluate_def, miscTheory.enumerate_def] \\ qexists_tac ‘st2.fp_state.opts’
      \\ fs[semState_comp_eq, fpState_component_equality])
  \\ fs[evaluate_append]
  \\ fs[miscTheory.enumerate_def]
  \\ fs[evaluate_append]
  \\ qpat_x_assum ‘case evaluate _ _ _ of _ => _’ (assume_tac o SIMP_RULE bool_ss [CaseEq"prod", CaseEq"result"])
  \\ fs[] \\ rveq
  \\ ‘∀e. MEM e es ⇒
          ∀(st1 :α semanticPrimitives$state) (st2 :α semanticPrimitives$state) env cfg rws r path.
            (∀ (st1:'a semanticPrimitives$state) st2 env exps r part.
               (∀x. MEM x part ⇒ MEM x rws) ⇒ is_rewriteFPexp_list_correct part st1 st2 env exps r)  ∧
            (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
            st1.fp_state.canOpt ≠ Strict ∧ ~st1.fp_state.real_sem ∧
            evaluate st1 env
                     [perform_rewrites (cfg with optimisations := rws) path rws e] = (st2,Rval r) ⇒
            ∃fpOpt choices fpOptR choicesR.
              evaluate
              (st1 with
               fp_state :=
               st1.fp_state with
                  <|rws := st1.fp_state.rws ++ rws; opts := fpOpt;
                    choices := choices|>) env [e] =
              (st2 with
               fp_state :=
               st2.fp_state with
                  <|rws := st2.fp_state.rws ++ rws; opts := fpOptR;
                    choices := choicesR|>,Rval r)’ by (
    rpt strip_tac
    \\ qpat_x_assum ‘∀e. e = h ∨ MEM e es ⇒ _’ (qspec_then ‘e’ strip_assume_tac)
    \\ rfs[] \\ pop_assum (qspecl_then [‘st1'’, ‘st2’, ‘env'’, ‘cfg'’, ‘rws'’, ‘r’, ‘path'’] strip_assume_tac)
    \\ rfs[] \\ qexistsl_tac [‘fpOpt’, ‘choices’, ‘fpOptR’, ‘choicesR’] \\ fs[]
    )
  \\ qpat_x_assum ‘(∀e. MEM e es ⇒ _) ⇒ _’ drule
  \\ disch_then (qspecl_then [‘st1’, ‘s'’, ‘env’, ‘cfg’, ‘rws’, ‘vs’, ‘path’, ‘i’, ‘m + 1’] strip_assume_tac)
  \\ rfs[]
  \\ Cases_on ‘m = i’ \\ fs[] \\ rveq
  >- (
  qpat_x_assum ‘∀e. e = h ∨ MEM e es ⇒ _’ (qspec_then ‘h’ strip_assume_tac) \\ fs[]
  \\ pop_assum (qspecl_then [‘s'’, ‘s''’, ‘env’, ‘cfg’, ‘rws’, ‘vs'’, ‘path’] strip_assume_tac)
  \\ ‘(cfg.canOpt ⇔ s'.fp_state.canOpt = FPScope Opt) ∧ s'.fp_state.canOpt ≠ Strict ∧
      ~s'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[]) \\ fs[]
  \\ qpat_x_assum ‘_ ∧ evaluate _ _ [perform_rewrites _ _ _ _] = _ ⇒ _’ imp_res_tac
  \\ optUntil_tac ‘evaluate _ _ (REVERSE es) = _’ ‘fpOpt'’
  \\ qexistsl_tac [‘optUntil (choicesR − choices) fpOpt fpOpt'’, ‘choices’] \\ fs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘choicesR’ strip_assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
  )
  >- (
  qpat_x_assum ‘evaluate _ _ [h] = _’ (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
  \\ pop_assum (qspecl_then [‘rws’, ‘s''.fp_state.opts’] strip_assume_tac)
  \\ optUntil_tac ‘evaluate _ _ (REVERSE es) = _’ ‘fpOpt'’
  \\ qexistsl_tac [‘optUntil (choicesR − choices) fpOpt fpOpt'’, ‘choices’] \\ fs[]
  \\ pop_assum kall_tac
  \\ drule (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘choicesR’ strip_assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
  )
QED

Triviality lift_P6_perform_rws:
  ∀ es.
    ^P6 es ⇒
    ∀ (st1: 'a semanticPrimitives$state) st2 env cfg rws r path i m.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r part.
       (∀x. MEM x part ⇒ MEM x rws) ⇒ is_rewriteFPexp_list_correct part st1 st2 env exps r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    ~st1.fp_state.real_sem ∧
    evaluate st1 env (MAP (λ (n, e). if (n = i) then
                                     perform_rewrites (cfg with optimisations := rws) path rws e
                                   else e) (enumerate m es)) = (st2, Rval r) ⇒
    ∃ fpOpt choices fpOptR choicesR.
      evaluate
        (st1 with fp_state := st1.fp_state with
                                 <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>)
        env es =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r)
Proof
  simp[] \\ Induct_on ‘es’ \\ rpt strip_tac
  >- (fs[evaluate_def, miscTheory.enumerate_def] \\ qexists_tac ‘st2.fp_state.opts’
      \\ fs[semState_comp_eq, fpState_component_equality])
  \\ fs[miscTheory.enumerate_def]
  \\ ‘evaluate st1 env ([(if m = i then
          perform_rewrites (cfg with optimisations := rws) path rws h
        else h)] ++
       MAP
       (λ(n,e).
          if n = i then
            perform_rewrites (cfg with optimisations := rws) path
                             rws e
          else e) (enumerate (m + 1) es)) = (st2, Rval r)’ by fs[]
  \\ fs[evaluate_append]
  \\ rpt (qpat_x_assum ‘evaluate _ _ (_ :: _) = _’ mp_tac)
  \\ once_rewrite_tac [evaluate_cons]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘case evaluate _ _ _ of _ => _’ (
                    assume_tac o SIMP_RULE bool_ss [CaseEq"prod", CaseEq"result"])
  \\ fs[] \\ rveq
  \\ ‘∀e. MEM e es ⇒
          ∀(st1 :α semanticPrimitives$state) (st2 :α semanticPrimitives$state) env cfg rws r path.
            (∀ (st1:'a semanticPrimitives$state) st2 env exps r part.
               (∀x. MEM x part ⇒ MEM x rws) ⇒ is_rewriteFPexp_list_correct part st1 st2 env exps r) ∧
            (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
            st1.fp_state.canOpt ≠ Strict ∧ ~st1.fp_state.real_sem ∧
            evaluate st1 env
                     [perform_rewrites (cfg with optimisations := rws) path rws e] = (st2,Rval r) ⇒
            ∃fpOpt choices fpOptR choicesR.
              evaluate (st1 with
                        fp_state :=
                        st1.fp_state with
                           <|rws := st1.fp_state.rws ++ rws; opts := fpOpt;
                             choices := choices|>) env [e] =
              (st2 with
               fp_state :=
               st2.fp_state with
                  <|rws := st2.fp_state.rws ++ rws; opts := fpOptR;
                    choices := choicesR|>,Rval r)’ by (
    rpt strip_tac
    \\ qpat_x_assum ‘∀e. e = h ∨ MEM e es ⇒ _’ (qspec_then ‘e’ strip_assume_tac)
    \\ rfs[] \\ pop_assum (qspecl_then [‘st1'’, ‘st2’, ‘env'’, ‘cfg'’, ‘rws'’, ‘r’, ‘path'’] strip_assume_tac)
    \\ rfs[] \\ qexistsl_tac [‘fpOpt’, ‘choices’, ‘fpOptR’, ‘choicesR’] \\ fs[]
    )
  \\ qpat_x_assum ‘(∀e. MEM e es ⇒ _) ⇒ _’ drule
  \\ disch_then (qspecl_then [‘s'’, ‘s''’, ‘env’, ‘cfg’, ‘rws’, ‘vs'’, ‘path’, ‘i’, ‘m + 1’] strip_assume_tac)
  \\ rfs[]
  \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔ s'.fp_state.canOpt = FPScope Opt)
      ∧ s'.fp_state.canOpt ≠ Strict ∧ ~s'.fp_state.real_sem’ by (
    imp_res_tac evaluate_fp_opts_inv \\ fs[]
    )
  \\ fs[]
  \\ Cases_on ‘m = i’ \\ fs[] \\ rveq
  >- (
  qpat_x_assum ‘∀e. e = h ∨ MEM e es ⇒ _’ (qspec_then ‘h’ strip_assume_tac) \\ fs[]
  \\ pop_assum (qspecl_then [‘st1’, ‘s'’, ‘env’, ‘cfg’, ‘rws’, ‘vs’, ‘path’] strip_assume_tac)
  \\ rfs[]
  \\ optUntil_tac ‘evaluate _ _ [h] = _’ ‘fpOpt’
  \\ qexistsl_tac [‘optUntil (choicesR' − choices') fpOpt' fpOpt’, ‘choices'’]
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ pop_assum kall_tac
  \\ drule (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘choicesR'’ strip_assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
  )
  >- (
  qpat_x_assum ‘evaluate _ _ [h] = _’ (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
  \\ pop_assum (qspecl_then [‘rws’, ‘fpOpt’] strip_assume_tac)
  \\ drule (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’] \\ fs[]
  \\ ntac 2 (pop_assum kall_tac)
  \\ drule (CONJUNCT1 evaluate_add_choices)
  \\ disch_then (qspec_then ‘s'.fp_state.choices’ strip_assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
  )
QED

Theorem perform_rewrites_correct:
  (∀ e. ^P0 e) ∧ (∀ l. ^P1 l) ∧ (∀ p. ^P2 p) ∧ (∀ l. ^P3 l) ∧ (∀ p. ^P4 p)
  ∧ (∀ p. ^P5 p) ∧ (∀ l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[perform_rewrites_def] \\ rpt strip_tac
  (* Case: If e e0 e1 *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Case: Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Case: Does not rewrite *)
    >- no_change_tac ‘If e e0 e1’
    )
  (* Case: ListIndex _ *)
  >- no_change_tac ‘If e e0 e1’
  (* Case: Center *)
  >- (
    qpat_x_assum ‘evaluate _ _ [If _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ Cases_on ‘do_if (HD v) (perform_rewrites (cfg with optimisations := rws) o' rws e0) e1’ \\ fs[]
    \\ Cases_on ‘(HD v) = Boolv T’ \\ fs[do_if_def]
    \\ imp_res_tac evaluate_sing \\ fs[] \\ rveq
    (* HD v = Boolv T *)
    >- (
      qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                      _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e0] = _ ⇒ _’ drule
      \\ disch_then (qspecl_then [‘st'’, ‘st2’, ‘env’, ‘cfg’, ‘[v']’, ‘o'’] strip_assume_tac) \\ rfs[]
      \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔
           st'.fp_state.canOpt = FPScope Opt) ∧ st'.fp_state.canOpt ≠ Strict ∧
          ~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
      \\ fs[]
      \\ fs[evaluate_def]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
      \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_if_def]
      \\ ntac 2 (pop_assum kall_tac)
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    (* HD v = Boolv F *)
    >- (
      qpat_x_assum ‘evaluate _ _ [e1] = _’ (
                     mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac) \\ fs[]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
      \\ fs[evaluate_def]
      \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’] \\ fs[]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_if_def]
      \\ ntac 2 (pop_assum kall_tac)
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  (* Case: Right *)
  >- (
    qpat_x_assum ‘evaluate _ _ [If _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ Cases_on ‘do_if (HD v) e0 (perform_rewrites (cfg with optimisations := rws) o' rws e1)’ \\ fs[]
    \\ Cases_on ‘(HD v) = Boolv T’ \\ fs[do_if_def]
    \\ imp_res_tac evaluate_sing \\ fs[] \\ rveq
    (* HD v = Boolv T *)
    >- (
      qpat_x_assum ‘evaluate _ _ [e0] = _’ (
                     mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac) \\ fs[]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
      \\ fs[evaluate_def]
      \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’] \\ fs[]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_if_def]
      \\ ntac 2 (pop_assum kall_tac)
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    (* HD v = Boolv F *)
    >- (
      qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                      _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e1] = _ ⇒ _’ drule
      \\ disch_then (qspecl_then [‘st'’, ‘st2’, ‘env’, ‘cfg’, ‘[v']’, ‘o'’] strip_assume_tac) \\ rfs[]
      \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔
           st'.fp_state.canOpt = FPScope Opt) ∧ st'.fp_state.canOpt ≠ Strict ∧
          ~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
      \\ fs[]
      \\ fs[evaluate_def]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
      \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_if_def]
      \\ ntac 2 (pop_assum kall_tac)
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  (* Case: Left *)
  >- (
    qpat_x_assum ‘evaluate _ _ [If _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ Cases_on ‘do_if (HD v) e0 e1’ \\ fs[]
    \\ qpat_x_assum ‘evaluate _ _ [x] = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac) \\ fs[]
    \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
    \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
    \\ qexists_tac ‘choices’
    \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ fs[evaluate_def]
    \\ disch_then (qspec_then ‘choicesR’ assume_tac) \\ fs[]
    \\ imp_res_tac (CONJUNCT1 evaluate_add_choices)
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
  )
  (* Case: Log l e e0 *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Case: Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Case: Does not rewrite *)
    >- no_change_tac ‘Log l e e0’
    )
  (* Case: ListIndex _ *)
  >- no_change_tac ‘Log l e e0’
  (* Case: Center *)
  >- no_change_tac ‘Log l e e0’
  (* Case: Right *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Log _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ imp_res_tac evaluate_sing \\ rveq
    \\ fs[do_log_def]
    \\ Cases_on ‘l = And ∧ v = Boolv T ∨ l = Or ∧ v = Boolv F’ \\ fs[]
    \\ rveq \\ fs[]
    (* l = And ∧ v = Boolv T and l = Or ∧ v = Boolv F *)
    \\ TRY (
      qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                      _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e0] = _ ⇒ _’ drule
      \\ disch_then (qspecl_then [‘st'’, ‘st2’, ‘env’, ‘cfg’, ‘r’, ‘o'’] strip_assume_tac) \\ rfs[]
      \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔
           st'.fp_state.canOpt = FPScope Opt) ∧ st'.fp_state.canOpt ≠ Strict ∧
          ~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[]) \\ fs[]
      \\ fs[evaluate_def]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
      \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_log_def]
      \\ ntac 2 (pop_assum kall_tac)
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ NO_TAC
      )
    >- (
      Cases_on ‘l’ \\ fs[] \\ Cases_on ‘v = Boolv T’ \\ fs[] \\ rveq \\ fs[]
      \\ fs[evaluate_def]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘st'.fp_state.opts’] assume_tac) \\ fs[]
      \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_log_def]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    (* v ≠ Boolv T ∧ l ≠ Or *)
    >- (
      Cases_on ‘l’ \\ fs[] \\ Cases_on ‘v = Boolv F’ \\ fs[] \\ rveq \\ fs[]
      \\ fs[evaluate_def]
      \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                        mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ first_x_assum (qspecl_then [‘rws’, ‘st'.fp_state.opts’] assume_tac) \\ fs[]
      \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’]
      \\ drule (CONJUNCT1 evaluate_add_choices)
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ fs[do_log_def]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  (* Case: Left *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Log _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ Cases_on ‘do_log l (HD v1) e0’ \\ fs[]
    \\ Cases_on ‘x’ \\ fs[]
    (* x is an expression *)
    >- (
    qpat_x_assum ‘evaluate _ _ [e'] = _’ (mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac) \\ fs[]
    \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
    \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
    \\ qexists_tac ‘choices’
    \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ fs[evaluate_def]
    \\ disch_then (qspec_then ‘choicesR’ assume_tac) \\ fs[]
    \\ imp_res_tac (CONJUNCT1 evaluate_add_choices)
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
    (* x is a value *)
    >- (
      qexistsl_tac [‘fpOpt’, ‘choices’] \\ fs[evaluate_def]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  )
  (* Case: Let o' e e0 *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- no_change_tac ‘Let o' e e0’
  (* Case: ListIndex _ *)
  >- no_change_tac ‘Let o' e e0’
  (* Case: Center *)
  >- no_change_tac ‘Let o' e e0’
  (* Case: Right *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Let _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e0] = _ ⇒ _’ drule
    \\ disch_then (
      qspecl_then [
          ‘st'’, ‘st2’, ‘(env with v := nsOptBind o' (HD v) env.v)’, ‘cfg’, ‘r’, ‘o''’
        ] strip_assume_tac) \\ rfs[]
    \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔
           st'.fp_state.canOpt = FPScope Opt) ∧ st'.fp_state.canOpt ≠ Strict ∧
          ~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[]) \\ fs[]
    \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
    \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ disch_then (qspec_then ‘st1.fp_state.choices’ strip_assume_tac)
    \\ fs[semState_comp_eq, fpState_component_equality]
    \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’]
    \\ fs[evaluate_def]
    \\ qpat_x_assum ‘evaluate _ _ [e0] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ disch_then (qspec_then ‘st'.fp_state.choices’ strip_assume_tac)
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
  (* Case: Left *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Let _ _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs[evaluate_def]
    \\ qpat_x_assum ‘evaluate _ _ [e0] = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac) \\ fs[]
    \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
    \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
    \\ qexists_tac ‘choices’ \\ fs[]
    \\ qpat_x_assum ‘evaluate _ _ [e0] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ disch_then (qspec_then ‘choicesR’ assume_tac) \\ fs[]
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
  )
  (* Case: ?? *)
  >- (
  rveq
  \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                     _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
  \\ rpt (disch_then drule)
  \\ fs[]
  )
  (* Case: ?? *)
  >- (
  rveq
  \\ qpat_x_assum ‘∀ e. MEM e l ⇒ ∀ st1 st2 env cfg rws r path.
                                    _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ _] = _ ⇒ _’ drule
  \\ rpt (disch_then drule)
  \\ fs[]
  )
  (* Case: Handle e l *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Handle e l’
  )
  \\ no_change_tac ‘Handle e l’
  )
  (* Case: Mat e l *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Mat e l’
    )
  (* Case: ListIndex p *)
  >- (
    Cases_on ‘p’ \\ fs[perform_rewrites_def]
    \\ qpat_x_assum ‘evaluate _ _ [Mat _ _] = _’ (
                      assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ Cases_on ‘can_pmatch_all env.c st'.refs
                 (MAPi
                  ($o FST ∘
                   (λn (p,e').
                    if n = q then
                      (p, perform_rewrites (cfg with optimisations := rws) r' rws e')
                    else (p,e'))) l) (HD v)’ \\ fs[]
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r v err_v path i.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate_match _ _ _ _ _ = _ ⇒ _’ drule
    \\ disch_then (qspecl_then [
                      ‘st'’, ‘st2’, ‘env’, ‘cfg’, ‘r’, ‘HD v’, ‘bind_exn_v’, ‘r'’, ‘q’ ] strip_assume_tac)
    \\ rfs[]
    \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔
         st'.fp_state.canOpt = FPScope Opt) ∧ st'.fp_state.canOpt ≠ Strict ∧
        ~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[]) \\ fs[]
    \\ fs[evaluate_def]
    \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [‘rws’, ‘fpOpt’] assume_tac) \\ fs[]
    \\ qpat_x_assum ‘evaluate _ _ [e] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
    \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac) \\ fs[]
    \\ qexistsl_tac [‘fpOpt'’, ‘st1.fp_state.choices’] \\ fs[]
    \\ ‘($o FST ∘
         (λn (p,e').
          if n = q then
            (p, perform_rewrites (cfg with optimisations := rws) r' rws e')
          else (p,e'))) = (λ n (p, e'). p)’ by (
      fs[FUN_EQ_THM]
      \\ rpt strip_tac \\ Cases_on ‘x’ \\ fs[] \\ Cases_on ‘n = q’ \\ fs[]
      )
    \\ ‘(MAPi ($o FST ∘
               (λn (p,e').
                if n = q then
                  (p, perform_rewrites (cfg with optimisations := rws) r' rws e')
                else (p,e'))) l) =
        (MAPi (λ n (p, e'). p) l)’ by (
      qspecl_then [‘l’, ‘l’, ‘($o FST ∘
                               (λn (p,e').
                                if n = q then
                                  (p, perform_rewrites (cfg with optimisations := rws) r' rws e')
                                else (p,e')))’, ‘(λ n (p, e'). p)’] strip_assume_tac MAPi_CONG
      \\ imp_res_tac FUN_EQ_THM
      \\ fs[]
      \\ AP_THM_TAC \\ AP_TERM_TAC
      \\ fs[FUN_EQ_THM, FORALL_PROD] \\ rw[]
      )
    \\ fs[]
    \\ ‘∀ l: (pat # exp) list. MAPi (λ n (p, e'). p) l = MAP FST l’ by (
      Induct \\ fs[]
      \\ fs[FORALL_PROD, o_DEF]
      )
    \\ pop_assum (qspec_then ‘l’ strip_assume_tac)
    \\ fs[]
    \\ ntac 3 (pop_assum kall_tac)
    \\ Cases_on ‘l’ \\ fs[evaluate_def] \\ Cases_on ‘h’ \\ fs[evaluate_def]
    \\ Cases_on ‘ALL_DISTINCT (pat_bindings q' [])’ \\ fs[]
    \\ Cases_on ‘pmatch env.c st'.refs q' (HD v) []’ \\ fs[]
    >- (
      qpat_x_assum ‘evaluate_match _ _ _ _ _ = (st2 with fp_state := _, _)’ (
                     mp_then Any mp_tac (CONJUNCT2 evaluate_add_choices))
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    >- (
      qpat_x_assum ‘evaluate _ _ [r''] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
      \\ disch_then (qspec_then ‘st'.fp_state.choices’ assume_tac) \\ fs[]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  >- no_change_tac ‘Mat e l’
  >- no_change_tac ‘Mat e l’
  (* Case: Left *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Mat _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs[evaluate_def]
    \\ Cases_on ‘can_pmatch_all env.c st'.refs (MAP FST l) (HD v)’ \\ fs[]
    \\ qpat_x_assum ‘evaluate_match st' _ _ _ _ = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT2 evaluate_fp_rws_append)))
    \\ first_x_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac) \\ fs[]
    \\ optUntil_tac ‘evaluate _ _ [e] = _’ ‘fpOpt'’
    \\ qexistsl_tac [‘optUntil (choicesR − choices) fpOpt fpOpt'’, ‘choices’] \\ fs[]
    \\ Cases_on ‘l’ \\ fs[evaluate_def] \\ Cases_on ‘h’ \\ fs[evaluate_def]
    \\ Cases_on ‘ALL_DISTINCT (pat_bindings q [])’ \\ fs[]
    \\ Cases_on ‘pmatch env.c st'.refs q (HD v) []’ \\ fs[]
    >- (
      qpat_x_assum ‘evaluate_match _ _ _ _ _ = (st2 with fp_state := _, _)’ (
                     mp_then Any mp_tac (CONJUNCT2 evaluate_add_choices))
      \\ disch_then (qspec_then ‘choicesR’ assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    >- (
      qpat_x_assum ‘evaluate _ _ [r'] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
      \\ disch_then (qspec_then ‘choicesR’ assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  )
  (* Case: Tannot e a *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Tannot e a’
    )
  >- no_change_tac ‘Tannot e a’
  >- (
    qpat_x_assum ‘evaluate _ _ [Tannot _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs[evaluate_def]
    \\ qexistsl_tac [‘fpOpt’, ‘choices’, ‘fpOptR’, ‘choicesR’] \\ fs[]
    )
  \\ no_change_tac ‘Tannot e a’
  )
  (* FpOptimise f e *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- no_change_tac ‘FpOptimise f e’
  (* Case: ListIndex _ *)
  >- no_change_tac ‘FpOptimise f e’
  (* Case: Center *)
  >- (
    qpat_x_assum ‘evaluate _ _ [FpOptimise _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ Cases_on ‘evaluate
                 (st1 with fp_state :=
                  if st1.fp_state.canOpt = Strict then st1.fp_state
                  else st1.fp_state with canOpt := FPScope f) env
                 [perform_rewrites <|optimisations := rws; canOpt := (f = Opt)|> o' rws e]’ \\ fs[]
    \\ Cases_on ‘r'’ \\ fs[] \\ rveq \\ fs[]
    \\ Cases_on ‘st1.fp_state.canOpt = Strict’ \\ fs[]
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ disch_then (qspecl_then [‘st1 with fp_state := st1.fp_state with canOpt := FPScope f’,
                               ‘q’, ‘env’, ‘<|optimisations := rws; canOpt := (f = Opt)|>’,
                               ‘a’, ‘o'’] strip_assume_tac)
    \\ rfs[]
    \\ fs[evaluate_def]
    \\ qexistsl_tac [‘fpOpt’, ‘choices’] \\ fs[]
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
  \\ no_change_tac ‘FpOptimise f e’
  )
  (* Case: ?? *)
  >- (
  qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                  _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
  \\ rpt (disch_then drule)
  \\ fs[]
  )
  (* Case: Fun s e *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Fun s e’
    )
  \\ no_change_tac ‘Fun s e’
  )
  (* Case: Lannot e l *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Lannot e l’
    )
  >- no_change_tac ‘Lannot e l’
  >- (
    qpat_x_assum ‘evaluate _ _ [Lannot _ _] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ fs[evaluate_def]
    \\ qexistsl_tac [‘fpOpt’, ‘choices’, ‘fpOptR’, ‘choicesR’] \\ fs[]
    )
  \\ no_change_tac ‘Lannot e a’
  )
  (* Case: ?? *)
  >- (
  qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                  _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ drule
  \\ rpt (disch_then drule)
  \\ fs[]
  )
  (* Case: Raise e *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Raise e’
    )
  (* ListIndex _ *)
  >- no_change_tac ‘Raise e’
  (* Center *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Raise _ ] = _’ (
                   assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    )
  \\ no_change_tac ‘Raise e’
  )
  (* Var i *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Var i’
    )
  \\ no_change_tac ‘Var i’
  )
  (* Case: App o' l *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘App o' l’
    )
  (* Case: ListIndex p *)
  >- (
    Cases_on ‘p’ \\ fs[perform_rewrites_def]
    \\ qpat_x_assum ‘evaluate _ _ [App _ _] = _’ (
                      assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ qspecl_then [‘(λ(n, e).
                        if n = q then
                          perform_rewrites (cfg with optimisations := rws) r' rws e
                        else e)’, ‘l’] strip_assume_tac MAP_enumerate_MAPi
    \\ fs[EVAL “(λn e. (λ(n,e).
                          if n = q then
                            perform_rewrites (cfg with optimisations := rws) r' rws e
                          else e) (n,e))”]
    \\ pop_assum (assume_tac o GSYM) \\ fs[]
    \\ pop_assum kall_tac
    \\ fs[GSYM MAP_REVERSE]
    \\ strip_assume_tac lift_P6_perform_rws_REVERSE
    \\ pop_assum (qspec_then ‘l’ strip_assume_tac)
    \\ rfs[] \\ pop_assum drule
    \\ disch_then (qspecl_then [‘st1’, ‘st'’, ‘env’, ‘cfg’, ‘rws’, ‘vs’, ‘r'’, ‘q’, ‘0’]
                   strip_assume_tac) \\ rfs[]
    \\ fs[GSYM MAP_REVERSE]
    \\ rfs[]
    \\ fs[evaluate_def]
    \\ Cases_on ‘getOpClass o'’ \\ fs[]
    (* Case: getOpClass o' = FunApp *)
    >- (
      Cases_on ‘do_opapp (REVERSE vs)’ \\ fs[] \\ Cases_on ‘x’ \\ Cases_on ‘st'.clock = 0’ \\ fs[]
      \\ qpat_x_assum ‘evaluate _ _ [r''] = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] strip_assume_tac)
      \\ optUntil_tac ‘evaluate _ _ (REVERSE l) = _’ ‘fpOpt'’
      \\ qexistsl_tac [‘optUntil (choicesR − choices) fpOpt fpOpt'’, ‘choices’] \\ fs[]
      \\ fs[dec_clock_def, semState_comp_eq, fpState_component_equality]
      \\ qpat_x_assum ‘evaluate _ _ [r''] = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    (* Case: getOpClass o' = Simple *)
    >- (
      Cases_on ‘do_app (st'.refs,st'.ffi) o' (REVERSE vs)’ \\ fs[] \\ Cases_on ‘x’ \\ fs[]
      \\ Cases_on ‘q'’ \\ fs[] \\ rveq
      \\ qexistsl_tac [‘fpOpt’, ‘choices’] \\ fs[]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    (* Case: getOpClass o' = Icing *)
    >- (
      rename1 ‘do_app (st1N.refs, st1N.ffi) op (REVERSE vs)’
      \\ Cases_on ‘do_app (st1N.refs, st1N.ffi) op (REVERSE vs)’ \\ fs[CaseEq"prod"] \\ rveq \\ fs[]
      \\ rename1 ‘do_fprw res (st1N.fp_state.opts 0) st1N.fp_state.rws’
      \\ Cases_on ‘st1N.fp_state.canOpt = FPScope Opt’ \\ fs[]
      >- (
         Cases_on ‘do_fprw res (st1N.fp_state.opts 0) st1N.fp_state.rws’ \\ fs[]
         \\ Cases_on ‘res’ \\ fs[]
         \\ imp_res_tac do_fprw_append_opt
         \\ first_x_assum (qspec_then ‘rws’ strip_assume_tac)
         \\ optUntil_tac ‘evaluate _ _ (REVERSE l) = _’ ‘λ x. if (x = 0) then sched2 else st1N.fp_state.opts x’
         \\ qexistsl_tac [‘optUntil (choicesR − choices) fpOpt
                           (λx. if x = 0 then sched2 else st1N.fp_state.opts x)’, ‘choices’] \\ fs[]
         \\ fsrw_tac [SATISFY_ss] [shift_fp_opts_def, semState_comp_eq, fpState_component_equality]
        )
      \\ qexistsl_tac [‘fpOpt’, ‘choices’, ‘fpOptR’, ‘choicesR’,
                       ‘st1N with fp_state :=
                        st1N.fp_state with
                            <|rws := st1N.fp_state.rws ++ rws; opts := fpOptR;
                              choices := choicesR|>’]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
      (* Case: getOpClass o' = Reals *)
      >- (
      ‘~st'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[]) \\ fs[]
      )
    )
  \\ no_change_tac ‘App o' l’
  )
  (* Case: Con o' l *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Con o' l’
    )
  (* Case: ListIndex p *)
  >- (
    Cases_on ‘p’ \\ fs[perform_rewrites_def]
    \\ qpat_x_assum ‘evaluate _ _ [Con _ _] = _’ (
                      assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ Cases_on ‘do_con_check env.c o' (LENGTH l)’ \\ fs[]
    \\ qspecl_then [‘(λ(n, e).
                        if n = q then
                          perform_rewrites (cfg with optimisations := rws) r' rws e
                        else e)’, ‘l’] strip_assume_tac MAP_enumerate_MAPi
    \\ fs[EVAL “(λn e. (λ(n,e).
                          if n = q then
                            perform_rewrites (cfg with optimisations := rws) r' rws e
                          else e) (n,e))”]
    \\ pop_assum (assume_tac o GSYM) \\ fs[]
    \\ pop_assum kall_tac
    \\ fs[GSYM MAP_REVERSE]
    \\ strip_assume_tac lift_P6_perform_rws_REVERSE
    \\ pop_assum (qspec_then ‘l’ strip_assume_tac)
    \\ rfs[] \\ pop_assum drule
    \\ Cases_on ‘evaluate st1 env
                 (MAP
                  (λ(n,e).
                     if n = q then
                       perform_rewrites (cfg with optimisations := rws) r'
                                        rws e
                     else e) (REVERSE (enumerate 0 l)))’ \\ fs[]
    \\ Cases_on ‘r''’ \\ fs[] \\ Cases_on ‘build_conv env.c o' (REVERSE a)’ \\ fs[] \\ rveq
    \\ disch_then (qspecl_then [‘st1’, ‘q'’, ‘env’, ‘cfg’, ‘rws’, ‘a’, ‘r'’, ‘q’, ‘0’]
                   strip_assume_tac) \\ rfs[]
    \\ fs[GSYM MAP_REVERSE] \\ rfs[]
    \\ fs[evaluate_def]
    \\ qexistsl_tac [‘fpOpt’, ‘choices’]
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
    \\ no_change_tac ‘Con o' l’
  )
  (* Case: Letrec l e *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Letrec l e’
    )
  (* Case: ListIndex _ *)
  >- no_change_tac ‘Letrec l e’
  (* Case: Center *)
  >- (
    qpat_x_assum ‘evaluate _ _ [Letrec _ _] = _’ (
                      assume_tac o SIMP_RULE bool_ss [evaluate_def, CaseEq"prod", CaseEq"result"])
    \\ fs[] \\ rveq
    \\ Cases_on ‘ALL_DISTINCT (MAP (λ(x,y,z). x) l)’ \\ fs[]
    \\ fs[evaluate_def]
    \\ qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ e] = _ ⇒ _’ mp_tac
    \\ disch_then (qspecl_then [‘st1’, ‘st2’, ‘(env with v := build_rec_env l env env.v)’,
                                ‘cfg’, ‘rws’, ‘r’, ‘o'’] strip_assume_tac)
    \\ rfs[]
    \\ qexistsl_tac [‘fpOpt’, ‘choices’] \\ fs[]
    \\ fs[semState_comp_eq, fpState_component_equality]
    )
  \\ no_change_tac ‘Letrec l e’
  )
  (* Case: Lit l *)
  >- (
  REVERSE (Cases_on ‘path’) \\ fs[perform_rewrites_def]
  (* Case: Here *)
  >- (
    Cases_on ‘cfg.canOpt’ \\ fs[]
    (* Does rewrite *)
    >- fs[is_rewriteFPexp_list_correct_def]
    (* Does not rewrite *)
    >- no_change_tac ‘Lit l’
    )
  \\ no_change_tac ‘Lit l’
  )
  (* Case: ?? *)
  >- fs[]
  (* Case: ?? *)
  >- fs[]
  (* Case: ?? *)
  >- (
  Cases_on ‘p’ \\ Cases_on ‘i = 0’ \\ fs[]
  \\ fs[o_DEF]
  >- (
    ‘∀l: (pat # exp) list. MAPi (λ x (n, e'). (n, e')) l = l’ by (
      Induct \\ fs[]
      \\ fs[FORALL_PROD, o_DEF]
      )
    \\ fs[evaluate_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    >- (
      qpat_x_assum ‘evaluate_match _ _ _ l _ = _’ (
                      mp_then Any assume_tac (prep (CONJUNCT2 evaluate_fp_rws_append)))
      \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] strip_assume_tac)
      \\ qpat_x_assum ‘evaluate_match _ _ _ l _ = _’ (mp_then Any mp_tac (CONJUNCT2 evaluate_add_choices))
      \\ disch_then (qspec_then ‘st1.fp_state.choices’ assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    >- (
      qpat_x_assum ‘∀ st1 st2 env cfg rws r path.
                       _ ∧ _ ∧ _ ∧ _ ∧ evaluate _ _ [perform_rewrites _ _ _ r'] = _ ⇒ _’ mp_tac
      \\ disch_then (qspecl_then [‘st1’, ‘st2’, ‘(env with v := nsAppend (alist_to_ns a) env.v)’,
                                  ‘cfg’, ‘rws’, ‘r’, ‘path’] strip_assume_tac)
      \\ rfs[]
      \\ qexistsl_tac [‘fpOpt’, ‘choices’]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
    >- (
    fs[evaluate_def]
    \\ ntac 2 (TOP_CASE_TAC \\ fs[])
    >- (
      pop_assum mp_tac
      \\ qmatch_goalsub_abbrev_tac ‘evaluate_match _ _ _ (MAPi selFun _) _ = _’
      \\ ‘selFun = λx (p,e).
                    if x = i - 1 then
                      (p, perform_rewrites (cfg with optimisations := rws) path rws e)
                    else (p,e)’ by (
        unabbrev_all_tac \\ fs[FUN_EQ_THM]
        \\ rpt strip_tac \\ TOP_CASE_TAC \\ fs[]
        )
      \\ pop_assum (rewrite_tac o single)
      \\ rpt strip_tac \\ unabbrev_all_tac
      \\ qpat_x_assum ‘∀st1 st2 env cfg rws r v err_v path i.
                      _ ∧ _ ∧ _ ∧ _ ∧ evaluate_match _ _ _ _ _ = _ ⇒ _’ (
                        qspecl_then [
                            ‘st1’, ‘st2’, ‘env’, ‘cfg’, ‘rws’, ‘r’, ‘v’, ‘err_v’, ‘path’, ‘i - 1’
                          ] strip_assume_tac
                        )
      \\ rfs[]
      \\ qexistsl_tac [‘fpOpt’, ‘choices’]
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    >- (
      qpat_x_assum ‘evaluate _ _ [r'] = _’ (
                     mp_then Any assume_tac (prep (CONJUNCT1 evaluate_fp_rws_append)))
      \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] strip_assume_tac)
      \\ fs[semState_comp_eq, fpState_component_equality]
      \\ qexistsl_tac [‘fpOpt’, ‘st1.fp_state.choices’, ‘st2.fp_state.opts’, ‘st2.fp_state.choices’]
      \\ imp_res_tac (CONJUNCT1 evaluate_add_choices)
      \\ fs[semState_comp_eq, fpState_component_equality]
      )
    )
  )
  (* Case: ?? *)
  >- fs[evaluate_def]
QED
end;

Theorem REVERSE_no_optimisations:
  REVERSE (MAP (\e. no_optimisations cfg e) exps) =
  MAP (no_optimisations cfg) (REVERSE exps)
Proof
  Induct_on `exps` \\ fs[]
QED

Theorem is_optimise_correct_lift:
  (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_rewriteFPexp_list_correct rws st1 st2 env exps r) ⇒
  (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
    is_optimise_correct rws st1 st2 env cfg exps r)
Proof
  rpt strip_tac
  \\ simp[is_optimise_correct_def]
  \\ assume_tac (List.nth ((CONJ_LIST 7 (SIMP_RULE std_ss [] optimise_correct)), 6))
  \\ qspec_then ‘exps’ mp_tac (SIMP_RULE std_ss [] lift_P6)
  \\ impl_tac
  >- (first_x_assum (qspec_then ‘exps’ mp_tac) \\ fs[])
  \\ pop_assum kall_tac \\ strip_tac
  \\ rpt strip_tac
  \\ first_x_assum (qspecl_then [‘st1’,‘st2’,‘env’,‘cfg’,‘rws’,‘r’] mp_tac)
  \\ impl_tac
  >- (
   rpt conj_tac \\ fs[]
   \\ ‘(λ e. optimise (cfg with optimisations := rws) e) = optimise (cfg with optimisations := rws) ’
     by (fs[FUN_EQ_THM])
   \\ pop_assum (fs o single))
  \\ rpt strip_tac \\ fsrw_tac [SATISFY_ss] []
QED

Definition is_perform_rewrites_correct_def:
  is_perform_rewrites_correct rws (st1:'a semanticPrimitives$state) st2 env cfg e r path =
  (evaluate st1 env [perform_rewrites cfg path rws e] = (st2, Rval r) ∧
   (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
   st1.fp_state.canOpt ≠ Strict ∧
   (~ st1.fp_state.real_sem) ⇒
   ∃ fpOpt choices fpOptR choicesR.
     evaluate (st1 with fp_state := st1.fp_state with
                                       <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env [e] =
     (st2 with fp_state := st2.fp_state with
                              <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r))
End


Theorem is_optimise_with_plan_correct_lift_sing:
  ∀ plan.
    (∀ rws path.
       MEM (path, rws) plan ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
         is_perform_rewrites_correct rws st1 st2 env cfg e r path) ⇒
    (∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
       is_optimise_with_plan_correct st1 st2 env cfg plan [e] r)
Proof
  Induct_on ‘plan’
  \\ rpt strip_tac
  \\ simp[is_optimise_with_plan_correct_def]
  >- (
  rpt strip_tac
  \\ fs[optimise_with_plan_def]
  \\ qexistsl_tac [‘st1.fp_state.opts’, ‘st1.fp_state.choices’,
                   ‘st2.fp_state.opts’, ‘st2.fp_state.choices’]
  \\ ‘st1 with
           fp_state :=
             st1.fp_state with
             <|rws := st1.fp_state.rws; opts := st1.fp_state.opts;
               choices := st1.fp_state.choices|> = st1’ by simp[semState_comp_eq, fpState_component_equality]
  \\ ‘st2 with
           fp_state :=
             st2.fp_state with
             <|rws := st2.fp_state.rws; opts := st2.fp_state.opts;
               choices := st2.fp_state.choices|> = st2’ by simp[semState_comp_eq, fpState_component_equality]
  \\ simp[semState_comp_eq, fpState_component_equality]
  )
  \\ Cases_on ‘h’
  \\ simp[optimise_with_plan_def]
  \\ rpt strip_tac
  \\ last_x_assum mp_tac \\ impl_tac
  >- metis_tac [MEM]
  \\ simp[is_optimise_with_plan_correct_def]
  \\ rpt (disch_then (fn th => first_assum ( fn ith => mp_then Any mp_tac th ith )))
  \\ strip_tac
  \\ first_x_assum (qspecl_then [‘r'’, ‘q’] mp_tac) \\ impl_tac \\ fs[MEM]
  \\ simp[is_perform_rewrites_correct_def]
  \\ rpt (disch_then (fn th => first_assum ( fn ith => mp_then Any mp_tac th ith )))
  \\ fs[semState_comp_eq, fpState_component_equality]
  \\ strip_tac
  \\ qspecl_then [‘(st1 with
                    fp_state :=
                    st1.fp_state with
                       <|rws := st1.fp_state.rws ++ FLAT (MAP SND plan) ++ r';
                         opts := fpOpt'; choices := choices'|>)’,
                  ‘env’, ‘[e]’] strip_assume_tac (CONJUNCT1 evaluate_fp_rws_up)
  \\ fs[]
  \\ pop_assum drule
  \\ disch_then (qspec_then ‘st1.fp_state.rws ++ r' ++ FLAT (MAP SND plan)’ strip_assume_tac)
  \\ rfs[]
  \\ ‘set st1.fp_state.rws ⊆ set st1.fp_state.rws ∪ set r' ∪ set (FLAT (MAP SND plan))’ by (
    fs[GSYM UNION_ASSOC, CONJUNCT1 SUBSET_UNION] )
  \\ ‘set r' ⊆ set st1.fp_state.rws ∪ set r' ∪ set (FLAT (MAP SND plan))’ by (
    simp[Once UNION_COMM, UNION_ASSOC, CONJUNCT1 SUBSET_UNION]
    )
  \\ fs[]
  \\ qexistsl_tac [‘fpOpt''’, ‘choices'’, ‘fpOpt2’, ‘choicesR'’]
  \\ simp[semState_comp_eq, fpState_component_equality]
  \\ ‘st1.fp_state.rws = st2.fp_state.rws’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
QED

Theorem is_optimise_with_plan_correct_lift:
  ∀ plan.
    (∀ rws path.
       MEM (path, rws) plan ⇒
       ∀ (st1:'a semanticPrimitives$state) st2 env cfg e r.
         is_perform_rewrites_correct rws st1 st2 env cfg e r path) ⇒
    (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
       is_optimise_with_plan_correct st1 st2 env cfg plan exps r)
Proof
  ntac 2 strip_tac
  \\ Induct_on ‘exps’
  \\ simp[is_optimise_with_plan_correct_def]
  \\ rpt strip_tac
  >- (
  rveq \\ simp[semState_comp_eq, fpState_component_equality]
  )
  \\ drule is_optimise_with_plan_correct_lift_sing
  \\ strip_tac
  \\ simp[Once evaluate_cons]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ ( assume_tac o SIMP_RULE bool_ss [Once evaluate_cons, CaseEq"prod", CaseEq"result"] )
  \\ fs[] \\ rveq
  \\ first_x_assum (qspecl_then [‘st1’, ‘s'’, ‘env’, ‘cfg’, ‘h’, ‘vs’] strip_assume_tac)
  \\ first_x_assum (qspecl_then [‘s'’, ‘s''’, ‘env’, ‘cfg’, ‘vs'’] strip_assume_tac)
  \\ fs[is_optimise_with_plan_correct_def]
  \\ rfs[] \\ fs[]
  \\ ‘(st1.fp_state.canOpt = FPScope Opt ⇔ s'.fp_state.canOpt = FPScope Opt) ∧
        s'.fp_state.canOpt ≠ Strict ∧ ~s'.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ optUntil_tac ‘evaluate _ _ [h] = _’ ‘fpOpt'’
  \\ qexistsl_tac [‘optUntil (choicesR − choices) fpOpt fpOpt'’, ‘choices’] \\ fs[]
  \\ qpat_x_assum ‘evaluate _ _ exps = _’ (mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices))
  \\ disch_then (qspec_then ‘choicesR’ assume_tac)
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem stos_pass_sing[simp]:
  [ HD (stos_pass cfg [e]) ] = stos_pass cfg [e]
Proof
  Cases_on ‘e’ \\ simp[stos_pass_def]
QED

Theorem stos_pass_with_plans_sing[simp]:
  [ HD (stos_pass_with_plans cfg [plan] [e]) ] = stos_pass_with_plans cfg [plan] [e]
Proof
  Cases_on ‘e’ \\ simp[stos_pass_with_plans_def]
QED

Theorem opt_pass_decs_unfold:
  no_opt_decs cfg (stos_pass_decs cfg [Dlet loc p e]) =
  [Dlet loc p (HD (no_optimise_pass cfg (stos_pass cfg [e])))]
Proof
  simp[stos_pass_decs_def, no_opt_decs_def, HD]
QED

Theorem opt_pass_with_plans_decs_unfold:
  no_opt_decs cfg (stos_pass_with_plans_decs cfg [plans] [Dlet loc p e]) =
  [Dlet loc p (HD (no_optimise_pass cfg (stos_pass_with_plans cfg [plans] [e])))]
Proof
  Cases_on ‘e’
  \\ simp[stos_pass_with_plans_decs_def, no_opt_decs_def, HD]
  \\ simp[no_optimise_pass_def, HD, stos_pass_with_plans_def]
QED

Theorem opt_pass_fun_unfold:
  no_optimise_pass cfg (stos_pass cfg [Fun s e]) =
  [Fun s (HD (no_optimise_pass cfg (stos_pass cfg [e])))]
Proof
  simp[stos_pass_def, no_optimise_pass_def]
QED


Theorem opt_pass_with_plans_fun_unfold:
  no_optimise_pass cfg (stos_pass_with_plans cfg [plans] [Fun s e]) =
  [Fun s (HD (no_optimise_pass cfg (stos_pass_with_plans cfg [plans] [e])))]
Proof
  simp[stos_pass_with_plans_def, no_optimise_pass_def]
QED

Theorem opt_pass_scope_unfold:
  no_optimise_pass cfg (stos_pass cfg [FpOptimise sc e]) =
  [no_optimisations cfg (optimise cfg (FpOptimise sc e))]
Proof
  simp[stos_pass_def, optimise_def, no_optimise_pass_def]
QED

Theorem optimise_with_plan_scope:
  ∀cfg plan sc e x. optimise_with_plan cfg plan (FpOptimise sc e) = x ⇒ ∃e'. x = (FpOptimise sc e')
Proof
  Induct_on ‘plan’
  >- fs[optimise_with_plan_empty_sing]
  >- (
  rpt strip_tac
  \\ PairCases_on ‘h’
  \\ fs[optimise_with_plan_def]
  \\ Cases_on ‘h0’ \\ fs[perform_rewrites_def]
  \\ TRY ( qpat_x_assum ‘∀ cfg' sc' e'. ∃ e''. optimise_with_plan _ _ _ = _’ (
                          qspecl_then [‘cfg’, ‘sc’, ‘e’] strip_assume_tac
                          )
           \\ qexists_tac ‘e'’ \\ fs[] \\ NO_TAC
         )
  \\ qpat_x_assum ‘∀ cfg' sc' e'. ∃ e''. optimise_with_plan _ _ _ = _’ (
                    qspecl_then [‘cfg’, ‘sc’, ‘perform_rewrites <|optimisations := h1; canOpt := (sc = Opt)|> o' h1 e’] strip_assume_tac
                    )
  \\ qexists_tac ‘e'’ \\ fs[]
  )
QED

Theorem opt_pass_with_plans_scope_unfold:
  no_optimise_pass cfg (stos_pass_with_plans cfg [plan] [FpOptimise sc e]) =
  [no_optimisations cfg (optimise_with_plan cfg plan (FpOptimise sc e))]
Proof
  simp[stos_pass_with_plans_def, optimise_with_plan_def, no_optimise_pass_def]
  \\ Cases_on ‘plan’
  >- fs[optimise_with_plan_empty_sing, no_optimise_pass_def]
  >- (
  Cases_on ‘h’
  \\ fs[optimise_with_plan_def, perform_rewrites_def]
  \\ Cases_on ‘optimise_with_plan cfg t (perform_rewrites (cfg with optimisations := r) q r (FpOptimise sc e))’
  \\ fs[no_optimise_pass_def]
  \\ fs[no_optimisations_def, no_optimise_pass_def, HD]
  \\ Induct_on ‘t’
  \\ rpt strip_tac
  >- (
    fs[optimise_with_plan_empty_sing, perform_rewrites_def]
    \\ Cases_on ‘q’ \\ fs[perform_rewrites_def]
    )
  >- (
    Cases_on ‘q’ \\ fs[perform_rewrites_def]
    \\ drule optimise_with_plan_scope
    \\ strip_tac
    \\ fs[]
    )
  )
QED

Theorem opt_pass_let_unfold:
  no_optimise_pass cfg (stos_pass cfg [Let x e1 e2]) =
  [no_optimisations cfg (optimise cfg (Let x e1 e2))]
Proof
  simp[stos_pass_def, optimise_def, no_optimise_pass_def]
QED

Theorem optimise_with_plan_let:
  ∀cfg plan sc e1 e2 x a. optimise_with_plan cfg plan (Let a e1 e2) = x ⇒ ∃e1' e2'. x = (Let a e1' e2')
Proof
  Induct_on ‘plan’
  >- fs[optimise_with_plan_empty_sing]
  >- (
  rpt strip_tac
  \\ PairCases_on ‘h’
  \\ fs[optimise_with_plan_def]
  \\ Cases_on ‘h0’ \\ fs[perform_rewrites_def]
  \\ TRY (
    qpat_x_assum ‘∀ cfg' e1' e2' a. ∃ e1'' e2''. optimise_with_plan _ _ _ = _’ (
                   qspecl_then [‘cfg’, ‘perform_rewrites (cfg with optimisations := h1) o' h1 e1’, ‘e2’, ‘a’] strip_assume_tac
                   )
    \\ qexists_tac ‘e1'’ \\ qexists_tac ‘e2'’ \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    qpat_x_assum ‘∀ cfg' e1' e2' a. ∃ e1'' e2''. optimise_with_plan _ _ _ = _’ (
                   qspecl_then [‘cfg’, ‘e1’, ‘perform_rewrites (cfg with optimisations := h1) o' h1 e2’, ‘a’] strip_assume_tac
                   )
    \\ qexists_tac ‘e1'’ \\ qexists_tac ‘e2'’ \\ fs[] \\ NO_TAC
    )
  \\ TRY (
    qpat_x_assum ‘∀ cfg' e1' e2' a. ∃ e1'' e2''. optimise_with_plan _ _ _ = _’ (
                   qspecl_then [‘cfg’, ‘e1’, ‘e2’, ‘a’] strip_assume_tac
                   )
    \\ qexists_tac ‘e1'’ \\ qexists_tac ‘e2'’ \\ fs[] \\ NO_TAC
    )
  )
QED

Theorem opt_pass_with_plans_let_unfold:
  no_optimise_pass cfg (stos_pass_with_plans cfg [plan] [Let x e1 e2]) =
  [no_optimisations cfg (optimise_with_plan cfg plan (Let x e1 e2))]
Proof
  simp[stos_pass_with_plans_def, optimise_with_plan_def, no_optimise_pass_def]
  \\ Induct_on ‘plan’
  >- fs[optimise_with_plan_empty_sing, no_optimise_pass_def]
  >- (
  Cases_on ‘h’
  \\ fs[optimise_with_plan_def, perform_rewrites_def]
  \\ Cases_on ‘optimise_with_plan cfg plan (perform_rewrites (cfg with optimisations := r) q r (Let x e1 e2))’
  \\ fs[no_optimise_pass_def, no_optimisations_def]
  \\ Induct_on ‘r’
  \\ rpt strip_tac
  \\ fs[optimise_with_plan_empty_sing, perform_rewrites_def]
  \\ Cases_on ‘q’ \\  fs[perform_rewrites_def]
  \\ drule optimise_with_plan_let
  \\ fs[]
  )
QED


Theorem genlist_is_all_distinct:
  ∀ f i. (∀ a b. a ≠ b ⇒ f a ≠ f b) ⇒ ALL_DISTINCT (GENLIST f i)
Proof
  fs[ALL_DISTINCT_GENLIST]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘∀ a b. _ ⇒ _’ (qspecl_then [‘m1’, ‘m2’] strip_assume_tac)
  \\ qspecl_then [‘m1 ≠ m2’, ‘f m1 ≠ f m2’] strip_assume_tac (GEN_ALL MONO_NOT_EQ) \\ fs[]
QED

Theorem FIND_exists:
  ∀ P l. (∃ x. MEM x l ∧ P x) ⇒ FIND P l ≠ NONE
Proof
  Induct_on ‘l’ \\ fs[]
  \\ rpt strip_tac
  \\ qpat_x_assum ‘∀P. _ ⇒ _’ (qspec_then ‘P’ assume_tac)
  \\ fs[FIND_thm] \\ rveq
  \\ Cases_on ‘P h’ \\ fs[]
  \\ qpat_x_assum ‘_ ⇒ _’ imp_res_tac
QED

Theorem longer_and_distinct_exists:
  ∀ l l'. ALL_DISTINCT l ∧ LENGTH l > LENGTH l' ⇒ ∃ x. MEM x l ∧ ~ MEM x l'
Proof
  rpt strip_tac
  \\ qspec_then ‘set l'’ strip_assume_tac LESS_CARD_DIFF \\ fs[]
  \\ pop_assum (qspec_then ‘set l’ strip_assume_tac) \\ fs[]
  \\ rfs[Once ALL_DISTINCT_CARD_LIST_TO_SET]
  \\ qspec_then ‘l'’ strip_assume_tac (GEN_ALL CARD_LIST_TO_SET)
  \\ fs[]
  \\ ‘CARD (set l') < LENGTH l’ by fs[]
  \\ fs[]
  \\ ‘CARD (set l) − CARD (set l ∩ set l') = CARD ((set l) DIFF (set l'))’ by fs[CARD_DIFF_EQN]
  \\ ‘0 < CARD (set l DIFF set l')’ by fs[]
  \\ ‘(set l DIFF set l') ≠ ∅’ by (
    qspec_then ‘set l DIFF set l'’ strip_assume_tac CARD_EQ_0
    \\ ‘FINITE (set l DIFF set l')’ by fs[FINITE_DIFF]
    \\ qpat_x_assum ‘FINITE _ ⇒ _’ imp_res_tac
    \\ Cases_on ‘set l DIFF set l' = ∅’ \\ simp[]
    \\ qpat_x_assum ‘set l DIFF set l' = ∅ ⇒ CARD (set l DIFF set l') = 0’ imp_res_tac
    \\ pop_assum mp_tac \\ qpat_x_assum ‘0 < CARD (set l DIFF set l')’ mp_tac
    \\ rpt (pop_assum kall_tac)
    \\ rpt strip_tac
    \\ pop_assum (assume_tac o GSYM)
    \\ decide_tac
    )
  \\ qspec_then ‘set l DIFF set l'’ imp_res_tac CHOICE_DEF
  \\ fs[DIFF_applied]
  \\ qexists_tac ‘CHOICE (set l DIFF set l')’
  \\ fs[]
QED

Theorem all_distinct_MEM_FIND:
  ∀ l l'. ALL_DISTINCT l ∧ LENGTH l > LENGTH l' ⇒ FIND (λ x. ~MEM x l') l = v ⇒ v ≠ NONE
Proof
  rpt strip_tac
  \\ qspecl_then [‘(λ x. ~MEM x l')’, ‘l’] strip_assume_tac FIND_exists
  \\ fs[]
  \\ qspecl_then [‘l’, ‘l'’] imp_res_tac longer_and_distinct_exists
  \\ qpat_x_assum ‘_ ⇒ _’ imp_res_tac
QED

Theorem generate_unique_name_some:
  ∀ identifiers base v. generate_unique_name identifiers base = v ⇒ ∃ x. v = SOME x
Proof
  fs[generate_unique_name_def]
  \\ rpt strip_tac
  \\ ‘ALL_DISTINCT (GENLIST (λi. STRCAT (STRCAT base "_") (toString i)) (LENGTH identifiers + 1))’ by (
    qspecl_then [‘(λi. STRCAT (STRCAT base "_") (toString i))’, ‘(LENGTH identifiers + 1)’] strip_assume_tac genlist_is_all_distinct
    \\ pop_assum irule \\ fs[]
    )
  \\ ‘LENGTH (GENLIST (λi. STRCAT (STRCAT base "_") (toString i)) (LENGTH identifiers + 1)) > LENGTH identifiers’ by fs[]
  \\ qspecl_then [‘(GENLIST (λi. STRCAT (STRCAT base "_") (toString i)) (LENGTH identifiers + 1))’, ‘identifiers’] imp_res_tac all_distinct_MEM_FIND
  \\ fs[]
  \\ Cases_on ‘FIND (λx. ~MEM x identifiers)
               (GENLIST (λi. STRCAT (STRCAT base "_") (toString i))
                (LENGTH identifiers + 1))’
  \\ fs[]
QED

Theorem FIND_result_fulfills:
  ∀ P l v. FIND P l = SOME v ⇒ P v
Proof
  Induct_on ‘l’ \\ fs[]
  \\ fs[FIND_thm]
  \\ rpt strip_tac
  \\ Cases_on ‘P h’ \\ fs[] \\ rveq \\ fs[]
QED

Theorem generate_unique_name_is_unique:
  ∀ identifiers base v. generate_unique_name identifiers base = SOME v ⇒ ~ MEM v identifiers
Proof
  fs[generate_unique_name_def]
  \\ rpt strip_tac
  \\ qspecl_then [‘(λx. ~MEM x identifiers)’,
                  ‘(GENLIST (λi. STRCAT (STRCAT base "_") (toString i)) (LENGTH identifiers + 1))’,
                  ‘v’] imp_res_tac FIND_result_fulfills
  \\ fs[]
QED

Triviality v_size_ALOOKUP:
  ∀ ls n v.
  ALOOKUP ls n = SOME v ⇒
  v_size v + 1 < v3_size ls + c
Proof
  Induct_on ‘ls’ \\ fs[ALOOKUP_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ fs[ALOOKUP_def]
  \\ Cases_on ‘q = n’ \\ fs[] \\ rveq
  \\ fs[semanticPrimitivesTheory.v_size_def]
  \\ res_tac
  \\ fs[]
QED

Triviality v2_size_ALOOKUP:
  ∀ ls s env.
  ALOOKUP ls s = SOME env ⇒
  v2_size env < v4_size ls + c
Proof
  Induct_on ‘ls’ \\ fs[ALOOKUP_def]
  \\ rpt strip_tac \\ Cases_on ‘h’ \\ fs[ALOOKUP_def]
  \\ Cases_on ‘q = s’ \\ fs[] \\ rveq
  \\ fs[semanticPrimitivesTheory.v_size_def]
  \\ res_tac
  \\ fs[]
QED

Theorem env_size_decreasing:
  ∀ env x v.
  nsLookup env x = SOME v ⇒
  v_size v + 1 < v2_size env
Proof
  ho_match_mp_tac namespaceTheory.nsLookup_ind
  \\ rpt strip_tac
  \\ fs[namespaceTheory.nsLookup_def, semanticPrimitivesTheory.v_size_def, CaseEq"option"]
  >- (imp_res_tac v_size_ALOOKUP \\ metis_tac[])
  \\ res_tac \\ fs[]
  \\ imp_res_tac v2_size_ALOOKUP
  \\ first_x_assum (qspec_then ‘v3_size env + 1’ assume_tac) \\ fs[]
QED

Definition v_sim_def[simp]:
  (v_sim [] [] ⇔ T)∧
  (v_sim (x1::y1::z1) (x2::y2::z2) ⇔ (v_sim [x1] [x2] ∧ v_sim (y1::z1) (y2::z2))) ∧
  (v_sim [FP_WordTree fp1] [FP_WordTree fp2] ⇔ compress_word fp1 = compress_word fp2)∧
  (v_sim [FP_BoolTree fp1] [FP_BoolTree fp2] ⇔ compress_bool fp1 = compress_bool fp2)∧
  (v_sim [Conv ts1 vs1] [Conv ts2 vs2] ⇔ (ts1 = ts2) ∧ v_sim vs1 vs2 )∧
  (v_sim [Vectorv vs1] [Vectorv vs2] ⇔ v_sim vs1 vs2 )∧
  (v_sim [Closure env s e] [Closure env2 s2 e2] ⇔ e = e2 ∧ s = s2 ∧ env_sim (env.v) (env2.v)) ∧
  (v_sim [Recclosure env1 defs1 n1] [Recclosure env2 defs2 n2] ⇔
            defs1 = defs2 ∧ n1 = n2 ∧ env_sim (env1.v) (env2.v)) ∧
  (v_sim v1 v2 ⇔  v1 = v2)
  ∧
  env_sim env1 env2 =
    ((∀ (x:(string,string) id) v1.
      nsLookup env1 x = SOME v1 ⇒
      ∃ v2. nsLookup env2 x = SOME v2 ∧
      v_sim [v1] [v2]) ∧
    (∀ x. nsLookup env1 x = NONE ⇒ nsLookup env2 x = NONE))
Termination
  wf_rel_tac ‘measure (λ x. case x of | INR p => ((v2_size o FST) p)+2 | INL p => (v7_size o FST) p)’
  \\ fs[] \\ conj_tac
  >- (rpt strip_tac \\ Cases_on ‘env’ \\ fs[semanticPrimitivesTheory.v_size_def])
  \\ conj_tac
  >- ( Cases_on`env1` \\ simp[semanticPrimitivesTheory.v_size_def] )
  \\ rpt strip_tac
  \\ imp_res_tac env_size_decreasing
  \\ fs[semanticPrimitivesTheory.v_size_def]
End

val v_sim_ind = theorem"v_sim_ind";

Definition v_sim1_def[simp]:
  (v_sim1 (FP_WordTree fp1) (FP_WordTree fp2) ⇔ compress_word fp1 = compress_word fp2)∧
  (v_sim1 (FP_BoolTree fp1) (FP_BoolTree fp2) ⇔ compress_bool fp1 = compress_bool fp2)∧
  (v_sim1 (Conv ts1 vs1) (Conv ts2 vs2) ⇔ (ts1 = ts2) ∧ v_sim vs1 vs2 )∧
  (v_sim1 (Vectorv vs1) (Vectorv vs2) ⇔ v_sim vs1 vs2 ) ∧
  (v_sim1 (Closure env s e) (Closure env2 s2 e2) ⇔ e = e2 ∧ s = s2 ∧ env_sim (env.v) (env2.v)) ∧
  (v_sim1 (Recclosure env1 defs1 n1) (Recclosure env2 defs2 n2) ⇔
            defs1 = defs2 ∧ n1 = n2 ∧ env_sim (env1.v) (env2.v)) ∧
  (v_sim1 v1 v2 ⇔ (v1 = v2))
End

Theorem v_sim_LIST_REL:
  (∀v1 v2. v_sim v1 v2 ⇔ LIST_REL v_sim1 v1 v2) ∧
  (∀ env1 env2. env_sim env1 env2 ⇒ T)
Proof
  ho_match_mp_tac v_sim_ind \\ rw[] \\ Cases_on`v6` \\ rw[]
QED

Theorem v_sim_empty_r:
  ∀ xs ys. v_sim xs ys ∧ ys = [] ⇒ xs = []
Proof
  rw[v_sim_LIST_REL] \\ fs[]
QED

Theorem v_sim_empty_l:
  ∀ xs ys. v_sim xs ys ∧ xs = [] ⇒ ys = []
Proof
  rw[v_sim_LIST_REL] \\ fs[]
QED

Definition noopt_sim_def[simp]:
  noopt_sim (Rerr (Rraise v1)) (Rerr (Rraise v2)) = v_sim1 v1 v2 ∧
  noopt_sim ((Rerr e1):(v list, v) semanticPrimitives$result) v2 = (v2 = Rerr e1) ∧
  noopt_sim (Rval vs1) (Rval vs2) = v_sim vs1 vs2 ∧
  noopt_sim _ _ = F
End

Theorem noopt_sim_val[simp]:
  noopt_sim (Rval vs1) v2 ⇒
  ∃ vs2. v2 = Rval vs2
Proof
  Cases_on ‘v2’ \\ simp[noopt_sim_def]
QED

Theorem noopt_sim_val_fp[simp]:
  noopt_sim (Rval [FP_WordTree fp1]) (Rval vs2) ⇒
  ∃ fp2. vs2 = [FP_WordTree fp2] ∧ compress_word fp1 = compress_word fp2
Proof
  simp[noopt_sim_def]
  \\ Cases_on`vs2` \\ simp[]
  \\ Cases_on`t` \\ simp[]
  \\ Cases_on`h` \\ simp[]
QED

Theorem v_sim_cons:
  v_sim (x::xs) (y::ys) ⇔ v_sim [x] [y] ∧ v_sim xs ys
Proof
  rw[v_sim_LIST_REL]
QED

Theorem v_sim_refl[simp]:
  ∀ vs. v_sim vs vs ∧ ∀ env. env_sim env env
Proof
  `(∀vs1 vs2. vs1 = vs2 ⇒ v_sim vs1 vs2) ∧ (∀ env1 env2. env1 = env2 ⇒ env_sim env1 env2)` suffices_by rw[]
  \\ ho_match_mp_tac v_sim_ind \\ rw[]
  \\ res_tac \\ fs[]
QED

Theorem v_sim1_refl[simp]:
  ∀v. v_sim1 v v
Proof
  `∀v1 v2. (v1 = v2) ⇒ v_sim1 v1 v2` suffices_by rw[]
  \\ recInduct v_sim1_ind \\ rw[]
QED

Theorem noopt_sim_refl[simp]:
  noopt_sim r r
Proof
  Cases_on ‘r’ \\ simp[noopt_sim_def]
  \\ Cases_on`e` \\ simp[]
QED

Theorem noopt_sim_rerr_rval[simp]:
  ¬noopt_sim (Rerr x) (Rval y) ∧
  ¬noopt_sim (Rval z) (Rerr w)
Proof
  Cases_on`x` \\ Cases_on`w` \\ simp[]
QED

Theorem v_sim_fpoptimise:
  (∀ vs1 vs2.
  v_sim vs1 vs2 ⇒
  v_sim (do_fpoptimise annot1 vs1) (do_fpoptimise annot2 vs2))
  ∧
  (∀ env1 env2.
   env_sim env1 env2 ⇒ T)
Proof
  ho_match_mp_tac v_sim_ind
  \\ fs[v_sim_def, do_fpoptimise_def, fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  \\ fs[v_sim_LIST_REL, LIST_REL_APPEND_suff]
QED

Theorem do_log_v_sim1:
  ∀v1 v2.
  v_sim1 v1 v2 ⇒
  ∀ e1 e2.
    do_log l v2 e2 =
    case do_log l v1 e1 of
    | NONE => NONE
    | SOME (Val v) => SOME (Val v)
    | SOME (Exp _) => SOME (Exp e2)
Proof
  simp[do_log_def, Boolv_def]
  \\ Cases \\ Cases \\ simp[]
  \\ rpt gen_tac \\ strip_tac \\ rveq \\ fs[]
  \\ Cases_on`l'` \\ Cases_on`l''` \\ fs[v_sim_LIST_REL]
  \\ rw[]
QED

Theorem pmatch_v_sim1:
  (∀envC refs p v env.
     ∀v2 env2.  v_sim1 v v2 ∧ MAP FST env = MAP FST env2 ∧ v_sim (MAP SND env) (MAP SND env2)  ⇒
     case pmatch envC refs p v env of
     | Match_type_error => pmatch envC refs p v2 env2 = Match_type_error
     | No_match => pmatch envC refs p v2 env2 = No_match
     | Match env3 => ∃env4. pmatch envC refs p v2 env2 = Match env4 ∧
                            MAP FST env3 = MAP FST env4 ∧ v_sim (MAP SND env3) (MAP SND env4)) ∧
  (∀envC refs ps vs env.
     ∀vs2 env2. v_sim vs vs2 ∧ MAP FST env = MAP FST env2 ∧ v_sim (MAP SND env) (MAP SND env2)  ⇒
     case pmatch_list envC refs ps vs env of
     | Match_type_error => pmatch_list envC refs ps vs2 env2 = Match_type_error
     | No_match => pmatch_list envC refs ps vs2 env2 = No_match
     | Match env3 => ∃env4. pmatch_list envC refs ps vs2 env2 = Match env4 ∧
                            MAP FST env3 = MAP FST env4 ∧ v_sim (MAP SND env3) (MAP SND env4))
Proof
  ho_match_mp_tac pmatch_ind
  \\  rw[pmatch_def] \\  rw[pmatch_def]
  \\ TRY(Cases_on`v2` \\ fs[pmatch_def])
  \\ rveq \\ fs[pmatch_def]
  \\ imp_res_tac v_sim_LIST_REL \\ imp_res_tac LIST_REL_LENGTH
  \\ fs[pmatch_def]
  \\ TRY(fs[v_sim_LIST_REL] \\ NO_TAC)
  \\ every_case_tac \\ fs[] \\ rveq \\ fs[v_sim_LIST_REL] \\ rfs[]
  \\ fs[GSYM v_sim_LIST_REL] \\ res_tac \\ fs[] \\ rfs[]
QED

Theorem can_pmatch_all_v_sim1:
  ∀envC refs ps v1 v2.
    v_sim1 v1 v2 ⇒
      can_pmatch_all envC refs ps v1 = can_pmatch_all envC refs ps v2
Proof
  Induct_on`ps`
  \\ rw[can_pmatch_all_def]
  \\ drule (CONJUNCT1 pmatch_v_sim1)
  \\ disch_then(qspecl_then[`envC`,`refs`,`h`,`[]`,`[]`]mp_tac)
  \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ strip_tac \\ simp[]
QED

val _ = augment_srw_ss[rewrites[fp_translate_def]];

Theorem fp_translate_v_sim1:
  v_sim1 v1 v2 ⇒
    case fp_translate v1 of
    | NONE => fp_translate v2 = NONE
    | SOME w1 => ∃w2. fp_translate v2 = SOME w2 ∧ v_sim1 w1 w2
Proof
  Cases_on`v1` \\ Cases_on`v2` \\ rw[]
  \\ Cases_on`l` \\ rw[]
QED

(* TODO: move *)
Theorem do_eq_refl:
  (∀v1 v2.  v1 = v2 ⇒ do_eq v1 v2 = Eq_val T) ∧
  (∀v1 v2 .  v1 = v2 ⇒ do_eq_list v1 v2 = Eq_val T)
Proof
  ho_match_mp_tac do_eq_ind \\ rw[do_eq_def]
QED

Theorem do_eq_v_sim1:
  (∀v1 v2 v3 v4.
     v_sim1 v1 v2 ∧ v_sim1 v3 v4 ⇒
       do_eq v1 v3 = do_eq v2 v4) ∧
  (∀v1 v2 v3 v4.
    v_sim v1 v2 ∧ v_sim v3 v4 ⇒
      do_eq_list v1 v3 = do_eq_list v2 v4)
Proof
  ho_match_mp_tac do_eq_ind \\ rw[do_eq_def]
  \\ Cases_on`v3` \\ Cases_on`v4` \\ fs[do_eq_def, Boolv_def] \\ rw[]
  \\ rw[] \\ fs[v_sim_LIST_REL] \\ rfs[] \\ fs[]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs[]
  \\ TRY(Cases_on`l1` \\ fs[do_eq_def] \\ NO_TAC)
  \\ TRY (qmatch_assum_rename_tac`v_sim1 v3 v4`
          \\ Cases_on`v3` \\ Cases_on`v4` \\ fs[do_eq_def] \\ NO_TAC)
  \\ TRY(Cases_on`l` \\ fs[do_eq_def] \\ NO_TAC)
  \\ res_tac \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
  \\ first_x_assum irule \\ rw[]
  \\ `do_eq v2 v2 = Eq_val T` suffices_by metis_tac[v_sim1_refl]
  \\ rw[do_eq_refl]
QED

Theorem v_to_char_list_v_sim1:
  ∀x y. v_sim1 x y ⇒ v_to_char_list x = v_to_char_list y
Proof
  recInduct v_to_char_list_ind
  \\ rw[v_to_char_list_def]
  \\ TRY(Cases_on`y`) \\ fs[]
  \\ rveq \\ fs[v_to_char_list_def, v_sim_LIST_REL]
  \\ rveq \\ fs[]
  \\ TRY(Cases_on`y`) \\ fs[CaseEq"option", v_to_char_list_def]
  \\ TRY(Cases_on`v`) \\ fs[ v_to_char_list_def]
  \\ rveq \\ fs[]
  \\ qmatch_assum_rename_tac`v_sim l1 l2`
  \\ qmatch_goalsub_rename_tac`Conv name l1`
  \\ first_x_assum(qspec_then`Conv name l2` mp_tac)
  \\ simp[v_to_char_list_def]
  \\ metis_tac[option_CASES]
QED

Theorem v_to_list_v_sim1:
  ∀x y. v_sim1 x y ⇒
    case v_to_list x of
    NONE => v_to_list y = NONE
    | SOME v2 => ∃v3. v_to_list y = SOME v3 ∧ v_sim v2 v3
Proof
  recInduct v_to_list_ind
  \\ rw[v_to_list_def]
  \\ TRY(Cases_on`y`) \\ fs[]
  \\ rveq \\ fs[v_to_list_def, v_sim_LIST_REL]
  \\ rveq \\ fs[]
  \\ first_x_assum drule
  \\ fs[CaseEq"option"]
  \\ TOP_CASE_TAC \\ fs[]
  \\ strip_tac \\ fs[]
QED

Theorem vs_to_string_v_sim:
  ∀x y. v_sim x y ⇒ vs_to_string x = vs_to_string y
Proof
  recInduct vs_to_string_ind
  \\ rw[vs_to_string_def]
  \\ TRY(Cases_on`y`) \\ fs[]
  \\ rveq \\ fs[vs_to_string_def, v_sim_LIST_REL]
  \\ rveq \\ fs[vs_to_string_def]
  \\ TRY(Cases_on`h`) \\ fs[vs_to_string_def]
  \\ first_x_assum drule \\ fs[]
QED

Theorem list_to_v_v_sim1:
  ∀l1 l2.
  v_sim l1 l2
  ⇒
  v_sim1 (list_to_v l1) (list_to_v l2)
Proof
  Induct \\ rw[list_to_v_def]
  \\ fs[v_sim_LIST_REL, list_to_v_def]
QED

(*
Globals.max_print_depth := 8
*)

Triviality sv_rel_v_sim1_refl:
  LIST_REL (sv_rel v_sim1) x x
Proof
  irule EVERY2_refl \\ rw[]
QED

val _ = augment_srw_ss[rewrites[sv_rel_v_sim1_refl]];

Theorem do_app_v_sim:
  v_sim v1 v2 ⇒
    case do_app x op v1 of
    | NONE => do_app x op v2 = NONE
    | SOME ((sv1, y), r1) => ∃sv2 r2. do_app x op v2 = SOME ((sv2, y), r2) ∧
                               LIST_REL (sv_rel v_sim1) sv1 sv2 ∧ (isPureOp op ⇒ sv1 = sv2) ∧
                               noopt_sim (list_result r1) (list_result r2)
Proof
  rw[v_sim_LIST_REL]
  \\ TOP_CASE_TAC
  >- (
    pop_assum mp_tac
    \\ Cases_on`x`
    \\ simp[Once do_app_def]
    \\ strip_tac
    \\ fs[CaseEq"list"] \\ rveq \\ fs[] \\ rveq \\ fs[]
    >- rw[do_app_def]
    \\ fs[CaseEq"list", CaseEq"option", CaseEq"op"] \\ rveq \\ fs[] \\ rveq
    \\ TRY (simp[do_app_def] \\ NO_TAC)
    \\ fs[CaseEq"v", CaseEq"list", CaseEq"lit", CaseEq"word_size", CaseEq"eq_result", CaseEq"option"]
    \\ rveq \\ fs[] \\ rveq \\ fs[]
    \\ TRY (simp[do_app_def]
            \\ TRY(qmatch_assum_rename_tac`fp_translate fpv = _` \\ Cases_on`fpv` \\ fs[] \\ rveq
                   \\ TRY(qmatch_assum_rename_tac`fp_translate (Litv l) = _` \\ Cases_on`l`)
                   \\ fs[] \\ rveq)
            \\ rpt(qmatch_assum_rename_tac`v_sim1 (_ _) v2` \\ Cases_on`v2` \\ fs[] \\ rveq)
            \\ NO_TAC)
    \\ TRY (CHANGED_TAC(imp_res_tac do_eq_v_sim1) \\ rw[do_app_def] \\ fs[] \\ NO_TAC)
    \\ TRY (CHANGED_TAC(imp_res_tac fp_translate_v_sim1) \\ rfs[] \\ rw[do_app_def]
            \\ TOP_CASE_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[] \\ TOP_CASE_TAC \\ fs[] \\ NO_TAC)
    >- ( fs[do_app_def, store_assign_def, store_v_same_type_def] )
    >- ( fs[do_app_def, store_alloc_def] )
    >- ( fs[do_app_def, CaseEq"option"] \\ imp_res_tac v_to_char_list_v_sim1 \\ fs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[]
         \\ imp_res_tac vs_to_string_v_sim \\ fs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[v_sim_LIST_REL]
         \\ imp_res_tac LIST_REL_LENGTH
         \\ TOP_CASE_TAC \\ fs[] )
    >- ( fs[do_app_def, store_alloc_def] \\ TOP_CASE_TAC \\ fs[] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[store_alloc_def]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ fs[v_sim_LIST_REL] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ fs[store_assign_def, store_v_same_type_def] )
    >- ( fs[do_app_def] \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ TOP_CASE_TAC \\ fs[]
         \\ fs[store_assign_def, store_v_same_type_def] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] )
    >- ( fs[do_app_def] \\ imp_res_tac v_to_list_v_sim1 \\ rfs[] ))
  \\ TOP_CASE_TAC
  \\ TOP_CASE_TAC
  \\ Cases_on`x`
  \\ pop_assum(strip_assume_tac o REWRITE_RULE[semanticPrimitivesPropsTheory.do_app_cases])
  \\ rveq \\ fs[] \\ simp[do_app_def] \\ rveq \\ fs[]
  \\ TRY(rpt (TOP_CASE_TAC \\ fs[]) \\ NO_TAC)
  >- ( imp_res_tac do_eq_v_sim1 \\ fs[] )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_cmp_def, fpSemTheory.compress_bool_def]  )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_uop_def, fpSemTheory.compress_word_def]  )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_bop_def, fpSemTheory.compress_word_def]  )
  >- (
    imp_res_tac fp_translate_v_sim1 \\ fs[]
    \\ TOP_CASE_TAC \\ fs[] \\ rfs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ TOP_CASE_TAC \\ fs[]
    \\ fs[fpValTreeTheory.fp_top_def, fpSemTheory.compress_word_def]  )
  >- (
    fs[store_assign_def, store_v_same_type_def]
    \\ rveq \\ fs[isPureOp_def]
    \\ irule EVERY2_LUPDATE_same \\ fs[] )
  >- (
    fs[store_alloc_def, isPureOp_def] \\ rveq
    \\ irule LIST_REL_APPEND_suff \\ fs[] )
  >- ( imp_res_tac v_to_char_list_v_sim1 \\ fs[] )
  >- (
    imp_res_tac v_to_list_v_sim1 \\ rfs[]
    \\ imp_res_tac vs_to_string_v_sim \\ fs[] )
  >- ( imp_res_tac v_to_list_v_sim1 \\ rfs[] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[v_sim_LIST_REL]
    \\ fs[LIST_REL_EL_EQN] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    TOP_CASE_TAC \\ fs[] \\ fs[v_sim_LIST_REL]
    \\ imp_res_tac LIST_REL_LENGTH \\ fs[] )
  >- (
    fs[store_alloc_def, isPureOp_def] \\ rveq
    \\ irule LIST_REL_APPEND_suff \\ fs[]
    \\ simp[LIST_REL_REPLICATE_same] )
  >- (
    fs[store_assign_def, store_v_same_type_def, isPureOp_def] \\ rveq
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_refl \\ fs[])
  >- (
    fs[store_assign_def, store_v_same_type_def, isPureOp_def] \\ rveq
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_LUPDATE_same \\ fs[]
    \\ irule EVERY2_refl \\ fs[])
  \\ imp_res_tac v_to_list_v_sim1
  \\ rfs[]
  \\ fs[v_sim_LIST_REL]
  \\ irule list_to_v_v_sim1
  \\ fs[v_sim_LIST_REL]
  \\ irule LIST_REL_APPEND_suff
  \\ fs[]
QED

Theorem build_conv_v_sim:
  v_sim v1 v2 ⇒  OPTREL v_sim1 (build_conv envc x v1 ) (build_conv envc x v2)
Proof
  rw[build_conv_def]
  \\ TOP_CASE_TAC \\ simp[OPTREL_def]
  \\ TOP_CASE_TAC \\ simp[]
  \\ TOP_CASE_TAC \\ simp[]
QED

(** Proofs about no_optimisations **)
local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
   ∀ st env cfg st2 r choices fpScope.
   evaluate st env [no_optimisations cfg e] = (st2, r) ∧
   st.fp_state.canOpt ≠ FPScope Opt ∧
   isPureExp e ⇒
     ∀ env2.
       env_sim (env.v) env2 ⇒
       ∃ choices2 r2.
         evaluate
           (st with fp_state :=
            st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices |>)
        (env with v := env2) [e] =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) ∧ noopt_sim r r2”
  (* P4: string * exp -> bool *)
  val P4 =
  Parse.Term (‘λ (s:string, e). ^P0 e’);
  (* P2: string * string * exp -> bool *)
  val P2 =
  Parse.Term (‘λ (s1:string, s2:string, e). ^P0 e’);
  (* Letrec goal *)
  val P1 =
  Parse.Term (‘λ (l:(string # string # exp) list).
  ∀ p. MEM p l ⇒ ^P2 p’)
  (* P5: pat * exp -> bool *)
  val P5 =
  Parse.Term (‘λ (p:pat, e). ^P0 e’)
  (* P3: pat * exp list -> bool *)
  val P3 =
  Parse.Term (‘λ (pes:(pat # exp) list).
  ∀ st env v cfg err_v st2 r cfg choices fpScope.
  evaluate_match st env v (MAP (λ (p,e). (p, no_optimisations cfg e)) pes) err_v = (st2, r) ∧
  st.fp_state.canOpt ≠ FPScope Opt ∧
  isPurePatExpList pes ⇒
    ∀ env2 v2 err_v2. env_sim env.v env2 ∧ v_sim1 v v2 ∧ v_sim1 err_v err_v2 ⇒
    ∃ choices2 r2.
      evaluate_match
        (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices|>)
      (env with v := env2) v2 pes err_v2 =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) ∧ noopt_sim r r2’);
  (* P6: exp list -> bool *)
  val P6 =
    Parse.Term (‘λ (es:ast$exp list). ∀ e. MEM e es ⇒ ^P0 e’);
  val ind_thm =
    astTheory.exp_induction |> SPEC P0 |> SPEC P1 |> SPEC P2 |> SPEC P3
    |> SPEC P4 |> SPEC P5 |> SPEC P6;
in

Triviality lift_P6_noopt_REVERSE:
  ∀ es.
    ^P6 es ⇒
   ∀ (st:'a semanticPrimitives$state) env cfg st2 r choices fpScope.
   evaluate st env (MAP (no_optimisations cfg) es) = (st2, r) ∧
   st.fp_state.canOpt ≠ FPScope Opt ∧
   isPureExpList es ⇒
     ∀ env2.
     env_sim env.v env2 ⇒
     ∃ choices2 r2.
       evaluate
         (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices |>)
        (env with v := env2) es =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) ∧
        noopt_sim r r2
Proof
  Induct \\ fs[]
  >- rw[semanticPrimitivesTheory.state_component_equality,fpState_component_equality]
  \\ srw_tac[DNF_ss][]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ rw[Once evaluate_cons]
  \\ rw[Once evaluate_cons]
  \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- metis_tac[])
  \\ strip_tac \\ fs[]
  \\ fs[CaseEq"prod"]
  \\ last_x_assum (first_assum o mp_then Any (qspecl_then[`choices`, `fpScope`]strip_assume_tac))
  \\ ntac 2 (first_x_assum (first_assum o mp_then Any assume_tac))
  \\ fs[isPureExp_def] \\ rfs[]
  \\ reverse(fs[CaseEq"result"] \\ rveq \\ Cases_on`r2` \\ fs[noopt_sim_def])
  >- rw[semanticPrimitivesTheory.state_component_equality,fpState_component_equality]
  \\ fs[CaseEq"prod"]
  \\ first_x_assum (first_assum o mp_then Any (qspecl_then[`choices2`, `fpScope`]strip_assume_tac))
  \\ ntac 2 (first_x_assum (first_assum o mp_then Any assume_tac)) \\ fs[]
  \\ ‘s'.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ fs[]
  \\ qmatch_asmsub_abbrev_tac`evaluate s1 envA es`
  \\ qmatch_goalsub_abbrev_tac`evaluate s11 envA es`
  \\ `s1 = s11` by (
    rw[Abbr`s1`, Abbr`s11`, semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[FUN_EQ_THM])
  \\ fs[Abbr`s1`, Abbr`s11`]
  \\ Cases_on`r2` \\ fs[noopt_sim_def]
  \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
  \\ rw[semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
  \\ imp_res_tac evaluate_fp_opts_inv \\ fs[FUN_EQ_THM]
  \\ fs[v_sim_LIST_REL, LIST_REL_APPEND_suff]
QED

Theorem no_optimisations_backwards_sim:
  (∀ e. ^P0 e) ∧ (∀ l. ^P1 l) ∧ (∀ p. ^P2 p) ∧ (∀ l. ^P3 l) ∧ (∀ p. ^P4 p)
  ∧ (∀ p. ^P5 p) ∧ (∀ l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[]
  \\ rpt strip_tac
  \\ (qpat_x_assum ‘evaluate _ _ _  = _’ mp_tac
      ORELSE qpat_x_assum ‘evaluate_match _ _ _ _ _ = _’ mp_tac
     ORELSE ALL_TAC)
  \\ fs[isPureExp_def]
  \\ simp[no_optimisations_def, Once evaluate_def]
  >- (
   ntac 2 (reverse TOP_CASE_TAC  \\ fs[])
   \\ res_tac
   \\ ntac 2 (first_x_assum (first_assum o mp_then Any strip_assume_tac))
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] strip_assume_tac)
   >- (
    Cases_on`r2` \\ strip_tac \\ rveq \\ fs[]
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq, noopt_sim_def])
   \\ imp_res_tac noopt_sim_val \\ rveq \\ fs[noopt_sim_def, do_if_def]
   \\ imp_res_tac evaluate_sing \\ rveq \\ fs[v_sim_LIST_REL, v_sim1_def] \\ rveq
   \\ rename1 ‘v1 = Boolv T’
   \\ Cases_on ‘v1 = Boolv T’ \\ rveq \\ fs[Boolv_def] \\ rveq
   >- (
    rpt strip_tac
    \\ Cases_on ‘v’ \\ fs[v_sim1_def] \\ rveq
    \\ ‘q.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ res_tac
    \\ rpt (first_x_assum (qspecl_then [‘fpScope’, ‘choices2’] assume_tac))
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq,
          noopt_sim_def, do_if_def, Boolv_def]
    \\ Cases_on ‘l’ \\ fs[v_sim_def]
    \\ ‘st.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope|> =
       q.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope |>’
     by (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
    \\ pop_assum (fs o single)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
   \\ TOP_CASE_TAC \\ fs[]
   >- (
    strip_tac \\ rveq \\ fs[evaluate_def, do_if_def]
    \\ Cases_on ‘v = Boolv T’ \\ fs[v_sim1_def]
    >- (‘v1 = Boolv T’ suffices_by (rveq \\ fs[Boolv_def])
        \\ Cases_on ‘v1’ \\ fs[v_sim1_def, Boolv_def]
        \\ imp_res_tac v_sim_empty_r \\ fs[] \\ rveq)
    \\ Cases_on ‘v = Boolv F’ \\ fs[v_sim1_def]
    >- (‘v1 = Boolv F’ suffices_by (rveq \\ fs[Boolv_def])
        \\ Cases_on ‘v1’ \\ fs[v_sim1_def, Boolv_def]
        \\ imp_res_tac v_sim_empty_r \\ fs[] \\ rveq)
    \\ fs[fpState_component_equality, semState_comp_eq])
    \\ rpt strip_tac
    \\ Cases_on ‘v’ \\ fs[v_sim1_def] \\ rveq
    \\ ‘q.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ res_tac
    \\ rpt (first_x_assum (qspecl_then [‘fpScope’, ‘choices2’] assume_tac))
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq,
          noopt_sim_def, do_if_def, Boolv_def]
    \\ Cases_on ‘l’ \\ fs[v_sim_def]
    \\ ‘st.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope|> =
        q.fp_state with <| rws := []; opts := (λ x. []); choices := choices2; canOpt := FPScope fpScope |>’
      by (imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
    \\ pop_assum (fs o single)
    \\ fs[fpState_component_equality, semState_comp_eq]
    \\ imp_res_tac evaluate_fp_opts_inv \\ fs[fpState_component_equality, semState_comp_eq, FUN_EQ_THM])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ last_x_assum (first_x_assum o mp_then Any assume_tac)
    \\ pop_assum (first_assum o mp_then Any (qspecl_then[`choices`,`fpScope`]strip_assume_tac))
    \\ pop_assum (first_assum o mp_then Any strip_assume_tac)
    \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
    \\ ‘st.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length
    \\ fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[v_sim_LIST_REL]
    \\ drule do_log_v_sim1
    \\ disch_then(qspecl_then[`l`,`no_optimisations cfg e0`,`e0`]strip_assume_tac)
    \\ simp[] \\ rveq \\ fs[]
    \\ fs[CaseEq"option", CaseEq"exp_or_val"] \\ rveq \\ fs[] \\ rfs[]
    \\ TRY (rw[semState_comp_eq, fpState_component_equality, noopt_sim_def] \\ PROVE_TAC[])
    \\ `e' = no_optimisations cfg e0` by (fs[do_log_def, CaseEq"bool"] \\ rveq \\ fs[Boolv_def])
    \\ rveq \\ fs[]
    \\ last_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`]strip_assume_tac))
    \\ rpt (pop_assum (first_assum o mp_then Any strip_assume_tac))
    \\ qmatch_asmsub_abbrev_tac`evaluate s1 envA [e0]`
    \\ qmatch_goalsub_abbrev_tac`evaluate s11 envA [e0]`
    \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rveq \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`]strip_assume_tac))
    \\ ntac 2 (pop_assum (first_assum o mp_then Any strip_assume_tac))
    \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
    \\ ‘st.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length
    \\ fs[LENGTH_EQ_NUM_compute] \\ rveq \\ fs[v_sim_LIST_REL]
    \\ rveq \\ fs[]
    \\ last_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`]strip_assume_tac))
    \\ qmatch_asmsub_abbrev_tac`evaluate s1 _ [e0]`
    \\ qmatch_goalsub_abbrev_tac`evaluate s11 _ [e0]`
    \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rveq \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rename1 ‘nsOptBind so v env2’
    \\ first_x_assum (qspec_then ‘nsOptBind so v env2’ mp_tac)
    \\ impl_tac
    >- (Cases_on ‘so’ \\ fs[namespaceTheory.nsOptBind_def]
        \\ fs[v_sim_def]
        \\ rpt strip_tac \\ Cases_on ‘x''’
        \\ TRY (fs[ml_progTheory.nsLookup_nsBind_compute]
                \\ TOP_CASE_TAC \\ fs[])
        \\ fs[namespaceTheory.nsBind_def])
    \\ strip_tac
    \\ fs[sem_env_component_equality, semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
  >- (
   rpt strip_tac \\ rveq \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] strip_assume_tac)
   \\ fs[ semState_comp_eq, fpState_component_equality])
  >- (
   rpt strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] strip_assume_tac)
   \\ fs[ semState_comp_eq, fpState_component_equality])
     (** Old case ...
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ simp[Once evaluate_def]
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- simp[] \\ strip_tac
    \\ reverse(fs[CaseEq"result", CaseEq"error_result"] \\ rveq \\ fs[noopt_sim_def])
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    >- (
      Cases_on`e'` \\ fs[]
      \\ imp_res_tac can_pmatch_all_v_sim1 \\ fs[]
      \\ reverse(fs[CaseEq"bool", MAP_MAP_o, o_DEF, UNCURRY, ETA_AX]) \\ rveq \\ fs[]
      >- simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
      \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT2 evaluate_fp_opts_inv))
      \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`,`env2`,`a`,`a`]mp_tac))
      \\ impl_tac >- simp[] \\ strip_tac
      \\ qmatch_asmsub_abbrev_tac`evaluate_match s1`
      \\ qmatch_goalsub_abbrev_tac`evaluate_match s11`
      \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
      \\ rw[]
      \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
    \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM]) **)
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ simp[Once evaluate_def]
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- simp[] \\ strip_tac
    \\ reverse(fs[CaseEq"result", CaseEq"error_result"] \\ rveq \\ fs[noopt_sim_def])
    \\ ‘st.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length \\ fs[LENGTH_EQ_NUM_compute] \\ rveq
    \\ fs[v_sim_LIST_REL] \\ rveq
    \\ drule can_pmatch_all_v_sim1
    \\ strip_tac \\ fs[]
    \\ reverse(fs[CaseEq"bool", MAP_MAP_o, o_DEF, UNCURRY, ETA_AX])
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT2 evaluate_fp_opts_inv))
    \\ qmatch_assum_rename_tac`v_sim1 v1 v2`
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`,`fpScope`,`env2`, `v2`, `bind_exn_v`]mp_tac))
    \\ impl_tac >- simp[] \\ strip_tac
    \\ qmatch_asmsub_abbrev_tac`evaluate_match s1 _ v2`
    \\ qmatch_goalsub_abbrev_tac`evaluate_match s11 _ v2`
    \\ `s1 = s11` by simp[Abbr`s1`, Abbr`s11`, semState_comp_eq, fpState_component_equality, FUN_EQ_THM]
    \\ rw[]
    \\ simp[semState_comp_eq, fpState_component_equality, FUN_EQ_THM])
  >- (
   rpt gen_tac
   \\ simp[no_optimisations_def, Once evaluate_def] \\ strip_tac
   \\ res_tac \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac) \\ fs[]
   \\ simp[evaluate_def, fpState_component_equality, semState_comp_eq])
  >- (
   rpt gen_tac
   \\ simp[no_optimisations_def, Once evaluate_def]
   \\ strip_tac \\ fs[CaseEq"prod"]
   \\ first_x_assum(first_x_assum o mp_then Any (qspecl_then[`choices`,`f`,`env2`]mp_tac))
   \\ simp[] \\ strip_tac
   \\ Cases_on`st.fp_state.canOpt = Strict` \\ fs[CaseEq"result"] \\ rveq \\ fs[]
   \\ Cases_on`r2` \\ fs[]
   \\ rw[semState_comp_eq, fpState_component_equality, v_sim_fpoptimise])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality])
  (** Unused case
  >- (
   simp[evaluate_def, semState_comp_eq, fpState_component_equality]
   \\ rpt strip_tac \\ rveq
   \\ fs[noopt_sim_def]) **)
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
  (** Unused case
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
    \\ simp[Once evaluate_def]
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- simp[] \\ strip_tac
    \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
    \\ Cases_on`r2` \\ fs[noopt_sim_def]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ simp[semState_comp_eq, fpState_component_equality]
    \\ imp_res_tac evaluate_length
    \\ fs[LENGTH_EQ_NUM_compute]
    \\ rveq \\ fs[v_sim_LIST_REL]) **)
  >- (
   TOP_CASE_TAC \\ fs[] \\ rpt strip_tac
   \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality]
   \\ rveq \\ res_tac
   \\ fs[noopt_sim_def, semState_comp_eq, fpState_component_equality])
  >- (
    strip_tac \\ fs[CaseEq"prod"]
    \\ fsrw_tac[ETA_ss][GSYM MAP_REVERSE]
    \\ qspec_then`REVERSE l`mp_tac lift_P6_noopt_REVERSE
    \\ simp[PULL_FORALL]
    \\ disch_then(first_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- (
      simp[] \\ rpt gen_tac \\ rpt strip_tac
      \\ first_x_assum drule \\ disch_then drule
      \\ disch_then match_mp_tac \\ simp[] )
    \\ strip_tac \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"result"]) \\ Cases_on`r2` \\ fs[] \\ rveq \\ fs[]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ fs[CaseEq"op_class"]
    >- (Cases_on ‘o'’ \\ fs[astTheory.getOpClass_def, isPureOp_def])
    \\ `v_sim (REVERSE vs) (REVERSE a)` by fs[v_sim_LIST_REL]
    \\ drule do_app_v_sim
    \\ qmatch_asmsub_abbrev_tac`do_app x op`
    \\ disch_then(qspecl_then[`x`,`op`]mp_tac)
    \\ map_every qunabbrev_tac[`x`,`op`]
    \\ TRY (
      fs[CaseEq"bool",CaseEq"option",CaseEq"prod"] \\ rveq \\ fs[]
      \\ TRY(strip_tac \\ fs[])
      \\ rw[semState_comp_eq, fpState_component_equality, shift_fp_opts_def]
      \\ Cases_on`st.fp_state.real_sem` \\ fs[noopt_sim_def]
      \\ imp_res_tac evaluate_fp_opts_inv \\ fs[]
      \\ NO_TAC )
    \\ TOP_CASE_TAC \\ fs[]
    >- ( rw[semState_comp_eq, fpState_component_equality] )
    \\ fs[CaseEq"prod"] \\ strip_tac \\ fs[]
    \\ rveq \\ fs[]
    \\ ‘st'.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[]
    \\ Cases_on ‘fpScope = Opt’
    \\ fs[do_fprw_def, rwAllWordTree_def, rwAllBoolTree_def, shift_fp_opts_def,
          semState_comp_eq, fpState_component_equality]
    \\ Cases_on ‘isFpBool o'’ \\ fs[]
    \\ Cases_on ‘r'’ \\ Cases_on ‘r2’ \\ fs[noopt_sim_def]
    \\ fs[v_sim_LIST_REL]
    \\ Cases_on ‘a'’ \\ Cases_on ‘a''’ \\ fs[v_sim1_def])
  >- (
    strip_tac \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"bool"])
    >- simp[semState_comp_eq, fpState_component_equality]
    \\ fs[CaseEq"prod"]
    \\ fsrw_tac[ETA_ss][GSYM MAP_REVERSE]
    \\ qspec_then`REVERSE l`mp_tac lift_P6_noopt_REVERSE
    \\ simp[PULL_FORALL]
    \\ disch_then(first_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ impl_tac >- (
      simp[] \\ rpt gen_tac \\ rpt strip_tac
      \\ first_x_assum drule \\ disch_then drule
      \\ disch_then match_mp_tac \\ simp[] )
    \\ strip_tac \\ simp[]
    \\ reverse(fs[CaseEq"result"]) \\ Cases_on`r2` \\ fs[] \\ rveq \\ fs[]
    >- rw[semState_comp_eq, fpState_component_equality]
    \\ `v_sim (REVERSE vs) (REVERSE a)` by fs[v_sim_LIST_REL]
    \\ drule build_conv_v_sim
    \\ qmatch_goalsub_rename_tac`build_conv env.c xx _`
    \\ disch_then(qspecl_then[`xx`,`env.c`]mp_tac)
    \\ simp[OPTREL_def] \\ strip_tac \\ fs[] \\ rveq \\ fs[]
    \\ rw[semState_comp_eq, fpState_component_equality]
    \\ fs[v_sim_LIST_REL])
  (** Unused case:
  >- (
    strip_tac \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"bool"])
    >- simp[semState_comp_eq, fpState_component_equality]
    \\ first_x_assum (first_x_assum o mp_then Any mp_tac)
    \\ simp[]
    \\ disch_then match_mp_tac \\ simp[]
    \\ simp[semanticPrimitivesPropsTheory.build_rec_env_merge]
    \\ undone...
    (*
    \\ simp[namespacePropsTheory.nsLookup_nsAppend_none,
            namespacePropsTheory.nsLookup_nsAppend_some]
    \\ simp[namespacePropsTheory.nsLookup_alist_to_ns_none,
            namespacePropsTheory.nsLookup_alist_to_ns_some]
    *)) *)
  >- (rpt strip_tac \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality])
  >- (
    Cases_on`p`
    \\ simp[Once evaluate_def]
    \\ strip_tac
    \\ simp[Once evaluate_def]
    \\ reverse(fs[CaseEq"bool"])
    >- simp[semState_comp_eq, fpState_component_equality]
    \\ last_assum (mp_then Any mp_tac (CONJUNCT1 pmatch_v_sim1))
    \\ disch_then (qspecl_then[`env.c`,`st.refs`,`q`,`[]`,`[]`]mp_tac)
    \\ simp[]
    \\ reverse(fs[CaseEq"match_result"])
    \\ TRY(simp[semState_comp_eq, fpState_component_equality]
           \\ rveq \\ fsrw_tac[DNF_ss][] \\ NO_TAC)
    >- (
      strip_tac \\ fs[]
      \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT1 evaluate_fp_opts_inv))
      \\ qmatch_goalsub_abbrev_tac`evaluate _ (env with v := env22)`
      \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env22`]mp_tac))
      \\ impl_tac >- (
        fs[isPureExp_def]
        \\ qmatch_assum_rename_tac`MAP FST env1 = MAP FST env4`
        \\ qmatch_goalsub_abbrev_tac `nsLookup env11`
        \\ `∀x. case nsLookup env11 x  of
                | NONE => nsLookup env22 x = NONE
                | SOME v1 => ∃v2. nsLookup env22 x = SOME v2 ∧ v_sim1 v1 v2` suffices_by (
              rw[]
              \\ first_x_assum(qspec_then`x`mp_tac) \\ rw[]
              \\ rw[v_sim_LIST_REL] )
        \\ gen_tac
        \\ simp[Abbr`env22`, Abbr`env11`]
        \\ TOP_CASE_TAC \\ fs[namespacePropsTheory.nsLookup_nsAppend_none]
        \\ fs[namespacePropsTheory.nsLookup_alist_to_ns_none, ALOOKUP_FAILS]
        \\ TRY (Cases_on`p1` \\ fs[namespacePropsTheory.nsLookupMod_alist_to_ns] \\ NO_TAC)
        >- (
          rw[]
          \\ `∀x. MEM x (MAP FST env1) = MEM x (MAP FST env4)` by simp[]
          \\ fs[MEM_MAP, EXISTS_PROD]
          \\ metis_tac[] )
        \\ reverse(fs[namespacePropsTheory.nsLookup_nsAppend_some])
        \\ fs[namespacePropsTheory.nsLookup_alist_to_ns_some,
              namespacePropsTheory.nsLookup_alist_to_ns_none]
        >- (
          res_tac \\ fs[v_sim_LIST_REL]
          \\ goal_assum(first_assum o mp_then Any mp_tac)
          \\ simp[]
          \\ disj2_tac
          \\ conj_tac
          >- (
            fs[ALOOKUP_FAILS]
            \\ `∀x. MEM x (MAP FST env1) = MEM x (MAP FST env4)` by simp[]
            \\ fs[MEM_MAP, EXISTS_PROD]
            \\ metis_tac[] )
          \\ Cases \\ simp[] )
        \\ fs[ALOOKUP_LEAST_EL]
        \\ rfs[]
        \\ rveq
        \\ simp[]
        \\ fs[v_sim_LIST_REL]
        \\ fs[LIST_REL_EL_EQN]
        \\ first_x_assum match_mp_tac
        \\ numLib.LEAST_ELIM_TAC
        \\ fs[MEM_EL]
        \\ conj_tac >- metis_tac[]
        \\ CCONTR_TAC \\ fs[]
        \\ `n < n'` by simp[]
        \\ metis_tac[] )
      \\ rw[] )
    \\ first_assum (mp_then Any strip_assume_tac (CONJUNCT2 evaluate_fp_opts_inv))
    \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`,`fpScope`,`env2`]mp_tac))
    \\ fs[isPureExp_def] )
  >- (rpt strip_tac \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality] \\ rw[])
QED
end;

Theorem no_optimisations_eval_sim =
  CONJUNCT1 (SIMP_RULE std_ss [] no_optimisations_backwards_sim)
  |> SPEC_ALL
  |> GEN “es:ast$exp list”
  |> SPEC “[e:ast$exp]”
  |> UNDISCH_ALL
  |> SPEC “(env:v sem_env).v”
  |> DISCH_ALL
  |> SIMP_RULE std_ss [MAP, v_sim_refl]
  |> GEN_ALL ;

(** Real-valued identitites preserve real semantics **)

Definition is_real_id_exp_def:
  is_real_id_exp rws (st1:'a semanticPrimitives$state) st2 env e r =
    (evaluate st1 env [realify (rewriteFPexp rws e)] = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = T ⇒
    ∃ choices.
      evaluate st1 env [realify e] =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Definition is_real_id_list_def:
  is_real_id_list rws (st1:'a semanticPrimitives$state) st2 env exps r =
    (evaluate st1 env (MAP realify (MAP (rewriteFPexp rws) exps)) = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = T ⇒
    ∃ choices.
      evaluate st1 env (MAP realify exps) =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Theorem empty_rw_real_id:
   ∀ (st1 st2:'a semanticPrimitives$state) env e r.
     is_real_id_exp [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_real_id_exp_def, rewriteFPexp_def]
  \\ fs[fpState_component_equality, semState_comp_eq]
QED

Definition is_real_id_optimise_def:
  is_real_id_optimise rws (st1:'a semanticPrimitives$state) st2 env cfg exps r =
    (evaluate st1 env
             (MAP realify (MAP (optimise (cfg with optimisations := rws)) exps)) = (st2, Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧
    st1.fp_state.real_sem ⇒
    ∃ choices.
      evaluate st1 env (MAP realify exps) =
        (st2 with fp_state := st2.fp_state with
           <| choices := choices|>, Rval r))
End

Theorem real_valued_id_compositional:
  ∀ rws opt.
   (∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_real_id_exp rws st1 st2 env e r) ∧
   (∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_real_id_exp [opt] st1 st2 env e r) ⇒
  ∀ (st1 st2:'a semanticPrimitives$state) env e r.
    is_real_id_exp ([opt] ++ rws) st1 st2 env e r
Proof
  rw[is_real_id_exp_def]
  \\ qpat_x_assum `_ = (_, _)` mp_tac
  \\ PairCases_on `opt` \\ simp[rewriteFPexp_def]
  \\ reverse TOP_CASE_TAC \\ fs[]
  >- (fs[fpState_component_equality, semState_comp_eq])
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ strip_tac
  \\ last_x_assum (first_assum o mp_then Any mp_tac) \\ fs[]
  \\ strip_tac
  \\ rename [‘matchesFPexp src e [] = SOME subst’, ‘appFPexp tgt subst = SOME eOpt’]
  \\ ‘eOpt = rewriteFPexp [(src,tgt)] e’ by (fs[rewriteFPexp_def])
  \\ rveq
  \\ last_x_assum (first_assum o mp_then Any mp_tac) \\ fs[]
QED

Theorem lift_real_id_exp_list:
  ∀rws.
    (∀ (st1 st2: 'a semanticPrimitives$state) env e r.
      is_real_id_exp rws st1 st2 env e r) ⇒
  ∀exps (st1 st2:'a semanticPrimitives$state) env r.
    is_real_id_list rws st1 st2 env exps r
Proof
  strip_tac>>strip_tac>>
  simp[is_real_id_list_def]>>Induct
  >- (
    simp[evaluate_def]>>
    rw[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality])>>
  rw[]>>
  fs[Once evaluate_cons]>>
  qpat_x_assum`_ = (st2,_)` mp_tac>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  strip_tac>>rveq>>
  fs[is_real_id_exp_def]>>
  last_x_assum drule>>fs[]>>
  strip_tac>>simp[]>>
  first_x_assum drule>>
  impl_tac >-
    (drule (CONJUNCT1 evaluate_fp_opts_inv)>>simp[])>>
  strip_tac>>fs[]>>
  drule (CONJUNCT1 evaluate_add_choices)>>
  disch_then(qspec_then`choices` assume_tac)>>simp[]>>
  rw[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.fpState_component_equality]
QED

Theorem lift_real_id_exp_list_strong:
  ∀rws.
    (∀ (st1 st2: 'a semanticPrimitives$state) env e r.
      is_real_id_exp rws st1 st2 env e r) ⇒
    ∀ (st1 st2:'a semanticPrimitives$state) env exps r.
  is_real_id_list rws st1 st2 env exps r
Proof
  metis_tac[lift_real_id_exp_list]
QED

local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
      is_real_id_list rws st1 st2 env exps r) ⇒
    (∀ (st1:'a semanticPrimitives$state) st2 env cfg r.
      is_real_id_optimise rws st1 st2 env cfg [e] r)”
  (* P4: string * exp -> bool *)
  val P4 =
  Parse.Term (‘λ (s:string, e). ^P0 e’);
  (* P2: string * string * exp -> bool *)
  val P2 =
  Parse.Term (‘λ (s1:string, s2:string, e). ^P0 e’);
  (* Letrec goal *)
  val P1 =
  Parse.Term (‘λ (l:(string # string # exp) list).
  ∀ p. MEM p l ⇒ ^P2 p’)
  (* P5: pat * exp -> bool *)
  val P5 =
  Parse.Term (‘λ (p:pat, e). ^P0 e’)
  (* P3: pat * exp list -> bool *)
  val P3 =
  Parse.Term (‘λ (l:(pat # exp) list).
    ∀(st1:'a semanticPrimitives$state) env v cfg err_v st2 r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
    evaluate_match st1 env v
      (MAP (λ (p,e). (p,realify (optimise (cfg with optimisations := rws) e))) l) err_v =
      (st2,Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ⇒
    ∃choices.
      evaluate_match st1 env v (MAP (λ(p,e). (p,realify e)) l) err_v =
      (st2 with fp_state := st2.fp_state with choices := choices, Rval r)’);
  (* P6: exp list -> bool *)
  val P6 =
    Parse.Term (‘λ (es:ast$exp list). ∀ e. MEM e es ⇒ ^P0 e’);
  val ind_thm =
    astTheory.exp_induction |> SPEC P0 |> SPEC P1 |> SPEC P2 |> SPEC P3
    |> SPEC P4 |> SPEC P5 |> SPEC P6;
in

Triviality lift_P6_REVERSE:
  ∀ es.
    ^P6 es ⇒
    ∀(st1:'a semanticPrimitives$state) env cfg st2 r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
    evaluate st1 env
      (MAP (realify o optimise (cfg with optimisations := rws)) (REVERSE es)) =
      (st2,Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ⇒
    ∃choices.
      evaluate st1 env
        (MAP realify (REVERSE es)) =
        (st2 with fp_state := st2.fp_state with choices := choices, Rval r)
Proof
  simp[] \\
  Induct_on ‘es’ \\ rpt strip_tac
  >- fs[semState_comp_eq, fpState_component_equality]>>
  fs[evaluate_append]>>
  qpat_x_assum `_ = (st2, _)` mp_tac>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  rfs[]>>
  first_x_assum drule>>
  simp[]>>
  strip_tac>>simp[]>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  strip_tac>> rveq>>fs[]>>
  first_x_assum(qspec_then`h` mp_tac)>>simp[is_real_id_optimise_def]>>
  disch_then drule>>
  impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
  strip_tac>>
  drule (CONJUNCT1 evaluate_add_choices)>>
  disch_then(qspec_then`choices` assume_tac)>>
  simp[semState_comp_eq, fpState_component_equality]
QED

Triviality lift_P6:
  ∀ es.
    ^P6 es ⇒
    ∀(st1:'a semanticPrimitives$state) env cfg st2 r.
    (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
    evaluate st1 env
      (MAP (realify o optimise (cfg with optimisations := rws)) es) =
      (st2,Rval r) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    st1.fp_state.canOpt ≠ Strict ∧ st1.fp_state.real_sem ⇒
    ∃choices.
      evaluate st1 env
        (MAP realify es) =
        (st2 with fp_state := st2.fp_state with choices := choices, Rval r)
Proof
  simp[] \\
  Induct_on ‘es’ \\ rpt strip_tac
  >- fs[semState_comp_eq, fpState_component_equality]>>
  fs[Once evaluate_cons]>>
  qpat_x_assum `_ = (st2, _)` mp_tac>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  first_x_assum(qspec_then`h` mp_tac)>>simp[is_real_id_optimise_def]>>
  disch_then drule >>
  simp[]>>
  strip_tac>>
  ntac 2 (TOP_CASE_TAC>>simp[])>>
  strip_tac>> rveq>>fs[]>>
  first_x_assum drule>>
  impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
  strip_tac>>
  drule (CONJUNCT1 evaluate_add_choices)>>
  disch_then(qspec_then`choices` assume_tac)>>
  simp[semState_comp_eq, fpState_component_equality]
QED

Theorem is_real_id_list_optimise_lift1:
  (∀ e. ^P0 e) ∧ (∀ l. ^P1 l) ∧ (∀ p. ^P2 p) ∧ (∀ l. ^P3 l) ∧ (∀ p. ^P4 p)
  ∧ (∀ p. ^P5 p) ∧ (∀ l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[is_real_id_optimise_def,optimise_def] \\ rpt strip_tac
  \\ TRY (qpat_x_assum `evaluate _ _ _ = _` mp_tac)
  \\ TRY( (* 15 subogals after *)
    simp[realify_def,evaluate_def]>>
    strip_tac>>
    first_x_assum drule>>
    rpt (disch_then drule)>>simp[] >> NO_TAC)
  >- (
    (* If *)
    simp[evaluate_def, realify_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    imp_res_tac evaluate_sing \\ rveq \\ fs[] \\ rveq >>
    simp[do_if_def]>>
    rpt (IF_CASES_TAC >>simp[])>>
    (* two subgoals *)
    (strip_tac>> first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac >> simp[]>>
    first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac >> simp[]>>
    pop_assum kall_tac>>
    drule (CONJUNCT1 evaluate_add_choices)>>
    disch_then(qspec_then`choices'` assume_tac)>>
    simp[semState_comp_eq, fpState_component_equality]))
  >- (
    (* Log *)
    simp[evaluate_def, realify_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    simp[do_log_def]>>
    IF_CASES_TAC>>simp[]
    >- (
      first_x_assum drule>>
      impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
      strip_tac >> simp[]>>
      strip_tac >> simp[]>>
      first_x_assum drule>>
      impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
      strip_tac >>simp[]>>
      drule (CONJUNCT1 evaluate_add_choices)>>
      disch_then(qspec_then`choices` assume_tac)>>
      simp[semState_comp_eq, fpState_component_equality])>>
    IF_CASES_TAC>>simp[] >> strip_tac>> rveq>>
    first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac >>simp[semState_comp_eq, fpState_component_equality])
  >- (
    (* Let *)
    simp[evaluate_def, realify_def]>>
    ntac 2 (TOP_CASE_TAC >> simp[])>>
    last_x_assum drule >> disch_then drule>>
    simp[]>>
    strip_tac >> simp[]>>
    strip_tac>>
    first_x_assum drule>>
    disch_then drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac>>
    drule (CONJUNCT1 evaluate_add_choices)>>
    disch_then(qspec_then`choices` assume_tac)>>
    simp[semState_comp_eq, fpState_component_equality] )
  >- (
    (* Handle *)
    simp[realify_def,evaluate_def]>>fs[]>>
    ntac 2 (TOP_CASE_TAC>>simp[])
    >- simp[semState_comp_eq, fpState_component_equality]>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ( (* Mat *)
    simp[realify_def,evaluate_def]>>fs[]>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    first_x_assum drule>>simp[]>>
    strip_tac>>simp[]>>
    IF_CASES_TAC>> fs[MAP_MAP_o,LAMBDA_PROD,o_DEF]>>
    strip_tac>> first_x_assum drule>>
    impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
    strip_tac>>
    drule (CONJUNCT2 evaluate_add_choices)>>
    disch_then(qspec_then`choices` assume_tac)>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ((* FpOptimise *)
    simp[realify_def,evaluate_def]>>
    ntac 2 (TOP_CASE_TAC>>simp[])>>
    strip_tac>>rveq>>
    qmatch_asmsub_abbrev_tac`optimise ccfg e`>>
    `ccfg = ccfg with optimisations := rws` by
      fs[Abbr`ccfg`]>>
    qpat_x_assum`_ = (q,_)` mp_tac>>
    pop_assum SUBST1_TAC>>
    strip_tac>>
    first_x_assum drule>> disch_then drule>>
    impl_tac>-
      simp[Abbr`ccfg`]>>
    strip_tac>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ( (* Fun *)
    simp[realify_def,evaluate_def]>>
    fs[semState_comp_eq, fpState_component_equality])
  >- ( (* Raise *)
    simp[realify_def,evaluate_def]>>
    every_case_tac>>simp[])
  >- ( (* Var *)
    simp[realify_def,evaluate_def]>>
    every_case_tac>>simp[semState_comp_eq, fpState_component_equality])
  >- ((* App *)
    fs[]>>
    qspec_then `l` mp_tac (lift_P6_REVERSE |> SIMP_RULE std_ss [is_real_id_optimise_def])>>
    impl_tac >- (
      simp[]>>
      metis_tac[] )>>
    simp[]>>
    strip_tac>>
    IF_CASES_TAC>>simp[]>>
    fs[is_real_id_list_def]
    >- (
      qmatch_goalsub_abbrev_tac`_ rws exp`>>
      strip_tac>>
      first_x_assum(qspecl_then [`st1`,`st2`,`env`,`[exp]`,`r`] mp_tac)>>
      simp[]>>
      strip_tac>>
      qpat_x_assum`_ = (st2,Rval r)`kall_tac>>
      pop_assum mp_tac>>
      fs[Abbr`exp`,realify_def]>>
      Cases_on`o'`>>simp[evaluate_def,astTheory.getOpClass_def]>>
      TRY( (* 50 cases *)
      ntac 2(TOP_CASE_TAC>>simp[])>>
      fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
      first_x_assum drule>>simp[]>>
      strip_tac>>simp[]>>
      `(λa. realify a) = realify` by
        fs[ETA_AX]>>
      simp[]>>
      rpt(TOP_CASE_TAC>>simp[])>>
      simp[semState_comp_eq, fpState_component_equality]>> NO_TAC)
      >- (
        strip_tac>>
        TOP_CASE_TAC>>fs[]
        >- simp[semState_comp_eq, fpState_component_equality,dec_clock_def]>>
        TOP_CASE_TAC>>fs[]
        >- (
          pop_assum mp_tac>> fs[evaluate_def]>>
          TOP_CASE_TAC>>simp[]>>
          TOP_CASE_TAC>>simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          first_x_assum drule>> simp[]>>
          strip_tac>>simp[]>>
          ntac 4 (TOP_CASE_TAC>>simp[])>>
          simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
        TOP_CASE_TAC>>fs[]
        >- (
          qpat_x_assum`_ = (_ , Rval r)` mp_tac>>
          simp[Once evaluate_def]>>
          ntac 2 (TOP_CASE_TAC>>simp[])>>
          first_x_assum drule >> simp[]>>
          strip_tac>> simp[evaluate_def]>>
          simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          ntac 4 (TOP_CASE_TAC>>simp[])>>
          simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
        TOP_CASE_TAC>>fs[]
        >- (
          pop_assum mp_tac>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          every_case_tac>>simp[]>>strip_tac>>rveq>>fs[]>>
          rveq>>fs[]>>
          first_assum(qspec_then`h` mp_tac)>>
          first_assum(qspec_then`h'` mp_tac)>>
          first_x_assum(qspec_then`h''` mp_tac)>>
          simp[]>>
          ntac 3 strip_tac>>
          first_x_assum drule >> simp[] >> strip_tac>>
          simp[evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
          last_x_assum drule >>
          impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
          strip_tac>>
          drule (CONJUNCT1 evaluate_add_choices)>>
          disch_then(qspec_then`choices'` assume_tac)>>
          fs[]>>
          last_x_assum drule >>
          impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
          strip_tac>>
          drule (CONJUNCT1 evaluate_add_choices)>>
          disch_then(qspec_then` choices' + choices'' − q.fp_state.choices` assume_tac)>>
          fs[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])
        >>
        pop_assum mp_tac>>
        fs[evaluate_def, MAP_REVERSE,MAP_MAP_o,o_DEF]>>
        ntac 2 (TOP_CASE_TAC>>simp[])>>
        simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        first_x_assum drule>>
        simp[]>>
        strip_tac>>
        `(λa. realify a) = realify` by
          fs[ETA_AX]>>
        simp[]>>
        rpt (TOP_CASE_TAC>>simp[])>>
        simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])
      >>
      ntac 2(TOP_CASE_TAC>>simp[])>>
      fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
      first_x_assum drule>>simp[]>>
      strip_tac>>simp[]>>
      `(λa. realify a) = realify` by
        fs[ETA_AX]>>
      simp[]>>
      rpt(TOP_CASE_TAC>>simp[])>>
      simp[dec_clock_def]>> strip_tac>>
      drule (CONJUNCT1 evaluate_add_choices)>>
      disch_then(qspec_then`choices'` assume_tac)>>
      fs[]>>
      simp[semState_comp_eq, fpState_component_equality])
    >>
    simp[realify_def]>>
    Cases_on`o'`>>simp[evaluate_def,astTheory.getOpClass_def]>>
    (* 50 cases *)
    TRY(
    ntac 2(TOP_CASE_TAC>>simp[])>>
    fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
    first_x_assum drule>>simp[]>>
    strip_tac>>simp[]>>
    `(λa. realify a) = realify` by
      fs[ETA_AX]>>
    simp[]>>
    rpt(TOP_CASE_TAC>>simp[])>>
    simp[semState_comp_eq, fpState_component_equality]>> NO_TAC)
    >- (
      strip_tac>>
      TOP_CASE_TAC>>fs[]
      >- simp[semState_comp_eq, fpState_component_equality,dec_clock_def]>>
      TOP_CASE_TAC>>fs[]
      >- (
        pop_assum mp_tac>> fs[evaluate_def]>>
        TOP_CASE_TAC>>simp[]>>
        TOP_CASE_TAC>>simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        first_x_assum drule>> simp[]>>
        strip_tac>>simp[]>>
        ntac 4 (TOP_CASE_TAC>>simp[])>>
        simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
      TOP_CASE_TAC>>fs[]
      >- (
        qpat_x_assum`_ = (_ , Rval r)` mp_tac>>
        simp[Once evaluate_def]>>
        ntac 2 (TOP_CASE_TAC>>simp[])>>
        first_x_assum drule >> simp[]>>
        strip_tac>> simp[evaluate_def]>>
        simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        ntac 4 (TOP_CASE_TAC>>simp[])>>
        simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
      TOP_CASE_TAC>>fs[]
      >- (
        pop_assum mp_tac>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        simp[Once evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        every_case_tac>>simp[]>>strip_tac>>rveq>>fs[]>>
        rveq>>fs[]>>
        first_assum(qspec_then`h` mp_tac)>>
        first_assum(qspec_then`h'` mp_tac)>>
        first_x_assum(qspec_then`h''` mp_tac)>>
        simp[]>>
        ntac 3 strip_tac>>
        first_x_assum drule >> simp[] >> strip_tac>>
        simp[evaluate_def,astTheory.getOpClass_def, astTheory.isFpBool_def]>>
        last_x_assum drule >>
        impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
        strip_tac>>
        drule (CONJUNCT1 evaluate_add_choices)>>
        disch_then(qspec_then`choices` assume_tac)>>
        fs[]>>
        last_x_assum drule >>
        impl_tac >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])>>
        strip_tac>>
        drule (CONJUNCT1 evaluate_add_choices)>>
        disch_then(qspec_then` choices + choices' − q.fp_state.choices` assume_tac)>>
        fs[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])
      >>
      pop_assum mp_tac>>
      fs[evaluate_def, MAP_REVERSE,MAP_MAP_o,o_DEF]>>
      ntac 2 (TOP_CASE_TAC>>simp[])>>
      simp[astTheory.getOpClass_def, astTheory.isFpBool_def]>>
      first_x_assum drule>>
      simp[]>>
      strip_tac>>
      `(λa. realify a) = realify` by
        fs[ETA_AX]>>
      simp[]>>
      rpt (TOP_CASE_TAC>>simp[])>>
      simp[semState_comp_eq, fpState_component_equality,shift_fp_opts_def])>>
    ntac 2(TOP_CASE_TAC>>simp[])>>
    fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
    first_x_assum drule>>simp[]>>
    strip_tac>>simp[]>>
    `(λa. realify a) = realify` by
      fs[ETA_AX]>>
    simp[]>>
    rpt(TOP_CASE_TAC>>simp[])>>
    simp[dec_clock_def]>> strip_tac>>
    drule (CONJUNCT1 evaluate_add_choices)>>
    disch_then(qspec_then`choices` assume_tac)>>
    fs[]>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ((* Con *)
    simp[realify_def,evaluate_def]>>
    IF_CASES_TAC>>simp[]>>
    ntac 2(TOP_CASE_TAC>>simp[])>>
    qspec_then `l` mp_tac (lift_P6_REVERSE |> SIMP_RULE std_ss [is_real_id_optimise_def])>>
    impl_tac >- (
      simp[]>>
      metis_tac[] )>>
    disch_then drule>>
    fs[MAP_MAP_o,o_DEF,MAP_REVERSE]>>
    disch_then drule>>
    simp[]>>
    strip_tac>>
    TOP_CASE_TAC>> simp[] >>
    strip_tac>> rveq>>
    `(λa. realify a) = realify` by
      fs[ETA_AX]>>
    simp[semState_comp_eq, fpState_component_equality])
  >- ( (* Letrec *)
    simp[realify_def,evaluate_def]>>
    IF_CASES_TAC>>simp[]>>
    strip_tac>> first_x_assum drule>>
    disch_then drule >> simp[])
  >- (* Lit *)
    simp[semState_comp_eq, fpState_component_equality]
  >- (
    pairarg_tac>>fs[evaluate_def]>>
    every_case_tac>>fs[]
    >- (
      first_x_assum drule>>
      simp[] )>>
    last_x_assum drule >> simp[])>>
  simp[semState_comp_eq, fpState_component_equality]
QED
end;

Theorem is_real_id_list_optimise_lift:
  (∀ (st1:'a semanticPrimitives$state) st2 env exps r.
    is_real_id_list rws st1 st2 env exps r) ⇒
  (∀ (st1:'a semanticPrimitives$state) st2 env cfg exps r.
    is_real_id_optimise rws st1 st2 env cfg exps r)
Proof
  rw[]>>
  assume_tac is_real_id_list_optimise_lift1>>
  fs[]>>
  pop_assum(qspec_then `exps` assume_tac)>>
  assume_tac lift_P6>>
  fs[]>>
  pop_assum(qspec_then `exps` assume_tac)>>
  rfs[]>>
  simp[is_real_id_optimise_def]>>
  strip_tac>>
  fs[MAP_MAP_o]>>
  first_x_assum drule>>
  simp[]
QED

Theorem do_foptimise_cons:
  ∀y x .
  do_fpoptimise f (x::y) = (do_fpoptimise f [x]) ++ (do_fpoptimise f y)
Proof
  Induct>>EVAL_TAC>>simp[]
QED

Theorem isPureExp_no_optimisations:
  (∀e.
    isPureExp e ⇒
    isPureExp ((no_optimisations cfg) e)) ∧
  (∀es.
    isPureExpList es ⇒
    isPureExpList (MAP (no_optimisations cfg) es)) ∧
  (∀pes.
    isPurePatExpList pes ⇒
    isPurePatExpList (MAP (λ(p,e). (p,(no_optimisations cfg) e)) pes))
Proof
  ho_match_mp_tac isPureExp_ind>>
  rw[isPureExp_def, source_to_sourceTheory.no_optimisations_def]>>fs[] >>
  `(λa. (no_optimisations cfg) a) = (no_optimisations cfg)` by
      simp[FUN_EQ_THM]>>
  simp[]
QED

Theorem realify_no_optimisations_commutes_IMP:
  ∀ e cfg e2.
  realify (no_optimisations cfg e) = e2 ⇒
  no_optimisations cfg (realify e) = e2
Proof
  ho_match_mp_tac realify_ind \\ rpt strip_tac \\ fs[realify_def, no_optimisations_def]
  \\ rveq \\ fs[no_optimisations_def]
  >- (
   Induct_on ‘pes’ \\ fs[]
   \\ rpt strip_tac
   >- (Cases_on ‘h’ \\ fs[realify_def, no_optimisations_def])
   \\ first_x_assum irule
   \\ strip_tac \\ metis_tac [])
  >- (Induct_on ‘exps’ \\ fs[])
  >- (Cases_on ‘op’ \\ fs[realify_def, no_optimisations_def, CaseEq"list"]
      \\ TRY (Induct_on ‘exps’ \\ fs[no_optimisations_def] \\ NO_TAC)
      \\ Cases_on ‘exps’ \\ fs[no_optimisations_def]
      \\ Cases_on ‘t’ \\ fs[no_optimisations_def]
      \\ Cases_on ‘t'’ \\ fs[no_optimisations_def]
      \\ Cases_on ‘t’ \\ fs[no_optimisations_def]
      \\ Induct_on ‘t'’ \\ fs[no_optimisations_def]
      \\ rpt strip_tac \\ first_x_assum irule \\ metis_tac[])
  \\ Induct_on ‘pes’ \\ fs[] \\ rpt strip_tac
  >- (Cases_on ‘h’ \\ fs[realify_def, no_optimisations_def])
  \\ first_x_assum irule
  \\ strip_tac \\ metis_tac []
QED

Theorem isPureExp_realify:
  (∀e.
    isPureExp e ⇒
    isPureExp (realify e)) ∧
  (∀es.
    isPureExpList es ⇒
    isPureExpList (MAP realify es)) ∧
  (∀pes.
    isPurePatExpList pes ⇒
    isPurePatExpList (MAP (λ(p,e). (p,realify e)) pes))
Proof
  ho_match_mp_tac isPureExp_ind>>
  rw[isPureExp_def, source_to_sourceTheory.realify_def]>>fs[]
  >-
    (Cases_on`e`>>simp[isPureExp_def, source_to_sourceTheory.realify_def])
  >- (
    `(λa. realify a) = realify` by
        fs[ETA_AX]>>
    simp[])>>
  TOP_CASE_TAC>>
  `(λa. realify a) = realify` by fs[ETA_AX]>>
  fs[isPureExp_def,isPureOp_def]>>
  every_case_tac>>fs[isPureOp_def,isPureExp_def]>>
  simp[isPureOp_def]
QED

Theorem realify_no_optimisations_comm:
  realify (no_optimisations cfg e) = no_optimisations cfg (realify e)
Proof
  metis_tac [realify_no_optimisations_commutes_IMP]
QED

Theorem evaluate_no_optimisations:
  ∀ fpScope choices.
  evaluate st env [realify (no_optimisations cfg e)] = (st, Rval [Real r]) ∧
  (st.fp_state.canOpt ≠ FPScope Opt ∧ isPureExp e) ⇒
  ∃ st2.
    evaluate
      (st with fp_state := st.fp_state with
         <| rws := []; opts := (λ x. []); choices:= choices; canOpt := FPScope fpScope|>)
      env [realify e] = (st2, Rval [Real r])
Proof
  rpt strip_tac \\ fs[realify_no_optimisations_comm]
  \\ last_x_assum
     (mp_then Any mp_tac
      (SIMP_RULE std_ss [] no_optimisations_backwards_sim |> CONJUNCT1))
  \\ fs[isPureExp_realify]
  \\ disch_then (qspecl_then [‘choices’, ‘fpScope’, ‘env.v’] mp_tac)
  \\ impl_tac >- fs[]
  \\ strip_tac
  \\ imp_res_tac noopt_sim_val \\ rveq
  \\ fs[noopt_sim_def, v_sim_LIST_REL]
QED

Inductive res_sim:
  (∀ (e1:v error_result) (e2:v error_result) (cfg:config) (st1:'a semanticPrimitives$state).
   res_sim (Rerr e1) (Rerr e2) cfg st1)
  ∧
  (∀ (vs1:v list) (vs2:v list) (cfg:config) (st1:'a semanticPrimitives$state).
   v_list_sim vs1 vs2 cfg st1 ⇒
   res_sim (Rval vs1) (Rval vs2) cfg st1)
  ∧
  (∀ (cfg:config) (st1:'a semanticPrimitives$state).
   v_list_sim [] [] cfg st1) ∧
  (∀ v1 v2 vs1 vs2 cfg st1 .
   v_list_sim vs1 vs2 cfg st1 ∧
   v1 = v2 ⇒
   v_list_sim (v1::vs1) (v2::vs2) cfg st1)
  ∧
  (∀ v1 v2 vs1 vs2 cfg env s e (st1:'a semanticPrimitives$state).
   v_list_sim vs1 vs2 cfg st1 ∧
   v2 = Closure env s e ∧
   v1 = Closure env s (HD(stos_pass cfg [e])) ∧
   (∀ st r1 (st2:'a semanticPrimitives$state).
    st1.fp_state.rws = st.fp_state.rws ⇒
    evaluate st env (stos_pass cfg [e]) = (st2, Rval r1) ∧
    (cfg.canOpt ⇔ st.fp_state.canOpt = FPScope Opt) ∧
    (st.fp_state.canOpt ≠ Strict) ∧
    (~ st.fp_state.real_sem) ==>
    ∃ fpOpt choices fpOptR choicesR r2.
    (evaluate (st with fp_state := st.fp_state with
               <| rws := st.fp_state.rws ++ (cfg.optimisations) ; opts := fpOpt; choices := choices |>) env [e] =
     (st2 with fp_state := st2.fp_state with
      <| rws := st2.fp_state.rws ++ (cfg.optimisations) ; opts := fpOptR; choices := choicesR |>, Rval r2)) ∧
    res_sim (Rval r1) (Rval r2) cfg st1) ⇒
   v_list_sim (v1::vs1) (v2::vs2) cfg st1)
End

Definition is_stos_pass_correct_def :
  is_stos_pass_correct rws (st1:'a semanticPrimitives$state) st2 env cfg exps r1 =
    (evaluate st1 env
             (stos_pass (cfg with optimisations := rws) exps) = (st2, Rval r1) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     (st1.fp_state.canOpt ≠ Strict) ∧
     (~ st1.fp_state.real_sem) ==>
    ∃ fpOpt choices fpOptR choicesR r2.
      (evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt; choices := choices |>) env exps =
      (st2 with fp_state := st2.fp_state with
       <| rws := st2.fp_state.rws ++ rws; opts := fpOptR; choices := choicesR |>, Rval r2)) ∧
      res_sim (Rval r1) (Rval r2) (cfg with optimisations := rws) st1)
End

Theorem stos_pass_cons:
  stos_pass cfg (e1::es) =
  (stos_pass cfg [e1])++stos_pass cfg es
Proof
  Cases_on ‘es’ \\ fs[stos_pass_def]
QED

Theorem v_list_sim_append:
  v_list_sim (vs1 ++ vs2) (vs1 ++ vs3) cfg st1 =
  v_list_sim vs2 vs3 cfg st1
Proof
  Induct_on ‘vs1’ \\ fs[res_sim_rules]
  \\ rpt strip_tac \\ EQ_TAC
  >- (
   rpt strip_tac
   \\ last_x_assum (rewrite_tac o single o GSYM)
   \\ pop_assum (assume_tac o (SIMP_RULE std_ss [Once res_sim_cases]))
   \\ fs[])
  \\ rpt strip_tac
  \\ last_x_assum (fs o single o GSYM)
  \\ drule (List.nth (CONJ_LIST 5 res_sim_rules, 3))
  \\ disch_then (qspecl_then [‘h’, ‘h’] mp_tac) \\ fs[]
QED

Theorem res_sim_swap:
  (∀ vs1 vs2 cfg (st1:'a semanticPrimitives$state).
  res_sim vs1 vs2 cfg st1 ⇒
  ∀ (st2:'a semanticPrimitives$state).
  st1.fp_state.rws = st2.fp_state.rws ∧
  (st1.fp_state.canOpt = FPScope Opt ⇔ st2.fp_state.canOpt = FPScope Opt) ∧
  (st1.fp_state.canOpt ≠ Strict) ∧
  (~ st1.fp_state.real_sem) ⇒
  res_sim vs1 vs2 cfg st2)
  ∧
  (∀ vs1 vs2 cfg (st1:'a semanticPrimitives$state).
  v_list_sim vs1 vs2 cfg st1 ⇒
  ∀ (st2:'a semanticPrimitives$state).
  st1.fp_state.rws = st2.fp_state.rws ∧
  (st1.fp_state.canOpt = FPScope Opt ⇔ st2.fp_state.canOpt = FPScope Opt) ∧
  (st1.fp_state.canOpt ≠ Strict) ∧
  (~ st1.fp_state.real_sem) ⇒
  v_list_sim vs1 vs2 cfg st2)
Proof
  ho_match_mp_tac res_sim_ind \\ rpt conj_tac \\ rpt strip_tac
  \\ fs[Once res_sim_cases]
  >- (
   first_x_assum (qspec_then ‘st2’ mp_tac)
   \\ impl_tac \\ fs[]
   \\ strip_tac \\ rveq \\ fs[Once res_sim_rules])
  >- (
   first_x_assum (qspec_then ‘st2’ mp_tac)
   \\ impl_tac \\ fs[]
   \\ strip_tac \\ rveq \\ fs[Once res_sim_rules])
  \\ last_x_assum (qspec_then ‘st2’ mp_tac)
  \\ impl_tac \\ fs[]
  \\ strip_tac
  \\ rveq  \\ fs[Once res_sim_rules] \\ DISJ2_TAC
  \\ conj_tac \\ fs[Once res_sim_rules]
  \\ rpt strip_tac
  \\ res_tac
  \\ first_x_assum (qspec_then ‘st2’ mp_tac)
  \\ impl_tac \\ fs[] \\ strip_tac
  \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘choices'’
  \\ fs[Once res_sim_rules, semState_comp_eq, fpState_component_equality]
QED

local
  val optimise_case = fn t =>
   TOP_CASE_TAC \\ fs[]
   \\ fs[is_optimise_correct_def]
   \\ first_x_assum (qspec_then t mp_tac) \\ fs[]
   \\ rpt (disch_then drule)
   \\ strip_tac \\ fs[]
   \\ ntac 2 (TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ rveq
   \\ first_x_assum (qspec_then ‘t’ mp_tac)
   \\ impl_tac \\ fs[astTheory.exp_size_def]
   \\ rpt (disch_then drule)
   \\ impl_tac
   >- (rpt conj_tac \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
   \\ strip_tac
   \\ optUntil_tac ‘evaluate _ _ ^(Parse.Term t) = _’ ‘fpOpt'’
   \\ qexists_tac ‘optUntil (choicesR - choices) fpOpt fpOpt'’
   \\ qexists_tac ‘choices’ \\ fs[]
   \\ rpt (first_x_assum (fn thm => mp_then Any mp_tac (CONJUNCT1 evaluate_add_choices) thm \\ mp_tac thm ))
   \\ rpt (first_x_assum (fn thm => mp_then Any mp_tac (CONJUNCT2 evaluate_add_choices) thm \\ mp_tac thm ))
   \\ rpt (disch_then (qspec_then ‘choicesR’ assume_tac) ORELSE disch_then assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality]
   \\ TRY (fs[Once res_sim_rules, Once res_sim_cases] \\ NO_TAC)
   \\ irule (List.nth (CONJ_LIST 4 res_sim_rules,1))
   \\ qpat_x_assum ‘res_sim _ _ _ _’ (assume_tac o SIMP_RULE std_ss [Once res_sim_cases])
   \\ fs[v_list_sim_append]
   \\ irule (List.nth (CONJ_LIST 2 res_sim_swap,1))
   \\ qexists_tac ‘q’
   \\ rpt conj_tac \\ imp_res_tac evaluate_fp_opts_inv \\ fs[];
in
Theorem stos_pass_correct:
  ∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
  (∀ exps (st1:'a semanticPrimitives$state) st2 env cfg r.
    is_optimise_correct rws st1 st2 env cfg exps r) ⇒
   is_stos_pass_correct rws st1 st2 env cfg exps r
Proof
  measureInduct_on ‘exp6_size exps’ \\ fs[is_stos_pass_correct_def]
  \\ rpt strip_tac \\ Cases_on ‘exps’
  \\ fs[stos_pass_def,Once stos_pass_cons, semState_comp_eq, fpState_component_equality]
  >- (rveq \\ fs[res_sim_rules])
  \\ qpat_x_assum `evaluate _ _ _ = _` mp_tac
  \\ simp[Once evaluate_cons, Once evaluate_append]
  \\ Cases_on ‘evaluate st1 env (stos_pass (cfg with optimisations := rws) [h])’
  \\ Cases_on ‘h’ \\ fs[stos_pass_def]
  >- optimise_case ‘[Raise e]’
  >- optimise_case ‘[Handle e l]’
  >- optimise_case ‘[Lit l]’
  >- optimise_case ‘[Con o' l]’
  >- optimise_case ‘[Var i]’
  >- (
   TOP_CASE_TAC \\ fs[]
   \\ qpat_x_assum `evaluate _ _ [Fun _ _] = _` mp_tac
   \\ simp[evaluate_def] \\ strip_tac \\ rveq \\ fs[]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ rveq \\ fs[]
   \\ last_assum (qspec_then ‘t’ mp_tac)
   \\ impl_tac >- fs[astTheory.exp_size_def]
   \\ rpt (disch_then drule)
   \\ strip_tac
   \\ qexists_tac ‘fpOpt’ \\ qexists_tac ‘choices’
   \\ fs[semState_comp_eq, fpState_component_equality]
   \\ simp[Once res_sim_cases]
   \\ irule (List.nth (CONJ_LIST 5 res_sim_rules,4))
   \\ fs[] \\ reverse conj_tac
   >- (
    pop_assum (assume_tac o SIMP_RULE std_ss [Once res_sim_cases])
    \\ fs[])
   \\ rpt strip_tac
   \\ last_x_assum (qspec_then ‘[e]’ mp_tac) \\ impl_tac
   >- fs[astTheory.exp_size_def]
   \\ disch_then drule
   \\ impl_tac \\ fs[]
   \\ strip_tac
   \\ qexists_tac ‘fpOpt'’ \\ qexists_tac ‘choices'’
   \\ fs[semState_comp_eq, fpState_component_equality]
   \\ irule (hd (CONJ_LIST 2 res_sim_swap))
   \\ qexists_tac ‘st’ \\ fs[])
  >- optimise_case ‘[App o' l]’
  >- optimise_case ‘[Log l e e0]’
  >- optimise_case ‘[If e e0 e1]’
  >- optimise_case ‘[Mat e l]’
  >- optimise_case ‘[Let o' e e0]’
  >- optimise_case ‘[Letrec l e]’
  >- optimise_case ‘[Tannot e a]’
  >- optimise_case ‘[Lannot e l]’
  \\ optimise_case ‘[FpOptimise f e]’
QED
end;

val _ = export_theory ();
