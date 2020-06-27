(*
  Correctness proofs for floating-point optimizations
*)
open icing_rewriterTheory source_to_sourceTheory fpOptTheory fpOptPropsTheory
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


(*
Definition icing_v_sim_def:
  icing_v_sim (v1:(v list, v) result) v2 =
  case (v1, v2) of
  | (Rval r1, Rval r2) => (r1 = r2)
  | (Rerr e1, Rerr e2) => T
  | _ => F
End

Theorem icing_v_sim_val:
  icing_v_sim (Rval r1) v2 ⇔ v2 = Rval r1
Proof
  simp[icing_v_sim_def] \\ TOP_CASE_TAC \\ fs[] \\ metis_tac []
QED

Theorem icing_v_sim_err:
  icing_v_sim (Rerr e1) v2 ⇔ ∃ e2. v2 = Rerr e2
Proof
  simp[icing_v_sim_def] \\ TOP_CASE_TAC \\ fs[] \\ metis_tac []
QED

Theorem icing_v_sim_refl:
  icing_v_sim v v
Proof
  simp[icing_v_sim_def] \\ TOP_CASE_TAC \\ fs[]
QED

Theorem icing_v_sim_trans:
  icing_v_sim v1 v2 ∧
  icing_v_sim v2 v3 ⇒
  icing_v_sim v1 v3
Proof
  simp[icing_v_sim_def] \\ rpt (TOP_CASE_TAC \\ fs[])
QED

Definition icing_state_sim_def:
  icing_state_sim st1 st2 v rws =
    case v of
    | Rval r =>
    ∃ fpOptR.
      st2 = st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOptR |>
    | Rerr e =>
      st2.fp_state.rws = st1.fp_state.rws ++ rws
End

Theorem icing_state_sim_refl:
  ∀ st r rws. icing_state_sim st st r []
Proof
  simp[icing_state_sim_def] \\ Cases_on ‘r’ \\ fs[]
  \\ rpt strip_tac \\ qexists_tac ‘st.fp_state.opts’
  \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem icing_state_sim_fine:
  ∀ st r rws g.
    icing_state_sim
      st
      (st with fp_state := st.fp_state with <| rws := st.fp_state.rws ++ rws; opts := g |>)
      r rws
Proof
  rpt strip_tac \\ fs[icing_state_sim_def]
  \\ TOP_CASE_TAC \\ fs[semState_comp_eq, fpState_component_equality]
QED

Theorem icing_state_sim_fine_app:
  ∀ st r rw rws g.
    icing_state_sim
      st
      (st with fp_state := st.fp_state with <| rws := st.fp_state.rws ++ [rw] ++ rws; opts := g |>)
      r (rw::rws)
Proof
  rpt strip_tac \\ fs[icing_state_sim_def]
  \\ TOP_CASE_TAC \\ fs[semState_comp_eq, fpState_component_equality]
QED

val _ =
  bossLib.augment_srw_ss [
    bossLib.rewrites [icing_state_sim_fine, icing_state_sim_refl,
                      icing_state_sim_fine_app,
                      icing_v_sim_refl, icing_v_sim_err, icing_v_sim_val]];
*)

(* Correctness definition for rewriteFPexp
 We need to handle the case where the expression returns an error, but we cannot
 preserve the exact error, as reordering may change which error is returned *)
Definition is_rewriteFPexp_correct_def:
  is_rewriteFPexp_correct rws (st1:'a semanticPrimitives$state) st2 env e r =
    (evaluate st1 env [rewriteFPexp rws e] = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = F ⇒
    ∃ fpOpt fpOptR.
      evaluate
        (st1 with fp_state := st1.fp_state with
           <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env [e] =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r))
End

Definition is_rewriteFPexp_list_correct_def:
  is_rewriteFPexp_list_correct rws (st1:'a semanticPrimitives$state) st2 env exps r =
    (evaluate st1 env (MAP (rewriteFPexp rws) exps) = (st2, Rval r) ∧
     st1.fp_state.canOpt = FPScope Opt ∧
     st1.fp_state.real_sem = F ⇒
     ∃ fpOpt fpOptR.
       evaluate
         (st1 with fp_state := st1.fp_state with
            <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r))
End

Theorem empty_rw_correct:
   ∀ (st1 st2:'a semanticPrimitives$state) env e r.
     is_rewriteFPexp_correct [] st1 st2 env e r
Proof
  rpt strip_tac \\ fs[is_rewriteFPexp_correct_def, rewriteFPexp_def]
  \\ rpt strip_tac \\ qexists_tac `st1.fp_state.opts`
  \\ `st1 = st1 with fp_state := st1.fp_state with
          <| rws := st1.fp_state.rws; opts := st1.fp_state.opts |>`
      by (fs[semState_comp_eq, fpState_component_equality])
  \\ pop_assum (fn thm => fs[GSYM thm])
  \\ fs[fpState_component_equality, semState_comp_eq]
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
    \\ asm_exists_tac \\ fs[])
  \\ TOP_CASE_TAC \\ fs[]
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
  \\ fs[] \\ qexists_tac `fpOpt''` \\ fs[]
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
  \\ qexists_tac `optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'`
  \\ qexists_tac `fpOptR` \\ fs[]
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
    ∃ fpOpt fpOptR.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r))
End

Theorem MAP_FST_optimise:
  MAP FST (MAP (\ (p, e). (p, optimise cfg e)) l) = MAP FST l
Proof
  Induct_on `l` \\ fs[] \\ rpt strip_tac \\ PairCases_on `h` \\ fs[]
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

Theorem optimise_empty:
  ∀ exps cfg. MAP (optimise (cfg with optimisations := [])) exps = exps
Proof
  Induct_on ‘exps’ \\ rpt strip_tac
  >- (EVAL_TAC)
  \\ rpt strip_tac \\ fs[optimise_def, optimise_empty_sing]
QED

Theorem optimise_pat_empty:
  ∀ pl cfg. MAP (λ (p,e). (p, optimise (cfg with optimisations := []) e)) pl = pl
Proof
  Induct_on ‘pl’ \\ rpt strip_tac >- (EVAL_TAC)
  \\ fs[] \\ Cases_on ‘h’ \\ fs[optimise_empty_sing]
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
    ∃ fpOpt fpOptR.
      evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env [e]=
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r)”
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
     ∃ fpOpt fpOptR.
       evaluate_match
         (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>)
         env v l err_v =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r)’);
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
    ∃ fpOpt fpOptR.
      evaluate
        (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>)
        env (REVERSE es) =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r)
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
      \\ qexists_tac ‘fpOpt’
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
  \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
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
    ∃ fpOpt fpOptR.
      evaluate
        (st1 with fp_state := st1.fp_state with <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>)
        env es =
        (st2 with fp_state := st2.fp_state with
           <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, Rval r)
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
   \\ qexists_tac ‘fpOpt'’
   \\ fs[semState_comp_eq, fpState_component_equality])
  \\ strip_tac
  \\ get_ext_eval_tac ‘evaluate q env (MAP _ _) = _’
  \\ pop_assum mp_tac \\ impl_tac
  >- (imp_res_tac evaluate_fp_opts_inv \\ fs[])
  \\ rveq \\ strip_tac
  \\ optUntil_tac ‘evaluate _ _ [h] = _’ ‘fpOpt'’
  \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
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
    \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
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
   \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
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
      \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
      \\ fs[semState_comp_eq, fpState_component_equality])
   \\ Cases_on ‘l = Or ∧ HD a = Boolv T’ \\ Cases_on ‘l = And ∧ HD a = Boolv F’
   \\ fs[]
   \\ rpt strip_tac \\ rveq \\ qexists_tac ‘fpOpt’ \\ fs[]
   \\ fs[semState_comp_eq, fpState_component_equality])
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
   \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   rpt strip_tac \\ res_tac
   \\ qexists_tac ‘fpOpt’
   \\ fs[semState_comp_eq, fpState_component_equality])
  (** Old Handle case
  >- (
   simp[evaluate_def]
   \\ ntac 2 (TOP_CASE_TAC \\ fs[])
   >- (trivial_tac)
   \\ reverse TOP_CASE_TAC \\ fs[]
   >- (trivial_tac)
   \\ simp[MAP_FST_optimise]
   \\ reverse (TOP_CASE_TAC \\ fs[])
   >- (trivial_tac)
   \\ get_ext_eval_tac ‘evaluate st1 env [optimise _ e] = _’
   \\ strip_tac
   \\ ‘(cfg.canOpt ⇔ q.fp_state.canOpt = FPScope Opt) ∧ ~ q.fp_state.real_sem’
      by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
   \\ first_x_assum drule \\ rpt (disch_then drule)
   \\ strip_tac
   \\ optUntil_tac ‘evaluate _ env [e] = _’ ‘fpOpt'’
   \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
   \\ fs[semState_comp_eq, fpState_component_equality]) **)
  >- (
   rpt strip_tac
   \\ imp_res_tac (CONJUNCT1 (prep evaluate_fp_rws_append))
   \\ pop_assum (qspecl_then [‘rws’, ‘st2.fp_state.opts’] assume_tac)
   \\ fs[] \\ qexists_tac ‘fpOpt’
   \\ fs[semState_comp_eq, fpState_component_equality])
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
   \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
   \\ fs[semState_comp_eq, fpState_component_equality])
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
    \\ qexists_tac ‘fpOpt’ \\ fs[semState_comp_eq, fpState_component_equality])
  >- (
   simp[evaluate_def]
   \\ rpt strip_tac \\ rveq
   \\ fs[semState_comp_eq, fpState_component_equality])
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
     \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt'' fpOpt’
     \\ simp[evaluate_def] \\ rfs[] \\ fs[]
     \\ fs[dec_clock_def]
     \\ fs[semState_comp_eq, fpState_component_equality])
    >- (
     TOP_CASE_TAC \\ fs[]
     \\ ntac 2 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac ‘fpOpt''’ \\ fs[]
     \\ rveq \\ rfs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    >- (
     ‘q.fp_state.canOpt = FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[]
     \\ ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ fs[shift_fp_opts_def]
     \\ optUntil_tac ‘evaluate _ _ (REVERSE _) = _’ ‘q.fp_state.opts’
     \\ rfs[fpState_component_equality]
     \\ simp[evaluate_def]
     \\ qexists_tac ‘optUntil (q.fp_state.choices − st1.fp_state.choices) fpOpt'' q.fp_state.opts’
     \\ fs[] \\ TOP_CASE_TAC
     \\ ‘q.fp_state.rws = st2.fp_state.rws ++ rws’
        by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[shift_fp_opts_def]
     \\ fs[semState_comp_eq, fpState_component_equality])
    \\ fs[] \\ rveq \\ fs[]
    \\ ‘~q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[shift_fp_opts_def] \\ rpt strip_tac \\ rveq
    \\ simp[evaluate_def])
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
     \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
     \\ simp[evaluate_def] \\ rfs[] \\ fs[]
     \\ fs[dec_clock_def]
     \\ ‘q.fp_state.rws = st2.fp_state.rws’
        by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    >- (
     ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac ‘fpOpt’ \\ fs[]
     \\ rveq \\ rfs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    >- (
     ‘q.fp_state.canOpt ≠ FPScope Opt’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
     \\ fs[]
     \\ ntac 3 (TOP_CASE_TAC \\ fs[])
     \\ rpt strip_tac \\ rveq \\ simp[evaluate_def]
     \\ qexists_tac ‘fpOpt’ \\ fs[]
     \\ rveq \\ rfs[]
     \\ fs[semState_comp_eq, fpState_component_equality])
    \\ fs[] \\ rveq \\ fs[]
    \\ ‘~q.fp_state.real_sem’ by (imp_res_tac evaluate_fp_opts_inv \\ fs[])
    \\ fs[shift_fp_opts_def] \\ rpt strip_tac \\ rveq
    \\ simp[evaluate_def])
  >- (
   qpat_x_assum ‘∀ e. MEM e l ⇒ _’
     (fn thm => (mp_then Any assume_tac (SIMP_RULE std_ss [] lift_P6_REVERSE) thm))
   \\ simp [evaluate_def]
   \\ reverse TOP_CASE_TAC \\ fs[]
   \\ ntac 2 (TOP_CASE_TAC \\ fs[GSYM MAP_REVERSE])
   \\ first_x_assum drule
   \\ rpt (disch_then drule) \\ strip_tac
   \\ rpt (TOP_CASE_TAC \\ fs[]) \\ strip_tac \\ rveq \\ fs[]
   \\ qexists_tac ‘fpOpt’
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
   \\ qexists_tac ‘fpOpt’
   \\ fs[semState_comp_eq, fpState_component_equality])
  \\ fs[evaluate_def]
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

Theorem stos_pass_sing[simp]:
  [ HD (stos_pass cfg [e]) ] = stos_pass cfg [e]
Proof
  Cases_on ‘e’ \\ simp[stos_pass_def]
QED

Theorem opt_pass_decs_unfold:
  no_opt_decs cfg (stos_pass_decs cfg [Dlet loc p e]) =
  [Dlet loc p (HD (no_optimise_pass cfg (stos_pass cfg [e])))]
Proof
  simp[stos_pass_decs_def, no_opt_decs_def, HD]
QED

Theorem opt_pass_fun_unfold:
  no_optimise_pass cfg (stos_pass cfg [Fun s e]) =
  [Fun s (HD (no_optimise_pass cfg (stos_pass cfg [e])))]
Proof
  simp[stos_pass_def, no_optimise_pass_def]
QED

Theorem opt_pass_scope_unfold:
  no_optimise_pass cfg (stos_pass cfg [FpOptimise sc e]) =
  [no_optimisations cfg (optimise cfg (FpOptimise sc e))]
Proof
  simp[stos_pass_def, optimise_def, no_optimise_pass_def]
QED

Theorem opt_pass_let_unfold:
  no_optimise_pass cfg (stos_pass cfg [Let x e1 e2]) =
  [no_optimisations cfg (optimise cfg (Let x e1 e2))]
Proof
  simp[stos_pass_def, optimise_def, no_optimise_pass_def]
QED

Definition v_sim_def[simp]:
  (v_sim [] [] ⇔ T)∧
  (v_sim (x1::y1::z1) (x2::y2::z2) ⇔ (v_sim [x1] [x2] ∧ v_sim (y1::z1) (y2::z2))) ∧
  (v_sim [FP_WordTree fp1] [FP_WordTree fp2] ⇔ compress_word fp1 = compress_word fp2)∧
  (v_sim [FP_BoolTree fp1] [FP_BoolTree fp2] ⇔ compress_bool fp1 = compress_bool fp2)∧
  (v_sim [Conv ts1 vs1] [Conv ts2 vs2] ⇔ (ts1 = ts2) ∧ v_sim vs1 vs2 )∧
  (v_sim [Vectorv vs1] [Vectorv vs2] ⇔ v_sim vs1 vs2 )∧
  (v_sim v1 v2 ⇔  v1 = v2)
Termination
  wf_rel_tac`measure (v7_size o FST)`
End

val v_sim_ind = theorem"v_sim_ind";

Definition v_sim1_def[simp]:
  (v_sim1 (FP_WordTree fp1) (FP_WordTree fp2) ⇔ compress_word fp1 = compress_word fp2)∧
  (v_sim1 (FP_BoolTree fp1) (FP_BoolTree fp2) ⇔ compress_bool fp1 = compress_bool fp2)∧
  (v_sim1 (Conv ts1 vs1) (Conv ts2 vs2) ⇔ (ts1 = ts2) ∧ v_sim vs1 vs2 )∧
  (v_sim1 (Vectorv vs1) (Vectorv vs2) ⇔ v_sim vs1 vs2 ) ∧
  (v_sim1 v1 v2 ⇔ (v1 = v2))
End

Theorem v_sim_LIST_REL:
  ∀v1 v2. v_sim v1 v2 ⇔ LIST_REL v_sim1 v1 v2
Proof
  recInduct v_sim_ind \\ rw[] \\ Cases_on`v4` \\ rw[]
QED

Theorem v_sim_empty:
  ∀ xs ys. v_sim xs ys ∧ ys = [] ⇒ xs = []
Proof
  recInduct v_sim_ind \\ rw[]
QED

Definition noopt_sim_def:
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

Theorem v_sim_refl[simp]:
  v_sim vs vs
Proof
  `∀vs1 vs2. vs1 = vs2 ⇒ v_sim vs1 vs2` suffices_by rw[]
  \\ recInduct v_sim_ind \\ rw[]
QED

Theorem noopt_sim_refl[simp]:
  noopt_sim r r
Proof
  Cases_on ‘r’ \\ simp[noopt_sim_def]
QED

Theorem v_sim_fpoptimise:
  v_sim vs1 vs2 ⇒
  v_sim (do_fpoptimise annot1 vs1) (do_fpoptimise annot2 vs2)
Proof
  map_every qid_spec_tac[`vs2`, `vs1`]
  \\ recInduct v_sim_ind
  \\ rw[do_fpoptimise_def, fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  \\ fs[v_sim_LIST_REL]
  \\ simp[LIST_REL_APPEND_suff]
QED

(** Proofs about no_optimisations **)
local
  (* exp goal *)
  val P0 =
  “λ (e:ast$exp).
   ∀ st env cfg st2 r choices fpScope.
     evaluate st env [no_optimisations cfg e] = (st2, r) ⇒
     ∃ choices2 r2.
       evaluate
         (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices |>)
        env [e] =
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
    evaluate_match st env v (MAP (λ (p,e). (p, no_optimisations cfg e)) pes) err_v = (st2, r) ⇒
    ∃ choices2 r2.
      evaluate_match
        (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices|>)
      env v (MAP (λ (p,e). (p, no_optimisations cfg e)) pes) err_v =
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
     evaluate st env (MAP (no_optimisations cfg) es) = (st2, r) ⇒
     ∃ choices2 r2.
       evaluate
         (st with fp_state :=
          st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices |>)
        env es =
        (st2 with fp_state := st.fp_state with <| opts := (λ x. []); rws := []; canOpt:= FPScope fpScope; choices := choices2|>, r2) ∧ noopt_sim r r2
Proof
  Induct \\ fs[]
  >- rw[semanticPrimitivesTheory.state_component_equality,fpState_component_equality]
  \\ srw_tac[DNF_ss][]
  \\ pop_assum mp_tac
  \\ rw[Once evaluate_cons]
  \\ rw[Once evaluate_cons]
  \\ first_x_assum(fn th => mp_tac th \\ impl_tac >- metis_tac[])
  \\ strip_tac \\ fs[]
  \\ fs[CaseEq"prod"]
  \\ last_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices`, `fpScope`]strip_assume_tac))
  \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
  >- rw[semanticPrimitivesTheory.state_component_equality,fpState_component_equality]
  \\ fs[CaseEq"prod"]
  \\ first_x_assum (first_x_assum o mp_then Any (qspecl_then[`choices2`, `fpScope`]strip_assume_tac))
  \\ qmatch_asmsub_abbrev_tac`evaluate s1 env es`
  \\ qmatch_goalsub_abbrev_tac`evaluate s11 env es`
  \\ `s1 = s11` by (
    rw[Abbr`s1`, Abbr`s11`, semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
    \\ cheat (* seems to require another assumption? *) )
  \\ fs[Abbr`s1`, Abbr`s11`]
  \\ Cases_on`r2` \\ fs[noopt_sim_def]
  \\ reverse(fs[CaseEq"result"] \\ rveq \\ fs[noopt_sim_def])
  >- (rw[semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
      \\ cheat (* seems to require more assumptions? *) )
  \\ Cases_on`r2'` \\ fs[noopt_sim_def]
  \\ rw[semanticPrimitivesTheory.state_component_equality, fpState_component_equality]
  >- cheat (* more assumptions required *)
  >- cheat (* more assumptions required *)
  \\ fs[v_sim_LIST_REL]
  \\ irule LIST_REL_APPEND_suff
  \\ fs[]
QED

Theorem no_optimisations_backwards_sim:
  (∀ e. ^P0 e) ∧ (∀ l. ^P1 l) ∧ (∀ p. ^P2 p) ∧ (∀ l. ^P3 l) ∧ (∀ p. ^P4 p)
  ∧ (∀ p. ^P5 p) ∧ (∀ l. ^P6 l)
Proof
  irule ind_thm \\ rpt strip_tac \\ fs[]
  \\ rpt gen_tac \\ simp[no_optimisations_def, Once evaluate_def]
  >- (
   ntac 2 (reverse TOP_CASE_TAC  \\ fs[])
   \\ res_tac \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[]
   >- (
    strip_tac \\ rveq \\ fs[]
    \\ fs[evaluate_def, fpState_component_equality, semState_comp_eq, noopt_sim_def])
   \\ imp_res_tac noopt_sim_val \\ rveq \\ fs[noopt_sim_def, do_if_def]
   \\ imp_res_tac evaluate_sing \\ rveq \\ fs[v_sim_LIST_REL, v_sim1_def] \\ rveq
   \\ rename1 ‘v1 = Boolv T’
   \\ Cases_on ‘v1 = Boolv T’ \\ rveq \\ fs[Boolv_def] \\ rveq
   >- (
    rpt strip_tac
    \\ Cases_on ‘v’ \\ fs[v_sim1_def] \\ rveq
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
        \\ imp_res_tac v_sim_empty \\ fs[] \\ rveq)
    \\ Cases_on ‘v = Boolv F’ \\ fs[v_sim1_def]
    >- (‘v1 = Boolv F’ suffices_by (rveq \\ fs[Boolv_def])
        \\ Cases_on ‘v1’ \\ fs[v_sim1_def, Boolv_def]
        \\ imp_res_tac v_sim_empty \\ fs[] \\ rveq)
    \\ fs[fpState_component_equality, semState_comp_eq])
    \\ rpt strip_tac
    \\ Cases_on ‘v’ \\ fs[v_sim1_def] \\ rveq
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
  >- (cheat) (* Same as case above *)
  >- (cheat) (* Same as case above *)
  >- (cheat) (* needs lifting lemma lift_P6_noopt_REVERSE *)
  >- (cheat) (* Same as case above *)
  >- (cheat) (* Same as case above *)
  >- (
   rpt gen_tac
   \\ simp[no_optimisations_def, Once evaluate_def] \\ strip_tac
   \\ res_tac \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac) \\ fs[]
   \\ simp[evaluate_def, fpState_component_equality, semState_comp_eq])
  >- (
   rpt gen_tac
   \\ simp[no_optimisations_def, Once evaluate_def]
   \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ fs[] \\ rveq
   \\ Cases_on ‘st.fp_state.canOpt = Strict’ \\ fs[]
   \\ res_tac \\ simp[evaluate_def]
   \\ TRY (first_x_assum (qspecl_then [‘f’, ‘choices’] assume_tac)
       \\ fs[semState_comp_eq, fpState_component_equality, noopt_sim_def]
       \\ NO_TAC)
   \\ first_x_assum (qspecl_then [‘f’, ‘choices’] assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality, noopt_sim_def]
   \\ imp_res_tac noopt_sim_val \\ rveq
   \\ fs[noopt_sim_def, semState_comp_eq, fpState_component_equality, v_sim_fpoptimise])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[semState_comp_eq, fpState_component_equality])
  >- (simp[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (
   strip_tac \\ res_tac
   \\ first_x_assum (qspecl_then [‘fpScope’, ‘choices’] assume_tac)
   \\ fs[evaluate_def, semState_comp_eq, fpState_component_equality])
  >- (cheat)
  >- (
   TOP_CASE_TAC \\ fs[] \\ rpt strip_tac
   \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality])
  >- (cheat)
  >- (cheat)
  >- (cheat)
  >- (rpt strip_tac \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality])
  >- (cheat)
  >- (cheat)
  >- (rpt strip_tac \\ fs[evaluate_def,semState_comp_eq, fpState_component_equality])
QED
end;

Theorem no_optimisations_eval_sim =
  CONJUNCT1 (SIMP_RULE std_ss [] no_optimisations_backwards_sim)
  |> SPEC_ALL
  |> GEN “es:ast$exp list”
  |> SPEC “[e:ast$exp]”
  |> SIMP_RULE std_ss [MAP]
  |> GEN_ALL ;

(**
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
    (∀ opt. MEM opt st1.fp_state.rws ⇒ MEM opt st.fp_state.rws) ⇒
    evaluate st env (stos_pass cfg [e]) = (st2, r1) ∧
    (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
    (~ st1.fp_state.real_sem) ==>
    ∃ fpOpt fpOptR r2.
    (evaluate (st with fp_state := st.fp_state with
               <| rws := st.fp_state.rws ++ (cfg.optimisations) ; opts := fpOpt |>) env [e] =
     (st2 with fp_state := st2.fp_state with
      <| rws := st2.fp_state.rws ++ (cfg.optimisations) ; opts := fpOptR |>, r2)) ∧
    res_sim r1 r2 cfg st1) ⇒
   v_list_sim (v1::vs1) (v2::vs2) cfg st1)
End

Definition is_stos_pass_correct_def :
  is_stos_pass_correct rws (st1:'a semanticPrimitives$state) st2 env cfg exps r1 =
    (evaluate st1 env
             (stos_pass (cfg with optimisations := rws) exps) = (st2, r1) ∧
     (cfg.canOpt ⇔ st1.fp_state.canOpt = FPScope Opt) ∧
     (~ st1.fp_state.real_sem) ==>
    ∃ fpOpt fpOptR r2.
      (evaluate (st1 with fp_state := st1.fp_state with
                <| rws := st1.fp_state.rws ++ rws; opts := fpOpt |>) env exps =
      (st2 with fp_state := st2.fp_state with
       <| rws := st2.fp_state.rws ++ rws; opts := fpOptR |>, r2)) ∧
      res_sim r1 r2 (cfg with optimisations := rws) st1)
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
  (~ st1.fp_state.real_sem) ⇒
  res_sim vs1 vs2 cfg st2)
  ∧
  (∀ vs1 vs2 cfg (st1:'a semanticPrimitives$state).
  v_list_sim vs1 vs2 cfg st1 ⇒
  ∀ (st2:'a semanticPrimitives$state).
  st1.fp_state.rws = st2.fp_state.rws ∧
  (st1.fp_state.canOpt = FPScope Opt ⇔ st2.fp_state.canOpt = FPScope Opt) ∧
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
  \\ qexists_tac ‘fpOpt'’ \\ fs[Once res_sim_rules, semState_comp_eq, fpState_component_equality]
QED

local
  val optimise_case = fn t =>
   fs[is_optimise_correct_def]
   \\ first_x_assum (qspec_then t mp_tac) \\ fs[]
   \\ rpt (disch_then drule)
   \\ strip_tac
   \\ reverse (Cases_on ‘r'’) \\ fs[]
   >- (
    rpt strip_tac \\ rveq \\ qexists_tac ‘fpOpt’
    \\ fs[semState_comp_eq, fpState_component_equality, res_sim_rules])
   \\ TOP_CASE_TAC \\ fs[]
   \\ first_x_assum (qspec_then ‘t’ mp_tac)
   \\ impl_tac \\ fs[astTheory.exp_size_def]
   \\ rpt (disch_then drule)
   \\ impl_tac
   >- (rpt conj_tac \\ imp_res_tac evaluate_fp_opts_inv \\ fs[])
   \\ strip_tac
   \\ optUntil_tac ‘evaluate _ _ ^(Parse.Term t) = _’ ‘fpOpt'’
   \\ strip_tac
   \\ qexists_tac ‘optUntil (q.fp_state.choices - st1.fp_state.choices) fpOpt fpOpt'’
   \\ fs[]
   \\ pop_assum mp_tac \\ TOP_CASE_TAC \\ strip_tac \\ rveq
   \\ TOP_CASE_TAC \\ rveq
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
   qpat_x_assum `evaluate _ _ [Fun _ _] = _` mp_tac
   \\ simp[evaluate_def] \\ rpt strip_tac \\ rveq \\ fs[]
   \\ pop_assum mp_tac \\ ntac 2 (reverse TOP_CASE_TAC \\ fs[])
   \\ rpt strip_tac \\ rveq \\ fs[]
   \\ last_assum (qspec_then ‘t’ mp_tac)
   \\ impl_tac \\ TRY (fs[astTheory.exp_size_def] \\ NO_TAC)
   \\ rpt (disch_then drule)
   \\ strip_tac
   >- (Cases_on ‘r2’ \\ fs[Once res_sim_rules, Once res_sim_cases]
       \\ qexists_tac ‘fpOpt’
       \\ fs[semState_comp_eq, fpState_component_equality, Once res_sim_rules])
   \\ Cases_on ‘r2’ \\ TRY (fs[Once res_sim_rules, Once res_sim_cases] \\ NO_TAC)
   \\ qexists_tac ‘fpOpt’
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
   >- (cheat)
   \\ strip_tac \\ qexists_tac ‘fpOpt'’ \\ fs[semState_comp_eq, fpState_component_equality]
   \\ irule (hd (CONJ_LIST 2 res_sim_swap))
   \\ qexists_tac ‘st’ \\ fs[]
   \\ cheat)
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
**)

val _ = export_theory ();
