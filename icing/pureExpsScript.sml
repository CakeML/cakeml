(*
  Implements a predicate to check whether an expression is pure, i.e. does not
  use memory or the FFI
*)
open bossLib semanticPrimitivesTheory fpValTreeTheory fpOptTheory
     fpOptPropsTheory fpSemPropsTheory;
open icingTacticsLib preamble;

val _ = new_theory "pureExps";

val semState_comp_eq = semanticPrimitivesTheory.state_component_equality;

Definition isPureOp_def:
  isPureOp op =
    case op of
    | AallocEmpty => F
    | AallocFixed => F
    | Aalloc => F
    | Aupdate => F
    | Aupdate_unsafe => F
    | Asub_unsafe => F
    | Aw8alloc => F
    | Aw8sub_unsafe => F
    | Aw8update => F
    | Aw8update_unsafe => F
    | Aw8length => F
    | Aw8sub => F
    | Alength => F
    | Asub => F
    | CopyAw8Aw8 => F
    | CopyStrAw8 => F
    | CopyAw8Str => F
    | XorAw8Str_unsafe => F
    | Eval => F
    | FFI _ => F
    | ThunkOp _ => F
    | Opassign => F
    | Opapp => F
    | Opderef => F
    | Opref => F
    | _ => T
End

Definition isPurePat_def:
  (isPurePat (Pvar _) = T) /\
  (isPurePat (Plit _) = T) /\
  (isPurePat (Pcon _ pl) = isPurePatList pl) /\
  (isPurePat (Ptannot p _) = isPurePat p) /\
  (isPurePat _ = F)
  /\
  (isPurePatList [] = T) /\
  (isPurePatList (p::pl) = (isPurePat p /\ isPurePatList pl))
End

Definition isPureExp_def:
  (isPureExp (Raise e) = F) /\
  (isPureExp (Handle e l) = F) /\
  (isPureExp (Lit _) = T) /\
  (isPureExp (Con _ exl) = isPureExpList exl) /\
  (isPureExp (Var _) = T) /\
  (isPureExp (Fun _ _) = F) /\
  (isPureExp (App op exl) = (isPureOp op /\ isPureExpList exl)) /\
  (isPureExp (Log _ e1 e2) = (isPureExp e1 /\ isPureExp e2)) /\
  (isPureExp (If e1 e2 e3) = (isPureExp e1 /\ isPureExp e2 /\ isPureExp e3)) /\
  (isPureExp (Mat e pel) = (isPureExp e /\ isPurePatExpList pel)) /\
  (isPureExp (Let _ e1 e2) = (isPureExp e1 /\ isPureExp e2)) /\
  (isPureExp (Letrec _ _) = F) /\
  (isPureExp (Tannot e a) = isPureExp e) /\
  (isPureExp (Lannot e l) = isPureExp e) /\
  (isPureExp (FpOptimise _ e) = isPureExp e)
  /\
    isPureExpList [] = T /\
    isPureExpList (e::exl) = (isPureExp e /\ isPureExpList exl)
  /\
    isPurePatExpList [] = T /\
    isPurePatExpList ((p,e)::pel) = (isPurePat p /\ isPureExp e /\ isPurePatExpList pel)
End

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
    ! refs (ffi:'b ffi_state).
      do_app (refs, ffi) op vl = SOME ((refs, ffi), r)
Proof
  Cases_on `op` \\ rpt gen_tac \\ strip_tac
  \\ fs[isPureOp_simp, do_app_def, CaseEq"list", CaseEq"lit", CaseEq"option", CaseEq"v",
        PULL_EXISTS, CaseEq"bool", CaseEq"word_size", CaseEq"eq_result", CaseEq"prod", store_alloc_def]
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
  val indThm = evaluate_ind
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
    \\ TRY (Cases_on ‘op’ \\ gs[astTheory.getOpClass_def, isPureOp_def] \\ NO_TAC)
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

val _ = export_theory();
