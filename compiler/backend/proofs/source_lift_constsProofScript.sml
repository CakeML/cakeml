(*
  Correctness for the source_lift_consts passes.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_lift_constsTheory source_evalProofTheory
     semanticsPropsTheory;

val _ = new_theory "source_lift_constsProof";

val _ = set_grammar_ancestry
  [ "source_lift_consts", "evaluate", "evaluateProps", "semanticPrimitives",
    "semanticPrimitivesProps", "misc", "semantics" ];

val s  = mk_var ("s",  “: 'ffi semanticPrimitives$state”);
val s' = mk_var ("s'", “: 'ffi semanticPrimitives$state”);

(*-----------------------------------------------------------------------*
   setup code copied from source_evalProof
 *-----------------------------------------------------------------------*)

val case_const = “marker$Case”
fun is_app_case t = is_comb t andalso same_const case_const (rator t)

fun setup (q : term quotation, t : tactic) = let
    val the_concl = Parse.typedTerm q bool
    val t2 = (t \\ rpt (pop_assum mp_tac))
    val (goals, validation) = t2 ([], the_concl)
    fun get_goal q = first (can (rename [q])) goals |> snd
    fun init thms st = if null (fst st) andalso aconv (snd st) the_concl
      then ((K (goals, validation)) \\ TRY (MAP_FIRST ACCEPT_TAC thms)) st
      else failwith "setup tactic: mismatching starting state"
    val cases = map (find_terms is_app_case o snd) goals
  in {get_goal = get_goal, concl = fn () => the_concl,
    cases = cases, init = (init : thm list -> tactic),
    all_goals = fn () => map snd goals} end

(*-----------------------------------------------------------------------*
   v_rel, env_rel, state_rel
 *-----------------------------------------------------------------------*)

Overload env_rel[local] = “source_evalProof$env_rel”
val env_rel_def = source_evalProofTheory.env_rel_def;
val _ = IndDefLib.add_mono_thm source_evalProofTheory.env_rel_mono_rel;

Inductive v_rel:
  (∀v. v_rel v v) ∧
  (LIST_REL v_rel xs ys ==>
    v_rel (Vectorv xs) (Vectorv ys)) ∧
  (LIST_REL v_rel xs ys ==>
    v_rel (Conv stmp xs) (Conv stmp ys)) ∧
  (env_rel v_rel env env' ==>
    v_rel (Closure env nm x) (Closure env' nm x)) ∧
  (env_rel v_rel env env' ==>
    v_rel (Recclosure env funs nm) (Recclosure env' funs nm)) ∧
  (env_rel v_rel env1 env2 ⇒
    v_rel (Env env1 id) (Env env2 id))
End

Theorem v_rel_refl:
  v_rel x x
Proof
  simp [Once v_rel_cases]
QED

Definition id_rel_def:
  id_rel x f y ⇔ y = x ∨ y = f x
End

Inductive eval_state_rel:
  (∀s. eval_state_rel (:'a) (EvalDecs s) (EvalDecs s)) ∧
  (∀e1 e2.
    e1.generation = e2.generation ∧
    e1.oracle = e2.oracle ∧
    LIST_REL (LIST_REL $ env_rel v_rel) e1.envs e2.envs ∧
    (e1.custom_do_eval = e2.custom_do_eval ∨
     ∃(ci:'a source_evalProof$compiler_instance) (f : dec list -> dec list).
       e1.custom_do_eval = source_evalProof$do_eval_oracle
                             (source_evalProof$mk_compiler_fun_from_ci ci) f ∧
       s2.custom_do_eval = source_evalProof$do_eval_oracle
           (source_evalProof$mk_compiler_fun_from_ci ci) (compile_decs ∘ f)) ⇒
    eval_state_rel (:'a) (EvalOracle e1) (EvalOracle e2))
End

Definition state_rel_def:
  state_rel (:'a) ^s ^s' <=>
    LIST_REL (sv_rel v_rel) s.refs s'.refs ∧
    s'.next_type_stamp = s.next_type_stamp ∧
    s'.next_exn_stamp = s.next_exn_stamp ∧
    s'.ffi = s.ffi ∧
    s'.clock = s.clock ∧
    OPTREL (eval_state_rel (:'a)) s.eval_state s'.eval_state
End

(*-----------------------------------------------------------------------*
   statement of evaluate theorem
 *-----------------------------------------------------------------------*)

val eval_simulation_setup = setup (`
  (∀ ^s env exps s' res es t env'.
     evaluate s env exps = (s', res) ∧
     state_rel (:'a) s t ∧
     env_rel v_rel env env' ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate t env' exps = (t', res') ∧
       state_rel (:'a) s' t' ∧
       result_rel (LIST_REL v_rel) v_rel res res')
  ∧
  (∀ ^s env x pes err_x s' res es t env' y err_y.
     evaluate_match s env x pes err_x = (s', res) ∧
     state_rel (:'a) s t ∧
     env_rel v_rel env env' ∧
     v_rel x y ∧
     v_rel err_x err_y ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate_match t env' y pes err_y = (t', res') ∧
       state_rel (:'a) s' t' ∧
       result_rel (LIST_REL v_rel) v_rel res res')
  ∧
  (∀ ^s env decs decs' s' res t env'.
     evaluate_decs s env decs = (s', res) ∧
     state_rel (:'a) s t ∧
     env_rel v_rel env env' ∧
     id_rel decs compile_decs decs' ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate_decs t env' decs' = (t', res') ∧
       state_rel (:'a) s' t' ∧
       result_rel (env_rel v_rel) v_rel res res')
  `,
  ho_match_mp_tac (name_ind_cases [``()``, ``()``, ``Dlet``] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def]
  \\ fs [Q.prove (`Case ((), x) = Case (x)`, simp [markerTheory.Case_def])]
  \\ rveq \\ fs []
  );

(*-----------------------------------------------------------------------*
   proofs of individual cases
 *-----------------------------------------------------------------------*)

Triviality eval_simulation_App:
  ^(#get_goal eval_simulation_setup `Case ([App _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Con:
  ^(#get_goal eval_simulation_setup `Case ([Con _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Let:
  ^(#get_goal eval_simulation_setup `Case ([Let _ _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Var:
  ^(#get_goal eval_simulation_setup `Case ([Var _])`)
Proof
  cheat
QED

Triviality eval_simulation_Lit:
  ^(#get_goal eval_simulation_setup `Case ([Lit _])`)
Proof
  cheat
QED

Triviality eval_simulation_Fun:
  ^(#get_goal eval_simulation_setup `Case ([Fun _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Letrec:
  ^(#get_goal eval_simulation_setup `Case ([Letrec _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_match:
  ^(#get_goal eval_simulation_setup `Case ((_, _) :: _)`)
Proof
  cheat
QED

Triviality eval_simulation_Scope:
  ^(#get_goal eval_simulation_setup `Case ([FpOptimise _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_If:
  ^(#get_goal eval_simulation_setup `Case ([If _ _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Mat:
  ^(#get_goal eval_simulation_setup `Case ([Mat _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Handle:
  ^(#get_goal eval_simulation_setup `Case ([Handle _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Raise:
  ^(#get_goal eval_simulation_setup `Case ([Raise _])`)
Proof
  cheat
QED

Triviality eval_simulation_Log:
  ^(#get_goal eval_simulation_setup `Case ([Log _ _ _])`)
Proof
  cheat
QED

Theorem pmatch_thm:
  pmatch env_c s.refs p v1 vs1 = m ∧
  v_rel v1 v2 ∧ LIST_REL ((=) ### v_rel) vs1 vs2 ∧ state_rel (:'a) s t ⇒
  case m of
  | No_match => pmatch env_c t.refs p v2 vs2 = No_match
  | Match new1 =>
      (∃new2. pmatch env_c t.refs p v2 vs2 = Match new2 ∧
              LIST_REL ((=) ### v_rel) new1 new2)
  | _ => T
Proof
  cheat
QED

Triviality alist_to_ns_eq:
  alist_to_ns xs = nsBindList xs nsEmpty
Proof
  Induct_on ‘xs’ \\ fs [namespaceTheory.nsBindList_def,FORALL_PROD]
QED

Triviality eval_simulation_Dlet:
  ^(#get_goal eval_simulation_setup `Case (Dlet, [_])`)
Proof
  rpt strip_tac
  \\ gvs [CaseEq"bool"]
  \\ gvs [id_rel_def,CaseEq"prod"]
  >-
   (Cases_on ‘v2 = Rerr (Rabort Rtype_error)’ >- gvs []
    \\ last_x_assum drule_all
    \\ ‘env'.c = env.c’ by fs [env_rel_def]
    \\ strip_tac \\ fs [evaluate_decs_def]
    \\ gvs [AllCaseEqs(),PULL_EXISTS,v_rel_refl]
    \\ imp_res_tac evaluate_sing \\ gvs []
    \\ drule pmatch_thm
    \\ disch_then drule \\ fs []
    \\ disch_then drule \\ fs []
    \\ rpt strip_tac \\ fs [alist_to_ns_eq]
    \\ drule_at Any source_evalProofTheory.env_rel_add_nsBindList
    \\ disch_then $ qspecl_then [‘nsEmpty’,‘nsEmpty’,
         ‘<| v := nsEmpty ; c := nsEmpty |>’,
         ‘<| v := nsEmpty ; c := nsEmpty |>’] mp_tac
    \\ fs [env_rel_def,SF SFY_ss])
  \\ cheat
QED

Triviality eval_simulation_Dletrec:
  ^(#get_goal eval_simulation_setup `Case (_, [Dletrec _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Dtype:
  ^(#get_goal eval_simulation_setup `Case (_, [Dtype _ _])`)
Proof
  fs [evaluate_decs_def] \\ rw []
  \\ ‘decs' = [Dtype locs tds]’ by fs [id_rel_def,compile_dec_def]
  \\ gvs [evaluate_decs_def,state_rel_def,env_rel_def]
QED

Triviality eval_simulation_Dexn:
  ^(#get_goal eval_simulation_setup `Case (_, [Dexn _ _ _])`)
Proof
  fs [evaluate_decs_def] \\ rw []
  \\ ‘decs' = [Dexn locs cn ts]’ by fs [id_rel_def,compile_dec_def]
  \\ gvs [evaluate_decs_def,state_rel_def,env_rel_def]
QED

Triviality eval_simulation_Dlocal:
  ^(#get_goal eval_simulation_setup `Case (_, [Dlocal _ _])`)
Proof
  rpt strip_tac
  \\ rename [‘id_rel [Dlocal decs1 decs2] compile_decs decs3’]
  \\ ‘∃decs1' decs2'.
       decs3 = [Dlocal decs1' decs2'] ∧
       id_rel decs1 compile_decs decs1' ∧
       id_rel decs2 compile_decs decs2'’ by gvs [id_rel_def,compile_dec_def]
  \\ gvs [CaseEq"prod"]
  \\ Cases_on ‘v1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule_all \\ strip_tac \\ fs []
  \\ fs [evaluate_decs_def]
  \\ gvs [AllCaseEqs()]
  \\ last_x_assum irule \\ fs []
  \\ irule source_evalProofTheory.env_rel_extend_dec_env \\ fs []
QED

Triviality eval_simulation_Dmod:
  ^(#get_goal eval_simulation_setup `Case (_, [Dmod _ _])`)
Proof
  rpt strip_tac
  \\ rename [‘id_rel [Dmod mn decs] compile_decs decs1’]
  \\ ‘∃decs'.
       decs1 = [Dmod mn decs'] ∧
       id_rel decs compile_decs decs'’ by gvs [id_rel_def,compile_dec_def]
  \\ gvs [CaseEq"prod"]
  \\ gvs [AllCaseEqs()]
  \\ first_x_assum drule_all \\ strip_tac \\ fs []
  \\ fs [evaluate_decs_def]
  \\ TOP_CASE_TAC \\ gvs []
  \\ irule source_evalProofTheory.env_rel_nsLift
  \\ fs [env_rel_def]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality eval_simulation_cons_decs:
  ^(#get_goal eval_simulation_setup `Case (Dlet, _ :: _ :: _)`)
Proof
  rw []
  \\ ‘∃d1' d2' ds'.
       decs' = d1'::d2'::ds' ∧
       id_rel [d1] compile_decs [d1'] ∧
       id_rel (d2::ds) compile_decs (d2'::ds')’ by gvs [id_rel_def,compile_dec_def]
  \\ gvs [CaseEq "prod"]
  \\ Cases_on ‘v1 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule_all \\ strip_tac \\ fs []
  \\ fs [evaluate_decs_def]
  \\ gvs [AllCaseEqs(),PULL_EXISTS]
  \\ last_x_assum drule
  \\ disch_then $ drule_at $ Pos $ el 2
  \\ rename [‘env_rel v_rel env1 env1a’]
  \\ disch_then $ qspecl_then [‘env1a +++ env'’] mp_tac
  \\ impl_tac
  >-
   (irule_at Any source_evalProofTheory.env_rel_extend_dec_env \\ fs []
    \\ CCONTR_TAC \\ fs [combine_dec_result_def])
  \\ strip_tac \\ fs []
  \\ Cases_on ‘r’ \\ gvs [combine_dec_result_def]
  \\ irule source_evalProofTheory.env_rel_nsAppend
  \\ gvs [env_rel_def,SF SFY_ss]
QED

Theorem LLOOKUP_LIST_REL:
  ∀n xs ys x.
    LLOOKUP xs n = SOME x ∧ LIST_REL R xs ys ⇒
    ∃y. LLOOKUP ys n = SOME y ∧ R x y
Proof
  Induct \\ Cases_on ‘xs’ \\ fs [oEL_def,PULL_EXISTS]
  \\ rw [] \\ res_tac \\ fs []
QED

Triviality eval_simulation_Denv:
  ^(#get_goal eval_simulation_setup `Case (Dlet, [Denv _])`)
Proof
  rw [] \\ gvs [AllCaseEqs()]
  \\ ‘decs' = [Denv n]’ by fs [id_rel_def,compile_dec_def]
  \\ gvs [full_evaluate_def]
  \\ Cases_on ‘s.eval_state’ \\ gvs [declare_env_def]
  \\ rename [‘SOME x1’]
  \\ ‘∃x2. eval_state_rel (:'a) x1 x2 ∧ t.eval_state = SOME x2’ by
       (fs [state_rel_def] \\ Cases_on ‘t.eval_state’ \\ fs [])
  \\ gvs []
  \\ qpat_x_assum ‘eval_state_rel (:'a) x1 x2’ mp_tac
  \\ simp [eval_state_rel_cases]
  \\ strip_tac \\ gvs [PULL_EXISTS]
  \\ gvs [AllCaseEqs()]
  >~ [‘EvalDecs’]
  >- (gvs [state_rel_def]
      \\ simp [eval_state_rel_cases]
      \\ fs [env_rel_def]
      \\ simp [Once v_rel_cases]
      \\ fs [env_rel_def, SF SFY_ss])
  \\ gvs [PULL_EXISTS,state_rel_def,env_rel_def]
  \\ simp [Once v_rel_cases]
  \\ drule_all LLOOKUP_LIST_REL
  \\ strip_tac
  \\ first_x_assum $ irule_at Any
  \\ fs [eval_state_rel_cases]
  \\ irule_at Any EVERY2_LUPDATE_same \\ fs []
  \\ fs [env_rel_def,SF SFY_ss]
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ fs [nat_to_v_def]
  \\ simp [Once v_rel_cases]
  \\ simp [Once v_rel_cases]
  \\ qexists_tac ‘s2’ \\ fs []
  \\ metis_tac []
QED

(*-----------------------------------------------------------------------*
   evaluation proof: putting all cases together
 *-----------------------------------------------------------------------*)

Theorem eval_simulation:
  ^(#concl eval_simulation_setup ())
Proof
  #init eval_simulation_setup
   [eval_simulation_App, eval_simulation_Lit, eval_simulation_Fun,
    eval_simulation_Var, eval_simulation_Denv, eval_simulation_Con,
    eval_simulation_Let, eval_simulation_Mat, eval_simulation_Handle,
    eval_simulation_If, eval_simulation_Raise, eval_simulation_Log,
    eval_simulation_Letrec, eval_simulation_Letrec, eval_simulation_match,
    eval_simulation_cons_decs, eval_simulation_Dletrec, eval_simulation_Dmod,
    eval_simulation_Dtype, eval_simulation_Dexn, eval_simulation_Dlet,
    eval_simulation_Dlocal, eval_simulation_Scope]
  \\ rpt disch_tac
  \\ gvs [AllCaseEqs()]
  \\ res_tac \\ gvs []
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ gvs [id_rel_def,compile_dec_def]
  \\ gvs [env_rel_def,full_evaluate_def]
QED

Theorem compile_decs_correct:
  ∀s env decs decs' s' res t env'.
    evaluate_decs s env decs = (s',res) ∧ state_rel (:'a) s t ∧
    env_rel v_rel env env' ∧ id_rel decs compile_decs decs' ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t' res'.
      evaluate_decs t env' decs' = (t',res') ∧ state_rel (:'a) s' t' ∧
      result_rel (env_rel v_rel) v_rel res res'
Proof
  rw [] \\ irule $ last (CONJUNCTS eval_simulation) \\ fs []
  \\ last_x_assum $ irule_at Any \\ fs []
QED

(*-----------------------------------------------------------------------*
   top-level semantics proofs
 *-----------------------------------------------------------------------*)

Theorem compile_semantics_state_rel:
  state_rel (:'a) s t ∧ id_rel prog compile_decs prog1 ⇒
  ¬semantics_prog s env prog Fail ⇒
  semantics_prog s env prog outcome ⇒
    semantics_prog t env prog1 outcome
Proof
  rw []
  \\ Cases_on ‘outcome = Fail’
  >- metis_tac [semantics_prog_deterministic]
  \\ ‘env_rel v_rel env env’ by (fs [env_rel_def] \\ rw [] \\ fs [v_rel_refl])
  \\ Cases_on ‘outcome’ \\ gvs []
  >~ [‘Terminate res ll’] >-
   (fs [semantics_prog_def,evaluate_prog_with_clock_def]
    \\ qexists_tac ‘k’ \\ fs []
    \\ rpt (pairarg_tac \\ gvs [])
    \\ ‘state_rel (:'a) (s with clock := k) (t with clock := k)’ by fs [state_rel_def]
    \\ drule_all compile_decs_correct \\ fs [] \\ strip_tac
    \\ Cases_on ‘r’ \\ gvs [state_rel_def]
    \\ every_case_tac \\ fs [])
  >~ [‘Diverge ll’]
  \\ fs [semantics_prog_def]
  \\ conj_tac
  >-
   (rw [] \\ first_x_assum $ qspec_then ‘k’ strip_assume_tac
    \\ fs [evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ ‘state_rel (:'a) (s with clock := k) (t with clock := k)’ by fs [state_rel_def]
    \\ drule compile_decs_correct
    \\ disch_then drule
    \\ disch_then drule
    \\ disch_then drule \\ fs [])
  \\ qpat_x_assum ‘lprefix_lub _ _’ mp_tac
  \\ match_mp_tac EQ_IMPLIES
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ rw [FUN_EQ_THM]
  \\ fs [evaluate_prog_with_clock_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ ‘state_rel (:'a) (s with clock := k) (t with clock := k)’ by fs [state_rel_def]
  \\ drule_at (Pos $ el 2) compile_decs_correct
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then drule
  \\ impl_tac
  >- (first_x_assum $ qspec_then ‘k’ mp_tac \\ fs [])
  \\ strip_tac \\ gvs []
  \\ fs [state_rel_def]
QED

Triviality sv_rel_refl:
  ∀xs. LIST_REL (sv_rel v_rel) xs xs
Proof
  Induct \\ fs []
  \\ Cases \\ fs [v_rel_refl]
  \\ Induct_on ‘l’ \\ fs [v_rel_refl]
QED

Triviality eval_state_rel_refl:
  eval_state_rel (:'a) x x
Proof
  Cases_on ‘x’ \\ fs [eval_state_rel_cases]
  \\ rename [‘LIST_REL _ xs _’]
  \\ Induct_on ‘xs’ \\ fs []
  \\ Induct \\ fs []
  \\ fs [env_rel_def]
  \\ rw [] \\ fs [v_rel_refl]
QED

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile_decs prog) outcome
Proof
  rewrite_tac [GSYM AND_IMP_INTRO]
  \\ match_mp_tac compile_semantics_state_rel
  \\ fs [state_rel_def,sv_rel_refl,id_rel_def]
  \\ Cases_on ‘s.eval_state’ \\ fs [eval_state_rel_refl]
QED

Theorem compile_semantics_oracle:
  ∀f.
    source_evalProof$is_insert_oracle ci f s.eval_state ∧
    ¬ semantics_prog s env prog Fail ∧
    semantics_prog s env prog outcome
    ⇒
    semantics_prog (s with eval_state updated_by
              source_evalProof$adjust_oracle ci (compile_decs ∘ f))
          env prog outcome
Proof
  rpt strip_tac
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ match_mp_tac compile_semantics_state_rel
  \\ fs [id_rel_def,state_rel_def,sv_rel_refl]
  \\ Cases_on ‘s.eval_state’
  \\ fs [source_evalProofTheory.adjust_oracle_def]
  \\ Cases_on ‘x’ \\ fs []
  \\ simp [Once eval_state_rel_cases]
  \\ fs [source_evalProofTheory.is_insert_oracle_def]
  \\ Cases_on ‘es'’ \\ fs []
  \\ fs [source_evalProofTheory.insert_gen_oracle_def]
  \\ gvs [AllCaseEqs()]
  \\ Q.REFINE_EXISTS_TAC ‘<| custom_do_eval := xx |>’
  \\ fs [GSYM PULL_EXISTS]
  \\ conj_tac
  >-
   (rename [‘LIST_REL _ xs’]
    \\ Induct_on ‘xs’ \\ fs []
    \\ Induct \\ fs []
    \\ fs [env_rel_def]
    \\ rw [] \\ fs [v_rel_refl])
  \\ irule_at Any (METIS_PROVE [] “b ⇒ a ∨ b”)
  \\ fs [] \\ metis_tac []
QED

val _ = export_theory ();
