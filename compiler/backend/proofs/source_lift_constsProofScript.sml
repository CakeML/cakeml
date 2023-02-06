(*
  Correctness for the source_lift_consts passes.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_lift_constsTheory source_evalProofTheory;

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
  (LIST_REL v_rel xs ys ==>
    v_rel (Vectorv xs) (Vectorv ys)) ∧
  (LIST_REL v_rel xs ys ==>
    v_rel (Conv stmp xs) (Conv stmp ys)) ∧
  (env_rel v_rel env env' ==>
    v_rel (Closure env nm x) (Closure env' nm x)) ∧
  (env_rel v_rel env env' ==>
    v_rel (Recclosure env funs nm) (Recclosure env' funs nm)) ∧
  (v_rel (Litv l) (Litv l)) ∧
  (v_rel (Loc n) (Loc n)) ∧
  (v_rel (FP_BoolTree b) (FP_BoolTree b)) ∧
  (v_rel (FP_WordTree w) (FP_WordTree w)) ∧
  (v_rel (Real r) (Real r)) ∧
  (env_rel v_rel env1 env2 ⇒
    v_rel (Env env1 id) (Env env2 id))
End

Definition id_rel_def:
  id_rel x f y ⇔ y = x ∨ y = f x
End

Definition state_rel_def:
  state_rel ^s ^s' <=>
    LIST_REL (sv_rel v_rel) s.refs s'.refs ∧
    s'.next_type_stamp = s.next_type_stamp ∧
    s'.next_exn_stamp = s.next_exn_stamp
    (* TODO: add more here *)
End

(*-----------------------------------------------------------------------*
   statement of evaluate theorem
 *-----------------------------------------------------------------------*)

val eval_simulation_setup = setup (`
  (∀ ^s env exps s' res es t env'.
     evaluate s env exps = (s', res) ∧
     state_rel s t ∧
     env_rel v_rel env env' ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate t env' exps = (t', res') ∧
       state_rel s' t' ∧
       result_rel (LIST_REL v_rel) v_rel res res')
  ∧
  (∀ ^s env x pes err_x s' res es t env' y err_y.
     evaluate_match s env x pes err_x = (s', res) ∧
     state_rel s t ∧
     env_rel v_rel env env' ∧
     v_rel x y ∧
     v_rel err_x err_y ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate_match t env' y pes err_y = (t', res') ∧
       state_rel s' t' ∧
       result_rel (LIST_REL v_rel) v_rel res res')
  ∧
  (∀ ^s env decs decs' s' res t env'.
     evaluate_decs s env decs = (s', res) ∧
     state_rel s t ∧
     env_rel v_rel env env' ∧
     id_rel decs compile_decs decs' ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate_decs t env' decs' = (t', res') ∧
       state_rel s' t' ∧
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

Triviality eval_simulation_Dlet:
  ^(#get_goal eval_simulation_setup `Case (Dlet, [_])`)
Proof
  cheat
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

Triviality eval_simulation_Denv:
  ^(#get_goal eval_simulation_setup `Case (Dlet, [Denv _])`)
Proof
  cheat
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
    evaluate_decs s env decs = (s',res) ∧ state_rel s t ∧
    env_rel v_rel env env' ∧ res ≠ Rerr (Rabort Rtype_error) ⇒
    ∃t' res'.
      evaluate_decs t env' (compile_decs decs) = (t',res') ∧ state_rel s' t' ∧
      result_rel (env_rel v_rel) v_rel res res'
Proof
  rw [] \\ irule $ last (CONJUNCTS eval_simulation) \\ fs []
  \\ last_x_assum $ irule_at Any \\ fs [id_rel_def]
QED

(*-----------------------------------------------------------------------*
   top-level semantics proofs
 *-----------------------------------------------------------------------*)

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile_decs prog) outcome
Proof
  cheat
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
  cheat
QED

val _ = export_theory ();
