(*
  Correctness for the source_lift_consts passes.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_lift_constsTheory source_evalProofTheory
     semanticsPropsTheory;

val _ = new_theory "source_lift_constsProof";

val _ = set_grammar_ancestry
  [ "source_lift_consts", "mlmap", "evaluate", "evaluateProps", "semanticPrimitives",
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

Theorem v_rel_Conv:
  v_rel (Conv x vs) v ⇔ ∃ws. v = Conv x ws ∧ LIST_REL v_rel vs ws
Proof
  simp [Once v_rel_cases] \\ Cases_on ‘v’ \\ fs []
  \\ eq_tac \\ rw [] \\ fs []
  \\ rename [‘LIST_REL _ l’] \\ Induct_on ‘l’ \\ fs [v_rel_refl]
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

Definition weak_env_rel_def:
  weak_env_rel fvs env1 env2 ⇔
    env1.c = env2.c ∧
    (∀m n v1.
       nsLookup env1.v (Long m n) = SOME v1 ⇒
       ∃v2. nsLookup env2.v (Long m n) = SOME v2 ∧ v_rel v1 v2) ∧
    (∀n (u:unit) v1.
      lookup fvs (implode n) = SOME u ∧ nsLookup env1.v (Short n) = SOME v1 ⇒
      ∃v2. nsLookup env2.v (Short n) = SOME v2 ∧ v_rel v1 v2)
End

Definition const_env_rel_def:
  const_env_rel binders (env1: v sem_env) env2 ⇔
    env1.c = env2.c ∧
    (∀m n v1.
       nsLookup env1.v (Long m n) = SOME v1 ⇒
       nsLookup env2.v (Long m n) = SOME v1) ∧
    (∀n v1.
      ~MEM n binders ∧
      nsLookup env1.v (Short n) = SOME v1 ⇒
      nsLookup env2.v (Short n) = SOME v1)
End

Definition can_lookup_def:
  can_lookup env_v (n,v) ⇔ nsLookup env_v (Short n) = SOME v
End

(*-----------------------------------------------------------------------*
   statement of evaluate theorem
 *-----------------------------------------------------------------------*)

val eval_simulation_setup = setup (‘
  (∀ ^s env exps.
     (* running the same code: *)
     (∀ s' res t env'.
         evaluate s env exps = (s', res) ∧
         state_rel (:'a) s t ∧
         env_rel v_rel env env' ∧
         res <> Rerr (Rabort Rtype_error) ==>
         ∃t' res' ws.
           evaluate t env' exps = (t', res') ∧
           state_rel (:'a) s' t' ∧
           result_rel (LIST_REL v_rel) v_rel res res') ∧
     (* running altered code: *)
     (∀ s' b n3 res t env' exps1 exps2 exps3 n2 n4 xs binders fvs ws0 env0 ws env3.
         evaluate s env exps = (s', res) ∧
         state_rel (:'a) s t ∧
         annotate_exps binders (REVERSE exps) = (exps1,n2,fvs) ∧ n2 ≤ n3 ∧
         lift_exps b [] n3 exps1 = (exps3,n4,xs) ∧
         EVERY (every_exp (one_con_check env.c)) exps ∧
         weak_env_rel fvs env env' ∧
         const_env_rel binders env' env0 ∧
         res <> Rerr (Rabort Rtype_error) ∧
         (∀(t0:'ffi semanticPrimitives$state).
           evaluate_decs t0 env0
             (MAP (λ(n,e). Dlet unknown_loc (Pvar (explode n)) e) (REVERSE xs)) =
             (t0,Rval (<|v := alist_to_ns ws; c := nsEmpty|>))) ∧
         EVERY (can_lookup env3.v) ws ∧ weak_env_rel fvs env env3 ⇒
         ∃t' res'.
           evaluate t env3 (REVERSE exps3) = (t', res') ∧
           state_rel (:'a) s' t' ∧
           result_rel (LIST_REL v_rel) v_rel res res' ∧
           (EVERY is_Constant exps1 ⇒
            ∀(t_any:'ffi semanticPrimitives$state).
              evaluate t_any env3 (REVERSE exps3) = (t_any, res') ∧
              ∃success. res' = Rval success)))
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
     (* declaration-level execution: *)
     evaluate_decs s env decs = (s', res) ∧
     state_rel (:'a) s t ∧
     env_rel v_rel env env' ∧
     id_rel decs compile_decs decs' ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate_decs t env' decs' = (t', res') ∧
       state_rel (:'a) s' t' ∧
       result_rel (env_rel v_rel) v_rel res res')
  ’,
  ho_match_mp_tac (name_ind_cases [``()``, ``()``, ``Dlet``] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def,Excl "getOpClass_def"]
  \\ fs [Q.prove (`Case ((), x) = Case (x)`, simp [markerTheory.Case_def]),
         Excl "getOpClass_def"]
  \\ rveq \\ fs [Excl "getOpClass_def"]);

(*
val eval_simulation_setup = setup (‘
  (∀ ^s env exps.
     (* running altered code: *)
     (∀ s' b n3 res t env' exps1 exps2 exps3 n2 n4 xs binders fvs ws0 env0
       (t0:'ffi semanticPrimitives$state).
         evaluate s env exps = (s', res) ∧
         state_rel (:'a) s t ∧
         annotate_exps binders (REVERSE exps) = (exps1,n2,fvs) ∧
         n2 ≤ n3 ∧
         lift_exps b [] n3 exps1 = (exps3,n4,xs) ∧
         EVERY (every_exp (one_con_check env.c)) exps ∧
         weak_env_rel fvs env env' ∧
         const_env_rel binders env' env0 ∧
         res <> Rerr (Rabort Rtype_error) ==>
         ∃ws.
           EVERY (every_exp (one_con_check env.c)) exps3 ∧
           LIST_REL (λ(n,x) w.
             evaluate t0 env0 [x] = (t0,Rval [w])) xs ws ∧
           (∀env3.
              EVERY (can_lookup env3.v)
                (ZIP (MAP (explode o FST) xs,ws)) ∧
              weak_env_rel fvs env env3 ⇒
              ∃t' res'.
                evaluate t env3 (REVERSE exps3) = (t', res') ∧
                state_rel (:'a) s' t' ∧
                result_rel (LIST_REL v_rel) v_rel res res')))
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
     (* declaration-level execution: *)
     evaluate_decs s env decs = (s', res) ∧
     state_rel (:'a) s t ∧
     env_rel v_rel env env' ∧
     id_rel decs compile_decs decs' ∧
     res <> Rerr (Rabort Rtype_error) ==>
     ∃t' res'.
       evaluate_decs t env' decs' = (t', res') ∧
       state_rel (:'a) s' t' ∧
       result_rel (env_rel v_rel) v_rel res res')
  ’,
  ho_match_mp_tac (name_ind_cases [``()``, ``()``, ``Dlet``] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def,Excl "getOpClass_def"]
  \\ fs [Q.prove (`Case ((), x) = Case (x)`, simp [markerTheory.Case_def]),
         Excl "getOpClass_def"]
  \\ rveq \\ fs [Excl "getOpClass_def"]);
*)

(*-----------------------------------------------------------------------*
   automatic rewrites and misc lemmas
 *-----------------------------------------------------------------------*)

Theorem annotate_exps_sing[simp]:
  annotate_exps t [e] = (es,n1,fvs) ⇔
  ∃e1. annotate_exp t e = (e1,n1,fvs) ∧ es = [e1]
Proof
  fs [annotate_exp_def] \\ pairarg_tac \\ gvs [] \\ eq_tac \\ gvs []
QED

Triviality get_c_simp[simp]:
  (<|v := alist_to_ns ws; c := nsEmpty|> +++ env).c = env.c
Proof
  fs [extend_dec_env_def]
QED

Triviality alist_to_ns_eq:
  alist_to_ns xs = nsBindList xs nsEmpty
Proof
  Induct_on ‘xs’ \\ fs [namespaceTheory.nsBindList_def,FORALL_PROD]
QED

Theorem nsLookup_nsBindList:
  nsLookup (nsBindList ws nsEmpty) (Long m n) = NONE
Proof
  Induct_on ‘ws’ \\ fs [namespaceTheory.nsBindList_def,FORALL_PROD]
QED

Theorem map_ok_str_empty:
  map_ok str_empty
Proof
  fs [str_empty_def,mlmapTheory.empty_thm,mlstringTheory.TotOrd_compare]
QED

Theorem bump_make_name:
  bump s n ≤ m ⇒ make_name m ≠ s
Proof
  rw [bump_def,make_name_def]
  \\ CCONTR_TAC \\ gvs []
  \\ last_x_assum mp_tac
  \\ EVAL_TAC \\ fs [ADD1]
QED

Theorem build_conv_v_rel:
  LIST_REL v_rel vs vs' ∧
  build_conv envc cn vs = SOME v
  ⇒
  ∃v'.
    build_conv envc cn vs' = SOME v' ∧
    v_rel v v'
Proof
  rw[build_conv_def,AllCaseEqs()]>>
  simp[v_rel_cases]
QED

Theorem annotate_exps_LENGTH:
  ∀es binders es' n fvs.
  annotate_exps binders es = (es',n,fvs)
  ⇒
  LENGTH es' = LENGTH es
Proof
  Induct_on`es`>>rw[annotate_exp_def]>>
  rpt(pairarg_tac>>fs[])>>
  every_case_tac>>gvs[]
  >- (Cases_on`es`>>fs[])>>
  metis_tac[]
QED

Theorem lift_exps_LENGTH:
  ∀es b xs n es' n' xs'.
  lift_exps b xs n es = (es',n',xs') ⇒
  LENGTH es' = LENGTH es
Proof
  Induct_on`es`>>rw[lift_exp_def]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[]>>
  metis_tac[]
QED

Theorem lift_exp_acc_aux:
  (∀b xs n e e' n' xs'.
    lift_exp b xs n e = (e',n',xs') ⇒
    ∀ys. lift_exp b (xs++ys) n e = (e',n',xs'++ys)) ∧
  (∀b xs n es es' n' xs'.
    lift_exps b xs n es = (es',n',xs') ⇒
    ∀ys. lift_exps b (xs++ys) n es = (es',n',xs'++ys)) ∧
  (∀b xs n pes pes' n' xs'.
    lift_pes b xs n pes = (pes',n',xs') ⇒
    ∀ys. lift_pes b (xs++ys) n pes = (pes',n',xs'++ys)) ∧
  (∀b xs n funs funs' n' xs'.
    lift_funs b xs n funs = (funs',n',xs') ⇒
    ∀ys. lift_funs b (xs++ys) n funs = (funs',n',xs'++ys))
Proof
  ho_match_mp_tac lift_exp_ind>>rw[lift_exp_def]>>
  rpt(pairarg_tac>>fs[])>>strip_tac>>gvs[]
QED

Theorem lift_exp_acc:
  ∀e b xs n e' n' xs'.
    lift_exp b xs n e = (e',n',xs') ⇒
    ∃ys.
      xs' = ys ++ xs ∧
      lift_exp b [] n e = (e',n',ys)
Proof
  rpt strip_tac>>
  ‘let
     (e'0,n'0,xs0) = lift_exp b [] n e;
     (e',n',xs') = lift_exp b xs n e
   in
     e'0=e' ∧ n'0=n' ∧ xs'=xs0++xs’ by
  (
    rw[]>>rpt(pairarg_tac>>fs[])>>
    ‘(∀b xs n e e' n' xs'.
       lift_exp b xs n e = (e',n',xs') ⇒
       ∀ys. lift_exp b (xs ++ ys) n e = (e',n',xs' ++ ys))’
      by metis_tac[lift_exp_acc_aux]>>
    ‘lift_exp b ([]++xs) n e = (e'0,n'0,xs0 ++ xs)’
      by metis_tac[]>>
    fs[]
  )
  >>fs[]>>rpt(pairarg_tac>>fs[])
QED

Theorem lift_exps_acc:
  ∀es b xs n es' n' xs'.
    lift_exps b xs n es = (es',n',xs') ⇒
    ∃ys.
      xs' = ys ++ xs ∧
      lift_exps b [] n es = (es',n',ys)
Proof
  rpt strip_tac>>
  ‘let
     (es'0,n'0,xs0) = lift_exps b [] n es;
     (es',n',xs') = lift_exps b xs n es
   in
     es'0=es' ∧ n'0=n' ∧ xs'=xs0++xs’ by
  (
    rw[]>>rpt(pairarg_tac>>fs[])>>
    ‘(∀b xs n es es' n' xs'.
       lift_exps b xs n es = (es',n',xs') ⇒
       ∀ys. lift_exps b (xs ++ ys) n es = (es',n',xs' ++ ys))’
      by metis_tac[lift_exp_acc_aux]>>
    ‘lift_exps b ([]++xs) n es = (es'0,n'0,xs0 ++ xs)’
      by metis_tac[]>>
    fs[]
  )
  >>fs[]>>rpt(pairarg_tac>>fs[])
QED

Theorem FDOM_SUBSET_SUBMAP:
  FDOM f ⊆ FDOM (g: 'a |-> unit) ⇒
  f SUBMAP g
Proof
  rw[SUBMAP_FLOOKUP_EQN]>>
  fs[SUBSET_DEF,FDOM_FLOOKUP]
QED

Theorem weak_env_rel_less:
  map_ok f ∧ map_ok g ∧
  FDOM (to_fmap f) ⊆ FDOM (to_fmap g) ∧
  weak_env_rel g env env' ⇒
  weak_env_rel f env env'
Proof
  rw[weak_env_rel_def]>>
  first_x_assum match_mp_tac>>
  qpat_x_assum`lookup _ _ = _` mp_tac>>
  DEP_REWRITE_TAC[mlmapTheory.lookup_thm]>>
  simp[]>>
  `(to_fmap f) SUBMAP (to_fmap g)` by
    (match_mp_tac FDOM_SUBSET_SUBMAP>>
    fs[])>>
  fs[SUBMAP_FLOOKUP_EQN]
QED

Triviality sing_lam_prod_lemma:
  (λ(a,b,c). ([a],b,c)) t = (x,y,z)
  ⇔
  ∃a1. t = (a1,y,z) ∧ x = [a1]
Proof
  PairCases_on ‘t’ \\ fs []
  \\ rw [] \\ eq_tac \\ rw [] \\ gvs []
QED

Triviality ann_list_exp_imp_eval_consts:
  every_exp (one_con_check env.c) e2 ∧
  annotate_exp binders e2 = (e3,n2,fvs2) ∧
  lift_exp b [] n3 e3 = (e4,n4,xs) ⇒
  every_exp (one_con_check env.c) e4 ∧
  ALL_DISTINCT (MAP FST xs) ∧
  ∃ws1. ∀t0.
    evaluate_decs (t0: 'ffi semanticPrimitives$state) env0
      (MAP (UNCURRY (λn. Dlet unknown_loc (Pvar (explode n)))) (REVERSE xs)) =
    (t0,Rval <|v := alist_to_ns ws1; c := nsEmpty|>)
Proof
  cheat (* intuition: the lifted expressions, xs, always evaluate to
                      some values without depending on / modifying state *)
QED

Triviality ann_list_exps_imp_eval_consts:
  EVERY (every_exp (one_con_check env.c)) e2 ∧
  annotate_exps binders e2 = (e3,n2,fvs2) ∧
  lift_exps b [] n3 e3 = (e4,n4,xs) ⇒
  EVERY (every_exp (one_con_check env.c)) e4 ∧
  ALL_DISTINCT (MAP FST xs) ∧
  ∃ws1. ∀t0.
    evaluate_decs (t0: 'ffi semanticPrimitives$state) env0
      (MAP (UNCURRY (λn. Dlet unknown_loc (Pvar (explode n)))) (REVERSE xs)) =
    (t0,Rval <|v := alist_to_ns ws1; c := nsEmpty|>)
Proof
  cheat (* intuition: the lifted expressions, xs, always evaluate to
                      some values without depending on / modifying state *)
QED

Theorem nsBind_EVERY_can_lookup:
  nsBind n v gs = alist_to_ns ws ∧ EVERY (can_lookup env) ws ⇒
  nsLookup env (Short n) = SOME v
Proof
  Cases_on ‘gs’
  \\ fs [namespaceTheory.alist_to_ns_def,namespaceTheory.nsBind_def]
  \\ rw [] \\ gvs [can_lookup_def]
QED

Theorem nsBind_EVERY_can_lookup_extra:
  nsBind n v (alist_to_ns ws1) = alist_to_ns ws ∧ EVERY (can_lookup env) ws ⇒
  EVERY (can_lookup env) ws1
Proof
  fs [namespaceTheory.alist_to_ns_def,namespaceTheory.nsBind_def]
  \\ rw [] \\ gvs []
QED

Triviality to_UNCURRY:
  (λ(n,e). Dlet unknown_loc (Pvar (explode n)) e) =
  UNCURRY (λn. Dlet unknown_loc (Pvar (explode n)))
Proof
  fs [FUN_EQ_THM,FORALL_PROD]
QED

(*-----------------------------------------------------------------------*
   proofs of individual cases
 *-----------------------------------------------------------------------*)

Triviality eval_simulation_Var:
  ^(#get_goal eval_simulation_setup `Case ([Var _])`)
Proof
  rw [] \\ gvs [AllCaseEqs(),PULL_EXISTS]
  >-
   (drule_all source_evalProofTheory.env_rel_nsLookup_v
    \\ strip_tac \\ fs [])
  \\ reverse (gvs [annotate_exp_def,AllCaseEqs(),lift_exp_def,evaluate_def])
  \\ rw []
  >- (gvs [alist_to_ns_eq,weak_env_rel_def]
      \\ res_tac \\ fs [nsLookup_nsBindList]
      \\ Cases \\ fs [])
  \\ gvs [extend_dec_env_def,namespacePropsTheory.nsLookup_nsAppend_some,
          namespaceTheory.id_to_mods_def,weak_env_rel_def]
  \\ first_x_assum $ drule_at Any
  \\ impl_tac >- fs [map_ok_str_empty,mlmapTheory.lookup_insert]
  \\ strip_tac \\ fs []
QED

Triviality eval_simulation_Lit:
  ^(#get_goal eval_simulation_setup `Case ([Lit _])`)
Proof
  simp [v_rel_refl] \\ rw []
  \\ gvs [annotate_exp_def,lift_exp_def,evaluate_def,v_rel_refl,AllCaseEqs()]
  \\ pairarg_tac \\ gvs [AllCaseEqs()]
  \\ rpt (fs [namespaceTheory.nsBindList_def,v_rel_refl]
          \\ gvs [evaluate_decs_def,pat_bindings_def,evaluate_def,pmatch_def,v_rel_refl]
          \\ NO_TAC)
  \\ gvs [evaluate_decs_def,pat_bindings_def,evaluate_def,pmatch_def,v_rel_refl]
  \\ gvs [namespaceTheory.nsBind_def,extend_dec_env_def,AllCaseEqs(),is_Constant_def]
  \\ rw [can_lookup_def]
  \\ fs [Once v_rel_cases] \\ fs []
  \\ drule_all nsBind_EVERY_can_lookup \\ fs []
QED

Triviality eval_simulation_App:
  ^(#get_goal eval_simulation_setup `Case ([App _ _])`)
Proof
  cheat
QED

Triviality eval_simulation_Con:
  ^(#get_goal eval_simulation_setup `Case ([Con _ _])`)
Proof
  rpt strip_tac
  >- cheat (* no change case *)
  \\ fs [CaseEq"prod"]
  \\ gvs [annotate_exp_def]
  \\ pairarg_tac \\ gvs [CaseEq"bool"]
  >~ [‘EXISTS ($¬ ∘ is_Constant) es2’] >-
   (last_x_assum kall_tac
    \\ last_x_assum drule
    \\ disch_then drule
    \\ gvs [lift_exp_def]
    \\ rpt (pairarg_tac \\ gvs [])
    \\ disch_then $ drule_at $ Pos $ el 2 \\ fs [SF ETA_ss]
    \\ disch_then $ drule_at $ Pos $ el 2 \\ fs [is_Constant_def]
    \\ disch_then $ qspec_then ‘env3’ mp_tac
    \\ impl_tac >- (fs [] \\ CCONTR_TAC \\ fs [])
    \\ strip_tac \\ fs []
    \\ imp_res_tac annotate_exps_LENGTH
    \\ imp_res_tac lift_exps_LENGTH
    \\ gvs [] \\ rpt strip_tac
    \\ fs [evaluate_def]
    \\ ‘env3.c = env.c’ by gvs [weak_env_rel_def,const_env_rel_def]
    \\ gvs []
    \\ Cases_on ‘v2’ \\ gvs [AllCaseEqs(),build_conv_def]
    \\ gvs [AllCaseEqs(),v_rel_Conv])
  \\ rename [‘EVERY is_Constant es2’]
  \\ fs [lift_exp_def,is_trivial_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ Cases_on ‘~b’ \\ gvs []
  >- cheat (* uninteresting case *)
  \\ gvs [CaseEq"bool"]
  >-
   (Cases_on ‘es2’ \\ gvs [evaluate_def,lift_exp_def]
    \\ imp_res_tac annotate_exps_LENGTH \\ gvs []
    \\ gvs [build_conv_def]
    \\ gvs [do_con_check_def,weak_env_rel_def]
    \\ rpt strip_tac \\ gvs []
    \\ Cases_on ‘cn’ \\ gvs [v_rel_Conv]
    \\ gvs [AllCaseEqs(),v_rel_Conv])
  \\ last_x_assum kall_tac
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then $ drule_at $ Pos $ el 2
  \\ fs [SF ETA_ss]
  \\ Cases_on ‘v2 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ disch_then $ drule_at $ Pos $ el 2 \\ fs []
  \\ drule ann_list_exps_imp_eval_consts
  \\ disch_then drule
  \\ disch_then drule
  \\ disch_then $ qspec_then ‘env0’ strip_assume_tac
  \\ gvs [evaluate_decs_append,AllCaseEqs(),PULL_EXISTS,combine_dec_result_def,is_Constant_def]
  \\ gvs [evaluate_decs_def,AllCaseEqs(),PULL_EXISTS,pmatch_def,evaluate_def]
  \\ last_assum $ qspec_then ‘t’ strip_assume_tac \\ gvs []
  \\ ‘env0.c = env.c’ by gvs [weak_env_rel_def,const_env_rel_def]
  \\ imp_res_tac annotate_exps_LENGTH
  \\ imp_res_tac lift_exps_LENGTH
  \\ gvs [can_lookup_def]
  \\ drule_all nsBind_EVERY_can_lookup_extra
  \\ strip_tac
  \\ drule_all nsBind_EVERY_can_lookup
  \\ strip_tac
  \\ fs []
  >- (disch_then $ qspec_then ‘env3’ mp_tac \\ fs []
      \\ strip_tac \\ gvs []
      \\ gvs [build_conv_def,AllCaseEqs(),v_rel_Conv]
      \\ cheat (* envs not quite right *))
  \\ qexists_tac ‘env3’ \\ fs [] \\ gvs [EVERY_MEM]
QED

Triviality eval_simulation_Let:
  ^(#get_goal eval_simulation_setup `Case ([Let _ _ _])`)
Proof
  cheat (*
  rw[]
  >- cheat (* no change case *)
  \\ gvs [CaseEq"prod"]
  \\ Cases_on ‘v2 = Rerr (Rabort Rtype_error)’ \\ gvs []
  \\ first_x_assum drule \\ gvs [PULL_EXISTS]
  \\ rename [‘Let xo’]
  \\ Cases_on ‘xo’
  >- cheat (* similar to below, but simpler *)
  \\ gvs [annotate_exp_def,lift_exp_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [annotate_exp_def,lift_exp_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ disch_then drule
  \\ gvs [sing_lam_prod_lemma,PULL_EXISTS]
  \\ disch_then $ drule_at $ Pos $ el 2
  \\ gvs []
  \\ ‘weak_env_rel fvs1 env env'’ by (
    (drule_at Any) weak_env_rel_less>>
    disch_then match_mp_tac>>
    DEP_REWRITE_TAC
      (CONJUNCTS (SIMP_RULE std_ss [IMP_CONJ_THM] mlmapTheory.union_thm))>>
    simp[]>>
    rw[]>>
    metis_tac[map_ok_annotate_exp_cmp,SND,mlmapTheory.delete_thm])
  \\ disch_then drule
  \\ disch_then drule
  \\ fs [is_Constant_def]
  \\ reverse (Cases_on ‘v2’) \\ gvs []
  >- cheat (* easier case *)
  \\ gvs [PULL_EXISTS]
  \\ drule lift_exp_acc
  \\ strip_tac \\ gvs [REVERSE_APPEND,evaluate_decs_append]
  \\ drule_all ann_list_exp_imp_eval_consts
  \\ disch_then $ qspecl_then
       [‘t0’,‘locs’,‘<|v := alist_to_ns ws; c := nsEmpty|> +++ env0’] strip_assume_tac
  \\ gvs [combine_dec_result_def]
  \\ rpt strip_tac
  \\ first_x_assum $ qspec_then ‘env3’ mp_tac
  \\ impl_tac
  >- cheat
  \\ strip_tac \\ fs []
  \\ last_x_assum kall_tac
  \\ last_x_assum drule
  \\ disch_then drule
  \\ disch_then $ drule_at $ Pos $ el 2
  \\ gvs [namespaceTheory.nsOptBind_def]
  \\ drule evaluate_sing \\ strip_tac \\ gvs []
  \\ rename [‘v_rel v1 v2’]
  \\ disch_then $ qspecl_then [‘<|v := alist_to_ns ws; c := nsEmpty|> +++ env3
                with v := nsBind x v1 (<|v := alist_to_ns ws; c := nsEmpty|> +++ env3).v’,
            ‘<|v := alist_to_ns ws; c := nsEmpty|> +++ env0’] mp_tac
  \\ impl_tac >- cheat
  \\ fs []
  \\ strip_tac \\ fs []
  \\ cheat (*
  \\ disch_then $ qspec_then ‘env3 with v := nsBind x v2 env3.v’ mp_tac
  \\ impl_tac >- cheat
  \\ strip_tac \\ fs [evaluate_def,namespaceTheory.nsOptBind_def] *) *)
QED

Triviality eval_simulation_Fun:
  ^(#get_goal eval_simulation_setup `Case ([Fun _ _])`)
Proof
  cheat (*
  rpt strip_tac
  >- simp [Once v_rel_cases]
  \\ gvs [annotate_exp_def]
  \\ rpt (pairarg_tac \\ fs [])
  \\ reverse $ gvs [AllCaseEqs()]
  \\ gvs [lift_exp_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ gvs [evaluate_def,is_trivial_def]
  >- cheat (* uninteresting case? *)
  \\ reverse $ Cases_on ‘b’ \\ gvs []
  >- cheat (* uninteresting case? *)
  \\ gvs [evaluate_decs_def,pat_bindings_def]
  \\ ‘env0.c = env.c’ by gvs [const_env_rel_def,weak_env_rel_def]
  \\ fs [evaluate_def,pmatch_def,is_Constant_def,PULL_EXISTS,AllCaseEqs()]
  \\ drule_all ann_list_exp_imp_eval_consts
  \\ disch_then $ qspecl_then [‘env0’] strip_assume_tac
  \\ fs [evaluate_decs_append,to_UNCURRY]
  \\ gvs [AllCaseEqs(),combine_dec_result_def,PULL_EXISTS]
  \\ fs [evaluate_decs_def,evaluate_def,pat_bindings_def,pmatch_def]
  \\ drule_all nsBind_EVERY_can_lookup_extra \\ rw []
  \\ drule_all nsBind_EVERY_can_lookup \\ rw []
  \\ cheat (* v_rel clos *) *)
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

Triviality eval_simulation_cons_cons:
  ^(#get_goal eval_simulation_setup `Case ((e1:exp)::e2::es)`)
Proof
  rpt strip_tac
  >- cheat
  \\ cheat
QED

Triviality eval_simulation_Tannot:
  ^(#get_goal eval_simulation_setup `Case [Tannot _ _]`)
Proof
  cheat
QED

Triviality eval_simulation_Lannot:
  ^(#get_goal eval_simulation_setup `Case [Lannot _ _]`)
Proof
  cheat
QED

Triviality store_lookup_LIST_REL:
  ∀s_refs t_refs l1 R x.
    store_lookup l1 s_refs = SOME x ∧
    LIST_REL R s_refs t_refs ⇒
    ∃y. store_lookup l1 t_refs = SOME y ∧ R x y
Proof
  Induct \\ fs [store_lookup_def,PULL_EXISTS]
  \\ strip_tac \\ Cases \\ fs [] \\ rw []
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
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
  qsuff_tac ‘
   (∀env_c s_refs p v1 vs1 v2 vs2 t_refs.
      v_rel v1 v2 ∧ LIST_REL ((=) ### v_rel) vs1 vs2 ∧
      LIST_REL (sv_rel v_rel) s_refs t_refs ⇒
      case pmatch env_c s_refs p v1 vs1 of
      | No_match => pmatch env_c t_refs p v2 vs2 = No_match
      | Match new1 =>
         (∃new2. pmatch env_c t_refs p v2 vs2 = Match new2 ∧
                 LIST_REL ((=) ### v_rel) new1 new2)
      | _ => T) ∧
   (∀env_c s_refs ps v1 vs1 v2 vs2 t_refs.
      LIST_REL v_rel v1 v2 ∧ LIST_REL ((=) ### v_rel) vs1 vs2 ∧
      LIST_REL (sv_rel v_rel) s_refs t_refs ⇒
      case pmatch_list env_c s_refs ps v1 vs1 of
      | No_match => pmatch_list env_c t_refs ps v2 vs2 = No_match
      | Match new1 =>
         (∃new2. pmatch_list env_c t_refs ps v2 vs2 = Match new2 ∧
                 LIST_REL ((=) ### v_rel) new1 new2)
      | _ => T)’
  >-
   (rw [state_rel_def]
    \\ last_x_assum drule_all
    \\ disch_then irule)
  \\ ho_match_mp_tac pmatch_ind
  \\ rpt conj_tac
  \\ rpt gen_tac
  \\ fs [pmatch_def]
  >~ [‘Litv l1’] >-
   (simp [Once v_rel_cases] \\ rw [] \\ fs [pmatch_def])
  >~ [‘Loc l1’] >-
   (strip_tac \\simp [Once v_rel_cases] \\ rw [] \\ fs [pmatch_def]
    \\ CASE_TAC \\ fs []
    \\ drule_all store_lookup_LIST_REL
    \\ strip_tac \\ fs []
    \\ Cases_on ‘x’ \\ fs [sv_rel_def]
    \\ Cases_on ‘y’ \\ fs [sv_rel_def]
    \\ first_x_assum drule_all \\ rw []
    \\ CASE_TAC \\ fs [])
  \\ rpt strip_tac
  \\ gvs [v_rel_Conv,pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH \\ gvs []
  \\ rpt IF_CASES_TAC \\ gvs []
  >-
   (Cases_on ‘nsLookup env_c n’ \\ gvs []
    \\ PairCases_on ‘x’ \\ gvs [] \\ rw [] \\ fs [])
  \\ reverse (Cases_on ‘pmatch env_c s_refs p v1 vs1’) \\ gvs []
  \\ res_tac \\ fs [] \\ CASE_TAC \\ fs []
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

Triviality evaluate_decs_make_local:
  evaluate_decs st env [make_local xs d] =
  evaluate_decs st env [Dlocal (MAP (λ(n,e).
    Dlet unknown_loc (Pvar (explode n)) e) (REVERSE xs)) [d]]
Proof
  rw [make_local_def] \\ Cases_on ‘xs’ \\ fs []
  \\ gvs [evaluate_decs_def,extend_dec_env_def]
QED

Triviality eval_simulation_Dlet:
  ^(#get_goal eval_simulation_setup `Case (Dlet, [_])`)
Proof
  cheat (*
  rpt strip_tac
  \\ gvs [CaseEq"bool"]
  \\ gvs [id_rel_def,CaseEq"prod"]
  >-
   (Cases_on ‘v2 = Rerr (Rabort Rtype_error)’ >- gvs [] \\ fs []
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
  \\ fs [compile_dec_def]
  \\ last_x_assum kall_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ fs [evaluate_decs_make_local,evaluate_decs_def]
  \\ Cases_on ‘v2 = Rerr (Rabort Rtype_error)’ \\ gvs [PULL_EXISTS]
  \\ last_x_assum $ drule_then mp_tac
  \\ disch_then drule
  \\ simp [lift_exp_def]
  \\ fs [MAX_ASSOC]
  \\ disch_then $ qspecl_then [‘F’,‘MAX n (bump_pat 0 p)’] mp_tac
  \\ fs []
  \\ disch_then $ qspecl_then [‘env'’,‘env'’] mp_tac
  \\ impl_tac >-
   (gvs [weak_env_rel_def,GSYM CONJ_ASSOC,const_env_rel_def]
    \\ conj_tac >- fs [env_rel_def]
    \\ rw []
    \\ drule_all source_evalProofTheory.env_rel_nsLookup_v \\ rw [] \\ fs [])
  \\ strip_tac \\ fs []
  \\ ‘env'.c = env.c’ by fs [env_rel_def] \\ fs []
  \\ qabbrev_tac ‘env3 = <|v := alist_to_ns ws; c := nsEmpty|> +++ env'’
  \\ first_x_assum $ qspec_then ‘env3’ mp_tac
  \\ impl_tac
  >- cheat (* ought to be true *)
  \\ gvs []
  \\ strip_tac \\ gvs []
  \\ reverse (gvs [CaseEq"result"])
  \\ imp_res_tac evaluate_sing \\ gvs []
  \\ rename [‘v_rel v5 v6’]
  \\ rename [‘state_rel (:α) s7 t7’]
  \\ ‘∃m. pmatch env.c s7.refs p v5 [] = m’ by fs []
  \\ drule pmatch_thm
  \\ disch_then drule \\ fs []
  \\ disch_then drule \\ fs []
  \\ strip_tac
  \\ Cases_on ‘m’ \\ gvs [v_rel_refl]
  \\ rpt strip_tac \\ fs [alist_to_ns_eq]
  \\ drule_at Any source_evalProofTheory.env_rel_add_nsBindList
  \\ disch_then $ qspecl_then [‘nsEmpty’,‘nsEmpty’,
                               ‘<| v := nsEmpty ; c := nsEmpty |>’,
                               ‘<| v := nsEmpty ; c := nsEmpty |>’] mp_tac
  \\ fs [env_rel_def,SF SFY_ss] *)
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

Triviality eval_simulation_Dlet_Dtabbrev:
  ^(#get_goal eval_simulation_setup `Case (_,[Dtabbrev _ _ _ _])`)
Proof
  gvs [id_rel_def,compile_dec_def,evaluate_decs_def,env_rel_def]
QED

Triviality eval_simulation_nil:
  ^(#get_goal eval_simulation_setup `Case []`)
Proof
  fs [annotate_exp_def,lift_exp_def] \\ rw []
  \\ qexists_tac ‘[]’ \\ fs []
QED

Triviality eval_simulation_Dlet_nil:
  ^(#get_goal eval_simulation_setup `Case (_,[])`)
Proof
  fs [annotate_exp_def,lift_exp_def,id_rel_def,compile_dec_def,env_rel_def]
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
    eval_simulation_Dlocal, eval_simulation_Scope, eval_simulation_nil,
    eval_simulation_cons_cons, eval_simulation_Tannot, eval_simulation_Lannot,
    eval_simulation_Dlet_nil, eval_simulation_Dlet_Dtabbrev]
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
