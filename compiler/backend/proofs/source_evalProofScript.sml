(*
  Proofs that the source_eval attachment of the compiler
  preserves semantics, and that the oracle semantics can
  be introduced
*)

open preamble semanticsTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     source_evalTheory evaluatePropsTheory evaluateTheory

val _ = new_theory "source_evalProof";

val _ = set_grammar_ancestry ["ast", "source_eval", "string",
    "semantics", "semanticPrimitivesProps"];

(* an instance of custom_do_eval that behaves as much as possible
   like the no-oracle semantics *)

Definition v_to_nat_def:
  v_to_nat v = case v of
   | (Litv (IntLit i)) => SOME (Num i)
   | _ => NONE
End

Definition v_to_env_id_def:
  v_to_env_id v = case v of
    | Conv NONE [gen_id_v; id_v] => (case (v_to_nat gen_id_v, v_to_nat id_v) of
      | (SOME gen_id, SOME id) => SOME (gen_id, id)
      | _ => NONE
    )
    | _ => NONE
End

Definition do_eval_record_def:
  do_eval_record vs (orac : eval_oracle_fun) = case vs of
    | [env_id_v; decs_v] => (case (v_to_env_id env_id_v, v_to_decs decs_v) of
      | (SOME env_id, SOME decs) =>
        let i = FST (FST (orac 0)) in
        let orac' = \j. if j = 0 then ((i + 1, 0), Conv NONE [], [])
          else if j = SUC i then (env_id, Conv NONE [], decs)
          else orac j in
        SOME (env_id, orac', decs)
      | _ => NONE
    )
    | _ => NONE
End

(* the non-Eval case. we need to prove that if there are (syntactically)
   no Eval ops, this will always be the case, and so we can replace an
   activated EvalDecs eval state with NONE *)

Definition env_rel_def:
  env_rel v_rel (env : v sem_env) env' <=>
    env.c = env'.c /\ nsDom env.v = nsDom env'.v /\
    nsDomMod env.v = nsDomMod env'.v /\
    (!nm x y. nsLookup env.v nm = SOME x /\ nsLookup env'.v nm = SOME y ==>
        v_rel x y)
End

Theorem env_rel_mono_rel:
  (!y z. R y z ==> R' y z) ==>
  env_rel R env env' ==>
  env_rel R' env env'
Proof
  simp [env_rel_def] \\ metis_tac []
QED

Theorem env_rel_add_nsBind:
  env_rel R (env with v := ev) (env' with v := ev') /\ R x y ==>
  env_rel R (env with v := nsBind n x ev) (env' with v := nsBind n y ev')
Proof
  rw [env_rel_def]
  \\ Cases_on `nm = Short n`
  \\ fs [nsLookup_nsBind]
  \\ res_tac
QED

Theorem env_rel_add_nsBindList:
  !xs ys. env_rel R (env with v := ev) (env' with v := ev') /\
  LIST_REL ((=) ### R) xs ys ==>
  env_rel R (env with v := nsBindList xs ev) (env' with v := nsBindList ys ev')
Proof
  Induct
  \\ simp [FORALL_PROD, EXISTS_PROD]
  \\ rw []
  \\ fs [namespaceTheory.nsBindList_def, quotient_pairTheory.PAIR_REL_THM]
  \\ irule env_rel_add_nsBind
  \\ simp []
QED

Theorem env_rel_nsLift:
  env_rel R (env with <| v := v |>) (env' with <| v := v' |>) ==>
  env_rel R (env with <| v := nsLift mn v |>)
    (env' with <| v := nsLift mn v' |>)
Proof
  rw [] \\ fs [env_rel_def, nsDom_nsLift, nsDomMod_nsLift]
  \\ rw [namespacePropsTheory.nsLookup_nsLift]
  \\ every_case_tac
  \\ fs []
  \\ res_tac
QED

Theorem env_rel_nsEmpty = LIST_CONJ
  [Q.SPECL [`R`, `x with <| v := nsEmpty |>`] env_rel_def,
    Q.SPECL [`R`, `x`, `y with <| v := nsEmpty |>`] env_rel_def]
  |> SIMP_RULE (std_ss ++ simpLib.type_ssfrag ``: 'a sem_env``)
        [nsLookup_nsEmpty]

val _ = IndDefLib.add_mono_thm env_rel_mono_rel;

Inductive no_Eval_v:
  (no_Eval_v (Env env)) /\
  (EVERY no_Eval_v xs ==> no_Eval_v (Vectorv xs)) /\
  (EVERY no_Eval_v xs ==> no_Eval_v (Conv stmp xs)) /\
  (env_rel (\x y. no_Eval_v x) env env /\ ~ has_Eval x ==>
    no_Eval_v (Closure env nm x)) /\
  (env_rel (\x y. no_Eval_v x) env env /\ ~ EXISTS has_Eval (MAP (SND o SND) funs) ==>
    no_Eval_v (Recclosure env funs nm)) /\
  (no_Eval_v (Litv l)) /\
  (no_Eval_v (Loc n))
End

Definition no_Eval_env_def:
  no_Eval_env env = env_rel (\x y. no_Eval_v x) env env
End

Theorem no_Eval_v_simps =
  [``no_Eval_v (Litv l)``, ``no_Eval_v (Conv cn vs)``,
    ``no_Eval_v (Loc l)``, ``no_Eval_v (Vectorv vs)``,
    ``no_Eval_v (Env e)``,
    ``no_Eval_v (Recclosure env funs nm)``,
    ``no_Eval_v (Closure env nm x)``]
  |> map (SIMP_CONV (srw_ss ()) [Once no_Eval_v_cases, GSYM no_Eval_env_def])
  |> map GEN_ALL
  |> LIST_CONJ

(* is there a [simp local] type way to do this? *)
val _ = bossLib.augment_srw_ss [rewrites [no_Eval_v_simps]];

Theorem do_opapp_no_Eval:
  do_opapp vs = SOME (env, v) /\
  EVERY no_Eval_v vs ==>
  no_Eval_env env /\ ~ has_Eval v
Proof
  rw [do_opapp_cases]
  \\ fs [no_Eval_env_def]
  >- (
    irule env_rel_add_nsBind
    \\ simp []
  )
  >- (
    irule env_rel_add_nsBind
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_rel_add_nsBindList
    \\ simp []
    \\ irule EVERY2_refl
    \\ fs [MEM_MAP, FORALL_PROD, EXISTS_PROD, PULL_EXISTS]
    \\ simp [quotient_pairTheory.PAIR_REL_THM, no_Eval_env_def]
  )
  >- (
    fs [find_recfun_ALOOKUP, EVERY_MEM, MEM_MAP, EXISTS_PROD, PULL_EXISTS]
    \\ imp_res_tac ALOOKUP_MEM
    \\ res_tac
  )
QED

Theorem no_Eval_v_list_to_v:
  !xs. no_Eval_v (list_to_v xs) = EVERY no_Eval_v xs
Proof
  Induct
  \\ simp [list_to_v_def]
QED

Theorem no_Eval_v_v_to_list:
  !v xs. v_to_list v = SOME xs /\ no_Eval_v v ==> EVERY no_Eval_v xs
Proof
  recInduct terminationTheory.v_to_list_ind
  \\ rw [terminationTheory.v_to_list_def]
  \\ fs [option_case_eq]
  \\ rveq \\ fs []
QED

Theorem do_app_no_Eval:
  do_app (refs, ffi) op vs = SOME r /\
  EVERY (sv_every no_Eval_v) refs /\
  EVERY no_Eval_v vs ==>
  ? refs' ffi' r'.
  r = ((refs', ffi'), r') /\
  EVERY (sv_every no_Eval_v) refs' /\
  case list_result r' of
          Rval vs => EVERY no_Eval_v vs
        | Rerr (Rraise v) => no_Eval_v v
        | Rerr (Rabort v8) => T
Proof
  PairCases_on `r`
  \\ rw [do_app_cases, Boolv_def, ffiTheory.ffi_result_case_eq]
  \\ rw []
  \\ fs [div_exn_v_def, sub_exn_v_def, chr_exn_v_def]
  \\ fs [store_assign_def, store_alloc_def] \\ rveq \\ fs []
  \\ TRY (irule IMP_EVERY_LUPDATE)
  \\ simp [no_Eval_v_list_to_v, EVERY_MAP]
  \\ imp_res_tac no_Eval_v_v_to_list
  \\ fs [option_case_eq] \\ rveq \\ fs []
  \\ TRY (irule IMP_EVERY_LUPDATE)
  \\ simp []
  \\ TRY (
    CHANGED_TAC (fs [store_lookup_def])
    \\ imp_res_tac EVERY_EL
    \\ rfs []
  )
  \\ TRY (drule_then irule (EVERY_EL |> RES_CANON |> hd))
  \\ simp []
  \\ cheat (* EnvLookup I think *)
QED

Theorem pmatch_no_Eval:
  (!env_c refs p v binds binds'.
  pmatch env_c refs p v binds = Match binds' /\
  EVERY (sv_every no_Eval_v) refs /\
  EVERY (no_Eval_v o SND) binds /\
  no_Eval_v v ==>
  EVERY (no_Eval_v o SND) binds'
  )
  /\
  (!env_c refs ps vs binds binds'.
  pmatch_list env_c refs ps vs binds = Match binds' /\
  EVERY (sv_every no_Eval_v) refs /\
  EVERY (no_Eval_v o SND) binds /\
  EVERY no_Eval_v vs ==>
  EVERY (no_Eval_v o SND) binds'
  )
Proof
  ho_match_mp_tac terminationTheory.pmatch_ind
  \\ rw [terminationTheory.pmatch_def] \\ fs []
  \\ fs [option_case_eq, pair_case_eq, bool_case_eq, store_v_case_eq,
        match_result_case_eq]
  \\ rveq \\ fs []
  \\ fs [Q.ISPEC `Match b` EQ_SYM_EQ]
  \\ TRY (
    CHANGED_TAC (fs [store_lookup_def])
    \\ imp_res_tac EVERY_EL
    \\ rfs []
  )
QED

Theorem no_Eval_extend:
  no_Eval_env env1 /\ no_Eval_env env2 ==>
  no_Eval_env (extend_dec_env env1 env2)
Proof
  rw [no_Eval_env_def, extend_dec_env_def]
  \\ fs [env_rel_def]
  \\ rw [nsLookup_nsAppend_some]
  \\ res_tac
QED

Triviality alist_to_ns_to_bind2 = GEN_ALL nsAppend_to_nsBindList
    |> Q.SPEC `nsEmpty`
    |> REWRITE_RULE [namespacePropsTheory.nsAppend_nsEmpty]

Triviality nsSing_eq_bind = namespaceTheory.nsSing_def
  |> REWRITE_RULE [GSYM namespaceTheory.nsBind_def,
    GSYM namespaceTheory.nsEmpty_def]

Definition not_oracle_def:
  not_oracle (SOME (EvalOracle _)) = F /\
  not_oracle _ = T
End

val _ = bossLib.augment_srw_ss [rewrites [not_oracle_def]];

Triviality pair_CASE_eq_pairarg:
  pair_CASE p f = (\(x, y). f x y) p
Proof
  Cases_on `p` \\ simp []
QED

Theorem combine_dec_result_eq_Rerr:
  combine_dec_result env r = Rerr e <=> r = Rerr e
Proof
  Cases_on `r` \\ simp [combine_dec_result_def]
QED

val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);

Theorem no_Eval_evaluate:
  (! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  no_Eval_env env /\
  ~ EXISTS has_Eval exps /\
  EVERY (sv_every no_Eval_v) s.refs /\
  not_oracle s.eval_state /\
  res <> Rerr (Rabort Rtype_error) ==>
  case evaluate (s with eval_state := NONE) env exps of
    (t, res') =>
  t = (s' with eval_state := NONE) /\ res' = res /\
  EVERY (sv_every no_Eval_v) s'.refs /\
  not_oracle s'.eval_state /\
  (case res of Rval vs => EVERY no_Eval_v vs
    | Rerr (Rraise v) => no_Eval_v v
    | _ => T)
  )
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  no_Eval_env env /\
  no_Eval_v err_x /\
  no_Eval_v x /\
  ~ EXISTS has_Eval (MAP SND pes) /\
  EVERY (sv_every no_Eval_v) s.refs /\
  not_oracle s.eval_state /\
  res <> Rerr (Rabort Rtype_error) ==>
  case evaluate_match (s with eval_state := NONE) env x pes err_x of
    (t, res') =>
  t = (s' with eval_state := NONE) /\ res' = res /\
  EVERY (sv_every no_Eval_v) s'.refs /\
  not_oracle s'.eval_state /\
  (case res of Rval vs => EVERY no_Eval_v vs
    | Rerr (Rraise v) => no_Eval_v v
    | _ => T)
  )
   /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  no_Eval_env env /\
  ~ EXISTS has_Eval_dec decs /\
  EVERY (sv_every no_Eval_v) s.refs /\
  not_oracle s.eval_state /\
  res <> Rerr (Rabort Rtype_error) ==>
  case evaluate_decs (s with eval_state := NONE) env decs of
    (t, res') =>
  t = (s' with eval_state := NONE) /\ res' = res /\
  EVERY (sv_every no_Eval_v) s'.refs /\
  not_oracle s'.eval_state /\
  (case res of Rval env => no_Eval_env env
    | Rerr (Rraise v) => no_Eval_v v
    | _ => T)
  )
Proof
  (* the try-this-on-everything approach is ugly, but it would be
     super tedious to go through 20-plus cases for this *)
  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rw [terminationTheory.full_evaluate_def]
  \\ fs [has_Eval_def, has_Eval_dec_def, EVERY_REVERSE]
  \\ rveq \\ fs []
  \\ fs [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
    option_case_eq, exp_or_val_case_eq, match_result_case_eq,
    eval_state_case_eq,
    do_log_def, do_if_def, build_conv_def, dec_clock_def, declare_env_def,
    bind_exn_v_def]
  \\ rw []
  \\ fs [pair_CASE_eq_pairarg, combine_dec_result_eq_Rerr]
  \\ rpt (pairarg_tac \\ fs [])
  \\ ntac 2 (rveq \\ fs [])
  \\ rfs []
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs []
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, EVERY_REVERSE]
  \\ rfs []
  \\ TRY (MAP_FIRST (drule_then strip_assume_tac) [
    do_opapp_no_Eval, do_app_no_Eval, CONJUNCT1 pmatch_no_Eval])
  \\ rfs [EVERY_REVERSE]
  \\ TRY (qpat_x_assum `_ ==> _` mp_tac
    \\ (impl_tac THENL [rpt strip_tac, strip_tac])
    \\ fs [] \\ rfs [])
  \\ rveq \\ fs []
  \\ simp [namespaceTheory.nsOptBind_def, build_rec_env_merge,
        nsAppend_to_nsBindList, combine_dec_result_def, no_Eval_extend,
        combine_dec_result_def,
        GSYM (SIMP_RULE (srw_ss ()) [] extend_dec_env_def)]
  \\ rpt CASE_TAC
  \\ fs [alist_to_ns_to_bind2, nsSing_eq_bind]
  \\ TRY (
    simp [no_Eval_env_def]
    \\ MAP_FIRST irule [env_rel_add_nsBind, env_rel_add_nsBindList,
        env_rel_nsLift]
    \\ simp [GSYM no_Eval_env_def]
  )
  \\ simp [Q.SPEC `x with <| v := nsEmpty |>` no_Eval_env_def, env_rel_nsEmpty,
    no_Eval_extend]
  \\ TRY (
    irule EVERY2_refl
    \\ fs [GSYM EVERY_MEM, EVERY_MAP]
    \\ first_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC)
    \\ simp [FORALL_PROD, quotient_pairTheory.PAIR_REL_THM, EVERY_MAP]
  )
  \\ TRY (fs [no_Eval_env_def, env_rel_def] \\ res_tac \\ fs [] \\ NO_TAC)
QED

(* the Eval case. adding the compiler adjusts the code, adds a
   compiler state to the refs, and adjusts every Env to contain
   the new module.
*)

Theorem namespace1_size:
  namespace1_size f1 f2 f3 xs =
    LENGTH xs + SUM (MAP (namespace2_size f1 f2 f3) xs)
Proof
  Induct_on `xs` \\ simp [namespaceTheory.namespace_size_def]
QED

Definition nsAdj_def:
  nsAdj (Bind nms mods) = Bind nms
        (MAP (\(nm, m). (adj_mod_name nm, nsAdj m)) mods)
Termination
  WF_REL_TAC `measure (namespace_size (K 0) (K 0) (K 0))`
  \\ rw [namespaceTheory.namespace_size_def]
  \\ fs [MEM_SPLIT, namespace1_size, namespaceTheory.namespace_size_def,
    SUM_APPEND]
End

Definition env_adj_rel_def:
  env_adj_rel v_rel (env : v sem_env) env' <=>
    nsDomMod env'.c DIFF IMAGE (CONS compiler_module_name) UNIV =
        IMAGE (MAP adj_mod_name) (nsDomMod env.c) /\
    nsDom env'.c DIFF IMAGE (Long compiler_module_name) UNIV =
        IMAGE adj_id (nsDom env.c) /\
    nsDomMod env'.v DIFF IMAGE (CONS compiler_module_name) UNIV =
        IMAGE (MAP adj_mod_name) (nsDomMod env.v) /\
    nsDom env'.v DIFF IMAGE (Long compiler_module_name) UNIV =
        IMAGE adj_id (nsDom env.v) /\
    (!nm x. nsLookup env.c nm = SOME x ==>
        nsLookup env'.c (adj_id nm) = SOME x) /\
    (!nm x y. nsLookup env.v nm = SOME x /\
        nsLookup env'.v (adj_id nm) = SOME y ==>
        v_rel x y)
End

Theorem env_adj_rel_mono_rel:
  (!y z. R y z ==> R' y z) ==>
  env_adj_rel R env env' ==>
  env_adj_rel R' env env'
Proof
  simp [env_adj_rel_def] \\ metis_tac []
QED

val _ = IndDefLib.add_mono_thm env_adj_rel_mono_rel;

Theorem env_adj_rel_nsLookup_c:
  env_adj_rel R env env' /\
  nsLookup env.c id = SOME data ==>
  nsLookup env'.c (adj_id id) = SOME data
Proof
  rw [env_adj_rel_def]
QED

Theorem adj_mod_name_not_compiler:
  adj_mod_name m ≠ compiler_module_name
Proof
  rw [adj_mod_name_def]
  \\ strip_tac
  \\ fs []
  \\ fs [stringTheory.isPREFIX_STRCAT]
  \\ rveq \\ fs []
QED

Theorem adj_id_not_compiler:
  !id x. adj_id id ≠ Long compiler_module_name x
Proof
  Induct
  \\ simp [adj_id_def, adj_mod_name_not_compiler]
QED

Theorem adj_mod_name_11:
  (adj_mod_name m = adj_mod_name m') = (m = m')
Proof
  rw [adj_mod_name_def]
  \\ EQ_TAC
  \\ rw []
  \\ TRY strip_tac
  \\ fs []
  \\ first_x_assum (fn t => mp_tac t \\ simp [] \\ irule IS_PREFIX_TRANS)
  \\ goal_assum (first_x_assum o mp_then Any mp_tac)
  \\ simp []
QED

Theorem adj_id_11:
  !id id'. (adj_id id = adj_id id') = (id = id')
Proof
  Induct \\ simp [adj_id_def]
  \\ gen_tac \\ Cases
  \\ simp [adj_id_def, adj_mod_name_11]
QED

Triviality env_adj_rel_nsLookup_helper:
  m = IMAGE f (nsDom ns) /\ nsLookup ns id = SOME v ==>
  f id ∈ m
Proof
  rw [nsLookup_nsDom]
  \\ simp []
  \\ metis_tac []
QED

Theorem env_adj_rel_nsLookup_v:
  env_adj_rel R env env' /\
  nsLookup env.v id = SOME v ==>
  ?v'. nsLookup env'.v (adj_id id) = SOME v' /\ R v v'
Proof
  rw [env_adj_rel_def]
  \\ drule_then drule env_adj_rel_nsLookup_helper
  \\ simp [adj_id_not_compiler, nsLookup_nsDom]
  \\ rw []
  \\ fs []
  \\ res_tac
QED

Theorem env_adj_rel_nsBind:
  R v v' /\ env_adj_rel R (env with v := vs) (env' with v := vs') ==>
  env_adj_rel R (env with v := nsBind nm v vs) (env' with v := nsBind nm v' vs')
Proof
  rw [env_adj_rel_def, adj_id_def]
  \\ Cases_on `nm'` \\ fs [adj_id_def]
  >- (
    Cases_on `nm = n` \\ fs [nsLookup_nsBind]
    \\ res_tac
    \\ rfs [adj_id_def]
  )
  \\ res_tac
  \\ rfs [adj_id_def]
QED

Theorem env_adj_rel_nsBindList:
  !xs ys. env_adj_rel R (env with v := ev) (env' with v := ev') /\
  LIST_REL ((=) ### R) xs ys ==>
  env_adj_rel R (env with v := nsBindList xs ev)
    (env' with v := nsBindList ys ev')
Proof
  Induct
  \\ simp [FORALL_PROD, EXISTS_PROD]
  \\ rw []
  \\ fs [namespaceTheory.nsBindList_def, quotient_pairTheory.PAIR_REL_THM]
  \\ irule env_adj_rel_nsBind
  \\ simp []
QED


Inductive v_rel:
  (!id env'. v_to_env_id v = SOME id /\ lookup_env es id = SOME env' /\
        env_adj_rel (v_rel es) env env' ==>
    v_rel es (Env env) v) /\
  (LIST_REL (v_rel es) xs ys ==>
    v_rel es (Vectorv xs) (Vectorv ys)) /\
  (LIST_REL (v_rel es) xs ys ==>
    v_rel es (Conv stmp xs) (Conv stmp ys)) /\
  (env_adj_rel (v_rel es) env env' ==>
    v_rel es (Closure env nm x) (Closure env' nm (compile_exp x))) /\
  (env_adj_rel (v_rel es) env env' ==>
    v_rel es (Recclosure env funs nm)
        (Recclosure env' (MAP (I ## I ## compile_exp) funs) nm)) /\
  (v_rel es (Litv l) (Litv l)) /\
  (v_rel es (Loc n) (Loc (n + 1)))
End

Theorem v_rel_l_simps =
  [``v_rel es (Litv l) v``, ``v_rel es (Conv cn vs) v``,
    ``v_rel es (Loc l) v``, ``v_rel es (Vectorv vs) v``,
    ``v_rel es (Env e) v``, ``v_rel es (Recclosure env funs nm) v``,
    ``v_rel es (Closure env nm x) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ

val _ = bossLib.augment_srw_ss [rewrites [v_rel_l_simps]];

Theorem v_rel_Boolv:
  v_rel es (Boolv b) v = (v = Boolv b)
Proof
  rw [Boolv_def]
QED

val _ = bossLib.augment_srw_ss [rewrites [v_rel_Boolv]];

Definition s_rel_def:
  s_rel s s' <=>
  ?es cs refs'. s' = s with <| refs := Refv cs :: refs';
    eval_state := SOME (EvalOracle es) |> /\
  LIST_REL (sv_rel (v_rel es)) s.refs refs' /\
  s.eval_state = SOME EvalDecs /\
  es.custom_do_eval = SOME do_eval_record /\
  es.generation < LENGTH es.envs
End

Definition orac_s_def:
  orac_s (SOME (EvalOracle es)) = es /\
  orac_s _ = ARB "not EvalOracle"
End

val _ = bossLib.augment_srw_ss [rewrites [orac_s_def]];

Definition es_forward_def:
  es_forward es es' <=>
  (es.custom_do_eval = SOME do_eval_record ==>
    es'.custom_do_eval = SOME do_eval_record) /\
  (LENGTH es.envs <= LENGTH es'.envs) /\
  (!env_id env. lookup_env es env_id = SOME env ==>
    lookup_env es' env_id = SOME env)
End

Theorem es_forward_refl:
  es_forward es es
Proof
  simp [es_forward_def]
QED

Theorem es_forward_trans:
  es_forward es es' /\ es_forward es' es'' ==>
  es_forward es es''
Proof
  fs [es_forward_def]
QED

Theorem v_rel_forward:
  !x y. v_rel es x y ==> es_forward es es' ==> v_rel es' x y
Proof
  ho_match_mp_tac v_rel_ind
  \\ rw []
  \\ full_simp_tac (bool_ss ++ ETA_ss) []
  \\ fs [es_forward_def]
  \\ res_tac
  \\ simp []
QED

Theorem forward_rules:
  (v_rel es x y /\ es_forward es es' ==> v_rel es' x y) /\
  (LIST_REL (v_rel es) xs ys /\ es_forward es es' ==>
    LIST_REL (v_rel es') xs ys) /\
  (env_adj_rel (v_rel es) env env' /\ es_forward es es' ==>
    env_adj_rel (v_rel es') env env') /\
  (!xs ys. LIST_REL (sv_rel (v_rel es)) xs ys /\ es_forward es es' ==>
    LIST_REL (sv_rel (v_rel es')) xs ys)
Proof
  rw []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono))
  \\ rw []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac sv_rel_mono))
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac env_adj_rel_mono_rel))
  \\ rw []
  \\ imp_res_tac v_rel_forward
QED

Definition match_result_rel_def:
  match_result_rel nerr R mr1 mr2 <=> (case mr1 of
    | No_match => mr2 = No_match
    | Match_type_error => nerr \/ mr2 = Match_type_error
    | Match x => ?y. mr2 = Match y /\ R x y)
End

Theorem store_lookup_rel:
  LIST_REL (sv_rel R) refs refs' ==>
  OPTREL (sv_rel R) (store_lookup i refs) (store_lookup i refs')
Proof
  rw [store_lookup_def, LIST_REL_EL_EQN]
  \\ simp [OPTREL_def]
QED

Theorem s_rel_store_lookup:
  s_rel s t /\ j = i + 1 /\ es = orac_s t.eval_state ==>
  OPTREL (sv_rel (v_rel es)) (store_lookup i s.refs) (store_lookup j t.refs)
Proof
  rw [s_rel_def]
  \\ drule store_lookup_rel
  \\ simp [store_lookup_def, ADD1, EL_CONS]
  \\ simp [GSYM ADD1]
QED

Theorem pmatch:
  s_rel s t /\ es = orac_s t.eval_state /\ env_adj_rel (v_rel es) env env' ==>
  (!env_c s_refs p x binds y binds'.
  s_refs = s.refs /\ env_c = env.c /\
  v_rel es x y /\
  LIST_REL ((=) ### v_rel es) binds binds' ==>
  match_result_rel T (LIST_REL ((=) ### v_rel es))
    (pmatch env_c s_refs p x binds)
    (pmatch env'.c t.refs (compile_pat p) y binds')
  ) /\
  (!env_c s_refs ps xs binds ys binds'.
  s_refs = s.refs /\ env_c = env.c /\
  LIST_REL (v_rel es) xs ys /\
  LIST_REL ((=) ### v_rel es) binds binds' ==>
  match_result_rel T (LIST_REL ((=) ### v_rel es))
    (pmatch_list env_c s_refs ps xs binds)
    (pmatch_list env'.c t.refs (MAP compile_pat ps) ys binds')
  )
Proof
  disch_tac
  \\ ho_match_mp_tac terminationTheory.pmatch_ind
  \\ rw [terminationTheory.pmatch_def, match_result_rel_def,
    quotient_pairTheory.PAIR_REL_THM, compile_pat_def]
  \\ rveq \\ fs []
  \\ fs [v_to_env_id_def, CaseEq "v", list_case_eq, option_case_eq]
  \\ fs [terminationTheory.pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [ETA_THM]
  >- (
    TOP_CASE_TAC \\ fs []
    \\ fs [option_case_eq, pair_case_eq, bool_case_eq]
    \\ rveq \\ fs []
    \\ every_case_tac
    \\ fs []
    \\ imp_res_tac env_adj_rel_nsLookup_c
    \\ fs []
    \\ res_tac
    \\ fs []
  )
  >- (
    drule s_rel_store_lookup
    \\ simp []
    \\ disch_then (qspec_then `lnum` mp_tac)
    \\ every_case_tac \\ fs []
    \\ rw [OPTREL_SOME, sv_rel_cases]
    \\ fs []
  )
  >- (
    first_x_assum (drule_then drule)
    \\ every_case_tac \\ fs []
    \\ first_x_assum (drule_then drule)
    \\ simp []
  )
QED

Triviality pmatch_use = UNDISCH_ALL pmatch |> CONJUNCT1 |> SPEC_ALL
  |> Q.INST [`binds` |-> `[]`]
  |> DISCH_ALL |> GEN_ALL
  |> SIMP_RULE list_ss []

Theorem can_pmatch_all:
  can_pmatch_all env.c s.refs pats x /\
  s_rel s t /\
  env_adj_rel (v_rel (orac_s t.eval_state)) env env' /\
  v_rel (orac_s t.eval_state) x y ==>
  can_pmatch_all env'.c t.refs (MAP compile_pat pats) y
Proof
  rw []
  \\ Induct_on `pats`
  \\ rw [can_pmatch_all_def]
  \\ drule pmatch_use
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `h` mp_tac)
  \\ simp [match_result_rel_def]
  \\ every_case_tac
  \\ fs []
  \\ rw []
  \\ simp []
QED

Theorem do_eq:
  (! x y x' y' b. do_eq x y = Eq_val b /\
  v_rel es x x' /\
  v_rel es y y' ==>
  do_eq x' y' = Eq_val b) /\
  (! xs ys xs' ys' b. do_eq_list xs ys = Eq_val b /\
  LIST_REL (v_rel es) xs xs' /\
  LIST_REL (v_rel es) ys ys' ==>
  do_eq_list xs' ys' = Eq_val b)
Proof
  ho_match_mp_tac do_eq_ind
  \\ rw [do_eq_def]
  \\ rw [do_eq_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rveq \\ fs []
  \\ fs [eq_result_case_eq, bool_case_eq]
  \\ fs []
QED

Theorem store_assign:
  store_assign lnum sv refs = SOME refs2 /\
  LIST_REL (sv_rel R) refs refs3 /\
  sv_rel R sv sv' ==>
  ?refs4.
  LIST_REL (sv_rel R) refs2 refs4 /\
  (!sv1.  store_assign (lnum + 1) sv' (sv1 :: refs3) = SOME (sv1 :: refs4))
Proof
  rw [store_assign_def, ADD1, EL_CONS]
  \\ simp [GSYM ADD1, LUPDATE_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [EVERY2_LUPDATE_same]
  \\ fs [LIST_REL_EL_EQN]
  \\ res_tac
  \\ fs [sv_rel_cases, store_v_same_type_def] \\ rveq \\ fs []
QED

Theorem store_lookup:
  LIST_REL (sv_rel R) refs refs' /\
  store_lookup n refs = SOME sv ==>
  ?sv'. sv_rel R sv sv' /\
  (!sv1. store_lookup (n + 1) (sv1 :: refs') = SOME sv')
Proof
  rw [store_lookup_def, LIST_REL_EL_EQN, GSYM ADD1]
  \\ res_tac
QED

Theorem sv_rel_l_cases =
  [``sv_rel R (Refv rv) v``, ``sv_rel R (W8array xs) v``,
        ``sv_rel R (Varray vs) v``]
  |> map (SIMP_CONV (srw_ss ()) [sv_rel_cases])
  |> map GEN_ALL |> LIST_CONJ

Theorem do_app:
  do_app (s.refs, s.ffi) op (REVERSE xs) = SOME ((refs, ffi), r) /\
  s_rel s t /\
  LIST_REL (v_rel (orac_s t.eval_state)) xs ys /\
  r <> Rerr (Rabort Rtype_error)
  ==>
  ? ref1 refs' r' es.
  es = orac_s t.eval_state /\
  do_app (t.refs, t.ffi) op (REVERSE ys) = SOME ((ref1 :: refs', ffi), r') /\
  ref1 = HD t.refs /\
  LIST_REL (sv_rel (v_rel es)) refs refs' /\
  result_rel (v_rel es) (v_rel es) r r'

Proof

  rw [s_rel_def]
  \\ fs []
  \\ last_x_assum mp_tac
  \\ simp [Once do_app_cases] \\ rw [listTheory.SWAP_REVERSE_SYM]
  \\ fs [CaseEq "ffi_result", option_case_eq] \\ rveq \\ fs []
  \\ simp [do_app_def]
  \\ simp [div_exn_v_def, sub_exn_v_def, chr_exn_v_def,
        EVERY2_refl, MEM_MAP, PULL_EXISTS]
  \\ TRY (drule_then imp_res_tac (CONJUNCT1 do_eq))
  \\ TRY (drule_then imp_res_tac store_lookup)
  \\ TRY (drule_then drule store_assign
        \\ simp [sv_rel_l_cases, PULL_EXISTS]
        \\ disch_then drule)

  \\ rw []
  \\ rw []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [PULL_EXISTS, store_alloc_def, sv_rel_l_cases, ADD1]
  \\ rveq \\ fs []

  \\ TRY (drule_then drule store_assign
        \\ simp [sv_rel_l_cases, PULL_EXISTS]
        \\ disch_then drule)


  \\ TRY (drule_then imp_res_tac v_to_char_list1)
  \\ TRY (drule_then kall_tac v_to_list1 \\ imp_res_tac v_to_list1)
  \\ TRY (drule_then kall_tac store_lookup \\ imp_res_tac store_lookup)
  \\ TRY (irule EVERY2_refl)
  \\ simp [v_rel1_l_cases, v_rel1_Boolv, v_rel1_list_to_v, LIST_REL_APPEND_EQ]

  \\ fs [PULL_EXISTS, store_alloc_def, sv_rel_l_cases]
  \\ rveq \\ fs []
  \\ simp [ADD1]

  \\ insts_tac
  \\ TRY (drule_then imp_res_tac vs_to_string1)
  \\ rveq \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rveq \\ fs []
  \\ fs [LIST_REL_REPLICATE_same]
  \\ TRY (fs [LIST_REL_EL_EQN] \\ NO_TAC)


(* well, we were doing so well here .. sort of

  EnvLookup puts us in a world of difficulties


Theorem pairarg_to_pair_map:
  (\(x, y). (f x, g y)) = (f ## g)
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem s_rel_clock:
  s_rel s t ==> s.clock = t.clock /\
    s_rel (dec_clock s) (dec_clock t)
Proof
  rw [s_rel_def]
  \\ fs [evaluateTheory.dec_clock_def]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED


Theorem compile_correct:

  (! ^s env exps s' res es t env'.
  evaluate s env exps = (s', res) /\
  s_rel s t /\
  env_adj_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ? es' t' res'.
  evaluate t env' (MAP compile_exp exps) = (t', res') /\
  s_rel s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (LIST_REL (v_rel es')) (v_rel es') res res' /\
  es_forward (orac_s t.eval_state) es')
  /\
  (! ^s env x pes err_x s' res es t env' y err_y.
  evaluate_match s env x pes err_x = (s', res) /\
  s_rel s t /\
  es = orac_s t.eval_state /\
  env_adj_rel (v_rel es) env env' /\
  v_rel es x y /\
  v_rel es err_x err_y /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_match t env' y (MAP (compile_pat ## compile_exp) pes) err_y =
    (t', res') /\
  s_rel s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (LIST_REL (v_rel es')) (v_rel es') res res' /\
  es_forward es es')
  /\
  (! ^s env decs s' res t env'.
  evaluate_decs s env decs = (s', res) /\
  s_rel s t /\
  env_adj_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_decs t env' (MAP compile_dec decs) = (t', res') /\
  s_rel s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (env_adj_rel (v_rel es')) (v_rel es') res res' /\
  es_forward (orac_s t.eval_state) es')

Proof

  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [compile_exp_def, terminationTheory.full_evaluate_def]
  \\ rveq \\ fs []

  >- (
    insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
  )

  >- (
    insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ drule_then assume_tac can_pmatch_all
    \\ insts_tac
    \\ fs [MAP_MAP_o, pairarg_to_pair_map, miscTheory.o_PAIR_MAP]
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ fs [ETA_THM, MAP_REVERSE]
    \\ insts_tac
    \\ fs [do_con_check_def, build_conv_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ drule_then drule env_adj_rel_nsLookup_c
    \\ simp []
  )

  >- (
    eval_cases_tac
    \\ drule_then drule env_adj_rel_nsLookup_v
    \\ rw []
    \\ simp []
    \\ insts_tac
  )

  >- (
    insts_tac
  )

  >- (
    (* App *)

    reverse (fs [pair_case_eq, result_case_eq] \\ rveq \\ fs [])
    >- (
      fs [MAP_REVERSE, ETA_THM]
      \\ rw [terminationTheory.evaluate_def, do_con_check_def]
      \\ insts_tac
    )
    \\ insts_tac
    \\ Cases_on `op = Opapp`

    >- (

      rveq \\ fs []
      \\ fs [ETA_THM, MAP_REVERSE, terminationTheory.evaluate_def]
      \\ imp_res_tac s_rel_clock
      \\ fs [do_opapp_def]
      \\ eval_cases_tac
      \\ fs [listTheory.SWAP_REVERSE_SYM, CaseEq "v"] \\ rveq \\ fs []
      \\ fs [listTheory.SWAP_REVERSE, miscTheory.FST_triple]
      \\ fs [find_recfun_ALOOKUP]
      \\ eval_cases_tac
      \\ insts_tac
      \\ TRY (drule (Q.ISPECL [`I ## compile_exp`, `I`]
        (GEN_ALL ALOOKUP_MAP_FST_INJ_SOME)))
      \\ simp []
      \\ rfs [EVAL ``(dec_clock s).eval_state``]
      \\ first_x_assum (q_pmatch_then `evaluate _ _ _` mp_tac)
      \\ impl_tac \\ rw [] \\ insts_tac
      \\ irule env_adj_rel_nsBind
      \\ insts_tac
      \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
      \\ irule env_adj_rel_nsBindList
      \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
      \\ simp [ELIM_UNCURRY, quotient_pairTheory.PAIR_REL_THM, EVERY2_refl]
    )

    \\ Cases_on `op = Eval`
    >- (
      fs [do_eval_res_def, terminationTheory.evaluate_def, do_con_check_def]
      \\ simp [MAP_REVERSE, ETA_THM, build_conv_def]
      \\ eval_cases_tac
      \\ insts_tac

      \\ cheat
    )
    \\ eval_cases_tac
    \\ simp [MAP_REVERSE, ETA_THM, terminationTheory.evaluate_def]



    eval_cases_tac
    \\ fs [ETA_THM]
    \\ insts_tac

    \\ first_x_assum (do_match_inst ``s_rel`` ["m", "i"])
    \\ rfs []
    \\ first_x_assum (do_match_inst ``env_rel`` ["_", "m", "i"])
    \\ rveq \\ fs []
    \\ TRY (qpat_x_assum `_ ==> _` mp_tac
      \\ (impl_tac THENL [rpt strip_tac, strip_tac]))
 
    \\ fsrw_tac [SATISFY_ss] [forward_rules]
    \\ fs []


fun do_match_inst const data cont thm = let
    val (vs, t1) = strip_forall (concl thm)
    val (lhs, _) = dest_imp t1
    val vset = HOLset.addList (empty_tmset, vs)
    val mem_vset = curry HOLset.member vset
    fun match_vars_free ("m", t) = all (not o mem_vset) (free_vars t)
      | match_vars_free _ = true
    fun inst_var ("i", t) = exists mem_vset (free_vars t)
      | inst_var _ = false
    val prems = strip_conj lhs
      |> filter (same_const const o fst o strip_comb)
      |> filter (all match_vars_free o zip data o snd o strip_comb)
      |> filter (exists inst_var o zip data o snd o strip_comb)
  in MAP_FIRST (fn prem => let
    val const = strip_comb prem |> fst
    val prem_els = strip_comb prem |> snd |> zip data
    fun matches (("m", t), t') = term_eq t t'
      | matches _ = true
    fun assum_match a = case strip_comb a of (c, xs) =>
      term_eq c const andalso all matches (zip prem_els xs)
  in FIRST_ASSUM (fn a => if assum_match (concl a)
  then let
    val fvs = FVL [concl thm, concl a] empty_tmset
    val (vs2, sub) = quantHeuristicsTools.list_variant (HOLset.listItems fvs) vs
    val thm2 = SPECL vs2 thm
    val prem2 = subst sub prem
    val els2 = strip_comb prem2 |> snd |> zip data
    fun get_subst (("i", t), t') = fst (match_term t t')
      | get_subst _ = []
    val sub2 = strip_comb (concl a) |> snd |> zip els2
      |> map get_subst |> List.concat
    val thm3 = INST sub2 thm2
    val fvs2 = FVL [concl thm3] empty_tmset
    val vs3 = filter (curry HOLset.member fvs2) vs2
    val thm4 = GENL vs3 thm3
  in cont thm4 end
  else NO_TAC)
  end) prems
  end

fun do_inst const data = first_x_assum (do_match_inst const data mp_tac)
  \\ simp [] \\ TRY disch_tac

val find_toplevel_bool = let
    fun find1 t = find_terms (fn t => type_of t = bool) t
        |> filter (not o fast_term_eq t)
    fun fvs t = FVL [t] empty_tmset
    fun is_toplevel s t = HOLset.isSubset (fvs t, s)
  in fn t => case find1 t of [] => []
    | ts => filter (is_toplevel (fvs t)) ts
  end

fun propose_subgoal_tac1 pat (asms, goal) = 
  (map find_toplevel_bool (goal :: asms)
    |> List.concat
    |> filter (can (match_term pat))
    |> MAP_FIRST (reverse o suff_tac)) (asms, goal)

fun propose_subgoal_tac pats = MAP_FIRST (Q_TAC propose_subgoal_tac1) pats



val forward_tac = MAP_FIRST (drule_then irule)
    (es_forward_trans :: IMP_CANON forward_rules)

val insts_tac = rpt (FIRST ([
      do_inst ``s_rel`` ["m", "i"],
      do_inst ``env_adj_rel`` ["_", "m", "i"],
      do_inst ``v_rel`` ["_", "m", "i"],
      CHANGED_TAC (fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, es_forward_refl] \\ rfs []),
      forward_tac,
      first_x_assum (fn t => mp_tac t \\ (impl_tac THENL
            [rpt conj_tac \\ forward_tac, disch_tac])),
      conj_tac \\ forward_tac
(*
      propose_subgoal_tac [`env_adj_rel _ _ _`, `v_rel _ _ _`]
            THENL [forward_tac, disch_tac]
*)
    ] 
    ))

val eval_cases_tac =
  fs [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
        option_case_eq, list_case_eq, exp_or_val_case_eq, match_result_case_eq]
  \\ rveq \\ fs [] 
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs [] 



