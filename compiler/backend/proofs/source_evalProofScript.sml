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
  do_eval_record f vs (orac : eval_oracle_fun) = case vs of
    | [env_id_v; decs_v] => (case (v_to_env_id env_id_v, v_to_decs decs_v) of
      | (SOME env_id, SOME decs) =>
        let i = FST (FST (orac 0)) in
        let orac' = \j. if j = 0 then ((i + 1, 0), Conv NONE [], [])
          else if j = SUC i then (env_id, Conv NONE [], decs)
          else orac j in
        SOME (env_id, orac', f decs)
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
    (!nm x. nsLookup env.c nm = SOME x ==>
        nsLookup env'.c (adj_id nm) = SOME x) /\
    (!nm x. nsLookup env.v nm = SOME x ==>
        ?y. nsLookup env'.v (adj_id nm) = SOME y /\ v_rel x y) /\
    (!mnms.
        (mnms ∈ nsDomMod env.c <=> MAP adj_mod_name mnms ∈ nsDomMod env'.c) /\
        (mnms ∈ nsDomMod env.v <=> MAP adj_mod_name mnms ∈ nsDomMod env'.v)) /\
    (!nm.
        (nm ∈ nsDom env.c <=> adj_id nm ∈ nsDom env'.c) /\
        (nm ∈ nsDom env.v <=> adj_id nm ∈ nsDom env'.v))
End

Theorem env_adj_rel_mono_rel:
  (!y z. R y z ==> R' y z) ==>
  env_adj_rel R env env' ==>
  env_adj_rel R' env env'
Proof
  simp [env_adj_rel_def] \\ metis_tac []
QED

val _ = IndDefLib.add_mono_thm env_adj_rel_mono_rel;

Theorem env_adj_rel_nsEmpty:
  env_adj_rel R <|v := nsEmpty; c := nsEmpty|> <|v := nsEmpty; c := nsEmpty|>
Proof
  rw [env_adj_rel_def]
QED

val _ = bossLib.augment_srw_ss [rewrites [env_adj_rel_nsEmpty]];

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

Theorem env_adj_rel_nsLookup_v:
  env_adj_rel R env env' /\
  nsLookup env.v id = SOME v ==>
  ?v'. nsLookup env'.v (adj_id id) = SOME v' /\ R v v'
Proof
  rw [env_adj_rel_def]
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

Theorem nsDomMod_nsAppend:
  nsDomMod (nsAppend ns1 ns2) = (nsDomMod ns1 UNION
    (nsDomMod ns2 DIFF { mnm' | TAKE 1 mnm' IN nsDomMod ns1 /\ ~ NULL mnm'}))
Proof
  rw [namespaceTheory.nsDomMod_def, EXTENSION, GSPECIFICATION, EXISTS_PROD]
  \\ Cases_on `nsLookupMod (nsAppend ns1 ns2) x`
  >- (
    fs [nsLookupMod_nsAppend_none] \\ rveq \\ fs []
    \\ Cases_on `p1` \\ fs []
    \\ Cases_on `ns1`
    \\ fs [namespaceTheory.nsLookupMod_def, option_case_eq]
  )
  >- (
    fs [nsLookupMod_nsAppend_some]
    \\ every_case_tac
    \\ Cases_on `ns1`
    \\ fs [namespaceTheory.nsLookupMod_def]
    \\ Cases_on `x` \\ fs []
  )
QED

Theorem nsLookup_NONE_nsDom:
  (nsLookup ns nm = NONE) = (~ (nm IN nsDom ns))
Proof
  cheat
QED

Theorem nsLookupMod_NONE_nsDomMod:
  (nsLookupMod ns nm = NONE) = (~ (nm IN nsDomMod ns))
Proof
  cheat
QED

Theorem id_to_mods_adj_id:
  !id. id_to_mods (adj_id id) = MAP adj_mod_name (id_to_mods id)
Proof
  Induct
  \\ simp [adj_id_def, namespaceTheory.id_to_mods_def]
QED

Theorem nsLookup_nsAppend_some_TAKE:
   ∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
      (id_to_mods id ≠ [] ⇒ nsLookupMod e1 (TAKE 1 (id_to_mods id)) = NONE))
Proof
  rw [nsLookup_nsAppend_some]
  \\ EQ_TAC \\ rw []
  \\ rw []
  \\ Cases_on `id_to_mods id` \\ fs []
  \\ Cases_on `p1` \\ fs []
  \\ Cases_on `e1` \\ fs [namespaceTheory.nsLookupMod_def]
  \\ fs [option_case_eq]
QED

Theorem env_adj_rel_extend_dec_env:
  env_adj_rel R env1 env3 /\ env_adj_rel R env2 env4 ==>
  env_adj_rel R (extend_dec_env env1 env2) (extend_dec_env env3 env4)
Proof
  rw [env_adj_rel_def, extend_dec_env_def]
  \\ simp [nsLookup_nsDom]
  \\ fs [nsLookup_nsAppend_some_TAKE]
  \\ fs [nsLookup_NONE_nsDom, nsLookupMod_NONE_nsDomMod]
  \\ rfs [id_to_mods_adj_id, MAP_TAKE]
  \\ TRY (res_tac \\ simp [RIGHT_AND_OVER_OR, EXISTS_OR_THM] \\ NO_TAC)
  \\ simp [nsDomMod_nsAppend, MAP_TAKE, NULL_EQ]
  \\ simp [EXISTS_OR_THM, GSYM nsLookup_nsDom, GSYM PULL_EXISTS]
QED

Theorem env_adj_rel_nsLift:
  env_adj_rel R <| v := vs; c := cs |> <| v := vs'; c := cs' |> ==>
  env_adj_rel R
    <| v := nsLift mn vs; c := nsLift mn cs |>
    <| v := nsLift (adj_mod_name mn) vs';
        c := nsLift (adj_mod_name mn) cs' |>
Proof
  rw [] \\ fs [env_adj_rel_def]
  \\ simp [nsDom_nsLift, nsLookup_nsLift, namespaceTheory.id_case_eq]
  \\ simp [PULL_EXISTS, adj_id_def]
  \\ simp [nsDomMod_nsLift, MAP_EQ_CONS, adj_mod_name_11, PULL_EXISTS]
  \\ Cases
  \\ simp [adj_id_def, adj_mod_name_11]
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
  es.custom_do_eval = SOME (do_eval_record (MAP compile_dec)) /\
  es.generation < LENGTH es.envs
End

Definition orac_s_def:
  orac_s (SOME (EvalOracle es)) = es /\
  orac_s _ = ARB "not EvalOracle"
End

val _ = bossLib.augment_srw_ss [rewrites [orac_s_def]];

Definition es_forward_def:
  es_forward es es' <=>
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

Theorem pat_bindings_compile_pat:
  (!p bs. pat_bindings (compile_pat p) bs = pat_bindings p bs)
Proof
  recInduct compile_pat_ind
  \\ rw [compile_pat_def, astTheory.pat_bindings_def]
  \\ qid_spec_tac `bs`
  \\ Induct_on `ps`
  \\ rw [compile_pat_def, astTheory.pat_bindings_def]
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
  ho_match_mp_tac terminationTheory.do_eq_ind
  \\ rw [terminationTheory.do_eq_def]
  \\ rw [terminationTheory.do_eq_def]
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

Theorem v_rel_list_to_v:
  !xs ys. v_rel es (list_to_v xs) (list_to_v ys)
  <=>
  LIST_REL (v_rel es) xs ys
Proof
  Induct
  \\ simp []
  >- (
    Cases
    \\ simp [list_to_v_def]
  )
  >- (
    gen_tac
    \\ Cases
    \\ simp [list_to_v_def]
  )
QED

Theorem v_to_list:
  ! x y xs. v_to_list x = SOME xs /\
  v_rel es x y ==>
  ?ys. v_to_list y = SOME ys /\
  LIST_REL (v_rel es) xs ys
Proof
  recInduct terminationTheory.v_to_list_ind
  \\ rw [terminationTheory.v_to_list_def]
  \\ fs [terminationTheory.v_to_list_def, option_case_eq]
  \\ rveq \\ fs []
  \\ res_tac
  \\ simp []
QED

Theorem v_to_char_list:
  ! x y xs. v_to_char_list x = SOME xs /\
  v_rel es x y ==>
  v_to_char_list y = SOME xs
Proof
  recInduct terminationTheory.v_to_char_list_ind
  \\ rw [terminationTheory.v_to_char_list_def]
  \\ fs [terminationTheory.v_to_char_list_def, option_case_eq]
  \\ rveq \\ fs []
QED

Theorem vs_to_string:
  !xs ys s. vs_to_string xs = SOME s /\
  LIST_REL (v_rel es) xs ys ==>
  vs_to_string ys = SOME s
Proof
  recInduct terminationTheory.vs_to_string_ind
  \\ rw [terminationTheory.vs_to_string_def]
  \\ fs [option_case_eq]
  \\ rveq \\ fs []
  \\ simp [terminationTheory.vs_to_string_def]
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
  \\ TRY (drule_then imp_res_tac v_to_char_list)
  \\ TRY (drule_then kall_tac v_to_list \\ imp_res_tac v_to_list)
  \\ TRY (drule_then imp_res_tac vs_to_string)
  \\ TRY (drule_then drule store_assign
        \\ simp [sv_rel_l_cases, PULL_EXISTS]
        \\ disch_then drule)
  \\ rw [EVERY2_LUPDATE_same, v_rel_list_to_v, LIST_REL_APPEND_EQ]
  \\ rw []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [PULL_EXISTS, store_alloc_def, sv_rel_l_cases, ADD1]
  \\ rveq \\ fs []
  \\ TRY (irule EVERY2_refl \\ simp [MEM_MAP, EXISTS_PROD, PULL_EXISTS])
  \\ TRY (drule_then (drule_then (q_pmatch_then `store_assign _ _` mp_tac))
        store_assign
        \\ rw [EVERY2_LUPDATE_same])
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [LIST_REL_REPLICATE_same, EVERY2_LUPDATE_same, LIST_REL_APPEND_EQ]
  \\ TRY (fs [LIST_REL_EL_EQN] \\ NO_TAC)
QED

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

Triviality build_tdefs_helper:
  <| v := nsEmpty; c := nsAppend a b |> = extend_dec_env
      <| v := nsEmpty; c := a |> <| v := nsEmpty; c := b |>
Proof
  simp [extend_dec_env_def]
QED

Theorem build_tdefs:
  !tds n n2. n = n2 ==>
    env_adj_rel R
        <|v := nsEmpty; c := build_tdefs n tds|>
        <|v := nsEmpty; c := build_tdefs n2
                (MAP (I ## I ## MAP (I ## MAP compile_type)) tds)|>
Proof
  Induct
  \\ simp [build_tdefs_def, FORALL_PROD]
  \\ rw []
  \\ simp [build_tdefs_helper]
  \\ irule env_adj_rel_extend_dec_env
  \\ simp [build_constrs_def, MAP_MAP_o, o_DEF, ELIM_UNCURRY]
  \\ simp [env_adj_rel_def, MEM_MAP, PULL_EXISTS]
  \\ simp [nsLookup_alist_to_ns_some, PULL_EXISTS, adj_id_def]
  \\ Cases
  \\ simp [adj_id_def]
QED

Theorem v_to_decs:
  v_to_decs x = SOME decs /\
  v_rel es x y ==>
  v_to_decs y = SOME decs
Proof
  cheat
QED

Theorem do_eval:
  do_eval (REVERSE xs) s.eval_state = SOME (env, decs, es) /\
  s_rel s t /\
  LIST_REL (v_rel (orac_s t.eval_state)) xs ys ==>
  ? x1 x2 env' es'.
  do_eval (REVERSE ys) t.eval_state = SOME (env', MAP compile_dec decs, es') /\
  xs = [x1; x2] /\
  es_forward (orac_s t.eval_state) (orac_s es') /\
  env_adj_rel (v_rel (orac_s es')) env env' /\
  s_rel (s with eval_state := es) (t with eval_state := es')
Proof
  rw []
  \\ fs [do_eval_def, s_rel_def] \\ fs []
  \\ fs [list_case_eq, v_case_eq, option_case_eq]
  \\ fs [listTheory.SWAP_REVERSE_SYM]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ imp_res_tac v_to_decs
  \\ simp [do_eval_record_def, state_component_equality]
  \\ simp [add_env_generation_def]
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, lem_listTheory.list_index_def]
    \\ simp [option_case_eq, EL_APPEND_EQN]
  )
  >- (
    imp_res_tac forward_rules
    \\ simp []
  )
QED

Theorem fetch_eval:
  nsLookup env.v (Long compiler_module_name (Short "eval")) =
  SOME (Closure ARB "x" (eval_fun_body ARB.filename))
Proof
  cheat
QED

Theorem fetch_state:
  nsLookup ARB.v (Short "state") = SOME (Loc 0)
Proof
  cheat
QED

(* so, assumptions we need:
   1. compiler prog evals to some definite collection of things
   2. those things include "compiler" and "load"
   3. "compiler" given a env_id/s/decs triple executes statelessly
      and returns a bytes/words/s triple
   4. "load" .. yeah let's come back to that.
   things we need to show:
   1. the world "eval" is called from has the compiler module,
      and "state", and the list constructors, and maybe some other
      things
   2. "eval" can safely call "compiler" and "load"
   3. that's it?
*)

Definition compiler_contents_def:
  compiler_contents cfg ffi = (case prim_sem_env ffi of
    | NONE => NONE
    | SOME (st, env) => (case evaluate_decs st env cfg.compiler_decs of
        | (st', Rval env') => SOME (st', env')
        | _ => NONE
  ))
End

Definition compiler_decs_assumption_def:
  compiler_decs_assumption cfg ffi <=>
  ?st env comp load.
  compiler_contents cfg ffi = SOME (st, env) /\
     nsLookup env.v (Short "compiler") = SOME comp /\
     nsLookup env.v (Short "load") = SOME load
End


Theorem nsLookup_Long_mod:
  nsLookup ns (Long mnm id) = case nsLookupMod ns [mnm] of
    | NONE => NONE
    | SOME ns' => nsLookup ns' id
Proof
  Cases_on `ns`
  \\ simp [namespaceTheory.nsLookupMod_def, namespaceTheory.nsLookup_def]
  \\ CASE_TAC \\ simp []
QED

(* this is all confused about the question of how to set things up
   to be compatible with translator theorems about the compiler
   function.
Theorem eval_eval:

  s_rel s t /\
  nsLookup vs (Short "state") = SOME (Loc 0) /\
  (if LENGTH (orac_s t.eval_state).envs <= 1
    then HD t.refs = Refv (list_to_v [])
    else ? compiler_st. HD t.refs = Refv (list_to_v [compiler_st])) /\
  nsLookup env.c (Short "::") = SOME (2,TypeStamp "::" list_type_num) /\
  nsLookupMod vs ["Compiler"] =

  ==>
  ? t'.
  evaluate t (env with v := nsBind "x" (Conv NONE [env_id; decs]) vs)
    [eval_fun_body fname]
    = (t', foo) /\
  s_rel s t'

Proof



  rw [s_rel_def]
  \\ simp [eval_fun_body_def, Once mk_matches_def]
  \\ simp [terminationTheory.evaluate_def, do_app_def, store_lookup_def]
  \\ simp [astTheory.pat_bindings_def]
  \\ fs [list_to_v_def, can_pmatch_all_def, terminationTheory.pmatch_def, same_type_def]
  \\ simp [same_ctor_def]

  >- cheat
  \\ simp [eval_fun_body_def, Once mk_matches_def]
  \\ simp [terminationTheory.evaluate_def, can_pmatch_all_def, terminationTheory.pmatch_def,
        astTheory.pat_bindings_def]
  \\ simp [eval_fun_body_def, Once mk_matches_def]
  \\ simp [terminationTheory.evaluate_def, can_pmatch_all_def, terminationTheory.pmatch_def,
        astTheory.pat_bindings_def, do_con_check_def, build_conv_def]


  EVAL_TAC
*)

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
  \\ fs [compile_exp_def, compile_dec_def, terminationTheory.full_evaluate_def]
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
      \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
      \\ drule_then (drule_then drule) do_eval
      \\ rw []
      \\ fs [MAP_REVERSE]
      \\ simp [fetch_eval, do_opapp_def]
      \\ simp [eval_fun_def, Once mk_matches_def, terminationTheory.evaluate_def]
      \\ simp [fetch_state, do_app_def]

      \\ drule_then assume_tac s_rel_clock

      \\ fs [bool_case_eq] \\ rveq \\ fs []
      \\ simp [do_opapp_def]

      \\ eval_cases_tac
      \\ insts_tac

      \\ fs [ETA_THM, terminationTheory.evaluate_def]

      (* Eval cheated *)
      \\ cheat
    )
    \\ eval_cases_tac
    \\ simp [MAP_REVERSE, ETA_THM, terminationTheory.evaluate_def]
    \\ drule_then assume_tac do_app
    \\ insts_tac
    \\ first_x_assum drule
    \\ rw []
    \\ fs [MAP_REVERSE]
    \\ fs [s_rel_def] \\ rveq \\ fs []
    \\ simp [state_component_equality]
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [do_log_def]
    \\ eval_cases_tac
    \\ rveq \\ fs []
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [do_if_def]
    \\ eval_cases_tac
    \\ insts_tac
   )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ drule_then assume_tac can_pmatch_all
    \\ insts_tac
    \\ fs [MAP_MAP_o, pairarg_to_pair_map, miscTheory.o_PAIR_MAP]
    \\ fs [bind_exn_v_def]
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ first_x_assum (q_pmatch_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\  insts_tac
    \\ simp [namespaceTheory.nsOptBind_def]
    \\ CASE_TAC \\ fs []
    \\ insts_tac
    \\ irule env_adj_rel_nsBind
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [miscTheory.FST_triple, MAP_MAP_o]
    \\ fs [GSYM pairarg_to_pair_map, ELIM_UNCURRY, o_DEF, ETA_THM]
    \\ first_x_assum (q_pmatch_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_adj_rel_nsBindList
    \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
    \\ simp [quotient_pairTheory.PAIR_REL_THM, ELIM_UNCURRY]
    \\ simp [GSYM pairarg_to_pair_map, ELIM_UNCURRY, EVERY2_refl]
  )

  >- (
    insts_tac
  )

  >- (
    fs [bool_case_eq]
    \\ insts_tac
    \\ drule_then (q_pmatch_then `pmatch _ _ _ _ _` mp_tac) pmatch_use
    \\ rpt (disch_then drule)
    \\ eval_cases_tac
    \\ fs [match_result_rel_def, pat_bindings_compile_pat]
    \\ rw []
    \\ insts_tac
    \\ first_x_assum (q_pmatch_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ simp [nsAppend_to_nsBindList]
    \\ irule env_adj_rel_nsBindList
    \\ simp [nsAppend_to_nsBindList]
  )

  >- (
    insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ first_x_assum (q_pmatch_then `evaluate_decs _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ TRY (irule env_adj_rel_extend_dec_env)
    \\ insts_tac
    \\ TRY strip_tac
    \\ fs [combine_dec_result_def]
    \\ every_case_tac \\ fs []
    \\ rw [] \\ insts_tac
    \\ simp [GSYM (SIMP_RULE (srw_ss ()) [] extend_dec_env_def)]
    \\ TRY (irule env_adj_rel_extend_dec_env)
    \\ insts_tac
  )

  >- (
    simp [pat_bindings_compile_pat]
    \\ fs [bool_case_eq, pair_case_eq, result_case_eq]
    \\ insts_tac
    \\ simp_tac bool_ss [GSYM (Q.ISPEC `compile_pat`
        (Q.ISPEC `pmatch _ _` o_THM))]
    \\ drule_then (q_pmatch_then `pmatch _ _ _ _ _` assume_tac) pmatch_use
    \\ eval_cases_tac
    \\ insts_tac
    \\ every_case_tac \\ fs [match_result_rel_def, bind_exn_v_def]
    \\ simp [alist_to_ns_to_bind2]
    \\ irule env_adj_rel_nsBindList
    \\ simp []
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [miscTheory.FST_triple, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_adj_rel_nsBindList
    \\ simp []
    \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
    \\ simp [quotient_pairTheory.PAIR_REL_THM, ELIM_UNCURRY]
    \\ simp [GSYM pairarg_to_pair_map, ELIM_UNCURRY, EVERY2_refl]
  )

  >- (
    eval_cases_tac
    \\ fs [EVERY_MEM, FORALL_PROD, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
        terminationTheory.check_dup_ctors_thm]
    \\ fs [s_rel_def, state_component_equality]
    \\ simp [build_tdefs, es_forward_refl]
    \\ rw []
    \\ res_tac
  )

  >- (
    insts_tac
  )

  >- (
    (* Denv *)
    eval_cases_tac
    \\ fs [declare_env_def, s_rel_def]
    \\ rveq \\ fs []
    \\ rveq \\ fs []
    \\ simp [lem_listTheory.list_index_def]
    \\ simp [state_component_equality]
    \\ qmatch_goalsub_abbrev_tac `es_forward es es'`
    \\ qsuff_tac `es_forward es es'`
    >- (
      rw [] \\ insts_tac
      \\ simp [nsSing_eq_bind]
      \\ irule env_adj_rel_nsBind
      \\ simp [v_to_env_id_def, v_to_nat_def, nat_to_v_def]
      \\ fs [markerTheory.Abbrev_def, lookup_env_def,
            lem_listTheory.list_index_def, EL_LUPDATE, EL_APPEND_EQN]
      \\ rveq \\ fs []
      \\ insts_tac
    )
    >- (
      fs [markerTheory.Abbrev_def, es_forward_def, FORALL_PROD]
      \\ simp [lookup_env_def, lem_listTheory.list_index_def, option_case_eq]
      \\ simp [EL_LUPDATE]
      \\ rw [EL_APPEND_EQN]
    )
  )

  >- (
    insts_tac
    \\ fs [s_rel_def, state_component_equality]
    \\ simp [env_adj_rel_def, adj_id_def]
    \\ Cases \\ simp [adj_id_def]
  )

  >- (
    eval_cases_tac
    \\ fs [ETA_THM]
    \\ insts_tac
    \\ irule env_adj_rel_nsLift
    \\ simp []
  )

  >- (
    eval_cases_tac
    \\ fs [ETA_THM]
    \\ insts_tac
    \\ first_x_assum (q_pmatch_then `evaluate_decs _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ irule env_adj_rel_extend_dec_env
    \\ insts_tac
  )
QED



(* some lighter stuff, show that the fast compiler is the same. *)

Theorem has_res_mod_name:
  ~ has_res_mod_name m ==> adj_mod_name m = m
Proof
  rw [has_res_mod_name_def, adj_mod_name_def]
QED

Theorem must_adj_id:
  !id. ~ must_adj_id id ==> adj_id id = id
Proof
  Induct
  \\ fs [must_adj_id_def, adj_id_def, has_res_mod_name]
QED

Theorem must_adj_pat:
  ! pat. ~ must_adj_pat pat ==> compile_pat pat = pat
Proof
  recInduct compile_pat_ind
  \\ rw [must_adj_pat_def, compile_pat_def]
  \\ fs [miscTheory.MAP_EQ_ID, EVERY_MEM]
  \\ every_case_tac \\ simp [must_adj_id]
QED

Theorem must_adj_exp:
  ! exp. ~ must_adj_exp exp ==> compile_exp exp = exp
Proof
  recInduct compile_exp_ind
  \\ rw [must_adj_exp_def, compile_exp_def, must_adj_id]
  \\ fs [miscTheory.MAP_EQ_ID, EVERY_MEM, FORALL_PROD]
  \\ rw [] \\ res_tac
  \\ simp [must_adj_pat]
  \\ every_case_tac \\ simp [must_adj_id]
QED

Theorem must_adj_type:
  ! ty. ~ must_adj_type ty ==> compile_type ty = ty
Proof
  recInduct compile_type_ind
  \\ rw [must_adj_type_def, compile_type_def, must_adj_id]
  \\ fs [miscTheory.MAP_EQ_ID, EVERY_MEM, FORALL_PROD]
QED

Theorem must_adj_dec:
  ! dec. ~ must_adj_dec dec ==> compile_dec dec = dec
Proof
  recInduct compile_dec_ind
  \\ rw [must_adj_dec_def, compile_dec_def, must_adj_id,
    must_adj_exp, has_res_mod_name, must_adj_type, must_adj_pat]
  \\ fs [miscTheory.MAP_EQ_ID, EVERY_MEM, FORALL_PROD]
  \\ rw [] \\ res_tac
  \\ simp [must_adj_type, must_adj_exp]
QED

Theorem fast_compile_dec:
  fast_compile_dec dec = compile_dec dec
Proof
  rw [fast_compile_dec_def, must_adj_dec]
QED

Definition is_record_def:
  is_record f es = case es of
    | SOME (EvalOracle s) => s.custom_do_eval = SOME (do_eval_record f)
    | _ => F
End

Definition insert_oracle_def:
  insert_oracle f orac es = case es of
    | SOME (EvalOracle s) => SOME (EvalOracle (s with <|
        custom_do_eval := NONE ;
        oracle := (I ## (I ## f)) o shift_seq (FST (FST (s.oracle 0))) orac |>))
    | _ => es
End

Definition orac_agrees_def:
  orac_agrees orac es = case es of
    | SOME (EvalOracle s) =>
      (!j. j < FST (FST (s.oracle 0)) ==> orac j = s.oracle (j + 1))
    | _ => F
End

Definition record_forward_def:
  record_forward es es' = (case es of
    | SOME (EvalOracle s) => ?s'. es' = SOME (EvalOracle s') /\
          (FST (FST (s.oracle 0)) <= FST (FST (s'.oracle 0))) /\
          (!j. 0 < j /\ j < FST (FST (s.oracle 0)) + 1 ==> s'.oracle j = s.oracle j)
    | _ => ~ (?s'. es' = SOME (EvalOracle s'))
  )
End

Theorem record_forward_refl:
  record_forward es es
Proof
  simp [record_forward_def] \\ every_case_tac \\ simp []
QED

Theorem record_forward_trans:
  record_forward es1 es2 /\ record_forward es2 es3 ==>
  record_forward es1 es3
Proof
  simp [record_forward_def] \\ every_case_tac \\ rw []
QED

Theorem orac_agrees_backward:
  orac_agrees orac es2 /\ record_forward es1 es2 ==>
  orac_agrees orac es1
Proof
  rw [orac_agrees_def, record_forward_def]
  \\ every_case_tac \\ fs []
QED

Theorem insert_do_eval:

  do_eval vs es = SOME (env, decs, es') /\
  is_record f es ==>
  is_record f es' /\
  do_eval vs (insert_oracle f orac es) = SOME (env, decs,
    insert_oracle f orac es')

Proof

  rw [is_record_def, Once do_eval_def]
  \\ fs [option_case_eq, eval_state_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ simp [add_env_generation_def]
  \\ rveq \\ fs []
  \\ fs [do_eval_record_def, list_case_eq, option_case_eq] \\ rveq \\ fs []
  \\ simp [do_eval_def, insert_oracle_def, shift_seq_def]
  \\ rpt (pairarg_tac \\ fs [])

  \\ every_case_tac \\ fs []
  \\ simp [Once do_eval_def, insert_oracle_def]
  \\ rpt (CASE_TAC \\ fs [])
  \\ simp [do_eval_def, do_eval_record_def, ELIM_UNCURRY]

  \\ rpt (CASE_TAC \\ fs [])

  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ simp [option_case_eq, pair_case_eq]

  \\ csimp [do_eval_record_def, option_case_eq, list_case_eq]


Theorem setup_oracle:

  (! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record f s.eval_state
  ==>
  is_record f s'.eval_state /\
  record_forward s.eval_state s'.eval_state /\
  (orac_agrees orac s'.eval_state ==>
  evaluate (s with eval_state updated_by insert_oracle f orac) env exps =
  (s' with eval_state updated_by insert_oracle f orac, res)
  ))
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record f s.eval_state
  ==>
  is_record f s'.eval_state /\
  record_forward s.eval_state s'.eval_state /\
  (
  orac_agrees orac s'.eval_state ==>
  evaluate_match (s with eval_state updated_by insert_oracle f orac)
    env x pes err_x =
  (s' with eval_state updated_by insert_oracle f orac, res)
  ))
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record f s.eval_state
  ==>
  is_record f s'.eval_state /\
  record_forward s.eval_state s'.eval_state /\
  (orac_agrees orac s'.eval_state ==>
  evaluate_decs (s with eval_state updated_by insert_oracle f orac) env decs =
  (s' with eval_state updated_by insert_oracle f orac, res)
  ))

Proof

  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [compile_exp_def, compile_dec_def, terminationTheory.full_evaluate_def]
  \\ rveq \\ fs []
  \\ simp [record_forward_refl]

  >- (
    eval_cases_tac
    \\ fsrw_tac [SATISFY_ss] [record_forward_trans, Q.ISPEC `(a, b)` EQ_SYM_EQ]
    \\ simp [record_forward_refl]
    \\ disch_tac
    \\ fs []
    \\ imp_res_tac orac_agrees_backward
    \\ fs []
  )

  >- (

    (* App *)
    fs [pair_case_eq, result_case_eq] \\ rveq \\ fs []
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    >- (
      (* Opapp *)
      eval_cases_tac
      \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] \\ rveq \\ fs []
      \\ fs [dec_clock_def]
      \\ fsrw_tac [SATISFY_ss] [record_forward_trans]
      \\ disch_tac
      \\ fs []
      \\ imp_res_tac orac_agrees_backward
      \\ fs []
    )
    >- (

      (* Eval *)
      fs [do_eval_res_def, Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq] \\ rveq \\ fs []
      \\ fs [option_case_eq] \\ rveq \\ fs []

  )





(* Tools *)

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
      CHANGED_TAC (rveq \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, es_forward_refl]
            \\ rfs []),
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



