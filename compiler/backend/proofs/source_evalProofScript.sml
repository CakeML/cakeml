(*
  Proofs that the eval mode of the source semantics can
  be switched to one that includes an oracle.
*)
Theory source_evalProof
Ancestors
  ast[qualified] string[qualified] semantics
  semanticPrimitivesProps namespaceProps semanticPrimitives
  evaluateProps evaluate
Libs
  preamble experimentalLib

val _ = temp_delsimps ["getOpClass_def"]

(* The things the translator is expected to produce from the
   compiler definition etc. *)

Datatype:
  compiler_instance = <|
    compiler_fun : ((num # num) # 'config # dec list) ->
        ('config # word8 list # word64 list) option ;
    config_v : 'config -> v ;
    config_dom : 'config set ;
    decs_v : dec list -> v ;
    decs_dom : (dec list) set ;
    init_state : 'config
  |>
End

Definition v_rel_abs:
  v_fun_abs fun_dom fun_v v = (some x. fun_v x = v /\ x IN fun_dom)
End

Definition mk_compiler_fun_from_ci_def:
  mk_compiler_fun_from_ci ci (env_id, cfg_v, decs) =
    OPTION_BIND (v_fun_abs ci.config_dom ci.config_v cfg_v) (\cfg.
    OPTION_BIND (ci.compiler_fun (env_id, cfg, decs)) (\(cfg2, bs, ws).
    SOME (ci.config_v cfg2, bs, ws)))
End

Overload ci_comp[local] = ``mk_compiler_fun_from_ci``;

Definition mk_init_eval_state_def:
  mk_init_eval_state ci = EvalDecs <|
    compiler := mk_compiler_fun_from_ci ci ;
    decode_decs := v_fun_abs ci.decs_dom ci.decs_v ;
    env_id_counter := (0, 0, 1) ;
    compiler_state := ci.config_v ci.init_state
  |>
End

(* an instance of custom_do_eval that behaves as much as possible
   like the no-oracle semantics *)

Definition v_to_nat_def:
  v_to_nat v = case v of
   | (Litv (IntLit i)) => (if 0 <= i then SOME (Num i) else NONE)
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
  do_eval_record ci vs (orac : eval_oracle_fun) = case vs of
    | [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] =>
      let ((i, _), st, _) = orac 0 in
      (case (v_to_env_id env_id_v, v_fun_abs ci.decs_dom ci.decs_v decs_v) of
      | (SOME env_id, SOME decs) =>
        if compiler_agrees (mk_compiler_fun_from_ci ci)
            (env_id, st_v, decs) (st_v2, bs_v, ws_v) /\ st_v = st
        then
        let orac' = \j. if j = 0 then ((i + 1, 0), st_v2, [])
          else if j = SUC i then (env_id, st, decs)
          else orac j in SOME (env_id, orac', decs)
        else NONE
      | _ => NONE
      )
    | _ => NONE
End

(* a somewhat generic env rel *)

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

val _ = IndDefLib.add_mono_thm env_rel_mono_rel;

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
  \\ fs [namespaceTheory.nsBindList_def]
  \\ irule env_rel_add_nsBind
  \\ simp []
QED

Theorem env_rel_nsLift:
  env_rel R (env with <| v := v; c := c |>)
    (env' with <| v := v'; c := c' |>) ==>
  env_rel R (env with <| v := nsLift mn v; c := nsLift mn c |>)
    (env' with <| v := nsLift mn v'; c := nsLift mn c' |>)
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

val _ = bossLib.augment_srw_ss [rewrites (CONJUNCTS env_rel_nsEmpty)];

Theorem env_rel_nsAppend:
  env_rel R (env with v := a) (env' with v := c) /\
  env_rel R (env with v := b) (env' with v := d) ==>
  env_rel R (env with <| v := nsAppend a b |>)
    (env' with <| v := nsAppend c d |>)
Proof
  rw [env_rel_def, namespacePropsTheory.nsDom_nsAppend_equal]
  \\ fs [Q.ISPEC `nsDom ns` EXTENSION, nsLookup_nsDom]
  \\ fs [nsLookup_nsAppend_some]
  \\ res_tac \\ fs []
QED

Theorem env_rel_extend_dec_env:
  env_rel R env1 env2 /\ env_rel R env3 env4 ==>
  env_rel R (extend_dec_env env1 env3) (extend_dec_env env2 env4)
Proof
  rw [extend_dec_env_def]
  \\ irule env_rel_nsAppend
  \\ fs [env_rel_def]
  \\ rw [] \\ res_tac
QED

Theorem env_rel_nsLookup_v:
  env_rel R env env' /\ nsLookup env.v id = SOME v ==>
  ?v'. nsLookup env'.v id = SOME v' /\ R v v'
Proof
  rw [env_rel_def]
  \\ fs [Q.ISPEC `nsDom ns` EXTENSION, nsLookup_nsDom]
  \\ res_tac
  \\ fs []
QED

Theorem env_rel_nsLookup_c[local]:
  env_rel R env env' /\ nsLookup env.c id = r ==>
  env'.c = env.c
Proof
  rw [env_rel_def]
QED


(* various trivia *)

Theorem alist_to_ns_to_bind2[local] = GEN_ALL nsAppend_to_nsBindList
    |> Q.SPEC `nsEmpty`
    |> REWRITE_RULE [namespacePropsTheory.nsAppend_nsEmpty]

Theorem nsSing_eq_bind[local] = namespaceTheory.nsSing_def
  |> REWRITE_RULE [GSYM namespaceTheory.nsBind_def,
    GSYM namespaceTheory.nsEmpty_def]

Theorem pair_CASE_eq_pairarg[local]:
  pair_CASE p f = (\ (x, y). f x y) p
Proof
  Cases_on `p` \\ simp []
QED

val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);

(* first step. switch over to recording semantics and move envs
   out of Env values and into the state *)

Inductive v_rel:
  (!env'. v_to_env_id v = SOME id /\ lookup_env es id = SOME env' /\
        env_rel (v_rel es) env env' ==>
    v_rel es (Env env id) v) /\
  (LIST_REL (v_rel es) xs ys ==>
    v_rel es (Vectorv xs) (Vectorv ys)) /\
  (LIST_REL (v_rel es) xs ys ==>
    v_rel es (Conv stmp xs) (Conv stmp ys)) /\
  (env_rel (v_rel es) env env' ==>
    v_rel es (Closure env nm x) (Closure env' nm x)) /\
  (env_rel (v_rel es) env env' ==>
    v_rel es (Recclosure env funs nm) (Recclosure env' funs nm)) /\
  (v_rel es (Litv l) (Litv l)) /\
  (v_rel es (Loc br n) (Loc br n))
End

Theorem v_rel_l_simps =
  [“v_rel es (Litv l) v”, “v_rel es (Conv cn vs) v”,
    “v_rel es (Loc b l) v”, “v_rel es (Vectorv vs) v”,
    “v_rel es (Env e id) v”, “v_rel es (Recclosure env funs nm) v”,
    “v_rel es (Closure env nm x) v”
    ]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ

Theorem v_rel_Boolv:
  v_rel es (Boolv b) v = (v = Boolv b)
Proof
  rw [Boolv_def, v_rel_l_simps]
QED

val _ = bossLib.augment_srw_ss [rewrites [v_rel_l_simps, v_rel_Boolv]];

Definition recorded_orac_wf_def:
  recorded_orac_wf compiler (orac : eval_oracle_fun) <=>
  (0 < FST (FST (orac 0)) ==>
    ?r. compiler (orac (FST (FST (orac 0)))) = SOME r /\
        FST (SND (orac 0)) = FST r) /\
  (!j. j < FST (FST (orac 0)) /\ 0 < j ==>
    ?r. compiler (orac j) = SOME r /\ FST (SND (orac (j + 1))) = FST r)
End

Definition s_rel_def:
  s_rel ci s s' <=>
  ? dec_s orac_s refs'. s' = s with <| refs := refs';
    eval_state := SOME (EvalOracle orac_s) |> /\
  LIST_REL (sv_rel (v_rel orac_s)) s.refs refs' /\
  s.eval_state = SOME (EvalDecs dec_s) /\
  orac_s.custom_do_eval = do_eval_record ci /\
  dec_s.compiler_state = (FST (SND (orac_s.oracle 0))) /\
  dec_s.decode_decs = v_fun_abs ci.decs_dom ci.decs_v /\
  dec_s.compiler = mk_compiler_fun_from_ci ci /\
(*
  (0 < FST (FST (orac_s.oracle 0)) ==>
    (FST (SND (orac_s.oracle 1))) = init_eds.compiler_state) /\
*)
  (0 = FST (FST (orac_s.oracle 0)) ==>
    dec_s.compiler_state = ci.config_v ci.init_state) /\
  (0 < FST (FST (orac_s.oracle 0)) ==>
    FST (SND (orac_s.oracle 1)) = ci.config_v ci.init_state) /\
  dec_s.env_id_counter = (orac_s.generation,
        LENGTH (EL orac_s.generation orac_s.envs), LENGTH orac_s.envs) /\
  orac_s.generation < LENGTH orac_s.envs /\
  recorded_orac_wf (mk_compiler_fun_from_ci ci) orac_s.oracle
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
  (env_rel (v_rel es) env env' /\ es_forward es es' ==>
    env_rel (v_rel es') env env') /\
  (!xs ys. LIST_REL (sv_rel (v_rel es)) xs ys /\ es_forward es es' ==>
    LIST_REL (sv_rel (v_rel es')) xs ys)
Proof
  rw []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono))
  \\ rw []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac sv_rel_mono))
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac env_rel_mono_rel))
  \\ rw []
  \\ imp_res_tac v_rel_forward
QED

(* a stronger notion that applies end-to-end over evaluate/evaluate_decs,
   where the generation stack will match at either end and the previous
   generations will be untouched. *)
Definition es_stack_forward_def:
  es_stack_forward es es' <=>
  es'.generation = es.generation /\
  (!j. j < es.generation ==> EL j es'.envs = EL j es.envs)
End

Theorem es_stack_forward_refl:
  es_stack_forward es es
Proof
  simp [es_stack_forward_def]
QED

Theorem es_stack_forward_trans:
  es_stack_forward es1 es2 /\ es_stack_forward es2 es3 ==>
  es_stack_forward es1 es3
Proof
  simp [es_stack_forward_def]
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

val ci = mk_var ("ci", ``: 'cfg compiler_instance``);

Theorem s_rel_store_lookup:
  s_rel ^ci s t /\ j = i /\ es = orac_s t.eval_state ==>
  OPTREL (sv_rel (v_rel es)) (store_lookup i s.refs) (store_lookup j t.refs)
Proof
  rw [s_rel_def]
  \\ drule store_lookup_rel
  \\ simp [store_lookup_def, ADD1, EL_CONS]
  \\ simp [GSYM ADD1]
QED

Theorem v_to_nat_SOME:
  v_to_nat v = SOME n ==>
  v = nat_to_v n
Proof
  rw [v_to_nat_def, v_case_eq, astTheory.lit_case_eq, nat_to_v_def]
  \\ rveq \\ fs []
  \\ fs [GSYM integerTheory.INT_OF_NUM]
QED

Theorem v_to_env_id_SOME:
  v_to_env_id v = SOME id ==>
  v = Conv NONE [nat_to_v (FST id); nat_to_v (SND id)]
Proof
  rw [v_to_env_id_def, v_case_eq, list_case_eq, option_case_eq]
  \\ imp_res_tac v_to_nat_SOME
  \\ simp []
QED

Theorem pmatch:
  s_rel ^ci s t /\ es = orac_s t.eval_state /\ env_rel (v_rel es) env env' ==>
  (!env_c s_refs p x binds y binds'.
  s_refs = s.refs /\ env_c = env.c /\
  v_rel es x y /\
  LIST_REL ((=) ### v_rel es) binds binds' ==>
  match_result_rel T (LIST_REL ((=) ### v_rel es))
    (pmatch env_c s_refs p x binds)
    (pmatch env'.c t.refs p y binds')
  ) /\
  (!env_c s_refs ps xs binds ys binds'.
  s_refs = s.refs /\ env_c = env.c /\
  LIST_REL (v_rel es) xs ys /\
  LIST_REL ((=) ### v_rel es) binds binds' ==>
  match_result_rel T (LIST_REL ((=) ### v_rel es))
    (pmatch_list env_c s_refs ps xs binds)
    (pmatch_list env'.c t.refs ps ys binds')
  )
Proof
  disch_tac
  \\ ho_match_mp_tac pmatch_ind
  \\ rw [pmatch_def, match_result_rel_def]
  \\ rveq \\ fs []
  \\ imp_res_tac v_to_env_id_SOME
  \\ fs [pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [ETA_THM]
  >- (
    fs [PULL_FORALL]
    \\ first_x_assum (first_assum o mp_then (Pat `LIST_REL _ _ _`) mp_tac)
    \\ disch_then (first_assum o mp_then (Pat `LIST_REL _ _ _`) mp_tac)
    \\ rw []
    \\ imp_res_tac env_rel_def
    \\ fs []
    \\ every_case_tac \\ fs []
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

Theorem pmatch_drule_form[local]:
  pmatch env.c s.refs p x [] = res ∧
  s_rel ^ci s t ∧ env_rel (v_rel (orac_s t.eval_state)) env env' ∧
  v_rel (orac_s t.eval_state) x y ⇒
  match_result_rel T (LIST_REL ($= ### v_rel (orac_s t.eval_state)))
    res (pmatch env'.c t.refs p y [])
Proof
  rw []
  \\ drule_then irule (UNDISCH_ALL pmatch |> CONJUNCT1 |> DISCH_ALL)
  \\ simp []
  \\ metis_tac []
QED

Theorem can_pmatch_all:
  can_pmatch_all env.c s.refs pats x /\
  s_rel ^ci s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  v_rel (orac_s t.eval_state) x y ==>
  can_pmatch_all env'.c t.refs pats y
Proof
  rw []
  \\ Induct_on `pats`
  \\ rw [can_pmatch_all_def]
  \\ drule (pmatch_drule_form |> GEN_ALL |> SIMP_RULE bool_ss [])
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `h` mp_tac)
  \\ simp [match_result_rel_def]
  \\ every_case_tac
  \\ fs []
  \\ rw []
  \\ simp []
QED

Theorem Num_11:
  0 <= i /\ 0 <= j ==> (Num i = Num j) = (i = j)
Proof
  metis_tac [integerTheory.INT_OF_NUM]
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
  \\ imp_res_tac v_to_env_id_SOME
  \\ rveq \\ fs []
  \\ fs [Boolv_def, eq_result_case_eq, bool_case_eq]
  \\ fs [do_eq_def, nat_to_v_def, lit_same_type_def]
  \\ rw []
  \\ TRY (Cases_on ‘ys’ ORELSE Cases_on ‘xs’ \\ gs[do_eq_def] \\ NO_TAC)
  \\ qpat_x_assum `_ = Eq_val _` mp_tac
  \\ rpt (COND_CASES_TAC \\ gs[])
QED

Theorem store_assign:
  store_assign lnum sv refs = SOME refs2 /\
  LIST_REL (sv_rel R) refs refs3 /\
  sv_rel R sv sv' ==>
  ?refs4.
  LIST_REL (sv_rel R) refs2 refs4 /\
  store_assign lnum sv' refs3 = SOME refs4
Proof
  rw [store_assign_def]
  \\ simp [LUPDATE_def]
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
  store_lookup n refs' = SOME sv'
Proof
  rw [store_lookup_def, LIST_REL_EL_EQN]
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
  recInduct v_to_list_ind
  \\ rw [v_to_list_def]
  \\ fs [v_to_list_def, option_case_eq]
  \\ rveq \\ fs []
  \\ res_tac
  \\ simp []
QED

Theorem v_to_char_list:
  ! x y xs. v_to_char_list x = SOME xs /\
  v_rel es x y ==>
  v_to_char_list y = SOME xs
Proof
  recInduct v_to_char_list_ind
  \\ rw [v_to_char_list_def]
  \\ fs [v_to_char_list_def, option_case_eq]
  \\ rveq \\ fs []
QED

Theorem vs_to_string:
  !xs ys s. vs_to_string xs = SOME s /\
  LIST_REL (v_rel es) xs ys ==>
  vs_to_string ys = SOME s
Proof
  recInduct vs_to_string_ind
  \\ rw [vs_to_string_def]
  \\ fs [option_case_eq]
  \\ rveq \\ fs []
  \\ simp [vs_to_string_def]
QED

Theorem sv_rel_l_cases =
  [``sv_rel R (Refv rv) v``, ``sv_rel R (W8array xs) v``,
        ``sv_rel R (Varray vs) v``]
  |> map (SIMP_CONV (srw_ss ()) [sv_rel_cases])
  |> map GEN_ALL |> LIST_CONJ

Theorem v_rel_check_type[local]:
  v_rel x v1 v2 ⇒
  (check_type ty v1 = check_type ty v2) ∧
  (dest_Litv v1 = dest_Litv v2)
Proof
  simp [Once v_rel_cases]
  \\ rw [] \\ gvs [check_type_def,dest_Litv_def, oneline v_to_env_id_def,AllCaseEqs()]
  \\ gvs [oneline check_type_def,Boolv_def]
  \\ Cases_on ‘ty’ \\ gvs []
  \\ eq_tac \\ rw [] \\ gvs []
QED

Theorem LIST_REL_v_rel_check_type[local]:
  LIST_REL (v_rel x) vs1 vs2 ⇒
  (EVERY (check_type ty) vs1 ⇔ EVERY (check_type ty) vs2)
Proof
  rw[LIST_REL_EL_EQN, EVERY_EL]
  \\ PROVE_TAC[v_rel_check_type]
QED

Theorem do_app_sim:
  do_app (s.refs, s.ffi) op (REVERSE xs) = SOME ((refs, ffi), r) /\
  s_rel ^ci s t /\
  LIST_REL (v_rel (orac_s t.eval_state)) xs ys /\
  r <> Rerr (Rabort Rtype_error)
  ==>
  ? ref1 refs' r' es.
    es = orac_s t.eval_state /\
    do_app (t.refs, t.ffi) op (REVERSE ys) = SOME ((refs', ffi), r') /\
    LIST_REL (sv_rel (v_rel es)) refs refs' /\
    result_rel (v_rel es) (v_rel es) r r'
Proof
  rw [s_rel_def]
  \\ fs []
  \\ last_x_assum mp_tac
  \\ simp [Once do_app_cases] \\ rw [listTheory.SWAP_REVERSE_SYM]
  \\ fs [CaseEq "ffi_result", option_case_eq] \\ rveq \\ fs []
  \\ simp [do_app_def]
  >~ [`do_test`] >- (
    imp_res_tac v_rel_check_type
    \\ Cases_on ‘test’ \\ gvs [do_test_def,AllCaseEqs()]
    >- (Cases_on ‘y’ \\ Cases_on ‘y'’ \\ gvs [check_type_def]
        \\ gvs [dest_Litv_def]
        \\ gvs [oneline dest_Litv_def,AllCaseEqs()])
    \\ res_tac
    \\ Cases_on ‘test_ty’ using prim_type_cases \\ gvs [check_type_def]
    \\ res_tac)
  >~ [‘do_arith’] >- (
    drule_then(qspec_then`ty`strip_assume_tac) LIST_REL_v_rel_check_type
    \\ `refs = s.refs` by gvs[CaseEq"sum"]
    \\ gvs[]
    \\ first_assum $ irule_at Any
    \\ Cases_on`a` \\ Cases_on ‘ty’ using prim_type_cases
    \\ Cases_on`xs`
    \\ gvs[do_arith_def, CaseEq"list", check_type_def, CaseEq"bool"]
    >- (EVAL_TAC \\ rw[])
    >- (EVAL_TAC \\ rw[])
    \\ Cases_on`t` \\ gvs[check_type_def])
  >~ [‘do_conversion’] >- (
    imp_res_tac v_rel_check_type \\ rw[]
    \\ Cases_on ‘ty1’ using prim_type_cases
    \\ Cases_on ‘ty2’ using prim_type_cases
    \\ gvs[do_conversion_def, check_type_def, AllCaseEqs()]
    \\ simp [chr_exn_v_def, EVERY2_refl])
  >~ [`thunk_op`]
  >- (
    gvs [AllCaseEqs(), PULL_EXISTS, thunk_op_def]
    >- (
      rpt (pairarg_tac \\ gvs [])
      \\ gvs [store_alloc_def, LIST_REL_EL_EQN])
    \\ Cases_on ‘xs’ \\ gvs []
    \\ drule_then (drule_then (qsubterm_then `store_assign _ _` mp_tac))
         store_assign \\ rw []
    \\ gvs [])
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
  \\ imp_res_tac v_to_env_id_SOME
  \\ fs [PULL_EXISTS, store_alloc_def, sv_rel_l_cases, nat_to_v_def]
  \\ rveq \\ fs []
  \\ TRY (irule EVERY2_refl \\ simp [MEM_MAP, EXISTS_PROD, PULL_EXISTS])
  \\ TRY (drule_then (drule_then (qsubterm_then `store_assign _ _` mp_tac))
        store_assign
        \\ rw [EVERY2_LUPDATE_same])
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [LIST_REL_REPLICATE_same, EVERY2_LUPDATE_same, LIST_REL_APPEND_EQ]
  \\ TRY (Cases_on ‘ys’ using SNOC_CASES \\ gs[SNOC_APPEND, REVERSE_APPEND])
  \\ TRY (fs [LIST_REL_EL_EQN, EVERY2_REVERSE1] \\ NO_TAC)
QED

Theorem pairarg_to_pair_map:
  (\(x, y). (f x, g y)) = (f ## g)
Proof
  simp [FUN_EQ_THM, FORALL_PROD]
QED

Theorem s_rel_clock:
  s_rel ^ci s t ==> s.clock = t.clock /\
    s_rel ci (dec_clock s) (dec_clock t)
Proof
  rw [s_rel_def]
  \\ fs [evaluateTheory.dec_clock_def]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ rw []
  \\ fs []
QED

Theorem concrete_v_rel:
  !x y. v_rel es x y ==> concrete_v x ==> y = x
Proof
  ho_match_mp_tac v_rel_ind
  \\ rw []
  \\ fs [EVERY_EL, LIST_REL_EL_EQN, LIST_EQ_REWRITE]
QED

Theorem v_to_list_concrete:
  !x xs. v_to_list x = SOME xs ==>
  concrete_v x = EVERY concrete_v xs
Proof
  recInduct v_to_list_ind
  \\ rw [v_to_list_def]
  \\ fs [option_case_eq]
  \\ rveq \\ fs []
  \\ rfs []
QED

Theorem maybe_all_list_SOME:
  !xs ys. maybe_all_list xs = SOME ys ==> xs = MAP SOME ys
Proof
  Induct \\ simp [Once maybe_all_list_def]
  \\ simp [option_case_eq, PULL_EXISTS]
QED

Theorem maybe_all_list_EVERY:
  maybe_all_list xs = SOME ys ==> EVERY (\x. x <> NONE) xs
Proof
  rw [] \\ imp_res_tac maybe_all_list_SOME
  \\ simp [EVERY_MAP]
QED

Theorem v_to_word8_list_concrete:
  v_to_word8_list x = SOME xs ==>
  concrete_v x
Proof
  rw [v_to_word8_list_def, option_case_eq]
  \\ imp_res_tac maybe_all_list_EVERY
  \\ drule v_to_list_concrete
  \\ rw []
  \\ fs [EVERY_MAP]
  \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac MONO_EVERY)
  \\ Cases \\ simp [v_to_word8_def]
QED

Theorem v_to_word64_list_concrete:
  v_to_word64_list x = SOME xs ==>
  concrete_v x
Proof
  rw [v_to_word64_list_def, option_case_eq]
  \\ imp_res_tac maybe_all_list_EVERY
  \\ drule v_to_list_concrete
  \\ rw []
  \\ fs [EVERY_MAP]
  \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac MONO_EVERY)
  \\ Cases \\ simp [v_to_word64_def]
QED

Theorem compiler_agrees:
  compiler_agrees f (id, st_v, decs) (st_v2, bs_v, ws_v) ==>
  concrete_v st_v /\ concrete_v st_v2 /\ concrete_v bs_v /\ concrete_v ws_v
Proof
  simp [compiler_agrees_def]
  \\ every_case_tac
  \\ rw []
  \\ imp_res_tac v_to_word8_list_concrete
  \\ imp_res_tac v_to_word64_list_concrete
QED

Theorem recorded_orac_wf_step:
  recorded_orac_wf compiler orac /\
  compiler_agrees compiler args (st_v2, bs_v, ws_v) /\
  (0 < FST (FST (orac 0)) ==> FST (SND args) = (FST (SND (orac 0))))
  ==>
  recorded_orac_wf compiler
    (λj. if j = 0 then ((FST (FST (orac 0)) + 1,0), st_v2, [])
      else if j = SUC (FST (FST (orac 0))) then args
      else orac j)
Proof
  simp [recorded_orac_wf_def, compiler_agrees_def]
  \\ simp [GSYM ADD1, prim_recTheory.LESS_THM]
  \\ every_case_tac \\ fs []
  \\ rw [] \\ fs []
QED

Theorem do_eval_sim:
  do_eval (REVERSE xs) s.eval_state = SOME (env, decs, es) /\
  s_rel ^ci (s : 'a semanticPrimitives$state) t /\
  LIST_REL (v_rel (orac_s t.eval_state)) xs ys ==>
  ? env' es'.
  es_forward (orac_s t.eval_state) (orac_s es') /\
  do_eval (REVERSE ys) t.eval_state = SOME (env', decs, es') /\
  env_rel (v_rel (orac_s es')) env env' /\
  s_rel ci (s with eval_state := es) (t with eval_state := es') /\
  (! s2 t2. s_rel ci (s2 : 'a semanticPrimitives$state) t2 /\
    es_forward (orac_s es') (orac_s t2.eval_state) /\
    es_stack_forward (orac_s es') (orac_s t2.eval_state) ==>
    es_forward (orac_s t2.eval_state)
        (orac_s (reset_env_generation t.eval_state t2.eval_state)) /\
    s_rel ci
        (s2 with eval_state := reset_env_generation s.eval_state s2.eval_state)
        (t2 with eval_state := reset_env_generation t.eval_state t2.eval_state)
    /\
    es_stack_forward (orac_s t.eval_state)
        (orac_s (reset_env_generation t.eval_state t2.eval_state))
  )
Proof
  rw []
  \\ fs [do_eval_def, s_rel_def] \\ fs []
  \\ fs [list_case_eq, v_case_eq, option_case_eq, pair_case_eq]
  \\ fs [listTheory.SWAP_REVERSE_SYM]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ simp [do_eval_record_def, state_component_equality]
  \\ imp_res_tac compiler_agrees
  \\ imp_res_tac concrete_v_rel
  \\ fs [ELIM_UNCURRY]
  \\ rveq \\ fs []
  \\ simp [add_env_generation_def, add_decs_generation_def, PULL_EXISTS]
  \\ simp [EL_APPEND_EQN]
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, oEL_THM]
    \\ simp [bool_case_eq, option_case_eq, EL_APPEND_EQN]
  )
  \\ rpt strip_tac \\ fs []
  \\ TRY (imp_res_tac forward_rules \\ rw [] \\ fs [] \\ NO_TAC)
  >- (
    drule_then (drule_then irule) recorded_orac_wf_step
    \\ rw [] \\ fs []
  )
  \\ fs [reset_env_generation_def]
  \\ simp []
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, oEL_THM]
  )
  \\ simp [EQ_SYM_EQ]
  \\ fs [es_stack_forward_def]
  \\ rfs [EL_APPEND_EQN]
  \\ imp_res_tac forward_rules
QED

Theorem declare_env_sim:
  declare_env s.eval_state env = SOME (v, es) /\
  s_rel ^ci s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' ==>
  ?v' es2.
  es_forward (orac_s t.eval_state) (orac_s es2) /\
  declare_env t.eval_state env' = SOME (v', es2) /\
  v_rel (orac_s es2) v v' /\
  s_rel ci (s with eval_state := es) (t with eval_state := es2) /\
  es_stack_forward (orac_s t.eval_state) (orac_s es2)
Proof
  rw [s_rel_def, declare_env_def]
  \\ fs []
  \\ rveq \\ fs []
  \\ simp [oEL_THM, v_to_env_id_def,
        v_to_nat_def, nat_to_v_def, lookup_env_def, EL_LUPDATE]
  \\ simp [EL_APPEND_EQN]
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, oEL_THM]
    \\ simp [bool_case_eq, option_case_eq]
    \\ rw [EL_APPEND_EQN, EL_LUPDATE]
  )
  \\ simp [state_component_equality, PULL_EXISTS]
  \\ simp [es_stack_forward_def, EL_LUPDATE]
  \\ imp_res_tac forward_rules \\ fs []
  \\ rw [] \\ fs []
QED

Definition abort_def:
  abort r <=> (case r of Rerr (Rabort a) => T
    | _ => F)
End

Theorem abort_simps[simp]:
  abort (Rerr (Rabort a)) = T /\
  abort (Rerr (Rraise e)) = F /\
  abort (Rval v) = F
Proof
  simp [abort_def]
QED

Theorem abort_imp_intro[local]:
  (!v. x = Rval v ==> P) /\ (!e. x = Rerr (Rraise e) ==> P) ==>
  (~ abort x ==> P)
Proof
  simp [abort_def] \\ every_case_tac \\ simp []
QED

val case_const = ``Case``
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

(* case splits for evaluate proofs *)
val eval_cases_tac =
  fs [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
        option_case_eq, list_case_eq, exp_or_val_case_eq, match_result_case_eq]
  \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs []

(* take a step of forward-consistency-type reasoning *)
val forward_tac = MAP_FIRST (drule_then irule)
    (map (REWRITE_RULE [Once CONJ_COMM])
        [es_forward_trans, es_stack_forward_trans] @ IMP_CANON forward_rules)

(* quantifier instantiation based on s_rel, v_rel etc *)
val insts_tac = rpt (FIRST ([
      do_xig_inst `s_rel Ig_ci X_s _`,
      do_xig_inst `env_rel (v_rel Ig_es) X_env _`,
      do_xig_inst `LIST_REL (v_rel Ig_es) X_env _`,
      do_xig_inst `v_rel Ig_es X_v _`,
      CHANGED_TAC (rveq \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ,
            es_forward_refl, es_stack_forward_refl]
        \\ rfs []),
      forward_tac,
      first_x_assum (fn t => mp_tac t \\ (impl_tac THENL
            [rpt conj_tac \\ forward_tac, disch_tac])),
      conj_tac THENL [forward_tac, all_tac],
      match_mp_tac abort_imp_intro \\ rw [] \\ fs []
    ]))

val eval_simulation_setup = setup (`
  (! ^s env exps s' res es t env'.
  evaluate s env exps = (s', res) /\
  s_rel ^ci s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ? es' t' res'.
  evaluate t env' exps = (t', res') /\
  s_rel ci s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (LIST_REL (v_rel es')) (v_rel es') res res' /\
  es_forward (orac_s t.eval_state) es' /\
  (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es'))
  /\
  (! ^s env x pes err_x s' res es t env' y err_y.
  evaluate_match s env x pes err_x = (s', res) /\
  s_rel ci s t /\
  es = orac_s t.eval_state /\
  env_rel (v_rel es) env env' /\
  v_rel es x y /\
  v_rel es err_x err_y /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_match t env' y pes err_y = (t', res') /\
  s_rel ci s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (LIST_REL (v_rel es')) (v_rel es') res res' /\
  es_forward es es' /\
  (~ abort res' ==> es_stack_forward es es'))
  /\
  (! ^s env decs s' res t env'.
  evaluate_decs s env decs = (s', res) /\
  s_rel ci s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_decs t env' decs = (t', res') /\
  s_rel ci s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (env_rel (v_rel es')) (v_rel es') res res' /\
  es_forward (orac_s t.eval_state) es' /\
  (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es'))
  `,
  ho_match_mp_tac (name_ind_cases [``()``, ``()``, ``Dlet``] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def]
  (* FIXME: tweak name_ind_cases to skip dummy patterns *)
  \\ fs [Q.prove (`Case ((), x) = Case (x)`, simp [markerTheory.Case_def])]
  \\ rveq \\ fs []
  );

Theorem eval_simulation_App:
  ^(#get_goal eval_simulation_setup `Case ([App _ _])`)
Proof
  rw []
  \\ reverse (fs [pair_case_eq, result_case_eq] \\ rveq \\ fs [])
  \\ insts_tac
  \\ Cases_on `getOpClass op`
  >- (
    fs [do_eval_res_def, evaluate_def, do_con_check_def]
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ drule_then (drule_then drule) do_eval_sim
    \\ rw []
    \\ fs []
    \\ drule_then assume_tac s_rel_clock
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    \\ insts_tac
    \\ fs [EVAL ``(dec_clock x).eval_state``]
    \\ eval_cases_tac
    \\ insts_tac
    \\ TRY (drule_then (drule_then (qsubterm_then `declare_env _ _` mp_tac))
        declare_env_sim
      \\ impl_tac
      \\ (irule env_rel_extend_dec_env ORELSE disch_tac))
    \\ insts_tac
    \\ first_x_assum drule \\ impl_tac
    \\ rw [] \\ insts_tac
  )
  >- (
    rveq \\ fs []
    \\ imp_res_tac s_rel_clock
    \\ fs [do_opapp_def]
    \\ eval_cases_tac
    \\ fs [listTheory.SWAP_REVERSE_SYM, CaseEq "v"] \\ rveq \\ fs []
    \\ fs [listTheory.SWAP_REVERSE, miscTheory.FST_triple]
    \\ eval_cases_tac
    \\ insts_tac
    \\ rfs [EVAL ``(dec_clock s).eval_state``]
    \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ irule env_rel_add_nsBind
    \\ insts_tac
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_rel_add_nsBindList
    \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
    \\ simp [ELIM_UNCURRY, EVERY2_refl]
  )
  >~ [`getOpClass op = Force`]
  >- (
    gvs [AllCaseEqs(), dec_clock_def]
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline store_lookup_def]
      \\ gvs [s_rel_def, LIST_REL_EL_EQN]
      \\ `∃a. EL n refs'' = Thunk Evaluated a ∧
              v_rel orac_s'' v a` by (
        first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs []
      \\ simp [state_component_equality])
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline store_lookup_def]
      \\ simp[PULL_EXISTS]
      \\ gvs [s_rel_def, LIST_REL_EL_EQN]
      \\ `∃a. EL n refs'' = Thunk NotEvaluated a ∧
              v_rel orac_s'' v a` by (
        first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs []
      \\ gvs[do_opapp_cases] \\ irule_at Any EQ_REFL >> simp[])
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline store_lookup_def]
      \\ `n < LENGTH t''.refs ∧
          ∃a. EL n t''.refs = Thunk NotEvaluated a ∧
          v_rel (orac_s t''.eval_state) v a` by (
        gvs [s_rel_def, LIST_REL_EL_EQN]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs [] >>
        gvs[do_opapp_cases, PULL_EXISTS]
        >- (
          imp_res_tac s_rel_def >> gvs[] >>
          drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
          last_x_assum dxrule >> simp[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
          disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
          >- (unabbrev_all_tac >> irule env_rel_add_nsBind >> simp[]) >>
          strip_tac >> gvs[] >>
          gvs[oneline update_thunk_def, AllCaseEqs()] >>
          gvs[store_assign_def, s_rel_def, state_component_equality] >>
          reverse $ rw[] >> insts_tac
          >- (irule EVERY2_LUPDATE_same >> gvs[])
          >- (
            gvs[LIST_REL_EL_EQN, store_v_same_type_def] >>
            first_x_assum drule >> simp[sv_rel_cases] >>
            strip_tac >> gvs[]
            )
          >- gvs[LIST_REL_EL_EQN] >>
          qpat_x_assum ‘dest_thunk _ _ = _’ mp_tac >> simp[oneline dest_thunk_def] >>
          qpat_x_assum ‘v_rel _ _ _’ mp_tac >> simp[Once v_rel_cases] >> strip_tac >> gvs[]
          >- gvs[oneline v_to_env_id_def, AllCaseEqs()] >>
          simp[store_lookup_def] >> gvs[LIST_REL_EL_EQN] >>
          IF_CASES_TAC >> gvs[] >>
          first_x_assum drule >> simp[sv_rel_cases] >> strip_tac >> gvs[] >>
          TOP_CASE_TAC >> gvs[]
          )
        >- (
          imp_res_tac s_rel_def >> gvs[] >>
          drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
          last_x_assum dxrule >> simp[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
          disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
          >- (
            unabbrev_all_tac >> simp[build_rec_env_merge, nsAppend_to_nsBindList] >>
            irule env_rel_add_nsBind >> simp[] >>
            irule env_rel_add_nsBindList >>
            simp[LIST_REL_MAP1, SRULE [SF ETA_ss] LIST_REL_MAP2, ELIM_UNCURRY] >>
            simp[LIST_REL_EL_EQN]
            ) >>
          strip_tac >> gvs[] >>
          gvs[oneline update_thunk_def, AllCaseEqs()] >>
          gvs[store_assign_def, s_rel_def, state_component_equality] >>
          reverse $ rw[] >> insts_tac
          >- (irule EVERY2_LUPDATE_same >> gvs[])
          >- (
            gvs[LIST_REL_EL_EQN, store_v_same_type_def] >>
            first_x_assum drule >> simp[sv_rel_cases] >>
            strip_tac >> gvs[]
            )
          >- gvs[LIST_REL_EL_EQN] >>
          qpat_x_assum ‘dest_thunk _ _ = _’ mp_tac >> simp[oneline dest_thunk_def] >>
          qpat_x_assum ‘v_rel _ _ _’ mp_tac >> simp[Once v_rel_cases] >> strip_tac >> gvs[]
          >- gvs[oneline v_to_env_id_def, AllCaseEqs()] >>
          simp[store_lookup_def] >> gvs[LIST_REL_EL_EQN] >>
          IF_CASES_TAC >> gvs[] >>
          first_x_assum drule >> simp[sv_rel_cases] >> strip_tac >> gvs[] >>
          TOP_CASE_TAC >> gvs[]
          )
      )
    >- (
      gvs [oneline dest_thunk_def, AllCaseEqs(), oneline store_lookup_def]
      \\ `n < LENGTH t''.refs ∧
          ∃a. EL n t''.refs = Thunk NotEvaluated a ∧
          v_rel (orac_s t''.eval_state) v a` by (
        gvs [s_rel_def, LIST_REL_EL_EQN]
        \\ first_x_assum drule \\ rw []
        \\ Cases_on `EL n refs''` \\ gvs [sv_rel_def]) \\ gvs [] >>
        gvs[do_opapp_cases, PULL_EXISTS]
        >- (
          imp_res_tac s_rel_def >> gvs[] >>
          irule_at Any OR_INTRO_THM2 >>
          drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
          last_x_assum dxrule >> simp[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
          disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
          >- (unabbrev_all_tac >> irule env_rel_add_nsBind >> simp[]) >>
          strip_tac >> gvs[] >> insts_tac
          )
        >- (
          imp_res_tac s_rel_def >> gvs[] >>
          irule_at Any OR_INTRO_THM2 >>
          drule s_rel_clock >> simp[dec_clock_def] >> strip_tac >>
          last_x_assum dxrule >> simp[] >>
          qmatch_goalsub_abbrev_tac ‘evaluate _ new_env’ >>
          disch_then $ qspec_then ‘new_env’ mp_tac >> impl_tac
          >- (
            unabbrev_all_tac >> simp[build_rec_env_merge, nsAppend_to_nsBindList] >>
            irule env_rel_add_nsBind >> simp[] >>
            irule env_rel_add_nsBindList >>
            simp[LIST_REL_MAP1, SRULE [SF ETA_ss] LIST_REL_MAP2, ELIM_UNCURRY] >>
            simp[LIST_REL_EL_EQN]
            ) >>
          strip_tac >> gvs[] >> insts_tac
          )
      )
    )
  \\ eval_cases_tac
  \\ drule_then (drule_then assume_tac) do_app_sim
  \\ insts_tac
  \\ fs [s_rel_def] \\ rveq \\ fs []
  \\ simp [state_component_equality]
  \\ rw [] \\ fs []
QED

Theorem eval_simulation_Denv[local]:
  ^(#get_goal eval_simulation_setup `Case (Dlet, [Denv _])`)
Proof
  rw []
  \\ eval_cases_tac
  \\ fs [declare_env_def, s_rel_def]
  \\ rveq \\ fs []
  \\ fs [pair_case_eq]
  \\ rveq \\ fs []
  \\ simp [oEL_THM]
  \\ simp [state_component_equality]
  \\ qmatch_goalsub_abbrev_tac `es_forward cur_es new_es`
  \\ qsuff_tac `es_forward cur_es new_es`
  >- (
    rpt strip_tac \\ insts_tac
    \\ simp [EL_LUPDATE]
    \\ insts_tac
    \\ simp [nsSing_eq_bind]
    \\ fs [markerTheory.Abbrev_def, es_stack_forward_def, EL_LUPDATE]
    \\ irule env_rel_add_nsBind
    \\ simp [v_to_env_id_def, v_to_nat_def, nat_to_v_def]
    \\ fs [markerTheory.Abbrev_def, lookup_env_def,
          oEL_THM, EL_LUPDATE, EL_APPEND_EQN,
          es_stack_forward_def]
    \\ insts_tac
  )
  >- (
    fs [markerTheory.Abbrev_def, es_forward_def, FORALL_PROD]
    \\ simp [lookup_env_def, oEL_THM, option_case_eq]
    \\ simp [EL_LUPDATE]
    \\ rw [EL_APPEND_EQN]
  )
QED

Theorem eval_simulation_Con[local]:
  ^(#get_goal eval_simulation_setup `Case ([Con _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ imp_res_tac env_rel_def
  \\ fs [do_con_check_def, build_conv_def]
  \\ every_case_tac
  \\ insts_tac
QED

Theorem eval_simulation_Let[local]:
  ^(#get_goal eval_simulation_setup `Case ([Let _ _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ simp [namespaceTheory.nsOptBind_def]
  \\ CASE_TAC \\ fs []
  \\ impl_tac
  \\ rw []
  \\ insts_tac
  \\ irule env_rel_add_nsBind
  \\ insts_tac
QED

Theorem eval_simulation_Letrec[local]:
  ^(#get_goal eval_simulation_setup `Case ([Letrec _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ fs [miscTheory.FST_triple, MAP_MAP_o]
  \\ fs [GSYM pairarg_to_pair_map, ELIM_UNCURRY, o_DEF, ETA_THM]
  \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
  \\ irule env_rel_add_nsBindList
  \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
  \\ simp [ELIM_UNCURRY]
  \\ simp [GSYM pairarg_to_pair_map, ELIM_UNCURRY, EVERY2_refl]
QED

Theorem eval_simulation_match[local]:
  ^(#get_goal eval_simulation_setup `Case ((_, _) :: _)`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ drule_then (drule_then assume_tac) pmatch_drule_form
  \\ insts_tac
  \\ fs [match_result_rel_def]
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ simp [nsAppend_to_nsBindList]
  \\ irule env_rel_add_nsBindList
  \\ simp [nsAppend_to_nsBindList]
QED

Theorem eval_simulation_cons_decs[local]:
  ^(#get_goal eval_simulation_setup `Case (Dlet, _ :: _ :: _)`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate_decs _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ TRY (irule env_rel_extend_dec_env)
  \\ insts_tac
  \\ TRY strip_tac
  \\ fs [combine_dec_result_def]
  \\ every_case_tac \\ fs []
  \\ rw [] \\ insts_tac
  \\ simp [GSYM (SIMP_RULE (srw_ss ()) [] extend_dec_env_def)]
  \\ TRY (irule env_rel_extend_dec_env)
  \\ insts_tac
QED

Theorem env_rel_imp_c[local]:
  env_rel x env env' ⇒ env'.c = env.c
Proof
  fs [env_rel_def]
QED

Theorem eval_simulation_Dletrec[local]:
  ^(#get_goal eval_simulation_setup `Case (_, [Dletrec _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ fs [miscTheory.FST_triple, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
  \\ imp_res_tac env_rel_imp_c
  \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
  \\ irule env_rel_add_nsBindList
  \\ simp []
  \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
  \\ simp [ELIM_UNCURRY]
  \\ simp [EVERY2_refl]
QED

Theorem check_dup_ctors_thm:
   check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs)
Proof
  rw [check_dup_ctors_def] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs [] >>
  eq_tac >>
  rw [] >>
  induct_on `condefs` >>
  rw [] >>
  pairarg_tac >>
  fs []
QED

Theorem eval_simulation_Dtype[local]:
  ^(#get_goal eval_simulation_setup `Case (_, [Dtype _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ fs [EVERY_MEM, FORALL_PROD, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
      check_dup_ctors_thm]
  \\ fs [s_rel_def, state_component_equality]
  \\ insts_tac
  \\ simp []
QED

Theorem eval_simulation_Dexn[local]:
  ^(#get_goal eval_simulation_setup `Case (_, [Dexn _ _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ fs [s_rel_def, state_component_equality]
  \\ insts_tac
QED

Theorem eval_simulation_Dlocal[local]:
  ^(#get_goal eval_simulation_setup `Case (_, [Dlocal _ _])`)
Proof
  rpt disch_tac
  \\ eval_cases_tac
  \\ insts_tac
  \\ first_x_assum (qsubterm_then `evaluate_decs _ _ _` mp_tac)
  \\ impl_tac \\ rw [] \\ insts_tac
  \\ irule env_rel_extend_dec_env
  \\ insts_tac
QED

Theorem eval_simulation:
  ^(#concl eval_simulation_setup ())
Proof
  #init eval_simulation_setup [eval_simulation_App,
    eval_simulation_Denv, eval_simulation_Con, eval_simulation_Let,
    eval_simulation_Letrec, eval_simulation_match,
    eval_simulation_cons_decs, eval_simulation_Dletrec,
    eval_simulation_Dtype, eval_simulation_Dexn, eval_simulation_Dlocal]
  \\ rpt disch_tac
  \\ insts_tac
  \\ TRY ( (
    (* big hammer for similar cases *)
    eval_cases_tac
    \\ fs []
    \\ imp_res_tac env_rel_imp_c
    \\ insts_tac
    \\ fs [do_con_check_def, build_conv_def, do_log_def, do_if_def]
    \\ TRY (drule_then (drule_then assume_tac) can_pmatch_all)
    \\ TRY (drule_then (drule_then assume_tac)
        (REWRITE_RULE [match_result_rel_def] pmatch_drule_form))
    \\ TRY (drule_then drule env_rel_nsLookup_v \\ rw [])
    \\ eval_cases_tac
    \\ fs [bind_exn_v_def]
    \\ insts_tac
    \\ simp [alist_to_ns_to_bind2]
    \\ TRY (irule env_rel_add_nsBindList)
    \\ TRY (irule env_rel_nsLift)
    \\ simp []
   )
  \\ NO_TAC
  )
QED

Overload shift_seq = “misc$shift_seq”

Definition do_eval_oracle_def:
  do_eval_oracle (f : compiler_fun) (g : dec list -> dec list) vs
    (orac : eval_oracle_fun) =
  case vs of
    | [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] =>
      let (env_id, st, decs) = orac 0 in
      (case f (env_id, st, decs), v_to_word8_list bs_v,
            v_to_word64_list ws_v of
        | (SOME (st_v2, c_bs, c_ws), SOME bs, SOME ws) =>
            if bs = c_bs /\ ws = c_ws /\ st_v2 = (FST (SND (orac 1)))
            then SOME (env_id, shift_seq 1 orac, g decs)
            else NONE
        | _ => NONE
      )
    | _ => NONE
End

Definition insert_gen_oracle_def:
  insert_gen_oracle ci g shift_f orac es = case es of
    | SOME (EvalOracle s) => SOME (EvalOracle (s with <|
        custom_do_eval := do_eval_oracle (mk_compiler_fun_from_ci ci) g;
        oracle := shift_seq (shift_f (s.oracle 0)) orac |>))
    | _ => es
End

Overload insert_oracle[local] = ``\ci. insert_gen_oracle ci I (FST o FST)``;

Definition orac_agrees_def:
  orac_agrees orac es = case es of
    | SOME (EvalOracle s) =>
      (!j. j < FST (FST (s.oracle 0)) ==> orac j = s.oracle (j + 1))
    | _ => F
End

(* the infinite extension of an oracle is still well-formed with
   respect to the compiler function *)
Definition orac_extended_wf_def:
  orac_extended_wf f orac =
  (!i x. f (orac i) = SOME x ==> FST x = FST (SND (orac (SUC i))))
End

Definition record_forward_def:
  record_forward es es' = (case es of
    | SOME (EvalOracle s) => ?s'. es' = SOME (EvalOracle s') /\
        (FST (FST (s.oracle 0)) <= FST (FST (s'.oracle 0))) /\
        (!j. 0 < j /\ j < FST (FST (s.oracle 0)) + 1 ==>
            s'.oracle j = s.oracle j)
    | _ => (case es' of SOME (EvalOracle _) => F | _ => T)
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

Definition is_record_def:
  is_record ci es ⇔ case es of
    | SOME (EvalOracle s) =>
        s.custom_do_eval = do_eval_record ci
    | _ => F
End

Theorem is_record_IMP:
  is_record ^ci es ==> ? orac_st. es = SOME (EvalOracle orac_st)
Proof
  simp [is_record_def] \\ every_case_tac \\ simp []
QED

Theorem insert_do_eval:
  do_eval vs es = SOME (env, decs, es') /\
  is_record ci es ==>
  is_record ci es' /\
  record_forward es es' /\
  (orac_agrees orac es' /\
  orac_extended_wf (ci_comp ci) orac ==>
  do_eval vs (insert_oracle ci orac es) = SOME (env, decs,
    insert_oracle ci orac es')) /\
  (recorded_orac_wf (ci_comp ci) (orac_s es).oracle ==>
    recorded_orac_wf (ci_comp ci) (orac_s es').oracle)
Proof
  simp [is_record_def, Once do_eval_def]
  \\ disch_tac
  \\ fs [option_case_eq, eval_state_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ fs [do_eval_def, add_env_generation_def, insert_gen_oracle_def]
  \\ fs [do_eval_record_def, list_case_eq, option_case_eq] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ every_case_tac \\ fs []
  \\ imp_res_tac compiler_agrees_def
  \\ every_case_tac \\ fs []
  \\ simp [do_eval_oracle_def]
  \\ rveq \\ fs []
  \\ fs [record_forward_def, orac_agrees_def, shift_seq_def]
  \\ rw []
  >- (
    fs [orac_extended_wf_def]
    \\ rpt (first_x_assum (qspec_then `i` mp_tac))
    \\ simp [ADD1]
  )
  >- (
    Cases_on `env_id` \\ fs [lookup_env_def]
  )
  >- (
    drule_then drule recorded_orac_wf_step
    \\ simp []
  )
QED

Theorem insert_declare_env:
  declare_env es1 env = SOME (x, es2) /\
  is_record ci es1 ==>
  is_record ci es2 /\
  record_forward es1 es2 /\
  (orac_agrees orac es2 ==>
  declare_env (insert_oracle ci orac es1) env = SOME (x,
    insert_oracle ci orac es2)) /\
  (recorded_orac_wf (ci_comp ci) (orac_s es1).oracle ==>
    recorded_orac_wf (ci_comp ci) (orac_s es2).oracle)
Proof
  simp [is_record_def, declare_env_def, insert_gen_oracle_def]
  \\ every_case_tac \\ fs []
  \\ disch_tac
  \\ fs [] \\ rveq \\ fs []
  \\ simp [PULL_EXISTS]
  \\ simp [record_forward_def, recorded_orac_wf_def]
QED

Theorem reset_env_generation_orac_eqs:
  (is_record ci (reset_env_generation es2 es3) = is_record ci es3) ∧
  (record_forward es1 (reset_env_generation es2 es3) = record_forward es1 es3) ∧
  (orac_agrees orac (reset_env_generation es2 es3) = orac_agrees orac es3) ∧
  (reset_env_generation (insert_oracle ci orac es1) es2 =
    reset_env_generation es1 es2) ∧
  (reset_env_generation es1 (insert_oracle ci orac es2) =
    insert_oracle ci orac (reset_env_generation es1 es2)) ∧
  ((orac_s (reset_env_generation es2 es3)).oracle = (orac_s es3).oracle)
Proof
  simp [is_record_def, reset_env_generation_def, insert_gen_oracle_def]
  \\ every_case_tac \\ fs []
  \\ simp [record_forward_def, orac_agrees_def]
QED

Theorem record_forward_trans_sym[local]
  = REWRITE_RULE [Once CONJ_COMM] record_forward_trans

Theorem evaluate_is_record_forward:
  (! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record ^ci s.eval_state
  ==>
  is_record ci s'.eval_state /\
  record_forward s.eval_state s'.eval_state /\
  (recorded_orac_wf (ci_comp ci) (orac_s s.eval_state).oracle ==>
    recorded_orac_wf (ci_comp ci) (orac_s s'.eval_state).oracle)
  )
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record ci s.eval_state
  ==>
  is_record ci s'.eval_state /\
  record_forward s.eval_state s'.eval_state /\
  (recorded_orac_wf (ci_comp ci) (orac_s s.eval_state).oracle ==>
    recorded_orac_wf (ci_comp ci) (orac_s s'.eval_state).oracle)
  )
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record ci s.eval_state
  ==>
  is_record ci s'.eval_state /\
  record_forward s.eval_state s'.eval_state /\
  (recorded_orac_wf (ci_comp ci) (orac_s s.eval_state).oracle ==>
    recorded_orac_wf (ci_comp ci) (orac_s s'.eval_state).oracle)
  )
Proof
  then_select_goals [``Case [App _ _]``] (
  ho_match_mp_tac (name_ind_cases [] full_evaluate_ind)
  \\ rpt conj_tac
  )
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def]
  \\ rveq \\ fs []
  \\ fs []
  \\ simp [record_forward_refl]
  >- (
    Cases_on ‘getOpClass op’ \\ fs[]
    >~ [`getOpClass op = Force`] >- (
      full_simp_tac bool_ss [do_eval_res_def, bool_case_eq, pair_case_eq,
          option_case_eq, result_case_eq, dec_clock_def]
      \\ rveq \\ full_simp_tac bool_ss [PAIR_EQ]
      \\ gvs [AllCaseEqs()]
      \\ imp_res_tac record_forward_trans_sym)
    \\ full_simp_tac bool_ss [do_eval_res_def, bool_case_eq, pair_case_eq,
        option_case_eq, result_case_eq, dec_clock_def]
    \\ rveq \\ full_simp_tac bool_ss [PAIR_EQ]
    \\ fs [] \\ rveq \\ fs []
    \\ fs [error_result_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ] \\ rveq \\ fs []
    \\ TRY (drule_then (drule_then assume_tac) insert_do_eval)
    \\ fs [GSYM PULL_FORALL]
    \\ TRY (drule_then (drule_then assume_tac) insert_declare_env)
    \\ fs [GSYM PULL_FORALL, reset_env_generation_orac_eqs]
    \\ rpt (drule_then irule record_forward_trans_sym)
    \\ simp [record_forward_refl]
    \\ COND_CASES_TAC \\ gs[]
  )
  \\ fs [pair_case_eq, option_case_eq, result_case_eq] \\ rveq \\ fs []
  \\ rpt (drule_then irule record_forward_trans_sym)
  \\ simp [record_forward_refl]
  \\ TRY (drule_then (drule_then assume_tac) insert_declare_env \\ fs [GSYM PULL_FORALL])
  \\ fs [bool_case_eq] \\ rveq \\ fs []
  \\ simp [record_forward_refl]
  \\ fs [dec_clock_def]
  \\ eval_cases_tac
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ rpt (drule_then irule record_forward_trans_sym)
  \\ simp [record_forward_refl]
QED

val agrees_tac = (drule_then irule orac_agrees_backward)
  \\ rpt (simp_tac bool_ss [record_forward_refl]
    \\ drule_then irule record_forward_trans_sym)

val agrees_impl_tac = rpt ((qpat_x_assum `orac_agrees _ _ ==> _` mp_tac
    \\ impl_tac)
  >- agrees_tac)

fun simp_res_tac t = ASSUM_LIST (fn asms => let
    val t2 = SIMP_RULE (srw_ss ()) asms t
  in drule_then simp_res_tac t2
    ORELSE (if is_forall (concl t) then all_tac else strip_assume_tac t)
  end)

fun imp_res_simp_tac t = IMP_RES_THEN mp_tac t
  \\ simp []
  \\ rpt ((disch_then drule \\ simp []) ORELSE disch_then
      (fn t => if is_forall (concl t) then all_tac else assume_tac t))

val imp_res_simp_tac = IMP_RES_THEN simp_res_tac

val insert_oracle_correct_setup = setup (
  `(! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record ci s.eval_state /\
  orac_agrees orac s'.eval_state /\
  orac_extended_wf (ci_comp ci) orac /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  evaluate (s with eval_state updated_by insert_oracle ci orac) env exps =
  (s' with eval_state updated_by insert_oracle ci orac, res)
  )
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record ci s.eval_state /\
  orac_agrees orac s'.eval_state /\
  orac_extended_wf (ci_comp ci) orac /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  evaluate_match (s with eval_state updated_by insert_oracle ci orac)
    env x pes err_x =
  (s' with eval_state updated_by insert_oracle ci orac, res)
  )
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record ci s.eval_state /\
  orac_agrees orac s'.eval_state /\
  orac_extended_wf (ci_comp ci) orac /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  evaluate_decs (s with eval_state updated_by insert_oracle ci orac) env decs =
  (s' with eval_state updated_by insert_oracle ci orac, res)
  )`,
  ho_match_mp_tac (name_ind_cases [``Let``, ``Mat``, ``Dlet``] full_evaluate_ind)
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def]
  \\ fs []
  \\ rveq \\ fs []
  );

Theorem insert_oracle_correct_App[local]:
  ^(#get_goal insert_oracle_correct_setup `Case (_, [App _ _])`)
Proof
  rw []
  \\ fs [pair_case_eq, result_case_eq] \\ rveq \\ fs []
  \\ fs [bool_case_eq] \\ rveq \\ fs [] \\ Cases_on ‘getOpClass op’ \\ gs[]
  >- (
    (* Eval *)
    fs [do_eval_res_def, Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ rveq \\ fs []
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ drule_then drule insert_do_eval
    \\ disch_then (qspecl_then [`orac`] mp_tac)
    \\ rw []
    \\ fs [bool_case_eq] \\ rveq \\ fs []
    >- (
      agrees_impl_tac
      \\ simp []
    )
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ fs [dec_clock_def]
    \\ fs [result_case_eq, option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ fs [error_result_case_eq] \\ rveq \\ fs []
    \\ fs [reset_env_generation_orac_eqs]
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ imp_res_simp_tac insert_declare_env
    \\ agrees_impl_tac
    \\ simp [reset_env_generation_orac_eqs]
  )
  >- (
    (* Opapp *)
    eval_cases_tac
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] \\ rveq \\ fs []
    \\ fs [dec_clock_def]
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ agrees_impl_tac
    \\ simp []
  )
  >~ [`getOpClass op = Force`] >- (
    gvs [AllCaseEqs(), dec_clock_def]
    \\ eval_cases_tac
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ imp_res_simp_tac insert_declare_env
    \\ agrees_impl_tac
    \\ simp [])
  \\ eval_cases_tac
  \\ gs[]
QED

Theorem insert_oracle_correct_Denv[local]:
  ^(#get_goal insert_oracle_correct_setup `Case (_, [Denv _])`)
Proof
  rw []
  \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ imp_res_simp_tac insert_declare_env
  \\ simp []
QED

Theorem insert_oracle_correct:
  ^(#concl insert_oracle_correct_setup ())
Proof
  #init insert_oracle_correct_setup [insert_oracle_correct_App,
    insert_oracle_correct_Denv]
  \\ TRY ((
    rw []
    \\ eval_cases_tac
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, combine_dec_result_eq_Rerr]
    \\ rveq \\ fs []
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ fs []
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ agrees_impl_tac
    \\ simp []
  ) \\ NO_TAC)
QED

Theorem v_rel_concrete_v:
  (! v. concrete_v v ==> v_rel es v v) /\
  (! vs. concrete_v_list vs ==> LIST_REL (v_rel es) vs vs)
Proof
  ho_match_mp_tac concrete_v_ind
  \\ simp []
  \\ Cases
  \\ simp []
QED

Theorem env_rel_concrete_v:
  nsAll (K concrete_v) env.v ==>
  env_rel (v_rel es) env env
Proof
  rw [env_rel_def]
  \\ imp_res_tac nsLookup_nsAll
  \\ fs [v_rel_concrete_v]
QED

Theorem neq_IMP_to_cases[local]:
  !y. (x <> y ==> P) ==> (x = y) \/ (x <> y)
Proof
  simp []
QED

Theorem less_sub_1_cases[local]:
  k <= clock /\ (k <= clock - 1 ==> P) ==>
  (k = clock \/ k <= clock - (1 : num))
Proof
  DECIDE_TAC
QED

Theorem evaluate_record_suffix:
  (! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record ci s.eval_state /\
  k <= s.clock
  ==>
  let ev = evaluate (s with clock updated_by (\c. c - k)) env exps in
  (
  k <= s'.clock /\
  ev = (s' with clock updated_by (\c. c - k), res)
  ) \/ (
  ? s''. ev = (s'', Rerr (Rabort Rtimeout_error)) /\
  record_forward s''.eval_state s'.eval_state
  ))
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record ci s.eval_state /\
  k <= s.clock
  ==>
  let ev = evaluate_match (s with clock updated_by (\c. c - k)) env x pes err_x in
  (
  k <= s'.clock /\
  ev = (s' with clock updated_by (\c. c - k), res)
  ) \/ (
  ? s''. ev = (s'', Rerr (Rabort Rtimeout_error)) /\
  record_forward s''.eval_state s'.eval_state
  ))
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record ci s.eval_state /\
  k <= s.clock
  ==>
  let ev = evaluate_decs (s with clock updated_by (\c. c - k)) env decs in
  (
  k <= s'.clock /\
  ev = (s' with clock updated_by (\c. c - k), res)
  ) \/ (
  ? s''. ev = (s'', Rerr (Rabort Rtimeout_error)) /\
  record_forward s''.eval_state s'.eval_state
  ))
Proof
  ho_match_mp_tac full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [full_evaluate_def]
  \\ rveq \\ fs []
  \\ simp [record_forward_refl]
  \\ fs [do_eval_res_def]
  \\ TRY( rename1 ‘getOpClass op’ \\ Cases_on ‘getOpClass op’)
  \\ eval_cases_tac
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, dec_clock_def]
  \\ rveq \\ fs []
  \\ imp_res_simp_tac evaluate_is_record_forward
  \\ fs []
  \\ TRY (drule_then imp_res_simp_tac insert_do_eval \\ fs [])
  \\ imp_res_simp_tac evaluate_is_record_forward
  \\ fs []
  \\ TRY (drule_then imp_res_simp_tac insert_declare_env)
  \\ TRY (drule_then (drule_then assume_tac) less_sub_1_cases \\ fs [])
  \\ fs [reset_env_generation_orac_eqs]
  \\ TRY (rpt (simp [record_forward_refl]
            \\ TRY DISJ2_TAC
            \\ drule_then irule record_forward_trans)
        \\ NO_TAC)
  \\ simp [combine_dec_result_def]
  >>~ [`getOpClass op = Force`]
  >- (
    gvs [AllCaseEqs(), dec_clock_def]
    \\ drule_then (drule_then assume_tac) less_sub_1_cases \\ gvs []
    \\ imp_res_simp_tac evaluate_is_record_forward \\ gvs [])
  >- (
    gvs [AllCaseEqs(), dec_clock_def]
    \\ imp_res_simp_tac evaluate_is_record_forward \\ gvs []
    >- (drule_then irule record_forward_trans \\ gvs [])
    >- (drule_then irule record_forward_trans \\ gvs [])
    >- (disj2_tac \\ drule_then irule record_forward_trans \\ gvs []))
QED

(* Constructs the oracle from an evaluation by using the recorded
   events, padding with null events if necessary. *)
Definition extract_oracle_def:
  extract_oracle s env decs n =
    case (OLEAST k. ?s' res.
      evaluate_decs (s with clock := k) env decs = (s', res) /\
        n < FST (FST ((orac_s (s'.eval_state)).oracle 0))
    ) of
    | NONE => NONE
    | SOME k =>
      let (s', _) = evaluate_decs (s with clock := k) env decs in
        SOME ((orac_s s'.eval_state).oracle (n + 1))
End

Theorem evaluate_decs_clock_record_common_prefix:
  evaluate_decs s env decs = (s', res) /\
  evaluate_decs (s with clock := k) env decs = (s'', res') /\
  is_record ^ci s.eval_state /\
  j < FST (FST ((orac_s s'.eval_state).oracle 0)) /\
  j < FST (FST ((orac_s s''.eval_state).oracle 0)) ==>
  (orac_s s'.eval_state).oracle (j + 1) =
    (orac_s s''.eval_state).oracle (j + 1)
Proof
  rw []
  \\ `? s_pre ck. s = (s_pre with clock := ck)`
    by (qexists_tac `s` \\ simp [state_component_equality])
  \\ fs []
  \\ Cases_on `ck <= k`
  >- (
    qspec_then `ci` drule
        (List.last (CONJUNCTS evaluate_record_suffix) |> Q.GEN `ci`)
    \\ simp []
    \\ disch_then drule
    \\ disch_then (qspec_then `k - ck` mp_tac)
    \\ rw []
    \\ fs []
    \\ qspec_then `ci` imp_res_simp_tac
        (evaluate_is_record_forward |> Q.GEN `ci`)
    \\ fs [record_forward_def]
    \\ imp_res_tac is_record_IMP
    \\ fs []
  )
  >- (
    qpat_x_assum `evaluate_decs _ _ _ = _` mp_tac
    \\ qspec_then `ci` drule
        (List.last (CONJUNCTS evaluate_record_suffix) |> Q.GEN `ci`)
    \\ simp []
    \\ disch_then (qspec_then `ck - k` mp_tac)
    \\ disch_then drule
    \\ rw []
    \\ fs []
    \\ qspec_then `ci` imp_res_simp_tac
        (evaluate_is_record_forward |> Q.GEN `ci`)
    \\ fs [record_forward_def]
    \\ imp_res_tac is_record_IMP
    \\ fs []
  )
QED

Theorem recorded_orac_wf_defined[local]:
  recorded_orac_wf compiler orac /\
  i <= FST (FST (orac 0)) /\
  0 < i ==>
  compiler (orac i) <> NONE
Proof
  rw [recorded_orac_wf_def]
  \\ Cases_on `i = FST (FST (orac 0))`
  \\ fs []
  \\ first_x_assum (qspec_then `i` mp_tac)
  \\ simp [PULL_EXISTS]
QED

Theorem extract_oracle_agrees:
  evaluate_decs (t with clock := k) env decs = (t', res) /\
  s_rel ^ci s t /\
  (!i r. extract_oracle t env decs i = SOME r /\ ci_comp ci r <> NONE ==>
    orac i = r) ==>
  orac_agrees orac (t'.eval_state)
Proof
  rw [s_rel_def, orac_agrees_def]
  \\ `is_record ci (SOME (EvalOracle orac_s'))`
    by (simp [is_record_def] )
  \\ imp_res_simp_tac evaluate_is_record_forward
  \\ imp_res_simp_tac is_record_IMP
  \\ fs []
  \\ rw []
  \\ first_x_assum (qspec_then `j` mp_tac)
  \\ simp [extract_oracle_def]
  \\ DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO
  \\ rpt strip_tac
  >- (
    first_x_assum (qspec_then `k` mp_tac)
    \\ fs []
  )
  >- (
    first_x_assum irule
    \\ fs []
    \\ dxrule evaluate_decs_clock_record_common_prefix
    \\ simp []
    \\ rpt (disch_then drule)
    \\ rw []
    \\ rfs []
    \\ drule_then irule recorded_orac_wf_defined
    \\ simp []
  )
QED

Definition get_oracle_def:
  get_oracle ci s env decs =
    let es_record = EvalOracle <|
      oracle := K ((0,0), ci.config_v ci.init_state, []);
      custom_do_eval := do_eval_record ci;
      envs := [[]]; generation := 0|> in
    extract_oracle (s with eval_state := SOME es_record) env decs
End

Definition put_oracle_def:
  put_oracle ci orac = (insert_oracle ci orac
    (SOME (EvalOracle <| oracle := K ((0,0), ci.config_v ci.init_state, []);
      custom_do_eval := do_eval_record ci;
      envs := [[]]; generation := 0|>))
  )
End

Theorem result_rel_IMP_cases:
  result_rel r_rel e_rel r r' ==>
  ((?x. r = Rval x) \/ (?y. r = Rerr (Rraise y)) \/ (?a. r = Rerr (Rabort a)))
Proof
  Cases_on `r` \\ simp []
  \\ Cases_on `e` \\ simp []
QED

Theorem s_rel_clock2[local]:
  !k. s_rel ci s t ==> s_rel ci (s with clock := k) (t with clock := k)
Proof
  rw [s_rel_def]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ simp []
QED

Definition precond_eval_state_def:
  precond_eval_state orac ci s env decs = (case s.eval_state of
    | NONE => T
    | SOME (EvalDecs eds) => EvalDecs eds = mk_init_eval_state ci /\
        (orac_extended_wf (ci_comp ci) orac) /\
        (!i r x. get_oracle ci s env decs i = SOME r /\ ci_comp ci r = SOME x ==>
            orac i = r)
    | SOME (EvalOracle _) => F
  )
End

Theorem extract_oracle_SOME_SUC[local]:
  IS_SOME (extract_oracle s env decs (SUC i)) ==>
  IS_SOME (extract_oracle s env decs i)
Proof
  simp [extract_oracle_def]
  \\ DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO
  \\ DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO
  \\ rw []
  \\ simp [UNCURRY]
  \\ res_tac
  \\ simp []
QED

Theorem extract_oracle_0_st[local]:
  extract_oracle t env decs 0 = SOME r /\
  ~ semantics_prog s env decs Fail /\
  s_rel ci s t /\
  nsAll (K concrete_v) env.v ==>
  FST (SND r) = ci.config_v ci.init_state
Proof
  simp [extract_oracle_def]
  \\ DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO
  \\ simp [UNCURRY]
  \\ rw []
  \\ Cases_on `evaluate_decs (s with clock := n) env decs`
  \\ drule_then (qspec_then `n` assume_tac) s_rel_clock2
  \\ qspec_then `ci` drule
    (List.last (CONJUNCTS eval_simulation) |> Q.GEN `ci`)
  \\ disch_then drule
  \\ disch_then (qspec_then `env` mp_tac)
  \\ fs [semantics_prog_def, evaluate_prog_with_clock_def]
  \\ first_x_assum (qspec_then `n` mp_tac)
  \\ rw [env_rel_concrete_v]
  \\ rfs [s_rel_def]
  \\ fs []
QED

Theorem orac_agrees_s_rel_IMP[local]:
  orac_agrees orac t.eval_state ==>
  s_rel ci s t ==>
  i < FST (FST ((orac_s t.eval_state).oracle 0)) ==>
  orac i = (orac_s t.eval_state).oracle (i + 1)
Proof
  rw [s_rel_def, orac_agrees_def]
  \\ fs []
QED

Theorem extract_oracle_SUC_st[local]:
  IS_SOME (extract_oracle t env decs (SUC i)) /\
  s_rel ci s t /\
  nsAll (K concrete_v) env.v /\
  ~ semantics_prog s env decs Fail ==>
  ?r r' x. extract_oracle t env decs (SUC i) = SOME r' /\
  extract_oracle t env decs i = SOME r /\
  ci_comp ci r = SOME x /\
  FST (SND r') = FST x
Proof
  rw []
  \\ drule extract_oracle_SOME_SUC
  \\ fs [IS_SOME_EXISTS]
  \\ reverse (Cases_on `?n t' res. evaluate_decs (t with clock := n) env decs = (t', res) /\
        SUC i < FST (FST ((orac_s t'.eval_state).oracle 0))`)
  >- (
    rpt (POP_ASSUM (mp_tac o REWRITE_RULE [extract_oracle_def]))
    \\ DEEP_INTRO_TAC WhileTheory.OLEAST_INTRO
    \\ rw []
    \\ metis_tac []
  )
  \\ fs []
  \\ drule_then drule extract_oracle_agrees
  \\ disch_then (qspec_then `THE o extract_oracle t env decs` mp_tac)
  \\ Cases_on `evaluate_decs (s with clock := n) env decs`
  \\ drule_then (qspec_then `n` assume_tac) s_rel_clock2
  \\ qspec_then `ci` (drule_then drule)
    (List.last (CONJUNCTS eval_simulation) |> INST_TYPE [``:'a`` |-> ``:'nota``] |> Q.GEN `ci`)
  \\ disch_then (qspec_then `env` mp_tac)
  \\ fs [semantics_prog_def, evaluate_prog_with_clock_def]
  \\ first_x_assum (qspec_then `n` mp_tac)
  \\ rw [env_rel_concrete_v]
  \\ drule_then drule orac_agrees_s_rel_IMP
  \\ disch_then (fn t => qspec_then `i` mp_tac t \\ qspec_then `SUC i` mp_tac t)
  \\ qpat_x_assum `s_rel _ _ _` mp_tac
  \\ rw [s_rel_def]
  \\ fs [recorded_orac_wf_def]
  \\ first_x_assum drule
  \\ simp [ADD1]
QED

Theorem get_oracle_props:
  nsAll (K concrete_v) env.v /\
  s.refs = [] /\
  s.eval_state = SOME (mk_init_eval_state ci) /\
  ~ semantics_prog s env decs Fail ==>
  (!r. get_oracle ci s env decs 0 = SOME r ==>
    FST (SND r) = ci.config_v ci.init_state) /\
  (!i r'. get_oracle ci s env decs (SUC i) = SOME r' ==>
    (?r x. get_oracle ci s env decs i = SOME r /\ ci_comp ci r = SOME x /\
        FST (SND r') = FST x))
Proof
  simp [get_oracle_def]
  \\ qmatch_goalsub_abbrev_tac `extract_oracle t`
  \\ strip_tac
  \\ `s_rel ci s t` by
    fs [markerTheory.Abbrev_def, s_rel_def, state_component_equality,
        recorded_orac_wf_def, mk_init_eval_state_def]
  \\ rw []
  >- (
    drule_then (drule_then irule) extract_oracle_0_st
    \\ simp []
  )
  >- (
    drule_then drule
        (extract_oracle_SUC_st |> SIMP_RULE std_ss [IS_SOME_EXISTS, PULL_EXISTS])
    \\ simp []
  )
QED

Theorem evaluate_prog_with_clock_put_oracle:
  precond_eval_state orac ci s1 env decs /\
  evaluate_prog_with_clock s1 env k decs = (ffi, res) /\
  res <> Rerr (Rabort Rtype_error) /\
  s1.refs = [] /\
  nsAll (K concrete_v) env.v /\
  ~ semantics_prog s1 env decs Fail
  ==>
  ?res'.
  evaluate_prog_with_clock
    (s1 with eval_state := put_oracle ci orac)
    env k decs = (ffi, res') /\
  result_rel (K (K T)) (K (K T)) res res'
Proof

  simp [evaluate_prog_with_clock_def, precond_eval_state_def]
  \\ every_case_tac
  \\ rpt disch_tac
  \\ rpt (pairarg_tac \\ fs [])
  >- (
    imp_res_tac eval_no_eval_simulation
    \\ rfs []
    \\ rveq \\ fs []
    \\ rveq \\ fs []
  )
  \\ rveq \\ fs []
  \\ fs [get_oracle_def]
  \\ qmatch_asmsub_abbrev_tac `SOME (EvalOracle orac_st)`
  \\ `s_rel ci s1 (s1 with <| eval_state := SOME (EvalOracle orac_st) |>)`
  by ( unabbrev_all_tac
    \\ simp [s_rel_def, state_component_equality, recorded_orac_wf_def,
        mk_init_eval_state_def] )
  \\ `is_record ci (SOME (EvalOracle orac_st))`
    by ( fs [is_record_def, markerTheory.Abbrev_def] )
  \\ drule_then (qspec_then `k` assume_tac) s_rel_clock2
  \\ qspec_then `ci` (drule_then drule)
    (List.last (CONJUNCTS eval_simulation) |> INST_TYPE [``:'a`` |-> ``:'nota``] |> Q.GEN `ci`)
  \\ simp []

  \\ disch_then (qspec_then `env` mp_tac)
  \\ simp [env_rel_concrete_v]
  \\ disch_tac \\ fs []
  \\ qspec_then `ci` drule
    (List.last (CONJUNCTS insert_oracle_correct) |> Q.GEN `ci`)
  \\ fs [put_oracle_def]

  \\ disch_then (drule_then (qsubterm_then `evaluate_decs _ _` mp_tac))
  \\ simp []
  \\ reverse impl_tac
  >- (
    rw []
    \\ fs [s_rel_def]
    \\ imp_res_tac result_rel_IMP_cases \\ fs []
  )
  \\ rpt strip_tac \\ fs []
  \\ drule_then (drule_then irule) extract_oracle_agrees

  \\ simp [GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]
QED

Theorem oracle_semantics_prog:
  ~ semantics_prog s1 env decs Fail /\
  semantics_prog (s1 with eval_state := put_oracle ci orac)
    env decs outcome /\
  precond_eval_state orac ^ci s1 env decs /\
  s1.refs = [] /\
  nsAll (K concrete_v) env.v
  ==>
  semantics_prog s1 env decs outcome
Proof
  rw []
  \\ drule evaluate_prog_with_clock_put_oracle
  \\ simp [PAIR_FST_SND_EQ]
  \\ Cases_on `outcome` \\ fs [semantics_prog_def]
  >- (
    fs [PAIR_FST_SND_EQ]
    \\ rw [] \\ fs []
  )
  >- (
    disch_then (qspec_then `k` mp_tac)
    \\ rw [PAIR_FST_SND_EQ]
    \\ qexists_tac `k`
    \\ imp_res_tac result_rel_IMP_cases \\ fs [] \\ fs []
  )
  >- (
    qexists_tac `k`
    \\ simp []
  )
QED

(* for use in source-to-source phases, a proof that the oracle can be adjusted
   by any stateless compiler *)

Definition adjust_oracle_def:
  adjust_oracle ci f es = (case es of
    NONE => es
  | SOME (EvalDecs _) => es
  | SOME (EvalOracle o_s) => SOME (EvalOracle
        (o_s with custom_do_eval := do_eval_oracle (ci_comp ci) f)))
End

Theorem adjust_oracle_insert_gen_oracle:
  adjust_oracle ci f (insert_gen_oracle ci g shift_f orac es) =
    insert_gen_oracle ci f shift_f orac es
Proof
  simp [insert_gen_oracle_def, adjust_oracle_def]
  \\ every_case_tac
  \\ simp [state_component_equality]
QED

Overload s_adjust_oracle[local] = ``\ci f s. s with eval_state updated_by (adjust_oracle ci f)``;

Definition is_insert_oracle_def:
  is_insert_oracle ci f es = (?es' shift_f orac. es = insert_gen_oracle ci f shift_f orac es')
End

Theorem is_insert_decs[local]:
  is_insert_oracle ci f (SOME (EvalDecs eds))
Proof
  simp [is_insert_oracle_def, insert_gen_oracle_def,
    Q.ISPEC `SOME _` EQ_SYM_EQ, option_case_eq, eval_state_case_eq]
  \\ dsimp []
QED

Theorem do_eval_adjust[local]:
  do_eval vs es = SOME (env1, decs, es1) ∧
  is_insert_oracle ci f es ==>
  (do_eval vs (adjust_oracle ci (g o f) es) = SOME (env1, g decs, adjust_oracle ci (g o f) es1)
    ∨ do_eval vs (adjust_oracle ci (g o f) es) = SOME (env1, decs, adjust_oracle ci (g o f) es1))
  ∧
  is_insert_oracle ci f es1
Proof
  rw [do_eval_def]
  \\ fs [option_case_eq, eval_state_case_eq, list_case_eq, v_case_eq, pair_case_eq] \\ gvs []
  \\ fs [is_insert_decs]
  \\ simp [adjust_oracle_def]
  >- (
    fs [is_insert_oracle_def, insert_gen_oracle_def, Q.ISPEC `SOME _` EQ_SYM_EQ]
    \\ fs [option_case_eq, eval_state_case_eq] \\ gvs []
    \\ fs [do_eval_oracle_def, list_case_eq]
    \\ rpt (pairarg_tac \\ fs [])
    \\ gvs [option_case_eq, pair_case_eq, bool_case_eq]
    \\ Cases_on `env_id`
    \\ fs [lookup_env_def]
    \\ simp [add_env_generation_def]
  )
  >- (
    fs [is_insert_oracle_def, insert_gen_oracle_def, Q.ISPEC `SOME _` EQ_SYM_EQ]
    \\ fs [option_case_eq, eval_state_case_eq] \\ gvs []
    \\ simp [add_env_generation_def]
    \\ dsimp []
    \\ qexists_tac `\_. 0`
    \\ simp [Q.SPEC `0` shift_seq_def, ETA_THM]
    \\ irule_at Any EQ_REFL
  )
QED

Theorem declare_env_adjust[local]:
  declare_env (adjust_oracle ci f es) env = (case declare_env es env of
    NONE => NONE
  | SOME (x, es2) => SOME (x, adjust_oracle ci f es2))
Proof
  simp [adjust_oracle_def, declare_env_def]
  \\ every_case_tac
  \\ fs []
QED

Theorem adjust_oracle_reset[local]:
  adjust_oracle ci f (reset_env_generation es1 es2) =
    reset_env_generation (adjust_oracle ci f es1) (adjust_oracle ci f es2)
Proof
  simp [adjust_oracle_def, reset_env_generation_def]
  \\ every_case_tac
  \\ fs []
QED

Theorem is_insert_related[local]:
  is_insert_oracle ci f (SOME (EvalOracle es)) ==>
  (es2.custom_do_eval = es.custom_do_eval /\ es2.oracle = es.oracle) ==>
  is_insert_oracle ci f (SOME (EvalOracle es2))
Proof
  rw [is_insert_oracle_def, insert_gen_oracle_def, Q.ISPEC `SOME _` EQ_SYM_EQ]
  \\ fs [option_case_eq, eval_state_case_eq] \\ gvs []
  \\ dsimp []
  \\ simp [eval_oracle_state_component_equality]
  \\ qexists_tac `\_. 0`
  \\ simp [Q.SPEC `0` shift_seq_def, ETA_THM]
  \\ irule_at (Pat `_.generation = _`) EQ_REFL
  \\ simp []
QED

Theorem is_insert_reset[local]:
  is_insert_oracle ci f (reset_env_generation es1 es2) = is_insert_oracle ci f es2
Proof
  simp [reset_env_generation_def]
  \\ every_case_tac
  \\ fs [is_insert_decs]
  \\ EQ_TAC \\ rw []
  \\ drule_then irule is_insert_related
  \\ fs []
QED

Theorem declare_env_is_insert[local]:
  declare_env es env = SOME (x, es2) /\
  is_insert_oracle ci f es ==>
  is_insert_oracle ci f es2
Proof
  rw [declare_env_def]
  \\ fs [option_case_eq, eval_state_case_eq, pair_case_eq] \\ gvs []
  \\ fs [is_insert_decs]
  \\ drule_then irule is_insert_related
  \\ fs []
QED

Theorem adjust_oracle_evaluate:
  (∀ ^s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate_decs s env (compile_decs ds) = (s', res)) ⇒
  (∀ ^s env exps s' res.
    evaluate s env exps = (s', res) ∧
    is_insert_oracle ci f s.eval_state ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      is_insert_oracle ci f s'.eval_state ∧
      evaluate (s_adjust_oracle ci (compile_decs o f) s) env exps =
          (s_adjust_oracle ci (compile_decs o f) s', res)) ∧
  (∀ ^s env x pes err_x s' res.
    evaluate_match s env x pes err_x = (s', res) ∧
    is_insert_oracle ci f s.eval_state ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      is_insert_oracle ci f s'.eval_state ∧
      evaluate_match (s_adjust_oracle ci (compile_decs o f) s) env x pes err_x =
          (s_adjust_oracle ci (compile_decs o f) s', res)) ∧
  (∀ ^s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    is_insert_oracle ci f s.eval_state ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      is_insert_oracle ci f s'.eval_state ∧
      evaluate_decs (s_adjust_oracle ci (compile_decs o f) s) env ds =
          (s_adjust_oracle ci (compile_decs o f) s', res))
Proof
  disch_tac
  \\ ho_match_mp_tac (name_ind_cases [] full_evaluate_ind)
  \\ fs [full_evaluate_def]
  \\ rpt conj_tac
  \\ rpt (pairarg_tac \\ gvs [])
  >~ [`Case [App _ _]`] >- (
    rpt (gen_tac ORELSE disch_tac)
    \\ (fs [pair_case_eq, result_case_eq] \\ rveq \\ fs [])
    \\ reverse (Cases_on `getOpClass op = EvalOp`)
    >- (
      fs [astTheory.op_class_case_eq]
      \\ fs [bool_case_eq, Q.ISPEC `(a, b)` EQ_SYM_EQ]
      \\ gvs []
      >~ [`getOpClass op = Force`] >- gvs [AllCaseEqs(), dec_clock_def]
      \\ fs [option_case_eq, pair_case_eq, bool_case_eq, result_case_eq]
      \\ insts_tac
      \\ fs [dec_clock_def]
    )
    (* Eval *)
    \\ fs [do_eval_res_def]
    \\ fs [pair_case_eq, result_case_eq, option_case_eq] \\ gvs []
    \\ drule_then drule do_eval_adjust
    \\ disch_then (qspec_then `compile_decs` assume_tac)
    \\ simp []
    \\ fs [bool_case_eq] \\ gvs []
    \\ fs [dec_clock_def]
    \\ fs [pair_case_eq]
    \\ TRY (last_x_assum (irule_at Any))
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq, result_case_eq,
        option_case_eq, error_result_case_eq] \\ gvs []
    \\ fs [declare_env_adjust, adjust_oracle_reset, is_insert_reset]
    \\ drule declare_env_is_insert
    \\ simp []
  )
  >~ [`Case [Denv _]`] >- (
    rw []
    \\ fs [option_case_eq, pair_case_eq] \\ gvs []
    \\ simp [declare_env_adjust]
    \\ drule_then irule declare_env_is_insert
    \\ simp []
  )
  (* brute force remaining goals *)
  \\ rw []
  \\ fs [pair_case_eq, option_case_eq, result_case_eq] \\ rveq \\ fs []
  \\ eval_cases_tac
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, combine_dec_result_eq_Rerr]
  \\ try (drule_then drule declare_env_is_insert)
  \\ fs [declare_env_adjust]
QED

Theorem adjust_oracle_ev_decs[local] =
  adjust_oracle_evaluate |> UNDISCH |> CONJUNCTS |> List.last |> DISCH_ALL
    |> SIMP_RULE bool_ss [PULL_FORALL]
    |> Q.SPEC `s with clock := k`
    |> SIMP_RULE (srw_ss ()) []

Theorem adjust_oracle_semantics_prog:
  !compile f.
  (∀ ^s env ds s' res.
    evaluate_decs s env ds = (s', res) ∧
    res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate_decs s env (compile ds) = (s', res)) ⇒
  is_insert_oracle ci f ^s.eval_state ∧
  ¬ semantics_prog ^s env prog Fail ∧
  semantics_prog ^s env prog outcome ⇒
  semantics_prog (s_adjust_oracle ci (compile o f) ^s) env prog outcome
Proof
  Cases_on ‘outcome’ \\ gs [SF CONJ_ss]
  >~ [‘Terminate outcome tr’] >- (
    rw [semantics_prog_def]
    \\ gs [evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ gvs []
    \\ drule_then (drule_then drule) adjust_oracle_ev_decs
    \\ rw []
    \\ qexists_tac ‘k’ \\ simp [])
  >~ [‘Diverge tr’] >- (
    rw [semantics_prog_def]
    >- (
      first_x_assum (qspec_then ‘k’ strip_assume_tac)
      \\ gs [evaluate_prog_with_clock_def]
      \\ rpt (pairarg_tac \\ gvs [])
      \\ drule_then (drule_then drule) adjust_oracle_ev_decs
      \\ simp [])
    \\ qmatch_asmsub_abbrev_tac ‘IMAGE f1’
    \\ qmatch_goalsub_abbrev_tac ‘IMAGE f2’
    \\ ‘f1 = f2’
      suffices_by (rw [] \\ gs [])
    \\ unabbrev_all_tac
    \\ rw [FUN_EQ_THM]
    \\ gs [evaluate_prog_with_clock_def]
    \\ rpt (pairarg_tac \\ gs [])
    \\ last_x_assum (qspec_then ‘k’ assume_tac) \\ gs []
    \\ drule_then (drule_then drule) adjust_oracle_ev_decs
    \\ simp []
  )
QED
