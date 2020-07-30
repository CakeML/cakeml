(*
  Proofs that the source_eval attachment of the compiler
  preserves semantics, and that the oracle semantics can
  be introduced
*)

open preamble semanticsTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     source_evalTheory evaluatePropsTheory evaluateTheory
     experimentalLib

val _ = new_theory "source_evalProof";

val _ = set_grammar_ancestry ["ast", "source_eval", "string",
    "semantics", "semanticPrimitivesProps"];

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
  do_eval_record f init_state vs (orac : eval_oracle_fun) = case vs of
    | [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] =>
      let ((i, _), st, _) = orac 0 in
      (case (v_to_env_id env_id_v, v_to_decs decs_v) of
      | (SOME env_id, SOME decs) =>
        if compiler_agrees f (env_id, st_v, decs) (st_v2, bs_v, ws_v)
          /\ (if i = 0 then init_state st_v else st_v = st)
        then
        let orac' = \j. if j = 0 then ((i + 1, 0), st_v2, [])
          else if j = SUC i then (env_id, st_v, decs)
          else orac j in SOME (env_id, orac', decs)
        else NONE
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


(* various trivia *)

Triviality alist_to_ns_to_bind2 = GEN_ALL nsAppend_to_nsBindList
    |> Q.SPEC `nsEmpty`
    |> REWRITE_RULE [namespacePropsTheory.nsAppend_nsEmpty]

Triviality nsSing_eq_bind = namespaceTheory.nsSing_def
  |> REWRITE_RULE [GSYM namespaceTheory.nsBind_def,
    GSYM namespaceTheory.nsEmpty_def]

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
  (v_rel es (Loc n) (Loc n))
End

Theorem v_rel_l_simps =
  [``v_rel es (Litv l) v``, ``v_rel es (Conv cn vs) v``,
    ``v_rel es (Loc l) v``, ``v_rel es (Vectorv vs) v``,
    ``v_rel es (Env e id) v``, ``v_rel es (Recclosure env funs nm) v``,
    ``v_rel es (Closure env nm x) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ

Theorem v_rel_Boolv:
  v_rel es (Boolv b) v = (v = Boolv b)
Proof
  rw [Boolv_def, v_rel_l_simps]
QED

val _ = bossLib.augment_srw_ss [rewrites [v_rel_l_simps, v_rel_Boolv]];

Definition s_rel_def:
  s_rel s s' <=>
  ? dec_s orac_s init_s refs'. s' = s with <| refs := refs';
    eval_state := SOME (EvalOracle orac_s) |> /\
  LIST_REL (sv_rel (v_rel orac_s)) s.refs refs' /\
  s.eval_state = SOME (EvalDecs dec_s) /\
  orac_s.custom_do_eval = do_eval_record dec_s.compiler init_s /\
  dec_s.compiler_state = (if FST (FST (orac_s.oracle 0)) = 0
    then init_s else ((=) (FST (SND (orac_s.oracle 0))))) /\
  dec_s.env_id_counter = (orac_s.generation,
        LENGTH (EL orac_s.generation orac_s.envs), LENGTH orac_s.envs) /\
  orac_s.generation < LENGTH orac_s.envs
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
  s_rel s t /\ j = i /\ es = orac_s t.eval_state ==>
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
  s_rel s t /\ es = orac_s t.eval_state /\ env_rel (v_rel es) env env' ==>
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
  \\ ho_match_mp_tac terminationTheory.pmatch_ind
  \\ rw [terminationTheory.pmatch_def, match_result_rel_def,
    quotient_pairTheory.PAIR_REL_THM, compile_pat_def]
  \\ rveq \\ fs []
  \\ imp_res_tac v_to_env_id_SOME
  \\ fs [terminationTheory.pmatch_def]
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

Triviality pmatch_use = UNDISCH_ALL pmatch |> CONJUNCT1 |> SPEC_ALL
  |> Q.INST [`binds` |-> `[]`]
  |> DISCH_ALL |> GEN_ALL
  |> SIMP_RULE list_ss []

Theorem can_pmatch_all:
  can_pmatch_all env.c s.refs pats x /\
  s_rel s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  v_rel (orac_s t.eval_state) x y ==>
  can_pmatch_all env'.c t.refs pats y
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
  ho_match_mp_tac terminationTheory.do_eq_ind
  \\ rw [terminationTheory.do_eq_def]
  \\ rw [terminationTheory.do_eq_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ imp_res_tac v_to_env_id_SOME
  \\ rveq \\ fs []
  \\ fs [eq_result_case_eq, bool_case_eq]
  \\ fs [terminationTheory.do_eq_def, nat_to_v_def, lit_same_type_def]
  \\ rw []
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
  \\ qexists_tac `init_s`
  \\ simp []
QED

Triviality build_tdefs_helper:
  <| v := nsEmpty; c := nsAppend a b |> = extend_dec_env
      <| v := nsEmpty; c := a |> <| v := nsEmpty; c := b |>
Proof
  simp [extend_dec_env_def]
QED

Theorem build_tdefs:
  !tds n n2. n = n2 ==>
    env_rel R
        <|v := nsEmpty; c := build_tdefs n tds|>
        <|v := nsEmpty; c := build_tdefs n2 tds|>
Proof
  Induct
  \\ simp [build_tdefs_def, FORALL_PROD]
  \\ rw []
  \\ simp [build_tdefs_helper]
  \\ irule env_rel_extend_dec_env
  \\ simp [build_constrs_def, MAP_MAP_o, o_DEF, ELIM_UNCURRY]
  \\ simp [env_rel_def, MEM_MAP, PULL_EXISTS]
  \\ simp [nsLookup_alist_to_ns_some, PULL_EXISTS]
QED

Theorem v1_size:
  !xs. v1_size xs = SUM (MAP v_size xs) + LENGTH xs
Proof
  Induct \\ simp [v_size_def]
QED

Definition concrete_v_def:
  concrete_v (Vectorv xs) = EVERY concrete_v xs /\
  concrete_v (Conv stmp xs) = EVERY concrete_v xs /\
  concrete_v (Litv l) = T /\
  concrete_v (Loc l) = T /\
  concrete_v _ = F
Termination
  WF_REL_TAC `measure v_size`
  \\ rw [v_size_def, v1_size]
  \\ fs [MEM_SPLIT, SUM_APPEND]
End

Theorem concrete_v_rel:
  !x y. v_rel es x y ==> concrete_v x ==> y = x
Proof
  ho_match_mp_tac v_rel_ind
  \\ rw [concrete_v_def]
  \\ fs [EVERY_EL, LIST_REL_EL_EQN, LIST_EQ_REWRITE]
QED

Theorem v_to_decs:
  v_to_decs x = SOME decs /\
  v_rel es x y ==>
  v_to_decs y = SOME decs
Proof
  cheat
QED

Theorem compiler_agrees:
  compiler_agrees f (id, st_v, decs) (st_v2, bs_v, ws_v) /\
  v_rel es st_v st_v3 /\ v_rel es st_v2 st_v4 /\
  v_rel es bs_v bs_v2 /\ v_rel es ws_v ws_v2 ==>
  compiler_agrees f (id, st_v3, decs) (st_v4, bs_v2, ws_v2) /\
  concrete_v st_v /\ concrete_v st_v2 /\ concrete_v bs_v /\ concrete_v ws_v
Proof
  cheat
QED

Theorem do_eval:
  do_eval (REVERSE xs) s.eval_state = SOME (env, decs, es) /\
  s_rel s t /\
  LIST_REL (v_rel (orac_s t.eval_state)) xs ys ==>
  ? env' es'.
  do_eval (REVERSE ys) t.eval_state = SOME (env', decs, es') /\
  es_forward (orac_s t.eval_state) (orac_s es') /\
  env_rel (v_rel (orac_s es')) env env' /\
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
  \\ drule compiler_agrees
  \\ rpt (disch_then drule)
  \\ disch_tac
  \\ fs [ELIM_UNCURRY]
  \\ imp_res_tac concrete_v_rel
  \\ rveq \\ fs []
  \\ simp [add_env_generation_def, add_decs_generation_def, PULL_EXISTS]
  \\ simp [EL_APPEND_EQN]
  \\ qexists_tac `init_s`
  \\ simp []
  \\ qmatch_goalsub_abbrev_tac `es_forward cur_es new_es`
  \\ qsuff_tac `es_forward cur_es new_es`
  >- (
    rpt strip_tac \\ rw [] \\ fs []
    \\ imp_res_tac forward_rules
    \\ simp [FUN_EQ_THM, EQ_SYM_EQ]
  )
  \\ fs [markerTheory.Abbrev_def, es_forward_def]
  \\ simp [lookup_env_def, FORALL_PROD, lem_listTheory.list_index_def]
  \\ simp [bool_case_eq, option_case_eq, EL_APPEND_EQN]
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



(* case splits for evaluate proofs *)
val eval_cases_tac =
  fs [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
        option_case_eq, list_case_eq, exp_or_val_case_eq, match_result_case_eq]
  \\ rveq \\ fs []
  \\ imp_res_tac evaluate_sing
  \\ rveq \\ fs []

(* take a step of forward-consistency-type reasoning *)
val forward_tac = MAP_FIRST (drule_then irule)
    (es_forward_trans :: IMP_CANON forward_rules)

(* quantifier instantiation based on s_rel, v_rel etc *)
val insts_tac = rpt (FIRST ([
      do_xig_inst `s_rel X_s _`,
      do_xig_inst `env_rel (v_rel Ig_es) X_env _`,
      do_xig_inst `v_rel Ig_es X_v _`,
      CHANGED_TAC (rveq \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, es_forward_refl]
            \\ rfs []),
      forward_tac,
      first_x_assum (fn t => mp_tac t \\ (impl_tac THENL
            [rpt conj_tac \\ forward_tac, disch_tac])),
      conj_tac \\ forward_tac
    ]))


Theorem compile_correct:

  (! ^s env exps s' res es t env'.
  evaluate s env exps = (s', res) /\
  s_rel s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ? es' t' res'.
  evaluate t env' exps = (t', res') /\
  s_rel s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (LIST_REL (v_rel es')) (v_rel es') res res' /\
  es_forward (orac_s t.eval_state) es')
  /\
  (! ^s env x pes err_x s' res es t env' y err_y.
  evaluate_match s env x pes err_x = (s', res) /\
  s_rel s t /\
  es = orac_s t.eval_state /\
  env_rel (v_rel es) env env' /\
  v_rel es x y /\
  v_rel es err_x err_y /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_match t env' y pes err_y = (t', res') /\
  s_rel s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (LIST_REL (v_rel es')) (v_rel es') res res' /\
  es_forward es es')
  /\
  (! ^s env decs s' res t env'.
  evaluate_decs s env decs = (s', res) /\
  s_rel s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_decs t env' decs = (t', res') /\
  s_rel s' t' /\
  es' = orac_s t'.eval_state /\
  result_rel (env_rel (v_rel es')) (v_rel es') res res' /\
  es_forward (orac_s t.eval_state) es')

Proof

  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [terminationTheory.full_evaluate_def]
  \\ rveq \\ fs []
  >- (
    simp [es_forward_refl]
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
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [do_con_check_def, build_conv_def]
    \\ every_case_tac \\ fs [] \\ rveq \\ fs []
    \\ rfs [env_rel_def]
  )
  >- (
    eval_cases_tac
    \\ drule_then drule env_rel_nsLookup_v
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
    \\ insts_tac
    \\ Cases_on `op = Opapp`
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
      \\ simp [Once mk_matches_def, terminationTheory.evaluate_def]

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
    \\ fs [bind_exn_v_def]
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ simp [namespaceTheory.nsOptBind_def]
    \\ CASE_TAC \\ fs []
    \\ insts_tac
    \\ irule env_rel_add_nsBind
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [miscTheory.FST_triple, MAP_MAP_o]
    \\ fs [GSYM pairarg_to_pair_map, ELIM_UNCURRY, o_DEF, ETA_THM]
    \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_rel_add_nsBindList
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
    \\ drule_then (qsubterm_then `pmatch _ _ _ _ _` mp_tac) pmatch_use
    \\ rpt (disch_then drule)
    \\ eval_cases_tac
    \\ fs [match_result_rel_def]
    \\ rw []
    \\ insts_tac
    \\ first_x_assum (qsubterm_then `evaluate _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ simp [nsAppend_to_nsBindList]
    \\ irule env_rel_add_nsBindList
    \\ simp [nsAppend_to_nsBindList]
  )

  >- (
    insts_tac
  )

  >- (
    eval_cases_tac
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
  )

  >- (
    fs [bool_case_eq, pair_case_eq, result_case_eq]
    \\ insts_tac
    \\ imp_res_tac evaluate_sing
    \\ rveq \\ fs []
    \\ drule_then (qsubterm_then `pmatch _ _ _ _ _` mp_tac) pmatch_use
    (* FIXME: why doesn't this work?
    \\ disch_then (qsubterm_then `pmatch _ s'.refs _ _ _` mp_tac)
    *)
    \\ imp_res_tac (List.nth (CONJUNCTS forward_rules, 2))
    \\ rpt (disch_then drule)
    \\ every_case_tac \\ fs [match_result_rel_def, bind_exn_v_def]
    \\ rw [alist_to_ns_to_bind2]
    \\ irule env_rel_add_nsBindList
    \\ simp []
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ fs [miscTheory.FST_triple, MAP_MAP_o, o_DEF, ELIM_UNCURRY, ETA_THM]
    \\ simp [build_rec_env_merge, nsAppend_to_nsBindList]
    \\ irule env_rel_add_nsBindList
    \\ simp []
    \\ simp [LIST_REL_MAP1, SIMP_RULE (bool_ss ++ ETA_ss) [] LIST_REL_MAP2]
    \\ simp [quotient_pairTheory.PAIR_REL_THM, ELIM_UNCURRY]
    \\ simp [EVERY2_refl]
  )

  >- (
    eval_cases_tac
    \\ fs [EVERY_MEM, FORALL_PROD, MEM_MAP, EXISTS_PROD, PULL_EXISTS,
        terminationTheory.check_dup_ctors_thm]
    \\ fs [s_rel_def, state_component_equality]
    \\ simp [es_forward_refl]
    \\ qexists_tac `init_s`
    \\ simp []
  )

  >- (
    insts_tac
  )

  >- (
    (* Denv *)
    eval_cases_tac
    \\ fs [declare_env_def, s_rel_def]
    \\ rveq \\ fs []
    \\ fs [pair_case_eq]
    \\ rveq \\ fs []
    \\ simp [lem_listTheory.list_index_def]
    \\ simp [state_component_equality]
    \\ qmatch_goalsub_abbrev_tac `es_forward cur_es new_es`
    \\ qsuff_tac `es_forward cur_es new_es`
    >- (
      rpt strip_tac \\ insts_tac
      \\ TRY (qexists_tac `init_s` \\ simp [])
      \\ simp [EL_LUPDATE]
      \\ insts_tac
      \\ simp [nsSing_eq_bind]
      \\ irule env_rel_add_nsBind
      \\ simp [v_to_env_id_def, v_to_nat_def, nat_to_v_def]
      \\ fs [markerTheory.Abbrev_def, lookup_env_def,
            lem_listTheory.list_index_def, EL_LUPDATE, EL_APPEND_EQN]
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
    \\ qexists_tac `init_s` \\ simp []
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ irule env_rel_nsLift
    \\ fs [env_rel_def]
    \\ rw [] \\ res_tac
  )

  >- (
    eval_cases_tac
    \\ insts_tac
    \\ first_x_assum (qsubterm_then `evaluate_decs _ _ _` mp_tac)
    \\ impl_tac \\ rw [] \\ insts_tac
    \\ irule env_rel_extend_dec_env
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





