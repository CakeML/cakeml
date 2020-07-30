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

Theorem concrete_v_rel:
  !x y. v_rel es x y ==> concrete_v x ==> y = x
Proof
  ho_match_mp_tac v_rel_ind
  \\ rw []
  \\ fs [EVERY_EL, LIST_REL_EL_EQN, LIST_EQ_REWRITE]
QED

Theorem v_to_decs:
  v_to_decs x = SOME decs ==>
  concrete_v x
Proof
  cheat
QED

Theorem v_to_list_concrete:
  !x xs. v_to_list x = SOME xs ==>
  concrete_v x = EVERY concrete_v xs
Proof
  recInduct terminationTheory.v_to_list_ind
  \\ rw [terminationTheory.v_to_list_def]
  \\ fs [option_case_eq]
  \\ rveq \\ fs []
  \\ rfs []
QED

Theorem maybe_all_list_SOME:
  !xs ys. maybe_all_list xs = SOME ys ==> xs = MAP SOME ys
Proof
  Induct \\ simp [Once terminationTheory.maybe_all_list_def]
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

Theorem do_eval:
  do_eval (REVERSE xs) s.eval_state = SOME (env, decs, es) /\
  s_rel (s : 'a semanticPrimitives$state) t /\
  LIST_REL (v_rel (orac_s t.eval_state)) xs ys ==>
  ? env' es'.
  es_forward (orac_s t.eval_state) (orac_s es') /\
  do_eval (REVERSE ys) t.eval_state = SOME (env', decs, es') /\
  env_rel (v_rel (orac_s es')) env env' /\
  s_rel (s with eval_state := es) (t with eval_state := es') /\
  (! s2 t2. s_rel (s2 : 'a semanticPrimitives$state) t2 /\
    es_forward (orac_s es') (orac_s t2.eval_state) /\
    es_stack_forward (orac_s es') (orac_s t2.eval_state) ==>
    es_forward (orac_s t2.eval_state)
        (orac_s (reset_env_generation t.eval_state t2.eval_state)) /\
    s_rel
        (s2 with eval_state := reset_env_generation s.eval_state s2.eval_state)
        (t2 with eval_state := reset_env_generation t.eval_state t2.eval_state)
    /\
    es_stack_forward (orac_s t.eval_state)
        (orac_s (reset_env_generation t.eval_state t2.eval_state))
  )
Proof
  rw []
  \\ fs [do_eval_def, s_rel_def] \\ fs []
  \\ fs [list_case_eq, v_case_eq, option_case_eq]
  \\ fs [listTheory.SWAP_REVERSE_SYM]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ imp_res_tac v_to_decs
  \\ simp [do_eval_record_def, state_component_equality]
  \\ imp_res_tac compiler_agrees
  \\ imp_res_tac concrete_v_rel
  \\ fs [ELIM_UNCURRY]
  \\ rveq \\ fs []
  \\ simp [add_env_generation_def, add_decs_generation_def, PULL_EXISTS]
  \\ simp [EL_APPEND_EQN]
  \\ qexists_tac `init_s`
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, lem_listTheory.list_index_def]
    \\ simp [bool_case_eq, option_case_eq, EL_APPEND_EQN]
  )
  \\ rpt strip_tac \\ rw [] \\ fs []
  \\ imp_res_tac forward_rules
  \\ simp [FUN_EQ_THM, EQ_SYM_EQ]
  \\ fs [reset_env_generation_def]
  \\ qexists_tac `init_s'`
  \\ simp []
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, lem_listTheory.list_index_def]
  )
  \\ simp [EQ_SYM_EQ]
  \\ fs [es_stack_forward_def]
  \\ rfs [EL_APPEND_EQN]
QED

Theorem declare_env:
  declare_env s.eval_state env = SOME (v, es) /\
  s_rel s t /\
  env_rel (v_rel (orac_s t.eval_state)) env env' ==>
  ?v' es2.
  es_forward (orac_s t.eval_state) (orac_s es2) /\
  declare_env t.eval_state env' = SOME (v', es2) /\
  v_rel (orac_s es2) v v' /\
  s_rel (s with eval_state := es) (t with eval_state := es2) /\
  es_stack_forward (orac_s t.eval_state) (orac_s es2)
Proof
  rw [s_rel_def, declare_env_def]
  \\ fs []
  \\ rveq \\ fs []
  \\ simp [lem_listTheory.list_index_def, v_to_env_id_def,
        v_to_nat_def, nat_to_v_def, lookup_env_def, EL_LUPDATE]
  \\ simp [EL_APPEND_EQN]
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD, lem_listTheory.list_index_def]
    \\ simp [bool_case_eq, option_case_eq]
    \\ rw [EL_APPEND_EQN, EL_LUPDATE]
  )
  \\ simp [state_component_equality, PULL_EXISTS]
  \\ qexists_tac `init_s`
  \\ simp [es_stack_forward_def, EL_LUPDATE]
  \\ imp_res_tac forward_rules \\ fs []
QED

Theorem reset_env_generation:
  s_rel s t /\
  s_rel prior_s prior_t /\
  es_forward (orac_s prior_t.eval_state) (orac_s t.eval_state) ==>
  es_forward (orac_s t.eval_state)
    (orac_s (reset_env_generation prior_t.eval_state t.eval_state)) /\
  s_rel (s with eval_state := reset_env_generation prior_s.eval_state s.eval_state)
    (t with eval_state := reset_env_generation prior_t.eval_state t.eval_state)

Proof

  disch_tac \\ fs [s_rel_def]
  \\ rveq \\ fs []
  \\ fs [reset_env_generation_def, state_component_equality]
  \\ conj_asm1_tac
  >- (
    simp [es_forward_def]
    \\ simp [lookup_env_def, FORALL_PROD]
  )
  \\ qexists_tac `init_s`
  \\ simp []
  \\ rw []
  \\ TRY (imp_res_tac forward_rules \\ fs [es_forward_def] \\ NO_TAC)
  (* a "real issue" here, we need a stronger relation showing the lower frames
     of the env stack aren't extended *)
  \\ cheat

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

Triviality abort_imp_intro:
  (!v. x = Rval v ==> P) /\ (!e. x = Rerr (Rraise e) ==> P) ==>
  (~ abort x ==> P)
Proof
  simp [abort_def] \\ every_case_tac \\ simp []
QED

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
      do_xig_inst `s_rel X_s _`,
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
  es_forward (orac_s t.eval_state) es' /\
  (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es'))
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
  es_forward es es' /\
  (~ abort res' ==> es_stack_forward es es'))
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
  es_forward (orac_s t.eval_state) es' /\
  (~ abort res' ==> es_stack_forward (orac_s t.eval_state) es'))

Proof

  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [terminationTheory.full_evaluate_def]
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
      \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
      \\ drule_then (drule_then drule) do_eval
      \\ rw []
      \\ fs []
      \\ drule_then assume_tac s_rel_clock
      \\ fs [bool_case_eq] \\ rveq \\ fs []
      \\ insts_tac
      \\ fs [EVAL ``(dec_clock x).eval_state``]
      \\ eval_cases_tac
      \\ insts_tac
      \\ TRY (drule_then (qsubterm_then `declare_env _ _` mp_tac) declare_env
        \\ impl_tac \\ rw []
        \\ TRY (irule env_rel_extend_dec_env))
      \\ insts_tac
      \\ first_x_assum drule \\ impl_tac
      \\ rw [] \\ insts_tac
    )
    \\ eval_cases_tac
    \\ drule_then assume_tac do_app
    \\ insts_tac
    \\ fs [s_rel_def] \\ rveq \\ fs []
    \\ simp [state_component_equality]
    \\ qexists_tac `init_s'`
    \\ simp []
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
    \\ insts_tac
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
      \\ fs [markerTheory.Abbrev_def, es_stack_forward_def, EL_LUPDATE]
      \\ irule env_rel_add_nsBind
      \\ simp [v_to_env_id_def, v_to_nat_def, nat_to_v_def]
      \\ fs [markerTheory.Abbrev_def, lookup_env_def,
            lem_listTheory.list_index_def, EL_LUPDATE, EL_APPEND_EQN,
            es_stack_forward_def]
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

Definition do_eval_oracle_def:
  do_eval_oracle (compiler : compiler_fun) vs (orac : eval_oracle_fun) =
  case vs of
    | [env_id_v; st_v; decs_v; st_v2; bs_v; ws_v] =>
      let (env_id, st_v, decs) = orac 0 in
      (case compiler (env_id, st_v, decs), v_to_word8_list bs_v,
            v_to_word64_list ws_v of
        | (SOME (_, c_bs, c_ws), SOME bs, SOME ws) =>
            if bs = c_bs /\ ws = c_ws
            then SOME (env_id, shift_seq 1 orac, decs)
            else NONE
        | _ => NONE
      )
    | _ => NONE
End

Definition insert_oracle_def:
  insert_oracle f orac es = case es of
    | SOME (EvalOracle s) => SOME (EvalOracle (s with <|
        custom_do_eval := do_eval_oracle f ;
        oracle := shift_seq (FST (FST (s.oracle 0))) orac |>))
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

Definition is_record_def:
  is_record f es ⇔ case es of
    | SOME (EvalOracle s) =>
        ∃init_s. s.custom_do_eval = do_eval_record f init_s
    | _ => F
End

Theorem insert_do_eval:
  do_eval vs es = SOME (env, decs, es') /\
  is_record f es ==>
  is_record f es' /\
  record_forward es es' /\
  (orac_agrees orac es' ==>
  do_eval vs (insert_oracle f orac es) = SOME (env, decs,
    insert_oracle f orac es'))
Proof
  simp [is_record_def, Once do_eval_def]
  \\ disch_tac
  \\ fs [option_case_eq, eval_state_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ fs [PULL_EXISTS]
  \\ qexists_tac `init_s`
  \\ fs [do_eval_def, add_env_generation_def, insert_oracle_def]
  \\ fs [do_eval_record_def, list_case_eq, option_case_eq] \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs [])
  \\ fs [COND_EXPAND_IMP]
  \\ fs [compiler_agrees_def]
  \\ every_case_tac \\ fs []
  \\ simp [do_eval_oracle_def]
  \\ rveq \\ fs []
  \\ fs [record_forward_def, orac_agrees_def, shift_seq_def]
  \\ Cases_on `env_id` \\ fs [lookup_env_def]
QED

Theorem insert_declare_env:
  declare_env es1 env = SOME (x, es2) /\
  is_record f es1 ==>
  is_record f es2 /\
  record_forward es1 es2 /\
  (orac_agrees orac es2 ==>
  declare_env (insert_oracle f orac es1) env = SOME (x,
    insert_oracle f orac es2))
Proof
  simp [is_record_def, declare_env_def, insert_oracle_def]
  \\ every_case_tac \\ fs []
  \\ disch_tac
  \\ fs [] \\ rveq \\ fs []
  \\ simp [PULL_EXISTS]
  \\ qexists_tac `init_s`
  \\ simp [record_forward_def]
QED

Theorem reset_env_generation_orac_eqs:
  (is_record f (reset_env_generation es2 es3) = is_record f es3) ∧
  (record_forward es1 (reset_env_generation es2 es3) = record_forward es1 es3) ∧
  (orac_agrees orac (reset_env_generation es2 es3) = orac_agrees orac es3) ∧
  (reset_env_generation (insert_oracle f orac es1) es2 =
    reset_env_generation es1 es2) ∧
  (reset_env_generation es1 (insert_oracle f orac es2) =
    insert_oracle f orac (reset_env_generation es1 es2))
Proof
  simp [is_record_def, reset_env_generation_def, insert_oracle_def]
  \\ every_case_tac \\ fs []
  \\ simp [record_forward_def, orac_agrees_def]
QED

Triviality record_forward_trans_sym
  = REWRITE_RULE [Once CONJ_COMM] record_forward_trans

Theorem evaluate_is_record_forward:
  (! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record f s.eval_state
  ==>
  is_record f s'.eval_state /\
  record_forward s.eval_state s'.eval_state)
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record f s.eval_state
  ==>
  is_record f s'.eval_state /\
  record_forward s.eval_state s'.eval_state)
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record f s.eval_state
  ==>
  is_record f s'.eval_state /\
  record_forward s.eval_state s'.eval_state)
Proof
  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [compile_exp_def, compile_dec_def, terminationTheory.full_evaluate_def]
  \\ rveq \\ fs []
  \\ simp [record_forward_refl]
  \\ fs [pair_case_eq, option_case_eq, result_case_eq] \\ rveq \\ fs []
  \\ fs [bool_case_eq] \\ rveq \\ fs []
  \\ simp [record_forward_refl]
  \\ fs [dec_clock_def, do_eval_res_def]
  \\ eval_cases_tac
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ]
  \\ rpt (drule_then irule record_forward_trans_sym)
  \\ simp [record_forward_refl]
  \\ TRY (drule_then (drule_then assume_tac) insert_do_eval)
  \\ fs [GSYM PULL_FORALL]
  \\ TRY (drule_then (drule_then assume_tac) insert_declare_env)
  \\ fs [GSYM PULL_FORALL, reset_env_generation_orac_eqs] 
  \\ rpt (drule_then irule record_forward_trans_sym)
  \\ simp [record_forward_refl]
QED

Definition Case_def:
  Case X <=> T
End

Theorem elim_Case:
  (Case X /\ Y) = Y /\
  (Case X ==> Y) = Y
Proof
  simp [Case_def]
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

val agrees_tac = (drule_then irule orac_agrees_backward)
  \\ rpt (simp_tac bool_ss [record_forward_refl]
    \\ drule_then irule record_forward_trans_sym)

val agrees_impl_tac = rpt ((qpat_x_assum `orac_agrees _ _ ==> _` mp_tac
    \\ impl_tac)
  >- agrees_tac)

fun imp_res_simp_tac t = IMP_RES_THEN mp_tac t
  \\ simp []
  \\ rpt ((disch_then drule \\ simp []) ORELSE disch_then
      (fn t => if is_forall (concl t) then all_tac else assume_tac t))

val insert_oracle_correct_setup = setup (
  `(! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record f s.eval_state /\
  orac_agrees orac s'.eval_state /\
  Case (Let, exps) /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  evaluate (s with eval_state updated_by insert_oracle f orac) env exps =
  (s' with eval_state updated_by insert_oracle f orac, res)
  )
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record f s.eval_state /\
  orac_agrees orac s'.eval_state /\
  Case (Mat, pes) /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  evaluate_match (s with eval_state updated_by insert_oracle f orac)
    env x pes err_x =
  (s' with eval_state updated_by insert_oracle f orac, res)
  )
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record f s.eval_state /\
  orac_agrees orac s'.eval_state /\
  Case (Dlet, decs) /\
  res <> Rerr (Rabort Rtype_error)
  ==>
  evaluate_decs (s with eval_state updated_by insert_oracle f orac) env decs =
  (s' with eval_state updated_by insert_oracle f orac, res)
  )`,
  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [compile_exp_def, compile_dec_def, terminationTheory.full_evaluate_def]
  \\ fs [elim_Case]
  \\ rveq \\ fs []
  );

Triviality insert_oracle_correct_App:
  ^(#get_goal insert_oracle_correct_setup `Case (_, [App _ _])`)
Proof
  rw []
  \\ fs [pair_case_eq, result_case_eq] \\ rveq \\ fs []
  \\ fs [bool_case_eq] \\ rveq \\ fs []
  >- (
    (* Opapp *)
    eval_cases_tac
    \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] \\ rveq \\ fs []
    \\ fs [dec_clock_def]
    \\ imp_res_simp_tac evaluate_is_record_forward
    \\ agrees_impl_tac
    \\ simp []
  )
  >- (
    (* Eval *)
    fs [do_eval_res_def, Q.ISPEC `(a, b)` EQ_SYM_EQ, pair_case_eq]
    \\ rveq \\ fs []
    \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
    \\ drule insert_do_eval
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [`orac`, `f`] mp_tac)
    \\ rw []
    \\ imp_res_simp_tac evaluate_is_record_forward
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
    eval_cases_tac
  )
QED

Triviality insert_oracle_correct_Denv:
  ^(#get_goal insert_oracle_correct_setup `Case (_, [Denv _])`)
Proof
  rw []
  \\ fs [option_case_eq, pair_case_eq] \\ rveq \\ fs []
  \\ imp_res_simp_tac insert_declare_env
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
  cheat
QED

Theorem env_rel_concrete_v:
  nsAll (K concrete_v) env.v ==>
  env_rel (v_rel es) env env
Proof
  rw [env_rel_def]
  \\ imp_res_tac nsLookup_nsAll
  \\ fs [v_rel_concrete_v]
QED

Triviality neq_IMP_to_cases:
  !y. (x <> y ==> P) ==> (x = y) \/ (x <> y)
Proof
  simp []
QED

Theorem evaluate_record_suffix:
  (! ^s env exps s' res.
  evaluate s env exps = (s', res) /\
  is_record f s.eval_state /\
  k <= s.clock
  ==>
  let ev = evaluate (s with clock updated_by ((-) k)) env exps in
  (
  k <= s'.clock /\
  ev = (s' with clock updated_by ((-) k), res)
  ) \/ (
  ? s''. ev = (s'', Rerr (Rabort Rtimeout_error)) /\
  record_forward s''.eval_state s'.eval_state
  ))
  /\
  (! ^s env x pes err_x s' res.
  evaluate_match s env x pes err_x = (s', res) /\
  is_record f s.eval_state /\
  k <= s.clock
  ==>
  let ev = evaluate_match (s with clock updated_by ((-) k)) env x pes err_x in
  (
  k <= s'.clock /\
  ev = (s' with clock updated_by ((-) k), res)
  ) \/ (
  ? s''. ev = (s'', Rerr (Rabort Rtimeout_error)) /\
  record_forward s''.eval_state s'.eval_state
  ))
  /\
  (! ^s env decs s' res.
  evaluate_decs s env decs = (s', res) /\
  is_record f s.eval_state /\
  k <= s.clock
  ==>
  let ev = evaluate_decs (s with clock updated_by ((-) k)) env decs in
  (
  k <= s'.clock /\
  ev = (s' with clock updated_by ((-) k), res)
  ) \/ (
  ? s''. ev = (s'', Rerr (Rabort Rtimeout_error)) /\
  record_forward s''.eval_state s'.eval_state
  ))
Proof
  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rpt conj_tac
  \\ rpt (gen_tac ORELSE disch_tac)
  \\ fs [compile_exp_def, compile_dec_def, terminationTheory.full_evaluate_def]
  \\ rveq \\ fs []
  \\ simp [record_forward_refl]
  \\ fs [do_eval_res_def]
  \\ eval_cases_tac
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, dec_clock_def]
  \\ rveq \\ fs []
  \\ imp_res_simp_tac evaluate_is_record_forward
  \\ fs []
  \\ imp_res_simp_tac insert_do_eval
  \\ fs []
  \\ imp_res_simp_tac evaluate_is_record_forward
  \\ fs []
  \\ imp_res_simp_tac insert_declare_env
  \\ fs [reset_env_generation_orac_eqs]
  \\ TRY (rpt (simp [record_forward_refl]
            \\ TRY DISJ2_TAC
            \\ drule_then irule record_forward_trans)
        \\ NO_TAC)
  \\ simp [combine_dec_result_def]
QED



Definition mk_good_orac_def:
  mk_good_orac compiler recorded_orac (n : num) =
  if n < FST (FST (recorded_orac 0))
  then recorded_orac (n + 1)
  else if n = 0
  then ARB
  else case compiler (mk_good_orac compiler recorded_orac (n - 1)) of
    | NONE => ARB
    | SOME (_, st, _) => ((0, 0), st, [])
End

semantics_prog_def |> SIMP_RULE (srw_ss ()) []
  concl |>
  


Theorem oracle_semantics_prog:

  semantics_prog s1 env decs outcome /\
  outcome <> Fail /\
  s1.eval_state = SOME (EvalDecs eds) /\
  s1.refs = [] /\
  nsAll (K concrete_v) env.v /\
  eds.env_id_counter = (0, 0, 1) ==>
  ? orac_s. 
  semantics_prog (s1 with eval_state := SOME (EvalOracle orac_s)) env decs
    outcome /\
  orac_s.custom_do_eval = do_eval_oracle eds.compiler /\
  eds.compiler_state (FST (SND (orac_s.oracle 0)))

Proof

  Cases_on `outcome` \\ rw [semantics_prog_def]

  >- (
    (* diverge case *)

  print_match [] ``semantics_prog``;



  precondition1 interp s1 env1 genv conf eval_conf prog ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog
      (semantics eval_conf s1.ffi
          (SND (compile_prog conf prog)))



Theorem evaluate_decs_choose_oracle:
  evaluate_decs s env decs = (s', res) /\
  s.eval_state = SOME (EvalDecs eds) /\
  s.refs = [] /\
  nsAll (K concrete_v) env.v /\
  eds.env_id_counter = (0,0,1) /\
  res <> Rerr (Rabort Rtype_error) ==>
  ? orac_s s'' res'.
  evaluate_decs (s with eval_state := SOME (EvalOracle orac_s)) env decs =
    (s'', res') /\
  orac_s.custom_do_eval = do_eval_oracle eds.compiler /\
  eds.compiler_state (FST (SND (orac_s.oracle 0))) /\
  s''.ffi = s'.ffi /\ s''.clock = s'.clock /\
  result_rel (env_rel (\v v'. concrete_v v ==> v' = v))
    (\v v'. concrete_v v ==> v' = v) res res'

Proof

  rw []
  \\ qabbrev_tac `orac_1 = <|
    oracle := K ((0, 0), Conv NONE [], []) ;
    custom_do_eval := do_eval_record eds.compiler eds.compiler_state ;
    envs := [[]] ;
    generation := 0 |>`
  \\ `s_rel s (s with eval_state := SOME (EvalOracle orac_1))`
  by ( unabbrev_all_tac \\ simp [s_rel_def, state_component_equality] )
  \\ drule_then (qspec_then `orac_1` assume_tac) env_rel_concrete_v
  \\ drule_then drule (List.last (CONJUNCTS compile_correct))
  \\ simp []
  \\ disch_then drule
  \\ rw []
  \\ drule (List.last (CONJUNCTS insert_oracle_correct))
  \\ simp [is_record_def, Case_def]
  \\ fs [markerTheory.Abbrev_def]

  \\ disch_then (qspecl_then [`shift_seq 1 (orac_s t'.eval_state).oracle`,
        `eds.compiler`] mp_tac)
  \\ impl_tac
  >- (
    simp [orac_agrees_def, shift_seq_def]
    \\ fs [s_rel_def]
    \\ rpt strip_tac \\ fs []
    \\ metis_tac []
  )
 
  \\ rw [insert_oracle_def]
  \\ asm_exists_tac
  \\ simp []
  \\ conj_tac
  >- (
    (* tricky part: compiler state assumption *)
    cheat
  )
  \\ fs [s_rel_def]
  \\ Cases_on `res` \\ fs []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac env_rel_mono_rel))
  \\ TRY (Cases_on `e` \\ fs [])
  \\ rw []
  \\ imp_res_tac concrete_v_rel
  \\ fs []

QED

