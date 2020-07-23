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



(* non-Eval case. it's almost straightforward except Envs might be
   represented differently, which means we need a v_rel, and to assume
   no Rtype_error, etc, which is sad *)

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
val _ = IndDefLib.add_mono_thm env_rel_mono_rel;

Inductive no_Eval_v_rel:
  (no_Eval_v_rel (Env env) v) /\
  (LIST_REL no_Eval_v_rel xs ys ==>
    no_Eval_v_rel (Vectorv xs) (Vectorv ys)) /\
  (LIST_REL no_Eval_v_rel xs ys ==>
    no_Eval_v_rel (Conv stmp xs) (Conv stmp ys)) /\
  (env_rel no_Eval_v_rel env env' ==>
    no_Eval_v_rel (Closure env nm x) (Closure env' nm x)) /\
  (env_rel no_Eval_v_rel env env' ==>
    no_Eval_v_rel (Recclosure env funs nm) (Recclosure env' funs nm)) /\
  (no_Eval_v_rel (Litv l) (Litv l)) /\
  (no_Eval_v_rel (Loc n) (Loc n))
End

Theorem no_Eval_v_rel_l_cases =
  [``no_Eval_v_rel (Litv l) v``, ``no_Eval_v_rel (Conv cn vs) v``,
    ``no_Eval_v_rel (Loc l) v``, ``no_Eval_v_rel (Vectorv vs) v``,
    ``no_Eval_v_rel (Env e) v``,
    ``no_Eval_v_rel (Recclosure env funs nm) v``,
    ``no_Eval_v_rel (Closure env nm x) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once no_Eval_v_rel_cases])
  |> map GEN_ALL
  |> LIST_CONJ

Theorem no_Eval_v_rel_Boolv:
  (no_Eval_v_rel (Boolv b) v) = (v = Boolv b)
Proof
  rw [Boolv_def, no_Eval_v_rel_l_cases]
QED

Definition no_Eval_s_rel_def:
  no_Eval_s_rel s s' <=>
  ?es refs. s' = s with <| refs := refs;
    eval_state := SOME (EvalOracle es) |> /\
  LIST_REL (sv_rel no_Eval_v_rel) s.refs refs /\
  s.eval_state = SOME EvalDecs
End

val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);

fun do_match_inst const data thm = let
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
  in assume_tac thm4 end
  else NO_TAC)
  end) prems
  end

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

Theorem no_Eval_v_cases =
  [``no_Eval_v (Litv l)``, ``no_Eval_v (Conv cn vs)``,
    ``no_Eval_v (Loc l)``, ``no_Eval_v (Vectorv vs)``,
    ``no_Eval_v (Env e)``,
    ``no_Eval_v (Recclosure env funs nm)``,
    ``no_Eval_v (Closure env nm x)``]
  |> map (SIMP_CONV (srw_ss ()) [Once no_Eval_v_cases, GSYM no_Eval_env_def])
  |> map GEN_ALL
  |> LIST_CONJ

Theorem do_opapp_no_Eval:
  do_opapp vs = SOME (env, v) /\
  EVERY no_Eval_v vs ==>
  no_Eval_env env /\ ~ has_Eval v
Proof
  rw [do_opapp_cases]
  \\ fs [no_Eval_v_cases, no_Eval_env_def]
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
    \\ simp [quotient_pairTheory.PAIR_REL_THM, no_Eval_v_cases, no_Eval_env_def]
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
  \\ simp [list_to_v_def, no_Eval_v_cases]
QED

Theorem no_Eval_v_v_to_list:
  !v xs. v_to_list v = SOME xs /\ no_Eval_v v ==> EVERY no_Eval_v xs
Proof
  recInduct terminationTheory.v_to_list_ind
  \\ rw [terminationTheory.v_to_list_def, no_Eval_v_cases]
  \\ fs [no_Eval_v_cases, option_case_eq]
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
  \\ fs [no_Eval_v_cases, div_exn_v_def, sub_exn_v_def, chr_exn_v_def]
  \\ fs [store_assign_def, store_alloc_def] \\ rveq \\ fs []
  \\ TRY (irule IMP_EVERY_LUPDATE)
  \\ simp [no_Eval_v_list_to_v, EVERY_MAP, no_Eval_v_cases]
  \\ imp_res_tac no_Eval_v_v_to_list
  \\ fs [option_case_eq] \\ rveq \\ fs []
  \\ TRY (irule IMP_EVERY_LUPDATE)
  \\ simp [no_Eval_v_cases]
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
  \\ fs [Q.ISPEC `Match b` EQ_SYM_EQ, no_Eval_v_cases]
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

Definition not_oracle_def[simp]:
  not_oracle (SOME (EvalOracle _)) = F /\
  not_oracle _ = T
End

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
  \\ fs [has_Eval_def, has_Eval_dec_def, EVERY_REVERSE, no_Eval_v_cases]
  \\ rveq \\ fs []
  \\ fs [pair_case_eq, result_case_eq, error_result_case_eq, bool_case_eq,
    option_case_eq, exp_or_val_case_eq]
  \\ rw []
  \\ fs [pair_CASE_eq_pairarg, combine_dec_result_eq_Rerr]
  \\ rpt (pairarg_tac \\ fs [])
  \\ rveq \\ fs []
  \\ fs [match_result_case_eq, do_log_def, do_if_def, build_conv_def,
        bind_exn_v_def, bool_case_eq, pair_case_eq]
  \\ ntac 2 (rveq \\ fs [])
  \\ TRY (drule do_opapp_no_Eval)
  \\ TRY (drule do_app_no_Eval)
  \\ fs [Q.ISPEC `(a, b)` EQ_SYM_EQ, no_Eval_v_cases, EVERY_REVERSE]
  \\ imp_res_tac evaluate_sing
  \\ TRY (drule_then imp_res_tac (CONJUNCT1 pmatch_no_Eval))
  \\ TRY (CHANGED_TAC (simp [combine_dec_result_def]) \\ CASE_TAC \\ fs [])
  \\ TRY (qpat_x_assum `no_Eval_env _ ==> _` mp_tac \\ impl_tac)
  \\ simp [EVERY_REVERSE]
  \\ rpt disch_tac
  \\ ntac 2 (rveq \\ fs [])
  \\ fs [dec_clock_def, build_rec_env_merge, nsAppend_to_nsBindList,
    declare_env_def, option_case_eq, eval_state_case_eq, pair_case_eq]
  \\ rveq \\ fs []
  \\ rfs []
  \\ simp [list_result_def]
  \\ TRY (
    CHANGED_TAC (simp [namespaceTheory.nsOptBind_def]) \\ CASE_TAC
    \\ simp []
  )
  \\ TRY (
    simp [no_Eval_env_def, alist_to_ns_to_bind2, nsSing_eq_bind]
    \\ MAP_FIRST irule [env_rel_add_nsBind, env_rel_add_nsBindList, env_rel_nsLift]
    \\ simp [GSYM no_Eval_env_def]
  )
  \\ simp [Q.SPEC `x with <| v := nsEmpty |>` no_Eval_env_def,
        Q.SPECL [`R`, `x with <| v := nsEmpty |>`] env_rel_def]
  \\ TRY (
    irule EVERY2_refl
    \\ fs [GSYM EVERY_MEM, EVERY_MAP]
    \\ first_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC)
    \\ simp [FORALL_PROD, quotient_pairTheory.PAIR_REL_THM, no_Eval_v_cases,
        EVERY_MAP]
  )
  \\ rfs [no_Eval_extend, combine_dec_result_def]
  \\ fs [no_Eval_extend, GSYM (SIMP_RULE (srw_ss ()) [] extend_dec_env_def)]
  \\ rveq \\ fs []
  \\ simp [no_Eval_v_cases, EVERY_REVERSE]
  \\ TRY (qpat_x_assum `_ <> Rerr _ ==> _` mp_tac \\ impl_tac \\ strip_tac)
  \\ rveq \\ fs []
  \\ TRY (fs [no_Eval_env_def, env_rel_def] \\ res_tac
    \\ fs [no_Eval_v_rel_rules] \\ NO_TAC)
QED




