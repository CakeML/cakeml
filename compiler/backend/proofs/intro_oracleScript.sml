(*
  Proofs that the oracle semantics can be introduced
*)

open preamble semanticsTheory namespacePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory

local open evaluatePropsTheory in end

val _ = new_theory "intro_oracle";

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

Inductive v_rel1:
  (!id env'. v_to_env_id v = SOME id /\ lookup_env es id = SOME env' /\
        env_rel (v_rel1 es) env env' ==>
    v_rel1 es (Env env) v) /\
  (LIST_REL (v_rel1 es) xs ys ==>
    v_rel1 es (Vectorv xs) (Vectorv ys)) /\
  (LIST_REL (v_rel1 es) xs ys ==>
    v_rel1 es (Conv stmp xs) (Conv stmp ys)) /\
  (env_rel (v_rel1 es) env env' ==>
    v_rel1 es (Closure env nm x) (Closure env' nm x)) /\
  (env_rel (v_rel1 es) env env' ==>
    v_rel1 es (Recclosure env funs nm) (Recclosure env' funs nm)) /\
  (v_rel1 es (Litv l) (Litv l)) /\
  (v_rel1 es (Loc n) (Loc n))
End

Theorem v_rel1_l_cases =
  [``v_rel1 es (Litv l) v``, ``v_rel1 es (Conv cn vs) v``,
    ``v_rel1 es (Loc l) v``, ``v_rel1 es (Vectorv vs) v``,
    ``v_rel1 es (Env e) v``, ``v_rel1 es (Recclosure env funs nm) v``,
    ``v_rel1 es (Closure env nm x) v``]
  |> map (SIMP_CONV (srw_ss ()) [Once v_rel1_cases])
  |> map GEN_ALL
  |> LIST_CONJ

Definition s_rel1_def:
  s_rel1 es s s' <=>
  ?refs'. s' = s with <| refs := refs';
    eval_state := SOME (EvalOracle es) |> /\
  LIST_REL (sv_rel (v_rel1 es)) s.refs s'.refs /\
  s.eval_state = SOME EvalDecs /\
  es.custom_do_eval = SOME do_eval_record /\
  es.generation < LENGTH es.envs
End

Definition es_forward1_def:
  es_forward1 es es' <=>
  (es.custom_do_eval = SOME do_eval_record ==>
    es'.custom_do_eval = SOME do_eval_record) /\
  (LENGTH es.envs <= LENGTH es'.envs) /\
  (!env_id env. lookup_env es env_id = SOME env ==>
    lookup_env es' env_id = SOME env)
End

Theorem es_forward1_refl:
  es_forward1 es es
Proof
  simp [es_forward1_def]
QED

Theorem es_forward1_trans:
  es_forward1 es es' /\ es_forward1 es' es'' ==>
  es_forward1 es es''
Proof
  fs [es_forward1_def]
QED

Theorem v_rel1_forward:
  !x y. v_rel1 es x y ==> es_forward1 es es' ==> v_rel1 es' x y
Proof
  ho_match_mp_tac v_rel1_ind
  \\ rw [v_rel1_l_cases]
  \\ full_simp_tac (bool_ss ++ ETA_ss) []
  \\ fs [es_forward1_def]
  \\ res_tac
  \\ simp []
QED

Theorem forward_rules:
  (v_rel1 es x y /\ es_forward1 es es' ==> v_rel1 es' x y) /\
  (LIST_REL (v_rel1 es) xs ys /\ es_forward1 es es' ==>
    LIST_REL (v_rel1 es') xs ys) /\
  (env_rel (v_rel1 es) env env' /\ es_forward1 es es' ==>
    env_rel (v_rel1 es') env env') /\
  (!xs ys. LIST_REL (sv_rel (v_rel1 es)) xs ys /\ es_forward1 es es' ==>
    LIST_REL (sv_rel (v_rel1 es')) xs ys)
Proof
  rw []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac LIST_REL_mono))
  \\ rw []
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac sv_rel_mono))
  \\ TRY (first_x_assum (fn t => mp_tac t \\ match_mp_tac env_rel_mono_rel))
  \\ rw []
  \\ imp_res_tac v_rel1_forward
QED

fun imp_res_final_tac thm = IMP_RES_THEN (fn t => fn (asms, goal) =>
    (print_term (concl t);
    if is_forall (concl t) orelse is_imp (concl t) then all_tac
    else let
      val (vs, tm) = strip_exists (concl t)
      val vset = HOLset.addList (empty_tmset, vs)
      fun m tm' = let
          val (ts, tys) = match_term tm tm'
        in null tys andalso all (curry HOLset.member vset o #redex) ts end
        handle HOL_ERR _ => false
    in if exists m asms then all_tac
      else strip_assume_tac thm
    end) (asms, goal)) thm

fun imp_res_final_tac2 thm = if is_forall (concl thm) orelse is_imp (concl thm)
    then IMP_RES_THEN imp_res_final_tac2 thm
    else strip_assume_tac thm

val rels = [``env_rel``, ``v_rel1``];

val const = ``s_rel1``;
val data = ["i", "m", "i"]

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

fun do_rel_insts rels thm = MAP_FIRST (fn thm => let
    val (vs, t1) = strip_forall (concl thm)
    val _ = length vs = 1 orelse raise Option
    val (lhs, _) = dest_imp t1
    val _ = term_eq (hd vs) (rand lhs) orelse raise Option
    val (rel, _) = strip_comb lhs
    val _ = exists (same_const rel) rels orelse raise Option
  in drule_then assume_tac thm ORELSE FIRST_ASSUM (fn a => let
    val known = concl a
    val (rel', _) = strip_comb known
    val _ = same_const rel rel' orelse raise Option
    val _ = term_eq (rand (rator known)) (rand (rator lhs))
      orelse raise Option
    val t = mk_comb (rator lhs, rand known)
  in suff_tac t end)
  end handle Option => NO_TAC) (RES_CANON thm)

val s = mk_var ("s", ``: 'ffi semanticPrimitives$state``);

val eval_cases_tac =
  fs [pair_case_eq, CaseEq "result", CaseEq "error_result", bool_case_eq,
        option_case_eq, list_case_eq, CaseEq "exp_or_val"]
  \\ rveq \\ fs []

val insts_tac = rpt (FIRST ([
      first_x_assum (do_match_inst const data),
      first_x_assum (do_match_inst ``env_rel`` ["_", "m", "i"]),
      first_x_assum (do_match_inst ``v_rel1`` ["_", "m", "i"]),
      first_x_assum (fn t => (mp_tac t \\ impl_tac) THENL [all_tac, disch_tac]),
      goal_assum (fn t => do_match_inst const data t \\ pop_assum match_mp_tac),
      CHANGED_TAC (fs [Q.ISPEC `(a, b)` EQ_SYM_EQ] \\ rfs [])
    ] @
      map (drule_then irule) (es_forward1_trans :: IMP_CANON forward_rules)
    ))

val sing_tac = imp_res_tac evaluatePropsTheory.evaluate_sing
    \\ rveq \\ fs []
    \\ rveq \\ fs []

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

Theorem s_rel1_store_lookup:
  s_rel1 es s t ==>
  OPTREL (sv_rel (v_rel1 es)) (store_lookup i s.refs) (store_lookup i t.refs)
Proof
  rw [s_rel1_def]
  \\ irule store_lookup_rel
  \\ fs []
QED

Theorem pmatch1:
  s_rel1 es s t ==>
  (!env_c s_refs p x env y env'.
  s_refs = s.refs /\
  v_rel1 es x y /\
  LIST_REL ((=) ### v_rel1 es) env env' ==>
  match_result_rel T (LIST_REL ((=) ### v_rel1 es))
    (pmatch env_c s_refs p x env)
    (pmatch env_c t.refs p y env')
  ) /\
  (!env_c s_refs ps xs env ys env'.
  s_refs = s.refs /\ LIST_REL (v_rel1 es) xs ys /\
  LIST_REL ((=) ### v_rel1 es) env env' ==>
  match_result_rel T (LIST_REL ((=) ### v_rel1 es))
    (pmatch_list env_c s_refs ps xs env)
    (pmatch_list env_c t.refs ps ys env')
  )
Proof
  disch_tac
  \\ ho_match_mp_tac terminationTheory.pmatch_ind
  \\ rw [terminationTheory.pmatch_def, match_result_rel_def,
    quotient_pairTheory.PAIR_REL_THM]
  \\ fs [v_rel1_l_cases]
  \\ rveq \\ fs []
  \\ fs [v_to_env_id_def, CaseEq "v", list_case_eq, option_case_eq]
  \\ fs [terminationTheory.pmatch_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs []
  >- (
    TOP_CASE_TAC \\ fs []
    \\ fs [option_case_eq, pair_case_eq, bool_case_eq]
    \\ rveq \\ fs []
    \\ every_case_tac
    \\ fs []
    \\ res_tac
    \\ fs []
  )
  >- (
    drule s_rel1_store_lookup
    \\ disch_then (qspec_then `lnum` assume_tac)
    \\ every_case_tac \\ fs [OPTREL_SOME]
  )
  >- (
    first_x_assum (drule_then drule)
    \\ every_case_tac \\ fs []
    \\ first_x_assum (drule_then drule)
    \\ simp []
  )
QED

Theorem pmatch11 = UNDISCH_ALL pmatch1 |> CONJUNCT1 |> SPEC_ALL
  |> Q.INST [`env` |-> `[]`]
  |> GEN_ALL |> DISCH_ALL
  |> SIMP_RULE list_ss []

Theorem can_pmatch_all1:
  can_pmatch_all env_c s.refs pats x /\
  s_rel1 es s t /\ v_rel1 es x y ==>
  can_pmatch_all env_c t.refs pats y
Proof
  rw []
  \\ Induct_on `pats`
  \\ rw [can_pmatch_all_def]
  \\ drule_then drule pmatch11
  \\ simp [match_result_rel_def]
  \\ disch_then (qspecl_then [`h`, `env_c`] mp_tac)
  \\ every_case_tac
  \\ fs []
  \\ rw []
  \\ simp []
QED

Theorem env_rel_nsLookup:
  env_rel R env env' /\ nsLookup env.v n = SOME x ==>
  ?y. nsLookup env'.v n = SOME y /\ R x y
Proof
  rw [env_rel_def, EXTENSION]
  \\ fs [nsLookup_nsDom]
  \\ res_tac
  \\ simp []
QED

Theorem s_rel1_clock:
  s_rel1 es s t ==> s.clock = t.clock /\
    s_rel1 es (dec_clock s) (dec_clock t)
Proof
  rw [s_rel1_def]
  \\ fs [evaluateTheory.dec_clock_def]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
QED

Theorem s_rel1_reset:
  !s0 t0 es0. s_rel1 es s t /\ s_rel1 es0 s0 t0 /\ es_forward1 es0 es ==>
  ?es2. es_forward1 es es2 /\
  s_rel1 es2
    (s with eval_state := reset_env_generation s0.eval_state s.eval_state)
    (t with eval_state := reset_env_generation t0.eval_state t.eval_state)
Proof
  rw [s_rel1_def]
  \\ fs [reset_env_generation_def]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ conj_asm1_tac
  >- (
    simp [es_forward1_def, FORALL_PROD, lookup_env_def]
  )
  \\ imp_res_tac forward_rules
  \\ fs [es_forward1_def]
QED

Theorem declare_env1:
  declare_env s.eval_state env = SOME (x, es1) /\
  s_rel1 es s t /\
  env_rel (v_rel1 es) env env' ==>
  ? y es2. declare_env t.eval_state env' = SOME (y, SOME (EvalOracle es2)) /\
  es_forward1 es es2 /\
  v_rel1 es2 x y /\
  s_rel1 es2 (s with eval_state := es1)
    (t with eval_state := SOME (EvalOracle es2))
Proof
  rw []
  \\ fs [declare_env_def, s_rel1_def]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ simp [lem_listTheory.list_index_def, v_rel1_l_cases, v_to_env_id_def,
        v_to_nat_def, nat_to_v_def, lookup_env_def, EL_LUPDATE, EL_APPEND_EQN]
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ conj_asm1_tac
  >- (
    rw [es_forward1_def, lookup_env_def, FORALL_PROD,
        lem_listTheory.list_index_def, EL_LUPDATE]
    \\ rw [EL_APPEND_EQN] \\ fs []
  )
  \\ imp_res_tac forward_rules
  \\ simp []
QED

Theorem env_rel_add_nsBind:
  env_rel R env env' /\ R x y ==>
  env_rel R (env with v := nsBind n x env.v) (env' with v := nsBind n y env'.v)
Proof
  rw [env_rel_def]
  \\ Cases_on `nm = Short n`
  \\ fs [nsLookup_nsBind]
  \\ res_tac
QED

Theorem nsLookup_nsBindList:
  nsLookup (nsBindList vs ns) nm = case ALOOKUP (MAP (Short ## I) vs) nm of 
    NONE => nsLookup ns nm
  | SOME v => SOME v
Proof
  Induct_on `vs`
  \\ fs [namespaceTheory.nsBindList_def]
  \\ simp [FORALL_PROD]
  \\ rw []
  \\ simp [nsLookup_nsBind]
QED

Theorem ALOOKUP_find_index:
  ALOOKUP xs v = (case find_index v (MAP FST xs) 0 of
    NONE => NONE | SOME i => SOME (SND (EL i xs)))
Proof
  Cases_on `ALOOKUP xs v`
  \\ imp_res_tac ALOOKUP_find_index_NONE
  \\ imp_res_tac ALOOKUP_find_index_SOME
  \\ simp []
QED

Theorem build_rec_env1:
  env_rel R env env' /\
  (!i. i < LENGTH funs ==>
    R (Recclosure env funs (FST (EL i funs)))
        (Recclosure env' funs (FST (EL i funs)))) ==>
  env_rel R (env with v := build_rec_env funs env env.v)
    (env' with v := build_rec_env funs env' env'.v)
Proof
  rw [build_rec_env_merge, env_rel_def, nsDomMod_nsAppend_flat]
  \\ simp [MAP_MAP_o, o_DEF, ELIM_UNCURRY]
  \\ fs [nsAppend_to_nsBindList, nsLookup_nsBindList, option_case_eq]
  \\ fs [ALOOKUP_find_index, option_case_eq, MAP_MAP_o, o_DEF, ELIM_UNCURRY]
  \\ fs []
  \\ res_tac
  \\ imp_res_tac find_index_LESS_LENGTH
  \\ rveq \\ fs [EL_MAP]
QED

Theorem v_to_decs1:
  v_to_decs decs_v = SOME decs /\ v_rel1 es decs_v decs_v2 ==>
  decs_v2 = decs_v
Proof
  cheat
QED

Theorem do_eval1:
  do_eval xs s.eval_state = SOME (env, decs, es2) /\
  s_rel1 es s t /\
  LIST_REL (v_rel1 es) xs ys ==>
  ? env' es3 es4.
  es2 = SOME es3 /\
  do_eval ys t.eval_state = SOME (env', decs, SOME (EvalOracle es4)) /\
  es_forward1 es es4 /\
  s_rel1 es4 (s with eval_state := es2)
    (t with eval_state := SOME (EvalOracle es4)) /\
  env_rel (v_rel1 es4) env env'
Proof
  rw [s_rel1_def]
  \\ fs [do_eval_def]
  \\ fs [CaseEq "v", list_case_eq, option_case_eq]
  \\ rveq \\ fs []
  \\ rveq \\ fs []
  \\ fs [v_rel1_l_cases]
  \\ simp [do_eval_record_def]
  \\ imp_res_tac v_to_decs1
  \\ simp [semanticPrimitivesTheory.state_component_equality]
  \\ simp [add_env_generation_def]
  \\ conj_asm1_tac
  >- (
    rw [es_forward1_def, FORALL_PROD, lookup_env_def,
        lem_listTheory.list_index_def, EL_APPEND_EQN]
    \\ fs [bool_case_eq, option_case_eq]
  )
  \\ imp_res_tac forward_rules
  \\ simp []
QED

Theorem env_rel_extend1:
  env_rel (v_rel1 es) a c /\ env_rel (v_rel1 es) b d ==>
  env_rel (v_rel1 es) (extend_dec_env a b) (extend_dec_env c d)
Proof
  rw [env_rel_def, extend_dec_env_def]
  \\ fs [nsDom_nsAppend_equal]
  \\ `(?v. nsLookup a.v nm = SOME v) = (?v. nsLookup c.v nm = SOME v)`
    by simp [GSYM nsLookup_nsDom]
  \\ fs [nsLookup_nsAppend_some] \\ rfs []
  \\ res_tac
QED

Theorem v_rel1_Boolv:
  v_rel1 es (Boolv a) (Boolv b) = (a = b)
Proof
  rw [Boolv_def, v_rel1_l_cases]
QED

Theorem do_eq1:
  (! x y x' y' b. do_eq x y = Eq_val b /\
  v_rel1 es x x' /\
  v_rel1 es y y' ==>
  do_eq x' y' = Eq_val b) /\
  (! xs ys xs' ys' b. do_eq_list xs ys = Eq_val b /\
  LIST_REL (v_rel1 es) xs xs' /\
  LIST_REL (v_rel1 es) ys ys' ==>
  do_eq_list xs' ys' = Eq_val b)
Proof
  ho_match_mp_tac do_eq_ind
  \\ rw [do_eq_def]
  \\ fs [v_rel1_l_cases, do_eq_def]
  \\ rveq \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs []
  (* why are you allowed to compare Env's? what does that accomplish? *)
  >- cheat
  \\ fs [CaseEq "eq_result", bool_case_eq]
  \\ fs []
QED

Theorem store_assign:
  store_assign lnum sv refs = SOME refs2 /\
  LIST_REL (sv_rel R) refs refs3 /\
  sv_rel R sv sv' ==>
  ?refs4. store_assign lnum sv' refs3 = SOME refs4 /\
  LIST_REL (sv_rel R) refs2 refs4
Proof
  rw [store_assign_def]
  \\ imp_res_tac LIST_REL_LENGTH
  \\ fs [EVERY2_LUPDATE_same]
  \\ fs [LIST_REL_EL_EQN]
  \\ res_tac
  \\ fs [sv_rel_cases, store_v_same_type_def] \\ rveq \\ fs []
QED

Theorem store_lookup:
  store_lookup i refs = SOME sv /\
  LIST_REL (sv_rel R) refs refs2 ==>
  ?sv2. store_lookup i refs2 = SOME sv2 /\
  sv_rel R sv sv2 
Proof
  rw [store_lookup_def]
  \\ fs [LIST_REL_EL_EQN]
QED

Theorem sv_rel_l_cases =
  [``sv_rel R (Refv rv) v``, ``sv_rel R (W8array xs) v``,
        ``sv_rel R (Varray vs) v``]
  |> map (SIMP_CONV (srw_ss ()) [sv_rel_cases])
  |> map GEN_ALL |> LIST_CONJ

Theorem v_rel1_list_to_v:
  !xs ys. v_rel1 es (list_to_v xs) (list_to_v ys)
  <=>
  LIST_REL (v_rel1 es) xs ys
Proof
  Induct
  \\ simp []
  >- (
    Cases
    \\ simp [list_to_v_def, v_rel1_l_cases]
  )
  >- (
    gen_tac
    \\ Cases
    \\ simp [list_to_v_def, v_rel1_l_cases]
  )
QED

Theorem v_to_list1:
  ! x y xs. v_to_list x = SOME xs /\
  v_rel1 es x y ==>
  ?ys. v_to_list y = SOME ys /\
  LIST_REL (v_rel1 es) xs ys
Proof
  recInduct v_to_list_ind
  \\ rw [v_to_list_def]
  \\ fs [v_rel1_l_cases, v_to_list_def, option_case_eq]
  \\ rveq \\ fs []
  \\ res_tac
  \\ simp []
QED

Theorem v_to_char_list1:
  ! x y xs. v_to_char_list x = SOME xs /\
  v_rel1 es x y ==>
  v_to_char_list y = SOME xs
Proof
  recInduct v_to_char_list_ind
  \\ rw [v_to_char_list_def]
  \\ fs [v_rel1_l_cases, v_to_char_list_def, option_case_eq]
  \\ rveq \\ fs []
QED

Theorem vs_to_string1:
  !xs ys s. vs_to_string xs = SOME s /\
  LIST_REL (v_rel1 es) xs ys ==>
  vs_to_string ys = SOME s
Proof
  recInduct vs_to_string_ind
  \\ rw [vs_to_string_def]
  \\ fs [option_case_eq, v_rel1_l_cases]
  \\ rveq \\ fs []
  \\ simp [vs_to_string_def]
QED

Theorem do_app1:
  do_app (s.refs, s.ffi) op (REVERSE xs) = SOME ((refs, ffi), r) /\
  s_rel1 es s t /\
  LIST_REL (v_rel1 es) xs ys /\
  r <> Rerr (Rabort Rtype_error)
  ==>
  ? refs' r'.
  do_app (t.refs, t.ffi) op (REVERSE ys) = SOME ((refs', ffi), r') /\
  LIST_REL (sv_rel (v_rel1 es)) refs refs' /\
  result_rel (v_rel1 es) (v_rel1 es) r r'

Proof

  rw [s_rel1_def]
  \\ fs []
  \\ last_x_assum mp_tac
  \\ simp [Once do_app_cases] \\ rw [listTheory.SWAP_REVERSE_SYM]
  \\ fs [v_rel1_l_cases, CaseEq "ffi_result", option_case_eq] \\ rveq \\ fs []
  \\ simp [do_app_def]
  \\ simp [div_exn_v_def, sub_exn_v_def, chr_exn_v_def,
        v_rel1_l_cases, v_rel1_Boolv, v_rel1_list_to_v,
        EVERY2_refl, MEM_MAP, PULL_EXISTS]
  \\ TRY (drule_then imp_res_tac (CONJUNCT1 do_eq1))
  \\ TRY (drule_then imp_res_tac store_assign)
  \\ TRY (drule_then imp_res_tac v_to_char_list1)
  \\ TRY (drule_then kall_tac v_to_list1 \\ imp_res_tac v_to_list1)
  \\ TRY (drule_then kall_tac store_lookup \\ imp_res_tac store_lookup)
  \\ TRY (irule EVERY2_refl)
  \\ imp_res_tac LIST_REL_LENGTH
  \\ simp [v_rel1_l_cases, v_rel1_Boolv, v_rel1_list_to_v, LIST_REL_APPEND_EQ]

  \\ fs [PULL_EXISTS, store_alloc_def, sv_rel_l_cases]
  \\ TRY (drule_then imp_res_tac vs_to_string1)
  \\ rveq \\ fs []
  \\ imp_res_tac LIST_REL_LENGTH
  \\ rveq \\ fs []
  \\ fs [LIST_REL_REPLICATE_same]
  \\ TRY (fs [LIST_REL_EL_EQN] \\ NO_TAC)


(* well, we were doing so well here .. sort of

  EnvLookup puts us in a world of difficulties

  it means we need to either create a just-for-now semantics in which it
  looks up the envs, or we need to compile it already, in which case we
  need to have solved the puzzle of putting the env store into the
  accessible state. grumble. *)


Theorem oracle_evaluate1:

  (! ^s env exps s' res es t env'.
  evaluate s env exps = (s', res) /\
  s_rel1 es s t /\
  env_rel (v_rel1 es) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate t env' exps = (t', res') /\
  s_rel1 es' s' t' /\
  result_rel (LIST_REL (v_rel1 es')) (v_rel1 es') res res' /\
  es_forward1 es es')
  /\
  (! ^s env x pes err_x s' res es t env' y err_y.
  evaluate_match s env x pes err_x = (s', res) /\
  s_rel1 es s t /\
  env_rel (v_rel1 es) env env' /\
  v_rel1 es x y /\
  v_rel1 es err_x err_y /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_match t env' y pes err_y = (t', res') /\
  s_rel1 es' s' t' /\
  result_rel (LIST_REL (v_rel1 es')) (v_rel1 es') res res' /\
  es_forward1 es es')
  /\
  (! ^s env decs s' res es t env'.
  evaluate_decs s env decs = (s', res) /\
  s_rel1 es s t /\
  env_rel (v_rel1 es) env env' /\
  res <> Rerr (Rabort Rtype_error) ==>
  ?es' t' res'.
  evaluate_decs t env' decs = (t', res') /\
  s_rel1 es' s' t' /\
  result_rel (env_rel (v_rel1 es')) (v_rel1 es') res res' /\
  es_forward1 es es')

Proof

  ho_match_mp_tac terminationTheory.full_evaluate_ind
  \\ rw [terminationTheory.full_evaluate_def]
  \\ simp [result_rel_def, v_rel1_rules]
  \\ fsrw_tac [SATISFY_ss] [es_forward1_refl]

  >- (
    eval_cases_tac \\ insts_tac
    \\ sing_tac
    \\ rw []
    \\ insts_tac
  )

  >- (
    eval_cases_tac \\ insts_tac
    \\ sing_tac
  )

  >- (
    eval_cases_tac \\ insts_tac
    \\ imp_res_tac can_pmatch_all1
    \\ fs [env_rel_def]
    \\ rfs []
    \\ insts_tac
  )

  >- (
    eval_cases_tac
    \\ imp_res_tac env_rel_def
    \\ fs []
    \\ insts_tac
    \\ fs [build_conv_def, option_case_eq, pair_case_eq]
    \\ rveq \\ fs []
    \\ simp [v_rel1_l_cases]
  )

  >- (
    fs [option_case_eq] \\ rveq \\ fs []
    \\ imp_res_tac env_rel_nsLookup
    \\ fs []
    \\ insts_tac
    \\ simp [es_forward1_refl]
  )

  >- (
    insts_tac
    \\ simp [v_rel1_l_cases, es_forward1_refl]
  )

  >- (
    (* App *)

    fs [pair_case_eq] \\ fs []
    \\ insts_tac
    \\ TRY (strip_tac \\ fs [])
    \\ fs [result_case_eq] \\ rveq \\ fs []
    \\ fs [result_rel_Rval, result_rel_Rerr1]
    \\ insts_tac
    \\ rveq \\ fs []
    \\ rw []
    >- (
      (* Opapp *)
      imp_res_tac s_rel1_clock
      \\ eval_cases_tac
      \\ fs [do_opapp_def]
      \\ eval_cases_tac
      \\ fs [listTheory.SWAP_REVERSE_SYM, CaseEq "v"] \\ rveq \\ fs []
      \\ fs [v_rel1_l_cases, listTheory.SWAP_REVERSE]
      \\ insts_tac
      \\ eval_cases_tac
      >- (
        drule_then (drule_then (qspec_then `n` mp_tac)) env_rel_add_nsBind
        \\ rw []
        \\ insts_tac
      )
      >- (
        drule_then (qspec_then `funs` mp_tac) build_rec_env1
        \\ rw [v_rel1_l_cases]
        \\ drule_then (drule_then (qspec_then `n` mp_tac)) env_rel_add_nsBind
        \\ rw []
        \\ insts_tac
      )
    )

    >- (
      (* Eval *)
      fs [evaluateTheory.do_eval_res_def, option_case_eq, pair_case_eq]
      \\ rveq \\ fs []
      \\ drule_then drule (Q.INST [`ys` |-> `REVERSE zs`] do_eval1)
      \\ simp []
      \\ disch_then drule
      \\ rw []
      \\ imp_res_tac s_rel1_clock
      \\ eval_cases_tac \\ insts_tac
      \\ rveq \\ fs []
      >- (
        qmatch_goalsub_abbrev_tac `declare_env _ ext_env`
        \\ drule_then drule declare_env1
        \\ disch_then (qspec_then `ext_env` mp_tac)
        \\ fs [markerTheory.Abbrev_def]
        \\ impl_tac
        >- (
          irule env_rel_extend1
          \\ insts_tac
        )
        \\ rw []
        \\ simp []
        \\ drule_then (qspec_then `st'` mp_tac) s_rel1_reset
        \\ rw []
        \\ insts_tac
        \\ rw [] \\ insts_tac
      )
      >- (
        drule_then (qspec_then `st'` mp_tac) s_rel1_reset
        \\ rw []
        \\ insts_tac
        \\ rw [] \\ insts_tac
      )
    )

    \\ fs [option_case_eq, pair_case_eq]
    \\ rveq \\ fs []


  ...
  more to do

