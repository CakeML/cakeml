open preamble;
open namespacePropsTheory semanticPrimitivesTheory semanticPrimitivesPropsTheory;
open source_to_modTheory modLangTheory modSemTheory modPropsTheory;

val _ = new_theory "source_to_modProof";

(* value relation *)

(* bind locals with an arbitrary trace *)
val bind_locals_def = Define `
  bind_locals ts locals var_map =
    nsBindList (MAP2 (\t x. (x, modLang$Var_local t x)) ts locals) var_map`;

val nsAppend_bind_locals = Q.prove(`
  ∀funs.
  nsAppend (alist_to_ns (MAP (λx. (x,Var_local t x)) (MAP FST funs))) (bind_locals ts locals var_map) =
  bind_locals (REPLICATE (LENGTH funs) t ++ ts) (MAP FST funs ++ locals) var_map`,
  Induct_on`funs`>>fs[FORALL_PROD,bind_locals_def,namespaceTheory.nsBindList_def]);

val nsBindList_pat_tups_bind_locals = Q.prove(`
  ∀ls.
  ∃tss.
  nsBindList (pat_tups t ls) (bind_locals ts locals var_map) =
  bind_locals (tss ++ ts) (ls ++ locals) var_map ∧
  LENGTH tss = LENGTH ls`,
  Induct>>rw[pat_tups_def,namespaceTheory.nsBindList_def,bind_locals_def]>>
  qexists_tac`(t § (LENGTH ls + 1))::tss`>>simp[]);

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!genv lit.
    v_rel genv ((Litv lit):semanticPrimitives$v) ((Litv lit):modSem$v)) ∧
  (!genv cn vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    v_rel genv (Conv cn vs) (Conv cn vs')) ∧
  (!genv var_map env_c env_v_top env_v_local x e env_v_local' t ts.
    env_rel genv env_v_local env_v_local' ∧
    global_env_inv genv var_map (set (MAP FST env_v_local')) env_v_top ∧
    LENGTH ts = LENGTH env_v_local' + 1
    ⇒
    v_rel genv (Closure <| c := env_c; v := nsAppend env_v_local env_v_top |> x e)
               (Closure (env_c, env_v_local') x
                 (compile_exp t (bind_locals ts (x::MAP FST env_v_local') var_map) e))) ∧
  (* For expression level let recs *)
  (!genv var_map env_c env_v_top env_v_local funs x env_v_local' t ts.
    env_rel genv env_v_local env_v_local' ∧
    global_env_inv genv var_map (set (MAP FST env_v_local')) env_v_top ∧
    LENGTH ts = LENGTH funs + LENGTH env_v_local'
    ⇒
    v_rel genv (Recclosure <| c := env_c; v := nsAppend env_v_local env_v_top |> funs x)
               (Recclosure (env_c, env_v_local')
                 (compile_funs t (bind_locals ts (MAP FST funs++MAP FST env_v_local') var_map) funs)
                 x)) ∧
  (* For top-level let recs *)
  (!genv var_map env funs x y e new_vars t1 t2.
    MAP FST new_vars = MAP FST (REVERSE funs) ∧
    global_env_inv genv var_map {} env.v ∧
    find_recfun x funs = SOME (y, e) ∧
    (* A syntactic way of relating the recursive function environment, rather
     * than saying that they build v_rel related environments, which looks to
     * require step-indexing *)
    (!x. x ∈ set (MAP FST funs) ⇒
         ?n y e t1 t2 t3.
           ALOOKUP new_vars x = SOME (Var_global t1 n) ∧
           n < LENGTH genv ∧
           find_recfun x funs = SOME (y,e) ∧
           EL n genv = SOME (Closure (env.c,[]) y (compile_exp t2 (nsBindList ((y, Var_local t3 y)::new_vars) var_map) e)))
    ⇒
    v_rel genv (Recclosure env funs x)
               (Closure (env.c, [])
                        y
                        (compile_exp t1 (nsBindList ((y, Var_local t2 y)::new_vars) var_map) e))) ∧
  (!genv loc.
    v_rel genv (Loc loc) (Loc loc)) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    v_rel genv (Vectorv vs) (Vectorv vs')) ∧
  (!genv.
    env_rel genv nsEmpty []) ∧
  (!genv x v env env' v'.
    env_rel genv env env' ∧
    v_rel genv v v'
    ⇒
    env_rel genv (nsBind x v env) ((x,v')::env')) ∧
  (!genv var_map shadowers env.
    (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env x = SOME v
       ⇒
       ?n v' t.
         nsLookup var_map x = SOME (Var_global t n) ∧
         n < LENGTH genv ∧
         EL n genv = SOME v' ∧
         v_rel genv v v')
    ⇒
    global_env_inv genv var_map shadowers env)`;

val v_rel_eqns = Q.store_thm ("v_rel_eqns",
  `(!genv l v.
    v_rel genv (Litv l) v ⇔
      (v = Litv l)) ∧
   (!genv b v. v_rel genv (Boolv b) v ⇔ (v = Boolv b)) ∧
   (!genv cn vs v.
    v_rel genv (Conv cn vs) v ⇔
      ?vs'. LIST_REL (v_rel genv) vs vs' ∧ (v = Conv cn vs')) ∧
   (!genv l v.
    v_rel genv (Loc l) v ⇔
      (v = Loc l)) ∧
   (!genv vs v.
    v_rel genv (Vectorv vs) v ⇔
      ?vs'. LIST_REL (v_rel genv) vs vs' ∧ (v = Vectorv vs')) ∧
   (!genv env'.
    env_rel genv nsEmpty env' ⇔
      env' = []) ∧
   (!genv x v env env'.
    env_rel genv (nsBind x v env) env' ⇔
      ?v' env''. v_rel genv v v' ∧ env_rel genv env env'' ∧ env' = ((x,v')::env'')) ∧
   (!genv var_map shadowers env.
    global_env_inv genv var_map shadowers env ⇔
      (!x v.
       x ∉ IMAGE Short shadowers ∧
       nsLookup env x = SOME v
       ⇒
       ?n v' t.
         nsLookup var_map x = SOME (Var_global t n) ∧
         n < LENGTH genv ∧
         EL n genv = SOME v' ∧
         v_rel genv v v'))`,
  srw_tac[][semanticPrimitivesTheory.Boolv_def,modSemTheory.Boolv_def] >>
  srw_tac[][Once v_rel_cases] >>
  srw_tac[][Q.SPECL[`genv`,`nsEmpty`](CONJUNCT1(CONJUNCT2 v_rel_cases))] >>
  metis_tac []);

val env_rel_dom = Q.prove (
  `!genv env env'.
    env_rel genv env env'
    ⇒
    ?l. env = alist_to_ns l ∧ MAP FST l = MAP FST env'`,
  induct_on `env'` >>
  simp [Once v_rel_cases] >>
  rw [] >>
  first_x_assum drule >>
  rw [] >>
  rw_tac list_ss [GSYM alist_to_ns_cons] >>
  metis_tac [MAP, FST]);

val env_rel_lookup = Q.prove (
  `!genv env x v env'.
    ALOOKUP env x = SOME v ∧
    env_rel genv (alist_to_ns env) env'
    ⇒
    ?v'.
      v_rel genv v v' ∧
      ALOOKUP env' x = SOME v'`,
  induct_on `env'` >>
  simp [] >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  fs [] >>
  rw [] >>
  Cases_on `env` >>
  TRY (PairCases_on `h`) >>
  fs [alist_to_ns_cons] >>
  rw [] >>
  metis_tac []);

val env_rel_append = Q.prove (
  `!genv env1 env2 env1' env2'.
    env_rel genv env1 env1' ∧
    env_rel genv env2 env2'
    ⇒
    env_rel genv (nsAppend env1 env2) (env1'++env2')`,
  induct_on `env1'` >>
  rw []
  >- (
    `env1 = nsEmpty` by fs [Once v_rel_cases] >>
    rw []) >>
  qpat_x_assum `env_rel _ _ (_::_)` mp_tac >>
  simp [Once v_rel_cases] >>
  rw [] >>
  rw [] >>
  simp [Once v_rel_cases]);

val env_rel_el = Q.prove (
  `!genv env env_i1.
    env_rel genv (alist_to_ns env) env_i1 ⇔
    LENGTH env = LENGTH env_i1 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i1)) ∧ v_rel genv (SND (EL n env)) (SND (EL n env_i1))`,
  induct_on `env` >>
  srw_tac[][v_rel_eqns] >>
  PairCases_on `h` >>
  srw_tac[][v_rel_eqns] >>
  eq_tac >>
  srw_tac[][] >>
  srw_tac[][]
  >- (cases_on `n` >>
      full_simp_tac(srw_ss())[])
  >- (cases_on `n` >>
      full_simp_tac(srw_ss())[])
  >- (cases_on `env_i1` >>
      full_simp_tac(srw_ss())[] >>
      FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
      SIMP_TAC (srw_ss()) [] >>
      srw_tac[][] >>
      qexists_tac `SND h` >>
      srw_tac[][] >>
      FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
      srw_tac[][]));

val v_rel_weakening = Q.prove (
  `(!genv v v'.
    v_rel genv v v'
    ⇒
    ∀l. v_rel (genv++l) v v') ∧
   (!genv env env'.
    env_rel genv env env'
    ⇒
    !l. env_rel (genv++l) env env') ∧
   (!genv var_map shadowers env.
    global_env_inv genv var_map shadowers env
    ⇒
    !l.global_env_inv (genv++l) var_map shadowers env)`,
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns]
  >- fs [LIST_REL_EL_EQN]
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`var_map`, `env`, `env'`, `t`, `ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`var_map`, `env`, `env'`, `t`,`ts`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`var_map`, `new_vars`, `t1`, `t2`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns, EL_APPEND1] >>
      srw_tac[][] >>
      res_tac >>
      qexists_tac `n` >>
      srw_tac[][EL_APPEND1] >>
      map_every qexists_tac [`t2`,`t3`] >>
      decide_tac)
  >- fs [LIST_REL_EL_EQN]
  >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]);

val (result_rel_rules, result_rel_ind, result_rel_cases) = Hol_reln `
  (∀genv v v'.
    f genv v v'
    ⇒
    result_rel f genv (Rval v) (Rval v')) ∧
  (∀genv v v'.
    v_rel genv v v'
    ⇒
    result_rel f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
  (!genv a.
    result_rel f genv (Rerr (Rabort a)) (Rerr (Rabort a)))`;

val result_rel_eqns = Q.prove (
  `(!genv v r.
    result_rel f genv (Rval v) r ⇔
      ?v'. f genv v v' ∧ r = Rval v') ∧
   (!genv v r.
    result_rel f genv (Rerr (Rraise v)) r ⇔
      ?v'. v_rel genv v v' ∧ r = Rerr (Rraise v')) ∧
   (!genv v r a.
    result_rel f genv (Rerr (Rabort a)) r ⇔
      r = Rerr (Rabort a))`,
  srw_tac[][result_rel_cases] >>
  metis_tac []);

val (sv_rel_rules, sv_rel_ind, sv_rel_cases) = Hol_reln `
  (!genv v v'.
    v_rel genv v v'
    ⇒
    sv_rel genv (Refv v) (Refv v')) ∧
  (!genv w.
    sv_rel genv (W8array w) (W8array w)) ∧
  (!genv vs vs'.
    LIST_REL (v_rel genv) vs vs'
    ⇒
    sv_rel genv (Varray vs) (Varray vs'))`;

val sv_rel_weakening = Q.prove (
  `(!genv sv sv_i1.
    sv_rel genv sv sv_i1
    ⇒
    ∀l. sv_rel (genv++l) sv sv_i1)`,
   srw_tac[][sv_rel_cases] >>
   metis_tac [v_rel_weakening, LIST_REL_EL_EQN]);

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!s s'.
    LIST_REL (sv_rel s'.globals) s.refs s'.refs ∧
    s.defined_types = s'.defined_types ∧
    s'.defined_mods = IMAGE HD s.defined_mods ∧
    s.clock = s'.clock ∧
    s.ffi = s'.ffi
    ⇒
    s_rel s s')`;

val (env_all_rel_rules, env_all_rel_ind, env_all_rel_cases) = Hol_reln `
  (!genv var_map env_c env_v_local env_v_top env' locals.
    (?l. env_v_local = alist_to_ns l ∧ MAP FST l = locals) ∧
    global_env_inv genv var_map (set locals) env_v_top ∧
    env_rel genv env_v_local env'
    ⇒
    env_all_rel genv var_map
      <| c := env_c; v := nsAppend env_v_local env_v_top |>
      <| c := env_c; v := env' |>
      locals)`;

val match_result_rel_def = Define
  `(match_result_rel genv env' (Match env) (Match env_i1) =
     ?env''. env = env'' ++ env' ∧ env_rel genv (alist_to_ns env'') env_i1) ∧
   (match_result_rel genv env' No_match No_match = T) ∧
   (match_result_rel genv env' Match_type_error Match_type_error = T) ∧
   (match_result_rel genv env' _ _ = F)`;

(* semantic functions respect relation *)

val do_eq = Q.prove (
  `(!v1 v2 genv r v1_i1 v2_i1.
    do_eq v1 v2 = r ∧
    v_rel genv v1 v1_i1 ∧
    v_rel genv v2 v2_i1
    ⇒
    do_eq v1_i1 v2_i1 = r) ∧
   (!vs1 vs2 genv r vs1_i1 vs2_i1.
    do_eq_list vs1 vs2 = r ∧
    LIST_REL (v_rel genv) vs1 vs1_i1 ∧
    LIST_REL (v_rel genv) vs2 vs2_i1
    ⇒
    do_eq_list vs1_i1 vs2_i1 = r)`,
  ho_match_mp_tac terminationTheory.do_eq_ind >>
  srw_tac[][terminationTheory.do_eq_def, modSemTheory.do_eq_def, v_rel_eqns] >>
  srw_tac[][] >>
  srw_tac[][terminationTheory.do_eq_def, modSemTheory.do_eq_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH >>
  full_simp_tac(srw_ss())[]
  >- metis_tac []
  >- metis_tac [] >>
  TRY (
     full_simp_tac(srw_ss())[Once v_rel_cases] >>
     srw_tac[][modSemTheory.do_eq_def] >>
     NO_TAC)
  >- (
    CASE_TAC >>
    res_tac >>
    every_case_tac >>
    full_simp_tac(srw_ss())[] >>
    metis_tac []));

val do_con_check = Q.prove (
  `!genv var_map env cn es env_i1 locals t1 ts.
    do_con_check env.c cn (LENGTH es) ∧
    env_all_rel genv var_map env env_i1 locals
    ⇒
    do_con_check env_i1.c cn (LENGTH (compile_exps t1 (bind_locals ts locals var_map) es))`,
  srw_tac[][do_con_check_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  ntac 3 (pop_assum (fn _ => all_tac)) >>
  induct_on `es` >>
  srw_tac[][compile_exp_def]);

val v_to_char_list = Q.prove (
  `!v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1`,
  ho_match_mp_tac terminationTheory.v_to_char_list_ind >>
  srw_tac[][terminationTheory.v_to_char_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_char_list_def]);

val v_to_list = Q.prove (
  `!v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      LIST_REL (v_rel genv) vs1 vs2`,
  ho_match_mp_tac terminationTheory.v_to_list_ind >>
  srw_tac[][terminationTheory.v_to_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  metis_tac [NOT_SOME_NONE, SOME_11]);

val vs_to_string = Q.prove(
  `∀v1 v2 s.
    LIST_REL (v_rel genv) v1 v2 ⇒
    vs_to_string v1 = SOME s ⇒
    vs_to_string v2 = SOME s`,
  ho_match_mp_tac terminationTheory.vs_to_string_ind
  \\ rw[terminationTheory.vs_to_string_def,vs_to_string_def]
  \\ fs[v_rel_eqns]
  \\ pop_assum mp_tac
  \\ TOP_CASE_TAC \\ strip_tac \\ rveq \\ fs[]
  \\ rw[vs_to_string_def]);

val do_app = Q.prove (
  `!genv s1 s2 op vs r s1_i1 vs_i1.
    do_app s1 op vs = SOME (s2, r) ∧
    LIST_REL (sv_rel genv) (FST s1) (FST s1_i1) ∧
    SND s1 = SND s1_i1 ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    op ≠ AallocEmpty
    ⇒
     ∃r_i1 s2_i1.
       LIST_REL (sv_rel genv) (FST s2) (FST s2_i1) ∧
       SND s2 = SND s2_i1 ∧
       result_rel v_rel genv r r_i1 ∧
       do_app s1_i1 (astOp_to_modOp op) vs_i1 = SOME (s2_i1, r_i1)`,
  rpt gen_tac >>
  Cases_on `s1` >>
  Cases_on `s1_i1` >>
  Cases_on `op = ConfigGC` >-
     (simp [astOp_to_modOp_def] >>
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def]) >>
  pop_assum mp_tac >>
  Cases_on `op` >>
  simp [astOp_to_modOp_def]
  >- ((* Opn *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Opb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Opw *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def]
      \\ rename1 `opw_lookup oo w1 w2`
      \\ Cases_on`oo` \\ fs[opw8_lookup_def,opw64_lookup_def])
  >- ((* Shift *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def]
      \\ rename1 `shift_lookup s w n`
      \\ Cases_on`w` \\ Cases_on`s` \\ fs[shift8_lookup_def,shift64_lookup_def])
  >- ((* Equality *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [Boolv_11, do_eq, eq_result_11, eq_result_distinct])
  >- ( (*FP_cmp *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      fs[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ( (*FP_uop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      fs[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ( (*FP_bop *)
      rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      fs[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Opapp *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Opassign *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_assign_def,store_v_same_type_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >-
      metis_tac [EVERY2_LUPDATE_same, sv_rel_rules] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_rel_cases] >>
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[])
  >- ((* Opref *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Opderef *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][])
  >- ((* Aw8alloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Aw8sub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def])
  >- ((* Aw8length *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def])
  >- ((* Aw8update *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      fsrw_tac[][] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][])
  >- ((* WordFromInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* WordToInt *)
    srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* CopyStrStr *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases]
    \\ simp[semanticPrimitivesTheory.prim_exn_def,modSemTheory.prim_exn_def,v_rel_eqns])
  >- ((* CopyStrAw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,semanticPrimitivesTheory.prim_exn_def,modSemTheory.prim_exn_def,v_rel_eqns]
    \\ simp[store_v_same_type_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >- ((* CopyAw8Str *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,semanticPrimitivesTheory.prim_exn_def,modSemTheory.prim_exn_def,v_rel_eqns])
  >- ((* CopyAw8Aw8 *)
    rw[semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def]
    \\ fs[v_rel_eqns,IMPLODE_EXPLODE_I,result_rel_cases,PULL_EXISTS,
          store_lookup_def,EXISTS_PROD,store_assign_def]
    \\ imp_res_tac LIST_REL_LENGTH \\ rw[]
    \\ TRY (asm_exists_tac \\ simp[])
    \\ imp_res_tac LIST_REL_EL_EQN
    \\ rfs[sv_rel_cases,semanticPrimitivesTheory.prim_exn_def,modSemTheory.prim_exn_def,v_rel_eqns]
    \\ simp[store_v_same_type_def]
    \\ match_mp_tac EVERY2_LUPDATE_same
    \\ simp[sv_rel_cases])
  >- ((* Ord *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Chr *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Chopb *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Implode *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][])
  >- ((* Strsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[stringTheory.IMPLODE_EXPLODE_I])
  >- ((* Strlen *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Strcat *)
    rw[semanticPrimitivesPropsTheory.do_app_cases,modSemTheory.do_app_def]
    \\ fs[LIST_REL_def]
    \\ imp_res_tac v_to_list \\ fs[]
    \\ imp_res_tac vs_to_string \\ fs[result_rel_cases,v_rel_eqns] )
  >- ((* VfromList *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      imp_res_tac v_to_list >>
      srw_tac[][])
  >- ((* Vsub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ])
  >- ((* Vlength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Aalloc *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, LIST_REL_REPLICATE_same] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Asub *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      decide_tac)
  >- ((* Alength *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[store_lookup_def, sv_rel_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      res_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      metis_tac [store_v_distinct, store_v_11, LIST_REL_LENGTH])
  >- ((* Aupdate *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][] >>
      decide_tac)
  >- ((* FFI *)
      srw_tac[][semanticPrimitivesPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def, IMPLODE_EXPLODE_I] >>
      imp_res_tac LIST_REL_LENGTH >>
      srw_tac[][] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[]));

val find_recfun = Q.prove (
  `!x funs e var_map y t.
    find_recfun x funs = SOME (y,e)
    ⇒
    find_recfun x (compile_funs t var_map funs) =
      SOME (y, compile_exp t (nsBind y (Var_local t y) var_map) e)`,
   induct_on `funs` >>
   srw_tac[][Once find_recfun_def, compile_exp_def] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[Once find_recfun_def, compile_exp_def]);

val do_app_rec_help = Q.prove (
  `!genv var_map env_v_local env_v_local' env_v_top funs t.
    env_rel genv env_v_local env_v_local' ∧
    global_env_inv genv var_map (set (MAP FST env_v_local')) env_v_top ∧
    LENGTH ts = LENGTH funs' + LENGTH env_v_local'
    ⇒
     env_rel genv
       (alist_to_ns
          (MAP
             (λ(f,n,e).
                (f,
                 Recclosure
                   <|v := nsAppend env_v_local env_v_top; c := env_c|>
                   funs' f)) funs))
       (MAP
          (λ(fn,n,e).
             (fn,
              Recclosure (env_c,env_v_local')
                (compile_funs t
                   (FOLDR (λ(x,v) e. nsBind x v e) var_map
                      (MAP2 (λt x. (x,Var_local t x)) ts
                         (MAP FST funs' ++ MAP FST env_v_local'))) funs')
                fn))
          (compile_funs t
             (FOLDR (λ(x,v) e. nsBind x v e) var_map
                (MAP2 (λt x. (x,Var_local t x)) ts
                   (MAP FST funs' ++ MAP FST env_v_local'))) funs))`,
  induct_on `funs`
  >- srw_tac[][v_rel_eqns, compile_exp_def] >>
  rw [] >>
  PairCases_on`h`>>fs[compile_exp_def]>>
  simp[v_rel_eqns]>>
  simp [Once v_rel_cases] >>
  MAP_EVERY qexists_tac [`var_map`, `env_v_top`, `env_v_local`, `t`,`ts`] >>
  simp[compile_exp_def,bind_locals_def]>>
  simp_tac (std_ss) [GSYM APPEND, namespaceTheory.nsBindList_def])

val global_env_inv_add_locals = Q.prove (
  `!genv var_map locals1 locals2 env.
    global_env_inv genv var_map locals1 env
    ⇒
    global_env_inv genv var_map (locals2 ∪ locals1) env`,
  srw_tac[][v_rel_eqns] >>
  metis_tac []);

val global_env_inv_extend2 = Q.prove (
  `!genv var_map env new_vars env' locals.
    set (MAP (Short o FST) new_vars) = nsDom env' ∧
    global_env_inv genv var_map locals env ∧
    global_env_inv genv (alist_to_ns new_vars) locals env'
    ⇒
    global_env_inv genv (nsBindList new_vars var_map) locals (nsAppend env' env)`,
  srw_tac[][v_rel_eqns, GSYM nsAppend_to_nsBindList] >>
  fs [nsLookup_nsAppend_some, nsLookup_alist_to_ns_none, nsLookup_alist_to_ns_some] >>
  res_tac >>
  fs [] >>
  rw [] >>
  qexists_tac `n` >>
  rw [] >>
  Cases_on `x` >>
  fs [] >>
  rw []
  >- (
    `Short n' ∉ nsDom env'` by metis_tac [nsLookup_nsDom, NOT_SOME_NONE] >>
    qexists_tac`t` >>
    disj2_tac >>
    rw [ALOOKUP_NONE] >>
    qpat_x_assum `_ = nsDom _` (assume_tac o GSYM) >>
    fs [MEM_MAP] >>
    fs [namespaceTheory.id_to_mods_def])
  >- (
    fs [namespaceTheory.id_to_mods_def] >>
    Cases_on `p1` >>
    fs [] >>
    rw []));

val lookup_build_rec_env_lem = Q.prove (
  `!x cl_env funs' funs.
    ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure cl_env funs' fn)) funs) x = SOME v
    ⇒
    v = semanticPrimitives$Recclosure cl_env funs' x`,
  induct_on `funs` >>
  srw_tac[][] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[]);

val do_opapp = Q.prove (
  `!genv vs vs_i1 env e.
    do_opapp vs = SOME (env, e) ∧
    LIST_REL (v_rel genv) vs vs_i1
    ⇒
     ∃var_map env_i1 locals t1 ts.
       env_all_rel genv var_map env env_i1 locals ∧
       LENGTH ts = LENGTH locals ∧
       do_opapp vs_i1 = SOME (env_i1, compile_exp t1 (bind_locals ts locals var_map) e)`,
   srw_tac[][do_opapp_cases, modSemTheory.do_opapp_def] >>
   full_simp_tac(srw_ss())[LIST_REL_CONS1] >>
   srw_tac[][]
   >- (qpat_x_assum `v_rel genv (Closure _ _ _) _` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       MAP_EVERY qexists_tac [`var_map`, `n :: MAP FST env_v_local'`, `t`, `ts`] >>
       srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def, FOLDR_MAP] >>
       fs[ADD1]>>
       MAP_EVERY qexists_tac [`nsBind n v2 env_v_local`, `env_v_top`] >>
       srw_tac[][v_rel_eqns]
       >- (
         drule env_rel_dom >>
         rw [MAP_o] >>
         rw_tac list_ss [GSYM alist_to_ns_cons] >>
         qexists_tac`(n,v2)::l`>>simp[])>>
       full_simp_tac(srw_ss())[v_rel_eqns] >>
       metis_tac [])
   >- (qpat_x_assum `v_rel genv (Recclosure _ _ _) _` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       imp_res_tac find_recfun >>
       srw_tac[][]
       >- (MAP_EVERY qexists_tac [`var_map`, `n'' :: MAP FST funs ++ MAP FST env_v_local'`,`t`,`t::ts`] >>
           srw_tac[][bind_locals_def, env_all_rel_cases, namespaceTheory.nsBindList_def] >>
           srw_tac[][]>>fs[]
           >- (MAP_EVERY qexists_tac [`nsBind n'' v2 (build_rec_env funs <|v := nsAppend env_v_local env_v_top; c := env_c|> env_v_local)`, `env_v_top`] >>
               srw_tac[][semanticPrimitivesPropsTheory.build_rec_env_merge, EXTENSION]
               >- (
                 imp_res_tac env_rel_dom >>
                 simp [] >>
                 rw_tac list_ss [GSYM alist_to_ns_cons] >>
                 simp [] >>
                 simp [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
                 rpt (pop_assum kall_tac) >>
                 induct_on `funs` >>
                 rw [] >>
                 pairarg_tac >>
                 rw [])
               >- metis_tac [INSERT_SING_UNION, global_env_inv_add_locals, UNION_COMM]
               >- (
                 simp [v_rel_eqns, build_rec_env_merge] >>
                 match_mp_tac env_rel_append >>
                 simp [] >>
                 metis_tac [do_app_rec_help]))
           >- (
            simp[compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
            full_simp_tac(srw_ss())[FST_triple])
           )
       >- (MAP_EVERY qexists_tac [`nsBindList new_vars var_map`, `[n'']`, `t1`, `[t2]`] >>
           srw_tac[][env_all_rel_cases, namespaceTheory.nsBindList_def,bind_locals_def] >>
           rw [GSYM namespaceTheory.nsBindList_def] >>
           MAP_EVERY qexists_tac [`nsSing n'' v2`, `build_rec_env funs env'' env''.v`] >>
           srw_tac[][semanticPrimitivesTheory.sem_env_component_equality, semanticPrimitivesPropsTheory.build_rec_env_merge, EXTENSION]
           >- (
             qexists_tac `[(n'',v2)]` >>
             rw [namespaceTheory.nsSing_def, namespaceTheory.nsBind_def,
                 namespaceTheory.nsEmpty_def])
           >- (
             match_mp_tac global_env_inv_extend2 >>
             rw []
             >- (
               `MAP (Short:tvarN -> (tvarN, tvarN) id) (MAP FST new_vars) = MAP Short (MAP FST (REVERSE funs))` by metis_tac [] >>
               fs [MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
             >- metis_tac [global_env_inv_add_locals, UNION_EMPTY]
             >- (
               srw_tac[][v_rel_eqns] >>
               fs [nsLookup_alist_to_ns_some] >>
               rw [] >>
               `MEM x' (MAP FST funs)`
                         by (imp_res_tac ALOOKUP_MEM >>
                             full_simp_tac(srw_ss())[MEM_MAP] >>
                             PairCases_on `y` >>
                             srw_tac[][] >>
                             full_simp_tac(srw_ss())[] >>
                             metis_tac [FST, MEM_MAP, pair_CASES]) >>
               res_tac >>
               qexists_tac `n` >>
               srw_tac[][] >>
               drule lookup_build_rec_env_lem >>
               srw_tac[][Once v_rel_cases] >>
               MAP_EVERY qexists_tac [`var_map`, `new_vars`, `t2`, `t3`] >>
               srw_tac[][find_recfun_ALOOKUP]))
           >- (
             simp [Once v_rel_cases] >>
             qexists_tac `v2` >>
             qexists_tac `nsEmpty` >>
             rw [namespaceTheory.nsSing_def, namespaceTheory.nsEmpty_def,
                 namespaceTheory.nsBind_def] >>
             simp [Once v_rel_cases, namespaceTheory.nsEmpty_def]))));

val build_conv = Q.prove (
  `!genv var_map env cn vs v vs' env_i1 locals.
    build_conv env.c cn vs = SOME v ∧
    env_all_rel genv var_map env env_i1 locals ∧
    LIST_REL (v_rel genv) vs vs'
    ⇒
    ∃v'.
      v_rel genv v v' ∧
      build_conv env_i1.c cn vs' = SOME v'`,
  srw_tac[][semanticPrimitivesTheory.build_conv_def, modSemTheory.build_conv_def] >>
  every_case_tac >>
  srw_tac[][Once v_rel_cases] >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >> rev_full_simp_tac(srw_ss())[]);

val pat_bindings_compile_pat = Q.store_thm ("pat_bindings_compile_pat[simp]",
`!(p:ast$pat) vars. pat_bindings (compile_pat p) vars = pat_bindings p vars`,
  ho_match_mp_tac compile_pat_ind >>
  simp [compile_pat_def, astTheory.pat_bindings_def] >>
  induct_on `ps` >>
  rw [] >>
  fs [astTheory.pat_bindings_def, PULL_FORALL]);

val pmatch = Q.prove (
  `(!cenv s p v env r env' env'' genv env_i1 s_i1 v_i1.
    pmatch cenv s p v env = r ∧
    env = env' ++ env'' ∧
    LIST_REL (sv_rel genv) s s_i1 ∧
    v_rel genv v v_i1 ∧
    env_rel genv (alist_to_ns env') env_i1
    ⇒
    ?r_i1.
      pmatch cenv s_i1 (compile_pat p) v_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1) ∧
   (!cenv s ps vs env r env' env'' genv env_i1 s_i1 vs_i1.
    pmatch_list cenv s ps vs env = r ∧
    env = env' ++ env'' ∧
    LIST_REL (sv_rel genv) s s_i1 ∧
    LIST_REL (v_rel genv) vs vs_i1 ∧
    env_rel genv (alist_to_ns env') env_i1
    ⇒
    ?r_i1.
      pmatch_list cenv s_i1 (MAP compile_pat ps) vs_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1)`,
  ho_match_mp_tac terminationTheory.pmatch_ind >>
  srw_tac[][terminationTheory.pmatch_def, modSemTheory.pmatch_def, compile_pat_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, modSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >> TRY (full_simp_tac(srw_ss())[Once v_rel_cases] >>
          srw_tac[][modSemTheory.pmatch_def, match_result_rel_def] >>
          FAIL_TAC "")
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def]
      >- (full_simp_tac(srw_ss())[store_lookup_def] >>
          metis_tac [])
      >- (full_simp_tac(srw_ss())[store_lookup_def] >>
          metis_tac [])
      >- (FIRST_X_ASSUM match_mp_tac >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[store_lookup_def, LIST_REL_EL_EQN, sv_rel_cases] >>
          res_tac >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][])
      >> (full_simp_tac(srw_ss())[store_lookup_def, LIST_REL_EL_EQN] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[sv_rel_cases] >>
          res_tac >>
          full_simp_tac(srw_ss())[]))
  >- (CASE_TAC >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      srw_tac[][] >>
      pop_assum mp_tac >>
      pop_assum mp_tac >>
      res_tac >>
      srw_tac[][] >>
      CCONTR_TAC >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [match_result_rel_def, match_result_distinct])) ;

(* compiler correctness *)

val s = mk_var("s",
  ``evaluate$evaluate`` |> type_of |> strip_fun |> #1 |> el 1
  |> type_subst[alpha |-> ``:'ffi``]);

val opt_bind_lem = Q.prove (
  `opt_bind NONE = \x y.y`,
  rw [FUN_EQ_THM, libTheory.opt_bind_def]);

val env_updated_lem = Q.prove (
  `env with v updated_by (λy. y) = (env : modSem$environment)`,
  rw [environment_component_equality]);

val evaluate_foldr_let_err = Q.prove (
  `!env s s' exps e x.
    modSem$evaluate env s exps = (s', Rerr x)
    ⇒
    evaluate env s [FOLDR (Let t NONE) e exps] = (s', Rerr x)`,
  Induct_on `exps` >>
  rw [evaluate_def] >>
  fs [Once evaluate_cons] >>
  every_case_tac >>
  fs [evaluate_def] >>
  rw [] >>
  first_x_assum drule >>
  disch_then (qspec_then `e` mp_tac) >>
  rw [] >>
  every_case_tac >>
  fs [opt_bind_lem, env_updated_lem]);

val compile_exp_correct' = Q.prove (
   `(∀^s env es res.
     evaluate$evaluate s env es = res ⇒
     SND res ≠ Rerr (Rabort Rtype_error) ⇒
     !var_map s' r env_i1 s_i1 es_i1 locals t ts.
       res = (s',r) ∧
       env_all_rel s_i1.globals var_map env env_i1 locals ∧
       s_rel s s_i1 ∧
       LENGTH ts = LENGTH locals ∧
       es_i1 = compile_exps t (bind_locals ts locals var_map) es
       ⇒
       ?s'_i1 r_i1.
         result_rel (LIST_REL o v_rel) s_i1.globals r r_i1 ∧
         s_rel s' s'_i1 ∧
         modSem$evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1)) ∧
   (∀^s env v pes err_v res.
     evaluate$evaluate_match s env v pes err_v = res ⇒
     SND res ≠ Rerr (Rabort Rtype_error) ⇒
     !var_map s' r env_i1 s_i1 v_i1 pes_i1 err_v_i1 locals t ts.
       (res = (s',r)) ∧
       env_all_rel s_i1.globals var_map env env_i1 locals ∧
       s_rel s s_i1 ∧
       v_rel s_i1.globals v v_i1 ∧
       LENGTH ts = LENGTH locals ∧
       pes_i1 = compile_pes t (bind_locals ts locals var_map) pes ∧
       v_rel s_i1.globals err_v err_v_i1
       ⇒
       ?s'_i1 r_i1.
         result_rel (LIST_REL o v_rel) s_i1.globals r r_i1 ∧
         s_rel s' s'_i1 ∧
         modSem$evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1))`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def, modSemTheory.evaluate_def,compile_exp_def] >>
  full_simp_tac(srw_ss())[result_rel_eqns, v_rel_eqns] >>
  TRY(first_assum(split_pair_case0_tac o lhs o concl) >> full_simp_tac(srw_ss())[])
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`t`,`ts`] strip_assume_tac)>>
    rfs[]>>
    first_assum(fn th => subterm split_pair_case0_tac (concl th)) >> full_simp_tac(srw_ss())[] >>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >>
      asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] ) >>
    strip_tac >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`t`,`ts`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[])
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`t`,`ts`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[])
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >>
    disch_then (qspecl_then[`t`,`ts`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] )
  >- (
    reverse (srw_tac[][])
    >- metis_tac [do_con_check, EVERY2_REVERSE, compile_exps_reverse]
    >- metis_tac [do_con_check, EVERY2_REVERSE, compile_exps_reverse] >>
    `env_i1.c = env.c` by full_simp_tac(srw_ss())[env_all_rel_cases] >>
    rename1` _ = (st',vv)`>>
    `vv = Rerr (Rabort Rtype_error) ∨
     (?err. vv = Rerr err ∧ err ≠ Rabort Rtype_error) ∨
     (?v. vv = Rval v)`
       by (Cases_on `vv` >> full_simp_tac(srw_ss())[]) >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][result_rel_cases] >>
    first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
    pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
    pop_assum (qspecl_then [`t`,`ts`] strip_assume_tac)>> rfs[]>>
    simp [GSYM compile_exps_reverse] >>
    full_simp_tac(srw_ss())[result_rel_cases] >>
    rpt var_eq_tac >>
    Cases_on `build_conv env.c cn (REVERSE v)` >>
    full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >>
    simp [] >>
    every_case_tac
    >- metis_tac [NOT_SOME_NONE, build_conv, EVERY2_REVERSE] >>
    simp []
    >- metis_tac [SOME_11, build_conv, EVERY2_REVERSE])
  >- ((* Variable lookup *)
    Cases_on `nsLookup env.v n` >>
    fs [env_all_rel_cases] >>
    rw [] >>
    fs [nsLookup_nsAppend_some]
    >- ((* Local variable *)
      fs [nsLookup_alist_to_ns_some,bind_locals_def] >>
      rw [] >>
      drule env_rel_lookup >>
      disch_then drule >>
      rw [GSYM nsAppend_to_nsBindList] >>
      simp[MAP2_MAP]>>
      every_case_tac >>
      fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
          nsLookup_alist_to_ns_none]>>
      fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]>>
      `(λ(p1:tra,p2:tvarN). p2) = SND` by fs[FUN_EQ_THM,FORALL_PROD]>>
      fs[]>>rfs[MAP_ZIP]
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP]
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP]
      >- (
        drule ALOOKUP_MEM >>
        rw [MEM_MAP] >>
        pairarg_tac>>fs[]>>
        simp [evaluate_def, result_rel_cases])
      >- metis_tac [ALOOKUP_MEM,PAIR,FST,MEM_MAP])
    >- ( (* top-level variable *)
      rw [GSYM nsAppend_to_nsBindList,bind_locals_def] >>
      fs [nsLookup_alist_to_ns_none] >>
      fs [v_rel_eqns, ALOOKUP_NONE, METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
      first_x_assum drule >>
      rw [] >>
      simp[MAP2_MAP]>>
      every_case_tac >>
      fs [nsLookup_nsAppend_some, nsLookup_nsAppend_none, nsLookup_alist_to_ns_some,
          nsLookup_alist_to_ns_none]>>
      fs[ALOOKUP_NONE,MAP_MAP_o,o_DEF,LAMBDA_PROD]
      >-
        (Cases_on`p1`>>fs[])
      >- (
        drule ALOOKUP_MEM >>
        simp[MEM_MAP,MEM_ZIP,EXISTS_PROD]>>
        rw[]>>
        metis_tac[MEM_EL,LENGTH_MAP])
      >- (
        rfs [ALOOKUP_TABULATE] >>
        rw [] >>
        simp [evaluate_def, result_rel_cases])))
  >- (* Closure creation *)
     (srw_tac[][Once v_rel_cases] >>
      full_simp_tac(srw_ss())[env_all_rel_cases] >>
      srw_tac[][] >>
      MAP_EVERY qexists_tac [`var_map`, `env_v_top`, `alist_to_ns l`,`t`,`(t§2)::ts`] >>
      imp_res_tac env_rel_dom >>
      srw_tac[][] >>
      simp [bind_locals_def, namespaceTheory.nsBindList_def] >>
      fs [ADD1]>>
      metis_tac[LENGTH_MAP])
  (* function application *)
  >- (
    srw_tac [boolSimps.DNF_ss] [PULL_EXISTS]
    >- (
      (* empty array creation *)
      every_case_tac >>
      fs [semanticPrimitivesTheory.do_app_def] >>
      every_case_tac >>
      fs [] >>
      rw [evaluate_def, modSemTheory.do_app_def] >>
      fs []
      >- (
        drule (CONJUNCT1 evaluatePropsTheory.evaluate_length) >>
        Cases_on `es` >>
        rw [LENGTH_NIL] >>
        fs [] >>
        simp [compile_exp_def, evaluate_def] >>
        pairarg_tac >>
        fs [store_alloc_def, compile_exp_def] >>
        rpt var_eq_tac >>
        first_x_assum drule >>
        disch_then(qspecl_then[`t`,`ts`] mp_tac)>>
        simp [] >>
        rw [result_rel_cases, Once v_rel_cases] >>
        simp [do_app_def] >>
        pairarg_tac >>
        fs [store_alloc_def] >>
        simp [Once v_rel_cases] >>
        fs [s_rel_cases] >>
        rw []
        >- metis_tac [LIST_REL_LENGTH] >>
        simp [REPLICATE, sv_rel_cases])
      >- (
        first_x_assum drule >>
        disch_then(qspecl_then[`t`,`ts`] mp_tac)>>
        rw [] >>
        qexists_tac `s'_i1` >>
        qexists_tac `r_i1` >>
        simp [] >>
        fs [compile_exps_reverse] >>
        `?e'. r_i1 = Rerr e'` by fs [result_rel_cases] >>
        rw [] >>
        metis_tac [evaluate_foldr_let_err])) >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then(qspecl_then[`t`,`ts`] strip_assume_tac)>> rfs[]>>
    full_simp_tac(srw_ss())[compile_exps_reverse] >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    TRY (simp [evaluate_def] >> NO_TAC) >>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    ntac 2 (BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]) >- (
      BasicProvers.TOP_CASE_TAC >>
      drule do_opapp >>
      full_simp_tac(srw_ss())[] >>
      imp_res_tac EVERY2_REVERSE >>
      disch_then drule >> strip_tac >>
      IF_CASES_TAC >> strip_tac >> full_simp_tac(srw_ss())[] >> rveq >- (
        full_simp_tac(srw_ss())[] >> asm_exists_tac >> srw_tac[][] >>
        full_simp_tac(srw_ss())[s_rel_cases, astOp_to_modOp_def, evaluate_def] ) >>
      rev_full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_globals >>
      pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_abbrev_tac`_ = _ ss` >>
      `ss.globals = (dec_clock ss).globals` by EVAL_TAC >>
      full_simp_tac(srw_ss())[Abbr`ss`] >>
      first_x_assum drule >>
      disch_then(qspecl_then [`t1`,`ts'`] mp_tac)>>
      impl_tac >- (
        full_simp_tac(srw_ss())[s_rel_cases,modSemTheory.dec_clock_def,evaluateTheory.dec_clock_def] ) >>
      strip_tac >> full_simp_tac(srw_ss())[PULL_EXISTS] >>
      asm_exists_tac >> full_simp_tac(srw_ss())[] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[s_rel_cases, astOp_to_modOp_def, evaluate_def] >>
      metis_tac []) >>
    BasicProvers.TOP_CASE_TAC >>
    BasicProvers.TOP_CASE_TAC >>
    strip_tac >> rveq >>
    drule do_app >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    ONCE_REWRITE_TAC[CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    imp_res_tac EVERY2_REVERSE >>
    disch_then drule >>
    full_simp_tac(srw_ss())[s_rel_cases] >>
    CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[pair_default_qp])[])) >>
    disch_then drule >> strip_tac >>
    simp[] >>
    `astOp_to_modOp op ≠ Opapp`
    by (
      rw [astOp_to_modOp_def] >>
      Cases_on `op` >>
      simp [] >>
      fs []) >>
    full_simp_tac(srw_ss())[PULL_EXISTS,result_rel_cases, evaluate_def])
  >- (
    fs[markerTheory.Abbrev_def]>>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
      BasicProvers.TOP_CASE_TAC >> srw_tac[][evaluate_def] ) >>
    BasicProvers.TOP_CASE_TAC >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    imp_res_tac evaluatePropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[terminationTheory.do_log_thm] >> srw_tac[][] >>
      pop_assum mp_tac >>
      BasicProvers.TOP_CASE_TAC >>
      BasicProvers.TOP_CASE_TAC >>
      BasicProvers.TOP_CASE_TAC >> srw_tac[][] >>
      BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >>
      srw_tac[][evaluate_def] >>
      asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >>
      full_simp_tac(srw_ss())[] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[Once v_rel_cases] >>
      srw_tac[][do_if_def] >> full_simp_tac(srw_ss())[] >>
      EVAL_TAC >>
      srw_tac[][state_component_equality] >>
      pop_assum mp_tac >> EVAL_TAC >>
      pop_assum mp_tac >> EVAL_TAC >>
      full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    first_x_assum drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    asm_exists_tac >> simp[] >>
    asm_exists_tac >> simp[] >>
    full_simp_tac(srw_ss())[terminationTheory.do_log_thm] >>
    qpat_x_assum`_ = SOME _`mp_tac >>
    srw_tac[][evaluate_def] >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[Once v_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    srw_tac[][do_if_def] >>
    EVAL_TAC >>
    full_simp_tac(srw_ss())[] >>
    pop_assum mp_tac >> EVAL_TAC >>
    pop_assum mp_tac >> EVAL_TAC >>
    srw_tac[][])
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    asm_exists_tac >> simp[] >>
    asm_exists_tac >> simp[] >>
    imp_res_tac evaluatePropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.do_if_def] >>
    qpat_x_assum`_ = SOME _`mp_tac >> srw_tac[][] >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[] >> rveq >>
    full_simp_tac(srw_ss())[Once v_rel_cases,semanticPrimitivesTheory.Boolv_def] >>
    srw_tac[][do_if_def] >>
    full_simp_tac(srw_ss())[] >>
    pop_assum mp_tac >> EVAL_TAC >>
    pop_assum mp_tac >> EVAL_TAC >>
    srw_tac[][] )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    first_x_assum drule >> simp[] >> strip_tac >>
    qhdtm_x_assum`result_rel`mp_tac >>
    simp[Once result_rel_cases] >> strip_tac >>
    imp_res_tac evaluatePropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    full_simp_tac(srw_ss())[] >>
    first_x_assum drule >>
    simp[Bindv_def] >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    simp[] )
  >- (
    qpat_x_assum`_ ⇒ _`mp_tac >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >>
    disch_then (qspecl_then [`t`,`ts`] strip_assume_tac)>>rfs[]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      Cases_on`xo`>> srw_tac[][compile_exp_def,evaluate_def] >>
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    qhdtm_x_assum`result_rel`mp_tac >>
    simp[Once result_rel_cases] >> strip_tac >>
    Cases_on`xo`>> srw_tac[][compile_exp_def,evaluate_def] >- (
      first_x_assum match_mp_tac >>
      simp[libTheory.opt_bind_def] >>
      qpat_abbrev_tac`env2 = env_i1 with v updated_by _` >>
      `env2 = env_i1` by (
        simp[environment_component_equality,Abbr`env2`,libTheory.opt_bind_def] ) >>
      simp[namespaceTheory.nsOptBind_def] ) >>
    qpat_abbrev_tac`env2 = env_i1 with v updated_by _` >>
    first_x_assum(qspecl_then[`var_map`,`env2`]mp_tac) >>
    simp[Abbr`env2`] >>
    disch_then(qspecl_then[`s'_i1`,`x::locals`,`t`,`(t § 2)::ts`] mp_tac)>>
    impl_tac >- (
      full_simp_tac(srw_ss())[env_all_rel_cases] >>
      full_simp_tac(srw_ss())[namespaceTheory.nsOptBind_def,libTheory.opt_bind_def] >>
      srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][] >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      simp[GSYM CONJ_ASSOC] >>
      drule global_env_inv_add_locals >>
      disch_then(qspec_then`{x}`strip_assume_tac) >>
      simp[Once INSERT_SING_UNION] >>
      asm_exists_tac >> simp[] >>
      qexists_tac `(x,HD a)::l` >>
      simp [v_rel_eqns] >>
      imp_res_tac evaluate_sing >>
      full_simp_tac(srw_ss())[] ) >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    fs [GSYM nsAppend_to_nsBindList,bind_locals_def])
  >- (
    srw_tac[][markerTheory.Abbrev_def] >>
    srw_tac[][evaluate_def] >>
    TRY (fs [compile_funs_map,MAP_MAP_o,o_DEF,UNCURRY] >>
         full_simp_tac(srw_ss())[FST_triple,ETA_AX] >>
         NO_TAC) >>
    fs [GSYM nsAppend_to_nsBindList] >>
    rw_tac std_ss [GSYM MAP_APPEND] >>
    simp[nsAppend_bind_locals]>>
    first_x_assum match_mp_tac >> simp[] >>
    full_simp_tac(srw_ss())[env_all_rel_cases] >>
    rw [] >>
    qexists_tac `build_rec_env funs <|v := nsAppend (alist_to_ns l) env_v_top; c := env_c|> (alist_to_ns l)` >>
    qexists_tac `env_v_top` >>
    rw [semanticPrimitivesPropsTheory.build_rec_env_merge,build_rec_env_merge]
    >- (
      simp [MAP_MAP_o, UNCURRY, combinTheory.o_DEF] >>
      metis_tac [])
    >- metis_tac [global_env_inv_add_locals] >>
    rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
    match_mp_tac env_rel_append >>
    rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    rw [env_rel_el, EL_MAP, UNCURRY] >>
    simp [Once v_rel_cases] >>
    qexists_tac `var_map` >>
    qexists_tac `env_v_top` >>
    qexists_tac `alist_to_ns l` >>
    qexists_tac `t` >>
    qexists_tac `REPLICATE (LENGTH funs) t ++ ts` >>
    drule env_rel_dom >>
    rw [compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, UNCURRY,
        bind_locals_def, nsAppend_to_nsBindList]
    >- metis_tac[]
    >- metis_tac [LENGTH_MAP])
  >-
    (Cases_on`l`>>fs[evaluate_def,compile_exp_def])
  >- (
    fs[markerTheory.Abbrev_def]>>
    qpat_x_assum`_ = (_,r)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
      rev_full_simp_tac(srw_ss())[] >>
      drule (CONJUNCT1 pmatch) >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      simp[GSYM CONJ_ASSOC] >>
      qhdtm_x_assum`s_rel`mp_tac >>
      simp[Once s_rel_cases] >> strip_tac >>
      disch_then drule >>
      disch_then drule >>
      qhdtm_x_assum`env_all_rel`mp_tac >>
      simp[Once env_all_rel_cases] >> strip_tac >>
      simp [v_rel_eqns] >>
      strip_tac >>
      qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm` >>
      Cases_on`mm`>>full_simp_tac(srw_ss())[match_result_rel_def] >>
      pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
      simp[evaluate_def]>>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      first_x_assum match_mp_tac >>
      simp[s_rel_cases] >>
      simp[env_all_rel_cases] >>
      metis_tac[] ) >>
    rfs [] >>
    drule (CONJUNCT1 pmatch) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    simp[GSYM CONJ_ASSOC] >>
    qhdtm_x_assum`s_rel`mp_tac >>
    simp[Once s_rel_cases] >> strip_tac >>
    disch_then drule >>
    disch_then drule >>
    qhdtm_x_assum`env_all_rel`mp_tac >>
    simp[Once env_all_rel_cases] >> strip_tac >>
    simp [v_rel_eqns] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm` >>
    Cases_on`mm`>>full_simp_tac(srw_ss())[match_result_rel_def] >>
    pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
    simp[evaluate_def]>>
    ONCE_REWRITE_TAC[CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    qspec_then `pat_bindings p []` assume_tac (nsBindList_pat_tups_bind_locals|>INST_TYPE[alpha|->``:tvarN``])>>
    fs[]>>
    first_x_assum match_mp_tac >>
    simp[s_rel_cases] >>
    simp[env_all_rel_cases] >>
    qexists_tac `alist_to_ns (a ++ l)` >>
    qexists_tac`env_v_top` >>
    rw []
    >- (
      drule (CONJUNCT1 pmatch_extend) >>
      rw [] >>
      drule env_rel_dom >>
      rw [])
    >- metis_tac [global_env_inv_add_locals]
    >- (
      rw_tac std_ss [GSYM nsAppend_alist_to_ns] >>
      match_mp_tac env_rel_append >>
      rw [])));

val compile_exp_correct = Q.prove (
  `∀s env es var_map s' r s_i1 t.
     evaluate s env es = (s',r) ∧
     s_rel s s_i1 ∧
     SND (evaluate s env es) ≠ Rerr (Rabort Rtype_error) ∧
     global_env_inv s_i1.globals var_map {} env.v ⇒
     ∃s'_i1 r_i1.
       result_rel (LIST_REL ∘ v_rel) s_i1.globals r r_i1 ∧
       s_rel s' s'_i1 ∧
       evaluate <| c := env.c; v := [] |> s_i1 (compile_exps t var_map es) = (s'_i1,r_i1)`,
  rw [] >>
  drule (CONJUNCT1 compile_exp_correct') >>
  rfs [env_all_rel_cases] >>
  disch_then (qspecl_then [`var_map`, `<| c := env.c; v := [] |>`, `s_i1`, `[]`,`t`,`[]`] mp_tac) >>
  simp [PULL_EXISTS, sem_env_component_equality] >>
  impl_tac
  >- simp [v_rel_eqns] >>
  simp [bind_locals_def,namespaceTheory.nsBindList_def]);

val ALOOKUP_alloc_defs_EL = Q.prove (
  `!funs l n m.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    n < LENGTH funs
    ⇒
    ∃tt.
    ALOOKUP (alloc_defs m l (MAP FST (REVERSE funs))) (EL n (MAP FST funs)) =
      SOME (Var_global tt (l + LENGTH funs − (n + 1)))`,
  gen_tac >>
  Induct_on `LENGTH funs` >>
  rw [] >>
  Cases_on `REVERSE funs` >>
  fs [alloc_defs_def] >>
  rw []
  >- (
    `LENGTH funs = n + 1` suffices_by decide_tac >>
    rfs [EL_MAP] >>
    `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
    fs [] >>
    rw [] >>
    CCONTR_TAC >>
    fs [] >>
    `n < LENGTH t` by decide_tac >>
    fs [EL_APPEND1, FST_triple] >>
    fs [ALL_DISTINCT_APPEND, MEM_MAP, FORALL_PROD] >>
    fs [MEM_EL, EL_REVERSE] >>
    `PRE (LENGTH t - n) < LENGTH t` by decide_tac >>
    fs [METIS_PROVE [] ``~x ∨ y ⇔ x ⇒ y``] >>
    metis_tac [FST, pair_CASES, PAIR_EQ])
  >- (
    `funs = REVERSE (h::t)` by metis_tac [REVERSE_REVERSE] >>
    fs [] >>
    rw [] >>
    Cases_on `n = LENGTH t` >>
    fs [EL_APPEND2] >>
    `n < LENGTH t` by decide_tac >>
    fs [EL_APPEND1, ADD1] >>
    first_x_assum (qspec_then `REVERSE t` mp_tac) >>
    simp [] >>
    fs [ALL_DISTINCT_APPEND, ALL_DISTINCT_REVERSE, MAP_REVERSE]>>
    disch_then(qspec_then`l+1` assume_tac)>>fs[]));

val letrec_global_env_lem3 = Q.prove (
  `!funs x genv cenv var_map t tt.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    MEM x (MAP FST funs)
    ⇒
    ∃n y e' t0 t2 t3.
      ALOOKUP (alloc_defs t (LENGTH genv) (MAP FST (REVERSE funs))) x = SOME (Var_global t0 n) ∧
      n < LENGTH genv + LENGTH funs ∧
      find_recfun x funs = SOME (y,e') ∧
      EL n (genv ++ MAP (λ(p1,p1',p2). SOME (Closure (cenv,[]) p1' (compile_exp tt (nsBind p1' (Var_local tt p1') (nsAppend (alist_to_ns (alloc_defs t (LENGTH genv) (MAP FST (REVERSE funs)))) var_map)) p2))) (REVERSE funs)) = SOME (Closure (cenv,[]) y
                (compile_exp t2 (nsBindList ((y,Var_local t3 y)::alloc_defs t (LENGTH genv) (MAP FST (REVERSE funs))) var_map) e'))`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[MEM_EL] >>
  srw_tac[][] >>
  MAP_EVERY qexists_tac [`LENGTH genv + LENGTH funs - (n + 1)`, `FST (SND (EL n funs))`, `SND (SND (EL n funs))`]>>
  CONV_TAC (RESORT_EXISTS_CONV (List.rev))>>
  qexists_tac`tt`>>qexists_tac`tt`>>
  simp[GSYM PULL_EXISTS]>>
  rw[EL_APPEND2]
  >- metis_tac [ALOOKUP_alloc_defs_EL]
  >- (srw_tac[][find_recfun_ALOOKUP] >>
      rpt (pop_assum mp_tac) >>
      Q.SPEC_TAC (`n`, `n`) >>
      induct_on `funs` >>
      srw_tac[][] >>
      cases_on `0 < n` >>
      srw_tac[][EL_CONS] >>
      PairCases_on `h` >>
      full_simp_tac(srw_ss())[]
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[] >>
          `PRE n < LENGTH funs` by decide_tac
          >- (full_simp_tac(srw_ss())[MEM_MAP, FST_triple] >>
              FIRST_X_ASSUM (qspecl_then [`EL (PRE n) funs`] mp_tac) >>
              srw_tac[][EL_MAP, EL_MEM])
          >- metis_tac []))
  >- (`LENGTH funs - (n + 1) < LENGTH funs` by decide_tac >>
      `LENGTH funs - (n + 1) < LENGTH (REVERSE funs)` by metis_tac [LENGTH_REVERSE] >>
      srw_tac [ARITH_ss] [EL_MAP, EL_REVERSE] >>
      `PRE (n + 1) = n` by decide_tac >>
      full_simp_tac(srw_ss())[] >>
      `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
      srw_tac[][] >>
      simp [nsAppend_to_nsBindList] >>
      simp [namespaceTheory.nsBindList_def, MAP_REVERSE]));
      (*
val compile_dec_num_bindings = Q.prove(
  `!next mn mods tops d next' tops' d_i1.
    compile_dec next mn mods tops d = (next',tops',d_i1)
    ⇒
    next' = next + dec_to_dummy_env d_i1`,
  srw_tac[][compile_dec_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM] >>
  srw_tac[][dec_to_dummy_env_def, compile_funs_map] >>
  metis_tac []);

val compile_decs_num_bindings = Q.prove(
  `!next mn mods tops ds next' tops' ds_i1.
    compile_decs next mn mods tops ds = (next',tops',ds_i1)
    ⇒
    next' = next + decs_to_dummy_env ds_i1`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def] >>
  srw_tac[][decs_to_dummy_env_def] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  first_assum(split_uncurry_arg_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[fupdate_list_foldl] >>
  srw_tac[][decs_to_dummy_env_def] >>
  res_tac >>
  srw_tac[][] >>
  imp_res_tac compile_dec_num_bindings >>
  srw_tac[][] >>
  decide_tac);
  *)

val global_env_inv_append = Q.prove (
  `!genv var_map1 var_map2 env1 env2.
    nsDomMod var_map1 = nsDomMod env1 ∧
    nsDom var_map1 = nsDom env1 ∧
    global_env_inv genv var_map1 {} env1 ∧
    global_env_inv genv var_map2 {} env2
    ⇒
    global_env_inv genv (nsAppend var_map1 var_map2) {} (nsAppend env1 env2)`,
  rw [v_rel_eqns, nsLookup_nsAppend_some] >>
  first_x_assum drule >>
  rw []
  >- (
    qexists_tac `n` >>
    qexists_tac `v'` >>
    rw [])
  >- (
    qexists_tac `n` >>
    qexists_tac `v'` >>
    qexists_tac `t` >>
    rw [] >>
    disj2_tac >>
    rw []
    >- (
      fs [EXTENSION, namespaceTheory.nsDom_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy])
    >- (
      fs [EXTENSION, namespaceTheory.nsDomMod_def, GSPECIFICATION, UNCURRY, LAMBDA_PROD, EXISTS_PROD] >>
      metis_tac [NOT_SOME_NONE, option_nchotomy])));

val pmatch_lem =
  pmatch
  |> CONJUNCTS
  |> hd
  |> SIMP_RULE (srw_ss()) [];

val ALOOKUP_alloc_defs = Q.prove (
  `!env x v genv tt.
    ALOOKUP (REVERSE env) x = SOME v
    ⇒
    ∃n t.
      ALOOKUP (alloc_defs tt (LENGTH genv) (MAP FST (REVERSE env))) x = SOME (Var_global t n) ∧
      n < LENGTH (MAP FST env) + LENGTH genv ∧
      EL n (genv ++ REVERSE (MAP SOME (MAP SND env))) = SOME v`,
  Induct_on `env` >>
  rw [ALOOKUP_APPEND, alloc_defs_append] >>
  every_case_tac >>
  fs [alloc_defs_def]
  >- (
    PairCases_on `h` >>
    fs [EL_APPEND_EQN])
  >- (
    PairCases_on `h` >>
    fs [] >>
    first_x_assum drule >>
    disch_then (qspecl_then [`genv`,`tt`] mp_tac) >>
    rw [])
  >- (
    PairCases_on `h` >>
    fs [] >>
    rw [] >>
    fs [ALOOKUP_NONE, MAP_REVERSE] >>
    drule ALOOKUP_MEM >>
    rw [] >>
    `MEM h0 (MAP FST (alloc_defs tt (LENGTH genv) (REVERSE (MAP FST env))))`
      by (rw [MEM_MAP] >> metis_tac [FST]) >>
    fs [fst_alloc_defs])
  >- (
    first_x_assum drule >>
    disch_then (qspecl_then [`genv`,`tt`] mp_tac) >>
    rw [EL_APPEND_EQN]));

val make_varls_trace_exists = Q.prove(`
  ∀ls n t.
  ∃tt.
  LENGTH tt = LENGTH ls ∧
  make_varls n t ls = bind_locals_list tt ls`,
  Induct>>fs[bind_locals_list_def,make_varls_def]>>rw[]>>
  pop_assum(qspecl_then[`n+1`,`t`] strip_assume_tac)>>fs[]>>
  qexists_tac`(t ▷ n) :: tt`>>fs[]);

val reverse_bind_locals_list = Q.prove(`
  ∀ls tt.
  LENGTH ls = LENGTH tt ⇒
  REVERSE (bind_locals_list tt (REVERSE ls)) =
  bind_locals_list (REVERSE tt) ls`,
  simp[bind_locals_list_def,MAP2_MAP,GSYM MAP_REVERSE,REVERSE_ZIP]);

fun spectv v tt = disch_then(qspec_then tt mp_tac o CONV_RULE (RESORT_FORALL_CONV(sort_vars[v])))
val spect = spectv "t"

val compile_decs_correct = Q.prove (
  `!mn s env ds var_map s' r s_i1 next' var_map' ds_i1 t t'.
    evaluate$evaluate_decs mn s env ds = (s',r) ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    global_env_inv s_i1.globals var_map {} env.v ∧
    s_rel s s_i1 ∧
    source_to_mod$compile_decs t (LENGTH s_i1.globals) mn var_map ds = (t',next', var_map', ds_i1)
    ⇒
    ?(s'_i1:'a modSem$state) cenv' env'_i1 r_i1.
      modSem$evaluate_decs <| c := env.c; v := [] |> s_i1 ds_i1 = (s'_i1,cenv',MAP SND env'_i1,r_i1) ∧
      (!env'.
        r = Rval env'
        ⇒
        r_i1 = NONE ∧
        cenv' = env'.c ∧
        next' = LENGTH (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) ∧
        env_rel (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) env'.v (REVERSE env'_i1) ∧
        s_rel s' s'_i1 ∧
        nsDom env'.v = nsDom var_map' ∧
        nsDomMod env'.v = nsDomMod var_map' ∧
        global_env_inv (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) var_map' {} env'.v) ∧
      (!err.
        r = Rerr err
        ⇒
        ?err_i1.
          r_i1 = SOME err_i1 ∧
          result_rel (\a b (c:'a). T) (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) (Rerr err) (Rerr err_i1) ∧
          s_rel s' s'_i1)`,
  ho_match_mp_tac evaluateTheory.evaluate_decs_ind >>
  simp [evaluateTheory.evaluate_decs_def] >>
  conj_tac
  >- ntac 2 (rw [compile_dec_def, compile_decs_def, evaluate_decs_def, v_rel_eqns]) >>
  conj_tac
  >- (
    rpt gen_tac >>
    qspec_tac (`d2::ds`, `ds`) >>
    rw [compile_decs_def]  >>
    ntac 2 (pairarg_tac \\ fs[])
    \\ rveq
    \\ simp[evaluate_decs_def]
    \\ qpat_x_assum`_ = (_,r)`mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ reverse BasicProvers.TOP_CASE_TAC \\ fs[]
    >- (
      rw[]
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ rfs[] \\ first_x_assum drule
      \\ disch_then drule
      \\ spect `t`
      \\ simp[]
      \\ simp[evaluate_decs_def,PULL_EXISTS]
      \\ rpt gen_tac
      \\ BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ TRY BasicProvers.TOP_CASE_TAC \\ fs[]
      \\ rw[] \\ fs[])
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rw[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ rfs[] \\ first_x_assum drule
    \\ disch_then drule
    \\ spect`t`
    \\ simp[]
    \\ simp[evaluate_decs_def,PULL_EXISTS]
    \\ rpt gen_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ rveq \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ qmatch_asmsub_rename_tac`res ≠ Rerr (Rabort Rtype_error)`
    \\ qmatch_asmsub_rename_tac `_ _ _ (ds) = (new_s, new_env, _)`
    \\ qmatch_asmsub_rename_tac `_ _ _ (ds') = (new_s', new_cenv', new_env', res')`
    \\ Cases_on`res = Rerr (Rabort Rtype_error)`
    >- fs[combine_dec_result_def]
    \\ fs []
    \\ fs [extend_dec_env_def]
    \\ imp_res_tac evaluate_dec_globals \\ fs[]
    \\ first_x_assum(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(
         move_conj_left(equal "s_rel" o #1 o dest_const o #1 o strip_comb)))))
    \\ spect`n'`
    \\ simp[]
    \\ disch_then(drule o CONV_RULE(STRIP_QUANT_CONV(LAND_CONV(
         move_conj_left(equal "compile_decs" o #1 o dest_const o #1 o strip_comb o lhs)))))
    >>
    impl_tac
    >- (
      irule global_env_inv_append >>
      rw []
      >- metis_tac [v_rel_weakening]) >>
    strip_tac \\ rveq \\ fs[] >>
    rw []
    \\ full_simp_tac std_ss [GSYM MAP_APPEND]
    \\ qmatch_goalsub_abbrev_tac`MAP SND www`
    \\ qexists_tac`www` \\ fs[Abbr`www`]
    \\ reverse (Cases_on`res`) \\ fs[combine_dec_result_def]
    \\ conj_tac
    >- (
      simp[REVERSE_APPEND]
      \\ match_mp_tac env_rel_append
      \\ simp[]
      \\ metis_tac[v_rel_weakening] ) >>
    ONCE_REWRITE_TAC [CONJ_ASSOC] >>
    conj_tac
    >- (
      irule nsDom_nsAppend_equal >>
      rw []) >>
    irule global_env_inv_append >>
    rw [] >>
    metis_tac[v_rel_weakening]) >>
  rw [compile_dec_def, compile_decs_def]
  >- (
    split_pair_case_tac >>
    fs [] >>
    qmatch_assum_rename_tac `evaluate _ _ _ = (st', res)` >>
    drule compile_exp_correct >>
    disch_then drule >>
    Cases_on `res` >>
    rfs [] >>
    rveq >>
    fs [] >>
    disch_then drule >>
    spect`(om_tra ▷ t)`>>
    rw [modSemTheory.evaluate_decs_def, modSemTheory.evaluate_dec_def, modSemTheory.evaluate_def,
        compile_exp_def, result_rel_cases] >>
    rw [] >>
    qmatch_assum_rename_tac `evaluate _ _ [e] = (st', Rval answer')` >>
    `?answer. answer' = [answer]`
      by (
        imp_res_tac evaluate_sing >>
        fs []) >>
    fs [] >>
    imp_res_tac evaluate_globals >>
    rpt var_eq_tac >>
    qmatch_assum_rename_tac `evaluate _ _ [compile_exp _ var_map e] = (st1', Rval [answer1])` >>
    `match_result_rel st1'.globals [] (pmatch env.c st'.refs p answer ([]++[]))
           (pmatch env.c st1'.refs (compile_pat p) answer1 [])`
      by (
        match_mp_tac pmatch_lem >>
        simp [] >>
        fs [s_rel_cases] >>
        rw [v_rel_eqns]) >>
    Cases_on `pmatch env.c st'.refs p answer []` >>
    Cases_on `pmatch env.c st1'.refs (compile_pat p) answer1 []` >>
    fs [match_result_rel_def,  Bindv_def]
    >- rw [v_rel_eqns] >>
    simp [do_con_check_def] >>
    qmatch_assum_rename_tac `_ = Match bind_i1` >>
    qmatch_goalsub_abbrev_tac`make_varls A B C`>>
    qspecl_then [`C`,`A`,`B`] strip_assume_tac make_varls_trace_exists>>
    unabbrev_all_tac>> simp[]>>
    drule pmatch_evaluate_vars_lem >>
    fs[LENGTH_REVERSE]>>
    disch_then (qspec_then`REVERSE tt` mp_tac)>>simp[]>>
    simp[reverse_bind_locals_list]>>
    simp [pat_bindings_compile_pat, MAP_REVERSE] >>
    simp [build_conv_def] >>
    drule pmatch_length >>
    rw [] >>
    qexists_tac `REVERSE bind_i1` >>
    simp [MAP_REVERSE] >>
    conj_tac >- metis_tac [v_rel_weakening] >>
    conj_tac
    >- (
      fs [s_rel_cases]
      >- metis_tac [sv_rel_weakening, LIST_REL_mono]) >>
    conj_tac
    >- (
      simp [GSYM MAP_MAP_o, fst_alloc_defs] >>
      drule (CONJUNCT1 pmatch_extend) >>
      rw [] >>
      drule env_rel_dom >>
      rw [MAP_REVERSE]) >>
    drule env_rel_dom >>
    rw [] >>
    simp [v_rel_eqns] >>
    rw [nsLookup_alist_to_ns_some] >>
    drule env_rel_lookup >>
    disch_then drule >>
    rw [] >>
    `pat_bindings p [] = MAP FST bind_i1`
      by metis_tac [pmatch_bindings, pat_bindings_compile_pat, APPEND_NIL, MAP] >>
    full_simp_tac std_ss [] >>
    `ALOOKUP (REVERSE bind_i1) x' = SOME v'` by metis_tac [alookup_distinct_reverse] >>
    drule ALOOKUP_alloc_defs >>
    metis_tac [MAP_REVERSE, v_rel_weakening])
  >- (
    simp [evaluate_decs_def, evaluate_dec_def] >>
    qmatch_goalsub_abbrev_tac `compile_funs tra var_map' (REVERSE funs)` >>
    qexists_tac `MAP (λ(f,x,e). (f, Closure (env.c,[]) x e)) (compile_funs tra var_map' (REVERSE funs))` >>
    simp [compile_funs_map,UNCURRY,fst_alloc_defs,
          semanticPrimitivesPropsTheory.build_rec_env_merge,MAP_REVERSE,ETA_AX] >>
    conj_tac
    >- simp [MAP_MAP_o, combinTheory.o_DEF, UNCURRY] >>
    conj_tac
    >- (
      simp [env_rel_el,EL_MAP,UNCURRY] >>
      rw [] >>
      simp [Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`var_map`, `SND(SND(EL n funs))`,
                             `alloc_defs t (LENGTH s_i1.globals) (MAP FST (REVERSE funs))`,
                             `tra`,`tra`] >>
      srw_tac[][] >>
      UNABBREV_ALL_TAC >>
      srw_tac[][SUBSET_DEF]
      >- (
        simp [nsAppend_to_nsBindList] >>
        simp [namespaceTheory.nsBindList_def, MAP_REVERSE])
      >- srw_tac[][MAP_REVERSE, fst_alloc_defs, FST_triple]
      >- metis_tac [v_rel_weakening]
      >- metis_tac [find_recfun_el,SND,PAIR] >>
      simp [MAP_MAP_o, combinTheory.o_DEF, UNCURRY, LAMBDA_PROD, GSYM MAP_REVERSE] >>
      drule letrec_global_env_lem3 >>
      disch_then drule>>
      disch_then (qspecl_then [`s_i1.globals`,`env.c`,`var_map`,`t`,`om_tra ▷ t + 1`] strip_assume_tac)>>
      simp[]>>
      metis_tac[])>>
    conj_tac
    >- (
      fs [s_rel_cases]
      >- metis_tac [sv_rel_weakening, LIST_REL_mono]) >>
    conj_tac
    >- (
      simp_tac std_ss [GSYM MAP_MAP_o, fst_alloc_defs] >>
      simp [MAP_MAP_o, MAP_REVERSE, combinTheory.o_DEF, LAMBDA_PROD]) >>
    simp [v_rel_eqns] >>
    rw [nsLookup_alist_to_ns_some] >>
    simp [MAP_MAP_o, combinTheory.o_DEF, UNCURRY, LAMBDA_PROD, GSYM MAP_REVERSE] >>
    imp_res_tac ALOOKUP_MEM >>
    fs [] >>
    drule letrec_global_env_lem3 >>
    `MEM x' (MAP FST funs)`
      by (
        fs [MEM_MAP] >>
        PairCases_on `y` >>
        fs [EXISTS_PROD] >>
        metis_tac []) >>
    disch_then drule >>
    disch_then (qspecl_then [`s_i1.globals`, `env.c`, `var_map`,`t`,`tra`] mp_tac) >>
    rw [Abbr `var_map'`, MAP_REVERSE] >>
    rw [] >>
    simp [Once v_rel_cases] >>
    disj2_tac >>
    qexists_tac `var_map` >>
    qexists_tac `env` >>
    qexists_tac `funs` >>
    qexists_tac `x'` >>
    qexists_tac `e'` >>
    qexists_tac `alloc_defs t (LENGTH s_i1.globals) (REVERSE (MAP FST funs))` >>
    qexists_tac `t2` >>
    qexists_tac `t3`>>
    rw [fst_alloc_defs, MAP_REVERSE]
    >- (
      fs [MEM_MAP] >>
      PairCases_on `y'` >>
      fs [])
    >- metis_tac [v_rel_weakening] >>
    drule letrec_global_env_lem3 >>
    disch_then drule >>
    disch_then (qspecl_then [`s_i1.globals`, `env.c`, `var_map`,`t`,`tra`] mp_tac) >>
    rw [MAP_REVERSE])
  >- (
    simp [evaluate_decs_def, evaluate_dec_def, fupdate_list_foldl] >>
    rw []
    >- fs [v_rel_eqns]
    >- fs [s_rel_cases]
    >- fs [v_rel_eqns]
    >- rfs [s_rel_cases])
  >- (
    simp [evaluate_decs_def, evaluate_dec_def, PULL_EXISTS, type_defs_to_new_tdecs_def, build_tdefs_def,
          check_dup_ctors_def] >>
    fs [s_rel_cases, v_rel_eqns])
  >- (
    rw [evaluate_decs_def, evaluate_dec_def]
    >- (rfs [s_rel_cases] >> fs [])
    >- fs [v_rel_eqns]
    >- (fs [s_rel_cases] >> simp [EXTENSION])
    >- simp [v_rel_eqns]));

    (*
val global_env_inv_extend_mod = Q.prove (
  `!genv new_genv mods tops tops' menv new_env env mn.
    global_env_inv genv mods tops menv ∅ env ∧
    global_env_inv (genv ++ MAP SOME (MAP SND new_genv)) FEMPTY (FEMPTY |++ tops') [] ∅ new_env
    ⇒
    global_env_inv (genv ++ MAP SOME (MAP SND new_genv)) (mods |+ (mn,FEMPTY |++ tops')) tops ((mn,new_env)::menv) ∅ env`,
  srw_tac[][last (CONJUNCTS v_rel_eqns)]
  >- metis_tac [v_rel_weakening] >>
  every_case_tac >>
  srw_tac[][FLOOKUP_UPDATE] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  res_tac >>
  qexists_tac `map'` >>
  srw_tac[][] >>
  res_tac  >>
  qexists_tac `n` >>
  qexists_tac `v_i1` >>
  srw_tac[][]
  >- decide_tac >>
  metis_tac [v_rel_weakening, EL_APPEND1]);

val global_env_inv_extend_mod_err = Q.prove (
  `!genv new_genv mods tops tops' menv new_env env mn new_genv'.
    mn ∉ set (MAP FST menv) ∧
    global_env_inv genv mods tops menv ∅ env
    ⇒
    global_env_inv (genv ++ MAP SOME (MAP SND new_genv) ++ new_genv')
                   (mods |+ (mn,FEMPTY |++ tops')) tops menv ∅ env`,
  srw_tac[][last (CONJUNCTS v_rel_eqns)]
  >- metis_tac [v_rel_weakening] >>
  srw_tac[][FLOOKUP_UPDATE]
  >- metis_tac [ALOOKUP_MEM, MEM_MAP, pair_CASES, FST] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  srw_tac[][] >>
  res_tac >>
  srw_tac[][] >>
  res_tac  >>
  qexists_tac `n` >>
  qexists_tac `v_i1` >>
  srw_tac[][]
  >- decide_tac >>
  metis_tac [v_rel_weakening, EL_APPEND1, APPEND_ASSOC]);

  *)

val prompt_mods_ok_dec = Q.prove (
  `!l mn var_map d l' var_map' d_i1 t t'.
    compile_dec t l [] var_map d = (t',l',var_map',d_i1)
    ⇒
    prompt_mods_ok NONE [d_i1]`,
  srw_tac[][LET_THM, prompt_mods_ok_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[compile_dec_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM]);

val prompt_mods_ok = Q.prove (
  `!l mn var_map ds l' var_map' ds_i1 t t'.
    compile_decs t l [mn] var_map ds = (t',l',var_map',ds_i1)
    ⇒
    prompt_mods_ok (SOME mn) ds_i1`,
  induct_on `ds` >>
  srw_tac[][LET_THM, compile_decs_def, prompt_mods_ok_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[prompt_mods_ok_def] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  srw_tac[][]
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[compile_dec_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LET_THM])
  >- metis_tac []);

val no_dup_types_helper = Q.prove (
  `!next mn  env ds next' env' ds_i1 t t'.
    compile_decs t next mn env ds = (t',next',env',ds_i1) ⇒
    FLAT (MAP (\d. case d of Dtype _ tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds)
    =
    FLAT (MAP (\d. case d of Dtype mn tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds_i1)`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def] >>
  srw_tac[][] >>
  fs [LET_THM] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[compile_dec_def, LET_THM] >>
  srw_tac[][] >>
  metis_tac []);

val no_dup_types = Q.prove(
  `!next mn env ds next' env' ds_i1 t t'.
    compile_decs t next mn env ds = (t',next',env',ds_i1) ∧
    no_dup_types ds
    ⇒
    no_dup_types ds_i1`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def]
  >- full_simp_tac(srw_ss())[semanticPrimitivesTheory.no_dup_types_def, modSemTheory.no_dup_types_def, modSemTheory.decs_to_types_def] >>
  fs [LET_THM] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  srw_tac[][] >>
  res_tac >>
  cases_on `h` >>
  full_simp_tac(srw_ss())[compile_dec_def, LET_THM] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.decs_to_types_def, semanticPrimitivesTheory.no_dup_types_def,
      modSemTheory.decs_to_types_def, modSemTheory.no_dup_types_def, ALL_DISTINCT_APPEND] >>
  srw_tac[][] >>
  metis_tac [no_dup_types_helper]);

val no_dup_types_dec = Q.prove (
  `!next mn env d next' env' d_i1 t t'.
    compile_dec t next mn env d = (t',next',env',d_i1) ∧
    no_dup_types [d]
    ⇒
    no_dup_types [d_i1]`,
  rw [] >>
  irule no_dup_types >>
  qexists_tac `[d]` >>
  rw [compile_decs_def] >>
  qexists_tac `env` >>
  qexists_tac `env'` >>
  qexists_tac `mn` >>
  qexists_tac `next` >>
  qexists_tac `next'` >>
  qexists_tac `t` >>
  simp []);

val compile_decs_dec = Q.prove(
  `compile_dec t next mn env d = (t',x,y,z) ⇒
   compile_decs t next mn env [d] = (t',x,y,[z])`,
  rw[compile_decs_def]);

val compile_top_decs = Q.store_thm("compile_top_decs",
  `compile_top t n env top =
   let (mno,ds) = case top of Tmod mn _ ds => (SOME mn,ds) | Tdec d => (NONE,[d]) in
   let (t',next,new_env,ds) = compile_decs t n (option_fold CONS [] mno) env ds in
   let env = case top of Tmod mn _ _ => nsAppend (nsLift mn new_env) env | _ => nsAppend new_env env in
   (t',next,env,Prompt mno ds)`,
  rw[compile_top_def]
  \\ every_case_tac \\ fs[option_fold_def]
  \\ pairarg_tac \\ fs[]
  \\ fs[Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST |> SIMP_RULE(srw_ss())[LAMBDA_PROD]]
  \\ fs[Q.ISPEC`I:α#β -> α#β`LAMBDA_PROD |> GSYM |> SIMP_RULE (srw_ss())[]]
  \\ imp_res_tac compile_decs_dec \\ fs[]);

val global_env_inv_lift = Q.prove (
  `!mn var_map env.
    global_env_inv genv var_map {} env
    ⇒
    global_env_inv genv (nsLift mn var_map) {} (nsLift mn env)`,
  rw [v_rel_eqns, nsLookup_nsLift] >>
  every_case_tac >>
  fs []);

val invariant_def = Define `
  invariant var_map env s s_i1 ⇔
    global_env_inv s_i1.globals var_map {} env ∧
    s_rel s s_i1 ∧
    (!x. x ∈ s.defined_mods ⇒ LENGTH x = 1)`;

val invariant_change_clock = Q.store_thm("invariant_change_clock",
  `invariant menv env st1 st2 ⇒
   invariant menv env (st1 with clock := k) (st2 with clock := k)`,
  srw_tac[][invariant_def] >> full_simp_tac(srw_ss())[s_rel_cases])

val invariant_defined_mods = Q.prove(
  `invariant c d e f ⇒ f.defined_mods = IMAGE HD e.defined_mods`,
  rw[invariant_def,s_rel_cases]);

val invariant_defined_types = Q.prove(
  `invariant c d e f ⇒ e.defined_types = f.defined_types`,
  rw[invariant_def,s_rel_cases]);

val compile_prog_correct = Q.store_thm ("compile_prog_correct",
  `!s env prog var_map  s' r s_i1 next' var_map' prog_i1 t.
    evaluate$evaluate_tops s env prog = (s',r) ∧
    invariant var_map env.v s s_i1 ∧
    r ≠ Rerr (Rabort Rtype_error) ∧
    source_to_mod$compile_prog t (LENGTH s_i1.globals) var_map prog = (next',var_map',prog_i1)
    ⇒
    ∃(s'_i1:'a modSem$state) new_genv cenv' r_i1.
     modSem$evaluate_prompts <|c := env.c; v := []|> s_i1 prog_i1 =
       (s'_i1,cenv',new_genv,r_i1) ∧
     (!new_env.
       r = Rval new_env
       ⇒
       next' = LENGTH (s_i1.globals ++ new_genv) ∧
       r_i1 = NONE ∧
       cenv' = new_env.c ∧
       invariant var_map' (nsAppend new_env.v env.v) s' s'_i1) ∧
     (!err.
       r = Rerr err
       ⇒
       ?err_i1.
         r_i1 = SOME err_i1 ∧ s_rel s' s'_i1 ∧
         result_rel (\a b (c:'a). T) (s_i1.globals ++ new_genv) r (Rerr err_i1))`,
  ho_match_mp_tac evaluateTheory.evaluate_tops_ind >>
  conj_tac
  (* Empty prog *)
  >- rw [compile_prog_def, evaluate_prompts_def] >>
  conj_tac
  (* Cons case *)
  >- (
    rpt gen_tac >>
    qspec_tac (`top2::tops`, `tops`) >>
    rw [] >>
    qpat_x_assum `evaluate_tops _ _ (_::_) = _` mp_tac >>
    simp [Once evaluatePropsTheory.evaluate_tops_cons] >>
    fs [compile_prog_def] >>
    pairarg_tac >>
    fs [] >>
    pairarg_tac >>
    fs [] >>
    rveq >>
    split_pair_case_tac >>
    fs [] >>
    reverse CASE_TAC
    (* Error case *)
    >- (
      rw [] >>
      pop_assum drule>> simp[]>>
      spectv "t'"`t`>>simp[]>>
      rw [] >>
      qpat_x_assum `evaluate_prompts _ _ [_] = _` mp_tac >>
      simp [evaluate_prompts_def] >>
      split_pair_case_tac >>
      simp [] >>
      CASE_TAC >>
      rw []) >>
    rfs [] >>
    first_x_assum drule >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rveq >>
    fs [extend_dec_env_def] >>
    qpat_x_assum`!x. P x` mp_tac>>
    spectv "t'" `t`>>simp[]>> strip_tac>>
    qpat_x_assum `evaluate_prompts _ _ [_] = _` mp_tac >>
    simp [evaluate_prompts_def] >>
    split_pair_case_tac >>
    simp [] >>
    CASE_TAC >>
    rw [] >>
    first_x_assum drule >>
    spect `n'`>>
    simp [] >>
    qmatch_assum_rename_tac `combine_dec_result _ final_res ≠ _` >>
    `final_res ≠ Rerr (Rabort Rtype_error)`
      by (
        Cases_on `final_res` >>
        fs [combine_dec_result_def]) >>
    rw [] >>
    Cases_on `final_res` >>
    fs [combine_dec_result_def] >>
    fs [result_rel_cases]) >>
  conj_tac
  (* Declarations case *)
  >- (
    rw [compile_prog_def, evaluateTheory.evaluate_tops_def] >>
    pairarg_tac >>
    fs [compile_top_def] >>
    pairarg_tac >>
    fs [compile_decs_def] >>
    rw [] >>
    drule compile_decs_correct >>
    fs [invariant_def] >>
    disch_then drule >>
    spectv "t'" `t`>>
    simp [compile_decs_def, evaluate_prompts_def, evaluate_prompt_def] >>
    strip_tac >>
    drule prompt_mods_ok_dec >>
    drule no_dup_types_dec >>
    impl_tac
    >- (
      Cases_on `d` >>
      fs [evaluate_decs_def, semanticPrimitivesTheory.no_dup_types_def,
          semanticPrimitivesTheory.decs_to_types_def] >>
      fs [evaluateTheory.evaluate_decs_def] >>
      every_case_tac >>
      fs []) >>
    simp [] >>
    rename1 `evaluate_decs [] _ _ [_] = (s', final_result)` >>
    Cases_on `final_result` >>
    fs []
    >- (
      rw [option_fold_def]
      >- (
        irule global_env_inv_append >>
        rw [] >>
        metis_tac [v_rel_weakening])
      >- (
        fs [s_rel_cases, update_mod_state_def] >>
        drule evaluate_decs_globals >>
        rw [] >>
        fs [])
      >- (
        drule evaluatePropsTheory.evaluate_decs_state_unchanged >>
        simp [] >>
        metis_tac []))
    >- (
      fs [s_rel_cases, update_mod_state_def, result_rel_cases] >>
      metis_tac [v_rel_weakening]))
  (* Module case *)
  >- (
    rw [compile_prog_def, evaluateTheory.evaluate_tops_def] >>
    pairarg_tac >>
    fs [compile_top_def] >>
    pairarg_tac >>
    fs [] >>
    rw [] >>
    split_pair_case_tac >>
    fs [] >>
    rename1 `evaluate_decs [_] _ _ _ = (st1, result)` >>
    `result ≠ Rerr (Rabort Rtype_error)`
      by (
        every_case_tac >> rw []) >>
    drule compile_decs_correct >>
    fs [invariant_def] >>
    disch_then drule >>
    spectv "t'" `t`>>
    simp [evaluate_prompts_def, evaluate_prompt_def] >>
    strip_tac >>
    drule prompt_mods_ok >>
    drule no_dup_types >>
    `mn ∉ s_i1.defined_mods`
    by (
      fs [s_rel_cases] >>
      rw [] >>
      Cases_on `x` >>
      fs [] >>
      CCONTR_TAC >>
      fs [] >>
      res_tac >>
      fs [LENGTH_EQ_NUM]) >>
    simp [] >>
    Cases_on `result` >>
    fs [] >>
    rw [] >>
    rw []
    >- simp [option_fold_def]
    >- (
      irule global_env_inv_append >>
      rw [nsDom_nsLift, nsDomMod_nsLift]
      >- metis_tac [global_env_inv_lift]
      >- metis_tac [v_rel_weakening])
    >- (
      fs [s_rel_cases, update_mod_state_def] >>
      drule evaluate_decs_globals >>
      rw [] >>
      fs [GSYM INSERT_SING_UNION])
    >- metis_tac [evaluatePropsTheory.evaluate_decs_state_unchanged]
    >- fs [s_rel_cases, update_mod_state_def, GSYM INSERT_SING_UNION]
    >- (
      fs [s_rel_cases, update_mod_state_def, result_rel_cases] >>
      metis_tac [v_rel_weakening])));

val compile_prog_mods = Q.prove (
  `!l var_map prog l' prog_i1 n.
    source_to_mod$compile_prog n l var_map prog = (l',var_map',prog_i1)
    ⇒
    EVERY (\mn. LENGTH mn = 1) (prog_to_mods prog) ∧
    modSem$prog_to_mods prog_i1 = MAP HD (semanticPrimitives$prog_to_mods prog)`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM, modSemTheory.prog_to_mods_def, semanticPrimitivesTheory.prog_to_mods_def] >>
  srw_tac[][modSemTheory.prog_to_mods_def] >>
  srw_tac[][] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [compile_top_def] >>
  every_case_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  pairarg_tac >>
  fs [] >>
  first_x_assum drule >>
  rw [] >>
  fs [semanticPrimitivesTheory.prog_to_mods_def, modSemTheory.prog_to_mods_def]);

val inj_hd_sing = Q.prove (
  `EVERY (\mn. LENGTH mn = 1) l
   ⇒
   !x y. MEM x l ∧ MEM y l ∧ HD x = HD y ⇒ x = y`,
  induct_on `l` >>
  rw [] >>
  fs [EVERY_MEM] >>
  res_tac >>
  fs [] >>
  `!lst. LENGTH lst = 1 ⇔ ?x. lst = [x]`
  by (rw [] >> Cases_on `lst` >> rw [LENGTH_NIL]) >>
  fs [] >>
  rw [] >>
  fs []);

val compile_prog_top_types = Q.prove (
  `!l var_map prog l' var_map' prog_i1 n.
    compile_prog n l var_map prog = (l',var_map',prog_i1)
    ⇒
    prog_to_top_types prog
    =
    prog_to_top_types prog_i1`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM] >>
  fs [semanticPrimitivesTheory.prog_to_top_types_def, modSemTheory.prog_to_top_types_def] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  fs [] >>
  fs [compile_top_def] >>
  pairarg_tac >>
  fs [] >>
  rw [] >>
  full_simp_tac(srw_ss())[compile_dec_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[LET_THM] >>
  srw_tac[][semanticPrimitivesTheory.decs_to_types_def, modSemTheory.decs_to_types_def]);

val compile_prog_mods_ok = Q.prove (
  `!l var_map prog l' var_map' prog_i1 n.
    compile_prog n l var_map prog = (l',var_map',prog_i1)
    ⇒
    EVERY (λp. case p of Prompt mn ds => prompt_mods_ok mn ds) prog_i1`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM] >>
  srw_tac[][] >>
  pairarg_tac >>
  fs [] >>
  pairarg_tac >>
  fs [] >>
  first_x_assum drule >>
  rw [] >>
  every_case_tac >>
  fs [compile_top_def] >>
  every_case_tac >>
  pairarg_tac >>
  fs [] >>
  rw [] >>
  metis_tac [prompt_mods_ok_dec, prompt_mods_ok]);

val whole_compile_prog_correct = Q.store_thm ("whole_compile_prog_correct",
  `evaluate_prog s env prog = (s',r) ∧
   invariant var_map env.v s s_i1 ∧
   compile_prog n (LENGTH s_i1.globals) var_map prog = (next',var_map',prog_i1) ∧
   r ≠ Rerr (Rabort Rtype_error)
   ⇒
    ∃(s'_i1:'a modSem$state) r_i1.
     evaluate_prog <| c := env.c; v := [] |> s_i1 prog_i1 = (s'_i1,r_i1) ∧
     s_rel s' s'_i1 ∧
     (∀v. r = Rval v ⇒ r_i1 = NONE) ∧
     (∀err. r = Rerr err ⇒ ∃err_i1. r_i1 = SOME err_i1 ∧
       ∃new_genv.
         result_rel (\a b (c:'a). T) (s_i1.globals ++ new_genv) r (Rerr err_i1))`,
  rw [modSemTheory.evaluate_prog_def, evaluateTheory.evaluate_prog_def]
  \\ imp_res_tac compile_prog_mods
  \\ imp_res_tac compile_prog_top_types
  \\ imp_res_tac compile_prog_mods_ok
  \\ imp_res_tac invariant_defined_mods
  \\ imp_res_tac invariant_defined_types
  \\ fs[semanticPrimitivesTheory.no_dup_mods_def,modSemTheory.no_dup_mods_def,
        semanticPrimitivesTheory.no_dup_top_types_def,modSemTheory.no_dup_top_types_def]
  >- (
    fs[EVERY_MEM,EXISTS_MEM]
    \\ res_tac
    \\ drule compile_prog_correct
    \\ disch_then drule
    \\ spect`n`
    \\ rw[] \\ fs[LIST_TO_SET_MAP]
    \\ TRY (Cases_on`r`\\fs[invariant_def])
    \\ rw []
    \\ metis_tac[PAIR, ALL_DISTINCT_MAP, typeSoundTheory.disjoint_image])
  >- metis_tac [ALL_DISTINCT_MAP_INJ, inj_hd_sing]
  >- (
    fs [DISJOINT_DEF, EXTENSION, MEM_MAP] >>
    rw [] >>
    `LENGTH x' = 1` by metis_tac [invariant_def] >>
    `LENGTH y = 1` by fs [EVERY_MEM] >>
    Cases_on `x'` >>
    Cases_on `y` >>
    fs [LENGTH_NIL] >>
    metis_tac [])
  >- (
    fs [EXISTS_MEM, EVERY_MEM] >>
    every_case_tac >>
    fs [] >>
    res_tac >>
    fs [])
  >- metis_tac [ALL_DISTINCT_MAP_INJ, inj_hd_sing]
  >- (
    fs [DISJOINT_DEF, EXTENSION, MEM_MAP] >>
    rw [] >>
    `LENGTH x' = 1` by metis_tac [invariant_def] >>
    `LENGTH y = 1` by fs [EVERY_MEM] >>
    Cases_on `x'` >>
    Cases_on `y` >>
    fs [LENGTH_NIL] >>
    metis_tac [])
  >- (
    fs [EXISTS_MEM, EVERY_MEM] >>
    every_case_tac >>
    fs [] >>
    res_tac >>
    fs [])
  >- metis_tac [ALL_DISTINCT_MAP_INJ, inj_hd_sing]
  >- (
    fs [DISJOINT_DEF, EXTENSION, MEM_MAP] >>
    rw [] >>
    `LENGTH x' = 1` by metis_tac [invariant_def] >>
    `LENGTH y = 1` by fs [EVERY_MEM] >>
    Cases_on `x'` >>
    Cases_on `y` >>
    fs [LENGTH_NIL] >>
    metis_tac [])
  >- (
    fs [EXISTS_MEM, EVERY_MEM] >>
    every_case_tac >>
    fs [] >>
    res_tac >>
    fs []));

open semanticsTheory

val precondition_def = Define`
  precondition s1 env1 conf s2 env2 ⇔
    invariant conf.mod_env env1.v s1 s2 ∧
    env2.c = env1.c ∧
    env2.v = [] ∧
    conf.next_global = LENGTH s2.globals`;

val SND_eq = Q.prove(
  `SND x = y ⇔ ∃a. x = (a,y)`,
  Cases_on`x`\\rw[]);

val compile_correct = Q.store_thm("compile_correct",
  `precondition s1 env1 c s2 env2 ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog (semantics env2 s2 (SND (compile c prog)))`,
  rw[semantics_prog_def,SND_eq,precondition_def,compile_def]
  \\ pairarg_tac \\ fs[]
  \\ simp[modSemTheory.semantics_def]
  \\ IF_CASES_TAC \\ fs[SND_eq]
  >- (
    fs[semantics_prog_def,SND_eq]
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ simp[]
    \\ (fn g => subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) (#2 g) g) \\ fs[]
    \\ spose_not_then strip_assume_tac \\ fs[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[] \\ rw[]
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ asm_exists_tac \\ fs[]
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ fs[]
    \\ Cases_on`r`\\fs[result_rel_cases] )
  \\ DEEP_INTRO_TAC some_intro \\ fs[]
  \\ conj_tac
  >- (
    rw[] \\ rw[semantics_prog_def]
    \\ fs[evaluate_prog_with_clock_def]
    \\ qexists_tac`k`
    \\ pairarg_tac \\ fs[]
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ impl_tac
    >- ( rpt(first_x_assum(qspec_then`k`mp_tac))\\fs[] )
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ strip_tac
    \\ fs[invariant_def,s_rel_cases]
    \\ rveq \\ fs[]
    \\ every_case_tac \\ fs[]
    \\ rw[]
    \\ strip_tac \\ fs[result_rel_cases] )
  \\ rw[]
  \\ simp[semantics_prog_def]
  \\ conj_tac
  >- (
    rw[]
    \\ fs[evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs[]
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ impl_tac
    >- ( rpt(first_x_assum(qspec_then`k`mp_tac))\\fs[] )
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ strip_tac
    \\ first_x_assum(qspec_then`k`mp_tac)
    \\ rveq \\ fs[]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ strip_tac \\ fs[]
    \\ rveq
    \\ fs[result_rel_cases]
    \\ fs[s_rel_cases]
    \\ last_x_assum(qspec_then`k`mp_tac)
    \\ simp[]
    \\ Cases_on`r`\\fs[]
    \\ Cases_on`a`\\fs[])
  \\ qmatch_abbrev_tac`lprefix_lub l1 (build_lprefix_lub l2)`
  \\ `l2 = l1`
  by (
    unabbrev_all_tac
    \\ AP_THM_TAC
    \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM]
    \\ fs[evaluate_prog_with_clock_def]
    \\ gen_tac
    \\ pairarg_tac \\ fs[]
    \\ AP_TERM_TAC
    \\ drule (GEN_ALL whole_compile_prog_correct)
    \\ spectv "n" `1`
    \\ imp_res_tac invariant_change_clock
    \\ first_x_assum(qspec_then`k`strip_assume_tac)
    \\ fs[]
    \\ disch_then drule \\ fs[]
    \\ impl_tac
    >- ( rpt(first_x_assum(qspec_then`k`mp_tac))\\fs[] )
    \\ qmatch_goalsub_abbrev_tac`modSem$evaluate_prog env2'`
    \\ `env2' = env2`
    by ( unabbrev_all_tac \\ rw[environment_component_equality])
    \\ rveq
    \\ strip_tac
    \\ fs[]
    \\ fs[s_rel_cases] )
  \\ fs[Abbr`l1`,Abbr`l2`]
  \\ match_mp_tac build_lprefix_lub_thm
  \\ Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF]
  \\ REWRITE_TAC[IMAGE_COMPOSE]
  \\ match_mp_tac prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def,PULL_EXISTS]
  \\ simp[evaluate_prog_with_clock_def]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ pairarg_tac \\ fs[]
  \\ pairarg_tac \\ fs[]
  \\ metis_tac[evaluatePropsTheory.evaluate_prog_ffi_mono_clock,
               evaluatePropsTheory.io_events_mono_def,
               LESS_EQ_CASES,FST]);

val _ = export_theory ();
