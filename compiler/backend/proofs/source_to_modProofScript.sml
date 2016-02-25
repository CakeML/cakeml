open preamble;
open semanticPrimitivesTheory evalPropsTheory;
open source_to_modTheory modLangTheory modSemTheory modPropsTheory;

val _ = new_theory "source_to_modProof";

(* value relation *)

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!genv lit.
    v_rel genv ((Litv lit):semanticPrimitives$v) ((Litv lit):modSem$v)) ∧
  (!genv cn vs vs'.
    vs_rel genv vs vs'
    ⇒
    v_rel genv (Conv cn vs) (Conv cn vs')) ∧
  (!genv mods tops env x e env' env_i1.
    env_rel genv env.v env_i1 ∧
    set (MAP FST env') DIFF set (MAP FST env.v) ⊆ FDOM tops ∧
    global_env_inv genv mods tops env.m (set (MAP FST env_i1)) env'
    ⇒
    v_rel genv (Closure (env with v := env.v ++ env') x e)
                 (Closure (env.c, env_i1) x (compile_exp mods (DRESTRICT tops (COMPL (set (MAP FST env_i1))) \\ x) e))) ∧
  (* For expression level let recs *)
  (!genv mods tops env funs x env' env_i1.
    env_rel genv env.v env_i1 ∧
    set (MAP FST env') DIFF set (MAP FST env.v) ⊆ FDOM tops ∧
    global_env_inv genv mods tops env.m (set (MAP FST env_i1)) env'
    ⇒
    v_rel genv (Recclosure (env with v := env.v ++ env') funs x)
                 (Recclosure (env.c,env_i1) (compile_funs mods (DRESTRICT tops (COMPL (set (MAP FST env_i1) ∪ set (MAP FST funs)))) funs) x)) ∧
  (* For top-level let recs *)
  (!genv mods tops env funs x y e tops'.
    set (MAP FST env.v) ⊆ FDOM tops ∧
    global_env_inv genv mods tops env.m {} env.v ∧
    MAP FST (REVERSE tops') = MAP FST funs ∧
    find_recfun x funs = SOME (y,e) ∧
    (* A syntactic way of relating the recursive function environment, rather
     * than saying that they build v_rel related environments, which looks to
     * require step-indexing *)
    (!x. x ∈ set (MAP FST funs) ⇒
         ?n y e.
           FLOOKUP (FEMPTY |++ tops') x = SOME n ∧
           n < LENGTH genv ∧
           find_recfun x funs = SOME (y,e) ∧
           EL n genv = SOME (Closure (env.c,[]) y (compile_exp mods ((tops |++ tops') \\ y) e)))
    ⇒
    v_rel genv (Recclosure env funs x)
                 (Closure (env.c,[]) y (compile_exp mods ((tops |++ tops') \\ y) e))) ∧
  (!genv loc.
    v_rel genv (Loc loc) (Loc loc)) ∧
  (!vs.
    vs_rel genv vs vs_i1
    ⇒
    v_rel genv (Vectorv vs) (Vectorv vs_i1)) ∧
  (!genv.
    vs_rel genv [] []) ∧
  (!genv v vs v' vs'.
    v_rel genv v v' ∧
    vs_rel genv vs vs'
    ⇒
    vs_rel genv (v::vs) (v'::vs')) ∧
  (!genv.
    env_rel genv [] []) ∧
  (!genv x v env env' v'.
    env_rel genv env env' ∧
    v_rel genv v v'
    ⇒
    env_rel genv ((x,v)::env) ((x,v')::env')) ∧
  (!genv map shadowers env.
    (!x v.
       x ∉ shadowers ∧
       ALOOKUP env x = SOME v
       ⇒
       ?n v_i1.
         FLOOKUP map x = SOME n ∧
         n < LENGTH genv ∧
         EL n genv = SOME v_i1 ∧
         v_rel genv v v_i1)
    ⇒
    global_env_inv_flat genv map shadowers env) ∧
  (!genv mods tops menv shadowers env.
    global_env_inv_flat genv tops shadowers env ∧
    (!mn env'.
      ALOOKUP menv mn = SOME env'
      ⇒
      ?map.
        FLOOKUP mods mn = SOME map ∧
        global_env_inv_flat genv map {} env')
    ⇒
    global_env_inv genv mods tops menv shadowers env)`;

val v_rel_eqns = Q.store_thm ("v_rel_eqns",
  `(!genv l v.
    v_rel genv (Litv l) v ⇔
      (v = Litv l)) ∧
   (!genv b v. v_rel genv (Boolv b) v ⇔ (v = Boolv b)) ∧
   (!genv cn vs v.
    v_rel genv (Conv cn vs) v ⇔
      ?vs'. vs_rel genv vs vs' ∧ (v = Conv cn vs')) ∧
   (!genv l v.
    v_rel genv (Loc l) v ⇔
      (v = Loc l)) ∧
   (!genv vs v.
    v_rel genv (Vectorv vs) v ⇔
      ?vs'. vs_rel genv vs vs' ∧ (v = Vectorv vs')) ∧
   (!genv vs.
    vs_rel genv [] vs ⇔
      (vs = [])) ∧
   (!genv v vs vs'.
    vs_rel genv (v::vs) vs' ⇔
      ?v' vs''. v_rel genv v v' ∧ vs_rel genv vs vs'' ∧ vs' = v'::vs'') ∧
   (!genv env'.
    env_rel genv [] env' ⇔
      env' = []) ∧
   (!genv x v env env'.
    env_rel genv ((x,v)::env) env' ⇔
      ?v' env''. v_rel genv v v' ∧ env_rel genv env env'' ∧ env' = ((x,v')::env'')) ∧
   (!genv map shadowers env.
    global_env_inv_flat genv map shadowers env ⇔
      (!x v.
        x ∉ shadowers ∧
        ALOOKUP env x = SOME v
        ⇒
        ?n v_i1.
          FLOOKUP map x = SOME n ∧
          n < LENGTH genv ∧
          EL n genv = SOME v_i1 ∧
          v_rel genv v v_i1)) ∧
  (!genv mods tops menv shadowers env.
    global_env_inv genv mods tops menv shadowers env ⇔
      global_env_inv_flat genv tops shadowers env ∧
      (!mn env'.
        ALOOKUP menv mn = SOME env'
        ⇒
        ?map.
          FLOOKUP mods mn = SOME map ∧
          global_env_inv_flat genv map {} env'))`,
  srw_tac[][semanticPrimitivesTheory.Boolv_def,modSemTheory.Boolv_def] >>
  srw_tac[][Once v_rel_cases] >>
  srw_tac[][Q.SPECL[`genv`,`[]`](CONJUNCT1(CONJUNCT2 v_rel_cases))] >>
  metis_tac []);

val vs_rel_list_rel = Q.prove (
  `!genv vs vs'. vs_rel genv vs vs' = LIST_REL (v_rel genv) vs vs'`,
   induct_on `vs` >>
   srw_tac[][v_rel_eqns] >>
   metis_tac []);

val vs_rel_append1 = Q.prove (
  `!genv vs v vs' v'.
    vs_rel genv (vs++[v]) (vs'++[v'])
    ⇔
    vs_rel genv vs vs' ∧
    v_rel genv v v'`,
  induct_on `vs` >>
  srw_tac[][] >>
  cases_on `vs'` >>
  srw_tac[][v_rel_eqns]
  >- (cases_on `vs` >>
      srw_tac[][v_rel_eqns]) >>
  metis_tac []);

val length_vs_rel = Q.prove (
  `!vs genv vs'.
    vs_rel genv vs vs'
    ⇒
    LENGTH vs = LENGTH vs'`,
  metis_tac[vs_rel_list_rel,LIST_REL_LENGTH])

val env_rel_dom = Q.prove (
  `!genv env env_i1.
    env_rel genv env env_i1
    ⇒
    MAP FST env = MAP FST env_i1`,
  induct_on `env` >>
  srw_tac[][v_rel_eqns] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  srw_tac[][] >>
  metis_tac []);

val env_rel_lookup = Q.prove (
  `!genv menv env genv x v env'.
    ALOOKUP env x = SOME v ∧
    env_rel genv env env'
    ⇒
    ?v'.
      v_rel genv v v' ∧
      ALOOKUP env' x = SOME v'`,
  induct_on `env` >>
  srw_tac[][] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  cases_on `h0 = x` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_rel_eqns]);

val env_rel_append = Q.prove (
  `!genv env1 env2 env1' env2'.
    env_rel genv env1 env1' ∧
    env_rel genv env2 env2'
    ⇒
    env_rel genv (env1++env2) (env1'++env2')`,
   induct_on `env1` >>
   srw_tac[][v_rel_eqns] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[v_rel_eqns]);

val env_rel_reverse = Q.prove (
  `!genv env1 env2.
    env_rel genv env1 env2
    ⇒
    env_rel genv (REVERSE env1) (REVERSE env2)`,
   induct_on `env1` >>
   srw_tac[][v_rel_eqns] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[v_rel_eqns] >>
   match_mp_tac env_rel_append >>
   srw_tac[][v_rel_eqns]);

val length_env_rel = Q.prove (
  `!env genv env'.
    env_rel genv env env'
    ⇒
    LENGTH env = LENGTH env'`,
  induct_on `env` >>
  srw_tac[][v_rel_eqns] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  metis_tac []);

val env_rel_el = Q.prove (
  `!genv env env_i1.
    env_rel genv env env_i1 ⇔
    LENGTH env = LENGTH env_i1 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i1)) ∧ v_rel genv (SND (EL n env)) (SND (EL n env_i1))`,
  induct_on `env` >>
  srw_tac[][v_rel_eqns]
  >- (cases_on `env_i1` >>
      full_simp_tac(srw_ss())[]) >>
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

val env_rel_list_rel = Q.prove (
`!genv env env'.
  env_rel genv env env'
  ⇔
  LIST_REL (λ(x,y) (x',y'). x = x' ∧ v_rel genv y y') env env'`,
 Induct_on `env` >>
 rw [Once v_rel_cases] >>
 Cases_on `env'` >>
 fs [] >>
 PairCases_on `h` >>
 PairCases_on `h'` >>
 fs [] >>
 metis_tac []);

val v_rel_weakening = Q.prove (
  `(!genv v v_i1.
    v_rel genv v v_i1
    ⇒
    ∀l. v_rel (genv++l) v v_i1) ∧
   (!genv vs vs_i1.
    vs_rel genv vs vs_i1
    ⇒
    !l. vs_rel (genv++l) vs vs_i1) ∧
   (!genv env env_i1.
    env_rel genv env env_i1
    ⇒
    !l. env_rel (genv++l) env env_i1) ∧
   (!genv map shadowers env.
    global_env_inv_flat genv map shadowers env
    ⇒
    !l. global_env_inv_flat (genv++l) map shadowers env) ∧
   (!genv mods tops menv shadowers env.
    global_env_inv genv mods tops menv shadowers env
    ⇒
    !l.global_env_inv (genv++l) mods tops menv shadowers env)`,
  ho_match_mp_tac v_rel_ind >>
  srw_tac[][v_rel_eqns]
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`mods`, `tops`, `env`, `env'`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`mods`, `tops`, `env`, `env'`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns])
  >- (srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`mods`, `tops`, `tops'`] >>
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, SUBSET_DEF, v_rel_eqns, EL_APPEND1] >>
      srw_tac[][] >>
      res_tac >>
      qexists_tac `n` >>
      srw_tac[][EL_APPEND1] >>
      decide_tac)
  >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]
  >- metis_tac []);

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
    vs_rel genv vs vs'
    ⇒
    sv_rel genv (Varray vs) (Varray vs'))`;

val sv_rel_weakening = Q.prove (
  `(!genv sv sv_i1.
    sv_rel genv sv sv_i1
    ⇒
    ∀l. sv_rel (genv++l) sv sv_i1)`,
   srw_tac[][sv_rel_cases] >>
   metis_tac [v_rel_weakening]);

val (s_rel_rules, s_rel_ind, s_rel_cases) = Hol_reln `
  (!s s'.
    LIST_REL (sv_rel s'.globals) s.refs s'.refs ∧
    s.defined_types = s'.defined_types ∧
    s.clock = s'.clock ∧
    s.ffi = s'.ffi
    ⇒
    s_rel s s')`;

val (env_all_rel_rules, env_all_rel_ind, env_all_rel_cases) = Hol_reln `
  (!genv mods tops env env' env_i1 locals.
    locals = set (MAP FST env.v) ∧
    global_env_inv genv mods tops env.m locals env' ∧
    env_rel genv env.v env_i1.v ∧
    env_i1.c = env.c
    ⇒
    env_all_rel genv mods tops (env with v := env.v ++ env') env_i1 locals)`;

val match_result_rel_def = Define
  `(match_result_rel genv env' (Match env) (Match env_i1) =
     ?env''. env = env'' ++ env' ∧ env_rel genv env'' env_i1) ∧
   (match_result_rel genv env' No_match No_match = T) ∧
   (match_result_rel genv env' Match_type_error Match_type_error = T) ∧
   (match_result_rel genv env' _ _ = F)`;

val invariant_def = Define `
  invariant mods tops menv env s s_i1 mod_names ⇔
    set (MAP FST menv) ⊆ mod_names ∧
    global_env_inv s_i1.globals mods tops menv {} env ∧
    s_rel s s_i1`;

val invariant_change_clock = Q.store_thm("invariant_change_clock",
  `invariant menv env envm envv st1 st2 mods ⇒
   invariant menv env envm envv (st1 with clock := k) (st2 with clock := k) mods`,
  srw_tac[][invariant_def] >> full_simp_tac(srw_ss())[s_rel_cases])

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
    vs_rel genv vs1 vs1_i1 ∧
    vs_rel genv vs2 vs2_i1
    ⇒
    do_eq_list vs1_i1 vs2_i1 = r)`,
  ho_match_mp_tac terminationTheory.do_eq_ind >>
  srw_tac[][terminationTheory.do_eq_def, modSemTheory.do_eq_def, v_rel_eqns] >>
  srw_tac[][] >>
  srw_tac[][terminationTheory.do_eq_def, modSemTheory.do_eq_def, v_rel_eqns] >>
  imp_res_tac length_vs_rel >>
  full_simp_tac(srw_ss())[]
  >- metis_tac []
  >- (rpt (qpat_assum `vs_rel env vs x0` (mp_tac o SIMP_RULE (srw_ss()) [Once v_rel_cases])) >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[vs_rel_list_rel, terminationTheory.do_eq_def, modSemTheory.do_eq_def] >>
      res_tac >>
      full_simp_tac(srw_ss())[modSemTheory.do_eq_def])
  >> TRY (
    CASE_TAC >>
    res_tac >>
    every_case_tac >>
    full_simp_tac(srw_ss())[] >>
    metis_tac []) >>
  full_simp_tac(srw_ss())[Once v_rel_cases] >>
  srw_tac[][modSemTheory.do_eq_def] );

val do_con_check = Q.prove (
  `!genv mods tops env cn es env_i1 locals.
    do_con_check env.c cn (LENGTH es) ∧
    env_all_rel genv mods tops env env_i1 locals
    ⇒
    do_con_check env_i1.c cn (LENGTH (compile_exps mods (DRESTRICT tops (COMPL locals)) es))`,
  srw_tac[][do_con_check_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >>
  srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  ntac 3 (pop_assum (fn _ => all_tac)) >>
  induct_on `es` >>
  srw_tac[][compile_exp_def]);

val char_list_to_v = prove(
  ``∀ls. v_rel genv (char_list_to_v ls) (char_list_to_v ls)``,
  Induct >> simp[semanticPrimitivesTheory.char_list_to_v_def,
                 modSemTheory.char_list_to_v_def,
                 v_rel_eqns])

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
      vs_rel genv vs1 vs2`,
  ho_match_mp_tac terminationTheory.v_to_list_ind >>
  srw_tac[][terminationTheory.v_to_list_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[v_rel_eqns, modSemTheory.v_to_list_def] >>
  srw_tac[][] >>
  metis_tac [NOT_SOME_NONE, SOME_11]);

val do_app = Q.prove (
  `!genv s1 s2 op vs r s1_i1 vs_i1.
    do_app s1 op vs = SOME (s2, r) ∧
    LIST_REL (sv_rel genv) (FST s1) (FST s1_i1) ∧
    SND s1 = SND s1_i1 ∧
    vs_rel genv vs vs_i1
    ⇒
     ∃r_i1 s2_i1.
       LIST_REL (sv_rel genv) (FST s2) (FST s2_i1) ∧
       SND s2 = SND s2_i1 ∧
       result_rel v_rel genv r r_i1 ∧
       do_app s1_i1 op vs_i1 = SOME (s2_i1, r_i1)`,
  rpt gen_tac >>
  Cases_on `s1` >>
  Cases_on `s1_i1` >>
  Cases_on `op`
  >- ((* Opn *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Opb *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Equality *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [Boolv_11, do_eq, eq_result_11, eq_result_distinct])
  >- ((* Opapp *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Opassign *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_assign_def,store_v_same_type_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[] >-
      metis_tac [EVERY2_LUPDATE_same, sv_rel_rules] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN,sv_rel_cases] >>
      srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >> res_tac >> full_simp_tac(srw_ss())[])
  >- ((* Opref *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Opderef *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
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
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Aw8sub *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
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
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
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
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
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
  >- ((* W8fromInt *)
    srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def,vs_rel_list_rel]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* W8toInt *)
    srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def,vs_rel_list_rel]
    \\ fsrw_tac[][v_rel_eqns] \\ srw_tac[][result_rel_cases,v_rel_eqns] )
  >- ((* Ord *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Chr *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Chopb *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* Explode *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      simp[char_list_to_v])
  >- ((* Implode *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      imp_res_tac v_to_char_list >>
      srw_tac[][])
  >- ((* Strlen *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def])
  >- ((* VfromList *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      imp_res_tac v_to_list >>
      srw_tac[][])
  >- ((* Vsub *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      srw_tac[][markerTheory.Abbrev_def] >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      full_simp_tac(srw_ss())[arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ])
  >- ((* Vlength *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][] >>
      metis_tac [LIST_REL_LENGTH, vs_rel_list_rel])
  >- ((* Aalloc *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_alloc_def] >>
      srw_tac[][sv_rel_cases, vs_rel_list_rel, LIST_REL_REPLICATE_same] >>
      metis_tac [LIST_REL_LENGTH])
  >- ((* Asub *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      decide_tac)
  >- ((* Alength *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[store_lookup_def, sv_rel_cases] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      res_tac >>
      full_simp_tac(srw_ss())[sv_rel_cases] >>
      metis_tac [store_v_distinct, store_v_11, LIST_REL_LENGTH, vs_rel_list_rel])
  >- ((* Aupdate *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LET_THM, arithmeticTheory.NOT_GREATER_EQ, GSYM arithmeticTheory.LESS_EQ] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN, sv_rel_cases] >>
      res_tac >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] >>
      imp_res_tac LIST_REL_LENGTH >>
      full_simp_tac(srw_ss())[LIST_REL_EL_EQN] >>
      srw_tac[][markerTheory.Abbrev_def, EL_LUPDATE] >>
      srw_tac[][] >>
      decide_tac)
  >- ((* FFI *)
      srw_tac[][evalPropsTheory.do_app_cases, modSemTheory.do_app_def, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[v_rel_eqns, result_rel_cases, semanticPrimitivesTheory.prim_exn_def, modSemTheory.prim_exn_def] >>
      full_simp_tac(srw_ss())[store_lookup_def, store_assign_def, store_v_same_type_def] >>
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
  `!x funs e mods tops y.
    find_recfun x funs = SOME (y,e)
    ⇒
    find_recfun x (compile_funs mods tops funs) = SOME (y,compile_exp mods (tops \\ y) e)`,
   induct_on `funs` >>
   srw_tac[][Once find_recfun_def, compile_exp_def] >>
   PairCases_on `h` >>
   full_simp_tac(srw_ss())[] >>
   every_case_tac >>
   full_simp_tac(srw_ss())[Once find_recfun_def, compile_exp_def]);

val do_app_rec_help = Q.prove (
  `!genv env'' funs env''' env_i1' mods' tops' funs'.
    env_rel genv env''.v env_i1' ∧
    set (MAP FST env''') DIFF set (MAP FST env''.v) ⊆ FDOM tops' ∧
    global_env_inv genv mods' tops' env''.m (set (MAP FST env_i1')) env'''
    ⇒
    env_rel genv
    (MAP
       (λ(fn,n,e). (fn,Recclosure (env'' with v := env''.v ++ env''') funs' fn))
       funs)
    (MAP
       (λ(fn,n,e).
          (fn,
           Recclosure (env''.c,env_i1')
             (compile_funs mods'
                (DRESTRICT tops'
                   (COMPL (set (MAP FST env_i1') ∪ set (MAP FST funs'))))
                funs') fn))
       (compile_funs mods'
          (DRESTRICT tops'
             (COMPL (set (MAP FST env_i1') ∪ set (MAP FST funs')))) funs))`,
  induct_on `funs` >>
  srw_tac[][v_rel_eqns, compile_exp_def] >>
  PairCases_on `h` >>
  srw_tac[][v_rel_eqns, compile_exp_def] >>
  srw_tac[][Once v_rel_cases] >>
  MAP_EVERY qexists_tac [`mods'`, `tops'`, `env''`, `env'''`] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_rel_eqns]);

val global_env_inv_add_locals = Q.prove (
  `!genv mods tops menv locals1 locals2 env.
    global_env_inv genv mods tops menv locals1 env
    ⇒
    global_env_inv genv mods tops menv (locals2 ∪ locals1) env`,
  srw_tac[][v_rel_eqns]);

val global_env_inv_extend2 = Q.prove (
  `!genv mods tops menv env tops' env' locals.
    MAP FST env' = REVERSE (MAP FST tops') ∧
    global_env_inv genv mods tops menv locals env ∧
    global_env_inv genv FEMPTY (FEMPTY |++ tops') [] locals env'
    ⇒
    global_env_inv genv mods (tops |++ tops') menv locals (env'++env)`,
  srw_tac[][v_rel_eqns, flookup_fupdate_list] >>
  full_case_tac >>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND] >>
  full_case_tac >>
  full_simp_tac(srw_ss())[] >>
  res_tac >>
  full_simp_tac(srw_ss())[] >>
  rpt (pop_assum mp_tac) >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[ALOOKUP_FAILS] >>
  imp_res_tac ALOOKUP_MEM >>
  `set (MAP FST env') = set (REVERSE (MAP FST tops'))` by metis_tac [] >>
  full_simp_tac(srw_ss())[EXTENSION] >>
  metis_tac [pair_CASES, MEM_MAP, FST]);

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
    vs_rel genv vs vs_i1
    ⇒
     ∃mods tops env_i1 locals.
       env_all_rel genv mods tops env env_i1 locals ∧
       do_opapp vs_i1 = SOME (env_i1, compile_exp mods (DRESTRICT tops (COMPL locals)) e)`,
   srw_tac[][do_opapp_cases, modSemTheory.do_opapp_def, vs_rel_list_rel] >>
   full_simp_tac(srw_ss())[LIST_REL_CONS1] >>
   srw_tac[][]
   >- (qpat_assum `v_rel genv (Closure env'' n e) v1_i1` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       MAP_EVERY qexists_tac [`mods`, `tops`, `n INSERT set (MAP FST env_i1)`] >>
       srw_tac[][DRESTRICT_DOMSUB, compl_insert, env_all_rel_cases] >>
       MAP_EVERY qexists_tac [`env with v := (n, v2) :: env.v`, `env'`] >>
       srw_tac[][v_rel_eqns]
       >- metis_tac [env_rel_dom] >>
       full_simp_tac(srw_ss())[v_rel_eqns])
   >- (qpat_assum `v_rel genv (Recclosure env'' funs n') v1_i1` mp_tac >>
       srw_tac[][Once v_rel_cases] >>
       srw_tac[][] >>
       imp_res_tac find_recfun >>
       srw_tac[][]
       >- (MAP_EVERY qexists_tac [`mods`, `tops`, `n'' INSERT set (MAP FST env_i1) ∪ set (MAP FST funs)`] >>
           srw_tac[][DRESTRICT_DOMSUB, compl_insert, env_all_rel_cases] >>
           srw_tac[][]
           >- (MAP_EVERY qexists_tac [`env with v := (n'', v2)::build_rec_env funs (env with v := env.v ++ env') env.v`, `env'`] >>
               srw_tac[][evalPropsTheory.build_rec_env_merge, EXTENSION]
               >- (srw_tac[][MEM_MAP, EXISTS_PROD] >>
                   imp_res_tac env_rel_dom >>
                   metis_tac [pair_CASES, FST, MEM_MAP, EXISTS_PROD, LAMBDA_PROD])
               >- metis_tac [INSERT_SING_UNION, global_env_inv_add_locals, UNION_COMM]
               >- (full_simp_tac(srw_ss())[v_rel_eqns, build_rec_env_merge] >>
                   match_mp_tac env_rel_append >>
                   srw_tac[][] >>
                   match_mp_tac do_app_rec_help >>
                   srw_tac[][] >>
                   full_simp_tac(srw_ss())[v_rel_eqns]))
           >- (
            simp[compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
            full_simp_tac(srw_ss())[FST_triple]))
       >- (MAP_EVERY qexists_tac [`mods`, `tops|++tops'`, `{n''}`] >>
           srw_tac[][DRESTRICT_UNIV, GSYM DRESTRICT_DOMSUB, compl_insert, env_all_rel_cases] >>
           MAP_EVERY qexists_tac [`<| m := env''.m; c := env''.c; v := [(n'',v2)] |>`,
                                  `build_rec_env funs env'' env''.v`] >>
           srw_tac[][semanticPrimitivesTheory.environment_component_equality, evalPropsTheory.build_rec_env_merge, EXTENSION]
           >- (match_mp_tac global_env_inv_extend2 >>
               srw_tac[][MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_triple, GSYM MAP_REVERSE]
               >- metis_tac [global_env_inv_add_locals, UNION_EMPTY] >>
               srw_tac[][v_rel_eqns] >>
               `MEM x (MAP FST funs)`
                         by (imp_res_tac ALOOKUP_MEM >>
                             full_simp_tac(srw_ss())[MEM_MAP] >>
                             PairCases_on `y` >>
                             srw_tac[][] >>
                             full_simp_tac(srw_ss())[] >>
                             metis_tac [FST, MEM_MAP, pair_CASES]) >>
               res_tac >>
               qexists_tac `n` >>
               srw_tac[][] >>
               `v = Recclosure env'' funs x` by metis_tac [lookup_build_rec_env_lem] >>
               srw_tac[][Once v_rel_cases] >>
               MAP_EVERY qexists_tac [`mods`, `tops`, `tops'`] >>
               srw_tac[][find_recfun_ALOOKUP])
           >- full_simp_tac(srw_ss())[v_rel_eqns, modPropsTheory.build_rec_env_merge])));

val build_conv = Q.prove (
  `!genv mods tops env cn vs v vs' env_i1 locals.
    (build_conv env.c cn vs = SOME v) ∧
    env_all_rel genv mods tops env env_i1 locals ∧
    vs_rel genv vs vs'
    ⇒
    ∃v'.
      v_rel genv v v' ∧
      build_conv env_i1.c cn vs' = SOME v'`,
  srw_tac[][semanticPrimitivesTheory.build_conv_def, modSemTheory.build_conv_def] >>
  every_case_tac >>
  srw_tac[][Once v_rel_cases] >>
  full_simp_tac(srw_ss())[env_all_rel_cases] >> rev_full_simp_tac(srw_ss())[]);

val pmatch = Q.prove (
  `(!cenv s p v env r env' env'' genv env_i1 s_i1 v_i1.
    pmatch cenv s p v env = r ∧
    env = env' ++ env'' ∧
    LIST_REL (sv_rel genv) s s_i1 ∧
    v_rel genv v v_i1 ∧
    env_rel genv env' env_i1
    ⇒
    ?r_i1.
      pmatch cenv s_i1 p v_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1) ∧
   (!cenv s ps vs env r env' env'' genv env_i1 s_i1 vs_i1.
    pmatch_list cenv s ps vs env = r ∧
    env = env' ++ env'' ∧
    LIST_REL (sv_rel genv) s s_i1 ∧
    vs_rel genv vs vs_i1 ∧
    env_rel genv env' env_i1
    ⇒
    ?r_i1.
      pmatch_list cenv s_i1 ps vs_i1 env_i1 = r_i1 ∧
      match_result_rel genv env'' r r_i1)`,
  ho_match_mp_tac terminationTheory.pmatch_ind >>
  srw_tac[][terminationTheory.pmatch_def, modSemTheory.pmatch_def] >>
  full_simp_tac(srw_ss())[match_result_rel_def, modSemTheory.pmatch_def, v_rel_eqns] >>
  imp_res_tac LIST_REL_LENGTH
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [length_vs_rel])
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def]
      >- (full_simp_tac(srw_ss())[store_lookup_def] >>
          metis_tac [])
      >- (full_simp_tac(srw_ss())[store_lookup_def] >>
          metis_tac [length_vs_rel])
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
  >> TRY (
      CASE_TAC >>
      every_case_tac >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      srw_tac[][] >>
      pop_assum mp_tac >>
      pop_assum mp_tac >>
      res_tac >>
      srw_tac[][] >>
      CCONTR_TAC >>
      full_simp_tac(srw_ss())[match_result_rel_def] >>
      metis_tac [match_result_rel_def, match_result_distinct]) >>
  full_simp_tac(srw_ss())[Once v_rel_cases] >>
  srw_tac[][modSemTheory.pmatch_def, match_result_rel_def]);

(* compiler correctness *)

val global_env_inv_lookup_top = Q.prove (
  `!genv mods tops menv shadowers env x v n.
    global_env_inv genv mods tops menv shadowers env ∧
    ALOOKUP env x = SOME v ∧
    x ∉ shadowers ∧
    FLOOKUP tops x = SOME n
    ⇒
    ?v_i1. LENGTH genv > n ∧ EL n genv = SOME v_i1 ∧ v_rel genv v v_i1`,
  srw_tac[][v_rel_eqns] >>
  res_tac >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  metis_tac []);

val global_env_inv_lookup_mod1 = Q.prove (
  `!genv mods tops menv shadowers env genv mn n env'.
    global_env_inv genv mods tops menv shadowers env ∧
    ALOOKUP menv mn = SOME env'
    ⇒
    ?n. FLOOKUP mods mn = SOME n`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  metis_tac []);

val global_env_inv_lookup_mod2 = Q.prove (
  `!genv mods tops menv shadowers env genv mn n env' x v map.
    global_env_inv genv mods tops menv shadowers env ∧
    ALOOKUP menv mn = SOME env' ∧
    ALOOKUP env' x = SOME v ∧
    FLOOKUP mods mn = SOME map
    ⇒
    ?n. FLOOKUP map x = SOME n`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  res_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  full_simp_tac(srw_ss())[]);

val global_env_inv_lookup_mod3 = Q.prove (
  `!genv mods tops menv shadowers env genv mn n env' x v map n.
    global_env_inv genv mods tops menv shadowers env ∧
    ALOOKUP menv mn = SOME env' ∧
    ALOOKUP env' x = SOME v ∧
    FLOOKUP mods mn = SOME map ∧
    FLOOKUP map x = SOME n
    ⇒
    LENGTH genv > n ∧ ?v_i1. EL n genv = SOME v_i1 ∧ v_rel genv v v_i1`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  res_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  metis_tac []);

val s = mk_var("s",
  ``bigStep$evaluate`` |> type_of |> strip_fun |> #1 |> el 3
  |> type_subst[alpha |-> ``:'ffi``]);

val compile_exp_correct' = Q.prove (
   `(∀^s env es res.
     funBigStep$evaluate s env es = res ⇒
     (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
     !mods tops s' r env_i1 s_i1 es_i1 locals.
       res = (s',r) ∧
       env_all_rel s_i1.globals mods tops env env_i1 locals ∧
       s_rel s s_i1 ∧
       es_i1 = compile_exps mods (DRESTRICT tops (COMPL locals)) es
       ⇒
       ?s'_i1 r_i1.
         result_rel vs_rel s_i1.globals r r_i1 ∧
         s_rel s' s'_i1 ∧
         modSem$evaluate env_i1 s_i1 es_i1 = (s'_i1, r_i1)) ∧
   (∀^s env v pes err_v res.
     funBigStep$evaluate_match s env v pes err_v = res ⇒
     SND res ≠ Rerr (Rabort Rtype_error) ⇒
     !mods tops s' r env_i1 s_i1 v_i1 pes_i1 err_v_i1 locals.
       (res = (s',r)) ∧
       env_all_rel s_i1.globals mods tops env env_i1 locals ∧
       s_rel s s_i1 ∧
       v_rel s_i1.globals v v_i1 ∧
       pes_i1 = compile_pes mods (DRESTRICT tops (COMPL locals)) pes ∧
       v_rel s_i1.globals err_v err_v_i1
       ⇒
       ?s'_i1 r_i1.
         result_rel vs_rel s_i1.globals r r_i1 ∧
         s_rel s' s'_i1 ∧
         modSem$evaluate_match env_i1 s_i1 v_i1 pes_i1 err_v_i1 = (s'_i1, r_i1))`,
  ho_match_mp_tac terminationTheory.evaluate_ind >>
  srw_tac[][terminationTheory.evaluate_def, modSemTheory.evaluate_def,compile_exp_def] >>
  full_simp_tac(srw_ss())[result_rel_eqns, v_rel_eqns] >>
  TRY(first_assum(split_pair_case_tac o lhs o concl) >> full_simp_tac(srw_ss())[])
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    simp[] >>
    first_assum(fn th => subterm split_pair_case_tac (concl th)) >> full_simp_tac(srw_ss())[] >>
    qpat_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >- (
      srw_tac[][] >>
      asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] ) >>
    strip_tac >>
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    disch_then drule >> simp[] >> strip_tac >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[])
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >>
    imp_res_tac evaluate_sing >> full_simp_tac(srw_ss())[])
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] )
  >- (
    reverse (srw_tac[][])
    >- metis_tac [do_con_check, EVERY2_REVERSE, vs_rel_list_rel, compile_exps_reverse]
    >- metis_tac [do_con_check, EVERY2_REVERSE, vs_rel_list_rel, compile_exps_reverse] >>
    `env_i1.c = env.c` by full_simp_tac(srw_ss())[env_all_rel_cases] >>
    `v3' = Rerr (Rabort Rtype_error) ∨
     (?err. v3' = Rerr err ∧ err ≠ Rabort Rtype_error) ∨
     (?v. v3' = Rval v)`
       by (Cases_on `v3'` >> full_simp_tac(srw_ss())[]) >>
    full_simp_tac(srw_ss())[] >>
    srw_tac[][result_rel_cases] >>
    first_x_assum (fn th => first_assum (assume_tac o MATCH_MP (SIMP_RULE (srw_ss()) [GSYM AND_IMP_INTRO] th))) >>
    pop_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
    simp [GSYM compile_exps_reverse] >>
    full_simp_tac(srw_ss())[result_rel_cases] >>
    rpt var_eq_tac >>
    Cases_on `build_conv env.c cn (REVERSE v)` >>
    full_simp_tac(srw_ss())[] >>
    rpt var_eq_tac >>
    simp [] >>
    every_case_tac
    >- metis_tac [NOT_SOME_NONE, build_conv, EVERY2_REVERSE, vs_rel_list_rel] >>
    simp [vs_rel_list_rel]
    >- metis_tac [SOME_11, build_conv, EVERY2_REVERSE, vs_rel_list_rel])
  >- (* Variable lookup *)
     (full_simp_tac(srw_ss())[env_all_rel_cases] >>
      cases_on `n` >>
      srw_tac[][compile_exp_def] >>
      full_simp_tac(srw_ss())[lookup_var_id_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[ALOOKUP_APPEND] >>
      srw_tac[][]
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[] >>
          simp [evaluate_def, result_rel_cases] >>
          srw_tac[][]
          >- (full_simp_tac(srw_ss())[v_rel_eqns, FLOOKUP_DRESTRICT] >>
              every_case_tac >>
              full_simp_tac(srw_ss())[ALOOKUP_FAILS] >>
              res_tac >>
              full_simp_tac(srw_ss())[MEM_MAP, FORALL_PROD] >>
              metis_tac [pair_CASES, FST, NOT_SOME_NONE])
          >- (imp_res_tac env_rel_lookup >>
              full_simp_tac(srw_ss())[vs_rel_list_rel]))
      >- (every_case_tac >>
          full_simp_tac(srw_ss())[FLOOKUP_DRESTRICT] >>
          simp [evaluate_def, result_rel_cases, vs_rel_list_rel] >>
          imp_res_tac global_env_inv_lookup_top >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          imp_res_tac ALOOKUP_MEM >>
          full_simp_tac (srw_ss()++ARITH_ss) [MEM_MAP] >>
          metis_tac [pair_CASES, FST, NOT_SOME_NONE])
      >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod1]
      >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod2]
      >- (imp_res_tac global_env_inv_lookup_mod3 >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          full_simp_tac(srw_ss())[] >>
          srw_tac[][] >>
          simp [result_rel_cases, evaluate_def] >>
          srw_tac[][vs_rel_list_rel]))
  >- (* Closure creation *)
     (srw_tac[][Once v_rel_cases] >>
      full_simp_tac(srw_ss())[env_all_rel_cases] >>
      srw_tac[][] >>
      MAP_EVERY qexists_tac [`mods`, `tops`, `env'`, `env''`] >>
      imp_res_tac env_rel_dom >>
      srw_tac[][]
      >- (full_simp_tac(srw_ss())[SUBSET_DEF, v_rel_eqns] >>
          srw_tac[][] >>
          `¬(ALOOKUP env'' x = NONE)` by metis_tac [ALOOKUP_FAILS, MEM_MAP, FST, pair_CASES] >>
          cases_on `ALOOKUP env'' x` >>
          full_simp_tac(srw_ss())[] >>
          res_tac >>
          full_simp_tac(srw_ss())[FLOOKUP_DEF])
      >- (imp_res_tac global_env_inv_lookup_top >>
          full_simp_tac(srw_ss())[] >>
          imp_res_tac disjoint_drestrict >>
          srw_tac[][]))
  (* function application *)
  >- (
    srw_tac [boolSimps.DNF_ss] [PULL_EXISTS] >>
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    full_simp_tac(srw_ss())[compile_exps_reverse] >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    qpat_assum`_ = (_,r)`mp_tac >>
    ntac 2 (BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[]) >- (
      BasicProvers.TOP_CASE_TAC >>
      drule do_opapp >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] >>
      imp_res_tac EVERY2_REVERSE >>
      disch_then drule >> strip_tac >>
      IF_CASES_TAC >> strip_tac >> full_simp_tac(srw_ss())[] >> rveq >- (
        full_simp_tac(srw_ss())[] >> asm_exists_tac >> srw_tac[][] >>
        full_simp_tac(srw_ss())[s_rel_cases] ) >>
      rev_full_simp_tac(srw_ss())[] >>
      imp_res_tac evaluate_globals >>
      pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
      qmatch_assum_abbrev_tac`_ = _ ss` >>
      `ss.globals = (dec_clock ss).globals` by EVAL_TAC >>
      full_simp_tac(srw_ss())[Abbr`ss`] >>
      first_x_assum drule >>
      discharge_hyps >- (
        full_simp_tac(srw_ss())[s_rel_cases,modSemTheory.dec_clock_def,funBigStepTheory.dec_clock_def] ) >>
      strip_tac >> full_simp_tac(srw_ss())[PULL_EXISTS] >>
      asm_exists_tac >> full_simp_tac(srw_ss())[] >>
      srw_tac[][] >> full_simp_tac(srw_ss())[] >>
      full_simp_tac(srw_ss())[s_rel_cases] ) >>
    BasicProvers.TOP_CASE_TAC >>
    BasicProvers.TOP_CASE_TAC >>
    strip_tac >> rveq >>
    drule do_app >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >>
    imp_res_tac EVERY2_REVERSE >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    ONCE_REWRITE_TAC[CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    disch_then drule >>
    full_simp_tac(srw_ss())[s_rel_cases] >>
    CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss()++QUANT_INST_ss[pair_default_qp])[])) >>
    disch_then drule >> strip_tac >>
    simp[] >>
    full_simp_tac(srw_ss())[PULL_EXISTS,result_rel_cases])
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    qpat_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
      BasicProvers.TOP_CASE_TAC >> srw_tac[][evaluate_def] ) >>
    BasicProvers.TOP_CASE_TAC >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    imp_res_tac funBigStepPropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
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
      full_simp_tac(srw_ss())[vs_rel_list_rel] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[Once v_rel_cases] >>
      srw_tac[][do_if_def] >> full_simp_tac(srw_ss())[] >>
      EVAL_TAC >>
      srw_tac[][state_component_equality] >>
      pop_assum mp_tac >> EVAL_TAC >>
      pop_assum mp_tac >> EVAL_TAC >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] ) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    first_x_assum drule >> simp[] >> strip_tac >>
    asm_exists_tac >> simp[] >>
    asm_exists_tac >> simp[] >>
    full_simp_tac(srw_ss())[terminationTheory.do_log_thm] >>
    qpat_assum`_ = SOME _`mp_tac >>
    srw_tac[][evaluate_def] >>
    full_simp_tac(srw_ss())[result_rel_cases,vs_rel_list_rel] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[Once v_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    srw_tac[][do_if_def] >>
    EVAL_TAC >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >>
    pop_assum mp_tac >> EVAL_TAC >>
    pop_assum mp_tac >> EVAL_TAC >>
    srw_tac[][])
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    qpat_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    asm_exists_tac >> simp[] >>
    asm_exists_tac >> simp[] >>
    imp_res_tac funBigStepPropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.do_if_def] >>
    qpat_assum`_ = SOME _`mp_tac >> srw_tac[][] >>
    full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >> rveq >>
    full_simp_tac(srw_ss())[Once v_rel_cases,semanticPrimitivesTheory.Boolv_def] >>
    srw_tac[][do_if_def] >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >>
    pop_assum mp_tac >> EVAL_TAC >>
    pop_assum mp_tac >> EVAL_TAC >>
    srw_tac[][] )
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    qpat_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    FIRST_X_ASSUM drule >> simp[] >> strip_tac >>
    rator_x_assum`result_rel`mp_tac >>
    simp[Once result_rel_cases] >> strip_tac >>
    imp_res_tac funBigStepPropsTheory.evaluate_length >> full_simp_tac(srw_ss())[] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[LENGTH_NIL] >> rveq >>
    full_simp_tac(srw_ss())[vs_rel_list_rel] >>
    first_x_assum drule >>
    simp[Bindv_def] >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    simp[vs_rel_list_rel] )
  >- (
    qpat_assum`_ ⇒ _`mp_tac >>
    discharge_hyps >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    disch_then drule >> simp[] >> strip_tac >>
    qpat_assum`_ = (_,r)`mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- (
      srw_tac[][] >> asm_exists_tac >> simp[] >>
      asm_exists_tac >> simp[] >>
      Cases_on`xo`>> srw_tac[][compile_exp_def,evaluate_def] >>
      full_simp_tac(srw_ss())[result_rel_cases] >> rveq >> full_simp_tac(srw_ss())[] ) >>
    srw_tac[][] >> rev_full_simp_tac(srw_ss())[] >>
    imp_res_tac evaluate_globals >>
    pop_assum (assume_tac o SYM) >> full_simp_tac(srw_ss())[] >>
    rator_x_assum`result_rel`mp_tac >>
    simp[Once result_rel_cases] >> strip_tac >>
    Cases_on`xo`>> srw_tac[][compile_exp_def,evaluate_def] >- (
      first_x_assum match_mp_tac >>
      simp[libTheory.opt_bind_def] >>
      qpat_abbrev_tac`env2 = env_i1 with v updated_by _` >>
      `env2 = env_i1` by (
        simp[environment_component_equality,Abbr`env2`,libTheory.opt_bind_def] ) >>
      simp[] ) >>
    qpat_abbrev_tac`env2 = env_i1 with v updated_by _` >>
    first_x_assum(qspecl_then[`mods`,`tops`,`env2`]mp_tac) >>
    simp[Abbr`env2`] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    disch_then drule >>
    disch_then(qspec_then`x INSERT locals`mp_tac) >>
    discharge_hyps >- (
      full_simp_tac(srw_ss())[env_all_rel_cases] >>
      full_simp_tac(srw_ss())[semanticPrimitivesTheory.environment_component_equality,libTheory.opt_bind_def] >>
      srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][] >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      simp[GSYM CONJ_ASSOC] >>
      drule global_env_inv_add_locals >>
      disch_then(qspec_then`{x}`strip_assume_tac) >>
      simp[Once INSERT_SING_UNION] >>
      asm_exists_tac >> simp[] >>
      full_simp_tac(srw_ss())[env_rel_el] >>
      Cases >> simp[] >>
      imp_res_tac evaluate_sing >>
      full_simp_tac(srw_ss())[vs_rel_list_rel] ) >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    full_simp_tac(srw_ss())[compl_insert] >>
    full_simp_tac(srw_ss())[DRESTRICT_DOMSUB])
  >- (
    srw_tac[][markerTheory.Abbrev_def] >>
    srw_tac[][evaluate_def,compile_funs_map,MAP_MAP_o,o_DEF,UNCURRY] >>
    full_simp_tac(srw_ss())[FST_triple,ETA_AX] >>
    simp[drestrict_iter_list] >>
    simp[GSYM COMPL_UNION] >>
    first_x_assum match_mp_tac >> simp[] >>
    full_simp_tac(srw_ss())[env_all_rel_cases,semanticPrimitivesTheory.environment_component_equality] >>
    srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][] >>
    simp[evalPropsTheory.build_rec_env_merge,build_rec_env_merge] >>
    qexists_tac`env''`>>simp[MAP_MAP_o,o_DEF,UNCURRY,ETA_AX] >>
    simp[UNION_COMM] >>
    imp_res_tac global_env_inv_add_locals >> simp[] >>
    match_mp_tac env_rel_append >> full_simp_tac(srw_ss())[] >>
    imp_res_tac env_rel_dom >>
    full_simp_tac(srw_ss())[env_rel_el,EL_MAP,UNCURRY] >>
    simp[Once v_rel_cases] >>
    srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][] >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.environment_component_equality] >>
    simp[compile_funs_map,MAP_EQ_f,FORALL_PROD] >>
    simp[UNION_COMM] >>
    map_every qexists_tac[`mods`,`tops`] >> simp[] >>
    qexists_tac`env''`>>full_simp_tac(srw_ss())[] >>
    full_simp_tac(srw_ss())[env_rel_el] >>
    full_simp_tac(srw_ss())[v_rel_eqns,SUBSET_DEF] >>
    srw_tac[][] >> res_tac >>
    full_simp_tac(srw_ss())[FLOOKUP_DEF] >>
    full_simp_tac(srw_ss())[MEM_MAP,EXISTS_PROD] >>
    metis_tac[ALOOKUP_FAILS,option_CASES,NOT_SOME_NONE] )
  >- (
    qpat_assum`_ = (_,r)`mp_tac >>
    BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] >> srw_tac[][] >> full_simp_tac(srw_ss())[] >- (
      rev_full_simp_tac(srw_ss())[] >>
      drule (CONJUNCT1 pmatch) >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      simp[GSYM CONJ_ASSOC] >>
      rator_x_assum`s_rel`mp_tac >>
      simp[Once s_rel_cases] >> strip_tac >>
      disch_then drule >>
      disch_then drule >>
      rator_x_assum`env_all_rel`mp_tac >>
      simp[Once env_all_rel_cases] >> strip_tac >>
      disch_then drule >> simp[] >> strip_tac >>
      qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm` >>
      Cases_on`mm`>>full_simp_tac(srw_ss())[match_result_rel_def] >>
      pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      ONCE_REWRITE_TAC[CONJ_COMM] >>
      first_x_assum match_mp_tac >>
      simp[s_rel_cases] >>
      simp[env_all_rel_cases] >>
      metis_tac[] ) >>
    rev_full_simp_tac(srw_ss())[] >>
    drule (CONJUNCT1 pmatch) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    simp[GSYM CONJ_ASSOC] >>
    rator_x_assum`s_rel`mp_tac >>
    simp[Once s_rel_cases] >> strip_tac >>
    disch_then drule >>
    disch_then drule >>
    rator_x_assum`env_all_rel`mp_tac >>
    simp[Once env_all_rel_cases] >> strip_tac >>
    disch_then drule >> simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`match_result_rel _ _ _ mm` >>
    Cases_on`mm`>>full_simp_tac(srw_ss())[match_result_rel_def] >>
    pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >>
    ONCE_REWRITE_TAC[CONJ_ASSOC] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    simp[drestrict_iter_list] >>
    simp[GSYM COMPL_UNION] >>
    first_x_assum match_mp_tac >>
    simp[s_rel_cases] >>
    simp[env_all_rel_cases] >>
    rveq >> full_simp_tac(srw_ss())[] >>
    imp_res_tac global_env_inv_add_locals >>
    full_simp_tac(srw_ss())[UNION_COMM] >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.environment_component_equality] >>
    srw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][] >>
    imp_res_tac pmatch_extend >> rveq >>
    qexists_tac`env''`>>simp[] >>
    simp[EXTENSION] >>
    imp_res_tac env_rel_dom >>
    simp[]));

val compile_exp_correct =
  compile_exp_correct'
    |> CONJUNCTS
    |> hd
    |> SIMP_RULE (srw_ss()) [AND_IMP_INTRO, PULL_FORALL]

val global_env_inv_flat_extend_lem = Q.prove (
  `!genv genv' env env_i1 x n v.
    env_rel genv' env env_i1 ∧
    ALOOKUP env x = SOME v ∧
    ALOOKUP (alloc_defs (LENGTH genv) (MAP FST env)) x = SOME n
    ⇒
    ?v_i1.
      EL n (genv ++ MAP SOME (MAP SND env_i1)) = SOME v_i1 ∧
      v_rel genv' v v_i1`,
  induct_on `env` >>
  srw_tac[][v_rel_eqns] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[alloc_defs_def] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[v_rel_eqns] >>
  srw_tac[][]
  >- metis_tac [EL_LENGTH_APPEND, NULL, HD]
  >- (FIRST_X_ASSUM (qspecl_then [`genv++[SOME v']`] mp_tac) >>
      srw_tac[][] >>
      metis_tac [APPEND, APPEND_ASSOC]));

val alookup_alloc_defs_bounds = Q.prove(
  `!next l x n.
    ALOOKUP (alloc_defs next l) x = SOME n
    ⇒
    next <= n ∧ n < next + LENGTH l`,
  induct_on `l` >>
  srw_tac[][alloc_defs_def]  >>
  res_tac >>
  DECIDE_TAC);

val global_env_inv_extend = Q.prove (
  `!genv mods tops menv env env' env_i1.
    ALL_DISTINCT (MAP FST env') ∧
    env_rel genv env' env_i1
    ⇒
    global_env_inv (genv++MAP SOME (MAP SND (REVERSE env_i1))) FEMPTY (tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP FST env'))) [] ∅ env'`,
  srw_tac[][v_rel_eqns] >>
  full_simp_tac(srw_ss())[flookup_fupdate_list, ALOOKUP_APPEND] >>
  every_case_tac >>
  srw_tac[][RIGHT_EXISTS_AND_THM]
  >- (imp_res_tac ALOOKUP_NONE >>
      full_simp_tac(srw_ss())[MAP_REVERSE, fst_alloc_defs] >>
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[MEM_MAP] >>
      metis_tac [pair_CASES, FST])
  >- metis_tac [ALL_DISTINCT_REVERSE, LENGTH_REVERSE, fst_alloc_defs, alookup_distinct_reverse,
                LENGTH_MAP, length_env_rel, alookup_alloc_defs_bounds]
  >- (match_mp_tac global_env_inv_flat_extend_lem >>
      MAP_EVERY qexists_tac [`(REVERSE env')`, `x`] >>
      srw_tac[][]
      >- metis_tac [env_rel_reverse, v_rel_weakening]
      >- metis_tac [alookup_distinct_reverse]
      >- metis_tac [alookup_distinct_reverse, MAP_REVERSE, fst_alloc_defs, ALL_DISTINCT_REVERSE]));

val letrec_global_env_lem2 = Q.prove (
  `!funs x genv n.
    ALL_DISTINCT (MAP FST funs) ∧
    n < LENGTH funs ∧
    ALOOKUP (REVERSE (alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))) (EL n (MAP FST funs)) = SOME x
    ⇒
    x = LENGTH funs + LENGTH genv - (n + 1)`,
  induct_on `funs` >>
  srw_tac[][alloc_defs_def] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[alloc_defs_append, ALOOKUP_APPEND, REVERSE_APPEND] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[alloc_defs_def] >>
  srw_tac[][] >>
  cases_on `n = 0` >>
  full_simp_tac (srw_ss()++ARITH_ss) [] >>
  `0 < n` by decide_tac >>
  full_simp_tac(srw_ss())[EL_CONS] >>
  `PRE n < LENGTH funs` by decide_tac >>
  res_tac >>
  srw_tac [ARITH_ss] [] >>
  full_simp_tac(srw_ss())[MEM_MAP, EL_MAP] >>
  LAST_X_ASSUM (qspecl_then [`EL (PRE n) funs`] mp_tac) >>
  srw_tac[][MEM_EL] >>
  metis_tac []);

val letrec_global_env_lem3 = Q.prove (
  `!funs x genv cenv tops mods.
    ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
    MEM x (MAP FST funs)
    ⇒
    ∃n y e'.
      FLOOKUP (FEMPTY |++ alloc_defs (LENGTH genv) (REVERSE (MAP FST funs))) x =
          SOME n ∧ n < LENGTH genv + LENGTH funs ∧
      find_recfun x funs = SOME (y,e') ∧
      EL n (genv ++ MAP (λ(p1,p1',p2).
                             SOME (Closure (cenv,[]) p1'
                                        (compile_exp mods ((tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP FST funs))) \\ p1') p2)))
                        (REVERSE funs)) =
        SOME (Closure (cenv,[]) y (compile_exp mods ((tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP FST funs))) \\ y) e'))`,
  srw_tac[][] >>
  full_simp_tac(srw_ss())[MEM_EL] >>
  srw_tac[][] >>
  MAP_EVERY qexists_tac [`LENGTH genv + LENGTH funs - (n + 1)`, `FST (SND (EL n funs))`, `SND (SND (EL n funs))`] >>
  srw_tac [ARITH_ss] [EL_APPEND2, flookup_fupdate_list]
  >- (every_case_tac >>
      srw_tac[][]
      >- (imp_res_tac ALOOKUP_NONE >>
          full_simp_tac(srw_ss())[MAP_REVERSE, fst_alloc_defs] >>
          full_simp_tac(srw_ss())[MEM_MAP, FST_triple] >>
          pop_assum mp_tac >>
          srw_tac[][EL_MAP] >>
          qexists_tac `EL n funs` >>
          srw_tac[][EL_MEM])
      >- metis_tac [FST_triple, letrec_global_env_lem2])
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
      srw_tac[][]));

val alookup_alloc_defs_bounds_rev = Q.prove(
  `!next l x n.
    ALOOKUP (REVERSE (alloc_defs next l)) x = SOME n
    ⇒
    next <= n ∧ n < next + LENGTH l`,
  induct_on `l` >>
  srw_tac[][alloc_defs_def]  >>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  DECIDE_TAC);

val letrec_global_env_lem = Q.prove (
  `!funs funs' (env:v environment) v x.
    ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs) x = SOME v ∧
    ALOOKUP (REVERSE (alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))) x = SOME x'
    ⇒
    v = SND (EL (LENGTH funs + LENGTH genv - (SUC x')) (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs))`,
  induct_on `funs` >>
  srw_tac[][alloc_defs_append] >>
  PairCases_on `h` >>
  full_simp_tac(srw_ss())[REVERSE_APPEND, alloc_defs_def, ALOOKUP_APPEND] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[] >>
  srw_tac [ARITH_ss] [arithmeticTheory.ADD1] >>
  res_tac >>
  srw_tac[][arithmeticTheory.ADD1] >>
  imp_res_tac alookup_alloc_defs_bounds_rev >>
  full_simp_tac(srw_ss())[] >>
  `LENGTH funs + LENGTH genv − x' = SUC (LENGTH funs + LENGTH genv − (x'+1))` by decide_tac >>
  srw_tac[][]);

val letrec_global_env = Q.prove (
  `!genv.
    ALL_DISTINCT (MAP (\(x,y,z). x) funs) ∧
    global_env_inv genv mods tops env.m {} env.v
    ⇒
    global_env_inv (genv ++ (MAP (λ(p1,p1',p2). SOME (Closure (env.c,[]) p1' p2))
                                 (compile_funs mods (tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))
                                                  (REVERSE funs))))
                 FEMPTY
                 (FEMPTY |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))
                 []
                 ∅
                 (build_rec_env funs env [])`,
  srw_tac[][evalPropsTheory.build_rec_env_merge] >>
  srw_tac[][v_rel_eqns, flookup_fupdate_list] >>
  every_case_tac >>
  srw_tac[][compile_funs_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, RIGHT_EXISTS_AND_THM]
  >- (imp_res_tac ALOOKUP_NONE >>
      full_simp_tac(srw_ss())[MAP_REVERSE, fst_alloc_defs] >>
      imp_res_tac ALOOKUP_MEM >>
      full_simp_tac(srw_ss())[MEM_MAP] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[LAMBDA_PROD, FORALL_PROD] >>
      PairCases_on `y` >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [])
  >- (imp_res_tac alookup_alloc_defs_bounds_rev >>
      full_simp_tac(srw_ss())[])
  >- (imp_res_tac letrec_global_env_lem >>
      imp_res_tac alookup_alloc_defs_bounds_rev >>
      srw_tac[][EL_APPEND2] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac [ARITH_ss] [EL_MAP, EL_REVERSE] >>
      `(PRE (LENGTH funs + LENGTH genv − x')) = (LENGTH funs + LENGTH genv − SUC x')` by decide_tac >>
      srw_tac[][] >>
      `?f x e. EL (LENGTH funs + LENGTH genv − SUC x') funs = (f,x,e)` by metis_tac [pair_CASES] >>
      srw_tac[][Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`mods`,
                             `tops`,
                             `e`,
                             `alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs))`] >>
      srw_tac[][]
      >- (full_simp_tac(srw_ss())[v_rel_eqns, SUBSET_DEF] >>
          srw_tac[][] >>
          `¬(ALOOKUP env.v x''' = NONE)` by metis_tac [ALOOKUP_NONE] >>
          cases_on `ALOOKUP env.v x'''` >>
          full_simp_tac(srw_ss())[] >>
          res_tac >>
          full_simp_tac(srw_ss())[FLOOKUP_DEF])
      >- metis_tac [v_rel_weakening]
      >- srw_tac[][MAP_REVERSE, fst_alloc_defs, FST_triple]
      >- (`LENGTH funs + LENGTH genv − SUC x' < LENGTH funs` by decide_tac >>
          metis_tac [find_recfun_el])
      >- metis_tac [letrec_global_env_lem3,FST_triple]))
  |> SIMP_RULE(srw_ss())[FUPDATE_LIST,FST_triple,compile_funs_map,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,
                         evalPropsTheory.build_rec_env_merge,MAP_REVERSE]

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
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[fupdate_list_foldl] >>
  srw_tac[][decs_to_dummy_env_def] >>
  res_tac >>
  srw_tac[][] >>
  imp_res_tac compile_dec_num_bindings >>
  srw_tac[][] >>
  decide_tac);

val pmatch_lem =
  pmatch
  |> CONJUNCTS
  |> hd
  |> SIMP_RULE (srw_ss()) []

val pmatch_evaluate_vars_lem =
  pmatch_evaluate_vars
  |> CONJUNCTS
  |> hd
  |> SIMP_RULE (srw_ss()) []

val compile_dec_correct = Q.prove (
  `!mn mods tops d env env_i1 s s' r s_i1 next' tops' d_i1 cenv'.
    r ≠ Rerr (Rabort Rtype_error) ∧
    funBigStep$evaluate_decs mn s env [d] = (s',cenv',r) ∧
    env.v = [] ∧
    global_env_inv s_i1.globals mods tops env.m {} env.v ∧
    env_all_rel s_i1.globals mods tops env env_i1 {} ∧
    s_rel s s_i1 ∧
    compile_dec (LENGTH s_i1.globals) mn mods tops d = (next',tops',d_i1)
    ⇒
    ?s'_i1 r_i1.
      evaluate_dec env_i1 s_i1 d_i1 = (s'_i1,r_i1) ∧
      (!env'.
        r = Rval env'
        ⇒
        ?env'_i1.
          r_i1 = Rval (cenv', MAP SND env'_i1) ∧
          next' = LENGTH (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) ∧
          env_rel (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) env' (REVERSE env'_i1) ∧
          s_rel s' s'_i1 ∧
          MAP FST env' = REVERSE (MAP FST tops') ∧
          global_env_inv (s_i1.globals ++ MAP SOME (MAP SND env'_i1)) FEMPTY (FEMPTY |++ tops') [] {} env') ∧
      (!err.
        r = Rerr err
        ⇒
        ?err_i1.
          r_i1 = Rerr err_i1 ∧
          result_rel (\a b c. T) s_i1.globals (Rerr err) (Rerr err_i1) ∧
          s_rel s' s'_i1)`,
  Cases_on `d` >>
  rw [funBigStepTheory.evaluate_decs_def, compile_dec_def] >>
  fs [] >>
  rw []
  >- (
    every_case_tac >>
    fs [] >>
    rw [] >>
    imp_res_tac compile_exp_correct >>
    fs [] >>
    rfs [result_rel_cases, compile_exp_def, DRESTRICT_UNIV] >>
    rw [modSemTheory.evaluate_dec_def] >>
    `env_i1 with v := [] = env_i1` by (
      rfs [env_all_rel_cases, environment_component_equality,
          env_rel_list_rel] >>
      fs []) >>
    fs [] >>
    simp [modSemTheory.evaluate_def] >>
    imp_res_tac evaluate_globals >>
    `?r'. v' = [r']` by metis_tac [evaluate_sing] >>
    fs [] >>
    `a = [] ∨ ?r t. a = r::t` by metis_tac [list_CASES] >>
    fs [vs_rel_list_rel] >>
    imp_res_tac evaluate_sing >>
    fs [s_rel_cases, env_all_rel_cases] >>
    rw [] >>
    `match_result_rel s'_i1.globals [] (pmatch env'.c q.refs p r ([]++[]))
           (pmatch env'.c s'_i1.refs p r' [])` by (
      match_mp_tac pmatch_lem >>
      simp [env_rel_list_rel] >>
      NO_TAC) >>
    fs [] >>
    Cases_on `pmatch env'.c s'_i1.refs p r' []` >>
    rfs [match_result_rel_def, env_rel_list_rel, Bindv_def]
    >- rw [v_rel_eqns] >>
    simp [do_con_check_def] >>
    qmatch_assum_abbrev_tac `_ = Match bind_i1` >>
    `evaluate (env_i1 with v := bind_i1) s'_i1 (MAP Var_local (pat_bindings p (MAP FST env_i1.v))) =
        (s'_i1,Rval (MAP SND bind_i1))` by (
      match_mp_tac pmatch_evaluate_vars_lem >>
      simp [] >>
      qexists_tac `r'` >>
      simp []) >>
    rfs [MAP_REVERSE] >>
    simp [build_conv_def] >>
    imp_res_tac evaluate_length >>
    fs [] >>
    qexists_tac `REVERSE bind_i1` >>
    simp [MAP_REVERSE, fst_alloc_defs] >>
    imp_res_tac pmatch_extend >>
    fs [] >>
    qmatch_assum_abbrev_tac `LIST_REL _ bind env'''` >>
    `MAP FST bind = MAP FST bind_i1` by (
      metis_tac [env_rel_dom, env_rel_list_rel]) >>
    rw []
    >- metis_tac [v_rel_weakening, env_rel_list_rel] >>
    pop_assum (mp_tac o GSYM) >>
    pop_assum mp_tac >>
    pop_assum (mp_tac o GSYM) >>
    rw [] >>
    match_mp_tac (SIMP_RULE (srw_ss()) [ MAP_REVERSE] global_env_inv_extend) >>
    metis_tac [env_rel_list_rel])
  >- (
    simp [evaluate_dec_def, fupdate_list_foldl] >>
    qpat_abbrev_tac `tops' = (tops |++ X)` >>
    qexists_tac `MAP (λ(f,x,e). (f, Closure (env.c,[]) x e)) (compile_funs mods tops' (REVERSE l))` >>
    simp [compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,fst_alloc_defs,
          evalPropsTheory.build_rec_env_merge,MAP_REVERSE,ETA_AX] >>
    conj_tac
    >- fs [env_all_rel_cases] >>
    conj_tac
    >- (
      simp [env_rel_el,EL_MAP,UNCURRY] >>
      fs [env_all_rel_cases] >>
      rw [] >>
      simp [Once v_rel_cases] >>
      MAP_EVERY qexists_tac [`mods`, `tops`, `SND(SND(EL n l))`,
                             `alloc_defs (LENGTH s_i1.globals) (REVERSE (MAP FST l))`] >>
      srw_tac[][] >>
      UNABBREV_ALL_TAC >>
      srw_tac[][SUBSET_DEF, FDOM_FUPDATE_LIST, FUPDATE_LIST_THM]
      >- (
        full_simp_tac(srw_ss())[v_rel_eqns] >>
        `~(ALOOKUP env'' x = NONE)` by metis_tac [ALOOKUP_NONE] >>
         cases_on `ALOOKUP env'' x` >>
        full_simp_tac(srw_ss())[] >>
        res_tac >>
        full_simp_tac(srw_ss())[FLOOKUP_DEF])
      >-  metis_tac [v_rel_weakening]
      >- srw_tac[][MAP_REVERSE, fst_alloc_defs, FST_triple]
      >- metis_tac [find_recfun_el,SND,PAIR]
      >- (simp[LAMBDA_PROD] >> metis_tac [MAP_REVERSE, letrec_global_env_lem3])) >>
    unabbrev_all_tac >>
    metis_tac [FST_triple, FUPDATE_LIST, letrec_global_env])
  >- (
    simp [evaluate_dec_def, fupdate_list_foldl] >>
    rw [env_rel_list_rel]
    >- fs [s_rel_cases]
    >- fs [v_rel_eqns]
    >- rfs [s_rel_cases])
  >- (
    simp [evaluate_dec_def, PULL_EXISTS, type_defs_to_new_tdecs_def, build_tdefs_def, 
          check_dup_ctors_def, env_rel_list_rel] >>
    fs [s_rel_cases, v_rel_eqns])
  >- (
    rw [evaluate_dec_def, env_rel_list_rel]
    >- (rfs [s_rel_cases] >> fs [])
    >- (fs [s_rel_cases] >> simp [EXTENSION])
    >- simp [v_rel_eqns]));

    (*
val compile_decs_correct = Q.prove (
  `!ck mn mods tops ds menv cenv env s s' r genv s_i1 tdecs s'_i1 tdecs' next' tops' ds_i1 cenv'.
    r ≠ Rerr (Rabort Rtype_error) ∧
    evaluate_decs ck mn env s ds (s',cenv',r) ∧
    global_env_inv genv mods tops env.m {} env.v ∧
    s_rel genv s s_i1 ∧
    compile_decs (LENGTH genv) mn mods tops ds = (next',tops',ds_i1)
    ⇒
    ∃s'_i1 new_genv new_genv' new_env' r_i1.
     new_genv' = MAP SND new_genv ∧
     evaluate_decs ck genv env.c (s_i1,s.defined_types) ds_i1 ((s'_i1,s'.defined_types),cenv',new_genv',r_i1) ∧
     s_rel (genv ++ MAP SOME new_genv') s' s'_i1 ∧
     (!new_env.
       r = Rval new_env
       ⇒
       r_i1 = NONE ∧
       next' = LENGTH (genv ++ MAP SOME new_genv') ∧
       env_rel (genv ++ MAP SOME new_genv') new_env (REVERSE new_genv) ∧
       MAP FST new_env = REVERSE (MAP FST tops') ∧
       global_env_inv (genv ++ MAP SOME new_genv') FEMPTY (FEMPTY |++ tops') [] {} new_env) ∧
     (!err.
       r = Rerr err
       ⇒
       ?err_i1 new_env.
         r_i1 = SOME err_i1 ∧
         next' ≥ LENGTH (genv++MAP SOME new_genv') ∧
         result_rel (\a b c. T) (genv ++ MAP SOME new_genv') (Rerr err) (Rerr err_i1))`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def] >>
  rator_x_assum `bigStep$evaluate_decs` (mp_tac o SIMP_RULE (srw_ss()) [Once bigStepTheory.evaluate_decs_cases]) >>
  srw_tac[][Once modSemTheory.evaluate_decs_cases, FUPDATE_LIST, result_rel_eqns]
  >- srw_tac[][v_rel_eqns]
  >- srw_tac[][v_rel_eqns] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
  imp_res_tac compile_dec_correct >> rev_full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[result_rel_eqns] >>
  `?envC' env'. v' = (envC',env')` by metis_tac [pair_CASES] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[fupdate_list_foldl] >>
  srw_tac[][]
  >- (full_simp_tac(srw_ss())[result_rel_cases] >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[] >>
      simp[PULL_EXISTS] >>
      srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
      first_assum(match_exists_tac o concl)  >> simp[] >>
      imp_res_tac compile_dec_num_bindings >>
      imp_res_tac compile_decs_num_bindings >>
      decide_tac)
  >- (
     first_x_assum(fn th => first_x_assum(mp_tac o
       MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](ONCE_REWRITE_RULE[CONJ_COMM]th)))) >>
     simp[Ntimes extend_dec_env_def 2] >>
     simp[Once AND_IMP_INTRO] >>
     ONCE_REWRITE_TAC[CONJ_COMM,CONJ_ASSOC] >>
     simp[GSYM AND_IMP_INTRO] >>
     disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >>
     simp[Once AND_IMP_INTRO] >>
     ONCE_REWRITE_TAC[CONJ_COMM,CONJ_ASSOC] >>
     simp[GSYM AND_IMP_INTRO] >>
     disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >>
     discharge_hyps >- (
       match_mp_tac (GEN_ALL global_env_inv_extend2) >> simp[] >>
       metis_tac[v_rel_weakening] ) >>
     discharge_hyps >- (
       rpt strip_tac >> full_simp_tac(srw_ss())[combine_dec_result_def] ) >>
     strip_tac >>
     srw_tac[boolSimps.DNF_ss][] >> disj2_tac >>
     CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``modSem$evaluate_dec`` o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     full_simp_tac(srw_ss())[extend_dec_env_def] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     rator_x_assum`s_rel`mp_tac >>
     REWRITE_TAC[GSYM MAP_APPEND,GSYM APPEND_ASSOC] >> strip_tac >>
     CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``s_rel`` o fst o strip_comb))) >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     Cases_on`r'`>>full_simp_tac(srw_ss())[combine_dec_result_def] >>
     conj_tac >- (
       simp[REVERSE_APPEND] >>
       match_mp_tac env_rel_append >>
       simp[] >>
       metis_tac[v_rel_weakening] ) >>
     simp[GSYM FUPDATE_LIST,FUPDATE_LIST_APPEND] >>
     match_mp_tac global_env_inv_extend2 >>
     simp[] >>
     metis_tac[v_rel_weakening]));

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

val prompt_mods_ok = Q.prove (
  `!l mn mods tops ds l' tops' ds_i1.
    compile_decs l (SOME mn) mods tops ds = (l',tops',ds_i1)
    ⇒
    prompt_mods_ok (SOME mn) ds_i1`,
  induct_on `ds` >>
  srw_tac[][LET_THM, compile_decs_def, prompt_mods_ok_def] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[prompt_mods_ok_def] >>
  `?x y z. compile_dec l (SOME mn) mods tops h = (x,y,z)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  `?x' y' z'. (compile_decs x (SOME mn) mods (FOLDL (λenv (k,v). env |+ (k,v)) tops y) ds) = (x',y',z')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][]
  >- (every_case_tac >>
      full_simp_tac(srw_ss())[compile_dec_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LET_THM])
  >- metis_tac []);

val no_dup_types_helper = Q.prove (
  `!next mn menv env ds next' menv' ds_i1.
    compile_decs next mn menv env ds = (next',menv',ds_i1) ⇒
    FLAT (MAP (\d. case d of Dtype tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds)
    =
    FLAT (MAP (\d. case d of Dtype mn tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds_i1)`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def] >>
  srw_tac[][] >>
  `?next1 new_env1 d'. compile_dec next mn menv env h = (next1,new_env1,d')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  `?next2 new_env2 ds'. (compile_decs next1 mn menv (FOLDL (λenv (k,v). env |+ (k,v)) env new_env1) ds) = (next2,new_env2,ds')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  every_case_tac >>
  full_simp_tac(srw_ss())[compile_dec_def, LET_THM] >>
  srw_tac[][] >>
  metis_tac []);

val no_dup_types = Q.prove(
  `!next mn menv env ds next' menv' ds_i1.
    compile_decs next mn menv env ds = (next',menv',ds_i1) ∧
    no_dup_types ds
    ⇒
    no_dup_types ds_i1`,
  induct_on `ds` >>
  srw_tac[][compile_decs_def]
  >- full_simp_tac(srw_ss())[semanticPrimitivesTheory.no_dup_types_def, modSemTheory.no_dup_types_def, modSemTheory.decs_to_types_def] >>
  `?next1 new_env1 d'. compile_dec next mn menv env h = (next1,new_env1,d')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[LET_THM] >>
  `?next2 new_env2 ds'. (compile_decs next1 mn menv (FOLDL (λenv (k,v). env |+ (k,v)) env new_env1) ds) = (next2,new_env2,ds')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  res_tac >>
  cases_on `h` >>
  full_simp_tac(srw_ss())[compile_dec_def, LET_THM] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.decs_to_types_def, semanticPrimitivesTheory.no_dup_types_def,
      modSemTheory.decs_to_types_def, modSemTheory.no_dup_types_def, ALL_DISTINCT_APPEND] >>
  srw_tac[][] >>
  metis_tac [no_dup_types_helper]);

val compile_top_correct = Q.store_thm ("compile_top_correct",
  `!mods tops t ck env s s' r genv s_i1 next' tops' mods' prompt_i1 cenv'.
    r ≠ Rerr (Rabort Rtype_error) ∧
    invariant genv mods tops env.m env.v s s_i1 s.defined_mods ∧
    evaluate_top ck env s t (s',cenv',r) ∧
    compile_top (LENGTH genv) mods tops t = (next',mods',tops',prompt_i1)
    ⇒
    ∃s'_i1 new_genv r_i1.
     evaluate_prompt ck genv env.c (s_i1,s.defined_types,s.defined_mods) prompt_i1 ((s'_i1,s'.defined_types,s'.defined_mods),cenv',new_genv,r_i1) ∧
     next' = LENGTH  (genv ++ new_genv) ∧
     (!new_menv new_env.
       r = Rval (new_menv, new_env)
       ⇒
       r_i1 = NONE ∧
       invariant (genv ++ new_genv) mods' tops' (new_menv++env.m) (new_env++env.v) s' s'_i1 s'.defined_mods) ∧
     (!err.
       r = Rerr err
       ⇒
       ?err_i1.
         r_i1 = SOME err_i1 ∧
         result_rel (\a b c. T) (genv ++ new_genv) (Rerr err) (Rerr err_i1) ∧
         invariant (genv ++ new_genv) mods' tops env.m env.v s' s'_i1 s'.defined_mods)`,
  srw_tac[][bigStepTheory.evaluate_top_cases, evaluate_prompt_cases, compile_top_def, LET_THM, invariant_def] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][]
  >- (first_assum(split_applied_pair_tac o lhs o concl) >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      imp_res_tac compile_dec_correct >>
      full_simp_tac(srw_ss())[result_rel_cases] >>
      full_simp_tac(srw_ss())[fupdate_list_foldl] >>
      srw_tac[][PULL_EXISTS] >>
      srw_tac[][Once modSemTheory.evaluate_decs_cases] >>
      srw_tac[][Once modSemTheory.evaluate_decs_cases] >>
      srw_tac[][mod_cenv_def,update_mod_state_def] >>
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``modSem$evaluate_dec`` o fst o strip_comb))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[GSYM CONJ_ASSOC] >>
      conj_tac >- (
        imp_res_tac eval_d_no_new_mods >>
        full_simp_tac(srw_ss())[]) >>
      conj_tac >- metis_tac[global_env_inv_extend2, v_rel_weakening] >>
      imp_res_tac eval_d_no_new_mods >>
      full_simp_tac(srw_ss())[] >>
      simp[prompt_mods_ok_def, modSemTheory.no_dup_types_def,decs_to_types_def] >>
      full_simp_tac(srw_ss())[modSemTheory.evaluate_dec_cases] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[compile_dec_def,LET_THM] >- (
        full_simp_tac(srw_ss())[bigStepTheory.evaluate_dec_cases] >> rev_full_simp_tac(srw_ss())[] ) >>
      every_case_tac >> full_simp_tac(srw_ss())[])
  >- (first_assum(split_applied_pair_tac o lhs o concl) >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      imp_res_tac compile_dec_correct >>
      pop_assum mp_tac >>
      srw_tac[][] >>
      srw_tac[][mod_cenv_def,update_mod_state_def] >>
      srw_tac[boolSimps.DNF_ss][] >>
      simp[Once evaluate_decs_cases] >>
      simp[Once evaluate_decs_cases] >>
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``modSem$evaluate_dec`` o fst o strip_comb))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[GSYM CONJ_ASSOC] >>
      imp_res_tac compile_dec_num_bindings >>
      simp[decs_to_dummy_env_def] >>
      conj_tac >- (
        full_simp_tac(srw_ss())[result_rel_cases] >>
        metis_tac[v_rel_weakening] ) >>
      conj_tac >- (
        imp_res_tac eval_d_no_new_mods >>
        full_simp_tac(srw_ss())[]) >>
      conj_tac >- metis_tac[v_rel_weakening] >>
      conj_tac >- (
        full_simp_tac(srw_ss())[s_rel_cases] >>
        metis_tac[sv_rel_weakening, LIST_REL_mono]) >>
      imp_res_tac eval_d_no_new_mods >>
      full_simp_tac(srw_ss())[]>>
      simp[prompt_mods_ok_def, no_dup_types_def, decs_to_types_def] >>
      full_simp_tac(srw_ss())[modSemTheory.evaluate_dec_cases] )
  >- (first_assum(split_applied_pair_tac o lhs o concl) >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      imp_res_tac compile_decs_correct >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][mod_cenv_def] >>
      simp[PULL_EXISTS] >>
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``modSem$evaluate_decs`` o fst o strip_comb))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[fupdate_list_foldl,update_mod_state_def] >>
      simp[GSYM CONJ_ASSOC] >>
      conj_tac >- (
        imp_res_tac eval_ds_no_new_mods >>
        full_simp_tac(srw_ss())[SUBSET_DEF]) >>
      conj_tac >- metis_tac[global_env_inv_extend_mod] >>
      conj_tac >- (
        full_simp_tac(srw_ss())[s_rel_cases] >>
        metis_tac [sv_rel_weakening, LIST_REL_mono]) >>
      conj_tac >- metis_tac[prompt_mods_ok] >>
      conj_tac >- metis_tac [no_dup_types] >>
      imp_res_tac eval_ds_no_new_mods >>
      full_simp_tac(srw_ss())[])
  >- (first_assum(split_applied_pair_tac o lhs o concl) >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      imp_res_tac compile_decs_correct >>
      pop_assum mp_tac >>
      srw_tac[][mod_cenv_def,update_mod_state_def] >>
      srw_tac[boolSimps.DNF_ss][] >>
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``modSem$evaluate_decs`` o fst o strip_comb))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      imp_res_tac compile_decs_num_bindings >>
      simp[GSYM CONJ_ASSOC] >>
      conj_tac >- (
        full_simp_tac(srw_ss())[result_rel_cases] >>
        metis_tac[v_rel_weakening] ) >>
      conj_tac >- (
        imp_res_tac eval_ds_no_new_mods >>
        full_simp_tac(srw_ss())[SUBSET_DEF]) >>
      conj_tac >- (
        simp[fupdate_list_foldl] >>
        match_mp_tac global_env_inv_extend_mod_err >>
        simp [] >>
        full_simp_tac(srw_ss())[SUBSET_DEF] >>
        metis_tac []) >>
      conj_tac >- (
        full_simp_tac(srw_ss())[s_rel_cases] >>
        metis_tac [sv_rel_weakening, LIST_REL_mono]) >>
      conj_tac >- metis_tac[prompt_mods_ok] >>
      conj_tac >- metis_tac[no_dup_types] >>
      imp_res_tac eval_ds_no_new_mods >>
      full_simp_tac(srw_ss())[]));

val compile_prog_correct = Q.store_thm ("compile_prog_correct",
  `!mods tops ck env s prog s' r genv s_i1 next' tops' mods'  cenv' prog_i1.
    r ≠ Rerr (Rabort Rtype_error) ∧
    evaluate_prog ck env s prog (s',cenv',r) ∧
    invariant genv mods tops env.m env.v s s_i1 s.defined_mods ∧
    compile_prog (LENGTH genv) mods tops prog = (next',mods',tops',prog_i1)
    ⇒
    ∃s'_i1 new_genv r_i1.
     evaluate_prog ck genv env.c (s_i1,s.defined_types,s.defined_mods) prog_i1 ((s'_i1,s'.defined_types,s'.defined_mods),cenv',new_genv,r_i1) ∧
     (!new_menv new_env.
       r = Rval (new_menv, new_env)
       ⇒
       next' = LENGTH (genv ++ new_genv) ∧
       r_i1 = NONE ∧
       invariant (genv ++ new_genv) mods' tops' (new_menv++env.m) (new_env++env.v) s' s'_i1 s'.defined_mods) ∧
     (!err.
       r = Rerr err
       ⇒
       ?err_i1.
         r_i1 = SOME err_i1 ∧
         result_rel (\a b c. T) (genv ++ new_genv) r (Rerr err_i1))`,
  induct_on `prog` >>
  srw_tac[][LET_THM, compile_prog_def]
  >- full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_prog_cases, Once modSemTheory.evaluate_prog_cases] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  rator_x_assum `bigStep$evaluate_prog` (mp_tac o SIMP_RULE (srw_ss()) [Once bigStepTheory.evaluate_prog_cases]) >>
  srw_tac[][] >>
  srw_tac[][Once modSemTheory.evaluate_prog_cases] >>
  srw_tac[][]
  >- (
    first_x_assum(
      mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO](ONCE_REWRITE_RULE[CONJ_COMM]compile_top_correct))) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >> strip_tac >>
    first_x_assum(fn th => first_x_assum(
      mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO](ONCE_REWRITE_RULE[CONJ_COMM]th)))) >>
    simp[extend_top_env_def] >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> full_simp_tac(srw_ss())[] >>
    discharge_hyps >- (Cases_on `r'` >> full_simp_tac(srw_ss())[combine_mod_result_def]) >>
    srw_tac[boolSimps.DNF_ss][] >> disj1_tac >>
    CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``modSem$evaluate_prog`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    cases_on `r'` >> full_simp_tac(srw_ss())[combine_mod_result_def] >>
    Cases_on`a`>>full_simp_tac(srw_ss())[] >> simp[] )
  >- (imp_res_tac compile_top_correct >>
      pop_assum mp_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[result_rel_cases] >>
      srw_tac[][] >>
      metis_tac [v_rel_weakening, APPEND_ASSOC, LENGTH_APPEND]));

val compile_prog_mods = Q.prove (
  `!l mods tops prog l' mods' tops' prog_i1.
    compile_prog l mods tops prog = (l',mods', tops',prog_i1)
    ⇒
    prog_to_mods prog
    =
    prog_to_mods prog_i1`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM, modSemTheory.prog_to_mods_def, semanticPrimitivesTheory.prog_to_mods_def] >>
  srw_tac[][] >>
  `?w x y z. compile_top l mods tops h = (w,x,y,z)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  `?w' x' y' z'. compile_prog w x y prog = (w',x',y',z')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[compile_top_def] >>
  every_case_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[LET_THM]
  >- (`?a b c. compile_decs l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[])
  >- (`?a b c. compile_decs l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[])
  >- (`?a b c. compile_decs l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[semanticPrimitivesTheory.prog_to_mods_def, modSemTheory.prog_to_mods_def] >>
      metis_tac [])
  >- (full_simp_tac(srw_ss())[semanticPrimitivesTheory.prog_to_mods_def, modSemTheory.prog_to_mods_def] >>
      metis_tac [])
  >- (`?a b c. compile_dec l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[]));

val compile_prog_top_types = Q.prove (
  `!l mods tops prog l' mods' tops' prog_i1.
    compile_prog l mods tops prog = (l',mods', tops',prog_i1)
    ⇒
    prog_to_top_types prog
    =
    prog_to_top_types prog_i1`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM] >>
  srw_tac[][] >>
  `?w x y z. compile_top l mods tops h = (w,x,y,z)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.prog_to_top_types_def, modSemTheory.prog_to_top_types_def] >>
  `?w' x' y' z'. compile_prog w x y prog = (w',x',y',z')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[compile_top_def] >>
  every_case_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[LET_THM]
  >- (`?a b c. compile_decs l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[])
  >- (`?a b c. compile_decs l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      metis_tac [])
  >- (`?a b c. compile_dec l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      res_tac >>
      srw_tac[][] >>
      full_simp_tac(srw_ss())[compile_dec_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LET_THM] >>
      srw_tac[][semanticPrimitivesTheory.decs_to_types_def, modSemTheory.decs_to_types_def])
  >- (`?a b c. compile_dec l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][]));

val compile_prog_mods_ok = Q.prove (
  `!l mods tops prog l' mods' tops' prog_i1.
    compile_prog l mods tops prog = (l',mods', tops',prog_i1)
    ⇒
    EVERY (λp. case p of Prompt mn ds => prompt_mods_ok mn ds) prog_i1`,
  induct_on `prog` >>
  srw_tac[][compile_prog_def, LET_THM] >>
  srw_tac[][] >>
  `?w x y z. compile_top l mods tops h = (w,x,y,z)` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  `?w' x' y' z'. compile_prog w x y prog = (w',x',y',z')` by metis_tac [pair_CASES] >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[compile_top_def] >>
  every_case_tac >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[LET_THM]
  >- (`?a b c. compile_decs l (SOME s) mods tops l''' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      metis_tac [prompt_mods_ok])
  >- (`?a b c. compile_dec l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][prompt_mods_ok_def] >>
      full_simp_tac(srw_ss())[compile_dec_def] >>
      every_case_tac >>
      full_simp_tac(srw_ss())[LET_THM])
  >- (`?a b c. compile_decs l (SOME s) mods tops l''' = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      srw_tac[][] >>
      metis_tac [prompt_mods_ok])
  >- (`?a b c. compile_dec l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
      full_simp_tac(srw_ss())[] >>
      metis_tac []));

val whole_compile_prog_correct = Q.store_thm ("whole_compile_prog_correct",
  `!mods tops ck env s prog s' r genv s_i1 next' tops' mods'  cenv' prog_i1.
    r ≠ Rerr (Rabort Rtype_error) ∧
    evaluate_whole_prog ck env s prog (s',cenv',r) ∧
    invariant genv mods tops env.m env.v s s_i1 s.defined_mods ∧
    compile_prog (LENGTH genv) mods tops prog = (next',mods',tops',prog_i1)
    ⇒
    ∃s'_i1 new_genv r_i1.
     evaluate_whole_prog ck genv env.c (s_i1,s.defined_types,s.defined_mods) prog_i1 ((s'_i1,s'.defined_types,s'.defined_mods),cenv',new_genv,r_i1) ∧
     (!new_menv new_env.
       r = Rval (new_menv, new_env)
       ⇒
       next' = LENGTH (genv ++ new_genv) ∧
       r_i1 = NONE ∧
       invariant (genv ++ new_genv) mods' tops' (new_menv++env.m) (new_env++env.v) s' s'_i1 s'.defined_mods) ∧
     (!err.
       r = Rerr err
       ⇒
       ?err_i1.
         r_i1 = SOME err_i1 ∧
         result_rel (\a b c. T) (genv ++ new_genv) r (Rerr err_i1))`,
  srw_tac[][modSemTheory.evaluate_whole_prog_def, bigStepTheory.evaluate_whole_prog_def] >>
  every_case_tac
  >- (imp_res_tac compile_prog_correct >>
      full_simp_tac(srw_ss())[] >>
      cases_on `r` >>
      full_simp_tac(srw_ss())[] >>
      first_assum(match_exists_tac o concl) >> simp[]) >>
  srw_tac[][result_rel_cases] >>
  CCONTR_TAC >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.no_dup_mods_def, modSemTheory.no_dup_mods_def,
      semanticPrimitivesTheory.no_dup_top_types_def, modSemTheory.no_dup_top_types_def] >>
  metis_tac [compile_prog_mods, compile_prog_top_types, compile_prog_mods_ok, NOT_EVERY]);

*)

open semanticsTheory funBigStepEquivTheory

val precondition_def = Define`
  precondition s1 env1 c s2 env2 ⇔
    invariant (FST c.mod_env) (SND c.mod_env)
      env1.m env1.v s1 s2
      s1.defined_mods ∧
    s2.defined_mods = s1.defined_mods ∧
    s2.defined_types = s1.defined_types ∧
    env2.c = env1.c ∧
    c.next_global = LENGTH s2.globals`;

val compile_correct = Q.store_thm("compile_correct",
  `precondition s1 env1 c s2 env2 ⇒
   ¬semantics_prog s1 env1 prog Fail ⇒
   semantics_prog s1 env1 prog (semantics env2 s2 (SND (compile c prog)))`,
  (*
  `∃genv cenv st tids mods. s2 = (genv,cenv,st,tids,mods)` by metis_tac[PAIR] >>
  srw_tac[][precondition_def,compile_def] >>
  Cases_on`∃k ffi r.
            evaluate_prog_with_clock s1 k prog = (ffi,r) ∧
            r ≠ Rerr (Rabort Rtimeout_error)` >> full_simp_tac(srw_ss())[] >- (
    full_simp_tac(srw_ss())[semanticsTheory.evaluate_prog_with_clock_def,LET_THM] >>
    first_assum(split_applied_pair_tac o lhs o concl) >> full_simp_tac(srw_ss())[] >>
    imp_res_tac functional_evaluate_prog >>
    (whole_compile_prog_correct
     |> ONCE_REWRITE_RULE[CONJ_COMM]
     |> REWRITE_RULE[GSYM AND_IMP_INTRO]
     |> (fn th => first_x_assum(mp_tac o MATCH_MP th))) >>
    simp[] >>
    imp_res_tac invariant_change_clock >>
    pop_assum(qspec_then`k`strip_assume_tac) >>
    disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[] >>
    discharge_hyps_keep >- (
      full_simp_tac(srw_ss())[semantics_prog_def] >>
      first_x_assum(qspec_then`k`mp_tac) >>
      simp[evaluate_prog_with_clock_def] ) >>
    strip_tac >>
    srw_tac[][modSemTheory.semantics_def] >- (
      full_simp_tac(srw_ss())[modSemTheory.evaluate_prog_with_clock_def] >>
      cheat (* need determinism of modSem$evaluate_whole_prog *) ) >>
    DEEP_INTRO_TAC some_intro >>
    simp[modSemTheory.evaluate_prog_with_clock_def,PULL_EXISTS] >>
    conj_tac >- (
      srw_tac[][] >>
      simp[semanticsTheory.semantics_prog_def] >>
      simp[semanticsTheory.evaluate_prog_with_clock_def] >>
      qexists_tac`k`>>simp[] >>
      cheat ) >>
    srw_tac[][semantics_prog_def] >>
    cheat ) >>
    *)
  cheat);

val _ = export_theory ();
