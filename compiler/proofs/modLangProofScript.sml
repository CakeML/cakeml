open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open libTheory astTheory semanticPrimitivesTheory bigStepTheory terminationTheory;
open bigClockTheory;
open modLangTheory;
open evalPropsTheory;
open compilerTerminationTheory;

val _ = new_theory "modLangProof";

val find_recfun_thm = Q.prove (
`!n funs f x e.
  (find_recfun n [] = NONE) ∧
  (find_recfun n ((f,x,e)::funs) =
    if f = n then SOME (x,e) else find_recfun n funs)`,
rw [] >>
rw [Once find_recfun_def]);

val find_recfun_lookup = Q.store_thm ("find_recfun_lookup",
`!n funs. find_recfun n funs = ALOOKUP funs n`,
 induct_on `funs` >>
 rw [find_recfun_thm] >>
 PairCases_on `h` >>
 rw [find_recfun_thm]);

val pat_bindings_accum = Q.store_thm ("pat_bindings_accum",
`(!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc)`,
 Induct >>
 rw []
 >- rw [pat_bindings_def]
 >- rw [pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]
 >- rw [pat_bindings_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_def]);

val pmatch_extend = Q.prove (
`(!cenv s p v env env' env''.
  pmatch cenv s p v env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p []) ∧
 (!cenv s ps vs env env' env''.
  pmatch_list cenv s ps vs env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps [])`,
 ho_match_mp_tac pmatch_ind >>
 rw [pat_bindings_def, pmatch_def] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 qexists_tac `env'''++env''` >>
 rw [] >>
 metis_tac [pat_bindings_accum]);

val pmatch_i1_extend = Q.prove (
`(!cenv s p v env env' env''.
  pmatch_i1 cenv s p v env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pat_bindings p []) ∧
 (!cenv s ps vs env env' env''.
  pmatch_list_i1 cenv s ps vs env = Match env'
  ⇒
  ?env''. env' = env'' ++ env ∧ MAP FST env'' = pats_bindings ps [])`,
 ho_match_mp_tac pmatch_i1_ind >>
 rw [pat_bindings_def, pmatch_i1_def] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 qexists_tac `env'''++env''` >>
 rw [] >>
 metis_tac [pat_bindings_accum]);

val (v_to_i1_rules, v_to_i1_ind, v_to_i1_cases) = Hol_reln `
(!genv lit.
  v_to_i1 genv (Litv lit) (Litv_i1 lit)) ∧
(!genv cn vs vs'.
  vs_to_i1 genv vs vs'
  ⇒
  v_to_i1 genv (Conv cn vs) (Conv_i1 cn vs')) ∧
(!genv mods tops menv cenv env x e env' env_i1.
  env_to_i1 genv env env_i1 ∧
  set (MAP FST env') DIFF set (MAP FST env) ⊆ FDOM tops ∧
  global_env_inv genv mods tops menv (set (MAP FST env_i1)) env'
  ⇒
  v_to_i1 genv (Closure (menv,cenv,env++env') x e)
               (Closure_i1 (cenv, env_i1) x (exp_to_i1 mods (DRESTRICT tops (COMPL (set (MAP FST env_i1))) \\ x) e))) ∧
(* For expression level let recs *)
(!genv mods tops menv cenv env funs x env' env_i1.
  env_to_i1 genv env env_i1 ∧
  set (MAP FST env') DIFF set (MAP FST env) ⊆ FDOM tops ∧
  global_env_inv genv mods tops menv (set (MAP FST env_i1)) env'
  ⇒
  v_to_i1 genv (Recclosure (menv,cenv,env++env') funs x)
               (Recclosure_i1 (cenv,env_i1) (funs_to_i1 mods (DRESTRICT tops (COMPL (set (MAP FST env_i1) ∪ set (MAP FST funs)))) funs) x)) ∧
(* For top-level let recs *)
(!genv mods tops menv cenv env funs x y e tops'.
  set (MAP FST env) ⊆ FDOM tops ∧
  global_env_inv genv mods tops menv {} env ∧
  MAP FST (REVERSE tops') = MAP FST funs ∧
  find_recfun x funs = SOME (y,e) ∧
  (* A syntactic way of relating the recursive function environment, rather
   * than saying that they build v_to_i1 related environments, which looks to
   * require step-indexing *)
  (!x. x ∈ set (MAP FST funs) ⇒
       ?n y e.
         FLOOKUP (FEMPTY |++ tops') x = SOME n ∧
         n < LENGTH genv ∧
         find_recfun x funs = SOME (y,e) ∧
         EL n genv = SOME (Closure_i1 (cenv,[]) y (exp_to_i1 mods ((tops |++ tops') \\ y) e)))
  ⇒
  v_to_i1 genv (Recclosure (menv,cenv,env) funs x)
               (Closure_i1 (cenv,[]) y (exp_to_i1 mods ((tops |++ tops') \\ y) e))) ∧
(!genv loc.
  v_to_i1 genv (Loc loc) (Loc_i1 loc)) ∧
(!vs.
  vs_to_i1 genv vs vs_i1
  ⇒
  v_to_i1 genv (Vectorv vs) (Vectorv_i1 vs_i1)) ∧
(!genv.
  vs_to_i1 genv [] []) ∧
(!genv v vs v' vs'.
  v_to_i1 genv v v' ∧
  vs_to_i1 genv vs vs'
  ⇒
  vs_to_i1 genv (v::vs) (v'::vs')) ∧
(!genv.
  env_to_i1 genv [] []) ∧
(!genv x v env env' v'.
  env_to_i1 genv env env' ∧
  v_to_i1 genv v v'
  ⇒
  env_to_i1 genv ((x,v)::env) ((x,v')::env')) ∧
(!genv map shadowers env.
  (!x v.
     x ∉ shadowers ∧
     ALOOKUP env x = SOME v
     ⇒
     ?n v_i1.
       FLOOKUP map x = SOME n ∧
       n < LENGTH genv ∧
       EL n genv = SOME v_i1 ∧
       v_to_i1 genv v v_i1)
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

val v_to_i1_eqns = Q.store_thm ("v_to_i1_eqns",
`(!genv l v.
  v_to_i1 genv (Litv l) v ⇔
    (v = Litv_i1 l)) ∧
 (!genv cn vs v.
  v_to_i1 genv (Conv cn vs) v ⇔
    ?vs'. vs_to_i1 genv vs vs' ∧ (v = Conv_i1 cn vs')) ∧
 (!genv l v.
  v_to_i1 genv (Loc l) v ⇔
    (v = Loc_i1 l)) ∧
 (!genv vs v.
  v_to_i1 genv (Vectorv vs) v ⇔
    ?vs'. vs_to_i1 genv vs vs' ∧ (v = Vectorv_i1 vs')) ∧
 (!genv vs.
  vs_to_i1 genv [] vs ⇔
    (vs = [])) ∧
 (!genv l v vs vs'.
  vs_to_i1 genv (v::vs) vs' ⇔
    ?v' vs''. v_to_i1 genv v v' ∧ vs_to_i1 genv vs vs'' ∧ vs' = v'::vs'') ∧
 (!genv env'.
  env_to_i1 genv [] env' ⇔
    env' = []) ∧
 (!genv x v env env'.
  env_to_i1 genv ((x,v)::env) env' ⇔
    ?v' env''. v_to_i1 genv v v' ∧ env_to_i1 genv env env'' ∧ env' = ((x,v')::env'')) ∧
 (!genv map shadowers env genv.
  global_env_inv_flat genv map shadowers env ⇔
    (!x v.
      x ∉ shadowers ∧
      ALOOKUP env x = SOME v
      ⇒
      ?n v_i1.
        FLOOKUP map x = SOME n ∧
        n < LENGTH genv ∧
        EL n genv = SOME v_i1 ∧
        v_to_i1 genv v v_i1)) ∧
(!genv mods tops menv shadowers env genv.
  global_env_inv genv mods tops menv shadowers env ⇔
    global_env_inv_flat genv tops shadowers env ∧
    (!mn env'.
      ALOOKUP menv mn = SOME env'
      ⇒
      ?map.
        FLOOKUP mods mn = SOME map ∧
        global_env_inv_flat genv map {} env'))`,
rw [] >>
rw [Once v_to_i1_cases] >>
metis_tac []);

val v_to_i1_weakening = Q.prove (
`(!genv v v_i1.
  v_to_i1 genv v v_i1
  ⇒
  ∀l. v_to_i1 (genv++l) v v_i1) ∧
 (!genv vs vs_i1.
  vs_to_i1 genv vs vs_i1
  ⇒
  !l. vs_to_i1 (genv++l) vs vs_i1) ∧
 (!genv env env_i1.
  env_to_i1 genv env env_i1
  ⇒
  !l. env_to_i1 (genv++l) env env_i1) ∧
 (!genv map shadowers env.
  global_env_inv_flat genv map shadowers env
  ⇒
  !l. global_env_inv_flat (genv++l) map shadowers env) ∧
 (!genv mods tops menv shadowers env.
  global_env_inv genv mods tops menv shadowers env
  ⇒
  !l.global_env_inv (genv++l) mods tops menv shadowers env)`,
 ho_match_mp_tac v_to_i1_ind >>
 rw [v_to_i1_eqns]
 >- (rw [Once v_to_i1_cases] >>
     MAP_EVERY qexists_tac [`mods`, `tops`, `env`, `env'`] >>
     fs [FDOM_FUPDATE_LIST, SUBSET_DEF, v_to_i1_eqns])
 >- (rw [Once v_to_i1_cases] >>
     MAP_EVERY qexists_tac [`mods`, `tops`, `env`, `env'`] >>
     fs [FDOM_FUPDATE_LIST, SUBSET_DEF, v_to_i1_eqns])
 >- (rw [Once v_to_i1_cases] >>
     MAP_EVERY qexists_tac [`mods`, `tops`, `tops'`] >>
     fs [FDOM_FUPDATE_LIST, SUBSET_DEF, v_to_i1_eqns, EL_APPEND1] >>
     rw [] >>
     res_tac >>
     qexists_tac `n` >>
     rw [EL_APPEND1] >>
     decide_tac)
 >- metis_tac [DECIDE ``x < y ⇒ x < y + l:num``, EL_APPEND1]
 >- metis_tac []);

val (result_to_i1_rules, result_to_i1_ind, result_to_i1_cases) = Hol_reln `
(∀genv v v'.
  f genv v v'
  ⇒
  result_to_i1 f genv (Rval v) (Rval v')) ∧
(∀genv v v'.
  v_to_i1 genv v v'
  ⇒
  result_to_i1 f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
(!genv.
  result_to_i1 f genv (Rerr Rtimeout_error) (Rerr Rtimeout_error)) ∧
(!genv.
  result_to_i1 f genv (Rerr Rtype_error) (Rerr Rtype_error))`;

val result_to_i1_eqns = Q.prove (
`(!genv v r.
  result_to_i1 f genv (Rval v) r ⇔
    ?v'. f genv v v' ∧ r = Rval v') ∧
 (!genv v r.
  result_to_i1 f genv (Rerr (Rraise v)) r ⇔
    ?v'. v_to_i1 genv v v' ∧ r = Rerr (Rraise v')) ∧
 (!genv v r.
  result_to_i1 f genv (Rerr Rtimeout_error) r ⇔
    r = Rerr Rtimeout_error) ∧
 (!genv v r.
  result_to_i1 f genv (Rerr Rtype_error) r ⇔
    r = Rerr Rtype_error)`,
rw [result_to_i1_cases] >>
metis_tac []);

val (sv_to_i1_rules, sv_to_i1_ind, sv_to_i1_cases) = Hol_reln `
(!genv v v'.
  v_to_i1 genv v v'
  ⇒
  sv_to_i1 genv (Refv v) (Refv v')) ∧
(!genv w.
  sv_to_i1 genv (W8array w) (W8array w)) ∧
(!genv vs vs'.
  vs_to_i1 genv vs vs'
  ⇒
  sv_to_i1 genv (Varray vs) (Varray vs'))`;

val sv_to_i1_weakening = Q.prove (
`(!genv sv sv_i1.
  sv_to_i1 genv sv sv_i1
  ⇒
  ∀l. sv_to_i1 (genv++l) sv sv_i1)`,
 rw [sv_to_i1_cases] >>
 metis_tac [v_to_i1_weakening]);

val (s_to_i1_rules, s_to_i1_ind, s_to_i1_cases) = Hol_reln `
(!genv c s s'.
  LIST_REL (sv_to_i1 genv) s s'
  ⇒
  s_to_i1 genv (c,s) (c,s'))`;

val vs_to_i1_list_rel = Q.prove (
`!genv vs vs'. vs_to_i1 genv vs vs' = LIST_REL (v_to_i1 genv) vs vs'`,
 induct_on `vs` >>
 rw [v_to_i1_eqns] >>
 metis_tac []);

val (env_all_to_i1_rules, env_all_to_i1_ind, env_all_to_i1_cases) = Hol_reln `
(!genv mods tops menv cenv env env' env_i1 locals.
  locals = set (MAP FST env) ∧
  global_env_inv genv mods tops menv locals env' ∧
  env_to_i1 genv env env_i1
  ⇒
  env_all_to_i1 genv mods tops (menv,cenv,env++env') (genv,cenv,env_i1) locals)`;

val env_to_i1_append = Q.prove (
`!genv env1 env2 env1' env2'.
  env_to_i1 genv env1 env1' ∧
  env_to_i1 genv env2 env2'
  ⇒
  env_to_i1 genv (env1++env2) (env1'++env2')`,
 induct_on `env1` >>
 rw [v_to_i1_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i1_eqns]);

val env_to_i1_reverse = Q.prove (
`!genv env1 env2.
  env_to_i1 genv env1 env2
  ⇒
  env_to_i1 genv (REVERSE env1) (REVERSE env2)`,
 induct_on `env1` >>
 rw [v_to_i1_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i1_eqns] >>
 match_mp_tac env_to_i1_append >>
 rw [v_to_i1_eqns]);

val do_con_check_i1 = Q.prove (
`!genv mods tops env cn es env_i1 locals.
  do_con_check (all_env_to_cenv env) cn (LENGTH es) ∧
  env_all_to_i1 genv mods tops env env_i1 locals
  ⇒
  do_con_check (all_env_i1_to_cenv env_i1) cn (LENGTH (exps_to_i1 mods (DRESTRICT tops (COMPL locals)) es))`,
 rw [do_con_check_def] >>
 every_case_tac >>
 fs [env_all_to_i1_cases] >>
 rw [] >>
 fs [all_env_i1_to_cenv_def, all_env_to_cenv_def] >>
 rw [] >>
 ntac 3 (pop_assum (fn _ => all_tac)) >>
 induct_on `es` >>
 rw [exp_to_i1_def]);

val build_conv_i1 = Q.prove (
`!genv mods tops env cn vs v vs' env_i1 locals.
  (build_conv (all_env_to_cenv env) cn vs = SOME v) ∧
  env_all_to_i1 genv mods tops env env_i1 locals ∧
  vs_to_i1 genv vs vs'
  ⇒
  ∃v'.
    v_to_i1 genv v v' ∧
    build_conv_i1 (all_env_i1_to_cenv env_i1) cn vs' = SOME v'`,
 rw [build_conv_def, build_conv_i1_def] >>
 every_case_tac >>
 rw [Once v_to_i1_cases] >>
 fs [env_all_to_i1_cases] >>
 rw [] >>
 fs [all_env_i1_to_cenv_def, all_env_to_cenv_def]);

val global_env_inv_lookup_top = Q.prove (
`!genv mods tops menv shadowers env x v n.
  global_env_inv genv mods tops menv shadowers env ∧
  ALOOKUP env x = SOME v ∧
  x ∉ shadowers ∧
  FLOOKUP tops x = SOME n
  ⇒
  ?v_i1. LENGTH genv > n ∧ EL n genv = SOME v_i1 ∧ v_to_i1 genv v v_i1`,
 rw [v_to_i1_eqns] >>
 res_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 metis_tac []);

val env_to_i1_lookup = Q.prove (
`!genv menv env genv x v env'.
  ALOOKUP env x = SOME v ∧
  env_to_i1 genv env env'
  ⇒
  ?v'.
    v_to_i1 genv v v' ∧
    ALOOKUP env' x = SOME v'`,
 induct_on `env` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = x` >>
 fs [] >>
 rw [] >>
 fs [v_to_i1_eqns]);

val global_env_inv_lookup_mod1 = Q.prove (
`!genv mods tops menv shadowers env genv mn n env'.
  global_env_inv genv mods tops menv shadowers env ∧
  ALOOKUP menv mn = SOME env'
  ⇒
  ?n. FLOOKUP mods mn = SOME n`,
 rw [] >>
 fs [v_to_i1_eqns] >>
 metis_tac []);

val global_env_inv_lookup_mod2 = Q.prove (
`!genv mods tops menv shadowers env genv mn n env' x v map.
  global_env_inv genv mods tops menv shadowers env ∧
  ALOOKUP menv mn = SOME env' ∧
  ALOOKUP env' x = SOME v ∧
  FLOOKUP mods mn = SOME map
  ⇒
  ?n. FLOOKUP map x = SOME n`,
 rw [] >>
 fs [v_to_i1_eqns] >>
 res_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 fs []);

val global_env_inv_lookup_mod3 = Q.prove (
`!genv mods tops menv shadowers env genv mn n env' x v map n.
  global_env_inv genv mods tops menv shadowers env ∧
  ALOOKUP menv mn = SOME env' ∧
  ALOOKUP env' x = SOME v ∧
  FLOOKUP mods mn = SOME map ∧
  FLOOKUP map x = SOME n
  ⇒
  LENGTH genv > n ∧ ?v_i1. EL n genv = SOME v_i1 ∧ v_to_i1 genv v v_i1`,
 rw [] >>
 fs [v_to_i1_eqns] >>
 res_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 metis_tac []);

val global_env_inv_add_locals = Q.prove (
`!genv mods tops menv locals1 locals2 env.
  global_env_inv genv mods tops menv locals1 env
  ⇒
  global_env_inv genv mods tops menv (locals2 ∪ locals1) env`,
 rw [v_to_i1_eqns]);

val env_to_i1_dom = Q.prove (
`!genv env env_i1.
  env_to_i1 genv env env_i1
  ⇒
  MAP FST env = MAP FST env_i1`,
 induct_on `env` >>
 rw [v_to_i1_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i1_eqns] >>
 rw [] >>
 metis_tac []);

val vs_to_i1_append1 = Q.prove (
`!genv vs v vs' v'.
  vs_to_i1 genv (vs++[v]) (vs'++[v'])
  ⇔
  vs_to_i1 genv vs vs' ∧
  v_to_i1 genv v v'`,
 induct_on `vs` >>
 rw [] >>
 cases_on `vs'` >>
 rw [v_to_i1_eqns]
 >- (cases_on `vs` >>
     rw [v_to_i1_eqns]) >>
 metis_tac []);

val length_env_to_i1 = Q.prove (
`!env genv env'.
  env_to_i1 genv env env'
  ⇒
  LENGTH env = LENGTH env'`,
 induct_on `env` >>
 rw [v_to_i1_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i1_eqns] >>
 metis_tac []);

val length_vs_to_i1 = Q.prove (
`!vs genv vs'.
  vs_to_i1 genv vs vs'
  ⇒
  LENGTH vs = LENGTH vs'`,
 induct_on `vs` >>
 rw [v_to_i1_eqns] >>
 fs [] >>
 metis_tac []);

val do_eq_i1 = Q.prove (
`(!v1 v2 genv r v1_i1 v2_i1.
  do_eq v1 v2 = r ∧
  v_to_i1 genv v1 v1_i1 ∧
  v_to_i1 genv v2 v2_i1
  ⇒
  do_eq_i1 v1_i1 v2_i1 = r) ∧
 (!vs1 vs2 genv r vs1_i1 vs2_i1.
  do_eq_list vs1 vs2 = r ∧
  vs_to_i1 genv vs1 vs1_i1 ∧
  vs_to_i1 genv vs2 vs2_i1
  ⇒
  do_eq_list_i1 vs1_i1 vs2_i1 = r)`,
 ho_match_mp_tac do_eq_ind >>
 rw [do_eq_i1_def, do_eq_def, v_to_i1_eqns] >>
 rw [] >>
 rw [do_eq_i1_def, do_eq_def, v_to_i1_eqns] >>
 imp_res_tac length_vs_to_i1 >>
 fs []
 >- metis_tac []
 >- (rpt (qpat_assum `vs_to_i1 env vs x0` (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i1_cases])) >>
     rw [] >>
     fs [vs_to_i1_list_rel, do_eq_def, do_eq_i1_def] >>
     res_tac >>
     fs [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [do_eq_i1_def]) >>
 res_tac >>
 every_case_tac >>
 fs [] >>
 metis_tac []);

val find_recfun_to_i1 = Q.prove (
`!x funs e mods tops y.
  find_recfun x funs = SOME (y,e)
  ⇒
  find_recfun x (funs_to_i1 mods tops funs) = SOME (y,exp_to_i1 mods (tops \\ y) e)`,
 induct_on `funs` >>
 rw [Once find_recfun_def, exp_to_i1_def] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 fs [Once find_recfun_def, exp_to_i1_def]);

val build_rec_env_i1_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. (f, Recclosure_i1 env funs' f)::env') env' funs =
MAP (λ(fn,n,e). (fn, Recclosure_i1 env funs' fn)) funs ++ env'`,
Induct >>
rw [] >>
PairCases_on `h` >>
rw []);

val funs_to_i1_dom = Q.prove (
`!funs.
  (MAP (λ(x,y,z). x) funs)
  =
  (MAP (λ(x,y,z). x) (funs_to_i1 mods tops funs))`,
 induct_on `funs` >>
 rw [exp_to_i1_def] >>
 PairCases_on `h` >>
 rw [exp_to_i1_def]);

val do_app_rec_help = Q.prove (
`!genv menv'' cenv'' env' funs env''' env_i1' mods' tops' funs'.
  env_to_i1 genv env' env_i1' ∧
  set (MAP FST env''') DIFF set (MAP FST env') ⊆ FDOM tops' ∧
  global_env_inv genv mods' tops' menv'' (set (MAP FST env_i1')) env'''
  ⇒
  env_to_i1 genv
  (MAP
     (λ(fn,n,e). (fn,Recclosure (menv'',cenv'',env' ++ env''') funs' fn))
     funs)
  (MAP
     (λ(fn,n,e).
        (fn,
         Recclosure_i1 (cenv'',env_i1')
           (funs_to_i1 mods'
              (DRESTRICT tops'
                 (COMPL (set (MAP FST env_i1') ∪ set (MAP FST funs'))))
              funs') fn))
     (funs_to_i1 mods'
        (DRESTRICT tops'
           (COMPL (set (MAP FST env_i1') ∪ set (MAP FST funs')))) funs))`,
 induct_on `funs` >>
 rw [v_to_i1_eqns, exp_to_i1_def] >>
 PairCases_on `h` >>
 rw [v_to_i1_eqns, exp_to_i1_def] >>
 rw [Once v_to_i1_cases] >>
 MAP_EVERY qexists_tac [`mods'`, `tops'`, `env'`, `env'''`] >>
 rw [] >>
 fs [v_to_i1_eqns]);

(* Alternate definition for build_rec_env_i1 *)
val build_rec_env_i1_merge = Q.store_thm ("build_rec_env_i1_merge",
`∀funs funs' env env'.
  build_rec_env_i1 funs env env' =
  MAP (λ(fn,n,e). (fn, Recclosure_i1 env funs fn)) funs ++ env'`,
rw [build_rec_env_i1_def, build_rec_env_i1_help_lem]);

val global_env_inv_extend2 = Q.prove (
`!genv mods tops menv env tops' env' locals.
  MAP FST env' = REVERSE (MAP FST tops') ∧
  global_env_inv genv mods tops menv locals env ∧
  global_env_inv genv FEMPTY (FEMPTY |++ tops') [] locals env'
  ⇒
  global_env_inv genv mods (tops |++ tops') menv locals (env'++env)`,
 rw [v_to_i1_eqns, flookup_fupdate_list] >>
 full_case_tac >>
 fs [ALOOKUP_APPEND] >>
 full_case_tac >>
 fs [] >>
 res_tac >>
 fs [] >>
 rpt (pop_assum mp_tac) >>
 rw [] >>
 fs [ALOOKUP_FAILS] >>
 imp_res_tac ALOOKUP_MEM >>
 `set (MAP FST env') = set (REVERSE (MAP FST tops'))` by metis_tac [] >>
 fs [EXTENSION] >>
 metis_tac [pair_CASES, MEM_MAP, FST]);

val lookup_build_rec_env_lem = Q.prove (
`!x cl_env funs' funs.
  ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure cl_env funs' fn)) funs) x = SOME v
  ⇒
  v = Recclosure cl_env funs' x`,
 induct_on `funs` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 every_case_tac >>
 fs []);

val funs_to_i1_map = Q.prove (
`!mods tops funs.
  funs_to_i1 mods tops funs = MAP (\(f,x,e). (f,x,exp_to_i1 mods (tops\\x) e)) funs`,
 induct_on `funs` >>
 rw [exp_to_i1_def] >>
 PairCases_on `h` >>
 rw [exp_to_i1_def]);

val v_to_list_i1_correct = Q.prove (
`!v1 v2 vs1.
  v_to_i1 genv v1 v2 ∧
  v_to_list v1 = SOME vs1
  ⇒
  ?vs2.
    v_to_list_i1 v2 = SOME vs2 ∧
    vs_to_i1 genv vs1 vs2`,
 ho_match_mp_tac v_to_list_ind >>
 rw [v_to_list_def] >>
 every_case_tac >>
 fs [v_to_i1_eqns, v_to_list_i1_def] >>
 rw [] >>
 every_case_tac >>
 fs [v_to_i1_eqns, v_to_list_i1_def] >>
 rw [] >>
 metis_tac [NOT_SOME_NONE, SOME_11]);

val char_list_to_v_i1_correct = prove(
  ``∀ls. v_to_i1 genv (char_list_to_v ls) (char_list_to_v_i1 ls)``,
  Induct >> simp[char_list_to_v_def,char_list_to_v_i1_def,v_to_i1_eqns])

val v_i1_to_char_list_correct = Q.prove (
`!v1 v2 vs1.
  v_to_i1 genv v1 v2 ∧
  v_to_char_list v1 = SOME vs1
  ⇒
  v_i1_to_char_list v2 = SOME vs1`,
 ho_match_mp_tac v_to_char_list_ind >>
 rw [v_to_char_list_def] >>
 every_case_tac >>
 fs [v_to_i1_eqns, v_i1_to_char_list_def]);

val do_app_i1 = Q.prove (
`!genv s1 s2 op vs r s1_i1 vs_i1.
  do_app s1 op vs = SOME (s2, r) ∧
  LIST_REL (sv_to_i1 genv) s1 s1_i1 ∧
  vs_to_i1 genv vs vs_i1
  ⇒
   ∃r_i1 s2_i1.
     LIST_REL (sv_to_i1 genv) s2 s2_i1 ∧
     result_to_i1 v_to_i1 genv r r_i1 ∧
     do_app_i1 s1_i1 op vs_i1 = SOME (s2_i1, r_i1)`,
 rw [do_app_cases, do_app_i1_def] >>
 fs [v_to_i1_eqns, result_to_i1_cases] >>
 srw_tac [boolSimps.DNF_ss] [] >>
 rw [METIS_PROVE [] ``(!x y. P x y ⇒ Q) ⇔ ((?x y. P x y) ⇒ Q)``, pair_CASES,
     prim_exn_def, prim_exn_i1_def, v_to_i1_eqns] >>
 imp_res_tac LIST_REL_LENGTH
 >- (every_case_tac >>
     metis_tac [do_eq_i1, eq_result_11, eq_result_distinct])
 >- (every_case_tac >>
     metis_tac [do_eq_i1, eq_result_11, eq_result_distinct])
 >- (fs [store_assign_def,store_v_same_type_def] >>
     every_case_tac >> fs[] >-
     metis_tac [EVERY2_LUPDATE_same, sv_to_i1_rules] >>
     fs[LIST_REL_EL_EQN,sv_to_i1_cases] >>
     metis_tac[store_v_distinct])
 >- (fs [store_alloc_def] >>
     rw [sv_to_i1_cases])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [])
 >- fs [store_alloc_def]
 >- (fs [store_alloc_def] >>
     rw [sv_to_i1_cases])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [markerTheory.Abbrev_def])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [markerTheory.Abbrev_def])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [] >>
     qexists_tac `s1_i1` >>
     rw [markerTheory.Abbrev_def] >>
     decide_tac)
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [markerTheory.Abbrev_def])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [markerTheory.Abbrev_def])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [markerTheory.Abbrev_def])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [] >>
     rw [markerTheory.Abbrev_def]
     >- decide_tac >>
     rw [EL_LUPDATE] >>
     fs[store_v_same_type_def])
 >- simp[char_list_to_v_i1_correct]
 >- (qpat_assum`SOME X = Y`(assume_tac o SYM) >>
     imp_res_tac v_i1_to_char_list_correct >> fs[] )
 >- (every_case_tac >>
     rw [] >>
     imp_res_tac v_to_list_i1_correct >>
     fs [] >>
     metis_tac [SOME_11, NOT_SOME_NONE])
 >- (rw [markerTheory.Abbrev_def] >>
     metis_tac [])
 >- (rw [markerTheory.Abbrev_def] >>
     fs [vs_to_i1_list_rel] >>
     metis_tac [LIST_REL_LENGTH])
 >- (rw [markerTheory.Abbrev_def] >>
     fs [vs_to_i1_list_rel] >>
     imp_res_tac LIST_REL_LENGTH
     >- intLib.ARITH_TAC >>
     fs [LIST_REL_EL_EQN])
 >- (fs [vs_to_i1_list_rel] >>
     metis_tac [LIST_REL_LENGTH])
 >- fs [store_alloc_def]
 >- (fs [store_alloc_def, sv_to_i1_cases, vs_to_i1_list_rel] >>
     rw [EL_REPLICATE, LIST_REL_EL_EQN, LENGTH_REPLICATE, sv_to_i1_cases])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def, vs_to_i1_list_rel] >>
     imp_res_tac LIST_REL_LENGTH >>
     rw [] >>
     decide_tac)
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def] >>
     qexists_tac `s1_i1` >>
     fs [LIST_REL_EL_EQN, vs_to_i1_list_rel] >>
     srw_tac [ARITH_ss] [])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def] >>
     fs [LIST_REL_EL_EQN, vs_to_i1_list_rel] >>
     srw_tac [ARITH_ss] [])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def] >>
     fs [LIST_REL_EL_EQN, vs_to_i1_list_rel] >>
     srw_tac [ARITH_ss] [])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def] >>
     fs [LIST_REL_EL_EQN, vs_to_i1_list_rel] >>
     srw_tac [ARITH_ss] [])
 >- (fs [store_lookup_def] >>
     every_case_tac >>
     fs [LIST_REL_EL_EQN, sv_to_i1_cases, store_assign_def] >>
     res_tac >>
     rw [] >>
     fs [markerTheory.Abbrev_def] >>
     rw [] >>
     fs [LIST_REL_EL_EQN, vs_to_i1_list_rel, store_v_same_type_def, EL_LUPDATE] >>
     srw_tac [ARITH_ss] [] >>
     rw [EL_LUPDATE]));

val do_opapp_i1 = Q.prove (
`!genv vs vs_i1 env e.
  do_opapp vs = SOME (env, e) ∧
  vs_to_i1 genv vs vs_i1
  ⇒
   ∃mods tops env_i1 locals.
     env_all_to_i1 genv mods tops env env_i1 locals ∧
     do_opapp_i1 genv vs_i1 = SOME (env_i1, exp_to_i1 mods (DRESTRICT tops (COMPL locals)) e)`,
 rw [do_opapp_cases, do_opapp_i1_def, vs_to_i1_list_rel] >>
 fs [LIST_REL_CONS1] >>
 rw []
 >- (qpat_assum `v_to_i1 genv (Closure (menv'',cenv'',env'') n e) v1_i1` mp_tac >>
     rw [Once v_to_i1_cases] >>
     rw [] >>
     MAP_EVERY qexists_tac [`mods`, `tops`, `n INSERT set (MAP FST env_i1)`] >>
     rw [DRESTRICT_DOMSUB, compl_insert, env_all_to_i1_cases] >>
     MAP_EVERY qexists_tac [`(n, v2) :: env`, `env'`] >>
     rw [v_to_i1_eqns]
     >- metis_tac [env_to_i1_dom] >>
     fs [v_to_i1_eqns])
 >- (qpat_assum `v_to_i1 genv (Recclosure (menv'',cenv'',env'') funs n') v1_i1` mp_tac >>
     rw [Once v_to_i1_cases] >>
     rw [] >>
     imp_res_tac find_recfun_to_i1 >>
     rw []
     >- (MAP_EVERY qexists_tac [`mods`, `tops`, `n'' INSERT set (MAP FST env_i1) ∪ set (MAP FST funs)`] >>
         rw [DRESTRICT_DOMSUB, compl_insert, env_all_to_i1_cases] >>
         rw []
         >- (MAP_EVERY qexists_tac [`(n'', v2)::build_rec_env funs (menv'',cenv'',env ++ env') env`, `env'`] >>
             rw [build_rec_env_merge, EXTENSION]
             >- (rw [MEM_MAP, EXISTS_PROD] >>
                 imp_res_tac env_to_i1_dom >>
                 metis_tac [pair_CASES, FST, MEM_MAP, EXISTS_PROD, LAMBDA_PROD])
             >- metis_tac [INSERT_SING_UNION, global_env_inv_add_locals, UNION_COMM]
             >- (fs [v_to_i1_eqns, build_rec_env_i1_merge] >>
                 match_mp_tac env_to_i1_append >>
                 rw [] >>
                 match_mp_tac do_app_rec_help >>
                 rw [] >>
                 fs [v_to_i1_eqns]))
         >- (
          simp[funs_to_i1_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
          fs[FST_triple]))
     >- (MAP_EVERY qexists_tac [`mods`, `tops|++tops'`, `{n''}`] >>
         rw [DRESTRICT_UNIV, GSYM DRESTRICT_DOMSUB, compl_insert, env_all_to_i1_cases] >>
         MAP_EVERY qexists_tac [`[(n'',v2)]`, `build_rec_env funs (menv'',cenv'',env'') env''`] >>
         rw [build_rec_env_merge, EXTENSION]
         >- (match_mp_tac global_env_inv_extend2 >>
             rw [MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_triple, GSYM MAP_REVERSE]
             >- metis_tac [global_env_inv_add_locals, UNION_EMPTY] >>
             rw [v_to_i1_eqns] >>
             `MEM x (MAP FST funs)`
                       by (imp_res_tac ALOOKUP_MEM >>
                           fs [MEM_MAP] >>
                           PairCases_on `y` >>
                           rw [] >>
                           fs [] >>
                           metis_tac [FST, MEM_MAP, pair_CASES]) >>
             res_tac >>
             qexists_tac `n` >>
             rw [] >>
             `v = Recclosure (menv'',cenv'',env'') funs x` by metis_tac [lookup_build_rec_env_lem] >>
             rw [Once v_to_i1_cases] >>
             MAP_EVERY qexists_tac [`mods`, `tops`, `tops'`] >>
             rw [find_recfun_lookup])
         >- fs [v_to_i1_eqns, build_rec_env_i1_merge])));

val match_result_to_i1_def = Define
`(match_result_to_i1 genv env' (Match env) (Match env_i1) =
   ?env''. env = env'' ++ env' ∧ env_to_i1 genv env'' env_i1) ∧
 (match_result_to_i1 genv env' No_match No_match = T) ∧
 (match_result_to_i1 genv env' Match_type_error Match_type_error = T) ∧
 (match_result_to_i1 genv env' _ _ = F)`;

val pmatch_to_i1_correct = Q.prove (
`(!cenv s p v env r env' env'' genv env_i1 s_i1 v_i1.
  pmatch cenv s p v env = r ∧
  env = env' ++ env'' ∧
  LIST_REL (sv_to_i1 genv) s s_i1 ∧
  v_to_i1 genv v v_i1 ∧
  env_to_i1 genv env' env_i1
  ⇒
  ?r_i1.
    pmatch_i1 cenv s_i1 p v_i1 env_i1 = r_i1 ∧
    match_result_to_i1 genv env'' r r_i1) ∧
 (!cenv s ps vs env r env' env'' genv env_i1 s_i1 vs_i1.
  pmatch_list cenv s ps vs env = r ∧
  env = env' ++ env'' ∧
  LIST_REL (sv_to_i1 genv) s s_i1 ∧
  vs_to_i1 genv vs vs_i1 ∧
  env_to_i1 genv env' env_i1
  ⇒
  ?r_i1.
    pmatch_list_i1 cenv s_i1 ps vs_i1 env_i1 = r_i1 ∧
    match_result_to_i1 genv env'' r r_i1)`,
 ho_match_mp_tac pmatch_ind >>
 rw [pmatch_def, pmatch_i1_def] >>
 fs [match_result_to_i1_def, pmatch_i1_def, v_to_i1_eqns] >>
 imp_res_tac LIST_REL_LENGTH
 >- (every_case_tac >>
     fs [match_result_to_i1_def])
 >- (every_case_tac >>
     fs [match_result_to_i1_def] >>
     metis_tac [length_vs_to_i1])
 >- (every_case_tac >>
     fs [match_result_to_i1_def]
     >- (fs [store_lookup_def] >>
         metis_tac [])
     >- (fs [store_lookup_def] >>
         metis_tac [length_vs_to_i1])
     >- (FIRST_X_ASSUM match_mp_tac >>
         rw [] >>
         fs [store_lookup_def, LIST_REL_EL_EQN, sv_to_i1_cases] >>
         res_tac >>
         fs [] >>
         rw [])
     >- (fs [store_lookup_def, LIST_REL_EL_EQN] >>
         rw [] >>
         fs [sv_to_i1_cases] >>
         res_tac >>
         fs [])
     >- (fs [store_lookup_def, LIST_REL_EL_EQN] >>
         rw [] >>
         fs [sv_to_i1_cases] >>
         res_tac >>
         fs [])
     >- (fs [store_lookup_def, LIST_REL_EL_EQN] >>
         rw [] >>
         fs [sv_to_i1_cases] >>
         res_tac >>
         fs [])
     >- (fs [store_lookup_def, LIST_REL_EL_EQN] >>
         rw [] >>
         fs [sv_to_i1_cases] >>
         res_tac >>
         fs []))
 >- (fs [Once v_to_i1_cases] >>
     rw [pmatch_i1_def, match_result_to_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [pmatch_i1_def, match_result_to_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [pmatch_i1_def, match_result_to_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [pmatch_i1_def, match_result_to_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [pmatch_i1_def, match_result_to_i1_def])
 >- (fs [Once v_to_i1_cases] >>
     rw [pmatch_i1_def, match_result_to_i1_def])
 >- (every_case_tac >>
     fs [match_result_to_i1_def] >>
     rw [] >>
     pop_assum mp_tac >>
     pop_assum mp_tac >>
     res_tac >>
     rw [] >>
     CCONTR_TAC >>
     fs [match_result_to_i1_def] >>
     metis_tac [match_result_to_i1_def, match_result_distinct]));

val exp_to_i1_correct = Q.prove (
`(∀b env s e res.
   evaluate b env s e res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !genv mods tops s' r env_i1 s_i1 e_i1 locals.
     (res = (s',r)) ∧
     env_all_to_i1 genv mods tops env env_i1 locals ∧
     s_to_i1 genv s s_i1 ∧
     (e_i1 = exp_to_i1 mods (DRESTRICT tops (COMPL locals)) e)
     ⇒
     ∃s'_i1 r_i1.
       result_to_i1 v_to_i1 genv r r_i1 ∧
       s_to_i1 genv s' s'_i1 ∧
       evaluate_i1 b env_i1 s_i1 e_i1 (s'_i1, r_i1)) ∧
 (∀b env s es res.
   evaluate_list b env s es res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !genv mods tops s' r env_i1 s_i1 es_i1 locals.
     (res = (s',r)) ∧
     env_all_to_i1 genv mods tops env env_i1 locals ∧
     s_to_i1 genv s s_i1 ∧
     (es_i1 = exps_to_i1 mods (DRESTRICT tops (COMPL locals)) es)
     ⇒
     ?s'_i1 r_i1.
       result_to_i1 vs_to_i1 genv r r_i1 ∧
       s_to_i1 genv s' s'_i1 ∧
       evaluate_list_i1 b env_i1 s_i1 es_i1 (s'_i1, r_i1)) ∧
 (∀b env s v pes err_v res.
   evaluate_match b env s v pes err_v res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !genv mods tops s' r env_i1 s_i1 v_i1 pes_i1 err_v_i1 locals.
     (res = (s',r)) ∧
     env_all_to_i1 genv mods tops env env_i1 locals ∧
     s_to_i1 genv s s_i1 ∧
     v_to_i1 genv v v_i1 ∧
     (pes_i1 = pat_exp_to_i1 mods (DRESTRICT tops (COMPL locals)) pes) ∧
     v_to_i1 genv err_v err_v_i1
     ⇒
     ?s'_i1 r_i1.
       result_to_i1 v_to_i1 genv r r_i1 ∧
       s_to_i1 genv s' s'_i1 ∧
       evaluate_match_i1 b env_i1 s_i1 v_i1 pes_i1 err_v_i1 (s'_i1, r_i1))`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >>
 rw [Once evaluate_i1_cases,exp_to_i1_def] >>
 TRY (Cases_on `err`) >>
 fs [result_to_i1_eqns, v_to_i1_eqns]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [do_con_check_i1, build_conv_i1]
 >- metis_tac [do_con_check_i1]
 >- metis_tac [do_con_check_i1]
 >- (* Variable lookup *)
    (fs [env_all_to_i1_cases] >>
     cases_on `n` >>
     rw [exp_to_i1_def] >>
     fs [lookup_var_id_def] >>
     every_case_tac >>
     fs [ALOOKUP_APPEND, all_env_i1_to_env_def, all_env_i1_to_genv_def] >>
     rw []
     >- (every_case_tac >>
         fs []
         >- (fs [v_to_i1_eqns, FLOOKUP_DRESTRICT] >>
             every_case_tac >>
             fs [ALOOKUP_FAILS] >>
             res_tac >>
             every_case_tac >>
             fs [MEM_MAP] >>
             metis_tac [pair_CASES, FST, NOT_SOME_NONE])
         >- metis_tac [env_to_i1_lookup])
     >- (every_case_tac >>
         fs [FLOOKUP_DRESTRICT]
         >- metis_tac [global_env_inv_lookup_top] >>
         imp_res_tac ALOOKUP_MEM >>
         fs [MEM_MAP] >>
         metis_tac [pair_CASES, FST, NOT_SOME_NONE])
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod1]
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod2]
     >- metis_tac [global_env_inv_lookup_mod3])
 >- (* Closure creation *)
    (rw [Once v_to_i1_cases] >>
     fs [env_all_to_i1_cases, all_env_i1_to_cenv_def, all_env_i1_to_env_def] >>
     rw [] >>
     MAP_EVERY qexists_tac [`mods`, `tops`, `env'`, `env''`] >>
     imp_res_tac env_to_i1_dom >>
     rw []
     >- (fs [SUBSET_DEF, v_to_i1_eqns] >>
         rw [] >>
         `¬(ALOOKUP env'' x = NONE)` by metis_tac [ALOOKUP_FAILS, MEM_MAP, FST, pair_CASES] >>
         cases_on `ALOOKUP env'' x` >>
         fs [] >>
         res_tac >>
         fs [FLOOKUP_DEF])
     >- (imp_res_tac global_env_inv_lookup_top >>
         fs [] >>
         imp_res_tac disjoint_drestrict >>
         rw []))
 >- (* function application *)
    (srw_tac [boolSimps.DNF_ss] [PULL_EXISTS] >>
     res_tac >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     imp_res_tac do_opapp_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1`
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- (* function application *)
    (srw_tac [boolSimps.DNF_ss] [PULL_EXISTS] >>
     res_tac >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     imp_res_tac do_opapp_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1`
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- (* function application *)
    (srw_tac [boolSimps.DNF_ss] [PULL_EXISTS] >>
     res_tac >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     imp_res_tac do_opapp_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1`
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- (* primitive application *)
    (srw_tac [boolSimps.DNF_ss] [PULL_EXISTS] >>
     res_tac >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     imp_res_tac do_app_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1`
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (fs [do_log_def] >>
     every_case_tac >>
     fs [v_to_i1_eqns, exp_to_i1_def] >>
     rw [do_if_i1_def]
     >- metis_tac [] >>
     res_tac >>
     MAP_EVERY qexists_tac [`s'_i1''`, `r_i1`] >>
     rw []
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool F)` >>
         rw [] >>
         fs [exp_to_i1_def] >>
         metis_tac [])
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool T)` >>
         rw [] >>
         fs [exp_to_i1_def] >>
         metis_tac [])
     >- (disj1_tac >>
         qexists_tac `Litv_i1 (Bool F)` >>
         rw [] >>
         fs [exp_to_i1_def] >>
         metis_tac []))
 >- (cases_on `op` >>
     rw [] >>
     metis_tac [])
 >- (cases_on `op` >>
     rw [] >>
     metis_tac [])
  >- (fs [do_if_def, do_if_i1_def] >>
     every_case_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i1''`, `r_i1`] >>
     rw [] >>
     disj1_tac
     >- (qexists_tac `Litv_i1 (Bool F)` >>
         fs [v_to_i1_eqns, exp_to_i1_def] >>
         metis_tac [])
     >- (qexists_tac `Litv_i1 (Bool T)` >>
         fs [v_to_i1_eqns, exp_to_i1_def] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []
 >- (fs [v_to_i1_eqns] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Let *)
    (`?env'. env_i1 = (genv,cenv,env')` by fs [env_all_to_i1_cases] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     cases_on `n` >>
     fs [opt_bind_def, exp_to_i1_def]
     >- metis_tac [compl_insert, DRESTRICT_DOMSUB] >>
     `env_all_to_i1 genv mods tops (menv,cenv,(x, v) :: env)
                    (genv, cenv, (x,v')::env') (x INSERT locals)`
                by (fs [env_all_to_i1_cases] >>
                    MAP_EVERY qexists_tac [`(x, v) :: env''`, `env'''`] >>
                    fs [v_to_i1_eqns] >>
                    rw []) >>
     metis_tac [compl_insert, DRESTRICT_DOMSUB])
 >- (cases_on `n` >>
     fs [exp_to_i1_def] >>
     metis_tac [])
 >- (cases_on `n` >>
     fs [exp_to_i1_def] >>
     metis_tac [])
 >- (* Letrec *)
    (rw [markerTheory.Abbrev_def] >>
     pop_assum mp_tac >>
     rw [] >>
     `?env'. env_i1 = (genv,cenv,env')` by fs [env_all_to_i1_cases] >>
     rw [] >>
     `env_all_to_i1 genv mods tops (menv,cenv,build_rec_env funs (menv,cenv,env) env)
                                   (genv,cenv,build_rec_env_i1 (funs_to_i1 mods (FOLDR (λk m. m \\ k) (DRESTRICT tops (COMPL locals)) (MAP FST funs)) funs) (cenv, env') env')
                                   (set (MAP FST funs) ∪ locals)`
                            by (fs [env_all_to_i1_cases] >>
                                MAP_EVERY qexists_tac [`build_rec_env funs (menv,cenv,env'' ++ env''') env''`, `env'''`] >>
                                rw [build_rec_env_merge, EXTENSION]
                                >- (rw [MEM_MAP, EXISTS_PROD] >>
                                   imp_res_tac env_to_i1_dom >>
                                   metis_tac [pair_CASES, FST, MEM_MAP, EXISTS_PROD, LAMBDA_PROD])
                                >- metis_tac [INSERT_SING_UNION, global_env_inv_add_locals, UNION_COMM]
                                >- (fs [v_to_i1_eqns, build_rec_env_i1_merge] >>
                                    match_mp_tac env_to_i1_append >>
                                    rw [drestrict_iter_list, GSYM COMPL_UNION] >>
                                    imp_res_tac env_to_i1_dom >>
                                    rw [] >>
                                    match_mp_tac do_app_rec_help >>
                                    rw [] >>
                                    fs [v_to_i1_eqns] >>
                                    rw [SUBSET_DEF] >>
                                    `¬(ALOOKUP env''' x = NONE)` 
                                           by (rw [ALOOKUP_FAILS] >>
                                               metis_tac [pair_CASES, FST, MEM_MAP]) >>
                                    cases_on `ALOOKUP env''' x` >>
                                    fs [] >>
                                    res_tac >>
                                    fs [FLOOKUP_DEF])) >>
      res_tac >>
      MAP_EVERY qexists_tac [`s'_i1'`, `r_i1'`] >>
      rw [] >>
      disj1_tac >>
      rw [] >>
      fs [drestrict_iter_list]
      >- metis_tac [funs_to_i1_dom]
      >- (`(\(x,y,z). x) = FST:tvarN # tvarN # exp -> tvarN` by (rw [FUN_EQ_THM] >>PairCases_on `x` >> rw []) >>
          rw [] >>
          fs [COMPL_UNION] >>
          metis_tac [INTER_COMM]))
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (* Pattern matching *)
    (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i1_cases, env_all_to_i1_cases] >>
     rw [] >>
     `match_result_to_i1 genv env''' (Match env') (pmatch_i1 cenv s'' p v_i1 env_i1')`
                   by metis_tac [pmatch_to_i1_correct] >>
     cases_on `pmatch_i1 cenv s'' p v_i1 env_i1'` >>
     fs [match_result_to_i1_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     FIRST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env''''`, `env'''`, `a`, `s''`] mp_tac) >>
     rw [] >>
     fs [] >>
     imp_res_tac pmatch_extend >>
     fs [APPEND_11] >>
     rw [] >>
     imp_res_tac global_env_inv_add_locals >>
     fs [] >>
     rw [] >>
     MAP_EVERY qexists_tac [`(c,s'''')`, `r_i1`] >>
     rw [] >>
     fs [COMPL_UNION, drestrict_iter_list] >>
     metis_tac [INTER_COMM])
 >- (* Pattern matching *)
    (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i1_cases, env_all_to_i1_cases] >>
     rw [] >>
     `match_result_to_i1 genv env'' (No_match) (pmatch_i1 cenv s'' p v_i1 env_i1')`
                   by metis_tac [pmatch_to_i1_correct] >>
     cases_on `pmatch_i1 cenv s'' p v_i1 env_i1'` >>
     fs [match_result_to_i1_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``]));

val evaluate_i1_con = Q.prove (
`evaluate_i1 a0 a1 a2 (Con_i1 cn es) a4 ⇔
      (∃vs s' v.
         a4 = (s',Rval v) ∧
         do_con_check (all_env_i1_to_cenv a1) cn (LENGTH es) ∧
         build_conv_i1 (all_env_i1_to_cenv a1) cn vs = SOME v ∧
         evaluate_list_i1 a0 a1 a2 es (s',Rval vs)) ∨
      (a4 = (a2,Rerr Rtype_error) ∧
       ¬do_con_check (all_env_i1_to_cenv a1) cn (LENGTH es)) ∨
      (∃err s'.
         a4 = (s',Rerr err) ∧
         do_con_check (all_env_i1_to_cenv a1) cn (LENGTH es) ∧
         evaluate_list_i1 a0 a1 a2 es (s',Rerr err))`,
rw [Once evaluate_i1_cases] >>
eq_tac >>
rw []);

val eval_list_i1_vars = Q.prove (
`!b genv cenv env c s env'.
  ALL_DISTINCT (MAP FST env) ∧
  DISJOINT (set (MAP FST env)) (set (MAP FST env'))
  ⇒
  evaluate_list_i1 b (genv,cenv,env'++env) (c,s)
    (MAP Var_local_i1 (MAP FST env)) ((c,s),Rval (MAP SND env))`,
 induct_on `env` >>
 rw [Once evaluate_i1_cases] >>
 rw [Once evaluate_i1_cases, all_env_i1_to_env_def]
 >- (PairCases_on `h` >>
     fs [ALOOKUP_APPEND] >>
     full_case_tac >>
     imp_res_tac ALOOKUP_MEM >>
     metis_tac [MEM_MAP, FST])
 >- (FIRST_X_ASSUM (qspecl_then [`b`, `genv`, `cenv`, `c`, `s`, `env'++[h]`] mp_tac) >>
     rw [] >>
     metis_tac [DISJOINT_SYM, APPEND, APPEND_ASSOC]));

val pmatch_i1_eval_list = Q.prove (
`(!cenv s p v env env'.
  pmatch_i1 cenv s p v env = Match env' ∧
  ALL_DISTINCT (pat_bindings p (MAP FST env))
  ⇒
  evaluate_list_i1 b (genv,cenv,env') (c,s) (MAP Var_local_i1 (pat_bindings p (MAP FST env))) ((c,s),Rval (MAP SND env'))) ∧
 (!cenv s ps vs env env'.
  pmatch_list_i1 cenv s ps vs env = Match env' ∧
  ALL_DISTINCT (pats_bindings ps (MAP FST env))
  ⇒
  evaluate_list_i1 b (genv,cenv,env') (c,s) (MAP Var_local_i1 (pats_bindings ps (MAP FST env))) ((c,s),Rval (MAP SND env')))`,
 ho_match_mp_tac pmatch_i1_ind >>
 rw [pat_bindings_def, pmatch_i1_def]
 >- (rw [Once evaluate_i1_cases] >>
     rw [Once evaluate_i1_cases, all_env_i1_to_env_def] >>
     `DISJOINT (set (MAP FST env)) (set (MAP FST [(x,v)]))`
                  by rw [DISJOINT_DEF, EXTENSION] >>
     metis_tac [eval_list_i1_vars, APPEND, APPEND_ASSOC])
 >- (`DISJOINT (set (MAP FST env)) (set (MAP FST ([]:(varN,v_i1) alist)))`
                  by rw [DISJOINT_DEF, EXTENSION] >>
     metis_tac [eval_list_i1_vars, APPEND, APPEND_ASSOC])
 >- (every_case_tac >>
     fs [])
 >- (every_case_tac >>
     fs [])
 >- (`DISJOINT (set (MAP FST env)) (set (MAP FST ([]:(varN,v_i1) alist)))`
                  by rw [DISJOINT_DEF, EXTENSION] >>
     metis_tac [eval_list_i1_vars, APPEND, APPEND_ASSOC])
 >- (every_case_tac >>
     fs [] >>
     `ALL_DISTINCT (pat_bindings p (MAP FST env))`
             by fs [Once pat_bindings_accum, ALL_DISTINCT_APPEND] >>
     `MAP FST a = pat_bindings p (MAP FST env)`
                  by (imp_res_tac pmatch_i1_extend >>
                      rw [] >>
                      metis_tac [pat_bindings_accum]) >>
     metis_tac []));

val eval_list_i1_reverse = Q.prove (
`!b env s es s' vs.
  evaluate_list_i1 b env s (MAP Var_local_i1 es) (s, Rval vs)
  ⇒
  evaluate_list_i1 b env s (MAP Var_local_i1 (REVERSE es)) (s, Rval (REVERSE vs))`,
 induct_on `es` >>
 rw []
 >- fs [Once evaluate_i1_cases] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_i1_cases]) >>
 rw [] >>
 fs [Once (hd (CONJUNCTS evaluate_i1_cases))] >>
 rw [] >>
 res_tac >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 pop_assum mp_tac >>
 pop_assum (fn _ => all_tac) >>
 Q.SPEC_TAC (`REVERSE vs'`, `vs`) >>
 Q.SPEC_TAC (`REVERSE es`, `es`) >>
 induct_on `es` >>
 rw []
 >- (ntac 3 (rw [Once evaluate_i1_cases]) >>
     fs [Once evaluate_i1_cases]) >>
 rw [] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_i1_cases]) >>
 rw [] >>
 fs [Once (hd (CONJUNCTS evaluate_i1_cases))] >>
 rw [] >>
 res_tac >>
 rw [Once evaluate_i1_cases] >>
 qexists_tac `s` >>
 rw [] >>
 rw [Once evaluate_i1_cases]);

val fst_alloc_defs = Q.prove (
`!next l. MAP FST (alloc_defs next l) = l`,
 induct_on `l` >>
 rw [alloc_defs_def]);

val alookup_alloc_defs_bounds = Q.prove (
`!next l x n.
  ALOOKUP (alloc_defs next l) x = SOME n
  ⇒
  next <= n ∧ n < next + LENGTH l`,
 induct_on `l` >>
 rw [alloc_defs_def]  >>
 res_tac >>
 DECIDE_TAC);

val alookup_alloc_defs_bounds_rev = Q.prove (
`!next l x n.
  ALOOKUP (REVERSE (alloc_defs next l)) x = SOME n
  ⇒
  next <= n ∧ n < next + LENGTH l`,
 induct_on `l` >>
 rw [alloc_defs_def]  >>
 fs [ALOOKUP_APPEND] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 DECIDE_TAC);

val global_env_inv_flat_extend_lem = Q.prove (
`!genv genv' env env_i1 x n v.
  env_to_i1 genv' env env_i1 ∧
  ALOOKUP env x = SOME v ∧
  ALOOKUP (alloc_defs (LENGTH genv) (MAP FST env)) x = SOME n
  ⇒
  ?v_i1.
    EL n (genv ++ MAP SOME (MAP SND env_i1)) = SOME v_i1 ∧
    v_to_i1 genv' v v_i1`,
 induct_on `env` >>
 rw [v_to_i1_eqns] >>
 PairCases_on `h` >>
 fs [alloc_defs_def] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 fs [v_to_i1_eqns] >>
 rw []
 >- metis_tac [EL_LENGTH_APPEND, NULL, HD]
 >- (FIRST_X_ASSUM (qspecl_then [`genv++[SOME v']`] mp_tac) >>
     rw [] >>
     metis_tac [APPEND, APPEND_ASSOC]));

val global_env_inv_extend = Q.prove (
`!genv mods tops menv env env' env_i1.
  ALL_DISTINCT (MAP FST env') ∧
  env_to_i1 genv env' env_i1
  ⇒
  global_env_inv (genv++MAP SOME (MAP SND (REVERSE env_i1))) FEMPTY (tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP FST env'))) [] ∅ env'`,
 rw [v_to_i1_eqns] >>
 fs [flookup_fupdate_list, ALOOKUP_APPEND] >>
 every_case_tac >>
 rw [RIGHT_EXISTS_AND_THM]
 >- (imp_res_tac ALOOKUP_NONE >>
     fs [MAP_REVERSE, fst_alloc_defs] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [MEM_MAP] >>
     metis_tac [pair_CASES, FST])
 >- metis_tac [ALL_DISTINCT_REVERSE, LENGTH_REVERSE, fst_alloc_defs, alookup_distinct_reverse,
               LENGTH_MAP, length_env_to_i1, alookup_alloc_defs_bounds]
 >- (match_mp_tac global_env_inv_flat_extend_lem >>
     MAP_EVERY qexists_tac [`(REVERSE env')`, `x`] >>
     rw []
     >- metis_tac [env_to_i1_reverse, v_to_i1_weakening]
     >- metis_tac [alookup_distinct_reverse]
     >- metis_tac [alookup_distinct_reverse, MAP_REVERSE, fst_alloc_defs, ALL_DISTINCT_REVERSE]));

val env_to_i1_el = Q.prove (
`!genv env env_i1.
  env_to_i1 genv env env_i1 ⇔
  LENGTH env = LENGTH env_i1 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i1)) ∧ v_to_i1 genv (SND (EL n env)) (SND (EL n env_i1))`,
 induct_on `env` >>
 rw [v_to_i1_eqns]
 >- (cases_on `env_i1` >>
     fs []) >>
 PairCases_on `h` >>
 rw [v_to_i1_eqns] >>
 eq_tac >>
 rw [] >>
 rw []
 >- (cases_on `n` >>
     fs [])
 >- (cases_on `n` >>
     fs [])
 >- (cases_on `env_i1` >>
     fs [] >>
     FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
     SIMP_TAC (srw_ss()) [] >>
     rw [] >>
     qexists_tac `SND h` >>
     rw [] >>
     FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
     rw []));

val find_recfun_el = Q.prove (
`!f funs x e n.
  ALL_DISTINCT (MAP (\(f,x,e). f) funs) ∧
  n < LENGTH funs ∧
  EL n funs = (f,x,e)
  ⇒
  find_recfun f funs = SOME (x,e)`,
 induct_on `funs` >>
 rw [find_recfun_thm] >>
 cases_on `n` >>
 fs [find_recfun_thm] >>
 PairCases_on `h` >>
 fs [find_recfun_thm] >>
 rw [] >>
 res_tac >>
 fs [MEM_MAP, MEM_EL, FORALL_PROD] >>
 metis_tac []);

val global_env_inv_extend2 = Q.prove (
`!genv mods tops menv env tops' env'.
  MAP FST env' = REVERSE (MAP FST tops') ∧
  global_env_inv genv mods tops menv {} env ∧
  global_env_inv genv FEMPTY (FEMPTY |++ tops') [] {} env'
  ⇒
  global_env_inv genv mods (tops |++ tops') menv {} (env'++env)`,
 rw [v_to_i1_eqns, flookup_fupdate_list] >>
 full_case_tac >>
 fs [ALOOKUP_APPEND] >>
 full_case_tac >>
 fs [] >>
 res_tac >>
 fs [] >>
 rpt (pop_assum mp_tac) >>
 rw [] >>
 imp_res_tac ALOOKUP_NONE >>
 imp_res_tac ALOOKUP_MEM >>
 metis_tac [MEM_REVERSE, MEM_MAP, FST]);

val alloc_defs_append = Q.prove (
`!n l1 l2. alloc_defs n (l1++l2) = alloc_defs n l1 ++ alloc_defs (n + LENGTH l1) l2`,
 induct_on `l1` >>
 srw_tac [ARITH_ss] [alloc_defs_def, arithmeticTheory.ADD1]);

val letrec_global_env_lem = Q.prove (
`!funs funs' menv cenv env v x x' genv.
  ALOOKUP (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs' fn)) funs) x = SOME v ∧
  ALOOKUP (REVERSE (alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))) x = SOME x'
  ⇒
  v = SND (EL (LENGTH funs + LENGTH genv - (SUC x')) (MAP (λ(fn,n,e). (fn,Recclosure (menv,cenv,env) funs' fn)) funs))`,
 induct_on `funs` >>
 rw [alloc_defs_append] >>
 PairCases_on `h` >>
 fs [REVERSE_APPEND, alloc_defs_def, ALOOKUP_APPEND] >>
 every_case_tac >>
 fs [] >>
 srw_tac [ARITH_ss] [arithmeticTheory.ADD1] >>
 res_tac >>
 rw [arithmeticTheory.ADD1] >>
 imp_res_tac alookup_alloc_defs_bounds_rev >>
 fs [] >>
 `LENGTH funs + LENGTH genv − x' = SUC (LENGTH funs + LENGTH genv − (x'+1))` by decide_tac >>
 rw []);

val letrec_global_env_lem2 = Q.prove (
`!funs x genv n.
  ALL_DISTINCT (MAP FST funs) ∧
  n < LENGTH funs ∧
  ALOOKUP (REVERSE (alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))) (EL n (MAP FST funs)) = SOME x
  ⇒
  x = LENGTH funs + LENGTH genv - (n + 1)`,
 induct_on `funs` >>
 rw [alloc_defs_def] >>
 PairCases_on `h` >>
 fs [alloc_defs_append, ALOOKUP_APPEND, REVERSE_APPEND] >>
 every_case_tac >>
 fs [alloc_defs_def] >>
 rw [] >>
 cases_on `n = 0` >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 `0 < n` by decide_tac >>
 fs [EL_CONS] >>
 `PRE n < LENGTH funs` by decide_tac >>
 res_tac >>
 srw_tac [ARITH_ss] [] >>
 fs [MEM_MAP, EL_MAP] >>
 LAST_X_ASSUM (qspecl_then [`EL (PRE n) funs`] mp_tac) >>
 rw [MEM_EL] >>
 metis_tac []);

val letrec_global_env_lem3 = Q.prove (
`!funs x genv cenv tops mods.
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
  MEM x (MAP FST funs)
  ⇒
  ∃n y e'.
    FLOOKUP (FEMPTY |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs))) x =
        SOME n ∧ n < LENGTH genv + LENGTH funs ∧
    find_recfun x funs = SOME (y,e') ∧
    EL n (genv ++ MAP (λ(p1,p1',p2).
                           SOME (Closure_i1 (cenv,[]) p1'
                                      (exp_to_i1 mods ((tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs))) \\ p1') p2)))
                      (REVERSE funs)) =
      SOME (Closure_i1 (cenv,[]) y (exp_to_i1 mods ((tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs))) \\ y) e'))`,
 rw [] >>
 fs [MEM_EL] >>
 rw [] >>
 MAP_EVERY qexists_tac [`LENGTH genv + LENGTH funs - (n + 1)`, `FST (SND (EL n funs))`, `SND (SND (EL n funs))`] >>
 srw_tac [ARITH_ss] [EL_APPEND2, flookup_fupdate_list]
 >- (every_case_tac >>
     rw []
     >- (imp_res_tac ALOOKUP_NONE >>
         fs [MAP_REVERSE, fst_alloc_defs] >>
         fs [MEM_MAP, FST_triple] >>
         pop_assum mp_tac >>
         rw [EL_MAP] >>
         qexists_tac `EL n funs` >>
         rw [EL_MEM])
     >- metis_tac [FST_triple, letrec_global_env_lem2])
 >- (rw [find_recfun_lookup] >>
     rpt (pop_assum mp_tac) >>
     Q.SPEC_TAC (`n`, `n`) >>
     induct_on `funs` >>
     rw [] >>
     cases_on `0 < n` >>
     rw [EL_CONS] >>
     PairCases_on `h` >>
     fs []
     >- (every_case_tac >>
         fs [] >>
         `PRE n < LENGTH funs` by decide_tac
         >- (fs [MEM_MAP, FST_triple] >>
             FIRST_X_ASSUM (qspecl_then [`EL (PRE n) funs`] mp_tac) >>
             rw [EL_MAP, EL_MEM])
         >- metis_tac []))
 >- (`LENGTH funs - (n + 1) < LENGTH funs` by decide_tac >>
     `LENGTH funs - (n + 1) < LENGTH (REVERSE funs)` by metis_tac [LENGTH_REVERSE] >>
     srw_tac [ARITH_ss] [EL_MAP, EL_REVERSE] >>
     `PRE (n + 1) = n` by decide_tac >>
     fs [] >>
     `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
     rw []));

val letrec_global_env = Q.prove (
`!genv.
  ALL_DISTINCT (MAP (\(x,y,z). x) funs) ∧
  global_env_inv genv mods tops menv {} env
  ⇒
  global_env_inv (genv ++ (MAP (λ(p1,p1',p2). SOME (Closure_i1 (cenv,[]) p1' p2))
                               (funs_to_i1 mods (tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))
                                                (REVERSE funs))))
               FEMPTY
               (FEMPTY |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))
               []
               ∅
               (build_rec_env funs (menv,cenv,env) [])`,
 rw [build_rec_env_merge] >>
 rw [v_to_i1_eqns, flookup_fupdate_list] >>
 every_case_tac >>
 rw [funs_to_i1_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, RIGHT_EXISTS_AND_THM]
 >- (imp_res_tac ALOOKUP_NONE >>
     fs [MAP_REVERSE, fst_alloc_defs] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [MEM_MAP] >>
     rw [] >>
     fs [LAMBDA_PROD, FORALL_PROD] >>
     PairCases_on `y` >>
     fs [] >>
     metis_tac [])
 >- (imp_res_tac alookup_alloc_defs_bounds_rev >>
     fs [])
 >- (imp_res_tac letrec_global_env_lem >>
     imp_res_tac alookup_alloc_defs_bounds_rev >>
     rw [EL_APPEND2] >>
     fs [] >>
     srw_tac [ARITH_ss] [EL_MAP, EL_REVERSE] >>
     `(PRE (LENGTH funs + LENGTH genv − x')) = (LENGTH funs + LENGTH genv − SUC x')` by decide_tac >>
     rw [] >>
     `?f x e. EL (LENGTH funs + LENGTH genv − SUC x') funs = (f,x,e)` by metis_tac [pair_CASES] >>
     rw [Once v_to_i1_cases] >>
     MAP_EVERY qexists_tac [`mods`,
                            `tops`,
                            `e`,
                            `alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs))`] >>
     rw []
     >- (fs [v_to_i1_eqns, SUBSET_DEF] >>
         rw [] >>
         `¬(ALOOKUP env x''' = NONE)` by metis_tac [ALOOKUP_NONE] >>
         cases_on `ALOOKUP env x'''` >>
         fs [] >>
         res_tac >>
         fs [FLOOKUP_DEF])
     >- metis_tac [v_to_i1_weakening]
     >- rw [MAP_REVERSE, fst_alloc_defs, FST_triple]
     >- (`LENGTH funs + LENGTH genv − SUC x' < LENGTH funs` by decide_tac >>
         metis_tac [find_recfun_el])
     >- metis_tac [letrec_global_env_lem3]));

val dec_to_i1_correct = Q.prove (
`!ck mn mods tops d menv cenv env s s' r genv s_i1 next' tops' d_i1 tdecs tdecs'.
  r ≠ Rerr Rtype_error ∧
  evaluate_dec ck mn (menv,cenv,env) (s,tdecs) d ((s',tdecs'),r) ∧
  global_env_inv genv mods tops menv {} env ∧
  s_to_i1 genv s s_i1 ∧
  dec_to_i1 (LENGTH genv) mn mods tops d = (next',tops',d_i1)
  ⇒
  ?s'_i1 r_i1.
    evaluate_dec_i1 ck genv cenv (s_i1,tdecs) d_i1 ((s'_i1,tdecs'),r_i1) ∧
    (!cenv' env'.
      r = Rval (cenv',env')
      ⇒
      ?env'_i1.
        r_i1 = Rval (cenv', MAP SND env'_i1) ∧
        next' = LENGTH (genv ++ MAP SOME (MAP SND env'_i1)) ∧
        env_to_i1 (genv ++ MAP SOME (MAP SND env'_i1)) env' (REVERSE env'_i1) ∧
        s_to_i1 (genv ++ MAP SOME (MAP SND env'_i1)) s' s'_i1 ∧
        MAP FST env' = REVERSE (MAP FST tops') ∧
        global_env_inv (genv ++ MAP SOME (MAP SND env'_i1)) FEMPTY (FEMPTY |++ tops') [] {} env') ∧
    (!err.
      r = Rerr err
      ⇒
      ?err_i1.
        r_i1 = Rerr err_i1 ∧
        result_to_i1 (\a b c. T) genv (Rerr err) (Rerr err_i1) ∧
        s_to_i1 genv s' s'_i1)`,
 rw [evaluate_dec_cases, evaluate_dec_i1_cases, dec_to_i1_def] >>
 every_case_tac >>
 fs [LET_THM] >>
 rw [FUPDATE_LIST, result_to_i1_eqns]
 >- (`env_all_to_i1 genv mods tops (menv,cenv,env) (genv,cenv,[]) {}`
           by fs [env_all_to_i1_cases, v_to_i1_eqns] >>
     imp_res_tac exp_to_i1_correct >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     fs [DRESTRICT_UNIV, result_to_i1_cases, all_env_to_cenv_def] >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     pop_assum (fn _ => all_tac) >>
     `match_result_to_i1 genv [] (Match env') (pmatch_i1 cenv s''' p v'' [])`
             by metis_tac [APPEND, pmatch_to_i1_correct, v_to_i1_eqns] >>
     cases_on `pmatch_i1 cenv s''' p v'' []` >>
     fs [match_result_to_i1_def] >>
     ONCE_REWRITE_TAC [evaluate_i1_cases] >>
     rw [] >>
     ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
     rw [] >>
     ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
     rw [evaluate_i1_con, do_con_check_def, build_conv_i1_def] >>
     imp_res_tac pmatch_i1_eval_list >>
     pop_assum mp_tac >>
     rw [] >>
     pop_assum (qspecl_then [`genv`, `count'`, `ck`] strip_assume_tac) >>
     MAP_EVERY qexists_tac [`(count',s''')`, `Rval ([], MAP SND (REVERSE a))`] >>
     rw [RIGHT_EXISTS_AND_THM] >>
     `pat_bindings p [] = MAP FST env'`
            by (imp_res_tac pmatch_extend >>
                fs [] >>
                rw [] >>
                metis_tac [LENGTH_MAP, length_env_to_i1])
     >- metis_tac [length_env_to_i1, LENGTH_MAP]
     >- metis_tac [eval_list_i1_reverse, MAP_REVERSE, PAIR_EQ, big_unclocked]
     >- (qexists_tac `REVERSE a` >>
         rw []
         >- metis_tac [LENGTH_MAP, length_env_to_i1]
         >- metis_tac [v_to_i1_weakening]
         >- metis_tac [sv_to_i1_weakening, MAP_REVERSE, LIST_REL_mono]
         >- rw [fst_alloc_defs]
         >- metis_tac [FUPDATE_LIST, global_env_inv_extend]))
 >- (`env_all_to_i1 genv mods tops (menv,cenv,env) (genv,cenv,[]) {}`
           by fs [env_all_to_i1_cases, v_to_i1_eqns] >>
     imp_res_tac exp_to_i1_correct >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     fs [DRESTRICT_UNIV, result_to_i1_cases, all_env_to_cenv_def, s_to_i1_cases] >>
     rw [] >>
     pop_assum (fn _ => all_tac) >>
     `match_result_to_i1 genv [] No_match (pmatch_i1 cenv s''' p v'' [])`
             by metis_tac [APPEND, pmatch_to_i1_correct, v_to_i1_eqns] >>
     cases_on `pmatch_i1 cenv s''' p v'' []` >>
     fs [match_result_to_i1_def] >>
     rw [] >>
     MAP_EVERY qexists_tac [`(count',s''')`, `Rerr (Rraise (Conv_i1 (SOME ("Bind",TypeExn (Short "Bind"))) []))`] >>
     rw []
     >- (ONCE_REWRITE_TAC [evaluate_i1_cases] >>
         rw [] >>
         ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
         rw [] >>
         ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
         rw [evaluate_i1_con, do_con_check_def, build_conv_i1_def] >>
         disj1_tac >>
         qexists_tac `v''` >>
         qexists_tac `(count',s''')` >>
         rw [])
     >- rw [v_to_i1_eqns])
 >- (`env_all_to_i1 genv mods tops (menv,cenv,env) (genv,cenv,[]) {}`
           by fs [env_all_to_i1_cases, v_to_i1_eqns] >>
     imp_res_tac exp_to_i1_correct >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     pop_assum (fn _ => all_tac) >>
     fs [DRESTRICT_UNIV, result_to_i1_cases, all_env_to_cenv_def] >>
     rw []
     >- (MAP_EVERY qexists_tac [`(c',s''''')`, `Rerr (Rraise v')`] >>
         rw [dec_to_dummy_env_def] >>
         ONCE_REWRITE_TAC [evaluate_i1_cases] >>
         rw [] >>
         ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
         rw [] >>
         ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
         rw [evaluate_i1_con, do_con_check_def, build_conv_i1_def])
     >- (qexists_tac `(c',s''''')` >>
         rw [dec_to_dummy_env_def] >>
         ONCE_REWRITE_TAC [evaluate_i1_cases] >>
         rw [] >>
         ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
         rw [] >>
         ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS evaluate_i1_cases)))] >>
         rw [evaluate_i1_con, do_con_check_def, build_conv_i1_def]))
 >- (rw [fupdate_list_foldl] >>
     Q.ABBREV_TAC `tops' = (tops |++ alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs)))` >>
     qexists_tac `MAP (λ(f,x,e). (f, Closure_i1 (cenv,[]) x e)) (funs_to_i1 mods tops' (REVERSE funs))` >>
     rw [GSYM funs_to_i1_dom, ALL_DISTINCT_REVERSE, MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
         GSYM FUPDATE_LIST]
     >- rw [build_rec_env_i1_merge, funs_to_i1_map]
     >- (rw [build_rec_env_merge,MAP_REVERSE, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
             funs_to_i1_map, env_to_i1_el] >>
         rw [EL_MAP] >>
         `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
         rw [] >>
         rw [Once v_to_i1_cases] >>
         MAP_EVERY qexists_tac [`mods`, `tops`, `e`, `alloc_defs (LENGTH genv) (REVERSE (MAP (λ(f,x,e). f) funs))`] >>
         rw [] >>
         UNABBREV_ALL_TAC >>
         rw [SUBSET_DEF, FDOM_FUPDATE_LIST, FUPDATE_LIST_THM]
         >- (fs [v_to_i1_eqns] >>
             `~(ALOOKUP env x' = NONE)` by metis_tac [ALOOKUP_NONE] >>
             cases_on `ALOOKUP env x'` >>
             fs [] >>
             res_tac >>
             fs [FLOOKUP_DEF])
         >- metis_tac [v_to_i1_weakening]
         >- rw [MAP_REVERSE, fst_alloc_defs, FST_triple]
         >- metis_tac [find_recfun_el]
         >- metis_tac [MAP_REVERSE, letrec_global_env_lem3])
     >- (fs [s_to_i1_cases] >>
         metis_tac [sv_to_i1_weakening, LIST_REL_mono])
     >- (rw [MAP_MAP_o, combinTheory.o_DEF, fst_alloc_defs, build_rec_env_merge, MAP_EQ_f] >>
         PairCases_on `x` >>
         rw [])
     >- metis_tac [letrec_global_env])
 >- fs [v_to_i1_eqns]
 >- fs [v_to_i1_eqns]
 >- (rw [PULL_EXISTS, type_defs_to_new_tdecs_def, build_tdefs_def, check_dup_ctors_def] >>
     unabbrev_all_tac >>
     rw [ALL_DISTINCT, Once v_to_i1_cases] >>
     rw [Once v_to_i1_cases, fmap_eq_flookup, flookup_fupdate_list])
 >- fs [v_to_i1_eqns]
 >- fs [v_to_i1_eqns]);

val dec_to_i1_num_bindings = Q.prove (
`!next mn mods tops d next' tops' d_i1.
  dec_to_i1 next mn mods tops d = (next',tops',d_i1)
  ⇒
  next' = next + dec_to_dummy_env d_i1`,
 rw [dec_to_i1_def] >>
 every_case_tac >>
 fs [LET_THM] >>
 rw [dec_to_dummy_env_def, funs_to_i1_map] >>
 metis_tac []);

val decs_to_i1_num_bindings = Q.prove (
`!next mn mods tops ds next' tops' ds_i1.
  decs_to_i1 next mn mods tops ds = (next',tops',ds_i1)
  ⇒
  next' = next + decs_to_dummy_env ds_i1`,
 induct_on `ds` >>
 rw [decs_to_i1_def] >>
 rw [decs_to_dummy_env_def] >>
 fs [LET_THM] >>
 `?next'' tops'' ds_i1''. dec_to_i1 next mn mods tops h = (next'',tops'',ds_i1'')` by metis_tac [pair_CASES] >>
 fs [fupdate_list_foldl] >>
 `?next''' tops''' ds_i1'''. decs_to_i1 next'' mn mods (tops |++ tops'') ds = (next''',tops''',ds_i1''')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [decs_to_dummy_env_def] >>
 res_tac >>
 rw [] >>
 imp_res_tac dec_to_i1_num_bindings >>
 rw [] >>
 decide_tac);

val decs_to_i1_correct = Q.prove (
`!ck mn mods tops ds menv cenv env s s' r genv s_i1 tdecs s'_i1 tdecs' next' tops' ds_i1 cenv'.
  r ≠ Rerr Rtype_error ∧
  evaluate_decs ck mn (menv,cenv,env) (s,tdecs) ds ((s',tdecs'),cenv',r) ∧
  global_env_inv genv mods tops menv {} env ∧
  s_to_i1 genv s s_i1 ∧
  decs_to_i1 (LENGTH genv) mn mods tops ds = (next',tops',ds_i1)
  ⇒
  ∃s'_i1 new_genv new_genv' new_env' r_i1.
   new_genv' = MAP SND new_genv ∧
   evaluate_decs_i1 ck genv cenv (s_i1,tdecs) ds_i1 ((s'_i1,tdecs'),cenv',new_genv',r_i1) ∧
   s_to_i1 (genv ++ MAP SOME new_genv') s' s'_i1 ∧
   (!new_env.
     r = Rval new_env
     ⇒
     r_i1 = NONE ∧
     next' = LENGTH (genv ++ MAP SOME new_genv') ∧
     env_to_i1 (genv ++ MAP SOME new_genv') new_env (REVERSE new_genv) ∧
     MAP FST new_env = REVERSE (MAP FST tops') ∧
     global_env_inv (genv ++ MAP SOME new_genv') FEMPTY (FEMPTY |++ tops') [] {} new_env) ∧
   (!err.
     r = Rerr err
     ⇒
     ?err_i1 new_env.
       r_i1 = SOME err_i1 ∧
       next' ≥ LENGTH (genv++MAP SOME new_genv') ∧
       result_to_i1 (\a b c. T) (genv ++ MAP SOME new_genv') (Rerr err) (Rerr err_i1))`,
 induct_on `ds` >>
 rw [decs_to_i1_def] >>
 qpat_assum `evaluate_decs a b c d e f` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_cases]) >>
 rw [Once evaluate_decs_i1_cases, FUPDATE_LIST, result_to_i1_eqns]
 >- rw [v_to_i1_eqns] >>
 fs [LET_THM] >>
 `?next' tops' d_i1. dec_to_i1 (LENGTH genv) mn mods tops h = (next',tops',d_i1)` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 `?s2' tdecs2. s2 = (s2',tdecs2)` by metis_tac [pair_CASES] >>
 fs [] >>
 imp_res_tac dec_to_i1_correct >>
 pop_assum mp_tac >>
 rw [] >>
 fs [result_to_i1_eqns] >>
 `?envC' env'. v' = (envC',env')` by metis_tac [pair_CASES] >>
 rw [] >>
 fs [fupdate_list_foldl] >>
 rw []
 >- fs [v_to_i1_eqns]
 >- (`?next''' tops''' ds_i1. decs_to_i1 next'' mn mods (tops |++ tops'') ds = (next''',tops''',ds_i1)`
                   by metis_tac [pair_CASES] >>
     fs [result_to_i1_cases] >>
     rw [] >>
     fs []
     >- (MAP_EVERY qexists_tac [`s'_i1`, `[]`, `SOME (Rraise v')`] >>
         rw [] >>
         imp_res_tac dec_to_i1_num_bindings >>
         imp_res_tac decs_to_i1_num_bindings >>
         decide_tac)
     >- (MAP_EVERY qexists_tac [`s'_i1`, `[]`] >>
         rw [] >>
         imp_res_tac dec_to_i1_num_bindings >>
         imp_res_tac decs_to_i1_num_bindings >>
         decide_tac))
 >- (`?next''' tops''' ds_i1. decs_to_i1 (LENGTH genv + LENGTH env'_i1) mn mods (tops |++ tops'') ds = (next''',tops''',ds_i1)`
               by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     `r' ≠ Rerr Rtype_error`
               by (cases_on `r'` >>
                   fs [combine_dec_result_def]) >>
     `global_env_inv (genv ++ MAP SOME (MAP SND env'_i1)) mods (tops |++ tops'') menv ∅ (new_env ++ env)`
             by metis_tac [v_to_i1_weakening, global_env_inv_extend2] >>
     FIRST_X_ASSUM (qspecl_then [`ck`, `mn`, `mods`, `tops |++ tops''`, `menv`,
                                 `merge_alist_mod_env ([],new_tds) cenv`, `new_env ++ env`,
                                 `s2'`, `s'`, `r'`, `genv ++ MAP SOME (MAP SND env'_i1)`, `s'_i1`,
                                 `tdecs2`, `tdecs'`, `next'`, `tops'''`, `ds_i1'`, `new_tds'`] mp_tac) >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i1'`, `env'_i1++new_genv`, `r_i1`] >>
     rw []
     >- (disj2_tac >>
         MAP_EVERY qexists_tac [`(s'_i1,tdecs2)`, `new_tds'`, `new_tds`, `MAP SND env'_i1`, `MAP SND new_genv`] >>
         rw [combine_dec_result_def, MAP_REVERSE])
     >- (cases_on `r'` >>
         fs [combine_dec_result_def])
     >- (cases_on `r'` >>
         full_simp_tac (srw_ss()++ARITH_ss) [combine_dec_result_def])
     >- (cases_on `r'` >>
         fs [combine_dec_result_def] >>
         rw [REVERSE_APPEND] >>
         metis_tac [env_to_i1_append, v_to_i1_weakening, MAP_REVERSE])
     >- (cases_on `r'` >>
         full_simp_tac (srw_ss()++ARITH_ss) [combine_dec_result_def] >>
         rw [])
     >- (cases_on `r'` >>
         fs [combine_dec_result_def] >>
         rw [REVERSE_APPEND] >>
         fs [MAP_REVERSE, GSYM FUPDATE_LIST, FUPDATE_LIST_APPEND] >>
         metis_tac [FUPDATE_LIST_APPEND, global_env_inv_extend2, APPEND_ASSOC, v_to_i1_weakening])
     >- (cases_on `r'` >>
         fs [combine_dec_result_def, MAP_REVERSE, GSYM FUPDATE_LIST, FUPDATE_LIST_APPEND,
             REVERSE_APPEND] >>
         rw [] >>
         imp_res_tac dec_to_i1_num_bindings >>
         imp_res_tac decs_to_i1_num_bindings >>
         decide_tac)));

val global_env_inv_extend_mod = Q.prove (
`!genv new_genv mods tops tops' menv new_env env mn.
  global_env_inv genv mods tops menv ∅ env ∧
  global_env_inv (genv ++ MAP SOME (MAP SND new_genv)) FEMPTY (FEMPTY |++ tops') [] ∅ new_env
  ⇒
  global_env_inv (genv ++ MAP SOME (MAP SND new_genv)) (mods |+ (mn,FEMPTY |++ tops')) tops ((mn,new_env)::menv) ∅ env`,
 rw [last (CONJUNCTS v_to_i1_eqns)]
 >- metis_tac [v_to_i1_weakening] >>
 every_case_tac >>
 rw [FLOOKUP_UPDATE] >>
 fs [v_to_i1_eqns] >>
 res_tac >>
 qexists_tac `map` >>
 rw [] >>
 res_tac  >>
 qexists_tac `n` >>
 qexists_tac `v_i1` >>
 rw []
 >- decide_tac >>
 metis_tac [v_to_i1_weakening, EL_APPEND1]);

val global_env_inv_extend_mod_err = Q.prove (
`!genv new_genv mods tops tops' menv new_env env mn new_genv'.
  mn ∉ set (MAP FST menv) ∧
  global_env_inv genv mods tops menv ∅ env
  ⇒
  global_env_inv (genv ++ MAP SOME (MAP SND new_genv) ++ new_genv')
                 (mods |+ (mn,FEMPTY |++ tops')) tops menv ∅ env`,
 rw [last (CONJUNCTS v_to_i1_eqns)]
 >- metis_tac [v_to_i1_weakening] >>
 rw [FLOOKUP_UPDATE]
 >- metis_tac [ALOOKUP_MEM, MEM_MAP, pair_CASES, FST] >>
 fs [v_to_i1_eqns] >>
 rw [] >>
 res_tac >>
 rw [] >>
 res_tac  >>
 qexists_tac `n` >>
 qexists_tac `v_i1` >>
 rw []
 >- decide_tac >>
 metis_tac [v_to_i1_weakening, EL_APPEND1, APPEND_ASSOC]);

val no_dup_types_to_i1_helper = Q.prove (
`!next mn menv env ds next' menv' ds_i1. 
  decs_to_i1 next mn menv env ds = (next',menv',ds_i1) ⇒
  FLAT (MAP (\d. case d of Dtype tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds)
  =
  FLAT (MAP (\d. case d of Dtype_i1 mn tds => MAP (\(tvs,tn,ctors). tn) tds | _ => []) ds_i1)`,
 induct_on `ds` >>
 rw [decs_to_i1_def] >>
 rw [] >>
 `?next1 new_env1 d'. dec_to_i1 next mn menv env h = (next1,new_env1,d')` by metis_tac [pair_CASES] >>
 fs [LET_THM] >>
 `?next2 new_env2 ds'. (decs_to_i1 next1 mn menv (FOLDL (λenv (k,v). env |+ (k,v)) env new_env1) ds) = (next2,new_env2,ds')` by metis_tac [pair_CASES] >> 
 fs [] >>
 rw [] >>
 every_case_tac >>
 fs [dec_to_i1_def, LET_THM] >>
 rw [] >>
 metis_tac []);

val no_dup_types_to_i1 = Q.prove (
`!next mn menv env ds next' menv' ds_i1. 
  decs_to_i1 next mn menv env ds = (next',menv',ds_i1) ∧
  no_dup_types ds 
  ⇒
  no_dup_types_i1 ds_i1`,
 induct_on `ds` >>
 rw [decs_to_i1_def]
 >- fs [no_dup_types_def, no_dup_types_i1_def, decs_to_types_i1_def] >>
 `?next1 new_env1 d'. dec_to_i1 next mn menv env h = (next1,new_env1,d')` by metis_tac [pair_CASES] >>
 fs [LET_THM] >>
 `?next2 new_env2 ds'. (decs_to_i1 next1 mn menv (FOLDL (λenv (k,v). env |+ (k,v)) env new_env1) ds) = (next2,new_env2,ds')` by metis_tac [pair_CASES] >> 
 fs [] >>
 rw [] >>
 res_tac >>
 cases_on `h` >>
 fs [dec_to_i1_def, LET_THM] >>
 rw [] >>
 fs [decs_to_types_def, no_dup_types_def, decs_to_types_i1_def, no_dup_types_i1_def, ALL_DISTINCT_APPEND] >>
 rw [] >>
 metis_tac [no_dup_types_to_i1_helper]);

val to_i1_prompt_mods_ok = Q.prove (
`!l mn mods tops ds l' tops' ds_i1.
  decs_to_i1 l (SOME mn) mods tops ds = (l',tops',ds_i1)
  ⇒
  prompt_mods_ok (SOME mn) ds_i1`,
 induct_on `ds` >>
 rw [LET_THM, decs_to_i1_def, prompt_mods_ok_def] >>
 rw [] >>
 fs [prompt_mods_ok_def] >>
 `?x y z. dec_to_i1 l (SOME mn) mods tops h = (x,y,z)` by metis_tac [pair_CASES] >>
 fs [] >>
 `?x' y' z'. (decs_to_i1 x (SOME mn) mods (FOLDL (λenv (k,v). env |+ (k,v)) tops y) ds) = (x',y',z')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw []
 >- (every_case_tac >>
     fs [dec_to_i1_def] >>
     every_case_tac >>
     fs [LET_THM])
 >- metis_tac []);

val to_i1_invariant_def = Define `
to_i1_invariant genv mods tops menv env s s_i1 mod_names ⇔
  set (MAP FST menv) ⊆ mod_names ∧
  global_env_inv genv mods tops menv {} env ∧
  s_to_i1 genv s s_i1`;

val top_to_i1_correct = Q.store_thm ("top_to_i1_correct",
`!mods tops t ck menv cenv env s s' r genv s_i1 next' tops' mods' prompt_i1 cenv' tdecs tdecs' mod_names mod_names'.
  r ≠ Rerr Rtype_error ∧
  to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
  evaluate_top ck (menv,cenv,env) (s,tdecs,mod_names) t ((s',tdecs',mod_names'),cenv',r) ∧
  top_to_i1 (LENGTH genv) mods tops t = (next',mods',tops',prompt_i1)
  ⇒
  ∃s'_i1 new_genv r_i1.
   evaluate_prompt_i1 ck genv cenv (s_i1,tdecs,mod_names) prompt_i1 ((s'_i1,tdecs',mod_names'),cenv',new_genv,r_i1) ∧
   next' = LENGTH  (genv ++ new_genv) ∧
   (!new_menv new_env.
     r = Rval (new_menv, new_env)
     ⇒
     r_i1 = NONE ∧
     to_i1_invariant (genv ++ new_genv) mods' tops' (new_menv++menv) (new_env++env) s' s'_i1 mod_names') ∧
   (!err.
     r = Rerr err
     ⇒
     ?err_i1.
       r_i1 = SOME err_i1 ∧
       result_to_i1 (\a b c. T) (genv ++ new_genv) (Rerr err) (Rerr err_i1) ∧
       to_i1_invariant (genv ++ new_genv) mods' tops menv env s' s'_i1 mod_names')`,
 rw [evaluate_top_cases, evaluate_prompt_i1_cases, top_to_i1_def, LET_THM, to_i1_invariant_def] >>
 fs [] >>
 rw []
 >- (`?next'' tops'' d_i1. dec_to_i1 (LENGTH genv) NONE mods tops d = (next'',tops'',d_i1)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     imp_res_tac dec_to_i1_correct >>
     fs [result_to_i1_cases] >>
     fs [fupdate_list_foldl] >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i1`, `MAP SOME (MAP SND env'_i1)`] >>
     rw [mod_cenv_def, update_mod_state_def] >>
     rw [Once evaluate_decs_i1_cases] >>
     rw [Once evaluate_decs_i1_cases] >>
     fs []
     >- (qexists_tac `MAP SND env'_i1` >>
         rw [no_dup_types_i1_def] >>
         fs [evaluate_dec_cases] >>
         rw [] >>
         fs [dec_to_i1_def, LET_THM] >>
         simp [prompt_mods_ok_def, decs_to_types_i1_def] >>
         BasicProvers.VAR_EQ_TAC >>
         simp [] >>
         metis_tac [APPEND, ALL_DISTINCT, APPEND_NIL])
     >- metis_tac [global_env_inv_extend2, v_to_i1_weakening])
 >- (`?next'' tops'' d_i1. dec_to_i1 (LENGTH genv) NONE mods tops d = (next'',tops'',d_i1)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     imp_res_tac dec_to_i1_correct >>
     pop_assum mp_tac >>
     rw [] >>
     rw [mod_cenv_def] >>
     fs [result_to_i1_cases] >>
     rw [] >>
     fs [fupdate_list_foldl] >>
     fs [] >>
     rw []
     >- (MAP_EVERY qexists_tac [`s'_i1`, `GENLIST (\n. NONE) (decs_to_dummy_env [d_i1])`, `SOME (Rraise v')`] >>
         rw []
         >- (ONCE_REWRITE_TAC [evaluate_decs_i1_cases] >>
             rw [] >>
             ONCE_REWRITE_TAC [evaluate_decs_i1_cases] >>
             rw [] >>
             fs [] >>
             rw [update_mod_state_def] >>
             fs [evaluate_dec_cases] >>
             rw [] >>
             fs [dec_to_i1_def, LET_THM] >>
             rw [no_dup_types_i1_def, decs_to_types_i1_def, prompt_mods_ok_def])
         >- (rw [decs_to_dummy_env_def] >>
             metis_tac [dec_to_i1_num_bindings])
         >- metis_tac [v_to_i1_weakening]
         >- metis_tac [v_to_i1_weakening]
         >- (fs [s_to_i1_cases] >>
             metis_tac [sv_to_i1_weakening, LIST_REL_mono]))
     >- (MAP_EVERY qexists_tac [`s'_i1`, `GENLIST (\n. NONE) (decs_to_dummy_env [d_i1])`] >>
         rw []
         >- (ONCE_REWRITE_TAC [evaluate_decs_i1_cases] >>
             rw [] >>
             ONCE_REWRITE_TAC [evaluate_decs_i1_cases] >>
             rw [] >>
             fs [evaluate_dec_i1_cases] >>
             rw [update_mod_state_def] >>
             fs [evaluate_dec_cases] >>
             rw [] >>
             fs [dec_to_i1_def, LET_THM] >>
             rw [no_dup_types_i1_def, decs_to_types_i1_def, prompt_mods_ok_def])
         >- (rw [decs_to_dummy_env_def] >>
             metis_tac [dec_to_i1_num_bindings])
         >- metis_tac [v_to_i1_weakening]
         >- (fs [s_to_i1_cases] >>
             metis_tac [sv_to_i1_weakening, LIST_REL_mono])))
 >- (`?next'' tops'' ds_i1. decs_to_i1 (LENGTH genv) (SOME mn) mods tops ds = (next'',tops'',ds_i1)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     imp_res_tac decs_to_i1_correct >>
     fs [] >>
     rw [mod_cenv_def] >>
     MAP_EVERY qexists_tac [`s'_i1`, `MAP SOME (MAP SND new_genv)`] >>
     rw [fupdate_list_foldl, update_mod_state_def] >>
     fs [SUBSET_DEF] >>
     `prompt_mods_ok (SOME mn) ds_i1` by metis_tac [to_i1_prompt_mods_ok] >>
     metis_tac [global_env_inv_extend_mod, no_dup_types_to_i1, no_dup_types_to_i1])
 >- (`?next'' tops'' ds_i1. decs_to_i1 (LENGTH genv) (SOME mn) mods tops ds = (next'',tops'',ds_i1)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     imp_res_tac decs_to_i1_correct >>
     pop_assum mp_tac >>
     rw [mod_cenv_def] >>
     MAP_EVERY qexists_tac [`s'_i1`,
                            `MAP SOME (MAP SND new_genv) ++ GENLIST (λn. NONE) (decs_to_dummy_env ds_i1 − LENGTH (MAP SND new_genv))`,
                            `SOME err_i1`] >>
     rw []
     >- (MAP_EVERY qexists_tac [`MAP SND new_genv`] >>
         rw [update_mod_state_def] >>
         metis_tac [no_dup_types_to_i1, to_i1_prompt_mods_ok])
     >- (imp_res_tac decs_to_i1_num_bindings >>
         decide_tac)
     >- (fs [result_to_i1_cases] >>
         rw [] >>
         metis_tac [v_to_i1_weakening])
     >- fs [SUBSET_DEF]
     >- (rw [fupdate_list_foldl] >>
         `mn ∉ set (MAP FST menv)`
                    by (fs [SUBSET_DEF] >>
                        metis_tac []) >>
         metis_tac [global_env_inv_extend_mod_err])
         >- (fs [s_to_i1_cases] >>
             metis_tac [sv_to_i1_weakening, LIST_REL_mono])));

val prog_to_i1_correct = Q.store_thm ("prog_to_i1_correct",
`!mods tops ck menv cenv env s prog s' r genv s_i1 next' tops' mods'  cenv' prog_i1 tdecs mod_names tdecs' mod_names'.
  r ≠ Rerr Rtype_error ∧
  evaluate_prog ck (menv,cenv,env) (s,tdecs,mod_names) prog ((s',tdecs',mod_names'),cenv',r) ∧
  to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
  prog_to_i1 (LENGTH genv) mods tops prog = (next',mods',tops',prog_i1)
  ⇒
  ∃s'_i1 new_genv r_i1.
   evaluate_prog_i1 ck genv cenv (s_i1,tdecs,mod_names) prog_i1 ((s'_i1,tdecs',mod_names'),cenv',new_genv,r_i1) ∧
   (!new_menv new_env.
     r = Rval (new_menv, new_env)
     ⇒
     next' = LENGTH (genv ++ new_genv) ∧
     r_i1 = NONE ∧
     to_i1_invariant (genv ++ new_genv) mods' tops' (new_menv++menv) (new_env++env) s' s'_i1 mod_names') ∧
   (!err.
     r = Rerr err
     ⇒
     ?err_i1.
       r_i1 = SOME err_i1 ∧
       result_to_i1 (\a b c. T) (genv ++ new_genv) (Rerr err) (Rerr err_i1))`,
 induct_on `prog` >>
 rw [LET_THM, prog_to_i1_def]
 >- fs [Once evaluate_prog_cases, Once evaluate_prog_i1_cases] >>
 `?next'' mods'' tops'' prompt_i1. top_to_i1 (LENGTH genv) mods tops h = (next'',mods'',tops'',prompt_i1)` by metis_tac [pair_CASES] >>
 fs [] >>
 `?next' mods' tops' prog_i1. prog_to_i1 next'' mods'' tops'' prog = (next',mods',tops',prog_i1)` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 qpat_assum `evaluate_prog a b c d e` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_prog_cases]) >>
 rw [] >>
 rw [Once evaluate_prog_i1_cases] >>
 `?s2' tdecs2' mod_names2'. s2 = (s2',tdecs2',mod_names2')` by metis_tac [pair_CASES] >>
 rw []
 >- (`∃s'_i1 new_genv.
      evaluate_prompt_i1 ck genv cenv (s_i1,tdecs,mod_names) prompt_i1
         ((s'_i1,tdecs2',mod_names2'),new_tds,new_genv,NONE) ∧
      next'' = LENGTH genv + LENGTH new_genv ∧
      to_i1_invariant (genv ++ new_genv) mods'' tops'' (new_mods ++ menv) (new_env ++ env) s2' s'_i1 mod_names2'`
                 by (imp_res_tac top_to_i1_correct >>
                     fs [] >>
                     metis_tac []) >>
     fs [] >>
     FIRST_X_ASSUM (qspecl_then [`mods''`, `tops''`, `ck`, `new_mods ++ menv`, `merge_alist_mod_env new_tds cenv`, `new_env ++ env`, `s2'`, `s'`, `r'`, `genv++new_genv`, `s'_i1`] mp_tac) >>
     rw [] >>
     FIRST_X_ASSUM (qspecl_then [`new_tds'`, `tdecs2'`, `mod_names2'`, `tdecs'`, `mod_names'`] mp_tac) >>
     rw [] >>
     `r' ≠ Rerr Rtype_error`
            by (Cases_on `r'` >>
                fs [combine_mod_result_def]) >>
     rw [] >>
     cases_on `r'` >>
     fs [combine_mod_result_def]
     >- (`?menv' env'. a = (menv',env')` by metis_tac [pair_CASES] >>
         rw [] >>
         MAP_EVERY qexists_tac [`s'_i1'`, `new_genv++new_genv'`] >>
         srw_tac [ARITH_ss] [] >>
         fs [] >>
         metis_tac [])
     >- (fs [result_to_i1_cases] >>
         rw [] >>
         metis_tac [v_to_i1_weakening, APPEND_ASSOC, LENGTH_APPEND, MAP_APPEND]))
 >- (imp_res_tac top_to_i1_correct >>
     pop_assum mp_tac >>
     rw [] >>
     fs [result_to_i1_cases] >>
     rw [] >>
     metis_tac [v_to_i1_weakening, APPEND_ASSOC, LENGTH_APPEND]));

val prog_to_i1_mods = Q.prove (
`!l mods tops prog l' mods' tops' prog_i1.
  prog_to_i1 l mods tops prog = (l',mods', tops',prog_i1)
  ⇒
  prog_to_mods prog
  =
  prog_i1_to_mods prog_i1`,
 induct_on `prog` >>
 rw [prog_to_i1_def, LET_THM, prog_i1_to_mods_def, prog_to_mods_def] >>
 rw [] >>
 `?w x y z. top_to_i1 l mods tops h = (w,x,y,z)` by metis_tac [pair_CASES] >>
 fs [] >>
 `?w' x' y' z'. prog_to_i1 w x y prog = (w',x',y',z')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 fs [top_to_i1_def] >>
 every_case_tac >>
 rw [] >>
 fs [LET_THM]
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [])
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [])
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [prog_to_mods_def, prog_i1_to_mods_def] >>
     metis_tac [])
 >- (fs [prog_to_mods_def, prog_i1_to_mods_def] >>
     metis_tac [])
 >- (`?a b c. dec_to_i1 l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
     fs []));

val prog_to_i1_top_types = Q.prove (
`!l mods tops prog l' mods' tops' prog_i1.
  prog_to_i1 l mods tops prog = (l',mods', tops',prog_i1)
  ⇒
  prog_to_top_types prog
  =
  prog_i1_to_top_types prog_i1`,
 induct_on `prog` >>
 rw [prog_to_i1_def, LET_THM] >>
 rw [] >>
 `?w x y z. top_to_i1 l mods tops h = (w,x,y,z)` by metis_tac [pair_CASES] >>
 fs [prog_to_top_types_def, prog_i1_to_top_types_def] >>
 `?w' x' y' z'. prog_to_i1 w x y prog = (w',x',y',z')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 fs [top_to_i1_def] >>
 every_case_tac >>
 rw [] >>
 fs [LET_THM]
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [])
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l'' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     metis_tac [])
 >- (`?a b c. dec_to_i1 l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     res_tac >>
     rw [] >>
     fs [dec_to_i1_def] >>
     every_case_tac >>
     fs [LET_THM] >>
     rw [decs_to_types_def, decs_to_types_i1_def])
 >- (`?a b c. dec_to_i1 l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw []));

val prog_to_i1_mods_ok = Q.prove (
`!l mods tops prog l' mods' tops' prog_i1.
  prog_to_i1 l mods tops prog = (l',mods', tops',prog_i1)
  ⇒
  EVERY (λp. case p of Prompt_i1 mn ds => prompt_mods_ok mn ds) prog_i1`,
 induct_on `prog` >>
 rw [prog_to_i1_def, LET_THM] >>
 rw [] >>
 `?w x y z. top_to_i1 l mods tops h = (w,x,y,z)` by metis_tac [pair_CASES] >>
 fs [] >>
 `?w' x' y' z'. prog_to_i1 w x y prog = (w',x',y',z')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 fs [top_to_i1_def] >>
 every_case_tac >>
 rw [] >>
 fs [LET_THM]
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l''' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac [to_i1_prompt_mods_ok])
 >- (`?a b c. dec_to_i1 l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [prompt_mods_ok_def] >>
     fs [dec_to_i1_def] >>
     every_case_tac >>
     fs [LET_THM])
 >- (`?a b c. decs_to_i1 l (SOME s) mods tops l''' = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac [to_i1_prompt_mods_ok])
 >- (`?a b c. dec_to_i1 l NONE mods tops d = (a,b,c)` by metis_tac [pair_CASES] >>
     fs [] >>
     metis_tac []));

val whole_prog_to_i1_correct = Q.store_thm ("whole_prog_to_i1_correct",
`!mods tops ck menv cenv env s prog s' r genv s_i1 next' tops' mods'  cenv' prog_i1 tdecs mod_names tdecs' mod_names'.
  r ≠ Rerr Rtype_error ∧
  evaluate_whole_prog ck (menv,cenv,env) (s,tdecs,mod_names) prog ((s',tdecs',mod_names'),cenv',r) ∧
  to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
  prog_to_i1 (LENGTH genv) mods tops prog = (next',mods',tops',prog_i1)
  ⇒
  ∃s'_i1 new_genv r_i1.
   evaluate_whole_prog_i1 ck genv cenv (s_i1,tdecs,mod_names) prog_i1 ((s'_i1,tdecs',mod_names'),cenv',new_genv,r_i1) ∧
   (!new_menv new_env.
     r = Rval (new_menv, new_env)
     ⇒
     next' = LENGTH (genv ++ new_genv) ∧
     r_i1 = NONE ∧
     to_i1_invariant (genv ++ new_genv) mods' tops' (new_menv++menv) (new_env++env) s' s'_i1 mod_names') ∧
   (!err.
     r = Rerr err
     ⇒
     ?err_i1.
       r_i1 = SOME err_i1 ∧
       result_to_i1 (\a b c. T) (genv ++ new_genv) (Rerr err) (Rerr err_i1))`,
 rw [evaluate_whole_prog_i1_def, evaluate_whole_prog_def] >>
 every_case_tac
 >- (imp_res_tac prog_to_i1_correct >>
     fs [] >>
     cases_on `r` >>
     fs [] >>
     metis_tac []) >>
 rw [result_to_i1_cases] >>
 CCONTR_TAC >>
 fs [] >>
 rw [] >>
 fs [no_dup_mods_def, no_dup_mods_i1_def, no_dup_top_types_def, no_dup_top_types_i1_def] >>
 metis_tac [prog_to_i1_mods, prog_to_i1_top_types, prog_to_i1_mods_ok, NOT_EVERY]);

val _ = export_theory ();
