open preamble;
open optionTheory;
open miscTheory;
open libTheory astTheory semanticPrimitivesTheory bigStepTheory terminationTheory;
open libPropsTheory;
open intLang1Theory;
open evalPropsTheory;

val _ = new_theory "toIntLang1Proof";

val LUPDATE_MAP = Q.prove (
`!x n l f. MAP f (LUPDATE x n l) = LUPDATE (f x) n (MAP f l)`,
 induct_on `l` >>
 rw [LUPDATE_def] >>
 cases_on `n` >>
 fs [LUPDATE_def]);

val disjoint_drestrict = Q.prove (
`!s m. DISJOINT s (FDOM m) ⇒ DRESTRICT m (COMPL s) = m`,
 rw [fmap_eq_flookup, FLOOKUP_DRESTRICT] >>
 cases_on `k ∉ s` >>
 rw [] >>
 fs [DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
 metis_tac []);

val compl_insert = Q.prove (
`!s x. COMPL (x INSERT s) = COMPL s DELETE x`,
 rw [EXTENSION] >>
 metis_tac []);

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (exp_to_i1_def, exp_to_i1_ind) =
  tprove_no_defn ((exp_to_i1_def, exp_to_i1_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,y,e) => exp_size e
                                        | INR (INL (x,y,es)) => exps_size es
                                        | INR (INR (INL (x,y,pes))) => pes_size pes
                                        | INR (INR (INR (x,y,funs))) => funs_size funs)` >>
  srw_tac [ARITH_ss] [size_abbrevs, exp_size_def]);
val _ = register "exp_to_i1_ind" exp_to_i1_def exp_to_i1_ind;

val (do_eq_i1_def, do_eq_i1_ind) =
  tprove_no_defn ((do_eq_i1_def, do_eq_i1_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,y) => v_i1_size x
                                        | INR (xs,ys) => v_i14_size xs)`);
val _ = register "do_eq_i1_ind" do_eq_i1_def do_eq_i1_ind;

val (v_to_i1_rules, v_to_i1_ind, v_to_i1_cases) = Hol_reln `
(!bindings lit.
  v_to_i1 bindings (Litv lit) (Litv_i1 lit)) ∧
(!bindings cn vs vs'.
  vs_to_i1 bindings vs vs'
  ⇒ 
  v_to_i1 bindings (Conv cn vs) (Conv_i1 cn vs')) ∧
(!bindings genv mods tops menv cenv env x e env' env_i1.
  bindings = (genv,mods,tops) ∧
  env_to_i1 bindings env env_i1 ∧
  set (MAP FST env') DIFF set (MAP FST env) ⊆ FDOM tops ∧
  global_env_inv bindings menv (set (MAP FST env_i1)) env'
  ⇒ 
  v_to_i1 bindings (Closure (menv,cenv,env++env') x e) 
                   (Closure_i1 (cenv, env_i1) x (exp_to_i1 mods (DRESTRICT tops (COMPL (set (MAP FST env_i1))) \\ x) e))) ∧
                    (*
(!genv mods tops menv cenv env funs x env' new_tops tops'.
  tops' SUBMAP tops ∧
  env_to_i1 genv mods tops' env env' ∧
  (new_tops = FOLDR (\(n,x,y) m. m \\ n) tops' funs)
  ⇒
  v_to_i1 genv mods tops (Recclosure (menv,cenv,env) funs x) 
    (Recclosure_i1 (cenv, FILTER (λ(n,v). n ∉ FDOM new_tops) env') (funs_to_i1 mods new_tops funs) x)) ∧
    *)
(!bindings loc.
  v_to_i1 bindings (Loc loc) (Loc_i1 loc)) ∧
(!bindings.
  vs_to_i1 bindings [] []) ∧
(!bindings v vs v' vs'.
  v_to_i1 bindings v v' ∧
  vs_to_i1 bindings vs vs'
  ⇒
  vs_to_i1 bindings (v::vs) (v'::vs')) ∧
(!bindings.
  env_to_i1 bindings [] []) ∧
(!bindings x v env env' v'. 
  env_to_i1 bindings env env' ∧
  v_to_i1 bindings v v'
  ⇒ 
  env_to_i1 bindings ((x,v)::env) ((x,v')::env')) ∧
(!genv mods tops map shadowers env.
  (!x v.
     x ∉ shadowers ∧
     lookup x env = SOME v
     ⇒
     ?n.
       FLOOKUP map x = SOME n ∧
       n < LENGTH genv ∧
       v_to_i1 (genv,mods,tops) v (EL n genv))
  ⇒ 
  global_env_inv_flat (genv,mods,tops) map shadowers env) ∧
(!genv mods tops menv shadowers env.
  global_env_inv_flat (genv,mods,tops) tops shadowers env ∧
  (!mn env'.
    lookup mn menv = SOME env'
    ⇒
    ?map.
      FLOOKUP mods mn = SOME map ∧
      global_env_inv_flat (genv,mods,tops) map {} env')
  ⇒
  global_env_inv (genv,mods,tops) menv shadowers env)`;

val v_to_i1_eqns = Q.prove (
`(!bindings l v.
  v_to_i1 bindings (Litv l) v ⇔ 
    (v = Litv_i1 l)) ∧
 (!bindings cn vs v.
  v_to_i1 bindings (Conv cn vs) v ⇔ 
    ?vs'. vs_to_i1 bindings vs vs' ∧ (v = Conv_i1 cn vs')) ∧
 (!bindings l v.
  v_to_i1 bindings (Loc l) v ⇔ 
    (v = Loc_i1 l)) ∧
 (!bindings vs.
  vs_to_i1 bindings [] vs ⇔ 
    (vs = [])) ∧
 (!bindings l v vs vs'.
  vs_to_i1 bindings (v::vs) vs' ⇔ 
    ?v' vs''. v_to_i1 bindings v v' ∧ vs_to_i1 bindings vs vs'' ∧ vs' = v'::vs'') ∧
 (!bindings env'.
  env_to_i1 bindings [] env' ⇔
    env' = []) ∧
 (!bindings x v env env'.
  env_to_i1 bindings ((x,v)::env) env' ⇔
    ?v' env''. v_to_i1 bindings v v' ∧ env_to_i1 bindings env env'' ∧ env' = ((x,v')::env'')) ∧
 (!bindings map shadowers env genv.
  global_env_inv_flat bindings map shadowers env ⇔
    ?genv mods tops. bindings = (genv,mods,tops) ∧
    (!x v.
      x ∉ shadowers ∧
      lookup x env = SOME v
      ⇒
      ?n.
        FLOOKUP map x = SOME n ∧
        n < LENGTH genv ∧
        v_to_i1 bindings v (EL n genv))) ∧
(!bindings menv shadowers env genv.
  global_env_inv bindings menv shadowers env ⇔
    ?genv mods tops. bindings = (genv,mods,tops) ∧
    global_env_inv_flat bindings tops shadowers env ∧
    (!mn env'.
      lookup mn menv = SOME env'
      ⇒
      ?map.
        FLOOKUP mods mn = SOME map ∧
        global_env_inv_flat bindings map {} env'))`,
rw [] >>
rw [Once v_to_i1_cases] >>
metis_tac []);

val (result_to_i1_rules, result_to_it_ind, result_to_i1_cases) = Hol_reln `
(∀bindings v v'. 
  v_to_i1 bindings v v'
  ⇒
  result_to_i1 bindings (Rval v) (Rval v')) ∧
(∀bindings v v'. 
  v_to_i1 bindings v v'
  ⇒
  result_to_i1 bindings (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
(!bindings.
  result_to_i1 bindings (Rerr Rtimeout_error) (Rerr Rtimeout_error)) ∧
(!bindings.
  result_to_i1 bindings (Rerr Rtype_error) (Rerr Rtype_error))`;

val result_to_i1_eqns = Q.prove (
`(!bindings v r.
  result_to_i1 bindings (Rval v) r ⇔ 
    ?v'. v_to_i1 bindings v v' ∧ r = Rval v') ∧
 (!bindings v r.
  result_to_i1 bindings (Rerr (Rraise v)) r ⇔ 
    ?v'. v_to_i1 bindings v v' ∧ r = Rerr (Rraise v')) ∧
 (!bindings v r.
  result_to_i1 bindings (Rerr Rtimeout_error) r ⇔ 
    r = Rerr Rtimeout_error) ∧
 (!bindings v r.
  result_to_i1 bindings (Rerr Rtype_error) r ⇔ 
    r = Rerr Rtype_error)`,
rw [result_to_i1_cases] >>
metis_tac []);

val (results_to_i1_rules, results_to_it_ind, results_to_i1_cases) = Hol_reln `
(∀bindings vs vs'. 
  vs_to_i1 bindings vs vs'
  ⇒
  results_to_i1 bindings (Rval vs) (Rval vs')) ∧
(∀bindings v v'. 
  v_to_i1 bindings v v'
  ⇒
  results_to_i1 bindings (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
(!bindings.
  results_to_i1 bindings (Rerr Rtimeout_error) (Rerr Rtimeout_error)) ∧
(!bindings.
  results_to_i1 bindings (Rerr Rtype_error) (Rerr Rtype_error))`;

val results_to_i1_eqns = Q.prove (
`(!bindings vs r.
  results_to_i1 bindings (Rval vs) r ⇔ 
    ?vs'. vs_to_i1 bindings vs vs' ∧ r = Rval vs') ∧
 (!bindings v r.
  results_to_i1 bindings (Rerr (Rraise v)) r ⇔ 
    ?v'. v_to_i1 bindings v v' ∧ r = Rerr (Rraise v')) ∧
 (!bindings v r.
  results_to_i1 bindings (Rerr Rtimeout_error) r ⇔ 
    r = Rerr Rtimeout_error) ∧
 (!bindings v r.
  results_to_i1 bindings (Rerr Rtype_error) r ⇔ 
    r = Rerr Rtype_error)`,
rw [results_to_i1_cases] >>
metis_tac []);

val (s_to_i1'_rules, s_to_i1'_ind, s_to_i1'_cases) = Hol_reln `
(!bindings s s'.
  vs_to_i1 bindings s s'
  ⇒
  s_to_i1' bindings s s')`;

val (s_to_i1_rules, s_to_i1_ind, s_to_i1_cases) = Hol_reln `
(!bindings c s s'.
  s_to_i1' bindings s s'
  ⇒
  s_to_i1 bindings (c,s) (c,s'))`;

val (env_all_to_i1_rules, env_all_to_i1_ind, env_all_to_i1_cases) = Hol_reln `
(!genv mods tops menv cenv env env' env_i1 locals.
  locals = set (MAP FST env) ∧
  global_env_inv (genv,mods,tops) menv locals env' ∧
  env_to_i1 (genv,mods,tops) env env_i1
  ⇒
  env_all_to_i1 (genv,mods,tops) (menv,cenv,env++env') (genv,cenv,env_i1) locals)`;

val do_con_check_i1 = Q.prove (
`!genv mods tops env cn es env_i1 locals. 
  do_con_check (all_env_to_cenv env) cn (LENGTH es) ∧
  env_all_to_i1 (genv,mods,tops) env env_i1 locals
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
`!bindings env cn vs v vs' env_i1 locals.
  (build_conv (all_env_to_cenv env) cn vs = SOME v) ∧
  env_all_to_i1 bindings env env_i1 locals ∧
  vs_to_i1 bindings vs vs'
  ⇒
  ∃v'.
    v_to_i1 bindings v v' ∧
    build_conv_i1 (all_env_i1_to_cenv env_i1) cn vs' = SOME v'`,
 rw [build_conv_def, build_conv_i1_def] >>
 every_case_tac >>
 rw [Once v_to_i1_cases] >>
 fs [env_all_to_i1_cases] >>
 rw [] >>
 fs [all_env_i1_to_cenv_def, all_env_to_cenv_def]);

val global_env_inv_lookup_top = Q.prove (
`!genv mods tops menv shadowers env x v n.
  global_env_inv (genv,mods,tops) menv shadowers env ∧
  lookup x env = SOME v ∧
  x ∉ shadowers ∧
  FLOOKUP tops x = SOME n
  ⇒
  LENGTH genv > n ∧ v_to_i1 (genv,mods,tops) v (EL n genv)`,
 rw [v_to_i1_eqns] >>
 res_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 metis_tac []);

val env_to_i1_lookup = Q.prove (
`!bindings menv env genv x v env'.
  lookup x env = SOME v ∧
  env_to_i1 bindings env env'
  ⇒
  ?v'.
    v_to_i1 bindings v v' ∧
    lookup x env' = SOME v'`,
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
  global_env_inv (genv,mods,tops) menv shadowers env ∧
  lookup mn menv = SOME env'
  ⇒
  ?n. FLOOKUP mods mn = SOME n`,
 rw [] >>
 fs [v_to_i1_eqns] >>
 metis_tac []);

val global_env_inv_lookup_mod2 = Q.prove (
`!genv mods tops menv shadowers env genv mn n env' x v map.
  global_env_inv (genv,mods,tops) menv shadowers env ∧
  lookup mn menv = SOME env' ∧
  lookup x env' = SOME v ∧
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
  global_env_inv (genv,mods,tops) menv shadowers env ∧
  lookup mn menv = SOME env' ∧
  lookup x env' = SOME v ∧
  FLOOKUP mods mn = SOME map ∧
  FLOOKUP map x = SOME n
  ⇒
  LENGTH genv > n ∧ v_to_i1 (genv,mods,tops) v (EL n genv)`,
 rw [] >>
 fs [v_to_i1_eqns] >>
 res_tac >>
 fs [] >>
 rw [] >>
 res_tac >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 metis_tac []);

val env_to_i1_dom = Q.prove (
`!bindings env env_i1.
  env_to_i1 bindings env env_i1
  ⇒
  MAP FST env = MAP FST env_i1`,
 induct_on `env` >>
 rw [v_to_i1_eqns] >>
 PairCases_on `h` >> 
 fs [v_to_i1_eqns] >>
 rw [] >>
 metis_tac []);

val vs_to_i1_append1 = Q.prove (
`!bindings vs v vs' v'.
  vs_to_i1 bindings (vs++[v]) (vs'++[v'])
  ⇔
  vs_to_i1 bindings vs vs' ∧
  v_to_i1 bindings v v'`,
 induct_on `vs` >>
 rw [] >>
 cases_on `vs'` >>
 rw [v_to_i1_eqns] 
 >- (cases_on `vs` >>
     rw [v_to_i1_eqns]) >>
 metis_tac []);

val length_vs_to_i1 = Q.prove (
`!vs bindings vs'. 
  vs_to_i1 bindings vs vs'
  ⇒
  LENGTH vs = LENGTH vs'`,
 induct_on `vs` >>
 rw [v_to_i1_eqns] >>
 fs [] >>
 metis_tac []);

val store_lookup_vs_to_i1 = Q.prove (
`!bindings vs vs_i1 v v_i1 n.
  vs_to_i1 bindings vs vs_i1 ∧
  store_lookup n vs = SOME v ∧
  store_lookup n vs_i1 = SOME v_i1
  ⇒
  v_to_i1 bindings v v_i1`,
 induct_on `vs` >>
 rw [v_to_i1_eqns] >>
 fs [store_lookup_def] >>
 cases_on `n` >>
 fs [] >>
 metis_tac []);

val do_uapp_i1 = Q.prove (
`!bindings s1 s2 uop v1 v2 s1_i1 v1_i1. 
  do_uapp s1 uop v1 = SOME (s2, v2) ∧
  s_to_i1' bindings s1 s1_i1 ∧
  v_to_i1 bindings v1 v1_i1
  ⇒
  ∃v2_i1 s2_i1.
    s_to_i1' bindings s2 s2_i1 ∧
    v_to_i1 bindings v2 v2_i1 ∧
    do_uapp_i1 s1_i1 uop v1_i1 = SOME (s2_i1, v2_i1)`,
 rw [do_uapp_def, do_uapp_i1_def] >>
 every_case_tac >>
 fs [store_alloc_def, LET_THM] >>
 rw [] >>
 fs [v_to_i1_eqns, s_to_i1'_cases, vs_to_i1_append1] >>
 imp_res_tac length_vs_to_i1 >>
 rw []
 >- fs [store_lookup_def] >>
 metis_tac [store_lookup_vs_to_i1]);


val do_eq_i1 = Q.prove (
`(!v1 v2 bindings r v1_i1 v2_i1.
  do_eq v1 v2 = r ∧
  v_to_i1 bindings v1 v1_i1 ∧
  v_to_i1 bindings v2 v2_i1
  ⇒ 
  do_eq_i1 v1_i1 v2_i1 = r) ∧
 (!vs1 vs2 bindings r vs1_i1 vs2_i1.
  do_eq_list vs1 vs2 = r ∧
  vs_to_i1 bindings vs1 vs1_i1 ∧
  vs_to_i1 bindings vs2 vs2_i1
  ⇒ 
  do_eq_list_i1 vs1_i1 vs2_i1 = r)`,
 ho_match_mp_tac do_eq_ind >>
 rw [do_eq_i1_def, do_eq_def, v_to_i1_eqns] >>
 rw [] >>
 rw [do_eq_i1_def, do_eq_def, v_to_i1_eqns] >>
 imp_res_tac length_vs_to_i1 >>
 fs []
 >- metis_tac []
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

val env_all_to_i1_exn = Q.prove (
`!genv tops mods. env_all_to_i1 (genv,mods,tops) exn_env (exn_env_i1 genv) {}`,
 rw [exn_env_def, exn_env_i1_def, env_all_to_i1_cases, emp_def, v_to_i1_eqns] >>
 metis_tac [pair_CASES]);

val vs_to_i1_lupdate = Q.prove (
`!bindings v n s v_i1 n s_i1.
  vs_to_i1 bindings s s_i1 ∧
  v_to_i1 bindings v v_i1
  ⇒
  vs_to_i1 bindings (LUPDATE v n s) (LUPDATE v_i1 n s_i1)`,
 induct_on `n` >>
 rw [v_to_i1_eqns, LUPDATE_def] >>
 cases_on `s` >>
 fs [v_to_i1_eqns, LUPDATE_def]);

val do_app_i1 = Q.prove (
`!genv mods tops env s1 s2 op v1 v2 e env' env_i1 s1_i1 v1_i1 v2_i1 locals.
  do_app env s1 op v1 v2 = SOME (env', s2, e) ∧
  s_to_i1' (genv,mods,tops) s1 s1_i1 ∧
  v_to_i1 (genv,mods,tops) v1 v1_i1 ∧
  v_to_i1 (genv,mods,tops) v2 v2_i1 ∧
  env_all_to_i1 (genv,mods,tops) env env_i1 locals ∧
  genv = all_env_i1_to_genv env_i1
  ⇒
   ∃env'_i1 s2_i1 locals'.
     s_to_i1' (genv,mods,tops) s2 s2_i1 ∧
     env_all_to_i1 (genv,mods,tops) env' env'_i1 locals' ∧
     do_app_i1 env_i1 s1_i1 op v1_i1 v2_i1 = SOME (env'_i1, s2_i1, exp_to_i1 mods (DRESTRICT tops (COMPL locals')) e)`,
 rw [do_app_cases, do_app_i1_def] >>
 fs [v_to_i1_eqns, exp_to_i1_def]
 >- metis_tac [env_all_to_i1_exn]
 >- metis_tac [env_all_to_i1_exn]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (every_case_tac >>
     metis_tac [do_eq_i1, eq_result_11, eq_result_distinct])
 >- (every_case_tac >>
     metis_tac [do_eq_i1, eq_result_distinct, env_all_to_i1_exn])
 >- (qpat_assum `v_to_i1 (genv,mods,tops) (Closure (menv'',cenv'',env'') n e) v1_i1` mp_tac >>
     rw [Once v_to_i1_cases] >>
     rw [] >>
     qexists_tac `n INSERT set (MAP FST env_i1')` >>
     rw [DRESTRICT_DOMSUB, compl_insert, env_all_to_i1_cases] >>
     MAP_EVERY qexists_tac [`bind n v2 env'`, `env'''`] >>
     rw [bind_def, v_to_i1_eqns, all_env_i1_to_genv_def]
     >- metis_tac [env_to_i1_dom] >>
     fs [v_to_i1_eqns] >>
     res_tac >>
     fs [])
 >- cheat
 >- (every_case_tac >>
     fs [store_assign_def, s_to_i1'_cases]
     >- (metis_tac [length_vs_to_i1]) >>
     rw [] >>
     metis_tac [vs_to_i1_lupdate]));

val exp_to_i1_correct = Q.prove (
`(∀b env s e res. 
   evaluate b env s e res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !genv mods tops s' r env_i1 s_i1 e_i1 locals.
     (res = (s',r)) ∧
     env_all_to_i1 (genv,mods,tops) env env_i1 locals ∧
     s_to_i1 (genv,mods,tops) s s_i1 ∧
     (e_i1 = exp_to_i1 mods (DRESTRICT tops (COMPL locals)) e)
     ⇒
     ∃s'_i1 r_i1.
       result_to_i1 (genv,mods,tops) r r_i1 ∧
       s_to_i1 (genv,mods,tops) s' s'_i1 ∧
       evaluate_i1 b env_i1 s_i1 e_i1 (s'_i1, r_i1)) ∧
 (∀b env s es res.
   evaluate_list b env s es res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !genv mods tops s' r env_i1 s_i1 es_i1 locals.
     (res = (s',r)) ∧
     env_all_to_i1 (genv,mods,tops) env env_i1 locals ∧
     s_to_i1 (genv,mods,tops) s s_i1 ∧
     (es_i1 = exps_to_i1 mods (DRESTRICT tops (COMPL locals)) es)
     ⇒
     ?s'_i1 r_i1.
       results_to_i1 (genv,mods,tops) r r_i1 ∧
       s_to_i1 (genv,mods,tops) s' s'_i1 ∧
       evaluate_list_i1 b env_i1 s_i1 es_i1 (s'_i1, r_i1)) ∧
 (∀b env s v pes err_v res. 
   evaluate_match b env s v pes err_v res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !genv mods tops s' r env_i1 s_i1 v_i1 pes_i1 err_v_i1 locals.
     (res = (s',r)) ∧
     env_all_to_i1 (genv,mods,tops) env env_i1 locals ∧
     s_to_i1 (genv,mods,tops) s s_i1 ∧
     v_to_i1 (genv,mods,tops) v v_i1 ∧
     (pes_i1 = pat_exp_to_i1 mods (DRESTRICT tops (COMPL locals)) pes) ∧
     v_to_i1 (genv,mods,tops) err_v err_v_i1
     ⇒
     ?s'_i1 r_i1.
       result_to_i1 (genv,mods,tops) r r_i1 ∧
       s_to_i1 (genv,mods,tops) s' s'_i1 ∧
       evaluate_match_i1 b env_i1 s_i1 v_i1 pes_i1 err_v_i1 (s'_i1, r_i1))`,
 ho_match_mp_tac evaluate_ind >>
 rw [] >>
 rw [Once evaluate_i1_cases,exp_to_i1_def] >>
 TRY (Cases_on `err`) >>
 fs [result_to_i1_eqns, v_to_i1_eqns, results_to_i1_eqns]
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
     fs [lookup_append, all_env_i1_to_env_def, all_env_i1_to_genv_def] >>
     rw []
     >- (every_case_tac >>
         fs []
         >- (fs [v_to_i1_eqns, FLOOKUP_DRESTRICT] >>
             metis_tac [lookup_notin, NOT_SOME_NONE])
         >- metis_tac [env_to_i1_lookup])
     >- (every_case_tac >>
         fs [FLOOKUP_DRESTRICT]
         >- metis_tac [lookup_notin, global_env_inv_lookup_top] >>
         imp_res_tac lookup_in2 >>
         fs [FLOOKUP_DEF, DISJOINT_DEF, EXTENSION] >>
         metis_tac [])
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod1]
     >- metis_tac [NOT_SOME_NONE, global_env_inv_lookup_mod2]
     >- metis_tac [global_env_inv_lookup_mod3])
 >- (* Closure creation *)
    (rw [Once v_to_i1_cases] >>
     fs [env_all_to_i1_cases, all_env_i1_to_cenv_def, all_env_i1_to_env_def] >>
     rw [] >>
     MAP_EVERY qexists_tac [`env'`, `env''`] >>
     imp_res_tac env_to_i1_dom >>
     rw []
     >- (fs [SUBSET_DEF, v_to_i1_eqns] >>
         rw [] >>
         `¬(lookup x env'' = NONE)` by metis_tac [lookup_notin] >>
         cases_on `lookup x env''` >>
         fs [] >>
         res_tac >>
         fs [FLOOKUP_DEF])
     >- (imp_res_tac global_env_inv_lookup_top >>
         fs [] >>
         imp_res_tac disjoint_drestrict >>
         rw []))
 >- (* Unary application *)
    (fs [s_to_i1_cases] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     imp_res_tac do_uapp_i1 >>
     metis_tac [])
 >- metis_tac []
 >- (* Application *)
    (LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s'_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     (qspecl_then [`genv`, `mods`, `tops`, `env`, `s3`, `s4`, `op`, `v1`, `v2`, `e''`, `env'`,
                   `env_i1`, `s'''''''`, `v'`, `v''`, `locals`] mp_tac) do_app_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1` 
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- (* Application *)
    (LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s'_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     (qspecl_then [`genv`, `mods`, `tops`, `env`, `s3`, `s4`, `op`, `v1`, `v2`, `e''`, `env'`,
                   `env_i1`, `s'''''''`, `v'`, `v''`, `locals`] mp_tac) do_app_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1` 
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- (* Application *)
    (LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s_i1`, `locals`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`genv`, `mods`, `tops`, `env_i1`, `s'_i1`, `locals`] mp_tac) >>
     rw [] >>
     fs [s_to_i1_cases] >>
     rw [] >>
     (qspecl_then [`genv`, `mods`, `tops`, `env`, `s3`, `s4`, `Opapp`, `v1`, `v2`, `e3`, `env'`,
                   `env_i1`, `s''''''`, `v'`, `v''`, `locals`] mp_tac) do_app_i1 >>
     rw [] >>
     `genv = all_env_i1_to_genv env_i1` 
                by fs [all_env_i1_to_genv_def, env_all_to_i1_cases] >>
     fs [] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
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
     `env_all_to_i1 (genv,mods,tops) (menv,cenv,bind n v env) 
                    (genv, cenv, (n,v')::env') (n INSERT locals)`
                by (fs [env_all_to_i1_cases] >>
                    MAP_EVERY qexists_tac [`bind n v env''`, `env'''`] >>
                    fs [bind_def, v_to_i1_eqns] >>
                    rw []) >>
     metis_tac [compl_insert, DRESTRICT_DOMSUB, bind_def])
 >- metis_tac []
 >- metis_tac []
 >- (* Letrec *)
    (rw [markerTheory.Abbrev_def] >>
     cheat)
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (* Pattern matching *)
    cheat
 >- (* Pattern matching *)
    cheat);

val _ = export_theory ();
