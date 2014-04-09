open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open modLangTheory;
open conLangTheory;
open modLangProofTheory;
open decLangProofTheory;
open evalPropsTheory;
open compilerTerminationTheory;

val _ = new_theory "conLangProof";

val fmap_inverse_def = Define `
fmap_inverse m1 m2 =
  !k. k ∈ FDOM m1 ⇒ ?v. FLOOKUP m1 k = SOME v ∧ FLOOKUP m2 v = SOME k`;

val map_some_eq = Q.prove (
`!l1 l2. MAP SOME l1 = MAP SOME l2 ⇔ l1 = l2`,
 induct_on `l1` >>
 rw [] >>
 Cases_on `l2` >>
 rw []);

val map_some_eq_append = Q.prove (
`!l1 l2 l3. MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3 ⇔ l1 ++ l2 = l3`,
metis_tac [map_some_eq, MAP_APPEND]);

val _ = augment_srw_ss [rewrites [map_some_eq,map_some_eq_append]];

val lookup_reverse = Q.prove (
`∀x l.
 ALL_DISTINCT (MAP FST l) ⇒
 lookup x (REVERSE l) = lookup x l`,
 induct_on `l` >>
 rw [] >>
 PairCases_on `h` >>
 rw [lookup_append] >>
 every_case_tac >>
 fs [] >>
 imp_res_tac lookup_in2);

val lookup_con_id_rev = Q.prove (
`!cn fenvC envC.
  ALL_DISTINCT (MAP FST fenvC) ⇒
  lookup_con_id cn (merge_envC ([],REVERSE fenvC) envC)
  =
  lookup_con_id cn (merge_envC ([],fenvC) envC)`,
 rw [] >>
 cases_on `cn` >>
 PairCases_on `envC` >>
 fs [merge_envC_def, lookup_con_id_def, merge_def, lookup_append] >>
 every_case_tac >>
 fs [] >>
 metis_tac [lookup_reverse, SOME_11, NOT_SOME_NONE]);

val same_tid_diff_ctor = Q.prove (
`!cn1 cn2 t1 t2.
  same_tid t1 t2 ∧ ~same_ctor (cn1, t1) (cn2, t2)
  ⇒
  (cn1 ≠ cn2) ∨ (cn1 = cn2 ∧ ?mn1 mn2. t1 = TypeExn mn1 ∧ t2 = TypeExn mn2 ∧ mn1 ≠ mn2)`,
rw [] >>
cases_on `t1` >>
cases_on `t2` >>
fs [same_tid_def, same_ctor_def]);

val build_rec_env_i2_help_lem = Q.prove (
`∀funs env funs'.
FOLDR (λ(f,x,e) env'. bind f (Recclosure_i2 env funs' f) env') env' funs =
merge (MAP (λ(fn,n,e). (fn, Recclosure_i2 env funs' fn)) funs) env'`,
Induct >>
rw [merge_def, bind_def] >>
PairCases_on `h` >>
rw []);

val build_rec_env_i2_merge = Q.store_thm ("build_rec_env_i2_merge",
`∀funs funs' env env'.
  build_rec_env_i2 funs env env' =
  merge (MAP (λ(fn,n,e). (fn, Recclosure_i2 env funs fn)) funs) env'`,
rw [build_rec_env_i2_def, build_rec_env_i2_help_lem]);

val funs_to_i2_map = Q.prove (
`!funs.
  funs_to_i2 cenv funs = MAP (\(f,x,e). (f,x,exp_to_i2 cenv e)) funs`,
 induct_on `funs` >>
 rw [exp_to_i2_def] >>
 PairCases_on `h` >>
 rw [exp_to_i2_def]);

val has_exns_def = Define `
has_exns gtagenv ⇔
  FLOOKUP gtagenv ("Bind", TypeExn (Short "Bind")) = SOME (bind_tag,0:num) ∧
  FLOOKUP gtagenv ("Div", TypeExn (Short "Div")) = SOME (div_tag,0) ∧
  FLOOKUP gtagenv ("Eq", TypeExn (Short "Eq")) = SOME (eq_tag,0)`;

val gtagenv_wf_def = Define `
gtagenv_wf gtagenv ⇔
  (∀cn l. FLOOKUP gtagenv cn ≠ SOME (tuple_tag,l)) ∧
  has_exns gtagenv ∧
  (∀t1 t2 tag l1 l2 cn cn'.
    (* Comment out same_tid because we're not using separate tag spaces per type *)
    (* same_tid t1 t2 ∧ *)
    FLOOKUP gtagenv (cn,t1) = SOME (tag,l1) ∧
    FLOOKUP gtagenv (cn',t2) = SOME (tag,l2) ⇒
    cn = cn' ∧ t1 = t2)`;

val envC_tagged_def = Define `
envC_tagged envC tagenv gtagenv =
  (!cn num_args t.
    lookup_con_id cn envC = SOME (num_args, t)
    ⇒
    ?tag t'.
      lookup_tag_env (SOME cn) tagenv = (tag, t') ∧
      FLOOKUP gtagenv (id_to_n cn, t) = SOME (tag,num_args) ∧
      (if tag = tuple_tag then t' = NONE else t' = SOME t))`;

val exhaustive_env_correct_def = Define `
exhaustive_env_correct exh gtagenv ⇔
  (!t.
     (?cn. (cn, TypeId t) ∈ FDOM gtagenv)
     ⇒
     ?tags.
       FLOOKUP exh t = SOME tags ∧
       (!cn tag l. FLOOKUP gtagenv (cn,TypeId t) = SOME (tag,l) ⇒ MEM tag tags))`;

val cenv_inv_def = Define `
cenv_inv envC exh tagenv gtagenv ⇔
 envC_tagged envC tagenv gtagenv ∧
 exhaustive_env_correct exh gtagenv ∧
 gtagenv_wf gtagenv`;

val (v_to_i2_rules, v_to_i2_ind, v_to_i2_cases) = Hol_reln `
(!gtagenv lit.
  v_to_i2 gtagenv (Litv_i1 lit) (Litv_i2 lit)) ∧
(!gtagenv vs vs'.
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Conv_i1 NONE vs) (Conv_i2 (tuple_tag,NONE) vs')) ∧
(!gtagenv cn tn tag vs vs'.
  FLOOKUP gtagenv (cn,tn) = SOME (tag, LENGTH vs) ∧
  vs_to_i2 gtagenv vs vs'
  ⇒
  v_to_i2 gtagenv (Conv_i1 (SOME (cn,tn)) vs) (Conv_i2 (tag,SOME tn) vs')) ∧
(!gtagenv env x e env_i2 envC exh tagenv.
  env_to_i2 gtagenv env env_i2 ∧
  cenv_inv envC exh tagenv gtagenv
  ⇒
  v_to_i2 gtagenv (Closure_i1 (envC,env) x e) (Closure_i2 env_i2 x (exp_to_i2 tagenv e))) ∧
(!gtagenv env funs x envC env_i2 exh tagenv.
  env_to_i2 gtagenv env env_i2 ∧
  cenv_inv envC exh tagenv gtagenv
  ⇒
  v_to_i2 gtagenv (Recclosure_i1 (envC,env) funs x) (Recclosure_i2 env_i2 (funs_to_i2 tagenv funs) x)) ∧
(!gtagenv loc.
  v_to_i2 gtagenv (Loc_i1 loc) (Loc_i2 loc)) ∧
(!gtagenv.
  vs_to_i2 gtagenv [] []) ∧
(!gtagenv v vs v' vs'.
  v_to_i2 gtagenv v v' ∧
  vs_to_i2 gtagenv vs vs'
  ⇒
  vs_to_i2 gtagenv (v::vs) (v'::vs')) ∧
(!gtagenv.
  env_to_i2 gtagenv [] []) ∧
(!gtagenv x v env env' v'.
  env_to_i2 gtagenv env env' ∧
  v_to_i2 gtagenv v v'
  ⇒
  env_to_i2 gtagenv ((x,v)::env) ((x,v')::env'))`;

val v_to_i2_eqns = Q.prove (
`(!gtagenv l v.
  v_to_i2 gtagenv (Litv_i1 l) v ⇔
    (v = Litv_i2 l)) ∧
 (!gtagenv cn vs v.
  v_to_i2 gtagenv (Conv_i1 cn vs) v ⇔
    (?vs' tag gtagenv' t'.
       vs_to_i2 gtagenv vs vs' ∧ (v = Conv_i2 (tag,t') vs') ∧
       (cn = NONE ∧ tag = tuple_tag ∧ t' = NONE ∨
        ?cn' tn.
          FLOOKUP gtagenv (cn',tn) = SOME (tag,LENGTH vs) ∧
          cn = SOME (cn',tn) ∧ t' = SOME tn))) ∧
 (!gtagenv l v.
  v_to_i2 gtagenv (Loc_i1 l) v ⇔
    (v = Loc_i2 l)) ∧
 (!gtagenv vs.
  vs_to_i2 gtagenv [] vs ⇔
    (vs = [])) ∧
 (!gtagenv l v vs vs'.
  vs_to_i2 gtagenv (v::vs) vs' ⇔
    ?v' vs''. v_to_i2 gtagenv v v' ∧ vs_to_i2 gtagenv vs vs'' ∧ vs' = v'::vs'') ∧
 (!gtagenv env'.
  env_to_i2 gtagenv [] env' ⇔
    env' = []) ∧
 (!gtagenv x v env env'.
  env_to_i2 gtagenv ((x,v)::env) env' ⇔
    ?v' env''. v_to_i2 gtagenv v v' ∧ env_to_i2 gtagenv env env'' ∧ env' = ((x,v')::env''))`,
rw [] >>
rw [Once v_to_i2_cases] >>
metis_tac []);

val gtagenv_weak_def = Define `
gtagenv_weak gtagenv1 gtagenv2 ⇔
  gtagenv1 SUBMAP gtagenv2 ∧
  (!cn l. FLOOKUP gtagenv2 cn ≠ SOME (tuple_tag,l)) ∧
  (* Don't weaken by adding a constructor to an existing type. This is necessary for pattern exhaustiveness checking. *)
  (!t. (?cn. (cn,t) ∈ FDOM gtagenv1) ⇒ !cn. (cn,t) ∈ FDOM gtagenv2 ⇒ (cn,t) ∈ FDOM gtagenv1) ∧
  (!t1 t2 tag cn cn' l1 l2.
     (* Comment out same_tid because we're not using separate tag spaces per type *)
     (* same_tid t1 t2 ∧ *)
     FLOOKUP gtagenv2 (cn,t1) = SOME (tag,l1) ∧
     FLOOKUP gtagenv2 (cn',t2) = SOME (tag,l2)
     ⇒
     cn = cn' ∧ t1 = t2)`;

val exhaustive_env_weak = Q.prove (
`!gtagenv gtagenv' exh.
    exhaustive_env_correct exh gtagenv ∧
    gtagenv_weak gtagenv gtagenv'
    ⇒
    ?exh'.
      exhaustive_env_correct exh' gtagenv'`,
 rw [gtagenv_weak_def, exhaustive_env_correct_def] >>
 qexists_tac `exh|++ARB` >>
 rw [] >>
 cases_on `?cn. (cn,TypeId t) ∈ FDOM gtagenv` >>
 res_tac >>
 fs [] >>
 rw []
 >- (`(cn,TypeId t) ∈ FDOM gtagenv` by metis_tac [] >>
     `?tags. FLOOKUP exh t = SOME tags ∧ 
             ∀cn tag l. FLOOKUP gtagenv (cn,TypeId t) = SOME (tag,l) ⇒ MEM tag tags` by metis_tac [] >>
     fs [flookup_fupdate_list] >>
     rw [] >>
     `ALOOKUP (REVERSE ARB) t = NONE:num list option` by cheat >>
     qexists_tac `tags` >>
     rw [] >>
     `(cn'',TypeId t) ∈ FDOM gtagenv` 
               by (fs [FLOOKUP_DEF] >> 
                   metis_tac [FLOOKUP_DEF]) >>
     `?tag l. FLOOKUP gtagenv (cn'',TypeId t) = SOME (tag,l)` 
                by (fs [FLOOKUP_DEF] >>
                    metis_tac [SUBMAP_DEF]) >>
     metis_tac [SOME_11, PAIR_EQ, FLOOKUP_SUBMAP])
 >- cheat);

val v_to_i2_weakening = Q.prove (
`(!gtagenv v v_i2.
  v_to_i2 gtagenv v v_i2
  ⇒
    !gtagenv'. gtagenv_weak gtagenv gtagenv'
    ⇒
    v_to_i2 gtagenv' v v_i2) ∧
 (!gtagenv vs vs_i2.
  vs_to_i2 gtagenv vs vs_i2
  ⇒
   !gtagenv'. gtagenv_weak gtagenv gtagenv'
    ⇒
    vs_to_i2 gtagenv' vs vs_i2) ∧
 (!gtagenv env env_i2.
  env_to_i2 gtagenv env env_i2
  ⇒
   !gtagenv'. gtagenv_weak gtagenv gtagenv'
    ⇒
    env_to_i2 gtagenv' env env_i2)`,
 ho_match_mp_tac v_to_i2_ind >>
 rw [v_to_i2_eqns] >>
 res_tac
 >- metis_tac [gtagenv_weak_def, FLOOKUP_SUBMAP]
 >- (fs [cenv_inv_def, gtagenv_wf_def, envC_tagged_def] >>
     imp_res_tac exhaustive_env_weak >>
     rw [Once v_to_i2_cases] >>
     MAP_EVERY qexists_tac [`exh'`, `tagenv`] >>
     fs [gtagenv_weak_def, cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >> 
     rw []
     >- (res_tac >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac [])
 >- (fs [cenv_inv_def, gtagenv_wf_def, envC_tagged_def] >>
     imp_res_tac exhaustive_env_weak >>
     rw [Once v_to_i2_cases] >>
     MAP_EVERY qexists_tac [`exh'`, `tagenv`] >>
     fs [gtagenv_weak_def, cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >> 
     rw []
     >- (res_tac >>
         metis_tac [FLOOKUP_SUBMAP])
     >- (fs [has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac []));

val (result_to_i2_rules, result_to_i2_ind, result_to_i2_cases) = Hol_reln `
(∀gtagenv v v'.
  f gtagenv v v'
  ⇒
  result_to_i2 f gtagenv (Rval v) (Rval v')) ∧
(∀gtagenv v v'.
  v_to_i2 gtagenv v v'
  ⇒
  result_to_i2 f gtagenv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
(!gtagenv.
  result_to_i2 f gtagenv (Rerr Rtimeout_error) (Rerr Rtimeout_error)) ∧
(!gtagenv.
  result_to_i2 f gtagenv (Rerr Rtype_error) (Rerr Rtype_error))`;

val result_to_i2_eqns = Q.prove (
`(!gtagenv v r.
  result_to_i2 f gtagenv (Rval v) r ⇔
    ?v'. f gtagenv v v' ∧ r = Rval v') ∧
 (!gtagenv v r.
  result_to_i2 f gtagenv (Rerr (Rraise v)) r ⇔
    ?v'. v_to_i2 gtagenv v v' ∧ r = Rerr (Rraise v')) ∧
 (!gtagenv v r.
  result_to_i2 f gtagenv (Rerr Rtimeout_error) r ⇔
    r = Rerr Rtimeout_error) ∧
 (!gtagenv v r.
  result_to_i2 f gtagenv (Rerr Rtype_error) r ⇔
    r = Rerr Rtype_error)`,
rw [result_to_i2_cases] >>
metis_tac []);

val (s_to_i2'_rules, s_to_i2'_ind, s_to_i2'_cases) = Hol_reln `
(!gtagenv s s'.
  vs_to_i2 gtagenv s s'
  ⇒
  s_to_i2' gtagenv s s')`;

val (s_to_i2_rules, s_to_i2_ind, s_to_i2_cases) = Hol_reln `
(!gtagenv c s s'.
  s_to_i2' gtagenv s s'
  ⇒
  s_to_i2 gtagenv (c,s) (c,s'))`;

val length_vs_to_i2 = Q.prove (
`!vs gtagenv vs'.
  vs_to_i2 gtagenv vs vs'
  ⇒
  LENGTH vs = LENGTH vs'`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 rw [] >>
 metis_tac []);

val length_evaluate_list_i2 = Q.prove (
`!b env s gtagenv es s' vs.
  evaluate_list_i2 b env s (exps_to_i2 gtagenv es) (s', Rval vs)
  ⇒
  LENGTH es = LENGTH vs`,
 induct_on `es` >>
 rw [exp_to_i2_def] >>
 cases_on `vs` >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_i2_cases]) >>
 rw [] >>
 metis_tac []);

val env_to_i2_el = Q.prove (
`!gtagenv env env_i2.
  env_to_i2 gtagenv env env_i2 ⇔
  LENGTH env = LENGTH env_i2 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i2)) ∧ v_to_i2 gtagenv (SND (EL n env)) (SND (EL n env_i2))`,
 induct_on `env` >>
 rw [v_to_i2_eqns]
 >- (cases_on `env_i2` >>
     fs []) >>
 PairCases_on `h` >>
 rw [v_to_i2_eqns] >>
 eq_tac >>
 rw [] >>
 rw []
 >- (cases_on `n` >>
     fs [])
 >- (cases_on `n` >>
     fs [])
 >- (cases_on `env_i2` >>
     fs [] >>
     FIRST_ASSUM (qspecl_then [`0`] mp_tac) >>
     SIMP_TAC (srw_ss()) [] >>
     rw [] >>
     qexists_tac `SND h` >>
     rw [] >>
     FIRST_X_ASSUM (qspecl_then [`SUC n`] mp_tac) >>
     rw []));

val vs_to_i2_lupdate = Q.prove (
`!gtagenv v n s v_i2 n s_i2.
  vs_to_i2 gtagenv s s_i2 ∧
  v_to_i2 gtagenv v v_i2
  ⇒
  vs_to_i2 gtagenv (LUPDATE v n s) (LUPDATE v_i2 n s_i2)`,
 induct_on `n` >>
 rw [v_to_i2_eqns, LUPDATE_def] >>
 cases_on `s` >>
 fs [v_to_i2_eqns, LUPDATE_def]);

val match_result_to_i2_def = Define
`(match_result_to_i2 gtagenv (Match env) (Match env_i2) ⇔
   env_to_i2 gtagenv env env_i2) ∧
 (match_result_to_i2 gtagenv No_match No_match = T) ∧
 (match_result_to_i2 gtagenv Match_type_error Match_type_error = T) ∧
 (match_result_to_i2 gtagenv _ _ = F)`;

val store_lookup_vs_to_i2 = Q.prove (
`!gtagenv vs vs_i2 v v_i2 n.
  vs_to_i2 gtagenv vs vs_i2 ∧
  store_lookup n vs = SOME v ∧
  store_lookup n vs_i2 = SOME v_i2
  ⇒
  v_to_i2 gtagenv v v_i2`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 fs [store_lookup_def] >>
 cases_on `n` >>
 fs [] >>
 metis_tac []);

val store_lookup_vs_to_i2_2 = Q.prove (
`!gtagenv vs vs_i2 v v_i2 n.
  vs_to_i2 gtagenv vs vs_i2 ∧
  store_lookup n vs = SOME v
  ⇒
  ?v'. store_lookup n vs_i2 = SOME v'`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 fs [store_lookup_def] >>
 cases_on `n` >>
 fs [] >>
 metis_tac []);

val pat_bindings_i2_accum = Q.store_thm ("pat_bindings_ai2_ccum",
`(!p acc. pat_bindings_i2 p acc = pat_bindings_i2 p [] ++ acc) ∧
 (!ps acc. pats_bindings_i2 ps acc = pats_bindings_i2 ps [] ++ acc)`,
 Induct >>
 rw []
 >- rw [pat_bindings_i2_def]
 >- rw [pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]
 >- rw [pat_bindings_i2_def]
 >- metis_tac [APPEND_ASSOC, pat_bindings_i2_def]);

val pat_bindings_to_i2 = Q.prove (
`!tagenv p x. pat_bindings_i2 (pat_to_i2 tagenv p) x = pat_bindings p x`,
 ho_match_mp_tac pat_to_i2_ind >>
 rw [pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 induct_on `ps` >>
 rw [] >>
 fs [pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 metis_tac [APPEND_11, pat_bindings_accum, pat_bindings_i2_accum]);

val pmatch_to_i2_correct = Q.prove (
`(!envC s p v env r env_i2 s_i2 v_i2 tagenv gtagenv exh.
  r ≠ Match_type_error ∧
  cenv_inv envC exh tagenv gtagenv ∧
  pmatch_i1 envC s p v env = r ∧
  s_to_i2' gtagenv s s_i2 ∧
  v_to_i2 gtagenv v v_i2 ∧
  env_to_i2 gtagenv env env_i2
  ⇒
  ?r_i2.
    pmatch_i2 exh s_i2 (pat_to_i2 tagenv p) v_i2 env_i2 = r_i2 ∧
    match_result_to_i2 gtagenv r r_i2) ∧
 (!envC s ps vs env r env_i2 s_i2 vs_i2 tagenv gtagenv exh.
  r ≠ Match_type_error ∧
  cenv_inv envC exh tagenv gtagenv ∧
  pmatch_list_i1 envC s ps vs env = r ∧
  s_to_i2' gtagenv s s_i2 ∧
  vs_to_i2 gtagenv vs vs_i2 ∧
  env_to_i2 gtagenv env env_i2
  ⇒
  ?r_i2.
    pmatch_list_i2 exh s_i2 (MAP (pat_to_i2 tagenv) ps) vs_i2 env_i2 = r_i2 ∧
    match_result_to_i2 gtagenv r r_i2)`,
 ho_match_mp_tac pmatch_i1_ind >>
 rw [pmatch_i1_def, pmatch_i2_def, pat_to_i2_def, match_result_to_i2_def] >>
 fs [match_result_to_i2_def, bind_def, v_to_i2_eqns] >>
 rw [pmatch_i2_def, match_result_to_i2_def]
 >- (every_case_tac >>
     fs []
     >- (`lookup_tag_env (SOME n) tagenv = (tag, if tag = tuple_tag then NONE else SOME t')`
                  by (fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >>
                      res_tac >>
                      fs [] >>
                      metis_tac [length_vs_to_i2, SOME_11, same_ctor_and_same_tid, PAIR_EQ]) >>
         rw [pmatch_i2_def] >>
         fs []
         >- (fs [cenv_inv_def,gtagenv_wf_def] >>
             metis_tac []) >>
         `(?tid. t' = TypeId tid) ∨ (?exid. t' = TypeExn exid)`
                    by (Cases_on `t'` >>
                        metis_tac []) >>
         rw [pmatch_i2_def]
         >- (`?tags. FLOOKUP exh tid = SOME tags ∧ MEM tag tags`
                    by (fs [cenv_inv_def, exhaustive_env_correct_def, FLOOKUP_DEF] >>
                        rw [] >>
                        metis_tac []) >>
             rw [] >>
             metis_tac [])
         >- (fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >>
             metis_tac [length_vs_to_i2, SOME_11, same_ctor_and_same_tid, PAIR_EQ])
         >- metis_tac [tid_or_exn_11, SOME_11, PAIR_EQ]
         >- (fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def] >>
             metis_tac [length_vs_to_i2, SOME_11, same_ctor_and_same_tid, PAIR_EQ]))
     >- (fs [cenv_inv_def, envC_tagged_def] >>
         res_tac >>
         rw [] >>
         `(?tid. t' = TypeId tid) ∨ (?exid. t' = TypeExn exid)`
                    by (Cases_on `t'` >>
                        metis_tac []) >>
         `(?tid. r = TypeId tid) ∨ (?exid. r = TypeExn exid)`
                    by (Cases_on `r` >>
                        metis_tac []) >>
         imp_res_tac same_tid_diff_ctor >>
         fs [same_tid_def] >>
         rw [] >>
         `tag' ≠ tuple_tag` by metis_tac [gtagenv_wf_def] >>
         fs [] >>
         rw [pmatch_i2_def]
         >- metis_tac [gtagenv_wf_def]
         >- metis_tac [gtagenv_wf_def]
         >- (`?tags. FLOOKUP exh tid = SOME tags ∧ MEM tag tags`
                    by (fs [cenv_inv_def, exhaustive_env_correct_def, FLOOKUP_DEF] >>
                        rw [] >>
                        metis_tac []) >>
             rw [match_result_to_i2_def]  >>
             `?tags. FLOOKUP exh tid = SOME tags ∧ MEM tag' tags`
                    by (fs [cenv_inv_def, exhaustive_env_correct_def, FLOOKUP_DEF] >>
                        rw [] >>
                        metis_tac []) >>
             fs [] >>
             rw [] >>
             fs [])
         >- metis_tac [gtagenv_wf_def]
         >- metis_tac [gtagenv_wf_def]
         >- rw [match_result_to_i2_def]
         >- metis_tac [tid_or_exn_11, gtagenv_wf_def]
         >- metis_tac [tid_or_exn_11, gtagenv_wf_def]
         >- rw [match_result_to_i2_def]))
 >- (PairCases_on `tagenv` >>
     fs [pmatch_i2_def, lookup_tag_env_def] >>
     rw [] >>
     metis_tac [length_vs_to_i2])
 >- (every_case_tac >>
     fs [s_to_i2'_cases] >>
     imp_res_tac store_lookup_vs_to_i2 >>
     fs [store_lookup_def] >>
     metis_tac [length_vs_to_i2])
 >- (every_case_tac >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     pop_assum mp_tac >>
     pop_assum mp_tac >>
     res_tac >>
     rw [] >>
     CCONTR_TAC >>
     fs [match_result_to_i2_def] >>
     metis_tac [match_result_to_i2_def, match_result_distinct]));

val (env_all_to_i2_rules, env_all_to_i2_ind, env_all_to_i2_cases) = Hol_reln `
(!genv envC gtagenv exh env env_i2 genv_i2.
  cenv_inv envC exh tagenv gtagenv ∧
  vs_to_i2 gtagenv genv genv_i2 ∧
  env_to_i2 gtagenv env env_i2
  ⇒
  env_all_to_i2 tagenv (MAP SOME genv,envC,env) (exh,MAP SOME genv_i2,env_i2) gtagenv)`;

val env_to_i2_append = Q.prove (
`!gtagenv env1 env2 env1' env2'.
  env_to_i2 gtagenv env1 env1' ∧
  env_to_i2 gtagenv env2 env2'
  ⇒
  env_to_i2 gtagenv (env1++env2) (env1'++env2')`,
 induct_on `env1` >>
 rw [v_to_i2_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i2_eqns]);

val env_to_i2_lookup = Q.prove (
`!gtagenv env x v env'.
  lookup x env = SOME v ∧
  env_to_i2 gtagenv env env'
  ⇒
  ?v'.
    v_to_i2 gtagenv v v' ∧
    lookup x env' = SOME v'`,
 induct_on `env` >>
 rw [] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `h0 = x` >>
 fs [] >>
 rw [] >>
 fs [v_to_i2_eqns]);

val genv_to_i2_lookup = Q.prove (
`!gtagenv genv n genv'.
  vs_to_i2 gtagenv genv genv' ∧
  LENGTH genv > n
  ⇒
  v_to_i2 gtagenv (EL n genv) (EL n genv')`,
 induct_on `genv` >>
 srw_tac [ARITH_ss] [v_to_i2_eqns] >>
 cases_on `n` >>
 srw_tac [ARITH_ss] [v_to_i2_eqns]);

val vs_to_i2_append1 = Q.prove (
`!gtagenv vs v vs' v'.
  vs_to_i2 gtagenv (vs++[v]) (vs'++[v'])
  ⇔
  vs_to_i2 gtagenv vs vs' ∧
  v_to_i2 gtagenv v v'`,
 induct_on `vs` >>
 rw [] >>
 cases_on `vs'` >>
 rw [v_to_i2_eqns]
 >- (cases_on `vs` >>
     rw [v_to_i2_eqns]) >>
 metis_tac []);

val vs_to_i2_append = Q.prove (
`!gtagenv vs1 vs1' vs2 vs2'.
  (LENGTH vs2 = LENGTH vs2' ∨ LENGTH vs1 = LENGTH vs1')
  ⇒
  (vs_to_i2 gtagenv (vs1++vs2) (vs1'++vs2') ⇔
   vs_to_i2 gtagenv vs1 vs1' ∧ vs_to_i2 gtagenv vs2 vs2')`,
 induct_on `vs1` >>
 rw [v_to_i2_eqns] >>
 eq_tac >>
 rw [] >>
 imp_res_tac length_vs_to_i2 >>
 fs [] >>
 cases_on `vs1'` >>
 fs [] >>
 rw [] >>
 full_simp_tac (srw_ss()++ARITH_ss) [] >>
 metis_tac []);

val do_uapp_correct = Q.prove (
`!s uop v s' v' gtagenv s_i2 v_i2.
  do_uapp_i1 s uop v = SOME (s',v') ∧
  s_to_i2' gtagenv s s_i2 ∧
  v_to_i2 gtagenv v v_i2
  ⇒
  ∃s'_i2 v'_i2.
    s_to_i2' gtagenv s' s'_i2 ∧
    v_to_i2 gtagenv v' v'_i2 ∧
    do_uapp_i2 s_i2 (uop_to_i2 uop) v_i2 = SOME (s'_i2,v'_i2)`,
 cases_on `uop` >>
 rw [uop_to_i2_def, do_uapp_i1_def, do_uapp_i2_def, LET_THM, store_alloc_def, s_to_i2'_cases] >>
 rw [vs_to_i2_append1, v_to_i2_eqns]
 >- metis_tac [length_vs_to_i2] >>
 every_case_tac >>
 fs [v_to_i2_eqns]
 >- metis_tac [store_lookup_vs_to_i2_2, NOT_SOME_NONE]
 >- metis_tac [store_lookup_vs_to_i2]);

val exn_env_i2_correct = Q.prove (
`!gtagenv.
  env_all_to_i2 tagenv env (exh,genv,env_i2) gtagenv
  ⇒
  env_all_to_i2 (FST (SND init_tagenv_state)) (exn_env_i1 (all_env_i1_to_genv env))
    (exh, genv, exn_env_i2) gtagenv`,
 rw [env_all_to_i2_cases, exn_env_i1_def, exn_env_i2_def, emp_def, v_to_i2_eqns,
     all_env_i1_to_genv_def, all_env_i2_to_genv_def, init_tagenv_state_def] >>
 qexists_tac `genv'` >>
 qexists_tac `genv_i2` >>
 fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def, lookup_con_id_def] >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 rw [id_to_n_def] >>
 fs [has_exns_def] >>
 fs [flookup_fupdate_list, lookup_tag_env_def, lookup_tag_flat_def, all_env_i1_to_genv_def, all_env_i2_to_genv_def] >>
 metis_tac []);

val do_eq_i2 = Q.prove (
`(!v1 v2 tagenv r v1_i2 v2_i2 gtagenv.
  env_all_to_i2 tagenv env env_i2 gtagenv ∧
  do_eq_i1 v1 v2 = r ∧
  v_to_i2 gtagenv v1 v1_i2 ∧
  v_to_i2 gtagenv v2 v2_i2
  ⇒
  do_eq_i2 v1_i2 v2_i2 = r) ∧
 (!vs1 vs2 tagenv r vs1_i2 vs2_i2 gtagenv.
  env_all_to_i2 tagenv env env_i2 gtagenv ∧
  do_eq_list_i1 vs1 vs2 = r ∧
  vs_to_i2 gtagenv vs1 vs1_i2 ∧
  vs_to_i2 gtagenv vs2 vs2_i2
  ⇒
  do_eq_list_i2 vs1_i2 vs2_i2 = r)`,
 ho_match_mp_tac do_eq_i1_ind >>
 rw [do_eq_i2_def, do_eq_i1_def, v_to_i2_eqns] >>
 rw [] >>
 rw [do_eq_i2_def, do_eq_i1_def, v_to_i2_eqns] >>
 imp_res_tac length_vs_to_i2 >>
 fs [env_all_to_i2_cases] >>
 rw []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac [cenv_inv_def, gtagenv_wf_def, SOME_11, PAIR_EQ, pair_CASES]
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def])
 >- (fs [Once v_to_i2_cases] >>
     rw [do_eq_i2_def]) >>
 res_tac >>
 every_case_tac >>
 fs [] >>
 metis_tac []);

val do_app_i2_correct = Q.prove (
`!env s op v1 v2 s' e env' tagenv s_i2 v1_i2 v2_i2 env_i2 gtagenv genv exh.
  do_app_i1 env s op v1 v2 = SOME (env',s',e) ∧
  env_all_to_i2 tagenv env (exh,genv,env_i2) gtagenv ∧
  s_to_i2' gtagenv s s_i2 ∧
  v_to_i2 gtagenv v1 v1_i2 ∧
  v_to_i2 gtagenv v2 v2_i2
  ⇒
  ∃s'_i2 env'_i2 tagenv'.
    env_all_to_i2 tagenv' env' (exh,genv,env'_i2) gtagenv ∧
    s_to_i2' gtagenv s' s'_i2 ∧
    do_app_i2 env_i2 s_i2 op v1_i2 v2_i2 = SOME (env'_i2,s'_i2,exp_to_i2 tagenv' e)`,
 cases_on `op` >>
 rw [do_app_i1_def, do_app_i2_def]
 >- (cases_on `v2` >>
     fs [] >>
     cases_on `v1` >>
     fs [v_to_i2_eqns] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     fs [v_to_i2_eqns] >>
     rw [exp_to_i2_def]
     >- (qexists_tac `FST (SND init_tagenv_state)` >>
         rw []
         >- metis_tac [exn_env_i2_correct, all_env_i2_to_genv_def]
         >- rw [init_tagenv_state_def, flookup_fupdate_list, lookup_tag_env_def, lookup_tag_flat_def])
     >- (qexists_tac `FST (SND init_tagenv_state)` >>
         rw []
         >- metis_tac [exn_env_i2_correct, all_env_i2_to_genv_def]
         >- rw [init_tagenv_state_def, flookup_fupdate_list, lookup_tag_env_def, lookup_tag_flat_def])
     >- metis_tac []
     >- metis_tac [])
 >- (cases_on `v2` >>
     fs [] >>
     cases_on `v1` >>
     fs [v_to_i2_eqns] >>
     rw [] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     rw [exp_to_i2_def, exn_env_i2_correct] >>
     metis_tac [])
 >- (every_case_tac >>
     fs [] >>
     rw [exp_to_i2_def]
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct]
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct]
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct]
     >- (qexists_tac `FST (SND init_tagenv_state)` >>
         rw []
         >- metis_tac [exn_env_i2_correct, all_env_i2_to_genv_def]
         >- rw [init_tagenv_state_def, flookup_fupdate_list, lookup_tag_env_def, lookup_tag_flat_def])
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct]
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct])
 >- (every_case_tac >>
     fs [] >>
     pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i2_cases]) >>
     rw []
     >- (qexists_tac `tagenv'` >>
         rw [] >>
         fs [env_all_to_i2_cases, bind_def] >>
         rw [v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def, get_tagenv_def] >>
         fs [cenv_inv_def])
     >- (CCONTR_TAC >>
         fs [] >>
         rw [] >>
         fs [find_recfun_lookup] >>
         induct_on `l'` >>
         rw [] >>
         PairCases_on `h` >>
         fs [exp_to_i2_def] >>
         every_case_tac >>
         fs [])
     >- (qexists_tac `tagenv'` >>
         rw [] >>
         fs [env_all_to_i2_cases, bind_def] >>
         rw [v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def,
             build_rec_env_i1_merge, build_rec_env_i2_merge, merge_def] >>
         fs [funs_to_i2_map]
         >- fs [cenv_inv_def]
         >- (match_mp_tac env_to_i2_append >>
             rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el, EL_MAP] >>
             `?f x e. EL n l' = (f,x,e)` by metis_tac [pair_CASES] >>
             rw [] >>
             rw [Once v_to_i2_cases] >>
             metis_tac [funs_to_i2_map])
         >- (fs [find_recfun_lookup] >>
             induct_on `l'` >>
             rw [] >>
             PairCases_on `h` >>
             fs [exp_to_i2_def] >>
             every_case_tac >>
             fs [])
         >- (fs [find_recfun_lookup] >>
             induct_on `l'` >>
             rw [] >>
             PairCases_on `h` >>
             fs [exp_to_i2_def] >>
             every_case_tac >>
             fs [get_tagenv_def])))
 >- (every_case_tac >>
     fs [] >>
     rw [] >>
     fs [v_to_i2_eqns, store_assign_def]
     >- metis_tac [length_vs_to_i2, s_to_i2'_cases] >>
     rw [exp_to_i2_def, s_to_i2'_cases] >>
     metis_tac [vs_to_i2_lupdate, s_to_i2'_cases]));

val lookup_tag_env_NONE = Q.prove (
`lookup_tag_env NONE tagenv = (tuple_tag, NONE)`,
PairCases_on `tagenv` >>
rw [lookup_tag_env_def]);

val exp_to_i2_correct = Q.prove (
`(∀b env s e res.
   evaluate_i1 b env s e res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !tagenv s' r env_i2 s_i2 e_i2 gtagenv.
     (res = (s',r)) ∧
     env_all_to_i2 tagenv env env_i2 gtagenv ∧
     s_to_i2 gtagenv s s_i2 ∧
     e_i2 = exp_to_i2 tagenv e
     ⇒
     ∃s'_i2 r_i2.
       result_to_i2 v_to_i2 gtagenv r r_i2 ∧
       s_to_i2 gtagenv s' s'_i2 ∧
       evaluate_i2 b env_i2 s_i2 e_i2 (s'_i2, r_i2)) ∧
 (∀b env s es res.
   evaluate_list_i1 b env s es res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !tagenv s' r env_i2 s_i2 es_i2 gtagenv.
     (res = (s',r)) ∧
     env_all_to_i2 tagenv env env_i2 gtagenv ∧
     s_to_i2 gtagenv s s_i2 ∧
     (es_i2 = exps_to_i2 tagenv es)
     ⇒
     ?s'_i2 r_i2.
       result_to_i2 vs_to_i2 gtagenv r r_i2 ∧
       s_to_i2 gtagenv s' s'_i2 ∧
       evaluate_list_i2 b env_i2 s_i2 es_i2 (s'_i2, r_i2)) ∧
 (∀b env s v pes err_v res.
   evaluate_match_i1 b env s v pes err_v res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !tagenv s' r env_i2 s_i2 v_i2 pes_i2 err_v_i2 gtagenv.
     (res = (s',r)) ∧
     env_all_to_i2 tagenv env env_i2 gtagenv ∧
     s_to_i2 gtagenv s s_i2 ∧
     v_to_i2 gtagenv v v_i2 ∧
     pes_i2 = pat_exp_to_i2 tagenv pes ∧
     v_to_i2 gtagenv err_v err_v_i2
     ⇒
     ?s'_i2 r_i2.
       result_to_i2 v_to_i2 gtagenv r r_i2 ∧
       s_to_i2 gtagenv s' s'_i2 ∧
       evaluate_match_i2 b env_i2 s_i2 v_i2 pes_i2 err_v_i2 (s'_i2, r_i2))`,
 ho_match_mp_tac evaluate_i1_ind >>
 rw [] >>
 rw [Once evaluate_i2_cases,exp_to_i2_def] >>
 TRY (Cases_on `err`) >>
 fs [result_to_i2_eqns, v_to_i2_eqns]
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (* Constructor application *)
    (res_tac >>
     rw [] >>
     fs [env_all_to_i2_cases, build_conv_i1_def] >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i2`, `Rval (Conv_i2 (lookup_tag_env cn tagenv) v')`] >>
     rw [] >>
     Cases_on `cn` >>
     fs [] >>
     rw [v_to_i2_eqns, lookup_tag_env_NONE] >>
     fs [all_env_i1_to_cenv_def] >>
     every_case_tac >>
     fs [get_tagenv_def] >>
     rw [v_to_i2_eqns] >>
     fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def, do_con_check_def] >>
     rw [] >>
     metis_tac [length_evaluate_list_i2, length_vs_to_i2, FST])
 >- metis_tac []
 >- (* Local variable lookup *)
    (fs [env_all_to_i2_cases, all_env_i2_to_env_def] >>
     rw [] >>
     fs [all_env_i1_to_env_def] >>
     metis_tac [env_to_i2_lookup])
 >- (* Global variable lookup *)
    (fs [env_all_to_i2_cases, all_env_i2_to_genv_def] >>
     rw [] >>
     fs [all_env_i1_to_genv_def] >>
     `n < LENGTH genv` by decide_tac >>
     `LENGTH genv_i2 = LENGTH genv` by metis_tac [length_vs_to_i2] >>
     fs [EL_MAP] >>
     metis_tac [genv_to_i2_lookup])
 >- (rw [Once v_to_i2_cases] >>
     fs [env_all_to_i2_cases] >>
     rw [all_env_i1_to_env_def, all_env_i2_to_env_def, all_env_i1_to_cenv_def] >>
     metis_tac [])
 >- (* Uapp *)
    (res_tac >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     `?s3_i2 v'_i2. do_uapp_i2 s''' (uop_to_i2 uop) v'' = SOME (s3_i2, v'_i2) ∧
       s_to_i2' gtagenv s3 s3_i2 ∧ v_to_i2 gtagenv v' v'_i2` by metis_tac [do_uapp_correct] >>
     metis_tac [])
 >- metis_tac []
 >- (* App *)
    (LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s'_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     (qspecl_then [`env`, `s3`, `op`, `v1`, `v2`, `s4`, `e''`, `env'`,
                   `tagenv`, `s'''''''`, `v'`, `v''`, `SND (SND env_i2)`, `gtagenv`, `FST (SND env_i2)`, `FST env_i2`] mp_tac) do_app_i2_correct >>
     rw [] >>
     PairCases_on `env_i2` >>
     fs [] >>
     metis_tac [])
 >- (* App *)
    (LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s'_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     (qspecl_then [`env`, `s3`, `op`, `v1`, `v2`, `s4`, `e''`, `env'`,
                   `tagenv`, `s'''''''`, `v'`, `v''`, `SND (SND env_i2)`, `gtagenv`, `FST (SND env_i2)`, `FST env_i2`] mp_tac) do_app_i2_correct >>
     rw [] >>
     PairCases_on `env_i2` >>
     fs [] >>
     metis_tac [])
 >- (* App *)
    (LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s'_i2`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     (qspecl_then [`env`, `s3`, `Opapp`, `v1`, `v2`, `s4`, `e3`, `env'`,
                   `tagenv`, `s''''''`, `v'`, `v''`, `SND (SND env_i2)`, `gtagenv`, `FST (SND env_i2)`, `FST env_i2`] mp_tac) do_app_i2_correct >>
     rw [] >>
     PairCases_on `env_i2` >>
     fs [] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (* If *)
    (fs [do_if_i2_def, do_if_i1_def] >>
     every_case_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     res_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i2''`, `r_i2`] >>
     rw [] >>
     disj1_tac
     >- (qexists_tac `Litv_i2 (Bool F)` >>
         fs [v_to_i2_eqns, exp_to_i2_def] >>
         metis_tac [])
     >- (qexists_tac `Litv_i2 (Bool T)` >>
         fs [v_to_i2_eqns, exp_to_i2_def] >>
         metis_tac []))
 >- metis_tac []
 >- metis_tac []
 >- (* Match *)
   (pop_assum mp_tac >>
     res_tac >>
     rw [] >>
     FIRST_X_ASSUM (qspecl_then [`tagenv`, `env_i2`, `s'_i2'`, `v''`,
                                  `Conv_i2 (bind_tag,SOME (TypeExn (Short "Bind"))) []`, `gtagenv`] mp_tac) >>
     rw [] >>
     fs [env_all_to_i2_cases] >>
     rw [] >>
     fs [cenv_inv_def, envC_tagged_def, gtagenv_wf_def, has_exns_def] >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     rw [] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Let *)
    (`?exh' genv' env'. env_i2 = (exh',genv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     `env_all_to_i2 tagenv (genv,cenv,opt_bind n v env) (exh',genv', opt_bind n v' env') gtagenv`
                by (fs [env_all_to_i2_cases] >>
                    fs [opt_bind_def, v_to_i2_eqns] >>
                    rw [] >>
                    every_case_tac >>
                    fs [] >>
                    rw [v_to_i2_eqns]) >>
     metis_tac [bind_def])
 >- metis_tac []
 >- metis_tac []
 >- (* Letrec *)
    (pop_assum mp_tac >>
     rw [] >>
     `?exh' genv' env'. env_i2 = (exh',genv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     `env_all_to_i2 tagenv (genv,cenv,build_rec_env_i1 funs (cenv,env) env)
                           (exh',genv',build_rec_env_i2 (funs_to_i2 tagenv funs) env' env')
                           gtagenv`
         by (fs [env_all_to_i2_cases] >>
             rw [build_rec_env_i1_merge, build_rec_env_i2_merge, merge_def] >>
             rw [] >>
             match_mp_tac env_to_i2_append >>
             rw [] >>
             rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el, EL_MAP] >>
             `?f x e. EL n funs = (f,x,e)` by metis_tac [pair_CASES] >>
             rw [] >>
             rw [Once v_to_i2_cases] >>
             metis_tac [funs_to_i2_map]) >>
      res_tac >>
      MAP_EVERY qexists_tac [`s'_i2'`, `r_i2'`] >>
      rw [] >>
      disj1_tac >>
      rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD])
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i2_cases, env_all_to_i2_cases] >>
     rw [] >>
     `match_result_to_i2 gtagenv (Match env')
            (pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2'` >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     FIRST_X_ASSUM (qspecl_then [`tagenv`, `gtagenv`, `exh`, `a`, `genv_i2`, `s''`] mp_tac) >>
     rw [] >>
     fs [] >>
     MAP_EVERY qexists_tac [`(c, s'''')`, `r_i2`] >>
     metis_tac [pat_bindings_to_i2])
 >- (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i2_cases, env_all_to_i2_cases] >>
     rw [] >>
     `match_result_to_i2 gtagenv No_match
            (pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 exh s'' (pat_to_i2 tagenv p) v_i2 env_i2'` >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     pop_assum mp_tac >>
     pop_assum (qspecl_then [`tagenv`, `(count',s'')`, `v_i2`, `err_v_i2`, `gtagenv`, `exh`, `env_i2'`, `genv_i2`] mp_tac) >>
     rw [] >>
     metis_tac [pat_bindings_to_i2]));

val merge_envC_empty = Q.prove (
`!envC. merge_envC (emp,emp) envC = envC ∧ merge_envC ([],[]) envC = envC`,
rw [emp_def] >>
PairCases_on `envC` >>
rw [merge_envC_def, merge_def]);

(*
val lookup_tag_env_insert = Q.prove (
`(!cn tag tagenv. lookup_tag_env (SOME (Short cn)) (insert_tag_env cn tag tagenv) = tag) ∧
 (!cn cn' tag tagenv.
   cn' ≠ Short cn
   ⇒
   lookup_tag_env (SOME cn') (insert_tag_env cn tag tagenv) = lookup_tag_env (SOME cn') tagenv)`,
 rw [] >>
 PairCases_on `tagenv` >>
 rw [lookup_tag_env_def, insert_tag_env_def, lookup_tag_flat_def, FLOOKUP_UPDATE] >>
 every_case_tac >>
 fs []);

val alloc_tags_flat = Q.prove (
`!mn tagenv_st defs.
  alloc_tags mn tagenv_st defs =
  FOLDL (λst' (cn,l,t). alloc_tag t cn st') tagenv_st
        (FLAT (MAP (\(tvs,tn,ctors). (MAP (\(cn,ts). (cn, LENGTH ts, TypeId (mk_id mn tn))) ctors)) defs))`,
 induct_on `defs` >>
 rw [alloc_tags_def, LET_THM] >>
 PairCases_on `h` >>
 rw [LET_THM, alloc_tags_def, FOLDL_APPEND, FOLDL_MAP, LAMBDA_PROD]);
 *)

val check_dup_ctors_flat = Q.prove (
`!defs.
  check_dup_ctors defs =
  ALL_DISTINCT (MAP FST (build_tdefs mn defs))`,
 rw [check_dup_ctors_thm, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, build_tdefs_def,
     MAP_REVERSE, ALL_DISTINCT_REVERSE]);

val gtagenv_weak_refl = Q.prove (
`!gtagenv envC tagenv.
  gtagenv_wf gtagenv
  ⇒
  gtagenv_weak gtagenv gtagenv`,
 rw [gtagenv_weak_def] >>
 metis_tac [SUBMAP_REFL, gtagenv_wf_def]);

val gtagenv_weak_trans = Q.prove (
`!gtagenv1 gtagenv2 gtagenv3.
  gtagenv_weak gtagenv1 gtagenv2 ∧
  gtagenv_weak gtagenv2 gtagenv3
  ⇒
  gtagenv_weak gtagenv1 gtagenv3`,
 rw [gtagenv_weak_def] >>
 fs [FLOOKUP_DEF, SUBMAP_DEF] >>
 metis_tac []);

val get_next_def = Define `
get_next (a,b,c,d) = a`;

val alloc_tags_invariant_def = Define `
alloc_tags_invariant tids tagenv_st gtagenv ⇔
  IMAGE SND (FDOM gtagenv) ⊆ tids ∧
  get_next tagenv_st > tuple_tag ∧
  (!cn t tag l. FLOOKUP gtagenv (cn,t) = SOME (tag,l) ⇒ get_next tagenv_st > tag)`;

val flat_envC_tagged_def = Define `
 flat_envC_tagged envC tagenv gtagenv ⇔
   ∀cn num_args t.
     lookup cn envC = SOME (num_args,t) ⇒
     ∃tag.
       lookup_tag_flat cn tagenv = tag ∧
       FLOOKUP gtagenv (cn,t) = SOME (FST tag,num_args)`;

       (*
val flat_envC_tagged_weakening = Q.prove (
`!envC tagenv gtagenv gtagenv'.
  flat_envC_tagged envC tagenv gtagenv ∧
  gtagenv_weak gtagenv gtagenv'
  ⇒
  flat_envC_tagged envC tagenv gtagenv'`,
 rw [flat_envC_tagged_def, gtagenv_weak_def] >>
 res_tac >>
 metis_tac [FLOOKUP_SUBMAP]);

val flat_envC_tagged_append = Q.prove (
`ALL_DISTINCT (MAP FST tagenv2) ∧
 set (MAP FST envC1) = set (MAP FST tagenv1) ∧
 flat_envC_tagged envC1 (FEMPTY |++ tagenv1) gtagenv ∧
 flat_envC_tagged envC2 (FEMPTY |++ REVERSE tagenv2) gtagenv
 ⇒
 flat_envC_tagged (envC1++envC2) (FEMPTY |++ (tagenv2 ++ tagenv1)) gtagenv`,
 rw [flat_envC_tagged_def] >>
 fs [lookup_append, lookup_tag_flat_def, flookup_fupdate_list, ALOOKUP_APPEND] >>
 every_case_tac >>
 fs []
 >- (res_tac >>
     cases_on `ALOOKUP tagenv2 cn` >>
     fs [ALOOKUP_NONE] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [MEM_REVERSE, MEM_MAP] >>
     metis_tac [FST])
 >- (res_tac >>
     cases_on `ALOOKUP (REVERSE tagenv1) cn` >>
     fs [ALOOKUP_NONE] >>
     imp_res_tac ALOOKUP_MEM >>
     fs [MEM_REVERSE, MEM_MAP] >>
     metis_tac [FST])
 >- (res_tac >>
     cases_on `ALOOKUP tagenv2 cn` >>
     fs [ALOOKUP_NONE, REVERSE_APPEND, ALOOKUP_APPEND] >>
     cases_on `ALOOKUP (REVERSE tagenv1) cn` >>
     fs [ALOOKUP_NONE, lookup_notin]
     >- (imp_res_tac ALOOKUP_MEM >>
         fs [MEM_REVERSE, MEM_MAP, REVERSE_APPEND] >>
         metis_tac [FST])
     >- (imp_res_tac ALOOKUP_MEM >>
         `MEM cn (MAP FST tagenv1)`
                    by (rw [MEM_MAP] >>
                        metis_tac [FST, MEM_REVERSE]) >>
         metis_tac [FST])
     >- metis_tac [SOME_11, alookup_distinct_reverse]
     >- (imp_res_tac ALOOKUP_MEM >>
         `MEM cn (MAP FST tagenv1)`
                    by (rw [MEM_MAP] >>
                        metis_tac [FST, MEM_REVERSE]) >>
         metis_tac [FST]))
 >- (res_tac >>
     cases_on `ALOOKUP (REVERSE tagenv1) cn` >>
     fs []
     >- (fs [ALOOKUP_NONE] >>
         `cn ∉ set (MAP FST envC1)` by fs [MAP_REVERSE] >>
         metis_tac [lookup_notin, NOT_SOME_NONE])
     >- fs [REVERSE_APPEND, ALOOKUP_APPEND]));

val alloc_tag_wf = Q.prove (
`!gtagenv next l t cn.
  gtagenv_wf gtagenv ∧
  (cn,t) ∉ FDOM gtagenv ∧
  (!cn t tag l. FLOOKUP gtagenv (cn,t) = SOME (tag,l) ⇒ next > tag) ∧
  next > tuple_tag
  ⇒
  gtagenv_wf (gtagenv |+ ((cn,t),(next,l))) ∧
  gtagenv_weak gtagenv (gtagenv |+ ((cn,t),(next,l))) ∧
  next + 1 > tuple_tag ∧
  (!cn' t' tag l. FLOOKUP (gtagenv |+ ((cn,t),(next,l))) (cn',t') = SOME (tag,l) ⇒ next+1 > tag)`,
 rw [] >>
 fs [get_next_def,bind_def, emp_def, gtagenv_wf_def, alloc_tag_def, get_tagenv_def] >>
 rw []
 >- (rw [FLOOKUP_UPDATE] >>
     fs [get_next_def] >>
     decide_tac)
 >- (fs [has_exns_def, FLOOKUP_UPDATE] >>
     rw [] >>
     fs [FLOOKUP_DEF])
 >- (fs [FLOOKUP_UPDATE] >>
     every_case_tac >>
     fs [get_next_def] >>
     rw [] >>
     res_tac >>
     fs [])
 >- (fs [FLOOKUP_UPDATE] >>
     every_case_tac >>
     fs [get_next_def] >>
     rw [] >>
     res_tac >>
     fs [])
 >-  (rw [gtagenv_weak_def, FLOOKUP_UPDATE] >>
      every_case_tac >>
      fs [get_next_def] >>
      rw [] >>
      res_tac >>
      full_simp_tac (srw_ss()++ARITH_ss) [])
 >- (fs [get_next_def] >>
     decide_tac)
 >- (rw [get_next_def] >>
     fs [FLOOKUP_UPDATE] >>
     every_case_tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [] >>
     res_tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [get_next_def]));
     *)

val alt_alloc_tags_def = Define `
alt_alloc_tags mn next tdefs =
  ZIP (MAP FST (build_tdefs mn tdefs), REVERSE (MAP (\x. next + x) (COUNT_LIST (LENGTH (build_tdefs mn tdefs)))))`;

val count_list_lem = Q.prove (
`!n l1 l2.
 MAP (λx. n + x) (COUNT_LIST (l1 + l2 + 1)) =
 [n] ++ MAP (λx. n + SUC x) (COUNT_LIST l2) ++ MAP (λx. n + SUC l2 + x) (COUNT_LIST l1)`,
cheat);

val alt_alloc_tags_cons = Q.prove (
`!mn next tdefs tvs tn ctors.
  alt_alloc_tags mn next ((tvs,tn,ctors)::tdefs) =
  alt_alloc_tags mn (next+LENGTH ctors) tdefs ++ REVERSE (ZIP (MAP FST ctors, MAP (\x. next + x) (COUNT_LIST (LENGTH ctors))))`,
 induct_on `ctors` >>
 rw [alt_alloc_tags_def, COUNT_LIST_def, build_tdefs_cons, MAP_REVERSE] >>
 rw [REVERSE_ZIP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_pair, ZIP_APPEND, LENGTH_COUNT_LIST] >>
 `[(FST h, next)] = ZIP ([FST h], [next])` by rw [] >>
 ASM_SIMP_TAC (std_ss) [ZIP_APPEND, LENGTH, LENGTH_COUNT_LIST, LENGTH_REVERSE, LENGTH_MAP, LENGTH_APPEND] >>
 pop_assum (fn _ => all_tac) >>
 PairCases_on `h` >>
 rw [] >>
 rw [MAP_MAP_o, combinTheory.o_DEF, count_list_lem]);

val get_next_lem = Q.prove (
`!mn tn tagenv_st ctors.
  get_next (FOLDL (λst' (cn,ts). alloc_tag (TypeId (mk_id mn tn)) cn st') tagenv_st ctors) =
  LENGTH ctors + get_next tagenv_st`,
 induct_on `ctors` >>
 srw_tac [ARITH_ss] [get_next_def, alloc_tag_def] >>
 PairCases_on `h` >>
 srw_tac [ARITH_ss] [get_next_def, alloc_tag_def] >>
 PairCases_on `tagenv_st` >>
 srw_tac [ARITH_ss] [get_next_def, alloc_tag_def]);

val get_tagacc_def = Define `
get_tagacc (a,b,c,d) = d`;

(*
val alloc_tags_eqn = Q.prove (
`!mn tagenv_st tdefs.
  (get_next (alloc_tags mn tagenv_st tdefs) =
    get_next tagenv_st + LENGTH (alt_alloc_tags mn (get_next tagenv_st) tdefs)) ∧
  (get_tagenv (alloc_tags mn tagenv_st tdefs) =
    FOLDL (\tagenv (cn,tag). insert_tag_env cn tag tagenv) (get_tagenv tagenv_st) (REVERSE (alt_alloc_tags mn (get_next tagenv_st) tdefs))) ∧
  (get_tagacc (alloc_tags mn tagenv_st tdefs) =
    alt_alloc_tags mn (get_next tagenv_st) tdefs ++ get_tagacc tagenv_st)`,
 induct_on `tdefs`
 >- srw_tac [ARITH_ss] [get_next_def, get_tagenv_def, get_tagacc_def, alloc_tags_def,
                        alt_alloc_tags_def, build_tdefs_def, COUNT_LIST_def, FUPDATE_LIST] >>
 rw []
 >- (PairCases_on `h` >>
     srw_tac [ARITH_ss] [LET_THM, alloc_tags_def, get_next_def, alt_alloc_tags_def] >>
     srw_tac [ARITH_ss] [LENGTH_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP, LENGTH_FLAT, build_tdefs_def,
                         MAP_MAP_o, combinTheory.o_DEF, get_next_lem])
 >- (PairCases_on `h` >>
     srw_tac [ARITH_ss] [LET_THM, alt_alloc_tags_cons, alloc_tags_def, get_next_lem] >>
     Q.SPEC_TAC (`alt_alloc_tags mn (LENGTH h2 + get_next tagenv_st) tdefs`, `l`) >>
     Q.SPEC_TAC (`tagenv_st`, `tagenv_st`) >>
     pop_assum (fn _ => all_tac) >>
     induct_on `h2` >>
     rw [COUNT_LIST_def] >>
     PairCases_on `h` >>
     rw [] >>
     PairCases_on `tagenv_st` >>
     rw [get_tagenv_def, alloc_tag_def, get_next_def, MAP_MAP_o, combinTheory.o_DEF] >>
     `!x. x + (tagenv_st0 + 1) = SUC x + tagenv_st0` by decide_tac >>
     rw [REVERSE_APPEND])
 >- (PairCases_on `h` >>
     srw_tac [ARITH_ss] [LET_THM, alt_alloc_tags_cons, alloc_tags_def, get_next_lem] >>
     Q.SPEC_TAC (`tagenv_st`, `tagenv_st`) >>
     induct_on `h2` >>
     rw [COUNT_LIST_def] >>
     PairCases_on `h` >>
     rw [] >>
     PairCases_on `tagenv_st` >>
     rw [get_tagacc_def, get_next_def, alloc_tag_def, MAP_MAP_o, combinTheory.o_DEF] >>
     `!x. x + (tagenv_st0 + 1) = SUC x + tagenv_st0` by decide_tac >>
     rw []));

val alloc_tags_invariant_lem = Q.prove (
`gtagenv_weak (gtagenv |+ ((cn,t),next,l)) gtagenv' ∧
 flat_envC_tagged flat_defs
         (FEMPTY |++
            ZIP
               (MAP FST flat_defs,
                REVERSE (MAP (λx. next + 1 + x)
                  (COUNT_LIST (LENGTH flat_defs))))) gtagenv'
                  ⇒
 flat_envC_tagged ((cn,l,t)::flat_defs)
  (FEMPTY |++
      (ZIP
         (MAP FST flat_defs,
          REVERSE (MAP (λx. next + x)
            (MAP SUC (COUNT_LIST (LENGTH flat_defs))))) ++ [(cn,next)]))
  gtagenv'`,
 rw [flat_envC_tagged_def, lookup_tag_flat_def] >>
 cases_on `cn = cn'` >>
 fs [] >>
 rw []
 >- (rw [flookup_fupdate_list] >>
     every_case_tac >>
     fs [REVERSE_APPEND] >>
     rw [] >>
     `FLOOKUP (gtagenv |+ ((cn,t),next,l)) (cn,t) = SOME (next,l)` by rw [FLOOKUP_UPDATE] >>
     metis_tac [gtagenv_weak_def, FLOOKUP_SUBMAP])
 >- (res_tac >>
     fs [MAP_MAP_o, combinTheory.o_DEF] >>
     `!x. next + SUC x = next + 1 + x` by decide_tac >>
     rw [] >>
     every_case_tac >>
     rw [] >>
     fs [REVERSE_APPEND, flookup_fupdate_list] >>
     rpt (pop_assum mp_tac) >>
     rw []));
     *)

     (*
val alloc_tags_invariant = Q.prove (
`!gtagenv next flat_defs tids.
  gtagenv_wf gtagenv ∧
  ALL_DISTINCT (MAP FST flat_defs) ∧
  EVERY (\(cn,l,t). (cn,t) ∉ FDOM gtagenv) flat_defs ∧
  (!cn t tag l. FLOOKUP gtagenv (cn,t) = SOME (tag,l) ⇒ next > tag) ∧
  IMAGE SND (FDOM gtagenv) ⊆ tids ∧
  next > tuple_tag
  ⇒
  ?gtagenv'.
    gtagenv_wf gtagenv' ∧
    flat_envC_tagged flat_defs (FEMPTY |++ ZIP (MAP FST flat_defs, REVERSE (MAP (λx. next + x) (COUNT_LIST (LENGTH flat_defs))))) gtagenv' ∧
    IMAGE SND (FDOM gtagenv') ⊆ set (MAP (λ(cn,l,t). t) flat_defs) ∪ tids ∧
    next + LENGTH (ZIP (MAP FST flat_defs, REVERSE (MAP (λx. next + x) (COUNT_LIST (LENGTH flat_defs))))) > tuple_tag ∧
    (!cn t tag l. FLOOKUP gtagenv' (cn,t) = SOME (tag,l) ⇒ next + LENGTH (ZIP (MAP FST flat_defs, REVERSE (MAP (λx. next + x) (COUNT_LIST (LENGTH flat_defs))))) > tag) ∧
    gtagenv_weak gtagenv gtagenv'`,
 induct_on `flat_defs` >>
 rw [COUNT_LIST_def, merge_envC_empty]
 >- (rw [flat_envC_tagged_def] >>
     metis_tac [gtagenv_weak_refl]) >>
 `?cn l t. h = (cn,l,t)` by metis_tac [pair_CASES] >>
 rw [] >>
 fs [] >>
 `gtagenv_wf (gtagenv |+ ((cn,t),next,l)) ∧
  gtagenv_weak gtagenv (gtagenv |+ ((cn,t),next,l)) ∧
  next+1 > tuple_tag ∧
  ∀cn' t' tag l.
    FLOOKUP (gtagenv |+ ((cn,t),next,l)) (cn',t') = SOME (tag,l) ⇒
    next+1 > tag`
          by metis_tac [alloc_tag_wf] >>
 `EVERY (λ(cn',l',t'). (cn',t') ∉ FDOM (gtagenv |+ ((cn,t),next,l))) flat_defs`
            by (fs [EVERY_MEM, MEM_MAP] >>
                rw [] >>
                PairCases_on `e` >>
                fs [FORALL_PROD] >>
                metis_tac [FST]) >>
 `∀cn' t' tag l'.
   FLOOKUP (gtagenv |+ ((cn,t),next,l)) (cn',t') = SOME (tag,l') ⇒ next+1 > tag`
                 by (srw_tac [ARITH_ss] [FLOOKUP_UPDATE, alloc_tag_def, get_next_def] >>
                     res_tac >>
                     fs [get_next_def] >>
                     decide_tac) >>
 `IMAGE SND (FDOM gtagenv) ⊆ {t} ∪ tids` by (fs [SUBSET_DEF]) >>
 FIRST_X_ASSUM (qspecl_then [`gtagenv |+ ((cn,t),next,l)`, `next+1`, `{t} ∪ tids`] mp_tac) >>
 rw [] >>
 res_tac >>
 qexists_tac `gtagenv'` >>
 rw []
 >- metis_tac [alloc_tags_invariant_lem]
 >- metis_tac [UNION_COMM, INSERT_SING_UNION, UNION_ASSOC]
 >- (rw [MAP_MAP_o, combinTheory.o_DEF] >>
     `!x. next + SUC x = next + 1 + x` by decide_tac >>
     rw [])
 >- (res_tac >>
     rw [MAP_MAP_o, combinTheory.o_DEF] >>
     `!x. next + SUC x = next + 1 + x` by decide_tac >>
     rw [])
 >- metis_tac [gtagenv_weak_trans]);

val alloc_tags_tid_lem = Q.prove (
`!mn type_defs x.
  set (MAP (λ(cn,l,t). t) (FLAT (MAP (λ(tvs,tn,condefs).  MAP (λ(n,ts). (n,LENGTH ts,TypeId (mk_id mn tn))) condefs) type_defs))) ∪ x ⊆
  set (MAP (λ(tvs,tn,ctors). TypeId (mk_id mn tn)) type_defs) ∪ x`,
 induct_on `type_defs` >>
 fs [SUBSET_DEF] >>
 rw []
 >-(rw [MEM_MAP,MEM_FLAT] >>
    PairCases_on `h` >>
    rw [MEM_MAP,EXISTS_PROD] >>
    fs [MEM_MAP] >>
    rw [] >>
    PairCases_on`y'` >>
    rw [])
    >- metis_tac []);

val alloc_tags_thm = Q.prove (
`!gtagenv tagenv_st mn type_defs tids.
  gtagenv_wf gtagenv ∧
  alloc_tags_invariant tids tagenv_st gtagenv ∧
  check_dup_ctors type_defs ∧
  EVERY (λ(cn,l,t). (cn,t) ∉ FDOM gtagenv) (build_tdefs mn type_defs)
  ⇒
  ?gtagenv'.
    gtagenv_wf gtagenv' ∧
    flat_envC_tagged (build_tdefs mn type_defs) (FEMPTY |++ alt_alloc_tags mn (get_next tagenv_st) type_defs) gtagenv' ∧
    alloc_tags_invariant (type_defs_to_new_tdecs mn type_defs ∪ tids) (alloc_tags mn tagenv_st type_defs) gtagenv' ∧
    gtagenv_weak gtagenv gtagenv'`,
 rw [alloc_tags_eqn, alloc_tags_invariant_def, alt_alloc_tags_def, check_dup_ctors_flat] >>
 `?gtagenv'.
    gtagenv_wf gtagenv' ∧
    flat_envC_tagged (build_tdefs mn type_defs)
         (FEMPTY |++
          (REVERSE
             (ZIP
                (MAP FST (build_tdefs mn type_defs),
                 MAP (λx. get_next tagenv_st + x)
                   (COUNT_LIST (LENGTH (build_tdefs mn type_defs))))))) gtagenv' ∧
    IMAGE SND (FDOM gtagenv') ⊆
       set (MAP (λ(cn,l,t). t) (build_tdefs mn type_defs)) ∪ tids ∧
    get_next tagenv_st +
       LENGTH
         (ZIP
            (MAP FST (build_tdefs mn type_defs),
             MAP (λx. get_next tagenv_st + x)
               (COUNT_LIST (LENGTH (build_tdefs mn type_defs))))) >
       tuple_tag ∧
    (∀cn t tag l.
         FLOOKUP gtagenv' (cn,t) = SOME (tag,l) ⇒
         get_next tagenv_st +
         LENGTH
           (ZIP
              (MAP FST (build_tdefs mn type_defs),
               MAP (λx. get_next tagenv_st + x)
                 (COUNT_LIST (LENGTH (build_tdefs mn type_defs))))) >
         tag) ∧
    gtagenv_weak gtagenv gtagenv'`
         by (match_mp_tac alloc_tags_invariant >>
             metis_tac [check_dup_ctors_flat]) >>
 qexists_tac `gtagenv'` >>
 rw []
 >- (fs [type_defs_to_new_tdecs_def, build_tdefs_def] >>
     metis_tac [alloc_tags_tid_lem, SUBSET_TRANS])
 >- metis_tac []);
 *)

val recfun_helper = Q.prove (
`cenv_inv envC exh tagenv gtagenv
 ⇒
 vs_to_i2 gtagenv
          (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l)
          (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 tagenv e)) l)`,
induct_on `l` >>
rw [v_to_i2_eqns] >>
PairCases_on `h` >>
rw [] >>
rw [Once v_to_i2_cases] >>
rw [v_to_i2_eqns] >>
metis_tac []);

val alloc_tags_inv_weak = Q.prove (
`!tids tagenv_st gtagenv mn tdefs.
  alloc_tags_invariant tids tagenv_st gtagenv ⇒
  alloc_tags_invariant tids (alloc_tags mn tagenv_st tdefs) gtagenv`,
 induct_on `tdefs` >>
 rw [alloc_tags_def] >>
 PairCases_on `h` >>
 rw [alloc_tags_def, LET_THM] >>
 FIRST_X_ASSUM match_mp_tac >>
 pop_assum mp_tac >>
 Q.SPEC_TAC (`tagenv_st`, `tagenv_st`) >>
 induct_on `h2` >>
 rw [alloc_tag_def] >>
 PairCases_on `h` >>
 rw [] >>
 FIRST_X_ASSUM match_mp_tac >>
 PairCases_on `tagenv_st` >>
 fs [alloc_tag_def, alloc_tags_invariant_def, get_next_def] >>
 metis_tac [DECIDE ``x > y ⇒ x + 1 > y:num``]);

val decs_to_i2_inv_weak = Q.prove (
`!tid tagenv_st gtagenv ds tagenv_st' ds_i2 tids.
  alloc_tags_invariant tids tagenv_st gtagenv ∧
  decs_to_i2 tagenv_st ds = (tagenv_st',ds_i2)
  ⇒
  alloc_tags_invariant tids tagenv_st' gtagenv`,
 induct_on `ds` >>
 rw [decs_to_i2_def] >>
 rw [] >>
 every_case_tac >>
 fs [LET_THM]
 >- (`?tagenv_st' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st',ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac [])
 >- (`?tagenv_st' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st',ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     metis_tac [])
 >- metis_tac [alloc_tags_inv_weak]
 >- (res_tac >>
     pop_assum match_mp_tac >>
     PairCases_on `tagenv_st` >>
     fs [alloc_tag_def, alloc_tags_invariant_def, get_next_def] >>
     metis_tac [DECIDE ``x > y ⇒ x + 1 > y:num``]));

val decs_to_i2_correct = Q.prove (
`!ck genv_opt envC s ds r.
  evaluate_decs_i1 ck genv_opt envC s ds r
  ⇒
  !res genv s1 tids s1_i2 genv_i2 tagenv_st ds_i2 tagenv_st' genv' envC' s' tids' gtagenv exh.
    genv_opt = MAP SOME genv ∧
    s = (s1,tids) ∧
    r = ((s',tids'), envC', genv', res) ∧
    res ≠ SOME Rtype_error ∧
    decs_to_i2 tagenv_st ds = (tagenv_st', ds_i2) ∧
    cenv_inv envC exh (get_tagenv tagenv_st) gtagenv ∧
    s_to_i2 gtagenv s1 s1_i2 ∧
    vs_to_i2 gtagenv genv genv_i2 ∧
    alloc_tags_invariant tids tagenv_st gtagenv
    ⇒
    ?genv'_i2 s'_i2 res_i2 gtagenv' acc'.
      gtagenv_weak gtagenv gtagenv' ∧
      evaluate_decs_i2 ck exh (MAP SOME genv_i2) s1_i2 ds_i2 (s'_i2,genv'_i2,res_i2) ∧
      vs_to_i2 gtagenv' genv' genv'_i2 ∧
      s_to_i2 gtagenv' s' s'_i2 ∧
      alloc_tags_invariant tids' tagenv_st' gtagenv' ∧
      gtagenv_wf gtagenv' ∧
      get_tagacc tagenv_st' = acc' ++ get_tagacc tagenv_st ∧
      flat_envC_tagged envC' (FEMPTY |++ REVERSE acc') gtagenv' ∧
      (res = NONE ∧ res_i2 = NONE ∧ set (MAP FST acc') = set (MAP FST envC') ∨
       ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2))`,
 ho_match_mp_tac evaluate_decs_i1_ind >>
 rw [decs_to_i2_def] >>
 every_case_tac >>
 fs [LET_THM, evaluate_dec_i1_cases] >>
 rw []
 >- (fs [emp_def, Once evaluate_decs_i2_cases, v_to_i2_eqns, s_to_i2'_cases, merge_envC_empty,
         flat_envC_tagged_def] >>
     metis_tac [gtagenv_weak_refl, cenv_inv_def])
 >- (`?tagenv_st' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st', ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [Once evaluate_decs_i2_cases] >>
     fs [s_to_i2'_cases] >>
     `env_all_to_i2 (get_tagenv tagenv_st) (MAP SOME genv,envC,emp) (exh,MAP SOME genv_i2,[]) gtagenv`
                 by (fs [env_all_to_i2_cases] >>
                     rw [emp_def, v_to_i2_eqns] >>
                     every_case_tac >>
                     metis_tac []) >>
     `?s'_i2 r_i2 count' s''.
        result_to_i2 v_to_i2 gtagenv (Rerr e) r_i2 ∧
        s_to_i2 gtagenv s' s'_i2 ∧
        evaluate_i2 ck (exh,MAP SOME genv_i2,[]) s1_i2 (exp_to_i2 (get_tagenv tagenv_st) e') (s'_i2,r_i2)`
           by (imp_res_tac exp_to_i2_correct >>
               fs [] >>
               pop_assum mp_tac >>
               rw [s_to_i2_cases, s_to_i2'_cases] >>
               res_tac >>
               fs [] >>
               res_tac >>
               fs [] >>
               metis_tac []) >>
     rw [evaluate_dec_i2_cases] >>
     fs [emp_def, result_to_i2_cases, v_to_i2_eqns] >>
     rw [merge_envC_empty, flat_envC_tagged_def] >>
     `alloc_tags_invariant tids tagenv_st' gtagenv` by metis_tac [decs_to_i2_inv_weak] >>
     `?acc'. get_tagacc tagenv_st' = acc'++get_tagacc tagenv_st` by cheat >>
     metis_tac [gtagenv_weak_refl, cenv_inv_def])
 >- (`?tagenv_st' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st', ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [Once evaluate_decs_i2_cases] >>
     fs [s_to_i2'_cases] >>
     `env_all_to_i2 (get_tagenv tagenv_st) (MAP SOME genv,envC,emp) (exh,MAP SOME genv_i2,[]) gtagenv`
                 by (fs [env_all_to_i2_cases] >>
                     rw [emp_def, v_to_i2_eqns] >>
                     every_case_tac >>
                     metis_tac []) >>
     `?r_i2 s'_i2. result_to_i2 v_to_i2 gtagenv (Rval (Conv_i1 NONE new_env)) r_i2 ∧
                s_to_i2 gtagenv s2 s'_i2 ∧
                evaluate_i2 ck (exh,MAP SOME genv_i2,[]) s1_i2 (exp_to_i2 (get_tagenv tagenv_st) e) (s'_i2,r_i2)`
                     by (imp_res_tac exp_to_i2_correct >>
                         fs [] >>
                         res_tac >>
                         fs [] >>
                         metis_tac []) >>
     rw [evaluate_dec_i2_cases] >>
     fs [result_to_i2_cases, v_to_i2_eqns, merge_envC_empty] >>
     rw [] >>
     `vs_to_i2 gtagenv (genv ++ new_env) (genv_i2++vs')`
                  by metis_tac [vs_to_i2_append, length_vs_to_i2] >>
     FIRST_X_ASSUM (qspecl_then [`s'_i2`, `genv_i2 ++ vs'`, `tagenv_st`, `ds_i2'`, `tagenv_st'`, `gtagenv`, `exh`] mp_tac) >>
     rw [] >>
     fs [emp_def, merge_def] >>
     `vs_to_i2 gtagenv'' (new_env ++ new_env') (vs' ++ genv'_i2)`
                  by metis_tac [vs_to_i2_append, length_vs_to_i2, v_to_i2_weakening] >>
     metis_tac [length_vs_to_i2, cenv_inv_def])
 >- (`?tagenv_st' ds_i2. decs_to_i2 tagenv_st ds = (tagenv_st', ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     fs [emp_def, merge_def, merge_envC_empty] >>
     `vs_to_i2 gtagenv
               (genv ++ MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l)
               (genv_i2 ++ MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (get_tagenv tagenv_st) e)) l)`
              by metis_tac [recfun_helper, length_vs_to_i2, vs_to_i2_append] >>
     FIRST_X_ASSUM (qspecl_then [`s1_i2`, `genv_i2 ++ MAP (λ(f,x,e).  Closure_i2 [] x (exp_to_i2 (get_tagenv tagenv_st) e)) l`, `tagenv_st`, `ds_i2'`, `tagenv_st'`, `gtagenv`, `exh`] mp_tac) >>
     rw [] >>
     rw [Once evaluate_decs_i2_cases, evaluate_dec_i2_cases] >>
     `vs_to_i2 gtagenv'
               (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l ++ new_env')
               (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (get_tagenv tagenv_st) e)) l ++ genv'_i2)`
               by metis_tac [recfun_helper, v_to_i2_weakening, vs_to_i2_append, length_vs_to_i2] >>
     fs [funs_to_i2_map , MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM PEXISTS_THM] >>
     fs [result_to_i2_cases] >>
     metis_tac [pair_CASES])
 >- cheat
 >- cheat);

 (*
 >- (`?gtagenv'.
       gtagenv_wf gtagenv' ∧
       flat_envC_tagged (build_tdefs o' l) (FEMPTY |++ REVERSE (alt_alloc_tags o' (get_next tagenv_st) l)) gtagenv' ∧
       alloc_tags_invariant (type_defs_to_new_tdecs o' l ∪ tids) (alloc_tags o' tagenv_st l) gtagenv' ∧
       gtagenv_weak gtagenv gtagenv'`
             by (match_mp_tac alloc_tags_thm >>
                 fs [cenv_inv_def, type_defs_to_new_tdecs_def, build_tdefs_def] >>
                 rw [EVERY_MAP, MEM_FLAT, EVERY_MEM, MEM_MAP, EXISTS_PROD] >>
                 fs [MEM_MAP] >>
                 rw [] >>
                 PairCases_on `y` >>
                 rw [] >>
                 fs [alloc_tags_invariant_def, SUBSET_DEF, DISJOINT_DEF, type_defs_to_new_tdecs_def, EXTENSION,
                     MEM_MAP, FORALL_PROD] >>
                 metis_tac [SND]) >>
     fs [merge_envC_empty_assoc, merge_def, emp_def] >>
     `s_to_i2' gtagenv' s1 s1_i2 ∧ vs_to_i2 gtagenv' genv genv_i2`
                 by metis_tac [v_to_i2_weakening, s_to_i2'_cases] >>
     `cenv_inv (merge_envC ([],build_tdefs o' l) envC) (get_tagenv (alloc_tags o' tagenv_st l)) gtagenv'`
                by cheat >>
     FIRST_X_ASSUM (qspecl_then [`s1_i2`, `genv_i2`, `alloc_tags o' tagenv_st l`,
                                 `ds_i2`, `tagenv_st'`, `gtagenv'` ] mp_tac) >>
     rw [] >>
     fs [alloc_tags_eqn]
     >- (Q.LIST_EXISTS_TAC [`genv'_i2`, `s'_i2`, `gtagenv''`] >>
         rw []
         >- metis_tac [gtagenv_weak_trans]
         >- (fs [REVERSE_APPEND] >>
             match_mp_tac flat_envC_tagged_append >>
             rw []
             >- (rw [alt_alloc_tags_def, MAP_ZIP, LENGTH_COUNT_LIST] >>
                 metis_tac [check_dup_ctors_flat])
             >- rw [MAP_REVERSE]
             >- metis_tac [flat_envC_tagged_weakening])
         >- rw [EXTENSION, alt_alloc_tags_def, MAP_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP, MAP_REVERSE])
     >- (Q.LIST_EXISTS_TAC [`genv'_i2`, `s'_i2`, `SOME err_i2`, `gtagenv''`] >>
         rw []
         >- metis_tac [gtagenv_weak_trans]
         >- (fs [REVERSE_APPEND] >>
             match_mp_tac flat_envC_tagged_append >>
             rw []
             >- (rw [alt_alloc_tags_def, MAP_ZIP, LENGTH_COUNT_LIST] >>
                 metis_tac [check_dup_ctors_flat])
             >- rw [MAP_REVERSE]
             >- metis_tac [flat_envC_tagged_weakening])
         >- rw [EXTENSION, alt_alloc_tags_def, MAP_ZIP, LENGTH_COUNT_LIST, LENGTH_MAP, MAP_REVERSE])





 >- (`?gtagenv'. cenv_inv (merge_envC ([],bind s (LENGTH l,TypeExn (mk_id o' s)) emp) envC)
                          (get_tagenv (alloc_tag (TypeExn (mk_id o' s)) s tagenv_st)) gtagenv' ∧
                 alloc_tags_invariant ({TypeExn (mk_id o' s)} ∪ tids) (alloc_tag (TypeExn (mk_id o' s)) s tagenv_st) gtagenv' ∧
                 gtagenv_weak gtagenv gtagenv'`
             by (fs [alloc_tags_invariant_def] >>
                 imp_res_tac alloc_tags_cenv_inv1 >>
                 pop_assum (qspecl_then [`bind s (LENGTH l,TypeExn (mk_id o' s)) emp`] mp_tac) >>
                 `(s,TypeExn (mk_id o' s)) ∉ FDOM gtagenv`
                          by (fs [SUBSET_DEF] >>
                              metis_tac [SND]) >>
                 rw [bind_def, emp_def] >>
                 pop_assum (qspecl_then [`[]`, `envC`] mp_tac) >>
                 rw [merge_envC_empty] >>
                 metis_tac []) >>
     fs [merge_envC_empty_assoc, merge_def, emp_def] >>
     `s_to_i2' gtagenv' s1 s1_i2 ∧ vs_to_i2 gtagenv' genv genv_i2`
                 by metis_tac [v_to_i2_weakening, s_to_i2'_cases] >>
     FIRST_X_ASSUM (qspecl_then [`s1_i2`, `genv_i2`, `alloc_tag (TypeExn (mk_id o' s)) s tagenv_st`,
                                 `ds_i2`, `tagenv_st'`, `gtagenv'` ] mp_tac) >>
     rw [] >>
     metis_tac [gtagenv_weak_trans]));
     *)

     (*
val dummy_env_to_i2 = Q.prove (
`!ds cenv cenv' ds'.
  decs_to_i2 cenv ds = (cenv',ds')
  ⇒
  decs_to_dummy_env ds = decs_to_dummy_env_i2 ds'`,
 induct_on `ds` >>
 rw [decs_to_i2_def, decs_to_dummy_env_def, decs_to_dummy_env_i2_def] >>
 rw [decs_to_i2_def, decs_to_dummy_env_def, decs_to_dummy_env_i2_def] >>
 every_case_tac >>
 fs [LET_THM, dec_to_dummy_env_def]
 >- (Cases_on `decs_to_i2 cenv ds` >>
     fs [] >>
     rw [decs_to_dummy_env_i2_def, dec_to_dummy_env_i2_def] >>
     metis_tac [])
 >- (Cases_on `decs_to_i2 cenv ds` >>
     fs [] >>
     rw [decs_to_dummy_env_i2_def, dec_to_dummy_env_i2_def,
         funs_to_i2_map] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []);

val to_i2_invariant_def = Define `
to_i2_invariant tids envC tagenv_st gtagenv s s_i2 genv genv_i2 ⇔
  cenv_inv envC (get_tagenv tagenv_st) gtagenv ∧
  s_to_i2' gtagenv s s_i2 ∧
  vs_to_i2 gtagenv genv genv_i2 ∧
  alloc_tags_invariant tids tagenv_st gtagenv`;



val cenv_inv_to_mod = Q.prove (
`!envC' envC tagenv gtagenv mn acc.
  cenv_inv (merge_envC (emp,envC') envC) tagenv gtagenv
  ⇒
  cenv_inv (merge_envC (mod_cenv mn envC') envC) (mod_tagenv mn acc tagenv) gtagenv`,

 rw [cenv_inv_def, mod_cenv_def] >>
 >- (every_case_tac >>
     fs [emp_def] >>

     >- (res_tac  >>
         fs [] >>
         PairCases_on `tagenv` >>
         fs [mod_tagenv_def, lookup_tag_env_def] >>
         every_case_tac >>
         fs []

 >- metis_tac []
 >- metis_tac []);


fun dec_lem t =
(SIMP_RULE (srw_ss()) [] o
 GEN_ALL o
 Q.INST [`res` |-> t] o
 SPEC_ALL o
 SIMP_RULE (srw_ss()) [PULL_FORALL]) decs_to_i2_correct

val prompt_to_i2_correct = Q.prove (
`!genv envC s tids mods prompt s_i2 genv_i2 next tagenv inv prompt_i2 genv' envC' s' tids' mods' res gtagenv next' tagenv' inv'.
  evaluate_prompt_i1 (MAP SOME genv) envC (s,tids,mods) prompt ((s',tids',mods'), envC', genv', res) ∧
  res ≠ SOME Rtype_error ∧
  to_i2_invariant tids envC (next,tagenv,inv,([]:(tvarN, num) alist)) gtagenv s s_i2 genv genv_i2 ∧
  ((next',tagenv',inv'), prompt_i2) = prompt_to_i2 (next,tagenv,inv) prompt
  ⇒
  ?genv'_i2 s'_i2 res_i2 gtagenv'.
    gtagenv_weak gtagenv gtagenv' ∧
    evaluate_prompt_i2 (MAP SOME genv_i2) s_i2 prompt_i2 (s'_i2,genv'_i2,res_i2) ∧
    to_i2_invariant tids' (merge_envC envC' envC) (next',tagenv',inv',([]:(tvarN, num) alist)) gtagenv' s' s'_i2 genv' genv'_i2 ∧
    (res = NONE ∧ res_i2 = NONE ∨
     ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ result_to_i2 (\a b c. T) gtagenv' (Rerr err) (Rerr err_i2))`,
 rw [evaluate_prompt_i1_cases, evaluate_prompt_i2_cases, prompt_to_i2_def, LET_THM] >>
 every_case_tac >>
 fs [] >>
 rw [] >>
 `?next' tagenv' inv'' acc ds_i2. decs_to_i2 (next,tagenv,inv',[]) ds = ((next',tagenv',inv'',acc),ds_i2)` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 fs [to_i2_invariant_def]
 >- (`∃genv'_i2 s'_i2 gtagenv'.
       gtagenv_weak gtagenv gtagenv' ∧
       evaluate_decs_i2 (MAP SOME genv_i2) s_i2 ds_i2 (s'_i2,genv'_i2,NONE) ∧
       vs_to_i2 gtagenv' genv' genv'_i2 ∧
       s_to_i2' gtagenv' s' s'_i2 ∧
       alloc_tags_invariant tids' (next',tagenv'',inv'',acc) gtagenv' ∧
       cenv_inv (merge_envC (emp,cenv') envC) (get_tagenv (next',tagenv'',inv'',acc)) gtagenv'`
           by (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (dec_lem `NONE`)) >>
               metis_tac []) >>
     rw [] >>
     Q.LIST_EXISTS_TAC [`genv'_i2`, `s'_i2`, `gtagenv'`] >>
     fs [get_tagenv_def] >>
     rw []
     >- cheat
     >- cheat)
 >- (`∃genv'_i2 s'_i2 res_i2 gtagenv'.
       gtagenv_weak gtagenv gtagenv' ∧
       evaluate_decs_i2 (MAP SOME genv_i2) s_i2 ds_i2 (s'_i2,genv'_i2,res_i2) ∧
       vs_to_i2 gtagenv' env genv'_i2 ∧
       s_to_i2' gtagenv' s' s'_i2 ∧
       alloc_tags_invariant tids' (next',tagenv'',inv'',acc) gtagenv' ∧
       ∃err_i2.
         res_i2 = SOME err_i2 ∧
         result_to_i2 (λa b c. T) gtagenv' (Rerr err) (Rerr err_i2)`
           by (match_mp_tac (SIMP_RULE (srw_ss()) [AND_IMP_INTRO] (dec_lem `SOME err`)) >>
               metis_tac []) >>
     rw [] >>
     Q.LIST_EXISTS_TAC [`genv'_i2 ++ GENLIST (λn. Litv_i2 Unit) (decs_to_dummy_env_i2 ds_i2 − LENGTH genv'_i2)`,
                        `s'_i2`,
                        `SOME err_i2`,
                        `gtagenv'`] >>
     rw []
     >- (qexists_tac `genv'_i2` >>
         rw [])
     >- cheat
     >- (`LENGTH env = LENGTH genv'_i2` by metis_tac [length_vs_to_i2] >>
         `vs_to_i2 gtagenv'
                   (GENLIST (λn. Litv_i1 Unit) (decs_to_dummy_env ds − LENGTH env))
                   (GENLIST (λn. Litv_i2 Unit) (decs_to_dummy_env_i2 ds_i2 − LENGTH env))`
                      by (imp_res_tac dummy_env_to_i2 >>
                          rw [] >>
                          rpt (pop_assum (fn _ => all_tac)) >>
                          Q.SPEC_TAC (`decs_to_dummy_env_i2 ds_i2 − LENGTH genv'_i2`, `nn`) >>
                          induct_on `nn` >>
                          rw [v_to_i2_eqns, GENLIST, SNOC_APPEND, vs_to_i2_append1]) >>
         metis_tac [vs_to_i2_append])
     >- cheat));
     *)

val _ = export_theory ();
