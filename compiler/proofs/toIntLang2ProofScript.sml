open preamble;
open alistTheory optionTheory rich_listTheory;
open miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open intLang1Theory;
open intLang2Theory;
open toIntLang1ProofTheory;
open evalPropsTheory;

val _ = new_theory "toIntLang2Proof";

val fmap_inverse_def = Define `
fmap_inverse m1 m2 =
  !k. k ∈ FDOM m1 ⇒ ?v. FLOOKUP m1 k = SOME v ∧ FLOOKUP m2 v = SOME k`;

val same_tid_diff_ctor = Q.prove (
`!cn1 cn2 t1 t2.
  same_tid t1 t2 ∧ ~same_ctor (cn1, t1) (cn2, t2)
  ⇒
  (cn1 ≠ cn2) ∨ (cn1 = cn2 ∧ ?mn1 mn2. t1 = TypeExn mn1 ∧ t2 = TypeExn mn2 ∧ mn1 ≠ mn2)`,
rw [] >>
cases_on `t1` >>
cases_on `t2` >>
fs [same_tid_def, same_ctor_def]);

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (pat_to_i2_def, pat_to_i2_ind) =
  tprove_no_defn ((pat_to_i2_def, pat_to_i2_ind),
  wf_rel_tac `inv_image $< (\(x,p). pat_size p)` >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  induct_on `ps` >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  srw_tac [ARITH_ss] [pat_size_def] >>
  res_tac >>
  decide_tac);
val _ = register "pat_to_i2" pat_to_i2_def pat_to_i2_ind;

val (exp_to_i2_def, exp_to_i2_ind) =
  tprove_no_defn ((exp_to_i2_def, exp_to_i2_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,e) => exp_i1_size e
                                        | INR (INL (x,es)) => exp_i16_size es
                                        | INR (INR (INL (x,pes))) => exp_i13_size pes
                                        | INR (INR (INR (x,funs))) => exp_i11_size funs)` >>
  srw_tac [ARITH_ss] [exp_i1_size_def]);
val _ = register "exp_to_i2" exp_to_i2_def exp_to_i2_ind;

val (pmatch_i2_def, pmatch_i2_ind) =
  tprove_no_defn ((pmatch_i2_def, pmatch_i2_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,p,y,z) => pat_i2_size p
                                        | INR (x,ps,y,z) => pat_i21_size ps)` >>
  srw_tac [ARITH_ss] [pat_i2_size_def]);
val _ = register "pmatch_i2" pmatch_i1_def pmatch_i2_ind;

val (do_eq_i2_def, do_eq_i2_ind) =
  tprove_no_defn ((do_eq_i2_def, do_eq_i2_ind),
  wf_rel_tac `inv_image $< (\x. case x of INL (x,y) => v_i2_size x
                                        | INR (xs,ys) => v_i23_size xs)`);
val _ = register "do_eq_i2" do_eq_i2_def do_eq_i2_ind;

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

val lookup_type_tag_def = Define `
(lookup_type_tag NONE cenv = SOME tuple_tag) ∧
(lookup_type_tag (SOME cn) (next,env,type_cenv,inv) = FLOOKUP type_cenv cn)`;

val has_exns_def = Define `
has_exns (cenv, clengths) ⇔
  FLOOKUP clengths ("Bind", TypeExn NONE) = SOME (0:num) ∧
  FLOOKUP clengths ("Div", TypeExn NONE) = SOME 0 ∧
  FLOOKUP clengths ("Eq", TypeExn NONE) = SOME 0 ∧
  FLOOKUP cenv ("Bind", TypeExn NONE) = SOME bind_tag ∧
  FLOOKUP cenv ("Div", TypeExn NONE) = SOME div_tag ∧
  FLOOKUP cenv ("Eq", TypeExn NONE) = SOME eq_tag`;

val cenv_inv_def = Define `
cenv_inv (cenv:envC) ((next, lex_cenv, type_cenv, inverse_cenv):cenv_mapping) (clengths:(conN#tid_or_exn)|-> num) ⇔
  (!cn num_args t.
    lookup_con_id cn cenv = SOME (num_args, t)
    ⇒
    FLOOKUP clengths (id_to_n cn,t) = SOME num_args ∧
    ?tag.
      FLOOKUP lex_cenv cn = SOME tag ∧
      FLOOKUP type_cenv (id_to_n cn, t) = SOME tag) ∧
  (!cn. FLOOKUP type_cenv cn ≠ SOME tuple_tag) ∧
  has_exns (type_cenv,clengths) ∧
  (!t1 t2 tag cn cn'.
     (* Comment out same_tid because we're not using separate tag spaces per type *)
     (* same_tid t1 t2 ∧ *)
     FLOOKUP type_cenv (cn,t1) = SOME tag ∧
     FLOOKUP type_cenv (cn',t2) = SOME tag
     ⇒
     cn = cn' ∧ t1 = t2)`;

val (v_to_i2_rules, v_to_i2_ind, v_to_i2_cases) = Hol_reln `
(!cenv lit.
  v_to_i2 cenv (Litv_i1 lit) (Litv_i2 lit)) ∧
(!cenv vs vs'.
  vs_to_i2 cenv vs vs'
  ⇒ 
  v_to_i2 cenv (Conv_i1 NONE vs) (Conv_i2 tuple_tag vs')) ∧
(!cenv clengths cn tn tag vs vs'.
  FLOOKUP cenv (cn,tn) = SOME tag ∧
  FLOOKUP clengths (cn,tn) = SOME (LENGTH vs) ∧
  vs_to_i2 (cenv,clengths) vs vs'
  ⇒ 
  v_to_i2 (cenv,clengths) (Conv_i1 (SOME (cn,tn)) vs) (Conv_i2 tag vs')) ∧
(!cenv env x e env_i2 envC next lex_cenv inverse_cenv.
  env_to_i2 (cenv,clengths) env env_i2 ∧
  cenv_inv envC (next, lex_cenv, cenv, inverse_cenv) clengths
  ⇒ 
  v_to_i2 (cenv,clengths) (Closure_i1 (envC,env) x e) (Closure_i2 env_i2 x (exp_to_i2 lex_cenv e))) ∧ 
(!cenv env funs x envC env_i2 next lex_cenv inverse_cenv.
  env_to_i2 (cenv,clengths) env env_i2 ∧
  cenv_inv envC (next, lex_cenv, cenv, inverse_cenv) clengths
  ⇒ 
  v_to_i2 (cenv,clengths) (Recclosure_i1 (envC,env) funs x) (Recclosure_i2 env_i2 (funs_to_i2 lex_cenv funs) x)) ∧
(!cenv loc.
  v_to_i2 cenv (Loc_i1 loc) (Loc_i2 loc)) ∧
(!cenv.
  vs_to_i2 cenv [] []) ∧
(!cenv v vs v' vs'.
  v_to_i2 cenv v v' ∧
  vs_to_i2 cenv vs vs'
  ⇒
  vs_to_i2 cenv (v::vs) (v'::vs')) ∧
(!cenv.
  env_to_i2 cenv [] []) ∧
(!cenv x v env env' v'. 
  env_to_i2 cenv env env' ∧
  v_to_i2 cenv v v'
  ⇒ 
  env_to_i2 cenv ((x,v)::env) ((x,v')::env'))`;

val v_to_i2_eqns = Q.prove (
`(!cenv l v.
  v_to_i2 cenv (Litv_i1 l) v ⇔ 
    (v = Litv_i2 l)) ∧
 (!cenv cn vs v.
  v_to_i2 cenv (Conv_i1 cn vs) v ⇔ 
    (?vs' tag cenv' clengths.
       vs_to_i2 cenv vs vs' ∧ (v = Conv_i2 tag vs') ∧
       (cn = NONE ∧ tag = tuple_tag ∨
        ?cenv' clengths cn' tn.
          cenv = (cenv',clengths) ∧
          FLOOKUP cenv' (cn',tn) = SOME tag ∧
          FLOOKUP clengths (cn',tn) = SOME (LENGTH vs) ∧
          cn = SOME (cn',tn) ∧ FLOOKUP cenv' (cn', tn) = SOME tag))) ∧
 (!cenv l v.
  v_to_i2 cenv (Loc_i1 l) v ⇔ 
    (v = Loc_i2 l)) ∧
 (!cenv vs.
  vs_to_i2 cenv [] vs ⇔ 
    (vs = [])) ∧
 (!cenv l v vs vs'.
  vs_to_i2 cenv (v::vs) vs' ⇔ 
    ?v' vs''. v_to_i2 cenv v v' ∧ vs_to_i2 cenv vs vs'' ∧ vs' = v'::vs'') ∧
 (!cenv env'.
  env_to_i2 cenv [] env' ⇔
    env' = []) ∧
 (!cenv x v env env'.
  env_to_i2 cenv ((x,v)::env) env' ⇔
    ?v' env''. v_to_i2 cenv v v' ∧ env_to_i2 cenv env env'' ∧ env' = ((x,v')::env''))`,
rw [] >>
rw [Once v_to_i2_cases] >>
metis_tac []);

val cenv_weak_def = Define `
cenv_weak (cenv1,clengths1) (cenv2,clengths2) ⇔
  cenv1 SUBMAP cenv2 ∧
  clengths1 SUBMAP clengths2 ∧
  (!cn. FLOOKUP cenv2 cn ≠ SOME tuple_tag) ∧
  (!t1 t2 tag cn cn'.
     (* Comment out same_tid because we're not using separate tag spaces per type *)
     (* same_tid t1 t2 ∧ *)
     FLOOKUP cenv2 (cn,t1) = SOME tag ∧
     FLOOKUP cenv2 (cn',t2) = SOME tag
     ⇒
     cn = cn' ∧ t1 = t2)`;

val v_to_i2_weakening = Q.prove (
`(!cenv v v_i2.
  v_to_i2 cenv v v_i2
  ⇒
    !cenv'. cenv_weak cenv cenv'
    ⇒
    v_to_i2 cenv' v v_i2) ∧
 (!cenv vs vs_i2.
  vs_to_i2 cenv vs vs_i2
  ⇒
   !cenv'. cenv_weak cenv cenv'
    ⇒
    vs_to_i2 cenv' vs vs_i2) ∧
 (!cenv env env_i2.
  env_to_i2 cenv env env_i2
  ⇒
   !cenv'. cenv_weak cenv cenv'
    ⇒
    env_to_i2 cenv' env env_i2)`,
 ho_match_mp_tac v_to_i2_ind >>
 rw [v_to_i2_eqns, cenv_weak_def] >>
 res_tac >>
 `?cenv1 clengths1. cenv' = (cenv1,clengths1)` by metis_tac [pair_CASES] >>
 fs [cenv_weak_def]
 >- metis_tac [FLOOKUP_SUBMAP]
 >- (rw [Once v_to_i2_cases] >>
     Q.LIST_EXISTS_TAC [`next`, `lex_cenv`, `inverse_cenv`] >> 
     fs [cenv_inv_def] >>
     rw []
     >- metis_tac [FLOOKUP_SUBMAP]
     >- metis_tac [FLOOKUP_SUBMAP]
     >- (fs [has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac [])
 >- (rw [Once v_to_i2_cases] >>
     Q.LIST_EXISTS_TAC [`next`, `lex_cenv`, `inverse_cenv`] >> 
     fs [cenv_inv_def] >>
     rw []
     >- metis_tac [FLOOKUP_SUBMAP]
     >- metis_tac [FLOOKUP_SUBMAP]
     >- (fs [has_exns_def] >>
         metis_tac [FLOOKUP_SUBMAP])
     >- metis_tac []
     >- metis_tac []));

val (result_to_i2_rules, result_to_i2_ind, result_to_i2_cases) = Hol_reln `
(∀genv v v'. 
  f genv v v'
  ⇒
  result_to_i2 f genv (Rval v) (Rval v')) ∧
(∀genv v v'. 
  v_to_i2 genv v v'
  ⇒
  result_to_i2 f genv (Rerr (Rraise v)) (Rerr (Rraise v'))) ∧
(!genv.
  result_to_i2 f genv (Rerr Rtimeout_error) (Rerr Rtimeout_error)) ∧
(!genv.
  result_to_i2 f genv (Rerr Rtype_error) (Rerr Rtype_error))`;

val result_to_i2_eqns = Q.prove (
`(!genv v r.
  result_to_i2 f genv (Rval v) r ⇔ 
    ?v'. f genv v v' ∧ r = Rval v') ∧
 (!genv v r.
  result_to_i2 f genv (Rerr (Rraise v)) r ⇔ 
    ?v'. v_to_i2 genv v v' ∧ r = Rerr (Rraise v')) ∧
 (!genv v r.
  result_to_i2 f genv (Rerr Rtimeout_error) r ⇔ 
    r = Rerr Rtimeout_error) ∧
 (!genv v r.
  result_to_i2 f genv (Rerr Rtype_error) r ⇔ 
    r = Rerr Rtype_error)`,
rw [result_to_i2_cases] >>
metis_tac []);

val (s_to_i2'_rules, s_to_i2'_ind, s_to_i2'_cases) = Hol_reln `
(!genv s s'.
  vs_to_i2 genv s s'
  ⇒
  s_to_i2' genv s s')`;

val (s_to_i2_rules, s_to_i2_ind, s_to_i2_cases) = Hol_reln `
(!genv c s s'.
  s_to_i2' genv s s'
  ⇒
  s_to_i2 genv (c,s) (c,s'))`;

val length_vs_to_i2 = Q.prove (
`!vs cenv vs'. 
  vs_to_i2 cenv vs vs'
  ⇒
  LENGTH vs = LENGTH vs'`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 rw [] >>
 metis_tac []);

val length_evaluate_list_i2 = Q.prove (
`!b env s cenv es s' vs.
  evaluate_list_i2 b env s (exps_to_i2 cenv es) (s', Rval vs)
  ⇒
  LENGTH es = LENGTH vs`,
 induct_on `es` >>
 rw [exp_to_i2_def] >>
 cases_on `vs` >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_i2_cases]) >>
 rw [] >>
 metis_tac []);

val env_to_i2_el = Q.prove (
`!cenv env env_i2. 
  env_to_i2 cenv env env_i2 ⇔ 
  LENGTH env = LENGTH env_i2 ∧ !n. n < LENGTH env ⇒ (FST (EL n env) = FST (EL n env_i2)) ∧ v_to_i2 cenv (SND (EL n env)) (SND (EL n env_i2))`,
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
`!cenv v n s v_i2 n s_i2.
  vs_to_i2 cenv s s_i2 ∧
  v_to_i2 cenv v v_i2
  ⇒
  vs_to_i2 cenv (LUPDATE v n s) (LUPDATE v_i2 n s_i2)`,
 induct_on `n` >>
 rw [v_to_i2_eqns, LUPDATE_def] >>
 cases_on `s` >>
 fs [v_to_i2_eqns, LUPDATE_def]);

val match_result_to_i2_def = Define 
`(match_result_to_i2 cenv (Match env) (Match env_i2) ⇔ 
   env_to_i2 cenv env env_i2) ∧
 (match_result_to_i2 cenv No_match No_match = T) ∧
 (match_result_to_i2 cenv Match_type_error Match_type_error = T) ∧
 (match_result_to_i2 cenv _ _ = F)`;

val store_lookup_vs_to_i2 = Q.prove (
`!cenv vs vs_i2 v v_i2 n.
  vs_to_i2 cenv vs vs_i2 ∧
  store_lookup n vs = SOME v ∧
  store_lookup n vs_i2 = SOME v_i2
  ⇒
  v_to_i2 cenv v v_i2`,
 induct_on `vs` >>
 rw [v_to_i2_eqns] >>
 fs [store_lookup_def] >>
 cases_on `n` >>
 fs [] >>
 metis_tac []);

val store_lookup_vs_to_i2_2 = Q.prove (
`!cenv vs vs_i2 v v_i2 n.
  vs_to_i2 cenv vs vs_i2 ∧
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
`!cenv p x. pat_bindings_i2 (pat_to_i2 cenv p) x = pat_bindings p x`,
 ho_match_mp_tac pat_to_i2_ind >>
 rw [pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 induct_on `ps` >>
 rw [] >>
 fs [pat_bindings_def, pat_bindings_i2_def, pat_to_i2_def] >>
 metis_tac [APPEND_11, pat_bindings_accum, pat_bindings_i2_accum]);

val pmatch_to_i2_correct = Q.prove (
`(!envC s p v env r env_i2 s_i2 v_i2 next lex_cenv cenv inverse_cenv clengths.
  r ≠ Match_type_error ∧
  cenv_inv envC (next,lex_cenv,cenv,inverse_cenv) clengths ∧
  pmatch_i1 envC s p v env = r ∧
  s_to_i2' (cenv,clengths) s s_i2 ∧
  v_to_i2 (cenv,clengths) v v_i2 ∧
  env_to_i2 (cenv,clengths) env env_i2
  ⇒
  ?r_i2.
    pmatch_i2 s_i2 (pat_to_i2 lex_cenv p) v_i2 env_i2 = r_i2 ∧
    match_result_to_i2 (cenv,clengths) r r_i2) ∧
 (!envC s ps vs env r env_i2 s_i2 vs_i2 next lex_cenv cenv inverse_cenv clengths.
  r ≠ Match_type_error ∧
  cenv_inv envC (next,lex_cenv,cenv,inverse_cenv) clengths ∧
  pmatch_list_i1 envC s ps vs env = r ∧
  s_to_i2' (cenv,clengths) s s_i2 ∧
  vs_to_i2 (cenv,clengths) vs vs_i2 ∧
  env_to_i2 (cenv,clengths) env env_i2
  ⇒
  ?r_i2.
    pmatch_list_i2 s_i2 (MAP (pat_to_i2 lex_cenv) ps) vs_i2 env_i2 = r_i2 ∧
    match_result_to_i2 (cenv,clengths) r r_i2)`,
 ho_match_mp_tac pmatch_i1_ind >>
 rw [pmatch_i1_def, pmatch_i2_def, pat_to_i2_def, match_result_to_i2_def] >>
 fs [match_result_to_i2_def, bind_def, v_to_i2_eqns] >>
 rw [pmatch_i2_def, match_result_to_i2_def]
 >- (cases_on `lookup_con_id n envC` >>
     fs [] >>
     every_case_tac >>
     fs [] 
     >- metis_tac [] >>
     fs [lookup_tag_def, cenv_inv_def] >>
     res_tac >>
     fs [] >>
     rw [] >>
     imp_res_tac same_tid_diff_ctor >>
     rw [] >>
     metis_tac [tid_or_exn_11])
 >- (cases_on `lookup_con_id n envC` >>
     fs [] >>
     every_case_tac >>
     fs [] >> 
     rw []
     >- metis_tac [length_vs_to_i2, cenv_inv_def, SOME_11, same_ctor_and_same_tid] >>
     fs [lookup_tag_def, cenv_inv_def] >>
     res_tac >>
     fs [] >>
     rw [] >>
     imp_res_tac same_tid_diff_ctor >>
     rw [] >>
     metis_tac [tid_or_exn_11])
 >- (cases_on `lookup_con_id n envC` >>
     fs [] >>
     every_case_tac >>
     fs [lookup_tag_def, cenv_inv_def] >>
     imp_res_tac same_ctor_and_same_tid >>
     imp_res_tac same_tid_diff_ctor >>
     rw [] >>
     res_tac >>
     fs [match_result_to_i2_def])
 >- metis_tac []
 >- metis_tac [length_vs_to_i2]
 >- fs [lookup_tag_def]
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
(!genv envC clengths lex_cenv next cenv inverse_cenv env env_i2 genv_i2.
  cenv_inv envC (next, lex_cenv, cenv, inverse_cenv) clengths ∧
  vs_to_i2 (cenv,clengths) genv genv_i2 ∧
  env_to_i2 (cenv,clengths) env env_i2
  ⇒
  env_all_to_i2 (next, lex_cenv, cenv, inverse_cenv) (genv,envC,env) (genv_i2,env_i2) (cenv,clengths))`;

val env_to_i2_append = Q.prove (
`!cenv env1 env2 env1' env2'.
  env_to_i2 cenv env1 env1' ∧
  env_to_i2 cenv env2 env2' 
  ⇒
  env_to_i2 cenv (env1++env2) (env1'++env2')`,
 induct_on `env1` >>
 rw [v_to_i2_eqns] >>
 PairCases_on `h` >>
 fs [v_to_i2_eqns]);

val env_to_i2_lookup = Q.prove (
`!cenv env x v env'.
  lookup x env = SOME v ∧
  env_to_i2 cenv env env'
  ⇒
  ?v'.
    v_to_i2 cenv v v' ∧
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
`!cenv genv n genv'.
  vs_to_i2 cenv genv genv' ∧
  LENGTH genv > n
  ⇒
  v_to_i2 cenv (EL n genv) (EL n genv')`,
 induct_on `genv` >>
 srw_tac [ARITH_ss] [v_to_i2_eqns] >>
 cases_on `n` >>
 srw_tac [ARITH_ss] [v_to_i2_eqns]);

val vs_to_i2_append1 = Q.prove (
`!cenv vs v vs' v'.
  vs_to_i2 cenv (vs++[v]) (vs'++[v'])
  ⇔
  vs_to_i2 cenv vs vs' ∧
  v_to_i2 cenv v v'`,
 induct_on `vs` >>
 rw [] >>
 cases_on `vs'` >>
 rw [v_to_i2_eqns] 
 >- (cases_on `vs` >>
     rw [v_to_i2_eqns]) >>
 metis_tac []);

val vs_to_i2_append = Q.prove (
`!cenv vs1 vs1' vs2 vs2'.
  LENGTH vs2 = LENGTH vs2'
  ⇒
  (vs_to_i2 cenv (vs1++vs2) (vs1'++vs2') ⇔
   vs_to_i2 cenv vs1 vs1' ∧ vs_to_i2 cenv vs2 vs2')`,
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
`!s uop v s' v' cenv s_i2 v_i2.
  do_uapp_i1 s uop v = SOME (s',v') ∧
  s_to_i2' cenv s s_i2 ∧
  v_to_i2 cenv v v_i2
  ⇒
  ∃s'_i2 v'_i2.
    s_to_i2' cenv s' s'_i2 ∧
    v_to_i2 cenv v' v'_i2 ∧
    do_uapp_i2 s_i2 uop v_i2 = SOME (s'_i2,v'_i2)`,
 cases_on `uop` >>
 rw [do_uapp_i1_def, do_uapp_i2_def, LET_THM, store_alloc_def, s_to_i2'_cases] >>
 rw [vs_to_i2_append1, v_to_i2_eqns]
 >- metis_tac [length_vs_to_i2] >>
 every_case_tac >>
 fs [v_to_i2_eqns]
 >- metis_tac [store_lookup_vs_to_i2_2, NOT_SOME_NONE] 
 >- metis_tac [store_lookup_vs_to_i2]);

val exn_env_i2_correct = Q.prove (
`!cenv cenv'.
  env_all_to_i2 (next,lex_cenv,type_cenv,inverse_cenv) env env_i2 cenv'
  ⇒
  env_all_to_i2 (next,FST (SND init_cenv_mapping),type_cenv,inverse_cenv) (exn_env_i1 (all_env_i1_to_genv env))
    (exn_env_i2 (all_env_i2_to_genv env_i2)) cenv'`,
 rw [env_all_to_i2_cases, exn_env_i1_def, exn_env_i2_def, emp_def, v_to_i2_eqns,
     all_env_i1_to_genv_def, all_env_i2_to_genv_def, init_cenv_mapping_def] >>
 fs [cenv_inv_def, lookup_con_id_def] >>
 rw [] >>
 every_case_tac >>
 fs [] >>
 rw [id_to_n_def] >>
 fs [has_exns_def] >>
 fs [flookup_fupdate_list] >>
 metis_tac []);

val do_eq_i2 = Q.prove (
`(!v1 v2 cenv r v1_i2 v2_i2 cenv'.
  env_all_to_i2 cenv env env_i2 cenv' ∧
  do_eq_i1 v1 v2 = r ∧
  v_to_i2 cenv' v1 v1_i2 ∧
  v_to_i2 cenv' v2 v2_i2
  ⇒ 
  do_eq_i2 v1_i2 v2_i2 = r) ∧
 (!vs1 vs2 cenv r vs1_i2 vs2_i2 cenv'.
  env_all_to_i2 cenv env env_i2 cenv' ∧
  do_eq_list_i1 vs1 vs2 = r ∧
  vs_to_i2 cenv' vs1 vs1_i2 ∧
  vs_to_i2 cenv' vs2 vs2_i2
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
 >- metis_tac [cenv_inv_def]
 >- metis_tac [cenv_inv_def]
 >- metis_tac [cenv_inv_def]
 >- metis_tac [cenv_inv_def]
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
`!env s op v1 v2 s' e env' cenv s_i2 v1_i2 v2_i2 env_i2 cenv'.
  do_app_i1 env s op v1 v2 = SOME (env',s',e) ∧
  env_all_to_i2 cenv env env_i2 cenv' ∧
  s_to_i2' cenv' s s_i2 ∧
  v_to_i2 cenv' v1 v1_i2 ∧
  v_to_i2 cenv' v2 v2_i2
  ⇒
  ∃s'_i2 env'_i2 cenv.
    env_all_to_i2 cenv env' env'_i2 cenv' ∧
    s_to_i2' cenv' s' s'_i2 ∧
    do_app_i2 env_i2 s_i2 op v1_i2 v2_i2 = SOME (env'_i2,s'_i2,exp_to_i2 (cenv_mapping_to_lex_cenv cenv) e)`,
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
     rw [exp_to_i2_def] >>
     `?next lex_cenv type_cenv inverse_cenv. cenv = (next,lex_cenv,type_cenv,inverse_cenv)` by metis_tac [pair_CASES] >>
     rw []
     >- (qexists_tac `(next,FST (SND init_cenv_mapping),type_cenv,inverse_cenv)` >>
         rw []
         >- metis_tac [exn_env_i2_correct]
         >- rw [init_cenv_mapping_def, flookup_fupdate_list, lookup_tag_def, cenv_mapping_to_lex_cenv_def])
     >- (qexists_tac `(next,FST (SND init_cenv_mapping),type_cenv,inverse_cenv)` >>
         rw []
         >- metis_tac [exn_env_i2_correct]
         >- rw [init_cenv_mapping_def, flookup_fupdate_list, lookup_tag_def, cenv_mapping_to_lex_cenv_def])
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
     >- (`?next lex_cenv type_cenv inverse_cenv. cenv = (next,lex_cenv,type_cenv,inverse_cenv)` by metis_tac [pair_CASES] >>
         rw [] >>
         qexists_tac `(next,FST (SND init_cenv_mapping),type_cenv,inverse_cenv)` >>
         rw []
         >- metis_tac [exn_env_i2_correct]
         >- rw [init_cenv_mapping_def, flookup_fupdate_list, lookup_tag_def, cenv_mapping_to_lex_cenv_def])
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct]
     >- metis_tac [do_eq_i2, eq_result_11, eq_result_distinct])
 >- (every_case_tac >>
     fs [] >>
     pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once v_to_i2_cases]) >>
     rw []
     >- (qexists_tac `(next,lex_cenv,cenv'',inverse_cenv)` >>
         rw [] >>
         fs [env_all_to_i2_cases, bind_def] >>
         rw [v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def, cenv_mapping_to_lex_cenv_def])
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
     >- (qexists_tac `(next,lex_cenv,cenv'',inverse_cenv)` >>
         rw [] >>
         fs [env_all_to_i2_cases, bind_def] >>
         rw [v_to_i2_eqns, all_env_i1_to_genv_def, all_env_i2_to_genv_def, 
             build_rec_env_i1_merge, build_rec_env_i2_merge, merge_def] >>
         fs [funs_to_i2_map]
         >- (match_mp_tac env_to_i2_append >>
             rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, env_to_i2_el,
                 EL_MAP] >>
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
             fs [cenv_mapping_to_lex_cenv_def])))
 >- (every_case_tac >>
     fs [] >>
     rw [] >>
     fs [v_to_i2_eqns, store_assign_def] 
     >- metis_tac [length_vs_to_i2, s_to_i2'_cases] >>
     rw [exp_to_i2_def, s_to_i2'_cases] >>
     metis_tac [vs_to_i2_lupdate, s_to_i2'_cases]));

val exp_to_i2_correct = Q.prove (
`(∀b env s e res. 
   evaluate_i1 b env s e res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !cenv s' r env_i2 s_i2 e_i2 cenv'.
     (res = (s',r)) ∧
     env_all_to_i2 cenv env env_i2 cenv' ∧
     s_to_i2 cenv' s s_i2 ∧
     (e_i2 = exp_to_i2 (cenv_mapping_to_lex_cenv cenv) e)
     ⇒
     ∃s'_i2 r_i2.
       result_to_i2 v_to_i2 cenv' r r_i2 ∧
       s_to_i2 cenv' s' s'_i2 ∧
       evaluate_i2 b env_i2 s_i2 e_i2 (s'_i2, r_i2)) ∧
 (∀b env s es res.
   evaluate_list_i1 b env s es res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !cenv s' r env_i2 s_i2 es_i2 cenv'.
     (res = (s',r)) ∧
     env_all_to_i2 cenv env env_i2 cenv' ∧
     s_to_i2 cenv' s s_i2 ∧
     (es_i2 = exps_to_i2 (cenv_mapping_to_lex_cenv cenv) es)
     ⇒
     ?s'_i2 r_i2.
       result_to_i2 vs_to_i2 cenv' r r_i2 ∧
       s_to_i2 cenv' s' s'_i2 ∧
       evaluate_list_i2 b env_i2 s_i2 es_i2 (s'_i2, r_i2)) ∧
 (∀b env s v pes err_v res. 
   evaluate_match_i1 b env s v pes err_v res ⇒ 
   (SND res ≠ Rerr Rtype_error) ⇒
   !cenv s' r env_i2 s_i2 v_i2 pes_i2 err_v_i2 cenv'.
     (res = (s',r)) ∧
     env_all_to_i2 cenv env env_i2 cenv' ∧
     s_to_i2 cenv' s s_i2 ∧
     v_to_i2 cenv' v v_i2 ∧
     (pes_i2 = pat_exp_to_i2 (cenv_mapping_to_lex_cenv cenv) pes) ∧
     v_to_i2 cenv' err_v err_v_i2
     ⇒
     ?s'_i2 r_i2.
       result_to_i2 v_to_i2 cenv' r r_i2 ∧
       s_to_i2 cenv' s' s'_i2 ∧
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
     MAP_EVERY qexists_tac [`s'_i2`, `Rval (Conv_i2 (lookup_tag cn lex_cenv) v')`] >>
     rw [] >>
     Cases_on `cn` >>
     fs [] >>
     rw [v_to_i2_eqns, lookup_tag_def] >>
     fs [all_env_i1_to_cenv_def] >>
     every_case_tac >>
     fs [cenv_mapping_to_lex_cenv_def] >>
     rw [v_to_i2_eqns]
     >- metis_tac [NOT_SOME_NONE, cenv_inv_def]
     >- metis_tac [NOT_SOME_NONE, cenv_inv_def]
     >- metis_tac [NOT_SOME_NONE, cenv_inv_def]
     >- metis_tac [NOT_SOME_NONE, cenv_inv_def]
     >- (fs [cenv_inv_def, do_con_check_def] >>
         rw [] >>
         metis_tac [length_evaluate_list_i2, length_vs_to_i2])
     >- metis_tac [NOT_SOME_NONE, cenv_inv_def])
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
     metis_tac [genv_to_i2_lookup, length_vs_to_i2])
 >- (rw [Once v_to_i2_cases] >>
     fs [env_all_to_i2_cases] >>
     rw [all_env_i1_to_env_def, all_env_i2_to_env_def, all_env_i1_to_cenv_def, cenv_mapping_to_lex_cenv_def] >>
     metis_tac [])
 >- (* Uapp *)
    (res_tac >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     `?s3_i2 v'_i2. do_uapp_i2 s''' uop v'' = SOME (s3_i2, v'_i2) ∧
       s_to_i2' cenv' s3 s3_i2 ∧ v_to_i2 cenv' v' v'_i2` by metis_tac [do_uapp_correct] >>
     metis_tac [])
 >- metis_tac []
 >- (* App *)
    (LAST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s_i2`, `cenv'`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s'_i2`, `cenv'`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     (qspecl_then [`env`, `s3`, `op`, `v1`, `v2`, `s4`, `e''`, `env'`,
                   `cenv`, `s'''''''`, `v'`, `v''`, `env_i2`, `cenv'`] mp_tac) do_app_i2_correct >>
     rw [] >>
     metis_tac [])
 >- (* App *)
    (LAST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s_i2`, `cenv'`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s'_i2`, `cenv'`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     (qspecl_then [`env`, `s3`, `op`, `v1`, `v2`, `s4`, `e''`, `env'`,
                   `cenv`, `s'''''''`, `v'`, `v''`, `env_i2`, `cenv'`] mp_tac) do_app_i2_correct >>
     rw [] >>
     metis_tac [])
 >- (* App *)
    (LAST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s_i2`, `cenv'`] mp_tac) >>
     rw [] >>
     LAST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s'_i2`, `cenv'`] mp_tac) >>
     rw [] >>
     fs [s_to_i2_cases] >>
     rw [] >>
     metis_tac [do_app_i2_correct])
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
     FIRST_X_ASSUM (qspecl_then [`cenv`, `env_i2`, `s'_i2'`, `v''`, `Conv_i2 bind_tag []`, `cenv'` ] mp_tac) >>
     rw [] >>
     fs [env_all_to_i2_cases] >>
     rw [] >>
     fs [cenv_inv_def, has_exns_def] >>
     pop_assum mp_tac >>
     rw [] >>
     MAP_EVERY qexists_tac [`s'_i2''`, `r_i2`] >>
     rw [] >>
     metis_tac [])
 >- metis_tac []
 >- metis_tac []
 >- (* Let *)
    (`?genv' env'. env_i2 = (genv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     res_tac >>
     fs [] >>
     rw [] >>
     `env_all_to_i2 cenv' (genv,cenv,bind n v env) (genv', (n,v')::env') cenv''`
                by (fs [env_all_to_i2_cases] >>
                    fs [bind_def, v_to_i2_eqns] >>
                    rw []) >>
     metis_tac [bind_def])
 >- metis_tac []
 >- metis_tac []
 >- (* Letrec *)
    (pop_assum mp_tac >>
     rw [] >>
     `?genv' env'. env_i2 = (genv',env')` by metis_tac [pair_CASES] >>
     rw [] >>
     `env_all_to_i2 cenv' (genv,cenv,build_rec_env_i1 funs (cenv,env) env) 
                          (genv',build_rec_env_i2 (funs_to_i2 (cenv_mapping_to_lex_cenv cenv') funs) env' env') 
                          cenv''`
         by (fs [env_all_to_i2_cases] >>
             rw [build_rec_env_i1_merge, build_rec_env_i2_merge, merge_def] >>
             match_mp_tac env_to_i2_append >>
             rw [cenv_mapping_to_lex_cenv_def] >>
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
     `match_result_to_i2 (cenv''',clengths) (Match env') 
            (pmatch_i2 s'' (pat_to_i2 lex_cenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 s'' (pat_to_i2 lex_cenv p) v_i2 env_i2'` >>
     fs [match_result_to_i2_def] >>
     rw [] >>
     fs [METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     FIRST_X_ASSUM (qspecl_then [`clengths`, `lex_cenv`, `next`, `cenv'''`, `inverse_cenv`, `a`, `genv_i2`, `s''`] mp_tac) >>
     rw [] >>
     fs [cenv_mapping_to_lex_cenv_def] >>
     MAP_EVERY qexists_tac [`(c, s''''')`, `r_i2`] >>
     rw [] >>
     metis_tac [pat_bindings_to_i2])
 >- (pop_assum mp_tac >>
     rw [] >>
     fs [s_to_i2_cases, env_all_to_i2_cases] >>
     rw [] >>
     `match_result_to_i2 (cenv''',clengths) No_match 
            (pmatch_i2 s'' (pat_to_i2 lex_cenv p) v_i2 env_i2')`
                   by metis_tac [pmatch_to_i2_correct, match_result_distinct] >>
     cases_on `pmatch_i2 s'' (pat_to_i2 lex_cenv p) v_i2 env_i2'` >>
     fs [match_result_to_i2_def] >>
     rw [cenv_mapping_to_lex_cenv_def] >>
     fs [cenv_mapping_to_lex_cenv_def,
         METIS_PROVE [] ``(((?x. P x) ∧ R ⇒ Q) ⇔ !x. P x ∧ R ⇒ Q) ∧ ((R ∧ (?x. P x) ⇒ Q) ⇔ !x. R ∧ P x ⇒ Q) ``] >>
     metis_tac [pat_bindings_to_i2]));

val cenv_mapping_to_cenv_def = Define `
cenv_mapping_to_cenv cenv_mapping clengths =
   case cenv_mapping of
     (a,b,c,d) => (c, clengths)`;

val merge_envC_empty = Q.prove (
`!envC. merge_envC (emp,emp) envC = envC ∧ merge_envC ([],[]) envC = envC`,
rw [emp_def] >>
PairCases_on `envC` >>
rw [merge_envC_def, merge_def]);

(*
val alloc_tag_cenv_inv = Q.prove (
`!envC mn cenv types clengths.
  cenv_inv envC cenv clengths ∧
  lookup x new_tds = SOME (l, t)
  ⇒
  ?clengths'. 
    cenv_inv (merge_envC ([],new_tds) envC) (alloc_tag mn t x cenv) clengths' ∧
    cenv_weak (cenv_mapping_to_cenv cenv clengths) (cenv_mapping_to_cenv (alloc_tag mn t x cenv) clengths')`,

 rw [] >>
 PairCases_on `cenv` >>
 rw [alloc_tag_def, cenv_mapping_to_cenv_def, cenv_inv_def, cenv_weak_def] >>
 qexists_tac `clengths |+ ((x,t),l)` >>
 rw [FLOOKUP_UPDATE]

val alloc_tags_cenv_inv = Q.prove (
`!envC mn cenv types clengths.
  cenv_inv envC cenv clengths 
  ⇒
  ?clengths'. 
    cenv_inv (merge_envC ([],new_tds) envC) (alloc_tags mn cenv types) clengths' ∧
    cenv_weak (cenv_mapping_to_cenv cenv clengths) (cenv_mapping_to_cenv (alloc_tags mn cenv types) clengths')`,
cheat);

  (*
 induct_on `types` >>
 rw [alloc_tags_def] >>
 PairCases_on `h` >>
 rw [alloc_tags_def, LET_THM]
 induct_on `h2` >>
 rw [] >>
 PairCases_on `h` >>
 rw [] >>
 res_tac
 *)

val extend_cenv_inv = Q.prove (
`!cenv_mapping ds cenv_mapping' ds_i2.
  cenv_inv envC cenv_mapping clengths /\
  decs_to_i2 cenv_mapping ds = (cenv_mapping', ds_i2)
  ==>
  ?clengths'. 
    cenv_inv envC cenv_mapping' clengths' ∧
    cenv_weak (cenv_mapping_to_cenv cenv_mapping clengths) (cenv_mapping_to_cenv cenv_mapping' clengths')`,
cheat);

(*
 induct_on `ds` >>
 rw [decs_to_i2_def] >>
 rw [] >>
 every_case_tac >>
 fs [LET_THM]
 >- (`?cenv_mapping' ds'. decs_to_i2 cenv_mapping ds = (cenv_mapping', ds')` by metis_tac [pair_CASES] >>
     fs [] >>
     metis_tac [])
 >- (`?cenv_mapping' ds'. decs_to_i2 cenv_mapping ds = (cenv_mapping', ds')` by metis_tac [pair_CASES] >>
     fs [] >>
     metis_tac [])
 >- (FIRST_X_ASSUM match_mp_tac >>
     Q.LIST_EXISTS_TAC [`alloc_tags o' cenv_mapping l`, `ds_i2`] >>
     rw [] >>
     pop_assum (fn _ => all_tac) >>
     pop_assum mp_tac >>
     Q.SPEC_TAC (`cenv_mapping`, `cenv_mapping`) >>
     induct_on `l` >>
     fs [cenv_inv_def, alloc_tags_def] >>
     rw [] >>
     PairCases_on `h` >>
     rw [alloc_tags_def, LET_THM] >>
     FIRST_X_ASSUM match_mp_tac >>

     induct_on `h2` >>
     rw [LAMBDA_PROD, allo]
     *)

val extend_cenv_inv2 = Q.prove (
`!cenv_mapping ds cenv_mapping' ds_i2.
  cenv_inv envC cenv_mapping clengths /\
  cenv_inv (merge_envC ([],new_tds) envC) cenv_mapping' clengths' /\
  decs_to_i2 cenv_mapping ds = (cenv_mapping', ds_i2)
  ==>
  cenv_weak (cenv_mapping_to_cenv cenv_mapping clengths) (cenv_mapping_to_cenv cenv_mapping' clengths')`,
cheat);

val recfun_helper = Q.prove (
`cenv_inv envC cenv_mapping clengths
 ⇒
 vs_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) 
          (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l)
          (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (cenv_mapping_to_lex_cenv cenv_mapping) e)) l)`,
induct_on `l` >>
rw [v_to_i2_eqns] >>
PairCases_on `h` >>
rw [] >>
rw [Once v_to_i2_cases] >>
rw [v_to_i2_eqns] >>
PairCases_on `cenv_mapping` >>
rw [cenv_mapping_to_cenv_def, cenv_mapping_to_lex_cenv_def] >>
metis_tac []);

val decs_to_i2_correct = Q.prove (
`!genv envC s1 ds r.
  evaluate_decs_i1 genv envC s1 ds r
  ⇒
  !s1_i2 genv_i2 cenv_mapping ds_i2 cenv_mapping' genv' envC' s' res clengths.
    r = (s', envC', genv', res) ∧
    res ≠ SOME Rtype_error ∧
    (cenv_mapping', ds_i2) = decs_to_i2 cenv_mapping ds ∧
    cenv_inv envC cenv_mapping clengths ∧
    s_to_i2' (cenv_mapping_to_cenv cenv_mapping clengths) s1 s1_i2 ∧
    vs_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) genv genv_i2
    ⇒
    ?r_i2 genv'_i2 s'_i2 res_i2 clengths'.
      evaluate_decs_i2 genv_i2 s1_i2 ds_i2 (s'_i2,genv'_i2,res_i2) ∧
      cenv_inv (merge_envC (emp,envC') envC) cenv_mapping' clengths' ∧
      vs_to_i2 (cenv_mapping_to_cenv cenv_mapping' clengths') genv' genv'_i2 ∧
      s_to_i2' (cenv_mapping_to_cenv cenv_mapping' clengths') s' s'_i2 ∧
      (res = NONE ∧ res_i2 = NONE ∨
       ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ result_to_i2 (\a b c. T) (cenv_mapping_to_cenv cenv_mapping' clengths') (Rerr err) (Rerr err_i2))`,
 ho_match_mp_tac evaluate_decs_i1_ind >>
 rw [decs_to_i2_def] >>
 every_case_tac >>
 fs [LET_THM, evaluate_dec_i1_cases] >>
 rw []  
 >- (fs [emp_def, Once evaluate_decs_i2_cases, v_to_i2_eqns, s_to_i2'_cases] >>
     PairCases_on `cenv_mapping` >>
     fs [merge_envC_empty, cenv_inv_def, cenv_mapping_to_cenv_def] >>
     qexists_tac `clengths` >>
     rw [] >>
     metis_tac [])
 >- (`?cenv_mapping' ds_i2. decs_to_i2 cenv_mapping ds = (cenv_mapping', ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [Once evaluate_decs_i2_cases] >>
     fs [s_to_i2'_cases] >>
     `env_all_to_i2 cenv_mapping (genv,envC,emp) (genv_i2,[]) (cenv_mapping_to_cenv cenv_mapping clengths)` 
                 by (fs [env_all_to_i2_cases, cenv_mapping_to_cenv_def] >>
                     rw [emp_def, v_to_i2_eqns] >>
                     every_case_tac >>
                     metis_tac []) >>
     imp_res_tac exp_to_i2_correct >>
     fs [] >>
     pop_assum mp_tac >>
     rw [s_to_i2_cases, s_to_i2'_cases] >>
     res_tac >>
     fs [] >>
     res_tac >>
     fs [] >>
     rw [evaluate_dec_i2_cases] >>
     `?clengths'.
       cenv_inv envC cenv_mapping' clengths' ∧
       cenv_weak (cenv_mapping_to_cenv cenv_mapping clengths) (cenv_mapping_to_cenv cenv_mapping' clengths')` 
                   by metis_tac [extend_cenv_inv] >>
     fs [emp_def, result_to_i2_cases, v_to_i2_eqns] >>
     rw [merge_envC_empty] >>
     metis_tac [v_to_i2_weakening])
 >- (`?cenv_mapping' ds_i2. decs_to_i2 cenv_mapping ds = (cenv_mapping', ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [Once evaluate_decs_i2_cases] >>
     fs [s_to_i2'_cases] >>
     `env_all_to_i2 cenv_mapping (genv,envC,emp) (genv_i2,[]) (cenv_mapping_to_cenv cenv_mapping clengths)` 
                 by (fs [env_all_to_i2_cases, cenv_mapping_to_cenv_def] >>
                     rw [emp_def, v_to_i2_eqns] >>
                     every_case_tac >>
                     metis_tac []) >>
     `?s' r_i2. result_to_i2 v_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) (Rval (Conv_i1 NONE new_env)) r_i2 ∧
                vs_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) s1' s' ∧
                evaluate_i2 F (genv_i2,[]) (0,s1_i2) (exp_to_i2 (cenv_mapping_to_lex_cenv cenv_mapping) e) ((count',s'),r_i2)` 
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
     fs [result_to_i2_cases, v_to_i2_eqns, merge_envC_empty] >>
     rw [] >>
     `vs_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) (genv ++ new_env) (genv_i2++vs')` 
                  by metis_tac [vs_to_i2_append, length_vs_to_i2] >>
     res_tac >>
     fs [] >>
     pop_assum mp_tac >>
     rw [] >>
     pop_assum (fn _ => all_tac) >>
     fs [emp_def, merge_def] >>
     `cenv_weak (cenv_mapping_to_cenv cenv_mapping clengths) (cenv_mapping_to_cenv cenv_mapping' clengths'')`
                by metis_tac [extend_cenv_inv2] >>
     `vs_to_i2 (cenv_mapping_to_cenv cenv_mapping' clengths'') (new_env ++ new_env') (vs' ++ genv'_i2)`
                  by metis_tac [vs_to_i2_append, length_vs_to_i2, v_to_i2_weakening] >>
     metis_tac [length_vs_to_i2])
 >- (`?cenv_mapping' ds_i2. decs_to_i2 cenv_mapping ds = (cenv_mapping', ds_i2)` by metis_tac [pair_CASES] >>
     fs [] >>
     rw [] >>
     fs [emp_def, merge_def, merge_envC_empty] >>
     `vs_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) 
               (genv ++ MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l)
               (genv_i2 ++ MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (cenv_mapping_to_lex_cenv cenv_mapping) e)) l)`
              by metis_tac [recfun_helper, length_vs_to_i2, vs_to_i2_append] >>
     res_tac >>
     pop_assum mp_tac >>
     rw [] >>
     rw [Once evaluate_decs_i2_cases, evaluate_dec_i2_cases] >>
     `vs_to_i2 (cenv_mapping_to_cenv cenv_mapping' clengths'') 
               (MAP (\(f,x,e). Closure_i1 (envC,[]) x e) l ++ new_env') 
               (MAP (\(f,x,e). Closure_i2 [] x (exp_to_i2 (cenv_mapping_to_lex_cenv cenv_mapping) e)) l ++ genv'_i2)`
               by metis_tac [extend_cenv_inv2, recfun_helper, v_to_i2_weakening, vs_to_i2_append, length_vs_to_i2] >>
     rw [funs_to_i2_map, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]
     >- metis_tac [] >>
     fs [result_to_i2_cases] >>
     metis_tac [])
 >- (fs [merge_envC_empty_assoc, merge_def, emp_def] >>
     FIRST_X_ASSUM match_mp_tac >>
     metis_tac [extend_cenv_inv2, v_to_i2_weakening, s_to_i2'_cases, alloc_tags_cenv_inv])
 >- (fs [merge_envC_empty_assoc, merge_def, emp_def] >>
     FIRST_X_ASSUM match_mp_tac >>
     metis_tac [extend_cenv_inv2, v_to_i2_weakening, s_to_i2'_cases, alloc_tag_cenv_inv]));


     (*
val prompt_to_i2_correct = Q.prove (
`!genv envC s prompt r.
  evaluate_prompt_i1 genv envC s prompt r
  ⇒
  !s1_i2 genv_i2 cenv_mapping prompt_i2 cenv_mapping' genv' envC' s' res clengths.
    r = (s', envC', genv', res) ∧
    res ≠ SOME Rtype_error ∧
    (cenv_mapping', prompt_i2) = prompt_to_i2 cenv_mapping prompt ∧
    cenv_inv envC cenv_mapping clengths ∧
    s_to_i2' (cenv_mapping_to_cenv cenv_mapping clengths) s s1_i2 ∧
    vs_to_i2 (cenv_mapping_to_cenv cenv_mapping clengths) genv genv_i2
    ⇒
    ?genv'_i2 s'_i2 res_i2 clengths'.
      evaluate_prompt_i2 genv_i2 s1_i2 prompt_i2 (s'_i2,genv'_i2,res_i2) ∧
      cenv_inv (merge_envC envC' envC) cenv_mapping' clengths' ∧
      vs_to_i2 (cenv_mapping_to_cenv cenv_mapping' clengths') genv' genv'_i2 ∧
      s_to_i2' (cenv_mapping_to_cenv cenv_mapping' clengths') s' s'_i2 ∧
      (res = NONE ∧ res_i2 = NONE ∨
       ?err err_i2. res = SOME err ∧ res_i2 = SOME err_i2 ∧ result_to_i2 (\a b c. T) (cenv_mapping_to_cenv cenv_mapping' clengths') (Rerr err) (Rerr err_i2))`,

 rw [evaluate_prompt_i1_cases, evaluate_prompt_i2_cases, prompt_to_i2_def] >>
 every_case_tac >>
 fs [LET_THM] >>
 rw [] >>
 `?cenv_mapping' prompt_i2. decs_to_i2 cenv_mapping ds = (cenv_mapping',prompt_i2)` by metis_tac [pair_CASES] >>
 fs [] >>
 rw []
 metis_tac [ decs_to_i2_correct, NOT_SOME_NONE]

 *)
 *)
val _ = export_theory ();
