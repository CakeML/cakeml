open preamble;
open alistTheory optionTheory rich_listTheory;
open miscLib miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open conLangTheory;
open decLangTheory;
open evalPropsTheory;
open compilerTerminationTheory;

val _ = new_theory "decLangProof";

val do_app_i3_correct = prove(
  ``∀s op vs res.
      do_app_i2 s op vs = SOME res ⇒
      ∀c g. do_app_i3 ((c,s),g) op vs = SOME (((c,FST res),g),SND res)``,
  rw[do_app_i2_def,do_app_i3_def] >>
  Cases_on`op`>>fs[]>>
  rpt(BasicProvers.CASE_TAC >> fs[LET_THM,store_alloc_def]))

val exp_to_i3_correct = Q.prove (
`(∀b env s e res.
   evaluate_i2 b env s e res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' exh genv env' r.
     (res = (s',r)) ∧
     (env = (exh:exh_ctors_env,genv,env'))
     ⇒
     evaluate_i3 b (exh,env') (s,genv) e ((s',genv),r)) ∧
 (∀b env s es res.
   evaluate_list_i2 b env s es res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' exh genv env' r.
     (res = (s',r)) ∧
     (env = (exh:exh_ctors_env,genv,env'))
     ⇒
     evaluate_list_i3 b (exh,env') (s,genv) es ((s',genv),r)) ∧
 (∀b env s v pes err_v res.
   evaluate_match_i2 b env s v pes err_v res ⇒
   (SND res ≠ Rerr Rtype_error) ⇒
   !s' exh genv env' r.
     (res = (s',r)) ∧
     (env = (exh:exh_ctors_env,genv,env'))
     ⇒
     evaluate_match_i3 b (exh,env') (s,genv) v pes err_v ((s',genv),r))`,
 ho_match_mp_tac evaluate_i2_ind >>
 rw [] >>
 rw [Once evaluate_i3_cases] >>
 fs [all_env_i2_to_genv_def, all_env_i2_to_env_def]
 >> TRY(metis_tac []) >>
 disj1_tac >>
 first_assum(match_exists_tac o concl) >> rw[] >>
 metis_tac[do_app_i3_correct,FST,SND]);

val do_app_i3_genv_weakening = prove(
  ``do_app_i3 (x,y) op vs = SOME ((a,b),c) ⇒
    do_app_i3 (x,y++z) op vs = SOME ((a,b++z),c)``,
  Cases_on`x` >> rw[do_app_i3_def] >>
  every_case_tac >> fs[] >> rw[] >>
  fsrw_tac[ARITH_ss][EL_APPEND1,LUPDATE_APPEND1])

val eval_i3_genv_weakening = Q.prove (
`(∀ck env s e res.
   evaluate_i3 ck (env:all_env_i3) s e res ⇒
   !s' s'' genv r genv' l.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r)) ∧
     r ≠ Rerr Rtype_error
     ⇒
     evaluate_i3 ck env (s',genv++GENLIST (\x.NONE) l) e ((s'',genv'++GENLIST (\x.NONE) l),r)) ∧
 (∀ck env s es res.
   evaluate_list_i3 ck (env:all_env_i3) s es res ⇒
   !s' s'' genv genv' l r.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r)) ∧
     r ≠ Rerr Rtype_error
     ⇒
     evaluate_list_i3 ck env (s',genv++GENLIST (\x.NONE) l) es ((s'',genv'++GENLIST (\x.NONE) l),r) )∧
 (∀ck env s v pes err_v res.
   evaluate_match_i3 ck (env:all_env_i3) s v pes err_v res ⇒
   !s' s'' genv genv' l r.
     (s = (s',genv)) ∧
     (res = ((s'',genv'),r)) ∧
     r ≠ Rerr Rtype_error
     ⇒
     evaluate_match_i3 ck env (s',genv++GENLIST (\x.NONE) l) v pes err_v ((s'',genv'++GENLIST (\x.NONE) l),r))`,
 ho_match_mp_tac evaluate_i3_ind >>
 rw [] >>
 srw_tac [ARITH_ss] [Once evaluate_i3_cases]
 >- metis_tac [pair_CASES]
 >- srw_tac [ARITH_ss] [EL_APPEND1] >>
 srw_tac[ARITH_ss][GSYM GENLIST_APPEND]>>
 metis_tac[pair_CASES,do_app_i3_genv_weakening])

val eval_i3_extend_genv = Q.prove (
`!b env s genv n s' genv' v.
  evaluate_i3 b env (s,genv) (Extend_global_i2 n) (s',r)
  ⇔
  r = Rval (Litv_i2 Unit) ∧
  s' = (s,genv ++ GENLIST (\x. NONE) n)`,
 rw [Once evaluate_i3_cases] >>
 metis_tac []);

val eval_i3_var =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Var_local_i2 var) (s',r)``;

val eval_i3_con =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Con_i2 tag es) (s',r)``;

val eval_i3_mat =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Mat_i2 e pes) (s',r)``;

val eval_i3_fun =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_i3 b env s (Fun_i2 x e) (s',r)``;

val eval_i3_let =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases, opt_bind_def] ``evaluate_i3 b env s (Let_i2 NONE e1 e2) (s',r)``;

val eval_match_i3_nil =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_match_i3 b env s v [] err_v (s',r)``;

val eval_match_i3_var =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases, eval_match_i3_nil, eval_i3_var, pmatch_i2_def, eval_i3_con]
  ``evaluate_match_i3 b env s v [(Pvar_i2 var, Con_i2 n [Var_local_i2 var])] err_v (s',r)``;

val eval_match_i3_var2 =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases, eval_match_i3_nil, eval_i3_var, pmatch_i2_def, eval_i3_con, pat_bindings_i2_def]
  ``evaluate_match_i3 b env s v [(Pvar_i2 var, Var_local_i2 var)] err_v (s',r)``;

val eval_i3_nil =
  SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_list_i3 b env s [] (s',r)``

val eval_i3_cons =
  SIMP_CONV (srw_ss()) [Once evaluate_i3_cases] ``evaluate_list_i3 b env s (e::es) (s',r)``

val eval_init_global_fun =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases, eval_i3_fun, do_app_i3_def,
   EXISTS_PROD,eval_i3_cons,eval_i3_nil,PULL_EXISTS,option_case_compute]
  ``evaluate_i3 b env s (App_i2 (Init_global_var_i2 i) [Fun_i2 x e]) (s',r)``;

val eval_match_i3_con =
SIMP_CONV (srw_ss()) [Once evaluate_i3_cases, pmatch_i2_def, pat_bindings_i2_def, eval_match_i3_var2, bind_def]
  ``evaluate_match_i3 b env s v [(Pcon_i2 n [], e); (Pvar_i2 "x",Var_local_i2 "x")] err_v (s',r)``;

val (dec_result_to_i3_rules, dec_result_to_i3_ind, dec_result_to_i3_cases) = Hol_reln `
(∀v. dec_result_to_i3 NONE (Rval v)) ∧
(∀err. dec_result_to_i3 (SOME (Rraise err)) (Rerr (Rraise err))) ∧
(dec_result_to_i3 (SOME Rtype_error) (Rerr Rtype_error)) ∧
(dec_result_to_i3 (SOME Rtimeout_error) (Rerr Rtimeout_error))`;

val pmatch_list_i2_Pvar = prove(
  ``∀xs exh vs s env.
      LENGTH xs = LENGTH vs ⇒
      pmatch_list_i2 exh s (MAP Pvar_i2 xs) vs env = Match (REVERSE(ZIP(xs,vs))++env)``,
  Induct >> simp[LENGTH_NIL_SYM,pmatch_i2_def] >>
  Cases_on`vs`>>simp[pmatch_i2_def,bind_def]);

val pats_bindings_i2_MAP_Pvar = prove(
  ``∀ws ls. pats_bindings_i2 (MAP Pvar_i2 ws) ls = (REVERSE ws) ++ ls``,
  Induct >> simp[pat_bindings_i2_def]);

val init_globals_thm = Q.prove (
`!new_env genv vs env. LENGTH vs = LENGTH new_env ∧ ALL_DISTINCT vs ⇒
  evaluate_match_i3 ck env (s, genv ++ GENLIST (λt. NONE) (LENGTH new_env)) (Conv_i2 (tuple_tag,NONE) new_env)
  [(Pcon_i2 (tuple_tag,NONE) (MAP Pvar_i2 vs), init_globals vs (LENGTH genv))]
  (Conv_i2 (bind_tag,SOME (TypeExn (Short "Bind"))) [])
  ((s,genv ++ MAP SOME new_env), Rval (Litv_i2 Unit))`,
  Induct >- (
    simp[Once evaluate_i3_cases,pmatch_i2_def,init_globals_def,LENGTH_NIL] >>
    simp[Once evaluate_i3_cases,pat_bindings_i2_def] >>
    metis_tac [pair_CASES]) >>
  qx_genl_tac[`v`,`genv`,`vs0`,`env`] >> strip_tac >>
  `∃w ws. vs0 = w::ws` by (Cases_on`vs0`>>fs[])>>
  first_x_assum(qspecl_then[`genv++[SOME v]`,`ws`]mp_tac) >>
  fs[] >> strip_tac >>
  simp[Once evaluate_i3_cases] >> disj1_tac >>
  simp[pmatch_i2_def,pat_bindings_i2_def] >>
  PairCases_on`s`>>fs[] >>
  simp[pmatch_list_i2_Pvar,pats_bindings_i2_MAP_Pvar,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE] >>
  pop_assum mp_tac >>
  simp[Once evaluate_i3_cases,pat_bindings_i2_def,pmatch_i2_def
      ,pmatch_list_i2_Pvar,pats_bindings_i2_MAP_Pvar,ALL_DISTINCT_REVERSE
      ,GENLIST_CONS,init_globals_def] >> strip_tac >>
  simp[Once evaluate_i3_cases] >>
  simp[Once evaluate_i3_cases] >>
  simp[Once evaluate_i3_cases] >>
  simp[Once evaluate_i3_cases] >>
  simp[Once evaluate_i3_cases] >>
  simp[do_app_i3_def,EL_APPEND1,EL_LENGTH_APPEND,PULL_EXISTS,opt_bind_def] >>
  simp[lookup_append,bind_def] >>
  reverse BasicProvers.CASE_TAC >- (
    imp_res_tac lookup_in2 >>
    fs[MEM_MAP] >> rfs[MEM_ZIP] >>
    fs[] >> metis_tac[MEM_EL] ) >>
  simp[LUPDATE_APPEND1,combinTheory.o_DEF] >>
  PairCases_on `env` >>
  fs [FORALL_PROD] >>
  metis_tac[CONS_APPEND,APPEND_ASSOC]);

val init_globals_thm = prove(
``!new_env.
  evaluate_match_i3 ck (exh,[]) (s, genv ++ GENLIST (λt. NONE) (LENGTH new_env)) (Conv_i2 (tuple_tag,NONE) new_env)
    [(Pcon_i2 (tuple_tag,NONE) (MAP Pvar_i2 (GENLIST (λn. STRING #"x" (toString n)) (LENGTH new_env))),
      init_globals (GENLIST (λn. STRING #"x" (toString n)) (LENGTH new_env)) (LENGTH genv))]
   (Conv_i2 (bind_tag,SOME (TypeExn (Short "Bind"))) [])
   ((s,genv ++ MAP SOME new_env), Rval (Litv_i2 Unit))``,
  rw[] >> match_mp_tac init_globals_thm >> simp[ALL_DISTINCT_GENLIST])

val init_global_funs_thm = Q.prove (
  `!l genv.
    evaluate_i3 ck (exh,[]) (s, genv ++ GENLIST (λt. NONE) (LENGTH l)) (init_global_funs (LENGTH genv) l)
    ((s,genv ++ MAP SOME (MAP (λ(f,x,e). Closure_i2 [] x e) l)), Rval (Litv_i2 Unit))`,
  Induct >> simp[init_global_funs_def] >- simp[Once evaluate_i3_cases] >>
  qx_gen_tac`f` >> PairCases_on`f` >>
  simp[init_global_funs_def] >>
  simp[Once evaluate_i3_cases] >>
  simp[eval_init_global_fun] >>
  simp[GENLIST_CONS,EL_LENGTH_APPEND,PULL_EXISTS,opt_bind_def] >>
  gen_tac >>
  first_x_assum(qspec_then`genv++[SOME(Closure_i2 [] f1 f2)]`mp_tac) >>
  simp[combinTheory.o_DEF] >>
  Cases_on`s`>>simp[] >>
  metis_tac[APPEND_ASSOC,CONS_APPEND])

val decs_to_i3_correct = Q.store_thm("decs_to_i3_correct",
`!ck exh genv s ds s' new_env r.
  evaluate_decs_i2 ck (exh:exh_ctors_env) genv s ds (s',new_env,r) ∧
  r ≠ SOME Rtype_error
  ⇒
  ?r_i3.
    dec_result_to_i3 r r_i3 ∧
    evaluate_i3 ck (exh,[]) (s,genv ++ GENLIST (\x. NONE) (num_defs ds)) (decs_to_i3 (LENGTH genv) ds)
                ((s',genv ++ MAP SOME new_env ++ GENLIST (\x. NONE) (num_defs ds - LENGTH new_env)),r_i3)`,
 induct_on `ds` >>
 rw [decs_to_i3_def]
 >- fs [Once evaluate_decs_i2_cases, Once evaluate_i3_cases, dec_result_to_i3_cases, num_defs_def] >>
 Cases_on `h` >>
 qpat_assum `evaluate_decs_i2 x0 x1 x2 x3 x4 x5` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_i2_cases]) >>
 rw [num_defs_def, LET_THM] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [] >>
 fs [evaluate_dec_i2_cases] >>
 rw [] >>
 imp_res_tac exp_to_i3_correct >>
 fs [emp_def] >>
 pop_assum mp_tac >>
 rw [eval_i3_mat, opt_bind_def]
 >- (qexists_tac `Rerr e'` >>
     rw [dec_result_to_i3_cases]
     >- (cases_on `e'` >>
         fs [])
     >- metis_tac [eval_i3_genv_weakening, result_11, error_result_distinct])
 >- (res_tac >>
     qexists_tac `r_i3` >>
     srw_tac [ARITH_ss] [GENLIST_APPEND] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`Litv_i2 Unit`, `(s2, genv ++ MAP SOME new_env' ++ GENLIST (λx. NONE) (num_defs ds))`] >>
     rw [] >>
     fs [LENGTH_APPEND] >>
     MAP_EVERY qexists_tac [`Conv_i2 (tuple_tag,NONE) new_env'`, `(s2,genv++GENLIST (λx. NONE) (num_defs ds) ++ GENLIST (λt. NONE) (LENGTH new_env'))`] >>
     rw []
     >- (simp_tac bool_ss [GSYM APPEND_ASSOC, GSYM GENLIST_APPEND] >>
         metis_tac [eval_i3_genv_weakening, result_distinct, pair_CASES])
     >- (`!(l:v_i2 option list) x y. l ++ GENLIST (\x.NONE) y ++ GENLIST (\x.NONE) x = l ++ GENLIST (\x.NONE) x ++ GENLIST (\x.NONE) y`
                  by (rw [] >>
                      `!b. (\x. (\y. NONE) (x + b)) = (\y.NONE)` by rw [EXTENSION] >>
                      srw_tac [ARITH_ss] [GSYM GENLIST_APPEND]) >>
         metis_tac [init_globals_thm, eval_i3_genv_weakening, result_distinct]))
 >- (res_tac >>
     qexists_tac `r_i3` >>
     srw_tac [ARITH_ss] [GENLIST_APPEND] >>
     disj1_tac >>
     MAP_EVERY qexists_tac [`Litv_i2 Unit`, `(s, genv ++ MAP SOME (MAP (λ(f,x,e).  Closure_i2 [] x e) l) ++ GENLIST (λx. NONE) (num_defs ds))`] >>
     rw [] >>
     fs [LENGTH_APPEND] >>
     `!(l:v_i2 option list) x y. l ++ GENLIST (\x.NONE) y ++ GENLIST (\x.NONE) x = l ++ GENLIST (\x.NONE) x ++ GENLIST (\x.NONE) y`
                  by (rw [] >>
                      `!b. (\x. (\y. NONE) (x + b)) = (\y.NONE)` by rw [EXTENSION] >>
                      srw_tac [ARITH_ss] [GSYM GENLIST_APPEND]) >>
     metis_tac [init_global_funs_thm, eval_i3_genv_weakening, result_distinct]))

val prompt_num_defs_def = Define `
prompt_num_defs (Prompt_i2 ds) = num_defs ds`;

val eval_decs_num_defs = Q.prove (
`!ck exh genv s ds s' env.
  evaluate_decs_i2 ck exh genv s ds (s',env,NONE) ⇒ num_defs ds = LENGTH env`,
 induct_on `ds` >>
 rw [num_defs_def] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_i2_cases]) >>
 rw [] >>
 cases_on `h` >>
 rw [num_defs_def] >>
 res_tac >>
 rw [] >>
 fs [evaluate_dec_i2_cases]);

val eval_decs_num_defs_err = Q.prove (
`!ck exh genv s ds s' env. evaluate_decs_i2 ck exh genv s ds (s',env,SOME err) ⇒ LENGTH env <= num_defs ds`,
 induct_on `ds` >>
 rw [num_defs_def] >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_decs_i2_cases]) >>
 rw [] >>
 cases_on `h` >>
 rw [num_defs_def] >>
 res_tac >>
 rw [] >>
 fs [evaluate_dec_i2_cases]);

val (result_to_i3_rules, result_to_i3_ind, result_to_i3_cases) = Hol_reln `
(result_to_i3 NONE (Rval (Conv_i2 (none_tag, SOME (TypeId (Short "option"))) []))) ∧
(∀err. result_to_i3 (SOME (Rraise err)) (Rval (Conv_i2 (some_tag, SOME (TypeId (Short "option"))) [err]))) ∧
(result_to_i3 (SOME Rtype_error) (Rerr Rtype_error)) ∧
(result_to_i3 (SOME Rtimeout_error) (Rerr Rtimeout_error))`;

val prompt_to_i3_correct = Q.store_thm ("prompt_to_i3_correct",
`!ck exh genv s p new_env s' r next' e.
  evaluate_prompt_i2 ck (exh:exh_ctors_env) genv s p (s',new_env,r) ∧
  r ≠ SOME Rtype_error ∧
  ((next',e) = prompt_to_i3 (none_tag, SOME (TypeId (Short "option"))) (some_tag, SOME (TypeId (Short "option"))) (LENGTH genv) p)
  ⇒
  ?r_i3.
    result_to_i3 r r_i3 ∧
    LENGTH genv + LENGTH new_env = next' ∧
    evaluate_i3 ck (exh,[]) (s,genv) e ((s',genv++new_env),r_i3)`,
 rw [evaluate_prompt_i2_cases, prompt_to_i3_def] >>
 fs [LET_THM, eval_i3_let, eval_i3_extend_genv] >>
 rw [eval_i3_con, eval_match_i3_var, pat_bindings_i2_def, bind_def, lookup_def, opt_bind_def, prompt_num_defs_def] >>
 imp_res_tac decs_to_i3_correct >>
 fs [dec_result_to_i3_cases, result_to_i3_cases] >>
 ONCE_REWRITE_TAC [evaluate_i3_cases] >>
 rw [eval_match_i3_var, eval_i3_let, eval_i3_con]
 >- metis_tac [eval_decs_num_defs]
 >- (rw [Once (hd (tl (CONJUNCTS evaluate_i3_cases)))] >>
     imp_res_tac eval_decs_num_defs >>
     fs [] >>
     metis_tac [])
 >- (pop_assum mp_tac >>
     rw [] >>
     rw [] >>
     imp_res_tac eval_decs_num_defs_err
     >- decide_tac
     >- (ntac 4 (rw [Once (hd (tl (CONJUNCTS evaluate_i3_cases)))]) >>
         rw [bind_def,eval_i3_var, pat_bindings_i2_def] >>
         metis_tac [PAIR_EQ, pair_CASES])
     >- decide_tac));

val prog_to_i3_correct = Q.store_thm ("prog_to_i3_correct",
`!ck exh genv s p new_env s' r next' e.
  evaluate_prog_i2 ck exh genv s p (s',new_env,r) ∧
  r ≠ SOME Rtype_error ∧
  FLOOKUP exh (Short "option") = SOME (insert some_tag () (insert none_tag () LN)) ∧
  (prog_to_i3 (none_tag, SOME (TypeId (Short "option"))) (some_tag, SOME (TypeId (Short "option"))) (LENGTH genv) p = (next',e))
  ⇒
  ?r_i3.
    result_to_i3 r r_i3 ∧
    (r = NONE ⇒ LENGTH genv + LENGTH new_env = next') ∧
    evaluate_i3 ck (exh,[]) (s,genv) e ((s',genv++new_env),r_i3)`,
 induct_on `p` >>
 rw [prog_to_i3_def, LET_THM]
 >- (fs [Once evaluate_i3_cases, result_to_i3_cases, Once evaluate_prog_i2_cases] >>
     rw [Once evaluate_i3_cases]) >>
 `?next' e'. prompt_to_i3 (none_tag, SOME (TypeId (Short "option"))) (some_tag, SOME (TypeId (Short "option")))(LENGTH genv) h = (next',e')` by metis_tac [pair_CASES] >>
 fs [] >>
 `?next' e'. prog_to_i3 (none_tag, SOME (TypeId (Short "option"))) (some_tag, SOME (TypeId (Short "option"))) next'' p = (next',e')` by metis_tac [pair_CASES] >>
 fs [] >>
 rw [] >>
 qpat_assum `evaluate_prog_i2 x0 x1 x2 x3 x4 x5` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_prog_i2_cases]) >>
 rw [] >>
 rw [Once evaluate_i3_cases, opt_bind_def]
 >- (`?r_i3.
        result_to_i3 NONE r_i3 ∧
        LENGTH genv + LENGTH env2 = next'' ∧
        evaluate_i3 ck (exh,[]) (s,genv) e' ((s2,genv ++ env2),r_i3)`
             by metis_tac [NOT_SOME_NONE, prompt_to_i3_correct] >>
     res_tac >>
     fs [] >>
     rpt (pop_assum mp_tac) >>
     rw [] >>
     qexists_tac `r_i3'` >>
     srw_tac [ARITH_ss] [eval_match_i3_con] >>
     fs [result_to_i3_cases] >>
     rw []
     >- (qexists_tac `Conv_i2 (none_tag,SOME (TypeId (Short "option"))) []` >>
         rw [pmatch_i2_def] >>
         fs[sptreeTheory.domain_insert] >>
         metis_tac [pair_CASES])
     >- (qexists_tac `Conv_i2 (none_tag,SOME (TypeId (Short "option"))) []` >>
         rw [pmatch_i2_def] >>
         fs[sptreeTheory.domain_insert] >>
         metis_tac [pair_CASES])
     >- (disj1_tac >>
         qexists_tac `Conv_i2 (none_tag,SOME (TypeId (Short "option"))) []` >>
         rw [pmatch_i2_def] >>
         fs[sptreeTheory.domain_insert] >>
         metis_tac [pair_CASES]))
 >- (imp_res_tac prompt_to_i3_correct >>
     fs [] >>
     pop_assum mp_tac >>
     rw [] >>
     qexists_tac `r_i3` >>
     srw_tac [ARITH_ss] [eval_match_i3_con] >>
     fs [result_to_i3_cases] >>
     rw [] >>
     qexists_tac `Conv_i2 (some_tag,SOME (TypeId (Short "option"))) [err']` >>
     fs [none_tag_def, some_tag_def, pmatch_i2_def] >>
     fs[sptreeTheory.domain_insert] >>
     metis_tac [pair_CASES]));

val _ = export_theory ();
