open preamble decSemTheory;

val _ = new_theory"decProps"

val csg_rel_def = Define`
  csg_rel R ((c1,s1),g1) (((c2,s2),g2):'a count_store_genv) ⇔
    c1 = c2 ∧ LIST_REL (sv_rel R) (FST s1) (FST s2) ∧ (SND s1 = SND s2) ∧ LIST_REL (OPTION_REL R) g1 g2`

val csg_rel_refl = store_thm("csg_rel_refl",
  ``∀V x. (∀x. V x x) ⇒ csg_rel V x x``,
  rpt gen_tac >> PairCases_on`x` >> simp[csg_rel_def] >>
  rw[] >> match_mp_tac EVERY2_refl >>
  rw[optionTheory.OPTREL_def] >>
  Cases_on`x` >> rw[])
val _ = export_rewrites["csg_rel_refl"]

val csg_rel_trans = store_thm("csg_rel_trans",
  ``∀V. (∀x y z. V x y ∧ V y z ⇒ V x z) ⇒ ∀x y z. csg_rel V x y ∧ csg_rel V y z ⇒ csg_rel V x z``,
  rw[] >> map_every PairCases_on [`x`,`y`,`z`] >>
  fs[csg_rel_def] >>
  conj_tac >>
  match_mp_tac (MP_CANON EVERY2_trans)
  >- metis_tac[evalPropsTheory.sv_rel_trans] >>
  simp[optionTheory.OPTREL_def] >>
  qexists_tac`y3` >> simp[] >>
  Cases >> Cases >> Cases >> simp[] >>
  metis_tac[])

val csg_rel_count = store_thm("csg_rel_count",
  ``csg_rel R csg1 csg2 ⇒ FST(FST csg2) = FST(FST csg1)``,
  PairCases_on`csg1` >>
  PairCases_on`csg2` >>
  simp[csg_rel_def])

val map_csg_def = Define`
  map_csg f (csg:'a count_store_genv) =
    ((FST(FST csg), (MAP (map_sv f) (FST(SND(FST csg))),SND(SND(FST csg)))), MAP (OPTION_MAP f) (SND csg))`

val map_csg_count = Q.store_thm("map_csg_count",
  `FST(FST (map_csg f csg)) = FST(FST csg)`,
  PairCases_on`csg`>>simp[map_csg_def])

val csg_every_def = Define`
  csg_every P (((c,s),g):'a count_store_genv) ⇔ EVERY (sv_every P) (FST s) ∧ EVERY (OPTION_EVERY P) g`

val do_app_genv_weakening = prove(
  ``decSem$do_app (x,y) op vs = SOME ((a,b),c) ⇒
    do_app (x,y++z) op vs = SOME ((a,b++z),c)``,
  PairCases_on`x` >> rw[do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  fsrw_tac[ARITH_ss][EL_APPEND1,LUPDATE_APPEND1])

val evaluate_genv_weakening = Q.store_thm ("evaluate_genv_weakening",
  `(∀ck env s e res.
     evaluate ck (env:all_env) s e res ⇒
     !s' s'' genv r genv' l.
       (s = (s',genv)) ∧
       (res = ((s'',genv'),r)) ∧
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate ck env (s',genv++GENLIST (\x.NONE) l) e ((s'',genv'++GENLIST (\x.NONE) l),r)) ∧
   (∀ck env s es res.
     evaluate_list ck (env:all_env) s es res ⇒
     !s' s'' genv genv' l r.
       (s = (s',genv)) ∧
       (res = ((s'',genv'),r)) ∧
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate_list ck env (s',genv++GENLIST (\x.NONE) l) es ((s'',genv'++GENLIST (\x.NONE) l),r) )∧
   (∀ck env s v pes err_v res.
     evaluate_match ck (env:all_env) s v pes err_v res ⇒
     !s' s'' genv genv' l r.
       (s = (s',genv)) ∧
       (res = ((s'',genv'),r)) ∧
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate_match ck env (s',genv++GENLIST (\x.NONE) l) v pes err_v ((s'',genv'++GENLIST (\x.NONE) l),r))`,
  ho_match_mp_tac evaluate_ind >>
  rw [] >>
  srw_tac [ARITH_ss] [Once evaluate_cases]
  >- metis_tac [pair_CASES]
  >- srw_tac [ARITH_ss] [EL_APPEND1] >>
  srw_tac[ARITH_ss][GSYM GENLIST_APPEND,combinTheory.K_DEF]>>
  metis_tac[pair_CASES,do_app_genv_weakening])

val evaluate_extend_genv = Q.store_thm ("evaluate_extend_genv",
  `!b env s genv n s' genv' v.
    evaluate b env (s,genv) (Extend_global n) (s',r)
    ⇔
    r = Rval (Conv NONE []) ∧
    s' = (s,genv ++ GENLIST (\x. NONE) n)`,
  rw [Once evaluate_cases] >>
  metis_tac []);

val _ = bring_to_front_overload "evaluate" {Name="evaluate",Thy="decSem"}
val _ = bring_to_front_overload "evaluate_list" {Name="evaluate_list",Thy="decSem"}

val eval_var =
SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate b env s (Var_local var) (s',r)``
|> curry save_thm "eval_var";

val eval_con =
SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate b env s (Con tag es) (s',r)``
|> curry save_thm "eval_con";

val eval_mat =
SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate b env s (Mat e pes) (s',r)``
|> curry save_thm "eval_mat";

val eval_fun =
SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate b env s (Fun x e) (s',r)``
|> curry save_thm "eval_fun";

val eval_let =
SIMP_CONV (srw_ss()) [Once evaluate_cases, libTheory.opt_bind_def] ``evaluate b env s (Let NONE e1 e2) (s',r)``
|> curry save_thm "eval_let";

val eval_match_nil =
SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate_match b env s v [] err_v (s',r)``
|> curry save_thm "eval_match_nil";

val pmatch_def = conSemTheory.pmatch_def
val pat_bindings_def = conSemTheory.pat_bindings_def

val eval_match_var =
SIMP_CONV (srw_ss()) [Once evaluate_cases, eval_match_nil, eval_var, pmatch_def, eval_con]
  ``evaluate_match b env s v [(Pvar var, Con n [Var_local var])] err_v (s',r)``
|> curry save_thm "eval_match_var";

val eval_match_var2 =
SIMP_CONV (srw_ss()) [Once evaluate_cases, eval_match_nil, eval_var, pmatch_def, eval_con, pat_bindings_def]
  ``evaluate_match b env s v [(Pvar var, Var_local var)] err_v (s',r)``
|> curry save_thm "eval_match_var2";

val eval_nil =
  SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate_list b env s [] (s',r)``
|> curry save_thm "eval_nil";

val eval_cons =
  SIMP_CONV (srw_ss()) [Once evaluate_cases] ``evaluate_list b env s (e::es) (s',r)``
|> curry save_thm "eval_cons";

val eval_init_global_fun =
SIMP_CONV (srw_ss()) [Once evaluate_cases, eval_fun, do_app_def,
   EXISTS_PROD,eval_cons,eval_nil,PULL_EXISTS,option_case_compute]
  ``evaluate b env s (App (Init_global_var i) [Fun x e]) (s',r)``
|> curry save_thm "eval_init_global_fun";

val eval_match_con =
SIMP_CONV (srw_ss()) [Once evaluate_cases, pmatch_def, pat_bindings_def, eval_match_var2]
  ``evaluate_match b env s v [(Pcon n [], e); (Pvar "x",Var_local "x")] err_v (s',r)``
|> curry save_thm "eval_match_con";

val prompt_num_defs_def = Define `
  prompt_num_defs (Prompt ds) = num_defs ds`;

val eval_decs_num_defs = Q.store_thm("eval_decs_num_defs",
  `!ck exh genv s ds s' env.
    evaluate_decs ck exh genv s ds (s',env,NONE) ⇒ num_defs ds = LENGTH env`,
  induct_on `ds` >>
  rw [conLangTheory.num_defs_def] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once conSemTheory.evaluate_decs_cases]) >>
  rw [] >>
  cases_on `h` >>
  rw [conLangTheory.num_defs_def] >>
  res_tac >>
  rw [] >>
  fs [conSemTheory.evaluate_dec_cases]);

val eval_decs_num_defs_err = Q.store_thm("eval_decs_num_defs_err",
  `!ck exh genv s ds s' env. evaluate_decs ck exh genv s ds (s',env,SOME err) ⇒ LENGTH env <= num_defs ds`,
  induct_on `ds` >>
  rw [conLangTheory.num_defs_def] >>
  pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once conSemTheory.evaluate_decs_cases]) >>
  rw [] >>
  cases_on `h` >>
  rw [conLangTheory.num_defs_def] >>
  res_tac >>
  rw [] >>
  fs [conSemTheory.evaluate_dec_cases]);

val _ = export_theory()
