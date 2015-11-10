open preamble decSemTheory;

val _ = new_theory"decProps"

val state_rel_def = Define`
  state_rel R s1 s2 ⇔
    s1.clock = s2.clock ∧
    LIST_REL (sv_rel R) s1.refs s2.refs ∧
    s1.ffi = s2.ffi ∧
    LIST_REL (OPTION_REL R) s1.globals s2.globals`;

val state_rel_refl = store_thm("state_rel_refl[simp]",
  ``∀V s. (∀x. V x x) ⇒ state_rel V s s``,
  rw[state_rel_def] >>
  match_mp_tac EVERY2_refl >>
  rw[optionTheory.OPTREL_def] >>
  Cases_on`x` >> rw[]);

val state_rel_trans = store_thm("csg_rel_trans",
  ``∀V. (∀x y z. V x y ∧ V y z ⇒ V x z) ⇒ ∀x y z. state_rel V x y ∧ state_rel V y z ⇒ state_rel V x z``,
  rw[state_rel_def] >>
  match_mp_tac (MP_CANON EVERY2_trans)
  >- metis_tac[evalPropsTheory.sv_rel_trans] >>
  simp[optionTheory.OPTREL_def] >>
  srw_tac[boolSimps.DNF_ss][] >>
  metis_tac[])

val state_rel_clock = store_thm("state_rel_clock",
  ``state_rel R csg1 csg2 ⇒ csg1.clock = csg2.clock``,
  simp[state_rel_def])

val map_state_def = Define`
  map_state f s =
    <|clock := s.clock;
      ffi := s.ffi;
      refs := MAP (map_sv f) s.refs;
      globals := MAP (OPTION_MAP f) s.globals |>`;

val map_state_clock = Q.store_thm("map_state_clock[simp]",
  `(map_state f s).clock = s.clock`,
  rw[map_state_def]);

val state_every_def = Define`
  state_every P s ⇔ EVERY (sv_every P) s.refs ∧ EVERY (OPTION_EVERY P) s.globals`

val do_app_genv_weakening = prove(
  ``decSem$do_app (x,y) op vs = SOME ((a,b),c) ⇒
    do_app (x,y++z) op vs = SOME ((a,b++z),c)``,
  PairCases_on`x` >> rw[do_app_def] >>
  every_case_tac >> fs[] >> rw[] >>
  fsrw_tac[ARITH_ss][EL_APPEND1,LUPDATE_APPEND1])

(* TODO: could be better if this was exported in decSem, but kept distinct from
         other abbreviations of the same name by including the theory name *)
val _ = temp_type_abbrev("all_env", ``:exh_ctors_env # (varN, conSem$v) alist``);

val evaluate_genv_weakening = Q.store_thm ("evaluate_genv_weakening",
  `(∀ck env (s:('ffi,conSem$v)count_store_genv) e res.
     evaluate ck (env:all_env) s e res ⇒
     !s' s'' genv r genv' l.
       (s = (s',genv)) ∧
       (res = ((s'',genv'),r)) ∧
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate ck env (s',genv++GENLIST (\x.NONE) l) e ((s'',genv'++GENLIST (\x.NONE) l),r)) ∧
   (∀ck env (s:('ffi,conSem$v)count_store_genv) es res.
     evaluate_list ck (env:all_env) s es res ⇒
     !s' s'' genv genv' l r.
       (s = (s',genv)) ∧
       (res = ((s'',genv'),r)) ∧
       r ≠ Rerr (Rabort Rtype_error)
       ⇒
       evaluate_list ck env (s',genv++GENLIST (\x.NONE) l) es ((s'',genv'++GENLIST (\x.NONE) l),r) )∧
   (∀ck env (s:('ffi,conSem$v)count_store_genv) v pes err_v res.
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

val _ = temp_bring_to_front_overload "evaluate" {Name="evaluate",Thy="decSem"}
val _ = temp_bring_to_front_overload "evaluate_list" {Name="evaluate_list",Thy="decSem"}

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
