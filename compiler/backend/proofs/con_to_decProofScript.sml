open preamble
     semanticPrimitivesTheory
     conSemTheory conPropsTheory con_to_decTheory
     decSemTheory decPropsTheory;

val _ = new_theory "con_to_decProof";

(* relations *)

val (result_rel_rules, result_rel_ind, result_rel_cases) = Hol_reln `
  (∀v. result_rel NONE (Rval v)) ∧
  (∀err. result_rel (SOME (Rraise err)) (Rerr (Rraise err))) ∧
  (∀a. result_rel (SOME (Rabort a)) (Rerr (Rabort a)))`;

val (dec_result_rel_rules, dec_result_rel_ind, dec_result_rel_cases) = Hol_reln `
  (dec_result_rel NONE (Rval (Conv (SOME (none_tag, TypeId (Short "option"))) []))) ∧
  (∀err. dec_result_rel (SOME (Rraise err)) (Rval (Conv (SOME (some_tag, TypeId (Short "option"))) [err]))) ∧
  (∀a. dec_result_rel (SOME (Rabort a)) (Rerr (Rabort a)))`;

val compile_state_def = Define`
  compile_state (s:'ffi conSem$state) g =
    <| ffi := s.ffi; refs := s.refs; clock := s.clock; globals := g |>`;

val compile_state_globals = Q.store_thm("compile_state_globals[simp]",
  `(compile_state s g).globals = g`,EVAL_TAC)

val compile_state_with_globals = Q.store_thm("compile_state_with_globals[simp]",
  `compile_state s g with globals updated_by f = compile_state s (f g)`,
  EVAL_TAC)

val compile_state_clock = Q.store_thm("compile_state_clock[simp]",
  `(compile_state s g).clock = s.clock`,EVAL_TAC)

val compile_state_refs = Q.store_thm("compile_state_refs[simp]",
  `(compile_state s g).refs = s.refs`,EVAL_TAC)

val compile_state_dec_clock = Q.store_thm("compile_state_dec_clock[simp]",
  `dec_clock (compile_state s g) = compile_state (dec_clock s) g`,
  EVAL_TAC)

val compile_env_def = Define`
  (compile_env (env:conSem$environment):decSem$environment) =
    <| v := env.v; exh := env.exh |>`;

val compile_env_v = Q.store_thm("compile_env_v[simp]",
  `(compile_env env).v = env.v`, EVAL_TAC)

val compile_env_with_v = Q.store_thm("compile_env_with_v[simp]",
  `compile_env (env with v updated_by x) = compile_env env with v updated_by x`,
  EVAL_TAC)

val compile_env_exh = Q.store_thm("compile_env_exh[simp]",
  `(compile_env env).exh = env.exh`, EVAL_TAC)

(* semantic functions are equivalent *)

val do_app = prove(
  ``∀st op vs res.
      conSem$do_app st op vs = SOME res ⇒
      ∀s. s.refs = FST st ∧ s.ffi = SND st ⇒
        decSem$do_app s op vs = SOME (s with <|refs := FST(FST res); ffi := SND(FST res)|>,SND res)``,
  Cases >> rw[conSemTheory.do_app_def,decSemTheory.do_app_def] >>
  Cases_on`op`>>fs[] >>
  rpt(BasicProvers.CASE_TAC >> fs[LET_THM,store_alloc_def]))

(* compiler correctness *)

val s = mk_var("s",
  ``conSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> ``:'ffi``])

val compile_exp_correct = Q.prove (
  `(∀env ^s es res.
     evaluate env s es = res ⇒
     (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
       evaluate (compile_env env) (compile_state s env.globals) es = (compile_state (FST res) env.globals,SND res)) ∧
   (∀env ^s v pes err_v res.
     evaluate_match env s v pes err_v = res ⇒
     (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
     evaluate_match (compile_env env) (compile_state s env.globals) v pes err_v = (compile_state (FST res) env.globals,SND res))`,
  ho_match_mp_tac conSemTheory.evaluate_ind >>
  rw [decSemTheory.evaluate_def,conSemTheory.evaluate_def] >> rw[] >>
  every_case_tac >> fs[] >>
  imp_res_tac do_app >> rw[] >>
  fsrw_tac[QUANT_INST_ss[record_default_qp]][compile_state_def]);

(*
val init_globals_thm = Q.prove (
  `!new_env genv vs env. LENGTH vs = LENGTH new_env ∧ ALL_DISTINCT vs ⇒
    evaluate_match env (s, genv ++ GENLIST (λt. NONE) (LENGTH new_env)) (Conv NONE new_env)
    [(Pcon NONE (MAP Pvar vs), init_globals vs (LENGTH genv))]
    (Conv (SOME(bind_tag,TypeExn (Short "Bind"))) [])
    ((s,genv ++ MAP SOME new_env), Rval (Conv NONE []))`,
  Induct >- (
    simp[Once decSemTheory.evaluate_cases,pmatch_def,init_globals_def,LENGTH_NIL] >>
    simp[Once decSemTheory.evaluate_cases,pat_bindings_def] >>
    simp[Once decSemTheory.evaluate_cases] >>
    metis_tac [pair_CASES]) >>
  qx_genl_tac[`v`,`genv`,`vs0`,`env`] >> strip_tac >>
  `∃w ws. vs0 = w::ws` by (Cases_on`vs0`>>fs[])>>
  first_x_assum(qspecl_then[`genv++[SOME v]`,`ws`]mp_tac) >>
  fs[] >> strip_tac >>
  simp[Once decSemTheory.evaluate_cases] >> disj1_tac >>
  simp[pmatch_def,pat_bindings_def] >>
  PairCases_on`s`>>fs[] >>
  simp[pmatch_list_Pvar,pats_bindings_MAP_Pvar,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE] >>
  pop_assum mp_tac >>
  simp[Once decSemTheory.evaluate_cases,pat_bindings_def,pmatch_def
      ,pmatch_list_Pvar,pats_bindings_MAP_Pvar,ALL_DISTINCT_REVERSE
      ,GENLIST_CONS,init_globals_def] >> strip_tac >>
  simp[Once decSemTheory.evaluate_cases] >>
  simp[Once decSemTheory.evaluate_cases] >>
  simp[Once decSemTheory.evaluate_cases] >>
  simp[Once decSemTheory.evaluate_cases] >>
  simp[Once decSemTheory.evaluate_cases] >>
  simp[decSemTheory.do_app_def,EL_APPEND1,EL_LENGTH_APPEND,PULL_EXISTS,libTheory.opt_bind_def] >>
  simp[ALOOKUP_APPEND] >>
  reverse BasicProvers.CASE_TAC >- (
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP] >> rfs[MEM_ZIP] >>
    fs[] >> metis_tac[MEM_EL] ) >>
  simp[LUPDATE_APPEND1,combinTheory.o_DEF] >>
  PairCases_on `env` >>
  fs [FORALL_PROD] >>
  metis_tac[CONS_APPEND,APPEND_ASSOC]);

val init_globals_thm = prove(
  ``!new_env.
    evaluate_match ck (exh,[]) (s, genv ++ GENLIST (λt. NONE) (LENGTH new_env)) (Conv NONE new_env)
      [(Pcon NONE (MAP Pvar (GENLIST (λn. STRING #"x" (toString n)) (LENGTH new_env))),
        init_globals (GENLIST (λn. STRING #"x" (toString n)) (LENGTH new_env)) (LENGTH genv))]
     (Conv (SOME(bind_tag,TypeExn (Short "Bind"))) [])
     ((s,genv ++ MAP SOME new_env), Rval (Conv NONE []))``,
  rw[] >> match_mp_tac init_globals_thm >> simp[ALL_DISTINCT_GENLIST])
*)

val init_global_funs_thm = Q.prove (
  `!l genv n.  LENGTH l ≤ n ⇒
    evaluate <|v := []; exh := exh|>
      (compile_state s (genv ++ GENLIST (K NONE) n)) [init_global_funs (LENGTH genv) l]
    = (compile_state s (genv ++ MAP SOME (MAP (λ(f,x,e). Closure [] x e) l) ++ GENLIST (K NONE) (n - LENGTH l)),
       Rval [Conv NONE []])`,
  Induct >> simp[init_global_funs_def] >- (rw[decSemTheory.evaluate_def]) >>
  qx_gen_tac`f` >> PairCases_on`f` >>
  simp[init_global_funs_def] >>
  simp[decSemTheory.evaluate_def] >>
  simp[decSemTheory.do_app_def] >>
  simp[EL_APPEND2,libTheory.opt_bind_def] >>
  Cases_on`n` >> simp[GENLIST_CONS] >> rw[] >>
  first_x_assum(qspec_then`genv++[SOME(Closure [] f1 f2)]`mp_tac) >> simp[] >>
  metis_tac[APPEND_ASSOC,CONS_APPEND]);

(*
val compile_decs_correct = Q.store_thm("compile_decs_correct",
  `!env s ds s' new_env r.
    evaluate_decs env s ds = (s',new_env,r) ∧
    r ≠ SOME (Rabort Rtype_error)
    ⇒
    ?r_i3.
      result_rel r r_i3 ∧
      evaluate <| v := []; exh := env.exh |>
        (compile_state s (env.globals ++ GENLIST (K NONE) (num_defs ds)))
        [compile_decs (LENGTH env.globals) ds]
        =
        (compile_state s' (env.globals ++ MAP SOME new_env ++ GENLIST (K NONE) (num_defs ds - LENGTH new_env)),
         r_i3)`,
  induct_on `ds` >>
  rw [compile_decs_def]
  >- ( fs[decSemTheory.evaluate_def,conSemTheory.evaluate_decs_def,
          result_rel_cases,conLangTheory.num_defs_def] >> rw[]) >>
  fs[conSemTheory.evaluate_decs_def] >>
  fs[conLangTheory.num_defs_def,LET_THM] >>
  reverse(Cases_on`h`)>>
  fs[conSemTheory.evaluate_dec_def] >- (
    every_case_tac >> fs[] >> rw[] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rw[] >>
    fs[conLangTheory.num_defs_def] >>
    rw[decSemTheory.evaluate_def] >>
    simp[init_global_funs_thm] >>
    simp[libTheory.opt_bind_def] ) >>
  reverse every_case_tac >> fs[] >> rw[] >- (
    qcase_tac`Rerr err` >>
    qexists_tac`Rerr err` >>
    rw[result_rel_cases]
    >-(Cases_on`err`>>fs[]) >>
    imp_res_tac compile_exp_correct >> rfs[compile_env_def] >>
    imp_res_tac evaluate_genv_weakening >>
    fs[EQT_ELIM(SIMP_CONV(srw_ss())[K_DEF]``(λx:num. NONE) = K NONE``)] >>
    rw[decSemTheory.evaluate_def] >> rfs[] ) >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  rw[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  imp_res_tac evaluate_genv_weakening >>
  fs[EQT_ELIM(SIMP_CONV(srw_ss())[K_DEF]``(λx:num. NONE) = K NONE``)] >>
  rw[conLangTheory.num_defs_def] >>
  rw[Once ADD_COMM] >> rw[GENLIST_APPEND] >>
  rw[decSemTheory.evaluate_def]

      srw_tac [ARITH_ss] [GENLIST_APPEND] >>
      disj1_tac >>
      MAP_EVERY qexists_tac [`Conv NONE []`, `(s2, genv ++ MAP SOME new_env'' ++ GENLIST (λx. NONE) (num_defs ds))`] >>
      rw [] >>
      fs [LENGTH_APPEND] >>
      MAP_EVERY qexists_tac [`Conv NONE new_env''`, `(s2,genv++GENLIST (λx. NONE) (num_defs ds) ++ GENLIST (λt. NONE) (LENGTH new_env''))`] >>
      rw []
      >- (simp_tac bool_ss [GSYM APPEND_ASSOC, GSYM GENLIST_APPEND] >>
          metis_tac [evaluate_genv_weakening, result_distinct, pair_CASES])
      >- (`!(l:conSem$v option list) x y. l ++ GENLIST (\x.NONE) y ++ GENLIST (\x.NONE) x = l ++ GENLIST (\x.NONE) x ++ GENLIST (\x.NONE) y`
                   by (rw [] >>
                       `!b. (\x. (\y. NONE) (x + b)) = (\y.NONE)` by rw [EXTENSION] >>
                       srw_tac [ARITH_ss] [GSYM GENLIST_APPEND]) >>
          metis_tac [init_globals_thm, evaluate_genv_weakening, result_distinct]))

val compile_prompt_correct = Q.store_thm ("compile_prompt_correct",
  `!ck exh genv s p new_env s' r next' e.
    evaluate_prompt ck (exh:exh_ctors_env) genv s p (s',new_env,r) ∧
    r ≠ SOME (Rabort Rtype_error) ∧
    ((next',e) = compile_prompt (none_tag, TypeId (Short "option")) (some_tag, TypeId (Short "option")) (LENGTH genv) p)
    ⇒
    ?r_i3.
      dec_result_rel r r_i3 ∧
      LENGTH genv + LENGTH new_env = next' ∧
      evaluate ck (exh,[]) (s,genv) e ((s',genv++new_env),r_i3)`,
  rw [evaluate_prompt_cases, compile_prompt_def] >>
  fs [LET_THM, eval_let, evaluate_extend_genv] >>
  rw [eval_con, eval_match_var, pat_bindings_def, libTheory.opt_bind_def, prompt_num_defs_def] >>
  imp_res_tac compile_decs_correct >>
  fs [result_rel_cases, dec_result_rel_cases] >>
  ONCE_REWRITE_TAC [decSemTheory.evaluate_cases] >>
  rw [eval_match_var, eval_let, eval_con]
  >- metis_tac [eval_decs_num_defs]
  >- (rw [Once (hd (tl (CONJUNCTS decSemTheory.evaluate_cases)))] >>
      imp_res_tac eval_decs_num_defs >>
      fs [] >>
      metis_tac [])
  >- (pop_assum mp_tac >>
      rw [] >>
      rw [] >>
      imp_res_tac eval_decs_num_defs_err
      >> TRY decide_tac
      >> (ntac 4 (rw [Once (hd (tl (CONJUNCTS decSemTheory.evaluate_cases)))]) >>
          rw [eval_var, pat_bindings_def] >>
          metis_tac [PAIR_EQ, pair_CASES])));

val compile_prog_correct = Q.store_thm ("compile_prog_correct",
  `!ck exh genv s p new_env s' r next' e.
    evaluate_prog ck exh genv s p (s',new_env,r) ∧
    r ≠ SOME (Rabort Rtype_error) ∧
    FLOOKUP exh (Short "option") = SOME (insert 0 2 (insert 1 2 LN)) ∧
    (compile_prog (none_tag, TypeId (Short "option")) (some_tag, TypeId (Short "option")) (LENGTH genv) p = (next',e))
    ⇒
    ?r_i3.
      dec_result_rel r r_i3 ∧
      (r = NONE ⇒ LENGTH genv + LENGTH new_env = next') ∧
      evaluate ck (exh,[]) (s,genv) e ((s',genv++new_env),r_i3)`,
  induct_on `p` >>
  rw [compile_prog_def, LET_THM]
  >- (fs [Once decSemTheory.evaluate_cases, dec_result_rel_cases, Once evaluate_prog_cases] >>
      rw [Once decSemTheory.evaluate_cases]) >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs [] >>
  `?next' e'. compile_prog (none_tag, TypeId (Short "option")) (some_tag, TypeId (Short "option")) next'' p = (next',e')` by metis_tac [pair_CASES] >>
  fs [] >>
  rw [] >>
  qpat_assum `evaluate_prog x0 x1 x2 x3 x4 x5` (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_prog_cases]) >>
  rw [] >>
  rw [Once decSemTheory.evaluate_cases, libTheory.opt_bind_def]
  >- (
    first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]compile_prompt_correct)) >>
    simp[] >> strip_tac >>
      res_tac >>
      fs [] >>
      rpt (pop_assum mp_tac) >>
      simp[] >>
      rw [] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      conj_tac >- (rw[] >> fs[] >> decide_tac) >>
      `none_tag < 2` by EVAL_TAC >>
      srw_tac [ARITH_ss] [eval_match_con] >>
      fs [dec_result_rel_cases] >>
      rw []
      >- (qexists_tac `Conv (SOME (none_tag,(TypeId (Short "option")))) []` >>
          simp [pmatch_def] >>
          metis_tac [pair_CASES])
      >- (qexists_tac `Conv (SOME (none_tag,TypeId (Short "option"))) []` >>
          simp [pmatch_def] >>
          metis_tac [pair_CASES])
      >- (disj1_tac >>
          qexists_tac `Conv (SOME (none_tag,(TypeId (Short "option")))) []` >>
          simp [pmatch_def] >>
          metis_tac [pair_CASES]))
  >- (imp_res_tac compile_prompt_correct >>
      fs [] >>
      pop_assum mp_tac >>
      rw [] >>
      qexists_tac `r_i3` >>
      srw_tac [ARITH_ss] [eval_match_con] >>
      fs [dec_result_rel_cases] >>
      rw [] >>
      qexists_tac `Conv (SOME(some_tag,(TypeId (Short "option")))) [err']` >>
      simp[PULL_EXISTS] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      disj2_tac >>
      simp[pmatch_def,sptreeTheory.lookup_insert] >>
      PairCases_on`s'`>>simp[] >>
      EVAL_TAC));
*)

val _ = export_theory ();
