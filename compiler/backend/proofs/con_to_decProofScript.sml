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
  (dec_result_rel NONE (Rval [Conv (SOME (none_tag, TypeId (Short "option"))) []])) ∧
  (∀err. dec_result_rel (SOME (Rraise err)) (Rval [Conv (SOME (some_tag, TypeId (Short "option"))) [err]])) ∧
  (∀a. dec_result_rel (SOME (Rabort a)) (Rerr (Rabort a)))`;

val compile_state_def = Define`
  compile_state (s:'ffi conSem$state) =
    (<| ffi := s.ffi; refs := s.refs; clock := s.clock; globals := s.globals |> : 'ffi decSem$state)`;

val compile_state_globals = Q.store_thm("compile_state_globals[simp]",
  `(compile_state s).globals = s.globals`,EVAL_TAC)

val compile_state_with_globals = Q.store_thm("compile_state_with_globals[simp]",
  `compile_state (s with globals updated_by f) = compile_state s with globals updated_by f`,
  EVAL_TAC)

val compile_state_clock = Q.store_thm("compile_state_clock[simp]",
  `(compile_state s).clock = s.clock`,EVAL_TAC)

val compile_state_with_clock = Q.store_thm("compile_state_with_clock[simp]",
  `compile_state (s with clock updated_by f) = compile_state s with clock updated_by f`,
  EVAL_TAC)

val compile_state_refs = Q.store_thm("compile_state_refs[simp]",
  `(compile_state s).refs = s.refs`,EVAL_TAC)

val compile_state_dec_clock = Q.store_thm("compile_state_dec_clock[simp]",
  `dec_clock (compile_state s) = compile_state (dec_clock s)`,
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
       evaluate (compile_env env) (compile_state s) es = (compile_state (FST res),SND res)) ∧
   (∀env ^s v pes err_v res.
     evaluate_match env s v pes err_v = res ⇒
     (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
     evaluate_match (compile_env env) (compile_state s) v pes err_v = (compile_state (FST res),SND res))`,
  ho_match_mp_tac conSemTheory.evaluate_ind >>
  rw [decSemTheory.evaluate_def,conSemTheory.evaluate_def] >> rw[] >>
  every_case_tac >> fs[] >>
  imp_res_tac do_app >> rw[] >>
  fsrw_tac[QUANT_INST_ss[record_default_qp,pair_default_qp]][compile_state_def]);

val init_globals_thm = Q.prove (
  `∀vs env s n genv gs s' extra.
   ALL_DISTINCT vs ∧ (MAP (ALOOKUP env.v) vs = MAP SOME gs) ∧
   s.globals = genv ++ GENLIST (K NONE) (LENGTH gs) ++ extra ∧ n = LENGTH genv ∧
   s' = s with globals := genv ++ MAP SOME gs ++ extra
   ⇒ evaluate env s [init_globals vs n] =
     (s',Rval [Conv NONE []])`,
  Induct >>
  rw[init_globals_def,decSemTheory.evaluate_def] >- rw[state_component_equality] >>
  qpat_assum`_ = MAP SOME _`mp_tac >>
  Cases_on`gs`>>rw[]>>
  rw[decSemTheory.do_app_def,EL_APPEND2,LUPDATE_LENGTH,GENLIST_CONS,EL_APPEND1,LUPDATE_APPEND1]
  >> TRY(fsrw_tac[ARITH_ss][] >> NO_TAC) >>
  first_x_assum match_mp_tac >>
  rw[state_component_equality] >>
  qmatch_assum_rename_tac`_ = SOME g` >>
  qmatch_assum_rename_tac`_ = MAP SOME gs` >>
  map_every qexists_tac[`genv ++ [SOME g]`,`gs`] >>
  simp[] >>
  fs[LIST_EQ_REWRITE,EL_MAP,libTheory.opt_bind_def]);

val init_global_funs_thm = Q.prove (
  `!l genv n.  LENGTH l ≤ n ⇒
    evaluate <|v := []; exh := exh|>
      (compile_state s with globals := genv ++ GENLIST (K NONE) n) [init_global_funs (LENGTH genv) l]
    = (compile_state s with globals := genv ++ MAP SOME (MAP (λ(f,x,e). Closure [] x e) l) ++ GENLIST (K NONE) (n - LENGTH l),
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

val klem = EQT_ELIM(SIMP_CONV(srw_ss())[K_DEF]``(λx:num. NONE) = K NONE``)

val compile_decs_correct = Q.store_thm("compile_decs_correct",
  `!env s ds s' new_env r.
    evaluate_decs env s ds = (s',new_env,r) ∧
    r ≠ SOME (Rabort Rtype_error)
    ⇒
    ?r_i3.
      result_rel r r_i3 ∧
      evaluate <| v := []; exh := env.exh |>
        (compile_state s with globals := s.globals ++ GENLIST (K NONE) (num_defs ds))
        [compile_decs (LENGTH s.globals) ds]
        =
        (compile_state s' with globals := s'.globals ++ GENLIST (K NONE) (num_defs ds - LENGTH new_env),
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
    fs[klem] >>
    rw[decSemTheory.evaluate_def] >> rfs[] ) >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  rw[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  imp_res_tac compile_exp_correct >> fs[] >>
  imp_res_tac evaluate_genv_weakening >> fs[] >>
  first_x_assum(fn th => mp_tac th >> discharge_hyps >- (strip_tac >> fs[result_rel_cases])) >>
  strip_tac >> fs[klem] >>
  fs[compile_env_def] >>
  simp[decSemTheory.evaluate_def] >>
  simp[pat_bindings_def,pats_bindings_MAP_Pvar,ALL_DISTINCT_REVERSE,ALL_DISTINCT_GENLIST] >>
  simp[pmatch_def,pmatch_list_Pvar] >>
  simp[libTheory.opt_bind_def] >>
  (fn g =>
    let
      val SOME (s,_) =
        bvk_find_term (K true) (match_term(lhs(rand(concl(SPEC_ALL init_globals_thm))))) (#2 g)
      val th = CONV_RULE (RESORT_FORALL_CONV (sort_vars (map (#1 o dest_var o #redex) s))) init_globals_thm
    in
      mp_tac(SPECL (map #residue s) th)
    end g) >>
  simp[ALL_DISTINCT_REVERSE,ALL_DISTINCT_GENLIST,MAP_GENLIST,o_DEF] >>
  simp[alookup_distinct_reverse,MAP_REVERSE,ALL_DISTINCT_GENLIST,MAP_ZIP] >>
  imp_res_tac evaluate_globals >>
  disch_then(qspecl_then[`s.globals`]mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["genv"]))) >>
  simp[] >>
  simp[GENLIST_eq_MAP] >>
  qpat_abbrev_tac`f:num->string = _` >> simp[] >>
  qpat_abbrev_tac`ls = ZIP _` >>
  `MAP FST ls = GENLIST f (LENGTH a)` by simp[Abbr`ls`,MAP_ZIP] >>
  `ALL_DISTINCT (MAP FST ls)` by simp[ALL_DISTINCT_GENLIST,Abbr`f`] >>
  `∀m. m < LENGTH a ⇒ ALOOKUP ls (f m) = SOME (SND (EL m ls))`
    by metis_tac[ALOOKUP_ALL_DISTINCT_EL,EL_GENLIST,EL_MAP,LENGTH_MAP,LENGTH_GENLIST] >>
  simp[] >>
  unabbrev_all_tac >> simp[EL_ZIP] >>
  disch_then(qspec_then`a`mp_tac) >>
  simp[conLangTheory.num_defs_def] >>
  ONCE_REWRITE_TAC[ADD_COMM] >>
  simp[GENLIST_APPEND] >>
  fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_COMM,klem]);

val compile_prompt_correct = Q.store_thm ("compile_prompt_correct",
  `!env s p new_env s' r next' e.
    evaluate_prompt env s p = (s',new_env,r) ∧
    r ≠ SOME (Rabort Rtype_error) ∧
    ((next',e) = compile_prompt (none_tag, TypeId (Short "option")) (some_tag, TypeId (Short "option")) (LENGTH s.globals) p)
    ⇒
    ?r_i3.
      dec_result_rel r r_i3 ∧
      LENGTH s.globals + LENGTH new_env = next' ∧
      evaluate <| v := []; exh := env.exh |>
        (compile_state s) [e] =
        (compile_state s' with globals := s.globals ++ new_env,r_i3)`,
  Cases_on`p`>>
  rw [evaluate_prompt_def, compile_prompt_def] >>
  fs [LET_THM, decSemTheory.evaluate_def] >>
  rw[libTheory.opt_bind_def] >>
  rw[pat_bindings_def,pmatch_def] >>
  first_assum(split_pair_case_tac o lhs o concl) >> fs[] >>
  imp_res_tac compile_decs_correct >> pop_assum kall_tac >>
  pop_assum mp_tac >> discharge_hyps >- (strip_tac >> fs[]) >> strip_tac >>
  simp[] >>
  fs[result_rel_cases,dec_result_rel_cases] >> fs[] >>
  imp_res_tac eval_decs_num_defs >>
  imp_res_tac eval_decs_num_defs_err >> fs[] >>
  rpt var_eq_tac >> simp[] >>
  simp[state_component_equality] >>
  imp_res_tac evaluate_decs_globals >> rfs[]);

val compile_prog_evaluate = Q.store_thm ("compile_prog_evaluate",
  `!env s p new_env s' r next' e.
    evaluate_prog env s p = (s',new_env,r) ∧
    r ≠ SOME (Rabort Rtype_error) ∧
    FLOOKUP env.exh (Short "option") = SOME (insert 0 1 (insert 1 1 LN)) ∧
    (compile_prog (none_tag, TypeId (Short "option")) (some_tag, TypeId (Short "option")) (LENGTH s.globals) p = (next',e))
    ⇒
    ?r_i3.
      dec_result_rel r r_i3 ∧
      (r = NONE ⇒ LENGTH s.globals + LENGTH new_env = next') ∧
      evaluate <| v := []; exh := env.exh|> (compile_state s) [e]
      = (compile_state s' with globals := s.globals ++ new_env, r_i3)`,
  induct_on `p` >>
  rw [evaluate_prog_def,compile_prog_def, LET_THM,LENGTH_NIL]
  >- (fs[dec_result_rel_cases,decSemTheory.evaluate_def,state_component_equality]) >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs [] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs [] >>
  rw [] >>
  rw [decSemTheory.evaluate_def] >>
  rw [pat_bindings_def,pmatch_def] >>
  first_assum(split_pair_case_tac o lhs o concl) >> fs [] >>
  first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]compile_prompt_correct)) >>
  simp[] >>
  discharge_hyps >- (strip_tac >> fs[]) >> strip_tac >> simp[] >>
  fs[dec_result_rel_cases,pmatch_def,LET_THM,EVAL``none_tag < 1``] >> fs[] >>
  rpt var_eq_tac >> simp[] >- (
    first_assum(split_pair_case_tac o lhs o concl) >> fs [] >> rw[] >>
    first_x_assum drule >> simp[]) >>
  EVAL_TAC);

val compile_semantics = Q.store_thm("compile_semantics",
  `FLOOKUP env.exh (Short "option") = SOME (insert 0 1 (insert 1 1 LN)) ∧
   semantics env s p ≠ Fail ⇒
   semantics <| v := []; exh := env.exh |> (compile_state s)
     [SND(compile (LENGTH s.globals) p)] =
   semantics env s p`,
  simp[conSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[] >>
    simp[decSemTheory.semantics_def] >>
    IF_CASES_TAC >> fs[] >- (
      rator_x_assum`conSem$evaluate_prog`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      pop_assum mp_tac >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)(pairSyntax.dest_snd tm))`) (#2 g) g) >>
      spose_not_then strip_assume_tac >> fs[] >>
      drule compile_prog_evaluate >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      simp[] >> spose_not_then strip_assume_tac >>
      fs[compile_def] >>
      fs[dec_result_rel_cases] >> rfs[] >>
      rveq >> fs[]) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      rw[] >>
      fs[compile_def] >>
      qmatch_assum_abbrev_tac`conSem$evaluate_prog env ss es = _` >>
      qmatch_assum_abbrev_tac`decSem$evaluate bnv bs be = _` >>
      qispl_then[`env`,`ss`,`es`]mp_tac conPropsTheory.evaluate_prog_add_to_clock_io_events_mono >>
      qispl_then[`bnv`,`bs`,`be`]mp_tac (CONJUNCT1 decPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      simp[Abbr`bs`,Abbr`ss`] >>
      disch_then(qspec_then`k`strip_assume_tac) >>
      disch_then(qspec_then`k'`strip_assume_tac) >>
      Cases_on`s'.ffi.final_event`>>fs[]>-(
        Cases_on`s''.ffi.final_event`>>fs[]>-(
          unabbrev_all_tac >>
          drule compile_prog_evaluate >>
          (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
          simp[] >>
          strip_tac >>
          drule (GEN_ALL (CONJUNCT1 decPropsTheory.evaluate_add_to_clock)) >>
          simp[RIGHT_FORALL_IMP_THM] >>
          discharge_hyps >- (strip_tac >> fs[dec_result_rel_cases]) >>
          disch_then(qspec_then`k'`mp_tac)>>simp[]>>
          rator_x_assum`decSem$evaluate`mp_tac >>
          drule (GEN_ALL (CONJUNCT1 decPropsTheory.evaluate_add_to_clock)) >>
          simp[] >>
          disch_then(qspec_then`k`mp_tac)>>simp[]>>
          ntac 3 strip_tac >> rveq >> fs[] >> rfs[] >>
          fs[state_component_equality,compile_state_def]) >>
        first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> fs[] >>
        qmatch_assum_rename_tac`_ = (_,pp)` >> Cases_on`pp` >>
        unabbrev_all_tac >>
        drule compile_prog_evaluate >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
        discharge_hyps >- (
          last_x_assum(qspec_then`k+k'`mp_tac)>>
          fsrw_tac[ARITH_ss][]) >>
        discharge_hyps >- fs[] >>
        (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
        strip_tac >> fs[] >>
        rator_x_assum`conSem$evaluate_prog`mp_tac >>
        drule (GEN_ALL conPropsTheory.evaluate_prog_add_to_clock) >>
        CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM])) >>
        discharge_hyps >- (strip_tac >> fs[]) >>
        disch_then(qspec_then`k'`mp_tac)>>simp[] >>
        strip_tac >>
        spose_not_then strip_assume_tac >>
        rveq >>
        fsrw_tac[ARITH_ss][compile_state_def,dec_result_rel_cases] >> rfs[] >> fs[]) >>
      first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> fs[] >>
      qmatch_assum_rename_tac`_ = (_,pp)` >> Cases_on`pp` >>
      unabbrev_all_tac >>
      drule compile_prog_evaluate >>
      CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO])) >>
      discharge_hyps >- (
        last_x_assum(qspec_then`k+k'`mp_tac)>>
        fsrw_tac[ARITH_ss][]) >>
      discharge_hyps >- fs[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >> fs[] >> rveq >>
      reverse(Cases_on`s''.ffi.final_event`)>>fs[]>>rfs[]>- (
        fsrw_tac[ARITH_ss][] >> rfs[compile_state_def,dec_result_rel_cases] >> fs[] >> rfs[]) >>
      rator_x_assum`decSem$evaluate`mp_tac >>
      drule (GEN_ALL(CONJUNCT1 decPropsTheory.evaluate_add_to_clock)) >>
      CONV_TAC(LAND_CONV(SIMP_CONV(srw_ss())[RIGHT_FORALL_IMP_THM])) >>
      discharge_hyps >- fs[] >>
      disch_then(qspec_then`k`mp_tac)>>simp[] >>
      rpt strip_tac >> spose_not_then strip_assume_tac >> rveq >>
      fsrw_tac[ARITH_ss][compile_state_def,decSemTheory.state_component_equality] >>
      fs[dec_result_rel_cases] >> rveq >> fs[] >> rfs[]) >>
    drule compile_prog_evaluate >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    last_x_assum(qspec_then`k`strip_assume_tac) >> rfs[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >> fs[] >>
    simp[compile_def] >>
    asm_exists_tac >> simp[] >>
    simp[compile_state_def] >>
    CASE_TAC >> fs[] >>
    spose_not_then strip_assume_tac >>
    fs[dec_result_rel_cases] >>
    Cases_on`a`>>fs[]) >>
  ntac 2 strip_tac >>
  simp[decSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`SND (SND q) ≠ _` >>
    PairCases_on`q`>>fs[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]compile_prog_evaluate)) >>
    simp[] >>
    simp_tac(std_ss++QUANT_INST_ss[pair_default_qp])[] >>
    fs[compile_def] >>
    rw[dec_result_rel_cases]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    pop_assum mp_tac >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)(pairSyntax.dest_snd tm))`) (#2 g) g) >>
    spose_not_then strip_assume_tac >> fs[] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[]>>
    drule compile_prog_evaluate >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >> rfs[] >> rveq >>
    fs[compile_def] >> rveq >> fs[compile_state_def] >>
    CASE_TAC >> fs[] >>
    spose_not_then strip_assume_tac >>
    fs[dec_result_rel_cases]) >>
  rpt strip_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  specl_args_of_then``evaluate_prog``compile_prog_evaluate mp_tac >>
  simp_tac(std_ss++QUANT_INST_ss[pair_default_qp])[] >>
  simp[] >>
  strip_tac >>
  first_x_assum(qspec_then`k`strip_assume_tac) >>
  fs[compile_def] >>
  qmatch_assum_abbrev_tac`dec_result_rel (SND(SND q1)) (SND q2)` >>
  PairCases_on`q1`>>PairCases_on`q2` >>
  fs[markerTheory.Abbrev_def] >>
  ntac 2 (qpat_assum`(_,_) = _`(assume_tac o SYM)) >> fs[] >>
  rpt var_eq_tac >>
  fs[dec_result_rel_cases,compile_state_def]);

val _ = export_theory ();
