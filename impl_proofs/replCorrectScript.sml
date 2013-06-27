open preamble boolSimps miscLib rich_listTheory;
open lexer_funTheory repl_funTheory replTheory untypedSafetyTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory
open lexer_implTheory mmlParseTheory inferSoundTheory BigStepTheory ElabTheory compileLabelsTheory compilerProofsTheory;
open TypeSystemTheory typeSoundTheory weakeningTheory typeSysPropsTheory;

val _ = new_theory "replCorrect";

val lex_impl_all_def = tDefine "lex_impl_all" `
lex_impl_all input = 
  case lex_until_toplevel_semicolon input of
    | NONE => []
    | SOME (t,input') => t::lex_impl_all input'`
(wf_rel_tac `measure LENGTH` >>
 rw [] >>
 metis_tac [lex_until_toplevel_semicolon_LESS]);

val lexer_correct = Q.prove (
  `!input. split_top_level_semi (lexer_fun input) = lex_impl_all input`,
  gen_tac
  >> completeInduct_on`LENGTH input` >> rw[]
  >> rw[Once split_top_level_semi_def]
  >> rw[Once lex_impl_all_def]
  >> rw[lex_until_toplevel_semicolon_def]
  >> rw[Once lexer_fun_def]
  >> rw[Once lex_aux_def]
  >> Cases_on`next_token input` >> rw[]
  >- (
    rw[toplevel_semi_dex_def]
    >> cheat (* false! *)
    )
  >> cheat)

val parser_correct = Q.prove (
`!toks. parse_top toks = repl$parse toks`,
  rw[parse_top_def,replTheory.parse_def] >>
  rw[mmlParseREPLTop_thm] >>
  qspec_then`toks`strip_assume_tac mmlPEGTheory.parse_REPLTop_total >>
  simp[destResult_def] >>
  (* this may be impossible to prove, until the grammar is proved unambiguous *)
  (* alternative would be to make parse a relation *)
cheat);

val get_type_error_mask_def = Define `
(get_type_error_mask Terminate = []) ∧
(get_type_error_mask Diverge = [F]) ∧
(get_type_error_mask Diverge = [F]) ∧
(get_type_error_mask (Result r rs) =
  (r = "<type error>")::get_type_error_mask rs)`;

val print_envC_not_type_error = prove(``ls ≠ "<type error>" ⇒ print_envC envc ++ ls ≠ "<type error>"``,
Induct_on`envc`>>
simp[print_envC_def]>>
Cases>>simp[]>>
Induct_on`q`>>simp[SemanticPrimitivesTheory.id_to_string_def]>>
lrw[LIST_EQ_REWRITE])

val print_envE_not_type_error = prove(``print_envE en ≠ "<type error>"``,
Induct_on`en`>>simp[print_envE_def]>>
Cases>>simp[])

val print_result_not_type_error = prove(``r ≠ Rerr Rtype_error ⇒ print_result top envc r ≠ "<type error>"``,
  Cases_on`r`>>
  TRY(Cases_on`e`)>>
  TRY(PairCases_on`a`)>>
  simp[print_result_def]>>
  Cases_on`top`>>simp[print_result_def]>>
  match_mp_tac print_envC_not_type_error >>
  simp[print_envE_not_type_error])

val type_infer_invariants_def = Define `
type_infer_invariants rs rinf_st ⇔
      check_menv (FST rinf_st)
    ∧ check_cenv (FST (SND rinf_st))
    ∧ check_env {} (SND (SND rinf_st))
    ∧ (rs.tenvM = convert_menv (FST rinf_st))
    ∧ (rs.tenvC = FST (SND rinf_st))
    ∧ (rs.tenv = (bind_var_list2 (convert_env2 (SND (SND rinf_st))) Empty))`;

val type_invariants_pres = Q.prove (
`!rs rfs.
  type_infer_invariants rs (infer_menv,infer_cenv,infer_env) ∧
  infer_top infer_menv infer_cenv infer_env top init_infer_state =
          (Success (new_infer_menv,new_infer_cenv,new_infer_env), infer_st2)
  ⇒
  type_infer_invariants (update_repl_state rs el0 el1 (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st'
                                     envC (Rval (envM,envE)))
                  (new_infer_menv ++ infer_menv, new_infer_cenv ++ infer_cenv,new_infer_env ++ infer_env)`,
rw [update_repl_state_def, type_infer_invariants_def] >>
`check_menv new_infer_menv ∧
 check_cenv new_infer_cenv ∧
 check_env {} new_infer_env`
           by metis_tac [infer_top_invariant] >|
[fs [check_menv_def],
 fs [check_cenv_def],
 fs [check_env_def],
 rw [convert_menv_def],
 rw [bvl2_append, convert_env2_def]]);

val type_invariants_pres_err = Q.prove (
`!rs rfs.
  type_infer_invariants rs (infer_menv,infer_cenv,infer_env) ∧
  infer_top infer_menv infer_cenv infer_env top init_infer_state =
          (Success (new_infer_menv,new_infer_cenv,new_infer_env), infer_st2)
  ⇒
  type_infer_invariants (update_repl_state rs el0 el1 (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st'
                                     envC (Rerr err))
                  ((strip_mod_env new_infer_menv) ++ infer_menv, infer_cenv,infer_env)`,
rw [update_repl_state_def, type_infer_invariants_def] >>
`check_menv new_infer_menv ∧
 check_cenv new_infer_cenv ∧
 check_env {} new_infer_env`
           by metis_tac [infer_top_invariant] >>
rw[strip_mod_env_def] >> rw[convert_menv_def] >- (
  fs[check_menv_def,EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  rw[] >> fs[] >> metis_tac[] ) >>
simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY])

val invariant_def = Define`
  invariant rs rfs bs ⇔
    rfs.relaborator_state = (rs.type_bindings, rs.ctors)

    ∧ type_infer_invariants rs rfs.rinferencer_state
    ∧ type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store)

    ∧ closed_context rs.envM rs.envC rs.store rs.envE
    ∧ good_il bs.inst_length
    ∧ (∃rd c. env_rs rs.envM rs.envC rs.envE rfs.rcompiler_state rd (c,rs.store) bs)
    ∧ good_labels rfs.rcompiler_state.rnext_label bs.code

    ∧ bs.clock = NONE
    ∧ (∃ls. bs.code = PrintE::Stop::ls)
    `;

(*
val check_menv_to_tenvM_ok = Q.prove (
`!menv. check_menv menv ⇒ tenvM_ok (convert_menv menv)`,
Induct >>
rw [EVERY_MAP,
    check_menv_def, typeSysPropsTheory.tenvM_ok_def, convert_menv_def] >|
[PairCases_on `h` >>
     fs [] >>
     REPEAT (pop_assum mp_tac) >>
     induct_on `h1` >>
     rw [tenv_ok_def, terminationTheory.bind_var_list2_def] >>
     PairCases_on `h` >>
     fs [terminationTheory.bind_var_list2_def, bind_tenv_def,
         tenv_ok_def, num_tvs_bvl2, num_tvs_def] >>
     metis_tac [check_t_to_check_freevars],
 fs [check_menv_def, tenvM_ok_def] >>
     REPEAT (pop_assum mp_tac) >>
     induct_on `menv` >>
     rw [] >>
     PairCases_on `h` >>
     rw [] >>
     fs [convert_menv_def, EVERY_MAP]]);
     *)

val infer_to_type = Q.prove (
`!rs st bs menv cenv env top new_menv new_cenv new_env st2.
  invariant rs st bs ∧
  (infer_top menv cenv env top init_infer_state =
      (Success (new_menv,new_cenv,new_env),st2)) ∧
  (st.rinferencer_state = (menv,cenv,env))
  ⇒
  type_top rs.tenvM rs.tenvC rs.tenv top
           (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
rw [invariant_def, type_infer_invariants_def, type_sound_invariants_def] >>
fs [] >>
rw [] >>
metis_tac [infer_top_sound]);

val closed_SUBSET = store_thm("closed_SUBSET",
  ``∀v. closed menv v ⇒ ∀menv'. menv_dom menv ⊆ menv_dom menv' ⇒ closed menv' v``,
  ho_match_mp_tac semanticsExtraTheory.closed_ind >>
  simp[] >> rw[] >- fs[EVERY_MEM] >>
  simp[Once semanticsExtraTheory.closed_cases] >>
  fs[EVERY_MEM] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  metis_tac[])

val closed_context_strip_mod_env = store_thm("closed_context_strip_mod_env",
  ``∀menv cenv s env menv'.
    closed_context menv cenv s env ⇒
     closed_context ((strip_mod_env menv')++menv) cenv s env``,
  rw[] >> fs[closed_context_def] >>
  fs[EVERY_MEM] >>
  `menv_dom menv ⊆ menv_dom (strip_mod_env menv' ++ menv)` by (
    srw_tac[DNF_ss][SUBSET_DEF] ) >>
  conj_tac >- metis_tac[closed_SUBSET] >>
  conj_tac >- metis_tac[closed_SUBSET] >>
  conj_tac >- (
    conj_tac >- (
      simp[strip_mod_env_def,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
      simp_tac(srw_ss()++DNF_ss)[] ) >>
    metis_tac[closed_SUBSET] ) >>
  conj_tac >- (
    fs[toIntLangProofsTheory.closed_under_cenv_def] >>
    simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,strip_mod_env_def] >>
    fsrw_tac[DNF_ss][MEM_MAP,SUBSET_DEF,MEM_FLAT] >>
    metis_tac[] ) >>
  conj_tac >- (
    rator_x_assum`closed_under_menv`mp_tac >>
    simp[closed_under_menv_def] >>
    simp[EVERY_MEM] >>
    strip_tac >>
    conj_tac >- metis_tac[closed_SUBSET] >>
    conj_tac >- metis_tac[closed_SUBSET] >>
    conj_tac >- (
      simp[strip_mod_env_def,MEM_MAP,EXISTS_PROD,FORALL_PROD] >>
      simp_tac(srw_ss()++DNF_ss)[] ) >>
    metis_tac[closed_SUBSET] ) >>
  rw[]>>TRY(metis_tac[])>>
  fsrw_tac[DNF_ss][strip_mod_env_def,MEM_FLAT,MEM_MAP,UNCURRY])

val tac =
  rpt gen_tac >> ntac 2 strip_tac >> fs[LibTheory.bind_def] >>
  qpat_assum`P ⇒ Q`mp_tac >>
  discharge_hyps >- (
    rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
  strip_tac >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS]

val MAP_FST_funs = store_thm("MAP_FST_funs",
  ``MAP (λ(x,y,z). x) funs = MAP FST funs``,
  lrw[MAP_EQ_f,FORALL_PROD])

val evaluate_locs = store_thm("evaluate_locs",
  ``(∀ck menv (cenv:envC) cs env e res. evaluate ck menv cenv cs env e res ⇒
       (∀v. v ∈ menv_range menv ∨ MEM v (SND cs) ∨ v ∈ env_range env ⇒ all_locs v ⊆ count (LENGTH (SND cs)))
       ⇒
       LENGTH (SND cs) ≤ LENGTH (SND (FST res)) ∧
       every_result (λv. all_locs v ⊆ count (LENGTH (SND (FST res)))) (SND res) ∧
       (∀v. MEM v (SND (FST res)) ⇒ all_locs v ⊆ count (LENGTH (SND (FST res))))) ∧
    (∀ck menv (cenv:envC) cs env e res. evaluate_list ck menv cenv cs env e res ⇒
       (∀v. v ∈ menv_range menv ∨ MEM v (SND cs) ∨ v ∈ env_range env ⇒ all_locs v ⊆ count (LENGTH (SND cs)))
       ⇒
       LENGTH (SND cs) ≤ LENGTH (SND (FST res)) ∧
       every_result (EVERY (λv. all_locs v ⊆ count (LENGTH (SND (FST res))))) (SND res) ∧
       (∀v. MEM v (SND (FST res)) ⇒ all_locs v ⊆ count (LENGTH (SND (FST res))))) ∧
    (∀ck menv (cenv:envC) cs env w pes res. evaluate_match ck menv cenv cs env w pes res ⇒
       (∀v. v = w ∨ v ∈ menv_range menv ∨ MEM v (SND cs) ∨ v ∈ env_range env ⇒ all_locs v ⊆ count (LENGTH (SND cs)))
       ⇒
       LENGTH (SND cs) ≤ LENGTH (SND (FST res)) ∧
       every_result (λv. all_locs v ⊆ count (LENGTH (SND (FST res)))) (SND res) ∧
       (∀v. MEM v (SND (FST res)) ⇒ all_locs v ⊆ count (LENGTH (SND (FST res)))))``,
  ho_match_mp_tac evaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fs[LibTheory.bind_def] >>
    strip_tac >>
    last_x_assum mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- (
      rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
    strip_tac >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fsrw_tac[ETA_ss,DNF_ss][SUBSET_DEF,EVERY_MEM] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[SemanticPrimitivesTheory.lookup_var_id_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    fsrw_tac[DNF_ss][MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
    metis_tac[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rw[] >>
    cheat ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    cheat ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    cheat ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    cheat ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >>
    cheat ) >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[LibTheory.bind_def,semanticsExtraTheory.build_rec_env_MAP,MAP_FST_funs] >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- (
      rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,UNCURRY] >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
    strip_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- tac >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[LibTheory.bind_def] >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- (
      rw[] >> rw[semanticsExtraTheory.all_locs_def] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      cheat) >>
    strip_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS,arithmeticTheory.LESS_EQ_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[])

val evaluate_dec_closed_context = store_thm("evaluate_dec_closed_context",
  ``∀mn menv cenv s env d s' res. evaluate_dec mn menv cenv s env d (s',res) ∧
    closed_context menv cenv s env ∧
    FV_dec d ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
    dec_cns d ⊆ set (MAP FST cenv)
    ⇒
    let (cenv',env') = case res of Rval(c,e)=>(c++cenv,e++env) | _ => (cenv,env) in
    (* let menv' = case (mn,d) of (SOME mod,Dtype _) => ((mod,[])::menv) | _ => menv in *)
    closed_context menv cenv' s' env'``,
  rpt gen_tac >>
  Cases_on`d`>>simp[Once evaluate_dec_cases]>>
  Cases_on`res`>>simp[]>>strip_tac>>rpt BasicProvers.VAR_EQ_TAC>>simp[LibTheory.emp_def]>>TRY(strip_tac)>>
  TRY (
    fs[closed_context_def] >>
    qmatch_assum_abbrev_tac`evaluate ck menv cenv s0 env e res` >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac(CONJUNCT1 semanticsExtraTheory.evaluate_closed) >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac toIntLangProofsTheory.evaluate_closed_under_cenv >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac (CONJUNCT1 evaluate_locs) >>
    UNABBREV_ALL_TAC >> simp[] >> ntac 3 strip_tac >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    conj_tac >- fs[closed_under_menv_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (
    fs[closed_context_def] >>
    qmatch_assum_abbrev_tac`evaluate ck menv cenv s0 env e res` >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac(CONJUNCT1 semanticsExtraTheory.evaluate_closed) >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac toIntLangProofsTheory.evaluate_closed_under_cenv >>
    qspecl_then[`ck`,`menv`,`cenv`,`s0`,`env`,`e`,`res`]mp_tac (CONJUNCT1 evaluate_locs) >>
    UNABBREV_ALL_TAC >> simp[] >> ntac 3 strip_tac >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    qspecl_then[`cenv`,`s'`,`p`,`v`,`emp`]mp_tac(CONJUNCT1 semanticsExtraTheory.pmatch_closed) >>
    simp[] >> disch_then(qspec_then`menv`mp_tac) >>
    simp[LibTheory.emp_def] >> strip_tac >>
    conj_tac >- (
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      qx_gen_tac`z` >> strip_tac >> TRY(metis_tac[]) >>
      imp_res_tac (CONJUNCT1 semanticsExtraTheory.pmatch_all_cns) >>
      fsrw_tac[DNF_ss][SUBSET_DEF,LibTheory.emp_def] >>
      metis_tac[] ) >>
    conj_tac >- fs[closed_under_menv_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    conj_tac >- metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS] >>
    conj_tac >- cheat >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (
    simp[semanticsExtraTheory.build_rec_env_MAP] >>
    fs[closed_context_def,MAP_FST_funs] >>
    simp[EVERY_MAP,UNCURRY] >>
    conj_tac >- (
      simp[Once semanticsExtraTheory.closed_cases] >>
      simp[EVERY_MEM,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      fs[] >> rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      fs[semanticsExtraTheory.FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
      metis_tac[] ) >>
    conj_tac >- (
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      qx_gen_tac`z` >> strip_tac >> TRY(metis_tac[]) >>
      pop_assum mp_tac >>
      simp[MEM_MAP,EXISTS_PROD] >> strip_tac >>
      simp[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[] ) >>
    conj_tac >- (
      fs[closed_under_menv_def,EVERY_MAP,UNCURRY] >>
      simp[Once semanticsExtraTheory.closed_cases] >>
      fs[EVERY_MEM] >>
      fs[FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
      rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
      fs[semanticsExtraTheory.FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD] >>
      metis_tac[] ) >>
    gen_tac >> strip_tac >> TRY(metis_tac[]) >>
    fs[MEM_MAP,UNCURRY] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP] >>
    metis_tac[] )
  >> (
    simp[SemanticPrimitivesTheory.build_tdefs_def] >>
    Cases_on`mn`>>fs[AstTheory.mk_id_def] >- (
      fs[closed_context_def] >>
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      reverse conj_tac >- metis_tac[] >>
      fs[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] >>
      metis_tac[] ) >>
    fs[closed_context_def] >>
    conj_tac >- (
      fs[toIntLangProofsTheory.closed_under_cenv_def] >>
      simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      fsrw_tac[DNF_ss][MEM_MAP,SUBSET_DEF] >>
      metis_tac[] ) >>
    metis_tac[] ))

val _ = Parse.overload_on("FV_decs",``λds. BIGUNION (IMAGE FV_dec (set ds))``)
val _ = Parse.overload_on("dec_cns_list",``λds. BIGUNION (IMAGE dec_cns (set ds))``)

val evaluate_decs_closed_context = store_thm("evaluate_decs_closed_context",
  ``∀mn menv cenv s env ds res. evaluate_decs mn menv cenv s env ds res ⇒
      closed_context menv cenv s env ∧
      FV_decs ds ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
      dec_cns_list ds ⊆ set (MAP FST cenv)
    ⇒
      let env' = case SND(SND res) of Rval(e)=>(e++env) | _ => env in
      (* let menv' = case mn of SOME mod => if EXISTS (λd. ∃ts. d = Dtype ts) ds then (mod,[])::menv else menv | _ => menv in *)
      closed_context menv ((FST(SND res))++cenv) (FST res) env'``,
  ho_match_mp_tac evaluate_decs_ind >>
  simp[LibTheory.emp_def] >>
  conj_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    imp_res_tac evaluate_dec_closed_context >>
    fs[] >> fs[LET_THM] ) >>
  simp[SemanticPrimitivesTheory.combine_dec_result_def,LibTheory.merge_def] >>
  rpt gen_tac >> rpt strip_tac >>
  qspecl_then[`mn`,`menv`,`cenv`,`s`,`env`,`d`,`s'`,`Rval (new_tds,new_env)`]mp_tac evaluate_dec_closed_context >>
  simp[] >> strip_tac >>
  Cases_on`r`>>fs[]>- (
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  qpat_assum`P ⇒ Q`mp_tac>>
  discharge_hyps>-(
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  strip_tac >>
  fs[closed_context_def] >>
  conj_tac >- (
    fs[toIntLangProofsTheory.closed_under_cenv_def] >>
    metis_tac[] ) >>
  conj_tac >- ( fs[closed_under_menv_def] ) >>
  metis_tac[] )

val closed_context_shift_menv = store_thm("closed_context_shift_menv",
  ``closed_context menv cenv s (env' ++ env) ⇒
    closed_context ((m,env')::menv) cenv s env``,
  strip_tac >>
  fs[closed_context_def] >>
  fs[EVERY_MEM] >>
  `menv_dom menv ⊆ menv_dom ((m,env')::menv)` by rw[SUBSET_DEF] >>
  conj_tac >- metis_tac[closed_SUBSET] >>
  conj_tac >- metis_tac[closed_SUBSET] >>
  conj_tac >- metis_tac[closed_SUBSET] >>
  conj_tac >- (
    fs[toIntLangProofsTheory.closed_under_cenv_def] >>
    metis_tac[] ) >>
  conj_tac >- (
    rator_x_assum`closed_under_menv`mp_tac >>
    simp[closed_under_menv_def] >>
    simp[EVERY_MEM] >>
    metis_tac[closed_SUBSET] ) >>
  metis_tac[])

val evaluate_top_closed_context = store_thm("evaluate_top_closed_context",
  ``∀menv cenv s env top s' cenv' res.
    evaluate_top menv cenv s env top (s',cenv',res) ∧
    closed_context menv cenv s env ∧
    FV_top top ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
    top_cns top ⊆ set (MAP FST cenv)
    ⇒
    let (menv',env') = case res of Rval (m,e) => (m ++ menv,e ++ env) | _ => (menv,env) in
    closed_context menv' (cenv'++cenv) s' env'``,
  rpt gen_tac >>
  Cases_on`top`>>simp[Once evaluate_top_cases]>>
  Cases_on`res`>>simp[]>>strip_tac>>rpt BasicProvers.VAR_EQ_TAC>>simp[LibTheory.emp_def]
  >- (
    imp_res_tac evaluate_decs_closed_context >>
    fs[LET_THM] >>
    metis_tac[closed_context_shift_menv] )
  >- (
    imp_res_tac evaluate_decs_closed_context >>
    fs[LET_THM] )
  >- (
    imp_res_tac evaluate_dec_closed_context >>
    fs[] >> fs[LET_THM] >>
    Cases_on`d`>>fs[] )
  >- (
    imp_res_tac evaluate_dec_closed_context >>
    fs[] >> fs[LET_THM] >>
    Cases_on`d`>>fs[] ))

val strip_mod_env_append = store_thm("strip_mod_env_append",
  ``strip_mod_env (ls ++ l2) = strip_mod_env ls ++ strip_mod_env l2``,
  rw[strip_mod_env_def])
val strip_mod_env_length = store_thm("strip_mod_env_length",
  ``LENGTH (strip_mod_env ls) = LENGTH ls``,
  rw[strip_mod_env_def])

val replCorrect_lem = Q.prove (
`!repl_state error_mask bc_state repl_fun_state.
  invariant repl_state repl_fun_state bc_state ⇒
  ast_repl repl_state
    (get_type_error_mask (main_loop (bc_state,repl_fun_state) input))
    (MAP parse (split_top_level_semi (lexer_fun input)))
    (main_loop (bc_state,repl_fun_state) input)`,

completeInduct_on `LENGTH input` >>
rw [lexer_correct, Once lex_impl_all_def] >>
ONCE_REWRITE_TAC [main_loop_def] >>
cases_on `lex_until_toplevel_semicolon input` >>
rw [get_type_error_mask_def] >-
metis_tac [ast_repl_rules] >>
`?tok input_rest. x = (tok, input_rest)`
        by (cases_on `x` >>
            metis_tac []) >>
rw [] >>
`(parse tok' = NONE) ∨ ∃ast. parse tok' = SOME ast`
        by (cases_on `parse tok'` >>
            metis_tac []) >-
((* A parse error *)
  rw [] >>
  rw [Once ast_repl_cases, parse_elaborate_infertype_compile_def, parser_correct,
      get_type_error_mask_def] >>
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
 metis_tac [lexer_correct]) >>
rw[parse_elaborate_infertype_compile_def,parser_correct] >>
qmatch_assum_rename_tac`elaborate_top st.relaborator_state top0 = (new_elab_state, top)`[] >>
qmatch_assum_rename_tac`invariant rs st bs`[] >>
rw [] >>
`?error_msg next_repl_run_infer_state.
  infertype_top st.rinferencer_state top = Failure error_msg ∨ 
  infertype_top st.rinferencer_state top = Success next_repl_run_infer_state`
         by (cases_on `infertype_top st.rinferencer_state top` >>
             metis_tac []) >>
rw [get_type_error_mask_def] >-
((* A type error *)
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
 rw[Once ast_repl_cases] >>
     metis_tac [lexer_correct]) >>
simp[] >>
`?infer_menv infer_cenv infer_env.
  st.rinferencer_state = (infer_menv,infer_cenv,infer_env)`
            by metis_tac [pair_CASES] >>
fs [infertype_top_def] >>

`?res infer_st2. infer_top infer_menv infer_cenv infer_env top init_infer_state = (res,infer_st2)`
        by metis_tac [pair_CASES] >>
fs [] >>
cases_on `res` >>
fs [] >>
`∃new_infer_menv new_infer_cenv new_infer_env.  a = (new_infer_menv,new_infer_cenv,new_infer_env)`
        by metis_tac [pair_CASES] >>
fs [] >>
BasicProvers.VAR_EQ_TAC >>
imp_res_tac infer_to_type >>
`type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store)`
        by fs [invariant_def] >>
`¬top_diverges rs.envM rs.envC rs.store rs.envE top ⇒
       ∃r envC2 store2.
         r ≠ Rerr Rtype_error ∧
         evaluate_top rs.envM rs.envC rs.store rs.envE top (store2,envC2,r) ∧
         type_sound_invariants
           (update_type_sound_inv
              (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,
               rs.store) (convert_menv new_infer_menv) new_infer_cenv
              (convert_env2 new_infer_env) store2 envC2 r)`
          by metis_tac [top_type_soundness] >>

simp[update_state_def,update_state_err_def] >>

qabbrev_tac`est = st.relaborator_state` >> PairCases_on`est` >>
pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])>>fs[]>>
qabbrev_tac`elab_res = elab_top est0 est1 top0` >> PairCases_on`elab_res` >>
pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])>>fs[]>>
`est0 = rs.type_bindings ∧ est1 = rs.ctors` by fs[invariant_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[elaborate_top_def,LET_THM] >>
qmatch_assum_rename_tac`xxxxxxxx = top`[] >> rpt BasicProvers.VAR_EQ_TAC >>

cases_on `bc_eval (install_code (cpam css) code bs)` >> fs[] >- (
  (* Divergence *)
  rw[Once ast_repl_cases,get_type_error_mask_def] >>
  MAP_EVERY qexists_tac [`convert_menv new_infer_menv`,`new_infer_cenv`,`convert_env2 new_infer_env`] >>
  rw [] >>
  qpat_assum`∀m. X ⇒ Y`kall_tac >>
  spose_not_then strip_assume_tac >> fs[] >>
  imp_res_tac compile_top_thm >>
  pop_assum(qspecl_then[`st.rcompiler_state`]mp_tac) >>
  simp[] >>
  fs[invariant_def] >>
  qmatch_assum_abbrev_tac`bc_eval bs0 = NONE` >>
  map_every qexists_tac[`rd`,`bs0 with clock := SOME ck`,`bs.code`] >>
  conj_tac >- cheat >> (* RK cheat: type system should prove this *)
  conj_tac >- cheat >> (* RK cheat: type system should prove this *)
  conj_tac >- (
    fs[env_rs_def,LET_THM] >>
    rpt HINT_EXISTS_TAC >> simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    simp[Abbr`bs0`,install_code_def]>>
    rfs[] >>
    match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(c,Cs)`,`bs with <|pc := next_addr bs.inst_length bs.code; output := ""; cons_names := cpam css|>`,`bs.refs`,`SOME ck`] >>
    simp[BytecodeTheory.bc_state_component_equality] >>
    conj_tac >- (
      match_mp_tac toBytecodeProofsTheory.Cenv_bs_with_irr >>
      HINT_EXISTS_TAC >> simp[] ) >>
    fs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] ) >>
  conj_tac >- simp[Abbr`bs0`,install_code_def] >>
  conj_tac >- simp[Abbr`bs0`,install_code_def] >>
  simp[] >>
  let
    val tac =
      `∀bs1. bc_next^* bs0 bs1 ⇒ ∃bs2. bc_next bs1 bs2` by (
        rw[] >>
        spose_not_then strip_assume_tac >>
        metis_tac[RTC_bc_next_bc_eval,optionTheory.NOT_SOME_NONE] ) >>
      spose_not_then strip_assume_tac >>
      imp_res_tac RTC_bc_next_can_be_unclocked >>
      fs[] >>
      `bs0 with clock := NONE = bs0` by rw[BytecodeTheory.bc_state_component_equality,Abbr`bs0`,install_code_def] >>
      fs[] >>
      qmatch_assum_rename_tac`bc_next^* bs0 (bs1 with clock := NONE)`[]>>
      `(bs1 with clock := NONE).code = bs0.code` by metis_tac[RTC_bc_next_preserves]
    in
  reverse(Cases_on`r`>>fs[])>-(
    reverse(Cases_on`e`>>fs[])>-(
      metis_tac[bigClockTheory.top_evaluate_not_timeout] ) >>
    tac >>
    `∃ls1. bs1.code = PrintE::Stop::ls1` by (
      rfs[Abbr`bs0`,install_code_def] ) >>
    `bc_fetch bs1 = SOME PrintE` by (
      simp[BytecodeTheory.bc_fetch_def,bytecodeTerminationTheory.bc_fetch_aux_def] ) >>
    `∃bs2. bc_next (bs1 with clock := NONE) bs2 ∧ bc_fetch bs2 = SOME Stop` by (
      simp[bc_eval1_thm] >>
      `(∃n. bv = Number n) ∨ (bv = Block (4 + bind_exc_cn) []) ∨ (bv = Block (4 + div_exc_cn) [])` by (
        qmatch_assum_rename_tac`err_bv xx bv`[] >>
        Cases_on`xx`>>fs[compilerProofsTheory.err_bv_def] ) >>
      simp[Once bc_eval1_def,bc_fetch_with_clock,BytecodeTheory.bump_pc_def] >>
      simp[IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def] >>
      qpat_assum`X = bs0.code`(assume_tac o SYM) >> fs[] >>
      simp[BytecodeTheory.bc_fetch_def,bytecodeTerminationTheory.bc_fetch_aux_def] ) >>
    `bc_next^* bs0 bs2` by metis_tac[RTC_CASES2] >>
    `∃bs3. bc_next bs2 bs3` by metis_tac[] >>
    pop_assum mp_tac >>
    simp[bc_eval1_thm,bc_eval1_def] ) >>
  PairCases_on`a` >> simp[] >>
  tac >>
  `∃bs3. bc_next (bs1 with clock := NONE) bs3` by metis_tac[] >>
  pop_assum mp_tac >>
  `bc_fetch (bs1 with clock := NONE) = NONE` by (
    simp[BytecodeTheory.bc_fetch_def] >>
    match_mp_tac bc_fetch_aux_end_NONE >>
    fs[Abbr`bs0`,install_code_def] ) >>
  simp[bc_eval1_thm,bc_eval1_def]
  end ) >>

`¬top_diverges rs.envM rs.envC rs.store rs.envE top` by (
  qpat_assum`X ⇒ Y`kall_tac >>
  qpat_assum`∀m. X ⇒ Y`kall_tac >>
  spose_not_then strip_assume_tac >>
  `∀r. ¬evaluate_top rs.envM rs.envC rs.store rs.envE top r` by metis_tac[untyped_safety_top] >>
  qmatch_assum_abbrev_tac`bc_eval bs0 = SOME bs1` >> pop_assum kall_tac >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac RTC_bc_next_can_be_clocked >>
  qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`]mp_tac compile_top_divergence >>
  fs[invariant_def] >>
  map_every qexists_tac[`st.rcompiler_state`,`rd`,`ck+1`,`bs.code`,`bs0 with clock := SOME (ck+1)`]>>
  simp[] >>
  conj_tac >- cheat >> (* RK cheat: type system should prove this *)
  conj_tac >- (
    fs[Abbr`bs0`,install_code_def,env_rs_def,LET_THM] >>
    rpt HINT_EXISTS_TAC >> simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    rfs[] >>
    match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(c,Cs)`,`bs with <|pc := next_addr bs.inst_length bs.code; output := ""; cons_names := cpam css|>`,`bs.refs`,`SOME (ck+1)`] >>
    simp[BytecodeTheory.bc_state_component_equality] >>
    conj_tac >- (
      match_mp_tac toBytecodeProofsTheory.Cenv_bs_with_irr >>
      HINT_EXISTS_TAC >> simp[] ) >>
    fs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] ) >>
  conj_tac >- simp[Abbr`bs0`,install_code_def] >>
  conj_tac >- simp[Abbr`bs0`,install_code_def] >>
  qspecl_then[`bs0 with clock := SOME ck`,`bs1 with clock := SOME 0`]mp_tac RTC_bc_next_add_clock >>
  simp[] >>
  disch_then(qspec_then`1`mp_tac) >> strip_tac >>
  qx_gen_tac`bs3` >>
  spose_not_then strip_assume_tac >>
  `∀s3. ¬bc_next (bs1 with clock := SOME 1) s3` by (
    spose_not_then strip_assume_tac >>
    imp_res_tac bc_next_can_be_unclocked >>
    `bs0.clock = NONE` by simp[Abbr`bs0`,install_code_def] >>
    `bs1.clock = NONE` by (
      imp_res_tac RTC_bc_next_clock_less >>
      rfs[optionTheory.OPTREL_def] ) >>
    `bs1 with clock := NONE = bs1` by rw[bc_state_component_equality] >>
    fs[] >> metis_tac[] ) >>
  `∀s3. ¬bc_next bs3 s3` by (
    simp[bc_eval1_thm,bc_eval1_def] ) >>
  qsuff_tac`bs3 = bs1 with clock := SOME 1` >- rw[bc_state_component_equality] >>
  metis_tac[RTC_bc_next_determ]) >>

fs [] >>
`STRLEN input_rest < STRLEN input` by metis_tac[lex_until_toplevel_semicolon_LESS] >>
simp[Once ast_repl_cases,get_type_error_mask_def] >>
disj1_tac >>
MAP_EVERY qexists_tac [`convert_menv new_infer_menv`,
                       `new_infer_cenv`, 
                       `convert_env2 new_infer_env`,
                       `store2`, 
                       `envC2`,
                       `r`] >>
conj_asm2_tac >- metis_tac[print_result_not_type_error] >>
simp[] >>

  qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`(store2,envC2,r)`]mp_tac compile_top_thm >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`ck`mp_tac) >>
  disch_then(qspec_then`st.rcompiler_state`mp_tac) >>
  simp[] >>
  `∃rd c.
    env_rs rs.envM rs.envC rs.envE st.rcompiler_state rd (c,rs.store) bs` by (
    fs[invariant_def,LET_THM] >> metis_tac[] ) >>
  qmatch_assum_abbrev_tac`bc_eval bs0 = SOME bs1` >>
  disch_then(qspecl_then[`rd`,`bs0 with clock := SOME ck`]mp_tac) >>
  `bs0.code = bs.code ++ code` by fs[install_code_def,Abbr`bs0`] >>
  simp[] >>
  discharge_hyps >- (
    fs[invariant_def,LET_THM,Abbr`bs0`,install_code_def] >>
    conj_tac >- cheat >> (* RK cheat: type checker guarantees this? *)
    conj_tac >- cheat >> (* RK cheat: type checker guarantees this? *)
    fs[env_rs_def,LET_THM] >>
    rpt HINT_EXISTS_TAC >> simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    rfs[] >>
    match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(c,Cs')`,`bs with <|pc := next_addr bs.inst_length bs.code; output := ""; cons_names := cpam css|>`,`bs.refs`,`SOME ck`] >>
    simp[BytecodeTheory.bc_state_component_equality] >>
    conj_tac >- (
      match_mp_tac toBytecodeProofsTheory.Cenv_bs_with_irr >>
      HINT_EXISTS_TAC >> simp[] ) >>
    rfs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] ) >>

  Cases_on `r` >> simp[] >- (
    (* successful declaration *)
    PairCases_on`a` >> simp[] >>
    disch_then(qx_choosel_then[`bs2`,`rd2`]strip_assume_tac) >>
    qspecl_then[`bs0 with clock := SOME ck`,`bs2`]mp_tac RTC_bc_next_can_be_unclocked >>
    simp[] >> strip_tac >>
    `bc_fetch bs2 = NONE` by (
      simp[BytecodeTheory.bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      imp_res_tac RTC_bc_next_preserves >>
      fs[Abbr`bs0`,install_code_def] ) >>
    `∀s3. ¬bc_next (bs2 with clock := NONE) s3` by (
      simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock] ) >>
    `bs0 with clock := NONE = bs0` by (
      simp[bc_state_component_equality,Abbr`bs0`,install_code_def] >>
      fs[invariant_def] ) >>
    qspecl_then[`bs0`,`bs2 with clock := NONE`]mp_tac RTC_bc_next_bc_eval >>
    fs[] >> strip_tac >>
    `bs0.output = ""` by fs[Abbr`bs0`,install_code_def] >> simp[] >>
    simp[bc_fetch_with_clock] >>
    first_x_assum(qspec_then`STRLEN input_rest`mp_tac) >>
    simp[] >> disch_then(qspec_then`input_rest`mp_tac) >> simp[] >>
    strip_tac >>
    Q.PAT_ABBREV_TAC`new_bc_state = bs2 with clock := NONE` >>
    Q.PAT_ABBREV_TAC`new_repl_state = update_repl_state X Y Z a b cd de e f` >>
    Q.PAT_ABBREV_TAC`new_repl_fun_state = X:repl_fun_state` >>
    first_x_assum(qspecl_then[`new_repl_state`,`new_bc_state`,`new_repl_fun_state`]mp_tac) >>
    simp[lexer_correct] >>
    disch_then match_mp_tac >>

    (* invariant preservation *)
   `type_infer_invariants new_repl_state (new_infer_menv ++ infer_menv,
                                    new_infer_cenv ++ infer_cenv,
                                    new_infer_env ++ infer_env)`
                        by metis_tac [type_invariants_pres, invariant_def] >>
    fs[invariant_def] >>
    conj_tac >- (
      UNABBREV_ALL_TAC >>
      simp[update_repl_state_def] ) >>
    conj_tac >- (
      fs[type_infer_invariants_def,Abbr`new_repl_fun_state`] ) >>
    conj_tac >- (
      fs[update_type_sound_inv_def,Abbr`new_repl_state`,update_repl_state_def] ) >>
    conj_tac >- (
      qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`store2`,`envC2`,`Rval (a0,a1)`]mp_tac evaluate_top_closed_context >>
      simp[] >>
      simp[Abbr`new_repl_state`,update_repl_state_def] >>
      disch_then (match_mp_tac o MP_CANON) >>
      cheat (* RK cheat: type system should prove this *)) >>
    conj_tac >- (
      imp_res_tac RTC_bc_next_preserves >>
      fs[Abbr`bs0`,install_code_def] ) >>
    conj_tac >- (
      simp[Abbr`new_repl_state`,update_repl_state_def,Abbr`new_bc_state`] >>
      simp[Abbr`new_repl_fun_state`] >>
      qexists_tac`rd2` >>
      qexists_tac`ARB` >>
      fs[env_rs_def,LET_THM] >>
      rpt HINT_EXISTS_TAC >>
      simp[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
      map_every qexists_tac[`rd2`,`(0,Cs'')`,`bs2`,`bs2.refs`,`NONE`] >>
      simp[BytecodeTheory.bc_state_component_equality] >>
      rfs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] ) >>
    conj_tac >- (
      (* good_labels preservation; need compile_top version of compile_append_out? *)
      cheat ) >>
    simp[Abbr`new_bc_state`] >>
    imp_res_tac RTC_bc_next_preserves >>
    fs[]) >>

  reverse(Cases_on`e`>>fs[])>-(
    metis_tac[bigClockTheory.top_evaluate_not_timeout] ) >>

  disch_then(qx_choosel_then[`bv`,`bs2`,`rd2`]strip_assume_tac) >>
  qmatch_assum_rename_tac`err_bv err bv`[] >>
  qmatch_abbrev_tac`X = PR ∧ Y` >>
  `∃bs3. bc_next bs2 bs3 ∧ REVERSE bs3.output = PR ∧ bc_fetch bs3 = SOME Stop` by (
    `∃ls2. bs2.code = PrintE::Stop::ls2` by (
      imp_res_tac RTC_bc_next_preserves >>
      fs[Abbr`bs0`,install_code_def] >>
      fs[invariant_def] ) >>
    `bc_fetch bs2 = SOME PrintE` by (
      simp[BytecodeTheory.bc_fetch_def] ) >>
    simp[print_result_def,Abbr`PR`] >>
    `bs0.output = ""` by fs[Abbr`bs0`,install_code_def] >>
    simp[bc_eval1_thm,bc_eval1_def,BytecodeTheory.bump_pc_def] >>
    Cases_on`err`>>fs[compilerProofsTheory.err_bv_def,print_error_def] >>
    simp[IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def] >>
    simp[BytecodeTheory.bc_fetch_def,bytecodeTerminationTheory.bc_fetch_aux_def] >>
    simp[IMPLODE_EXPLODE_I] ) >>
  `∀s3. ¬bc_next (bs3 with clock := NONE) s3` by (
    simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock] ) >>
  qspecl_then[`bs0 with clock := SOME ck`,`bs3`]mp_tac RTC_bc_next_can_be_unclocked >>
  discharge_hyps >- metis_tac[RTC_CASES2] >>
  strip_tac >>
  `bs0.clock = NONE` by fs[Abbr`bs0`,install_code_def,invariant_def] >>
  `bs0 with clock := NONE = bs0` by simp[bc_state_component_equality] >>
  fs[Abbr`X`,Abbr`PR`,Abbr`Y`] >>
  imp_res_tac RTC_bc_next_bc_eval >>
  fs[] >>
  BasicProvers.VAR_EQ_TAC >>
  simp[] >>
  simp[bc_fetch_with_clock] >>
  first_x_assum(qspec_then`STRLEN input_rest`mp_tac) >>
  simp[] >> disch_then(qspec_then`input_rest`mp_tac) >> simp[] >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`new_bc_state = bs3 with clock := NONE` >>
  Q.PAT_ABBREV_TAC`new_repl_state = update_repl_state X Y Z a b cd de e f` >>
  Q.PAT_ABBREV_TAC`new_repl_fun_state = X:repl_fun_state` >>
  first_x_assum(qspecl_then[`new_repl_state`,`new_bc_state`,`new_repl_fun_state`]mp_tac) >>
  simp[lexer_correct] >>
  disch_then match_mp_tac >>
  (* invariant preservation *)

  pop_assum mp_tac >>
  simp[strip_mod_env_append,strip_mod_env_length,BUTLASTN_APPEND1,BUTLASTN] >>
  strip_tac >>

 `type_infer_invariants new_repl_state (strip_mod_env new_infer_menv ++ infer_menv,
                                  infer_cenv,
                                  infer_env)`
                      by metis_tac [type_invariants_pres_err, invariant_def] >>
  fs[invariant_def] >>
  conj_tac >- (
    UNABBREV_ALL_TAC >>
    simp[update_repl_state_def] ) >>
  conj_tac >- (
    fs[type_infer_invariants_def,Abbr`new_repl_fun_state`] ) >>
  conj_tac >- (
    fs[update_type_sound_inv_def,Abbr`new_repl_state`,update_repl_state_def] ) >>
  conj_tac >- (
    qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`store2`,`envC2`,`Rerr (Rraise err)`]mp_tac evaluate_top_closed_context >>
    simp[] >>
    simp[Abbr`new_repl_state`,update_repl_state_def] >>
    strip_tac >>
    match_mp_tac closed_context_strip_mod_env >>
    pop_assum match_mp_tac >>
    cheat (* RK cheat: type system should prove this *)) >>
  conj_tac >- (
    imp_res_tac RTC_bc_next_preserves >>
    fs[Abbr`bs0`,install_code_def] ) >>
  conj_tac >- (
    simp[Abbr`new_repl_state`,update_repl_state_def,Abbr`new_bc_state`] >>
    simp[Abbr`new_repl_fun_state`] >>
    (* implementation may be broken here? or need to prove that the env_rs we have implies the one with extra module/constructor env stuff *)
    cheat
    (*
    qexists_tac`rd2` >>
    qexists_tac`ARB` >>
    fs[env_rs_def,LET_THM] >>
    rpt HINT_EXISTS_TAC >>
    simp[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd2`,`(0,Cs'')`,`bs2`,`bs2.refs`,`NONE`] >>
    simp[BytecodeTheory.bc_state_component_equality] >>
    rfs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def]
    *)
    ) >>
  conj_tac >- (
    (* good_labels preservation; need compile_top version of compile_append_out? *)
    cheat ) >>
  simp[Abbr`new_bc_state`] >>
  imp_res_tac RTC_bc_next_preserves >>
  fs[])

val FST_compile_fake_exp_contab = store_thm("FST_compile_fake_exp_contab",
  ``FST (compile_fake_exp pr rs vs e) = rs.contab``,
  qabbrev_tac`p = compile_fake_exp pr rs vs e` >>
  PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
  metis_tac[compile_fake_exp_contab])

val good_compile_primitives = prove(
  ``good_contab (FST compile_primitives).contab ∧
    good_cmap [] (cmap (FST compile_primitives).contab) ∧
    {Short ""} = FDOM (cmap (FST compile_primitives).contab) ∧
    (∀id. FLOOKUP (cmap (FST compile_primitives).contab) id = SOME (cmap (FST compile_primitives).contab ' (Short "")) ⇒ id = Short "")
    ``,
  rw[compile_primitives_def] >>
  rw[CompilerTheory.compile_top_def,CompilerTheory.compile_dec_def] >>
  imp_res_tac compile_fake_exp_contab >>
  rw[good_contab_def,intLangExtraTheory.good_cmap_def] >>
  rw[CompilerTheory.init_compiler_state_def,good_contab_def] >>
  rw[IntLangTheory.tuple_cn_def,IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def] >>
  rw[toIntLangProofsTheory.cmap_linv_def,FAPPLY_FUPDATE_THM] >>
  fs[CompilerTheory.compile_top_def,CompilerTheory.compile_dec_def,LET_THM,UNCURRY,FST_compile_fake_exp_contab] >>
  fs[CompilerTheory.init_compiler_state_def,FLOOKUP_UPDATE])

val compile_primitives_menv = store_thm("compile_primitives_menv",
  ``(FST compile_primitives).rmenv = FEMPTY``,
  rw[compile_primitives_def,CompilerTheory.compile_top_def] >>
  rw[CompilerTheory.init_compiler_state_def])

val compile_primitives_renv = store_thm("compile_primitives_renv",
  ``((FST compile_primitives).renv = GENLIST (λi. (FST(EL i init_env), i)) (LENGTH init_env)) ∧
    ((FST compile_primitives).rsz = LENGTH init_env)``,
  rw[compile_primitives_def,CompilerTheory.compile_top_def] >>
  rw[CompilerTheory.init_compiler_state_def] >>
  fs[CompilerTheory.compile_dec_def,LET_THM] >>
  fs[CompilerTheory.compile_fake_exp_def,LET_THM] >>
  rw[CompilerTheory.init_compiler_state_def] >>
  rw[LIST_EQ_REWRITE,SemanticPrimitivesTheory.init_env_def] >>
  `x ∈ count 13` by rw[] >>
  pop_assum mp_tac >> EVAL_TAC >>
  rw[] >> simp[])

val initial_bc_state_invariant = store_thm("initial_bc_state_invariant",
  ``(initial_bc_state.inst_length = K 0) ∧
    good_labels (FST compile_primitives).rnext_label initial_bc_state.code ∧
    (initial_bc_state.clock = NONE) ∧
    (∃ls. initial_bc_state.code = PrintE::Stop::ls)``,
  simp[initial_bc_state_def] >>
  Q.PAT_ABBREV_TAC`bs = install_code X Y Z` >>
  (* cheat: repl setup terminates *)
  `∃bs1. bc_eval bs = SOME bs1` by cheat >>
  simp[] >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_preserves >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_clock_less >>
  `bs1.clock = NONE` by rfs[optionTheory.OPTREL_def,Abbr`bs`,install_code_def] >>
  simp[Abbr`bs`,install_code_def] >>
  (* cheat: compile_top version of compile_append_out *)
  cheat)

val initial_invariant = prove(
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  rw[invariant_def,initial_repl_fun_state_def,initial_elaborator_state_def,init_repl_state_def,LET_THM] >>
  rw[initial_inferencer_state_def,initial_bc_state_invariant]
  >- EVAL_TAC
  >- simp[typeSoundTheory.initial_type_sound_invariant]
  >- (
    simp[closed_context_def] >>
    simp[SemanticPrimitivesTheory.init_env_def,semanticsExtraTheory.closed_cases] >>
    simp[SemanticPrimitivesTheory.init_env_def,toIntLangProofsTheory.closed_under_cenv_def] >>
    simp[SemanticPrimitivesTheory.init_env_def,compilerProofsTheory.closed_under_menv_def] >>
    simp[semanticsExtraTheory.closed_cases] >>
    rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
    simp[SUBSET_DEF] >> metis_tac[] )
  >- ( simp[good_il_def] ) >>

  (* env_rs stuff *)
  simp[env_rs_def,good_compile_primitives,compile_primitives_menv,compile_primitives_renv] >>

  simp[MAP_GENLIST,combinTheory.o_DEF] >>
  Q.PAT_ABBREV_TAC`Cenv = env_to_Cenv FEMPTY X Y` >>

  cheat)

val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
match_mp_tac replCorrect_lem >>
rw[initial_invariant])

val _ = export_theory ();
