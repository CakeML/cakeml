open HolKernel boolLib boolSimps bossLib lcsymtacs preamble miscLib miscTheory arithmeticTheory rich_listTheory
open typeSystemTheory typeSoundTheory typeSoundInvariantsTheory typeSysPropsTheory untypedSafetyTheory
open replTheory printTheory evalPropsTheory free_varsTheory
open inferTheory inferPropsTheory inferSoundTheory
open lexer_implTheory cmlParseTheory pegSoundTheory pegCompleteTheory
open bytecodeTheory bytecodeExtraTheory bytecodeClockTheory bytecodeEvalTheory compilerProofTheory
open initCompEnvTheory repl_funTheory

val _ = new_theory "repl_funProof";

val _ = ParseExtras.temp_tight_equality ();

(* TODO: move *)
val bc_eval_NONE_NRC = store_thm("bc_eval_NONE_NRC",
  ``∀bs. bc_eval bs = NONE ⇒ ∀n. ∃bs'. NRC bc_next n bs bs'``,
  gen_tac >> strip_tac >>
  Induct >> simp[] >>
  simp[NRC_SUC_RECURSE_LEFT] >> fs[] >>
  CONV_TAC SWAP_EXISTS_CONV >>
  qexists_tac`bs'` >> simp[] >>
  spose_not_then strip_assume_tac >>
  `bc_next^* bs bs'` by metis_tac[RTC_eq_NRC] >>
  imp_res_tac RTC_bc_next_bc_eval >> fs[] )

val code_labels_ok_append_local = store_thm("code_labels_ok_append_local",
  ``∀l1 l2. code_labels_ok l1 ∧ code_labels_ok (local_labels l2) ∧
            contains_primitives l1 ⇒
            code_labels_ok (l1 ++ l2)``,
  rw[bytecodeLabelsTheory.code_labels_ok_def,
     bytecodeLabelsTheory.uses_label_thm] >-
  metis_tac[] >>
  fs[local_labels_def,EXISTS_MEM,MEM_FILTER,PULL_EXISTS] >>
  Cases_on`l = VfromListLab` >- (
    fs[bytecodeProofTheory.contains_primitives_def,toBytecodeTheory.VfromListCode_def] ) >>
  `¬inst_uses_label VfromListLab e` by (
    Cases_on`e`>>fs[]>>
    Cases_on`l'`>>fs[]) >>
  metis_tac[])

val code_labels_ok_VfromListCode = store_thm("code_labels_ok_VfromListCode",
  ``code_labels_ok VfromListCode``,
  simp[bytecodeLabelsTheory.code_labels_ok_def,
       bytecodeLabelsTheory.uses_label_thm] >>
  simp[toBytecodeTheory.VfromListCode_def])
(* -- *)

(* TODO: move? *)
val parser_correct = store_thm("parser_correct",
  ``!toks. parse_top toks = repl$parse toks``,
    rw[parse_top_def,replTheory.parse_def] >>
    rw[cmlParseREPLTop_def] >>
    qspec_then`toks`strip_assume_tac cmlPEGTheory.parse_REPLTop_total >>
    simp[destResult_def] >>
    fs[GSYM pegexecTheory.peg_eval_executed, cmlPEGTheory.pnt_def] >>
    `r = NONE \/ ?toks' pts. r = SOME(toks',pts)`
      by metis_tac[optionTheory.option_CASES, pairTheory.pair_CASES] >>
    rw[]
    >- (DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
        qx_gen_tac `pt` >> strip_tac >>
        qspecl_then [`pt`, `nREPLTop`, `toks`, `[]`] mp_tac completeness >>
        simp[] >>
        IMP_RES_THEN mp_tac (pegTheory.peg_deterministic |> CONJUNCT1) >>
        simp[]) >>
    first_assum (strip_assume_tac o MATCH_MP peg_sound) >>
    rw[cmlPtreeConversionTheory.oHD_def] >>
    Cases_on `ptree_REPLTop pt` >> simp[]
    >- (DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
        qx_gen_tac `pt2` >> strip_tac >>
        qspecl_then [`pt2`, `nREPLTop`, `toks`, `[]`] mp_tac completeness >>
        simp[] >> first_x_assum (assume_tac o MATCH_MP (CONJUNCT1 (pegTheory.peg_deterministic))) >>
        simp[]) >>
    DEEP_INTRO_TAC optionTheory.some_intro >> simp[] >>
    reverse conj_tac
    >- (disch_then (qspec_then `pt` mp_tac) >> simp[]) >>
    qx_gen_tac `pt2` >> strip_tac >>
    qspecl_then [`pt2`, `nREPLTop`, `toks`, `[]`] mp_tac completeness >>
    simp[] >> first_x_assum (assume_tac o MATCH_MP (CONJUNCT1 (pegTheory.peg_deterministic))) >>
    simp[]);
(* -- *)

(* type inferencer: invariants *)
val type_infer_invariants_def = Define `
  type_infer_invariants rs (rinf_st : inferencer_state) ⇔
      tenvT_ok (FST (SND rinf_st))
    ∧ check_menv (FST (SND (SND rinf_st)))
    ∧ check_cenv (FST (SND (SND (SND rinf_st))))
    ∧ check_env {} (SND (SND (SND (SND rinf_st))))
    ∧ (rs.tdecs = convert_decls (FST rinf_st))
    ∧ (rs.tenvT = FST (SND rinf_st))
    ∧ (rs.tenvM = convert_menv (FST (SND (SND rinf_st))))
    ∧ (rs.tenvC = FST (SND (SND (SND rinf_st))))
    ∧ (rs.tenv = (bind_var_list2 (convert_env2 (SND (SND (SND (SND rinf_st))))) Empty))`;

val type_invariants_pres = Q.prove (
  `!rs rfs.
    type_infer_invariants rs (decls, infer_tenvT, infer_menv, infer_cenv, infer_env) ∧
    infer_top decls infer_tenvT infer_menv infer_cenv infer_env top init_infer_state =
            (Success (new_decls, new_infer_tenvT, new_infer_menv, new_infer_cenv, new_infer_env), infer_st2)
    ⇒
    type_infer_invariants
         (update_repl_state top rs (convert_decls new_decls)
                                   new_infer_tenvT (convert_menv new_infer_menv) new_infer_cenv
                                   (convert_env2 new_infer_env) st' envC (Rval (envM,envE)))
         (new_decls, merge_tenvT new_infer_tenvT infer_tenvT,
          new_infer_menv ++ infer_menv, merge_tenvC new_infer_cenv infer_cenv,
          new_infer_env ++ infer_env)`,
   simp [update_repl_state_def, type_infer_invariants_def] >>
   gen_tac >>
   strip_tac >>
   `tenvT_ok new_infer_tenvT ∧
    check_menv new_infer_menv ∧
    check_cenv new_infer_cenv ∧
    check_env {} new_infer_env`
              by metis_tac [inferPropsTheory.infer_top_invariant] >>
   rw []
   >- rw [tenvT_ok_merge]
   >- fs [check_menv_def]
   >- (cases_on `new_infer_cenv` >>
       cases_on `rs.tenvC` >>
       fs [merge_tenvC_def, libTheory.merge_def, check_cenv_def, check_flat_cenv_def])
   >- fs [check_env_def]
   >- rw [convert_menv_def]
   >- rw [bvl2_append, convert_env2_def]);

val type_invariants_pres_err = Q.prove (
  `!rs rfs.
    type_infer_invariants rs (decls, infer_tenvT, infer_menv, infer_cenv, infer_env) ∧
    infer_top decls infer_tenvT infer_menv infer_cenv infer_env top init_infer_state =
            (Success (new_decls, new_infer_tenvT, new_infer_menv, new_infer_cenv, new_infer_env), infer_st2)
    ⇒
    type_infer_invariants
         (update_repl_state top rs (convert_decls (append_decls new_decls decls)) 
                                   new_infer_tenvT (convert_menv new_infer_menv) new_infer_cenv 
                                   (convert_env2 new_infer_env) st' envC (Rerr err))
         (append_decls new_decls decls, infer_tenvT, infer_menv, infer_cenv, infer_env)`,
  rw [update_repl_state_def, type_infer_invariants_def] >>
  `check_menv new_infer_menv ∧
   check_cenv new_infer_cenv ∧
   check_env {} new_infer_env`
             by metis_tac [inferPropsTheory.infer_top_invariant] >>
   every_case_tac >>
   rw [] >>
   PairCases_on `decls` >>
   fs [convert_decls_def, convert_menv_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM FST_pair]);
(* -- *)

val repl_invariant_def = Define`
  repl_invariant rs rfs bs ⇔
      SND(SND rs.sem_env.sem_store) = FST rs.tdecs

    ∧ type_infer_invariants rs rfs.rinferencer_state
    ∧ type_sound_invariants (NONE : (v,v) result option)
            (rs.tdecs,rs.tenvT, rs.tenvM, rs.tenvC, rs.tenv,
             FST (SND rs.sem_env.sem_store), rs.sem_env.sem_envM,
             rs.sem_env.sem_envC,rs.sem_env.sem_envE,SND (FST rs.sem_env.sem_store))

    ∧ (∃grd. env_rs (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE) rs.sem_env.sem_store grd rfs.rcompiler_state bs)

    ∧ bs.clock = NONE

    ∧ code_labels_ok bs.code
    ∧ code_executes_ok bs
    `;

(* type errors *)
val get_type_error_mask_def = Define `
  (get_type_error_mask Terminate = []) ∧
  (get_type_error_mask Diverge = [F]) ∧
  (get_type_error_mask Diverge = [F]) ∧
  (get_type_error_mask (Result r rs) =
     (r = "<type error>\n")::get_type_error_mask rs)`;

val print_envC_not_type_error = prove(``ls ≠ "<type error>\n" ⇒ print_envC envc ++ ls ≠ "<type error>\n"``,
  PairCases_on`envc`>>
  simp[print_envC_def]>>
  Induct_on`envc1`>>simp[] >>
  Cases>>simp[]>>
  Induct_on`q`>>simp[id_to_string_def]>>
  lrw[LIST_EQ_REWRITE])

val print_envE_not_type_error = prove(``!types en.
  LENGTH types = LENGTH en ⇒ print_envE types en ≠ "<type error>\n"``,
  ho_match_mp_tac print_envE_ind >>
  simp[print_envE_def])

val print_result_not_type_error = prove(``
  r ≠ Rerr Rtype_error ⇒
  (∀v. r = Rval v ⇒ LENGTH types = LENGTH (SND v)) ⇒
  print_result types top envc r ≠ "<type error>\n"``,
  Cases_on`r`>>
  TRY(Cases_on`e`)>>
  TRY(PairCases_on`a`)>>
  simp[print_result_def]>>
  Cases_on`top`>>simp[print_result_def]>>
  strip_tac >>
  match_mp_tac print_envC_not_type_error >>
  simp[print_envE_not_type_error])
(* -- *)

(* misc: TODO move? *)
val lemma = prove(``∀ls. next_addr len ls = SUM (MAP (λi. if is_Label i then 0 else len i + 1) ls)``,
  Induct >> simp[] >> rw[] >> fs[] >> simp[ADD1] )

val union_append_decls = store_thm("union_append_decls",
  ``union_decls (convert_decls new_decls) (convert_decls decls) = convert_decls (append_decls new_decls decls)``,
   PairCases_on `new_decls` >>
   PairCases_on `decls` >>
   rw [append_decls_def, union_decls_def, convert_decls_def]);

val infer_to_type = Q.prove (
  `!rs st bs decls menv cenv env top new_decls new_menv new_cenv new_env st2.
    repl_invariant rs st bs ∧
    (infer_top decls tenvT menv cenv env top init_infer_state =
        (Success (new_decls,new_tenvT,new_menv,new_cenv,new_env),st2)) ∧
    (st.rinferencer_state = (decls,tenvT,menv,cenv,env))
    ⇒
    infer_sound_invariant (merge_tenvT new_tenvT tenvT) (new_menv ++ menv) (merge_tenvC new_cenv cenv) (new_env++env) ∧
    type_top rs.tdecs rs.tenvT rs.tenvM rs.tenvC rs.tenv top
             (convert_decls new_decls) new_tenvT (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
   rw [repl_invariant_def, type_infer_invariants_def, type_sound_invariants_def] >>
   fs [] >>
   rw [] >>
   metis_tac [infer_top_sound, infer_sound_invariant_def]);
(* -- *)

fun HO_IMP_IMP_tac (g as (_,w)) =
  let
    val (l,r) = dest_imp w
    val (xs,b) = strip_forall l
    val xs' = map (fst o dest_var o variant (free_vars r)) xs
    val l = rhs(concl(RENAME_VARS_CONV xs' l))
    val (xs,b) = strip_forall l
    val (h,c) = dest_imp b
    val new = list_mk_exists(xs,mk_conj(h,mk_imp(c,r)))
  in
    suff_tac new >- metis_tac[]
  end g

val inv_pres_tac =
  imp_res_tac RTC_bc_next_preserves >> fs[] >>
  conj_tac >- (
    qexists_tac`grd'` >>
    match_mp_tac env_rs_change_clock >>
    first_assum(match_exists_tac o concl) >>
    simp[bc_state_component_equality] ) >>
  conj_tac >- (
    simp[install_code_def] >>
    match_mp_tac code_labels_ok_append_local >>
    fs[] >>
    reverse conj_tac >- (PairCases_on`grd`>>fs[env_rs_def])>>
    rator_x_assum`compile_top`mp_tac >>
    specl_args_of_then``compile_top``compile_top_labels mp_tac >>
    match_mp_tac SWAP_IMP >> simp[] >> strip_tac >>
    discharge_hyps >- (
      imp_res_tac type_sound_inv_closed >>
      Cases_on`st.rcompiler_state.globals_env` >>
      fs[global_dom_def,all_env_dom_def] >>
      PairCases_on`grd`>>
      fs[env_rs_def,modLangProofTheory.to_i1_invariant_def] >>
      imp_res_tac global_env_inv_inclusion >>
      fs[SUBSET_DEF] >> rw[] >>
      first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      rw[] >>
      fs[Once modLangProofTheory.v_to_i1_cases] >>
      first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
      rw[] >> rw[] >>
      fs[Once modLangProofTheory.v_to_i1_cases] >>
      qmatch_assum_rename_tac`MEM z (MAP FST e)`[] >>
      first_x_assum(qspec_then`z`mp_tac) >>
      reverse(Cases_on`lookup z e`)>>simp[FLOOKUP_DEF] >- metis_tac[] >>
      imp_res_tac libPropsTheory.lookup_notin ) >>
    rw[] ) >>
  simp[code_executes_ok_def] >>
  disj1_tac >>
  qexists_tac`bs2 with clock := NONE` >>
  simp[bc_fetch_with_clock]

val type_to_string_lem = Q.prove (
  `(!t n. check_t n {} t ⇒ (inf_type_to_string t = type_to_string (convert_t t))) ∧
   (!ts n. EVERY (check_t n {}) ts ⇒
     (MAP inf_type_to_string ts = MAP (type_to_string o convert_t) ts) ∧
     (inf_types_to_string ts = types_to_string (MAP convert_t ts)))`,
   Induct >>
   rw [check_t_def, inf_type_to_string_def, type_to_string_def, convert_t_def] >-
   (cases_on `t` >>
      rw [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
      cases_on `ts` >>
      rw [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
      fs [] >>
      TRY
      (cases_on `t` >>
         fs [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
         cases_on `t'` >>
         fs [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
         metis_tac []) >>
      metis_tac []) >-
   metis_tac [] >-
   metis_tac [] >>
   cases_on `ts` >>
   rw [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
   fs [EVERY_DEF] >>
   metis_tac []);

val type_string_word8 = Q.prove (
  `∀envE tenvE n m envE' tenvE' ctMap tenvS ctMap' tenvS'.
    n < LENGTH tenvE ∧
    (?m. check_t m ∅ (SND (SND (EL n tenvE)))) ∧
    type_env ctMap tenvS envE' tenvE' ∧
    type_env ctMap' tenvS' (envE++envE') (bind_var_list2 (convert_env2 tenvE) tenvE')
    ⇒
    (SND (SND (EL n tenvE)) = Infer_Tapp [] TC_word8 ⇔ ∃w. SND (EL n envE) = Litv (Word8 w))`,
   rw [] >>
   imp_res_tac type_env_length >>
   imp_res_tac type_env_list_rel_append >>
   fs [LIST_REL_EL_EQN, convert_env2_def] >>
   `n < LENGTH envE` by metis_tac [] >>
   res_tac >>
   fs [] >>
   `?x v1. EL n envE = (x,v1)` by metis_tac [pair_CASES] >>
   fs [] >>
   `?x' n' t'. EL n (MAP (λ(x,tvs,t). (x,tvs,convert_t t)) tenvE) = (x',n',t')` by metis_tac [pair_CASES] >>
   fs [] >>
   rw [] >>
   pop_assum mp_tac >>
   rw [EL_MAP] >>
   `?x' n' t'. EL n tenvE = (x',n',t')` by metis_tac [pair_CASES] >>
   fs [] >>
   rw [] >>
   eq_tac >>
   rw [] >>
   fs [convert_t_def] >>
   imp_res_tac (SIMP_RULE (bool_ss) [astTheory.Tword8_def] canonical_values_thm)
   >- metis_tac [] >>
   `convert_t t'' = Tword8` by fs [Once type_v_cases] >>
   cases_on `t''` >>
   fs [convert_t_def, check_t_def]);

val word8_help_tac =
  reverse BasicProvers.CASE_TAC >- (
        fs[update_type_sound_inv_def,type_sound_invariants_def] >>
        Cases_on`e`>>fs[]>>
        fs [Once type_v_cases]) >>
      BasicProvers.CASE_TAC >>
      fs[update_type_sound_inv_def,type_sound_invariants_def] >>
      imp_res_tac type_env_list_rel_append >>
      fs[convert_env2_def] >>
      imp_res_tac type_env_length >> fs[] >>
      pop_assum kall_tac >>
      fs[LIST_REL_EL_EQN] >> rw[] >>
      first_x_assum(qspec_then`n`mp_tac) >>
      simp[EL_MAP,UNCURRY] >> strip_tac >>
      Q.ABBREV_TAC `t = EL n new_infer_env` >>
      `check_t (FST (SND t)) {} (SND (SND t))`
                by (fs [infer_sound_invariant_def, check_env_def] >>
                    `MEM t new_infer_env` by metis_tac [EL_MEM] >>
                    fs [EVERY_MEM] >>
                    res_tac >>
                    PairCases_on `t` >>
                    fs []) >>
      conj_tac >- (
        PairCases_on `t` >>
        fs [] >>
        cases_on `t2` >>
        fs [check_t_def]) >>
      conj_tac >- (
        match_mp_tac (CONJUNCT1 type_to_string_lem) >>
        metis_tac [] ) >>
      metis_tac [convert_env2_def, type_string_word8];

val and_shadow_def = zDefine`and_shadow = $/\`

val repl_correct_lemma = Q.prove (
  `!repl_state bc_state repl_fun_state.
    repl_invariant repl_state repl_fun_state bc_state ⇒
      ast_repl repl_state
        (get_type_error_mask (FST (simple_main_loop (bc_state,repl_fun_state) input)))
        (MAP parse (split_top_level_semi (lexer_fun input)))
        (FST (simple_main_loop (bc_state,repl_fun_state) input))
      ∧ SND (simple_main_loop (bc_state,repl_fun_state) input)`,
  completeInduct_on `LENGTH input` >>
  simp[GSYM and_shadow_def] >>
  rw [lexer_correct, Once lex_impl_all_def] >>
  ONCE_REWRITE_TAC [simple_main_loop_def] >>
  cases_on `lex_until_toplevel_semicolon input` >>
  rw [get_type_error_mask_def] >- (
    rw[Abbr`code_assert`] >> fs[repl_invariant_def] >>
    rw[and_shadow_def,get_type_error_mask_def] >>
    metis_tac [ast_repl_rules] ) >>
  rw[Abbr`code_assert`] >>
  `?tok input_rest. x = (tok, input_rest)`
          by (cases_on `x` >>
              metis_tac []) >>
  rw [] >>
  `(parse tok' = (NONE : top option)) ∨ ∃(ast:top). parse tok' = SOME ast`
          by (cases_on `(parse tok': top option)` >>
              metis_tac []) >-
  ((* A parse error *)
    rw [] >>
    rw [Once ast_repl_cases, parse_infertype_compile_def, parser_correct,
        get_type_error_mask_def] >>
   `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
   rw[and_shadow_def] >>
   TRY (fs[repl_invariant_def] >> NO_TAC) >>
   metis_tac [lexer_correct,FST,SND]) >>
  rw[parse_infertype_compile_def,parser_correct] >>
  qmatch_assum_rename_tac`repl_invariant rs st bs`[] >>
  rw [] >>
  `?error_msg next_repl_run_infer_state types.
    infertype_top st.rinferencer_state ast = Failure error_msg ∨
    infertype_top st.rinferencer_state ast = Success (next_repl_run_infer_state,types)`
           by (cases_on `infertype_top st.rinferencer_state ast` >>
               TRY(Cases_on`a`)>>
               metis_tac []) >>
  rw [get_type_error_mask_def] >-
  ((* A type error *)
    `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
    rw[Once ast_repl_cases] >>
    rw[and_shadow_def] >>
    TRY (fs[repl_invariant_def] >> NO_TAC) >>
    rw[get_type_error_mask_def] >>
    metis_tac [lexer_correct,FST,SND]) >>
  simp[] >>
  `?decls infer_tenvT infer_menv infer_cenv infer_env.
    st.rinferencer_state = (decls,infer_tenvT,infer_menv,infer_cenv,infer_env)`
              by metis_tac [pair_CASES] >>
  fs [infertype_top_def] >>
  `?res infer_st2. infer_top decls infer_tenvT infer_menv infer_cenv infer_env ast init_infer_state = (res,infer_st2)`
          by metis_tac [pair_CASES] >>
  fs [] >>
  cases_on `res` >>
  fs [] >>
  `∃new_decls new_infer_tenvT new_infer_menv new_infer_cenv new_infer_env.  a = (new_decls, new_infer_tenvT, new_infer_menv,new_infer_cenv,new_infer_env)`
          by metis_tac [pair_CASES] >>
  fs [] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac infer_to_type >>
  `type_sound_invariants (NONE:(v,v) result option) (rs.tdecs,rs.tenvT,rs.tenvM,rs.tenvC,rs.tenv,FST (SND rs.sem_env.sem_store),rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE,SND (FST rs.sem_env.sem_store))`
          by fs [repl_invariant_def] >>
  `¬top_diverges (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE)
            (SND (FST rs.sem_env.sem_store),FST (SND rs.sem_env.sem_store),FST rs.tdecs) ast ⇒
         ∀count'.
           ∃r cenv2 store2 decls2'.
             r ≠ Rerr Rtype_error ∧
             evaluate_top F (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE)
               ((count',SND (FST rs.sem_env.sem_store)),FST (SND rs.sem_env.sem_store),
                FST rs.tdecs) ast
               (((count',store2),decls2',
                 FST (convert_decls new_decls) ∪ FST rs.tdecs),cenv2,r) ∧
             type_sound_invariants (SOME r)
               (update_type_sound_inv
                  (rs.tdecs,rs.tenvT,rs.tenvM,rs.tenvC,rs.tenv,FST (SND rs.sem_env.sem_store),
                   rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE,SND (FST rs.sem_env.sem_store))
                  (convert_decls new_decls) new_infer_tenvT (convert_menv new_infer_menv)
                  new_infer_cenv (convert_env2 new_infer_env) store2
                  decls2' cenv2 r)`
            by metis_tac [top_type_soundness] >>
  simp[update_state_def,update_state_err_def] >>

  cases_on `bc_eval (install_code code bs)` >> fs[] >- (
    (* Divergence *)
    rw[Once ast_repl_cases,get_type_error_mask_def] >>
    simp[and_shadow_def] >>
    conj_asm1_tac >- (
      first_assum(match_exists_tac o concl) >> rw[] >>
      qpat_assum`∀m. X ⇒ Y`kall_tac >>
      `∃ck store tdecls. rs.sem_env.sem_store = ((ck,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,repl_invariant_def,SND] >>
      fs[semanticPrimitivesTheory.remove_count_def] >>
      spose_not_then strip_assume_tac >> fs[] >>
      fs[repl_invariant_def] >>
      first_x_assum(qspec_then`ck`strip_assume_tac) >>
      imp_res_tac bigClockTheory.top_evaluate_not_timeout >>
      first_x_assum(mp_tac o MATCH_MP bigClockTheory.top_add_clock) >> simp[] >>
      qx_gen_tac`ck0` >>
      disch_then(mp_tac o MATCH_MP compile_top_thm) >> simp[] >>
      CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(equal``compile_top`` o fst o strip_comb o lhs)))) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[RIGHT_EXISTS_AND_THM,GSYM CONJ_ASSOC] >>
      conj_tac >- ( word8_help_tac ) >>
      conj_tac >- ( fs[closed_top_def] >> metis_tac [type_sound_inv_closed] ) >>
      qmatch_assum_abbrev_tac`bc_eval bs0 = NONE` >>
      map_every qexists_tac[`grd`,`bs0 with clock := SOME ck0`,`bs.code`] >>
      simp[] >>
      conj_tac >- simp[Abbr`bs0`,install_code_def] >>
      conj_tac >- simp[Abbr`bs0`,install_code_def] >>
      conj_tac >- (
        match_mp_tac env_rs_change_clock >>
        CONV_TAC SWAP_EXISTS_CONV >>
        qexists_tac`bs0 with code := bs.code` >>
        simp[bc_state_component_equality] >>
        simp[EXISTS_PROD] >> qexists_tac`ck` >>
        match_mp_tac env_rs_with_bs_irr >>
        first_assum(match_exists_tac o concl) >>
        simp[Abbr`bs0`,install_code_def]) >>
      let
        val tac =
          `∀bs1. bc_next^* bs0 bs1 ⇒ ∃bs2. bc_next bs1 bs2` by (
            rw[] >>
            spose_not_then strip_assume_tac >>
            metis_tac[RTC_bc_next_bc_eval,optionTheory.NOT_SOME_NONE] ) >>
          spose_not_then strip_assume_tac >>
          imp_res_tac RTC_bc_next_can_be_unclocked >>
          fs[] >>
          `bs0 with clock := NONE = bs0` by rw[bytecodeTheory.bc_state_component_equality,Abbr`bs0`,install_code_def] >>
          fs[] >>
          qmatch_assum_rename_tac`bc_next^* bs0 (bs1 with clock := NONE)`[]>>
          `(bs1 with clock := NONE).code = bs0.code` by metis_tac[RTC_bc_next_preserves] >>
          res_tac >> pop_assum mp_tac >>
          simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock]
        in
      reverse(Cases_on`r`>>fs[])>-(
        reverse(Cases_on`e`>>fs[])>> tac) >>
      PairCases_on`a` >> simp[] >> tac
      end ) >>
    fs[] >> fs[] >>
    fs[repl_invariant_def] >>
    simp[code_executes_ok_def] >>
    disj2_tac >>
    qx_gen_tac`n` >>
    `∃ck store tdecls. rs.sem_env.sem_store = ((ck,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,repl_invariant_def,SND] >>
    fs[semanticPrimitivesTheory.remove_count_def] >>
    (untyped_safety_top |> Q.SPECL[`d`,`a,b,c`] |> SPEC_ALL |> EQ_IMP_RULE |> fst |> CONTRAPOS |> SIMP_RULE std_ss []
     |> GEN_ALL |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
    disch_then(qspec_then`n`strip_assume_tac) >>
    (compile_top_divergence |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
     |> (fn th => first_assum(mp_tac o MATCH_MP th))) >>
    HO_IMP_IMP_tac >>
    CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(equal``compile_top`` o fst o strip_comb o lhs)))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    map_every qexists_tac[`grd`,`bs.code`,`install_code code (bs with clock := SOME n)`] >>
    simp[install_code_def] >>
    conj_tac >- (
      reverse conj_tac >- ( fs[closed_top_def] >> metis_tac [type_sound_inv_closed] ) >>
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs with clock := SOME n` >>
      simp[] >>
      match_mp_tac env_rs_change_clock >>
      first_assum(match_exists_tac o concl) >>
      simp[bc_state_component_equality] ) >>
    disch_then(qx_choosel_then[`s2`]strip_assume_tac) >> fs[] >>
    imp_res_tac RTC_bc_next_uses_clock >>
    rfs[] >>
    imp_res_tac NRC_bc_next_can_be_unclocked >> fs[] >>
    qmatch_assum_abbrev_tac`NRC bc_next n bs0 bs1` >>
    Q.PAT_ABBREV_TAC`bs0':bc_state = x y` >>
    `bs0 = bs0'` by (
      simp[Abbr`bs0`,Abbr`bs0'`,bc_state_component_equality] ) >>
    rw[] >> HINT_EXISTS_TAC >> rw[Abbr`bs1`] >>
    imp_res_tac RTC_bc_next_output_IS_PREFIX >>
    rfs[] >> fs[IS_PREFIX_NIL] ) >>

  qpat_assum`¬p ⇒ q`mp_tac >>
  discharge_hyps >- (
    qpat_assum`∀m. X ⇒ Y`kall_tac >>
    spose_not_then (mp_tac o MATCH_MP
      (untyped_safety_top |> SPEC_ALL |> EQ_IMP_RULE |> fst |> CONTRAPOS |> SIMP_RULE std_ss [] |> GEN_ALL)) >>
    simp[] >>
    qmatch_assum_abbrev_tac`bc_eval bs0 = SOME bs1` >> pop_assum kall_tac >>
    imp_res_tac bc_eval_SOME_RTC_bc_next >>
    imp_res_tac RTC_bc_next_can_be_clocked >>
    qexists_tac`ck+1` >>
    spose_not_then
      (compile_top_divergence |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
       |> (fn th => (mp_tac o MATCH_MP th))) >>
    fs[repl_invariant_def] >>
    CONV_TAC(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(equal``compile_top`` o fst o strip_comb o lhs)))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    `∃ck0 store tdecls. rs.sem_env.sem_store = ((ck0,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,SND] >> fs[] >>
    map_every qexists_tac[`grd`,`bs.code`,`bs0 with clock := SOME (ck+1)`]>>
    simp[GSYM CONJ_ASSOC] >>
    conj_tac >- simp[Abbr`bs0`,install_code_def] >>
    conj_tac >- simp[Abbr`bs0`,install_code_def] >>
    conj_tac >- (
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs with clock := SOME (ck+1)` >>
      simp[Abbr`bs0`,install_code_def] >>
      match_mp_tac env_rs_change_clock >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      simp[bc_state_component_equality] ) >>
    conj_tac >- ( fs[closed_top_def] >> metis_tac [type_sound_inv_closed] )>>
    first_x_assum(mp_tac o MATCH_MP RTC_bc_next_add_clock) >>
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
  strip_tac >>

  fs [] >>
  simp[UNCURRY] >>
  `STRLEN input_rest < STRLEN input` by metis_tac[lex_until_toplevel_semicolon_LESS] >>
  simp[Once ast_repl_cases,get_type_error_mask_def] >>
  simp[and_shadow_def] >>

  qmatch_abbrev_tac`(A ∨ B) ∧ C` >>
  qsuff_tac`A ∧ C`>-rw[] >>
  map_every qunabbrev_tac[`A`,`B`,`C`] >>
  simp[GSYM LEFT_EXISTS_AND_THM] >>
  Q.PAT_ABBREV_TAC`pp:repl_result#bool = X` >>

  first_x_assum(qspec_then`FST(FST rs.sem_env.sem_store)`strip_assume_tac) >>
  imp_res_tac bigClockTheory.top_evaluate_not_timeout >>
  first_assum(mp_tac o MATCH_MP bigClockTheory.top_add_clock) >>
  simp[] >>
  disch_then(qx_choose_then`ck`strip_assume_tac) >>
  first_x_assum(mp_tac o MATCH_MP compile_top_thm) >>
  simp[] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(equal``compile_top`` o fst o strip_comb o lhs))))) >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >> simp[] >>
  CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(equal``env_rs`` o fst o strip_comb))))) >>
  rator_x_assum`repl_invariant`mp_tac >>
  simp[repl_invariant_def] >> strip_tac >>
  disch_then(qspecl_then[`grd`,`install_code code bs with clock := SOME ck`,`bs.code`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs with clock := SOME ck` >>
      simp[install_code_def] >>
      match_mp_tac env_rs_change_clock >>
      `∃ck0 store tdecls. rs.sem_env.sem_store = ((ck0,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,SND] >> fs[] >>
      fs[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[bc_state_component_equality] ) >>
    conj_tac >- ( word8_help_tac ) >>
    conj_tac >- ( fs[closed_top_def] >> metis_tac [type_sound_inv_closed] ) >>
    simp[install_code_def] ) >>
  strip_tac >>
  first_assum(split_applied_pair_tac o concl) >> fs[] >>
  qmatch_assum_rename_tac`bc_fetch bs2 = SOME (Stop success)`[] >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  `bc_eval (install_code code bs) = SOME (bs2 with clock := NONE)` by (
    match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >>
    `install_code code bs with clock := NONE = install_code code bs` by (
      fs[install_code_def,bc_state_component_equality] ) >> fs[] >>
    simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock] ) >>
  fs[] >> BasicProvers.VAR_EQ_TAC >> simp[Abbr`pp`,bc_fetch_with_clock] >>
  simp[get_type_error_mask_def] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``evaluate_top`` o fst o strip_comb))) >>
  `∃ck0 store tdecls. rs.sem_env.sem_store = ((ck0,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,SND] >> fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``type_top`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  reverse conj_asm1_tac >- (
    fs [] >>
    match_mp_tac (SIMP_RULE (srw_ss()++boolSimps.DNF_ss) [AND_IMP_INTRO] print_result_not_type_error) >>
    rw [] >>
    fs [convert_env2_def] >>
    PairCases_on `v` >>
    fs [type_sound_invariants_def, update_type_sound_inv_def] >>
    metis_tac [type_env_length, LENGTH_MAP]) >>

  Cases_on `r` >> fs[] >- (
    (* successful declaration *)
    PairCases_on`a` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rpt(qpat_assum`T`kall_tac) >>
    simp[install_code_def] >>
    CONV_TAC(lift_conjunct_conv(equal``code_executes_ok`` o fst o strip_comb)) >>
    conj_tac >- (
      simp[code_executes_ok_def] >> disj1_tac >>
      rfs[install_code_def] >>
      qexists_tac`bs2 with clock := NONE` >>
      simp[bc_fetch_with_clock] >>
      qmatch_abbrev_tac`bc_next^* a b` >>
      qmatch_assum_abbrev_tac`bc_next^* a' b` >>
      `a' = a` by simp[Abbr`a`,Abbr`a'`,bc_state_component_equality] >>
      rw[] ) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    disch_then(qspec_then`input_rest`mp_tac) >> simp[] >>
    simp[lexer_correct] >>
    disch_then(match_mp_tac) >>

    (* invariant preservation *)
    simp[repl_invariant_def,update_repl_state_def] >>
    conj_tac >- metis_tac [pair_CASES, FST, union_decls_def] >>
    conj_tac >-
       ( imp_res_tac type_invariants_pres >>
         fs [update_repl_state_def, type_infer_invariants_def] >>
         metis_tac [union_append_decls] ) >>
    conj_tac >- (fs [update_type_sound_inv_def, type_sound_invariants_def] >> metis_tac []) >>
    inv_pres_tac) >>

  (* exception *)
  reverse(Cases_on`e`>>fs[])>>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[install_code_def] >>
  CONV_TAC(lift_conjunct_conv(equal``code_executes_ok`` o fst o strip_comb)) >>
  conj_tac >- (
    simp[code_executes_ok_def] >> disj1_tac >>
    rfs[install_code_def] >>
    qexists_tac`bs2 with clock := NONE` >>
    simp[bc_fetch_with_clock] >>
    qmatch_abbrev_tac`bc_next^* x b` >>
    qmatch_assum_abbrev_tac`bc_next^* x' b` >>
    `x' = x` by simp[Abbr`x`,Abbr`x'`,bc_state_component_equality] >>
    rw[] ) >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  disch_then(qspec_then`input_rest`mp_tac) >> simp[] >>
  simp[lexer_correct] >>
  disch_then(match_mp_tac) >>

  (* invariant preservation *)
  simp[repl_invariant_def,update_repl_state_def] >>
  conj_tac >- (
    `∃m t e. rs.tdecs = (m,t,e)` by metis_tac[pair_CASES] >>
    simp[] >>
    PairCases_on`new_decls` >>
    simp[convert_menv_def,convert_decls_def,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    fs [union_decls_def] ) >>
  conj_tac >- (
    imp_res_tac type_invariants_pres_err >>
    fs [update_repl_state_def, GSYM union_append_decls, type_infer_invariants_def]) >>
  conj_tac >- (fs [update_type_sound_inv_def, type_sound_invariants_def] >> metis_tac []) >>
  inv_pres_tac);

val _ = delete_const"and_shadow"

val simple_repl_thm = Q.store_thm ("simple_repl_thm",
  `!init_bc_code init_repl_state sem_initial input output b.
    initial_bc_state_side init_bc_code ∧
    repl_invariant sem_initial init_repl_state (THE (bc_eval (install_code init_bc_code initial_bc_state))) ∧
    (simple_repl_fun (init_repl_state,init_bc_code) input = (output,b)) ⇒
    (repl sem_initial (get_type_error_mask output) input output) /\ b`,
   rpt gen_tac >>
   simp [simple_repl_fun_def, repl_def, UNCURRY] >>
   strip_tac >>
   rpt BasicProvers.VAR_EQ_TAC >>
   fs [] >>
   match_mp_tac repl_correct_lemma >>
   rw []);

val unrolled_main_loop_thm = store_thm("unrolled_main_loop_thm",
  ``∀input s bs x y success ss sf s.
    lex_until_toplevel_semicolon input = SOME (x,y) ∧
    (s = if success then ss else sf) ∧
    SND (simple_main_loop (bs,s) input)
    ⇒
    (unrolled_main_loop (INR (x,success,ss,sf)) bs y =
     simple_main_loop (bs,s) input)``,
  strip_tac >> completeInduct_on`LENGTH input`>>rw[]>>
  simp[Once unrolled_main_loop_def] >>
  simp[labelled_repl_step_def] >>
  simp[Once simple_main_loop_def] >>
  Q.PAT_ABBREV_TAC`s = if success then ss else sf` >>
  reverse BasicProvers.CASE_TAC >- (
    BasicProvers.CASE_TAC >- (
      simp[Once simple_main_loop_def] ) >>
    BasicProvers.CASE_TAC >>
    AP_TERM_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[] >>
    conj_tac >- metis_tac[lex_until_toplevel_semicolon_LESS] >>
    qpat_assum`SND Z`mp_tac >>
    simp[Once simple_main_loop_def] >>
    simp[UNCURRY]) >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  Cases_on`bc_eval (install_code q bs)` >> simp[] >>
  qpat_assum`SND Z`mp_tac >>
  simp[Once simple_main_loop_def] >>
  Cases_on`bc_fetch x'`>>simp[] >>
  BasicProvers.CASE_TAC >> simp[] >>
  Q.PAT_ABBREV_TAC`s':repl_fun_state = if b then X else Y` >>
  BasicProvers.CASE_TAC >- (
    simp[UNCURRY] >>
    simp[Once simple_main_loop_def] >>
    simp[Once simple_main_loop_def] ) >>
  BasicProvers.CASE_TAC >>
  strip_tac >>
  AP_TERM_TAC >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  conj_tac >- metis_tac[lex_until_toplevel_semicolon_LESS] >>
  fs[UNCURRY])

val unrolled_repl_thm = store_thm("unrolled_repl_thm",
  ``∀initial input res.
    initial_bc_state_side (SND initial) ⇒
    simple_repl_fun initial input = (res,T) ⇒
    unrolled_repl_fun initial input =
    (Result (THE (bc_eval (install_code (SND initial) initial_bc_state))).output res,T)``,
  rw[unrolled_repl_fun_def,simple_repl_fun_def] >> fs[LET_THM] >>
  rw[Once unrolled_main_loop_def] >>
  rw[labelled_repl_step_def] >>
  Cases_on`initial` >> fs[] >> rw[] >>
  `code_assert` by (
    simp[Abbr`code_assert`] >>
    simp[initial_bc_state_def] >>
    ACCEPT_TAC code_labels_ok_VfromListCode) >>
  fs[Abbr`code_assert`] >>
  fs[initial_bc_state_side_def,LET_THM] >>
  `code_assert'` by (
    simp[Abbr`code_assert'`] >>
    simp[code_executes_ok_def] >>
    metis_tac[bytecodeEvalTheory.bc_eval_SOME_RTC_bc_next] ) >>
  fs[Abbr`code_assert'`] >>
  BasicProvers.CASE_TAC >> fs[] >- (
    fs[Once simple_main_loop_def,LET_THM] ) >>
  BasicProvers.CASE_TAC >> fs[] >>
  simp[UNCURRY] >>
  first_x_assum(
    mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]unrolled_main_loop_thm)) >>
  simp[] >>
  disch_then(qspecl_then[`bs3`,`T`,`q`,`q`]mp_tac) >>
  rfs[UNCURRY])

open bytecodeLabelsTheory

(* TODO: move *)
val code_length_reverse = store_thm("code_length_reverse",
  ``∀l code. code_length l (REVERSE code) = code_length l code``,
  rw[code_length_def,MAP_REVERSE,SUM_REVERSE])

val code_length_append = store_thm("code_length_append",
  ``∀l c1 c2. code_length l (c1 ++ c2) = code_length l c1 + code_length l c2``,
  rw[code_length_def,SUM_APPEND])

val unstrip_labels = prove(
  ``!bs1 bs2. length_ok bs1.inst_length /\
              bc_next (strip_labels bs1) bs2 ==> ?bs3. bc_next bs1 bs3``,
  METIS_TAC [bc_next_strip_IMP]);

val bc_next_strip_labels_NRC = store_thm("bc_next_strip_labels_NRC",
  ``!n s1 s2. length_ok s1.inst_length /\ NRC bc_next n s1 s2 ==>
              NRC bc_next n (strip_labels s1) (strip_labels s2)``,
  Induct >> simp[NRC] >> rw[] >>
  qexists_tac`strip_labels z` >>
  METIS_TAC[bc_next_strip_labels,bc_next_preserves_inst_length])

val unstrip_labels_NRC = store_thm("unstrip_labels_NRC",
  ``!n bs1 bs2. length_ok bs1.inst_length /\
                NRC bc_next n (strip_labels bs1) bs2 ==>
                ?bs3. NRC bc_next n bs1 bs3``,
  Induct >> simp[NRC] >> rw[] >>
  imp_res_tac unstrip_labels >>
  `z = strip_labels bs3` by METIS_TAC[bc_next_strip_labels,bc_eval1_thm,optionTheory.SOME_11] >>
  `length_ok z.inst_length` by METIS_TAC[strip_labels_inst_length,bc_next_preserves_inst_length] >>
  `NRC bc_next n (strip_labels bs3) (strip_labels bs2)` by METIS_TAC[bc_next_strip_labels_NRC,strip_labels_idempot] >>
  METIS_TAC[strip_labels_inst_length] )

val NRC_bc_next_determ = store_thm("NRC_bc_next_determ",
  ``!n s1 s2. NRC bc_next n s1 s2 ==> !s3. NRC bc_next n s1 s3 ==> s3 = s2``,
  Induct>>simp[NRC]>>rw[]>>fs[bc_eval1_thm]>> METIS_TAC[])

val bc_eval_NONE_strip_labels = prove(
  ``(bc_eval bs1 = NONE) /\ code_executes_ok bs1 /\
    length_ok bs1.inst_length ==>
    (bc_eval (strip_labels bs1) = NONE)``,
  rw[] >>
  `!bs2. bc_next^* bs1 bs2 ==> ?bs3. bc_next bs2 bs3` by (
    rw[] >> spose_not_then strip_assume_tac >>
    imp_res_tac RTC_bc_next_bc_eval >>
    fs[] ) >>
  Cases_on`bc_eval (strip_labels bs1)`>>rw[] >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac bc_next_strip_labels_RTC >>
  rfs[strip_labels_inst_length] >>
  `strip_labels (strip_labels bs1) = strip_labels bs1` by METIS_TAC[strip_labels_idempot] >>
  fs[] >>
  `length_ok x.inst_length` by ALL_TAC THEN1
    (IMP_RES_TAC RTC_bc_next_preserves
     \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def]) >>
  qsuff_tac`?bs3. bc_next (strip_labels x) bs3` >- METIS_TAC[unstrip_labels] >>
  `?n. NRC bc_next n (strip_labels bs1) x` by METIS_TAC[RTC_eq_NRC] >>
  `?bs3. NRC bc_next n bs1 bs3` by METIS_TAC[unstrip_labels_NRC] >>
  `NRC bc_next n (strip_labels bs1) (strip_labels bs3)` by METIS_TAC[bc_next_strip_labels_NRC] >>
  `?bs4. bc_next bs3 bs4` by METIS_TAC[RTC_eq_NRC] >>
  `length_ok bs3.inst_length` by METIS_TAC[RTC_bc_next_preserves,RTC_eq_NRC] >>
  qsuff_tac`strip_labels x = strip_labels bs3` >- METIS_TAC[bc_next_strip_labels] >>
  METIS_TAC[NRC_bc_next_determ,strip_labels_idempot])

val bc_eval_SOME_strip_labels = prove(
  ``(bc_eval bs1 = SOME bs2) /\ code_executes_ok bs1 /\
    length_ok bs1.inst_length ==>
    (bc_eval (strip_labels bs1) = SOME (strip_labels bs2))``,
  rw[] >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac bc_next_strip_labels_RTC >>
  imp_res_tac RTC_bc_next_bc_eval >>
  first_x_assum match_mp_tac >>
  `length_ok bs2.inst_length` by ALL_TAC THEN1
    (IMP_RES_TAC RTC_bc_next_preserves
     \\ FULL_SIMP_TAC (srw_ss()) [strip_labels_def]) >>
  METIS_TAC[unstrip_labels]);
(* -- *)

val unlabelled_main_loop_thm = store_thm("unlabelled_main_loop_thm",
  ``∀input bs syms len labs success ss sf.
    labs = collect_labels bs.code 0 bs.inst_length ∧
    len = code_length bs.inst_length bs.code ∧
    bs.inst_length = real_inst_length ∧
    SND (unrolled_main_loop (INR (MAP token_of_sym syms,success,ss,sf)) bs input)
    ⇒
    unlabelled_main_loop (INR (syms,success,(len,labs),ss,sf)) (strip_labels bs) input =
    unrolled_main_loop (INR (MAP token_of_sym syms,success,ss,sf)) bs input``,
  strip_tac >>
  completeInduct_on`LENGTH input` >>
  rw[] >>
  simp[Once unrolled_main_loop_def,labelled_repl_step_def] >>
  simp[Once unlabelled_main_loop_def,unlabelled_repl_step_def] >>
  Q.PAT_ABBREV_TAC`s = if success then ss else sf` >>
  reverse BasicProvers.CASE_TAC >- (
    assume_tac lex_until_top_semicolon_alt_thm >>
    `code_labels_ok bs.code` by (
      fs[Once unrolled_main_loop_def,LET_THM,labelled_repl_step_def] >>
      qpat_assum`SND X`mp_tac >>
      BasicProvers.CASE_TAC >> simp[] >>
      BasicProvers.CASE_TAC >> simp[UNCURRY] ) >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    AP_TERM_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[] >>
    conj_tac >- metis_tac[lex_until_top_semicolon_alt_LESS] >>
    qpat_assum`SND x`mp_tac >>
    simp[Once unrolled_main_loop_def,labelled_repl_step_def,UNCURRY]) >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  simp[install_bc_lists_thm,unlabel_and_encode_def] >>
  Q.PAT_ABBREV_TAC`bs' = install_code X (strip_labels bs)` >>
  `code_labels_ok bs.code` by (
    UNABBREV_ALL_TAC >>
    fs[Once unrolled_main_loop_def,LET_THM,labelled_repl_step_def] >>
    qpat_assum`SND X`mp_tac >>
    BasicProvers.CASE_TAC >> simp[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    simp[UNCURRY]) >>
  `bs' = strip_labels (install_code q bs)` by (
    UNABBREV_ALL_TAC >>
    simp[install_code_def,strip_labels_def,bc_state_component_equality] >>
    reverse conj_tac >- (
      simp[next_addr_thm,code_labels_def] >>
      match_mp_tac code_length_inst_labels >>
      simp[real_inst_length_ok] ) >>
    qspecl_then[`bs.code`,`REVERSE q`,`bs.inst_length`]mp_tac code_labels_APPEND >>
    discharge_hyps >- (
      simp[GSYM code_labels_ok_def]) >>
    simp[] >>
    disch_then SUBST1_TAC >>
    simp[GSYM all_labels_def] >>
    simp[code_labels_def]) >>
  fs[Abbr`bs'`] >> pop_assum kall_tac >>
  Q.PAT_ABBREV_TAC`bs' = install_code q bs` >>
  `length_ok bs'.inst_length` by (
    simp[Abbr`bs'`,install_code_def,real_inst_length_ok] ) >>
  `code_executes_ok bs'` by (
    qpat_assum`SND x`mp_tac >>
    simp[Once unrolled_main_loop_def,labelled_repl_step_def] >>
    Cases_on`bc_eval bs'`>>simp[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    BasicProvers.CASE_TAC >> simp[] >>
    simp[UNCURRY] ) >>
  imp_res_tac code_executes_ok_strip_labels >>
  Cases_on`bc_eval bs'` >> simp[] >- (
    imp_res_tac bc_eval_NONE_strip_labels >> simp[] ) >>
  imp_res_tac bc_eval_SOME_strip_labels >> simp[] >>
  assume_tac lex_until_top_semicolon_alt_thm >>
  BasicProvers.CASE_TAC >> fs[] >- (
    simp[strip_labels_def] ) >>
  BasicProvers.CASE_TAC >> fs[] >>
  `length_ok x.inst_length` by (
    metis_tac[bc_eval_SOME_RTC_bc_next,RTC_bc_next_preserves] ) >>
  simp[bc_fetch_strip_labels] >>
  simp[strip_labels_def] >> simp[GSYM strip_labels_def] >>
  AP_TERM_TAC >>
  first_x_assum(qspec_then`LENGTH r`mp_tac) >>
  discharge_hyps >- metis_tac[lex_until_top_semicolon_alt_LESS] >>
  disch_then(qspec_then`r`mp_tac) >> simp[] >>
  disch_then(qspec_then`x`mp_tac) >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac RTC_bc_next_preserves >>
  simp[Abbr`bs'`,install_code_def] >>
  simp[code_length_append,collect_labels_APPEND] >>
  disch_then match_mp_tac >>
  qpat_assum`SND X`mp_tac >>
  simp[Once unrolled_main_loop_def,labelled_repl_step_def,UNCURRY])

val unlabelled_repl_thm = store_thm("unlabelled_repl_thm",
  ``∀initial input.
      SND (unrolled_repl_fun initial input) ⇒
      (unlabelled_repl_fun initial input =
       unrolled_repl_fun initial input)``,
  rw[unlabelled_repl_fun_def,unrolled_repl_fun_def] >>
  rw[Once unlabelled_main_loop_def] >>
  rw[unlabelled_repl_step_def] >>
  Cases_on`initial`>>rw[unlabel_and_encode_def] >>
  rw[Once unrolled_main_loop_def] >>
  rw[labelled_repl_step_def] >>
  `code_assert` by (
    simp[Abbr`code_assert`,Abbr`code`] >>
    simp[initial_bc_state_def] >>
    ACCEPT_TAC code_labels_ok_VfromListCode) >>
  fs[Abbr`code_assert`] >>
  fs[install_bc_lists_thm] >>
  `bs' = strip_labels bs''` by (
    simp[Abbr`bs'`,Abbr`bs''`] >>
    simp[install_code_def,strip_labels_def,bc_state_component_equality] >>
    reverse conj_tac >- (
      simp[next_addr_thm,code_labels_def] >>
      match_mp_tac code_length_inst_labels >>
      simp[initial_bc_state_def,empty_bc_state_def,real_inst_length_ok] ) >>
    `initial_bc_state.inst_length = real_inst_length` by (
      simp[initial_bc_state_def,empty_bc_state_def] ) >>
    qspecl_then[`code`,`code'`,`real_inst_length`]mp_tac code_labels_APPEND >>
    discharge_hyps >- (
      simp[Abbr`code`,initial_bc_state_def] >>
      simp[GSYM code_labels_ok_def] >>
      ACCEPT_TAC code_labels_ok_VfromListCode ) >>
    simp[] >>
    disch_then SUBST1_TAC >>
    UNABBREV_ALL_TAC >>
    simp[GSYM all_labels_def] >>
    simp[code_labels_def]) >>
  fs[Abbr`bs'`] >>
  `length_ok bs''.inst_length` by (
    simp[Abbr`bs''`,install_code_def,initial_bc_state_def,
         empty_bc_state_def,real_inst_length_ok] ) >>
  `code_executes_ok bs''` by (
    fs[Once unrolled_main_loop_def,labelled_repl_step_def,LET_THM] >>
    last_x_assum mp_tac >>
    Cases_on`bc_eval bs''`>>simp[]>>
    BasicProvers.CASE_TAC >>simp[]>>
    BasicProvers.CASE_TAC >>simp[]>>
    simp[UNCURRY] ) >>
  `code_assert''` by rfs[] >>
  fs[Abbr`code_assert''`] >>
  `code_assert'` by (
    UNABBREV_ALL_TAC >>
    simp[code_executes_ok_strip_labels] ) >>
  fs[Abbr`code_assert'`] >>
  Cases_on`bc_eval bs''` >> simp[] >- (
    imp_res_tac bc_eval_NONE_strip_labels >> simp[] ) >>
  imp_res_tac bc_eval_SOME_strip_labels >> simp[] >>
  assume_tac lex_until_top_semicolon_alt_thm >>
  BasicProvers.CASE_TAC >> fs[] >- (
    simp[strip_labels_def] ) >>
  BasicProvers.CASE_TAC >> fs[] >>
  `length_ok x.inst_length` by (
    metis_tac[bc_eval_SOME_RTC_bc_next,RTC_bc_next_preserves] ) >>
  simp[bc_fetch_strip_labels] >>
  simp[strip_labels_def] >> simp[GSYM strip_labels_def] >>
  AP_TERM_TAC >>
  match_mp_tac unlabelled_main_loop_thm >>
  UNABBREV_ALL_TAC >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac RTC_bc_next_preserves >>
  simp[install_code_def] >>
  `initial_bc_state.inst_length = real_inst_length` by (
      simp[initial_bc_state_def,empty_bc_state_def] ) >>
  simp[collect_labels_APPEND,code_length_append] >>
  qpat_assum`SND X`mp_tac >>
  simp[Once unrolled_main_loop_def,labelled_repl_step_def,UNCURRY])

val convert_invariants = Q.prove (
`!se e bs.
   initCompEnv$invariant se e bs
   ⇒
   repl_invariant
             <| tdecs := convert_decls (e.inf_mdecls, e.inf_tdecls, e.inf_edecls);
                tenvT := e.inf_tenvT;
                tenvM := convert_menv e.inf_tenvM;
                tenvC := e.inf_tenvC;
                tenv := bind_var_list2 (convert_env2 e.inf_tenvE) Empty;
                sem_env := se |>
             <| rinferencer_state := ((e.inf_mdecls, e.inf_tdecls, e.inf_edecls),
                                      e.inf_tenvT,
                                      e.inf_tenvM,
                                      e.inf_tenvC,
                                      e.inf_tenvE);
                rcompiler_state := e.comp_rs |>
            bs`,
 rw [repl_invariant_def, initCompEnvTheory.invariant_def] >>
 rw [convert_decls_def] >>
 rw [GSYM PULL_EXISTS]
 >- fs [type_infer_invariants_def, infer_sound_invariant_def, convert_decls_def]
 >- fs [convert_decls_def]
 >- metis_tac []
 >- metis_tac [code_labels_ok_local_to_all,contains_primitives_MEM_Label_VfromListLab,env_rs_def]
 >- (fs [init_code_executes_ok_def, code_executes_ok_def] >>
     metis_tac []));

val initial_bc_state_side_basis_state = store_thm("initial_bc_state_side_basis_state",
  ``initial_bc_state_side (SND (SND basis_state))``,
   strip_assume_tac basis_env_inv >>
   rw[initial_bc_state_side_def,basis_state_def] >> fs[] >>
   rw[Abbr`bs1`] >>
   imp_res_tac add_stop_invariant >> rfs[] >>
   fs[invariant_def,init_code_executes_ok_def] >>
   imp_res_tac bc_eval_SOME_RTC_bc_next >>
   fs[Once RTC_CASES1] )

val simple_repl_basis_lemma = prove(
  ``!input.
    let (output,b) = simple_repl_fun (SND basis_state) input in
    (repl basis_repl_env (get_type_error_mask output) input output) /\ b``,
   rpt gen_tac >>
   Cases_on`simple_repl_fun (SND basis_state) input` >>
   simp[] >>
   match_mp_tac simple_repl_thm >>
   qexists_tac `SND (SND basis_state)` >>
   qexists_tac `FST (SND basis_state)` >> simp[initial_bc_state_side_basis_state] >>
   strip_assume_tac basis_env_inv >>
   imp_res_tac add_stop_invariant >> rfs[basis_state_def] >>
   imp_res_tac convert_invariants >>
   fs[basis_repl_env_def,LET_THM] >> rfs[])

(* TODO: move

These are probably not true because of the type error mask.

val ast_repl_determ = store_thm("ast_repl_determ",
  ``∀s t i o1. ast_repl s t i o1 ⇒ ∀o2. ast_repl s t i o2 ⇒ (o2 = o1)``,
  HO_MATCH_MP_TAC ast_repl_ind >>
  conj_tac >- rw[Once ast_repl_cases] >>
  conj_tac >- cheat >>
  conj_tac >- cheat >>
  conj_tac >- (
    rw[] >>
    pop_assum mp_tac >>
    rw[Once ast_repl_cases] ) >>
  rw[] >>
    pop_assum mp_tac >>
  rw[Once ast_repl_cases] )

val repl_determ = store_thm("repl_determ",
  ``∀s t i o1 o2. repl s t i o1 ∧ repl s t i o2 ⇒ (o1 = o2)``,
  rw[repl_def] >> metis_tac[ast_repl_determ])

val simple_repl_fun_basis_thm = store_thm("simple_repl_fun_basis_thm",
  ``∀input output.
    repl basis_repl_env (get_type_error_mask output) input output ⇔
    simple_repl_fun basis_state input = (output,T)``,
  rw[] >>
  qspec_then`input`mp_tac simple_repl_basis_lemma >>
  Cases_on`simple_repl_fun basis_state input` >> simp[] >>
  rw[EQ_IMP_THM] >> rw[] >> metis_tac[repl_determ])
*)

val simple_repl_fun_basis_thm = save_thm("simple_repl_fun_basis_thm",
   simple_repl_basis_lemma)

val unrolled_repl_fun_basis_thm = store_thm("unrolled_repl_fun_basis_thm",
  ``∀input.
    let (output',b) = unrolled_repl_fun (SND basis_state) input in
      ∃output.
        let res = (THE (bc_eval (install_code (SND(SND basis_state)) initial_bc_state))).output in
        output' = Result res output ∧
        repl basis_repl_env (get_type_error_mask output) input output ∧
        b``,
  rw[LET_THM] >>
  qspec_then`input`mp_tac simple_repl_fun_basis_thm >>
  simp[UNCURRY] >> strip_tac >>
  qspecl_then[`SND basis_state`,`input`]mp_tac unrolled_repl_thm >>
  simp[initial_bc_state_side_basis_state] >>
  Cases_on`simple_repl_fun (SND basis_state) input`>>fs[])

val unlabelled_repl_fun_basis_thm = store_thm("unlabelled_repl_fun_basis_thm",
  ``∀input.
    let (output',b) = unlabelled_repl_fun (SND basis_state) input in
    ∃output.
      let res = (THE (bc_eval (install_code (SND(SND basis_state)) initial_bc_state))).output in
      output' = Result res output ∧
      repl basis_repl_env (get_type_error_mask output) input output ∧
      b``,
  rw[LET_THM] >>
  qspec_then`input`mp_tac unrolled_repl_fun_basis_thm >>
  simp[UNCURRY] >> strip_tac >>
  qexists_tac`output` >> simp[] >>
  qspecl_then[`SND basis_state`,`input`]mp_tac unlabelled_repl_thm >>
  simp[])

val basis_main_loop_thm = store_thm("basis_main_loop_thm",
  ``∀input s bs.
    basis_main_loop (SOME s) bs input =
    unlabelled_main_loop (INR s) bs input``,
  gen_tac >> completeInduct_on`LENGTH input` >> rw[] >>
  simp[Once basis_main_loop_def] >>
  simp[basis_repl_step_def] >>
  simp[Once unlabelled_main_loop_def] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  reverse BasicProvers.CASE_TAC >- (
    BasicProvers.CASE_TAC >>
    metis_tac[lex_until_top_semicolon_alt_LESS] ) >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  metis_tac[lex_until_top_semicolon_alt_LESS] )

val basis_repl_fun_lemma = prove(
  ``∀input. basis_repl_fun input =
            unlabelled_repl_fun (SND basis_state) input``,
  rw[basis_repl_fun_def] >>
  rw[unlabelled_repl_fun_def] >>
  rw[Once basis_main_loop_def] >>
  rw[basis_repl_step_def] >>
  rw[Once unlabelled_main_loop_def] >>
  `((len,labs),SND basis_state) = basis_state` by (
    simp[basis_state_def] ) >>
  simp[] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  reverse BasicProvers.CASE_TAC >- (
    BasicProvers.CASE_TAC >>
    metis_tac[basis_main_loop_thm] ) >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  metis_tac[basis_main_loop_thm] )

val basis_repl_fun_thm = store_thm("basis_repl_fun_thm",
  ``∀input.
    let (output',b) = basis_repl_fun input in
    ∃output.
      let res = (THE (bc_eval (install_code (SND(SND basis_state)) initial_bc_state))).output in
      output' = Result res output ∧
      repl basis_repl_env (get_type_error_mask output) input output ∧
      b``,
  rw[LET_THM] >>
  qspec_then`input`mp_tac unlabelled_repl_fun_basis_thm >>
  simp[UNCURRY] >> strip_tac >>
  qexists_tac`output` >> simp[] >>
  simp[basis_repl_fun_lemma])

val _ = export_theory ()
