open preamble boolSimps miscLib rich_listTheory arithmeticTheory;
open lexer_funTheory repl_funTheory replTheory untypedSafetyTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory
open lexer_implTheory mmlParseTheory inferSoundTheory BigStepTheory ElabTheory compilerProofsTheory;
open SemanticPrimitivesTheory semanticsExtraTheory TypeSystemTheory typeSoundTheory weakeningTheory typeSysPropsTheory terminationTheory;
open BytecodeTheory repl_fun_altTheory repl_fun_alt_proofTheory;
open gramPropsTheory pegSoundTheory pegCompleteTheory

val _ = new_theory "replCorrect";

val lex_impl_all_def = tDefine "lex_impl_all" `
lex_impl_all input =
  case lex_until_toplevel_semicolon input of
    | NONE => []
    | SOME (t,input') => t::lex_impl_all input'`
(wf_rel_tac `measure LENGTH` >>
 rw [] >>
 metis_tac [lex_until_toplevel_semicolon_LESS]);

val lex_aux_tokens_def = Define `
  lex_aux_tokens acc error stk input =
     case input of
       [] => NONE
     | token::rest =>
         if token = SemicolonT /\ (stk = [] \/ error) then
           SOME (REVERSE (token::acc),rest)
         else
           (let new_acc = token::acc
            in
              if error then lex_aux_tokens new_acc error stk rest
              else if token = LetT then
                lex_aux_tokens new_acc F (SH_END::stk) rest
              else if token = StructT then
                lex_aux_tokens new_acc F (SH_END::stk) rest
              else if token = SigT then
                lex_aux_tokens new_acc F (SH_END::stk) rest
              else if token = LparT then
                lex_aux_tokens new_acc F (SH_PAR::stk) rest
              else if token = EndT then
                case stk of
                  [] => lex_aux_tokens new_acc T [] rest
                | SH_END::stk' => lex_aux_tokens new_acc F stk' rest
                | SH_PAR::stk' => lex_aux_tokens new_acc T [] rest
              else if token = RparT then
                case stk of
                  [] => lex_aux_tokens new_acc T [] rest
                | SH_END::stk' => lex_aux_tokens new_acc T [] rest
                | SH_PAR::stk' => lex_aux_tokens new_acc F stk' rest
              else lex_aux_tokens new_acc F stk rest)`

val lex_until_toplevel_semicolon_tokens_def = Define `
  lex_until_toplevel_semicolon_tokens input = lex_aux_tokens [] F [] input`;

val lex_aux_tokens_LESS = prove(
  ``!acc error stk input.
      (lex_aux_tokens acc error stk input = SOME (t,rest)) ==>
      (if acc = [] then LENGTH rest < LENGTH input
                   else LENGTH rest <= LENGTH input)``,
  Induct_on `input`
  THEN1 (EVAL_TAC >> SRW_TAC [] [LENGTH] >> SRW_TAC [] [LENGTH])
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def,LET_DEF]
  >> SRW_TAC [] [] >> RES_TAC
  >> FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
  >> TRY (Cases_on `stk`) >> RES_TAC
  >> TRY (Cases_on `h`) >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [] >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [] >> RES_TAC
  >> DECIDE_TAC);

val lex_impl_all_tokens_def = tDefine "lex_impl_all_tokens" `
  lex_impl_all_tokens input =
     case lex_until_toplevel_semicolon_tokens input of
       NONE => []
     | SOME (t,input) => t::lex_impl_all_tokens input`
  (WF_REL_TAC `measure LENGTH`
   >> SIMP_TAC std_ss [lex_until_toplevel_semicolon_tokens_def]
   >> METIS_TAC [lex_aux_tokens_LESS])

val lex_aux_tokens_thm = prove(
  ``!input acc error stk res1 res2.
      (lex_aux_tokens acc error stk (lexer_fun input) = res1) /\
      (lex_aux acc error stk input = res2) ==>
      (case res2 of NONE => (res1 = NONE)
                  | SOME (ts,rest) => (res1 = SOME (ts,lexer_fun rest)))``,
  HO_MATCH_MP_TAC lexer_fun_ind >> SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> SIMP_TAC std_ss [Once lex_aux_def]
  >> ONCE_REWRITE_TAC [lexer_fun_def]
  >> ONCE_REWRITE_TAC [lex_aux_tokens_def]
  >> Cases_on `next_token input` >> ASM_SIMP_TAC (srw_ss()) []
  >> Cases_on `x`
  >> Q.MATCH_ASSUM_RENAME_TAC `next_token input = SOME (t,rest)` []
  >> FULL_SIMP_TAC (srw_ss()) []
  >> SRW_TAC [] []
  THEN1 (METIS_TAC [lexer_fun_def])
  THEN1 (METIS_TAC [lexer_fun_def])
  >> SRW_TAC [] []
  >> ASM_SIMP_TAC std_ss [GSYM lexer_fun_def]
  >> Cases_on `stk`
  >> ASM_SIMP_TAC (srw_ss()) [GSYM lexer_fun_def]
  >> Cases_on `h`
  >> ASM_SIMP_TAC (srw_ss()) [GSYM lexer_fun_def]) |> SIMP_RULE std_ss [];

val lex_impl_all_tokens_thm = prove(
  ``!input. lex_impl_all input =
            lex_impl_all_tokens (lexer_fun input)``,
  HO_MATCH_MP_TAC (fetch "-" "lex_impl_all_ind") >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once lex_impl_all_def,Once lex_impl_all_tokens_def]
  >> FULL_SIMP_TAC std_ss [lex_until_toplevel_semicolon_tokens_def]
  >> FULL_SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  >> MP_TAC (lex_aux_tokens_thm |> Q.SPECL [`input`,`[]`,`F`,`[]`])
  >> Cases_on `lex_aux [] F [] input` >> FULL_SIMP_TAC std_ss []
  >> Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) []
  >> REPEAT STRIP_TAC >> RES_TAC);

val lex_aux_tokens_thm = prove(
  ``!input stk error acc.
      (res = lex_aux_tokens acc error stk input) ==>
      case res of
        NONE => (toplevel_semi_dex (LENGTH acc) error stk input = NONE)
      | SOME (toks,rest) =>
          (toplevel_semi_dex (LENGTH acc) error stk input = SOME (LENGTH toks)) /\
          (REVERSE acc ++ input = toks ++ rest)``,
  Induct
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def]
  >> ONCE_REWRITE_TAC [toplevel_semi_dex_def]
  >> SIMP_TAC std_ss [LET_DEF] >> Cases
  >> FULL_SIMP_TAC (srw_ss()) []
  >> Cases_on `error` >> ASM_SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> RES_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM (ASSUME_TAC o GSYM)
  >> ASM_REWRITE_TAC []
  >> Cases_on `res` >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> Cases_on `stk` >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> TRY (Cases_on `h`) >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> TRY (Cases_on `x`) >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> SIMP_TAC std_ss [Once EQ_SYM_EQ]
  >> FULL_SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [LENGTH,arithmeticTheory.ADD1])
  |> Q.SPECL [`input`,`[]`,`F`,`[]`] |> Q.GEN `res` |> SIMP_RULE std_ss [LENGTH];

val split_top_level_semi_thm = prove(
  ``!input. split_top_level_semi input = lex_impl_all_tokens input``,
  HO_MATCH_MP_TAC split_top_level_semi_ind >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once split_top_level_semi_def,Once lex_impl_all_tokens_def,
      Once lex_until_toplevel_semicolon_tokens_def]
  >> MP_TAC lex_aux_tokens_thm
  >> Cases_on `lex_aux_tokens [] F [] input` >> FULL_SIMP_TAC std_ss []
  >> Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) []
  >> FULL_SIMP_TAC std_ss [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]
  >> STRIP_TAC >> RES_TAC >> POP_ASSUM MP_TAC
  >> FULL_SIMP_TAC std_ss [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]);

val lexer_correct = prove(
  ``!input. split_top_level_semi (lexer_fun input) = lex_impl_all input``,
  SIMP_TAC std_ss [lex_impl_all_tokens_thm,split_top_level_semi_thm]);

val peg_det = pegTheory.peg_deterministic |> CONJUNCT1
val parser_correct = Q.prove (
`!toks. parse_top toks = repl$parse toks`,
  rw[parse_top_def,replTheory.parse_def] >>
  rw[mmlParseREPLTop_def] >>
  qspec_then`toks`strip_assume_tac mmlPEGTheory.parse_REPLTop_total >>
  simp[destResult_def] >>
  fs[GSYM pegexecTheory.peg_eval_executed, mmlPEGTheory.pnt_def] >>
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
Induct_on`q`>>simp[id_to_string_def]>>
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
  type_infer_invariants (update_repl_state top rs el0 el1 (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st'
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
  type_infer_invariants (update_repl_state top rs el0 el1 (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st'
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
simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY]);

val invariant_def = Define`
  invariant rs rfs bs ⇔
    rfs.relaborator_state = (rs.type_bindings, rs.ctors)

    ∧ type_infer_invariants rs rfs.rinferencer_state
    ∧ type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store)

    ∧ closed_context rs.envM rs.envC rs.store rs.envE
    ∧ (∃rd c. env_rs rs.envM rs.envC rs.envE rfs.rcompiler_state (LENGTH bs.stack) rd (c,rs.store) bs)
    ∧ good_labels rfs.rcompiler_state.rnext_label bs.code

    ∧ bs.clock = NONE
    ∧ (∃ls. bs.code = PrintE++Stop::ls)

    ∧ code_labels_ok bs.code
    ∧ code_executes_ok bs
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
    closed_context menv cenv s env ∧ ALL_DISTINCT (MAP FST menv') ∧ (∀m. MEM m (MAP FST menv') ⇒ m ∉ set (MAP FST menv)) ⇒
     closed_context ((strip_mod_env menv')++menv) cenv s env``,
  rw[] >> fs[closed_context_def] >>
  fs[EVERY_MEM] >>
  `menv_dom menv ⊆ menv_dom (strip_mod_env menv' ++ menv)` by (
    srw_tac[DNF_ss][SUBSET_DEF] ) >>
  conj_tac >- (
    simp[ALL_DISTINCT_APPEND,strip_mod_env_def,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,miscTheory.FST_pair] ) >>
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
  fsrw_tac[DNF_ss][strip_mod_env_def,MEM_FLAT,MEM_MAP,UNCURRY]);

val closed_context_shift_menv = store_thm("closed_context_shift_menv",
  ``closed_context menv cenv s (env' ++ env) ∧ m ∉ set (MAP FST menv) ⇒
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
  metis_tac[]);

val evaluate_top_closed_context = store_thm("evaluate_top_closed_context",
  ``∀menv cenv s env top s' cenv' res.
    evaluate_top menv cenv s env top (s',cenv',res) ∧
    closed_context menv cenv s env ∧
    FV_top top ⊆ set (MAP (Short o FST) env) ∪ menv_dom menv ∧
    top_cns top ⊆ cenv_dom cenv
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
    Cases_on`d`>>fs[] ));

val strip_mod_env_append = store_thm("strip_mod_env_append",
  ``strip_mod_env (ls ++ l2) = strip_mod_env ls ++ strip_mod_env l2``,
  rw[strip_mod_env_def])
val strip_mod_env_length = store_thm("strip_mod_env_length",
  ``LENGTH (strip_mod_env ls) = LENGTH ls``,
  rw[strip_mod_env_def])

(* TODO: move, and things above probably too *)
val o_f_FUNION = store_thm("o_f_FUNION",
  ``f o_f (f1 ⊌ f2) = (f o_f f1) ⊌ (f o_f f2)``,
  simp[GSYM fmap_EQ_THM,FUNION_DEF] >>
  rw[o_f_FAPPLY]);

(*
val env_rs_strip_mod_env = store_thm("env_rs_strip_mod_env",
  ``closed_context menv cenv (SND s) env ∧
    DISJOINT (set (MAP FST menv')) (set (MAP FST menv)) ∧
    env_rs menv cenv env cs rd s bs ⇒
    env_rs (strip_mod_env menv' ++ menv) cenv env cs rd s bs``,
  rw[env_rs_def] >>
  fs[LET_THM] >>
  qmatch_assum_abbrev_tac`LIST_REL syneq Cs00 Cs` >>
  `Cs00 = Cs0` by (
    UNABBREV_ALL_TAC >>
    simp[MAP_EQ_f] >>
    fs[closed_context_def] >>
    rw[] >>
    simp[o_f_FUNION] >>
    simp[GSYM miscTheory.alist_to_fmap_MAP_values,strip_mod_env_def,MAP_MAP_o,UNCURRY,combinTheory.o_DEF]

  compilerTerminationTheory.v_to_Cv_def
    DB.find"v_to_Cv"

    DB.find"v_to_Cv_def"
    simp[Abbr`Cs00
  simp[env_rs_def] >> strip_tac >>
*)

val tenv_names_def = Define`
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)`
val _ = export_rewrites["tenv_names_def"]

val lookup_tenv_names = store_thm("lookup_tenv_names",
  ``∀tenv n inc x. lookup_tenv n inc tenv = SOME x ⇒ n ∈ tenv_names tenv``,
  Induct >> simp[lookup_tenv_def] >> metis_tac[])

val tenv_names_bind_var_list = store_thm("tenv_names_bind_var_list",
  ``∀n l1 l2. tenv_names (bind_var_list n l1 l2) = set (MAP FST l1) ∪ tenv_names l2``,
  ho_match_mp_tac bind_var_list_ind >>
  simp[bind_var_list_def,bind_tenv_def,EXTENSION] >>
  metis_tac[])

val _ = Parse.overload_on("tmenv_dom",``λmenv:tenvM.  set (FLAT (MAP (λx. MAP (Long (FST x) o FST) (SND x)) menv))``)
val _ = Parse.overload_on("tmenv_sdom",``λmenv:tenvM.  set (FLAT (MAP (λx. MAP (Short o FST) (SND x)) menv))``)

val type_p_closed = store_thm("type_p_closed",
  ``(∀tvs tcenv p t tenv.
       type_p tvs tcenv p t tenv ⇒
       pat_bindings p [] = MAP FST tenv ∧
       all_cns_pat p ⊆ cenv_dom tcenv) ∧
    (∀tvs cenv ps ts tenv.
      type_ps tvs cenv ps ts tenv ⇒
      pats_bindings ps [] = MAP FST tenv ∧
      all_cns_pats ps ⊆ cenv_dom cenv)``,
  ho_match_mp_tac type_p_ind >>
  simp[AstTheory.pat_bindings_def,pats_bindings_MAP] >>
  rw[] >> fs[SUBSET_DEF] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  simp[MEM_MAP,EXISTS_PROD] >>
  fs [cenv_dom_def, MEM_MAP] >>
  metis_tac[FST])

val type_e_closed = store_thm("type_e_closed",
  ``(∀tmenv tcenv tenv e t.
      type_e tmenv tcenv tenv e t
      ⇒
      FV e ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv ∧
      all_cns_exp e ⊆ cenv_dom tcenv) ∧
    (∀tmenv tcenv tenv es ts.
      type_es tmenv tcenv tenv es ts
      ⇒
      FV_list es ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv ∧
      all_cns_list es ⊆ cenv_dom tcenv) ∧
    (∀tmenv tcenv tenv funs ts.
      type_funs tmenv tcenv tenv funs ts ⇒
      let ds = set (MAP (Short o FST) funs) in
      let fs = set (MAP (Short o FST) ts) in
      fs = ds ∧
      FV_defs ds funs ⊆ ((IMAGE Short (tenv_names tenv)) DIFF fs) ∪ tmenv_dom tmenv ∧
      all_cns_defs funs ⊆ cenv_dom tcenv)``,
  ho_match_mp_tac type_e_ind >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tenv_def] >>
    metis_tac[]) >>
 strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD, cenv_dom_def] >>
    metis_tac[] ) >>
 strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD, cenv_dom_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[t_lookup_var_id_def] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[MEM_FLAT,MEM_MAP,EXISTS_PROD] >-
      metis_tac[lookup_tenv_names] >>
    BasicProvers.CASE_TAC >> fs[] >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp_tac(srw_ss()++DNF_ss)[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP,all_cns_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP] >>
    rw[] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes`[] >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac) >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >> metis_tac[]) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def,bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def,bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    qmatch_assum_abbrev_tac`FV_defs x y ⊆ a ∪ b DIFF c ∪ d` >>
    `c = a` by (
      simp[Abbr`c`,Abbr`a`,EXTENSION,MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    `b = IMAGE Short (tenv_names tenv)` by (
      simp[Abbr`b`,bind_tvar_def] >> rw[] ) >>
    `a ∪ b DIFF c ∪ d ⊆ b ∪ d` by (
      simp[SUBSET_DEF] >>
      metis_tac[] ) >>
    conj_tac >- metis_tac[SUBSET_TRANS] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    fs[Once SUBSET_DEF] >>
    metis_tac[]) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  simp[] >>
  srw_tac[DNF_ss][SUBSET_DEF,bind_tenv_def] >>
  fsrw_tac[DNF_ss][FV_defs_MAP,UNCURRY] >>
  metis_tac[] )

val type_d_closed = store_thm("type_d_closed",
  ``∀mno tmenv tcenv tenv d y z.
      type_d mno tmenv tcenv tenv d y z ⇒
        FV_dec d ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv ∧
        dec_cns d ⊆ cenv_dom tcenv``,
  ho_match_mp_tac type_d_ind >>
  strip_tac >- (
    simp[bind_tvar_def] >>
    rpt gen_tac >>
    Cases_on`tvs=0`>>simp[]>>strip_tac>>
    imp_res_tac (CONJUNCT1 type_e_closed) >> fs[] >>
    imp_res_tac (CONJUNCT1 type_p_closed) >> fs[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac (CONJUNCT1 type_e_closed) >> fs[] >>
    imp_res_tac (CONJUNCT1 type_p_closed) >> fs[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac (CONJUNCT2 type_e_closed) >>
    fs[tenv_names_bind_var_list,bind_tvar_def,LET_THM] >>
    qmatch_assum_abbrev_tac`FV_defs x y ⊆ z ∪ a DIFF b ∪ c` >>
    qmatch_abbrev_tac`FV_defs x y ⊆ e ∪ c` >>
    `a = e` by (
      simp[Abbr`a`,Abbr`e`] >> rw[] ) >>
    qunabbrev_tac`y` >>
    `z = b` by (
      UNABBREV_ALL_TAC >>
      simp[EXTENSION,MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    fs[SUBSET_DEF] >> metis_tac[] ) >>
  simp[])


val tenv_names_bind_var_list2 = store_thm("tenv_names_bind_var_list2",
  ``∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv``,
  Induct >> TRY(qx_gen_tac`p`>>PairCases_on`p`) >> simp[bind_var_list2_def,bind_tenv_def] >>
  simp[EXTENSION] >> metis_tac[])

val fst_lem = Q.prove (
`FST = λ(x,y). x`,
rw [FUN_EQ_THM] >>
PairCases_on `x` >>
fs []);

val type_d_new_dec_vs = Q.prove (
`!mn tenvM tenvC tenv d tenvC' tenv'.
  type_d mn tenvM tenvC tenv d tenvC' tenv'
  ⇒
  set (new_dec_vs d) = set (MAP FST tenv')`,
rw [type_d_cases, new_dec_vs_def, LibTheory.emp_def] >>
rw [new_dec_vs_def] >>
imp_res_tac type_p_closed >>
imp_res_tac type_e_closed >>
rw [tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
fs [LET_THM, LIST_TO_SET_MAP, GSYM fst_lem, IMAGE_COMPOSE] >>
metis_tac [IMAGE_11, AstTheory.id_11]);

val type_d_dec_cns = Q.prove (
`!mn tenvM tenvC tenv d tenvC' tenv'.
  type_d (SOME mn) tenvM tenvC tenv d tenvC' tenv'
  ⇒
  IMAGE (Long mn) (set (new_dec_cns d)) = set (MAP FST tenvC')`,
rw [type_d_cases, new_dec_cns_def, LibTheory.emp_def] >>
rw [new_dec_cns_def, build_ctor_tenv_def, MAP_FLAT, MAP_MAP_o,
    combinTheory.o_DEF, AstTheory.mk_id_def, LAMBDA_PROD] >>
fs [GSYM LIST_TO_SET_MAP, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD]);

val type_ds_closed = store_thm("type_ds_closed",
  ``∀mn tmenv cenv tenv ds y z. type_ds mn tmenv cenv tenv ds y z ⇒
     !mn'. mn = SOME mn' ⇒
      FV_decs ds ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv ∧
      decs_cns mn ds ⊆ cenv_dom cenv``,
ho_match_mp_tac type_ds_ind >>
rw [FV_decs_def,decs_cns_def] >>
imp_res_tac type_d_closed >>
fs [tenv_names_bind_var_list2] >>
rw [SUBSET_DEF] >|
[`x ∈ IMAGE Short (set (MAP FST tenv')) ∪ IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv`
         by fs [SUBSET_DEF] >>
     fs [] >>
     rw [] >>
     fs[MEM_MAP] >>
     metis_tac [type_d_new_dec_vs,MEM_MAP],
 fs [cenv_dom_def] >>
     `x ∈ NONE INSERT set (MAP (SOME o FST) (merge cenv' cenv))` by fs [SUBSET_DEF] >>
     fs [LibTheory.merge_def] >>
     imp_res_tac type_d_dec_cns >>
     pop_assum (ASSUME_TAC o GSYM) >>
     fs [] >>
     rw [] >>
     fs[AstTheory.mk_id_def, EXTENSION, MEM_MAP] >>
     metis_tac [] ]);

val type_top_closed = store_thm("type_top_closed",
  ``∀tmenv tcenv tenv top tm' tc' te'.
      type_top tmenv tcenv tenv top tm' tc' te'
      ⇒
      FV_top top ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv ∧
      top_cns top ⊆ cenv_dom tcenv``,
  ho_match_mp_tac type_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac type_d_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,LibTheory.emp_def] >>
    metis_tac[]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac type_ds_closed >>
  fs[])

val type_env_dom = Q.prove (
`!tenvM tenvC tenvS env tenv.
  type_env tenvM tenvC tenvS env tenv ⇒
  (set (MAP (Short o FST) env) = IMAGE Short (tenv_names tenv))`,
induct_on `env` >>
ONCE_REWRITE_TAC [TypeSoundInvariantsTheory.type_v_cases] >>
fs [LibTheory.emp_def, tenv_names_def] >>
fs [bind_tenv_def, LibTheory.bind_def, tenv_names_def] >>
rw [] >>
rw [] >>
metis_tac []);

val weakM_dom = Q.prove (
`!tenvM1 tenvM2.
  weakM tenvM1 tenvM2 ∧
  ALL_DISTINCT (MAP FST tenvM2)
  ⇒
  tmenv_dom tenvM2 ⊆ tmenv_dom tenvM1`,
rw [weakM_def, SUBSET_DEF] >>
fs [MEM_FLAT, MEM_MAP] >>
rw [] >>
fs [MEM_MAP] >>
rw [] >>
`?mn tenv. x' = (mn,tenv)` by metis_tac [pair_CASES] >>
rw [] >>
imp_res_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
res_tac >>
imp_res_tac alistTheory.ALOOKUP_MEM >>
fs [weakE_def] >>
`?n tvs t. y = (n,(tvs,t))` by metis_tac [pair_CASES] >>
rw [] >>
`ALOOKUP tenv n ≠ NONE` by metis_tac [alistTheory.ALOOKUP_NONE, FST, MEM_MAP] >>
`?tvs2 t2. ALOOKUP tenv n = SOME (tvs2,t2)`
            by metis_tac [pair_CASES, optionTheory.option_nchotomy] >>
res_tac >>
qpat_assum `!x. P x` (mp_tac o Q.SPEC `n`) >>
rw [] >>
cases_on `ALOOKUP tenv''' n` >>
fs [] >>
PairCases_on `x` >>
fs [] >>
qexists_tac `MAP (Long mn o FST) tenv'` >>
rw [MEM_MAP] >|
[qexists_tac `(mn, tenv')` >>
     rw [],
 imp_res_tac alistTheory.ALOOKUP_MEM >>
     metis_tac [FST]]);

val weakC_dom = Q.prove (
`!tenvC1 tenvC2.
  weakC tenvC1 tenvC2
  ⇒
  set (MAP FST tenvC2) ⊆ set (MAP FST tenvC1)`,
rw [weakC_def, SUBSET_DEF] >>
first_x_assum (mp_tac o Q.SPEC `x`) >>
rw [] >>
every_case_tac >>
fs [alistTheory.ALOOKUP_NONE] >>
imp_res_tac alistTheory.ALOOKUP_MEM >>
rw [MEM_MAP] >>
metis_tac [FST]);

val type_env_dom2 = Q.prove (
`!mn tenvM tenvC tenvS env tenv.
  type_env tenvM tenvC tenvS env (bind_var_list2 tenv Empty) ⇒
  (set (MAP (Long mn o FST) env) = set (MAP (Long mn o FST) tenv))`,
induct_on `env` >>
ONCE_REWRITE_TAC [TypeSoundInvariantsTheory.type_v_cases] >>
fs [bind_var_list2_def, LibTheory.emp_def, tenv_names_def] >>
fs [bind_tenv_def, LibTheory.bind_def, tenv_names_def] >>
rw [] >>
rw [] >>
cases_on `tenv` >>
TRY (PairCases_on `h`) >>
fs [bind_var_list2_def, bind_tenv_def] >>
metis_tac []);

val consistent_mod_env_dom = Q.prove (
`!tenvS tenvC envM tenvM.
  consistent_mod_env tenvS tenvC envM tenvM
  ⇒
  (tmenv_dom tenvM = menv_dom envM)`,
ho_match_mp_tac metaTerminationTheory.consistent_mod_env_ind >>
rw [] >>
imp_res_tac type_env_dom2 >>
metis_tac []);

val consistent_mod_env_distinct = Q.prove (
`!tenvS tenvC envM tenvM.
  consistent_mod_env tenvS tenvC envM tenvM
  ⇒
  ALL_DISTINCT (MAP FST tenvM)`,
ho_match_mp_tac metaTerminationTheory.consistent_mod_env_ind >>
rw [] >>
metis_tac []);

val consistent_con_env_dom = Q.prove (
`!envC tenvC.
  consistent_con_env envC tenvC
  ⇒
  (set (MAP FST envC) = set (MAP FST tenvC))`,
ho_match_mp_tac typeSysPropsTheory.consistent_con_env_ind >>
rw [typeSysPropsTheory.consistent_con_env_def]);

val type_sound_inv_closed = Q.prove (
`∀top rs new_tenvM new_tenvC new_tenv new_st envC r.
  type_top rs.tenvM rs.tenvC rs.tenv top new_tenvM new_tenvC new_tenv ∧
  type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store)
  ⇒
  FV_top top ⊆ set (MAP (Short o FST) rs.envE) ∪ menv_dom rs.envM ∧
  top_cns top ⊆ cenv_dom rs.envC`,
rw [] >>
imp_res_tac type_top_closed >>
`(?err. r = Rerr err) ∨ (?menv env. r = Rval (menv,env))`
        by (cases_on `r` >>
            rw [] >>
            PairCases_on `a` >>
            fs [])  >>
fs [type_sound_invariants_def, update_type_sound_inv_def] >>
rw [] >>
imp_res_tac type_env_dom >>
imp_res_tac consistent_mod_env_dom >>
imp_res_tac consistent_mod_env_distinct >>
imp_res_tac weakM_dom >>
imp_res_tac weakC_dom >>
imp_res_tac consistent_con_env_dom >>
fs [SUBSET_DEF, cenv_dom_def, MEM_MAP, EXTENSION] >>
rw [] >>
metis_tac []);

val check_dup_ctors_names_lem1 = Q.prove (
`!tds acc.
  FOLDR (λ(tvs,tn,condefs) x2. FOLDR (λ(n,ts) x2. n::x2) x2 condefs) acc tds
  =
  MAP FST (FLAT (MAP (SND o SND) tds)) ++ acc`,
induct_on `tds` >>
rw [] >>
PairCases_on `h` >>
fs [FOLDR_APPEND] >>
pop_assum (fn _ => all_tac) >>
induct_on `h2` >>
rw [] >>
PairCases_on `h` >>
fs []);

val check_dup_ctors_eqn = Q.store_thm ("check_dup_ctors_eqn",
`!tds.
  check_dup_ctors mn cenv tds
  =
  (ALL_DISTINCT (MAP FST (FLAT (MAP (SND o SND) tds))) ∧
   (!e. MEM e (MAP FST (FLAT (MAP (SND o SND) tds))) ⇒ mk_id mn e ∉ set (MAP FST cenv)))`,
SIMP_TAC (srw_ss()) [LET_THM,RES_FORALL,check_dup_ctors_def, check_dup_ctors_names_lem1] >>
induct_on `tds` >>
rw [] >>
`?tvs ts ctors. h = (tvs,ts,ctors)` by metis_tac [pair_CASES] >>
rw [] >>
fs [ALL_DISTINCT_APPEND] >>
rw [] >>
eq_tac >>
rw [] >>
fs [alistTheory.ALOOKUP_NONE] >>
fs [] >>
rw [] >|
[qpat_assum `!x. x = (tvs,ts,ctors) ∨ MEM x tds ⇒ P x` (mp_tac o Q.SPEC `(tvs,ts,ctors)`) >>
     rw [] >>
     `?v. ALOOKUP ctors e = SOME v`
              by metis_tac [alistTheory.ALOOKUP_NONE, optionTheory.NOT_SOME_NONE, optionTheory.option_nchotomy] >>
     imp_res_tac alistTheory.ALOOKUP_MEM >>
     res_tac >>
     fs [],
 PairCases_on `x` >>
     fs [] >>
     metis_tac [MEM_MAP, FST]]);

val type_ds_dup_ctors = Q.prove (
`!mn tenvM tenvC tenv ds tenvC' tenv'.
  type_ds mn tenvM tenvC tenv ds tenvC' tenv' ⇒
  !i ts tenvC_no_sig.
    i < LENGTH ds ∧ (EL i ds = Dtype ts)
    ⇒
    ALL_DISTINCT (MAP FST (FLAT (MAP (SND o SND) ts))) ∧
    (!e. MEM e (MAP FST (FLAT (MAP (SND o SND) ts)))
         ⇒
         mk_id mn e ∉ set (MAP FST (decs_to_cenv mn (TAKE i ds))) ∧
         mk_id mn e ∉ set (MAP FST tenvC))`,
ho_match_mp_tac type_ds_ind >>
REPEAT GEN_TAC >>
STRIP_TAC >>
REPEAT GEN_TAC >>
STRIP_TAC >>
REPEAT GEN_TAC >>
cases_on `i = 0` >>
fs [] >|
[fs [type_d_cases] >>
     rw [] >>
     fs [check_ctor_tenv_def, check_dup_ctors_eqn, decs_to_cenv_def],
 `0 < i` by decide_tac >>
     fs [EL_CONS] >>
     STRIP_TAC >>
     `PRE i < LENGTH ds`
               by (cases_on `i` >>
                  fs []) >>
     `i - 1 = PRE i` by decide_tac >>
     rw [decs_to_cenv_def] >>
     res_tac >>
     fs [LibTheory.merge_def] >>
     fs [type_d_cases, dec_to_cenv_def] >>
     rw [] >>
     fs [GSYM alistTheory.ALOOKUP_NONE, SIMP_RULE (srw_ss()) [] lookup_none]]);

val type_sound_inv_dup_ctors = Q.prove (
`∀mn spec ds rs new_tenvM new_tenvC new_tenv new_st envC r i ts.
  type_top rs.tenvM rs.tenvC rs.tenv (Tmod mn spec ds) new_tenvM new_tenvC new_tenv  ∧
  type_sound_invariants (rs.tenvM,rs.tenvC,rs.tenv,rs.envM,rs.envC,rs.envE,rs.store) ∧
  i < LENGTH ds ∧ (EL i ds = Dtype ts)
  ⇒
  check_dup_ctors (SOME mn) (decs_to_cenv (SOME mn) (TAKE i ds) ++ rs.envC) ts`,
rw [type_sound_invariants_def, type_top_cases, top_to_cenv_def] >>
imp_res_tac consistent_con_env_dom >>
rw [check_dup_ctors_eqn] >-
metis_tac [type_ds_dup_ctors] >-
metis_tac [type_ds_dup_ctors] >>
`mk_id (SOME mn) e ∉ set (MAP FST rs.tenvC)` by metis_tac [type_ds_dup_ctors] >>
imp_res_tac weakC_not_SOME >>
imp_res_tac consistent_mod_env_distinct >>
imp_res_tac weakM_dom >>
res_tac >>
fs [SUBSET_DEF] >>
fs [weak_other_mods_def, GSYM alistTheory.ALOOKUP_NONE]);

val consistent_mod_env_dom = Q.prove (
`!tenvS tenvC menv tenvM.
  consistent_mod_env tenvS tenvC menv tenvM ⇒
  (MAP FST menv = MAP FST tenvM)`,
ho_match_mp_tac metaTerminationTheory.consistent_mod_env_ind >>
rw [metaTerminationTheory.consistent_mod_env_def]);

val consistent_mod_env_dup_modules = Q.prove (
`!tenvM_no_sig rs. 
  consistent_mod_env tenvS tenvC_no_sig
        (MAP (λ(n,tenv). (n,[]))
           (MAP
              (λ(mn,env).
                 (mn,MAP (λ(x,tvs,t). (x,tvs,convert_t t)) env))
              new_infer_menv) ++ rs.envM) tenvM_no_sig
 ⇒ 
 ALL_DISTINCT (MAP FST new_infer_menv) ∧
 ∀m. MEM m (MAP FST new_infer_menv) ⇒ m ∉ set (MAP FST rs.envM)`,
 induct_on `new_infer_menv` >>
 rw [metaTerminationTheory.consistent_mod_env_def] >>
 PairCases_on `h` >>
 fs [] >>
 cases_on `tenvM_no_sig` >>
 fs [metaTerminationTheory.consistent_mod_env_def] >>
 PairCases_on `h` >>
 fs [metaTerminationTheory.consistent_mod_env_def, MEM_MAP] >>
 fs [METIS_PROVE [] ``(~a ∨ b) = (a ⇒ b)``] >>
 rw [] >>
 imp_res_tac consistent_mod_env_dom >>
 fs [MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, GSYM PFORALL_THM, GSYM PEXISTS_THM] >>
 metis_tac [fst_lem, consistent_mod_env_dom, pair_CASES, MEM_APPEND, MEM_MAP, FST]);

val evaluate_top_to_cenv = store_thm("evaluate_top_to_cenv",
  ``∀menv cenv store env top res.
    evaluate_top menv cenv store env top res ⇒
    SND (SND res) ≠ Rerr Rtype_error ⇒
    ∃cenv'. top_to_cenv top = cenv' ++ (FST(SND res))``,
  HO_MATCH_MP_TAC evaluate_top_ind >> simp[] >>
  strip_tac >- (
    simp[top_to_cenv_def] >> rw[] >>
    imp_res_tac evaluate_dec_dec_to_cenv >> fs[] ) >>
  strip_tac >- (
    simp[top_to_cenv_def] >> rw[] >>
    imp_res_tac evaluate_dec_err_cenv_emp >> fs[LibTheory.emp_def] ) >>
  strip_tac >- (
    simp[top_to_cenv_def] >> rw[] >>
    imp_res_tac evaluate_decs_to_cenv >> fs[] ) >>
  rw[] >>
  simp[top_to_cenv_def] >>
  imp_res_tac evaluate_decs_to_cenv >>
  fs[])


val ctac =
  qspecl_then[`st.rcompiler_state`,`top`]mp_tac compile_top_append_code >>
  discharge_hyps >- (
    `MAP FST st.rcompiler_state.renv = MAP FST rs.envE` by (
      fs[env_rs_def,LET_THM,GSYM MAP_MAP_o] ) >>
    simp[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,MEM_FLAT] >>
    rw[] >> res_tac >> fs[MEM_MAP] >> metis_tac[] )

val labels_tac =
  ctac >>
  imp_res_tac RTC_bc_next_preserves >>
  qpat_assum`bs.code = PrintE++Y++Z`kall_tac >>
  simp[between_labels_def,good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
  fs[good_labels_def] >> strip_tac >>
  fsrw_tac[DNF_ss][EVERY_MEM,miscTheory.between_def,MEM_FILTER,MEM_MAP,is_Label_rwt,Abbr`new_repl_fun_state`,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC

val PrintE_labels = store_thm("PrintE_labels",
  ``good_labels 4 PrintE``, EVAL_TAC)

val lem13 = prove(
  ``13 < LENGTH PrintE ∧ EL 13 PrintE = Label 0 ∧
    next_addr il (TAKE 14 PrintE) =
    next_addr il (TAKE 13 PrintE)``,
EVAL_TAC)

val _ =  computeLib.add_funs[CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV NRC]

val PrintE_thm = store_thm("PrintE_thm",
  ``∀bs bv st err.
    bs.code = PrintE
    ∧ bs.pc = 0
    ∧ bs.stack = bv::st
    ∧ err_bv err bv
    ⇒
    let bs' = bs with <|pc:=next_addr bs.inst_length bs.code
                       ;stack:=st
                       ;output:=bs.output++("raise "++print_error err)
                       |> in
    bc_next^* bs bs'``,
  (*
    It would be nice to prove this by evaluation, but it would require some tricks...
    rw[] >>
    simp[RTC_eq_NRC] >>
    Cases_on`err`>>fs[err_bv_def]>>
    TRY (
      qmatch_assum_rename_tac`bv = Number i`[] >>
      qexists_tac`13` >>
      EVAL_TAC >>
      simp[bc_eval1_thm,Abbr`bs'`] >>
      `bs = bs with <|code:=PrintE;pc:=0;stack:=Number i::st;output:=bs.output;inst_length:=bs.inst_length|>` by (
        simp[bc_state_component_equality] ) >>
      pop_assum SUBST1_TAC >>
      EVAL_TAC
  *)
  assume_tac PrintE_labels >>
  fs[good_labels_def] >>
  rw[] >>
  qabbrev_tac`bs1 = bs with <|pc := next_addr bs.inst_length (TAKE (LENGTH "raise ") PrintE)
                             ;output := bs.output++("raise ")|>` >>
  `bc_next^* bs bs1` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`"raise "` >>
    qexists_tac`[]` >>
    simp[PrintE_def] >>
    simp[Abbr`bs1`,bc_state_component_equality] >>
    EVAL_TAC >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  qabbrev_tac`bs2 = bs1 with <|pc:=next_addr bs.inst_length (TAKE 8 PrintE)
                              ;stack := (bool_to_val (is_Block bv))::bv::st|>` >>
  `bc_next^* bs1 bs2` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC 0)` >>
    simp[NRC] >>
    `bc_fetch bs1 = SOME (Stack(Load 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 6 PrintE` >>
      qexists_tac`DROP 7 PrintE` >>
      simp[Abbr`bs1`] >> EVAL_TAC) >>
    simp[Once bc_eval1_thm] >>
    simp[bc_eval1_def] >>
    simp[bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def] >>
    qmatch_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs1 = SOME (Stack IsBlock)` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 7 PrintE` >>
      qexists_tac`DROP 8 PrintE` >>
      simp[Abbr`bs1`] >>
      EVAL_TAC >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`] >>
    Cases_on`bv`>>simp[bc_eval_stack_def,Abbr`bs2`,bc_state_component_equality] >>
    EVAL_TAC >> simp[SUM_APPEND,FILTER_APPEND] >>
    Cases_on`err`>>fs[compilerProofsTheory.err_bv_def] ) >>
  `bc_fetch bs2 = SOME (JumpIf (Lab 0))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE 8 PrintE` >>
    qexists_tac`DROP 9 PrintE` >>
    simp[Abbr`bs2`,Abbr`bs1`] >>
    EVAL_TAC) >>
  Cases_on`err`>>fs[compilerProofsTheory.err_bv_def]>>
  TRY (
    qmatch_assum_rename_tac`bv = Number i`[] >>
    `bc_next bs2 (bump_pc bs2 with <|stack := bv::st|>)` by (
      simp[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs2`,bc_state_component_equality,bump_pc_with_stack] >>
      simp[bc_find_loc_def] >>
      qmatch_abbrev_tac`∃n. x = SOME n` >>
      qsuff_tac`x ≠ NONE`>-(Cases_on`x`>>rw[])>>
      simp[Abbr`x`] >> spose_not_then strip_assume_tac >>
      imp_res_tac bc_find_loc_aux_NONE >>
      pop_assum mp_tac >>
      simp[Abbr`bs1`] >>
      EVAL_TAC ) >>
    qmatch_assum_abbrev_tac`bc_next bs2 bs3` >>
    qabbrev_tac`bs4 = bump_pc bs3 with <|output := SNOC #"<" bs3.output|>` >>
    `bc_fetch bs3 = SOME (PrintC #"<")` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 9 PrintE` >>
      qexists_tac`DROP 10 PrintE` >>
      simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,bump_pc_def] >>
      EVAL_TAC >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    `bc_next bs3 bs4` by ( simp[bc_eval1_thm,bc_eval1_def,IMPLODE_EXPLODE_I] ) >>
    `bc_fetch bs4 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 10 PrintE` >>
      qexists_tac`DROP 11 PrintE` >>
      simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,bump_pc_def] >>
      EVAL_TAC >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    qabbrev_tac`bs5 = bump_pc bs4 with <|stack:=st;output := bs4.output++(int_to_string i)|>` >>
    `bc_next bs4 bs5` by (
      simp[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs4`,Abbr`bs3`,bump_pc_def,Abbr`bs5`] >>
      simp[bc_state_component_equality,IMPLODE_EXPLODE_I] >>
      EVAL_TAC) >>
    qabbrev_tac`bs6 = bump_pc bs5 with <|output := SNOC #">" bs5.output|>` >>
    `bc_fetch bs5 = SOME (PrintC #">")` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 11 PrintE` >>
      qexists_tac`DROP 12 PrintE` >>
      simp[Abbr`bs5`,bump_pc_def] >>
      UNABBREV_ALL_TAC >>
      simp[bump_pc_def] >>
      EVAL_TAC >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    `bc_next bs5 bs6` by ( simp[bc_eval1_thm,bc_eval1_def,IMPLODE_EXPLODE_I] ) >>
    `bc_fetch bs6 = SOME (Jump (Lab 3))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 12 PrintE` >>
      qexists_tac`DROP 13 PrintE` >>
      simp[Abbr`bs6`,bump_pc_def] >>
      simp[Abbr`bs5`,bump_pc_def] >>
      UNABBREV_ALL_TAC >>
      simp[bump_pc_def] >>
      EVAL_TAC >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    `bc_next bs6 bs'` by (
      simp[bc_eval1_thm,bc_eval1_def] >>
      simp[bc_state_component_equality] >>
      conj_tac >- (
        simp[bc_find_loc_def] >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[Abbr`bs6`,Abbr`bs5`,bump_pc_def] >>
        UNABBREV_ALL_TAC >> simp[bump_pc_def] >>
        qexists_tac`LENGTH PrintE - 1` >>
        EVAL_TAC ) >>
      `bs6.output = bs'.output` by (
        simp[Abbr`bs6`,Abbr`bs'`,print_error_def] >>
        simp[Abbr`bs5`,Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`,bump_pc_def] ) >>
      simp[Abbr`bs6`,Abbr`bs5`,bump_pc_def] >>
      UNABBREV_ALL_TAC >> simp[bump_pc_def] >> EVAL_TAC >> rw[] >> EVAL_TAC ) >>
    rpt(qpat_assum`Abbrev(x =y)`kall_tac) >>
    rpt(qpat_assum`bc_fetch x = y`kall_tac) >>
    qsuff_tac`bc_next^* bs2 bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC(SUC(SUC(SUC 0))))` >>
    simp[NRC] >>
    metis_tac[] ) >>
  fs[print_error_def] >>
  qmatch_assum_abbrev_tac`bv = Block t []` >>
  qabbrev_tac`bs3 = bs2 with <|stack:=(bool_to_val (t=block_tag+bind_exc_cn))::bv::st; pc := next_addr bs.inst_length (TAKE 16 PrintE)|>` >>
  `bc_next^* bs2 bs3` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC(SUC 0))` >>
    simp[NRC] >>
    qho_match_abbrev_tac`∃z. bc_next bs2 z ∧ P z` >>
    simp[bc_eval1_thm,bc_eval1_def]>>
    simp[Abbr`bs2`,Abbr`bs3`,Abbr`bs1`] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    simp[bc_find_loc_def] >>
    qexists_tac`next_addr bs.inst_length (TAKE 14 PrintE)` >>
    conj_tac >- (match_mp_tac bc_find_loc_aux_ALL_DISTINCT>>fs[]>>qexists_tac`13`>>EVAL_TAC) >>
    qmatch_abbrev_tac`P bs1` >>
    `bc_fetch bs1 = SOME (Stack (Load 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`] >>
      qexists_tac`TAKE 14 PrintE` >>
      qexists_tac`DROP 15 PrintE` >>
      EVAL_TAC ) >>
    simp[Abbr`P`] >>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    simp[bc_eval1_thm,bc_eval1_def]>>
    simp[bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def] >>
    qmatch_abbrev_tac`P bs1` >>
    `bc_fetch bs1 = SOME (Stack (TagEq (block_tag+bind_exc_cn)))`  by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs1`] >>
      qexists_tac`TAKE 15 PrintE` >>
      qexists_tac`DROP 16 PrintE` >>
      EVAL_TAC >>
      simp[Abbr`t`,IntLangTheory.bind_exc_cn_def]) >>
    simp[Abbr`P`] >>
    simp[bc_eval1_thm,bc_eval1_def]>>
    simp[bump_pc_def]>>
    simp[Abbr`bs1`,bc_eval_stack_def]>>
    simp[bc_state_component_equality]>>
    EVAL_TAC>>
    simp[Abbr`t`,IntLangTheory.bind_exc_cn_def] ) >>
  `bc_fetch bs3 = SOME (JumpIf (Lab 1))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE 16 PrintE` >>
    qexists_tac`DROP 17 PrintE` >>
    simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`]>>
    EVAL_TAC ) >>
  TRY (
    `t=block_tag+bind_exc_cn` by (simp[Abbr`t`]>>NO_TAC) >> pop_assum kall_tac >>
    qsuff_tac`bc_next^* bs3 bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def] >>
    simp[Abbr`bs3`] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    qexists_tac`next_addr bs.inst_length (TAKE 33 PrintE)` >>
    conj_tac >- (
      simp[bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      fs[Abbr`bs2`,Abbr`bs1`] >>
      qexists_tac`32` >>
      EVAL_TAC ) >>
    qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    qexists_tac`bump_pc bs3 with stack := TL bs3.stack` >>
    `bc_fetch bs3 = SOME (Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 33 PrintE` >>
      qexists_tac`DROP 34 PrintE` >>
      simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
      EVAL_TAC ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs3`,bc_eval_stack_def] >>
    qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
    simp[Once RTC_CASES2] >> disj2_tac >>
    qexists_tac`bs3 with <|stack:=st; pc := next_addr bs.inst_length (TAKE 40 PrintE); output := bs'.output|>` >>
    conj_tac >- (
      match_mp_tac MAP_PrintC_thm >>
      qexists_tac`DROP (LENGTH bs.output + LENGTH "raise ") bs'.output` >>
      qexists_tac`TAKE 34 PrintE` >>
      qexists_tac`DROP 40 PrintE` >>
      simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
      conj_tac >- (
        EVAL_TAC >>
        simp[Abbr`bs'`,DROP_APPEND1,miscTheory.DROP_LENGTH_NIL_rwt,DROP_APPEND2] ) >>
      simp[bc_state_component_equality,Abbr`bs'`] >>
      simp[DROP_APPEND1,DROP_APPEND2] >>
      EVAL_TAC >>
      simp[SUM_APPEND,FILTER_APPEND]) >>
    qmatch_abbrev_tac`bc_next bs4 bs'` >>
    `bc_fetch bs4 = SOME (Jump (Lab 3))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 40 PrintE` >>
      simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
      qexists_tac`DROP 41 PrintE` >>
      EVAL_TAC ) >>
    simp[bc_eval1_thm,bc_eval1_def] >>
    simp[Abbr`bs4`,bc_state_component_equality,Abbr`bs'`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
    simp[bc_find_loc_def] >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    qexists_tac`LENGTH PrintE - 1` >>
    fs[] >>
    EVAL_TAC) >>
  TRY (
    `t=block_tag+div_exc_cn` by (simp[Abbr`t`]>>NO_TAC) >> pop_assum kall_tac >>
    qsuff_tac`bc_next^* bs3 bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_fetch_with_stack] >>
    simp[Abbr`bs3`] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    simp[Abbr`t`,IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def,bump_pc_def] >>
    qexists_tac`next_addr bs.inst_length (TAKE 33 PrintE)` >>
    conj_tac >- (
      simp[bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      fs[Abbr`bs2`,Abbr`bs1`] >>
      qexists_tac`32` >>
      EVAL_TAC ) >>
    qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    qexists_tac`bump_pc bs3 with stack := (bool_to_val T)::(TL bs3.stack)` >>
    `bc_fetch bs3 = SOME (Stack (TagEq (block_tag+div_exc_cn)))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 17 PrintE` >>
      qexists_tac`DROP 18 PrintE` >>
      simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
      EVAL_TAC >>
      simp[FILTER_APPEND,SUM_APPEND]) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs3`,bc_eval_stack_def] >>
    conj_tac >- (
      simp[bc_state_component_equality] >>
      simp[IntLangTheory.div_exc_cn_def] ) >>
    qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
    simp[Once RTC_CASES1] >> disj2_tac >>
    qexists_tac`bump_pc bs3 with <|stack := TL bs3.stack; pc := next_addr bs.inst_length (TAKE 42 PrintE)|>` >>
    `bc_fetch bs3 = SOME (JumpIf (Lab 2))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`TAKE 18 PrintE` >>
      qexists_tac`DROP 19 PrintE` >>
      simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
      EVAL_TAC >>
      simp[FILTER_APPEND,SUM_APPEND]) >>
    simp[bump_pc_def] >>
    simp[bc_eval1_thm,bc_eval1_def] >>
    simp[Abbr`bs3`] >>
    conj_tac >- (
      simp_tac(srw_ss()++DNF_ss)[] >>
      simp[bc_state_component_equality] >>
      simp[bc_find_loc_def] >>
      simp[Abbr`bs2`,Abbr`bs1`] >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      fs[] >>
      qexists_tac`41` >>
      EVAL_TAC ) >>
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`DROP (LENGTH bs.output + LENGTH "raise ") bs'.output` >>
    qexists_tac`TAKE 42 PrintE` >>
    qexists_tac`DROP 47 PrintE` >>
    simp[Abbr`bs2`,Abbr`bs1`] >>
    conj_tac >- (
      EVAL_TAC >>
      simp[Abbr`bs'`,DROP_APPEND1,miscTheory.DROP_LENGTH_NIL_rwt,DROP_APPEND2] ) >>
    simp[bc_state_component_equality,Abbr`bs'`] >>
    simp[DROP_APPEND1,DROP_APPEND2] >>
    EVAL_TAC ) >>
  qsuff_tac`bc_next^* bs3 bs'` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_fetch_with_stack] >>
  simp[Abbr`bs3`] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  simp[Abbr`t`,IntLangTheory.bind_exc_cn_def,IntLangTheory.eq_exc_cn_def,bump_pc_def] >>
  qexists_tac`next_addr bs.inst_length (TAKE 33 PrintE)` >>
  conj_tac >- (
    simp[bc_find_loc_def] >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    fs[Abbr`bs2`,Abbr`bs1`] >>
    qexists_tac`32` >>
    EVAL_TAC ) >>
  qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
  `bc_fetch bs3 = SOME (Stack(TagEq (block_tag+div_exc_cn)))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE 17 PrintE` >>
    qexists_tac`DROP 18 PrintE` >>
    simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
    EVAL_TAC >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_fetch_with_stack] >>
  simp[Abbr`bs3`,bc_eval_stack_def] >>
  qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
  `bc_fetch bs3 = SOME (JumpIf (Lab 2))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE 18 PrintE` >>
    qexists_tac`DROP 19 PrintE` >>
    simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
    EVAL_TAC >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_fetch_with_stack] >>
  simp[Abbr`bs3`,bc_eval_stack_def] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  simp[IntLangTheory.div_exc_cn_def,IntLangTheory.eq_exc_cn_def,bump_pc_def] >>
  qexists_tac`next_addr bs.inst_length (TAKE 42 PrintE)` >>
  conj_tac >- (
    simp[bc_find_loc_def] >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    fs[Abbr`bs2`,Abbr`bs1`] >>
    qexists_tac`41` >>
    EVAL_TAC ) >>
  qmatch_abbrev_tac`bc_next^* bs3 bs'` >>
  simp[Once RTC_CASES2] >> disj2_tac >>
  qexists_tac`bs3 with <|stack:=st; pc := next_addr bs.inst_length (TAKE 31 PrintE); output := bs'.output|>` >>
  conj_tac >- (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`DROP (LENGTH bs.output + LENGTH "raise ") bs'.output` >>
    qexists_tac`TAKE 19 PrintE` >>
    qexists_tac`DROP 31 PrintE` >>
    simp[Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
    conj_tac >- (
      EVAL_TAC >>
      simp[Abbr`bs'`,DROP_APPEND1,miscTheory.DROP_LENGTH_NIL_rwt,DROP_APPEND2] ) >>
    simp[bc_state_component_equality,Abbr`bs'`,DROP_APPEND1,DROP_APPEND2] >>
    EVAL_TAC >>
    simp[FILTER_APPEND,SUM_APPEND] ) >>
  qmatch_abbrev_tac`bc_next bs4 bs'` >>
  `bc_fetch bs4 = SOME (Jump (Lab 3))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`TAKE 31 PrintE` >>
    simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
    qexists_tac`DROP 32 PrintE` >>
    EVAL_TAC) >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  simp[Abbr`bs4`,bc_state_component_equality,Abbr`bs'`,Abbr`bs3`,Abbr`bs2`,Abbr`bs1`] >>
  simp[bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH PrintE - 1` >>
  fs[] >>
  EVAL_TAC)

val and_shadow_def = zDefine`and_shadow = $/\`

val lemma = prove(``∀ls. next_addr len ls = SUM (MAP (λi. if is_Label i then 0 else len i + 1) ls)``,
  Induct >> simp[] >> rw[] >> fs[] >> simp[ADD1] )

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

val replCorrect'_lem = Q.prove (
`!repl_state error_mask bc_state repl_fun_state.
  invariant repl_state repl_fun_state bc_state ⇒
  ast_repl repl_state
    (get_type_error_mask (FST (main_loop' (bc_state,repl_fun_state) input)))
    (MAP parse (split_top_level_semi (lexer_fun input)))
    (FST (main_loop' (bc_state,repl_fun_state) input))
  ∧ SND (main_loop' (bc_state,repl_fun_state) input)`,

completeInduct_on `LENGTH input` >>
simp[GSYM and_shadow_def] >>
rw [lexer_correct, Once lex_impl_all_def] >>
ONCE_REWRITE_TAC [main_loop'_def] >>
cases_on `lex_until_toplevel_semicolon input` >>
rw [get_type_error_mask_def] >- (
  rw[and_shadow_def] >> metis_tac [ast_repl_rules] ) >>
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
 rw[and_shadow_def] >>
 metis_tac [lexer_correct,FST,SND]) >>
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
  rw[and_shadow_def] >>
  rw[get_type_error_mask_def] >>
  metis_tac [lexer_correct,FST,SND]) >>
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
           (update_type_sound_inv top
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
  simp[and_shadow_def] >>
  conj_asm1_tac >- (
    MAP_EVERY qexists_tac [`convert_menv new_infer_menv`,`new_infer_cenv`,`convert_env2 new_infer_env`] >>
    rw [] >>
    qpat_assum`∀m. X ⇒ Y`kall_tac >>
    spose_not_then strip_assume_tac >> fs[] >>
    qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`store2,envC2,r`]mp_tac compile_top_thm >>
    simp[] >>
    conj_tac >- (
      conj_tac >- (
        fs[closed_top_def] >>
        reverse conj_tac >- metis_tac [type_sound_inv_closed] >>
        fs[invariant_def] ) >>
      metis_tac [type_sound_inv_dup_ctors] ) >>
    qexists_tac`st.rcompiler_state` >> strip_tac >>
    simp[] >>
    qmatch_assum_abbrev_tac`bc_eval bs0 = NONE` >>
    fs[invariant_def] >>
    map_every qexists_tac[`rd`,`bs0 with clock := SOME ck`,`bs.code`] >>
    simp[] >>
    conj_tac >- (
      fs[env_rs_def,LET_THM] >> rfs[] >> fs[] >>
      rpt HINT_EXISTS_TAC >> simp[] >>
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
      `∃ls1. bs1.code = PrintE++Stop::ls1` by (
        rfs[Abbr`bs0`,install_code_def] ) >>
      qmatch_assum_rename_tac`err_bv err bv`[] >>
      qspecl_then[`bs1 with <|clock := NONE; code := PrintE|>`,`bv`,`bs0.stack`,`err`]mp_tac PrintE_thm >>
      simp[] >> spose_not_then strip_assume_tac >>
      qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
      `bc_next^* (bs1 with clock := NONE) (bs3 with code := bs1.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs2`,`bs3`] >>
        simp[Abbr`bs2`,Abbr`bs3`,bc_state_component_equality] >>
        rfs[] ) >>
      qmatch_assum_abbrev_tac`bc_next^* bs4 bs5` >>
      `bc_next^* bs0 bs5` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
      `∃bs9. bc_next bs5 bs9` by metis_tac[] >>
      pop_assum mp_tac >>
      `bc_fetch bs5 = SOME Stop` by (
        match_mp_tac bc_fetch_next_addr >>
        simp[Abbr`bs5`] >>
        qexists_tac`PrintE` >>
        simp[Abbr`bs3`,Abbr`bs4`] ) >>
      simp[bc_eval1_thm,bc_eval1_def] ) >>
    PairCases_on`a` >> simp[] >>
    tac >>
    `∃bs3. bc_next (bs1 with clock := NONE) bs3` by metis_tac[] >>
    pop_assum mp_tac >>
    `bc_fetch (bs1 with clock := NONE) = NONE` by (
      simp[BytecodeTheory.bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      fs[Abbr`bs0`,install_code_def] ) >>
    simp[bc_eval1_thm,bc_eval1_def] >>
    simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE]
    end ) >>
  fs[] >> fs[] >>
  fs[invariant_def] >>
  simp[code_executes_ok_def] >>
  disj2_tac >>
  qx_gen_tac`n` >>
  qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`]mp_tac compile_top_divergence >>
  disch_then(qspecl_then[`st.rcompiler_state`,`rd`,`n`,`bs.code`]mp_tac) >> simp[] >>
  disch_then(qspec_then`install_code (cpam css) code bs with clock := SOME n`mp_tac) >>
  discharge_hyps >- (
    conj_tac >- metis_tac[untyped_safety_top] >>
    conj_tac >- (simp[closed_top_def] >> metis_tac[type_sound_inv_closed]) >>
    conj_tac >- metis_tac[type_sound_inv_dup_ctors] >>
    conj_tac >- (
      match_mp_tac env_rs_change_clock >>
      simp[] >>
      qexists_tac`c,rs.store` >>
      qexists_tac`bs with <|output:="";cons_names:=cpam css;pc:=next_addr bs.inst_length bs.code|>` >>
      simp[bc_state_component_equality,install_code_def] >>
      match_mp_tac env_rs_with_bs_irr >>
      qexists_tac`bs` >> simp[] ) >>
    simp[install_code_def] ) >>
  disch_then(qx_choosel_then[`s2`]strip_assume_tac) >> fs[] >>
  imp_res_tac RTC_bc_next_uses_clock >>
  rfs[] >>
  imp_res_tac NRC_bc_next_can_be_unclocked >> fs[] >>
  qmatch_assum_abbrev_tac`NRC bc_next n (bs0 with clock := NONE) bs1` >>
  `bs0 with clock := NONE = bs0` by (
    simp[Abbr`bs0`,bc_state_component_equality,install_code_def] ) >>
  qexists_tac`bs1`>>fs[]>>
  imp_res_tac RTC_bc_next_output_IS_PREFIX >>
  fs[Abbr`bs0`,install_code_def,Abbr`bs1`] >> rfs[] >>
  fs[IS_PREFIX_NIL] ) >>

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
  conj_tac >- (
    fs[closed_top_def] >>
    metis_tac [type_sound_inv_closed]
    ) >>
  conj_tac >- metis_tac [type_sound_inv_dup_ctors] >>
  conj_tac >- (
    fs[Abbr`bs0`,install_code_def,env_rs_def,LET_THM] >> rfs[] >> fs[] >>
    rpt HINT_EXISTS_TAC >> simp[] >>
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
simp[UNCURRY] >>
`STRLEN input_rest < STRLEN input` by metis_tac[lex_until_toplevel_semicolon_LESS] >>
simp[Once ast_repl_cases,get_type_error_mask_def] >>
simp[and_shadow_def] >>
reverse conj_tac >- (
  first_x_assum(qspec_then`STRLEN input_rest`mp_tac) >> simp[] >>
  disch_then(qspec_then`input_rest`mp_tac) >> simp[] >>
  cheat (* probably need to refactor this to reuse the proofs below? *)
  ) >>
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
  discharge_hyps >- (
    conj_tac >- (
      fs[closed_top_def] >>
      reverse conj_tac >- metis_tac [type_sound_inv_closed] >>
      fs[invariant_def] ) >>
    metis_tac [type_sound_inv_dup_ctors]) >>
  disch_then(qspec_then`st.rcompiler_state`mp_tac) >>
  disch_then(Q.X_CHOOSE_THEN`ck`mp_tac) >>
  simp[] >>
  `∃rd c.
    env_rs rs.envM rs.envC rs.envE st.rcompiler_state (LENGTH bs.stack) rd (c,rs.store) bs` by (
    fs[invariant_def,LET_THM] >> metis_tac[] ) >>
  qmatch_assum_abbrev_tac`bc_eval bs0 = SOME bs1` >>
  disch_then(qspecl_then[`rd`,`bs0 with clock := SOME ck`]mp_tac) >>
  `bs0.code = bs.code ++ REVERSE code` by fs[install_code_def,Abbr`bs0`] >>
  simp[] >>
  discharge_hyps >- (
    fs[invariant_def,LET_THM,Abbr`bs0`,install_code_def] >>
    fs[env_rs_def,LET_THM] >> rfs[] >> fs[] >>
    rpt HINT_EXISTS_TAC >> simp[] >>
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
      fs[Abbr`bs0`,install_code_def] >>
      simp[FILTER_APPEND,SUM_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE]) >>
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
    Q.PAT_ABBREV_TAC`new_repl_state = update_repl_state top X Y Z a b cd de e f` >>
    Q.PAT_ABBREV_TAC`new_repl_fun_state = X:repl_fun_state` >>
    first_x_assum(qspecl_then[`new_repl_state`,`new_bc_state`,`new_repl_fun_state`]mp_tac) >>
    simp[lexer_correct] >>

    discharge_hyps >- (

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
    `FV_top top ⊆ set (MAP (Short o FST) rs.envE) ∪ menv_dom rs.envM ∧
     top_cns top ⊆ cenv_dom rs.envC`
             by (fs[closed_top_def] >> metis_tac [type_sound_inv_closed]) >>
    conj_tac >- (
      qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`store2`,`envC2`,`Rval (a0,a1)`]mp_tac evaluate_top_closed_context >>
      simp[] >>
      simp[Abbr`new_repl_state`,update_repl_state_def]) >>
    conj_tac >- (
      simp[Abbr`new_repl_state`,update_repl_state_def,Abbr`new_bc_state`] >>
      simp[Abbr`new_repl_fun_state`] >>
      qexists_tac`rd2` >>
      qexists_tac`ARB` >>
      fs[env_rs_def,LET_THM] >> rfs[] >> fs[] >>
      rpt HINT_EXISTS_TAC >>
      simp[] >>
      match_mp_tac toBytecodeProofsTheory.Cenv_bs_change_store >>
      map_every qexists_tac[`rd2`,`(0,Cs'')`,`bs2`,`bs2.refs`,`NONE`] >>
      simp[BytecodeTheory.bc_state_component_equality] >>
      rfs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.s_refs_def,toBytecodeProofsTheory.good_rd_def] ) >>
    conj_tac >- ( labels_tac  ) >>
    simp[Abbr`new_bc_state`] >>
    imp_res_tac RTC_bc_next_preserves >>
    fs[] >>
    conj_tac >- (
      match_mp_tac bytecodeLabelsTheory.code_labels_ok_append >> simp[] >>
      conj_tac >- rfs[] >>
      ctac >> simp[]) >>
    simp[code_executes_ok_def] >>
    disj1_tac >>
    qexists_tac`bs2 with clock := NONE` >>
    simp[lemma] >>
    disj2_tac >>
    simp[MAP_REVERSE,SUM_REVERSE,SUM_APPEND] ) >>
  simp[] ) >>

  (* exception *)
  reverse(Cases_on`e`>>fs[])>-(
    metis_tac[bigClockTheory.top_evaluate_not_timeout] ) >>

  disch_then(qx_choosel_then[`bv`,`bs2`,`rd2`]strip_assume_tac) >>
  qmatch_assum_rename_tac`err_bv err bv`[] >>
  qmatch_abbrev_tac`X = PR ∧ Y` >>
  `∃bs3. bc_next^* bs2 bs3 ∧ bs3.output = PR ∧ bc_fetch bs3 = SOME Stop ∧ bs3.stack = bs0.stack ∧ bs3.refs = bs2.refs` by (
    `∃ls2. bs2.code = PrintE++Stop::ls2` by (
      imp_res_tac RTC_bc_next_preserves >>
      fs[Abbr`bs0`,install_code_def] >>
      fs[invariant_def] ) >>
    qunabbrev_tac`Y` >>
    qspecl_then[`bs2 with <|code := PrintE|>`,`bv`,`bs0.stack`,`err`]mp_tac PrintE_thm >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs3 bs4` >>
    qexists_tac`bs4 with code := bs2.code` >>
    conj_tac >- (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs3`,`bs4`] >>
      simp[Abbr`bs3`,Abbr`bs4`,bc_state_component_equality]) >>
    simp[Abbr`bs4`] >>
    conj_tac >- (
      simp[Abbr`PR`,print_result_def,Abbr`bs0`] >>
      simp[install_code_def] ) >>
    match_mp_tac bc_fetch_next_addr >>
    simp[] >>
    qexists_tac`PrintE` >>
    simp[]) >>
  `∀s3. ¬bc_next (bs3 with clock := NONE) s3` by (
    simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock] ) >>
  qspecl_then[`bs0 with clock := SOME ck`,`bs3`]mp_tac RTC_bc_next_can_be_unclocked >>
  discharge_hyps >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
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
  Q.PAT_ABBREV_TAC`new_repl_state = update_repl_state top X Y Z a b cd de e f` >>
  Q.PAT_ABBREV_TAC`new_repl_fun_state = X:repl_fun_state` >>
  first_x_assum(qspecl_then[`new_repl_state`,`new_bc_state`,`new_repl_fun_state`]mp_tac) >>
  simp[lexer_correct] >>
  discharge_hyps >- (

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
  `FV_top top ⊆ set (MAP (Short o FST) rs.envE) ∪ menv_dom rs.envM ∧
   top_cns top ⊆ cenv_dom rs.envC`
              by (fs[closed_top_def] >> metis_tac [type_sound_inv_closed]) >>
  qspecl_then[`rs.envM`,`rs.envC`,`rs.store`,`rs.envE`,`top`,`store2`,`envC2`,`Rerr (Rraise err)`]mp_tac evaluate_top_closed_context >>
  simp[] >> strip_tac >>
  conj_tac >- (
    simp[Abbr`new_repl_state`,update_repl_state_def] >>
    match_mp_tac closed_context_strip_mod_env >>
    imp_res_tac evaluate_top_to_cenv >> fs[] >>
    conj_tac >- metis_tac[closed_context_extend_cenv,APPEND_ASSOC] >>
    fs[convert_menv_def,MAP_MAP_o,combinTheory.o_DEF,LAMBDA_PROD,miscTheory.FST_pair] >>
    fs [type_sound_invariants_def, update_type_sound_inv_def, strip_mod_env_def] >>
    metis_tac [consistent_mod_env_dup_modules]) >>
  conj_tac >- (
    fs[Abbr`new_repl_state`,update_repl_state_def,Abbr`new_bc_state`] >>
    simp[Abbr`new_repl_fun_state`] >>
    qexists_tac`rd2` >>
    qexists_tac`ARB` >>
    match_mp_tac env_rs_with_bs_irr >>
    qexists_tac`bs2 with <|stack := bs0.stack; clock := NONE|>` >>
    simp[] >>
    imp_res_tac RTC_bc_next_preserves >>
    simp[] >>
    match_mp_tac env_rs_remove_clock >>
    simp[] >>
    qexists_tac`0,store2` >>
    qexists_tac`bs2 with stack := bs0.stack` >>
    simp[] >>
    Cases_on`top`>>fs[]>-(
      rator_x_assum`env_rs`mp_tac >>
      Q.PAT_ABBREV_TAC`menv1 = xx::rs.envM` >>
      Q.PAT_ABBREV_TAC`menv2 = yy++rs.envM` >>
      `menv1 = menv2` by (
        simp[Abbr`menv1`,Abbr`menv2`] >>
        simp[convert_menv_def,strip_mod_env_def] >>
        qpat_assum`A = (Success Y,Z)`mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[inferTheory.infer_top_def] >>
        EVAL_TAC >> rw[] >>
        BasicProvers.EVERY_CASE_TAC >>
        fs[UNCURRY] >>
        BasicProvers.EVERY_CASE_TAC >>
        fs[] >> rw[] ) >>
      simp[] ) >>
    `new_infer_menv = []` by (
      qpat_assum`A = (Success Y,Z)`mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[inferTheory.infer_top_def] >>
      EVAL_TAC >> rw[] >>
      BasicProvers.EVERY_CASE_TAC >>
      fs[UNCURRY]) >>
    simp[convert_menv_def,strip_mod_env_def]) >>
  conj_tac >- labels_tac >>
  simp[Abbr`new_bc_state`] >>
  imp_res_tac RTC_bc_next_preserves >>
  fs[] >>
  conj_tac >- (
    match_mp_tac bytecodeLabelsTheory.code_labels_ok_append >> simp[] >>
    conj_tac >- rfs[] >>
    ctac >> simp[]) >>
  simp[code_executes_ok_def] >>
  disj1_tac >>
  qexists_tac`bs3 with clock := NONE` >>
  simp[bc_fetch_with_clock] ) >>
simp[]);

val _ = delete_const"and_shadow"

  (*
val good_compile_primitives = prove(
  ``good_contab (FST compile_primitives).contab ∧
    good_cmap [] (cmap (FST compile_primitives).contab) ∧
    {} = FDOM (cmap (FST compile_primitives).contab)
    ``,
  rw[compile_primitives_def, initial_program_def] >>
  rw[CompilerTheory.compile_top_def,CompilerTheory.compile_dec_def] >>
  (* need to update for new compiler interface *)
  imp_res_tac compile_fake_exp_contab >>
  rw[good_contab_def,intLangExtraTheory.good_cmap_def] >>
  rw[CompilerTheory.init_compiler_state_def,good_contab_def] >>
  rw[IntLangTheory.tuple_cn_def,IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def, IntLangTheory.eq_exc_cn_def] >>
  rw[toIntLangProofsTheory.cmap_linv_def,FAPPLY_FUPDATE_THM] >>
  fs[CompilerTheory.compile_top_def,CompilerTheory.compile_dec_def,LET_THM,UNCURRY,FST_compile_fake_exp_contab] >>
  fs[CompilerTheory.init_compiler_state_def,FLOOKUP_UPDATE])

val compile_primitives_menv = store_thm("compile_primitives_menv",
  ``(FST compile_primitives).rmenv = FEMPTY``,
  rw[compile_primitives_def,CompilerTheory.compile_top_def, initial_program_def] >>
  rw[CompilerTheory.init_compiler_state_def])

val compile_primitives_renv = store_thm("compile_primitives_renv",
  ``((FST compile_primitives).renv = GENLIST (λi. (FST(EL i init_env), i)) (LENGTH init_env)) ∧
    ((FST compile_primitives).rsz = LENGTH init_env)``,
  rw[compile_primitives_def,CompilerTheory.compile_top_def, initial_program_def] >>
  rw[CompilerTheory.init_compiler_state_def] >>
  fs[CompilerTheory.compile_dec_def,LET_THM] >>
  fs[CompilerTheory.compile_fake_exp_def,LET_THM] >>
  rw[CompilerTheory.init_compiler_state_def] >>
  rw[LIST_EQ_REWRITE,init_env_def] >>
  `x ∈ count 13` by rw[] >>
  pop_assum mp_tac >> EVAL_TAC >>
  rw[] >> simp[])
  *)

(* Annoying to do this by hand.  With the clocked evaluate, it shouldn't be
 * too hard to set up a clocked interpreter function for the semantics and
 * do this automatically *)
val eval_initial_program = Q.prove (
`evaluate_dec NONE [] [] [] [] initial_program ([], Rval ([], init_env))`,
rw [init_env_def, initial_program_def, evaluate_dec_cases, LibTheory.emp_def, pmatch_def] >>
NTAC 15 (rw [Once evaluate_cases]) >>
srw_tac[DNF_ss][] >>
rw [do_con_check_def, AstTheory.pat_bindings_def, pmatch_def, LibTheory.bind_def] >>
simp[ADD1] >> rw[Once evaluate_cases] >>
rw [do_con_check_def, AstTheory.pat_bindings_def, pmatch_def, LibTheory.bind_def]);

val compile_primitives_terminates = store_thm("compile_primitives_terminates",
  ``bc_eval (install_code [] (SND(SND compile_primitives)) (^(rand(rhs(concl(initial_bc_state_def)))))) = SOME initial_bc_state ∧
      initial_bc_state.pc = next_addr initial_bc_state.inst_length initial_bc_state.code ∧
      initial_bc_state.stack ≠ [] ∧
      ∃rd. env_rs [] [] init_env (FST compile_primitives) (LENGTH initial_bc_state.stack) rd (0,[]) initial_bc_state``,
  qho_match_abbrev_tac`bc_eval bs = SOME bs1i ∧ P` >>
  `evaluate_top [] [] [] [] (Tdec initial_program) ([],[],Rval ([],init_env))`
        by (rw [evaluate_top_cases, LibTheory.emp_def] >>
            metis_tac [eval_initial_program]) >>
  qspecl_then[`[]`,`[]`,`[]`,`[]`,`Tdec initial_program`,`([],[],Rval ([],init_env))`]mp_tac compile_top_thm >>
  simp[] >>
  simp[closed_top_def,closed_context_def,toIntLangProofsTheory.closed_under_cenv_def,closed_under_menv_def] >>
  `FV_dec initial_program = {}`
          by (rw [initial_program_def, EXTENSION] >> metis_tac []) >>
  `dec_cns initial_program ⊆ cenv_dom ([]:envC)`
          by (rw [initial_program_def, cenv_dom_def, SUBSET_DEF]) >>
  fs [] >>
  disch_then(qspec_then`init_compiler_state`mp_tac) >>
  disch_then(qx_choosel_then[`ck`]mp_tac) >>
  qabbrev_tac`p = compile_top init_compiler_state (Tdec initial_program)` >>
  PairCases_on`p`>>simp[] >>
  disch_then(qspecl_then
    [`<|sm:=[];cls:=FEMPTY|>`
    ,`^(rand(rhs(concl(initial_bc_state_def)))) with
      <| pc := next_addr (K 0) (PrintE++[Stop])
       ; clock := SOME ck
       ; code := PrintE++[Stop]++(REVERSE p2)|>`
    ,`PrintE++[Stop]`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    assume_tac PrintE_labels >>
    fs[good_labels_def] >>
    conj_tac >- (
      match_mp_tac env_rs_empty >>
      simp[] ) >>
    fsrw_tac[][FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    simp[CompilerTheory.init_compiler_state_def] ) >>
  disch_then(qx_choosel_then[`bs1`,`rd`]strip_assume_tac) >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  pop_assum mp_tac >>
  qpat_assum`bc_next^* X bs`kall_tac >>
  strip_tac >>
  imp_res_tac RTC_bc_next_bc_eval >>
  qmatch_assum_abbrev_tac`bc_next^* bs3 bs2` >>
  `bs3 = bs` by (
    simp[Abbr`bs3`,Abbr`bs`,bc_state_component_equality] >>
    simp[install_code_def] >>
    simp[compile_primitives_def] ) >>
  fs[] >>
  `∀s3. ¬bc_next bs2 s3` by (
    simp[bc_eval1_thm] >>
    `bc_fetch bs2 = NONE` by (
      simp[bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      simp[Abbr`bs2`] >>
      imp_res_tac RTC_bc_next_preserves >>
      fs[] >>
      simp[Abbr`bs`,SUM_APPEND,FILTER_APPEND,FILTER_REVERSE,SUM_REVERSE,MAP_REVERSE] ) >>
    simp[bc_eval1_def] ) >>
  fs[] >>
  conj_asm1_tac >- simp[Abbr`bs1i`,initial_bc_state_def] >>
  simp[Abbr`P`] >>
  pop_assum(assume_tac o SYM) >>
  simp[] >>
  conj_tac >- (
    simp[Abbr`bs2`] >>
    imp_res_tac RTC_bc_next_preserves >>
    fs[Abbr`bs`] >>
    simp[SUM_APPEND,FILTER_APPEND,SUM_REVERSE,FILTER_REVERSE,MAP_REVERSE] ) >>
  conj_tac >- (
    simp[Abbr`bs2`] >>
    fs[env_rs_def,LET_THM] >>
    fs[toBytecodeProofsTheory.Cenv_bs_def,toBytecodeProofsTheory.env_renv_def] >>
    fs[EVERY2_EVERY,pmatchTheory.env_to_Cenv_MAP] >>
    simp[GSYM LENGTH_NIL] >>
    spose_not_then strip_assume_tac >> fs[] >>
    fs[LENGTH_NIL] >> rfs[] >> fs[] >>
    fs[init_env_def] ) >>
  qexists_tac`rd` >>
  simp[compile_primitives_def] >>
  match_mp_tac env_rs_remove_clock >>
  simp[EXISTS_PROD] >>
  qexists_tac`0` >>
  qexists_tac`bs1` >>
  simp[] >>
  simp[Abbr`bs2`] )

val initial_bc_state_invariant = store_thm("initial_bc_state_invariant",
  ``(initial_bc_state.inst_length = K 0) ∧
    good_labels (FST compile_primitives).rnext_label initial_bc_state.code ∧
    (initial_bc_state.clock = NONE) ∧
    (∃ls. initial_bc_state.code = PrintE++Stop::ls) ∧
    code_labels_ok initial_bc_state.code ∧
    code_executes_ok initial_bc_state
    ``,
  simp[initial_bc_state_def] >>
  Q.PAT_ABBREV_TAC`bs = install_code X Y Z` >>
  `∃bs1. bc_eval bs = SOME bs1` by (
    assume_tac compile_primitives_terminates >>
    fs[Abbr`bs`] ) >>
  simp[] >>
  imp_res_tac bc_eval_SOME_RTC_bc_next >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_preserves >>
  imp_res_tac bytecodeExtraTheory.RTC_bc_next_clock_less >>
  `bs1.clock = NONE` by rfs[optionTheory.OPTREL_def,Abbr`bs`,install_code_def] >>
  simp[Abbr`bs`,install_code_def] >>
  qspecl_then[`init_compiler_state`]mp_tac compile_top_append_code >>
  disch_then(mp_tac o SPEC(rand(rhs(concl(compile_primitives_def))))) >>
  discharge_hyps >- (
    simp[] >>
    simp[CompilerTheory.init_compiler_state_def, initial_program_def] >>
    simp[EXTENSION] >>
    metis_tac[] ) >>
  simp[GSYM compile_primitives_def, initial_program_def] >>
  simp[good_labels_def,between_labels_def] >>
  strip_tac >>
  assume_tac PrintE_labels >>
  fs[good_labels_def] >>
  conj_asm1_tac >- (
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,miscTheory.between_def,MEM_MAP,FILTER_REVERSE,ALL_DISTINCT_REVERSE,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> fs[CompilerTheory.init_compiler_state_def] >> DECIDE_TAC) >>
  cheat (* code_labels_ok and code_executes_ok for initial code *))

val initial_invariant = prove(
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  rw[invariant_def,initial_repl_fun_state_def,initial_elaborator_state_def,init_repl_state_def,LET_THM] >>
  rw[initial_inferencer_state_def,initial_bc_state_invariant]
  >- EVAL_TAC
  >- simp[typeSoundTheory.initial_type_sound_invariant]
  >- (
    simp[closed_context_def] >>
    simp[init_env_def,semanticsExtraTheory.closed_cases] >>
    simp[init_env_def,toIntLangProofsTheory.closed_under_cenv_def] >>
    simp[init_env_def,compilerProofsTheory.closed_under_menv_def] >>
    simp[semanticsExtraTheory.closed_cases] >>
    rw[] >> rw[semanticsExtraTheory.all_cns_def] >>
    simp[SUBSET_DEF] >> metis_tac[] ) >>
  TRY (assume_tac initial_bc_state_invariant >> fs[] >> NO_TAC) >>
  TRY (metis_tac[compile_primitives_terminates]))

val initial_bc_state_side_thm = store_thm("initial_bc_state_side_thm",
  ``initial_bc_state_side``,
  REWRITE_TAC[initial_bc_state_side_def] >>
  Q.PAT_ABBREV_TAC`A = $/\` >>
  rw[] >> simp[Abbr`A`] >>
  assume_tac compile_primitives_terminates >>
  rfs[] >>
  fs[Abbr`bs3`] >>
  simp[GSYM CONJ_ASSOC] >>
  conj_asm1_tac >- (
    simp[Abbr`bs4`] >>
    imp_res_tac bc_eval_SOME_RTC_bc_next >>
    imp_res_tac RTC_bc_next_preserves >>
    simp[Abbr`bs2`,install_code_def]) >>
  simp[Abbr`bs4`])

(*
val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
match_mp_tac replCorrect_lem >>
rw[initial_invariant])
*)

val replCorrect' = Q.store_thm ("replCorrect'",
`!input output b.
  (repl_fun' input = (output,b)) ⇒
  (repl (get_type_error_mask output) input output) /\ b`,
rpt gen_tac >> simp [repl_fun'_def, repl_def,UNCURRY] >>
strip_tac >>
fs[initial_bc_state_side_thm] >>
rpt BasicProvers.VAR_EQ_TAC >>
match_mp_tac replCorrect'_lem >>
simp[initial_invariant])

val replCorrect_thm = Q.store_thm ("replCorrect_thm",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
metis_tac [replCorrect',repl_fun'_thm,PAIR])

val _ = export_theory ();
