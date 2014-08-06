open preamble boolSimps miscLib rich_listTheory arithmeticTheory;
open lexer_funTheory repl_funTheory replTheory untypedSafetyTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory
open lexer_implTheory cmlParseTheory inferSoundTheory bigStepTheory compilerProofTheory;
open semanticPrimitivesTheory typeSystemTheory typeSoundTheory weakeningTheory evalPropsTheory typeSysPropsTheory terminationTheory;
open initSemEnvTheory interpTheory;
open typeSoundInvariantsTheory inferTheory free_varsTheory;
open bytecodeTheory;
open gramPropsTheory pegSoundTheory pegCompleteTheory;
open repl_fun_alt_proofTheory initialProgramTheory initCompEnvTheory;

val _ = new_theory "replCorrect";

val _ = ParseExtras.temp_tight_equality ();

(* TODO: move *)
val o_f_FUNION = store_thm("o_f_FUNION",
  ``f o_f (f1 ⊌ f2) = (f o_f f1) ⊌ (f o_f f2)``,
  simp[GSYM fmap_EQ_THM,FUNION_DEF] >>
  rw[o_f_FAPPLY]);

val type_env_list_rel = Q.prove (
`!ctMap tenvS env tenv.
  type_env ctMap tenvS env (bind_var_list2 tenv Empty) ⇔ LIST_REL (λ(x,v1) (y,n,v2). x = y ∧ type_v n ctMap tenvS v1 v2) env tenv`,
 induct_on `env` >>
 rw [] >>
 cases_on `tenv` >>
 rw [bind_var_list2_def] >>
 ONCE_REWRITE_TAC [hd (tl (tl (CONJUNCTS type_v_cases)))] >>
 rw [libTheory.emp_def, bind_var_list2_def, libTheory.bind_def] >>
 PairCases_on `h` >>
 fs [bind_var_list2_def, bind_tenv_def] >>
 PairCases_on `h'` >>
 fs [bind_var_list2_def, bind_tenv_def] >>
 metis_tac []);

val type_env_list_rel_append = Q.prove (
`!ctMap tenvS env tenv rest rst.
  type_env ctMap tenvS (env ++ rest) (bind_var_list2 tenv rst) ∧ LENGTH env = LENGTH tenv
    ⇒ LIST_REL (λ(x,v1) (y,n,v2). x = y ∧ type_v n ctMap tenvS v1 v2) env tenv`,
 induct_on `env` >>
 rw [LENGTH_NIL_SYM] >>
 cases_on `tenv` >> fs[] >>
 PairCases_on`h'` >>
 fs [bind_var_list2_def] >>
 PairCases_on`h`>>simp[] >>
 rator_x_assum`type_env`mp_tac >>
 simp[Once type_v_cases,libTheory.emp_def,libTheory.bind_def] >>
 rw[bind_tenv_def] >>
 metis_tac[])

val bind_var_list2_append = prove(
  ``∀l1 l2 g. bind_var_list2 (l1 ++ l2) g = bind_var_list2 l1 (bind_var_list2 l2 g)``,
  Induct >> simp[bind_var_list2_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[bind_var_list2_def])

val type_env_length = prove(
  ``∀d a b c e f g h.
    type_env a b (c ++ d) (bind_var_list2 e f) ∧
    type_env g h d f ⇒
    LENGTH c = LENGTH e``,
  Induct >> simp[] >- (
    rw[] >>
    pop_assum mp_tac >>
    simp[Once type_v_cases,libTheory.bind_def] >>
    rw[] >>
    imp_res_tac type_env_list_rel >>
    fs[LIST_REL_EL_EQN] ) >>
  rw[] >>
  pop_assum mp_tac >>
  simp[Once type_v_cases,libTheory.bind_def,libTheory.emp_def] >>
  rw[] >>
  qsuff_tac`LENGTH (c ++ [n,v]) = LENGTH (e++[n,tvs,t])` >- simp[] >>
  first_x_assum match_mp_tac >>
  simp[bind_var_list2_append,bind_var_list2_def] >>
  metis_tac[CONS_APPEND,APPEND_ASSOC])

val fst_lem = Q.prove (
`FST = λ(x,y). x`,
rw [FUN_EQ_THM] >>
PairCases_on `x` >>
fs []);

val union_append_decls = Q.prove (
`union_decls (convert_decls new_decls) (convert_decls decls) = convert_decls (append_decls new_decls decls)`,
 PairCases_on `new_decls` >>
 PairCases_on `decls` >>
 rw [append_decls_def, union_decls_def, convert_decls_def]);

val FV_pes_MAP = store_thm("FV_pes_MAP",
  ``FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes))``,
  Induct_on`pes`>>simp[]>>
  qx_gen_tac`p`>>PairCases_on`p`>>rw[])

val lex_impl_all_def = tDefine "lex_impl_all" `
lex_impl_all input =
  case lex_until_toplevel_semicolon input of
    | NONE => []
    | SOME (t,input') => t::lex_impl_all input'`
(wf_rel_tac `measure LENGTH` >>
 rw [] >>
 metis_tac [lex_until_toplevel_semicolon_LESS]);

val lex_aux_tokens_def = Define `
  lex_aux_tokens acc (d:num) input =
     case input of
       [] => NONE
     | token::rest =>
         let new_acc = token::acc in
           if token = SemicolonT /\ (d = 0) then
             SOME (REVERSE (new_acc),rest)
           else
             if token = LetT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = StructT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = SigT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = LparT then
               lex_aux_tokens new_acc (d+1) rest
             else if token = EndT then
               lex_aux_tokens new_acc (d-1) rest
             else if token = RparT then
               lex_aux_tokens new_acc (d-1) rest
             else lex_aux_tokens new_acc d rest`

val lex_until_toplevel_semicolon_tokens_def = Define `
  lex_until_toplevel_semicolon_tokens input = lex_aux_tokens [] 0 input`;

val lex_aux_tokens_LESS = prove(
  ``!acc d input.
      (lex_aux_tokens acc d input = SOME (t,rest)) ==>
      (if acc = [] then LENGTH rest < LENGTH input
                   else LENGTH rest <= LENGTH input)``,
  Induct_on `input`
  THEN1 (EVAL_TAC >> SRW_TAC [] [LENGTH] >> SRW_TAC [] [LENGTH])
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def,LET_DEF]
  >> SRW_TAC [] [] >> RES_TAC
  >> FULL_SIMP_TAC std_ss [NOT_CONS_NIL]
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
  ``!input acc d res1 res2.
      (lex_aux_tokens acc d (lexer_fun input) = res1) /\
      (lex_aux acc d input = res2) ==>
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
  >> SRW_TAC [] [] >> SRW_TAC [] []
  >> ASM_SIMP_TAC std_ss [GSYM lexer_fun_def]) |> SIMP_RULE std_ss [];

val lex_impl_all_tokens_thm = prove(
  ``!input. lex_impl_all input =
            lex_impl_all_tokens (lexer_fun input)``,
  HO_MATCH_MP_TAC (fetch "-" "lex_impl_all_ind") >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once lex_impl_all_def,Once lex_impl_all_tokens_def]
  >> FULL_SIMP_TAC std_ss [lex_until_toplevel_semicolon_tokens_def]
  >> FULL_SIMP_TAC std_ss [lex_until_toplevel_semicolon_def]
  >> MP_TAC (lex_aux_tokens_thm |> Q.SPECL [`input`,`[]`,`0`])
  >> Cases_on `lex_aux [] 0 input` >> FULL_SIMP_TAC std_ss []
  >> Cases_on `x` >> FULL_SIMP_TAC (srw_ss()) []
  >> REPEAT STRIP_TAC >> RES_TAC);

val lex_aux_tokens_thm = prove(
  ``!input d acc.
      (res = lex_aux_tokens acc d input) ==>
      case res of
        NONE => (toplevel_semi_dex (LENGTH acc) d input = NONE)
      | SOME (toks,rest) =>
          (toplevel_semi_dex (LENGTH acc) d input = SOME (LENGTH toks)) /\
          (REVERSE acc ++ input = toks ++ rest)``,
  Induct
  >> SIMP_TAC (srw_ss()) [Once lex_aux_tokens_def]
  >> ONCE_REWRITE_TAC [toplevel_semi_dex_def]
  >> SIMP_TAC std_ss [LET_DEF] >> Cases
  >> FULL_SIMP_TAC (srw_ss()) []
  >> REPEAT STRIP_TAC >> RES_TAC
  >> POP_ASSUM MP_TAC
  >> POP_ASSUM (ASSUME_TAC o GSYM)
  >> ASM_REWRITE_TAC []
  >> Cases_on `res` >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> Cases_on `d = 0` >> ASM_SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> TRY (Cases_on `x`) >> SIMP_TAC (srw_ss()) [arithmeticTheory.ADD1]
  >> SIMP_TAC std_ss [Once EQ_SYM_EQ]
  >> FULL_SIMP_TAC std_ss []
  >> REPEAT STRIP_TAC >> RES_TAC
  >> FULL_SIMP_TAC (srw_ss()) [LENGTH,arithmeticTheory.ADD1])
  |> Q.SPECL [`input`,`0`,`[]`] |> Q.GEN `res` |> SIMP_RULE std_ss [LENGTH];

val split_top_level_semi_thm = prove(
  ``!input. split_top_level_semi input = lex_impl_all_tokens input``,
  HO_MATCH_MP_TAC split_top_level_semi_ind >> REPEAT STRIP_TAC
  >> SIMP_TAC std_ss [Once split_top_level_semi_def,Once lex_impl_all_tokens_def,
      Once lex_until_toplevel_semicolon_tokens_def]
  >> MP_TAC lex_aux_tokens_thm
  >> Cases_on `lex_aux_tokens [] 0 input` >> FULL_SIMP_TAC std_ss []
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
 fs [convert_decls_def, convert_menv_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, fst_lem]);

val invariant_def = Define`
  invariant rs rfs bs ⇔
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

val infer_to_type = Q.prove (
`!rs st bs decls menv cenv env top new_decls new_menv new_cenv new_env st2.
  invariant rs st bs ∧
  (infer_top decls tenvT menv cenv env top init_infer_state =
      (Success (new_decls,new_tenvT,new_menv,new_cenv,new_env),st2)) ∧
  (st.rinferencer_state = (decls,tenvT,menv,cenv,env))
  ⇒
  infer_sound_invariant (merge_tenvT new_tenvT tenvT) (new_menv ++ menv) (merge_tenvC new_cenv cenv) (new_env++env) ∧
  type_top rs.tdecs rs.tenvT rs.tenvM rs.tenvC rs.tenv top
           (convert_decls new_decls) new_tenvT (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
 rw [invariant_def, type_infer_invariants_def, type_sound_invariants_def] >>
 fs [] >>
 rw [] >>
 metis_tac [infer_top_sound, infer_sound_invariant_def]);

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

val tenv_names_bind_var_list2 = store_thm("tenv_names_bind_var_list2",
  ``∀l1 tenv. tenv_names (bind_var_list2 l1 tenv) = set (MAP FST l1) ∪ tenv_names tenv``,
  Induct >> TRY(qx_gen_tac`p`>>PairCases_on`p`) >> simp[bind_var_list2_def,bind_tenv_def] >>
  simp[EXTENSION] >> metis_tac[])

val _ = Parse.overload_on("tmenv_dom",``λmenv:tenvM. {Long m x | (m,x) | ∃e. lookup m menv = SOME e ∧ MEM x (MAP FST e)}``);

val type_p_closed = store_thm("type_p_closed",
  ``(∀tvs tcenv p t tenv.
       type_p tvs tcenv p t tenv ⇒
       pat_bindings p [] = MAP FST tenv) ∧
    (∀tvs cenv ps ts tenv.
      type_ps tvs cenv ps ts tenv ⇒
      pats_bindings ps [] = MAP FST tenv)``,
  ho_match_mp_tac type_p_ind >>
  simp[astTheory.pat_bindings_def] >>
  rw[] >> fs[SUBSET_DEF] >>
  rw [Once pat_bindings_accum]);

val type_funs_dom = Q.prove (
`!tenvM tenvC tenv funs tenv'.
  type_funs tenvM tenvC tenv funs tenv'
  ⇒
  IMAGE FST (set funs) = IMAGE FST (set tenv')`,
 induct_on `funs` >>
 rw [Once type_e_cases] >>
 rw [] >>
 metis_tac []);

val type_e_closed = store_thm("type_e_closed",
  ``(∀tmenv tcenv tenv e t.
      type_e tmenv tcenv tenv e t
      ⇒
      FV e ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)) ∧
    (∀tmenv tcenv tenv es ts.
      type_es tmenv tcenv tenv es ts
      ⇒
      FV_list es ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)) ∧
    (∀tmenv tcenv tenv funs ts.
      type_funs tmenv tcenv tenv funs ts ⇒
      FV_defs funs ⊆ (IMAGE Short (tenv_names tenv)) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_e_strongind >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
    simp_tac(srw_ss()++DNF_ss)[SUBSET_DEF,UNCURRY,FORALL_PROD,MEM_MAP] >>
    rw[] >> res_tac >>
    qmatch_assum_rename_tac`MEM (p1,p2) pes`[] >>
    first_x_assum(qspecl_then[`p1`,`p2`]mp_tac) >>
    simp[EXISTS_PROD] >> disch_then(Q.X_CHOOSE_THEN`tv`strip_assume_tac) >>
    imp_res_tac type_p_closed >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,EXISTS_PROD,FORALL_PROD] >> metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac alistTheory.ALOOKUP_MEM >>
    simp[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[t_lookup_var_id_def] >>
    rpt gen_tac >>
    BasicProvers.CASE_TAC >> fs[] >>
    simp[MEM_FLAT,MEM_MAP,EXISTS_PROD] >-
      metis_tac[lookup_tenv_names] >>
    BasicProvers.CASE_TAC >> fs[] >> 
    simp_tac(srw_ss()++DNF_ss)[MEM_MAP,EXISTS_PROD] >>
    rw [] >>
    imp_res_tac libPropsTheory.lookup_in3 >>
    metis_tac [] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- (
    simp[RES_FORALL_THM,FORALL_PROD,tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    simp[FV_pes_MAP] >>
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
    every_case_tac >>
    fs [opt_bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[] >>
    srw_tac[DNF_ss][SUBSET_DEF,bind_tvar_def,bind_tenv_def] >>
    every_case_tac >>
    fs [opt_bind_tenv_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[tenv_names_bind_var_list] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac type_funs_dom >>
    fs [SUBSET_DEF] >>
    rw [] >>
    res_tac >>
    fs [MEM_MAP] >>
    `tenv_names (bind_tvar tvs tenv) = tenv_names tenv` 
               by (rw [bind_tvar_def] >>
                   every_case_tac >>
                   fs [tenv_names_def]) >>
    fs [] >>
    rw [] >>
    res_tac >>
    fs [] >>
    rw [] >>
    fs [EXTENSION] >>
    metis_tac []) >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  strip_tac >- simp[] >>
  simp[] >>
  rw [SUBSET_DEF,bind_tenv_def] >>
  res_tac >>
  fsrw_tac[DNF_ss][MEM_MAP,FV_defs_MAP,UNCURRY] >>
  rw [] >>
  metis_tac []);

val type_d_closed = store_thm("type_d_closed",
  ``∀mno decls tenvT tmenv tcenv tenv d w x y z.
      type_d mno decls tenvT tmenv tcenv tenv d w x y z ⇒
        FV_dec d ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_d_ind >>
  strip_tac >- (
    simp[bind_tvar_def] >>
    rpt gen_tac >>
    Cases_on`tvs=0`>>simp[]>>strip_tac>>
    imp_res_tac (CONJUNCT1 type_e_closed) >> fs[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    imp_res_tac (CONJUNCT1 type_e_closed) >> fs[]) >>
  strip_tac >- (
    rw [] >>
    imp_res_tac (CONJUNCT2 type_e_closed) >>
    fs[tenv_names_bind_var_list,LET_THM] >>
    `tenv_names (bind_tvar tvs tenv) = tenv_names tenv`
              by (rw [bind_tvar_def] >>
                  every_case_tac >>
                  rw [tenv_names_def]) >>
    fs[SUBSET_DEF] >> 
    rw [] >>
    fs [MEM_MAP] >>
    res_tac >>
    rw [] >>
    imp_res_tac type_funs_dom >>
    fs [EXTENSION] >>
    metis_tac[]) >>
  simp[]);

val type_d_new_dec_vs = Q.prove (
`!mn decls tenvT tenvM tenvC tenv d decls' tenvT' tenvC' tenv'.
  type_d mn decls tenvT tenvM tenvC tenv d decls' tenvT' tenvC' tenv'
  ⇒
  set (new_dec_vs d) = set (MAP FST tenv')`,
 rw [type_d_cases, new_dec_vs_def, libTheory.emp_def] >>
 rw [new_dec_vs_def] >>
 imp_res_tac type_p_closed >>
 rw [tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
 fs [LET_THM, LIST_TO_SET_MAP, GSYM fst_lem, IMAGE_COMPOSE] >>
 metis_tac [type_funs_dom]);

(*
val new_top_vs_inf_tenv_to_string_map_lem = Q.prove (
`!decls tenvM tenvC tenv top decls' tenvM' tenvC' tenv'.
  type_top decls tenvM tenvC tenv top decls' tenvM' tenvC' (convert_env2 tenv')
  ⇒
  set (new_top_vs top) ⊆ FDOM (inf_tenv_to_string_map tenv')`,
 rw [] >>
 cases_on `top` >>
 fs [printingTheory.new_top_vs_def, type_top_cases] >>
 imp_res_tac type_d_new_dec_vs >>
 rw [convert_env2_def, MAP_MAP_o, combinTheory.o_DEF] >>
 rpt (pop_assum (fn _ => all_tac)) >>
 induct_on `tenv'` >>
 rw [inf_tenv_to_string_map_def] >>
 PairCases_on `h` >>
 rw [inf_tenv_to_string_map_def, SUBSET_INSERT_RIGHT]);
*)

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
    fs [] >-
    metis_tac [] >-
    metis_tac [] >-
    metis_tac [] >-
    metis_tac [] >-
    metis_tac [] >-
    metis_tac [] >-
    metis_tac [] >-
    metis_tac [] >-
    (cases_on `t` >>
       fs [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
       cases_on `t'` >>
       fs [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
       metis_tac []) >-
    metis_tac [] >-
    metis_tac []) >-
 metis_tac [] >-
 metis_tac [] >>
 cases_on `ts` >>
 rw [inf_type_to_string_def, type_to_string_def, convert_t_def] >>
 fs [EVERY_DEF] >>
 metis_tac []);

(*
val to_string_map_lem = Q.prove (
`!env. check_env {} env ⇒ (inf_tenv_to_string_map env = tenv_to_string_map (convert_env2 env))`,
 induct_on `env` >>
 rw [check_env_def, inf_tenv_to_string_map_def, tenv_to_string_map_def, convert_env2_def] >>
 PairCases_on `h` >>
 rw [inf_tenv_to_string_map_def, tenv_to_string_map_def] >>
 fs [check_env_def, convert_env2_def] >>
 metis_tac [type_to_string_lem]);
*)

val type_ds_closed = store_thm("type_ds_closed",
  ``∀mn decls tenvT tmenv cenv tenv ds w x y z. type_ds mn decls tenvT tmenv cenv tenv ds w x y z ⇒
     !mn'. mn = SOME mn' ⇒
      FV_decs ds ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)``,
ho_match_mp_tac type_ds_ind >>
rw [FV_decs_def] >>
imp_res_tac type_d_closed >>
fs [tenv_names_bind_var_list2] >>
rw [SUBSET_DEF] >>
`x ∈ IMAGE Short (set (MAP FST tenv')) ∪ IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv`
         by fs [SUBSET_DEF] >>
fs [] >>
rw [] >>
fs[MEM_MAP] >>
metis_tac [type_d_new_dec_vs,MEM_MAP]);

val type_top_closed = store_thm("type_top_closed",
  ``∀decls tenvT tmenv tcenv tenv top decls' tT' tm' tc' te'.
      type_top decls tenvT tmenv tcenv tenv top decls' tT' tm' tc' te'
      ⇒
      FV_top top ⊆ (IMAGE Short (tenv_names tenv) ∪ tmenv_dom tmenv)``,
  ho_match_mp_tac type_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    metis_tac [type_d_closed]) >>
  simp[] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac type_ds_closed >>
  fs[])

val type_env_dom = Q.prove (
`!ctMap tenvS env tenv.
  type_env ctMap tenvS env tenv ⇒
  IMAGE Short (set (MAP FST env)) = IMAGE Short (tenv_names tenv)`,
 induct_on `env` >>
 ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
 fs [libTheory.emp_def, tenv_names_def] >>
 fs [bind_tenv_def, libTheory.bind_def, tenv_names_def] >>
 rw [] >>
 rw [] >>
 metis_tac []);

val weakM_dom = Q.prove (
`!tenvM1 tenvM2.
  weakM tenvM1 tenvM2
  ⇒
  tmenv_dom tenvM2 ⊆ tmenv_dom tenvM1`,
 rw [weakM_def, SUBSET_DEF] >>
 res_tac >>
 rw [] >>
 fs [weakE_def] >>
 qpat_assum `!x. P x` (mp_tac o Q.SPEC `x'`) >>
 every_case_tac >>
 fs [] >>
 imp_res_tac libPropsTheory.lookup_notin >>
 rw [] >>
 imp_res_tac libPropsTheory.lookup_in2); 

val type_env_dom2 = Q.prove (
`!ctMap tenvS env tenv.
  type_env ctMap tenvS env (bind_var_list2 tenv Empty) ⇒
  (set (MAP FST env) = set (MAP FST tenv))`,
 induct_on `env` >>
 ONCE_REWRITE_TAC [typeSoundInvariantsTheory.type_v_cases] >>
 fs [bind_var_list2_def, libTheory.emp_def, tenv_names_def] >>
 fs [bind_tenv_def, libTheory.bind_def, tenv_names_def] >>
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
  (tmenv_dom tenvM = {Long m x | ∃e. lookup m envM = SOME e ∧ MEM x (MAP FST e)})`,
 induct_on `envM` >>
 rw []
 >- (Cases_on `tenvM` >>
     fs [Once type_v_cases]) >>
 pop_assum (mp_tac o SIMP_RULE (srw_ss()) [Once type_v_cases]) >>
 rw [] >>
 res_tac >>
 rw [] >>
 imp_res_tac type_env_dom2 >>
 fs [EXTENSION] >>
 rw [] >>
 eq_tac >>
 rw [] >>
 every_case_tac >>
 rw [] >>
 fs [MEM_MAP] >>
 rw [] >>
 res_tac >>
 fs [] >>
 metis_tac []);

val type_sound_inv_closed = Q.prove (
`∀top rs new_tenvM new_tenvC new_tenv new_decls decls' store.
  type_top rs.tdecs rs.tenvT rs.tenvM rs.tenvC rs.tenv top new_decls new_tenvT new_tenvM new_tenvC new_tenv ∧
  type_sound_invariants NONE (rs.tdecs,rs.tenvT,rs.tenvM,rs.tenvC,rs.tenv,decls',rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE,store)
  ⇒
  FV_top top ⊆ all_env_dom (rs.sem_env.sem_envM,rs.sem_env.sem_envC,rs.sem_env.sem_envE)`,
rw [] >>
imp_res_tac type_top_closed >>
`(?err. r = Rerr err) ∨ (?menv env. r = Rval (menv,env))`
        by (cases_on `r` >>
            rw [] >>
            PairCases_on `a` >>
            fs [])  >>
fs [all_env_dom_def, type_sound_invariants_def, update_type_sound_inv_def] >>
rw [] >>
imp_res_tac weakM_dom >>
imp_res_tac type_env_dom >>
imp_res_tac (GSYM consistent_mod_env_dom) >>
fs [] >>
fs [SUBSET_DEF] >>
metis_tac []);

(*
val ctac =
  qspecl_then[`inf_tenv_to_string_map new_infer_env`,`st.rcompiler_state`,`top`]mp_tac compile_top_append_code >>
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
  ``good_labels 0 PrintE ∧ EVERY ($~ o is_Label) PrintE``, EVAL_TAC)

val PrintE_thm = store_thm("PrintE_thm",
  ``∀bs bv st.
    bs.code = PrintE
    ∧ bs.pc = 0
    ∧ bs.stack = bv::st
    ∧ can_Print bv
    ⇒
    let bs' = bs with <|pc:=next_addr bs.inst_length bs.code
                       ;stack:=st
                       ;output:=bs.output++("raise "++print_bv bs.cons_names bv++"\n")
                       |> in
    bc_next^* bs bs'``,
  rw[] >>
  qsuff_tac`∃bs1 bs2. bc_next^* bs bs1 ∧ bc_next bs1 bs2 ∧ bc_next bs2 bs'` >-
    metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] >>
  qexists_tac`bs with <|output := bs.output ++ "raise "; pc := next_addr bs.inst_length (BUTLASTN 2 PrintE)|>` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    match_mp_tac MAP_PrintC_thm >>
    rw[bc_state_component_equality] >>
    rw[PrintE_def] >>
    qexists_tac`[]` >>
    rw[] >> EVAL_TAC >> simp[]) >>
  qho_match_abbrev_tac`∃bs2. bc_next bs0 bs2 ∧ P bs2` >>
  `bc_fetch bs0 = SOME Print` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs0`,PrintE_def] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`[PrintC#"\n"]` >> simp[] >> EVAL_TAC >> simp[]) >>
  rw[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,bump_pc_def] >>
  simp[Abbr`P`] >>
  qmatch_abbrev_tac`bc_next bs0 bs1` >>
  `bc_fetch bs0 = SOME(PrintC#"\n")` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs0`,PrintE_def] >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`[]` >> simp[] >> EVAL_TAC >> simp[]) >>
  rw[bc_eval1_thm,bc_eval1_def,Abbr`bs0`,bump_pc_def,Abbr`bs1`] >>
  rw[bc_state_component_equality,Abbr`bs'`] >>
  rw[PrintE_def] >> simp[] >> EVAL_TAC >>simp[] >> simp[IMPLODE_EXPLODE_I])
*)

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
  conj_tac >- (
    qexists_tac`grd'` >>
    match_mp_tac env_rs_change_clock >>
    first_assum(match_exists_tac o concl) >>
    simp[bc_state_component_equality] ) >>
  imp_res_tac RTC_bc_next_preserves >> fs[] >>
  conj_tac >- (
    simp[install_code_def] >>
    match_mp_tac bytecodeLabelsTheory.code_labels_ok_append >>
    fs[] >>
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

val replCorrect'_lem = Q.prove (
`!repl_state bc_state repl_fun_state.
  invariant repl_state repl_fun_state bc_state ⇒
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
  rw[and_shadow_def] >> metis_tac [ast_repl_rules] ) >>
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
 metis_tac [lexer_correct,FST,SND]) >>
rw[parse_infertype_compile_def,parser_correct] >>
qmatch_assum_rename_tac`invariant rs st bs`[] >>
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
        by fs [invariant_def] >>
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
    `∃ck store tdecls. rs.sem_env.sem_store = ((ck,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,invariant_def,SND] >>
    fs[remove_count_def] >>
    spose_not_then strip_assume_tac >> fs[] >>
    fs[invariant_def] >>
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
  fs[invariant_def] >>
  simp[code_executes_ok_def] >>
  disj2_tac >>
  qx_gen_tac`n` >>
  `∃ck store tdecls. rs.sem_env.sem_store = ((ck,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,invariant_def,SND] >>
  fs[remove_count_def] >>
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
  fs[invariant_def] >>
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
  rator_x_assum`invariant`mp_tac >>
  simp[invariant_def] >> strip_tac >>
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
    (*
    reverse conj_tac >- (
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      match_mp_tac to_string_map_lem >>
      fs [infer_sound_invariant_def, check_env_def] ) >>
      *)
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
    simp[invariant_def,update_repl_state_def] >>
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
  (*
  reverse conj_tac >- (
    rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
    match_mp_tac to_string_map_lem >>
    fs [infer_sound_invariant_def, check_env_def] ) >>
    *)
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
  simp[invariant_def,update_repl_state_def] >>
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

val simple_replCorrect = Q.store_thm ("simple_replCorrect",
`!init_bc_code init_repl_state sem_initial input output b.
  initial_bc_state_side init_bc_code ∧
  invariant sem_initial init_repl_state (THE (bc_eval (install_code init_bc_code empty_bc_state))) ∧
  (simple_repl_fun (init_repl_state,init_bc_code) input = (output,b)) ⇒
  (repl sem_initial (get_type_error_mask output) input output) /\ b`,
 rpt gen_tac >>
 simp [simple_repl_fun_def, repl_def, UNCURRY] >>
 strip_tac >>
 rpt BasicProvers.VAR_EQ_TAC >>
 fs [] >>
 match_mp_tac replCorrect'_lem >>
 rw []);

val convert_invariants = Q.prove (
`!se e bs.
   initCompEnv$invariant se e bs 
   ⇒
   invariant <| tdecs := convert_decls (e.inf_mdecls, e.inf_tdecls, e.inf_edecls);
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
 rw [invariant_def, initCompEnvTheory.invariant_def] >>
 rw [convert_decls_def] >>
 rw [GSYM PULL_EXISTS]
 >- fs [type_infer_invariants_def, infer_sound_invariant_def, convert_decls_def]
 >- fs [convert_decls_def]
 >- metis_tac []
 >- (fs [init_code_executes_ok_def, code_executes_ok_def] >>
     metis_tac []));

     (*
val convert_invariants2 = Q.prove (
`!r rf bs.
   invariant r rf bs 
   ⇒ 
   initialProgram$invariant 
             <| sem_envM := r.envM;
                sem_envC := r.envC;
                sem_envE := r.envE;
                sem_s := SND (FST r.store);
                sem_tids := FST (SND r.store);
                sem_mdecls := SND (SND r.store) |>
             <| inf_mdecls := FST (FST rf.rinferencer_state);
                inf_tdecls := FST (SND (FST rf.rinferencer_state));
                inf_edecls := SND (SND (FST rf.rinferencer_state));
                inf_tenvM := FST (SND rf.rinferencer_state);
                inf_tenvC := FST (SND (SND rf.rinferencer_state));
                inf_tenvE := SND (SND (SND rf.rinferencer_state));
                comp_rs := rf.rcompiler_state |>
            bs`,
 rw [invariant_def, initialProgramTheory.invariant_def] >>
 qabbrev_tac `x = rf.rinferencer_state` >>
 PairCases_on `x` >>
 rw [GSYM PULL_EXISTS, infer_sound_invariant_def] >>
 fs [type_infer_invariants_def] >>
 rw [] >>
 fs [convert_decls_def]
 >- metis_tac [] >>
 qabbrev_tac `y = r.store` >>
 PairCases_on `y` >>
 rw [] >>
 PairCases_on `grd` >>
 fs [] >>
 rw [] >>
 MAP_EVERY qexists_tac [`grd0`, `grd1`, `grd2`] >>
 match_mp_tac env_rs_change_clock >>
 MAP_EVERY qexists_tac [`((y0,y1),y2,LIST_TO_SET x0)`, `bs`, `0`, `bs.clock`] >>
 rw [] >>
 cases_on `bs` >>
 rw [] >>
 fs [bc_state_clock_fupd, bc_state_clock]);
 *)

val simple_replCorrect_basis = Q.store_thm ("simple_replCorrect_basis",
`!input.
  let (output,b) = simple_repl_fun basis_state input in
  let e = FST (THE basis_env) in
  let r =
      <| tdecs := convert_decls (e.inf_mdecls, e.inf_tdecls, e.inf_edecls);
         tenvT := e.inf_tenvT;
         tenvM := convert_menv e.inf_tenvM;
         tenvC := e.inf_tenvC;
         tenv := bind_var_list2 (convert_env2 e.inf_tenvE) Empty;
         sem_env := THE basis_sem_env |> in
  (repl r (get_type_error_mask output) input output) /\ b`,
 rpt gen_tac >>
 Cases_on`simple_repl_fun basis_state input` >>
 simp [basis_state_def] >>
 match_mp_tac simple_replCorrect >>
 qexists_tac `SND basis_state` >>
 qexists_tac `FST basis_state` >>
 strip_assume_tac basis_env_inv >>
 fs[basis_state_def,LET_THM] >>
 imp_res_tac add_stop_invariant >>
 imp_res_tac convert_invariants >>
 rw [] >>
 fs [] >>
 rw [basis_state_def,initial_bc_state_side_def] >>
 fs [init_code_executes_ok_def, initCompEnvTheory.invariant_def, env_rs_def, code_executes_ok_def] >>
 `s2 = bs'` by all_tac >>
 rw [] >>
 imp_res_tac bc_eval_SOME_RTC_bc_next >>
 fs [Once RTC_CASES1])

val _ = export_theory ();
