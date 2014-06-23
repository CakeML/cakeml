open preamble boolSimps miscLib rich_listTheory arithmeticTheory;
open lexer_funTheory repl_funTheory replTheory untypedSafetyTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory
open lexer_implTheory cmlParseTheory inferSoundTheory bigStepTheory elabTheory compilerProofTheory;
open semanticPrimitivesTheory typeSystemTheory typeSoundTheory weakeningTheory evalPropsTheory typeSysPropsTheory terminationTheory;
open initialEnvTheory interpTheory;
open typeSoundInvariantsTheory inferTheory free_varsTheory;
open bytecodeTheory repl_fun_altTheory repl_fun_alt_proofTheory;
open gramPropsTheory pegSoundTheory pegCompleteTheory

val _ = new_theory "replCorrect";

(* TODO: move *)
val o_f_FUNION = store_thm("o_f_FUNION",
  ``f o_f (f1 ⊌ f2) = (f o_f f1) ⊌ (f o_f f2)``,
  simp[GSYM fmap_EQ_THM,FUNION_DEF] >>
  rw[o_f_FAPPLY]);

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

val print_envE_not_type_error = prove(``print_envE types en ≠ "<type error>\n"``,
Induct_on`en`>>simp[print_envE_def]>>
Cases>>simp[])

val print_result_not_type_error = prove(``r ≠ Rerr Rtype_error ⇒ print_result types top envc r ≠ "<type error>\n"``,
  Cases_on`r`>>
  TRY(Cases_on`e`)>>
  TRY(PairCases_on`a`)>>
  simp[print_result_def]>>
  Cases_on`top`>>simp[print_result_def]>>
  match_mp_tac print_envC_not_type_error >>
  simp[print_envE_not_type_error])

val type_infer_invariants_def = Define `
type_infer_invariants rs rinf_st ⇔
      check_menv (FST (SND rinf_st))
    ∧ check_cenv (FST (SND (SND rinf_st)))
    ∧ check_env {} (SND (SND (SND rinf_st)))
    ∧ (rs.tdecs = convert_decls (FST rinf_st))
    ∧ (rs.tenvM = convert_menv (FST (SND rinf_st)))
    ∧ (rs.tenvC = FST (SND (SND rinf_st)))
    ∧ (rs.tenv = (bind_var_list2 (convert_env2 (SND (SND (SND rinf_st)))) Empty))`;

val type_invariants_pres = Q.prove (
`!rs rfs.
  type_infer_invariants rs (decls,infer_menv,infer_cenv,infer_env) ∧
  infer_top decls infer_menv infer_cenv infer_env top init_infer_state =
          (Success (new_decls,new_infer_menv,new_infer_cenv,new_infer_env), infer_st2)
  ⇒
  type_infer_invariants (update_repl_state top rs el (convert_decls new_decls) (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st'
                                     envC (Rval (envM,envE)))
                  (new_decls,new_infer_menv ++ infer_menv, merge_tenvC new_infer_cenv infer_cenv,new_infer_env ++ infer_env)`,
rw [update_repl_state_def, type_infer_invariants_def] >>
`check_menv new_infer_menv ∧
 check_cenv new_infer_cenv ∧
 check_env {} new_infer_env`
           by metis_tac [inferPropsTheory.infer_top_invariant] >|
[fs [check_menv_def],
 cases_on `new_infer_cenv` >>
     cases_on `rs.tenvC` >>
     fs [merge_tenvC_def, libTheory.merge_def, check_cenv_def, check_flat_cenv_def],
 fs [check_env_def],
 rw [convert_menv_def],
 rw [bvl2_append, convert_env2_def]]);

val type_invariants_pres_err = Q.prove (
`!rs rfs.
  type_infer_invariants rs (decls,infer_menv,infer_cenv,infer_env) ∧
  infer_top decls infer_menv infer_cenv infer_env top init_infer_state =
          (Success (new_decls,new_infer_menv,new_infer_cenv,new_infer_env), infer_st2)
  ⇒
  type_infer_invariants (update_repl_state top rs el (convert_decls (append_decls new_decls decls)) (convert_menv new_infer_menv) new_infer_cenv (convert_env2 new_infer_env) st' envC (Rerr err))
                  (append_decls new_decls decls, infer_menv,infer_cenv,infer_env)`,
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
    rfs.relaborator_state = rs.type_bindings
    ∧ SND(SND rs.store) = FST rs.tdecs

    ∧ type_infer_invariants rs rfs.rinferencer_state
    ∧ type_sound_invariants (rs.tdecs,rs.tenvM,rs.tenvC,rs.tenv,FST (SND rs.store),rs.envM,rs.envC,rs.envE,SND (FST rs.store))

    ∧ (∃grd. env_rs (rs.envM,rs.envC,rs.envE) rs.store grd rfs.rcompiler_state bs)

    ∧ bs.clock = NONE

    ∧ code_labels_ok bs.code
    ∧ code_executes_ok bs
    `;

val infer_to_type = Q.prove (
`!rs st bs decls menv cenv env top new_decls new_menv new_cenv new_env st2.
  invariant rs st bs ∧
  (infer_top decls menv cenv env top init_infer_state =
      (Success (new_decls, new_menv,new_cenv,new_env),st2)) ∧
  (st.rinferencer_state = (decls,menv,cenv,env))
  ⇒
  infer_sound_invariant (new_menv ++ menv) (merge_tenvC new_cenv cenv) (new_env++env) ∧
  type_top rs.tdecs rs.tenvM rs.tenvC rs.tenv top
           (convert_decls new_decls) (convert_menv new_menv) new_cenv (convert_env2 new_env)`,
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
  ``∀mno decls tmenv tcenv tenv d x y z.
      type_d mno decls tmenv tcenv tenv d x y z ⇒
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
`!mn decls tenvM tenvC tenv d decls' tenvC' tenv'.
  type_d mn decls tenvM tenvC tenv d decls' tenvC' tenv'
  ⇒
  set (new_dec_vs d) = set (MAP FST tenv')`,
 rw [type_d_cases, new_dec_vs_def, libTheory.emp_def] >>
 rw [new_dec_vs_def] >>
 imp_res_tac type_p_closed >>
 rw [tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
 fs [LET_THM, LIST_TO_SET_MAP, GSYM fst_lem, IMAGE_COMPOSE] >>
 metis_tac [type_funs_dom]);

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

val to_string_map_lem = Q.prove (
`!env. check_env {} env ⇒ (inf_tenv_to_string_map env = tenv_to_string_map (convert_env2 env))`,
 induct_on `env` >>
 rw [check_env_def, inf_tenv_to_string_map_def, tenv_to_string_map_def, convert_env2_def] >>
 PairCases_on `h` >>
 rw [inf_tenv_to_string_map_def, tenv_to_string_map_def] >>
 fs [check_env_def, convert_env2_def] >>
 metis_tac [type_to_string_lem]);

val type_ds_closed = store_thm("type_ds_closed",
  ``∀mn decls tmenv cenv tenv ds x y z. type_ds mn decls tmenv cenv tenv ds x y z ⇒
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
  ``∀decls tmenv tcenv tenv top decls' tm' tc' te'.
      type_top decls tmenv tcenv tenv top decls' tm' tc' te'
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
  type_top rs.tdecs rs.tenvM rs.tenvC rs.tenv top new_decls new_tenvM new_tenvC new_tenv ∧
  type_sound_invariants (rs.tdecs,rs.tenvM,rs.tenvC,rs.tenv,decls',rs.envM,rs.envC,rs.envE,store)
  ⇒
  FV_top top ⊆ all_env_dom (rs.envM,rs.envC,rs.envE)`,
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
`?error_msg next_repl_run_infer_state types.
  infertype_top st.rinferencer_state top = Failure error_msg ∨
  infertype_top st.rinferencer_state top = Success (next_repl_run_infer_state,types)`
         by (cases_on `infertype_top st.rinferencer_state top` >>
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
`?decls infer_menv infer_cenv infer_env.
  st.rinferencer_state = (decls,infer_menv,infer_cenv,infer_env)`
            by metis_tac [pair_CASES] >>
fs [infertype_top_def] >>
`?res infer_st2. infer_top decls infer_menv infer_cenv infer_env top init_infer_state = (res,infer_st2)`
        by metis_tac [pair_CASES] >>
fs [] >>
cases_on `res` >>
fs [] >>
`∃new_decls new_infer_menv new_infer_cenv new_infer_env.  a = (new_decls, new_infer_menv,new_infer_cenv,new_infer_env)`
        by metis_tac [pair_CASES] >>
fs [] >>
BasicProvers.VAR_EQ_TAC >>
imp_res_tac infer_to_type >>
`type_sound_invariants (rs.tdecs,rs.tenvM,rs.tenvC,rs.tenv,FST (SND rs.store),rs.envM,rs.envC,rs.envE,SND (FST rs.store))`
        by fs [invariant_def] >>
`¬top_diverges (rs.envM,rs.envC,rs.envE)
          (SND (FST rs.store),FST (SND rs.store),FST rs.tdecs) top ⇒
       ∀count'.
         ∃r cenv2 store2 decls2'.
           r ≠ Rerr Rtype_error ∧
           evaluate_top F (rs.envM,rs.envC,rs.envE)
             ((count',SND (FST rs.store)),FST (SND rs.store),
              FST rs.tdecs) top
             (((count',store2),decls2',
               FST (convert_decls new_decls) ∪ FST rs.tdecs),cenv2,r) ∧
           type_sound_invariants
             (update_type_sound_inv
                (rs.tdecs,rs.tenvM,rs.tenvC,rs.tenv,FST (SND rs.store),
                 rs.envM,rs.envC,rs.envE,SND (FST rs.store))
                (convert_decls new_decls) (convert_menv new_infer_menv)
                new_infer_cenv (convert_env2 new_infer_env) store2
                decls2' cenv2 r)`
          by metis_tac [top_type_soundness] >>

simp[update_state_def,update_state_err_def] >>

qabbrev_tac`elab_res = elab_top st.relaborator_state top0` >> PairCases_on`elab_res` >>
pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def])>>fs[]>>
`st.relaborator_state = rs.type_bindings` by fs[invariant_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[elaborate_top_def,LET_THM] >>
qmatch_assum_rename_tac`xxxxxxxx = top`[] >> rpt BasicProvers.VAR_EQ_TAC >>

cases_on `bc_eval (install_code code bs)` >> fs[] >- (
  (* Divergence *)
  rw[Once ast_repl_cases,get_type_error_mask_def] >>
  simp[and_shadow_def] >>
  conj_asm1_tac >- (
    first_assum(match_exists_tac o concl) >> rw[] >>
    qpat_assum`∀m. X ⇒ Y`kall_tac >>
    `∃ck store tdecls. rs.store = ((ck,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,invariant_def,SND] >>
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
    conj_tac >- ( metis_tac [new_top_vs_inf_tenv_to_string_map_lem] ) >>
    conj_tac >- cheat >>
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
  `∃ck store tdecls. rs.store = ((ck,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,invariant_def,SND] >>
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
  `∃ck0 store tdecls. rs.store = ((ck0,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,SND] >> fs[] >>
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

  first_x_assum(qspec_then`FST(FST rs.store)`strip_assume_tac) >>
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
      `∃ck0 store tdecls. rs.store = ((ck0,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,SND] >> fs[] >>
      fs[] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[bc_state_component_equality] ) >>
    conj_tac >- metis_tac[new_top_vs_inf_tenv_to_string_map_lem] >>
    conj_tac >- cheat >>
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
  `∃ck0 store tdecls. rs.store = ((ck0,store),tdecls,FST rs.tdecs)` by metis_tac[pair_CASES,SND] >> fs[] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(equal``type_top`` o fst o strip_comb))) >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  reverse conj_asm1_tac >- metis_tac[print_result_not_type_error] >>

  Cases_on `r` >> fs[] >- (
    (* successful declaration *)
    PairCases_on`a` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rpt(qpat_assum`T`kall_tac) >>
    simp[install_code_def] >>
    reverse conj_tac >- (
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      match_mp_tac to_string_map_lem >>
      fs [infer_sound_invariant_def, check_env_def] ) >>
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
    conj_tac >- fs [update_type_sound_inv_def] >> 
    inv_pres_tac) >>

  (* exception *)
  reverse(Cases_on`e`>>fs[])>>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[install_code_def] >>
  reverse conj_tac >- (
    rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
    match_mp_tac to_string_map_lem >>
    fs [infer_sound_invariant_def, check_env_def] ) >>
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
  conj_tac >- fs [update_type_sound_inv_def] >>
  inv_pres_tac);

val _ = delete_const"and_shadow"

val eval_initial_program = store_thm("eval_initial_program",
``evaluate_top F ([],init_envC,[]) s (Tdec initial_program)
  (s, ([],[]), Rval ([],init_env))``,
PairCases_on`s` >>
match_mp_tac (MP_CANON bigClockTheory.top_unclocked_ignore) >>
qexists_tac`T` >> simp[] >>
exists_suff_gen_then mp_tac run_eval_top_spec >>
CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV EVAL))) >>
REWRITE_TAC[astTheory.pat_bindings_def,run_eval_def] >>
CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV EVAL))) >>
metis_tac[])

val initial_bc_state_side_thm = store_thm("initial_bc_state_side_thm",
  ``initial_bc_state_side``,
  REWRITE_TAC[initial_bc_state_side_def] >> simp[] >>
  mp_tac (MATCH_MP bigClockTheory.top_add_clock
           (Q.SPEC`init_repl_state.store`(Q.GEN`s`eval_initial_program))) >>
  simp[init_repl_state_def] >>
  disch_then(qx_choose_then`ck`(mp_tac o MATCH_MP compile_top_thm))>>
  disch_then(qspecl_then[`init_compiler_state`,`NONE`]mp_tac) >>
  simp[GSYM compile_primitives_def] >>
  `∃rss rsf bc. compile_primitives = (rss,rsf,bc)` by metis_tac[pair_CASES] >>
  simp[] >>
  disch_then(qspecl_then[`([],init_gtagenv,<|sm:=[];cls:=FEMPTY|>)`,
                         `install_code bc empty_bc_state with clock := SOME ck`,
                         `[]`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      match_mp_tac env_rs_empty >>
      simp[install_code_def,initialProgramTheory.empty_bc_state_def] >>
      EVAL_TAC ) >>
    conj_tac >- (EVAL_TAC >> simp[]) >>
    simp[install_code_def,initialProgramTheory.empty_bc_state_def] ) >>
  strip_tac >>
  qmatch_assum_rename_tac`bc_fetch bs2 = SOME (Stop T)`[] >>
  qexists_tac`initial_bc_state` >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  imp_res_tac RTC_bc_next_bc_eval >>
  pop_assum kall_tac >>
  pop_assum mp_tac >>
  discharge_hyps >- (
    simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock] ) >>
  `install_code bc empty_bc_state with clock := NONE = install_code bc empty_bc_state` by
    simp[install_code_def,initialProgramTheory.empty_bc_state_def] >>
  simp[initial_bc_state_def,bc_fetch_with_clock])

val initial_invariant = store_thm("initial_invariant",
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  simp[invariant_def,initial_repl_fun_state_def,init_repl_state_def]>>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- simp[typeSoundTheory.initial_type_sound_invariant] >>
  mp_tac (MATCH_MP bigClockTheory.top_add_clock
           (Q.SPEC`init_repl_state.store`(Q.GEN`s`eval_initial_program))) >>
  simp[init_repl_state_def] >>
  disch_then(qx_choose_then`ck`(mp_tac o MATCH_MP compile_top_thm))>>
  disch_then(qspecl_then[`init_compiler_state`,`NONE`]mp_tac) >>
  simp[GSYM compile_primitives_def] >>
  `∃rss rsf bc. compile_primitives = (rss,rsf,bc)` by metis_tac[pair_CASES] >>
  simp[] >>
  disch_then(qspecl_then[`([],init_gtagenv,<|sm:=[];cls:=FEMPTY|>)`,
                         `install_code bc empty_bc_state with clock := SOME ck`,
                         `[]`]mp_tac) >>
  discharge_hyps >- (
    conj_tac >- (
      match_mp_tac env_rs_empty >>
      simp[install_code_def,initialProgramTheory.empty_bc_state_def] >>
      EVAL_TAC ) >>
    conj_tac >- (EVAL_TAC >> simp[]) >>
    simp[install_code_def,initialProgramTheory.empty_bc_state_def] ) >>
  strip_tac >>
  qmatch_assum_rename_tac`bc_fetch bs2 = SOME (Stop T)`[] >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  `bs2 with clock := NONE = initial_bc_state` by (
    rw[initial_bc_state_def] >>
    imp_res_tac RTC_bc_next_bc_eval >>
    pop_assum kall_tac >>
    pop_assum mp_tac >>
    discharge_hyps >- (
      simp[bc_eval1_thm,bc_eval1_def,bc_fetch_with_clock] ) >>
    `empty_bc_state with clock := NONE = empty_bc_state` by simp[initialProgramTheory.empty_bc_state_def] >>
    rw[install_code_def] ) >>
  conj_tac >- (
    fs[merge_envC_def,init_envC_def,libTheory.merge_def] >>
    qexists_tac`grd'` >>
    match_mp_tac env_rs_change_clock >>
    first_assum(match_exists_tac o concl) >>
    simp[] >> metis_tac[] ) >>
  conj_tac >- (
    pop_assum(SUBST1_TAC o SYM) >> rw[] ) >>
  conj_tac >- (
    fs[compile_primitives_def] >>
    qspecl_then[`NONE`,`init_compiler_state`,`Tdec initial_program`]mp_tac compile_top_labels >>
    discharge_hyps >- (
      simp[SUBSET_DEF] >>
      EVAL_TAC >> simp[] ) >>
    simp[] >>
    imp_res_tac RTC_bc_next_preserves >>
    simp[install_code_def,initialProgramTheory.empty_bc_state_def] ) >>
  simp[code_executes_ok_def] >>
  disj1_tac >>
  qexists_tac`initial_bc_state` >>
  simp[] >>
  metis_tac[bc_fetch_with_clock])

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
