open preamble boolSimps;
open lexer_funTheory repl_funTheory replTheory
open lexer_implTheory mmlParseTheory inferSoundTheory BigStepTheory ElabTheory compilerProofsTheory;

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
cheat);

val get_type_error_mask_def = Define `
(get_type_error_mask Terminate = []) ∧
(get_type_error_mask Diverge = [F]) ∧
(get_type_error_mask Diverge = [F]) ∧
(get_type_error_mask (Result r rs) =
  (r = "<type error>")::get_type_error_mask rs)`;


val invariant_def = Define`
  invariant rs rfs bs ⇔
    rfs.relaborator_state = (rs.type_bindings, rs.ctors)

    ∧ check_menv (FST rfs.rinferencer_state)
    ∧ check_cenv (FST (SND rfs.rinferencer_state))
    ∧ check_env {} (SND (SND rfs.rinferencer_state))
    (* ∧ rfs.tenvE *)
    ∧ (FST (SND rfs.rinferencer_state)) = rs.tenvC
    (* ∧ rfs.tenvM *)

    ∧ ∃rd c. env_rs rs.envM rs.envC rs.envE rfs.rcompiler_state rd (c,rs.store) bs
    (* ∧ rfs.top = ??? *)`

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
  rw [Once ast_repl_cases, parse_elaborate_infertype_compile_def, parser_correct,
      get_type_error_mask_def] >>
`?error_msg new_repl_run_infer_state.
  infertype_top st.rinferencer_state top = Failure error_msg ∨ 
  infertype_top st.rinferencer_state top = Success new_repl_run_infer_state`
         by (cases_on `infertype_top st.rinferencer_state top` >>
             metis_tac []) >>
rw [get_type_error_mask_def] >-
((* A type error *)
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
     metis_tac [lexer_correct]) >>
`?new_bc_success new_bc_failure code. compile_top st.rcompiler_state top = (new_bc_success, new_bc_failure, code)`
         by (cases_on `compile_top st.rcompiler_state top` >>
             Cases_on`r` >>
             metis_tac []) >>
rw [] >>

cases_on `bc_eval (install_code code bs)` >>
rw [get_type_error_mask_def] >>
qabbrev_tac`est = st.relaborator_state` >> PairCases_on`est` >>
qabbrev_tac`elab_res = elab_top est0 est1 top0` >> PairCases_on`elab_res` >>
`est0 = rs.type_bindings ∧ est1 = rs.ctors` by fs[invariant_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[elaborate_top_def,LET_THM] >>
qabbrev_tac`el = elab_top rs.type_bindings rs.ctors top0` >> PairCases_on`el` >>
fs[] >> qmatch_assum_rename_tac`xxxxxxxx = top`[] >> BasicProvers.VAR_EQ_TAC >- (

  (* Divergence *)


  cheat ) >>

disj1_tac >>
rw[update_state_def] >>

Cases_on`top0` >- (
   (* Module *)
  cheat ) >>

fs[elab_top_def,LET_THM] >>
qabbrev_tac`p = elab_dec NONE rs.type_bindings rs.ctors a` >>
PairCases_on`p` >> fs[] >>
fs[markerTheory.Abbrev_def] >>
rpt BasicProvers.VAR_EQ_TAC >>
fs[compile_top_def] >>

simp[Once evaluate_prog_cases] >>
fs[elaborate_top_def,LET_THM] >>
cheat

)

val good_compile_primitives = prove(
  ``good_contab (FST compile_primitives).contab ∧
    good_cmap [] (cmap (FST compile_primitives).contab) (* ∧ not true
    {Short ""} = FDOM (cmap (FST compile_primitives).contab) *)
    ``,
  rw[compile_primitives_def] >>
  rw[CompilerTheory.compile_dec_def] >>
  rw[CompilerTheory.compile_fake_exp_def] >>
  rw[good_contab_def,intLangExtraTheory.good_cmap_def] >>
  rw[CompilerTheory.init_compiler_state_def,good_contab_def] >>
  rw[IntLangTheory.tuple_cn_def,IntLangTheory.bind_exc_cn_def,IntLangTheory.div_exc_cn_def] >>
  rw[toIntLangProofsTheory.cmap_linv_def,FAPPLY_FUPDATE_THM])

val initial_invariant = prove(
  ``invariant init_repl_state initial_repl_fun_state initial_bc_state``,
  rw[invariant_def,initial_repl_fun_state_def,initial_elaborator_state_def,init_repl_state_def] >>
  rw[check_menv_def,initial_inferencer_state_def,check_cenv_def,check_env_def]
  >- EVAL_TAC >>

  (* env_rs proof: *)
  simp[env_rs_def,good_compile_primitives] >>

  cheat)

val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
match_mp_tac replCorrect_lem >>
rw[initial_invariant])

val _ = export_theory ();
