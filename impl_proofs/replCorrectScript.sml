open preamble boolSimps;
open lexer_funTheory repl_funTheory replTheory lexer_implTheory mmlParseTheory BigStepTheory compilerProofsTheory;

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


val replCorrect_lem = Q.prove (
`!repl_state error_mask bc_state repl_fun_state.
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
            metis_tac []) >>
rw [] >>
rw [Once ast_repl_cases, parse_elaborate_infertype_compile_def, parser_correct,
    get_type_error_mask_def] >-
((* A parse error *)
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
     metis_tac [lexer_correct]) >>
`?new_repl_fun_elab_state ast'.
    elaborate_top repl_fun_state'.relaborator_state ast = (new_repl_fun_elab_state, ast')`
          by (cases_on `elaborate_top repl_fun_state'.relaborator_state ast` >>
              metis_tac []) >>
rw [] >>
`?error_msg new_repl_run_infer_state.
  infertype_top repl_fun_state'.rinferencer_state ast' = Failure error_msg ∨ 
  infertype_top repl_fun_state'.rinferencer_state ast' = Success new_repl_run_infer_state`
         by (cases_on `infertype_top repl_fun_state'.rinferencer_state ast'` >>
             metis_tac []) >>
rw [get_type_error_mask_def] >-
((* A type error *)
 `LENGTH input_rest < LENGTH input` by metis_tac [lex_until_toplevel_semicolon_LESS] >>
     metis_tac [lexer_correct]) >>
`?new_bc_success new_bc_failure code. compile_top repl_fun_state'.rcompiler_state ast' = (new_bc_success, new_bc_failure, code)`
         by (cases_on `compile_top repl_fun_state'.rcompiler_state ast'` >>
             Cases_on`r` >>
             metis_tac []) >>
rw [] >>
cases_on `bc_eval (install_code code bc_state')` >>
rw [get_type_error_mask_def] >|
[(* Divergence *)
 cheat,

 disj1_tac >>
 rw[update_state_def] >>

 simp[Once evaluate_prog_cases] >>
 qabbrev_tac`est = repl_fun_state'.relaborator_state` >>
 PairCases_on`est` >>
 qabbrev_tac`elab_res = elab_top est0 est1 ast` >>
 PairCases_on`elab_res` >>
 fs[elaborate_top_def,LET_THM] >>
 cheat

])

val replCorrect = Q.store_thm ("replCorrect",
`!input output.
  (repl_fun input = output) ⇒
  (repl (get_type_error_mask output) input output)`,
rw [repl_fun_def, repl_def] >>
rw[replCorrect_lem])

val _ = export_theory ();
