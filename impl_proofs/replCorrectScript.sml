open preamble;
open repl_funTheory replTheory lexer_implTheory;

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
cheat);

val parser_correct = Q.prove (
`!toks. parse_top tok' = parse tok'`,
cheat);

(*
val replCorrect = Q.store_thm ("replCorrect",
`!input output. (repl_fun input = output) ⇒ (repl input output)`,

completeInduct_on `LENGTH input` >>
rw [repl_fun_def, repl_def, Once main_loop_def, lexer_correct, 
    Once lex_impl_all_def] >>
cases_on `lex_until_toplevel_semicolon input'` >>
rw [] >-
metis_tac [ast_repl_rules] >>
`?tok input_rest. x = (tok, input_rest)`
        by (cases_on `x` >>
            metis_tac []) >>
rw [] >>
`(parse tok' = NONE) ∨ ∃ast. parse tok' = SOME ast` 
        by (cases_on `parse tok'` >>
            metis_tac []) >>
rw [] >>
rw [Once ast_repl_cases, parse_elaborate_infertype_compile_def, parser_correct] >-
(* The semantics and implementation had a different error message*)
cheat >>
Q.ABBREV_TAC `x = elaborate_top init_repl_fun_state.relaborator_state ast` >>
`?new_elaborate_state ast'. x = (new_elaborate_state, ast')` 
       by (cases_on `x` >>
           metis_tac []) >>
rw [] >>
Q.ABBREV_TAC `infer_res = infertype_top init_repl_fun_state.rinferencer_state ast'` >>
rw [] >>
`?error_msg infer_state.
  infer_res = Failure error_msg ∨ 
  infer_res = Success infer_state`
         by (cases_on `infer_res` >>
             metis_tac []) >>
rw []
        


cases_on `infer_top init_repl_fun_state.rmenv
              init_repl_fun_state.rcenv init_repl_fun_state.rtenv top'
              init_infer_state` >>
rw []
*)

val _ = export_theory ();

