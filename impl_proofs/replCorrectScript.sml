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
`!toks. parse_top toks = parse toks`,
cheat);

(*
val replCorrect_lem = Q.prove (
`!repl_state bc_state repl_fun_state.
  ast_repl repl_state
    (MAP parse (split_top_level_semi (lexer_fun input)))
    (main_loop (bc_state,repl_fun_state) input)`,
  

completeInduct_on `LENGTH input` >>
rw [Once main_loop_def, lexer_correct, Once lex_impl_all_def] >>
cases_on `lex_until_toplevel_semicolon input` >>
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
rw [] >-
((* A type error *)
 

(* To encapsulate that we allow the type inferencer to fail when the type system
 * has a type. *)
val (add_type_error_rules, add_type_error_cases, add_type_error_ind) = Hol_reln `
(add_type_error Terminate Terminate) ∧
(add_type_error Diverge Diverge) ∧
(!rs. add_type_error Diverge (Result "<type error>" rs)) ∧
(!r rs rs'. 
  add_type_error rs rs'
  ⇒
  add_type_error (Result r rs) (Result r rs')) ∧
(!r rs rs'. 
  add_type_error rs rs'
  ⇒
  add_type_error (Result r rs) (Result "<type error>" rs'))`;

val replCorrect = Q.store_thm ("replCorrect",
`!input output. 
  (repl_fun input = output) ⇒ 
  ?output'. add_type_error output' output ∧ (repl input output')`,
rw [repl_fun_def, repl_def]
*)

val _ = export_theory ();

