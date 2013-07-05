open preamble repl_funTheory lexer_implTheory;

val _ = new_theory "inferTest";

val parse_elaborate_infertype_def = Define `
  parse_elaborate_infertype tokens s =
    case parse_top tokens of
      (* case: parse error *)
      NONE => Failure "<parse error>"
    | (* case: ast_top produced *)
      SOME ast_top =>
        let (es,top) = elaborate_top s.relaborator_state ast_top in
          case infertype_top s.rinferencer_state top of
            (* type inference failed to find type *)
          | Failure _ => Failure "<type error>"
            (* type found, type safe! *)
          | Success is =>
              Success (update_state s es is s.rcompiler_state)`;

val tac = (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lex_until_toplevel_semicolon_LESS);

val infer_test_main_loop_def = tDefine "main_loop" `
  infer_test_main_loop (bs,s) input =
    case lex_until_toplevel_semicolon input of
      (* case: no semicolon found, i.e. trailing characters then end of input *)
      NONE => Terminate
    | (* case: tokens for next top have been read, now eval-print-and-loop *)
      SOME (tokens, rest_of_input) =>
        case parse_elaborate_infertype tokens s of
          (* case: cannot turn into code, print error message, continue *)
          Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)
        | (* case: new code generated, install, run, print and continue *)
          Success (s) =>
            Result "<type checks>" (infer_test_main_loop (bs,s) rest_of_input) ` tac ;

val infer_test_repl_fun_def = Define`
  infer_test_repl_fun input = infer_test_main_loop (initial_bc_state,initial_repl_fun_state) input`;

val _ = export_theory ();
