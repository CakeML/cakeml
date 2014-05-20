
open HolKernel Parse boolLib bossLib;

val _ = new_theory "repl_fun_alt";

open listTheory arithmeticTheory relationTheory;
open repl_funTheory bytecodeLabelsTheory bytecodeTheory;

(*

   This file rephrases repl_fun (as repl_fun_alt) so that it fits
   better with the machine-code implementation. In particular:

    - all functions that are to be bootstrapped are collected into
      one function called repl_step, and

    - all labels are expanded away before code installation.

*)

val repl_step_def = Define `
  repl_step state =
    case state of
    | NONE => (* first time around *)
       let code = SND (SND compile_primitives) in
       let code = REVERSE code in
       let labs = collect_labels code 0 real_inst_length in
       let len = code_length real_inst_length code in
       let code = inst_labels labs code in
       INL (MAP bc_num code,len,labs,
            initial_repl_fun_state,initial_repl_fun_state)
    | SOME (tokens,new_s,len,labs,s',s_exc) => (* received some input *)
        let s = if new_s then s' else s_exc in
        case parse_elaborate_infertype_compile (MAP token_of_sym tokens) s of
        | Success (code,s',s_exc) =>
            let code = REVERSE code in
            let labs = FUNION labs (collect_labels code len real_inst_length) in
            let len = len + code_length real_inst_length code in
            let code = inst_labels labs code in
              INL (MAP bc_num code,len,labs,s',s_exc)
        | Failure error_msg => INR (error_msg,(F,len,labs,s,s))`

val install_bc_lists_def = Define `
  install_bc_lists code bs =
    install_code (REVERSE (MAP num_bc code)) bs`

val tac = (WF_REL_TAC `measure (LENGTH o FST o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lexer_implTheory.lex_until_top_semicolon_alt_LESS);

val main_loop_alt_def = tDefine "main_loop_alt" `
  main_loop_alt bs input state init =
    case repl_step state of
      | INR (error_msg,x) =>
            Result error_msg
             (case lex_until_top_semicolon_alt input of
              | NONE => Terminate
              | SOME (ts,rest) =>
                  (main_loop_alt bs rest (SOME (ts,x)) F))
      | INL (code,new_state) =>
        case bc_eval (install_bc_lists code bs) of
        | NONE => Diverge
        | SOME new_bs =>
            let new_s = (bc_fetch new_bs = SOME (Stop T)) in
              (if init then I else Result new_bs.output)
                (case lex_until_top_semicolon_alt input of
                 | NONE => Terminate
                 | SOME (ts,rest) =>
                     (main_loop_alt new_bs rest (SOME (ts,new_s,new_state)) F)) ` tac

val repl_fun_alt_def = Define `
  repl_fun_alt input = main_loop_alt empty_bc_state input NONE T`;

val _ = export_theory();
