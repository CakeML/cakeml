
open HolKernel Parse boolLib bossLib;

val _ = new_theory "repl_fun_alt";

open listTheory arithmeticTheory relationTheory;
open repl_funTheory bytecodeLabelsTheory BytecodeTheory;

(*

   This file rephrases repl_fun (as repl_fun_alt) so that it fits
   better with the machine-code implementation. In particular:

    - all functions that are to be bootstrapped are collected into
      one function called repl_step, and

    - all labels are expanded away before code installation.

*)

val inst_length_def = Define `
  inst_length (x:bc_inst) = 0:num`; (* fix me *)

val empty_bc_state_def = Define `
  empty_bc_state = <| stack := []; code := []; pc := 0; refs := FEMPTY;
                      handler := 0; clock := NONE; output := "";
                      cons_names := []; inst_length := K 0|>`;

val repl_step_def = Define `
  repl_step state =
    case state of
    | NONE => (* first time around *)
       let len = 0 in
       let code = PrintE ++ [Stop] in
       let labs = collect_labels code len inst_length in
       let len = code_length inst_length code in
       let code = inst_labels labs code in
       let code1 = REVERSE code in
       let code = SND (SND compile_primitives) in
       let code = REVERSE code in
       let labs = FUNION labs (collect_labels code len inst_length) in
       let len = len + code_length inst_length code in
       let code = inst_labels labs code in
       let code = REVERSE code in
         INL ([],code1,code,len,labs,
                 initial_repl_fun_state,initial_repl_fun_state)
    | SOME (tokens,new_s,len,labs,s',s_exc) => (* received some input *)
        let s = if new_s then s' else s_exc in
        case parse_elaborate_infertype_compile tokens s of
        | Success (code,s',s_exc) =>
            let code = REVERSE code in
            let labs = FUNION labs (collect_labels code len inst_length) in
            let len = len + code_length inst_length code in
            let code = inst_labels labs code in
            let code = REVERSE code in
              INL (cpam s'.rcompiler_state,[],code,len,labs,s_exc,s')
        | Failure error_msg => INR (error_msg,len,labs,s)`

val tac = (WF_REL_TAC `measure (LENGTH o FST o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lexer_implTheory.lex_until_toplevel_semicolon_LESS);

val main_loop_alt_def = tDefine "main_loop_alt" `
  main_loop_alt bs input state =
    case repl_step state of
      | INR (error_msg,len,labs,s) =>
            Result error_msg
             (case lex_until_toplevel_semicolon input of
              | NONE => Terminate
              | SOME (ts,rest) =>
                  (main_loop_alt bs rest (SOME (ts,F,len,labs,s,s))))
      | INL (m,code1,code2,new_state) =>
        case bc_eval (install_code m code2 (install_code m code1 bs)) of
        | NONE => Diverge
        | SOME new_bs =>
            let new_bs = (if state = NONE then new_bs with stack := TL new_bs.stack
                                          else new_bs) in
            let new_s = (bc_fetch new_bs = SOME Stop) in
              (if state = NONE then I else Result (REVERSE new_bs.output))
                (case lex_until_toplevel_semicolon input of
                 | NONE => Terminate
                 | SOME (ts,rest) =>
                     (main_loop_alt new_bs rest (SOME (ts,new_s,new_state)))) ` tac

val repl_fun_alt_def = Define `
  repl_fun_alt input = main_loop_alt empty_bc_state input NONE`;

val _ = export_theory();
