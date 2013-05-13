open HolKernel boolLib bossLib lcsymtacs
open lexer_implTheory mmlParseTheory AstTheory inferTheory CompilerTheory
     PrinterTheory compilerTerminationTheory bytecodeEvalTheory replTheory

val _ = new_theory "repl_fun";

val _ = Hol_datatype`repl_fun_state = <|
  rtypes : typeN list ; rctors : ctor_env ; rbindings : binding_env;
  rmenv : (modN, (varN,num#infer_t) env) env ; rcenv : tenvC;
  rtenv : (tvarN,num#infer_t) env ;
  rcompiler_state : compiler_state ;
  top : top |>`

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := K 0 |>`

val init_repl_fun_state = Define`
  init_repl_fun_state = <|
    rtypes := []; rctors := []; rbindings := Elab$init_env;
    rmenv := []; rcenv := []; rtenv := [];
    rcompiler_state := init_compiler_state ; top := (Tmod "" NONE []) |>`

val print_result_def = Define `
  print_result s bs =
    if HD bs.stack = (Number 0) then
      (bs with <| stack := TL bs.stack |>
      ,case s.top of
       | Tmod _ _ _ => "module"
       | Tdec dec =>
           simple_printer
            (preprint_dec s.rcompiler_state dec)
            (cpam s.rcompiler_state) (TL bs.stack)
      )
    else
      (bs with <| stack := TL (TL bs.stack) |> (* TODO: depends on how exception handlers are represented *)
      ,"Exception" (* TODO: simple_print the actual exception at HD (TL bs.stack) *)
      )`

val update_state_def = Define`
  update_state s tbs cts bds (rm,rc,rt) cs t =
  s with <| rtypes  := tbs ++ s.rtypes
          ; rctors          := cts ++ s.rctors
          ; rbindings       := bds ++ s.rbindings
          ; rmenv           := rm ++ s.rmenv
          ; rcenv           := rc ++ s.rcenv
          ; rtenv           := rt ++ s.rtenv
          ; rcompiler_state := cs
          ; top             := t
          |>`

val compile_top_def = Define `
  (compile_top cs (Tmod _ _ _) = (cs,[])) /\ (* fix! *)
  (compile_top cs (Tdec dec) = compile_dec cs dec)`;

val parse_elaborate_typecheck_compile_def = Define `
  parse_elaborate_typecheck_compile tokens s =
    case parse_top tokens of
      (* case: parse error *)
      NONE => Failure "parse error"
    | (* case: ast_top produced *)
      SOME ast_top =>
        let (ts,cts,bds,top) = elab_top s.rtypes s.rctors s.rbindings ast_top in
          case FST (infer_top s.rmenv s.rcenv s.rtenv top init_infer_state) of
            (* type inference failed to find type *)
          | Failure _ => Failure "type error"
            (* type found, type safe! *)
          | Success type_state =>
             let (cs,code) = compile_top s.rcompiler_state top in
               Success (code,update_state s ts cts bds type_state cs top)`

val install_code_def = Define `
  install_code code bs =
    let code = compile_labels bs.inst_length (bs.code ++ code) in
    bs with <| code := code ; pc := next_addr bs.inst_length bs.code |>`;

val tac = (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lex_until_toplevel_semicolon_LESS);

val main_loop_def = tDefine "main_loop" `
  main_loop (bs,s) input =
    case lex_until_toplevel_semicolon input of
      (* case: no semicolon found, i.e. trailing characters then end of input *)
      NONE => Terminate
    | (* case: tokens for next top have been read, now eval-print-and-loop *)
      SOME (tokens, rest_of_input) =>
        case parse_elaborate_typecheck_compile tokens s of
          (* case: cannot turn into code, print error message, continue *)
          Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)
        | (* case: new code generated, install, run, print and continue *)
          Success (code,new_s) =>
            case bc_eval (install_code code bs) of
              (* case: evaluation of code does not terminate *)
              NONE => Diverge
            | (* case: evaluation terminated, print result and continue *)
              SOME new_bs =>
                let (new_bs,output) = print_result new_s new_bs in
                Result output (main_loop (new_bs,new_s) rest_of_input) ` tac ;

val repl_fun_def = Define`
  repl_fun input = main_loop (init_bc_state,init_repl_fun_state) input`;

(*

TODO:

 - Distinguish between error messages (e.g. from failed type check)
   and real output in repl_result, i.e. above

     Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)

   should really be something like:

     Failure error_msg => Error error_msg (main_loop (bs,s) rest_of_input)

*)

val _ = export_theory()
