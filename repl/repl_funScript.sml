open HolKernel Parse boolLib bossLib lcsymtacs
open lexer_implTheory cmlParseTheory astTheory inferTheory compilerTheory
     compilerTerminationTheory bytecodeEvalTheory replTheory
     elabTheory initialProgramTheory

val _ = new_theory "repl_fun";

val _ = type_abbrev ("elaborator_state", ``:tdef_env``);

val elaborate_top_def = Define `
elaborate_top (types : elaborator_state) ast_top =
  let (new_types, top) = elab_top types ast_top in
    ((new_types++types), top)`;

val initial_elaborator_state_def = Define `
initial_elaborator_state : elaborator_state = init_repl_state.type_bindings`;

val _ = type_abbrev ("inferencer_state",
  ``:(modN list # conN id list # varN id list) #
     (modN, (varN, num # infer_t) env) env #
     tenvC #
     (varN, num # infer_t) env``);

val append_decls_def = Define `
append_decls (a,b,c) (x,y,z) = (a++x,b++y,c++z)`;

val infertype_top_def = Define `
infertype_top ((decls, module_type_env, constructor_type_env, type_env) :inferencer_state) ast_top =
  case FST (infer_top decls module_type_env constructor_type_env type_env ast_top infer$init_infer_state) of
     | Failure _ => Failure "<type error>"
     | Success (new_decls, new_module_type_env, new_constructor_type_env, new_type_env) =>
        Success ((append_decls new_decls decls,
                  new_module_type_env ++ module_type_env,
                  merge_tenvC new_constructor_type_env constructor_type_env,
                  new_type_env ++ type_env),
                 new_type_env)`;

val initial_inferencer_state_def = Define `
initial_inferencer_state : inferencer_state = (init_infer_decls, [], init_tenvC, infer$init_type_env)`;

val _ = Hol_datatype`repl_fun_state = <|
  relaborator_state : elaborator_state;
  rinferencer_state : inferencer_state;
  rcompiler_state  : compiler_state |>`

val compile_primitives_def = Define`
  compile_primitives =
    compile_top (NONE:(varN, num # infer_t) alist option) init_compiler_state (Tdec initial_program)`;

val initial_repl_fun_state = Define`
  initial_repl_fun_state = <|
    relaborator_state := initial_elaborator_state;
    rinferencer_state := initial_inferencer_state;
    rcompiler_state   := FST compile_primitives |>`

val update_state_def = Define`
  update_state s es is cs =
  s with <| relaborator_state := es
          ; rinferencer_state := is
          ; rcompiler_state   := cs
          |>`

val update_state_err_def = Define`
  update_state_err s is cs =
  s with <| rinferencer_state := 
              (FST is, FST (SND s.rinferencer_state), FST (SND (SND s.rinferencer_state)), SND (SND (SND s.rinferencer_state)))
          ; rcompiler_state   := cs
          |>`

val parse_elaborate_infertype_compile_def = Define `
  parse_elaborate_infertype_compile tokens s =
    case parse_top tokens of
      (* case: parse error *)
      NONE => Failure "<parse error>\n"
    | (* case: ast_top produced *)
      SOME ast_top =>
        let (es,top) = elaborate_top s.relaborator_state ast_top in
          case infertype_top s.rinferencer_state top of
            (* type inference failed to find type *)
          | Failure _ => Failure "<type error>\n"
            (* type found, type safe! *)
          | Success (is,types) =>
             let (css,csf,code) = compile_top (SOME types) s.rcompiler_state top in
               Success (code,update_state s es is css,update_state_err s is csf)`

val install_code_def = Define `
  install_code code bs =
    bs with <| code   := bs.code ++ REVERSE code
             ; pc     := next_addr bs.inst_length bs.code
             ; output := ""
             |>`;

val initial_bc_state_def =  Define`
  initial_bc_state = THE (bc_eval (install_code (SND (SND compile_primitives)) empty_bc_state))`

val tac = (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lex_until_toplevel_semicolon_LESS);

val main_loop_def = tDefine "main_loop" `
  main_loop (bs,s) input =
    case lex_until_toplevel_semicolon input of
      (* case: no semicolon found, i.e. trailing characters then end of input *)
      NONE => Terminate
    | (* case: tokens for next top have been read, now eval-print-and-loop *)
      SOME (tokens, rest_of_input) =>
        case parse_elaborate_infertype_compile tokens s of
          (* case: cannot turn into code, print error message, continue *)
          Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)
        | (* case: new code generated, install, run, print and continue *)
          Success (code,s,s_exc) =>
            case bc_eval (install_code code bs) of
              (* case: evaluation of code does not terminate *)
              NONE => Diverge
            | (* case: evaluation terminated, analyse result and continue *)
              SOME new_bs =>
                case bc_fetch new_bs of
                  SOME (Stop success) =>
                    let new_s = if success then s else s_exc in
                      Result new_bs.output (main_loop (new_bs,new_s) rest_of_input)` tac ;

val repl_fun_def = Define`
  repl_fun input = main_loop (initial_bc_state,initial_repl_fun_state) input`;

(*

TODO:

 - Distinguish between error messages (e.g. from failed type check)
   and real output in repl_result, i.e. above

     Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)

   should really be something like:

     Failure error_msg => Error error_msg (main_loop (bs,s) rest_of_input)

*)

val _ = export_theory()
