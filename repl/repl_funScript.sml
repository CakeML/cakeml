open HolKernel Parse boolLib bossLib lcsymtacs
open lexer_implTheory cmlParseTheory astTheory inferTheory compilerTheory
     compilerTerminationTheory bytecodeEvalTheory replTheory
     initialProgramTheory;
open listTheory arithmeticTheory relationTheory;
open bytecodeLabelsTheory bytecodeTheory;

val _ = new_theory "repl_fun";

val _ = type_abbrev ("inferencer_state",
  ``:(modN list # conN id list # varN id list) #
     tenvT #
     (modN, (varN, num # infer_t) env) env #
     tenvC #
     (varN, num # infer_t) env``);

val infertype_top_def = Define `
infertype_top ((decls, type_name_env, module_type_env, constructor_type_env, type_env) :inferencer_state) ast_top =
  case FST (infer_top decls type_name_env module_type_env constructor_type_env type_env ast_top infer$init_infer_state) of
     | Failure _ => Failure "<type error>"
     | Success (new_decls, new_type_name_env, new_module_type_env, new_constructor_type_env, new_type_env) =>
        Success ((append_decls new_decls decls,
                  merge_tenvT new_type_name_env type_name_env,
                  new_module_type_env ++ module_type_env,
                  merge_tenvC new_constructor_type_env constructor_type_env,
                  new_type_env ++ type_env),
                 new_type_env)`;

                 (*
val initial_inferencer_state_def = Define `
initial_inferencer_state : inferencer_state = (((THE basis_env).inf_mdecls,(THE basis_env).inf_tdecls,(THE basis_env).inf_edecls), (THE basis_env).inf_tenvM, (THE basis_env).inf_tenvC, (THE basis_env).inf_tenvE)`;
*)

val _ = Hol_datatype`repl_fun_state = <|
  rinferencer_state : inferencer_state;
  rcompiler_state  : compiler_state |>`;

  (*
val initial_repl_fun_state = Define`
  initial_repl_fun_state = <|
    rinferencer_state := initial_inferencer_state;
    rcompiler_state   := (THE basis_env).comp_rs |>`
    *)

val update_state_def = Define`
  update_state s is cs =
  s with <| rinferencer_state := is
          ; rcompiler_state   := cs
          |>`;

val update_state_err_def = Define`
  update_state_err s is cs =
  s with <| rinferencer_state := 
              (FST is, FST (SND s.rinferencer_state), FST (SND (SND s.rinferencer_state)), SND (SND (SND s.rinferencer_state)))
          ; rcompiler_state   := cs
          |>`;

val parse_infertype_compile_def = Define `
  parse_infertype_compile tokens s =
    case parse_top tokens of
      (* case: parse error *)
      NONE => Failure "<parse error>\n"
    | (* case: top produced *)
      SOME top =>
        case infertype_top s.rinferencer_state top of
          (* type inference failed to find type *)
        | Failure _ => Failure "<type error>\n"
          (* type found, type safe! *)
        | Success (is,types) =>
           let (css,csf,code) = compile_top (SOME types) s.rcompiler_state top in
             Success (code,update_state s is css,update_state_err s is csf)`;

val repl_step_def = Define `
  repl_step state =
    case state of
    | INL (initial,code) => (* first time around *)
       let code = REVERSE code in
       let labs = collect_labels code 0 real_inst_length in
       let len = code_length real_inst_length code in
       let code = inst_labels labs code in
       INL (MAP bc_num code,len,labs,initial,initial)
    | INR (tokens,new_s,len,labs,s',s_exc) => (* received some input *)
        let s = if new_s then s' else s_exc in
        case parse_infertype_compile (MAP token_of_sym tokens) s of
        | Success (code,s',s_exc) =>
            let code = REVERSE code in
            let labs = FUNION labs (collect_labels code len real_inst_length) in
            let len = len + code_length real_inst_length code in
            let code = inst_labels labs code in
              INL (MAP bc_num code,len,labs,s',s_exc)
        | Failure error_msg => INR (error_msg,(F,len,labs,s,s))`;

val install_bc_lists_def = Define `
  install_bc_lists code bs =
    install_code (REVERSE (MAP num_bc code)) bs`;

val tac = (WF_REL_TAC `measure (LENGTH o FST o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lexer_implTheory.lex_until_top_semicolon_alt_LESS);

val main_loop_def = tDefine "main_loop" `
  main_loop bs input state init =
    case repl_step state of
      | INR (error_msg,x) =>
            Result error_msg
             (case lex_until_top_semicolon_alt input of
              | NONE => Terminate
              | SOME (ts,rest) =>
                  (main_loop bs rest (INR (ts,x)) F))
      | INL (code,new_state) =>
        case bc_eval (install_bc_lists code bs) of
        | NONE => Diverge
        | SOME new_bs =>
            let new_s = (bc_fetch new_bs = SOME (Stop T)) in
              (if init then I else Result new_bs.output)
                (case lex_until_top_semicolon_alt input of
                 | NONE => Terminate
                 | SOME (ts,rest) =>
                     (main_loop new_bs rest (INR (ts,new_s,new_state)) F)) ` tac;

val repl_fun_def = Define `
  repl_fun initial input = main_loop empty_bc_state input (INL initial) T`;
  
(*

TODO:

 - Distinguish between error messages (e.g. from failed type check)
   and real output in repl_result, i.e. above

     Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)

   should really be something like:

     Failure error_msg => Error error_msg (main_loop (bs,s) rest_of_input)

*)

val _ = export_theory()
