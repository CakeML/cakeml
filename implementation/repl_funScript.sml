open HolKernel boolLib bossLib lcsymtacs
open lexer_implTheory mmlParseTheory AstTheory inferTheory CompilerTheory
     PrinterTheory compilerTerminationTheory bytecodeEvalTheory replTheory

val _ = new_theory "repl_fun";

val _ = Hol_datatype`repl_fun_state = <|
  rtypes : typeN list ; rctors : ctor_env ; rbindings : binding_env;
  rmenv : (modN, (varN,num#infer_t) env) env ; rcenv : tenvC;
  rtenv : (tvarN,num#infer_t) env ;
  rcompiler_state : compiler_state ;
  decs : dec list |>`

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := \x.0 |>`

val init_repl_fun_state = Define`
  init_repl_fun_state = <|
    rtypes := []; rctors := []; rbindings := [];
    rmenv := []; rcenv := []; rtenv := [];
    rcompiler_state := init_compiler_state ; decs := [] |>`

val print_result_def = Define `
  print_result s bs =
    simple_printer
      (FLAT (MAP (preprint_dec s.rcompiler_state) s.decs))
      (cpam s.rcompiler_state) bs.stack`

val update_state_def = Define`
  update_state s tbs cts bds (rm,rc,rt) cs ds =
  s with <| rtypes  := tbs ++ s.rtypes
          ; rctors          := cts ++ s.rctors
          ; rbindings       := bds ++ s.rbindings
          ; rmenv           := rm ++ s.rmenv
          ; rcenv           := rc ++ s.rcenv
          ; rtenv           := rt ++ s.rtenv
          ; rcompiler_state := cs
          ; decs            := ds
          |>`

val compile_prog_def = Define `
  (compile_prog cs [] = (cs,[],[])) /\
  (compile_prog cs (Tmod _ _ _::xs) = compile_prog cs xs) /\ (* fix! *)
  (compile_prog cs (Tdec dec::xs) =
     let (cs,code1) = compile_dec cs dec in
     let (cs,decs,code2) = compile_prog cs xs in
       (cs,dec :: decs,code1 ++ code2))`;

val parse_elaborate_typecheck_compile_def = Define `
  parse_elaborate_typecheck_compile tokens s =
    case parse tokens of
      (* case: parse error *)
      NONE => Failure "parse error"
    | (* case: ast_prog produced *)
      SOME ast_prog =>
        let (ts,cts,bds,prog) = elab_prog s.rtypes s.rctors s.rbindings ast_prog in
          case FST (infer_prog s.rmenv s.rcenv s.rtenv prog init_infer_state) of
            (* type inference failed to find type *)
          | Failure _ => Failure "type error"
            (* type found, type safe! *)
          | Success type_state =>
             let (cs,decs,code) = compile_prog s.rcompiler_state prog in
               Success (code,update_state s ts cts bds type_state cs decs)`

val install_code_def = Define `
  install_code code bs =
    let code = compile_labels bs.inst_length (bs.code ++ code) in
    bs with <| code := code ;
               pc := next_addr bs.inst_length bs.code |>`;

val tac = (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
           THEN IMP_RES_TAC lex_until_toplevel_semicolon_LESS);

val main_loop_def = tDefine "main_loop" `
  main_loop (bs,s) input =
    case lex_until_toplevel_semicolon input of
      (* case: nothing but white space found, i.e. end of input *)
      NONE => Terminate
    | (* case: tokens have been read, now eval-print-and-loop *)
      SOME (tokens, rest_of_input) =>
        case parse_elaborate_typecheck_compile tokens s of
          (* case: cannot turn into code, show print error message, continue *)
          Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)
        | (* case: new code generated, install, run, print and continue *)
          Success (code,new_s) =>
            case bc_eval (install_code code bs) of
              (* case: evaluation of code does not terminate *)
              NONE => Diverge
            | (* case: evaluation terminated, print result and continue *)
              SOME new_bs => Result (print_result new_s new_bs)
                                    (main_loop (new_bs,new_s) rest_of_input) ` tac ;

val repl_fun_def = Define`
  repl_fun input = main_loop (init_bc_state,init_repl_fun_state) input`;

(*

val cheat_wfs = let val wfs = (mk_thm([],``t_wfs s``)) in
fn th => PROVE_HYP wfs (UNDISCH(SPEC_ALL th))
end

val _ = computeLib.add_funs
  [cheat_wfs unifyTheory.t_unify_eqn
  ,unifyTheory.t_walk_eqn
  ,unifyTheory.t_ext_s_check_eqn
  ,cheat_wfs unifyTheory.t_oc_eqn
  ,cheat_wfs unifyTheory.t_vwalk_eqn
  ,computeLib.lazyfy_thm(bytecodeEvalTheory.bc_eval_def)
  ]
val _ = computeLib.add_funs[listTheory.SUM] (* why isn't this in there already !? *)

val input = ``"val x = true; val y = false;"``
(* LOOPS if you use numbers, because of toString or Num in ov_to_string *)

val (tokens,rest_of_input) = EVAL ``lex_until_toplevel_semicolon ^input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair
val ast_prog = EVAL ``mmlParse$parse ^tokens`` |> concl |> rhs |> rand
val s = ``init_repl_fun_state``

val prog = EVAL ``elab_prog ^s.rtypes ^s.rctors ^s.rbindings ^ast_prog``
  |> concl |> rhs |> rand |> rand |> rand

val res = EVAL ``FST (infer_prog ^s.rmenv ^s.rcenv ^s.rtenv ^prog init_infer_state)``

val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens init_repl_fun_state``

val (code,new_s) = res |> concl |> rhs |> rand |> pairSyntax.dest_pair

val bs = EVAL ``install_code ^code init_bc_state`` |> concl |> rhs

val new_bs = EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

val res = EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs

val (tokens,rest_of_input) = EVAL ``lex_until_toplevel_semicolon ^rest_of_input`` |> concl |> rhs |> rand |> pairSyntax.dest_pair
val ast_prog = EVAL ``mmlParse$parse ^tokens`` |> concl |> rhs |> rand
val s = new_s
val bs = new_bs

val prog = EVAL ``elab_prog ^s.rtypes ^s.rctors ^s.rbindings ^ast_prog``
  |> concl |> rhs |> rand |> rand |> rand

val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens init_repl_fun_state``

val (code,new_s) = res |> concl |> rhs |> rand |> pairSyntax.dest_pair

val bs = EVAL ``install_code ^code ^bs`` |> concl |> rhs

val new_bs = EVAL ``bc_eval ^bs`` |> concl |> rhs |> rand

val res = EVAL ``print_result ^new_s ^new_bs`` |> concl |> rhs

val res = EVAL ``repl_fun ^input``

*)


(*

TODO:

 - Distinguish between error messages (e.g. from failed type check)
   and real output in repl_result, i.e. above

     Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)

   should really be something like:

     Failure error_msg => Error error_msg (main_loop (bs,s) rest_of_input)

*)

val _ = export_theory()
