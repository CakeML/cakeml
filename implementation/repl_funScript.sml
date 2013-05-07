open HolKernel boolLib bossLib lcsymtacs
open lexer_funTheory mmlParseTheory AstTheory inferTheory CompilerTheory PrinterTheory compilerTerminationTheory bytecodeEvalTheory replTheory

val _ = new_theory "repl_fun";

val lex_chunk_def = Define `
  lex_chunk input = SOME (lexer_fun input, "")`; (* ugly hack, needs doing properly *)

(* EVAL ``parse(  lexer_fun "val b = 5;val a = 7")`` *)

val lex_chunk_thm = prove(
  ``(lex_chunk input = SOME (ts,rest)) ==> LENGTH rest < LENGTH input``,
  cheat);

val _ = Hol_datatype`repl_fun_state = <|
  rtype_bindings : typeN list ; rctors : ctor_env ; rbindings : binding_env;
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
    rtype_bindings := []; rctors := []; rbindings := [];
    rmenv := []; rcenv := []; rtenv := [];
    rcompiler_state := init_compiler_state ; decs := [] |>`

val print_result_def = Define `
  print_result s bs =
    simple_printer (FLAT (MAP (preprint_dec s.rcompiler_state) s.decs)) (cpam s.rcompiler_state) bs.stack`

val update_state_def = Define`
  update_state s tbs cts bds (rm,rc,rt) cs ds =
  s with <| rtype_bindings  := tbs ++ s.rtype_bindings
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
        let (ts,cts,bds,prog) = elab_prog s.rtype_bindings s.rctors s.rbindings ast_prog in
          case FST (infer_prog s.rmenv s.rcenv s.rtenv prog init_infer_state) of
            (* type inference failed to find type *)
          | Failure _ => Failure "type error"
            (* type found, type safe! *)
          | Success type_state =>
             let (cs,decs,code) = compile_prog s.rcompiler_state prog in
               Success (code,update_state s ts cts bds type_state cs decs)`

val install_code_def = Define `
  install_code code bs =
    bs with <| code := bs.code ++ code ;
               pc := next_addr bs.inst_length bs.code |>`;

val main_loop_def = tDefine "main_loop" `
  main_loop (bs,s) input =
    case lex_chunk input of
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
                                    (main_loop (new_bs,new_s) rest_of_input)
`
  (WF_REL_TAC `measure (LENGTH o SND)` THEN REPEAT STRIP_TAC
   THEN IMP_RES_TAC lex_chunk_thm)  ;

val repl_fun_def = Define`
  repl_fun input = main_loop (init_bc_state,init_repl_fun_state) input`;

(*

val lemma1 =
  unifDefTheory.unify_def |> SPEC_ALL |> UNDISCH |> concl |> (fn tm => mk_thm([],tm))

val lemma2 =
  walkTheory.vwalk_def |> SPEC_ALL |> UNDISCH |> concl |> (fn tm => mk_thm([],tm))

val _ = computeLib.add_funs [lemma1,lemma2]

val input = ``"val x = 1"``

val tokens = EVAL ``lex_chunk ^input`` |> concl |> rhs |> rand |> rator |> rand
val ast_prog = EVAL ``parse ^tokens`` |> concl |> rhs |> rand
val s = ``init_repl_fun_state``

val prog = EVAL ``elab_prog ^s.rtype_bindings ^s.rctors ^s.rbindings ^ast_prog``
  |> concl |> rhs |> rand |> rand |> rand

val res = EVAL ``FST (infer_prog ^s.rmenv ^s.rcenv ^s.rtenv ^prog init_infer_state)``

val res = EVAL  ``parse_elaborate_typecheck_compile ^tokens init_repl_fun_state``

*)


(*

TODO:

 - Distinguish between error messages (e.g. from failed type check)
   and real output in repl_result, i.e. above

     Failure error_msg => Result error_msg (main_loop (bs,s) rest_of_input)

   should really be something like:

     Failure error_msg => Error error_msg (main_loop (bs,s) rest_of_input)

 - Printer function should have a very simple interface at least
   internally. Example:

     val (x,y,z) = (5,Nil,7);

   should call [(0,"x");(1,"y");(2,"z")] and [(7,"Nil")] a special
   function at the end. This function produces:

     val x = 5
     val y = Nil
     val z = 7

*)

val _ = export_theory()
