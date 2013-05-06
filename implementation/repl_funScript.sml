open HolKernel boolLib bossLib lcsymtacs
open lexer_funTheory mmlParseTheory AstTheory inferTheory CompilerTheory PrinterTheory compilerTerminationTheory bytecodeEvalTheory replTheory

val _ = new_theory"repl_fun"

val parse = new_constant("parse",``:token list -> ast_prog option list``)

val _ = Hol_datatype`repl_fun_state = <|
  rtype_bindings : typeN list; rctors : ctor_env; rbindings : binding_env;
  rmenv : (modN, (varN,num#infer_t) env) env; rcenv : tenvC; rtenv : (tvarN,num#infer_t) env;
  rinfer_state : (num |-> infer_t) elab_st;
  rcompiler_state : compiler_state|>`

val init_repl_fun_state = Define`
  init_repl_fun_state = <|
    rtype_bindings := []; rctors := []; rbindings := [];
    rmenv := []; rcenv := []; rvenv := []; rinfer_state := init_infer_state;
    rcompiler_state := init_compiler_state |>`

val ast_repl_fun_def = Define`
  (ast_repl_fun s [] = Terminate) ∧
  (ast_repl_fun s (NONE::asts) = Result "<parse error>"::ast_repl_fun s asts) ∧
  (ast_repl_fun s (SOME ast::asts) =
   let (ts,cs,bs,prog) = elab_prog s.rtype_bindings s.rctors s.rbindings ast in
   let (?,rm,rt,result) = infer_prog s.rmenv s.rcenv s.rtenv prog in
   case result of ?

val repl_fun_def = Define`
  repl_fun input = ast_repl_fun init_repl_fun_state (parse (lexer_fun input))`

val _ = export_theory()
