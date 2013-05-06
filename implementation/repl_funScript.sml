open HolKernel boolLib bossLib lcsymtacs
open lexer_funTheory mmlParseTheory AstTheory inferTheory CompilerTheory PrinterTheory compilerTerminationTheory bytecodeEvalTheory replTheory

val _ = new_theory"repl_fun"

val _ = new_constant("parse",``:token list -> ast_prog option list``)

val _ = Hol_datatype`repl_fun_state = <|
  rtype_bindings : typeN list; rctors : ctor_env; rbindings : binding_env;
  rmenv : (modN, (varN,num#infer_t) env) env; rcenv : tenvC; rtenv : (tvarN,num#infer_t) env;
  rcompiler_state : compiler_state;
  rbc_state : bc_state|>`

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := ARB |>`

val init_repl_fun_state = Define`
  init_repl_fun_state = <|
    rtype_bindings := []; rctors := []; rbindings := [];
    rmenv := []; rcenv := []; rtenv := [];
    rcompiler_state := init_compiler_state;
    rbc_state := init_bc_state|>`

(* TODO: Does not handle exceptions! *)
val prog_repl_fun_def = Define`
  (prog_repl_fun s [] = SOME (s,[])) ∧
  (prog_repl_fun s (Tmod modN specs decs::tops) =
   OPTION_MAP (λ(s,ls). (s,"<modules not implemented>"::ls))
   (prog_repl_fun s tops)) ∧
  (prog_repl_fun (cs,bs) (Tdec dec::tops) =
    let (cs,bc) = compile_dec cs dec in
    let bs = bs with <| code := bs.code ++ bc ; pc := next_addr bs.inst_length bs.code |> in
    OPTION_BIND (bc_eval bs)
    (λbs. OPTION_MAP (λ(s,ls). (s, (FLAT(MAP(SNOC #"\n")(print_dec cs bs dec)))::ls)) (prog_repl_fun (cs,bs) tops)))`

val update_state_def = Define`
  update_state s tbs cts bds rm rc rt cs bs =
  s with <| rtype_bindings := tbs ++ s.rtype_bindings
          ; rctors         := cts ++ s.rctors
          ; rbindings      := bds ++ s.rbindings
          ; rmenv := rm ++ s.rmenv
          ; rcenv := rc ++ s.rcenv
          ; rtenv := rt ++ s.rtenv
          ; rcompiler_state := cs
          ; rbc_state       := bs
          |>`

val Results_def = Define`
  (Results [] s = s) ∧
  (Results (x::xs) s = Result x (Results xs s))`

val ast_repl_fun_def = Define`
  (ast_repl_fun s [] = Terminate) ∧
  (ast_repl_fun s (NONE::asts) = Result "<parse error>" (ast_repl_fun s asts)) ∧
  (ast_repl_fun s (SOME ast::asts) =
   let (ts,cts,bds,prog) = elab_prog s.rtype_bindings s.rctors s.rbindings ast in
   case FST (infer_prog s.rmenv s.rcenv s.rtenv prog init_infer_state) of
   | Failure _ => Result "<type error>" (ast_repl_fun s asts)
   | Success (rm,rc,rt) =>
     case prog_repl_fun (s.rcompiler_state,s.rbc_state) prog of
     | NONE => Diverge
     | SOME ((cs,bs),ls) => Results ls
       (ast_repl_fun (update_state s ts cts bds rm rc rt cs bs) asts))`

val repl_fun_def = Define`
  repl_fun input = ast_repl_fun init_repl_fun_state (parse (lexer_fun input))`

val _ = export_theory()
