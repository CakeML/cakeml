open HolKernel Parse boolLib bossLib lcsymtacs
open lexer_implTheory cmlParseTheory astTheory inferTheory compilerTheory
     printerTheory compilerTerminationTheory bytecodeEvalTheory replTheory
     elabTheory

val _ = new_theory "repl_fun";

val _ = type_abbrev ("elaborator_state", ``:tdef_env # ctor_env``);

val elaborate_top_def = Define `
elaborate_top ((types, constructors) : elaborator_state) ast_top =
  let (new_types, new_constructors, top) = elab_top types constructors ast_top in
    ((new_types++types, new_constructors ++ constructors), top)`;

val initial_elaborator_state_def = Define `
initial_elaborator_state : elaborator_state = (init_repl_state.type_bindings, [])`;

val inf_type_to_string_def = tDefine "inf_type_to_string" `
(inf_type_to_string (Infer_Tuvar _) ⇔ "<unification variable>") ∧
(inf_type_to_string (Infer_Tvar_db n) ⇔ num_to_dec_string n) ∧
(inf_type_to_string (Infer_Tapp [t1;t2] TC_fn) ⇔ 
  "(" ++ inf_type_to_string t1 ++ "->" ++ inf_type_to_string t2 ++ ")") ∧
(inf_type_to_string (Infer_Tapp ts TC_fn) ⇔ "<bad function type>") ∧
(inf_type_to_string (Infer_Tapp ts TC_tup) ⇔
  "(" ++ inf_types_to_string ts ++ ")") ∧
(inf_type_to_string (Infer_Tapp [] tc) ⇔ tc_to_string tc) ∧
(inf_type_to_string (Infer_Tapp ts tc) ⇔ 
  "(" ++ inf_types_to_string ts ++ ") " ++ tc_to_string tc) ∧
(inf_types_to_string [] ⇔ "") ∧
(inf_types_to_string [t] ⇔ inf_type_to_string t) ∧
(inf_types_to_string (t::ts) ⇔ inf_type_to_string t ++ ", " ++ inf_types_to_string ts)`
(WF_REL_TAC `measure (\x. case x of INL x => infer_t_size x | INR x => infer_t1_size x)`);

val inf_tenv_to_string_map_def = Define `
(inf_tenv_to_string_map [] ⇔ FEMPTY) ∧
(inf_tenv_to_string_map ((x, (_, t)) :: tenv) ⇔
inf_tenv_to_string_map tenv |+ (x, inf_type_to_string t))`;

val _ = type_abbrev ("inferencer_state", ``:(modN, (varN, num # infer_t) env) env # tenvC # (varN, num # infer_t) env``);

val infertype_top_def = Define `
infertype_top ((module_type_env, constructor_type_env, type_env) :inferencer_state) ast_top =
  case FST (infer_top module_type_env constructor_type_env type_env ast_top infer$init_infer_state) of
     | Failure _ => Failure "<type error>"
     | Success (new_module_type_env, new_constructor_type_env, new_type_env) =>
        Success ((new_module_type_env ++ module_type_env,
                  new_constructor_type_env ++ constructor_type_env,
                  new_type_env ++ type_env),
                 inf_tenv_to_string_map new_type_env)`;

val initial_inferencer_state_def = Define `
initial_inferencer_state : inferencer_state = ([], init_tenvC, infer$init_type_env)`;

val _ = Hol_datatype`repl_fun_state = <|
  relaborator_state : elaborator_state;
  rinferencer_state : inferencer_state;
  rcompiler_state  : compiler_state |>`

val initial_program_def = Define `
initial_program =
   Dlet (Pcon NONE [Pvar "ref";
                    Pvar "!";
                    Pvar "~";
                    Pvar ":=";
                    Pvar "=";
                    Pvar ">=";
                    Pvar "<=";
                    Pvar ">";
                    Pvar "<";
                    Pvar "mod";
                    Pvar "div";
                    Pvar "*";
                    Pvar "-";
                    Pvar "+"])
        (Con NONE [(Fun "x" (Uapp Opref (Var(Short"x"))));
                   (Fun "x" (Uapp Opderef (Var(Short"x"))));
                   (Fun "x" (App (Opn Minus) (Lit (IntLit 0)) (Var(Short"x"))));
                   (Fun "x" (Fun"y"(App Opassign (Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App Equality(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Geq)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Leq)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Gt)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opb Lt)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Modulo)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Divide)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Times)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Minus)(Var(Short"x"))(Var(Short"y")))));
                   (Fun "x" (Fun"y"(App(Opn Plus)(Var(Short"x"))(Var(Short"y")))))])`;

val initial_program_types_def = Define `
initial_program_types =
  FEMPTY |+ ("ref", "UNUSED") 
         |+ ("!", "UNUSED")
         |+ ("~", "UNUSED")
         |+ (":=", "UNUSED")
         |+ ("=", "UNUSED")
         |+ (">=", "UNUSED")
         |+ ("<=", "UNUSED")
         |+ ("<", "UNUSED")
         |+ (">", "UNUSED")
         |+ ("mod", "UNUSED")
         |+ ("div", "UNUSED")
         |+ ("*", "UNUSED")
         |+ ("-", "UNUSED")
         |+ ("+", "UNUSED")`;

val compile_primitives_def = Define`
  compile_primitives =
    compile_top initial_program_types init_compiler_state
    (Tdec initial_program)`;

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
  let (m0,c,e) = s.rinferencer_state in
  s with <| rinferencer_state := (BUTLASTN (LENGTH m0) (strip_mod_env (FST is)) ++ m0,c,e)
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
             let (css,csf,code) = compile_top types s.rcompiler_state top in
               Success (code,update_state s es is css,update_state_err s is csf)`

val install_code_def = Define `
  install_code m code bs =
    bs with <| code   := bs.code ++ REVERSE code
             ; pc     := next_addr bs.inst_length bs.code
             ; output := ""
             ; cons_names := m
             |>`;

val PrintE_def = Define`PrintE = (MAP PrintC "raise ")++[Print;PrintC(#"\n")]`

val initial_bc_state_def =  Define`
  initial_bc_state =
  let bs =
    <|stack := [];
      code := PrintE++[Stop];
      pc := 0;
      refs := FEMPTY;
      handler := 0;
      clock := NONE;
      output := "";
      cons_names := [];
      inst_length := real_inst_length |> in
  THE (bc_eval (install_code [] (SND (SND compile_primitives)) bs))`

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
            case bc_eval (install_code (cpam s.rcompiler_state) code bs) of
              (* case: evaluation of code does not terminate *)
              NONE => Diverge
            | (* case: evaluation terminated, analyse result and continue *)
              SOME new_bs =>
                let new_s = if bc_fetch new_bs = SOME Stop then s_exc else s in
                Result new_bs.output (main_loop (new_bs,new_s) rest_of_input) ` tac ;

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
