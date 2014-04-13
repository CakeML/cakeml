open preamble;
open intLib wordsLib unifyLib;
open astTheory initialEnvTheory lexer_implTheory;
open compilerTheory;
open compilerTerminationTheory bytecodeEncodeTheory;

val _ = new_theory "progToBytecode";

(* TODO: Copied from repl_fun. *)
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

val get_all_asts_def = tDefine "get_all_asts" `
get_all_asts input =
  case lex_until_toplevel_semicolon input of
       NONE => Success []
     | SOME (tokens, rest_of_input) =>
        case parse_top tokens of
             NONE => Failure "<parse error>\n"
           | SOME top => 
               case get_all_asts rest_of_input of
                    Failure x => Failure x
                  | Success prog => Success (top::prog)`
(wf_rel_tac `measure LENGTH` >>
 rw [lex_until_toplevel_semicolon_LESS]);

val prog_to_bytecode_def = Define `
prog_to_bytecode p =
  case get_all_asts p of
       Failure x => Failure x
     | Success asts =>
         let (x,asts') = elab_prog init_type_bindings asts in
         case FST (infer_prog init_infer_decls [] init_tenvC init_type_env asts' infer$init_infer_state) of
              Failure x => Failure x
            | Success x =>
                let bc = compile_prog (Tdec initial_program::asts') in
                  Success bc`;

val prog_to_bytecode_string_def = Define `
prog_to_bytecode_string p =
  case prog_to_bytecode p of
     | Failure x => Failure x
     | Success bcs => Success (FLAT (MAP (\inst. bc_inst_to_string inst ++ "\n") bcs))`;

val prog_to_bytecode_encoded_def = Define `
prog_to_bytecode_encoded p =
  case prog_to_bytecode p of
     | Failure x => Failure x
     | Success bcs => Success (encode_bc_insts bcs : word64 list option)`;

val _ = export_theory ();
