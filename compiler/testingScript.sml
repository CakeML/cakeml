load "compilerTheory";
load "lexer_funTheory";
open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     backendTheory
open jsonTheory presLangTheory
open astTheory source_to_modTheory

val _ = computeLib.add_funs [pat_bindings_def];

(* COMPILING *)
val parse_def = Define`
  parse p = parse_prog (lexer_fun p)`;

(* Basic string representation of a program. *)
val basic_prog_def = Define`
  basic_prog = "val x = 3 + 5;"`;

(* The input program, parsed *)
val parsed_basic_def = Define`
  parsed_basic =
    case parse basic_prog of
         NONE => []
       | SOME x => x`;

(* If parsing breaks, we can use the pre-parsed program for testing. Note that
* it lacks traces *)
val parsed_basic_def = Define`
  parsed_basic = [Tdec
      (Dlet (Pcon NONE [Pvar "x"; Pvar "y"])
         (Con NONE
            [App Opapp
               [App Opapp [Var (Short "+"); Lit (IntLit 3)];
                Lit (IntLit 5)]; Lit (IntLit 1)]));
    Tdec (Dlet (Pvar "y") (Lit (StrLit "hello")))]`;

EVAL ``parsed_basic``;

(* ModLang representation of the input program *)
val mod_prog_def = Define`
  mod_prog = SND (source_to_mod$compile source_to_mod$empty_config parsed_basic)`;

EVAL ``mod_prog``;
(* Test running the compiler backend on the basic program *)
EVAL ``backend$compile_explorer backend$prim_config parsed_basic``;

(* PRESLANG *)
(* Test converting mod to pres *)
EVAL ``mod_to_pres mod_prog``;

(* Test converting pres to json *)
EVAL ``pres_to_json (mod_to_pres mod_prog)``;

(* Test converting json to string *)
EVAL ``json_to_string (pres_to_json (mod_to_pres mod_prog))``;

(* Unit test JSON *)
val _ = Define `
  json =
    (Object [
              ("modLang", Array [
                          Null;
                          Bool T;
                          Bool F;
                          String "Hello, World!";
                          Object [("n", Null); ("b", Bool T)];
                          Int (-9999999999999999999999999999999999999999999999999999999122212)
                        ]
              )
            ]
    )`;

EVAL ``json_to_string json``;
EVAL ``pres_to_json (Dexn ["modul"; "modul1"] "conN" [Tvar "TVARN"; Tvar_db 5])``
