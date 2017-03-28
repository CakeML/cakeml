load "cfTacticsBaseLib";
open preamble
     cmlParseTheory
     inferTheory
     backendTheory
     cfTacticsBaseLib
open jsonTheory presLangTheory
open astTheory source_to_modTheory
open stringTheory;

val _ = computeLib.add_funs [pat_bindings_def];

(* COMPILING *)
val parse_def = Define`
  parse p = parse_prog (lexer_fun p)`;

val parsed_basic = parse_topdecs
  `
  val x = 3 + 5;
  fun fromList l =
    let val arr = array (List.length l) 0
      fun f l i =
       case l of
          [] => arr
        | (h::t) => (update arr i h; f t (i + 1))
    in f l 0 end`;
(* The input program, parsed *)
val parsed_basic_def = Define`
  parsed_basic = ^parsed_basic`;

EVAL ``parsed_basic``;

(* ModLang representation of the input program *)
val mod_prog_def = Define`
  mod_prog = SND (source_to_mod$compile source_to_mod$empty_config parsed_basic)`;

EVAL ``mod_prog``;
(* Test running the compiler backend on the basic program *)
EVAL ``backend$compile_explorer backend$prim_config parsed_basic``;

(* Convert output to string *)
EVAL ``append (backend$compile_explorer backend$prim_config parsed_basic)``;

(* PRESLANG *)
(* Test converting mod to pres *)
EVAL ``mod_to_pres mod_prog``;

(* Test converting pres to json *)
EVAL ``pres_to_json (mod_to_pres mod_prog)``;

(* Test converting json to string *)
EVAL ``json_to_string (pres_to_json (mod_to_pres mod_prog))``;

val tm = ``"hel\"lo"``;
val _ = print ("\n\n" ^ stringSyntax.fromHOLstring tm ^ "\n\n");

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
