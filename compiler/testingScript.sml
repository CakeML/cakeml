open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     backendTheory
     basisProgTheory
open jsonTheory presLangTheory

(* COMPILING *)
val parse_def = Define`
  parse p = parse_prog (lexer_fun p)`;
val basic_prog_def = Define`
  basic_prog = "val x = 3 + 5"`;
val parsed_basic_def = Define`
  parsed_basic =
    case parse basic_prog of
         NONE => [] 
       | SOME x => x`;

EVAL ``parsed_basic``;

val mod_prog_def = Define`
  mod_prog = SND (source_to_mod$compile source_to_mod$empty_config parsed_basic)`;

EVAL ``mod_prog``;
EVAL ``mod_to_pres mod_prog``

    let res = [modLang$to_json p] in
    let c = c with source_conf := c' in

(* JSON *)
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
