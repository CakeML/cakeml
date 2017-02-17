open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     backendTheory
     basisProgTheory
open jsonTheory

(* COMPILING *)
val _ = Define`
  basic_prog = "val (x,y) = (3 + 5, 1); val y = \"hello\";"`;
val _ = Define`
  parse p = parse_prog (MAP FST (lexer_fun p))`;

EVAL ``parse basic_prog``;


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
