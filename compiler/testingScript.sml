open preamble
     lexer_funTheory
     cmlParseTheory
     inferTheory
     backendTheory
     basisProgTheory
open jsonTheory

(* COMPILING *)
val _ = Define`
  parse p = parse_prog (MAP FST (lexer_fun p))`;
val _ = Define`
  basic_prog = "1; val (x,y) = let val my1 = 1 in (3 + 5 mod 10, my1) end; fun foo(x:int) = [x,x,x]; val x = String.size \"bob\"; exception ExplorerException of string; fun mk_ref(x,v) = x := v"`;
val _ = Define`
  parsed_basic =
    case parse basic_prog of
         NONE => [] 
       | SOME x => x`;

EVAL ``parsed_basic``;
EVAL ``source_to_mod$ast_to_pres parsed_basic``;

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
