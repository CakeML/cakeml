(*
  Module for parsing and pretty-printing s-expressions.
*)
Theory SexpProg
Ancestors
  mlsexp
  TextIOProg
Libs
  preamble
  ml_translatorLib  (* translation_extends, register_type, .. *)
  basisFunctionsLib  (* add_cakeml *)


val _ = translation_extends "TextIOProg";

val _ = register_type “:mlsexp$sexp”;
val _ = register_type “:mlsexp$token”;

Quote add_cakeml:
  exception LexFail string
End

Quote add_cakeml:
  fun read_string_aux input acc =
    case TextIO.b_input1 input of
      NONE => raise LexFail "unterminated string literal"
    | SOME c =>
        if c = #"\"" then (String.implode (List.rev acc), input) else
        if c = #"\\" then
          (case TextIO.b_input1 input of
             NONE => read_string_aux input acc (* causes error: unterminated string *)
           | SOME e =>
               (if e = #"\\" then read_string_aux input (#"\""::acc) else
                if e = #"0"  then read_string_aux input (#"\000"::acc) else
                if e = #"n"  then read_string_aux input (#"\n"::acc) else
                if e = #"r"  then read_string_aux input (#"\""::acc) else
                if e = #"t"  then read_string_aux input (#"\""::acc) else
                  raise LexFail "unrecognised escape"))
        else
          read_string_aux input (c::acc)
End

Quote add_cakeml:
  fun read_string input = read_string_aux input []
End

Quote add_cakeml:
  fun read_symbol_aux input acc =
    case TextIO.b_input1 input of
      NONE => (String.implode (List.rev acc), input)
    | SOME c =>
        if c = #")" orelse Char.isSpace c
        then (String.implode (List.rev acc), input)
        else read_symbol_aux input (c::acc)
End

Quote add_cakeml:
  fun read_symbol input = read_symbol input []
End

Quote add_cakeml:
  fun lex_aux depth input acc =
    case TextIO.b_input1 input of
      NONE => if depth = 0 then (acc, input)
              else raise LexFail "missing closing parenthesis"
    | SOME c =>
        if Char.isSpace c then lex_aux depth input acc
        else if c = #"(" then lex_aux (depth + 1) input (OPEN::acc)
        else if c = #")" then
          (if depth = 0 then raise LexFail "too many closing parenthesis"
           else if depth = 1 then (CLOSE::acc, input)
           else lex_aux (depth - 1) input (CLOSE::acc))
        else if c = #"\"" then
          let val (s, input) = read_string input in
            if depth = 0 then ([SYMBOL s], input)
            else lex_aux depth input ((SYMBOL s)::acc) end
        else
          let val (s, input) = read_symbol input in
            if depth = 0 then ([SYMBOL s], input)
            else lex_aux depth input ((SYMBOL s)::acc) end
End

Quote add_cakeml:
  fun lex input = lex_aux 0 input []
End

val r = translate mlsexpTheory.parse_aux_def;

Quote add_cakeml:
  fun parse input = let
    val (rev_toks, input) = lex input
  in (parse_aux rev_toks [] [], input) end
End
