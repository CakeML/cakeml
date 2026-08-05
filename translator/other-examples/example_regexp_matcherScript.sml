(*
  This is a simple example of applying the translator to a
  matcher for regular expressions.
*)
Theory example_regexp_matcher
Ancestors
  arithmetic list sorting regexpMatch ml_translator
Libs
  ml_translatorLib

(* matcher -- recursion over a datatype *)

val _ = register_type ``:'a # 'b``;

val res = translate MEMBER_def
val res = translate (match_def |> REWRITE_RULE [MEMBER_INTRO])

