(*
  Translation of printing to CakeML sexp
*)
Theory to_sexpProg
Ancestors
  ast fromSexp simpleSexpParse
Libs
  preamble basis

val _ = translation_extends "basisProg";

val _ = register_type “:ast$dec”;

(* TODO: remove all preconditions *)

val r = translate numposrepTheory.n2l_def;
val r = translate ASCIInumbersTheory.n2s_def;
val r = translate ASCIInumbersTheory.HEX_def;
val r = translate ASCIInumbersTheory.num_to_dec_string_def;
val r = translate simpleSexpParseTheory.print_space_separated_def;
val r = translate simpleSexpParseTheory.strip_dot_def;
val r = translate simpleSexpParseTheory.escape_string_def;
val r = translate listTheory.EL;
val r = translate simpleSexpParseTheory.print_sexp_def;
val r = translate fromSexpTheory.listsexp_def;
val r = translate fromSexpTheory.locnsexp_def;
val r = translate fromSexpTheory.locssexp_def;
val r = translate stringTheory.isPrint_def;
val r = translate ASCIInumbersTheory.num_to_hex_string_def;
val r = translate fromSexpTheory.encode_control_def;
val r = translate fromSexpTheory.SEXSTR_def;
val r = translate fromSexpTheory.litsexp_def;
val r = translate fromSexpTheory.optsexp_def;
val r = translate fromSexpTheory.idsexp_def;
val r = translate fromSexpTheory.typesexp_def;
val r = translate fromSexpTheory.patsexp_def;
val r = translate fromSexpTheory.opsexp_def;
val r = translate fromSexpTheory.lopsexp_def;
val r = translate fromSexpTheory.expsexp_def;
val r = translate fromSexpTheory.type_defsexp_def;
val r = translate fromSexpTheory.decsexp_def;

