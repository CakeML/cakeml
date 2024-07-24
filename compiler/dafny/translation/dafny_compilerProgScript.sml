(*
 * Translates the Dafny to CakeML compiler.
 *)

open preamble basis
open dafny_to_cakemlProgTheory
open dafny_compilerTheory

val _ = new_theory "dafny_compilerProg";

val _ = translation_extends "dafny_to_cakemlProg";

val r = translate dafny_compilerTheory.sexp_program_m_def;
val r = translate dafny_compilerTheory.dfy_to_cml_def;

val r = translate numposrepTheory.n2l_def;
val r = translate ASCIInumbersTheory.n2s_def;
val r = translate ASCIInumbersTheory.HEX_def;
val r = translate ASCIInumbersTheory.num_to_dec_string_def;
val r = translate simpleSexpParseTheory.print_space_separated_def;
val r = translate simpleSexpParseTheory.strip_dot_def;
val r = translate simpleSexpParseTheory.escape_string_def;
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
val r = translate fromSexpTheory.scsexp_def;
val r = translate fromSexpTheory.expsexp_def;
val r = translate fromSexpTheory.type_defsexp_def;
val r = translate fromSexpTheory.decsexp_def;

val r = translate dafny_compilerTheory.cmlm_to_str_def;
val r = translate dafny_compilerTheory.main_function_def;

val _ = type_of “main_function” = “:mlstring -> mlstring”
        orelse failwith "The main_function has the wrong type.";

val main = process_topdecs
           `print (main_function (TextIO.inputAll TextIO.stdIn));`;

val prog =
  get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> REWRITE_RULE [ml_progTheory.ML_code_def]
  |> concl |> rator |> rator |> rand
  |> (fn tm => “^tm ++ ^main”)
  |> EVAL |> concl |> rand;

Definition dafny_compiler_prog_def:
  dafny_compiler_prog = ^prog
End

val _ = export_theory ();
