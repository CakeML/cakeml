(*
  Translates the Dafny to CakeML compiler.
*)
Theory dafny_compilerProg
Ancestors
  dafny_remove_assertProg dafny_compiler
Libs
  preamble ml_translatorLib basisFunctionsLib

val _ = translation_extends "dafny_remove_assertProg";

val r = translate dafny_compilerTheory.compile_def;
val r = translate dafny_compilerTheory.dfy_to_cml_def;
val r = translate dafny_compilerTheory.unpack_def;
val r = translate dafny_compilerTheory.cmlm_to_str_def;
val r = translate dafny_compilerTheory.main_function_def;

(* Sanity checks + Finalizing *)

val _ = type_of “main_function” = “:mlsexp$sexp -> mlstring”
        orelse failwith "The main_function has the wrong type.";

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of \
                  \dafny_compilerTheory.main_function_def");

Quote main = cakeml:
  print (main_function (Sexp.parse (TextIO.openStdIn ())));
End

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
