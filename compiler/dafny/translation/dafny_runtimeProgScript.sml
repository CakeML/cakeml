(*
  Module about the Dafny runtime.
*)

open preamble
open ml_translatorLib
open sexp_to_dafnyProgTheory
open cfTacticsLib (* process_topdecs *)
open basisFunctionsLib (* append_prog *)
open ml_progLib (* open_module *)
open integerTheory (* EDIV_DEF, INT_ABS, EMOD_DEF *)

val _ = new_theory "dafny_runtimeProg";

val _ = translation_extends "sexp_to_dafnyProg";

val cakeml = append_prog o process_topdecs;

val _ = ml_prog_update (open_module "Dafny");

(* Exceptions to support method returns and (labeled) breaks in loops *)

Quote cakeml:
  exception Return;
  exception Break;
  exception LabeledBreak string;
End

(* Functions to support Euclidian division and modulo *)

(* TODO Precondition *)
val _ = next_ml_names := ["ediv"]
val r = translate EDIV_DEF

val _ = next_ml_names := ["abs"]
val r = translate INT_ABS

(* TODO Precondition *)
val _ = next_ml_names := ["emod"]
val r = translate EMOD_DEF

(* Array functions *)

Quote cakeml:
  fun array_to_list arr = Array.foldr (fn x => fn xs => x :: xs) [] arr;
End

(* to_string functions to be used for "Dafny-conform" printing *)

Quote cakeml:
  fun bool_to_string b = if b then "true" else "false";
End

Quote cakeml:
  fun int_to_string i = Int.int_to_string #"-" i;
End

Quote cakeml:
  fun escape_char c =
    if c = #"'" then "\\'"
    else if c = #"\"" then "\\\""
    else if c = #"\\" then "\\\\"
    else if c = #"\000" then "\\0"
    else if c = #"\n" then "\\n"
    (* #"\r" leads to "not terminated with nil" exception *)
    else if c = #"\013" then "\\r"
    else if c = #"\t" then "\\t"
    else String.str c;
End

Quote cakeml:
  fun char_to_string c = String.concat ["'", escape_char c, "'"];
End

Quote cakeml:
  fun list_to_string f lst =
    String.concat ["[", String.concatWith ", " (List.map f lst), "]"];
End

Quote cakeml:
  fun char_list_to_string cs = list_to_string char_to_string cs;
End

Quote cakeml:
  (* f converts the tuple into a list of strings *)
  fun tuple_to_string f tpl =
    String.concat ["(", String.concatWith ", " (f tpl), ")"];
End

val _ = ml_prog_update (close_module NONE);

val _ = export_theory()
