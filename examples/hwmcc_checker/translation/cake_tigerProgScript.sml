(*
  Defines the top-level binary cake_tiger.
*)
Theory cake_tigerProg
Ancestors
  aig_cert_fullProg
Libs
  preamble (* ml_translatorLib  *)basisFunctionsLib

val _ = translation_extends "aig_cert_fullProg";

(* Copied from examples/xlrup_checker/array/xlrup_arrayFullProgScript.sml *)
val usage_string = ‘

Usage: ./cake_tiger model witness [prefix]

’

fun drop_until p [] = []
  | drop_until p (x::xs) = if p x then x::xs else drop_until p xs;

val usage_string_tm =
  usage_string |> hd |> (fn QUOTE s => s) |> explode
  |> drop_until (fn c => c = #"\n") |> tl |> implode
  |> stringSyntax.fromMLstring;

Definition usage_string_def:
  usage_string = strlit ^usage_string_tm
End

val r = translate usage_string_def;

Quote add_cakeml:
  fun make_cert fmodel fwitness prefix =
  case TextIO.inputAllFrom (Some fmodel) of
    None => TextIO.output TextIO.stdErr "cannot read model file\n"
  | Some model =>
  case TextIO.inputAllFrom (Some fwitness) of
    None => TextIO.output TextIO.stdErr "cannot read witness file\n"
  | Some witness =>
  case make_cert_strings model witness of
    error (msg, _) => TextIO.output TextIO.stdErr msg
  | return certs => let
      fun write (name, cert) = let
        val oname = case prefix of None => name | Some pfx => pfx ^ name
        val ostrm = TextIO.openOut oname
        val _     = TextIO.output ostrm cert
        in TextIO.closeOut ostrm end
      in List.app write certs end
End

Quote add_cakeml:
  fun main_function () =
  case CommandLine.arguments () of
    [fmodel, fwitness] => make_cert fmodel fwitness None
  | [fmodel, fwitness, prefix] =>
      make_cert fmodel fwitness (Some prefix)
  | _ => TextIO.output TextIO.stdErr usage_string
End

Quote main = cakeml:
  main_function ();
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

Definition cake_tiger_prog_def:
  cake_tiger_prog = ^prog
End
