(*
  Defines the top-level binary cake_tiger.
*)
Theory cake_tigerProg
Ancestors
  infer_cv  (* TODO Remove once we have a proper CF spec *)
  aig_cert_fullProg
Libs
  cv_transLib preamble ml_translatorLib basisFunctionsLib

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
  case (print "parsing..."; parse_and_process model witness) of
    Error (msg, _) => TextIO.output TextIO.stdErr msg
  | Return
      (mcirc, (mreset, (mnext, (mpreds, (mcnstrs, (mlive, (mlatches,
        (wcirc, (wreset, (wnext, (wpreds, (wcnstrs, (wlive, (wlatches, interv)))))))))))))) =>
    let
      fun write (name, cert) = let
        val oname =
          (case prefix of None => name | Some pfx => pfx ^ name) ^ ".cnf"
        val ostrm = TextIO.openOut oname
        val _     = TextIO.output ostrm cert
      in TextIO.closeOut ostrm end
      val _ = print "parsing finished! continuing with encodings..."
      val _ = write (
        make_reset_string mcirc mreset mcnstrs mlatches wcirc wreset wcnstrs
          wlatches)
      val _ = write (
        make_transition_string mcirc mnext mcnstrs mlatches wcirc wnext wcnstrs
          wlatches)
      val _ = write (
        make_property_string mcirc mcnstrs mpreds wcirc wcnstrs wpreds)
      val _ = write (
        make_base_string wcirc wreset wcnstrs wpreds wlatches)
      val _ = write (
        make_step_string wcirc wnext wcnstrs wpreds wlatches)
      val _ = write (
        make_liveness_string mcirc mcnstrs mlive
          wcirc wnext wcnstrs wpreds wlive wlatches interv)
      val _ = write (
        make_decrease_string wcirc wnext wcnstrs wpreds wlive wlatches interv)
      val _ = write (
        make_closure_string wcirc wnext wcnstrs wpreds wlive wlatches interv)
      val _ = write (
        make_consistent_string wcirc wnext wcnstrs wpreds wlive wlatches interv)
    in () end
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

(* TODO Remove once we have a proper CF spec *)
(* for testing (type inference) ***********************************************)

(*
val _ = cv_auto_trans inferTheory.init_config_def;

val _ = cv_trans_deep_embedding EVAL cake_tiger_prog_def;

val basis_types = cv_eval “infertype_prog init_config cake_tiger_prog”;
*)
