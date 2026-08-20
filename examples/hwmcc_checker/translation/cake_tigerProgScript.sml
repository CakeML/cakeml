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

(* TODO Can we turn this into a cleaner, general mechanism using Quote and move it
   to preamble perhaps? *)
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

Definition make_fname_def:
  (make_fname NONE s = s ^ «.cnf») ∧
  (make_fname (SOME pfx) s = concat [pfx; s; «.cnf»])
End
val r = translate make_fname_def;

Quote add_cakeml:
  fun make_cert fmodel fwitness prefix =
  case TextIO.inputAllFrom (Some fmodel) of
    None => TextIO.print_err "cannot read model file\n"
  | Some model =>
  case TextIO.inputAllFrom (Some fwitness) of
    None => TextIO.print_err "cannot read witness file\n"
  | Some witness =>
  case ((* print "parsing...\n";  *)parse model witness) of
    Error (msg, _) => TextIO.print_err msg
  | Return (maig, (waig, ms)) =>
  case ((* print "processing and checking...\n"; *) process_and_check maig waig ms) of
    Error msg => TextIO.print_err msg
  | Return
      (mcirc, (mreset, (mnext, (mpreds, (mcnstrs, (mlive, (mlatches,
        (wcirc, (wreset, (wnext, (wpreds, (wcnstrs, (wlive, (wlatches,
          (interv, klatches))))))))))))))) =>
    let
      (* val _ = print "making reset...\n" *)
      val (name, str) =
        make_reset_string mcirc mreset mcnstrs mlatches wcirc wreset wcnstrs
          wlatches klatches
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making transition...\n" *)
      val (name, str) =
        make_transition_string mcirc mnext mcnstrs mlatches wcirc wnext wcnstrs
          wlatches klatches
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making property...\n" *)
      val (name, str) =
        make_property_string mcirc mcnstrs mpreds wcirc wcnstrs wpreds
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making base...\n" *)
      val (name, str) =
        make_base_string wcirc wreset wcnstrs wpreds wlatches
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making step...\n" *)
      val (name, str) =
        make_step_string wcirc wnext wcnstrs wpreds wlatches
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making liveness...\n" *)
      val (name, str) =
        make_liveness_string mcirc mcnstrs mlive
          wcirc wnext wcnstrs wpreds wlive wlatches interv
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making decrease...\n" *)
      val (name, str) =
        make_decrease_string wcirc wnext wcnstrs wpreds wlive wlatches interv
      val _ = outputFile (make_fname prefix name) str
      (* val _ = print "making closure...\n" *)
      val (name, str) =
        make_closure_string wcirc wnext wcnstrs wpreds wlive wlatches interv
      val _ = outputFile (make_fname prefix name) str
     (* val _ = print "making consistent...\n" *)
      val (name, str) =
        make_consistent_string wcirc wnext wcnstrs wpreds wlive wlatches interv
      val _ = outputFile (make_fname prefix name) str
      val _ = print "SUCCESS"
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
