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
  make_fname pfx s = concat [pfx; s; «.cnf»]
End
val r = translate make_fname_def;

(* By splitting the writes we can write separate CFCML specifications for them,
   making the proof of make_cert's postcondition cleaner.
   By writing immediately after generating the string (as opposed to doing all
   writing at the end), we don't need to keep all strings around at the same
   time. *)

Quote add_cakeml:
  fun write_reset
    prefix maig mreset mcnstrs mlatches waig wreset wcnstrs wlatches klatches
  =
  let
    (* val _ = print "making reset...\n" *)
    val (name, str) =
      make_reset_string maig mreset mcnstrs mlatches waig wreset wcnstrs
        wlatches klatches
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_transition
    prefix maig mnext mcnstrs mlatches waig wnext wcnstrs wlatches klatches
  =
  let
    (* val _ = print "making transition...\n" *)
    val (name, str) =
      make_transition_string maig mnext mcnstrs mlatches waig wnext wcnstrs
        wlatches klatches
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_property prefix maig mcnstrs mpreds waig wcnstrs wpreds
  =
  let
    (* val _ = print "making property...\n" *)
    val (name, str) =
      make_property_string maig mcnstrs mpreds waig wcnstrs wpreds
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_base prefix waig wreset wcnstrs wpreds wlatches
  =
  let
    (* val _ = print "making base...\n" *)
    val (name, str) = make_base_string waig wreset wcnstrs wpreds wlatches
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_step prefix waig wnext wcnstrs wpreds wlatches
  =
  let
    (* val _ = print "making step...\n" *)
    val (name, str) = make_step_string waig wnext wcnstrs wpreds wlatches
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_liveness
    prefix maig mcnstrs mlive waig wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    (* val _ = print "making liveness...\n" *)
    val (name, str) =
      make_liveness_string
       maig mcnstrs mlive waig wnext wcnstrs wpreds wlive wlatches interv
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_decrease prefix waig wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    (* val _ = print "making decrease...\n" *)
    val (name, str) =
      make_decrease_string waig wnext wcnstrs wpreds wlive wlatches interv
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_closure prefix waig wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    (* val _ = print "making closure...\n" *)
    val (name, str) =
      make_closure_string waig wnext wcnstrs wpreds wlive wlatches interv
  in TextIO.outputFile (make_fname prefix name) str end
End

Quote add_cakeml:
  fun write_consistent prefix waig wnext wcnstrs wpreds wlive wlatches interv
  =
  let
    (* val _ = print "making consistent...\n" *)
    val (name, str) =
      make_consistent_string waig wnext wcnstrs wpreds wlive wlatches interv
  in TextIO.outputFile (make_fname prefix name) str end
End

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
  | Return (maiger, (waiger, ms)) =>
  case ((* print "processing and checking...\n"; *) process_and_check maiger waiger ms) of
    Error msg => TextIO.print_err msg
  | Return
      (maig, (mreset, (mnext, (mpreds, (mcnstrs, (mlive, (mlatches,
        (waig, (wreset, (wnext, (wpreds, (wcnstrs, (wlive, (wlatches,
          (interv, klatches))))))))))))))) => (
      write_reset
        prefix maig mreset mcnstrs mlatches waig wreset wcnstrs
        wlatches klatches;
      write_transition
        prefix maig mnext mcnstrs mlatches waig wnext wcnstrs
        wlatches klatches;
      write_property prefix maig mcnstrs mpreds waig wcnstrs wpreds;
      write_base prefix waig wreset wcnstrs wpreds wlatches;
      write_step prefix waig wnext wcnstrs wpreds wlatches;
      write_liveness
        prefix maig mcnstrs mlive waig wnext wcnstrs wpreds wlive wlatches
        interv;
      write_decrease prefix waig wnext wcnstrs wpreds wlive wlatches interv;
      write_closure prefix waig wnext wcnstrs wpreds wlive wlatches interv;
      write_consistent prefix waig wnext wcnstrs wpreds wlive wlatches interv;
      print "SUCCESS"
    )
End

Quote add_cakeml:
  fun main () =
  case CommandLine.arguments () of
    [fmodel, fwitness] => make_cert fmodel fwitness ""
  | [fmodel, fwitness, prefix] =>
      (* length of prefix + condition name + file extension must be less than
         65536 *)
      if 65522 <= String.size prefix
      then TextIO.print_err "prefix too long"
      else make_cert fmodel fwitness prefix
  | _ => TextIO.print_err usage_string
End

(* TODO Remove once we have a proper CF spec *)
(* for testing (type inference) ***********************************************)

(*
Quote main = cakeml:
  main ();
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

val _ = cv_auto_trans inferTheory.init_config_def;

val _ = cv_trans_deep_embedding EVAL cake_tiger_prog_def;

val basis_types = cv_eval “infertype_prog init_config cake_tiger_prog”;
*)
