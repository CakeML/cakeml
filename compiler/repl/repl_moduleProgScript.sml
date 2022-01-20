(*
  Module for the configurable part of the REPL. Note that this file
  does not contain the code for the main loop of the REPL (which is at
  the end of bootstrap translation).

  This REPL module defines some references:
   - REPL.prompt : string ref
      -- the string that the default input function prints before reading
         user input (by default this is "> ")
   - REPL.isEOF : bool ref
      -- true means that all user input has been read (e.g. if we have
         reached the end of stdin)
   - REPL.nextString : string ref
      -- contains the next user input (if isEOF is false)
   - REPL.readNextString : (unit -> unit) ref
      -- the function that the REPL uses to read user input; it is this
         function that assigns new values to REPL.isEOF and REPL.nextString.

  At runtine, users are allowed (encouraged?) to change these references.
*)
open preamble
     ml_translatorTheory ml_translatorLib ml_progLib basisFunctionsLib
     candle_kernelProgTheory

val _ = new_theory"repl_moduleProg";

val _ = translation_extends "candle_kernelProg";

val _ = ml_prog_update (open_module "REPL");

val tidy_up =
  SIMP_RULE std_ss [candle_kernel_valsTheory.refs_defs,LENGTH_APPEND,LENGTH];

Theorem isEOF_def      = declare_new_ref "isEOF"      “F”           |> tidy_up
Theorem prompt_def     = declare_new_ref "prompt"     “strlit "> "” |> tidy_up
Theorem nextString_def = declare_new_ref "nextString" “strlit ""”   |> tidy_up

val _ = ml_prog_update open_local_block;

val _ = (append_prog o process_topdecs) `
  fun default_readNextString () =
    (TextIO.print (!prompt);
     case TextIO.inputLine TextIO.stdIn of
       None =>      (isEOF := True;  nextString := "")
     | Some line => (isEOF := False; nextString := line)); `

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  val readNextString = Ref default_readNextString; `

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* --- *)

val repl_prog = get_ml_prog_state () |> remove_snocs |> ml_progLib.get_prog;

val repl_prog_def = Define `repl_prog = ^repl_prog`;

Theorem Decls_repl_prog =
  ml_progLib.get_Decls_thm (get_ml_prog_state ())
  |> REWRITE_RULE [GSYM repl_prog_def];

val _ = export_theory();
