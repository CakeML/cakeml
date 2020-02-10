(*
  x64 compilation
*)

open preamble botProgTheory
open compilationLib

(* Compile the program *)

val _ = new_theory "bot_x64Compile"

val folder_str =
  Option.valOf (OS.Process.getEnv "SANDBOX_FOLDER")
  handle _ => ".";

(* Produce .S files *)
val x64 = save_thm("bot_x64", compile_x64 500 500 (folder_str ^ "/bot_x64") bot_prog_def);

val _ = export_theory();
