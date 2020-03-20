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

(*
max_print_depth := 10
*)

val _ = intermediate_prog_prefix := "bot_";
Theorem bot_thm = compile_x64 1000 1000 "bot" bot_prog_def;
val _ = intermediate_prog_prefix := "";

val bot_data_code_def       = definition"bot_data_prog_def"
val bot_to_data_thm         = theorem"bot_to_data_thm"
val bot_config_def          = definition"bot_config_def"
val bot_x64_conf            = (rand o rator o lhs o concl) bot_thm
val bot_x64_conf_def        = mk_abbrev"bot_x64_conf" bot_x64_conf

Theorem bot_to_data_updated_thm =
  MATCH_MP (GEN_ALL to_data_change_config) bot_to_data_thm
  |> ISPEC ((rand o rator o lhs o concl) bot_thm)
  |> SIMP_RULE (srw_ss()) [];

Theorem bot_data_code_def = bot_data_code_def;

(* Produce .S files *)
val x64 = save_thm("bot_x64", compile_x64 500 500 (folder_str ^ "/bot_x64") bot_prog_def);

val _ = export_theory();
