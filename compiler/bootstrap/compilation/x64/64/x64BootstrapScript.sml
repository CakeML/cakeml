(*
  Evaluate the 64-bit version of the compiler into x64 machine code.
*)
open preamble compiler64ProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "x64Bootstrap"

Theorem compiler64_compiled =
  eval_cake_compile_x64_general
    { prefix               = ""
    , conf_def             = x64_configTheory.x64_backend_config_def
    , prog_def             = compiler64_prog_def
    , output_filename      = "cake.S"
    , output_conf_filename = SOME "config_enc_str.txt" };

val _ = export_theory ();
