(*
  Compiles the OCaml parser things.
 *)

open preamble compilationLib camlProgTheory;
open x64_configTheory;

val _ = new_theory "camlCompile";

val reader_compiled = save_thm("caml_compiled",
  compile_x64 "caml" caml_parse_prog_def);

val _ = export_theory ();

