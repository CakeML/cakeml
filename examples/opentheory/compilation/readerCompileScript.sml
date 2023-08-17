(*
  Compiles the OpenTheory article checker in the logic.
*)
open preamble compilationLib readerProgTheory
open x64_configTheory
open costLib

val _ = new_theory "readerCompile"

val reader_compiled = save_thm("reader_compiled",
  compile_x64 "reader" reader_prog_def);

(* the following stores a pretty printer the dataLang program in a textfile *)

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val _ = install_naming_overloads "readerCompile";
val _ = write_to_file (fetch "-" "data_prog_def");

val _ = export_theory ();
