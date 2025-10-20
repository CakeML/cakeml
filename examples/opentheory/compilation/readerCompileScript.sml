(*
  Compiles the OpenTheory article checker in the logic.
*)
Theory readerCompile
Ancestors
  readerProg x64_config
Libs
  preamble eval_cake_compile_x64Lib

(* open costLib *)

Theorem reader_compiled =
  eval_cake_compile_x64 "" reader_prog_def "reader.S";

(* the following stores a pretty printer the dataLang program in a textfile

Overload monad_unitbind[local] = ``data_monad$bind``
Overload return[local] = ``data_monad$return``
val _ = monadsyntax.temp_add_monadsyntax()

val _ = install_naming_overloads "readerCompile";
val _ = write_to_file (fetch "-" "data_prog_def");

*)

