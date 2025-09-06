(*
  Compiles the iocat example by evaluation inside the logic of HOL
*)
Theory iocatCompile
Ancestors
  iocatProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem iocat_compiled =
  eval_cake_compile_x64 "" cat_prog_def "iocat.S";

