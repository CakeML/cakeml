(*
  Compiles the patch example by evaluation inside the logic of HOL
*)
Theory patchCompile
Ancestors
  patchProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem patch_compiled =
  eval_cake_compile_x64 "" patch_prog_def "patch.S";

