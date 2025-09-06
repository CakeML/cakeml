(*
  Compiles the Dafny to CakeML compiler.
*)
Theory dafny_compilerCompile
Ancestors
  dafny_compilerProg
Libs
  preamble eval_cake_compile_x64Lib


Theorem dafny_compiler_compiled =
  eval_cake_compile_x64 "" dafny_compiler_prog_def "dafny_compiler.S";

