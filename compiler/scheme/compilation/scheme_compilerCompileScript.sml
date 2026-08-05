(*
  In-logic compilation of the Scheme-to-CakeML compiler
*)
Theory scheme_compilerCompile
Ancestors
  scheme_compilerProg
Libs
  preamble eval_cake_compile_x64Lib


Theorem scheme_compiler_compiled =
        eval_cake_compile_x64 "" scheme_compiler_prog_def
                                "scheme_compiler.S";

