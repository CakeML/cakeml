(*
  Compile the encoder for the sudoku puzzle
*)
Theory example_funsCompile
Ancestors
  example_funsProg
Libs
  preamble eval_cake_compile_x64Lib eval_cake_compile_arm8Lib

Theorem example_funs_compiled_x64 =
  eval_cake_compile_x64 "x64_" example_funs_prog_def
                              "example_funs_x64.S";

Theorem example_funs_compiled_arm8 =
  eval_cake_compile_arm8 "arm8_" example_funs_prog_def
                                "example_funs_arm8.S";
