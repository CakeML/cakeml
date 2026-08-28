(*
  Generates the cake_tiger binary for ARM8.
*)
Theory cake_tigerARM8Compile
Ancestors
  cake_tigerProgProof
Libs
  preamble eval_cake_compile_arm8Lib

Theorem cake_tiger_compiled =
  eval_cake_compile_arm8 "" main_prog_def "cake_tiger_arm8.S";
