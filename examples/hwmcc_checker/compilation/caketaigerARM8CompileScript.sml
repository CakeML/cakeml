(*
  Generates the caketaiger binary for ARM8.
*)
Theory caketaigerARM8Compile
Ancestors
  caketaigerProgProof
Libs
  preamble eval_cake_compile_arm8Lib

Theorem caketaiger_compiled =
  eval_cake_compile_arm8 "" main_prog_def "caketaiger_arm8.S";
