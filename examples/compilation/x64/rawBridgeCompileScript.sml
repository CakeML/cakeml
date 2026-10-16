(*
  Compiles the rawBridge example by evaluation inside the logic of HOL
*)
Theory rawBridgeCompile
Ancestors
  rawBridgeProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem rawBridge_compiled =
  eval_cake_compile_x64 "" rawBridge_prog_def "rawBridge.S";
