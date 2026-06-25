(*
  Generates the cake_tiger binary.
*)
Theory cake_tigerCompile
Ancestors
  cake_tigerProg x64_config
Libs
  preamble eval_cake_compile_x64Lib

Definition x64_config'_def:
  x64_config' =
  let x64_stack_conf = x64_backend_config.stack_conf with perf_calls := T in
    x64_backend_config with stack_conf := x64_stack_conf
End

Theorem cake_tiger_compiled =
  eval_cake_compile_x64_with_conf "" x64_config'_def cake_tiger_prog_def "cake_tiger.S";
