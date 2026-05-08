(*
  Compiles the distrup example by evaluation inside the logic of HOL
*)
Theory distrupCompile
Ancestors
  distrup_fullProg
Libs
  preamble eval_cake_compile_x64Lib x64_configTheory

Theorem distrup_array_compiled =
  eval_cake_compile_x64_general
    { prefix               = ""
    , conf_def             = x64_configTheory.x64_backend_config_def
    , prog_def             = distrup_prog_def
    , run_as_explorer      = false
    , main_return          = true
    , output_filename      = "cake_distrup.S"
    , output_conf_filename = NONE };

