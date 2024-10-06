
signature eval_cake_compileLib =
sig

  include Abbrev

  type arch_thms =
    { default_config_def       : thm
    , default_config_simp      : thm
    , to_livesets_def          : thm
    , compile_cake_def         : thm
    , compile_cake_imp         : thm
    , compile_cake_explore_def : thm
    , cv_export_def            : thm }

  type comp_input =
    { prefix               : string
    , conf_def             : thm
    , prog_def             : thm
    , run_as_explorer      : bool
    , output_filename      : string
    , output_conf_filename : string option }

  val eval_cake_compile :
    arch_thms -> string -> thm -> string -> thm

  val eval_cake_compile_explore :
    arch_thms -> string -> thm -> string -> thm

  val eval_cake_compile_with_conf :
    arch_thms -> string -> thm -> thm -> string -> thm

  val eval_cake_compile_explore_with_conf:
    arch_thms -> string -> thm -> thm -> string -> thm

  val eval_cake_compile_general :
    arch_thms -> comp_input -> thm

end
