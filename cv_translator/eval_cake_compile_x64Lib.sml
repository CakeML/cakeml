(*
  Functions for in-logic evaluation of the CakeML compiler for x64.
*)
structure eval_cake_compile_x64Lib =
struct

local

  open eval_cake_compileLib;

  val x64_arch_thms =
    { default_config_def       = x64_configTheory.x64_backend_config_def
    , default_config_simp      = backend_x64_cvTheory.set_asm_conf_x64_backend_config
    , to_livesets_def          = backend_x64Theory.to_livesets_x64_def
    , compile_cake_def         = backend_x64Theory.compile_cake_x64_def
    , compile_cake_imp         = backend_x64Theory.compile_cake_x64_thm
    , compile_cake_explore_def = backend_x64Theory.compile_cake_explore_x64_def
    , cv_export_def            = backend_x64_cvTheory.cv_x64_export_def } : arch_thms;

in

  val eval_cake_compile_x64 =
      eval_cake_compile x64_arch_thms;

  val eval_cake_compile_x64_with_conf =
      eval_cake_compile_with_conf x64_arch_thms;

  val eval_cake_compile_explore_x64 =
      eval_cake_compile_explore x64_arch_thms;

  val eval_cake_compile_explore_x64_with_conf =
      eval_cake_compile_explore_with_conf x64_arch_thms;

  val eval_cake_compile_x64_general =
      eval_cake_compile_general x64_arch_thms;

end

end
