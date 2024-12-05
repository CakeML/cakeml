(*
  Functions for in-logic evaluation of the CakeML compiler for arm8.
*)
structure eval_cake_compile_arm8Lib =
struct

local

  open eval_cake_compileLib;

  val arm8_arch_thms =
    { default_config_def       = arm8_configTheory.arm8_backend_config_def
    , default_config_simp      = backend_arm8_cvTheory.set_asm_conf_arm8_backend_config
    , to_livesets_def          = backend_arm8Theory.to_livesets_arm8_def
    , compile_cake_def         = backend_arm8Theory.compile_cake_arm8_def
    , compile_cake_imp         = backend_arm8Theory.compile_cake_arm8_thm
    , compile_cake_explore_def = backend_arm8Theory.compile_cake_explore_arm8_def
    , cv_export_def            = backend_arm8_cvTheory.cv_arm8_export_def } : arch_thms;

in

  val eval_cake_compile_arm8 =
      eval_cake_compile arm8_arch_thms;

  val eval_cake_compile_arm8_with_conf =
      eval_cake_compile_with_conf arm8_arch_thms;

  val eval_cake_compile_explore_arm8 =
      eval_cake_compile_explore arm8_arch_thms;

  val eval_cake_compile_explore_arm8_with_conf =
      eval_cake_compile_explore_with_conf arm8_arch_thms;

  val eval_cake_compile_arm8_general =
      eval_cake_compile_general arm8_arch_thms;

end

end
