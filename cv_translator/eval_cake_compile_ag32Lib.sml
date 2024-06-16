(*
  Functions for in-logic evaluation of the CakeML compiler for ag32.
*)
structure eval_cake_compile_ag32Lib =
struct

local

  open eval_cake_compileLib;

  val ag32_arch_thms =
    { default_config_def  = ag32_configTheory.ag32_backend_config_def
    , default_config_simp = backend_ag32_cvTheory.set_asm_conf_ag32_backend_config
    , to_livesets_def     = backend_ag32Theory.to_livesets_ag32_def
    , compile_cake_def    = backend_ag32Theory.compile_cake_ag32_def
    , compile_cake_imp    = backend_ag32Theory.compile_cake_ag32_thm
    , cv_export_def       = backend_ag32_cvTheory.cv_ag32_export_def } : arch_thms;

in

  val eval_cake_compile_ag32 = eval_cake_compile ag32_arch_thms;
  val eval_cake_compile_ag32_with_conf = eval_cake_compile_with_conf ag32_arch_thms;
  val eval_cake_compile_ag32_general = eval_cake_compile_general ag32_arch_thms;

end

end
