(*
  Functions for in-logic evaluation of the CakeML compiler for wasm.
*)
structure eval_cake_compile_wasmLib =
struct

local

  open eval_cake_compileLib;

  val wasm_arch_thms =
    { default_config_def       = wasm_configTheory.wasm_backend_config_def
    , default_config_simp      = backend_wasm_cvTheory.set_asm_conf_wasm_backend_config
    , to_livesets_def          = backend_wasmTheory.to_livesets_wasm_def
    , compile_cake_def         = backend_wasm_cvTheory.cake_to_wasm_binary_def
    , compile_cake_imp         = backend_wasm_cvTheory.cake_to_wasm_binary_IMP
    , compile_cake_explore_def = backend_wasmTheory.compile_cake_explore_wasm_def
    , cv_export_def            = boolTheory.TRUTH } : arch_thms;

in

  val eval_cake_compile_wasm =
      eval_cake_compile wasm_arch_thms;

  val eval_cake_compile_wasm_with_conf =
      eval_cake_compile_with_conf wasm_arch_thms;

  val eval_cake_compile_explore_wasm =
      eval_cake_compile_explore wasm_arch_thms;

  val eval_cake_compile_explore_wasm_with_conf =
      eval_cake_compile_explore_with_conf wasm_arch_thms;

  val eval_cake_compile_wasm_general =
      eval_cake_compile_general wasm_arch_thms;

end

end
