open HolKernel boolLib bossLib evaluateReplTheory flookupLib compute_compilerLib
val _ = new_theory"compileRepl"

val _ = Globals.max_print_depth := 20

val cs = the_compiler_compset false;
val () = computeLib.scrub_const cs finite_mapSyntax.flookup_t;
val () = computeLib.add_conv (finite_mapSyntax.flookup_t,2,FLOOKUP_DEFN_CONV) cs;
(* TODO: this should go into a separate compset *)
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:comp_environment``))
val eval = computeLib.CBV_CONV cs

val compile_repl_module_eq = save_thm("compile_repl_module_eq",
  time (REWR_CONV compile_repl_module_def
        THENC PURE_ONCE_REWRITE_CONV[replModuleTheory.replModule_decls,initCompEnvTheory.prim_env_eq]
        THENC eval)
  ``compile_repl_module``)

val _ = computeLib.add_thms [compilerTheory.compile_special_def] cs
val eval_special = computeLib.CBV_CONV cs
val compile_call_repl_step_eq = save_thm("compile_call_repl_step_eq",
  time (REWR_CONV compile_call_repl_step_def THENC
        PURE_ONCE_REWRITE_CONV[compile_repl_module_eq] THENC
        eval_special)
  ``compile_call_repl_step``)

val _ = Feedback.set_trace "TheoryPP.include_docs" 0
val _ = export_theory()
