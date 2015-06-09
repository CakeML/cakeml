open HolKernel boolLib bossLib lcsymtacs miscLib
open ml_hol_kernelTheory flookupLib compute_compilerLib compute_bytecodeLib
val _ = new_theory"compile_kernel"

val _ = Globals.max_print_depth := 20

val cs = the_compiler_compset false;
val () = computeLib.scrub_const cs finite_mapSyntax.flookup_t;
val () = computeLib.add_conv (finite_mapSyntax.flookup_t,2,FLOOKUP_DEFN_CONV) cs;
(* TODO: this should go into a separate compset *)
val () = computeLib.add_datatype_info cs (valOf(TypeBase.fetch``:comp_environment``))
val eval = computeLib.CBV_CONV cs

val compile_kernel_module_def = zDefine`
  compile_kernel_module =
  compile_top NONE ((FST(THE prim_env)).comp_rs) (Tmod "Kernel" NONE ml_hol_kernel_decls)`

val compile_kernel_module_eq = save_thm("compile_kernel_module_eq",
  time (REWR_CONV compile_kernel_module_def
        THENC PURE_ONCE_REWRITE_CONV[ml_hol_kernel_decls,initCompEnvTheory.prim_env_eq]
        THENC eval)
  ``compile_kernel_module``)

(*
val kernel_code_def = zDefine`
  kernel_code = code_labels real_inst_length
    (initial_bc_state.code++REVERSE(SND(THE prim_env))++SND(SND compile_kernel_module))`

val initial_bc_state_code_eq = EVAL``initial_bc_state.code``

val kernel_code_labels_ok0 = prove(
  ``code_labels_ok ^(rand(rhs(concl kernel_code_def)))``,
  match_mp_tac compilerTerminationTheory.code_labels_ok_append_local >>
  conj_tac >- (
    match_mp_tac bytecodeLabelsTheory.code_labels_ok_append >>
    reverse conj_tac >- (
      REWRITE_TAC[initCompEnvTheory.prim_env_eq] >>
      EVAL_TAC >> simp[]) >>
    simp[initCompEnvTheory.initial_bc_state_def,
         compilerTerminationTheory.code_labels_ok_microcode] ) >>
  conj_tac >- (
    simp[compile_kernel_module_def] >>
    match_mp_tac (
      compilerProofTheory.compile_top_labels
      |> SPEC_ALL |> UNDISCH_ALL  |> CONJUNCT2 |> CONJUNCT2
      |> DISCH_ALL |> GEN_ALL) >>
    simp[evalPropsTheory.FV_top_def,
*)

val _ = export_theory()
