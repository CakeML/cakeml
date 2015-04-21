open HolKernel Parse boolLib bossLib;

val _ = new_theory "x64_code_eval";

open x64_heapTheory bc_compileTheory lcsymtacs;

val x64_def_expanded = x64_def
  |> SIMP_RULE std_ss [small_offset_def,LET_DEF,globals_count_def,
       small_offset16_def,small_offset12_def,small_offset6_def,
       prog_x64_extraTheory.IMM32_def]

val x64_EQ_inst_compile = store_thm("x64_EQ_inst_compile",
  ``x64 = inst_compile``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ STRIP_TAC \\ Cases
  \\ FULL_SIMP_TAC std_ss [x64_def_expanded,inst_compile_def]
  \\ TRY (Cases_on `b`)
  \\ FULL_SIMP_TAC std_ss [x64_def_expanded,inst_compile_def]
  \\ TRY (Cases_on `l`)
  \\ FULL_SIMP_TAC std_ss [x64_def_expanded,inst_compile_def]);

val x64_length_EQ_inst_length = store_thm("x64_length_EQ_inst_length",
  ``x64_length = inst_length``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM,x64_length_def,
    inst_length_def,x64_EQ_inst_compile]);

val x64_code_EQ_bc_compile = store_thm("x64_code_EQ_bc_compile",
  ``x64_code = bc_compile``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] \\ Induct_on `x'`
  \\ FULL_SIMP_TAC std_ss [bc_compile_def,x64_code_def,
       x64_length_EQ_inst_length,x64_EQ_inst_compile]);

val _ = computeLib.add_persistent_funs
          ["x64_EQ_inst_compile",
           "x64_length_EQ_inst_length",
           "x64_code_EQ_bc_compile"];

val _ = export_theory();
