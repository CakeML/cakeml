open preamble
open ml_translatorLib ml_hol_kernelProgTheory holKernelProofTheory ml_monadProgTheory
open bigStepTheory
open terminationTheory

val _ = new_theory"ml_hol_init"

val kernel_init_thm = store_thm("kernel_init_thm",
  ``∃refs.
      HOL_STORE (candle_init_state ffi).refs refs ∧
      STATE init_ctxt refs``,
  qexists_tac`<|
    the_type_constants := init_type_constants;
    the_term_constants := init_term_constants;
    the_axioms := init_axioms;
    the_context := init_context |>`
  \\ fs [HOL_STORE_def,isRefv_def,EVAL ``(candle_init_state ffi).refs``,
         GSYM init_context_def,
         GSYM init_axioms_def,
         GSYM init_term_constants_def,
         GSYM init_type_constants_def]
  \\ rw[STATE_def,IS_PREFIX_APPEND]
  \\ fs [init_context_v_thm,
         init_axioms_v_thm,
         init_term_constants_v_thm,
         init_type_constants_v_thm]
  \\ EVAL_TAC \\ fs[]);

val _ = export_theory()
