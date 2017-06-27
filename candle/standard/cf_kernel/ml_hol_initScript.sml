open preamble
open ml_translatorLib ml_hol_kernelProgTheory holKernelProofTheory ml_monad_translatorTheory
open bigStepTheory
open terminationTheory
open cfStoreTheory

val _ = new_theory"ml_hol_init"

val EVAL_STATE_CONV = ((STRIP_QUANT_CONV o RAND_CONV o RAND_CONV o RAND_CONV) EVAL) THENC (SIMP_CONV (srw_ss()) []);

val kernel_init_thm = Q.store_thm("kernel_init_thm",
  `∃refs.
      (HOL_STORE refs * GC) (store2heap (candle_init_state ffi).refs) ∧
      STATE init_ctxt refs`,
  `?refs. refs.the_type_constants = init_type_constants ∧
      refs.the_term_constants = init_term_constants ∧
      refs.the_axioms = init_axioms ∧ refs.the_context = init_context` by srw_tac[QI_ss][]
  \\ qexists_tac `refs`
  \\ SIMP_TAC (srw_ss()) [EVAL ``candle_init_state ffi``]
  \\ CONJ_TAC
  >-(
     ASSUME_TAC (CONV_RULE ((SIMP_CONV bool_ss [REFS_PRED_def]) THENC EVAL_STATE_CONV) INIT_HOL_STORE)
     >> POP_ASSUM irule >> fs[]
  ) \\ 
  rw[STATE_def]
  \\ EVAL_TAC \\ fs[])

val _ = export_theory()
