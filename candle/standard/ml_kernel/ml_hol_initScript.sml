open preamble
open ml_hol_kernelProgTheory holKernelProofTheory
open ml_monad_translatorBaseTheory ml_translatorLib
open bigStepTheory terminationTheory cfStoreTheory

val _ = new_theory"ml_hol_init"

val EVAL_STATE_CONV = ((STRIP_QUANT_CONV o RAND_CONV o RAND_CONV o RAND_CONV) EVAL) THENC (SIMP_CONV (srw_ss()) []);

val kernel_init_thm = Q.store_thm("kernel_init_thm",
  `∃refs. !p.
      (HOL_STORE refs * GC) (st2heap (p : unit ffi_proj) (candle_init_state ffi)) ∧
      STATE init_ctxt refs`,
  `?refs. refs.the_type_constants = init_type_constants ∧
      refs.the_term_constants = init_term_constants ∧
      refs.the_axioms = init_axioms ∧ refs.the_context = init_context` by srw_tac[QI_ss][]
  \\ qexists_tac `refs`
  \\ STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [EVAL ``candle_init_state ffi``]
  \\ CONJ_TAC
  >-(
     ASSUME_TAC (CONV_RULE ((SIMP_CONV bool_ss [REFS_PRED_def]) THENC EVAL_STATE_CONV) INIT_HOL_STORE)
     >> POP_ASSUM IMP_RES_TAC >> POP_ASSUM (qspec_then `p` ASSUME_TAC)
     >> Cases_on `p` >> fs[st2heap_def]) \\ 
  rw[STATE_def]
  \\ EVAL_TAC \\ fs[])

val _ = export_theory()
