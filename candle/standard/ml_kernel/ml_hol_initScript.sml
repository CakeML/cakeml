open preamble
open ml_hol_kernelProgTheory holKernelProofTheory
open ml_monad_translatorBaseTheory ml_translatorLib
open bigStepTheory terminationTheory cfStoreTheory

val _ = new_theory"ml_hol_init"

val EVAL_STATE_CONV = ((STRIP_QUANT_CONV o RAND_CONV o RAND_CONV o RAND_CONV) EVAL) THENC (SIMP_CONV (srw_ss()) []);

val kernel_init_thm = Q.store_thm("kernel_init_thm",
  `∃refs. !p.
      (HOL_STORE refs * GC) (st2heap (p : 'ffi ffi_proj) (candle_init_state ffi)) ∧
      STATE init_ctxt refs`,
  `?refs.
    refs.the_type_constants = init_type_constants ∧
    refs.the_term_constants = init_term_constants ∧
    refs.the_axioms = init_axioms ∧
    refs.the_context = init_context` by srw_tac[QI_ss][]
  \\ qexists_tac `refs`
  \\ STRIP_TAC
  \\ SIMP_TAC (srw_ss()) [EVAL ``candle_init_state ffi``]
  \\ reverse CONJ_TAC
  THEN1 (rw[STATE_def] \\ EVAL_TAC \\ fs[])
  \\ ASSUME_TAC (CONV_RULE
      ((SIMP_CONV bool_ss [REFS_PRED_def]) THENC EVAL_STATE_CONV) INIT_HOL_STORE)
  \\ pop_assum drule \\ fs []
  \\ disch_then (qspec_then `p` assume_tac)
  \\ fs [st2heap_def]);

val _ = export_theory()
