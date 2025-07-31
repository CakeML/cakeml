(*
  Prove that the state of the kernel can be initialised in a way that
  meets the invariants (STATE and HOL_STORE).
*)
Theory ml_hol_init
Ancestors
  ml_hol_kernelProg ml_hol_kernel_funsProg holKernelProof
  ml_monad_translatorBase evaluate evaluate cfStore
Libs
  preamble ml_translatorLib

val EVAL_STATE_CONV = ((STRIP_QUANT_CONV o RAND_CONV o RAND_CONV o RAND_CONV) EVAL) THENC (SIMP_CONV (srw_ss()) []);

Theorem kernel_init_thm:
   ∃refs. !p.
      (HOL_STORE refs * GC) (st2heap (p : 'ffi ffi_proj) (candle_init_state ffi)) ∧
      STATE init_ctxt refs
Proof
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
  \\ fs [st2heap_def]
QED

