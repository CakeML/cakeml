(*
  Proof of correctness for source_to_source.
 *)
Theory source_to_sourceProof
Ancestors
  source_letProof source_dceProof source_to_source evaluate evaluateProps
  semanticPrimitives semanticPrimitivesProps misc[qualified]
  semantics ast source_evalProof semanticsProps
Libs
  preamble


Theorem compile_semantics:
  env.v = nsEmpty ∧
  (∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile prog) outcome
Proof
  rw [compile_def]
  \\ drule_all source_dceProofTheory.compile_semantics \\ rw []
  \\ irule source_letProofTheory.compile_semantics \\ rw []
  \\ Cases_on ‘outcome = Fail’ \\ fs []
  \\ CCONTR_TAC \\ gvs []
  \\ imp_res_tac semantics_prog_deterministic
QED

Theorem compile_semantics_oracle:
  !f.
  source_evalProof$is_insert_oracle ci f s.eval_state ∧
  ¬ semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
  semantics_prog (s with eval_state updated_by
            source_evalProof$adjust_oracle ci (source_to_source$inc_compile ∘ f))
        env prog outcome
Proof
  rw [compile_def,
      SRULE [LET_THM, GSYM FUN_EQ_THM, SF ETA_ss] source_to_sourceTheory.inc_compile_def]
  \\ irule source_letProofTheory.compile_semantics_oracle
  \\ simp []
QED
