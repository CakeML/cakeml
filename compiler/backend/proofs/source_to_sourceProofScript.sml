(*
  Proof of correctness for source_to_source.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_to_sourceTheory source_letProofTheory
     source_evalProofTheory;

val _ = new_theory "source_to_sourceProof";

val _ = set_grammar_ancestry [
  "source_letProof", "source_to_source", "evaluate", "evaluateProps",
  "semanticPrimitives", "semanticPrimitivesProps", "misc", "semantics"
  ];

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile prog) outcome
Proof
  rw [compile_def]
  \\ irule source_letProofTheory.compile_semantics
  \\ gs []
QED

Theorem compile_semantics_oracle:
  !f.
  source_evalProof$is_insert_oracle ci f s.eval_state ∧
  ¬ semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
  semantics_prog (s with eval_state updated_by
            source_evalProof$adjust_oracle ci (compile ∘ f))
        env prog outcome
Proof
  rw [compile_def]
  \\ irule source_letProofTheory.compile_semantics_oracle
  \\ simp []
QED


val _ = export_theory ();

