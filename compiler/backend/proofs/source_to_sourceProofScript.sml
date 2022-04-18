(*
  Proof of correctness for source_to_source.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_to_sourceTheory source_letProofTheory;

val _ = new_theory "source_to_sourceProof";

val _ = set_grammar_ancestry [
  "source_letProof", "source_to_source", "evaluate", "evaluateProps",
  "semanticPrimitives", "semanticPrimitivesProps", "misc", "semantics"
  ];

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile_prog prog) outcome
Proof
  rw [compile_prog_def]
  \\ irule source_letProofTheory.compile_semantics
  \\ gs []
QED

val _ = export_theory ();

