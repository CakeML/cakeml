(*
  Correctness for the source_lift_consts passes.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_lift_constsTheory source_evalProofTheory;

val _ = new_theory "source_lift_constsProof";

val _ = set_grammar_ancestry
  [ "source_lift_consts", "evaluate", "evaluateProps", "semanticPrimitives",
    "semanticPrimitivesProps", "misc", "semantics" ];

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile_decs prog) outcome
Proof
  cheat
QED

Theorem compile_semantics_oracle:
  ∀f.
    source_evalProof$is_insert_oracle ci f s.eval_state ∧
    ¬ semantics_prog s env prog Fail ∧
    semantics_prog s env prog outcome
    ⇒
    semantics_prog (s with eval_state updated_by
              source_evalProof$adjust_oracle ci (compile_decs ∘ f))
          env prog outcome
Proof
  cheat
QED

val _ = export_theory ();
