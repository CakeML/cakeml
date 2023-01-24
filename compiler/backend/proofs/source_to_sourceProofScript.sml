(*
  Proof of correctness for source_to_source.
 *)

open preamble astTheory evaluateTheory evaluatePropsTheory
     semanticPrimitivesTheory semanticPrimitivesPropsTheory
     semanticsTheory source_to_sourceTheory semanticsPropsTheory
     source_letProofTheory
     source_lift_constsProofTheory
     source_evalProofTheory;

val _ = new_theory "source_to_sourceProof";

val _ = set_grammar_ancestry
  [ "source_letProof", "source_lift_constsProof",
    "source_to_source", "evaluate", "evaluateProps",
    "semanticPrimitives", "semanticPrimitivesProps", "misc", "semantics" ];

Triviality semantics_prog_11:
  semantics_prog s env prog outcome1 ∧
  semantics_prog s env prog outcome2 ⇒
  outcome1 = outcome2
Proof
  metis_tac [semanticsPropsTheory.semantics_prog_deterministic]
QED

Theorem compile_semantics:
  ¬semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
    semantics_prog s env (compile prog) outcome
Proof
  rw [source_to_sourceTheory.compile_def]
  \\ drule_all source_letProofTheory.compile_semantics
  \\ strip_tac
  \\ drule_at Any source_lift_constsProofTheory.compile_semantics
  \\ impl_tac
  >-
   (strip_tac
    \\ imp_res_tac semantics_prog_11
    \\ rpt var_eq_tac \\ fs [])
  \\ fs [semantics_prog_def]
QED

Triviality adjust_oracle_o:
  source_evalProof$adjust_oracle cj f ∘
  source_evalProof$adjust_oracle ci g =
  source_evalProof$adjust_oracle cj f
Proof
  fs [adjust_oracle_def,FUN_EQ_THM]
  \\ Cases \\ fs []
  \\ Cases_on ‘x'’ \\ fs []
QED

Triviality compile_eq:
  source_to_source$compile =
    source_lift_consts$compile_decs o
    source_let$compile_decs
Proof
  fs [FUN_EQ_THM,source_to_sourceTheory.compile_def]
QED

Theorem compile_semantics_oracle:
  ∀f.
  source_evalProof$is_insert_oracle ci f s.eval_state ∧
  ¬ semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
  semantics_prog (s with eval_state updated_by
            source_evalProof$adjust_oracle ci (compile ∘ f))
        env prog outcome
Proof
  rw [source_to_sourceTheory.compile_def]
  \\ drule_all source_letProofTheory.compile_semantics_oracle
  \\ strip_tac
  \\ drule_at (Pos last) source_lift_constsProofTheory.compile_semantics_oracle
  \\ fs [adjust_oracle_o,compile_eq]
  \\ disch_then irule
  \\ conj_tac
  >-
   (strip_tac
    \\ imp_res_tac semantics_prog_11
    \\ rpt var_eq_tac \\ fs [])
  \\ last_x_assum mp_tac
  \\ fs [is_insert_oracle_def,adjust_oracle_def]
  \\ rw [] \\ fs []
  \\ fs [insert_gen_oracle_def]
  \\ every_case_tac
  \\ fs [AllCaseEqs()]
  \\ metis_tac []
QED

val _ = export_theory ();
