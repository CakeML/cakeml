(*
  Proof of correctness for source_to_source.
 *)
Theory source_to_sourceProof
Ancestors
  source_letProof source_dceProof source_lift_constsProof
  source_to_source semanticsProps
Libs
  preamble


Theorem compile_semantics:
  env.v = nsEmpty ∧
  (∀x. s.eval_state = SOME x ⇒ ∃ev. x = EvalDecs ev) ∧
  ¬semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
    semantics_determ s env (compile prog) outcome
Proof
  rw [source_to_sourceTheory.compile_def]
  >> ‘outcome ≠ Fail’ by metis_tac []
  >> drule_all source_dceProofTheory.compile_semantics
  >> strip_tac
  >> ‘¬semantics_determ s env (source_dce$compile_decs prog) Fail’ by
       metis_tac [semantics_determ_deterministic]
  >> drule_all source_letProofTheory.compile_semantics
  >> strip_tac
  >> irule source_lift_constsProofTheory.compile_semantics
  >> simp []
  >> metis_tac [semantics_determ_deterministic]
QED

Theorem is_insert_oracle_adjust:
  source_evalProof$is_insert_oracle ci f es ⇒
  source_evalProof$is_insert_oracle ci g (source_evalProof$adjust_oracle ci g es)
Proof
  rewrite_tac [source_evalProofTheory.is_insert_oracle_def]
  >> disch_then (qx_choosel_then [‘initial_state’,‘shift’,‘orac’] strip_assume_tac)
  >> qexistsl_tac [‘initial_state’,‘shift’,‘orac’]
  >> gvs [source_evalProofTheory.adjust_oracle_insert_gen_oracle]
QED

Theorem adjust_oracle_compose:
  source_evalProof$adjust_oracle ci g (source_evalProof$adjust_oracle ci f es) =
  source_evalProof$adjust_oracle ci g es
Proof
  namedCases_on ‘es’ ["","eval_mode"]
  >> gvs [source_evalProofTheory.adjust_oracle_def]
  >> namedCases_on ‘eval_mode’ ["eval_decs","eval_oracle"]
  >> simp []
QED

Theorem inc_compile_eq:
  source_to_source$inc_compile =
    source_lift_consts$compile_decs ∘ source_let$compile_decs
Proof
  simp [FUN_EQ_THM,source_to_sourceTheory.inc_compile_def]
QED

Theorem adjust_oracle_state_compose:
  ((s:'ffi semanticPrimitives$state) with eval_state updated_by
    source_evalProof$adjust_oracle ci f) with eval_state updated_by
    source_evalProof$adjust_oracle ci g =
  s with eval_state updated_by source_evalProof$adjust_oracle ci g
Proof
  simp [semanticPrimitivesTheory.state_component_equality,adjust_oracle_compose]
QED

Theorem compile_semantics_oracle:
  !f.
  source_evalProof$is_insert_oracle
    (ci:'config source_evalProof$compiler_instance) f
    (s:'ffi semanticPrimitives$state).eval_state ∧
  ¬ semantics_determ s env prog Fail ∧
  semantics_determ s env prog outcome ⇒
  semantics_determ (s with eval_state updated_by
            source_evalProof$adjust_oracle ci (source_to_source$inc_compile ∘ f))
        env prog outcome
Proof
  qx_gen_tac ‘f’
  >> strip_tac
  >> ‘outcome ≠ Fail’ by metis_tac []
  >> drule_all source_letProofTheory.compile_semantics_oracle
  >> strip_tac
  >> ‘¬semantics_determ (s with eval_state updated_by
        source_evalProof$adjust_oracle ci (source_let$compile_decs ∘ f))
        env prog Fail’ by metis_tac [semantics_determ_deterministic]
  >> sg ‘source_evalProof$is_insert_oracle ci (source_let$compile_decs ∘ f)
        (s with eval_state updated_by
          source_evalProof$adjust_oracle ci (source_let$compile_decs ∘ f)).eval_state’
  >- (
    simp []
    >> irule is_insert_oracle_adjust
    >> qexists_tac ‘f’
    >> simp [])
  >> drule_all source_lift_constsProofTheory.compile_semantics_oracle
  >> pure_rewrite_tac [adjust_oracle_state_compose,inc_compile_eq,GSYM o_ASSOC]
  >> simp []
QED
