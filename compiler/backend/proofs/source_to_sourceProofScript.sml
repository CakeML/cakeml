(*
  Proof of correctness for source_to_source.
 *)
Theory source_to_sourceProof
Ancestors
  source_letProof source_dceProof source_lift_constsProof
  source_to_source evaluate evaluateProps
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
  rw [source_to_sourceTheory.compile_def]
  >> ‘outcome ≠ Fail’ by metis_tac []
  >> drule_all source_dceProofTheory.compile_semantics
  >> strip_tac
  >> ‘¬semantics_prog s env (source_dce$compile_decs prog) Fail’ by
       metis_tac [semantics_prog_deterministic]
  >> drule_all source_letProofTheory.compile_semantics
  >> strip_tac
  >> irule source_lift_constsProofTheory.compile_semantics
  >> simp []
  >> metis_tac [semantics_prog_deterministic]
QED

Theorem lift_oracle_compiler_arguments:
  lift_runtime_rel value value' ⇒
  v_to_mlstring value = v_to_mlstring value' ∧
  v_to_word64_list value = v_to_word64_list value'
Proof
  rw [lift_runtime_rel_unfold]
  >> metis_tac [lift_value_rel_compiler_literals,lift_value_rel_compiler_words]
QED

Theorem lift_do_eval_oracle:
  LIST_REL lift_runtime_rel vs vs' ⇒
  OPTREL (λ(env_id,orac,decs) (env_id',orac',decs').
    env_id = env_id' ∧ orac = orac' ∧
    decs' = source_lift_consts$compile_decs decs)
    (source_evalProof$do_eval_oracle compiler f vs orac)
    (source_evalProof$do_eval_oracle compiler
      (source_lift_consts$compile_decs ∘ f) vs' orac)
Proof
  strip_tac
  >> namedCases_on ‘vs’ ["","source_env_id source_after_env_id"]
  >> namedCases_on ‘vs'’ ["","target_env_id target_after_env_id"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> namedCases_on ‘source_after_env_id’ ["","source_config source_after_config"]
  >> namedCases_on ‘target_after_env_id’ ["","target_config target_after_config"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> namedCases_on ‘source_after_config’ ["","source_declarations source_after_declarations"]
  >> namedCases_on ‘target_after_config’ ["","target_declarations target_after_declarations"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> namedCases_on ‘source_after_declarations’ ["","source_next_config source_after_next_config"]
  >> namedCases_on ‘target_after_declarations’ ["","target_next_config target_after_next_config"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> namedCases_on ‘source_after_next_config’ ["","source_bytes source_after_bytes"]
  >> namedCases_on ‘target_after_next_config’ ["","target_bytes target_after_bytes"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> namedCases_on ‘source_after_bytes’ ["","source_words source_after_words"]
  >> namedCases_on ‘target_after_bytes’ ["","target_words target_after_words"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> namedCases_on ‘source_after_words’ ["","source_extra source_after_extra"]
  >> namedCases_on ‘target_after_words’ ["","target_extra target_after_extra"]
  >> gvs [source_evalProofTheory.do_eval_oracle_def]
  >> imp_res_tac lift_oracle_compiler_arguments
  >> gvs []
  >> pairarg_tac
  >> gvs []
  >> namedCases_on ‘v_to_mlstring target_bytes’ ["","bytes"]
  >> namedCases_on ‘v_to_word64_list target_words’ ["","words"]
  >> gvs []
  >> namedCases_on ‘compiler (orac 0)’ ["","compiler_result"]
  >> gvs []
  >> namedCases_on ‘compiler_result’ ["compiler_state compiler_bytes compiler_words"]
  >> gvs []
  >> Cases_on ‘bytes = compiler_bytes ∧ words = compiler_words ∧
       compiler_state = FST (SND (orac 1))’
  >> simp []
QED

Theorem lift_adjust_oracle_state_rel:
  source_evalProof$is_insert_oracle ci f es ⇒
  lift_oracle_state_rel
    (source_evalProof$do_eval_oracle (source_evalProof$mk_compiler_fun_from_ci ci) f)
    (source_evalProof$do_eval_oracle (source_evalProof$mk_compiler_fun_from_ci ci)
      (source_lift_consts$compile_decs ∘ f))
    es (source_evalProof$adjust_oracle ci (source_lift_consts$compile_decs ∘ f) es)
Proof
  rewrite_tac [source_evalProofTheory.is_insert_oracle_def]
  >> disch_then (qx_choosel_then [‘initial_state’,‘shift’,‘orac’] strip_assume_tac)
  >> namedCases_on ‘initial_state’ ["","initial_mode"]
  >> gvs [source_evalProofTheory.insert_gen_oracle_def,
       source_evalProofTheory.adjust_oracle_def,lift_oracle_state_rel_def]
  >> namedCases_on ‘initial_mode’ ["initial_decs","initial_oracle"]
  >> gvs []
  >> simp [LIST_REL_refl,lift_runtime_env_refl]
QED

Theorem lift_compile_semantics_oracle:
  source_evalProof$is_insert_oracle
    (ci:'config source_evalProof$compiler_instance) f
    (s:'ffi semanticPrimitives$state).eval_state ∧
  ¬semantics_prog s env prog Fail ∧ semantics_prog s env prog outcome ⇒
  semantics_prog (s with eval_state updated_by
    source_evalProof$adjust_oracle ci (source_lift_consts$compile_decs ∘ f))
    env prog outcome
Proof
  strip_tac
  >> mp_tac (Q.INST
       [‘source_callback’ |-> ‘source_evalProof$do_eval_oracle
          (source_evalProof$mk_compiler_fun_from_ci
            (ci:'config source_evalProof$compiler_instance)) f’,
        ‘target_callback’ |-> ‘source_evalProof$do_eval_oracle
          (source_evalProof$mk_compiler_fun_from_ci
            (ci:'config source_evalProof$compiler_instance))
          (source_lift_consts$compile_decs ∘ f)’,
        ‘s’ |-> ‘(s:'ffi semanticPrimitives$state)’,
        ‘s'’ |-> ‘(s:'ffi semanticPrimitives$state) with eval_state updated_by
          source_evalProof$adjust_oracle
            (ci:'config source_evalProof$compiler_instance)
            (source_lift_consts$compile_decs ∘ f)’,
        ‘env’ |-> ‘env’,‘env'’ |-> ‘env’,‘prog’ |-> ‘prog’,‘outcome’ |-> ‘outcome’]
       (SPEC_ALL lift_oracle_semantics))
  >> impl_tac
  >- (
    simp [lift_state_rel_def,lift_adjust_oracle_state_rel,
      LIST_REL_refl,lift_runtime_store_refl,lift_runtime_env_refl]
    >> qx_genl_tac [‘vs’,‘vs'’,‘orac’]
    >> strip_tac
    >> irule OPTREL_MONO
    >> qexists_tac ‘λ(env_id,orac,decs) (env_id',orac',decs').
         env_id = env_id' ∧ orac = orac' ∧
         decs' = source_lift_consts$compile_decs decs’
    >> simp [FORALL_PROD,lift_do_eval_oracle])
  >> simp []
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
  ¬ semantics_prog s env prog Fail ∧
  semantics_prog s env prog outcome ⇒
  semantics_prog (s with eval_state updated_by
            source_evalProof$adjust_oracle ci (source_to_source$inc_compile ∘ f))
        env prog outcome
Proof
  qx_gen_tac ‘f’
  >> strip_tac
  >> ‘outcome ≠ Fail’ by metis_tac []
  >> drule_all source_letProofTheory.compile_semantics_oracle
  >> strip_tac
  >> ‘¬semantics_prog (s with eval_state updated_by
        source_evalProof$adjust_oracle ci (source_let$compile_decs ∘ f))
        env prog Fail’ by metis_tac [semantics_prog_deterministic]
  >> sg ‘source_evalProof$is_insert_oracle ci (source_let$compile_decs ∘ f)
        (s with eval_state updated_by
          source_evalProof$adjust_oracle ci (source_let$compile_decs ∘ f)).eval_state’
  >- (
    simp []
    >> irule is_insert_oracle_adjust
    >> qexists_tac ‘f’
    >> simp [])
  >> mp_tac (Q.INST
       [‘ci’ |-> ‘(ci:'config source_evalProof$compiler_instance)’,
        ‘f’ |-> ‘source_let$compile_decs ∘ f’,
        ‘s’ |-> ‘(s:'ffi semanticPrimitives$state) with eval_state updated_by
          source_evalProof$adjust_oracle
            (ci:'config source_evalProof$compiler_instance) (source_let$compile_decs ∘ f)’,
        ‘env’ |-> ‘env’,‘prog’ |-> ‘prog’,‘outcome’ |-> ‘outcome’]
       (SPEC_ALL lift_compile_semantics_oracle))
  >> pure_rewrite_tac [adjust_oracle_state_compose,inc_compile_eq,GSYM o_ASSOC]
  >> simp []
QED
