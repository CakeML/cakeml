(*
  Lemma used in repl_typesTheory: that evaluate_skip's invariant
  holds at initialisation.
*)

open preamble evaluate_skipTheory

val _ = new_theory "evaluate_init";

Theorem state_rel_init:
  state_rel 0 FEMPTY (FUN_FMAP I (count 2)) (FUN_FMAP I (count 4))
  (init_state ffi with clock := ck)
  (init_state ffi with clock := ck)
Proof
  rw[state_rel_def, ml_progTheory.init_state_def, FLOOKUP_FUN_FMAP]
  \\ rw[INJ_DEF, FUN_FMAP_DEF]
  \\ EVAL_TAC
QED

Theorem env_rel_init:
  env_rel FEMPTY (FUN_FMAP I (count 2)) (FUN_FMAP I (count 4))
    init_env init_env
Proof
  rw[env_rel_def, ml_progTheory.init_env_def,
     GSYM namespaceTheory.nsEmpty_def]
  \\ rw[ctor_rel_def, namespaceTheory.nsAll2_def]
  \\ rw[namespaceTheory.nsSub_def]
  \\ Cases_on`id` \\ fs[namespaceTheory.nsLookup_def]
  \\ pop_assum mp_tac \\ rw[]
  \\ rw[stamp_rel_cases, FLOOKUP_FUN_FMAP]
QED

Theorem evaluate_decs_init:
  evaluate_decs (init_state ffi with clock := ck) init_env decs = (s,Rval env) ⇒
  ∃fr ft fe.
     fr = FUN_FMAP I (count (LENGTH s.refs)) ∧
     ft = FUN_FMAP I (count s.next_type_stamp) ∧
     fe = FUN_FMAP I (count s.next_exn_stamp) ∧
     state_rel (LENGTH s.refs) fr ft fe s s ∧
     env_rel fr ft fe (extend_dec_env env init_env)
                      (extend_dec_env env init_env)
Proof
  rpt strip_tac
  (* this may not be the right thing to do *)
  \\ drule (el 3 (CONJUNCTS evaluate_update))
  \\ disch_then(resolve_then Any mp_tac state_rel_init)
  \\ disch_then(resolve_then Any mp_tac env_rel_init)
  \\ simp[]
  \\ strip_tac
  \\ cheat
QED

val _ = export_theory();
