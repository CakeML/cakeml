(*
  Lemma used in repl_typesTheory: that evaluate_skip's invariant
  holds at initialisation.
*)

open preamble evaluate_skipTheory

val _ = new_theory "evaluate_init";

(* TODO: move *)

Theorem FUN_FMAP_SUBMAP_SUBSET:
  FINITE d1 ∧ FINITE d2 ⇒
  (FUN_FMAP f d1 SUBMAP FUN_FMAP f d2 <=> d1 SUBSET d2)
Proof
  rw[SUBMAP_FLOOKUP_EQN, FLOOKUP_FUN_FMAP, SUBSET_DEF]
QED

(* -- *)

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
  rpt strip_tac \\ simp[]
  \\ drule (el 3 (CONJUNCTS evaluate_update))
  \\ disch_then(resolve_then Any mp_tac state_rel_init)
  \\ disch_then(resolve_then Any mp_tac env_rel_init)
  \\ simp[]
  \\ strip_tac
  \\ reverse conj_tac
  >- (
    irule env_rel_extend_dec_env
    \\ conj_tac
    >- (
      irule env_rel_update
      \\ goal_assum(resolve_then Any mp_tac env_rel_init)
      \\ simp[FUN_FMAP_SUBMAP_SUBSET]
      \\ conj_tac \\ irule COUNT_MONO
      \\ gs[state_rel_def, FLOOKUP_DEF]
      \\ rpt(qpat_x_assum`_ < _`mp_tac)
      \\ EVAL_TAC \\ simp[] )
    \\ cheat)
  \\ fs[state_rel_def, FLOOKUP_FUN_FMAP]
  \\ conj_tac
  >- (
    rpt (qhdtm_x_assum`INJ`mp_tac)
    \\ rewrite_tac[INJ_DEF]
    \\ simp_tac(std_ss ++ pred_setLib.PRED_SET_ss)[FUN_FMAP_DEF])
  \\ conj_tac
  >- (
    rpt (qhdtm_x_assum`INJ`mp_tac)
    \\ rewrite_tac[INJ_DEF]
    \\ simp_tac(std_ss ++ pred_setLib.PRED_SET_ss)[FUN_FMAP_DEF])
  \\ conj_tac
  >- (
    rpt (qhdtm_x_assum`INJ`mp_tac)
    \\ rewrite_tac[INJ_DEF]
    \\ simp_tac(std_ss ++ pred_setLib.PRED_SET_ss)[FUN_FMAP_DEF])
  \\ conj_tac >- gs[FLOOKUP_DEF]
  \\ conj_tac >- gs[FLOOKUP_DEF]
  \\ conj_tac >- gs[FLOOKUP_DEF]
  \\ conj_tac >- gs[FLOOKUP_DEF]
  \\ conj_tac >- gs[FLOOKUP_DEF]
  \\ conj_tac >- gs[FLOOKUP_DEF]
  \\ rw[]
  \\ first_x_assum (qspec_then`n`mp_tac)
  \\ rw[]
  \\ cheat
QED

val _ = export_theory();
