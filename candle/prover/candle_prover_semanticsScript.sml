(*
  Top-level soundness theorem for the Candle theorem prover.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory ml_hol_kernelProgTheory
open permsTheory candle_kernel_funsTheory candle_kernel_valsTheory
     candle_prover_invTheory candle_prover_evaluateTheory ast_extrasTheory
     candle_basis_evaluateTheory semanticsTheory;
open holKernelProofTheory basisProgTheory ml_hol_kernelProgTheory;
open ml_translatorLib ml_progTheory;
local open ml_progLib in end

val _ = new_theory "candle_prover_semantics";

val _ = translation_extends "ml_hol_kernelProg";

Theorem LPREFIX_LNTH:
  ∀n xs l ll.
    LPREFIX xs l ∧
    LNTH n xs = NONE ∧
    LTAKE n l = SOME ll ⇒
      LPREFIX xs (fromList ll)
Proof
  Induct \\ rpt Cases \\ rw [llistTheory.fromList_def]
  \\ gvs [LPREFIX_LCONS, SF SFY_ss]
QED

(* TODO move to evaluateProps (or wherever evaluate_decs_cons is)
 *)

Theorem evaluate_decs_append:
  ∀ds1 s env ds2.
    evaluate_decs s env (ds1 ++ ds2) =
    case evaluate_decs s env ds1 of
      (s1,Rval env1) =>
        (case evaluate_decs s1 (extend_dec_env env1 env) ds2 of
           (s2,r) => (s2,combine_dec_result env1 r))
    | (s1,Rerr v7) => (s1,Rerr v7)
Proof
  Induct \\ rw []
  >- (
    rw [extend_dec_env_def, combine_dec_result_def]
    \\ rpt CASE_TAC)
  \\ once_rewrite_tac [evaluate_decs_cons] \\ simp []
  \\ gs [combine_dec_result_def, extend_dec_env_def]
  \\ rpt CASE_TAC \\ gs []
QED

(* TODO move *)

Theorem env_ok_extend_dec_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (extend_dec_env env1 env2)
Proof
  rw [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some] \\ gs [SF SFY_ss]
QED

(* -------------------------------------------------------------------------
 * - The basis program:
 *   basis, basis_env, basis_state
 * - The candle program (includes the former):
 *   candle_code, candle_init_env, candle_init_state
 * ------------------------------------------------------------------------- *)

Overload basis_env = (basis_Decls_thm |> concl |> rator |> rand);

Overload basis_state = (basis_Decls_thm |> concl |> rand |> rator);

(* -------------------------------------------------------------------------
 * Show that the basis program satisfies post_state_ok, simple_dec and
 * safe_dec. Use this to show basis_env is env_ok.
 * ------------------------------------------------------------------------- *)

Theorem post_state_ok_basis_state:
  post_state_ok (basis_state ffi)
Proof
  rw [post_state_ok_def, kernel_types_def, kernel_locs_def,
      the_type_constants_def, the_term_constants_def,
      the_axioms_def, the_context_def]
  \\ EVAL_TAC \\ gs []
QED

Theorem basis_decs_ok:
  EVERY simple_dec basis ∧
  EVERY safe_dec basis
Proof
  once_rewrite_tac [basis_def]
  \\ conj_tac
  \\ EVAL_TAC
  \\ simp [namespaceTheory.id_to_n_def]
QED

Theorem env_ok_basis_env:
  env_ok ctxt basis_env
Proof
  assume_tac basis_Decls_thm
  \\ gs [Decls_def]
  \\ drule_then (qspec_then ‘ctxt’ mp_tac) evaluate_basis_v_ok_decs
  \\ simp [basis_decs_ok, post_state_ok_basis_state, env_ok_init_env]
  \\ rw [env_ok_def, extend_dec_env_def, nsLookup_nsAppend_some, SF SFY_ss]
QED

(* --------------------------------------------------------------------------
 * Show that the candle_init_state is state_ok.
 * ------------------------------------------------------------------------- *)

Definition init_refs_def:
  init_refs = <|
      the_type_constants := init_type_constants;
      the_term_constants := init_term_constants;
      the_axioms         := init_axioms;
      the_context        := init_context |>
End

Theorem STATE_init_refs:
  STATE init_context init_refs
Proof
  simp [STATE_def, CONTEXT_def, init_type_constants_def, init_axioms_def,
        init_term_constants_def, init_context_def, init_refs_def,
        holSyntaxTheory.init_ctxt_def, holSyntaxTheory.extends_def]
QED

Theorem candle_init_state_stamp:
  n ∈ kernel_types ⇒ n < (candle_init_state ffi).next_type_stamp
Proof
  EVAL_TAC \\ gs []
QED

Theorem kernel_refs_distinct[local,simp]:
  the_type_constants ≠ the_term_constants ∧
  the_type_constants ≠ the_axioms ∧
  the_type_constants ≠ the_context ∧
  the_term_constants ≠ the_axioms ∧
  the_term_constants ≠ the_context ∧
  the_axioms ≠ the_context
Proof
  simp [the_type_constants_def, the_term_constants_def, the_context_def,
        the_axioms_def]
QED

Theorem LLOOKUPs[local]:
  (Loc loc = the_type_constants ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_type_constants_v)) ∧
  (Loc loc = the_term_constants ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_term_constants_v)) ∧
  (Loc loc = the_axioms ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_axioms_v)) ∧
  (Loc loc = the_context ⇒
     LLOOKUP (candle_init_state ffi).refs loc =
     SOME (Refv init_context_v))
Proof
  rpt strip_tac
  \\ gvs [the_type_constants_def, the_term_constants_def, the_axioms_def,
          the_context_def]
  \\ rw [candle_init_state_def, LLOOKUP_EQ_EL, EL_APPEND_EQN]
QED

Theorem candle_init_state_refs:
  loc ∈ kernel_locs ⇒
    kernel_loc_ok init_refs loc (candle_init_state ffi).refs
Proof
  gvs [kernel_locs_def, kernel_loc_ok_def]
  \\ rw [] \\ gs []
  \\ FIRST (map (drule_then (qspec_then ‘ffi’ assume_tac))
                (CONJUNCTS LLOOKUPs))
  \\ first_assum (irule_at Any) \\ gs []
  \\ simp [init_refs_def, init_type_constants_v_thm, init_term_constants_v_thm,
           init_axioms_v_thm, init_context_v_thm]
QED

Theorem candle_init_state_eval[simp]:
  eval_state_ok (candle_init_state ffi).eval_state
Proof
  EVAL_TAC
QED

Theorem candle_init_state_ffi[simp]:
  (candle_init_state ffi).ffi = ffi
Proof
  EVAL_TAC
QED

Theorem candle_init_state_state_ok:
  ffi.io_events = [] ⇒
  state_ok init_context (candle_init_state ffi)
Proof
  strip_tac
  \\ simp [state_ok_def, candle_init_state_stamp]
  \\ irule_at Any STATE_init_refs
  \\ simp [candle_init_state_refs]
  (* TODO:
   *    The rest of the state; it's all OK but we cant inspect the references
   *    until the translator is set up to store defintions. *)
  \\ rw [LLOOKUP_EQ_EL, EL_APPEND_EQN, candle_init_state_def]
  \\ gvs [NOT_LESS, LESS_OR_EQ, ref_ok_def, kernel_locs_def,
          the_context_def, the_axioms_def, the_type_constants_def,
          the_term_constants_def]
  \\ cheat
QED

(* --------------------------------------------------------------------------
 * Show that candle_init_env is env_ok wrt. the initial context.
 * ------------------------------------------------------------------------- *)

Theorem candle_init_env_env_ok:
  env_ok init_ctxt candle_init_env
Proof
  cheat
QED

(* --------------------------------------------------------------------------
 * Top-level semantics theorem.
 * ------------------------------------------------------------------------- *)

(* TODO Print context updates on FFI
    -- Magnus: actually, we might want to print the entire context
               for each theorem to make soundness statement simple
   TODO: Use 'ffi
 *)

(* TODO why do these both exist? *)

Theorem init_context_init_ctxt[local,simp]:
  init_ctxt = init_context
Proof
  rw [holSyntaxTheory.init_ctxt_def, init_context_def]
QED

Theorem semantics_thm:
  semantics_prog (init_state ffi) init_env (candle_code ++ prog) res ∧
  EVERY safe_dec prog ∧
  ffi.io_events = [] ∧
  res ≠ Fail ⇒
    ∃ctxt.
      (∀outcome io_list.
         res = Terminate outcome io_list ⇒
           EVERY (ok_event ctxt) io_list) ∧
      (∀io_trace.
         res = Diverge io_trace ⇒
           every (ok_event ctxt) io_trace)
Proof
  strip_tac
  \\ Cases_on ‘res’ \\ gs []
  >~ [‘Terminate outcome io_list’] >- (
    gs [semanticsTheory.semantics_prog_def]
    \\ gs [semanticsTheory.evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ gvs []
    \\ assume_tac candle_prog_thm
    \\ gvs [evaluate_decs_append, CaseEqs ["prod", "semanticPrimitives$result"]]
    >- (
      gs [ml_progTheory.Decls_def]
      \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
      \\ qpat_x_assum ‘evaluate_decs _ _ _ = (s1, Rval _)’ assume_tac
      \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
      \\ rw []
      \\ qpat_x_assum ‘evaluate_decs s1 _ prog = _’ assume_tac
      \\ drule_then (qspec_then ‘init_context’ mp_tac)
                    (el 3 (CONJUNCTS evaluate_v_ok))
      \\ impl_tac
      >- (
        drule_then assume_tac candle_init_state_state_ok
        \\ assume_tac candle_init_env_env_ok \\ gs []
        \\ irule_at Any env_ok_extend_dec_env \\ gs [env_ok_init_env]
        \\ gs [state_ok_def, semanticPrimitivesTheory.state_component_equality]
        \\ first_assum (irule_at Any) \\ gs [SF SFY_ss])
      \\ strip_tac
      \\ rename1 ‘combine_dec_result _ res’ \\ Cases_on ‘res’ \\ gs []
      >- (
        gs [state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [])
      \\ rename1 ‘Rerr err’ \\ Cases_on ‘err’ \\ gs []
      >- (
        gs [state_ok_def]
        \\ first_assum (irule_at Any) \\ gs [])
      \\ first_assum (irule_at Any) \\ gs [])
    \\ gs [ml_progTheory.Decls_def]
    \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
    \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
    \\ rw [] \\ gs [CaseEqs ["semanticPrimitives$result"]])
  \\ gs [semanticsTheory.semantics_prog_def]
  \\ gs [lprefix_lub_def, PULL_EXISTS, every_LNTH]
  \\ qabbrev_tac ‘ff : num -> io_event llist =
                    λk. fromList (FST (evaluate_prog_with_clock
                                         (init_state ffi) init_env k
                                         (candle_code ++ prog))).io_events’
  \\ gs []
  \\ cheat
(*

    first_x_assum (qspec_then `k` assume_tac)
    \\ first_x_assum (qspec_then `k` strip_assume_tac)
    \\ imp_res_tac LPREFIX_LNTH
    \\ pop_assum kall_tac
    \\ fs [Abbr `ff`, semanticsTheory.evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs []
    \\ drule kernel_evaluate_decs
    \\ disch_then drule
    \\ rw [extract_events_def]
    \\ fs [EVERY_MEM, MEM_MAP, MEM_FILTER, PULL_EXISTS, ELIM_UNCURRY,
           CaseEq "io_event"]
    \\ PURE_CASE_TAC \\ rw []
    \\ first_x_assum irule
    \\ fs [LNTH_fromList]
    \\ drule EL_MEM
    \\ srw_tac [SATISFY_ss] []

  \\ `!k. LNTH n (ff k) = NONE` by metis_tac [option_nchotomy] \\ fs []
  \\ `F` suffices_by fs [] \\ rw []
  \\ qpat_x_assum `!ub. _ ==> _` mp_tac
  \\ simp []
  \\ drule LNTH_LTAKE \\ rw []
  \\ qexists_tac `fromList ll` \\ fs []
  \\ fsrw_tac [SATISFY_ss] [LTAKE_LPREFIX, LPREFIX_lemma] *)
QED

val _ = export_theory ();

