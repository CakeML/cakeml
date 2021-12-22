(*
  Top-level soundness theorem for the Candle theorem prover.
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory ml_hol_kernelProgTheory
open permsTheory candle_kernel_funsTheory candle_kernel_valsTheory
     candle_prover_invTheory candle_prover_evaluateTheory ast_extrasTheory
     semanticsTheory;
open ml_translatorLib;
local open ml_progLib in end

val _ = new_theory "candle_prover_semantics";

val _ = translation_extends "ml_hol_kernelProg";

val prog_thm = get_ml_prog_state ()
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_thm
  |> SIMP_RULE std_ss [ml_progTheory.ML_code_def, ml_progTheory.ML_code_env_def]

Definition basis_and_kernel_def:
  basis_and_kernel = ^(concl prog_thm |> rator |> rator |> rand)
End

Overload basis_and_kernel_env = (prog_thm |> concl |> rator |> rand);
Overload basis_and_kernel_state = (prog_thm |> concl |> rand |> rator);

Theorem Decls_basis_kernel = REWRITE_RULE [GSYM basis_and_kernel_def] prog_thm;

Theorem LPREFIX_lemma:
  !n xs l ll.
    LPREFIX xs l /\
    LNTH n xs = NONE /\
    LTAKE n l = SOME ll
    ==>
    LPREFIX xs (fromList ll)
Proof
  Induct \\ rpt Cases
  \\ rw [llistTheory.fromList_def]
  \\ res_tac
QED

(*
THM ctxt th
(ctxt,hyps) |- concl th
            |=
 *)

(* TODO Print context updates on FFI *)

(*
  basis_and_kernel = basis ++ candle kernel
 *)

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
    simp [extend_dec_env_def, combine_dec_result_def]
    \\ CASE_TAC \\ gs []
    \\ CASE_TAC \\ gs [])
  \\ once_rewrite_tac [evaluate_decs_cons] \\ simp []
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
  \\ simp [combine_dec_result_def]
  \\ CASE_TAC \\ gs []
  \\ simp [extend_dec_env_def]
  \\ CASE_TAC \\ gs []
  \\ CASE_TAC \\ gs []
QED

(* TODO: 'ffi *)



(*
 |- state_ok ctxt s1
 |- env_ok ctxt (extend_dec_env basis_and_kernel_env init_env)
 *)

Theorem state_ok_init_context:
  ffi.io_events = [] ⇒
  state_ok init_context (basis_and_kernel_state ffi)
Proof
  cheat
QED

Theorem env_ok_init_context:
  env_ok init_context basis_and_kernel_env
Proof
  cheat
QED

Theorem env_ok_extend_dec_env:
  env_ok ctxt env1 ∧
  env_ok ctxt env2 ⇒
    env_ok ctxt (extend_dec_env env1 env2)
Proof
  cheat
QED

Theorem semantics_thm:
  semantics_prog (init_state ffi) init_env (basis_and_kernel ++ prog) res ∧
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
    \\ gvs [evaluate_decs_append, CaseEqs ["prod", "semanticPrimitives$result"]]
    >- (
      assume_tac Decls_basis_kernel
      \\ gs [ml_progTheory.Decls_def]
      \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
      \\ qpat_x_assum ‘evaluate_decs _ _ _ = (s1, Rval _)’ assume_tac
      \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
      \\ rw []
      \\ qpat_x_assum ‘evaluate_decs s1 _ prog = _’ assume_tac
      \\ drule_then (qspec_then ‘init_context’ mp_tac)
                    (el 3 (CONJUNCTS evaluate_v_ok))
      \\ impl_tac
      >- (
        drule_then assume_tac state_ok_init_context
        \\ assume_tac env_ok_init_context \\ gs []
        \\ irule_at Any env_ok_extend_dec_env \\ gs [env_ok_init_env]
        \\ gs [state_ok_def, state_component_equality]
        \\ first_assum (irule_at Any) \\ gs [])
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
    \\ assume_tac Decls_basis_kernel
    \\ gs [ml_progTheory.Decls_def]
    \\ dxrule_then (qspec_then ‘k’ mp_tac) evaluate_decs_add_to_clock
    \\ dxrule_then (qspec_then ‘ck1’ mp_tac) evaluate_decs_add_to_clock
    \\ rw [] \\ gs [AllCaseEqs ()])
  \\



  ntac 2 strip_tac
  \\ reverse (Cases_on `res`)
  \\ fs [semanticsTheory.semantics_prog_def]
  >- (* Terminate *)
   (fs [semanticsTheory.evaluate_prog_with_clock_def]
    \\ pairarg_tac \\ fs []
    \\ rveq \\ fs []
    \\ drule kernel_evaluate_decs
    \\ disch_then drule
    \\ simp []
    \\ rw [EVERY_MEM, extract_events_def, MEM_MAP, PULL_EXISTS, MEM_FILTER,
           CaseEq "io_event"]
    \\ PURE_CASE_TAC \\ fs [] \\ rw []
    \\ fsrw_tac [SATISFY_ss] [])
     (* Diverge *)
  \\ fs [lprefix_lub_def, PULL_EXISTS, every_LNTH]
  \\ rw []
  \\ qabbrev_tac
    `ff : num -> io_event llist =
      \k. fromList (FST
        (evaluate_prog_with_clock
          (init_state ffi) init_env k (kernel_decls ++ prog))).io_events`
  \\ fs []
  \\ Cases_on `?k v. LNTH n (ff k) = SOME v` \\ fs []
  >-
   (first_x_assum (qspec_then `k` assume_tac)
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
    \\ srw_tac [SATISFY_ss] [])
  \\ `!k. LNTH n (ff k) = NONE` by metis_tac [option_nchotomy] \\ fs []
  \\ `F` suffices_by fs [] \\ rw []
  \\ qpat_x_assum `!ub. _ ==> _` mp_tac
  \\ simp []
  \\ drule LNTH_LTAKE \\ rw []
  \\ qexists_tac `fromList ll` \\ fs []
  \\ fsrw_tac [SATISFY_ss] [LTAKE_LPREFIX, LPREFIX_lemma]
QED


val _ = export_theory ();

