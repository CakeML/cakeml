(*
  Prove perms theorems for kernel functions
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory sptreeTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory
     candle_kernel_valsTheory;
open permsTheory ml_hol_kernelProgTheory ast_extrasTheory;

val _ = new_theory "candle_kernel_perms";

val _ = set_grammar_ancestry ["candle_kernel_vals", "perms", "misc"];

(* Functions translated with 'translate' should be proved for any ps *)

Theorem call_variant_v_perms_ok:
  ∀ps. perms_ok ps call_variant_v
Proof
  cheat
QED

Theorem perms_ok_concl:
  ∀ps. perms_ok ps concl_v
Proof
  cheat
QED

(* Functions translated with 'm_translate' should be proved for kernel_perms *)

Theorem trans_v_perms_ok:
  perms_ok kernel_perms trans_v
Proof
  cheat
QED

Theorem beta_v_perms_ok:
  perms_ok kernel_perms beta_v
Proof
  cheat
QED

(*
Theorem perms_ok_member_v:
  perms_ok ps member_v
Proof
  rw [member_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem perms_ok_list_union_v:
  perms_ok ps list_union_v
Proof
  rw [list_union_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "member"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_member_v]
QED

Theorem conj_v_perms_ok:
  perms_ok ps conj_v
Proof
  rw [conj_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "list_union"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_list_union_v]
QED

Theorem disj1_v_perms_ok:
  perms_ok ps disj1_v
Proof
  rw [disj1_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs []
        \\ CCONTR_TAC \\ gs [])
  \\ gs [perms_ok_env_def]
QED
*)

Triviality evaluate_kernel_perms_lemma:
  ∀ps.
    evaluate s env [exp] = (s',res) ∧
    perms_ok_exp ps exp ∧ perms_ok_env ps (freevars exp) env ∧ perms_ok_state ps s ∧
    DoFFI ∉ ps ∧ RefAlloc ∉ ps ∧ W8Alloc ∉ ps ⇒
    LENGTH s'.refs = LENGTH s.refs ∧
    s'.ffi = s.ffi ∧
    s'.eval_state = s.eval_state
Proof
  metis_tac [evaluate_perms_ok_exp]
QED

Theorem evaluate_kernel_perms =
  evaluate_kernel_perms_lemma
  |> Q.SPEC ‘kernel_perms’
  |> SIMP_RULE (srw_ss()) [kernel_perms_def]
  |> REWRITE_RULE [GSYM kernel_perms_def];

Theorem evaluate_empty_perms =
  evaluate_kernel_perms_lemma
  |> Q.SPEC ‘{}’
  |> SIMP_RULE (srw_ss()) [];

val _ = export_theory ();