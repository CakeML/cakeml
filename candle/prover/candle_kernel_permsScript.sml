(*
  Prove perms theorems for kernel functions
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory sptreeTheory
     evaluateTheory namespacePropsTheory evaluatePropsTheory;
open permsTheory ml_hol_kernelProgTheory ast_extrasTheory;

val _ = new_theory "candle_kernel_perms";

val _ = set_grammar_ancestry ["ml_hol_kernelProg", "perms", "misc"];

Theorem perms_ok_concl:
  perms_ok ∅ concl_v
Proof
  cheat
QED

Theorem trans_v_perms_ok:
  perms_ok ps trans_v
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

val _ = export_theory ();
