(*
  Correctness proof for word_unreach
*)
open preamble wordLangTheory wordSemTheory wordPropsTheory word_unreachTheory;

val _ = new_theory "word_unreachProof";

val s = ``s:('a,'c,'ffi) wordSem$state``

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_unreach"];

(* -- proofs about semantics -- *)

Theorem evaluate_Skip_Seq:
   evaluate (Seq Skip p,s) = evaluate (p,^s)
Proof
  fs [evaluate_def]
QED

Theorem evaluate_Seq_Skip:
   !p1 s. evaluate (Seq p1 Skip,s) = evaluate (p1,^s)
Proof
  Induct \\ fs [evaluate_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs [])
QED

Theorem evaluate_Seq_assoc:
  evaluate (Seq p1 (Seq p2 p3), s) = evaluate (Seq (Seq p1 p2) p3, s)
Proof
  gvs [evaluate_def] \\ rpt (pairarg_tac \\ gvs []) \\ rw [] \\ gvs []
QED

Theorem merge_moves_thm:
  ∀p n l1 l2 s.
    evaluate (Seq (Move n l1) (Seq (Move n l2) p),s) =
    evaluate (Seq (Move n (merge_moves l1 l2)) p,s)
Proof
  cheat
QED

Theorem merge_moves_Skip =
  merge_moves_thm |> Q.SPEC ‘Skip’
                  |> SRULE [evaluate_Seq_Skip,evaluate_Seq_assoc]

Theorem evaluate_SimpSeq[local,simp]:
  evaluate (SimpSeq p1 p2,s) = evaluate (Seq p1 p2,^s)
Proof
  Cases_on ‘SimpSeq p1 p2 = Seq p1 p2’ >- simp []
  \\ gvs [SimpSeq_def,evaluate_Seq_Skip]
  \\ gvs [AllCaseEqs(),evaluate_Seq_Skip]
  \\ rw [evaluate_Seq_Skip]
  \\ Cases_on ‘p1’ \\ gvs [evaluate_Skip_Seq]
  >~ [‘dest_Seq_Move’] >-
   (Cases_on ‘dest_Seq_Move p2’ \\ gvs []
    \\ PairCases_on ‘x’ \\ gvs []
    \\ gvs [oneline dest_Seq_Move_def,AllCaseEqs()] \\ rw []
    \\ gvs [merge_moves_Skip,merge_moves_thm,evaluate_Seq_Skip])
  \\ gvs [evaluate_def]
  \\ pairarg_tac \\ gvs [] \\ rw [] \\ gvs []
  \\ gvs [evaluate_def,AllCaseEqs()]
QED

Theorem evaluate_Seq_assoc_right_lemma:
  ∀p1 p2 s. evaluate (Seq_assoc_right p1 p2,s) = evaluate (Seq p1 p2,^s)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,evaluate_Seq_Skip,evaluate_Skip_Seq]
  >- (gvs [evaluate_def] \\ rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs []))
  >- (gvs [evaluate_def] \\ rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs []))
  >- (gvs [evaluate_def] \\ rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs []))
  \\ Cases_on ‘ret_prog’ \\ gvs []
  >- (gvs [evaluate_def] \\ pairarg_tac \\ gvs [AllCaseEqs()])
  \\ PairCases_on ‘x’ \\ gvs []
  \\ gvs [evaluate_def] \\ pairarg_tac
  \\ Cases_on ‘handler’
  >- (gvs [AllCaseEqs(),add_ret_loc_def,flush_state_def,call_env_def,push_env_def,dec_clock_def]
      \\ CCONTR_TAC \\ gvs [])
  \\ PairCases_on ‘x’
  \\ gvs [AllCaseEqs(),add_ret_loc_def,flush_state_def,call_env_def,push_env_def,dec_clock_def]
  \\ CCONTR_TAC \\ gvs []
QED

Theorem evaluate_remove_unreach:
  ∀p s. evaluate (remove_unreach p,s) = evaluate (p,s)
Proof
  fs [evaluate_Seq_assoc_right_lemma,evaluate_def,remove_unreach_def]
  \\ rw [] \\ pairarg_tac \\ gvs [] \\ rw [] \\ gvs []
QED

(* -- proofs about syntax -- *)

Theorem extract_labels_SimpSeq:
  set (extract_labels (SimpSeq p1 p2)) ⊆  set (extract_labels (Seq p1 p2))
Proof
  rw [SimpSeq_def,extract_labels_def]
  \\ Cases_on ‘p1’ \\ rw [extract_labels_def] \\ gvs [SUBSET_DEF]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [extract_labels_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), extract_labels_def]
QED

Theorem extract_labels_Seq_assoc_right_lemma:
  ∀p1 p2. set (extract_labels (Seq_assoc_right p1 p2)) ⊆
          set (extract_labels p1) ∪ set (extract_labels p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  >- (
    gvs[SUBSET_DEF]
    \\ metis_tac[])
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[extract_labels_def]
    \\ irule SUBSET_TRANS
    \\ irule_at Any extract_labels_SimpSeq
    \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
    \\ gvs[SUBSET_DEF]
  )
  \\ irule SUBSET_TRANS
  \\ irule_at Any extract_labels_SimpSeq
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  \\ gvs[SUBSET_DEF]
QED

Theorem extract_labels_remove_unreach:
   set (extract_labels (remove_unreach p)) ⊆ set (extract_labels p)
Proof
  simp[remove_unreach_def]
  \\ irule SUBSET_TRANS
  \\ irule_at (Pos hd) extract_labels_Seq_assoc_right_lemma
  \\ gvs [extract_labels_def]
QED

Theorem wf_cutsets_SimpSeq:
  wf_cutsets p1 ∧ wf_cutsets p2 ⇒
  wf_cutsets (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,wf_cutsets_def]
  \\ Cases_on ‘p1’ \\ rw [wf_cutsets_def]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [wf_cutsets_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), wf_cutsets_def]
QED

Theorem wf_cutsets_Seq_assoc_right_lemma:
  ∀p1 p2.
  wf_cutsets p1 ∧ wf_cutsets p2 ⇒
  wf_cutsets (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,wf_cutsets_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[wf_cutsets_def]
    \\ match_mp_tac wf_cutsets_SimpSeq
    \\ gvs[wf_cutsets_def])
  \\ match_mp_tac wf_cutsets_SimpSeq
  \\ gvs[wf_cutsets_def]
QED

Theorem wf_cutsets_remove_unreach:
  wf_cutsets p ⇒ wf_cutsets (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule wf_cutsets_Seq_assoc_right_lemma
  \\ gvs[wf_cutsets_def]
QED

Theorem every_inst_distinct_tar_reg_SimpSeq:
  every_inst distinct_tar_reg p1 ∧ every_inst distinct_tar_reg p2 ⇒
  every_inst distinct_tar_reg (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,every_inst_def]
  \\ Cases_on ‘p1’ \\ rw [every_inst_def]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [every_inst_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), every_inst_def]
QED

Theorem every_inst_distinct_tar_reg_Seq_assoc_right_lemma:
  ∀p1 p2.
  every_inst distinct_tar_reg p1 ∧ every_inst distinct_tar_reg p2 ⇒
  every_inst distinct_tar_reg (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,every_inst_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[every_inst_def]
    \\ match_mp_tac every_inst_distinct_tar_reg_SimpSeq
    \\ gvs[every_inst_def])
  \\ match_mp_tac every_inst_distinct_tar_reg_SimpSeq
  \\ gvs[every_inst_def]
QED

Theorem every_inst_distinct_tar_reg_remove_unreach:
  every_inst distinct_tar_reg p ⇒
  every_inst distinct_tar_reg (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule every_inst_distinct_tar_reg_Seq_assoc_right_lemma
  \\ gvs[every_inst_def]
QED

Theorem flat_exp_conventions_SimpSeq:
  flat_exp_conventions p1 ∧ flat_exp_conventions p2 ⇒
  flat_exp_conventions (SimpSeq p1 p2)
Proof
  rw [SimpSeq_def,flat_exp_conventions_def]
  \\ Cases_on ‘p1’ \\ rw [flat_exp_conventions_def]
  \\ Cases_on ‘dest_Seq_Move p2’ \\ gvs []
  \\ rw [flat_exp_conventions_def] \\ gvs [SUBSET_DEF]
  \\ PairCases_on ‘x’ \\ gvs []
  \\ pop_assum mp_tac \\ rw []
  \\ gvs [oneline dest_Seq_Move_def, AllCaseEqs(), flat_exp_conventions_def]
QED

Theorem flat_exp_conventions_Seq_assoc_right_lemma:
  ∀p1 p2.
  flat_exp_conventions p1 ∧ flat_exp_conventions p2 ⇒
  flat_exp_conventions (Seq_assoc_right p1 p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,flat_exp_conventions_def]
  >~ [`Call`]
  >- (
    every_case_tac \\ gvs[flat_exp_conventions_def]
    \\ match_mp_tac flat_exp_conventions_SimpSeq
    \\ gvs[flat_exp_conventions_def])
  \\ match_mp_tac flat_exp_conventions_SimpSeq
  \\ gvs[flat_exp_conventions_def]
QED

Theorem flat_exp_conventions_remove_unreach:
  flat_exp_conventions p ⇒
  flat_exp_conventions (remove_unreach p)
Proof
  rw[remove_unreach_def]
  \\ irule flat_exp_conventions_Seq_assoc_right_lemma
  \\ gvs[flat_exp_conventions_def]
QED

val _ = export_theory();
