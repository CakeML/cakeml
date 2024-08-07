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

Theorem evaluate_SimpSeq[local,simp]:
  evaluate (SimpSeq p1 p2,s) = evaluate (Seq p1 p2,^s)
Proof
  rw [SimpSeq_def,evaluate_Seq_Skip]
  \\ Cases_on ‘p1’ \\ gvs [evaluate_Skip_Seq]
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
QED

Theorem extract_labels_Seq_assoc_right_lemma:
  ∀p1 p2. set (extract_labels (Seq_assoc_right p1 p2)) ⊆
          set (extract_labels p1) ∪ set (extract_labels p2)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,extract_labels_def,extract_labels_SimpSeq]
  \\ cheat
QED

Theorem extract_labels_Seq_assoc_right:
   set (extract_labels (Seq_assoc_right Skip p)) ⊆ set (extract_labels p)
Proof
  irule SUBSET_TRANS
  \\ irule_at (Pos hd) extract_labels_Seq_assoc_right_lemma
  \\ gvs [extract_labels_def]
QED

Theorem remove_unreach_wf_cutsets:
  wf_cutsets p ⇒ wf_cutsets (remove_unreach p)
Proof
  cheat
QED

val _ = export_theory();
