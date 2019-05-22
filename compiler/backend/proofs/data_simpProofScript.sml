(*
  Correctness proof for data_simp
*)
open preamble data_simpTheory dataSemTheory dataPropsTheory;

val _ = new_theory"data_simpProof";

val _ = set_grammar_ancestry ["data_simp", "dataSem", "dataProps"];

val evaluate_Seq_Skip = Q.prove(
  `!c s. evaluate (Seq c Skip,s) = evaluate (c,s)`,
  fs [evaluate_def,LET_DEF] \\ REPEAT STRIP_TAC
  \\ Cases_on `evaluate (c,s)` \\ fs [] \\ SRW_TAC [] []);

val evaluate_pSeq = Q.prove(
  `evaluate (pSeq c1 c2, s) = evaluate (Seq c1 c2, s)`,
  SRW_TAC [] [pSeq_def] \\ fs [evaluate_Seq_Skip]);

val evaluate_simp = Q.prove(
  `!c1 s c2. evaluate (simp c1 c2,s) = evaluate (Seq c1 c2,s)`,
  recInduct evaluate_ind \\ reverse (REPEAT STRIP_TAC) THEN1
   (Cases_on `handler` \\ fs [simp_def,evaluate_pSeq]
    \\ Cases_on `x` \\ fs [simp_def,evaluate_pSeq]
    \\ fs [evaluate_def]
    \\ every_case_tac >> fs[evaluate_def,LET_THM]
    \\ Cases_on `evaluate (r,set_var q a r''')` \\ fs []
    \\ Cases_on `q'` \\ fs [])
  \\ fs [simp_def,evaluate_def,LET_DEF,evaluate_pSeq,evaluate_pSeq]
  \\ Cases_on `evaluate (c1,s)` \\ fs []
  \\ Cases_on `evaluate (c2,r)` \\ fs []
  \\ Cases_on `evaluate (c2,set_var n a r)` \\ fs []
  \\ rw[] >> every_case_tac \\ fs [evaluate_def] \\ fs []
  \\ CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV))
  \\ every_case_tac >> fs[evaluate_def]);

Theorem simp_correct:
   !c s. evaluate (simp c Skip,s) = evaluate (c,s)
Proof
  SIMP_TAC std_ss [evaluate_simp,evaluate_Seq_Skip]
QED

Theorem get_code_labels_simp:
   ∀x y. get_code_labels (simp x y) ⊆ get_code_labels x ∪ get_code_labels y
Proof
  recInduct data_simpTheory.simp_ind
  \\ rw[data_simpTheory.simp_def]
  \\ fs[SUBSET_DEF, data_simpTheory.pSeq_def] \\ rw[]
  \\ metis_tac[]
QED

val _ = export_theory();
