open preamble wordLangTheory wordSemTheory wordPropsTheory word_simpTheory;

val _ = new_theory "word_simpProof";

val s = ``s:('a,'ffi) wordSem$state``

(* verification of Seq_assoc *)

val evaluate_SmartSeq = Q.store_thm("evaluate_SmartSeq",
  `evaluate (SmartSeq p1 p2,s) = evaluate (Seq p1 p2,^s)`,
  rw [SmartSeq_def,evaluate_def]);

val evaluate_Seq_Skip = Q.store_thm("evaluate_Seq_Skip",
  `!p1 s. evaluate (Seq p1 Skip,s) = evaluate (p1,^s)`,
  Induct \\ fs [evaluate_def] \\ rw []
  \\ rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs []));

val evaluate_Skip_Seq = Q.store_thm("evaluate_Skip_Seq",
  `evaluate (Seq Skip p,s) = evaluate (p,^s)`,
  fs [evaluate_def]);

val evaluate_Seq_assoc_lemma = Q.store_thm("evaluate_Seq_assoc_lemma",
  `!p1 p2 s. evaluate (Seq_assoc p1 p2,s) = evaluate (Seq p1 p2,^s)`,
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [evaluate_SmartSeq,Seq_assoc_def,evaluate_Seq_Skip,evaluate_def]
  \\ (rpt (pairarg_tac \\ fs [] \\ rw [] \\ fs []))
  \\ Cases_on `get_vars args s1` \\ fs []
  \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ret_prog` \\ fs []
  \\ Cases_on `handler` \\ fs []
  \\ fs [add_ret_loc_def]
  \\ PairCases_on `x'` \\ fs[add_ret_loc_def]
  \\ PairCases_on `x''` \\ fs[add_ret_loc_def,push_env_def])

val evaluate_Seq_assoc = Q.store_thm("evaluate_Seq_assoc",
  `!p s. evaluate (Seq_assoc Skip p,s) = evaluate (p,^s)`,
  fs [evaluate_Seq_assoc_lemma,evaluate_def]);

val extract_labels_SmartSeq = Q.store_thm("extract_labels_SmartSeq",
  `extract_labels (SmartSeq p1 p2) = extract_labels (Seq p1 p2)`,
  rw [SmartSeq_def,extract_labels_def]);

val extract_labels_Seq_assoc_lemma = Q.store_thm("extract_labels_Seq_assoc_lemma",
  `!p1 p2. extract_labels (Seq_assoc p1 p2) =
            extract_labels p1 ++ extract_labels p2`,
  HO_MATCH_MP_TAC Seq_assoc_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_def,extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `ret_prog` \\ Cases_on `handler` \\ fs []
  \\ PairCases_on `x` \\ fs []
  \\ PairCases_on `x'` \\ fs []);

val extract_labels_Seq_assoc = Q.store_thm("extract_labels_Seq_assoc",
  `extract_labels (Seq_assoc Skip p) = extract_labels p`,
  fs [extract_labels_Seq_assoc_lemma,extract_labels_def]);

(* verification of simp_if *)

val dest_If_Eq_Imm_thm = Q.store_thm("dest_If_Eq_Imm_thm",
  `dest_If_Eq_Imm x2 = SOME (n,w,p1,p2) <=>
    x2 = If Equal n (Imm w) p1 p2`,
  Cases_on `x2` \\ fs [dest_If_Eq_Imm_def,dest_If_def]
  \\ every_case_tac \\ fs []);

val dest_If_thm = Q.store_thm("dest_If_thm",
  `dest_If x2 = SOME (g1,g2,g3,g4,g5) <=> x2 = If g1 g2 g3 g4 g5`,
  Cases_on `x2` \\ fs [dest_If_def]);

val dest_Seq_IMP = Q.store_thm("dest_Seq_IMP",
  `dest_Seq p1 = (x1,x2) ==> evaluate (p1,s) = evaluate (Seq x1 x2,^s)`,
  Cases_on `p1` \\ fs [SmartSeq_def,dest_Seq_def]
  \\ rw [] \\ fs [evaluate_Skip_Seq]);

val dest_Seq_Assign_Const_IMP = Q.store_thm("dest_Seq_Assign_Const_IMP",
  `dest_Seq_Assign_Const v p = SOME (q,w) ==>
    evaluate (p,s) = evaluate (Seq q (Assign v (Const w)),^s)`,
  fs [dest_Seq_Assign_Const_def] \\ pairarg_tac \\ fs []
  \\ Cases_on `p2` \\ fs [] \\ Cases_on `e` \\ fs []
  \\ rw [] \\ imp_res_tac dest_Seq_IMP \\ fs []);

val evaluate_apply_if_opt = Q.store_thm("evaluate_apply_if_opt",
  `apply_if_opt p1 p2 = SOME x ==>
    evaluate (Seq p1 p2,s) = evaluate (x,^s)`,
  fs [apply_if_opt_def]
  \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs []
  \\ fs [dest_If_Eq_Imm_thm] \\ strip_tac \\ rveq
  \\ fs [evaluate_SmartSeq]
  \\ imp_res_tac dest_Seq_IMP \\ fs []
  \\ fs [dest_If_thm]
  \\ fs [evaluate_def]
  \\ Cases_on `evaluate (x0,s)` \\ fs []
  \\ rename1 `evaluate (x0,s) = (res1,s1)` \\ fs []
  \\ Cases_on `res1` \\ fs []
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ fs [])
  \\ fs [get_var_imm_def]
  \\ imp_res_tac dest_Seq_Assign_Const_IMP \\ fs []
  \\ rename1 `dest_Seq_Assign_Const v1 t1 = SOME (t1a,w1)`
  \\ qpat_x_assum `dest_Seq_Assign_Const v1 t1 = SOME (t1a,w1)` mp_tac
  \\ rename1 `dest_Seq_Assign_Const v2 t2 = SOME (t2a,w2)`
  \\ qpat_x_assum `dest_Seq_Assign_Const v2 t2 = SOME (t2a,w2)` mp_tac
  \\ rw [] \\ rpt (qpat_x_assum `!x._` kall_tac)
  \\ fs [evaluate_def]
  \\ pairarg_tac \\ fs [] \\ rveq \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ pairarg_tac \\ fs [] \\ fs []
  \\ Cases_on `res' = NONE` \\ fs [word_exp_def] \\ rveq
  \\ fs [get_var_def,set_var_def,asmSemTheory.word_cmp_def]);

val evaluate_simp_if = Q.store_thm("evaluate_simp_if",
  `!p s. evaluate (simp_if p,s) = evaluate (p,^s)`,
  HO_MATCH_MP_TAC simp_if_ind \\ fs [simp_if_def,evaluate_def] \\ rw []
  THEN1
   (CASE_TAC \\ fs [evaluate_def]
    \\ imp_res_tac evaluate_apply_if_opt \\ fs []
    \\ pop_assum (fn th => once_rewrite_tac [GSYM th])
    \\ fs [evaluate_def])
  \\ Cases_on `get_vars args s` \\ fs [] \\ IF_CASES_TAC \\ fs []
  \\ Cases_on `ret_prog` \\ fs []
  \\ Cases_on `handler` \\ fs [] \\ fs [add_ret_loc_def]
  \\ PairCases_on `x'` \\ fs[add_ret_loc_def,push_env_def]
  \\ TRY (PairCases_on `x''`) \\ fs[add_ret_loc_def,push_env_def]);

val simp_if_works = Q.store_thm("simp_if_works",
  `IS_SOME (apply_if_opt
     (If Less 5 (Imm 5w) (Assign 3 (Const 5w)) (Assign 3 (Const (4w:word32))))
     (If Equal 3 (Imm (4w:word32)) (Raise 1) (Raise 2)))`,
  EVAL_TAC);

val extract_labels_apply_if_opt = Q.store_thm("extract_labels_apply_if_opt",
  `apply_if_opt p1 p2 = SOME p ==>
    PERM (extract_labels p) (extract_labels p1 ++ extract_labels p2)`,
  fs [apply_if_opt_def]
  \\ every_case_tac \\ fs [] \\ pairarg_tac \\ fs []
  \\ every_case_tac \\ fs [] \\ rw []
  \\ fs [dest_If_thm,dest_If_Eq_Imm_thm] \\ rveq
  \\ fs [extract_labels_def,extract_labels_SmartSeq]
  \\ Cases_on `p1` \\ fs [dest_Seq_def] \\ rveq \\ fs [extract_labels_def]
  \\ metis_tac[PERM_APPEND,APPEND_ASSOC,PERM_APPEND_IFF])

val extract_labels_simp_if = Q.store_thm("extract_labels_simp_if",
  `!p. PERM (extract_labels (simp_if p)) (extract_labels p)`,
  HO_MATCH_MP_TAC simp_if_ind \\ fs [simp_if_def] \\ rw []
  \\ fs [extract_labels_def]
  \\ every_case_tac \\ fs [extract_labels_def]
  \\ imp_res_tac extract_labels_apply_if_opt
  \\ metis_tac[PERM_APPEND,PERM_TRANS,PERM_APPEND_IFF])

(* putting it all together *)

val compile_exp_thm = Q.store_thm("compile_exp_thm",
  `wordSem$evaluate (prog,^s) = (res,s2) /\ res <> SOME Error ==>
    evaluate (word_simp$compile_exp prog,s) = (res,s2)`,
  fs [word_simpTheory.compile_exp_def,evaluate_simp_if,evaluate_Seq_assoc]);

val extract_labels_compile_exp = Q.store_thm("extract_labels_compile_exp[simp]",
  `!p. PERM (extract_labels (word_simp$compile_exp p)) (extract_labels p)`,
  fs [word_simpTheory.compile_exp_def]>>
  metis_tac[extract_labels_simp_if,extract_labels_Seq_assoc,PERM_TRANS])

val _ = export_theory();
