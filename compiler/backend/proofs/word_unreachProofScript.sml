(*
  Correctness proof for word_unreach
*)
open preamble wordLangTheory wordSemTheory wordPropsTheory wordConvsTheory word_unreachTheory;

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

Theorem ALL_DISTINCT_merge_moves:
  ALL_DISTINCT (MAP FST (merge_moves l1 l2))
Proof
  gvs [merge_moves_def]
  \\ metis_tac [miscTheory.anub_all_distinct_keys,APPEND_NIL,ALL_DISTINCT]
QED

Definition copy_vars_def:
  copy_vars [] from to = to ∧
  copy_vars ((l,r)::rest) from to =
    insert l (THE (lookup r from)) (copy_vars rest from to)
End

Theorem copy_vars_append:
  ∀xs ys from to.
    copy_vars (xs ++ ys) from to = copy_vars xs from (copy_vars ys from to)
Proof
  Induct \\ gvs [copy_vars_def]
  \\ PairCases \\ gvs [copy_vars_def]
QED

Theorem evaluate_Move:
  evaluate (Move pri moves,s) =
  if ALL_DISTINCT (MAP FST moves) then
    case get_vars (MAP SND moves) s of
      NONE => (SOME Error,s)
    | SOME l => (NONE,s with locals := copy_vars moves s.locals s.locals)
  else (SOME Error,s)
Proof
  gvs [evaluate_def]
  \\ IF_CASES_TAC \\ gvs []
  \\ CASE_TAC \\ gvs []
  \\ gvs [set_vars_def,state_component_equality]
  \\ pop_assum mp_tac
  \\ qsuff_tac ‘
    ∀moves x t.
      get_vars (MAP SND moves) s = SOME x ⇒
      alist_insert (MAP FST moves) x t =
      copy_vars moves s.locals t’
  >- (rw [] \\ res_tac \\ gvs [])
  \\ Induct \\ gvs [get_vars_def,alist_insert_def,copy_vars_def]
  \\ PairCases \\ gvs [AllCaseEqs()] \\ rw []
  \\ gvs [copy_vars_def,alist_insert_def,get_var_def]
QED

Theorem copy_vars_MEM_acc:
  ∀xs acc n w.
    MEM n acc ⇒
    insert n w (copy_vars (anub xs acc) s t) =
    insert n w (copy_vars (anub xs (FILTER (λx. n ≠ x) acc)) s t)
Proof
  Induct \\ gvs [anub_def,FORALL_PROD]
  \\ rpt gen_tac \\ gvs [MEM_FILTER]
  \\ Cases_on ‘n = p_1’ \\ gvs []
  \\ gvs [copy_vars_def]
  \\ simp [Once insert_insert]
  \\ gvs [FILTER_FILTER]
  \\ IF_CASES_TAC \\ gvs []
  \\ gvs [copy_vars_def]
  \\ once_rewrite_tac [insert_insert]
  \\ IF_CASES_TAC \\ gvs []
  \\ strip_tac \\ AP_TERM_TAC
  \\ ‘MEM n (FILTER (λx. p_1 ≠ x) acc)’ by gvs [MEM_FILTER]
  \\ last_x_assum drule
  \\ strip_tac \\ gvs []
  \\ gvs [FILTER_FILTER,AC CONJ_COMM CONJ_ASSOC]
QED

Theorem copy_vars_anub:
  copy_vars (anub xs []) = copy_vars xs
Proof
  Induct_on ‘xs’ \\ gvs [anub_def,FORALL_PROD,copy_vars_def,FUN_EQ_THM]
  \\ gvs [copy_vars_MEM_acc]
QED

Theorem lookup_copy_vars_ignore:
  ∀l1 h1 x y.
    ALOOKUP l1 h1 = NONE ⇒
    lookup h1 (copy_vars l1 x y) = lookup h1 y
Proof
  Induct \\ gvs [copy_vars_def]
  \\ PairCases \\ gvs [copy_vars_def] \\ rw []
  \\ gvs [lookup_insert]
QED

Theorem lookup_copy_vars:
  ∀l1 h1 y s t z.
    ALOOKUP l1 h1 = SOME y ∧
    lookup h1 (copy_vars l1 s t) = SOME z ⇒
    THE (lookup y s) = z
Proof
  Induct \\ gvs [copy_vars_def]
  \\ PairCases \\ gvs [] \\ rw []
  \\ gvs [copy_vars_def,lookup_insert]
  \\ res_tac \\ gvs []
QED

Triviality get_vars_IS_SOME_lookup:
  ∀xs s.
    (∃ws. get_vars xs s = SOME ws)
    ⇔
    EVERY (λx. IS_SOME (lookup x s.locals)) xs
Proof
  Induct
  \\ gvs [get_vars_def,get_var_def,AllCaseEqs(),PULL_EXISTS]
  \\ rpt gen_tac
  \\ Cases_on ‘lookup h s.locals’ \\ gvs []
QED

Theorem IMP_EVERY_MAP_SND_anub:
  ∀xs acc p.
    EVERY p (MAP SND xs) ⇒
    EVERY p (MAP SND (anub xs acc))
Proof
  Induct \\ gvs [anub_def,FORALL_PROD] \\ rw []
QED

Theorem merge_moves_Skip:
  ∀l1 l2 s res s1.
    evaluate (Seq (Move n1 l1) (Move n2 l2),s) = (res,s1) ∧
    res ≠ SOME Error ⇒
    evaluate (Move m (merge_moves l1 l2),s) = (res,s1)
Proof
  simp [Once evaluate_def,evaluate_Move] \\ rpt gen_tac
  \\ rpt gen_tac
  \\ pairarg_tac \\ gvs []
  \\ strip_tac
  \\ gvs [AllCaseEqs(),ALL_DISTINCT_merge_moves]
  \\ gvs [state_component_equality]
  \\ ‘∃ws. get_vars (MAP SND (merge_moves l1 l2)) s = SOME ws’ by
    (simp [get_vars_IS_SOME_lookup]
     \\ gvs [merge_moves_def]
     \\ irule IMP_EVERY_MAP_SND_anub
     \\ imp_res_tac get_vars_IS_SOME_lookup
     \\ gvs [MAP_APPEND,MAP_MAP_o,o_DEF]
     \\ gvs [LAMBDA_PROD,EVERY_MAP]
     \\ gvs [EVERY_MEM]
     \\ PairCases \\ gvs [FORALL_PROD]
     \\ Cases_on ‘ALOOKUP l1 e1’ \\ gvs []
     \\ rw [] \\ res_tac \\ gvs [lookup_copy_vars_ignore]
     \\ Cases_on ‘lookup e1 (copy_vars l1 s.locals s.locals)’
     \\ gvs []
     \\ drule_all lookup_copy_vars
     \\ Cases_on ‘lookup x s.locals’ \\ gvs []
     \\ imp_res_tac ALOOKUP_MEM
     \\ res_tac \\ gvs [])
  \\ gvs [] \\ gvs [merge_moves_def]
  \\ pop_assum kall_tac
  \\ gvs [copy_vars_anub]
  \\ gvs [copy_vars_append]
  \\ AP_THM_TAC \\ gvs [FUN_EQ_THM] \\ gen_tac
  \\ qpat_x_assum ‘ALL_DISTINCT (MAP FST l2)’ mp_tac
  \\ rename [‘_ = SOME zs’]
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘zs’
  \\ qid_spec_tac ‘l2’
  \\ Induct
  >- gvs [get_vars_def,copy_vars_def]
  \\ PairCases \\ gvs [get_vars_def]
  \\ simp [AllCaseEqs(),get_var_def]
  \\ rpt strip_tac \\ gvs []
  \\ Cases_on ‘ALOOKUP l1 h1’ \\ gvs []
  >- (gvs [copy_vars_def,lookup_copy_vars_ignore])
  \\ gvs [copy_vars_def]
  \\ drule_all lookup_copy_vars
  \\ gvs []
QED

Theorem merge_moves_thm:
  ∀p l1 l2 s res s1.
    evaluate (Seq (Move n1 l1) (Seq (Move n2 l2) p),s) = (res,s1) ∧
    res ≠ SOME Error ⇒
    evaluate (Seq (Move m (merge_moves l1 l2)) p,s) = (res,s1)
Proof
  rewrite_tac [evaluate_Seq_assoc]
  \\ once_rewrite_tac [evaluate_def]
  \\ gvs [] \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ rpt strip_tac
  \\ rename [‘evaluate (Seq (Move n1 l1) (Move n2 l2),s) = (res2,s2)’]
  \\ Cases_on ‘res2 = SOME Error’ \\ gvs []
  \\ drule_all merge_moves_Skip
  \\ strip_tac \\ gvs []
QED

Theorem evaluate_SimpSeq[local]:
  evaluate (Seq p1 p2,s) = (res,s1) ∧ res ≠ SOME Error ⇒
  evaluate (SimpSeq p1 p2,s) = (res,s1)
Proof
  Cases_on ‘SimpSeq p1 p2 = Seq p1 p2’ >- simp []
  \\ gvs [SimpSeq_def,evaluate_Seq_Skip]
  \\ gvs [AllCaseEqs(),evaluate_Seq_Skip]
  \\ rw [evaluate_Seq_Skip]
  \\ Cases_on ‘p1’ \\ gvs [evaluate_Skip_Seq]
  >~ [‘dest_Seq_Move’] >- (
    Cases_on ‘dest_Seq_Move p2’ \\ gvs []
    \\ PairCases_on ‘x’ \\ gvs []
    \\ gvs [oneline dest_Seq_Move_def,AllCaseEqs()] \\ rw []
    >- (
      drule_all merge_moves_Skip \\ gvs [])
    >- (
      gvs [evaluate_Seq_assoc,evaluate_Seq_Skip,merge_moves_Skip]
      \\ drule_all merge_moves_Skip \\ gvs [])
    \\ gvs [evaluate_Seq_assoc,evaluate_Seq_Skip,merge_moves_Skip]
    \\ gvs [GSYM evaluate_Seq_assoc]
    \\ drule_all merge_moves_thm \\ gvs [])
  \\ gvs [evaluate_def]
  \\ pairarg_tac \\ gvs [] \\ rw [] \\ gvs []
  \\ gvs [evaluate_def,AllCaseEqs()]
QED

Triviality push_env_handler:
  push_env x' (case handler of
               | NONE => NONE
               | SOME (y1,q2,y2,y3) => SOME (y1,Seq_assoc_right q2 Skip,y2,y3))
              (dec_clock s) =
  push_env x' handler (dec_clock s)
Proof
  Cases_on ‘handler’ \\ gvs [push_env_def]
  \\ PairCases_on ‘x’ \\ gvs [push_env_def,FUN_EQ_THM]
QED

Theorem evaluate_Seq_assoc_right_lemma:
  ∀p1 p2 s res s1.
    evaluate (Seq p1 p2,^s) = (res,s1) ∧ res ≠ SOME Error ⇒
    evaluate (Seq_assoc_right p1 p2,s) = (res,s1)
Proof
  HO_MATCH_MP_TAC Seq_assoc_right_ind \\ fs [] \\ rw []
  \\ fs [Seq_assoc_right_def,evaluate_Seq_Skip,evaluate_Skip_Seq]
  \\ TRY (irule evaluate_SimpSeq \\ gvs [] \\ NO_TAC)
  >-
   (first_x_assum irule \\ simp []
    \\ qpat_x_assum ‘_ = (res,_)’ mp_tac
    \\ rewrite_tac [GSYM evaluate_Seq_assoc]
    \\ once_rewrite_tac [evaluate_def] \\ gvs []
    \\ pairarg_tac \\ gvs []
    \\ IF_CASES_TAC \\ gvs [])
  >-
   (irule evaluate_SimpSeq \\ gvs []
    \\ qpat_x_assum ‘_ = (res,_)’ mp_tac
    \\ once_rewrite_tac [evaluate_def] \\ gvs []
    \\ once_rewrite_tac [evaluate_def] \\ gvs []
    \\ pairarg_tac \\ gvs [] \\ gvs [AllCaseEqs()]
    \\ strip_tac \\ gvs []
    \\ last_x_assum drule \\ strip_tac \\ gvs [])
  >-
   (irule evaluate_SimpSeq \\ gvs []
    \\ qpat_x_assum ‘_ = (res,_)’ mp_tac
    \\ once_rewrite_tac [evaluate_def] \\ gvs []
    \\ once_rewrite_tac [evaluate_def] \\ gvs []
    \\ rpt (pairarg_tac \\ gvs [] \\ gvs [AllCaseEqs()])
    \\ strip_tac \\ gvs []
    \\ last_x_assum drule \\ strip_tac \\ gvs [])
  \\ Cases_on ‘ret_prog’ \\ gvs []
  >- (gvs [evaluate_def] \\ pairarg_tac \\ gvs [AllCaseEqs()])
  \\ PairCases_on ‘x’ \\ gvs []
  \\ irule evaluate_SimpSeq \\ gvs []
  \\ gvs [evaluate_def] \\ pairarg_tac
  \\ Cases_on ‘get_vars args s’ \\ gvs []
  \\ Cases_on ‘bad_dest_args dest args’ \\ gvs [add_ret_loc_def]
  \\ Cases_on ‘find_code dest (Loc x3 x4::x) s.code s.stack_size’ \\ gvs []
  \\ rename [‘_ = SOME y’] \\ PairCases_on ‘y’ \\ gvs []
  \\ Cases_on ‘domain x1 = ∅’ \\ gvs []
  \\ Cases_on ‘cut_env x1 s.locals’ \\ gvs []
  \\ Cases_on ‘s.clock = 0’
  >-
   (gvs [flush_state_def,state_component_equality,call_env_def,push_env_def]
    \\ Cases_on ‘handler’ \\ gvs [push_env_def]
    \\ PairCases_on ‘x''’ \\ gvs [push_env_def])
  \\ gvs [push_env_handler]
  \\ Cases_on ‘evaluate (y1,call_env y0 y2 (push_env x' handler (dec_clock s)))’
  \\ gvs [] \\ Cases_on ‘q’ \\ gvs []
  \\ rename [‘_ = (SOME t,_)’] \\ Cases_on ‘t’ \\ gvs []
  >-
   (gvs [AllCaseEqs()] \\ pairarg_tac \\ gvs []
    \\ rename [‘_ = (t,_)’] \\ Cases_on ‘t = SOME Error’ \\ gvs []
    \\ first_x_assum drule_all
    \\ strip_tac \\ gvs []
    \\ Cases_on ‘res'’ \\ gvs [])
  \\ Cases_on ‘handler’ \\ gvs []
  \\ PairCases_on ‘x''’ \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ pairarg_tac \\ gvs []
  \\ rename [‘_ = (t,_)’] \\ Cases_on ‘t = SOME Error’ \\ gvs []
  \\ last_x_assum drule_all
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘res'’ \\ gvs []
QED

Theorem evaluate_remove_unreach:
  ∀p s res s1.
    evaluate (p,s) = (res,s1) ∧ res ≠ SOME Error ⇒
    evaluate (remove_unreach p,s) = (res,s1)
Proof
  fs [evaluate_Seq_assoc_right_lemma,evaluate_def,remove_unreach_def] \\ rw []
  \\ irule evaluate_Seq_assoc_right_lemma \\ rw []
  \\ gvs [evaluate_Seq_Skip]
QED

(* -- proofs about syntax -- *)

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
