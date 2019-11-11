(*
  Proofs about `size_of` and `size_of_heap`
*)

open preamble basis compilationLib;
open backendProofTheory backendPropsTheory;
open dataSemTheory data_monadTheory dataLangTheory;

val _ = new_theory "costProps"

(* Overload monad_unitbind[local] = ``bind`` *)
(* Overload return[local] = ``return`` *)

(* val _ = monadsyntax.temp_add_monadsyntax() *)

Theorem EVERY_lookup:
  ∀t. EVERY (\(k,v). lookup k t = SOME v) (toAList t)
Proof
  fs [EVERY_MEM,MEM_toAList,FORALL_PROD]
QED

(* MOVE: sptreeTheory *)
Theorem domain_IS_SOME:
  ∀t k. k ∈ domain t = IS_SOME (lookup k t)
Proof
  rw [domain_lookup,IS_SOME_EXISTS]
QED

Theorem size_of_Number_head:
  ∀vs refs seen n. size_of (Number n::vs) refs seen = size_of vs refs seen
Proof
  Cases \\ rw [size_of_def] \\ pairarg_tac \\ fs []
QED

Theorem size_of_seen_SUBSET:
  ∀vs refs seen n1 seen1 refs1.
  (size_of vs refs seen = (n1,refs1,seen1))
  ⇒ domain seen ⊆  domain seen1
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (ho_match_mp_tac SUBSET_TRANS
     \\ asm_exists_tac \\ fs [])
 \\ every_case_tac \\ fs []
 \\ first_x_assum irule
 \\ rpt (pairarg_tac \\ fs [])
QED

Theorem size_of_refs_SUBSET:
  ∀vs refs seen n1 seen1 refs1.
  (size_of vs refs seen = (n1,refs1,seen1))
  ⇒ domain refs1 ⊆  domain refs
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (ho_match_mp_tac SUBSET_TRANS
     \\ asm_exists_tac \\ fs [])
  \\ every_case_tac \\ fs []
  \\ rveq \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ ho_match_mp_tac SUBSET_TRANS
  \\ asm_exists_tac \\ fs []
QED

Theorem size_of_le_head:
  ∀vs refs seen v n1 seen1 refs1 n2 refs2 seen2.
   (size_of (v::vs) refs seen = (n1,refs1,seen1)) ∧
   (size_of vs refs seen = (n2,refs2,seen2))
   ⇒ n2 ≤ n1
Proof
  Cases \\ fs [size_of_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
QED

Theorem size_of_refs_SUBSET_head:
  ∀vs refs seen v n1 seen1 refs1 n2 refs2 seen2.
   (size_of (v::vs) refs seen = (n1,refs1,seen1)) ∧
   (size_of vs refs seen = (n2,refs2,seen2))
   ⇒ domain refs1 ⊆ domain refs2
Proof
  Cases \\ fs [size_of_def]
  \\ rw [] \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ ho_match_mp_tac size_of_refs_SUBSET
  \\ asm_exists_tac \\ fs []
QED

Theorem size_of_le_APPEND:
  ∀a b refs seen n1 seen1 refs1 n2 refs2 seen2.
   (size_of (a ++ b) refs seen = (n1,refs1,seen1)) ∧
   (size_of b refs seen = (n2,refs2,seen2))
   ⇒ n2 ≤ n1
Proof
  Induct
  >- (rw [] \\ fs [])
  \\ rw [] \\ irule LESS_EQ_TRANS
  \\ qexists_tac `FST (size_of (a++b) refs seen)`
  \\ Cases_on `size_of (a++b) refs seen` \\ Cases_on `r`
  \\ simp []
  \\ conj_tac
  >- (first_x_assum irule \\ metis_tac [])
  \\ (ho_match_mp_tac size_of_le_head \\ metis_tac [])
QED

Theorem size_of_refs_SUBSET_APPEND:
  ∀a b refs seen n1 seen1 refs1 n2 refs2 seen2.
   (size_of (a ++ b) refs seen = (n1,refs1,seen1)) ∧
   (size_of b refs seen = (n2,refs2,seen2))
   ⇒ domain refs1 ⊆ domain refs2
Proof
  Induct
  >- (rw [] \\ fs [])
  \\ rw [] \\ irule SUBSET_TRANS
  \\ qexists_tac `domain (FST (SND (size_of (a++b) refs seen)))`
  \\ Cases_on `size_of (a++b) refs seen` \\ Cases_on `r`
  \\ simp []
  \\ reverse conj_tac
  >- (first_x_assum irule \\ metis_tac [])
  \\ ho_match_mp_tac size_of_refs_SUBSET_head \\ metis_tac []
QED

Definition closed_ptrs_list_def:
  (closed_ptrs_list [] refs = T)
∧ (closed_ptrs_list (RefPtr p::vs) refs =
     IS_SOME (lookup p refs) ∧
     closed_ptrs_list vs refs)
∧ (closed_ptrs_list (Block ts tag l::vs) refs =
     closed_ptrs_list l refs ∧
     closed_ptrs_list vs refs)
∧ (closed_ptrs_list (v::vs) refs = closed_ptrs_list vs refs)
Termination
  WF_REL_TAC `(inv_image (measure v1_size) (\(vs,refs). vs))`
End


Definition closed_ptrs_refs_def:
  closed_ptrs_refs refs =
    ∀x l. (sptree$lookup x refs = SOME (ValueArray l))
        ⇒ closed_ptrs_list l refs
End

Definition closed_ptrs_def:
  closed_ptrs vs refs = closed_ptrs_list vs refs ∧ closed_ptrs_refs refs
End

Theorem closed_ptrs_cons_intro:
  ∀vs refs v. closed_ptrs (v::vs) refs ⇒ closed_ptrs vs refs ∧ closed_ptrs [v] refs
Proof
  ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_def,closed_ptrs_list_def]
  \\ Cases_on `v` \\ fs [closed_ptrs_list_def]
QED

Theorem closed_ptrs_cons_dest:
  ∀vs refs v. closed_ptrs vs refs ∧ closed_ptrs [v] refs ⇒ closed_ptrs (v::vs) refs
Proof
  ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_def,closed_ptrs_list_def]
  \\ Cases_on `v` \\ fs [closed_ptrs_list_def]
QED

Theorem closed_ptrs_cons:
  ∀vs refs v. closed_ptrs (v::vs) refs = closed_ptrs vs refs ∧ closed_ptrs [v] refs
Proof
  rw [] \\ eq_tac \\ fs [closed_ptrs_cons_dest]
  \\ rw [] \\ drule closed_ptrs_cons_intro \\ rw []
QED

Definition live_ptr_list_def:
  (live_ptr_list p [] = F)
∧ (live_ptr_list p (RefPtr n::vs) = ((p = n) ∨ live_ptr_list p vs))
∧ (live_ptr_list p (Block ts tag l::vs) = (live_ptr_list p l ∨ live_ptr_list p vs))
∧ (live_ptr_list p (v::vs) = live_ptr_list p vs)
Termination
  WF_REL_TAC `(inv_image (measure v1_size) (\(p,vs). vs))`
End

Definition live_ptr_def:
  (live_ptr p vs refs =
     live_ptr_list p vs ∨
     (∃x l. (sptree$lookup x refs = SOME (ValueArray l)) ∧
            live_ptr_list p l))
End

Theorem live_ptr_cons:
  ∀p vs refs v. live_ptr p (v::vs) refs = live_ptr p [v] refs ∨ live_ptr p vs refs
Proof
  ho_match_mp_tac live_ptr_list_ind \\ rw [live_ptr_def,live_ptr_list_def]
  \\ EQ_TAC \\ rw []
  \\ TRY (Cases_on `v` \\ fs [live_ptr_list_def] \\ NO_TAC)
  \\ metis_tac []
QED

Theorem size_of_refs_subspt:
  ∀vs refs seen n refs' seen'.
    (size_of vs refs seen = (n,refs',seen'))
    ⇒ subspt refs' refs
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (irule subspt_trans \\ metis_tac [])
  \\ EVERY_CASE_TAC \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [subspt_delete] \\ irule subspt_trans
  \\ asm_exists_tac \\ fs [subspt_delete]
QED

Theorem not_live_ptr_subspt:
  ∀vs refs refs' p.
    subspt refs' refs ∧
    ¬live_ptr p vs refs
    ⇒¬live_ptr p vs refs'
Proof
  rw [live_ptr_def] \\ fs []
  \\ first_x_assum (qspecl_then [`x`,`l`] assume_tac) \\ rw []
  >- (disj1_tac \\ CCONTR_TAC \\ fs [subspt_lookup]
     \\ first_x_assum drule \\ rw [])
  \\ disj2_tac \\ rw []
QED

Theorem live_ptr_ptr:
  ∀r refs l p.
   (lookup r refs = SOME (ValueArray l))
   ⇒ (live_ptr p [RefPtr r] refs = ((p = r) ∨ live_ptr p l refs))
Proof
  rw [] \\ EQ_TAC
  \\ rw [live_ptr_def] \\ fs [live_ptr_list_def]
  \\ metis_tac []
QED

Theorem live_ptr_delete:
  ∀vs p refs r l.
    p ≠ r ∧ (lookup r refs = SOME (ValueArray l))
    ⇒ (live_ptr p vs refs = live_ptr_list p l ∨ live_ptr p vs (delete r refs))
Proof
  rw []
  \\ EQ_TAC \\ rw [live_ptr_def] \\ fs [live_ptr_list_def]
  >- (Cases_on `x = r` \\ fs [] \\ rveq \\ metis_tac [lookup_delete])
  >- metis_tac []
  \\ Cases_on `x = r` \\ fs [lookup_delete] \\ metis_tac [lookup_delete]
QED

Theorem insert_delete_swap:
  ∀k v x r.
   wf r ∧ k ≠ x
   ⇒ (insert k v (delete x r) = delete x (insert k v r))
Proof
  rw []
  \\ `wf (insert k v (delete x r))` by rw [wf_insert,wf_delete]
  \\ `wf (delete x (insert k v r))` by rw [wf_insert,wf_delete]
  \\ drule spt_eq_thm \\ disch_then (qspec_then `insert k v (delete x r)` drule)
  \\ rw [] \\ rw [lookup_delete,lookup_insert]
QED

Theorem wf_size_of:
  ∀vs refs seen n' refs' seen'.
    wf refs ∧ (size_of vs refs seen = (n',refs',seen'))
    ⇒ wf refs'
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def] \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ every_case_tac \\ fs []
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  \\ fs [wf_delete]
QED

Triviality size_of_insert_aux:
  ∀vs refs seen p x n refs' seen'.
    wf refs                 ∧
    ¬live_ptr p vs refs     ∧
    (lookup p refs = NONE)  ∧
    (size_of vs refs seen = (n,refs',seen'))
    ⇒ (size_of vs (insert p x refs) seen = (n,insert p x refs',seen'))
Proof
  ho_match_mp_tac size_of_ind \\ rw [size_of_def]
  \\ rpt (pairarg_tac \\ fs []) \\ rveq
  >- (qpat_x_assum `¬ _` (assume_tac o ONCE_REWRITE_RULE [live_ptr_cons])
     \\ fs [] \\ first_x_assum drule
     \\ disch_then (qspec_then `x'` assume_tac) \\ rfs [] \\ rveq
     \\ `subspt refs1' refs` by
        (ho_match_mp_tac size_of_refs_subspt
        \\ asm_exists_tac \\ fs [])
     \\ drule wf_size_of \\ disch_then (drule_then assume_tac)
     \\ drule_then (qspec_then `[x]` (drule_then assume_tac)) not_live_ptr_subspt
     \\ first_x_assum (drule_then (drule_then (qspec_then `x'` mp_tac)))
     \\ impl_tac
     >- (CCONTR_TAC \\ fs []
        \\ Cases_on `lookup p refs1'`
        \\ fs [subspt_lookup]
        \\ first_x_assum drule \\ fs [])
     \\ rw [])
  >- (`p ≠ r` by fs [live_ptr_def,live_ptr_list_def]
     \\ fs [lookup_insert]
     \\ every_case_tac \\ fs [] \\ rveq
     >- (rpt (pairarg_tac \\ fs []) \\ rveq
        \\ drule live_ptr_ptr
        \\ disch_then (qspec_then `p` (fn t => fs [t]))
        \\ drule live_ptr_delete
        \\ disch_then (drule_then (qspec_then `l` (fn t => fs [t])))
        \\ drule_then (qspec_then `r` assume_tac) wf_delete
        \\ first_x_assum drule \\ disch_then drule \\ fs [lookup_delete]
        \\ disch_then (qspec_then `x` assume_tac) \\ fs []
        \\ qpat_x_assum `_ = (_,refs'',seen'')` mp_tac
        \\ qmatch_goalsub_abbrev_tac `size_of l refs1 seen`
        \\ qmatch_asmsub_abbrev_tac  `size_of l refs2 seen`
        \\ `refs1 = refs2` suffices_by fs []
        \\ UNABBREV_ALL_TAC \\ fs [insert_delete_swap])
     \\ fs [insert_delete_swap])
  \\ fs [live_ptr_def,live_ptr_list_def]
  \\ first_x_assum drule \\ disch_then drule \\ disch_then drule
  \\ disch_then (qspec_then `x` assume_tac) \\ fs [] \\ rfs []
QED

Theorem closed_ptrs_list_not_live_ptr_list:
  ∀p vs refs.
    closed_ptrs_list vs refs ∧
    (lookup p refs = NONE)
    ⇒ ¬live_ptr_list p vs
Proof
  ho_match_mp_tac live_ptr_list_ind\\ rw [closed_ptrs_list_def,live_ptr_list_def]
  \\ fs [IS_SOME_EXISTS]
  >- (CCONTR_TAC \\ fs [])
  \\ first_x_assum ho_match_mp_tac \\ metis_tac []
QED

Theorem closed_ptrs_not_live_ptr:
  ∀vs refs p.
    closed_ptrs vs refs ∧
    (lookup p refs = NONE)
    ⇒ ¬live_ptr p vs refs
Proof
  rw [closed_ptrs_def,live_ptr_def]
  >- (drule closed_ptrs_list_not_live_ptr_list \\ disch_then drule \\ fs [])
  \\ CCONTR_TAC \\ fs [closed_ptrs_refs_def]  \\ first_x_assum drule \\ strip_tac
  \\ drule closed_ptrs_list_not_live_ptr_list \\ disch_then drule \\ fs []
QED

Theorem size_of_insert:
  ∀vs refs seen p x n refs' seen'.
    wf refs                 ∧
    closed_ptrs vs refs     ∧
    (lookup p refs = NONE)  ∧
    (size_of vs refs seen = (n,refs',seen'))
    ⇒ (size_of vs (insert p x refs) seen = (n,insert p x refs',seen'))
Proof
  rw [] \\ ho_match_mp_tac size_of_insert_aux
  \\ fs [closed_ptrs_not_live_ptr]
QED

Theorem closed_ptrs_APPEND:
  ∀a b refs. closed_ptrs (a ++ b) refs = closed_ptrs a refs ∧ closed_ptrs b refs
Proof
  Induct
  >- (rw [closed_ptrs_def,closed_ptrs_list_def] \\ metis_tac [])
  \\ rw [] \\ ONCE_REWRITE_TAC [closed_ptrs_cons] \\ metis_tac []
QED

Theorem closed_ptrs_refs_insert:
  ∀refs p x y.
    closed_ptrs_refs refs ∧
    (lookup p refs = NONE)
    ⇒ closed_ptrs_refs (insert p (ByteArray x y) refs)
Proof
  rw [closed_ptrs_refs_def]
  \\ Cases_on `x' = p` \\ fs [lookup_insert]
  \\ first_x_assum drule
  \\ pop_assum kall_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ Q.SPEC_TAC (`refs`,`refs`)
  \\ Q.SPEC_TAC (`l`,`l`)
  \\ ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_list_def]
  \\ metis_tac [IS_SOME_EXISTS,lookup_insert]
QED

Theorem closed_ptrs_insert:
  ∀vs refs p x.
  closed_ptrs vs refs
  ∧ (lookup p refs = NONE)
  ∧ closed_ptrs_refs (insert p x refs)
  ⇒ closed_ptrs vs (insert p x refs)
Proof
  ho_match_mp_tac closed_ptrs_list_ind
  \\ rw [closed_ptrs_def]
  \\ fs [closed_ptrs_list_def]
  \\ metis_tac [lookup_insert,IS_SOME_EXISTS]
QED

Theorem IMP_is_safe_for_space_alt:
  backend_config_ok c ∧
  (compile c prog = SOME (code,data,conf)) ∧
  (to_data c prog = (c0,data_prog)) ∧
  data_lang_safe_for_space ffi (fromAList data_prog)
    (compute_limits c.data_conf.len_size (is_64_bits c) heap_stack_limit)
    conf.word_conf.stack_frame_size InitGlobals_location ⇒
  is_safe_for_space ffi c prog heap_stack_limit
Proof
 rw [IMP_is_safe_for_space]
QED

val _ = export_theory();
