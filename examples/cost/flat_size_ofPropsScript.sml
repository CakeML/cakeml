(*
  Lemmas about flat_size_of
*)

open preamble dataSemTheory dataPropsTheory;

val _ = new_theory "flat_size_ofProps";

Theorem flat_size_of_head_simps[simp]:
  (∀vs lims refs blocks n.
     flat_size_of lims refs blocks (Number n::vs) =
     flat_measure lims [Number n] + flat_size_of lims refs blocks vs)
  ∧ (∀vs lims refs blocks ptr.
     flat_size_of lims refs blocks (CodePtr ptr::vs) =
     flat_measure lims [CodePtr ptr] + flat_size_of lims refs blocks vs)
  ∧ (∀vs lims refs blocks w.
     flat_size_of lims refs blocks (Word64 w::vs) =
     flat_measure lims [Word64 w] + flat_size_of lims refs blocks vs)
Proof
  rw[flat_size_of_def,to_roots_def,flat_size_of_def]
  \\ Cases_on ‘vs’ \\ rw[flat_measure_def]
QED

Theorem flat_measure_cons:
  ∀x xs lims.
    flat_measure lims (x::xs) = flat_measure lims [x] + flat_measure lims xs
Proof
  rw[] \\ Cases_on ‘x’ \\ Cases_on ‘xs’ \\ rw[flat_measure_def]
QED

Triviality ITSET_add:
  ∀f x n m.
    FINITE x ⇒
    ITSET (λa b. (b:num) + f a) x (n + m) =
     ITSET (λa b. (b:num) + f a) x n + m
Proof
  rpt (strip_tac)
  \\ pop_assum mp_tac
  \\ MAP_EVERY qid_spec_tac [‘n’,‘x’]
  \\ qmatch_goalsub_abbrev_tac ‘ITSET ff _ _’
  \\ qspec_then ‘ff’ assume_tac (GEN_ALL ITSET_ind)
  \\ pop_assum ho_match_mp_tac
  \\ UNABBREV_ALL_TAC \\ rw[] \\ gs[]
  \\ Cases_on ‘x = ∅’ \\ gs[]
  >- simp[ITSET_THM]
  \\ pop_assum (fn t => qmatch_asmsub_abbrev_tac ‘a2 = b2’ \\ assume_tac t)
  \\ qmatch_goalsub_abbrev_tac ‘a1 = b1’
  \\ ‘a1 = a2 ∧ b1 = b2’ suffices_by simp[]
  \\ qpat_x_assum ‘a2 = b2’ kall_tac
  \\ UNABBREV_ALL_TAC \\ rw[]
  \\ simp[Once ITSET_THM]
QED

Triviality ITSET_REST_le:
  ∀x n f.
    FINITE x ∧ x ≠ ∅ ⇒
    ITSET (λa b. (b:num) + f a) (REST x) n ≤ ITSET (λa b. (b:num) + f a) x n
Proof
  rw[]
  \\ qmatch_goalsub_abbrev_tac ‘aa ≤ _’
  \\ simp[Once ITSET_THM,ITSET_add]
QED

Theorem sum_img_REST_le:
  ∀f x.
    FINITE x ∧ x ≠ ∅ ⇒
    sum_img f (REST x) ≤ sum_img f x
Proof
    rw[sum_img_def,ITSET_REST_le]
QED

Triviality ITSET_insert_le:
  ∀f n s x.
    FINITE s ⇒
    ITSET (λa b. (b:num) + f a) s n ≤ ITSET (λa b. (b:num) + f a) (x INSERT s) n
Proof
  rw[]
  \\ qmatch_goalsub_abbrev_tac ‘ITSET ff _ _’
  \\ Cases_on ‘x ∈ s’ \\ simp[ABSORPTION_RWT]
  \\ qspecl_then [‘ff’,‘s’] mp_tac COMMUTING_ITSET_INSERT
  \\ impl_tac >- simp[Abbr‘ff’]
  \\ simp[DELETE_NON_ELEMENT_RWT,Abbr‘ff’,ITSET_add]
QED

Triviality ITSET_insert_add:
  ∀f n s x.
    FINITE s ∧ x ∉ s ⇒
    ITSET (λa b. (b:num) + f a) (x INSERT s) n = ITSET (λa b. (b:num) + f a) s n + f x
Proof
  rw[]
  \\ qmatch_goalsub_abbrev_tac ‘ITSET ff _ _’
  \\ qspecl_then [‘ff’,‘s’] mp_tac COMMUTING_ITSET_INSERT
  \\ impl_tac >- simp[Abbr‘ff’]
  \\ simp[DELETE_NON_ELEMENT_RWT,Abbr‘ff’,ITSET_add]
QED

Triviality ITSET_union_le:
  ∀f n x y.
    FINITE x ∧ FINITE y ⇒
    ITSET (λa b. (b:num) + f a) x n ≤ ITSET (λa b. (b:num) + f a) (x ∪ y) n
Proof
  rw[]
  \\ ntac 2 (pop_assum mp_tac)
  \\ MAP_EVERY qid_spec_tac [‘y’,‘n’,‘x’]
  \\ qmatch_goalsub_abbrev_tac ‘ITSET ff _ _’
  \\ qspec_then ‘ff’ assume_tac (GEN_ALL ITSET_ind)
  \\ pop_assum ho_match_mp_tac
  \\ UNABBREV_ALL_TAC \\ rw[] \\ gs[]
  \\ drule_then assume_tac FINITE_REST
  \\ Cases_on ‘x = ∅’ \\ gs[]
  >- (simp[Once ITSET_THM,Once ITSET_THM]
      \\ IF_CASES_TAC \\ simp[]
      \\ qmatch_goalsub_abbrev_tac ‘ITSET ff _ _’
      \\ ONCE_ASM_REWRITE_TAC [ADD_SYM]
      \\ qunabbrev_tac ‘ff’
      \\ simp[FINITE_REST,ITSET_add])
  \\ qmatch_goalsub_abbrev_tac ‘ _ ≤ b2’
  \\ simp[Once ITSET_THM]
  \\ qunabbrev_tac ‘b2’
  \\ irule LESS_EQ_TRANS
  \\ first_x_assum (irule_at Any)
  \\ Cases_on ‘CHOICE x ∈ y’
  >- (qexists_tac ‘y DELETE CHOICE x’
      \\ simp[FINITE_DELETE]
      \\ ‘x ∪ y = CHOICE x INSERT ((REST x) ∪ (y DELETE CHOICE x))’ by
        (rw [FUN_EQ_THM,IN_DEF] \\ EQ_TAC \\ rw[] \\ metis_tac [IN_DEF])
      \\ pop_assum (ONCE_ASM_REWRITE_TAC o single)
      \\ qmatch_goalsub_abbrev_tac ‘a ≤ ITSET _ (_ INSERT ss) _’
      \\ qspecl_then [‘f’,‘n’,‘ss’,‘CHOICE x’] mp_tac ITSET_insert_add
      \\ impl_tac >- simp[Abbr‘ss’,FINITE_REST,FINITE_DELETE,CHOICE_NOT_IN_REST]
      \\ disch_then (REWRITE_TAC o single)
      \\ simp[Abbr‘a’,Abbr‘ss’,ITSET_add])
  \\ qexists_tac ‘y’ \\ simp[]
  \\ qmatch_goalsub_abbrev_tac ‘a ≤ _’
  \\ ‘x = CHOICE x INSERT REST x’ by rw[GSYM CHOICE_INSERT_REST]
  \\ pop_assum (ONCE_REWRITE_TAC o single)
  \\ simp[INSERT_UNION_EQ]
  \\ qmatch_goalsub_abbrev_tac ‘a ≤ ITSET _ (_ INSERT ss) _’
  \\ qspecl_then [‘f’,‘n’,‘ss’,‘CHOICE x’] mp_tac ITSET_insert_add
  \\ impl_tac >- simp[Abbr‘ss’,FINITE_REST,CHOICE_NOT_IN_REST]
  \\ disch_then (REWRITE_TAC o single)
  \\ simp[Abbr‘a’,Abbr‘ss’,ITSET_add]
QED

Theorem sum_img_subset:
  ∀x y f.
    FINITE y ∧ x ⊆ y ⇒
    sum_img f x ≤ sum_img f y
Proof
  rw[sum_img_def]
  \\ ‘FINITE x’ by metis_tac [SUBSET_FINITE]
  \\ gs[SUBSET_UNION_ABSORPTION]
  \\ qpat_x_assum ‘_ = _’ (ONCE_REWRITE_TAC o single o GSYM)
  \\ irule ITSET_union_le
  \\ simp[]
QED

Definition ref_to_vs_def:
  ref_to_vs [] = []
∧ ref_to_vs (ValueArray vs::xs) = vs ++ ref_to_vs xs
∧ ref_to_vs (ByteArray _ _::xs) = ref_to_vs xs
End

Definition blocks_to_vs_def:
  blocks_to_vs [] = []
∧ blocks_to_vs (Block _ _ l::xs) = l ++ blocks_to_vs xs
∧ blocks_to_vs (x::xs) = blocks_to_vs xs
End

Theorem FINITE_to_roots:
  ∀l. FINITE (to_roots l)
Proof
  Induct \\ rw[to_roots_def]
  \\ Cases_on ‘h’
  \\ rw[to_roots_def]
QED

(* Any block within a block must also be in all_blocks *)
Definition all_blocks_ok_def:
  all_blocks_ok blocks =
    ∀ts ts' tag tag' l l'.
      MEM (Block ts tag l) blocks ∧
      MEM (Block ts' tag' l') l
      ⇒ MEM (Block ts' tag' l') blocks
End

Theorem to_roots_APPEND:
  ∀a b. to_roots (a ++ b) = to_roots a ∪ to_roots b
Proof
  Induct \\ rw[to_roots_def]
  \\ Cases_on ‘h’ \\ rw[to_roots_def,UNION_ASSOC]
QED

(* Note: This might be tricky as it will relay on well-formedness properties
         of references  and blocks which should not have circular pointers/timestamps
 *)
Theorem FINITE_reachable_v:
  ∀refs blocks roots.
    FINITE roots ⇒
    FINITE (reachable_v refs blocks roots)
Proof
  rw[]
  \\ qspec_then ‘to_roots (blocks_to_vs blocks) ∪
                 to_roots (ref_to_vs (sptree$toList refs))  ∪
                 roots’
                mp_tac SUBSET_FINITE
  \\ impl_tac >- rw[FINITE_to_roots]
  \\ disch_then ho_match_mp_tac
  \\ rw [SUBSET_DEF,IN_DEF,reachable_v_def]
  \\ gs[Once RTC_CASES2]
  \\ Cases_on ‘u’
  >- (gs[next_def,block_to_roots_def]
      \\ Cases_on ‘LLOOKUP blocks n’ \\ gs []
      \\ Cases_on ‘x''’ \\ gs [LLOOKUP_EQ_EL]
      \\ drule EL_MEM
      \\ qpat_x_assum ‘Blocks _ _ _ = _’ (REWRITE_TAC o single o GSYM)
      \\ rw[] \\ DISJ1_TAC \\ DISJ1_TAC
      \\ gs[IN_DEF] \\ pop_assum mp_tac
      \\ qpat_x_assum ‘to_roots _ _’ mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp[AND_IMP_INTRO]
      \\ induct_on ‘blocks’
      \\ rw[]
      >- (simp[blocks_to_vs_def,to_roots_APPEND,IN_DEF])
      \\ first_x_assum drule_all \\ rw[]
      \\ Cases_on ‘h’ \\ rw[]
      \\ rw[blocks_to_vs_def,to_roots_def,to_roots_APPEND,IN_DEF])
  >-(gs[next_def,ptr_to_roots_def]
     \\ Cases_on ‘lookup n refs’ \\ gs[]
     \\ Cases_on ‘x''’ \\ gs[]
     \\ ‘MEM (ValueArray l) (toList refs)’ by metis_tac[MEM_toList]
     \\ DISJ1_TAC \\ DISJ2_TAC
     \\ pop_assum mp_tac \\ qpat_x_assum ‘x ∈ _’ mp_tac
     \\ rpt (pop_assum kall_tac)
     \\ qmatch_goalsub_abbrev_tac ‘MEM _ ll’
     \\ pop_assum kall_tac \\ simp[AND_IMP_INTRO]
     \\ induct_on ‘ll’
     \\ rw[]
     >- (simp[ref_to_vs_def,to_roots_APPEND])
     \\ first_x_assum drule_all \\ rw[]
     \\ Cases_on ‘h’ \\ rw[]
     \\ rw[ref_to_vs_def,to_roots_def,to_roots_APPEND,IN_DEF])
QED

Theorem flat_size_of_le_APPEND:
  ∀lims refs blocks a b.
       flat_size_of lims refs blocks b ≤ flat_size_of lims refs blocks (a ++ b)
Proof
  rw[flat_size_of_def]
  \\ qmatch_goalsub_abbrev_tac ‘a1 + a2 ≤ b1 + b2’
  \\ ‘a1 ≤ b1’ by
    (simp[Abbr‘a1’,Abbr‘b1’]
     \\ ntac 2 (pop_assum kall_tac)
     \\ induct_on ‘a’ \\ rw[]
     \\ Cases_on ‘h’ \\ simp [flat_measure_def]
     \\ simp[Once flat_measure_cons])
  \\ ‘a2 ≤ b2’ suffices_by simp[]
  \\ UNABBREV_ALL_TAC
  \\ irule sum_img_subset
  \\ simp[FINITE_to_roots,FINITE_reachable_v,SUBSET_DEF,to_roots_APPEND]
  \\ rw[IN_DEF,reachable_v_def]
  \\ metis_tac[]
QED

val _ = export_theory();
