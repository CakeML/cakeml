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


(* Note: This might be tricky as it will relay on well-formedness properties
         of references  and blocks which should not have circular pointers/timestamps
 *)
Theorem FINITE_reachable_v:
  ∀refs blocks roots.
  FINITE roots ⇒
  FINITE (reachable_v refs blocks roots)
Proof
  cheat
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
QED

val _ = export_theory();
