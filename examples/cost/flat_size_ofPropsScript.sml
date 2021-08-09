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

Theorem sum_img_add:
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

Theorem sum_image_subset:
  ∀x y f.
    FINITE y ∧ x ⊆ y ⇒
    sum_img f x ≤ sum_img f y
Proof
  rw[sum_img_def]
  \\ qmatch_goalsub_abbrev_tac ‘ITSET _ _ n’
  \\ pop_assum kall_tac
  \\ ntac 2 (pop_assum mp_tac)
  \\ MAP_EVERY qid_spec_tac [‘n’,‘y’]
  \\ qmatch_goalsub_abbrev_tac ‘ITSET ff _ _’
  \\ qspec_then ‘ff’ assume_tac (GEN_ALL ITSET_ind)
  \\ pop_assum ho_match_mp_tac
  \\ UNABBREV_ALL_TAC \\ rw[] \\ gs[]
  \\ Cases_on ‘y = ∅’ \\ gs[]
  \\ drule_all SUBSET_FINITE_I
  \\ strip_tac
  \\ Cases_on ‘x ⊆ REST y’
  >- (gs[sum_img_add] \\ cheat)
  \\ cheat
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
  \\ cheat
QED

val _ = export_theory();
