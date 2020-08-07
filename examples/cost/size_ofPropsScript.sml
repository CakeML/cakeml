(*
  Lemmas about size_of
*)

open preamble dataSemTheory dataPropsTheory;

val _ = new_theory "size_ofProps";

Definition sane_timestamps_def:
  sane_timestamps l =
  ∀ts tag bl tag' bl'.
    MEM (Block ts tag bl) l ∧ MEM (Block ts tag' bl') l ⇒
    tag = tag' ∧ bl = bl'
End

Definition all_blocks_def[simp]:
  (all_blocks [] = []) ∧
  (all_blocks (Block ts tag bl :: ys) =
   Block ts tag bl :: all_blocks bl ++ all_blocks ys) ∧
  (all_blocks (_ :: ys) = all_blocks ys)
Termination
  WF_REL_TAC ‘measure v1_size’
End

Theorem size_of_cons:
  size_of lims (x::xs) refs seen =
    let (n1,refs1,seen1) = size_of lims xs refs seen in
    let (n2,refs2,seen2) = size_of lims [x] refs1 seen1 in
       (n1 + n2,refs2,seen2)
Proof
  Cases_on ‘xs’ \\ fs [size_of_def] \\ fs [UNCURRY]
QED

Theorem size_of_append:
  ∀lims xs ys refs seen.
    size_of lims (xs++ys) refs seen =
      let (n1,refs1,seen1) = size_of lims ys refs seen in
      let (n2,refs2,seen2) = size_of lims xs refs1 seen1 in
         (n1 + n2,refs2,seen2)
Proof
  Induct_on ‘xs’ \\ fs []
  THEN1 (fs [size_of_def] \\ fs [UNCURRY])
  \\ once_rewrite_tac [size_of_cons] \\ fs [UNCURRY]
QED

Theorem size_of_refs_shirnk:
  size_of lims ts refs seen = (n,refs1,seen1) ∧ refs ≠ refs1 ⇒
  size refs1 < size refs
Proof
  cheat
QED

Theorem size_of_seen_pres:
  size_of lims ys refs seen1 = (q0,q1,seen2) ∧
  IS_SOME (lookup x1 seen1) ⇒
  IS_SOME (lookup x1 seen2)
Proof
  cheat
QED

Theorem size_of_seen_ignored:
  size_of lims ys refs seen1 = (q0,q1,seen2) ∧
  lookup x1 seen1 = NONE ∧
  lookup x1 seen2 = NONE ⇒
  size_of lims ys refs (insert x1 () seen1) = (q0,q1,insert x1 () seen2)
Proof
  cheat
QED

(* TODO: the refs also need have sane_timestamps, but that can wait until later *)
Theorem size_of_swap:
  ∀lims refs xs ys zs seen.
    sane_timestamps (all_blocks xs ++ all_blocks ys ++ all_blocks zs) ⇒
    size_of lims (xs ++ ys ++ zs) refs seen =
    size_of lims (ys ++ xs ++ zs) refs seen
Proof
  gen_tac \\ gen_tac
  \\ completeInduct_on ‘size refs’
  \\ fs [PULL_FORALL]
  \\ completeInduct_on ‘v1_size (xs ++ ys ++ zs)’
  \\ fs [PULL_FORALL]
  \\ rw [] \\ fs [AND_IMP_INTRO]
  \\ Cases_on ‘xs’ \\ fs []
  \\ match_mp_tac EQ_TRANS
  \\ qexists_tac ‘size_of lims (h::(ys ++ t ++ zs)) refs seen’
  \\ conj_tac
  THEN1
   (qsuff_tac ‘size_of lims (t ++ ys ++ zs) refs seen =
               size_of lims (ys ++ t ++ zs) refs seen’
    THEN1
     (once_rewrite_tac [size_of_cons]
      \\ fs [size_of_def,UNCURRY]
      \\ metis_tac [PAIR,PAIR_EQ])
    \\ first_x_assum match_mp_tac
    \\ fs [v_size_def]
    \\ fs [sane_timestamps_def,all_blocks_def]
    \\ rpt gen_tac
    \\ disch_then assume_tac
    \\ first_x_assum match_mp_tac
    \\ qexists_tac ‘ts’
    \\ Cases_on ‘h’ \\ fs [])
  \\ qsuff_tac
     ‘size_of lims (h::ys ++ (t ++ zs)) refs seen =
      size_of lims (ys ++ [h] ++ (t ++ zs)) refs seen’
  THEN1 (fs [] \\ rewrite_tac [APPEND,GSYM APPEND_ASSOC])
  \\ qabbrev_tac ‘ts = (t ++ zs)’
  \\ qabbrev_tac ‘xs2 = ys ++ [h]’
  \\ simp [size_of_append]
  \\ ‘∃q. size_of lims ts refs seen = q’ by fs []
  \\ PairCases_on ‘q’ \\ fs []
  \\ AP_TERM_TAC \\ fs [Abbr‘xs2’]
  \\ rename [‘size_of lims ts refs seen = (n,refs1,seen1)’]
  \\ drule size_of_refs_shirnk
  \\ Cases_on ‘refs ≠ refs1’ \\ fs []
  THEN1
   (rw [] \\ last_x_assum drule
    \\ disch_then (qspecl_then [‘[h]’,‘ys’,‘[]’] mp_tac) \\ fs []
    \\ disch_then match_mp_tac
    \\ fs [sane_timestamps_def]
    \\ rpt gen_tac
    \\ disch_then assume_tac
    \\ first_x_assum match_mp_tac
    \\ qexists_tac ‘ts'’
    \\ Cases_on ‘h’ \\ fs [] \\ metis_tac []) \\ fs []
  \\ var_eq_tac
  \\ qsuff_tac ‘size_of lims ([h] ++ ys) refs seen1 =
                size_of lims (ys ++ [h]) refs seen1’
  THEN1 fs []
  \\ Cases_on ‘h’
  \\ TRY (rename [‘Block x1 x2 x3’] \\ Cases_on ‘x3’)
  \\ TRY (rewrite_tac [size_of_append] \\ simp [size_of_def] \\ NO_TAC)

  (* only non-empty Block and RefPtr cases left *)
  THEN1
   (rewrite_tac [size_of_append] \\ simp [size_of_def]
    \\ Cases_on ‘IS_SOME (lookup x1 seen1)’ \\ fs []
    THEN1
     (‘∃q. size_of lims ys refs seen1 = q’ by fs []
      \\ PairCases_on ‘q’ \\ fs []
      \\ imp_res_tac size_of_seen_pres \\ fs [])
    \\ ‘∃q. size_of lims ys refs seen1 = q’ by fs []
    \\ PairCases_on ‘q’ \\ fs []
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
     (drule size_of_seen_ignored
      \\ disch_then drule \\ fs []
      \\ cheat (* confusing but probably follows from IH *))
    \\ qsuff_tac ‘size_of lims ys refs seen1 =
       size_of lims (ys ++ [Block x1 x2 (h::t')]) refs seen1’
    THEN1
     (fs [] \\ disch_then kall_tac
      \\ simp [Once size_of_append]
      \\ fs [size_of_def])

    \\ cheat (* could the IH save the day here?! *))

  \\ cheat
QED

val _ = export_theory();
