(*
  The stamped assignment map of the checkers, as a list of nums: an entry
  below the stamp b is unassigned, b is false and b+1 is true.
*)
Theory ccnf_dm
Ancestors
  misc
Libs
  preamble

Definition dm_rel_def:
  dm_rel dm dml (b:num) ⇔
  0 < b ∧
  ∀n.
    (FLOOKUP dm n = NONE ⇔ (any_el n dml 0 < b)) ∧
    (FLOOKUP dm n = SOME F ⇔ any_el n dml 0 = b) ∧
    (FLOOKUP dm n = SOME T ⇔ any_el n dml 0 = b+1)
End

(* Ensures that the dml is of sufficient size.
  Advancing the stamp by 2 makes every existing entry read as unassigned.
  The map is cleared once the stamp reaches 2 ** 29, so that stamps and map
  entries stay below 2 ** 30. *)
Definition reset_dm_list_def:
  reset_dm_list dml (b:num) sz =
  if LENGTH dml < sz then
    (REPLICATE (2 * sz) (0:num), 1)
  else if 2 ** 29 ≤ b then
    (REPLICATE (LENGTH dml) 0, 1)
  else
    (dml,b+2)
End

(* The stamp bound kept by every map operation *)
Definition stamps_ok_def:
  stamps_ok dml (b:num) ⇔
  b ≤ 2 ** 29 + 1 ∧ EVERY (λx. x ≤ b + 1) dml
End

Theorem stamps_ok_REPLICATE[simp]:
  stamps_ok (REPLICATE n 0) 1
Proof
  rw[stamps_ok_def,EVERY_REPLICATE]
QED

Theorem stamps_ok_reset_dm_list:
  stamps_ok dml b ∧
  reset_dm_list dml b sz = (dml',b') ⇒
  stamps_ok dml' b'
Proof
  rw[reset_dm_list_def]>>
  gvs[stamps_ok_def,EVERY_MEM]>>
  rw[]>>
  first_x_assum drule>>
  simp[]
QED

Theorem stamps_ok_update_resize:
  stamps_ok dml b ∧ x ≤ b + 1 ⇒
  stamps_ok (update_resize dml 0 x n) b
Proof
  rw[stamps_ok_def,update_resize_def]>>
  irule IMP_EVERY_LUPDATE>>
  simp[EVERY_REPLICATE]
QED

Theorem stamps_ok_LUPDATE:
  stamps_ok dml b ∧ x ≤ b + 1 ⇒
  stamps_ok (LUPDATE x n dml) b
Proof
  rw[stamps_ok_def]>>
  irule IMP_EVERY_LUPDATE>>
  simp[]
QED

Theorem stamps_ok_bounds:
  stamps_ok dml b ⇒
  b + 2 < 2 ** 30 ∧ ∀n. n < LENGTH dml ⇒ EL n dml < 2 ** 30
Proof
  rw[stamps_ok_def,EVERY_EL]>>
  first_x_assum drule>>
  simp[]
QED

(* The stamp just below the bound advances; the one above clears the map *)
Theorem reset_dm_list_stamp_bound[local]:
  reset_dm_list [0;0] (2 ** 29 - 1) 1 = ([0;0], 2 ** 29 + 1) ∧
  reset_dm_list [3;0] (2 ** 29 + 1) 1 = ([0;0], 1)
Proof
  EVAL_TAC
QED

Theorem dm_rel_FEMPTY_REPLICATE:
  dm_rel FEMPTY (REPLICATE n 0) 1
Proof
  pure_rewrite_tac[dm_rel_def]>>
  rw[any_el_ALT,EL_REPLICATE]
QED

Theorem dm_rel_imp_any_el:
  dm_rel dm dml b ⇒
  any_el n dml 0 < b+2
Proof
  rw[dm_rel_def]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  Cases_on`FLOOKUP dm n`>>gvs[]
QED

Theorem dm_rel_reset_dm_list:
  dm_rel dm dml b ∧
  reset_dm_list dml b sz = (dml',b') ⇒
  dm_rel FEMPTY dml' b' ∧ sz ≤ LENGTH dml'
Proof
  rw[reset_dm_list_def]>>
  fs[LENGTH_REPLICATE,dm_rel_FEMPTY_REPLICATE]>>
  drule dm_rel_imp_any_el>>
  rw[dm_rel_def]>>
  qpat_x_assum`∀n. _`(qspec_then`n` assume_tac)>>
  decide_tac
QED

Theorem reset_dm_list_LENGTH:
  reset_dm_list dml b sz = (dml',b') ⇒
  LENGTH dml ≤ LENGTH dml' ∧ sz ≤ LENGTH dml'
Proof
  rw[reset_dm_list_def]>>
  simp[LENGTH_REPLICATE]
QED
