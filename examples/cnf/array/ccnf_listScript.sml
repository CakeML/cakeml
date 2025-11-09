(*
  This refines the CCNF functions to a fixed-size, list-based implementation.
*)
Theory ccnf_list
Ancestors
  ccnf
Libs
  preamble basis blastLib

Theorem any_el_update_resize:
  any_el y (update_resize ls def v x) def =
  if y = x then v
  else
    any_el y ls def
Proof
  simp[update_resize_def]>>
  IF_CASES_TAC
  >- (
    simp[any_el_ALT,EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[any_el_ALT,EL_LUPDATE,EL_APPEND_EQN,REPLICATE]>>
  IF_CASES_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  simp[EL_REPLICATE]
QED

(* We use a scheme where
  <+ b is NONE,
  b is SOME F,
  b+1 is SOME T *)

Definition all_assigned_list_def:
  all_assigned_list dml (b:word8) v (i:num) =
  if i = 0 then T
  else
    let i1 = i - 1 in
    let c = sub v i1 in
    if c < 0
    then
      if any_el (Num (-c)) dml (b-1w) = b
      then
        all_assigned_list dml b v i1
      else
        F
    else
      if b <+ any_el (Num c) dml (b-1w)
      then
        all_assigned_list dml b v i1
      else F
End

Definition dm_rel_def:
  dm_rel dm dml (b:word8) ⇔
  0w <+ b ∧ b <+ 255w ∧
  ∀n.
    (FLOOKUP dm n = NONE ⇔ (any_el n dml (b-1w) <+ b)) ∧
    (FLOOKUP dm n = SOME F ⇔ any_el n dml (b-1w) = b) ∧
    (FLOOKUP dm n = SOME T ⇔ any_el n dml (b-1w) = b+1w)
End

Theorem all_assigned_list:
  ∀dml b v i dm.
  dm_rel dm dml b ⇒
  (all_assigned_list dml b v i =
  all_assigned_vec dm v i)
Proof
  ho_match_mp_tac all_assigned_list_ind>>
  rw[]>>
  simp[Once all_assigned_list_def,Once all_assigned_vec_def]>>
  Cases_on`i = 0`>>fs[]>>
  IF_CASES_TAC>>fs[dm_rel_def]
  >- (
    TOP_CASE_TAC>>gvs[]
    >- (rw[]>>gvs[])>>
    Cases_on`x`>>gvs[])>>
  TOP_CASE_TAC>>gvs[]
  >- FULL_BBLAST_TAC>>
  Cases_on`x`>>gvs[]>>
  `b <+ b+1w` by FULL_BBLAST_TAC>>
  simp[]
QED

Definition delete_literals_sing_list_def:
  delete_literals_sing_list dml b v i =
  if i = 0 then SOME (T,dml)
  else
    let i1 = i - 1 in
    let c = sub v i1 in
    if c < 0
    then
      let nc = Num (-c) in
      if any_el nc dml (b-1w) = b
      then
        delete_literals_sing_list dml b v i1
      else
        (if all_assigned_list dml b v i1
          then SOME (F,
            update_resize dml (b-1w) (b+1w) nc)
          else NONE)
    else
      let nc = Num c in
      if b <+ any_el nc dml (b-1w)
      then
        delete_literals_sing_list dml b v i1
      else
        (if all_assigned_list dml b v i1
          then SOME (F,
            update_resize dml (b-1w) b nc)
          else NONE)
End

Theorem dm_rel_update_resize:
  dm_rel dm dml b ∧
  bbb = (if bb then b+1w else b) ∧
  b1 = b-1w ⇒
  dm_rel (dm |+ (n,bb))
    (update_resize dml b1 bbb n) b
Proof
  rw[dm_rel_def,any_el_update_resize,FLOOKUP_UPDATE]>>
  rw[]>>
  FULL_BBLAST_TAC
QED

Theorem delete_literals_sing_list:
  ∀dml b v i dm res dml'.
  dm_rel dm dml b ∧
  delete_literals_sing_list dml b v i = SOME (res,dml') ⇒
  ∃dm'.
    delete_literals_sing_vec dm v i = SOME (res,dm') ∧
    dm_rel dm' dml' b
Proof
  ho_match_mp_tac delete_literals_sing_list_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once delete_literals_sing_list_def,Once delete_literals_sing_vec_def]>>
  IF_CASES_TAC>>simp[]
  >-
    metis_tac[]>>
  IF_CASES_TAC>>simp[]
  >- (
    DEP_REWRITE_TAC[all_assigned_list]>>simp[]>>
    qpat_assum`dm_rel _ _ _` mp_tac>>
    PURE_REWRITE_TAC[Once dm_rel_def]>>
    strip_tac>>
    IF_CASES_TAC
    >- (
      gvs[]>>every_case_tac>>gvs[]>>
      FULL_BBLAST_TAC)>>
    IF_CASES_TAC>>rw[]>>
    gvs[]>>every_case_tac>>gvs[]>>
    irule dm_rel_update_resize>>simp[])>>
  DEP_REWRITE_TAC[all_assigned_list]>>simp[]>>
  qpat_assum`dm_rel _ _ _` mp_tac>>
  PURE_REWRITE_TAC[Once dm_rel_def]>>
  strip_tac>>
  IF_CASES_TAC
  >- (
    gvs[]>>every_case_tac>>gvs[]>>
    FULL_BBLAST_TAC)>>
  IF_CASES_TAC>>rw[]>>
  gvs[]>>every_case_tac>>gvs[]
  >- (irule dm_rel_update_resize>>simp[])
  >- FULL_BBLAST_TAC
  >- (irule dm_rel_update_resize>>simp[])
QED

(* Ensures that the dml is of sufficient size
  and properly reset *)
Definition reset_dm_list_def:
  reset_dm_list dml b sz =
  if LENGTH dml < sz then
    (REPLICATE (2 * sz) 0w, 1w)
  else
    if b <+ 253w
    then (dml,b+2w)
    else (REPLICATE (LENGTH dml) 0w, 1w)
End

Theorem dm_rel_FEMPTY_REPLICATE:
  dm_rel FEMPTY (REPLICATE n 0w) 1w
Proof
  pure_rewrite_tac[dm_rel_def]>>
  rw[any_el_ALT,EL_REPLICATE]
QED

Theorem dm_rel_imp_any_el:
  dm_rel dm dml b ∧ b <+ 253w ⇒
  any_el n dml (b-1w) <+ b+2w
Proof
  rw[dm_rel_def]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  Cases_on`FLOOKUP dm n`>>gvs[]>>
  FULL_BBLAST_TAC
QED

Theorem dm_rel_reset_dm_list:
  dm_rel dm dml b ∧
  reset_dm_list dml b sz = (dml',b') ⇒
  dm_rel FEMPTY dml' b' ∧ sz ≤ LENGTH dml'
Proof
  rw[reset_dm_list_def]>>
  fs[LENGTH_REPLICATE,dm_rel_FEMPTY_REPLICATE]>>
  drule dm_rel_imp_any_el>>
  fs[dm_rel_def]>>rw[]
  >- FULL_BBLAST_TAC
  >- FULL_BBLAST_TAC>>
  pop_assum (qspec_then`n` assume_tac)>>
  fs[any_el_ALT]>>rw[]>>gvs[]>>
  FULL_BBLAST_TAC
QED

