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
  < b is NONE,
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
      if any_el (Num c) dml (b-1w) > b
      then
        all_assigned_list dml b v i1
      else F
End

Definition dm_rel_def:
  dm_rel dm dml (b:word8) ⇔
  b < 255w ∧
  ∀n.
    (FLOOKUP dm n = NONE ⇔ (any_el n dml (b-1w) < b)) ∧
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
  Cases_on`x`>>gvs[]
  >- (
    `b+1w > b` by FULL_BBLAST_TAC>>
    simp[])>>
  FULL_BBLAST_TAC
QED

Definition delete_literals_sing_list_def:
  (delete_literals_sing_list dml b v i =
  if i = 0 then SOME (T,dml)
  else
    let i1 = i - 1 in
    let c = sub v i1 in
    if c < 0
    then
      let nc = Num (-c) in
      let bb = any_el nc dml (b-1w) in
      (if bb < b
      then
        (if all_assigned_list dml b v i1
          then SOME (F,
            update_resize dml (b-1w) (b+1w) nc)
          else NONE)
      else if bb = b
      then
        delete_literals_sing_list dml b v i1
      else NONE)
    else
      let nc = Num c in
      let bb = any_el nc dml (b-1w) in
      (if bb < b
      then
        (if all_assigned_list dml b v i1
          then SOME (F,
            update_resize dml (b-1w) b nc)
          else NONE)
      else if bb > b
      then
        delete_literals_sing_list dml b v i1
      else NONE))
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

(* TODO: can give more information in NONE case, *)
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
    ntac 2 strip_tac>>
    TOP_CASE_TAC>>gvs[]
    >-
      (irule dm_rel_update_resize>>simp[])>>
    Cases_on`x`>>gvs[]>>
    FULL_BBLAST_TAC)>>
  DEP_REWRITE_TAC[all_assigned_list]>>simp[]>>
  qpat_assum`dm_rel _ _ _` mp_tac>>
  PURE_REWRITE_TAC[Once dm_rel_def]>>
  ntac 2 strip_tac>>
  TOP_CASE_TAC>>gvs[]
  >-
    (irule dm_rel_update_resize>>simp[])>>
  Cases_on`x`>>gvs[AllCaseEqs()]>>
  FULL_BBLAST_TAC
QED


