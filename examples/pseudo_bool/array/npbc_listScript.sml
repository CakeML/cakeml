(*
  Refine PB proof checker to use arrays
*)
open preamble basis npbc_checkTheory;

val _ = new_theory "npbc_list"

Theorem any_el_update_resize:
  any_el n (update_resize fml def v id) def =
  if n = id then v else any_el n fml def
Proof
  rw[update_resize_def,any_el_ALT,EL_LUPDATE]>>fs[]>>
  fs[EL_APPEND_EQN,EL_REPLICATE]>>
  every_case_tac>>fs[]
QED

Definition lookup_core_only_list_def:
  lookup_core_only_list b fml n =
  case any_el n fml NONE of
    NONE => NONE
  | SOME (x,b') =>
    if ¬b ∨ b' then SOME x
    else NONE
End

(* TODO: optimize this using arrays instead of lists
  alternative:
    collapse all adds into one big list before normalizing
*)
Definition check_cutting_list_def:
  (check_cutting_list b (fml: (npbc # bool) option list) (Id n) =
    lookup_core_only_list b fml n) ∧
  (check_cutting_list b fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting_list b fml c1) (check_cutting_list b fml c2)) ∧
  (check_cutting_list b fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting_list b fml c)) ∧
  (check_cutting_list b fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_cutting_list b fml c)
    else NONE) ∧
  (check_cutting_list b fml (Sat c) =
    OPTION_MAP saturate (check_cutting_list b fml c)) ∧
  (check_cutting_list b fml (Lit l) =
    case l of
      Pos v => SOME ([(1,v)],0)
    | Neg v => SOME ([(-1,v)],0)) ∧
  (check_cutting_list b fml (Triv ls) = SOME (clean_triv ls)) ∧
  (check_cutting_list b fml (Weak c var) =
    OPTION_MAP (λc. weaken_sorted c var) (check_cutting_list b fml c))
End

(* Copied from LPR *)
Definition delete_list_def:
  delete_list i fml =
  if LENGTH fml ≤ i then fml
  else LUPDATE NONE i fml
End

Definition list_delete_list_def:
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    list_delete_list is (delete_list i fml))
End

(* Rollback a formula to starting ID
  NOTE: design decision
  - this always frees up constraints to be collected by the GC
*)
Definition rollback_def:
  rollback fml id_start id_end =
  list_delete_list
    (MAP ($+id_start) (COUNT_LIST (id_end-id_start))) fml
End

(* ensure list remains ≥ sorted -- common case: will always just insert at the front *)
Definition sorted_insert_def:
  (sorted_insert (x:num) [] = [x]) ∧
  (sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys
    else y::(sorted_insert x ys))
End

Definition check_contradiction_fml_list_def:
  check_contradiction_fml_list b fml n =
  case lookup_core_only_list b fml n of
    NONE => F
  | SOME c =>
    check_contradiction c
End

Definition opt_update_def[simp]:
  (opt_update fml NONE id = (fml,id)) ∧
  (opt_update fml (SOME cc) id = (update_resize fml NONE (SOME cc) id,id+1))
End

Definition rup_pass1_list_def:
  rup_pass1_list (assg:word8 list) [] acc ys m = (acc,ys,m) ∧
  rup_pass1_list assg ((i:int,n:num)::xs) acc ys m =
    let k = Num (ABS i) in
      if ~(n < LENGTH assg) ∨ EL n assg = 0w then
        rup_pass1_list assg xs (acc + k) ((k,i,n)::ys) (MAX m n)
      else if EL n assg = 1w  then
        rup_pass1_list assg xs (if i < 0 then acc else acc + k) ys m
      else
        rup_pass1_list assg xs (if i < 0 then acc + k else acc) ys m
End

Definition rup_pass2_list_def:
  rup_pass2_list (assg:word8 list) max [] l changes =
    (changes,assg,T) ∧
  rup_pass2_list assg max ((k:num,i:int,n:num)::ys) l changes =
    if max < l + k then
      let pre1 = (n < LENGTH assg) in
      let assg1 = LUPDATE (if 0 ≤ i then 1w else 2w) n assg in
      let (changes2,assg2,pre2) = rup_pass2_list assg1 max ys l (n::changes) in
        (changes2,assg2,pre1 ∧ pre2)
    else
      rup_pass2_list assg max ys l changes
End

Definition resize_to_fit_def:
   resize_to_fit n (bytes:word8 list) =
     if n < LENGTH bytes then bytes else
       bytes ++ REPLICATE (2 * LENGTH bytes + n + 1) 0w
End

Definition update_assg_list_def:
  update_assg_list assg (ls,n) =
    let (max,ls1,m) = rup_pass1_list assg ls 0 [] 0 in
    let assg1 = resize_to_fit m assg in
      rup_pass2_list assg1 max ls1 n []
End

Definition get_rup_constraint_list_def:
  get_rup_constraint_list b fml n nc =
  if n = 0 then SOME nc
  else
    lookup_core_only_list b fml n
End

Definition check_rup_loop_list_def:
  check_rup_loop_list b nc fml assg all_changes [] =
    (F,assg,all_changes,T) ∧
  check_rup_loop_list b nc fml assg all_changes (n::ns) =
    case get_rup_constraint_list b fml n nc of
    | NONE => (F,assg,all_changes,T)
    | SOME c =>
        if NULL ns then
          let (max,ls1,m) = rup_pass1_list assg (FST c) 0 [] 0 in
            (max < SND c,assg,all_changes,T)
        else
          let (new_changes,assg,pre) = update_assg_list assg c in
          let all_changes = new_changes ++ all_changes in
          let (res,assg,all_changes,pre1) =
                check_rup_loop_list b nc fml assg all_changes ns
          in (res,assg,all_changes,pre ∧ pre1)
End

Definition delete_each_def:
  delete_each [] assg = (assg:word8 list,T) ∧
  delete_each (n::ns) assg =
    let pre1 = (n < LENGTH assg) in
    let assg1 = LUPDATE 0w n assg in
    let (assg2,pre2) = delete_each ns assg1 in
      (assg2,pre1 ∧ pre2)
End

Definition check_rup_list_def:
  check_rup_list b nc fml zeros ls =
    let (res,assg1,all_changes1,pre1) =
      check_rup_loop_list b nc fml zeros [] ls in
    let (zeros2,pre2) = delete_each all_changes1 assg1 in
      (res,zeros2,pre1 ∧ pre2)
End

Definition check_lstep_list_def:
  (check_lstep_list lstep
    b (fml: (npbc # bool) option list)
    (mindel:num) (id:num) zeros =
  case lstep of
  | Delete ls =>
      if EVERY (λid. mindel ≤ id ∧
          lookup_core_only_list T fml id = NONE) ls then
        SOME(list_delete_list ls fml, NONE, id, zeros)
      else
        NONE
  | Cutting constr =>
    (case check_cutting_list b fml (to_triv constr) of
      NONE => NONE
    | SOME c =>
      SOME (fml, SOME(c,b), id, zeros))
  | Rup c ls =>
    let (res,zeros,_) =
      check_rup_list b (not c) fml zeros ls in
    (if res then
         SOME(
           fml,
           SOME(c,b),
           id,
           zeros)
     else NONE)
  | Con c pf n =>
    let (fml_not_c,id') =
      opt_update fml (SOME (not c,b)) id in
    (case check_lsteps_list pf b fml_not_c id id' zeros of
      SOME (fml',id',zeros) =>
      if check_contradiction_fml_list b fml' n then
        let rfml = rollback fml' id id' in
        SOME(
          rfml,
          SOME(c,b),
          id',
          zeros)
      else NONE
    | _ => NONE)
  | Check n c =>
    (case lookup_core_only_list b fml n of
      NONE => NONE
    | SOME c' =>
      if c = c' then SOME(fml, NONE, id, zeros)
      else NONE)
  | NoOp => SOME (fml, NONE, id, zeros)) ∧
  (check_lsteps_list [] b fml mindel id zeros =
    SOME (fml, id, zeros)) ∧
  (check_lsteps_list (step::steps) b fml mindel id zeros =
    case check_lstep_list step b fml mindel id zeros of
      SOME (fml',c,id',zeros) =>
        let (fml'',id'') = opt_update fml' c id' in
          check_lsteps_list steps b fml'' mindel id'' zeros
    | NONE => NONE)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST))’
End

(* id numbers are monotone increasing *)
Theorem opt_update_id:
  opt_update fmlls c id = (fmlls',id') ⇒
  id ≤ id'
Proof
  Cases_on`c`>>rw[]
QED

Theorem check_lstep_list_id:
  (∀step b fmlls mindel id zeros fmlls' id' zeros' c.
  check_lstep_list step b fmlls mindel id zeros =
    SOME (fmlls',c,id',zeros') ⇒
    id ≤ id') ∧
  (∀steps b fmlls mindel id zeros fmlls' id' zeros'.
  check_lsteps_list steps b fmlls mindel id zeros =
    SOME (fmlls',id',zeros') ⇒
    id ≤ id')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[] >> gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def] >>
  rpt (pairarg_tac >> gvs [])
QED

Theorem any_el_list_delete_list:
  ∀ls n fml.
  any_el n (list_delete_list ls fml) NONE =
  if MEM n ls then NONE else any_el n fml NONE
Proof
  Induct>>rw[list_delete_list_def,delete_list_def]>>
  gs[any_el_ALT,EL_LUPDATE]
QED

Theorem opt_update_id_upper:
  opt_update fmlls c id = (fmlls',id') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)
Proof
  Cases_on`c`>>rw[]>>
  simp[any_el_update_resize]
QED

(* id numbers bound those in the formula *)
Theorem check_lstep_list_id_upper:
  (∀step b fmlls mindel id zeros fmlls' id' zeros' c.
  check_lstep_list step b fmlls mindel id zeros =
    SOME (fmlls',c,id',zeros') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀steps b fmlls mindel id zeros fmlls' id' zeros'.
  check_lsteps_list steps b fmlls mindel id zeros =
    SOME (fmlls',id',zeros') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE))
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >-
      simp[any_el_list_delete_list]
    >- (rpt (pairarg_tac \\ gvs []))
    >- (
      fs[any_el_update_resize,rollback_def,any_el_list_delete_list]>>
      last_x_assum (qspec_then`n` mp_tac)>>simp[]>>rw[]>>
      gvs[MEM_MAP,MEM_COUNT_LIST]>>
      drule (CONJUNCT2 check_lstep_list_id)>>
      rw[]>>
      Cases_on`n ≥ id'` >> gvs[]>>
      `F` by intLib.ARITH_TAC))
  >- gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
  >- (
    qpat_x_assum`_= SOME _ `mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    pairarg_tac>>fs[]>>
    rw[]>>
    last_x_assum mp_tac>>
    impl_tac>- (
      match_mp_tac (GEN_ALL opt_update_id_upper)>>
      first_x_assum (irule_at Any)>>
      drule (CONJUNCT1 check_lstep_list_id)>>
      rw[])>>
    simp[]
    )
QED

Theorem opt_update_mindel:
  opt_update fmlls c id = (fmlls',id') ∧
  n < id ⇒
  any_el n fmlls NONE = any_el n fmlls' NONE
Proof
  Cases_on`c`>>rw[]>>
  simp[any_el_update_resize]
QED

(* ids below mindel are unchanged *)
Theorem check_lstep_list_mindel:
  (∀step b fmlls mindel id zeros fmlls' res n.
    check_lstep_list step b fmlls mindel id zeros =
      SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒
      any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps b fmlls mindel id zeros fmlls' res n.
    check_lsteps_list steps b fmlls mindel id zeros =
      SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒
      any_el n fmlls NONE = any_el n fmlls' NONE)
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >- (
      rw[any_el_list_delete_list]>>fs[EVERY_MEM]>>
      first_x_assum drule>>fs[])
    >- (
      rpt (pairarg_tac \\ gvs [])>>
      simp[rollback_def,any_el_list_delete_list,MEM_MAP]>>
      simp[any_el_update_resize])
    >- (
      first_x_assum(qspec_then`n`mp_tac)>>
      simp[any_el_update_resize]>>
      drule (el 2 (CONJUNCTS check_lstep_list_id))>>
      simp[rollback_def,any_el_list_delete_list,MEM_MAP]))
  >- fs[check_lstep_list_def]
  >- (
    qpat_x_assum`_=SOME _` mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    first_x_assum drule>>
    pairarg_tac>>gvs[AllCaseEqs()]>>
    drule (el 1 (CONJUNCTS check_lstep_list_id))>>
    drule opt_update_id>>simp[]>>
    drule opt_update_mindel>>
    rw[]
    )
QED

(* ids below id are only deleted *)
Theorem check_lstep_list_id_del:
  (∀step b fmlls mindel id zeros fmlls' res n.
    check_lstep_list step b fmlls mindel id zeros =
      SOME (fmlls', res) ∧
    n < id ∧
    IS_SOME (any_el n fmlls' NONE) ⇒
    any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps b fmlls mindel id zeros fmlls' res n.
    check_lsteps_list steps b fmlls mindel id zeros =
      SOME (fmlls', res) ∧
    n < id ∧
    IS_SOME (any_el n fmlls' NONE) ⇒
    any_el n fmlls NONE = any_el n fmlls' NONE)
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >- (
      fs[any_el_list_delete_list]>>fs[EVERY_MEM]>>
      every_case_tac>>fs[])
    >- (
      rpt (pairarg_tac \\ gvs []) >>
      fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,
         IS_SOME_EXISTS] >>
      gvs [any_el_update_resize])
    >- (
      first_x_assum(qspec_then`n`mp_tac)>>
      fs[any_el_update_resize]>>
      drule (el 2 (CONJUNCTS check_lstep_list_id))>>
      fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,IS_SOME_EXISTS]))
  >- fs[check_lstep_list_def]
  >- (
    qpat_x_assum`_=SOME _` mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    first_x_assum drule>>
    pairarg_tac>>gvs[AllCaseEqs()]>>
    drule (el 1 (CONJUNCTS check_lstep_list_id))>>
    drule opt_update_id>>simp[]>>
    drule opt_update_mindel>>
    rw[] )
QED

(* Relation between
  sptree representation fml and list representation fmlls
  If we allow "fmlls" to be lazy, then this relation needs
  to also be parameterized by x ∈ set inds
*)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x. any_el x fmlls NONE = lookup x fml
End

Theorem fml_rel_lookup_core_only:
  fml_rel fml fmlls ⇒
  lookup_core_only_list b fmlls n =
  lookup_core_only b fml n
Proof
  rw[fml_rel_def,lookup_core_only_def,lookup_core_only_list_def]
QED

Theorem fml_rel_check_cutting:
  ∀p.
  fml_rel fml fmlls ⇒
  check_cutting_list b fmlls p = check_cutting b fml p
Proof
  Induct>>rw[check_cutting_list_def,check_cutting_def]
  >-
    metis_tac[fml_rel_lookup_core_only]>>
  every_case_tac>>simp[check_cutting_def]
QED

Theorem fml_rel_rollback:
  fml_rel fml fmlls ∧
  (∀n. n < id ∨ n ≥ id' ⇒ any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE)
  ⇒
  fml_rel fml (rollback fmlls' id id')
Proof
  rw[fml_rel_def,rollback_def]>>
  simp[any_el_list_delete_list]>>
  rw[MEM_MAP]>>
  fs[MEM_COUNT_LIST]
  >- (
    `id + y ≥ id` by fs[]>>
    metis_tac[])
  >- (
    `x < id ∨ x ≥ id'` by intLib.ARITH_TAC>>
    metis_tac[])
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert id c fml) (update_resize fmlls NONE (SOME c) id)
Proof
  rw[fml_rel_def,lookup_insert,any_el_update_resize]
QED

Theorem fml_rel_list_delete_list:
  ∀ls fml fmlls.
  fml_rel fml fmlls ⇒
  fml_rel (FOLDL (λa b. delete b a) fml ls) (list_delete_list ls fmlls)
Proof
  Induct>>rw[list_delete_list_def,delete_list_def]>>
  first_x_assum match_mp_tac
  >- (
    fs[fml_rel_def]>>
    rw[lookup_delete]>>
    first_x_assum(qspec_then`h` assume_tac)>>fs[any_el_ALT]>>
    gs[])>>
  fs[fml_rel_def]>>
  rw[lookup_delete]>>
  fs[any_el_ALT,EL_LUPDATE]
QED

Theorem fml_rel_check_contradiction_fml:
  fml_rel fml fmlls ∧
  check_contradiction_fml_list b fmlls n ⇒
  check_contradiction_fml b fml n
Proof
  rw[check_contradiction_fml_list_def,check_contradiction_fml_def]>>
  every_case_tac>>gvs[]>>
  metis_tac[option_CLAUSES,fml_rel_lookup_core_only]
QED

Triviality rup_pass1_list_pre:
  ∀assg xs n ys m n1 ys1 m1.
    rup_pass1_list assg xs n ys m = (n1,ys1,m1) ∧
    EVERY (λ(_,_,k). k ≤ m) ys ⇒
    EVERY (λ(_,_,k). k ≤ m1) ys1
Proof
  Induct_on ‘xs’ \\ gvs [rup_pass1_list_def,FORALL_PROD]
  \\ rw [] \\ res_tac \\ gvs []
  \\ gvs [EVERY_MEM,FORALL_PROD]
  \\ metis_tac []
QED

Triviality rup_pass2_list_pre:
  ∀assg m xs l changes res changes1 assg1 pre.
    rup_pass2_list assg m xs l changes = (changes1,assg1,pre) ∧
    EVERY (λi. i < LENGTH assg) changes ∧
    EVERY (λ(_,_,k). k < LENGTH assg) xs
    ⇒
    pre ∧ LENGTH assg1 = LENGTH assg ∧ set changes ⊆ set changes1 ∧
    EVERY (λi. i < LENGTH assg1) changes1 ∧
    ∀n. n < LENGTH assg1 ∧ EL n assg ≠ EL n assg1 ⇒ MEM n changes1
Proof
  Induct_on ‘xs’ \\ gvs [rup_pass2_list_def,FORALL_PROD]
  \\ rpt gen_tac
  \\ reverse IF_CASES_TAC \\ strip_tac >- metis_tac []
  \\ pairarg_tac \\ gvs []
  \\ first_x_assum drule
  \\ impl_tac >- gvs []
  \\ strip_tac \\ gvs []
  \\ gvs [EL_LUPDATE]
  \\ metis_tac []
QED

Triviality update_assg_list_pre:
  ∀assg x changes assg1 pre.
    update_assg_list assg x = (changes,assg1,pre) ⇒
    pre ∧ EVERY (λi. i < LENGTH assg1) changes ∧
    LENGTH assg ≤ LENGTH assg1 ∧
    ∀n. n < LENGTH assg1 ∧ EL n assg1 ≠ 0w ⇒
        MEM n changes ∨ n < LENGTH assg ∧ EL n assg = EL n assg1
Proof
  rpt gen_tac \\ PairCases_on ‘x’
  \\ gvs [update_assg_list_def]
  \\ pairarg_tac \\ gvs [] \\ strip_tac
  \\ drule rup_pass1_list_pre \\ gvs [] \\ strip_tac
  \\ drule rup_pass2_list_pre \\ fs []
  \\ impl_tac >-
   (pop_assum mp_tac
    \\ match_mp_tac MONO_EVERY \\ gvs [FORALL_PROD]
    \\ rw [resize_to_fit_def])
  \\ strip_tac \\ gvs []
  \\ conj_tac
  >- rw [resize_to_fit_def]
  \\ rw []
  \\ Cases_on ‘MEM n changes’ \\ gvs []
  \\ first_x_assum drule \\ strip_tac \\ gvs []
  \\ gvs [resize_to_fit_def]
  \\ Cases_on ‘m < LENGTH assg’ \\ gvs []
  \\ Cases_on ‘n < LENGTH assg’ \\ gvs []
  \\ gvs [EL_APPEND1,EL_APPEND2]
  \\ gvs [EL_REPLICATE]
QED

Triviality check_rup_loop_list_pre:
  ∀b nc fmlls assg changes ls res assg1 changes1 pre.
    check_rup_loop_list b nc fmlls assg changes ls =
      (res,assg1,changes1,pre) ∧
    EVERY (λi. i < LENGTH assg) changes ∧
    (∀n. n < LENGTH assg ∧ EL n assg ≠ 0w ⇒ MEM n changes)
    ⇒
    pre ∧ EVERY (λi. i < LENGTH assg1) changes1 ∧
    LENGTH assg ≤ LENGTH assg1 ∧
    (∀n. n < LENGTH assg1 ∧ EL n assg1 ≠ 0w ⇒ MEM n changes1)
Proof
  Induct_on ‘ls’ \\ gvs [check_rup_loop_list_def]
  \\ rpt gen_tac \\ TOP_CASE_TAC \\ gvs []
  >- (strip_tac \\ gvs [])
  \\ IF_CASES_TAC
  >- (pairarg_tac \\ gvs [] \\ strip_tac \\ gvs [])
  \\ pairarg_tac \\ gvs []
  \\ strip_tac
  \\ drule update_assg_list_pre \\ strip_tac
  \\ qabbrev_tac ‘all_changes = new_changes ++ changes’
  \\ ‘EVERY (λi. i < LENGTH assg') all_changes ∧
      ∀n. n < LENGTH assg' ∧ EL n assg' ≠ 0w ⇒ MEM n all_changes’ by
   (simp [Abbr‘all_changes’] \\ conj_tac
    >-
     (qpat_x_assum ‘EVERY _ changes’ mp_tac
      \\ match_mp_tac MONO_EVERY \\ simp_tac std_ss []
      \\ fs [])
    \\ metis_tac [])
  \\ pairarg_tac \\ gvs []
  \\ last_x_assum drule
  \\ impl_tac >- gvs []
  \\ strip_tac \\ gvs []
QED

Triviality delete_each_pre:
  ∀changes assg zeros pre.
    delete_each changes assg = (zeros,pre) ∧
    EVERY (λi. i < LENGTH assg) changes ∧
    (∀n. n < LENGTH assg ∧ EL n assg ≠ 0w ⇒ MEM n changes) ⇒
    pre ∧ EVERY (λw. w = 0w) zeros
Proof
  Induct \\ gvs [delete_each_def]
  >- (gvs [EVERY_EL] \\ metis_tac [])
  \\ rpt gen_tac \\ strip_tac \\ rpt (pairarg_tac \\ gvs [])
  \\ last_x_assum drule \\ disch_then irule
  \\ gvs [EL_LUPDATE] \\ rw [] \\ res_tac \\ gvs []
QED

Theorem check_rup_list_pre:
  check_rup_list b nc fmlls zeros ls = (res,zeros',pre) ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  pre ∧ EVERY (λw. w = 0w) zeros'
Proof
  gvs [check_rup_list_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule check_rup_loop_list_pre \\ fs []
  \\ ntac 2 strip_tac \\ gvs []
  \\ qpat_x_assum ‘_ ⇒ _’ mp_tac
  \\ impl_tac >- (gvs [EVERY_EL] \\ metis_tac [])
  \\ strip_tac \\ gvs []
  \\ drule_all delete_each_pre \\ fs []
QED

Definition get_assg_def:
  get_assg i xs =
    if i < LENGTH xs ∧ EL i xs ≠ (0w:word8) then SOME (EL i xs) else NONE
End

Triviality get_assg_resize_to_fit[simp]:
  get_assg i (resize_to_fit m assg) = get_assg i assg
Proof
  rw [resize_to_fit_def] \\ gvs [get_assg_def]
  \\ Cases_on ‘i < LENGTH assg’ \\ gvs [EL_APPEND1,EL_APPEND2]
  \\ CCONTR_TAC \\ gvs [EL_REPLICATE]
QED

Triviality to_get_assg:
  ~(p < LENGTH assg) ∨ EL p assg = 0w ⇔ get_assg p assg = NONE
Proof
  gvs [get_assg_def] \\ metis_tac []
QED

Theorem rup_pass1_list_invs:
  ∀xs n ys m nA1 nB1 lsA lsB mA mB.
    rup_pass1_list assgA xs n ys m = (nA1,lsA,mA) ∧
    rup_pass1_list assgB xs n ys m = (nB1,lsB,mB) ∧
    (∀i. get_assg i assgA = get_assg i assgB) ⇒
    nA1 = nB1 ∧ lsA = lsB ∧ mA = mB
Proof
  Induct_on ‘xs’ \\ gvs [rup_pass1_list_def,FORALL_PROD,to_get_assg]
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ Cases_on ‘get_assg p_2 assgB = NONE’ \\ gvs []
  >- (res_tac \\ gvs [])
  \\ ‘EL p_2 assgA = 1w ⇔ get_assg p_2 assgA = SOME 1w’ by
    (first_x_assum $ qspec_then ‘p_2’ assume_tac
    \\ gvs [get_assg_def])
  \\ ‘EL p_2 assgB = 1w ⇔ get_assg p_2 assgB = SOME 1w’ by
    (first_x_assum $ qspec_then ‘p_2’ assume_tac
    \\ gvs [get_assg_def])
  \\ gvs []
  \\ Cases_on ‘get_assg p_2 assgB = SOME 1w’ \\ gvs []
  \\ res_tac \\ gvs []
QED

Theorem rup_pass2_list_invs:
  ∀assgA assgB m ls1 x1 acc new_changesA assgA1 preA
   new_changesB assgB1 preB.
    rup_pass2_list assgA m ls1 x1 acc = (new_changesA,assgA1,preA) ∧
    rup_pass2_list assgB m ls1 x1 acc = (new_changesB,assgB1,preB) ∧
    EVERY (λ(_,_,k). k < LENGTH assgB) ls1 ∧
    EVERY (λ(_,_,k). k < LENGTH assgA) ls1 ∧
    (∀i. get_assg i assgA = get_assg i assgB) ⇒
    new_changesA = new_changesB ∧
    (∀i. get_assg i assgA1 = get_assg i assgB1)
Proof
  Induct_on ‘ls1’ \\ gvs [rup_pass2_list_def,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ reverse $ Cases_on ‘m < p_1 + x1’ \\ gvs []
  >- (last_x_assum $ dxrule_then dxrule \\ fs [])
  \\ rpt (pairarg_tac \\ gvs [])
  \\ last_x_assum $ dxrule_then dxrule \\ fs []
  \\ reverse impl_tac >- (strip_tac \\ gvs [])
  \\ gvs [get_assg_def,EL_LUPDATE] \\ gen_tac
  \\ Cases_on ‘i = p_2’ \\ gvs []
QED

Theorem update_assg_list_invs:
  ∀assgA assgB x new_changesA assgA1 preA new_changesB assgB1 preB.
    update_assg_list assgA x = (new_changesA,assgA1,preA) ∧
    update_assg_list assgB x = (new_changesB,assgB1,preB) ∧
    (∀i. get_assg i assgA = get_assg i assgB) ⇒
    (new_changesA) = (new_changesB) ∧
    (∀i. get_assg i assgA1 = get_assg i assgB1)
Proof
  rpt gen_tac \\ strip_tac \\ PairCases_on ‘x’
  \\ gvs [update_assg_list_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ imp_res_tac rup_pass1_list_pre \\ gvs []
  \\ dxrule_then dxrule rup_pass1_list_invs
  \\ impl_tac >- simp [] \\ strip_tac \\ gvs []
  \\ Cases_on ‘max' < x1’ \\ gvs []
  \\ dxrule_then dxrule rup_pass2_list_invs
  \\ reverse impl_tac >- (strip_tac \\ gvs [])
  \\ gvs []
  \\ gvs [EVERY_MEM,FORALL_PROD] \\ rw [] \\ res_tac
  \\ rw [resize_to_fit_def]
QED

Theorem check_rup_loop_list_invs:
  ∀b nc fmlls assgA assgB xs ls qA assgA1 changesA bA qB assgB1 changesB bB.
    check_rup_loop_list b nc fmlls assgA xs ls =
      (qA,assgA1,changesA,bA) ∧
    check_rup_loop_list b nc fmlls assgB xs ls =
      (qB,assgB1,changesB,bB) ∧
    (∀i. get_assg i assgA = get_assg i assgB) ⇒
    qA = qB
Proof
  Induct_on ‘ls’ \\ gvs [check_rup_loop_list_def]
  \\ rpt gen_tac \\ TOP_CASE_TAC \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac
  \\ dxrule_then dxrule update_assg_list_invs
  \\ impl_tac >- simp [] \\ strip_tac \\ gvs []
  \\ last_x_assum $ dxrule_then dxrule
  \\ impl_tac >- simp []
  \\ every_case_tac \\ gvs []
  \\ strip_tac \\ gvs []
  \\ dxrule_then dxrule rup_pass1_list_invs
  \\ impl_tac >- simp [] \\ strip_tac \\ gvs []
QED

Theorem check_rup_list_invs:
  check_rup_list b nc fmlls zeros ls = (res,zeros',pre) ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  pre ∧ EVERY (λw. w = 0w) zeros' ∧
  ∀zeros1.
    EVERY (λw. w = 0w) zeros1 ⇒
    ∃zeros2.
      check_rup_list b nc fmlls zeros1 ls = (res,zeros2,pre) ∧
             EVERY (λw. w = 0w) zeros2
Proof
  strip_tac \\ drule_all check_rup_list_pre \\ gs [] \\ rpt strip_tac
  \\ Cases_on ‘check_rup_list b nc fmlls zeros1 ls’ \\ Cases_on ‘r’ \\ gvs []
  \\ drule_all check_rup_list_pre \\ gs [] \\ strip_tac \\ gvs []
  \\ gvs [check_rup_list_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ dxrule_then dxrule check_rup_loop_list_invs \\ gvs []
  \\ impl_tac \\ gvs []
  \\ gvs [EVERY_EL,get_assg_def] \\ metis_tac []
QED

Definition assg_rel_def:
  assg_rel assg assgl ⇔
    (∀n. FLOOKUP assg n = NONE ⇔ get_assg n assgl = NONE) ∧
    (∀n. FLOOKUP assg n = SOME T ⇒ get_assg n assgl = SOME 1w) ∧
    (∀n. FLOOKUP assg n = SOME F ⇒ get_assg n assgl = SOME 2w)
End

Theorem rup_pass1_list_thm:
  ∀xs n ys m n1 ls1 m1 n2 ls2.
    rup_pass1_list assgl xs n ys m = (n1,ls1,m1) ∧
    rup_pass1 assg xs n ys = (n2,ls2) ∧
    assg_rel assg assgl ⇒
    n1 = n2 ∧ ls1 = ls2
Proof
  Induct_on ‘xs’
  \\ gvs [rup_pass1_list_def,rup_pass1_def,FORALL_PROD,to_get_assg]
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ gvs [assg_rel_def]
  \\ ntac 3 $ first_x_assum $ qspec_then ‘p_2’ assume_tac
  \\ Cases_on ‘FLOOKUP assg p_2’ \\ gvs []
  >- (last_x_assum drule_all \\ gvs [])
  \\ Cases_on ‘x’ \\ gvs [] \\ gvs [get_assg_def]
  \\ last_x_assum drule_all \\ gvs []
QED

Theorem rup_pass2_list_thm:
  ∀assg assgl m ls1 c1 ys ys1 assgl1.
    rup_pass2_list assgl m ls1 c1 ys = (ys1,assgl1,T) ∧
    assg_rel assg assgl ⇒
    case rup_pass2 assg m ls1 c1 of
    | NONE => F
    | SOME assg1 => assg_rel assg1 assgl1
Proof
  Induct_on ‘ls1’ \\ gvs [rup_pass2_list_def,FORALL_PROD,rup_pass2_def]
  \\ rpt gen_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ strip_tac
  \\ reverse IF_CASES_TAC \\ gvs []
  >- (last_x_assum $ drule_then drule \\ fs [])
  \\ last_x_assum $ drule
  \\ gvs [] \\ disch_then irule
  \\ gvs [assg_rel_def] \\ rw []
  \\ Cases_on ‘p_2 = n’ \\ gvs [FLOOKUP_UPDATE]
  \\ gvs [FLOOKUP_UPDATE,get_assg_def,EL_LUPDATE]
QED

Theorem fml_rel_get_rup_constraint:
  fml_rel fml fmlls ⇒
  get_rup_constraint_list b fmlls n nc =
  get_rup_constraint b fml n nc
Proof
  rw[get_rup_constraint_list_def,get_rup_constraint_def]>>
  metis_tac[fml_rel_lookup_core_only]
QED

Theorem check_rup_loop_list_thm:
  ∀b nc fmlls assgl cs ns cs1 assgl1 pre assg fml.
    check_rup_loop_list b nc fmlls assgl cs ns =
      (T,assgl1,cs1,T) ∧
    fml_rel fml fmlls ∧ assg_rel assg assgl ⇒
    check_rup b nc fml assg ns
Proof
  Induct_on ‘ns’
  \\ gvs [check_rup_loop_list_def,check_rup_def]
  \\ rpt gen_tac \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ drule_all fml_rel_get_rup_constraint
  \\ disch_then $ qspecl_then [`nc`,‘h’,‘b’] assume_tac
  \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ PairCases_on ‘c’
  \\ gvs [update_assg_list_def,update_assg_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_then drule rup_pass1_list_thm
  \\ (impl_tac >- simp [] \\ strip_tac \\ gvs [])
  \\ drule rup_pass2_list_thm \\ fs []
  \\ disch_then $ qspecl_then [‘assg’] mp_tac
  \\ (impl_tac >- gvs [assg_rel_def])
  \\ CASE_TAC \\ gvs []
  \\ rw [] \\ gvs []
  \\ metis_tac []
QED

Theorem check_rup_list_thm:
  check_rup_list b nc fmlls zeros ls = (T,zeros',c) ∧
  fml_rel fml fmlls ∧
  EVERY (λw. w = 0w) zeros ⇒
  check_rup b nc fml FEMPTY ls
Proof
  strip_tac
  \\ drule_all check_rup_list_pre \\ strip_tac \\ gvs []
  \\ gvs [check_rup_list_def]
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_then drule check_rup_loop_list_thm
  \\ disch_then irule
  \\ gvs [assg_rel_def,get_assg_def,EVERY_EL]
  \\ metis_tac []
QED

(* zeros preserved *)
Theorem check_lstep_list_zeros:
  (∀step b fmlls mindel id zeros fmlls' id' zeros' c.
  EVERY (λw. w = 0w) zeros ∧
  check_lstep_list step b fmlls mindel id zeros =
    SOME (fmlls',c,id',zeros') ⇒
    EVERY (λw. w = 0w) zeros') ∧
  (∀steps b fmlls mindel id zeros fmlls' id' zeros'.
  EVERY (λw. w = 0w) zeros ∧
  check_lsteps_list steps b fmlls mindel id zeros =
    SOME (fmlls',id',zeros') ⇒
    EVERY (λw. w = 0w) zeros')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [check_lstep_def,check_lstep_list_def,AllCaseEqs()] >>
    rpt (pairarg_tac >> gvs [])>>
    drule check_rup_list_pre>>
    simp[])
  >-
    gvs [check_lstep_list_def]>>
  pop_assum mp_tac>>
  simp[Once check_lstep_list_def,AllCaseEqs()]>>
  rw[]>>
  pairarg_tac>>gvs[]
QED

Theorem fml_rel_check_lstep_list:
  (∀lstep b fmlls mindel id zeros
    fmlls' id' zeros' fmlls'' id'' c fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    EVERY (λw. w = 0w) zeros ∧
    check_lstep_list lstep b fmlls mindel id zeros =
      SOME (fmlls',c,id',zeros') ∧
    opt_update fmlls' c id' = (fmlls'',id'') ⇒
    ∃fml'.
      check_lstep lstep b fml id = SOME (fml',id'') ∧
      fml_rel fml' fmlls'') ∧
  (∀lsteps b fmlls mindel id zeros fmlls' id' zeros' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    EVERY (λw. w = 0w) zeros ∧
    check_lsteps_list lsteps b fmlls mindel id zeros =
      SOME (fmlls',id',zeros') ⇒
    ∃fml'.
      check_lsteps lsteps b fml id = SOME (fml',id') ∧
      fml_rel fml' fmlls')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >- ( (* Deletion *)
      CONJ_TAC >- (
        fs[EVERY_MEM]>>
        metis_tac[fml_rel_lookup_core_only])>>
      metis_tac[fml_rel_list_delete_list])
    >- ((* Cutting *)
      drule fml_rel_check_cutting>>
      disch_then(qspecl_then[`b`,`to_triv constr`] assume_tac)>>
      fs[insert_fml_def]>>
      metis_tac[fml_rel_update_resize])
    >- ( (* Rup*)
      rpt (pairarg_tac \\ gvs [])>>
      gvs [insert_fml_def]>>
      conj_tac >- (
        drule_then drule check_rup_list_thm \\ fs []
      ) >>
      irule fml_rel_update_resize >>
      gvs[])
    >- ( (* Con *)
      rename1`insert_fml _ _ _ (not cc)`>>
      `fml_rel (insert id (not cc,b) fml)
        (update_resize fmlls NONE (SOME (not cc,b)) id)` by
        simp[fml_rel_update_resize]>>
      first_x_assum drule>>
      impl_tac>-
        simp[any_el_update_resize]>>
      strip_tac>>gvs[insert_fml_def]>>
      CONJ_TAC >-
        metis_tac[fml_rel_check_contradiction_fml]>>
      match_mp_tac fml_rel_update_resize>>
      match_mp_tac fml_rel_rollback>>fs[]>>
      rw[]
      >- (
        drule (el 2 (CONJUNCTS check_lstep_list_mindel))>>
        simp[any_el_update_resize])>>
      first_assum(qspec_then`n` mp_tac)>>
      drule (el 2 (CONJUNCTS check_lstep_list_id))>>
      simp[]>>rw[]>>
      drule (el 2 (CONJUNCTS check_lstep_list_id_upper))>>
      disch_then match_mp_tac>>
      simp[any_el_update_resize])
    >- (
      gvs[lookup_core_only_list_def,AllCaseEqs()]>>
      rw[]>>fs[fml_rel_def]>>
      metis_tac[SOME_11]))
  >- fs[check_lstep_list_def,check_lstep_def]
  >- (
    pop_assum mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    pairarg_tac>>gvs[]>>
    rw[]>>
    first_x_assum drule>>
    impl_tac >- (
      drule opt_update_id>>
      drule (hd (CONJUNCTS check_lstep_list_id))>>
      simp[any_el_update_resize]>>
      rw[]>>
      drule opt_update_id_upper>>
      drule (el 1 (CONJUNCTS check_lstep_list_id_upper))>>
      simp[]>>
      drule (el 1 (CONJUNCTS check_lstep_list_zeros))>>
      disch_then drule>>simp[]
      )>>
    strip_tac>>
    simp[Once check_lstep_def])
QED

(* Inline subst fun *)
Definition subst_subst_fun_def:
  subst_subst_fun s c = subst (subst_fun s) c
End

Definition extract_clauses_list_def:
  (extract_clauses_list s b fml rsubs [] acc =
    SOME (REVERSE acc)) ∧
  (extract_clauses_list s b fml rsubs (cpf::pfs) acc =
    case cpf of
      (NONE,pf) =>
      extract_clauses_list s b fml rsubs pfs ((NONE,pf)::acc)
    | (SOME (INL n,i),pf) =>
        (case lookup_core_only_list b fml n of
          NONE => NONE
        | SOME c =>
          extract_clauses_list s b fml rsubs pfs
            ((SOME ([not (subst_subst_fun s c)],i),pf)::acc))
    | (SOME (INR u,i),pf) =>
      if u < LENGTH rsubs then
        extract_clauses_list s b fml rsubs pfs
          ((SOME (EL u rsubs,i),pf)::acc)
      else NONE)
End

Definition extract_scopes_list_def:
  (extract_scopes_list scopes
    s b fml rsubs [] = SOME []) ∧
  (extract_scopes_list scopes
    s b fml rsubs ((sc,pfs)::rest) =
    case mk_scope scopes sc of NONE => NONE
    | SOME scs =>
    case extract_clauses_list s b fml rsubs pfs [] of
      NONE => NONE
    | SOME cpfs =>
      case extract_scopes_list scopes s b fml rsubs rest of
        NONE => NONE
      | SOME crest => SOME ((scs,cpfs)::crest))
End

Definition list_insert_fml_list_def:
  (list_insert_fml_list [] b id fml =
    (id,fml)) ∧
  (list_insert_fml_list (c::cs) b id fml =
    list_insert_fml_list cs b
      (id+1)
      (update_resize fml NONE (SOME (c,b)) id ))
End

Definition check_subproofs_list_def:
  (check_subproofs_list [] b fml mindel id zeros =
    SOME(fml,id,zeros)) ∧
  (check_subproofs_list ((cnopt,pf)::pfs) b fml
    mindel id zeros =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps_list pf b fml mindel id zeros of
        SOME (fml', id', zeros') =>
        check_subproofs_list pfs b fml' mindel id' zeros'
      | res => NONE)
    | SOME (cs,n) =>
      let (cid,cfml) =
        list_insert_fml_list cs b id fml in
      (* no deletions below id *)
      case check_lsteps_list pf b cfml id cid zeros of
        SOME (fml', id', zeros') =>
        if check_contradiction_fml_list b fml' n then
          let rfml = rollback fml' id id' in
            check_subproofs_list pfs b rfml mindel id' zeros'
        else NONE
      | _ => NONE)
End

Definition check_scopes_list_def:
  (check_scopes_list [] b fml mindel id zeros =
    SOME (fml,id,zeros)) ∧
  (check_scopes_list ((scopt,pf)::scpfs) b
    fml mindel id zeros =
    case scopt of
      NONE =>
        (case check_subproofs_list pf b fml mindel id zeros of
          NONE => NONE
        | SOME (fml',id',zeros') =>
            check_scopes_list scpfs b fml' mindel id' zeros')
    | SOME sc =>
    let (cid,cfml) = list_insert_fml_list sc b id fml in
    case check_subproofs_list pf b cfml id cid zeros of
      NONE => NONE
    | SOME (fml',id',zeros') =>
        let rfml = rollback fml' id id' in
        check_scopes_list scpfs b rfml mindel id' zeros')
End

(*
Definition reindex_aux_def:
  (reindex_aux b fml [] iacc vacc =
    (REVERSE iacc, vacc)) ∧
  (reindex_aux b fml (i::is) iacc vacc =
  case any_el i fml NONE of
    NONE => reindex_aux b fml is iacc vacc
  | SOME (v,b') =>
    let vacc' =
      if b ⇒ b' then v::vacc else vacc in
    reindex_aux b fml is (i::iacc) vacc')
End

(* Make inds non-lazy *)
Definition reindex_def:
  (reindex b fml is = reindex_aux b fml is [] [])
End
*)

Definition reindex_aux_def:
  (reindex_aux fml [] iacc = REVERSE iacc) ∧
  (reindex_aux fml (i::is) iacc =
  case any_el i fml NONE of
    NONE => reindex_aux fml is iacc
  | SOME (v,b') =>
    reindex_aux fml is (i::iacc))
End

Definition reindex_def:
  (reindex fml is = reindex_aux fml is [])
End

Definition revalue_aux_def:
  (revalue_aux b fml [] vacc = vacc) ∧
  (revalue_aux b fml (i::is) vacc =
  case any_el i fml NONE of
    NONE => revalue_aux b fml is vacc
  | SOME (v,b') =>
    let vacc' =
      if b ⇒ b' then v::vacc else vacc in
    revalue_aux b fml is vacc')
End

Definition revalue_def:
  (revalue b fml is = revalue_aux b fml is [])
End

(*
Definition reindex_partial_aux_def:
  (reindex_partial_aux b fml mini [] iacc vacc =
    (REVERSE iacc, vacc,[])) ∧
  (reindex_partial_aux b fml mini (i::is) iacc vacc =
  if i < mini then (REVERSE iacc, vacc, i::is)
  else
  case any_el i fml NONE of
    NONE => reindex_partial_aux b fml mini is iacc vacc
  | SOME (v,b') =>
    let vacc' =
      if b ⇒ b' then v::vacc else vacc in
    reindex_partial_aux b fml mini is (i::iacc) vacc')
End

Definition reindex_partial_def:
  reindex_partial b fml mini is =
  case mini of NONE => ([],[],is)
  | SOME mini =>
    reindex_partial_aux b fml mini is [] []
End
*)

Definition subst_opt_subst_fun_def:
  subst_opt_subst_fun s c = subst_opt (subst_fun s) c
End

Definition subst_indexes_def:
  (subst_indexes s b fml [] = []) ∧
  (subst_indexes s b fml (i::is) =
    case lookup_core_only_list b fml i of
      NONE => subst_indexes s b fml is
    | SOME res =>
      (case subst_opt_subst_fun s res of
        NONE => subst_indexes s b fml is
      | SOME c => (i,c)::subst_indexes s b fml is))
End

Definition h_base_def:
  h_base = 32768:num
End

Definition h_base_sq_def:
  h_base_sq = 1073741824:num
End

Definition h_mod_def:
  h_mod = 1000000009:num
End

(* Fixed size of the hash table *)
Definition splim_def:
  splim = 2000000:num
End

Definition hash_pair_def:
  hash_pair (i:int,n:num) =
  if i ≤ 0 then
    (2 * (Num(ABS i)) + h_base * n) MOD h_mod
  else
    (2 * (Num (ABS i)) - 1 + h_base * n) MOD h_mod
End

Definition hash_list_def:
  (hash_list [] = 0n) ∧
  (hash_list (x::xs) =
    (hash_pair x + h_base_sq * hash_list xs) MOD h_mod)
End

Definition hash_constraint_def:
  hash_constraint (c,n) =
  ((n + h_base * hash_list c) MOD h_mod) MOD splim
End

Definition mk_hashset_def:
  (mk_hashset [] acc = acc) ∧
  (mk_hashset (p::ps) acc =
  let h = hash_constraint p in
  mk_hashset ps (LUPDATE (p::EL h acc) h acc))
End

Definition in_hashset_def:
  in_hashset p hs =
  let h = hash_constraint p in
  mem_constraint p (EL h hs)
End

Theorem in_hashset_mk_hashset:
  ∀cs c acc.
  in_hashset c (mk_hashset cs acc) ⇒
  MEM c cs ∨ in_hashset c acc
Proof
  Induct>>rw[mk_hashset_def]>>
  first_x_assum drule>>
  rw[]>>simp[]>>
  fs[in_hashset_def,mem_constraint_thm,EL_LUPDATE]>>
  every_case_tac>>fs[]
QED

(* Fast path for a special case corresponding to pbc
   --- enables faster checked deletion
   No scoping and no proofgoals used *)
Definition red_fast_def:
  red_fast s idopt pfs = (
  if s = INR (Vector []) then
    case idopt of
      NONE => NONE
    | SOME id =>(
      case (pfs:scope) of
      | [(NONE,[(NONE,pf)])] => SOME (pf,id)
      | [] => SOME ([],id)
      | _ => NONE)
  else NONE)
End

(* inds is just passed through here *)
Definition check_red_list_fast_def:
  check_red_list_fast b fml inds id c pf cid vimap zeros =
  let nc = not c in
  let fml_not_c = update_resize fml NONE (SOME (nc,b)) id in
  case check_lsteps_list pf b fml_not_c id (id+1) zeros of
    NONE => NONE
  | SOME (fml', id',zeros') =>
  if check_contradiction_fml_list b fml' cid then
    let rfml = rollback fml' id id' in
      SOME (rfml,inds,vimap,id',zeros')
  else
    NONE
End

(* The fmlls argument should be delayed and avoided
  as much as possible *)
Definition split_goals_hash_def:
  split_goals_hash fmlls extra (proved:num_set)
    (goals:(num # (int # num) list # num) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). lookup i proved ≠ NONE) goals in
  let lf = FILTER (λc. ¬check_triv extra (not c)) (MAP SND lf) in
  let proved = MAP SND lp in
  let hs = mk_hashset fmlls (mk_hashset proved (REPLICATE splim [])) in
  EVERY (λc. in_hashset c hs) lf
End

(* Not meant to be executed, mainly just abbrevation... *)
Definition do_red_check_def:
  do_red_check idopt b tcb fml inds
    s rfml rinds extra pfs rsubs skipped cond =
  case idopt of NONE =>
    let goals = subst_indexes s (b ∨ tcb) rfml rinds in
    let (l,r) = extract_scoped_pids pfs LN LN in
    let fmlls = revalue (b ∨ tcb) rfml inds in
      cond ∧
      split_goals_hash fmlls extra l goals ∧
      EVERY (λ(id,cs).
        lookup id r ≠ NONE ∨
        check_hash_triv extra cs  ∨
        MEM id skipped
        )
        (enumerate 0 rsubs)
  | SOME cid =>
     check_contradiction_fml_list b fml cid
End

Definition add_listsLR_def:
  (add_listsL cx (xn:num) xs1 ys zs n =
    case ys of
    | [] => (REV zs ((cx,xn)::xs1),n)
    | (y::ys1) =>
      let (cy,yn) = y in
        if yn < xn then add_listsL cx xn xs1 ys1 (y::zs) n
        else
        if xn < yn then add_listsR cy yn xs1 ys1 ((cx,xn)::zs) n
        else
          let (zs1,n1) = add_terms cx cy xn zs n in
            add_listsLR xs1 ys1 zs1 n1) ∧
  (add_listsR cy yn xs ys1 zs n =
    case xs of
    | [] => (REV zs ((cy,yn)::ys1),n)
    | (x::xs1) =>
      let (cx,xn) = x in
        if xn < yn then add_listsR cy yn xs1 ys1 (x::zs) n
        else
        if yn < xn then add_listsL cx xn xs1 ys1 ((cy,yn)::zs) n
        else
          let (zs1,n1) = add_terms cx cy xn zs n in
            add_listsLR xs1 ys1 zs1 n1) ∧
  (add_listsLR xs ys zs n =
    case xs of
    | [] => (REV zs ys,n)
    | (x::xs1) =>
    case ys of
    | [] => (REV zs xs,n)
    | (y::ys1) =>
      let (cx,xn) = x in
      let (cy,yn) = y in
        if xn < yn then add_listsR cy yn xs1 ys1 (x::zs) n
        else
        if yn < xn then add_listsL cx xn xs1 ys1 (y::zs) n
        else
          let (zs1,n1) = add_terms cx cy xn zs n in
            add_listsLR xs1 ys1 zs1 n1)
Termination
  WF_REL_TAC `measure (λv.
    case v of
      INL (cx,xn,xs1,ys,zs,n) => LENGTH xs1 + LENGTH ys
    | INR v =>
      case v of
        INL (cy,yn,xs,ys1,zs,n) => LENGTH xs + LENGTH ys1
      | INR (xs,ys,zs,n) => LENGTH xs + LENGTH ys)`>>
  rw[]
End

Theorem add_listsLR_eq:
  (∀cx xn xs1 ys zs n.
  add_listsL cx xn xs1 ys zs n =
  add_lists' ((cx,xn)::xs1) ys zs n) ∧
  (∀cy yn xs ys1 zs n.
  add_listsR cy yn xs ys1 zs n =
  add_lists' xs ((cy,yn)::ys1) zs n) ∧
  (∀xs ys zs n.
  add_lists' xs ys zs n =
  add_listsLR xs ys zs n)
Proof
  ho_match_mp_tac add_listsLR_ind>>rw[]>>
  simp[Once npbcTheory.add_lists'_def,Once add_listsLR_def]>>
  every_case_tac>>simp[]>>
  rpt(pairarg_tac>>gvs[])>>rw[]>>fs[]
QED

Theorem add_listsLR_thm:
  add_lists xs ys = add_listsLR xs ys [] 0
Proof
  rw[npbcTheory.add_lists'_thm,add_listsLR_eq]
QED

val ow = rconc (EVAL``CHR 1``);
val zw = rconc (EVAL``CHR 0``);

Theorem subst_aux_no_INR_FILTER:
  ∀l.
  EVERY (λ(c,x). case f x of SOME (INR _ ) => F | _ => T) l ⇒
  subst_aux f l =
  (FILTER (λ(c,x). f x = NONE) l,
    [],
   SUM (MAP (λ(c,x).
    if is_Pos c ⇔ OUTL (THE (f x))
    then Num(ABS c) else 0)
    (FILTER (λ(c,x). f x ≠ NONE) l)))
Proof
  Induct>>rw[npbcTheory.subst_aux_def]>>
  rpt(pairarg_tac>>gvs[])>>
  simp[npbcTheory.subst_aux_def]>>
  Cases_on`f x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  rw[]>>fs[]
QED

Theorem add_lists_emp_2:
  add_lists ls [] = (ls,0)
Proof
  Cases_on`ls`>>EVAL_TAC
QED

Theorem subst_lhs_no_INR_FILTER:
  ∀l.
  EVERY (λ(c,x). case f x of SOME (INR _ ) => F | _ => T) l ⇒
  subst_lhs f l =
  (FILTER (λ(c,x). f x = NONE) l,
   SUM (MAP (λ(c,x).
    if is_Pos c ⇔ OUTL (THE (f x))
    then Num(ABS c) else 0)
    (FILTER (λ(c,x). f x ≠ NONE) l)))
Proof
  rw[npbcTheory.subst_lhs_def]>>
  drule subst_aux_no_INR_FILTER>>
  rw[]>>
  simp[npbcTheory.clean_up_def,add_lists_emp_2]
QED

Theorem SORTED_add_lists_FILTER_MAP:
  ∀l.
  SORTED $< (MAP SND l) ⇒
  add_lists l
    (FILTER (λ(c,x). f x = NONE) (MAP (λ(c,l). (-c,l)) l)) =
  (FILTER (λ(c,x). f x <> NONE) l,
    SUM (MAP (λ(c,x). Num (ABS c))
    (FILTER (λ(c,x). f x = NONE) l)) )
Proof
  Induct>>rw[npbcTheory.add_lists_def]>>
  rpt(pairarg_tac>>gvs[])>>
  drule SORTED_TL>>rw[]>>gvs[]>>
  simp[npbcTheory.add_lists_def]
  >- (EVAL_TAC>>rw[])>>
  qmatch_goalsub_abbrev_tac`add_lists _ lss`>>
  Cases_on`lss`>>gvs[add_lists_emp_2]>>
  Cases_on`h`>>gvs[npbcTheory.add_lists_def]>>
  `MEM r (MAP SND l)` by
    (pop_assum (mp_tac o Q.AP_TERM `λx. MEM r (MAP SND x)`)>>
    simp[MEM_MAP,MEM_FILTER,PULL_EXISTS,EXISTS_PROD]>>
    metis_tac[])>>
  `x < r` by (
    qpat_x_assum`SORTED _ (_ :: _)` mp_tac>>
    DEP_REWRITE_TAC[SORTED_EQ]>>
    simp[])>>
  simp[]
QED

Theorem SUM_SPLIT_LE:
  ∀l.
  SUM (MAP (λ(c,x). Num (ABS c)) (FILTER (λ(c,x). f x = NONE) l)) +
  SUM
    (MAP (λ(c,x). if 0 ≤ c ⇔ OUTL (THE (f x)) then Num (ABS c) else 0)
       (FILTER (λ(c,x). f x ≠ NONE) (MAP (λ(c,l). (-c,l)) l))) ≤
  SUM (MAP (λi. Num (ABS (FST i))) l)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[]
QED

Theorem obj_constraint_simp:
  EVERY (λ(c,x). case f x of SOME (INR _ ) => F | _ => T) l ∧
  SORTED $< (MAP SND l) ⇒
  obj_constraint f (l,b) =
    (FILTER (λ(c,x). f x ≠ NONE) l,
      SUM
      (MAP
         (λ(c,x). if 0 ≤ c ⇔ OUTL (THE (f x)) then Num (ABS c) else 0)
         (FILTER (λ(c,x). f x ≠ NONE) l)))
Proof
  rw[npbcTheory.obj_constraint_def]>>
  DEP_REWRITE_TAC[subst_lhs_no_INR_FILTER]>>
  CONJ_TAC >- (
    gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD]>>
    metis_tac[])>>
  simp[]>>
  DEP_REWRITE_TAC[SORTED_add_lists_FILTER_MAP]>>
  simp[]>>
  pop_assum kall_tac>>
  pop_assum mp_tac>>
  Induct_on`l`>>simp[FORALL_PROD]>>
  rw[]>>
  every_case_tac>>gvs[]
  >- (
    `p_1 = 0` by intLib.ARITH_TAC>>
    simp[])
  >- (
    DEP_REWRITE_TAC[LESS_EQ_ADD_SUB]>>
    simp[SUM_SPLIT_LE])
  >- (
    DEP_REWRITE_TAC[LESS_EQ_ADD_SUB]>>
    simp[SUM_SPLIT_LE]>>
    Cases_on`x'`>>fs[]>>
    intLib.ARITH_TAC)
QED

(* one pass obj_constraint *)
Definition obj_single_aux_def:
  (obj_single_aux f n [] acc k = SOME(REVERSE acc,k:num)) ∧
  (obj_single_aux f n ((c,x:num)::xs) acc k =
    if n < x then
      case f x of
        NONE => obj_single_aux f x xs acc k
      | SOME (INL b) =>
        let r = if is_Pos c ⇔ b then k + Num (ABS c) else k in
          obj_single_aux f x xs ((c,x)::acc) r
      | SOME (INR _) => NONE
    else NONE)
End

Definition obj_single_def:
  (obj_single f [] = SOME([],0:num)) ∧
  (obj_single f ((c,x:num)::xs) =
      case f x of
        NONE => obj_single_aux f x xs [] 0
      | SOME (INL b) =>
        let r = if is_Pos c ⇔ b then Num (ABS c) else 0 in
          obj_single_aux f x xs [(c,x)] r
      | SOME (INR _) => NONE)
End

Theorem obj_single_aux_eq_SOME:
  ∀l f n acc k res.
  obj_single_aux f n l acc k = SOME res ⇒
  EVERY (λ(c,x). case f x of SOME (INR _ ) => F | _ => T) l ∧
  SORTED $< (n::MAP SND l) ∧
  res = (REVERSE acc ++ FILTER (λ(c,x). f x ≠ NONE) l,
      k + SUM
      (MAP
         (λ(c,x). if 0 ≤ c ⇔ OUTL (THE (f x)) then Num (ABS c) else 0)
         (FILTER (λ(c,x). f x ≠ NONE) l)))
Proof
  Induct>>simp[obj_single_aux_def,FORALL_PROD]>>rw[]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[]>>rw[]
QED

Theorem obj_single_eq:
  obj_single f l = SOME res ⇒
  obj_constraint f (l,b) = res
Proof
  Cases_on`l`>>simp[obj_single_def]>>rw[]
  >-
    EVAL_TAC>>
  Cases_on`h`>>fs[obj_single_def] >>
  gvs[AllCaseEqs()]>>
  drule obj_single_aux_eq_SOME>>rw[]>>
  DEP_REWRITE_TAC[obj_constraint_simp]>>
  simp[]
QED

Definition full_obj_single_def:
  full_obj_single f lb =
  case obj_single f (FST lb) of
    NONE => obj_constraint f lb
  | SOME res => res
End

(* DO NOT TRANSLATE DIRECTLY *)
Theorem obj_constraint_rewrite:
  full_obj_single f lb =
  obj_constraint f lb
Proof
  rw[full_obj_single_def]>>
  every_case_tac>>simp[]>>
  drule obj_single_eq>>
  metis_tac[PAIR]
QED

(* Fast substitution for obj_constraint if it is in vomap *)
Definition fast_obj_constraint_def:
  fast_obj_constraint s l vomap =
  case s of
    INR v =>
    if length v = 0 then ([],0)
    else full_obj_single (subst_fun s) l
  | INL (n,_) =>
    if n < strlen vomap
    then
      if strsub vomap n = ^zw then
        ([],0)
      else
        full_obj_single (subst_fun s) l
    else ([],0)
End

Definition fast_red_subgoals_def:
  fast_red_subgoals ord s def obj vomap hs =
  let cobj =
    case obj of NONE => []
    | SOME l => [[not (fast_obj_constraint s l vomap)]] in
  let s = subst_fun s in
  let (fs,gs) = dom_subst hs s ord in
  let c0 = subst s def in (**)
  ([not c0]::(MAP (λc. [not c]) fs) ++ cobj, [gs])
End

Type vimap_ty = ``:((num # num list) + num) option list``;

(* Given a descending sorted list, return the prefix ≥ earliest
Definition split_earliest_def:
  (split_earliest earliest [] acc = REVERSE acc) ∧
  (split_earliest earliest (i::is) acc =
    if i < (earliest:num) then acc
    else
      split_earliest earliest is (i::acc))
End
 *)

(* A reverse mapping of vars -> indices *)
Definition get_indices_def:
  get_indices fml inds s (vimap:vimap_ty) =
  case s of
    INR v =>
    if length v = 0 then []
    else reindex fml inds
  | INL (n,_) =>
    case any_el n vimap NONE of
      NONE => []
    | SOME (INL (n,inds)) => reindex fml inds
    | SOME (INR earliest) => reindex fml inds
End

Definition set_indices_def:
  set_indices inds s (vimap:vimap_ty) rinds =
  case s of
    INR v =>
    if length v = 0 then (inds,vimap)
    else (rinds,vimap)
  | INL (n,_) =>
    case any_el n vimap NONE of
    | NONE => (inds,vimap)
    | SOME (INL _) => (inds , update_resize vimap NONE (SOME (INL (LENGTH rinds,rinds))) n)
    | SOME (INR _) => (rinds,vimap)
End

Definition check_fresh_aux_fml_vimap_def:
  check_fresh_aux_fml_vimap as vimap ⇔
  EVERY (λx. any_el x vimap NONE = NONE) as
End

Definition check_fresh_aux_obj_vomap_def:
  check_fresh_aux_obj_vomap as vomap ⇔
  EVERY (λx. strlen vomap ≤ x ∨ strsub vomap x = ^zw) as
End

Definition check_fresh_aspo_list_def:
  check_fresh_aspo_list c s ord vimap vomap ⇔
  case ord of NONE => T
  | SOME ((f,g,us,vs,as),xs) =>
    check_fresh_aux_fml_vimap as vimap ∧
    check_fresh_aux_obj_vomap as vomap ∧
    check_fresh_aux_constr as c ∧
    check_fresh_aux_subst as s
End

(* The fast path allows for faster checked deletion *)
Definition check_red_list_def:
  check_red_list pres ord obj b tcb fml inds id c s
    (pfs:scope) idopt vimap vomap zeros =
  if check_pres pres s
  then
  let ss = mk_subst s in
  case red_fast ss idopt pfs of
    NONE => (
    let rinds = get_indices fml inds ss vimap in
    let (inds',vimap') = set_indices inds ss vimap rinds in
    let nc = not c in
    let fml_not_c = update_resize fml NONE (SOME (nc,b)) id in
    let hs = has_scope pfs in
    let (rsubs,rscopes) = fast_red_subgoals ord ss c obj vomap hs in
    case extract_scopes_list rscopes ss b fml rsubs pfs of
      NONE => NONE
    | SOME cpfs =>
      (case check_scopes_list cpfs b
        fml_not_c id (id+1) zeros of
         NONE => NONE
      |  SOME(fml', id', zeros') =>
        let rfml = rollback fml' id id' in
        let (untouched,skipped) = skip_ord_subgoal (subst_fun ss) ord in
        if
          do_red_check idopt b tcb fml' inds'
            ss rfml rinds nc pfs rsubs skipped
          (hs ∨ ¬ untouched ⇒
            check_fresh_aspo_list c s ord vimap' vomap)
        then
          SOME (rfml,inds',vimap',id',zeros')
        else NONE))
  | SOME (pf,cid) =>
    check_red_list_fast b fml inds id c pf cid vimap zeros
  else NONE
End

(*
Definition min_opt_def:
  min_opt i j =
  case i of NONE => j
  | SOME ii => MIN ii j
End *)

(* v is the new index of the constraint (last arg) *)
(*
Definition update_earliest_def:
  (update_earliest earliest v [] = earliest) ∧
  (update_earliest earliest v ((i,n)::ns) =
    update_earliest
    (insert n (min_opt (lookup n earliest) v) earliest)
    v
    ns)
End
*)
Definition ind_lim_def:
  ind_lim = 10n
End

Definition opt_cons_def:
  (opt_cons (v:num) NONE = INL (1n,[v])) ∧
  (opt_cons v (SOME (INL (n,ls))) =
    if ind_lim ≤ n
    then
      INR (0n)
    else
      INL (n+1, v::ls)) ∧
  (opt_cons v (SOME (INR earliest)) = INR earliest)
End

Definition update_vimap_def:
  (update_vimap vimap v [] = vimap) ∧
  (update_vimap vimap v ((i,n)::ns) =
    update_vimap
    (update_resize vimap NONE
      (SOME (opt_cons v (any_el n vimap NONE))) n)
    v
    ns)
End

Definition opt_update_inds_def[simp]:
  (opt_update_inds fml NONE id inds vimap zeros =
    (fml,inds,vimap,id,zeros)) ∧
  (opt_update_inds fml (SOME cc) id inds vimap zeros =
    (update_resize fml NONE (SOME cc) id,
      sorted_insert id inds,
      update_vimap vimap id (FST (FST cc)),
      id+1,
      zeros))
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) pres ord obj tcb
    (fml: (npbc # bool) option list) (inds:num list) (id:num)
    vimap vomap zeros =
  case sstep of
  | Lstep lstep =>
    (case check_lstep_list lstep F fml 0 id zeros of
      NONE => NONE
    | SOME (rfml,c,id',zeros') =>
      SOME (opt_update_inds rfml c id' inds vimap zeros'))
  | Red c s pfs idopt =>
    case check_red_list pres ord obj F tcb fml inds id c s pfs
      idopt vimap vomap zeros of
      SOME (rfml,rinds,vimap',id',zeros') =>
      SOME (
        update_resize rfml NONE (SOME (c,tcb)) id',
        sorted_insert id' rinds,
        update_vimap vimap' id' (FST c),
        id'+1,
        zeros')
    | NONE => NONE)
End

Theorem fml_rel_extract_clauses_list:
  ∀ls s b fml fmlls rsubs acc.
  fml_rel fml fmlls ⇒
  extract_clauses (subst_fun s) b fml rsubs ls acc =
  extract_clauses_list s b fmlls rsubs ls acc
Proof
  Induct>>rw[extract_clauses_def,extract_clauses_list_def]>>
  every_case_tac>>
  fs[subst_subst_fun_def]
  >- metis_tac[option_CLAUSES,fml_rel_lookup_core_only]
  >- metis_tac[option_CLAUSES,fml_rel_lookup_core_only]>>
  first_x_assum drule>>
  metis_tac[option_CLAUSES,fml_rel_lookup_core_only]
QED

Theorem fml_rel_extract_scopes_list:
  ∀ls s b fml fmlls rsubs.
  fml_rel fml fmlls ⇒
  extract_scopes scopes ls (subst_fun s) b fml rsubs =
  extract_scopes_list scopes s b fmlls rsubs ls
Proof
  Induct>>rw[]
  >- simp[extract_scopes_def,extract_scopes_list_def]>>
  Cases_on`h`>> simp[extract_scopes_def,extract_scopes_list_def]>>
  TOP_CASE_TAC>>simp[]>>
  DEP_REWRITE_TAC [fml_rel_extract_clauses_list]>> simp[]>>
  metis_tac[]
QED

(* Index list must lazily overapproximate the
  active indices in fmlls *)
Definition ind_rel_def:
  ind_rel fmlls inds ⇔
  ∀x. IS_SOME (any_el x fmlls NONE) ⇒ MEM x inds
End

Theorem ind_rel_list_delete_list:
  ∀l fmlls.
  ind_rel fmlls inds ==>
  ind_rel (list_delete_list l fmlls) inds
Proof
  rw[ind_rel_def]>>
  fs[any_el_list_delete_list,delete_list_def]>>
  every_case_tac>>fs[]
QED

Theorem ind_rel_update_resize:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls NONE v n) (n::inds)
Proof
  simp[ind_rel_def,any_el_update_resize]>>rw[]>>
  every_case_tac>>fs[]
QED

Theorem MEM_sorted_insert:
  ∀ls.
  MEM y (sorted_insert n ls) <=> MEM y (n::ls)
Proof
  Induct>>rw[sorted_insert_def]>>fs[]>>
  metis_tac[]
QED

Theorem SORTED_sorted_insert:
  ∀ls.
  SORTED $>= ls ⇒
  SORTED $>= (sorted_insert n ls)
Proof
  Induct>>rw[sorted_insert_def]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def]>>
  rw[]>>
  fs[MEM_sorted_insert]>>rw[]
QED

Theorem ind_rel_update_resize_sorted_insert:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls NONE v n) (sorted_insert n inds)
Proof
  strip_tac>> drule ind_rel_update_resize>>
  metis_tac[ind_rel_def,MEM_sorted_insert]
QED

Theorem ind_rel_rollback_2:
  ind_rel fmlls inds ∧
  (∀n. n ≥ id' ⇒ any_el n fml NONE = NONE) ∧
  (∀n. n < id ⇒ any_el n fmlls NONE = any_el n fml NONE)
  ⇒
  ind_rel (rollback fml id id') inds
Proof
  rw[rollback_def]>>
  fs[ind_rel_def]>>
  simp[any_el_list_delete_list]>>
  rw[]>>
  fs[MEM_MAP,MEM_COUNT_LIST]>>
  `x < id ∨ x ≥ id'` by intLib.ARITH_TAC>>
  fs[]>>
  first_x_assum drule>>rw[]>>gs[]
QED

Theorem ind_rel_rollback:
  ind_rel fmlls inds ⇒
  ind_rel (rollback fmlls id id') inds
Proof
  rw[rollback_def]>>
  metis_tac[ind_rel_list_delete_list]
QED

Theorem list_insert_fml_list_id:
  ∀cs b id fmlls cid cfmlls.
  list_insert_fml_list cs b id fmlls =
    (cid,cfmlls) ⇒
  id ≤ cid
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  first_x_assum drule>>
  simp[]
QED

Theorem list_insert_fml_list_id_upper:
  ∀cs b id fmlls cid cfmlls.
  list_insert_fml_list cs b id fmlls =
    (cid,cfmlls) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ cid ⇒ any_el n cfmlls NONE = NONE)
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem list_insert_fml_list_mindel:
  ∀cs b id fmlls cid cfmlls.
  list_insert_fml_list cs b id fmlls =
    (cid,cfmlls) ⇒
  (∀n. n < id ⇒ any_el n cfmlls NONE = any_el n fmlls NONE)
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem fml_rel_list_insert_fml_list:
  ∀cs b id fml fmlls cid cfml cid' cfmlls.
  fml_rel fml fmlls ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  list_insert_fml b fml id cs = (cfml,cid) ∧
  list_insert_fml_list cs b id fmlls =
    (cid',cfmlls) ⇒
  cid = cid' ∧
  fml_rel cfml cfmlls ∧
  (∀n. n ≥ cid ⇒ any_el n cfmlls NONE = NONE) ∧
  (∀n. n < id ⇒ any_el n cfmlls NONE = any_el n fmlls NONE) ∧
  id ≤ cid
Proof
  Induct>>
  simp[list_insert_fml_def,list_insert_fml_list_def]>>
  ntac 10 strip_tac>>
  qpat_x_assum`_ = (cfml,_)` mp_tac>>
  simp[insert_fml_def]>>
  strip_tac>>
  first_x_assum (drule_at Any)>>
  disch_then (drule_at Any)>>
  impl_tac >- (
    simp[fml_rel_update_resize,ind_rel_update_resize_sorted_insert]>>
    simp[any_el_update_resize])>>
  rw[any_el_update_resize]
QED

Theorem fml_rel_check_subproofs_list:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    EVERY (λw. w = 0w) zeros ∧
    check_subproofs_list pfs b fmlls mindel id zeros =
      SOME (fmlls', id', zeros') ⇒
    ∃fml'.
      check_subproofs pfs b fml id =
        SOME (fml',id') ∧
      fml_rel fml' fmlls'
Proof
  ho_match_mp_tac check_subproofs_list_ind>>rw[]>>
  fs[check_subproofs_def,check_subproofs_list_def]>>
  gvs[AllCaseEqs()]
  >- (
    drule (CONJUNCT2 fml_rel_check_lstep_list)>>
    rpt(disch_then drule)>>
    drule (CONJUNCT2 check_lstep_list_zeros)>>
    rpt(disch_then drule)>>
    drule (CONJUNCT2 check_lstep_list_id)>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    drule (CONJUNCT2 check_lstep_list_mindel)>>
    simp[]>>
    rw[]>>every_case_tac>>fs[])>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_list_insert_fml_list>>
  strip_tac>>gvs[]>>
  drule_all (CONJUNCT2 fml_rel_check_lstep_list)>>
  rw[]>> simp[]>>
  drule_all fml_rel_check_contradiction_fml>>rw[]>>
  first_x_assum match_mp_tac>>
  rw[]
  >- (
    match_mp_tac fml_rel_rollback>>rw[]
    >- (
      drule (CONJUNCT2 check_lstep_list_mindel)>>
      rw[])>>
    first_assum(qspec_then`n` mp_tac)>>
    drule (CONJUNCT2 check_lstep_list_id)>>
    simp[]>>rw[]>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])
  >- (
    fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])
  >- (
    imp_res_tac check_lstep_list_id>>
    fs[])
  >- (
    drule (CONJUNCT2 check_lstep_list_zeros)>>
    metis_tac[] )
QED

Theorem check_subproofs_list_id:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros'.
    check_subproofs_list pfs b fmlls mindel id zeros =
    SOME (fmlls', id',zeros') ⇒
    id ≤ id'
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  rw[check_subproofs_list_def]>>
  gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_lstep_list_id>>
  imp_res_tac list_insert_fml_list_id>>
  fs[]
QED

Theorem check_subproofs_list_id_upper:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros'.
  check_subproofs_list pfs b fmlls mindel id zeros =
    SOME (fmlls', id',zeros') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  simp[check_subproofs_list_def]>>
  ntac 12 strip_tac>>
  simp[AllCaseEqs()]>>
  strip_tac>>gvs[]
  >- (
    first_x_assum match_mp_tac>>
    match_mp_tac (CONJUNCT2 check_lstep_list_id_upper)>>
    first_x_assum (irule_at Any)>>
    metis_tac[])>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  first_x_assum match_mp_tac>>
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  match_mp_tac (CONJUNCT2 check_lstep_list_id_upper)>>
  first_x_assum (irule_at Any)>>
  metis_tac[list_insert_fml_list_id_upper]
QED

Theorem check_subproofs_list_mindel:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros' n.
  check_subproofs_list pfs b fmlls mindel id zeros =
    SOME (fmlls', id', zeros') ∧
  mindel ≤ id ∧
  n < mindel ⇒
  any_el n fmlls NONE = any_el n fmlls' NONE
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  simp[check_subproofs_list_def]>>rw[]>>
  gvs[AllCaseEqs()]
  >- (
    drule (CONJUNCT2 check_lstep_list_mindel)>>fs[]>>
    drule (CONJUNCT2 check_lstep_list_id)>>fs[]>>
    disch_then drule>>
    simp[])>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  drule (CONJUNCT2 check_lstep_list_mindel)>>fs[]>>
  drule (list_insert_fml_list_mindel)>>fs[]>>
  rw[]>>
  drule (list_insert_fml_list_id)>>
  drule (CONJUNCT2 check_lstep_list_id)>>rw[]>>
  gvs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem check_subproofs_list_zeros:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros'.
  check_subproofs_list pfs b fmlls mindel id zeros =
  SOME (fmlls', id',zeros') ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  EVERY (λw. w = 0w) zeros'
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  rw[check_subproofs_list_def]>>
  gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_lstep_list_zeros>>
  fs[]
QED

Theorem fml_rel_check_scopes_list:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    EVERY (λw. w = 0w) zeros ∧
    check_scopes_list pfs b fmlls mindel id zeros =
      SOME (fmlls', id', zeros') ⇒
    ∃fml'.
      check_scopes pfs b fml id =
        SOME (fml',id') ∧
      fml_rel fml' fmlls'
Proof
  ho_match_mp_tac check_scopes_list_ind>>rw[]>>
  fs[check_scopes_def,check_scopes_list_def]>>
  gvs[AllCaseEqs()]
  >- (
    drule_all fml_rel_check_subproofs_list>>
    rw[]>>simp[]>>
    first_x_assum irule>>
    drule check_subproofs_list_id>>
    drule check_subproofs_list_id_upper>>
    drule check_subproofs_list_zeros>>
    simp[])>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_list_insert_fml_list>>
  strip_tac>>gvs[]>>
  drule_all fml_rel_check_subproofs_list>>
  rw[]>> simp[]>>
  first_x_assum irule>>
  rw[]
  >- (
    fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    drule check_subproofs_list_id_upper>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])
  >- (
    drule check_subproofs_list_id>>
    fs[])
  >- (
    drule check_subproofs_list_zeros>>
    metis_tac[])
  >- (
    match_mp_tac fml_rel_rollback>>rw[]
    >- (
      drule check_subproofs_list_mindel>>
      rw[])>>
    first_assum(qspec_then`n` mp_tac)>>
    drule check_subproofs_list_id>>
    simp[]>>rw[]>>
    drule check_subproofs_list_id_upper>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])
QED

Theorem check_scopes_list_id:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros'.
    check_scopes_list pfs b fmlls mindel id zeros =
    SOME (fmlls', id',zeros') ⇒
    id ≤ id'
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  rw[check_scopes_list_def]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_subproofs_list_id>>
  imp_res_tac list_insert_fml_list_id>>
  gvs[]
QED

Theorem check_scopes_list_id_upper:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros'.
  check_scopes_list pfs b fmlls mindel id zeros =
    SOME (fmlls', id',zeros') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  simp[check_scopes_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  simp[AllCaseEqs()]>>
  rpt strip_tac>>
  gvs[]
  >- metis_tac[check_subproofs_list_id_upper]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  first_x_assum (irule_at Any)>>
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  match_mp_tac check_subproofs_list_id_upper>>
  first_x_assum (irule_at Any)>>
  metis_tac[list_insert_fml_list_id_upper]
QED

Theorem check_scopes_list_mindel:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros' n.
  check_scopes_list pfs b fmlls mindel id zeros =
    SOME (fmlls', id', zeros') ∧
  mindel ≤ id ∧
  n < mindel ⇒
  any_el n fmlls NONE = any_el n fmlls' NONE
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  simp[check_scopes_list_def]>>rw[]>>
  gvs[AllCaseEqs()]
  >- (
    drule check_subproofs_list_mindel>> fs[]>>
    drule check_subproofs_list_id>>fs[])>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  drule check_subproofs_list_mindel>> fs[]>>
  drule (list_insert_fml_list_mindel)>>fs[]>>
  rw[]>>
  drule (list_insert_fml_list_id)>>
  drule check_subproofs_list_id>>rw[]>>
  gvs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem check_scopes_list_zeros:
  ∀pfs b fmlls mindel id zeros fmlls' id' zeros'.
  check_scopes_list pfs b fmlls mindel id zeros =
  SOME (fmlls', id',zeros') ∧
  EVERY (λw. w = 0w) zeros
  ⇒
  EVERY (λw. w = 0w) zeros'
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  rw[check_scopes_list_def]>>
  gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_subproofs_list_zeros>>
  fs[]
QED

Theorem reindex_aux:
  ∀inds iacc.
  reindex_aux fmlls inds iacc =
  let is = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds in
  (REVERSE iacc ++ is)
Proof
  Induct>>rw[reindex_aux_def]>>
  gvs[lookup_core_only_list_def,IS_SOME_EXISTS,AllCaseEqs()]
QED

Theorem reindex_characterize:
  reindex fmlls inds = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds
Proof
  rw[reindex_def,reindex_aux]
QED

Theorem revalue_aux_SUBSET:
  ∀inds vacc.
  fml_rel fml fmlls ∧
  set vacc ⊆ core_only_fml b fml ⇒
  set (revalue_aux b fmlls inds vacc) ⊆ core_only_fml b fml
Proof
  Induct>>rw[revalue_aux_def]>>
  every_case_tac>>rw[]>>
  first_x_assum match_mp_tac>>fs[]>>
  drule fml_rel_lookup_core_only>>
  simp[lookup_core_only_list_def]>>
  disch_then(qspecl_then[`h`,`b`] mp_tac)>>
  simp[]>>rw[]>>gvs[]>>
  gvs[core_only_fml_def,lookup_core_only_def,AllCaseEqs()]>>
  rw[]>>gvs[]>>
  metis_tac[]
QED

Theorem revalue_SUBSET:
  fml_rel fml fmlls ==>
  set (revalue b fmlls inds) ⊆ core_only_fml b fml
Proof
  rw[revalue_def,revalue_aux_SUBSET]
QED

Theorem SORTED_reindex:
  SORTED $>= inds ∧
  reindex fml inds = is ⇒
  SORTED $>= is
Proof
  rw[reindex_characterize]>>
  match_mp_tac SORTED_FILTER>>
  fs[transitive_def]
QED

Theorem ind_rel_reindex:
  ind_rel fml inds ⇒
  ind_rel fml (reindex fml inds)
Proof
  rw[reindex_characterize]>>
  fs[ind_rel_def,MEM_FILTER]
QED

Theorem SORTED_HEAD_LESS:
  ¬(h ≥ mini:num) ∧
  SORTED $>= (h::inds) ⇒
  EVERY (λx. x < mini) inds
Proof
  DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def,EVERY_MEM]>>
  rw[]>>
  first_x_assum drule>>
  fs[]
QED

(*
Theorem reindex_partial_aux:
  ∀inds iacc vacc.
  SORTED $>= inds ⇒
  reindex_partial_aux b fmlls mini inds iacc vacc =
  let finds = FILTER (λx. x ≥ mini) inds in
  let binds = FILTER (λx. x < mini) inds in
  let is = FILTER (λx. IS_SOME (any_el x fmlls NONE)) finds in
  let vs =
    MAP (λx. THE (lookup_core_only_list b fmlls x))
    (FILTER (λx. IS_SOME (lookup_core_only_list b fmlls x))
      finds) in
  (REVERSE iacc ++ is, REVERSE vs ++ vacc, binds)
Proof
  Induct>>simp[reindex_partial_aux_def]>>
  rw[]>>fs[]
  >- (
    drule_all SORTED_HEAD_LESS>>rw[]>>
    fs[FILTER_FILTER,FILTER_EQ_NIL,EVERY_MEM,MEM_FILTER]>>
    rw[]>>
    first_x_assum drule>>fs[])
  >- (
    drule_all SORTED_HEAD_LESS>>rw[]>>
    fs[FILTER_FILTER,FILTER_EQ_NIL,EVERY_MEM,MEM_FILTER]>>
    rw[]>>
    first_x_assum drule>>fs[])
  >- (
    drule_all SORTED_HEAD_LESS>>rw[]>>
    metis_tac[GSYM FILTER_EQ_ID])>>
  drule SORTED_TL>>strip_tac>>fs[]>>
  every_case_tac>>
  gvs[lookup_core_only_list_def,IS_SOME_EXISTS,AllCaseEqs()]
QED

Theorem FST_reindex_partial_characterize:
  SORTED $>= inds ∧
  reindex_partial b fmlls mini inds = (is,vs,rest) ⇒
  case mini of NONE => is = []
  | SOME mini =>
    is = FILTER (λx. IS_SOME (any_el x fmlls NONE))
      (FILTER (λx. x ≥ mini) inds)
Proof
  rw[reindex_partial_def,reindex_partial_aux]>>
  every_case_tac>>fs[]>>
  drule reindex_partial_aux>>
  rw[]>>gvs[]
QED

Theorem SND_reindex_partial_characterize:
  fml_rel fml fmlls ∧
  SORTED $>= inds ∧
  reindex_partial b fmlls mini inds = (is,vs,rest) ⇒
  set vs ⊆ core_only_fml b fml
Proof
  rw[reindex_partial_def]>>
  gvs[AllCaseEqs()]>>
  drule reindex_partial_aux>>
  rw[]>>gvs[]>>
  simp[SUBSET_DEF,MEM_MAP,MEM_FILTER,PULL_EXISTS,range_def]>>
  rw[]>>
  fs[IS_SOME_EXISTS]>>
  drule fml_rel_lookup_core_only>>
  rw[]>>
  gvs[lookup_core_only_def,core_only_fml_def,AllCaseEqs()]
  >-
    metis_tac[]>>
  rw[]>>fs[]>>
  metis_tac[]
QED

Theorem ind_rel_reindex_partial:
  SORTED $>= inds ∧
  ind_rel fml inds ∧
  reindex_partial b fml mini inds = (is,vs,rest) ⇒
  ind_rel fml (is++rest) ∧
  SORTED $>= (is++rest)
Proof
  strip_tac>>
  gvs[reindex_partial_def,AllCaseEqs()]>>
  drule reindex_partial_aux>>
  strip_tac>>gvs[]>>
  conj_tac >- (gvs [ind_rel_def,MEM_FILTER])
  \\ DEP_REWRITE_TAC [SORTED_APPEND]
  \\ gvs [MEM_FILTER]
  \\ rpt $ irule_at Any sortingTheory.SORTED_FILTER \\ gvs []
  \\ gvs [transitive_def]
QED
*)

Theorem MEM_subst_indexes:
  ∀inds i c.
  MEM i inds ∧
  lookup_core_only_list b fml i = SOME c ∧
  subst_opt (subst_fun s) c = SOME res
  ⇒
  MEM (i,res) (subst_indexes s b fml inds)
Proof
  Induct>>rw[subst_indexes_def]>>
  every_case_tac>>
  fs[AllCaseEqs(),any_el_def]>>
  fs[subst_opt_subst_fun_def]
QED

Theorem subst_indexes_MEM:
  ∀inds i res.
  MEM (i,res) (subst_indexes s b fml inds) ⇒
  ∃c.
  MEM i inds ∧
  lookup_core_only_list b fml i = SOME c ∧
  subst_opt (subst_fun s) c = SOME res
Proof
  Induct>>rw[subst_indexes_def]>>
  every_case_tac>>
  gvs[AllCaseEqs(),any_el_def,subst_opt_subst_fun_def]>>
  metis_tac[]
QED

Theorem split_goals_same_goals:
  set goals' = set goals ⇒
  split_goals fml nc proved goals ⇒
  split_goals fml nc proved goals'
Proof
  rw[split_goals_def,PARTITION_DEF]>>
  pairarg_tac>>rw[]>>
  pairarg_tac>>fs[]>>
  qpat_x_assum`_ = (_,_)` (ASSUME_TAC o SYM)>>
  drule PARTs_HAVE_PROP>>
  drule PART_MEM>>
  qpat_x_assum`_ = (_,_)` (ASSUME_TAC o SYM)>>
  drule PARTs_HAVE_PROP>>
  drule PART_MEM>>
  rw[] >>
  fs[EVERY_MEM,FORALL_PROD,EXTENSION]>>rw[]>>
  fs[MEM_MAP,EXISTS_PROD,mem_constraint_thm]>>
  metis_tac[]
QED

Theorem split_goals_hash_imp_split_goals:
  set fmlls ⊆ range fml ∧
  split_goals_hash fmlls nc proved goals ⇒
  split_goals fml nc proved goals
Proof
  rw[split_goals_def,split_goals_hash_def]>>
  rw[]>>
  pairarg_tac>>fs[]>>
  fs[EVERY_FILTER,EVERY_MAP]>>
  qpat_x_assum`EVERY _ _`mp_tac>> match_mp_tac MONO_EVERY>>
  simp[FORALL_PROD, METIS_PROVE []``(¬P ⇒ Q) ⇔ P ∨ Q``]>>
  rw[]>>simp[]>>
  drule in_hashset_mk_hashset>>
  rw[]
  >- fs[MEM_MAP,SUBSET_DEF]>>
  drule in_hashset_mk_hashset>>
  rw[]
  >-
    simp[mem_constraint_thm,MEM_MAP]>>
  pop_assum mp_tac>>
  simp[in_hashset_def]>>
  DEP_REWRITE_TAC[EL_REPLICATE]>>
  simp[hash_constraint_def,mem_constraint_thm]>>
  match_mp_tac MOD_LESS>>
  EVAL_TAC
QED

Theorem lookup_core_only_list_list_delete_list:
  ∀ls n fml.
  lookup_core_only_list b
    (list_delete_list ls fml) n =
  if MEM n ls then NONE
  else
    lookup_core_only_list b fml n
Proof
  Induct>>rw[list_delete_list_def,delete_list_def]>>
  fs[]
  >- (
    gvs[lookup_core_only_list_def,IS_SOME_EXISTS,AllCaseEqs()]>>
    gs[any_el_ALT,EL_LUPDATE])
  >- (
    gvs[lookup_core_only_list_def,IS_SOME_EXISTS,AllCaseEqs()]>>
    gs[any_el_ALT,EL_LUPDATE])>>
  simp[lookup_core_only_list_def,any_el_ALT,EL_LUPDATE]
QED

(*
Definition earliest_rel_def:
  earliest_rel fmlls earliest ⇔
  ∀x pos.
  pos < min_opt (sptree$lookup x earliest) (LENGTH fmlls) ⇒
  case EL pos fmlls of NONE => T
    | SOME c => ¬MEM x (MAP SND (FST (FST c)))
End
*)

(*
Definition vimap_rel_aux_def:
  vimap_rel_aux fmlls vimap ⇔
  ∀i c x.
    i < LENGTH fmlls ∧
    EL i fmlls = SOME c ∧
    MEM x (MAP SND (FST (FST c))) ⇒
    ∃ls. sptree$lookup x vimap = SOME ls ∧ MEM i ls
End

Definition vimap_rel_def:
  vimap_rel fmlls vimap ⇔
  OPTION_ALL (vimap_rel_aux fmlls) vimap
End
*)

Definition vimap_rel_def:
  vimap_rel fmlls (vimap:vimap_ty) ⇔
  ∀i c x.
    i < LENGTH fmlls ∧
    EL i fmlls = SOME c ∧
    MEM x (MAP SND (FST (FST c))) ⇒
    ∃ll.
      any_el x vimap NONE = SOME ll ∧
      case ll of
        INL (n,ls) => MEM i ls
      | INR earliest => T (*earliest ≤ i *)
End


(*
(* If we already proved fml_rel, then we get earliest_rel
  for free *)
Theorem fml_rel_fml_rel_earliest_rel:
  fml_rel fml fmlls ∧
  earliest_rel fmlls earliest ∧
  fml_rel fml fmlls' ⇒
  earliest_rel fmlls' earliest
Proof
  rw[fml_rel_def,earliest_rel_def]>>
  first_x_assum(qspec_then `pos` mp_tac)>>
  first_x_assum(qspecl_then [`x`,`pos`] mp_tac)>>
  first_x_assum(qspec_then `pos` mp_tac)>>
  rw[any_el_ALT]>>
  gvs[min_opt_def]>>
  every_case_tac>>fs[]
QED
*)
Theorem subst_opt_aux_MEM:
  ∀c old new k.
  subst_opt_aux f c = (old,new,k,F) ⇒
  ∃x. MEM x (MAP SND c) ∧ IS_SOME (f x)
Proof
  Induct>> simp[npbcTheory.subst_opt_aux_def]>>
  Cases>>
  rw[npbcTheory.subst_opt_aux_def]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  every_case_tac>>gvs[]>>
  metis_tac[IS_SOME_EXISTS]
QED

Theorem IS_SOME_subst_opt:
  IS_SOME (subst_opt f c) ⇒
  ∃x. MEM x (MAP SND (FST c)) ∧ IS_SOME (f x)
Proof
  Cases_on`c`>>rw[npbcTheory.subst_opt_eq]>>
  rpt (pairarg_tac>>fs[])>>
  every_case_tac>>gvs[]>>
  metis_tac[subst_opt_aux_MEM]
QED

Theorem mk_subst_cases:
  mk_subst s =
  case s of
  | [] => INR (Vector [])
  | [(n,v)] => INL (n,v)
  | _ => INR (spt_to_vec (fromAList s))
Proof
  every_case_tac>>fs[mk_subst_def]
QED

Theorem MEM_get_indices_mk_subst:
  vimap_rel fmlls vimap ∧
  ind_rel fmlls inds ∧
  any_el i fmlls NONE = SOME (c,b) ∧
  IS_SOME (subst_opt (subst_fun (mk_subst s)) c)
  ⇒
  MEM i (get_indices fmlls inds (mk_subst s) vimap)
Proof
  rw[get_indices_def]>>
  TOP_CASE_TAC>>rw[]
  >- (
    drule IS_SOME_subst_opt>>simp[subst_fun_def]>>
    rw[]>>Cases_on`x`>>gvs[]>>
    gvs[IS_SOME_EXISTS,vimap_rel_def,any_el_ALT]>>
    last_x_assum (drule_at Any)>>
    simp[]>>
    disch_then drule>>rw[]>>
    every_case_tac>>
    gvs[reindex_characterize,MEM_FILTER,IS_SOME_EXISTS,ind_rel_def,PULL_EXISTS,any_el_ALT])
  >- (
    drule IS_SOME_subst_opt>>
    strip_tac>>
    gvs[mk_subst_cases,AllCaseEqs(),subst_fun_def,spt_to_vecTheory.vec_lookup_def])
  >- (
    gvs[reindex_characterize,MEM_FILTER]>>
    gvs[ind_rel_def])
QED

Theorem fml_rel_fml_rel_vimap_rel:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  fml_rel fml fmlls' ⇒
  vimap_rel fmlls' vimap
Proof
  rw[fml_rel_def,vimap_rel_def]>>
  rw[]>>
  first_x_assum(qspec_then `i` mp_tac)>>
  last_x_assum(qspec_then `i` mp_tac)>>
  last_x_assum(qspec_then `i` mp_tac)>>
  rw[any_el_ALT]>>gvs[]>>
  metis_tac[]
QED

Theorem ind_rel_get_indices_set_indices:
  get_indices fmlls inds s vimap = rinds ∧
  set_indices inds s vimap rinds = (inds',vimap') ∧
  ind_rel fmlls inds ⇒
  ind_rel fmlls inds'
Proof
  rw[get_indices_def,set_indices_def] >>
  gvs[AllCaseEqs()]>>
  metis_tac[ind_rel_reindex]
QED

Theorem vimap_rel_get_indices_set_indices:
  set_indices inds s vimap
    (get_indices fmlls inds s vimap) = (inds',vimap') ∧
  vimap_rel fmlls vimap ⇒
  vimap_rel fmlls vimap'
Proof
  rw[get_indices_def,set_indices_def] >>
  gvs[AllCaseEqs(),vimap_rel_def]>>
  every_case_tac>>rw[any_el_update_resize]>>
  first_x_assum drule_all>>
  rw[reindex_characterize,MEM_FILTER]>>
  simp[any_el_ALT]
QED

Definition vomap_rel_def:
  vomap_rel obj ls ⇔
  case obj of
    NONE => T
  | SOME l =>
    ∀x.
    MEM x (MAP SND (FST l)) <=>
    x < strlen ls ∧ strsub ls x ≠ ^zw
End

Theorem add_lists_map_negate_coeff:
  ∀ls rs.
  rs = (MAP (λ(c,l). (-c,l)) ls) ⇒
  add_lists ls rs = ([],SUM (MAP (λi. Num (ABS (FST i))) ls))
Proof
  ho_match_mp_tac npbcTheory.add_lists_ind>>
  simp[npbcTheory.add_lists_def,npbcTheory.add_terms_def]
QED

Theorem subst_aux_id:
  ∀l.
  EVERY (\v. f v = NONE) (MAP SND l) ⇒
  subst_aux f l = (l,[],0)
Proof
  Induct>-simp[npbcTheory.subst_aux_def]>>
  Cases>>
  rw[npbcTheory.subst_aux_def]
QED

Theorem subst_lhs_id:
  EVERY (\v. f v = NONE) (MAP SND l) ⇒
  subst_lhs f l = (l, 0)
Proof
  rw[npbcTheory.subst_lhs_def]>>
  rpt(pairarg_tac>>fs[])>>
  drule subst_aux_id>>strip_tac>>
  gvs[EVAL``clean_up []``]>>
  Cases_on`l`>>
  gvs[npbcTheory.add_lists_def]
QED

Theorem vomap_rel_fast_obj_constraint:
  vomap_rel (SOME l) vomap ⇒
  fast_obj_constraint s l vomap =
  obj_constraint (subst_fun s) l
Proof
  rw[fast_obj_constraint_def,obj_constraint_rewrite]>>
  every_case_tac>>
  Cases_on`l`>>
  fs[npbcTheory.obj_constraint_def,subst_fun_def]>>
  rpt (pairarg_tac>>fs[])>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[add_lists_map_negate_coeff]>>rw[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[subst_lhs_id]>>
  fs[vomap_rel_def]>>
  simp[EVERY_MAP,LAMBDA_PROD,subst_fun_def]>>
  gvs[EVERY_MEM]>>
  rw[]>>pairarg_tac>>
  fs[EXTENSION,MEM_MAP,domain_lookup,spt_to_vecTheory.vec_lookup_def]>>
  metis_tac[option_CLAUSES,SND,PAIR]
QED

Theorem vomap_rel_fast_red_subgoals:
  vomap_rel obj vomap ⇒
  fast_red_subgoals ord s def obj vomap hs =
  red_subgoals ord (subst_fun s) def obj hs
Proof
  rw[fast_red_subgoals_def,red_subgoals_def]>>
  every_case_tac>>fs[]>>
  metis_tac[vomap_rel_fast_obj_constraint]
QED

Theorem vimap_rel_check_fresh_aux_fml_vimap:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  check_fresh_aux_fml_vimap as vimap ⇒
  check_fresh_aux_fml as fml
Proof
  rw[check_fresh_aux_fml_vimap_def,check_fresh_aux_fml_def]>>
  pop_assum mp_tac>>
  match_mp_tac EVERY_MONOTONIC>>
  gvs[vimap_rel_def,fml_rel_def]>>rw[]>>
  CCONTR_TAC>>
  gvs[range_def]>>
  first_x_assum (drule_at Any)>>
  first_x_assum (qspec_then`n` mp_tac)>>
  simp[any_el_ALT]>>
  metis_tac[]
QED

Theorem vomap_rel_check_fresh_aux_obj_vomap:
  vomap_rel obj vomap ∧
  check_fresh_aux_obj_vomap as vomap ⇒
  check_fresh_aux_obj as obj
Proof
  rw[check_fresh_aux_obj_vomap_def,check_fresh_aux_obj_def]>>
  TOP_CASE_TAC>>simp[]>>
  last_x_assum mp_tac>>
  match_mp_tac EVERY_MONOTONIC>>
  gvs[vomap_rel_def]>>rw[]>>
  CCONTR_TAC>>
  gvs[]
QED

Theorem vimap_rel_vomap_rel_check_fresh_aspo_list:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  vomap_rel obj vomap ∧
  check_fresh_aspo_list c s ord vimap vomap ⇒
  check_fresh_aspo fml c obj s ord
Proof
  rw[check_fresh_aspo_list_def,check_fresh_aspo_def]>>
  gvs[AllCasePreds()]>>
  metis_tac[vomap_rel_check_fresh_aux_obj_vomap,vimap_rel_check_fresh_aux_fml_vimap]
QED

Theorem fml_rel_check_red_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel obj vomap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  EVERY (λw. w = 0w) zeros ∧
  check_red_list pres ord obj b tcb fmlls inds id c s pfs
    idopt vimap vomap zeros =
    SOME (fmlls', inds', vimap', id', zeros') ⇒
    check_red pres ord obj b tcb fml id c s pfs idopt = SOME id' ∧
    fml_rel fml fmlls' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
    EVERY (λw. w = 0w) zeros' ∧
    id ≤ id'
Proof
  strip_tac>>
  fs[check_red_list_def]>>
  gvs[AllCaseEqs()]
  >- (
    gvs[vomap_rel_fast_red_subgoals]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    gvs[AllCaseEqs()]>>
    simp[check_red_def]>>
    DEP_REWRITE_TAC [fml_rel_extract_scopes_list]>> simp[]>>
    `fml_rel (insert id ((not c,b)) fml)
      (update_resize fmlls NONE (SOME (not c,b)) id)` by
      metis_tac[fml_rel_update_resize]>>
    drule fml_rel_check_scopes_list>>
    disch_then (drule_at Any)>>
    impl_tac>- (
      rw[]>>
      simp[any_el_update_resize])>>
    simp[]>>strip_tac>>
    gvs[insert_fml_def]>>
    drule check_scopes_list_id>>
    drule check_scopes_list_id_upper>>
    drule check_scopes_list_mindel>>
    drule_all vimap_rel_get_indices_set_indices>>
    simp[any_el_update_resize]>>
    ntac 4 strip_tac>>
    CONJ_TAC >- (
      gvs[do_red_check_def,AllCaseEqs(),insert_fml_def]>>
      TOP_CASE_TAC>>fs[]
      >- (
        rpt (pairarg_tac>>fs[])>>
        CONJ_TAC >-
          metis_tac[vimap_rel_vomap_rel_check_fresh_aspo_list]>>
        (drule_at Any) split_goals_hash_imp_split_goals>>
        disch_then (qspec_then`mk_core_fml (b ∨ tcb) fml` mp_tac)>>
        impl_tac >- (
          simp[range_mk_core_fml]>>
          gvs[get_indices_def,set_indices_def] >>
          every_case_tac>> gvs[]>>
          match_mp_tac revalue_SUBSET>>
          match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
        match_mp_tac split_goals_same_goals>>
        simp[EXTENSION,FORALL_PROD]>>
        rw[]>>eq_tac>>rw[]
        >- (
          fs[MEM_toAList,lookup_map_opt,AllCaseEqs()]>>
          match_mp_tac (GEN_ALL MEM_subst_indexes)>>
          gvs[lookup_mk_core_fml]>>
          first_assum (irule_at Any)>>
          `∃b'.
            lookup p_1 fml = SOME (x,b') ∧
            (b ⇒ b')` by (
            gvs[lookup_core_only_def,AllCaseEqs()])>>
          CONJ_TAC>- (
            match_mp_tac (GEN_ALL MEM_get_indices_mk_subst)>>
            gvs[IS_SOME_EXISTS]>>
            first_x_assum (irule_at Any)>>
            metis_tac[fml_rel_def])>>
          simp[rollback_def,lookup_core_only_list_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
          rw[]
          >- (
            last_x_assum(qspec_then`id+y` assume_tac)>>
            fs[fml_rel_def]>>
            last_x_assum(qspec_then`id+y` assume_tac)>>
            fs[])
          >- (
            `p_1 < id` by (
              CCONTR_TAC>>fs[]>>
              last_x_assum(qspec_then`p_1` mp_tac)>>
              impl_tac>-fs[]>>
              fs[fml_rel_def])>>
            first_x_assum drule>>
            qpat_x_assum`fml_rel fml _` assume_tac>>
            drule (GSYM fml_rel_lookup_core_only)>>
            strip_tac>>fs[]>>
            gvs[lookup_core_only_list_def,AllCaseEqs()]>>
            metis_tac[]))>>
        drule subst_indexes_MEM>>
        rw[MEM_toAList,lookup_map_opt]>>
        gvs[reindex_characterize]>>
        fs[rollback_def,lookup_core_only_list_list_delete_list,MEM_MAP,MEM_COUNT_LIST,MEM_FILTER]>>
        `p_1 < id'` by (
          CCONTR_TAC>>fs[]>>
          first_x_assum(qspec_then`p_1` mp_tac)>>
          impl_tac>-fs[]>>
          gvs[lookup_core_only_list_def]>>
          CCONTR_TAC>>gvs[])>>
        `p_1 < id` by intLib.ARITH_TAC>>
        simp[lookup_mk_core_fml]>>
        `lookup_core_only (b ∨ tcb) fml p_1 = SOME c'` by (
          qpat_x_assum`fml_rel fml _` assume_tac>>
          drule (GSYM fml_rel_lookup_core_only)>>
          strip_tac>>fs[]>>
          gvs[lookup_core_only_list_def,AllCaseEqs()])>>
        fs[])>>
      match_mp_tac (GEN_ALL fml_rel_check_contradiction_fml)>>
      metis_tac[])>>
    CONJ_ASM1_TAC>- (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[] >>
      metis_tac[ind_rel_get_indices_set_indices])>>
    CONJ_TAC >- (
      metis_tac[fml_rel_fml_rel_vimap_rel])>>
    CONJ_TAC >- (
      simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
      rw[])>>
    metis_tac[check_scopes_list_zeros])>>
  gvs[check_red_list_fast_def,AllCaseEqs(),red_fast_def,check_red_def,insert_fml_def]>>
  pairarg_tac>>gvs[extract_scopes_def,check_scopes_def,mk_scope_def,extract_clauses_def,check_subproofs_def,insert_fml_def,check_lstep_list_def]
  >- (
    drule fml_rel_update_resize>>
    disch_then(qspecl_then[`id`,`(not c,b)`] assume_tac)>>
    drule_all fml_rel_check_contradiction_fml>>
    simp[]>>
    strip_tac>>
    CONJ_ASM1_TAC
    >- (
      match_mp_tac fml_rel_rollback>>
      simp[]>>
      rw[any_el_update_resize])>>
    CONJ_TAC
    >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[any_el_update_resize])>>
    CONJ_TAC
    >- (* vimap_rel *)
      metis_tac[fml_rel_fml_rel_vimap_rel]
    >-
      simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,any_el_update_resize])>>
  `fml_rel (insert id ((not c,b)) fml)
    (update_resize fmlls NONE (SOME (not c,b)) id)` by
    metis_tac[fml_rel_update_resize]>>
  drule (CONJUNCT2 fml_rel_check_lstep_list)>>
  disch_then (drule_at Any)>>
  impl_tac >- simp[any_el_update_resize]>>
  strip_tac>>simp[]>>
  drule (CONJUNCT2 check_lstep_list_id)>>
  drule (CONJUNCT2 check_lstep_list_id_upper)>>
  drule (CONJUNCT2 check_lstep_list_mindel)>>
  simp[any_el_update_resize]>>
  ntac 3 strip_tac>>
  CONJ_TAC >- metis_tac[fml_rel_check_contradiction_fml]>>
  CONJ_ASM1_TAC >- (
    match_mp_tac fml_rel_rollback>>
    fs[]>>
    rw[]>- metis_tac[]>>
    first_x_assum drule >> simp[] )>>
  CONJ_TAC >- (
    match_mp_tac ind_rel_rollback_2>>
    simp[])>>
  CONJ_TAC >- (* vimap_rel *)
    metis_tac[fml_rel_fml_rel_vimap_rel]>>
  CONJ_TAC >- (
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,any_el_update_resize]>>
    rw[])>>
  metis_tac[check_lstep_list_zeros]
QED

Theorem opt_update_inds_opt_update:
  opt_update_inds fml c id inds vimap zeros =
    (fml',inds',vimap',id',zeros') ⇒
  opt_update fml c id = (fml',id')
Proof
  Cases_on`c`>>rw[]
QED

Theorem ind_rel_check_lstep_list:
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_lstep_list lstep b fmlls mindel id zeros =
    SOME (fmlls',x,y,z) ⇒
  ind_rel fmlls' inds
Proof
  rw[]>>
  fs[ind_rel_def]>>
  drule (CONJUNCT1 check_lstep_list_id_del)>>
  drule (CONJUNCT1 check_lstep_list_id_upper)>>
  rw[]>>
  `x' < id` by
    (CCONTR_TAC>>gvs[])>>
  metis_tac[]
QED

Theorem opt_update_inds_SORTED:
  SORTED $>= inds ∧
  opt_update_inds fml c id inds vimap zeros =
    (fml',inds',vimap',id',zeros') ⇒
  SORTED $>= inds'
Proof
  Cases_on`c`>>rw[]>>fs[]>>
  metis_tac[SORTED_sorted_insert]
QED

Theorem opt_update_inds_ind_rel:
  ind_rel fml inds ∧
  opt_update_inds fml c id inds vimap zeros =
    (fml',inds',vimap',id',zeros') ⇒
  ind_rel fml' inds'
Proof
  Cases_on`c`>>rw[]>>fs[]>>
  simp[ind_rel_update_resize_sorted_insert]
QED

(*
Theorem earliest_rel_check_lstep_list:
  earliest_rel fmlls earliest ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_lstep_list lstep b fmlls mindel id =
    SOME (fmlls',x,y) ⇒
  earliest_rel fmlls' earliest
Proof
  rw[]>>
  fs[earliest_rel_def]>>
  rw[]>>
  first_x_assum(qspecl_then[`x'`,`pos`] mp_tac)>>
  drule (CONJUNCT1 check_lstep_list_id_del)>>
  drule (CONJUNCT1 check_lstep_list_id_upper)>>
  disch_then drule>>
  rw[]>>
  Cases_on`pos < id`>>fs[]
  >- (
    gvs[min_opt_def]>>
    every_case_tac>>gvs[]>>
    first_x_assum drule >>
    rw[any_el_ALT]>>
    gvs[])>>
  `pos ≥ id` by fs[]>>
  gvs[min_opt_def]>>
  every_case_tac>>gvs[]>>
  first_x_assum drule >>
  rw[any_el_ALT]>>
  gvs[]
QED

Triviality earliest_rel_append_NONE:
  earliest_rel fml earliest ⇒
  earliest_rel (fml ++ REPLICATE k NONE) earliest
Proof
  gvs [earliest_rel_def] \\ rw []
  \\ Cases_on ‘LENGTH fml ≤ pos’ >-
   (simp [EL_APPEND2]
    \\ DEP_REWRITE_TAC [EL_REPLICATE] \\ fs []
    \\ Cases_on ‘lookup x earliest’ \\ gvs [min_opt_def])
  \\ gvs [GSYM NOT_LESS,EL_APPEND1]
  \\ last_x_assum irule
  \\ Cases_on ‘lookup x earliest’ \\ gvs [min_opt_def]
QED

Triviality lookup_update_earliest_none:
  ∀v0 n earliest x.
    lookup x (update_earliest earliest n v0) = NONE ⇒
    ¬MEM x (MAP SND v0) ∧ lookup x earliest = NONE
Proof
  Induct \\ gvs [update_earliest_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum drule \\ fs []
  \\ gvs [lookup_insert,AllCaseEqs()]
QED

Triviality lookup_update_earliest_some:
  ∀v0 n earliest x k.
    lookup x (update_earliest earliest n v0) = SOME k ∧ n < k ⇒
    ¬MEM x (MAP SND v0) ∧ lookup x earliest = SOME k
Proof
  Induct \\ gvs [update_earliest_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum drule \\ fs []
  \\ gvs [lookup_insert,AllCaseEqs()]
  \\ Cases_on ‘lookup p_2 earliest’ \\ gvs [min_opt_def]
  \\ ‘MIN x' n ≠ k’ by gvs [MIN_DEF] \\ gvs []
QED

Triviality earliest_rel_lupdate:
  n < LENGTH fml ∧
  earliest_rel fml earliest ⇒
  earliest_rel (LUPDATE (SOME (v,b)) n fml)
    (update_earliest earliest n (FST v))
Proof
  gvs [earliest_rel_def] \\ rw [] \\ gvs [EL_LUPDATE]
  \\ PairCases_on ‘v’ \\ gvs []
  \\ IF_CASES_TAC \\ gvs []
  >-
   (Cases_on ‘lookup x (update_earliest earliest n v0)’ \\ gvs [min_opt_def]
    \\ imp_res_tac lookup_update_earliest_none
    \\ imp_res_tac lookup_update_earliest_some)
  \\ first_x_assum irule
  \\ Cases_on ‘lookup x (update_earliest earliest n v0)’ \\ gvs []
  >- (imp_res_tac lookup_update_earliest_none \\ gvs [])
  \\ gvs [min_opt_def]
  \\ Cases_on ‘lookup x earliest’ \\ gvs []
  \\ irule LESS_LESS_EQ_TRANS
  \\ last_x_assum $ irule_at $ Pos hd
  \\ rename [‘a ≤ b’]
  \\ pop_assum mp_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘earliest’
  \\ qid_spec_tac ‘b’
  \\ qid_spec_tac ‘a’
  \\ Induct_on ‘v0’ \\ gvs [update_earliest_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum drule
  \\ gvs [lookup_insert] \\ rw []
  \\ gvs [min_opt_def]
QED

Theorem earliest_rel_update_resize_update_earliest:
  earliest_rel fml earliest ⇒
  earliest_rel (update_resize fml NONE (SOME (v,b)) n)
    (update_earliest earliest n (FST v))
Proof
  gvs [update_resize_def] \\ IF_CASES_TAC \\ strip_tac
  \\ irule earliest_rel_lupdate \\ fs []
  \\ irule earliest_rel_append_NONE \\ fs []
QED

Theorem opt_update_inds_earliest_rel:
  earliest_rel fml earliest ∧
  opt_update_inds fml c id inds earliest =
    (fml',inds',earliest',id') ⇒
  earliest_rel fml' earliest'
Proof
  Cases_on`c`>>rw[]>>fs[]>>
  metis_tac[earliest_rel_update_resize_update_earliest,FST,PAIR]
QED
*)

Theorem vimap_rel_check_lstep_list:
  vimap_rel fmlls vimap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_lstep_list lstep b fmlls mindel id zeros =
    SOME (fmlls',x,y,z) ⇒
  vimap_rel fmlls' vimap
Proof
  rw[] \\ fs[vimap_rel_def] \\ rw[] >>
  drule (CONJUNCT1 check_lstep_list_id_del)>>
  drule (CONJUNCT1 check_lstep_list_id_upper)>>
  disch_then drule>>rw[]>>
  `i < id` by (
    gvs[any_el_ALT,AND_IMP_INTRO]>>
    pop_assum kall_tac>>
    pop_assum (qspec_then`i` mp_tac)>>simp[])>>
  first_x_assum drule>>
  simp[any_el_ALT]
QED

Theorem opt_cons_alt:
  opt_cons (v:num) opt =
  case opt of
    NONE => INL (1n,[v])
  | (SOME (INL (n,ls))) =>
    if ind_lim ≤ n
    then
      INR (0n)
    else
      INL (n+1, v::ls)
  | (SOME (INR earliest)) => INR earliest
Proof
  every_case_tac>>rw[opt_cons_def]
QED

Theorem lookup_update_vimap:
  ∀v0 vimap ls x ll0.
    any_el x vimap NONE = SOME ll0 ⇒
    ∃ll.
      any_el x (update_vimap vimap n v0) NONE = SOME ll ∧
      case ll0 of
        INL (n,ls) =>
        (case ll of INL (n',ls') => ∀i. MEM i ls ⇒ MEM i ls'
        | INR _ => T)
      | INR _ => ISR ll
Proof
  Induct \\ gvs [update_vimap_def,FORALL_PROD] \\ rw []
  >-
    (every_case_tac>>simp[])
  \\ `∃ll.
    any_el x
    (update_resize vimap NONE
       (SOME (opt_cons n (any_el p_2 vimap NONE))) p_2) NONE = SOME ll ∧
    case ll0 of
      INL (n,ls) =>
      (case ll of INL (n',ls') => ∀i. MEM i ls ⇒ MEM i ls'
      | INR _ => T)
    | INR _ => ISR ll` by
    (rw[any_el_update_resize]>>gvs[]>>
    every_case_tac>>gvs[opt_cons_alt])
  \\ first_x_assum drule_all
  \\ rw[]>>simp[]
  \\ every_case_tac \\ gvs[]
QED

Theorem lookup_update_vimap':
  any_el x vimap NONE = SOME ll0 ∧
  (case ll0 of INL (n,ls) => MEM i ls | INR _ => T) ⇒
  ∃ll.
    any_el x (update_vimap vimap n v0) NONE = SOME ll ∧
    case ll of
      INL (n,ls) => MEM i ls
    | INR _ => T
Proof
  rw[]>>
  drule  lookup_update_vimap>>
  disch_then(qspecl_then[`n`,`v0`] assume_tac)>>gvs[]>>
  every_case_tac>>gvs[]
QED

Theorem lookup_update_vimap_MEM:
  ∀v0 vimap.
    MEM x (MAP SND v0) ⇒
    ∃ll.
      any_el x (update_vimap vimap i v0) NONE = SOME ll ∧
      case ll of INL (n,ls) => MEM i ls | INR earliest => T
Proof
  Induct \\ gvs [update_vimap_def,FORALL_PROD] \\ reverse (rw [])
  >- (last_x_assum irule \\ fs [])
  \\ irule lookup_update_vimap'
  \\ gvs [any_el_update_resize] \\ rw []
  \\ rw[opt_cons_alt]
  \\ every_case_tac>>gvs[]
QED

Theorem vimap_rel_LUPDATE:
  n < LENGTH fml ∧
  vimap_rel fml vimap ⇒
  vimap_rel (LUPDATE (SOME (v,b)) n fml)
    (update_vimap vimap n (FST v))
Proof
  gvs [vimap_rel_def,EL_LUPDATE]
  \\ rpt strip_tac
  \\ PairCases_on ‘v’ \\ gvs []
  \\ Cases_on ‘i = n’ \\ gvs []
  >- (irule lookup_update_vimap_MEM \\ fs [])
  \\ first_assum drule_all \\ strip_tac \\ gvs []
  \\ irule lookup_update_vimap' \\ fs []
QED

Theorem vimap_rel_nones:
  vimap_rel fml vimap ⇒
  vimap_rel (fml ++ REPLICATE n NONE) vimap
Proof
  rw [vimap_rel_def]
  \\ last_x_assum irule
  \\ Cases_on ‘i < LENGTH fml’ \\ gvs [EL_APPEND1]
  \\ gvs [EL_APPEND2,NOT_LESS]
  \\ gvs [EL_REPLICATE]
QED

Theorem vimap_rel_update_resize_update_vimap:
  vimap_rel fml vimap ⇒
  vimap_rel (update_resize fml NONE (SOME (v,b)) n)
    (update_vimap vimap n (FST v))
Proof
  rewrite_tac [update_resize_def] \\ rw []
  \\ irule vimap_rel_LUPDATE \\ fs []
  \\ irule vimap_rel_nones \\ fs []
QED

Theorem opt_update_inds_vimap_rel:
  vimap_rel fml vimap ∧
  opt_update_inds fml c id inds vimap zeros =
    (fml',inds',vimap',id',zeros') ⇒
  vimap_rel fml' vimap'
Proof
  Cases_on`c`>>rw[]>>fs[]>>
  metis_tac[vimap_rel_update_resize_update_vimap,FST,PAIR]
QED

Theorem fml_rel_check_sstep_list:
  ∀sstep pres ord obj fmlls inds id zeros fmlls' id' inds' zeros' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    vimap_rel fmlls vimap ∧
    vomap_rel obj vomap ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    EVERY (λw. w = 0w) zeros ∧
    check_sstep_list sstep pres ord obj tcb fmlls inds id vimap vomap zeros =
      SOME (fmlls',inds',vimap',id',zeros') ⇒
    ∃fml'.
      check_sstep sstep pres ord obj tcb fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      vimap_rel fmlls' vimap' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      EVERY (λw. w = 0w) zeros' ∧
      id ≤ id'
Proof
  Cases>>rw[]>>fs[check_sstep_list_def,check_sstep_def]
  >- (
    gvs[AllCaseEqs()]>>
    `0 ≤ id` by fs[]>>
    imp_res_tac opt_update_inds_opt_update>>
    drule (CONJUNCT1 fml_rel_check_lstep_list)>>
    rpt(disch_then drule)>>
    rw[]>>simp[]>>
    CONJ_TAC >-
      metis_tac[opt_update_inds_ind_rel,ind_rel_check_lstep_list]>>
    CONJ_TAC >-
      metis_tac[opt_update_inds_vimap_rel,vimap_rel_check_lstep_list]>>
    drule (CONJUNCT1 check_lstep_list_id_upper)>>
    drule opt_update_id_upper>>
    drule opt_update_id>>
    drule (CONJUNCT1 check_lstep_list_id)>>
    drule (CONJUNCT1 check_lstep_list_mindel)>>
    drule_all (CONJUNCT1 check_lstep_list_zeros)>>
    simp[]>>rw[]>>
    Cases_on`c`>>gvs[])
  >- ( (* Red*)
    gvs[AllCaseEqs(),insert_fml_def]>>
    drule_all fml_rel_check_red_list>>
    simp[]>>rw[]
    >-
      metis_tac[fml_rel_update_resize]
    >-
      metis_tac[ind_rel_update_resize_sorted_insert]
    >-
      metis_tac[PAIR,FST,SND,vimap_rel_update_resize_update_vimap]>>
    simp[any_el_update_resize])
QED

Definition MAP_OPT_def:
  (MAP_OPT f [] = []) ∧
  (MAP_OPT f ((i,x)::xs) =
    case f x of
      NONE => MAP_OPT f xs
    | SOME c => (i,c) :: MAP_OPT f xs)
End

Theorem MEM_MAP_OPT:
  MEM (x,y) (MAP_OPT f xs) ⇔
  (∃z. MEM (x,z) xs ∧ f z = SOME y)
Proof
  Induct_on`xs`>>simp[MAP_OPT_def]>>
  Cases>>rw[MAP_OPT_def]>>
  every_case_tac>>simp[]>>
  metis_tac[option_CLAUSES]
QED

Definition do_dom_check_def:
  do_dom_check idopt fml rfml w indcore rinds extra pfs dsubs dindex =
  case idopt of NONE =>
    let goals =
      MAP_OPT (subst_opt w) indcore in
    let (l,r) = extract_scoped_pids pfs LN LN in
    if
      find_scope_1 dindex pfs ∧
      EVERY (λ(id,cs).
              lookup id r ≠ NONE ∨
              check_hash_triv extra cs ∨
              id = dindex)
      (enumerate 0 dsubs)
    then
      let fmlls = revalue F rfml rinds in
      split_goals_hash fmlls extra l goals
    else F
  | SOME cid =>
     check_contradiction_fml_list F fml cid
End

(* maybe memory ... *)
Definition core_fmlls_def:
  (core_fmlls fml [] = []) ∧
  (core_fmlls fml (i::is) =
  case any_el i fml NONE of
    NONE => core_fmlls fml is
  | SOME (v,b) =>
    if b then (i,v)::core_fmlls fml is
    else core_fmlls fml is)
End

(* flag all indices as T *)
Definition core_from_inds_def:
  (core_from_inds fml [] = SOME fml) ∧
  (core_from_inds fml (i::is) =
    case any_el i fml NONE of
      NONE => NONE
    | SOME (x,b) =>
      core_from_inds (update_resize fml NONE (SOME (x,T)) i) is)
End

Theorem any_el_core_from_inds:
  ∀fmlls n fmlls'.
  core_from_inds fmlls inds = SOME fmlls' ⇒
  any_el n fmlls' NONE =
  if MEM n inds then
    OPTION_MAP (λ(x,b). (x,T)) (any_el n fmlls NONE)
  else
    any_el n fmlls NONE
Proof
  Induct_on`inds`>>simp[core_from_inds_def]>>
  strip_tac>>
  ntac 4 strip_tac>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  rw[]>>
  first_x_assum(qspec_then`n`mp_tac)>>
  Cases_on`n=h`>>fs[]
  >- (
    simp[any_el_update_resize]>>
    metis_tac[])>>
  simp[any_el_update_resize]
QED

Definition all_core_list_def:
  (all_core_list fml [] iacc = SOME (REVERSE iacc)) ∧
  (all_core_list fml (i::is) iacc =
    case any_el i fml NONE of
      NONE => all_core_list fml is iacc
    | SOME (v,b) =>
      if b then
        all_core_list fml is (i::iacc)
      else NONE)
End

Definition emp_vec_def:
  emp_vec = INR (Vector [])
End

Definition do_change_check_def:
  do_change_check pfs csubs =
  let (l,r) = extract_pids pfs LN LN in
    EVERY (λ(id,cs).
      lookup id r ≠ NONE ∨
      EXISTS check_contradiction cs
      )
      (enumerate 0 csubs)
End

Definition check_change_obj_list_def:
  check_change_obj_list b fml id obj fc' pfs zeros ⇔
  case obj of NONE => NONE
  | SOME fc =>
    let csubs = change_obj_subgoals (mk_tar_obj b fc) fc' in
    case extract_clauses_list emp_vec T fml csubs pfs [] of
      NONE => NONE
    | SOME cpfs =>
      (case check_subproofs_list cpfs T fml id id zeros of
        NONE => NONE
      | SOME (fml',id',zeros') =>
        let rfml = rollback fml' id id' in
        if do_change_check pfs csubs then
          let fc'' = mk_diff_obj b fc fc' in
          SOME (rfml,fc'',id',zeros')
        else NONE)
End

Definition mk_vomap_def:
  mk_vomap n (f,c) =
  strlit (FOLDL (λacc i. update_resize acc ^zw ^ow i) (REPLICATE n ^zw) (MAP SND f))
End

Theorem resize_acc_bitset_iff:
   ∀ls acc.
   (x <
   LENGTH
     (FOLDL (λacc i. update_resize acc ^zw ^ow i) acc ls) ∧
   EL x (FOLDL (λacc i. update_resize acc ^zw ^ow i) acc ls) ≠ ^zw) ⇔
   (MEM x ls ∨ x < LENGTH acc ∧ EL x acc ≠ ^zw)
Proof
  Induct>>rw[]>>
  rw[update_resize_def,EL_LUPDATE,EL_APPEND_EQN,EL_REPLICATE]>>
  EVERY_CASE_TAC>>gvs[]>>
  Cases_on`x < 2 * h + 1` >>simp[]>>
  DEP_REWRITE_TAC[EL_REPLICATE]>>
  simp[]
QED

Theorem vomap_rel_mk_vomap:
  vomap_rel (SOME fc) (mk_vomap n fc)
Proof
  Cases_on`fc`>>rw[vomap_rel_def,mk_vomap_def]>>
  simp[resize_acc_bitset_iff]>>
  metis_tac[EL_REPLICATE]
QED

Definition check_change_pres_list_def:
  check_change_pres_list b fml id pres v c pfs zeros ⇔
  case pres of NONE => NONE
  | SOME pres =>
    if pres_only c pres v then
    ( let csubs = change_pres_subgoals v c in
      case extract_clauses_list emp_vec T fml csubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs_list cpfs T fml id id zeros of
        NONE => NONE
      | SOME (fml',id',zeros') =>
        let rfml = rollback fml' id id' in
        if do_change_check pfs csubs then
          SOME (rfml,update_pres b v pres,id',zeros')
        else NONE))
    else NONE
End

Definition check_cstep_list_def:
  check_cstep_list cstep fml zeros inds vimap vomap pc =
  case cstep of
    Dom c s pfs idopt =>
    (case pc.ord of
      NONE => NONE
    | SOME spo =>
    if check_pres pc.pres s ∧
      check_fresh_aspo_list c s pc.ord vimap vomap then
    ( let nc = not c in
      let id = pc.id in
      let rinds = reindex fml inds in
      let corels = core_fmlls fml rinds in
      let fml_not_c = update_resize fml NONE (SOME (nc,F)) id in
      let s = mk_subst s in
      let w = subst_fun s in
      let (dsubs,dscopes,dindex) = dom_subgoals spo w c pc.obj in
      case extract_scopes_list dscopes s F fml dsubs pfs of
        NONE => NONE
      | SOME cpfs =>
        (case check_scopes_list cpfs F
          fml_not_c id (id+1) zeros of
          NONE => NONE
        | SOME (fml',id',zeros') =>
          let rfml = rollback fml' id id' in
          if do_dom_check idopt fml' rfml w corels rinds nc pfs dsubs dindex then
            SOME(
              update_resize rfml NONE (SOME (c,pc.tcb)) id',
              zeros',
              sorted_insert id' rinds,
              update_vimap vimap id' (FST c),
              vomap,
              pc with id := id'+1)
          else NONE))
    else NONE)
  | Sstep sstep =>
    (case check_sstep_list sstep pc.pres pc.ord pc.obj pc.tcb
      fml inds pc.id vimap vomap zeros of
      SOME(fml',inds',vimap',id',zeros') =>
        SOME(fml',zeros', inds', vimap', vomap, pc with id := id')
    | NONE => NONE)
  | CheckedDelete n s pfs idopt => (
    if check_tcb_idopt pc.tcb idopt then
      (case lookup_core_only_list T fml n of
        NONE => NONE
      | SOME c =>
          (let nfml = delete_list n fml in
          case check_red_list pc.pres pc.ord pc.obj T pc.tcb
            nfml inds pc.id c s pfs idopt vimap vomap zeros of
            SOME (ncf',inds',vimap',id',zeros') =>
            SOME (ncf',zeros', inds',
              vimap', vomap, pc with <| id := id' |>)
          | NONE => NONE) )
    else NONE)
  | UncheckedDelete ls => (
    (* Either no order or all ids are in core *)
    if ¬pc.tcb ∧ pc.ord = NONE
    then
      SOME (list_delete_list ls fml, zeros, inds,
        vimap, vomap, pc with chk := F)
    else
    case all_core_list fml inds [] of NONE => NONE
    | SOME inds' =>
      SOME (list_delete_list ls fml, zeros, inds',
        vimap, vomap, pc with chk := F))
  | Transfer ls =>
    (case core_from_inds fml ls of NONE => NONE
    | SOME fml' =>
      SOME (fml', zeros, inds, vimap, vomap, pc))
  | StrengthenToCore b =>
    (let inds' = reindex fml inds in
    let pc' = pc with tcb := b in
    if b
    then
      (case core_from_inds fml inds' of NONE => NONE
      | SOME fml' =>
        SOME (fml',zeros,inds', vimap, vomap, pc'))
    else
      SOME (fml,zeros,inds',vimap, vomap, pc'))
  | LoadOrder nn xs =>
    (let inds' = reindex fml inds in
      case ALOOKUP pc.orders nn of NONE => NONE
      | SOME ord' =>
        if LENGTH xs = LENGTH (FST (SND ord')) then
          case core_from_inds fml inds' of NONE => NONE
          | SOME fml' =>
          SOME (fml',zeros, inds',
            vimap,vomap,pc with ord := SOME (ord',xs))
        else NONE)
  | UnloadOrder =>
    (case pc.ord of NONE => NONE
    | SOME spo =>
        SOME (fml, zeros, inds,
          vimap, vomap, pc with ord := NONE))
  | StoreOrder nn vars gspec f pfsr pfst =>
    if check_spec vars gspec
    then
      let aord = mk_aord vars f gspec in
      if check_good_aord aord
      then
        case check_transitivity aord pfst of
          NONE => NONE
        | SOME id =>
          if check_reflexivity aord pfsr id then
            SOME (fml, zeros, inds,
              vimap, vomap,
              pc with orders := (nn ,aord)::pc.orders)
          else NONE
      else
        NONE
    else NONE
  | Obj w mi bopt => (
    let corels = core_fmlls fml inds in
    case check_obj pc.obj w (MAP SND corels) bopt of
      NONE => NONE
    | SOME new =>
      let (bound',dbound') =
        update_bound pc.chk pc.bound pc.dbound new in
      if mi then
        let c = model_improving pc.obj new in
        SOME (
          update_resize fml NONE (SOME (c,T)) pc.id,
          zeros,
          sorted_insert pc.id inds,
          update_vimap vimap pc.id (FST c),
          vomap,
          pc with
          <| id := pc.id+1;
             bound := bound';
             dbound := dbound' |>)
      else
        SOME (fml, zeros, inds, vimap, vomap,
          pc with
          <| bound := bound';
             dbound := dbound' |>))
  | ChangeObj b fc' pfs =>
    (case check_change_obj_list b fml pc.id pc.obj
        fc' pfs zeros of
      NONE => NONE
    | SOME (fml',fc',id',zeros') =>
      SOME (
        fml', zeros', inds,
        vimap, mk_vomap (strlen vomap) fc',
        pc with <| id:=id'; obj:=SOME fc' |>))
  | CheckObj fc' =>
    if check_eq_obj pc.obj fc'
    then SOME (fml, zeros, inds, vimap, vomap, pc)
    else NONE
  | ChangePres b v c pfs =>
    (case check_change_pres_list b fml pc.id pc.pres
        v c pfs zeros of
      NONE => NONE
    | SOME (fml',pres',id',zeros') =>
      SOME (
        fml', zeros', inds,
        vimap, vomap,
        pc with <| id:=id'; pres:=SOME pres' |>))
End

Theorem MEM_core_fmlls:
  MEM (x,z) (core_fmlls fmlls rinds) ⇔
    MEM x rinds ∧
    lookup_core_only_list T fmlls x = SOME z
Proof
  Induct_on`rinds`>>rw[core_fmlls_def]>>
  fs[lookup_core_only_list_def]>>
  eq_tac>>rw[]>>
  every_case_tac>>gvs[]
QED

Theorem ind_rel_lookup_core_only_list:
  ind_rel fmlls rinds ∧
  lookup_core_only_list b fmlls x = SOME z ⇒
  MEM x rinds
Proof
  rw[ind_rel_def,lookup_core_only_list_def]>>
  gvs[AllCaseEqs()]
QED

Theorem core_from_inds_do_transfer:
  ∀l fml fmlls fmlls'.
  fml_rel fml fmlls ∧
  core_from_inds fmlls l = SOME fmlls' ⇒
  ∃fml'.
    do_transfer fml l = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>rw[do_transfer_def,core_from_inds_def]>>
  gvs[AllCaseEqs(),PULL_EXISTS]>>
  `lookup h fml = SOME(x,b)` by
    (fs[fml_rel_def]>>
    metis_tac[])>>
  simp[]>>
  first_x_assum match_mp_tac>>
  first_x_assum (irule_at Any)>>
  match_mp_tac fml_rel_update_resize>>
  metis_tac[]
QED

Triviality all_core_list_mem:
  ∀inds fmlls acc inds'.
    all_core_list fmlls inds acc = SOME inds' ⇒
    MEM x inds' ⇒ MEM x acc ∨ MEM x inds
Proof
  Induct
  \\ fs [all_core_list_def,AllCaseEqs()]
  \\ rw [] \\ res_tac \\ gvs []
QED

Theorem all_core_list_inds:
  ∀inds acc inds'.
  all_core_list fmlls inds acc = SOME inds' ⇒
  let is =
    FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds in
  inds' = REVERSE acc ++ is ∧
  EVERY (λx.
    ∃c. any_el x fmlls NONE = SOME(c,T)) is
Proof
  Induct>>rw[all_core_list_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[]
QED

Theorem fml_rel_all_core:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  all_core_list fmlls inds [] = SOME inds' ⇒
  all_core fml ∧
  ind_rel fmlls inds'
Proof
  rw[]>>drule_all all_core_list_inds>>rw[]
  >- (
    fs[all_core_def,EVERY_MEM,MEM_FILTER,MEM_toAList,FORALL_PROD,fml_rel_def,IS_SOME_EXISTS,PULL_EXISTS,ind_rel_def]>>
    metis_tac[SND,PAIR])>>
  fs[ind_rel_def,MEM_FILTER]
QED

Theorem check_obj_cong:
  set ls = set ls' ⇒
  check_obj obj s ls ob = check_obj obj s ls' ob
Proof
  fs [check_obj_def,EVERY_MEM]
QED

Theorem any_el_rollback:
  (n < id ⇒
    any_el n (rollback fml id id') NONE =
    any_el n fml NONE) ∧
  (n >= id' ⇒
    any_el n (rollback fml id id') NONE =
    any_el n fml NONE)
Proof
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem list_delete_list_length:
  ∀l fmlls. LENGTH (list_delete_list l fmlls) = LENGTH fmlls
Proof
  Induct \\ gvs [list_delete_list_def]
  \\ rw [delete_list_def]
QED

Theorem vimap_rel_list_delete_list:
  ∀l fmlls.
  vimap_rel fmlls vimap ==>
  vimap_rel (list_delete_list l fmlls) vimap
Proof
  gvs [vimap_rel_def]
  \\ rw []
  \\ gvs [list_delete_list_length]
  \\ qsuff_tac ‘EL i fmlls = SOME c’
  >- metis_tac []
  \\ qpat_x_assum ‘i < LENGTH fmlls’ mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ rpt $ pop_assum kall_tac
  \\ qid_spec_tac ‘fmlls’
  \\ qid_spec_tac ‘i’
  \\ qid_spec_tac ‘l’
  \\ Induct
  \\ gvs [list_delete_list_def]
  \\ rw []
  \\ last_x_assum drule
  \\ impl_tac >- rw [delete_list_def]
  \\ rw [delete_list_def]
  \\ gvs [EL_LUPDATE]
QED

Theorem all_core_list_SORTED:
  SORTED $>= inds ∧
  all_core_list fmlls inds [] = SOME inds' ⇒
  SORTED $>= inds'
Proof
  rw[]>>drule all_core_list_inds>>rw[]>>
  match_mp_tac SORTED_FILTER>>
  fs[transitive_def]
QED

Theorem vimap_rel_core_from_inds:
  ∀l fmlls fmlls'.
  vimap_rel fmlls vimap ∧
  core_from_inds fmlls l = SOME fmlls' ⇒
  vimap_rel fmlls' vimap
Proof
  Induct \\ rw[core_from_inds_def] \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ last_x_assum irule
  \\ pop_assum $ irule_at Any
  \\ rw [update_resize_def]
  \\ gvs [vimap_rel_def,EL_LUPDATE,any_el_ALT]
  \\ rw [] \\ gvs []
QED

Theorem fml_rel_check_cstep_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel pc.obj vomap ∧
  (∀n. n ≥ pc.id ⇒ any_el n fmlls NONE = NONE) ∧
  EVERY (λw. w = 0w) zeros ∧
  check_cstep_list cstep fmlls zeros inds vimap vomap pc =
    SOME (fmlls',zeros',inds',vimap',vomap',pc') ⇒
  ∃fml'.
    check_cstep cstep fml pc = SOME (fml', pc') ∧
    fml_rel fml' fmlls' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧
    vomap_rel pc'.obj vomap' ∧
    (∀n. n ≥ pc'.id ⇒ any_el n fmlls' NONE = NONE) ∧
    EVERY (λw. w = 0w) zeros' ∧
    pc.id ≤ pc'.id
Proof
  cheat
  (*
  Cases_on`cstep`>>rw[]
  >- ( (* Dom *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs()]>>
    DEP_REWRITE_TAC[fml_rel_extract_clauses_list]>>
    simp[PULL_EXISTS]>>
    (drule_at Any) fml_rel_check_subproofs_list>>
    disch_then(qspec_then`insert pc.id (not p,F) fml` mp_tac)>>
    impl_tac >- (
      simp[fml_rel_update_resize,any_el_update_resize])>>
    rw[]>>simp[]>>
    drule check_subproofs_list_id>>
    drule check_subproofs_list_id_upper>>
    drule check_subproofs_list_mindel>>
    simp[any_el_update_resize]>>
    ntac 3 strip_tac>>
    gvs[insert_fml_def]>>
    CONJ_TAC>- (
      fs[do_dom_check_def]>>
      every_case_tac>>fs[]
      >- (
        (drule_at Any) split_goals_hash_imp_split_goals>>
        disch_then(qspec_then `mk_core_fml F fml` mp_tac)>>
        impl_tac >- (
          simp[range_mk_core_fml]>>
          match_mp_tac revalue_SUBSET>>
          match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
        match_mp_tac split_goals_same_goals>>
        simp[EXTENSION,FORALL_PROD,MEM_toAList,lookup_map_opt,MEM_MAP_OPT,AllCaseEqs(),lookup_mk_core_fml]>>
        simp[MEM_core_fmlls]>>
        metis_tac[ind_rel_reindex,ind_rel_lookup_core_only_list,fml_rel_lookup_core_only])>>
      metis_tac[fml_rel_check_contradiction_fml] )>>
    CONJ_TAC>- (
      match_mp_tac fml_rel_update_resize>>
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_update_resize_sorted_insert>>
      match_mp_tac ind_rel_rollback_2>>
      fs[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >- (
      match_mp_tac vimap_rel_update_resize_update_vimap>>
      match_mp_tac fml_rel_fml_rel_vimap_rel>>fs[]>>
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    metis_tac[check_subproofs_list_zeros])
  >- ( (* Sstep *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all fml_rel_check_sstep_list>>
    rw[]>>simp[])
  >- ( (* CheckedDelete *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule fml_rel_lookup_core_only>>
    rw[]>>gvs[]>>
    simp[PULL_EXISTS]>>
    qexists_tac`id'`>>
    simp[]>>
    drule_at (Pos last) fml_rel_check_red_list>>
    disch_then match_mp_tac>>
    simp[]>>
    CONJ_TAC >- (
      drule fml_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>
      simp[list_delete_list_def])>>
    CONJ_TAC >- (
      drule ind_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>
      simp[list_delete_list_def])>>
    CONJ_TAC >- (
      drule vimap_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>
      simp[list_delete_list_def])>>
    metis_tac[any_el_list_delete_list,list_delete_list_def])
  >- ( (* UncheckedDelete *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]
    >- (
      CONJ_TAC >-
        metis_tac[fml_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[ind_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[vimap_rel_list_delete_list]>>
      simp[any_el_list_delete_list])
    >- (
      drule_all fml_rel_all_core>>strip_tac>>
      simp[]>>
      CONJ_TAC >-
        metis_tac[fml_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[ind_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[vimap_rel_list_delete_list]>>
      simp[any_el_list_delete_list]))
  >- ( (* Transfer *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all core_from_inds_do_transfer>>
    drule any_el_core_from_inds>>
    strip_tac>>fs[]>>
    fs[ind_rel_def]>>
    rw[]>>
    `vimap_rel fmlls' vimap` by
      metis_tac[vimap_rel_core_from_inds]>>
    metis_tac[IS_SOME_EXISTS,option_CLAUSES])
  >- ( (* StrengthenToCore *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all ind_rel_reindex
    >- (
      drule any_el_core_from_inds>>
      rw[]
      >- (
        simp[fml_rel_def,lookup_map]>>
        fs[ind_rel_def]>>rw[]
        >-
          metis_tac[fml_rel_def] >>
        `any_el x fmlls NONE = NONE` by
          metis_tac[IS_SOME_EXISTS,option_CLAUSES]>>
        simp[]>>
        metis_tac[fml_rel_def])
      >- (
        fs[ind_rel_def]>>
        rw[]>>
        metis_tac[IS_SOME_EXISTS,option_CLAUSES])
      >- (
        fs[vimap_rel_def]>>rw[]>>
        first_x_assum match_mp_tac>>
        first_x_assum(qspec_then`i` mp_tac)>>
        rw[any_el_ALT]>>gvs[]>>
        fs[MEM_MAP]
        >- (
          pairarg_tac>>fs[]>>
          metis_tac[FST,PAIR,SND])>>
        metis_tac[FST,PAIR,SND])
        )
    >-
      fs[])
  >- ( (* LoadOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all ind_rel_reindex>>
    drule any_el_core_from_inds>>
    strip_tac>>fs[]>>
    strip_tac>>fs[]>>
    CONJ_TAC >- (
      simp[fml_rel_def,lookup_map]>>
      fs[ind_rel_def]>>rw[]
      >-
        metis_tac[fml_rel_def] >>
      `any_el x fmlls NONE = NONE` by
        metis_tac[IS_SOME_EXISTS,option_CLAUSES]>>
      simp[]>>
      metis_tac[fml_rel_def])>>
    CONJ_TAC >- (
      fs[ind_rel_def]>>
      rw[]>>
      metis_tac[IS_SOME_EXISTS,option_CLAUSES])>>
    metis_tac[vimap_rel_core_from_inds])
  >- ( (* UnloadOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >- ( (* StoreOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >- ( (* Obj *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    rw[PULL_EXISTS]>>
    `set (MAP SND (core_fmlls fmlls inds)) =
      set (MAP SND (toAList (mk_core_fml T fml)))` by (
      rw[EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,MEM_core_fmlls]>>
      simp[lookup_mk_core_fml]>>
      metis_tac[ind_rel_lookup_core_only_list,fml_rel_lookup_core_only])>>
    drule check_obj_cong>>rw[]>>fs[]>>
    pairarg_tac>>gvs[]>>
    rw[]>>gvs[]
    >- metis_tac[fml_rel_update_resize]
    >- metis_tac[ind_rel_update_resize_sorted_insert]
    >- metis_tac[vimap_rel_update_resize_update_vimap]>>
    simp[any_el_update_resize])
  >- ( (* ChangeObj *)
    fs[check_cstep_def,check_cstep_list_def]>>
    gvs[AllCaseEqs(),check_change_obj_list_def,check_change_obj_def]>>
    qpat_x_assum`_ = SOME cpfs` mp_tac>>
    DEP_REWRITE_TAC [GSYM fml_rel_extract_clauses_list]>>
    simp[]>>
    `subst_fun emp_vec = (λx:num. NONE)` by
      (simp[FUN_EQ_THM,subst_fun_def,emp_vec_def]>>
      EVAL_TAC>>rw[])>>
    strip_tac>>
    rfs[]>>
    `pc.id ≤ pc.id` by fs[]>>
    drule_all fml_rel_check_subproofs_list>>
    fs[do_change_check_def]>>
    pairarg_tac>>fs[]>>
    strip_tac>>simp[]>>
    drule check_subproofs_list_id>>
    drule check_subproofs_list_id_upper>>
    drule check_subproofs_list_mindel>>
    ntac 3 strip_tac>>
    CONJ_ASM1_TAC >- (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >-
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    CONJ_TAC >-
      metis_tac[vomap_rel_mk_vomap]>>
    simp[any_el_rollback]>>
    metis_tac[check_subproofs_list_zeros])
  >- ( (* CheckObj *)
    fs[check_cstep_def,check_cstep_list_def]
  )
  >- ( (* ChangePres *)
    fs[check_cstep_def,check_cstep_list_def]>>
    gvs[AllCaseEqs(),check_change_pres_list_def,check_change_pres_def]>>
    qpat_x_assum`_ = SOME cpfs` mp_tac>>
    DEP_REWRITE_TAC [GSYM fml_rel_extract_clauses_list]>>
    simp[]>>
    `subst_fun emp_vec = (λx:num. NONE)` by
      (simp[FUN_EQ_THM,subst_fun_def,emp_vec_def]>>
      EVAL_TAC>>rw[])>>
    strip_tac>>
    rfs[]>>
    `pc.id ≤ pc.id` by fs[]>>
    drule_all fml_rel_check_subproofs_list>>
    fs[do_change_check_def]>>
    pairarg_tac>>fs[]>>
    strip_tac>>simp[]>>
    drule check_subproofs_list_id>>
    drule check_subproofs_list_id_upper>>
    drule check_subproofs_list_mindel>>
    ntac 3 strip_tac>>
    CONJ_ASM1_TAC >- (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >-
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    simp[any_el_rollback]>>
    metis_tac[check_subproofs_list_zeros]) *)
QED

Definition check_csteps_list_def:
  (check_csteps_list [] fml zeros inds vimap vomap pc =
    SOME (fml, zeros, inds, vimap, vomap, pc)) ∧
  (check_csteps_list (c::cs) fml zeros inds vimap vomap pc =
    case check_cstep_list c fml zeros inds vimap vomap pc of
      NONE => NONE
    | SOME(fml', zeros', inds', vimap', vomap', pc') =>
      check_csteps_list cs fml' zeros' inds' vimap' vomap' pc')
End

Theorem fml_rel_check_csteps_list:
  ∀csteps fml fmlls zeros inds vimap vomap pc
    fmlls' zeros' inds' vimap' vomap' pc'.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel pc.obj vomap ∧
  (∀n. n ≥ pc.id ⇒ any_el n fmlls NONE = NONE) ∧
  EVERY (λw. w = 0w) zeros ∧
  check_csteps_list csteps fmlls zeros inds vimap vomap pc =
    SOME (fmlls', zeros', inds', vimap', vomap', pc') ⇒
  ∃fml'.
    check_csteps csteps fml pc = SOME (fml', pc') ∧
    fml_rel fml' fmlls' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧
    vomap_rel pc'.obj vomap' ∧
    (∀n. n ≥ pc'.id ⇒ any_el n fmlls' NONE = NONE) ∧
    EVERY (λw. w = 0w) zeros' ∧
    pc.id ≤ pc'.id
Proof
  Induct>>simp[]
  >- (
    rw[check_csteps_list_def,check_csteps_def]>>
    metis_tac[])>>
  rw[]>>
  gvs[check_csteps_list_def,check_csteps_def,AllCaseEqs()]>>
  drule_all fml_rel_check_cstep_list>>
  rw[]>>simp[]>>
  first_x_assum drule_all>>
  rw[]>>simp[]
QED

Definition check_implies_fml_list_def:
  check_implies_fml_list fml n c =
  (case any_el n fml NONE of
      NONE => F
    | SOME (ci,_) =>
      check_triv2 ci c)
End

Definition check_hconcl_list_def:
  (check_hconcl_list fml obj fml' obj' bound' dbound'
    HNoConcl = T) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound'
    (HDSat wopt) =
    case wopt of
      NONE =>
      bound' ≠ NONE
    | SOME wm =>
      check_obj obj wm fml NONE ≠ NONE) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound'
    (HDUnsat n) =
    (dbound' = NONE ∧
      check_contradiction_fml_list F fml' n)) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound'
    (HOBounds lbi ubi n wopt) =
    (
    (opt_le lbi dbound' ∧
    case lbi of
      NONE => check_contradiction_fml_list F fml' n
    | SOME lb => check_implies_fml_list fml' n (lower_bound obj' lb)) ∧
    (
    case wopt of
      NONE => opt_le bound' ubi
    | SOME wm =>
      opt_le (check_obj obj wm fml NONE) ubi)))
End

Theorem fml_rel_check_implies_fml:
  fml_rel fml fmlls ∧
  check_implies_fml_list fmlls n c ⇒
  check_implies_fml fml n c
Proof
  rw[check_implies_fml_list_def,check_implies_fml_def,fml_rel_def]>>
  every_case_tac>>fs[]>>
  metis_tac[option_CLAUSES,PAIR,FST]
QED

Theorem fml_rel_check_hconcl_list:
  fml_rel fml' fmlls' ∧
  check_hconcl_list fml obj fmlls'
    obj' bound' dbound' hconcl ⇒
  check_hconcl fml obj fml'
    obj' bound' dbound' hconcl
Proof
  Cases_on`hconcl`>>
  fs[check_hconcl_def,check_hconcl_list_def]
  >-
    metis_tac[fml_rel_check_contradiction_fml]>>
  rw[]>>every_case_tac>>fs[]>>
  metis_tac[fml_rel_check_contradiction_fml,fml_rel_check_implies_fml]
QED

Theorem all_distinct_map_fst_rev:
  ALL_DISTINCT (MAP FST ls) ⇔ ALL_DISTINCT (MAP FST (REVERSE ls))
Proof
  fs[MAP_REVERSE]
QED

Theorem LENGTH_FOLDR_update_resize2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME (v,b)) i) x) (REPLICATE n NONE) ll)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once update_resize_def]
  >- (
    first_x_assum drule>>
    simp[])>>
  first_x_assum drule>>simp[]
QED

Theorem FOLDL_update_resize_lookup:
  ∀ls.
  ALL_DISTINCT (MAP FST ls) ⇒
  ∀x.
  x < LENGTH (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,b)) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,b)) i) (REPLICATE n NONE) ls)
  =
  OPTION_MAP (λv. (v,b)) (ALOOKUP ls x)
Proof
  simp[Once (GSYM EVERY_REVERSE), Once (GSYM MAP_REVERSE)]>>
  simp[FOLDL_FOLDR_REVERSE]>>
  simp[GSYM alookup_distinct_reverse]>>
  simp[Once all_distinct_map_fst_rev]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE ls`>>
  pop_assum kall_tac>>
  Induct_on`ll`>-
    simp[EL_REPLICATE]>>
  simp[FORALL_PROD]>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once update_resize_def]>>
  strip_tac>>
  simp[Once update_resize_def]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[EL_LUPDATE]>>
  IF_CASES_TAC >> simp[]>>
  simp[EL_APPEND_EQN]>>rw[]>>
  simp[EL_REPLICATE]>>
  CCONTR_TAC>>fs[]>>
  Cases_on`ALOOKUP ll x`>>fs[]>>
  drule ALOOKUP_MEM>>
  strip_tac>>
  drule LENGTH_FOLDR_update_resize2>>
  simp[]>>
  metis_tac[]
QED

Theorem fml_rel_FOLDL_update_resize:
  fml_rel (build_fml b k fml)
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,b)) i) (REPLICATE n NONE) (enumerate k fml))
Proof
  rw[fml_rel_def]>>
  simp[any_el_ALT]>>
  reverse IF_CASES_TAC
  >- (
    fs[lookup_build_fml]>>
    CCONTR_TAC>>fs[]>>
    `MEM x (MAP FST (enumerate k fml))` by
      (fs[MAP_FST_enumerate,MEM_GENLIST]>>
      intLib.ARITH_TAC)>>
    fs[MEM_MAP]>>
    fs[FOLDL_FOLDR_REVERSE]>>
    `MEM y (REVERSE (enumerate k fml))` by
      fs[MEM_REVERSE]>>
    drule LENGTH_FOLDR_update_resize2>>
    simp[]>>
    metis_tac[]) >>
  DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
  simp[]>>
  CONJ_TAC >-
    simp[ALL_DISTINCT_MAP_FST_enumerate]>>
  simp[lookup_build_fml,ALOOKUP_enumerate]>>
  rw[]
QED

Theorem ind_rel_FOLDL_update_resize:
  ind_rel
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,b)) i) (REPLICATE n NONE) (enumerate k fml))
  (REVERSE (MAP FST (enumerate k fml)))
Proof
  simp[ind_rel_def,FOLDL_FOLDR_REVERSE]>>
  `∀z. MEM z (MAP FST (enumerate k fml)) ⇔ MEM z (MAP FST (REVERSE (enumerate k fml)))` by
    simp[MEM_MAP]>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`MAP FST ls`>>
  rpt(pop_assum kall_tac)>>
  Induct_on`ls`>>rw[]
  >- (
    simp[any_el_ALT]>>
    metis_tac[EL_REPLICATE])>>
  Cases_on`h`>>fs[]>>
  fs[IS_SOME_EXISTS]>>
  pop_assum mp_tac>>
  simp[Once update_resize_def]>>
  IF_CASES_TAC>>fs[]
  >- (
    fs[any_el_ALT,EL_LUPDATE]>>
    IF_CASES_TAC>>simp[]) >>
  fs[any_el_ALT,EL_LUPDATE]>>
  IF_CASES_TAC>>simp[EL_APPEND_EQN]>>
  IF_CASES_TAC>>simp[]>>
  rw[]>>
  first_x_assum match_mp_tac>>
  gs[EL_REPLICATE]
QED

Theorem vimap_rel_FOLDL_update_resize:
  ∀xs ls t.
  vimap_rel ls t ⇒
  vimap_rel
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,b)) i) ls xs)
  (FOLDL (λacc (i,v). update_vimap acc i (FST v)) t xs)
Proof
  Induct>>rw[]>>
  first_x_assum match_mp_tac>>
  pairarg_tac>>gvs[]>>
  match_mp_tac vimap_rel_update_resize_update_vimap>>
  fs[]
QED

Theorem SORTED_REVERSE_enumerate:
  ∀(ls:'a list) k.
  SORTED $>= (REVERSE (MAP FST (enumerate k ls)))
Proof
  Induct>>rw[miscTheory.enumerate_def]>>
  match_mp_tac SORTED_APPEND_IMP>>
  rw[transitive_def]>>
  fs[MAP_FST_enumerate,MEM_GENLIST]
QED

Definition mk_vomap_opt_def:
  (mk_vomap_opt NONE = strlit "") ∧
  (mk_vomap_opt (SOME fc) = mk_vomap (LENGTH (FST fc)) fc)
End

Definition mk_vimap_def:
  mk_vimap ls efml =
    FOLDL (λacc (i,v). update_vimap acc i (FST v)) ls efml
End

Theorem check_csteps_list_concl:
  check_csteps_list cs
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE m NONE) (enumerate 1 fml))
    (REPLICATE z 0w)
    (REVERSE (MAP FST (enumerate 1 fml)))
    (mk_vimap (REPLICATE k NONE) (enumerate 1 fml))
    (mk_vomap_opt obj)
    (init_conf (LENGTH fml + 1) chk pres obj) =
    SOME(fmlls',zeros',inds',vimap',vomap',pc') ∧
  check_hconcl_list fml obj fmlls'
    pc'.obj pc'.bound pc'.dbound hconcl ⇒
  sem_concl (set fml) obj (hconcl_concl hconcl)
Proof
  rw[]>>
  qmatch_asmsub_abbrev_tac`check_csteps_list cs fmlls zeros
    inds vimap vomap pc = _`>>
  `fml_rel (build_fml T 1 fml) fmlls` by
    simp[Abbr`fmlls`,fml_rel_FOLDL_update_resize]>>
  `ind_rel fmlls inds` by (
    unabbrev_all_tac>>
    simp[ind_rel_FOLDL_update_resize])>>
  `SORTED $>= inds` by
    (unabbrev_all_tac>>fs[SORTED_REVERSE_enumerate])>>
  `vimap_rel fmlls vimap` by (
    unabbrev_all_tac>>
    rw[mk_vimap_def]>>
    irule vimap_rel_FOLDL_update_resize>>
    rw[vimap_rel_def]>>
    gvs[EL_REPLICATE])>>
  `vomap_rel pc.obj vomap` by (
    unabbrev_all_tac>>
    simp[init_conf_def]>>
    Cases_on`obj`>-
      EVAL_TAC>>
    metis_tac[vomap_rel_mk_vomap,mk_vomap_opt_def])>>
  `∀n. n ≥ pc.id ⇒ any_el n fmlls NONE = NONE` by (
    rw[Abbr`pc`,Abbr`fmlls`,any_el_ALT,init_conf_def]>>
    DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
    simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])>>
  `EVERY (λw. w = 0w) zeros` by
    simp[Abbr`zeros`]>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  `id_ok (build_fml T 1 fml) pc.id` by
    fs[Abbr`pc`,init_conf_def,id_ok_def,domain_build_fml]>>
  `all_core (build_fml T 1 fml)` by
    fs[all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD,lookup_build_fml]>>
  drule check_csteps_check_hconcl>>
  rpt(disch_then drule)>>
  disch_then match_mp_tac>>simp[core_only_fml_build_fml]>>
  drule_all fml_rel_check_hconcl_list>>
  fs[Abbr`pc`,init_conf_def]>>
  metis_tac[]
QED

Definition fml_include_list_def:
  fml_include_list fml fml' =
  let hs = mk_hashset fml (REPLICATE splim []) in
  EVERY (λc. in_hashset c hs) fml'
End

Theorem fml_include_list_fml_include:
  fml_include_list fml fml' ⇒
  npbc_check$fml_include fml fml'
Proof
  rw[fml_include_list_def,fml_include_def,EVERY_MEM]>>
  first_x_assum drule>>
  rw[]>>
  drule in_hashset_mk_hashset>>
  simp[in_hashset_def]>>
  DEP_REWRITE_TAC[EL_REPLICATE]>>
  Cases_on`c`>>
  simp[hash_constraint_def,mem_constraint_thm]>>
  match_mp_tac MOD_LESS>>
  EVAL_TAC
QED

Definition check_output_list_def:
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' NoOutput = T) ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Derivable =
    let cls = MAP SND (core_fmlls fml inds) in
      dbound = NONE ∧ fml_include_list cls fml') ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Equisatisfiable =
    let cls = MAP SND (core_fmlls fml inds) in
      dbound = NONE ∧ bound = NONE ∧
      chk ∧
      fml_include_list cls fml' ∧
      fml_include_list fml' cls) ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Equioptimal =
    let cls = MAP SND (core_fmlls fml inds) in
      chk ∧ opt_le bound dbound ∧
      fml_include_list cls fml' ∧
      fml_include_list fml' cls ∧
      opt_eq_obj obj obj') ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Equisolvable =
    let cls = MAP SND (core_fmlls fml inds) in
      chk ∧ opt_le bound dbound ∧
      fml_include_list cls fml' ∧
      fml_include_list fml' cls ∧
      opt_eq_obj_opt obj obj' ∧
      opt_eq_pres pres pres')
End

Theorem fml_include_set:
  set (ls:'a list) = set ls' ∧
  set rs = set rs'
  ⇒
  fml_include ls rs = fml_include ls' rs'
Proof
  rw[fml_include_def,EVERY_MEM]
QED

Theorem fml_rel_check_output_list:
  fml_rel fml' fmlls' ∧
  ind_rel fmlls' inds' ∧
  check_output_list fmlls' inds' pres obj bound dbound chk fmlt prest objt output ⇒
  check_output fml' pres obj bound dbound chk fmlt prest objt output
Proof
  rw[]>>
  `set (MAP SND (core_fmlls fmlls' inds')) =
   set (MAP SND (toAList (mk_core_fml T fml')))` by (
   rw[EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,MEM_core_fmlls]>>
   simp[lookup_mk_core_fml]>>
   metis_tac[ind_rel_lookup_core_only_list,fml_rel_lookup_core_only])>>
  Cases_on`output`>>
  fs[check_output_list_def,check_output_def]>>rw[]>>
  imp_res_tac fml_include_list_fml_include>>fs[]>>
  metis_tac[fml_include_set]
QED

Theorem check_csteps_list_output:
  check_csteps_list cs
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE m NONE) (enumerate 1 fml))
    (REPLICATE z 0w)
    (REVERSE (MAP FST (enumerate 1 fml)))
    (mk_vimap (REPLICATE k NONE) (enumerate 1 fml))
    (mk_vomap_opt obj)
    (init_conf (LENGTH fml + 1) chk pres obj) =
    SOME(fmlls',zeros',inds',vimap',vomap',pc') ∧
  check_output_list fmlls' inds'
    pc'.pres pc'.obj pc'.bound pc'.dbound pc'.chk fmlt prest objt output ⇒
  sem_output (set fml) obj (pres_set_spt pres) pc'.bound (set fmlt) objt (pres_set_spt prest) output
Proof
  rw[]>>
  qmatch_asmsub_abbrev_tac`check_csteps_list cs fmlls zeros
    inds vimap vomap pc = _`>>
  `fml_rel (build_fml T 1 fml) fmlls` by
    simp[Abbr`fmlls`,fml_rel_FOLDL_update_resize]>>
  `ind_rel fmlls inds` by (
    unabbrev_all_tac>>
    simp[ind_rel_FOLDL_update_resize])>>
  `SORTED $>= inds` by
    (unabbrev_all_tac>>fs[SORTED_REVERSE_enumerate])>>
  `vimap_rel fmlls vimap` by (
    unabbrev_all_tac>>
    rw[mk_vimap_def]>>
    irule vimap_rel_FOLDL_update_resize>>
    rw[vimap_rel_def]>>
    gvs[EL_REPLICATE])>>
  `vomap_rel pc.obj vomap` by (
    unabbrev_all_tac>>
    simp[init_conf_def]>>
    Cases_on`obj`>-
      EVAL_TAC>>
    metis_tac[vomap_rel_mk_vomap,mk_vomap_opt_def])>>
  `∀n. n ≥ pc.id ⇒ any_el n fmlls NONE = NONE` by (
    rw[Abbr`pc`,Abbr`fmlls`,any_el_ALT,init_conf_def]>>
    DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
    simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])>>
  `EVERY (λw. w = 0w) zeros` by
    simp[Abbr`zeros`]>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  `id_ok (build_fml T 1 fml) pc.id` by
    fs[Abbr`pc`,init_conf_def,id_ok_def,domain_build_fml]>>
  `all_core (build_fml T 1 fml)` by
    fs[all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD,lookup_build_fml]>>
  drule check_csteps_check_output>>
  fs[Abbr`pc`]>>
  gvs[init_conf_def]>>
  rpt(disch_then drule)>>
  simp[core_only_fml_build_fml]>>
  disch_then match_mp_tac>>
  drule_all fml_rel_check_output_list>>
  metis_tac[]
QED

val _ = export_theory();
