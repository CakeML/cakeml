(*
  Refine PB proof checker to use arrays
*)
open preamble basis pb_checkTheory;

val _ = new_theory "pb_list"

Definition check_cutting_list_def:
  (check_cutting_list (fml: npbc option list) (Id n) =
    any_el n fml NONE) ∧
  (check_cutting_list fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting_list fml c1) (check_cutting_list fml c2)) ∧
  (check_cutting_list fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting_list fml c)) ∧
  (check_cutting_list fml (Div c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. divide c k) (check_cutting_list fml c)
    else NONE) ∧
  (check_cutting_list fml (Sat c) =
    OPTION_MAP saturate (check_cutting_list fml c)) ∧
  (check_cutting_list fml (Lit l) = SOME (PBC [(1,l)] 0)) ∧
  (check_cutting_list fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting_list fml c))
End

(* Copied from LPR *)
val list_delete_list_def = Define`
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))`

(* ensure list remains ≥ sorted -- common case: will always just insert at the front *)
val sorted_insert_def = Define`
  (sorted_insert (x:num) [] = [x]) ∧
  (sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys
    else y::(sorted_insert x ys))`

(* Rollback formula to starting ID *)
Definition rollback_def:
  rollback fml id_start id_end =
  list_delete_list
    (MAP ($+id_start) (COUNT_LIST (id_end-id_start))) fml
End

(*
  fml is represented by an array [...], where fml[i] is the i-th constraint
    when fml[i]=NONE (or i is out of range)
    that means there is no constraint at that index
  inds is a list of indexes (sorted in descending order)
  mindel is the minimum index allowed for deletion

  Return NONE for Failure
  T for Unsat
  F for Cont
*)
Definition check_pbpstep_list_def:
  (check_pbpstep_list (step:pbpstep) (fml: npbc option list) (inds:num list) (mindel:num) (id:num) =
  case step of
    Contradiction n =>
      (case any_el n fml NONE of
        NONE => (fml, NONE)
      | SOME c =>
        if check_contradiction c
        then (fml, SOME (T,id, inds))
        else (fml, NONE))
  | Check n c =>
    if any_el n fml NONE = SOME c
    then (fml, SOME (F, id, inds))
    else (fml, NONE)
  | NoOp => (fml, SOME (F, id, inds))
  | Delete ls =>
      if EVERY ($<= mindel) ls then
        (list_delete_list ls fml, SOME(F, id, inds))
      else
        (fml,NONE)
  | Cutting constr =>
    (case check_cutting_list fml constr of
      NONE => (fml,NONE)
    | SOME c =>
      (update_resize fml NONE (SOME c) id, SOME(F, (id+1), sorted_insert id inds)))
  | Con c pf =>
    let fml_not_c = update_resize fml NONE (SOME (not c)) id in
    (case check_pbpsteps_list pf fml_not_c inds id (id+1) of
      (fml', SOME (T, id' ,inds')) =>
        let rfml = rollback fml' id id' in
        (* TODO: rfml may be a subset of fml because there might have been deletions *)
        (update_resize rfml NONE (SOME c) id', SOME(F, (id'+1), sorted_insert id' inds'))
    | (fml',_) => (fml',NONE))
  | _ => (fml,NONE)) ∧
  (check_pbpsteps_list [] fml inds mindel id = (fml, SOME (F, id, inds))) ∧
  (check_pbpsteps_list (step::steps) fml inds mindel id =
    case check_pbpstep_list step fml inds mindel id of
      (fml', SOME (F, id', inds')) =>
        check_pbpsteps_list steps fml' inds' mindel id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (pbpstep_size o FST)
    (list_size pbpstep_size o FST))’
  \\ fs [pbpstep_size_eq] \\ rw []
End

(* TODO:
  | Red c s pfs =>
    (let fml_not_c = insert id (not c) fml in
      let w = subst_fun s in
      case extract_clauses w c fml pfs [] of
        NONE => Fail
      | SOME cpfs =>
      (case check_redundancy cpfs fml_not_c (id+1) of
        Cont fml' id' =>
        let goals = MAP FST (toAList (map_opt (subst_opt w) fml)) in
        let pids = MAP FST pfs in (* optimize and change later *)
          if MEM (SOME (INR ())) pids ∧
            EVERY (λid. MEM (SOME (INL id)) pids) goals then
            Cont (insert id' c fml) (id'+1)
          else Fail
      | _ => Fail) )) ∧
  (check_redundancy [] fml id = Cont fml id) ∧
  (check_redundancy ((copt,pf)::pfs) fml id =
    case copt of
      NONE => (* no clause given *)
      (if ~EVERY is_pol_con pf then Fail else
      case check_pbpsteps_list pf fml id of
        Cont fml' id' => check_redundancy pfs fml' id'
      | res => Fail)
    | SOME c =>
      let cfml = insert id (not c) fml in
      case check_pbpsteps_list pf cfml (id+1) of
        Unsat id' => check_redundancy pfs fml id'
      | res => Fail)
Termination
  WF_REL_TAC ‘measure (
    sum_size (pbpstep_list_size o FST)
    (sum_size (list_size pbpstep_list_size o FST)
    (list_size (list_size pbpstep_list_size) o MAP SND o FST)))’
  \\ fs [fetch "-" "pbpstep_list_size_eq"] \\ rw []
  >- (EVAL_TAC>>rw[])
  >- (EVAL_TAC>>rw[])
  >- (EVAL_TAC>>rw[])
  >- (EVAL_TAC>>rw[])
  \\ drule extract_clauses_MAP_SND
  \\ simp[] \\ rw[]
  \\ qmatch_goalsub_abbrev_tac`ls1 < _ + (ls2 + _)`
  \\ `ls1 <= ls2` by (
    unabbrev_all_tac
    \\ rpt (pop_assum kall_tac)
    \\ Induct_on`pfs` \\ simp[FORALL_PROD]
    \\ rw[] \\ EVAL_TAC
    \\ fs[])
  \\ simp[]
End
 *)

(* prove that check_pbpstep_list implements check_pbpstep *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x. any_el x fmlls NONE = lookup x fml
End

Theorem fml_rel_check_cutting:
  ∀p.
  fml_rel fml fmlls ⇒
  check_cutting_list fmlls p = check_cutting fml p
Proof
  Induct>>rw[check_cutting_list_def,check_cutting_def]>>
  fs[fml_rel_def]
QED

Theorem any_el_list_delete_list:
  ∀ls n fml.
  any_el n (list_delete_list ls fml) NONE =
  if MEM n ls then NONE else any_el n fml NONE
Proof
  Induct>>rw[list_delete_list_def]>>
  gs[any_el_ALT,EL_LUPDATE]
QED

Theorem fml_rel_list_delete_list:
  ∀ls fml fmlls.
  fml_rel fml fmlls ⇒
  fml_rel (FOLDL (λa b. delete b a) fml ls) (list_delete_list ls fmlls)
Proof
  Induct>>rw[list_delete_list_def]>>
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

Theorem any_el_update_resize:
  any_el n (update_resize fml NONE v id) NONE =
  if n = id then v else any_el n fml NONE
Proof
  rw[update_resize_def,any_el_ALT,EL_LUPDATE]>>fs[]>>
  fs[EL_APPEND_EQN,EL_REPLICATE]>>
  every_case_tac>>fs[]
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert id c fml) (update_resize fmlls NONE (SOME c) id)
Proof
  rw[fml_rel_def,lookup_insert,any_el_update_resize]
QED

Theorem check_pbpstep_list_id:
  (∀step fmlls inds mindel id fmlls' b id' inds'.
  check_pbpstep_list step fmlls inds mindel id = (fmlls', SOME (b,id',inds')) ⇒ id ≤ id') ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds'.
  check_pbpsteps_list steps fmlls inds mindel id = (fmlls', SOME (b,id',inds')) ⇒ id ≤ id')
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >-
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >-
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- (
    pop_assum mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    simp[]>>
    rw[]>>
    first_x_assum drule>>
    disch_then drule>>
    fs[])
QED

Theorem check_pbpstep_list_id_upper:
  (∀step fmlls inds mindel id fmlls' b id' inds'.
  check_pbpstep_list step fmlls inds mindel id = (fmlls', SOME (b,id',inds')) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds'.
  check_pbpsteps_list steps fmlls inds mindel id = (fmlls', SOME (b,id',inds')) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE))
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
    >-
      simp[any_el_list_delete_list]
    >-
      simp[any_el_update_resize]
    >-
      simp[any_el_update_resize,rollback_def,any_el_list_delete_list])
  >-
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- (
    qpat_x_assum`_=(_,_)`mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule
    >- (
      disch_then match_mp_tac>>
      fs[] ) >>
    first_x_assum drule>>
    disch_then drule>>
    rw[])
QED

Theorem check_pbpstep_list_mindel:
  (∀step fmlls inds mindel id fmlls' res n.
  check_pbpstep_list step fmlls inds mindel id = (fmlls', res) ∧
  mindel ≤ id ∧
  n < mindel ⇒ any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps fmlls inds mindel id fmlls' res n.
  check_pbpsteps_list steps fmlls inds mindel id = (fmlls', res) ∧
  mindel ≤ id ∧
  n < mindel ⇒ any_el n fmlls NONE = any_el n fmlls' NONE)
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
    >- (
      rw[any_el_list_delete_list]>>fs[EVERY_MEM]>>
      first_x_assum drule>>fs[])
    >-
      rw[any_el_update_resize]
    >- (
      first_x_assum(qspec_then`n`mp_tac)>>
      simp[any_el_update_resize])
    >- (
      first_x_assum(qspec_then`n`mp_tac)>>
      simp[any_el_update_resize]>>
      drule (el 2 (CONJUNCTS check_pbpstep_list_id))>>
      simp[rollback_def,any_el_list_delete_list,MEM_MAP])
    >- (
      first_x_assum(qspec_then`n`mp_tac)>>
      simp[any_el_update_resize]))
  >-
    fs[check_pbpstep_list_def]
  >- (
    qpat_x_assum`_=(_,res)` mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    simp[]>>
    rw[]>>
    first_x_assum drule>>
    first_x_assum drule>>
    disch_then drule>>
    disch_then (qspec_then`n`mp_tac)>>
    drule (el 1 (CONJUNCTS check_pbpstep_list_id))>>
    simp[])
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

Theorem fml_rel_check_pbpstep_list:
  (∀step fmlls inds mindel id fmlls' b id' inds' fml.
  fml_rel fml fmlls ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_pbpstep_list step fmlls inds mindel id = (fmlls', SOME (b,id',inds')) ⇒
  if b then check_pbpstep step fml id = Unsat id'
  else ∃fml'. check_pbpstep step fml id = Cont fml' id' ∧ fml_rel fml' fmlls') ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds' fml.
  fml_rel fml fmlls ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_pbpsteps_list steps fmlls inds mindel id = (fmlls', SOME (b,id',inds')) ⇒
  if b then check_pbpsteps steps fml id = Unsat id'
  else ∃fml'. check_pbpsteps steps fml id = Cont fml' id' ∧ fml_rel fml' fmlls')
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
    >-
      metis_tac[fml_rel_def]
    >- (* Deletion *)
      metis_tac[fml_rel_list_delete_list]
    >- ((* Cutting *)
      drule fml_rel_check_cutting>>
      disch_then(qspec_then`constr` assume_tac)>>fs[]>>
      metis_tac[fml_rel_update_resize])
    >- ( (* Con *)
      first_x_assum (irule_at Any)>>
      simp[fml_rel_update_resize]>>
      CONJ_TAC>-
        simp[any_el_update_resize]>>
      match_mp_tac fml_rel_update_resize>>
      match_mp_tac fml_rel_rollback>>fs[]>>
      rw[]
      >- (
        drule (el 2 (CONJUNCTS check_pbpstep_list_mindel))>>
        simp[any_el_update_resize])>>
      first_assum(qspec_then`n` mp_tac)>>
      drule (el 2 (CONJUNCTS check_pbpstep_list_id))>>
      simp[]>>rw[]>>
      drule (el 2 (CONJUNCTS check_pbpstep_list_id_upper))>>
      disch_then match_mp_tac>>
      simp[any_el_update_resize])>>
    metis_tac[fml_rel_def])
  >- (
    fs[check_pbpstep_list_def,check_pbpstep_def] >>
    rw[])
  >- (
    fs[check_pbpstep_list_def,check_pbpstep_def] >>
    rw[])
  >- (
    pop_assum mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    disch_then drule>>fs[]
    >-
      (strip_tac>>simp[Once check_pbpstep_def])
    >>(
      rw[]>>
      first_x_assum drule>>
      impl_tac >- (
        drule (hd (CONJUNCTS check_pbpstep_list_id))>>
        simp[]>>
        rw[]>>
        drule (el 1 (CONJUNCTS check_pbpstep_list_id_upper))>>
        disch_then match_mp_tac>>fs[])
      >- (strip_tac>>simp[Once check_pbpstep_def])>>
      strip_tac>>simp[Once check_pbpstep_def])
    )
QED

val _ = export_theory();
