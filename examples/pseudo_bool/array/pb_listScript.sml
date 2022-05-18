(*
  Refine PB proof checker to use arrays
*)
open preamble basis pb_checkTheory;

val _ = new_theory "pb_list"

Theorem any_el_update_resize:
  any_el n (update_resize fml def v id) def =
  if n = id then v else any_el n fml def
Proof
  rw[update_resize_def,any_el_ALT,EL_LUPDATE]>>fs[]>>
  fs[EL_APPEND_EQN,EL_REPLICATE]>>
  every_case_tac>>fs[]
QED

(*
  (* Make an array representation of a constraint *)
  Definition expand_constraint_aux_def:
    (expand_constraint_aux [] (lit_arr:int list) = (lit_arr,[])) ∧
    (expand_constraint_aux ((n,l)::xs) lit_arr =
      let (lit_arr', vs') = expand_constraint_aux xs lit_arr in
      case l of
        Neg v =>
        let la = update_resize lit_arr' 0 (-(&n)) v in (la,v::vs')
      | Pos v =>
        let la = update_resize lit_arr' 0 (&n) v in (la,v::vs'))
  End

  Definition contract_constraint_aux_def:
    (contract_constraint_aux lit_arr [] = []) ∧
    (contract_constraint_aux lit_arr (v::vs) =
      let n = any_el v lit_arr 0 in
      if n < 0 then
        (Num (-n), Neg v) :: contract_constraint_aux lit_arr vs
      else
        (Num (n), Pos v) :: contract_constraint_aux lit_arr vs)
  End

  Theorem not_var_contract:
    ∀vs la.
    EVERY (\v.  v ≠ n) vs ⇒
    contract_constraint_aux (update_resize la 0 q n) vs =
    contract_constraint_aux la vs
  Proof
    Induct>>
    rw[]>>
    simp[contract_constraint_aux_def]>>
    simp[any_el_update_resize]
  QED

  Theorem expand_constraint_get_var:
    ∀xs lit_arr lit_arr' vs'.
    expand_constraint_aux xs lit_arr = (lit_arr',vs') ⇒
    vs' = MAP (get_var o SND) xs
  Proof
    Induct>>fs[expand_constraint_aux_def]>>
    Cases>>fs[expand_constraint_aux_def]>>rw[]>>
    pairarg_tac>>fs[]>>
    first_x_assum drule>>fs[]>>
    every_case_tac>>fs[]>>rw[]
  QED

  Theorem contract_expand_constraint_aux:
    ∀xs lit_arr lit_arr' vs'.
    SORTED term_lt xs ∧
    EVERY (λ(c,l). c ≠ 0) xs ∧
    expand_constraint_aux xs lit_arr = (lit_arr',vs') ⇒
    contract_constraint_aux lit_arr' vs' = xs
  Proof
    Induct>>fs[expand_constraint_aux_def,contract_constraint_aux_def]>>
    Cases>>rw[]>>
    fs[expand_constraint_aux_def,contract_constraint_aux_def]>>
    pairarg_tac>>fs[]>>
    drule SORTED_TL>>
    strip_tac>>
    fs[]>>
    first_x_assum drule>>
    `EVERY (\v. get_var v ≠ get_var r) (MAP SND xs)` by
      (simp[EVERY_MAP]>>
      qpat_x_assum`SORTED _ (_::_)` mp_tac>>
      DEP_ONCE_REWRITE_TAC[SORTED_EQ]>>
      simp[pb_constraintTheory.transitive_term_lt]>>
      simp[EVERY_MEM,FORALL_PROD]>>
      rw[]>>
      CCONTR_TAC>>fs[]>>
      first_x_assum drule>>
      simp[])>>
    every_case_tac>>fs[]>>rw[]
    >> ( (* two subgoals *)
      simp[contract_constraint_aux_def]>>
      simp[any_el_update_resize]>>
      match_mp_tac not_var_contract>>
      drule expand_constraint_get_var>>
      disch_then SUBST1_TAC>>
      fs[EVERY_MAP])
  QED

  Definition expand_constraint_def:
    (expand_constraint (PBC l n) lit_arr =
      (n,expand_constraint_aux l lit_arr))
  End

  Definition contract_constraint_def:
    (contract_constraint (n,lit_arr,vs) =
      PBC (contract_constraint_aux lit_arr vs) n)
  End

  Theorem contract_expand_constraint:
    compact c ⇒
    contract_constraint (expand_constraint c lit_arr) = c
  Proof
    Cases_on`c`>>rw[expand_constraint_def]>>
    Cases_on`expand_constraint_aux l lit_arr`>>rw[contract_constraint_def]>>
    drule contract_expand_constraint_aux>>
    metis_tac[]
  QED
*)

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
  (check_cutting_list fml (Lit l) =
    case l of
      Pos v => SOME (PBC [(1,v)] 0)
    | Neg v => SOME (PBC [(-1,v)] 0)) ∧
  (check_cutting_list fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting_list fml c))
End

(*
(* Multiply an expanded constraint by k *)
Definition left_multiply_aux_def:
  (left_multiply_aux (k:int) lit_arr [] = lit_arr) ∧
  (left_multiply_aux k lit_arr (v::vs) =
    let l = any_el v lit_arr 0 in
    let la = left_multiply_aux k lit_arr vs in
      update_resize la 0 (l * k) v)
End

Theorem left_multiply_aux_eq:
  ∀vs lit_arr xs.
  k ≠ 0 ⇒
  contract_constraint_aux
    (left_multiply_aux (&k) lit_arr vs) vs =
  MAP (λ(c,v). (c * k,v)) (contract_constraint_aux lit_arr vs)
Proof
  Induct>>simp[contract_constraint_aux_def,left_multiply_aux_def]>>
  rw[]>>fs[any_el_update_resize]>>
  cheat
QED

Definition left_multiply_def:
  left_multiply k (n,(lit_arr,vs)) =
  if k = 0
  then (0,(lit_arr,[]))
  else
    (n*k,(left_multiply_aux (&k) lit_arr vs,vs))
End

Definition left_check_cutting_list_def:
  (left_check_cutting_list (fml: npbc option list) lit_arr (Id n) =
    OPTION_MAP (λc. expand_constraint c lit_arr) (any_el n fml NONE)) ∧
  (left_check_cutting_list fml lit_arr (Mul c k) =
    OPTION_MAP (left_multiply k) (left_check_cutting_list fml lit_arr c))
End

Theorem contract_left_check_cutting_list:
  ∀constr.
  OPTION_MAP contract_constraint
  (left_check_cutting_list fml lit_arr constr) =
  check_cutting_list fml constr
Proof
  Induct>>rw[check_cutting_list_def,left_check_cutting_list_def]
  >- (
    simp[OPTION_MAP_COMPOSE, o_DEF,OPTION_MAP_CASE]>>
    TOP_CASE_TAC>>DEP_REWRITE_TAC[contract_expand_constraint]>>
    (* assume compactness for everything in fml *)
    cheat)
  >- (* Add = hard case *) cheat
  >- (
    fs[OPTION_MAP_COMPOSE, o_DEF,OPTION_MAP_CASE]>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum sym_sub_tac>>simp[]>>
    cheat)>>
  cheat
QED
*)

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

Definition extract_clauses_list_def:
  (extract_clauses_list f def fml [] acc = SOME (REVERSE acc)) ∧
  (extract_clauses_list f def fml (cpf::pfs) acc =
    case cpf of
      (NONE,pf) => extract_clauses_list f def fml pfs ((NONE,pf)::acc)
    | (SOME (INL n),pf) =>
      (case any_el n fml NONE of
        NONE => NONE
      | SOME c => extract_clauses_list f def fml pfs ((SOME (subst f c),pf)::acc))
    | (SOME (INR u),pf) =>
      extract_clauses_list f def fml pfs ((SOME (subst f def),pf)::acc))
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
Theorem list_size_REVERSE:
  list_size f (REVERSE ls) = list_size f ls
Proof
  Induct_on`ls`>>rw[]>>
  simp[list_size_append,list_size_def]
QED

Theorem extract_clauses_list_list_size:
  ∀pfs cpfs acc.
  extract_clauses_list f c fml pfs acc = SOME cpfs ⇒
  list_size (λx. list_size pbpstep_size (SND x)) cpfs <=
  (list_size
  (pair_size (option_size (full_sum_size (λx. x) one_size)) (list_size pbpstep_size)) pfs) +
  list_size (λx. list_size pbpstep_size (SND x)) (REVERSE acc)
Proof
  Induct>>rw[extract_clauses_list_def] >>simp[]>>
  every_case_tac>>fs[]>>first_x_assum drule>>
  simp[list_size_REVERSE]>>
  EVAL_TAC>>simp[]
QED

Definition check_pbpstep_list_def:
  (check_pbpstep_list (step:pbpstep) (fml: npbc option list) (inds:num list) (mindel:num) (id:num) =
  case step of
    Contradiction n =>
      (case any_el n fml NONE of
        NONE => NONE
      | SOME c =>
        if check_contradiction c
        then SOME (fml, T,id, inds)
        else NONE)
  | Check n c =>
    if any_el n fml NONE = SOME c
    then SOME (fml, F, id, inds)
    else NONE
  | NoOp => SOME (fml, F, id, inds)
  | Delete ls =>
      if EVERY ($<= mindel) ls then
        SOME(list_delete_list ls fml, F, id, inds)
      else
        NONE
  | Cutting constr =>
    (case check_cutting_list fml constr of
      NONE => NONE
    | SOME c =>
      SOME (update_resize fml NONE (SOME c) id, F, (id+1), sorted_insert id inds))
  | Con c pf =>
    let fml_not_c = update_resize fml NONE (SOME (not c)) id in
    (case check_pbpsteps_list pf fml_not_c (sorted_insert id inds) id (id+1) of
      SOME (fml', T, id' ,inds') =>
        let rfml = rollback fml' id id' in
        SOME(update_resize rfml NONE (SOME c) id', F, (id'+1), sorted_insert id' inds')
    | _ => NONE)
  | Red c s pfs =>
    (let fml_not_c = update_resize fml NONE (SOME (not c)) id in
     let w = subst_fun s in
      case extract_clauses_list w c fml pfs [] of
        NONE => NONE
      | SOME cpfs =>
        case check_redundancy_list cpfs fml_not_c (sorted_insert id inds) id (id+1) of
          SOME(fml', id', inds') =>
          let rfml = rollback fml' id id' in
          (* TODO: check that all goals are covered *)
          SOME(update_resize rfml NONE (SOME c) id', F, (id'+1), sorted_insert id' inds')
        | NONE => NONE
       )) ∧
  (check_pbpsteps_list [] fml inds mindel id = SOME (fml, F, id, inds)) ∧
  (check_pbpsteps_list (step::steps) fml inds mindel id =
    case check_pbpstep_list step fml inds mindel id of
      SOME (fml', F, id', inds') =>
        check_pbpsteps_list steps fml' inds' mindel id'
    | res => res) ∧
  (check_redundancy_list [] fml inds mindel id = SOME(fml,id,inds)) ∧
  (check_redundancy_list ((copt,pf)::pfs) fml inds mindel id =
    case copt of
      NONE => (* no clause given *)
      (if ~EVERY is_pol_con pf then NONE else
      case check_pbpsteps_list pf fml inds mindel id of
        SOME (fml', F, id', inds') => check_redundancy_list pfs fml' inds' mindel id'
      | res => NONE)
    | SOME c =>
      let cfml = update_resize fml NONE (SOME (not c)) id in
      case check_pbpsteps_list pf cfml (sorted_insert id inds) mindel (id+1) of
        SOME (fml', T, id', inds') =>
        let rfml = rollback fml' id id' in
          check_redundancy_list pfs rfml inds' mindel id'
      | _ => NONE)
Termination
  WF_REL_TAC ‘measure (
    sum_size (pbpstep_size o FST)
    (sum_size (list_size pbpstep_size o FST) (list_size (list_size pbpstep_size o SND) o FST)))’
  \\ fs [pbpstep_size_eq] \\ rw []
  \\ drule extract_clauses_list_list_size
  \\ simp[list_size_def]
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

(* Relate sptree representation fml with list representation fmlls *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x. any_el x fmlls NONE = lookup x fml
End

(* Index list must overapproximate active indices in fmlls *)
Definition ind_rel_def:
  ind_rel fmlls inds ⇔
  ∀x. x < LENGTH fmlls ∧ IS_SOME (EL x fmlls) ⇒
  MEM x inds
End

Theorem fml_rel_check_cutting:
  ∀p.
  fml_rel fml fmlls ⇒
  check_cutting_list fmlls p = check_cutting fml p
Proof
  Induct>>rw[check_cutting_list_def,check_cutting_def]>>
  fs[fml_rel_def]>>
  every_case_tac>>simp[check_cutting_def]
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

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert id c fml) (update_resize fmlls NONE (SOME c) id)
Proof
  rw[fml_rel_def,lookup_insert,any_el_update_resize]
QED

(* id numbers are monotone increasing *)
Theorem check_pbpstep_list_id:
  (∀step fmlls inds mindel id fmlls' b id' inds'.
  check_pbpstep_list step fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒ id ≤ id') ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds'.
  check_pbpsteps_list steps fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒ id ≤ id') ∧
  (∀pfs fmlls inds mindel id fmlls' id' inds'.
  check_redundancy_list pfs fmlls inds mindel id = SOME (fmlls',id',inds') ⇒ id ≤ id')
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >- gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- (
    pop_assum mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    rw[]>>
    fs[o_DEF,ETA_AX]>>
    first_x_assum drule>>
    simp[]>>
    rw[]>>
    first_x_assum drule>>
    disch_then drule>>
    fs[])
QED

(* id numbers bound those in the formula *)
Theorem check_pbpstep_list_id_upper:
  (∀step fmlls inds mindel id fmlls' b id' inds'.
  check_pbpstep_list step fmlls inds mindel id = SOME (fmlls', b,id',inds') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds'.
  check_pbpsteps_list steps fmlls inds mindel id = SOME (fmlls', b,id',inds') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀pfs fmlls inds mindel id fmlls' id' inds'.
  check_redundancy_list pfs fmlls inds mindel id = SOME (fmlls',id',inds') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE))
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >- ( (* slow *)
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
    >-
      simp[any_el_list_delete_list]
    >-
      simp[any_el_update_resize]
    >-
      simp[any_el_update_resize,rollback_def,any_el_list_delete_list]
    >-
      simp[any_el_update_resize,rollback_def,any_el_list_delete_list])
  >- gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
  >- (
    qpat_x_assum`_= SOME _ `mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule
    >- (
      disch_then match_mp_tac>>
      fs[] ) >>
    first_x_assum drule>>
    disch_then drule>>
    rw[])
  >- gs[check_pbpstep_list_def]
  >- (
    qpat_x_assum`_= SOME _ `mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    simp[o_DEF,ETA_AX]>>
    rw[]>>first_x_assum drule
    >- (
      disch_then drule>> disch_then drule>>
      rfs[])>>
    rfs[]>>
    fs[any_el_update_resize,rollback_def,any_el_list_delete_list])
QED

Theorem check_pbpstep_list_mindel:
  (∀step fmlls inds mindel id fmlls' res n.
    check_pbpstep_list step fmlls inds mindel id = SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒ any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps fmlls inds mindel id fmlls' res n.
    check_pbpsteps_list steps fmlls inds mindel id = SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒ any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀pfs fmlls inds mindel id fmlls' res n.
    check_redundancy_list pfs fmlls inds mindel id = SOME (fmlls', res) ∧
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
      simp[any_el_update_resize]>>
      drule (el 2 (CONJUNCTS check_pbpstep_list_id))>>
      simp[rollback_def,any_el_list_delete_list,MEM_MAP])
    >- (
      first_x_assum(qspec_then`n`mp_tac)>>
      simp[any_el_update_resize]>>
      drule (el 3 (CONJUNCTS check_pbpstep_list_id))>>
      simp[rollback_def,any_el_list_delete_list,MEM_MAP]))
  >-
    fs[check_pbpstep_list_def]
  >- (
    qpat_x_assum`_=SOME _` mp_tac>>
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
  >- fs[check_pbpstep_list_def]
  >- (
    qpat_x_assum`_=SOME _` mp_tac>>
    simp[Once check_pbpstep_list_def,AllCaseEqs()] >>
    simp[o_DEF,ETA_AX]>>
    rw[]>>first_x_assum drule>>
    rfs[]
    >- (
      rw[]>>
      drule (el 2 (CONJUNCTS check_pbpstep_list_id))>>
      fs[])>>
    disch_then drule >>
    rfs[any_el_update_resize,rollback_def,any_el_list_delete_list,MEM_MAP]>>
    drule (el 2 (CONJUNCTS check_pbpstep_list_id))>>
    fs[])
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

Theorem list_delete_list_FOLDL:
  ∀l fmlls.
  list_delete_list l fmlls =
  FOLDL (\fml i.
    if LENGTH fml ≤ i then fml else LUPDATE NONE i fml) fmlls l
Proof
  Induct>>rw[list_delete_list_def]
QED

Theorem ind_rel_list_delete_list:
  ∀l fmlls.
  ind_rel fmlls inds ==>
  ind_rel (list_delete_list l fmlls) inds
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>
  rw[]>>fs[]>>
  first_x_assum drule>>
  rw[ind_rel_def,EL_LUPDATE]>>
  pop_assum mp_tac>> IF_CASES_TAC>>fs[]
QED


Theorem ind_rel_update_resize:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls NONE v n) (n::inds)
Proof
  rw[update_resize_def,ind_rel_def,EL_LUPDATE]>>every_case_tac>>fs[]>>
  fs[ind_rel_def]>>rw[]>>
  fs[IS_SOME_EXISTS,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  rfs[EL_REPLICATE,LENGTH_REPLICATE]
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

Theorem ind_rel_update_resize:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls NONE v n) (n::inds)
Proof
  rw[update_resize_def,ind_rel_def,EL_LUPDATE]>>every_case_tac>>fs[]>>
  fs[ind_rel_def]>>rw[]>>
  fs[IS_SOME_EXISTS,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  rfs[EL_REPLICATE,LENGTH_REPLICATE]
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

Theorem ind_rel_rollback:
  ind_rel fmlls inds ⇒
  ind_rel (rollback fmlls id id') inds
Proof
  rw[rollback_def]>>
  metis_tac[ind_rel_list_delete_list]
QED

Theorem ind_rel_check_pbpstep_list:
  (∀step fmlls inds mindel id fmlls' b id' inds' fml.
  ind_rel fmlls inds ∧
  check_pbpstep_list step fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒
  ind_rel fmlls' inds') ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds' fml.
  ind_rel fmlls inds ∧
  check_pbpsteps_list steps fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒
  ind_rel fmlls' inds') ∧
  (∀pfs fmlls inds mindel id fmlls' id' inds' fml.
  ind_rel fmlls inds ∧
  check_redundancy_list pfs fmlls inds mindel id = SOME (fmlls', id',inds') ⇒
  ind_rel fmlls' inds')
Proof
  ho_match_mp_tac check_pbpstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_pbpstep_def,check_pbpstep_list_def]
    >- metis_tac[ind_rel_list_delete_list]
    >- metis_tac[ind_rel_update_resize_sorted_insert]
    >- metis_tac[ind_rel_update_resize_sorted_insert,ind_rel_rollback]
    >- metis_tac[ind_rel_update_resize_sorted_insert,ind_rel_rollback])
  >- fs[check_pbpstep_list_def]
  >- gvs [AllCaseEqs(),check_pbpstep_list_def]
  >- gvs [AllCaseEqs(),check_pbpstep_list_def]
  >- (
    gvs [AllCaseEqs(),check_pbpstep_list_def]>>
    fs[o_DEF,ETA_AX]>>
    metis_tac[ind_rel_update_resize_sorted_insert,ind_rel_rollback])
QED

Theorem fml_rel_check_pbpstep_list:
  (∀step fmlls inds mindel id fmlls' b id' inds' fml.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_pbpstep_list step fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒
  if b then check_pbpstep step fml id = Unsat id'
  else ∃fml'. check_pbpstep step fml id = Cont fml' id' ∧ fml_rel fml' fmlls') ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds' fml.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_pbpsteps_list steps fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒
  if b then check_pbpsteps steps fml id = Unsat id'
  else ∃fml'. check_pbpsteps steps fml id = Cont fml' id' ∧ fml_rel fml' fmlls') ∧
  (∀pfs fmlls inds mindel id fmlls' id' inds' fml.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_redundancy_list pfs fmlls inds mindel id = SOME (fmlls', id',inds') ⇒
  ∃fml'. check_redundancy pfs fml id = Cont fml' id' ∧ fml_rel fml' fmlls')
Proof
  cheat
  (*
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
    ) *)
QED

val _ = export_theory();
