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

(* TODO: optimize this using arrays instead of lists
  alternative:
    collapse all adds into one big list before normalizing
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
      Pos v => SOME ([(1,v)],0)
    | Neg v => SOME ([(-1,v)],0)) ∧
  (check_cutting_list fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting_list fml c))
End

(* Copied from LPR *)
Definition list_delete_list_def:
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))
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
val sorted_insert_def = Define`
  (sorted_insert (x:num) [] = [x]) ∧
  (sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys
    else y::(sorted_insert x ys))`

Definition check_contradiction_fml_list_def:
  check_contradiction_fml_list fml n =
  case any_el n fml NONE of
    NONE => F
  | SOME c => check_contradiction c
End

Definition check_lstep_list_def:
  (check_lstep_list lstep
    (core:num_set) (fml: npbc option list) (inds:num list)
    (mindel:num) (id:num) =
  case lstep of
  | Check n c =>
    if any_el n fml NONE = SOME c
    then SOME (fml, id, inds)
    else NONE
  | NoOp => SOME (fml, id, inds)
  | Delete ls =>
      if EVERY (λid. mindel ≤ id ∧ lookup id core = NONE) ls then
        SOME(list_delete_list ls fml, id, inds)
      else
        NONE
  | Cutting constr =>
    (case check_cutting_list fml constr of
      NONE => NONE
    | SOME c =>
      SOME (update_resize fml NONE (SOME c) id, (id+1), sorted_insert id inds))
  | Con c pf n =>
    let fml_not_c = update_resize fml NONE (SOME (not c)) id in
    (case check_lsteps_list pf core fml_not_c (sorted_insert id inds) id (id+1) of
      SOME (fml', id' ,inds') =>
      if check_contradiction_fml_list fml' n then
        let rfml = rollback fml' id id' in
        (* Optimization: inds' ignored since inds should suffice *)
        SOME(
          update_resize rfml NONE (SOME c) id',
          (id'+1), sorted_insert id' inds)
      else NONE
    | _ => NONE)) ∧
  (check_lsteps_list [] core fml inds mindel id =
    SOME (fml, id, inds)) ∧
  (check_lsteps_list (step::steps) core fml inds mindel id =
    case check_lstep_list step core fml inds mindel id of
      SOME (fml', id', inds') =>
        check_lsteps_list steps core fml' inds' mindel id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST))’
End

(* id numbers are monotone increasing *)
Theorem check_lstep_list_id:
  (∀step core fmlls inds mindel id fmlls' id' inds'.
  check_lstep_list step core fmlls inds mindel id =
    SOME (fmlls',id',inds') ⇒
    id ≤ id') ∧
  (∀steps core fmlls inds mindel id fmlls' id' inds'.
  check_lsteps_list steps core fmlls inds mindel id =
    SOME (fmlls',id',inds') ⇒
    id ≤ id')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[] >> gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
QED

Theorem any_el_list_delete_list:
  ∀ls n fml.
  any_el n (list_delete_list ls fml) NONE =
  if MEM n ls then NONE else any_el n fml NONE
Proof
  Induct>>rw[list_delete_list_def]>>
  gs[any_el_ALT,EL_LUPDATE]
QED

(* id numbers bound those in the formula *)
Theorem check_lstep_list_id_upper:
  (∀step core fmlls inds mindel id fmlls' id' inds'.
  check_lstep_list step core fmlls inds mindel id =
    SOME (fmlls',id',inds') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀steps core fmlls inds mindel id fmlls' id' inds'.
  check_lsteps_list steps core fmlls inds mindel id =
    SOME (fmlls',id',inds') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE))
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >-
      simp[any_el_list_delete_list]
    >-
      simp[any_el_update_resize]
    >-
      simp[any_el_update_resize,rollback_def,any_el_list_delete_list])
  >- gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
  >- (
    qpat_x_assum`_= SOME _ `mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    first_x_assum drule>>
    disch_then drule>>
    rw[])
QED

(* ids below mindel are unchanged *)
Theorem check_lstep_list_mindel:
  (∀step core fmlls inds mindel id fmlls' res n.
    check_lstep_list step core fmlls inds mindel id =
      SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒
      any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps core fmlls inds mindel id fmlls' res n.
    check_lsteps_list steps core fmlls inds mindel id =
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
    >-
      rw[any_el_update_resize]
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
    simp[]>>
    rw[]>>
    first_x_assum drule>>
    first_x_assum drule>>
    disch_then drule>>
    disch_then (qspec_then`n`mp_tac)>>
    drule (el 1 (CONJUNCTS check_lstep_list_id))>>
    simp[])
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

(* Index list must lazily overapproximate the
  active indices in fmlls *)
Definition ind_rel_def:
  ind_rel fmlls inds ⇔
  ∀x. IS_SOME (any_el x fmlls NONE) ⇒ MEM x inds
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

Theorem fml_rel_check_contradiction_fml:
  fml_rel fml fmlls ∧
  check_contradiction_fml_list fmlls n ⇒
  check_contradiction_fml fml n
Proof
  rw[check_contradiction_fml_list_def,check_contradiction_fml_def,fml_rel_def]>>
  every_case_tac>>fs[]>>
  metis_tac[option_CLAUSES]
QED

Theorem fml_rel_check_lstep_list:
  (∀lstep core fmlls inds mindel id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_lstep_list lstep core fmlls inds mindel id = SOME (fmlls',id',inds') ⇒
    ∃fml'.
      check_lstep lstep core fml id = SOME (fml',id') ∧
      fml_rel fml' fmlls') ∧
  (∀lsteps core fmlls inds mindel id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_lsteps_list lsteps core fmlls inds mindel id = SOME (fmlls',id',inds') ⇒
    ∃fml'.
      check_lsteps lsteps core fml id = SOME (fml',id') ∧
      fml_rel fml' fmlls')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >- ( (* Deletion *)
      CONJ_TAC >- fs[EVERY_MEM]>>
      metis_tac[fml_rel_list_delete_list])
    >- ((* Cutting *)
      drule fml_rel_check_cutting>>
      disch_then(qspec_then`constr` assume_tac)>>fs[]>>
      metis_tac[fml_rel_update_resize])
    >- ( (* Con *)
      `fml_rel (insert id (not c') fml) (update_resize fmlls NONE (SOME (not c')) id)` by
        simp[fml_rel_update_resize]>>
      first_x_assum drule>>
      impl_tac>-
        simp[any_el_update_resize]>>
      rw[]>>gs[]>>
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
      rw[]>>fs[fml_rel_def]>>
      metis_tac[SOME_11]))
  >- fs[check_lstep_list_def,check_lstep_def]
  >- (
    pop_assum mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    disch_then drule>>fs[]>>
    rw[]>>
    first_x_assum drule>>
    impl_tac >- (
      drule (hd (CONJUNCTS check_lstep_list_id))>>
      simp[]>>
      rw[]>>
      drule (el 1 (CONJUNCTS check_lstep_list_id_upper))>>
      disch_then match_mp_tac>>fs[])>>
    strip_tac>>simp[Once check_lstep_def])
QED

Theorem ind_rel_list_delete_list:
  ∀l fmlls.
  ind_rel fmlls inds ==>
  ind_rel (list_delete_list l fmlls) inds
Proof
  rw[ind_rel_def]>>
  fs[any_el_list_delete_list]>>
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

Theorem ind_rel_check_lstep_list:
  (∀lstep core fmlls inds mindel id fmlls' id' inds'.
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_lstep_list lstep core fmlls inds mindel id = SOME (fmlls',id',inds') ⇒
    ind_rel fmlls' inds') ∧
  (∀lsteps core fmlls inds mindel id fmlls' id' inds'.
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_lsteps_list lsteps core fmlls inds mindel id = SOME (fmlls',id',inds') ⇒
    ind_rel fmlls' inds')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >- metis_tac[ind_rel_list_delete_list]
    >- metis_tac[ind_rel_update_resize_sorted_insert]
    >- (
      match_mp_tac ind_rel_update_resize_sorted_insert>>
      match_mp_tac (GEN_ALL ind_rel_rollback_2)>>
      asm_exists_tac>>simp[]>>
      drule (el 2 (CONJUNCTS check_lstep_list_mindel))>> simp[any_el_update_resize]>>
      drule (el 2 (CONJUNCTS check_lstep_list_id_upper))>> simp[any_el_update_resize]))
  >- fs[check_lstep_list_def]
  >- (
    fs[] >>
    gvs [AllCaseEqs(),check_lstep_list_def]>>
    first_x_assum match_mp_tac>>
    fs[any_el_list_delete_list,any_el_update_resize,rollback_def,MEM_MAP]
    >- (
      simp[MEM_COUNT_LIST]>>
      pop_assum kall_tac>>
      drule (el 2 (CONJUNCTS check_lstep_list_id_upper))>> simp[any_el_update_resize]>>
      strip_tac>>
      drule (el 2 (CONJUNCTS check_lstep_list_id))>> simp[any_el_update_resize]))
QED

(* Inline subst fun *)
Definition subst_subst_fun_def:
  subst_subst_fun s c = subst (subst_fun s) c
End

Definition extract_clauses_list_def:
  (extract_clauses_list s fml rsubs [] acc = SOME (REVERSE acc)) ∧
  (extract_clauses_list s fml rsubs (cpf::pfs) acc =
    case cpf of
      (NONE,pf) =>
      extract_clauses_list s fml rsubs pfs ((NONE,pf)::acc)
    | (SOME (INL n,i),pf) =>
      (case any_el n fml NONE of
        NONE => NONE
      | SOME c =>
        extract_clauses_list s fml rsubs pfs
          ((SOME ([not (subst_subst_fun s c)],i),pf)::acc))
    | (SOME (INR u,i),pf) =>
      if u < LENGTH rsubs then
        extract_clauses_list s fml rsubs pfs
          ((SOME (EL u rsubs,i),pf)::acc)
      else NONE)
End

Definition list_insert_list_def:
  (list_insert_list [] id fml inds = (id,fml,inds)) ∧
  (list_insert_list (c::cs) id fml inds =
    list_insert_list cs (id+1)
      (update_resize fml NONE (SOME c) id )
      (sorted_insert id inds))
End

Definition check_subproofs_list_def:
  (check_subproofs_list [] core fml inds mindel id =
    SOME(fml,id)) ∧
  (check_subproofs_list ((cnopt,pf)::pfs) core fml inds mindel id =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps_list pf core fml inds mindel id of
        SOME (fml', id', inds') =>
        check_subproofs_list pfs core fml' inds' mindel id'
      | res => NONE)
    | SOME (cs,n) =>
      let (cid,cfml,cinds) = list_insert_list cs id fml inds in
      (* no deletions below id *)
      case check_lsteps_list pf core cfml cinds id cid of
        SOME (fml', id', inds') =>
        if check_contradiction_fml_list fml' n then
          let rfml = rollback fml' id id' in
            check_subproofs_list pfs core rfml inds' mindel id'
        else NONE
      | _ => NONE)
End

Definition reindex_aux_def:
  (reindex_aux fml [] iacc vacc = (REVERSE iacc, vacc)) ∧
  (reindex_aux fml (i::is) iacc vacc =
  case any_el i fml NONE of
    NONE => reindex_aux fml is iacc vacc
  | SOME v =>
    reindex_aux fml is (i::iacc) (v::vacc))
End

(* Make inds non-lazy *)
Definition reindex_def:
  (reindex fml is = reindex_aux fml is [] [])
End

Definition subst_opt_subst_fun_def:
  subst_opt_subst_fun s c = subst_opt (subst_fun s) c
End

Definition subst_indexes_def:
  (subst_indexes s fml [] = []) ∧
  (subst_indexes s fml (i::is) =
    case any_el i fml NONE of NONE => subst_indexes s fml is
    | SOME res =>
    case subst_opt_subst_fun s res of NONE => subst_indexes s fml is
    | SOME c => (i,c)::subst_indexes s fml is)
End

(* Arbitrarily chosen big prime near 2^20 *)
Definition splim_def:
  splim = 1048583:num
End

Definition hash_pair_def:
  hash_pair (i:int,n:num) =
  if i < 0 then
    2 * (Num(ABS i)) + 7 * n
  else
    Num (ABS i) + 7 * n
End

Definition hash_list_def:
  (hash_list [] = 0n) ∧
  (hash_list (x::xs) =
    (hash_pair x + 7 * hash_list xs) MOD splim)
End

Definition hash_constraint_def:
  hash_constraint (c,n) =
  (n + 7 * hash_list c) MOD splim
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

Definition split_goals_hash_def:
  split_goals_hash fmlls (proved:num_set)
    (goals:(num # (int # num) list # num) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). lookup i proved ≠ NONE) goals in
  let proved = MAP SND lp in
  let hs = mk_hashset fmlls (mk_hashset proved (REPLICATE splim [])) in
  EVERY (λ(i,c). in_hashset c hs) lf
End

Definition do_red_check_def:
  do_red_check idopt fml s rfml rinds fmlls pfs rsubs =
  case idopt of NONE =>
    let goals = subst_indexes s rfml rinds in
    let (l,r) = extract_pids pfs LN LN in
      split_goals_hash fmlls l goals ∧
      EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs))
  | SOME cid =>
     check_contradiction_fml_list fml cid
End

Definition check_red_list_def:
  check_red_list ord obj core fml inds id c s pfs idopt =
  let (rinds,fmlls) = reindex fml inds in
  let nc = not c in
  let fml_not_c = update_resize fml NONE (SOME nc) id in
  let rsubs = red_subgoals ord (subst_fun s) c obj in
  case extract_clauses_list s fml rsubs pfs [] of
    NONE => NONE
  | SOME cpfs =>
    (case check_subproofs_list cpfs core fml_not_c (sorted_insert id rinds) id (id+1) of
       NONE => NONE
    |  SOME(fml', id') =>
      let rfml = rollback fml' id id' in
      if do_red_check idopt fml' s rfml
          rinds (nc::fmlls) pfs rsubs then
          SOME (rfml,id',rinds)
      else NONE)
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) ord obj core
    (fml: npbc option list) (inds:num list) (id:num) =
  case sstep of
  | Lstep lstep =>
    check_lstep_list lstep core fml inds 0 id
  | Red c s pfs idopt =>
    case check_red_list ord obj core fml inds id c s pfs idopt of
      SOME (rfml,id',rinds) =>
      SOME(
        update_resize rfml NONE (SOME c) id',
        (id'+1), sorted_insert id' rinds)
    | NONE => NONE)
End

Theorem fml_rel_extract_clauses_list:
  ∀ls s fml fmlls rsubs acc.
  fml_rel fml fmlls ⇒
  extract_clauses (subst_fun s) fml rsubs ls acc =
  extract_clauses_list s fmlls rsubs ls acc
Proof
  Induct>>rw[extract_clauses_def,extract_clauses_list_def]>>
  every_case_tac>>
  fs[fml_rel_def,subst_subst_fun_def]>>
  metis_tac[option_CLAUSES]
QED

Theorem ind_rel_rollback:
  ind_rel fmlls inds ⇒
  ind_rel (rollback fmlls id id') inds
Proof
  rw[rollback_def]>>
  metis_tac[ind_rel_list_delete_list]
QED

Theorem list_insert_list_id:
  ∀cs id fmlls inds cid cfmlls cinds.
  list_insert_list cs id fmlls inds = (cid,cfmlls,cinds) ⇒
  id ≤ cid
Proof
  Induct>>rw[list_insert_list_def]>>
  first_x_assum drule>>
  simp[]
QED

Theorem list_insert_list_id_upper:
  ∀cs id fmlls inds cid cfmlls cinds.
  list_insert_list cs id fmlls inds = (cid,cfmlls,cinds) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ cid ⇒ any_el n cfmlls NONE = NONE)
Proof
  Induct>>rw[list_insert_list_def]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem list_insert_list_mindel:
  ∀cs id fmlls inds cid cfmlls cinds.
  list_insert_list cs id fmlls inds = (cid,cfmlls,cinds) ⇒
  (∀n. n < id ⇒ any_el n cfmlls NONE = any_el n fmlls NONE)
Proof
  Induct>>rw[list_insert_list_def]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem fml_rel_list_insert_list:
  ∀cs id fml fmlls inds cid cfml cid' cfmlls cinds.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  list_insert cs id fml = (cid,cfml) ∧
  list_insert_list cs id fmlls inds = (cid',cfmlls,cinds) ⇒
  cid = cid' ∧
  fml_rel cfml cfmlls ∧
  ind_rel cfmlls cinds ∧
  (∀n. n ≥ cid ⇒ any_el n cfmlls NONE = NONE) ∧
  (∀n. n < id ⇒ any_el n cfmlls NONE = any_el n fmlls NONE) ∧
  id ≤ cid
Proof
  Induct>>simp[list_insert_def,list_insert_list_def]>>
  ntac 11 strip_tac>>
  first_x_assum (drule_at Any)>>
  disch_then (drule_at Any)>>
  impl_tac >- (
    simp[fml_rel_update_resize,ind_rel_update_resize_sorted_insert]>>
    simp[any_el_update_resize])>>
  rw[any_el_update_resize]
QED

Theorem fml_rel_check_subproofs_list:
  ∀pfs core fmlls inds mindel id fmlls' id' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_subproofs_list pfs core fmlls inds mindel id = SOME (fmlls', id') ⇒
    ∃fml'.
      check_subproofs pfs core fml id = SOME (fml',id') ∧
      fml_rel fml' fmlls'
Proof
  ho_match_mp_tac check_subproofs_list_ind>>rw[]>>
  fs[check_subproofs_def,check_subproofs_list_def]>>
  gvs[AllCaseEqs()]
  >- (
    drule (CONJUNCT2 fml_rel_check_lstep_list)>>
    rpt(disch_then drule)>>
    drule (CONJUNCT2 ind_rel_check_lstep_list)>>
    rpt(disch_then drule)>>
    drule (CONJUNCT2 check_lstep_list_id)>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    drule (CONJUNCT2 check_lstep_list_mindel)>>
    simp[]>>
    rw[]>>every_case_tac>>fs[])>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_list_insert_list>>
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
    drule_all (CONJUNCT2 ind_rel_check_lstep_list)>>
    metis_tac[ind_rel_rollback])
  >- (
    fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])>>
  imp_res_tac check_lstep_list_id>>
  fs[]
QED

Theorem check_subproofs_list_id:
  ∀pfs core fmlls inds mindel id fmlls' id'.
    check_subproofs_list pfs core fmlls inds mindel id = SOME (fmlls', id') ⇒
    id ≤ id'
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  rw[check_subproofs_list_def]>>
  gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_lstep_list_id>>
  imp_res_tac list_insert_list_id>>
  fs[]
QED

Theorem check_subproofs_list_id_upper:
  ∀pfs core fmlls inds mindel id fmlls' id'.
  check_subproofs_list pfs core fmlls inds mindel id = SOME (fmlls', id') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  simp[check_subproofs_list_def]>>
  ntac 11 strip_tac>>
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
  metis_tac[list_insert_list_id_upper]
QED

Theorem check_subproofs_list_mindel:
  ∀pfs core fmlls inds mindel id fmlls' id' n.
  check_subproofs_list pfs core fmlls inds mindel id = SOME (fmlls', id') ∧
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
  drule (list_insert_list_mindel)>>fs[]>>
  rw[]>>
  drule (list_insert_list_id)>>
  drule (CONJUNCT2 check_lstep_list_id)>>rw[]>>
  gvs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem reindex_aux:
  ∀inds iacc vacc.
  reindex_aux fmlls inds iacc vacc =
  let is = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds in
  let vs = MAP (λx. THE (any_el x fmlls NONE)) is in
  (REVERSE iacc ++ is, REVERSE vs ++ vacc)
Proof
  Induct>>rw[reindex_aux_def]>>
  every_case_tac>>fs[]
QED

Theorem FST_reindex_characterize:
  reindex fmlls inds = (is,vs) ⇒
  is = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds
Proof
  rw[reindex_def,reindex_aux]
QED

Theorem SND_reindex_characterize:
  fml_rel fml fmlls ∧
  reindex fmlls inds = (is,vs) ⇒
  set vs ⊆ range fml
Proof
  rw[reindex_def,reindex_aux]>>
  simp[SUBSET_DEF,MEM_MAP,MEM_FILTER,PULL_EXISTS,range_def]>>
  rw[]>>
  fs[fml_rel_def,IS_SOME_EXISTS]>>
  metis_tac[]
QED

Theorem ind_rel_reindex:
  ind_rel fml inds ∧
  reindex fml inds = (is,vs) ⇒
  ind_rel fml is
Proof
  rw[]>>drule FST_reindex_characterize>>
  fs[ind_rel_def,MEM_FILTER]
QED

Theorem MEM_subst_indexes:
  ∀inds i c.
  MEM i inds ∧
  any_el i fml NONE = SOME c ∧
  subst_opt (subst_fun s) c = SOME res
  ⇒
  MEM (i,res) (subst_indexes s fml inds)
Proof
  Induct>>rw[subst_indexes_def]>>
  every_case_tac>>
  fs[AllCaseEqs(),any_el_def]>>
  fs[subst_opt_subst_fun_def]
QED

Theorem subst_indexes_MEM:
  ∀inds i res.
  MEM (i,res) (subst_indexes s fml inds) ⇒
  ∃c.
  MEM i inds ∧
  any_el i fml NONE = SOME c ∧
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
  split_goals_hash (nc::fmlls) proved goals ⇒
  split_goals fml nc proved goals
Proof
  rw[split_goals_def,split_goals_hash_def]>>
  pairarg_tac>>fs[]>>
  qpat_x_assum`EVERY _ _`mp_tac>> match_mp_tac MONO_EVERY>>
  simp[FORALL_PROD]>>
  rw[]>>
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

Theorem fml_rel_check_red_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_red_list ord obj core fmlls inds id c s pfs idopt =
    SOME (fmlls', id', inds') ⇒
    check_red ord obj core fml id c s pfs idopt = SOME id' ∧
    fml_rel fml fmlls' ∧
    ind_rel fmlls' inds' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
    id ≤ id'
Proof
  strip_tac>>
  fs[check_red_list_def]>>
  pairarg_tac>>fs[]>>
  every_case_tac>>gvs[]>>
  simp[check_red_def]>>
  DEP_REWRITE_TAC [fml_rel_extract_clauses_list]>> simp[]>>
  gvs[AllCaseEqs()]>>
  `fml_rel (insert id (not c) fml)
    (update_resize fmlls NONE (SOME (not c)) id)` by
    metis_tac[fml_rel_update_resize]>>
  drule fml_rel_check_subproofs_list>>
  disch_then (drule_at Any)>>
  impl_tac>- (
    rw[]
    >- (
      match_mp_tac ind_rel_update_resize_sorted_insert>>
      metis_tac[ind_rel_reindex] )>>
    simp[any_el_update_resize])>>
  simp[]>>strip_tac>>
  gvs[]>>
  drule check_subproofs_list_id>>
  drule check_subproofs_list_id_upper>>
  drule check_subproofs_list_mindel>>
  simp[any_el_update_resize]>>
  ntac 3 strip_tac>>
  CONJ_TAC >- (
    gvs[do_red_check_def,AllCaseEqs()]>>
    TOP_CASE_TAC>>fs[]
    >- (
      rpt (pairarg_tac>>fs[])>>
      (drule_at Any) split_goals_hash_imp_split_goals>>
      disch_then (qspec_then`fml` mp_tac)>>
      impl_tac >- (
        match_mp_tac (GEN_ALL SND_reindex_characterize)>>
        metis_tac[])>>
      match_mp_tac split_goals_same_goals>>
      simp[EXTENSION,FORALL_PROD]>>
      rw[]>>eq_tac>>rw[]
      >- (
        fs[MEM_toAList,lookup_map_opt,AllCaseEqs()]>>
        match_mp_tac (GEN_ALL MEM_subst_indexes)>>
        first_x_assum (irule_at Any)>>
        CONJ_TAC>- (
          drule FST_reindex_characterize>>
          simp[MEM_FILTER]>>
          fs[fml_rel_def,ind_rel_def])>>
        simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
        rw[]
        >- (
          last_x_assum(qspec_then`id+y` assume_tac)>>
          fs[fml_rel_def]>>
          last_x_assum(qspec_then`id+y` assume_tac)>>
          fs[])>>
        rename1`any_el idd _ _ = _`>>
        `idd < id` by (
          CCONTR_TAC>>fs[]>>
          last_x_assum(qspec_then`idd` mp_tac)>>
          impl_tac>-fs[]>>
          fs[fml_rel_def])>>
        first_x_assum drule>>
        fs[fml_rel_def])>>
      drule subst_indexes_MEM>>
      rw[MEM_toAList,lookup_map_opt]>>
      rename1`any_el idd _ _ = _`>>
      drule FST_reindex_characterize>>
      strip_tac>>gvs[]>>
      fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,MEM_FILTER]>>
      `idd < id` by (
        CCONTR_TAC>>fs[]>>
        last_x_assum(qspec_then`idd` mp_tac)>>
        impl_tac>-fs[]>>
        metis_tac[option_CLAUSES])>>
      `lookup idd fml = SOME c'` by
        (fs[fml_rel_def]>>
        metis_tac[])>>
      simp[])>>
    match_mp_tac (GEN_ALL fml_rel_check_contradiction_fml)>>
    metis_tac[])>>
  CONJ_TAC>- (
    match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
  CONJ_TAC >- (
    match_mp_tac ind_rel_rollback_2>>
    simp[]>>
    metis_tac[ind_rel_reindex])>>
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem fml_rel_check_sstep_list:
  ∀sstep ord obj core fmlls inds id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_sstep_list sstep ord obj core fmlls inds id =
      SOME (fmlls',id',inds') ⇒
    ∃fml'.
      check_sstep sstep ord obj core fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      id ≤ id'
Proof
  Cases>>rw[]>>fs[check_sstep_list_def,check_sstep_def]
  >- (
    drule (CONJUNCT1 fml_rel_check_lstep_list)>>
    `0 ≤ id` by fs[]>>
    rpt (disch_then drule)>>
    drule (CONJUNCT1 ind_rel_check_lstep_list)>>
    rpt (disch_then drule)>>
    rw[]>>gs[]>>
    CONJ_TAC
    >- (
      drule (CONJUNCT1 check_lstep_list_id_upper)>>
      simp[])>>
    drule (CONJUNCT1 check_lstep_list_id)>>
    simp[])
  >- ( (* Red*)
    pop_assum mp_tac>>
    TOP_CASE_TAC>>fs[]>>
    PairCases_on`x`>>strip_tac>>gvs[]>>
    drule_all fml_rel_check_red_list>>
    simp[]>>rw[]
    >-
      metis_tac[fml_rel_update_resize]
    >-
      metis_tac[ind_rel_update_resize_sorted_insert]>>
    simp[any_el_update_resize])
QED

Definition check_ssteps_list_def:
  (check_ssteps_list [] ord obj core
    (fml: npbc option list) (inds:num list) (id:num) =
    SOME (fml, id, inds)) ∧
  (check_ssteps_list (s::ss) ord obj core fml inds id =
  case check_sstep_list s ord obj core fml inds id of
    SOME (fml',id',inds') =>
      check_ssteps_list ss ord obj core fml' inds' id'
  | res => res)
End

Theorem fml_rel_check_ssteps_list:
  ∀ss ord obj core fmlls inds id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_ssteps_list ss ord obj core fmlls inds id = SOME (fmlls',id',inds') ⇒
    ∃fml'.
      check_ssteps ss ord obj core fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      id ≤ id'
Proof
  Induct>>rw[check_ssteps_list_def]
  >-
    simp[check_ssteps_def]>>
  simp[check_ssteps_def]>>
  pop_assum mp_tac>> TOP_CASE_TAC>>
  PairCases_on`x`>>fs[]>>rw[]>>
  drule fml_rel_check_sstep_list>>
  rpt(disch_then drule)>>
  rw[]>>
  first_x_assum drule_all>>
  rw[]>>
  fs[]
QED

Definition read_coref_list_def:
  (read_coref_list [] fml = []) ∧
  (read_coref_list (i::is) fml =
    case any_el i fml NONE of
      NONE => read_coref_list is fml
    | SOME res => (i,res) :: read_coref_list is fml)
End

Theorem ALOOKUP_read_coref_list:
  ∀ids fml n.
  ALL_DISTINCT ids ⇒
  ALOOKUP (read_coref_list ids fml) n =
  if MEM n ids then
     (case any_el n fml NONE of
      NONE => NONE
    | SOME res => SOME res)
  else NONE
Proof
  Induct>>rw[read_coref_list_def]
  >-
    (TOP_CASE_TAC>>simp[])
  >- (
    `h ≠ n` by metis_tac[]>>
    TOP_CASE_TAC>>fs[])>>
  fs[]>>
  every_case_tac>>fs[]
QED

(* TODO: this can be made more efficient with imperative mapi *)
Definition coref_list_def:
  coref_list core fmlls =
  let ids = MAP FST (toAList core) in
  fromAList (read_coref_list ids fmlls)
End

Theorem coref_coref_list:
  fml_rel fml fmlls ⇒
  coref core fml = coref_list core fmlls
Proof
  rw[fml_rel_def,coref_list_def,coref_def]>>
  DEP_REWRITE_TAC[spt_eq_thm]>>
  rw[wf_fromAList,lookup_fromAList,lookup_inter]>>
  DEP_REWRITE_TAC[ALOOKUP_read_coref_list]>>
  simp[ALL_DISTINCT_MAP_FST_toAList,toAList_domain,domain_lookup]>>
  rw[]>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  Cases_on`lookup n core`>>fs[]
QED

Definition all_core_def:
  all_core fml inds core ⇔
  let inds' = FST (reindex fml inds) in
  (EVERY (λn. lookup n core ≠ NONE) inds', inds')
End

Theorem fml_rel_all_core:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  all_core fmlls inds core = (T,inds') ⇒
  domain fml ⊆ domain core ∧
  ind_rel fmlls inds'
Proof
  reverse (rw[all_core_def])
  >-
    metis_tac[ind_rel_reindex,FST,PAIR]>>
  Cases_on`reindex fmlls inds`>>
  drule FST_reindex_characterize>>rw[]>>
  fs[EVERY_FILTER]>>
  fs[fml_rel_def,ind_rel_def,SUBSET_DEF,domain_lookup]>>
  rw[]>>
  first_x_assum(qspec_then`x` assume_tac)>>
  first_x_assum(qspec_then`x` assume_tac)>>
  gs[EVERY_MEM]>>
  first_x_assum drule>>
  simp[]>>
  Cases_on`lookup x core`>>simp[]
QED

Definition core_from_inds_def:
  core_from_inds inds = fromAList (MAP (λx. (x,())) inds)
End

Definition do_dom_check_def:
  do_dom_check idopt fml rfml w cf indfml pfs dsubs =
  case idopt of NONE =>
    let goals = toAList (map_opt (subst_opt w) cf) in
    let (l,r) = extract_pids pfs LN LN in
    if EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH dsubs))
    then
      split_goals_hash indfml l goals
    else F
  | SOME cid =>
     check_contradiction_fml_list fml cid
End

Definition check_change_obj_list_def:
  check_change_obj_list fml core chk obj ord fc' n1 n2 ⇔
  case obj of NONE => F
  | SOME fc =>
    case (any_el n1 fml NONE, any_el n2 fml NONE) of
      (SOME c1, SOME c2) =>
      (chk ∨ IS_SOME ord ⇒ lookup n1 core = SOME ()) ∧
      imp c1 (model_bounding fc fc') ∧
      imp c2 (model_bounding fc' fc)
    | _ => F
End

Definition load_coref_list_def:
  (load_coref_list [] fml newfml = newfml) ∧
  (load_coref_list (i::is) fml newfml =
    load_coref_list is fml (LUPDATE (EL i fml) i newfml))
End

(* Extract the core array from a core *)
Definition arr_from_core_list_def:
  arr_from_core_list core fmlls =
  let ids = MAP FST (toAList core) in
  let newfml = REPLICATE (LENGTH fmlls) NONE in
  (load_coref_list ids fmlls newfml, ids)
End

Definition check_cstep_list_def:
  check_cstep_list cstep core chk obj bound
    ord orders fml inds id =
  case cstep of
    Dom c s pfs idopt =>
    (case ord of NONE => NONE
    | SOME spo =>
    ( let nc = not c in
      let (rinds,fmlls) = reindex fml inds in
      let fml_not_c = update_resize fml NONE (SOME nc) id in
      let w = subst_fun s in
      let cf = coref_list core fml in
      let dsubs = dom_subgoals spo w c obj in
      case extract_clauses_list s fml dsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
        (case check_subproofs_list cpfs core fml_not_c (sorted_insert id rinds) id (id+1) of
          NONE => NONE
        | SOME (fml',id') =>
          let rfml = rollback fml' id id' in
          if do_dom_check idopt fml' rfml w cf (nc::fmlls) pfs dsubs then
            SOME(
              update_resize rfml NONE (SOME c) id',
              sorted_insert id' rinds,
              id'+1,
              core, chk, obj, bound, ord, orders)
          else NONE)))
  | LoadOrder nn xs =>
    (let inds' = FST (reindex fml inds) in
      case ALOOKUP orders nn of NONE => NONE
      | SOME ord' =>
        if LENGTH xs = LENGTH (FST (SND ord')) then
          SOME (fml,inds',id,
            core_from_inds inds',
            chk, obj, bound, SOME (ord',xs),orders)
        else NONE)
  | UnloadOrder =>
    (case ord of NONE => NONE
    | SOME spo =>
        SOME (fml,inds,id,
          core, chk, obj, bound, NONE, orders))
  | StoreOrder nn spo ws pfs =>
    if check_good_ord spo ∧ check_ws spo ws ∧
       check_transitivity spo ws pfs then
        SOME (fml,inds,id,
          core, chk, obj, bound, ord, (nn,spo)::orders)
    else
      NONE
  | Transfer ls =>
    if EVERY (λid. any_el id fml NONE ≠ NONE) ls
    then SOME (fml, inds, id,
               FOLDL (λa b. insert b () a) core ls,
               chk, obj, bound, ord, orders)
    else NONE
  | CheckedDelete n s pfs idopt => (
    case any_el n fml NONE of
      NONE => NONE
    | SOME c =>
      if lookup n core = SOME () then
        let nc = delete n core in
        let (ncf,ninds) = arr_from_core_list nc fml in
        case check_red_list ord obj nc ncf ninds id c s pfs idopt of
          SOME (ncf',id',ninds') =>
          SOME (list_delete_list [n] fml, inds, id',
                nc, chk, obj, bound, ord, orders)
        | NONE => NONE
      else NONE)
  | UncheckedDelete ls =>
    if ord = NONE then
      SOME (list_delete_list ls fml, inds, id,
            FOLDL (λa b. delete b a) core ls,
            F, obj, bound, ord, orders)
    else
      let (ac,inds') = all_core fml inds core in
      if ac then
        SOME (list_delete_list ls fml, inds', id,
            FOLDL (λa b. delete b a) core ls,
            F, obj, bound, ord, orders)
      else NONE
  | Sstep sstep =>
    (case check_sstep_list sstep ord obj core fml inds id of
      SOME(fml',id',inds') =>
      SOME (fml',inds',id',
        core, chk, obj, bound, ord, orders)
    | NONE => NONE)
  | Obj w mi bopt =>
    (case check_obj obj w (MAP SND (toAList (coref_list core fml))) bopt of
      NONE => NONE
    | SOME new =>
      let bound' = update_bound bound new in
      if mi then
        let c = model_improving obj new in
        SOME (
          update_resize fml NONE (SOME c) id,
          sorted_insert id inds,
          id+1,
          insert id () core,
          chk, obj, bound', ord, orders)
      else
        SOME(fml,inds,id,core,chk,obj,bound',ord,orders))
  | ChangeObj fc' n1 n2 =>
    if check_change_obj_list fml core chk obj ord fc' n1 n2 then
      SOME (
      fml, inds, id, core, chk, SOME fc', bound, ord, orders)
    else NONE
End

Theorem check_lstep_id:
  (∀s c f id fml' id'.
  check_lstep s c f id = SOME (fml',id') ⇒
  id ≤ id') ∧
  (∀s c f id fml' id'.
  check_lsteps s c f id = SOME (fml',id') ⇒
  id ≤ id')
Proof
  ho_match_mp_tac check_lstep_ind>>rw[check_lstep_def]>>
  gvs[AllCaseEqs()]
QED

Theorem list_insert_id:
  ∀cs id fml cid cfml.
  list_insert cs id fml = (cid,cfml) ⇒
  id ≤ cid
Proof
  Induct>>rw[list_insert_def]>>
  first_x_assum drule>>
  simp[]
QED

Theorem check_subproofs_id:
  ∀ls c f id f' id'.
  check_subproofs ls c f id = SOME (f',id') ⇒
  id ≤ id'
Proof
  Induct>>simp[FORALL_PROD]>>rw[check_subproofs_def]>>
  gvs[AllCaseEqs()]
  >- (
    imp_res_tac check_lstep_id>>
    first_x_assum drule>>
    fs[])>>
  pairarg_tac>>gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  drule list_insert_id>>
  imp_res_tac check_lstep_id>>
  fs[]
QED

Theorem check_red_id:
  check_red ord obj core fml id c s pfs idopt = SOME id' ⇒
  id ≤ id'
Proof
  rw[check_red_def]>>
  every_case_tac>>fs[]>>
  drule check_subproofs_id>>
  simp[]
QED

Theorem check_ssteps_id:
  ∀r f id f' id'.
  check_ssteps r ord obj c f id = SOME (f', id') ⇒
  id ≤ id'
Proof
  Induct>>rw[check_ssteps_def]>>
  Cases_on`h`>>
  gvs[AllCaseEqs(),check_sstep_def]>>
  first_x_assum drule
  >- (
    imp_res_tac check_lstep_id>>
    fs[])>>
  drule check_red_id>>
  simp[]
QED

Theorem fromAList_toAList_core_from_inds:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ⇒
  fromAList (MAP (λ(x,y). (x,())) (toAList fml)) =
  core_from_inds (FST (reindex fmlls inds))
Proof
  DEP_REWRITE_TAC[spt_eq_thm]>>
  Cases_on`reindex fmlls inds`>>
  drule FST_reindex_characterize>>strip_tac>>
  gvs[]>>
  simp[core_from_inds_def,wf_fromAList,lookup_fromAList,ALOOKUP_MAP,ALOOKUP_toAList]>>rw[]>>
  Cases_on`lookup n fml`>>fs[fml_rel_def]>>
  last_x_assum(qspec_then`n` assume_tac)
  >-
    simp[ALOOKUP_NONE,MEM_MAP,PULL_FORALL,MEM_FILTER]>>
  qmatch_goalsub_abbrev_tac`ALOOKUP ls n`>>
  Cases_on`ALOOKUP ls n`>>
  gvs[ALOOKUP_NONE,MEM_MAP,PULL_FORALL,MEM_FILTER,Abbr`ls`,ind_rel_def]
QED

Theorem any_el_load_coref_list:
  ∀ls fml newfml.
  LENGTH fml = LENGTH newfml ⇒
  any_el n (load_coref_list ls fml newfml) NONE =
  if MEM n ls then
    any_el n fml NONE
  else any_el n newfml NONE
Proof
  Induct>>rw[load_coref_list_def]>>fs[]>>
  rw[any_el_ALT,EL_LUPDATE]>>fs[]
QED

Theorem any_el_REPLICATE:
  any_el n (REPLICATE l v) def =
  if n < l then v else def
Proof
  rw[any_el_ALT,EL_REPLICATE]
QED

Theorem arr_from_core_list_rel:
  fml_rel fml fmlls ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  arr_from_core_list core fmlls = (ncf,ninds) ⇒
  fml_rel (coref core fml) ncf ∧
  ind_rel ncf ninds ∧
  (∀n. n ≥ id ⇒ any_el n ncf NONE = NONE)
Proof
  rw[fml_rel_def,arr_from_core_list_def,ind_rel_def]>>
  fs[any_el_load_coref_list,any_el_REPLICATE]>>
  every_case_tac>>fs[toAList_domain,domain_lookup,IS_SOME_EXISTS]>>
  simp[coref_def,lookup_inter,AllCaseEqs()]
  >- metis_tac[option_CLAUSES]>>
  Cases_on`lookup x core`>>fs[]>>
  metis_tac[option_CLAUSES]
QED

Theorem fml_rel_check_cstep_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_cstep_list cstep core chk obj bound ord orders
    fmlls inds id =
    SOME (fmlls',inds',id',rest) ⇒
  ∃fml'.
    check_cstep cstep fml id core chk obj bound ord orders =
      SOME (fml', id', rest) ∧
    fml_rel fml' fmlls' ∧
    ind_rel fmlls' inds' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
    id ≤ id'
Proof
  Cases_on`cstep`>>rw[]
  >- ((* Dom *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs()]>>
    DEP_REWRITE_TAC[fml_rel_extract_clauses_list]>>
    simp[PULL_EXISTS]>>
    (drule_at Any) fml_rel_check_subproofs_list>>
    disch_then(qspec_then`insert id (not p) fml` mp_tac)>>
    impl_tac >- (
      simp[fml_rel_update_resize,any_el_update_resize]>>
      match_mp_tac ind_rel_update_resize_sorted_insert>>
      metis_tac[ind_rel_reindex])>>
    rw[]>>simp[]>>
    drule check_subproofs_list_id>>
    drule check_subproofs_list_id_upper>>
    drule check_subproofs_list_mindel>>
    simp[any_el_update_resize]>>
    ntac 3 strip_tac>>
    CONJ_TAC>- (
      fs[do_dom_check_def]>>
      every_case_tac>>fs[]
      >- (
        (drule_at Any) split_goals_hash_imp_split_goals>>
        DEP_REWRITE_TAC[coref_coref_list]>>
        fs[]>>
        disch_then match_mp_tac>>
        match_mp_tac (GEN_ALL SND_reindex_characterize)>>
        metis_tac[])>>
      metis_tac[fml_rel_check_contradiction_fml] )>>
    CONJ_TAC>- (
      match_mp_tac fml_rel_update_resize>>
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_update_resize_sorted_insert>>
      match_mp_tac ind_rel_rollback_2>>
      fs[]>>
      metis_tac[ind_rel_reindex])>>
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST])
  >- ( (* LoadOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    simp[fromAList_toAList_core_from_inds]>>
    metis_tac[FST_reindex_characterize,PAIR,FST,ind_rel_reindex])
  >- ( (* UnloadOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >- ( (* StoreOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >- ( (* Transfer *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    fs[EVERY_MEM,fml_rel_def]>>
    rw[]>>first_x_assum drule>>
    metis_tac[option_CLAUSES])
  >- ( (* CheckedDelete *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    `lookup n fml = SOME c` by
      metis_tac[fml_rel_def]>>
    simp[]>>
    pairarg_tac>>gvs[AllCaseEqs()]>>
    drule_all arr_from_core_list_rel>>
    strip_tac>>
    drule_all fml_rel_check_red_list>>
    strip_tac>>simp[]>>
    CONJ_TAC >- (
      qpat_x_assum`fml_rel fml _` assume_tac>>
      drule fml_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>simp[])>>
    CONJ_TAC >- (
      qpat_x_assum`ind_rel fmlls _` assume_tac>>
      drule ind_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>simp[])>>
    simp[any_el_list_delete_list])
  >- ((* UncheckedDelete *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]
    >- (
      CONJ_TAC >-
        metis_tac[fml_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[ind_rel_list_delete_list]>>
      simp[any_el_list_delete_list])
    >- (
      pairarg_tac>>gvs[]>>
      drule_all fml_rel_all_core>>strip_tac>>
      simp[]>>
      CONJ_TAC >-
        metis_tac[fml_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[ind_rel_list_delete_list]>>
      simp[any_el_list_delete_list]))
  >- ( (* Sstep *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all fml_rel_check_sstep_list>>
    rw[])
  >- ( (* Obj *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule coref_coref_list>>
    rw[]>>gvs[]
    >- metis_tac[fml_rel_update_resize]
    >- metis_tac[ind_rel_update_resize_sorted_insert]>>
    simp[any_el_update_resize])
  >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    gvs[check_change_obj_list_def,check_change_obj_def]>>
    gs[fml_rel_def])
QED

Definition check_csteps_list_def:
  (check_csteps_list [] core chk obj bound
    ord orders fml inds id =
    SOME
      (fml, inds, id, core, chk, obj, bound, ord, orders)) ∧
  (check_csteps_list (c::cs) core chk obj bound
    ord orders fml inds id =
    case check_cstep_list c core chk obj bound
      ord orders fml inds id of
      NONE => NONE
    | SOME(fml', inds', id',
      core', chk', obj', bound', ord', orders') =>
      check_csteps_list cs core' chk' obj' bound'
        ord' orders' fml' inds' id')
End

Theorem fml_rel_check_csteps_list:
  ∀csteps core chk obj bound ord orders fmlls inds id
    fmlls' inds' id' fml rest.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_csteps_list csteps core chk obj bound
      ord orders fmlls inds id =
    SOME (fmlls', inds', id', rest) ⇒
    ∃fml'.
      check_csteps csteps fml id core chk obj bound
        ord orders = SOME (fml', id', rest) ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      id ≤ id'
Proof
  Induct>>simp[]
  >- (
    rw[check_csteps_list_def,check_csteps_def]>>
    metis_tac[])>>
  rw[]>>
  fs[check_csteps_list_def,check_csteps_def]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_check_cstep_list>>
  rw[]>>simp[]>>
  first_x_assum drule_all>>
  rw[]>>simp[]
QED

Theorem LENGTH_FOLDR_update_resize2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME v) i) x) (REPLICATE n NONE) ll)
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once update_resize_def]
  >- (
    first_x_assum drule>>
    simp[])>>
  first_x_assum drule>>simp[]
QED

Theorem all_distinct_map_fst_rev:
  ALL_DISTINCT (MAP FST ls) ⇔ ALL_DISTINCT (MAP FST (REVERSE ls))
Proof
  fs[MAP_REVERSE]
QED

Theorem FOLDL_update_resize_lookup:
  ∀ls.
  ALL_DISTINCT (MAP FST ls) ⇒
  ∀x.
  x < LENGTH (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) ls)
  =
  ALOOKUP ls x
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
  fml_rel (build_fml k fml)
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
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
  simp[lookup_build_fml,ALOOKUP_enumerate]
QED

Theorem ind_rel_FOLDL_update_resize:
  ind_rel
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i) (REPLICATE n NONE) (enumerate k fml))
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

Definition check_implies_fml_list_def:
  check_implies_fml_list fml n c =
  (case any_el n fml NONE of
      NONE => F
    | SOME ci =>
      imp ci c)
End

Definition check_hconcl_list_def:
  (check_hconcl_list fml obj fml' chk' obj' bound' HNoConcl = T) ∧
  (check_hconcl_list fml obj fml' chk' obj' bound' (HDSat wopt) =
    case wopt of
      NONE =>
      chk' ∧ bound' ≠ NONE
    | SOME wm =>
      check_obj obj wm fml NONE ≠ NONE) ∧
  (check_hconcl_list fml obj fml' chk' obj' bound' (HDUnsat n) =
    (bound' = NONE ∧ check_contradiction_fml_list fml' n)) ∧
  (check_hconcl_list fml obj fml' chk' obj' bound'
    (HOBounds lbi ubi n wopt) =
    (
    (opt_le lbi bound' ∧
    case lbi of
      NONE => check_contradiction_fml_list fml' n
    | SOME lb => check_implies_fml_list fml' n (lower_bound obj' lb)) ∧
    (
    case wopt of
      NONE => chk' ∧ opt_le bound' ubi
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
  metis_tac[option_CLAUSES]
QED

Theorem fml_rel_check_hconcl_list:
  fml_rel fml' fmlls' ∧
  check_hconcl_list fml obj fmlls' chk' obj' bound' hconcl ⇒
  check_hconcl fml obj fml' chk' obj' bound' hconcl
Proof
  Cases_on`hconcl`>>
  fs[check_hconcl_def,check_hconcl_list_def]
  >-
    metis_tac[fml_rel_check_contradiction_fml]>>
  rw[]>>every_case_tac>>fs[]>>
  metis_tac[fml_rel_check_contradiction_fml,fml_rel_check_implies_fml]
QED

Theorem wf_build_fml:
  ∀fml n.
  wf (build_fml n fml)
Proof
  Induct>>rw[build_fml_def]>>
  simp[wf_insert]
QED

Theorem check_csteps_list_concl:
  check_csteps_list cs
    (fromAList (MAP (λ(x,y). (x,())) (enumerate 1 fml)))
    T obj NONE NONE []
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i)
      (REPLICATE (2 * (LENGTH fml + 1)) NONE) (enumerate 1 fml))
    (REVERSE (MAP FST (enumerate 1 fml)))
    (LENGTH fml + 1) =
    SOME(fmlls',inds',id',core',chk',obj',bound',ord',orders') ∧
  check_hconcl_list fml obj fmlls' chk' obj' bound' hconcl ⇒
  sem_concl (set fml) obj (hconcl_concl hconcl)
Proof
  rw[]>>
  qmatch_asmsub_abbrev_tac`
    check_csteps_list cs core T obj NONE NONE [] fmlls inds id = _`>>
  `fml_rel (build_fml 1 fml) fmlls` by
    simp[Abbr`fmlls`,fml_rel_FOLDL_update_resize]>>
  `ind_rel fmlls inds` by
    (unabbrev_all_tac>>
    simp[ind_rel_FOLDL_update_resize])>>
  `∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE` by (
    rw[Abbr`id`,Abbr`fmlls`,any_el_ALT]>>
    DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
    simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  `id_ok (build_fml 1 fml) id` by
    fs[id_ok_def,domain_build_fml]>>
  drule check_csteps_check_hconcl>>
  `core = map (λv. ()) (build_fml 1 fml)` by (
    fs[Abbr`core`]>>
    DEP_REWRITE_TAC[spt_eq_thm]>>
    simp[wf_map,wf_fromAList,wf_build_fml]>>
    simp[lookup_fromAList,lookup_map,lookup_build_fml]>>
    simp[ALOOKUP_MAP,ALOOKUP_enumerate])>>
  gvs[]>>
  disch_then drule>>
  fs[range_build_fml]>>
  disch_then match_mp_tac>>
  drule_all fml_rel_check_hconcl_list>>
  metis_tac[]
QED

val _ = export_theory();
