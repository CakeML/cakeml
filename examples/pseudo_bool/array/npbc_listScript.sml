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

Definition check_red_list_def:
  (check_red_list [] core fml inds mindel id = SOME(fml,id)) ∧
  (check_red_list ((cnopt,pf)::pfs) core fml inds mindel id =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps_list pf core fml inds mindel id of
        SOME (fml', id', inds') =>
        check_red_list pfs core fml' inds' mindel id'
      | res => NONE)
    | SOME (c,n) =>
      let cfml = update_resize fml NONE (SOME (npbc$not c)) id in
      case check_lsteps_list pf core cfml (sorted_insert id inds) id (id+1) of
        SOME (fml', id', inds') =>
        if check_contradiction_fml_list fml' n then
          let rfml = rollback fml' id id' in
            check_red_list pfs core rfml inds' mindel id'
        else NONE
      | _ => NONE)
End

(* Make inds non-lazy *)
Definition reindex_def:
  (reindex fml [] = []) ∧
  (reindex fml (i::is) =
  case any_el i fml NONE of
    NONE => reindex fml is
  | SOME v =>
    i :: reindex fml is)
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
    | SOME c => i::subst_indexes s fml is)
End

Definition subst_subst_fun_def:
  subst_subst_fun s c = subst (subst_fun s) c
End

Definition get_red_constraint_subst_fun_def:
  get_red_constraint_subst_fun u s def obj =
  if u = 0 then
    SOME (subst (subst_fun s) def)
  else if u = (1:num) then
    case obj of NONE => NONE
    | SOME l =>
    SOME (obj_constraint (subst_fun s) l)
  else NONE
End

Definition extract_clauses_list_def:
  (extract_clauses_list s def fml obj [] acc = SOME (REVERSE acc)) ∧
  (extract_clauses_list s def fml obj (cpf::pfs) acc =
    case cpf of
      (NONE,pf) => extract_clauses_list s def fml obj pfs ((NONE,pf)::acc)
    | (SOME (INL n,i),pf) =>
      (case any_el n fml NONE of
        NONE => NONE
      | SOME c => extract_clauses_list s def fml obj pfs ((SOME (subst_subst_fun s c,i),pf)::acc))
    | (SOME (INR u,i),pf) =>
      case get_red_constraint_subst_fun u s def obj of
        NONE => NONE
      | SOME c =>
        extract_clauses_list s def fml obj pfs
          ((SOME (c,i),pf)::acc))
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) obj core (fml: npbc option list) (inds:num list) (id:num) =
  case sstep of
  | Lstep lstep =>
    check_lstep_list lstep core fml inds 0 id
  | Red c s pfs =>
    (let rinds = reindex fml inds in
     let fml_not_c = update_resize fml NONE (SOME (not c)) id in
      case extract_clauses_list s c fml obj pfs [] of
        NONE => NONE
      | SOME cpfs =>
        case check_red_list cpfs core fml_not_c (sorted_insert id rinds) id (id+1) of
          SOME(fml', id') =>
          let rfml = rollback fml' id id' in
          let pids = extract_pids pfs in
          if check_red_obj obj pids ∧
            EVERY (λid. MEM (INL id) pids) (subst_indexes s rfml rinds)
          then
            SOME(update_resize rfml NONE (SOME c) id', (id'+1), sorted_insert id' rinds)
          else NONE
        | NONE => NONE))
End

Theorem fml_rel_extract_clauses_list:
  ∀ls s def fml fmlls obj acc.
  fml_rel fml fmlls ⇒
  extract_clauses (subst_fun s) def fml obj ls acc =
  extract_clauses_list s def fmlls obj ls acc
Proof
  Induct>>rw[extract_clauses_def,extract_clauses_list_def]>>
  every_case_tac>>fs[]>>
  fs[fml_rel_def,subst_subst_fun_def,get_red_constraint_subst_fun_def,get_red_constraint_def]>>
  metis_tac[SOME_11,NOT_SOME_NONE]
QED

Theorem ind_rel_rollback:
  ind_rel fmlls inds ⇒
  ind_rel (rollback fmlls id id') inds
Proof
  rw[rollback_def]>>
  metis_tac[ind_rel_list_delete_list]
QED

Theorem fml_rel_check_red_list:
  ∀pfs core fmlls inds mindel id fmlls' id' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_red_list pfs core fmlls inds mindel id = SOME (fmlls', id') ⇒
    check_red pfs core fml id = SOME id'
Proof
  ho_match_mp_tac check_red_list_ind>>rw[]>>
  fs[check_red_def,check_red_list_def]>>
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
  `fml_rel (insert id (not c) fml)  (update_resize fmlls NONE (SOME (not c)) id)` by
    metis_tac[fml_rel_update_resize]>>
  drule (CONJUNCT2 fml_rel_check_lstep_list)>>
  disch_then (drule_at Any)>>
  simp[any_el_update_resize]>>
  rw[]>>
  simp[]>>
  CONJ_TAC >- metis_tac[fml_rel_check_contradiction_fml]>>
  first_x_assum match_mp_tac>>
  rw[]
  >- (
    match_mp_tac fml_rel_rollback>>rw[]
    >- (
      drule (CONJUNCT2 check_lstep_list_mindel)>>
      simp[any_el_update_resize])>>
    first_assum(qspec_then`n` mp_tac)>>
    drule (CONJUNCT2 check_lstep_list_id)>>
    simp[]>>rw[]>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])
  >- (
    drule ind_rel_update_resize_sorted_insert>>
    disch_then(qspecl_then[`SOME (not c)`,`id`] assume_tac)>>
    drule (CONJUNCT2 ind_rel_check_lstep_list)>>
    disch_then (drule_at Any)>>
    simp[any_el_update_resize]>>
    metis_tac[ind_rel_rollback])
  >- (
    fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    disch_then match_mp_tac>>
    simp[any_el_update_resize])>>
  imp_res_tac check_lstep_list_id>>
  fs[]
QED

Theorem check_red_list_id:
  ∀pfs core fmlls inds mindel id fmlls' id'.
    check_red_list pfs core fmlls inds mindel id = SOME (fmlls', id') ⇒
    id ≤ id'
Proof
  ho_match_mp_tac check_red_list_ind>>rw[check_red_list_def]>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_lstep_list_id>>
  fs[]
QED

Theorem check_red_list_id_upper:
  ∀pfs core fmlls inds mindel id fmlls' id'.
  check_red_list pfs core fmlls inds mindel id = SOME (fmlls', id') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)
Proof
  ho_match_mp_tac check_red_list_ind>>
  simp[check_red_list_def]>>
  ntac 11 strip_tac>>
  simp[AllCaseEqs()]>>
  strip_tac>>gvs[]
  >- (
    first_x_assum match_mp_tac>>
    match_mp_tac (CONJUNCT2 check_lstep_list_id_upper)>>
    metis_tac[])>>
  first_x_assum match_mp_tac>>
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  match_mp_tac (CONJUNCT2 check_lstep_list_id_upper)>>
  first_x_assum (irule_at Any)>>
  simp[any_el_update_resize]
QED

Theorem check_red_list_mindel:
  ∀pfs core fmlls inds mindel id fmlls' id' n.
  check_red_list pfs core fmlls inds mindel id = SOME (fmlls', id') ∧
  mindel ≤ id ∧
  n < mindel ⇒
  any_el n fmlls NONE = any_el n fmlls' NONE
Proof
  ho_match_mp_tac check_red_list_ind>>
  simp[check_red_list_def]>>rw[]>>
  gvs[AllCaseEqs()]
  >- (
    drule (CONJUNCT2 check_lstep_list_mindel)>>fs[]>>
    drule (CONJUNCT2 check_lstep_list_id)>>fs[]>>
    disch_then drule>>
    simp[])>>
  drule (CONJUNCT2 check_lstep_list_mindel)>>fs[]>>
  simp[any_el_update_resize]>>
  fs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  drule (CONJUNCT2 check_lstep_list_id)>>fs[]
QED

Theorem reindex_characterize:
  ∀inds inds'.
  reindex fmlls inds = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds
Proof
  Induct>>fs[reindex_def] >>
  rw[]>>every_case_tac>>fs[]
QED

Theorem ind_rel_reindex:
  ind_rel fml inds ⇒
  ind_rel fml (reindex fml inds)
Proof
  simp[ind_rel_def,reindex_characterize,MEM_FILTER]
QED

Theorem MEM_subst_indexes:
  ∀inds i c.
  MEM i inds ∧
  any_el i fml NONE = SOME c ∧
  subst_opt (subst_fun s) c = SOME res
  ⇒
  MEM i (subst_indexes s fml inds)
Proof
  Induct>>rw[subst_indexes_def]>>
  every_case_tac>>
  fs[AllCaseEqs(),any_el_def]>>
  rw[]>>
  fs[subst_opt_subst_fun_def]
QED

Theorem fml_rel_check_sstep_list:
  ∀sstep obj core fmlls inds id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_sstep_list sstep obj core fmlls inds id = SOME (fmlls',id',inds') ⇒
    ∃fml'.
      check_sstep sstep obj core fml id = SOME(fml',id') ∧
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
    DEP_REWRITE_TAC [fml_rel_extract_clauses_list]>> simp[]>>
    gvs[AllCaseEqs()]>>
    `fml_rel (insert id (not p) fml) (update_resize fmlls NONE (SOME (not p)) id)` by
      metis_tac[fml_rel_update_resize]>>
    drule fml_rel_check_red_list>>
    disch_then (drule_at Any)>>
    impl_tac>- (
      rw[]
      >- (
        match_mp_tac ind_rel_update_resize_sorted_insert>>
        metis_tac[ind_rel_reindex] )>>
      simp[any_el_update_resize])>>
    simp[]>>strip_tac>>
    drule check_red_list_id>>
    drule check_red_list_id_upper>>
    drule check_red_list_mindel>>
    simp[any_el_update_resize]>>
    ntac 3 strip_tac>>
    CONJ_ASM1_TAC >- (
      fs[EVERY_MEM,MEM_MAP,EXISTS_PROD]>>rw[]>>
      fs[MEM_toAList,lookup_map_opt,AllCaseEqs()]>>
      first_x_assum match_mp_tac>>
      match_mp_tac (GEN_ALL MEM_subst_indexes)>>
      first_x_assum (irule_at Any)>>
      CONJ_TAC>- (
        simp[reindex_characterize,MEM_FILTER]>>
        fs[fml_rel_def,ind_rel_def])>>
      simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
      rw[]
      >- (
        last_x_assum(qspec_then`id+y` assume_tac)>>
        fs[fml_rel_def]>>
        last_x_assum(qspec_then`id+y` assume_tac)>>
        fs[])>>
      `id' < id` by (
        CCONTR_TAC>>fs[]>>
        last_x_assum(qspec_then`id'` mp_tac)>>
        impl_tac>-fs[]>>
        fs[fml_rel_def])>>
      first_x_assum drule>>
      fs[fml_rel_def])>>
    simp[]>>
    CONJ_TAC>- (
      match_mp_tac fml_rel_update_resize>>
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_update_resize_sorted_insert>>
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST])
QED

Definition check_ssteps_list_def:
  (check_ssteps_list [] obj core (fml: npbc option list) (inds:num list) (id:num) = SOME (fml, id, inds)) ∧
  (check_ssteps_list (s::ss) obj core fml inds id =
  case check_sstep_list s obj core fml inds id of
    SOME (fml',id',inds') =>
      check_ssteps_list ss obj core fml' inds' id'
  | res => res)
End

Theorem fml_rel_check_ssteps_list:
  ∀ss obj core fmlls inds id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_ssteps_list ss obj core fmlls inds id = SOME (fmlls',id',inds') ⇒
    ∃fml'.
      check_ssteps ss obj core fml id = SOME(fml',id') ∧
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

(* Specialized for UNSAT checking *)
Theorem check_ssteps_list_unsat:
  check_ssteps_list ss NONE LN
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME v) i)
             (REPLICATE (2 * (LENGTH fml + 1)) NONE) (enumerate 1 fml))
    (REVERSE (MAP FST (enumerate 1 fml)))
    (LENGTH fml + 1 )= SOME(fml',b,c) ∧
  check_contradiction_fml_list fml' n
  ⇒
  unsatisfiable (set fml)
Proof
  rw[]>>
  qmatch_asmsub_abbrev_tac`check_ssteps_list ss NONE LN fmlls inds id = _`>>
  `fml_rel (build_fml 1 fml) fmlls` by
    simp[Abbr`fmlls`,fml_rel_FOLDL_update_resize]>>
  `ind_rel fmlls inds` by
    (unabbrev_all_tac>>
    simp[ind_rel_FOLDL_update_resize])>>
  `∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE` by (
    rw[Abbr`id`,Abbr`fmlls`,any_el_ALT]>>
    DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
    simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])>>
  drule_all fml_rel_check_ssteps_list>>
  rw[]>>
  `id_ok (build_fml 1 fml) id` by
    fs[id_ok_def,domain_build_fml]>>
  drule check_ssteps_correct>>
  disch_then(qspecl_then[`ss`,`NONE`,`LN`] mp_tac)>>simp[]>>
  simp[range_build_fml,npbcTheory.sat_obj_def]>>
  drule_all fml_rel_check_contradiction_fml>>
  metis_tac[check_contradiction_fml_unsat,npbcTheory.unsatisfiable_def,npbcTheory.satisfiable_def]
QED

val _ = export_theory();
