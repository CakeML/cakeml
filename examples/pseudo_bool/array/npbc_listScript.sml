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

Definition check_lstep_list_def:
  (check_lstep_list lstep
    (fml: npbc option list) (inds:num list)
    (mindel:num) (id:num) =
  case lstep of
  | Contradiction n =>
      (case any_el n fml NONE of
        NONE => NONE
      | SOME c =>
        if check_contradiction c
        then SOME (fml, T, id, inds)
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
    (case check_lsteps_list pf fml_not_c (sorted_insert id inds) id (id+1) of
      SOME (fml', T, id' ,inds') =>
        let rfml = rollback fml' id id' in
        (* Optimization: inds' ignored since inds should suffice *)
        SOME(update_resize rfml NONE (SOME c) id', F, (id'+1), sorted_insert id' inds)
    | _ => NONE)) ∧
  (check_lsteps_list [] fml inds mindel id =
    SOME (fml, F, id, inds)) ∧
  (check_lsteps_list (step::steps) fml inds mindel id =
    case check_lstep_list step fml inds mindel id of
      SOME (fml', F, id', inds') =>
        check_lsteps_list steps fml' inds' mindel id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST))’
End

(* id numbers are monotone increasing *)
Theorem check_lstep_list_id:
  (∀step fmlls inds mindel id fmlls' b id' inds'.
  check_lstep_list step fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒ id ≤ id') ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds'.
  check_lsteps_list steps fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒ id ≤ id')
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
  (∀step fmlls inds mindel id fmlls' b id' inds'.
  check_lstep_list step fmlls inds mindel id = SOME (fmlls', b,id',inds') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀steps fmlls inds mindel id fmlls' b id' inds'.
  check_lsteps_list steps fmlls inds mindel id = SOME (fmlls', b,id',inds') ∧
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
    rw[]>>first_x_assum drule
    >- (
      disch_then match_mp_tac>>
      fs[] ) >>
    first_x_assum drule>>
    disch_then drule>>
    rw[])
QED

(* ids below mindel are unchanged *)
Theorem check_lstep_list_mindel:
  (∀step fmlls inds mindel id fmlls' res n.
    check_lstep_list step fmlls inds mindel id = SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒ any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps fmlls inds mindel id fmlls' res n.
    check_lsteps_list steps fmlls inds mindel id = SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒ any_el n fmlls NONE = any_el n fmlls' NONE)
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

Theorem fml_rel_check_lstep_list:
  (∀lstep fmlls inds mindel id fmlls' b id' inds' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_lstep_list lstep fmlls inds mindel id = SOME (fmlls',b,id',inds') ⇒
    case check_lstep lstep fml id of
      Unsat idd => idd = id' ∧ b
    | Cont fml' idd => idd = id' ∧ fml_rel fml' fmlls' ∧ ¬ b
    | _ => F) ∧
  (∀lsteps fmlls inds mindel id fmlls' b id' inds' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_lsteps_list lsteps fmlls inds mindel id = SOME (fmlls',b,id',inds') ⇒
    case check_lsteps lsteps fml id of
      Unsat idd => idd = id' ∧ b
    | Cont fml' idd => idd = id' ∧ fml_rel fml' fmlls' ∧ ¬ b
    | _ => F)
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs [AllCaseEqs(),check_lstep_def,check_lstep_list_def]
    >- ( (* Contradiction *)
      fs[fml_rel_def]>>
      last_x_assum(qspec_then`n` assume_tac)>>fs[])
    >- (* Deletion *)
      metis_tac[fml_rel_list_delete_list]
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
      TOP_CASE_TAC>>rw[]>>gs[]>>
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
  >- (
    fs[check_lstep_list_def,check_lstep_def] >>
    rw[])
  >- (
    pop_assum mp_tac>>
    simp[Once check_lstep_list_def,AllCaseEqs()] >>
    rw[]>>first_x_assum drule>>
    disch_then drule>>fs[]
    >- (
      strip_tac>>simp[Once check_lstep_def]>>
      every_case_tac>>fs[])
    >> (
      TOP_CASE_TAC>>simp[]>>
      rw[]>>
      first_x_assum drule>>
      impl_tac >- (
        drule (hd (CONJUNCTS check_lstep_list_id))>>
        simp[]>>
        rw[]>>
        drule (el 1 (CONJUNCTS check_lstep_list_id_upper))>>
        disch_then match_mp_tac>>fs[])>>
      strip_tac>>simp[Once check_lstep_def]))
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
  (∀lstep fmlls inds mindel id fmlls' b id' inds'.
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_lstep_list lstep fmlls inds mindel id = SOME (fmlls',b,id',inds') ⇒
    ind_rel fmlls' inds') ∧
  (∀lsteps fmlls inds mindel id fmlls' b id' inds'.
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_lsteps_list lsteps fmlls inds mindel id = SOME (fmlls', b,id',inds') ⇒
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
  (check_red_list [] fml inds mindel id = SOME(fml,id)) ∧
  (check_red_list ((copt,pf)::pfs) fml inds mindel id =
    case copt of
      NONE => (* no clause given *)
      (case check_lsteps_list pf fml inds mindel id of
        SOME (fml', F, id', inds') =>
        check_red_list pfs fml' inds' mindel id'
      | res => NONE)
    | SOME c =>
      let cfml = update_resize fml NONE (SOME (npbc$not c)) id in
      case check_lsteps_list pf cfml (sorted_insert id inds) id (id+1) of
        SOME (fml', T, id', inds') =>
        let rfml = rollback fml' id id' in
          check_red_list pfs rfml inds' mindel id'
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

Definition extract_clauses_list_def:
  (extract_clauses_list s def fml [] acc = SOME (REVERSE acc)) ∧
  (extract_clauses_list s def fml (cpf::pfs) acc =
    case cpf of
      (NONE,pf) => extract_clauses_list s def fml pfs ((NONE,pf)::acc)
    | (SOME (INL n),pf) =>
      (case any_el n fml NONE of
        NONE => NONE
      | SOME c => extract_clauses_list s def fml pfs ((SOME (subst_subst_fun s c),pf)::acc))
    | (SOME (INR u),pf) =>
      extract_clauses_list s def fml pfs ((SOME (subst_subst_fun s def),pf)::acc))
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) (fml: npbc option list) (inds:num list) (id:num) =
  case sstep of
  | Lstep lstep =>
    check_lstep_list lstep fml inds 0 id
  | Red c s pfs =>
    (let rinds = reindex fml inds in
     let fml_not_c = update_resize fml NONE (SOME (not c)) id in
      case extract_clauses_list s c fml pfs [] of
        NONE => NONE
      | SOME cpfs =>
        case check_red_list cpfs fml_not_c (sorted_insert id rinds) id (id+1) of
          SOME(fml', id') =>
          let rfml = rollback fml' id id' in
          let pids = MAP FST pfs in
          if MEM (SOME (INR ())) (MAP FST pfs) ∧
            EVERY (λid. MEM (SOME (INL id)) (MAP FST pfs)) (subst_indexes s rfml rinds)
          then
            SOME(update_resize rfml NONE (SOME c) id', F, (id'+1), sorted_insert id' rinds)
          else NONE
        | NONE => NONE))
End

Theorem fml_rel_extract_clauses_list:
  ∀ls f def fml fmlls acc.
  fml_rel fml fmlls ⇒
  extract_clauses (subst_fun f) def fml ls acc = extract_clauses_list f def fmlls ls acc
Proof
  Induct>>rw[extract_clauses_def,extract_clauses_list_def]>>
  every_case_tac>>fs[]>>
  fs[fml_rel_def,subst_subst_fun_def]>>
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
  ∀pfs fmlls inds mindel id fmlls' id' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_red_list pfs fmlls inds mindel id = SOME (fmlls', id') ⇒
    check_red pfs fml id = SOME id'
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
  every_case_tac>>fs[]>>rw[]>>
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
  ∀pfs fmlls inds mindel id fmlls' id'.
    check_red_list pfs fmlls inds mindel id = SOME (fmlls', id') ⇒
    id ≤ id'
Proof
  ho_match_mp_tac check_red_list_ind>>rw[check_red_list_def]>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_lstep_list_id>>
  fs[]
QED

Theorem check_red_list_id_upper:
  ∀pfs fmlls inds mindel id fmlls' id'.
  check_red_list pfs fmlls inds mindel id = SOME (fmlls', id') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)
Proof
  ho_match_mp_tac check_red_list_ind>>
  simp[check_red_list_def]>>
  ntac 10 strip_tac>>
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
  ∀pfs fmlls inds mindel id fmlls' id' n.
  check_red_list pfs fmlls inds mindel id = SOME (fmlls', id') ∧
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
  ∀sstep fmlls inds id fmlls' b id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_sstep_list sstep fmlls inds id = SOME (fmlls',b,id',inds') ⇒
    case check_sstep sstep fml id of
      Unsat idd => idd = id' ∧ id ≤ id' ∧ b
    | Cont fml' idd =>
      idd = id' ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      id ≤ id' ∧
      ¬ b
    | _ => F
Proof
  Cases>>rw[]>>fs[check_sstep_list_def,check_sstep_def]
  >- (
    drule (CONJUNCT1 fml_rel_check_lstep_list)>>
    `0 ≤ id` by fs[]>>
    rpt (disch_then drule)>>
    drule (CONJUNCT1 ind_rel_check_lstep_list)>>
    rpt (disch_then drule)>>
    TOP_CASE_TAC>>gvs[]
    >- (
      drule (CONJUNCT1 check_lstep_list_id)>>
      fs[])>>
    drule (CONJUNCT1 check_lstep_list_id)>>
    simp[]>>
    drule (CONJUNCT1 check_lstep_list_id_upper)>>
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
    `EVERY (λid. MEM (SOME (INL id)) (MAP FST l)) (MAP FST (toAList (map_opt (subst_opt (subst_fun s)) fml)))` by (
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

val _ = export_theory();
