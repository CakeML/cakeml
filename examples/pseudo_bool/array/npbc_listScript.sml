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
  (check_cutting_list b fml (Weak c var) =
    OPTION_MAP (λc. weaken c var) (check_cutting_list b fml c))
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
val sorted_insert_def = Define`
  (sorted_insert (x:num) [] = [x]) ∧
  (sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys
    else y::(sorted_insert x ys))`

Definition check_contradiction_fml_list_def:
  check_contradiction_fml_list b fml n =
  case lookup_core_only_list b fml n of
    NONE => F
  | SOME c =>
    check_contradiction c
End

Definition check_lstep_list_def:
  (check_lstep_list lstep
    b (fml: (npbc # bool) option list) (inds:num list)
    (mindel:num) (id:num) =
  case lstep of
  | Check n c =>
    (case any_el n fml NONE of NONE => NONE
    | SOME (c',b) =>
      if c = c' then SOME(fml, inds, id)
      else NONE)
  | NoOp => SOME (fml, inds, id)
  | Delete ls =>
      if EVERY (λid. mindel ≤ id ∧
          lookup_core_only_list T fml id = NONE) ls then
        SOME(list_delete_list ls fml, inds, id)
      else
        NONE
  | Cutting constr =>
    (case check_cutting_list b fml constr of
      NONE => NONE
    | SOME c =>
      SOME (
        update_resize fml NONE (SOME (c,b)) id,
        sorted_insert id inds,
        (id+1))
    )
  | Con c pf n =>
    let fml_not_c = update_resize fml NONE (SOME (not c,b)) id in
    (case check_lsteps_list pf b fml_not_c
      (sorted_insert id inds) id (id+1) of
      SOME (fml',inds',id') =>
      if check_contradiction_fml_list b fml' n then
        let rfml = rollback fml' id id' in
        (* Optimization: inds' ignored since
          inds should suffice *)
        SOME(
          update_resize rfml NONE (SOME (c,b)) id',
          sorted_insert id' inds,
          id'+1)
      else NONE
    | _ => NONE)) ∧
  (check_lsteps_list [] b fml inds mindel id =
    SOME (fml, inds, id)) ∧
  (check_lsteps_list (step::steps) b fml inds mindel id =
    case check_lstep_list step b fml inds mindel id of
      SOME (fml',inds',id') =>
        check_lsteps_list steps b fml' inds' mindel id'
    | res => res)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST))’
End

(* id numbers are monotone increasing *)
Theorem check_lstep_list_id:
  (∀step b fmlls inds mindel id fmlls' id' inds'.
  check_lstep_list step b fmlls inds mindel id =
    SOME (fmlls',inds',id') ⇒
    id ≤ id') ∧
  (∀steps b fmlls inds mindel id fmlls' id' inds'.
  check_lsteps_list steps b fmlls inds mindel id =
    SOME (fmlls',inds',id') ⇒
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
  Induct>>rw[list_delete_list_def,delete_list_def]>>
  gs[any_el_ALT,EL_LUPDATE]
QED

(* id numbers bound those in the formula *)
Theorem check_lstep_list_id_upper:
  (∀step b fmlls inds mindel id fmlls' id' inds'.
  check_lstep_list step b fmlls inds mindel id =
    SOME (fmlls',inds',id') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE)) ∧
  (∀steps b fmlls inds mindel id fmlls' id' inds'.
  check_lsteps_list steps b fmlls inds mindel id =
    SOME (fmlls',inds',id') ∧
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
  (∀step b fmlls inds mindel id fmlls' res n.
    check_lstep_list step b fmlls inds mindel id =
      SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒
      any_el n fmlls NONE = any_el n fmlls' NONE) ∧
  (∀steps b fmlls inds mindel id fmlls' res n.
    check_lsteps_list steps b fmlls inds mindel id =
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

Theorem fml_rel_check_lstep_list:
  (∀lstep b fmlls inds mindel id fmlls' inds' id' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_lstep_list lstep b fmlls inds mindel id =
      SOME (fmlls',inds',id') ⇒
    ∃fml'.
      check_lstep lstep b fml id = SOME (fml',id') ∧
      fml_rel fml' fmlls') ∧
  (∀lsteps b fmlls inds mindel id fmlls' inds' id' fml.
    fml_rel fml fmlls ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_lsteps_list lsteps b fmlls inds mindel id =
      SOME (fmlls',inds',id') ⇒
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
      disch_then(qspecl_then[`b`,`constr`] assume_tac)>>
      fs[insert_fml_def]>>
      metis_tac[fml_rel_update_resize])
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

Theorem ind_rel_check_lstep_list:
  (∀lstep b fmlls inds mindel id fmlls' id' inds'.
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_lstep_list lstep b fmlls inds mindel id =
    SOME (fmlls',inds',id') ⇒
    ind_rel fmlls' inds') ∧
  (∀lsteps b fmlls inds mindel id fmlls' id' inds'.
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  mindel ≤ id ∧
  check_lsteps_list lsteps b fmlls inds mindel id =
    SOME (fmlls',inds',id') ⇒
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

Definition list_insert_fml_list_def:
  (list_insert_fml_list [] b id fml inds =
    (id,fml,inds)) ∧
  (list_insert_fml_list (c::cs) b id fml inds =
    list_insert_fml_list cs b
      (id+1)
      (update_resize fml NONE (SOME (c,b)) id )
      (sorted_insert id inds))
End

Definition check_subproofs_list_def:
  (check_subproofs_list [] b fml inds mindel id =
    SOME(fml,id)) ∧
  (check_subproofs_list ((cnopt,pf)::pfs) b fml inds mindel id =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps_list pf b fml inds mindel id of
        SOME (fml', inds', id') =>
        check_subproofs_list pfs b fml' inds' mindel id'
      | res => NONE)
    | SOME (cs,n) =>
      let (cid,cfml,cinds) =
        list_insert_fml_list cs b id fml inds in
      (* no deletions below id *)
      case check_lsteps_list pf b cfml cinds id cid of
        SOME (fml', inds', id') =>
        if check_contradiction_fml_list b fml' n then
          let rfml = rollback fml' id id' in
            check_subproofs_list pfs b rfml inds' mindel id'
        else NONE
      | _ => NONE)
End

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
  split_goals_hash fmlls extra (proved:num_set)
    (goals:(num # (int # num) list # num) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). lookup i proved ≠ NONE) goals in
  let lf = FILTER (λc. ¬(imp extra c)) (MAP SND lf) in
  let proved = MAP SND lp in
  let hs = mk_hashset fmlls (mk_hashset proved (REPLICATE splim [])) in
  EVERY (λc. in_hashset c hs) lf
End

(* Not meant to be executed, mainly just abbrevation... *)
Definition do_red_check_def:
  do_red_check idopt b fml
    s rfml rinds fmlls extra pfs rsubs =
  case idopt of NONE =>
    let goals = subst_indexes s b rfml rinds in
    let (l,r) = extract_pids pfs LN LN in
      split_goals_hash fmlls extra l goals ∧
      EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH rsubs))
  | SOME cid =>
     check_contradiction_fml_list b fml cid
End

Definition check_red_list_def:
  check_red_list ord obj b fml inds id c s pfs idopt =
  let (rinds,fmlls) = reindex b fml inds in
  let nc = not c in
  let fml_not_c = update_resize fml NONE (SOME (nc,b)) id in
  let rsubs = red_subgoals ord (subst_fun s) c obj in
  case extract_clauses_list s b fml rsubs pfs [] of
    NONE => NONE
  | SOME cpfs =>
    (case check_subproofs_list cpfs b
      fml_not_c (sorted_insert id rinds) id (id+1) of
       NONE => NONE
    |  SOME(fml', id') =>
      let rfml = rollback fml' id id' in
      if do_red_check idopt b fml'
          s rfml rinds fmlls nc pfs rsubs then
          SOME (rfml,rinds,id')
      else NONE)
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) ord obj
    (fml: (npbc # bool) option list) (inds:num list) (id:num) =
  case sstep of
  | Lstep lstep =>
      (check_lstep_list lstep F fml inds 0 id)
  | Red c s pfs idopt =>
    case check_red_list ord obj F fml inds id c s pfs idopt of
      SOME (rfml,rinds,id') =>
      SOME(
        update_resize rfml NONE (SOME (c,F)) id',
        sorted_insert id' rinds,
        id'+1)
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

Theorem ind_rel_rollback:
  ind_rel fmlls inds ⇒
  ind_rel (rollback fmlls id id') inds
Proof
  rw[rollback_def]>>
  metis_tac[ind_rel_list_delete_list]
QED

Theorem list_insert_fml_list_id:
  ∀cs b id fmlls inds cid cfmlls cinds.
  list_insert_fml_list cs b id fmlls inds =
    (cid,cfmlls,cinds) ⇒
  id ≤ cid
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  first_x_assum drule>>
  simp[]
QED

Theorem list_insert_fml_list_id_upper:
  ∀cs b id fmlls inds cid cfmlls cinds.
  list_insert_fml_list cs b id fmlls inds =
    (cid,cfmlls,cinds) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ⇒
  (∀n. n ≥ cid ⇒ any_el n cfmlls NONE = NONE)
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem list_insert_fml_list_mindel:
  ∀cs b id fmlls inds cid cfmlls cinds.
  list_insert_fml_list cs b id fmlls inds =
    (cid,cfmlls,cinds) ⇒
  (∀n. n < id ⇒ any_el n cfmlls NONE = any_el n fmlls NONE)
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem fml_rel_list_insert_fml_list:
  ∀cs b id fml fmlls inds cid cfml cid' cfmlls cinds.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  list_insert_fml b fml id cs = (cfml,cid) ∧
  list_insert_fml_list cs b id fmlls inds =
    (cid',cfmlls,cinds) ⇒
  cid = cid' ∧
  fml_rel cfml cfmlls ∧
  ind_rel cfmlls cinds ∧
  (∀n. n ≥ cid ⇒ any_el n cfmlls NONE = NONE) ∧
  (∀n. n < id ⇒ any_el n cfmlls NONE = any_el n fmlls NONE) ∧
  id ≤ cid
Proof
  Induct>>
  simp[list_insert_fml_def,list_insert_fml_list_def]>>
  ntac 12 strip_tac>>
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
  ∀pfs b fmlls inds mindel id fmlls' id' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    mindel ≤ id ∧
    check_subproofs_list pfs b fmlls inds mindel id =
      SOME (fmlls', id') ⇒
    ∃fml'.
      check_subproofs pfs b fml id = SOME (fml',id') ∧
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
  ∀pfs b fmlls inds mindel id fmlls' id'.
    check_subproofs_list pfs b fmlls inds mindel id =
    SOME (fmlls', id') ⇒
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
  ∀pfs b fmlls inds mindel id fmlls' id'.
  check_subproofs_list pfs b fmlls inds mindel id =
    SOME (fmlls', id') ∧
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
  metis_tac[list_insert_fml_list_id_upper]
QED

Theorem check_subproofs_list_mindel:
  ∀pfs b fmlls inds mindel id fmlls' id' n.
  check_subproofs_list pfs b fmlls inds mindel id =
    SOME (fmlls', id') ∧
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

Theorem reindex_aux:
  ∀inds iacc vacc.
  reindex_aux b fmlls inds iacc vacc =
  let is = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds in
  let vs =
    MAP (λx. THE (lookup_core_only_list b fmlls x))
    (FILTER (λx. IS_SOME (lookup_core_only_list b fmlls x))
      inds) in
  (REVERSE iacc ++ is, REVERSE vs ++ vacc)
Proof
  Induct>>rw[reindex_aux_def]>>
  gvs[lookup_core_only_list_def,IS_SOME_EXISTS,AllCaseEqs()]
QED

Theorem FST_reindex_characterize:
  reindex b fmlls inds = (is,vs) ⇒
  is = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds
Proof
  rw[reindex_def,reindex_aux]
QED

Theorem SND_reindex_characterize:
  fml_rel fml fmlls ∧
  reindex b fmlls inds = (is,vs) ⇒
  set vs ⊆ core_only_fml b fml
Proof
  rw[reindex_def,reindex_aux]>>
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

Theorem ind_rel_reindex:
  ind_rel fml inds ∧
  reindex b fml inds = (is,vs) ⇒
  ind_rel fml is
Proof
  rw[]>>drule FST_reindex_characterize>>
  fs[ind_rel_def,MEM_FILTER]
QED

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
  pairarg_tac>>fs[]>>
  fs[EVERY_FILTER,EVERY_MAP]>>
  qpat_x_assum`EVERY _ _`mp_tac>> match_mp_tac MONO_EVERY>>
  simp[FORALL_PROD, METIS_PROVE []``(¬P ⇒ Q) ⇔ P ∨ Q``]>>
  rw[]
  >-
    simp[]>>
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

Theorem fml_rel_check_red_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_red_list ord obj b fmlls inds id c s pfs idopt =
    SOME (fmlls', inds', id') ⇒
    check_red ord obj b fml id c s pfs idopt = SOME id' ∧
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
  `fml_rel (insert id ((not c,b)) fml)
    (update_resize fmlls NONE (SOME (not c,b)) id)` by
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
    gvs[do_red_check_def,AllCaseEqs(),insert_fml_def]>>
    TOP_CASE_TAC>>fs[]
    >- (
      rpt (pairarg_tac>>fs[])>>
      (drule_at Any) split_goals_hash_imp_split_goals>>
      disch_then (qspec_then`mk_core_fml b fml` mp_tac)>>
      impl_tac >- (
        simp[range_mk_core_fml]>>
        match_mp_tac (GEN_ALL SND_reindex_characterize)>>
        metis_tac[])>>
      match_mp_tac split_goals_same_goals>>
      simp[EXTENSION,FORALL_PROD]>>
      rw[]>>eq_tac>>rw[]
      >- (
        fs[MEM_toAList,lookup_map_opt,AllCaseEqs()]>>
        match_mp_tac (GEN_ALL MEM_subst_indexes)>>
        gvs[lookup_mk_core_fml]>>
        first_x_assum (irule_at Any)>>
        `∃b'.
          lookup p_1 fml = SOME (x',b') ∧
          (b ⇒ b')` by (
          gvs[lookup_core_only_def,AllCaseEqs()])>>
        CONJ_TAC>- (
          drule FST_reindex_characterize>>
          simp[MEM_FILTER]>>
          fs[fml_rel_def,ind_rel_def])>>
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
      drule FST_reindex_characterize>>
      strip_tac>>gvs[]>>
      fs[rollback_def,lookup_core_only_list_list_delete_list,MEM_MAP,MEM_COUNT_LIST,MEM_FILTER]>>
      `p_1 < id` by (
        CCONTR_TAC>>fs[]>>
        last_x_assum(qspec_then`p_1` mp_tac)>>
        impl_tac>-fs[]>>
        metis_tac[option_CLAUSES])>>
      simp[lookup_mk_core_fml]>>
      `lookup_core_only b fml p_1 = SOME c'` by (
        qpat_x_assum`fml_rel fml _` assume_tac>>
        drule (GSYM fml_rel_lookup_core_only)>>
        strip_tac>>fs[]>>
        gvs[lookup_core_only_list_def,AllCaseEqs()])>>
      fs[])>>
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
  ∀sstep ord obj fmlls inds id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_sstep_list sstep ord obj fmlls inds id =
      SOME (fmlls',inds',id') ⇒
    ∃fml'.
      check_sstep sstep ord obj fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      id ≤ id'
Proof
  Cases>>rw[]>>fs[check_sstep_list_def,check_sstep_def]
  >- (
    `0 ≤ id` by fs[]>>
    drule_all (CONJUNCT1 fml_rel_check_lstep_list)>>
    drule_all (CONJUNCT1 ind_rel_check_lstep_list)>>
    rw[]>>gs[]>>
    CONJ_TAC
    >- (
      drule (CONJUNCT1 check_lstep_list_id_upper)>>
      simp[])>>
    drule (CONJUNCT1 check_lstep_list_id)>>
    simp[])
  >- ( (* Red*)
    gvs[AllCaseEqs(),insert_fml_def]>>
    drule_all fml_rel_check_red_list>>
    simp[]>>rw[]
    >-
      metis_tac[fml_rel_update_resize]
    >-
      metis_tac[ind_rel_update_resize_sorted_insert]>>
    simp[any_el_update_resize])
QED

Definition check_ssteps_list_def:
  (check_ssteps_list [] ord obj
    (fml: (npbc # bool) option list) (inds:num list) (id:num) =
    SOME (fml, inds, id)) ∧
  (check_ssteps_list (s::ss) ord obj fml inds id =
  case check_sstep_list s ord obj fml inds id of
    SOME (fml', inds', id') =>
      check_ssteps_list ss ord obj fml' inds' id'
  | res => res)
End

Theorem fml_rel_check_ssteps_list:
  ∀ss ord obj fmlls inds id fmlls' id' inds' fml.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_ssteps_list ss ord obj fmlls inds id =
      SOME (fmlls',inds',id') ⇒
    ∃fml'.
      check_ssteps ss ord obj fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧
      ind_rel fmlls' inds' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' NONE = NONE) ∧
      id ≤ id'
Proof
  Induct>>rw[check_ssteps_list_def]>>
  simp[check_ssteps_def]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_check_sstep_list>>
  rw[]>>
  first_x_assum drule_all>>
  rw[]>>
  fs[]
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
  do_dom_check idopt fml rfml w indcore indfml extra pfs dsubs =
  case idopt of NONE =>
    let goals =
      MAP_OPT (subst_opt w) indcore in
    let (l,r) = extract_pids pfs LN LN in
    if EVERY (λid. lookup id r ≠ NONE) (COUNT_LIST (LENGTH dsubs))
    then
      split_goals_hash indfml extra l goals
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

Definition check_cstep_list_def:
  check_cstep_list cstep chk obj bound
    ord orders fml inds id =
  case cstep of
    Dom c s pfs idopt =>
    (case ord of NONE => NONE
    | SOME spo =>
    ( let nc = not c in
      let (rinds,fmlls) = reindex F fml inds in
      let corels = core_fmlls fml rinds in
      let fml_not_c = update_resize fml NONE (SOME (nc,F)) id in
      let w = subst_fun s in
      let dsubs = dom_subgoals spo w c obj in
      case extract_clauses_list s F fml dsubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
        (case check_subproofs_list cpfs F fml_not_c (sorted_insert id rinds) id (id+1) of
          NONE => NONE
        | SOME (fml',id') =>
          let rfml = rollback fml' id id' in
          if do_dom_check idopt fml' rfml w corels fmlls nc pfs dsubs then
            SOME(
              update_resize rfml NONE (SOME (c,F)) id',
              sorted_insert id' rinds,
              id'+1, chk, obj, bound, ord, orders)
          else NONE)))
  | LoadOrder nn xs =>
    (let inds' = FST (reindex F fml inds) in
      case ALOOKUP orders nn of NONE => NONE
      | SOME ord' =>
        if LENGTH xs = LENGTH (FST (SND ord')) then
          case core_from_inds fml inds' of NONE => NONE
          | SOME fml' =>
          SOME (fml',inds',id,
            chk, obj, bound, SOME (ord',xs),orders)
        else NONE)
  | UnloadOrder =>
    (case ord of NONE => NONE
    | SOME spo =>
        SOME (fml,inds,id,chk, obj, bound, NONE, orders))
  | StoreOrder nn spo ws pfs =>
    if check_good_ord spo ∧ check_ws spo ws ∧
       check_transitivity spo ws pfs then
        SOME (fml,inds,id,chk, obj, bound, ord, (nn,spo)::orders)
    else
      NONE
  | Transfer ls =>
    (case core_from_inds fml ls of NONE => NONE
    | SOME fml' =>
      SOME (fml', inds, id,
           chk, obj, bound, ord, orders))
  | CheckedDelete n s pfs idopt => (
    case lookup_core_only_list T fml n of
      NONE => NONE
    | SOME c =>
        (let nfml = delete_list n fml in
        case check_red_list ord obj T nfml inds id c s pfs idopt of
          SOME (ncf',inds',id') =>
          SOME (ncf', inds', id',
            chk, obj, bound, ord, orders)
        | NONE => NONE) )
  | UncheckedDelete ls => (
    if ord = NONE then
      SOME (list_delete_list ls fml, inds, id,
            F, obj, bound, ord, orders)
    else
      case all_core_list fml inds [] of NONE => NONE
      | SOME inds' =>
        SOME (list_delete_list ls fml, inds', id,
            F, obj, bound, ord, orders))
  | Sstep sstep =>
    (case check_sstep_list sstep ord obj fml inds id of
      SOME(fml',inds',id') =>
        SOME(fml',inds',id', chk, obj, bound, ord, orders)
    | NONE => NONE)
  | Obj w mi bopt =>
    (
    let corels = core_fmlls fml inds in
    case check_obj obj w (MAP SND corels) bopt of
      NONE => NONE
    | SOME new =>
      let bound' = update_bound chk bound new in
      if mi then
        (* no model improving constraint in unchecked *)
        if ¬chk then NONE else
        let c = model_improving obj new in
        SOME (
          update_resize fml NONE (SOME (c,T)) id,
          sorted_insert id inds,
          id+1,
          chk, obj, bound', ord, orders)
      else
        SOME(fml,inds,id,chk,obj,bound',ord,orders))
  | ChangeObj fc' n1 n2 =>
    NONE
    (* if check_change_obj_list fml core chk obj ord fc' n1 n2 then
      SOME (
      fml, inds, id, core, chk, SOME fc', bound, ord, orders)
    else NONE *)
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

Theorem fml_rel_all_core:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  all_core_list fmlls inds acc = SOME inds' ⇒
  all_core fml ∧
  ind_rel fmlls inds'
Proof
  cheat
QED

Theorem check_obj_cong:
  set ls = set ls' ⇒
  check_obj obj s ls ob = check_obj obj s ls' ob
Proof
  cheat
QED

Theorem fml_rel_check_cstep_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
  check_cstep_list cstep chk obj bound ord orders
    fmlls inds id =
    SOME (fmlls',inds',id',rest) ⇒
  ∃fml'.
    check_cstep cstep fml id chk obj bound ord orders =
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
    disch_then(qspec_then`insert id (not p,F) fml` mp_tac)>>
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
    gvs[insert_fml_def]>>
    CONJ_TAC>- (
      fs[do_dom_check_def]>>
      every_case_tac>>fs[]
      >- (
        (drule_at Any) split_goals_hash_imp_split_goals>>
        disch_then(qspec_then `mk_core_fml F fml` mp_tac)>>
        impl_tac >- (
          drule_all (GEN_ALL SND_reindex_characterize)>>
          simp[range_mk_core_fml])>>
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
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST])
  >- ( (* LoadOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    Cases_on`reindex F fmlls inds`>>
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
    fs[ind_rel_def]>>
    rw[]>>
    metis_tac[IS_SOME_EXISTS,option_CLAUSES])
  >- ( (* UnloadOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >- ( (* StoreOrder *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >- ( (* Transfer *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all core_from_inds_do_transfer>>
    drule any_el_core_from_inds>>
    strip_tac>>fs[]>>
    fs[ind_rel_def]>>
    rw[]>>
    metis_tac[IS_SOME_EXISTS,option_CLAUSES])
  >- ( (* CheckedDelete *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule fml_rel_lookup_core_only>>
    rw[]>>gvs[]>>
    drule_at (Pos last) fml_rel_check_red_list>>
    disch_then match_mp_tac>>
    CONJ_TAC >- (
      drule fml_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>
      simp[list_delete_list_def])>>
    CONJ_TAC >- (
      drule ind_rel_list_delete_list>>
      disch_then(qspec_then`[n]` mp_tac)>>
      simp[list_delete_list_def])>>
    metis_tac[any_el_list_delete_list,list_delete_list_def])
  >- ((* UncheckedDelete *)
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]
    >- (
      CONJ_TAC >-
        metis_tac[fml_rel_list_delete_list]>>
      CONJ_TAC >-
        metis_tac[ind_rel_list_delete_list]>>
      simp[any_el_list_delete_list])
    >- (
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
    rw[PULL_EXISTS]>>
    `set (MAP SND (core_fmlls fmlls inds)) =
      set (MAP SND (toAList (mk_core_fml T fml)))` by (
      rw[EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,MEM_core_fmlls]>>
      simp[lookup_mk_core_fml]>>
      metis_tac[ind_rel_lookup_core_only_list,fml_rel_lookup_core_only])>>
    drule check_obj_cong>>rw[]>>fs[]>>
    rw[]>>gvs[]
    >- metis_tac[fml_rel_update_resize]
    >- metis_tac[ind_rel_update_resize_sorted_insert]>>
    simp[any_el_update_resize])
  >-
    fs[check_cstep_def,check_cstep_list_def]
  (* >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    gvs[check_change_obj_list_def,check_change_obj_def]>>
    gs[fml_rel_def]) *)
QED

Definition check_csteps_list_def:
  (check_csteps_list [] chk obj bound
    ord orders fml inds id =
    SOME
      (fml, inds, id, chk, obj, bound, ord, orders)) ∧
  (check_csteps_list (c::cs) chk obj bound
    ord orders fml inds id =
    case check_cstep_list c chk obj bound
      ord orders fml inds id of
      NONE => NONE
    | SOME(fml', inds', id',
      chk', obj', bound', ord', orders') =>
      check_csteps_list cs chk' obj' bound'
        ord' orders' fml' inds' id')
End

Theorem fml_rel_check_csteps_list:
  ∀csteps chk obj bound ord orders fmlls inds id
    fmlls' inds' id' fml rest.
    fml_rel fml fmlls ∧
    ind_rel fmlls inds ∧
    (∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE) ∧
    check_csteps_list csteps chk obj bound
      ord orders fmlls inds id =
    SOME (fmlls', inds', id', rest) ⇒
    ∃fml'.
      check_csteps csteps fml id chk obj bound
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

Definition check_implies_fml_list_def:
  check_implies_fml_list fml n c =
  (case any_el n fml NONE of
      NONE => F
    | SOME (ci,_) =>
      imp ci c)
End

Definition check_hconcl_list_def:
  (check_hconcl_list fml obj fml' obj' bound' HNoConcl = T) ∧
  (check_hconcl_list fml obj fml' obj' bound' (HDSat wopt) =
    case wopt of
      NONE =>
      bound' ≠ NONE
    | SOME wm =>
      check_obj obj wm fml NONE ≠ NONE) ∧
  (check_hconcl_list fml obj fml' obj' bound' (HDUnsat n) =
    (bound' = NONE ∧
      check_contradiction_fml_list F fml' n)) ∧
  (check_hconcl_list fml obj fml' obj' bound'
    (HOBounds lbi ubi n wopt) =
    (
    (opt_le lbi bound' ∧
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
  check_hconcl_list fml obj fmlls' obj' bound' hconcl ⇒
  check_hconcl fml obj fml' obj' bound' hconcl
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

(*
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
  fml_rel (build_fml T k fml)
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
*)

Theorem check_csteps_list_concl:
  check_csteps_list cs
    T obj NONE NONE []
    (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,T)) i)
      (REPLICATE m NONE) (enumerate 1 fml))
    (REVERSE (MAP FST (enumerate 1 fml)))
    (LENGTH fml + 1) =
    SOME(fmlls',inds',id',chk',obj',bound',ord',orders') ∧
  check_hconcl_list fml obj fmlls' obj' bound' hconcl ⇒
  sem_concl (set fml) obj (hconcl_concl hconcl)
Proof
  rw[]>>
  qmatch_asmsub_abbrev_tac`
    check_csteps_list cs T obj NONE NONE [] fmlls inds id = _`>>
  `fml_rel (build_fml T 1 fml) fmlls` by
    cheat>>
    (*
    simp[Abbr`fmlls`,fml_rel_FOLDL_update_resize]>> *)
  `ind_rel fmlls inds` by
    cheat>>
    (*(unabbrev_all_tac>>
    simp[ind_rel_FOLDL_update_resize])>> *)
  `∀n. n ≥ id ⇒ any_el n fmlls NONE = NONE` by
    cheat
    (*(
    rw[Abbr`id`,Abbr`fmlls`,any_el_ALT]>>
    DEP_REWRITE_TAC [FOLDL_update_resize_lookup]>>
    simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])*)>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  `id_ok (build_fml T 1 fml) id` by
    fs[id_ok_def,domain_build_fml]>>
  `all_core (build_fml T 1 fml)` by cheat>>
  drule check_csteps_check_hconcl>>
  rpt(disch_then drule)>>
  disch_then match_mp_tac>>simp[core_only_fml_build_fml]>>
  drule_all fml_rel_check_hconcl_list>>
  metis_tac[]
QED

val _ = export_theory();
