(*
  Refine PB proof checker to use arrays
*)
Theory npbc_list
Ancestors
  npbc_check npbc_slot ccnf_dm
Libs
  preamble

Theorem any_el_update_resize:
  any_el n (update_resize fml def v id) def =
  if n = id then v else any_el n fml def
Proof
  rw[update_resize_def,any_el_ALT,EL_LUPDATE]>>fs[]>>
  fs[EL_APPEND_EQN,EL_REPLICATE]>>
  every_case_tac>>fs[]
QED

Definition lookup_core_only_dec_def:
  lookup_core_only_dec b fml n =
  case lookup_core_only_list b fml n of
    Empty => NONE
  | s => SOME (dec s)
End

(* The stored operands of a linear combination, as slots with factors *)
Definition lookup_lincomb_slots_def:
  (lookup_lincomb_slots b fml [] = SOME []) ∧
  (lookup_lincomb_slots b fml ((n,k:num)::ids) =
    case lookup_core_only_list b fml n of
      Empty => NONE
    | s =>
      case lookup_lincomb_slots b fml ids of
        NONE => NONE
      | SOME sks => SOME ((s,k) :: sks))
End

(* TODO: optimize this using arrays instead of lists
  alternative:
    collapse all adds into one big list before normalizing
*)
(* vb is the length of the assignment, which bounds the variables of the
  stored constraints; it selects only how a Lincomb is evaluated *)
Definition check_cutting_list_def:
  (check_cutting_list b (vb:num) (fml: slot list) (Id n) =
    lookup_core_only_dec b fml n) ∧
  (check_cutting_list b vb fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting_list b vb fml c1) (check_cutting_list b vb fml c2)) ∧
  (check_cutting_list b vb fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting_list b vb fml c)) ∧
  (check_cutting_list b vb fml (Div dty c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. do_divide dty c k) (check_cutting_list b vb fml c)
    else NONE) ∧
  (check_cutting_list b vb fml (Minus c k) =
       OPTION_MAP (λc. minus c k) (check_cutting_list b vb fml c)) ∧
  (check_cutting_list b vb fml (Sat c) =
    OPTION_MAP saturate (check_cutting_list b vb fml c)) ∧
  (check_cutting_list b vb fml (Lit l) =
    case l of
      Pos v => SOME ([(1,v)],0)
    | Neg v => SOME ([(-1,v)],0)) ∧
  (check_cutting_list b vb fml (Triv ls) = SOME (clean_triv ls)) ∧
  (check_cutting_list b vb fml (Weak c var) =
    OPTION_MAP (λc. weaken_sorted c var) (check_cutting_list b vb fml c)) ∧
  (check_cutting_list b vb fml (Lincomb ids ns) =
    case lookup_lincomb_slots b fml ids of
      NONE => NONE
    | SOME sks =>
      case check_cutting_list_nest b vb fml ns of
        NONE => NONE
      | SOME ncs => SOME (lincomb_eval vb sks ncs)) ∧
  (check_cutting_list_nest b vb fml [] = SOME []) ∧
  (check_cutting_list_nest b vb fml ((c,k)::ns) =
    case check_cutting_list b vb fml c of
      NONE => NONE
    | SOME c =>
      case check_cutting_list_nest b vb fml ns of
        NONE => NONE
      | SOME cs => SOME (multiply c k :: cs))
End

(* Copied from LPR *)
Definition delete_list_def:
  delete_list i fml =
  if LENGTH fml ≤ i then fml
  else LUPDATE Empty i fml
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
  if id_start < id_end then
    rollback (delete_list id_start fml) (id_start + 1) id_end
  else fml
Termination
  WF_REL_TAC`measure (λ(fml,id_start,id_end). id_end - id_start)`
End

Theorem rollback_list_delete:
  ∀fml id_start id_end.
  rollback fml id_start id_end =
  list_delete_list
    (MAP ($+id_start) (COUNT_LIST (id_end-id_start))) fml
Proof
  ho_match_mp_tac rollback_ind>>
  rw[]>>
  simp[Once rollback_def]>>
  reverse (rw[])
  >- (
    `id_end - id_start = 0` by simp[]>>
    simp[COUNT_LIST_def,list_delete_list_def])>>
  `id_end - id_start = SUC (id_end - (id_start + 1))` by simp[]>>
  pop_assum SUBST1_TAC>>
  simp[COUNT_LIST_def,list_delete_list_def,MAP_MAP_o,combinTheory.o_DEF,ADD1]>>
  AP_THM_TAC>>
  AP_TERM_TAC>>
  simp[MAP_EQ_f]
QED

(* ensure list remains ≥ sorted -- common case: will always just insert at the front *)
Definition sorted_insert_def:
  sorted_insert (x:num) ys =
  case ys of
    [] => [x]
  | y::ys' =>
    if x ≥ y then x::ys
    else y::sorted_insert x ys'
End

Definition check_contradiction_fml_list_def:
  check_contradiction_fml_list b fml n =
  contr_slot (lookup_core_only_list b fml n)
End

(* Stores slot s, whose largest variable is mv; the assignment grows to
  cover its variables *)
Definition store_slot_def:
  store_slot fml s mv id assg st =
    let (assg',st') = grow_assg assg st (mv + 1) in
    (update_resize fml Empty s id,id+1,assg',st')
End

Definition opt_update_def:
  (opt_update fml NONE id assg st = (fml,id,assg,st)) ∧
  (opt_update fml (SOME (c,b)) id assg st =
    let (s,mv) = enc_mv c b in
    store_slot fml s mv id assg st)
End

Definition opt_update_neg_def:
  opt_update_neg fml c b id assg st =
    let (s,mv) = neg_slot c b in
    store_slot fml s mv id assg st
End

Theorem opt_update_neg_eq[simp]:
  opt_update_neg fml c b id assg st = opt_update fml (SOME (not c,b)) id assg st
Proof
  simp[opt_update_neg_def,opt_update_def,neg_slot_enc,enc_mv_enc,max_var_not]
QED

Definition get_rup_constraint_list_def:
  get_rup_constraint_list b fml n nc =
  if n = 0 then nc
  else
    lookup_core_only_list b fml n
End

(* (contradiction derived, assignment, all reads within the assignment) *)
Definition check_rup_loop_list_def:
  check_rup_loop_list b nc fml assg st [] = (F,assg,T) ∧
  check_rup_loop_list b nc fml assg st (n::ns) =
    case get_rup_constraint_list b fml n nc of
      Empty => (F,assg,T)
    | s =>
      let (done,assg,pre) = update_assg_slot assg st s in
      if done then (T,assg,pre)
      else
        let (res,assg,pre1) = check_rup_loop_list b nc fml assg st ns in
        (res,assg,pre ∧ pre1)
End

(* The negated constraint nc has its variables below sz; the check starts
  with every entry of the assignment unassigned *)
Definition check_rup_list_def:
  check_rup_list b nc sz fml assg st ls =
    let (assg,st) = reset_dm_list assg st sz in
    let (res,assg,pre) = check_rup_loop_list b nc fml assg st ls in
    (res,assg,st,pre)
End

Definition check_lstep_list_def:
  (check_lstep_list lstep
    b (fml: slot list)
    (mindel:num) (id:num) assg (st:num) =
  case lstep of
  | Delete ls =>
      if EVERY (λid. mindel ≤ id ∧
          lookup_core_only_list T fml id = Empty) ls then
        SOME(list_delete_list ls fml, NONE, id, assg, st)
      else
        NONE
  | Cutting constr =>
    (case check_cutting_list b (LENGTH assg) fml (to_triv constr) of
      NONE => NONE
    | SOME c =>
      SOME (fml, SOME(c,b), id, assg, st))
  | Rup c ls =>
    let (nc,mv) = neg_slot c b in
    let (res,assg,st,_) =
      check_rup_list b nc (mv + 1) fml assg st ls in
    (if res then
         SOME(
           fml,
           SOME(c,b),
           id,
           assg, st)
     else NONE)
  | Con c pf n =>
    let (fml_not_c,id',assg,st) =
      opt_update_neg fml c b id assg st in
    (case check_lsteps_list pf b fml_not_c id id' assg st of
      SOME (fml',id',assg,st) =>
      if check_contradiction_fml_list b fml' n then
        let rfml = rollback fml' id id' in
        SOME(
          rfml,
          SOME(c,b),
          id',
          assg, st)
      else NONE
    | _ => NONE)
  | ImplyAdd n c =>
    (case lookup_core_only_list b fml n of
      Empty => NONE
    | s =>
      if imp_slot s c then SOME(fml, SOME(c,b), id, assg, st)
      else NONE)
  | Check n c =>
    (case lookup_core_only_list b fml n of
      Empty => NONE
    | s =>
      if eq_slot c s then SOME(fml, NONE, id, assg, st)
      else NONE)
  | NoOp => SOME (fml, NONE, id, assg, st)) ∧
  (check_lsteps_list [] b fml mindel id assg st =
    SOME (fml, id, assg, st)) ∧
  (check_lsteps_list (step::steps) b fml mindel id assg st =
    case check_lstep_list step b fml mindel id assg st of
      SOME (fml',c,id',assg,st) =>
        let (fml'',id'',assg,st) = opt_update fml' c id' assg st in
          check_lsteps_list steps b fml'' mindel id'' assg st
    | NONE => NONE)
Termination
  WF_REL_TAC ‘measure (
    sum_size (lstep_size o FST)
    (list_size lstep_size o FST))’
End

Theorem opt_update_NONE[simp]:
  opt_update fml NONE id assg st = (fml,id,assg,st)
Proof
  simp[opt_update_def]
QED

Theorem opt_update_SOME:
  opt_update fml (SOME (c,b)) id assg st = (fml',id',assg',st') ⇔
  fml' = update_resize fml Empty (enc c b) id ∧ id' = id + 1 ∧
  grow_assg assg st (max_var (FST c) + 1) = (assg',st')
Proof
  simp[opt_update_def,store_slot_def,enc_mv_enc]>>
  pairarg_tac>>
  simp[]>>
  metis_tac[]
QED

Theorem store_slot_enc:
  mv = max_var (FST c) ⇒
  store_slot fml (enc c b) mv id assg st = opt_update fml (SOME (c,b)) id assg st
Proof
  simp[opt_update_def,enc_mv_enc]
QED

(* id numbers are monotone increasing *)
Theorem opt_update_id:
  opt_update fmlls c id assg st = (fmlls',id',assg',st') ⇒
  id ≤ id'
Proof
  Cases_on`c`
  >- simp[]>>
  rename1`SOME cc`>>
  PairCases_on`cc`>>
  simp[opt_update_SOME]
QED

Theorem check_lstep_list_id:
  (∀step b fmlls mindel id assg st fmlls' c id' assg' st'.
  check_lstep_list step b fmlls mindel id assg st =
    SOME (fmlls',c,id',assg',st') ⇒
    id ≤ id') ∧
  (∀steps b fmlls mindel id assg st fmlls' id' assg' st'.
  check_lsteps_list steps b fmlls mindel id assg st =
    SOME (fmlls',id',assg',st') ⇒
    id ≤ id')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]>>
  gvs[AllCaseEqs(),check_lstep_list_def]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  imp_res_tac opt_update_id>>
  gvs[]
QED

Theorem any_el_list_delete_list:
  ∀ls n fml.
  any_el n (list_delete_list ls fml) Empty =
  if MEM n ls then Empty else any_el n fml Empty
Proof
  Induct>>rw[list_delete_list_def,delete_list_def]>>
  gs[any_el_ALT,EL_LUPDATE]
QED

Theorem opt_update_id_upper:
  opt_update fmlls c id assg st = (fmlls',id',assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty)
Proof
  Cases_on`c`
  >- (
    rw[]>>
    gvs[])>>
  rename1`SOME cc`>>
  PairCases_on`cc`>>
  rw[opt_update_SOME]>>
  simp[any_el_update_resize]
QED

(* id numbers bound those in the formula *)
Theorem check_lstep_list_id_upper:
  (∀step b fmlls mindel id assg st fmlls' id' assg' st' c.
  check_lstep_list step b fmlls mindel id assg st =
    SOME (fmlls',c,id',assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
    (∀n. n ≥ id ⇒ any_el n fmlls' Empty = Empty)) ∧
  (∀steps b fmlls mindel id assg st fmlls' id' assg' st'.
  check_lsteps_list steps b fmlls mindel id assg st =
    SOME (fmlls',id',assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
    (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty))
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs[AllCaseEqs(),check_lstep_list_def]>>
    rpt (pairarg_tac>>gvs[AllCaseEqs()])
    >- rw[any_el_list_delete_list]>>
    gvs[opt_update_SOME]>>
    qpat_x_assum`_ ⇒ _` mp_tac>>
    impl_tac
    >- simp[any_el_update_resize]>>
    rw[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    qpat_x_assum`∀n. n ≥ id' ⇒ _` irule>>
    CCONTR_TAC>>
    qpat_x_assum`¬∃y. _` mp_tac>>
    simp[]>>
    qexists_tac`n - id`>>
    simp[])
  >- gvs[check_lstep_list_def]>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = SOME _` mp_tac>>
  simp[Once check_lstep_list_def,AllCaseEqs()]>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  rename1`opt_update fml1 c id1 assg1 st1 = (fml2,id2,assg2,st2)`>>
  qpat_x_assum`_ ⇒ _` irule>>
  rw[]>>
  qpat_x_assum`opt_update _ _ _ _ _ = _` assume_tac>>
  drule opt_update_id_upper>>
  disch_then irule>>
  rw[]>>
  qpat_x_assum`∀n. n ≥ id ⇒ any_el n fml1 Empty = Empty` irule>>
  drule (CONJUNCT1 check_lstep_list_id)>>
  simp[]
QED

Theorem opt_update_mindel:
  opt_update fmlls c id assg st = (fmlls',id',assg',st') ∧
  n < id ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
Proof
  Cases_on`c`
  >- simp[]>>
  rename1`SOME cc`>>
  PairCases_on`cc`>>
  rw[opt_update_SOME]>>
  simp[any_el_update_resize]
QED

(* ids below mindel are unchanged *)
Theorem check_lstep_list_mindel:
  (∀step b fmlls mindel id assg st fmlls' res n.
    check_lstep_list step b fmlls mindel id assg st =
      SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒
      any_el n fmlls Empty = any_el n fmlls' Empty) ∧
  (∀steps b fmlls mindel id assg st fmlls' res n.
    check_lsteps_list steps b fmlls mindel id assg st =
      SOME (fmlls', res) ∧
    mindel ≤ id ∧
    n < mindel ⇒
      any_el n fmlls Empty = any_el n fmlls' Empty)
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs[AllCaseEqs(),check_lstep_list_def]>>
    rpt (pairarg_tac>>gvs[AllCaseEqs()])
    >- (
      rw[any_el_list_delete_list]>>
      gvs[EVERY_MEM]>>
      first_x_assum drule>>
      simp[])>>
    gvs[opt_update_SOME]>>
    first_x_assum (qspec_then`n` mp_tac)>>
    simp[any_el_update_resize,rollback_list_delete,any_el_list_delete_list,MEM_MAP])
  >- gvs[check_lstep_list_def]>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = SOME _` mp_tac>>
  simp[Once check_lstep_list_def,AllCaseEqs()]>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  rename1`opt_update fml1 c id1 assg1 st1 = (fml2,id2,assg2,st2)`>>
  drule (CONJUNCT1 check_lstep_list_id)>>
  qpat_x_assum`opt_update _ _ _ _ _ = _` assume_tac>>
  drule opt_update_id>>
  drule opt_update_mindel>>
  rw[]
QED

(* ids below id are only deleted *)
Theorem check_lstep_list_id_del:
  (∀step b fmlls mindel id assg st fmlls' res n.
    check_lstep_list step b fmlls mindel id assg st =
      SOME (fmlls', res) ∧
    n < id ∧
    any_el n fmlls' Empty ≠ Empty ⇒
    any_el n fmlls Empty = any_el n fmlls' Empty) ∧
  (∀steps b fmlls mindel id assg st fmlls' res n.
    check_lsteps_list steps b fmlls mindel id assg st =
      SOME (fmlls', res) ∧
    n < id ∧
    any_el n fmlls' Empty ≠ Empty ⇒
    any_el n fmlls Empty = any_el n fmlls' Empty)
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    gvs[AllCaseEqs(),check_lstep_list_def]>>
    rpt (pairarg_tac>>gvs[AllCaseEqs()])
    >- (
      gvs[any_el_list_delete_list]>>
      Cases_on`MEM n ls`>>gvs[])>>
    gvs[opt_update_SOME]>>
    first_x_assum (qspec_then`n` mp_tac)>>
    gvs[any_el_update_resize,rollback_list_delete,any_el_list_delete_list,MEM_MAP])
  >- gvs[check_lstep_list_def]>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = SOME _` mp_tac>>
  simp[Once check_lstep_list_def,AllCaseEqs()]>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  rename1`opt_update fml1 c id1 assg1 st1 = (fml2,id2,assg2,st2)`>>
  drule (CONJUNCT1 check_lstep_list_id)>>
  qpat_x_assum`opt_update _ _ _ _ _ = _` assume_tac>>
  drule opt_update_id>>
  drule opt_update_mindel>>
  rw[]>>
  gvs[]
QED

(* Relation between
  sptree representation fml and list representation fmlls
  If we allow "fmlls" to be lazy, then this relation needs
  to also be parameterized by x ∈ set inds
*)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x. any_el x fmlls Empty = enc_opt (lookup x fml)
End

(* every variable of every stored constraint is below n *)
Definition fml_bound_def:
  fml_bound fmlls n ⇔
  ∀x. slot_bound (any_el x fmlls Empty) n
End

(* The state of the RUP check between steps *)
Definition rup_inv_def:
  rup_inv fmlls assg st ⇔
  fml_bound fmlls (LENGTH assg) ∧ ∃dm. dm_rel dm assg st
End

Theorem fml_rel_lookup_core_only:
  fml_rel fml fmlls ⇒
  lookup_core_only b fml n =
  case lookup_core_only_list b fmlls n of
    Empty => NONE
  | s => SOME (dec s)
Proof
  rw[fml_rel_def,lookup_core_only_def,lookup_core_only_list_def,core_only_def]>>
  first_x_assum (qspec_then`n` assume_tac)>>
  Cases_on`lookup n fml`>>
  gvs[enc_opt_def]>>
  rename1`lookup n fml = SOME p`>>
  PairCases_on`p`>>
  gvs[enc_opt_def,slot_CASE_default]>>
  rw[]
QED

Theorem fml_rel_lookup_core_only_enc:
  fml_rel fml fmlls ∧
  lookup_core_only_list b fmlls n ≠ Empty ⇒
  ∃c b'.
    lookup_core_only b fml n = SOME c ∧
    lookup_core_only_list b fmlls n = enc c b'
Proof
  rw[fml_rel_def]>>
  qpat_x_assum`_ ≠ Empty` mp_tac>>
  simp[lookup_core_only_list_def,core_only_def,lookup_core_only_def]>>
  Cases_on`lookup n fml`>>
  simp[enc_opt_def]>>
  rename1`lookup n fml = SOME p`>>
  PairCases_on`p`>>
  rw[enc_opt_def]>>
  metis_tac[]
QED

Theorem fml_rel_lookup_core_only_list:
  fml_rel fml fmlls ⇒
  (lookup_core_only_list b fmlls n = Empty ⇔
    lookup_core_only b fml n = NONE) ∧
  (lookup_core_only b fml n = SOME c ⇒
    ∃b'. lookup_core_only_list b fmlls n = enc c b')
Proof
  strip_tac>>
  Cases_on`lookup_core_only_list b fmlls n = Empty`
  >- (
    drule fml_rel_lookup_core_only>>
    disch_then (qspecl_then [`n`,`b`] mp_tac)>>
    simp[])>>
  drule_all fml_rel_lookup_core_only_enc>>
  rw[]>>gvs[]>>
  metis_tac[]
QED

Theorem dec_Empty[simp]:
  dec Empty = ([],0)
Proof
  simp[dec_def]
QED

Theorem MEM_dec_NOT_Empty:
  MEM x (FST (dec s)) ⇒ s ≠ Empty
Proof
  Cases_on`s`>>simp[]
QED

Theorem fml_rel_any_el:
  fml_rel fml fmlls ∧ any_el n fmlls Empty ≠ Empty ⇒
  ∃c b. lookup n fml = SOME (c,b) ∧ any_el n fmlls Empty = enc c b
Proof
  rw[fml_rel_def]>>
  first_x_assum (qspec_then`n` assume_tac)>>
  Cases_on`lookup n fml`>>gvs[enc_opt_def]>>
  rename1`SOME x`>>
  Cases_on`x`>>
  gvs[enc_opt_def]
QED

Theorem fml_rel_wf_slot:
  fml_rel fml fmlls ⇒ wf_slot (any_el n fmlls Empty)
Proof
  rw[fml_rel_def]>>
  Cases_on`lookup n fml`>>simp[enc_opt_def,wf_slot_def]>>
  rename1`SOME p`>>PairCases_on`p`>>simp[enc_opt_def]
QED

Theorem fml_rel_lookup_core_only_dec:
  fml_rel fml fmlls ⇒
  lookup_core_only_dec b fmlls n = lookup_core_only b fml n
Proof
  rw[lookup_core_only_dec_def]>>
  drule fml_rel_lookup_core_only>>
  simp[]
QED

Theorem fml_rel_lookup_lincomb_slots:
  ∀ids.
  fml_rel fml fmlls ⇒
  OPTION_MAP (MAP (λ(s,k). multiply (dec s) k))
    (lookup_lincomb_slots b fmlls ids) = lookup_lincomb b fml ids
Proof
  Induct>>
  simp[FORALL_PROD,lookup_lincomb_slots_def,lookup_lincomb_def]>>
  rw[]>>
  drule fml_rel_lookup_core_only_dec>>
  disch_then (simp o single o GSYM)>>
  simp[lookup_core_only_dec_def]>>
  TOP_CASE_TAC>>simp[]>>
  gvs[]>>
  Cases_on`lookup_lincomb_slots b fmlls ids`>>gvs[]>>
  qpat_x_assum`SOME _ = lookup_lincomb _ _ _` (simp o single o GSYM)
QED

(* The looked-up slots are entries of the formula *)
Theorem lookup_lincomb_slots_EVERY:
  ∀ids sks.
  (∀n. P (any_el n fmlls Empty)) ∧
  lookup_lincomb_slots b fmlls ids = SOME sks ⇒
  EVERY (λ(s,k). P s) sks
Proof
  Induct>>
  simp[lookup_lincomb_slots_def,FORALL_PROD,AllCaseEqs()]>>
  rw[]>>
  gvs[]>>
  qpat_x_assum`lookup_core_only_list _ _ _ = _` mp_tac>>
  rw[lookup_core_only_list_def,core_only_def]>>
  metis_tac[]
QED

Theorem fml_rel_check_cutting_mutual[local]:
  (∀b vb fmlls p.
    fml_rel fml fmlls ⇒
    check_cutting_list b vb fmlls p = check_cutting b fml p) ∧
  (∀b vb fmlls ns.
    fml_rel fml fmlls ⇒
    check_cutting_list_nest b vb fmlls ns = check_cutting_nest b fml ns)
Proof
  ho_match_mp_tac check_cutting_list_ind>>
  rw[check_cutting_list_def,check_cutting_def]
  >~[`lookup_core_only_dec`]
  >- metis_tac[fml_rel_lookup_core_only_dec]
  >~[`lookup_lincomb_slots`]
  >- (
    drule_then (qspecl_then [`b`,`ids`] assume_tac)
      fml_rel_lookup_lincomb_slots>>
    Cases_on`lookup_lincomb_slots b fmlls ids`>>gvs[]>>
    rename1`lookup_lincomb_slots _ _ _ = SOME sks`>>
    qpat_x_assum`SOME _ = lookup_lincomb _ _ _` (simp o single o GSYM)>>
    `EVERY (λ(s,k). wf_slot s) sks` by (
      irule lookup_lincomb_slots_EVERY>>
      metis_tac[fml_rel_wf_slot])>>
    TOP_CASE_TAC>>
    simp[lincomb_eval_eq,lincomb_slow_def])
  >~[`multiply`]
  >- (TOP_CASE_TAC>>gvs[])
QED

Theorem fml_rel_check_cutting:
  ∀p.
  fml_rel fml fmlls ⇒
  check_cutting_list b vb fmlls p = check_cutting b fml p
Proof
  metis_tac[fml_rel_check_cutting_mutual]
QED

Theorem fml_rel_rollback:
  fml_rel fml fmlls ∧
  (∀n. n < id ∨ n ≥ id' ⇒ any_el n fmlls Empty = any_el n fmlls' Empty) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty)
  ⇒
  fml_rel fml (rollback fmlls' id id')
Proof
  rw[fml_rel_def,rollback_list_delete]>>
  simp[any_el_list_delete_list]>>
  rw[MEM_MAP]>>
  fs[MEM_COUNT_LIST]
  >- (
    `id + y ≥ id` by fs[]>>
    metis_tac[enc_opt_eq_Empty])>>
  `x < id ∨ x ≥ id'` by intLib.ARITH_TAC>>
  metis_tac[]
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert id (c,b) fml) (update_resize fmlls Empty (enc c b) id)
Proof
  rw[fml_rel_def,lookup_insert,any_el_update_resize]>>
  rw[enc_opt_def]
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
    rw[lookup_delete,enc_opt_def]>>
    first_x_assum(qspec_then`h` assume_tac)>>fs[any_el_ALT]>>
    gs[])>>
  fs[fml_rel_def]>>
  rw[lookup_delete,enc_opt_def]>>
  fs[any_el_ALT,EL_LUPDATE]
QED

Theorem fml_rel_check_contradiction_fml:
  fml_rel fml fmlls ∧
  check_contradiction_fml_list b fmlls n ⇒
  check_contradiction_fml b fml n
Proof
  rw[check_contradiction_fml_list_def,check_contradiction_fml_def]>>
  `lookup_core_only_list b fmlls n ≠ Empty` by (
    strip_tac>>gvs[contr_slot_def])>>
  drule_all fml_rel_lookup_core_only_enc>>
  rw[]>>
  gvs[contr_slot_enc]
QED

Theorem bound_mono:
  fml_bound fmlls n ∧ n ≤ m ⇒ fml_bound fmlls m
Proof
  rw[fml_bound_def]>>
  metis_tac[slot_bound_mono]
QED

Theorem bound_list_delete_list:
  fml_bound fmlls n ⇒ fml_bound (list_delete_list ls fmlls) n
Proof
  rw[fml_bound_def,any_el_list_delete_list]>>
  rw[slot_bound_def]
QED

Theorem bound_rollback:
  fml_bound fmlls n ⇒ fml_bound (rollback fmlls id id') n
Proof
  rw[rollback_list_delete,bound_list_delete_list]
QED

Theorem rup_inv_list_delete_list:
  rup_inv fmlls assg st ⇒ rup_inv (list_delete_list ls fmlls) assg st
Proof
  rw[rup_inv_def,bound_list_delete_list]>>
  metis_tac[]
QED

Theorem rup_inv_rollback:
  rup_inv fmlls assg st ⇒ rup_inv (rollback fmlls id id') assg st
Proof
  rw[rollback_list_delete,rup_inv_list_delete_list]
QED

Theorem bound_update_resize:
  fml_bound fmlls n ∧ slot_bound s n ⇒
  fml_bound (update_resize fmlls Empty s id) n
Proof
  rw[fml_bound_def,any_el_update_resize]>>
  rw[]
QED

Theorem rup_inv_opt_update:
  rup_inv fmlls assg st ∧
  opt_update fmlls c id assg st = (fmlls',id',assg',st') ⇒
  rup_inv fmlls' assg' st' ∧ LENGTH assg ≤ LENGTH assg'
Proof
  Cases_on`c`
  >- (
    rw[]>>
    gvs[])>>
  rename1`SOME cc`>>
  PairCases_on`cc`>>
  rw[opt_update_SOME,rup_inv_def]>>
  drule_all dm_rel_grow_assg>>
  rw[]>>
  irule bound_update_resize>>
  conj_tac
  >- (
    irule bound_mono>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  irule slot_bound_mono>>
  irule_at Any slot_bound_enc_max_var>>
  simp[]
QED

Theorem rup_inv_update_resize_grow:
  rup_inv fmlls assg st ∧
  grow_assg assg st (max_var (FST c) + 1) = (assg',st') ⇒
  rup_inv (update_resize fmlls Empty (enc c b) id) assg' st'
Proof
  rw[rup_inv_def]>>
  drule_all dm_rel_grow_assg>>
  rw[]>>
  irule bound_update_resize>>
  conj_tac
  >- (
    irule bound_mono>>
    first_x_assum (irule_at Any)>>
    simp[])>>
  irule slot_bound_mono>>
  irule_at Any slot_bound_enc_max_var>>
  simp[]
QED

Theorem fml_rel_opt_update:
  fml_rel fml fmlls ∧
  opt_update fmlls (SOME (c,b)) id assg st = (fmlls',id',assg',st') ⇒
  fml_rel (insert id (c,b) fml) fmlls' ∧ id' = id + 1
Proof
  rw[opt_update_SOME]>>
  simp[fml_rel_update_resize]
QED

Theorem lookup_core_only_list_cases:
  ∀b fmlls n.
  lookup_core_only_list b fmlls n = Empty ∨
  lookup_core_only_list b fmlls n = any_el n fmlls Empty
Proof
  rw[lookup_core_only_list_def,core_only_def]
QED

Theorem get_rup_constraint_list_enc:
  fml_rel fml fmlls ∧ fml_bound fmlls k ∧
  EVERY (λ(i,v). v < k) (FST nc) ∧
  get_rup_constraint_list b fmlls h (enc nc b0) ≠ Empty ⇒
  ∃c b'.
    get_rup_constraint b fml h nc = SOME c ∧
    get_rup_constraint_list b fmlls h (enc nc b0) = enc c b' ∧
    EVERY (λ(i,v). v < k) (FST c)
Proof
  rw[get_rup_constraint_list_def,get_rup_constraint_def]
  >- metis_tac[]>>
  drule_all fml_rel_lookup_core_only_enc>>
  rw[]>>
  simp[]>>
  qspecl_then [`b`,`fmlls`,`h`] assume_tac lookup_core_only_list_cases>>
  gvs[fml_bound_def]>>
  first_x_assum (qspec_then`h` mp_tac)>>
  qpat_x_assum`enc c b' = _` (assume_tac o SYM)>>
  simp[slot_bound_enc]>>
  metis_tac[]
QED

Theorem get_rup_constraint_list_Empty:
  fml_rel fml fmlls ∧
  get_rup_constraint_list b fmlls h (enc nc b0) = Empty ⇒
  get_rup_constraint b fml h nc = NONE
Proof
  rw[get_rup_constraint_list_def,get_rup_constraint_def]>>
  drule fml_rel_lookup_core_only>>
  simp[]
QED

Theorem check_rup_loop_list_thm:
  ∀ns assg dm res assg' pre.
    fml_rel fml fmlls ∧ fml_bound fmlls (LENGTH assg) ∧
    EVERY (λ(i,v). v < LENGTH assg) (FST nc) ∧
    dm_rel dm assg st ∧
    check_rup_loop_list b (enc nc b0) fmlls assg st ns = (res,assg',pre) ⇒
    pre ∧ LENGTH assg' = LENGTH assg ∧ (∃dm'. dm_rel dm' assg' st) ∧
    (res ⇒ check_rup b nc fml dm ns)
Proof
  Induct
  >- (
    rw[check_rup_loop_list_def]>>
    metis_tac[])>>
  rpt gen_tac>>
  strip_tac>>
  qpat_x_assum`check_rup_loop_list _ _ _ _ _ _ = _` mp_tac>>
  simp[Once check_rup_loop_list_def]>>
  Cases_on`get_rup_constraint_list b fmlls h (enc nc b0) = Empty`
  >- (
    rw[]>>
    metis_tac[])>>
  drule_all get_rup_constraint_list_enc>>
  strip_tac>>
  simp[]>>
  drule_then (qspecl_then [`c`,`b'`] mp_tac) update_assg_slot_thm>>
  simp[]>>
  strip_tac>>
  gvs[slot_CASE_default]>>
  simp[check_rup_def]>>
  Cases_on`update_assg dm c`>>gvs[]
  >- (
    rw[]>>
    metis_tac[])>>
  rename1`update_assg dm c = SOME dm1`>>
  rename1`update_assg_slot assg st _ = (F,assg1,T)`>>
  `∃r1 a1 p1. check_rup_loop_list b (enc nc b0) fmlls assg1 st ns = (r1,a1,p1)`
    by metis_tac[PAIR]>>
  simp[]>>
  strip_tac>>
  gvs[]>>
  last_x_assum (qspecl_then [`assg1`,`dm1`,`r1`,`a1`,`p1`] mp_tac)>>
  simp[]
QED

Theorem check_rup_list_thm:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  EVERY (λ(i,v). v < sz) (FST nc) ∧
  check_rup_list b (enc nc b0) sz fmlls assg st ns = (res,assg',st',pre) ⇒
  pre ∧ rup_inv fmlls assg' st' ∧ LENGTH assg ≤ LENGTH assg' ∧
  (res ⇒ check_rup b nc fml FEMPTY ns)
Proof
  strip_tac>>
  gvs[check_rup_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[rup_inv_def]>>
  rename1`reset_dm_list assg st sz = (assg1,st1)`>>
  drule_all dm_rel_reset_dm_list>>
  strip_tac>>
  drule reset_dm_list_LENGTH>>
  strip_tac>>
  drule_at (Pos last) check_rup_loop_list_thm>>
  disch_then (qspecl_then [`fml`,`FEMPTY`] mp_tac)>>
  impl_tac
  >- (
    simp[]>>
    conj_tac
    >- (
      irule bound_mono>>
      first_x_assum (irule_at Any)>>
      simp[])>>
    irule MONO_EVERY>>
    first_x_assum (irule_at Any)>>
    simp[FORALL_PROD])>>
  rw[]>>
  irule bound_mono>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Theorem fml_rel_check_lstep_list:
  (∀lstep b fmlls mindel id assg st
    fmlls' id' assg' st' fmlls'' id'' assg'' st'' c fml.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    mindel ≤ id ∧
    check_lstep_list lstep b fmlls mindel id assg st =
      SOME (fmlls',c,id',assg',st') ∧
    opt_update fmlls' c id' assg' st' = (fmlls'',id'',assg'',st'') ⇒
    ∃fml'.
      check_lstep lstep b fml id = SOME (fml',id'') ∧
      fml_rel fml' fmlls'' ∧ rup_inv fmlls'' assg'' st'') ∧
  (∀lsteps b fmlls mindel id assg st fmlls' id' assg' st' fml.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    mindel ≤ id ∧
    check_lsteps_list lsteps b fmlls mindel id assg st =
      SOME (fmlls',id',assg',st') ⇒
    ∃fml'.
      check_lsteps lsteps b fml id = SOME (fml',id') ∧
      fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st')
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rw[]
  >- (
    qpat_x_assum`check_lstep_list _ _ _ _ _ _ _ = _` mp_tac>>
    simp[Once check_lstep_list_def]>>
    Cases_on`lstep`>>
    simp[slot_CASE_default]
    >~[`Delete ls`] >- suspend "Delete"
    >~[`Cutting cc`] >- suspend "Cutting"
    >~[`Rup cc ls`] >- suspend "Rup"
    >~[`Con cc pf n`] >- suspend "Con"
    >~[`ImplyAdd n cc`] >- suspend "ImplyAdd"
    >~[`Check n cc`] >- suspend "Check"
    >~[`NoOp`] >- suspend "NoOp")
  >- (
    gvs[check_lstep_list_def]>>
    simp[Once check_lstep_def])
  >- suspend "Cons"
QED

Resume fml_rel_check_lstep_list[Delete]:
  rw[]>>
  gvs[]>>
  simp[Once check_lstep_def]>>
  drule fml_rel_lookup_core_only>>
  strip_tac>>
  gvs[EVERY_MEM,fml_rel_list_delete_list,rup_inv_def,bound_list_delete_list]>>
  metis_tac[]
QED

Resume fml_rel_check_lstep_list[Cutting]:
  simp[AllCaseEqs()]>>
  strip_tac>>
  gvs[]>>
  simp[Once check_lstep_def]>>
  drule fml_rel_check_cutting>>
  strip_tac>>
  gvs[insert_fml_def]>>
  drule_all fml_rel_opt_update>>
  drule_all rup_inv_opt_update>>
  simp[]
QED

Resume fml_rel_check_lstep_list[Rup]:
  rpt (pairarg_tac>>gvs[neg_slot_enc,max_var_not])>>
  strip_tac>>
  gvs[]>>
  simp[Once check_lstep_def]>>
  `EVERY (λ(i,v). v < max_var (FST cc) + 1) (FST (not cc))` by (
    qspec_then`FST (not cc)` mp_tac max_var_bound>>
    simp[max_var_not])>>
  drule_at (Pos last) check_rup_list_thm>>
  disch_then (qspec_then`fml` mp_tac)>>
  simp[]>>
  strip_tac>>
  gvs[insert_fml_def]>>
  drule_all fml_rel_opt_update>>
  drule_all rup_inv_opt_update>>
  simp[]
QED

Resume fml_rel_check_lstep_list[Con]:
  pairarg_tac>>gvs[]>>
  simp[AllCaseEqs()]>>
  strip_tac>>
  gvs[]>>
  simp[Once check_lstep_def]>>
  rename1`opt_update fmlls _ id assg st = (fml_not_c,id1,assg1,st1)`>>
  qpat_x_assum`opt_update fmlls _ _ _ _ = _` assume_tac>>
  drule_all fml_rel_opt_update>>
  strip_tac>>
  drule_all rup_inv_opt_update>>
  strip_tac>>
  `∀n. n ≥ id1 ⇒ any_el n fml_not_c Empty = Empty` by (
    qpat_x_assum`opt_update fmlls _ _ _ _ = _` mp_tac>>
    rw[opt_update_SOME]>>
    simp[any_el_update_resize])>>
  gvs[]>>
  first_x_assum (qspec_then`insert id (not cc,b) fml` mp_tac)>>
  simp[]>>
  strip_tac>>
  simp[insert_fml_def]>>
  rename1`fml_rel fml3 fml'`>>
  `fml_rel fml (rollback fml' id id')` by (
    irule fml_rel_rollback>>
    qexists_tac`fmlls`>>
    rw[]
    >- (
      rename1`k < id`>>
      qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` assume_tac>>
      drule (CONJUNCT2 check_lstep_list_mindel)>>
      disch_then (qspec_then`k` mp_tac)>>
      qpat_x_assum`opt_update fmlls _ _ _ _ = _` assume_tac>>
      drule_then (qspec_then`k` mp_tac) opt_update_mindel>>
      simp[])>>
    qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` assume_tac>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    drule (CONJUNCT2 check_lstep_list_id)>>
    simp[])>>
  `rup_inv (rollback fml' id id') assg' st'` by
    metis_tac[rup_inv_rollback]>>
  qpat_x_assum`opt_update (rollback _ _ _) _ _ _ _ = _` assume_tac>>
  drule_all fml_rel_opt_update>>
  drule_all rup_inv_opt_update>>
  rw[]>>
  metis_tac[fml_rel_check_contradiction_fml]
QED

Resume fml_rel_check_lstep_list[ImplyAdd]:
  simp[AllCaseEqs()]>>
  strip_tac>>
  gvs[]>>
  simp[Once check_lstep_def]>>
  drule_all fml_rel_lookup_core_only_enc>>
  strip_tac>>
  gvs[insert_fml_def,imp_slot_enc]>>
  drule_all fml_rel_opt_update>>
  drule_all rup_inv_opt_update>>
  simp[]
QED

Resume fml_rel_check_lstep_list[Check]:
  simp[AllCaseEqs()]>>
  strip_tac>>
  gvs[]>>
  simp[Once check_lstep_def]>>
  drule_all fml_rel_lookup_core_only_enc>>
  strip_tac>>
  gvs[eq_slot_enc]
QED

Resume fml_rel_check_lstep_list[NoOp]:
  rw[]>>
  gvs[]>>
  simp[Once check_lstep_def]
QED

Resume fml_rel_check_lstep_list[Cons]:
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = SOME _` mp_tac>>
  simp[Once check_lstep_list_def,AllCaseEqs()]>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  rename1`opt_update fml1 c id1 assg1 st1 = (fml2,id2,assg2,st2)`>>
  first_x_assum (qspec_then`fml` mp_tac)>>
  simp[]>>
  strip_tac>>
  rename1`check_lstep lstep b fml id = SOME (fmlA,id2)`>>
  simp[Once check_lstep_def]>>
  first_x_assum irule>>
  simp[]>>
  qpat_x_assum`check_lstep_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule (CONJUNCT1 check_lstep_list_id)>>
  qpat_x_assum`opt_update _ _ _ _ _ = _` assume_tac>>
  drule opt_update_id>>
  rw[]>>
  drule_then irule opt_update_id_upper>>
  rw[]>>
  qpat_x_assum`check_lstep_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule (CONJUNCT1 check_lstep_list_id_upper)>>
  simp[]>>
  disch_then irule
QED

Finalise fml_rel_check_lstep_list;

Definition extract_clauses_list_def:
  (extract_clauses_list s b fml rsubs [] acc =
    SOME (REVERSE acc)) ∧
  (extract_clauses_list s b fml rsubs (cpf::pfs) acc =
    case cpf of
      (NONE,pf) =>
      extract_clauses_list s b fml rsubs pfs ((NONE,pf)::acc)
    | (SOME (INL n,i),pf) =>
        (case lookup_core_only_list b fml n of
          Empty => NONE
        | c =>
          extract_clauses_list s b fml rsubs pfs
            ((SOME ([not (subst_slot s c)],i),pf)::acc))
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
  (list_insert_fml_list [] b id fml assg st =
    (id,fml,assg,st)) ∧
  (list_insert_fml_list (c::cs) b id fml assg st =
    let (fml',id',assg',st') = opt_update fml (SOME (c,b)) id assg st in
    list_insert_fml_list cs b id' fml' assg' st')
End

Definition check_subproofs_list_def:
  (check_subproofs_list [] b fml mindel id assg st =
    SOME(fml,id,assg,st)) ∧
  (check_subproofs_list ((cnopt,pf)::pfs) b fml
    mindel id assg st =
    case cnopt of
      NONE => (* no clause given *)
      (case check_lsteps_list pf b fml mindel id assg st of
        SOME (fml', id', assg', st') =>
        check_subproofs_list pfs b fml' mindel id' assg' st'
      | res => NONE)
    | SOME (cs,n) =>
      let (cid,cfml,assg,st) =
        list_insert_fml_list cs b id fml assg st in
      (* no deletions below id *)
      case check_lsteps_list pf b cfml id cid assg st of
        SOME (fml', id', assg', st') =>
        if check_contradiction_fml_list b fml' n then
          let rfml = rollback fml' id id' in
            check_subproofs_list pfs b rfml mindel id' assg' st'
        else NONE
      | _ => NONE)
End

(* A scope hypothesis: a constraint, or its slot with its largest
  variable *)
Type sc_hyp = ``:npbc + (slot # num)``

Definition sc_hyp_dec_def[simp]:
  (sc_hyp_dec (INL c) = c) ∧
  (sc_hyp_dec (INR (s,mv)) = dec s)
End

(* A slot hypothesis is an encoding with its largest variable *)
Definition sc_hyp_ok_def[simp]:
  (sc_hyp_ok (INL c) ⇔ T) ∧
  (sc_hyp_ok (INR (s,mv)) ⇔ ∃c. s = enc c F ∧ mv = max_var (FST c))
End

Definition dec_scopes_def:
  dec_scopes (pfs:(sc_hyp list option # 'a) list) =
    MAP (λ(scopt,pf). (OPTION_MAP (MAP sc_hyp_dec) scopt, pf)) pfs
End

Definition scopes_ok_def:
  scopes_ok (pfs:(sc_hyp list option # 'a) list) ⇔
    EVERY (λ(scopt,pf). ∀sc. scopt = SOME sc ⇒ EVERY sc_hyp_ok sc) pfs
End

(* The slot a scope hypothesis is stored as, core iff b, with its largest
  variable *)
Definition sc_slot_def:
  (sc_slot b (INL c) = enc_mv c b) ∧
  (sc_slot b (INR (s,mv)) = (set_core_slot s b, mv:num))
End

Theorem sc_slot_enc:
  sc_hyp_ok h ⇒
  sc_slot b h = (enc (sc_hyp_dec h) b, max_var (FST (sc_hyp_dec h)))
Proof
  Cases_on`h`>>simp[sc_slot_def,enc_mv_enc]>>
  rename1`INR p`>>PairCases_on`p`>>
  rw[sc_slot_def]>>
  simp[]
QED

(* Inserts scope hypotheses, as core iff b *)
Definition list_insert_sc_list_def:
  (list_insert_sc_list ([]:sc_hyp list) b id fml assg st =
    (id,fml,assg,st)) ∧
  (list_insert_sc_list (h::hs) b id fml assg st =
    let (s,mv) = sc_slot b h in
    let (fml',id',assg',st') = store_slot fml s mv id assg st in
    list_insert_sc_list hs b id' fml' assg' st')
End

Definition check_scopes_list_def:
  (check_scopes_list [] b fml mindel id assg st =
    SOME (fml,id,assg,st)) ∧
  (check_scopes_list ((scopt,pf)::scpfs) b
    fml mindel id assg st =
    case scopt of
      NONE =>
        (case check_subproofs_list pf b fml mindel id assg st of
          NONE => NONE
        | SOME (fml',id',assg',st') =>
            check_scopes_list scpfs b fml' mindel id' assg' st')
    | SOME (sc:sc_hyp list) =>
    let (cid,cfml,assg,st) = list_insert_sc_list sc b id fml assg st in
    case check_subproofs_list pf b cfml id cid assg st of
      NONE => NONE
    | SOME (fml',id',assg',st') =>
        let rfml = rollback fml' id id' in
        check_scopes_list scpfs b rfml mindel id' assg' st')
End

Definition reindex_aux_def:
  (reindex_aux fml [] iacc = REVERSE iacc) ∧
  (reindex_aux fml (i::is) iacc =
  if any_el i fml Empty = Empty then reindex_aux fml is iacc
  else reindex_aux fml is (i::iacc))
End

Definition reindex_def:
  (reindex fml is = reindex_aux fml is [])
End

Definition subst_indexes_def:
  (subst_indexes s b fml [] = []) ∧
  (subst_indexes s b fml (i::is) =
    case subst_opt_slot s (lookup_core_only_list b fml i) of
      NONE => subst_indexes s b fml is
    | SOME c => (i,c)::subst_indexes s b fml is)
End

(* Fast path for a special case corresponding to pbc
   --- enables faster checked deletion
   No scoping and no proofgoals used *)
Definition red_fast_def:
  red_fast idopt pfs = (
    case idopt of
      NONE => NONE
    | SOME id =>(
      case (pfs:scope) of
      | [(NONE,[(NONE,pf)])] => SOME (pf,id)
      | [] => SOME ([],id)
      | _ => NONE))
End

(* inds and the table ht are just passed through here *)
Definition check_red_list_fast_def:
  check_red_list_fast b fml inds id fc mv pf cid vimap assg st ht =
  let (fml_not_c,id1,assg,st) = store_slot fml (not_slot fc b) mv id assg st in
  case check_lsteps_list pf b fml_not_c id id1 assg st of
    NONE => NONE
  | SOME (fml', id',assg',st') =>
  if check_contradiction_fml_list b fml' cid then
    let rfml = rollback fml' id id' in
      SOME (rfml,inds,vimap,id',assg',st',ht)
  else
    NONE
End

(* The INL ids proved by a list of proofs, as keys of a list, and the INR
  ids, as a set *)
Definition extract_pids_list_def:
  (extract_pids_list [] (l:(num # unit) list) r = (l,r)) ∧
  (extract_pids_list (cpf::pfs) l r =
  case FST cpf of
    NONE => extract_pids_list pfs l r
  | SOME (i,n) =>
    (case i of
      INL i => extract_pids_list pfs ((i,())::l) r
    | INR i => extract_pids_list pfs l (insert i () r)))
End

Definition extract_scoped_pids_list_def:
  (extract_scoped_pids_list [] l r = (l,r)) ∧
  (extract_scoped_pids_list ((scopt,pf)::scpfs) l r =
  if extract_scope_val scopt
  then
      let (l,r) = extract_pids_list pf l r in
        extract_scoped_pids_list scpfs l r
  else extract_scoped_pids_list scpfs l r)
End

(* The proved goals, and the goals neither proved nor implied by extra,
  in one pass; both in reverse order *)
Definition split_goals_pure_def:
  (split_goals_pure (proved:unit lmap) extra [] lp lf = (lp,lf)) ∧
  (split_goals_pure proved extra
    ((i,c)::(goals:(num # (int # num) list # int) list)) lp lf =
    if map_lookup proved i ≠ NONE then
      split_goals_pure proved extra goals (c::lp) lf
    else if imp_slot extra c then
      split_goals_pure proved extra goals lp lf
    else
      split_goals_pure proved extra goals lp (c::lf))
End

(* The goals proved by the subproofs pids, and the others that extra does
  not imply *)
Definition split_goals_pids_def:
  split_goals_pids (pids:(num # unit) list) extra goals =
  split_goals_pure (mk_map [] pids) extra goals [] []
End

(* Every goal matches a slot (core only, if b) of fml in the table tbl, or
  is one of the proved goals lp *)
Definition ht_goals_def:
  (ht_goals b fml lp tbl [] ⇔ T) ∧
  (ht_goals b fml lp tbl (c::cs) ⇔
    (ht_probe b fml c (hash_constraint c) tbl ∨ mem_constraint c lp) ∧
    ht_goals b fml lp tbl cs)
End

(* The goals neither proved nor implied by extra are looked up in the
  table, which is filled first; pids are the proved ids and base is the
  first id of the step *)
Definition split_goals_hash_def:
  split_goals_hash b fml inds base ht extra (pids:(num # unit) list)
    (goals:(num # (int # num) list # int) list) =
  let (lp,lf) = split_goals_pids pids extra goals in
  if NULL lf then (T,ht)
  else
    let ht = ht_fill fml inds base ht in
    let (hw,a,d,tbl) = ht in
    (ht_goals b fml lp tbl lf, ht)
End

Theorem split_goals_hash_test:
  let fml = [Empty; enc ([(2,1);(-3,4)],5) T; enc ([(1,1)],1) F] in
  let extra = enc ([(1,7)],1) T in
  let proved = [(5n,())] in
  let gp = ([(1,9)],1) in
  let run b gs = split_goals_hash b fml [2;1] 3 ht_empty extra proved gs in
  (* a goal in the database: core only when b *)
  FST (run F [(5,gp); (6,([(2,1);(-3,4)],5)); (7,([(1,1)],1))]) ∧
  ¬FST (run T [(5,gp); (6,([(2,1);(-3,4)],5)); (7,([(1,1)],1))]) ∧
  (* a goal equal to a proved goal, outside or inside the database *)
  FST (run T [(5,gp); (8,gp); (6,([(2,1);(-3,4)],5))]) ∧
  FST (run F [(5,([(1,1)],1)); (7,([(1,1)],1))]) ∧
  ¬FST (run F [(8,gp)]) ∧
  (* a goal implied by extra *)
  FST (run F [(9,([(1,7)],1))]) ∧
  FST (split_goals_hash F fml [2;1] 3 ht_empty extra [] [(9,([(1,7)],1))]) ∧
  (* nothing to look up: the table is not filled *)
  run F [(5,gp); (9,([(1,7)],1))] = (T,ht_empty) ∧
  FST (SND (run F [(6,([(2,1);(-3,4)],5))])) = 3
Proof
  EVAL_TAC
QED

Definition red_cond_check_def:
  red_cond_check b fml inds base ht extra pfs
    (rsubs:((int # num) list # int) list list) goals skipped =
  let (l,r) = extract_scoped_pids_list pfs [] LN in
  if check_hash_goals_slot extra skipped r rsubs then
    split_goals_hash b fml inds base ht extra l goals
  else (F,ht)
End

(* Not meant to be executed, mainly just abbrevation... *)
Definition do_red_check_def:
  do_red_check idopt b tcb fml inds base ht
    s rfml rinds extra pfs rsubs skipped cond =
  case idopt of NONE =>
    let goals = subst_indexes s (b ∨ tcb) rfml rinds in
      if cond then
        red_cond_check b rfml inds base ht extra pfs rsubs goals skipped
      else (F,ht)
  | SOME cid =>
     (check_contradiction_fml_list b fml cid, ht)
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
   &SUM (MAP (λ(c,x).
    if is_Pos c ⇔ OUTL (THE (f x))
    then Num(ABS c) else 0)
    (FILTER (λ(c,x). f x ≠ NONE) l)))
Proof
  Induct>>rw[npbcTheory.subst_aux_def]>>
  rpt(pairarg_tac>>gvs[])>>
  simp[npbcTheory.subst_aux_def]>>
  Cases_on`f x`>>fs[]>>
  Cases_on`x'`>>fs[]>>
  rw[]>>fs[]>>
  intLib.ARITH_TAC
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
   &SUM (MAP (λ(c,x).
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
      &SUM
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
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- intLib.ARITH_TAC
  >- (
    DEP_REWRITE_TAC[LESS_EQ_ADD_SUB]>>
    simp[SUM_SPLIT_LE]>>
    Cases_on`x'`>>fs[]>>
    intLib.ARITH_TAC)
QED

(* one pass obj_constraint *)
Definition obj_single_aux_def:
  (obj_single_aux f n [] acc k = SOME(REVERSE acc,k:int)) ∧
  (obj_single_aux f n ((c,x:num)::xs) acc k =
    if n < x then
      case f x of
        NONE => obj_single_aux f x xs acc k
      | SOME (INL b) =>
        let r = if is_Pos c ⇔ b then k + ABS c else k in
          obj_single_aux f x xs ((c,x)::acc) r
      | SOME (INR _) => NONE
    else NONE)
End

Definition obj_single_def:
  (obj_single f [] = SOME([],0:int)) ∧
  (obj_single f ((c,x:num)::xs) =
      case f x of
        NONE => obj_single_aux f x xs [] 0
      | SOME (INL b) =>
        let r = if is_Pos c ⇔ b then ABS c else 0 in
          obj_single_aux f x xs [(c,x)] r
      | SOME (INR _) => NONE)
End

Theorem obj_single_aux_eq_SOME:
  ∀l f n acc k res.
  obj_single_aux f n l acc k = SOME res ⇒
  EVERY (λ(c,x). case f x of SOME (INR _ ) => F | _ => T) l ∧
  SORTED $< (n::MAP SND l) ∧
  res = (REVERSE acc ++ FILTER (λ(c,x). f x ≠ NONE) l,
      k + &SUM
      (MAP
         (λ(c,x). if 0 ≤ c ⇔ OUTL (THE (f x)) then Num (ABS c) else 0)
         (FILTER (λ(c,x). f x ≠ NONE) l)))
Proof
  Induct>>simp[obj_single_aux_def,FORALL_PROD]>>rw[]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[]>>rw[]>>
  intLib.ARITH_TAC
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
  simp[]>>
  intLib.ARITH_TAC
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

(* Fast substitution for obj_constraint: trivial unless the witness
  (raw form sr) maps an objective variable (in vomap) *)
Definition fast_obj_constraint_def:
  fast_obj_constraint s sr l vomap =
  if EVERY (λ(n,v). strlen vomap ≤ n ∨ strsub_unsafe vomap n = ^zw) sr
  then ([],0)
  else full_obj_single (subst_fun s) l
End

(* The order precomputed at its load.

  A record of an order constraint c: c renamed with the empty witness (each
  formal of us and vs replaced by its literal of xs), its negation, the
  terms of c on the formals of us and of vs as
  (coefficient, problem variable, sign bit), and the renamed constraint
  encoded as a non-core slot with its largest variable.

  The precomputed order: the records of f and of g, the length of f, and
  for us and for vs, a map from a problem variable to the ids (f's records
  first, then g's) of the records with a term on a formal mapped to it *)
Type ord_rec = ``:npbc # npbc # (int # num # bool) list #
  (int # num # bool) list # (slot # num)``

Type ord_pre = ``:ord_rec list # ord_rec list # num #
  num list lmap # num list lmap``

Definition ord_ww0_def:
  ord_ww0 us_xs vs_xs n =
    case map_lookup us_xs n of
      SOME (v,b) => SOME (INR (mk_lit (v,b)))
    | NONE => OPTION_MAP (INR o mk_lit) (map_lookup vs_xs n)
End

(* The terms of l on the keys of m, as (coefficient, variable, sign bit) *)
Definition formal_terms_def:
  (formal_terms (m:(num # bool) lmap) [] acc = acc) ∧
  (formal_terms m ((c:int,n)::l) acc =
    case map_lookup m n of
      NONE => formal_terms m l acc
    | SOME (v,b) => formal_terms m l ((c,v,b)::acc))
End

Definition mk_ord_rec_def:
  mk_ord_rec us_xs vs_xs (c:npbc) =
  let c0 = subst (ord_ww0 us_xs vs_xs) c in
  ((c0, not c0, formal_terms us_xs (FST c) [], formal_terms vs_xs (FST c) [],
    enc_mv c0 F):ord_rec)
End

(* Adds id j to the entry of each variable of l *)
Definition ord_index_aux_def:
  (ord_index_aux (t:num list num_map) (j:num) [] = t) ∧
  (ord_index_aux t j (((c:int),v,(b:bool))::l) =
    ord_index_aux
      (insert v (case lookup v t of NONE => [j] | SOME js => j::js) t) j l)
End

Definition ord_index_def:
  (ord_index side t j ([]:ord_rec list) = t) ∧
  (ord_index side t j ((c0,ncs,uts,vts,sl)::rs) =
    ord_index side (ord_index_aux t j (if side then uts else vts)) (j+1) rs)
End

Definition compact_terms_def:
  (compact_terms ([]:(int # num) list) ⇔ T) ∧
  (compact_terms [x] ⇔ FST x ≠ 0) ∧
  (compact_terms (x::y::l) ⇔
    FST x ≠ 0 ∧ SND x < SND y ∧ compact_terms (y::l))
End

(* The precomputed order, when every constraint is compact and no formal
  is in both us and vs *)
Definition mk_ord_pre_def:
  mk_ord_pre (ord:ord_s option) =
  case ord of NONE => NONE
  | SOME (((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv) =>
    if EVERY (compact_terms o FST) f ∧ EVERY (compact_terms o FST) g ∧
      EVERY (λn. map_lookup us_xs n = NONE) vs
    then
      let frs = MAP (mk_ord_rec us_xs vs_xs) f in
      let grs = MAP (mk_ord_rec us_xs vs_xs) g in
      let rs = frs ++ grs in
      SOME ((frs, grs, LENGTH f,
        mk_map [] (toAList (ord_index T LN 0 rs)),
        mk_map [] (toAList (ord_index F LN 0 rs))):ord_pre)
    else NONE
End

(* The ids of the records with a term on a variable of the witness, in
  increasing order, possibly repeated *)
Definition ord_touched_aux_def:
  (ord_touched_aux (idx:num list lmap) ([]:var subst_raw) acc = acc) ∧
  (ord_touched_aux idx ((v,x)::sr) acc =
    case map_lookup idx v of
      NONE => ord_touched_aux idx sr acc
    | SOME ids => ord_touched_aux idx sr (ids ++ acc))
End

Definition ord_touched_def:
  ord_touched idx sr = mllist$sort (λx y. x ≤ y) (ord_touched_aux idx sr [])
End

(* The change, under witness w, of the renamed terms l of a record: a
  constraint (dts, k) with dts not normalised *)
Definition delta_terms_def:
  (delta_terms w [] dts (k:int) = (dts,k)) ∧
  (delta_terms w ((c,v,b)::l) dts k =
    case w v of
      NONE => delta_terms w l dts k
    | SOME res =>
      let dts = (if b then -c else c, v)::dts in
      let k = k + ABS c in
      case mk_bit_lit b res of
        INL b' => delta_terms w l dts (if is_Pos c = b' then k - ABS c else k)
      | INR (Pos n) => delta_terms w l ((c,n)::dts) k
      | INR (Neg n) => delta_terms w l ((-c,n)::dts) k)
End

(* A renamed constraint corrected by the witness *)
Definition touched_rec_def:
  touched_rec w (c0:npbc) l =
  let (dts,k) = delta_terms w l [] 0 in
  let (sorted,k2) = clean_up dts in
  add c0 (sorted, k - k2)
End

(* The negation of a renamed constraint corrected by the witness, from the
  negation nc0 of the renamed constraint *)
Definition touched_not_def:
  touched_not w (nc0:npbc) l =
  let (dts,k) = delta_terms w l [] 0 in
  let (sorted,k2) = clean_up dts in
  let (nds,r) = not (sorted, k - k2) in
  add nc0 (nds, r - 1)
End

(* The records from id j renamed under witness w, on side us (side) or vs;
  ts holds the touched ids *)
(* TMC *)
Definition fast_rn_def:
  (fast_rn w side ([]:ord_rec list) ts (j:num) = []) ∧
  (fast_rn w side (r::rs) ts j =
    case ts of
      [] => FST r :: fast_rn w side rs [] (j+1)
    | (t::ts') =>
      if t < j then fast_rn w side (r::rs) ts' j
      else if t = j then
        (case r of (c0,ncs,uts,vts,sl) =>
          touched_rec w c0 (if side then uts else vts) ::
          fast_rn w side rs ts' (j+1))
      else FST r :: fast_rn w side rs ts (j+1))
Termination
  WF_REL_TAC`measure (λ(w,side,rs,ts,j). LENGTH rs + LENGTH ts)`
  \\ rw []
End

(* As fast_rn on side us, as the one-element lists of the negations *)
(* TMC *)
Definition fast_rn_not_def:
  (fast_rn_not w ([]:ord_rec list) ts (j:num) = ([]:npbc list list)) ∧
  (fast_rn_not w (r::rs) ts j =
    case ts of
      [] => [FST (SND r)] :: fast_rn_not w rs [] (j+1)
    | (t::ts') =>
      if t < j then fast_rn_not w (r::rs) ts' j
      else if t = j then
        (case r of (c0,nc0,uts,vts,sl) =>
          [touched_not w nc0 uts] :: fast_rn_not w rs ts' (j+1))
      else [FST (SND r)] :: fast_rn_not w rs ts (j+1))
Termination
  WF_REL_TAC`measure (λ(w,rs,ts,j). LENGTH rs + LENGTH ts)`
  \\ rw []
End

(* As fast_rn, as scope hypotheses: the slot of an untouched record *)
(* TMC *)
Definition fast_rn_sc_def:
  (fast_rn_sc w side ([]:ord_rec list) ts (j:num) = ([]:sc_hyp list)) ∧
  (fast_rn_sc w side (r::rs) ts j =
    case ts of
      [] => INR (SND (SND (SND (SND r)))) :: fast_rn_sc w side rs [] (j+1)
    | (t::ts') =>
      if t < j then fast_rn_sc w side (r::rs) ts' j
      else if t = j then
        (case r of (c0,ncs,uts,vts,sl) =>
          INL (touched_rec w c0 (if side then uts else vts)) ::
          fast_rn_sc w side rs ts' (j+1))
      else INR (SND (SND (SND (SND r)))) :: fast_rn_sc w side rs ts (j+1))
Termination
  WF_REL_TAC`measure (λ(w,side,rs,ts,j). LENGTH rs + LENGTH ts)`
  \\ rw []
End

(* The negated f subgoals and the g scope hypotheses of dom_subst *)
Definition dom_subst_fast_def:
  dom_subst_fast hs w sr ((frs,grs,nf,uidx,vidx):ord_pre) =
  let ts = ord_touched uidx sr in
  (fast_rn_not w frs ts 0, if hs then fast_rn_sc w T grs ts nf else [])
End

Definition neg_dom_subst_fast_def:
  neg_dom_subst_fast w sr ((frs,grs,nf,uidx,vidx):ord_pre) =
  let ts = ord_touched vidx sr in
  (fast_rn w F frs ts 0, fast_rn_sc w F grs ts nf)
End

(* dom_subst as negated f subgoals and scope hypotheses, from the
  precomputed order po when present *)
Definition dom_subst_list_def:
  dom_subst_list hs w sr ord (po:ord_pre option) =
  case po of
    NONE =>
      let (fs,gs) = dom_subst hs w ord in
      (MAP (λc. [not c]) fs, MAP INL gs : sc_hyp list)
  | SOME p => dom_subst_fast hs w sr p
End

Definition fast_red_subgoals_def:
  fast_red_subgoals ord po s sr def obj vomap hs =
  let cobj =
    case obj of NONE => []
    | SOME l => [[not (fast_obj_constraint s sr l vomap)]] in
  let w = subst_fun s in
  let (nfs,gs) = dom_subst_list hs w sr ord po in
  let c0 = subst_slot s def in
  ([not c0]::nfs ++ cobj, [gs])
End

(* dom_subgoals, from the precomputed order po when present *)
Definition dom_subgoals_list_def:
  dom_subgoals_list (aspo:ord_s) (po:ord_pre option) s sr obj =
  let w = subst_fun s in
  let (nfs,gs) = dom_subst_list T w sr (SOME aspo) po in
  let (fs',gs') =
    (case po of
      NONE =>
        let (fs',gs') = neg_dom_subst w aspo in
        (fs', MAP INL gs' : sc_hyp list)
    | SOME p => neg_dom_subst_fast w sr p) in
  let cobj =
    case obj of NONE => []
    | SOME l => [[not (obj_constraint w l)]] in
  (nfs ++ fs' :: cobj, [gs; gs'], LENGTH nfs)
End

(* The precomputed order renames as dom_subst and neg_dom_subst do; xs
  repeats variable 10, and a witness may repeat a key or miss the order *)
Theorem dom_subst_fast_test:
  let f = [([(4,1);(2,2);(1,3);(-4,4);(-2,5);(-1,6)],0); ([(3,1);(1,7)],1)] in
  let g = [([(1,2);(-1,5)],0); ([(2,3);(1,7)],1)] in
  let xs = [(10,T);(11,F);(10,T)] in
  let ord = mk_ordsub ((f,g,[1;2;3],[4;5;6],[7]), mk_as_vec [7]) xs in
  let po = mk_ord_pre ord in
  let dec_nfs = λ(nfs,gs). (nfs, MAP sc_hyp_dec gs) in
  let dec_gs = λ(fs,gs). (fs, MAP sc_hyp_dec gs) in
  let neg_fs = λ(fs,gs). (MAP (λc. [not c]) fs, gs) in
  let chk sr =
    let w = subst_fun (mk_subst [] sr) in
    dec_nfs (dom_subst_list T w sr ord po) = neg_fs (dom_subst T w ord) ∧
    dec_gs (neg_dom_subst_fast w sr (THE po)) = neg_dom_subst w (THE ord) in
  IS_SOME po ∧
  chk [] ∧ chk [(10,INL T)] ∧ chk [(11,INR (Pos 12))] ∧
  chk [(10,INR (Neg 11)); (11,INL F)] ∧ chk [(10,INL T); (10,INL F)] ∧
  chk [(20,INL T)] ∧ chk [(11,INR (Neg 10)); (10,INR (Pos 11))] ∧
  chk [(10,INR (Neg 7))] ∧ chk [(10,INR (Pos 7)); (11,INR (Pos 10))] ∧
  (* a formal in both us and vs: no precomputation *)
  mk_ord_pre (mk_ordsub ((f,g,[1;2;3],[3;5;6],[7]), mk_as_vec [7]) xs) = NONE
Proof
  EVAL_TAC
QED

(* The maps of a loaded order are built from its formals and xs, as
  mk_ordsub builds them *)
Definition ord_maps_ok_def:
  ord_maps_ok ((((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv):ord_s) ⇔
  us_xs = mk_map [] (ZIP (us,xs)) ∧
  vs_xs = mk_map [] (ZIP (vs,xs))
End

Theorem compact_terms_thm:
  ∀l. compact_terms l ⇔
    SORTED $< (MAP SND l) ∧ EVERY (λc. c ≠ 0) (MAP FST l)
Proof
  recInduct compact_terms_ind
  \\ rw[compact_terms_def]
  \\ eq_tac \\ rw[]
QED

(* The renaming of dom_subst (m1 = us_xs, m2 = vs_xs) and of neg_dom_subst
  (m1 = vs_xs, m2 = us_xs) under witness w *)
Definition ord_ww_def:
  ord_ww (m1:(num # bool) lmap) (m2:(num # bool) lmap) w =
    λn.
    case map_lookup m1 n of
      SOME (v,b) =>
        SOME (mk_bit_lit b
          (case w v of NONE => INR (Pos v) | SOME res => res))
    | NONE => OPTION_MAP (INR o mk_lit) (map_lookup m2 n)
End

Theorem dom_subst_ord_ww:
  dom_subst hs w (SOME (((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv)) =
  (MAP (subst (ord_ww us_xs vs_xs w)) f,
   if hs then MAP (subst (ord_ww us_xs vs_xs w)) g else [])
Proof
  simp[dom_subst_def, ord_ww_def]
QED

Theorem neg_dom_subst_ord_ww:
  neg_dom_subst w (((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv) =
  (MAP (subst (ord_ww vs_xs us_xs w)) f, MAP (subst (ord_ww vs_xs us_xs w)) g)
Proof
  simp[neg_dom_subst_def, ord_ww_def]
QED

Theorem ord_ww0_ord_ww:
  ord_ww0 m1 m2 = ord_ww m1 m2 (K NONE)
Proof
  simp[FUN_EQ_THM, ord_ww0_def, ord_ww_def]
  \\ qx_gen_tac ‘n’ \\ Cases_on ‘map_lookup m1 n’ \\ simp[]
  \\ rename1 ‘SOME p’ \\ PairCases_on ‘p’
  \\ simp[npbcTheory.mk_bit_lit_def]
QED

Theorem ord_ww_swap:
  (∀n. map_lookup m1 n = NONE ∨ map_lookup m2 n = NONE) ⇒
  ord_ww m1 m2 (K NONE) = ord_ww m2 m1 (K NONE)
Proof
  strip_tac \\ simp[FUN_EQ_THM, ord_ww_def]
  \\ qx_gen_tac ‘n’
  \\ ‘map_lookup m1 n = NONE ∨ map_lookup m2 n = NONE’ by simp[]
  \\ Cases_on ‘map_lookup m1 n’ \\ Cases_on ‘map_lookup m2 n’ \\ gvs[]
  \\ qmatch_asmsub_rename_tac ‘_ = SOME q’ \\ PairCases_on ‘q’
  \\ simp[npbcTheory.mk_bit_lit_def]
QED

Theorem formal_terms_acc:
  ∀l acc. formal_terms m l acc = formal_terms m l [] ++ acc
Proof
  Induct >- simp[formal_terms_def]
  \\ rpt strip_tac \\ rename1 ‘formal_terms m (t::l) acc’
  \\ PairCases_on ‘t’
  \\ qpat_x_assum ‘∀acc. _’ (fn ih =>
    simp[formal_terms_def] \\ Cases_on ‘map_lookup m t1’ \\ simp[]
    >- (once_rewrite_tac [ih] \\ simp[])
    \\ qmatch_asmsub_rename_tac ‘_ = SOME q’ \\ PairCases_on ‘q’ \\ simp[]
    \\ once_rewrite_tac [ih] \\ simp[])
QED

Theorem formal_terms_nonzero:
  ∀l acc.
  EVERY (λc. c ≠ 0) (MAP FST l) ∧ EVERY (λ(c,v,b). c ≠ 0) acc ⇒
  EVERY (λ(c,v,b). c ≠ 0) (formal_terms m l acc)
Proof
  Induct >- simp[formal_terms_def]
  \\ rpt strip_tac \\ rename1 ‘formal_terms m (t::l) acc’
  \\ PairCases_on ‘t’ \\ gvs[formal_terms_def]
  \\ Cases_on ‘map_lookup m t1’ \\ simp[]
  \\ qmatch_asmsub_rename_tac ‘_ = SOME q’ \\ PairCases_on ‘q’ \\ simp[]
QED

Theorem delta_terms_APPEND:
  ∀l1 l2 dts k.
  delta_terms w (l1 ++ l2) dts k =
  UNCURRY (delta_terms w l2) (delta_terms w l1 dts k)
Proof
  Induct \\ simp[delta_terms_def, FORALL_PROD]
  \\ rw[] \\ every_case_tac \\ simp[]
QED

Theorem delta_terms_untouched:
  ∀l dts k.
  EVERY (λ(c,v,b). w v = NONE) l ⇒ delta_terms w l dts k = (dts,k)
Proof
  Induct \\ simp[delta_terms_def, FORALL_PROD]
QED

Theorem delta_terms_nonzero:
  ∀l dts k dts' k'.
  delta_terms w l dts k = (dts',k') ∧
  EVERY (λ(c,v,b). c ≠ 0) l ∧ EVERY (λc. c ≠ 0) (MAP FST dts) ⇒
  EVERY (λc. c ≠ 0) (MAP FST dts')
Proof
  Induct \\ simp[delta_terms_def, FORALL_PROD]
  \\ rw[] \\ every_case_tac \\ gvs[]
  \\ first_x_assum drule \\ simp[]
QED

(* The change made by the witness to a term on a formal *)
Theorem delta_one:
  map_lookup m1 x = SOME (v,b) ∧
  delta_terms w [(c,v,b)] d k = (d',k') ⇒
  &SUM (MAP (eval_term w') d') − k' =
  &SUM (MAP (eval_term w') d) − k +
  (&eval_term (assign (ord_ww m1 m2 w) w') (c,x) −
   &eval_term (assign (ord_ww m1 m2 (K NONE)) w') (c,x))
Proof
  strip_tac
  \\ gvs[delta_terms_def, npbcTheory.assign_def, ord_ww_def]
  \\ Cases_on ‘w v’ \\ gvs[delta_terms_def]
  \\ qmatch_asmsub_rename_tac ‘w v = SOME res’
  \\ Cases_on ‘res’
  >- (
    rename1 ‘INL bb’
    \\ strip_assume_tac (Q.SPEC ‘c’ integerTheory.INT_NUM_CASES)
    \\ gvs[npbcTheory.mk_bit_lit_def, npbcTheory.mk_lit_def]
    \\ Cases_on ‘b’ \\ Cases_on ‘bb’ \\ Cases_on ‘w' v’
    \\ gvs[] \\ intLib.ARITH_TAC)
  \\ rename1 ‘INR l’ \\ Cases_on ‘l’
  >- (
    rename1 ‘INR (Pos n)’
    \\ strip_assume_tac (Q.SPEC ‘c’ integerTheory.INT_NUM_CASES)
    \\ gvs[npbcTheory.mk_bit_lit_def, npbcTheory.mk_lit_def]
    \\ Cases_on ‘b’ \\ Cases_on ‘w' v’ \\ Cases_on ‘w' n’
    \\ gvs[npbcTheory.mk_lit_def] \\ intLib.ARITH_TAC)
  \\ rename1 ‘INR (Neg n)’
  \\ strip_assume_tac (Q.SPEC ‘c’ integerTheory.INT_NUM_CASES)
  \\ gvs[npbcTheory.mk_bit_lit_def, npbcTheory.mk_lit_def]
  \\ Cases_on ‘b’ \\ Cases_on ‘w' v’ \\ Cases_on ‘w' n’
  \\ gvs[npbcTheory.mk_lit_def] \\ intLib.ARITH_TAC
QED

(* The change made by the witness to the terms of l *)
Theorem delta_formal_terms:
  ∀l dts k dts' k'.
  delta_terms w (formal_terms m1 l []) dts k = (dts',k') ⇒
  &SUM (MAP (eval_term w') dts') − k' =
  &SUM (MAP (eval_term w') dts) − k +
  (&SUM (MAP (eval_term (assign (ord_ww m1 m2 w) w')) l) −
   &SUM (MAP (eval_term (assign (ord_ww m1 m2 (K NONE)) w')) l))
Proof
  Induct >- simp[formal_terms_def, delta_terms_def]
  \\ rpt strip_tac \\ rename1 ‘formal_terms m1 (t::l) []’
  \\ PairCases_on ‘t’
  \\ gvs[formal_terms_def]
  \\ Cases_on ‘map_lookup m1 t1’ \\ gvs[]
  >- (
    ‘assign (ord_ww m1 m2 w) w' t1 = assign (ord_ww m1 m2 (K NONE)) w' t1’ by
      simp[npbcTheory.assign_def, ord_ww_def]
    \\ pop_assum SUBST1_TAC
    \\ first_x_assum drule
    \\ qmatch_goalsub_abbrev_tac ‘&(_ + h) − &(_ + h)’
    \\ rpt (pop_assum kall_tac) \\ intLib.ARITH_TAC)
  \\ qmatch_asmsub_rename_tac ‘map_lookup m1 t1 = SOME q’ \\ PairCases_on ‘q’
  \\ gvs[]
  \\ qpat_x_assum ‘delta_terms _ _ _ _ = _’ mp_tac
  \\ once_rewrite_tac [formal_terms_acc]
  \\ simp[delta_terms_APPEND]
  \\ Cases_on ‘delta_terms w (formal_terms m1 l []) dts k’ \\ simp[]
  \\ strip_tac
  \\ first_x_assum drule
  \\ drule_all delta_one
  \\ disch_then (qspecl_then [‘w'’,‘m2’] mp_tac)
  \\ simp[]
  \\ qabbrev_tac ‘EA = Num (ABS t0) *
      if t0 < 0 then 1 − b2n (assign (ord_ww m1 m2 w) w' t1)
      else b2n (assign (ord_ww m1 m2 w) w' t1)’
  \\ qabbrev_tac ‘EB = Num (ABS t0) *
      if t0 < 0 then 1 − b2n (assign (ord_ww m1 m2 (K NONE)) w' t1)
      else b2n (assign (ord_ww m1 m2 (K NONE)) w' t1)’
  \\ rpt (pop_assum kall_tac) \\ intLib.ARITH_TAC
QED

(* A record's renamed constraint and its negation, corrected by the
  witness, are the constraint and its negation renamed under the witness *)
Theorem touched_rec_thm:
  compact c ⇒
  touched_rec w (subst (ord_ww m1 m2 (K NONE)) c)
    (formal_terms m1 (FST c) []) = subst (ord_ww m1 m2 w) c ∧
  touched_not w (not (subst (ord_ww m1 m2 (K NONE)) c))
    (formal_terms m1 (FST c) []) = not (subst (ord_ww m1 m2 w) c)
Proof
  strip_tac
  \\ Cases_on ‘delta_terms w (formal_terms m1 (FST c) []) [] 0’
  \\ rename1 ‘_ = (dts,k)’
  \\ Cases_on ‘clean_up dts’ \\ rename1 ‘clean_up dts = (srt,k2)’
  \\ ‘EVERY (λc. c ≠ 0) (MAP FST dts)’ by (
    drule delta_terms_nonzero \\ disch_then irule \\ simp[]
    \\ irule formal_terms_nonzero \\ Cases_on ‘c’ \\ gvs[])
  \\ ‘compact (srt, k − k2)’ by (
    drule_all npbcTheory.clean_up_sorted \\ simp[])
  \\ drule delta_formal_terms \\ strip_tac
  \\ drule_then assume_tac npbcTheory.clean_up_thm
  \\ simp[touched_rec_def, touched_not_def]
  \\ conj_tac
  >- (
    irule npbcTheory.compact_unique
    \\ simp[npbcTheory.compact_add, npbcTheory.compact_subst,
      npbcTheory.add_val, npbcTheory.subst_val]
    \\ qx_gen_tac ‘u’
    \\ qpat_x_assum ‘∀w' m2. _’ (qspecl_then [‘u’,‘m2’] mp_tac)
    \\ qpat_x_assum ‘∀w. _ = _ + k2’ (qspec_then ‘u’ mp_tac)
    \\ rpt (pop_assum kall_tac) \\ simp[] \\ intLib.ARITH_TAC)
  \\ Cases_on ‘not (srt,k − k2)’ \\ rename1 ‘_ = (nds,r)’ \\ simp[]
  \\ ‘compact (nds,r − 1)’ by (
    ‘compact (nds,r)’ by metis_tac[npbcTheory.compact_not]
    \\ gvs[])
  \\ irule npbcTheory.compact_unique
  \\ simp[npbcTheory.compact_add, npbcTheory.compact_subst,
    npbcTheory.compact_not, npbcTheory.add_val, npbcTheory.not_val,
    npbcTheory.subst_val]
  \\ qx_gen_tac ‘u’
  \\ mp_tac (Q.INST [‘w:num->bool’ |-> ‘u’, ‘c’ |-> ‘(srt,k − k2)’]
    npbcTheory.not_val)
  \\ qpat_x_assum ‘∀w' m2. _’ (qspecl_then [‘u’,‘m2’] mp_tac)
  \\ qpat_x_assum ‘∀w. _ = _ + k2’ (qspec_then ‘u’ mp_tac)
  \\ qpat_x_assum ‘not _ = _’ (simp o single)
  \\ ‘&SUM (MAP (eval_term u) (FST (subst (ord_ww m1 m2 w) c))) −
      SND (subst (ord_ww m1 m2 w) c) =
      &SUM (MAP (eval_term (assign (ord_ww m1 m2 w) u)) (FST c)) − SND c’ by
    simp[npbcTheory.subst_val]
  \\ pop_assum mp_tac
  \\ ‘&SUM (MAP (eval_term u) (FST (subst (ord_ww m1 m2 (K NONE)) c))) −
      SND (subst (ord_ww m1 m2 (K NONE)) c) =
      &SUM (MAP (eval_term (assign (ord_ww m1 m2 (K NONE)) u)) (FST c)) −
      SND c’ by
    simp[npbcTheory.subst_val]
  \\ pop_assum mp_tac
  \\ rpt (pop_assum kall_tac) \\ intLib.ARITH_TAC
QED

Theorem untouched_rec_thm:
  compact c ∧ EVERY (λ(c,v,b). w v = NONE) (formal_terms m1 (FST c) []) ⇒
  subst (ord_ww m1 m2 (K NONE)) c = subst (ord_ww m1 m2 w) c
Proof
  strip_tac
  \\ ‘touched_rec w (subst (ord_ww m1 m2 (K NONE)) c)
        (formal_terms m1 (FST c) []) = subst (ord_ww m1 m2 w) c’ by
    simp[touched_rec_thm]
  \\ pop_assum (SUBST1_TAC o SYM)
  \\ simp[touched_rec_def, delta_terms_untouched, npbcTheory.clean_up_def,
    npbcTheory.add_empty]
QED

Theorem fast_rn_MAPi:
  ∀w side rs ts j.
  SORTED $<= ts ⇒
  fast_rn w side rs ts j =
  MAPi (λi r. if MEM (i + j) ts then
      (case r of (c0,ncs,uts,vts,sl) =>
        touched_rec w c0 (if side then uts else vts))
    else FST r) rs
Proof
  recInduct fast_rn_ind \\ rpt strip_tac
  >- simp[fast_rn_def]
  \\ Cases_on ‘ts’
  >- (gvs[] \\ simp[Once fast_rn_def, combinTheory.o_DEF, ADD1])
  \\ rename1 ‘SORTED _ (x::xs)’
  \\ ‘transitive ($<= : num -> num -> bool)’ by
    simp[relationTheory.transitive_def]
  \\ ‘SORTED $<= xs ∧ ∀y. MEM y xs ⇒ x ≤ y’ by
    gvs[sortingTheory.SORTED_EQ]
  \\ gvs[]
  \\ simp[Once fast_rn_def, combinTheory.o_DEF, ADD1]
  \\ Cases_on ‘x < j’ \\ gvs[]
  \\ Cases_on ‘x = j’ \\ gvs[]
  >- (
    PairCases_on ‘r’ \\ gvs[]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM] \\ qx_gen_tac ‘i’
    \\ ‘j + (i + 1) = i + (j + 1)’ by decide_tac
    \\ pop_assum SUBST1_TAC \\ simp[])
  \\ ‘¬MEM j xs’ by (strip_tac \\ res_tac \\ decide_tac)
  \\ simp[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM] \\ qx_gen_tac ‘i’
  \\ ‘j + (i + 1) = i + (j + 1)’ by decide_tac
  \\ pop_assum SUBST1_TAC \\ simp[]
QED

Theorem fast_rn_not_MAPi:
  ∀w rs ts j.
  SORTED $<= ts ⇒
  fast_rn_not w rs ts j =
  MAPi (λi r. if MEM (i + j) ts then
      (case r of (c0,nc0,uts,vts,sl) => [touched_not w nc0 uts])
    else [FST (SND r)]) rs
Proof
  recInduct fast_rn_not_ind \\ rpt strip_tac
  >- simp[fast_rn_not_def]
  \\ Cases_on ‘ts’
  >- (gvs[] \\ simp[Once fast_rn_not_def, combinTheory.o_DEF, ADD1])
  \\ rename1 ‘SORTED _ (x::xs)’
  \\ ‘transitive ($<= : num -> num -> bool)’ by
    simp[relationTheory.transitive_def]
  \\ ‘SORTED $<= xs ∧ ∀y. MEM y xs ⇒ x ≤ y’ by
    gvs[sortingTheory.SORTED_EQ]
  \\ gvs[]
  \\ simp[Once fast_rn_not_def, combinTheory.o_DEF, ADD1]
  \\ Cases_on ‘x < j’ \\ gvs[]
  \\ Cases_on ‘x = j’ \\ gvs[]
  >- (
    PairCases_on ‘r’ \\ gvs[]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM] \\ qx_gen_tac ‘i’
    \\ ‘j + (i + 1) = i + (j + 1)’ by decide_tac
    \\ pop_assum SUBST1_TAC \\ simp[])
  \\ ‘¬MEM j xs’ by (strip_tac \\ res_tac \\ decide_tac)
  \\ simp[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM] \\ qx_gen_tac ‘i’
  \\ ‘j + (i + 1) = i + (j + 1)’ by decide_tac
  \\ pop_assum SUBST1_TAC \\ simp[]
QED

Theorem fast_rn_sc_MAPi:
  ∀w side rs ts j.
  SORTED $<= ts ⇒
  fast_rn_sc w side rs ts j =
  MAPi (λi r. if MEM (i + j) ts then
      (case r of (c0,ncs,uts,vts,sl) =>
        INL (touched_rec w c0 (if side then uts else vts)))
    else INR (SND (SND (SND (SND r))))) rs
Proof
  recInduct fast_rn_sc_ind \\ rpt strip_tac
  >- simp[fast_rn_sc_def]
  \\ Cases_on ‘ts’
  >- (gvs[] \\ simp[Once fast_rn_sc_def, combinTheory.o_DEF, ADD1])
  \\ rename1 ‘SORTED _ (x::xs)’
  \\ ‘transitive ($<= : num -> num -> bool)’ by
    simp[relationTheory.transitive_def]
  \\ ‘SORTED $<= xs ∧ ∀y. MEM y xs ⇒ x ≤ y’ by
    gvs[sortingTheory.SORTED_EQ]
  \\ gvs[]
  \\ simp[Once fast_rn_sc_def, combinTheory.o_DEF, ADD1]
  \\ Cases_on ‘x < j’ \\ gvs[]
  \\ Cases_on ‘x = j’ \\ gvs[]
  >- (
    PairCases_on ‘r’ \\ gvs[]
    \\ AP_THM_TAC \\ AP_TERM_TAC
    \\ simp[FUN_EQ_THM] \\ qx_gen_tac ‘i’
    \\ ‘j + (i + 1) = i + (j + 1)’ by decide_tac
    \\ pop_assum SUBST1_TAC \\ simp[])
  \\ ‘¬MEM j xs’ by (strip_tac \\ res_tac \\ decide_tac)
  \\ simp[]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM] \\ qx_gen_tac ‘i’
  \\ ‘j + (i + 1) = i + (j + 1)’ by decide_tac
  \\ pop_assum SUBST1_TAC \\ simp[]
QED

Theorem ord_touched_SORTED:
  SORTED $<= (ord_touched idx sr)
Proof
  simp[ord_touched_def]
  \\ mp_tac (Q.ISPECL [‘λx y:num. x ≤ y’, ‘ord_touched_aux idx sr []’]
    mllistTheory.sort_SORTED)
  \\ simp[relationTheory.transitive_def, relationTheory.total_def]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ simp[]
QED

Theorem MEM_ord_index_aux:
  ∀l t.
  MEM i (case lookup v (ord_index_aux t j l) of NONE => [] | SOME ids => ids) ⇔
  MEM i (case lookup v t of NONE => [] | SOME ids => ids) ∨
  (i = j ∧ ∃c b. MEM (c,v,b) l)
Proof
  Induct >- simp[ord_index_aux_def]
  \\ rpt strip_tac \\ rename1 ‘ord_index_aux t j (h::l)’
  \\ PairCases_on ‘h’ \\ simp[ord_index_aux_def, lookup_insert]
  \\ Cases_on ‘v = h1’ \\ gvs[]
  \\ Cases_on ‘lookup h1 t’ \\ gvs[]
  \\ metis_tac[]
QED

Theorem MEM_ord_index:
  ∀rs t j.
  MEM i (case lookup v (ord_index side t j rs) of NONE => [] | SOME ids => ids) ⇔
  MEM i (case lookup v t of NONE => [] | SOME ids => ids) ∨
  ∃k c b. k < LENGTH rs ∧ i = j + k ∧
    MEM (c,v,b)
      (case EL k rs of (c0,ncs,uts,vts,sl) => if side then uts else vts)
Proof
  Induct >- simp[ord_index_def]
  \\ rpt strip_tac \\ rename1 ‘ord_index side t j (r::rs)’
  \\ PairCases_on ‘r’
  \\ simp[ord_index_def, MEM_ord_index_aux, arithmeticTheory.LT_SUC,
    LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM, PULL_EXISTS]
  \\ simp[ADD1]
  \\ metis_tac[]
QED

Theorem MEM_ord_touched_aux[local]:
  ∀sr acc.
  MEM j (ord_touched_aux idx sr acc) ⇔
  MEM j acc ∨ ∃v x ids. MEM (v,x) sr ∧ map_lookup idx v = SOME ids ∧ MEM j ids
Proof
  Induct >- simp[ord_touched_aux_def]
  \\ rpt strip_tac \\ rename1 ‘ord_touched_aux idx (h::sr) acc’
  \\ PairCases_on ‘h’ \\ simp[ord_touched_aux_def]
  \\ Cases_on ‘map_lookup idx h0’
  \\ simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM]
  \\ simp[AC DISJ_ASSOC DISJ_COMM]
QED

(* Every record with a term on a variable that the witness maps is
  touched *)
Theorem ord_touched_complete:
  (∀v. (w:num -> (bool + num lit) option) v ≠ NONE ⇒ MEM v (MAP FST sr)) ∧
  k < LENGTH rs ∧
  MEM (c,v,b)
    (case EL k rs of (c0,ncs,uts,vts,sl) => if side then uts else vts) ∧
  w v ≠ NONE ⇒
  MEM k (ord_touched (mk_map [] (toAList (ord_index side LN 0 rs))) sr)
Proof
  strip_tac
  \\ simp[ord_touched_def, mllistTheory.sort_MEM, MEM_ord_touched_aux,
    spt_to_vecTheory.map_lookup_mk_map, ALOOKUP_toAList]
  \\ ‘MEM k (case lookup v (ord_index side LN 0 rs) of
       NONE => [] | SOME ids => ids)’ by (
    simp[MEM_ord_index] \\ qexistsl_tac [‘c’,‘b’] \\ simp[])
  \\ ‘MEM v (MAP FST sr)’ by metis_tac[]
  \\ gvs[MEM_MAP, EXISTS_PROD]
  \\ Cases_on ‘lookup v (ord_index side LN 0 rs)’ \\ gvs[]
  \\ metis_tac[]
QED

(* A record, touched (t) or not, renames its constraint and its negation
  as ord_ww does, if every record with a term on a mapped variable is
  touched *)
Theorem ord_rec_elem:
  compact c ∧
  (EXISTS (λ(c,v,b). w v ≠ NONE) (formal_terms m1 (FST c) []) ⇒ t) ⇒
  (if t then
     touched_rec w (subst (ord_ww m1 m2 (K NONE)) c)
       (formal_terms m1 (FST c) [])
   else subst (ord_ww m1 m2 (K NONE)) c) = subst (ord_ww m1 m2 w) c ∧
  (if t then
     touched_not w (not (subst (ord_ww m1 m2 (K NONE)) c))
       (formal_terms m1 (FST c) [])
   else not (subst (ord_ww m1 m2 (K NONE)) c)) =
    not (subst (ord_ww m1 m2 w) c)
Proof
  strip_tac \\ Cases_on ‘t’ \\ simp[touched_rec_thm]
  \\ ‘subst (ord_ww m1 m2 (K NONE)) c = subst (ord_ww m1 m2 w) c’ by (
    irule untouched_rec_thm
    \\ gvs[EXISTS_MEM, EVERY_MEM, FORALL_PROD] \\ metis_tac[])
  \\ simp[]
QED

(* The records of cs, with ids from off, renamed on side us (side) or vs,
  where m1 is that side's map *)
Theorem fast_rn_elems[local]:
  ∀cs off m1 m2 side us_xs vs_xs w ts.
  (∀i. i < LENGTH cs ⇒
     compact (EL i cs) ∧
     (EXISTS (λ(c,v,b). w v ≠ NONE) (formal_terms m1 (FST (EL i cs)) []) ⇒
      MEM (i + off) ts)) ∧
  ord_ww0 us_xs vs_xs = ord_ww m1 m2 (K NONE) ∧
  m1 = (if side then us_xs else vs_xs) ⇒
  MAPi (λi r. if MEM (i + off) ts then
      (case r of (c0,ncs,uts,vts,sl) =>
        touched_rec w c0 (if side then uts else vts))
    else FST r) (MAP (mk_ord_rec us_xs vs_xs) cs) =
    MAP (subst (ord_ww m1 m2 w)) cs ∧
  (side ⇒
    MAPi (λi r. if MEM (i + off) ts then
        (case r of (c0,nc0,uts,vts,sl) => [touched_not w nc0 uts])
      else [FST (SND r)]) (MAP (mk_ord_rec us_xs vs_xs) cs) =
    MAP (λc. [not (subst (ord_ww m1 m2 w) c)]) cs) ∧
  MAP sc_hyp_dec (MAPi (λi r. if MEM (i + off) ts then
      (case r of (c0,ncs,uts,vts,sl) =>
        INL (touched_rec w c0 (if side then uts else vts)))
    else INR (SND (SND (SND (SND r))))) (MAP (mk_ord_rec us_xs vs_xs) cs)) =
    MAP (subst (ord_ww m1 m2 w)) cs ∧
  EVERY sc_hyp_ok (MAPi (λi r. if MEM (i + off) ts then
      (case r of (c0,ncs,uts,vts,sl) =>
        INL (touched_rec w c0 (if side then uts else vts)))
    else INR (SND (SND (SND (SND r))))) (MAP (mk_ord_rec us_xs vs_xs) cs))
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on ‘side’ \\ gvs[]
  \\ rpt conj_tac
  \\ simp[LIST_EQ_REWRITE, EL_MAPi, EL_MAP, mk_ord_rec_def, EVERY_EL]
  \\ rpt strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ drule_all ord_rec_elem \\ strip_tac
  \\ rw[] \\ gvs[enc_mv_enc]
  \\ metis_tac[]
QED

(* The records of f and g renamed on side us (side) or vs; the vs side
  needs the keys of us_xs and vs_xs to be disjoint *)
Theorem fast_rn_ok:
  ∀f g side us_xs vs_xs w sr.
  EVERY (compact_terms o FST) f ∧ EVERY (compact_terms o FST) g ∧
  (side ∨ ∀n. map_lookup us_xs n = NONE ∨ map_lookup vs_xs n = NONE) ∧
  (∀v. w v ≠ NONE ⇒ MEM v (MAP FST sr)) ⇒
  let m1 = (if side then us_xs else vs_xs) in
  let m2 = (if side then vs_xs else us_xs) in
  let frs = MAP (mk_ord_rec us_xs vs_xs) f in
  let grs = MAP (mk_ord_rec us_xs vs_xs) g in
  let ts =
    ord_touched (mk_map [] (toAList (ord_index side LN 0 (frs ++ grs)))) sr in
  fast_rn w side frs ts 0 = MAP (subst (ord_ww m1 m2 w)) f ∧
  (side ⇒
    fast_rn_not w frs ts 0 = MAP (λc. [not (subst (ord_ww m1 m2 w) c)]) f) ∧
  MAP sc_hyp_dec (fast_rn_sc w side grs ts (LENGTH f)) =
    MAP (subst (ord_ww m1 m2 w)) g ∧
  EVERY sc_hyp_ok (fast_rn_sc w side grs ts (LENGTH f))
Proof
  rpt gen_tac \\ disch_then (map_every assume_tac o CONJUNCTS)
  \\ qabbrev_tac ‘m1 = if side then us_xs else vs_xs’
  \\ qabbrev_tac ‘m2 = if side then vs_xs else us_xs’
  \\ qabbrev_tac ‘rs = MAP (mk_ord_rec us_xs vs_xs) f ++
                        MAP (mk_ord_rec us_xs vs_xs) g’
  \\ qabbrev_tac
    ‘ts = ord_touched (mk_map [] (toAList (ord_index side LN 0 rs))) sr’
  \\ simp[]
  \\ ‘ord_ww0 us_xs vs_xs = ord_ww m1 m2 (K NONE)’ by (
    simp[Abbr ‘m1’, Abbr ‘m2’]
    \\ rw[ord_ww0_ord_ww] \\ gvs[] \\ irule ord_ww_swap \\ simp[])
  \\ ‘SORTED $<= ts’ by simp[Abbr ‘ts’, ord_touched_SORTED]
  \\ sg ‘∀k. k < LENGTH rs ∧
        EXISTS (λ(c,v,b). w v ≠ NONE)
          (case EL k rs of (c0,ncs,uts,vts,sl) => if side then uts else vts) ⇒
        MEM k ts’
  >- (
    qunabbrev_tac ‘ts’ \\ rpt strip_tac
    \\ gvs[EXISTS_MEM]
    \\ rename1 ‘MEM e _’ \\ PairCases_on ‘e’ \\ gvs[]
    \\ irule ord_touched_complete
    \\ simp[] \\ metis_tac[])
  \\ qspecl_then [‘f’,‘0’,‘m1’,‘m2’,‘side’,‘us_xs’,‘vs_xs’,‘w’,‘ts’]
    mp_tac fast_rn_elems
  \\ impl_tac
  >- (
    rpt conj_tac
    >- (
      rpt gen_tac \\ strip_tac
      \\ ‘compact_terms (FST (EL i f))’ by gvs[EVERY_EL]
      \\ conj_tac >- (Cases_on ‘EL i f’ \\ gvs[compact_terms_thm])
      \\ strip_tac
      \\ qpat_x_assum ‘∀k. _’ (qspec_then ‘i’ mp_tac)
      \\ simp[Abbr ‘rs’, EL_APPEND1, EL_MAP, mk_ord_rec_def]
      \\ disch_then irule
      \\ gvs[Abbr ‘m1’] \\ Cases_on ‘side’ \\ gvs[])
    >- simp[]
    \\ simp[Abbr ‘m1’])
  \\ qspecl_then [‘g’,‘LENGTH f’,‘m1’,‘m2’,‘side’,‘us_xs’,‘vs_xs’,‘w’,‘ts’]
    mp_tac fast_rn_elems
  \\ impl_tac
  >- (
    rpt conj_tac
    >- (
      rpt gen_tac \\ strip_tac
      \\ ‘compact_terms (FST (EL i g))’ by gvs[EVERY_EL]
      \\ conj_tac >- (Cases_on ‘EL i g’ \\ gvs[compact_terms_thm])
      \\ strip_tac
      \\ qpat_x_assum ‘∀k. _’ (qspec_then ‘i + LENGTH f’ mp_tac)
      \\ simp[Abbr ‘rs’, EL_APPEND2, EL_MAP, mk_ord_rec_def]
      \\ disch_then irule
      \\ gvs[Abbr ‘m1’] \\ Cases_on ‘side’ \\ gvs[])
    >- simp[]
    \\ simp[Abbr ‘m1’])
  \\ simp[fast_rn_MAPi, fast_rn_not_MAPi, fast_rn_sc_MAPi]
QED

Theorem dom_subst_list_thm:
  po = mk_ord_pre ord ∧ (∀v. w v ≠ NONE ⇒ MEM v (MAP FST sr)) ⇒
  (λ(nfs,gs). (nfs, MAP sc_hyp_dec gs)) (dom_subst_list hs w sr ord po) =
  (λ(fs,gs). (MAP (λc. [not c]) fs, gs)) (dom_subst hs w ord) ∧
  EVERY sc_hyp_ok (SND (dom_subst_list hs w sr ord po))
Proof
  strip_tac \\ gvs[]
  \\ Cases_on ‘mk_ord_pre ord’ \\ simp[dom_subst_list_def]
  >- (
    Cases_on ‘dom_subst hs w ord’
    \\ simp[MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP])
  \\ Cases_on ‘ord’ \\ gvs[mk_ord_pre_def]
  \\ rename1 ‘SOME aspo’ \\ PairCases_on ‘aspo’
  \\ gvs[mk_ord_pre_def, AllCaseEqs()]
  \\ simp[dom_subst_fast_def, dom_subst_ord_ww]
  \\ qspecl_then [‘aspo0’,‘aspo1’,‘T’,‘aspo6’,‘aspo7’,‘w’,‘sr’]
    mp_tac fast_rn_ok
  \\ rw[MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem ALOOKUP_ZIP_MEM[local]:
  ∀l1 l2. ALOOKUP (ZIP (l1,l2)) n = SOME y ⇒ MEM n l1
Proof
  Induct \\ Cases_on ‘l2’ \\ rw[ZIP_def] \\ metis_tac[]
QED

Theorem neg_dom_subst_fast_thm:
  mk_ord_pre (SOME aspo) = SOME p ∧ ord_maps_ok aspo ∧
  (∀v. w v ≠ NONE ⇒ MEM v (MAP FST sr)) ⇒
  (λ(fs,gs). (fs, MAP sc_hyp_dec gs)) (neg_dom_subst_fast w sr p) =
  neg_dom_subst w aspo ∧
  EVERY sc_hyp_ok (SND (neg_dom_subst_fast w sr p))
Proof
  strip_tac
  \\ PairCases_on ‘aspo’
  \\ gvs[mk_ord_pre_def, AllCaseEqs(), ord_maps_ok_def]
  \\ simp[neg_dom_subst_fast_def, neg_dom_subst_ord_ww]
  \\ ‘∀n. map_lookup (mk_map [] (ZIP (aspo2,aspo5))) n = NONE ∨
       map_lookup (mk_map [] (ZIP (aspo3,aspo5))) n = NONE’ by (
    rw[spt_to_vecTheory.map_lookup_mk_map]
    \\ Cases_on ‘ALOOKUP (ZIP (aspo3,aspo5)) n’ \\ simp[]
    \\ drule ALOOKUP_ZIP_MEM \\ strip_tac
    \\ gvs[EVERY_MEM, spt_to_vecTheory.map_lookup_mk_map])
  \\ qspecl_then [‘aspo0’,‘aspo1’,‘F’,‘mk_map [] (ZIP (aspo2,aspo5))’,
      ‘mk_map [] (ZIP (aspo3,aspo5))’,‘w’,‘sr’] mp_tac fast_rn_ok
  \\ simp[]
QED

(* Per variable: the indices of the constraints where it occurs
  positively and negatively, newest first. The ids up to m (the input
  constraints) are always kept. Until the variable is first read, the
  ids above m are capped: Vcount k counts their k insertions, and Vinput
  has dropped them. A read variable is tracked uncapped (Vtrack) *)
Datatype:
  vent = Vnone
       | Vtrack (num list) (num list)
       | Vcount num (num list) (num list)
       | Vinput (num list) (num list)
End

(* The positive and negative lists of an entry *)
Definition vent_lists_def[simp]:
  (vent_lists Vnone = ([],[]):num list # num list) ∧
  (vent_lists (Vtrack pinds ninds) = (pinds,ninds)) ∧
  (vent_lists (Vcount k pinds ninds) = (pinds,ninds)) ∧
  (vent_lists (Vinput pinds ninds) = (pinds,ninds))
End

(* The index (m, vw, entries): its entries cover the constraints below
  the watermark vw *)
Type vimap_ty = ``:num # num # vent list``;

Definition vent_mem_def:
  (vent_mem (m:num) Vnone pos i = F) ∧
  (vent_mem m (Vtrack pinds ninds) pos i =
    MEM (i:num) (if pos then pinds else ninds)) ∧
  (vent_mem m (Vcount k pinds ninds) pos i =
    MEM i (if pos then pinds else ninds)) ∧
  (vent_mem m (Vinput pinds ninds) pos i =
    (m < i ∨ MEM i (if pos then pinds else ninds)))
End

Definition ind_lim_def:
  ind_lim = 10n
End

(* Drops the ids above m from the front of a list *)
Definition drop_derived_def:
  (drop_derived (m:num) [] = []) ∧
  (drop_derived m (i::is) =
    if m < i then drop_derived m is else i::is)
End

(* The entry after inserting id i, where the variable occurs positively
  iff pos *)
Definition vent_insert_def:
  (vent_insert m pos i Vnone =
    let k = if i ≤ m then 0 else 1 in
    if pos then Vcount k [i] [] else Vcount k [] [i]) ∧
  (vent_insert m pos i (Vtrack pinds ninds) =
    if pos then Vtrack (i::pinds) ninds else Vtrack pinds (i::ninds)) ∧
  (vent_insert m pos i (Vcount k pinds ninds) =
    if i ≤ m then
      (if pos then Vcount k (i::pinds) ninds else Vcount k pinds (i::ninds))
    else if ind_lim ≤ k then
      Vinput (drop_derived m pinds) (drop_derived m ninds)
    else if pos then Vcount (k+1) (i::pinds) ninds
    else Vcount (k+1) pinds (i::ninds)) ∧
  (vent_insert m pos i (Vinput pinds ninds) =
    if i ≤ m then
      (if pos then Vinput (i::pinds) ninds else Vinput pinds (i::ninds))
    else Vinput pinds ninds)
End

(* Inserts id i for the first k terms of the slot cs, vs *)
Definition fill_slot_def:
  fill_slot m (ents:vent list) i cs vs k =
  if k = 0 then ents
  else
    let k1 = k - 1 in
    let x = sub_unsafe vs k1 in
    fill_slot m
      (update_resize ents Vnone
        (vent_insert m (0 ≤ (sub_unsafe cs k1):int) i
          (any_el x ents Vnone)) x)
      i cs vs k1
End

Definition fill_vimap_aux_def:
  fill_vimap_aux m fml ents (i:num) (id:num) =
  if id ≤ i then ents
  else
    let ents =
      (case any_el i fml Empty of
        Empty => ents
      | Stored cs vs d mc sm b => fill_slot m ents i cs vs (length vs)) in
    fill_vimap_aux m fml ents (i+1) id
Termination
  WF_REL_TAC`measure (λ(m,fml,ents,i,id). id - i)`
End

(* Indexes the constraints from the watermark up to id *)
Definition fill_vimap_def:
  fill_vimap fml id ((m,vw,ents):vimap_ty) =
  if id ≤ vw then (m,vw,ents)
  else (m, id, fill_vimap_aux m fml ents vw id)
End

(* Adds id i to the lists in t of the variables among the first k terms
  of the slot cs, vs *)
Definition rebuild_slot_def:
  rebuild_slot (t:(num list # num list) num_map) (i:num) cs vs k =
  if k = 0 then t
  else
    let k1 = k - 1 in
    let x = sub_unsafe vs k1 in
    case sptree$lookup x t of
      NONE => rebuild_slot t i cs vs k1
    | SOME (pinds,ninds) =>
      rebuild_slot
        (insert x
          (if 0 ≤ (sub_unsafe cs k1):int
           then (i::pinds,ninds) else (pinds,i::ninds)) t)
        i cs vs k1
End

(* Adds the ids from i up to vw, oldest first *)
Definition rebuild_aux_def:
  rebuild_aux fml t (i:num) (vw:num) =
  if vw ≤ i then t
  else
    let t =
      (case any_el i fml Empty of
        Empty => t
      | Stored cs vs d mc sm b => rebuild_slot t i cs vs (length vs)) in
    rebuild_aux fml t (i+1) vw
Termination
  WF_REL_TAC`measure (λ(fml,t,i,vw). vw - i)`
End

(* The lists read by rhs, added to acc when not empty *)
Definition get_inds_rhs_list_def:
  get_inds_rhs_list rhs (pinds:num list) ninds acc =
  (case rhs of
    INL b =>
      let l = if b then ninds else pinds in
      if NULL l then acc else l::acc
  | _ =>
      let acc = if NULL ninds then acc else ninds::acc in
      if NULL pinds then acc else pinds::acc)
End

(* The union of two lists *)
(* TMC *)
Definition merge_desc_def:
  (merge_desc [] ys = ys) ∧
  (merge_desc xs [] = xs) ∧
  (merge_desc (x::xs) (y::ys) =
    if x = y then x :: merge_desc xs ys
    else if (y:num) < x then x :: merge_desc xs (y::ys)
    else y :: merge_desc (x::xs) ys)
End

(* Merges the lists in adjacent pairs *)
(* TMC *)
Definition merge_pairs_def:
  (merge_pairs (l1::l2::ls) =
    let l = merge_desc l1 l2 in
    l :: merge_pairs ls) ∧
  (merge_pairs ls = ls)
End

Theorem LENGTH_merge_pairs:
  ∀ls. LENGTH (merge_pairs ls) ≤ LENGTH ls ∧
    (2 ≤ LENGTH ls ⇒ LENGTH (merge_pairs ls) < LENGTH ls)
Proof
  ho_match_mp_tac merge_pairs_ind>>
  rw[merge_pairs_def]
QED

(* The union of the lists, by rounds of pairwise merges *)
Definition merge_all_def:
  (merge_all [] = []) ∧
  (merge_all [l] = (l:num list)) ∧
  (merge_all ls = merge_all (merge_pairs ls))
Termination
  WF_REL_TAC`measure LENGTH`>>
  rpt strip_tac>>
  irule (CONJUNCT2 (SPEC_ALL LENGTH_merge_pairs))>>
  simp[]
End

Definition do_reindex_rhs_def:
  do_reindex_rhs fml rhs pinds ninds =
  (case rhs of
    INL b =>
    if b
    then (pinds, reindex fml ninds)
    else (reindex fml pinds, ninds)
  | _ =>
    (reindex fml pinds, reindex fml ninds))
End

(* Reads the witness variables: the read lists are added to acc, and the
  cleaned lists of the variables whose ids above m were dropped go to t *)
Definition get_inds_fold_def:
  (get_inds_fold fml [] acc ents t = (acc,ents,t)) ∧
  (get_inds_fold fml ((n,rhs)::xs) acc ents t =
    case any_el n ents Vnone of
      Vnone =>
      get_inds_fold fml xs acc
        (update_resize ents Vnone (Vtrack [] []) n) t
    | Vinput pinds ninds =>
      let (pinds,ninds) = do_reindex_rhs fml rhs pinds ninds in
      get_inds_fold fml xs acc ents (insert n (pinds,ninds) t)
    | e =>
      let (pinds,ninds) = vent_lists e in
      let (pinds,ninds) = do_reindex_rhs fml rhs pinds ninds in
      get_inds_fold fml xs (get_inds_rhs_list rhs pinds ninds acc)
        (update_resize ents Vnone (Vtrack pinds ninds) n) t)
End

(* Reads the rebuilt witness variables in t *)
Definition get_inds_rebuilt_def:
  (get_inds_rebuilt [] t acc ents = (acc,ents)) ∧
  (get_inds_rebuilt ((n,rhs)::xs) t acc ents =
    case sptree$lookup n t of
      NONE => get_inds_rebuilt xs t acc ents
    | SOME (pinds,ninds) =>
      get_inds_rebuilt xs t (get_inds_rhs_list rhs pinds ninds acc)
        (update_resize ents Vnone (Vtrack pinds ninds) n))
End

(* The indices of the constraints the witness s can change, and the index
  after the read; the variables whose ids above m were dropped are rebuilt
  by one walk of the constraints above m *)
Definition get_set_indices_def:
  get_set_indices fml s ((m,vw,ents):vimap_ty) =
  let (acc,ents,t) = get_inds_fold fml s [] ents LN in
  let (acc,ents) =
    (case t of
      LN => (acc,ents)
    | _ => get_inds_rebuilt s (rebuild_aux fml t (m+1) vw) acc ents) in
  (merge_all acc, (m,vw,ents))
End

(* Whether a step reads the index: its witness is not empty, or it checks
  that the auxiliary variables of the order are fresh *)
Definition reads_vimap_def:
  reads_vimap (s:var subst_raw) fresh (ord:ord_s option) ⇔
    ¬NULL s ∨
    fresh ∧
    (case ord of NONE => F
    | SOME (((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv) => ¬NULL as)
End

(* The variable occurs in no constraint below the watermark *)
Definition vent_fresh_def:
  (vent_fresh Vnone ⇔ T) ∧
  (vent_fresh (Vtrack pinds ninds) ⇔ NULL pinds ∧ NULL ninds) ∧
  (vent_fresh (Vcount k pinds ninds) ⇔ NULL pinds ∧ NULL ninds) ∧
  (vent_fresh (Vinput pinds ninds) ⇔ F)
End

Definition check_fresh_aux_fml_vimap_def:
  check_fresh_aux_fml_vimap as ((m,vw,ents):vimap_ty) ⇔
  EVERY (λx. vent_fresh (any_el x ents Vnone)) as
End

Definition check_fresh_aux_obj_vomap_def:
  check_fresh_aux_obj_vomap as vomap ⇔
  EVERY (λx. strlen vomap ≤ x ∨ strsub_unsafe vomap x = ^zw) as
End

Definition check_fresh_aspo_list_def:
  check_fresh_aspo_list fc s ord vimap vomap ⇔
  case ord of NONE => T
  | SOME (((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv) =>
    check_fresh_aux_fml_vimap as vimap ∧
    check_fresh_aux_obj_vomap as vomap ∧
    check_fresh_aux_constr_slot asv fc ∧
    check_fresh_aux_subst asv s
End

(* The part of check_fresh_aspo_list that does not read vimap, and the
  auxiliary variables to check against vimap *)
Definition mk_get_ord_def:
  mk_get_ord fc (s:var subst_raw) (ord:ord_s option) vomap =
  case ord of NONE => SOME (INL ())
  | SOME (((f,g,us,vs,as),xs),us_xs,vs_xs,xsv,asv) =>
    if
      check_fresh_aux_obj_vomap as vomap ∧
      check_fresh_aux_constr_slot asv fc ∧
      check_fresh_aux_subst asv s
    then SOME (INR as)
    else NONE
End

Theorem check_fresh_aspo_list_mk_get_ord:
  check_fresh_aspo_list fc s ord vimap vomap ⇔
  case mk_get_ord fc s ord vomap of
    NONE => F
  | SOME (INL ()) => T
  | SOME (INR as) => check_fresh_aux_fml_vimap as vimap
Proof
  rw[check_fresh_aspo_list_def,mk_get_ord_def]>>
  every_case_tac>>
  gvs[]>>
  metis_tac[]
QED

(* The fast path allows for faster checked deletion *)
Definition check_red_list_def:
  check_red_list pres ord po obj b tcb fml inds id fc mv s
    (pfs:scope) idopt vimap vomap assg st ht =
  if check_pres pres s
  then
  case red_fast idopt pfs of
    NONE => (
    let hs = has_scope pfs in
    let (untouched,skipped) = skip_ord_subgoal s ord in
    let fresh = (hs ∨ ¬ untouched) in
    let vimap =
      if reads_vimap s fresh ord then fill_vimap fml id vimap
      else vimap in
    let (rinds,vimap') = get_set_indices fml s vimap in
    let ss = mk_subst rinds s in
    let nfc = not_slot fc b in
    let (fml_not_c,id1,assg,st) = store_slot fml nfc mv id assg st in
    let (rsubs,rscopes) = fast_red_subgoals ord po ss s fc obj vomap hs in
    case extract_scopes_list rscopes ss b fml rsubs pfs of
      NONE => NONE
    | SOME cpfs =>
      (case check_scopes_list cpfs b
        fml_not_c id id1 assg st of
         NONE => NONE
      |  SOME(fml', id', assg', st') =>
        let rfml = rollback fml' id id' in
        let (res,ht') =
          do_red_check idopt b tcb fml' inds id ht
            ss rfml rinds nfc pfs rsubs skipped
          (fresh ⇒
            check_fresh_aspo_list fc s ord vimap' vomap) in
        if res then
          SOME (rfml,inds,vimap',id',assg',st',ht')
        else NONE))
  | SOME (pf,cid) =>
    check_red_list_fast b fml inds id fc mv pf cid vimap assg st ht
  else NONE
End

(* Stores slot s, whose largest variable is mv, at index id *)
Definition store_ind_def:
  store_ind fml s mv id inds assg st =
    let (fml',id',assg',st') = store_slot fml s mv id assg st in
    (fml', sorted_insert id inds, id', assg', st')
End

Definition opt_update_inds_def:
  (opt_update_inds fml NONE id inds assg st =
    (fml,inds,id,assg,st)) ∧
  (opt_update_inds fml (SOME (c,b)) id inds assg st =
    let (s,mv) = enc_mv c b in
    store_ind fml s mv id inds assg st)
End

(* The table before a top-level lstep: its deletions are counted *)
Definition ht_lstep_def:
  ht_lstep fml lstep ht =
  case lstep of
    Delete ls => ht_del fml ls ht
  | _ => ht
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) pres ord po obj tcb
    (fml: slot list) (inds:num list) (id:num)
    vimap vomap assg st ht =
  case sstep of
  | Lstep lstep =>
    (case check_lstep_list lstep F fml 0 id assg st of
      NONE => NONE
    | SOME (rfml,c,id',assg',st') =>
      let (fml',inds',id'',assg'',st'') =
        opt_update_inds rfml c id' inds assg' st' in
      SOME (fml',inds',vimap,id'',assg'',st'',ht_lstep fml lstep ht))
  | Red c s pfs idopt =>
    let (fc,mv) = enc_mv c tcb in
    case check_red_list pres ord po obj F tcb fml inds id fc mv s pfs
      idopt vimap vomap assg st ht of
      SOME (rfml,rinds,vimap',id',assg',st',ht') =>
      let (fml'',inds'',id'',assg'',st'') =
        store_ind rfml fc mv id' rinds assg' st' in
      SOME (fml'',inds'',vimap',id'',assg'',st'',ht')
    | NONE => NONE)
End

Theorem fml_rel_extract_clauses_list:
  ∀ls s b fml fmlls rsubs acc.
  fml_rel fml fmlls ⇒
  extract_clauses (subst_fun s) b fml rsubs ls acc =
  extract_clauses_list s b fmlls rsubs ls acc
Proof
  Induct>>rw[extract_clauses_def,extract_clauses_list_def]>>
  PairCases_on`h`>>
  Cases_on`h0`>>
  simp[extract_clauses_def,extract_clauses_list_def]>>
  PairCases_on`x`>>
  Cases_on`x0`
  >- (
    gvs[slot_CASE_default]>>
    Cases_on`lookup_core_only b fml x`
    >- (
      `lookup_core_only_list b fmlls x = Empty` by
        metis_tac[fml_rel_lookup_core_only_list]>>
      gvs[])>>
    `∃b'. lookup_core_only_list b fmlls x = enc x' b'` by
      metis_tac[fml_rel_lookup_core_only_list]>>
    gvs[subst_slot_enc])>>
  rw[]>>
  first_x_assum irule>>
  simp[]
QED

Theorem fml_rel_extract_scopes_list:
  ∀ls s b fml fmlls rsubs.
  fml_rel fml fmlls ⇒
  extract_scopes (MAP (MAP sc_hyp_dec) scopes) ls (subst_fun s) b fml rsubs =
  OPTION_MAP dec_scopes (extract_scopes_list scopes s b fmlls rsubs ls)
Proof
  Induct>>rw[]
  >- simp[extract_scopes_def,extract_scopes_list_def,dec_scopes_def]>>
  Cases_on`h`>> simp[extract_scopes_def,extract_scopes_list_def,mk_scope_def]>>
  first_x_assum (drule_then assume_tac)>>
  DEP_REWRITE_TAC [fml_rel_extract_clauses_list]>> simp[]>>
  Cases_on`q`>> simp[EL_MAP]>>
  every_case_tac>> gvs[dec_scopes_def]
QED

Theorem scopes_ok_extract_scopes_list:
  ∀ls cpfs.
  EVERY (EVERY sc_hyp_ok) scopes ∧
  extract_scopes_list scopes s b fmlls rsubs ls = SOME cpfs ⇒
  scopes_ok cpfs
Proof
  Induct>>rw[extract_scopes_list_def,scopes_ok_def]>>
  rename1`extract_scopes_list _ _ _ _ _ (h::_)`>>
  PairCases_on`h`>>gvs[extract_scopes_list_def,AllCaseEqs(),mk_scope_def]>>
  gvs[scopes_ok_def,EVERY_EL]
QED

(* Index list must lazily overapproximate the
  active indices in fmlls *)
Definition ind_rel_def:
  ind_rel fmlls inds ⇔
  ∀x. any_el x fmlls Empty ≠ Empty ⇒ MEM x inds
End

Theorem ind_rel_list_delete_list:
  ∀l fmlls.
  ind_rel fmlls inds ==>
  ind_rel (list_delete_list l fmlls) inds
Proof
  rw[ind_rel_def]>>
  gvs[any_el_list_delete_list,AllCaseEqs()]
QED

Theorem ind_rel_update_resize:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls Empty v n) (n::inds)
Proof
  simp[ind_rel_def,any_el_update_resize]>>rw[]>>
  Cases_on`x = n`>>gvs[]
QED

Theorem sorted_insert_thm:
  sorted_insert x [] = [x] ∧
  sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys else y::sorted_insert x ys
Proof
  conj_tac>>
  simp[Once sorted_insert_def]
QED

Theorem MEM_sorted_insert:
  ∀ls.
  MEM y (sorted_insert n ls) <=> MEM y (n::ls)
Proof
  Induct>>rw[sorted_insert_thm]>>fs[]>>
  metis_tac[]
QED

Theorem SORTED_sorted_insert:
  ∀ls.
  SORTED $>= ls ⇒
  SORTED $>= (sorted_insert n ls)
Proof
  Induct>>rw[sorted_insert_thm]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC [SORTED_EQ]>>
  simp[transitive_def]>>
  rw[]>>
  fs[MEM_sorted_insert]>>rw[]
QED

Theorem ind_rel_update_resize_sorted_insert:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls Empty v n) (sorted_insert n inds)
Proof
  strip_tac>> drule ind_rel_update_resize>>
  metis_tac[ind_rel_def,MEM_sorted_insert]
QED

Theorem ind_rel_rollback_2:
  ind_rel fmlls inds ∧
  (∀n. n ≥ id' ⇒ any_el n fml Empty = Empty) ∧
  (∀n. n < id ⇒ any_el n fmlls Empty = any_el n fml Empty)
  ⇒
  ind_rel (rollback fml id id') inds
Proof
  rw[rollback_list_delete]>>
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
  rw[rollback_list_delete]>>
  metis_tac[ind_rel_list_delete_list]
QED

Theorem list_insert_fml_list_id:
  ∀cs b id fmlls assg st cid cfmlls assg' st'.
  list_insert_fml_list cs b id fmlls assg st =
    (cid,cfmlls,assg',st') ⇒
  id ≤ cid
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  pairarg_tac>>gvs[opt_update_SOME]>>
  first_x_assum drule>>
  simp[]
QED

Theorem list_insert_fml_list_id_upper:
  ∀cs b id fmlls assg st cid cfmlls assg' st'.
  list_insert_fml_list cs b id fmlls assg st =
    (cid,cfmlls,assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
  (∀n. n ≥ cid ⇒ any_el n cfmlls Empty = Empty)
Proof
  Induct>>rw[list_insert_fml_list_def]
  >- gvs[]>>
  pairarg_tac>>gvs[opt_update_SOME]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem list_insert_fml_list_mindel:
  ∀cs b id fmlls assg st cid cfmlls assg' st'.
  list_insert_fml_list cs b id fmlls assg st =
    (cid,cfmlls,assg',st') ⇒
  (∀n. n < id ⇒ any_el n cfmlls Empty = any_el n fmlls Empty)
Proof
  Induct>>rw[list_insert_fml_list_def]>>
  pairarg_tac>>gvs[opt_update_SOME]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem fml_rel_list_insert_fml_list:
  ∀cs b id fml fmlls assg st cid cfml cid' cfmlls assg' st'.
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  list_insert_fml b fml id cs = (cfml,cid) ∧
  list_insert_fml_list cs b id fmlls assg st =
    (cid',cfmlls,assg',st') ⇒
  cid = cid' ∧
  fml_rel cfml cfmlls ∧ rup_inv cfmlls assg' st' ∧
  (∀n. n ≥ cid ⇒ any_el n cfmlls Empty = Empty) ∧
  (∀n. n < id ⇒ any_el n cfmlls Empty = any_el n fmlls Empty) ∧
  id ≤ cid
Proof
  Induct>>
  simp[list_insert_fml_def,list_insert_fml_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  rename1`opt_update fmlls _ id assg st = (fml1,id1,assg1,st1)`>>
  qpat_x_assum`opt_update _ _ _ _ _ = _` assume_tac>>
  drule_all rup_inv_opt_update>>
  drule_all fml_rel_opt_update>>
  rpt strip_tac>>
  gvs[insert_fml_def]>>
  `∀n. n ≥ id + 1 ⇒ any_el n fml1 Empty = Empty` by (
    qpat_x_assum`opt_update _ _ _ _ _ = _` mp_tac>>
    rw[opt_update_SOME]>>
    simp[any_el_update_resize])>>
  first_x_assum drule_all>>
  rw[]>>
  qpat_x_assum`opt_update _ _ _ _ _ = _` mp_tac>>
  rw[opt_update_SOME]>>
  gvs[any_el_update_resize]
QED

(* Scope hypotheses whose slots are encodings are inserted as their
  decoded constraints *)
Theorem list_insert_sc_list_eq:
  ∀hs b id fmlls assg st.
  EVERY sc_hyp_ok hs ⇒
  list_insert_sc_list hs b id fmlls assg st =
  list_insert_fml_list (MAP sc_hyp_dec hs) b id fmlls assg st
Proof
  Induct>>rw[list_insert_sc_list_def,list_insert_fml_list_def]>>
  gvs[sc_slot_enc,store_slot_enc]
QED

(* Each scope hypothesis is stored at the next id *)
Theorem store_slot_step[local]:
  store_slot fml s mv id assg st = (fml',id',assg',st') ⇒
  fml' = update_resize fml Empty s id ∧ id' = id + 1
Proof
  rw[store_slot_def]>>
  pairarg_tac>>gvs[]
QED

Theorem list_insert_sc_list_id:
  ∀cs b id fmlls assg st cid cfmlls assg' st'.
  list_insert_sc_list cs b id fmlls assg st =
    (cid,cfmlls,assg',st') ⇒
  id ≤ cid
Proof
  Induct>>rw[list_insert_sc_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  drule store_slot_step>>strip_tac>>gvs[]>>
  first_x_assum drule>>
  simp[]
QED

Theorem list_insert_sc_list_id_upper:
  ∀cs b id fmlls assg st cid cfmlls assg' st'.
  list_insert_sc_list cs b id fmlls assg st =
    (cid,cfmlls,assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
  (∀n. n ≥ cid ⇒ any_el n cfmlls Empty = Empty)
Proof
  Induct>>rw[list_insert_sc_list_def]
  >- gvs[]>>
  rpt (pairarg_tac>>gvs[])>>
  drule store_slot_step>>strip_tac>>gvs[]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem list_insert_sc_list_mindel:
  ∀cs b id fmlls assg st cid cfmlls assg' st'.
  list_insert_sc_list cs b id fmlls assg st =
    (cid,cfmlls,assg',st') ⇒
  (∀n. n < id ⇒ any_el n cfmlls Empty = any_el n fmlls Empty)
Proof
  Induct>>rw[list_insert_sc_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  drule store_slot_step>>strip_tac>>gvs[]>>
  first_x_assum drule>>
  simp[any_el_update_resize]
QED

Theorem fml_rel_check_subproofs_list:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st' fml.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    mindel ≤ id ∧
    check_subproofs_list pfs b fmlls mindel id assg st =
      SOME (fmlls', id', assg', st') ⇒
    ∃fml'.
      check_subproofs pfs b fml id =
        SOME (fml',id') ∧
      fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st'
Proof
  ho_match_mp_tac check_subproofs_list_ind>>rw[]>>
  fs[check_subproofs_def,check_subproofs_list_def]>>
  gvs[AllCaseEqs()]
  >- (
    drule_all (CONJUNCT2 fml_rel_check_lstep_list)>>
    rw[]>>simp[]>>
    first_x_assum irule>>
    simp[]>>
    drule (CONJUNCT2 check_lstep_list_id)>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    simp[])>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs()]>>
  rename1`list_insert_fml_list _ _ _ _ _ _ = (cid1,cfmlls,assg1,st1)`>>
  rename1`check_lsteps_list _ _ _ _ _ _ _ = SOME (fml2,id2,assg2,st2)`>>
  drule_all fml_rel_list_insert_fml_list>>
  strip_tac>>gvs[]>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule_at (Pos last) (CONJUNCT2 fml_rel_check_lstep_list)>>
  disch_then (qspec_then`cfml` mp_tac)>>
  simp[]>>
  strip_tac>>
  simp[]>>
  drule_all fml_rel_check_contradiction_fml>>
  strip_tac>>
  simp[]>>
  drule (CONJUNCT2 check_lstep_list_id)>>
  drule (CONJUNCT2 check_lstep_list_id_upper)>>
  drule (CONJUNCT2 check_lstep_list_mindel)>>
  rpt strip_tac>>
  first_x_assum irule>>
  rw[]
  >~[`fml_rel fml (rollback _ _ _)`] >- (
    irule fml_rel_rollback>>
    qexists_tac`fmlls`>>
    rw[]>>
    gvs[])
  >~[`rup_inv (rollback _ _ _) _ _`] >-
    (metis_tac[rup_inv_rollback])>>
  simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem check_subproofs_list_id:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st'.
    check_subproofs_list pfs b fmlls mindel id assg st =
    SOME (fmlls', id',assg',st') ⇒
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
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st'.
  check_subproofs_list pfs b fmlls mindel id assg st =
    SOME (fmlls', id',assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty)
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  simp[check_subproofs_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  simp[AllCaseEqs()]>>
  rpt gen_tac>>
  strip_tac>>
  gvs[]
  >- (
    rpt strip_tac>>
    qpat_x_assum`_ ⇒ _` (irule_at Any)>>
    simp[]>>
    qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` assume_tac>>
    drule (CONJUNCT2 check_lstep_list_id_upper)>>
    simp[])>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  rpt strip_tac>>
  qpat_x_assum`_ ⇒ _` (irule_at Any)>>
  simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  rw[]>>
  qpat_x_assum`list_insert_fml_list _ _ _ _ _ _ = _` assume_tac>>
  drule list_insert_fml_list_id_upper>>
  simp[]>>
  strip_tac>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule (CONJUNCT2 check_lstep_list_id_upper)>>
  simp[]
QED

Theorem check_subproofs_list_mindel:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st' n.
  check_subproofs_list pfs b fmlls mindel id assg st =
    SOME (fmlls', id', assg', st') ∧
  mindel ≤ id ∧
  n < mindel ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
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
  gvs[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem fml_rel_check_scopes_list:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st' fml.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    mindel ≤ id ∧ scopes_ok pfs ∧
    check_scopes_list pfs b fmlls mindel id assg st =
      SOME (fmlls', id', assg', st') ⇒
    ∃fml'.
      check_scopes (dec_scopes pfs) b fml id =
        SOME (fml',id') ∧
      fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st'
Proof
  ho_match_mp_tac check_scopes_list_ind>>rw[]>>
  fs[check_scopes_def,check_scopes_list_def,dec_scopes_def,scopes_ok_def]>>
  gvs[AllCaseEqs()]
  >- (
    drule_all fml_rel_check_subproofs_list>>
    rw[]>>simp[]>>
    first_x_assum irule>>
    simp[]>>
    drule check_subproofs_list_id>>
    drule check_subproofs_list_id_upper>>
    simp[])>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs(),list_insert_sc_list_eq]>>
  rename1`list_insert_fml_list _ _ _ _ _ _ = (cid1,cfmlls,assg1,st1)`>>
  rename1`check_subproofs_list _ _ _ _ _ _ _ = SOME (fml2,id2,assg2,st2)`>>
  drule_all fml_rel_list_insert_fml_list>>
  strip_tac>>gvs[]>>
  qpat_x_assum`check_subproofs_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule_at (Pos last) fml_rel_check_subproofs_list>>
  disch_then (qspec_then`cfml` mp_tac)>>
  simp[]>>
  strip_tac>>
  simp[]>>
  drule check_subproofs_list_id>>
  drule check_subproofs_list_id_upper>>
  drule check_subproofs_list_mindel>>
  rpt strip_tac>>
  first_x_assum irule>>
  rw[]
  >~[`fml_rel fml (rollback _ _ _)`] >- (
    irule fml_rel_rollback>>
    qexists_tac`fmlls`>>
    rw[]>>
    gvs[])
  >~[`rup_inv (rollback _ _ _) _ _`] >-
    (metis_tac[rup_inv_rollback])>>
  simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem check_scopes_list_id:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st'.
    check_scopes_list pfs b fmlls mindel id assg st =
    SOME (fmlls', id',assg',st') ⇒
    id ≤ id'
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  rw[check_scopes_list_def]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  imp_res_tac check_subproofs_list_id>>
  imp_res_tac list_insert_sc_list_id>>
  gvs[]
QED

Theorem check_scopes_list_id_upper:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st'.
  check_scopes_list pfs b fmlls mindel id assg st =
    SOME (fmlls', id',assg',st') ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ⇒
  (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty)
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  simp[check_scopes_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  simp[AllCaseEqs()]>>
  rpt gen_tac>>
  strip_tac>>
  gvs[]
  >- (
    rpt strip_tac>>
    qpat_x_assum`_ ⇒ _` (irule_at Any)>>
    simp[]>>
    qpat_x_assum`check_subproofs_list _ _ _ _ _ _ _ = _` assume_tac>>
    drule check_subproofs_list_id_upper>>
    simp[])>>
  rpt(pairarg_tac>>fs[])>>
  gvs[AllCaseEqs()]>>
  rpt strip_tac>>
  qpat_x_assum`_ ⇒ _` (irule_at Any)>>
  simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  rw[]>>
  qpat_x_assum`list_insert_sc_list _ _ _ _ _ _ = _` assume_tac>>
  drule list_insert_sc_list_id_upper>>
  simp[]>>
  strip_tac>>
  qpat_x_assum`check_subproofs_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule check_subproofs_list_id_upper>>
  simp[]
QED

Theorem check_scopes_list_mindel:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st' n.
  check_scopes_list pfs b fmlls mindel id assg st =
    SOME (fmlls', id', assg', st') ∧
  mindel ≤ id ∧
  n < mindel ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
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
  drule (list_insert_sc_list_mindel)>>fs[]>>
  rw[]>>
  drule (list_insert_sc_list_id)>>
  drule check_subproofs_list_id>>rw[]>>
  gvs[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem reindex_aux:
  ∀inds iacc.
  reindex_aux fmlls inds iacc =
  let is = FILTER (λx. any_el x fmlls Empty ≠ Empty) inds in
  (REVERSE iacc ++ is)
Proof
  Induct>>rw[reindex_aux_def]>>
  Cases_on`any_el h fmlls Empty`>>gvs[]
QED

Theorem reindex_characterize:
  reindex fmlls inds = FILTER (λx. any_el x fmlls Empty ≠ Empty) inds
Proof
  rw[reindex_def,reindex_aux]
QED

(* A hit in the table is a constraint of the formula, wherever the walk
  starts *)
Theorem ht_mem_core_only_fml:
  ∀b fmlls c tbl j fuel.
  fml_rel fml fmlls ∧
  ht_mem b fmlls c tbl j fuel ⇒
  c ∈ core_only_fml b fml
Proof
  ho_match_mp_tac ht_mem_ind>>
  rpt gen_tac>>
  strip_tac>>
  simp[Once ht_mem_def,eq_stored_def]>>
  rw[]>>
  gvs[]>>
  rename1`lookup_core_only_list b fmlls i`>>
  Cases_on`lookup_core_only_list b fmlls i`>>
  gvs[]>>
  `lookup_core_only_list b fmlls i ≠ Empty` by simp[]>>
  drule_all fml_rel_lookup_core_only_enc>>
  rw[]>>
  gvs[eq_slot_enc,lookup_core_only_def,core_only_fml_def,AllCaseEqs()]>>
  rw[]>>
  metis_tac[]
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

Theorem fml_rel_subst_opt_slot:
  fml_rel fmls fml ⇒
  subst_opt_slot s (lookup_core_only_list b fml i) =
  case lookup_core_only b fmls i of
    NONE => NONE
  | SOME c => subst_opt (subst_fun s) c
Proof
  rw[]>>
  Cases_on`lookup_core_only b fmls i`
  >- (
    `lookup_core_only_list b fml i = Empty` by
      metis_tac[fml_rel_lookup_core_only_list]>>
    simp[subst_opt_slot_def])>>
  `∃b'. lookup_core_only_list b fml i = enc x b'` by
    metis_tac[fml_rel_lookup_core_only_list]>>
  simp[subst_opt_slot_enc]
QED

Theorem MEM_subst_indexes:
  ∀inds i c.
  fml_rel fmls fml ∧
  MEM i inds ∧
  lookup_core_only b fmls i = SOME c ∧
  subst_opt (subst_fun s) c = SOME res
  ⇒
  MEM (i,res) (subst_indexes s b fml inds)
Proof
  Induct>>rw[subst_indexes_def]>>
  drule fml_rel_subst_opt_slot>>
  strip_tac>>
  gvs[]>>
  TOP_CASE_TAC>>
  gvs[]
QED

Theorem subst_indexes_MEM:
  ∀inds i res.
  fml_rel fmls fml ∧
  MEM (i,res) (subst_indexes s b fml inds) ⇒
  ∃c.
  MEM i inds ∧
  lookup_core_only b fmls i = SOME c ∧
  subst_opt (subst_fun s) c = SOME res
Proof
  Induct>>rw[subst_indexes_def]>>
  qpat_x_assum`MEM _ _` mp_tac>>
  drule fml_rel_subst_opt_slot>>
  disch_then (fn th => simp[th])>>
  Cases_on`lookup_core_only b fmls h`>>simp[]
  >- metis_tac[]>>
  Cases_on`subst_opt (subst_fun s) x`>>simp[]>>
  rw[]>>
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

(* The spec's goal check, one goal at a time *)
Theorem split_goals_MEM:
  (∀i c. MEM (i,c) goals ∧ lookup i proved = NONE ⇒
    c ∈ range fml ∨ imp nc c ∨ ∃j. MEM (j,c) goals ∧ lookup j proved ≠ NONE) ⇒
  split_goals fml nc proved goals
Proof
  rw[split_goals_def,PARTITION_DEF]>>
  pairarg_tac>>rw[]>>
  qpat_x_assum`_ = (_,_)` (ASSUME_TAC o SYM)>>
  drule PARTs_HAVE_PROP>>
  drule PART_MEM>>
  rw[]>>
  fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
  fs[MEM_MAP,EXISTS_PROD,mem_constraint_thm]>>
  metis_tac[]
QED

Theorem MEM_split_goals_pure:
  ∀goals lp lf lp' lf'.
  split_goals_pure proved extra goals lp lf = (lp',lf') ⇒
  (∀c. MEM c lp' ⇔ MEM c lp ∨
    ∃i. MEM (i,c) goals ∧ map_lookup proved i ≠ NONE) ∧
  (∀c. MEM c lf' ⇔ MEM c lf ∨
    ∃i. MEM (i,c) goals ∧ map_lookup proved i = NONE ∧ ¬imp_slot extra c)
Proof
  Induct>>
  simp[split_goals_pure_def,FORALL_PROD]>>
  rw[]>>
  first_x_assum drule>>
  rw[]>>
  metis_tac[]
QED

Theorem ht_goals_EVERY:
  ∀cs.
  ht_goals b fml lp tbl cs ⇔
  EVERY (λc. ht_probe b fml c (hash_constraint c) tbl ∨ mem_constraint c lp) cs
Proof
  Induct>>
  rw[ht_goals_def]
QED

(* The INL proved ids as keys of a list, and the INR ones as a set, are
  extract_pids's *)
Theorem extract_pids_list_thm:
  ∀pf l r l1.
  (∀i. lookup i l1 = NONE ⇔ ALOOKUP l i = NONE) ⇒
  SND (extract_pids_list pf l r) = SND (extract_pids pf l1 r) ∧
  ∀i. lookup i (FST (extract_pids pf l1 r)) = NONE ⇔
      ALOOKUP (FST (extract_pids_list pf l r)) i = NONE
Proof
  Induct >- simp[extract_pids_list_def,extract_pids_def]>>
  rpt gen_tac>>strip_tac>>
  rename1`extract_pids_list (cpf::pf) l r`>>
  simp[extract_pids_list_def,extract_pids_def]>>
  Cases_on`FST cpf`>>simp[]>>
  rename1`SOME p`>>PairCases_on`p`>>Cases_on`p0`>>simp[]>>
  first_x_assum irule>>
  rw[lookup_insert]>>
  metis_tac[]
QED

Theorem extract_scoped_pids_list_thm:
  ∀pfs l r l1.
  (∀i. lookup i l1 = NONE ⇔ ALOOKUP l i = NONE) ⇒
  SND (extract_scoped_pids_list pfs l r) = SND (extract_scoped_pids pfs l1 r) ∧
  ∀i. lookup i (FST (extract_scoped_pids pfs l1 r)) = NONE ⇔
      ALOOKUP (FST (extract_scoped_pids_list pfs l r)) i = NONE
Proof
  Induct >- simp[extract_scoped_pids_list_def,extract_scoped_pids_def]>>
  rpt gen_tac>>strip_tac>>
  rename1`extract_scoped_pids_list (h::pfs) l r`>>PairCases_on`h`>>
  simp[extract_scoped_pids_list_def,extract_scoped_pids_def]>>
  Cases_on`extract_scope_val h0`>>simp[]>>
  qspecl_then [`h1`,`l`,`r`,`l1`] mp_tac extract_pids_list_thm>>
  simp[]>>
  Cases_on`extract_pids_list h1 l r`>>Cases_on`extract_pids h1 l1 r`>>
  rw[]
QED

Theorem split_goals_hash_imp_split_goals:
  fml_rel fml fmlls ∧
  split_goals_hash b fmlls inds base ht (enc nc b0) pids goals = (T,ht') ∧
  (∀i. lookup i proved ≠ NONE ⇔ ALOOKUP pids i ≠ NONE) ⇒
  split_goals (mk_core_fml b fml) nc proved goals
Proof
  rw[split_goals_hash_def,split_goals_pids_def]>>
  pairarg_tac>>gvs[]>>
  irule split_goals_MEM>>
  drule MEM_split_goals_pure>>
  rw[spt_to_vecTheory.map_lookup_mk_map]>>
  Cases_on`imp_slot (enc nc b0) c`
  >- gvs[imp_slot_enc]>>
  `MEM c lf` by metis_tac[]>>
  `¬NULL lf` by (Cases_on`lf`>>gvs[])>>
  qpat_x_assum`(if _ then _ else _) = _` mp_tac>>
  simp[]>>
  qabbrev_tac`HT = ht_fill fmlls inds base ht`>>
  PairCases_on`HT`>>
  simp[ht_goals_EVERY,EVERY_MEM]>>
  strip_tac>>
  first_x_assum (qspec_then`c` mp_tac)>>
  impl_tac >- metis_tac[]>>
  strip_tac
  >- (
    disj1_tac>>
    simp[range_mk_core_fml]>>
    metis_tac[ht_mem_core_only_fml,ht_probe_def])>>
  metis_tac[mem_constraint_thm]
QED

Theorem lookup_core_only_list_list_delete_list:
  ∀ls n fml.
  lookup_core_only_list b
    (list_delete_list ls fml) n =
  if MEM n ls then Empty
  else
    lookup_core_only_list b fml n
Proof
  rw[lookup_core_only_list_def,core_only_def,any_el_list_delete_list]>>
  gvs[]
QED

(* The Delete step's check and deletion in one pass over the ids *)
Definition delete_ids_list_def:
  (delete_ids_list mindel fml [] = SOME fml) ∧
  (delete_ids_list mindel fml (i::is) =
    if mindel ≤ i ∧ lookup_core_only_list T fml i = Empty then
      delete_ids_list mindel (delete_list i fml) is
    else NONE)
End

Theorem delete_ids_list_eq:
  ∀ls fml.
  delete_ids_list mindel fml ls =
  if EVERY (λid. mindel ≤ id ∧ lookup_core_only_list T fml id = Empty) ls
  then SOME (list_delete_list ls fml)
  else NONE
Proof
  Induct >> rw[delete_ids_list_def,list_delete_list_def] >>
  `delete_list h fml = list_delete_list [h] fml` by
    simp[list_delete_list_def] >>
  pop_assum SUBST_ALL_TAC >>
  `∀id. lookup_core_only_list T (list_delete_list [h] fml) id =
        lookup_core_only_list T fml id` by
    rw[lookup_core_only_list_list_delete_list] >>
  gvs[] >> metis_tac[NOT_EVERY]
QED

(* Every occurrence in a constraint below the watermark is indexed *)
Definition vimap_rel_def:
  vimap_rel fmlls ((m,vw,ents):vimap_ty) ⇔
  ∀i coeff x.
    i < vw ∧
    MEM (coeff:int,x) (FST (dec (any_el i fmlls Empty))) ⇒
    vent_mem m (any_el x ents Vnone) (0 ≤ coeff) i
End

Theorem subst_opt_aux_MEM:
  ∀c old new k.
  subst_opt_aux f c = (old,new,k,F) ⇒
  ∃coeff x. MEM (coeff,x) c ∧
    IS_SOME (f x) ∧
    f x ≠ SOME (INL (0 ≤ coeff))
Proof
  Induct>> simp[npbcTheory.subst_opt_aux_def]>>
  Cases>>
  rw[npbcTheory.subst_opt_aux_def]>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  every_case_tac>>gvs[]
  >- metis_tac[IS_SOME_EXISTS]
  >- metis_tac[IS_SOME_EXISTS]
  >> (
    simp[IS_SOME_EXISTS,PULL_EXISTS]>>
    first_assum (irule_at Any)>>
    simp[]>>
    metis_tac[])
QED

Theorem IS_SOME_subst_opt:
  IS_SOME (subst_opt f c) ⇒
  ∃coeff x. MEM (coeff,x) (FST c) ∧
    IS_SOME (f x) ∧
    f x ≠ SOME (INL (0 ≤ coeff))
Proof
  Cases_on`c`>>rw[npbcTheory.subst_opt_eq]>>
  rpt (pairarg_tac>>fs[])>>
  every_case_tac>>gvs[]>>
  metis_tac[subst_opt_aux_MEM]
QED

Theorem vec_lookup_empty[simp]:
  vec_lookup (Vector []) x = NONE
Proof
  EVAL_TAC
QED

Theorem MEM_dec_Stored:
  length cs = length vs ⇒
  (MEM (c,x) (FST (dec (Stored cs vs d mc sm b))) ⇔
    ∃l. l < length vs ∧ c = sub cs l ∧ x = sub vs l)
Proof
  rw[dec_def,dec_terms_GENLIST,MEM_GENLIST]>>
  metis_tac[]
QED

Theorem EXISTS_MEM_dec_Stored:
  length cs = length vs ⇒
  ((∃c. MEM (c,x) (FST (dec (Stored cs vs d mc sm b))) ∧ P c) ⇔
   ∃l. l < length vs ∧ sub vs l = x ∧ P (sub cs l))
Proof
  rw[MEM_dec_Stored]>>
  metis_tac[]
QED

Theorem MEM_drop_derived:
  ∀l. MEM j (drop_derived m l) ⇒ MEM j l
Proof
  Induct>>rw[drop_derived_def]>>gvs[]
QED

Theorem MEM_drop_derived_input:
  ∀l. j ≤ m ∧ MEM j l ⇒ MEM j (drop_derived m l)
Proof
  Induct>>rw[drop_derived_def]>>gvs[]
QED

Theorem vent_mem_vent_insert:
  vent_mem m e pos j ⇒ vent_mem m (vent_insert m pos' i e) pos j
Proof
  Cases_on`e`>>rw[vent_insert_def,vent_mem_def]>>gvs[]>>
  Cases_on`m < j`>>gvs[NOT_LESS]>>
  metis_tac[MEM_drop_derived_input]
QED

Theorem vent_mem_vent_insert_self:
  vent_mem m (vent_insert m pos i e) pos i
Proof
  Cases_on`e`>>rw[vent_insert_def,vent_mem_def]
QED

Theorem fill_slot_vent_mem:
  ∀k ents.
  (∀x pos j.
    vent_mem m (any_el x ents Vnone) pos j ⇒
    vent_mem m (any_el x (fill_slot m ents i cs vs k) Vnone) pos j) ∧
  (∀l. l < k ⇒
    vent_mem m (any_el (sub vs l) (fill_slot m ents i cs vs k) Vnone)
      (0 ≤ sub cs l) i)
Proof
  Induct>>
  ONCE_REWRITE_TAC[fill_slot_def]>>
  simp[]>>
  rpt gen_tac>>
  qmatch_goalsub_abbrev_tac`fill_slot m ents1 i cs vs k`>>
  `∀y pos j. vent_mem m (any_el y ents Vnone) pos j ⇒
    vent_mem m (any_el y ents1 Vnone) pos j` by (
    rw[Abbr`ents1`,any_el_update_resize]>>
    metis_tac[vent_mem_vent_insert])>>
  `vent_mem m (any_el (sub vs k) ents1 Vnone) (0 ≤ sub cs k) i` by
    simp[Abbr`ents1`,any_el_update_resize,vent_mem_vent_insert_self]>>
  rw[]>>
  Cases_on`l = k`
  >- metis_tac[]>>
  `l < k` by simp[]>>
  metis_tac[]
QED

Theorem fill_vimap_aux_vent_mem:
  ∀n i ents.
  n = id - i ∧
  (∀k. wf_slot (any_el k fml Empty)) ⇒
  (∀x pos j.
    vent_mem m (any_el x ents Vnone) pos j ⇒
    vent_mem m (any_el x (fill_vimap_aux m fml ents i id) Vnone) pos j) ∧
  (∀k coeff y.
    i ≤ k ∧ k < id ∧ MEM (coeff,y) (FST (dec (any_el k fml Empty))) ⇒
    vent_mem m (any_el y (fill_vimap_aux m fml ents i id) Vnone)
      (0 ≤ coeff) k)
Proof
  completeInduct_on`n`>>
  rpt gen_tac>>strip_tac>>
  ONCE_REWRITE_TAC[fill_vimap_aux_def]>>
  IF_CASES_TAC>- (rw[]>>gvs[])>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`fill_vimap_aux m fml ents1 (i + 1) id`>>
  qpat_x_assum`∀m'. m' < n ⇒ _` (qspec_then`id - (i + 1)` mp_tac)>>
  impl_tac>- simp[]>>
  disch_then (qspecl_then [`i + 1`,`ents1`] mp_tac)>>
  impl_tac>- simp[]>>
  strip_tac>>
  `∀y pos j. vent_mem m (any_el y ents Vnone) pos j ⇒
    vent_mem m (any_el y ents1 Vnone) pos j` by (
    rw[Abbr`ents1`]>>
    TOP_CASE_TAC>>gvs[fill_slot_vent_mem])>>
  `∀coeff y. MEM (coeff,y) (FST (dec (any_el i fml Empty))) ⇒
    vent_mem m (any_el y ents1 Vnone) (0 ≤ coeff) i` by (
    `wf_slot (any_el i fml Empty)` by simp[]>>
    rw[Abbr`ents1`]>>
    Cases_on`any_el i fml Empty`>>gvs[wf_slot_def,MEM_dec_Stored]>>
    metis_tac[fill_slot_vent_mem])>>
  rw[]>>
  Cases_on`k = i`>>gvs[]
QED

(* The index after a store at or above the watermark *)
Theorem vimap_rel_update_resize:
  vimap_rel fml vimap ∧ FST (SND vimap) ≤ n ⇒
  vimap_rel (update_resize fml Empty s n) vimap
Proof
  PairCases_on`vimap`>>
  rw[vimap_rel_def,any_el_update_resize]>>
  gvs[]
QED

(* After the fill, the index covers every constraint below id *)
Theorem vimap_rel_fill_vimap:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  fill_vimap fmlls id vimap = vimap' ⇒
  vimap_rel fmlls vimap' ∧
  FST vimap' = FST vimap ∧
  FST (SND vimap') = MAX id (FST (SND vimap))
Proof
  PairCases_on`vimap`>>
  rw[fill_vimap_def]>>
  gvs[MAX_DEF]>>
  `∀k. wf_slot (any_el k fmlls Empty)` by metis_tac[fml_rel_wf_slot]>>
  gvs[vimap_rel_def]>>
  rw[]>>
  mp_tac (Q.SPECL [`id - vimap1`,`vimap1`,`vimap2`]
    (Q.INST [`m`|->`vimap0`,`fml`|->`fmlls`] fill_vimap_aux_vent_mem))>>
  simp[]>>
  strip_tac>>
  Cases_on`i < vimap1`
  >- metis_tac[]>>
  first_x_assum irule>>
  simp[]>>
  metis_tac[]
QED

(* The union of two lists *)
Theorem MEM_merge_desc:
  ∀xs ys. MEM i (merge_desc xs ys) ⇔ MEM i xs ∨ MEM i ys
Proof
  ho_match_mp_tac merge_desc_ind>>
  rw[merge_desc_def]>>
  metis_tac[]
QED

Theorem MEM_FLAT_merge_pairs:
  ∀ls. MEM i (FLAT (merge_pairs ls)) ⇔ MEM i (FLAT ls)
Proof
  ho_match_mp_tac merge_pairs_ind>>
  rw[merge_pairs_def,MEM_merge_desc]>>
  metis_tac[]
QED

Theorem MEM_merge_all:
  ∀ls. MEM i (merge_all ls) ⇔ MEM i (FLAT ls)
Proof
  ho_match_mp_tac merge_all_ind>>
  rw[merge_all_def]>>
  gvs[MEM_FLAT_merge_pairs]
QED

Theorem MEM_FLAT_get_inds_rhs_list:
  MEM i (FLAT (get_inds_rhs_list rhs pinds ninds acc)) ⇔
  MEM i (FLAT acc) ∨
  (rhs ≠ INL T ∧ MEM i pinds) ∨ (rhs ≠ INL F ∧ MEM i ninds)
Proof
  rw[get_inds_rhs_list_def]>>
  every_case_tac>>gvs[NULL_EQ]>>
  metis_tac[MEM]
QED

(* Cleaning keeps exactly the live indices *)
Theorem do_reindex_rhs_MEM:
  do_reindex_rhs fml rhs p n = (p',n') ⇒
  (∀j. MEM j p' ⇒ MEM j p) ∧ (∀j. MEM j n' ⇒ MEM j n) ∧
  (∀j. any_el j fml Empty ≠ Empty ∧ MEM j p ⇒ MEM j p') ∧
  (∀j. any_el j fml Empty ≠ Empty ∧ MEM j n ⇒ MEM j n')
Proof
  rw[do_reindex_rhs_def]>>
  every_case_tac>>gvs[reindex_characterize,MEM_FILTER]
QED

Theorem rebuild_slot_lookup:
  ∀k t.
  (lookup x (rebuild_slot t i cs vs k) = NONE ⇔ lookup x t = NONE) ∧
  ∀p n. lookup x t = SOME (p,n) ⇒
  ∃p' n'. lookup x (rebuild_slot t i cs vs k) = SOME (p',n') ∧
    (∀j. MEM j p' ⇔ MEM j p ∨
      j = i ∧ ∃l. l < k ∧ sub vs l = x ∧ 0 ≤ sub cs l) ∧
    (∀j. MEM j n' ⇔ MEM j n ∨
      j = i ∧ ∃l. l < k ∧ sub vs l = x ∧ sub cs l < 0)
Proof
  Induct
  >- (ONCE_REWRITE_TAC[rebuild_slot_def]>>simp[])>>
  ONCE_REWRITE_TAC[rebuild_slot_def]>>
  simp[]>>
  gen_tac>>
  Cases_on`lookup (sub vs k) t`>>simp[]
  >- (
    rpt strip_tac>>
    first_x_assum (qspec_then`t` strip_assume_tac)>>
    first_x_assum drule>>strip_tac>>
    qexistsl_tac[`p'`,`n'`]>>simp[]>>
    `x ≠ sub vs k` by (CCONTR_TAC>>gvs[])>>
    `∀l. l < SUC k ∧ sub vs l = x ⇔ l < k ∧ sub vs l = x` by (
      rw[EQ_IMP_THM]>>
      Cases_on`l = k`>>gvs[])>>
    metis_tac[])>>
  rename1`lookup (sub vs k) t = SOME pn`>>
  PairCases_on`pn`>>simp[]>>
  qmatch_goalsub_abbrev_tac`rebuild_slot t1 i cs vs k`>>
  first_x_assum (qspec_then`t1` strip_assume_tac)>>
  conj_tac
  >- (
    simp[Abbr`t1`,lookup_insert]>>
    Cases_on`x = sub vs k`>>gvs[])>>
  rpt strip_tac>>
  `∀l. l < SUC k ⇔ l < k ∨ l = k` by simp[]>>
  Cases_on`x = sub vs k`
  >- (
    gvs[]>>
    qpat_x_assum`∀p n. lookup _ t1 = SOME (p,n) ⇒ _` (qspecl_then
        [`if 0 ≤ sub cs k then i::p else p`,
         `if 0 ≤ sub cs k then n else i::n`] mp_tac)>>
    impl_tac>- (Cases_on`0 ≤ sub cs k`>>gvs[Abbr`t1`,lookup_insert])>>
    disch_then (qx_choosel_then [`pp`,`nn`] strip_assume_tac)>>
    qexistsl_tac[`pp`,`nn`]>>
    simp[arithmeticTheory.LT,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,EXISTS_OR_THM]>>
    Cases_on`0 ≤ sub cs k`
    >- (
      `¬(sub cs k < 0)` by intLib.ARITH_TAC>>
      gvs[]>>metis_tac[])>>
    `sub cs k < 0` by intLib.ARITH_TAC>>
    gvs[]>>metis_tac[])>>
  qpat_x_assum`∀p n. lookup _ t1 = SOME (p,n) ⇒ _` (qspecl_then [`p`,`n`] mp_tac)>>
  impl_tac>- simp[Abbr`t1`,lookup_insert]>>
  disch_then (qx_choosel_then [`pp`,`nn`] strip_assume_tac)>>
  qexistsl_tac[`pp`,`nn`]>>
  simp[arithmeticTheory.LT,LEFT_AND_OVER_OR,RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

(* One step of the rebuild walk, on the slot s at index i *)
Theorem rebuild_slot_dec_lookup:
  wf_slot s ⇒
  ∀x t i.
  (lookup x (case s of
      Empty => t
    | Stored cs vs d mc sm b => rebuild_slot t i cs vs (length vs)) = NONE ⇔
   lookup x t = NONE) ∧
  ∀p n. lookup x t = SOME (p,n) ⇒
  ∃p' n'.
    lookup x (case s of
      Empty => t
    | Stored cs vs d mc sm b => rebuild_slot t i cs vs (length vs)) =
      SOME (p',n') ∧
    (∀j. MEM j p' ⇔ MEM j p ∨ j = i ∧
      ∃c. MEM (c,x) (FST (dec s)) ∧ 0 ≤ c) ∧
    (∀j. MEM j n' ⇔ MEM j n ∨ j = i ∧
      ∃c. MEM (c,x) (FST (dec s)) ∧ c < 0)
Proof
  Cases_on`s`>>rw[wf_slot_def]>>
  simp[EXISTS_MEM_dec_Stored]>>
  rename1`rebuild_slot t i cs vs`>>
  mp_tac (Q.SPECL [`length (vs:num vector)`,`t`] rebuild_slot_lookup)>>
  simp[]
QED

Theorem rebuild_aux_lookup:
  ∀d i t.
  d = vw - i ∧
  (∀k. wf_slot (any_el k fml Empty)) ⇒
  (lookup x (rebuild_aux fml t i vw) = NONE ⇔ lookup x t = NONE) ∧
  ∀p n. lookup x t = SOME (p,n) ⇒
  ∃p' n'. lookup x (rebuild_aux fml t i vw) = SOME (p',n') ∧
    (∀j. MEM j p' ⇔ MEM j p ∨ i ≤ j ∧ j < vw ∧
      ∃c. MEM (c,x) (FST (dec (any_el j fml Empty))) ∧ 0 ≤ c) ∧
    (∀j. MEM j n' ⇔ MEM j n ∨ i ≤ j ∧ j < vw ∧
      ∃c. MEM (c,x) (FST (dec (any_el j fml Empty))) ∧ c < 0)
Proof
  completeInduct_on`d`>>
  rpt gen_tac>>strip_tac>>
  ONCE_REWRITE_TAC[rebuild_aux_def]>>
  IF_CASES_TAC
  >- (
    simp[]>>
    rpt strip_tac>>
    `¬(i ≤ j ∧ j < vw)` by simp[]>>
    metis_tac[])>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`rebuild_aux fml t1 (i + 1) vw`>>
  qpat_x_assum`∀m. m < d ⇒ _` (qspec_then`vw - (i + 1)` mp_tac)>>
  simp[]>>
  disch_then (qspecl_then [`i + 1`,`t1`] mp_tac)>>
  simp[]>>strip_tac>>
  `wf_slot (any_el i fml Empty)` by simp[]>>
  drule_then (qspecl_then [`x`,`t`,`i`] strip_assume_tac)
    rebuild_slot_dec_lookup>>
  gvs[Abbr`t1`]>>
  rpt strip_tac>>
  qpat_x_assum`∀p n. lookup x t = SOME (p,n) ⇒ _` drule>>
  disch_then (qx_choosel_then [`p1`,`n1`] strip_assume_tac)>>
  qpat_x_assum`∀p n. _ = SOME (p,n) ⇒ ∃p' n'. lookup x (rebuild_aux _ _ _ _) = _ ∧ _`
    drule>>
  disch_then (qx_choosel_then [`p2`,`n2`] strip_assume_tac)>>
  qexistsl_tac[`p2`,`n2`]>>
  simp[]>>
  rw[]>>eq_tac>>rw[]>>gvs[]>>
  metis_tac[DECIDE``∀i j:num. i ≤ j ⇔ j = i ∨ i + 1 ≤ j``]
QED


Theorem get_inds_fold_thm:
  ∀fml ls acc ents t acc' ents' t'.
  get_inds_fold fml ls acc ents t = (acc',ents',t') ⇒
  (∀j. MEM j (FLAT acc) ⇒ MEM j (FLAT acc')) ∧
  (∀x p0 n0. any_el x ents Vnone = Vinput p0 n0 ⇒
    any_el x ents' Vnone = Vinput p0 n0) ∧
  (∀x pos j.
    any_el j fml Empty ≠ Empty ∧ vent_mem m (any_el x ents Vnone) pos j ⇒
    vent_mem m (any_el x ents' Vnone) pos j) ∧
  (∀x. lookup x t ≠ NONE ⇒ lookup x t' ≠ NONE) ∧
  (∀x. lookup x t' ≠ NONE ⇒ lookup x t ≠ NONE ∨ ∃rhs. MEM (x,rhs) ls) ∧
  (∀x p n. lookup x t' = SOME (p,n) ⇒
    lookup x t = SOME (p,n) ∨
    ∃p0 n0. any_el x ents Vnone = Vinput p0 n0 ∧
      ∀pos j. any_el j fml Empty ≠ Empty ∧
        MEM j (if pos then p0 else n0) ⇒ MEM j (if pos then p else n)) ∧
  (∀x rhs. MEM (x,rhs) ls ⇒
    (∃p0 n0. any_el x ents Vnone = Vinput p0 n0) ∧ lookup x t' ≠ NONE ∨
    (∀p0 n0. any_el x ents Vnone ≠ Vinput p0 n0) ∧
    ∀pos j. any_el j fml Empty ≠ Empty ∧
      vent_mem m (any_el x ents Vnone) pos j ∧ rhs ≠ INL pos ⇒
      MEM j (FLAT acc'))
Proof
  ho_match_mp_tac get_inds_fold_ind>>
  rpt conj_tac
  >- simp[get_inds_fold_def]>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  simp[Once get_inds_fold_def]>>
  reverse (Cases_on`any_el n ents Vnone`)>>gvs[]
  >- (
    pairarg_tac>>gvs[]>>
    strip_tac>>
    qpat_x_assum`∀acc' ents' t'. _` drule>>strip_tac>>
    drule do_reindex_rhs_MEM>>strip_tac>>
    rpt conj_tac
    >- (
      gen_tac>>strip_tac>>
      qpat_x_assum`∀x. lookup x (insert _ _ _) ≠ NONE ⇒ _` irule>>
      rw[lookup_insert])
    >- (
      rpt strip_tac>>
      Cases_on`x = n`
      >- (qexists_tac`rhs`>>simp[])>>
      qpat_x_assum`∀x. lookup x t' ≠ NONE ⇒ _` drule>>
      impl_tac>- simp[lookup_insert]>>
      disch_then (qx_choose_then`r` assume_tac)>>
      qexists_tac`r`>>simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x p n'. lookup x t' = SOME (p,n') ⇒ _` drule>>
      strip_tac
      >- (
        Cases_on`x = n`>>gvs[lookup_insert]>>
        disj2_tac>>
        Cases>>rw[])>>
      disj2_tac>>
      qpat_x_assum`any_el x ents Vnone = Vinput _ _` (irule_at Any)>>
      simp[])>>
    rpt gen_tac>>strip_tac
    >- (
      gvs[]>>
      qpat_x_assum`∀x. lookup x (insert _ _ _) ≠ NONE ⇒ _` irule>>
      simp[lookup_insert])>>
    qpat_x_assum`∀x rhs. MEM (x,rhs) ls ⇒ _` drule>>
    disch_then ACCEPT_TAC)
  >>~- ([`do_reindex_rhs _ _ _ _`],
    pairarg_tac>>gvs[]>>
    strip_tac>>
    qpat_x_assum`∀acc' ents' t'. _` drule>>strip_tac>>
    drule do_reindex_rhs_MEM>>strip_tac>>
    qmatch_asmsub_abbrev_tac`get_inds_fold fml ls acc1 ents1 t`>>
    `∀x pos j. any_el j fml Empty ≠ Empty ∧
      vent_mem m (any_el x ents Vnone) pos j ⇒
      vent_mem m (any_el x ents1 Vnone) pos j` by (
      rw[Abbr`ents1`,any_el_update_resize]>>
      gvs[vent_mem_def]>>
      Cases_on`pos`>>gvs[])>>
    `∀x p0 n0. any_el x ents1 Vnone = Vinput p0 n0 ⇔
      any_el x ents Vnone = Vinput p0 n0` by
      rw[Abbr`ents1`,any_el_update_resize]>>
    `∀j. MEM j (FLAT acc) ⇒ MEM j (FLAT acc1)` by
      simp[Abbr`acc1`,MEM_FLAT_get_inds_rhs_list]>>
    rpt conj_tac
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀j. MEM j (FLAT acc1) ⇒ _` irule>>
      qpat_x_assum`∀j. MEM j (FLAT acc) ⇒ _` irule>>
      simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x p0 n0. any_el x ents1 Vnone = Vinput p0 n0 ⇒ _` irule>>
      simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x pos j. _ ⇒ vent_mem m (any_el x ents' Vnone) pos j` irule>>
      simp[]>>
      qpat_x_assum`∀x pos j. _ ⇒ vent_mem m (any_el x ents1 Vnone) pos j` irule>>
      simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x. lookup x t' ≠ NONE ⇒ _` drule_all>>
      disch_then (qx_choose_then`r` assume_tac)>>
      qexists_tac`r`>>simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x p n'. lookup x t' = SOME (p,n') ⇒ _` drule>>
      strip_tac>>gvs[])>>
    rpt gen_tac>>strip_tac
    >- (
      gvs[]>>
      rw[]>>
      qpat_x_assum`∀j. MEM j (FLAT acc1) ⇒ _` irule>>
      simp[Abbr`acc1`,MEM_FLAT_get_inds_rhs_list]>>
      gvs[vent_mem_def]>>
      Cases_on`pos`>>gvs[])>>
    qpat_x_assum`∀x rhs. MEM (x,rhs) ls ⇒ _` drule>>
    strip_tac
    >- (
      disj1_tac>>
      qpat_x_assum`any_el x ents1 Vnone = _` mp_tac>>
      simp[Abbr`ents1`,any_el_update_resize]>>
      rw[])>>
    disj2_tac>>
    gvs[]>>
    rpt strip_tac>>
    first_x_assum irule>>
    simp[]>>
    qexists_tac`pos`>>simp[]>>
    qpat_x_assum`∀x pos j. _ ⇒ vent_mem m (any_el x ents1 Vnone) pos j` irule>>
    simp[])
  >- (
    strip_tac>>
    qpat_x_assum`∀acc' ents' t'. _` drule>>strip_tac>>
    qmatch_asmsub_abbrev_tac`get_inds_fold fml ls acc ents1 t`>>
    `∀x pos j. vent_mem m (any_el x ents Vnone) pos j ⇒
      vent_mem m (any_el x ents1 Vnone) pos j` by (
      rw[Abbr`ents1`,any_el_update_resize]>>
      gvs[vent_mem_def])>>
    `∀x p0 n0. any_el x ents1 Vnone = Vinput p0 n0 ⇔
      any_el x ents Vnone = Vinput p0 n0` by
      rw[Abbr`ents1`,any_el_update_resize]>>
    rpt conj_tac
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x p0 n0. any_el x ents1 Vnone = Vinput p0 n0 ⇒ _` irule>>
      simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x pos j. _ ⇒ vent_mem m (any_el x ents' Vnone) pos j` irule>>
      simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x. lookup x t' ≠ NONE ⇒ _` drule_all>>
      disch_then (qx_choose_then`r` assume_tac)>>
      qexists_tac`r`>>simp[])
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x p n'. lookup x t' = SOME (p,n') ⇒ _` drule>>
      strip_tac>>gvs[])>>
    rpt gen_tac>>strip_tac
    >- gvs[vent_mem_def]>>
    qpat_x_assum`∀x rhs. MEM (x,rhs) ls ⇒ _` drule>>
    strip_tac
    >- (
      disj1_tac>>
      qpat_x_assum`any_el x ents1 Vnone = _` mp_tac>>
      simp[Abbr`ents1`,any_el_update_resize]>>
      rw[])>>
    disj2_tac>>
    gvs[]>>
    rpt strip_tac>>
    first_x_assum irule>>
    simp[]>>
    qexists_tac`pos`>>simp[])
QED

Theorem get_inds_rebuilt_thm:
  ∀ls t acc ents acc' ents'.
  get_inds_rebuilt ls t acc ents = (acc',ents') ⇒
  (∀j. MEM j (FLAT acc) ⇒ MEM j (FLAT acc')) ∧
  (∀x. (lookup x t = NONE ∨ ∀rhs. ¬MEM (x,rhs) ls) ⇒
    any_el x ents' Vnone = any_el x ents Vnone) ∧
  (∀x rhs p n. MEM (x,rhs) ls ∧ lookup x t = SOME (p,n) ⇒
    any_el x ents' Vnone = Vtrack p n ∧
    ∀pos j. MEM j (if pos then p else n) ∧ rhs ≠ INL pos ⇒
      MEM j (FLAT acc'))
Proof
  ho_match_mp_tac get_inds_rebuilt_ind>>
  rpt conj_tac
  >- simp[get_inds_rebuilt_def]>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  simp[Once get_inds_rebuilt_def]>>
  Cases_on`lookup n t`>>gvs[]
  >- (
    strip_tac>>
    first_x_assum drule>>strip_tac>>
    conj_tac
    >- (
      rpt strip_tac>>
      qpat_x_assum`∀x. lookup x t = NONE ∨ _ ⇒ _` irule>>
      metis_tac[])>>
    rpt gen_tac>>strip_tac
    >- gvs[]>>
    qpat_x_assum`∀x rhs p n. MEM (x,rhs) ls ∧ _ ⇒ _` drule_all>>
    simp[])>>
  rename1`lookup n t = SOME pn`>>PairCases_on`pn`>>
  gvs[]>>
  strip_tac>>
  first_x_assum drule>>strip_tac>>
  rpt conj_tac
  >- (
    rw[]>>
    first_x_assum irule>>
    simp[MEM_FLAT_get_inds_rhs_list])
  >- (
    gen_tac>>strip_tac
    >- (
      `x ≠ n` by (CCONTR_TAC>>gvs[])>>
      qpat_x_assum`∀x. lookup x t = NONE ∨ _ ⇒ _` (qspec_then`x` mp_tac)>>
      simp[any_el_update_resize])>>
    `x ≠ n` by (
      CCONTR_TAC>>gvs[]>>
      first_x_assum (qspec_then`rhs` mp_tac)>>simp[])>>
    qpat_x_assum`∀x. lookup x t = NONE ∨ _ ⇒ _` (qspec_then`x` mp_tac)>>
    simp[any_el_update_resize]>>
    metis_tac[])>>
  rpt gen_tac>>
  Cases_on`MEM (x,rhs') ls`
  >- (
    strip_tac>>
    qpat_x_assum`∀x rhs p n. MEM (x,rhs) ls ∧ _ ⇒ _` drule_all>>
    simp[])>>
  strip_tac>>gvs[]>>
  conj_tac
  >- (
    Cases_on`∃r. MEM (n,r) ls`
    >- (
      gvs[]>>
      qpat_x_assum`∀x rhs p n. MEM (x,rhs) ls ∧ _ ⇒ _` drule_all>>
      simp[])>>
    qpat_x_assum`∀x. lookup x t = NONE ∨ _ ⇒ _` (qspec_then`n` mp_tac)>>
    gvs[any_el_update_resize])>>
  rw[]>>
  qpat_x_assum`∀j. MEM j (FLAT (get_inds_rhs_list _ _ _ _)) ⇒ _` irule>>
  simp[MEM_FLAT_get_inds_rhs_list]>>
  Cases_on`pos`>>gvs[]
QED

(* The read is complete for the constraints below the watermark *)
Theorem MEM_get_set_indices_mk_subst:
  fml_rel fml fmlls ∧
  vimap_rel fmlls (m,vw,ents) ∧
  i < vw ∧
  any_el i fmlls Empty ≠ Empty ∧
  IS_SOME (subst_opt (subst_fun (mk_subst r s)) (dec (any_el i fmlls Empty))) ∧
  get_set_indices fmlls s (m,vw,ents) = (rinds, vimap')
  ⇒
  MEM i rinds
Proof
  rw[]>>
  `∀k. wf_slot (any_el k fmlls Empty)` by metis_tac[fml_rel_wf_slot]>>
  drule IS_SOME_subst_opt>>strip_tac>>
  gvs[subst_fun_mk_subst,IS_SOME_EXISTS]>>
  rename1`ALOOKUP s x = SOME rhs`>>
  drule ALOOKUP_MEM>>strip_tac>>
  `vent_mem m (any_el x ents Vnone) (0 ≤ coeff) i` by
    metis_tac[vimap_rel_def]>>
  gvs[get_set_indices_def]>>
  rpt (pairarg_tac>>gvs[])>>
  simp[MEM_merge_all]>>
  drule get_inds_fold_thm>>
  disch_then (qspec_then`m` strip_assume_tac)>>
  `(t = LN ⇒ acc' = acc) ∧
   (t ≠ LN ⇒
    get_inds_rebuilt s (rebuild_aux fmlls t (m + 1) vw) acc ents' =
      (acc',ents''))` by (Cases_on`t`>>gvs[])>>
  qpat_x_assum`∀x rhs. MEM (x,rhs) s ⇒ _` drule>>
  strip_tac
  >- (
    `t ≠ LN` by (CCONTR_TAC>>gvs[lookup_def])>>
    gvs[]>>
    Cases_on`lookup x t`>>gvs[]>>
    rename1`lookup x t = SOME pn`>>PairCases_on`pn`>>
    drule get_inds_rebuilt_thm>>strip_tac>>
    mp_tac (Q.SPECL [`vw - (m + 1)`,`m + 1`,`t`]
      (Q.INST [`fml`|->`fmlls`] rebuild_aux_lookup))>>
    simp[]>>strip_tac>>
    qpat_x_assum`∀x rhs p n. MEM (x,rhs) s ∧ _ ⇒ _`
      (qspecl_then [`x`,`rhs`,`p'`,`n'`] mp_tac)>>
    simp[]>>strip_tac>>
    first_x_assum (qspec_then`0 ≤ coeff` irule)>>
    qexists_tac`coeff`>>simp[]>>
    qpat_x_assum`∀x'' p n. lookup x'' t = SOME (p,n) ⇒ _` drule>>
    strip_tac>>
    gvs[vent_mem_def]>>
    Cases_on`m < i`
    >- (
      Cases_on`0 ≤ coeff`>>gvs[]>>
      disj2_tac>>
      qexists_tac`coeff`>>
      gvs[integerTheory.INT_NOT_LE])>>
    gvs[]>>
    first_x_assum (qspecl_then [`0 ≤ coeff`,`i`] mp_tac)>>
    Cases_on`0 ≤ coeff`>>gvs[])>>
  `MEM i (FLAT acc)` by metis_tac[]>>
  Cases_on`t = LN`>>gvs[]>>
  drule get_inds_rebuilt_thm>>
  metis_tac[]
QED

Theorem MEM_get_set_indices_lookup_core_only:
  fml_rel fml fmlls ∧
  vimap_rel fmlls (m,vw,ents) ∧
  i < vw ∧
  lookup_core_only b fml i = SOME x ∧
  IS_SOME (subst_opt (subst_fun (mk_subst r s)) x) ∧
  get_set_indices fmlls s (m,vw,ents) = (rinds, vimap')
  ⇒
  MEM i rinds
Proof
  rw[]>>
  `∃b'. lookup i fml = SOME (x,b')` by
    gvs[lookup_core_only_def,AllCaseEqs()]>>
  `any_el i fmlls Empty = enc x b'` by (
    qpat_x_assum`fml_rel fml fmlls` mp_tac>>
    rw[fml_rel_def]>>
    simp[enc_opt_def])>>
  irule MEM_get_set_indices_mk_subst>>
  qexistsl_tac[`ents`,`fml`,`fmlls`,`m`,`r`,`s`,`vimap'`,`vw`]>>
  simp[dec_enc,enc_NOT_Empty]
QED

Theorem fml_rel_fml_rel_vimap_rel:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  fml_rel fml fmlls' ⇒
  vimap_rel fmlls' vimap
Proof
  PairCases_on`vimap`>>
  rw[vimap_rel_def]>>
  `any_el i fmlls' Empty = any_el i fmlls Empty` by gvs[fml_rel_def]>>
  first_x_assum irule>>
  gvs[]
QED

Theorem vimap_rel_get_set_indices:
  fml_rel fml fmlls ∧
  get_set_indices fmlls s vimap = (rinds,vimap') ∧
  vimap_rel fmlls vimap ⇒
  vimap_rel fmlls vimap' ∧
  FST vimap' = FST vimap ∧ FST (SND vimap') = FST (SND vimap)
Proof
  PairCases_on`vimap`>>
  strip_tac>>
  `∀k. wf_slot (any_el k fmlls Empty)` by metis_tac[fml_rel_wf_slot]>>
  gvs[get_set_indices_def]>>
  rpt (pairarg_tac>>gvs[])>>
  drule get_inds_fold_thm>>
  disch_then (qspec_then`vimap0` strip_assume_tac)>>
  gvs[vimap_rel_def]>>
  rpt strip_tac>>
  `any_el i fmlls Empty ≠ Empty` by metis_tac[MEM_dec_NOT_Empty]>>
  `vent_mem vimap0 (any_el x vimap2 Vnone) (0 ≤ coeff) i` by
    (first_x_assum irule>>simp[])>>
  `vent_mem vimap0 (any_el x ents Vnone) (0 ≤ coeff) i` by (
    qpat_x_assum`∀x pos j. _ ⇒ vent_mem _ (any_el x ents Vnone) pos j` irule>>
    simp[])>>
  `(t = LN ⇒ ents' = ents) ∧
   (t ≠ LN ⇒
    get_inds_rebuilt s (rebuild_aux fmlls t (vimap0 + 1) vimap1) acc ents =
      (acc',ents'))` by (Cases_on`t`>>gvs[])>>
  Cases_on`t = LN`>>gvs[]>>
  drule get_inds_rebuilt_thm>>strip_tac>>
  Cases_on`lookup x (rebuild_aux fmlls t (vimap0 + 1) vimap1) = NONE ∨
    ∀rhs. ¬MEM (x,rhs) s`
  >- (
    `any_el x ents' Vnone = any_el x ents Vnone` by (
      qpat_x_assum`∀x. _ ∨ _ ⇒ any_el x ents' Vnone = _` irule>>
      simp[])>>
    simp[]>>
    qpat_x_assum`∀x pos j. _ ⇒ vent_mem _ (any_el x ents Vnone) pos j` irule>>
    simp[]>>
    qpat_x_assum`∀i coeff x. _ ⇒ vent_mem _ (any_el x vimap2 Vnone) _ _` irule>>
    simp[])>>
  gvs[]>>
  Cases_on`lookup x (rebuild_aux fmlls t (vimap0 + 1) vimap1)`>>gvs[]>>
  rename1`_ = SOME pq`>>PairCases_on`pq`>>
  qpat_x_assum`∀x rhs p n. MEM (x,rhs) s ∧ _ ⇒ _` drule_all>>
  strip_tac>>
  simp[vent_mem_def]>>
  mp_tac (Q.SPECL [`vimap1 - (vimap0 + 1)`,`vimap0 + 1`,`t`]
    (Q.INST [`fml`|->`fmlls`,`vw`|->`vimap1`] rebuild_aux_lookup))>>
  simp[]>>strip_tac>>
  Cases_on`lookup x t`>>gvs[]>>
  rename1`lookup x t = SOME ab`>>PairCases_on`ab`>>
  gvs[]>>
  qpat_x_assum`∀x p n. lookup x t = SOME (p,n) ⇒ _` drule>>
  strip_tac>>
  `vent_mem vimap0 (Vinput p0 n0) (0 ≤ coeff) i` by (
    qpat_x_assum`any_el x vimap2 Vnone = _` (SUBST1_TAC o SYM)>>
    qpat_x_assum`∀i coeff x. _ ⇒ vent_mem _ (any_el x vimap2 Vnone) _ _` irule>>
    simp[])>>
  gvs[vent_mem_def]
  >- (
    Cases_on`0 ≤ coeff`>>gvs[]>>
    disj2_tac>>
    qexists_tac`coeff`>>gvs[integerTheory.INT_NOT_LE])>>
  qpat_x_assum`∀pos j. _ ∧ MEM j (if pos then p0 else n0) ⇒ _`
    (qspecl_then [`0 ≤ coeff`,`i`] mp_tac)>>
  Cases_on`0 ≤ coeff`>>gvs[]
QED

(* An empty-listed entry: no constraint below the watermark has it *)
Theorem vimap_rel_vent_fresh:
  vimap_rel fmlls (m,vw,ents) ∧
  vent_fresh (any_el x ents Vnone) ∧
  i < vw ∧
  MEM (coeff,x) (FST (dec (any_el i fmlls Empty))) ⇒
  F
Proof
  strip_tac>>
  gvs[vimap_rel_def]>>
  first_x_assum drule_all>>
  Cases_on`any_el x ents Vnone`>>
  gvs[vent_fresh_def,vent_mem_def,NULL_EQ]
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

(* po is the precomputation of the loaded order ord, whose maps are built
  by mk_ordsub. OPTION_ALL ord_maps_ok ord duplicates part of the
  invariant OPTION_ALL good_aspo_subst pc.ord that npbc_check proves for
  check_cstep (check_cstep_correct); it is carried again here because
  that theorem's other hypotheses are not available at this level *)
Definition po_rel_def:
  po_rel ord po ⇔ po = mk_ord_pre ord ∧ OPTION_ALL ord_maps_ok ord
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
  fast_obj_constraint (mk_subst r sr) sr l vomap =
  obj_constraint (subst_fun (mk_subst r sr)) l
Proof
  rw[fast_obj_constraint_def,obj_constraint_rewrite,
     mlstringTheory.strsub_unsafe_eq_strsub]>>
  every_case_tac>>
  Cases_on`l`>>
  fs[npbcTheory.obj_constraint_def,subst_fun_mk_subst]>>
  rpt (pairarg_tac>>fs[])>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[add_lists_map_negate_coeff]>>rw[]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[subst_lhs_id]>>
  fs[vomap_rel_def]>>
  simp[EVERY_MAP,LAMBDA_PROD,subst_fun_mk_subst]>>
  gvs[EVERY_MEM]>>
  rw[]>>pairarg_tac>>
  fs[EXTENSION,MEM_MAP,domain_lookup,ALOOKUP_NONE]>>
  qx_gen_tac`pr`>> rpt strip_tac>>
  qpat_x_assum`∀x. _ ⇔ _` (qspec_then`FST pr` mp_tac)>>
  qpat_x_assum`∀e. MEM e sr ⇒ _` (drule_then mp_tac)>>
  Cases_on`pr`>>gvs[]>>
  rw[]>>gvs[EXISTS_PROD]>>
  metis_tac[]
QED

Theorem vomap_rel_fast_red_subgoals:
  vomap_rel obj vomap ∧ po = mk_ord_pre ord ∧
  fast_red_subgoals ord po (mk_subst r sr) sr (enc def b) obj vomap hs =
    (rsubs,rscopes) ⇒
  red_subgoals ord (subst_fun (mk_subst r sr)) def obj hs =
    (rsubs, MAP (MAP sc_hyp_dec) rscopes)
Proof
  strip_tac>>
  mp_tac (Q.INST [‘po’ |-> ‘mk_ord_pre ord’,
    ‘w’ |-> ‘subst_fun (mk_subst r sr)’] dom_subst_list_thm)>>
  impl_tac
  >- rw[subst_fun_mk_subst,ALOOKUP_NONE]>>
  qpat_x_assum`fast_red_subgoals _ _ _ _ _ _ _ _ = _` mp_tac>>
  rw[fast_red_subgoals_def,red_subgoals_def,subst_slot_enc]>>
  Cases_on`dom_subst_list hs (subst_fun (mk_subst r sr)) sr ord (mk_ord_pre ord)`>>
  Cases_on`dom_subst hs (subst_fun (mk_subst r sr)) ord`>>
  rw[]>>
  every_case_tac>>gvs[]>>
  metis_tac[vomap_rel_fast_obj_constraint]
QED

Theorem fast_red_subgoals_scopes_ok:
  po = mk_ord_pre ord ∧
  fast_red_subgoals ord po (mk_subst r sr) sr def obj vomap hs =
    (rsubs,rscopes) ⇒
  EVERY (EVERY sc_hyp_ok) rscopes
Proof
  strip_tac>>
  mp_tac (Q.INST [‘po’ |-> ‘mk_ord_pre ord’,
    ‘w’ |-> ‘subst_fun (mk_subst r sr)’] dom_subst_list_thm)>>
  simp[subst_fun_mk_subst,ALOOKUP_NONE]>>
  gvs[fast_red_subgoals_def]>>
  rpt (pairarg_tac>>gvs[])
QED

Theorem vimap_rel_check_fresh_aux_fml_vimap:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  (∀n. n ≥ FST (SND vimap) ⇒ any_el n fmlls Empty = Empty) ∧
  check_fresh_aux_fml_vimap as vimap ⇒
  check_fresh_aux_fml as fml
Proof
  PairCases_on`vimap`>>
  rw[check_fresh_aux_fml_vimap_def,check_fresh_aux_fml_def]>>
  pop_assum mp_tac>>
  match_mp_tac EVERY_MONOTONIC>>
  rw[]>>
  CCONTR_TAC>>
  gvs[range_def,MEM_MAP]>>
  rename1`MEM y _`>>
  PairCases_on`c`>> PairCases_on`y`>>
  `any_el n fmlls Empty = enc (c0,c1) c2` by gvs[fml_rel_def,enc_opt_def]>>
  `n < vimap1` by (
    CCONTR_TAC>>
    first_x_assum (qspec_then`n` mp_tac)>>
    simp[enc_NOT_Empty])>>
  drule vimap_rel_vent_fresh>>
  disch_then (qspecl_then [`y1`,`n`,`y0`] mp_tac)>>
  gvs[dec_enc]
QED

Theorem vomap_rel_check_fresh_aux_obj_vomap:
  vomap_rel obj vomap ∧
  check_fresh_aux_obj_vomap as vomap ⇒
  check_fresh_aux_obj as obj
Proof
  rw[check_fresh_aux_obj_vomap_def,check_fresh_aux_obj_def,
     mlstringTheory.strsub_unsafe_eq_strsub]>>
  TOP_CASE_TAC>>simp[]>>
  last_x_assum mp_tac>>
  match_mp_tac EVERY_MONOTONIC>>
  gvs[vomap_rel_def]>>rw[]>>
  CCONTR_TAC>>
  gvs[]
QED

(* The index is filled up to id whenever the freshness check reads it *)
Theorem vimap_rel_vomap_rel_check_fresh_aspo_list:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  (reads_vimap s T ord ⇒ FST (SND vimap) = id) ∧
  vomap_rel obj vomap ∧
  check_fresh_aspo_list (enc c b) s ord vimap vomap ⇒
  check_fresh_aspo fml c obj s ord
Proof
  strip_tac>>
  Cases_on`reads_vimap s T ord`
  >- (
    gvs[check_fresh_aspo_list_def,check_fresh_aspo_def,
      check_fresh_aux_constr_slot_enc,AllCasePreds()]>>
    metis_tac[vomap_rel_check_fresh_aux_obj_vomap,
      vimap_rel_check_fresh_aux_fml_vimap])>>
  gvs[reads_vimap_def,check_fresh_aspo_list_def,check_fresh_aspo_def,
    AllCasePreds(),check_fresh_aux_constr_slot_enc,NULL_EQ,
    check_fresh_aux_fml_def,check_fresh_aux_obj_def]>>
  Cases_on`obj`>>simp[]
QED

(* The fill and the read at the start of a step *)
Theorem fill_get_set_indices:
  fml_rel fml fmlls ∧ vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  get_set_indices fmlls s
    (if reads_vimap s fresh ord then fill_vimap fmlls id vimap else vimap) =
    (rinds,vimap') ⇒
  vimap_rel fmlls vimap' ∧ FST (SND vimap') ≤ id ∧
  (reads_vimap s fresh ord ⇒ FST (SND vimap') = id) ∧
  ∀i x b r.
    lookup_core_only b fml i = SOME x ∧
    IS_SOME (subst_opt (subst_fun (mk_subst r s)) x) ⇒
    MEM i rinds
Proof
  strip_tac>>
  Cases_on`reads_vimap s fresh ord`>>gvs[]
  >- (
    `∃m vw ents. fill_vimap fmlls id vimap = (m,vw,ents)` by metis_tac[PAIR]>>
    drule_all vimap_rel_fill_vimap>>
    strip_tac>>gvs[MAX_DEF]>>
    drule_all vimap_rel_get_set_indices>>
    strip_tac>>simp[]>>
    rpt strip_tac>>
    irule MEM_get_set_indices_lookup_core_only>>
    qexistsl_tac[`b`,`ents`,`fml`,`fmlls`,`FST vimap`,`r`,`s`,`vimap'`,`id`,`x`]>>
    simp[]>>
    gvs[lookup_core_only_def,AllCaseEqs()]>>
    CCONTR_TAC>>
    qpat_x_assum`∀n. n ≥ id ⇒ _` (qspec_then`i` mp_tac)>>
    gvs[fml_rel_def,enc_opt_def,enc_NOT_Empty])>>
  drule_all vimap_rel_get_set_indices>>
  strip_tac>>simp[]>>
  gvs[reads_vimap_def,NULL_EQ]>>
  rpt strip_tac>>
  drule IS_SOME_subst_opt>>
  simp[subst_fun_mk_subst]
QED

(* The freshness check on the index filled at the start of a step *)
Theorem fill_check_fresh_aspo_list:
  fml_rel fml fmlls ∧ vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  vomap_rel obj vomap ∧
  check_fresh_aspo_list (enc c b) s ord
    (if reads_vimap s T ord then fill_vimap fmlls id vimap else vimap)
    vomap ⇒
  check_fresh_aspo fml c obj s ord
Proof
  strip_tac>>
  irule vimap_rel_vomap_rel_check_fresh_aspo_list>>
  qexistsl_tac[`b`,`fmlls`,`id`,
    `if reads_vimap s T ord then fill_vimap fmlls id vimap else vimap`,
    `vomap`]>>
  rw[]>>
  qspecl_then [`vimap`,`id`,`fmlls`,`fml`,`fill_vimap fmlls id vimap`] mp_tac
    (Q.GENL [`vimap`,`id`,`fmlls`,`fml`,`vimap'`] vimap_rel_fill_vimap)>>
  simp[MAX_DEF]
QED

Theorem fml_rel_check_red_list:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  vomap_rel obj vomap ∧ po = mk_ord_pre ord ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_red_list pres ord po obj b tcb fmlls inds id (enc c b0) (max_var (FST c)) s pfs
    idopt vimap vomap assg st ht =
    SOME (fmlls', inds', vimap', id', assg', st', ht') ⇒
    check_red pres ord obj b tcb fml id c s pfs idopt = SOME id' ∧
    fml_rel fml fmlls' ∧ rup_inv fmlls' assg' st' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧ FST (SND vimap') ≤ id' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
    id ≤ id'
Proof
  strip_tac>>
  fs[check_red_list_def,not_slot_enc,store_slot_enc,max_var_not]>>
  gvs[AllCaseEqs()]
  >- (
    rpt (pairarg_tac>>fs[])>>
    gvs[AllCaseEqs()]>>
    drule_at (Pos last) vomap_rel_fast_red_subgoals>>
    simp[]>>strip_tac>>
    drule_at (Pos last) fast_red_subgoals_scopes_ok>>
    simp[]>>strip_tac>>
    drule_all fill_get_set_indices>>
    strip_tac>>
    simp[check_red_def]>>
    qspecl_then [`[]`,`rinds`,`s`] SUBST_ALL_TAC subst_fun_mk_subst_rinds>> simp[]>>
    DEP_REWRITE_TAC [fml_rel_extract_scopes_list]>> simp[]>>
    drule_all scopes_ok_extract_scopes_list>> strip_tac>>
    drule_all rup_inv_opt_update>> strip_tac>>
    drule_all fml_rel_opt_update>> strip_tac>>
    gvs[opt_update_SOME]>>
    qpat_x_assum`check_scopes_list _ _ _ _ _ _ _ = _` assume_tac>>
    drule_at (Pos last) fml_rel_check_scopes_list>>
    disch_then (qspec_then`insert id (not c,b) fml` mp_tac)>>
    impl_tac>- (
      rw[]>>
      simp[any_el_update_resize])>>
    simp[]>>strip_tac>>
    gvs[insert_fml_def]>>
    drule check_scopes_list_id>>
    drule check_scopes_list_id_upper>>
    drule check_scopes_list_mindel>>
    simp[any_el_update_resize]>>
    ntac 3 strip_tac>>
    pairarg_tac>>gvs[AllCaseEqs()]>>
    qmatch_asmsub_abbrev_tac`UNCURRY _ DRC = SOME _`>>
    PairCases_on`DRC`>>
    gvs[markerTheory.Abbrev_def]>>
    `fml_rel fml (rollback fml' id id')` by (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      gvs[do_red_check_def,red_cond_check_def,AllCaseEqs(),insert_fml_def,
        check_hash_goals_slot_enc]
      >- (
        Cases_on`extract_scoped_pids_list pfs [] LN`>>
        rename1`extract_scoped_pids_list pfs [] LN = (pl,pr)`>>
        qspecl_then [`pfs`,`[]`,`LN`,`LN`] mp_tac
          extract_scoped_pids_list_thm>>
        simp[]>>strip_tac>>gvs[]>>
        CONJ_TAC >- (
          disch_tac>>
          gvs[]>>
          metis_tac[vimap_rel_vomap_rel_check_fresh_aspo_list])>>
        Cases_on`check_hash_goals c skipped pr rsubs`>>
        gvs[]>>
        drule_at (Pos (el 2)) split_goals_hash_imp_split_goals>>
        disch_then drule>>
        disch_then (qspec_then`l` mp_tac)>>
        impl_tac >- simp[]>>
        match_mp_tac split_goals_same_goals>>
        simp[EXTENSION,FORALL_PROD]>>
        rw[]>>eq_tac>>rw[]
        >- (
          fs[MEM_toAList,lookup_map_opt,AllCaseEqs(),lookup_mk_core_fml]>>
          irule MEM_subst_indexes>>
          first_assum (irule_at Any)>>
          simp[]>>
          metis_tac[IS_SOME_EXISTS])>>
        drule_at (Pos last) subst_indexes_MEM>>
        disch_then drule>>
        rw[]>>
        gvs[MEM_toAList,lookup_map_opt,lookup_mk_core_fml])>>
      match_mp_tac (GEN_ALL fml_rel_check_contradiction_fml)>>
      metis_tac[])>>
    CONJ_TAC >- fs[]>>
    CONJ_TAC >- (
      metis_tac[rup_inv_rollback])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[])>>
    CONJ_TAC >- (
      metis_tac[fml_rel_fml_rel_vimap_rel])>>
    simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    rw[])>>
  gvs[check_red_list_fast_def,AllCaseEqs(),red_fast_def,check_red_def,
    insert_fml_def,not_slot_enc,store_slot_enc,max_var_not]>>
  rpt (pairarg_tac>>gvs[])>>gvs[AllCaseEqs()]>>
  drule_all rup_inv_opt_update>> strip_tac>>
  drule_all fml_rel_opt_update>> strip_tac>>
  gvs[opt_update_SOME]>>
  gvs[extract_scopes_def,check_scopes_def,mk_scope_def,extract_clauses_def,check_subproofs_def,insert_fml_def,check_lstep_list_def]
  >- (
    CONJ_TAC >- metis_tac[fml_rel_check_contradiction_fml]>>
    CONJ_ASM1_TAC >- (
      match_mp_tac fml_rel_rollback>>
      simp[]>>
      rw[any_el_update_resize])>>
    CONJ_TAC >- (
      metis_tac[rup_inv_rollback])>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[any_el_update_resize])>>
    CONJ_TAC >- metis_tac[fml_rel_fml_rel_vimap_rel]>>
    simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,any_el_update_resize])>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` assume_tac>>
  drule_at (Pos last) (CONJUNCT2 fml_rel_check_lstep_list)>>
  disch_then (qspec_then`insert id (not c,b) fml` mp_tac)>>
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
    first_x_assum drule >> simp[])>>
  CONJ_TAC >- (
    metis_tac[rup_inv_rollback])>>
  CONJ_TAC >- (
    match_mp_tac ind_rel_rollback_2>>
    simp[])>>
  CONJ_TAC >- metis_tac[fml_rel_fml_rel_vimap_rel]>>
  simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,any_el_update_resize]>>
  rw[]
QED

Theorem store_ind_enc:
  mv = max_var (FST c) ⇒
  (store_ind fml (enc c b) mv id inds assg st =
    (fml',inds',id',assg',st') ⇔
  opt_update fml (SOME (c,b)) id assg st = (fml',id',assg',st') ∧
  inds' = sorted_insert id inds)
Proof
  rw[store_ind_def,opt_update_def,enc_mv_enc]>>
  pairarg_tac>>simp[]>>
  metis_tac[]
QED

Theorem opt_update_inds_opt_update:
  opt_update_inds fml c id inds assg st =
    (fml',inds',id',assg',st') ⇒
  opt_update fml c id assg st = (fml',id',assg',st')
Proof
  Cases_on`c`>>simp[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  simp[opt_update_inds_def,enc_mv_enc,store_ind_enc]
QED

Theorem ind_rel_check_lstep_list:
  ind_rel fmlls inds ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_lstep_list lstep b fmlls mindel id assg st =
    SOME (fmlls',x,y,z,w) ⇒
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
  opt_update_inds fml c id inds assg st =
    (fml',inds',id',assg',st') ⇒
  SORTED $>= inds'
Proof
  Cases_on`c`>>strip_tac>>gvs[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  gvs[opt_update_inds_def,enc_mv_enc,store_ind_enc]>>
  metis_tac[SORTED_sorted_insert]
QED

Theorem opt_update_inds_ind_rel:
  ind_rel fml inds ∧
  opt_update_inds fml c id inds assg st =
    (fml',inds',id',assg',st') ⇒
  ind_rel fml' inds'
Proof
  Cases_on`c`>>strip_tac>>gvs[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  gvs[opt_update_inds_def,enc_mv_enc,store_ind_enc,opt_update_SOME]>>
  simp[ind_rel_update_resize_sorted_insert]
QED

Theorem vimap_rel_check_lstep_list:
  vimap_rel fmlls vimap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_lstep_list lstep b fmlls mindel id assg st =
    SOME (fmlls',x,y,z,w) ⇒
  vimap_rel fmlls' vimap
Proof
  PairCases_on`vimap`>>
  rw[] \\ fs[vimap_rel_def] \\ rw[] >>
  imp_res_tac MEM_dec_NOT_Empty>>
  drule (CONJUNCT1 check_lstep_list_id_del)>>
  drule (CONJUNCT1 check_lstep_list_id_upper)>>
  disch_then drule>>rw[]>>
  `i < id` by (
    CCONTR_TAC>>
    gvs[])>>
  first_x_assum drule_all>>
  rw[]>>
  gvs[]
QED

Theorem opt_update_inds_vimap_rel:
  vimap_rel fml vimap ∧ FST (SND vimap) ≤ id ∧
  opt_update_inds fml c id inds assg st =
    (fml',inds',id',assg',st') ⇒
  vimap_rel fml' vimap
Proof
  Cases_on`c`>>strip_tac>>gvs[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  gvs[opt_update_inds_def,enc_mv_enc,store_ind_enc,opt_update_SOME]>>
  simp[vimap_rel_update_resize]
QED

Theorem store_rels:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧ ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  grow_assg assg st (max_var (FST c) + 1) = (assg',st') ⇒
  fml_rel (insert id (c,b) fml) (update_resize fmlls Empty (enc c b) id) ∧
  rup_inv (update_resize fmlls Empty (enc c b) id) assg' st' ∧
  ind_rel (update_resize fmlls Empty (enc c b) id) (sorted_insert id inds) ∧
  vimap_rel (update_resize fmlls Empty (enc c b) id) vimap ∧
  (∀n. n ≥ id + 1 ⇒
    any_el n (update_resize fmlls Empty (enc c b) id) Empty = Empty)
Proof
  rw[fml_rel_update_resize,ind_rel_update_resize_sorted_insert,
    vimap_rel_update_resize,any_el_update_resize]>>
  metis_tac[rup_inv_update_resize_grow]
QED

Theorem fml_rel_check_sstep_list:
  ∀sstep pres ord obj fmlls inds id assg st fmlls' id' inds' assg' st' fml
    ht ht'.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    ind_rel fmlls inds ∧
    vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
    vomap_rel obj vomap ∧ po = mk_ord_pre ord ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    check_sstep_list sstep pres ord po obj tcb fmlls inds id vimap vomap assg st
      ht =
      SOME (fmlls',inds',vimap',id',assg',st',ht') ⇒
    ∃fml'.
      check_sstep sstep pres ord obj tcb fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st' ∧
      ind_rel fmlls' inds' ∧
      vimap_rel fmlls' vimap' ∧ FST (SND vimap') ≤ id' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
      id ≤ id'
Proof
  Cases>>rw[]>>fs[check_sstep_list_def,check_sstep_def]
  >- (
    gvs[AllCaseEqs()]>>
    pairarg_tac>>gvs[]>>
    `0 ≤ id` by fs[]>>
    imp_res_tac opt_update_inds_opt_update>>
    drule (CONJUNCT1 fml_rel_check_lstep_list)>>
    rpt(disch_then drule)>>
    rw[]>>simp[]>>
    CONJ_TAC >-
      metis_tac[opt_update_inds_ind_rel,ind_rel_check_lstep_list]>>
    `id ≤ id'' ∧ id'' ≤ id'` by
      metis_tac[check_lstep_list_id,opt_update_id]>>
    `vimap_rel rfml vimap` by metis_tac[vimap_rel_check_lstep_list]>>
    `FST (SND vimap) ≤ id''` by decide_tac>>
    `vimap_rel fml' vimap` by metis_tac[opt_update_inds_vimap_rel]>>
    simp[]>>
    drule (CONJUNCT1 check_lstep_list_id_upper)>>
    drule opt_update_id_upper>>
    simp[])>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs(),insert_fml_def,enc_mv_enc,store_ind_enc]>>
  drule_at (Pos last) fml_rel_check_red_list>>
  disch_then (qspec_then`fml` mp_tac)>>
  simp[]>>strip_tac>>
  gvs[opt_update_SOME]>>
  qmatch_asmsub_abbrev_tac`UNCURRY _ SI = SOME _`>>
  PairCases_on`SI`>>
  qpat_x_assum`Abbrev _`
    (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
  gvs[store_ind_enc,opt_update_SOME]>>
  drule_all store_rels>>
  simp[]
QED

Definition do_dom_check_def:
  do_dom_check idopt fml rfml inds base ht goals extra pfs dsubs dindex =
  case idopt of NONE =>
    let (l,r) = extract_scoped_pids_list pfs [] LN in
    if
      find_scope_1 dindex pfs ∧
      check_hash_goals_slot extra [dindex] r dsubs
    then
      split_goals_hash F rfml inds base ht extra l goals
    else (F,ht)
  | SOME cid =>
     (check_contradiction_fml_list F fml cid, ht)
End

(* maybe memory ... *)
Definition core_fmlls_def:
  (core_fmlls fml [] = []) ∧
  (core_fmlls fml (i::is) =
  case lookup_core_only_list T fml i of
    Empty => core_fmlls fml is
  | s => (i,s)::core_fmlls fml is)
End

(* The objective and solution checks, evaluated over the core
  constraints at the indices *)
Definition check_obj_core_def:
  check_obj_core obj wm fml inds bopt =
  let wv = mk_obj_vec wm in
  let w = vec_lookup_d F wv in
  let new = eval_obj obj w in
  if EVERY (λi. sat_slot wv (lookup_core_only_list T fml i)) inds
  then
    case bopt of NONE => SOME (new, w)
    | SOME b =>
      if b = new then SOME (new, w) else NONE
  else NONE
End

Definition check_sol_core_def:
  check_sol_core wm free fml inds =
  if sol_free_ok wm free then
    let cv = mk_cube_vec wm free in
    let cw = vec_lookup_d 0 cv in
    if sol_cw_ok cw wm ∧
      EVERY (λi. cube_slot cv (lookup_core_only_list T fml i)) inds then
      SOME (sol_fun cw)
    else NONE
  else NONE
End

(* flag all indices as T *)
Definition core_from_inds_def:
  (core_from_inds fml [] = SOME fml) ∧
  (core_from_inds fml (i::is) =
    let s = any_el i fml Empty in
    if s = Empty then NONE
    else core_from_inds (update_resize fml Empty (set_core_slot s T) i) is)
End

Theorem any_el_core_from_inds:
  ∀inds fml fmlls fmlls' n.
  fml_rel fml fmlls ∧
  core_from_inds fmlls inds = SOME fmlls' ⇒
  any_el n fmlls' Empty =
    enc_opt (OPTION_MAP (λ(c,b). (c, b ∨ MEM n inds)) (lookup n fml))
Proof
  Induct>>rw[core_from_inds_def]
  >- (
    gvs[fml_rel_def]>>
    Cases_on`lookup n fml`>>simp[]>>
    rename1`SOME p`>>PairCases_on`p`>>simp[])>>
  `∃c b'. lookup h fml = SOME (c,b') ∧ any_el h fmlls Empty = enc c b'` by (
    irule fml_rel_any_el>>simp[])>>
  gvs[]>>
  first_x_assum (qspecl_then [`insert h (c,T) fml`,
    `update_resize fmlls Empty (enc c T) h`,`fmlls'`,`n`] mp_tac)>>
  impl_tac >- gvs[fml_rel_update_resize]>>
  rw[lookup_insert]>>
  gvs[]
QED

(* core_from_inds, leaving slots that are already core untouched *)
Definition core_from_inds_skip_def:
  (core_from_inds_skip fml [] = SOME fml) ∧
  (core_from_inds_skip fml (i::is) =
    let s = any_el i fml Empty in
    if s = Empty then NONE
    else if core_slot s then core_from_inds_skip fml is
    else core_from_inds_skip (update_resize fml Empty (set_core_slot s T) i) is)
End

Theorem core_from_inds_skip_eq:
  ∀is fml.
  core_from_inds_skip fml is = core_from_inds fml is
Proof
  Induct>>rw[core_from_inds_skip_def,core_from_inds_def]>>
  `update_resize fml Empty (set_core_slot (any_el h fml Empty) T) h = fml` by (
    Cases_on`any_el h fml Empty`>>
    gvs[core_slot_def,set_core_slot_def]>>
    gvs[update_resize_def,any_el_ALT,AllCaseEqs()]>>
    metis_tac[LUPDATE_SAME])>>
  simp[]
QED

(* every stored slot below w is core *)
Definition core_below_def:
  core_below w fmlls ⇔
  ∀n. n < w ∧ any_el n fmlls Empty ≠ Empty ⇒ core_slot (any_el n fmlls Empty)
End

Theorem core_below_0[simp]:
  core_below 0 fmlls
Proof
  simp[core_below_def]
QED

(* flag the stored slots in [w, id) as core, within the length of fml *)
Definition core_from_range_def:
  core_from_range fml w id =
  if w < id ∧ w < LENGTH fml then
    let s = any_el w fml Empty in
    if s = Empty ∨ core_slot s then core_from_range fml (w + 1) id
    else core_from_range (update_resize fml Empty (set_core_slot s T) w) (w + 1) id
  else fml
Termination
  WF_REL_TAC`measure (λ(fml,w,id). id - w)`
End

Theorem any_el_core_from_range:
  ∀fml w id n.
  any_el n (core_from_range fml w id) Empty =
  if w ≤ n ∧ n < id then set_core_slot (any_el n fml Empty) T
  else any_el n fml Empty
Proof
  ho_match_mp_tac core_from_range_ind>>
  rpt strip_tac>>
  simp[Once core_from_range_def]>>
  reverse IF_CASES_TAC
  >- (
    rw[]>>
    `LENGTH fml ≤ n` by gvs[]>>
    gvs[any_el_ALT,set_core_slot_def])>>
  IF_CASES_TAC>>
  gvs[any_el_update_resize]>>
  Cases_on`n = w`>>gvs[]
  >~ [`any_el n fml Empty = set_core_slot (any_el n fml Empty) T`]
  >- (Cases_on`any_el n fml Empty`>>gvs[set_core_slot_def,core_slot_def])>>
  `w + 1 ≤ n ⇔ w ≤ n` by decide_tac>>
  simp[]
QED

Theorem any_el_core_from_range_Empty:
  any_el n (core_from_range fmlls w id) Empty = Empty ⇔
  any_el n fmlls Empty = Empty
Proof
  rw[any_el_core_from_range]
QED

Theorem core_below_core_from_range:
  core_below w fmlls ⇒
  core_below id (core_from_range fmlls w id)
Proof
  rw[core_below_def,any_el_core_from_range]>>
  Cases_on`w ≤ n`>>gvs[]
  >- (Cases_on`any_el n fmlls Empty`>>gvs[set_core_slot_def,core_slot_def])>>
  first_x_assum irule>>
  simp[]
QED

(* core_below w is kept by any change that, below w, only deletes *)
Theorem core_below_frame:
  core_below w fmlls ∧
  (∀n. n < w ∧ any_el n fmlls' Empty ≠ Empty ⇒
    any_el n fmlls Empty = any_el n fmlls' Empty) ⇒
  core_below w fmlls'
Proof
  rw[core_below_def]>>
  metis_tac[]
QED

Theorem core_below_core_from_inds:
  ∀l fmlls fmlls'.
  core_below w fmlls ∧
  core_from_inds fmlls l = SOME fmlls' ⇒
  core_below w fmlls'
Proof
  Induct>>rw[core_from_inds_def]>>gvs[AllCaseEqs()]>>
  last_x_assum irule>>
  pop_assum $ irule_at Any>>
  gvs[core_below_def,any_el_update_resize]>>
  rw[]>>
  Cases_on`any_el h fmlls Empty`>>gvs[set_core_slot_def,core_slot_def]
QED

(* With every slot at or above id Empty, flagging [w, id) makes every
  constraint core *)
Theorem fml_rel_core_from_range:
  fml_rel fml fmlls ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  core_below w fmlls ⇒
  fml_rel (map (λ(c,b). (c,T)) fml) (core_from_range fmlls w id)
Proof
  rw[fml_rel_def,any_el_core_from_range,lookup_map]>>
  Cases_on`lookup x fml`>>gvs[enc_opt_def]>>
  rename1`lookup x fml = SOME p`>>PairCases_on`p`>>
  gvs[enc_opt_def]>>
  rw[]>>
  Cases_on`x < id`
  >- (
    `any_el x fmlls Empty = enc (p0,p1) p2` by simp[enc_opt_def]>>
    gvs[core_below_def]>>
    first_x_assum (qspec_then`x` mp_tac)>>
    simp[enc_NOT_Empty])>>
  first_x_assum (qspec_then`x` mp_tac)>>
  simp[]
QED

Definition all_core_list_def:
  (all_core_list fml [] iacc = SOME (REVERSE iacc)) ∧
  (all_core_list fml (i::is) iacc =
    let s = any_el i fml Empty in
    if s = Empty then all_core_list fml is iacc
    else if core_slot s then all_core_list fml is (i::iacc)
    else NONE)
End

Theorem slot_list_test:
  let c1 = enc ([(1,1)],1) T in
  let c2 = enc ([(-1,2)],1) F in
  let c3 = enc ([(2,3)],1) T in
  rollback [Empty; c1; c2; c3] 1 3 = [Empty; Empty; Empty; c3] ∧
  sorted_insert 5 [4;2] = [5;4;2] ∧
  sorted_insert 3 [4;2] = [4;3;2] ∧
  lookup_core_only_list T [c1; c2] 1 = Empty ∧
  lookup_core_only_list F [c1; c2] 1 = c2 ∧
  lookup_core_only_list T [c1; c2] 0 = c1 ∧
  reindex [c1; Empty; c2] [2;1;0] = [2;0] ∧
  core_from_inds [c1; c2] [1] = SOME [c1; enc ([(-1,2)],1) T] ∧
  core_from_inds [c1; Empty] [1] = NONE ∧
  all_core_list [c1; Empty; c3] [2;1;0] [] = SOME [2;0] ∧
  all_core_list [c1; c2] [1;0] [] = NONE ∧
  split_goals_pure (mk_map [] [(0,())]) c1 [(0,([(1,1)],1)); (1,([(1,1)],1));
    (2,([(1,2)],1))] [] [] = ([([(1,1)],1)], [([(1,2)],1)])
Proof
  EVAL_TAC
QED

(* Variable 1 occurs positively in the 13 constraints, 2 of them input *)
Theorem vimap_test:
  let c = enc ([(1,1)],1) T in
  let fml = Empty :: REPLICATE 13 c in
  let vi = fill_vimap fml 14 (2,0,[]) in
  let r = get_set_indices fml [(1,INL F)] vi in
  let fml2 = LUPDATE Empty 5 fml in
  let r2 = get_set_indices fml2 [(1,INL F)] (SND r) in
  let r3 = get_set_indices fml [(7,INL F)] vi in
  let fml4 = SNOC (enc ([(1,1);(-1,2)],1) T) fml in
  let vi4 = fill_vimap fml4 15 vi in
  let r4 = get_set_indices fml4 [(1,INL F);(2,INL T)] vi4 in
  let vi5 = fill_vimap fml 14 (0,0,[]) in
  any_el 1 (SND (SND vi)) Vnone = Vinput [2;1] [] ∧
  any_el 1 (SND (SND (fill_vimap fml 14 (12,0,[])))) Vnone =
    Vcount 1 (REVERSE (GENLIST SUC 13)) [] ∧
  fill_vimap fml 10 vi = vi ∧
  any_el 1 (SND (SND (SND r))) Vnone = Vtrack (REVERSE (GENLIST SUC 13)) [] ∧
  QSORT $<= (FST r) = GENLIST SUC 13 ∧
  any_el 1 (SND (SND (SND r2))) Vnone =
    Vtrack (FILTER (λx. x ≠ 5) (REVERSE (GENLIST SUC 13))) [] ∧
  QSORT $<= (FST r2) = FILTER (λx. x ≠ 5) (GENLIST SUC 13) ∧
  FST r3 = [] ∧ any_el 7 (SND (SND (SND r3))) Vnone = Vtrack [] [] ∧
  check_fresh_aux_fml_vimap [3;7] (SND r3) ∧
  ¬check_fresh_aux_fml_vimap [1] vi ∧
  any_el 2 (SND (SND vi4)) Vnone = Vcount 1 [] [14] ∧
  any_el 1 (SND (SND (SND r4))) Vnone = Vtrack (REVERSE (GENLIST SUC 14)) [] ∧
  any_el 2 (SND (SND (SND r4))) Vnone = Vtrack [] [14] ∧
  QSORT $<= (FST r4) = GENLIST SUC 14 ∧
  any_el 1 (SND (SND vi5)) Vnone = Vinput [] [] ∧
  QSORT $<= (FST (get_set_indices fml [(1,INL F)] vi5)) = GENLIST SUC 13 ∧
  FST r4 = REVERSE (GENLIST SUC 14) ∧
  merge_all [] = [] ∧
  merge_all [[3;1]] = [3;1] ∧
  merge_all [[5;3;1];[4;3]] = [5;4;3;1] ∧
  merge_all [[5;3;1];[4;3];[6;1];[2];[9;5]] = [9;6;5;4;3;2;1]
Proof
  EVAL_TAC
QED

Definition emp_vec_def:
  emp_vec = (Sorted (Vector []) : subst)
End

Definition do_change_check_def:
  do_change_check pfs csubs =
  let (l,r) = extract_pids pfs LN LN in
    check_hash_goals ([],1) [] r csubs
End

Definition check_change_obj_list_def:
  check_change_obj_list b fml id obj fc' pfs assg st ⇔
  case obj of NONE => NONE
  | SOME fc =>
    let csubs = change_obj_subgoals (mk_tar_obj b fc) fc' in
    case extract_clauses_list emp_vec T fml csubs pfs [] of
      NONE => NONE
    | SOME cpfs =>
      (case check_subproofs_list cpfs T fml id id assg st of
        NONE => NONE
      | SOME (fml',id',assg',st') =>
        let rfml = rollback fml' id id' in
        if do_change_check pfs csubs then
          let fc'' = mk_diff_obj b fc fc' in
          SOME (rfml,fc'',id',assg',st')
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
  check_change_pres_list b fml id pres v c pfs assg st ⇔
  case pres of NONE => NONE
  | SOME pres =>
    if pres_only c pres v then
    ( let csubs = change_pres_subgoals v c in
      case extract_clauses_list emp_vec T fml csubs pfs [] of
        NONE => NONE
      | SOME cpfs =>
      (case check_subproofs_list cpfs T fml id id assg st of
        NONE => NONE
      | SOME (fml',id',assg',st') =>
        let rfml = rollback fml' id id' in
        if do_change_check pfs csubs then
          SOME (rfml,update_pres b v pres,id',assg',st')
        else NONE))
    else NONE
End

(* The invariants of the assignment between steps, which the unchecked
  operations of the RUP passes rely on: every variable of every stored
  constraint stays below its length, and the stamps stay bounded
  (stamps_ok) *)

Theorem fml_bound_store_slot:
  fml_bound fmlls (LENGTH assg) ∧ slot_bound s (mv + 1) ∧
  store_slot fmlls s mv id assg st = (fmlls',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  rpt strip_tac>>
  gvs[store_slot_def]>>
  pairarg_tac>>gvs[]>>
  drule grow_assg_LENGTH>>
  rw[]
  >- (
    irule bound_update_resize>>
    metis_tac[bound_mono,slot_bound_mono])>>
  metis_tac[stamps_ok_grow_assg]
QED

Theorem fml_bound_opt_update:
  fml_bound fmlls (LENGTH assg) ∧
  opt_update fmlls c id assg st = (fmlls',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  Cases_on`c`
  >- (rw[]>>gvs[])>>
  rename1`SOME cb`>>
  Cases_on`cb`>>
  rpt strip_tac>>
  gvs[opt_update_def,enc_mv_enc]>>
  drule_at (Pos last) fml_bound_store_slot>>
  simp[slot_bound_enc_max_var]
QED

Theorem check_rup_loop_list_LENGTH:
  ∀ns assg res assg' pre.
  check_rup_loop_list b nc fmlls assg st ns = (res,assg',pre) ⇒
  LENGTH assg' = LENGTH assg
Proof
  Induct>>
  simp[check_rup_loop_list_def]>>
  rpt gen_tac>>
  TOP_CASE_TAC>>
  simp[]>>
  rpt (pairarg_tac>>simp[])>>
  rw[]>>
  metis_tac[LENGTH_update_assg_slot,FST,SND]
QED

Theorem check_rup_list_LENGTH:
  check_rup_list b nc sz fmlls assg st ns = (res,assg',st',pre) ⇒
  LENGTH assg ≤ LENGTH assg' ∧ sz ≤ LENGTH assg'
Proof
  rw[check_rup_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  imp_res_tac check_rup_loop_list_LENGTH>>
  imp_res_tac reset_dm_list_LENGTH>>
  simp[]
QED

Theorem stamps_ok_check_rup_loop_list:
  ∀ns assg res assg' pre.
  stamps_ok assg st ∧
  check_rup_loop_list b nc fmlls assg st ns = (res,assg',pre) ⇒
  stamps_ok assg' st
Proof
  Induct>>
  simp[check_rup_loop_list_def]>>
  rpt gen_tac>>
  TOP_CASE_TAC>>
  simp[]>>
  rpt (pairarg_tac>>simp[])>>
  rw[]>>
  metis_tac[stamps_ok_update_assg_slot,FST,SND]
QED

Theorem stamps_ok_check_rup_list:
  stamps_ok assg st ∧
  check_rup_list b nc sz fmlls assg st ns = (res,assg',st',pre) ⇒
  stamps_ok assg' st'
Proof
  rw[check_rup_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  metis_tac[stamps_ok_reset_dm_list,stamps_ok_check_rup_loop_list]
QED

Theorem check_rup_loop_list_pre:
  ∀ns assg res assg' pre.
  EVERY wf_slot fmlls ∧ fml_bound fmlls (LENGTH assg) ∧
  wf_slot nc ∧ slot_bound nc (LENGTH assg) ∧
  check_rup_loop_list b nc fmlls assg st ns = (res,assg',pre) ⇒
  pre
Proof
  Induct>>
  simp[check_rup_loop_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac`get_rup_constraint_list b fmlls n nc`>>
  `wf_slot (get_rup_constraint_list b fmlls n nc) ∧
   slot_bound (get_rup_constraint_list b fmlls n nc) (LENGTH assg)` by (
    rw[get_rup_constraint_list_def]>>
    qspecl_then [`b`,`fmlls`,`n`] strip_assume_tac lookup_core_only_list_cases>>
    gvs[fml_bound_def,wf_slot_def,slot_bound_def]>>
    gvs[EVERY_EL,any_el_ALT]>>
    rw[wf_slot_def])>>
  Cases_on`get_rup_constraint_list b fmlls n nc`>>
  gvs[]>>
  rpt (pairarg_tac>>gvs[])>>
  rename1`update_assg_slot assg st s0 = (dn,assg1,p1)`>>
  `p1 ∧ LENGTH assg1 = LENGTH assg` by
    metis_tac[update_assg_slot_pre,LENGTH_update_assg_slot,FST,SND]>>
  Cases_on`dn`>>gvs[]>>
  last_x_assum (qspec_then`assg1` mp_tac)>>
  simp[]
QED

Theorem check_rup_list_pre:
  EVERY wf_slot fmlls ∧ fml_bound fmlls (LENGTH assg) ∧
  wf_slot nc ∧ slot_bound nc sz ∧
  check_rup_list b nc sz fmlls assg st ns = (res,assg',st',pre) ⇒
  pre
Proof
  rw[check_rup_list_def]>>
  rpt (pairarg_tac>>gvs[])>>
  drule_at (Pos last) check_rup_loop_list_pre>>
  disch_then irule>>
  imp_res_tac reset_dm_list_LENGTH>>
  metis_tac[bound_mono,slot_bound_mono]
QED

Theorem fml_bound_check_lstep_list:
  (∀lstep b fmlls mindel id assg st fmlls' c id' assg' st'.
    fml_bound fmlls (LENGTH assg) ∧
    check_lstep_list lstep b fmlls mindel id assg st =
      SOME (fmlls',c,id',assg',st') ⇒
    fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
    (stamps_ok assg st ⇒ stamps_ok assg' st')) ∧
  (∀lsteps b fmlls mindel id assg st fmlls' id' assg' st'.
    fml_bound fmlls (LENGTH assg) ∧
    check_lsteps_list lsteps b fmlls mindel id assg st =
      SOME (fmlls',id',assg',st') ⇒
    fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
    (stamps_ok assg st ⇒ stamps_ok assg' st'))
Proof
  ho_match_mp_tac check_lstep_list_ind>>
  rpt conj_tac>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  strip_tac
  >- (
    qpat_x_assum`check_lstep_list _ _ _ _ _ _ _ = _` mp_tac>>
    simp[Once check_lstep_list_def]>>
    Cases_on`lstep`>>
    simp[AllCaseEqs()]>>
    strip_tac>>
    rpt (pairarg_tac>>gvs[])>>
    gvs[bound_list_delete_list,AllCaseEqs()]
    >~ [`check_rup_list`]
    >- (
      drule check_rup_list_LENGTH>>
      metis_tac[bound_mono,stamps_ok_check_rup_list])>>
    drule_all fml_bound_opt_update>>
    strip_tac>>
    first_x_assum drule_all>>
    simp[bound_rollback])
  >- gvs[check_lstep_list_def]
  >- gvs[check_lstep_list_def]>>
  qpat_x_assum`check_lsteps_list _ _ _ _ _ _ _ = _` mp_tac>>
  simp[Once check_lstep_list_def,AllCaseEqs()]>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  drule_all fml_bound_opt_update>>
  strip_tac>>
  gvs[]
QED

Theorem fml_bound_list_insert_fml_list:
  ∀cs b id fmlls assg st id' fmlls' assg' st'.
  fml_bound fmlls (LENGTH assg) ∧
  list_insert_fml_list cs b id fmlls assg st = (id',fmlls',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  Induct>>
  simp[list_insert_fml_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  pairarg_tac>>gvs[]>>
  drule_all fml_bound_opt_update>>
  strip_tac>>
  first_x_assum drule_all>>
  gvs[]
QED

Theorem fml_bound_check_subproofs_list:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st'.
  fml_bound fmlls (LENGTH assg) ∧
  check_subproofs_list pfs b fmlls mindel id assg st =
    SOME (fmlls',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  ho_match_mp_tac check_subproofs_list_ind>>
  simp[check_subproofs_list_def]>>
  rpt strip_tac>>
  gvs[AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  imp_res_tac fml_bound_list_insert_fml_list>>
  imp_res_tac (CONJUNCT2 fml_bound_check_lstep_list)>>
  imp_res_tac bound_rollback>>
  gvs[]
QED

Theorem fml_bound_list_insert_sc_list:
  ∀cs b id fmlls assg st id' fmlls' assg' st'.
  fml_bound fmlls (LENGTH assg) ∧ EVERY sc_hyp_ok cs ∧
  list_insert_sc_list cs b id fmlls assg st = (id',fmlls',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  rpt strip_tac>>
  gvs[list_insert_sc_list_eq]>>
  drule_all fml_bound_list_insert_fml_list>>
  simp[]
QED

Theorem fml_bound_check_scopes_list:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st'.
  fml_bound fmlls (LENGTH assg) ∧ scopes_ok pfs ∧
  check_scopes_list pfs b fmlls mindel id assg st =
    SOME (fmlls',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  ho_match_mp_tac check_scopes_list_ind>>
  simp[check_scopes_list_def,scopes_ok_def]>>
  rpt strip_tac>>
  gvs[AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  imp_res_tac fml_bound_list_insert_sc_list>>
  imp_res_tac fml_bound_check_subproofs_list>>
  imp_res_tac bound_rollback>>
  gvs[scopes_ok_def]
QED

Theorem fml_bound_check_red_list_fast:
  fml_bound fmlls (LENGTH assg) ∧ slot_bound fc (mv + 1) ∧
  check_red_list_fast b fmlls inds id fc mv pf cid vimap assg st ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  strip_tac>>
  gvs[check_red_list_fast_def]>>
  pairarg_tac>>gvs[AllCaseEqs()]>>
  drule_at (Pos last) fml_bound_store_slot>>
  gvs[]>>
  strip_tac>>
  imp_res_tac (CONJUNCT2 fml_bound_check_lstep_list)>>
  gvs[bound_rollback]
QED

Theorem fml_bound_check_red_list:
  fml_bound fmlls (LENGTH assg) ∧ slot_bound fc (mv + 1) ∧
  po = mk_ord_pre ord ∧
  check_red_list pres ord po obj b tcb fmlls inds id fc mv s pfs idopt
    vimap vomap assg st ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  strip_tac>>
  gvs[check_red_list_def,AllCaseEqs()]
  >- (
    rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
    drule_at (Pos last) fast_red_subgoals_scopes_ok>>
    simp[]>>strip_tac>>
    drule_all scopes_ok_extract_scopes_list>>strip_tac>>
    drule_at (Pos last) fml_bound_store_slot>>
    gvs[]>>
    strip_tac>>
    imp_res_tac fml_bound_check_scopes_list>>
    gvs[bound_rollback])>>
  drule_all fml_bound_check_red_list_fast>>
  simp[]
QED

Definition check_spec_aux_list_def:
  (check_spec_aux_list asv fml inds id [] vimap assg st ht = SOME (assg,st)) ∧
  (check_spec_aux_list asv fml inds id (((c,s,pfs,idopt)::gs):specproof) vimap assg st ht =
  if check_support asv s then
    let (fc,mv) = enc_mv c F in
    case check_red_list (NONE:num_set option) (NONE:ord_s option) NONE NONE
      F F fml inds id fc mv s pfs idopt vimap «» assg st ht of
        NONE => NONE
      | SOME (fml',inds',vimap',id',assg',st',ht') =>
        let (fml'',inds'',id'',assg'',st'') =
          store_ind fml' fc mv id' inds' assg' st' in
        check_spec_aux_list asv fml'' inds'' id'' gs vimap' assg'' st'' ht'
  else NONE)
End

Theorem fml_rel_check_spec_aux_list:
  ∀gs fml fmlls inds vimap id assg st ht.
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_spec_aux_list as fmlls inds id gs vimap assg st ht = SOME (assg',st') ⇒
  check_spec_aux as (fml,id) gs ∧
  ∃dm. dm_rel dm assg' st'
Proof
  Induct
  >- (
    rw[check_spec_aux_def,check_spec_aux_list_def]>>
    gvs[rup_inv_def]>>
    metis_tac[])>>
  rpt gen_tac>>strip_tac>>
  `?c s pfs idopt. h = (c,s,pfs,idopt)` by metis_tac[PAIR]>>
  gvs[check_spec_aux_def,check_spec_aux_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  gvs[enc_mv_enc]>>
  drule_at (Pos last) fml_rel_check_red_list>>
  simp[vomap_rel_def,mk_ord_pre_def]>>
  disch_then drule>>
  strip_tac>>
  gvs[store_ind_enc,opt_update_SOME,insert_fml_def]>>
  drule_all store_rels>>
  disch_then (qspec_then`F` strip_assume_tac)>>
  `FST (SND vimap') ≤ id' + 1` by decide_tac>>
  first_x_assum drule_all>>
  simp[]
QED

Theorem check_spec_aux_list_LENGTH:
  ∀gs fmlls inds vimap id assg st ht.
  fml_bound fmlls (LENGTH assg) ∧
  check_spec_aux_list as fmlls inds id gs vimap assg st ht = SOME (assg',st') ⇒
  LENGTH assg ≤ LENGTH assg' ∧ (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  Induct>>
  rw[check_spec_aux_list_def]>>
  `?c s pfs idopt. h = (c,s,pfs,idopt)` by metis_tac[PAIR]>>
  gvs[check_spec_aux_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  gvs[enc_mv_enc]>>
  drule_at (Pos last) fml_bound_check_red_list>>
  simp[slot_bound_enc_max_var,mk_ord_pre_def]>>
  strip_tac>>
  gvs[store_ind_enc]>>
  drule_all fml_bound_opt_update>>
  strip_tac>>
  first_x_assum drule_all>>
  strip_tac>>
  simp[]>>
  metis_tac[]
QED

(* The largest variable of the specification's constraints, at least mv *)
Definition spec_max_var_def:
  (spec_max_var ([]:specproof) mv = mv:num) ∧
  (spec_max_var ((c,rest)::gs) mv =
    let (s,m,mv',n) = sum_max_abs (FST c) 0 0 mv 0 in
    spec_max_var gs mv')
End

(* The specification is checked on its own formula and index, with the
  assignment array of the main proof; the index starts sized to the
  specification's variables *)
Definition check_spec_list_def:
  check_spec_list (us,vs,as) gs assg st =
    let asv = mk_as_vec as in
    let mv = spec_max_var gs 0 in
    case check_spec_aux_list asv [] [] 1 gs (0,0,REPLICATE (mv+1) Vnone)
      assg st ht_empty of
      NONE => NONE
    | SOME (assg',st') => SOME (asv,assg',st')
End

Theorem fml_rel_check_spec_list:
  check_spec_list vars gs assg st = SOME (asv,assg',st') ∧
  (∃dm. dm_rel dm assg st) ⇒
  check_spec vars gs = SOME asv ∧
  ∃dm. dm_rel dm assg' st'
Proof
  PairCases_on`vars`>>
  simp[check_spec_list_def,check_spec_def,AllCaseEqs()]>>
  disch_then strip_assume_tac>>gvs[]>>
  drule_at (Pos last) fml_rel_check_spec_aux_list>>
  disch_then (qspec_then`LN` mp_tac)>>
  impl_tac >- (
    rw[rup_inv_def,fml_bound_def]>>
    EVAL_TAC>>
    simp[lookup_def,enc_opt_def]>>
    metis_tac[dm_rel_def])>>
  simp[]
QED

Theorem check_spec_list_LENGTH:
  check_spec_list vars gs assg st = SOME (asv,assg',st') ⇒
  LENGTH assg ≤ LENGTH assg' ∧ (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  PairCases_on`vars`>>
  simp[check_spec_list_def,AllCaseEqs()]>>
  strip_tac>>gvs[]>>
  drule_at (Pos last) check_spec_aux_list_LENGTH>>
  disch_then irule>>
  simp[fml_bound_def,any_el_ALT]>>
  EVAL_TAC
QED

Definition insert_distinct_def:
  (insert_distinct t [] = SOME t) ∧
  (insert_distinct t (x::xs) =
    case sptree$lookup x t of
      NONE => insert_distinct (insert x () t) xs
    | SOME () => NONE
  )
End

Theorem insert_distinct_NONE:
  ∀ls t.
  insert_distinct t ls = NONE ⇔
  (¬ALL_DISTINCT ls ∨ set ls ∩ domain t ≠ {})
Proof
  Induct>>rw[insert_distinct_def]>>
  TOP_CASE_TAC>>rw[]>>
  gvs[EXTENSION,INTER_DEF,domain_lookup]
  >- (
    eq_tac>>rw[]>>
    metis_tac[option_CLAUSES])>>
  metis_tac[]
QED

Theorem insert_distinct_SOME:
  ∀ls t.
  insert_distinct t ls = SOME t' ⇒
  domain t' = domain t ∪ set ls ∧
  ALL_DISTINCT ls ∧
  set ls ∩ domain t = {}
Proof
  Induct>>rw[insert_distinct_def]>>gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  rw[EXTENSION]>>
  gvs[domain_lookup]>>
  metis_tac[option_CLAUSES]
QED

Theorem insert_distinct_IS_SOME:
  ALL_DISTINCT ls ∧ set ls ∩ domain t = {}
  ⇒
  IS_SOME (insert_distinct t ls)
Proof
  CCONTR_TAC>>gvs[]>>
  metis_tac[insert_distinct_NONE]
QED

Definition check_good_aord_fast_def:
  check_good_aord_fast ((f,g,us,vs,as):aord) ⇔
  LENGTH us = LENGTH vs ∧
  case insert_distinct LN us of NONE => F
  | SOME t =>
  case insert_distinct t vs of NONE => F
  | SOME t =>
  case insert_distinct t as of NONE => F
  | SOME t =>
  EVERY (λls. EVERY (λx. case lookup x t of NONE => F | _ => T) ls) (MAP (MAP SND o FST) f) ∧
  EVERY (λls. EVERY (λx. case lookup x t of NONE => F | _ => T) ls) (MAP (MAP SND o FST) g)
End

Theorem check_good_aord_fast_correct_1[local]:
  check_good_aord_fast aord ⇒
  check_good_aord aord
Proof
  PairCases_on`aord`>>
  rw[check_good_aord_fast_def,npbc_checkTheory.check_good_aord_def]>>
  gvs[AllCasePreds()]>>
  imp_res_tac insert_distinct_SOME>>gvs[ALL_DISTINCT_APPEND,EXTENSION]>>
  simp[EVERY_FLAT]
  >- metis_tac[]>>
  irule EVERY_MONOTONIC>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  irule EVERY_MONOTONIC>>
  first_x_assum (irule_at Any)>>
  gvs[domain_lookup]
QED

Theorem check_good_aord_fast_correct_2[local]:
  check_good_aord aord ⇒
  check_good_aord_fast aord
Proof
  PairCases_on`aord`>>
  rw[check_good_aord_fast_def,npbc_checkTheory.check_good_aord_def]>>
  gvs[AllCasePreds()]>>
  gvs[ALL_DISTINCT_APPEND]>>
  qmatch_goalsub_abbrev_tac`insert_distinct tt _`>>
  `set aord2 ∩ domain tt = {}` by fs[Abbr`tt`]>>
  drule_all insert_distinct_IS_SOME>>
  rw[IS_SOME_EXISTS]>>simp[]>>
  drule_all insert_distinct_SOME>> strip_tac>>gvs[]>>
  rename1`insert_distinct ttt _`>>
  `set aord3 ∩ domain ttt = {}` by (
    fs[Abbr`tt`,EXTENSION]>>
    metis_tac[])>>
  drule_all insert_distinct_IS_SOME>>
  rw[IS_SOME_EXISTS]>>simp[]>>
  drule_all insert_distinct_SOME>> strip_tac>>gvs[]>>
  rename1`insert_distinct tttt _`>>
  `set aord4 ∩ domain tttt = {}` by (
    fs[Abbr`tt`,EXTENSION]>>
    metis_tac[])>>
  drule_all insert_distinct_IS_SOME>>
  rw[IS_SOME_EXISTS]>>simp[]>>
  drule_all insert_distinct_SOME>> strip_tac>>gvs[]>>
  fs[EVERY_FLAT]>>
  rw[]>>
  irule EVERY_MONOTONIC>>
  first_x_assum (irule_at Any)>>
  rw[]>>
  irule EVERY_MONOTONIC>>
  first_x_assum (irule_at Any)>>
  gvs[domain_lookup,Abbr`tt`,EXTENSION]
QED

Theorem check_good_aord_eq:
  check_good_aord aord = check_good_aord_fast aord
Proof
  metis_tac[check_good_aord_fast_correct_1, check_good_aord_fast_correct_2]
QED

Definition check_ws_fast_def:
  check_ws_fast (f,g,us,vs,as) ws bs cs ⇔
  LENGTH us = LENGTH ws ∧
  LENGTH bs = LENGTH as ∧
  LENGTH cs = LENGTH as ∧
  case insert_distinct LN ws of NONE => F
  | SOME t =>
  case insert_distinct t bs of NONE => F
  | SOME t =>
  case insert_distinct t cs of NONE => F
  | SOME t =>
  EVERY (λv. case sptree$lookup v t of NONE => T | _ => F) us ∧
  EVERY (λv. case sptree$lookup v t of NONE => T | _ => F) vs ∧
  EVERY (λv. case sptree$lookup v t of NONE => T | _ => F) as
End

Theorem check_ws_fast_correct_1[local]:
  check_ws_fast aord ws bs cs ⇒
  check_ws aord ws bs cs
Proof
  PairCases_on`aord`>>
  rw[check_ws_fast_def,npbc_checkTheory.check_ws_def]>>
  gvs[AllCasePreds()]>>
  imp_res_tac insert_distinct_SOME>>gvs[ALL_DISTINCT_APPEND,EXTENSION]
  >- metis_tac[]>>
  gvs[EVERY_MEM,domain_lookup]>>
  metis_tac[option_CLAUSES]
QED

Theorem check_ws_fast_correct_2[local]:
  check_ws aord ws bs cs ⇒
  check_ws_fast aord ws bs cs
Proof
  PairCases_on`aord`>>
  rw[check_ws_fast_def,npbc_checkTheory.check_ws_def]>>
  gvs[AllCasePreds()]>>
  gvs[ALL_DISTINCT_APPEND]>>
  qmatch_goalsub_abbrev_tac`insert_distinct tt _`>>
  `set ws ∩ domain tt = {}` by fs[Abbr`tt`]>>
  drule_all insert_distinct_IS_SOME>>
  rw[IS_SOME_EXISTS]>>simp[]>>
  drule_all insert_distinct_SOME>> strip_tac>>gvs[]>>
  rename1`insert_distinct ttt _`>>
  `set bs ∩ domain ttt = {}` by (
    fs[Abbr`tt`,EXTENSION]>>
    metis_tac[])>>
  drule_all insert_distinct_IS_SOME>>
  rw[IS_SOME_EXISTS]>>simp[]>>
  drule_all insert_distinct_SOME>> strip_tac>>gvs[]>>
  rename1`insert_distinct tttt _`>>
  `set cs ∩ domain tttt = {}` by (
    fs[Abbr`tt`,EXTENSION]>>
    metis_tac[])>>
  drule_all insert_distinct_IS_SOME>>
  rw[IS_SOME_EXISTS]>>simp[]>>
  drule_all insert_distinct_SOME>> strip_tac>>gvs[]>>
  gvs[EVERY_MEM,domain_lookup,EXTENSION,Abbr`tt`]>>
  CCONTR_TAC>>gvs[GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
QED

Theorem check_ws_eq:
  check_ws aord ws bs cs = check_ws_fast aord ws bs cs
Proof
  metis_tac[check_ws_fast_correct_1, check_ws_fast_correct_2]
QED

Definition check_storeorder_def:
  check_storeorder vars gspec f pfst pfsr assg st =
  case check_spec_list vars gspec assg st of NONE => NONE
  | SOME (asv,assg',st') =>
    let aord = mk_aord vars f gspec in
    if check_good_aord aord
    then
      case check_transitivity aord pfst of
        NONE => NONE
      | SOME id =>
        if check_reflexivity aord pfsr id then SOME ((aord,asv),assg',st')
        else NONE
    else NONE
End

(* The configuration (pc, vomap, cw, po) changes only in the configuration
  steps; every stored slot below the watermark cw is core, and po is the
  precomputed loaded order. The table ht
  changes only in the goal checks and the deletions *)
Definition check_cstep_list_def:
  check_cstep_list cstep fml assg st inds vimap id (pc,vomap,cw,po) ht =
  case cstep of
    Dom c s pfs idopt =>
    (case pc.ord of
      NONE => NONE
    | SOME spo =>
    let (fc,nfc,mv) = neg_pos_slot c pc.tcb F in
    let vimap =
      if reads_vimap s T pc.ord then fill_vimap fml id vimap
      else vimap in
    if check_pres pc.pres s ∧
      check_fresh_aspo_list fc s pc.ord vimap vomap then
    ( let (rinds,vimap') = get_set_indices fml s vimap in
      let ss = mk_subst rinds s in
      let goals =
        case idopt of
          NONE => subst_indexes ss T fml rinds
        | SOME _ => [] in
      let (fml_not_c,id1,assg1,st1) = store_slot fml nfc mv id assg st in
      let (dsubs,dscopes,dindex) = dom_subgoals_list spo po ss s pc.obj in
      case extract_scopes_list dscopes ss F fml dsubs pfs of
        NONE => NONE
      | SOME cpfs =>
        (case check_scopes_list cpfs F
          fml_not_c id id1 assg1 st1 of
          NONE => NONE
        | SOME (fml',id',assg',st') =>
          let rfml = rollback fml' id id' in
          let (res,ht') =
            do_dom_check idopt fml' rfml inds id ht goals nfc pfs dsubs
              dindex in
          if res then
            let (fml'',inds'',id'',assg'',st'') =
              store_ind rfml fc mv id' inds assg' st' in
            SOME(fml'', assg'', st'', inds'', vimap', id'', (pc,vomap,cw,po),
              ht')
          else NONE))
    else NONE)
  | Sstep sstep =>
    (case check_sstep_list sstep pc.pres pc.ord po pc.obj pc.tcb
      fml inds id vimap vomap assg st ht of
      SOME(fml',inds',vimap',id',assg',st',ht') =>
        SOME(fml',assg',st', inds', vimap', id', (pc,vomap,cw,po), ht')
    | NONE => NONE)
  | CheckedDelete n s pfs idopt => (
    if check_tcb_idopt pc.tcb idopt then
      (case lookup_core_only_list T fml n of
        Empty => NONE
      | fc =>
          (let nfml = delete_list n fml in
          let mv = slot_max_var fc in
          case check_red_list pc.pres pc.ord po pc.obj T pc.tcb
            nfml inds id fc mv s pfs idopt vimap vomap assg st
            (ht_del fml [n] ht) of
            SOME (ncf',inds',vimap',id',assg',st',ht') =>
            SOME (ncf',assg',st', inds', vimap', id', (pc,vomap,cw,po), ht')
          | NONE => NONE) )
    else NONE)
  | UncheckedDelete ls => (
    (* Either no order or all ids are in core *)
    if ¬pc.tcb ∧ pc.ord = NONE
    then
      SOME (list_delete_list ls fml, assg, st, inds,
        vimap, id, (pc with chk := F, vomap, cw, po), ht_del fml ls ht)
    else
    case all_core_list fml inds [] of NONE => NONE
    | SOME inds' =>
      SOME (list_delete_list ls fml, assg, st, inds',
        vimap, id, (pc with chk := F, vomap, cw, po), ht_del fml ls ht))
  | Transfer ls =>
    (case core_from_inds fml ls of NONE => NONE
    | SOME fml' =>
      SOME (fml', assg, st, inds, vimap, id, (pc,vomap,cw,po), ht))
  | StrengthenToCore b =>
    (let pc' = pc with tcb := b in
    if b
    then
      SOME (core_from_range fml cw id, assg, st, inds, vimap, id,
        (pc', vomap, id, po), ht)
    else
      SOME (fml, assg, st, inds, vimap, id, (pc', vomap, cw, po), ht))
  | LoadOrder nn xs =>
    (case ALOOKUP pc.orders nn of NONE => NONE
    | SOME ord' =>
      if guard_ord_t ord' xs then
        let ord = mk_ordsub ord' xs in
        SOME (core_from_range fml cw id, assg, st, inds,
          vimap, id,
          (pc with ord := ord, vomap, id, mk_ord_pre ord), ht)
      else NONE)
  | UnloadOrder =>
    (case pc.ord of NONE => NONE
    | SOME spo =>
        SOME (fml, assg, st, inds,
          vimap, id, (pc with ord := NONE, vomap, cw, NONE), ht))
  | StoreOrder nn vars gspec f pfsr pfst =>
    (case check_storeorder vars gspec f pfst pfsr assg st of NONE => NONE
    | SOME (aord,assg',st') =>
      SOME (fml, assg', st', inds,
        vimap, id,
        (pc with orders := (nn ,aord)::pc.orders, vomap, cw, po), ht))
  | Obj w mi bopt => (
    case check_obj_core pc.obj w fml inds bopt of
      NONE => NONE
    | SOME (new,w) =>
      let rinds = reindex fml inds in
      let bound' = update_bound pc.chk pc.bound new in
      let dbound' = update_dbound pc.dbound new in
      if mi then
        if pc.obj ≠ NONE then
          let c = model_improving pc.obj new in
          let (s,mv) = enc_mv c T in
          let (fml',inds',id',assg',st') =
            store_ind fml s mv id rinds assg st in
          SOME (
            fml', assg', st', inds', vimap, id',
            (pc with
            <| bound := bound';
               dbound := dbound' |>, vomap, cw, po), ht)
        else NONE
      else
        SOME (fml, assg, st, rinds, vimap, id,
          (pc with
          <| bound := bound';
             dbound := dbound' |>, vomap, cw, po), ht))
  | ChangeObj b fc' pfs =>
    (case check_change_obj_list b fml id pc.obj
        fc' pfs assg st of
      NONE => NONE
    | SOME (fml',fc',id',assg',st') =>
      SOME (
        fml', assg', st', inds,
        vimap, id',
        (pc with obj:=SOME fc', mk_vomap (strlen vomap) fc', cw, po), ht))
  | CheckObj fc' =>
    if check_eq_obj pc.obj fc'
    then SOME (fml, assg, st, inds, vimap, id, (pc,vomap,cw,po), ht)
    else NONE
  | AssertObj i => (
      if pc.obj ≠ NONE then
        let c = model_improving pc.obj i in
        let dbound' = update_dbound pc.dbound i in
        let (s,mv) = enc_mv c T in
        let (fml',inds',id',assg',st') =
          store_ind fml s mv id inds assg st in
          SOME (
            fml', assg', st', inds', vimap, id',
            (pc with dbound := dbound', vomap, cw, po), ht)
      else NONE
    )
  | ChangePres b v c pfs =>
    (case check_change_pres_list b fml id pc.pres
        v c pfs assg st of
      NONE => NONE
    | SOME (fml',pres',id',assg',st') =>
      SOME (
        fml', assg', st', inds,
        vimap, id',
        (pc with pres:=SOME pres', vomap, cw, po), ht))
  | Sol w free =>
    (if pc.obj ≠ NONE ∨ ¬pc.chk ∨ ¬free_ok pc.pres free then NONE
    else
    case check_sol_core w free fml inds of
      NONE => NONE
    | SOME w =>
      let rinds = reindex fml inds in
      let bound' = update_bound pc.chk pc.bound 0 in
      let dbound' = update_dbound pc.dbound 0 in
      let c = model_banning pc.pres free w in
      let (s,mv) = enc_mv c T in
      let (fml',inds',id',assg',st') =
        store_ind fml s mv id rinds assg st in
        SOME (
          fml', assg', st', inds', vimap, id',
          (pc with
          <| bound := bound';
             dbound := dbound';
             enum := pc.enum + cube_count free |>, vomap, cw, po), ht))
  | CheckPres ls' =>
    if check_eq_pres pc.pres ls'
    then SOME (fml, assg, st, inds, vimap, id, (pc,vomap,cw,po), ht)
    else NONE
End

Theorem MEM_core_fmlls:
  MEM (x,s) (core_fmlls fmlls rinds) ⇔
    MEM x rinds ∧ s ≠ Empty ∧
    lookup_core_only_list T fmlls x = s
Proof
  Induct_on`rinds`>>rw[core_fmlls_def,slot_CASE_default]>>
  metis_tac[]
QED

Theorem EVERY_core_fmlls:
  ∀inds.
  P Empty ⇒
  (EVERY P (MAP SND (core_fmlls fml inds)) ⇔
   EVERY (λi. P (lookup_core_only_list T fml i)) inds)
Proof
  Induct>>rw[core_fmlls_def,slot_CASE_default]>>
  gvs[]
QED

Theorem check_obj_core_thm:
  check_obj_core obj wm fml inds bopt =
  check_obj_slots obj wm (MAP SND (core_fmlls fml inds)) bopt
Proof
  simp[check_obj_core_def,check_obj_slots_def]>>
  DEP_REWRITE_TAC[EVERY_core_fmlls]>>
  simp[sat_slot_def]
QED

Theorem check_sol_core_thm:
  check_sol_core wm free fml inds =
  check_sol_slots wm free (MAP SND (core_fmlls fml inds))
Proof
  simp[check_sol_core_def,check_sol_slots_def]>>
  DEP_REWRITE_TAC[EVERY_core_fmlls]>>
  simp[cube_slot_def]
QED

Theorem ind_rel_lookup_core_only_list:
  ind_rel fmlls rinds ∧
  lookup_core_only_list b fmlls x ≠ Empty ⇒
  MEM x rinds
Proof
  rw[ind_rel_def,lookup_core_only_list_def,core_only_def]>>
  gvs[AllCaseEqs()]
QED

Theorem core_fmlls_mk_core_fml:
  fml_rel fml fmlls ∧ ind_rel fmlls inds ⇒
  set (MAP dec (MAP SND (core_fmlls fmlls inds))) =
  set (MAP SND (toAList (mk_core_fml T fml)))
Proof
  strip_tac>>
  drule fml_rel_lookup_core_only>>strip_tac>>
  rw[EXTENSION,MEM_MAP,EXISTS_PROD,MEM_toAList,MEM_core_fmlls,
    lookup_mk_core_fml,slot_CASE_default]>>
  PairCases_on`x`>>simp[]>>
  metis_tac[ind_rel_lookup_core_only_list]
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
  `∃c b'. lookup h fml = SOME (c,b') ∧ any_el h fmlls Empty = enc c b'` by (
    irule fml_rel_any_el>>simp[])>>
  gvs[]>>
  first_x_assum match_mp_tac>>
  first_x_assum (irule_at Any)>>
  gvs[fml_rel_update_resize]
QED

Theorem all_core_list_mem[local]:
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
    FILTER (λx. any_el x fmlls Empty ≠ Empty) inds in
  inds' = REVERSE acc ++ is ∧
  EVERY (λx.
    ∀c b. any_el x fmlls Empty = enc c b ⇒ b) is
Proof
  Induct>>rw[all_core_list_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[]>>
  rw[]>>
  gvs[]
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
    rw[all_core_def,EVERY_MEM,FORALL_PROD,MEM_toAList]>>
    rename1`lookup i fml = SOME (c,b)`>>
    `any_el i fmlls Empty = enc c b` by
      gvs[fml_rel_def,enc_opt_def]>>
    gvs[EVERY_MEM,MEM_FILTER,ind_rel_def]>>
    first_x_assum irule>>
    metis_tac[enc_NOT_Empty])>>
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
    any_el n (rollback fml id id') Empty =
    any_el n fml Empty) ∧
  (n >= id' ⇒
    any_el n (rollback fml id id') Empty =
    any_el n fml Empty)
Proof
  simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
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
  PairCases_on`vimap`>>
  rw[vimap_rel_def,any_el_list_delete_list]>>
  Cases_on`MEM i l`>>gvs[]
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
  PairCases_on`vimap`
  \\ Induct \\ rw[core_from_inds_def] \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ last_x_assum irule
  \\ pop_assum $ irule_at Any
  \\ gvs [vimap_rel_def,any_el_update_resize]
  \\ rw [] \\ gvs []
QED

Theorem any_el_core_from_inds_Empty:
  ∀l fmlls fmlls'.
  core_from_inds fmlls l = SOME fmlls' ⇒
  (any_el n fmlls' Empty = Empty ⇔ any_el n fmlls Empty = Empty)
Proof
  Induct \\ rw[core_from_inds_def] \\ gvs [AllCaseEqs()]
  \\ first_x_assum drule
  \\ rw[any_el_update_resize]
  \\ gvs[]
QED

Theorem ind_rel_core_from_inds:
  ind_rel fmlls inds ∧
  core_from_inds fmlls l = SOME fmlls' ⇒
  ind_rel fmlls' inds
Proof
  rw[ind_rel_def]>>
  metis_tac[any_el_core_from_inds_Empty]
QED

Theorem rup_inv_core_from_inds:
  ∀l fmlls fmlls'.
  rup_inv fmlls assg st ∧
  core_from_inds fmlls l = SOME fmlls' ⇒
  rup_inv fmlls' assg st
Proof
  Induct \\ rw[core_from_inds_def] \\ gvs [AllCaseEqs()]
  \\ last_x_assum irule
  \\ pop_assum $ irule_at Any
  \\ fs[rup_inv_def]
  \\ reverse conj_tac >- metis_tac[]
  \\ irule bound_update_resize
  \\ gvs[fml_bound_def]
QED

Theorem vimap_rel_core_from_range:
  vimap_rel fmlls vimap ⇒
  vimap_rel (core_from_range fmlls w id) vimap
Proof
  PairCases_on`vimap`>>
  rw[vimap_rel_def,any_el_core_from_range]>>
  first_x_assum irule>>
  pop_assum mp_tac>>
  rw[]
QED

Theorem ind_rel_core_from_range:
  ind_rel fmlls inds ⇒
  ind_rel (core_from_range fmlls w id) inds
Proof
  simp[ind_rel_def,any_el_core_from_range_Empty]
QED

Theorem rup_inv_core_from_range:
  rup_inv fmlls assg st ⇒
  rup_inv (core_from_range fmlls w id) assg st
Proof
  rw[rup_inv_def,fml_bound_def,any_el_core_from_range]>>
  rw[]>>
  metis_tac[]
QED

Theorem ord_maps_ok_mk_ordsub:
  OPTION_ALL ord_maps_ok (mk_ordsub a xs)
Proof
  PairCases_on`a`>>simp[mk_ordsub_def,ord_maps_ok_def]
QED

Theorem fast_rn_sc_ok:
  ∀w side rs ts j.
  EVERY (λr. ∃c. r = mk_ord_rec m1 m2 c) rs ⇒
  EVERY sc_hyp_ok (fast_rn_sc w side rs ts j)
Proof
  recInduct fast_rn_sc_ind>>rw[]>>
  simp[Once fast_rn_sc_def]>>
  every_case_tac>>gvs[mk_ord_rec_def,enc_mv_enc]>>
  metis_tac[]
QED

Theorem dom_subgoals_list_scopes_ok:
  po = mk_ord_pre (SOME aspo) ∧
  dom_subgoals_list aspo po s sr obj = (dsubs,dscopes,dindex) ⇒
  EVERY (EVERY sc_hyp_ok) dscopes
Proof
  strip_tac>>
  qpat_x_assum`dom_subgoals_list _ _ _ _ _ = _` mp_tac>>
  simp[dom_subgoals_list_def]>>
  Cases_on`mk_ord_pre (SOME aspo)`>>
  simp[dom_subst_list_def]
  >- (
    Cases_on`dom_subst T (subst_fun s) (SOME aspo)`>>
    Cases_on`neg_dom_subst (subst_fun s) aspo`>>
    rw[]>>
    simp[EVERY_MAP])>>
  PairCases_on`aspo`>>
  gvs[mk_ord_pre_def,AllCaseEqs(),dom_subst_fast_def,neg_dom_subst_fast_def]>>
  rw[]>>
  simp[]>>rw[]>>
  irule fast_rn_sc_ok>>
  simp[EVERY_MAP,EVERY_MEM]>>
  metis_tac[]
QED

Theorem dom_subgoals_list_thm:
  po_rel (SOME aspo) po ∧
  dom_subgoals_list aspo po (mk_subst r sr) sr obj = (dsubs,dscopes,dindex) ⇒
  dom_subgoals aspo (subst_fun (mk_subst r sr)) def obj =
    (dsubs, MAP (MAP sc_hyp_dec) dscopes, dindex)
Proof
  strip_tac>>
  gvs[po_rel_def]>>
  mp_tac (Q.INST [‘po’ |-> ‘mk_ord_pre (SOME aspo)’, ‘ord’ |-> ‘SOME aspo’,
    ‘hs’ |-> ‘T’, ‘w’ |-> ‘subst_fun (mk_subst r sr)’] dom_subst_list_thm)>>
  impl_tac >- rw[subst_fun_mk_subst,ALOOKUP_NONE]>>
  qpat_x_assum`dom_subgoals_list _ _ _ _ _ = _` mp_tac>>
  simp[dom_subgoals_list_def,dom_subgoals_def]>>
  Cases_on`dom_subst_list T (subst_fun (mk_subst r sr)) sr (SOME aspo)
    (mk_ord_pre (SOME aspo))`>>
  Cases_on`dom_subst T (subst_fun (mk_subst r sr)) (SOME aspo)`>>
  simp[]>>
  Cases_on`neg_dom_subst (subst_fun (mk_subst r sr)) aspo`>>
  Cases_on`mk_ord_pre (SOME aspo)`>>simp[]
  >- (
    rw[]>>
    simp[MAP_MAP_o,combinTheory.o_DEF,EVERY_MAP])>>
  qmatch_asmsub_rename_tac`mk_ord_pre (SOME aspo) = SOME p`>>
  mp_tac (Q.INST [‘w’ |-> ‘subst_fun (mk_subst r sr)’] neg_dom_subst_fast_thm)>>
  impl_tac >- rw[subst_fun_mk_subst,ALOOKUP_NONE]>>
  Cases_on`neg_dom_subst_fast (subst_fun (mk_subst r sr)) sr p`>>
  rw[]>>
  simp[]
QED

Theorem fml_rel_check_cstep_list:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  vomap_rel pc.obj vomap ∧ po_rel pc.ord po ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  core_below cw fmlls ∧
  check_cstep_list cstep fmlls assg st inds vimap id (pc,vomap,cw,po) ht =
    SOME (fmlls',assg',st',inds',vimap',id',(pc',vomap',cw',po'),ht') ⇒
  ∃fml'.
    check_cstep cstep fml id pc = SOME (fml', id', pc') ∧
    fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧ FST (SND vimap') ≤ id' ∧
    vomap_rel pc'.obj vomap' ∧ po_rel pc'.ord po' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
    id ≤ id'
Proof
  Cases_on`cstep`>>rw[po_rel_def]
  >~ [‘Dom’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs(),neg_pos_slot_enc,store_slot_enc,max_var_not]>>
    qmatch_asmsub_abbrev_tac`UNCURRY _ DDC = SOME _`>>
    PairCases_on`DDC`>>
    qpat_x_assum`Abbrev _`
      (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
    gvs[]>>
    `dom_subgoals spo (subst_fun (mk_subst rinds l)) p pc.obj =
       (dsubs',MAP (MAP sc_hyp_dec) dscopes',dindex')` by (
      irule dom_subgoals_list_thm>>simp[po_rel_def])>>
    drule_at (Pos last) dom_subgoals_list_scopes_ok>>
    simp[]>>strip_tac>>
    drule_all fill_get_set_indices>> strip_tac>>
    qspecl_then [`[]`,`rinds`,`l`] SUBST_ALL_TAC subst_fun_mk_subst_rinds>> gvs[]>>
    drule_all fill_check_fresh_aspo_list>>
    disch_then $ irule_at Any>>
    DEP_REWRITE_TAC[fml_rel_extract_scopes_list]>>
    simp[PULL_EXISTS]>>
    drule_all scopes_ok_extract_scopes_list>> strip_tac>>
    qpat_x_assum`opt_update fmlls _ _ _ _ = _` assume_tac>>
    drule_all rup_inv_opt_update>> strip_tac>>
    gvs[opt_update_SOME]>>
    drule_at (Pos last) fml_rel_check_scopes_list >>
    disch_then(qspec_then`insert id (not p,F) fml` mp_tac)>>
    impl_tac >- (
      fs[fml_rel_update_resize,any_el_update_resize])>>
    strip_tac>>simp[]>>
    drule check_scopes_list_id>>
    drule check_scopes_list_id_upper>>
    drule check_scopes_list_mindel>>
    simp[any_el_update_resize]>>
    ntac 3 strip_tac>>
    pairarg_tac>>
    gvs[insert_fml_def,store_ind_enc,opt_update_SOME]>>
    qmatch_asmsub_rename_tac`check_scopes_list _ _ _ _ _ _ _ = SOME (_,id1,_,_)`>>
    `fml_rel fml (rollback fml' id id1)` by (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      qmatch_asmsub_rename_tac
        `do_dom_check dopt _ _ _ _ _ _ (enc (not dc) F) dpfs _ _ = _`>>
      qmatch_asmsub_rename_tac`extract_scoped_pids _ LN LN = (dl,dr)`>>
      Cases_on`dopt`>>
      gvs[do_dom_check_def,check_hash_goals_slot_enc]
      >- (
        Cases_on`extract_scoped_pids_list dpfs [] LN`>>
        rename1`extract_scoped_pids_list dpfs [] LN = (pl,pr)`>>
        qspecl_then [`dpfs`,`[]`,`LN`,`LN`] mp_tac
          extract_scoped_pids_list_thm>>
        simp[]>>strip_tac>>gvs[]>>
        Cases_on`find_scope_1 dindex dpfs ∧ check_hash_goals dc [dindex] dr dsubs`>>
        gvs[]>>
        drule_at (Pos (el 2)) split_goals_hash_imp_split_goals>>
        disch_then drule>>
        disch_then (qspec_then`dl` mp_tac)>>
        impl_tac >- simp[]>>
        match_mp_tac split_goals_same_goals>>
        simp[EXTENSION,FORALL_PROD]>>
        rw[]>>eq_tac>>rw[]
        >- (
          fs[MEM_toAList,lookup_map_opt,AllCaseEqs(),lookup_mk_core_fml]>>
          irule MEM_subst_indexes>>
          qpat_assum`fml_rel fml fmlls` (irule_at Any)>>
          simp[]>>
          metis_tac[IS_SOME_EXISTS])>>
        qpat_x_assum`fml_rel fml fmlls` assume_tac>>
        drule_at (Pos last) subst_indexes_MEM>>
        disch_then drule>>
        rw[]>>
        gvs[MEM_toAList,lookup_map_opt,lookup_mk_core_fml])>>
      metis_tac[fml_rel_check_contradiction_fml])>>
    `rup_inv (rollback fml' id id1) assg'' st''` by
      metis_tac[rup_inv_rollback]>>
    `ind_rel (rollback fml' id id1) inds` by (
      match_mp_tac ind_rel_rollback_2>>
      fs[])>>
    `vimap_rel (rollback fml' id id1) vimap'` by
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    `FST (SND vimap') ≤ id1` by decide_tac>>
    `∀n. n ≥ id1 ⇒ any_el n (rollback fml' id id1) Empty = Empty` by
      simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    drule_all store_rels>>
    simp[])
  >~ [‘Sstep’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_at (Pos last) fml_rel_check_sstep_list>>
    disch_then (qspec_then`fml` mp_tac)>>
    simp[]>>rw[]>>simp[])
  >~ [‘CheckedDelete’] >- (
    gvs[check_cstep_list_def,slot_CASE_default,AllCaseEqs(),check_cstep_def]>>
    drule_all fml_rel_lookup_core_only_enc>> strip_tac>> gvs[]>>
    `delete_list n fmlls = list_delete_list [n] fmlls` by
      simp[list_delete_list_def]>>
    gvs[]>>
    drule_at (Pos last) fml_rel_check_red_list>>
    disch_then (qspec_then`delete n fml` mp_tac)>>
    impl_tac >- (
      rw[]
      >~ [`fml_rel`] >- (
        drule fml_rel_list_delete_list>>
        disch_then (qspec_then`[n]` mp_tac)>>
        simp[])
      >~ [`rup_inv`] >- metis_tac[rup_inv_list_delete_list]
      >~ [`ind_rel`] >- metis_tac[ind_rel_list_delete_list]
      >~ [`vimap_rel`] >- metis_tac[vimap_rel_list_delete_list]>>
      gvs[any_el_list_delete_list])>>
    rw[])
  >~ [‘UncheckedDelete’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]
    >- (
      rw[]
      >- metis_tac[fml_rel_list_delete_list]
      >- metis_tac[rup_inv_list_delete_list]
      >- metis_tac[ind_rel_list_delete_list]
      >- metis_tac[vimap_rel_list_delete_list]>>
      gvs[any_el_list_delete_list])>>
    drule_all fml_rel_all_core>>strip_tac>>
    rw[]
    >- metis_tac[fml_rel_list_delete_list]
    >- metis_tac[rup_inv_list_delete_list]
    >- metis_tac[ind_rel_list_delete_list]
    >- metis_tac[vimap_rel_list_delete_list]>>
    gvs[any_el_list_delete_list])
  >~ [‘Transfer’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all core_from_inds_do_transfer>> strip_tac>>
    simp[]>>
    rw[]
    >~ [`rup_inv`] >- metis_tac[rup_inv_core_from_inds]
    >~ [`ind_rel`] >- metis_tac[ind_rel_core_from_inds]
    >~ [`vimap_rel`] >- metis_tac[vimap_rel_core_from_inds]>>
    metis_tac[any_el_core_from_inds_Empty])
  >~ [‘StrengthenToCore’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    rw[]
    >~ [`fml_rel (map _ _)`] >- metis_tac[fml_rel_core_from_range]
    >~ [`rup_inv`] >- metis_tac[rup_inv_core_from_range]
    >~ [`ind_rel`] >- metis_tac[ind_rel_core_from_range]
    >~ [`vimap_rel`] >- metis_tac[vimap_rel_core_from_range]>>
    metis_tac[any_el_core_from_range_Empty])
  >~ [‘LoadOrder’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,ord_maps_ok_mk_ordsub]>>
    rw[]
    >~ [`fml_rel (map _ _)`] >- metis_tac[fml_rel_core_from_range]
    >~ [`rup_inv`] >- metis_tac[rup_inv_core_from_range]
    >~ [`ind_rel`] >- metis_tac[ind_rel_core_from_range]
    >~ [`vimap_rel`] >-
      metis_tac[vimap_rel_core_from_range]>>
    metis_tac[any_el_core_from_range_Empty])
  >~ [‘UnloadOrder’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,mk_ord_pre_def])
  >~ [‘StoreOrder’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,check_storeorder_def]>>
    gvs[rup_inv_def]>>
    drule fml_rel_check_spec_list>>
    impl_tac >- metis_tac[]>>
    strip_tac>>
    drule check_spec_list_LENGTH>>
    strip_tac>>
    gvs[]>>
    metis_tac[bound_mono])
  >~ [‘Obj’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,
      check_obj_core_thm,check_obj_slots_thm]>>
    drule_all core_fmlls_mk_core_fml>>strip_tac>>
    drule check_obj_cong>>rw[]>>fs[]>>
    drule_all ind_rel_reindex>>strip_tac>>
    rpt (pairarg_tac>>gvs[])>>
    gvs[enc_mv_enc,store_ind_enc,opt_update_SOME]>>
    drule_all store_rels>>
    simp[])
  >~ [‘ChangeObj’] >- (
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
    `id ≤ id` by fs[]>>
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
    CONJ_TAC >- metis_tac[rup_inv_rollback]>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >-
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    CONJ_TAC >- fs[]>>
    CONJ_TAC >-
      metis_tac[vomap_rel_mk_vomap]>>
    simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    rw[])
  >~ [‘CheckObj’] >- (
    gvs[check_cstep_def,check_cstep_list_def,AllCaseEqs()])
  >~ [‘AssertObj’] >- (
    gvs[check_cstep_def,check_cstep_list_def]>>
    rpt (pairarg_tac>>gvs[])>>
    gvs[enc_mv_enc,store_ind_enc,opt_update_SOME]>>
    drule_all store_rels>>
    simp[])
  >~ [‘ChangePres’] >- (
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
    `id ≤ id` by fs[]>>
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
    CONJ_TAC >- metis_tac[rup_inv_rollback]>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >-
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    simp[rollback_list_delete,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    rw[])
  >~ [‘CheckPres’] >- (
    gvs[check_cstep_def,check_cstep_list_def,AllCaseEqs()])
  >~ [‘Sol’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,
      check_sol_core_thm,check_sol_slots_thm]>>
    drule_all core_fmlls_mk_core_fml>>strip_tac>>
    drule check_sol_cong>>rw[]>>fs[]>>
    drule_all ind_rel_reindex>>strip_tac>>
    rpt (pairarg_tac>>gvs[])>>
    gvs[enc_mv_enc,store_ind_enc,opt_update_SOME]>>
    drule_all store_rels>>
    simp[])
QED

Theorem store_ind_id:
  store_ind fmlls s mv id inds assg st =
    (fmlls',inds',id',assg',st') ⇒
  id ≤ id'
Proof
  rw[store_ind_def,store_slot_def]>>
  rpt (pairarg_tac>>gvs[])
QED

Theorem check_red_list_id:
  check_red_list pres ord po obj b tcb fmlls inds id fc mv s pfs idopt
    vimap vomap assg st ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ⇒
  id ≤ id'
Proof
  strip_tac>>
  gvs[check_red_list_def,check_red_list_fast_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  gvs[store_slot_def]>>
  rpt (pairarg_tac>>gvs[])
  >- (
    drule check_scopes_list_id>>
    simp[])>>
  drule (CONJUNCT2 check_lstep_list_id)>>
  simp[]
QED

Theorem check_change_obj_list_id:
  check_change_obj_list b fmlls id obj fc' pfs assg st =
    SOME (fmlls',fc'',id',assg',st') ⇒
  id ≤ id'
Proof
  rw[check_change_obj_list_def,AllCaseEqs()]>>
  drule check_subproofs_list_id>>
  simp[]
QED

Theorem check_change_pres_list_id:
  check_change_pres_list b fmlls id pres v c pfs assg st =
    SOME (fmlls',pres',id',assg',st') ⇒
  id ≤ id'
Proof
  rw[check_change_pres_list_def,AllCaseEqs()]>>
  drule check_subproofs_list_id>>
  simp[]
QED

Theorem check_sstep_list_id:
  check_sstep_list sstep pres ord po obj tcb fmlls inds id vimap vomap assg st
    ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ⇒
  id ≤ id'
Proof
  strip_tac>>
  gvs[check_sstep_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[])
  >- (
    imp_res_tac opt_update_inds_opt_update>>
    imp_res_tac opt_update_id>>
    imp_res_tac (CONJUNCT1 check_lstep_list_id)>>
    simp[])>>
  gvs[AllCaseEqs()]>>
  pairarg_tac>>gvs[]>>
  imp_res_tac store_ind_id>>
  imp_res_tac check_red_list_id>>
  simp[]
QED

(* ids below id are unchanged *)
Theorem store_ind_mindel:
  store_ind fmlls s mv id inds assg st =
    (fmlls',inds',id',assg',st') ∧
  n < id ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
Proof
  rw[store_ind_def,store_slot_def]>>
  rpt (pairarg_tac>>gvs[])>>
  rw[any_el_update_resize]
QED

Theorem check_red_list_mindel:
  check_red_list pres ord po obj b tcb fmlls inds id fc mv s pfs idopt
    vimap vomap assg st ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ∧
  n < id ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
Proof
  strip_tac>>
  gvs[check_red_list_def,check_red_list_fast_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])>>
  gvs[store_slot_def]>>
  rpt (pairarg_tac>>gvs[])
  >- (
    drule check_scopes_list_mindel>>
    drule check_scopes_list_id>>
    rw[any_el_rollback]>>
    first_x_assum (qspec_then`n` mp_tac)>>
    simp[any_el_update_resize])>>
  drule (CONJUNCT2 check_lstep_list_mindel)>>
  drule (CONJUNCT2 check_lstep_list_id)>>
  rw[any_el_rollback]>>
  first_x_assum (qspec_then`n` mp_tac)>>
  simp[any_el_update_resize]
QED

Theorem check_change_obj_list_mindel:
  check_change_obj_list b fmlls id obj fc' pfs assg st =
    SOME (fmlls',fc'',id',assg',st') ∧
  n < id ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
Proof
  rw[check_change_obj_list_def,AllCaseEqs()]>>
  drule check_subproofs_list_mindel>>
  drule check_subproofs_list_id>>
  rw[any_el_rollback]
QED

Theorem check_change_pres_list_mindel:
  check_change_pres_list b fmlls id pres v c pfs assg st =
    SOME (fmlls',pres',id',assg',st') ∧
  n < id ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
Proof
  rw[check_change_pres_list_def,AllCaseEqs()]>>
  drule check_subproofs_list_mindel>>
  drule check_subproofs_list_id>>
  rw[any_el_rollback]
QED

(* ids below id are only deleted *)
Theorem check_sstep_list_id_del:
  check_sstep_list sstep pres ord po obj tcb fmlls inds id vimap vomap assg st
    ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ∧
  n < id ∧
  any_el n fmlls' Empty ≠ Empty ⇒
  any_el n fmlls Empty = any_el n fmlls' Empty
Proof
  strip_tac>>
  gvs[check_sstep_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[])
  >- (
    qmatch_asmsub_rename_tac`opt_update_inds _ _ id1 _ _ _ = _`>>
    imp_res_tac opt_update_inds_opt_update>>
    drule (CONJUNCT1 check_lstep_list_id)>>
    strip_tac>>
    `n < id1` by decide_tac>>
    metis_tac[opt_update_mindel,check_lstep_list_id_del])>>
  gvs[AllCaseEqs()]>>
  pairarg_tac>>gvs[]>>
  qmatch_asmsub_rename_tac`store_ind _ _ _ id1 _ _ _ = _`>>
  drule check_red_list_id>>
  strip_tac>>
  `n < id1` by decide_tac>>
  metis_tac[check_red_list_mindel,store_ind_mindel]
QED

Theorem core_below_check_cstep_list:
  core_below cw fmlls ∧ cw ≤ id ∧
  check_cstep_list cstep fmlls assg st inds vimap id (pc,vomap,cw,po) ht =
    SOME (fmlls',assg',st',inds',vimap',id',(pc',vomap',cw',po'),ht') ⇒
  core_below cw' fmlls' ∧ cw' ≤ id'
Proof
  Cases_on`cstep`>>
  strip_tac>>
  gvs[check_cstep_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[AllCaseEqs()])
  >~ [`check_scopes_list`] >- (
    qmatch_asmsub_rename_tac`check_scopes_list _ _ _ _ _ _ _ = SOME (_,id2,_,_)`>>
    drule store_ind_mindel>>
    drule store_ind_id>>
    drule check_scopes_list_mindel>>
    drule check_scopes_list_id>>
    gvs[store_slot_def]>>
    rpt (pairarg_tac>>gvs[])>>
    rw[]>>
    irule core_below_frame>>
    first_assum (irule_at Any)>>
    rw[]>>
    `n < id ∧ n < id2` by decide_tac>>
    qpat_x_assum`∀n. n < id2 ⇒ _` (qspec_then`n` mp_tac)>>
    qpat_x_assum`∀n. n < id ⇒ _` (qspec_then`n` mp_tac)>>
    simp[any_el_rollback,any_el_update_resize])
  >~ [`check_sstep_list`] >- (
    drule check_sstep_list_id_del>>
    drule check_sstep_list_id>>
    rw[]>>
    irule core_below_frame>>
    first_assum (irule_at Any)>>
    rw[])
  >~ [`check_red_list`] >- (
    qmatch_asmsub_rename_tac`lookup_core_only_list T fmlls del`>>
    drule check_red_list_mindel>>
    drule check_red_list_id>>
    rw[]>>
    irule core_below_frame>>
    first_assum (irule_at Any)>>
    rw[]>>
    rename1`m < cw`>>
    `m < id` by decide_tac>>
    `delete_list del fmlls = list_delete_list [del] fmlls` by
      simp[list_delete_list_def]>>
    gvs[any_el_list_delete_list]>>
    qpat_x_assum`∀n. n < id ⇒ _` (qspec_then`m` mp_tac)>>
    rw[])
  >>~- ([`list_delete_list`],
    irule core_below_frame>>
    first_assum (irule_at Any)>>
    rw[any_el_list_delete_list])
  >~ [`core_from_inds`] >- metis_tac[core_below_core_from_inds]
  >>~- ([`core_from_range`], metis_tac[core_below_core_from_range])>>
  imp_res_tac store_ind_mindel>>
  imp_res_tac store_ind_id>>
  imp_res_tac check_change_obj_list_mindel>>
  imp_res_tac check_change_obj_list_id>>
  imp_res_tac check_change_pres_list_mindel>>
  imp_res_tac check_change_pres_list_id>>
  rw[]>>
  irule core_below_frame>>
  first_assum (irule_at Any)>>
  rw[]
QED

Definition check_csteps_list_def:
  (check_csteps_list [] fml assg st inds vimap id cfg ht =
    SOME (fml, assg, st, inds, vimap, id, cfg, ht)) ∧
  (check_csteps_list (c::cs) fml assg st inds vimap id cfg ht =
    case check_cstep_list c fml assg st inds vimap id cfg ht of
      NONE => NONE
    | SOME(fml', assg', st', inds', vimap', id', cfg', ht') =>
      check_csteps_list cs fml' assg' st' inds' vimap' id' cfg' ht')
End

Theorem fml_rel_check_csteps_list:
  ∀csteps fml fmlls assg st inds vimap id pc vomap cw po ht
    fmlls' assg' st' inds' vimap' id' pc' vomap' cw' po' ht'.
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  vomap_rel pc.obj vomap ∧ po_rel pc.ord po ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  core_below cw fmlls ∧ cw ≤ id ∧
  check_csteps_list csteps fmlls assg st inds vimap id (pc,vomap,cw,po) ht =
    SOME (fmlls', assg', st', inds', vimap', id', (pc',vomap',cw',po'), ht') ⇒
  ∃fml'.
    check_csteps csteps fml id pc = SOME (fml', id', pc') ∧
    fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧ FST (SND vimap') ≤ id' ∧
    vomap_rel pc'.obj vomap' ∧ po_rel pc'.ord po' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
    id ≤ id'
Proof
  Induct>>simp[]
  >- (
    rw[check_csteps_list_def,check_csteps_def]>>
    metis_tac[])>>
  rw[]>>
  gvs[check_csteps_list_def,check_csteps_def,AllCaseEqs()]>>
  PairCases_on`cfg'`>>
  drule_all fml_rel_check_cstep_list>>
  drule_all core_below_check_cstep_list>>
  rw[]>>simp[]>>
  first_x_assum drule_all>>
  rw[]>>simp[]
QED

Theorem fml_bound_store_ind:
  fml_bound fmlls (LENGTH assg) ∧ slot_bound s (mv + 1) ∧
  store_ind fmlls s mv id inds assg st =
    (fmlls',inds',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  strip_tac>>
  gvs[store_ind_def]>>
  pairarg_tac>>gvs[]>>
  drule_all fml_bound_store_slot>>
  simp[]
QED

Theorem fml_bound_opt_update_inds:
  fml_bound fmlls (LENGTH assg) ∧
  opt_update_inds fmlls c id inds assg st =
    (fmlls',inds',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  Cases_on`c`
  >- (rw[opt_update_inds_def]>>gvs[opt_update_inds_def])>>
  rename1`SOME cb`>>
  Cases_on`cb`>>
  rpt strip_tac>>
  gvs[opt_update_inds_def,enc_mv_enc]>>
  drule_at (Pos last) fml_bound_store_ind>>
  simp[slot_bound_enc_max_var]
QED

Theorem fml_bound_check_sstep_list:
  fml_bound fmlls (LENGTH assg) ∧ po = mk_ord_pre ord ∧
  check_sstep_list sstep pres ord po obj tcb fmlls inds id vimap vomap assg st
    ht =
    SOME (fmlls',inds',vimap',id',assg',st',ht') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  strip_tac>>
  gvs[check_sstep_list_def,AllCaseEqs()]
  >- (
    pairarg_tac>>gvs[]>>
    drule_all (CONJUNCT1 fml_bound_check_lstep_list)>>
    strip_tac>>
    drule_all fml_bound_opt_update_inds>>
    simp[])>>
  pairarg_tac>>gvs[AllCaseEqs(),enc_mv_enc]>>
  pairarg_tac>>gvs[]>>
  drule_at (Pos last) fml_bound_check_red_list>>
  simp[slot_bound_enc_max_var]>>
  strip_tac>>
  drule_at (Pos last) fml_bound_store_ind>>
  simp[slot_bound_enc_max_var]
QED

Theorem fml_bound_check_change_obj_list:
  fml_bound fmlls (LENGTH assg) ∧
  check_change_obj_list b fmlls id obj fc' pfs assg st =
    SOME (fmlls',fc'',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  rw[check_change_obj_list_def,AllCaseEqs()]>>
  imp_res_tac fml_bound_check_subproofs_list>>
  simp[bound_rollback]
QED

Theorem fml_bound_check_change_pres_list:
  fml_bound fmlls (LENGTH assg) ∧
  check_change_pres_list b fmlls id pres v c pfs assg st =
    SOME (fmlls',pres',id',assg',st') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st')
Proof
  rw[check_change_pres_list_def,AllCaseEqs()]>>
  imp_res_tac fml_bound_check_subproofs_list>>
  simp[bound_rollback]
QED

Theorem fml_bound_core_from_inds:
  ∀l fmlls fmlls'.
  fml_bound fmlls n ∧
  core_from_inds fmlls l = SOME fmlls' ⇒
  fml_bound fmlls' n
Proof
  Induct>>
  rw[core_from_inds_def]>>
  gvs[AllCaseEqs()]>>
  last_x_assum irule>>
  pop_assum (irule_at Any)>>
  irule bound_update_resize>>
  gvs[fml_bound_def]
QED

Theorem fml_bound_core_from_range:
  fml_bound fmlls n ⇒
  fml_bound (core_from_range fmlls w id) n
Proof
  rw[fml_bound_def,any_el_core_from_range]>>
  rw[]
QED

Theorem fml_bound_check_cstep_list:
  fml_bound fmlls (LENGTH assg) ∧ po = mk_ord_pre pc.ord ∧
  check_cstep_list cstep fmlls assg st inds vimap id (pc,vomap,cw,po) ht =
    SOME (fmlls',assg',st',inds',vimap',id',(pc',vomap',cw',po'),ht') ⇒
  fml_bound fmlls' (LENGTH assg') ∧ LENGTH assg ≤ LENGTH assg' ∧
  (stamps_ok assg st ⇒ stamps_ok assg' st') ∧
  po' = mk_ord_pre pc'.ord
Proof
  Cases_on`cstep`>>
  strip_tac>>
  gvs[check_cstep_list_def,AllCaseEqs()]>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs(),neg_pos_slot_enc,enc_mv_enc]>>
  rpt (pairarg_tac>>gvs[])
  >~ [`dom_subgoals_list`] >- (
    `slot_bound (enc (not p) F) (max_var (FST p) + 1)` by
      metis_tac[slot_bound_enc_max_var,max_var_not]>>
    drule_at (Pos last) dom_subgoals_list_scopes_ok>>
    simp[]>>strip_tac>>
    drule_all scopes_ok_extract_scopes_list>>strip_tac>>
    drule_all fml_bound_store_slot>>
    strip_tac>>
    drule_all fml_bound_check_scopes_list>>
    strip_tac>>
    drule_at (Pos last) fml_bound_store_ind>>
    gvs[bound_rollback,slot_bound_enc_max_var])
  >~ [`check_sstep_list`] >- (
    drule_at (Pos last) fml_bound_check_sstep_list>>
    simp[])
  >~ [`check_red_list`] >- (
    drule_at (Pos last) fml_bound_check_red_list>>
    disch_then irule>>
    simp[slot_bound_slot_max_var]>>
    metis_tac[bound_list_delete_list,list_delete_list_def])
  >~ [`check_storeorder`] >- (
    gvs[check_storeorder_def,AllCaseEqs()]>>
    drule check_spec_list_LENGTH>>
    metis_tac[bound_mono])>>
  imp_res_tac fml_bound_core_from_inds>>
  imp_res_tac fml_bound_check_change_obj_list>>
  imp_res_tac fml_bound_check_change_pres_list>>
  gvs[bound_list_delete_list,fml_bound_core_from_range,mk_ord_pre_def]>>
  drule_at (Pos last) fml_bound_store_ind>>
  gvs[slot_bound_enc_max_var]
QED

Definition check_implies_fml_list_def:
  check_implies_fml_list fml n c =
  (case any_el n fml Empty of
      Empty => F
    | s => imp_slot s c)
End

Definition check_sat_def:
  check_sat fmls obj bound' wopt =
  case wopt of
    NONE => bound' ≠ NONE
  | SOME wm =>
    case check_obj_slots obj wm fmls NONE of NONE => F
    | _ => T
End

Definition check_ub_def:
  check_ub fmls obj bound' ubi wopt =
    case wopt of
      NONE => opt_le bound' ubi
    | SOME wm =>
      opt_le (OPTION_MAP FST (check_obj_slots obj wm fmls NONE)) ubi
End

Definition check_hconcl_list_def:
  (check_hconcl_list fml obj fml' obj' bound' dbound' enum
    HNoConcl = T) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound' enum
    (HDSat wopt) =
    check_sat fml obj bound' wopt) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound' enum
    (HDUnsat n) =
    (dbound' = NONE ∧
      check_contradiction_fml_list F fml' n)) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound' enum
    (HOBounds lbi ubi n wopt) =
    (
    (opt_le lbi dbound' ∧
    case lbi of
      NONE => check_contradiction_fml_list F fml' n
    | SOME lb => check_implies_fml_list fml' n (lower_bound obj' lb)) ∧
    check_ub fml obj bound' ubi wopt)) ∧
  (check_hconcl_list fml obj fml' obj' bound' dbound' enum
    (HEEnum n complete hint) =
    (
    obj = NONE ∧
    (* Number of solutions claimed must be at most enumerated *)
    n = enum ∧
    (* And if complete enumeration is claimed, formula must be hinted *)
    (complete ⇒
      case hint of NONE => F
      | SOME i => check_contradiction_fml_list F fml' i)))
End

Theorem fml_rel_check_implies_fml:
  fml_rel fml fmlls ∧
  check_implies_fml_list fmlls n c ⇒
  check_implies_fml fml n c
Proof
  rw[check_implies_fml_def]>>
  `any_el n fmlls Empty ≠ Empty ∧ imp_slot (any_el n fmlls Empty) c` by (
    qpat_x_assum`check_implies_fml_list _ _ _` mp_tac>>
    simp[check_implies_fml_list_def]>>
    Cases_on`any_el n fmlls Empty`>>simp[])>>
  drule_all fml_rel_any_el>>
  rw[]>>
  gvs[imp_slot_enc]
QED

Theorem fml_rel_check_hconcl_list:
  fml_rel fml' fmlls' ∧
  check_hconcl_list (MAP (λc. enc c T) fml) obj fmlls'
    obj' bound' dbound' enum hconcl ⇒
  check_hconcl fml obj fml'
    obj' bound' dbound' enum hconcl
Proof
  Cases_on`hconcl`>>
  fs[check_hconcl_def,check_hconcl_list_def,check_sat_def,check_ub_def,
    check_obj_slots_thm,MAP_MAP_o,o_DEF]>>
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
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc d v i) x) (REPLICATE n d) ll)
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
  x < LENGTH (FOLDL (λacc (i,v). update_resize acc d v i) (REPLICATE n d) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). update_resize acc d v i) (REPLICATE n d) ls)
  =
  case ALOOKUP ls x of NONE => d | SOME v => v
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

Theorem any_el_FOLDL_update_resize:
  ALL_DISTINCT (MAP FST ls) ⇒
  any_el x (FOLDL (λacc (i,v). update_resize acc d v i) (REPLICATE n d) ls) d =
  case ALOOKUP ls x of NONE => d | SOME v => v
Proof
  rw[any_el_ALT]
  >- simp[FOLDL_update_resize_lookup]>>
  Cases_on`ALOOKUP ls x`>>simp[]>>
  drule ALOOKUP_MEM>>
  strip_tac>>
  gvs[FOLDL_FOLDR_REVERSE]>>
  `MEM (x,x') (REVERSE ls)` by simp[MEM_REVERSE]>>
  drule LENGTH_FOLDR_update_resize2>>
  disch_then (qspecl_then [`n`,`d`] mp_tac)>>
  simp[]
QED

Theorem ALOOKUP_enumerate_MAP:
  ALOOKUP (enumerate k (MAP f ls)) x =
  OPTION_MAP f (ALOOKUP (enumerate k ls) x)
Proof
  rw[ALOOKUP_enumerate,EL_MAP]
QED

Theorem fml_rel_FOLDL_update_resize:
  fml_rel (build_fml T k fml)
  (FOLDL (λacc (i,v). update_resize acc Empty v i) (REPLICATE n Empty)
    (enumerate k (MAP (λc. enc c T) fml)))
Proof
  rw[fml_rel_def]>>
  DEP_REWRITE_TAC[any_el_FOLDL_update_resize]>>
  simp[ALL_DISTINCT_MAP_FST_enumerate,ALOOKUP_enumerate_MAP,
    lookup_build_fml,ALOOKUP_enumerate]>>
  rw[enc_opt_def]
QED

Theorem ind_rel_FOLDL_update_resize:
  ind_rel
  (FOLDL (λacc (i,v). update_resize acc Empty v i) (REPLICATE n Empty) (enumerate k fmls))
  (REVERSE (MAP FST (enumerate k fmls)))
Proof
  rw[ind_rel_def]>>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[any_el_FOLDL_update_resize]>>
  simp[ALL_DISTINCT_MAP_FST_enumerate]>>
  Cases_on`ALOOKUP (enumerate k fmls) x`>>simp[]>>
  drule ALOOKUP_MEM>>
  rw[MEM_MAP]>>
  metis_tac[FST]
QED

Theorem bound_FOLDL_update_resize:
  EVERY (λs. slot_bound s m) fmls ⇒
  fml_bound
  (FOLDL (λacc (i,v). update_resize acc Empty v i) (REPLICATE n Empty) (enumerate k fmls))
  m
Proof
  rw[fml_bound_def]>>
  DEP_REWRITE_TAC[any_el_FOLDL_update_resize]>>
  simp[ALL_DISTINCT_MAP_FST_enumerate]>>
  Cases_on`ALOOKUP (enumerate k fmls) x`>>
  simp[slot_bound_def]>>
  drule ALOOKUP_MEM>>
  rw[]>>
  drule MEM_enumerate_IMP>>
  gvs[EVERY_MEM]
QED

Theorem FOLDL_enumerate_MAP:
  FOLDL (λacc (i,v). g acc i v) a (enumerate k (MAP f ls)) =
  FOLDL (λacc (i,v). g acc i (f v)) a (enumerate k ls)
Proof
  qid_spec_tac`k`>>
  qid_spec_tac`a`>>
  Induct_on`ls`>>
  simp[miscTheory.enumerate_def]
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
  (mk_vomap_opt NONE = «») ∧
  (mk_vomap_opt (SOME fc) = mk_vomap (LENGTH (FST fc)) fc)
End

Theorem init_state_rels:
  fmls = MAP (λc. enc c T) fml ∧
  EVERY (λs. slot_bound s (LENGTH assg)) fmls ∧
  (∃dm. dm_rel dm assg st) ∧
  fmlls = FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE m Empty) (enumerate 1 fmls) ∧
  inds = REVERSE (MAP FST (enumerate 1 fmls)) ∧
  vimap = (LENGTH fml, 0, ents) ∧
  vomap = mk_vomap_opt obj ∧
  id = LENGTH fml + 1 ∧
  pc = init_conf chk pres obj ⇒
  fml_rel (build_fml T 1 fml) fmlls ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧
  vomap_rel pc.obj vomap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  rup_inv fmlls assg st ∧
  id_ok (build_fml T 1 fml) id ∧
  all_core (build_fml T 1 fml)
Proof
  strip_tac>>
  gvs[]>>
  rpt conj_tac
  >- simp[fml_rel_FOLDL_update_resize]
  >- simp[ind_rel_FOLDL_update_resize]
  >- simp[vimap_rel_def]
  >- (
    simp[init_conf_def]>>
    Cases_on`obj`>- EVAL_TAC>>
    metis_tac[vomap_rel_mk_vomap,mk_vomap_opt_def])
  >- (
    rw[init_conf_def]>>
    DEP_REWRITE_TAC[any_el_FOLDL_update_resize]>>
    simp[ALOOKUP_enumerate,ALL_DISTINCT_MAP_FST_enumerate])
  >- (
    rw[rup_inv_def]
    >- simp[bound_FOLDL_update_resize]>>
    metis_tac[])
  >- fs[init_conf_def,id_ok_def,domain_build_fml]>>
  fs[all_core_def,EVERY_MEM,MEM_toAList,FORALL_PROD,lookup_build_fml]
QED

Theorem check_csteps_list_concl:
  fmls = MAP (λc. enc c T) fml ∧
  EVERY (λs. slot_bound s (LENGTH assg)) fmls ∧
  (∃dm. dm_rel dm assg st) ∧
  check_csteps_list cs
    (FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE m Empty) (enumerate 1 fmls))
    assg st
    (REVERSE (MAP FST (enumerate 1 fmls)))
    (LENGTH fml, 0, ents)
    (LENGTH fml + 1)
    (init_conf chk pres obj, mk_vomap_opt obj, 0, NONE) ht =
    SOME(fmlls',assg',st',inds',vimap',id',(pc',vomap',cw',po'),ht') ∧
  check_hconcl_list fmls obj fmlls'
    pc'.obj pc'.bound pc'.dbound pc'.enum hconcl ⇒
  sem_concl (set fml) obj (pres_set_spt pres) (hconcl_concl hconcl)
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`check_csteps_list cs fmlls assg st
    inds vimap id (pc,vomap,_) _ = _`>>
  `fml_rel (build_fml T 1 fml) fmlls ∧ ind_rel fmlls inds ∧
   vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧ vomap_rel pc.obj vomap ∧
   (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
   rup_inv fmlls assg st ∧
   id_ok (build_fml T 1 fml) id ∧ all_core (build_fml T 1 fml)` by (
    irule init_state_rels>>
    simp[Abbr`fmlls`,Abbr`inds`,Abbr`vimap`,Abbr`vomap`,Abbr`pc`,Abbr`id`]>>
    metis_tac[])>>
  `core_below 0 fmlls ∧ 0 ≤ id` by simp[]>>
  `po_rel pc.ord NONE` by
    simp[Abbr`pc`,init_conf_def,po_rel_def,mk_ord_pre_def]>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  drule check_csteps_check_hconcl>>
  rpt(disch_then drule)>>
  disch_then match_mp_tac>>simp[core_only_fml_build_fml]>>
  drule_all fml_rel_check_hconcl_list>>
  fs[Abbr`pc`,init_conf_def]>>
  metis_tac[]
QED

(* The table is filled up to the id counter id; each output slot must match
  a core slot in it (the output is in the core), and every core slot below
  id must be marked by a matching output slot (the core is in the output) *)
Definition check_output_list_def:
  (check_output_list fml inds id ht
    pres obj bound dbound chk fml' pres' obj' NoOutput = T) ∧
  (check_output_list fml inds id ht
    pres obj bound dbound chk fml' pres' obj' Derivable =
    let (hw,a,d,bks) = ht_fill fml inds id ht in
      dbound = NONE ∧ ht_include fml bks fml') ∧
  (check_output_list fml inds id ht
    pres obj bound dbound chk fml' pres' obj' Equisatisfiable =
    let (hw,a,d,bks) = ht_fill fml inds id ht in
      dbound = NONE ∧ bound = NONE ∧
      chk ∧
      ht_include fml bks fml' ∧
      all_marked fml (ht_marks fml bks fml' (REPLICATE id F)) id) ∧
  (check_output_list fml inds id ht
    pres obj bound dbound chk fml' pres' obj' Equioptimal =
    let (hw,a,d,bks) = ht_fill fml inds id ht in
      chk ∧ opt_le bound dbound ∧
      ht_include fml bks fml' ∧
      all_marked fml (ht_marks fml bks fml' (REPLICATE id F)) id ∧
      opt_eq_obj obj obj') ∧
  (check_output_list fml inds id ht
    pres obj bound dbound chk fml' pres' obj' Equisolvable =
    let (hw,a,d,bks) = ht_fill fml inds id ht in
      chk ∧ opt_le bound dbound ∧
      ht_include fml bks fml' ∧
      all_marked fml (ht_marks fml bks fml' (REPLICATE id F)) id ∧
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

(* Output check against the table *)

Theorem LENGTH_ht_mark:
  ∀fmlls c tbl j fuel mk. LENGTH (ht_mark fmlls c tbl j fuel mk) = LENGTH mk
Proof
  ho_match_mp_tac ht_mark_ind>>
  rw[]>>
  rw[Once ht_mark_def]>>
  TOP_CASE_TAC>>
  rw[]
QED

Theorem EL_ht_mark:
  ∀fmlls c tbl j fuel mk k.
  k < LENGTH mk ∧ EL k (ht_mark fmlls c tbl j fuel mk) ⇒
  EL k mk ∨
  (lookup_core_only_list T fmlls k ≠ Empty ∧
    eq_slot c (lookup_core_only_list T fmlls k))
Proof
  ho_match_mp_tac ht_mark_ind>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  simp[Once ht_mark_def]>>
  rw[]>>
  gvs[]>>
  first_x_assum (drule_at (Pos last))>>
  rw[EL_LUPDATE]>>
  gvs[eq_stored_thm]
QED

Theorem LENGTH_ht_marks:
  ∀cs mk. LENGTH (ht_marks fmlls tbl cs mk) = LENGTH mk
Proof
  Induct>>
  rw[ht_marks_def,LENGTH_ht_mark]
QED

Theorem EL_ht_marks:
  ∀cs mk j.
  j < LENGTH mk ∧ EL j (ht_marks fmlls tbl cs mk) ⇒
  EL j mk ∨
  ∃c. MEM c cs ∧ lookup_core_only_list T fmlls j ≠ Empty ∧
    eq_slot c (lookup_core_only_list T fmlls j)
Proof
  Induct>>
  rw[ht_marks_def]>>
  first_x_assum (drule_at (Pos last))>>
  simp[LENGTH_ht_mark]>>
  strip_tac
  >- (
    drule_at (Pos last) EL_ht_mark>>
    rw[]>>
    metis_tac[])>>
  metis_tac[]
QED

Theorem all_marked_EL:
  ∀n j.
  all_marked fmlls mk n ∧ j < n ∧
  lookup_core_only_list T fmlls j ≠ Empty ⇒
  EL j mk
Proof
  Induct>>
  rw[Once all_marked_def]>>
  Cases_on`j = n`>>
  gvs[]
QED

(* The output constraints are core constraints of the formula *)
Theorem ht_include_fml_include:
  fml_rel fml fmlls ∧
  ht_include fmlls tbl fmlt ⇒
  fml_include (MAP SND (toAList (mk_core_fml T fml))) fmlt
Proof
  rw[ht_include_def,fml_include_def,EVERY_MEM,ht_probe_def]>>
  first_x_assum drule>>
  strip_tac>>
  drule_all ht_mem_core_only_fml>>
  rw[GSYM range_mk_core_fml,range_def,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
  Cases_on`c`>>
  metis_tac[]
QED

(* Every core constraint of the formula is an output constraint *)
Theorem all_marked_fml_include:
  fml_rel fml fmlls ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  all_marked fmlls (ht_marks fmlls tbl fmlt (REPLICATE id F)) id ⇒
  fml_include fmlt (MAP SND (toAList (mk_core_fml T fml)))
Proof
  rw[fml_include_def,EVERY_MAP,EVERY_MEM,MEM_MAP,FORALL_PROD,MEM_toAList,
    lookup_mk_core_fml]>>
  rename1`lookup_core_only T fml n = SOME c`>>
  drule_all (cj 2 fml_rel_lookup_core_only_list)>>
  strip_tac>>
  `n < id` by (
    CCONTR_TAC>>
    gvs[lookup_core_only_list_def,core_only_def,NOT_LESS,GREATER_EQ]>>
    first_x_assum drule>>
    strip_tac>>
    gvs[core_slot_def])>>
  drule all_marked_EL>>
  disch_then (qspec_then`n` mp_tac)>>
  gvs[]>>
  strip_tac>>
  drule_at (Pos last) EL_ht_marks>>
  simp[LENGTH_REPLICATE,EL_REPLICATE]>>
  strip_tac>>
  gvs[eq_slot_enc]
QED

Theorem fml_rel_check_output_list:
  fml_rel fml' fmlls' ∧
  (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
  check_output_list fmlls' inds' id' ht' pres obj bound dbound chk
    fmlt prest objt output ⇒
  check_output fml' pres obj bound dbound chk fmlt prest objt output
Proof
  rw[]>>
  Cases_on`output`>>
  gvs[check_output_list_def,check_output_def]>>
  pairarg_tac>>
  gvs[]>>
  metis_tac[ht_include_fml_include,all_marked_fml_include]
QED

Theorem check_csteps_list_output:
  fmls = MAP (λc. enc c T) fml ∧
  EVERY (λs. slot_bound s (LENGTH assg)) fmls ∧
  (∃dm. dm_rel dm assg st) ∧
  check_csteps_list cs
    (FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE m Empty) (enumerate 1 fmls))
    assg st
    (REVERSE (MAP FST (enumerate 1 fmls)))
    (LENGTH fml, 0, ents)
    (LENGTH fml + 1)
    (init_conf chk pres obj, mk_vomap_opt obj, 0, NONE) ht =
    SOME(fmlls',assg',st',inds',vimap',id',(pc',vomap',cw',po'),ht') ∧
  check_output_list fmlls' inds' id' ht'
    pc'.pres pc'.obj pc'.bound pc'.dbound pc'.chk fmlt prest objt output ⇒
  sem_output (set fml) obj (pres_set_spt pres) pc'.bound (set fmlt) objt (pres_set_spt prest) output
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`check_csteps_list cs fmlls assg st
    inds vimap id (pc,vomap,_) _ = _`>>
  `fml_rel (build_fml T 1 fml) fmlls ∧ ind_rel fmlls inds ∧
   vimap_rel fmlls vimap ∧ FST (SND vimap) ≤ id ∧ vomap_rel pc.obj vomap ∧
   (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
   rup_inv fmlls assg st ∧
   id_ok (build_fml T 1 fml) id ∧ all_core (build_fml T 1 fml)` by (
    irule init_state_rels>>
    simp[Abbr`fmlls`,Abbr`inds`,Abbr`vimap`,Abbr`vomap`,Abbr`pc`,Abbr`id`]>>
    metis_tac[])>>
  `core_below 0 fmlls ∧ 0 ≤ id` by simp[]>>
  `po_rel pc.ord NONE` by
    simp[Abbr`pc`,init_conf_def,po_rel_def,mk_ord_pre_def]>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  drule check_csteps_check_output>>
  fs[Abbr`pc`]>>
  gvs[init_conf_def]>>
  rpt(disch_then drule)>>
  simp[core_only_fml_build_fml]>>
  disch_then match_mp_tac>>
  drule_all fml_rel_check_output_list>>
  metis_tac[]
QED
