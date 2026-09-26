(*
  Refine PB proof checker to use arrays
*)
Theory npbc_list
Ancestors
  npbc_check npbc_slot
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

(* returns the stored slot itself *)
Definition lookup_core_only_list_def:
  lookup_core_only_list b fml n =
  let s = any_el n fml Empty in
  case s of
    Empty => Empty
  | Stored cs vs d mc b' =>
    if ¬b ∨ b' then s
    else Empty
End

Theorem lookup_core_only_list_eq:
  lookup_core_only_list b fml n =
  case any_el n fml Empty of
    Empty => Empty
  | Stored cs vs d mc b' =>
    if ¬b ∨ b' then Stored cs vs d mc b'
    else Empty
Proof
  simp[lookup_core_only_list_def]>>
  every_case_tac>>simp[]
QED

Definition lookup_core_only_dec_def:
  lookup_core_only_dec b fml n =
  case lookup_core_only_list b fml n of
    Empty => NONE
  | s => SOME (dec s)
End

(* TODO: optimize this using arrays instead of lists
  alternative:
    collapse all adds into one big list before normalizing
*)
Definition check_cutting_list_def:
  (check_cutting_list b (fml: slot list) (Id n) =
    lookup_core_only_dec b fml n) ∧
  (check_cutting_list b fml (Add c1 c2) =
    OPTION_MAP2 add (check_cutting_list b fml c1) (check_cutting_list b fml c2)) ∧
  (check_cutting_list b fml (Mul c k) =
       OPTION_MAP (λc. multiply c k) (check_cutting_list b fml c)) ∧
  (check_cutting_list b fml (Div dty c k) =
    if k ≠ 0 then
      OPTION_MAP (λc. do_divide dty c k) (check_cutting_list b fml c)
    else NONE) ∧
  (check_cutting_list b fml (Minus c k) =
       OPTION_MAP (λc. minus c k) (check_cutting_list b fml c)) ∧
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
    (case check_cutting_list b fml (to_triv constr) of
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
    rw[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
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
    simp[any_el_update_resize,rollback_def,any_el_list_delete_list,MEM_MAP])
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
    gvs[any_el_update_resize,rollback_def,any_el_list_delete_list,MEM_MAP])
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
  rw[fml_rel_def,lookup_core_only_def,lookup_core_only_list_eq]>>
  first_x_assum (qspec_then`n` assume_tac)>>
  Cases_on`lookup n fml`>>
  gvs[enc_opt_def]>>
  rename1`lookup n fml = SOME p`>>
  PairCases_on`p`>>
  gvs[enc_opt_def,enc_def]>>
  rw[]>>
  simp[GSYM enc_def]
QED

Theorem fml_rel_lookup_core_only_enc:
  fml_rel fml fmlls ∧
  lookup_core_only_list b fmlls n ≠ Empty ⇒
  ∃c b'.
    lookup_core_only b fml n = SOME c ∧
    lookup_core_only_list b fmlls n = enc c b'
Proof
  rw[fml_rel_def,lookup_core_only_def,lookup_core_only_list_eq]>>
  first_x_assum (qspec_then`n` assume_tac)>>
  Cases_on`lookup n fml`>>
  gvs[enc_opt_def]>>
  rename1`lookup n fml = SOME p`>>
  PairCases_on`p`>>
  gvs[enc_opt_def,enc_def]>>
  Cases_on`¬b ∨ p2`>>
  gvs[]
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

Theorem slot_CASE_default:
  (case s of Empty => x | Stored cs vs d mc b => f (Stored cs vs d mc b)) =
  if s = Empty then x else f s
Proof
  Cases_on`s`>>simp[]
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

Theorem enc_eq_Stored:
  enc c b0 = Stored cs vs d mc b ⇔
  cs = Vector (MAP FST (FST c)) ∧ vs = Vector (MAP SND (FST c)) ∧
  d = SND c ∧ mc = max_coeff (FST c) ∧ b = b0
Proof
  PairCases_on`c`>>
  rw[enc_def]>>
  metis_tac[]
QED

Theorem fml_rel_lookup_core_only_dec:
  fml_rel fml fmlls ⇒
  lookup_core_only_dec b fmlls n = lookup_core_only b fml n
Proof
  rw[lookup_core_only_dec_def]>>
  drule fml_rel_lookup_core_only>>
  simp[]
QED

Theorem fml_rel_check_cutting:
  ∀p.
  fml_rel fml fmlls ⇒
  check_cutting_list b fmlls p = check_cutting b fml p
Proof
  Induct>>rw[check_cutting_list_def,check_cutting_def]>>
  drule fml_rel_lookup_core_only_dec>>
  simp[]
QED

Theorem fml_rel_rollback:
  fml_rel fml fmlls ∧
  (∀n. n < id ∨ n ≥ id' ⇒ any_el n fmlls Empty = any_el n fmlls' Empty) ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty)
  ⇒
  fml_rel fml (rollback fmlls' id id')
Proof
  rw[fml_rel_def,rollback_def]>>
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
  rw[rollback_def,bound_list_delete_list]
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
  rw[rollback_def,rup_inv_list_delete_list]
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
  rw[lookup_core_only_list_eq]>>
  Cases_on`any_el n fmlls Empty`>>
  rw[]
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
  `∃cs vs d mc cb. enc c b' = Stored cs vs d mc cb` by
    (Cases_on`enc c b'`>>gvs[])>>
  gvs[]>>
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
    simp[]
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
  `lookup_core_only_list b fmlls n ≠ Empty` by simp[]>>
  drule_all fml_rel_lookup_core_only_enc>>
  strip_tac>>
  `Stored v5 v6 v7 v8 v9 = enc c b'` by metis_tac[]>>
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
  `lookup_core_only_list b fmlls n ≠ Empty` by simp[]>>
  drule_all fml_rel_lookup_core_only_enc>>
  strip_tac>>
  `Stored v5 v6 v7 v8 v9 = enc c b'` by metis_tac[]>>
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

(* Inline subst fun *)
Definition subst_subst_fun_def:
  subst_subst_fun s c = subst_slot (subst_fun s) c
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
          Empty => NONE
        | c =>
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
    | SOME sc =>
    let (cid,cfml,assg,st) = list_insert_fml_list sc b id fml assg st in
    case check_subproofs_list pf b cfml id cid assg st of
      NONE => NONE
    | SOME (fml',id',assg',st') =>
        let rfml = rollback fml' id id' in
        check_scopes_list scpfs b rfml mindel id' assg' st')
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
  case any_el i fml Empty of
    Empty => reindex_aux fml is iacc
  | Stored cs vs d mc b' =>
    reindex_aux fml is (i::iacc))
End

Definition reindex_def:
  (reindex fml is = reindex_aux fml is [])
End

Definition revalue_aux_def:
  (revalue_aux b fml [] vacc = vacc) ∧
  (revalue_aux b fml (i::is) vacc =
  case lookup_core_only_list b fml i of
    Empty => revalue_aux b fml is vacc
  | s => revalue_aux b fml is (s::vacc))
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

Definition subst_indexes_def:
  (subst_indexes w b fml [] = []) ∧
  (subst_indexes w b fml (i::is) =
    case subst_opt_slot w (lookup_core_only_list b fml i) of
      NONE => subst_indexes w b fml is
    | SOME c => (i,c)::subst_indexes w b fml is)
End

(* Fast path for a special case corresponding to pbc
   --- enables faster checked deletion
   No scoping and no proofgoals used *)
Definition red_fast_def:
  red_fast s idopt pfs = (
    case idopt of
      NONE => NONE
    | SOME id =>(
      case (pfs:scope) of
      | [(NONE,[(NONE,pf)])] => SOME (pf,id)
      | [] => SOME ([],id)
      | _ => NONE))
End

(* inds is just passed through here *)
Definition check_red_list_fast_def:
  check_red_list_fast b fml inds id fc mv pf cid vimap assg st =
  let (fml_not_c,id1,assg,st) = store_slot fml (not_slot fc b) mv id assg st in
  case check_lsteps_list pf b fml_not_c id id1 assg st of
    NONE => NONE
  | SOME (fml', id',assg',st') =>
  if check_contradiction_fml_list b fml' cid then
    let rfml = rollback fml' id id' in
      SOME (rfml,inds,vimap,id',assg',st')
  else
    NONE
End

(* The fmlls argument should be delayed and avoided
  as much as possible *)
Definition split_goals_hash_def:
  split_goals_hash fmlls extra (proved:num_set)
    (goals:(num # (int # num) list # int) list) =
  let (lp,lf) =
    PARTITION (λ(i,c). lookup i proved ≠ NONE) goals in
  let lf = FILTER (λc. ¬imp_slot extra c) (MAP SND lf) in
  lf = [] ∨
  let proved = MAP (λ(i,c). enc c T) lp in
  let hs =
    mk_hashset_slot fmlls (mk_hashset_slot proved (REPLICATE splim [])) in
  EVERY (λc. in_hashset_slot c hs) lf
End

Theorem split_goals_hash_eq:
  split_goals_hash fmlls extra proved goals ⇔
  let (lp,lf) =
    PARTITION (λ(i,c). lookup i proved ≠ NONE) goals in
  let lf = FILTER (λc. ¬imp_slot extra c) (MAP SND lf) in
  let proved = MAP (λ(i,c). enc c T) lp in
  let hs =
    mk_hashset_slot fmlls (mk_hashset_slot proved (REPLICATE splim [])) in
  EVERY (λc. in_hashset_slot c hs) lf
Proof
  simp[split_goals_hash_def]>>
  pairarg_tac>>simp[]>>
  qmatch_goalsub_abbrev_tac`l = [] ∨ _`>>
  Cases_on`l`>>simp[]
QED

(* Not meant to be executed, mainly just abbrevation... *)
Definition do_red_check_def:
  do_red_check idopt b tcb fml inds
    s rfml rinds extra pfs rsubs skipped cond =
  case idopt of NONE =>
    let goals = subst_indexes (subst_fun s) (b ∨ tcb) rfml rinds in
    let (l,r) = extract_scoped_pids pfs LN LN in
    let fmlls = revalue b rfml inds in
      cond ∧
      split_goals_hash fmlls extra l goals ∧
      check_hash_goals_slot extra skipped r rsubs
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
  let c0 = subst_slot s def in
  ([not c0]::(MAP (λc. [not c]) fs) ++ cobj, [gs])
End

(* Per variable: the indices of the constraints where it occurs
  positively and negatively; Vcount also counts the insertions
  (tracking stops at ind_lim), Voverflow keeps no indices *)
Datatype:
  vent = Vnone
       | Vtrack (num list) (num list)
       | Vcount num (num list) (num list)
       | Voverflow
End

Type vimap_ty = ``:vent list``;

Definition vent_mem_def:
  (vent_mem Vnone pos i = F) ∧
  (vent_mem (Vtrack pinds ninds) pos i =
    MEM (i:num) (if pos then pinds else ninds)) ∧
  (vent_mem (Vcount k pinds ninds) pos i =
    MEM i (if pos then pinds else ninds)) ∧
  (vent_mem Voverflow pos i = T)
End

(* Useful for translation *)

(* TODO: a technical optimization we can do here
  is to stop checking after we hit n > x, because
  the constraints should be sorted *)
Definition cond_pos_acc_def:
  cond_pos_acc x cc i lacc =
    if cond_pos x cc then i::lacc
    else lacc
End

Definition cond_neg_acc_def:
  cond_neg_acc x cc i racc =
    if cond_neg x cc then i::racc
    else racc
End

Definition restore_aux_def:
  (restore_aux x fml [] lacc racc =
    (REVERSE lacc, REVERSE racc)) ∧
  (restore_aux x fml (i::is) lacc racc =
  case any_el i fml Empty of
    Empty => restore_aux x fml is lacc racc
  | s =>
    let (p,q) = restore_slot x s in
    restore_aux x fml is
      (if p then i::lacc else lacc)
      (if q then i::racc else racc))
End

Definition restore_def:
  (restore x fml is = restore_aux x fml is [] [])
End

Definition get_inds_rhs_def:
  get_inds_rhs rhs pinds ninds t =
  (case rhs of
    INL b =>
      list_insert (if b then ninds else pinds) t
  | _ => list_insert pinds (list_insert ninds t))
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

Definition check_get_inds_rhs_def:
  (check_get_inds_rhs vimap [] = T) ∧
  (check_get_inds_rhs vimap ((n,rhs)::xs) =
    (case any_el n vimap Vnone of
      Voverflow => F
    | _ => check_get_inds_rhs vimap xs))
End

Definition fold_get_inds_rhs_def:
  (fold_get_inds_rhs fml [] t vimap = (t,vimap)) ∧
  (fold_get_inds_rhs fml ((n,rhs)::xs) t vimap =
    (case any_el n vimap Vnone of
      Vnone => fold_get_inds_rhs fml xs t vimap
    | Vtrack pinds ninds =>
      let (pinds,ninds) = do_reindex_rhs fml rhs pinds ninds in
      let t = get_inds_rhs rhs pinds ninds t in
      fold_get_inds_rhs fml xs t
        (update_resize vimap Vnone (Vtrack pinds ninds) n)
    | Vcount k pinds ninds =>
      let (pinds,ninds) = do_reindex_rhs fml rhs pinds ninds in
      let t = get_inds_rhs rhs pinds ninds t in
      fold_get_inds_rhs fml xs t
        (update_resize vimap Vnone (Vtrack pinds ninds) n)
    | Voverflow => (t,vimap)))
End

(* (indices in goal, overall indices, vimap) *)
Definition get_set_indices_def:
  get_set_indices fml inds s (vimap:vimap_ty) =
  case s of
    [] => ([], inds ,vimap)
  | [(n,rhs)] =>
    (case any_el n vimap Vnone of
      Vnone => ([], inds, vimap)
    | Vtrack pinds ninds =>
      let (pinds,ninds) = do_reindex_rhs fml rhs pinds ninds in
      let t = get_inds_rhs rhs pinds ninds LN in
      let rinds = MAP FST (toAList t) in
      (rinds, inds,
        update_resize vimap Vnone (Vtrack pinds ninds) n)
    | Vcount k pinds ninds =>
      let (pinds,ninds) = do_reindex_rhs fml rhs pinds ninds in
      let t = get_inds_rhs rhs pinds ninds LN in
      let rinds = MAP FST (toAList t) in
      (rinds, inds,
        update_resize vimap Vnone (Vtrack pinds ninds) n)
    | Voverflow =>
      let (pinds,ninds) = restore n fml inds in
      let t = get_inds_rhs rhs pinds ninds LN in
      let rinds = MAP FST (toAList t) in
      (rinds, inds,
        update_resize vimap Vnone (Vtrack pinds ninds) n))
  | _ =>
    if check_get_inds_rhs vimap s
    then
      let (t,vimap) = fold_get_inds_rhs fml s LN vimap in
      let rinds = MAP FST (toAList t) in
        (rinds, inds, vimap)
    else
      let rinds = reindex fml inds in
        (rinds, rinds, vimap)
End

(* We use a hard-coded limit on the reverse mapping, i.e.,
  we store vars -> indices until the length of indices exceeds the limit.

  however, we will ignore this limit for:
  1. fresh variables that are introduced in a proof
  2. any variable that is ever used in a witness (and we restore the mapping)
*)
Definition ind_lim_def:
  ind_lim = 10n
End

Definition check_fresh_aux_fml_vimap_def:
  check_fresh_aux_fml_vimap as vimap ⇔
  EVERY (λx. any_el x vimap Vnone = Vnone) as
End

Definition check_fresh_aux_obj_vomap_def:
  check_fresh_aux_obj_vomap as vomap ⇔
  EVERY (λx. strlen vomap ≤ x ∨ strsub vomap x = ^zw) as
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

(* The fast path allows for faster checked deletion *)
Definition check_red_list_def:
  check_red_list pres ord obj b tcb fml inds id fc mv s
    (pfs:scope) idopt vimap vomap assg st =
  if check_pres pres s
  then
  let ss = mk_subst s in
  case red_fast ss idopt pfs of
    NONE => (
    let (rinds,inds',vimap') = get_set_indices fml inds s vimap in
    let nfc = not_slot fc b in
    let (fml_not_c,id1,assg,st) = store_slot fml nfc mv id assg st in
    let hs = has_scope pfs in
    let (rsubs,rscopes) = fast_red_subgoals ord ss fc obj vomap hs in
    case extract_scopes_list rscopes ss b fml rsubs pfs of
      NONE => NONE
    | SOME cpfs =>
      (case check_scopes_list cpfs b
        fml_not_c id id1 assg st of
         NONE => NONE
      |  SOME(fml', id', assg', st') =>
        let rfml = rollback fml' id id' in
        let (untouched,skipped) = skip_ord_subgoal s ord in
        if
          do_red_check idopt b tcb fml' inds'
            ss rfml rinds nfc pfs rsubs skipped
          (hs ∨ ¬ untouched ⇒
            check_fresh_aspo_list fc s ord vimap' vomap)
        then
          SOME (rfml,inds',vimap',id',assg',st')
        else NONE))
  | SOME (pf,cid) =>
    check_red_list_fast b fml inds id fc mv pf cid vimap assg st
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
Definition opt_cons_aux_def:
  opt_cons_aux i v (pinds,ninds) =
  if 0 ≤ (i:int) then (v::pinds,ninds) else (pinds,v::ninds)
End

(* fresh flag controls if, when we see a new var,
  whether to track it forever or not.
  Also, we only start resetting once fresh is set
    (i.e., when actually running a proof) *)
Definition opt_cons_def:
  (opt_cons fresh i (v:num) Vnone =
    let (pinds,ninds) = opt_cons_aux i v ([],[]) in
    if fresh then Vtrack pinds ninds else Vcount 1 pinds ninds) ∧
  (opt_cons fresh i v (Vtrack pinds ninds) =
    let (pinds,ninds) = opt_cons_aux i v (pinds,ninds) in
    Vtrack pinds ninds) ∧
  (opt_cons fresh i v (Vcount n pinds ninds) =
    if ind_lim ≤ n ∧ fresh
    then
      Voverflow
    else
      let (pinds,ninds) = opt_cons_aux i v (pinds,ninds) in
      Vcount (n+1) pinds ninds) ∧
  (opt_cons fresh i v Voverflow = Voverflow)
End

(* vimap covers every variable of the slot: the updates are unchecked *)
Definition update_vimap_slot_aux_def:
  update_vimap_slot_aux fresh (vimap:vimap_ty) v cs vs i =
  if i = 0 then vimap
  else
    let i1 = i - 1 in
    let n = sub_unsafe vs i1 in
    update_vimap_slot_aux fresh
      (LUPDATE (opt_cons fresh (sub_unsafe cs i1) v (EL n vimap)) n vimap)
      v cs vs i1
End

(* m is the slot's largest variable: vimap is resized once to cover it *)
Definition update_vimap_slot_def:
  (update_vimap_slot fresh vimap v m Empty = vimap) ∧
  (update_vimap_slot fresh vimap v m (Stored cs vs d mc b) =
    let vimap =
      if m < LENGTH vimap then vimap
      else update_resize vimap Vnone Vnone m in
    update_vimap_slot_aux fresh vimap v cs vs (length vs))
End

(* Stores slot s, whose largest variable is mv, at index id and indexes it *)
Definition store_ind_def:
  store_ind fml s mv id inds vimap assg st =
    let (fml',id',assg',st') = store_slot fml s mv id assg st in
    (fml', sorted_insert id inds, update_vimap_slot T vimap id mv s,
      id', assg', st')
End

Definition opt_update_inds_def:
  (opt_update_inds fml NONE id inds vimap assg st =
    (fml,inds,vimap,id,assg,st)) ∧
  (opt_update_inds fml (SOME (c,b)) id inds vimap assg st =
    let (s,mv) = enc_mv c b in
    store_ind fml s mv id inds vimap assg st)
End

Definition check_sstep_list_def:
  (check_sstep_list (sstep:sstep) pres ord obj tcb
    (fml: slot list) (inds:num list) (id:num)
    vimap vomap assg st =
  case sstep of
  | Lstep lstep =>
    (case check_lstep_list lstep F fml 0 id assg st of
      NONE => NONE
    | SOME (rfml,c,id',assg',st') =>
      SOME (opt_update_inds rfml c id' inds vimap assg' st'))
  | Red c s pfs idopt =>
    let (fc,mv) = enc_mv c tcb in
    case check_red_list pres ord obj F tcb fml inds id fc mv s pfs
      idopt vimap vomap assg st of
      SOME (rfml,rinds,vimap',id',assg',st') =>
      SOME (store_ind rfml fc mv id' rinds vimap' assg' st')
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
    gvs[subst_subst_fun_def,subst_slot_enc])>>
  rw[]>>
  first_x_assum irule>>
  simp[]
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
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
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
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
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
  gvs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
QED

Theorem fml_rel_check_scopes_list:
  ∀pfs b fmlls mindel id assg st fmlls' id' assg' st' fml.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    mindel ≤ id ∧
    check_scopes_list pfs b fmlls mindel id assg st =
      SOME (fmlls', id', assg', st') ⇒
    ∃fml'.
      check_scopes pfs b fml id =
        SOME (fml',id') ∧
      fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st'
Proof
  ho_match_mp_tac check_scopes_list_ind>>rw[]>>
  fs[check_scopes_def,check_scopes_list_def]>>
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
  gvs[AllCaseEqs()]>>
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
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
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
  imp_res_tac list_insert_fml_list_id>>
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
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
  rw[]>>
  qpat_x_assum`list_insert_fml_list _ _ _ _ _ _ = _` assume_tac>>
  drule list_insert_fml_list_id_upper>>
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
  drule (list_insert_fml_list_mindel)>>fs[]>>
  rw[]>>
  drule (list_insert_fml_list_id)>>
  drule check_subproofs_list_id>>rw[]>>
  gvs[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]
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

Theorem revalue_aux_SUBSET:
  ∀inds vacc.
  fml_rel fml fmlls ∧
  EVERY (λs. ∃c b'. s = enc c b' ∧ c ∈ core_only_fml b fml) vacc ⇒
  EVERY (λs. ∃c b'. s = enc c b' ∧ c ∈ core_only_fml b fml)
    (revalue_aux b fmlls inds vacc)
Proof
  Induct>>rw[revalue_aux_def,slot_CASE_default]>>
  first_x_assum irule>>simp[]>>
  drule_all fml_rel_lookup_core_only_enc>>
  rw[]>>
  first_assum (irule_at Any)>>
  gvs[lookup_core_only_def,core_only_fml_def,AllCaseEqs()]>>
  rw[]>>
  metis_tac[]
QED

Theorem revalue_SUBSET:
  fml_rel fml fmlls ==>
  EVERY (λs. ∃c b'. s = enc c b' ∧ c ∈ core_only_fml b fml)
    (revalue b fmlls inds)
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
  gvs[lookup_core_only_list_eq,IS_SOME_EXISTS,AllCaseEqs()]
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

Theorem fml_rel_subst_opt_slot:
  fml_rel fmls fml ⇒
  subst_opt_slot w (lookup_core_only_list b fml i) =
  case lookup_core_only b fmls i of
    NONE => NONE
  | SOME c => subst_opt w c
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
  subst_opt w c = SOME res
  ⇒
  MEM (i,res) (subst_indexes w b fml inds)
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
  MEM (i,res) (subst_indexes w b fml inds) ⇒
  ∃c.
  MEM i inds ∧
  lookup_core_only b fmls i = SOME c ∧
  subst_opt w c = SOME res
Proof
  Induct>>rw[subst_indexes_def]>>
  qpat_x_assum`MEM _ _` mp_tac>>
  drule fml_rel_subst_opt_slot>>
  disch_then (fn th => simp[th])>>
  Cases_on`lookup_core_only b fmls h`>>simp[]
  >- metis_tac[]>>
  Cases_on`subst_opt w x`>>simp[]>>
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

Theorem split_goals_hash_imp_split_goals:
  EVERY (λs. ∃c b. s = enc c b ∧ c ∈ range fml) fmlls ∧
  split_goals_hash fmlls (enc nc b0) proved goals ⇒
  split_goals fml nc proved goals
Proof
  rw[split_goals_def,split_goals_hash_eq]>>
  pairarg_tac>>fs[]>>
  fs[EVERY_FILTER,EVERY_MAP,imp_slot_enc]>>
  qpat_x_assum`EVERY _ lf`mp_tac>> match_mp_tac MONO_EVERY>>
  simp[FORALL_PROD, METIS_PROVE []``(¬P ⇒ Q) ⇔ P ∨ Q``]>>
  rw[]
  >- fs[]>>
  qpat_x_assum`in_hashset_slot _ _`
    (mp_then (Pos last) mp_tac in_hashset_slot_mk_hashset_slot)>>
  simp[LENGTH_mk_hashset_slot]>>
  strip_tac
  >- (
    gvs[EVERY_MEM]>>
    first_x_assum drule>>
    rw[]>>
    gvs[eq_slot_enc])>>
  drule_at (Pos last) in_hashset_slot_mk_hashset_slot>>
  simp[]>>
  strip_tac
  >- (
    gvs[MEM_MAP,eq_slot_enc,mem_constraint_thm,EXISTS_PROD]>>
    metis_tac[])>>
  gvs[in_hashset_slot_def,EL_REPLICATE,hash_constraint_lt_splim]
QED

Theorem lookup_core_only_list_list_delete_list:
  ∀ls n fml.
  lookup_core_only_list b
    (list_delete_list ls fml) n =
  if MEM n ls then Empty
  else
    lookup_core_only_list b fml n
Proof
  rw[lookup_core_only_list_eq,any_el_list_delete_list]
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
  ∀i coeff x.
    MEM (coeff:int,x) (FST (dec (any_el i fmlls Empty))) ⇒
    vent_mem (any_el x vimap Vnone) (0 ≤ coeff) i
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

Theorem mk_subst_cases:
  mk_subst s =
  case s of
  | [] => INR (Vector [])
  | [(n,v)] => INL (n,v)
  | _ => INR (spt_to_vec (fromAList s))
Proof
  every_case_tac>>fs[mk_subst_def]
QED

Theorem restore_aux:
  ∀inds lacc racc.
  restore_aux x fmlls inds lacc racc =
  let lis = FILTER (λn.
      cond_pos x (FST (dec (any_el n fmlls Empty)))) inds in
  let ris = FILTER (λn.
      cond_neg x (FST (dec (any_el n fmlls Empty)))) inds in
  (REVERSE lacc ++ lis,REVERSE racc ++ ris)
Proof
  Induct>>rw[restore_aux_def]>>
  `cond_pos x [] = F ∧ cond_neg x [] = F` by simp[cond_pos_def,cond_neg_def]>>
  Cases_on`any_el h fmlls Empty`>>
  gvs[restore_slot_thm]>>
  rw[]
QED

Theorem restore_characterize:
  restore x fmlls inds =
  (
  FILTER (λn.
      cond_pos x (FST (dec (any_el n fmlls Empty)))) inds,
  FILTER (λn.
      cond_neg x (FST (dec (any_el n fmlls Empty)))) inds)
Proof
  rw[restore_def,restore_aux]
QED

Theorem vec_lookup_empty[simp]:
  vec_lookup (Vector []) x = NONE
Proof
  EVAL_TAC
QED

Theorem domain_get_inds_rhs_pinds_reindex:
  any_el i fml Empty ≠ Empty ∧
  MEM i pinds ∧ rhs ≠ (INL T):bool + num lit ⇒
  i ∈ domain (get_inds_rhs rhs (reindex fml pinds) ninds t)
Proof
  rw[get_inds_rhs_def]>>
  every_case_tac>>gvs[domain_list_insert]>>
  rw[reindex_characterize,MEM_FILTER]
QED

Theorem domain_get_inds_rhs_ninds_reindex:
  any_el i fml Empty ≠ Empty ∧
  MEM i ninds ∧ rhs ≠ (INL F):bool + num lit ⇒
  i ∈ domain (get_inds_rhs rhs pinds (reindex fml ninds) t)
Proof
  rw[get_inds_rhs_def]>>
  every_case_tac>>gvs[domain_list_insert]>>
  rw[reindex_characterize,MEM_FILTER]
QED

Theorem check_get_inds_rhs_not_overflow:
  ∀vimap ls.
  check_get_inds_rhs vimap ls ∧
  MEM (n,rhs) ls ⇒
  any_el n vimap Vnone ≠ Voverflow
Proof
  ho_match_mp_tac check_get_inds_rhs_ind>>
  rw[check_get_inds_rhs_def]>>
  gvs[AllCasePreds()]
QED

Theorem get_inds_rhs_acc:
  i ∈ domain t ⇒
  i ∈ domain (get_inds_rhs rhs pinds ninds t)
Proof
  rw[get_inds_rhs_def]>>
  every_case_tac>>gvs[domain_list_insert]
QED

Theorem fold_get_inds_rhs_acc:
  ∀fml ls t vimap t' vimap'.
  fold_get_inds_rhs fml ls t vimap = (t',vimap') ∧
  i ∈ domain t ⇒ i ∈ domain t'
Proof
  ho_match_mp_tac fold_get_inds_rhs_ind>>
  rw[]
  >- gvs[fold_get_inds_rhs_def]>>
  gvs[fold_get_inds_rhs_def,AllCaseEqs(),UNCURRY_EQ,get_inds_rhs_acc]
QED

Theorem fold_get_inds_rhs_MEM:
  ∀fml ls t vimap t' vimap'.
  fold_get_inds_rhs fml ls t vimap = (t',vimap') ∧
  (∀n rhs.
    MEM (n,rhs) ls ⇒
    any_el n vimap Vnone ≠ Voverflow) ∧
  any_el i fml Empty ≠ Empty ∧
  vent_mem (any_el x vimap Vnone) pos i ∧
  MEM (x,rhs) ls ⇒
  (rhs ≠ INL T ∧ pos ⇒ i ∈ domain t') ∧
  (rhs ≠ (INL F):bool + num lit ∧ ¬pos ⇒ i ∈ domain t')
Proof
  ho_match_mp_tac fold_get_inds_rhs_ind>>
  conj_tac>- rw[]>>
  rpt gen_tac>>
  strip_tac>>
  rpt gen_tac>>
  SIMP_TAC list_ss []>>
  strip_tac>>
  rveq
  >- (
    ntac 3 (last_x_assum kall_tac)>>
    `any_el n vimap Vnone ≠ Voverflow` by metis_tac[]>>
    Cases_on`any_el n vimap Vnone`>>
    gvs[vent_mem_def,fold_get_inds_rhs_def,UNCURRY_EQ]>>
    rw[]>>
    drule_then irule fold_get_inds_rhs_acc>>
    gvs[do_reindex_rhs_def,AllCaseEqs()]>>
    drule domain_get_inds_rhs_ninds_reindex>>
    drule domain_get_inds_rhs_pinds_reindex>>
    rw[])>>
  `any_el n vimap Vnone ≠ Voverflow` by metis_tac[]>>
  Cases_on`any_el n vimap Vnone`>>
  gvs[fold_get_inds_rhs_def,UNCURRY_EQ]
  >- metis_tac[]>>
  (
    first_x_assum irule>>
    rw[any_el_update_resize]
    >- metis_tac[]>>
    Cases_on`pos`>>
    gvs[vent_mem_def,do_reindex_rhs_def,AllCaseEqs(),reindex_characterize,
      MEM_FILTER])
QED

Theorem MEM_get_set_indices_mk_subst:
  vimap_rel fmlls vimap ∧
  ind_rel fmlls inds ∧
  any_el i fmlls Empty ≠ Empty ∧
  IS_SOME (subst_opt (subst_fun (mk_subst s)) (dec (any_el i fmlls Empty))) ∧
  get_set_indices fmlls inds s vimap = (rinds, inds',vimap')
  ⇒
  MEM i rinds
Proof
  strip_tac>>
  gvs[get_set_indices_def,AllCaseEqs(),mk_subst_def,UNCURRY_EQ,toAList_domain]
  >- (
    drule IS_SOME_subst_opt>>strip_tac>>
    gvs[subst_fun_def,IS_SOME_EXISTS,vimap_rel_def])
  >- (
    drule IS_SOME_subst_opt>>strip_tac>>
    gvs[subst_fun_def,IS_SOME_EXISTS,vimap_rel_def]>>
    first_x_assum drule>>simp[vent_mem_def])
  >- (
    drule IS_SOME_subst_opt>>strip_tac>>
    gvs[subst_fun_def,IS_SOME_EXISTS,vimap_rel_def]>>
    first_x_assum drule>>simp[vent_mem_def]>>
    strip_tac>>
    gvs[AllCasePreds(),do_reindex_rhs_def,AllCaseEqs()]>>
    drule domain_get_inds_rhs_ninds_reindex>>
    drule domain_get_inds_rhs_pinds_reindex>>
    Cases_on`0 ≤ coeff`>>gvs[])
  >- (
    drule IS_SOME_subst_opt>>strip_tac>>
    gvs[subst_fun_def,IS_SOME_EXISTS,vimap_rel_def]>>
    first_x_assum drule>>simp[vent_mem_def]>>
    strip_tac>>
    gvs[AllCasePreds(),do_reindex_rhs_def,AllCaseEqs()]>>
    drule domain_get_inds_rhs_ninds_reindex>>
    drule domain_get_inds_rhs_pinds_reindex>>
    Cases_on`0 ≤ coeff`>>gvs[])
  >- (
    drule IS_SOME_subst_opt>>strip_tac>>
    gvs[subst_fun_def,IS_SOME_EXISTS]>>
    gvs[get_inds_rhs_def]>>
    Cases_on`rhs`>>
    rw[]>>
    gvs[restore_characterize,MEM_FILTER,IS_SOME_EXISTS,ind_rel_def,PULL_EXISTS,domain_list_insert]>>
    rw[cond_pos_def,cond_neg_def,EXISTS_MEM]
    >- (
      first_x_assum (irule_at Any)>>simp[]>>
      intLib.ARITH_TAC)
    >- (first_x_assum (irule_at Any)>>simp[])
    >- (Cases_on`0 ≤ coeff`
      >- (DISJ1_TAC >> first_x_assum (irule_at Any)>>simp[])
      >- (DISJ2_TAC >> first_x_assum (irule_at Any)>>simp[]>>
        intLib.ARITH_TAC)))
  >- (
    qmatch_asmsub_abbrev_tac`fold_get_inds_rhs _ ls LN _`>>
    drule IS_SOME_subst_opt>>strip_tac>>
    gvs[subst_fun_def,spt_to_vecTheory.vec_lookup_num_man_to_vec,lookup_fromAList,IS_SOME_EXISTS]>>
    rename1`ALOOKUP _ x = SOME rhs`>>
    drule ALOOKUP_MEM>> strip_tac>>
    `vent_mem (any_el x vimap Vnone) (0 ≤ coeff) i` by
      metis_tac[vimap_rel_def]>>
    `∀n rhs. MEM (n,rhs) ls ⇒ any_el n vimap Vnone ≠ Voverflow` by
      metis_tac[check_get_inds_rhs_not_overflow]>>
    drule_all fold_get_inds_rhs_MEM>>
    Cases_on`0 ≤ coeff`>>gvs[])>>
  gvs[reindex_characterize,MEM_FILTER]>>
  gvs[ind_rel_def]
QED

Theorem MEM_get_set_indices_lookup_core_only:
  fml_rel fml fmlls ∧
  vimap_rel fmlls vimap ∧
  ind_rel fmlls inds ∧
  lookup_core_only b fml i = SOME x ∧
  IS_SOME (subst_opt (subst_fun (mk_subst s)) x) ∧
  get_set_indices fmlls inds s vimap = (rinds, inds',vimap')
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
  qexistsl_tac[`fmlls`,`inds`,`inds'`,`s`,`vimap`,`vimap'`]>>
  simp[dec_enc,enc_NOT_Empty]
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

Theorem ind_rel_get_set_indices:
  get_set_indices fmlls inds s vimap = (rinds,inds',vimap') ∧
  ind_rel fmlls inds ⇒
  ind_rel fmlls inds'
Proof
  rw[get_set_indices_def] >>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  metis_tac[ind_rel_reindex]
QED

Theorem vimap_rel_do_reindex:
  vimap_rel fmlls vimap ∧
  (any_el n vimap Vnone = Vtrack pinds ninds ∨
   any_el n vimap Vnone = Vcount k pinds ninds) ∧
  do_reindex_rhs fmlls rhs pinds ninds = (pinds',ninds') ⇒
  vimap_rel fmlls
    (update_resize vimap Vnone (Vtrack pinds' ninds') n)
Proof
  rw[]>>gvs[do_reindex_rhs_def,AllCaseEqs()]>>
  fs[vimap_rel_def,any_el_update_resize]>>rw[]>>
  first_x_assum drule_all>>
  imp_res_tac MEM_dec_NOT_Empty>>
  rw[vent_mem_def,reindex_characterize]>>
  gvs[vent_mem_def,MEM_FILTER]
QED

Theorem vimap_rel_restore:
  vimap_rel fmlls vimap ∧
  restore n fmlls inds = (pinds', ninds') ∧
  ind_rel fmlls inds ⇒
  vimap_rel fmlls
    (update_resize vimap Vnone (Vtrack pinds' ninds') n)
Proof
  rw[restore_characterize,AllCaseEqs()]>>
  fs[vimap_rel_def,any_el_update_resize]>>rw[]>>
  first_x_assum drule_all>>
  rw[]>>gvs[vent_mem_def,MEM_FILTER,AllCasePreds()]>>
  rw[cond_pos_def,cond_neg_def,EXISTS_MEM,MEM_FILTER]>>
  imp_res_tac MEM_dec_NOT_Empty>>
  gvs[ind_rel_def]>>
  first_x_assum (irule_at Any)>>gvs[]>>
  intLib.ARITH_TAC
QED

Theorem vimap_rel_fold_get_inds_rhs:
  ∀fmlls ls acc vimap rinds vimap'.
  fold_get_inds_rhs fmlls ls acc vimap = (rinds,vimap') ∧
  vimap_rel fmlls vimap ⇒
  vimap_rel fmlls vimap'
Proof
  ho_match_mp_tac fold_get_inds_rhs_ind>>
  rw[fold_get_inds_rhs_def]>>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  first_x_assum irule>>
  metis_tac[vimap_rel_do_reindex]
QED

Theorem vimap_rel_get_set_indices:
  get_set_indices fmlls inds s vimap = (rinds,inds',vimap') ∧
  vimap_rel fmlls vimap ∧
  ind_rel fmlls inds ⇒
  vimap_rel fmlls vimap'
Proof
  rw[get_set_indices_def] >>
  gvs[AllCaseEqs(),UNCURRY_EQ]>>
  metis_tac[vimap_rel_do_reindex,vimap_rel_restore,vimap_rel_fold_get_inds_rhs]
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
  fast_red_subgoals ord s (enc def b) obj vomap hs =
  red_subgoals ord (subst_fun s) def obj hs
Proof
  rw[fast_red_subgoals_def,red_subgoals_def,subst_slot_enc]>>
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
  gvs[range_def,MEM_MAP]>>
  rename1`MEM y _`>>
  PairCases_on`c`>> PairCases_on`y`>>
  first_x_assum (qspecl_then [`n`,`y0`,`y1`] mp_tac)>>
  gvs[enc_opt_def,dec_enc,vent_mem_def]
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
  check_fresh_aspo_list (enc c b) s ord vimap vomap ⇒
  check_fresh_aspo fml c obj s ord
Proof
  rw[check_fresh_aspo_list_def,check_fresh_aspo_def,
    check_fresh_aux_constr_slot_enc]>>
  gvs[AllCasePreds()]>>
  metis_tac[vomap_rel_check_fresh_aux_obj_vomap,vimap_rel_check_fresh_aux_fml_vimap]
QED

Theorem fml_rel_check_red_list:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel obj vomap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_red_list pres ord obj b tcb fmlls inds id (enc c b0) (max_var (FST c)) s pfs
    idopt vimap vomap assg st =
    SOME (fmlls', inds', vimap', id', assg', st') ⇒
    check_red pres ord obj b tcb fml id c s pfs idopt = SOME id' ∧
    fml_rel fml fmlls' ∧ rup_inv fmlls' assg' st' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧
    (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
    id ≤ id'
Proof
  strip_tac>>
  fs[check_red_list_def,not_slot_enc,store_slot_enc,max_var_not]>>
  gvs[AllCaseEqs()]
  >- (
    gvs[vomap_rel_fast_red_subgoals]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    gvs[AllCaseEqs()]>>
    simp[check_red_def]>>
    DEP_REWRITE_TAC [fml_rel_extract_scopes_list]>> simp[]>>
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
    drule_all vimap_rel_get_set_indices>>
    simp[any_el_update_resize]>>
    ntac 4 strip_tac>>
    pairarg_tac>>gvs[AllCaseEqs()]>>
    `fml_rel fml (rollback fml' id id')` by (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      gvs[do_red_check_def,AllCaseEqs(),insert_fml_def,
        check_hash_goals_slot_enc]>>
      TOP_CASE_TAC>>fs[]
      >- (
        rpt (pairarg_tac>>fs[])>>
        CONJ_TAC >-
          metis_tac[vimap_rel_vomap_rel_check_fresh_aspo_list]>>
        (drule_at Any) split_goals_hash_imp_split_goals>>
        disch_then (qspec_then`mk_core_fml b fml` mp_tac)>>
        impl_tac >- (
          simp[range_mk_core_fml]>>
          gvs[get_set_indices_def] >>
          every_case_tac>> gvs[]>>
          match_mp_tac revalue_SUBSET>>
          metis_tac[])>>
        match_mp_tac split_goals_same_goals>>
        simp[EXTENSION,FORALL_PROD]>>
        rw[]>>eq_tac>>rw[]
        >- (
          fs[MEM_toAList,lookup_map_opt,AllCaseEqs(),lookup_mk_core_fml]>>
          irule MEM_subst_indexes>>
          first_assum (irule_at Any)>>
          simp[]>>
          metis_tac[MEM_get_set_indices_lookup_core_only,IS_SOME_EXISTS])>>
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
      simp[] >>
      metis_tac[ind_rel_get_set_indices])>>
    CONJ_TAC >- (
      metis_tac[fml_rel_fml_rel_vimap_rel])>>
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
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
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,any_el_update_resize])>>
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
  simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST,any_el_update_resize]>>
  rw[]
QED

Theorem store_ind_enc:
  mv = max_var (FST c) ⇒
  (store_ind fml (enc c b) mv id inds vimap assg st =
    (fml',inds',vimap',id',assg',st') ⇔
  opt_update fml (SOME (c,b)) id assg st = (fml',id',assg',st') ∧
  inds' = sorted_insert id inds ∧
  vimap' = update_vimap_slot T vimap id mv (enc c b))
Proof
  rw[store_ind_def,opt_update_def,enc_mv_enc]>>
  pairarg_tac>>simp[]>>
  metis_tac[]
QED

Theorem opt_update_inds_opt_update:
  opt_update_inds fml c id inds vimap assg st =
    (fml',inds',vimap',id',assg',st') ⇒
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
  opt_update_inds fml c id inds vimap assg st =
    (fml',inds',vimap',id',assg',st') ⇒
  SORTED $>= inds'
Proof
  Cases_on`c`>>strip_tac>>gvs[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  gvs[opt_update_inds_def,enc_mv_enc,store_ind_enc]>>
  metis_tac[SORTED_sorted_insert]
QED

Theorem opt_update_inds_ind_rel:
  ind_rel fml inds ∧
  opt_update_inds fml c id inds vimap assg st =
    (fml',inds',vimap',id',assg',st') ⇒
  ind_rel fml' inds'
Proof
  Cases_on`c`>>strip_tac>>gvs[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  gvs[opt_update_inds_def,enc_mv_enc,store_ind_enc,opt_update_SOME]>>
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

Theorem earliest_rel_append_NONE[local]:
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

Theorem lookup_update_earliest_none[local]:
  ∀v0 n earliest x.
    lookup x (update_earliest earliest n v0) = NONE ⇒
    ¬MEM x (MAP SND v0) ∧ lookup x earliest = NONE
Proof
  Induct \\ gvs [update_earliest_def,FORALL_PROD]
  \\ rw [] \\ first_x_assum drule \\ fs []
  \\ gvs [lookup_insert,AllCaseEqs()]
QED

Theorem lookup_update_earliest_some[local]:
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

Theorem earliest_rel_lupdate[local]:
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
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_lstep_list lstep b fmlls mindel id assg st =
    SOME (fmlls',x,y,z,w) ⇒
  vimap_rel fmlls' vimap
Proof
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

Theorem vent_mem_opt_cons:
  vent_mem e pos j ⇒ vent_mem (opt_cons fresh c v e) pos j
Proof
  Cases_on`e`>>
  rw[opt_cons_def,vent_mem_def,opt_cons_aux_def]>>
  gvs[]
QED

Theorem vent_mem_opt_cons_new:
  vent_mem (opt_cons fresh c v e) (0 ≤ c) v
Proof
  Cases_on`e`>>
  rw[opt_cons_def,vent_mem_def,opt_cons_aux_def]>>
  rw[vent_mem_def]
QED

Theorem any_el_LUPDATE:
  any_el i (LUPDATE v n ls) d =
  if i = n ∧ n < LENGTH ls then v else any_el i ls d
Proof
  rw[any_el_ALT,EL_LUPDATE]>>
  gvs[]
QED

Theorem LENGTH_update_vimap_slot_aux:
  ∀fresh vimap v cs vs i.
  LENGTH (update_vimap_slot_aux fresh vimap v cs vs i) = LENGTH vimap
Proof
  ho_match_mp_tac update_vimap_slot_aux_ind>>
  rw[]>>
  rw[Once update_vimap_slot_aux_def]
QED

Theorem vent_mem_update_vimap_slot_aux:
  ∀fresh vimap v cs vs i.
  (∀k. k < i ⇒ sub vs k < LENGTH vimap) ⇒
  (∀x pos j.
    vent_mem (any_el x vimap Vnone) pos j ⇒
    vent_mem (any_el x (update_vimap_slot_aux fresh vimap v cs vs i) Vnone)
      pos j) ∧
  (∀k. k < i ⇒
    vent_mem
      (any_el (sub vs k) (update_vimap_slot_aux fresh vimap v cs vs i) Vnone)
      (0 ≤ sub cs k) v)
Proof
  ho_match_mp_tac update_vimap_slot_aux_ind>>
  rpt gen_tac>>strip_tac>>strip_tac>>
  ONCE_REWRITE_TAC[update_vimap_slot_aux_def]>>
  IF_CASES_TAC
  >- simp[]>>
  simp[]>>
  first_x_assum (qspecl_then [`i-1`,`sub vs (i-1)`] mp_tac)>>
  simp[]>>
  qmatch_goalsub_abbrev_tac`update_vimap_slot_aux _ vimap1 _ _ _ _`>>
  `sub vs (i-1) < LENGTH vimap` by simp[]>>
  `∀x pos j. vent_mem (any_el x vimap Vnone) pos j ⇒
    vent_mem (any_el x vimap1 Vnone) pos j` by (
    rw[Abbr`vimap1`,any_el_LUPDATE]>>
    gvs[any_el_ALT]>>
    metis_tac[vent_mem_opt_cons])>>
  `vent_mem (any_el (sub vs (i-1)) vimap1 Vnone) (0 ≤ sub cs (i-1)) v` by
    simp[Abbr`vimap1`,any_el_LUPDATE,vent_mem_opt_cons_new]>>
  rw[]>>
  Cases_on`k = i - 1`
  >- metis_tac[]>>
  `k < i - 1` by simp[]>>
  metis_tac[]
QED

Theorem vent_mem_update_vimap_slot:
  max_var (FST c) ≤ m ⇒
  (vent_mem (any_el x vimap Vnone) pos j ⇒
    vent_mem (any_el x (update_vimap_slot fresh vimap v m (enc c b)) Vnone)
      pos j) ∧
  (MEM (coeff,y) (FST c) ⇒
    vent_mem (any_el y (update_vimap_slot fresh vimap v m (enc c b)) Vnone)
      (0 ≤ coeff) v)
Proof
  PairCases_on`c`>>
  simp[update_vimap_slot_def,enc_def,mlvectorTheory.length_def]>>
  strip_tac>>
  qmatch_goalsub_abbrev_tac`update_vimap_slot_aux _ vimap1 _ _ _ _`>>
  `∀x. any_el x vimap1 Vnone = any_el x vimap Vnone` by (
    rw[Abbr`vimap1`,any_el_update_resize]>>
    IF_CASES_TAC>>gvs[any_el_ALT])>>
  `∀k. k < LENGTH c0 ⇒ sub (Vector (MAP SND c0)) k < LENGTH vimap1` by (
    rw[mlvectorTheory.sub_def,EL_MAP]>>
    `SND (EL k c0) < max_var c0 + 1` by (
      qspec_then`c0` assume_tac max_var_bound>>
      gvs[EVERY_EL]>>
      first_x_assum drule>>
      pairarg_tac>>simp[])>>
    rw[Abbr`vimap1`,update_resize_def])>>
  drule vent_mem_update_vimap_slot_aux>>
  disch_then (qspecl_then [`fresh`,`v`,`Vector (MAP FST c0)`]
    strip_assume_tac)>>
  rw[]>>
  gvs[MEM_EL]>>
  first_x_assum (qspec_then`n` mp_tac)>>
  simp[mlvectorTheory.sub_def,EL_MAP]>>
  qpat_x_assum`_ = EL _ _` (assume_tac o SYM)>>
  gvs[]
QED

Theorem vimap_rel_update_resize_update_vimap_slot:
  vimap_rel fml vimap ∧ max_var (FST c) ≤ m ⇒
  vimap_rel (update_resize fml Empty (enc c b) n)
    (update_vimap_slot fresh vimap n m (enc c b'))
Proof
  rw[vimap_rel_def,any_el_update_resize]>>
  Cases_on`i = n`>>gvs[dec_enc]>>
  metis_tac[vent_mem_update_vimap_slot]
QED

Theorem opt_update_inds_vimap_rel:
  vimap_rel fml vimap ∧
  opt_update_inds fml c id inds vimap assg st =
    (fml',inds',vimap',id',assg',st') ⇒
  vimap_rel fml' vimap'
Proof
  Cases_on`c`>>strip_tac>>gvs[opt_update_inds_def]>>
  rename1`SOME cc`>>PairCases_on`cc`>>
  gvs[opt_update_inds_def,enc_mv_enc,store_ind_enc,opt_update_SOME]>>
  simp[vimap_rel_update_resize_update_vimap_slot]
QED

Theorem store_rels:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧ ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  grow_assg assg st (max_var (FST c) + 1) = (assg',st') ⇒
  fml_rel (insert id (c,b) fml) (update_resize fmlls Empty (enc c b) id) ∧
  rup_inv (update_resize fmlls Empty (enc c b) id) assg' st' ∧
  ind_rel (update_resize fmlls Empty (enc c b) id) (sorted_insert id inds) ∧
  vimap_rel (update_resize fmlls Empty (enc c b) id)
    (update_vimap_slot T vimap id (max_var (FST c)) (enc c b)) ∧
  (∀n. n ≥ id + 1 ⇒
    any_el n (update_resize fmlls Empty (enc c b) id) Empty = Empty)
Proof
  rw[fml_rel_update_resize,ind_rel_update_resize_sorted_insert,
    vimap_rel_update_resize_update_vimap_slot,any_el_update_resize]>>
  metis_tac[rup_inv_update_resize_grow]
QED

Theorem fml_rel_check_sstep_list:
  ∀sstep pres ord obj fmlls inds id assg st fmlls' id' inds' assg' st' fml.
    fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
    ind_rel fmlls inds ∧
    vimap_rel fmlls vimap ∧
    vomap_rel obj vomap ∧
    (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
    check_sstep_list sstep pres ord obj tcb fmlls inds id vimap vomap assg st =
      SOME (fmlls',inds',vimap',id',assg',st') ⇒
    ∃fml'.
      check_sstep sstep pres ord obj tcb fml id = SOME(fml',id') ∧
      fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st' ∧
      ind_rel fmlls' inds' ∧
      vimap_rel fmlls' vimap' ∧
      (∀n. n ≥ id' ⇒ any_el n fmlls' Empty = Empty) ∧
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
    simp[]>>rw[])>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[AllCaseEqs(),insert_fml_def,enc_mv_enc,store_ind_enc]>>
  drule_all fml_rel_check_red_list>>
  strip_tac>>
  gvs[opt_update_SOME]>>
  drule_all store_rels>>
  simp[]
QED

Definition do_dom_check_def:
  do_dom_check idopt fml rfml inds goals extra pfs dsubs dindex =
  case idopt of NONE =>
    let (l,r) = extract_scoped_pids pfs LN LN in
    if
      find_scope_1 dindex pfs ∧
      check_hash_goals_slot extra [dindex] r dsubs
    then
      let fmlls = revalue F rfml inds in
      split_goals_hash fmlls extra l goals
    else F
  | SOME cid =>
     check_contradiction_fml_list F fml cid
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
  if EVERY (λi. sat_slot w (lookup_core_only_list T fml i)) inds
  then
    case bopt of NONE => SOME (new, w)
    | SOME b =>
      if b = new then SOME (new, w) else NONE
  else NONE
End

Definition check_sol_core_def:
  check_sol_core wm free fml inds =
  if EVERY (λ(v,b). lookup v free = NONE) wm then
    let cw = vec_lookup_d (SOME F) (mk_cube_vec wm free) in
    if EVERY (λ(v,b). cw v = SOME b) wm ∧
      EVERY (λi. cube_slot cw (lookup_core_only_list T fml i)) inds then
      SOME (λv. case cw v of NONE => F | SOME b => b)
    else NONE
  else NONE
End

(* flag all indices as T *)
Definition core_from_inds_def:
  (core_from_inds fml [] = SOME fml) ∧
  (core_from_inds fml (i::is) =
    case any_el i fml Empty of
      Empty => NONE
    | Stored cs vs d mc b =>
      core_from_inds (update_resize fml Empty (Stored cs vs d mc T) i) is)
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
  gvs[AllCaseEqs()]>>
  rename1`any_el h fmlls Empty = Stored cs vs d mc b`>>
  `∃c b'. lookup h fml = SOME (c,b') ∧ any_el h fmlls Empty = enc c b'` by (
    irule fml_rel_any_el>>simp[])>>
  `Stored cs vs d mc T = enc c T` by gvs[enc_eq_Stored]>>
  first_x_assum (qspecl_then [`insert h (c,T) fml`,
    `update_resize fmlls Empty (enc c T) h`,`fmlls'`,`n`] mp_tac)>>
  impl_tac >- gvs[fml_rel_update_resize]>>
  rw[lookup_insert]>>
  gvs[]
QED

Definition all_core_list_def:
  (all_core_list fml [] iacc = SOME (REVERSE iacc)) ∧
  (all_core_list fml (i::is) iacc =
    case any_el i fml Empty of
      Empty => all_core_list fml is iacc
    | Stored cs vs d mc b =>
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

Definition check_spec_aux_list_def:
  (check_spec_aux_list asv fml inds id [] vimap assg st = T) ∧
  (check_spec_aux_list asv fml inds id (((c,s,pfs,idopt)::gs):specproof) vimap assg st =
  if check_support asv s then
    let (fc,mv) = enc_mv c F in
    case check_red_list (NONE:num_set option) (NONE:ord_s option) NONE F F
      fml inds id fc mv s pfs idopt vimap «» assg st of
        NONE => F
      | SOME (fml',inds',vimap',id',assg',st') =>
        let (fml'',inds'',vimap'',id'',assg'',st'') =
          store_ind fml' fc mv id' inds' vimap' assg' st' in
        check_spec_aux_list asv fml'' inds'' id'' gs vimap'' assg'' st''
  else F)
End

Theorem fml_rel_check_spec_aux_list:
  ∀gs fml fmlls inds vimap id assg st.
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  (∀n. n ≥ id ⇒ any_el n fmlls Empty = Empty) ∧
  check_spec_aux_list as fmlls inds id gs vimap assg st ⇒
  check_spec_aux as (fml,id) gs
Proof
  Induct>>rw[check_spec_aux_def,check_spec_aux_list_def]>>
  `?c s pfs idopt. h = (c,s,pfs,idopt)` by metis_tac[PAIR]>>
  gvs[check_spec_aux_def,check_spec_aux_list_def,AllCasePreds()]>>
  rpt (pairarg_tac>>gvs[])>>
  gvs[enc_mv_enc]>>
  drule_at (Pos last) fml_rel_check_red_list>>
  simp[vomap_rel_def]>>
  disch_then drule>>
  strip_tac>>
  gvs[store_ind_enc,opt_update_SOME,insert_fml_def]>>
  drule_all store_rels>> strip_tac>>
  first_x_assum irule>>
  first_x_assum (irule_at (Pos last))>>
  gvs[]
QED

Definition check_spec_list_def:
  check_spec_list (us,vs,as) gs =
    let asv = spt_to_vec (fromAList (MAP (\n. n,()) as)) in
    if check_spec_aux_list asv [] [] 1 gs [] [] 1 then
      SOME asv
    else NONE
End

Theorem fml_rel_check_spec_list:
  check_spec_list vars gs = SOME asv ⇒
  check_spec vars gs = SOME asv
Proof
  PairCases_on`vars`>>rw[check_spec_list_def,check_spec_def]>>
  drule_at (Pos last) fml_rel_check_spec_aux_list>>
  disch_then irule>>
  rw[rup_inv_def,fml_bound_def]
  >~ [`dm_rel`] >- (
    qexists_tac`FEMPTY`>>
    metis_tac[dm_rel_FEMPTY_REPLICATE,REPLICATE])>>
  EVAL_TAC>>simp[]
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
  check_storeorder vars gspec f pfst pfsr =
  case check_spec_list vars gspec of NONE => NONE
  | SOME asv =>
    let aord = mk_aord vars f gspec in
    if check_good_aord aord
    then
      case check_transitivity aord pfst of
        NONE => NONE
      | SOME id =>
        if check_reflexivity aord pfsr id then SOME (aord,asv)
        else NONE
    else NONE
End

(* make a list of variables (which are partially tracked) permanently tracked *)
Definition mk_perm_def:
  (mk_perm (vimap:vimap_ty) [] = vimap) ∧
  (mk_perm (vimap:vimap_ty) (n::ns) =
    (case any_el n vimap Vnone of
    | Vcount k pinds ninds =>
      mk_perm
        (update_resize vimap Vnone (Vtrack pinds ninds) n) ns
    | _ => mk_perm vimap ns))
End

Definition check_cstep_list_def:
  check_cstep_list cstep fml assg st inds vimap vomap pc =
  case cstep of
    Dom c s pfs idopt =>
    (case pc.ord of
      NONE => NONE
    | SOME spo =>
    let (fc,nfc,mv) = neg_pos_slot c pc.tcb F in
    if check_pres pc.pres s ∧
      check_fresh_aspo_list fc s pc.ord vimap vomap then
    ( let id = pc.id in
      let (rinds,inds',vimap') = get_set_indices fml inds s vimap in
      let s = mk_subst s in
      let w = subst_fun s in
      let goals = subst_indexes w T fml rinds in
      let (fml_not_c,id1,assg1,st1) = store_slot fml nfc mv id assg st in
      let (dsubs,dscopes,dindex) = dom_subgoals spo w c pc.obj in
      case extract_scopes_list dscopes s F fml dsubs pfs of
        NONE => NONE
      | SOME cpfs =>
        (case check_scopes_list cpfs F
          fml_not_c id id1 assg1 st1 of
          NONE => NONE
        | SOME (fml',id',assg',st') =>
          let rfml = rollback fml' id id' in
          if do_dom_check idopt fml' rfml inds' goals nfc pfs dsubs dindex then
            let (fml'',inds'',vimap'',id'',assg'',st'') =
              store_ind rfml fc mv id' inds' vimap' assg' st' in
            SOME(fml'', assg'', st'', inds'', vimap'', vomap,
              pc with id := id'')
          else NONE))
    else NONE)
  | Sstep sstep =>
    (case check_sstep_list sstep pc.pres pc.ord pc.obj pc.tcb
      fml inds pc.id vimap vomap assg st of
      SOME(fml',inds',vimap',id',assg',st') =>
        SOME(fml',assg',st', inds', vimap', vomap, pc with id := id')
    | NONE => NONE)
  | CheckedDelete n s pfs idopt => (
    if check_tcb_idopt pc.tcb idopt then
      (case lookup_core_only_list T fml n of
        Empty => NONE
      | fc =>
          (let nfml = delete_list n fml in
          let mv = slot_max_var fc in
          case check_red_list pc.pres pc.ord pc.obj T pc.tcb
            nfml inds pc.id fc mv s pfs idopt vimap vomap assg st of
            SOME (ncf',inds',vimap',id',assg',st') =>
            SOME (ncf',assg',st', inds',
              vimap', vomap, pc with <| id := id' |>)
          | NONE => NONE) )
    else NONE)
  | UncheckedDelete ls => (
    (* Either no order or all ids are in core *)
    if ¬pc.tcb ∧ pc.ord = NONE
    then
      SOME (list_delete_list ls fml, assg, st, inds,
        vimap, vomap, pc with chk := F)
    else
    case all_core_list fml inds [] of NONE => NONE
    | SOME inds' =>
      SOME (list_delete_list ls fml, assg, st, inds',
        vimap, vomap, pc with chk := F))
  | Transfer ls =>
    (case core_from_inds fml ls of NONE => NONE
    | SOME fml' =>
      SOME (fml', assg, st, inds, vimap, vomap, pc))
  | StrengthenToCore b =>
    (let inds' = reindex fml inds in
    let pc' = pc with tcb := b in
    if b
    then
      (case core_from_inds fml inds' of NONE => NONE
      | SOME fml' =>
        SOME (fml',assg,st,inds', vimap, vomap, pc'))
    else
      SOME (fml,assg,st,inds',vimap, vomap, pc'))
  | LoadOrder nn xs =>
    (let inds' = reindex fml inds in
      case ALOOKUP pc.orders nn of NONE => NONE
      | SOME ord' =>
        if guard_ord_t ord' xs then
          case core_from_inds fml inds' of NONE => NONE
          | SOME fml' =>
          SOME (fml',assg,st, inds',
            mk_perm vimap (MAP FST xs),vomap,pc with ord := mk_ordsub ord' xs)
        else NONE)
  | UnloadOrder =>
    (case pc.ord of NONE => NONE
    | SOME spo =>
        SOME (fml, assg, st, inds,
          vimap, vomap, pc with ord := NONE))
  | StoreOrder nn vars gspec f pfsr pfst =>
    (case check_storeorder vars gspec f pfst pfsr of NONE => NONE
    | SOME aord =>
      SOME (fml, assg, st, inds,
        vimap, vomap,
        pc with orders := (nn ,aord)::pc.orders))
  | Obj w mi bopt => (
    case check_obj_core pc.obj w fml inds bopt of
      NONE => NONE
    | SOME (new,w) =>
      let bound' = update_bound pc.chk pc.bound new in
      let dbound' = update_dbound pc.dbound new in
      if mi then
        if pc.obj ≠ NONE then
          let c = model_improving pc.obj new in
          let (s,mv) = enc_mv c T in
          let (fml',inds',vimap',id',assg',st') =
            store_ind fml s mv pc.id inds vimap assg st in
          SOME (
            fml', assg', st', inds', vimap', vomap,
            pc with
            <| id := id';
               bound := bound';
               dbound := dbound' |>)
        else NONE
      else
        SOME (fml, assg, st, inds, vimap, vomap,
          pc with
          <| bound := bound';
             dbound := dbound' |>))
  | ChangeObj b fc' pfs =>
    (case check_change_obj_list b fml pc.id pc.obj
        fc' pfs assg st of
      NONE => NONE
    | SOME (fml',fc',id',assg',st') =>
      SOME (
        fml', assg', st', inds,
        vimap, mk_vomap (strlen vomap) fc',
        pc with <| id:=id'; obj:=SOME fc' |>))
  | CheckObj fc' =>
    if check_eq_obj pc.obj fc'
    then SOME (fml, assg, st, inds, vimap, vomap, pc)
    else NONE
  | AssertObj i => (
      if pc.obj ≠ NONE then
        let c = model_improving pc.obj i in
        let dbound' = update_dbound pc.dbound i in
        let (s,mv) = enc_mv c T in
        let (fml',inds',vimap',id',assg',st') =
          store_ind fml s mv pc.id inds vimap assg st in
          SOME (
            fml', assg', st', inds', vimap', vomap,
            pc with
            <| id := id';
               dbound := dbound' |>)
      else NONE
    )
  | ChangePres b v c pfs =>
    (case check_change_pres_list b fml pc.id pc.pres
        v c pfs assg st of
      NONE => NONE
    | SOME (fml',pres',id',assg',st') =>
      SOME (
        fml', assg', st', inds,
        vimap, vomap,
        pc with <| id:=id'; pres:=SOME pres' |>))
  | Sol w free =>
    (if pc.obj ≠ NONE ∨ ¬pc.chk then NONE
    else
    case check_sol_core w free fml inds of
      NONE => NONE
    | SOME w =>
      let bound' = update_bound pc.chk pc.bound 0 in
      let dbound' = update_dbound pc.dbound 0 in
      let c = model_banning pc.pres free w in
      let (s,mv) = enc_mv c T in
      let (fml',inds',vimap',id',assg',st') =
        store_ind fml s mv pc.id inds vimap assg st in
        SOME (
          fml', assg', st', inds', vimap', vomap,
          pc with
          <| id := id';
             bound := bound';
             dbound := dbound';
             enum := pc.enum + cube_count pc.pres free |>))
  | CheckPres ls' =>
    if check_eq_pres pc.pres ls'
    then SOME (fml, assg, st, inds, vimap, vomap, pc)
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
  rw[ind_rel_def,lookup_core_only_list_eq]>>
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
  rename1`any_el h fmlls Empty = Stored cs vs d mc b`>>
  `∃c b'. lookup h fml = SOME (c,b') ∧ any_el h fmlls Empty = enc c b'` by (
    irule fml_rel_any_el>>simp[])>>
  `Stored cs vs d mc T = enc c T` by gvs[enc_eq_Stored]>>
  simp[]>>
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
  gvs[enc_eq_Stored]
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
  Induct \\ rw[core_from_inds_def] \\ gvs []
  \\ gvs [AllCaseEqs()]
  \\ last_x_assum irule
  \\ pop_assum $ irule_at Any
  \\ gvs [vimap_rel_def,any_el_update_resize]
  \\ rw [] \\ gvs []
  \\ first_x_assum irule
  \\ gvs [dec_def]
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
  \\ first_x_assum (qspec_then`h` mp_tac)
  \\ simp[slot_bound_def]
QED

Theorem fml_rel_core_from_inds_reindex:
  fml_rel fml fmlls ∧ ind_rel fmlls inds ∧
  core_from_inds fmlls (reindex fmlls inds) = SOME fmlls' ⇒
  fml_rel (map (λ(c,b). (c,T)) fml) fmlls'
Proof
  rw[]>>
  drule_all any_el_core_from_inds>> strip_tac>>
  rw[fml_rel_def,lookup_map]>>
  Cases_on`lookup x fml`>>gvs[]>>
  rename1`lookup x fml = SOME p`>>Cases_on`p`>>
  gvs[reindex_characterize,MEM_FILTER]>>
  `any_el x fmlls Empty = enc q r` by (
    qpat_x_assum`fml_rel fml fmlls` mp_tac>>
    rw[fml_rel_def]>>
    simp[enc_opt_def])>>
  gvs[ind_rel_def,enc_NOT_Empty]
QED

Theorem vimap_rel_mk_perm:
  ∀ls vimap.
  vimap_rel fmlls vimap ⇒
  vimap_rel fmlls (mk_perm vimap ls)
Proof
  Induct>>rw[mk_perm_def]>>
  every_case_tac>>gvs[]>>
  first_x_assum irule>>
  gvs[vimap_rel_def]>>rw[]>>
  first_x_assum drule_all>>
  gvs[any_el_update_resize]>>rw[]>>
  gvs[vent_mem_def]
QED

Theorem fml_rel_check_cstep_list:
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel pc.obj vomap ∧
  (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty) ∧
  check_cstep_list cstep fmlls assg st inds vimap vomap pc =
    SOME (fmlls',assg',st',inds',vimap',vomap',pc') ⇒
  ∃fml'.
    check_cstep cstep fml pc = SOME (fml', pc') ∧
    fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧
    vomap_rel pc'.obj vomap' ∧
    (∀n. n ≥ pc'.id ⇒ any_el n fmlls' Empty = Empty) ∧
    pc.id ≤ pc'.id
Proof
  Cases_on`cstep`>>rw[]
  >~ [‘Dom’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    rpt(pairarg_tac>>gvs[])>>
    gvs[AllCaseEqs(),neg_pos_slot_enc,store_slot_enc,max_var_not]>>
    drule_all vimap_rel_vomap_rel_check_fresh_aspo_list >>
    disch_then $ irule_at Any >>
    DEP_REWRITE_TAC[fml_rel_extract_scopes_list]>>
    simp[PULL_EXISTS]>>
    qpat_x_assum`opt_update fmlls _ _ _ _ = _` assume_tac>>
    drule_all rup_inv_opt_update>> strip_tac>>
    gvs[opt_update_SOME]>>
    drule_at (Pos last) fml_rel_check_scopes_list >>
    disch_then(qspec_then`insert pc.id (not p,F) fml` mp_tac)>>
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
    `fml_rel fml (rollback fml' pc.id id')` by (
      match_mp_tac fml_rel_rollback>>rw[]>>fs[])>>
    CONJ_TAC >- (
      fs[do_dom_check_def,check_hash_goals_slot_enc]>>
      every_case_tac>>fs[]
      >- (
        (drule_at Any) split_goals_hash_imp_split_goals>>
        disch_then(qspec_then `mk_core_fml F fml` mp_tac)>>
        impl_tac >- (
          simp[range_mk_core_fml]>>
          match_mp_tac revalue_SUBSET>>
          simp[])>>
        match_mp_tac split_goals_same_goals>>
        simp[EXTENSION,FORALL_PROD]>>
        rw[]>>eq_tac>>rw[]
        >- (
          fs[MEM_toAList,lookup_map_opt,AllCaseEqs(),lookup_mk_core_fml]>>
          irule MEM_subst_indexes>>
          qpat_assum`fml_rel fml fmlls` (irule_at Any)>>
          simp[]>>
          metis_tac[MEM_get_set_indices_lookup_core_only,IS_SOME_EXISTS])>>
        qpat_x_assum`fml_rel fml fmlls` assume_tac>>
        drule_at (Pos last) subst_indexes_MEM>>
        disch_then drule>>
        rw[]>>
        gvs[MEM_toAList,lookup_map_opt,lookup_mk_core_fml])>>
      metis_tac[fml_rel_check_contradiction_fml])>>
    `rup_inv (rollback fml' pc.id id') assg'' st''` by
      metis_tac[rup_inv_rollback]>>
    `ind_rel (rollback fml' pc.id id') inds''` by (
      match_mp_tac ind_rel_rollback_2>>
      fs[]>>
      metis_tac[ind_rel_get_set_indices])>>
    `vimap_rel (rollback fml' pc.id id') vimap''` by (
      match_mp_tac fml_rel_fml_rel_vimap_rel>>fs[]>>
      metis_tac[vimap_rel_get_set_indices])>>
    `∀n. n ≥ id' ⇒ any_el n (rollback fml' pc.id id') Empty = Empty` by
      simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    drule_all store_rels>>
    simp[])
  >~ [‘Sstep’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all fml_rel_check_sstep_list>>
    rw[]>>simp[])
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
    drule_all ind_rel_reindex>> strip_tac>>
    rw[]
    >~ [`fml_rel (map _ _)`] >- metis_tac[fml_rel_core_from_inds_reindex]
    >~ [`rup_inv`] >- metis_tac[rup_inv_core_from_inds]
    >~ [`ind_rel`] >- metis_tac[ind_rel_core_from_inds]
    >~ [`vimap_rel`] >- metis_tac[vimap_rel_core_from_inds]>>
    metis_tac[any_el_core_from_inds_Empty])
  >~ [‘LoadOrder’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def]>>
    drule_all ind_rel_reindex>> strip_tac>>
    rw[]
    >~ [`fml_rel (map _ _)`] >- metis_tac[fml_rel_core_from_inds_reindex]
    >~ [`rup_inv`] >- metis_tac[rup_inv_core_from_inds]
    >~ [`ind_rel`] >- metis_tac[ind_rel_core_from_inds]
    >~ [`vimap_rel`] >-
      metis_tac[vimap_rel_core_from_inds,vimap_rel_mk_perm]>>
    metis_tac[any_el_core_from_inds_Empty])
  >~ [‘UnloadOrder’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def])
  >~ [‘StoreOrder’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,check_storeorder_def]>>
    metis_tac[fml_rel_check_spec_list])
  >~ [‘Obj’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,
      check_obj_core_thm,check_obj_slots_thm]>>
    drule_all core_fmlls_mk_core_fml>>strip_tac>>
    drule check_obj_cong>>rw[]>>fs[]>>
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
    CONJ_TAC >- metis_tac[rup_inv_rollback]>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >-
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    CONJ_TAC >-
      metis_tac[vomap_rel_mk_vomap]>>
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    rw[])
  >~ [‘CheckObj’] >- (
    fs[check_cstep_def,check_cstep_list_def])
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
    CONJ_TAC >- metis_tac[rup_inv_rollback]>>
    CONJ_TAC >- (
      match_mp_tac ind_rel_rollback_2>>
      simp[]>>
      metis_tac[ind_rel_reindex])>>
    CONJ_TAC >-
      metis_tac[fml_rel_fml_rel_vimap_rel]>>
    simp[rollback_def,any_el_list_delete_list,MEM_MAP,MEM_COUNT_LIST]>>
    rw[])
  >~ [‘CheckPres’] >- (
    fs[check_cstep_def,check_cstep_list_def])
  >~ [‘Sol’] >- (
    gvs[check_cstep_list_def,AllCaseEqs(),check_cstep_def,
      check_sol_core_thm,check_sol_slots_thm]>>
    drule_all core_fmlls_mk_core_fml>>strip_tac>>
    drule check_sol_cong>>rw[]>>fs[]>>
    rpt (pairarg_tac>>gvs[])>>
    gvs[enc_mv_enc,store_ind_enc,opt_update_SOME]>>
    drule_all store_rels>>
    simp[])
QED


Definition check_csteps_list_def:
  (check_csteps_list [] fml assg st inds vimap vomap pc =
    SOME (fml, assg, st, inds, vimap, vomap, pc)) ∧
  (check_csteps_list (c::cs) fml assg st inds vimap vomap pc =
    case check_cstep_list c fml assg st inds vimap vomap pc of
      NONE => NONE
    | SOME(fml', assg', st', inds', vimap', vomap', pc') =>
      check_csteps_list cs fml' assg' st' inds' vimap' vomap' pc')
End

Theorem fml_rel_check_csteps_list:
  ∀csteps fml fmlls assg st inds vimap vomap pc
    fmlls' assg' st' inds' vimap' vomap' pc'.
  fml_rel fml fmlls ∧ rup_inv fmlls assg st ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel pc.obj vomap ∧
  (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty) ∧
  check_csteps_list csteps fmlls assg st inds vimap vomap pc =
    SOME (fmlls', assg', st', inds', vimap', vomap', pc') ⇒
  ∃fml'.
    check_csteps csteps fml pc = SOME (fml', pc') ∧
    fml_rel fml' fmlls' ∧ rup_inv fmlls' assg' st' ∧
    ind_rel fmlls' inds' ∧
    vimap_rel fmlls' vimap' ∧
    vomap_rel pc'.obj vomap' ∧
    (∀n. n ≥ pc'.id ⇒ any_el n fmlls' Empty = Empty) ∧
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

(* For initial setup. Do not track vars; also returns the largest
  variable seen *)
Definition mk_vimap_def:
  (mk_vimap vimap (mx:num) [] = (vimap,mx)) ∧
  (mk_vimap vimap mx ((i,s)::efmls) =
    let m = slot_max_var s in
    mk_vimap (update_vimap_slot F vimap i m s)
      (if mx < m then m else mx) efmls)
End

Theorem vimap_rel_mk_vimap:
  ∀l k fmlls vimap mx.
  vimap_rel fmlls vimap ⇒
  vimap_rel
    (FOLDL (λacc (i,v). update_resize acc Empty (enc v b) i) fmlls
      (enumerate k l))
    (FST (mk_vimap vimap mx (enumerate k (MAP (λc. enc c b) l))))
Proof
  Induct>>rw[miscTheory.enumerate_def,mk_vimap_def]>>
  first_x_assum irule>>
  irule vimap_rel_update_resize_update_vimap_slot>>
  simp[]
QED

(* the returned maximum bounds the variables of the model *)
Theorem mk_vimap_bound:
  ∀l k vimap mx.
  mx ≤ SND (mk_vimap vimap mx (enumerate k (MAP (λc. enc c b) l))) ∧
  EVERY (λc. slot_bound (enc c b')
    (SND (mk_vimap vimap mx (enumerate k (MAP (λc. enc c b) l))) + 1)) l
Proof
  Induct>>rw[miscTheory.enumerate_def,mk_vimap_def]>>
  qmatch_goalsub_abbrev_tac`SND (mk_vimap vimap1 mx1 _)`>>
  first_x_assum (qspecl_then [`k+1`,`vimap1`,`mx1`] strip_assume_tac)>>
  gvs[Abbr`mx1`]>>
  irule slot_bound_mono>>
  irule_at Any slot_bound_enc_max_var>>
  simp[]
QED

Theorem init_state_rels:
  fmls = MAP (λc. enc c T) fml ∧
  EVERY (λs. slot_bound s (LENGTH assg)) fmls ∧
  (∃dm. dm_rel dm assg st) ∧
  fmlls = FOLDL (λacc (i,v). update_resize acc Empty v i)
      (REPLICATE m Empty) (enumerate 1 fmls) ∧
  inds = REVERSE (MAP FST (enumerate 1 fmls)) ∧
  vimap = FST (mk_vimap (REPLICATE k Vnone) 0 (enumerate 1 fmls)) ∧
  vomap = mk_vomap_opt obj ∧
  pc = init_conf (LENGTH fml + 1) chk pres obj ⇒
  fml_rel (build_fml T 1 fml) fmlls ∧
  ind_rel fmlls inds ∧
  vimap_rel fmlls vimap ∧
  vomap_rel pc.obj vomap ∧
  (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty) ∧
  rup_inv fmlls assg st ∧
  id_ok (build_fml T 1 fml) pc.id ∧
  all_core (build_fml T 1 fml)
Proof
  strip_tac>>
  gvs[]>>
  rpt conj_tac
  >- simp[fml_rel_FOLDL_update_resize]
  >- simp[ind_rel_FOLDL_update_resize]
  >- (
    rw[FOLDL_enumerate_MAP]>>
    irule vimap_rel_mk_vimap>>
    rw[vimap_rel_def,any_el_ALT,EL_REPLICATE])
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
    (FST (mk_vimap (REPLICATE k Vnone) 0 (enumerate 1 fmls)))
    (mk_vomap_opt obj)
    (init_conf (LENGTH fml + 1) chk pres obj) =
    SOME(fmlls',assg',st',inds',vimap',vomap',pc') ∧
  check_hconcl_list fmls obj fmlls'
    pc'.obj pc'.bound pc'.dbound pc'.enum hconcl ⇒
  sem_concl (set fml) obj (pres_set_spt pres) (hconcl_concl hconcl)
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`check_csteps_list cs fmlls assg st
    inds vimap vomap pc = _`>>
  `fml_rel (build_fml T 1 fml) fmlls ∧ ind_rel fmlls inds ∧
   vimap_rel fmlls vimap ∧ vomap_rel pc.obj vomap ∧
   (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty) ∧
   rup_inv fmlls assg st ∧
   id_ok (build_fml T 1 fml) pc.id ∧ all_core (build_fml T 1 fml)` by (
    irule init_state_rels>>
    simp[Abbr`fmlls`,Abbr`inds`,Abbr`vimap`,Abbr`vomap`,Abbr`pc`]>>
    metis_tac[])>>
  drule_all fml_rel_check_csteps_list>>
  rw[]>>
  drule check_csteps_check_hconcl>>
  rpt(disch_then drule)>>
  disch_then match_mp_tac>>simp[core_only_fml_build_fml]>>
  drule_all fml_rel_check_hconcl_list>>
  fs[Abbr`pc`,init_conf_def]>>
  metis_tac[]
QED

Definition check_output_list_def:
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' NoOutput = T) ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Derivable =
    let cls = MAP SND (core_fmlls fml inds) in
      dbound = NONE ∧ fml_include_slots cls fml') ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Equisatisfiable =
    let cls = MAP SND (core_fmlls fml inds) in
      dbound = NONE ∧ bound = NONE ∧
      chk ∧
      fml_include_slots cls fml' ∧
      fml_include_slots fml' cls) ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Equioptimal =
    let cls = MAP SND (core_fmlls fml inds) in
      chk ∧ opt_le bound dbound ∧
      fml_include_slots cls fml' ∧
      fml_include_slots fml' cls ∧
      opt_eq_obj obj obj') ∧
  (check_output_list fml inds
    pres obj bound dbound chk fml' pres' obj' Equisolvable =
    let cls = MAP SND (core_fmlls fml inds) in
      chk ∧ opt_le bound dbound ∧
      fml_include_slots cls fml' ∧
      fml_include_slots fml' cls ∧
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
  check_output_list fmlls' inds' pres obj bound dbound chk
    (MAP (λc. enc c T) fmlt) prest objt output ⇒
  check_output fml' pres obj bound dbound chk fmlt prest objt output
Proof
  rw[]>>
  drule_all core_fmlls_mk_core_fml>> strip_tac>>
  `EVERY (λs. s ≠ Empty) (MAP SND (core_fmlls fmlls' inds'))` by
    simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,FORALL_PROD,MEM_core_fmlls]>>
  `EVERY (λs. s ≠ Empty) (MAP (λc. enc c T) fmlt)` by
    simp[EVERY_MAP]>>
  `MAP dec (MAP (λc. enc c T) fmlt) = fmlt` by
    simp[MAP_MAP_o,o_DEF]>>
  Cases_on`output`>>
  fs[check_output_list_def,check_output_def]>>rw[]>>
  imp_res_tac fml_include_slots_thm>>gvs[]>>
  metis_tac[fml_include_set]
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
    (FST (mk_vimap (REPLICATE k Vnone) 0 (enumerate 1 fmls)))
    (mk_vomap_opt obj)
    (init_conf (LENGTH fml + 1) chk pres obj) =
    SOME(fmlls',assg',st',inds',vimap',vomap',pc') ∧
  fmlts = MAP (λc. enc c T) fmlt ∧
  check_output_list fmlls' inds'
    pc'.pres pc'.obj pc'.bound pc'.dbound pc'.chk fmlts prest objt output ⇒
  sem_output (set fml) obj (pres_set_spt pres) pc'.bound (set fmlt) objt (pres_set_spt prest) output
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`check_csteps_list cs fmlls assg st
    inds vimap vomap pc = _`>>
  `fml_rel (build_fml T 1 fml) fmlls ∧ ind_rel fmlls inds ∧
   vimap_rel fmlls vimap ∧ vomap_rel pc.obj vomap ∧
   (∀n. n ≥ pc.id ⇒ any_el n fmlls Empty = Empty) ∧
   rup_inv fmlls assg st ∧
   id_ok (build_fml T 1 fml) pc.id ∧ all_core (build_fml T 1 fml)` by (
    irule init_state_rels>>
    simp[Abbr`fmlls`,Abbr`inds`,Abbr`vimap`,Abbr`vomap`,Abbr`pc`]>>
    metis_tac[])>>
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
