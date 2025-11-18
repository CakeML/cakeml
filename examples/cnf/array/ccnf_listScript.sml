(*
  This refines the CCNF functions to a fixed-size, list-based implementation.
*)
Theory ccnf_list
Ancestors
  cnf ccnf
Libs
  preamble basis blastLib

(* TODO: move? *)
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
  <+ b is NONE,
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
      if b <+ any_el (Num c) dml (b-1w)
      then
        all_assigned_list dml b v i1
      else F
End

Definition dm_rel_def:
  dm_rel dm dml (b:word8) ⇔
  0w <+ b ∧ b <+ 255w ∧
  ∀n.
    (FLOOKUP dm n = NONE ⇔ (any_el n dml (b-1w) <+ b)) ∧
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
  Cases_on`x`>>gvs[]>>
  `b <+ b+1w` by FULL_BBLAST_TAC>>
  simp[]
QED

Definition assert_def:
  assert P x =
    if P then x else NONE
End

Definition all_assigned_list'_def:
  all_assigned_list' dml (b:word8) v (i:num) =
  if i = 0 then SOME T
  else
    let i1 = i - 1 in
    assert (i1 < length v)
    let c = sub v i1 in
    if c < 0
    then
      assert (Num (-c) < LENGTH dml)
      if EL (Num (-c)) dml = b
      then
        all_assigned_list' dml b v i1
      else
        SOME F
    else
      assert (Num c < LENGTH dml)
      if b <+ any_el (Num c) dml (b-1w)
      then
        all_assigned_list' dml b v i1
      else SOME F
End

Theorem assert_cond[simp]:
  assert x y = SOME res ⇔
  x ∧ y = SOME res
Proof
  Cases_on`y`>>rw[assert_def]>>
  metis_tac[]
QED

Theorem IS_SOME_assert[simp]:
  IS_SOME(assert x y) ⇔
  x ∧ (x ⇒ IS_SOME y)
Proof
  Cases_on`y`>>rw[assert_def]
QED

Theorem all_assigned_list':
  ∀dml b v i res.
  all_assigned_list' dml b v i = SOME res ⇒
  all_assigned_list dml b v i = res
Proof
  ho_match_mp_tac all_assigned_list_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once all_assigned_list_def,
       Once all_assigned_list'_def]>>
  every_case_tac>>gvs[any_el_ALT,AllCaseEqs()]
QED

Definition delete_literals_sing_list_def:
  delete_literals_sing_list dml b v i =
  if i = 0 then SOME (T,dml)
  else
    let i1 = i - 1 in
    let c = sub v i1 in
    if c < 0
    then
      let nc = Num (-c) in
      if any_el nc dml (b-1w) = b
      then
        delete_literals_sing_list dml b v i1
      else
        (if all_assigned_list dml b v i1
          then SOME (F,
            update_resize dml (b-1w) (b+1w) nc)
          else NONE)
    else
      let nc = Num c in
      if b <+ any_el nc dml (b-1w)
      then
        delete_literals_sing_list dml b v i1
      else
        (if all_assigned_list dml b v i1
          then SOME (F,
            update_resize dml (b-1w) b nc)
          else NONE)
End

Theorem dm_rel_update_resize:
  dm_rel dm dml b ∧
  bbb = (if bb then b+1w else b) ∧
  b1 = b-1w ∧
  nn = n ⇒
  dm_rel (dm |+ (n,bb))
    (update_resize dml b1 bbb nn) b
Proof
  rw[dm_rel_def,any_el_update_resize,FLOOKUP_UPDATE]>>
  rw[]>>
  FULL_BBLAST_TAC
QED

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
    strip_tac>>
    IF_CASES_TAC
    >- (
      gvs[]>>every_case_tac>>gvs[]>>
      FULL_BBLAST_TAC)>>
    IF_CASES_TAC>>rw[]>>
    gvs[]>>every_case_tac>>gvs[]>>
    irule dm_rel_update_resize>>simp[])>>
  DEP_REWRITE_TAC[all_assigned_list]>>simp[]>>
  qpat_assum`dm_rel _ _ _` mp_tac>>
  PURE_REWRITE_TAC[Once dm_rel_def]>>
  strip_tac>>
  IF_CASES_TAC
  >- (
    gvs[]>>every_case_tac>>gvs[]>>
    FULL_BBLAST_TAC)>>
  IF_CASES_TAC>>rw[]>>
  gvs[]>>every_case_tac>>gvs[]
  >- (irule dm_rel_update_resize>>simp[])
  >- FULL_BBLAST_TAC
  >- (irule dm_rel_update_resize>>simp[])
QED

Definition delete_literals_sing_list'_def:
  delete_literals_sing_list' dml b v i =
  if i = 0 then SOME (SOME (T,dml))
  else
    let i1 = i - 1 in
    assert (i1 < length v)
    let c = sub v i1 in
    if c < 0
    then
      let nc = Num (-c) in
      assert (nc < LENGTH dml)
      (if EL nc dml = b
      then
        delete_literals_sing_list' dml b v i1
      else
        OPTION_MAP
        (λres.
          if res
          then SOME (F, LUPDATE (b+1w) nc dml)
          else NONE)
        (all_assigned_list' dml b v i1)
      )
    else
      let nc = Num c in
      assert (nc < LENGTH dml)
      (if b <+ any_el nc dml (b-1w)
      then
        delete_literals_sing_list' dml b v i1
      else
        OPTION_MAP
        (λres.
          if res
          then SOME (F, LUPDATE b nc dml)
          else NONE)
        (all_assigned_list' dml b v i1))
End

Theorem delete_literals_sing_list':
  ∀dml b v i res.
  delete_literals_sing_list' dml b v i = SOME res ⇒
  delete_literals_sing_list dml b v i = res
Proof
  ho_match_mp_tac delete_literals_sing_list_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once delete_literals_sing_list_def,
       Once delete_literals_sing_list'_def]>>
  every_case_tac>>
  gvs[any_el_ALT,AllCaseEqs(),update_resize_def]>>
  rw[]>>
  metis_tac[all_assigned_list']
QED

(* Clause which is bounded in size *)
Definition bnd_clause_def:
  bnd_clause v sz ⇔
  ∀n. n < length v ⇒
    Num (ABS (sub v n)) < sz
End

Theorem bnd_clause_imp:
  bnd_clause v sz ∧
  n ≠ 0 ∧ n ≤ length v ∧
  nn = Num (ABS (sub v (n - 1))) ⇒
  nn < sz
Proof
  rw[bnd_clause_def]
QED

Theorem all_assigned_list'_SOME:
  ∀dml b v i res.
  bnd_clause v (LENGTH dml) ∧
  i ≤ length v ⇒
  IS_SOME (all_assigned_list' dml b v i)
Proof
  ho_match_mp_tac all_assigned_list'_ind>>
  rw[]>>
  simp[Once all_assigned_list'_def]>>
  rw[]>>
  gvs[any_el_ALT]>>
  drule_then irule bnd_clause_imp>>
  rpt(first_x_assum (irule_at Any))>>
  intLib.ARITH_TAC
QED

Theorem delete_literals_sing_list'_SOME:
  ∀dml b v i res.
  bnd_clause v (LENGTH dml) ∧
  i ≤ length v ⇒
  IS_SOME (delete_literals_sing_list' dml b v i)
Proof
  ho_match_mp_tac delete_literals_sing_list'_ind>>
  rw[]>>
  simp[Once delete_literals_sing_list'_def]>>
  rw[]>>
  gvs[any_el_ALT,IS_SOME_MAP]
  >>~[`all_assigned_list'`]
  >- (irule all_assigned_list'_SOME>>gvs[])
  >- (irule all_assigned_list'_SOME>>gvs[])>>
  drule_then irule bnd_clause_imp>>
  rpt(first_x_assum (irule_at Any))>>
  intLib.ARITH_TAC
QED

Theorem delete_literals_sing_list'_LENGTH:
  ∀dml b v i.
  delete_literals_sing_list' dml b v i =
    SOME(SOME(res,dml')) ⇒
  LENGTH dml = LENGTH dml'
Proof
  ho_match_mp_tac delete_literals_sing_list'_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once delete_literals_sing_list'_def]>>
  rw[]>>gvs[]
QED

(* Ensures that the dml is of sufficient size
  and properly reset *)
Definition reset_dm_list_def:
  reset_dm_list dml b sz =
  if LENGTH dml < sz then
    (REPLICATE (2 * sz) 0w, 1w)
  else
    if b <+ 253w
    then (dml,b+2w)
    else (REPLICATE (LENGTH dml) 0w, 1w)
End

Theorem dm_rel_FEMPTY_REPLICATE:
  dm_rel FEMPTY (REPLICATE n 0w) 1w
Proof
  pure_rewrite_tac[dm_rel_def]>>
  rw[any_el_ALT,EL_REPLICATE]
QED

Theorem dm_rel_imp_any_el:
  dm_rel dm dml b ∧ b <+ 253w ⇒
  any_el n dml (b-1w) <+ b+2w
Proof
  rw[dm_rel_def]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  Cases_on`FLOOKUP dm n`>>gvs[]>>
  FULL_BBLAST_TAC
QED

Theorem dm_rel_reset_dm_list:
  dm_rel dm dml b ∧
  reset_dm_list dml b sz = (dml',b') ⇒
  dm_rel FEMPTY dml' b' ∧ sz ≤ LENGTH dml'
Proof
  rw[reset_dm_list_def]>>
  fs[LENGTH_REPLICATE,dm_rel_FEMPTY_REPLICATE]>>
  drule dm_rel_imp_any_el>>
  fs[dm_rel_def]>>rw[]
  >- FULL_BBLAST_TAC
  >- FULL_BBLAST_TAC>>
  pop_assum (qspec_then`n` assume_tac)>>
  fs[any_el_ALT]>>rw[]>>gvs[]>>
  FULL_BBLAST_TAC
QED

(* The standard fml rel *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀n.
    any_el n fmlls NONE = lookup n fml
End

Definition bnd_fml_def:
  bnd_fml fmlls sz ⇔
  ∀n v.
    any_el n fmlls NONE = SOME v ⇒
    bnd_clause v sz
End

(* Unit propagating on an array *)
Definition unit_prop_list_def:
  (unit_prop_list fmlls dml b [] = SOME (F,dml)) ∧
  (unit_prop_list fmlls dml b (i::is) =
  case any_el i fmlls NONE of
    NONE => NONE
  | SOME c =>
  case delete_literals_sing_list dml b c (length c) of
    NONE => NONE
  | SOME (T,dml') => SOME (T,dml')
  | SOME (F,dml') => unit_prop_list fmlls dml' b is)
End

Theorem unit_prop_list:
  ∀is dm dml dml'.
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  unit_prop_list fmlls dml b is = SOME (res,dml') ⇒
  ∃dm'.
    unit_prop_vec fml dm is = SOME (res,dm') ∧
    dm_rel dm' dml' b
Proof
  Induct>>rw[unit_prop_vec_def,unit_prop_list_def]>>
  gvs[AllCaseEqs(),PULL_EXISTS,fml_rel_def]>>
  drule_all delete_literals_sing_list>>rw[]>>
  simp[]>>
  metis_tac[]
QED

Definition unit_prop_list'_def:
  (unit_prop_list' fmlls dml b [] =
    SOME (SOME (F,dml))) ∧
  (unit_prop_list' fmlls dml b (i::is) =
  case any_el i fmlls NONE of
    NONE => SOME NONE
  | SOME c =>
  OPTION_BIND
    (delete_literals_sing_list' dml b c (length c))
    (λres.
    case res of
      NONE => SOME NONE
    | SOME (T,dml') => SOME (SOME (T,dml'))
    | SOME (F,dml') => unit_prop_list' fmlls dml' b is))
End

Theorem unit_prop_list':
  ∀is dml res.
  unit_prop_list' fmlls dml b is = SOME res ⇒
  unit_prop_list fmlls dml b is = res
Proof
  Induct>>
  rw[unit_prop_list_def,unit_prop_list'_def]>>
  gvs[AllCaseEqs()]>>
  drule delete_literals_sing_list'>>rw[]
QED

Theorem IS_SOME_OPTION_BIND:
  IS_SOME (OPTION_BIND opt f) ⇔
  IS_SOME opt ∧
  ∀v. opt = SOME v ⇒ IS_SOME (f v)
Proof
  Cases_on`opt`>>rw[]
QED

Theorem unit_prop_list'_SOME:
  ∀is dml res.
  bnd_fml fmlls (LENGTH dml) ⇒
  IS_SOME (unit_prop_list' fmlls dml b is)
Proof
  Induct>>
  rw[unit_prop_list'_def]>>
  every_case_tac>>gvs[IS_SOME_OPTION_BIND]>>
  rw[]
  >- (
    irule delete_literals_sing_list'_SOME>>
    gvs[bnd_fml_def,any_el_ALT]>>
    metis_tac[])>>
  every_case_tac>>fs[]>>
  first_x_assum irule>>
  drule delete_literals_sing_list'_LENGTH>>
  metis_tac[]
QED

Theorem unit_prop_list'_LENGTH:
  ∀is dml.
  unit_prop_list' fmlls dml b is = SOME (SOME (res,dml')) ⇒
  LENGTH dml = LENGTH dml'
Proof
  Induct>>
  rw[unit_prop_list'_def]>>
  gvs[AllCaseEqs()]>>
  drule delete_literals_sing_list'_LENGTH>>
  rw[]
QED

Definition init_lit_map_list_def:
  init_lit_map_list i v dml b =
  if i = 0
  then dml
  else
    let i1 = i - 1 in
    let d = sub v i1 in
    let (bb,nc) = if d > 0 then (b+1w, d) else (b,-d) in
    init_lit_map_list i1 v (update_resize dml (b-1w) bb (Num nc)) b
End

Theorem init_lit_map_list:
  ∀i v dml b dm.
  dm_rel dm dml b ⇒
  dm_rel (init_lit_map_vec i v dm) (init_lit_map_list i v dml b) b
Proof
  ho_match_mp_tac init_lit_map_list_ind>>
  rpt gen_tac>>strip_tac>>
  rw[Once init_lit_map_list_def,Once init_lit_map_vec_def]>>
  fs[] >>
  first_x_assum irule>>simp[]>>
  irule dm_rel_update_resize>>
  simp[]>>
  intLib.ARITH_TAC
QED

Definition init_lit_map_list'_def:
  init_lit_map_list' i v dml b =
  if i = 0
  then SOME dml
  else
    let i1 = i - 1 in
    assert (i1 < length v)
    let d = sub v i1 in
    let (bb,nc) = (if d > 0 then (b+1w, d) else (b,-d)) in
    init_lit_map_list' i1 v
      (LUPDATE bb (Num nc) dml) b
End

Theorem update_resize_LUPDATE:
  n < LENGTH ls ⇒
  update_resize ls def v n = LUPDATE v n ls
Proof
  rw[update_resize_def]
QED

Theorem init_lit_map_list':
  ∀i v dml b.
  bnd_clause v (LENGTH dml) ∧
  i ≤ length v ∧
  init_lit_map_list' i v dml b = SOME res ⇒
  init_lit_map_list i v dml b = res
Proof
  ho_match_mp_tac init_lit_map_list_ind>>
  rpt gen_tac>>strip_tac>>
  rw[Once init_lit_map_list_def,Once init_lit_map_list'_def]>>
  fs[] >>
  first_x_assum irule>>
  DEP_REWRITE_TAC[update_resize_LUPDATE]>>
  simp[]>>
  drule_then irule bnd_clause_imp>>
  first_x_assum $ irule_at Any>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem init_lit_map_list'_SOME:
  ∀i v dml b.
  bnd_clause v (LENGTH dml) ∧
  i ≤ length v ⇒
  IS_SOME (init_lit_map_list' i v dml b)
Proof
  ho_match_mp_tac init_lit_map_list'_ind>>
  rpt gen_tac>>strip_tac>>
  rw[Once init_lit_map_list'_def]
QED

Definition sz_lit_map_list_def:
  sz_lit_map_list i v m =
  if i = 0
  then
    m
  else
    let i1 = i - 1 in
    let d = Num (ABS (sub v i1)) in
    if d < m
    then
      sz_lit_map_list i1 v m
    else
      sz_lit_map_list i1 v (d+1)
End

Theorem sz_lit_map_list_inc:
  ∀i v m.
  m ≤ sz_lit_map_list i v m
Proof
  ho_match_mp_tac sz_lit_map_list_ind>>
  rw[]>>
  simp[Once sz_lit_map_list_def]
QED

Theorem sz_lit_map_list_bnd_clause:
  ∀i v m m'.
  i ≤ length v ∧
  sz_lit_map_list i v m = m' ⇒
  ∀j. j < i ⇒
    Num (ABS (sub v j)) < m'
Proof
  ho_match_mp_tac sz_lit_map_list_ind>>
  rw[]>>
  simp[Once sz_lit_map_list_def]>>
  rw[]>>gvs[]>>
  Cases_on`j < i - 1`>>gvs[]>>
  `j = i -1` by fs[]>>
  gvs[]
  >- (
    qspecl_then[`i-1`,`v`,`m`] assume_tac sz_lit_map_list_inc>>
    fs[])>>
  rename1`Num mm`>>
  qspecl_then[`i-1`,`v`,`Num mm + 1`] assume_tac sz_lit_map_list_inc>>
  fs[]
QED

Definition sz_lit_map_list'_def:
  sz_lit_map_list' i v m =
  if i = 0
  then
    SOME m
  else
    let i1 = i - 1 in
    assert (i1 < length v)
    let d = Num (ABS (sub v i1)) in
    if d < m
    then
      sz_lit_map_list' i1 v m
    else
      sz_lit_map_list' i1 v (d+1)
End

Theorem sz_lit_map_list':
  ∀i v m.
  sz_lit_map_list' i v m = SOME res ⇒
  sz_lit_map_list i v m = res
Proof
  ho_match_mp_tac sz_lit_map_list_ind>>
  rpt gen_tac>>strip_tac>>
  rw[Once sz_lit_map_list_def,Once sz_lit_map_list'_def]>>
  fs[]
QED

Theorem sz_lit_map_list'_SOME:
  ∀i v m.
  i ≤ length v ⇒
  IS_SOME (sz_lit_map_list' i v m)
Proof
  ho_match_mp_tac sz_lit_map_list'_ind>>
  rpt gen_tac>>strip_tac>>
  rw[Once sz_lit_map_list'_def]
QED

(* Automatically resize the dml if needed for the new clause
*)
Definition prepare_rup_def:
  prepare_rup dml b v =
  let lv = length v in
  let sz = sz_lit_map_list lv v 0 in
  let (dml',b') = reset_dm_list dml b sz in
  let dml'' = init_lit_map_list lv v dml' b' in
    (dml'',b')
End

(* TODO: prepare_rup should be unconditional,
  not sure if this is the right theorem... *)

Definition is_rup_list_def:
  is_rup_list fmlls dml b v is =
  let (dml',b') = prepare_rup dml b v in
  case unit_prop_list fmlls dml' b' is of
    SOME (T,dml'') => (T,dml'',b')
  | _ => (F, (dml',b'))
End

Theorem is_rup_list:
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  is_rup_list fmlls dml b v is = (T, (dml',b')) ⇒
  is_rup fml v is ∧
  ∃dm'. dm_rel dm' dml' b'
Proof
  strip_tac>>
  gvs[is_rup_list_def,UNCURRY_EQ,AllCaseEqs(),prepare_rup_def]>>
  drule_all dm_rel_reset_dm_list>>
  strip_tac>>
  drule unit_prop_list>>
  disch_then $ drule_at (Pos (el 2))>>
  simp[is_rup_def]>>
  drule init_lit_map_list>>
  rw[AllCasePreds()]>>
  metis_tac[]
QED

Definition is_rup_list'_def:
  is_rup_list' fmlls dml b v is =
  let (dml',b') = prepare_rup dml b v in
  OPTION_MAP
  (λres.
    case res of
      SOME (T,dml'') => (T,dml'',b')
    | _ => (F, (dml',b')))
  (unit_prop_list' fmlls dml' b' is)
End

Theorem is_rup_list':
  is_rup_list' fmlls dml b v is = SOME res ⇒
  is_rup_list fmlls dml b v is = res
Proof
  rw[is_rup_list'_def,is_rup_list_def]>>
  gvs[UNCURRY_EQ,AllCaseEqs()]>>
  drule unit_prop_list'>>rw[]
QED

Theorem prepare_rup_LENGTH:
  prepare_rup dml b v = (dml',b') ⇒
  LENGTH dml ≤ LENGTH dml'
Proof
  rw[prepare_rup_def]>>
  gvs[UNCURRY_EQ]>>
  (* annoying! *)
  cheat
QED

Theorem is_rup_list'_SOME:
  bnd_fml fmlls (LENGTH dml) ⇒
  IS_SOME (is_rup_list' fmlls dml b v is)
Proof
  rw[is_rup_list'_def]>>
  pairarg_tac>>gvs[IS_SOME_MAP]>>
  irule unit_prop_list'_SOME>>
  drule prepare_rup_LENGTH>>
  fs[bnd_fml_def,bnd_clause_def]>>
  rw[]>>
  first_x_assum drule_all>>
  fs[]
QED

Definition delete_ids_list_def:
  (delete_ids_list [] fml = fml) ∧
  (delete_ids_list (i::is) fml =
    if LENGTH fml ≤ i
    then delete_ids_list is fml
    else delete_ids_list is (LUPDATE NONE i fml))
End

Theorem delete_ids_list_FOLDL:
  ∀l fmlls.
  delete_ids_list l fmlls =
  FOLDL (\fml i.
    if LENGTH fml ≤ i then fml else LUPDATE NONE i fml) fmlls l
Proof
  Induct>>rw[delete_ids_list_def]
QED

Theorem LENGTH_delete_ids_list[simp]:
  ∀l.
  LENGTH (delete_ids_list l fmlls) = LENGTH fmlls
Proof
  simp[delete_ids_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]
QED

Theorem fml_rel_delete_ids_list:
  ∀l fml fmlls fmlls'.
  fml_rel fml fmlls ∧
  delete_ids_list l fmlls = fmlls' ⇒
  fml_rel (delete_ids fml l) fmlls'
Proof
  simp[delete_ids_def,delete_ids_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]>>
  first_x_assum drule>>
  rw[fml_rel_def]
  >- (
    rw[lookup_delete]>>
    first_x_assum(qspec_then`h` (assume_tac o SYM))>>
    fs[any_el_ALT])>>
  rw[any_el_ALT,EL_LUPDATE,lookup_delete]>>
  first_x_assum(qspec_then`n` assume_tac)>>
  gvs[any_el_ALT]
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert n v fml) (update_resize fmlls NONE (SOME v) n)
Proof
  rw[update_resize_def,fml_rel_def,any_el_ALT,EL_LUPDATE]>>
  rw[lookup_insert]>>
  gvs[AllCaseEqs()]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    fs[EL_APPEND_EQN]>>
    rw[]>>fs[EL_REPLICATE,LENGTH_REPLICATE]>>
    metis_tac[]) >>
  rename1`lookup nn fml`>>
  first_x_assum(qspec_then`nn` assume_tac)>>rfs[]
QED

Theorem bnd_fml_update_resize:
  bnd_fml fmlls sz ∧ bnd_clause v sz ⇒
  bnd_fml (update_resize fmlls NONE (SOME v) n) sz
Proof
  rw[bnd_fml_def,any_el_update_resize]>>
  gvs[AllCaseEqs()]>>
  metis_tac[]
QED
