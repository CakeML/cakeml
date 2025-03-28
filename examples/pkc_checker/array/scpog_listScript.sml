(*
  This refines the SCPOG checker to a fixed-size, list-based implementation.
*)
open preamble basis cnf_scpogTheory mlvectorTheory;

val _ = new_theory "scpog_list"

Definition w8z_def:
  w8z = (0w:word8)
End

Definition w8o_def:
  w8o = (1w:word8)
End

Definition index_def:
  index (i:int) =
  if i ≤ 0 then
    2 * Num(-i)
  else
    2 * Num(i) - 1
End

(* optimized for is_rup  step *)
Definition delete_literals_sing_list_def:
  (delete_literals_sing_list Clist [] = SOME 0) ∧
  (delete_literals_sing_list Clist (c::cs) =
  if any_el (index c) Clist (w8z) = w8o
  then delete_literals_sing_list Clist cs
  else (* c should be the only literal left *)
    if EVERY (λi. any_el (index i) Clist w8z = w8o) cs
    then SOME (~c)
    else NONE)
End

Definition is_rup_list_aux_def:
  (is_rup_list_aux is_struct fml [] C Clist = NONE) ∧
  (is_rup_list_aux is_struct fml (i::is) C Clist =
  case any_el i fml NONE of
    NONE => NONE
  | SOME (c,tag) =>
  if is_struct ⇒ tag then
    case delete_literals_sing_list Clist c of
      NONE => NONE
    | SOME nl =>
      if nl = 0 then SOME (C, Clist)
      else is_rup_list_aux is_struct fml is (nl::C) (update_resize Clist w8z w8o (index nl))
  else NONE)
End

Definition set_list_def:
  (set_list Clist v [] = Clist) ∧
  (set_list Clist v (c::cs) =
    set_list (update_resize Clist w8z v (index c)) v cs)
End

Definition is_rup_list_def:
  is_rup_list is_struct fml ls c Clist =
  let Clist = set_list Clist w8o c in
  case is_rup_list_aux is_struct fml ls c Clist of
    NONE => NONE
  | SOME (c, Clist) => SOME (set_list Clist w8z c)
End

Definition list_max_index_def:
  list_max_index C = 2*MAX_LIST (MAP (λc. Num (ABS c)) C) + 1
End

(* bump up the length to a large number *)
Definition resize_Clist_def:
  resize_Clist C Clist =
  if LENGTH Clist ≤ list_max_index C then
    REPLICATE (2 * (list_max_index C)) w8z
  else Clist
End

Definition insert_one_list_def:
  insert_one_list tag fml i c =
    case any_el i fml NONE of
      NONE => SOME (update_resize fml NONE (SOME (c,tag)) i)
    | SOME _ => NONE
End

Definition insert_list_list_def:
  (insert_list_list tag fml i [] = SOME fml) ∧
  (insert_list_list tag fml i (c::cs) =
  case insert_one_list tag fml i c of
    NONE => NONE
  | SOME fml' => insert_list_list tag fml' (i+1) cs)
End

Definition arb_delete_list_def:
  (arb_delete_list nc [] fml = SOME fml) ∧
  (arb_delete_list nc (i::is) fml =
    if i ≤ nc then NONE
    else
    case any_el i fml NONE of
      NONE => NONE
    | SOME (c,tag) =>
      if tag then NONE
      else arb_delete_list nc is (LUPDATE NONE i fml))
End

Definition fold_resize_Clist_def:
  fold_resize_Clist cs Clist =
  FOLDL (λx e. resize_Clist e x) Clist cs
End

Definition check_scpstep_list_def:
  check_scpstep_list scpstep pc fml sc Clist =
  case scpstep of
    Skip => SOME (fml, sc, Clist)
  | Root l =>
    OPTION_MAP (λsc'. (fml,sc',Clist)) (declare_root sc l)
  | RupAdd b n c i0 =>
    (let Clist = resize_Clist c Clist in
    case
      is_rup_list b fml i0 c Clist of
      NONE => NONE
    | SOME Clist =>
      if
        EVERY (λi. ¬is_fresh pc sc (var_lit i) ∧ i ≠ 0) c
      then
        OPTION_MAP (λfml'. (fml',sc,Clist))
          (insert_one_list b fml n c)
      else NONE)
  | ArbDel ls =>
    OPTION_MAP (λfml'. (fml',sc,Clist))
      (arb_delete_list pc.nc ls fml)
  | DeclPro n v ls =>
    (case declare_pro pc sc v ls of
      SOME (cs,sc') =>
        let Clist = fold_resize_Clist cs Clist in
        OPTION_MAP (λfml'. (fml',sc',Clist))
          (insert_list_list T fml n cs)
    | NONE => NONE)
  | DeclSum n v l1 l2 i0 =>
    (let c = [-l1;-l2] in
    let Clist = resize_Clist c Clist in
    case is_rup_list T fml i0 c Clist of
      NONE => NONE
    | SOME Clist =>
      (case declare_sum pc sc v l1 l2 of
        SOME (cs,sc') =>
          let Clist = fold_resize_Clist cs Clist in
          OPTION_MAP (λfml'. (fml',sc',Clist))
            (insert_list_list T fml n cs)
      | NONE => NONE))
  | DeclSko n v ls =>
    (case declare_sko pc sc v ls of
      SOME (cT,sc') =>
        let Clist = resize_Clist cT Clist in
        OPTION_MAP (λfml'. (fml',sc',Clist))
        (insert_one_list T fml n cT)
    | NONE => NONE)
End

(* semantic *)
Definition check_scpsteps_list_def:
  (check_scpsteps_list [] pc fml sc Clist =
    SOME (fml, sc, Clist)) ∧
  (check_scpsteps_list (x::xs) pc fml sc Clist =
    case check_scpstep_list x pc fml sc Clist of
      NONE => NONE
    | SOME (fml', sc', Clist') =>
      check_scpsteps_list xs pc fml' sc' Clist')
End

(* prove that check_scpstep_list implements check_scpstep *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x.
  if x < LENGTH fmlls then
    lookup x fml = EL x fmlls
  else
    lookup x fml = NONE
End

Theorem fml_rel_any_el:
  fml_rel fml fmlls ⇒
  any_el i fmlls NONE = lookup i fml
Proof
  rw[fml_rel_def,any_el_ALT]>>
  first_x_assum(qspec_then`i` mp_tac)>>
  rw[]
QED

(* Require that the lookup table matches a clause exactly *)
Definition lookup_rel_def:
  lookup_rel C Clist ⇔
  (* elements are either 0 or 1 *)
  (∀i. MEM i Clist ⇒ i = w8z ∨ i = w8o) ∧
  (* where 1 indicates membership in C *)
  (∀i. any_el (index i) Clist w8z = w8o ⇔ MEM i C)
End

Theorem delete_literals_sing_list_correct:
  ∀ls.
  lookup_rel C Clist ∧ wf_clause ls ⇒
  case delete_literals_sing_list Clist ls of
    NONE => LENGTH (delete_literals ls C) > 1
  | SOME 0 => delete_literals ls C = []
  | SOME l => delete_literals ls C = [-l]
Proof
  Induct>>simp[delete_literals_sing_list_def,delete_literals_def]>>
  ntac 2 strip_tac>>fs[lookup_rel_def,wf_clause_def]>>
  IF_CASES_TAC>>simp[]
  >-
    fs[delete_literals_def]
  >>
  IF_CASES_TAC>>simp[]
  >-
    simp[FILTER_EQ_NIL]
  >>
  Cases_on`FILTER (λx. ¬MEM x C) ls` >>
  pop_assum mp_tac>> simp[FILTER_EQ_NIL,o_DEF]
QED

Theorem MEM_update_resize:
  MEM i (update_resize ls def v x) ⇒
  i = def ∨ MEM i ls ∨ i = v
Proof
  rw[update_resize_def,MEM_LUPDATE]
  >- metis_tac[MEM_EL]>>
  rw[EL_APPEND_EQN]>- metis_tac[MEM_EL]>>
  simp[EL_REPLICATE]
QED

Theorem any_el_update_resize:
  any_el y (update_resize ls def v x) def =
  if y = x then v
  else
    any_el y ls def
Proof
  simp[update_resize_def]>>
  IF_CASES_TAC
  >-
    (simp[any_el_ALT,EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[any_el_ALT,EL_LUPDATE,EL_APPEND_EQN,REPLICATE]>>
  IF_CASES_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  simp[EL_REPLICATE]
QED

Theorem index_11:
  index i = index x ⇔ i = x
Proof
  rw[index_def,EQ_IMP_THM]>>
  intLib.ARITH_TAC
QED

Theorem index_onto:
  ∃i. index i = k
Proof
  rw[index_def]>>
  qexists_tac`if k MOD 2 = 0 then -&(k DIV 2) else &((k+1) DIV 2)`>>
  rw[]>>fs[]>>simp[bitTheory.DIV_MULT_THM2]>>
  intLib.ARITH_TAC
QED

Theorem lookup_rel_cons:
  lookup_rel C Clist ⇒
  lookup_rel (x::C) (update_resize Clist w8z w8o (index x))
Proof
  rw[lookup_rel_def]
  >-
   (drule MEM_update_resize >>
   metis_tac[])>>
  simp[any_el_update_resize,index_11]>>
  IF_CASES_TAC>>metis_tac[]
QED

Theorem lookup_rel_REVERSE:
  lookup_rel (REVERSE C) Clist ⇔ lookup_rel C Clist
Proof
  rw[lookup_rel_def]
QED

Theorem fml_rel_is_rup_list_aux:
  ∀ls C Clist.
  fml_rel fml fmlls ∧ wf_fml fml ∧
  lookup_rel C Clist ⇒
  case is_rup_list_aux b fmlls ls C Clist of
    SOME (C', Clist') =>
    is_rup b fml ls C ∧ lookup_rel C' Clist'
  | NONE => ¬ is_rup b fml ls C (* Not required but should be true *)
Proof
  Induct>>fs[is_rup_list_aux_def,is_rup_def]>>rw[]>>
  DEP_REWRITE_TAC[fml_rel_any_el]>>simp[]>>
  Cases_on`lookup h fml`>>simp[]>>
  `wf_clause (FST x)` by
    (fs[wf_fml_def,range_def]>>metis_tac[FST,PAIR])>>
  drule delete_literals_sing_list_correct>>
  disch_then drule>>
  TOP_CASE_TAC>>simp[]
  >-  (every_case_tac>>fs[]) >>
  Cases_on`x`>>gvs[]>>
  Cases_on`b ⇒ r` >>gvs[]>>
  IF_CASES_TAC>>simp[]>>
  qmatch_goalsub_abbrev_tac`is_rup_list_aux _ _ _ aaa bbb`>>
  first_x_assum(qspecl_then[`aaa`,`bbb`] mp_tac)>>
  impl_tac >-
    (unabbrev_all_tac>>simp[lookup_rel_cons])>>
  TOP_CASE_TAC>>simp[]
QED

Theorem lookup_rel_set_list_lookup_rel:
  ∀D ls C.
  lookup_rel C ls ⇒
  lookup_rel (C++D) (set_list ls w8o D)
Proof
  Induct>>rw[set_list_def]>>
  `C ++ h::D = (C++[h])++D` by simp[]>>
  pop_assum SUBST_ALL_TAC>>
  first_x_assum match_mp_tac>>
  `C++[h] = REVERSE (h::REVERSE C)` by fs[]>>
  metis_tac[lookup_rel_REVERSE,lookup_rel_cons]
QED

Theorem empty_set_list_lookup_rel:
  EVERY ($= w8z) Clist ⇒
  lookup_rel C (set_list Clist w8o C)
Proof
  rw[]>>
  `lookup_rel [] Clist` by
    (fs[lookup_rel_def,EVERY_MEM,any_el_ALT]>>
    rw[]>>fs[w8z_def,w8o_def]>>
    first_x_assum(qspec_then`EL (index i) Clist` mp_tac)>>
    impl_tac>-
      simp[EL_MEM]>>
    simp[])>>
  drule lookup_rel_set_list_lookup_rel>>
  simp[]
QED

Theorem any_el_set_list:
  ∀is ls.
  any_el x (set_list ls v is) w8z =
  if ∃y. x = index y ∧ MEM y is then v
  else
    any_el x ls w8z
Proof
  Induct>>simp[set_list_def]>>
  ntac 2 strip_tac>>
  IF_CASES_TAC>-
    (fs[]>>
    metis_tac[])>>
  simp[any_el_update_resize]>>
  fs[]>>
  metis_tac[]
QED

Theorem lookup_rel_set_list_empty:
  ∀C.
  lookup_rel C Clist ⇒
  EVERY ($= w8z) (set_list Clist w8z C)
Proof
  rw[EVERY_EL]>>
  `any_el n (set_list Clist w8z C) w8z = w8z` by
    (simp[any_el_set_list]>>
    rw[]>>fs[lookup_rel_def,PULL_EXISTS]>>
    `?k. index k = n` by fs[index_onto]>>
    first_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    first_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    fs[any_el_ALT]>>
    rw[]>>fs[]>>
    first_x_assum(qspec_then `EL (index k) Clist` mp_tac)>>
    impl_tac>-
      (simp[MEM_EL]>>
      qexists_tac`index k`>>simp[])>>
    metis_tac[])>>
  rfs[any_el_ALT]
QED

Theorem fml_rel_is_rup_list:
  EVERY ($= w8z) Clist ∧ (* the array is always zero-ed before and after *)
  wf_fml fml ∧
  fml_rel fml fmlls ⇒
  (case is_rup_list b fmlls ls (C:int list) Clist of
    SOME Clist' => is_rup b fml ls C ∧ EVERY ($= w8z) Clist'
  | NONE => ¬is_rup b fml ls C)
Proof
  rw[is_rup_list_def]>>
  drule fml_rel_is_rup_list_aux>>
  simp[]>>
  drule empty_set_list_lookup_rel>>
  disch_then(qspec_then`C` assume_tac)>>
  disch_then drule>>
  disch_then(qspecl_then[`b`,`ls`] assume_tac)>>
  every_case_tac>>fs[]>>
  metis_tac[lookup_rel_set_list_empty]
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert n v fml) (update_resize fmlls NONE (SOME v) n)
Proof
  rw[update_resize_def,fml_rel_def,EL_LUPDATE]>>
  IF_CASES_TAC>> rw[lookup_insert]
  >- metis_tac[]
  >- metis_tac[]
  >-
    (first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
    fs[EL_APPEND_EQN]>>
    rw[]>>fs[EL_REPLICATE,LENGTH_REPLICATE])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]
QED

Theorem fml_rel_insert_one_list:
  fml_rel fml fmlls ∧
  insert_one_list tag fmlls n l = SOME fmlls' ⇒
  ∃fml'.
    insert_one tag fml n l = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  rw[insert_one_def,insert_one_list_def]>>
  gvs[AllCaseEqs()]>>
  drule fml_rel_any_el>>
  metis_tac[fml_rel_update_resize]
QED

Theorem fml_rel_LUPDATE_NONE:
  fml_rel fml fmlls ⇒
  fml_rel (delete n fml) (LUPDATE NONE n fmlls)
Proof
  rw[fml_rel_def]>>
  rw[lookup_delete,EL_LUPDATE]>>
  gvs[AllCasePreds(),SF DNF_ss]>>
  first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
  gvs[]
QED

Theorem fml_rel_arb_delete_list:
  ∀ls fml fmlls.
  fml_rel fml fmlls ∧
  arb_delete_list sc ls fmlls = SOME fmlls' ⇒
  ∃fml'.
    arb_delete sc ls fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>
  rw[arb_delete_def,arb_delete_list_def]>>
  gvs[AllCaseEqs()]>>
  drule fml_rel_any_el>>
  rw[]>>gvs[]>>
  first_x_assum irule>>
  first_x_assum (irule_at Any)>>
  simp[fml_rel_LUPDATE_NONE]
QED

Theorem fml_rel_insert_list_list:
  ∀ls fml fmlls n.
  fml_rel fml fmlls ∧
  insert_list_list tag fmlls n ls = SOME fmlls' ⇒
  ∃fml'.
    insert_list tag fml n ls = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>rw[insert_list_def,insert_list_list_def]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_insert_one_list>>rw[]>>
  simp[]>>
  first_x_assum irule>>
  metis_tac[]
QED

Theorem zero_resize_Clist:
  ∀l Clist.
  EVERY ($= w8z) Clist ⇒
  EVERY ($= w8z) (fold_resize_Clist l Clist)
Proof
  simp[fold_resize_Clist_def]>>
  Induct>>
  rw[]>>
  first_x_assum (irule_at Any)>>
  rw[resize_Clist_def]
QED

Theorem fml_rel_check_scpstep_list:
  fml_rel fml fmlls ∧
  EVERY ($= w8z) Clist ∧
  wf_fml fml ⇒
  case check_scpstep_list scpstep pc fmlls sc Clist of
    SOME (fmlls', sc', Clist') =>
    EVERY ($= w8z) Clist' ∧
    ∃fml'.
    check_scpstep pc fml sc scpstep =
      SOME (fml',sc') ∧
    fml_rel fml' fmlls'
  | NONE => T
Proof
  simp[check_scpstep_def,check_scpstep_list_def]>>
  strip_tac>>
  Cases_on`scpstep`>>simp[]
  >- ( (* Declare root *)
    simp[OPTION_MAP_CASE,o_DEF]>>
    every_case_tac>>simp[])
  >- ( (* RupAdd *)
    every_case_tac>>gvs[]>>
    `EVERY ($= w8z) (resize_Clist l Clist)` by
      rw[resize_Clist_def]>>
    drule_all fml_rel_is_rup_list>>
    disch_then (qspecl_then [`l0`,`b`,`l`] assume_tac)>>
    every_case_tac>>gvs[]>>
    metis_tac[fml_rel_insert_one_list])
  >- (
    simp[OPTION_MAP_CASE,o_DEF]>>
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    metis_tac[fml_rel_arb_delete_list])
  >- (
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    metis_tac[fml_rel_insert_list_list,zero_resize_Clist])
  >- (
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    qmatch_asmsub_abbrev_tac`is_rup_list A B C D E`>>
    qspecl_then [`C`,`B`,`fml`,`A`,`E`,`D`] mp_tac (GEN_ALL fml_rel_is_rup_list)>>
    unabbrev_all_tac>>simp[]>>
    impl_tac >-
      rw[resize_Clist_def]>>
    rw[]>>
    metis_tac[fml_rel_insert_list_list,zero_resize_Clist])
  >- (
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    rw[resize_Clist_def]>>
    metis_tac[fml_rel_insert_list_list,fml_rel_insert_one_list])
QED

Theorem wf_fml_insert_one:
  wf_fml fml ∧
  insert_one b fml n C = SOME fml' ∧
  wf_clause C ⇒
  wf_fml fml'
Proof
  rw[wf_fml_def,insert_one_def]>>
  gvs[AllCaseEqs()]>>
  drule range_insert_2>>
  rw[]>>
  metis_tac[]
QED

Theorem wf_fml_insert_list:
  ∀cs n fml fml'.
  wf_fml fml ∧
  insert_list b fml n cs = SOME fml' ∧
  EVERY wf_clause cs ⇒
  wf_fml fml'
Proof
  Induct>>rw[insert_list_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  metis_tac[wf_fml_insert_one]
QED

Theorem wf_fml_delete:
  wf_fml fml ⇒
  wf_fml (delete h fml)
Proof
  rw[wf_fml_def]>>
  metis_tac[range_delete,SUBSET_DEF]
QED

Theorem wf_fml_arb_delete:
  ∀l fml fml'.
  wf_fml fml ∧
  arb_delete nc l fml = SOME fml' ⇒
  wf_fml fml'
Proof
  Induct>>rw[arb_delete_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum irule>>
  pop_assum (irule_at Any)>>
  metis_tac[wf_fml_delete]
QED

Theorem check_scpstep_wf_fml:
  wf_fml fml ∧
  check_scpstep pc fml sc h = SOME (fml', sc') ⇒
  wf_fml fml'
Proof
  rw[check_scpstep_def]>>
  gvs[AllCaseEqs()]
  >- (
    irule wf_fml_insert_one>>
    first_x_assum (irule_at Any)>>
    fs[wf_clause_def,EVERY_MEM]>>
    metis_tac[])
  >- metis_tac[wf_fml_arb_delete]
  >- (
    irule wf_fml_insert_list>>
    first_x_assum (irule_at Any)>>
    gvs[declare_pro_def,mk_pro_def,check_pro_def,mk_sko_def,EVERY_MEM,MEM_MAP,wf_clause_def,PULL_EXISTS])
  >- (
    irule wf_fml_insert_list>>
    first_x_assum (irule_at Any)>>
    gvs[declare_sum_def,mk_sum_def,check_sum_def,wf_clause_def])
  >- (
    irule wf_fml_insert_one>>
    first_x_assum (irule_at Any)>>
    gvs[declare_sko_def,check_sko_def,wf_clause_def])
QED

Theorem fml_rel_check_scpsteps_list:
  ∀scpsteps fml fmlls fmlls' sc sc' Clist Clist'.
  fml_rel fml fmlls ∧
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧
  check_scpsteps_list scpsteps pc fmlls sc Clist =
    SOME (fmlls', sc', Clist') ⇒
  ∃fml'.
    check_scpsteps pc fml sc scpsteps = SOME (fml',sc') ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_scpsteps_list_def,check_scpsteps_def]>>
  rw[]>>gvs[AllCaseEqs()]>>
  drule  fml_rel_check_scpstep_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`h`,`sc`,`pc`] mp_tac)>>
  simp[PULL_EXISTS]>>
  rw[]>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  first_x_assum (irule_at Any)>>
  metis_tac[check_scpstep_wf_fml]
QED

Definition is_forward_clause_def:
  is_forward_clause c ctopt ⇔
  case ctopt of NONE => F
  | SOME (cc,tag) => cc = c
End

Definition is_forward_fml_list_def:
  is_forward_fml_list ls c =
  EXISTS (is_forward_clause c) ls
End

Theorem fml_rel_is_forward_fml_list:
  fml_rel fml fmlls ⇒
  (is_forward_fml_list fmlls c ⇔ c ∈ get_fml F fml)
Proof
  rw[is_forward_fml_list_def,get_fml_def,EXISTS_MEM,MEM_EL]>>
  eq_tac>>gvs[fml_rel_def]>>rw[]>>
  gvs[is_forward_clause_def,AllCasePreds()]>>
  metis_tac[option_CLAUSES]
QED

Theorem all_distinct_map_fst_rev:
  ALL_DISTINCT (MAP FST ls) ⇔ ALL_DISTINCT (MAP FST (REVERSE ls))
Proof
  fs[MAP_REVERSE]
QED

Theorem LENGTH_FOLDR_update_resize1:
  ∀ll.
  LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME (v,F)) i) x) (REPLICATE n NONE) ll) ≥ n
Proof
  Induct>>simp[FORALL_PROD]>>rw[]>>
  rw[Once update_resize_def]
QED

Theorem LENGTH_FOLDR_update_resize2:
  ∀ll x.
  MEM x ll ⇒
  FST x < LENGTH (FOLDR (λx acc. (λ(i,v). update_resize acc NONE (SOME (v,F)) i) x) (REPLICATE n NONE) ll)
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
  x < LENGTH (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,F)) i) (REPLICATE n NONE) ls)
  ⇒
  EL x (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,F)) i) (REPLICATE n NONE) ls)
  =
  OPTION_MAP (λc. (c,F)) (ALOOKUP ls x)
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

Theorem SORTED_REVERSE:
  transitive P ⇒
  (SORTED P (REVERSE ls) ⇔ SORTED (λx y. P y x)  ls)
Proof
  rw[]>>
  DEP_REWRITE_TAC [SORTED_EL_LESS]>>
  fs[]>>
  CONJ_TAC>- (
    fs[transitive_def]>>
    metis_tac[])>>
  simp[EL_REVERSE]>>
  rw[EQ_IMP_THM]
  >- (
    first_x_assum (qspecl_then [`LENGTH ls-n-1`,`LENGTH ls-m-1`] mp_tac)>>
    simp[GSYM ADD1])>>
  first_x_assum match_mp_tac>>
  simp[]>>
  intLib.ARITH_TAC
QED

Theorem fml_rel_FOLDL_update_resize:
  fml_rel (build_fml kc fml)
  (FOLDL (λacc (i,v). update_resize acc NONE (SOME (v,F)) i) (REPLICATE n NONE) (enumerate kc fml))
Proof
  rw[fml_rel_def]>>
  reverse IF_CASES_TAC
  >- (
    fs[lookup_build_fml]>>
    CCONTR_TAC>>fs[]>>
    `MEM x (MAP FST (enumerate kc fml))` by
      (fs[MAP_FST_enumerate,MEM_GENLIST]>>
      intLib.ARITH_TAC)>>
    fs[MEM_MAP]>>
    fs[FOLDL_FOLDR_REVERSE]>>
    `MEM y (REVERSE (enumerate kc fml))` by
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

Definition iter_input_fml_def:
  iter_input_fml i n fml P =
    if n < i then T
    else
    let chk =
      (case any_el i fml NONE of
        NONE => T
      | SOME (c,b) => P c) in
      chk ∧ iter_input_fml (i+1) n fml P
Termination
  WF_REL_TAC`measure (λ(a,b,_). b+1-a)`>>rw[]
End

Theorem fml_rel_iter_input_fml:
  ∀i nc fmlls P.
  fml_rel fml fmlls ⇒
  (iter_input_fml i nc fmlls P ⇔
  (∀c. c ∈
    {c | ∃n b. i ≤ n ∧ n ≤ nc ∧
      lookup n fml = SOME (c:int list,b)} ⇒
      P c))
Proof
  ho_match_mp_tac iter_input_fml_ind>>
  rw[]>>
  simp[Once iter_input_fml_def]>>rw[]>>
  Cases_on`nc < i`>>gvs[]
  >- (
    rw[]>>
    `F` by intLib.ARITH_TAC)>>
  `∀n. i ≤ n ⇔ i + 1 ≤ n ∨ i = n` by intLib.ARITH_TAC>>
  simp[SF DNF_ss]>>
  DEP_REWRITE_TAC[fml_rel_any_el]>>
  simp[]>>
  every_case_tac>>simp[]>>
  metis_tac[]
QED

Definition clean_list_def:
  clean_list i fml =
  if LENGTH fml <= i
  then fml
  else
    clean_list (i+1) (LUPDATE NONE i fml)
Termination
  WF_REL_TAC`measure (λ(i,f). LENGTH f - i)`>>rw[]
End

Definition check_inputs_scp_list_def:
  check_inputs_scp_list r pc scp fml =
  let fml = clean_list (pc.nc+1) fml in
  if ISL (check_dec scp) then NONE
  else
  if is_data_var pc (var_lit r)
  then
    if iter_input_fml 0 pc.nc fml (MEM r)
    then SOME (INR (r,scp))
    else NONE
  else
    let ns = map_scpnv pc scp in
    let ov = alist_to_vec ns in
    let iter = LENGTH scp in
    if iter_input_fml 0 pc.nc fml
      (falsify_top pc iter (var_lit r) ov)
    then SOME (INR (r,scp))
    else NONE
End

Definition check_final_list_def:
  check_final_list pc sc fml =
  case sc.root of
    NONE => NONE
  | SOME r =>
    if r = 0
    then
      if is_forward_fml_list fml []
      then SOME (INL())
      else NONE
    else
      if is_data_ext_lit_run pc sc.Ev r ∧
         is_forward_fml_list fml [r]
      then
        check_inputs_scp_list r pc sc.scp fml
      else
        NONE
End

Theorem iter_input_fml_same:
  ∀i nc fml P fml'.
  LENGTH fml = LENGTH fml' ∧
  (∀i. i ≤ nc ∧ i < LENGTH fml ⇒ EL i fml = EL i fml') ⇒
  iter_input_fml i nc fml P =
  iter_input_fml i nc fml' P
Proof
  ho_match_mp_tac iter_input_fml_ind>>
  rw[]>>
  simp[Once iter_input_fml_def]>>
  simp[Once iter_input_fml_def,SimpRHS]>>
  rw[]>>
  Cases_on`nc < i`>>
  gvs[any_el_ALT]>>rw[]>>gvs[]>>
  metis_tac[]
QED

Theorem clean_list_LENGTH:
  ∀nc fml fml'.
  clean_list nc fml = fml' ⇒
  LENGTH fml = LENGTH fml'
Proof
  ho_match_mp_tac clean_list_ind>>rw[]>>
  simp[Once clean_list_def]>>rw[]
QED

Theorem clean_list_same:
  ∀nc fml i.
  i < LENGTH fml ⇒
  EL i (clean_list nc fml) =
  if i < nc then EL i fml
  else NONE
Proof
  ho_match_mp_tac clean_list_ind>>
  rw[]>>
  simp[Once clean_list_def]>>rw[]>>gvs[]>>
  rw[EL_LUPDATE]
QED

Theorem iter_input_fml_clean_list:
  iter_input_fml i nc (clean_list (nc + 1) fmlls) P =
  iter_input_fml i nc fmlls P
Proof
  ho_match_mp_tac iter_input_fml_same>>
  rw[]
  >- metis_tac[clean_list_LENGTH]>>
  DEP_REWRITE_TAC[clean_list_same]>>
  rw[]>>
  metis_tac[clean_list_LENGTH]
QED

Theorem fml_rel_check_inputs_scp_list:
  fml_rel fml fmlls ⇒
  check_inputs_scp_list r pc sc fmlls =
  check_inputs_scp r pc sc fml
Proof
  strip_tac>>
  simp[check_inputs_scp_list_def,check_inputs_scp_def,iter_input_fml_clean_list]>>
  DEP_REWRITE_TAC[fml_rel_iter_input_fml]>>
  simp[get_input_fml_def]
QED

Theorem fml_rel_check_final_list:
  fml_rel fml fmlls ⇒
  check_final_list pc sc fmlls =
  check_final pc sc fml
Proof
  strip_tac>>
  simp[check_final_list_def,check_final_def]>>
  DEP_REWRITE_TAC[fml_rel_is_forward_fml_list]>>
  simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  DEP_REWRITE_TAC[fml_rel_is_forward_fml_list,fml_rel_check_inputs_scp_list]>>
  simp[]
QED

Definition check_scp_final_list_def:
  check_scp_final_list ls pc fmlls sc Clist =
  case check_scpsteps_list ls pc fmlls sc Clist of
    NONE => NONE
  | SOME (fmlls', sc', Clist') =>
    check_final_list pc sc' fmlls'
End

Theorem range_build_fml:
  ∀ls id.
  range (build_fml id ls) = IMAGE (\C. (C,F)) (set ls)
Proof
  Induct>>
  rw[build_fml_def,range_def,lookup_insert,EXTENSION]>>
  eq_tac>>rw[]
  >- (
    gvs[AllCaseEqs(),lookup_build_fml,MEM_EL]>>
    DISJ2_TAC>>simp[]>>
    qexists_tac`n - (id + 1)`>>simp[])
  >-
    metis_tac[]>>
  gvs[MEM_EL]>>
  simp[lookup_build_fml]>>
  qexists_tac`n + (id+1)` >> simp[]
QED

Theorem wf_fml_build_fml:
  EVERY wf_clause ls ⇒
  wf_fml (build_fml id ls)
Proof
  simp[wf_fml_def]>>
  rw[range_build_fml]>>
  metis_tac[EVERY_MEM]
QED

Theorem check_scp_final_list_sound:
  good_pc pc ∧ pc.nc = LENGTH fml ∧
  EVERY wf_clause fml ∧
  EVERY (λC. vars_clause C ⊆ count (pc.nv + 1)) fml ∧
  check_scp_final_list ls pc
    (FOLDL (λacc (i,v).
      update_resize acc NONE (SOME (v,F)) i) (REPLICATE nc NONE)
        (enumerate 1 fml))
    init_sc Clist = SOME res ∧
  EVERY ($= w8z) Clist ⇒
  case res of
    INL () => {w | sat_fml w (set fml)} = {}
  | INR (r,scp) =>
    models (get_data_vars pc) (sat_scp F r scp) =
      models (get_data_vars pc) {w | sat_fml w (set fml)} ∧
    decomposable_scp F r scp ∧
    deterministic_scp F r scp
Proof
  rw[check_scp_final_list_def]>>
  gvs[AllCaseEqs()]>>
  assume_tac (GEN_ALL fml_rel_FOLDL_update_resize |>
    INST_TYPE [alpha |-> ``:int list``] |>
    Q.SPECL [`nc`,`1`,`fml`])>>
  drule fml_rel_check_scpsteps_list>>
  rpt (disch_then (drule_at Any))>>
  impl_tac >-
    metis_tac[wf_fml_build_fml]>>
  rw[]>>
  drule fml_rel_check_final_list>>
  strip_tac>>gvs[]>>
  every_case_tac
  >- (
    irule scpog_soundness_special>>
    first_x_assum (irule_at Any)>>
    gvs[])>>
  irule scpog_soundness>>
  simp[]>>
  metis_tac[]
QED

val _ = export_theory();
