(*
  This refines the SCPOG checker to a fixed-size, list-based implementation.
*)
open preamble basis cnf_scpogTheory;

val _ = new_theory "scpog_list"

(* TODO *)
Definition wf_clause_def:
  wf_clause (C:int list) ⇔ ¬ MEM 0 C
End

Definition wf_fml_def:
  wf_fml fml ⇔
  ∀C tag. (C,tag) ∈ misc$range fml ⇒ wf_clause C
End

Definition w8z_def:
  w8z = (0w:word8)
End

Definition w8o_def:
  w8o = (1w:word8)
End

Definition list_lookup_def:
  list_lookup ls default k =
  if LENGTH ls ≤ k then default
  else EL k ls
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
  if list_lookup Clist (w8z) (index c) = w8o
  then delete_literals_sing_list Clist cs
  else (* c should be the only literal left *)
    if EVERY (λi. list_lookup Clist w8z (index i) = w8o) cs
    then SOME (~c)
    else NONE)
End

Definition is_rup_list_aux_def:
  (is_rup_list_aux pred fml [] C Clist = NONE) ∧
  (is_rup_list_aux pred fml (i::is) C Clist =
  case list_lookup fml NONE i of
    NONE => NONE
  | SOME ctag =>
  if pred ctag then
    case delete_literals_sing_list Clist (FST ctag) of
      NONE => NONE
    | SOME nl =>
      if nl = 0 then SOME (C, Clist)
      else is_rup_list_aux pred fml is (nl::C) (update_resize Clist w8z w8o (index nl))
  else NONE)
End

Definition set_list_def:
  (set_list Clist v [] = Clist) ∧
  (set_list Clist v (c::cs) =
    set_list (update_resize Clist w8z v (index c)) v cs)
End

Definition is_rup_list_def:
  is_rup_list pred fml ls c Clist =
  let Clist = set_list Clist w8o c in
  case is_rup_list_aux pred fml ls c Clist of
    NONE => NONE
  | SOME (c, Clist) => SOME (set_list Clist w8z c)
End

Definition list_max_index_def:
  list_max_index C = 2*list_max (MAP (λc. Num (ABS c)) C) + 1
End

(* bump up the length to a large number *)
Definition resize_Clist_def:
  resize_Clist C Clist =
  if LENGTH Clist ≤ list_max_index C then
    REPLICATE (2 * (list_max_index C )) w8z
  else Clist
End

Definition insert_one_list_def:
  insert_one_list tag fml i c =
    case list_lookup fml NONE i of
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
  (arb_delete_list sc [] fml = SOME fml) ∧
  (arb_delete_list sc (i::is) fml =
    case list_lookup fml NONE i of
      NONE => NONE
    | SOME ctag =>
      if is_adel sc.root ctag
      then arb_delete_list sc is (LUPDATE NONE i fml)
      else NONE)
End

Definition check_scpstep_list_def:
  check_scpstep_list scpstep pc fml sc Clist =
  case scpstep of
    Skip => SOME (fml, sc, Clist)
  | Root l =>
    OPTION_MAP (λsc'. (fml,sc',Clist)) (declare_root pc sc l)
  | RupAdd b n c i0 =>
    (let Clist = resize_Clist c Clist in
    case
      is_rup_list (is_strfwd b) fml i0 c Clist of
      NONE => NONE
    | SOME Clist =>
      if
        EVERY (λi. ¬is_fresh pc sc (var_lit i)) c
      then
        OPTION_MAP (λfml'. (fml',sc,Clist))
          (insert_one_list (strfwd_tag b) fml n c)
      else NONE)
  | RupDel n i0 =>
    (case list_lookup fml NONE n of
      NONE => NONE
    | SOME (C,tag) =>
      if tag = input_tag
      then
      let fml' = LUPDATE NONE n fml in
      case is_rup_list (is_backward sc.root) fml' i0 C Clist of
        NONE => NONE
      | SOME Clist => SOME (fml',sc,Clist)
      else NONE)
  | ArbDel ls =>
    OPTION_MAP (λfml'. (fml',sc,Clist))
      (arb_delete_list sc ls fml)
  | DeclPro n v ls =>
    (case declare_pro pc sc v ls of
      SOME (cs,sc') =>
        OPTION_MAP (λfml'. (fml',sc',Clist))
          (insert_list_list tseitin_tag fml n cs)
    | NONE => NONE)
  | DeclSum n v l1 l2 i0 =>
    (let c = [-l1;-l2] in
    let Clist = resize_Clist c Clist in
    case is_rup_list is_structural fml i0 c Clist of
      NONE => NONE
    | SOME Clist =>
      (case declare_sum pc sc v l1 l2 of
        SOME (cs,sc') =>
          OPTION_MAP (λfml'. (fml',sc',Clist))
            (insert_list_list tseitin_tag fml n cs)
      | NONE => NONE))
  | DeclSko n v ls =>
    (case declare_sko pc sc v ls of
      SOME (cT,csF,sc') =>
        (case insert_one_list disable_tag fml n cT of
          NONE => NONE
        | SOME fml' =>
          OPTION_MAP (λfml''. (fml'',sc',Clist))
            (insert_list_list skolem_tag fml' (n + 1) csF))
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

Theorem fml_rel_list_lookup:
  fml_rel fml fmlls ⇒
  list_lookup fmlls NONE i = lookup i fml
Proof
  rw[fml_rel_def,list_lookup_def]>>
  first_x_assum(qspec_then`i` mp_tac)>>
  rw[]
QED

(* Require that the lookup table matches a clause exactly *)
Definition lookup_rel_def:
  lookup_rel C Clist ⇔
  (* elements are either 0 or 1 *)
  (∀i. MEM i Clist ⇒ i = w8z ∨ i = w8o) ∧
  (* where 1 indicates membership in C *)
  (∀i. list_lookup Clist w8z (index i) = w8o ⇔ MEM i C)
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

Theorem list_lookup_update_resize:
  list_lookup (update_resize ls def v x) def y =
  if y = x then v
  else
    list_lookup ls def y
Proof
  simp[update_resize_def]>>
  IF_CASES_TAC
  >-
    (simp[list_lookup_def,EL_LUPDATE]>>
    IF_CASES_TAC>>simp[])>>
  simp[list_lookup_def,EL_LUPDATE,EL_APPEND_EQN,REPLICATE]>>
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
  simp[list_lookup_update_resize,index_11]>>
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
  case is_rup_list_aux pred fmlls ls C Clist of
    SOME (C', Clist') =>
    is_rup pred fml ls C ∧ lookup_rel C' Clist'
  | NONE => ¬ is_rup pred fml ls C (* Not required but should be true *)
Proof
  Induct>>fs[is_rup_list_aux_def,is_rup_def]>>rw[]>>
  DEP_REWRITE_TAC[fml_rel_list_lookup]>>simp[]>>
  Cases_on`lookup h fml`>>simp[]>>
  `wf_clause (FST x)` by
    (fs[wf_fml_def,range_def]>>metis_tac[FST,PAIR])>>
  drule delete_literals_sing_list_correct>>
  disch_then drule>>
  TOP_CASE_TAC>>simp[]
  >-
    (every_case_tac>>fs[]) >>
  Cases_on `pred x`>>gvs[]>>
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
    (fs[lookup_rel_def,EVERY_MEM,list_lookup_def]>>
    rw[]>>fs[w8z_def,w8o_def]>>
    first_x_assum(qspec_then`EL (index i) Clist` mp_tac)>>
    impl_tac>-
      simp[EL_MEM]>>
    simp[])>>
  drule lookup_rel_set_list_lookup_rel>>
  simp[]
QED

Theorem list_lookup_set_list:
  ∀is ls.
  list_lookup (set_list ls v is) w8z x =
  if ∃y. x = index y ∧ MEM y is then v
  else
    list_lookup ls w8z x
Proof
  Induct>>simp[set_list_def]>>
  ntac 2 strip_tac>>
  IF_CASES_TAC>-
    (fs[]>>
    metis_tac[])>>
  simp[list_lookup_update_resize]>>
  fs[]>>
  metis_tac[]
QED

Theorem lookup_rel_set_list_empty:
  ∀C.
  lookup_rel C Clist ⇒
  EVERY ($= w8z) (set_list Clist w8z C)
Proof
  rw[EVERY_EL]>>
  `list_lookup (set_list Clist w8z C) w8z n = w8z` by
    (simp[list_lookup_set_list]>>
    rw[]>>fs[lookup_rel_def,PULL_EXISTS]>>
    `?k. index k = n` by fs[index_onto]>>
    first_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    first_x_assum(qspec_then`k` assume_tac)>>rfs[]>>
    fs[list_lookup_def]>>
    rw[]>>fs[]>>
    first_x_assum(qspec_then `EL (index k) Clist` mp_tac)>>
    impl_tac>-
      (simp[MEM_EL]>>
      qexists_tac`index k`>>simp[])>>
    metis_tac[])>>
  rfs[list_lookup_def]
QED

Theorem fml_rel_is_rup_list:
  EVERY ($= w8z) Clist ∧ (* the array is always zero-ed before and after *)
  wf_fml fml ∧
  fml_rel fml fmlls ⇒
  (case is_rup_list pred fmlls ls (C:int list) Clist of
    SOME Clist' => is_rup pred fml ls C ∧ EVERY ($= w8z) Clist'
  | NONE => ¬is_rup pred fml ls C)
Proof
  rw[is_rup_list_def]>>
  drule fml_rel_is_rup_list_aux>>
  simp[]>>
  drule empty_set_list_lookup_rel>>
  disch_then(qspec_then`C` assume_tac)>>
  disch_then drule>>
  disch_then(qspecl_then[`pred`,`ls`] assume_tac)>>
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
  drule fml_rel_list_lookup>>
  metis_tac[fml_rel_update_resize]
QED

Theorem wf_fml_delete:
  wf_fml fml ⇒
  wf_fml (delete n fml)
Proof
  rw[wf_fml_def]>>
  metis_tac[range_delete,SUBSET_DEF]
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
  drule fml_rel_list_lookup>>
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
    disch_then (qspecl_then [`is_strfwd b`,`l0`,`l`] assume_tac)>>
    every_case_tac>>gvs[]>>
    metis_tac[fml_rel_insert_one_list])
  >- ( (* RupDel *)
    DEP_REWRITE_TAC[fml_rel_list_lookup]>>
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    qmatch_asmsub_abbrev_tac`is_rup_list A B C D E`>>
    qspecl_then [`A`,`C`,`B`,`delete n fml`,`Clist`,`D`] mp_tac (GEN_ALL fml_rel_is_rup_list)>>
    impl_tac >-
      simp[wf_fml_delete,fml_rel_LUPDATE_NONE,Abbr`B`]>>
    simp[fml_rel_LUPDATE_NONE,Abbr`B`])
  >- (
    simp[OPTION_MAP_CASE,o_DEF]>>
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    metis_tac[fml_rel_arb_delete_list])
  >- (
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    metis_tac[fml_rel_insert_list_list])
  >- (
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    qmatch_asmsub_abbrev_tac`is_rup_list A B C D E`>>
    qspecl_then [`A`,`C`,`B`,`fml`,`E`,`D`] mp_tac (GEN_ALL fml_rel_is_rup_list)>>
    unabbrev_all_tac>>simp[]>>
    impl_tac >-
      rw[resize_Clist_def]>>
    rw[]>>
    metis_tac[fml_rel_insert_list_list])
  >- (
    TOP_CASE_TAC>>gvs[AllCaseEqs()]>>
    metis_tac[fml_rel_insert_list_list,fml_rel_insert_one])
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
  cheat
QED

val _ = export_theory();
