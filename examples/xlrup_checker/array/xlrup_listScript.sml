(*
  This refines the checker to a fixed-size, list-based implementation
*)
open preamble basis xlrupTheory;

val _ = new_theory "xlrup_list"

val w8z_def = Define`w8z = (0w:word8)`

val w8o_def = Define`w8o = (1w:word8)`

val list_lookup_def = Define`
  list_lookup ls default k =
  if LENGTH ls ≤ k then default
  else EL k ls`

val index_def = Define`
  index (i:int) =
  if i ≤ 0 then
    2 * Num(-i)
  else
    2 * Num(i) - 1`

(* This version directly sets the size to double the input + 1 *)
val resize_update_list_def = Define`
  resize_update_list ls default v n =
  if n < LENGTH ls
  then
    LUPDATE v n ls
  else
    LUPDATE v n (ls ++ REPLICATE (n * 2 + 1 - LENGTH ls) default)`

(* optimized for is_rup  step *)
val delete_literals_sing_list_def = Define`
  (delete_literals_sing_list Clist [] = SOME 0) ∧
  (delete_literals_sing_list Clist (c::cs) =
  if list_lookup Clist (w8z) (index c) = w8o
  then delete_literals_sing_list Clist cs
  else (* c should be the only literal left *)
    if EVERY (λi. list_lookup Clist w8z (index i) = w8o) cs
    then SOME (~c)
    else NONE)`

val is_rup_list_aux_def = Define`
  (is_rup_list_aux fml [] C Clist = NONE) ∧
  (is_rup_list_aux fml (i::is) C Clist =
  case list_lookup fml NONE i of
    NONE => NONE
  | SOME Ci =>
  case delete_literals_sing_list Clist Ci of
    NONE => NONE
  | SOME nl =>
    if nl = 0 then SOME (C, Clist)
    else is_rup_list_aux fml is (nl::C) (resize_update_list Clist w8z w8o (index nl)))`

val set_list_def = Define`
  (set_list Clist v [] = Clist) ∧
  (set_list Clist v (c::cs) =
    set_list (resize_update_list Clist w8z v (index c)) v cs)`

val is_rup_list_def = Define`
  is_rup_list fml ls c Clist =
  let Clist = set_list Clist w8o c in
  case is_rup_list_aux fml ls c Clist of
    NONE => NONE
  | SOME (c, Clist) => SOME (set_list Clist w8z c)`

val list_delete_list_def = Define`
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))`

val safe_hd_def = Define`
  safe_hd ls = case ls of [] => (0:int) | (x::xs) => x`

val list_max_index_def = Define`
  list_max_index C = 2*list_max (MAP (λc. Num (ABS c)) C) + 1`

(* bump up the length to a large number *)
val resize_Clist_def = Define`
  resize_Clist C Clist =
  if LENGTH Clist ≤ list_max_index C then
    REPLICATE (2 * (list_max_index C )) w8z
  else Clist`

Definition check_xlrup_list_def:
  check_xlrup_list xlrup cfml xfml Clist =
  case xlrup of
    Del cl =>
    SOME (list_delete_list cl cfml, xfml, Clist)
  | RUP n c i0 =>
    (case is_rup_list cfml i0 c Clist of
      NONE => NONE
    | SOME Clist =>
      SOME (resize_update_list cfml NONE (SOME c) n, xfml, Clist))
  | XDel xl =>
    SOME (cfml, list_delete_list xl xfml, Clist)
  | _ => NONE
End

(* prove that check_xlrup_list implements check_xlrup *)
val fml_rel_def = Define`
  fml_rel fml fmlls ⇔
  ∀x.
  if x < LENGTH fmlls then
    lookup x fml = EL x fmlls
  else
    lookup x fml = NONE`

(* Require that the lookup table matches a clause exactly *)
val lookup_rel_def = Define`
  lookup_rel C Clist ⇔
  (* elements are either 0 or 1 *)
  (∀i. MEM i Clist ⇒ i = w8z ∨ i = w8o) ∧
  (* where 1 indicates membership in C *)
  (∀i. list_lookup Clist w8z (index i) = w8o ⇔ MEM i C)`

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

Theorem MEM_resize_update_list:
  MEM i (resize_update_list ls def v x) ⇒
  i = def ∨ MEM i ls ∨ i = v
Proof
  rw[resize_update_list_def,MEM_LUPDATE]
  >- metis_tac[MEM_EL]>>
  rw[EL_APPEND_EQN]>- metis_tac[MEM_EL]>>
  simp[EL_REPLICATE]
QED

Theorem list_lookup_resize_update_list:
  list_lookup (resize_update_list ls def v x) def y =
  if y = x then v
  else
    list_lookup ls def y
Proof
  simp[resize_update_list_def]>>
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
  lookup_rel (x::C) (resize_update_list Clist w8z w8o (index x))
Proof
  rw[lookup_rel_def]
  >-
   (drule MEM_resize_update_list >>
   metis_tac[])>>
  simp[list_lookup_resize_update_list,index_11]>>
  IF_CASES_TAC>>metis_tac[]
QED

Theorem lookup_rel_REVERSE:
  lookup_rel (REVERSE C) Clist ⇔ lookup_rel C Clist
Proof
  rw[lookup_rel_def]
QED

Theorem fml_rel_is_rup_list_aux:
  ∀ls C Clist.
  fml_rel fml fmlls ∧ wf_cfml fml ∧
  lookup_rel C Clist ⇒
  case is_rup_list_aux fmlls ls C Clist of
    SOME (C', Clist') =>
    is_rup fml ls C ∧ lookup_rel C' Clist'
  | NONE => ¬ is_rup fml ls C (* Not required but should be true *)
Proof
  Induct>>fs[is_rup_list_aux_def,is_rup_def]>>rw[]>>
  fs[fml_rel_def,list_lookup_def]>>
  first_x_assum(qspec_then`h` mp_tac)>>IF_CASES_TAC>>fs[]>>
  strip_tac>>
  Cases_on`EL h fmlls`>>simp[]>>
  `wf_clause x` by
    (fs[wf_cfml_def,values_def]>>metis_tac[])>>
  drule delete_literals_sing_list_correct>>
  disch_then drule>>
  TOP_CASE_TAC>>simp[]
  >-
    (every_case_tac>>fs[]) >>
  IF_CASES_TAC>>simp[]>>
  qmatch_goalsub_abbrev_tac`is_rup_list_aux _ _ aaa bbb`>>
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
  simp[list_lookup_resize_update_list]>>
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
  wf_cfml fml ∧
  fml_rel fml fmlls ⇒
  (case is_rup_list fmlls ls (C:cclause) Clist of
    SOME Clist' => is_rup fml ls C ∧ EVERY ($= w8z) Clist'
  | NONE => ¬is_rup fml ls C)
Proof
  rw[is_rup_list_def]>>
  drule fml_rel_is_rup_list_aux>>
  simp[]>>
  drule empty_set_list_lookup_rel>>
  disch_then(qspec_then`C` assume_tac)>>
  disch_then drule>>
  disch_then(qspec_then`ls` assume_tac)>>
  every_case_tac>>fs[]>>
  metis_tac[lookup_rel_set_list_empty]
QED

Theorem list_delete_list_FOLDL:
  ∀l fmlls.
  list_delete_list l fmlls =
  FOLDL (\fml i.
    if LENGTH fml ≤ i then fml else LUPDATE NONE i fml) fmlls l
Proof
  Induct>>rw[list_delete_list_def]
QED

Theorem LENGTH_list_delete_list[simp]:
  ∀l.
  LENGTH (list_delete_list l fmlls) = LENGTH fmlls
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]
QED

Theorem fml_rel_list_delete_list:
  ∀l fml fmlls fmlls'.
  fml_rel fml fmlls ∧
  list_delete_list l fmlls = fmlls' ⇒
  fml_rel (FOLDL (\a b. delete b a) fml l) fmlls'
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>rw[]>>
  first_x_assum drule>>
  rw[fml_rel_def]
  >- (
    first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
    IF_CASES_TAC>>fs[]>>
    simp[lookup_delete])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>fs[]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE,lookup_delete]>>
    IF_CASES_TAC>>fs[])>>
  simp[lookup_delete]
QED

Theorem fml_rel_resize_update_list:
  fml_rel fml fmlls ⇒
  fml_rel (insert n v fml) (resize_update_list fmlls NONE (SOME v) n)
Proof
  rw[resize_update_list_def,fml_rel_def,EL_LUPDATE]>>
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

Theorem fml_rel_check_xlrup_list:
  fml_rel cfml cfmlls ∧
  fml_rel xfml xfmlls ∧
  EVERY ($= w8z) Clist ∧
  wf_cfml cfml ⇒
  case check_xlrup_list xlrup cfmlls xfmlls Clist of
    SOME (cfmlls', xfmlls', Clist') =>
    EVERY ($= w8z) Clist' ∧
    ∃cfml' xfml'.
    check_xlrup xlrup cfml xfml = SOME (cfml',xfml')
  | NONE => T
Proof
  simp[check_xlrup_def,check_xlrup_list_def]>>
  strip_tac>>
  Cases_on`xlrup`>>simp[]
  >- ( (* RUP *)
    every_case_tac>>fs[]>>
    drule_all fml_rel_is_rup_list>>
    disch_then (qspecl_then [`l0`,`l`] assume_tac)>>gvs[])
QED

(*
Theorem fml_rel_contains_clauses_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  contains_clauses_list fmlls inds cls ⇒
  contains_clauses fml cls
Proof
  simp[contains_clauses_list_def,contains_clauses_def,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
  TOP_CASE_TAC>>rw[]>>
  drule reindex_characterize>>
  rw[]>>
  fs[EVERY_MEM]>>rw[]>>first_x_assum drule>>
  fs[MEM_MAP,MEM_FILTER,list_lookup_def]>>
  strip_tac>>
  Cases_on ‘LENGTH fmlls ≤ x’ >> fs [] >>
  fs[fml_rel_def]>>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
  fs[IS_SOME_EXISTS]>>
  rfs [] >>
  fs [] >>
  metis_tac[]
QED

Theorem fml_rel_check_lpr_list:
  ∀steps mindel fml fmlls inds fmlls' inds' Clist earliest.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  EVERY ($= w8z) Clist ∧ wf_cfml fml ∧
  earliest_rel fmlls earliest ∧
  EVERY wf_lpr steps ∧
  check_lpr_list mindel steps fmlls inds Clist earliest = SOME (fmlls', inds') ⇒
  ind_rel fmlls' inds' ∧
  ∃fml'. check_lpr mindel steps fml = SOME fml' ∧
    fml_rel fml' fmlls'
Proof
  Induct>>fs[check_lpr_list_def,check_lpr_def]>>
  ntac 9 strip_tac>>
  ntac 4 (TOP_CASE_TAC>>fs[])>>
  strip_tac>>
  drule  fml_rel_check_xlrup_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`h`,`mindel`] mp_tac)>> simp[]>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  qexists_tac`r`>>fs[]>>
  match_mp_tac check_xlrup_wf_cfml>>
  metis_tac[]
QED
*)

val _ = export_theory();
