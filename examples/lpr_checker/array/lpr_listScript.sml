(*
  This refines the LPR checker to a fixed-size, list-based implementation

  These fixed-size arrays are used in two places:
  1) Storing the formula
  2) Marking clauses (in the is_AT step)
*)
open preamble basis lprTheory;

val _ = new_theory "lpr_list"

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

(* optimized for is_AT  step *)
val delete_literals_sing_list_def = Define`
  (delete_literals_sing_list Clist [] = SOME 0) ∧
  (delete_literals_sing_list Clist (c::cs) =
  if list_lookup Clist (w8z) (index c) = w8o
  then delete_literals_sing_list Clist cs
  else (* c should be the only literal left *)
    if EVERY (λi. list_lookup Clist w8z (index i) = w8o) cs
    then SOME (~c)
    else NONE)`

val is_AT_list_aux_def = Define`
  (is_AT_list_aux fml [] C Clist = SOME (INR C, Clist)) ∧
  (is_AT_list_aux fml (i::is) C Clist =
  case list_lookup fml NONE i of
    NONE => NONE
  | SOME Ci =>
  case delete_literals_sing_list Clist Ci of
    NONE => NONE
  | SOME nl =>
    if nl = 0 then SOME (INL C, Clist)
    else is_AT_list_aux fml is (nl::C) (resize_update_list Clist w8z w8o (index nl)))`

val set_list_def = Define`
  (set_list Clist v [] = Clist) ∧
  (set_list Clist v (c::cs) =
    set_list (resize_update_list Clist w8z v (index c)) v cs)`

val is_AT_list_def = Define`
  is_AT_list fml ls c Clist =
  let Clist = set_list Clist w8o c in
  case is_AT_list_aux fml ls c Clist of
    NONE => NONE
  | SOME (INL c, Clist) => SOME (INL (), set_list Clist w8z c)
  | SOME (INR c, Clist) => SOME (INR c, set_list Clist w8z c)`

(* TODO: perhaps lookup trees can be replaced by alists since they're fairly short? *)
val check_RAT_list_def = Define`
  check_RAT_list fml Clist np C ik i Ci =
  if MEM np Ci then
    case sptree$lookup i ik of
      NONE => NONE
    | SOME is =>
    case is of
      [] =>
      if check_overlap Ci (overlap_assignment [-np] C)
      then SOME Clist
      else NONE
    | _ =>
      (* TODO: inefficient! should compute just once here
        skipped for now, because this path is rarely taken
      *)
      case is_AT_list fml is (C ++ (delete_literals Ci [np])) Clist of
        SOME (INL (), Clist) => SOME Clist
      | _ => NONE
  else SOME Clist`

val check_PR_list_def = Define`
  check_PR_list fml Clist nw C ik i Ci =
  if check_overlap Ci nw then
    case sptree$lookup i ik of
      NONE =>
      if check_overlap Ci (flip nw)
      then SOME Clist
      else NONE
    | SOME is =>
    case is of
      [] =>
      if check_overlap Ci (overlap_assignment (flip nw) C)
      then SOME Clist
      else NONE
    | _ =>
      case is_AT_list fml is (C ++ (delete_literals Ci (flip (overlap_assignment (flip nw) C)))) Clist of
        SOME (INL (), Clist) => SOME Clist
      | _ => NONE
  else SOME Clist`

(* Clean up the index list *)
val reindex_def = Define`
  (reindex fml [] = ([],[])) ∧
  (reindex fml (i::is) =
  case list_lookup fml NONE i of
    NONE => reindex fml is
  | SOME v =>
    let (l,r) = reindex fml is in
      (i::l, v::r))`

val every_check_RAT_list_def = Define`
  (every_check_RAT_list fml Clist np C ik [] [] = SOME Clist) ∧
  (every_check_RAT_list fml Clist np C ik (i::is) (Ci::Cis) =
  case check_RAT_list fml Clist np C ik i Ci of
    NONE => NONE
  | SOME Clist => every_check_RAT_list fml Clist np C ik is Cis) ∧
  (every_check_RAT_list fml Clist np C ik _ _ = NONE)`

val every_check_PR_list_def = Define`
  (every_check_PR_list fml Clist nw C ik [] [] = SOME Clist) ∧
  (every_check_PR_list fml Clist nw C ik (i::is) (Ci::Cis) =
  case check_PR_list fml Clist nw C ik i Ci of
    NONE => NONE
  | SOME Clist => every_check_PR_list fml Clist nw C ik is Cis) ∧
  (every_check_PR_list fml Clist nw C ik _ _ = NONE)`

val is_PR_list_def = Define`
  is_PR_list fml inds Clist p (C:cclause) wopt i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT_list fml i0 C Clist of
    NONE => NONE
  | SOME (INL (), Clist) => SOME (inds, Clist)
  | SOME (INR D, Clist) =>
  if p ≠ 0 then
    let (inds,vs) = reindex fml inds in
    case wopt of
      NONE =>
      (case every_check_RAT_list fml Clist (~p) D ik inds vs of
        NONE => NONE
      | SOME Clist => SOME (inds, Clist))
    | SOME w =>
      if check_overlap w (flip w) then NONE (* error *)
      else
      case every_check_PR_list fml Clist (flip w) D ik inds vs of
        NONE => NONE
      | SOME Clist => SOME (inds, Clist)
  else
     NONE`

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

val check_lpr_step_list_def = Define`
  check_lpr_step_list step fml inds Clist =
  case step of
    Delete cl =>
      SOME (list_delete_list cl fml, inds, Clist)
  | PR n C w i0 ik =>
    let p = safe_hd C in
    let Clist = resize_Clist C Clist in
      case is_PR_list fml inds Clist p C w i0 ik of
        NONE => NONE
      | SOME (inds, Clist) =>
        SOME (resize_update_list fml NONE (SOME C) n, n::inds, Clist)`

val is_unsat_list_def = Define`
  is_unsat_list fml inds =
  case reindex fml inds of
    (_,inds') => MEM [] inds'`

val check_lpr_list_def = Define`
  (check_lpr_list [] fml inds Clist = SOME (fml, inds)) ∧
  (check_lpr_list (step::steps) fml inds Clist =
    case check_lpr_step_list step fml inds Clist of
      NONE => NONE
    | SOME (fml', inds', Clist') => check_lpr_list steps fml' inds' Clist')`

val check_lpr_unsat_list_def = Define`
  check_lpr_unsat_list lpr fml inds Clist =
  case check_lpr_list lpr fml inds Clist of
    NONE => F
  | SOME (fml', inds') => is_unsat_list fml' inds'`

(* prove that check_lpr_step_list implements check_lpr_step *)
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

Theorem fml_rel_is_AT_list_aux:
  ∀ls C Clist.
  fml_rel fml fmlls ∧ wf_fml fml ∧
  lookup_rel C Clist ⇒
  case is_AT_list_aux fmlls ls C Clist of
    SOME (INL C', Clist') => is_AT fml ls C = SOME (INL ()) ∧ lookup_rel C' Clist'
  | SOME (INR C', Clist') => is_AT fml ls C = SOME (INR C') ∧ lookup_rel C' Clist'
  | NONE => is_AT fml ls C = NONE (* Not required but should be true *)
Proof
  Induct>>fs[is_AT_list_aux_def,is_AT_def]>>rw[]>>
  fs[fml_rel_def,list_lookup_def]>>
  first_x_assum(qspec_then`h` mp_tac)>>IF_CASES_TAC>>fs[]>>
  strip_tac>>
  Cases_on`EL h fmlls`>>simp[]>>
  `wf_clause x` by
    (fs[wf_fml_def,values_def]>>metis_tac[])>>
  drule delete_literals_sing_list_correct>>
  disch_then drule>>
  TOP_CASE_TAC>>simp[]
  >-
    (every_case_tac>>fs[])
  >>
  IF_CASES_TAC>>simp[]>>
  qmatch_goalsub_abbrev_tac`is_AT_list_aux _ _ aaa bbb`>>
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

Theorem fml_rel_is_AT_list:
  EVERY ($= w8z) Clist ∧ (* the array is always zero-ed before and after *)
  wf_fml fml ∧
  fml_rel fml fmlls ⇒
  (case is_AT_list fmlls ls (C:cclause) Clist of
    SOME (INL (), Clist') => is_AT fml ls C = SOME (INL ()) ∧ EVERY ($= w8z) Clist'
  | SOME (INR C', Clist') => is_AT fml ls C = SOME (INR C') ∧ EVERY ($= w8z) Clist'
  | NONE => is_AT fml ls C = NONE)
Proof
  rw[is_AT_list_def]>>
  drule fml_rel_is_AT_list_aux>>
  simp[]>>
  drule empty_set_list_lookup_rel>>
  disch_then(qspec_then`C` assume_tac)>>
  disch_then drule>>
  disch_then(qspec_then`ls` assume_tac)>>
  every_case_tac>>fs[]>>
  metis_tac[lookup_rel_set_list_empty]
QED

Theorem fml_rel_check_RAT_list:
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧ fml_rel fml fmlls ⇒
  case check_RAT_list fmlls Clist (-p) C ik i Ci of
    SOME Clist' => check_RAT fml p C ik (i,Ci) ∧ EVERY ($= w8z) Clist'
  | NONE => T (* not needed but can probably show it's ¬ check_RAT *)
Proof
  simp[check_RAT_list_def,check_RAT_def]>>
  simp[check_overlap_def]>>
  strip_tac>> IF_CASES_TAC>> simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  every_case_tac>>fs[]>>
  drule fml_rel_is_AT_list>>
  disch_then drule>>
  disch_then drule>>
  qmatch_asmsub_abbrev_tac`is_AT_list _ aaa bbb`>>
  disch_then(qspecl_then[`aaa`,`bbb`] mp_tac)>>
  every_case_tac>>fs[]
QED

Theorem fml_rel_every_check_RAT_list:
  ∀is Cis Clist.
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧ fml_rel fml fmlls ⇒
  case every_check_RAT_list fmlls Clist (-p) C ik is Cis of
    SOME Clist' => EVERY (check_RAT fml p C ik) (ZIP (is,Cis))∧ EVERY ($= w8z) Clist'
  | NONE => T (* not needed but can probably show it's ¬ check_RAT *)
Proof
  Induct>>rw[]
  >-
    (Cases_on`Cis`>>simp[every_check_RAT_list_def])
  >>
  Cases_on`Cis`>>simp[every_check_RAT_list_def]>>
  drule fml_rel_check_RAT_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`p`,`ik`,`h`,`h'`,`C`] mp_tac)>>
  TOP_CASE_TAC>>simp[]
QED

Theorem flip_flip[simp]:
  flip(flip w) = w
Proof
  rw[flip_def,MAP_MAP_o,o_DEF]
QED

Theorem fml_rel_check_PR_list:
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧ fml_rel fml fmlls ⇒
  case check_PR_list fmlls Clist (flip w) C ik i Ci of
    SOME Clist' => check_PR fml w C ik (i,Ci) ∧ EVERY ($= w8z) Clist'
  | NONE => T (* see above *)
Proof
  simp[check_PR_list_def,check_PR_def]>>
  IF_CASES_TAC>> simp[]>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  strip_tac>>
  every_case_tac>>fs[]>>
  drule fml_rel_is_AT_list>>
  disch_then drule>>
  disch_then drule>>
  qmatch_asmsub_abbrev_tac`is_AT_list _ aaa bbb`>>
  disch_then(qspecl_then[`aaa`,`bbb`] mp_tac)>>
  every_case_tac>>fs[]
QED

Theorem fml_rel_every_check_PR_list:
  ∀is Cis Clist.
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧ fml_rel fml fmlls ⇒
  case every_check_PR_list fmlls Clist (flip w) C ik is Cis of
    SOME Clist' => EVERY (check_PR fml w C ik) (ZIP (is,Cis)) ∧ EVERY ($= w8z) Clist'
  | NONE => T
Proof
  Induct>>rw[]
  >-
    (Cases_on`Cis`>>simp[every_check_PR_list_def])
  >>
  Cases_on`Cis`>>simp[every_check_PR_list_def]>>
  drule fml_rel_check_PR_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`w`,`ik`,`h`,`h'`,`C`] mp_tac)>>
  TOP_CASE_TAC>>simp[]
QED

(* It must be the case that everything that is SOME is in inds *)
val ind_rel_def = Define`
  ind_rel fmlls inds ⇔
  ∀x. x < LENGTH fmlls ∧
  IS_SOME (EL x fmlls) ⇒
  MEM x inds`

Theorem reindex_characterize:
  ∀inds inds' vs.
  reindex fmlls inds = (inds',vs) ⇒
  inds' = FILTER (λx. IS_SOME (list_lookup fmlls NONE x)) inds ∧
  vs = MAP (λx. THE (list_lookup fmlls NONE x)) inds'
Proof
  Induct>>fs[reindex_def] >>
  ntac 3 strip_tac>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  pairarg_tac>>fs[]>>rw[]>>
  simp[]
QED

Theorem ind_rel_filter:
  ind_rel fmlls inds ⇒
  ind_rel fmlls (FILTER (λx. IS_SOME (list_lookup fmlls NONE x)) inds)
Proof
  rw[ind_rel_def]>>
  simp[MEM_FILTER,list_lookup_def]
QED

Theorem ind_rel_reindex:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  reindex fmlls inds = (inds',vs) ⇒
  LENGTH inds' = LENGTH vs ∧
  (∀x. MEM x (toAList fml) ⇔ MEM x (ZIP (inds',vs))) ∧
  ind_rel fmlls inds'
Proof
  strip_tac>> drule reindex_characterize>> simp[]>>
  simp[FORALL_PROD,MEM_toAList]>>rw[]
  >-
    (simp[ZIP_MAP,MEM_MAP,MEM_FILTER]>>
    fs[fml_rel_def]>>first_x_assum(qspec_then`p_1` mp_tac)>>fs[]>>
    IF_CASES_TAC>>simp[list_lookup_def]>>
    rw[EQ_IMP_THM]>>fs[IS_SOME_EXISTS]>>
    fs[ind_rel_def])
  >>
  metis_tac[ind_rel_filter]
QED

Theorem fml_rel_is_PR_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  EVERY ($= w8z) Clist ∧
  wf_fml fml ⇒
  case is_PR_list fmlls inds Clist p C wopt i0 ik of
    SOME (inds', Clist') =>
      is_PR fml p C wopt i0 ik ∧
      ind_rel fmlls inds' ∧
      EVERY ($= w8z) Clist'
    | NONE => T
Proof
  rw[is_PR_list_def,is_PR_def]>>
  drule fml_rel_is_AT_list>>
  rpt(disch_then drule)>>
  disch_then (qspecl_then [`i0`,`C`] mp_tac)>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  strip_tac>>
  pairarg_tac>>fs[]>>
  IF_CASES_TAC >>fs[]>>
  Cases_on`wopt`>>simp[]
  >- (
    drule fml_rel_every_check_RAT_list>>
    rpt(disch_then drule)>>
    disch_then(qspecl_then[`p`,`ik`,`y`,`inds'`,`vs`] mp_tac)>>
    TOP_CASE_TAC>>simp[]>>
    imp_res_tac ind_rel_reindex>> simp[]>>
    simp[EVERY_MEM,FORALL_PROD])>>
  IF_CASES_TAC>>simp[]>>
  drule fml_rel_every_check_PR_list>>
  rpt(disch_then drule)>>
  disch_then(qspecl_then[`x`,`ik`,`y`,`inds'`,`vs`] mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  imp_res_tac ind_rel_reindex>> simp[]>>
  simp[EVERY_MEM,FORALL_PROD]
QED

Theorem list_delete_list_FOLDL:
  ∀l fmlls.
  list_delete_list l fmlls =
  FOLDL (\fml i.
    if LENGTH fml ≤ i then fml else LUPDATE NONE i fml) fmlls l
Proof
  Induct>>rw[list_delete_list_def]
QED

Theorem ind_rel_list_delete_list:
  ∀l fmlls fmlls'.
  ind_rel fmlls inds ∧
  list_delete_list l fmlls = fmlls' ⇒
  ind_rel fmlls' inds
Proof
  simp[list_delete_list_FOLDL,FOLDL_FOLDR_REVERSE]>>
  strip_tac>>
  qabbrev_tac`ll= REVERSE l`>>
  pop_assum kall_tac>>
  Induct_on`ll`>>
  rw[]>>fs[]>>
  first_x_assum drule>>
  rw[ind_rel_def,EL_LUPDATE]>>
  pop_assum mp_tac>> IF_CASES_TAC>>fs[]
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

Theorem ind_rel_resize_update_list:
  ind_rel fmlls inds ⇒
  ind_rel (resize_update_list fmlls NONE v n) (n::inds)
Proof
  rw[resize_update_list_def,ind_rel_def,EL_LUPDATE]>>every_case_tac>>fs[]>>
  fs[ind_rel_def]>>rw[]>>
  fs[IS_SOME_EXISTS,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  rfs[EL_REPLICATE,LENGTH_REPLICATE]
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

Theorem fml_rel_check_lpr_step_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  EVERY ($= w8z) Clist ∧
  wf_fml fml ⇒
  case check_lpr_step_list step fmlls inds Clist of
    SOME (fmlls', inds', Clist') =>
    EVERY ($= w8z) Clist' ∧
    ind_rel fmlls' inds' ∧
    ∃fml'. check_lpr_step step fml = SOME fml' ∧ fml_rel fml' fmlls'
  | NONE => T
Proof
  simp[check_lpr_step_def,check_lpr_step_list_def]>>
  strip_tac>>
  Cases_on`step`>>simp[]
  >- (
    CONJ_TAC >- metis_tac[ind_rel_list_delete_list]>>
    metis_tac[fml_rel_list_delete_list])>>
  drule fml_rel_is_PR_list>>
  `EVERY ($= w8z) (resize_Clist l Clist)` by
    rw[resize_Clist_def]>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`o'`,`safe_hd l`,`s`,`l0`,`l`] mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  simp[safe_hd_def]>>
  metis_tac[ind_rel_resize_update_list, fml_rel_resize_update_list]
QED

Theorem fml_rel_is_unsat_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  is_unsat_list fmlls inds ⇒
  is_unsat fml
Proof
  simp[is_unsat_list_def,is_unsat_def,MEM_MAP,EXISTS_PROD,MEM_toAList]>>
  TOP_CASE_TAC>>rw[]>>
  drule reindex_characterize>>
  rw[]>>
  fs[MEM_MAP,MEM_FILTER,list_lookup_def]>>
  Cases_on ‘LENGTH fmlls ≤ x’ >> fs [] >>
  fs[fml_rel_def]>>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
  fs[IS_SOME_EXISTS]>>
  rfs [] >>
  fs [] >>
  metis_tac[]
QED

val _ = export_theory();
