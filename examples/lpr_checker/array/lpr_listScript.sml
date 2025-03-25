(*
  This refines the LPR checker to a fixed-size, list-based implementation

  These fixed-size lists (later refined to arrays) are used in three places:
  1) Storing the formula
  2) Marking clauses (in the is_AT step)
  3) Tracking earliest occurences of pivots
*)
open preamble basis lprTheory;

val _ = new_theory "lpr_list"

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

(* optimized for is_AT  step *)
Definition delete_literals_sing_list_def:
  (delete_literals_sing_list Clist [] = SOME 0) ∧
  (delete_literals_sing_list Clist (c::cs) =
  if any_el (index c) Clist w8z = w8o
  then delete_literals_sing_list Clist cs
  else (* c should be the only literal left *)
    if EVERY (λi. any_el (index i) Clist w8z = w8o) cs
    then SOME (~c)
    else NONE)
End

Definition is_AT_list_aux_def:
  (is_AT_list_aux fml [] C Clist = SOME (INR C, Clist)) ∧
  (is_AT_list_aux fml (i::is) C Clist =
  case any_el i fml NONE of
    NONE => NONE
  | SOME Ci =>
  case delete_literals_sing_list Clist Ci of
    NONE => NONE
  | SOME nl =>
    if nl = 0 then SOME (INL C, Clist)
    else is_AT_list_aux fml is (nl::C) (update_resize Clist w8z w8o (index nl)))
End

Definition set_list_def:
  (set_list Clist v [] = Clist) ∧
  (set_list Clist v (c::cs) =
    set_list (update_resize Clist w8z v (index c)) v cs)
End

Definition is_AT_list_def:
  is_AT_list fml ls c Clist =
  let Clist = set_list Clist w8o c in
  case is_AT_list_aux fml ls c Clist of
    NONE => NONE
  | SOME (INL c, Clist) => SOME (INL (), set_list Clist w8z c)
  | SOME (INR c, Clist) => SOME (INR c, set_list Clist w8z c)
End

Definition check_RAT_list_def:
  check_RAT_list fml Clist np C ik (i:num) Ci =
  if MEM np Ci then
    case ALOOKUP ik i of
      NONE => NONE
    | SOME is =>
    case is of
      [] =>
      if check_overlap Ci (overlap_assignment [-np] C)
      then SOME Clist
      else NONE
    | _ =>
      case is_AT_list fml is (C ++ (delete_literals Ci [np])) Clist of
        SOME (INL (), Clist) => SOME Clist
      | _ => NONE
  else SOME Clist
End

Definition check_PR_list_def:
  check_PR_list fml Clist nw C ik (i:num) Ci =
  if check_overlap Ci nw then
    case ALOOKUP ik i of
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
  else SOME Clist
End

Definition every_check_RAT_list_def:
  (every_check_RAT_list fml Clist np C ik [] [] = SOME Clist) ∧
  (every_check_RAT_list fml Clist np C ik (i::is) (Ci::Cis) =
  case check_RAT_list fml Clist np C ik i Ci of
    NONE => NONE
  | SOME Clist => every_check_RAT_list fml Clist np C ik is Cis) ∧
  (every_check_RAT_list fml Clist np C ik _ _ = NONE)
End

Definition every_check_PR_list_def:
  (every_check_PR_list fml Clist nw C ik [] [] = SOME Clist) ∧
  (every_check_PR_list fml Clist nw C ik (i::is) (Ci::Cis) =
  case check_PR_list fml Clist nw C ik i Ci of
    NONE => NONE
  | SOME Clist => every_check_PR_list fml Clist nw C ik is Cis) ∧
  (every_check_PR_list fml Clist nw C ik _ _ = NONE)
End

Definition min_opt_def:
  min_opt i j =
  case i of NONE => j
  | SOME ii =>
    (case j of
      NONE => SOME ii
    | SOME jj => SOME (MIN ii jj))
End

Definition list_min_opt_def:
  (list_min_opt min [] = min) ∧
  (list_min_opt min (i::is) =
    list_min_opt (min_opt min i) is)
End

(* Clean up the index list *)
Definition reindex_def:
  (reindex fml [] = ([],[])) ∧
  (reindex fml (i::is) =
  case any_el i fml NONE of
    NONE => reindex fml is
  | SOME v =>
    let (l,r) = reindex fml is in
      (i::l, v::r))
End

Definition reindex_partial_def:
  (reindex_partial fml mini [] = ([],[],[])) ∧
  (reindex_partial fml mini (i::is) =
  if i ≥ mini then
    case any_el i fml NONE of
      NONE => reindex_partial fml mini is
    | SOME v =>
      let (l,r,rest) = reindex_partial fml mini is in
        (i::l, v::r,rest)
  else
    ([],[],i::is))
End

Definition every_check_RAT_inds_list_def:
  (every_check_RAT_inds_list fml Clist np C ik mini [] acc = SOME (REVERSE acc, Clist)) ∧
  (every_check_RAT_inds_list fml Clist np C ik mini (i::is) acc =
  if i ≥ mini then
  case any_el i fml NONE of
    NONE => every_check_RAT_inds_list fml Clist np C ik mini is acc
  | SOME Ci =>
    case check_RAT_list fml Clist np C ik i Ci of
      NONE => NONE
    | SOME Clist => every_check_RAT_inds_list fml Clist np C ik mini is (i::acc)
  else
      SOME(REV acc (i::is), Clist))
End

(* rewrite into a simpler form without accumulator *)
Theorem every_check_RAT_inds_list_eq:
  ∀inds fml Clist np C ik mini acc.
  every_check_RAT_inds_list fml Clist np C ik mini inds acc =
  let (inds,vs,rest) = reindex_partial fml mini inds in
  case every_check_RAT_list fml Clist np C ik inds vs of
    NONE => NONE
  | SOME Clist => SOME(REVERSE acc ++ inds ++ rest, Clist)
Proof
  Induct>>rw[every_check_RAT_inds_list_def,reindex_partial_def,every_check_RAT_list_def]
  >- (
    TOP_CASE_TAC>>simp[]>>
    pairarg_tac>>fs[]>>
    simp[every_check_RAT_list_def]>>
    TOP_CASE_TAC>>simp[]>>
    metis_tac[APPEND_ASSOC,APPEND])
  >>
  simp[REV_REVERSE_LEM]
QED

Definition every_check_PR_inds_list_def:
  (every_check_PR_inds_list fml Clist np C ik mini [] acc = SOME (REVERSE acc, Clist)) ∧
  (every_check_PR_inds_list fml Clist np C ik mini (i::is) acc =
  if i ≥ mini then
  case any_el i fml NONE of
    NONE => every_check_PR_inds_list fml Clist np C ik mini is acc
  | SOME Ci =>
    case check_PR_list fml Clist np C ik i Ci of
      NONE => NONE
    | SOME Clist => every_check_PR_inds_list fml Clist np C ik mini is (i::acc)
  else
    SOME(REV acc (i::is), Clist))
End

Theorem every_check_PR_inds_list_eq:
  ∀inds fml Clist np C ik mini acc.
  every_check_PR_inds_list fml Clist np C ik mini inds acc =
  let (inds,vs,rest) = reindex_partial fml mini inds in
  case every_check_PR_list fml Clist np C ik inds vs of
    NONE => NONE
  | SOME Clist => SOME(REVERSE acc ++ inds ++ rest, Clist)
Proof
  Induct>>rw[every_check_PR_inds_list_def,reindex_partial_def,every_check_PR_list_def]
  >- (
    TOP_CASE_TAC>>simp[]>>
    pairarg_tac>>fs[]>>
    simp[every_check_PR_list_def]>>
    TOP_CASE_TAC>>simp[]>>
    metis_tac[APPEND_ASSOC,APPEND])
  >>
  simp[REV_REVERSE_LEM]
QED

Definition is_PR_list_def:
  is_PR_list fml inds Clist earliest p (C:cclause) wopt i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT_list fml i0 C Clist of
    NONE => NONE
  | SOME (INL (), Clist) => SOME (inds, Clist)
  | SOME (INR D, Clist) =>
  if p ≠ 0 then
    case wopt of NONE =>
      (let miniopt = any_el (index (~p)) earliest NONE in
      case miniopt of NONE => SOME (inds,Clist)
      | SOME mini => every_check_RAT_inds_list fml Clist (~p) D ik mini inds [])
    | SOME w =>
      if check_overlap w (flip w) then NONE (* error *)
      else
      let miniopt = list_min_opt NONE (MAP (λw. any_el (index w) earliest NONE) (flip w)) in
      case miniopt of NONE => SOME (inds,Clist)
      | SOME mini => every_check_PR_inds_list fml Clist (flip w) D ik mini inds []
  else
     NONE
End

(* easier to reason about later *)
Theorem is_PR_list_eq:
  is_PR_list fml inds Clist earliest p (C:cclause) wopt i0 ik =
  (* First, do the asymmetric tautology check *)
  case is_AT_list fml i0 C Clist of
    NONE => NONE
  | SOME (INL (), Clist) => SOME (inds, Clist)
  | SOME (INR D, Clist) =>
  if p ≠ 0 then
    case wopt of NONE =>
      (let miniopt = any_el (index (~p)) earliest NONE in
      case miniopt of NONE => SOME (inds,Clist)
      | SOME mini =>
      let (inds,vs,rest) = reindex_partial fml mini inds in
      (case every_check_RAT_list fml Clist (~p) D ik inds vs of
         NONE => NONE
       | SOME Clist => SOME (inds ++ rest, Clist)))
    | SOME w =>
      if check_overlap w (flip w) then NONE (* error *)
      else
      let miniopt = list_min_opt NONE (MAP (λw. any_el (index w) earliest NONE) (flip w)) in
      case miniopt of NONE => SOME (inds,Clist)
      | SOME mini =>
      let (inds,vs,rest) = reindex_partial fml mini inds in
      (case every_check_PR_list fml Clist (flip w) D ik inds vs of
         NONE => NONE
       | SOME Clist => SOME (inds ++ rest, Clist))
  else
     NONE
Proof
  simp[is_PR_list_def]>>
  ntac 6 (TOP_CASE_TAC>>simp[])>>
  rpt(pairarg_tac>>fs[])
  >- simp[every_check_RAT_inds_list_eq]>>
  TOP_CASE_TAC>>fs[]>>
  pairarg_tac>>fs[]>>
  simp[every_check_PR_inds_list_eq]
QED

Definition list_delete_list_def:
  (list_delete_list [] fml = fml) ∧
  (list_delete_list (i::is) fml =
    if LENGTH fml ≤ i
    then list_delete_list is fml
    else list_delete_list is (LUPDATE NONE i fml))
End

Definition safe_hd_def:
  safe_hd ls = case ls of [] => (0:int) | (x::xs) => x
End

(*Might want to rename to MAX_LIST_index*)
Definition list_max_index_def:
  list_max_index C = 2*MAX_LIST (MAP (λc. Num (ABS c)) C) + 1
End

(* bump up the length to a large number *)
Definition resize_Clist_def:
  resize_Clist C Clist =
  if LENGTH Clist ≤ list_max_index C then
    REPLICATE (2 * (list_max_index C )) w8z
  else Clist
End

(* v is the clause index *)
Definition update_earliest_def:
  (update_earliest ls v [] = ls) ∧
  (update_earliest ls v (n::ns) =
    let ind = index n in
    let minn = any_el ind ls NONE in
    let updmin = min_opt minn (SOME v) in
    update_earliest (update_resize ls NONE updmin ind) v ns)
End

(* ensure list remains ≥ sorted -- common case: will always just insert at the front *)
Definition sorted_insert_def:
  (sorted_insert (x:num) [] = [x]) ∧
  (sorted_insert x (y::ys) =
    if x ≥ y then x::y::ys
    else y::(sorted_insert x ys))
End

Definition check_earliest_def:
  (check_earliest fml x old new [] = T) ∧
  (check_earliest fml x old new (i::is) =
  if i ≥ old then
    if i < new
    then
      case any_el i fml NONE of
        NONE => check_earliest fml x old new is
      | SOME Ci =>
        ¬ (MEM x Ci) ∧ check_earliest fml x old new is
    else
      check_earliest fml x old new is
  else T)
End

Definition list_min_aux_def:
  (list_min_aux min [] = min) ∧
  (list_min_aux min ((i,_)::is) =
      list_min_aux (MIN min i) is)
End

(* Note that clauses are 1 indexed *)
Definition list_min_def:
  list_min ls =
  case ls of [] => 0
  | (x::xs) => list_min_aux (FST x) xs
End

Definition hint_earliest_def:
  hint_earliest C (w:int list option) (ik:(num # num list) list) fml inds earliest =
  case w of
    NONE =>
    (let lm = list_min ik in
      if lm = 0 then earliest
      else
        (* RAT *)
        let p = safe_hd C in
        case any_el (index (~p)) earliest NONE of
          NONE => earliest
        | SOME mini => (* The current mini index of ~p *)
          if check_earliest fml (~p) mini lm inds
          then update_resize earliest NONE (SOME lm) (index (~p))
          else earliest)
  | SOME _ => earliest
End

Definition check_lpr_step_list_def:
  check_lpr_step_list mindel step fml inds Clist earliest =
  case step of
    Delete cl =>
      if EVERY ($< mindel) cl then
        SOME (list_delete_list cl fml, inds, Clist, earliest)
      else
        NONE
  | PR n C w i0 ik =>
    let p = safe_hd C in
    let Clist = resize_Clist C Clist in
    let earliest = hint_earliest C w ik fml inds earliest in
      case is_PR_list fml inds Clist earliest p C w i0 ik of
        NONE => NONE
      | SOME (inds, Clist) =>
        if mindel < n then
          SOME (update_resize fml NONE (SOME C) n, sorted_insert n inds, Clist,
            update_earliest earliest n C)
        else NONE
End

Definition check_lpr_list_def:
  (check_lpr_list mindel [] fml inds Clist earliest = SOME (fml, inds)) ∧
  (check_lpr_list mindel (step::steps) fml inds Clist earliest =
    case check_lpr_step_list mindel step fml inds Clist earliest of
      NONE => NONE
    | SOME (fml', inds', Clist',earliest') => check_lpr_list mindel steps fml' inds' Clist' earliest')
End

Definition contains_clauses_list_def:
  contains_clauses_list fml inds cls =
  case reindex fml inds of
    (_,inds') =>
  let inds'' = MAP canon_clause inds' in
  EVERY (λcl. MEM (canon_clause cl) inds'') cls
End

Definition check_lpr_unsat_list_def:
  check_lpr_unsat_list lpr fml inds Clist earliest =
  case check_lpr_list 0 lpr fml inds Clist earliest of
    NONE => F
  | SOME (fml', inds') => contains_clauses_list fml' inds' [[]]
End

(* Checking satisfiability equivalence *)
Definition check_lpr_sat_equiv_list_def:
  check_lpr_sat_equiv_list lpr fml inds Clist earliest mindel cls =
  case check_lpr_list mindel lpr fml inds Clist earliest of
    NONE => F
  | SOME (fml', inds') => contains_clauses_list fml' inds' cls
End

(* prove that check_lpr_step_list implements check_lpr_step *)
Definition fml_rel_def:
  fml_rel fml fmlls ⇔
  ∀x.
  lookup x fml = any_el x fmlls NONE
End

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
  >- (
    simp[any_el_ALT,EL_LUPDATE]>>
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
  >- (
    drule MEM_update_resize >>
    metis_tac[])>>
  simp[any_el_update_resize,index_11]>>
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
  fs[fml_rel_def,any_el_ALT]>>
  first_x_assum(qspec_then`h` mp_tac)>>IF_CASES_TAC>>fs[]>>
  strip_tac>>
  Cases_on`EL h fmlls`>>simp[]>>
  `wf_clause x` by
    (fs[wf_fml_def,range_def]>>metis_tac[])>>
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
  else any_el x ls w8z
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
Definition ind_rel_def:
  ind_rel fmlls inds ⇔
  ∀x. x < LENGTH fmlls ∧
  IS_SOME (EL x fmlls) ⇒
  MEM x inds
End

Theorem reindex_characterize:
  ∀inds inds' vs.
  reindex fmlls inds = (inds',vs) ⇒
  inds' = FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds ∧
  vs = MAP (λx. THE (any_el x fmlls NONE )) inds'
Proof
  Induct>>fs[reindex_def] >>
  ntac 3 strip_tac>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  pairarg_tac>>fs[]>>rw[]>>
  simp[]
QED

Theorem ind_rel_filter:
  ind_rel fmlls inds ⇒
  ind_rel fmlls (FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds)
Proof
  rw[ind_rel_def]>>
  simp[MEM_FILTER,any_el_ALT]
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
  >- (
    simp[ZIP_MAP,MEM_MAP,MEM_FILTER]>>
    fs[fml_rel_def,any_el_ALT]>>
    first_x_assum(qspec_then`p_1` mp_tac)>>fs[]>>
    IF_CASES_TAC>>simp[any_el_ALT]>>
    rw[EQ_IMP_THM]>>fs[IS_SOME_EXISTS]>>
    fs[ind_rel_def])
  >>
  metis_tac[ind_rel_filter]
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

Theorem reindex_partial_characterize:
  ∀inds inds' vs rest.
  SORTED $>= inds ∧
  reindex_partial (fmlls:int list option list) mini inds = (inds',vs, rest) ⇒
  ∃f.
  inds = f ++ rest ∧
  f = FILTER (λx. x ≥ mini) inds ∧
  inds' = FILTER (λx. IS_SOME (any_el x fmlls NONE)) f ∧
  vs = MAP (λx. THE (any_el x fmlls NONE)) inds'
Proof
  Induct>>fs[reindex_partial_def] >>
  ntac 4 strip_tac>>fs[]>>
  reverse IF_CASES_TAC>>
  simp[]
  >- (
    strip_tac>>simp[]>>
    CONJ_ASM1_TAC>>simp[]>>
    drule SORTED_HEAD_LESS>>
    disch_then drule>>
    rw[FILTER_EQ_NIL,EVERY_MEM]>>
    first_x_assum drule>>simp[])>>
  strip_tac>>
  IF_CASES_TAC>>fs[]
  >- (
    fs[IS_SOME_EXISTS]>>fs[]>>
    drule SORTED_TL>>strip_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    rw[]>>simp[])
  >>
  drule SORTED_TL>>
  strip_tac>>fs[]
QED

Theorem ind_rel_filter_partial:
  ind_rel fmlls (inds++rest) ⇒
  ind_rel fmlls (FILTER (λx. IS_SOME (any_el x fmlls NONE)) inds ++ rest)
Proof
  rw[ind_rel_def]>>
  simp[MEM_FILTER,any_el_ALT]
QED

Theorem SORTED_FILTER_part:
  transitive R ⇒
  SORTED R (a++b) ⇒
  SORTED R (FILTER P a ++ b)
Proof
  strip_tac>>
  DEP_REWRITE_TAC [SORTED_APPEND]>>
  metis_tac[SORTED_FILTER,MEM_FILTER]
QED

Theorem ind_rel_reindex_partial:
  fml_rel fml (fmlls:int list option list) ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  reindex_partial fmlls x inds = (inds',vs,rest) ⇒
  ind_rel fmlls (inds'++rest) ∧
  SORTED $>= (inds'++rest)
Proof
  strip_tac>>
  drule reindex_partial_characterize>>
  disch_then drule>>
  strip_tac>>
  CONJ_TAC>-
    metis_tac[ind_rel_filter_partial]>>
  qpat_x_assum`SORTED _ _` mp_tac>>
  qpat_x_assum`_ = _ ++_` SUBST_ALL_TAC>>
  qpat_x_assum`inds' = _` SUBST_ALL_TAC>>
  match_mp_tac SORTED_FILTER_part>>
  simp[transitive_def]
QED

(* earliest correctly tracks earliest occurrence of a literal *)
Definition earliest_rel_def:
  earliest_rel fmlls earliest ⇔
  ∀x.
  case any_el x earliest NONE of
    NONE =>
    (∀pos z.
      pos < LENGTH fmlls ⇒
      case EL pos fmlls of
        NONE => T
      | SOME ls => MEM z ls ⇒ index z ≠ x)
  | SOME i =>
    (∀pos z.
      pos < i ∧
      pos < LENGTH fmlls ⇒
      case EL pos fmlls of
        NONE => T
      | SOME ls => MEM z ls ⇒ index z ≠ x)
End

(* Trivial case when the earliest index is NONE *)
Theorem earliest_rel_RAT_NONE:
  ∀fmlls Clist np ik is inds vs inds' vs' Clist' earliest.
  earliest_rel fmlls earliest ∧
  EVERY (λx. IS_SOME (any_el x fmlls NONE)) inds ∧
  vs = MAP (λx. THE (any_el x fmlls NONE)) inds ∧
  any_el (index np) earliest NONE = NONE ⇒
  every_check_RAT_list fmlls Clist np ik is inds vs = SOME Clist
Proof
  ho_match_mp_tac (fetch "-" "every_check_RAT_list_ind")>>
  rw[]>>
  simp[every_check_RAT_list_def]>>
  qpat_x_assum`!Clist'. _` (qspec_then `Clist` mp_tac)>>
  impl_keep_tac>- (
    simp[check_RAT_list_def]>>
    fs[earliest_rel_def]>>
    first_x_assum (qspec_then`index np` mp_tac)>>
    simp[]>>
    fs[any_el_ALT,IS_SOME_EXISTS]>>
    disch_then(qspec_then`i` mp_tac)>>simp[]>>
    disch_then(qspec_then`np` mp_tac)>>simp[])>>
  simp[]>>
  rpt (disch_then drule)>>
  metis_tac[]
QED

Theorem earliest_rel_RAT_NONE_alt:
  ∀fmlls Clist np ik is inds earliest.
  earliest_rel fmlls earliest ∧
  any_el (index np) earliest NONE = NONE ⇒
  let (aaa,bbb) = reindex fmlls inds in
  every_check_RAT_list fmlls Clist np ik is aaa bbb = SOME Clist
Proof
  rw[]>>
  pairarg_tac>>simp[]>>
  match_mp_tac earliest_rel_RAT_NONE>>
  drule reindex_characterize>>
  simp[EVERY_FILTER]>>
  metis_tac[]
QED

(* Trivial case when the earliest index is beyond any index *)
Theorem earliest_rel_RAT_skip:
  ∀inds fmlls Clist np ik is vs Clist earliest pos.
  earliest_rel fmlls earliest ∧
  any_el (index np) earliest NONE = SOME pos ∧
  EVERY (λx. x < pos) inds ∧
  EVERY (λx. IS_SOME (any_el x fmlls NONE)) inds ∧
  vs = MAP (λx. THE (any_el x fmlls NONE)) inds ⇒
  every_check_RAT_list fmlls Clist np ik is inds vs = SOME Clist
Proof
  Induct>>rw[every_check_RAT_list_def]>>
  qpat_x_assum`IS_SOME _` mp_tac>>
  simp[IS_SOME_EXISTS]>>
  rw[]>> fs[]>>
  simp[check_RAT_list_def]>>
  `¬MEM np x` by (
    fs[earliest_rel_def]>>
    first_x_assum (qspec_then`index np` mp_tac)>>
    simp[]>>
    fs[any_el_ALT,IS_SOME_EXISTS]>>
    disch_then(qspec_then`h` mp_tac)>>simp[]>>
    disch_then(qspec_then`np` mp_tac)>>simp[])>>
  simp[]>>
  first_x_assum drule>>
  disch_then drule>>
  fs[]
QED

Theorem earliest_rel_reindex_partial_RAT_FILTER_min:
  ∀inds fmlls Clist np ik is aaa bbb Clist' earliest pos.
  earliest_rel fmlls earliest ∧
  SORTED ($>=) inds ∧
  any_el (index np) earliest NONE = SOME pos ∧
  reindex fmlls (FILTER (λx. x ≥ pos) inds) = (aaa,bbb) ∧
  every_check_RAT_list fmlls Clist np ik is aaa bbb = SOME Clist' ⇒
  let (aaa,bbb) = reindex fmlls inds in
  every_check_RAT_list fmlls Clist np ik is aaa bbb = SOME Clist'
Proof
  Induct>>rw[every_check_RAT_list_def,reindex_partial_def]
  >- (
    fs[reindex_def]>>
    TOP_CASE_TAC>>fs[]
    >- (
      drule SORTED_TL>>
      strip_tac>>
      first_x_assum drule>>
      simp[])>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    rw[]>>fs[]>>
    fs[every_check_RAT_list_def]>>
    TOP_CASE_TAC>>fs[]>>
    drule SORTED_TL>>
    strip_tac>>
    first_x_assum drule>>
    simp[])>>
  `EVERY (λx. x < pos) inds` by
    metis_tac[SORTED_HEAD_LESS]>>
  `aaa = [] ∧ bbb = []` by
    (`FILTER (λx. x ≥ pos) inds = []` by
      (fs[FILTER_EQ_NIL,EVERY_MEM]>>
      rw[]>>
      first_x_assum drule>>simp[])>>
    fs[reindex_def])>>
  pairarg_tac>>fs[]>>
  fs[every_check_RAT_list_def]>>
  drule earliest_rel_RAT_skip>>
  disch_then match_mp_tac>>
  asm_exists_tac>>simp[]>>
  drule reindex_characterize>>
  rw[]>>simp[EVERY_FILTER]>>
  fs[EVERY_MEM]
QED

Theorem earliest_rel_reindex_partial_RAT_SOME:
  ∀fmlls Clist np ik is inds vs inds' rest Clist' earliest pos.
  earliest_rel fmlls earliest ∧
  SORTED ($>=) inds ∧
  any_el (index np) earliest NONE = SOME pos ∧
  reindex_partial fmlls pos inds = (inds', vs, rest) ∧
  every_check_RAT_list fmlls Clist np ik is inds' vs = SOME Clist' ⇒
  let (aaa,bbb) = reindex fmlls inds in
  every_check_RAT_list fmlls Clist np ik is aaa bbb = SOME Clist'
Proof
  rw[]>>
  drule reindex_partial_characterize>>
  disch_then drule>>
  rw[]>>
  pairarg_tac>>fs[]>>
  drule reindex_characterize>>rw[]>>
  drule earliest_rel_reindex_partial_RAT_FILTER_min>>
  rpt(disch_then drule)>>
  simp[]>>
  disch_then match_mp_tac>>
  Cases_on`reindex fmlls (FILTER (λx. x ≥ pos) inds)` >>fs[]>>
  drule reindex_characterize>>rw[]
QED

Theorem list_min_opt_FOLDL:
  ∀ls opt opt'.
  list_min_opt opt ls =
  FOLDL (λx opt. min_opt x opt) opt ls
Proof
  Induct>>fs[list_min_opt_def]
QED

Theorem list_min_opt_opt[simp]:
  ∀ls opt opt'.
  min_opt opt opt' = opt' ⇒
  min_opt opt (list_min_opt opt' ls) = (list_min_opt opt' ls)
Proof
  Induct>>simp[list_min_opt_def,min_opt_def]>>
  every_case_tac>>rw[]>>simp[]>>
  TOP_CASE_TAC>>fs[]>>
  pop_assum mp_tac>>
  TOP_CASE_TAC>>fs[]>>
  Cases_on`h`>>fs[]
  >- (
    TOP_CASE_TAC>>simp[]>>
    first_x_assum(qspecl_then[`SOME x`,`SOME x'`] mp_tac)>>simp[min_opt_def])>>
  TOP_CASE_TAC>>simp[]
  >- (
    first_x_assum(qspecl_then[`SOME (MIN x' x'')`,`SOME (MIN x' x'')`] mp_tac)>>
    simp[min_opt_def])>>
  first_x_assum(qspecl_then[`SOME (MIN x' x'')`,`SOME (MIN x' x'')`] mp_tac)>>
  simp[min_opt_def,MIN_DEF]
QED

Theorem list_min_opt_bound:
  ∀ls x opt.
  MEM x ls ⇒
  min_opt x (list_min_opt opt ls) = (list_min_opt opt ls)
Proof
  Induct>>simp[list_min_opt_def]>>
  ntac 4 strip_tac
  >- (
    rveq>>
    simp[Once min_opt_def]>>
    match_mp_tac list_min_opt_opt>>
    simp[min_opt_def]>>
    every_case_tac>>simp[MIN_DEF])>>
  first_x_assum drule>>
  simp[]
QED

Theorem earliest_rel_PR_NONE:
  ∀fmlls Clist nw ik is inds vs inds' vs' Clist' earliest.
  earliest_rel fmlls earliest ∧
  EVERY (λx. IS_SOME (any_el x fmlls NONE)) inds ∧
  vs = MAP (λx. THE (any_el x fmlls NONE)) inds ∧
  list_min_opt NONE
    (MAP (λx. any_el (index x) earliest NONE) nw) = NONE ⇒
  every_check_PR_list fmlls Clist nw ik is inds vs = SOME Clist
Proof
  ho_match_mp_tac (fetch "-" "every_check_PR_list_ind")>>
  rw[]>>
  simp[every_check_PR_list_def]>>
  qpat_x_assum`!Clist'. _` (qspec_then `Clist` mp_tac)>>
  impl_keep_tac>- (
    simp[check_PR_list_def]>>
    IF_CASES_TAC>>simp[]>>
    `F` by (
      fs[check_overlap_eq]>>
      qmatch_asmsub_abbrev_tac`_ _ lss = _` >>
      `MEM (any_el (index x) earliest NONE) lss` by
        (fs[Abbr`lss`,MEM_MAP]>>
        metis_tac[])>>
      drule list_min_opt_bound>>
      disch_then(qspec_then`NONE` mp_tac)>>strip_tac>>
      rfs[min_opt_def]>>
      every_case_tac>>fs[]>>
      fs[earliest_rel_def]>>
      first_x_assum (qspec_then`index x` assume_tac)>>
      rfs[]>>
      fs[IS_SOME_EXISTS,any_el_ALT]>>
      pop_assum(qspec_then`i` assume_tac)>>rfs[]>>
      metis_tac[]))>>
  simp[]>>
  rpt (disch_then drule)>>
  metis_tac[]
QED

Theorem earliest_rel_PR_NONE_alt:
  ∀fmlls Clist nw ik is inds earliest.
  earliest_rel fmlls earliest ∧
  list_min_opt NONE
    (MAP (λx. any_el (index x) earliest NONE) nw) = NONE ⇒
  let (aaa,bbb) = reindex fmlls inds in
  every_check_PR_list fmlls Clist nw ik is aaa bbb = SOME Clist
Proof
  rw[]>>
  pairarg_tac>>simp[]>>
  match_mp_tac earliest_rel_PR_NONE>>
  drule reindex_characterize>>
  simp[EVERY_FILTER]>>
  metis_tac[]
QED

(* Trivial case when the earliest index is beyond any index *)
Theorem earliest_rel_PR_skip:
  ∀inds fmlls Clist nw ik is vs Clist earliest pos.
  earliest_rel fmlls earliest ∧
  list_min_opt NONE
    (MAP (λx. any_el (index x) earliest NONE) nw) = SOME pos ∧
  EVERY (λx. x < pos) inds ∧
  EVERY (λx. IS_SOME (any_el x fmlls NONE)) inds ∧
  vs = MAP (λx. THE (any_el x fmlls NONE)) inds ⇒
  every_check_PR_list fmlls Clist nw ik is inds vs = SOME Clist
Proof
  Induct>>rw[every_check_PR_list_def]>>
  qpat_x_assum`IS_SOME _` mp_tac>>
  simp[IS_SOME_EXISTS]>>
  rw[]>> fs[]>>
  simp[check_PR_list_def]>>
  `¬check_overlap x nw` by (
      fs[check_overlap_eq]>>
      qmatch_asmsub_abbrev_tac`_ _ lss = SOME pos` >>
      CCONTR_TAC>>fs[]>>
      `MEM (any_el (index x') earliest NONE) lss` by
        (fs[Abbr`lss`,MEM_MAP]>>
        metis_tac[])>>
      drule list_min_opt_bound>>
      disch_then(qspec_then`NONE` mp_tac)>>strip_tac>>
      rfs[min_opt_def]>>
      every_case_tac>>fs[]>>
      fs[earliest_rel_def,MIN_DEF]>>
      first_x_assum (qspec_then`index x'` assume_tac)>>
      rfs[]>>
      fs[IS_SOME_EXISTS,any_el_ALT]>>
      pop_assum(qspec_then`h` assume_tac)>>rfs[]>>
      metis_tac[])>>
  simp[]>>
  first_x_assum drule>>
  disch_then drule>>
  fs[]
QED

Theorem earliest_rel_reindex_partial_PR_FILTER_min:
  ∀inds fmlls Clist nw ik is aaa bbb Clist' earliest pos.
  earliest_rel fmlls earliest ∧
  SORTED ($>=) inds ∧
  list_min_opt NONE
    (MAP (λx. any_el (index x) earliest NONE) nw) = SOME pos ∧
  reindex fmlls (FILTER (λx. x ≥ pos) inds) = (aaa,bbb) ∧
  every_check_PR_list fmlls Clist nw ik is aaa bbb = SOME Clist' ⇒
  let (aaa,bbb) = reindex fmlls inds in
  every_check_PR_list fmlls Clist nw ik is aaa bbb = SOME Clist'
Proof
  Induct>>rw[every_check_PR_list_def,reindex_partial_def]
  >- (
    fs[reindex_def]>>
    TOP_CASE_TAC>>fs[]
    >- (
      drule SORTED_TL>>
      strip_tac>>
      first_x_assum drule>>
      simp[])>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    pairarg_tac>>fs[]>>
    rw[]>>fs[]>>
    fs[every_check_PR_list_def]>>
    TOP_CASE_TAC>>fs[]>>
    drule SORTED_TL>>
    strip_tac>>
    first_x_assum drule>>
    simp[])>>
  `EVERY (λx. x < pos) inds` by
    metis_tac[SORTED_HEAD_LESS]>>
  `aaa = [] ∧ bbb = []` by
    (`FILTER (λx. x ≥ pos) inds = []` by
      (fs[FILTER_EQ_NIL,EVERY_MEM]>>
      rw[]>>
      first_x_assum drule>>simp[])>>
    fs[reindex_def])>>
  pairarg_tac>>fs[]>>
  fs[every_check_PR_list_def]>>
  drule earliest_rel_PR_skip>>
  disch_then match_mp_tac>>
  asm_exists_tac>>simp[]>>
  drule reindex_characterize>>
  rw[]>>simp[EVERY_FILTER]>>
  fs[EVERY_MEM]
QED

Theorem earliest_rel_reindex_partial_PR_SOME:
  ∀fmlls Clist nw ik is inds vs inds' vs' rest Clist' earliest pos.
  earliest_rel fmlls earliest ∧
  SORTED ($>=) inds ∧
  list_min_opt NONE
    (MAP (λx. any_el (index x) earliest NONE) nw) = SOME pos ∧
  reindex_partial fmlls pos inds = (inds', vs, rest) ∧
  every_check_PR_list fmlls Clist nw ik is inds' vs = SOME Clist' ⇒
  let (aaa,bbb) = reindex fmlls inds in
  every_check_PR_list fmlls Clist nw ik is aaa bbb = SOME Clist'
Proof
  rw[]>>
  drule reindex_partial_characterize>>
  disch_then drule>>
  rw[]>>
  pairarg_tac>>fs[]>>
  drule reindex_characterize>>rw[]>>
  drule earliest_rel_reindex_partial_PR_FILTER_min>>
  rpt(disch_then drule)>>
  simp[]>>
  disch_then match_mp_tac>>
  Cases_on`reindex fmlls (FILTER (λx. x ≥ pos) inds)` >>fs[]>>
  drule reindex_characterize>>rw[]
QED

Theorem fml_rel_is_PR_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED ($>=) inds ∧
  EVERY ($= w8z) Clist ∧
  earliest_rel fmlls earliest ∧
  wf_fml fml ⇒
  case is_PR_list fmlls inds Clist earliest p C wopt i0 ik of
    SOME (inds', Clist') =>
      is_PR fml p C wopt i0 ik ∧
      ind_rel fmlls inds' ∧
      SORTED ($>=) inds' ∧
      EVERY ($= w8z) Clist'
    | NONE => T
Proof
  rw[is_PR_list_eq,is_PR_def]>>
  drule fml_rel_is_AT_list>>
  rpt(disch_then drule)>>
  disch_then (qspecl_then [`i0`,`C`] mp_tac)>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  TOP_CASE_TAC>>fs[]>>
  strip_tac>>
  IF_CASES_TAC >>fs[]>>
  Cases_on`wopt`>>simp[]
  >- (
    (* RAT *)
    TOP_CASE_TAC>>simp[]>>
    TOP_CASE_TAC>>simp[]>>
    pop_assum mp_tac>> TOP_CASE_TAC>>simp[]
    >- (
      (* Pivot never appeared, so we invent a reindex *)
      strip_tac>>rveq>>simp[]>>
      drule earliest_rel_RAT_NONE_alt>>
      disch_then drule>>
      simp[]>>
      disch_then (qspecl_then [`r`,`y`,`ik`,`inds`] assume_tac)>>
      pairarg_tac>>fs[]>>
      drule reindex_characterize>>
      strip_tac>>rw[]>>
      drule fml_rel_every_check_RAT_list>>
      rpt(disch_then drule)>>
      disch_then(qspecl_then[`p`,`ik`,`y`] mp_tac)>>
      qmatch_asmsub_abbrev_tac`_ aaa bbb = SOME r`>>
      disch_then(qspecl_then[`aaa`,`bbb`] mp_tac)>>simp[]>>
      imp_res_tac ind_rel_reindex>> simp[]>>
      simp[EVERY_MEM,FORALL_PROD])>>
    pairarg_tac>>simp[]>>
    TOP_CASE_TAC>>simp[]>>
    strip_tac>>
    simp[METIS_PROVE [] ``A ∧ B ∧ C ∧ D ⇔ (A ∧ D) ∧ B ∧ C``]>>
    CONJ_TAC>- (
      drule earliest_rel_reindex_partial_RAT_SOME>>
      rpt(disch_then drule)>>
      simp[]>>
      pairarg_tac>>simp[]>>strip_tac>>
      drule reindex_characterize>>
      strip_tac>> rw[]>>
      drule fml_rel_every_check_RAT_list>>
      rpt(disch_then drule)>>
      disch_then(qspecl_then[`p`,`ik`,`y`] mp_tac)>>
      qmatch_asmsub_abbrev_tac`_ aaa bbb = SOME r'`>>
      disch_then(qspecl_then[`aaa`,`bbb`] mp_tac)>>simp[]>>
      imp_res_tac ind_rel_reindex>> simp[]>>
      simp[EVERY_MEM,FORALL_PROD])>>
    drule ind_rel_reindex_partial>>
    rpt(disch_then drule)>>
    simp[])>>
  (* PR *)
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  pop_assum mp_tac>> TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]
  >- (
    strip_tac>>rveq>>simp[]>>
    drule earliest_rel_PR_NONE_alt>>
    disch_then drule>>
    simp[]>>
    disch_then (qspecl_then [`r`,`y`,`ik`,`inds`] assume_tac)>>
    pairarg_tac>>fs[]>>
    drule reindex_characterize>>
    strip_tac>>rw[]>>
    drule fml_rel_every_check_PR_list>>
    rpt(disch_then drule)>>
    qmatch_asmsub_abbrev_tac`every_check_PR_list _ _  _ _ _ aaa bbb`>>
    disch_then(qspecl_then[`x`,`ik`,`y`,`aaa`,`bbb`] mp_tac)>>
    simp[]>>
    imp_res_tac ind_rel_reindex>> simp[]>>
    simp[EVERY_MEM,FORALL_PROD])>>
  pairarg_tac>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  strip_tac>>
  simp[METIS_PROVE [] ``A ∧ B ∧ C ∧ D ⇔ (A ∧ D) ∧ B ∧ C``]>>
  CONJ_TAC>- (
    drule earliest_rel_reindex_partial_PR_SOME>>
    rpt(disch_then drule)>>
    simp[]>>
    pairarg_tac>>simp[]>>strip_tac>>
    drule reindex_characterize>>
    strip_tac>>
    rveq>>
    drule fml_rel_every_check_PR_list>>
    rpt(disch_then drule)>>
    disch_then(qspecl_then[`x`,`ik`,`y`] mp_tac)>>
    qmatch_asmsub_abbrev_tac`_ aaa bbb = SOME r'`>>
    disch_then(qspecl_then[`aaa`,`bbb`] mp_tac)>>simp[]>>
    imp_res_tac ind_rel_reindex>> simp[]>>
    simp[EVERY_MEM,FORALL_PROD])>>
  drule ind_rel_reindex_partial>>
  rpt(disch_then drule)>>
  simp[]
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
    first_x_assum(qspec_then`x` assume_tac)>>fs[any_el_ALT]>>
    IF_CASES_TAC>>fs[]>>
    simp[lookup_delete])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>fs[any_el_ALT]>>
  IF_CASES_TAC>>fs[]
  >-
    (simp[EL_LUPDATE,lookup_delete]>>
    IF_CASES_TAC>>fs[])>>
  simp[lookup_delete]
QED

Theorem ind_rel_update_resize:
  ind_rel fmlls inds ⇒
  ind_rel (update_resize fmlls NONE v n) (n::inds)
Proof
  rw[update_resize_def,ind_rel_def,EL_LUPDATE]>>every_case_tac>>fs[]>>
  fs[ind_rel_def]>>rw[]>>
  fs[IS_SOME_EXISTS,EL_APPEND_EQN]>>
  every_case_tac>>fs[]>>
  rfs[EL_REPLICATE,LENGTH_REPLICATE]
QED

Theorem fml_rel_update_resize:
  fml_rel fml fmlls ⇒
  fml_rel (insert n v fml) (update_resize fmlls NONE (SOME v) n)
Proof
  rw[update_resize_def,fml_rel_def,any_el_ALT]>>
  fs[EL_LUPDATE]>>
  IF_CASES_TAC>> rw[lookup_insert]
  >-
    (first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
    fs[EL_APPEND_EQN]>>
    rw[]>>fs[EL_REPLICATE,LENGTH_REPLICATE])
  >>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[]>>
  simp[EL_APPEND_EQN,EL_REPLICATE]
QED

Theorem earliest_rel_list_delete_list:
  ∀l fmlls earliest.
  earliest_rel fmlls earliest ⇒
  earliest_rel (list_delete_list l fmlls) earliest
Proof
  Induct>>rw[list_delete_list_def]>>
  first_x_assum match_mp_tac>>
  fs[earliest_rel_def]>>
  rw[]>>
  first_x_assum(qspec_then`x` mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  simp[EL_LUPDATE]>>
  rw[]>>
  IF_CASES_TAC>>simp[]
QED

Theorem earliest_rel_update_resize0_pre:
  ∀l earliest n z.
    any_el (index z) (update_earliest earliest n l) NONE =
    min_opt (any_el (index z) earliest NONE)
    (if MEM z l then SOME n else NONE)
Proof
  Induct>>
  simp[update_earliest_def]
  >- (
    simp[min_opt_def]>>
    rw[]>>every_case_tac>>simp[])>>
  ntac 4 strip_tac>>
  Cases_on`z=h`>>simp[]
  >- (
    simp[min_opt_def]>>
    Cases_on`any_el (index h) earliest NONE`>>simp[]>>
    simp[any_el_update_resize]>>
    every_case_tac>>
    simp[MIN_DEF])>>
  simp[min_opt_def]>>
  Cases_on`any_el (index h) earliest NONE`>>simp[]>>
  simp[any_el_update_resize,index_11]
QED

Theorem earliest_rel_update_resize0:
  (∀z. MEM z l ⇒
    case any_el (index z) (update_earliest earliest n l) NONE of
      NONE => F
    | SOME i => i ≤ n)
Proof
  rw[earliest_rel_update_resize0_pre]>>
  simp[min_opt_def]>>every_case_tac>>simp[]
QED

Theorem earliest_rel_update_resize1:
  ∀l fmlls earliest n.
  earliest_rel fmlls earliest ⇒
  earliest_rel fmlls (update_earliest earliest n l)
Proof
  Induct>>rw[update_earliest_def]>>
  first_x_assum match_mp_tac>>
  fs[earliest_rel_def]>>
  rw[]>>
  simp[any_el_update_resize]>>
  IF_CASES_TAC>>simp[min_opt_def]>>
  every_case_tac>>simp[]>>
  rw[]>>TOP_CASE_TAC>>simp[]>>
  first_x_assum(qspec_then`index h` mp_tac)>>simp[]>>
  disch_then drule>>simp[]>>
  metis_tac[]
QED

Theorem earliest_rel_update_resize2:
  ∀l fmlls earliest n.
  earliest_rel fmlls earliest ∧
  (∀z. MEM z l ⇒
    case any_el (index z) earliest NONE of
      NONE => F
    | SOME i => i ≤ n) ⇒
  earliest_rel (update_resize fmlls NONE (SOME l) n) earliest
Proof
  rw[update_resize_def]>>
  fs[earliest_rel_def]>>
  rw[]>>
  first_x_assum(qspec_then`x` mp_tac)
  >- (
    TOP_CASE_TAC>>fs[]>>
    simp[]>>
    rw[EL_LUPDATE]>> rw[]>>
    first_x_assum drule>>simp[]>>
    first_x_assum drule>>simp[]>>
    strip_tac>>
    CCONTR_TAC>>fs[]>>rfs[])>>
  TOP_CASE_TAC>>fs[]
  >- (
    rw[EL_LUPDATE]>> rw[]
    >- (
      first_x_assum drule>>simp[]>>
      strip_tac>>
      CCONTR_TAC>>fs[]>>rfs[])>>
    simp[EL_APPEND_EQN,EL_REPLICATE]>>rw[])>>
  rw[EL_LUPDATE]>> rw[]
  >- (
    first_x_assum drule>>simp[]>>
    first_x_assum drule>>simp[]>>
    strip_tac>>
    CCONTR_TAC>>fs[]>>rfs[])>>
  simp[EL_APPEND_EQN,EL_REPLICATE]>>rw[]
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

Theorem check_earliest_bound:
  ∀inds fmlls x old new i z ls.
  SORTED $>= inds ∧
  check_earliest fmlls x old new inds ∧
  i ≥ old ∧ i < new ∧ i < LENGTH fmlls ∧ MEM i inds ∧ EL i fmlls = SOME ls /\
  MEM z ls ⇒ index z ≠ index x
Proof
  Induct >> rw[check_earliest_def]>>fs[]
  >- (
    fs[any_el_ALT]>>
    metis_tac[index_11])
  >- (
    reverse (Cases_on`h ≥ old`)>>fs[]
    >- (
      drule SORTED_HEAD_LESS>>
      disch_then drule>>
      fs[EVERY_MEM]>>
      disch_then drule>>
      rw[])>>
    first_x_assum match_mp_tac>>
    simp[]>>
    every_case_tac>>fs[]>>
    metis_tac[SORTED_TL])
  >>
    reverse (Cases_on`h ≥ old`)>>fs[]>>
    first_x_assum match_mp_tac>>
    simp[]>>
    every_case_tac>>fs[]>>
    metis_tac[SORTED_TL]
QED

Theorem earliest_rel_hint_earliest:
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  earliest_rel fmlls earliest ∧
  hint_earliest C w ik fmlls inds earliest = earliest' ⇒
  earliest_rel fmlls earliest'
Proof
  strip_tac>>fs[hint_earliest_def]>>
  every_case_tac>>fs[]>>
  fs[earliest_rel_def]>>
  rw[]>>
  simp[any_el_update_resize]>>
  rw[]>>
  first_x_assum(qspec_then`(index (-safe_hd C))` mp_tac)>>rfs[]>>
  disch_then(qspecl_then[`pos`,`z`] assume_tac)>>rfs[]>>
  Cases_on`pos < x`>> fs[]>>
  TOP_CASE_TAC>>rw[]>>
  match_mp_tac check_earliest_bound>>fs[]>>
  asm_exists_tac>>simp[]>>
  asm_exists_tac>>simp[]>>
  qexists_tac`pos`>>fs[]>>
  fs[ind_rel_def]
QED

Theorem fml_rel_check_lpr_step_list:
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED ($>=) inds ∧
  EVERY ($= w8z) Clist ∧
  earliest_rel fmlls earliest ∧
  wf_fml fml ⇒
  case check_lpr_step_list mindel step fmlls inds Clist earliest of
    SOME (fmlls', inds', Clist', earliest') =>
    SORTED ($>=) inds' ∧
    EVERY ($= w8z) Clist' ∧
    ind_rel fmlls' inds' ∧
    earliest_rel fmlls' earliest' ∧
    ∃fml'. check_lpr_step mindel step fml = SOME fml' ∧ fml_rel fml' fmlls'
  | NONE => T
Proof
  simp[check_lpr_step_def,check_lpr_step_list_def]>>
  strip_tac>>
  Cases_on`step`>>simp[]
  >- (
    IF_CASES_TAC>>simp[]>>
    CONJ_TAC >- metis_tac[ind_rel_list_delete_list]>>
    metis_tac[fml_rel_list_delete_list,earliest_rel_list_delete_list])>>
  rename1 `hint_earliest a b c`>>
  drule earliest_rel_hint_earliest>>
  simp[]>>
  disch_then drule>>
  disch_then (qspecl_then [`b`,`c`,`a`] assume_tac)>>
  drule fml_rel_is_PR_list>>
  `EVERY ($= w8z) (resize_Clist a Clist)` by
    rw[resize_Clist_def]>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`b`,`safe_hd a`,`c`,`l0`,`a`] mp_tac)>>
  TOP_CASE_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  simp[safe_hd_def]>>
  IF_CASES_TAC >> simp[]>>
  metis_tac[ind_rel_update_resize_sorted_insert,  SORTED_sorted_insert,
    fml_rel_update_resize,
    earliest_rel_update_resize0,
    earliest_rel_update_resize1, earliest_rel_update_resize2]
QED

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
  fs[MEM_MAP,MEM_FILTER,any_el_ALT]>>
  strip_tac>>
  Cases_on ‘LENGTH fmlls ≤ x’ >> fs [] >>
  fs[fml_rel_def]>>
  first_x_assum(qspec_then`x` assume_tac)>>rfs[any_el_ALT]>>
  fs[IS_SOME_EXISTS]>>
  rfs [] >>
  fs [] >>
  first_x_assum (irule_at Any) >> simp[]
QED

Theorem fml_rel_check_lpr_list:
  ∀steps mindel fml fmlls inds fmlls' inds' Clist earliest.
  fml_rel fml fmlls ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  EVERY ($= w8z) Clist ∧ wf_fml fml ∧
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
  drule  fml_rel_check_lpr_step_list>>
  rpt (disch_then drule)>>
  disch_then (qspecl_then [`h`,`mindel`] mp_tac)>> simp[]>>
  strip_tac>>
  simp[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  asm_exists_tac>>fs[]>>
  qexists_tac`r`>>fs[]>>
  match_mp_tac check_lpr_step_wf_fml>>
  metis_tac[]
QED

(* Construct "hash table" mapping clauses -> list of indexes *)
Definition hash_insert_def:
  hash_insert fm k v =
    case FLOOKUP fm k of
      NONE => fm |+ (k,[v])
    | SOME vs => fm |+ (k, v::vs)
End

Definition hash_clauses_aux_def:
  (hash_clauses_aux [] [] fm = fm) ∧
  (hash_clauses_aux (c::cs) (i::is) fm =
    hash_clauses_aux cs is (hash_insert fm c i))
End

(* Construct a "hash table" from an existing formula representation *)
Definition hash_clauses_list_def:
  hash_clauses_list fml inds =
  case reindex fml inds of
    (inds', cls) => hash_clauses_aux cls inds' FEMPTY
End

(*
  Run "first part" of proof that updates all moving parts simultaneously:
    - fml is an array of index -> clauses
    - inds is lazily updated list of active indices (only added to)
    - earliest tracks optimization information
    - fm is a "hashtable" mapping clause -> list of indices it appears

  The "second part" of the proof only needs to project out the "fm" component
*)
Definition run_proof_step_list_def:
  (run_proof_step_list (fml,inds,earliest,fm,n,mv) (Del C) =
    case FLOOKUP fm C of
      NONE => (* the clause to be deleted doesn't exist, don't do anything *)
        (fml,inds,earliest,fm,n,mv)
    | SOME cls => (* list of clause indices *)
        (list_delete_list cls fml, inds, earliest, fm \\ C,n,mv)) ∧
  (run_proof_step_list (fml,inds,earliest,fm,n,mv) (Add C) =
    (update_resize fml NONE (SOME C) n,
     sorted_insert n inds,
     update_earliest earliest n C,
     hash_insert fm C n,
     n+1,
     MAX mv (list_max_index C + 1)))
End

Definition run_proof_list_def:
  run_proof_list data pf = FOLDL run_proof_step_list data pf
End

Definition check_lpr_range_list_def:
  check_lpr_range_list lpr fml inds earliest mv n pf i j =
  if i ≤ j then
    let fm = hash_clauses_list fml inds in
    let pfij = TAKE j pf in
    let pfi = TAKE i pfij in
    let pfj = DROP i pfij in
    let (fml',inds',earliest',fm',n',mv') = run_proof_list (fml,inds,earliest,fm,n,mv) pfi in
    let (fml'',inds'',earliest'',fm'',n'',mv'') = run_proof_list (fml',inds',earliest',fm',n',mv') pfj in
    let cls = MAP FST (fmap_to_alist fm'') in
    check_lpr_sat_equiv_list lpr fml' inds' (REPLICATE mv' w8z) earliest' 0 cls
  else F
End

(* The "easy" part of the induction *)
Theorem run_proof_list_rels:
  ∀pf fmlls inds earliest fm n mv
      fmlls' inds' earliest' fm' n' mv'.
  run_proof_list (fmlls,inds,earliest,fm,n,mv) pf = (fmlls',inds',earliest',fm',n',mv') ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  earliest_rel fmlls earliest
  ⇒
  ind_rel fmlls' inds' ∧
  SORTED $>= inds' ∧
  earliest_rel fmlls' earliest'
Proof
  Induct>>fs[run_proof_list_def]>>
  Cases>>ntac 13 strip_tac>>
  fs[run_proof_step_list_def]>>every_case_tac>>fs[]>>
  first_x_assum drule>>
  disch_then match_mp_tac>>fs[]
  >- metis_tac[ind_rel_list_delete_list,earliest_rel_list_delete_list] >>
  CONJ_TAC >-
    metis_tac[ind_rel_update_resize_sorted_insert]>>
  simp[SORTED_sorted_insert]>>
  rw[resize_Clist_def]>>
  metis_tac[earliest_rel_update_resize0, earliest_rel_update_resize1, earliest_rel_update_resize2]
QED

(* the hash set contains all the information necessary and nothing extra *)
Definition hash_rel_def:
  hash_rel fmlls fm ⇔
  (∀C x. x < LENGTH fmlls ∧ EL x fmlls = SOME C ⇒
    ∃xs. FLOOKUP fm C = SOME xs ∧ MEM x xs) ∧
  (∀C x xs. FLOOKUP fm C = SOME xs ∧ MEM x xs ⇒
    x < LENGTH fmlls ∧ EL x fmlls = SOME C)
End

Theorem fml_rel_from_to_AList:
  fml_rel fml fmlls ⇒
  fml_rel (fromAList (toAList fml)) fmlls
Proof
  rw[fml_rel_def]>>rw[]>>
  first_x_assum (qspec_then`x` assume_tac)>>rfs[]>>
  simp[lookup_fromAList,ALOOKUP_toAList]
QED

Theorem EL_list_delete_list:
  ∀y ls x.
  x < LENGTH ls ⇒
  EL x (list_delete_list y ls) =
  if MEM x y then NONE else EL x ls
Proof
  Induct>>rw[list_delete_list_def]>>
  fs[]>>rfs[EL_LUPDATE]
QED

Theorem hash_rel_list_delete_list:
  hash_rel fmlls fm ∧
  FLOOKUP fm l = SOME x ⇒
  hash_rel (list_delete_list x fmlls) (fm \\ l)
Proof
  rw[hash_rel_def]
  >- (
    pop_assum mp_tac>>
    DEP_REWRITE_TAC [EL_list_delete_list]>>
    simp[]>>
    strip_tac>>
    last_x_assum drule>>
    disch_then drule>>
    strip_tac>>
    first_x_assum drule>>
    fs[DOMSUB_FLOOKUP_THM]>>
    CCONTR_TAC>>rw[]>>
    gs[])
  >- (
    fs[DOMSUB_FLOOKUP_THM]>>
    metis_tac[]) >>
  fs[DOMSUB_FLOOKUP_THM]>>
  first_assum drule>>
  disch_then drule>>
  simp[EL_list_delete_list]>>
  rw[]>>CCONTR_TAC>>rw[]>>
  first_assum drule>>
  disch_then drule>>
  qpat_x_assum`_ = SOME xs` mp_tac>>
  first_assum drule>>
  disch_then drule>>
  rpt strip_tac>>
  fs[]
QED

Theorem FLOOKUP_hash_insert:
  FLOOKUP (hash_insert fm l n) C =
  if C = l then
    case FLOOKUP fm C of
      NONE => SOME [n]
    | SOME ls => SOME (n::ls)
  else
    FLOOKUP fm C
Proof
  rw[hash_insert_def]>>every_case_tac>>fs[FLOOKUP_UPDATE]
QED

Theorem EL_update_resize:
  x < LENGTH (update_resize fmlls NONE (SOME l) n) ⇒
  EL x (update_resize fmlls NONE (SOME l) n)  =
  if x = n then SOME l
  else
    if x < LENGTH fmlls then EL x fmlls
    else NONE
Proof
  rw[update_resize_def,EL_LUPDATE]>>
  fs[EL_APPEND_EQN,EL_REPLICATE]
QED

Theorem hash_rel_hash_insert:
  hash_rel fmlls fm ∧
  (∀x. IS_SOME(any_el x fmlls NONE) ⇒ x < n)
  ⇒
  hash_rel (update_resize fmlls NONE (SOME l) n) (hash_insert fm l n)
Proof
  simp[hash_rel_def,hash_insert_def,EL_update_resize]>>
  strip_tac>>
  CONJ_TAC
  >- (
    rw[]>>rfs[EL_update_resize]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    strip_tac>>rw[]
    >- (TOP_CASE_TAC>>simp[FLOOKUP_UPDATE])>>
    TOP_CASE_TAC>>simp[FLOOKUP_UPDATE]>>rw[]>>fs[]
    >- (
      last_x_assum drule>>
      disch_then drule>>
      rw[])>>
    metis_tac[SOME_11]) >>
  ntac 4 strip_tac>>
  every_case_tac>>fs[]
  >- (
    pop_assum mp_tac>>simp[FLOOKUP_UPDATE]>>
    IF_CASES_TAC>>simp[]>>strip_tac>>rveq>>fs[]
    >- (
      CONJ_ASM1_TAC >> simp[EL_update_resize]>>
      simp[update_resize_def]>>
      every_case_tac>>simp[])>>
    first_x_assum drule>>
    disch_then drule>>
    strip_tac>>
    CONJ_ASM1_TAC >> simp[EL_update_resize]
    >- (simp[update_resize_def]>> every_case_tac>>simp[])>>
    rw[]>>
    first_x_assum(qspec_then`n` mp_tac)>>simp[any_el_ALT])
  >- (
    pop_assum mp_tac>>simp[FLOOKUP_UPDATE]>>
    IF_CASES_TAC>>simp[]>>strip_tac>>rveq>>fs[]
    >- (
      CONJ_ASM1_TAC >> simp[EL_update_resize]>>
      simp[update_resize_def]>>
      every_case_tac>>simp[])>>
    first_x_assum drule>>
    disch_then drule>>
    strip_tac>>
    CONJ_ASM1_TAC >> simp[EL_update_resize]
    >- (simp[update_resize_def]>> every_case_tac>>simp[])>>
    rw[]
    >- rw[update_resize_def]
    >>
      first_x_assum(qspec_then`n` mp_tac)>>simp[any_el_ALT])
QED

Theorem same_lookup_fml_rel:
  fml_rel a b ∧
  (∀x. sptree$lookup x a = lookup x a') ⇒
  fml_rel a' b
Proof
  rw[fml_rel_def]>>
  metis_tac[]
QED

(* The "hard" part of the induction *)
Theorem fml_rel_run_proof_list:
  ∀pf fmlls inds earliest fm n mv
      fmlls' inds' earliest' fm' n' mv'
      fml fml' m.
  run_proof_list (fmlls,inds,earliest,fm,n,mv) pf = (fmlls',inds',earliest',fm',n',mv') ∧
  run_proof_spt (fml,n) pf = (fml',m) ∧
  fml_rel fml fmlls ∧
  hash_rel fmlls fm ∧
  (∀x. IS_SOME(any_el x fmlls NONE) ⇒ x < n) ⇒
    n' = m ∧
    fml_rel fml' fmlls' ∧
    hash_rel fmlls' fm' ∧
    (∀x. IS_SOME(any_el x fmlls' NONE) ⇒ x < n')
Proof
  Induct>>fs[run_proof_list_def,run_proof_spt_def]>>
  Cases>>fs[run_proof_step_spt_def,run_proof_step_list_def]>>
  rpt gen_tac>>
  strip_tac>>
  every_case_tac>>fs[]>>
  first_x_assum drule>>
  disch_then drule>>
  disch_then match_mp_tac
  >- (
    fs[]>>
    qmatch_goalsub_abbrev_tac`FOLDL _ _ lss`>>
    `lss = []` by (
      simp[Abbr`lss`,FILTER_EQ_NIL]>>
      rw[EVERY_MEM,FORALL_PROD,MEM_toAList]>>
      fs[hash_rel_def,fml_rel_def]>>
      CCONTR_TAC>>
      fs[]>>
      last_x_assum(qspec_then`p_1` mp_tac)>>
      fs[any_el_ALT]>>rw[]>>
      CCONTR_TAC>>fs[] >>
      last_x_assum drule>>
      disch_then(qspec_then`l` assume_tac)>>rfs[])>>
    simp[])
  >- (
    CONJ_TAC>- (
      qmatch_goalsub_abbrev_tac`FOLDL _ _ lss`>>
      `set x = set lss` by (
        simp[Abbr`lss`,EXTENSION,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList]>>
        fs[hash_rel_def,fml_rel_def,any_el_ALT]>>
        first_x_assum drule>>
        rw[EQ_IMP_THM]>>
        first_x_assum drule>>strip_tac>>
        last_x_assum(qspec_then`x'` assume_tac)>>rfs[])>>
      drule fml_rel_list_delete_list>>
      disch_then (qspecl_then [`x`,`list_delete_list x fmlls`] mp_tac)>>
      simp[]>>
      strip_tac>> drule same_lookup_fml_rel>>
      disch_then match_mp_tac>>
      simp[lookup_FOLDL_delete])>>
    CONJ_TAC>- metis_tac[hash_rel_list_delete_list]>>
    rw[any_el_ALT, EL_list_delete_list]) >>
  simp[fml_rel_update_resize]>>
  drule hash_rel_hash_insert>>simp[]>>
  rw[any_el_update_resize]>>
  every_case_tac>>fs[]>>
  last_x_assum drule>>simp[]
QED

Theorem FLOOKUP_hash_clauses_aux_0:
  ∀xs ys C x is fm.
  LENGTH xs = LENGTH ys ∧
  FLOOKUP fm C = SOME is ∧ MEM x is ⇒
  ∃is'.
    FLOOKUP (hash_clauses_aux xs ys fm) C = SOME is' ∧ MEM x is'
Proof
  Induct>>fs[hash_clauses_aux_def]>>rw[]>>
  Cases_on`ys`>>fs[hash_clauses_aux_def]>>rw[]>>
  first_x_assum match_mp_tac>>fs[FLOOKUP_hash_insert]>>
  rw[]>>simp[]
QED

Theorem FLOOKUP_hash_clauses_aux_1:
  ∀xs ys x y fm.
  LENGTH xs = LENGTH ys ∧
  MEM (x,y) (ZIP (xs,ys)) ⇒
  ∃is.
    FLOOKUP (hash_clauses_aux xs ys fm) x = SOME is ∧ MEM y is
Proof
  Induct>>fs[hash_clauses_aux_def]>>rw[]>>
  Cases_on`ys`>>fs[hash_clauses_aux_def]>>rw[]>>
  match_mp_tac FLOOKUP_hash_clauses_aux_0>>
  simp[FLOOKUP_hash_insert]>>
  every_case_tac>>fs[]
QED

Theorem FLOOKUP_hash_clauses_aux_2:
  ∀xs ys fm x is y.
  FLOOKUP (hash_clauses_aux xs ys fm) x = SOME is ∧ MEM y is ∧
  LENGTH xs = LENGTH ys ⇒
  (∃is'. FLOOKUP fm x = SOME is' ∧ MEM y is') ∨
  MEM (x,y) (ZIP (xs,ys))
Proof
  Induct>>fs[hash_clauses_aux_def]>>rw[]>>
  Cases_on`ys`>>fs[hash_clauses_aux_def]>>
  first_x_assum(qspec_then`t` mp_tac)>>fs[]>>
  disch_then drule>>
  disch_then drule>>
  strip_tac>>simp[]>>
  qpat_x_assum`_=SOME is` kall_tac>>
  fs[hash_insert_def]>>every_case_tac>>fs[FLOOKUP_UPDATE]>>
  every_case_tac>>fs[]>>rw[]>>fs[]
QED

Theorem hash_rel_hash_clauses_list:
  ind_rel fmlls inds ⇒
  hash_rel fmlls (hash_clauses_list fmlls inds)
Proof
  simp[hash_clauses_list_def]>>
  TOP_CASE_TAC>>fs[]>>
  drule reindex_characterize>>
  rw[]>>
  simp[hash_rel_def]>>
  CONJ_TAC>- (
    rw[]>>
    match_mp_tac FLOOKUP_hash_clauses_aux_1>>
    fs[MEM_ZIP]>>
    qmatch_goalsub_abbrev_tac`MAP _ lss`>>
    `MEM x lss` by (
      simp[Abbr`lss`,MEM_FILTER]>>
      fs[ind_rel_def,any_el_ALT])>>
    fs[MEM_EL]>>
    qexists_tac`n`>>simp[EL_MAP,any_el_ALT]>>
    rw[])>>
  ntac 4 strip_tac>>
  drule FLOOKUP_hash_clauses_aux_2>>
  disch_then drule>>
  simp[MEM_ZIP]>>strip_tac>>
  qmatch_asmsub_abbrev_tac`EL n lss`>>
  `MEM x lss` by
    metis_tac[MEM_EL]>>
  `IS_SOME (any_el x fmlls NONE)` by
    fs[Abbr`lss`,MEM_FILTER]>>
  pop_assum mp_tac>>
  simp[any_el_ALT]>>
  rw[]>>simp[EL_MAP]>>
  Cases_on`EL (EL n lss) fmlls`>>fs[]
QED

Theorem fml_rel_check_lpr_range_list:
  check_lpr_range_list lpr fmlls inds earliest mv n pf i j ∧
  fml_rel fml fmlls ∧
  (∀x. IS_SOME(any_el x fmlls NONE) ⇒ x < n) ∧
  ind_rel fmlls inds ∧
  SORTED $>= inds ∧
  earliest_rel fmlls earliest ∧
  wf_fml fml ∧ EVERY wf_proof pf ∧ EVERY wf_lpr lpr
  ⇒
  check_lpr_range lpr fml n pf i j
Proof
  rw[check_lpr_range_def,check_lpr_range_list_def]>>
  rpt(pairarg_tac >> fs[])>>
  fs[check_lpr_sat_equiv_list_def,check_lpr_list_def]>>
  every_case_tac>>fs[]>>
  qpat_x_assum `run_proof_list _ _ = (fml', _)` assume_tac>>
  drule run_proof_list_rels>>
  simp[]>> strip_tac>>
  drule fml_rel_run_proof_list>>
  simp[TAKE_TAKE_T]>>
  qpat_x_assum `run_proof_spt _ _ = (fml1, _)` assume_tac>>
  disch_then drule>>
  simp[]>>
  impl_tac>-
    fs[hash_rel_hash_clauses_list]>>
  rw[]>>
  simp[check_lpr_sat_equiv_def]>>
  drule fml_rel_check_lpr_list>>
  `EVERY ($= w8z) (REPLICATE mv' w8z)` by fs[EVERY_REPLICATE]>>
  rpt(disch_then drule)>>
  drule wf_run_proof_spt>> simp[EVERY_TAKE]>>
  strip_tac>>
  rpt(disch_then drule)>>
  rw[]>>simp[]>>
  drule fml_rel_contains_clauses_list>>
  rpt (disch_then drule)>>
  qpat_x_assum `run_proof_list _ _ = (fml'', _)` assume_tac>>
  drule run_proof_list_rels>>
  simp[]>> strip_tac>>
  drule (GEN_ALL fml_rel_run_proof_list)>>
  qpat_x_assum `run_proof_spt _ _ = (fml2, _)` assume_tac>>
  disch_then drule>>
  simp[]>>
  strip_tac >>
  qmatch_goalsub_abbrev_tac`_ _ A  ==> _ _ B`>>
  `set B ⊆ set A` by (
    unabbrev_all_tac>>simp[SUBSET_DEF]>>
    ntac 3 (pop_assum mp_tac)>>
    rpt (pop_assum kall_tac)>>
    rw[fml_rel_def,hash_rel_def,any_el_ALT]>>
    fs[MEM_MAP,EXISTS_PROD,MEM_toAList]>>
    last_x_assum(qspec_then`p_1` assume_tac)>>
    every_case_tac>>fs[]>>
    first_x_assum drule>>
    disch_then drule>>simp[]>>
    rw[FDOM_FLOOKUP]>>
    metis_tac[])>>
  pop_assum mp_tac>>
  simp[contains_clauses_def,SUBSET_DEF,EVERY_MEM]>>
  rw[]
QED

val _ = export_theory();
