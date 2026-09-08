(*
  This refines the XLRUP checker to a list-based implementation.
*)
Theory xlrup_list
Ancestors
  cnf ccnf xor xor_list xlrup ccnf_list mlstring mlvector sptree
Libs
  preamble

(*** The XOR store.

  XORs are accumulated into a byte list, which the array implementation
  updates in place. Note the two index spaces: the RUP assignment array
  dml is indexed by the original variable, while the XOR bitstrings are
  indexed by the dense name given by tn.

  The XOR store keeps an option at each index, unlike the clause array,
  which marks a free slot with the vcc_none sentinel. The sentinel is
  sound there because vcc_none is a clause no assignment satisfies, so a
  deleted clause cannot be used to justify anything. A strxor admits no
  such value: adding a free slot into the accumulator would be a no-op
  rather than a failure, so a deleted XOR must be absent, not empty. ***)

Definition xfml_rel_def:
  xfml_rel fml fmlls ⇔
  ∀n. FLOOKUP fml n = any_el n fmlls NONE
End

Theorem xfml_rel_any_el:
  xfml_rel fml fmlls ⇒
  any_el n fmlls NONE = FLOOKUP fml n
Proof
  rw[xfml_rel_def]
QED

Theorem xfml_rel_update_resize:
  xfml_rel fml fmlls ⇒
  xfml_rel (fml |+ (n,v)) (update_resize fmlls NONE (SOME v) n)
Proof
  rw[xfml_rel_def,any_el_update_resize,FLOOKUP_UPDATE]>>
  rw[]
QED

Theorem xfml_rel_REPLICATE_NONE:
  xfml_rel FEMPTY (REPLICATE n NONE)
Proof
  rw[xfml_rel_def,any_el_ALT,EL_REPLICATE]
QED

Definition xdelete_list_def:
  xdelete_list fml i =
  if i < LENGTH fml
  then LUPDATE NONE i fml
  else fml
End

Definition xdelete_ids_list_def:
  xdelete_ids_list fml ls = FOLDL xdelete_list fml ls
End

Theorem LENGTH_xdelete_list[simp]:
  LENGTH (xdelete_list fmlls l) = LENGTH fmlls
Proof
  rw[xdelete_list_def]
QED

Theorem any_el_xdelete_list:
  any_el n (xdelete_list fmlls l) NONE =
  if l = n then NONE else any_el n fmlls NONE
Proof
  rw[xdelete_list_def,any_el_ALT,EL_LUPDATE]>>
  gvs[]
QED

Theorem xfml_rel_xdelete_list:
  xfml_rel fml fmlls ⇒
  xfml_rel (fml \\ l) (xdelete_list fmlls l)
Proof
  simp[xfml_rel_def,DOMSUB_FLOOKUP_THM]>>
  rw[any_el_xdelete_list]
QED

Theorem xfml_rel_xdelete_ids_list:
  ∀l fml fmlls.
  xfml_rel fml fmlls ⇒
  xfml_rel (delete_ids fml l) (xdelete_ids_list fmlls l)
Proof
  simp[delete_ids_def,xdelete_ids_list_def]>>
  Induct>>rw[]>>
  first_x_assum irule>>
  metis_tac[xfml_rel_xdelete_list]
QED

(*** Adding XORs into a byte-list accumulator, for the array
  implementation. This is an equivalent of add_xors_aux. ***)

Definition add_xors_aux_c_def:
  (add_xors_aux_c fml [] s = SOME s) ∧
  (add_xors_aux_c fml (i::is) s =
  case FLOOKUP fml i of NONE => NONE
  | SOME x =>
    add_xors_aux_c fml is (strxor_c s x))
End

Theorem add_xors_aux_c_add_xors_aux:
  ∀is s t.
  add_xors_aux_c fml is s = SOME t ⇒
  add_xors_aux fml is
    (implode (MAP fromByte s)) = SOME (implode (MAP fromByte t))
Proof
  Induct>>rw[add_xors_aux_c_def,add_xors_aux_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  simp[strxor_c,MAP_MAP_o,o_DEF]
QED

Definition add_xors_aux_c_list_def:
  (add_xors_aux_c_list fml [] s = SOME s) ∧
  (add_xors_aux_c_list fml (i::is) s =
  case any_el i fml NONE of NONE => NONE
  | SOME x =>
    add_xors_aux_c_list fml is (strxor_c s x))
End

Theorem add_xors_aux_c_list:
  ∀is x y.
  xfml_rel fml fmlls ∧
  add_xors_aux_c_list fmlls is x = SOME y ⇒
  add_xors_aux_c fml is x = SOME y
Proof
  Induct>>rw[add_xors_aux_c_def,add_xors_aux_c_list_def]>>
  drule xfml_rel_any_el>>rw[]>>
  gvs[AllCaseEqs()]>>
  first_x_assum irule>>
  gvs[]
QED

Definition unit_prop_xor_list_def:
  unit_prop_xor_list t s l =
  case lookup (Num (ABS l)) t of NONE => s
  | SOME n =>
  if n < 8 * LENGTH s then
    if l > 0 then
      (if get_bit_list s n then
        flip_bit_list (set_bit_list s n F) 0
      else s)
    else set_bit_list s n F
  else s
End

Theorem unit_prop_xor_list:
  implode (MAP fromByte (unit_prop_xor_list t x l)) =
  unit_prop_xor t (implode (MAP fromByte x)) l
Proof
  rw[unit_prop_xor_def,unit_prop_xor_list_def]>>
  TOP_CASE_TAC>>simp[]>>
  qmatch_goalsub_rename_tac`v < 8 * LENGTH x`>>
  IF_CASES_TAC>>fs[]>>
  `v DIV 8 < LENGTH x` by
    (DEP_REWRITE_TAC[DIV_LT_X]>>simp[])>>
  rw[]>>
  gvs[get_bit_list]>>
  simp[set_bit_list]>>
  DEP_REWRITE_TAC[flip_bit_list]>>simp[]>>
  simp[MAP_MAP_o,o_DEF]
QED

Definition get_units_list_def:
  (get_units_list fml [] cs = SOME cs) ∧
  (get_units_list fml (i::is) cs =
  let v = any_el i fml vcc_none in
  if v = vcc_none then NONE
  else
    if length v = 1
    then get_units_list fml is (sub v 0::cs)
    else NONE)
End

(* One-directional, like the core's refinement lemmas: fml_rel does not rule
  out FLOOKUP fml n = SOME vcc_none, which the array cannot tell apart from a
  free slot, so the two sides are not equal -- only sound in this direction. *)
Theorem get_units_list:
  ∀is acc cs.
  fml_rel fml fmlls ∧
  get_units_list fmlls is acc = SOME cs ⇒
  get_units fml is acc = SOME cs
Proof
  Induct>>rw[get_units_list_def,get_units_def]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_any_el_NEQ_vcc_none_FLOOKUP>>
  strip_tac>>gvs[]
QED

Definition unit_props_xor_list_def:
  unit_props_xor_list fml t ls s =
  case get_units_list fml ls [] of NONE => NONE
  | SOME cs =>
    SOME (FOLDL (unit_prop_xor_list t) s cs)
End

Theorem unit_props_xor_list:
  ∀is x y.
  fml_rel fml fmlls ∧
  unit_props_xor_list fmlls t is x = SOME y ⇒
  unit_props_xor fml t is (implode (MAP fromByte x)) =
    SOME (implode (MAP fromByte y))
Proof
  rw[unit_props_xor_def,unit_props_xor_list_def]>>
  gvs[AllCaseEqs()]>>
  drule_all get_units_list>>
  rw[]>>
  rpt (pop_assum kall_tac)>>
  qid_spec_tac`x`>>
  qid_spec_tac`cs`>>
  ho_match_mp_tac SNOC_INDUCT>>rw[]>>
  simp[FOLDL_SNOC,GSYM unit_prop_xor_list]
QED

Definition is_xor_list_def:
  is_xor_list def fml is cfml cis t s =
  let r = REPLICATE def (0w:word8) in
  let r = strxor_c r s in
  case add_xors_aux_c_list fml is r of NONE => F
  | SOME x =>
    case unit_props_xor_list cfml t cis x of
      NONE => F
    | SOME y => is_emp_xor_list y
End

Theorem is_xor_list:
  xfml_rel fml fmlls ∧
  fml_rel cfml cfmlls ∧
  is_xor_list def fmlls is cfmlls cis t x ⇒
  is_xor def fml is cfml cis t x
Proof
  rw[is_xor_list_def]>>
  every_case_tac>>fs[]>>
  drule_all add_xors_aux_c_list>>
  rw[is_xor_def]>>
  drule add_xors_aux_c_add_xors_aux>>
  simp[strxor_c,MAP_MAP_o,o_DEF,implode_REPLICATE_extend_s]>>
  rw[]>>
  drule_all unit_props_xor_list>>
  fs[is_emp_xor_list]
QED

Definition conv_rawxor_list_def:
  conv_rawxor_list mv x =
  let r = REPLICATE (MAX 1 mv) (0w:word8) in
  let r = flip_bit_list r 0 in
    implode (MAP fromByte (conv_xor_aux_list r x))
End

Theorem conv_rawxor_list:
  conv_rawxor_list mv x = conv_rawxor mv x
Proof
  rw[conv_rawxor_list_def,conv_rawxor_def]>>
  simp[conv_xor_aux_list]>>
  DEP_REWRITE_TAC[flip_bit_list]>>
  simp[MAP_MAP_o,o_DEF,implode_REPLICATE_extend_s]
QED

Definition conv_xor_mv_list_def:
  conv_xor_mv_list mv x =
  conv_rawxor_list mv (MAP to_ilit x)
End

Theorem conv_xor_mv_list:
  conv_xor_mv_list mv x = conv_xor_mv mv x
Proof
  rw[conv_xor_mv_list_def,conv_xor_mv_def,conv_rawxor_list]
QED

(* TODO: There is a minor optimization here if we inline
  conv_rawxor into the addition in is_cfromx_list
  so that the byte array is allocated only once *)
Definition strxor_imp_cclause_list_def:
  strxor_imp_cclause_list mv s c =
  let t = conv_rawxor_list mv c in
  is_emp_xor_list (strxor_c s t)
End

Theorem strxor_imp_cclause_list:
  strxor_imp_cclause_list def x c =
  strxor_imp_cclause def (implode (MAP fromByte x)) c
Proof
  rw[strxor_imp_cclause_list_def,strxor_imp_cclause_def]>>
  simp[is_emp_xor_list,strxor_c]>>
  simp[MAP_MAP_o,o_DEF,conv_rawxor_list]
QED

Definition is_cfromx_list_def:
  is_cfromx_list def fml is c =
  let r = REPLICATE def (0w:word8) in
  case add_xors_aux_c_list fml is r of NONE => F
  | SOME x => strxor_imp_cclause_list def x c
End

Theorem is_cfromx_list:
  xfml_rel fml fmlls ∧
  is_cfromx_list def fmlls is c ⇒
  is_cfromx def fml is c
Proof
  rw[is_cfromx_list_def]>>
  every_case_tac>>fs[]>>
  drule_all add_xors_aux_c_list>>
  rw[is_cfromx_def]>>
  drule add_xors_aux_c_add_xors_aux>>
  simp[implode_REPLICATE_extend_s]>>
  rw[]>>
  fs[strxor_imp_cclause_list]
QED

Definition get_constrs_list_def:
  (get_constrs_list fml [] = SOME []) ∧
  (get_constrs_list fml (i::is) =
    let Ci = any_el i fml vcc_none in
    if Ci = vcc_none then NONE
    else
      (case get_constrs_list fml is of NONE => NONE
      | SOME Cs => SOME (toList Ci::Cs)))
End

Theorem fml_rel_get_constrs_list:
  ∀is ds.
  fml_rel fml fmlls ∧
  get_constrs_list fmlls is = SOME ds ⇒
  get_constrs fml is = SOME ds
Proof
  Induct>>rw[get_constrs_def,get_constrs_list_def]>>
  gvs[AllCaseEqs()]>>
  drule_all fml_rel_any_el_NEQ_vcc_none_FLOOKUP>>
  strip_tac>>gvs[]
QED

Definition is_xfromc_list_def:
  is_xfromc_list fml is rx =
  case get_constrs_list fml is of NONE => F
  | SOME ds =>
    check_rawxor_imp ds rx
End

Theorem is_xfromc_list:
  fml_rel fml fmlls ∧
  is_xfromc_list fmlls is rx ⇒
  is_xfromc fml is rx
Proof
  rw[is_xfromc_list_def,is_xfromc_def]>>
  every_case_tac>>
  fs[]>>
  metis_tac[fml_rel_get_constrs_list,option_CLAUSES]
QED

(*** The checker ***)

Definition check_xlrup_list_def:
  check_xlrup_list xorig xlrup cfml xfml tn def dml b =
  case xlrup of
    Del cl =>
    SOME (delete_ids_list cfml cl, xfml, tn, def, dml, b)
  | RUP n C i0 =>
    (case is_rup_list cfml dml b C i0 of
      (T, dml', b') =>
      SOME (insert_vcc_list cfml n C, xfml, tn, def, dml', b')
    | _ => NONE)
  | XOrig n rX =>
    if MEM rX xorig
    then
      let (mX,tn) = ren_lit_ls tn rX [] in
      let X = conv_xor_mv_list def mX in
      SOME (cfml, update_resize xfml NONE (SOME X) n, tn,
        MAX def (strlen X), dml, b)
    else NONE
  | XAdd n rX i0 i1 =>
    let (mX,tn) = ren_int_ls tn rX [] in
    let X = conv_rawxor_list def mX in
    if is_xor_list def xfml i0 cfml i1 (FST tn) X then
      SOME (cfml, update_resize xfml NONE (SOME X) n, tn,
        MAX def (strlen X), dml, b)
    else NONE
  | XDel xl =>
    SOME (cfml, xdelete_ids_list xfml xl, tn, def, dml, b)
  | CFromX n C i0 =>
    let (mC,tn) = ren_int_ls tn C [] in
    if is_cfromx_list def xfml i0 mC then
      SOME (insert_vcc_list cfml n (Vector C), xfml, tn,
        def, resize_dm dml b (Vector C))
    else NONE
  | XFromC n rX i0 =>
    if is_xfromc_list cfml i0 rX then
      let (mX,tn) = ren_int_ls tn rX [] in
      let X = conv_rawxor_list def mX in
      SOME (cfml, update_resize xfml NONE (SOME X) n, tn,
        MAX def (strlen X), dml, b)
    else NONE
End

Theorem check_xlrup_list:
  fml_rel cfml cfmlls ∧
  xfml_rel xfml xfmlls ∧
  dm_rel dm dml b ∧
  check_xlrup_list xorig xlrup cfmlls xfmlls tn def dml b =
    SOME (cfmlls', xfmlls', tn', def', dml', b') ⇒
  ∃cfml' xfml' dm'.
    check_xlrup xorig xlrup cfml xfml tn def =
      SOME (cfml',xfml',tn',def') ∧
    fml_rel cfml' cfmlls' ∧
    xfml_rel xfml' xfmlls' ∧
    dm_rel dm' dml' b'
Proof
  simp[check_xlrup_def,check_xlrup_list_def]>>
  strip_tac>>
  Cases_on`xlrup`>>gvs[AllCaseEqs()]
  >- (* Del *)
    (simp[fml_rel_delete_ids_list]>>metis_tac[])
  >- ( (* RUP *)
    drule_all is_rup_list>>rw[]>>
    drule fml_rel_insert_vcc_list>>
    metis_tac[])
  >- ( (* XOrig *)
    pairarg_tac>>gvs[conv_xor_mv_list]>>
    metis_tac[xfml_rel_update_resize])
  >- ( (* XAdd *)
    pairarg_tac>>gvs[conv_rawxor_list]>>
    drule_all is_xor_list>>
    metis_tac[xfml_rel_update_resize])
  >- (* XDel *)
    (simp[xfml_rel_xdelete_ids_list]>>metis_tac[])
  >- ( (* CFromX *)
    pairarg_tac>>gvs[]>>
    drule_all is_cfromx_list>>
    rw[]>>
    drule fml_rel_insert_vcc_list>>
    gvs[resize_dm_def]>>
    drule_all dm_rel_reset_dm_list>>
    metis_tac[])
  >- ( (* XFromC *)
    pairarg_tac>>gvs[conv_rawxor_list]>>
    drule_all is_xfromc_list>>
    metis_tac[xfml_rel_update_resize])
QED


Theorem check_xlrup_list_bnd_fml:
  bnd_fml cfmlls (LENGTH dml) ∧
  check_xlrup_list xorig xlrup cfmlls xfmlls tn def dml b =
    SOME (cfmlls', xfmlls', tn', def', dml', b') ⇒
  bnd_fml cfmlls' (LENGTH dml')
Proof
  simp[check_xlrup_list_def]>>
  strip_tac>>
  Cases_on`xlrup`>>gvs[AllCaseEqs()]
  >- metis_tac[bnd_fml_delete_ids_list]
  >- (
    drule_all bnd_fml_is_rup_list>>
    metis_tac[bnd_fml_insert_vcc_list])
  >- (pairarg_tac>>gvs[])
  >- (pairarg_tac>>gvs[])
  >- (
    pairarg_tac>>gvs[]>>
    metis_tac[bnd_fml_insert_vcc_list_resize_dm])
  >- (pairarg_tac>>gvs[])
QED

Definition check_xlrups_list_def:
  (check_xlrups_list xorig [] cfml xfml tn def dml b =
    SOME (cfml, xfml, tn, def)) ∧
  (check_xlrups_list xorig (x::xs) cfml xfml tn def dml b =
    case check_xlrup_list xorig x cfml xfml tn def dml b of
      NONE => NONE
    | SOME (cfml', xfml', tn', def', dml', b') =>
      check_xlrups_list xorig xs cfml' xfml' tn' def' dml' b')
End

Theorem check_xlrups_list:
  ∀xlrups cfml cfmlls xfml xfmlls cfmlls' xfmlls'
    tn tn' def def' dml b dm.
  fml_rel cfml cfmlls ∧
  xfml_rel xfml xfmlls ∧
  dm_rel dm dml b ∧
  check_xlrups_list xorig xlrups cfmlls xfmlls tn def dml b =
    SOME (cfmlls', xfmlls', tn', def') ⇒
  ∃cfml' xfml'.
    check_xlrups xorig xlrups cfml xfml tn def =
      SOME (cfml',xfml',tn',def') ∧
    fml_rel cfml' cfmlls' ∧
    xfml_rel xfml' xfmlls'
Proof
  Induct>>fs[check_xlrups_list_def,check_xlrups_def]>>
  rw[]>>gvs[AllCaseEqs()]>>
  drule check_xlrup_list>>
  rpt (disch_then drule)>>
  strip_tac>>
  first_x_assum drule_all>>
  rw[]>>
  metis_tac[]
QED

Definition check_xlrups_unsat_list_def:
  check_xlrups_unsat_list xorig xlrups cfml xfml tn def dml b =
  case check_xlrups_list xorig xlrups cfml xfml tn def dml b of
    NONE => F
  | SOME (cfml', xfml', tn', def') =>
    contains_emp_list cfml'
End

Theorem check_xlrups_unsat_list:
  fml_rel cfml cfmlls ∧
  xfml_rel xfml xfmlls ∧
  dm_rel dm dml b ∧
  check_xlrups_unsat_list xorig xlrups cfmlls xfmlls tn def dml b ⇒
  check_xlrups_unsat xorig xlrups cfml xfml tn def
Proof
  simp[check_xlrups_unsat_list_def,check_xlrups_unsat_def]>>
  strip_tac>>
  Cases_on`check_xlrups_list xorig xlrups cfmlls xfmlls tn def dml b`>>
  gvs[]>>
  rename1`SOME res`>>
  PairCases_on`res`>>gvs[]>>
  drule_all check_xlrups_list>>
  strip_tac>>gvs[]>>
  metis_tac[fml_rel_contains_emp_list]
QED

(* The list-level checker's guarantee, phrased on the parsed formula *)
Theorem check_xlrups_unsat_list_sound:
  check_xlrups_unsat_list xfml xlrups
    (build_cfml_list kc (conv_cfml cfml) nc)
    (REPLICATE nx NONE)
    (LN,1) def
    (REPLICATE n 0w) 1w ∧
  EVERY (EVERY nz_lit) cfml ∧
  EVERY wf_xlrup xlrups ⇒
  sols (cfml,xfml) = {}
Proof
  strip_tac>>
  irule check_xlrups_unsat_conv_sound>>
  simp[]>>
  qexists_tac`kc`>>
  qexists_tac`def`>>
  qexists_tac`xlrups`>>
  simp[]>>
  irule check_xlrups_unsat_list>>
  rpt (first_x_assum (irule_at Any))>>
  irule_at Any fml_rel_build_cfml_list>>
  irule_at Any xfml_rel_REPLICATE_NONE>>
  irule_at Any dm_rel_FEMPTY_REPLICATE>>
  metis_tac[]
QED
