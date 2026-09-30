(*
  This refines the XLRUP checker to a list-based implementation.
*)
Theory xlrup_list
Ancestors
  cnf ccnf syntax_helper xor xor_list xlrup ccnf_list mlstring
  mlvector sptree comparison
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

Theorem xfml_rel_delete_list:
  xfml_rel fml fmlls ⇒
  xfml_rel (fml \\ l) (delete_list NONE fmlls l)
Proof
  simp[xfml_rel_def,DOMSUB_FLOOKUP_THM]>>
  rw[any_el_delete_list]
QED

Theorem xfml_rel_delete_ids_list:
  ∀l fml fmlls.
  xfml_rel fml fmlls ⇒
  xfml_rel (delete_ids fml l) (delete_ids_list NONE fmlls l)
Proof
  simp[delete_ids_def,delete_ids_list_def]>>
  Induct>>rw[]>>
  first_x_assum irule>>
  metis_tac[xfml_rel_delete_list]
QED

Theorem xfml_rel_delete_ids_vb_list:
  ∀fml s i len fmlls.
  xfml_rel fml fmlls ⇒
  xfml_rel (delete_ids_vb fml s i len) (delete_ids_vb_list NONE fmlls s i len)
Proof
  ho_match_mp_tac delete_ids_vb_ind>>
  rw[]>>
  simp[Once delete_ids_vb_def,Once delete_ids_vb_list_def]>>
  pairarg_tac>>rw[]>>
  first_x_assum irule>>
  metis_tac[xfml_rel_delete_list]
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

(*** The dense renaming.

  The spec's sptree is refined to a list indexed by the original variable.
  A zero entry marks an unnamed variable: dense names start at 1, so a zero
  and an index past the end both mean absent. ***)

Type tname_list = ``:num list # num``;

Definition nm_rel_def:
  nm_rel t (tl:num list) ⇔
  ∀v. lookup v t =
    (let m = any_el v tl 0 in
      if m = 0 then NONE else SOME m)
End

Definition tn_rel_def:
  tn_rel ((t,n):tname) ((tl,n'):tname_list) ⇔
  n = n' ∧ 0 < n ∧ nm_rel t tl
End

Theorem tn_rel_nm_rel:
  tn_rel tn tnl ⇒ nm_rel (FST tn) (FST tnl)
Proof
  PairCases_on`tn`>>PairCases_on`tnl`>>
  rw[tn_rel_def]
QED

Definition get_name_list_def:
  get_name_list ((tl,n):tname_list) (v:num) =
  let m = any_el v tl 0 in
  if m = 0
  then (n, (update_resize tl 0 n v, n+(1:num)))
  else (m, (tl,n))
End

Theorem tn_rel_get_name_list:
  tn_rel tn tnl ∧
  get_name_list tnl v = (m,tnl') ⇒
  ∃tn'.
    get_name tn v = (m,tn') ∧
    tn_rel tn' tnl'
Proof
  PairCases_on`tn`>>PairCases_on`tnl`>>
  simp[tn_rel_def,get_name_list_def,get_name_def]>>
  strip_tac>>
  `lookup v tn0 =
    if any_el v tnl0 0 = 0 then NONE
    else SOME (any_el v tnl0 0)` by gvs[nm_rel_def]>>
  Cases_on`any_el v tnl0 0 = 0`>>
  gvs[]>>
  gvs[tn_rel_def,nm_rel_def,lookup_insert,any_el_update_resize]>>
  rw[]>>gvs[]
QED

Definition unit_prop_xor_list_def:
  unit_prop_xor_list tl s l =
  let n = any_el (Num (ABS l)) tl 0 in
  if n = 0 then s
  else
  if n < 8 * LENGTH s then
    if l > 0 then
      (if get_bit_list s n then
        flip_bit_list (set_bit_list s n F) 0
      else s)
    else set_bit_list s n F
  else s
End

Theorem unit_prop_xor_list:
  nm_rel t tl ⇒
  implode (MAP fromByte (unit_prop_xor_list tl x l)) =
  unit_prop_xor t (implode (MAP fromByte x)) l
Proof
  strip_tac>>
  `lookup (Num (ABS l)) t =
    if any_el (Num (ABS l)) tl 0 = 0 then NONE
    else SOME (any_el (Num (ABS l)) tl 0)` by gvs[nm_rel_def]>>
  rw[unit_prop_xor_def,unit_prop_xor_list_def]>>
  qabbrev_tac`v = any_el (Num (ABS l)) tl 0`>>
  `v DIV 8 < LENGTH x` by
    (DEP_REWRITE_TAC[DIV_LT_X]>>simp[])>>
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
  unit_props_xor_list fml tl ls s =
  case get_units_list fml ls [] of NONE => NONE
  | SOME cs =>
    SOME (FOLDL (unit_prop_xor_list tl) s cs)
End

Theorem unit_props_xor_list:
  ∀is x y.
  fml_rel fml fmlls ∧
  nm_rel t tl ∧
  unit_props_xor_list fmlls tl is x = SOME y ⇒
  unit_props_xor fml t is (implode (MAP fromByte x)) =
    SOME (implode (MAP fromByte y))
Proof
  rw[unit_props_xor_def,unit_props_xor_list_def]>>
  gvs[AllCaseEqs()]>>
  drule_all get_units_list>>
  rw[]>>
  qpat_x_assum`nm_rel _ _` mp_tac>>
  rpt (pop_assum kall_tac)>>
  strip_tac>>
  qid_spec_tac`x`>>
  qid_spec_tac`cs`>>
  ho_match_mp_tac SNOC_INDUCT>>rw[]>>
  simp[FOLDL_SNOC]>>
  drule unit_prop_xor_list>>
  simp[]
QED

Definition is_xor_list_def:
  is_xor_list def fml is cfml cis tl s =
  let r = REPLICATE def (0w:word8) in
  let r = strxor_c r s in
  case add_xors_aux_c_list fml is r of NONE => F
  | SOME x =>
    case unit_props_xor_list cfml tl cis x of
      NONE => F
    | SOME y => is_emp_xor_list y
End

Theorem is_xor_list:
  xfml_rel fml fmlls ∧
  fml_rel cfml cfmlls ∧
  nm_rel t tl ∧
  is_xor_list def fmlls is cfmlls cis tl x ⇒
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

(* The clause's XOR need not be built: flipping its bits into s gives
  the same verdict *)
Theorem strxor_imp_cclause_list_flip:
  strxor_imp_cclause_list mv s c ⇔
  is_emp_xor_list (conv_xor_aux_list (flip_bit_list (extend_s_list s 1) 0) c)
Proof
  simp[strxor_imp_cclause_list_def,conv_rawxor_list_def,
    is_emp_xor_list_bit_list,bit_list_strxor_c,GSYM bit_list_get_bit]>>
  ONCE_REWRITE_TAC[bit_list_conv_xor_aux_list]>>
  qspecl_then[`s`,`1`] assume_tac LENGTH_extend_s_list>>
  simp[bit_list_flip_bit_list,bit_list_REPLICATE_0w,bit_list_extend_s_list]>>
  metis_tac[]
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

(*** The binary format's hint walkers, on the list representation.
  Each is the list function above reading its ids with parse_vb_int. ***)

Definition add_xors_aux_vb_list_def:
  add_xors_aux_vb_list fml s i len acc =
  let (m,i) = parse_vb_int s i len in
  if m ≤ 0 then SOME acc
  else
  case any_el (Num m) fml NONE of NONE => NONE
  | SOME x =>
    add_xors_aux_vb_list fml s i len (strxor_c acc x)
Termination
  WF_REL_TAC` measure (λ(f,s,i,len,acc). len-i)`>>
  rw[] >> fs[parse_vb_int_def,parse_vb_num_def,
  UNCURRY_EQ,AllCaseEqs()] >> rveq >>
  fs[] >>
  last_x_assum (assume_tac o GSYM) >>
  drule_all parse_vb_num_aux_i >>
  fs[]
End

Theorem add_xors_aux_vb_list:
  ∀fmlls s i len x y.
  xfml_rel fml fmlls ∧
  add_xors_aux_vb_list fmlls s i len x = SOME y ⇒
  add_xors_aux_vb fml s i len
    (implode (MAP fromByte x)) = SOME (implode (MAP fromByte y))
Proof
  ho_match_mp_tac add_xors_aux_vb_list_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once add_xors_aux_vb_list_def,Once add_xors_aux_vb_def]>>
  pairarg_tac>>gvs[]>>
  IF_CASES_TAC>>simp[]>>
  drule xfml_rel_any_el>>rw[]>>
  gvs[AllCaseEqs()]>>
  gvs[strxor_c,MAP_MAP_o,o_DEF]
QED

Definition get_units_vb_list_def:
  get_units_vb_list fml s i len cs =
  let (m,i) = parse_vb_int s i len in
  if m ≤ 0 then SOME cs
  else
  let v = any_el (Num m) fml vcc_none in
  if v = vcc_none then NONE
  else
    if length v = 1
    then get_units_vb_list fml s i len (sub v 0::cs)
    else NONE
Termination
  WF_REL_TAC` measure (λ(f,s,i,len,cs). len-i)`>>
  rw[] >> fs[parse_vb_int_def,parse_vb_num_def,
  UNCURRY_EQ,AllCaseEqs()] >> rveq >>
  fs[] >>
  last_x_assum (assume_tac o GSYM) >>
  drule_all parse_vb_num_aux_i >>
  fs[]
End

Theorem get_units_vb_list:
  ∀fmlls s i len acc cs.
  fml_rel fml fmlls ∧
  get_units_vb_list fmlls s i len acc = SOME cs ⇒
  get_units_vb fml s i len acc = SOME cs
Proof
  ho_match_mp_tac get_units_vb_list_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once get_units_vb_list_def,Once get_units_vb_def]>>
  pairarg_tac>>gvs[]>>
  IF_CASES_TAC>>simp[]>>
  rw[AllCaseEqs()]>>
  drule_all fml_rel_any_el_NEQ_vcc_none_FLOOKUP>>
  strip_tac>>gvs[]
QED

Definition unit_props_xor_vb_list_def:
  unit_props_xor_vb_list fml tl s x =
  case get_units_vb_list fml s 0 (strlen s) [] of NONE => NONE
  | SOME cs =>
    SOME (FOLDL (unit_prop_xor_list tl) x cs)
End

Theorem unit_props_xor_vb_list:
  fml_rel fml fmlls ∧
  nm_rel t tl ∧
  unit_props_xor_vb_list fmlls tl s x = SOME y ⇒
  unit_props_xor_vb fml t s (implode (MAP fromByte x)) =
    SOME (implode (MAP fromByte y))
Proof
  rw[unit_props_xor_vb_def,unit_props_xor_vb_list_def]>>
  gvs[AllCaseEqs()]>>
  drule_all get_units_vb_list>>
  rw[]>>
  qpat_x_assum`nm_rel _ _` mp_tac>>
  rpt (pop_assum kall_tac)>>
  strip_tac>>
  qid_spec_tac`x`>>
  qid_spec_tac`cs`>>
  ho_match_mp_tac SNOC_INDUCT>>rw[]>>
  simp[FOLDL_SNOC]>>
  drule unit_prop_xor_list>>
  simp[]
QED

Definition is_xor_vb_list_def:
  is_xor_vb_list def fml s1 cfml s2 tl s =
  let r = REPLICATE def (0w:word8) in
  let r = strxor_c r s in
  case add_xors_aux_vb_list fml s1 0 (strlen s1) r of NONE => F
  | SOME x =>
    case unit_props_xor_vb_list cfml tl s2 x of
      NONE => F
    | SOME y => is_emp_xor_list y
End

Theorem is_xor_vb_list:
  xfml_rel fml fmlls ∧
  fml_rel cfml cfmlls ∧
  nm_rel t tl ∧
  is_xor_vb_list def fmlls s1 cfmlls s2 tl x ⇒
  is_xor_vb def fml s1 cfml s2 t x
Proof
  rw[is_xor_vb_list_def]>>
  every_case_tac>>fs[]>>
  drule_all add_xors_aux_vb_list>>
  rw[is_xor_vb_def]>>
  gvs[strxor_c,MAP_MAP_o,o_DEF,implode_REPLICATE_extend_s]>>
  drule_all unit_props_xor_vb_list>>
  fs[is_emp_xor_list]
QED

Definition is_cfromx_vb_list_def:
  is_cfromx_vb_list def fml s c =
  let r = REPLICATE def (0w:word8) in
  case add_xors_aux_vb_list fml s 0 (strlen s) r of NONE => F
  | SOME x => strxor_imp_cclause_list def x c
End

Theorem is_cfromx_vb_list:
  xfml_rel fml fmlls ∧
  is_cfromx_vb_list def fmlls s c ⇒
  is_cfromx_vb def fml s c
Proof
  rw[is_cfromx_vb_list_def]>>
  every_case_tac>>fs[]>>
  drule_all add_xors_aux_vb_list>>
  simp[implode_REPLICATE_extend_s]>>
  rw[is_cfromx_vb_def]>>
  fs[strxor_imp_cclause_list]
QED

(*** The checks started from zero bytes of any length, as the array
  checkers in xlrup_arrayProg do: the verdicts depend only on the bits
  of the accumulator ***)

Overload same_bits = ``λa b. ∀n. bit_list a n ⇔ bit_list b n``;

Theorem bit_list_unit_prop_xor_list:
  bit_list (unit_prop_xor_list tl s l) m ⇔
  let k = any_el (Num (ABS l)) tl 0 in
  if k = 0 then bit_list s m
  else if l > 0 then
    (if bit_list s k then ((m ≠ k ∧ bit_list s m) ⇎ m = 0)
     else bit_list s m)
  else m ≠ k ∧ bit_list s m
Proof
  qabbrev_tac`k = any_el (Num (ABS l)) tl 0`>>
  simp[unit_prop_xor_list_def]>>
  Cases_on`k = 0`>>simp[]>>
  Cases_on`k < 8 * LENGTH s`
  >- (
    `k DIV 8 < LENGTH s` by simp[DIV_LT_X]>>
    `bit_list s k ⇔ get_bit_list s k` by simp[bit_list_def]>>
    `LENGTH (set_bit_list s k F) = LENGTH s` by simp[set_bit_list_def]>>
    `0 < LENGTH s` by (Cases_on`s`>>fs[])>>
    rw[bit_list_set_bit_list,bit_list_flip_bit_list]>>
    metis_tac[])>>
  `¬bit_list s k` by simp[bit_list_def,DIV_LT_X]>>
  rw[]>>metis_tac[]
QED

Theorem add_xors_aux_c_list_same_bits:
  ∀is a b.
  same_bits a b ⇒
  OPTREL same_bits
    (add_xors_aux_c_list fml is a) (add_xors_aux_c_list fml is b)
Proof
  Induct>>rw[add_xors_aux_c_list_def]>>
  TOP_CASE_TAC>>simp[]>>
  first_x_assum irule>>
  simp[bit_list_strxor_c]
QED

Theorem add_xors_aux_vb_list_same_bits:
  ∀fml s i len a b.
  same_bits a b ⇒
  OPTREL same_bits
    (add_xors_aux_vb_list fml s i len a) (add_xors_aux_vb_list fml s i len b)
Proof
  ho_match_mp_tac add_xors_aux_vb_list_ind>>rw[]>>
  ONCE_REWRITE_TAC[add_xors_aux_vb_list_def]>>
  Cases_on`parse_vb_int s i len`>>simp[]>>
  IF_CASES_TAC>>simp[]>>
  TOP_CASE_TAC>>simp[]>>
  first_x_assum irule>>
  simp[bit_list_strxor_c]
QED

Theorem FOLDL_unit_prop_xor_list_same_bits:
  ∀cs a b.
  same_bits a b ⇒
  same_bits
    (FOLDL (unit_prop_xor_list tl) a cs) (FOLDL (unit_prop_xor_list tl) b cs)
Proof
  Induct>>rw[]>>
  first_x_assum irule>>
  gvs[bit_list_unit_prop_xor_list]
QED

Theorem is_xor_list_zeros:
  EVERY ($= 0w) zs ⇒
  (is_xor_list def fml is cfml cis tl s ⇔
   case add_xors_aux_c_list fml is (strxor_c zs s) of
     NONE => F
   | SOME x =>
     case unit_props_xor_list cfml tl cis x of
       NONE => F
     | SOME y => is_emp_xor_list y)
Proof
  strip_tac>>
  `∀n. ¬bit_list zs n` by
    metis_tac[is_emp_xor_list_bit_list,is_emp_xor_list_def]>>
  `same_bits (strxor_c (REPLICATE def 0w) s) (strxor_c zs s)` by
    simp[bit_list_strxor_c,bit_list_REPLICATE_0w]>>
  drule add_xors_aux_c_list_same_bits>>
  disch_then (qspecl_then[`fml`,`is`] mp_tac)>>
  simp[is_xor_list_def]>>
  Cases_on`add_xors_aux_c_list fml is (strxor_c zs s)`>>
  Cases_on`add_xors_aux_c_list fml is (strxor_c (REPLICATE def 0w) s)`>>
  simp[optionTheory.OPTREL_def]>>
  strip_tac>>simp[unit_props_xor_list_def]>>
  Cases_on`get_units_list cfml cis []`>>simp[is_emp_xor_list_bit_list]>>
  drule FOLDL_unit_prop_xor_list_same_bits>>simp[]
QED

Theorem is_xor_vb_list_zeros:
  EVERY ($= 0w) zs ⇒
  (is_xor_vb_list def fml s1 cfml s2 tl s ⇔
   case add_xors_aux_vb_list fml s1 0 (strlen s1) (strxor_c zs s) of
     NONE => F
   | SOME x =>
     case unit_props_xor_vb_list cfml tl s2 x of
       NONE => F
     | SOME y => is_emp_xor_list y)
Proof
  strip_tac>>
  `∀n. ¬bit_list zs n` by
    metis_tac[is_emp_xor_list_bit_list,is_emp_xor_list_def]>>
  `same_bits (strxor_c (REPLICATE def 0w) s) (strxor_c zs s)` by
    simp[bit_list_strxor_c,bit_list_REPLICATE_0w]>>
  drule add_xors_aux_vb_list_same_bits>>
  disch_then (qspecl_then[`fml`,`s1`,`0`,`strlen s1`] mp_tac)>>
  simp[is_xor_vb_list_def]>>
  Cases_on`add_xors_aux_vb_list fml s1 0 (strlen s1) (strxor_c zs s)`>>
  Cases_on`add_xors_aux_vb_list fml s1 0 (strlen s1)
    (strxor_c (REPLICATE def 0w) s)`>>
  simp[optionTheory.OPTREL_def]>>
  strip_tac>>simp[unit_props_xor_vb_list_def]>>
  Cases_on`get_units_vb_list cfml s2 0 (strlen s2) []`>>
  simp[is_emp_xor_list_bit_list]>>
  drule FOLDL_unit_prop_xor_list_same_bits>>simp[]
QED

Theorem is_cfromx_list_zeros:
  EVERY ($= 0w) zs ⇒
  (is_cfromx_list def fml is c ⇔
   case add_xors_aux_c_list fml is zs of
     NONE => F
   | SOME x =>
     is_emp_xor_list
       (conv_xor_aux_list (flip_bit_list (extend_s_list x 1) 0) c))
Proof
  strip_tac>>
  `∀n. ¬bit_list zs n` by
    metis_tac[is_emp_xor_list_bit_list,is_emp_xor_list_def]>>
  `same_bits (REPLICATE def 0w) zs` by simp[bit_list_REPLICATE_0w]>>
  drule add_xors_aux_c_list_same_bits>>
  disch_then (qspecl_then[`fml`,`is`] mp_tac)>>
  simp[is_cfromx_list_def,strxor_imp_cclause_list_flip]>>
  Cases_on`add_xors_aux_c_list fml is zs`>>
  Cases_on`add_xors_aux_c_list fml is (REPLICATE def 0w)`>>
  simp[optionTheory.OPTREL_def]>>
  strip_tac>>
  simp[is_emp_xor_list_bit_list]>>
  ONCE_REWRITE_TAC[bit_list_conv_xor_aux_list]>>
  qspecl_then[`x`,`1`] assume_tac LENGTH_extend_s_list>>
  qspecl_then[`x'`,`1`] assume_tac LENGTH_extend_s_list>>
  gvs[bit_list_flip_bit_list,bit_list_extend_s_list]
QED

Theorem is_cfromx_vb_list_zeros:
  EVERY ($= 0w) zs ⇒
  (is_cfromx_vb_list def fml s c ⇔
   case add_xors_aux_vb_list fml s 0 (strlen s) zs of
     NONE => F
   | SOME x =>
     is_emp_xor_list
       (conv_xor_aux_list (flip_bit_list (extend_s_list x 1) 0) c))
Proof
  strip_tac>>
  `∀n. ¬bit_list zs n` by
    metis_tac[is_emp_xor_list_bit_list,is_emp_xor_list_def]>>
  `same_bits (REPLICATE def 0w) zs` by simp[bit_list_REPLICATE_0w]>>
  drule add_xors_aux_vb_list_same_bits>>
  disch_then (qspecl_then[`fml`,`s`,`0`,`strlen s`] mp_tac)>>
  simp[is_cfromx_vb_list_def,strxor_imp_cclause_list_flip]>>
  Cases_on`add_xors_aux_vb_list fml s 0 (strlen s) zs`>>
  Cases_on`add_xors_aux_vb_list fml s 0 (strlen s) (REPLICATE def 0w)`>>
  simp[optionTheory.OPTREL_def]>>
  strip_tac>>
  simp[is_emp_xor_list_bit_list]>>
  ONCE_REWRITE_TAC[bit_list_conv_xor_aux_list]>>
  qspecl_then[`x`,`1`] assume_tac LENGTH_extend_s_list>>
  qspecl_then[`x'`,`1`] assume_tac LENGTH_extend_s_list>>
  gvs[bit_list_flip_bit_list,bit_list_extend_s_list]
QED

Definition get_constrs_vb_list_def:
  get_constrs_vb_list fml s i len =
  let (m,i) = parse_vb_int s i len in
  if m ≤ 0 then SOME []
  else
  let Ci = any_el (Num m) fml vcc_none in
  if Ci = vcc_none then NONE
  else
    (case get_constrs_vb_list fml s i len of NONE => NONE
    | SOME Cs => SOME (toList Ci::Cs))
Termination
  WF_REL_TAC` measure (λ(f,s,i,len). len-i)`>>
  rw[] >> fs[parse_vb_int_def,parse_vb_num_def,
  UNCURRY_EQ,AllCaseEqs()] >> rveq >>
  fs[] >>
  last_x_assum (assume_tac o GSYM) >>
  drule_all parse_vb_num_aux_i >>
  fs[]
End

Theorem fml_rel_get_constrs_vb_list:
  ∀fmlls s i len ds.
  fml_rel fml fmlls ∧
  get_constrs_vb_list fmlls s i len = SOME ds ⇒
  get_constrs_vb fml s i len = SOME ds
Proof
  ho_match_mp_tac get_constrs_vb_list_ind>>
  rw[]>>
  pop_assum mp_tac>>
  simp[Once get_constrs_vb_list_def,Once get_constrs_vb_def]>>
  pairarg_tac>>gvs[]>>
  IF_CASES_TAC>>simp[]>>
  rw[AllCaseEqs()]>>
  drule_all fml_rel_any_el_NEQ_vcc_none_FLOOKUP>>
  strip_tac>>gvs[]
QED

Definition is_xfromc_vb_list_def:
  is_xfromc_vb_list fml s rx =
  case get_constrs_vb_list fml s 0 (strlen s) of NONE => F
  | SOME ds =>
    check_rawxor_imp ds rx
End

Theorem is_xfromc_vb_list:
  fml_rel fml fmlls ∧
  is_xfromc_vb_list fmlls s rx ⇒
  is_xfromc_vb fml s rx
Proof
  rw[is_xfromc_vb_list_def,is_xfromc_vb_def]>>
  every_case_tac>>
  fs[]>>
  metis_tac[fml_rel_get_constrs_vb_list,option_CLAUSES]
QED

Definition ren_int_ls_list_def:
  (ren_int_ls_list tnl [] (acc:int list) = (REVERSE acc, tnl)) ∧
  (ren_int_ls_list tnl (i::is) acc =
    let v = Num (ABS i) in
    let (m,tnl) = get_name_list tnl v in
    let vv = if i < (0:int) then -&m else &m in
    ren_int_ls_list tnl is (vv::acc))
End

Theorem tn_rel_ren_int_ls_list:
  ∀is tn tnl acc ms tnl'.
  tn_rel tn tnl ∧
  ren_int_ls_list tnl is acc = (ms,tnl') ⇒
  ∃tn'.
    ren_int_ls tn is acc = (ms,tn') ∧
    tn_rel tn' tnl'
Proof
  Induct>>
  simp[ren_int_ls_def,ren_int_ls_list_def]>>
  rw[]>>
  rpt (pairarg_tac>>gvs[])>>
  drule_all tn_rel_get_name_list>>
  strip_tac>>
  gvs[]>>
  first_x_assum drule_all>>
  rw[]
QED

Definition ren_lit_ls_list_def:
  (ren_lit_ls_list tnl [] (acc:cmsxor) = (REVERSE acc, tnl)) ∧
  (ren_lit_ls_list tnl (i::is) acc =
    case i of
      Pos v =>
      let (m,tnl) = get_name_list tnl v in
        ren_lit_ls_list tnl is (Pos m::acc)
    | Neg v =>
      let (m,tnl) = get_name_list tnl v in
        ren_lit_ls_list tnl is (Neg m::acc))
End

Theorem tn_rel_ren_lit_ls_list:
  ∀is tn tnl acc ms tnl'.
  tn_rel tn tnl ∧
  ren_lit_ls_list tnl is acc = (ms,tnl') ⇒
  ∃tn'.
    ren_lit_ls tn is acc = (ms,tn') ∧
    tn_rel tn' tnl'
Proof
  Induct>>
  simp[ren_lit_ls_def,ren_lit_ls_list_def]>>
  rw[]>>
  TOP_CASE_TAC>>
  rpt (pairarg_tac>>gvs[])>>
  drule_all tn_rel_get_name_list>>
  strip_tac>>
  gvs[]>>
  first_x_assum drule_all>>
  rw[]
QED

(*** The original XORs.

  An XOrig step looks its XOR up in a finite map keyed by the literal
  list; the map is compiled to a balanced tree ordered by cmsxor_cmp. ***)

Definition lit_cmp_def:
  lit_cmp (l1:num lit) l2 =
  case l1 of
    Pos v1 =>
      (case l2 of
        Pos v2 => num_cmp v1 v2
      | Neg _ => LESS)
  | Neg v1 =>
      (case l2 of
        Pos _ => GREATER
      | Neg v2 => num_cmp v1 v2)
End

Definition cmsxor_cmp_def:
  cmsxor_cmp = list_cmp lit_cmp
End

Theorem lit_forall[local]:
  (∀x. P x) ⇔ (∀v. P (Pos v)) ∧ (∀v. P (Neg v))
Proof
  eq_tac>>rw[]>>
  Cases_on`x`>>fs[]
QED

Theorem TotOrd_lit_cmp:
  TotOrd lit_cmp
Proof
  mp_tac TotOrd_num_cmp>>
  fs[totoTheory.TotOrd,lit_cmp_def,AllCaseEqs(),lit_forall]>>
  simp[SF DNF_ss,PULL_EXISTS]>>
  metis_tac[]
QED

Theorem TotOrd_cmsxor_cmp:
  TotOrd cmsxor_cmp
Proof
  rewrite_tac[cmsxor_cmp_def]>>
  irule TotOrd_list_cmp>>
  simp[TotOrd_lit_cmp]
QED

Definition build_xorig_map_def:
  (build_xorig_map [] = (FEMPTY : cmsxor |-> unit)) ∧
  (build_xorig_map (x::xs) = fmap_update (build_xorig_map xs) x ())
End

Theorem FDOM_build_xorig_map:
  ∀xs. FDOM (build_xorig_map xs) = set xs
Proof
  Induct>>rw[build_xorig_map_def]
QED

Definition xorig_mem_def:
  xorig_mem (xm:cmsxor |-> unit) rX ⇔ IS_SOME (FLOOKUP xm rX)
End

Theorem xorig_mem_FDOM:
  xorig_mem xm rX ⇔ rX ∈ FDOM xm
Proof
  rw[xorig_mem_def,IS_SOME_EXISTS,flookup_thm]
QED

(*** The checker ***)

Definition check_xlrup_list_def:
  check_xlrup_list xm xlrup cfml xfml tnl def dml b =
  case xlrup of
    Del cl =>
    SOME (delete_ids_list vcc_none cfml cl, xfml, tnl, def, dml, b)
  | RUP n C i0 =>
    (case is_rup_list cfml dml b C i0 of
      (T, dml', b') =>
      SOME (insert_vcc_list cfml n C, xfml, tnl, def, dml', b')
    | _ => NONE)
  | XOrig n rX =>
    if xorig_mem xm rX
    then
      let (mX,tnl) = ren_lit_ls_list tnl rX [] in
      let X = conv_xor_mv_list def mX in
      SOME (cfml, update_resize xfml NONE (SOME X) n, tnl,
        MAX def (strlen X), dml, b)
    else NONE
  | XAdd n rX i0 i1 =>
    let (mX,tnl) = ren_int_ls_list tnl rX [] in
    let X = conv_rawxor_list def mX in
    if is_xor_list def xfml i0 cfml i1 (FST tnl) X then
      SOME (cfml, update_resize xfml NONE (SOME X) n, tnl,
        MAX def (strlen X), dml, b)
    else NONE
  | XDel xl =>
    SOME (cfml, delete_ids_list NONE xfml xl, tnl, def, dml, b)
  | CFromX n C i0 =>
    let (mC,tnl) = ren_int_ls_list tnl C [] in
    if is_cfromx_list def xfml i0 mC then
      SOME (insert_vcc_list cfml n (Vector C), xfml, tnl,
        def, resize_dm dml b (Vector C))
    else NONE
  | XFromC n rX i0 =>
    if is_xfromc_list cfml i0 rX then
      let (mX,tnl) = ren_int_ls_list tnl rX [] in
      let X = conv_rawxor_list def mX in
      SOME (cfml, update_resize xfml NONE (SOME X) n, tnl,
        MAX def (strlen X), dml, b)
    else NONE
  | Delvb s =>
    SOME (delete_ids_vb_list vcc_none cfml s 1 (strlen s), xfml, tnl, def,
      dml, b)
  | RUPvb n C s =>
    (case is_rup_vb_list cfml dml b C s of
      (T, dml', b') =>
      SOME (insert_vcc_list cfml n C, xfml, tnl, def, dml', b')
    | _ => NONE)
  | XAddvb n rX s1 s2 =>
    let (mX,tnl) = ren_int_ls_list tnl rX [] in
    let X = conv_rawxor_list def mX in
    if is_xor_vb_list def xfml s1 cfml s2 (FST tnl) X then
      SOME (cfml, update_resize xfml NONE (SOME X) n, tnl,
        MAX def (strlen X), dml, b)
    else NONE
  | XDelvb s =>
    SOME (cfml, delete_ids_vb_list NONE xfml s 2 (strlen s), tnl, def, dml, b)
  | CFromXvb n C s =>
    let (mC,tnl) = ren_int_ls_list tnl C [] in
    if is_cfromx_vb_list def xfml s mC then
      SOME (insert_vcc_list cfml n (Vector C), xfml, tnl,
        def, resize_dm dml b (Vector C))
    else NONE
  | XFromCvb n rX s =>
    if is_xfromc_vb_list cfml s rX then
      let (mX,tnl) = ren_int_ls_list tnl rX [] in
      let X = conv_rawxor_list def mX in
      SOME (cfml, update_resize xfml NONE (SOME X) n, tnl,
        MAX def (strlen X), dml, b)
    else NONE
End

Theorem check_xlrup_list:
  fml_rel cfml cfmlls ∧
  xfml_rel xfml xfmlls ∧
  dm_rel dm dml b ∧
  tn_rel tn tnl ∧
  FDOM xm = set xorig ∧
  check_xlrup_list xm xlrup cfmlls xfmlls tnl def dml b =
    SOME (cfmlls', xfmlls', tnl', def', dml', b') ⇒
  ∃cfml' xfml' tn' dm'.
    check_xlrup xorig xlrup cfml xfml tn def =
      SOME (cfml',xfml',tn',def') ∧
    fml_rel cfml' cfmlls' ∧
    xfml_rel xfml' xfmlls' ∧
    tn_rel tn' tnl' ∧
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
    gvs[xorig_mem_FDOM]>>
    rpt (pairarg_tac>>gvs[conv_xor_mv_list])>>
    drule_all tn_rel_ren_lit_ls_list>>
    strip_tac>>gvs[]>>
    metis_tac[xfml_rel_update_resize])
  >- ( (* XAdd *)
    rpt (pairarg_tac>>gvs[conv_rawxor_list])>>
    drule_all tn_rel_ren_int_ls_list>>
    strip_tac>>gvs[]>>
    imp_res_tac tn_rel_nm_rel>>
    drule_all is_xor_list>>
    strip_tac>>
    metis_tac[xfml_rel_update_resize])
  >- (* XDel *)
    (simp[xfml_rel_delete_ids_list]>>metis_tac[])
  >- ( (* CFromX *)
    rpt (pairarg_tac>>gvs[])>>
    drule_all tn_rel_ren_int_ls_list>>
    strip_tac>>gvs[]>>
    drule_all is_cfromx_list>>
    rw[]>>
    drule fml_rel_insert_vcc_list>>
    gvs[resize_dm_def]>>
    drule_all dm_rel_reset_dm_list>>
    metis_tac[])
  >- ( (* XFromC *)
    rpt (pairarg_tac>>gvs[conv_rawxor_list])>>
    drule_all tn_rel_ren_int_ls_list>>
    strip_tac>>gvs[]>>
    drule_all is_xfromc_list>>
    metis_tac[xfml_rel_update_resize])
  >- (* Delvb *)
    (simp[fml_rel_delete_ids_vb_list]>>metis_tac[])
  >- ( (* RUPvb *)
    drule_all is_rup_vb_list>>rw[]>>
    drule fml_rel_insert_vcc_list>>
    metis_tac[])
  >- ( (* XAddvb *)
    rpt (pairarg_tac>>gvs[conv_rawxor_list])>>
    drule_all tn_rel_ren_int_ls_list>>
    strip_tac>>gvs[]>>
    imp_res_tac tn_rel_nm_rel>>
    drule_all is_xor_vb_list>>
    strip_tac>>
    metis_tac[xfml_rel_update_resize])
  >- (* XDelvb *)
    (simp[xfml_rel_delete_ids_vb_list]>>metis_tac[])
  >- ( (* CFromXvb *)
    rpt (pairarg_tac>>gvs[])>>
    drule_all tn_rel_ren_int_ls_list>>
    strip_tac>>gvs[]>>
    drule_all is_cfromx_vb_list>>
    rw[]>>
    drule fml_rel_insert_vcc_list>>
    gvs[resize_dm_def]>>
    drule_all dm_rel_reset_dm_list>>
    metis_tac[])
  >- ( (* XFromCvb *)
    rpt (pairarg_tac>>gvs[conv_rawxor_list])>>
    drule_all tn_rel_ren_int_ls_list>>
    strip_tac>>gvs[]>>
    drule_all is_xfromc_vb_list>>
    metis_tac[xfml_rel_update_resize])
QED

Theorem check_xlrup_list_bnd_fml:
  bnd_fml cfmlls (LENGTH dml) ∧
  check_xlrup_list xm xlrup cfmlls xfmlls tnl def dml b =
    SOME (cfmlls', xfmlls', tnl', def', dml', b') ⇒
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
  >- metis_tac[bnd_fml_delete_ids_vb_list]
  >- (
    drule_all bnd_fml_is_rup_vb_list>>
    metis_tac[bnd_fml_insert_vcc_list])
  >- (pairarg_tac>>gvs[])
  >- (
    pairarg_tac>>gvs[]>>
    metis_tac[bnd_fml_insert_vcc_list_resize_dm])
  >- (pairarg_tac>>gvs[])
QED

Definition check_xlrups_list_def:
  (check_xlrups_list xm [] cfml xfml tnl def dml b =
    SOME (cfml, xfml, tnl, def)) ∧
  (check_xlrups_list xm (x::xs) cfml xfml tnl def dml b =
    case check_xlrup_list xm x cfml xfml tnl def dml b of
      NONE => NONE
    | SOME (cfml', xfml', tnl', def', dml', b') =>
      check_xlrups_list xm xs cfml' xfml' tnl' def' dml' b')
End

Theorem check_xlrups_list:
  ∀xlrups cfml cfmlls xfml xfmlls cfmlls' xfmlls'
    tn tnl tnl' def def' dml b dm.
  fml_rel cfml cfmlls ∧
  xfml_rel xfml xfmlls ∧
  dm_rel dm dml b ∧
  tn_rel tn tnl ∧
  FDOM xm = set xorig ∧
  check_xlrups_list xm xlrups cfmlls xfmlls tnl def dml b =
    SOME (cfmlls', xfmlls', tnl', def') ⇒
  ∃cfml' xfml' tn'.
    check_xlrups xorig xlrups cfml xfml tn def =
      SOME (cfml',xfml',tn',def') ∧
    fml_rel cfml' cfmlls' ∧
    xfml_rel xfml' xfmlls' ∧
    tn_rel tn' tnl'
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
  check_xlrups_unsat_list xm xlrups cfml xfml tnl def dml b =
  case check_xlrups_list xm xlrups cfml xfml tnl def dml b of
    NONE => F
  | SOME (cfml', xfml', tnl', def') =>
    contains_emp_list cfml'
End

Theorem check_xlrups_unsat_list:
  fml_rel cfml cfmlls ∧
  xfml_rel xfml xfmlls ∧
  dm_rel dm dml b ∧
  tn_rel tn tnl ∧
  FDOM xm = set xorig ∧
  check_xlrups_unsat_list xm xlrups cfmlls xfmlls tnl def dml b ⇒
  check_xlrups_unsat xorig xlrups cfml xfml tn def
Proof
  simp[check_xlrups_unsat_list_def,check_xlrups_unsat_def]>>
  strip_tac>>
  Cases_on`check_xlrups_list xm xlrups cfmlls xfmlls tnl def dml b`>>
  gvs[]>>
  rename1`SOME res`>>
  PairCases_on`res`>>gvs[]>>
  drule_all check_xlrups_list>>
  strip_tac>>gvs[]>>
  metis_tac[fml_rel_contains_emp_list]
QED

(* The list-level checker's guarantee, phrased on the parsed formula *)
Theorem check_xlrups_unsat_list_sound:
  FDOM xm = set xfml ∧
  check_xlrups_unsat_list xm xlrups
    (build_cfml_list kc (conv_cfml cfml) nc)
    (REPLICATE nx NONE)
    ([],1) def
    (REPLICATE n 0) 1 ∧
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
  simp[tn_rel_def,nm_rel_def,any_el_def,lookup_def]
QED
