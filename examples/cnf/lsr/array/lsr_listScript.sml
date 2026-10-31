(*
  This refines the LSR checker to a list-based implementation.
*)
Theory lsr_list
Ancestors
  cnf ccnf ccnf_list syntax_helper sr lsr mlstring mlvector
Libs
  preamble

(***
  RUP-level additions: propagation at a stamp chosen by the caller, and
  propagation that undoes its own writes
 ***)

(* The offset of the first non-positive token at or after i: the next
  group header, or the end of the hints *)
Definition skip_hints_vb_def:
  skip_hints_vb s i1 len =
  let (m,i) = parse_vb_int s i1 len in
  if m ≤ 0 then i1
  else skip_hints_vb s i len
Termination
  WF_REL_TAC `measure (λ(s,i,len). len - i)` >>
  rw[] >>
  drule_then strip_assume_tac parse_vb_int_i >>
  gvs[]
End

Theorem skip_hints_vb_le:
  ∀s i len. i ≤ len ⇒ i ≤ skip_hints_vb s i len ∧ skip_hints_vb s i len ≤ len
Proof
  ho_match_mp_tac skip_hints_vb_ind>>
  rpt gen_tac>>strip_tac>>
  once_rewrite_tac[skip_hints_vb_def]>>
  strip_tac>>
  Cases_on`parse_vb_int s i len`>>
  rename1`_ = (m,i')`>>
  simp[]>>
  rw[]>>
  `m = 0 ∨ i < len ∧ i < i'` by metis_tac[parse_vb_int_i]>>
  `i' ≤ len` by metis_tac[parse_vb_int_le]>>
  gvs[]
QED

(* Hints are positive, so they never match a group header *)
Theorem group_offset_skip_hints_vb:
  ∀s i len j.
  group_offset s (skip_hints_vb s i len) len j = group_offset s i len j
Proof
  ho_match_mp_tac skip_hints_vb_ind>>
  rpt gen_tac>>strip_tac>>
  simp[Once skip_hints_vb_def]>>
  pairarg_tac>>gvs[]>>
  rw[]>>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [group_offset_def]))>>
  `m ≠ 0 ∧ m ≠ -&j` by intLib.ARITH_TAC>>
  simp[]
QED

(* Without a conflict, propagation stops at the first non-positive token *)
Theorem unit_prop_vb_vec_SOME_SOME:
  ∀fml dm s i len j dm'.
  unit_prop_vb_vec fml dm s i len = SOME (SOME j,dm') ⇒
  j = skip_hints_vb s i len
Proof
  ho_match_mp_tac unit_prop_vb_vec_ind>>
  rpt gen_tac>>strip_tac>>
  simp[Once unit_prop_vb_vec_def,Once skip_hints_vb_def]>>
  pairarg_tac>>gvs[]>>
  rw[AllCaseEqs()]>>
  metis_tac[]
QED

(* Assume ¬C and propagate the global hints at stamp b, which the caller
  has made fresh. The map is neither reset nor resized here. *)
Definition rup_dm_vb_list_def:
  rup_dm_vb_list fmlls dml b C s =
  unit_prop_vb_list fmlls (init_lit_map_list (length C) C dml b) b s 0 (strlen s)
End

Theorem rup_dm_vb_list:
  fml_rel fml fmlls ∧
  dm_rel dm dml b ∧
  rup_dm_vb_list fmlls dml b C s = SOME (res,dml') ⇒
  ∃dm'.
    unit_prop_vb_vec fml (init_lit_map_vec (length C) C dm) s 0 (strlen s) =
      SOME (res,dm') ∧
    dm_rel dm' dml' b
Proof
  rw[rup_dm_vb_list_def]>>
  drule_then (qspecl_then [`length C`,`C`] assume_tac) init_lit_map_list>>
  drule_all unit_prop_vb_list>>
  simp[]
QED

Theorem LENGTH_init_lit_map_list_bnd:
  ∀i v dml b.
  bnd_clause v (LENGTH dml) ∧ i ≤ length v ⇒
  LENGTH (init_lit_map_list i v dml b) = LENGTH dml
Proof
  ho_match_mp_tac init_lit_map_list_ind>>
  rpt gen_tac>>strip_tac>>strip_tac>>
  simp[Once init_lit_map_list_def]>>
  Cases_on`i = 0`>>simp[]>>
  `Num (ABS (sub v (i − 1))) < LENGTH dml` by gvs[bnd_clause_def]>>
  Cases_on`sub v (i − 1) > 0`>>gvs[]
  >- (
    `Num (sub v (i − 1)) < LENGTH dml` by intLib.ARITH_TAC>>
    gvs[update_resize_LUPDATE])>>
  `Num (-sub v (i − 1)) < LENGTH dml` by intLib.ARITH_TAC>>
  gvs[update_resize_LUPDATE]
QED

Theorem unit_prop_vb_list_LENGTH:
  bnd_fml fmlls (LENGTH dml) ∧
  unit_prop_vb_list fmlls dml b s i len = SOME (res,dml') ⇒
  LENGTH dml' = LENGTH dml
Proof
  strip_tac>>
  `IS_SOME (unit_prop_vb_list' fmlls dml b s i len)`
    by simp[unit_prop_vb_list'_SOME]>>
  gvs[IS_SOME_EXISTS]>>
  drule unit_prop_vb_list'>>
  strip_tac>>gvs[]>>
  drule unit_prop_vb_list'_LENGTH>>
  simp[]
QED

Theorem rup_dm_vb_list_LENGTH:
  bnd_clause C (LENGTH dml) ∧
  bnd_fml fmlls (LENGTH dml) ∧
  rup_dm_vb_list fmlls dml b C s = SOME (res,dml') ⇒
  LENGTH dml' = LENGTH dml
Proof
  rw[rup_dm_vb_list_def]>>
  `LENGTH (init_lit_map_list (length C) C dml b) = LENGTH dml`
    by simp[LENGTH_init_lit_map_list_bnd]>>
  drule_at (Pos last) unit_prop_vb_list_LENGTH>>
  simp[]
QED

Theorem stamps_ok_rup_dm_vb_list:
  stamps_ok dml b ∧
  rup_dm_vb_list fmlls dml b C s = SOME (res,dml') ⇒
  stamps_ok dml' b
Proof
  rw[rup_dm_vb_list_def]>>
  metis_tac[stamps_ok_init_lit_map_list,stamps_ok_unit_prop_vb_list]
QED

(* Propagate the hints from offset i1 up to the next non-positive token,
  then reset every variable this propagation wrote. The result is 0 if
  the hints did not conflict, and otherwise the offset just after the
  hint that conflicted. *)
Definition unit_prop_vb_undo_list_def:
  unit_prop_vb_undo_list fmlls dml b s i1 len =
  let (m,i) = parse_vb_int s i1 len in
  if m ≤ 0 then SOME (0n,dml)
  else
  case unit_prop_one fmlls dml b (Num m) of
    NONE => NONE
  | SOME (r,dml') =>
    if r = 0 then SOME (i,dml')
    else if 0 < r then
      (case unit_prop_vb_undo_list fmlls dml' b s i len of
        NONE => NONE
      | SOME (j,dml'') => SOME (j, LUPDATE 0 (Num r) dml''))
    else unit_prop_vb_undo_list fmlls dml' b s i len
Termination
  WF_REL_TAC `measure (λ(fmlls,dml,b,s,i,len). len - i)` >>
  rw[] >>
  drule_then strip_assume_tac parse_vb_int_i >>
  gvs[]
End

(* Clearing a variable that the map did not assign restores the map *)
Theorem dm_rel_LUPDATE_0:
  dm_rel (dm |+ (n,x)) dml b ∧
  FLOOKUP dm n = NONE ⇒
  dm_rel dm (LUPDATE 0 n dml) b
Proof
  PURE_REWRITE_TAC[dm_rel_def]>>
  strip_tac>>
  conj_tac
  >- first_assum ACCEPT_TAC>>
  gen_tac>>
  qpat_x_assum`∀m. _`(qspec_then`n'` mp_tac)>>
  Cases_on`n' = n`>>
  simp[FLOOKUP_UPDATE,any_el_ALT,EL_LUPDATE]
QED

(* On a clause without the literal 0, a step that writes returns a
  positive variable, so a conflict (r = 0) never writes *)
Theorem delete_literals_sing_assigns_nz:
  ∀ls dm r dm'.
  delete_literals_sing dm ls = SOME (r,dm') ∧ ¬MEM 0 ls ⇒
  (r ≤ 0 ∧ dm' = dm) ∨
  ∃n b. 0 < n ∧ r = &n ∧ FLOOKUP dm n = NONE ∧ dm' = dm |+ (n,b)
Proof
  Induct
  >- simp[delete_literals_sing_def]>>
  rpt strip_tac>>
  gvs[delete_literals_sing_def,AllCaseEqs()]
  >- (
    DISJ2_TAC>>
    qexistsl_tac[`Num (-h)`,`T`]>>
    simp[]>>
    intLib.ARITH_TAC)
  >- (
    DISJ2_TAC>>
    qexistsl_tac[`Num h`,`F`]>>
    simp[]>>
    intLib.ARITH_TAC)>>
  DISJ1_TAC>>
  intLib.ARITH_TAC
QED

(* The core's unit step on hint i, read through the formula: it either
  writes nothing, or assigns the variable it returns, which was
  unassigned *)
Theorem unit_prop_one_step:
  fml_rel fml fmlls ∧
  nz_vcfml (FRANGE fml) ∧
  dm_rel dm dml b ∧
  unit_prop_one fmlls dml b i = SOME (r,dml') ⇒
  ∃c dm'.
    FLOOKUP fml i = SOME c ∧
    delete_literals_sing_vec dm c (length c) = SOME (r,dm') ∧
    dm_rel dm' dml' b ∧
    ((r ≤ 0 ∧ dm' = dm) ∨
     ∃n bb. 0 < n ∧ r = &n ∧ FLOOKUP dm n = NONE ∧ dm' = dm |+ (n,bb))
Proof
  rw[unit_prop_one_def]>>
  drule_all delete_literals_sing_list>>
  strip_tac>>
  `FLOOKUP fml i = SOME (any_el i fmlls vcc_none)`
    by metis_tac[fml_rel_any_el_NEQ_vcc_none_FLOOKUP]>>
  qmatch_asmsub_abbrev_tac`delete_literals_sing_vec dm c _`>>
  `∃ds. c = Vector ds` by (Cases_on`c`>>simp[])>>
  gvs[length_def,delete_literals_sing_vec]>>
  `¬MEM 0 (REVERSE ds)` by (
    gvs[nz_vcfml_def,FRANGE_FLOOKUP,PULL_EXISTS]>>
    first_x_assum drule>>
    simp[toList_thm])>>
  drule_all delete_literals_sing_assigns_nz>>
  rw[]>>
  simp[]
QED

Theorem unit_prop_vb_undo_list:
  ∀fmlls dml b s i len dm j dml'.
  fml_rel fml fmlls ∧
  nz_vcfml (FRANGE fml) ∧
  dm_rel dm dml b ∧
  unit_prop_vb_undo_list fmlls dml b s i len = SOME (j,dml') ⇒
  dm_rel dm dml' b ∧
  ∃res dm'.
    unit_prop_vb_vec fml dm s i len = SOME (res,dm') ∧
    (res = NONE ⇔ j ≠ 0)
Proof
  ho_match_mp_tac unit_prop_vb_undo_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`unit_prop_vb_undo_list _ _ _ _ _ _ = _` mp_tac>>
  simp[Once unit_prop_vb_undo_list_def,Once unit_prop_vb_vec_def]>>
  pairarg_tac>>gvs[]>>
  IF_CASES_TAC>>gvs[]>>
  strip_tac>>
  gvs[AllCaseEqs()]
  >- (
    (* conflict: nothing written *)
    drule_all unit_prop_one_step>>
    strip_tac>>gvs[]>>
    `m = 0 ∨ i < len ∧ i < i'` by metis_tac[parse_vb_int_i]>>
    gvs[])
  >- (
    (* r assigned: the rest runs on the map with r, then r is cleared *)
    drule_all unit_prop_one_step>>
    strip_tac>>
    `¬(r ≤ 0)` by simp[integerTheory.INT_NOT_LE]>>
    gvs[]>>
    first_x_assum drule>>
    strip_tac>>
    simp[]>>
    irule dm_rel_LUPDATE_0>>
    metis_tac[])>>
  (* r already true: nothing written *)
  drule_all unit_prop_one_step>>
  strip_tac>>gvs[]
QED

Theorem stamps_ok_LUPDATE_0:
  stamps_ok dml b ⇒ stamps_ok (LUPDATE 0 n dml) b
Proof
  rw[stamps_ok_def]>>
  irule IMP_EVERY_LUPDATE>>
  simp[]
QED

Theorem stamps_ok_unit_prop_vb_undo_list:
  ∀fmlls dml b s i len j dml'.
  stamps_ok dml b ∧
  unit_prop_vb_undo_list fmlls dml b s i len = SOME (j,dml') ⇒
  stamps_ok dml' b
Proof
  ho_match_mp_tac unit_prop_vb_undo_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`unit_prop_vb_undo_list _ _ _ _ _ _ = _` mp_tac>>
  simp[Once unit_prop_vb_undo_list_def]>>
  pairarg_tac>>gvs[]>>
  rw[AllCaseEqs()]>>
  metis_tac[stamps_ok_unit_prop_one,stamps_ok_LUPDATE_0]
QED

Theorem unit_prop_one_LENGTH:
  bnd_fml fmlls (LENGTH dml) ∧
  unit_prop_one fmlls dml b i = SOME (r,dml') ⇒
  LENGTH dml' = LENGTH dml
Proof
  strip_tac>>
  `IS_SOME (unit_prop_one' fmlls dml b i)` by simp[unit_prop_one'_SOME]>>
  gvs[IS_SOME_EXISTS]>>
  drule unit_prop_one'>>
  strip_tac>>gvs[]>>
  drule unit_prop_one'_LENGTH>>
  simp[]
QED

Theorem unit_prop_vb_undo_list_LENGTH:
  ∀fmlls dml b s i len j dml'.
  bnd_fml fmlls (LENGTH dml) ∧
  unit_prop_vb_undo_list fmlls dml b s i len = SOME (j,dml') ⇒
  LENGTH dml' = LENGTH dml
Proof
  ho_match_mp_tac unit_prop_vb_undo_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`unit_prop_vb_undo_list _ _ _ _ _ _ = _` mp_tac>>
  simp[Once unit_prop_vb_undo_list_def]>>
  pairarg_tac>>gvs[]>>
  rw[AllCaseEqs()]>>
  drule_all unit_prop_one_LENGTH>>
  strip_tac>>
  gvs[]
QED

(* The step returns 0, or a literal of the clause, or its negation *)
Theorem delete_literals_sing_list_bound:
  ∀dml b v i r dml'.
  delete_literals_sing_list dml b v i = SOME (r,dml') ∧
  i ≤ length v ∧ bnd_clause v sz ∧ r ≠ 0 ⇒
  Num (ABS r) < sz
Proof
  ho_match_mp_tac delete_literals_sing_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  simp[Once delete_literals_sing_list_def]>>
  rw[]>>
  gvs[bnd_clause_def]
QED

Theorem unit_prop_one_bound:
  bnd_fml fmlls (LENGTH dml) ∧
  unit_prop_one fmlls dml b i = SOME (r,dml') ∧ r ≠ 0 ⇒
  Num (ABS r) < LENGTH dml
Proof
  rw[unit_prop_one_def]>>
  irule delete_literals_sing_list_bound>>
  gvs[bnd_fml_def]>>
  metis_tac[LESS_EQ_REFL]
QED

(* The size the arrays need for the witness w, at least m: above every
  variable it maps and every literal it maps to *)
Definition sz_witness_def:
  (sz_witness [] m = m:num) ∧
  (sz_witness ((v,x:bool + int)::w) m =
    let m = (if v < m then m else v + 1) in
    let m = (case x of
               INR l => if Num (ABS l) < m then m else Num (ABS l) + 1
             | INL _ => m) in
    sz_witness w m)
End

Theorem sz_witness_mono:
  ∀w m. m ≤ sz_witness w m
Proof
  Induct>>
  simp[sz_witness_def,FORALL_PROD]>>
  rpt gen_tac>>
  qmatch_goalsub_abbrev_tac`sz_witness w mm`>>
  `m ≤ mm` by (unabbrev_all_tac>>every_case_tac>>rw[])>>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem sz_witness_bnd:
  ∀w m.
  EVERY (λ(v,x). v < sz_witness w m ∧
    ∀l. x = INR l ⇒ Num (ABS l) < sz_witness w m) w
Proof
  Induct>>simp[]>>
  Cases>>rename1`(v,x)`>>
  gen_tac>>Cases_on`x`>>simp[sz_witness_def]>>
  qmatch_goalsub_abbrev_tac`sz_witness w mm`>>
  `mm ≤ sz_witness w mm` by simp[sz_witness_mono]
  >- (
    `v < mm` by (unabbrev_all_tac>>rw[])>>
    simp[])>>
  rename1`Num (ABS l)`>>
  `v < mm ∧ Num (ABS l) < mm` by (unabbrev_all_tac>>rw[])>>
  simp[]
QED

(***
  Literal occurrence counts with a watermark wm: cnt holds, for each
  literal, its number of occurrences in the live clauses with id below wm
 ***)

(* The index of literal l in the count arrays *)
Definition lit_code_def:
  lit_code (l:int) = 2 * Num (ABS l) + (if l < 0 then 1 else 0)
End

Theorem lit_code_11:
  lit_code l = lit_code l' ⇔ l = l'
Proof
  rw[lit_code_def]>>
  intLib.ARITH_TAC
QED

Theorem lit_code_bound:
  Num (ABS l) < n ⇒ lit_code l < 2 * n
Proof
  rw[lit_code_def]
QED

(* The occurrences of l in the clause c *)
Definition occ_def:
  occ (l:int) c = LENGTH (FILTER ($= l) (toList c))
End

(* A deleted slot holds vcc_none, in which no literal but 0 occurs *)
Theorem occ_vcc_none:
  l ≠ 0 ⇒ occ l vcc_none = 0
Proof
  rw[occ_def,vcc_none_def,toList_thm]
QED

Definition lit_count_def:
  lit_count fmlls wm l = SUM (MAP (occ l) (TAKE wm fmlls))
End

Definition count_rel_def:
  count_rel fmlls cnt wm ⇔
  wm ≤ LENGTH fmlls ∧
  ∀l. l ≠ 0 ∧ lit_code l < LENGTH cnt ⇒
    EL (lit_code l) cnt = lit_count fmlls wm l
End

(* Add (or subtract) one for every literal of c read from index i down *)
Definition add_counts_def:
  add_counts c i (cnt:num list) =
  if i = 0 then cnt
  else
    let k = lit_code (sub c (i - 1)) in
    add_counts c (i - 1) (LUPDATE (EL k cnt + 1) k cnt)
End

Definition sub_counts_def:
  sub_counts c i (cnt:num list) =
  if i = 0 then cnt
  else
    let k = lit_code (sub c (i - 1)) in
    sub_counts c (i - 1) (LUPDATE (EL k cnt - 1) k cnt)
End

(* Reading a clause from index 0 up to i, one literal at a time *)
Theorem TAKE_SUC_toList:
  i < length c ⇒
  TAKE (SUC i) (toList c) = TAKE i (toList c) ++ [sub c i]
Proof
  Cases_on`c`>>
  rw[toList_thm,sub_def,length_def,ADD1,TAKE_EL_SNOC,SNOC_APPEND]
QED

(* Every literal of the clause has its count in range *)
Definition codes_in_def:
  codes_in c (n:num) ⇔ ∀j. j < length c ⇒ lit_code (sub c j) < n
End

Theorem add_counts_LENGTH[simp]:
  ∀c i cnt. LENGTH (add_counts c i cnt) = LENGTH cnt
Proof
  ho_match_mp_tac add_counts_ind>>
  rw[]>>
  once_rewrite_tac[add_counts_def]>>
  rw[]
QED

Theorem sub_counts_LENGTH[simp]:
  ∀c i cnt. LENGTH (sub_counts c i cnt) = LENGTH cnt
Proof
  ho_match_mp_tac sub_counts_ind>>
  rw[]>>
  once_rewrite_tac[sub_counts_def]>>
  rw[]
QED

Theorem add_counts:
  ∀i cnt.
  codes_in c (LENGTH cnt) ∧ i ≤ length c ∧ l ≠ 0 ∧ lit_code l < LENGTH cnt ⇒
  EL (lit_code l) (add_counts c i cnt) =
    EL (lit_code l) cnt + LENGTH (FILTER ($= l) (TAKE i (toList c)))
Proof
  Induct
  >- (once_rewrite_tac[add_counts_def]>>simp[])>>
  rpt strip_tac>>
  once_rewrite_tac[add_counts_def]>>
  simp[]>>
  `lit_code (sub c i) < LENGTH cnt` by gvs[codes_in_def]>>
  simp[TAKE_SUC_toList,EL_LUPDATE,FILTER_APPEND,lit_code_11]>>
  rw[]
QED

Theorem sub_counts:
  ∀i cnt.
  codes_in c (LENGTH cnt) ∧ i ≤ length c ∧ l ≠ 0 ∧ lit_code l < LENGTH cnt ∧
  LENGTH (FILTER ($= l) (TAKE i (toList c))) ≤ EL (lit_code l) cnt ⇒
  EL (lit_code l) (sub_counts c i cnt) =
    EL (lit_code l) cnt - LENGTH (FILTER ($= l) (TAKE i (toList c)))
Proof
  Induct
  >- (once_rewrite_tac[sub_counts_def]>>simp[])>>
  rpt gen_tac>>strip_tac>>
  once_rewrite_tac[sub_counts_def]>>
  `lit_code (sub c i) < LENGTH cnt` by gvs[codes_in_def]>>
  gvs[TAKE_SUC_toList,FILTER_APPEND]>>
  qmatch_goalsub_abbrev_tac`sub_counts c i cnt1`>>
  `LENGTH cnt1 = LENGTH cnt` by simp[Abbr`cnt1`]>>
  first_x_assum (qspec_then`cnt1` mp_tac)>>
  simp[Abbr`cnt1`,EL_LUPDATE,lit_code_11]>>
  rw[]>>gvs[]
QED

(* Count every live clause from id j up to lim *)
Definition catch_up_def:
  catch_up fmlls j lim cnt =
  if j < lim then
    let c = any_el j fmlls vcc_none in
    catch_up fmlls (j + 1) lim
      (if c = vcc_none then cnt else add_counts c (length c) cnt)
  else cnt
Termination
  WF_REL_TAC `measure (λ(fmlls,j,lim,cnt). lim - j)`
End

(* No clause is live from id tp on: tp is one more than the highest id
  inserted so far *)
Definition top_ok_def:
  top_ok fmlls tp ⇔ ∀k. tp ≤ k ∧ k < LENGTH fmlls ⇒ EL k fmlls = vcc_none
End

(* Every live clause has its literal counts in range *)
Definition codes_fml_def:
  codes_fml fmlls n ⇔
  ∀j. j < LENGTH fmlls ∧ EL j fmlls ≠ vcc_none ⇒ codes_in (EL j fmlls) n
End

Theorem lit_count_SUC:
  j < LENGTH fmlls ⇒
  lit_count fmlls (j + 1) l = lit_count fmlls j l + occ l (EL j fmlls)
Proof
  rw[lit_count_def,TAKE_EL_SNOC,MAP_SNOC,SUM_SNOC]
QED

Theorem FILTER_TAKE_length:
  LENGTH (FILTER ($= l) (TAKE (length c) (toList c))) = occ l c
Proof
  Cases_on`c`>>simp[occ_def,toList_thm,length_def]
QED

(* Counting a whole clause adds its occurrences *)
Theorem add_counts_occ:
  codes_in c (LENGTH cnt) ∧ l ≠ 0 ∧ lit_code l < LENGTH cnt ⇒
  EL (lit_code l) (add_counts c (length c) cnt) =
  EL (lit_code l) cnt + occ l c
Proof
  metis_tac[add_counts,FILTER_TAKE_length,LESS_EQ_REFL]
QED

Theorem sub_counts_occ:
  codes_in c (LENGTH cnt) ∧ l ≠ 0 ∧ lit_code l < LENGTH cnt ∧
  occ l c ≤ EL (lit_code l) cnt ⇒
  EL (lit_code l) (sub_counts c (length c) cnt) =
  EL (lit_code l) cnt - occ l c
Proof
  metis_tac[sub_counts,FILTER_TAKE_length,LESS_EQ_REFL]
QED

(* One step of the catch-up counts the clause at the watermark *)
Theorem count_rel_catch_up_step:
  count_rel fmlls cnt wm ∧ wm < LENGTH fmlls ∧ codes_fml fmlls (LENGTH cnt) ⇒
  count_rel fmlls
    (if EL wm fmlls = vcc_none then cnt
     else add_counts (EL wm fmlls) (length (EL wm fmlls)) cnt) (wm + 1) ∧
  LENGTH (if EL wm fmlls = vcc_none then cnt
          else add_counts (EL wm fmlls) (length (EL wm fmlls)) cnt) =
  LENGTH cnt
Proof
  rw[]
  >- gvs[count_rel_def,lit_count_SUC,occ_vcc_none]>>
  `codes_in (EL wm fmlls) (LENGTH cnt)` by gvs[codes_fml_def]>>
  gvs[count_rel_def,lit_count_SUC,add_counts_occ]
QED

Theorem count_rel_catch_up:
  ∀fmlls wm lim cnt.
  count_rel fmlls cnt wm ∧ wm ≤ lim ∧ lim ≤ LENGTH fmlls ∧
  codes_fml fmlls (LENGTH cnt) ⇒
  count_rel fmlls (catch_up fmlls wm lim cnt) lim ∧
  LENGTH (catch_up fmlls wm lim cnt) = LENGTH cnt
Proof
  ho_match_mp_tac catch_up_ind>>
  rpt gen_tac>>strip_tac>>strip_tac>>
  once_rewrite_tac[catch_up_def]>>
  reverse IF_CASES_TAC
  >- (
    `wm = lim` by gvs[]>>
    gvs[])>>
  `wm < LENGTH fmlls` by gvs[]>>
  `any_el wm fmlls vcc_none = EL wm fmlls` by simp[any_el_ALT]>>
  pop_assum SUBST_ALL_TAC>>
  simp[]>>
  drule_all count_rel_catch_up_step>>
  strip_tac>>
  gvs[]
QED

(* No literal occurs in the slots from lim on *)
Theorem SUM_occ_DROP_top:
  top_ok fmlls tp ∧ (tp ≤ lim ∨ LENGTH fmlls ≤ lim) ∧ l ≠ 0 ⇒
  SUM (MAP (occ l) (DROP lim fmlls)) = 0
Proof
  rw[SUM_eq_0,MEM_MAP,MEM_EL]>>
  gvs[EL_DROP,top_ok_def]>>
  `EL (n + lim) fmlls = vcc_none` by (
    first_x_assum irule>>
    simp[])>>
  simp[occ_vcc_none]
QED

(* Counts exact up to tp are exact for the whole formula *)
Theorem count_rel_top:
  count_rel fmlls cnt lim ∧ top_ok fmlls tp ∧ MIN tp (LENGTH fmlls) ≤ lim ⇒
  count_rel fmlls cnt (LENGTH fmlls)
Proof
  simp[count_rel_def,lit_count_def]>>
  rpt strip_tac>>
  first_x_assum drule_all>>
  disch_then SUBST1_TAC>>
  `SUM (MAP (occ l) fmlls) =
   SUM (MAP (occ l) (TAKE lim fmlls ++ DROP lim fmlls))`
    by REWRITE_TAC[TAKE_DROP]>>
  pop_assum SUBST1_TAC>>
  simp[SUM_APPEND]>>
  irule SUM_occ_DROP_top>>
  metis_tac[]
QED

Theorem top_ok_insert_vcc_list:
  top_ok fmlls tp ⇒ top_ok (insert_vcc_list fmlls n c) (MAX tp (n + 1))
Proof
  rw[top_ok_def,insert_vcc_list_def,update_resize_def]>>
  gvs[EL_LUPDATE,EL_APPEND_EQN,EL_REPLICATE]
QED

Theorem top_ok_delete_list:
  top_ok fmlls tp ⇒ top_ok (delete_list vcc_none fmlls k) tp
Proof
  rw[top_ok_def,delete_list_def,EL_LUPDATE]>>
  rw[]
QED

Theorem top_ok_delete_ids_vb_list:
  ∀d fmlls s i len.
  top_ok fmlls tp ∧ d = vcc_none ⇒
  top_ok (delete_ids_vb_list d fmlls s i len) tp
Proof
  ho_match_mp_tac delete_ids_vb_list_ind>>
  rw[]>>
  Cases_on`parse_vb_int s i len`>>
  rename1`parse_vb_int s i len = (m,i')`>>
  simp[Once delete_ids_vb_list_def]>>
  rw[]>>
  first_x_assum irule>>
  simp[top_ok_delete_list]
QED

(* Insertion of a clause at a free id: counted at once below the watermark *)
Definition insert_cnt_list_def:
  insert_cnt_list fmlls cnt wm n c =
  (insert_vcc_list fmlls n c,
   if n < wm then add_counts c (length c) cnt else cnt)
End

Theorem SUM_MAP_LUPDATE:
  ∀ls n.
  n < LENGTH ls ⇒
  SUM (MAP f (LUPDATE x n ls)) + f (EL n ls) = SUM (MAP f ls) + f x
Proof
  Induct>>
  rw[]>>
  Cases_on`n`>>gvs[LUPDATE_def]
QED

(* The clauses below the watermark after an update at n *)
Theorem TAKE_update_resize:
  wm ≤ LENGTH ls ⇒
  TAKE wm (update_resize ls d x n) =
  if n < wm then LUPDATE x n (TAKE wm ls) else TAKE wm ls
Proof
  rw[update_resize_def,LIST_EQ_REWRITE]>>
  gvs[EL_TAKE,EL_LUPDATE,EL_APPEND_EQN]
QED

Theorem TAKE_LUPDATE:
  TAKE wm (LUPDATE x k ls) =
  if k < wm then LUPDATE x k (TAKE wm ls) else TAKE wm ls
Proof
  rw[LIST_EQ_REWRITE,LENGTH_TAKE_EQ]>>
  gvs[LENGTH_TAKE_EQ,EL_TAKE,EL_LUPDATE]>>
  rw[]
QED

Theorem count_rel_insert_cnt_list:
  count_rel fmlls cnt wm ∧
  any_el n fmlls vcc_none = vcc_none ∧
  codes_in c (LENGTH cnt) ∧
  insert_cnt_list fmlls cnt wm n c = (fmlls',cnt') ⇒
  count_rel fmlls' cnt' wm ∧ LENGTH cnt' = LENGTH cnt
Proof
  rw[insert_cnt_list_def,insert_vcc_list_def]>>
  `LENGTH fmlls ≤ LENGTH (update_resize fmlls vcc_none c n)`
    by rw[update_resize_def]>>
  gvs[count_rel_def,lit_count_def,TAKE_update_resize]>>
  rw[]>>
  `n < LENGTH fmlls ∧ EL n fmlls = vcc_none` by gvs[any_el_ALT]>>
  `SUM (MAP (occ l) (LUPDATE c n (TAKE wm fmlls))) +
     occ l (EL n (TAKE wm fmlls)) =
   SUM (MAP (occ l) (TAKE wm fmlls)) + occ l c`
    by (irule SUM_MAP_LUPDATE>>simp[])>>
  gvs[EL_TAKE,occ_vcc_none,add_counts_occ]
QED

(* Deletion of id k: uncounted below the watermark if it was live *)
Definition delete_cnt_list_def:
  delete_cnt_list fmlls cnt wm k =
  (delete_list vcc_none fmlls k,
   if k < wm then
     (let c = EL k fmlls in
      if c = vcc_none then cnt else sub_counts c (length c) cnt)
   else cnt)
End

Definition delete_ids_cnt_list_def:
  delete_ids_cnt_list fmlls cnt wm s i len =
  let (m,i) = parse_vb_int s i len in
  if m ≤ 0 then (fmlls,cnt)
  else
    let (fmlls',cnt') = delete_cnt_list fmlls cnt wm (Num m) in
    delete_ids_cnt_list fmlls' cnt' wm s i len
Termination
  WF_REL_TAC `measure (λ(fmlls,cnt,wm,s,i,len). len - i)` >>
  rw[] >>
  drule_then strip_assume_tac parse_vb_int_i >>
  gvs[]
End

Theorem delete_ids_cnt_list_fml:
  ∀fmlls cnt wm s i len.
  FST (delete_ids_cnt_list fmlls cnt wm s i len) =
  delete_ids_vb_list vcc_none fmlls s i len
Proof
  ho_match_mp_tac delete_ids_cnt_list_ind>>
  rw[]>>
  once_rewrite_tac[delete_ids_cnt_list_def,delete_ids_vb_list_def]>>
  Cases_on`parse_vb_int s i len`>>
  rename1`parse_vb_int s i len = (m,i')`>>
  simp[]>>
  rw[]>>
  Cases_on`delete_cnt_list fmlls cnt wm (Num m)`>>
  gvs[delete_cnt_list_def]
QED

Theorem codes_fml_delete_list:
  codes_fml fmlls n ⇒ codes_fml (delete_list vcc_none fmlls k) n
Proof
  rw[codes_fml_def,delete_list_def]>>
  Cases_on`j = k`>>gvs[EL_LUPDATE]
QED

Theorem count_rel_delete_cnt_list:
  count_rel fmlls cnt wm ∧ codes_fml fmlls (LENGTH cnt) ∧
  delete_cnt_list fmlls cnt wm k = (fmlls',cnt') ⇒
  count_rel fmlls' cnt' wm ∧ codes_fml fmlls' (LENGTH cnt) ∧
  LENGTH cnt' = LENGTH cnt
Proof
  strip_tac>>
  gvs[delete_cnt_list_def]>>
  `codes_fml (delete_list vcc_none fmlls k) (LENGTH cnt)`
    by simp[codes_fml_delete_list]>>
  reverse (Cases_on`k < wm`)>>gvs[]
  >- (
    (* above the watermark: the counted clauses are unchanged *)
    gvs[count_rel_def,lit_count_def,delete_list_def]>>
    rw[TAKE_LUPDATE])>>
  `k < LENGTH fmlls` by gvs[count_rel_def]>>
  Cases_on`EL k fmlls = vcc_none`>>gvs[]
  >- (
    (* a dead slot: deleting it changes nothing *)
    `delete_list vcc_none fmlls k = fmlls` by
      (rw[delete_list_def]>>metis_tac[LUPDATE_SAME])>>
    gvs[])>>
  (* a live clause below the watermark: its occurrences are subtracted *)
  `codes_in (EL k fmlls) (LENGTH cnt)` by gvs[codes_fml_def]>>
  gvs[count_rel_def,lit_count_def,delete_list_def,TAKE_LUPDATE]>>
  rw[]>>
  `SUM (MAP (occ l) (LUPDATE vcc_none k (TAKE wm fmlls))) +
     occ l (EL k (TAKE wm fmlls)) =
   SUM (MAP (occ l) (TAKE wm fmlls)) + occ l vcc_none`
    by (irule SUM_MAP_LUPDATE>>simp[])>>
  gvs[EL_TAKE,occ_vcc_none]>>
  DEP_REWRITE_TAC[sub_counts_occ]>>
  simp[]
QED

Theorem count_rel_delete_ids_cnt_list:
  ∀fmlls cnt wm s i len fmlls' cnt'.
  count_rel fmlls cnt wm ∧ codes_fml fmlls (LENGTH cnt) ∧
  delete_ids_cnt_list fmlls cnt wm s i len = (fmlls',cnt') ⇒
  count_rel fmlls' cnt' wm ∧ codes_fml fmlls' (LENGTH cnt) ∧
  LENGTH cnt' = LENGTH cnt
Proof
  ho_match_mp_tac delete_ids_cnt_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  once_rewrite_tac[delete_ids_cnt_list_def]>>
  Cases_on`parse_vb_int s i len`>>
  rename1`parse_vb_int s i len = (m,i')`>>
  simp[]>>
  Cases_on`delete_cnt_list fmlls cnt wm (Num m)`>>
  rename1`delete_cnt_list _ _ _ _ = (fmlls1,cnt1)`>>
  strip_tac>>
  Cases_on`m ≤ 0`>>gvs[]>>
  drule_all count_rel_delete_cnt_list>>
  strip_tac>>
  qpat_x_assum`_ ⇒ _` mp_tac>>
  simp[]
QED

(***
  The substitution array: for a variable v below its length kk, sarr
  holds 0 if σ leaves v alone, and otherwise the image of v: a literal, or
  kk for ⊤ and -kk for ⊥, so that negating the entry gives the image of ¬v
 ***)

Definition enc_img_def:
  (enc_img (kk:num) (INL b) = if b then (&kk:int) else -&kk) ∧
  (enc_img kk (INR m) = m)
End

Definition fill_subst_def:
  (fill_subst kk [] (sarr:int list) = sarr) ∧
  (fill_subst kk ((v,x)::w) sarr =
    fill_subst kk w (LUPDATE (enc_img kk x) v sarr))
End

Definition clear_subst_def:
  (clear_subst [] (sarr:int list) = sarr) ∧
  (clear_subst ((v,x:bool + int)::w) sarr = clear_subst w (LUPDATE 0 v sarr))
End

(* The image code of l: 0 when σ leaves l alone, and plus or minus the
  length of sarr for ⊤ and ⊥.
  On a RAT line (rat) σ maps the pivot p to ⊤ and nothing else, and sarr is
  not read. *)
Definition img_code_def:
  img_code rat (p:int) (sarr:int list) (l:int) =
  if rat then
    (if l = p then &LENGTH sarr else if l = -p then -&LENGTH sarr else 0)
  else
    let x = any_el (Num (ABS l)) sarr 0 in
    if l < 0 then -x else x
End

Definition dec_img_def:
  dec_img (kk:num) (y:int) (l:int) : bool + int =
  if y = 0 then INR l
  else if y = &kk then INL T
  else if y = -&kk then INL F
  else INR y
End

Definition sarr_rel_def:
  sarr_rel σ rat p sarr ⇔
  ∀l. sub_lit σ l = dec_img (LENGTH sarr) (img_code rat p sarr l) l
End

Theorem LENGTH_fill_subst[simp]:
  ∀w sarr. LENGTH (fill_subst kk w sarr) = LENGTH sarr
Proof
  Induct>>simp[fill_subst_def,FORALL_PROD]
QED

Theorem LENGTH_clear_subst[simp]:
  ∀w sarr. LENGTH (clear_subst w sarr) = LENGTH sarr
Proof
  Induct>>simp[clear_subst_def,FORALL_PROD]
QED

Theorem any_el_fill_subst:
  ∀w sarr.
  EVERY (λ(v,x). v < LENGTH sarr) w ⇒
  any_el u (fill_subst kk w sarr) 0 =
  case ALOOKUP (REVERSE w) u of
    NONE => any_el u sarr 0
  | SOME x => enc_img kk x
Proof
  Induct>>
  simp[fill_subst_def,FORALL_PROD]>>
  rw[ALOOKUP_APPEND]>>
  TOP_CASE_TAC>>
  rw[any_el_ALT,EL_LUPDATE]
QED

Theorem any_el_clear_subst:
  ∀w sarr.
  any_el u (clear_subst w sarr) 0 =
  if MEM u (MAP FST w) then 0 else any_el u sarr 0
Proof
  Induct>>
  simp[clear_subst_def,FORALL_PROD]>>
  rw[any_el_ALT,EL_LUPDATE]>>
  gvs[]
QED

(* The witness's variables and images are below the arrays' length *)
Definition w_bnd_def:
  w_bnd w n ⇔
  EVERY (λ(v,x). v < n ∧ ∀m. x = INR m ⇒ Num (ABS m) < n) w
End

Theorem w_bnd_vars:
  w_bnd w n ⇒ EVERY (λ(v,x). v < n) w
Proof
  strip_tac>>
  irule EVERY_MONOTONIC>>
  qexists_tac`λ(v,x). v < n ∧ ∀m. x = INR m ⇒ Num (ABS m) < n`>>
  gvs[w_bnd_def,FORALL_PROD]
QED

Theorem EVERY_0_any_el:
  EVERY ($= 0) ls ⇔ ∀u. any_el u ls 0 = 0
Proof
  rw[EVERY_EL,any_el_ALT,EQ_IMP_THM]>>
  rw[]>>
  first_x_assum (qspec_then`n` mp_tac)>>
  simp[]
QED

Theorem sarr_rel_fill_subst:
  EVERY ($= 0) sarr ∧ EVERY wf_entry w ∧ w_bnd w (LENGTH sarr) ⇒
  sarr_rel (mk_subst w) F p (fill_subst (LENGTH sarr) w sarr)
Proof
  rw[sarr_rel_def,img_code_def,mk_subst_def,sub_lit_def,FLOOKUP_FUPDATE_LIST]>>
  `EVERY (λ(v,x). v < LENGTH sarr) w` by simp[w_bnd_vars]>>
  simp[any_el_fill_subst]>>
  `any_el (Num (ABS l)) sarr 0 = 0` by gvs[any_el_ALT,EVERY_EL]>>
  Cases_on`ALOOKUP (REVERSE w) (Num (ABS l))`>>
  simp[dec_img_def]>>
  rename1`ALOOKUP _ _ = SOME x`>>
  `MEM (Num (ABS l),x) w` by metis_tac[ALOOKUP_MEM,MEM_REVERSE]>>
  `Num (ABS l) ≠ 0 ∧ x ≠ INR 0 ∧ Num (ABS l) < LENGTH sarr ∧
   ∀m. x = INR m ⇒ Num (ABS m) < LENGTH sarr` by (
    qpat_x_assum`w_bnd _ _` mp_tac>>
    qpat_x_assum`EVERY wf_entry _` mp_tac>>
    simp[w_bnd_def,EVERY_MEM]>>
    rpt strip_tac>>
    rpt (first_x_assum drule)>>
    simp[wf_entry_def])>>
  Cases_on`x`>>gvs[enc_img_def]
  >- (
    rename1`MEM (_,INL b) w`>>
    `&LENGTH sarr ≠ (0:int) ∧ -&LENGTH sarr ≠ (&LENGTH sarr:int)`
      by intLib.ARITH_TAC>>
    `sarr ≠ []` by (strip_tac>>gvs[])>>
    Cases_on`b`>>Cases_on`l < 0`>>simp[])>>
  rename1`MEM (_,INR m) w`>>
  rw[]>>intLib.ARITH_TAC
QED

Theorem sarr_rel_rat:
  0 < v ∧ v < LENGTH sarr ⇒
  sarr_rel (mk_subst [(v,INL b)]) T (if b then &v else -&v) sarr
Proof
  rw[sarr_rel_def,img_code_def,mk_subst_def,sub_lit_def,FUPDATE_LIST_THM,
     FLOOKUP_UPDATE,dec_img_def]>>
  `(v = Num (ABS l) ⇔ l = &v ∨ l = -&v) ∧ &LENGTH sarr ≠ (0:int) ∧
   -&LENGTH sarr ≠ (&LENGTH sarr:int) ∧ &v ≠ (-&v:int)` by intLib.ARITH_TAC>>
  rw[]>>gvs[]
QED

Theorem clear_fill_subst:
  EVERY ($= 0) sarr ∧ w_bnd w (LENGTH sarr) ⇒
  EVERY ($= 0) (clear_subst w (fill_subst kk w sarr))
Proof
  strip_tac>>
  drule_then assume_tac w_bnd_vars>>
  gvs[EVERY_0_any_el,any_el_clear_subst,any_el_fill_subst]>>
  rw[]>>
  `ALOOKUP (REVERSE w) u = NONE` by simp[ALOOKUP_NONE,MAP_REVERSE]>>
  simp[]
QED

(* Every image code is at most the length of sarr in magnitude, so a
  literal image (neither 0 nor ±length) is below it *)
Definition img_bnd_def:
  img_bnd rat p sarr ⇔
  ∀l. Num (ABS (img_code rat p sarr l)) ≤ LENGTH sarr
End

Theorem img_bnd_fill_subst:
  EVERY ($= 0) sarr ∧ w_bnd w (LENGTH sarr) ⇒
  img_bnd F p (fill_subst (LENGTH sarr) w sarr)
Proof
  rw[img_bnd_def,img_code_def]>>
  drule_then assume_tac w_bnd_vars>>
  `any_el (Num (ABS l)) sarr 0 = 0` by gvs[EVERY_0_any_el]>>
  simp[any_el_fill_subst]>>
  Cases_on`ALOOKUP (REVERSE w) (Num (ABS l))`>>simp[]>>
  rename1`ALOOKUP _ _ = SOME x`>>
  `MEM (Num (ABS l),x) w` by metis_tac[ALOOKUP_MEM,MEM_REVERSE]>>
  `∀m. x = INR m ⇒ Num (ABS m) < LENGTH sarr` by (
    qpat_x_assum`w_bnd _ _` mp_tac>>
    simp[w_bnd_def,EVERY_MEM]>>
    rpt strip_tac>>
    first_x_assum drule>>
    simp[])>>
  Cases_on`x`>>gvs[enc_img_def]>>
  rw[]
QED

Theorem img_bnd_rat:
  img_bnd T p sarr
Proof
  rw[img_bnd_def,img_code_def]>>
  intLib.ARITH_TAC
QED

(***
  The round for one clause of the formula: one pass over its literals that
  tallies the moved non-⊤ ones, classifies the clause, and assumes the
  negation of its reduct, undoing those writes as the recursion returns
 ***)

Definition inc_tally_def:
  inc_tally (k:num) (tally:num list) = LUPDATE (EL k tally + 1) k tally
End

(* l is moved by σ, and not to ⊤: the literals whose occurrences the
  certificate compares *)
Definition in_L_def:
  in_L σ l ⇔ sub_lit σ l ≠ INR l ∧ sub_lit σ l ≠ INL T
End

Definition tally_rest_def:
  tally_rest rat p sarr D i tally =
  if i = 0 then tally
  else
    let l = sub D (i - 1) in
    let y = img_code rat p sarr l in
    tally_rest rat p sarr D (i - 1)
      (if y ≠ 0 ∧ y ≠ l ∧ y ≠ &LENGTH sarr
       then inc_tally (lit_code l) tally else tally)
End

(* The pass over the literals of D from index i down. The result is 0 if
  the round on D|σ found no conflict, and otherwise the offset from which
  the group's remaining hints are skipped. *)
Definition red_pass_list_def:
  red_pass_list fmlls dml b rat p sarr tally D i s k len =
  if i = 0 then
    (case unit_prop_vb_undo_list fmlls dml b s k len of
       NONE => NONE
     | SOME (j,dml') => SOME (j,dml',tally))
  else
    let l = sub D (i - 1) in
    let y = img_code rat p sarr l in
    if y ≠ 0 ∧ y = &LENGTH sarr then
      SOME (k,dml,tally_rest rat p sarr D (i - 1) tally)
    else
      let mv = (y ≠ 0 ∧ y ≠ l) in
      let tally = (if mv then inc_tally (lit_code l) tally else tally) in
      if y ≠ 0 ∧ y = -&LENGTH sarr then
        red_pass_list fmlls dml b rat p sarr tally D (i - 1) s k len
      else
        let m = (if y = 0 then l else y) in
        let n = Num (ABS m) in
        let st = any_el n dml 0 in
        if st < b then
          (case red_pass_list fmlls (LUPDATE (if m > 0 then b + 1 else b) n dml)
                  b rat p sarr tally D (i - 1) s k len of
             NONE => NONE
           | SOME (r,dml',tally') => SOME (r,LUPDATE 0 n dml',tally'))
        else if st = (if m > 0 then b + 1 else b) then
          red_pass_list fmlls dml b rat p sarr tally D (i - 1) s k len
        else SOME (k,dml,tally_rest rat p sarr D (i - 1) tally)
End

(* The tally after counting the literals ls that are in L *)
Definition add_tally_def:
  (add_tally σ [] tally = tally) ∧
  (add_tally σ (l::ls) tally =
    add_tally σ ls (if in_L σ l then inc_tally (lit_code l) tally else tally))
End

(* What a pass over the literals ls establishes on top of the map dm: some
  literal is mapped to ⊤, or the round on their reduct conflicts *)
Definition red_ok_def:
  red_ok fml dm σ s k len ls ⇔
  EXISTS (λl. sub_lit σ l = INL T) ls ∨
  case assume_neg dm (reduct σ ls) of
    NONE => T
  | SOME dm' => ∃dm''. unit_prop_vb_vec fml dm' s k len = SOME (NONE,dm'')
End

(* One more literal l in front of a pass, by what σ and the map make of
  it *)
Theorem red_ok_top:
  sub_lit σ l = INL T ⇒ red_ok fml dm σ s k len (l::ls)
Proof
  rw[red_ok_def]
QED

Theorem red_ok_bot:
  sub_lit σ l = INL F ∧ red_ok fml dm σ s k len ls ⇒
  red_ok fml dm σ s k len (l::ls)
Proof
  rw[red_ok_def,reduct_CONS]>>
  gvs[]
QED

Theorem red_ok_true:
  sub_lit σ l = INR m ∧ lit_true dm m ⇒
  red_ok fml dm σ s k len (l::ls)
Proof
  rw[red_ok_def,reduct_CONS,assume_neg_CONS_true]
QED

Theorem red_ok_false:
  sub_lit σ l = INR m ∧ m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = SOME (m > 0) ∧
  red_ok fml dm σ s k len ls ⇒
  red_ok fml dm σ s k len (l::ls)
Proof
  rw[red_ok_def,reduct_CONS,assume_neg_CONS_false]>>
  gvs[]
QED

Theorem red_ok_unassigned:
  sub_lit σ l = INR m ∧ m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = NONE ∧
  red_ok fml (dm |+ (Num (ABS m), m > 0)) σ s k len ls ⇒
  red_ok fml dm σ s k len (l::ls)
Proof
  rw[red_ok_def,reduct_CONS,assume_neg_CONS_unassigned]>>
  gvs[]
QED

(* The stamp of a literal's variable says whether it is unassigned, false
  or true *)
Theorem dm_rel_lit:
  dm_rel dm dml b ∧ m ≠ 0 ⇒
  (any_el (Num (ABS m)) dml 0 < b ⇔ FLOOKUP dm (Num (ABS m)) = NONE) ∧
  (any_el (Num (ABS m)) dml 0 = (if m > 0 then b + 1 else b) ⇔
   FLOOKUP dm (Num (ABS m)) = SOME (m > 0)) ∧
  (¬(any_el (Num (ABS m)) dml 0 < b) ∧
   any_el (Num (ABS m)) dml 0 ≠ (if m > 0 then b + 1 else b) ⇒
   lit_true dm m)
Proof
  PURE_REWRITE_TAC[dm_rel_def,lit_true_def]>>
  strip_tac>>
  first_x_assum (qspec_then`Num (ABS m)` mp_tac)>>
  `m < 0 ⇔ ¬(m > 0)` by intLib.ARITH_TAC>>
  Cases_on`FLOOKUP dm (Num (ABS m))`>>simp[]
  >- rw[]>>
  rename1`SOME bb`>>
  Cases_on`bb`>>Cases_on`m > 0`>>simp[]
QED

(* The code for ⊥ decodes to it, and is no literal below the length *)
Theorem dec_img_bot:
  y ≠ 0 ∧ y = -&k ∧ Num (ABS l) < k ⇒
  dec_img k y l = INL F ∧ y ≠ l
Proof
  rw[dec_img_def]>>
  intLib.ARITH_TAC
QED

(* An image code that is neither ⊤ nor ⊥ is a literal below the length *)
Theorem img_lit_bound:
  Num (ABS y) ≤ k ∧ Num (ABS l) < k ∧ k ≤ n ∧
  ¬(y ≠ 0 ∧ y = &k) ∧ ¬(y ≠ 0 ∧ y = -&k) ⇒
  Num (ABS (if y = 0 then l else y)) < n
Proof
  rw[]>>
  intLib.ARITH_TAC
QED

(* The literals of D from index i - 1 down to 0 *)
Theorem REVERSE_TAKE_toList:
  0 < i ∧ i ≤ length D ⇒
  REVERSE (TAKE i (toList D)) = sub D (i - 1) :: REVERSE (TAKE (i - 1) (toList D))
Proof
  strip_tac>>
  Cases_on`i`>>gvs[TAKE_SUC_toList,REVERSE_APPEND]
QED

(* The test the passes use for membership of L *)
Theorem img_code_in_L:
  sarr_rel σ rat p sarr ∧ Num (ABS l) < LENGTH sarr ⇒
  (in_L σ l ⇔
   img_code rat p sarr l ≠ 0 ∧ img_code rat p sarr l ≠ l ∧
   img_code rat p sarr l ≠ &LENGTH sarr)
Proof
  strip_tac>>
  gvs[sarr_rel_def,in_L_def,dec_img_def]>>
  rw[]>>
  intLib.ARITH_TAC
QED

Theorem tally_rest:
  ∀i tally.
  sarr_rel σ rat p sarr ∧ i ≤ length D ∧
  (∀j. j < i ⇒ Num (ABS (sub D j)) < LENGTH sarr) ⇒
  tally_rest rat p sarr D i tally =
  add_tally σ (REVERSE (TAKE i (toList D))) tally
Proof
  Induct
  >- simp[Once tally_rest_def,add_tally_def]>>
  rpt strip_tac>>
  simp[Once tally_rest_def,REVERSE_TAKE_toList,add_tally_def]>>
  `Num (ABS (sub D i)) < LENGTH sarr` by simp[]>>
  drule_all img_code_in_L>>
  strip_tac>>
  simp[]
QED

Theorem red_pass_list:
  ∀i fmlls dml b rat p sarr tally D s k len dm r dml' tally'.
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧
  bnd_fml fmlls (LENGTH dml) ∧
  dm_rel dm dml b ∧ sarr_rel σ rat p sarr ∧ img_bnd rat p sarr ∧
  LENGTH sarr ≤ LENGTH dml ∧
  i ≤ length D ∧
  (∀j. j < i ⇒ sub D j ≠ 0 ∧ Num (ABS (sub D j)) < LENGTH sarr) ∧
  red_pass_list fmlls dml b rat p sarr tally D i s k len =
    SOME (r,dml',tally') ⇒
  dm_rel dm dml' b ∧ LENGTH dml' = LENGTH dml ∧
  tally' = add_tally σ (REVERSE (TAKE i (toList D))) tally ∧
  (r ≠ 0 ⇒ red_ok fml dm σ s k len (REVERSE (TAKE i (toList D))))
Proof
  Induct
  >- suspend "Base">>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`red_pass_list _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac>>
  once_rewrite_tac[red_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  qabbrev_tac`l = sub D i`>>
  qabbrev_tac`y = img_code rat p sarr l`>>
  `REVERSE (TAKE (SUC i) (toList D)) = l :: REVERSE (TAKE i (toList D))`
    by simp[Abbr`l`,REVERSE_TAKE_toList]>>
  `l ≠ 0 ∧ Num (ABS l) < LENGTH sarr` by simp[Abbr`l`]>>
  `sub_lit σ l = dec_img (LENGTH sarr) y l` by gvs[sarr_rel_def,Abbr`y`]>>
  `in_L σ l ⇔ y ≠ 0 ∧ y ≠ l ∧ y ≠ &LENGTH sarr`
    by metis_tac[img_code_in_L]>>
  IF_CASES_TAC
  >- suspend "Top">>
  IF_CASES_TAC
  >- suspend "Bot">>
  qabbrev_tac`m = if y = 0 then l else y`>>
  `sub_lit σ l = INR m ∧ m ≠ 0` by (
    gvs[dec_img_def,Abbr`m`]>>
    rw[]>>gvs[])>>
  `Num (ABS y) ≤ LENGTH sarr` by (
    qpat_x_assum`img_bnd _ _ _` mp_tac>>
    simp[img_bnd_def,Abbr`y`])>>
  `Num (ABS m) < LENGTH dml` by (
    qunabbrev_tac`m`>>
    metis_tac[img_lit_bound])>>
  `((y ≠ 0 ∧ y ≠ l) ⇔ m ≠ l) ∧ ((y = 0 ∨ y = l) ⇔ m = l)`
    by (rw[Abbr`m`]>>metis_tac[])>>
  qpat_x_assum`sub_lit σ l = dec_img _ _ _` kall_tac>>
  qpat_x_assum`in_L σ l ⇔ _` kall_tac>>
  `in_L σ l ⇔ m ≠ l` by simp[in_L_def]>>
  drule dm_rel_lit>>
  disch_then (qspec_then`m` mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  qpat_x_assum`y ≠ 0 ∧ y ≠ l ⇔ _` (fn th => pure_rewrite_tac[th])>>
  qpat_x_assum`y = 0 ∨ y = l ⇔ _` (fn th => pure_rewrite_tac[th])>>
  qpat_x_assum`REVERSE (TAKE (SUC i) _) = _` (fn th => pure_rewrite_tac[th])>>
  IF_CASES_TAC
  >- suspend "Unassigned">>
  IF_CASES_TAC
  >- suspend "False"
  >- suspend "True"
QED

Resume red_pass_list[Unassigned]:
  `FLOOKUP dm (Num (ABS m)) = NONE` by metis_tac[]>>
  qabbrev_tac`dml1 = LUPDATE (if m > 0 then b + 1 else b) (Num (ABS m)) dml`>>
  `dml1 = update_resize dml 0 (if m > 0 then b + 1 else b) (Num (ABS m))`
    by simp[Abbr`dml1`,update_resize_LUPDATE]>>
  `dm_rel (dm |+ (Num (ABS m), m > 0)) dml1 b` by (
    pop_assum SUBST1_TAC>>
    irule dm_rel_update_resize>>
    simp[])>>
  `LENGTH dml1 = LENGTH dml` by simp[Abbr`dml1`]>>
  qmatch_goalsub_abbrev_tac`red_pass_list _ _ _ _ _ _ tally1 _ _ _ _ _`>>
  Cases_on`red_pass_list fmlls dml1 b rat p sarr tally1 D i s k len`>>
  simp[]>>
  rename1`_ = SOME res`>>
  PairCases_on`res`>>
  simp[]>>
  strip_tac>>
  first_x_assum (qspecl_then [`fmlls`,`dml1`,`b`,`rat`,`p`,`sarr`,`tally1`,`D`,
    `s`,`k`,`len`,`dm |+ (Num (ABS m), m > 0)`,`res0`,`res1`,`res2`]
    mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  gvs[add_tally_def,Abbr`tally1`]>>
  conj_tac
  >- (irule dm_rel_LUPDATE_0>>metis_tac[])>>
  rw[]>>
  irule red_ok_unassigned>>
  qexists_tac`m`>>
  simp[]
QED

Resume red_pass_list[False]:
  `FLOOKUP dm (Num (ABS m)) = SOME (m > 0)` by metis_tac[]>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac`red_pass_list _ _ _ _ _ _ tally1 _ _ _ _ _ = _`>>
  first_x_assum (qspecl_then [`fmlls`,`dml`,`b`,`rat`,`p`,`sarr`,`tally1`,`D`,
    `s`,`k`,`len`,`dm`,`r`,`dml'`,`tally'`] mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  gvs[add_tally_def,Abbr`tally1`]>>
  rw[]>>
  irule red_ok_false>>
  simp[]>>
  qexists_tac`m`>>
  simp[]
QED

Resume red_pass_list[True]:
  `lit_true dm m` by metis_tac[]>>
  strip_tac>>
  gvs[add_tally_def]>>
  conj_tac
  >- (irule tally_rest>>simp[])>>
  metis_tac[red_ok_true]
QED

Resume red_pass_list[Base]:
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`red_pass_list _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac>>
  once_rewrite_tac[red_pass_list_def]>>
  rw[AllCaseEqs(),add_tally_def,red_ok_def,reduct_def]
  >- (drule_all unit_prop_vb_undo_list>>simp[])
  >- (drule_all unit_prop_vb_undo_list_LENGTH>>simp[])>>
  drule_all unit_prop_vb_undo_list>>
  strip_tac>>
  gvs[assume_neg_def,init_lit_map_def]
QED

Resume red_pass_list[Top]:
  strip_tac>>
  `sub_lit σ l = INL T` by gvs[dec_img_def]>>
  `¬in_L σ l` by simp[in_L_def]>>
  gvs[add_tally_def,red_ok_top]>>
  irule tally_rest>>
  simp[]
QED

Resume red_pass_list[Bot]:
  `sub_lit σ l = INL F ∧ y ≠ l` by metis_tac[dec_img_bot]>>
  `in_L σ l` by metis_tac[]>>
  `sarr ≠ [] ∧ -&LENGTH sarr ≠ l` by (
    rpt strip_tac>>gvs[])>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac`red_pass_list _ _ _ _ _ _ tally1 _ _ _ _ _ = _`>>
  first_x_assum (qspecl_then [`fmlls`,`dml`,`b`,`rat`,`p`,`sarr`,`tally1`,`D`,
    `s`,`k`,`len`,`dm`,`r`,`dml'`,`tally'`] mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  gvs[add_tally_def,Abbr`tally1`]>>
  rw[]>>
  irule red_ok_bot>>
  simp[]
QED

Finalise red_pass_list;

(***
  The walk over a line's groups
 ***)

Theorem skip_hints_vb_ge:
  ∀s i len. i ≤ skip_hints_vb s i len
Proof
  ho_match_mp_tac skip_hints_vb_ind>>
  rpt strip_tac>>
  once_rewrite_tac[skip_hints_vb_def]>>
  Cases_on`parse_vb_int s i len`>>
  rename1`parse_vb_int s i len = (m,i')`>>
  rw[]>>gvs[]>>
  `m = 0 ∨ i < len ∧ i < i'` by metis_tac[parse_vb_int_i]>>
  gvs[]
QED

(* Only hints (positive tokens) lie between offsets i and j *)
Definition hints_between_def:
  hints_between s i j len ⇔
  i ≤ j ∧ skip_hints_vb s i len = skip_hints_vb s j len ∧
  ∀d. group_offset s i len d = group_offset s j len d
End

Theorem hints_between_refl:
  hints_between s i i len
Proof
  simp[hints_between_def]
QED

Theorem hints_between_trans:
  hints_between s i j len ∧ hints_between s j k len ⇒ hints_between s i k len
Proof
  rw[hints_between_def]
QED

(* Reading one hint *)
Theorem hints_between_step:
  parse_vb_int s i len = (m,i') ∧ 0 < m ⇒ hints_between s i i' len
Proof
  strip_tac>>
  `m ≠ 0 ∧ ¬(m ≤ 0) ∧ ∀d. m ≠ -&d` by intLib.ARITH_TAC>>
  `i < i'` by metis_tac[parse_vb_int_i]>>
  rw[hints_between_def]
  >- (
    CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [skip_hints_vb_def]))>>
    simp[])>>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [group_offset_def]))>>
  simp[]
QED

Theorem unit_prop_vb_undo_list_hints_between:
  ∀fmlls dml b s i len j dml'.
  unit_prop_vb_undo_list fmlls dml b s i len = SOME (j,dml') ∧ j ≠ 0 ⇒
  hints_between s i j len
Proof
  ho_match_mp_tac unit_prop_vb_undo_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  once_rewrite_tac[unit_prop_vb_undo_list_def]>>
  Cases_on`parse_vb_int s i len`>>
  rename1`parse_vb_int s i len = (m,i')`>>
  simp[]>>
  rw[AllCaseEqs()]>>
  `hints_between s i i' len` by (
    irule hints_between_step>>
    qexists_tac`m`>>
    simp[]>>
    intLib.ARITH_TAC)>>
  metis_tac[hints_between_trans]
QED

Theorem red_pass_list_hints_between:
  ∀i fmlls dml b rat p sarr tally D s k len r dml' tally'.
  red_pass_list fmlls dml b rat p sarr tally D i s k len =
    SOME (r,dml',tally') ∧ r ≠ 0 ⇒
  hints_between s k r len
Proof
  Induct>>
  rpt gen_tac>>
  once_rewrite_tac[red_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[hints_between_refl,unit_prop_vb_undo_list_hints_between]
QED

(* The ids of the group headers from offset g, which holds a group header or
  ends the hints *)
Definition group_ids_def:
  group_ids s g len =
  let (m,k) = parse_vb_int s g len in
  if 0 ≤ m then []
  else Num (-m) :: group_ids s (skip_hints_vb s k len) len
Termination
  WF_REL_TAC `measure (λ(s,g,len). len - g)`>>
  rpt gen_tac>>strip_tac>>
  `m ≠ 0` by intLib.ARITH_TAC>>
  `g < len ∧ g < k` by metis_tac[parse_vb_int_i]>>
  qspecl_then [`s`,`k`,`len`] assume_tac skip_hints_vb_ge>>
  simp[]
End

(* The walk over the groups from offset g, which holds a group header or
  ends the hints. prev: the previous group's id; srt: whether every id so
  far exceeded its predecessor; cand: the offset of the candidate's (n's)
  group, 0 while none. A named live clause gets its pass; a dead id is
  skipped. *)
Definition walk_list_def:
  walk_list fmlls dml b rat p sarr tally n s g len prev cand srt =
  let (m,k) = parse_vb_int s g len in
  if m = 0 then SOME (cand,srt,dml,tally)
  else if 0 < m then NONE
  else
    let D = Num (-m) in
    let srt = (if D ≤ prev then F else srt) in
    if D = n then
      walk_list fmlls dml b rat p sarr tally n s (skip_hints_vb s k len) len D k
        srt
    else
      let c = any_el D fmlls vcc_none in
      if c = vcc_none then
        walk_list fmlls dml b rat p sarr tally n s (skip_hints_vb s k len) len D
          cand srt
      else
        case red_pass_list fmlls dml b rat p sarr tally c (length c) s k len of
          NONE => NONE
        | SOME (r,dml',tally') =>
          if r = 0 then NONE
          else
            walk_list fmlls dml' b rat p sarr tally' n s (skip_hints_vb s r len)
              len D cand srt
Termination
  WF_REL_TAC `measure (λ(fmlls,dml,b,rat,p,sarr,tally,n,s,g,len,prev,cand,srt).
    len - g)`>>
  rpt conj_tac
  >- (
    rpt gen_tac>>strip_tac>>
    rename1`_ = SOME (r,_,_)`>>
    `g < len ∧ g < k` by metis_tac[parse_vb_int_i]>>
    drule red_pass_list_hints_between>>
    simp[hints_between_def]>>
    strip_tac>>
    qspecl_then [`s`,`r`,`len`] assume_tac skip_hints_vb_ge>>
    simp[])>>
  rpt gen_tac>>strip_tac>>
  `g < len ∧ g < k` by metis_tac[parse_vb_int_i]>>
  qspecl_then [`s`,`k`,`len`] assume_tac skip_hints_vb_ge>>
  simp[]
End

Theorem reduct_REVERSE:
  reduct σ (REVERSE ls) = REVERSE (reduct σ ls)
Proof
  simp[reduct_def,MAP_REVERSE,FILTER_REVERSE]
QED

(* A clause's pass, read back as the spec's check of that clause *)
Theorem red_ok_check_sr:
  group_offset h i len j = SOME k ∧
  red_ok fml dm σ h k len (REVERSE (toList D)) ⇒
  check_sr fml dm σ h i len (j,D)
Proof
  strip_tac>>
  `assume_neg dm (reduct σ (REVERSE (toList D))) =
   assume_neg dm (reduct σ (toList D))` by (
    simp[reduct_REVERSE]>>
    irule assume_neg_PERM>>
    simp[PERM_REVERSE_EQ])>>
  gvs[red_ok_def,check_sr_def,classify_def,check_red_def,EXISTS_REVERSE,
      EVERY_REVERSE]>>
  rw[]>>
  Cases_on`assume_neg dm (reduct σ (toList D))`>>gvs[]
QED

Theorem check_sr_group_offset:
  group_offset h i len j = group_offset h i' len j ⇒
  (check_sr fml dm σ h i len (j,D) ⇔ check_sr fml dm σ h i' len (j,D))
Proof
  rw[check_sr_def,check_red_def]
QED

(* The token at g is the header of group d *)
Theorem group_offset_header:
  parse_vb_int s g len = (-&d,k) ∧ 0 < d ⇒
  group_offset s g len d = SOME k ∧
  ∀j. j ≠ d ⇒ group_offset s g len j = group_offset s k len j
Proof
  strip_tac>>
  `-&d ≠ (0:int)` by intLib.ARITH_TAC>>
  conj_tac
  >- simp[Once group_offset_def]>>
  rw[]>>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [group_offset_def]))>>
  simp[]
QED

Theorem group_ids_header:
  parse_vb_int s g len = (-&d,k) ∧ 0 < d ⇒
  group_ids s g len = d :: group_ids s (skip_hints_vb s k len) len
Proof
  strip_tac>>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [group_ids_def]))>>
  simp[]
QED

(* The pass of one named live clause d, read as the walk needs it *)
Theorem walk_live_step:
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧
  bnd_fml fmlls (LENGTH dml) ∧ bnd_fml fmlls (LENGTH sarr) ∧
  dm_rel dm dml b ∧ sarr_rel σ rat p sarr ∧ img_bnd rat p sarr ∧
  LENGTH sarr ≤ LENGTH dml ∧
  any_el d fmlls vcc_none ≠ vcc_none ∧
  group_offset s g len d = SOME k ∧
  red_pass_list fmlls dml b rat p sarr tally (any_el d fmlls vcc_none)
    (length (any_el d fmlls vcc_none)) s k len = SOME (r,dml1,tally1) ∧
  r ≠ 0 ⇒
  dm_rel dm dml1 b ∧ LENGTH dml1 = LENGTH dml ∧
  tally1 = add_tally σ (REVERSE (toList (any_el d fmlls vcc_none))) tally ∧
  check_sr fml dm σ s g len (d,any_el d fmlls vcc_none) ∧
  hints_between s k r len
Proof
  strip_tac>>
  qabbrev_tac`c = any_el d fmlls vcc_none`>>
  `FLOOKUP fml d = SOME c`
    by metis_tac[fml_rel_any_el_NEQ_vcc_none_FLOOKUP]>>
  `¬MEM 0 (toList c)` by (
    gvs[nz_vcfml_def,FRANGE_FLOOKUP,PULL_EXISTS]>>
    metis_tac[])>>
  `bnd_clause c (LENGTH sarr)` by gvs[bnd_fml_def,Abbr`c`]>>
  `∀j. j < length c ⇒ sub c j ≠ 0 ∧ Num (ABS (sub c j)) < LENGTH sarr` by (
    rw[]>>
    gvs[bnd_clause_def]>>
    Cases_on`c`>>
    gvs[toList_thm,sub_def,length_def,MEM_EL]>>
    metis_tac[])>>
  `TAKE (length c) (toList c) = toList c` by (
    Cases_on`c`>>simp[toList_thm,length_def])>>
  drule_at (Pos last) red_pass_list>>
  simp[]>>
  disch_then (qspecl_then [`σ`,`fml`,`dm`] mp_tac)>>
  simp[]>>
  strip_tac>>
  simp[]>>
  metis_tac[red_ok_check_sr,red_pass_list_hints_between]
QED

(* V lists the group ids the walk read; G the live ones other than n, each
  of which passed its round. The candidate's offset is the one the spec
  finds when no id is repeated. *)
Theorem walk_list:
  ∀fmlls dml b rat p sarr tally n s g len prev cand srt cand' srt' dml' tally'.
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧
  bnd_fml fmlls (LENGTH dml) ∧ bnd_fml fmlls (LENGTH sarr) ∧
  dm_rel dm dml b ∧ sarr_rel σ rat p sarr ∧ img_bnd rat p sarr ∧
  LENGTH sarr ≤ LENGTH dml ∧
  walk_list fmlls dml b rat p sarr tally n s g len prev cand srt =
    SOME (cand',srt',dml',tally') ⇒
  dm_rel dm dml' b ∧ LENGTH dml' = LENGTH dml ∧
  ∃G V.
    V = group_ids s g len ∧
    (srt' ⇒ srt ∧ EVERY (λj. prev < j) V ∧ SORTED $< V) ∧
    (ALL_DISTINCT V ⇒ ALL_DISTINCT G) ∧
    EVERY (λj. MEM j V ∧ j ≠ n ∧ any_el j fmlls vcc_none ≠ vcc_none) G ∧
    tally' =
      FOLDL (λt j. add_tally σ (REVERSE (toList (any_el j fmlls vcc_none))) t)
        tally G ∧
    (∀j. MEM j G ⇒ check_sr fml dm σ s g len (j,any_el j fmlls vcc_none)) ∧
    (∀j. ¬MEM j V ⇒ group_offset s g len j = NONE) ∧
    (ALL_DISTINCT V ⇒
     if MEM n V then cand' ≠ 0 ∧ group_offset s g len n = SOME cand'
     else cand' = cand)
Proof
  ho_match_mp_tac walk_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`walk_list _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac>>
  once_rewrite_tac[walk_list_def]>>
  Cases_on`parse_vb_int s g len`>>
  rename1`parse_vb_int s g len = (m,k)`>>
  simp_tac (srw_ss()) [LET_THM]>>
  asm_rewrite_tac[]>>
  IF_CASES_TAC
  >- suspend "End">>
  IF_CASES_TAC
  >- simp[]>>
  `∃d. m = -&d ∧ 0 < d` by (qexists_tac`Num (-m)`>>intLib.ARITH_TAC)>>
  qpat_x_assum`m = _` SUBST_ALL_TAC>>
  `Num (- -&d) = d` by simp[]>>
  pop_assum SUBST1_TAC>>
  drule_all group_offset_header>>
  strip_tac>>
  drule_all group_ids_header>>
  strip_tac>>
  `g < k` by metis_tac[parse_vb_int_i,integerTheory.INT_NEG_EQ0,
    DECIDE ``0 < d ⇒ d ≠ 0n``,integerTheory.INT_INJ]>>
  IF_CASES_TAC
  >- suspend "Cand">>
  IF_CASES_TAC
  >- suspend "Dead"
  >- suspend "Live"
QED

Resume walk_list[End]:
  rpt (qpat_x_assum`∀m'. _` kall_tac)>>
  strip_tac>>gvs[]>>
  `group_ids s g len = []` by simp[Once group_ids_def]>>
  qexists_tac`[]`>>
  simp[]>>
  rw[Once group_offset_def]
QED

Resume walk_list[Cand]:
  gvs[]>>
  strip_tac>>
  first_x_assum drule_all>>
  strip_tac>>
  simp[]>>
  `∀j. j ≠ d ⇒
     group_offset s (skip_hints_vb s k len) len j = group_offset s g len j`
    by simp[group_offset_skip_hints_vb]>>
  qexists_tac`G`>>
  `transitive ($< : num -> num -> bool)`
    by simp[relationTheory.transitive_def]>>
  rpt conj_tac
  >- (strip_tac>>gvs[SORTED_EQ,EVERY_MEM]>>rw[]>>res_tac>>simp[])
  >- simp[]
  >- gvs[EVERY_MEM]
  >- simp[]
  >- (
    rw[]>>
    `j ≠ d` by gvs[EVERY_MEM]>>
    metis_tac[check_sr_group_offset])
  >- (rw[]>>metis_tac[])>>
  strip_tac>>
  gvs[]
QED

Resume walk_list[Dead]:
  gvs[]>>
  strip_tac>>
  first_x_assum drule_all>>
  strip_tac>>
  simp[]>>
  `∀j. j ≠ d ⇒
     group_offset s (skip_hints_vb s k len) len j = group_offset s g len j`
    by simp[group_offset_skip_hints_vb]>>
  qexists_tac`G`>>
  `transitive ($< : num -> num -> bool)`
    by simp[relationTheory.transitive_def]>>
  rpt conj_tac
  >- (strip_tac>>gvs[SORTED_EQ,EVERY_MEM]>>rw[]>>res_tac>>simp[])
  >- simp[]
  >- gvs[EVERY_MEM]
  >- simp[]
  >- (
    rw[]>>
    `j ≠ d` by (gvs[EVERY_MEM]>>metis_tac[])>>
    metis_tac[check_sr_group_offset])
  >- (rw[]>>metis_tac[])>>
  strip_tac>>
  gvs[]>>
  rw[]>>
  metis_tac[]
QED

Resume walk_list[Live]:
  qpat_x_assum`∀m cand prev' srt'. _` kall_tac>>
  qpat_x_assum`∀m k' prev' srt' c. _` kall_tac>>
  qpat_x_assum`∀m k' prev' srt' c fmlls' r b' dml' tally'. _` mp_tac>>
  Cases_on`red_pass_list fmlls dml b rat p sarr tally (any_el d fmlls vcc_none)
    (length (any_el d fmlls vcc_none)) s k len`>>
  simp[]>>
  rename1`_ = SOME res`>>
  PairCases_on`res`>>
  rename1`_ = SOME (r,dml1,tally1)`>>
  Cases_on`r = 0`>>simp[]>>
  drule_all walk_live_step>>
  strip_tac>>
  strip_tac>>
  strip_tac>>
  first_x_assum (qspecl_then [`cand'`,`srt'`,`dml'`,`tally'`] mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  `skip_hints_vb s r len = skip_hints_vb s k len` by gvs[hints_between_def]>>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]))>>
  `∀j. j ≠ d ⇒
     group_offset s (skip_hints_vb s k len) len j = group_offset s g len j`
    by simp[group_offset_skip_hints_vb]>>
  `transitive ($< : num -> num -> bool)`
    by simp[relationTheory.transitive_def]>>
  simp[]>>
  qexists_tac`d::G`>>
  rpt conj_tac
  >- (strip_tac>>gvs[SORTED_EQ,EVERY_MEM]>>rw[]>>res_tac>>simp[])
  >- (strip_tac>>gvs[EVERY_MEM]>>metis_tac[])
  >- gvs[EVERY_MEM]
  >- simp[]
  >- (
    rw[]>>
    Cases_on`j = d`>>
    gvs[]>>
    metis_tac[check_sr_group_offset])
  >- (rw[]>>metis_tac[])>>
  strip_tac>>
  gvs[]>>
  rw[]>>
  metis_tac[]
QED

Finalise walk_list;

(***
  The certificate: the tally of the named clauses equals the count of all
  live clauses for every literal of L, so no other live clause contains one
 ***)

Theorem add_tally_LENGTH[simp]:
  ∀ls tally. LENGTH (add_tally σ ls tally) = LENGTH tally
Proof
  Induct>>rw[add_tally_def,inc_tally_def]
QED

Theorem FOLDL_add_tally_LENGTH[simp]:
  ∀G tally.
  LENGTH
    (FOLDL (λt j. add_tally σ (REVERSE (toList (any_el j fmlls vcc_none))) t)
      tally G) = LENGTH tally
Proof
  Induct>>simp[]
QED

Theorem add_tally_EL:
  ∀ls tally.
  EVERY (λx. lit_code x < LENGTH tally) ls ∧ lit_code l < LENGTH tally ⇒
  EL (lit_code l) (add_tally σ ls tally) =
  EL (lit_code l) tally +
  (if in_L σ l then LENGTH (FILTER ($= l) ls) else 0)
Proof
  Induct>>
  rw[add_tally_def,inc_tally_def]>>
  gvs[EL_LUPDATE,lit_code_11]>>
  rw[]>>gvs[]
QED

(* The tally after the walk named the clauses G *)
Theorem FOLDL_add_tally_EL:
  ∀G tally.
  (∀j x. MEM j G ∧ MEM x (toList (any_el j fmlls vcc_none)) ⇒
     lit_code x < LENGTH tally) ∧
  lit_code l < LENGTH tally ⇒
  EL (lit_code l)
    (FOLDL (λt j. add_tally σ (REVERSE (toList (any_el j fmlls vcc_none))) t)
      tally G) =
  EL (lit_code l) tally +
  (if in_L σ l then SUM (MAP (λj. occ l (any_el j fmlls vcc_none)) G) else 0)
Proof
  Induct
  >- simp[]>>
  rpt gen_tac>>strip_tac>>
  qmatch_goalsub_rename_tac`FOLDL _ _ (j0::G)`>>
  simp[]>>
  qabbrev_tac`tally1 =
    add_tally σ (REVERSE (toList (any_el j0 fmlls vcc_none))) tally`>>
  `LENGTH tally1 = LENGTH tally` by simp[Abbr`tally1`]>>
  first_x_assum (qspec_then`tally1` mp_tac)>>
  impl_tac
  >- (rw[]>>metis_tac[MEM])>>
  disch_then SUBST1_TAC>>
  simp[Abbr`tally1`]>>
  DEP_REWRITE_TAC[add_tally_EL]>>
  simp[EVERY_MEM,occ_def,FILTER_REVERSE]>>
  rw[]>>
  metis_tac[MEM]
QED

Theorem lit_count_GENLIST:
  N ≤ LENGTH fmlls ⇒
  lit_count fmlls N l = SUM (GENLIST (λj. occ l (EL j fmlls)) N)
Proof
  rw[lit_count_def]>>
  `TAKE N fmlls = GENLIST (λj. EL j fmlls) N`
    by rw[LIST_EQ_REWRITE,EL_TAKE]>>
  simp[MAP_GENLIST,o_DEF]
QED

(* The sum over all ids splits into the named ids and the others *)
Theorem SUM_GENLIST_split:
  ALL_DISTINCT G ∧ EVERY (λj. j < N) G ⇒
  SUM (GENLIST f N) =
  SUM (MAP f G) + SUM (MAP f (FILTER (λj. ¬MEM j G) (COUNT_LIST N)))
Proof
  strip_tac>>
  `GENLIST f N = MAP f (COUNT_LIST N)`
    by simp[COUNT_LIST_GENLIST,MAP_GENLIST]>>
  `PERM (COUNT_LIST N) (G ++ FILTER (λj. ¬MEM j G) (COUNT_LIST N))` by (
    irule PERM_ALL_DISTINCT>>
    simp[all_distinct_count_list,ALL_DISTINCT_APPEND,FILTER_ALL_DISTINCT,
         MEM_FILTER,MEM_COUNT_LIST]>>
    gvs[EVERY_MEM]>>
    metis_tac[])>>
  drule (INST_TYPE [beta |-> ``:num``] PERM_MAP)>>
  disch_then (qspec_then`f` assume_tac)>>
  drule PERM_SUM>>
  simp[SUM_APPEND]
QED

Theorem codes_in_MEM:
  codes_in c n ∧ MEM x (toList c) ⇒ lit_code x < n
Proof
  Cases_on`c`>>
  rw[codes_in_def,toList_thm,MEM_EL,sub_def,length_def]>>
  first_x_assum drule>>
  simp[]
QED

(* If the named clauses G hold all occurrences of every literal of L, then
  no literal of a live clause outside G is in L *)
Theorem cert_unnamed:
  ALL_DISTINCT G ∧ EVERY (λj. j < LENGTH fmlls) G ∧
  codes_fml fmlls n ∧
  (∀l. l ≠ 0 ∧ in_L σ l ∧ lit_code l < n ⇒
     SUM (MAP (λj. occ l (any_el j fmlls vcc_none)) G) =
     lit_count fmlls (LENGTH fmlls) l) ∧
  j < LENGTH fmlls ∧ EL j fmlls ≠ vcc_none ∧ ¬MEM j G ∧
  ¬MEM 0 (toList (EL j fmlls)) ⇒
  EVERY (λx. ¬in_L σ x) (toList (EL j fmlls))
Proof
  rw[EVERY_MEM]>>
  CCONTR_TAC>>gvs[]>>
  `x ≠ 0` by (strip_tac>>gvs[])>>
  `lit_code x < n` by (
    `codes_in (EL j fmlls) n` by gvs[codes_fml_def]>>
    metis_tac[codes_in_MEM])>>
  first_x_assum (qspec_then`x` mp_tac)>>
  simp[lit_count_GENLIST]>>
  `MAP (λj. occ x (any_el j fmlls vcc_none)) G =
   MAP (λj. occ x (EL j fmlls)) G`
    by (irule MAP_CONG>>gvs[EVERY_MEM,any_el_ALT])>>
  simp[]>>
  `EVERY (λj. j < LENGTH fmlls) G` by simp[EVERY_MEM]>>
  drule_all SUM_GENLIST_split>>
  disch_then (qspec_then`λj. occ x (EL j fmlls)` SUBST1_TAC)>>
  simp[SUM_eq_0,MEM_MAP,MEM_FILTER,MEM_COUNT_LIST,PULL_EXISTS]>>
  qexists_tac`j`>>
  simp[occ_def]>>
  strip_tac>>
  gvs[FILTER_EQ_NIL,EVERY_MEM]
QED

(* The comparison for one literal: if it is in L, its tally must equal its
  count *)
Definition cert_lit_def:
  cert_lit rat p sarr cnt tally (l:int) ⇔
  let y = img_code rat p sarr l in
  (y = 0 ∨ y = l ∨ y = &LENGTH sarr) ∨
  EL (lit_code l) tally = EL (lit_code l) cnt
End

(* Both polarities of every variable the witness maps *)
Definition cert_list_def:
  (cert_list rat p sarr cnt tally [] ⇔ T) ∧
  (cert_list rat p sarr cnt tally ((v,x:bool + int)::w) ⇔
    cert_lit rat p sarr cnt tally (&v) ∧
    cert_lit rat p sarr cnt tally (-&v) ∧
    cert_list rat p sarr cnt tally w)
End

Definition clear_tally_def:
  (clear_tally [] (tally:num list) = tally) ∧
  (clear_tally ((v,x:bool + int)::w) tally =
    clear_tally w
      (LUPDATE 0 (lit_code (-&v)) (LUPDATE 0 (lit_code (&v)) tally)))
End

Theorem cert_list_MEM:
  ∀w. cert_list rat p sarr cnt tally w ∧ MEM (v,x) w ⇒
  cert_lit rat p sarr cnt tally (&v) ∧ cert_lit rat p sarr cnt tally (-&v)
Proof
  Induct>>
  simp[cert_list_def,FORALL_PROD]>>
  metis_tac[]
QED

Theorem in_L_FDOM:
  in_L σ l ⇒ Num (ABS l) ∈ FDOM σ
Proof
  CCONTR_TAC>>
  gvs[in_L_def,sub_lit_def,FLOOKUP_DEF]
QED

Theorem cert_list_in_L:
  cert_list rat p sarr cnt tally w ∧ sarr_rel σ rat p sarr ∧
  (∀v. v ∈ FDOM σ ⇒ MEM v (MAP FST w)) ∧
  EVERY (λ(v,x). v < LENGTH sarr) w ∧
  in_L σ l ⇒
  EL (lit_code l) tally = EL (lit_code l) cnt
Proof
  strip_tac>>
  drule_then assume_tac in_L_FDOM>>
  `∃x. MEM (Num (ABS l),x) w` by (
    res_tac>>
    gvs[MEM_MAP,EXISTS_PROD]>>
    metis_tac[])>>
  drule_all cert_list_MEM>>
  strip_tac>>
  `Num (ABS l) < LENGTH sarr` by (
    gvs[EVERY_MEM,FORALL_PROD]>>
    metis_tac[])>>
  drule_all img_code_in_L>>
  strip_tac>>
  `l = &Num (ABS l) ∨ l = -&Num (ABS l)` by intLib.ARITH_TAC>>
  gvs[cert_lit_def]>>
  metis_tac[]
QED

(* With the counts up to date, a passing certificate means the clauses the
  walk named hold every occurrence of each literal of L *)
Theorem cert_list_count:
  cert_list rat p sarr cnt
    (FOLDL (λt j. add_tally σ (REVERSE (toList (any_el j fmlls vcc_none))) t)
      tally G) w ∧
  sarr_rel σ rat p sarr ∧
  (∀v. v ∈ FDOM σ ⇒ MEM v (MAP FST w)) ∧
  EVERY (λ(v,x). v < LENGTH sarr) w ∧
  EVERY ($= 0) tally ∧ LENGTH tally = LENGTH cnt ∧
  count_rel fmlls cnt (LENGTH fmlls) ∧ codes_fml fmlls (LENGTH cnt) ∧
  EVERY (λj. any_el j fmlls vcc_none ≠ vcc_none) G ∧
  l ≠ 0 ∧ in_L σ l ∧ lit_code l < LENGTH cnt ⇒
  SUM (MAP (λj. occ l (any_el j fmlls vcc_none)) G) =
  lit_count fmlls (LENGTH fmlls) l
Proof
  strip_tac>>
  drule_all cert_list_in_L>>
  strip_tac>>
  `EL (lit_code l) cnt = lit_count fmlls (LENGTH fmlls) l`
    by gvs[count_rel_def]>>
  `EL (lit_code l) tally = 0` by gvs[EVERY_EL]>>
  qspecl_then [`G`,`tally`] mp_tac FOLDL_add_tally_EL>>
  impl_tac
  >- (
    gvs[]>>
    rpt strip_tac>>
    `any_el j fmlls vcc_none ≠ vcc_none` by gvs[EVERY_MEM]>>
    `j < LENGTH fmlls` by (CCONTR_TAC>>gvs[any_el_ALT])>>
    gvs[any_el_ALT,codes_fml_def]>>
    metis_tac[codes_in_MEM])>>
  simp[]
QED

Theorem LENGTH_clear_tally[simp]:
  ∀w tally. LENGTH (clear_tally w tally) = LENGTH tally
Proof
  Induct>>simp[clear_tally_def,FORALL_PROD]
QED

(* After the walk, a non-zero tally entry is at the code of a literal of L *)
Theorem add_tally_nonzero:
  ∀ls tally c.
  c < LENGTH tally ∧ EL c (add_tally σ ls tally) ≠ EL c tally ⇒
  ∃l. c = lit_code l ∧ in_L σ l
Proof
  Induct
  >- simp[add_tally_def]>>
  rpt gen_tac>>
  qmatch_goalsub_rename_tac`add_tally σ (x::ls)`>>
  simp[add_tally_def]>>
  qabbrev_tac`tally1 =
    if in_L σ x then inc_tally (lit_code x) tally else tally`>>
  strip_tac>>
  `LENGTH tally1 = LENGTH tally` by rw[Abbr`tally1`,inc_tally_def]>>
  reverse (Cases_on`EL c (add_tally σ ls tally1) = EL c tally1`)
  >- (first_x_assum (qspecl_then [`tally1`,`c`] mp_tac)>>simp[])>>
  gvs[Abbr`tally1`,inc_tally_def]>>
  Cases_on`in_L σ x`>>gvs[EL_LUPDATE]>>
  Cases_on`c = lit_code x`>>gvs[]>>
  metis_tac[]
QED

Theorem clear_tally_zero:
  ∀w tally.
  (∀c. c < LENGTH tally ∧ EL c tally ≠ 0 ⇒
     ∃v. MEM v (MAP FST w) ∧ (c = lit_code (&v) ∨ c = lit_code (-&v))) ⇒
  EVERY ($= 0) (clear_tally w tally)
Proof
  Induct
  >- (simp[clear_tally_def,EVERY_EL]>>metis_tac[])>>
  simp[FORALL_PROD,clear_tally_def]>>
  rpt strip_tac>>
  first_x_assum irule>>
  rw[EL_LUPDATE]>>
  first_x_assum (qspec_then`c` mp_tac)>>
  rw[]>>
  metis_tac[]
QED

(***
  The candidate's round: the last on the line, so its writes are not
  undone, and it neither tallies nor tests for an unmoved candidate
 ***)

(* k: the offset of the candidate's group, 0 if it has none *)
Definition cand_pass_list_def:
  cand_pass_list fmlls dml b rat p sarr C i s k len =
  if i = 0 then
    (if k = 0 then SOME (F,dml)
     else
       case unit_prop_vb_list fmlls dml b s k len of
         NONE => NONE
       | SOME (res,dml') => SOME (res = NONE,dml'))
  else
    let l = sub C (i - 1) in
    let y = img_code rat p sarr l in
    if y ≠ 0 ∧ y = &LENGTH sarr then SOME (T,dml)
    else if y ≠ 0 ∧ y = -&LENGTH sarr then
      cand_pass_list fmlls dml b rat p sarr C (i - 1) s k len
    else
      let m = (if y = 0 then l else y) in
      let n = Num (ABS m) in
      let st = any_el n dml 0 in
      if st < b then
        cand_pass_list fmlls (LUPDATE (if m > 0 then b + 1 else b) n dml) b
          rat p sarr C (i - 1) s k len
      else if st = (if m > 0 then b + 1 else b) then
        cand_pass_list fmlls dml b rat p sarr C (i - 1) s k len
      else SOME (T,dml)
End

(* What the candidate's pass over the literals ls establishes on top of
  dm: a literal is mapped to ⊤, or the round on their reduct, from the
  candidate's group at offset k, conflicts *)
Definition cand_ok_def:
  cand_ok fml dm σ s k len ls ⇔
  EXISTS (λl. sub_lit σ l = INL T) ls ∨
  case assume_neg dm (reduct σ ls) of
    NONE => T
  | SOME dm' =>
    k ≠ 0 ∧ ∃dm''. unit_prop_vb_vec fml dm' s k len = SOME (NONE,dm'')
End

Theorem cand_ok_top:
  sub_lit σ l = INL T ⇒ cand_ok fml dm σ s k len (l::ls)
Proof
  rw[cand_ok_def]
QED

Theorem cand_ok_bot:
  sub_lit σ l = INL F ∧ cand_ok fml dm σ s k len ls ⇒
  cand_ok fml dm σ s k len (l::ls)
Proof
  rw[cand_ok_def,reduct_CONS]>>
  gvs[]
QED

Theorem cand_ok_true:
  sub_lit σ l = INR m ∧ lit_true dm m ⇒
  cand_ok fml dm σ s k len (l::ls)
Proof
  rw[cand_ok_def,reduct_CONS,assume_neg_CONS_true]
QED

Theorem cand_ok_false:
  sub_lit σ l = INR m ∧ m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = SOME (m > 0) ∧
  cand_ok fml dm σ s k len ls ⇒
  cand_ok fml dm σ s k len (l::ls)
Proof
  rw[cand_ok_def,reduct_CONS,assume_neg_CONS_false]>>
  gvs[]
QED

Theorem cand_ok_unassigned:
  sub_lit σ l = INR m ∧ m ≠ 0 ∧ FLOOKUP dm (Num (ABS m)) = NONE ∧
  cand_ok fml (dm |+ (Num (ABS m), m > 0)) σ s k len ls ⇒
  cand_ok fml dm σ s k len (l::ls)
Proof
  rw[cand_ok_def,reduct_CONS,assume_neg_CONS_unassigned]>>
  gvs[]
QED

Theorem cand_ok_check_cand:
  group_offset h i len n = (if k = 0 then NONE else SOME k) ∧
  cand_ok fml dm σ h k len (REVERSE (toList C)) ⇒
  check_cand fml dm σ h i len n C
Proof
  strip_tac>>
  `assume_neg dm (reduct σ (REVERSE (toList C))) =
   assume_neg dm (reduct σ (toList C))` by (
    simp[reduct_REVERSE]>>
    irule assume_neg_PERM>>
    simp[PERM_REVERSE_EQ])>>
  gvs[cand_ok_def,check_cand_def,check_red_def,EXISTS_REVERSE]>>
  Cases_on`assume_neg dm (reduct σ (toList C))`>>gvs[]
QED

Theorem cand_pass_list:
  ∀i fmlls dml b rat p sarr C s k len dm res dml'.
  fml_rel fml fmlls ∧ bnd_fml fmlls (LENGTH dml) ∧
  dm_rel dm dml b ∧ sarr_rel σ rat p sarr ∧ img_bnd rat p sarr ∧
  LENGTH sarr ≤ LENGTH dml ∧
  i ≤ length C ∧
  (∀j. j < i ⇒ sub C j ≠ 0 ∧ Num (ABS (sub C j)) < LENGTH sarr) ∧
  cand_pass_list fmlls dml b rat p sarr C i s k len = SOME (res,dml') ⇒
  (∃dm'. dm_rel dm' dml' b) ∧ LENGTH dml' = LENGTH dml ∧
  (res ⇒ cand_ok fml dm σ s k len (REVERSE (TAKE i (toList C))))
Proof
  Induct
  >- suspend "Base">>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`cand_pass_list _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac>>
  once_rewrite_tac[cand_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  qabbrev_tac`l = sub C i`>>
  qabbrev_tac`y = img_code rat p sarr l`>>
  `REVERSE (TAKE (SUC i) (toList C)) = l :: REVERSE (TAKE i (toList C))`
    by simp[Abbr`l`,REVERSE_TAKE_toList]>>
  `l ≠ 0 ∧ Num (ABS l) < LENGTH sarr` by simp[Abbr`l`]>>
  `sub_lit σ l = dec_img (LENGTH sarr) y l` by gvs[sarr_rel_def,Abbr`y`]>>
  qpat_x_assum`REVERSE (TAKE (SUC i) _) = _` (fn th => pure_rewrite_tac[th])>>
  IF_CASES_TAC
  >- suspend "Top">>
  IF_CASES_TAC
  >- suspend "Bot">>
  qabbrev_tac`m = if y = 0 then l else y`>>
  `sub_lit σ l = INR m ∧ m ≠ 0` by (
    gvs[dec_img_def,Abbr`m`]>>
    rw[]>>gvs[])>>
  `Num (ABS y) ≤ LENGTH sarr` by (
    qpat_x_assum`img_bnd _ _ _` mp_tac>>
    simp[img_bnd_def,Abbr`y`])>>
  `Num (ABS m) < LENGTH dml` by (
    qunabbrev_tac`m`>>
    metis_tac[img_lit_bound])>>
  qpat_x_assum`sub_lit σ l = dec_img _ _ _` kall_tac>>
  drule dm_rel_lit>>
  disch_then (qspec_then`m` mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  IF_CASES_TAC
  >- suspend "Unassigned">>
  IF_CASES_TAC
  >- suspend "False"
  >- suspend "True"
QED

Resume cand_pass_list[Base]:
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`cand_pass_list _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac>>
  once_rewrite_tac[cand_pass_list_def]>>
  rw[AllCaseEqs()]
  >- metis_tac[]
  >- (drule_all unit_prop_vb_list>>strip_tac>>metis_tac[])
  >- metis_tac[unit_prop_vb_list_LENGTH]>>
  drule_all unit_prop_vb_list>>
  strip_tac>>
  gvs[cand_ok_def,reduct_def,assume_neg_def,init_lit_map_def]
QED

Resume cand_pass_list[Top]:
  strip_tac>>gvs[]>>
  `sub_lit σ l = INL T` by gvs[dec_img_def]>>
  metis_tac[cand_ok_top]
QED

Resume cand_pass_list[Bot]:
  `sub_lit σ l = INL F ∧ y ≠ l` by metis_tac[dec_img_bot]>>
  strip_tac>>
  first_x_assum (qspecl_then [`fmlls`,`dml`,`b`,`rat`,`p`,`sarr`,`C`,`s`,`k`,
    `len`,`dm`,`res`,`dml'`] mp_tac)>>
  rw[]>>
  metis_tac[cand_ok_bot]
QED

Resume cand_pass_list[Unassigned]:
  `FLOOKUP dm (Num (ABS m)) = NONE` by metis_tac[]>>
  qabbrev_tac`dml1 = LUPDATE (if m > 0 then b + 1 else b) (Num (ABS m)) dml`>>
  `dml1 = update_resize dml 0 (if m > 0 then b + 1 else b) (Num (ABS m))`
    by simp[Abbr`dml1`,update_resize_LUPDATE]>>
  `dm_rel (dm |+ (Num (ABS m), m > 0)) dml1 b` by (
    pop_assum SUBST1_TAC>>
    irule dm_rel_update_resize>>
    simp[])>>
  `LENGTH dml1 = LENGTH dml` by simp[Abbr`dml1`]>>
  strip_tac>>
  first_x_assum (qspecl_then [`fmlls`,`dml1`,`b`,`rat`,`p`,`sarr`,`C`,`s`,`k`,
    `len`,`dm |+ (Num (ABS m), m > 0)`,`res`,`dml'`] mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  rpt conj_tac
  >- metis_tac[]
  >- simp[]>>
  strip_tac>>
  irule cand_ok_unassigned>>
  qexists_tac`m`>>
  simp[]
QED

Resume cand_pass_list[False]:
  `FLOOKUP dm (Num (ABS m)) = SOME (m > 0)` by metis_tac[]>>
  strip_tac>>
  first_x_assum (qspecl_then [`fmlls`,`dml`,`b`,`rat`,`p`,`sarr`,`C`,`s`,`k`,
    `len`,`dm`,`res`,`dml'`] mp_tac)>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  rpt conj_tac
  >- metis_tac[]
  >- simp[]>>
  strip_tac>>
  irule cand_ok_false>>
  metis_tac[]
QED

Resume cand_pass_list[True]:
  `lit_true dm m` by metis_tac[]>>
  strip_tac>>gvs[]>>
  metis_tac[cand_ok_true]
QED

Finalise cand_pass_list;

(***
  One step of the proof
 ***)

(* A clause without a literal of L is satisfied or unmoved by σ *)
Theorem check_sr_not_in_L:
  EVERY (λx. ¬in_L σ x) (toList D) ⇒ check_sr fml dm σ h i len (j,D)
Proof
  rw[check_sr_def,classify_def]>>
  gvs[EVERY_MEM,EXISTS_MEM,in_L_def]>>
  metis_tac[]
QED

Theorem bnd_clause_codes_in:
  bnd_clause c n ⇒ codes_in c (2 * n)
Proof
  rw[bnd_clause_def,codes_in_def,lit_code_bound]
QED

Theorem bnd_fml_codes_fml:
  bnd_fml fmlls n ⇒ codes_fml fmlls (2 * n)
Proof
  rw[bnd_fml_def,codes_fml_def,codes_in_def,bnd_clause_def]>>
  first_x_assum (qspec_then`j` mp_tac)>>
  simp[any_el_ALT,lit_code_bound]
QED

(* Literals whose code is beyond the counts occur in no live clause *)
Theorem count_rel_grow:
  count_rel fmlls cnt wm ∧ codes_fml fmlls (LENGTH cnt) ⇒
  count_rel fmlls (cnt ++ REPLICATE k 0) wm
Proof
  rw[count_rel_def]>>
  Cases_on`lit_code l < LENGTH cnt`
  >- gvs[EL_APPEND_EQN]>>
  simp[EL_APPEND_EQN,EL_REPLICATE]>>
  simp[lit_count_def,SUM_eq_0,MEM_MAP,PULL_EXISTS]>>
  rw[]>>
  rename1`MEM c (TAKE wm fmlls)`>>
  `MEM c fmlls` by metis_tac[MEM_TAKE]>>
  Cases_on`c = vcc_none`
  >- simp[occ_vcc_none]>>
  `codes_in c (LENGTH cnt)` by (
    gvs[codes_fml_def,MEM_EL]>>
    metis_tac[])>>
  simp[occ_def,FILTER_EQ_NIL,EVERY_MEM]>>
  metis_tac[codes_in_MEM]
QED

Theorem fml_rel_free:
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧
  any_el n fmlls vcc_none = vcc_none ⇒
  n ∉ FDOM fml
Proof
  rw[fml_rel_def,nz_vcfml_def,FRANGE_FLOOKUP]>>
  first_x_assum (qspec_then`n` mp_tac)>>
  rw[FLOOKUP_DEF]>>
  strip_tac>>gvs[]>>
  first_x_assum (qspec_then`fml ' n` mp_tac)>>
  impl_tac
  >- (qexists_tac`n`>>simp[FLOOKUP_DEF])>>
  simp[vcc_none_def,toList_thm]
QED

Theorem fml_rel_live:
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧ FLOOKUP fml j = SOME D ⇒
  any_el j fmlls vcc_none = D ∧ D ≠ vcc_none ∧ j < LENGTH fmlls
Proof
  strip_tac>>
  `any_el j fmlls vcc_none = D` by (
    gvs[fml_rel_def]>>
    first_x_assum (qspec_then`j` mp_tac)>>
    simp[])>>
  `D ≠ vcc_none` by (
    strip_tac>>
    gvs[nz_vcfml_def,FRANGE_FLOOKUP,PULL_EXISTS]>>
    first_x_assum drule>>
    simp[vcc_none_def,toList_thm])>>
  simp[]>>
  CCONTR_TAC>>
  gvs[any_el_ALT]
QED

Theorem FOLDL_add_tally_nonzero:
  ∀G tally c.
  c < LENGTH tally ∧
  EL c (FOLDL (λt j. add_tally σ (REVERSE (toList (any_el j fmlls vcc_none))) t)
    tally G) ≠ EL c tally ⇒
  ∃l. c = lit_code l ∧ in_L σ l
Proof
  Induct>>
  rw[]>>
  qmatch_asmsub_abbrev_tac`FOLDL _ tally1 G`>>
  `LENGTH tally1 = LENGTH tally` by simp[Abbr`tally1`]>>
  Cases_on`EL c tally1 = EL c tally`
  >- (first_x_assum (qspecl_then [`tally1`,`c`] mp_tac)>>simp[])>>
  metis_tac[add_tally_nonzero]
QED

(* Clearing the witness's codes restores a zero tally after the walk *)
Theorem clear_tally_FOLDL_zero:
  EVERY ($= 0) tally ∧ (∀v. v ∈ FDOM σ ⇒ MEM v (MAP FST w)) ⇒
  EVERY ($= 0)
    (clear_tally w
      (FOLDL (λt j. add_tally σ (REVERSE (toList (any_el j fmlls vcc_none))) t)
        tally G))
Proof
  strip_tac>>
  irule clear_tally_zero>>
  rw[]>>
  `EL c tally = 0` by gvs[EVERY_EL]>>
  qspecl_then [`G`,`tally`,`c`] mp_tac FOLDL_add_tally_nonzero>>
  simp[]>>
  strip_tac>>
  drule_then assume_tac in_L_FDOM>>
  qexists_tac`Num (ABS l)`>>
  `l = &Num (ABS l) ∨ l = -&Num (ABS l)` by intLib.ARITH_TAC>>
  metis_tac[]
QED

Theorem stamps_ok_LUPDATE_stamp:
  stamps_ok dml b ⇒ stamps_ok (LUPDATE (if c then b + 1 else b) n dml) b
Proof
  rw[stamps_ok_def]>>
  irule IMP_EVERY_LUPDATE>>
  rw[]
QED

Theorem stamps_ok_red_pass_list:
  ∀i fmlls dml b rat p sarr tally D s k len r dml' tally'.
  stamps_ok dml b ∧
  red_pass_list fmlls dml b rat p sarr tally D i s k len =
    SOME (r,dml',tally') ⇒
  stamps_ok dml' b
Proof
  Induct>>
  rpt gen_tac>>
  once_rewrite_tac[red_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[stamps_ok_unit_prop_vb_undo_list,stamps_ok_LUPDATE_0,
    stamps_ok_LUPDATE_stamp]
QED

Theorem tally_rest_LENGTH[simp]:
  ∀i tally. LENGTH (tally_rest rat p sarr D i tally) = LENGTH tally
Proof
  Induct>>
  rw[Once tally_rest_def,inc_tally_def]
QED

Theorem red_pass_list_LENGTH:
  ∀i fmlls dml b rat p sarr tally D s k len r dml' tally'.
  bnd_fml fmlls (LENGTH dml) ∧
  red_pass_list fmlls dml b rat p sarr tally D i s k len =
    SOME (r,dml',tally') ⇒
  LENGTH dml' = LENGTH dml ∧ LENGTH tally' = LENGTH tally
Proof
  Induct>>
  rpt gen_tac>>
  once_rewrite_tac[red_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  imp_res_tac unit_prop_vb_undo_list_LENGTH>>
  res_tac>>
  gvs[inc_tally_def]
QED

Theorem unit_prop_vb_undo_list_le:
  ∀fmlls dml b s i len j dml'.
  unit_prop_vb_undo_list fmlls dml b s i len = SOME (j,dml') ∧ i ≤ len ⇒
  j ≤ len
Proof
  ho_match_mp_tac unit_prop_vb_undo_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`unit_prop_vb_undo_list _ _ _ _ _ _ = _` mp_tac>>
  simp[Once unit_prop_vb_undo_list_def]>>
  pairarg_tac>>gvs[]>>
  drule_all parse_vb_int_le>>
  rw[AllCaseEqs()]>>
  gvs[]
QED

Theorem red_pass_list_le:
  ∀i fmlls dml b rat p sarr tally D s k len r dml' tally'.
  red_pass_list fmlls dml b rat p sarr tally D i s k len =
    SOME (r,dml',tally') ∧ k ≤ len ⇒
  r ≤ len
Proof
  Induct>>
  rpt gen_tac>>
  once_rewrite_tac[red_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[unit_prop_vb_undo_list_le]
QED

Theorem stamps_ok_walk_list:
  ∀fmlls dml b rat p sarr tally n s g len prev cand srt cand' srt' dml' tally'.
  stamps_ok dml b ∧
  walk_list fmlls dml b rat p sarr tally n s g len prev cand srt =
    SOME (cand',srt',dml',tally') ⇒
  stamps_ok dml' b
Proof
  ho_match_mp_tac walk_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  once_rewrite_tac[walk_list_def]>>
  Cases_on`parse_vb_int s g len`>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[stamps_ok_red_pass_list]
QED

Theorem stamps_ok_cand_pass_list:
  ∀i fmlls dml b rat p sarr C s k len res dml'.
  stamps_ok dml b ∧
  cand_pass_list fmlls dml b rat p sarr C i s k len = SOME (res,dml') ⇒
  stamps_ok dml' b
Proof
  Induct>>
  rpt gen_tac>>
  once_rewrite_tac[cand_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[stamps_ok_unit_prop_vb_list,stamps_ok_LUPDATE_stamp]
QED

Theorem cand_pass_list_LENGTH:
  ∀i fmlls dml b rat p sarr C s k len res dml'.
  bnd_fml fmlls (LENGTH dml) ∧
  cand_pass_list fmlls dml b rat p sarr C i s k len = SOME (res,dml') ⇒
  LENGTH dml' = LENGTH dml
Proof
  Induct>>
  rpt gen_tac>>
  once_rewrite_tac[cand_pass_list_def]>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[unit_prop_vb_list_LENGTH,LENGTH_LUPDATE]
QED

(* Decoding a non-zero value ends within the hints *)
Theorem parse_vb_int_nz_le:
  parse_vb_int s i len = (v,j) ∧ v ≠ 0 ⇒ j ≤ len
Proof
  strip_tac>>
  `i < len` by metis_tac[parse_vb_int_i]>>
  drule parse_vb_int_le>>
  simp[]
QED

(* The offset where the RUP hints stop is within the hints *)
Theorem unit_prop_vb_list_SOME_le:
  ∀fmlls dml b s i len j dml'.
  unit_prop_vb_list fmlls dml b s i len = SOME (SOME j,dml') ∧ i ≤ len ⇒
  j ≤ len
Proof
  ho_match_mp_tac unit_prop_vb_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>strip_tac>>
  qpat_x_assum`unit_prop_vb_list _ _ _ _ _ _ = _` mp_tac>>
  simp[Once unit_prop_vb_list_def]>>
  pairarg_tac>>gvs[]>>
  drule_all parse_vb_int_le>>
  rw[AllCaseEqs()]>>
  gvs[]
QED

(* The walk returns the candidate offset it was given, or one within the
  hints *)
Theorem walk_list_cand_le:
  ∀fmlls dml b rat p sarr tally n s g len prev cand srt cand' srt' dml' tally'.
  walk_list fmlls dml b rat p sarr tally n s g len prev cand srt =
    SOME (cand',srt',dml',tally') ⇒
  cand' = cand ∨ cand' ≤ len
Proof
  ho_match_mp_tac walk_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  once_rewrite_tac[walk_list_def]>>
  Cases_on`parse_vb_int s g len`>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]
  >- (
    drule_all parse_vb_int_nz_le>>
    strip_tac>>
    qpat_x_assum`_ ⇒ _` mp_tac>>
    impl_tac
    >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    disch_then drule>>
    strip_tac>>
    gvs[])
  >- (
    qpat_x_assum`_ ⇒ ∀a b c d. walk_list _ _ _ _ _ _ _ _ _ _ _ _ cand _ = _ ⇒ _`
      mp_tac>>
    impl_tac
    >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
    disch_then drule>>
    simp[])>>
  qpat_x_assum`∀r dml tally. _`
    (qspecl_then [`r'`,`dml''`,`tally''`] mp_tac)>>
  impl_tac
  >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
  disch_then drule>>
  simp[]
QED

Theorem walk_list_LENGTH:
  ∀fmlls dml b rat p sarr tally n s g len prev cand srt cand' srt' dml' tally'.
  bnd_fml fmlls (LENGTH dml) ∧
  walk_list fmlls dml b rat p sarr tally n s g len prev cand srt =
    SOME (cand',srt',dml',tally') ⇒
  LENGTH dml' = LENGTH dml ∧ LENGTH tally' = LENGTH tally
Proof
  ho_match_mp_tac walk_list_ind>>
  rpt gen_tac>>strip_tac>>
  rpt gen_tac>>
  once_rewrite_tac[walk_list_def]>>
  Cases_on`parse_vb_int s g len`>>
  simp_tac (srw_ss()) [LET_THM]>>
  rw[AllCaseEqs()]>>
  metis_tac[red_pass_list_LENGTH]
QED

(* When the map grows, sarr and tally are replaced by zero arrays and the
  counts are copied into a larger one *)
Definition grow_list_def:
  grow_list n (sarr:int list) (cnt:num list) (tally:num list) =
  if LENGTH sarr < n then
    (REPLICATE n 0, cnt ++ REPLICATE (2 * n - LENGTH cnt) 0,
     REPLICATE (2 * n) 0)
  else (sarr,cnt,tally)
End

(* The pivot of a RAT line: a witness that maps the pivot to ⊤ and nothing
  else *)
Definition rat_pivot_def:
  (rat_pivot [(v,INL b)] = SOME (if b then (&v:int) else -&v)) ∧
  (rat_pivot (w:(num # (bool + int)) list) = NONE)
End

Theorem rat_pivot_SOME:
  rat_pivot w = SOME p ⇒
  ∃v b. w = [(v,INL b)] ∧ p = if b then &v else -&v
Proof
  Cases_on`w`>>simp[rat_pivot_def]>>
  rename1`x::w`>>
  PairCases_on`x`>>
  rename1`(v,y)::w`>>
  Cases_on`y`>>Cases_on`w`>>
  simp[rat_pivot_def]
QED

(* The state threaded through the steps: the formula, the assignment map and
  its stamp, the substitution array, the counts with their watermark, the
  tally, and tp, from which on no clause is live. On a non-RUP line the
  counts catch up to tp, which becomes the watermark. *)
Definition check_lsr_list_def:
  check_lsr_list lsr fmlls dml b sarr cnt wm tally tp =
  case lsr of
    Delvb s i =>
      (case delete_ids_cnt_list fmlls cnt wm s i (strlen s) of
        (fmlls',cnt') => SOME (fmlls',dml,b,sarr,cnt',wm,tally,tp))
  | Lsrvb n C w h =>
    if any_el n fmlls vcc_none ≠ vcc_none then NONE
    else
    let sz = sz_witness w (sz_lit_map (length C) C 0) in
    case reset_dm_list dml b sz of (dml1,b1) =>
    case grow_list (LENGTH dml1) sarr cnt tally of (sarr1,cnt1,tally1) =>
    case rup_dm_vb_list fmlls dml1 b1 C h of
      NONE => NONE
    | SOME (NONE,dml2) =>
      (case insert_cnt_list fmlls cnt1 wm n C of
        (fmlls',cnt2) =>
          SOME (fmlls',dml2,b1,sarr1,cnt2,wm,tally1,MAX tp (n + 1)))
    | SOME (SOME i0,dml2) =>
      let (rat,p) = (case rat_pivot w of SOME p => (T,p) | NONE => (F,0)) in
      let sarr2 = (if rat then sarr1 else fill_subst (LENGTH sarr1) w sarr1) in
      let len = strlen h in
      case walk_list fmlls dml2 b1 rat p sarr2 tally1 n h i0 len 0 0 T of
        NONE => NONE
      | SOME (cand,srt,dml3,tally2) =>
        if ¬srt ∧ ¬ALL_DISTINCT (group_ids h i0 len) then NONE
        else
        let lim = MIN tp (LENGTH fmlls) in
        let cnt2 = catch_up fmlls wm lim cnt1 in
        if ¬cert_list rat p sarr2 cnt2 tally2 w then NONE
        else
          case cand_pass_list fmlls dml3 b1 rat p sarr2 C (length C) h cand len of
            SOME (T,dml4) =>
              (case insert_cnt_list fmlls cnt2 lim n C of
                (fmlls',cnt3) =>
                SOME (fmlls',dml4,b1,clear_subst w sarr2,cnt3,lim,
                      clear_tally w tally2,MAX tp (n + 1)))
          | _ => NONE
End

(* The state kept between steps *)
Definition lsr_inv_def:
  lsr_inv fmlls dml b (sarr:int list) (cnt:num list) (wm:num)
    (tally:num list) (tp:num) ⇔
  dm_ok fmlls dml b ∧ (∃dm. dm_rel dm dml b) ∧
  LENGTH sarr = LENGTH dml ∧ EVERY ($= 0) sarr ∧
  LENGTH cnt = 2 * LENGTH dml ∧ LENGTH tally = LENGTH cnt ∧
  EVERY ($= 0) tally ∧ count_rel fmlls cnt wm ∧ wm ≤ tp ∧ top_ok fmlls tp
End

Theorem grow_list_inv:
  ∀n sarr cnt tally sarr1 cnt1 tally1.
  LENGTH sarr = LENGTH (dml:num list) ∧ EVERY ($= 0) sarr ∧
  LENGTH cnt = 2 * LENGTH dml ∧ LENGTH tally = LENGTH cnt ∧
  EVERY ($= 0) tally ∧ count_rel fmlls cnt wm ∧
  codes_fml fmlls (LENGTH cnt) ∧ LENGTH dml ≤ n ∧
  grow_list n sarr cnt tally = (sarr1,cnt1,tally1) ⇒
  LENGTH sarr1 = n ∧ EVERY ($= 0) sarr1 ∧ LENGTH cnt1 = 2 * n ∧
  LENGTH tally1 = LENGTH cnt1 ∧ EVERY ($= 0) tally1 ∧
  count_rel fmlls cnt1 wm
Proof
  rw[grow_list_def]>>
  gvs[EVERY_REPLICATE]>>
  irule count_rel_grow>>
  simp[]
QED

Theorem check_lsr_list:
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧ wf_lsr lsr ∧
  lsr_inv fmlls dml b sarr cnt wm tally tp ∧
  check_lsr_list lsr fmlls dml b sarr cnt wm tally tp =
    SOME (fmlls',dml',b',sarr',cnt',wm',tally',tp') ⇒
  ∃fml'.
    check_lsr lsr fml = SOME fml' ∧ fml_rel fml' fmlls' ∧
    lsr_inv fmlls' dml' b' sarr' cnt' wm' tally' tp'
Proof
  strip_tac>>
  `codes_fml fmlls (LENGTH cnt)`
    by gvs[lsr_inv_def,dm_ok_def,bnd_fml_codes_fml]>>
  Cases_on`lsr`
  >- (
    rename1`Delvb s i`>>
    gvs[check_lsr_list_def,check_lsr_def]>>
    Cases_on`delete_ids_cnt_list fmlls cnt wm s i (strlen s)`>>
    rename1`_ = (fmlls1,cnt1)`>>
    gvs[]>>
    `fmlls' = delete_ids_vb_list vcc_none fmlls s i (strlen s)`
      by metis_tac[delete_ids_cnt_list_fml,FST]>>
    gvs[lsr_inv_def,dm_ok_def]>>
    drule count_rel_delete_ids_cnt_list>>
    disch_then (qspecl_then [`s`,`i`,`strlen s`,
      `delete_ids_vb_list vcc_none fmlls s i (strlen s)`,`cnt'`] mp_tac)>>
    rw[fml_rel_delete_ids_vb_list,bnd_fml_delete_ids_vb_list,
      top_ok_delete_ids_vb_list]>>
    metis_tac[])>>
  rename1`Lsrvb n C w h`>>
  qpat_x_assum`check_lsr_list _ _ _ _ _ _ _ _ _ = _` mp_tac>>
  simp[check_lsr_list_def]>>
  strip_tac>>
  `n ∉ FDOM fml` by metis_tac[fml_rel_free]>>
  gvs[lsr_inv_def,dm_ok_def,wf_lsr_def]>>
  qabbrev_tac`sz = sz_witness w (sz_lit_map (length C) C 0)`>>
  Cases_on`reset_dm_list dml b sz`>>
  rename1`_ = (dml1,b1)`>>
  `dm_rel FEMPTY dml1 b1 ∧ sz ≤ LENGTH dml1`
    by metis_tac[dm_rel_reset_dm_list]>>
  `LENGTH dml ≤ LENGTH dml1` by metis_tac[reset_dm_list_LENGTH]>>
  `stamps_ok dml1 b1` by metis_tac[stamps_ok_reset_dm_list]>>
  `bnd_fml fmlls (LENGTH dml1)` by metis_tac[bnd_fml_le]>>
  `sz_lit_map (length C) C 0 ≤ sz` by simp[Abbr`sz`,sz_witness_mono]>>
  `bnd_clause C (LENGTH dml1)` by (
    irule bnd_clause_le>>
    qexists_tac`sz_lit_map (length C) C 0`>>
    simp[sz_lit_map_bnd_clause])>>
  `w_bnd w (LENGTH dml1)` by (
    qspecl_then [`w`,`sz_lit_map (length C) C 0`] assume_tac sz_witness_bnd>>
    gvs[w_bnd_def,EVERY_MEM,FORALL_PROD]>>
    rw[]>>res_tac>>gvs[Abbr`sz`])>>
  Cases_on`grow_list (LENGTH dml1) sarr cnt tally`>>
  rename1`_ = (sarr1,cnt1t)`>>
  PairCases_on`cnt1t`>>
  rename1`_ = (sarr1,cnt1,tally1)`>>
  qspecl_then [`LENGTH dml1`,`sarr`,`cnt`,`tally`,`sarr1`,`cnt1`,`tally1`]
    mp_tac grow_list_inv>>
  impl_tac
  >- simp[]>>
  strip_tac>>
  gvs[]>>
  Cases_on`rup_dm_vb_list fmlls dml1 b1 C h`>>gvs[]>>
  rename1`_ = SOME res`>>
  PairCases_on`res`>>
  rename1`_ = SOME (r0,dml2)`>>
  drule_all rup_dm_vb_list>>
  strip_tac>>
  `LENGTH dml2 = LENGTH dml1` by metis_tac[rup_dm_vb_list_LENGTH]>>
  `stamps_ok dml2 b1` by metis_tac[stamps_ok_rup_dm_vb_list]>>
  Cases_on`r0`
  >- (
    Cases_on`insert_cnt_list fmlls cnt1 wm n C`>>
    rename1`_ = (fmlls2,cnt2)`>>
    gvs[]>>
    `codes_in C (LENGTH cnt1)` by gvs[bnd_clause_codes_in]>>
    drule_all count_rel_insert_cnt_list>>
    strip_tac>>
    gvs[insert_cnt_list_def,check_lsr_def]>>
    rw[fml_rel_insert_vcc_list,bnd_fml_insert_vcc_list,
      top_ok_insert_vcc_list]>>
    metis_tac[])>>
  rename1`rup_dm_vb_list _ _ _ _ _ = SOME (SOME i0,dml2)`>>
  qabbrev_tac`σ = mk_subst w`>>
  `∃rat p. (case rat_pivot w of NONE => (F,0) | SOME p => (T,p)) = (rat,p)`
    by metis_tac[PAIR]>>
  gvs[]>>
  qabbrev_tac`sarr2 = if rat then sarr1 else fill_subst (LENGTH dml1) w sarr1`>>
  sg`sarr_rel σ rat p sarr2 ∧ img_bnd rat p sarr2 ∧ LENGTH sarr2 = LENGTH dml1 ∧
     EVERY ($= 0) (clear_subst w sarr2)`
  >- (
    Cases_on`rat_pivot w`>>gvs[Abbr`sarr2`]
    >- (
      simp[Abbr`σ`]>>
      rpt conj_tac
      >- metis_tac[sarr_rel_fill_subst]
      >- metis_tac[img_bnd_fill_subst]>>
      metis_tac[clear_fill_subst])>>
    drule rat_pivot_SOME>>
    strip_tac>>
    gvs[w_bnd_def,wf_entry_def,img_bnd_rat]>>
    conj_tac
    >- (
      simp[Abbr`σ`]>>
      irule sarr_rel_rat>>
      simp[])>>
    gvs[EVERY_0_any_el,any_el_clear_subst])>>
  qpat_x_assum`option_CASE (walk_list _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ = _` mp_tac>>
  simp[AllCaseEqs()]>>
  disch_then (strip_assume_tac o PURE_ONCE_REWRITE_RULE [DISJ_EQ_IMP])>>
  rpt VAR_EQ_TAC>>
  drule_at (Pos last) walk_list>>
  disch_then (qspecl_then [`σ`,`fml`,`dm'`] mp_tac)>>
  impl_tac
  >- gvs[]>>
  strip_tac>>
  `ALL_DISTINCT V` by (
    Cases_on`srt`>>gvs[]>>
    irule SORTED_ALL_DISTINCT>>
    qexists_tac`$<`>>
    simp[relationTheory.irreflexive_def,relationTheory.transitive_def])>>
  qpat_x_assum`ALL_DISTINCT V ⇒ ALL_DISTINCT G`
    (fn th => first_assum (assume_tac o MATCH_MP th))>>
  qpat_x_assum`ALL_DISTINCT V ⇒ if _ then _ else _`
    (fn th => first_assum (assume_tac o MATCH_MP th))>>
  `∀j. j < length C ⇒ sub C j ≠ 0 ∧ Num (ABS (sub C j)) < LENGTH sarr2` by (
    qpat_x_assum`¬MEM 0 _` mp_tac>>
    qpat_x_assum`bnd_clause _ _` mp_tac>>
    qpat_x_assum`LENGTH sarr2 = _` mp_tac>>
    rpt (pop_assum kall_tac)>>
    Cases_on`C`>>
    rw[bnd_clause_def,toList_thm,sub_def,length_def,MEM_EL]>>
    metis_tac[])>>
  drule_at (Pos last) cand_pass_list>>
  disch_then (qspecl_then [`σ`,`fml`,`dm'`] mp_tac)>>
  impl_tac
  >- gvs[]>>
  strip_tac>>
  `∀v. v ∈ FDOM σ ⇒ MEM v (MAP FST w)`
    by simp[Abbr`σ`,mk_subst_def,FDOM_FUPDATE_LIST]>>
  `codes_fml fmlls (2 * LENGTH dml1)` by simp[bnd_fml_codes_fml]>>
  qabbrev_tac`lim = MIN tp (LENGTH fmlls)`>>
  `count_rel fmlls (catch_up fmlls wm lim cnt1) lim ∧
   LENGTH (catch_up fmlls wm lim cnt1) = LENGTH cnt1` by (
    irule count_rel_catch_up>>
    gvs[Abbr`lim`,count_rel_def])>>
  `count_rel fmlls (catch_up fmlls wm lim cnt1) (LENGTH fmlls)` by (
    irule count_rel_top>>
    qpat_assum`count_rel _ (catch_up _ _ _ _) lim` (irule_at Any)>>
    qpat_assum`top_ok _ _` (irule_at Any)>>
    simp[Abbr`lim`])>>
  `check_cand fml dm' σ h i0 (strlen h) n C` by (
    irule cand_ok_check_cand>>
    qexists_tac`cand`>>
    `TAKE (length C) (toList C) = toList C` by (
      rpt (pop_assum kall_tac)>>
      Cases_on`C`>>
      simp[toList_thm,length_def])>>
    Cases_on`MEM n V`>>gvs[])>>
  sg`EVERY (check_sr fml dm' σ h i0 (strlen h)) (fmap_to_alist fml)`
  >- (
    simp[EVERY_MEM,FORALL_PROD,MEM_fmap_to_alist_FLOOKUP]>>
    rpt strip_tac>>
    rename1`FLOOKUP fml j = SOME D`>>
    drule_all fml_rel_live>>
    strip_tac>>
    Cases_on`MEM j G`
    >- (
      qpat_x_assum`∀j. MEM j G ⇒ _` drule>>
      simp[])>>
    irule check_sr_not_in_L>>
    `¬MEM 0 (toList D)` by (
      qpat_x_assum`nz_vcfml _` mp_tac>>
      simp[nz_vcfml_def,FRANGE_FLOOKUP]>>
      disch_then match_mp_tac>>
      qexists_tac`j`>>
      first_assum ACCEPT_TAC)>>
    `EL j fmlls = D` by gvs[any_el_ALT]>>
    qpat_assum`EL j fmlls = D` (SUBST1_TAC o SYM)>>
    irule cert_unnamed>>
    qpat_assum`EL j fmlls = D` SUBST1_TAC>>
    rpt (conj_tac >- first_assum ACCEPT_TAC)>>
    `EVERY (λj. any_el j fmlls vcc_none ≠ vcc_none) G` by (
      qpat_x_assum`EVERY (λj. MEM j V ∧ _) G` mp_tac>>
      match_mp_tac EVERY_MONOTONIC>>
      simp[])>>
    qexistsl_tac[`G`,`2 * LENGTH dml1`]>>
    conj_tac
    >- (
      rpt strip_tac>>
      `EVERY (λ(v,x). v < LENGTH sarr2) w` by gvs[w_bnd_vars]>>
      qpat_x_assum`tally2 = _` (fn th =>
        qpat_x_assum`cert_list _ _ _ _ _ _` (assume_tac o REWRITE_RULE [th]))>>
      drule cert_list_count>>
      disch_then irule>>
      gvs[])>>
    rpt (conj_tac >- first_assum ACCEPT_TAC)>>
    conj_tac
    >- (
      qpat_x_assum`EVERY (λj. any_el j fmlls vcc_none ≠ vcc_none) G` mp_tac>>
      match_mp_tac EVERY_MONOTONIC>>
      rw[any_el_ALT]>>
      CCONTR_TAC>>
      gvs[])>>
    first_assum ACCEPT_TAC)>>
  `codes_in C (LENGTH (catch_up fmlls wm lim cnt1))` by gvs[bnd_clause_codes_in]>>
  drule_at (Pos last) count_rel_insert_cnt_list>>
  impl_tac
  >- (rpt conj_tac>>first_assum ACCEPT_TAC)>>
  strip_tac>>
  `stamps_ok dml3 b'` by (
    drule_at (Pos last) stamps_ok_walk_list>>
    disch_then irule>>
    first_assum ACCEPT_TAC)>>
  `stamps_ok dml' b'` by (
    drule_at (Pos last) stamps_ok_cand_pass_list>>
    disch_then irule>>
    first_assum ACCEPT_TAC)>>
  `EVERY ($= 0) (clear_tally w tally2) ∧ LENGTH tally2 = LENGTH tally1` by (
    qpat_x_assum`tally2 = _` SUBST1_TAC>>
    simp[]>>
    irule clear_tally_FOLDL_zero>>
    conj_tac>>
    first_assum ACCEPT_TAC)>>
  qunabbrev_tac`σ`>>
  gvs[insert_cnt_list_def,check_lsr_def,fml_rel_insert_vcc_list,
    top_ok_insert_vcc_list,Abbr`lim`]>>
  conj_tac
  >- (
    irule bnd_fml_insert_vcc_list>>
    conj_tac>>
    first_assum ACCEPT_TAC)>>
  first_assum (irule_at Any)
QED

Definition check_lsrs_list_def:
  (check_lsrs_list [] fmlls dml b sarr cnt wm tally tp = SOME fmlls) ∧
  (check_lsrs_list (x::xs) fmlls dml b sarr cnt wm tally tp =
    case check_lsr_list x fmlls dml b sarr cnt wm tally tp of
      NONE => NONE
    | SOME (fmlls',dml',b',sarr',cnt',wm',tally',tp') =>
      check_lsrs_list xs fmlls' dml' b' sarr' cnt' wm' tally' tp')
End

Theorem check_lsrs_list:
  ∀lsrs fml fmlls dml b sarr cnt wm tally tp fmlls'.
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧ EVERY wf_lsr lsrs ∧
  lsr_inv fmlls dml b sarr cnt wm tally tp ∧
  check_lsrs_list lsrs fmlls dml b sarr cnt wm tally tp = SOME fmlls' ⇒
  ∃fml'. check_lsrs lsrs fml = SOME fml' ∧ fml_rel fml' fmlls'
Proof
  Induct>>
  simp[check_lsrs_list_def,check_lsrs_def]>>
  rw[]>>
  gvs[AllCaseEqs()]>>
  drule_all check_lsr_list>>
  strip_tac>>
  drule_all check_lsr_nz_vcfml>>
  strip_tac>>
  first_x_assum drule_all>>
  simp[]
QED

Definition check_lsrs_unsat_list_def:
  check_lsrs_unsat_list lsrs fmlls dml b sarr cnt wm tally tp =
  case check_lsrs_list lsrs fmlls dml b sarr cnt wm tally tp of
    NONE => F
  | SOME fmlls' => contains_emp_list fmlls'
End

Theorem check_lsrs_unsat_list:
  fml_rel fml fmlls ∧ nz_vcfml (FRANGE fml) ∧ EVERY wf_lsr lsrs ∧
  lsr_inv fmlls dml b sarr cnt wm tally tp ∧
  check_lsrs_unsat_list lsrs fmlls dml b sarr cnt wm tally tp ⇒
  check_lsrs_unsat lsrs fml
Proof
  simp[check_lsrs_unsat_list_def,check_lsrs_unsat_def]>>
  strip_tac>>
  Cases_on`check_lsrs_list lsrs fmlls dml b sarr cnt wm tally tp`>>
  gvs[]>>
  drule_all check_lsrs_list>>
  strip_tac>>
  gvs[]>>
  metis_tac[fml_rel_contains_emp_list]
QED

(* The input clauses occupy ids kc to kc + LENGTH ls - 1 *)
Theorem top_ok_build_cfml_list:
  top_ok (build_cfml_list kc ls nc) (kc + LENGTH ls)
Proof
  rw[top_ok_def]>>
  `any_el k (build_fml_list kc ls nc) vcc_none = vcc_none`
    by simp[any_el_build_fml_list,lookup_build_fml]>>
  gvs[build_cfml_list_def,any_el_ALT]
QED

(* The state the checker starts from: arrays of zeros, the map at stamp 1,
  and nothing counted yet *)
Theorem lsr_inv_init:
  bnd_fml fmlls n ∧ top_ok fmlls tp ⇒
  lsr_inv fmlls (REPLICATE n 0) 1 (REPLICATE n 0) (REPLICATE (2 * n) 0) 0
    (REPLICATE (2 * n) 0) tp
Proof
  rw[lsr_inv_def,dm_ok_REPLICATE,EVERY_REPLICATE]
  >- metis_tac[dm_rel_FEMPTY_REPLICATE]>>
  rw[count_rel_def,lit_count_def,EL_REPLICATE]
QED

(* The checker's guarantee at the list level, phrased on the parsed
  formula rather than on the checker's internal representation *)
Theorem check_lsrs_unsat_list_sound:
  check_lsrs_unsat_list lsrs
    (build_cfml_list kc (conv_cfml cfml) nc)
    (REPLICATE n 0) 1 (REPLICATE n 0) (REPLICATE (2 * n) 0) 0
    (REPLICATE (2 * n) 0) (kc + LENGTH cfml) ∧
  EVERY (EVERY nz_lit) cfml ∧
  EVERY (EVERY (λl. var_lit l < n)) cfml ∧
  EVERY wf_lsr lsrs ⇒
  unsatisfiable_cnf (set cfml)
Proof
  strip_tac>>
  irule check_lsrs_unsat_conv_sound>>
  simp[]>>
  qexistsl_tac [`kc`,`lsrs`]>>
  simp[]>>
  irule check_lsrs_unsat_list>>
  simp[range_build_cfml,nz_vcfml_conv_cfml]>>
  first_x_assum (irule_at Any)>>
  simp[fml_rel_build_cfml_list]>>
  irule lsr_inv_init>>
  conj_tac
  >- (
    irule bnd_fml_build_cfml_list>>
    irule bnd_clause_conv_cfml>>
    first_assum ACCEPT_TAC)>>
  `LENGTH cfml = LENGTH (conv_cfml cfml)` by simp[conv_cfml_def]>>
  pop_assum SUBST1_TAC>>
  simp[top_ok_build_cfml_list]
QED

(* A slot holding vcc_none is a deleted clause, so dropping such entries
  from the spec formula keeps the refinement *)
Theorem fml_rel_drop_none:
  fml_rel fml fmlls ⇒
  fml_rel (DRESTRICT fml {n | FLOOKUP fml n ≠ SOME vcc_none}) fmlls
Proof
  rw[fml_rel_def,FLOOKUP_DRESTRICT]>>
  first_x_assum (qspec_then`n` mp_tac)>>
  Cases_on`FLOOKUP fml n`>>
  rw[]>>
  gvs[]
QED

(* The spec formula of an input whose entries may be vcc_none: those
  entries are deleted clauses *)
Theorem build_cfml_list_none:
  ∀vcfml kc nc.
  EVERY (λc. c ≠ vcc_none ⇒ ¬MEM 0 (toList c)) vcfml ⇒
  ∃fml.
    fml_rel fml (build_cfml_list kc vcfml nc) ∧ nz_vcfml (FRANGE fml) ∧
    FRANGE fml ⊆ set vcfml DIFF {vcc_none}
Proof
  rpt strip_tac>>
  qabbrev_tac`fml0 = build_cfml kc vcfml`>>
  qexists_tac`DRESTRICT fml0 {n | FLOOKUP fml0 n ≠ SOME vcc_none}`>>
  `fml_rel (DRESTRICT fml0 {n | FLOOKUP fml0 n ≠ SOME vcc_none})
     (build_cfml_list kc vcfml nc)` by (
    irule fml_rel_drop_none>>
    simp[Abbr`fml0`,fml_rel_build_cfml_list])>>
  `FRANGE (DRESTRICT fml0 {n | FLOOKUP fml0 n ≠ SOME vcc_none}) ⊆
     set vcfml DIFF {vcc_none}` by (
    `FRANGE fml0 = set vcfml` by simp[Abbr`fml0`,range_build_cfml]>>
    rw[SUBSET_DEF,IN_FRANGE_FLOOKUP,FLOOKUP_DRESTRICT]>>
    gvs[EXTENSION,IN_FRANGE_FLOOKUP]>>
    metis_tac[])>>
  gvs[nz_vcfml_def,SUBSET_DEF,EVERY_MEM]>>
  metis_tac[]
QED

(* The guarantee for an input whose entries may be vcc_none: those entries
  are loaded as deleted clauses, and the checker refutes the others *)
Theorem check_lsrs_unsat_list_sound_none:
  check_lsrs_unsat_list lsrs
    (build_cfml_list kc vcfml nc)
    (REPLICATE n 0) 1 (REPLICATE n 0) (REPLICATE (2 * n) 0) 0
    (REPLICATE (2 * n) 0) (kc + LENGTH vcfml) ∧
  EVERY (λc. bnd_clause c n) vcfml ∧
  EVERY (λc. c ≠ vcc_none ⇒ ¬MEM 0 (toList c)) vcfml ∧
  EVERY wf_lsr lsrs ⇒
  ¬∃w. satisfies_vcfml w (set vcfml DIFF {vcc_none})
Proof
  strip_tac>>
  qspecl_then [`vcfml`,`kc`,`nc`] mp_tac build_cfml_list_none>>
  impl_tac
  >- first_assum ACCEPT_TAC>>
  strip_tac>>
  sg`check_lsrs_unsat lsrs fml`
  >- (
    irule check_lsrs_unsat_list>>
    simp[]>>
    qpat_x_assum`check_lsrs_unsat_list _ _ _ _ _ _ _ _ _` (irule_at Any)>>
    simp[top_ok_build_cfml_list]>>
    irule lsr_inv_init>>
    simp[top_ok_build_cfml_list]>>
    irule bnd_fml_build_cfml_list>>
    first_assum ACCEPT_TAC)>>
  gvs[check_lsrs_unsat_def]>>
  Cases_on`check_lsrs lsrs fml`>>
  gvs[]>>
  CCONTR_TAC>>
  gvs[]>>
  `satisfies_vcfml w (FRANGE fml)` by
    gvs[satisfies_vcfml_def,satisfies_fml_gen_def,SUBSET_DEF]>>
  drule_all check_lsrs_sound>>
  metis_tac[contains_emp_unsat]
QED

