(*
  Normalization from pb_preconstraint into pb_constraint
*)
open preamble pb_preconstraintTheory pb_constraintTheory;

val _ = new_theory "pb_normalise";

val _ = numLib.prefer_num();

(*
  Injective mapping from mlstring into num

  This does not simply parse a number but is optimized to keep numbers small if they are in the range

  a-z, A-Z, 0-9, []{}_^

  Other characters can be used but

  EVAL ``MAP ORD (explode (strlit "[]{}_^"))``
*)
Definition mapNon_def:
  mapNon n =
  if n = 91 then 63
  else if n = 93 then 64
  else if n = 123 then 65
  else if n = 125 then 66
  else if n = 95 then 67
  else if n = 94 then 68
  else 0
End

Definition mapChar_def:
  mapChar c =
  let oc = ORD c in
  if 48 ≤ oc ∧ oc ≤ 57 (* char 0 to 9 maps to 1-10 respectively *)
  then oc - 47
  else if 65 ≤ oc ∧ oc ≤ 90 (* char A to Z maps to 11-36 *)
  then oc - 54
  else if 97 ≤ oc ∧ oc ≤ 122 (* char a to z maps to 37-62 *)
  then oc - 60
  else mapNon oc
End

Definition mapChars_def:
  (mapChars 0 str = 0) ∧
  (mapChars (SUC n) str =
    mapChars n str * 68 + mapChar (strsub str n))
End

Definition mapString_def:
  mapString str = mapChars (strlen str) str
End

(* Kind of a circular definition ... *)
Definition goodChar_def:
  goodChar c ⇔
  mapChar c ≠ 0
End

Definition goodChars_def:
  (goodChars 0 str = T) ∧
  (goodChars (SUC n) str =
    (goodChar (strsub str n) ∧
    goodChars n str))
End

Definition goodString_def:
  goodString str = goodChars (strlen str) str
End

Theorem mapString_INJ:
  INJ mapString goodString UNIV
Proof
  cheat
QED

Definition convert_pbf:
  convert_pbf pbf = MAP (map_pbc mapString) pbf
End

(* TODO: prove that, under suitable assumptions
  convert_pbf preserves satisfiability exactly
*)

(* Convert a list of pbc to one with ≥ constraints only *)
Definition pbc_ge_def:
  (pbc_ge (GreaterEqual xs n) = [GreaterEqual xs n]) ∧
  (pbc_ge (Equal xs n) =
    let xs' = MAP (λ(c:int,l). (-c,l)) xs in
      [GreaterEqual xs n; GreaterEqual xs' (-n)])
End

Theorem eq_disj:
  (∀x. x = a ∨ x = b ⇒ P x) ⇔ P a ∧ P b
Proof
  metis_tac[]
QED

Theorem eval_term_negate:
  ∀ls.
  (MAP (eval_term w) (MAP (λ(c,l). (-c,l)) ls)) =
  (MAP (\i. -i) (MAP (eval_term w) ls))
Proof
  Induct>>simp[]>>
  Cases>>rw[eval_term_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_negate:
  ∀ls. iSUM (MAP (\i. -i) ls) = -iSUM ls
Proof
  Induct>>simp[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem pbc_ge_thm:
  ∀c.
  satisfies w (set (pbc_ge c)) ⇔
  satisfies_pbc w c
Proof
  Cases>>
  simp[pbc_ge_def,satisfies_def]>>
  rw[EQ_IMP_THM]
  >- (
    fs[satisfies_pbc_def,eq_disj,eval_term_negate,iSUM_negate]>>
    intLib.ARITH_TAC) >>
  fs[satisfies_pbc_def,eval_term_negate,iSUM_negate]>>
  intLib.ARITH_TAC
QED

Definition term_lt_def[simp]:
  term_lt (_,l1) (_,l2) = (lit_var l1 < lit_var l2)
End

Definition term_le_def[simp]:
  term_le (_,l1) (_,l2) = (lit_var l1 <= lit_var l2)
End

(* Ensure compact LHS in preconstraint form:
  sort by variables *)
Definition compact_lhs_def:
  (compact_lhs ((c1:int,l1)::(c2,l2)::cs) n =
    if lit_var l1 = lit_var l2 then
      if l1 = l2 then
        compact_lhs ((c1+c2,l1)::cs) n
      else
        compact_lhs ((c1-c2,l1)::cs) (n+c2)
    else
      let (cs',n') = compact_lhs ((c2,l2)::cs) n in
      ((c1,l1)::cs',n')) ∧
  (compact_lhs c n = (c,n))
End

Theorem compact_lhs_MEM:
  ∀xs n xs' n' y l.
  compact_lhs xs n = (xs',n') ∧
  MEM (y,l) xs' ⇒
  ∃y'. MEM (y',l) xs
Proof
  ho_match_mp_tac (theorem "compact_lhs_ind")>>
  rw[compact_lhs_def]>> fs[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    pairarg_tac>>gs[]>>rw[]>>fs[]>>rw[]>>
    metis_tac[])
  >> metis_tac[]
QED

Theorem transitive_term_le:
  transitive term_le
Proof
  simp[transitive_def]>>
  rpt Cases >>
  simp[term_le_def]
QED

Theorem transitive_term_lt:
  transitive term_lt
Proof
  simp[transitive_def]>>
  rpt Cases >>
  simp[term_lt_def]
QED

Theorem lit_var_eq_term_le:
  lit_var l1 = lit_var l2 ⇒
  (term_le (a,l1) x ⇔ term_le (b,l2) x)
Proof
  Cases_on`x`>>rw[term_le_def]
QED

Theorem compact_lhs_no_dup:
  ∀xs n xs' n'.
  SORTED term_le xs ∧
  compact_lhs xs n = (xs',n') ⇒
  SORTED term_lt xs'
Proof
  ho_match_mp_tac (theorem "compact_lhs_ind")>>
  rw[compact_lhs_def]>> fs[]
  >- (
    first_x_assum match_mp_tac>>
    qpat_x_assum `SORTED _ _` mp_tac>>
    DEP_REWRITE_TAC[SORTED_EQ]>>simp[transitive_term_le]>>
    metis_tac[lit_var_eq_term_le])
  >- (
    first_x_assum match_mp_tac>>
    qpat_x_assum `SORTED _ _` mp_tac>>
    DEP_REWRITE_TAC[SORTED_EQ]>>simp[transitive_term_le]>>
    metis_tac[lit_var_eq_term_le])>>
  pairarg_tac>>fs[]>>rw[]>>
  qpat_x_assum `SORTED _ _` mp_tac>>
  DEP_REWRITE_TAC[SORTED_EQ]>>
  simp[transitive_term_le,transitive_term_lt]>>
  simp[FORALL_PROD]>>rw[]>>
  drule compact_lhs_MEM>>
  disch_then drule>>strip_tac>>
  fs[]>>first_x_assum drule>>
  fs[]
QED

Theorem iSUM_PERM:
  ∀l1 l2. PERM l1 l2 ⇒
  iSUM l1 = iSUM l2
Proof
  ho_match_mp_tac PERM_IND>>rw[iSUM_def]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_QSORT_term_le[simp]:
  iSUM (MAP (eval_term w) (QSORT $≤ l)) =
  iSUM (MAP (eval_term w) l)
Proof
  match_mp_tac iSUM_PERM>>
  match_mp_tac PERM_MAP>>
  metis_tac[QSORT_PERM,PERM_SYM]
QED

Theorem eval_lit_eq_flip:
  q * eval_lit w r = q + (-q * eval_lit w (negate r))
Proof
  Cases_on`r` \\ EVAL_TAC
  \\ Cases_on`w a` \\ EVAL_TAC
  \\ fs[]
QED

Theorem compact_lhs_sound:
  ∀xs n xs' n'.
  compact_lhs xs n = (xs',n') ⇒
  iSUM (MAP (pb_preconstraint$eval_term w) xs) + n = iSUM (MAP (pb_preconstraint$eval_term w) xs') + n'
Proof
  ho_match_mp_tac (theorem "compact_lhs_ind")>>
  rw[compact_lhs_def]>> fs[]
  >- (
    (* l1 = l2 *)
    fs[iSUM_def]>>
    intLib.ARITH_TAC)
  >- (
    (* l1 = negate l2 *)
    fs[iSUM_def]>>
    qmatch_goalsub_abbrev_tac` A + _ + _`>>
    REWRITE_TAC[Once eval_lit_eq_flip]>>
    `negate l2 = l1` by
      (Cases_on`l1`>>Cases_on`l2`>>fs[])>>
    fs[Abbr`A`]>>
    qpat_x_assum`_ = _ + _` sym_sub_tac>>
    simp[integerTheory.INT_SUB_RDISTRIB]>>
    qmatch_goalsub_abbrev_tac`_ * wl2 + _ +_ = _ - _ + is + _`>>
    rpt (pop_assum kall_tac)>>
    intLib.ARITH_TAC)>>
  pairarg_tac>>fs[]>>
  rw[]>>
  fs[iSUM_def]>>
  intLib.ARITH_TAC
QED

Definition mk_coeff_def:
  (mk_coeff c (Pos v) = c) ∧
  (mk_coeff c (Neg v) = -c:int)
End

Definition normalize_lhs_def:
  (normalize_lhs [] acc n = (REVERSE acc,n)) ∧
  (normalize_lhs ((x,l)::xs) acc n =
    let v = lit_var l in
    if x < 0 then
      normalize_lhs xs ((mk_coeff x l,v)::acc) (n+x)
    else if x > 0 then normalize_lhs xs ((mk_coeff x l,v)::acc) n
    else normalize_lhs xs acc n)
End

Theorem normalize_lhs_normalizes:
  ∀ls acc n ls' n'.
  normalize_lhs ls acc n = (ls',n') ⇒
  iSUM (MAP (pb_preconstraint$eval_term w) ls) + &(SUM (MAP (eval_term w) acc)) + n =
  &(SUM (MAP (eval_term w) ls')) + n'
Proof
  Induct>>rw[normalize_lhs_def,iSUM_def]
  >-
    metis_tac[SUM_REVERSE,MAP_REVERSE] >>
  Cases_on`h`>>fs[normalize_lhs_def]>>
  every_case_tac>>fs[]
  >- intLib.ARITH_TAC>>
  first_x_assum drule>>
  simp[GSYM integerTheory.INT_ADD]
  >- (
    qmatch_goalsub_abbrev_tac`&SUM _ + qq`>>
    `qq = q * eval_lit w r` by
      (fs[Abbr`qq`]>>Cases_on`r`>>simp[mk_coeff_def]>>
      rename1`b2n( w a)`>>
      Cases_on`w a`>>simp[]>>
      intLib.COOPER_TAC)>>
    rw[] >>
    rename1`A +B + C + D = E`>>
    pop_assum mp_tac>> rpt (pop_assum kall_tac)>> intLib.ARITH_TAC)
  >- (
    qmatch_goalsub_abbrev_tac`&SUM _ + qq`>>
    `qq + q  = q * eval_lit w r` by (
      fs[Abbr`qq`]>>Cases_on`r`>>simp[mk_coeff_def]>>
      rename1`b2n (w a)`>>
      Cases_on`w a`>>simp[]>>
      intLib.ARITH_TAC)>>
    rw[] >>
    rename1`A +B + C + D = E`>>
    ntac 2 (pop_assum mp_tac)>> rpt (pop_assum kall_tac)>> intLib.ARITH_TAC)
  >- (
    `q=0` by intLib.ARITH_TAC>>
    simp[])
QED

Definition pbc_to_npbc_def:
  (pbc_to_npbc (GreaterEqual lhs n) =
    let (lhs',m') = compact_lhs (QSORT term_le lhs) 0 in
    let (lhs'',m'') = normalize_lhs lhs' [] 0 in
    let rhs = if n-(m'+m'') ≥ 0 then Num(n-(m'+m'')) else 0 in
    PBC lhs'' rhs) ∧
  (pbc_to_npbc (Equal xs n) = PBC [] 0)
End

Definition normalize_def:
  normalize pbf =
  let pbf' = FLAT (MAP pbc_ge pbf) in
  MAP pbc_to_npbc pbf'
End

Theorem pbc_to_npbc_thm:
  (∀xs n. pbc ≠ Equal xs n) ⇒
  (satisfies_pbc w pbc ⇔ satisfies_npbc w (pbc_to_npbc pbc))
Proof
  Cases_on`pbc`>>fs[]>>
  rw[satisfies_pbc_def,satisfies_npbc_def,pbc_to_npbc_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  drule compact_lhs_sound>>
  disch_then(qspec_then`w` assume_tac)>>fs[]>>
  drule normalize_lhs_normalizes>>
  disch_then(qspec_then`w` assume_tac)>>fs[]>>
  simp[satisfies_npbc_def]>>
  intLib.ARITH_TAC
QED

Theorem normalize_thm:
  satisfies w (set pbf) ⇔
  satisfies w (set (normalize pbf))
Proof
  simp[normalize_def]>>
  qmatch_goalsub_abbrev_tac`MAP _ pbf'`>>
  `satisfies w (set pbf) ⇔ satisfies w (set pbf')` by
    (simp[Abbr`pbf'`]>>
    Induct_on`pbf`>>
    simp[]>>
    metis_tac[pbc_ge_thm])>>
  simp[]>>
  `!x. MEM x pbf' ⇒ (∀xs n. x ≠ Equal xs n)` by
    (simp[Abbr`pbf'`,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    Cases_on`y`>>simp[pbc_ge_def]>>
    rw[]>>simp[])>>
  pop_assum mp_tac>>
  rpt(pop_assum kall_tac)>>
  Induct_on`pbf'`>>simp[]>>
  rw[]>>
  metis_tac[pbc_to_npbc_thm]
QED

Theorem lit_var_negate[simp]:
  lit_var (negate r) = lit_var r
Proof
  Cases_on`r`>>simp[]
QED

Theorem normalize_lhs_compact1:
  ∀lhs acc n lhs' n'.
  normalize_lhs lhs acc n = (lhs',n') ∧
  SORTED $< (MAP SND (REVERSE acc) ++ MAP (lit_var o SND) lhs) ⇒
  SORTED $< (MAP SND lhs')
Proof
  Induct>>simp[normalize_lhs_def]>>
  Cases>>simp[normalize_lhs_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]
  >- (
    PURE_REWRITE_TAC[Once (GSYM APPEND_ASSOC),APPEND]>>
    fs[])
  >- (
    PURE_REWRITE_TAC[Once (GSYM APPEND_ASSOC),APPEND]>>
    fs[]) >>
  pop_assum mp_tac>>
  DEP_REWRITE_TAC[SORTED_APPEND,SORTED_EQ]  >>
  CONJ_TAC>- simp[transitive_def]>>
  simp[]
QED

Theorem normalize_lhs_compact2:
  ∀lhs acc n lhs' n'.
  normalize_lhs lhs acc n = (lhs',n') ∧
  EVERY (λc. c ≠ 0) (MAP FST acc) ⇒
  EVERY (λc. c ≠ 0) (MAP FST lhs')
Proof
  Induct>>simp[normalize_lhs_def]
  >-
    simp[EVERY_MAP]>>
  Cases>>fs[normalize_lhs_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  Cases_on`r`>>fs[mk_coeff_def]>>
  intLib.ARITH_TAC
QED

Theorem compact_pbc_to_npbc:
  compact (pbc_to_npbc c)
Proof
  Cases_on`c`>>rw[pbc_to_npbc_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  imp_res_tac compact_lhs_no_dup>>
  pop_assum mp_tac>>
  impl_tac>- (
    match_mp_tac QSORT_SORTED>>
    fs[transitive_term_le]>>
    simp[total_def]>>
    Cases>>Cases>>simp[])>>
  strip_tac>>
  CONJ_TAC>- (
    match_mp_tac normalize_lhs_compact1>>
    asm_exists_tac>>
    simp[sorted_map]>>
    qmatch_goalsub_abbrev_tac`_ tlt _`>>
    `tlt = term_lt` by
      simp[Abbr`tlt`,FUN_EQ_THM,FORALL_PROD]>>
    fs[])>>
  match_mp_tac normalize_lhs_compact2>>
  asm_exists_tac>>
  simp[]
QED

Theorem normalize_compact:
  EVERY compact (normalize pbf)
Proof
  simp[normalize_def,EVERY_MAP,compact_pbc_to_npbc]
QED

val _ = export_theory();
