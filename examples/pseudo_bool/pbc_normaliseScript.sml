(*
  Normalizes pbc into npbc
*)
Theory pbc_normalise
Libs
  preamble
Ancestors
  pbc npbc mllist mlmap mergesort

val _ = numLib.temp_prefer_num();

(* Normalization proceeds in three steps (for string variables):

  'a pbc -> string pbc (for graph encoders) ~> print out
  string pbc -> int pbc
  int pbc -> int pbc with ≥
  int pbc with ≥ -> npbc

  ----
  'a pbc -> 'a pbc with ≥ ~> print out
  'a pbc with ≥ -> string pbc (for graph encoders)


  There is a builtin string normalization using hashing for
  the supported characters, but this is (should be) unused
*)

(*
  Injective mapping from mlstring into num, supports

  a-z, A-Z, 0-9, []{}_^-$

*)
val non_list = (EVAL ``fromAList (MAP SWAP (enumerate 63 (MAP ORD (explode (strlit "[]{}_^-$")))))``);

Definition non_list_def:
  non_list = ^(rconc non_list)
End

Theorem non_list_eq = non_list_def |> SIMP_RULE std_ss [GSYM non_list];

Theorem lookup_non_list:
  sptree$lookup n non_list = SOME v ⇔
  SOME n = (ALOOKUP (enumerate 63 (MAP ORD (explode (strlit "[]{}_^-$")))) v)
Proof
  simp[non_list_eq,lookup_fromAList]>>
  EVAL_TAC>>rw[]
QED

Definition hashNon_def:
  hashNon n =
  case sptree$lookup n non_list of
    NONE => 0n
  | SOME v => v
End

Definition hashChar_def:
  hashChar c =
  let oc = ORD c in
  if 48 ≤ oc ∧ oc ≤ 57 (* char 0 to 9 hashes to 1-10 respectively *)
  then oc - 47
  else if 65 ≤ oc ∧ oc ≤ 90 (* char A to Z hashes to 11-36 *)
  then oc - 54
  else if 97 ≤ oc ∧ oc ≤ 122 (* char a to z hashes to 37-62 *)
  then oc - 60
  else hashNon oc
End

Definition hashChars_alt_def:
  (hashChars_alt [] = 0) ∧
  (hashChars_alt (c::cs) =
    hashChar c + 71 * hashChars_alt cs)
End

Definition hashString_def:
  hashString s = hashChars_alt (explode s)
End

(* Kind of a circular definition ... *)
Definition goodChar_def:
  goodChar c ⇔ hashChar c ≠ 0
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

Theorem goodString_eq_EVERY_goodChar:
  ∀s. goodString s ⇔ EVERY goodChar (explode s)
Proof
  Cases \\ fs [goodString_def]
  \\ qsuff_tac ‘∀s t. goodChars (STRLEN s) (strlit (s ++ t)) ⇔ EVERY goodChar s’
  >- metis_tac [APPEND_NIL]
  \\ Induct using SNOC_INDUCT
  >- (EVAL_TAC \\ fs [])
  \\ fs [goodChars_def,EVERY_SNOC]
  \\ rewrite_tac [SNOC_APPEND,GSYM APPEND_ASSOC,APPEND]
  \\ fs [EL_LENGTH_APPEND]
  \\ rw [] \\ eq_tac \\ rw []
QED

Theorem goodChar_toString:
  EVERY goodChar (case toString n1 of strlit x => x)
Proof
  Cases_on ‘toString n1’ \\ fs []
  \\ imp_res_tac mlintTheory.num_to_str_imp_cons
  \\ gvs [goodChar_def,EVERY_MEM]
  \\ rw [] \\ res_tac \\ fs []
  \\ fs [hashChar_def]
QED

Theorem hashChar_bound[local]:
  ∀h. hashChar h < 71
Proof
  rw [hashChar_def,hashNon_def,non_list_eq,lookup_fromAList]>>
  EVAL_TAC>>
  rw[]
QED

Theorem hashChar_11[local]:
  hashChar h <> 0 /\ hashChar h' <> 0 ==>
  (hashChar h = hashChar h' <=> h = h')
Proof
  rw [] \\ eq_tac \\ rw []
  \\ Cases_on ‘h’
  \\ Cases_on ‘h'’
  \\ fs []
  \\ rpt $ last_x_assum mp_tac
  \\ once_rewrite_tac [hashChar_def]
  \\ ntac 2 strip_tac
  \\ imp_res_tac ORD_CHR
  \\ asm_rewrite_tac []
  \\ simp_tac std_ss [LET_THM,hashNon_def]
  \\ rename [‘ORD (CHR m) = m’]
  \\ reverse (Cases_on `lookup n non_list`)
  >- (
    FULL_SIMP_TAC std_ss [lookup_non_list]>>
    pop_assum mp_tac>>
    qmatch_goalsub_abbrev_tac`_ ⇒ P`>>
    EVAL_TAC>>
    ntac 8 (IF_CASES_TAC>- (
      simp[]>>
      unabbrev_all_tac>>
      SIMP_TAC std_ss []>>
      rw[]>>fs[AllCaseEqs()]>>
      pop_assum mp_tac >> simp[lookup_non_list]>>
      EVAL_TAC>>rw[]))>>
    simp[])
  \\ reverse (Cases_on `lookup m non_list`)
  >- (
    FULL_SIMP_TAC std_ss [lookup_non_list]>>
    pop_assum mp_tac>>
    qmatch_goalsub_abbrev_tac`_ ⇒ P`>>
    EVAL_TAC>>
    ntac 8 (IF_CASES_TAC>- (
      simp[]>>
      unabbrev_all_tac>>
      SIMP_TAC std_ss []>>
      rw[]>>fs[AllCaseEqs()]>>
      pop_assum mp_tac >> simp[lookup_non_list]>>
      EVAL_TAC>>rw[]))>>
    simp[])
  \\ reverse $ Cases_on ‘48 <= n’ \\ asm_rewrite_tac []
  >-
   (Cases_on ‘48 <= m’ \\ asm_rewrite_tac []
    \\ rewrite_tac [AllCaseEqs()]
    \\ strip_tac \\ fs [])
  \\ reverse $ Cases_on ‘48 <= m’ \\ asm_rewrite_tac []
  >- (rewrite_tac [AllCaseEqs()] \\ strip_tac \\ fs [])
  \\ Cases_on ‘n <= 57’ \\ asm_rewrite_tac []
  >-
   (Cases_on ‘m <= 57’ \\ asm_rewrite_tac []
    \\ rewrite_tac [AllCaseEqs()]
    \\ strip_tac \\ fs [])
  \\ reverse $ Cases_on ‘m <= 57’ \\ asm_rewrite_tac []
  >- (rewrite_tac [AllCaseEqs()] \\ strip_tac \\ fs [])
  \\ fs []
QED

Theorem hashString_INJ:
  INJ hashString goodString UNIV
Proof
  rw[INJ_DEF,SPECIFICATION,hashString_def]
  \\ gs [goodString_eq_EVERY_goodChar]
  \\ Cases_on ‘x’ \\ Cases_on ‘y’ \\ fs []
  \\ rename [‘s = t’]
  \\ rpt $ pop_assum mp_tac
  \\ qid_spec_tac ‘t’
  \\ qid_spec_tac ‘s’
  \\ Induct
  \\ Cases_on ‘t’ \\ fs []
  >- fs [hashChars_alt_def,goodChar_def]
  >- fs [hashChars_alt_def,goodChar_def]
  \\ fs [hashChars_alt_def]
  \\ rpt gen_tac
  \\ rpt $ disch_then assume_tac
  \\ gvs []
  \\ rename [‘EVERY goodChar t’]
  \\ Cases_on ‘h = h'’ \\ fs []
  \\ qsuff_tac ‘hashChar h = hashChar h'’
  >- fs [hashChar_11,goodChar_def]
  \\ ‘(hashChar h' + 71 * hashChars_alt s) MOD 71 =
      (hashChar h + 71 * hashChars_alt t) MOD 71’ by metis_tac []
  \\ mp_tac arithmeticTheory.MOD_TIMES
  \\ once_rewrite_tac [ADD_COMM]
  \\ once_rewrite_tac [MULT_COMM]
  \\ strip_tac \\ full_simp_tac std_ss []
  \\ fs [hashChar_bound]
QED

Definition convert_pbf_def:
  convert_pbf pbf = MAP (map_pbc hashString) pbf
End

Theorem convert_pbf_satisfies:
  pbf_vars (set pbf) ⊆ goodString ⇒
  (satisfies w (set pbf) ⇔
    satisfies (w o LINV hashString goodString) (set (convert_pbf pbf)))
Proof
  rw[]>>
  `INJ hashString goodString UNIV` by
    metis_tac[hashString_INJ,SUBSET_REFL]>>
  simp[convert_pbf_def,LIST_TO_SET_MAP]>>
  rw[EQ_IMP_THM]
  >- (
    match_mp_tac satisfies_INJ>>
    simp[])>>
  drule satisfies_map_pbf>>
  match_mp_tac satisfies_pbf_vars>>
  rw[]>>fs[]>>
  drule LINV_DEF>>
  fs[pbf_vars_IMAGE,SUBSET_DEF]
QED

Theorem convert_pbf_satisfies_2:
  pbf_vars (set pbf) ⊆ goodString ⇒
  (satisfies w (set (convert_pbf pbf)) ⇔
  satisfies (w o hashString) (set pbf))
Proof
  rw[]>>
  simp[convert_pbf_def,LIST_TO_SET_MAP]>>
  rw[EQ_IMP_THM]
  >-
    metis_tac[satisfies_map_pbf]>>
  match_mp_tac satisfies_INJ_2>>
  simp[]>>
  match_mp_tac INJ_SUBSET>>
  first_x_assum (irule_at Any)>>
  metis_tac[hashString_INJ,SUBSET_REFL]
QED

Definition flip_coeffs_def:
  flip_coeffs xs = MAP (λ(c,l). (-c:int,l)) xs
End

(* Convert a list of pbc to one with ≥ constraints only *)
Definition pbc_ge_def:
  (pbc_ge ((GreaterEqual,xs,n):'a pbc) = [(GreaterEqual,xs,n)]) ∧
  (pbc_ge (Greater,xs,n) = [(GreaterEqual,xs,(n+1))]) ∧
  (pbc_ge (LessEqual,xs,n) = [(GreaterEqual,flip_coeffs xs,-n)]) ∧
  (pbc_ge (Less,xs,n) = [(GreaterEqual,flip_coeffs xs,-(n-1))]) ∧
  (pbc_ge (Equal,xs,n) =
      [(GreaterEqual,xs,n); (GreaterEqual,flip_coeffs xs,(-n))])
End

Theorem eq_disj:
  (∀x. x = a ∨ x = b ⇒ P x) ⇔ P a ∧ P b
Proof
  metis_tac[]
QED

Theorem eval_lin_term_flip_coeffs:
  ∀f.
  eval_lin_term w (flip_coeffs f) =
  -eval_lin_term w f
Proof
  Induct>>fs[eval_lin_term_def,iSUM_def,flip_coeffs_def]>>
  Cases_on`h`>>rw[]>>
  Cases_on`r`>>rw[]>>Cases_on`w a`>>rw[]>>
  intLib.ARITH_TAC
QED

Theorem pbc_ge_thm:
  satisfies w (set (pbc_ge c)) ⇔
  satisfies_pbc w c
Proof
  PairCases_on`c`>>
  rename1`(pbop,xs,n)`>>
  Cases_on`pbop`>>
  simp[pbc_ge_def,satisfies_def]
  >- ( (* Equal *)
    fs[satisfies_pbc_def,eq_disj,eval_lin_term_flip_coeffs]>>
    intLib.ARITH_TAC)
  >- ( (* Greater *)
    simp[satisfies_pbc_def]>>
    intLib.ARITH_TAC)
  >- ( (* LessEqual *)
    simp[satisfies_pbc_def,eval_lin_term_flip_coeffs]>>
    intLib.ARITH_TAC)
  >- ( (* Less*)
    simp[satisfies_pbc_def,eval_lin_term_flip_coeffs]>>
    intLib.ARITH_TAC)
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

Theorem iSUM_sort_term_le[simp]:
  iSUM (MAP (eval_term w) (sort $≤ l)) =
  iSUM (MAP (eval_term w) l)
Proof
  match_mp_tac iSUM_PERM>>
  match_mp_tac PERM_MAP>>
  metis_tac[sort_PERM,PERM_SYM]
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
  iSUM (MAP (pbc$eval_term w) xs) + n = iSUM (MAP (pbc$eval_term w) xs') + n'
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

Definition normalise_lhs_def:
  (normalise_lhs [] acc n = (REVERSE acc,n)) ∧
  (normalise_lhs ((x,l)::xs) acc n =
    let v = lit_var l in
    if x < 0 then
      normalise_lhs xs ((mk_coeff x l,v)::acc) (n+x)
    else if x > 0 then normalise_lhs xs ((mk_coeff x l,v)::acc) n
    else normalise_lhs xs acc n)
End

Theorem normalise_lhs_normalises:
  ∀ls acc n ls' n'.
  normalise_lhs ls acc n = (ls',n') ⇒
  iSUM (MAP (pbc$eval_term w) ls) + &(SUM (MAP (eval_term w) acc)) + n =
  &(SUM (MAP (eval_term w) ls')) + n'
Proof
  Induct>>rw[normalise_lhs_def,iSUM_def]
  >-
    metis_tac[SUM_REVERSE,MAP_REVERSE] >>
  Cases_on`h`>>fs[normalise_lhs_def]>>
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
  (pbc_to_npbc (GreaterEqual,lhs,n) =
    let (lhs',m') = compact_lhs (sort term_le lhs) 0 in
    let (lhs'',m'') = normalise_lhs lhs' [] 0 in
    let rhs = n-(m'+m'') in
    (lhs'',rhs):npbc) ∧
  (pbc_to_npbc _ = ([],0))
End

Definition normalise_def:
  normalise pbf =
  let pbf' = FLAT (MAP pbc_ge pbf) in
  MAP pbc_to_npbc pbf'
End

Theorem pbc_to_npbc_thm:
  FST pbc = GreaterEqual ⇒
  (satisfies_pbc w pbc ⇔ satisfies_npbc w (pbc_to_npbc pbc))
Proof
  PairCases_on`pbc`>>fs[]>>
  rw[satisfies_pbc_def,satisfies_npbc_def,pbc_to_npbc_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  drule compact_lhs_sound>>
  disch_then(qspec_then`w` assume_tac)>>fs[eval_lin_term_def]>>
  drule normalise_lhs_normalises>>
  disch_then(qspec_then`w` assume_tac)>>fs[]>>
  simp[satisfies_npbc_def]>>
  intLib.ARITH_TAC
QED

Theorem normalise_thm:
  satisfies w (set (normalise pbf)) ⇔
  satisfies w (set pbf)
Proof
  simp[normalise_def]>>
  qmatch_goalsub_abbrev_tac`MAP _ pbf'`>>
  `satisfies w (set pbf) ⇔ satisfies w (set pbf')` by
    (simp[Abbr`pbf'`]>>
    Induct_on`pbf`>>
    simp[]>>
    metis_tac[pbc_ge_thm])>>
  simp[]>>
  `!x. MEM x pbf' ⇒ FST x = GreaterEqual` by
    (simp[Abbr`pbf'`,MEM_FLAT,MEM_MAP,PULL_EXISTS]>>
    rw[]>>
    PairCases_on`y`>>Cases_on`y0`>>fs[pbc_ge_def])>>
  pop_assum mp_tac>>
  rpt(pop_assum kall_tac)>>
  Induct_on`pbf'`>>simp[]>>
  rw[]>>
  metis_tac[pbc_to_npbc_thm]
QED

Definition full_normalise_def:
  full_normalise pbf = normalise (convert_pbf pbf)
End

Theorem full_normalise_satisfies:
  pbf_vars (set pbf) ⊆ goodString ⇒
  (satisfies w (set pbf) ⇔
  satisfies (w ∘ LINV hashString goodString) (set (full_normalise pbf)))
Proof
  rw[full_normalise_def,normalise_thm]>>
  metis_tac[convert_pbf_satisfies]
QED

Theorem full_normalise_satisfies_2:
  pbf_vars (set pbf) ⊆ goodString ⇒
  (satisfies w (set (full_normalise pbf)) ⇔
  satisfies (w o hashString) (set pbf))
Proof
  rw[full_normalise_def,normalise_thm]>>
  metis_tac[convert_pbf_satisfies_2]
QED

Theorem full_normalise_unsatisfiable:
  pbf_vars (set pbf) ⊆ goodString ⇒
  (unsatisfiable (set (full_normalise pbf)) ⇔
  unsatisfiable (set pbf))
Proof
  rw[pbcTheory.unsatisfiable_def,npbcTheory.unsatisfiable_def]>>
  fs[pbcTheory.satisfiable_def,npbcTheory.satisfiable_def]>>
  metis_tac[full_normalise_satisfies,full_normalise_satisfies_2]
QED

Theorem lit_var_negate[simp]:
  lit_var (negate r) = lit_var r
Proof
  Cases_on`r`>>simp[]
QED

Theorem normalise_lhs_compact1:
  ∀lhs acc n lhs' n'.
  normalise_lhs lhs acc n = (lhs',n') ∧
  SORTED $< (MAP SND (REVERSE acc) ++ MAP (lit_var o SND) lhs) ⇒
  SORTED $< (MAP SND lhs')
Proof
  Induct>>simp[normalise_lhs_def]>>
  Cases>>simp[normalise_lhs_def]>>rw[]>>
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

Theorem normalise_lhs_compact2:
  ∀lhs acc n lhs' n'.
  normalise_lhs lhs acc n = (lhs',n') ∧
  EVERY (λc. c ≠ 0) (MAP FST acc) ⇒
  EVERY (λc. c ≠ 0) (MAP FST lhs')
Proof
  Induct>>simp[normalise_lhs_def]
  >-
    simp[EVERY_MAP]>>
  Cases>>fs[normalise_lhs_def]>>rw[]>>
  first_x_assum match_mp_tac>>
  asm_exists_tac>>fs[]>>
  Cases_on`r`>>fs[mk_coeff_def]>>
  intLib.ARITH_TAC
QED

Theorem compact_pbc_to_npbc:
  compact (pbc_to_npbc c)
Proof
  PairCases_on`c`>>Cases_on`c0`>>
  rw[pbc_to_npbc_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  imp_res_tac compact_lhs_no_dup>>
  pop_assum mp_tac>>
  impl_tac>- (
    match_mp_tac sort_SORTED>>
    fs[transitive_term_le]>>
    simp[total_def]>>
    Cases>>Cases>>simp[])>>
  strip_tac>>
  CONJ_TAC>- (
    match_mp_tac normalise_lhs_compact1>>
    asm_exists_tac>>
    simp[sorted_map]>>
    qmatch_goalsub_abbrev_tac`_ tlt _`>>
    `tlt = term_lt` by
      simp[Abbr`tlt`,FUN_EQ_THM,FORALL_PROD]>>
    fs[])>>
  match_mp_tac normalise_lhs_compact2>>
  asm_exists_tac>>
  simp[]
QED

Theorem normalise_compact:
  EVERY compact (normalise pbf)
Proof
  simp[normalise_def,EVERY_MAP,compact_pbc_to_npbc]
QED

Theorem full_normalise_optimal_val:
  pbf_vars (set pbf) ⊆ goodString ∧
  set (MAP (lit_var ∘ SND) f) ⊆ goodString ∧
  normalise_lhs
    (MAP (λ(a,b). (a, map_lit hashString b)) f) [] 0 = (f',m') ⇒
    optimal_val (set (full_normalise pbf)) (SOME (f',m'+c)) =
    optimal_val (set pbf) (f,c)
Proof
  reverse (rw[optimal_val_def])
  >- (
    fs[pbcTheory.optimal_val_def,satisfiable_def,pbcTheory.satisfiable_def]>>
    metis_tac[full_normalise_satisfies])>>
  qmatch_goalsub_abbrev_tac`eval_obj _ w`>>
  qsuff_tac `optimal (w o hashString) (set pbf) f`
  >- (
    drule normalise_lhs_normalises>>
    simp[GSYM eval_lin_term_def,eval_lin_term_MAP]>>
    rw[]>>drule optimal_optimal_val>>
    simp[eval_obj_def,integerTheory.INT_ADD_ASSOC])>>
  `optimal w (set (full_normalise pbf)) (SOME (f',m'+c))` by
    (fs[satisfiable_def]>>
    imp_res_tac optimal_exists>>
    simp[Abbr`w`]>>
    metis_tac[SELECT_AX])>>
  qpat_x_assum`Abbrev _` kall_tac>>
  fs[optimal_def,pbcTheory.optimal_def]>>
  CONJ_TAC
  >- (
    drule full_normalise_satisfies_2>>
    metis_tac[])>>
  rw[]>>
  drule normalise_lhs_normalises>>
  simp[GSYM eval_lin_term_def,eval_lin_term_MAP]>>
  rw[]>>
  drule full_normalise_satisfies>>
  disch_then(qspec_then `w'` assume_tac)>>fs[]>>
  first_x_assum drule>>
  qmatch_goalsub_abbrev_tac`_ <= eval_obj _ ww`>>
  first_x_assum(qspec_then`ww` mp_tac)>>
  qsuff_tac` eval_lin_term (ww ∘ hashString) f = eval_lin_term w' f`
  >-
    simp[eval_obj_def]>>
  simp[Abbr`ww`]>>
  simp[eval_lin_term_def]>>
  AP_TERM_TAC>>
  qpat_x_assum`_ ⊆ goodString` mp_tac>>
  simp[MAP_EQ_f,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
  rw[]>>
  first_x_assum drule>>
  Cases_on`e`>>simp[]>>
  rw[]>>
  `INJ hashString goodString UNIV` by
    metis_tac[hashString_INJ,SUBSET_REFL]>>
  drule LINV_DEF>>
  Cases_on`r`>>fs[]
QED

(*--------------------------------------------------------------*
   converting α pbc into num pbc
 *--------------------------------------------------------------*)

Datatype:
  name_to_num_state =
    <| to_num : (('a, num) mlmap$map) num_map
     ; to_str : 'a num_map
     ; hash_fun : 'a -> num
     ; cmp_name : 'a -> 'a -> ordering
     ; next_num : num |>
End

Definition init_state_def:
  init_state hf cmp =
    <| to_num := LN
     ; to_str := LN
     ; hash_fun := hf
     ; cmp_name := cmp
     ; next_num := 0 |>
End

Definition mk_map_def:
  mk_map s v n = insert (mlmap$empty s.cmp_name) v (n:num)
End

Definition name_to_num_var_def:
  name_to_num_var (v:'a) (s:'a name_to_num_state) =
    let h = s.hash_fun v in
      case sptree$lookup h s.to_num of
      | NONE =>
          (s.next_num,
           s with <| to_num := insert h (mk_map s v s.next_num) s.to_num ;
                     to_str := insert s.next_num v s.to_str ;
                     next_num := s.next_num + 1 |>)
      | SOME m =>
          case mlmap$lookup m v of
          | SOME index => (index,s)
          | NONE =>
              (s.next_num,
               s with <| to_num := insert h (mlmap$insert m v s.next_num) s.to_num ;
                         to_str := insert s.next_num v s.to_str ;
                         next_num := s.next_num + 1 |>)
End

Definition name_to_num_lit_def:
  name_to_num_lit (Pos v) s = (let (v1,s1) = name_to_num_var v s in (Pos v1,s1)) ∧
  name_to_num_lit (Neg v) s = (let (v1,s1) = name_to_num_var v s in (Neg v1,s1))
End

Definition name_to_num_lin_term_def:
  name_to_num_lin_term [] s acc = (REVERSE acc,s) ∧
  name_to_num_lin_term ((i,l)::xs) s acc =
    let (l1,s1) = name_to_num_lit l s in
      name_to_num_lin_term xs s1 ((i,l1)::acc)
End

Definition name_to_num_pbf_def:
  name_to_num_pbf [] s acc = (REVERSE acc,s) ∧
  name_to_num_pbf ((p,l,i)::xs) s acc =
    let (l1,s1) = name_to_num_lin_term l s [] in
      name_to_num_pbf xs s1 ((p,l1,i)::acc)
End

(* ---- verification ---- *)

Definition lookup_index_def:
  lookup_index s v =
    let h = s.hash_fun v in
      case sptree$lookup h s.to_num of
      | NONE => NONE
      | SOME m => mlmap$lookup m v
End

Definition lookup_name_def:
  lookup_name s n = sptree$lookup n s.to_str
End

Definition name_to_num_state_ok_def:
  name_to_num_state_ok s ⇔
    TotOrd s.cmp_name ∧
    (∀h m.
       lookup h s.to_num = SOME m ⇒
       map_ok m ∧
       ∀name index.
         lookup m name = SOME index ⇒
         s.hash_fun name = h ∧ index < s.next_num) ∧
    (∀name index.
       lookup_name s index = SOME name ⇔ lookup_index s name = SOME index)
End

Theorem lookup_name_inj:
  name_to_num_state_ok s ∧
  lookup_name s index1 = SOME name ∧
  lookup_name s index2 = SOME name ⇒
  index1 = index2
Proof
  fs [name_to_num_state_ok_def] \\ rw [] \\ gvs []
QED

Theorem lookup_index_inj:
  name_to_num_state_ok s ∧
  lookup_index s name1 = SOME index ∧
  lookup_index s name2 = SOME index ⇒
  name1 = name2
Proof
  fs [name_to_num_state_ok_def] \\ metis_tac [SOME_11]
QED

Theorem init_state_ok:
  TotOrd cmp ⇒
  name_to_num_state_ok (init_state hf cmp)
Proof
  fs [name_to_num_state_ok_def,init_state_def,lookup_name_def,lookup_index_def]
QED

Theorem name_to_num_var_thm:
  name_to_num_state_ok s ∧
  name_to_num_var v s = (index,s1)
  ⇒
  name_to_num_state_ok s1 ∧
  lookup_name s1 index = SOME v ∧
  lookup_index s1 v = SOME index ∧
  (∀w i. lookup_index s w = SOME i ⇒ lookup_index s1 w = SOME i)
Proof
  fs [name_to_num_var_def,AllCaseEqs()]
  \\ reverse strip_tac \\ gvs []
  >-
   (conj_asm2_tac >- fs [name_to_num_state_ok_def]
    \\ fs [lookup_name_def,lookup_index_def])
  >-
   (fs [lookup_index_def,lookup_name_def,AllCaseEqs(),
        sptreeTheory.lookup_insert,PULL_EXISTS]
    \\ gvs [name_to_num_state_ok_def] \\ res_tac
    \\ gvs [mlmapTheory.lookup_insert,lookup_index_def,lookup_name_def,
            sptreeTheory.lookup_insert,AllCaseEqs()]
    \\ rw [] \\ gvs [insert_thm,lookup_insert]
    \\ gvs [AllCaseEqs()]
    \\ res_tac \\ fs []
    >-
     (Cases_on ‘v = name’ \\ gvs []
      \\ gvs [insert_thm,lookup_insert]
      \\ Cases_on ‘s.hash_fun name = s.hash_fun v’ \\ gvs []
      \\ gvs [insert_thm,lookup_insert]
      \\ Cases_on ‘lookup m name’ \\ gvs [] \\ res_tac \\ fs []
      \\ Cases_on ‘lookup (s.hash_fun name) s.to_num’ \\ gvs []
      \\ Cases_on ‘lookup x name’ \\ gvs [] \\ res_tac \\ fs [])
    \\ Cases_on ‘s.hash_fun w = s.hash_fun v’ \\ gvs []
    \\ rw [] \\ gvs [insert_thm,lookup_insert]
    \\ rw [] \\ gvs [])
  \\ gvs [mk_map_def]
  \\ qpat_abbrev_tac ‘x = empty s.cmp_name’
  \\ ‘map_ok x ∧ ∀n. lookup x n = NONE’ by
    (unabbrev_all_tac
     \\ gvs [empty_thm,name_to_num_state_ok_def]
     \\ EVAL_TAC \\ fs [])
  \\ unabbrev_all_tac
  \\ fs [lookup_index_def,lookup_name_def,AllCaseEqs(),
         sptreeTheory.lookup_insert,PULL_EXISTS,mk_map_def]
  \\ gvs [name_to_num_state_ok_def] \\ res_tac
  \\ gvs [mlmapTheory.lookup_insert,lookup_index_def,lookup_name_def,
          sptreeTheory.lookup_insert,AllCaseEqs()]
  \\ rw [] \\ gvs [insert_thm,lookup_insert]
  \\ res_tac \\ fs []
  >- (Cases_on ‘v = name’ \\ gvs []
      \\ gvs [insert_thm,lookup_insert]
      \\ Cases_on ‘s.hash_fun name = s.hash_fun v’ \\ gvs []
      \\ gvs [insert_thm,lookup_insert]
      \\ Cases_on ‘lookup (s.hash_fun name) s.to_num’ \\ gvs []
      \\ Cases_on ‘lookup x name’ \\ gvs [] \\ res_tac \\ fs [])
  \\ Cases_on ‘s.hash_fun w = s.hash_fun v’ \\ gvs []
  \\ rw [] \\ gvs [insert_thm,lookup_insert]
QED

Definition map_lin_term_def:
  map_lin_term f xs = MAP (λ(a,b). (a,map_lit f b)) xs
End

Theorem name_to_num_lit:
  ∀x (s:'a name_to_num_state) y t.
    name_to_num_lit x s = (y,t) ∧ name_to_num_state_ok s
    ⇒
    name_to_num_state_ok t  ∧
    y = map_lit (THE o lookup_index t) x ∧
    (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
    lit_var x ∈ { i | lookup_index t i ≠ NONE }
Proof
  Cases \\ fs [name_to_num_lit_def]
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule_all name_to_num_var_thm
  \\ strip_tac \\ gvs [map_lit_def]
QED

Theorem name_to_num_lin_term:
  ∀xs (s:'a name_to_num_state) zs acc ys t.
    name_to_num_lin_term xs s acc = (ys,t) ∧ name_to_num_state_ok s ∧
    acc = map_lin_term (THE o lookup_index s) zs ∧
    set (MAP (lit_var ∘ SND) zs) ⊆ { i | lookup_index s i ≠ NONE }
    ⇒
    name_to_num_state_ok t  ∧
    ys = REVERSE acc ++ map_lin_term (THE o lookup_index t) xs ∧
    (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
    set (MAP (lit_var ∘ SND) xs) ⊆ { i | lookup_index t i ≠ NONE }
Proof
  Induct
  \\ gvs [name_to_num_lin_term_def,map_lin_term_def,FORALL_PROD]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule name_to_num_lit
  \\ strip_tac \\ gvs []
  \\ last_x_assum $ qspecl_then [‘s1’,‘(p_1,p_2)::zs’] mp_tac \\ fs []
  \\ ‘MAP (λ(a,b). (a,map_lit (THE ∘ lookup_index s) b)) zs =
      MAP (λ(a,b). (a,map_lit (THE ∘ lookup_index s1) b)) zs’ by
    (gvs [MAP_EQ_f,FORALL_PROD,map_lit_def] \\ rw []
     \\ gvs [SUBSET_DEF,MEM_MAP,PULL_EXISTS]
     \\ res_tac \\ fs []
     \\ rename [‘lit_var v’]
     \\ Cases_on ‘lookup_index s1 (lit_var v)’ \\ gvs []
     \\ res_tac \\ gvs []
     \\ Cases_on ‘v’ \\ gvs [map_lit_def]
     \\ res_tac \\ fs []
     \\ Cases_on ‘lookup_index s a’ \\ gvs []
     \\ res_tac \\ gvs [])
  \\ fs []
  \\ impl_tac >-
   (irule SUBSET_TRANS
    \\ first_x_assum $ irule_at Any
    \\ fs [SUBSET_DEF]
    \\ strip_tac \\ Cases_on ‘lookup_index s x’ \\ gvs [] \\ res_tac \\ fs [])
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘lookup_index s1 (lit_var p_2)’ \\ gvs []
  \\ res_tac \\ fs []
  \\ Cases_on ‘p_2’ \\ gvs [map_lit_def]
  \\ res_tac \\ fs []
QED

Theorem name_to_num_pbf_rec:
  ∀xs (s:'a name_to_num_state) zs acc ys t.
    name_to_num_pbf xs s acc = (ys,t) ∧ name_to_num_state_ok s ∧
    acc = MAP (map_pbc (THE o lookup_index s)) zs ∧
    pbf_vars (set zs) ⊆ { i | lookup_index s i ≠ NONE }
    ⇒
    name_to_num_state_ok t  ∧
    ys = REVERSE acc ++ MAP (map_pbc (THE o lookup_index t)) xs ∧
    (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
    pbf_vars (set xs) ⊆ { i | lookup_index t i ≠ NONE }
Proof
  Induct
  \\ fs [name_to_num_pbf_def,FORALL_PROD]
  >- fs [pbf_vars_def,GSYM MAP_REVERSE]
  \\ fs [map_pbc_def]
  \\ rpt gen_tac
  \\ strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule name_to_num_lin_term
  \\ gvs [map_lin_term_def]
  \\ strip_tac \\ gvs []
  \\ rename [‘pbf_vars ((p1,p2,p3) INSERT set xs) ⊆ _’]
  \\ last_x_assum $ qspecl_then [‘s1’,‘(p1,p2,p3)::zs’] mp_tac
  \\ fs [map_pbc_def]
  \\ ‘MAP (map_pbc (THE ∘ lookup_index s)) zs =
      MAP (map_pbc (THE ∘ lookup_index s1)) zs’ by
    (gvs [MAP_EQ_f,FORALL_PROD] \\ rw []
     \\ fs [map_pbc_def,MAP_EQ_f,FORALL_PROD]
     \\ gvs [pbf_vars_def,pbc_vars_def,SUBSET_DEF,PULL_EXISTS]
     \\ gvs [pbc_vars_def,FORALL_PROD,MEM_MAP,PULL_EXISTS]
     \\ rw [] \\ res_tac
     \\ rename [‘lit_var v’]
     \\ Cases_on ‘lookup_index s (lit_var v)’ \\ gvs []
     \\ res_tac \\ gvs []
     \\ Cases_on ‘v’ \\ gvs [map_lit_def]
     \\ res_tac \\ fs [])
  \\ gvs []
  \\ ‘{i | lookup_index s i ≠ NONE} ⊆ {i | lookup_index s1 i ≠ NONE}’ by
     (gvs [SUBSET_DEF] \\ strip_tac
      \\ Cases_on ‘lookup_index s x’ \\ gvs [] \\ res_tac \\ fs [])
  \\ impl_tac
  >- (gvs [pbf_vars_def,pbc_vars_def] \\ imp_res_tac SUBSET_TRANS)
  \\ strip_tac \\ gvs []
  \\ ‘{i | lookup_index s1 i ≠ NONE} ⊆ {i | lookup_index t i ≠ NONE}’ by
     (gvs [SUBSET_DEF] \\ strip_tac
      \\ Cases_on ‘lookup_index s1 x’ \\ gvs [] \\ res_tac \\ fs [])
  \\ reverse conj_tac
  >- (gvs [pbf_vars_def,pbc_vars_def] \\ imp_res_tac SUBSET_TRANS \\ gvs [])
  \\ gvs [MAP_EQ_f,FORALL_PROD] \\ rw []
  \\ fs [map_pbc_def,MAP_EQ_f,FORALL_PROD]
  \\ gvs [pbf_vars_def,pbc_vars_def,SUBSET_DEF,PULL_EXISTS]
  \\ gvs [pbc_vars_def,FORALL_PROD,MEM_MAP,PULL_EXISTS]
  \\ rw [] \\ res_tac
  \\ rename [‘lit_var v’]
  \\ Cases_on ‘lookup_index s1 (lit_var v)’ \\ gvs []
  \\ res_tac \\ gvs []
  \\ Cases_on ‘v’ \\ gvs [map_lit_def]
  \\ res_tac \\ fs []
QED

Theorem name_to_num_pbf_thm:
  ∀(xs: α pbc list) (ys: num pbc list) s t.
    name_to_num_pbf xs s [] = (ys,t) ∧ name_to_num_state_ok s ⇒
    satisfiable (set xs) =
    satisfiable (set ys)
Proof
  rpt gen_tac \\ fs [pbcTheory.satisfiable_def]
  \\ strip_tac
  \\ drule_then drule name_to_num_pbf_rec \\ fs []
  \\ impl_tac
  >- fs [pbf_vars_def]
  \\ strip_tac \\ gvs [MAP_REVERSE]
  \\ eq_tac \\ fs [] \\ strip_tac
  >-
   (drule_at (Pos $ el 2) (satisfies_INJ |> INST_TYPE [“:'b”|->“:num”])
    \\ disch_then $ drule_at Any
    \\ fs [LIST_TO_SET_MAP]
    \\ disch_then $ irule_at Any
    \\ gvs [INJ_DEF]
    \\ rpt gen_tac
    \\ Cases_on ‘lookup_index t x’ \\ gvs []
    \\ Cases_on ‘lookup_index t y’ \\ gvs []
    \\ rw [] \\ metis_tac [lookup_index_inj])
  \\ fs [LIST_TO_SET_MAP]
  \\ drule_at (Pos last) (satisfies_INJ |> INST_TYPE [“:'a”|->“:num”,“:'b”|->“:'a”]
                                        |> Q.GEN ‘s’)
  \\ qabbrev_tac ‘f = THE ∘ lookup_name t’
  \\ disch_then $ qspec_then ‘f’ mp_tac
  \\ disch_then $ qspec_then ‘{i | lookup_name t i ≠ NONE}’ mp_tac
  \\ impl_tac
  >-
   (conj_tac
    >- (gvs [INJ_DEF]
        \\ rpt gen_tac
        \\ Cases_on ‘lookup_name t x’ \\ gvs []
        \\ Cases_on ‘lookup_name t y’ \\ gvs []
        \\ gvs [Abbr‘f’]
        \\ rw [] \\ metis_tac [lookup_name_inj])
    \\ gvs [pbf_vars_def,SUBSET_DEF,PULL_EXISTS,pbc_vars_map_pbc]
    \\ rw [] \\ res_tac
    \\ rename [‘lookup_index t a ≠ NONE’]
    \\ Cases_on ‘lookup_index t a’ \\ gvs []
    \\ gvs [name_to_num_state_ok_def]
    \\ res_tac \\ fs [])
  \\ fs [IMAGE_IMAGE]
  \\ fs [GSYM LIST_TO_SET_MAP]
  \\ ‘MAP (map_pbc f ∘ map_pbc (THE ∘ lookup_index t)) xs = xs’
        by (fs [MAP_EQ_ID,map_pbc_o] \\ rw []
            \\ irule map_pbc_I \\ fs [SUBSET_DEF]
            \\ rw [Abbr‘f’]
            \\ rename [‘a ∈ pbc_vars x’]
            \\ ‘lookup_index t a ≠ NONE’ by
             (first_x_assum irule
              \\ gvs [pbf_vars_def,PULL_EXISTS] \\ metis_tac [])
            \\ Cases_on ‘lookup_index t a’ \\ gvs [name_to_num_state_ok_def]
            \\ res_tac \\ fs [])
  \\ fs [] \\ disch_then $ irule_at Any
QED

Definition name_to_num_obj_def:
  (name_to_num_obj NONE s = (NONE,s)) ∧
  (name_to_num_obj (SOME (f,c)) s =
    let (f',t) = name_to_num_lin_term f s [] in
    (SOME(f',c),t))
End

Definition name_to_num_list_def:
  name_to_num_list [] s acc = (REVERSE acc,s) ∧
  name_to_num_list (v::xs) s acc =
    let (v1,s1) = name_to_num_var v s in
      name_to_num_list xs s1 (v1::acc)
End

Definition name_to_num_pres_def:
  (name_to_num_pres NONE s = (NONE,s)) ∧
  (name_to_num_pres (SOME pres) s =
    let (pres',s') = name_to_num_list pres s [] in
    (SOME pres',s'))
End

Definition name_to_num_prob_def:
  name_to_num_prob (pres,obj,fml) s =
  let (pres',s') = name_to_num_pres pres s in
  let (obj',s'') = name_to_num_obj obj s' in
  let (fml',s''') = name_to_num_pbf fml s'' [] in
    ((pres',obj',fml'),s''')
End

Theorem name_to_num_obj:
  name_to_num_obj obj s = (obj',t) ∧
  name_to_num_state_ok s
  ⇒
  name_to_num_state_ok t  ∧
  obj' = map_obj (THE o lookup_index t) obj ∧
  (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
  obj_vars obj ⊆ { i | lookup_index t i ≠ NONE }
Proof
  Cases_on`obj`
  >-
    (rw[]>>gvs[name_to_num_obj_def,map_obj_def,obj_vars_def])>>
  strip_tac>>
  Cases_on`x`>>fs[name_to_num_obj_def]>>
  pairarg_tac>>gvs[]>>
  drule name_to_num_lin_term>>
  simp[]>>
  disch_then(qspec_then`[]` mp_tac)>>
  impl_tac>-
    simp[map_lin_term_def]>>
  strip_tac>>simp[obj_vars_def,map_obj_def,map_lin_term_def]
QED

Theorem name_to_num_list:
  ∀xs (s:'a name_to_num_state) zs acc ys t.
    name_to_num_list xs s acc = (ys,t) ∧
    name_to_num_state_ok s ∧
    acc = MAP (THE o lookup_index s) zs ∧
    set zs ⊆ { i | lookup_index s i ≠ NONE }
    ⇒
    name_to_num_state_ok t  ∧
    ys = REVERSE acc ++ MAP (THE o lookup_index t) xs ∧
    (∀i n. lookup_index s i = SOME n ⇒
      lookup_index t i = SOME n) ∧
    set xs ⊆ { i | lookup_index t i ≠ NONE }
Proof
  Induct
  \\ gvs [name_to_num_list_def]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt (pairarg_tac \\ gvs [])
  \\ drule name_to_num_var_thm
  \\ disch_then drule \\ simp[]
  \\ strip_tac \\ gvs []
  \\ last_x_assum $ qspecl_then [‘s1’,‘h::zs’] mp_tac
  \\ fs []
  \\ ‘MAP (THE ∘ lookup_index s) zs =
      MAP (THE ∘ lookup_index s1) zs’ by (
     gvs [MAP_EQ_f,FORALL_PROD,map_lit_def] \\ rw []
     \\ gvs [SUBSET_DEF,MEM_MAP,PULL_EXISTS]
     \\ first_x_assum drule
     \\ rename [‘lookup_index s v’]
     \\ Cases_on`lookup_index s v` \\ gvs[]
     \\ metis_tac[THE_DEF] )
  \\ fs []
  \\ impl_tac >- (
    irule SUBSET_TRANS
    \\ first_x_assum $ irule_at Any
    \\ fs [SUBSET_DEF]
    \\ strip_tac
    \\ Cases_on ‘lookup_index s x’
    \\ gvs [] \\ res_tac \\ fs [])
  \\ strip_tac \\ gvs []
  \\ Cases_on ‘lookup_index s1 h’ \\ gvs []
  \\ res_tac \\ fs []
QED

Theorem name_to_num_pres:
  name_to_num_pres pres s = (pres',t) ∧
  name_to_num_state_ok s
  ⇒
  name_to_num_state_ok t  ∧
  pres' = OPTION_MAP (MAP (THE o lookup_index t)) pres ∧
  (∀i n. lookup_index s i = SOME n ⇒ lookup_index t i = SOME n) ∧
  pres_set_list pres ⊆ { i | lookup_index t i ≠ NONE }
Proof
  Cases_on`pres`
  >- (
    rw[]>>
    gvs[name_to_num_pres_def,pres_set_list_def])>>
  strip_tac>>
  fs[name_to_num_pres_def]>>
  pairarg_tac>>gvs[]>>
  drule name_to_num_list>>
  simp[pres_set_list_def]
QED

Definition normalise_obj_def:
  (normalise_obj NONE = NONE) ∧
  (normalise_obj (SOME (f,c)) =
    let (f',c') = compact_lhs (sort term_le f) 0 in
    let (f'', c'') = normalise_lhs f' [] 0 in
    SOME (f'',c + c'+c''))
End

Definition normalise_obj_pbf_def:
  normalise_obj_pbf (obj,fml) =
  (normalise_obj obj,
  normalise fml)
End

Definition normalise_prob_def:
  normalise_prob (x,objf) =
    (OPTION_MAP list_to_num_set x,normalise_obj_pbf objf)
End

Theorem eval_obj_normalise_obj:
  eval_obj (normalise_obj obj) w = eval_obj obj w
Proof
  Cases_on`obj`>>
  simp[normalise_obj_def,eval_obj_def,pbcTheory.eval_obj_def]>>
  Cases_on`x`>>
  simp[normalise_obj_def,eval_lin_term_def]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  drule normalise_lhs_normalises>>
  simp[]>>
  disch_then(qspec_then`w` assume_tac)>>
  drule compact_lhs_sound>>
  disch_then(qspec_then`w` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem satisfiable_normalise:
  satisfiable(set fml) ⇔
  satisfiable(set (normalise fml))
Proof
  fs[pbcTheory.satisfiable_def,satisfiable_def]>>
  metis_tac[normalise_thm]
QED

Theorem normalise_prob_sem_concl:
  normalise_prob (pres,obj,fml) = (pres',obj',fml') ⇒
  sem_concl (set fml) obj concl = sem_concl (set fml') obj' concl
Proof
  Cases_on`concl`>>
  rw[normalise_prob_def,normalise_obj_pbf_def,sem_concl_def,pbcTheory.sem_concl_def,satisfiable_normalise,pbcTheory.unsatisfiable_def,unsatisfiable_def,eval_obj_normalise_obj,normalise_thm]>>
  simp[satisfiable_normalise,eval_obj_normalise_obj,normalise_thm]
QED

Theorem pres_set_spt_pres_set_list:
  pres_set_spt (OPTION_MAP list_to_num_set pres) =
  pres_set_list pres
Proof
  Cases_on`pres`>>simp[pres_set_list_def,pres_set_spt_def]>>
  simp[EXTENSION,domain_list_to_num_set]
QED

Theorem normalise_prob_sem_output:
  normalise_prob (pres1,obj1,fml1) = (pres1',obj1',fml1') ∧
  normalise_prob (pres2,obj2,fml2) = (pres2',obj2',fml2') ⇒
  (pbc$sem_output (set fml1) obj1 (pres_set_list pres1) bound (set fml2) obj2 (pres_set_list pres2) output ⇔
  npbc$sem_output (set fml1') obj1' (pres_set_spt pres1') bound (set fml2') obj2' (pres_set_spt pres2') output)
Proof
  Cases_on`output`>>
  rw[npbcTheory.sem_output_def,pbcTheory.sem_output_def,normalise_prob_def,normalise_obj_pbf_def]>>
  simp[satisfiable_normalise,eval_obj_normalise_obj,normalise_thm,pres_set_spt_pres_set_list]
QED

Theorem name_to_num_prob_concl_thm:
  ∀concl
    (fml: α pbc list) (fml': num pbc list)
    (obj : (α lin_term # int) option)
    (obj': (num lin_term # int) option)
    (pres : α list option)
    (pres' : num list option)
    s t.
    name_to_num_prob (pres,obj,fml) s = ((pres',obj',fml'),t) ∧
    name_to_num_state_ok s ⇒
    sem_concl (set fml) obj concl = sem_concl (set fml') obj' concl
Proof
  rw[name_to_num_prob_def]>>
  rpt(pairarg_tac>>gvs[])>>
  drule_all name_to_num_pres>> rw[]>>
  drule_all name_to_num_obj>>rw[]>>
  drule_then drule name_to_num_pbf_rec \\ fs []
  \\ impl_tac
  >- fs [pbf_vars_def]>>
  rw[]>>
  simp[LIST_TO_SET_MAP]>>
  rename1`name_to_num_pres _ _ = (_, s1)`>>
  rename1`name_to_num_obj _ _ = (_, s2)`>>
  rename1`name_to_num_pbf _ _ _ = (_, s3)`>>
  `obj_vars obj ⊆ {i | lookup_index s3 i ≠ NONE}` by (
    Cases_on`obj`>>fs[obj_vars_def]>>
    Cases_on`x`>>fs[obj_vars_def,SUBSET_DEF]>>
    rw[]>>first_x_assum drule>>
    metis_tac[option_CLAUSES])>>
  `map_obj (THE o lookup_index s2) obj =
   map_obj (THE o lookup_index s3) obj` by (
    Cases_on`obj`>>
    simp[map_obj_def]>>
    Cases_on`x`>>
    fs[map_obj_def,obj_vars_def]>>
    fs[MAP_EQ_f,FORALL_PROD,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
    rw[]>>first_x_assum drule>>
    Cases_on`p_2`>>simp[map_lit_def]>>
    Cases_on`lookup_index s2 a`>>rw[]>>
    first_x_assum drule>>fs[])>>
  simp[]>>
  match_mp_tac concl_INJ_iff>>
  gvs [INJ_DEF] \\ rpt gen_tac
  \\ Cases_on ‘lookup_index s3 x’ \\ gvs []
  \\ Cases_on ‘lookup_index s3 y’ \\ gvs []
  \\ gvs[SUBSET_DEF] \\ metis_tac[lookup_index_inj]
QED

Theorem name_to_num_state_ok_name_to_num_prob:
  name_to_num_state_ok (s:'a name_to_num_state) ∧
  name_to_num_prob res s = (res',t) ⇒
  name_to_num_state_ok t
Proof
  PairCases_on`res`>>rw[name_to_num_prob_def]>>
  rpt(pairarg_tac>>gvs[])>>
  drule_all name_to_num_pres>> rw[]>>
  drule_all name_to_num_obj>>rw[]>>
  drule_then drule name_to_num_pbf_rec \\ fs []
  \\ impl_tac
  >- fs [pbf_vars_def]>>
  rw[]
QED

Theorem pres_set_list_OPTION_MAP:
  pres_set_list (OPTION_MAP (MAP f) pres) =
  IMAGE f (pres_set_list pres)
Proof
  Cases_on`pres`>>rw[pres_set_list_def,LIST_TO_SET_MAP]
QED

Theorem name_to_num_state_ok_lookup_index:
  name_to_num_state_ok s ∧
  lookup_index s x = SOME y ⇒
  y < s.next_num
Proof
  rw[name_to_num_state_ok_def,lookup_index_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  rw[]>>
  first_x_assum drule>>
  simp[]
QED

(* Typically, take t = st *)
Theorem name_to_num_prob_output_thm:
  ∀output
    (fml: α pbc list) (fml': num pbc list)
    (obj : (α lin_term # int) option)
    (obj': (num lin_term # int) option)
    (pres : (α list) option)
    (pres' : (num list) option)
    s t
    (fmlt: 'b pbc list) (fmlt': num pbc list)
    (objt : ('b lin_term # int) option)
    (objt': (num lin_term # int) option)
    (prest : ('b list) option)
    (prest' : (num list) option)
    st tt.
    name_to_num_prob (pres,obj,fml) s = ((pres',obj',fml'),t) ∧
    name_to_num_prob (prest,objt,fmlt) st = ((prest',objt',fmlt'),tt) ∧
    name_to_num_state_ok s ∧
    name_to_num_state_ok st ⇒
    sem_output (set fml) obj (pres_set_list pres) bound
               (set fmlt) objt (pres_set_list prest) output =
    sem_output (set fml') obj' (pres_set_list pres') bound
               (set fmlt') objt' (pres_set_list prest') output
Proof
  rw[name_to_num_prob_def]>>
  rpt(pairarg_tac>>gvs[])>>
  rename1`_ pres s = (_,s1)`>>
  rename1`_ obj s1 = (_,s2)`>>
  rename1`_ fml s2 _ = (_,s3)`>>
  drule_all name_to_num_pres>> rw[]>>
  drule_all name_to_num_obj>>rw[]>>
  drule_then drule name_to_num_pbf_rec \\ fs []
  \\ impl_tac
  >- fs [pbf_vars_def]>>
  rw[]>>
  qabbrev_tac`f = λx. (case lookup_index s3 x of NONE => s3.next_num | SOME v => v)`>>
  `obj_vars obj ⊆ {i | lookup_index s3 i ≠ NONE}` by (
    Cases_on`obj`>>fs[obj_vars_def]>>
    Cases_on`x`>>fs[obj_vars_def,SUBSET_DEF]>>
    rw[]>>first_x_assum drule>>
    metis_tac[option_CLAUSES])>>
  `map_obj (THE o lookup_index s2) obj =
   map_obj f obj` by (
    Cases_on`obj`>>
    simp[map_obj_def]>>
    Cases_on`x`>>
    fs[map_obj_def,obj_vars_def,Abbr`f`]>>
    fs[MAP_EQ_f,FORALL_PROD,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
    rw[]>>first_x_assum drule>>
    Cases_on`p_2`>>simp[map_lit_def]>>
    Cases_on`lookup_index s2 a`>>rw[]>>
    first_x_assum drule>>fs[])>>
  `OPTION_MAP (MAP (THE ∘ lookup_index s1)) pres =
   OPTION_MAP (MAP f) pres` by (
    Cases_on`pres` >>
    fs[Abbr`f`,pres_set_list_def,MAP_EQ_f,FORALL_PROD,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
    rw[]>>first_x_assum drule>>
    simp[GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>rw[]>>
    res_tac>>
    res_tac>>
    simp[])>>
  `MAP (map_pbc (THE ∘ lookup_index s3)) fml = MAP (map_pbc f) fml` by (
    fs[Abbr`f`,MAP_EQ_f,SUBSET_DEF,pbf_vars_def,PULL_EXISTS,FORALL_PROD,pbc_vars_def,map_pbc_def,MEM_MAP]>>
    rw[]>>first_x_assum drule>>
    disch_then drule>>
    simp[GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>rw[]>>
    rename1`lit_var vv`>>
    Cases_on`vv`>>gvs[lit_var_def,map_lit_def])>>
  simp[]>>
  qpat_x_assum`_ fmlt _ _ = _` assume_tac>>
  qpat_x_assum`_ objt _ = _` assume_tac>>
  qpat_x_assum`_ prest _ = _` assume_tac>>
  rename1`_ prest st = (_,st1)`>>
  rename1`_ objt st1 = (_,st2)`>>
  rename1`_ fmlt st2 _ = (_,st3)`>>
  drule_all name_to_num_pres>>rw[]>>
  drule_all name_to_num_obj>>rw[]>>
  drule_then drule name_to_num_pbf_rec \\ fs []
  \\ impl_tac
  >- fs [pbf_vars_def]>>
  rw[]>>
  qabbrev_tac`ft = λx. (case lookup_index st3 x of NONE => st3.next_num | SOME v => v)`>>
  `obj_vars objt ⊆ {i | lookup_index st3 i ≠ NONE}` by (
    Cases_on`objt`>>fs[obj_vars_def]>>
    Cases_on`x`>>fs[obj_vars_def,SUBSET_DEF]>>
    rw[]>>first_x_assum drule>>
    metis_tac[option_CLAUSES])>>
  `map_obj (THE o lookup_index st2) objt =
   map_obj ft objt` by (
    Cases_on`objt`>>
    simp[map_obj_def]>>
    Cases_on`x`>>
    fs[map_obj_def,obj_vars_def,Abbr`ft`]>>
    fs[MAP_EQ_f,FORALL_PROD,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
    rw[]>>first_x_assum drule>>
    Cases_on`p_2`>>simp[map_lit_def]>>
    Cases_on`lookup_index st2 a`>>rw[]>>
    first_x_assum drule>>fs[])>>
  `OPTION_MAP (MAP (THE ∘ lookup_index st1)) prest =
   OPTION_MAP (MAP ft) prest` by (
    Cases_on`prest` >>
    fs[Abbr`ft`,pres_set_list_def,MAP_EQ_f,FORALL_PROD,SUBSET_DEF,MEM_MAP,PULL_EXISTS]>>
    rw[]>>first_x_assum drule>>
    simp[GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>rw[]>>
    res_tac>>
    res_tac>>
    simp[])>>
  `MAP (map_pbc (THE ∘ lookup_index st3)) fmlt = MAP (map_pbc ft) fmlt` by (
    fs[Abbr`ft`,MAP_EQ_f,SUBSET_DEF,pbf_vars_def,PULL_EXISTS,FORALL_PROD,pbc_vars_def,map_pbc_def,MEM_MAP]>>
    rw[]>>first_x_assum drule>>
    disch_then drule>>
    simp[GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>rw[]>>
    rename1`lit_var vv`>>
    Cases_on`vv`>>gvs[lit_var_def,map_lit_def])>>
  simp[]>>
  gvs[LIST_TO_SET_MAP,pres_set_list_OPTION_MAP]>>
  match_mp_tac output_INJ_iff>>
  qmatch_goalsub_abbrev_tac`INJ f vs`>>
  `∀x. x ∈ vs ⇒
    lookup_index s3 x ≠ NONE` by (
    gvs[Abbr`vs`,SUBSET_DEF]>>
    metis_tac[option_CLAUSES])>>
  `∀x. lookup_index s3 x ≠ NONE ⇒ lookup_index s3 x = SOME (f x)` by (
    rw[Abbr`f`]>>
    TOP_CASE_TAC>>gvs[])>>
  `∀x y. x ∈ vs ∧ lookup_index s3 y = NONE ⇒ f x ≠ f y` by (
    rw[Abbr`f`]>>
    TOP_CASE_TAC>>gvs[]>>
    drule_all name_to_num_state_ok_lookup_index>>
    simp[])>>
  qmatch_goalsub_abbrev_tac`INJ ft vst`>>
  `∀x. x ∈ vst ⇒
    lookup_index st3 x ≠ NONE` by (
    gvs[Abbr`vst`,SUBSET_DEF]>>
    metis_tac[option_CLAUSES])>>
  `∀x. lookup_index st3 x ≠ NONE ⇒ lookup_index st3 x = SOME (ft x)` by (
    rw[Abbr`ft`]>>
    TOP_CASE_TAC>>gvs[])>>
  `∀x y. x ∈ vst ∧ lookup_index st3 y = NONE ⇒ ft x ≠ ft y` by (
    rw[Abbr`ft`]>>
    TOP_CASE_TAC>>gvs[]>>
    drule_all name_to_num_state_ok_lookup_index>>
    simp[])>>
  gvs [INJ_DEF]>>
  CONJ_TAC>- (
    (* Manual proof since metis is slow *)
    rw[]>>
    irule lookup_index_inj>>
    qexists_tac`f x`>>
    qexists_tac`s3`>>
    metis_tac[])>>
  CONJ_TAC>- (
    (* Manual proof since metis is slow *)
    rw[]>>
    irule lookup_index_inj>>
    qexists_tac`ft x`>>
    qexists_tac`st3`>>
    metis_tac[])>>
  CONJ_TAC >- (
     (* Manual proof since metis is slow *)
    rw[]>>
    gvs[Abbr`vs`]>>
    Cases_on`lookup_index s3 y = NONE `>>gvs[]>>
    irule lookup_index_inj>>
    qexists_tac`f x`>>
    qexists_tac`s3`>>
    gvs[])>>
  (* Manual proof since metis is slow *)
  rw[]>>
  gvs[Abbr`vst`]>>
  Cases_on`lookup_index st3 y = NONE `>>gvs[]>>
  irule lookup_index_inj>>
  qexists_tac`ft x`>>
  qexists_tac`st3`>>
  gvs[]
QED
