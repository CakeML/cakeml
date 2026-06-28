(*
  Formalization of the CP to ILP phase (sorting constraints)
*)
Theory cp_to_ilp_sorting
Libs
  preamble
Ancestors
  pbc pbc_encode cp ilp cp_to_ilp int_bitwise int_bitwiseExtra

(* Generic, CP-free helpers (bit lookup, iSUM/FILTER counting, list/PERM/SORTED
   and finite-self-map facts) shared across the Sort/ArgSort encodings. *)

(* total, subtraction-free bit lookup into a little-endian bool list (for
   translation: avoids EL/BIT side conditions; see sort_guard_alt) *)
Definition nth_bit_def:
  (nth_bit [] b = F) ∧
  (nth_bit (x::xs) 0 = x) ∧
  (nth_bit (x::xs) (SUC b) = nth_bit xs b)
End

Theorem nth_bit_eq[local]:
  ∀l b. nth_bit l b ⇔ b < LENGTH l ∧ EL b l
Proof
  Induct>>rw[nth_bit_def]>>Cases_on`b`>>gvs[nth_bit_def]
QED

(* sum of indicator weights = number of satisfied indices *)
Theorem iSUM_b2i_GENLIST[local]:
  ∀n. iSUM (GENLIST (λk. b2i (P k)) n) =
      &(LENGTH (FILTER P (COUNT_LIST n)))
Proof
  simp[COUNT_LIST_GENLIST]>>
  Induct>>
  simp[GENLIST,SNOC_APPEND,iSUM_APPEND,FILTER_APPEND,iSUM_def,combinTheory.I_THM]>>
  Cases_on`P n`>>simp[b2i_def]>>intLib.ARITH_TAC
QED

(* a bounded injective endofunction of [0,n) is surjective onto [0,n) *)
Theorem inj_count_surj[local]:
  (∀i. i < n ⇒ f i < n) ∧
  (∀i j. i < n ∧ j < n ∧ f i = f j ⇒ i = j) ∧
  (y:num) < n ⇒
  ∃i. i < n ∧ f i = y
Proof
  rpt strip_tac>>
  `IMAGE f (count n) = count n` by
    (irule SUBSET_EQ_CARD>>simp[SUBSET_DEF,PULL_EXISTS]>>
     DEP_REWRITE_TAC[CARD_IMAGE_INJ]>>simp[]>>rw[]>>first_x_assum irule>>simp[])>>
  gvs[EXTENSION,IN_IMAGE,IN_COUNT]>>
  first_x_assum(qspec_then`y`mp_tac)>>simp[]>>
  rw[]>>first_assum (irule_at Any)>>simp[]
QED

(* mapping an injective endofunction over COUNT_LIST permutes it *)
Theorem PERM_MAP_COUNT_LIST_inj[local]:
  (∀i. i < n ⇒ f i < n) ∧
  (∀i j. i < n ∧ j < n ∧ f i = f j ⇒ i = j) ⇒
  PERM (MAP f (COUNT_LIST n)) (COUNT_LIST n)
Proof
  strip_tac>>
  irule PERM_ALL_DISTINCT>>
  rpt conj_tac
  >- (simp[MEM_MAP,MEM_COUNT_LIST]>>rw[]>>eq_tac>>rw[]
      >- (gvs[]>>first_x_assum irule>>simp[])
      >- (`∃i. i < n ∧ f i = x` by (irule inj_count_surj>>metis_tac[])>>
          metis_tac[]))
  >- (irule ALL_DISTINCT_MAP_INJ>>simp[all_distinct_count_list,MEM_COUNT_LIST]>>
      metis_tac[])
  >- simp[all_distinct_count_list]
QED

(* reading a list along its own index range is the identity *)
Theorem MAP_EL_COUNT_LIST_self[local]:
  LENGTH xs = LENGTH (ys:'a list) ⇒
  MAP (λk. EL k ys) (COUNT_LIST (LENGTH xs)) = ys
Proof
  strip_tac>>irule LIST_EQ>>rw[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST]
QED

(* a length-n list with bounded, injective entries is a permutation of [0,n) *)
Theorem PERM_inj_COUNT_LIST[local]:
  LENGTH qs = n ∧ (∀j. j < n ⇒ EL j qs < n) ∧
  (∀i j. i < n ∧ j < n ∧ EL i qs = EL j qs ⇒ i = j) ⇒
  PERM qs (COUNT_LIST n)
Proof
  strip_tac>>
  `qs = MAP (λk. EL k qs) (COUNT_LIST n)` by (
    qpat_x_assum`LENGTH qs = n`(SUBST1_TAC o SYM)>>
    simp[MAP_EL_COUNT_LIST_self])>>
  pop_assum SUBST1_TAC>>
  irule PERM_MAP_COUNT_LIST_inj>>
  simp[EL_COUNT_LIST,LENGTH_COUNT_LIST]
QED

(* entries of a permutation of [0,n) are themselves < n *)
Theorem PERM_COUNT_LIST_EL_lt[local]:
  PERM qs (COUNT_LIST n) ∧ j < n ⇒ EL j qs < n
Proof
  rw[]>>
  `LENGTH qs = n` by metis_tac[PERM_LENGTH,LENGTH_COUNT_LIST]>>
  `MEM (EL j qs) qs` by (irule EL_MEM>>simp[])>>
  drule PERM_MEM_EQ>>
  disch_then(qspec_then`EL j qs`mp_tac)>>
  simp[MEM_COUNT_LIST]
QED

(* a list whose entries are non-decreasing in the index is SORTED *)
Theorem SORTED_le_GENLIST[local]:
  (∀a b. a < b ∧ b < n ⇒ h a ≤ (h b:int)) ⇒
  SORTED (λ(x:int) y. x ≤ y) (GENLIST h n)
Proof
  strip_tac>>simp[SORTED_EL_SUC]>>rw[]>>
  DEP_REWRITE_TAC[EL_GENLIST]>>simp[]>>
  first_x_assum irule>>simp[]
QED

(* sorted permutations under (≤) coincide *)
Theorem sorted_le_PERM_EQ[local]:
  SORTED (λ(x:int) y. x ≤ y) l1 ∧ SORTED (λ(x:int) y. x ≤ y) l2 ∧ PERM l1 l2 ⇒
  l1 = l2
Proof
  strip_tac>>irule SORTED_PERM_EQ>>
  conj_tac >- first_x_assum ACCEPT_TAC>>
  qexists_tac`λ(x:int) y. x ≤ y`>>
  rw[transitive_def,antisymmetric_def]>>intLib.ARITH_TAC
QED

(* a strictly-increasing self-map of [0,n) bounded by n is the identity *)
Theorem strict_mono_ge[local]:
  (∀j. j < n ⇒ (f:num->num) j < n) ∧ (∀a b. a < b ∧ b < n ⇒ f a < f b) ∧
  (∀j. j < n ⇒ j ≤ f j) ⇒
  ∀k. k < n ⇒ f (n - 1 - k) = n - 1 - k
Proof
  strip_tac>>
  Induct>>rw[]
  >- (
    `n - 1 < n` by simp[]>>
    `n - 1 ≤ f (n - 1)` by metis_tac[]>>
    `f (n - 1) < n` by metis_tac[]>>
    fs[])>>
  `k < n` by fs[]>>
  `f (n - 1 - k) = n - 1 - k` by metis_tac[]>>
  `n - (SUC k + 1) < n - 1 - k ∧ n - 1 - k < n ∧ n - (SUC k + 1) < n` by simp[]>>
  `f (n - (SUC k + 1)) < f (n - 1 - k)` by metis_tac[]>>
  `n - (SUC k + 1) ≤ f (n - (SUC k + 1))` by metis_tac[]>>
  fs[]
QED

Theorem strict_mono_id[local]:
  (∀j. j < n ⇒ (f:num->num) j < n) ∧ (∀a b. a < b ∧ b < n ⇒ f a < f b) ⇒
  ∀j. j < (n:num) ⇒ f j = j
Proof
  strip_tac>>
  `∀j. j < n ⇒ j ≤ f j` by (
    Induct>-simp[]>>
    rw[]>>
    `j < n` by fs[]>>
    `j ≤ f j` by metis_tac[]>>
    `f j < f (SUC j)` by metis_tac[prim_recTheory.LESS_SUC_REFL]>>
    fs[])>>
  `∀k. k < n ⇒ f (n - 1 - k) = n - 1 - k` by metis_tac[strict_mono_ge]>>
  rw[]>>
  `n - 1 - j < n ∧ n - 1 - (n - 1 - j) = j` by simp[]>>
  first_x_assum (qspec_then`n - 1 - j`mp_tac)>>
  simp[]
QED

(* a self-map of [0,n) bounded in [0,n) is strictly increasing iff it is the
   identity *)
Theorem strict_mono_iff_id[local]:
  (∀j. j < n ⇒ (f:num->num) j < n) ⇒
  ((∀a b. a < b ∧ b < n ⇒ f a < f b) ⇔ (∀j. j < n ⇒ f j = j))
Proof
  strip_tac>>eq_tac>>strip_tac
  >- (match_mp_tac strict_mono_id>>conj_tac>>first_x_assum ACCEPT_TAC)
  >- (rw[]>>`a < n` by fs[]>>`f a = a ∧ f b = b` by fs[]>>fs[])
QED

(* at most one element can map (under an injective g) to a fixed value *)
Theorem ALL_DISTINCT_MAP_FILTER_le_1[local]:
  ∀l. ALL_DISTINCT (MAP g l) ⇒ LENGTH (FILTER (λx. g x = c) l) ≤ 1
Proof
  Induct>>rw[]>>
  `FILTER (λx. g x = g h) l = []` by
    (simp[FILTER_EQ_NIL,EVERY_MEM]>>gvs[MEM_MAP]>>metis_tac[])>>
  simp[]
QED

(* adjacent pairs of a list, total (no side condition), one pass *)
Definition adj_pairs_def:
  (adj_pairs [] = []) ∧
  (adj_pairs [x] = []) ∧
  (adj_pairs (x::y::rest) = (x,y) :: adj_pairs (y::rest))
End

Theorem LENGTH_adj_pairs[local]:
  ∀l. LENGTH (adj_pairs l) = LENGTH l - 1
Proof
  ho_match_mp_tac adj_pairs_ind>>rw[adj_pairs_def]
QED

Theorem EL_adj_pairs[local]:
  ∀l j. j < LENGTH l - 1 ⇒ EL j (adj_pairs l) = (EL j l, EL (j+1) l)
Proof
  ho_match_mp_tac adj_pairs_ind>>rw[adj_pairs_def]>>
  Cases_on`j`>>gvs[GSYM ADD1,EL]
QED

(* Increasing: a monotone chain over Xs — one adjacent comparison per pair,
   with (strct,desc) selecting the relation. *)

(* the adjacent comparison constraint picked by (strct,desc) *)
Definition inc_cmp_def:
  inc_cmp strct desc X Y =
  if desc then (if strct then mk_gt X Y else mk_ge X Y)
  else (if strct then mk_lt X Y else mk_le X Y)
End

Theorem inc_cmp_sem[simp]:
  iconstraint_sem (inc_cmp strct desc X Y) (wi,wb) ⇔
  inc_rel strct desc (varc wi X) (varc wi Y)
Proof
  Cases_on`desc`>>Cases_on`strct`>>rw[inc_cmp_def]>>
  intLib.ARITH_TAC
QED

(* Increasing: linear chain x0 ⋈ x1, x1 ⋈ x2, ... *)
Definition inc_chain_def:
  (inc_chain strct desc i name X [] = []) ∧
  (inc_chain strct desc i name X (Y::Ys) =
    (SOME (mk_name name (toString i)), inc_cmp strct desc X Y)::
    inc_chain strct desc (i+1) name Y Ys)
End

Definition cencode_increasing_def:
  cencode_increasing Xs strct desc name =
  case Xs of [] => Nil
  | (X::Xs) =>
    List (inc_chain strct desc 0 name X Xs)
End

Definition encode_increasing_def:
  encode_increasing Xs strct desc name =
  abstr $ cencode_increasing Xs strct desc name
End

Theorem inc_chain_sem:
  ∀Xs i name X.
  EVERY (λx. iconstraint_sem x (wi,wb))
    (abstrl (inc_chain strct desc i name X Xs)) ⇔
  SORTED (inc_rel strct desc) (varc wi X :: MAP (varc wi) Xs)
Proof
  Induct>>rw[inc_chain_def,SORTED_DEF]
QED

Theorem encode_increasing_sem_1:
  increasing_sem Xs strct desc wi ⇒
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_increasing Xs strct desc name)
Proof
  gs[encode_increasing_def,cencode_increasing_def,increasing_sem_def]>>
  Cases_on`Xs`>>
  rw[]>>fs[inc_chain_sem]
QED

Theorem encode_increasing_sem_2:
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_increasing Xs strct desc name) ⇒
  increasing_sem Xs strct desc wi
Proof
  gs[encode_increasing_def,cencode_increasing_def,increasing_sem_def]>>
  Cases_on`Xs`>>
  rw[]>>fs[inc_chain_sem]
QED

(* Sort: ys is a non-decreasing permutation of xs, via stable before-flags, a
   proof-only stable rank (weighted bit-sum), and a position channel. *)

(* flag accessors: before[ip][i] and bit b of the stable rank pos[i] *)
Definition sort_bf_def[simp]:
  sort_bf name ip i = INR (name, Indices [ip; i] (SOME «bf»))
End
Definition sort_posbit_def[simp]:
  sort_posbit name i b = INR (name, Values [&i; &b] (SOME «pos»))
End

(* bit-width for ranks 0 … n−1 *)
Definition sort_width_def:
  sort_width n = LENGTH (bits_of_num (n − 1))
End

(* (c) proof-only stable-rank bit-sum for element i *)
Definition sort_pos_num_def:
  sort_pos_num name i w =
  GENLIST (λb. (&(2 ** b), Pos (sort_posbit name i b))) w
End

(* Σ_{ip<n} before[ip][i] as a bit lin-term (before[i][i] is forced false) *)
Definition sort_before_sum_def:
  sort_before_sum name n i =
  GENLIST (λip. (1i, Pos (sort_bf name ip i))) n
End

(* (a) the non-decreasing chain y[0] ≤ y[1] ≤ … : an Increasing (≤) chain over Ys *)
Definition sort_chain_le_def:
  sort_chain_le name Ys = cencode_increasing Ys F F name
End

(* (b) two-way pin each before-flag to its stable comparison; the indices i/ip
   name the flag, the elements xi/xip feed the comparison *)
Definition sort_bf_lines_def:
  sort_bf_lines bnd name Xs =
  flat_app (MAPi (λi xi.
    flat_app (MAPi (λip xip.
      cbimply_var bnd (sort_bf name ip i)
        (if ip < i then mk_le xip xi else mk_lt xip xi))
      Xs))
    Xs)
End

(* (d) rank equation pos[i] = Σ_{ip} before[ip][i], as ≥ and ≤ halves *)
Definition sort_rank_lines_def:
  sort_rank_lines name w n =
  List (FLAT (MAP (λi.
    let bs = sort_pos_num name i w in
    let cs = sort_before_sum name n i in
    [(SOME (mk_name name («rge» ^ toString i)),
        ([], bs ++ MAP (λ(a,l). (-a,l)) cs, 0i));
     (SOME (mk_name name («rle» ^ toString i)),
        ([], cs ++ MAP (λ(a,l). (-a,l)) bs, 0i))])
    (COUNT_LIST n)))
End

(* conjunction-of-bit-literals guard fixing pos[i]'s bits to binary(j) *)
Definition sort_guard_def:
  sort_guard name w i j =
  MAPi (λb sb. (if sb then Pos else Neg) (sort_posbit name i b))
       (PAD_RIGHT F w (bits_of_num j))
End

(* (e) position channel: (pos[i]=j) → y[j] = x[i], emitted as ≤ and ≥ *)
Definition sort_chan_lines_def:
  sort_chan_lines bnd name w Xs Ys =
  flat_app (MAPi (λi xi.
    flat_app (MAPi (λj yj.
      Append
        (List [(SOME (mk_name name («cle» ^ toString i ^ «_» ^ toString j)),
                 bits_imply bnd (sort_guard name w i j) (mk_le yj xi))])
        (List [(SOME (mk_name name («cge» ^ toString i ^ «_» ^ toString j)),
                 bits_imply bnd (sort_guard name w i j) (mk_ge yj xi))]))
      Ys))
    Xs)
End

Definition cencode_sort_def:
  cencode_sort bnd Xs Ys name =
  let n = LENGTH Xs in
  if n ≠ LENGTH Ys then cfalse_constr
  else
    let w = sort_width n in
    Append (sort_chain_le name Ys)
    (Append (sort_bf_lines bnd name Xs)
    (Append (sort_rank_lines name w n)
            (sort_chan_lines bnd name w Xs Ys)))
End

Definition encode_sort_def:
  encode_sort bnd Xs Ys name = abstr (cencode_sort bnd Xs Ys name)
End

(* Sort soundness: the stable rank is a bijection on [0,n) placing element i at
   its rank; combinatorics and bit/eval bridges, then the two directions. *)

(* the stable order on positions of a value list: by value, ties by index *)
Definition idx_lt_def:
  idx_lt (xs:int list) i j ⇔
    EL i xs < EL j xs ∨ (EL i xs = EL j xs ∧ i < j)
End

Theorem idx_lt_irrefl[local]:
  ¬ idx_lt xs i i
Proof
  rw[idx_lt_def]>>intLib.ARITH_TAC
QED

Theorem idx_lt_transitive[local]:
  transitive (idx_lt xs)
Proof
  `idx_lt xs = inv_image ($< LEX $<) (λi. (EL i xs, i))` by
    simp[FUN_EQ_THM,idx_lt_def,pairTheory.LEX_DEF,relationTheory.inv_image_def]>>
  pop_assum SUBST1_TAC>>
  irule relationTheory.transitive_inv_image>>
  irule pairTheory.transitive_LEX>>
  conj_tac
  >- (simp[relationTheory.transitive_def]>>intLib.ARITH_TAC)
  >- (simp[relationTheory.transitive_def]>>decide_tac)
QED

Theorem idx_lt_total[local]:
  i = j ∨ idx_lt xs i j ∨ idx_lt xs j i
Proof
  simp[idx_lt_def]>>
  Cases_on`EL i xs = EL j xs`
  >- (gvs[]>>decide_tac)
  >- (`EL i xs < EL j xs ∨ EL j xs < EL i xs` by intLib.ARITH_TAC>>
      metis_tac[])
QED

Theorem idx_lt_le[local]:
  idx_lt xs i j ⇒ EL i xs ≤ EL j xs
Proof
  rw[idx_lt_def]
  >- intLib.ARITH_TAC
  >- gvs[]
QED

(* translation-friendly forms (subtraction-free) of the two width/guard helpers:
   the truncated subtractions n-1 and w-LENGTH(...) would otherwise force carried
   preconditions through the whole Sort/ArgSort encoder.  Both are value-preserving. *)
Theorem sort_width_alt:
  sort_width n = if n = 0 then 0 else LENGTH (bits_of_num (n − 1))
Proof
  rw[sort_width_def]>>simp[Once bits_of_num_def]
QED

Theorem sort_guard_alt:
  sort_guard name w i j =
  GENLIST (λb. (if nth_bit (bits_of_num j) b then Pos else Neg) (sort_posbit name i b))
          (MAX (LENGTH (bits_of_num j)) w)
Proof
  rw[sort_guard_def]>>irule LIST_EQ>>
  `LENGTH (PAD_RIGHT F w (bits_of_num j)) = MAX (LENGTH (bits_of_num j)) w` by
    rw[bitstringTheory.length_pad_right,MAX_DEF]>>
  simp[indexedListsTheory.LENGTH_MAPi,LENGTH_GENLIST,
       indexedListsTheory.EL_MAPi,EL_GENLIST]>>
  rpt strip_tac>>
  `EL x (PAD_RIGHT F w (bits_of_num j)) = nth_bit (bits_of_num j) x` by
    (simp[nth_bit_eq,PAD_RIGHT,EL_APPEND_EQN,MAX_DEF]>>rw[]>>gvs[EL_GENLIST])>>
  simp[]
QED

(* negating coefficients negates the linear value *)
Theorem eval_lin_term_MAP_neg_sort[local]:
  ∀bs. eval_lin_term wb (MAP (λ(a,l). (-a,l)) bs) = -eval_lin_term wb bs
Proof
  Induct>>gvs[eval_lin_term_def,iSUM_def]>>
  Cases>>gvs[eval_term_def,eval_lin_term_def,iSUM_def]>>
  intLib.ARITH_TAC
QED

(* the proof-only before-flag is the stable order on the value list *)
Theorem sort_before_idx_lt[local]:
  ip < LENGTH Xs ∧ i < LENGTH Xs ⇒
  (sort_before wi Xs ip i ⇔ idx_lt (MAP (varc wi) Xs) ip i)
Proof
  rw[sort_before_def,idx_lt_def,EL_MAP]>>simp[integerTheory.INT_LE_LT]
QED

(* the stable rank counts the positions strictly below i in the stable order *)
Theorem sort_rank_card[local]:
  i < LENGTH Xs ⇒
  sort_rank wi Xs i =
  CARD {ip | ip < LENGTH Xs ∧ idx_lt (MAP (varc wi) Xs) ip i}
Proof
  strip_tac>>
  simp[sort_rank_def]>>
  `FILTER (λip. sort_before wi Xs ip i) (COUNT_LIST (LENGTH Xs)) =
   FILTER (λip. idx_lt (MAP (varc wi) Xs) ip i) (COUNT_LIST (LENGTH Xs))` by
    (simp[FILTER_EQ,MEM_COUNT_LIST]>>rw[]>>metis_tac[sort_before_idx_lt])>>
  pop_assum SUBST_ALL_TAC>>
  `LENGTH (FILTER (λip. idx_lt (MAP (varc wi) Xs) ip i) (COUNT_LIST (LENGTH Xs))) =
   CARD (set (FILTER (λip. idx_lt (MAP (varc wi) Xs) ip i) (COUNT_LIST (LENGTH Xs))))` by
    (irule (GSYM ALL_DISTINCT_CARD_LIST_TO_SET)>>
     simp[FILTER_ALL_DISTINCT,all_distinct_count_list])>>
  pop_assum SUBST_ALL_TAC>>
  AP_TERM_TAC>>
  simp[EXTENSION,MEM_FILTER,MEM_COUNT_LIST]>>
  metis_tac[]
QED

(* the stable rank lies in [0,n) *)
Theorem sort_rank_lt[local]:
  i < LENGTH Xs ⇒ sort_rank wi Xs i < LENGTH Xs
Proof
  strip_tac>>
  simp[sort_rank_card]>>
  `{ip | ip < LENGTH Xs ∧ idx_lt (MAP (varc wi) Xs) ip i} ⊂ count (LENGTH Xs)` by (
    simp[PSUBSET_MEMBER,SUBSET_DEF]>>
    qexists`i`>>simp[idx_lt_irrefl])>>
  metis_tac[CARD_PSUBSET,FINITE_COUNT,CARD_COUNT]
QED

(* the stable rank is strictly monotone for the stable order *)
Theorem sort_rank_card_lt[local]:
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  (idx_lt (MAP (varc wi) Xs) i j ⇔ sort_rank wi Xs i < sort_rank wi Xs j)
Proof
  strip_tac>>
  simp[sort_rank_card]>>
  `∀p q. p < LENGTH Xs ∧ q < LENGTH Xs ∧ idx_lt (MAP (varc wi) Xs) p q ⇒
     CARD {ip | ip < LENGTH Xs ∧ idx_lt (MAP (varc wi) Xs) ip p} <
     CARD {ip | ip < LENGTH Xs ∧ idx_lt (MAP (varc wi) Xs) ip q}` by (
    rw[]>>
    irule CARD_PSUBSET>>
    conj_tac
    >- (irule SUBSET_FINITE>>qexists`count (LENGTH Xs)`>>simp[SUBSET_DEF])>>
    simp[PSUBSET_MEMBER,SUBSET_DEF]>>
    conj_tac
    >- (rw[]>>metis_tac[idx_lt_transitive,relationTheory.transitive_def])>>
    qexists`p`>>simp[idx_lt_irrefl])>>
  eq_tac
  >- (strip_tac>>first_x_assum irule>>simp[])>>
  strip_tac>>
  `i = j ∨ idx_lt (MAP (varc wi) Xs) i j ∨ idx_lt (MAP (varc wi) Xs) j i`
    by metis_tac[idx_lt_total]>>
  gvs[]>>
  first_x_assum drule_all>>simp[]
QED

(* injectivity of the stable rank on [0,n) *)
Theorem sort_rank_inj[local]:
  i < LENGTH Xs ∧ j < LENGTH Xs ∧ sort_rank wi Xs i = sort_rank wi Xs j ⇒ i = j
Proof
  rw[]>>
  `¬(sort_rank wi Xs i < sort_rank wi Xs j) ∧
   ¬(sort_rank wi Xs j < sort_rank wi Xs i)` by gvs[]>>
  metis_tac[sort_rank_card_lt,idx_lt_total]
QED

(* the stable rank is surjective onto [0,n) *)
Theorem sort_rank_surj[local]:
  r < LENGTH Xs ⇒ ∃i. i < LENGTH Xs ∧ sort_rank wi Xs i = r
Proof
  strip_tac>>
  irule inj_count_surj>>
  simp[]>>metis_tac[sort_rank_lt,sort_rank_inj]
QED

(* eval bridges: the proof-only bit-sum and the before-flag sum *)

(* the weighted bit-sum reads back as num_of_bits of its bits *)
Theorem sort_pos_num_num_of_bits[local]:
  eval_lin_term wb (sort_pos_num name i w) =
  &num_of_bits (GENLIST (λb. wb (sort_posbit name i b)) w)
Proof
  rw[num_of_bits_GENLIST,sort_pos_num_def,eval_lin_term_def,MAP_GENLIST,o_DEF,
     eval_term_def,eval_lit_def,lit_def]
QED

(* the unit-coefficient before-flag sum counts the set before-flags *)
Theorem sort_before_sum_count[local]:
  eval_lin_term wb (sort_before_sum name n i) =
  &(LENGTH (FILTER (λip. wb (sort_bf name ip i)) (COUNT_LIST n)))
Proof
  rw[sort_before_sum_def,eval_lin_term_def,MAP_GENLIST,o_DEF,
     eval_term_def,eval_lit_def,lit_def]>>
  simp[GSYM iSUM_b2i_GENLIST]
QED

(* the bit-pattern guard for pos[i]=j holds iff every bit of pos[i] matches j *)
Theorem sort_guard_lit[local]:
  j < 2 ** w ⇒
  (EVERY (lit wb) (sort_guard name w i j) ⇔
   ∀b. b < w ⇒ (wb (sort_posbit name i b) ⇔ BIT b j))
Proof
  strip_tac>>
  `LENGTH (bits_of_num j) ≤ w` by simp[LENGTH_bits_of_num_LE]>>
  simp[sort_guard_def,EVERY_EL,LENGTH_MAPi,PAD_RIGHT,EL_MAPi]>>
  eq_tac>>rw[]>>
  first_x_assum drule>>
  simp[EL_PAD_RIGHT_bits |> SIMP_RULE std_ss [PAD_RIGHT]]>>
  rw[]>>gvs[lit_def]>>
  Cases_on`BIT b j`>>gvs[lit_def]
QED

(* block-level semantics *)

(* (b) the before-flag block pins each flag to its stable comparison *)
Theorem sort_bf_lines_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (sort_bf_lines bnd name Xs)) ⇔
   ∀ip i. ip < LENGTH Xs ∧ i < LENGTH Xs ⇒
     (wb (sort_bf name ip i) ⇔ sort_before wi Xs ip i))
Proof
  strip_tac>>
  simp[sort_bf_lines_def, EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
  `∀ip i. ip < LENGTH Xs ∧ i < LENGTH Xs ⇒
    (iconstraint_sem
       (if ip < i then mk_constraint_ge 1 (EL i Xs) (-1) (EL ip Xs) 0
        else mk_constraint_ge 1 (EL i Xs) (-1) (EL ip Xs) 1) (wi,wb) ⇔
     sort_before wi Xs ip i)` by
    (rw[sort_before_def,mk_constraint_ge_sem]>>intLib.ARITH_TAC)>>
  metis_tac[]
QED

(* (d) the rank equation forces the bit-sum to equal the before-flag count *)
Theorem sort_rank_lines_sem[local]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (sort_rank_lines name w n)) ⇔
  ∀i. i < n ⇒
    eval_lin_term wb (sort_pos_num name i w) =
    eval_lin_term wb (sort_before_sum name n i)
Proof
  simp[sort_rank_lines_def,EVERY_FLAT,EVERY_MAP,MEM_MAP,PULL_EXISTS,MEM_COUNT_LIST,
       iconstraint_sem_def,eval_ilin_term_def,iSUM_def,eval_lin_term_append,
       eval_lin_term_MAP_neg_sort]>>
  simp[EVERY_MEM,MEM_COUNT_LIST]>>
  `∀a b:int. (a + -b ≥ 0 ∧ b + -a ≥ 0) ⇔ a = b` by intLib.ARITH_TAC>>
  metis_tac[]
QED

(* (e) the channel block: whenever pos[i]'s bits spell j, y[j] = x[i] *)
Theorem sort_chan_lines_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (sort_chan_lines bnd name w Xs Ys)) ⇔
   ∀i j. i < LENGTH Xs ∧ j < LENGTH Ys ⇒
     EVERY (lit wb) (sort_guard name w i j) ⇒
       varc wi (EL j Ys) = varc wi (EL i Xs))
Proof
  strip_tac>>
  simp[sort_chan_lines_def, EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
  `∀g (a:int) b. ((g ⇒ a + -1*b ≥ 0) ∧ (g ⇒ b + -1*a ≥ 0)) ⇔ (g ⇒ b = a)` by
    (rw[]>>Cases_on`g`>>simp[]>>intLib.ARITH_TAC)>>
  metis_tac[]
QED

(* Crux B: the sorted permutation places x[i] at its stable rank *)

Theorem sort_rank_channel[local]:
  PERM (MAP (varc wi) Xs) (MAP (varc wi) Ys) ∧
  SORTED (λ(x:int) y. x ≤ y) (MAP (varc wi) Ys) ∧
  i < LENGTH Xs ⇒
  EL (sort_rank wi Xs i) (MAP (varc wi) Ys) = EL i (MAP (varc wi) Xs)
Proof
  strip_tac>>
  qabbrev_tac`n = LENGTH Xs`>>
  qabbrev_tac`xs = MAP (varc wi) Xs`>>
  qabbrev_tac`ys = MAP (varc wi) Ys`>>
  qabbrev_tac`f = sort_rank wi Xs`>>
  `LENGTH xs = n ∧ LENGTH ys = n` by (
    unabbrev_all_tac>>imp_res_tac PERM_LENGTH>>gvs[])>>
  (* f is a bijection on [0,n) respecting the stable index order *)
  `(∀j. j < n ⇒ f j < n) ∧
   (∀a b. a < n ∧ b < n ∧ f a = f b ⇒ a = b) ∧
   (∀r. r < n ⇒ ∃j. j < n ∧ f j = r) ∧
   (∀a b. a < n ∧ b < n ⇒ (idx_lt xs a b ⇔ f a < f b))` by (
    rpt conj_tac>>rpt strip_tac>>unabbrev_all_tac>>
    metis_tac[sort_rank_lt,sort_rank_inj,sort_rank_surj,sort_rank_card_lt])>>
  (* g is the inverse rank → index function *)
  qabbrev_tac`g = λr. @j. j < n ∧ f j = r`>>
  `∀r. r < n ⇒ f (g r) = r ∧ g r < n` by (
    gen_tac>>strip_tac>>simp[Abbr`g`]>>SELECT_ELIM_TAC>>metis_tac[])>>
  `∀a. a < n ⇒ g (f a) = a` by (
    rw[]>>`f a < n` by metis_tac[]>>
    `f (g (f a)) = f a ∧ g (f a) < n` by metis_tac[]>>
    metis_tac[])>>
  (* reading xs along g is non-decreasing *)
  `∀a b. a < b ∧ b < n ⇒ xs❲g a❳ ≤ xs❲g b❳` by (
    rpt strip_tac>>
    `a < n` by simp[]>>
    `f (g a) = a ∧ g a < n` by
      (qpat_assum`∀r. r < n ⇒ f (g r) = _ ∧ _`(qspec_then`a`mp_tac)>>simp[])>>
    `f (g b) = b ∧ g b < n` by
      (qpat_assum`∀r. r < n ⇒ f (g r) = _ ∧ _`(qspec_then`b`mp_tac)>>simp[])>>
    `idx_lt xs (g a) (g b)` by
      (qpat_assum`∀a b. a < n ∧ b < n ⇒ (idx_lt xs a b ⇔ _)`
         (qspecl_then[`g a`,`g b`]mp_tac)>>simp[])>>
    irule idx_lt_le>>first_x_assum ACCEPT_TAC)>>
  (* zs = xs permuted into rank order: sorted, and a permutation of xs *)
  qabbrev_tac`zs = GENLIST (λr. xs❲g r❳) n`>>
  `LENGTH zs = n` by simp[Abbr`zs`]>>
  `SORTED (λ(x:int) y. x ≤ y) zs` by (
    simp[Abbr`zs`]>>irule SORTED_le_GENLIST>>rw[]>>first_x_assum irule>>simp[])>>
  `(∀a. a < n ⇒ g a < n) ∧ (∀a b. a < n ∧ b < n ∧ g a = g b ⇒ a = b)` by (
    conj_tac
    >- (rw[]>>qpat_assum`∀r. r < n ⇒ f (g r) = _ ∧ _`(qspec_then`a`mp_tac)>>simp[])
    >- (rw[]>>
        `f (g a) = a ∧ f (g b) = b` by
          (qpat_assum`∀r. r < n ⇒ f (g r) = _ ∧ _`(fn th =>
             mp_tac (Q.SPEC`a` th)>>mp_tac (Q.SPEC`b` th))>>simp[])>>
        metis_tac[]))>>
  `PERM zs xs` by (
    `PERM (GENLIST g n) (COUNT_LIST n)` by (
       `GENLIST g n = MAP g (COUNT_LIST n)` by simp[COUNT_LIST_GENLIST,MAP_GENLIST]>>
       pop_assum SUBST1_TAC>>
       irule PERM_MAP_COUNT_LIST_inj>>rw[])>>
    `zs = MAP (λk. xs❲k❳) (GENLIST g n)` by
      simp[Abbr`zs`,MAP_GENLIST,combinTheory.o_DEF]>>
    `xs = MAP (λk. xs❲k❳) (COUNT_LIST n)` by
      (simp[COUNT_LIST_GENLIST,MAP_GENLIST,combinTheory.o_DEF]>>metis_tac[GENLIST_ID])>>
    ntac 2 (pop_assum SUBST1_TAC)>>
    irule PERM_MAP>>simp[])>>
  `PERM zs ys` by metis_tac[PERM_TRANS]>>
  (* sorted permutations of a multiset coincide *)
  `zs = ys` by metis_tac[sorted_le_PERM_EQ]>>
  `f i < n ∧ g (f i) = i` by simp[]>>
  qpat_x_assum`zs = ys`(SUBST_ALL_TAC o SYM)>>
  simp[Abbr`zs`,EL_GENLIST]
QED

(* reify bridges: flags read back as their intended meaning *)

Theorem reify_bf[local]:
  ALOOKUP cs name = SOME (Sorting (Sort Xs Ys)) ⇒
  (reify_avar cs wi (sort_bf name ip i) ⇔ sort_before wi Xs ip i)
Proof
  rw[reify_avar_def,reify_flag_def]
QED

Theorem reify_pos[local]:
  ALOOKUP cs name = SOME (Sorting (Sort Xs Ys)) ⇒
  (reify_avar cs wi (sort_posbit name i b) ⇔ BIT b (sort_rank wi Xs i))
Proof
  rw[reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

(* width is wide enough: ranks (which are < n) fit in sort_width n bits *)
Theorem sort_width_bound[local]:
  0 < n ⇒ n ≤ 2 ** sort_width n
Proof
  rw[sort_width_def]>>
  `n - 1 < 2 ** LENGTH (bits_of_num (n-1))` by MATCH_ACCEPT_TAC LESS_LENGTH_bits_of_num>>
  decide_tac
QED

Theorem sort_rank_2EXP[local]:
  i < LENGTH Xs ⇒ sort_rank wi Xs i < 2 ** sort_width (LENGTH Xs)
Proof
  rw[]>>
  `sort_rank wi Xs i < LENGTH Xs` by simp[sort_rank_lt]>>
  `LENGTH Xs ≤ 2 ** sort_width (LENGTH Xs)` by (irule sort_width_bound>>simp[])>>
  decide_tac
QED

(* under reify_avar the proof-only bit-sum evaluates to the stable rank *)
Theorem sort_pos_num_reify[local]:
  ALOOKUP cs name = SOME (Sorting (Sort Xs Ys)) ∧ i < LENGTH Xs ⇒
  eval_lin_term (reify_avar cs wi)
    (sort_pos_num name i (sort_width (LENGTH Xs))) = &(sort_rank wi Xs i)
Proof
  rw[]>>
  `sort_rank wi Xs i < 2 ** sort_width (LENGTH Xs)` by (irule sort_rank_2EXP>>simp[])>>
  `∀b. reify_avar cs wi (sort_posbit name i b) ⇔ BIT b (sort_rank wi Xs i)` by
    (rw[]>>drule reify_pos>>simp[])>>
  pop_assum (fn th =>
    simp[sort_pos_num_num_of_bits,th,num_of_bits_GENLIST_BIT,arithmeticTheory.LESS_MOD])
QED

(* under reify_avar the before-flag sum also evaluates to the stable rank *)
Theorem sort_before_sum_reify[local]:
  ALOOKUP cs name = SOME (Sorting (Sort Xs Ys)) ⇒
  eval_lin_term (reify_avar cs wi) (sort_before_sum name (LENGTH Xs) i) =
  &(sort_rank wi Xs i)
Proof
  rw[sort_before_sum_count,sort_rank_def]>>
  AP_TERM_TAC>>
  simp[FILTER_EQ,MEM_COUNT_LIST]>>rw[]>>drule reify_bf>>simp[]
QED

Theorem encode_sort_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Sorting (Sort Xs Ys)) ∧
  sort_sem Xs Ys wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_sort bnd Xs Ys name)
Proof
  rw[]>>
  `LENGTH Xs = LENGTH Ys ∧ PERM (MAP (varc wi) Xs) (MAP (varc wi) Ys) ∧
   SORTED (λ(x:int) y. x ≤ y) (MAP (varc wi) Ys)` by fs[sort_sem_def]>>
  simp[encode_sort_def,cencode_sort_def]>>
  gvs[append_thm,EVERY_APPEND]>>
  rpt conj_tac
  >- (* (a) non-decreasing chain over Ys *)
    (simp[sort_chain_le_def,GSYM encode_increasing_def]>>
     irule encode_increasing_sem_1>>
     simp[increasing_sem_def]>>
     `inc_rel F F = (λ(x:int) y. x ≤ y)` by simp[FUN_EQ_THM]>>
     pop_assum SUBST1_TAC>>first_x_assum ACCEPT_TAC)
  >- (* (b) before-flags pinned to the stable comparison *)
    (simp[sort_bf_lines_sem]>>rw[]>>drule reify_bf>>simp[])
  >- (* (d) rank equation: both sides equal the stable rank *)
    (simp[sort_rank_lines_sem]>>rw[]>>
     `LENGTH Ys = LENGTH Xs` by gvs[]>>gvs[]>>
     DEP_REWRITE_TAC[sort_pos_num_reify,sort_before_sum_reify]>>gvs[])
  >- (* (e) position channel: pos[i]=j forces y[j]=x[i] *)
    (simp[sort_chan_lines_sem]>>rw[]>>
     `j < 2 ** sort_width (LENGTH Ys)` by
       (`LENGTH Ys ≤ 2 ** sort_width (LENGTH Ys)` by (irule sort_width_bound>>gvs[])>>gvs[])>>
     `∀k. k < sort_width (LENGTH Ys) ⇒ (BIT k (sort_rank wi Xs i) ⇔ BIT k j)` by
       (qpat_x_assum`EVERY (lit _) _`mp_tac>>
        simp[sort_guard_lit]>>rw[]>>
        first_x_assum drule>>drule reify_pos>>simp[])>>
     `sort_rank wi Xs i = j` by
       (irule BIT_eq_lt_2EXP>>
        qexists_tac`sort_width (LENGTH Ys)`>>gvs[]>>
        `sort_rank wi Xs i < 2 ** sort_width (LENGTH Xs)` by (irule sort_rank_2EXP>>gvs[])>>
        gvs[])>>
     `EL j (MAP (varc wi) Ys) = EL i (MAP (varc wi) Xs)` by
       (pop_assum (assume_tac o GSYM)>>gvs[]>>irule sort_rank_channel>>gvs[])>>
     gvs[EL_MAP])
QED

(* given the per-flag pinning, the before-flag sum reads back as the rank *)
Theorem sort_before_sum_count_eq[local]:
  (∀ip. ip < LENGTH Xs ⇒ (wb (sort_bf name ip i) ⇔ sort_before wi Xs ip i)) ⇒
  eval_lin_term wb (sort_before_sum name (LENGTH Xs) i) = &(sort_rank wi Xs i)
Proof
  strip_tac>>
  rw[sort_before_sum_count,sort_rank_def]>>
  AP_TERM_TAC>>
  simp[FILTER_EQ,MEM_COUNT_LIST]>>rw[]>>
  first_x_assum drule>>simp[]
QED

(* a bijection on [0,n) that channels xs through ys witnesses a permutation *)
Theorem PERM_from_channel[local]:
  LENGTH xs = LENGTH (ys:'a list) ∧
  (∀i. i < LENGTH xs ⇒ f i < LENGTH xs) ∧
  (∀i j. i < LENGTH xs ∧ j < LENGTH xs ∧ f i = f j ⇒ i = j) ∧
  (∀i. i < LENGTH xs ⇒ EL (f i) ys = EL i xs) ⇒
  PERM xs ys
Proof
  strip_tac>>
  `xs = MAP (λk. EL k ys) (MAP f (COUNT_LIST (LENGTH xs)))` by
    (irule LIST_EQ>>rw[EL_MAP,EL_COUNT_LIST,LENGTH_COUNT_LIST])>>
  pop_assum SUBST1_TAC>>
  `PERM (MAP (λk. EL k ys) (MAP f (COUNT_LIST (LENGTH xs))))
        (MAP (λk. EL k ys) (COUNT_LIST (LENGTH xs)))` by
    (irule PERM_MAP>>irule PERM_MAP_COUNT_LIST_inj>>rpt conj_tac>>
     first_assum ACCEPT_TAC)>>
  `MAP (λk. EL k ys) (COUNT_LIST (LENGTH xs)) = ys` by
    (irule MAP_EL_COUNT_LIST_self>>first_assum ACCEPT_TAC)>>
  gvs[]
QED

Theorem encode_sort_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_sort bnd Xs Ys name) ⇒
  sort_sem Xs Ys wi
Proof
  strip_tac>>
  `LENGTH Xs = LENGTH Ys` by
    (CCONTR_TAC>>gvs[encode_sort_def,cencode_sort_def,cfalse_constr_def])>>
  `LENGTH Ys = LENGTH Xs` by simp[]>>
  qpat_x_assum`LENGTH Xs = LENGTH Ys`kall_tac>>
  fs[encode_sort_def,cencode_sort_def,append_thm,EVERY_APPEND]>>
  fs[sort_rank_lines_sem]>>
  drule sort_bf_lines_sem>>disch_then(fn th => fs[th])>>
  `∀i j. i < LENGTH Xs ∧ j < LENGTH Ys ⇒
     EVERY (lit wb) (sort_guard name (sort_width (LENGTH Xs)) i j) ⇒
     varc wi (EL j Ys) = varc wi (EL i Xs)` by
    metis_tac[sort_chan_lines_sem]>>
  (* (a) the non-decreasing chain gives SORTED *)
  `SORTED (λ(x:int) y. x ≤ y) (MAP (varc wi) Ys)` by (
    qpat_x_assum`EVERY _ (abstr (sort_chain_le _ _))`mp_tac>>
    simp[sort_chain_le_def,GSYM encode_increasing_def]>>
    strip_tac>>drule encode_increasing_sem_2>>
    simp[increasing_sem_def]>>
    `inc_rel F F = (λ(x:int) y. x ≤ y)` by simp[FUN_EQ_THM]>>
    simp[])>>
  (* (b)+(d)+(e): the sorted permutation places x[i] at its stable rank *)
  `∀i. i < LENGTH Xs ⇒
     EL (sort_rank wi Xs i) (MAP (varc wi) Ys) = EL i (MAP (varc wi) Xs)` by (
    rw[]>>
    `sort_rank wi Xs i < LENGTH Xs` by simp[sort_rank_lt]>>
    `sort_rank wi Xs i < 2 ** sort_width (LENGTH Xs)` by (irule sort_rank_2EXP>>simp[])>>
    `eval_lin_term wb (sort_before_sum name (LENGTH Xs) i) = &(sort_rank wi Xs i)` by (
      irule sort_before_sum_count_eq>>rw[]>>
      qpat_x_assum`∀ip i. _ ⇒ (wb _ ⇔ _)`(qspecl_then[`ip`,`i`]mp_tac)>>simp[])>>
    `num_of_bits (GENLIST (λb. wb (sort_posbit name i b)) (sort_width (LENGTH Xs))) =
       sort_rank wi Xs i` by (
      qpat_x_assum`∀i. _ ⇒ eval_lin_term _ (sort_pos_num _ _ _) = _`
        (qspec_then`i`mp_tac)>>simp[sort_pos_num_num_of_bits]>>strip_tac>>
      gvs[integerTheory.INT_INJ])>>
    `EVERY (lit wb) (sort_guard name (sort_width (LENGTH Xs)) i (sort_rank wi Xs i))` by (
      simp[sort_guard_lit]>>rw[]>>
      qpat_x_assum`num_of_bits _ = sort_rank wi Xs i`(SUBST1_TAC o SYM)>>
      DEP_REWRITE_TAC[BIT_num_of_bits_EL]>>simp[EL_GENLIST])>>
    qpat_x_assum`∀i j. _ ⇒ _ ⇒ varc _ _ = varc _ _`
      (qspecl_then[`i`,`sort_rank wi Xs i`]mp_tac)>>
    gvs[EL_MAP])>>
  (* PERM follows from the channel via the stable-rank bijection *)
  `PERM (MAP (varc wi) Xs) (MAP (varc wi) Ys)` by (
    irule PERM_from_channel>>conj_tac
    >- (qexists_tac`sort_rank wi Xs`>>rw[]>>gvs[LENGTH_MAP]>>
        metis_tac[sort_rank_lt,sort_rank_inj])
    >- gvs[LENGTH_MAP])>>
  gvs[sort_sem_def]
QED

Theorem cencode_sort_sem:
  valid_assignment bnd wi ∧
  cencode_sort bnd Xs Ys name = es ⇒
  enc_rel wi es (encode_sort bnd Xs Ys name) ec ec
Proof
  rw[encode_sort_def]
QED

(* ArgSort: y[j] is a proof-only signed value in two's-complement layout (sign
   bit «ysgn», positive bits «y», tie-break «yge»), matching ilp_to_pb's
   encode_ivar. *)

Definition argsort_ybit_def[simp]:
  argsort_ybit name j b = INR (name, Values [&j; &b] (SOME «y»))
End
Definition argsort_ysgn_def[simp]:
  argsort_ysgn name j = INR (name, Values [&j] (SOME «ysgn»))
End
Definition argsort_yge_def[simp]:
  argsort_yge name j = INR (name, Values [&j] (SOME «yge»))
End

(* signed (two's-complement) bit-sum for y[j] over an h-bit layout *)
Definition argsort_y_num_def:
  argsort_y_num name j h =
    (-&(2 ** h), Pos (argsort_ysgn name j)) ::
    GENLIST (λb. (&(2 ** b), Pos (argsort_ybit name j b))) h
End

(* two's-complement width (comp,h) for y: covers [min lb(x), max ub(x)] over the
   Xs entries (seed 0 keeps 0 in range, so comp ⇔ some x can be negative).  Each
   bnd lookup is the var-or-const dispatch (cf. scheduling's varc_bnd). *)
Definition argsort_width_def:
  argsort_width bnd Xs =
  let bnds = MAP (λx. case x of INL v => bnd v | INR c => (c,c)) Xs in
  let lb = FOLDR int_min 0 (MAP FST bnds) in
  let ub = FOLDR int_max 0 (MAP SND bnds) in
  bit_width (λu:unit. (lb,ub)) ()
End

(* Mixed constraint builders: a Boolean-side linear term compared against a
   varc, another Boolean-side term, or a constant. *)

(* eval_lin_term wb ys ≥ varc wi X *)
Definition lin_ge_varc_def:
  lin_ge_varc ys X =
  case X of INL v => ([(-1i,v)], ys, 0i)
          | INR c => ([], ys, c)
End

Theorem lin_ge_varc_sem[simp]:
  iconstraint_sem (lin_ge_varc ys X) (wi,wb) ⇔
  eval_lin_term wb ys ≥ varc wi X
Proof
  Cases_on`X`>>
  rw[lin_ge_varc_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def]>>
  intLib.ARITH_TAC
QED

(* eval_lin_term wb ys ≤ varc wi X *)
Definition lin_le_varc_def:
  lin_le_varc ys X =
  case X of INL v => ([(1i,v)], flip_coeffs ys, 0i)
          | INR c => ([], flip_coeffs ys, -c)
End

Theorem lin_le_varc_sem[simp]:
  iconstraint_sem (lin_le_varc ys X) (wi,wb) ⇔
  eval_lin_term wb ys ≤ varc wi X
Proof
  Cases_on`X`>>
  rw[lin_le_varc_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,varc_def,
     eval_lin_term_flip_coeffs]>>
  intLib.ARITH_TAC
QED

(* eval_lin_term wb ys ≥ eval_lin_term wb zs *)
Definition lin_ge_lin_def:
  lin_ge_lin ys zs = ([], ys ++ flip_coeffs zs, 0i)
End

Theorem lin_ge_lin_sem[simp]:
  iconstraint_sem (lin_ge_lin ys zs) (wi,wb) ⇔
  eval_lin_term wb ys ≥ eval_lin_term wb zs
Proof
  rw[lin_ge_lin_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,
     eval_lin_term_append,eval_lin_term_flip_coeffs]>>
  intLib.ARITH_TAC
QED

(* eval_lin_term wb ys ≥ c *)
Definition lin_ge_const_def:
  lin_ge_const ys (c:int) = ([], ys, c)
End

Theorem lin_ge_const_sem[simp]:
  iconstraint_sem (lin_ge_const ys c) (wi,wb) ⇔ eval_lin_term wb ys ≥ c
Proof
  rw[lin_ge_const_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def]
QED

(* eval_lin_term wb ys ≤ c *)
Definition lin_le_const_def:
  lin_le_const ys (c:int) = ([], flip_coeffs ys, -c)
End

Theorem lin_le_const_sem[simp]:
  iconstraint_sem (lin_le_const ys c) (wi,wb) ⇔ eval_lin_term wb ys ≤ c
Proof
  rw[lin_le_const_def,iconstraint_sem_def,eval_ilin_term_def,iSUM_def,
     eval_lin_term_flip_coeffs]>>
  intLib.ARITH_TAC
QED

(* ArgSort encoder: runs Sort's rank core on Xs over an internal proof-only
   signed value array y, then links the permutation Ps. *)

(* wrap a raw iconstraint list into the app_list container with names *)
Definition cwrap_def:
  cwrap name tag cs =
  List (MAPi (λi c. (SOME (mk_name name (tag ^ toString i)), c)) cs)
End

Theorem abstr_cwrap[simp]:
  abstr (cwrap name tag cs) = cs
Proof
  rw[cwrap_def]>>
  simp[combinTheory.o_DEF,LIST_EQ_REWRITE,indexedListsTheory.EL_MAPi]
QED

(* (a) the internal value array is non-decreasing: y[j] ≤ y[j+1] *)
Definition argsort_chain_le_def:
  argsort_chain_le name h n =
  List (MAP (λj.
    (SOME (mk_name name («yle» ^ toString j)),
     lin_ge_lin (argsort_y_num name (j+1) h) (argsort_y_num name j h)))
    (COUNT_LIST (n-1)))
End

(* translation-friendly form: guard the n-1 subtraction (cf. sort_width_alt) *)
Theorem argsort_chain_le_alt:
  argsort_chain_le name h n =
  List (MAP (λj.
    (SOME (mk_name name («yle» ^ toString j)),
     lin_ge_lin (argsort_y_num name (j+1) h) (argsort_y_num name j h)))
    (COUNT_LIST (if n = 0 then 0 else n - 1)))
Proof
  rw[argsort_chain_le_def]>>Cases_on`n`>>gvs[]
QED

(* (e) position channel: whenever pos[i]'s bits spell j, y[j] = x[i] *)
Definition argsort_pos_chan_def:
  argsort_pos_chan bnd name w h Xs =
  flat_app (MAPi (λi xi.
    flat_app (MAP (λj.
      Append
        (List [(SOME (mk_name name («acle» ^ toString i ^ «_» ^ toString j)),
                 bits_imply bnd (sort_guard name w i j)
                   (lin_le_varc (argsort_y_num name j h) xi))])
        (List [(SOME (mk_name name («acge» ^ toString i ^ «_» ^ toString j)),
                 bits_imply bnd (sort_guard name w i j)
                   (lin_ge_varc (argsort_y_num name j h) xi))]))
      (COUNT_LIST (LENGTH Xs))))
    Xs)
End

(* range: offset ≤ p[j] ≤ offset+n−1 *)
Definition argsort_p_range_def:
  argsort_p_range name Ps offset n =
  flat_app (MAPi (λj pj.
    List [(SOME (mk_name name («plb» ^ toString j)),
            mk_constraint_one_ge 1 pj offset);
          (SOME (mk_name name («pub» ^ toString j)),
            mk_constraint_one_ge (-1) pj (-(offset + &n - 1)))])
    Ps)
End

(* equality flags: pin [p[j] = offset+k] (and the needed Ge flags) *)
Definition argsort_eq_flags_def:
  argsort_eq_flags bnd name Ps offset n =
  flat_app (MAPi (λj pj.
    flat_app (MAP (λk.
      cwrap name («peq» ^ toString j ^ «_» ^ toString k)
        (encode_full_eq bnd pj (offset + &k)))
      (COUNT_LIST n)))
    Ps)
End

(* (5) permutation: each value offset+k is taken by at most one position *)
Definition argsort_perm_def:
  argsort_perm name Ps offset n =
  flat_app (MAP (λk.
    cat_most_one name («perm» ^ toString k)
      (MAP (λpj. Pos (INL (Eq pj (offset + &k)))) Ps))
    (COUNT_LIST n))
End

(* (6) value channel: (p[j] = offset+k) → y[j] = x[k] *)
Definition argsort_valchan_def:
  argsort_valchan bnd name h Xs Ps offset =
  flat_app (MAPi (λj pj.
    flat_app (MAPi (λk xk.
      Append
        (List [(SOME (mk_name name («vcle» ^ toString j ^ «_» ^ toString k)),
                 bits_imply bnd [Pos (INL (Eq pj (offset + &k)))]
                   (lin_le_varc (argsort_y_num name j h) xk))])
        (List [(SOME (mk_name name («vcge» ^ toString j ^ «_» ^ toString k)),
                 bits_imply bnd [Pos (INL (Eq pj (offset + &k)))]
                   (lin_ge_varc (argsort_y_num name j h) xk))]))
      Xs))
    Ps)
End

(* (7) rank channel: (p[j] = offset+k) → pos[k] = j *)
Definition argsort_rankchan_def:
  argsort_rankchan bnd name w Ps offset n =
  flat_app (MAPi (λj pj.
    flat_app (MAP (λk.
      Append
        (List [(SOME (mk_name name («rcge» ^ toString j ^ «_» ^ toString k)),
                 bits_imply bnd [Pos (INL (Eq pj (offset + &k)))]
                   (lin_ge_const (sort_pos_num name k w) (&j)))])
        (List [(SOME (mk_name name («rcle» ^ toString j ^ «_» ^ toString k)),
                 bits_imply bnd [Pos (INL (Eq pj (offset + &k)))]
                   (lin_le_const (sort_pos_num name k w) (&j)))]))
      (COUNT_LIST n)))
    Ps)
End

(* (8) stable tie-break: eq_j ⇔ y[j] ≥ y[j+1]; eq_j → p[j]+1 ≤ p[j+1] *)
Definition argsort_tiebreak_def:
  argsort_tiebreak bnd name h Ps n =
  Append
    (flat_app (MAP (λj.
       cbimply_var bnd (argsort_yge name j)
         (lin_ge_lin (argsort_y_num name j h) (argsort_y_num name (j+1) h)))
       (COUNT_LIST (n-1))))
    (flat_app (MAPi (λj (pj,pj1).
       List [(SOME (mk_name name («tb» ^ toString j)),
              bits_imply bnd [Pos (argsort_yge name j)]
                (mk_constraint_ge 1 pj1 (-1) pj 1))])
       (adj_pairs Ps)))
End

(* translation-friendly form: guard the n-1 subtraction (cf. sort_width_alt) *)
Theorem argsort_tiebreak_alt:
  argsort_tiebreak bnd name h Ps n =
  Append
    (flat_app (MAP (λj.
       cbimply_var bnd (argsort_yge name j)
         (lin_ge_lin (argsort_y_num name j h) (argsort_y_num name (j+1) h)))
       (COUNT_LIST (if n = 0 then 0 else n - 1))))
    (flat_app (MAPi (λj (pj,pj1).
       List [(SOME (mk_name name («tb» ^ toString j)),
              bits_imply bnd [Pos (argsort_yge name j)]
                (mk_constraint_ge 1 pj1 (-1) pj 1))])
       (adj_pairs Ps)))
Proof
  rw[argsort_tiebreak_def]>>Cases_on`n`>>gvs[]
QED

Definition cencode_argsort_def:
  cencode_argsort bnd Xs Ps offset name =
  let n = LENGTH Xs in
  if LENGTH Ps ≠ n then cfalse_constr
  else
    let w = sort_width n in
    let h = SND (argsort_width bnd Xs) in
    Append (argsort_chain_le name h n)
    (Append (sort_bf_lines bnd name Xs)
    (Append (sort_rank_lines name w n)
    (Append (argsort_pos_chan bnd name w h Xs)
    (Append (argsort_p_range name Ps offset n)
    (Append (argsort_eq_flags bnd name Ps offset n)
    (Append (argsort_perm name Ps offset n)
    (Append (argsort_valchan bnd name h Xs Ps offset)
    (Append (argsort_rankchan bnd name w Ps offset n)
            (argsort_tiebreak bnd name h Ps n)))))))))
End

Definition encode_argsort_def:
  encode_argsort bnd Xs Ps offset name = abstr (cencode_argsort bnd Xs Ps offset name)
End

(* ArgSort block-level semantics (reify-free): each block holds iff its
   intended relation over (wi,wb) does. *)

(* (a) the value array is non-decreasing *)
Theorem argsort_chain_le_sem[local]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_chain_le name h n)) ⇔
  ∀j. j < n-1 ⇒
    eval_lin_term wb (argsort_y_num name j h) ≤
    eval_lin_term wb (argsort_y_num name (j+1) h)
Proof
  simp[argsort_chain_le_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MEM_COUNT_LIST,
       integerTheory.int_ge]
QED

(* range: every p[j] lies in [offset, offset+n−1] *)
Theorem argsort_p_range_sem[local]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_p_range name Ps offset n)) ⇔
  ∀j. j < LENGTH Ps ⇒
    offset ≤ varc wi (EL j Ps) ∧ varc wi (EL j Ps) ≤ offset + &n - 1
Proof
  simp[argsort_p_range_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,combinTheory.o_DEF]>>
  rw[]>>eq_tac>>rw[]>>first_x_assum drule>>rw[]>>intLib.ARITH_TAC
QED

(* (e) position channel: when pos[i]'s bits spell j, y[j] = x[i] *)
Theorem argsort_pos_chan_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_pos_chan bnd name w h Xs)) ⇔
   ∀i j. i < LENGTH Xs ∧ j < LENGTH Xs ⇒
     EVERY (lit wb) (sort_guard name w i j) ⇒
       eval_lin_term wb (argsort_y_num name j h) = varc wi (EL i Xs))
Proof
  strip_tac>>
  simp[argsort_pos_chan_def, EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,combinTheory.o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAP,MEM_COUNT_LIST,PULL_EXISTS]>>
  `∀g (a:int) b. ((g ⇒ a ≤ b) ∧ (g ⇒ a ≥ b)) ⇔ (g ⇒ a = b)` by
    (rw[]>>eq_tac>>rw[]>>intLib.ARITH_TAC)>>
  metis_tac[]
QED

(* equality flags: pin [p[j] = offset+k] and the bracketing Ge flags *)
Theorem argsort_eq_flags_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_eq_flags bnd name Ps offset n)) ⇔
   ∀j k. j < LENGTH Ps ∧ k < n ⇒
     (wb (INL (Ge (EL j Ps) (offset + &k))) ⇔ varc wi (EL j Ps) ≥ offset + &k) ∧
     (wb (INL (Ge (EL j Ps) (offset + &k + 1))) ⇔ varc wi (EL j Ps) ≥ offset + &k + 1) ∧
     (wb (INL (Eq (EL j Ps) (offset + &k))) ⇔ varc wi (EL j Ps) = offset + &k))
Proof
  strip_tac>>
  simp[argsort_eq_flags_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,combinTheory.o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAP,MEM_COUNT_LIST,PULL_EXISTS]>>
  metis_tac[encode_full_eq_sem]
QED

(* (5) permutation: each value offset+k is taken by at most one position *)
Theorem argsort_perm_sem[local]:
  EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_perm name Ps offset n)) ⇔
  ∀k. k < n ⇒
    iSUM (MAP (b2i ∘ lit wb)
      (MAP (λpj. Pos (INL (Eq pj (offset + &k)))) Ps)) ≤ 1
Proof
  simp[argsort_perm_def,EVERY_FLAT]>>
  simp[EVERY_MAP,EVERY_MEM,MEM_COUNT_LIST,cat_most_one_def]
QED

(* (6) value channel: (p[j] = offset+k) → y[j] = x[k] *)
Theorem argsort_valchan_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_valchan bnd name h Xs Ps offset)) ⇔
   ∀j k. j < LENGTH Ps ∧ k < LENGTH Xs ⇒
     wb (INL (Eq (EL j Ps) (offset + &k))) ⇒
       eval_lin_term wb (argsort_y_num name j h) = varc wi (EL k Xs))
Proof
  strip_tac>>
  simp[argsort_valchan_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,combinTheory.o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS]>>
  `∀g (a:int) b. ((g ⇒ a ≤ b) ∧ (g ⇒ a ≥ b)) ⇔ (g ⇒ a = b)` by
    (rw[]>>eq_tac>>rw[]>>intLib.ARITH_TAC)>>
  simp[lit_def]>>metis_tac[]
QED

(* (7) rank channel: (p[j] = offset+k) → pos[k] = j *)
Theorem argsort_rankchan_sem[local]:
  valid_assignment bnd wi ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_rankchan bnd name w Ps offset n)) ⇔
   ∀j k. j < LENGTH Ps ∧ k < n ⇒
     wb (INL (Eq (EL j Ps) (offset + &k))) ⇒
       eval_lin_term wb (sort_pos_num name k w) = &j)
Proof
  strip_tac>>
  simp[argsort_rankchan_def,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAPi,PULL_EXISTS,combinTheory.o_DEF]>>
  simp[EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAP,MEM_COUNT_LIST,PULL_EXISTS]>>
  `∀g (a:int) b. ((g ⇒ a ≥ b) ∧ (g ⇒ a ≤ b)) ⇔ (g ⇒ a = b)` by
    (rw[]>>eq_tac>>rw[]>>intLib.ARITH_TAC)>>
  simp[lit_def]>>metis_tac[]
QED

(* (8) tie-break: eq_j ⇔ y[j] ≥ y[j+1]; eq_j → p[j]+1 ≤ p[j+1] *)
Theorem argsort_tiebreak_sem[local]:
  valid_assignment bnd wi ∧ LENGTH Ps = n ⇒
  (EVERY (λx. iconstraint_sem x (wi,wb)) (abstr (argsort_tiebreak bnd name h Ps n)) ⇔
   (∀j. j < n-1 ⇒
      (eval_lin_term wb (argsort_y_num name j h) ≥
       eval_lin_term wb (argsort_y_num name (j+1) h) ⇔
       wb (argsort_yge name j))) ∧
   (∀j. j < n-1 ⇒
      wb (argsort_yge name j) ⇒
      varc wi (EL (j+1) Ps) ≥ varc wi (EL j Ps) + 1))
Proof
  strip_tac>>
  simp[argsort_tiebreak_def,EVERY_APPEND,EVERY_FLAT]>>
  simp[Once EVERY_MEM,MEM_MAP,MEM_COUNT_LIST,PULL_EXISTS,
       abstr_cbimply_var,EVERY_REVERSE,bimply_bit_sem,lit_def]>>
  simp[Once EVERY_MEM,indexedListsTheory.MEM_MAPi,MEM_COUNT_LIST,PULL_EXISTS,
       LENGTH_adj_pairs,lit_def]>>
  `∀a b:int. (a + -1*b ≥ 1) ⇔ (a ≥ b + 1)` by (rw[]>>intLib.ARITH_TAC)>>
  simp[EL_adj_pairs]
QED

(* ArgSort soundness: reify bridges, the rank↔stable-sort crux, then the two
   directions. *)

Theorem reify_argsort_bf[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ⇒
  (reify_avar cs wi (sort_bf name ip i) ⇔ sort_before wi Xs ip i)
Proof
  rw[reify_avar_def,reify_flag_def]
QED

Theorem reify_argsort_pos[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ⇒
  (reify_avar cs wi (sort_posbit name i b) ⇔ BIT b (sort_rank wi Xs i))
Proof
  rw[reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

Theorem reify_argsort_y[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ⇒
  (reify_avar cs wi (argsort_ybit name j b) ⇔ int_bit b (argsort_yval wi Xs j))
Proof
  rw[reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

Theorem reify_argsort_ysgn[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ⇒
  (reify_avar cs wi (argsort_ysgn name j) ⇔ argsort_yval wi Xs j < 0)
Proof
  rw[reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

Theorem reify_argsort_yge[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ⇒
  (reify_avar cs wi (argsort_yge name j) ⇔
   argsort_yval wi Xs j ≥ argsort_yval wi Xs (j+1))
Proof
  rw[reify_avar_def,reify_flag_def,integerTheory.NUM_OF_INT]
QED

(* stable_lt is the lexicographic strict order, hence transitive *)
Theorem stable_lt_transitive[local]:
  transitive stable_lt
Proof
  `stable_lt = ($< LEX $<)` by
    simp[FUN_EQ_THM,FORALL_PROD,stable_lt_def,pairTheory.LEX_DEF]>>
  pop_assum SUBST1_TAC>>
  irule pairTheory.transitive_LEX>>
  conj_tac
  >- (simp[relationTheory.transitive_def]>>intLib.ARITH_TAC)
  >- (simp[relationTheory.transitive_def]>>decide_tac)
QED

(* stable_lt on (value,index) pairs is the stable rank order *)
Theorem stable_lt_pair_idx[local]:
  i < LENGTH Xs ∧ j < LENGTH Xs ⇒
  (stable_lt (varc wi (EL i Xs), i) (varc wi (EL j Xs), j) ⇔
   sort_rank wi Xs i < sort_rank wi Xs j)
Proof
  rw[]>>
  `stable_lt (varc wi (EL i Xs), i) (varc wi (EL j Xs), j) ⇔
   idx_lt (MAP (varc wi) Xs) i j` by simp[stable_lt_def,idx_lt_def,EL_MAP]>>
  pop_assum SUBST1_TAC>>
  irule sort_rank_card_lt>>simp[]
QED

(* reading the (value,index) pair at position a along qs orders by the stable
   rank of the original index qs[a] *)
Theorem stable_lt_idx_equiv[local]:
  LENGTH qs = n ∧ (∀j. j < n ⇒ EL j qs < n) ∧ LENGTH Xs = n ⇒
  ∀a b. a < n ∧ b < n ⇒
    (stable_lt (EL a (MAP (λq. (EL q (MAP (varc wi) Xs), q)) qs))
               (EL b (MAP (λq. (EL q (MAP (varc wi) Xs), q)) qs)) ⇔
     sort_rank wi Xs (EL a qs) < sort_rank wi Xs (EL b qs))
Proof
  strip_tac>>rpt strip_tac>>
  DEP_REWRITE_TAC[EL_MAP]>>
  gvs[]>>
  irule stable_lt_pair_idx>>
  gvs[]
QED

(* SORTED of a list whose pairwise order matches the stable rank order is the
   pointwise rank-increasing condition *)
Theorem sorted_stable_lt_rank[local]:
  LENGTH ll = n ∧
  (∀a b. a < n ∧ b < n ⇒
     (stable_lt (EL a ll) (EL b ll) ⇔
      sort_rank wi Xs (EL a qs) < sort_rank wi Xs (EL b qs))) ⇒
  (SORTED stable_lt ll ⇔
   ∀a b. a < b ∧ b < n ⇒
     sort_rank wi Xs (EL a qs) < sort_rank wi Xs (EL b qs))
Proof
  strip_tac>>
  DEP_REWRITE_TAC[SORTED_EL_LESS]>>
  simp[stable_lt_transitive]
QED

(* Crux: for a permutation qs of [0,n), reading the (value,index) pairs along
   qs is stable-sorted iff qs is the inverse of the stable rank. *)
Theorem argsort_rank_inv[local]:
  LENGTH Xs = n ∧ PERM qs (COUNT_LIST n) ⇒
  (SORTED stable_lt (MAP (λq. (EL q (MAP (varc wi) Xs), q)) qs) ⇔
   ∀j. j < n ⇒ sort_rank wi Xs (EL j qs) = j)
Proof
  strip_tac>>
  `LENGTH qs = n` by metis_tac[PERM_LENGTH,LENGTH_COUNT_LIST]>>
  `∀j. j < n ⇒ EL j qs < n` by (rw[]>>irule PERM_COUNT_LIST_EL_lt>>simp[])>>
  qmatch_goalsub_abbrev_tac`SORTED _ ll`>>
  `LENGTH ll = n` by simp[Abbr`ll`,LENGTH_MAP]>>
  `∀a b. a < n ∧ b < n ⇒
     (stable_lt (EL a ll) (EL b ll) ⇔
      sort_rank wi Xs (EL a qs) < sort_rank wi Xs (EL b qs))` by (
    qunabbrev_tac`ll`>>match_mp_tac stable_lt_idx_equiv>>simp[])>>
  `SORTED stable_lt ll ⇔
     ∀a b. a < b ∧ b < n ⇒
       sort_rank wi Xs (EL a qs) < sort_rank wi Xs (EL b qs)` by (
    match_mp_tac sorted_stable_lt_rank>>conj_tac>>first_assum ACCEPT_TAC)>>
  pop_assum SUBST1_TAC>>
  ho_match_mp_tac strict_mono_iff_id>>
  rw[]>>
  `EL j qs < LENGTH Xs` by fs[]>>
  drule sort_rank_lt>>fs[]
QED

Theorem encode_argsort_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_argsort bnd Xs Ps offset name) ⇒
  argsort_sem Xs Ps offset wi
Proof
  strip_tac>>
  `LENGTH Ps = LENGTH Xs` by
    (CCONTR_TAC>>gvs[encode_argsort_def,cencode_argsort_def,cfalse_constr_def])>>
  fs[encode_argsort_def,cencode_argsort_def,append_thm,EVERY_APPEND]>>
  `∀j. j < LENGTH Ps ⇒
     offset ≤ varc wi (EL j Ps) ∧ varc wi (EL j Ps) ≤ offset + &LENGTH Xs - 1` by
    metis_tac[argsort_p_range_sem]>>
  `∀j k. j < LENGTH Ps ∧ k < LENGTH Xs ⇒
     (wb (INL (Eq (EL j Ps) (offset + &k))) ⇔ varc wi (EL j Ps) = offset + &k)` by
    metis_tac[argsort_eq_flags_sem]>>
  `∀j k. j < LENGTH Ps ∧ k < LENGTH Xs ⇒
     wb (INL (Eq (EL j Ps) (offset + &k))) ⇒
       eval_lin_term wb (sort_pos_num name k (sort_width (LENGTH Xs))) = &j` by
    metis_tac[argsort_rankchan_sem]>>
  drule sort_bf_lines_sem>>disch_then(fn th => fs[th])>>
  fs[sort_rank_lines_sem]>>
  `∀k. k < LENGTH Xs ⇒
     eval_lin_term wb (sort_pos_num name k (sort_width (LENGTH Xs))) =
       &(sort_rank wi Xs k)` by (
    rw[]>>
    `eval_lin_term wb (sort_before_sum name (LENGTH Xs) k) = &(sort_rank wi Xs k)` by (
      irule sort_before_sum_count_eq>>rw[]>>
      qpat_x_assum`∀ip i. _ ⇒ (wb _ ⇔ _)`(qspecl_then[`ip`,`k`]mp_tac)>>simp[])>>
    metis_tac[])>>
  rpt (qpat_x_assum`EVERY _ _`kall_tac)>>
  simp[argsort_sem_def]>>
  qmatch_goalsub_abbrev_tac`PERM qs _`>>
  `LENGTH qs = LENGTH Xs` by simp[Abbr`qs`]>>
  `∀j. j < LENGTH Xs ⇒ &(EL j qs) = varc wi (EL j Ps) − offset` by (
    rw[]>>
    `j < LENGTH Ps` by fs[]>>
    `offset ≤ varc wi (EL j Ps)` by (
      qpat_x_assum`∀j. j < LENGTH Ps ⇒ offset ≤ _ ∧ _`(qspec_then`j`mp_tac)>>simp[])>>
    qunabbrev_tac`qs`>>DEP_REWRITE_TAC[EL_MAP]>>
    simp[integerTheory.INT_OF_NUM]>>fs[]>>
    simp[integerTheory.INT_SUB_LE])>>
  `∀j. j < LENGTH Xs ⇒
     EL j qs < LENGTH Xs ∧ varc wi (EL j Ps) = offset + &(EL j qs)` by (
    rw[]>>
    `&(EL j qs) = varc wi (EL j Ps) − offset` by (first_x_assum irule>>simp[])>>
    `j < LENGTH Ps` by fs[]>>
    `varc wi (EL j Ps) ≤ offset + &LENGTH Xs − 1` by (
      qpat_x_assum`∀j. j < LENGTH Ps ⇒ offset ≤ _ ∧ _`(qspec_then`j`mp_tac)>>fs[])>>
    `&(EL j qs):int < &LENGTH Xs` by (
      qpat_x_assum`varc wi (EL j Ps) ≤ _`mp_tac>>
      qpat_x_assum`&(EL j qs) = _`mp_tac>>
      rpt (pop_assum kall_tac)>>intLib.ARITH_TAC)>>
    fs[integerTheory.INT_LT])>>
  qpat_x_assum`∀ip i. _ ⇒ (wb _ ⇔ sort_before _ _ _ _)`kall_tac>>
  qpat_x_assum`∀i. i < LENGTH Xs ⇒ eval_lin_term _ _ = eval_lin_term _ _`kall_tac>>
  qpat_x_assum`∀j. j < LENGTH Xs ⇒ &(EL j qs) = _`kall_tac>>
  `∀j. j < LENGTH Xs ⇒ sort_rank wi Xs (EL j qs) = j` by (
    rw[]>>
    `EL j qs < LENGTH Xs ∧ varc wi (EL j Ps) = offset + &(EL j qs)` by (
      qpat_x_assum`∀j. j < LENGTH Xs ⇒ EL j qs < LENGTH Xs ∧ _`
        (qspec_then`j`mp_tac)>>simp[])>>
    `j < LENGTH Ps` by fs[]>>
    `wb (INL (Eq (EL j Ps) (offset + &(EL j qs))))` by (
      qpat_x_assum`∀j k. _ ⇒ (wb _ ⇔ _)`(qspecl_then[`j`,`EL j qs`]mp_tac)>>fs[])>>
    `eval_lin_term wb (sort_pos_num name (EL j qs) (sort_width (LENGTH Xs))) = &j` by (
      qpat_x_assum`∀j k. _ ⇒ wb _ ⇒ _`(qspecl_then[`j`,`EL j qs`]mp_tac)>>fs[])>>
    `eval_lin_term wb (sort_pos_num name (EL j qs) (sort_width (LENGTH Xs))) =
       &(sort_rank wi Xs (EL j qs))` by (
      qpat_x_assum`∀k. k < LENGTH Xs ⇒ eval_lin_term _ _ = &sort_rank _ _ _`
        (qspec_then`EL j qs`mp_tac)>>fs[])>>
    gvs[integerTheory.INT_INJ])>>
  `PERM qs (COUNT_LIST (LENGTH Xs))` by (
    irule PERM_inj_COUNT_LIST>>simp[]>>rw[]>>
    `sort_rank wi Xs (EL i qs) = i ∧ sort_rank wi Xs (EL j qs) = j` by
      (conj_tac>>first_x_assum irule>>simp[])>>
    metis_tac[])>>
  rpt conj_tac
  >- (simp[EVERY_MAP,EVERY_EL]>>rw[]>>
      qpat_x_assum`∀j. j < LENGTH Ps ⇒ offset ≤ _ ∧ _`(qspec_then`n'`mp_tac)>>
      simp[]>>intLib.ARITH_TAC)
  >- first_assum ACCEPT_TAC
  >- metis_tac[argsort_rank_inv]
QED

(* ArgSort soundness (sem_1): every emitted constraint holds under the witness
   wb = reify_avar cs wi. *)

(* the order statistic at the rank of i is exactly x[i] *)
Theorem argsort_yval_rank[local]:
  i < LENGTH Xs ⇒ argsort_yval wi Xs (sort_rank wi Xs i) = varc wi (EL i Xs)
Proof
  rw[argsort_yval_def]>>
  `(@k. k < LENGTH Xs ∧ sort_rank wi Xs k = sort_rank wi Xs i) = i` by (
    SELECT_ELIM_TAC>>rw[]
    >- (qexists`i`>>simp[])>>
    metis_tac[sort_rank_inj])>>
  simp[]
QED

(* under reify the proof-only bit-sum / before-flag sum read back as the rank *)
Theorem sort_pos_num_reify_argsort[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ∧ i < LENGTH Xs ⇒
  eval_lin_term (reify_avar cs wi)
    (sort_pos_num name i (sort_width (LENGTH Xs))) = &(sort_rank wi Xs i)
Proof
  rw[]>>
  `sort_rank wi Xs i < 2 ** sort_width (LENGTH Xs)` by (irule sort_rank_2EXP>>simp[])>>
  `∀b. reify_avar cs wi (sort_posbit name i b) ⇔ BIT b (sort_rank wi Xs i)` by
    (rw[]>>drule reify_argsort_pos>>simp[])>>
  pop_assum (fn th =>
    simp[sort_pos_num_num_of_bits,th,num_of_bits_GENLIST_BIT,arithmeticTheory.LESS_MOD])
QED

Theorem sort_before_sum_reify_argsort[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ⇒
  eval_lin_term (reify_avar cs wi) (sort_before_sum name (LENGTH Xs) i) =
  &(sort_rank wi Xs i)
Proof
  rw[sort_before_sum_count,sort_rank_def]>>
  AP_TERM_TAC>>
  simp[FILTER_EQ,MEM_COUNT_LIST]>>rw[]>>drule reify_argsort_bf>>simp[]
QED

(* SORTED stable_lt gives the adjacent strict comparison on the mapped pairs *)
Theorem argsort_sorted_adj[local]:
  SORTED stable_lt (MAP (λq. (EL q xs, q)) qs) ∧ j + 1 < LENGTH qs ⇒
  stable_lt (EL (EL j qs) xs, EL j qs) (EL (EL (j+1) qs) xs, EL (j+1) qs)
Proof
  rw[]>>
  fs[SORTED_EL_SUC]>>
  first_x_assum(qspec_then`j`mp_tac)>>
  simp[arithmeticTheory.ADD1]>>
  DEP_REWRITE_TAC[EL_MAP]>>simp[]
QED

(* the order statistic / any x entry fits the chosen two's-complement width *)
Theorem argsort_y_width[local]:
  valid_assignment bnd wi ∧ k < LENGTH Xs ⇒
  -&(2 ** SND (argsort_width bnd Xs)) ≤ varc wi (EL k Xs) ∧
  varc wi (EL k Xs) < &(2 ** SND (argsort_width bnd Xs))
Proof
  strip_tac>>
  simp[argsort_width_def,MAP_MAP_o,o_DEF]>>
  qmatch_goalsub_abbrev_tac`bit_width (λu. (lb,ub)) ()`>>
  `FST (case EL k Xs of INL v => bnd v | INR c => (c,c)) ≤ varc wi (EL k Xs) ∧
   varc wi (EL k Xs) ≤ SND (case EL k Xs of INL v => bnd v | INR c => (c,c))` by (
    Cases_on`EL k Xs`>>simp[varc_def]>>
    gvs[valid_assignment_def]>>first_x_assum(qspec_then`x`mp_tac)>>
    Cases_on`bnd x`>>simp[])>>
  `lb ≤ varc wi (EL k Xs)` by (
    `lb ≤ FST (case EL k Xs of INL v => bnd v | INR c => (c,c))` by (
      simp[Abbr`lb`]>>irule FOLDR_int_min_LE_MEM>>
      simp[MEM_MAP]>>qexists`EL k Xs`>>simp[EL_MEM])>>
    intLib.ARITH_TAC)>>
  `varc wi (EL k Xs) ≤ ub` by (
    `SND (case EL k Xs of INL v => bnd v | INR c => (c,c)) ≤ ub` by (
      simp[Abbr`ub`]>>irule FOLDR_int_max_GE_MEM>>
      simp[MEM_MAP]>>qexists`EL k Xs`>>simp[EL_MEM])>>
    intLib.ARITH_TAC)>>
  Cases_on`bit_width (λu. (lb,ub)) ()`>>simp[]>>
  qmatch_asmsub_rename_tac`bit_width _ _ = (comp,h)`>>
  conj_tac
  >- (
    Cases_on`0 ≤ varc wi (EL k Xs)`
    >- intLib.ARITH_TAC>>
    `∃m. varc wi (EL k Xs) = -&m` by intLib.ARITH_TAC>>
    `lb < 0` by intLib.ARITH_TAC>>
    `comp = T` by (qpat_x_assum`bit_width _ _ = _`mp_tac>>rw[bit_width_def])>>
    `bit_width (λu. (lb,ub)) () = (T,h)` by gvs[]>>
    `lb ≤ -&m` by (qpat_x_assum`varc wi _ = -&m`(fn th => fs[GSYM th]))>>
    `m ≤ 2 ** h` by
      (drule bit_width_lemma2>>disch_then(qspecl_then[`ub`,`lb`,`m`]mp_tac)>>gvs[])>>
    qpat_x_assum`varc wi _ = -&m`SUBST1_TAC>>
    gvs[integerTheory.INT_LE_NEG,integerTheory.INT_LE])
  >- (
    Cases_on`0 ≤ varc wi (EL k Xs)`
    >- (
      `∃m. varc wi (EL k Xs) = &m` by intLib.ARITH_TAC>>
      `&m ≤ ub` by (qpat_x_assum`varc wi _ = &m`(fn th => fs[GSYM th]))>>
      `m < 2 ** h` by
        (drule bit_width_lemma1>>disch_then(qspecl_then[`ub`,`lb`,`m`]mp_tac)>>gvs[])>>
      qpat_x_assum`varc wi _ = &m`SUBST1_TAC>>
      gvs[integerTheory.INT_LT])>>
    intLib.ARITH_TAC)
QED

(* under reify the proof-only signed bit-sum reconstructs the order statistic *)
Theorem argsort_y_reconstruct[local]:
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ∧
  -&(2 ** h) ≤ argsort_yval wi Xs j ∧ argsort_yval wi Xs j < &(2 ** h) ⇒
  eval_lin_term (reify_avar cs wi) (argsort_y_num name j h) = argsort_yval wi Xs j
Proof
  rw[argsort_y_num_def,two_comp_eval]>>
  `∀b. reify_avar cs wi (INR (name,Values [&j; &b] (SOME «y»))) ⇔
       int_bit b (argsort_yval wi Xs j)` by
    (gen_tac>>drule reify_argsort_y>>simp[])>>
  `reify_avar cs wi (INR (name,Values [&j] (SOME «ysgn»))) ⇔ argsort_yval wi Xs j < 0` by
    (drule reify_argsort_ysgn>>simp[])>>
  asm_simp_tac std_ss []>>
  DEP_REWRITE_TAC[two_comp_reconstruct]>>
  simp[]
QED

(* projections of the stable order *)
Theorem stable_lt_le[local]:
  stable_lt (v1,i1) (v2,i2) ⇒ v1 ≤ (v2:int)
Proof
  rw[stable_lt_def]>>simp[integerTheory.INT_LE_LT]
QED

Theorem encode_argsort_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Sorting (ArgSort Xs Ps offset)) ∧
  argsort_sem Xs Ps offset wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_argsort bnd Xs Ps offset name)
Proof
  rw[]>>
  `LENGTH Ps = LENGTH Xs` by fs[argsort_sem_def]>>
  qabbrev_tac`h = SND (argsort_width bnd Xs)`>>
  fs[argsort_sem_def]>>
  qmatch_asmsub_abbrev_tac`PERM qs _`>>
  `LENGTH qs = LENGTH Xs` by gvs[Abbr`qs`]>>
  `∀j. j < LENGTH Xs ⇒ EL j qs < LENGTH Xs` by metis_tac[PERM_COUNT_LIST_EL_lt]>>
  `∀j. j < LENGTH Xs ⇒ sort_rank wi Xs (EL j qs) = j` by
    metis_tac[argsort_rank_inv]>>
  `∀j. j < LENGTH Xs ⇒
     offset ≤ varc wi (EL j Ps) ∧ varc wi (EL j Ps) ≤ offset + &LENGTH Xs - 1` by (
    qpat_x_assum`EVERY _ (MAP (varc wi) Ps)`mp_tac>>simp[EVERY_EL,EL_MAP]>>
    rw[]>>first_x_assum drule>>strip_tac>>
    qpat_x_assum`varc wi _ < _`mp_tac>>rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
  `∀j. j < LENGTH Xs ⇒ varc wi (EL j Ps) = offset + &(EL j qs)` by (
    rw[]>>
    `offset ≤ varc wi (EL j Ps)` by metis_tac[]>>
    `&(EL j qs) = varc wi (EL j Ps) − offset` by (
      `EL j qs = Num (varc wi (EL j Ps) − offset)` by gvs[Abbr`qs`,EL_MAP]>>
      `0 ≤ varc wi (EL j Ps) − offset` by
        (qpat_x_assum`offset ≤ varc wi _`mp_tac>>rpt(pop_assum kall_tac)>>intLib.ARITH_TAC)>>
      asm_simp_tac (srw_ss())[integerTheory.INT_OF_NUM])>>
    qpat_x_assum`&(EL j qs) = _`(fn th => simp[th])>>intLib.ARITH_TAC)>>
  `∀j. j < LENGTH Xs ⇒ argsort_yval wi Xs j = varc wi (EL (EL j qs) Xs)` by (
    rw[]>>
    `sort_rank wi Xs (EL j qs) = j` by metis_tac[]>>
    `EL j qs < LENGTH Xs` by metis_tac[]>>
    metis_tac[argsort_yval_rank])>>
  `∀j. j < LENGTH Xs ⇒
     -&(2 ** h) ≤ argsort_yval wi Xs j ∧ argsort_yval wi Xs j < &(2 ** h)` by (
    rw[]>>
    `argsort_yval wi Xs j = varc wi (EL (EL j qs) Xs)` by metis_tac[]>>
    `EL j qs < LENGTH Xs` by metis_tac[]>>
    simp[Abbr`h`]>>metis_tac[argsort_y_width])>>
  `∀j. j < LENGTH Xs ⇒
     eval_lin_term (reify_avar cs wi) (argsort_y_num name j h) = argsort_yval wi Xs j` by (
    rw[]>>
    `-&(2 ** h) ≤ argsort_yval wi Xs j ∧ argsort_yval wi Xs j < &(2 ** h)` by metis_tac[]>>
    metis_tac[argsort_y_reconstruct])>>
  simp[encode_argsort_def,cencode_argsort_def]>>
  `¬(LENGTH Ps ≠ LENGTH Xs)` by simp[]>>
  simp[append_thm,EVERY_APPEND]>>
  rpt conj_tac
  >- (
    simp[argsort_chain_le_sem]>>rpt strip_tac>>
    `j + 1 < LENGTH Xs` by simp[]>>
    `EL j qs < LENGTH Xs ∧ EL (j + 1) qs < LENGTH Xs` by
      (qpat_x_assum`∀j. j < LENGTH Xs ⇒ EL j qs < LENGTH Xs`mp_tac>>simp[])>>
    qpat_x_assum`∀j. j < LENGTH Xs ⇒ eval_lin_term _ _ = _`(fn th => simp[th])>>
    qpat_x_assum`∀j. j < LENGTH Xs ⇒ argsort_yval _ _ _ = _`(fn th => simp[th])>>
    drule argsort_sorted_adj>>disch_then(qspec_then`j`mp_tac)>>impl_tac>-simp[]>>
    strip_tac>>imp_res_tac stable_lt_le>>
    rpt(qpat_x_assum`∀j. _`kall_tac)>>
    gvs[EL_MAP])
  >- (
    drule sort_bf_lines_sem>>disch_then(fn th => simp[th])>>rw[]>>
    drule reify_argsort_bf>>simp[])
  >- (
    simp[sort_rank_lines_sem]>>rw[]>>
    DEP_REWRITE_TAC[sort_pos_num_reify_argsort,sort_before_sum_reify_argsort]>>
    metis_tac[])
  >- (
    simp[argsort_pos_chan_sem]>>rpt strip_tac>>
    `j < 2 ** sort_width (LENGTH Xs)` by
      (`LENGTH Xs ≤ 2 ** sort_width (LENGTH Xs)` by (irule sort_width_bound>>gvs[])>>gvs[])>>
    `∀k. k < sort_width (LENGTH Xs) ⇒ (BIT k (sort_rank wi Xs i) ⇔ BIT k j)` by
      (qpat_x_assum`EVERY (lit _) _`mp_tac>>simp[sort_guard_lit]>>rw[]>>
       first_x_assum drule>>drule reify_argsort_pos>>simp[])>>
    `sort_rank wi Xs i = j` by
      (irule BIT_eq_lt_2EXP>>qexists_tac`sort_width (LENGTH Xs)`>>gvs[]>>
       `sort_rank wi Xs i < 2 ** sort_width (LENGTH Xs)` by (irule sort_rank_2EXP>>gvs[])>>gvs[])>>
    `EL j qs = i` by (
      `sort_rank wi Xs (EL j qs) = j` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ sort_rank wi Xs (EL j qs) = j`(qspec_then`j`mp_tac)>>simp[])>>
      `EL j qs < LENGTH Xs` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ EL j qs < LENGTH Xs`(qspec_then`j`mp_tac)>>simp[])>>
      metis_tac[sort_rank_inj])>>
    `eval_lin_term (reify_avar cs wi) (argsort_y_num name j h) = argsort_yval wi Xs j` by
      (qpat_x_assum`∀j. j < LENGTH Xs ⇒ eval_lin_term _ _ = _`(qspec_then`j`mp_tac)>>simp[])>>
    `argsort_yval wi Xs j = varc wi (EL (EL j qs) Xs)` by
      (qpat_x_assum`∀j. j < LENGTH Xs ⇒ argsort_yval _ _ _ = _`(qspec_then`j`mp_tac)>>simp[])>>
    rpt(qpat_x_assum`∀j. _`kall_tac)>>gvs[])
  >- (simp[argsort_p_range_sem]>>gvs[])
  >- (simp[argsort_eq_flags_sem]>>rw[]>>simp[reify_avar_def,reify_reif_def])
  >- (
    simp[argsort_perm_sem]>>rw[]>>
    `MAP (b2i ∘ lit (reify_avar cs wi))
       (MAP (λpj. Pos (INL (Eq pj (offset + &k)))) Ps) =
     MAP (b2i ∘ (λpj. varc wi pj = offset + &k)) Ps` by
      simp[MAP_MAP_o,o_DEF,lit_def,reify_avar_def,reify_reif_def]>>
    pop_assum SUBST1_TAC>>
    simp[iSUM_FILTER]>>
    `LENGTH (FILTER (λpj. varc wi pj = offset + &k) Ps) ≤ 1` by (
      irule ALL_DISTINCT_MAP_FILTER_le_1>>
      `MAP (varc wi) Ps = MAP (λq. offset + &q) qs` by (
        irule LIST_EQ>>simp[EL_MAP]>>rw[]>>
        qpat_x_assum`∀j. j < LENGTH Xs ⇒ varc wi _ = _`irule>>gvs[])>>
      simp[]>>irule ALL_DISTINCT_MAP_INJ>>
      simp[integerTheory.INT_INJ,integerTheory.INT_EQ_LADD]>>
      metis_tac[ALL_DISTINCT_PERM,all_distinct_count_list])>>
    intLib.ARITH_TAC)
  >- (
    simp[argsort_valchan_sem]>>rpt strip_tac>>
    `j < LENGTH Xs` by gvs[]>>
    qpat_x_assum`reify_avar _ _ (INL (Eq _ _))`mp_tac>>
    simp[reify_avar_def,reify_reif_def]>>strip_tac>>
    `EL j qs = k` by (
      `varc wi (EL j Ps) = offset + &(EL j qs)` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ varc wi _ = _`(qspec_then`j`mp_tac)>>simp[])>>
      `&(EL j qs) = (&k):int` by
        (qpat_x_assum`varc wi _ = offset + &(EL j qs)`mp_tac>>
         qpat_x_assum`varc wi _ = offset + &k`mp_tac>>simp[integerTheory.INT_EQ_LADD])>>
      fs[integerTheory.INT_INJ])>>
    `eval_lin_term (reify_avar cs wi) (argsort_y_num name j h) = argsort_yval wi Xs j` by
      (qpat_x_assum`∀j. j < LENGTH Xs ⇒ eval_lin_term _ _ = _`(qspec_then`j`mp_tac)>>simp[])>>
    `argsort_yval wi Xs j = varc wi (EL (EL j qs) Xs)` by
      (qpat_x_assum`∀j. j < LENGTH Xs ⇒ argsort_yval _ _ _ = _`(qspec_then`j`mp_tac)>>simp[])>>
    rpt(qpat_x_assum`∀j. _`kall_tac)>>gvs[])
  >- (
    simp[argsort_rankchan_sem]>>rpt strip_tac>>
    `j < LENGTH Xs` by gvs[]>>
    qpat_x_assum`reify_avar _ _ (INL (Eq _ _))`mp_tac>>
    simp[reify_avar_def,reify_reif_def]>>strip_tac>>
    `sort_rank wi Xs k = j` by (
      `sort_rank wi Xs (EL j qs) = j` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ sort_rank wi Xs (EL j qs) = j`(qspec_then`j`mp_tac)>>simp[])>>
      gvs[])>>
    rpt(qpat_x_assum`∀j. _`kall_tac)>>
    `eval_lin_term (reify_avar cs wi) (sort_pos_num name k (sort_width (LENGTH Xs))) =
       &(sort_rank wi Xs k)` by (irule sort_pos_num_reify_argsort>>metis_tac[])>>
    gvs[])
  >- (
    simp[argsort_tiebreak_sem]>>
    `∀i. reify_avar cs wi (INR (name,Values [&i] (SOME «yge»))) ⇔
         argsort_yval wi Xs i ≥ argsort_yval wi Xs (i+1)` by
      (rw[]>>drule reify_argsort_yge>>simp[])>>
    conj_tac
    >- (
      rpt strip_tac>>
      `j + 1 < LENGTH Xs ∧ j < LENGTH Xs` by simp[]>>
      `eval_lin_term (reify_avar cs wi) (argsort_y_num name j h) = argsort_yval wi Xs j` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ eval_lin_term _ _ = _`(qspec_then`j`mp_tac)>>simp[])>>
      `eval_lin_term (reify_avar cs wi) (argsort_y_num name (j+1) h) = argsort_yval wi Xs (j+1)` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ eval_lin_term _ _ = _`(qspec_then`j+1`mp_tac)>>simp[])>>
      simp[]>>
      qpat_x_assum`∀i. reify_avar _ _ _ ⇔ _`(qspec_then`j`mp_tac)>>simp[])
    >- (
      rpt strip_tac>>
      `j + 1 < LENGTH Xs ∧ j < LENGTH Xs` by simp[]>>
      `EL j qs < LENGTH Xs ∧ EL (j+1) qs < LENGTH Xs` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ EL j qs < LENGTH Xs`mp_tac>>simp[])>>
      `argsort_yval wi Xs j ≥ argsort_yval wi Xs (j+1)` by
        (qpat_x_assum`reify_avar _ _ (INR _)`mp_tac>>
         qpat_x_assum`∀i. reify_avar _ _ _ ⇔ _`(qspec_then`j`mp_tac)>>simp[])>>
      `stable_lt (varc wi (EL (EL j qs) Xs), EL j qs)
                 (varc wi (EL (EL (j+1) qs) Xs), EL (j+1) qs)` by
        (drule argsort_sorted_adj>>disch_then(qspec_then`j`mp_tac)>>impl_tac>-simp[]>>simp[EL_MAP])>>
      `argsort_yval wi Xs j = varc wi (EL (EL j qs) Xs)` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ argsort_yval _ _ _ = _`(qspec_then`j`mp_tac)>>simp[])>>
      `argsort_yval wi Xs (j+1) = varc wi (EL (EL (j+1) qs) Xs)` by
        (qpat_x_assum`∀j. j < LENGTH Xs ⇒ argsort_yval _ _ _ = _`(qspec_then`j+1`mp_tac)>>simp[])>>
      `varc wi (EL (EL j qs) Xs) = varc wi (EL (EL (j+1) qs) Xs)` by (
        imp_res_tac stable_lt_le>>
        qpat_x_assum`argsort_yval wi Xs j ≥ _`mp_tac>>
        qpat_x_assum`argsort_yval wi Xs j = _`mp_tac>>
        qpat_x_assum`argsort_yval wi Xs (j+1) = _`mp_tac>>
        qpat_x_assum`varc wi _ ≤ varc wi _`mp_tac>>
        rpt(pop_assum kall_tac)>>
        simp[integerTheory.int_ge]>>intLib.ARITH_TAC)>>
      `EL j qs < EL (j+1) qs` by (qpat_x_assum`stable_lt _ _`mp_tac>>gvs[stable_lt_def])>>
      `&(EL j qs):int < &(EL (j+1) qs)` by simp[integerTheory.INT_LT]>>
      qpat_x_assum`&(EL j qs) < &(EL (j+1) qs)`mp_tac>>
      rpt(pop_assum kall_tac)>>
      simp[integerTheory.int_ge]>>intLib.ARITH_TAC))
QED

Theorem cencode_argsort_sem:
  valid_assignment bnd wi ∧
  cencode_argsort bnd Xs Ps offset name = es ⇒
  enc_rel wi es (encode_argsort bnd Xs Ps offset name) ec ec
Proof
  rw[encode_argsort_def]
QED

(* Category dispatch *)

Definition encode_sorting_constr_def:
  encode_sorting_constr bnd c name =
  case c of
    Increasing Xs strct desc =>
      encode_increasing Xs strct desc name
  | Sort Xs Ys => encode_sort bnd Xs Ys name
  | ArgSort Xs Ps offset => encode_argsort bnd Xs Ps offset name
End

Definition cencode_sorting_constr_def:
  cencode_sorting_constr bnd c name ec =
  case c of
    Increasing Xs strct desc =>
      (cencode_increasing Xs strct desc name, ec)
  | Sort Xs Ys => (cencode_sort bnd Xs Ys name, ec)
  | ArgSort Xs Ps offset => (cencode_argsort bnd Xs Ps offset name, ec)
End

Theorem encode_sorting_constr_sem_1:
  valid_assignment bnd wi ∧
  ALOOKUP cs name = SOME (Sorting c) ∧
  sorting_constr_sem c wi ⇒
  EVERY (λx. iconstraint_sem x (wi,reify_avar cs wi))
    (encode_sorting_constr bnd c name)
Proof
  Cases_on`c`>>
  rw[encode_sorting_constr_def,sorting_constr_sem_def]>>
  metis_tac[encode_increasing_sem_1,encode_sort_sem_1,encode_argsort_sem_1]
QED

Theorem encode_sorting_constr_sem_2:
  valid_assignment bnd wi ∧
  EVERY (λx. iconstraint_sem x (wi,wb))
    (encode_sorting_constr bnd c name) ⇒
  sorting_constr_sem c wi
Proof
  Cases_on`c`>>
  rw[encode_sorting_constr_def,sorting_constr_sem_def]
  >- metis_tac[encode_increasing_sem_2]
  >- metis_tac[encode_sort_sem_2]
  >- metis_tac[encode_argsort_sem_2]
QED

Theorem cencode_sorting_constr_sem:
  valid_assignment bnd wi ∧
  cencode_sorting_constr bnd c name ec = (es,ec') ⇒
  enc_rel wi es (encode_sorting_constr bnd c name) ec ec'
Proof
  Cases_on`c`>>
  simp[cencode_sorting_constr_def,encode_sorting_constr_def,
    cencode_increasing_def,encode_increasing_def,encode_sort_def,encode_argsort_def]
QED
