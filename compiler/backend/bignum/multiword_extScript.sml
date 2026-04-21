(*
  Extensions to multiword that should be upstreamed.
*)
Theory multiword_ext
Ancestors
  arithmetic (* CEILING_DIV_def *)
  divides  (* SUB_DIV, DIV_POS *)
  bit
  integer
  fcp (* DIMINDEX_GE_1 *)
  int_bitwise
  multiword
Libs
  preamble wordsLib

(** General helper lemmas *****************************************************)

(* TODO Decide which theorems should be moved, and which should stay here as
   local. *)

Theorem ODD_MOD_2_EXP:
  0 ≠ m ⇒ ODD (x MOD (2 ** m)) = ODD x
Proof
  Induct_on ‘m’ >> simp [EXP]
  >> irule EQ_TRANS
  >> irule_at (Pos hd) $ GSYM ODD_MOD_2
  >> qspecl_then [‘2 ** m’, ‘2’] mp_tac MOD_MULT_MOD
  >> simp [Excl "ODD_MOD_2"] >> simp []
QED

Theorem ZERO_CEILING_DIV[simp]:
  0 \\ k = 0
Proof
  Cases_on ‘k = 0’ >> simp [CEILING_DIV_def, LESS_DIV_EQ_ZERO]
QED

Theorem CEILING_DIV_ZERO[simp]:
  k \\ 0 = 0
Proof
  simp [CEILING_DIV_def]
QED

Theorem CEILING_DIV_POS:
  0 < x ∧ 0 < y ⇒ 0 < x \\ y
Proof
  simp [CEILING_DIV_def, DIV_POS]
QED

Theorem SUB_CEILING_DIV:
  (x - y) \\ y = (x \\ y) - 1
Proof
  Cases_on ‘y = 0’
  >> simp [CEILING_DIV]
  >> Cases_on ‘x < y’
  >- (‘x - y = 0’ by (simp[]) >> simp [LESS_DIV_EQ_ZERO])
  >> simp [SUB_DIV, SUB_MOD]
  >> ‘0 < x DIV y’ by (simp [DIV_POS]) >> simp []
QED

Theorem MULT_CEILING_DIV:
  0 < n ⇒ q * n \\ n = q
Proof
  Cases_on ‘q = 0’ >- simp []
  >> rw [CEILING_DIV]
  >> drule MULT_DIV >> simp []
QED

Theorem MAP2_SYM:
  ∀xs ys. (∀x y. R x y = R y x) ⇒ MAP2 R xs ys = MAP2 R ys xs
Proof
  Induct >> simp [] >> Cases_on ‘ys’ >>
  rewrite_tac [MAP2_DEF] >> metis_tac []
QED

Theorem MAP2_MAP:
  ∀xs ys.
    MAP2 f (MAP g xs) ys = MAP2 (λx y. f (g x) y) xs ys ∧
    MAP2 f xs (MAP h ys) = MAP2 (λx y. f x (h y)) xs ys
Proof
  Induct >> Cases_on ‘ys’ >> gvs []
QED

Theorem MAP2_DROP:
  ∀xs ys n. MAP2 f (DROP n xs) (DROP n ys) = DROP n (MAP2 f xs ys)
Proof
  Induct >> Cases_on ‘ys’ >> Cases_on ‘n’ >> simp []
QED

Theorem MAP2_TAKE:
  ∀xs ys n. MAP2 f (TAKE n xs) (TAKE n ys) = TAKE n (MAP2 f xs ys)
Proof
  Induct >> Cases_on ‘ys’ >> Cases_on ‘n’ >> simp []
QED

Theorem MAP2_EQ_NIL:
  MAP2 f xs ys = [] ⇔ (xs = []) ∨ (ys = [])
Proof
  Cases_on ‘xs’ >> Cases_on ‘ys’ >> fs [MAP2_DEF]
QED

(** Helper lemmas for int_bitwise *********************************************)

(* TODO Decide which of these should live in int_bitwise and move them. *)

Theorem int_of_bits_sign:
  int_of_bits bs < 0 ⇔ SND bs
Proof
  namedCases_on ‘bs’ ["xs r"] >> Cases_on ‘r’
  >> simp [int_of_bits_def, int_not_def]
  >> intLib.COOPER_TAC
QED

Theorem bits_bitwise_rest:
  ∀f xs s ys t zs z. bits_bitwise f (xs, s) (ys, t) = (zs, z) ⇒ z = f s t
Proof
  recInduct bits_bitwise_ind >> rw [bits_bitwise_def]
  >> (pairarg_tac >> gvs [])
QED

Theorem int_and_sign:
  int_and i j < 0 ⇔ i < 0 ∧ j < 0
Proof
  rw [int_and_def, int_bitwise_def, bits_of_int_def, int_of_bits_sign]
  >> rw [GSYM SND_pair] >> pairarg_tac >> gvs []
  >> drule bits_bitwise_rest >> simp []
QED

(* TODO Remove bits_bitwise_NIL - superseded by bits_bitwise_empty_{left,right} *)

Theorem bits_bitwise_empty_left[simp]:
  ∀xs rest f. bits_bitwise f ([],b) (xs,rest) = (MAP (f b) xs,f b rest)
Proof
  Induct >> fs [bits_bitwise_def]
QED

Theorem bits_bitwise_empty_right[simp]:
  ∀xs rest f. bits_bitwise f (xs,rest) ([],b) = (MAP (λx. f x b) xs,f rest b)
Proof
  Induct >> fs [bits_bitwise_def]
QED

Theorem bits_bitwise_empty_result:
  ∀f xs b₁ ys b₂.
    bits_bitwise f (xs,b₁) (ys,b₂) = ([],b₃) ⇔
    (xs = [] ∧ ys = [] ∧ b₃ = f b₁ b₂)
Proof
  recInduct bits_bitwise_ind >> rw []
  >- (eq_tac >> rw [])
  >> simp [bits_bitwise_def]
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem bits_bitwise_cong:
  ∀f bs₁ r₁ bs₂ r₂ g.
    (∀x y. f x y = g x y) ⇒
    bits_bitwise f (bs₁,r₁) (bs₂,r₂) = bits_bitwise g (bs₁,r₁) (bs₂,r₂)
Proof
  recInduct bits_bitwise_ind >> rw [bits_bitwise_def]
  >> AP_TERM_TAC
  >> first_assum drule >> simp []
QED

Theorem bits_bitwise_sym:
  ∀f bs₁ r₁ bs₂ r₂.
    (∀x y. f x y = f y x) ⇒
    bits_bitwise f (bs₁,r₁) (bs₂,r₂) = bits_bitwise f (bs₂,r₂) (bs₁,r₁)
Proof
  recInduct bits_bitwise_ind >> rw [bits_bitwise_def]
  >> AP_TERM_TAC
  >> first_assum drule >> simp []
QED

Theorem bits_bitwise_and_sym:
  ∀x y. bits_bitwise $/\ x y = bits_bitwise $/\ y x
Proof
  rpt Cases >> irule bits_bitwise_sym >> rpt Cases >> simp []
QED

Theorem bits_bitwise_MAP_NOT:
  ∀f xs b₁ ys b₂ zs b₃.
    bits_bitwise f (xs,b₁) (ys,b₂) = (zs,b₃) ⇔
    bits_bitwise (λa b. ¬f (¬a) (¬b)) (MAP $¬ xs,¬b₁) (MAP $¬ ys,¬b₂) =
    (MAP $¬ zs,¬b₃)
Proof
  recInduct bits_bitwise_ind >> rw [bits_bitwise_def]
  >> eq_tac >> rw []
  >- metis_tac [MAP]
  >- (Cases_on ‘zs’ >> gvs [] >> metis_tac [])
  >- metis_tac [MAP]
  >- (Cases_on ‘zs’ >> gvs [] >> metis_tac [])
  >> rpt (pairarg_tac >> gvs [])
  >- metis_tac []
  >- (Cases_on ‘zs’ >> gvs [])
QED

Theorem int_and_sym:
  int_and i j = int_and j i
Proof
  simp [int_and_def, int_bitwise_def, bits_bitwise_and_sym]
QED

Theorem bits_of_num_nil:
  bits_of_num n = [] ⇔ n = 0
Proof
  simp [Once bits_of_num_def] >> IF_CASES_TAC >> simp []
QED

Theorem num_of_bits_bits_of_num:
  ∀n. num_of_bits (bits_of_num n) = n
Proof
  recInduct bits_of_num_ind >> rw []
  >> Cases_on ‘n = 0’ >> gvs []
  >- simp [Once bits_of_num_def, num_of_bits_def]
  >> simp [Once bits_of_num_def]
  >> Cases_on ‘ODD n’
  >> simp [num_of_bits_def, DIV_MULT_THM2]
  >- fs [ODD_MOD2_LEM]
  >> fs [ODD_EVEN, EVEN_MOD2]
QED

Theorem num_of_bits_append:
  ∀xs ys.
    num_of_bits (xs ⧺ ys) =
    2 ** LENGTH xs * num_of_bits ys + num_of_bits xs
Proof
  recInduct num_of_bits_ind >> simp [num_of_bits_def, ADD1, EXP_ADD]
QED

Theorem num_of_bits_TAKE_DROP_dimindex:
  num_of_bits (TAKE (dimindex (:α)) xs) +
  dimword (:α) * num_of_bits (DROP (dimindex (:α)) xs) =
  num_of_bits xs
Proof
  ‘num_of_bits xs =
   num_of_bits (TAKE (dimindex (:α)) xs ++ DROP (dimindex (:α)) xs)’ by simp []
  >> pop_assum SUBST_ALL_TAC
  >> rewrite_tac [num_of_bits_append]
  >> simp [LENGTH_TAKE_EQ, dimword_def]
  >> IF_CASES_TAC >> simp [DROP_LENGTH_TOO_LONG, num_of_bits_def]
QED

Theorem num_of_bits_cons:
  num_of_bits (b::ys) = 2 * num_of_bits ys + num_of_bits [b]
Proof
  once_rewrite_tac [CONS_APPEND]
  >> rewrite_tac [num_of_bits_append]
  >> simp [num_of_bits_def]
QED

Theorem num_of_bits_lt:
  ∀xs. num_of_bits xs < 2 ** LENGTH xs
Proof
  recInduct num_of_bits_ind >> rw [num_of_bits_def, EXP]
QED

Theorem num_of_bits_TAKE:
  ∀n m. num_of_bits (TAKE m (bits_of_num n)) = n MOD (2 ** m)
Proof
  recInduct bits_of_num_ind >> rw []
  >> Cases_on ‘n = 0’ >> gvs []
  >- simp [Once bits_of_num_def, num_of_bits_def]
  >> Cases_on ‘m’ >- simp [num_of_bits_def]
  >> simp [Once bits_of_num_def]
  >> Cases_on ‘ODD n’
  >> simp [num_of_bits_def]
  >> simp [DIV_MOD_MOD_DIV, GSYM EXP]
  >> qmatch_goalsub_abbrev_tac ‘_ MOD m'’
  >-
   (‘ODD (n MOD m')’ by (unabbrev_all_tac >> simp [ODD_MOD_2_EXP])
    >> ‘n MOD m' ≠ 0’ by (drule ODD_POS >> simp [])
    >> fs [DIV_MULT_THM2, ODD_MOD2_LEM])
  >> ‘EVEN (n MOD m')’ by (unabbrev_all_tac >> simp [EVEN_ODD, ODD_MOD_2_EXP])
  >> fs [DIV_MULT_THM2, EVEN_MOD2]
QED

(** multiword extensions ******************************************************)

(* TODO Move to HOL's multiword. *)

(* mw2n_mw_fix uses prove() in HOL; should be replaced by this *)
Theorem mw2n_mw_fix:
  ∀xs. mw2n (mw_fix xs) = mw2n xs
Proof
  recInduct mw_fix_ind
  >> rw [Once mw_fix_def]
  >> namedCases_on ‘xs’ ["", "y ys"] using SNOC_CASES >> gvs []
  >> simp [Once mw_fix_def]
  >> IF_CASES_TAC
  >> simp [SNOC_APPEND, mw2n_APPEND, Once mw_fix_def, mw2n_def]
QED

(* TODO Split into mw_ok_nil[local,simp] and mw_ok_cons (not local).
   Replace mw_ok_CLAUSES with mw_ok_cons in multiwordScript.sml *)
Theorem mw_ok_CLAUSES[local]:
  mw_ok [] ∧ (mw_ok (x::xs) ⇔ (xs = [] ⇒ x ≠ 0w) ∧ mw_ok xs)
Proof
  simp [mw_ok_def] >> Cases_on ‘xs’ using SNOC_CASES >> simp [LAST_DEF]
QED

Theorem cons_n2mw:
  (n = 0 ⇒ (w: α word) ≠ 0w) ⇒ w::n2mw n = n2mw (w2n w + n * dimword (:α))
Proof
  rw []
  >> simp [Once n2mw_def, SimpRHS]
  >> IF_CASES_TAC >> gvs []
  >- fs [ZERO_LT_dimword]
  >> conj_tac
  >- (Cases_on ‘w’ >> gvs [])
  >> ‘w2n w < dimword (:α)’ by (Cases_on ‘w’ >> fs [])
  >> drule DIV_MULT >> simp []
QED

(* Replace version in HOL with this*)
Theorem mw_ok_IMP_EXISTS_n2mw:
  ∀xs. mw_ok xs ⇒ ∃n. xs = n2mw n
Proof
  Induct >- metis_tac [n2mw_def]
  >> simp [mw_ok_CLAUSES]
  >> rpt strip_tac >> gvs []
  >> fs [n2mw_NIL]
  >> metis_tac [cons_n2mw]
QED

(* TODO Remove mw_fix_EQ_n2mw from HOL *)

(* Replace version in HOL with this*)
Theorem n2mw_mw2n:
  mw_fix xs = n2mw (mw2n xs)
Proof
  qspec_then ‘mw_fix xs’ assume_tac mw_ok_IMP_EXISTS_n2mw >> fs [mw_ok_fix]
  >> simp [(Once o GSYM) mw2n_mw_fix, mw2n_n2mw]
QED

(*
Motivation for definition:
bits_of_int_def |> Q.SPEC ‘-i’ |> DISCH “0 < i” |> SRULE [int_not_def]

Subtracts one and flips all the bits. Together with the (separate) sign bit, we
get the two's complement form.
*)
Definition mw_bits_of_int_def:
  mw_bits_of_int xs =
    let (ys,c) = mw_sub xs [] F in
      MAP (~) ys
End

(*
Motivation for definition:
int_of_bits_def |> SRULE [int_not_def, intLib.COOPER_PROVE “-i-1 = -(i+1):int”]
*)
Definition mw_int_of_bits_def:
  mw_int_of_bits xs =
    let (ys,c) = mw_add (MAP (~) xs) (MAP (K 0w) xs) T in
      if c then ys ++ [1w] else ys
End

Theorem LENGTH_mw_bits_of_int:
  LENGTH (mw_bits_of_int xs) = LENGTH xs
Proof
  Induct_on ‘xs’ >> rw []
  >- simp [mw_bits_of_int_def, mw_sub_def]
  >> fs [mw_bits_of_int_def, mw_sub_def]
  >> rpt (pairarg_tac >> gvs [])
  >> imp_res_tac LENGTH_mw_sub >> simp []
QED

(* Computes the bitwise and of two non-negative multiwords.
 *
 * If the multiwords have different lengths, the length of the result will be
 * the smaller of those lengths: if we were to pad the shorter word with 0s
 * (since we are in the non-negative case), the result would have a tail of 0s,
 * which we do not represent. *)
Definition mw_and_def:
  mw_and (x::xs) (y::ys) = (x && y)::mw_and xs ys ∧
  mw_and _ _ = []
End

Definition mw_and_flip_def:
  mw_and_flip xs ys =
    if LENGTH xs ≤ LENGTH ys then mw_and xs ys else mw_and ys xs
End

Definition mw_and_keep_def:
  mw_and_keep (x::xs) (y::ys) = (x && y)::mw_and_keep xs ys ∧
  mw_and_keep _       []      = [] ∧
  mw_and_keep []      rest    = rest
End

Definition mw_and_keep_flip_def:
  mw_and_keep_flip xs ys =
    if LENGTH xs ≤ LENGTH ys then mw_and_keep xs ys else mw_and_keep ys xs
End

Definition mwi_and_def:
  mwi_and (s, xs) (t, ys) =
  if ¬(s ∨ t) then
    (F, mw_fix (mw_and_flip xs ys))
  else if s ∧ ~t then
    (F, mw_fix (if LENGTH xs < LENGTH ys
                then mw_and_keep (mw_bits_of_int xs) ys
                else mw_and ys (mw_bits_of_int xs)))
  else if ~s ∧ t then
    mwi_and (t, ys) (s, xs)
  else
    (T, mw_fix (mw_int_of_bits (mw_and_keep_flip
                                  (mw_bits_of_int xs)
                                  (mw_bits_of_int ys))))
Termination
  WF_REL_TAC ‘measure $ λ((s,xs),(t,ys)). if t then 1 else 0n’
End


Theorem mw_and_keep_nil_left:
  ∀xs. mw_and_keep [] xs = xs
Proof
  Induct >> simp [mw_and_keep_def]
QED

Theorem mw_and_nil_left:
  ∀xs. mw_and [] xs = []
Proof
  Induct >> simp [mw_and_def]
QED


Definition mwi_and_neg_neg_def:
  (mwi_and_neg_neg c d e (x₁::xs) (y₁::ys) =
   let
     (x₂, c₁) = single_sub x₁ 0w c;
     (y₂, d₁) = single_sub y₁ 0w d;
     z₁ = x₂ || y₂;
     (z₂, e₁) = single_add z₁ 0w e;
   in
     z₂::mwi_and_neg_neg c₁ d₁ e₁ xs ys) ∧
  (mwi_and_neg_neg c d e xs (y₁::ys) =
   let
     (y₂, d₁) = single_sub y₁ 0w d;
     (z, e₁) = single_add y₂ 0w e;
   in
     z::mwi_and_neg_neg c d₁ e₁ xs ys) ∧
  (mwi_and_neg_neg c d e xs [] =
   if e then [1w] else [])
End

Theorem LENGTH_mw_and_keep:
  ∀xs ys. LENGTH (mw_and_keep xs ys) = LENGTH ys
Proof
  recInduct mw_and_keep_ind >> rw [mw_and_keep_def]
QED

Theorem mwi_and_neg_neg_eq:
  ∀c d e xs ys.
    mwi_and_neg_neg c d e xs ys =
    let
      xs₂ = (let (xs₁,c') = mw_sub xs [] c in MAP $¬ xs₁);
      ys₂ = (let (ys₁,d') = mw_sub ys [] d in MAP $¬ ys₁);
      zs = mw_and_keep xs₂ ys₂;
      (zs₁, e') = mw_add (MAP $¬ zs) (MAP (K 0w) zs) e
    in
      if e' then zs₁ ++ [1w] else zs₁
Proof
  recInduct mwi_and_neg_neg_ind >> rw []
  >> gvs [mwi_and_neg_neg_def, mw_and_keep_def, mw_sub_def, mw_add_def,
          mw_and_keep_def]
  >> rpt (pairarg_tac >> gvs [])
  >> gvs [mw_and_keep_def, mw_add_def]
  >- gvs [COND_RAND]
  >> rpt (pairarg_tac >> gvs [])
  >> gvs [mw_and_keep_nil_left, COND_RAND]
QED

Theorem mwi_and_neg_neg_thm:
  (if LENGTH xs ≤ LENGTH ys
   then mwi_and_neg_neg F F T xs ys
   else mwi_and_neg_neg F F T ys xs)
  =
  (mw_int_of_bits (mw_and_keep_flip (mw_bits_of_int xs) (mw_bits_of_int ys)))
Proof
  simp [mw_and_keep_flip_def, LENGTH_mw_bits_of_int, COND_RAND]
  >> IF_CASES_TAC
  >> simp [mwi_and_neg_neg_eq, mw_int_of_bits_def, mw_bits_of_int_def]
  >> rpt (pairarg_tac >> gvs [])
QED

(* Used when LENGTH xs >= LENGTH ys. *)
Definition mwi_and_neg_pos_geq_def:
  (mwi_and_neg_pos_geq c (x::xs) (y₁::ys) =
   let
     (y₂,c₁) = single_sub y₁ 0w c;
     z = x && ¬y₂;
   in
     z::mwi_and_neg_pos_geq c₁ xs ys) ∧
  (mwi_and_neg_pos_geq _ _ _ = [])
End

Theorem mwi_and_neg_pos_geq_eq:
  ∀c xs ys.
    mwi_and_neg_pos_geq c xs ys =
    mw_and xs (let (ys',c') = mw_sub ys [] c in MAP $¬ ys')
Proof
  recInduct mwi_and_neg_pos_geq_ind >> rw []
  >> gvs [mwi_and_neg_pos_geq_def, mw_sub_def, mw_and_nil_left,
          mw_and_def]
  >> rpt (pairarg_tac >> gvs [])
  >> gvs [mw_and_def]
QED

Theorem mwi_and_neg_pos_geq_thm:
  mwi_and_neg_pos_geq F xs ys = mw_and xs (mw_bits_of_int ys)
Proof
  simp [mw_bits_of_int_def, mwi_and_neg_pos_geq_eq]
QED

(* Used when LENGTH xs < LENGTH ys. *)
Definition mwi_and_neg_pos_lt_def:
  (mwi_and_neg_pos_lt c (x₁::xs) (y::ys) =
   let
     (x₂,c₁) = single_sub x₁ 0w c;
     x₃ = ¬x₂;
     z = x₃ && y;
   in
     z::mwi_and_neg_pos_lt c₁ xs ys) ∧
  (mwi_and_neg_pos_lt _ xs ys = ys)
End

Theorem mwi_and_neg_pos_lt_eq:
  ∀c xs ys.
    mwi_and_neg_pos_lt c xs ys =
    mw_and_keep (let (xs',c') = mw_sub xs [] c in MAP $¬ xs') ys
Proof
  recInduct mwi_and_neg_pos_lt_ind >> rw []
  >> gvs [mwi_and_neg_pos_lt_def, mw_sub_def, mw_and_keep_nil_left,
          mw_and_keep_def]
  >> rpt (pairarg_tac >> gvs [])
  >> Cases_on ‘c’
  >> gvs [single_sub_def, single_add_def, mw_and_keep_def]
QED

Theorem mwi_and_neg_pos_lt_thm:
  mwi_and_neg_pos_lt F xs ys = mw_and_keep (mw_bits_of_int xs) ys
Proof
  simp [mw_bits_of_int_def, mwi_and_neg_pos_lt_eq]
QED

Definition mwi_and_fused_def:
  mwi_and_fused (s, xs) (t, ys) =
  if ¬(s ∨ t) then
    (F, mw_fix (mw_and_flip xs ys))
  else if s ∧ ~t then
    (F, mw_fix (if LENGTH xs < LENGTH ys
                then mwi_and_neg_pos_lt F xs ys
                else mwi_and_neg_pos_geq F ys xs))
  else if ~s ∧ t then
    (F, mw_fix (if LENGTH ys < LENGTH xs
                then mwi_and_neg_pos_lt F ys xs
                else mwi_and_neg_pos_geq F xs ys))
  else
    (T, mw_fix (if LENGTH xs ≤ LENGTH ys
                then mwi_and_neg_neg F F T xs ys
                else mwi_and_neg_neg F F T ys xs))
End

Theorem mwi_and_fused_thm:
  mwi_and_fused x y = mwi_and x y
Proof
  PairCases_on ‘x’ >> PairCases_on ‘y’
  >> simp [Ntimes mwi_and_def 2]
  >> simp [mwi_and_fused_def]
  >> IF_CASES_TAC >- simp []
  >> IF_CASES_TAC >- simp [mwi_and_neg_pos_lt_thm, mwi_and_neg_pos_geq_thm]
  >> IF_CASES_TAC >- simp [mwi_and_neg_pos_lt_thm, mwi_and_neg_pos_geq_thm]
  >> simp [mwi_and_neg_neg_thm]
QED

(* verification *)

Theorem mw_fix_lemma[local]:
  (mw2n xs = n) ⇒ mw_fix xs = n2mw n
Proof
  simp [n2mw_mw2n]
QED

Definition b2mw_def:
  b2mw xs =
    if xs = [] then [] else
      n2w (num_of_bits (TAKE (dimindex (:'a)) xs)) ::
      b2mw (DROP (dimindex (:'a)) xs) : 'a word list
Termination
  WF_REL_TAC ‘measure LENGTH’ >> Cases >> simp [LENGTH_DROP]
End

Definition b2mw'_def:
  b2mw' k xs =
    if k = 0 then [] else
      n2w (num_of_bits (TAKE (dimindex (:'a)) xs)) ::
      b2mw' (k-1:num) (DROP (dimindex (:'a)) xs) : 'a word list
End

Theorem num_of_bits_TAKE_dimindex_lt:
  num_of_bits (TAKE (dimindex (:α)) xs) < dimword (:α)
Proof
  irule LESS_LESS_EQ_TRANS
  >> irule_at (Pos hd) num_of_bits_lt
  >> simp [dimword_def, LENGTH_TAKE_EQ]
QED

Theorem num_of_bits_TAKE_dimindex:
  num_of_bits (TAKE (dimindex (:α)) (bits_of_num n)) = n MOD dimword (:α)
Proof
  simp [num_of_bits_TAKE, dimword_def]
QED

Theorem DROP_bits_of_num:
  ∀n m. DROP m (bits_of_num n) = bits_of_num (n DIV (2 ** m))
Proof
  recInduct bits_of_num_ind >> rw []
  >> Cases_on ‘n = 0’ >> gvs []
  >- (once_rewrite_tac [bits_of_num_def] >> simp [])
  >> Cases_on ‘m’ >- simp []
  >> simp [Once bits_of_num_def, SimpLHS]
  >> simp [EXP, DIV_DIV_DIV_MULT]
QED

Theorem DROP_dimindex_bits_of_num:
  DROP (dimindex (:α)) (bits_of_num n) =
  bits_of_num (n DIV (dimword (:α)))
Proof
  simp [DROP_bits_of_num, dimword_def]
QED

Theorem n2mw_eq_b2mw:
  ∀n. n2mw n = b2mw (bits_of_num n) : 'a word list
Proof
  recInduct n2mw_ind >> rw []
  >> Cases_on ‘n = 0’
  >- simp [Once b2mw_def, Once bits_of_num_def, Once n2mw_def]
  >> fs []
  >> simp [Once b2mw_def, bits_of_num_nil]
  >> simp [Once n2mw_def]
  >> simp [num_of_bits_TAKE_dimindex_lt, num_of_bits_TAKE_dimindex,
           DROP_dimindex_bits_of_num]
QED

Theorem mw2n_b2mw:
  ∀bs. mw2n (b2mw bs : 'a word list) = num_of_bits bs
Proof
  recInduct b2mw_ind >> rw []
  >> Cases_on ‘xs = []’
  >> simp [Once b2mw_def, mw2n_def, num_of_bits_def] >> fs []
  >> irule EQ_TRANS
  >> qexists ‘num_of_bits (TAKE (dimindex (:α)) xs ++ (DROP (dimindex (:α)) xs))’
  >> reverse conj_tac >- simp []
  >> rewrite_tac [num_of_bits_append]
  >> simp [num_of_bits_TAKE_dimindex_lt]
  >> Cases_on ‘LENGTH xs ≤ dimindex (:α)’
  >- simp [Req0 DROP_LENGTH_TOO_LONG, num_of_bits_def]
  >> simp [GSYM dimword_def]
QED

Theorem BIT_num_of_bits:
  ∀xs i. BIT i (num_of_bits xs) ⇔ if i < LENGTH xs then xs❲i❳ else F
Proof
  recInduct num_of_bits_ind >> rw [num_of_bits_def]
  >> Cases_on ‘i’ >> simp [BIT_TIMES2, BIT_TIMES2_1]
  >> simp [ADD1]
  >> eq_tac >> simp []
QED

Theorem num_of_bits_and:
  ∀xs ys.
    n2w (num_of_bits xs) && n2w (num_of_bits ys) =
    n2w (num_of_bits (MAP2 $/\ xs ys))
Proof
  simp [fcpTheory.CART_EQ]
  >> simp [word_and_def, fcpTheory.FCP_BETA, n2w_def]
  >> simp [BIT_num_of_bits] >> rw []
  >> Cases_on ‘i < LENGTH xs’ >> fs []
  >> Cases_on ‘i < LENGTH ys’ >> fs []
  >> simp [EL_MAP2]
QED

Theorem num_of_bits_TAKE_and:
  ∀xs ys n.
    n2w (num_of_bits (TAKE n xs)) && n2w (num_of_bits (TAKE n ys)) =
    n2w (num_of_bits (TAKE n (MAP2 $/\ xs ys)))
Proof
  Induct >> simp [num_of_bits_def]
  >> Cases_on ‘ys’ >> simp [num_of_bits_def]
  >> Cases_on ‘n’ >> simp []
  >> rpt strip_tac
  >> once_rewrite_tac [num_of_bits_and]
  >> rpt AP_TERM_TAC >> simp []
  >> simp [GSYM MAP2_TAKE]
  >> irule_at (Pos last) MAP2_SYM
  >> simp [CONJ_SYM]
QED

Theorem LENGTH_b2mw:
  ∀xs. LENGTH (b2mw xs : α word list) = LENGTH xs \\ dimindex (:α)
Proof
  recInduct b2mw_ind >> rw []
  >> Cases_on ‘xs = []’ >> simp [Once b2mw_def]
  >> simp [SUB_CEILING_DIV, ADD1]
  >> ‘0 < LENGTH xs \\ dimindex (:α)’ by
    (irule CEILING_DIV_POS >> simp [LENGTH_NON_NIL])
  >> simp []
QED

Theorem mw_and_b2mw:
  ∀xs ys.
    LENGTH (b2mw xs : 'a word list) ≤ LENGTH (b2mw ys : 'a word list) ⇒
    mw_and (b2mw xs) (b2mw ys) = b2mw (MAP2 $/\ xs ys) : 'a word list
Proof
  recInduct b2mw_ind >> rw []
  >> once_rewrite_tac [b2mw_def]
  >> IF_CASES_TAC >- simp [mw_and_def]
  >> IF_CASES_TAC >- simp [mw_and_def]
  >> IF_CASES_TAC >- (gvs [mw_and_def, MAP2_EQ_NIL])
  >> gvs []
  >> simp [mw_and_def]
  >> conj_tac >- simp [num_of_bits_TAKE_and]
  >> first_assum $ qspec_then ‘DROP (dimindex (:α)) ys’ mp_tac
  >> impl_tac >- gvs [LENGTH_b2mw, SUB_CEILING_DIV]
  >> rw [MAP2_DROP]
QED

Theorem AND_F_K:
  ($/\ F) = K F
Proof
  simp [FUN_EQ_THM]
QED

Theorem bitwise_and_F_F:
  ∀xs ys q x y.
    bits_bitwise $/\ (xs,F) (ys,F) = (q,F) ⇒
    ∃k. q = MAP2 $/\ xs ys ++ REPLICATE k F
Proof
  Induct >> simp [bits_bitwise_def]
  >- (metis_tac [AND_F_K, MAP_K_REPLICATE])
  >> Cases_on ‘ys’ >> simp [bits_bitwise_def]
  >- (metis_tac [K_DEF, MAP_K_REPLICATE, REPLICATE])
  >> rpt (pairarg_tac >> gvs [])
QED

Theorem EVERY_F_num_of_bits:
  ∀xs. EVERY (λx. x = F) xs ⇒ num_of_bits xs = 0
Proof
  recInduct num_of_bits_ind >> rw [num_of_bits_def]
QED

Theorem num_of_bits_leading_F:
  num_of_bits (xs ++ REPLICATE k F) = num_of_bits xs
Proof
  simp [num_of_bits_append, EVERY_F_num_of_bits]
QED

Theorem mwi_and_pos:
  ¬(i < 0) ∧ ¬(j < 0) ⇒ mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  rpt strip_tac
  >> simp [i2mw_def, Once mwi_and_def, mw_and_flip_def, Req0 int_and_sign, INT_ABS]
  >> rw []
  >> irule mw_fix_lemma
  >> simp [int_and_def, int_bitwise_def]
  >> simp [bits_of_int_def]
  >> qmatch_goalsub_abbrev_tac ‘int_of_bits bs’
  >> Cases_on ‘bs’ >> gvs [oneline int_of_bits_def, bits_of_int_def]
  >> drule_then assume_tac bits_bitwise_rest >> gvs []
  >> rewrite_tac [n2mw_eq_b2mw]
  >> DEP_REWRITE_TAC [mw_and_b2mw]
  >> gvs [n2mw_eq_b2mw,mw2n_b2mw]
  >> drule bitwise_and_F_F >> strip_tac >> gvs []
  >> rewrite_tac [num_of_bits_leading_F]
  >> DEP_ONCE_REWRITE_TAC [MAP2_SYM]
  >> rw [] >> eq_tac >> rw []
QED

Theorem b2mw'_eq_b2mw:
  ∀xs. b2mw' (LENGTH xs \\ dimindex (:α)) xs = b2mw xs : 'a word list
Proof
  recInduct b2mw_ind >> rw []
  >> Cases_on ‘xs = []’ >> gvs []
  >> once_rewrite_tac [b2mw_def, b2mw'_def] >> simp []
  >> ‘0 < LENGTH xs \\ dimindex (:α)’ by
    (irule CEILING_DIV_POS >> simp [LENGTH_NON_NIL])
  >> fs [SUB_CEILING_DIV]
QED

Theorem LENGTH_b2mw':
  ∀k xs. LENGTH (b2mw' k xs) = k
Proof
  recInduct b2mw'_ind >> rw []
  >> Cases_on ‘k = 0’
  >> simp [Once b2mw'_def]
QED

Theorem MAP_NOT_EQ:
  ∀xs ys. MAP $¬ xs = MAP $¬ ys ⇔ xs = ys : 'a word list
Proof
  Induct >> Cases_on ‘ys’ >> rw []
QED

Theorem w2n_neg2_plus1:
  w2n (-(2w: α word)) + 1 = w2n (-(1w: α word))
Proof
  simp [w2n_plus1]
  >> Cases_on ‘dimindex (:α) = 1’
  >- simp [dimword_def]
  >> ‘2 < dimword (:α)’ by simp [dimword_def, DIMINDEX_GE_1]
  >> simp []
QED

Theorem single_sub_carry:
  single_sub (x: α word) 0w F = single_sub x 1w T
Proof
  simp [single_sub_def, single_add_def, b2n_def, b2w_def]
  >> ‘w2n (-(2w :α word)) + 1 = w2n (-(1w :α word))’ suffices_by simp []
  >> simp [w2n_neg2_plus1]
QED

Theorem mw_sub_carry:
  ∀xs. xs ≠ [] ⇒ mw_sub xs [] F = mw_sub xs [1w] T
Proof
  Induct >> rw [mw_sub_def]
  >> rpt (pairarg_tac >> gvs [])
  >> gvs [single_sub_carry]
QED

Theorem mw2n_eq:
  ∀xs ys. mw2n xs = mw2n ys ∧ LENGTH xs = LENGTH ys ⇒ xs = ys
Proof
  Induct >> Cases_on ‘ys’ >> simp [mw2n_def]
  >> ntac 2 strip_tac
  >> rename1 ‘w2n x + _ * mw2n xs = w2n y + _ * mw2n ys’
  >> ‘w2n x = w2n y’ suffices_by (strip_tac >> gvs [ZERO_LT_dimword])
  >> qmatch_asmsub_abbrev_tac ‘r₁ + n * k₁ = r₂ + _ * k₂’
  >> ‘r₁ < n ∧ r₂ < n’ by (unabbrev_all_tac >> simp [w2n_lt])
  >> rpt $ qpat_x_assum ‘Abbrev _’ $ kall_tac
  >> ‘(r₁ + n * k₁) MOD n = (r₂ + n * k₂) MOD n’ by simp []
  >> ‘r₁ MOD n = r₂ MOD n’ by metis_tac [MOD_TIMES, MULT_COMM, ADD_COMM]
  >> imp_res_tac LESS_MOD >> simp []
QED

(* from HOL *)
val mw_sub_thm = prove(
  ``!xs ys c zs d.
     (LENGTH xs = LENGTH ys) /\ mw2n ys <= mw2n xs ==>
     (mw2n (FST (mw_sub xs ys T)) = mw2n xs - mw2n ys)``,
  cheat);

(* From HOL *)
val mw_sub_APPEND_0 = prove(
  ``!n xs ys c. mw_sub xs (ys ++ REPLICATE n 0w) c = mw_sub xs ys c``,
cheat);

(* From HOL *)
val mw2n_REPLICATE = prove(
  ``!n. mw2n (REPLICATE n 0x0w) = 0``,
  Induct THEN1 EVAL_TAC
  \\ ASM_SIMP_TAC std_ss [REPLICATE,mw2n_def,w2n_n2w,ZERO_LT_dimword]);

Theorem mw2n_mw_sub:
  mw2n ys ≤ mw2n xs ∧ LENGTH ys ≤ LENGTH xs ⇒
  mw2n (FST (mw_sub xs ys T)) = mw2n xs - mw2n ys
Proof
  disch_tac
  >> qabbrev_tac ‘zs = REPLICATE (LENGTH xs - LENGTH ys) 0w : α word list’
  >> ‘mw2n (FST (mw_sub xs ys T)) = mw2n (FST (mw_sub xs (ys ⧺ zs) T))’ by
    (unabbrev_all_tac >> simp [mw_sub_APPEND_0])
  >> pop_assum SUBST_ALL_TAC
  >> ‘mw2n (ys ⧺ zs) = mw2n ys’ by
    (unabbrev_all_tac >> simp [mw2n_APPEND, mw2n_REPLICATE])
  >> DEP_REWRITE_TAC [mw_sub_thm]
  >> unabbrev_all_tac >> simp [mw2n_APPEND]
QED

Theorem LENGTH_n2mw_DIV_dimword:
  ∀n.
    LENGTH (n2mw (n DIV dimword (:α)) :α word list) =
    LENGTH (n2mw n :α word list) - 1
Proof
  recInduct n2mw_ind >> rw []
  >> Cases_on ‘n = 0’
  >- (once_rewrite_tac [n2mw_def] >> simp [])
  >> once_rewrite_tac [n2mw_def] >> fs []
  >> IF_CASES_TAC >- simp [Once n2mw_def]
  >> simp [ADD1]
  >> ‘LENGTH (n2mw (n DIV dimword (:α)) :α word list) ≠ 0’ by
    (CCONTR_TAC >> gvs [n2mw_NIL])
  >> simp []
QED

Theorem b2mw'_nil_REPLICATE:
  ∀k. b2mw' k [] = REPLICATE k 0w
Proof
  Induct >> simp [Once b2mw'_def]
  >> EVAL_TAC >> simp [MOD_0]
QED

Theorem b2mw'_n2mw:
  ∀x k.
    LENGTH (n2mw x :α word list) ≤ k ⇒
    b2mw' k (bits_of_num x) =
    n2mw x ⧺ REPLICATE (k - LENGTH (n2mw x :α word list)) 0w :α word list
Proof
  recInduct n2mw_ind >> rw []
  >> Cases_on ‘n = 0’ >> fs []
  >-
   (once_rewrite_tac [n2mw_def, bits_of_num_def]
    >> simp [b2mw'_nil_REPLICATE])
  >> once_rewrite_tac [b2mw'_def]
  >> IF_CASES_TAC >> fs []
  >> simp [DROP_dimindex_bits_of_num]
  >> fs [LENGTH_n2mw_DIV_dimword]
  >> simp [num_of_bits_TAKE_dimindex]
  >> simp [Once n2mw_def, SimpRHS]
  >> simp [LENGTH_n2mw_DIV_dimword]
  >> cong_tac (SOME 1)
  >> ‘LENGTH (n2mw n) ≠ 0’ by simp [n2mw_NIL]
  >> simp []
QED

Theorem mw_sub_n2mw_b2mw':
  n ≠ 0 ⇒
  FST (mw_sub (n2mw (n :num) :α word list) [] F) =
  b2mw' (LENGTH (n2mw n :α word list)) (bits_of_num (Num (&n − 1)))
Proof
  disch_tac
  >> ‘n2mw n ≠ []’ by simp [n2mw_NIL]
  >> DEP_REWRITE_TAC [mw_sub_carry] >> simp []
  >> irule mw2n_eq
  >> conj_tac >-
   (‘LENGTH (FST (mw_sub (n2mw n: α word list) [1w] T)) =
     LENGTH (n2mw n: α word list)’ by
      (Cases_on ‘mw_sub (n2mw n) [1w] T’ >> drule LENGTH_mw_sub >> simp [])
    >> simp [LENGTH_b2mw'])
  >> DEP_REWRITE_TAC [mw2n_mw_sub]
  >> rpt conj_tac
  >- simp [mw2n_def, mw2n_n2mw]
  >- simp [Once n2mw_def]
  >> ‘Num (&n - 1) = n - 1’ by (DEP_REWRITE_TAC [INT_SUB] >> simp [])
  >> pop_assum SUBST_ALL_TAC
  >> DEP_REWRITE_TAC [b2mw'_n2mw]
  >> conj_tac >- simp [LENGTH_n2mw_LESS_LENGTH_n2mw]
  >> simp [mw2n_def, mw2n_n2mw, mw2n_APPEND, mw2n_REPLICATE]
QED

Theorem mw_bits_of_int_b2mw:
  ∀n. n ≠ 0 ⇒
      mw_bits_of_int (b2mw (bits_of_num n)) =
      MAP $¬ (b2mw' (LENGTH (b2mw (bits_of_num n) : 'a word list))
                    (bits_of_num (Num (& n - 1)))) : 'a word list
Proof
  rw [mw_bits_of_int_def, UNCURRY, MAP_NOT_EQ]
  >> Cases_on ‘mw_sub (b2mw (bits_of_num n)) [] F’ >> simp []
  >> fs [GSYM n2mw_eq_b2mw, GSYM mw_sub_n2mw_b2mw']
QED

Theorem selftest_1:
  EVERY
    (λn. mw_bits_of_int (b2mw (bits_of_num n)) =
         MAP $¬ (b2mw' (LENGTH (b2mw (bits_of_num n) : word3 list))
                       (bits_of_num (Num (& n - 1)))) : word3 list)
    (GENLIST (λn. n + 1) 10)
Proof
  CONV_TAC (RAND_CONV EVAL)
  >> rewrite_tac [EVERY_DEF] >> rpt strip_tac >> simp []
  >> TRY (EVAL_TAC >> NO_TAC)
QED

Theorem b2mw_nil:
  ∀xs. b2mw xs = [] ⇔ xs = []
Proof
  Induct >> simp [Once b2mw_def]
QED

Theorem num_of_bits_REPLICATE_F:
  ∀x. num_of_bits (REPLICATE x F) = 0
Proof
  Induct >> simp [num_of_bits_def]
QED

Theorem bits_bitwise_TAKE_DROP:
  ∀f xs b₁ ys b₂ zs b₃ n.
    bits_bitwise f (xs, b₁) (ys, b₂) = (zs, b₃) ⇔
      bits_bitwise f (TAKE n xs, b₁) (TAKE n ys, b₂) = (TAKE n zs, b₃) ∧
      bits_bitwise f (DROP n xs, b₁) (DROP n ys, b₂) = (DROP n zs, b₃)
Proof
  recInduct bits_bitwise_ind >> rw []
  >> eq_tac >> rw []
  >- fs []
  >- fs [MAP_TAKE]
  >- fs [MAP_DROP]
  >- metis_tac [TAKE_DROP, MAP_TAKE, MAP_DROP, MAP]
  >- fs [MAP_TAKE]
  >- fs [MAP_DROP]
  >-
   (rename1 ‘f b1 r2::MAP (λx. f x r2) bs1’
    >> ‘MAP (λx. f x r2) (b1::bs1) = zs’ suffices_by rw [MAP]
    >> metis_tac [TAKE_DROP, MAP_TAKE, MAP_DROP, MAP])
  >-
   (Cases_on ‘n’
    >> gvs [bits_bitwise_def]
    >> rpt (pairarg_tac >> gvs [])
    >- (drule bits_bitwise_rest >> simp [])
    >> rename1 ‘_ = TAKE _ bs' ∧ _ = b₃’
    >> first_x_assum $ qspecl_then [‘bs'’, ‘b₃’]assume_tac >> gvs [])
  >-
   (Cases_on ‘n’
    >> gvs [bits_bitwise_def]
    >> rpt (pairarg_tac >> gvs [])
    >> rename1 ‘_ = (DROP _ bs, b₃)’
    >> first_x_assum $ qspecl_then [‘bs’, ‘b₃’]assume_tac >> gvs [])
  >-
   (Cases_on ‘n’
    >> gvs [bits_bitwise_def]
    >> rpt (pairarg_tac >> gvs [])
    >> rename1 ‘_::bs = _ ∧ r = _’
    >> first_x_assum $ qspecl_then [‘bs’, ‘r’] assume_tac >> gvs []
    >> metis_tac [TAKE_DROP, APPEND])
QED

Theorem MAP_AND_T:
  ∀xs. MAP ($/\ T) xs = xs
Proof
  Induct >> simp []
QED

Theorem MAP_OR_F:
  ∀xs. MAP ($\/ F) xs = xs
Proof
  Induct >> simp []
QED

Theorem MAP_LAMBDA_F:
  MAP (λx. F) xs = REPLICATE (LENGTH xs) F
Proof
  metis_tac [K_DEF, MAP_K_REPLICATE]
QED

Theorem neg_n2w_SUC:
  -n2w (SUC k) = ¬n2w (k)
Proof
  simp []
QED

Theorem num_of_bits_DIV_2:
  num_of_bits (x::xs) DIV 2 = num_of_bits xs
Proof
  Cases_on ‘x’ >> simp [num_of_bits_def]
QED

Theorem ODD_num_of_bits:
  ODD (num_of_bits (x::xs)) = x
Proof
  Cases_on ‘x’ >> simp [num_of_bits_def]
  >- simp [ODD_DOUBLE, GSYM ADD1]
  >- simp [ODD_EVEN, EVEN_DOUBLE]
QED

Theorem n2w_and_not_BITWISE:
  n2w n && ¬n2w m = n2w (BITWISE (dimindex (:α)) (λa b. a ∧ ¬b) n m) : α word
Proof
  simp [CART_EQ, word_and_def, FCP_BETA]
  >> rewrite_tac [neg_n2w_SUC, word_1comp_def]
  >> simp [FCP_BETA, n2w_def, BITWISE_THM]
QED

Theorem BITWISE_AND_NOT_zero_left:
  ∀k n. BITWISE k (λa b. a ∧ ¬b) 0 n = 0
Proof
  Induct >> rw [BITWISE_def, SBIT_def]
QED

Theorem BITWISE_AND_NOT_zero:
  ∀k. BITWISE k (λa b. a ∧ ¬b) 0 0 = 0
Proof
  Induct >> rw [BITWISE_def, SBIT_def]
QED

Theorem BITWISE_AND_NOT_zero_right:
  ∀xs k.
    LENGTH xs ≤ k ⇒
    BITWISE k (λa b. a ∧ ¬b) (num_of_bits xs) 0 = (num_of_bits xs)
Proof
  Induct >> rw [BITWISE_def, num_of_bits_def]
  >- simp [BITWISE_AND_NOT_zero]
  >> Cases_on ‘k’ >> fs []
  >> simp [BITWISE_EVAL, ODD_num_of_bits, num_of_bits_DIV_2, SBIT_def]
  >> rw [num_of_bits_def]
QED

Theorem bits_bitwise_and_not_BITWISE:
  ∀ys xs zs k.
    bits_bitwise $/\ (MAP $¬ xs,T) (ys,F) = (zs,F) ∧
    LENGTH ys ≤ k
    ⇒
    BITWISE k (λa b. a ∧ ¬b) (num_of_bits ys) (num_of_bits xs) =
    num_of_bits zs
Proof
  Induct >> rw []
  >- simp [num_of_bits_def, MAP_LAMBDA_F, num_of_bits_REPLICATE_F,
            BITWISE_AND_NOT_zero_left]
  >> Cases_on ‘xs’
  >- gvs [num_of_bits_def, MAP_AND_T, BITWISE_AND_NOT_zero_right]
  >> Cases_on ‘k’ >> fs []
  >> simp [BITWISE_EVAL]
  >> gvs [bits_bitwise_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [num_of_bits_DIV_2, ODD_num_of_bits]
  >> first_x_assum drule_all >> rw []
  >> once_rewrite_tac [num_of_bits_cons]
  >> simp []
  >> simp [oneline num_of_bits_def]
  >> rw [SBIT_def] >> fs []
QED

Theorem bits_bitwise_and_not_w2n:
  ∀xs ys zs.
    bits_bitwise $/\ (MAP $¬ xs,T) (ys,F) = (zs,F) ∧
    LENGTH ys ≤ dimindex (:α) ∧
    num_of_bits zs < dimword (:α) ⇒
    w2n ((n2w (num_of_bits ys) :α word) &&
    -(n2w (SUC (num_of_bits xs)) :α word)) =
    (num_of_bits zs)
Proof
  rw []
  >> rewrite_tac [neg_n2w_SUC, n2w_and_not_BITWISE]
  >> simp []
  >> drule bits_bitwise_and_not_BITWISE
  >> disch_then $ DEP_REWRITE_TAC o single
  >> simp []
QED

Theorem mw2n_mw_and_keep_not:
  ∀l xs ys zs.
    bits_bitwise $/\ (MAP $¬ xs,T) (ys,F) = (zs,F) ∧
    LENGTH (b2mw xs : 'a word list) ≤ l ∧
    l < LENGTH (b2mw ys : 'a word list) ⇒
    mw2n (mw_and_keep (MAP $¬ (b2mw' l xs)) (b2mw ys : 'a word list)) =
    num_of_bits zs
Proof
  recInduct b2mw'_ind >> rw []
  >> Cases_on ‘k = 0’ >> fs []
  >-
   (simp [Once b2mw'_def]
    >> gvs [mw_and_keep_nil_left, mw2n_b2mw, b2mw_nil]
    >> simp [MAP_AND_T])
  >> once_rewrite_tac [b2mw'_def, b2mw_def] >> simp []
  >> Cases_on ‘ys = []’ >> gvs []
  >-
   (once_rewrite_tac [b2mw_def]
    >> simp [mw_and_keep_def, mw2n_def]
    >> metis_tac [K_DEF, MAP_K_REPLICATE, num_of_bits_REPLICATE_F])
  >> simp [mw_and_keep_def, mw2n_def]
  >> drule $ iffLR bits_bitwise_TAKE_DROP
  >> disch_then $ qspec_then ‘dimindex (:α)’ assume_tac
  >> fs [MAP_DROP] >> first_assum drule
  >> impl_tac >- gvs [LENGTH_b2mw, SUB_CEILING_DIV]
  >> strip_tac >> simp []
  >> gvs [GSYM MAP_DROP, GSYM MAP_TAKE]
  >> qspec_then ‘TAKE (dimindex (:α)) xs’ mp_tac bits_bitwise_and_not_w2n
  >> disch_then drule
  >> impl_tac >- simp [num_of_bits_TAKE_dimindex_lt, LENGTH_TAKE_EQ]
  >> simp [num_of_bits_TAKE_DROP_dimindex]
QED

Theorem mw2n_mw_and_not:
  ∀l xs ys zs.
    bits_bitwise $/\ (MAP $¬ xs,T) (ys,F) = (zs,F) ∧
    LENGTH (b2mw ys : 'a word list) ≤ l ⇒
    mw2n (mw_and (b2mw ys : 'a word list) (MAP $¬ (b2mw' l xs))) =
    num_of_bits zs
Proof
  recInduct b2mw'_ind >> rw []
  >> Cases_on ‘k = 0’ >> gvs []
  >- (gvs [mw_and_nil_left, mw2n_def, b2mw_nil, MAP_LAMBDA_F,
           num_of_bits_REPLICATE_F])
  >> once_rewrite_tac [b2mw'_def, b2mw_def] >> simp []
  >> Cases_on ‘ys = []’ >> gvs []
  >- simp [mw_and_nil_left, mw2n_def, MAP_LAMBDA_F, num_of_bits_REPLICATE_F]
  >> simp [mw_and_def, mw2n_def]
  >> drule $ iffLR bits_bitwise_TAKE_DROP
  >> disch_then $ qspec_then ‘dimindex (:α)’ assume_tac
  >> fs [MAP_DROP] >> first_assum drule
  >> impl_tac >- gvs [LENGTH_b2mw, SUB_CEILING_DIV]
  >> strip_tac >> simp []
  >> gvs [GSYM MAP_DROP, GSYM MAP_TAKE]
  >> qspec_then ‘TAKE (dimindex (:α)) xs’ mp_tac bits_bitwise_and_not_w2n
  >> disch_then drule
  >> impl_tac >- simp [num_of_bits_TAKE_dimindex_lt, LENGTH_TAKE_EQ]
  >> simp [num_of_bits_TAKE_DROP_dimindex]
QED

Theorem mwi_and_neg_pos:
  (i < 0) ∧ ¬(j < 0) ⇒ mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  rpt strip_tac
  >> simp [i2mw_def, Once mwi_and_def, mw_and_flip_def, Req0 int_and_sign, INT_ABS]
  >> rw []
  >> irule mw_fix_lemma
  >> simp [int_and_def, int_bitwise_def]
  >> simp [bits_of_int_def, int_not_def]
  >> Cases_on ‘i’ >> gvs []
  >> qmatch_goalsub_abbrev_tac ‘int_of_bits bs’
  >> Cases_on ‘bs’ >> gvs [oneline int_of_bits_def, bits_of_int_def]
  >> drule_then assume_tac bits_bitwise_rest >> gvs []
  >> rewrite_tac [n2mw_eq_b2mw]
  >> simp [mw_bits_of_int_b2mw]
  >> fs [mw_bits_of_int_b2mw] >> simp []
  >-
   (irule mw2n_mw_and_keep_not >> simp []
    >> simp [GSYM n2mw_eq_b2mw]
    >> ‘Num (&n - 1) = n - 1’ by (DEP_REWRITE_TAC [INT_SUB] >> simp [])
    >> pop_assum SUBST_ALL_TAC
    >> simp [LENGTH_n2mw_LESS_LENGTH_n2mw])
  >> irule mw2n_mw_and_not >> simp [GSYM n2mw_eq_b2mw]
QED

Theorem mwi_and_pos_neg:
  ¬(i < 0) ∧ (j < 0) ⇒ mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  rpt strip_tac
  >> simp [i2mw_def, Once mwi_and_def, mw_and_flip_def, Req0 int_and_sign, INT_ABS]
  >> drule_all mwi_and_neg_pos
  >> simp [i2mw_def, mw_and_flip_def, Req0 int_and_sign, INT_ABS]
  >> rw [] >> rpt AP_TERM_TAC
  >> simp [Once int_and_sym]
QED

Theorem b2mw'_0:
  b2mw' 0 xs = []
Proof
  simp [Once b2mw'_def]
QED

Theorem MAP_NOT_NOT:
  MAP $¬ (MAP $¬ xs) = xs
Proof
  Induct_on ‘xs’ >> rw []
QED

Theorem MAP_word1_comp_word1_comp:
  MAP $¬ (MAP $¬ xs : 'a word list) = xs
Proof
  Induct_on ‘xs’ >> rw []
QED

Theorem mw_int_of_bits_nil:
  mw_int_of_bits [] = [1w]
Proof
  simp [mw_int_of_bits_def, mw_add_def]
QED

Theorem K_LAMBDA:
  K x = λy. x
Proof
  simp [K_DEF]
QED

(* TODO HOL has a more restrictive version - replace it with this one *)
Theorem mw_add_F:
  ∀xs ys.
    LENGTH ys = LENGTH xs ⇒
    mw_add xs (MAP (\x. 0x0w) ys) F = (xs,F)
Proof
  Induct >> rw [mw_add_def]
  >> rpt (pairarg_tac >> gvs [])
  >> Cases_on ‘ys’ >> gvs []
  >> rename1 ‘single_add y’
  >> gvs [single_add_def, b2w_def, b2n_def]
  >> ‘w2n y < dimword (:α)’ by simp [w2n_lt]
  >> last_x_assum $ drule_then assume_tac >> gvs[]
QED

Theorem w2n_b2w_T:
  w2n (b2w T) = 1
Proof
  simp [b2w_def, b2n_def]
QED

Theorem mw2n_mw_int_of_bits:
  ∀xs. mw2n (mw_int_of_bits xs) = mw2n (MAP $¬ xs) + 1
Proof
  Induct_on ‘xs’
  >- simp [mw_int_of_bits_nil, mw2n_def]
  >> strip_tac >> rename1 ‘x::xs’
  >> gvs [mw2n_def, mw_int_of_bits_def, mw_add_def]
  >> rpt (pairarg_tac >> gvs [])
  >> gvs [MAP_word1_comp_word1_comp, single_add_def]
  >> Cases_on ‘dimword (:α) ≤ b2n T + w2n (¬x)’
  >> gvs [b2n_def]
  >-
   (‘w2n (¬x) = dimword (:α) - 1’ by
      (qspec_then ‘¬x’ assume_tac w2n_lt >> simp [])
    >> ‘¬x + b2w T = 0w’ by gvs [GSYM w2n_minus1, b2w_def, b2n_def]
    >> IF_CASES_TAC >> gvs [mw2n_def, ZERO_LT_dimword])
  >> gvs [K_LAMBDA, mw_add_F, mw2n_def]
  >> DEP_REWRITE_TAC [w2n_add_2]
  >> simp [b2w_def, b2n_def]
QED

Theorem mw2n_b2mw':
  ∀l xs.
    LENGTH (b2mw xs : 'a word list) ≤ l ⇒
    mw2n (b2mw' l xs : 'a word list) = num_of_bits xs
Proof
  recInduct b2mw'_ind >> rw []
  >> Cases_on ‘k = 0’ >> gvs []
  >- fs [b2mw_nil, b2mw'_0, mw2n_def, num_of_bits_def]
  >> once_rewrite_tac [b2mw'_def]
  >> simp [mw2n_def]
  >> qpat_x_assum ‘ _ ⇒ _’ $ DEP_REWRITE_TAC o single
  >> conj_tac >- gvs [LENGTH_b2mw, SUB_CEILING_DIV]
  >> simp [num_of_bits_TAKE_dimindex_lt, num_of_bits_TAKE_DROP_dimindex]
QED

Theorem bits_bitwise_and_not_not_or:
  bits_bitwise $/\ (MAP $¬ xs,b₁) (MAP $¬ ys,b₂) = (zs,b₃)
  ⇔
  bits_bitwise $\/ (xs,¬b₁) (ys,¬b₂) = (MAP $¬ zs,¬b₃)
Proof
  simp [Once bits_bitwise_MAP_NOT, SimpLHS]
  >> simp [MAP_NOT_NOT]
  >> ‘(λa b. a ∨ b) = $\/’ by simp [FUN_EQ_THM]
  >> simp []
QED

Theorem BITWISE_OR_zero_right:
  ∀k n xs.
    LENGTH xs ≤ k ⇒
    BITWISE k (λa b. a ∨ b) (num_of_bits xs) 0 = (num_of_bits xs)
Proof
  Induct >> rw []
  >- simp [num_of_bits_def, BITWISE_def]
  >> Cases_on ‘xs’
  >- (simp [num_of_bits_def, BITWISE_def, SBIT_def])
  >> gvs [BITWISE_EVAL, ODD_num_of_bits, num_of_bits_DIV_2, SBIT_def]
  >> rw [num_of_bits_def]
QED

Theorem BITWISE_OR_zero_left:
  ∀k n ys.
    LENGTH ys ≤ k ⇒
    BITWISE k (λa b. a ∨ b) 0 (num_of_bits ys) = (num_of_bits ys)
Proof
  Induct >> rw []
  >- simp [num_of_bits_def, BITWISE_def]
  >> Cases_on ‘ys’
  >- (simp [num_of_bits_def, BITWISE_def, SBIT_def])
  >> gvs [BITWISE_EVAL, ODD_num_of_bits, num_of_bits_DIV_2, SBIT_def]
  >> rw [num_of_bits_def]
QED

Theorem bits_bitwise_or_BITWISE:
  ∀xs ys zs k b.
    bits_bitwise $\/ (xs,F) (ys,F) = (zs,b) ∧
    LENGTH xs ≤ k ∧ LENGTH ys ≤ k ⇒
    BITWISE k (λa b. a ∨ b) (num_of_bits xs) (num_of_bits ys) =
    num_of_bits zs
Proof
  Induct >> rw []
  >- simp [num_of_bits_def, Req0 BITWISE_OR_zero_left, MAP_OR_F]
  >> Cases_on ‘ys’
  >- gvs [num_of_bits_def, BITWISE_OR_zero_right]
  >> Cases_on ‘k’ >> fs []
  >> simp [BITWISE_EVAL]
  >> gvs [bits_bitwise_def]
  >> rpt (pairarg_tac >> gvs [])
  >> simp [num_of_bits_DIV_2, ODD_num_of_bits]
  >> first_x_assum $ drule_all_then assume_tac
  >> simp []
  >> once_rewrite_tac [num_of_bits_cons]
  >> simp [oneline num_of_bits_def, SBIT_def]
QED

Theorem bits_bitwise_and_not_not_w2n:
  ∀xs ys zs.
    bits_bitwise $/\ (MAP $¬ xs,T) (MAP $¬ ys,T) = (zs,T) ∧
    LENGTH xs ≤ dimindex (:α) ∧ LENGTH ys ≤ dimindex (:α) ∧
    num_of_bits (MAP $¬ zs) < dimword (:α) ⇒
    w2n
      (¬-(n2w (SUC (num_of_bits xs)) :α word) ‖
       ¬-n2w (SUC (num_of_bits ys))) =
    num_of_bits (MAP $¬ zs)
Proof
  rpt gen_tac
  >> rewrite_tac [neg_n2w_SUC, WORD_NOT_NOT, word_or_n2w]
  >> simp [bits_bitwise_and_not_not_or]
  >> strip_tac
  >> drule bits_bitwise_or_BITWISE
  >> ‘(λa b. a ∨ b) = $\/’ by simp [FUN_EQ_THM]
  >> simp []
QED

Theorem mw2n_mw_and_keep_not_not:
  ∀l xs l' ys zs.
    bits_bitwise $/\ (MAP $¬ xs,T) (MAP $¬ ys,T) = (zs,T) ∧ l ≤ l' ∧
    LENGTH (b2mw xs : 'a word list) ≤ l ∧ LENGTH (b2mw ys : 'a word list) ≤ l' ⇒
    mw2n
      (MAP $¬
         (mw_and_keep
            (MAP $¬ (b2mw' l xs : 'a word list))
            (MAP $¬ (b2mw' l' ys : 'a word list)))) =
    num_of_bits (MAP $¬ zs)
Proof
  recInduct b2mw'_ind >> rw []
  >> Cases_on ‘k = 0’ >> gvs []
  >- gvs [b2mw_nil, b2mw'_0, mw_and_keep_nil_left, MAP_word1_comp_word1_comp,
          MAP_AND_T, MAP_NOT_NOT, mw2n_b2mw']
  >> once_rewrite_tac [b2mw'_def] >> simp []
  >> simp [mw_and_keep_def, mw2n_def]
  >> drule $ iffLR bits_bitwise_TAKE_DROP
  >> disch_then $ qspec_then ‘dimindex (:α)’ assume_tac
  >> fs [GSYM MAP_DROP] >> first_assum drule
  >> disch_then $ qspec_then ‘l' - 1’ mp_tac
  >> impl_tac >- gvs [LENGTH_b2mw, SUB_CEILING_DIV]
  >> strip_tac >> simp []
  >> gvs [GSYM MAP_DROP, GSYM MAP_TAKE]
  >> qspec_then ‘TAKE (dimindex (:α)) xs’ mp_tac bits_bitwise_and_not_not_w2n
  >> disch_then drule
  >> impl_tac >- simp [num_of_bits_TAKE_dimindex_lt, MAP_TAKE, LENGTH_TAKE_EQ]
  >> strip_tac >> simp [MAP_TAKE, MAP_DROP, num_of_bits_TAKE_DROP_dimindex]
QED

Theorem mwi_and_neg:
  (i < 0) ∧ (j < 0) ⇒ mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  rpt strip_tac
  >> simp [i2mw_def, Once mwi_and_def, mw_and_keep_flip_def, Req0 int_and_sign, INT_ABS]
  >> rw []
  >> irule mw_fix_lemma
  >> simp [int_and_def, int_bitwise_def]
  >> simp [bits_of_int_def, int_not_def]
  >> Cases_on ‘i’ >> gvs []
  >> Cases_on ‘j’ >> gvs []
  >> qmatch_goalsub_abbrev_tac ‘int_of_bits bs’
  >> Cases_on ‘bs’ >> gvs [oneline int_of_bits_def, bits_of_int_def]
  >> drule_then assume_tac bits_bitwise_rest >> gvs []
  >> rewrite_tac [n2mw_eq_b2mw]
  >> simp [mw_bits_of_int_b2mw,int_not_def,integerTheory.int_calculate,
           mw2n_mw_int_of_bits]
  >> irule mw2n_mw_and_keep_not_not
  >> fs [GSYM n2mw_eq_b2mw, LENGTH_mw_bits_of_int, bits_bitwise_and_sym]
  >> ‘Num (&n - 1) = n - 1’ by (DEP_REWRITE_TAC [INT_SUB] >> simp [])
  >> pop_assum SUBST_ALL_TAC
  >> ‘Num (&n' - 1) = n' - 1’ by (DEP_REWRITE_TAC [INT_SUB] >> simp [])
  >> pop_assum SUBST_ALL_TAC
  >> simp [LENGTH_n2mw_LESS_LENGTH_n2mw]
QED

Theorem selftest_2[local]:
  EVERY
    (λ(i,j). mw2i (mwi_and (i2mw i) (i2mw j : bool # word2 list)) = int_and i j)
    (FLAT $ GENLIST (λi. GENLIST (λj. (&i - 5, &j - 5)) 10) 10)
Proof
  CONV_TAC (RAND_CONV EVAL)
  >> rewrite_tac [EVERY_DEF] >> rpt strip_tac
  >> TRY (EVAL_TAC >> NO_TAC)
QED

Theorem mwi_and_thm:
  mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  Cases_on ‘i < 0’ >> Cases_on ‘j < 0’
  >> simp [mwi_and_neg_pos, mwi_and_pos_neg, mwi_and_pos, mwi_and_neg]
QED
