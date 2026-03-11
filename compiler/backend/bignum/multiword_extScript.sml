(*
  Extensions to multiword that should be upstreamed.
*)
Theory multiword_ext
Ancestors
  integer
  int_bitwise
  multiword
Libs
  preamble wordsLib

(** Helper lemmas for int_bitwise *********************************************)

(* TODO Decide which of these should live in int_bitwise and move them. *)

Theorem int_of_bits_sign[local]:
  int_of_bits bs < 0 ⇔ SND bs
Proof
  namedCases_on ‘bs’ ["xs r"] >> Cases_on ‘r’
  >> simp [int_of_bits_def, int_not_def]
  >> intLib.COOPER_TAC
QED

Theorem bits_bitwise_rest[local]:
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

(* TODO Copied from HOL - Remove HOL version (too specific) *)
Theorem bits_bitwise_empty_left[simp]:
  ∀xs rest f. bits_bitwise f ([],b) (xs,rest) = (MAP (f b) xs,f b rest)
Proof
  Induct >> fs [bits_bitwise_def]
QED

(* TODO Copied from HOL - Remove HOL version (too specific) *)
Theorem bits_bitwise_empty_right[simp]:
  ∀xs rest f. bits_bitwise f (xs,rest) ([],b) = (MAP (λx. f x b) xs,f rest b)
Proof
  Induct >> fs [bits_bitwise_def]
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

Theorem bits_bitwise_and:
  ∀x y. bits_bitwise $/\ x y = bits_bitwise $/\ y x
Proof
  rpt Cases >> irule bits_bitwise_sym >> rpt Cases >> simp []
QED

Theorem int_and_sym:
  int_and i j = int_and j i
Proof
  simp [int_and_def, int_bitwise_def, bits_bitwise_and]
QED


(** multiword extensions ******************************************************)

(* TODO Move to HOL's multiword. *)

Definition mw_neg_def:
  mw_neg xs =
    let (ys,c) = mw_sub xs [] F in
      MAP (~) ys
End

Definition mw_neg_expand_def:
  mw_neg_expand xs =
    let (ys,c) = mw_sub xs [] F in
      if c then MAP (~) ys else MAP (~) ys ++ [1w]
End

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
                then mw_and_keep (mw_neg xs) ys
                else mw_and ys (mw_neg xs)))
  else if ~s ∧ t then
    mwi_and (t, ys) (s, xs)
  else
    (T, mw_fix (mw_neg_expand (mw_and_keep_flip (mw_neg xs) (mw_neg ys))))
Termination
  WF_REL_TAC ‘measure $ λ((s,xs),(t,ys)). if t then 1 else 0n’
End

(* verification *)

Theorem mw_fix_lemma:
  (mw2n xs = n) ⇒ mw_fix xs = n2mw n
Proof
  cheat
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

Theorem n2mw_eq_b2mw:
  n2mw n = b2mw (bits_of_num n) : 'a word list
Proof
  cheat
QED

Theorem mw2n_b2mw:
  ∀bs. mw2n (b2mw bs : 'a word list) = num_of_bits bs
Proof
  cheat
QED

Theorem mw_and_b2mw:
  ∀xs ys.
    LENGTH (b2mw xs : 'a word list) ≤ LENGTH (b2mw ys : 'a word list) ⇒
    mw_and (b2mw xs) (b2mw ys) = b2mw (MAP2 $/\ xs ys) : 'a word list
Proof
  cheat
QED

Theorem mw_and_keep_b2mw:
  ∀xs ys.
    LENGTH (b2mw xs : 'a word list) ≤ LENGTH (b2mw ys : 'a word list) ⇒
    mw_and_keep (b2mw xs) (b2mw ys) =
    b2mw (MAP2 $/\ xs ys ++ DROP (LENGTH xs) ys) : 'a word list
Proof
  cheat
QED

Theorem bitwise_and_F_F:
  ∀xs ys q x y.
    bits_bitwise $/\ (xs,F) (ys,F) = (q,F) ⇒
    ∃k. q = MAP2 $/\ xs ys ++ REPLICATE k F
Proof
  cheat
QED

Theorem num_of_bits_leading_F:
  num_of_bits (xs ++ REPLICATE k F) = num_of_bits xs
Proof
  cheat
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
  Induct \\ Cases_on ‘ys’ \\ gvs []
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

Theorem mw_neg_b2mw:
  ∀n. n ≠ 0 ⇒
      mw_neg (b2mw (bits_of_num n)) =
      MAP $¬ (b2mw' (LENGTH (b2mw (bits_of_num n) : 'a word list))
                    (bits_of_num (Num (& n - 1)))) : 'a word list
Proof
  cheat
QED

Theorem selftest_1:
  EVERY
    (λn. mw_neg (b2mw (bits_of_num n)) =
         MAP $¬ (b2mw' (LENGTH (b2mw (bits_of_num n) : word3 list))
                       (bits_of_num (Num (& n - 1)))) : word3 list)
    (GENLIST (λn. n + 1) 10)
Proof
  CONV_TAC (RAND_CONV EVAL)
  >> rewrite_tac [EVERY_DEF] >> rpt strip_tac >> simp []
  >> TRY (EVAL_TAC >> NO_TAC)
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
  >> simp [mw_neg_b2mw]
  >> fs [mw_neg_b2mw] >> simp []
  >> cheat
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
  >> simp [mw_neg_b2mw,int_not_def,integerTheory.int_calculate]
  >> cheat
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
