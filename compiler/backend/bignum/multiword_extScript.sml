(*
  TODO Extensions to multiword that should be upstreamed.
*)
Theory multiword_ext
Ancestors
  integer
  int_bitwise
  multiword
Libs
  preamble

(** Helper lemmas for int_bitwise *********************************************)

(* TODO Decide which of these should live in int_bitwise and move them. *)

Theorem int_of_bits_nonneg[local]:
  ¬(int_of_bits bs < 0) ⇔ SND bs = F
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

Theorem int_and_nonneg[local]:
  ¬(i < 0) ∧ ¬(j < 0) ⇒ ¬(int_and i j < 0)
Proof
  rw [int_and_def, int_bitwise_def, bits_of_int_def, int_of_bits_nonneg]
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


(** multiword extensions ******************************************************)

(* TODO Move to HOL's multiword. *)

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

Definition mw2b_def:
  mw2b xs = bits_of_num (mw2n xs)
End

Theorem mw2b_empty[simp]:
  mw2b [] = []
Proof
  simp [mw2b_def, mw2n_def, Once bits_of_num_def]
QED

Theorem bits_of_num_w2n_append:
  bits_of_num (w2n x) ++ bits_of_num y =
  bits_of_num ((w2n x) + dimword (:α) * y)
Proof
  cheat
QED

Theorem mw2b_cons:
  mw2b (x::xs) = bits_of_num (w2n x) ++ mw2b xs
Proof
  simp [mw2b_def, mw2n_def, bits_of_num_w2n_append]
QED

Theorem EVERY_NOT_num_of_bits:
  ∀xs. EVERY (¬) xs ⇒ num_of_bits xs = 0
Proof
  Induct >> rw [num_of_bits_def]
QED

Theorem foo:
  ∀xs ys. mw2n (mw_and xs ys) = num_of_bits (FST (bits_bitwise (/\) (mw2b xs, F) (mw2b ys, F)))
Proof
  ho_match_mp_tac mw_and_ind >> rw [mw_and_def]
  >- cheat
  >> DEP_REWRITE_TAC [EVERY_NOT_num_of_bits] >> simp [EVERY_MAP, mw2n_def]
QED

Definition mwi_and_def:
  mwi_and (s, xs) (t, ys) =
  if ¬(s ∨ t) then (F, mw_and xs ys)
  else ARB
End

Theorem mwi_and_thm:
  ¬(i < 0) ∧ ¬(j < 0) ⇒ mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  rpt strip_tac
  >> simp [i2mw_def, mwi_and_def, Req0 int_and_nonneg, INT_ABS]
  >> simp [int_and_def, int_bitwise_def]
  >> qmatch_goalsub_abbrev_tac ‘int_of_bits bs’
  >> Cases_on ‘bs’ >> gvs [oneline int_of_bits_def, bits_of_int_def]
  >> drule_then assume_tac bits_bitwise_rest >> gvs []

  >> cheat
QED
