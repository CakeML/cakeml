(*
  TODO Extensions to multiword that should be upstreamed.
*)
Theory multiword_ext
Ancestors
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
  ∀f xs s ys t. SND (bits_bitwise f (xs, s) (ys, t)) = f s t
Proof
  recInduct bits_bitwise_ind >> rw [bits_bitwise_def]
  >> (pairarg_tac >> gvs [])
QED

Theorem int_and_nonneg[local]:
  ¬(i < 0) ∧ ¬(j < 0) ⇒ ¬(int_and i j < 0)
Proof
  rw [int_and_def, int_bitwise_def, bits_of_int_def, int_of_bits_nonneg,
      bits_bitwise_rest]
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

Definition mwi_and_def:
  mwi_and (s, xs) (t, ys) =
  if ¬(s ∨ t) then (F, mw_and xs ys)
  else ARB
End

Theorem mwi_and_thm:
  ¬(i < 0) ∧ ¬(j < 0) ⇒ mwi_and (i2mw i) (i2mw j) = i2mw (int_and i j)
Proof
  rw [i2mw_def, mwi_and_def, int_and_nonneg]
  >> cheat
QED
