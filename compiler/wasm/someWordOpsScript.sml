(*
  Some word operations

  No specs
*)
open preamble;
open wordsTheory;
open wordsLib;

val _ = new_theory "someWordOps";

(* Definition popcnt_def[simp]:
  popcnt (w:α word) : β word = n2w $ bit_count w
End *)

Overload popcnt = “λ (w:α word). n2w $ bit_count w”

(* Triviality popcnt_unit_tests:
  pop_count (0x1w:word8) : word32 = 1w ∧
  pop_count (0x3w:word8) : word32 = 2w ∧
  pop_count (0x7w:word8) : word32 = 3w ∧
  pop_count (0xfw:word8) : word32 = 4w
  (* pocnt (0x1w:word8) = (1w:word32) *)
  (* pocnt (0x3w:word8) = (2w:word32) *)
Proof
  rw[popcnt_def] >> EVAL_TAC
  (* EVAL_TAC *)
QED *)

(* Definition one_hot_def:
  one_hot w = (popcnt w = 1)
End *)

Overload one_hot = “λ (w:α word). (popcnt w = 1w)”

Definition ctz_def: (* count trailing zeros *)
  ctz (w:α word) : β word = popcnt $ w ⊕ (w && (w-1w))
End

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End

Definition lend128_def:
  lend128 (w:128 word) : word8 list  =
    MAP (λ (n:num). w2w (w >>> (8*n))) [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
End

Definition unlend128_def:
  unlend128 (b0::b1::b3::b4::b5::b6::b7::b8::b9::bA::bB::bC::bD::bE::bF::rest) =
  SOME (concat_word_list [bF; bE; bD; bC; bB; bA; b9; b8; b7; b6; b5; b4; b3; b1; b0],rest)
  ∧ unlend128 _ = NONE
End


Theorem ctz_spec:
  ∀ n. n < w2n (ctz w) ⇒ w ' n = F
Proof
  cheat
QED

Theorem clz_spec:
  ∀ n. (dimword(:α) - n) < w2n (ctz (w:α word)) ⇒ w ' n = F
Proof
  cheat
QED


Theorem lend128_spec:
  ∀ w. w = concat_word_list $ REVERSE $ lend128 w
Proof
  cheat
QED

val _ = export_theory();