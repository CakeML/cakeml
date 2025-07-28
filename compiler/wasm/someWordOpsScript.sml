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
  ctz (w:α word) : β word = n2w (bit_count (w ⊕ (w-1w)) - 1)
End

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End

Definition list_to_def:
  list_to (0:num) : num list = [0] ∧
  list_to n = list_to (n-1) ++ [n]
End

Definition lend_def:
  lend (w:α word) : word8 list = let width = dimindex(:α) in
    MAP (λ n. w2w (w >>> (8*n))) $ list_to $
      if 0 <> width MOD 8 then width + 1 else width
End

(* Definition lend_def:
  lend (w:α word) : (word8 list) option = let width = dimindex(:α) in
    if 0 <> width MOD 8 then NONE else SOME $
    MAP (λ n. w2w (w >>> (8*n))) $ list_to width
End *)

Definition unlend_def:
  unlend (0:num) (res:word8 list) (bs:word8 list) = SOME (concat_word_list res, bs) ∧
  unlend n acc (b::bs) = unlend (n-1) (b::acc) bs ∧
  unlend _ _ [] = NONE
End

Overload unlend32  = “unlend 4  []”
Overload unlend128 = “unlend 16 []”

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