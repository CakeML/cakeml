(*
  Some word operations

  No specs
*)
open preamble;
open wordsTheory wordsLib;

val _ = new_theory "someWordOps";

Overload popcnt  = “λ (w:α word). n2w $ bit_count w”
Overload one_hot = “λ (w:α word). (popcnt w = 1w)”

Definition ctz_def: (* count trailing zeros *)
  ctz (w:α word) : β word = n2w (bit_count (w ⊕ (w-1w)) - 1)
End

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End

(* lend := little endian *)
Definition lend_def:
  lend (w:α word) : word8 list =

    let width        = dimindex(:α)                      in
    let need_1_more  = if 0 <> width MOD 8 then 1 else 0 in
    let bytes_needed = width DIV 8 + need_1_more         in

    MAP (λ n. w2w (w >>> (8*n))) $ COUNT_LIST bytes_needed

End

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


(*                vestigial                   *)


(* Definition list_to_def:
  list_to (0:num) : num list = [0] ∧
  list_to n = list_to (n-1) ++ [n]
End *)

(* val it =
   ⊢ (∀f. GENLIST f 0 = []) ∧
     ∀f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n): thm *)