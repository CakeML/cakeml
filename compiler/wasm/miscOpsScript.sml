(*
  Some extra operations
  No specs yet
*)

open preamble;
open wordsTheory wordsLib;
open byteTheory;

val _ = new_theory "miscOps";

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”


Overload popcnt  = “λ (w:α word). n2w $ bit_count w”
Overload one_hot = “λ (w:α word). (popcnt w = 1w)”

Definition ctz_def: (* count trailing zeros *)
  ctz (w:α word) : β word = n2w (bit_count (w ⊕ (w-1w)) - 1)
End

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End

(* this is lend *)
(* print_match [] ``word_to_bytes`` *)


(* REPLACE MMYK say there are library versions of lend and unlend *)
(* lend := little endian *)
(* Overload lend = “word_to_bytes”*)
Definition lend_def:
  lend (w:α word) : byteSeq =
    word_to_bytes w F
End

Definition unlend_def:
  unlend (bs:byteSeq) =
    let n = dimindex(:α) DIV 8 in
    if LENGTH bs < n then NONE else
      let xs = TAKE n bs in
      let ys = DROP n bs in
(* F selects little endian mode *)
      SOME (word_of_bytes F (0w:α word) xs, ys)
End


Theorem unlend_lend32[simp]:
  unlend (lend (w:word32) ++ rest) = SOME (w, rest)
Proof
  simp[lend_def, unlend_def] >>
  (* this is how you do asserts *)
  `4 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes] >>
  (* asm_rw additionally uses the assumptions to rewrite *)
  asm_rewrite_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  rw[word_to_bytes_word_of_bytes_32]
QED

(* print_match [] ``TAKE (LENGTH xs) (xs ++ ys)`` *)

Theorem unlend_lend64[simp]:
  unlend (lend (w:word64) ++ rest) = SOME (w, rest)
Proof
  simp[lend_def, unlend_def] >>
  `8 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes] >>
  asm_rewrite_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  rw[word_to_bytes_word_of_bytes_64]
QED

(*
Theorem unlend_lend128[simp]:
  unlend (lend (w:word128) ++ rest) = SOME (w, rest)
Proof
  simp[lend_def, unlend_def] >>
  `16 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes] >>
  asm_rewrite_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND] >>
  rw[word_to_bytes_word_of_bytes_128]
QED
*)

(*
Overload unlend32  = “unlend  4 []”
Overload unlend64  = “unlend  8 []”
Overload unlend128 = “unlend 16 []”
*)

(* REPLACE ASKMM *)
Definition take_def:
  take (n:num) (xs: α list) : (α list # bool) = (TAKE n xs, n <= LENGTH xs)
End

Definition load_def:
  load (n:num) (offs:α word) (algn:β word) (bs:byteSeq) : (γ word # bool) =
    let ofs = w2n offs in
    let alg = w2n algn in
    let bs' = DROP (ofs * alg) bs in
    case unlend bs' of
    | NONE       => (0w,F)
    | SOME (v,_) => (v ,T)
End

Definition store_def:
  store (x:α word) (offs:β word) (algn:γ word) (bs:byteSeq) : (byteSeq # bool) =
    let oa = (w2n offs) * (w2n algn) in
    let n = dimindex(:α) DIV 8 in
    (TAKE oa bs ⧺ lend x ⧺ DROP (oa + n) bs, oa + n <= LENGTH bs)
End

(* print_match [] "word_to_bytes" *)

Theorem clz_spec:
  ∀ n. (dimindex(:α) - n) < w2n (ctz (w:α word)) ⇒ w ' n = F
Proof
  cheat
QED

Theorem lend128_spec:
  ∀ w. w = concat_word_list $ REVERSE $ lend128 w
Proof
  cheat
QED


Theorem ctz_spec1:
  ∀ n. n < w2n (ctz w) ⇒ ¬ w ' n
Proof
  (* I kind of don't know where to start here... *)
  (* clearly the "real" coal face is all the way
     inside ctz_def, starting at "w-1w"

     I want some way to be able to capture how
     w-1w is different from w. Or rather
     To characterize "w ⊕ (w-1w)".
  *)
  (* Most of all, such a proof won't proceed
     "structurally" cos I don't think words
     _are_ defined structurally. (MM said this too I think)

     so we would want to appeal to thms about the
     existing word ops that we do already use
     (MM: ditto)
  *)
  cheat
QED

Theorem ctz_spec2:
  ∀ w. 0w <+ w >> w2n (ctz w)
Proof
  (* cf ctz_spec1... *)
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
