(*
  Some extra operations
  No specs yet
*)
open preamble;
open wordsTheory wordsLib;

val _ = new_theory "miscOps";

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”


Overload popcnt  = “λ (w:α word). n2w $ bit_count w”
Overload one_hot = “λ (w:α word). (popcnt w = 1w)”

Definition ctz_def: (* count trailing zeros *)
  ctz (w:α word) : β word = n2w (bit_count (w ⊕ (w-1w)) - 1)
End

Theorem ctz_spec1:
  ∀ n. n < w2n (ctz w) ⇒ w ' n = F
Proof
  (* Induct_on ‘n’
  rw[ctz_def]
  Cases_on ‘w’  *)
  cheat
QED

Theorem ctz_spec2:
  w >> w2n (ctz w) <> 0x00w
Proof
  cheat
QED

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End

(* lend := little endian *)
Definition lend_def:
  lend (w:α word) : byteSeq =

    let width        = dimindex(:α)                      in
    let need_1_more  = if 0 <> width MOD 8 then 1 else 0 in
    let bytes_needed = width DIV 8 + need_1_more         in

    MAP (λ n. w2w (w >>> (8*n))) $ COUNT_LIST bytes_needed

End

Definition unlend_def:
  unlend (0:num) (res:byteSeq) (bs:byteSeq) = SOME (concat_word_list res, bs) ∧
  unlend n acc (b::bs) = unlend (n-1) (b::acc) bs ∧
  unlend _ _ [] = NONE
End

Overload unlend32  = “unlend 4  []”
Overload unlend128 = “unlend 16 []”

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

Definition take_def:
  take (n:num) (xs: α list) : (α list # bool) = (TAKE n xs, n <= LENGTH xs)
End

Definition load_def:
  load (n:num) (offs:α word) (algn:β word) (bs:byteSeq) : (γ word # bool) =
    let ofs = w2n offs in
    let alg = w2n algn in
    let bs' = DROP (ofs * alg) bs in
    case unlend n [] bs' of
    | NONE       => (0w,F)
    | SOME (v,_) => (v ,T)
End

Definition store_def:
  store (x:α word) (offs:β word) (algn:γ word) (bs:byteSeq) : (byteSeq # bool) =
    let oa = (w2n offs) * (w2n algn) in
    let n = dimindex(:α) DIV 8 in
    (TAKE oa bs ⧺ lend x ⧺ DROP (oa + n) bs, oa + n <= LENGTH bs)
End

val _ = export_theory();


(*                vestigial                   *)


(* Definition list_to_def:
  list_to (0:num) : num list = [0] ∧
  list_to n = list_to (n-1) ++ [n]
End *)

(* val it =
   ⊢ (∀f. GENLIST f 0 = []) ∧
     ∀f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n): thm *)