(*
  Encoding and decoding
*)
open preamble;
open wasmLangTheory wordsTheory wordsLib;

val _ = new_theory "wasm_enc_dec";

(* --- basic LEB128 functions --- *)

Type byte[local]       = “:word8”
Type byteStream[local] = “:word8 list”

Overload        n128[local] = “(128:num)”
Overload     under7b[local] = “λ n. (n <   n128)”         (* : num -> bool    *)
Overload      last7b[local] = “λ n. (n MOD n128)”         (* : num -> num     *)
Overload sans_last7b[local] = “λ n. (n DIV n128)”         (* : num -> num     *)
Overload     not_MSB[local] = “word_msb”                  (* : α word -> bool *)
Overload      mk_lsB[local] = “λ n.128w + n2w (last7b n)” (* : num -> byte    *)
(*           under7b := is a num representable in 7 bits / is less than 128
              last7b := the last 7 bits of the binary rep of a num
         sans_last7b := binary rep of a num with last 7 bits truncated
             not_MSB := not the most sig Byte of a LEB128 encoded int
              mk_lsB := LEB128 encode 7 bits into a less significant (than the most) Byte
         *)



Definition read_num_def:
  read_num [] = NONE ∧
  read_num (b::rest) =
    if word_msb (b:word8) then
      case read_num rest of
      | NONE => NONE
      | SOME (n,left_over) => SOME (w2n b MOD 128 + 128 * n, left_over)
    else SOME (w2n b, rest)
End

Definition num_to_leb128_def:
  num_to_leb128 n =
    if n < 128 then [(n2w n):word8] else
      n2w (n MOD 128) + 128w :: num_to_leb128 (n DIV 128)
End

Theorem read_num_num_to_leb128:
  ∀n rest. read_num (num_to_leb128 n ++ rest) = SOME (n,rest)
Proof
  ho_match_mp_tac num_to_leb128_ind \\ rw []
  \\ simp [Once num_to_leb128_def] \\ rw []
  >-
   (simp [Once read_num_def]
    \\ ‘n DIV 128 = 0’ by gvs [DIV_EQ_X]
    \\ simp [word_msb_n2w,bitTheory.BIT_DEF])
  \\ simp [Once read_num_def,word_add_n2w]
  \\ simp [word_msb_n2w,bitTheory.BIT_DEF]
  \\ ‘0 < 128:num’ by fs []
  \\ drule ADD_DIV_ADD_DIV
  \\ disch_then $ qspecl_then [‘1’] assume_tac
  \\ gvs []
  \\ ‘(n MOD 128 + 128) < 256’ by
   (‘n MOD 128 < 128’ by simp [MOD_LESS]
    \\ decide_tac)
  \\ simp [LESS_MOD]
  \\ ‘0 < 128:num’ by fs []
  \\ drule DIVISION
  \\ disch_then (fn th => CONV_TAC (RAND_CONV $ ONCE_REWRITE_CONV [th]))
  \\ gvs []
QED

Definition read_w8_def:
  read_w8 input =
    case read_num input of
    | NONE => NONE
    | SOME (n,rest) => if n < 256 then SOME ((n2w n):word8, rest) else NONE
End

Definition read_w32_def:
  read_w32 input =
    case read_num input of
    | NONE => NONE
    | SOME (n,rest) => if n < 2**32 then SOME ((n2w n):word32, rest) else NONE
End

Definition write_w8_def:
  write_w8 (x:word8) acc = (num_to_leb128 (w2n x)) ++ acc
End

Definition write_w32_def:
  write_w32 (x:word32) acc = (num_to_leb128 (w2n x)) ++ acc
End

Theorem read_w8_thm[simp]:
  read_w8 (write_w8 x rest) = SOME (x,rest)
Proof
  simp [write_w8_def,read_w8_def,read_num_num_to_leb128]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED

Theorem read_w32_thm[simp]:
  read_w32 (write_w32 x rest) = SOME (x,rest)
Proof
  simp [write_w32_def,read_w32_def,read_num_num_to_leb128]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED

(* --- example --- *)

Definition encode_def:
  encode (b1,b2,b3) =
    write_w8 b1 (write_w8 b2 (write_w8 b3 []))
End

Definition decode_def:
  decode input =
    case read_w8 input of NONE => NONE | SOME (b1,input) =>
    case read_w8 input of NONE => NONE | SOME (b2,input) =>
    case read_w8 input of NONE => NONE | SOME (b3,input) =>
      if input = [] then SOME (b1,b2,b3) else NONE
End

Theorem decode_encode_thm:
  ∀x. decode (encode x) = SOME x
Proof
  PairCases
  \\ simp [encode_def,decode_def]
QED

val _ = export_theory();
