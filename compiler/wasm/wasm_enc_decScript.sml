(*
  Encoding and decoding between Cake-Wasm AST & Wasm binary format
*)
(* Currently only handling positive numbers *)
open preamble;
open wasmLangTheory wordsTheory wordsLib;

(*  TODOs
    - unsigned LEB
    - finish up numeric instructions
    - more of the AST
    - parser for the decoder
    - right now LEB decoding takes a detour through HOL nums;
      would a better route be straight to words?
 *)

val _ = new_theory "wasm_enc_dec";

(* --- basic leb functions --- *)

Type byte[local]       = “:word8”
Type byteStream[local] = “:word8 list”

(*******************)
(*                 *)
(*     LEB128      *)
(*                 *)
(*******************)

  (***************)
  (*   Helpers   *)
  (***************)
  (* for maintaining an leb abstraction *)
Overload        n128[local] = “(128:num)”
Overload     under7b[local] = “λ n. (n <   n128)”         (* : num -> bool    *)
Overload      last7b[local] = “λ n. (n MOD n128)”         (* : num -> num     *)
Overload sans_last7b[local] = “λ n. (n DIV n128)”         (* : num -> num     *)
Overload     not_MSB[local] = “word_msb”                  (* : α word -> bool *)
Overload      mk_lsB[local] = “λ n.128w + n2w (last7b n)” (* : num -> byte    *)
Overload  leb_append[local] = “λ pre post. pre * n128 + last7b post”
(*  under7b := is a num representable in 7 bits
     last7b := the last 7 bits of the binary rep of a num
sans_last7b := num with last 7 bits of its binary rep truncated
    not_MSB := not the most sig Byte of a leb encoded int
     mk_lsB := leb encode 7 bits into a less significant (than the most) Byte
 leb_append := "append" a less-sig byte (post) to the end
                of under-construction number (pre) *)

(* Magnus orig code *)
  (* Definition read_num_def:
    read_num [] = NONE ∧
    read_num (b::rest) =
      if word_msb (b:word8) then
        case read_num rest of
        | NONE => NONE
        | SOME (n,left_over) => SOME (w2n b MOD 128 + 128 * n, left_over)
      else SOME (w2n b, rest)
  End

  Definition encode_num_def:
    encode_num n =
      if n < 128 then [(n2w n):word8] else
        n2w (n MOD 128) + 128w :: encode_num (n DIV 128)
  End

  Theorem read_num_encode_num:
    ∀n rest. read_num (encode_num n ++ rest) = SOME (n,rest)
  Proof
    ho_match_mp_tac encode_num_ind \\ rw []
    \\ simp [Once encode_num_def] \\ rw []
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
  QED *)
(* End Magnus orig code *)

(* uleb decode a HOL num from a byte stream *)
Definition decode_num_def:
  decode_num ([]:byteStream) : (num # byteStream) option = NONE ∧
  decode_num (b::rest) =
    let bn = w2n b in
    if not_MSB b then
      case decode_num rest of
      | SOME (n, left_over) => SOME (leb_append n bn, left_over)
      | NONE => NONE
    else SOME (bn, rest)
End

(* uleb encode a (+ve) HOL num to bytes *)
Definition encode_num_def:
  encode_num (n:num) : byteStream =
    if n < 128 then [n2w n]
    else n2w (n MOD 128) + 128w :: encode_num (n DIV 128)
End

(* TODO : Documentation *)
Theorem dec_enc_num_id:
  ∀n rest. decode_num (encode_num n ++ rest) = SOME (n,rest)
Proof
  ho_match_mp_tac encode_num_ind \\ rw []
  \\ simp [Once encode_num_def] \\ rw []
  >-
   (simp [Once decode_num_def]
    \\ ‘n DIV 128 = 0’ by gvs [DIV_EQ_X]
    \\ simp [word_msb_n2w,bitTheory.BIT_DEF])
  \\ simp [Once decode_num_def,word_add_n2w]
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

(* read (unencoded) word out of uleb stream; "polymorphic" *)
Definition read_u_word_def:
  read_u_word (input:byteStream) = case decode_num input of
  | SOME (n,rest) => if n < dimword(:α) then SOME ((n2w n):α word, rest) else NONE
  | NONE => NONE
End

Definition write_u_word_def:
  write_u_word (x:(α word)) (acc:byteStream) : byteStream = (encode_num (w2n x)) ++ acc
End

Overload read_u_B   = “read_u_word : byteStream -> (byte    # byteStream) option”
Overload read_u_4B  = “read_u_word : byteStream -> (word32  # byteStream) option”
Overload read_u_8B  = “read_u_word : byteStream -> (word64  # byteStream) option”
Overload read_u_16B = “read_u_word : byteStream -> (word128 # byteStream) option”

(* TODO: implement signed leb *)
Overload read_s_B   = “read_u_B  ”
Overload read_s_4B  = “read_u_4B ”
Overload read_s_8B  = “read_u_8B ”
Overload read_s_16B = “read_u_16B”

(* TODO: floats *)
Overload read_f_B   = “read_u_B  ”
Overload read_f_4B  = “read_u_4B ”
Overload read_f_8B  = “read_u_8B ”
Overload read_f_16B = “read_u_16B”

Overload write_u_B   = “write_u_word : byte    -> byteStream -> byteStream”
Overload write_u_4B  = “write_u_word : word32  -> byteStream -> byteStream”
Overload write_u_8B  = “write_u_word : word64  -> byteStream -> byteStream”
Overload write_u_16B = “write_u_word : word128 -> byteStream -> byteStream”

Theorem read_write_u_B[simp]:
  read_u_B (write_u_B x rest) = SOME (x, rest)
Proof
  simp [read_u_word_def,dec_enc_num_id,write_u_word_def]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED

Theorem read_write_u_4B[simp]:
  read_u_4B (write_u_4B x rest) = SOME (x, rest)
Proof
  simp [read_u_word_def,dec_enc_num_id,write_u_word_def]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED

Theorem read_write_u_8B[simp]:
  read_u_8B (write_u_8B x rest) = SOME (x, rest)
Proof
  simp [read_u_word_def,dec_enc_num_id,write_u_word_def]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED

Theorem read_write_u_16B[simp]:
  read_u_16B (write_u_16B x rest) = SOME (x, rest)
Proof
  simp [read_u_word_def,dec_enc_num_id,write_u_word_def]
  \\ irule LESS_LESS_EQ_TRANS
  \\ irule_at Any w2n_lt \\ simp []
QED


(* --- example --- *)

Definition encode_def:
  encode (b1,b2,b3) =
    write_u_B b1 (write_u_B b2 (write_u_B b3 []))
End

Definition decode_def:
  decode input =
    case read_u_B input of NONE => NONE | SOME (b1,input) =>
    case read_u_B input of NONE => NONE | SOME (b2,input) =>
    case read_u_B input of NONE => NONE | SOME (b3,input) =>
      if input = [] then SOME (b1,b2,b3) else NONE
End

Theorem decode_encode_thm:
  ∀x. decode (encode x) = SOME x
Proof
  PairCases
  \\ simp [encode_def,decode_def]
QED

(* --- example --- *)



(***********************************************)
(*                                             *)
(*     Wasm Binary Format ⇔ WasmCake AST      *)
(*                                             *)
(***********************************************)

  (***************)
  (*   Helpers   *)
  (***************)

Overload selWidth = “λbool. if bool then W64      else W32”
Overload selSign  = “λbool. if bool then Unsigned else Signed”



  (****************)
  (*   Numtypes   *)
  (****************)

Definition decode_numtype_def:
  decode_numtype (b:byte) : numtype option =
  (* QQ Why not case? MM: this is better. Explanation elided for now *)
  if b = 0x7Fw then SOME (NT Int   W32) else
  if b = 0x7Ew then SOME (NT Int   W64) else
  if b = 0x7Dw then SOME (NT Float W32) else
  if b = 0x7Cw then SOME (NT Float W64) else NONE
End

Definition encode_numtype_def:
  encode_numtype (t:numtype) : byte = case t of
  | (NT Int   W32) => 0x7Fw
  | (NT Int   W64) => 0x7Ew
  | (NT Float W32) => 0x7Dw
  | (NT Float W64) => 0x7Cw
End

Theorem dec_enc_numtype[simp]:
  ∀ t. decode_numtype (encode_numtype t) = SOME t
Proof
  Cases >> Cases_on `b` >> Cases_on `w` >>
  simp[decode_numtype_def, encode_numtype_def]
QED

(* TODO *)
(* Theorem enc_dec_numtype:
  ∀ b t. decode_numtype b = Some t ⇒ (encode_numtype t) = b
Proof
  Cases_on `t` >> Cases_on `b` >> Cases_on `w` >>
  Cases_on `n`

  simp[decode_numtype_def, encode_numtype_def]
QED *)

  (****************************)
  (*   Numeric Instructions   *)
  (****************************)

(* decode a numeric instruction from a stream of bytes. *)
(*  NB: numeric instructions are variable length as some take numbers as part of their encoding
    eg constant functions *)
Definition decode_numI_def:
  decode_numI ([]:byteStream) : (num_instr option # byteStream) = (NONE, []) ∧
  decode_numI (b::bs) = let default = (NONE,b::bs) in

  if b = 0x45w then (SOME   (N_test       (Eqz W32)                    ), bs) else
  if b = 0x46w then (SOME   (N_compare    (Eq Int W32)                 ), bs) else
  if b = 0x47w then (SOME   (N_compare    (Ne Int W32)                 ), bs) else
  if b = 0x48w then (SOME   (N_compare    (Lt_   Signed W32)           ), bs) else
  if b = 0x49w then (SOME   (N_compare    (Lt_ Unsigned W32)           ), bs) else
  if b = 0x4Aw then (SOME   (N_compare    (Gt_   Signed W32)           ), bs) else
  if b = 0x4Bw then (SOME   (N_compare    (Gt_ Unsigned W32)           ), bs) else
  if b = 0x4Cw then (SOME   (N_compare    (Le_   Signed W32)           ), bs) else
  if b = 0x4Dw then (SOME   (N_compare    (Le_ Unsigned W32)           ), bs) else
  if b = 0x4Ew then (SOME   (N_compare    (Ge_   Signed W32)           ), bs) else
  if b = 0x4Fw then (SOME   (N_compare    (Ge_ Unsigned W32)           ), bs) else
  if b = 0x50w then (SOME   (N_test       (Eqz W64)                    ), bs) else
  if b = 0x51w then (SOME   (N_compare    (Eq Int W64)                 ), bs) else
  if b = 0x52w then (SOME   (N_compare    (Ne Int W64)                 ), bs) else
  if b = 0x53w then (SOME   (N_compare    (Lt_   Signed W64)           ), bs) else
  if b = 0x54w then (SOME   (N_compare    (Lt_ Unsigned W64)           ), bs) else
  if b = 0x55w then (SOME   (N_compare    (Gt_   Signed W64)           ), bs) else
  if b = 0x56w then (SOME   (N_compare    (Gt_ Unsigned W64)           ), bs) else
  if b = 0x57w then (SOME   (N_compare    (Le_   Signed W64)           ), bs) else
  if b = 0x58w then (SOME   (N_compare    (Le_ Unsigned W64)           ), bs) else
  if b = 0x59w then (SOME   (N_compare    (Ge_   Signed W64)           ), bs) else
  if b = 0x5Aw then (SOME   (N_compare    (Ge_ Unsigned W64)           ), bs) else
  if b = 0x5Bw then (SOME   (N_compare    (Eq Float W32)               ), bs) else
  if b = 0x5Cw then (SOME   (N_compare    (Ne Float W32)               ), bs) else
  if b = 0x5Dw then (SOME   (N_compare    (Lt W32)                     ), bs) else
  if b = 0x5Ew then (SOME   (N_compare    (Gt W32)                     ), bs) else
  if b = 0x5Fw then (SOME   (N_compare    (Le W32)                     ), bs) else
  if b = 0x60w then (SOME   (N_compare    (Ge W32)                     ), bs) else
  if b = 0x61w then (SOME   (N_compare    (Eq Float W64)               ), bs) else
  if b = 0x62w then (SOME   (N_compare    (Ne Float W64)               ), bs) else
  if b = 0x63w then (SOME   (N_compare    (Lt W64)                     ), bs) else
  if b = 0x64w then (SOME   (N_compare    (Gt W64)                     ), bs) else
  if b = 0x65w then (SOME   (N_compare    (Le W64)                     ), bs) else
  if b = 0x66w then (SOME   (N_compare    (Ge W64)                     ), bs) else
  if b = 0x67w then (SOME   (N_unary      (Clz    W32)                 ), bs) else
  if b = 0x68w then (SOME   (N_unary      (Ctz    W32)                 ), bs) else
  if b = 0x69w then (SOME   (N_unary      (Popcnt W32)                 ), bs) else
  if b = 0x6Aw then (SOME   (N_binary     (Add Int W32)                ), bs) else
  if b = 0x6Bw then (SOME   (N_binary     (Sub Int W32)                ), bs) else
  if b = 0x6Cw then (SOME   (N_binary     (Mul Int W32)                ), bs) else
  if b = 0x6Dw then (SOME   (N_binary     (Div_   Signed W32)          ), bs) else
  if b = 0x6Ew then (SOME   (N_binary     (Div_ Unsigned W32)          ), bs) else
  if b = 0x6Fw then (SOME   (N_binary     (Rem_   Signed W32)          ), bs) else
  if b = 0x70w then (SOME   (N_binary     (Rem_ Unsigned W32)          ), bs) else
  if b = 0x71w then (SOME   (N_binary     (And W32)                    ), bs) else
  if b = 0x72w then (SOME   (N_binary     (Or W32)                     ), bs) else
  if b = 0x73w then (SOME   (N_binary     (Xor W32)                    ), bs) else
  if b = 0x74w then (SOME   (N_binary     (Shl W32)                    ), bs) else
  if b = 0x75w then (SOME   (N_binary     (Shr_   Signed W32)          ), bs) else
  if b = 0x76w then (SOME   (N_binary     (Shr_ Unsigned W32)          ), bs) else
  if b = 0x77w then (SOME   (N_binary     (Rotl W32)                   ), bs) else
  if b = 0x78w then (SOME   (N_binary     (Rotr W32)                   ), bs) else
  if b = 0x79w then (SOME   (N_unary      (Clz    W64)                 ), bs) else
  if b = 0x7Aw then (SOME   (N_unary      (Ctz    W64)                 ), bs) else
  if b = 0x7Bw then (SOME   (N_unary      (Popcnt W64)                 ), bs) else
  if b = 0x7Cw then (SOME   (N_binary     (Add Int W64)                ), bs) else
  if b = 0x7Dw then (SOME   (N_binary     (Sub Int W64)                ), bs) else
  if b = 0x7Ew then (SOME   (N_binary     (Mul Int W64)                ), bs) else
  if b = 0x7Fw then (SOME   (N_binary     (Div_   Signed W64)          ), bs) else
  if b = 0x80w then (SOME   (N_binary     (Div_ Unsigned W64)          ), bs) else
  if b = 0x81w then (SOME   (N_binary     (Rem_   Signed W64)          ), bs) else
  if b = 0x82w then (SOME   (N_binary     (Rem_ Unsigned W64)          ), bs) else
  if b = 0x83w then (SOME   (N_binary     (And W64)                    ), bs) else
  if b = 0x84w then (SOME   (N_binary     (Or  W64)                    ), bs) else
  if b = 0x85w then (SOME   (N_binary     (Xor W64)                    ), bs) else
  if b = 0x86w then (SOME   (N_binary     (Shl W64)                    ), bs) else
  if b = 0x87w then (SOME   (N_binary     (Shr_   Signed W64)          ), bs) else
  if b = 0x88w then (SOME   (N_binary     (Shr_ Unsigned W64)          ), bs) else
  if b = 0x89w then (SOME   (N_binary     (Rotl W64)                   ), bs) else
  if b = 0x8Aw then (SOME   (N_binary     (Rotr W64)                   ), bs) else
  if b = 0x8Bw then (SOME   (N_unary      (Abs     W32)                ), bs) else
  if b = 0x8Cw then (SOME   (N_unary      (Neg     W32)                ), bs) else
  if b = 0x8Dw then (SOME   (N_unary      (Ceil    W32)                ), bs) else
  if b = 0x8Ew then (SOME   (N_unary      (Floor   W32)                ), bs) else
  if b = 0x8Fw then (SOME   (N_unary      (Trunc   W32)                ), bs) else
  if b = 0x90w then (SOME   (N_unary      (Nearest W32)                ), bs) else
  if b = 0x91w then (SOME   (N_unary      (Sqrt    W32)                ), bs) else
  if b = 0x92w then (SOME   (N_binary     (Add Float W32)              ), bs) else
  if b = 0x93w then (SOME   (N_binary     (Sub Float W32)              ), bs) else
  if b = 0x94w then (SOME   (N_binary     (Mul Float W32)              ), bs) else
  if b = 0x95w then (SOME   (N_binary     (Div W32)                    ), bs) else
  if b = 0x96w then (SOME   (N_binary     (Min W32)                    ), bs) else
  if b = 0x97w then (SOME   (N_binary     (Max W32)                    ), bs) else
  if b = 0x98w then (SOME   (N_binary     (Copysign W32)               ), bs) else
  if b = 0x99w then (SOME   (N_unary      (Abs     W64)                ), bs) else
  if b = 0x9Aw then (SOME   (N_unary      (Neg     W64)                ), bs) else
  if b = 0x9Bw then (SOME   (N_unary      (Ceil    W64)                ), bs) else
  if b = 0x9Cw then (SOME   (N_unary      (Floor   W64)                ), bs) else
  if b = 0x9Dw then (SOME   (N_unary      (Trunc   W64)                ), bs) else
  if b = 0x9Ew then (SOME   (N_unary      (Nearest W64)                ), bs) else
  if b = 0x9Fw then (SOME   (N_unary      (Sqrt    W64)                ), bs) else
  if b = 0xA0w then (SOME   (N_binary     (Add Float W64)              ), bs) else
  if b = 0xA1w then (SOME   (N_binary     (Sub Float W64)              ), bs) else
  if b = 0xA2w then (SOME   (N_binary     (Mul Float W64)              ), bs) else
  if b = 0xA3w then (SOME   (N_binary     (Div W64)                    ), bs) else
  if b = 0xA4w then (SOME   (N_binary     (Min W64)                    ), bs) else
  if b = 0xA5w then (SOME   (N_binary     (Max W64)                    ), bs) else
  if b = 0xA6w then (SOME   (N_binary     (Copysign W64)               ), bs) else
  if b = 0xA7w then (SOME   (N_convert     Wrap_i64                    ), bs) else
  if b = 0xA8w then (SOME   (N_convert    (Trunc_f W32   Signed W32)   ), bs) else
  if b = 0xA9w then (SOME   (N_convert    (Trunc_f W32 Unsigned W32)   ), bs) else
  if b = 0xAAw then (SOME   (N_convert    (Trunc_f W64   Signed W32)   ), bs) else
  if b = 0xABw then (SOME   (N_convert    (Trunc_f W64 Unsigned W32)   ), bs) else
  if b = 0xACw then (SOME   (N_unary      (Extend_i32_   Signed)       ), bs) else
  if b = 0xADw then (SOME   (N_unary      (Extend_i32_ Unsigned)       ), bs) else
  if b = 0xAEw then (SOME   (N_convert    (Trunc_f W32   Signed W64)   ), bs) else
  if b = 0xAFw then (SOME   (N_convert    (Trunc_f W32 Unsigned W64)   ), bs) else
  if b = 0xB0w then (SOME   (N_convert    (Trunc_f W64   Signed W64)   ), bs) else
  if b = 0xB1w then (SOME   (N_convert    (Trunc_f W64 Unsigned W64)   ), bs) else
  if b = 0xB2w then (SOME   (N_convert    (Convert W32   Signed W32)   ), bs) else
  if b = 0xB3w then (SOME   (N_convert    (Convert W32 Unsigned W32)   ), bs) else
  if b = 0xB4w then (SOME   (N_convert    (Convert W64   Signed W32)   ), bs) else
  if b = 0xB5w then (SOME   (N_convert    (Convert W64 Unsigned W32)   ), bs) else
  if b = 0xB6w then (SOME   (N_convert     Demote                      ), bs) else
  if b = 0xB7w then (SOME   (N_convert    (Convert W32   Signed W64)   ), bs) else
  if b = 0xB8w then (SOME   (N_convert    (Convert W32 Unsigned W64)   ), bs) else
  if b = 0xB9w then (SOME   (N_convert    (Convert W64   Signed W64)   ), bs) else
  if b = 0xBAw then (SOME   (N_convert    (Convert W64 Unsigned W64)   ), bs) else
  if b = 0xBBw then (SOME   (N_convert     Promote                     ), bs) else
  if b = 0xBCw then (SOME   (N_convert    (Reinterpret_f W32)          ), bs) else
  if b = 0xBDw then (SOME   (N_convert    (Reinterpret_f W64)          ), bs) else
  if b = 0xBEw then (SOME   (N_convert    (Reinterpret_i W32)          ), bs) else
  if b = 0xBFw then (SOME   (N_convert    (Reinterpret_i W64)          ), bs) else
  if b = 0xC0w then (SOME   (N_unary      (Extend8_s  W32)             ), bs) else
  if b = 0xC1w then (SOME   (N_unary      (Extend16_s W32)             ), bs) else
  if b = 0xC2w then (SOME   (N_unary      (Extend8_s  W64)             ), bs) else
  if b = 0xC3w then (SOME   (N_unary      (Extend16_s W64)             ), bs) else
  if b = 0xC4w then (SOME   (N_unary       Extend32_s                  ), bs) else

  (************************************)
  (*   Variable length instructions   *)
  (************************************)
  (* eg, because the encoding contains a const *)

  (* TODO: BOGUS until read_s and read_f properly implemented *)
  (* Constant instructions *)
  if b = 0x41w then   case read_s_4B bs of
  | SOME (c32,rest) => (SOME (N_const32 Int   c32), rest)
  | NONE            => default                                                else
  if b = 0x42w then   case read_s_8B bs of
  | SOME (c64,rest) => (SOME (N_const64 Int   c64), rest)
  | NONE            => default                                                else
  if b = 0x43w then   case read_f_4B bs of
  | SOME (c32,rest) => (SOME (N_const32 Float c32), rest)
  | NONE            => default                                                else
  if b = 0x44w then case read_f_8B bs of SOME (c64,rest) => (SOME (N_const64 Float c64), rest)
  | NONE            => default                                                else

  (* trunc_sat_f. Forwhatever reason is coded as 2 bytes, instead of  *)
  if b = 0xFCw then case read_u_4B bs of
  | SOME (sel,rest) =>  (SOME (N_convert (Trunc_sat_f
                          (selWidth $ sel ' 1)
                          (selSign  $ sel ' 2)
                          (selWidth $ sel ' 0)
                        )) , rest)
  | NONE            => default                                                else

  default
End


(*



  (* Curiosity (ie, not technically impt): why is the encoding not contiguous??? *)
  if b = 0xFCw then case read_4B bs of
    | SOME (sel, rest) => (SOME (N_convert (Trunc_sat_f
                            (selWidth $ sel ' 1)
                            (selSign $ sel ' 2)
                            (selWidth $ sel ' 0)
                          )) , rest)
    | NONE => (NONE,b::bs)                                                    else (NONE, bs)
  (* 0:u32 ⇒ (Trunc_sat_f W32   Signed W32)
  1:u32 ⇒ (Trunc_sat_f W32 Unsigned W32)
  2:u32 ⇒ (Trunc_sat_f W64   Signed W32)
  3:u32 ⇒ (Trunc_sat_f W64 Unsigned W32)
  4:u32 ⇒ (Trunc_sat_f W32   Signed W64)
  5:u32 ⇒ (Trunc_sat_f W32 Unsigned W64)
  6:u32 ⇒ (Trunc_sat_f W64   Signed W64)
  7:u32 ⇒ (Trunc_sat_f W64 Unsigned W64) *) *)

val _ = export_theory();
