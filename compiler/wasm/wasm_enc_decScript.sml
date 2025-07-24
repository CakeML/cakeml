(*
  Encoding and decoding between Cake-Wasm AST & Wasm binary format
*)
(* Currently only handling positive numbers *)
open preamble;
open wasmLangTheory wordsTheory wordsLib;

(*  TODOs
    - unsigned LEB
    - monad notation, dear god
    - encode numeric instructions
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

(* TODO: implement signed leb *)
Overload write_s_B   = “write_u_B  ”
Overload write_s_4B  = “write_u_4B ”
Overload write_s_8B  = “write_u_8B ”
Overload write_s_16B = “write_u_16B”

(* TODO: floats *)
Overload write_f_B   = “write_u_B  ”
Overload write_f_4B  = “write_u_4B ”
Overload write_f_8B  = “write_u_8B ”
Overload write_f_16B = “write_u_16B”

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


(* Magnus orig code *)
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
(* End Magnus orig code *)



(***********************************************)
(*                                             *)
(*     Wasm Binary Format ⇔ WasmCake AST      *)
(*                                             *)
(***********************************************)

  (***************)
  (*   Helpers   *)
  (***************)

Overload selWidth = “λ(b:bool). if b then W64      else W32”
Overload selSign  = “λ(b:bool). if b then Unsigned else Signed”

  (********************)
  (*   Number types   *)
  (********************)

Definition encode_numtype_def:
  encode_numtype (t:numtype) : byte = case t of
  | (NT Int   W32) => 0x7Fw
  | (NT Int   W64) => 0x7Ew
  | (NT Float W32) => 0x7Dw
  | (NT Float W64) => 0x7Cw
End

Definition decode_numtype_def:
  decode_numtype (b:byte) : numtype option =
  (* QQ Why not case? MM: this is better. Explanation elided for now *)
  if b = 0x7Fw then SOME (NT Int   W32) else
  if b = 0x7Ew then SOME (NT Int   W64) else
  if b = 0x7Dw then SOME (NT Float W32) else
  if b = 0x7Cw then SOME (NT Float W64) else NONE
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

  (*******************)
  (*   Value types   *)
  (*******************)

Datatype: valtype
  = Tnum numtype
  | Tvec
  | TFunRef
  | TExtRef
End

Definition encode_valtype_def:
  encode_valtype (t:valtype) : byte = case t of
  | Tnum (NT Int   W32) => 0x7Fw
  | Tnum (NT Int   W64) => 0x7Ew
  | Tnum (NT Float W32) => 0x7Dw
  | Tnum (NT Float W64) => 0x7Cw
  | Tvec                => 0x7Bw
  | TFunRef             => 0x70w
  | TExtRef             => 0x6Fw
End

Definition decode_valtype_def:
  decode_valtype (b:byte) : valtype option =
  if b = 0x7Fw then SOME (Tnum (NT Int   W32)) else
  if b = 0x7Ew then SOME (Tnum (NT Int   W64)) else
  if b = 0x7Dw then SOME (Tnum (NT Float W32)) else
  if b = 0x7Cw then SOME (Tnum (NT Float W64)) else
  if b = 0x7Bw then SOME (Tvec               ) else
  if b = 0x70w then SOME (TFunRef            ) else
  if b = 0x6Fw then SOME (TExtRef            ) else NONE
End

Theorem dec_enc_valtype[simp]:
  ∀ t. decode_valtype (encode_valtype t) = SOME t
Proof
  cheat
  (* Cases >>
  simp[decode_valtype_def, encode_valtype_def] *)
QED



  (****************************)
  (*   Numeric Instructions   *)
  (****************************)
  (*  NB: numeric instructions are variable length as some take numbers as part of their encoding
      eg constant functions *)

(* decode a numeric instruction from a stream of bytes. *)
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
  if b = 0x41w then case read_s_4B bs of SOME (c32,rest) => (SOME (N_const32 Int   c32), rest) | NONE => default else
  if b = 0x42w then case read_s_8B bs of SOME (c64,rest) => (SOME (N_const64 Int   c64), rest) | NONE => default else
  if b = 0x43w then case read_f_4B bs of SOME (c32,rest) => (SOME (N_const32 Float c32), rest) | NONE => default else
  if b = 0x44w then case read_f_8B bs of SOME (c64,rest) => (SOME (N_const64 Float c64), rest) | NONE => default else

  (* trunc_sat_f. Forwhatever reason is coded as 2 bytes, instead of  *)
  if b = 0xFCw then case read_u_4B bs of
  | SOME (sel,rest) =>  (SOME (N_convert (Trunc_sat_f
                          (selWidth $ sel ' 1)
                          (selSign  $ sel ' 2)
                          (selWidth $ sel ' 0)
                        )) , rest)
  | NONE => default else

  default
End


(* encode a numeric instruction into bytes. *)

Definition encode_numI_def:
  encode_numI (i:num_instr) : byteStream = case i of

  | N_test       (Eqz W32)                    => [0x45w]
  | N_compare    (Eq Int W32)                 => [0x46w]
  | N_compare    (Ne Int W32)                 => [0x47w]
  | N_compare    (Lt_   Signed W32)           => [0x48w]
  | N_compare    (Lt_ Unsigned W32)           => [0x49w]
  | N_compare    (Gt_   Signed W32)           => [0x4Aw]
  | N_compare    (Gt_ Unsigned W32)           => [0x4Bw]
  | N_compare    (Le_   Signed W32)           => [0x4Cw]
  | N_compare    (Le_ Unsigned W32)           => [0x4Dw]
  | N_compare    (Ge_   Signed W32)           => [0x4Ew]
  | N_compare    (Ge_ Unsigned W32)           => [0x4Fw]
  | N_test       (Eqz W64)                    => [0x50w]
  | N_compare    (Eq Int W64)                 => [0x51w]
  | N_compare    (Ne Int W64)                 => [0x52w]
  | N_compare    (Lt_   Signed W64)           => [0x53w]
  | N_compare    (Lt_ Unsigned W64)           => [0x54w]
  | N_compare    (Gt_   Signed W64)           => [0x55w]
  | N_compare    (Gt_ Unsigned W64)           => [0x56w]
  | N_compare    (Le_   Signed W64)           => [0x57w]
  | N_compare    (Le_ Unsigned W64)           => [0x58w]
  | N_compare    (Ge_   Signed W64)           => [0x59w]
  | N_compare    (Ge_ Unsigned W64)           => [0x5Aw]
  | N_compare    (Eq Float W32)               => [0x5Bw]
  | N_compare    (Ne Float W32)               => [0x5Cw]
  | N_compare    (Lt W32)                     => [0x5Dw]
  | N_compare    (Gt W32)                     => [0x5Ew]
  | N_compare    (Le W32)                     => [0x5Fw]
  | N_compare    (Ge W32)                     => [0x60w]
  | N_compare    (Eq Float W64)               => [0x61w]
  | N_compare    (Ne Float W64)               => [0x62w]
  | N_compare    (Lt W64)                     => [0x63w]
  | N_compare    (Gt W64)                     => [0x64w]
  | N_compare    (Le W64)                     => [0x65w]
  | N_compare    (Ge W64)                     => [0x66w]
  | N_unary      (Clz    W32)                 => [0x67w]
  | N_unary      (Ctz    W32)                 => [0x68w]
  | N_unary      (Popcnt W32)                 => [0x69w]
  | N_binary     (Add Int W32)                => [0x6Aw]
  | N_binary     (Sub Int W32)                => [0x6Bw]
  | N_binary     (Mul Int W32)                => [0x6Cw]
  | N_binary     (Div_   Signed W32)          => [0x6Dw]
  | N_binary     (Div_ Unsigned W32)          => [0x6Ew]
  | N_binary     (Rem_   Signed W32)          => [0x6Fw]
  | N_binary     (Rem_ Unsigned W32)          => [0x70w]
  | N_binary     (And W32)                    => [0x71w]
  | N_binary     (Or W32)                     => [0x72w]
  | N_binary     (Xor W32)                    => [0x73w]
  | N_binary     (Shl W32)                    => [0x74w]
  | N_binary     (Shr_   Signed W32)          => [0x75w]
  | N_binary     (Shr_ Unsigned W32)          => [0x76w]
  | N_binary     (Rotl W32)                   => [0x77w]
  | N_binary     (Rotr W32)                   => [0x78w]
  | N_unary      (Clz    W64)                 => [0x79w]
  | N_unary      (Ctz    W64)                 => [0x7Aw]
  | N_unary      (Popcnt W64)                 => [0x7Bw]
  | N_binary     (Add Int W64)                => [0x7Cw]
  | N_binary     (Sub Int W64)                => [0x7Dw]
  | N_binary     (Mul Int W64)                => [0x7Ew]
  | N_binary     (Div_   Signed W64)          => [0x7Fw]
  | N_binary     (Div_ Unsigned W64)          => [0x80w]
  | N_binary     (Rem_   Signed W64)          => [0x81w]
  | N_binary     (Rem_ Unsigned W64)          => [0x82w]
  | N_binary     (And W64)                    => [0x83w]
  | N_binary     (Or  W64)                    => [0x84w]
  | N_binary     (Xor W64)                    => [0x85w]
  | N_binary     (Shl W64)                    => [0x86w]
  | N_binary     (Shr_   Signed W64)          => [0x87w]
  | N_binary     (Shr_ Unsigned W64)          => [0x88w]
  | N_binary     (Rotl W64)                   => [0x89w]
  | N_binary     (Rotr W64)                   => [0x8Aw]
  | N_unary      (Abs     W32)                => [0x8Bw]
  | N_unary      (Neg     W32)                => [0x8Cw]
  | N_unary      (Ceil    W32)                => [0x8Dw]
  | N_unary      (Floor   W32)                => [0x8Ew]
  | N_unary      (Trunc   W32)                => [0x8Fw]
  | N_unary      (Nearest W32)                => [0x90w]
  | N_unary      (Sqrt    W32)                => [0x91w]
  | N_binary     (Add Float W32)              => [0x92w]
  | N_binary     (Sub Float W32)              => [0x93w]
  | N_binary     (Mul Float W32)              => [0x94w]
  | N_binary     (Div W32)                    => [0x95w]
  | N_binary     (Min W32)                    => [0x96w]
  | N_binary     (Max W32)                    => [0x97w]
  | N_binary     (Copysign W32)               => [0x98w]
  | N_unary      (Abs     W64)                => [0x99w]
  | N_unary      (Neg     W64)                => [0x9Aw]
  | N_unary      (Ceil    W64)                => [0x9Bw]
  | N_unary      (Floor   W64)                => [0x9Cw]
  | N_unary      (Trunc   W64)                => [0x9Dw]
  | N_unary      (Nearest W64)                => [0x9Ew]
  | N_unary      (Sqrt    W64)                => [0x9Fw]
  | N_binary     (Add Float W64)              => [0xA0w]
  | N_binary     (Sub Float W64)              => [0xA1w]
  | N_binary     (Mul Float W64)              => [0xA2w]
  | N_binary     (Div W64)                    => [0xA3w]
  | N_binary     (Min W64)                    => [0xA4w]
  | N_binary     (Max W64)                    => [0xA5w]
  | N_binary     (Copysign W64)               => [0xA6w]
  | N_convert     Wrap_i64                    => [0xA7w]
  | N_convert    (Trunc_f W32   Signed W32)   => [0xA8w]
  | N_convert    (Trunc_f W32 Unsigned W32)   => [0xA9w]
  | N_convert    (Trunc_f W64   Signed W32)   => [0xAAw]
  | N_convert    (Trunc_f W64 Unsigned W32)   => [0xABw]
  | N_unary      (Extend_i32_   Signed)       => [0xACw]
  | N_unary      (Extend_i32_ Unsigned)       => [0xADw]
  | N_convert    (Trunc_f W32   Signed W64)   => [0xAEw]
  | N_convert    (Trunc_f W32 Unsigned W64)   => [0xAFw]
  | N_convert    (Trunc_f W64   Signed W64)   => [0xB0w]
  | N_convert    (Trunc_f W64 Unsigned W64)   => [0xB1w]
  | N_convert    (Convert W32   Signed W32)   => [0xB2w]
  | N_convert    (Convert W32 Unsigned W32)   => [0xB3w]
  | N_convert    (Convert W64   Signed W32)   => [0xB4w]
  | N_convert    (Convert W64 Unsigned W32)   => [0xB5w]
  | N_convert     Demote                      => [0xB6w]
  | N_convert    (Convert W32   Signed W64)   => [0xB7w]
  | N_convert    (Convert W32 Unsigned W64)   => [0xB8w]
  | N_convert    (Convert W64   Signed W64)   => [0xB9w]
  | N_convert    (Convert W64 Unsigned W64)   => [0xBAw]
  | N_convert     Promote                     => [0xBBw]
  | N_convert    (Reinterpret_f W32)          => [0xBCw]
  | N_convert    (Reinterpret_f W64)          => [0xBDw]
  | N_convert    (Reinterpret_i W32)          => [0xBEw]
  | N_convert    (Reinterpret_i W64)          => [0xBFw]
  | N_unary      (Extend8_s  W32)             => [0xC0w]
  | N_unary      (Extend16_s W32)             => [0xC1w]
  | N_unary      (Extend8_s  W64)             => [0xC2w]
  | N_unary      (Extend16_s W64)             => [0xC3w]
  | N_unary       Extend32_s                  => [0xC4w]

  | N_const32 Int   c32                       =>  0x41w :: write_s_4B c32 []
  | N_const64 Int   c64                       =>  0x42w :: write_s_8B c64 []
  | N_const32 Float c32                       =>  0x43w :: write_f_4B c32 []
  | N_const64 Float c64                       =>  0x44w :: write_f_8B c64 []

  | N_convert (Trunc_sat_f W32   Signed W32)  =>  0xFCw :: write_u_4B 0x0w []
  | N_convert (Trunc_sat_f W32 Unsigned W32)  =>  0xFCw :: write_u_4B 0x1w []
  | N_convert (Trunc_sat_f W64   Signed W32)  =>  0xFCw :: write_u_4B 0x2w []
  | N_convert (Trunc_sat_f W64 Unsigned W32)  =>  0xFCw :: write_u_4B 0x3w []
  | N_convert (Trunc_sat_f W32   Signed W64)  =>  0xFCw :: write_u_4B 0x4w []
  | N_convert (Trunc_sat_f W32 Unsigned W64)  =>  0xFCw :: write_u_4B 0x5w []
  | N_convert (Trunc_sat_f W64   Signed W64)  =>  0xFCw :: write_u_4B 0x6w []
  | N_convert (Trunc_sat_f W64 Unsigned W64)  =>  0xFCw :: write_u_4B 0x7w []

End


Theorem dec_enc_numI[simp]:
  ∀ t. decode_numI (encode_numI i) = (SOME t,[])
Proof
  Cases >> TRY (simp[decode_numI_def, encode_numI_def, read_u_word_def, write_u_word_def, read_write_u_4B]) >>
  cheat
QED


val _ = export_theory();
