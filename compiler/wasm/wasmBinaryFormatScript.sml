(*
  En- & De- coding between Cake's Wasm 1.0 AST & Wasm's binary format

  Notes
  - Rotten in Denmark: There's no way we're going to know the type of instructions ahead of time,
    so we need to structure decodes according the the grammar of programs. In particular, no
    having separate functions for numerics and control flow
*)

open preamble;
open leb128Theory;
(* open someWordOpsTheory; *)
open wasmLangTheory;

val _ = new_theory "wasmBinaryFormat";

(*  API
    enc goes from AST to Wasm Binary format (WBF)
    dec goes from WBF to AST

    enc_numtype : numtype -> byte
    dec_numtype : byte -> numtype option

    enc_numI : num_instr -> byteStream
    dec_numI : byteStream -> (num_instr option # byteStream)
 *)


(***********************************************)
(*                                             *)
(*     Wasm Binary Format ⇔ WasmCake AST      *)
(*                                             *)
(***********************************************)

(********************************)
(*   Misc notations/helps/etc   *)
(********************************)

Type byte[local]       = “:word8”
Type byteStream[local] = “:word8 list”

Overload dec_s32[local] = “dec_signed : byteStream -> (word32 # byteStream) option”
Overload dec_s64[local] = “dec_signed : byteStream -> (word64 # byteStream) option”
Overload dec_u8[local]  = “dec_unsigned_word : byteStream -> (byte # byteStream) option”
Overload dec_u32[local] = “dec_unsigned_word : byteStream -> (word64 # byteStream) option”

(***************************************)
(*   Encode-Decode pairs - Functions   *)
(***************************************)

Definition enc_numtype_def:
  enc_numtype (t:numtype) : byte = case t of
  | (NT Int   W32) => 0x7Fw
  | (NT Int   W64) => 0x7Ew
End

Definition dec_numtype_def:
  dec_numtype (b:byte) : numtype option =
  (* QQ Why not case? MM: this is better. Explanation elided for now *)
  if b = 0x7Fw then SOME (NT Int   W32) else
  if b = 0x7Ew then SOME (NT Int   W64) else NONE
End

Definition enc_valtype_def:
  enc_valtype (t:valtype) : byte = case t of
  | Tnum (NT Int   W32) => 0x7Fw
  | Tnum (NT Int   W64) => 0x7Ew
  | Tvec                => 0x7Bw
  | TFunRef             => 0x70w
  | TExtRef             => 0x6Fw
End

Definition dec_valtype_def:
  dec_valtype (b:byte) : valtype option =
  if b = 0x7Fw then SOME (Tnum $ NT Int   W32) else
  if b = 0x7Ew then SOME (Tnum $ NT Int   W64) else
  if b = 0x7Bw then SOME (Tvec               ) else
  if b = 0x70w then SOME (TFunRef            ) else
  if b = 0x6Fw then SOME (TExtRef            ) else NONE
End

Definition enc_numI_def:
  enc_numI (i:num_instr) : byteStream = case i of

  | N_eqz         W32                         => [0x45w]
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
  | N_eqz         W64                         => [0x45w]
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
  | N_convert     Wrap_i64                    => [0xA7w]
  | N_unary      (Extend_i32_   Signed)       => [0xACw]
  | N_unary      (Extend_i32_ Unsigned)       => [0xADw]
  | N_unary      (Extend8_s  W32)             => [0xC0w]
  | N_unary      (Extend16_s W32)             => [0xC1w]
  | N_unary      (Extend8_s  W64)             => [0xC2w]
  | N_unary      (Extend16_s W64)             => [0xC3w]
  | N_unary       Extend32_s                  => [0xC4w]

  | N_const32 Int   c32                       =>  0x41w :: enc_signed_word32 c32
  | N_const64 Int   c64                       =>  0x42w :: enc_signed_word64 c64

End

Definition dec_numI_def:
  dec_numI ([]:byteStream) : (num_instr option # byteStream) = (NONE, []) ∧
  dec_numI (b::bs) = let default = (NONE,b::bs) in

  if b = 0x45w then (SOME   (N_eqz         W32                         ), bs) else
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
  if b = 0x45w then (SOME   (N_eqz         W64                         ), bs) else
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
  if b = 0xA7w then (SOME   (N_convert     Wrap_i64                    ), bs) else
  if b = 0xACw then (SOME   (N_unary      (Extend_i32_   Signed)       ), bs) else
  if b = 0xADw then (SOME   (N_unary      (Extend_i32_ Unsigned)       ), bs) else
  if b = 0xC0w then (SOME   (N_unary      (Extend8_s  W32)             ), bs) else
  if b = 0xC1w then (SOME   (N_unary      (Extend16_s W32)             ), bs) else
  if b = 0xC2w then (SOME   (N_unary      (Extend8_s  W64)             ), bs) else
  if b = 0xC3w then (SOME   (N_unary      (Extend16_s W64)             ), bs) else
  if b = 0xC4w then (SOME   (N_unary       Extend32_s                  ), bs) else

  if b = 0x41w then case dec_s32 bs of SOME (s32,cs) => (SOME (N_const32 Int   s32), cs) | NONE => default else
  if b = 0x42w then case dec_s64 bs of SOME (s64,cs) => (SOME (N_const64 Int   s64), cs) | NONE => default else

  default
End

(***************)
(*             *)
(*     WIP     *)
(*             *)
(***************)

(* TODO *)
(*
Definition enc_blocktype_def:
  enc_blocktype =
End
Definition dec_blocktype_def:
  dec_blocktype =
End
*)
Overload elseOC = “0x05w : byte”
Overload endOC  = “0x0Bw : byte”
Definition enc_instr_def:
  enc_instr (inst:instr) (bs:byteStream) : byteStream = case inst of

  (* control instructions *)
  | Unreachable => 0x00w :: bs
  | Nop         => 0x01w :: bs

  (* TODO termination
  | Block bTyp body          => 0x02w :: enc_blocktype bTyp ++ (FOLDR enc_instr (endOC :: bs) body)
  | Loop  bTyp body          => 0x03w :: enc_blocktype bTyp ++ (FOLDR enc_instr (endOC :: bs) body)
  | If    bTyp bodyTh [    ] => 0x04w :: enc_blocktype bTyp ++ (FOLDR enc_instr (endOC :: bs) body)
  | If    bTyp bodyTh bodyEl => 0x04w :: enc_blocktype bTyp ++ (FOLDR enc_instr
                                                                  (elseOC :: (FOLDR enc_instr (endOC :: bs) bodyEl))
                                                                  bodyTh) *)

  | Br           lbl => 0x0Cw ::                    enc_num lbl ++ bs
  | BrIf         lbl => 0x0Dw ::                    enc_num lbl ++ bs
  | BrTable lbls lbl => 0x0Ew :: (* TODO lbls ++ *) enc_num lbl ++ bs

  | Return      => 0x0Fw :: bs
  | Call   fnId => 0x10w :: enc_num fnId ++ bs

  (* TODO
    (* | CallIndirect       num tf               TODO: first num is tableid *)
    (* | ReturnCall         num                  TODO: tail call *)
    (* | ReturnCallIndirect num tf               TODO: input/output params, names *)
  *)

  (* parametric instructions *)
  | Drop        => 0x1Aw :: bs
  | Select      => 0x1Bw :: bs

  (* variable instructions *)
  | LocalGet  x => 0x20w :: enc_num x ++ bs
  | LocalSet  x => 0x21w :: enc_num x ++ bs
  | LocalTee  x => 0x22w :: enc_num x ++ bs
  | GlobalGet x => 0x23w :: enc_num x ++ bs
  | GlobalSet x => 0x24w :: enc_num x ++ bs

  (* TODO
    (* memory instructions *)
    (* | Load  t ((tp_num # bool) option) word32 TODO: alignment *)
    (* | Store t tp_num word32                   TODO: alignment *)
  *)

  (* other classes of instructions *)
  | Numeric i => enc_numI i ++ bs

End

Definition dec_instr_def:

  dec_instr ([]:byteStream) : (instr option # byteStream) = (NONE,[]) ∧
  dec_instr (b::bs) = let default = (NONE, b::bs) in

  (* control instructions *)
  if b = 0x00w then (SOME Unreachable, bs) else
  if b = 0x01w then (SOME Nop        , bs) else


  if b = 0x0Fw then (SOME Return     , bs) else
  if b = 0x10w then case dec_num bs of NONE => default | SOME(f, cs) => (SOME $ Call f,cs) else

  (* parametric instructions *)
  if b = 0x1Aw then (SOME Drop  , bs) else
  if b = 0x1Bw then (SOME Select, bs) else

  (* variable instructions *)
  if b = 0x20w then case dec_num bs of NONE => default | SOME(x,cs) => (SOME $ LocalGet  x, cs) else
  if b = 0x21w then case dec_num bs of NONE => default | SOME(x,cs) => (SOME $ LocalSet  x, cs) else
  if b = 0x22w then case dec_num bs of NONE => default | SOME(x,cs) => (SOME $ LocalTee  x, cs) else
  if b = 0x23w then case dec_num bs of NONE => default | SOME(x,cs) => (SOME $ GlobalGet x, cs) else
  if b = 0x24w then case dec_num bs of NONE => default | SOME(x,cs) => (SOME $ GlobalSet x, cs) else


  default
End

val _ = export_theory();
