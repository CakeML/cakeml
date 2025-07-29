(*
  En- & De- coding between Cake's Wasm 1.0 AST & Wasm's binary format

  Notes
  - Rotten in Denmark: There's no way we're going to know the type of instructions ahead of time,
    so we need to structure decodes according the the grammar of programs. In particular, no
    having separate functions for numerics and control flow
*)

open preamble;
open leb128Theory;
open mlstringTheory;
open wasmLangTheory;

val _ = new_theory "wasm_binary_format";

(*  API
    enc goes from AST to Wasm Binary format (WBF)
    dec goes from WBF to AST

    enc_numtype : numtype -> byte
    dec_numtype : byte -> numtype option

    enc_numI : num_instr -> byteSeq
    dec_numI : byteSeq -> (num_instr option # byteSeq)
 *)


(***********************************************)
(*                                             *)
(*     Wasm Binary Format ⇔ WasmCake AST      *)
(*                                             *)
(***********************************************)

(********************************)
(*   Misc notations/helps/etc   *)
(********************************)

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”

Overload dec_s32[local] = “dec_signed : byteSeq -> (word32 # byteSeq) option”
Overload dec_s64[local] = “dec_signed : byteSeq -> (word64 # byteSeq) option”
Overload dec_u8[local]  = “dec_unsigned_word : byteSeq -> (byte # byteSeq) option”
Overload dec_u32[local] = “dec_unsigned_word : byteSeq -> (word64 # byteSeq) option”
Overload error = “λ str obj. (INL (strlit str),obj)”


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
  (* | Tvec                => 0x7Bw
  | TFunRef             => 0x70w
  | TExtRef             => 0x6Fw *)
End

Definition dec_valtype_def:
  dec_valtype (b:byte) : valtype option =
  if b = 0x7Fw then SOME (Tnum $ NT Int   W32) else
  if b = 0x7Ew then SOME (Tnum $ NT Int   W64) else
  (* if b = 0x7Bw then SOME (Tvec               ) else
  if b = 0x70w then SOME (TFunRef            ) else
  if b = 0x6Fw then SOME (TExtRef            ) else *)
  NONE
End

Definition enc_numI_def:
  enc_numI (i:num_instr) : byteSeq = case i of

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
  | N_convert     WrapI64                    => [0xA7w]
  | N_unary      (ExtendI32_   Signed)        => [0xACw]
  | N_unary      (ExtendI32_ Unsigned)        => [0xADw]
  | N_unary      (Extend8s  W32)              => [0xC0w]
  | N_unary      (Extend16s W32)              => [0xC1w]
  | N_unary      (Extend8s  W64)              => [0xC2w]
  | N_unary      (Extend16s W64)              => [0xC3w]
  | N_unary       Extend32s                   => [0xC4w]

  | N_const32 Int   c32                       =>  0x41w :: enc_signed_word32 c32
  | N_const64 Int   c64                       =>  0x42w :: enc_signed_word64 c64

End

Definition dec_numI_def:
  dec_numI ([]:byteSeq) : ((mlstring + num_instr) # byteSeq) = error "[dec_numI] : Given empty byteSeq." [] ∧
  dec_numI (b::bs) = let failure = error "[dec_numI] : " (b::bs) in

  if b = 0x45w then (INR $ N_eqz     $   W32                   ,bs) else
  if b = 0x46w then (INR $ N_compare $   Eq Int W32            ,bs) else
  if b = 0x47w then (INR $ N_compare $   Ne Int W32            ,bs) else
  if b = 0x48w then (INR $ N_compare $   Lt_   Signed W32      ,bs) else
  if b = 0x49w then (INR $ N_compare $   Lt_ Unsigned W32      ,bs) else
  if b = 0x4Aw then (INR $ N_compare $   Gt_   Signed W32      ,bs) else
  if b = 0x4Bw then (INR $ N_compare $   Gt_ Unsigned W32      ,bs) else
  if b = 0x4Cw then (INR $ N_compare $   Le_   Signed W32      ,bs) else
  if b = 0x4Dw then (INR $ N_compare $   Le_ Unsigned W32      ,bs) else
  if b = 0x4Ew then (INR $ N_compare $   Ge_   Signed W32      ,bs) else
  if b = 0x4Fw then (INR $ N_compare $   Ge_ Unsigned W32      ,bs) else
  if b = 0x45w then (INR $ N_eqz     $   W64                   ,bs) else
  if b = 0x51w then (INR $ N_compare $   Eq Int W64            ,bs) else
  if b = 0x52w then (INR $ N_compare $   Ne Int W64            ,bs) else
  if b = 0x53w then (INR $ N_compare $   Lt_   Signed W64      ,bs) else
  if b = 0x54w then (INR $ N_compare $   Lt_ Unsigned W64      ,bs) else
  if b = 0x55w then (INR $ N_compare $   Gt_   Signed W64      ,bs) else
  if b = 0x56w then (INR $ N_compare $   Gt_ Unsigned W64      ,bs) else
  if b = 0x57w then (INR $ N_compare $   Le_   Signed W64      ,bs) else
  if b = 0x58w then (INR $ N_compare $   Le_ Unsigned W64      ,bs) else
  if b = 0x59w then (INR $ N_compare $   Ge_   Signed W64      ,bs) else
  if b = 0x5Aw then (INR $ N_compare $   Ge_ Unsigned W64      ,bs) else
  if b = 0x67w then (INR $ N_unary   $   Clz    W32            ,bs) else
  if b = 0x68w then (INR $ N_unary   $   Ctz    W32            ,bs) else
  if b = 0x69w then (INR $ N_unary   $   Popcnt W32            ,bs) else
  if b = 0x6Aw then (INR $ N_binary  $   Add  Int      W32     ,bs) else
  if b = 0x6Bw then (INR $ N_binary  $   Sub  Int      W32     ,bs) else
  if b = 0x6Cw then (INR $ N_binary  $   Mul  Int      W32     ,bs) else
  if b = 0x6Dw then (INR $ N_binary  $   Div_   Signed W32     ,bs) else
  if b = 0x6Ew then (INR $ N_binary  $   Div_ Unsigned W32     ,bs) else
  if b = 0x6Fw then (INR $ N_binary  $   Rem_   Signed W32     ,bs) else
  if b = 0x70w then (INR $ N_binary  $   Rem_ Unsigned W32     ,bs) else
  if b = 0x71w then (INR $ N_binary  $   And           W32     ,bs) else
  if b = 0x72w then (INR $ N_binary  $   Or            W32     ,bs) else
  if b = 0x73w then (INR $ N_binary  $   Xor           W32     ,bs) else
  if b = 0x74w then (INR $ N_binary  $   Shl           W32     ,bs) else
  if b = 0x75w then (INR $ N_binary  $   Shr_   Signed W32     ,bs) else
  if b = 0x76w then (INR $ N_binary  $   Shr_ Unsigned W32     ,bs) else
  if b = 0x77w then (INR $ N_binary  $   Rotl          W32     ,bs) else
  if b = 0x78w then (INR $ N_binary  $   Rotr          W32     ,bs) else
  if b = 0x79w then (INR $ N_unary   $   Clz    W64            ,bs) else
  if b = 0x7Aw then (INR $ N_unary   $   Ctz    W64            ,bs) else
  if b = 0x7Bw then (INR $ N_unary   $   Popcnt W64            ,bs) else
  if b = 0x7Cw then (INR $ N_binary  $   Add Int W64           ,bs) else
  if b = 0x7Dw then (INR $ N_binary  $   Sub Int W64           ,bs) else
  if b = 0x7Ew then (INR $ N_binary  $   Mul Int W64           ,bs) else
  if b = 0x7Fw then (INR $ N_binary  $   Div_   Signed W64     ,bs) else
  if b = 0x80w then (INR $ N_binary  $   Div_ Unsigned W64     ,bs) else
  if b = 0x81w then (INR $ N_binary  $   Rem_   Signed W64     ,bs) else
  if b = 0x82w then (INR $ N_binary  $   Rem_ Unsigned W64     ,bs) else
  if b = 0x83w then (INR $ N_binary  $   And W64               ,bs) else
  if b = 0x84w then (INR $ N_binary  $   Or  W64               ,bs) else
  if b = 0x85w then (INR $ N_binary  $   Xor W64               ,bs) else
  if b = 0x86w then (INR $ N_binary  $   Shl W64               ,bs) else
  if b = 0x87w then (INR $ N_binary  $   Shr_   Signed W64     ,bs) else
  if b = 0x88w then (INR $ N_binary  $   Shr_ Unsigned W64     ,bs) else
  if b = 0x89w then (INR $ N_binary  $   Rotl W64              ,bs) else
  if b = 0x8Aw then (INR $ N_binary  $   Rotr W64              ,bs) else
  if b = 0xA7w then (INR $ N_convert $   WrapI64              ,bs) else
  if b = 0xACw then (INR $ N_unary   $   ExtendI32_   Signed   ,bs) else
  if b = 0xADw then (INR $ N_unary   $   ExtendI32_ Unsigned   ,bs) else
  if b = 0xC0w then (INR $ N_unary   $   Extend8s  W32         ,bs) else
  if b = 0xC1w then (INR $ N_unary   $   Extend16s W32         ,bs) else
  if b = 0xC2w then (INR $ N_unary   $   Extend8s  W64         ,bs) else
  if b = 0xC3w then (INR $ N_unary   $   Extend16s W64         ,bs) else
  if b = 0xC4w then (INR $ N_unary   $   Extend32s             ,bs) else

  if b = 0x41w then case dec_s32 bs of SOME (s32,cs) => (INR (N_const32 Int s32), cs) | NONE => failure else
  if b = 0x42w then case dec_s64 bs of SOME (s64,cs) => (INR (N_const64 Int s64), cs) | NONE => failure else

  failure
End

(* TODO *)
Theorem dec_enc_numI[simp]:
  ∀ t rest . dec_numI (enc_numI i ++ rest) = (INR t, rest)
Proof
  Cases >> simp[dec_numI_def, enc_numI_def ] >>
  cheat
QED


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

(* TODO : helper to make sure AST nums fit within the Wasm spec'd sizes like u32 etc *)
(*
Definition enc_instr_def:
(  enc_instr (inst:instr) (bs:byteSeq) : byteSeq = case inst of

  (* control instructions *)
  | Unreachable => 0x00w :: bs
  | Nop         => 0x01w :: bs

  (* TODO termination *)
  | Block bTyp body          => 0x02w :: enc_blocktype bTyp ++ enc_instr_list body
  | Loop  bTyp body          => 0x03w :: enc_blocktype bTyp ++ enc_instr_list body
  | If    bTyp bodyTh [    ] => 0x04w :: enc_blocktype bTyp ++ enc_instr_list body
  | If    bTyp bodyTh bodyEl => 0x04w :: enc_blocktype bTyp ++ enc_instr_list bodyTh ++ elseOC :: enc_instr_list bodyEl

  | Br           lbl => 0x0Cw ::                    enc_num lbl ++ bs
  | BrIf         lbl => 0x0Dw ::                    enc_num lbl ++ bs
  | BrTable lbls lbl => 0x0Ew :: (* TODO lbls ++ *) enc_num lbl ++ bs

  | Return      => 0x0Fw :: bs
  | Call   fnId => (* TODO *) 0x10w :: enc_num fnId ++ bs

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
) ∧
  (enc_instr_list ([]:instr list) = [endOC]) ∧
  (enc_instr_list (i::instrs) = enc_instr i ++ enc_instr_list instrs)
End
*)

Definition dec_instr_def:

  dec_instr ([]:byteSeq) : (instr option # byteSeq) = (NONE,[]) ∧
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
