(*
  En- & De- coding between Cake's Wasm 2.0 AST & Wasm's binary format

*)

open preamble;
open wasm2LangTheory;
open mlstringTheory;
open leb128Theory miscOpsTheory;

val _ = new_theory "wasm2_binary_format";

(*  Note:
    enc goes from AST to Wasm Binary format (WBF)
    dec goes from WBF to AST
 *)


(************************************)
(*                                  *)
(*     Misc notations/helps/etc     *)
(*                                  *)
(************************************)

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”

Overload zeroB[local] = “0x00w:byte”
Overload elseB[local] = “0x05w:byte”
Overload endB[local]  = “0x0Bw:byte”
Overload B0[local]    = “λ x. x = zeroB”

Overload error = “λ str obj. (INL (strlit str),obj)”
(* ": Byte sequence unexpectedly empty." *)

Overload dec_u8[local]  = “dec_unsigned_word : byteSeq -> (byte   # byteSeq) option”
Overload dec_u32[local] = “dec_unsigned_word : byteSeq -> (word32 # byteSeq) option”
Overload dec_u64[local] = “dec_unsigned_word : byteSeq -> (word64 # byteSeq) option”

Overload dec_s8[local]  = “dec_signed        : byteSeq -> (byte   # byteSeq) option”
Overload dec_s32[local] = “dec_signed        : byteSeq -> (word32 # byteSeq) option”
Overload dec_s64[local] = “dec_signed        : byteSeq -> (word64 # byteSeq) option”

Overload enc_u8[local]  = “enc_unsigned_word : byte   -> byteSeq”
Overload enc_u32[local] = “enc_unsigned_word : word32 -> byteSeq”
Overload enc_u64[local] = “enc_unsigned_word : word64 -> byteSeq”

Overload enc_s8[local]  = “enc_signed_word8  : byte   -> byteSeq”
Overload enc_s32[local] = “enc_signed_word32 : word32 -> byteSeq”
Overload enc_s64[local] = “enc_signed_word64 : word64 -> byteSeq”

Definition dec_2u32_def:
  dec_2u32 (bs:byteSeq) : (word32 # word32 # byteSeq) option =
  case dec_u32 bs of NONE=>NONE| SOME(n,cs) =>
  case dec_u32 cs of NONE=>NONE| SOME(m,rs) => SOME (n,m,rs)
End

Definition enc_2u32_def:
  enc_2u32 w v = enc_u32 w ++ enc_u32 v
End

Theorem dec_enc_2u32[simp]:
  dec_2u32 (enc_2u32 w v ++ rest) = SOME (w,v,rest)
Proof
  rw[enc_2u32_def, dec_2u32_def, dec_enc_unsigned_word]
  >> rewrite_tac[GSYM APPEND_ASSOC]
  >> rw[dec_enc_unsigned_word]
QED


Definition dec_2u32_u8_def:
  dec_2u32_u8 (bs:byteSeq) : (word32 # word32 # byte # byteSeq) option =
    case dec_u32 bs of NONE=>NONE| SOME(i,cs) =>
    case dec_u32 cs of NONE=>NONE| SOME(j,ds) =>
    case dec_u8  ds of NONE=>NONE| SOME(k,rs) => SOME (i,j,k,rs)
End

Definition enc_2u32_u8_def:
  enc_2u32_u8 ofs al lid = enc_u32 ofs ++ enc_u32 al ++ enc_u8 lid
End

Theorem dec_enc_2u32_u8[simp]:
  dec_2u32_u8 (enc_2u32_u8 ofs al lid ++ rest) = SOME (ofs,al,lid,rest)
Proof
  rw[enc_2u32_u8_def, dec_2u32_u8_def]
  (* ASKYK ASKMM *)
  (* what's the right way to eliminate this repetition *)
  >> (rewrite_tac[GSYM APPEND_ASSOC]
  >> rw[dec_enc_unsigned_word])
  >> (rewrite_tac[GSYM APPEND_ASSOC])
  >> rw[dec_enc_unsigned_word]
  (* something else to try *)
  (* >> simp_tac std_ss [GSYM APPEND_ASSOC]
  >> rw[dec_enc_unsigned_word] *)
QED


(* ASKYK ASKMM *)
(* what's the right way to add notated (with word width)
   dec_enc_unsigned_word versions to the simp set *)
Theorem dec_enc_u32[simp]:
  dec_u32 (enc_u32 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_unsigned_word]
QED

Theorem dec_enc_s8[simp]:
  dec_s8 (enc_s8 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_signed_word8]
QED

Theorem dec_enc_s32[simp]:
  dec_s32 (enc_s32 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_signed_word32]
QED

Theorem dec_enc_s64[simp]:
  dec_s64 (enc_s64 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_signed_word64]
QED

(***********************************************)
(*                                             *)
(*     Wasm Binary Format ⇔ WasmCake AST      *)
(*                                             *)
(***********************************************)

(***************************************)
(*   Encode-Decode pairs - Functions   *)
(***************************************)

Definition enc_valtype_def:
  enc_valtype (t:valtype) : byte = case t of
  | Tnum   Int W32 => 0x7Fw
  | Tnum   Int W64 => 0x7Ew
  | Tnum Float W32 => 0x7Dw
  | Tnum Float W64 => 0x7Cw
  | Tvec           => 0x7Bw
  | TFunRef        => 0x70w
  | TExtRef        => 0x6Fw
End

Definition dec_valtype_def:
  dec_valtype (b:byte) : valtype option =
  if b = 0x7Fw then SOME (Tnum   Int W32) else
  if b = 0x7Ew then SOME (Tnum   Int W64) else
  if b = 0x7Dw then SOME (Tnum Float W32) else
  if b = 0x7Cw then SOME (Tnum Float W64) else
  if b = 0x7Bw then SOME  Tvec            else
  if b = 0x70w then SOME  TFunRef         else
  if b = 0x6Fw then SOME  TExtRef         else
  NONE
End



Definition enc_numI_def:
  enc_numI (i:num_instr) : byteSeq = case i of
  | N_eqz     $   W32                        => [0x45w]
  | N_compare $   Eq  Int      W32           => [0x46w]
  | N_compare $   Ne  Int      W32           => [0x47w]
  | N_compare $   Lt_   Signed W32           => [0x48w]
  | N_compare $   Lt_ Unsigned W32           => [0x49w]
  | N_compare $   Gt_   Signed W32           => [0x4Aw]
  | N_compare $   Gt_ Unsigned W32           => [0x4Bw]
  | N_compare $   Le_   Signed W32           => [0x4Cw]
  | N_compare $   Le_ Unsigned W32           => [0x4Dw]
  | N_compare $   Ge_   Signed W32           => [0x4Ew]
  | N_compare $   Ge_ Unsigned W32           => [0x4Fw]
  | N_eqz     $   W64                        => [0x45w]
  | N_compare $   Eq Int       W64           => [0x51w]
  | N_compare $   Ne Int       W64           => [0x52w]
  | N_compare $   Lt_   Signed W64           => [0x53w]
  | N_compare $   Lt_ Unsigned W64           => [0x54w]
  | N_compare $   Gt_   Signed W64           => [0x55w]
  | N_compare $   Gt_ Unsigned W64           => [0x56w]
  | N_compare $   Le_   Signed W64           => [0x57w]
  | N_compare $   Le_ Unsigned W64           => [0x58w]
  | N_compare $   Ge_   Signed W64           => [0x59w]
  | N_compare $   Ge_ Unsigned W64           => [0x5Aw]
  | N_compare $   Eq  Float    W32           => [0x5Bw]
  | N_compare $   Ne  Float    W32           => [0x5Cw]
  | N_compare $   Lt           W32           => [0x5Dw]
  | N_compare $   Gt           W32           => [0x5Ew]
  | N_compare $   Le           W32           => [0x5Fw]
  | N_compare $   Ge           W32           => [0x60w]
  | N_compare $   Eq  Float    W64           => [0x61w]
  | N_compare $   Ne  Float    W64           => [0x62w]
  | N_compare $   Lt           W64           => [0x63w]
  | N_compare $   Gt           W64           => [0x64w]
  | N_compare $   Le           W64           => [0x65w]
  | N_compare $   Ge           W64           => [0x66w]
  | N_unary   $   Clz    W32                 => [0x67w]
  | N_unary   $   Ctz    W32                 => [0x68w]
  | N_unary   $   Popcnt W32                 => [0x69w]
  | N_binary  $   Add  Int      W32          => [0x6Aw]
  | N_binary  $   Sub  Int      W32          => [0x6Bw]
  | N_binary  $   Mul  Int      W32          => [0x6Cw]
  | N_binary  $   Div_   Signed W32          => [0x6Dw]
  | N_binary  $   Div_ Unsigned W32          => [0x6Ew]
  | N_binary  $   Rem_   Signed W32          => [0x6Fw]
  | N_binary  $   Rem_ Unsigned W32          => [0x70w]
  | N_binary  $   And           W32          => [0x71w]
  | N_binary  $   Or            W32          => [0x72w]
  | N_binary  $   Xor           W32          => [0x73w]
  | N_binary  $   Shl           W32          => [0x74w]
  | N_binary  $   Shr_   Signed W32          => [0x75w]
  | N_binary  $   Shr_ Unsigned W32          => [0x76w]
  | N_binary  $   Rotl          W32          => [0x77w]
  | N_binary  $   Rotr          W32          => [0x78w]
  | N_unary   $   Clz    W64                 => [0x79w]
  | N_unary   $   Ctz    W64                 => [0x7Aw]
  | N_unary   $   Popcnt W64                 => [0x7Bw]
  | N_binary  $   Add Int       W64          => [0x7Cw]
  | N_binary  $   Sub Int       W64          => [0x7Dw]
  | N_binary  $   Mul Int       W64          => [0x7Ew]
  | N_binary  $   Div_   Signed W64          => [0x7Fw]
  | N_binary  $   Div_ Unsigned W64          => [0x80w]
  | N_binary  $   Rem_   Signed W64          => [0x81w]
  | N_binary  $   Rem_ Unsigned W64          => [0x82w]
  | N_binary  $   And           W64          => [0x83w]
  | N_binary  $   Or            W64          => [0x84w]
  | N_binary  $   Xor           W64          => [0x85w]
  | N_binary  $   Shl           W64          => [0x86w]
  | N_binary  $   Shr_   Signed W64          => [0x87w]
  | N_binary  $   Shr_ Unsigned W64          => [0x88w]
  | N_binary  $   Rotl          W64          => [0x89w]
  | N_binary  $   Rotr          W64          => [0x8Aw]
  | N_unary   $   Abs     W32                => [0x8Bw]
  | N_unary   $   Neg     W32                => [0x8Cw]
  | N_unary   $   Ceil    W32                => [0x8Dw]
  | N_unary   $   Floor   W32                => [0x8Ew]
  | N_unary   $   Trunc   W32                => [0x8Fw]
  | N_unary   $   Nearest W32                => [0x90w]
  | N_unary   $   Sqrt    W32                => [0x91w]
  | N_binary  $   Add Float W32              => [0x92w]
  | N_binary  $   Sub Float W32              => [0x93w]
  | N_binary  $   Mul Float W32              => [0x94w]
  | N_binary  $   Div       W32              => [0x95w]
  | N_binary  $   Min       W32              => [0x96w]
  | N_binary  $   Max       W32              => [0x97w]
  | N_binary  $   Copysign  W32              => [0x98w]
  | N_unary   $   Abs     W64                => [0x99w]
  | N_unary   $   Neg     W64                => [0x9Aw]
  | N_unary   $   Ceil    W64                => [0x9Bw]
  | N_unary   $   Floor   W64                => [0x9Cw]
  | N_unary   $   Trunc   W64                => [0x9Dw]
  | N_unary   $   Nearest W64                => [0x9Ew]
  | N_unary   $   Sqrt    W64                => [0x9Fw]
  | N_binary  $   Add Float W64              => [0xA0w]
  | N_binary  $   Sub Float W64              => [0xA1w]
  | N_binary  $   Mul Float W64              => [0xA2w]
  | N_binary  $   Div       W64              => [0xA3w]
  | N_binary  $   Min       W64              => [0xA4w]
  | N_binary  $   Max       W64              => [0xA5w]
  | N_binary  $   Copysign  W64              => [0xA6w]
  | N_convert $   WrapI64                    => [0xA7w]
  | N_convert $   Trunc_f W32   Signed W32   => [0xA8w]
  | N_convert $   Trunc_f W32 Unsigned W32   => [0xA9w]
  | N_convert $   Trunc_f W64   Signed W32   => [0xAAw]
  | N_convert $   Trunc_f W64 Unsigned W32   => [0xABw]
  | N_unary   $   ExtendI32_   Signed        => [0xACw]
  | N_unary   $   ExtendI32_ Unsigned        => [0xADw]
  | N_convert $   Trunc_f W32   Signed W64   => [0xAEw]
  | N_convert $   Trunc_f W32 Unsigned W64   => [0xAFw]
  | N_convert $   Trunc_f W64   Signed W64   => [0xB0w]
  | N_convert $   Trunc_f W64 Unsigned W64   => [0xB1w]
  | N_convert $   Convert W32   Signed W32   => [0xB2w]
  | N_convert $   Convert W32 Unsigned W32   => [0xB3w]
  | N_convert $   Convert W64   Signed W32   => [0xB4w]
  | N_convert $   Convert W64 Unsigned W32   => [0xB5w]
  | N_convert $   Demote                     => [0xB6w]
  | N_convert $   Convert W32   Signed W64   => [0xB7w]
  | N_convert $   Convert W32 Unsigned W64   => [0xB8w]
  | N_convert $   Convert W64   Signed W64   => [0xB9w]
  | N_convert $   Convert W64 Unsigned W64   => [0xBAw]
  | N_convert $   Promote                    => [0xBBw]
  | N_convert $   Reinterpret_f        W32   => [0xBCw]
  | N_convert $   Reinterpret_f        W64   => [0xBDw]
  | N_convert $   Reinterpret_i        W32   => [0xBEw]
  | N_convert $   Reinterpret_i        W64   => [0xBFw]
  | N_unary   $   Extend8s  W32              => [0xC0w]
  | N_unary   $   Extend16s W32              => [0xC1w]
  | N_unary   $   Extend8s  W64              => [0xC2w]
  | N_unary   $   Extend16s W64              => [0xC3w]
  | N_unary   $   Extend32s                  => [0xC4w]

  | N_const32 Int   (c32: word32)            =>  0x41w :: enc_s32 c32
  | N_const64 Int   (c64: word64)            =>  0x42w :: enc_s64 c64

  | N_const32 Float (c32: word32)            =>  0x43w :: lend c32
  | N_const64 Float (c64: word64)            =>  0x44w :: lend c64

  | N_convert $   Trunc_sat_f W32   Signed W32   => 0xFCw :: enc_u32 0w
  | N_convert $   Trunc_sat_f W32 Unsigned W32   => 0xFCw :: enc_u32 1w
  | N_convert $   Trunc_sat_f W64   Signed W32   => 0xFCw :: enc_u32 2w
  | N_convert $   Trunc_sat_f W64 Unsigned W32   => 0xFCw :: enc_u32 3w
  | N_convert $   Trunc_sat_f W32   Signed W64   => 0xFCw :: enc_u32 4w
  | N_convert $   Trunc_sat_f W32 Unsigned W64   => 0xFCw :: enc_u32 5w
  | N_convert $   Trunc_sat_f W64   Signed W64   => 0xFCw :: enc_u32 6w
  | N_convert $   Trunc_sat_f W64 Unsigned W64   => 0xFCw :: enc_u32 7w

End

Definition dec_numI_def:
  dec_numI ([]:byteSeq) : ((mlstring + num_instr) # byteSeq) = error "[dec_numI]" [] ∧
  dec_numI (b::bs) = let failure = error "[dec_numI]" $ b::bs in

  if b = 0x45w then (INR $ N_eqz     $   W32                        ,bs) else
  if b = 0x46w then (INR $ N_compare $   Eq Int W32                 ,bs) else
  if b = 0x47w then (INR $ N_compare $   Ne Int W32                 ,bs) else
  if b = 0x48w then (INR $ N_compare $   Lt_   Signed W32           ,bs) else
  if b = 0x49w then (INR $ N_compare $   Lt_ Unsigned W32           ,bs) else
  if b = 0x4Aw then (INR $ N_compare $   Gt_   Signed W32           ,bs) else
  if b = 0x4Bw then (INR $ N_compare $   Gt_ Unsigned W32           ,bs) else
  if b = 0x4Cw then (INR $ N_compare $   Le_   Signed W32           ,bs) else
  if b = 0x4Dw then (INR $ N_compare $   Le_ Unsigned W32           ,bs) else
  if b = 0x4Ew then (INR $ N_compare $   Ge_   Signed W32           ,bs) else
  if b = 0x4Fw then (INR $ N_compare $   Ge_ Unsigned W32           ,bs) else
  if b = 0x45w then (INR $ N_eqz     $   W64                        ,bs) else
  if b = 0x51w then (INR $ N_compare $   Eq Int W64                 ,bs) else
  if b = 0x52w then (INR $ N_compare $   Ne Int W64                 ,bs) else
  if b = 0x53w then (INR $ N_compare $   Lt_   Signed W64           ,bs) else
  if b = 0x54w then (INR $ N_compare $   Lt_ Unsigned W64           ,bs) else
  if b = 0x55w then (INR $ N_compare $   Gt_   Signed W64           ,bs) else
  if b = 0x56w then (INR $ N_compare $   Gt_ Unsigned W64           ,bs) else
  if b = 0x57w then (INR $ N_compare $   Le_   Signed W64           ,bs) else
  if b = 0x58w then (INR $ N_compare $   Le_ Unsigned W64           ,bs) else
  if b = 0x59w then (INR $ N_compare $   Ge_   Signed W64           ,bs) else
  if b = 0x5Aw then (INR $ N_compare $   Ge_ Unsigned W64           ,bs) else
  if b = 0x5Bw then (INR $ N_compare $   Eq Float W32               ,bs) else
  if b = 0x5Cw then (INR $ N_compare $   Ne Float W32               ,bs) else
  if b = 0x5Dw then (INR $ N_compare $   Lt W32                     ,bs) else
  if b = 0x5Ew then (INR $ N_compare $   Gt W32                     ,bs) else
  if b = 0x5Fw then (INR $ N_compare $   Le W32                     ,bs) else
  if b = 0x60w then (INR $ N_compare $   Ge W32                     ,bs) else
  if b = 0x61w then (INR $ N_compare $   Eq Float W64               ,bs) else
  if b = 0x62w then (INR $ N_compare $   Ne Float W64               ,bs) else
  if b = 0x63w then (INR $ N_compare $   Lt W64                     ,bs) else
  if b = 0x64w then (INR $ N_compare $   Gt W64                     ,bs) else
  if b = 0x65w then (INR $ N_compare $   Le W64                     ,bs) else
  if b = 0x66w then (INR $ N_compare $   Ge W64                     ,bs) else
  if b = 0x67w then (INR $ N_unary   $   Clz    W32                 ,bs) else
  if b = 0x68w then (INR $ N_unary   $   Ctz    W32                 ,bs) else
  if b = 0x69w then (INR $ N_unary   $   Popcnt W32                 ,bs) else
  if b = 0x6Aw then (INR $ N_binary  $   Add Int W32                ,bs) else
  if b = 0x6Bw then (INR $ N_binary  $   Sub Int W32                ,bs) else
  if b = 0x6Cw then (INR $ N_binary  $   Mul Int W32                ,bs) else
  if b = 0x6Dw then (INR $ N_binary  $   Div_   Signed W32          ,bs) else
  if b = 0x6Ew then (INR $ N_binary  $   Div_ Unsigned W32          ,bs) else
  if b = 0x6Fw then (INR $ N_binary  $   Rem_   Signed W32          ,bs) else
  if b = 0x70w then (INR $ N_binary  $   Rem_ Unsigned W32          ,bs) else
  if b = 0x71w then (INR $ N_binary  $   And W32                    ,bs) else
  if b = 0x72w then (INR $ N_binary  $   Or W32                     ,bs) else
  if b = 0x73w then (INR $ N_binary  $   Xor W32                    ,bs) else
  if b = 0x74w then (INR $ N_binary  $   Shl W32                    ,bs) else
  if b = 0x75w then (INR $ N_binary  $   Shr_   Signed W32          ,bs) else
  if b = 0x76w then (INR $ N_binary  $   Shr_ Unsigned W32          ,bs) else
  if b = 0x77w then (INR $ N_binary  $   Rotl W32                   ,bs) else
  if b = 0x78w then (INR $ N_binary  $   Rotr W32                   ,bs) else
  if b = 0x79w then (INR $ N_unary   $   Clz    W64                 ,bs) else
  if b = 0x7Aw then (INR $ N_unary   $   Ctz    W64                 ,bs) else
  if b = 0x7Bw then (INR $ N_unary   $   Popcnt W64                 ,bs) else
  if b = 0x7Cw then (INR $ N_binary  $   Add Int W64                ,bs) else
  if b = 0x7Dw then (INR $ N_binary  $   Sub Int W64                ,bs) else
  if b = 0x7Ew then (INR $ N_binary  $   Mul Int W64                ,bs) else
  if b = 0x7Fw then (INR $ N_binary  $   Div_   Signed W64          ,bs) else
  if b = 0x80w then (INR $ N_binary  $   Div_ Unsigned W64          ,bs) else
  if b = 0x81w then (INR $ N_binary  $   Rem_   Signed W64          ,bs) else
  if b = 0x82w then (INR $ N_binary  $   Rem_ Unsigned W64          ,bs) else
  if b = 0x83w then (INR $ N_binary  $   And W64                    ,bs) else
  if b = 0x84w then (INR $ N_binary  $   Or  W64                    ,bs) else
  if b = 0x85w then (INR $ N_binary  $   Xor W64                    ,bs) else
  if b = 0x86w then (INR $ N_binary  $   Shl W64                    ,bs) else
  if b = 0x87w then (INR $ N_binary  $   Shr_   Signed W64          ,bs) else
  if b = 0x88w then (INR $ N_binary  $   Shr_ Unsigned W64          ,bs) else
  if b = 0x89w then (INR $ N_binary  $   Rotl W64                   ,bs) else
  if b = 0x8Aw then (INR $ N_binary  $   Rotr W64                   ,bs) else
  if b = 0x8Bw then (INR $ N_unary   $   Abs     W32                ,bs) else
  if b = 0x8Cw then (INR $ N_unary   $   Neg     W32                ,bs) else
  if b = 0x8Dw then (INR $ N_unary   $   Ceil    W32                ,bs) else
  if b = 0x8Ew then (INR $ N_unary   $   Floor   W32                ,bs) else
  if b = 0x8Fw then (INR $ N_unary   $   Trunc   W32                ,bs) else
  if b = 0x90w then (INR $ N_unary   $   Nearest W32                ,bs) else
  if b = 0x91w then (INR $ N_unary   $   Sqrt    W32                ,bs) else
  if b = 0x92w then (INR $ N_binary  $   Add Float W32              ,bs) else
  if b = 0x93w then (INR $ N_binary  $   Sub Float W32              ,bs) else
  if b = 0x94w then (INR $ N_binary  $   Mul Float W32              ,bs) else
  if b = 0x95w then (INR $ N_binary  $   Div W32                    ,bs) else
  if b = 0x96w then (INR $ N_binary  $   Min W32                    ,bs) else
  if b = 0x97w then (INR $ N_binary  $   Max W32                    ,bs) else
  if b = 0x98w then (INR $ N_binary  $   Copysign W32               ,bs) else
  if b = 0x99w then (INR $ N_unary   $   Abs     W64                ,bs) else
  if b = 0x9Aw then (INR $ N_unary   $   Neg     W64                ,bs) else
  if b = 0x9Bw then (INR $ N_unary   $   Ceil    W64                ,bs) else
  if b = 0x9Cw then (INR $ N_unary   $   Floor   W64                ,bs) else
  if b = 0x9Dw then (INR $ N_unary   $   Trunc   W64                ,bs) else
  if b = 0x9Ew then (INR $ N_unary   $   Nearest W64                ,bs) else
  if b = 0x9Fw then (INR $ N_unary   $   Sqrt    W64                ,bs) else
  if b = 0xA0w then (INR $ N_binary  $   Add Float W64              ,bs) else
  if b = 0xA1w then (INR $ N_binary  $   Sub Float W64              ,bs) else
  if b = 0xA2w then (INR $ N_binary  $   Mul Float W64              ,bs) else
  if b = 0xA3w then (INR $ N_binary  $   Div W64                    ,bs) else
  if b = 0xA4w then (INR $ N_binary  $   Min W64                    ,bs) else
  if b = 0xA5w then (INR $ N_binary  $   Max W64                    ,bs) else
  if b = 0xA6w then (INR $ N_binary  $   Copysign W64               ,bs) else
  if b = 0xA7w then (INR $ N_convert $   WrapI64                    ,bs) else
  if b = 0xA8w then (INR $ N_convert $   Trunc_f W32   Signed W32   ,bs) else
  if b = 0xA9w then (INR $ N_convert $   Trunc_f W32 Unsigned W32   ,bs) else
  if b = 0xAAw then (INR $ N_convert $   Trunc_f W64   Signed W32   ,bs) else
  if b = 0xABw then (INR $ N_convert $   Trunc_f W64 Unsigned W32   ,bs) else
  if b = 0xACw then (INR $ N_unary   $   ExtendI32_   Signed        ,bs) else
  if b = 0xADw then (INR $ N_unary   $   ExtendI32_ Unsigned        ,bs) else
  if b = 0xAEw then (INR $ N_convert $   Trunc_f W32   Signed W64   ,bs) else
  if b = 0xAFw then (INR $ N_convert $   Trunc_f W32 Unsigned W64   ,bs) else
  if b = 0xB0w then (INR $ N_convert $   Trunc_f W64   Signed W64   ,bs) else
  if b = 0xB1w then (INR $ N_convert $   Trunc_f W64 Unsigned W64   ,bs) else
  if b = 0xB2w then (INR $ N_convert $   Convert W32   Signed W32   ,bs) else
  if b = 0xB3w then (INR $ N_convert $   Convert W32 Unsigned W32   ,bs) else
  if b = 0xB4w then (INR $ N_convert $   Convert W64   Signed W32   ,bs) else
  if b = 0xB5w then (INR $ N_convert $   Convert W64 Unsigned W32   ,bs) else
  if b = 0xB6w then (INR $ N_convert $   Demote                     ,bs) else
  if b = 0xB7w then (INR $ N_convert $   Convert W32   Signed W64   ,bs) else
  if b = 0xB8w then (INR $ N_convert $   Convert W32 Unsigned W64   ,bs) else
  if b = 0xB9w then (INR $ N_convert $   Convert W64   Signed W64   ,bs) else
  if b = 0xBAw then (INR $ N_convert $   Convert W64 Unsigned W64   ,bs) else
  if b = 0xBBw then (INR $ N_convert $   Promote                    ,bs) else
  if b = 0xBCw then (INR $ N_convert $   Reinterpret_f W32          ,bs) else
  if b = 0xBDw then (INR $ N_convert $   Reinterpret_f W64          ,bs) else
  if b = 0xBEw then (INR $ N_convert $   Reinterpret_i W32          ,bs) else
  if b = 0xBFw then (INR $ N_convert $   Reinterpret_i W64          ,bs) else
  if b = 0xC0w then (INR $ N_unary   $   Extend8s  W32              ,bs) else
  if b = 0xC1w then (INR $ N_unary   $   Extend16s W32              ,bs) else
  if b = 0xC2w then (INR $ N_unary   $   Extend8s  W64              ,bs) else
  if b = 0xC3w then (INR $ N_unary   $   Extend16s W64              ,bs) else
  if b = 0xC4w then (INR $ N_unary   $   Extend32s                  ,bs) else

  if b = 0x41w then case dec_s32 bs of SOME (s32,cs) => (INR $ N_const32  Int  s32, cs) | NONE => failure else
  if b = 0x42w then case dec_s64 bs of SOME (s64,cs) => (INR $ N_const64  Int  s64, cs) | NONE => failure else

  if b = 0x43w then case unlend bs of SOME (c32,cs) => (INR $ N_const32 Float c32, cs) | NONE => failure else
  if b = 0x44w then case unlend bs of SOME (c64,cs) => (INR $ N_const64 Float c64, cs) | NONE => failure else

  if b = 0xFCw then case dec_u32 bs of NONE=>failure| SOME (oc, rs) =>
    if oc = 0w then (INR $ N_convert $   Trunc_sat_f W32   Signed W32   ,rs) else
    if oc = 1w then (INR $ N_convert $   Trunc_sat_f W32 Unsigned W32   ,rs) else
    if oc = 2w then (INR $ N_convert $   Trunc_sat_f W64   Signed W32   ,rs) else
    if oc = 3w then (INR $ N_convert $   Trunc_sat_f W64 Unsigned W32   ,rs) else
    if oc = 4w then (INR $ N_convert $   Trunc_sat_f W32   Signed W64   ,rs) else
    if oc = 5w then (INR $ N_convert $   Trunc_sat_f W32 Unsigned W64   ,rs) else
    if oc = 6w then (INR $ N_convert $   Trunc_sat_f W64   Signed W64   ,rs) else
    if oc = 7w then (INR $ N_convert $   Trunc_sat_f W64 Unsigned W64   ,rs) else
    failure
  else
  (* failure "[dec_numI] : Not a numeric instruction" *)
  failure
End

(* ASKYK ASKMM *)
(* this is super slow. How to speed up *)
Theorem dec_enc_numI:
  ∀ i. dec_numI (enc_numI i ++ rest) = (INR i, rest)
Proof
  cheat
  (* the following script results in

    1 subgoal:
    val it =

       w = W32

       : proof

    ?????? + it takes super long (like 15 seconds)
  *)
  (*
  rw[enc_numI_def] >> every_case_tac
  >>~ [ `Trunc_sat_f`]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]

  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]
  >- rw[dec_numI_def]

  >> rw[dec_numI_def]
  *)
QED



(*-----------------------------------------------------------------------------------------------------------------------------------------------------------*)


Overload v_opcode[local] = “λ n. 0xFDw :: enc_num n”
Definition enc_vecI_def:
  enc_vecI (i:vec_instr) : byteSeq = case i of

  | V_binary  $   Vswizzle                              => v_opcode 14
  | V_splat   $          IShp $ Is3 $ Is2 I8x16         => v_opcode 15
  | V_splat   $          IShp $ Is3 $ Is2 I16x8         => v_opcode 16
  | V_splat   $          IShp $ Is3       I32x4         => v_opcode 17
  | V_splat   $          IShp             I64x2         => v_opcode 18
  | V_splat   $          FShp             F32x4         => v_opcode 19
  | V_splat   $          FShp             F64x2         => v_opcode 20
  | V_compare $   Veq  $ IShp $ Is3 $ Is2 I8x16         => v_opcode 35
  | V_compare $   Vne  $ IShp $ Is3 $ Is2 I8x16         => v_opcode 36
  | V_compare $   Vlt_     Signed   $ Is2 I8x16         => v_opcode 37
  | V_compare $   Vlt_   Unsigned   $ Is2 I8x16         => v_opcode 38
  | V_compare $   Vgt_     Signed   $ Is2 I8x16         => v_opcode 39
  | V_compare $   Vgt_   Unsigned   $ Is2 I8x16         => v_opcode 40
  | V_compare $   Vle_     Signed   $ Is2 I8x16         => v_opcode 41
  | V_compare $   Vle_   Unsigned   $ Is2 I8x16         => v_opcode 42
  | V_compare $   Vge_     Signed   $ Is2 I8x16         => v_opcode 43
  | V_compare $   Vge_   Unsigned   $ Is2 I8x16         => v_opcode 44
  | V_compare $   Veq  $ IShp $ Is3 $ Is2 I16x8         => v_opcode 45
  | V_compare $   Vne  $ IShp $ Is3 $ Is2 I16x8         => v_opcode 46
  | V_compare $   Vlt_     Signed   $ Is2 I16x8         => v_opcode 47
  | V_compare $   Vlt_   Unsigned   $ Is2 I16x8         => v_opcode 48
  | V_compare $   Vgt_     Signed   $ Is2 I16x8         => v_opcode 49
  | V_compare $   Vgt_   Unsigned   $ Is2 I16x8         => v_opcode 50
  | V_compare $   Vle_     Signed   $ Is2 I16x8         => v_opcode 51
  | V_compare $   Vle_   Unsigned   $ Is2 I16x8         => v_opcode 52
  | V_compare $   Vge_     Signed   $ Is2 I16x8         => v_opcode 53
  | V_compare $   Vge_   Unsigned   $ Is2 I16x8         => v_opcode 54
  | V_compare $   Veq  $ IShp $ Is3       I32x4         => v_opcode 55
  | V_compare $   Vne  $ IShp $ Is3       I32x4         => v_opcode 56
  | V_compare $   Vlt_    Signed          I32x4         => v_opcode 57
  | V_compare $   Vlt_  Unsigned          I32x4         => v_opcode 58
  | V_compare $   Vgt_    Signed          I32x4         => v_opcode 59
  | V_compare $   Vgt_  Unsigned          I32x4         => v_opcode 60
  | V_compare $   Vle_    Signed          I32x4         => v_opcode 61
  | V_compare $   Vle_  Unsigned          I32x4         => v_opcode 62
  | V_compare $   Vge_    Signed          I32x4         => v_opcode 63
  | V_compare $   Vge_  Unsigned          I32x4         => v_opcode 64
  | V_compare $   Veq $ IShp              I64x2         => v_opcode 214
  | V_compare $   Vne $ IShp              I64x2         => v_opcode 215
  | V_compare $   Vlt_s                                 => v_opcode 216
  | V_compare $   Vgt_s                                 => v_opcode 217
  | V_compare $   Vle_s                                 => v_opcode 218
  | V_compare $   Vge_s                                 => v_opcode 219
  | V_compare $   Veq  $ FShp             F32x4         => v_opcode 65
  | V_compare $   Vne  $ FShp             F32x4         => v_opcode 66
  | V_compare $   Vlt                     F32x4         => v_opcode 67
  | V_compare $   Vgt                     F32x4         => v_opcode 68
  | V_compare $   Vle                     F32x4         => v_opcode 69
  | V_compare $   Vge                     F32x4         => v_opcode 70
  | V_compare $   Veq  $ FShp             F64x2         => v_opcode 71
  | V_compare $   Vne  $ FShp             F64x2         => v_opcode 72
  | V_compare $   Vlt                     F64x2         => v_opcode 73
  | V_compare $   Vgt                     F64x2         => v_opcode 74
  | V_compare $   Vle                     F64x2         => v_opcode 75
  | V_compare $   Vge                     F64x2         => v_opcode 76
  | V_ternary     VbitSelect                            => v_opcode 77
  | V_binary      Vand                                  => v_opcode 78
  | V_binary      VandNot                               => v_opcode 79
  | V_binary      Vor                                   => v_opcode 80
  | V_binary      Vxor                                  => v_opcode 81
  | V_ternary     VbitSelect                            => v_opcode 82
  | V_test        VanyTrue                              => v_opcode 83
  | V_unary   $   Vabs $ IShp $ Is3 $ Is2 I8x16         => v_opcode 96
  | V_unary   $   Vneg $ IShp $ Is3 $ Is2 I8x16         => v_opcode 97
  | V_unary       Vpopcnt                               => v_opcode 98
  | V_test    $   VallTrue    $ Is3 $ Is2 I8x16         => v_opcode 99
  | V_unary   $   Vbitmask    $ Is3 $ Is2 I8x16         => v_opcode 100
  | V_binary  $   Vnarrow   Signed I8x16                => v_opcode 101
  | V_binary  $   Vnarrow Unsigned I8x16                => v_opcode 102
  | V_shift   $   Vshl           $ Is3 $ Is2 I8x16      => v_opcode 107
  | V_shift   $   Vshr_   Signed $ Is3 $ Is2 I8x16      => v_opcode 108
  | V_shift   $   Vshr_ Unsigned $ Is3 $ Is2 I8x16      => v_opcode 109
  | V_binary  $   Vadd $ IShp $ Is3 $ Is2 I8x16         => v_opcode 110
  | V_binary  $   Vadd_sat_    Signed     I8x16         => v_opcode 111
  | V_binary  $   Vadd_sat_  Unsigned     I8x16         => v_opcode 112
  | V_binary  $   Vsub $ IShp $ Is3 $ Is2 I8x16         => v_opcode 113
  | V_binary  $   Vsub_sat_    Signed     I8x16         => v_opcode 114
  | V_binary  $   Vsub_sat_  Unsigned     I8x16         => v_opcode 115
  | V_binary  $   Vmin_   Signed $ Is2 I8x16            => v_opcode 118
  | V_binary  $   Vmin_ Unsigned $ Is2 I8x16            => v_opcode 119
  | V_binary  $   Vmax_   Signed $ Is2 I8x16            => v_opcode 120
  | V_binary  $   Vmax_ Unsigned $ Is2 I8x16            => v_opcode 121
  | V_binary  $   Vavgr_u I8x16                         => v_opcode 123
  | V_convert $   VextAdd I8x16   Signed                => v_opcode 124
  | V_convert $   VextAdd I8x16 Unsigned                => v_opcode 125
  | V_unary   $   Vabs $ IShp $ Is3 $ Is2 I16x8         => v_opcode 128
  | V_unary   $   Vneg $ IShp $ Is3 $ Is2 I16x8         => v_opcode 129
  | V_binary  $   VmulQ15                               => v_opcode 130
  | V_test    $   VallTrue    $ Is3 $ Is2 I16x8         => v_opcode 131
  | V_unary   $   Vbitmask    $ Is3 $ Is2 I16x8         => v_opcode 132
  | V_binary  $   Vnarrow          Signed I16x8         => v_opcode 133
  | V_binary  $   Vnarrow        Unsigned I16x8         => v_opcode 134
  | V_convert $   Vextend   Low  (Is2 I8x16)   Signed   => v_opcode 135
  | V_convert $   Vextend  High  (Is2 I8x16)   Signed   => v_opcode 136
  | V_convert $   Vextend   Low  (Is2 I8x16) Unsigned   => v_opcode 137
  | V_convert $   Vextend  High  (Is2 I8x16) Unsigned   => v_opcode 138
  | V_shift   $   Vshl           $ Is3 $ Is2 I16x8      => v_opcode 139
  | V_shift   $   Vshr_   Signed $ Is3 $ Is2 I16x8      => v_opcode 140
  | V_shift   $   Vshr_ Unsigned $ Is3 $ Is2 I16x8      => v_opcode 141
  | V_binary  $   Vadd $ IShp $ Is3 $ Is2 I16x8         => v_opcode 142
  | V_binary  $   Vadd_sat_   Signed      I16x8         => v_opcode 143
  | V_binary  $   Vadd_sat_ Unsigned      I16x8         => v_opcode 144
  | V_binary  $   Vsub $ IShp $ Is3 $ Is2 I16x8         => v_opcode 145
  | V_binary  $   Vsub_sat_   Signed      I16x8         => v_opcode 146
  | V_binary  $   Vsub_sat_ Unsigned      I16x8         => v_opcode 147
  | V_binary  $   VmulI16                               => v_opcode 149
  | V_binary  $   Vmin_    Signed   $ Is2 I16x8         => v_opcode 150
  | V_binary  $   Vmin_  Unsigned   $ Is2 I16x8         => v_opcode 151
  | V_binary  $   Vmax_    Signed   $ Is2 I16x8         => v_opcode 152
  | V_binary  $   Vmax_  Unsigned   $ Is2 I16x8         => v_opcode 153
  | V_binary  $   Vavgr_u I16x8                         => v_opcode 155
  | V_convert $   VextMul   Low  (Is2 I8x16)   Signed   => v_opcode 156
  | V_convert $   VextMul  High  (Is2 I8x16)   Signed   => v_opcode 157
  | V_convert $   VextMul   Low  (Is2 I8x16) Unsigned   => v_opcode 158
  | V_convert $   VextMul  High  (Is2 I8x16) Unsigned   => v_opcode 159
  | V_convert $   VextAdd I16x8   Signed                => v_opcode 126
  | V_convert $   VextAdd I16x8 Unsigned                => v_opcode 127
  | V_unary   $   Vabs $ IShp $ Is3 I32x4               => v_opcode 160
  | V_unary   $   Vneg $ IShp $ Is3 I32x4               => v_opcode 161
  | V_test    $   VallTrue    $ Is3 I32x4               => v_opcode 163
  | V_unary   $   Vbitmask    $ Is3 I32x4               => v_opcode 164
  | V_convert $   Vextend   Low  (Is2 I16x8)   Signed   => v_opcode 167
  | V_convert $   Vextend  High  (Is2 I16x8)   Signed   => v_opcode 168
  | V_convert $   Vextend   Low  (Is2 I16x8) Unsigned   => v_opcode 169
  | V_convert $   Vextend  High  (Is2 I16x8) Unsigned   => v_opcode 170
  | V_shift   $   Vshl           (Is3 I32x4)            => v_opcode 171
  | V_shift   $   Vshr_   Signed (Is3 I32x4)            => v_opcode 172
  | V_shift   $   Vshr_ Unsigned (Is3 I32x4)            => v_opcode 173
  | V_binary  $   Vadd $ IShp $ Is3 I32x4               => v_opcode 174
  | V_binary  $   Vsub $ IShp $ Is3 I32x4               => v_opcode 177
  | V_binary  $   VmulI32                               => v_opcode 181
  | V_binary  $   Vmin_   Signed I32x4                  => v_opcode 182
  | V_binary  $   Vmin_ Unsigned I32x4                  => v_opcode 183
  | V_binary  $   Vmax_   Signed I32x4                  => v_opcode 184
  | V_binary  $   Vmax_ Unsigned I32x4                  => v_opcode 185
  | V_binary  $   Vdot                                  => v_opcode 186
  | V_convert $   VextMul   Low  (Is2 I16x8)   Signed   => v_opcode 188
  | V_convert $   VextMul  High  (Is2 I16x8)   Signed   => v_opcode 189
  | V_convert $   VextMul   Low  (Is2 I16x8) Unsigned   => v_opcode 190
  | V_convert $   VextMul  High  (Is2 I16x8) Unsigned   => v_opcode 191
  | V_unary   $   Vabs $ IShp I64x2                     => v_opcode 192
  | V_unary   $   Vneg $ IShp I64x2                     => v_opcode 193
  | V_test    $   VallTrue    I64x2                     => v_opcode 195
  | V_unary   $   Vbitmask    I64x2                     => v_opcode 196
  | V_convert $   Vextend   Low  I32x4    Signed        => v_opcode 199
  | V_convert $   Vextend  High  I32x4    Signed        => v_opcode 200
  | V_convert $   Vextend   Low  I32x4  Unsigned        => v_opcode 201
  | V_convert $   Vextend  High  I32x4  Unsigned        => v_opcode 202
  | V_shift   $   Vshl I64x2                            => v_opcode 203
  | V_shift   $   Vshr_   Signed I64x2                  => v_opcode 204
  | V_shift   $   Vshr_ Unsigned I64x2                  => v_opcode 205
  | V_binary  $   Vadd (IShp I64x2)                     => v_opcode 206
  | V_binary  $   Vsub (IShp I64x2)                     => v_opcode 209
  | V_binary  $   VmulI64                               => v_opcode 213
  | V_convert $   VextMul   Low  I32x4    Signed        => v_opcode 220
  | V_convert $   VextMul  High  I32x4    Signed        => v_opcode 221
  | V_convert $   VextMul   Low  I32x4  Unsigned        => v_opcode 222
  | V_convert $   VextMul  High  I32x4  Unsigned        => v_opcode 223
  | V_unary   $   Vceil       F32x4                     => v_opcode 103
  | V_unary   $   Vfloor      F32x4                     => v_opcode 104
  | V_unary   $   Vtrunc      F32x4                     => v_opcode 105
  | V_unary   $   Vnearest    F32x4                     => v_opcode 106
  | V_unary   $   Vabs $ FShp F32x4                     => v_opcode 224
  | V_unary   $   Vneg $ FShp F32x4                     => v_opcode 225
  | V_unary   $   Vsqrt       F32x4                     => v_opcode 227
  | V_binary  $   Vadd $ FShp F32x4                     => v_opcode 228
  | V_binary  $   Vsub $ FShp F32x4                     => v_opcode 229
  | V_binary  $   VmulF       F32x4                     => v_opcode 230
  | V_binary  $   Vdiv        F32x4                     => v_opcode 231
  | V_binary  $   Vmin        F32x4                     => v_opcode 232
  | V_binary  $   Vmax        F32x4                     => v_opcode 233
  | V_binary  $   Vpmin       F32x4                     => v_opcode 234
  | V_binary  $   Vpmax       F32x4                     => v_opcode 235
  | V_unary   $   Vceil       F64x2                     => v_opcode 116
  | V_unary   $   Vfloor      F64x2                     => v_opcode 117
  | V_unary   $   Vtrunc      F64x2                     => v_opcode 122
  | V_unary   $   Vnearest    F64x2                     => v_opcode 148
  | V_unary   $   Vabs $ FShp F64x2                     => v_opcode 236
  | V_unary   $   Vneg $ FShp F64x2                     => v_opcode 237
  | V_unary   $   Vsqrt       F64x2                     => v_opcode 239
  | V_binary  $   Vadd $ FShp F64x2                     => v_opcode 240
  | V_binary  $   Vsub $ FShp F64x2                     => v_opcode 241
  | V_binary  $   VmulF       F64x2                     => v_opcode 242
  | V_binary  $   Vdiv        F64x2                     => v_opcode 243
  | V_binary  $   Vmin        F64x2                     => v_opcode 244
  | V_binary  $   Vmax        F64x2                     => v_opcode 245
  | V_binary  $   Vpmin       F64x2                     => v_opcode 246
  | V_binary  $   Vpmax       F64x2                     => v_opcode 247
  | V_convert $   VtruncSat          Signed             => v_opcode 248
  | V_convert $   VtruncSat        Unsigned             => v_opcode 249
  | V_convert $   Vconvert   High    Signed             => v_opcode 250
  | V_convert $   Vconvert   High  Unsigned             => v_opcode 251
  | V_convert $   VtruncSat0         Signed             => v_opcode 252
  | V_convert $   VtruncSat0       Unsigned             => v_opcode 253
  | V_convert $   Vconvert    Low    Signed             => v_opcode 254
  | V_convert $   Vconvert    Low  Unsigned             => v_opcode 255
  | V_convert $   Vdemote                               => v_opcode 94
  | V_convert $   Vpromote                              => v_opcode 95

  | V_const (w128: word128)                             => (v_opcode 12) ++ lend w128

  | V_lane   (Vextract_           Signed  I8x16)   lidx => (v_opcode 21) ++ enc_u8 lidx
  | V_lane   (Vextract_         Unsigned  I8x16)   lidx => (v_opcode 22) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp $ Is3 $ Is2 I8x16)   lidx => (v_opcode 23) ++ enc_u8 lidx
  | V_lane   (Vextract_           Signed  I16x8)   lidx => (v_opcode 24) ++ enc_u8 lidx
  | V_lane   (Vextract_         Unsigned  I16x8)   lidx => (v_opcode 25) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp $ Is3 $ Is2 I16x8)   lidx => (v_opcode 26) ++ enc_u8 lidx
  | V_lane    VextractI32x4                        lidx => (v_opcode 27) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp $ Is3       I32x4)   lidx => (v_opcode 28) ++ enc_u8 lidx
  | V_lane    VextractI64x2                        lidx => (v_opcode 29) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp             I64x2)   lidx => (v_opcode 30) ++ enc_u8 lidx
  | V_lane   (VextractF                   F32x4)   lidx => (v_opcode 31) ++ enc_u8 lidx
  | V_lane   (Vreplace $ FShp             F32x4)   lidx => (v_opcode 32) ++ enc_u8 lidx
  | V_lane   (VextractF                   F64x2)   lidx => (v_opcode 33) ++ enc_u8 lidx
  | V_lane   (Vreplace $ FShp             F64x2)   lidx => (v_opcode 34) ++ enc_u8 lidx

  | V_lane (Vshuffle l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 lA lB lC lD lE) lF => (v_opcode 13) ++
  (FLAT $ MAP enc_u8 [l0; l1; l2; l3; l4; l5; l6; l7; l8; l9; lA; lB; lC; lD; lE; lF])

End

Definition dec_vecI_def:
  dec_vecI ([]:byteSeq) : ((mlstring + vec_instr) # byteSeq) = error "[dec_vecI] : Byte sequence unexpectedly empty." [] ∧
  dec_vecI (xFD::bs) = let failure = error "[dec_vecI]" $ xFD::bs in

  if xFD <> 0xFDw ∨ NULL bs then failure else

  case dec_u32 (bs:byteSeq) of NONE => failure | SOME (oc,cs) =>

  if oc =  14w then (INR $ V_binary      Vswizzle                              ,cs) else
  if oc =  15w then (INR $ V_splat   $          IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc =  16w then (INR $ V_splat   $          IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc =  17w then (INR $ V_splat   $          IShp $ Is3       I32x4         ,cs) else
  if oc =  18w then (INR $ V_splat   $          IShp             I64x2         ,cs) else
  if oc =  19w then (INR $ V_splat   $          FShp             F32x4         ,cs) else
  if oc =  20w then (INR $ V_splat   $          FShp             F64x2         ,cs) else
  if oc =  35w then (INR $ V_compare $   Veq  $ IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc =  36w then (INR $ V_compare $   Vne  $ IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc =  37w then (INR $ V_compare $   Vlt_     Signed   $ Is2 I8x16         ,cs) else
  if oc =  38w then (INR $ V_compare $   Vlt_   Unsigned   $ Is2 I8x16         ,cs) else
  if oc =  39w then (INR $ V_compare $   Vgt_     Signed   $ Is2 I8x16         ,cs) else
  if oc =  40w then (INR $ V_compare $   Vgt_   Unsigned   $ Is2 I8x16         ,cs) else
  if oc =  41w then (INR $ V_compare $   Vle_     Signed   $ Is2 I8x16         ,cs) else
  if oc =  42w then (INR $ V_compare $   Vle_   Unsigned   $ Is2 I8x16         ,cs) else
  if oc =  43w then (INR $ V_compare $   Vge_     Signed   $ Is2 I8x16         ,cs) else
  if oc =  44w then (INR $ V_compare $   Vge_   Unsigned   $ Is2 I8x16         ,cs) else
  if oc =  45w then (INR $ V_compare $   Veq  $ IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc =  46w then (INR $ V_compare $   Vne  $ IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc =  47w then (INR $ V_compare $   Vlt_     Signed   $ Is2 I16x8         ,cs) else
  if oc =  48w then (INR $ V_compare $   Vlt_   Unsigned   $ Is2 I16x8         ,cs) else
  if oc =  49w then (INR $ V_compare $   Vgt_     Signed   $ Is2 I16x8         ,cs) else
  if oc =  50w then (INR $ V_compare $   Vgt_   Unsigned   $ Is2 I16x8         ,cs) else
  if oc =  51w then (INR $ V_compare $   Vle_     Signed   $ Is2 I16x8         ,cs) else
  if oc =  52w then (INR $ V_compare $   Vle_   Unsigned   $ Is2 I16x8         ,cs) else
  if oc =  53w then (INR $ V_compare $   Vge_     Signed   $ Is2 I16x8         ,cs) else
  if oc =  54w then (INR $ V_compare $   Vge_   Unsigned   $ Is2 I16x8         ,cs) else
  if oc =  55w then (INR $ V_compare $   Veq $ IShp $ Is3        I32x4         ,cs) else
  if oc =  56w then (INR $ V_compare $   Vne $ IShp $ Is3        I32x4         ,cs) else
  if oc =  57w then (INR $ V_compare $   Vlt_     Signed         I32x4         ,cs) else
  if oc =  58w then (INR $ V_compare $   Vlt_   Unsigned         I32x4         ,cs) else
  if oc =  59w then (INR $ V_compare $   Vgt_     Signed         I32x4         ,cs) else
  if oc =  60w then (INR $ V_compare $   Vgt_   Unsigned         I32x4         ,cs) else
  if oc =  61w then (INR $ V_compare $   Vle_     Signed         I32x4         ,cs) else
  if oc =  62w then (INR $ V_compare $   Vle_   Unsigned         I32x4         ,cs) else
  if oc =  63w then (INR $ V_compare $   Vge_     Signed         I32x4         ,cs) else
  if oc =  64w then (INR $ V_compare $   Vge_   Unsigned         I32x4         ,cs) else
  if oc = 214w then (INR $ V_compare $   Veq $ IShp              I64x2         ,cs) else
  if oc = 215w then (INR $ V_compare $   Vne $ IShp              I64x2         ,cs) else
  if oc = 216w then (INR $ V_compare     Vlt_s                                 ,cs) else
  if oc = 217w then (INR $ V_compare     Vgt_s                                 ,cs) else
  if oc = 218w then (INR $ V_compare     Vle_s                                 ,cs) else
  if oc = 219w then (INR $ V_compare     Vge_s                                 ,cs) else
  if oc =  65w then (INR $ V_compare $   Veq $ FShp              F32x4         ,cs) else
  if oc =  66w then (INR $ V_compare $   Vne $ FShp              F32x4         ,cs) else
  if oc =  67w then (INR $ V_compare $   Vlt                     F32x4         ,cs) else
  if oc =  68w then (INR $ V_compare $   Vgt                     F32x4         ,cs) else
  if oc =  69w then (INR $ V_compare $   Vle                     F32x4         ,cs) else
  if oc =  70w then (INR $ V_compare $   Vge                     F32x4         ,cs) else
  if oc =  71w then (INR $ V_compare $   Veq $ FShp              F64x2         ,cs) else
  if oc =  72w then (INR $ V_compare $   Vne $ FShp              F64x2         ,cs) else
  if oc =  73w then (INR $ V_compare $   Vlt                     F64x2         ,cs) else
  if oc =  74w then (INR $ V_compare $   Vgt                     F64x2         ,cs) else
  if oc =  75w then (INR $ V_compare $   Vle                     F64x2         ,cs) else
  if oc =  76w then (INR $ V_compare $   Vge                     F64x2         ,cs) else
  if oc =  77w then (INR $ V_ternary     VbitSelect                            ,cs) else
  if oc =  78w then (INR $ V_binary      Vand                                  ,cs) else
  if oc =  79w then (INR $ V_binary      VandNot                               ,cs) else
  if oc =  80w then (INR $ V_binary      Vor                                   ,cs) else
  if oc =  81w then (INR $ V_binary      Vxor                                  ,cs) else
  if oc =  82w then (INR $ V_ternary     VbitSelect                            ,cs) else
  if oc =  83w then (INR $ V_test        VanyTrue                              ,cs) else
  if oc =  96w then (INR $ V_unary   $   Vabs $ IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc =  97w then (INR $ V_unary   $   Vneg $ IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc =  98w then (INR $ V_unary       Vpopcnt                               ,cs) else
  if oc =  99w then (INR $ V_test    $   VallTrue    $ Is3 $ Is2 I8x16         ,cs) else
  if oc = 100w then (INR $ V_unary   $   Vbitmask    $ Is3 $ Is2 I8x16         ,cs) else
  if oc = 101w then (INR $ V_binary  $   Vnarrow   Signed I8x16                ,cs) else
  if oc = 102w then (INR $ V_binary  $   Vnarrow Unsigned I8x16                ,cs) else
  if oc = 107w then (INR $ V_shift   $   Vshl           $ Is3 $ Is2 I8x16      ,cs) else
  if oc = 108w then (INR $ V_shift   $   Vshr_   Signed $ Is3 $ Is2 I8x16      ,cs) else
  if oc = 109w then (INR $ V_shift   $   Vshr_ Unsigned $ Is3 $ Is2 I8x16      ,cs) else
  if oc = 110w then (INR $ V_binary  $   Vadd $ IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc = 111w then (INR $ V_binary  $   Vadd_sat_   Signed I8x16              ,cs) else
  if oc = 112w then (INR $ V_binary  $   Vadd_sat_ Unsigned I8x16              ,cs) else
  if oc = 113w then (INR $ V_binary  $   Vsub $ IShp $ Is3 $ Is2 I8x16         ,cs) else
  if oc = 114w then (INR $ V_binary  $   Vsub_sat_   Signed I8x16              ,cs) else
  if oc = 115w then (INR $ V_binary  $   Vsub_sat_ Unsigned I8x16              ,cs) else
  if oc = 118w then (INR $ V_binary  $   Vmin_   Signed (Is2 I8x16)            ,cs) else
  if oc = 119w then (INR $ V_binary  $   Vmin_ Unsigned (Is2 I8x16)            ,cs) else
  if oc = 120w then (INR $ V_binary  $   Vmax_   Signed (Is2 I8x16)            ,cs) else
  if oc = 121w then (INR $ V_binary  $   Vmax_ Unsigned (Is2 I8x16)            ,cs) else
  if oc = 123w then (INR $ V_binary  $   Vavgr_u I8x16                         ,cs) else
  if oc = 124w then (INR $ V_convert $   VextAdd I8x16   Signed                ,cs) else
  if oc = 125w then (INR $ V_convert $   VextAdd I8x16 Unsigned                ,cs) else
  if oc = 128w then (INR $ V_unary   $   Vabs $ IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc = 129w then (INR $ V_unary   $   Vneg $ IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc = 130w then (INR $ V_binary  $   VmulQ15                               ,cs) else
  if oc = 131w then (INR $ V_test    $   VallTrue    $ Is3 $ Is2 I16x8         ,cs) else
  if oc = 132w then (INR $ V_unary   $   Vbitmask    $ Is3 $ Is2 I16x8         ,cs) else
  if oc = 133w then (INR $ V_binary  $   Vnarrow   Signed I16x8                ,cs) else
  if oc = 134w then (INR $ V_binary  $   Vnarrow Unsigned I16x8                ,cs) else
  if oc = 135w then (INR $ V_convert $   Vextend   Low  (Is2 I8x16)   Signed   ,cs) else
  if oc = 136w then (INR $ V_convert $   Vextend  High  (Is2 I8x16)   Signed   ,cs) else
  if oc = 137w then (INR $ V_convert $   Vextend   Low  (Is2 I8x16) Unsigned   ,cs) else
  if oc = 138w then (INR $ V_convert $   Vextend  High  (Is2 I8x16) Unsigned   ,cs) else
  if oc = 139w then (INR $ V_shift   $   Vshl           $ Is3 $ Is2 I16x8      ,cs) else
  if oc = 140w then (INR $ V_shift   $   Vshr_   Signed $ Is3 $ Is2 I16x8      ,cs) else
  if oc = 141w then (INR $ V_shift   $   Vshr_ Unsigned $ Is3 $ Is2 I16x8      ,cs) else
  if oc = 142w then (INR $ V_binary  $   Vadd $ IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc = 143w then (INR $ V_binary  $   Vadd_sat_     Signed    I16x8         ,cs) else
  if oc = 144w then (INR $ V_binary  $   Vadd_sat_   Unsigned    I16x8         ,cs) else
  if oc = 145w then (INR $ V_binary  $   Vsub $ IShp $ Is3 $ Is2 I16x8         ,cs) else
  if oc = 146w then (INR $ V_binary  $   Vsub_sat_     Signed    I16x8         ,cs) else
  if oc = 147w then (INR $ V_binary  $   Vsub_sat_   Unsigned    I16x8         ,cs) else
  if oc = 149w then (INR $ V_binary  $   VmulI16                               ,cs) else
  if oc = 150w then (INR $ V_binary  $   Vmin_   Signed (Is2 I16x8)            ,cs) else
  if oc = 151w then (INR $ V_binary  $   Vmin_ Unsigned (Is2 I16x8)            ,cs) else
  if oc = 152w then (INR $ V_binary  $   Vmax_   Signed (Is2 I16x8)            ,cs) else
  if oc = 153w then (INR $ V_binary  $   Vmax_ Unsigned (Is2 I16x8)            ,cs) else
  if oc = 155w then (INR $ V_binary  $   Vavgr_u I16x8                         ,cs) else
  if oc = 156w then (INR $ V_convert $   VextMul   Low  (Is2 I8x16)   Signed   ,cs) else
  if oc = 157w then (INR $ V_convert $   VextMul  High  (Is2 I8x16)   Signed   ,cs) else
  if oc = 158w then (INR $ V_convert $   VextMul   Low  (Is2 I8x16) Unsigned   ,cs) else
  if oc = 159w then (INR $ V_convert $   VextMul  High  (Is2 I8x16) Unsigned   ,cs) else
  if oc = 126w then (INR $ V_convert $   VextAdd I16x8   Signed                ,cs) else
  if oc = 127w then (INR $ V_convert $   VextAdd I16x8 Unsigned                ,cs) else
  if oc = 160w then (INR $ V_unary   $   Vabs $ IShp $ Is3 I32x4               ,cs) else
  if oc = 161w then (INR $ V_unary   $   Vneg $ IShp $ Is3 I32x4               ,cs) else
  if oc = 163w then (INR $ V_test    $   VallTrue    $ Is3 I32x4               ,cs) else
  if oc = 164w then (INR $ V_unary   $   Vbitmask    $ Is3 I32x4               ,cs) else
  if oc = 167w then (INR $ V_convert $   Vextend   Low  (Is2 I16x8)   Signed   ,cs) else
  if oc = 168w then (INR $ V_convert $   Vextend  High  (Is2 I16x8)   Signed   ,cs) else
  if oc = 169w then (INR $ V_convert $   Vextend   Low  (Is2 I16x8) Unsigned   ,cs) else
  if oc = 170w then (INR $ V_convert $   Vextend  High  (Is2 I16x8) Unsigned   ,cs) else
  if oc = 171w then (INR $ V_shift   $   Vshl           (Is3 I32x4)            ,cs) else
  if oc = 172w then (INR $ V_shift   $   Vshr_   Signed (Is3 I32x4)            ,cs) else
  if oc = 173w then (INR $ V_shift   $   Vshr_ Unsigned (Is3 I32x4)            ,cs) else
  if oc = 174w then (INR $ V_binary  $   Vadd (IShp (Is3 I32x4))               ,cs) else
  if oc = 177w then (INR $ V_binary  $   Vsub (IShp (Is3 I32x4))               ,cs) else
  if oc = 181w then (INR $ V_binary  $   VmulI32                               ,cs) else
  if oc = 182w then (INR $ V_binary  $   Vmin_   Signed I32x4                  ,cs) else
  if oc = 183w then (INR $ V_binary  $   Vmin_ Unsigned I32x4                  ,cs) else
  if oc = 184w then (INR $ V_binary  $   Vmax_   Signed I32x4                  ,cs) else
  if oc = 185w then (INR $ V_binary  $   Vmax_ Unsigned I32x4                  ,cs) else
  if oc = 186w then (INR $ V_binary  $   Vdot                                  ,cs) else
  if oc = 188w then (INR $ V_convert $   VextMul   Low  (Is2 I16x8)   Signed   ,cs) else
  if oc = 189w then (INR $ V_convert $   VextMul  High  (Is2 I16x8)   Signed   ,cs) else
  if oc = 190w then (INR $ V_convert $   VextMul   Low  (Is2 I16x8) Unsigned   ,cs) else
  if oc = 191w then (INR $ V_convert $   VextMul  High  (Is2 I16x8) Unsigned   ,cs) else
  if oc = 192w then (INR $ V_unary   $   Vabs $ IShp I64x2                     ,cs) else
  if oc = 193w then (INR $ V_unary   $   Vneg $ IShp I64x2                     ,cs) else
  if oc = 195w then (INR $ V_test    $   VallTrue    I64x2                     ,cs) else
  if oc = 196w then (INR $ V_unary   $   Vbitmask    I64x2                     ,cs) else
  if oc = 199w then (INR $ V_convert $   Vextend   Low  I32x4    Signed        ,cs) else
  if oc = 200w then (INR $ V_convert $   Vextend  High  I32x4    Signed        ,cs) else
  if oc = 201w then (INR $ V_convert $   Vextend   Low  I32x4  Unsigned        ,cs) else
  if oc = 202w then (INR $ V_convert $   Vextend  High  I32x4  Unsigned        ,cs) else
  if oc = 203w then (INR $ V_shift   $   Vshl             I64x2                ,cs) else
  if oc = 204w then (INR $ V_shift   $   Vshr_    Signed  I64x2                ,cs) else
  if oc = 205w then (INR $ V_shift   $   Vshr_  Unsigned  I64x2                ,cs) else
  if oc = 206w then (INR $ V_binary  $   Vadd (IShp I64x2)                     ,cs) else
  if oc = 209w then (INR $ V_binary  $   Vsub (IShp I64x2)                     ,cs) else
  if oc = 213w then (INR $ V_binary  $   VmulI64                               ,cs) else
  if oc = 220w then (INR $ V_convert $   VextMul   Low  I32x4   Signed         ,cs) else
  if oc = 221w then (INR $ V_convert $   VextMul  High  I32x4   Signed         ,cs) else
  if oc = 222w then (INR $ V_convert $   VextMul   Low  I32x4 Unsigned         ,cs) else
  if oc = 223w then (INR $ V_convert $   VextMul  High  I32x4 Unsigned         ,cs) else
  if oc = 103w then (INR $ V_unary   $   Vceil       F32x4                     ,cs) else
  if oc = 104w then (INR $ V_unary   $   Vfloor      F32x4                     ,cs) else
  if oc = 105w then (INR $ V_unary   $   Vtrunc      F32x4                     ,cs) else
  if oc = 106w then (INR $ V_unary   $   Vnearest    F32x4                     ,cs) else
  if oc = 224w then (INR $ V_unary   $   Vabs $ FShp F32x4                     ,cs) else
  if oc = 225w then (INR $ V_unary   $   Vneg $ FShp F32x4                     ,cs) else
  if oc = 227w then (INR $ V_unary   $   Vsqrt       F32x4                     ,cs) else
  if oc = 228w then (INR $ V_binary  $   Vadd $ FShp F32x4                     ,cs) else
  if oc = 229w then (INR $ V_binary  $   Vsub $ FShp F32x4                     ,cs) else
  if oc = 230w then (INR $ V_binary  $   VmulF       F32x4                     ,cs) else
  if oc = 231w then (INR $ V_binary  $   Vdiv        F32x4                     ,cs) else
  if oc = 232w then (INR $ V_binary  $   Vmin        F32x4                     ,cs) else
  if oc = 233w then (INR $ V_binary  $   Vmax        F32x4                     ,cs) else
  if oc = 234w then (INR $ V_binary  $   Vpmin       F32x4                     ,cs) else
  if oc = 235w then (INR $ V_binary  $   Vpmax       F32x4                     ,cs) else
  if oc = 116w then (INR $ V_unary   $   Vceil       F64x2                     ,cs) else
  if oc = 117w then (INR $ V_unary   $   Vfloor      F64x2                     ,cs) else
  if oc = 122w then (INR $ V_unary   $   Vtrunc      F64x2                     ,cs) else
  if oc = 148w then (INR $ V_unary   $   Vnearest    F64x2                     ,cs) else
  if oc = 236w then (INR $ V_unary   $   Vabs $ FShp F64x2                     ,cs) else
  if oc = 237w then (INR $ V_unary   $   Vneg $ FShp F64x2                     ,cs) else
  if oc = 239w then (INR $ V_unary   $   Vsqrt       F64x2                     ,cs) else
  if oc = 240w then (INR $ V_binary  $   Vadd $ FShp F64x2                     ,cs) else
  if oc = 241w then (INR $ V_binary  $   Vsub $ FShp F64x2                     ,cs) else
  if oc = 242w then (INR $ V_binary  $   VmulF       F64x2                     ,cs) else
  if oc = 243w then (INR $ V_binary  $   Vdiv        F64x2                     ,cs) else
  if oc = 244w then (INR $ V_binary  $   Vmin        F64x2                     ,cs) else
  if oc = 245w then (INR $ V_binary  $   Vmax        F64x2                     ,cs) else
  if oc = 246w then (INR $ V_binary  $   Vpmin       F64x2                     ,cs) else
  if oc = 247w then (INR $ V_binary  $   Vpmax       F64x2                     ,cs) else
  if oc = 248w then (INR $ V_convert $   VtruncSat           Signed            ,cs) else
  if oc = 249w then (INR $ V_convert $   VtruncSat         Unsigned            ,cs) else
  if oc = 250w then (INR $ V_convert $   Vconvert    High    Signed            ,cs) else
  if oc = 251w then (INR $ V_convert $   Vconvert    High  Unsigned            ,cs) else
  if oc = 252w then (INR $ V_convert $   VtruncSat0          Signed            ,cs) else
  if oc = 253w then (INR $ V_convert $   VtruncSat0        Unsigned            ,cs) else
  if oc = 254w then (INR $ V_convert $   Vconvert     Low    Signed            ,cs) else
  if oc = 255w then (INR $ V_convert $   Vconvert     Low  Unsigned            ,cs) else
  if oc =  94w then (INR $ V_convert    Vdemote                                ,cs) else
  if oc =  95w then (INR $ V_convert    Vpromote                               ,cs) else

  if oc=12w then case unlend cs of NONE => failure | SOME (w128, ds) => (INR $ V_const w128,ds) else

  if oc=21w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vextract_            Signed I8x16)  lidx,ds) else
  if oc=22w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vextract_          Unsigned I8x16)  lidx,ds) else
  if oc=23w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vreplace $ IShp $ Is3 $ Is2 I8x16)  lidx,ds) else
  if oc=24w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vextract_            Signed I16x8)  lidx,ds) else
  if oc=25w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vextract_          Unsigned I16x8)  lidx,ds) else
  if oc=26w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vreplace $ IShp $ Is3 $ Is2 I16x8)  lidx,ds) else
  if oc=27w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane   VextractI32x4                       lidx,ds) else
  if oc=28w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vreplace $ IShp $ Is3       I32x4)  lidx,ds) else
  if oc=29w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane   VextractI64x2                       lidx,ds) else
  if oc=30w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vreplace $ IShp             I64x2)  lidx,ds) else
  if oc=31w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (VextractF                   F32x4)  lidx,ds) else
  if oc=32w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vreplace $ FShp             F32x4)  lidx,ds) else
  if oc=33w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (VextractF                   F64x2)  lidx,ds) else
  if oc=34w then case dec_u8 cs of NONE => failure | SOME (lidx,ds) => (INR $ V_lane  (Vreplace $ FShp             F64x2)  lidx,ds) else

  if oc=13w then case dec_u8 cs of NONE => failure | SOME (l0,cs) => (* there's gotta be a better way to do this *)
                 case dec_u8 cs of NONE => failure | SOME (l1,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l2,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l3,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l4,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l5,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l6,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l7,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l8,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (l9,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (lA,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (lB,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (lC,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (lD,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (lE,cs) =>
                 case dec_u8 cs of NONE => failure | SOME (lF,ds) =>
  (INR $ V_lane (Vshuffle l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 lA lB lC lD lE) lF ,ds) else

  failure
End



Definition enc_loadI_def:
  enc_loadI (i:load_instr) : byteSeq = case i of
  | Load    Int                  W32 ofs al  => 0x28w :: enc_2u32 al ofs
  | Load    Int                  W64 ofs al  => 0x29w :: enc_2u32 al ofs
  | Load  Float                  W32 ofs al  => 0x2Aw :: enc_2u32 al ofs
  | Load  Float                  W64 ofs al  => 0x2Bw :: enc_2u32 al ofs
  | LoadNarrow I8x16    Signed   W32 ofs al  => 0x2Cw :: enc_2u32 al ofs
  | LoadNarrow I8x16  Unsigned   W32 ofs al  => 0x2Dw :: enc_2u32 al ofs
  | LoadNarrow I16x8    Signed   W32 ofs al  => 0x2Ew :: enc_2u32 al ofs
  | LoadNarrow I16x8  Unsigned   W32 ofs al  => 0x2Fw :: enc_2u32 al ofs
  | LoadNarrow I8x16    Signed   W64 ofs al  => 0x30w :: enc_2u32 al ofs
  | LoadNarrow I8x16  Unsigned   W64 ofs al  => 0x31w :: enc_2u32 al ofs
  | LoadNarrow I16x8    Signed   W64 ofs al  => 0x32w :: enc_2u32 al ofs
  | LoadNarrow I16x8  Unsigned   W64 ofs al  => 0x33w :: enc_2u32 al ofs
  | LoadNarrow32        Signed       ofs al  => 0x34w :: enc_2u32 al ofs
  | LoadNarrow32      Unsigned       ofs al  => 0x35w :: enc_2u32 al ofs
  | Load128                          ofs al  => 0xFDw :: enc_u32  0w ++ enc_2u32 al ofs
  | LoadHalf  (Is2 I16x8)    Signed  ofs al  => 0xFDw :: enc_u32  1w ++ enc_2u32 al ofs
  | LoadHalf  (Is2 I16x8)  Unsigned  ofs al  => 0xFDw :: enc_u32  2w ++ enc_2u32 al ofs
  | LoadHalf  (Is2 I8x16)    Signed  ofs al  => 0xFDw :: enc_u32  3w ++ enc_2u32 al ofs
  | LoadHalf  (Is2 I8x16)  Unsigned  ofs al  => 0xFDw :: enc_u32  4w ++ enc_2u32 al ofs
  | LoadHalf  (    I32x4)    Signed  ofs al  => 0xFDw :: enc_u32  5w ++ enc_2u32 al ofs
  | LoadHalf  (    I32x4)  Unsigned  ofs al  => 0xFDw :: enc_u32  6w ++ enc_2u32 al ofs
  | LoadSplat (Is3 $ Is2 I16x8)      ofs al  => 0xFDw :: enc_u32  7w ++ enc_2u32 al ofs
  | LoadSplat (Is3 $ Is2 I8x16)      ofs al  => 0xFDw :: enc_u32  8w ++ enc_2u32 al ofs
  | LoadSplat (Is3 $     I32x4)      ofs al  => 0xFDw :: enc_u32  9w ++ enc_2u32 al ofs
  | LoadSplat (          I64x2)      ofs al  => 0xFDw :: enc_u32 10w ++ enc_2u32 al ofs
  | LoadZero                     W32 ofs al  => 0xFDw :: enc_u32 92w ++ enc_2u32 al ofs
  | LoadZero                     W64 ofs al  => 0xFDw :: enc_u32 93w ++ enc_2u32 al ofs
  | LoadLane  (Is3 $ Is2 I16x8) ofs al lidx  => 0xFDw :: enc_u32 84w ++ enc_2u32_u8 al ofs lidx
  | LoadLane  (Is3 $ Is2 I8x16) ofs al lidx  => 0xFDw :: enc_u32 85w ++ enc_2u32_u8 al ofs lidx
  | LoadLane  (Is3 $     I32x4) ofs al lidx  => 0xFDw :: enc_u32 86w ++ enc_2u32_u8 al ofs lidx
  | LoadLane  (          I64x2) ofs al lidx  => 0xFDw :: enc_u32 87w ++ enc_2u32_u8 al ofs lidx
End

Definition dec_loadI_def:
  dec_loadI ([]:byteSeq) : ((mlstring + load_instr) # byteSeq) = error "[dec_loadI] : Byte sequence unexpectedly empty." [] ∧
  dec_loadI (b::bs) = let failure = error "[dec_loadI]" $ b::bs in

  if b = 0x28w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   Load    Int                  W32 ofs al,rs) else
  if b = 0x29w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   Load    Int                  W64 ofs al,rs) else
  if b = 0x2Aw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   Load  Float                  W32 ofs al,rs) else
  if b = 0x2Bw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   Load  Float                  W64 ofs al,rs) else
  if b = 0x2Cw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I8x16    Signed   W32 ofs al,rs) else
  if b = 0x2Dw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I8x16  Unsigned   W32 ofs al,rs) else
  if b = 0x2Ew then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I16x8    Signed   W32 ofs al,rs) else
  if b = 0x2Fw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I16x8  Unsigned   W32 ofs al,rs) else
  if b = 0x30w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I8x16    Signed   W64 ofs al,rs) else
  if b = 0x31w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I8x16  Unsigned   W64 ofs al,rs) else
  if b = 0x32w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I16x8    Signed   W64 ofs al,rs) else
  if b = 0x33w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow I16x8  Unsigned   W64 ofs al,rs) else
  if b = 0x34w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow32        Signed       ofs al,rs) else
  if b = 0x35w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   LoadNarrow32      Unsigned       ofs al,rs) else
  if b = 0xFDw then case dec_u32 bs of NONE=>failure| SOME (oc, cs) =>
    if oc =  0w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ Load128                          ofs al,rs)) else
    if oc =  1w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadHalf  (Is2 I16x8)    Signed  ofs al,rs)) else
    if oc =  2w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadHalf  (Is2 I16x8)  Unsigned  ofs al,rs)) else
    if oc =  3w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadHalf  (Is2 I8x16)    Signed  ofs al,rs)) else
    if oc =  4w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadHalf  (Is2 I8x16)  Unsigned  ofs al,rs)) else
    if oc =  5w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadHalf  (    I32x4)    Signed  ofs al,rs)) else
    if oc =  6w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadHalf  (    I32x4)  Unsigned  ofs al,rs)) else
    if oc =  7w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadSplat (Is3 $ Is2 I16x8)      ofs al,rs)) else
    if oc =  8w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadSplat (Is3 $ Is2 I8x16)      ofs al,rs)) else
    if oc =  9w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadSplat (Is3 $     I32x4)      ofs al,rs)) else
    if oc = 10w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadSplat (          I64x2)      ofs al,rs)) else
    if oc = 92w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadZero                     W32 ofs al,rs)) else
    if oc = 93w then (case dec_2u32 cs of NONE=>failure|SOME (al,ofs,rs) => (INR $ LoadZero                     W64 ofs al,rs)) else

    if oc = 84w then (case dec_2u32_u8 cs of NONE=>failure|SOME (al,ofs,lidx,rs) => (INR $ LoadLane (Is3 $ Is2 I16x8) ofs al lidx,rs)) else
    if oc = 85w then (case dec_2u32_u8 cs of NONE=>failure|SOME (al,ofs,lidx,rs) => (INR $ LoadLane (Is3 $ Is2 I8x16) ofs al lidx,rs)) else
    if oc = 86w then (case dec_2u32_u8 cs of NONE=>failure|SOME (al,ofs,lidx,rs) => (INR $ LoadLane (Is3 $     I32x4) ofs al lidx,rs)) else
    if oc = 87w then (case dec_2u32_u8 cs of NONE=>failure|SOME (al,ofs,lidx,rs) => (INR $ LoadLane (          I64x2) ofs al lidx,rs)) else
    failure
  else
  failure
End

(* ASKYK ASKMM *)
(* this is super slow. How to speed up *)
Theorem dec_enc_loadI:
  ∀ i. dec_loadI (enc_loadI i ++ rest) = (INR i, rest)
Proof
  cheat
  (* rw [enc_loadI_def] >> every_case_tac
  >> rw [dec_loadI_def]
  >> (rewrite_tac[GSYM APPEND_ASSOC] >- rw[]) *)
QED


(*-----------------------------------------------------------------------------------------------------------------------------------------------------------*)


Definition enc_storeI_def:
  enc_storeI (i:store_instr) : byteSeq = case i of
  | Store   Int                  W32 ofs al => 0x36w :: enc_2u32 al ofs
  | Store   Int                  W64 ofs al => 0x37w :: enc_2u32 al ofs
  | Store Float                  W32 ofs al => 0x38w :: enc_2u32 al ofs
  | Store Float                  W64 ofs al => 0x39w :: enc_2u32 al ofs
  | StoreNarrow I8x16            W32 ofs al => 0x3Aw :: enc_2u32 al ofs
  | StoreNarrow I16x8            W32 ofs al => 0x3Bw :: enc_2u32 al ofs
  | StoreNarrow I8x16            W64 ofs al => 0x3Cw :: enc_2u32 al ofs
  | StoreNarrow I16x8            W64 ofs al => 0x3Dw :: enc_2u32 al ofs
  | StoreNarrow32                    ofs al => 0x3Ew :: enc_2u32 al ofs
  | Store128                         ofs al => 0xFDw :: enc_u32 11w ++ enc_2u32 al ofs
  | StoreLane (Is3 $ Is2 I16x8) ofs al lidx => 0xFDw :: enc_u32 88w ++ enc_2u32_u8 al ofs lidx
  | StoreLane (Is3 $ Is2 I8x16) ofs al lidx => 0xFDw :: enc_u32 89w ++ enc_2u32_u8 al ofs lidx
  | StoreLane (Is3 $     I32x4) ofs al lidx => 0xFDw :: enc_u32 90w ++ enc_2u32_u8 al ofs lidx
  | StoreLane (          I64x2) ofs al lidx => 0xFDw :: enc_u32 91w ++ enc_2u32_u8 al ofs lidx
End

Overload i16x8 = “Is3 $ Is2 I16x8”
Overload i8x16 = “Is3 $ Is2 I8x16”
Overload i32x4 = “Is3       I32x4”
Overload i64x2 = “          I64x2”

Definition dec_storeI_def:
  dec_storeI ([]:byteSeq) : ((mlstring + store_instr) # byteSeq) = error "[dec_storeI] : Byte sequence unexpectedly empty." [] ∧
  dec_storeI (b::bs) = let failure = error "[dec_storeI]" $ b::bs in

  if b = 0x36w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store          Int  W32 ofs al,rs) else
  if b = 0x37w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store          Int  W64 ofs al,rs) else
  if b = 0x38w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store        Float  W32 ofs al,rs) else
  if b = 0x39w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store        Float  W64 ofs al,rs) else
  if b = 0x3Aw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W32 ofs al,rs) else
  if b = 0x3Bw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W32 ofs al,rs) else
  if b = 0x3Cw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W64 ofs al,rs) else
  if b = 0x3Dw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W64 ofs al,rs) else
  if b = 0x3Ew then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow32           ofs al,rs) else
  if b = 0xFDw then case dec_u32  bs of NONE=>failure| SOME (oc,cs) =>
    if oc= 11w then case dec_2u32    cs of NONE=>failure| SOME (al,ofs     ,rs) => (INR $ Store128        ofs al     ,rs) else
    if oc= 88w then case dec_2u32_u8 cs of NONE=>failure| SOME (al,ofs,lidx,rs) => (INR $ StoreLane i16x8 ofs al lidx,rs) else
    if oc= 89w then case dec_2u32_u8 cs of NONE=>failure| SOME (al,ofs,lidx,rs) => (INR $ StoreLane i8x16 ofs al lidx,rs) else
    if oc= 90w then case dec_2u32_u8 cs of NONE=>failure| SOME (al,ofs,lidx,rs) => (INR $ StoreLane i32x4 ofs al lidx,rs) else
    if oc= 91w then case dec_2u32_u8 cs of NONE=>failure| SOME (al,ofs,lidx,rs) => (INR $ StoreLane i64x2 ofs al lidx,rs) else
    failure
  else
  failure
End



Definition enc_memI_def:
  enc_memI (i:mem_others) : byteSeq = case i of
  | MemorySize      =>[0x3Fw ;zeroB]
  | MemoryGrow      =>[0x40w ;zeroB]
  | MemoryInit didx => 0xFCw :: enc_u32  8w ++ enc_u32 didx ++ [zeroB]
  | DataDrop   didx => 0xFCw :: enc_u32  9w ++ enc_u32 didx
  | MemoryCopy      => 0xFCw :: enc_u32 10w ++          [zeroB; zeroB]
  | MemoryFill      => 0xFCw :: enc_u32 11w ++                 [zeroB]
End

Definition dec_memI_def:
  dec_memI ([]:byteSeq) : ((mlstring + mem_others) # byteSeq) = error "[dec_memI] : Byte sequence unexpectedly empty." [] ∧
  dec_memI (b::nxt::bs) = let failure = error "[dec_memI]" $ b::nxt::bs in

  if b = 0x3Fw ∧ B0 nxt then (INR MemorySize, bs) else
  if b = 0x40w ∧ B0 nxt then (INR MemoryGrow, bs) else
  if b = 0xFCw then case dec_u32 $ nxt::bs of NONE=>failure| SOME (oc,cs) =>
    if oc =  8w then case dec_u32 cs of NONE=>failure| SOME (didx,z::rst) => if B0 z then (INR $ MemoryInit didx,rst) else failure else
    if oc =  9w then case dec_u32 cs of NONE=>failure| SOME (didx,   rst) =>              (INR $ DataDrop   didx,rst)              else
    if oc = 10w then case cs of z::n::rst => if B0 $ n+z then (INR   MemoryCopy     ,rst) else failure | _ => failure              else
    if oc = 11w then case cs of z::   rst => if B0     z then (INR   MemoryFill     ,rst) else failure | _ => failure              else
    failure
  else
  failure
End

(* ASKYK ASKMMM *)
Theorem dec_enc_memI:
  ∀ i. dec_memI (enc_memI i ++ rest) = (INR i, rest)
Proof
  rw [enc_memI_def] >> every_case_tac
  >- rw [dec_memI_def]              (* MemorySize *)
  >- rw [dec_memI_def]              (* MemoryGrow *)

  (* I don't understand why the following doesn't work
     on the MemoryFill case. I assume it has something to
     do with the way I encoded dec_memI *)
  >> rw[] (* to massage the list from   e :: (xs ++ ys) ++ zs
                                   to   e :: xs ++ ys ++ zs *)
  >> rewrite_tac [GSYM APPEND_ASSOC]
  >> fs[oneline dec_memI_def]    (* this does nothing - but I don't know enough to be surprised *)
  >> rw [dec_memI_def]           (* this does nothing - I thought it should have... *)
  >> cheat
QED


(*-----------------------------------------------------------------------------------------------------------------------------------------------------------*)


Definition enc_paraI_def:
  enc_paraI (i:para_instr) : byteSeq = case i of
  | Drop   => [0x1Aw]
  | Select => [0x1Bw]
End

Definition dec_paraI_def:
  dec_paraI ([]:byteSeq) : ((mlstring + para_instr) # byteSeq) = error "[dec_paraI] : Byte sequence unexpectedly empty." [] ∧
  dec_paraI (b::bs) = let failure = error "[dec_paraI]" $ b::bs in

  if b = 0x1Aw then (INR Drop  , bs) else
  if b = 0x1Bw then (INR Select, bs) else
  failure
End



Definition enc_varI_def:
  enc_varI (i:var_instr) : byteSeq = case i of
  | LocalGet  x => 0x20w :: enc_unsigned_word x
  | LocalSet  x => 0x21w :: enc_unsigned_word x
  | LocalTee  x => 0x22w :: enc_unsigned_word x
  | GlobalGet x => 0x23w :: enc_unsigned_word x
  | GlobalSet x => 0x24w :: enc_unsigned_word x
End

Definition dec_varI_def:
  dec_varI ([]:byteSeq) : ((mlstring + var_instr) # byteSeq) = error "[dec_varI] : Byte sequence unexpectedly empty." [] ∧
  dec_varI (b::bs) = let failure = error "[dec_varI]" $ b::bs in

  if b = 0x20w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalGet  x,rs) else
  if b = 0x21w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalSet  x,rs) else
  if b = 0x22w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalTee  x,rs) else
  if b = 0x23w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ GlobalGet x,rs) else
  if b = 0x24w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ GlobalSet x,rs) else

  failure
End



Definition enc_tableI_def:
  enc_tableI (i:table_instr) : byteSeq = case i of
  | TableSet  x   => 0x25w :: enc_u32 x
  | TableGet  x   => 0x26w :: enc_u32 x
  | TableSize x   => 0xFCw :: enc_u32 12w ++ enc_u32    x
  | TableGrow x   => 0xFCw :: enc_u32 13w ++ enc_u32    x
  | TableFill x   => 0xFCw :: enc_u32 14w ++ enc_u32    x
  | TableCopy x y => 0xFCw :: enc_u32 15w ++ enc_2u32 y x
  | TableInit x y => 0xFCw :: enc_u32 16w ++ enc_2u32 y x
  | Elemdrop  x   => 0xFCw :: enc_u32 17w ++ enc_u32    x
End

Definition dec_tableI_def:
  dec_tableI ([]:byteSeq) : ((mlstring + table_instr) # byteSeq) = error "[dec_tableI] : Byte sequence unexpectedly empty." [] ∧
  dec_tableI (b::bs) = let failure = error "[dec_tableI]" $ b::bs in

  if b = 0x25w then  case dec_u32  bs of NONE=>failure| SOME (x,rs) => (INR $ TableSet  x,rs) else
  if b = 0x26w then  case dec_u32  bs of NONE=>failure| SOME (x,rs) => (INR $ TableGet  x,rs) else
  if b = 0xFCw then  case dec_u32  bs of NONE=>failure| SOME (oc,cs) =>
    if oc = 12w then case dec_u32  cs of NONE=>failure| SOME (  x,rs) => (INR $ TableSize x  ,rs) else
    if oc = 13w then case dec_u32  cs of NONE=>failure| SOME (  x,rs) => (INR $ TableGrow x  ,rs) else
    if oc = 14w then case dec_u32  cs of NONE=>failure| SOME (  x,rs) => (INR $ TableFill x  ,rs) else
    if oc = 15w then case dec_2u32 cs of NONE=>failure| SOME (y,x,rs) => (INR $ TableCopy x y,rs) else
    if oc = 16w then case dec_2u32 cs of NONE=>failure| SOME (y,x,rs) => (INR $ TableInit x y,rs) else
    if oc = 17w then case dec_u32  cs of NONE=>failure| SOME (  x,rs) => (INR $ Elemdrop  x  ,rs) else
    failure
  else
  failure
End

(* ASKYK ASKMMM *)
(* I myself don't know how to improve this
   but surely it can be improved *)
Theorem dec_enc_tableI:
  ∀ i. dec_tableI (enc_tableI i ++ rest) = (INR i, rest)
Proof
  rw[enc_tableI_def] >> every_case_tac

  >- rw[dec_tableI_def, dec_enc_unsigned_word]

  >- rw[dec_tableI_def, dec_enc_unsigned_word]

  >> (rw[dec_tableI_def]
  >> rewrite_tac[GSYM APPEND_ASSOC]
  >> rw[dec_enc_unsigned_word])

  >> rw[dec_enc_unsigned_word, dec_enc_2u32]
QED


(*-----------------------------------------------------------------------------------------------------------------------------------------------------------*)


(***********************************)
(*                                 *)
(*     Decode--Encode Theorems     *)
(*                                 *)
(***********************************)



Theorem dec_enc_valtype:
  ∀ t. dec_valtype (enc_valtype t) = SOME t
Proof
  rpt strip_tac (* this is like intros *)
  >> `? val. enc_valtype t = val` by simp []
  >> asm_rewrite_tac[]
  >> pop_assum mp_tac
  >> rewrite_tac[enc_valtype_def]
  >> simp[AllCaseEqs()]
  >> rpt strip_tac (* this is like intros *)
  >> gvs[dec_valtype_def]
QED

Theorem dec_enc_valtype_redux:
  ∀ t. dec_valtype (enc_valtype t) = SOME t
Proof
  rw[enc_valtype_def] >> every_case_tac >> rw[dec_valtype_def]
QED

Theorem dec_enc_vecI:
  ∀ i. dec_vecI (enc_vecI i ++ rest) = (INR i, rest)
Proof
  cheat
  (* try this when I know how to speed up dec_enc_numI *)
QED

Theorem dec_enc_storeI:
  ∀ i. dec_storeI (enc_storeI i ++ rest) = (INR i, rest)
Proof
  rw[enc_storeI_def] >> every_case_tac
  >> rw[dec_storeI_def]
  >> (rewrite_tac[GSYM APPEND_ASSOC] >- rw[])
QED

Theorem dec_enc_paraI:
  ∀ i. dec_paraI (enc_paraI i ++ rest) = (INR i, rest)
Proof
  rw[enc_paraI_def] >> every_case_tac >>
  rw[dec_paraI_def]
QED

Theorem dec_enc_varI:
  ∀ i. dec_varI (enc_varI i ++ rest) = (INR i, rest)
Proof
  rw[enc_varI_def] >> every_case_tac >>
  rw[dec_varI_def, dec_enc_unsigned_word]
QED


(***************)
(*             *)
(*     WIP     *)
(*             *)
(***************)




(* TODO *)
Definition enc_blocktype_def:
  enc_blocktype = ARB
End
Definition dec_blocktype_def:
  dec_blocktype = ARB
End

Theorem dec_enc_blocktype:
  ∀b rest. dec_blocktype (enc_blocktype b ++ rest) = (INR b, rest)
Proof
  cheat
QED

Definition enc_vec_def:
  enc_vec = ARB
End
Definition dec_vec_def:
  dec_vec = ARB
End
Definition enc_fsig_def:
  enc_fsig = ARB
End
Definition dec_fsig_def:
  dec_fsig = ARB
End

Definition enc_instr_def:

  (enc_instr (inst:instr) : byteSeq = case inst of

  (* control instructions *)
  | Unreachable => [zeroB]
  | Nop         => [0x01w]

  | Block bTyp body => 0x02w :: enc_blocktype bTyp ++ enc_instr_list body ++ [endB]
  | Loop  bTyp body => 0x03w :: enc_blocktype bTyp ++ enc_instr_list body ++ [endB]
  | If    bTyp bodyTh bodyEl => 0x04w :: enc_blocktype bTyp ++
      enc_instr_list bodyTh ++
        (if NULL bodyEl then [endB] else elseB :: enc_instr_list bodyEl ++ [endB])

  | Br           lbl => 0x0Cw ::                    enc_unsigned_word lbl
  | BrIf         lbl => 0x0Dw ::                    enc_unsigned_word lbl
  | BrTable lbls lbl => 0x0Ew :: (* TODO lbls ++ *) enc_unsigned_word lbl

  | Return                    => [0x0Fw]
  | Call               f      =>  0x10w :: enc_unsigned_word f
  | CallIndirect       f fsig =>  0x11w :: enc_fsig fsig ++ enc_unsigned_word f
  | ReturnCall         f      =>  0x12w :: enc_unsigned_word f
  | ReturnCallIndirect f fsig =>  0x13w :: enc_fsig fsig ++ enc_unsigned_word f

  (* other classes of instructions *)
  | Variable   i => enc_varI   i
  | Parametric i => enc_paraI  i
  | Numeric    i => enc_numI   i
  | Vector     i => enc_vecI   i
  | MemRead    i => enc_loadI  i
  | MemWrite   i => enc_storeI i
  | MemOthers  i => enc_memI   i
  | _ => []
  ) ∧

  (enc_instr_list ([]:instr list) : byteSeq = [endB]) ∧
  (enc_instr_list (i::ins) = enc_instr i ++ enc_instr_list ins)

End

Theorem dec_blocktype_len:
  dec_blocktype bs = (r,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs
Proof
  cheat
QED

Definition check_len_def:
  (check_len bs (INR x,bs1) =
    if LENGTH bs1 < LENGTH bs then (INR x,bs1) else (INR x,[])) ∧
  (check_len bs (INL x,bs1) =
    if LENGTH bs1 ≤ LENGTH bs then (INL x,bs1) else (INL x,bs))
End

Theorem check_len_IMP:
  check_len bs xs = (INR x,bs1) ⇒
  (LENGTH bs1 ≤ LENGTH bs) ∧
  (bs ≠ [] ⇒ LENGTH bs1 < LENGTH bs)
Proof
  PairCases_on ‘xs’ \\ rw [check_len_def]
  \\ Cases_on ‘xs0’ \\ gvs [check_len_def,AllCaseEqs()]
  \\ fs [] \\ Cases_on ‘bs’ \\ fs []
QED

Theorem check_len_IMP_INL:
  check_len bs xs = (INL x,bs1) ⇒
  (LENGTH bs1 ≤ LENGTH bs)
Proof
  PairCases_on ‘xs’ \\ rw [check_len_def]
  \\ Cases_on ‘xs0’ \\ gvs [check_len_def,AllCaseEqs()]
QED

Definition dec_instr_def:
  (dec_instr ([]:byteSeq) : ((mlstring + instr) # byteSeq) =
     error "[dec_instr] : Byte sequence unexpectedly empty." []) ∧
  (dec_instr (b::bs) =
     if b = zeroB then (INR Unreachable, bs) else
     if b = 0x01w then (INR Nop, bs) else
     if b = 0x02w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
        case bs of
        | [] => error "[dec_instr] : Byte sequence unexpectedly empty." []
        | (b::bs) =>
          if b = 0x0Bw then
            (INR (Block bTyp body),bs)
          else
            error "[dec_instr] : Byte sequence unexpectedly empty." []) else
     if b = 0x03w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
        case bs of
        | [] => error "[dec_instr] : Byte sequence unexpectedly empty." []
        | (b::bs) =>
          if b = 0x0Bw then
            (INR (Loop bTyp body),bs)
          else
            error "[dec_instr] : Byte sequence unexpectedly empty." []) else
     if b = 0x04w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case check_len bs (dec_instr_list bs) of (INL err,bs) => (INL err,bs) | (INR bodyTh,bs) =>
        case bs of
        | [] => error "[dec_instr] : Byte sequence unexpectedly empty." []
        | (b::bs) =>
          if b = 0x0Bw then
            (INR (If bTyp bodyTh []),bs)
          else if b ≠ 0x05w then
            error "[dec_instr] : Byte sequence unexpectedly empty." (b::bs)
          else
            case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR bodyEl,bs) =>
            case bs of
            | [] => error "[dec_instr] : Byte sequence unexpectedly empty." []
            | (b::bs) =>
              if b = 0x0Bw then
                (INR (If bTyp bodyTh bodyEl),bs)
              else
                error "[dec_instr] : Byte sequence unexpectedly empty." [])
     else error "TODO not yet supported" (b::bs)) ∧
  (dec_instr_list ([]:byteSeq) =
     error "[dec_instr] : Byte sequence unexpectedly empty." []) ∧
  (dec_instr_list (b::bs) =
     if b = 0x0Bw then (INR [],bs) else
     case check_len (b::bs) (dec_instr (b::bs)) of (INL err,bs) => (INL err,bs) | (INR i,bs) =>
     case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR is,bs) =>
       (INR (i::is),bs))
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL bs => 2 * LENGTH bs
                            | INR bs => 2 * LENGTH bs + 1’
  \\ rw [] \\ imp_res_tac dec_blocktype_len \\ fs []
  \\ imp_res_tac check_len_IMP \\ fs []
End

Triviality check_len_INR:
  check_len bs0 y = (INR x,bs1) ⇒ ∃y1 y2. y = (INR y1,y2)
Proof
  gvs [oneline check_len_def, AllCaseEqs()] \\ rw [] \\ fs []
QED

Triviality check_len_INL:
  check_len bs0 y = (INL x,bs1) ⇒ ∃y1 y2. y = (INL y1,y2)
Proof
  gvs [oneline check_len_def, AllCaseEqs()] \\ rw [] \\ fs []
QED

Theorem dec_instr_length:
  (∀bs x bs1. dec_instr bs = (INR x,bs1) ⇒ LENGTH bs1 < LENGTH bs) ∧
  (∀bs x bs1. dec_instr_list bs = (INR x,bs1) ⇒ LENGTH bs1 < LENGTH bs)
Proof
  ho_match_mp_tac dec_instr_ind \\ rw []
  >~ [‘dec_instr []’] >- simp [dec_instr_def]
  >~ [‘dec_instr_list []’] >- simp [dec_instr_def]
  \\ pop_assum mp_tac
  \\ simp [Once dec_instr_def]
  \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac dec_blocktype_len \\ fs []
  \\ imp_res_tac check_len_INL \\ fs []
  \\ imp_res_tac check_len_INR \\ fs []
  \\ gvs [check_len_def]
QED

Theorem dec_instr_INL_length:
  (∀bs x bs1. dec_instr bs = (INL x,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs) ∧
  (∀bs x bs1. dec_instr_list bs = (INL x,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs)
Proof
  ho_match_mp_tac dec_instr_ind \\ rw []
  \\ pop_assum mp_tac
  \\ simp [Once dec_instr_def]
  \\ strip_tac
  \\ gvs [AllCaseEqs()]
  \\ imp_res_tac dec_blocktype_len \\ gvs []
  \\ imp_res_tac check_len_IMP_INL \\ gvs []
  \\ imp_res_tac check_len_INR \\ fs []
  \\ imp_res_tac check_len_IMP \\ fs []
  \\ cheat (* not implemented cases *)
QED

Theorem check_len_thm:
  check_len bs (dec_instr bs) = dec_instr bs ∧
  check_len bs (dec_instr_list bs) = dec_instr_list bs
Proof
  conj_tac
  >-
   (Cases_on ‘dec_instr bs’ \\ fs []
    \\ Cases_on ‘q’ \\ fs [check_len_def]
    \\ imp_res_tac dec_instr_INL_length \\ fs []
    \\ imp_res_tac dec_instr_length \\ fs [])
  \\ Cases_on ‘dec_instr_list bs’ \\ fs []
  \\ Cases_on ‘q’ \\ fs [check_len_def]
  \\ imp_res_tac dec_instr_INL_length \\ fs []
  \\ imp_res_tac dec_instr_length \\ fs []
QED

Theorem dec_instr_def[allow_rebind] = REWRITE_RULE [check_len_thm] dec_instr_def;
Theorem dec_instr_ind[allow_rebind] = REWRITE_RULE [check_len_thm] dec_instr_ind;

Theorem enc_instr_not_end:
  ∀i. ∃h t. enc_instr i = h::t ∧ h ≠ 0x0Bw
Proof
  Cases \\ simp [Once enc_instr_def]
  >~ [‘enc_varI’] >- (simp [enc_varI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_paraI’] >- (simp [enc_paraI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_numI’] >- (simp [enc_numI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_loadI’] >- (simp [enc_loadI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_storeI’] >- (simp [enc_storeI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_memI’] >- (simp [enc_memI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_vecI’] >- cheat (* incomplete *)
QED

Theorem dec_enc_instr:
  (∀i rest. dec_instr (enc_instr i ++ rest) = (INR i,rest)) ∧
  (∀is rest. dec_instr_list (enc_instr_list is ++ rest) = (INR is,rest))
Proof
  ho_match_mp_tac enc_instr_ind \\ reverse $ rw []
  \\ once_rewrite_tac [enc_instr_def]
  >- (rename [‘enc_instr i’]
      \\ qspec_then ‘i’ strip_assume_tac enc_instr_not_end \\ fs []
      \\ simp [Once dec_instr_def]
      \\ asm_rewrite_tac [GSYM APPEND_ASSOC] \\ simp [])
  >- simp [dec_instr_def]
  \\ Cases_on ‘i’ \\ fs []
  >~ [‘Unreachable’] >- (simp [dec_instr_def])
  >~ [‘Nop’] >- (simp [dec_instr_def])
  >~ [‘Block’] >-
   (simp [dec_instr_def]
    \\ asm_rewrite_tac [dec_enc_blocktype, GSYM APPEND_ASSOC] \\ simp [])
  >~ [‘Loop’] >-
   (simp [dec_instr_def]
    \\ asm_rewrite_tac [dec_enc_blocktype, GSYM APPEND_ASSOC] \\ simp [])
  >~ [‘If g b1 b2’] >-
   (simp [dec_instr_def]
    \\ asm_rewrite_tac [dec_enc_blocktype, GSYM APPEND_ASSOC] \\ simp []
    \\ Cases_on ‘b2’ \\ simp []
    \\ asm_rewrite_tac [GSYM APPEND_ASSOC] \\ simp [])
  \\ cheat (* not yet implemented cases *)
QED

(* Definition dec_instr_def:
  dec_instr ([]:byteSeq) : ((mlstring + instr) # byteSeq) = error "[dec_instr] : Byte sequence unexpectedly empty." [] ∧
  dec_instr (b::bs) = let failure = error "[dec_instr]" $ b::bs in

  (* control instructions *)
  if b = zeroB then (INR Unreachable, bs) else
  if b = 0x01w then (INR Nop        , bs) else

  if b = 0x0Cw then case dec_unsigned_word bs of NONE => failure | SOME (lbl,cs) => (INR $ Br           lbl, cs) else
  if b = 0x0Dw then case dec_unsigned_word bs of NONE => failure | SOME (lbl,cs) => (INR $ BrIf         lbl, cs) else
  (* TODO
  if b = 0x0Ew then case dec_u32 bs of NONE => failure | SOME (lbl,cs) => (INR $ BrTable [lbl] lbl ,bs) else *)

  if b = 0x0Fw then (INR Return , bs) else
  if b = 0x10w then case dec_unsigned_word bs of NONE => failure | SOME (f,cs) => (INR $ Call               f        , cs) else
   (* TODO
  if b = 0x11w then case dec_unsigned_word bs of NONE => failure | SOME (f,cs) => (INR $ CallIndirect       f (* tblIdx *) , cs) else *)
  if b = 0x12w then case dec_unsigned_word bs of NONE => failure | SOME (f,cs) => (INR $ ReturnCall         f        , cs) else
   (* TODO
  if b = 0x13w then case dec_unsigned_word bs of NONE => failure | SOME (f,cs) => (INR $ ReturnCallIndirect f (* tblIdx *) , cs) else *)

  (* variable instructions *)
  if b = 0x20w then case dec_unsigned_word bs of NONE=>failure| SOME(x,cs) => (INR $ LocalGet  x, cs) else
  if b = 0x21w then case dec_unsigned_word bs of NONE=>failure| SOME(x,cs) => (INR $ LocalSet  x, cs) else
  if b = 0x22w then case dec_unsigned_word bs of NONE=>failure| SOME(x,cs) => (INR $ LocalTee  x, cs) else
  if b = 0x23w then case dec_unsigned_word bs of NONE=>failure| SOME(x,cs) => (INR $ GlobalGet x, cs) else
  if b = 0x24w then case dec_unsigned_word bs of NONE=>failure| SOME(x,cs) => (INR $ GlobalSet x, cs) else

  case dec_numI (b::bs) of (INR inum,cs) => (INR $ Numeric inum, cs) | _ =>
  case dec_vecI (b::bs) of (INR ivec,cs) => (INR $ Vector  ivec, cs) | _ =>

  failure
End *)

val _ = export_theory();
