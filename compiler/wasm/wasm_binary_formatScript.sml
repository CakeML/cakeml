(*
  En- & De- coding between CWasm 1.0 AST & Wasm's binary format

*)

open preamble;
open wasmLangTheory;
open mlstringTheory;
open leb128Theory miscOpsTheory;

val _ = new_theory "wasm_binary_format";

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
End

Definition dec_valtype_def:
  dec_valtype (b:byte) : valtype option =
  if b = 0x7Fw then SOME (Tnum   Int W32) else
  if b = 0x7Ew then SOME (Tnum   Int W64) else
  NONE
End

Theorem dec_enc_valtype_redux:
  ∀ t. dec_valtype (enc_valtype t) = SOME t
Proof
  rw[enc_valtype_def] >> every_case_tac
  >> Cases_on `b`
  >> rw[dec_valtype_def]
QED



Definition enc_blocktype_def:
  enc_blocktype (bt:blocktype) : byteSeq = case bt of
  | BlkNil    => [0x40w]
  | BlkVal vt => [enc_valtype vt]
End

Definition dec_blocktype_def:
  dec_blocktype ([]:byteSeq) : ((mlstring + blocktype) # byteSeq) = error "[dec_blocktype] : Byte sequence unexpectedly empty." [] ∧
  dec_blocktype (b::bs) = let failure = error "[dec_blocktype]" $ b::bs in

  if b = 0x40w then                        (INR   BlkNil        , bs) else
  case dec_valtype x40   of SOME t      => (INR $ BlkVal t      , bs) | _ =>
  failure
End

Theorem dec_enc_blocktype:
  ∀b rest. dec_blocktype (enc_blocktype b ++ rest) = (INR b, rest)
Proof
  cheat
  (* rw[enc_blocktype_def] >> every_case_tac
  >- rw[dec_blocktype_def]
  >- (rw[dec_blocktype_def, dec_enc_valtype_redux]
  >- Cases_on `v` >> Cases_on `b` >> Cases_on `w`
  >> pop_assum mp_tac
  >> rw[enc_valtype_def] ) *)
QED



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
  | N_convert $   WrapI64                    => [0xA7w]
  | N_unary   $   ExtendI32_   Signed        => [0xACw]
  | N_unary   $   ExtendI32_ Unsigned        => [0xADw]
  | N_unary   $   Extend8s  W32              => [0xC0w]
  | N_unary   $   Extend16s W32              => [0xC1w]
  | N_unary   $   Extend8s  W64              => [0xC2w]
  | N_unary   $   Extend16s W64              => [0xC3w]
  | N_unary   $   Extend32s                  => [0xC4w]

  | N_const32 Int   (c32: word32)            =>  0x41w :: enc_s32 c32
  | N_const64 Int   (c64: word64)            =>  0x42w :: enc_s64 c64
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
  if b = 0xA7w then (INR $ N_convert $   WrapI64                    ,bs) else
  if b = 0xACw then (INR $ N_unary   $   ExtendI32_   Signed        ,bs) else
  if b = 0xADw then (INR $ N_unary   $   ExtendI32_ Unsigned        ,bs) else
  if b = 0xC0w then (INR $ N_unary   $   Extend8s  W32              ,bs) else
  if b = 0xC1w then (INR $ N_unary   $   Extend16s W32              ,bs) else
  if b = 0xC2w then (INR $ N_unary   $   Extend8s  W64              ,bs) else
  if b = 0xC3w then (INR $ N_unary   $   Extend16s W64              ,bs) else
  if b = 0xC4w then (INR $ N_unary   $   Extend32s                  ,bs) else

  if b = 0x41w then case dec_s32 bs of SOME (s32,cs) => (INR $ N_const32  Int  s32, cs) | NONE => failure else
  if b = 0x42w then case dec_s64 bs of SOME (s64,cs) => (INR $ N_const64  Int  s64, cs) | NONE => failure else
  (* failure "[dec_numI] : Not a numeric instruction" *)
  failure
End


Theorem dec_enc_numI:
  ∀ i. dec_numI (enc_numI i ++ rest) = (INR i, rest)
Proof
  cheat
QED



Definition enc_loadI_def:
  enc_loadI (i:load_instr) : byteSeq = case i of
  | Load    Int                  W32 ofs al  => 0x28w :: enc_2u32 al ofs
  | Load    Int                  W64 ofs al  => 0x29w :: enc_2u32 al ofs
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
End

Definition dec_loadI_def:
  dec_loadI ([]:byteSeq) : ((mlstring + load_instr) # byteSeq) = error "[dec_loadI] : Byte sequence unexpectedly empty." [] ∧
  dec_loadI (b::bs) = let failure = error "[dec_loadI]" $ b::bs in

  if b = 0x28w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   Load    Int                  W32 ofs al,rs) else
  if b = 0x29w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $   Load    Int                  W64 ofs al,rs) else
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
  failure
End



Definition enc_storeI_def:
  enc_storeI (i:store_instr) : byteSeq = case i of
  | Store   Int                  W32 ofs al => 0x36w :: enc_2u32 al ofs
  | Store   Int                  W64 ofs al => 0x37w :: enc_2u32 al ofs
  | StoreNarrow I8x16            W32 ofs al => 0x3Aw :: enc_2u32 al ofs
  | StoreNarrow I16x8            W32 ofs al => 0x3Bw :: enc_2u32 al ofs
  | StoreNarrow I8x16            W64 ofs al => 0x3Cw :: enc_2u32 al ofs
  | StoreNarrow I16x8            W64 ofs al => 0x3Dw :: enc_2u32 al ofs
  | StoreNarrow32                    ofs al => 0x3Ew :: enc_2u32 al ofs
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
  if b = 0x3Aw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W32 ofs al,rs) else
  if b = 0x3Bw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W32 ofs al,rs) else
  if b = 0x3Cw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W64 ofs al,rs) else
  if b = 0x3Dw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W64 ofs al,rs) else
  if b = 0x3Ew then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow32           ofs al,rs) else
  failure
End



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



(***********************************)
(*                                 *)
(*     Decode--Encode Theorems     *)
(*                                 *)
(***********************************)

(*
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
*)

Theorem dec_enc_loadI:
  ∀ i. dec_loadI (enc_loadI i ++ rest) = (INR i, rest)
Proof
  cheat
  (* rw [enc_loadI_def] >> every_case_tac
  >> rw [dec_loadI_def]
  >> (rewrite_tac[GSYM APPEND_ASSOC] >- rw[]) *)
QED

Theorem dec_enc_storeI:
  ∀ i. dec_storeI (enc_storeI i ++ rest) = (INR i, rest)
Proof
  rw[enc_storeI_def] >> every_case_tac
  >- (Cases_on `b`  >> rw[dec_storeI_def])
  >- (Cases_on `b`  >> rw[dec_storeI_def])
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

Definition enc_vector_aux_def:
  enc_vector_aux (encdr:α -> byteSeq) ([]:α list) = (0:num,[]) ∧
  enc_vector_aux encdr (x::xs) =
    let (n,ys) = enc_vector_aux encdr xs in
    (n+1, encdr x ++ ys)
End

Definition enc_vector_def:
  enc_vector (encdr:α -> byteSeq) ([]:α list) : byteSeq option = SOME $ enc_num 0 ∧
  enc_vector encdr xs =
    let (n,ys) = enc_vector_aux encdr xs in
    if n < 2 ** 32 then SOME $ enc_num n ++ ys else NONE
End

(* Definition dec_vector_aux:
  dec_vector_aux decdr (n:num) (bs:byteSeq) =
  dec_vector_aux decdr (n:num) (bs:byteSeq) =
  dec_vector_aux decdr (n:num) (bs:byteSeq) =
    case decdr bs of
End *)

(* Definition dec_vec_def:
  dec_vector (_:byteSeq -> ((mlstring + α) # byteSeq)) ([]:byteSeq) : ((mlstring + α) # byteSeq) =
    error "[dec_vector] : Byte sequence unexpectedly empty." [] ∧

  dec_vector decdr bs = let failure = error "[dec_vector]" $ bs in

    case dec_u32 bs of NONE=>failure| SOME (len, vs) =>

    failure
  (* dec_vec decdr (bs:byteSeq) =
    case dec_num bs of NONE => ARB
    ARB *)
End *)

(* Definition dec_vec_def:
  (* dec_vec ([]:byteSeq) : ((mlstring + table_instr) # byteSeq) = error "[dec_vec] : Byte sequence unexpectedly empty." [] ∧ *)
  dec_vec decdr (bs) = ARB
End *)

(* Theorem dec_enc_vector:
  ∀ (enc:α -> byteSeq) (dec:byteSeq -> (α # byteSeq) option) x xs rs1 rs2.
    dec (enc x ++ rs1) = SOME (x,rs1) ⇒
  dec_vector dec (enc_vector enc xs ++ rs2) = SOME (xs,rs2)
Proof
  cheat
QED *)

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
  | MemRead    i => enc_loadI  i
  | MemWrite   i => enc_storeI i
  | _ => []
  ) ∧

  (enc_instr_list ([]:instr list) : byteSeq = [endB]) ∧
  (enc_instr_list (i::ins) = enc_instr i ++ enc_instr_list ins)

End
(*
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
  >> cheat
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
*)
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
