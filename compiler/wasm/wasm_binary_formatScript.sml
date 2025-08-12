(*
  En- & De- coding between CWasm 1.0 AST & Wasm's binary format
*)

open preamble;
open wasmLangTheory;
open mlstringTheory;
open leb128Theory miscOpsTheory;

val _ = set_grammar_ancestry ["wasmLang", "mlstring", "leb128", "miscOps"];

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

Overload error[local] = “λ obj str. (INL $ strlit str,obj)”
Overload emErr[local] = “λ str. (INL $ strlit $ "[" ++ str ++ "] : Byte sequence unexpectedly empty.\n",[])”


(*********************************************************)
(*                                                       *)
(*     Wasm Binary Format ⇔ WasmCake AST Functions      *)
(*                                                       *)
(*********************************************************)


(*****************************************)
(*   Vectors (not vector instructions)   *)
(*****************************************)

Definition enc_list_def:
  enc_list (encdr:α -> byteSeq) ([]:α list) : byteSeq option = SOME [] ∧
  enc_list encdr (x::xs) =
    case enc_list encdr xs of NONE=>NONE| SOME encxs =>
    SOME $ encdr x ++ encxs
End

Definition enc_vector_def:
  enc_vector (encdr:α -> byteSeq) (xs:α list) : byteSeq option =
    let n = LENGTH xs in
    if  2 ** 32 ≤ n then NONE else

    case enc_list encdr xs of NONE=>NONE| SOME encxs =>
    SOME $ enc_u32 (n2w n) ++ encxs
End

Definition dec_list_def:
  dec_list (n:num) decdr bs =
    if n = 0 then (INR [],bs) else
    case decdr bs of
    | (INL err, rs) => (INL err, rs)
    | (INR x  , rs) =>
      case dec_list (n-1) decdr rs of
      | (INL err, rs) => (INL err, rs)
      | (INR xs , rs) => (INR $ x::xs, rs)
End

Definition dec_vector_def:
  dec_vector (dec:byteSeq -> (mlstring + α) # byteSeq) (bs:byteSeq) : (mlstring + α list) # byteSeq =
    case dec_u32 bs of
    | NONE => error bs "dec_vec"
    | SOME (w,cs) => dec_list (w2n w) dec cs
End



Definition enc_listO_def:
  enc_listO (encdr:α -> byteSeq option) ([]:α list) : byteSeq option = SOME [] ∧
  enc_listO encdr (x::xs) =
    case           encdr x  of NONE=>NONE| SOME encx  =>
    case enc_listO encdr xs of NONE=>NONE| SOME encxs =>
    SOME $ encx ++ encxs
End

Definition enc_vectorO_def:
  enc_vectorO (encdr:α -> byteSeq option) (xs:α list) : byteSeq option =
    let n = LENGTH xs in
    if  2 ** 32 ≤ n then NONE else

    case enc_listO encdr xs of NONE=>NONE| SOME encxs =>
    SOME $ enc_u32 (n2w n) ++ encxs
End



(*************)
(*   Types   *)
(*************)

Definition enc_valtype_def:
  enc_valtype (t:valtype) : byte = case t of
  | Tnum   Int W32 => 0x7Fw
  | Tnum   Int W64 => 0x7Ew
End

Definition dec_valtype_def:
  dec_valtype ([]:byteSeq) : ((mlstring + valtype) # byteSeq) = emErr "dec_valtype" ∧
  dec_valtype (b::bs) = let failure = error (b::bs) "[dec_valtype]" in

  if b = 0x7Fw then (INR $ Tnum   Int W32 ,bs) else
  if b = 0x7Ew then (INR $ Tnum   Int W64 ,bs) else
  failure
End

Overload enc_valtype_Seq = “λ t. [enc_valtype t] : byteSeq”


Definition enc_functype_def:
  enc_functype (sg:functype) : byteSeq option =
    case enc_vector enc_valtype_Seq (FST sg) of NONE=>NONE| SOME argTs =>
    case enc_vector enc_valtype_Seq (SND sg) of NONE=>NONE| SOME resTs =>
    SOME $ 0x60w :: argTs ++ resTs
End

Definition dec_functype_def:
  dec_functype ([]:byteSeq) : (mlstring + functype) # byteSeq = emErr "dec_functype" ∧
  dec_functype (b::bs) = let failure = error (b::bs) "[dec_functype]" in

  if b ≠ 0x60w then failure else
  case dec_vector dec_valtype bs of (INL err, es) =>failure| (INR argTs,cs) =>
  case dec_vector dec_valtype cs of (INL err, es) =>failure| (INR resTs,rs) =>
  (INR (argTs, resTs), rs)
End



Definition enc_limits_def:
  enc_limits (lim:limits) : byteSeq = case lim of
  | Lunb mn    => 0x00w :: enc_u32  mn
  | Lwmx mn mx => 0x01w :: enc_2u32 mn mx
End

Definition dec_limits_def:
  dec_limits ([]:byteSeq) : (mlstring + limits) # byteSeq = emErr "dec_limits" ∧
  dec_limits (b::bs) = let failure = error (b::bs) "[dec_limits]" in

  if b = 0x00w then case dec_u32  bs of NONE=>failure| SOME (mn   ,rs) => (INR $ Lunb mn   , rs) else
  if b = 0x01w then case dec_2u32 bs of NONE=>failure| SOME (mn,mx,rs) => (INR $ Lwmx mn mx, rs) else
  failure
End



Definition enc_globaltype_def:
  enc_globaltype (t:globaltype) : byteSeq = case t of
  | Gconst vt => enc_valtype vt :: [0x00w]
  | Gmut   vt => enc_valtype vt :: [0x01w]
End

Definition dec_globaltype_def:
  dec_globaltype ([]:byteSeq) : ((mlstring + globaltype) # byteSeq) = emErr "dec_global" ∧
  dec_globaltype bs = let failure = error bs "[dec_global]" in

  case dec_valtype bs of (INL _,_) => failure | (INR vt, cs) =>
  case cs         of [] => emErr "dec_global" |  b  ::   rs  =>
  if b = 0x00w then (INR $ Gconst vt, rs) else
  if b = 0x01w then (INR $ Gmut   vt, rs) else
  failure
End



(*******************************************)
(*   Instructions (hierarchically lower)   *)
(*******************************************)

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
  | N_eqz     $   W64                        => [0x50w]
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
  dec_numI ([]:byteSeq) : ((mlstring + num_instr) # byteSeq) = emErr "dec_numI" ∧
  dec_numI (b::bs) = let failure = error (b::bs) "[dec_numI]" in

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
  if b = 0x50w then (INR $ N_eqz     $   W64                        ,bs) else
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



Definition enc_paraI_def:
  enc_paraI (i:para_instr) : byteSeq = case i of
  | Drop   => [0x1Aw]
  | Select => [0x1Bw]
End

Definition dec_paraI_def:
  dec_paraI ([]:byteSeq) : ((mlstring + para_instr) # byteSeq) = emErr "dec_paraI" ∧
  dec_paraI (b::bs) = let failure = error (b::bs) "[dec_paraI]" in

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
  dec_varI ([]:byteSeq) : ((mlstring + var_instr) # byteSeq) = emErr "dec_varI" ∧
  dec_varI (b::bs) = let failure = error (b::bs) "[dec_varI]" in

  if b = 0x20w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalGet  x,rs) else
  if b = 0x21w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalSet  x,rs) else
  if b = 0x22w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalTee  x,rs) else
  if b = 0x23w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ GlobalGet x,rs) else
  if b = 0x24w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ GlobalSet x,rs) else

  failure
End



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
  dec_loadI ([]:byteSeq) : ((mlstring + load_instr) # byteSeq) = emErr "dec_loadI" ∧
  dec_loadI (b::bs) = let failure = error (b::bs) "[dec_loadI]" in

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
  dec_storeI ([]:byteSeq) : ((mlstring + store_instr) # byteSeq) = emErr "dec_storeI" ∧
  dec_storeI (b::bs) = let failure = error (b::bs) "[dec_storeI]" in

  if b = 0x36w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store          Int  W32 ofs al,rs) else
  if b = 0x37w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store          Int  W64 ofs al,rs) else
  if b = 0x3Aw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W32 ofs al,rs) else
  if b = 0x3Bw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W32 ofs al,rs) else
  if b = 0x3Cw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W64 ofs al,rs) else
  if b = 0x3Dw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W64 ofs al,rs) else
  if b = 0x3Ew then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow32           ofs al,rs) else
  failure
End



(**********************************************)
(*                                            *)
(*     Top-level Instructions + Controls      *)
(*                                            *)
(**********************************************)

Definition enc_blocktype_def:
  enc_blocktype (bt:blocktype) : byteSeq = case bt of
  | BlkNil    => [0x40w]
  | BlkVal vt => [enc_valtype vt]
End

Definition dec_blocktype_def:
  dec_blocktype ([]:byteSeq) : (mlstring + blocktype) # byteSeq = emErr "dec_blocktype" ∧
  dec_blocktype bs = let failure = error bs "[dec_blocktype]" in

  case bs of []=>failure| b::rs => if b = 0x40w then (INR   BlkNil  , rs) else
  case dec_valtype bs of (INR t ,rs)            =>   (INR $ BlkVal t, rs) | _ =>
  failure
End

Overload enc_indxs = “enc_vector enc_u32”

Definition enc_instr_def:
  (* "Expressions" in Wasm are lists of instructions terminated by
      the byte 0x0B [endB]. Here we use a flag to control whether
      we are encoding expressions, or just lists of instructions.
      cf the If case for an example *)
  (enc_instrs (exp:bool) ([]:instr list) : byteSeq option = SOME if exp then [endB] else []) ∧
  (enc_instrs e (i::is) =
    case enc_instr  e i  of NONE=>NONE| SOME enci  =>
    case enc_instrs e is of NONE=>NONE| SOME encis =>  SOME $ enci ++ encis) ∧

  enc_instr (e:bool) (inst:instr) : byteSeq option = case inst of

  (* control instructions *)
  | Unreachable => SOME [zeroB]
  | Nop         => SOME [0x01w]

  | Block bT body => (case enc_instrs T body of NONE=>NONE| SOME encb => SOME $ 0x02w :: enc_blocktype bT ++ encb)
  | Loop  bT body => (case enc_instrs T body of NONE=>NONE| SOME encb => SOME $ 0x03w :: enc_blocktype bT ++ encb)
  | If bT bdT []  => (case enc_instrs T bdT  of NONE=>NONE| SOME enct => SOME $ 0x04w :: enc_blocktype bT ++ enct)
  | If bT bdT bdE => (case enc_instrs F bdT  of NONE=>NONE| SOME enct =>
                      case enc_instrs T bdE  of NONE=>NONE| SOME ence => SOME $ 0x04w :: enc_blocktype bT ++ enct ++ elseB :: ence)

  | Br           lbl =>                                     SOME $ 0x0Cw ::                            enc_u32 lbl
  | BrIf         lbl =>                                     SOME $ 0x0Dw ::                            enc_u32 lbl
  | BrTable lbls lbl => (case enc_indxs lbls of NONE=>NONE| SOME enclbls => SOME $ 0x0Ew :: enclbls ++ enc_u32 lbl)

  | Return                    =>                                                      SOME  [0x0Fw]
  | Call               fdx    =>                                                      SOME $ 0x10w ::            enc_u32 fdx
  | ReturnCall         fdx    =>                                                      SOME $ 0x12w ::            enc_u32 fdx
  | CallIndirect       fdx sg => (case enc_functype sg of NONE=>NONE| SOME encFsig => SOME $ 0x11w :: encFsig ++ enc_u32 fdx)
  | ReturnCallIndirect fdx sg => (case enc_functype sg of NONE=>NONE| SOME encFsig => SOME $ 0x13w :: encFsig ++ enc_u32 fdx)

  (* other classes of instructions *)
  | Variable   i => SOME $ enc_varI   i
  | Parametric i => SOME $ enc_paraI  i
  | Numeric    i => SOME $ enc_numI   i
  | MemRead    i => SOME $ enc_loadI  i
  | MemWrite   i => SOME $ enc_storeI i
End

Overload enc_expr       = “enc_instrs T”
Overload enc_instr_list = “enc_instrs F”



Definition enc_global_def:
  enc_global (g:global) : byteSeq option =

  case enc_expr g.ginit of NONE=>NONE| SOME expr =>
  SOME $ enc_globaltype g.gtype ++ expr
End

Definition enc_code_def:
  enc_code (c:valtype list # expr) : byteSeq option =
    case enc_vector enc_valtype_Seq (FST c) of NONE=>NONE| SOME encL =>
    case enc_expr                   (SND c) of NONE=>NONE| SOME encC =>
    let code = encL ++ encC in
    SOME $ enc_u32 (n2w $ LENGTH code) ++ code
End

Definition enc_data_def:
  enc_data (d:data) : byteSeq option =
    case enc_expr d.offset             of NONE=>NONE| SOME ofs =>
    case enc_vector (λ b. [b]) d.dinit of NONE=>NONE| SOME ini =>

    SOME $ enc_u32 d.data ++ ofs ++ ini
End

Definition enc_section_def:
  enc_section (leadByte:byte) (contents:byteSeq) : byteSeq =
    leadByte :: enc_u32 (n2w $ LENGTH contents) ++ contents
End

(* Definition dec_section_def:
  dec_section ([]:byteSeq) : ((mlstring + byteSeq) # byteSeq) = emErr "dec_section" ∧
  dec_section bs = let failure = error bs "[dec_section]" in

  case dec_u32 of NONE=>NONE| SOME

  dec_section (leadByte:byte) (contents:byteSeq) : byteSeq =
    leadByte :: enc_u32 (n2w $ LENGTH contents) ++ contents
End *)

Overload enc_custom_sec  = “enc_section  0w”
Overload enc_type_sec    = “enc_section  1w”
Overload enc_funcs_sec   = “enc_section  3w”
Overload enc_memory_sec  = “enc_section  5w”
Overload enc_global_sec  = “enc_section  6w”
Overload enc_code_sec    = “enc_section 10w”
Overload enc_data_sec    = “enc_section 11w”
(* Overload enc_import_sec  = “enc_section  2w” *)
(* Overload enc_table_sec   = “enc_section  4w” *)
(* Overload enc_export_sec  = “enc_section  7w” *)
(* Overload enc_start_sec   = “enc_section  8w” *)
(* Overload enc_element_sec = “enc_section  9w” *)

Definition split_funcs_def:
  split_funcs ([]:func list) : index list # (valtype list # expr) list = ([],[]) ∧
  split_funcs (f::fs) =
  let (typs, lBods) = split_funcs fs in
  (f.ftype :: typs, (f.locals, f.body) :: lBods)
End

(* Overload enc_types   = enc_vectorO enc_functype
Overload enc_funcs   = enc_vector  enc_u32
Overload enc_mems    = enc_vector  enc_limits
Overload enc_globals = enc_vectorO enc_global
Overload enc_codes   = enc_vectorO enc_code
Overload enc_datas   = enc_vectorO enc_data     *)

(* From CWasm (not Wasm!) modules to Wasm binary format *)
Definition enc_module_def:
  enc_module (m:module) : byteSeq option =

    let (fTIdxs, locBods) = split_funcs m.funcs in
    case enc_vectorO  enc_functype  m.types   of NONE=>NONE| SOME types'   =>
    case enc_vector   enc_u32       fTIdxs    of NONE=>NONE| SOME funcs'   =>
    case enc_vector   enc_limits    m.mems    of NONE=>NONE| SOME mems'    =>
    case enc_vectorO  enc_global    m.globals of NONE=>NONE| SOME globals' =>
    case enc_vectorO  enc_code      locBods   of NONE=>NONE| SOME code'    =>
    case enc_vectorO  enc_data      m.datas   of NONE=>NONE| SOME datas'   =>

    SOME $
    0x00w:: 0x61w:: 0x73w:: 0x6Dw:: (* \0asm - magic number         *)
    0x01w:: 0x00w:: 0x00w:: 0x00w:: (* version number of Bin format *)

    enc_type_sec   types'   ++
    enc_funcs_sec  funcs'   ++
    enc_memory_sec mems'    ++
    enc_global_sec globals' ++
    enc_code_sec   code'    ++
    enc_data_sec   datas'
End



(***********************************)
(*                                 *)
(*     Decode--Encode Theorems     *)
(*                                 *)
(***********************************)

(* neat trick to check if we're making progress - due to MM *)
fun print_dot_tac h = (print "."; all_tac h);

(*************)
(*   Types   *)
(*************)

Theorem dec_enc_valtype:
  ∀ t rest. dec_valtype (enc_valtype t :: rest) = (INR t, rest)
Proof
  rpt strip_tac
  >> `∃ val. enc_valtype t = val` by simp []
  >> asm_rewrite_tac[]
  >> pop_assum mp_tac
  >> rewrite_tac[enc_valtype_def]
  >> simp[AllCaseEqs()]
  >> simp[bvtype_nchotomy]
  >> rpt strip_tac
  >> gvs[dec_valtype_def]
  (*
  rw[enc_valtype_def] >> every_case_tac >> simp[bvtype_nchotomy] >> rw[dec_valtype_def]
  *)
QED

Theorem dec_enc_globaltype:
  ∀ x rest. dec_globaltype (enc_globaltype x ++ rest) = (INR x, rest)
Proof
  rpt strip_tac
  >> `∃ val. enc_globaltype x = val` by simp []
  >> asm_rewrite_tac[]
  >> pop_assum mp_tac
  >> rewrite_tac[enc_globaltype_def]
  >> simp[AllCaseEqs()]
  >> rpt strip_tac
  >> gvs[dec_globaltype_def, dec_enc_valtype]
  (*
  rw[enc_globaltype_def] >> every_case_tac >> rw[dec_globaltype_def, dec_enc_valtype]
  *)
QED


(********************)
(*   Instructions   *)
(********************)

Theorem dec_enc_numI:
  ∀ i rest. dec_numI (enc_numI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_numI i = res’ by simp []
  \\ asm_rewrite_tac []
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_numI_def]
  \\ simp[AllCaseEqs()]
  \\ simp[bvtype_nchotomy]
  \\ simp[convert_op_nchotomy]
  \\ rpt strip_tac

  (* single byte encoding cases *)
  \\ asm_rewrite_tac[APPEND, dec_numI_def]
  \\ simp[AllCaseEqs()]

  (* cases requiring further encoding (of their "immediates") *)
  \\ (
    pop_assum sym_sub_tac
    >- simp[dec_numI_def, AllCaseEqs()]
  )
QED

Theorem dec_enc_paraI:
  ∀ i rest. dec_paraI (enc_paraI i ++ rest) = (INR i, rest)
Proof
  rw[enc_paraI_def] >> every_case_tac >> rw[dec_paraI_def]
QED

Theorem dec_enc_varI:
  ∀ i rest. dec_varI (enc_varI i ++ rest) = (INR i, rest)
Proof
  rw[enc_varI_def] >> every_case_tac >> rw[dec_varI_def, dec_enc_unsigned_word]
QED

Theorem dec_enc_loadI:
  ∀ i rest. dec_loadI (enc_loadI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_loadI i = res’ by simp [] >> asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_loadI_def]
  \\ simp[AllCaseEqs()]
  \\ simp[bvtype_nchotomy]
  \\ simp[convert_op_nchotomy]
  \\ rpt strip_tac

  \\ ( pop_assum sym_sub_tac >- simp[dec_loadI_def, AllCaseEqs()] )
QED

Theorem dec_enc_storeI:
  ∀ i rest. dec_storeI (enc_storeI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_storeI i = res’ by simp []
  \\ asm_rewrite_tac []
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_storeI_def]
  \\ simp[AllCaseEqs()]
  \\ simp[bvtype_nchotomy]
  \\ rpt strip_tac
  \\ gvs[dec_storeI_def, dec_enc_2u32]
  (*
  rw[enc_storeI_def] >> every_case_tac
  >> simp[bvtype_nchotomy]
  >> rw[dec_storeI_def]
  *)
QED



Theorem dec_enc_blocktype:
  ∀b rest. dec_blocktype (enc_blocktype b ++ rest) = (INR b, rest)
Proof
  rpt strip_tac
  >> `∃ val. enc_blocktype b = val` by simp []
  >> asm_rewrite_tac[]
  >> pop_assum mp_tac
  >> rewrite_tac[enc_blocktype_def]
  >> simp[AllCaseEqs()]
  >> rpt strip_tac
  >- gvs[dec_blocktype_def]
  >- (
    gvs[dec_blocktype_def, dec_enc_valtype]
    >> rw[enc_valtype_def]
    >> fs[AllCaseEqs()]
  )
QED

Theorem dec_enc_vector:
  ∀ dec enc x rs. (dec (enc x ++ rs) =  (INR x,rs)) ⇒
  ∀ is encis rest. (enc_vector enc is = SOME encis) ⇒
  (dec_vector dec encis = (INR items, rest))
Proof
  rpt strip_tac
  \\ pop_assum mp_tac
  \\ rewrite_tac[dec_vector_def, enc_vector_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
  \\
  cheat
QED


(*
  ∀ dec enc x rs1 items encitems rest.
Theorem dec_enc_vector:

    (dec (enc x ++ rs1) =  (INR x,rs1)) ⇒
    (enc_vector enc items = SOME encitems) ⇒

  (dec_vector dec encitems = (INR items, rest))
Proof
  cheat
QED

*)


(***************)
(*             *)
(*     WIP     *)
(*             *)
(***************)


Theorem dec_blocktype_len:
  ∀ bs r bs1. dec_blocktype bs = (r,bs1) ⇒ LENGTH bs1 ≤ LENGTH bs
Proof
  Cases
  >- simp[dec_blocktype_def]
  >- (
    rpt gen_tac
    >> simp[dec_blocktype_def]
    >> simp[AllCaseEqs()]
    >> rpt strip_tac
    >>
    cheat
  )
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
  (dec_instr ([]:byteSeq) : ((mlstring + instr) # byteSeq) = emErr "dec_instr") ∧
  (dec_instr (b::bs) = let failure = error (b::bs) "[dec_instr]" in
    if b = zeroB then (INR Unreachable, bs) else
    if b = 0x01w then (INR Nop        , bs) else
    if b = 0x0Fw then (INR Return     , bs) else

     if b = 0x02w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
        case bs of
        | [] => failure
        | (b::bs) =>
          if b = 0x0Bw then
            (INR (Block bTyp body),bs)
          else
            failure) else
     if b = 0x03w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
        case bs of
        | [] => failure
        | (b::bs) =>
          if b = 0x0Bw then
            (INR (Loop bTyp body),bs)
          else
            failure) else
     if b = 0x04w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case check_len bs (dec_instr_list bs) of (INL err,bs) => (INL err,bs) | (INR bodyTh,bs) =>
        case bs of
        | [] => failure
        | (b::bs) =>
          if b = 0x0Bw then
            (INR (If bTyp bodyTh []),bs)
          else if b ≠ 0x05w then
            failure
          else
            case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR bodyEl,bs) =>
            case bs of
            | [] => failure
            | (b::bs) =>
              if b = 0x0Bw then
                (INR (If bTyp bodyTh bodyEl),bs)
              else
                failure)
     else error (b::bs) "TODO not yet supported") ∧
  (dec_instr_list ([]:byteSeq) = emErr "dec_instr_list") ∧
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
  ∀i b. ∃h t. enc_instr b i = SOME $ h::t ∧ h ≠ 0x0Bw
Proof
  Cases \\ simp [Once enc_instr_def]
  >~ [‘enc_varI’] >- (simp [enc_varI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_paraI’] >- (simp [enc_paraI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_numI’] >- (simp [enc_numI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_loadI’] >- (simp [enc_loadI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_storeI’] >- (simp [enc_storeI_def] \\ every_case_tac \\ fs [])
  \\ cheat
QED

(* Theorem dec_enc_instr:
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
QED *)

val _ = export_theory();

