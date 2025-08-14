(*
  En- & De- coding between CWasm 2.0 AST & Wasm's binary format
*)

Theory      wasm2_binary_format
Ancestors   wasm2Lang leb128 ancillaryOps
Libs        preamble wordsLib blastLib
(*
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
Overload B0[local]    = “(λ x. x = zeroB):byte -> bool”

Overload error[local] = “λ obj str. (INL (strlit str),obj)”
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
  | Tnum Float W32 => 0x7Dw
  | Tnum Float W64 => 0x7Cw
  | Tvec           => 0x7Bw
  | Tref Fun       => 0x70w
  | Tref Ext       => 0x6Fw
End

Definition dec_valtype_def:
  dec_valtype ([]:byteSeq) : ((mlstring + valtype) # byteSeq) = emErr "dec_valtype" ∧
  dec_valtype (b::bs) = let failure = error (b::bs) "[dec_valtype]" in

  if b = 0x7Fw then (INR $ Tnum   Int W32 ,bs) else
  if b = 0x7Ew then (INR $ Tnum   Int W64 ,bs) else
  if b = 0x7Dw then (INR $ Tnum Float W32 ,bs) else
  if b = 0x7Cw then (INR $ Tnum Float W64 ,bs) else
  if b = 0x7Bw then (INR $ Tvec           ,bs) else
  if b = 0x70w then (INR $ Tref Fun       ,bs) else
  if b = 0x6Fw then (INR $ Tref Ext       ,bs) else
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

Overload enc_expr       = “enc_instrs T”
Overload enc_instr_list = “enc_instrs F”


Definition dec_limits_def:
  dec_limits ([]:byteSeq) : (mlstring + limits) # byteSeq = emErr "dec_limits" ∧
  dec_limits (b::bs) = let failure = error (b::bs) "[dec_limits]" in

  if b = 0x00w then case dec_u32  bs of NONE=>failure| SOME (mn   ,rs) => (INR $ Lunb mn   , rs) else
  if b = 0x01w then case dec_2u32 bs of NONE=>failure| SOME (mn,mx,rs) => (INR $ Lwmx mn mx, rs) else
  failure
End



Definition enc_globaltype_def:
  enc_globaltype (t:globaltype) : byteSeq = case t of
  | Gconst vt => 0x00w :: [enc_valtype vt]
  | Gmut   vt => 0x01w :: [enc_valtype vt]
End

Definition dec_globaltype_def:
  dec_globaltype ([]:byteSeq) : ((mlstring + globaltype) # byteSeq) = emErr "dec_global" ∧
  dec_globaltype (b::bs) = let failure = error (b::bs) "[dec_global]" in

  if b = 0x00w then case dec_valtype bs of (INR vt, rs) => (INR $ Gconst vt, rs) | _ => failure else
  if b = 0x01w then case dec_valtype bs of (INR vt, rs) => (INR $ Gmut   vt, rs) | _ => failure else
  failure
End



(*******************************************)
(*   Instructions (hierarchically lower)   *)
(*******************************************)

Definition enc_numI_def:
  enc_numI (i:num_instr) : byteSeq = case i of
  |N_eqz    $   W32                        => [0x45w]
  |N_compare$   Eq  Int      W32           => [0x46w]
  |N_compare$   Ne  Int      W32           => [0x47w]
  |N_compare$   Lt_   Signed W32           => [0x48w]
  |N_compare$   Lt_ Unsigned W32           => [0x49w]
  |N_compare$   Gt_   Signed W32           => [0x4Aw]
  |N_compare$   Gt_ Unsigned W32           => [0x4Bw]
  |N_compare$   Le_   Signed W32           => [0x4Cw]
  |N_compare$   Le_ Unsigned W32           => [0x4Dw]
  |N_compare$   Ge_   Signed W32           => [0x4Ew]
  |N_compare$   Ge_ Unsigned W32           => [0x4Fw]
  |N_eqz    $   W64                        => [0x50w]
  |N_compare$   Eq Int       W64           => [0x51w]
  |N_compare$   Ne Int       W64           => [0x52w]
  |N_compare$   Lt_   Signed W64           => [0x53w]
  |N_compare$   Lt_ Unsigned W64           => [0x54w]
  |N_compare$   Gt_   Signed W64           => [0x55w]
  |N_compare$   Gt_ Unsigned W64           => [0x56w]
  |N_compare$   Le_   Signed W64           => [0x57w]
  |N_compare$   Le_ Unsigned W64           => [0x58w]
  |N_compare$   Ge_   Signed W64           => [0x59w]
  |N_compare$   Ge_ Unsigned W64           => [0x5Aw]
  |N_compare$   Eq  Float    W32           => [0x5Bw]
  |N_compare$   Ne  Float    W32           => [0x5Cw]
  |N_compare$   Lt           W32           => [0x5Dw]
  |N_compare$   Gt           W32           => [0x5Ew]
  |N_compare$   Le           W32           => [0x5Fw]
  |N_compare$   Ge           W32           => [0x60w]
  |N_compare$   Eq  Float    W64           => [0x61w]
  |N_compare$   Ne  Float    W64           => [0x62w]
  |N_compare$   Lt           W64           => [0x63w]
  |N_compare$   Gt           W64           => [0x64w]
  |N_compare$   Le           W64           => [0x65w]
  |N_compare$   Ge           W64           => [0x66w]
  |N_unary  $   Clz    W32                 => [0x67w]
  |N_unary  $   Ctz    W32                 => [0x68w]
  |N_unary  $   Popcnt W32                 => [0x69w]
  |N_binary $   Add  Int      W32          => [0x6Aw]
  |N_binary $   Sub  Int      W32          => [0x6Bw]
  |N_binary $   Mul  Int      W32          => [0x6Cw]
  |N_binary $   Div_   Signed W32          => [0x6Dw]
  |N_binary $   Div_ Unsigned W32          => [0x6Ew]
  |N_binary $   Rem_   Signed W32          => [0x6Fw]
  |N_binary $   Rem_ Unsigned W32          => [0x70w]
  |N_binary $   And           W32          => [0x71w]
  |N_binary $   Or            W32          => [0x72w]
  |N_binary $   Xor           W32          => [0x73w]
  |N_binary $   Shl           W32          => [0x74w]
  |N_binary $   Shr_   Signed W32          => [0x75w]
  |N_binary $   Shr_ Unsigned W32          => [0x76w]
  |N_binary $   Rotl          W32          => [0x77w]
  |N_binary $   Rotr          W32          => [0x78w]
  |N_unary  $   Clz    W64                 => [0x79w]
  |N_unary  $   Ctz    W64                 => [0x7Aw]
  |N_unary  $   Popcnt W64                 => [0x7Bw]
  |N_binary $   Add Int       W64          => [0x7Cw]
  |N_binary $   Sub Int       W64          => [0x7Dw]
  |N_binary $   Mul Int       W64          => [0x7Ew]
  |N_binary $   Div_   Signed W64          => [0x7Fw]
  |N_binary $   Div_ Unsigned W64          => [0x80w]
  |N_binary $   Rem_   Signed W64          => [0x81w]
  |N_binary $   Rem_ Unsigned W64          => [0x82w]
  |N_binary $   And           W64          => [0x83w]
  |N_binary $   Or            W64          => [0x84w]
  |N_binary $   Xor           W64          => [0x85w]
  |N_binary $   Shl           W64          => [0x86w]
  |N_binary $   Shr_   Signed W64          => [0x87w]
  |N_binary $   Shr_ Unsigned W64          => [0x88w]
  |N_binary $   Rotl          W64          => [0x89w]
  |N_binary $   Rotr          W64          => [0x8Aw]
  |N_unary  $   Abs     W32                => [0x8Bw]
  |N_unary  $   Neg     W32                => [0x8Cw]
  |N_unary  $   Ceil    W32                => [0x8Dw]
  |N_unary  $   Floor   W32                => [0x8Ew]
  |N_unary  $   Trunc   W32                => [0x8Fw]
  |N_unary  $   Nearest W32                => [0x90w]
  |N_unary  $   Sqrt    W32                => [0x91w]
  |N_binary $   Add Float W32              => [0x92w]
  |N_binary $   Sub Float W32              => [0x93w]
  |N_binary $   Mul Float W32              => [0x94w]
  |N_binary $   Div       W32              => [0x95w]
  |N_binary $   Min       W32              => [0x96w]
  |N_binary $   Max       W32              => [0x97w]
  |N_binary $   Copysign  W32              => [0x98w]
  |N_unary  $   Abs     W64                => [0x99w]
  |N_unary  $   Neg     W64                => [0x9Aw]
  |N_unary  $   Ceil    W64                => [0x9Bw]
  |N_unary  $   Floor   W64                => [0x9Cw]
  |N_unary  $   Trunc   W64                => [0x9Dw]
  |N_unary  $   Nearest W64                => [0x9Ew]
  |N_unary  $   Sqrt    W64                => [0x9Fw]
  |N_binary $   Add Float W64              => [0xA0w]
  |N_binary $   Sub Float W64              => [0xA1w]
  |N_binary $   Mul Float W64              => [0xA2w]
  |N_binary $   Div       W64              => [0xA3w]
  |N_binary $   Min       W64              => [0xA4w]
  |N_binary $   Max       W64              => [0xA5w]
  |N_binary $   Copysign  W64              => [0xA6w]
  |N_convert$   WrapI64                    => [0xA7w]
  |N_convert$   Trunc_f W32   Signed W32   => [0xA8w]
  |N_convert$   Trunc_f W32 Unsigned W32   => [0xA9w]
  |N_convert$   Trunc_f W64   Signed W32   => [0xAAw]
  |N_convert$   Trunc_f W64 Unsigned W32   => [0xABw]
  |N_unary  $   ExtendI32_   Signed        => [0xACw]
  |N_unary  $   ExtendI32_ Unsigned        => [0xADw]
  |N_convert$   Trunc_f W32   Signed W64   => [0xAEw]
  |N_convert$   Trunc_f W32 Unsigned W64   => [0xAFw]
  |N_convert$   Trunc_f W64   Signed W64   => [0xB0w]
  |N_convert$   Trunc_f W64 Unsigned W64   => [0xB1w]
  |N_convert$   Convert W32   Signed W32   => [0xB2w]
  |N_convert$   Convert W32 Unsigned W32   => [0xB3w]
  |N_convert$   Convert W64   Signed W32   => [0xB4w]
  |N_convert$   Convert W64 Unsigned W32   => [0xB5w]
  |N_convert$   Demote                     => [0xB6w]
  |N_convert$   Convert W32   Signed W64   => [0xB7w]
  |N_convert$   Convert W32 Unsigned W64   => [0xB8w]
  |N_convert$   Convert W64   Signed W64   => [0xB9w]
  |N_convert$   Convert W64 Unsigned W64   => [0xBAw]
  |N_convert$   Promote                    => [0xBBw]
  |N_convert$   Reinterpret_f        W32   => [0xBCw]
  |N_convert$   Reinterpret_f        W64   => [0xBDw]
  |N_convert$   Reinterpret_i        W32   => [0xBEw]
  |N_convert$   Reinterpret_i        W64   => [0xBFw]
  |N_unary  $   Extend8s  W32              => [0xC0w]
  |N_unary  $   Extend16s W32              => [0xC1w]
  |N_unary  $   Extend8s  W64              => [0xC2w]
  |N_unary  $   Extend16s W64              => [0xC3w]
  |N_unary  $   Extend32s                  => [0xC4w]

  |N_const32 Int   (c32: word32)           =>  0x41w :: enc_s32 c32
  |N_const64 Int   (c64: word64)           =>  0x42w :: enc_s64 c64

  |N_const32 Float (c32: word32)           =>  0x43w :: lend32 c32
  |N_const64 Float (c64: word64)           =>  0x44w :: lend64 c64

  |N_convert$   Trunc_sat_f W32   Signed W32   => 0xFCw :: enc_u32 0w
  |N_convert$   Trunc_sat_f W32 Unsigned W32   => 0xFCw :: enc_u32 1w
  |N_convert$   Trunc_sat_f W64   Signed W32   => 0xFCw :: enc_u32 2w
  |N_convert$   Trunc_sat_f W64 Unsigned W32   => 0xFCw :: enc_u32 3w
  |N_convert$   Trunc_sat_f W32   Signed W64   => 0xFCw :: enc_u32 4w
  |N_convert$   Trunc_sat_f W32 Unsigned W64   => 0xFCw :: enc_u32 5w
  |N_convert$   Trunc_sat_f W64   Signed W64   => 0xFCw :: enc_u32 6w
  |N_convert$   Trunc_sat_f W64 Unsigned W64   => 0xFCw :: enc_u32 7w

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

  if b = 0x43w then case unlend32 bs of SOME (c32,cs) => (INR $ N_const32 Float c32, cs) | NONE => failure else
  if b = 0x44w then case unlend64 bs of SOME (c64,cs) => (INR $ N_const64 Float c64, cs) | NONE => failure else

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



Overload v_opcode[local] = “λ w. 0xFDw :: enc_u32 w”
Definition enc_vecI_def:
  enc_vecI (i:vec_instr) : byteSeq = case i of

  | V_binary  $   Vswizzle                              => v_opcode  14w
  | V_splat   $          IShp $ Is3 $ Is2 I8x16         => v_opcode  15w
  | V_splat   $          IShp $ Is3 $ Is2 I16x8         => v_opcode  16w
  | V_splat   $          IShp $ Is3       I32x4         => v_opcode  17w
  | V_splat   $          IShp             I64x2         => v_opcode  18w
  | V_splat   $          FShp             F32x4         => v_opcode  19w
  | V_splat   $          FShp             F64x2         => v_opcode  20w
  | V_compare $   Veq  $ IShp $ Is3 $ Is2 I8x16         => v_opcode  35w
  | V_compare $   Vne  $ IShp $ Is3 $ Is2 I8x16         => v_opcode  36w
  | V_compare $   Vlt_     Signed   $ Is2 I8x16         => v_opcode  37w
  | V_compare $   Vlt_   Unsigned   $ Is2 I8x16         => v_opcode  38w
  | V_compare $   Vgt_     Signed   $ Is2 I8x16         => v_opcode  39w
  | V_compare $   Vgt_   Unsigned   $ Is2 I8x16         => v_opcode  40w
  | V_compare $   Vle_     Signed   $ Is2 I8x16         => v_opcode  41w
  | V_compare $   Vle_   Unsigned   $ Is2 I8x16         => v_opcode  42w
  | V_compare $   Vge_     Signed   $ Is2 I8x16         => v_opcode  43w
  | V_compare $   Vge_   Unsigned   $ Is2 I8x16         => v_opcode  44w
  | V_compare $   Veq  $ IShp $ Is3 $ Is2 I16x8         => v_opcode  45w
  | V_compare $   Vne  $ IShp $ Is3 $ Is2 I16x8         => v_opcode  46w
  | V_compare $   Vlt_     Signed   $ Is2 I16x8         => v_opcode  47w
  | V_compare $   Vlt_   Unsigned   $ Is2 I16x8         => v_opcode  48w
  | V_compare $   Vgt_     Signed   $ Is2 I16x8         => v_opcode  49w
  | V_compare $   Vgt_   Unsigned   $ Is2 I16x8         => v_opcode  50w
  | V_compare $   Vle_     Signed   $ Is2 I16x8         => v_opcode  51w
  | V_compare $   Vle_   Unsigned   $ Is2 I16x8         => v_opcode  52w
  | V_compare $   Vge_     Signed   $ Is2 I16x8         => v_opcode  53w
  | V_compare $   Vge_   Unsigned   $ Is2 I16x8         => v_opcode  54w
  | V_compare $   Veq  $ IShp $ Is3       I32x4         => v_opcode  55w
  | V_compare $   Vne  $ IShp $ Is3       I32x4         => v_opcode  56w
  | V_compare $   Vlt_    Signed          I32x4         => v_opcode  57w
  | V_compare $   Vlt_  Unsigned          I32x4         => v_opcode  58w
  | V_compare $   Vgt_    Signed          I32x4         => v_opcode  59w
  | V_compare $   Vgt_  Unsigned          I32x4         => v_opcode  60w
  | V_compare $   Vle_    Signed          I32x4         => v_opcode  61w
  | V_compare $   Vle_  Unsigned          I32x4         => v_opcode  62w
  | V_compare $   Vge_    Signed          I32x4         => v_opcode  63w
  | V_compare $   Vge_  Unsigned          I32x4         => v_opcode  64w
  | V_compare $   Veq $ IShp              I64x2         => v_opcode 214w
  | V_compare $   Vne $ IShp              I64x2         => v_opcode 215w
  | V_compare $   Vlt_s                                 => v_opcode 216w
  | V_compare $   Vgt_s                                 => v_opcode 217w
  | V_compare $   Vle_s                                 => v_opcode 218w
  | V_compare $   Vge_s                                 => v_opcode 219w
  | V_compare $   Veq  $ FShp             F32x4         => v_opcode  65w
  | V_compare $   Vne  $ FShp             F32x4         => v_opcode  66w
  | V_compare $   Vlt                     F32x4         => v_opcode  67w
  | V_compare $   Vgt                     F32x4         => v_opcode  68w
  | V_compare $   Vle                     F32x4         => v_opcode  69w
  | V_compare $   Vge                     F32x4         => v_opcode  70w
  | V_compare $   Veq  $ FShp             F64x2         => v_opcode  71w
  | V_compare $   Vne  $ FShp             F64x2         => v_opcode  72w
  | V_compare $   Vlt                     F64x2         => v_opcode  73w
  | V_compare $   Vgt                     F64x2         => v_opcode  74w
  | V_compare $   Vle                     F64x2         => v_opcode  75w
  | V_compare $   Vge                     F64x2         => v_opcode  76w
  | V_unary       Vnot                                  => v_opcode  77w
  | V_binary      Vand                                  => v_opcode  78w
  | V_binary      VandNot                               => v_opcode  79w
  | V_binary      Vor                                   => v_opcode  80w
  | V_binary      Vxor                                  => v_opcode  81w
  | V_ternary     VbitSelect                            => v_opcode  82w
  | V_test        VanyTrue                              => v_opcode  83w
  | V_unary   $   Vabs $ IShp $ Is3 $ Is2 I8x16         => v_opcode  96w
  | V_unary   $   Vneg $ IShp $ Is3 $ Is2 I8x16         => v_opcode  97w
  | V_unary       Vpopcnt                               => v_opcode  98w
  | V_test    $   VallTrue    $ Is3 $ Is2 I8x16         => v_opcode  99w
  | V_unary   $   Vbitmask    $ Is3 $ Is2 I8x16         => v_opcode 100w
  | V_binary  $   Vnarrow   Signed I8x16                => v_opcode 101w
  | V_binary  $   Vnarrow Unsigned I8x16                => v_opcode 102w
  | V_shift   $   Vshl           $ Is3 $ Is2 I8x16      => v_opcode 107w
  | V_shift   $   Vshr_   Signed $ Is3 $ Is2 I8x16      => v_opcode 108w
  | V_shift   $   Vshr_ Unsigned $ Is3 $ Is2 I8x16      => v_opcode 109w
  | V_binary  $   Vadd $ IShp $ Is3 $ Is2 I8x16         => v_opcode 110w
  | V_binary  $   Vadd_sat_    Signed     I8x16         => v_opcode 111w
  | V_binary  $   Vadd_sat_  Unsigned     I8x16         => v_opcode 112w
  | V_binary  $   Vsub $ IShp $ Is3 $ Is2 I8x16         => v_opcode 113w
  | V_binary  $   Vsub_sat_    Signed     I8x16         => v_opcode 114w
  | V_binary  $   Vsub_sat_  Unsigned     I8x16         => v_opcode 115w
  | V_binary  $   Vmin_   Signed $ Is2 I8x16            => v_opcode 118w
  | V_binary  $   Vmin_ Unsigned $ Is2 I8x16            => v_opcode 119w
  | V_binary  $   Vmax_   Signed $ Is2 I8x16            => v_opcode 120w
  | V_binary  $   Vmax_ Unsigned $ Is2 I8x16            => v_opcode 121w
  | V_binary  $   Vavgr_u I8x16                         => v_opcode 123w
  | V_convert $   VextAdd I8x16   Signed                => v_opcode 124w
  | V_convert $   VextAdd I8x16 Unsigned                => v_opcode 125w
  | V_unary   $   Vabs $ IShp $ Is3 $ Is2 I16x8         => v_opcode 128w
  | V_unary   $   Vneg $ IShp $ Is3 $ Is2 I16x8         => v_opcode 129w
  | V_binary  $   VmulQ15                               => v_opcode 130w
  | V_test    $   VallTrue    $ Is3 $ Is2 I16x8         => v_opcode 131w
  | V_unary   $   Vbitmask    $ Is3 $ Is2 I16x8         => v_opcode 132w
  | V_binary  $   Vnarrow          Signed I16x8         => v_opcode 133w
  | V_binary  $   Vnarrow        Unsigned I16x8         => v_opcode 134w
  | V_convert $   Vextend   Low  (Is2 I8x16)   Signed   => v_opcode 135w
  | V_convert $   Vextend  High  (Is2 I8x16)   Signed   => v_opcode 136w
  | V_convert $   Vextend   Low  (Is2 I8x16) Unsigned   => v_opcode 137w
  | V_convert $   Vextend  High  (Is2 I8x16) Unsigned   => v_opcode 138w
  | V_shift   $   Vshl           $ Is3 $ Is2 I16x8      => v_opcode 139w
  | V_shift   $   Vshr_   Signed $ Is3 $ Is2 I16x8      => v_opcode 140w
  | V_shift   $   Vshr_ Unsigned $ Is3 $ Is2 I16x8      => v_opcode 141w
  | V_binary  $   Vadd $ IShp $ Is3 $ Is2 I16x8         => v_opcode 142w
  | V_binary  $   Vadd_sat_   Signed      I16x8         => v_opcode 143w
  | V_binary  $   Vadd_sat_ Unsigned      I16x8         => v_opcode 144w
  | V_binary  $   Vsub $ IShp $ Is3 $ Is2 I16x8         => v_opcode 145w
  | V_binary  $   Vsub_sat_   Signed      I16x8         => v_opcode 146w
  | V_binary  $   Vsub_sat_ Unsigned      I16x8         => v_opcode 147w
  | V_binary  $   VmulI16                               => v_opcode 149w
  | V_binary  $   Vmin_    Signed   $ Is2 I16x8         => v_opcode 150w
  | V_binary  $   Vmin_  Unsigned   $ Is2 I16x8         => v_opcode 151w
  | V_binary  $   Vmax_    Signed   $ Is2 I16x8         => v_opcode 152w
  | V_binary  $   Vmax_  Unsigned   $ Is2 I16x8         => v_opcode 153w
  | V_binary  $   Vavgr_u I16x8                         => v_opcode 155w
  | V_convert $   VextMul   Low  (Is2 I8x16)   Signed   => v_opcode 156w
  | V_convert $   VextMul  High  (Is2 I8x16)   Signed   => v_opcode 157w
  | V_convert $   VextMul   Low  (Is2 I8x16) Unsigned   => v_opcode 158w
  | V_convert $   VextMul  High  (Is2 I8x16) Unsigned   => v_opcode 159w
  | V_convert $   VextAdd I16x8   Signed                => v_opcode 126w
  | V_convert $   VextAdd I16x8 Unsigned                => v_opcode 127w
  | V_unary   $   Vabs $ IShp $ Is3 I32x4               => v_opcode 160w
  | V_unary   $   Vneg $ IShp $ Is3 I32x4               => v_opcode 161w
  | V_test    $   VallTrue    $ Is3 I32x4               => v_opcode 163w
  | V_unary   $   Vbitmask    $ Is3 I32x4               => v_opcode 164w
  | V_convert $   Vextend   Low  (Is2 I16x8)   Signed   => v_opcode 167w
  | V_convert $   Vextend  High  (Is2 I16x8)   Signed   => v_opcode 168w
  | V_convert $   Vextend   Low  (Is2 I16x8) Unsigned   => v_opcode 169w
  | V_convert $   Vextend  High  (Is2 I16x8) Unsigned   => v_opcode 170w
  | V_shift   $   Vshl           (Is3 I32x4)            => v_opcode 171w
  | V_shift   $   Vshr_   Signed (Is3 I32x4)            => v_opcode 172w
  | V_shift   $   Vshr_ Unsigned (Is3 I32x4)            => v_opcode 173w
  | V_binary  $   Vadd $ IShp $ Is3 I32x4               => v_opcode 174w
  | V_binary  $   Vsub $ IShp $ Is3 I32x4               => v_opcode 177w
  | V_binary  $   VmulI32                               => v_opcode 181w
  | V_binary  $   Vmin_   Signed I32x4                  => v_opcode 182w
  | V_binary  $   Vmin_ Unsigned I32x4                  => v_opcode 183w
  | V_binary  $   Vmax_   Signed I32x4                  => v_opcode 184w
  | V_binary  $   Vmax_ Unsigned I32x4                  => v_opcode 185w
  | V_binary  $   Vdot                                  => v_opcode 186w
  | V_convert $   VextMul   Low  (Is2 I16x8)   Signed   => v_opcode 188w
  | V_convert $   VextMul  High  (Is2 I16x8)   Signed   => v_opcode 189w
  | V_convert $   VextMul   Low  (Is2 I16x8) Unsigned   => v_opcode 190w
  | V_convert $   VextMul  High  (Is2 I16x8) Unsigned   => v_opcode 191w
  | V_unary   $   Vabs $ IShp I64x2                     => v_opcode 192w
  | V_unary   $   Vneg $ IShp I64x2                     => v_opcode 193w
  | V_test    $   VallTrue    I64x2                     => v_opcode 195w
  | V_unary   $   Vbitmask    I64x2                     => v_opcode 196w
  | V_convert $   Vextend   Low  I32x4    Signed        => v_opcode 199w
  | V_convert $   Vextend  High  I32x4    Signed        => v_opcode 200w
  | V_convert $   Vextend   Low  I32x4  Unsigned        => v_opcode 201w
  | V_convert $   Vextend  High  I32x4  Unsigned        => v_opcode 202w
  | V_shift   $   Vshl I64x2                            => v_opcode 203w
  | V_shift   $   Vshr_   Signed I64x2                  => v_opcode 204w
  | V_shift   $   Vshr_ Unsigned I64x2                  => v_opcode 205w
  | V_binary  $   Vadd (IShp I64x2)                     => v_opcode 206w
  | V_binary  $   Vsub (IShp I64x2)                     => v_opcode 209w
  | V_binary  $   VmulI64                               => v_opcode 213w
  | V_convert $   VextMul   Low  I32x4    Signed        => v_opcode 220w
  | V_convert $   VextMul  High  I32x4    Signed        => v_opcode 221w
  | V_convert $   VextMul   Low  I32x4  Unsigned        => v_opcode 222w
  | V_convert $   VextMul  High  I32x4  Unsigned        => v_opcode 223w
  | V_unary   $   Vceil       F32x4                     => v_opcode 103w
  | V_unary   $   Vfloor      F32x4                     => v_opcode 104w
  | V_unary   $   Vtrunc      F32x4                     => v_opcode 105w
  | V_unary   $   Vnearest    F32x4                     => v_opcode 106w
  | V_unary   $   Vabs $ FShp F32x4                     => v_opcode 224w
  | V_unary   $   Vneg $ FShp F32x4                     => v_opcode 225w
  | V_unary   $   Vsqrt       F32x4                     => v_opcode 227w
  | V_binary  $   Vadd $ FShp F32x4                     => v_opcode 228w
  | V_binary  $   Vsub $ FShp F32x4                     => v_opcode 229w
  | V_binary  $   VmulF       F32x4                     => v_opcode 230w
  | V_binary  $   Vdiv        F32x4                     => v_opcode 231w
  | V_binary  $   Vmin        F32x4                     => v_opcode 232w
  | V_binary  $   Vmax        F32x4                     => v_opcode 233w
  | V_binary  $   Vpmin       F32x4                     => v_opcode 234w
  | V_binary  $   Vpmax       F32x4                     => v_opcode 235w
  | V_unary   $   Vceil       F64x2                     => v_opcode 116w
  | V_unary   $   Vfloor      F64x2                     => v_opcode 117w
  | V_unary   $   Vtrunc      F64x2                     => v_opcode 122w
  | V_unary   $   Vnearest    F64x2                     => v_opcode 148w
  | V_unary   $   Vabs $ FShp F64x2                     => v_opcode 236w
  | V_unary   $   Vneg $ FShp F64x2                     => v_opcode 237w
  | V_unary   $   Vsqrt       F64x2                     => v_opcode 239w
  | V_binary  $   Vadd $ FShp F64x2                     => v_opcode 240w
  | V_binary  $   Vsub $ FShp F64x2                     => v_opcode 241w
  | V_binary  $   VmulF       F64x2                     => v_opcode 242w
  | V_binary  $   Vdiv        F64x2                     => v_opcode 243w
  | V_binary  $   Vmin        F64x2                     => v_opcode 244w
  | V_binary  $   Vmax        F64x2                     => v_opcode 245w
  | V_binary  $   Vpmin       F64x2                     => v_opcode 246w
  | V_binary  $   Vpmax       F64x2                     => v_opcode 247w
  | V_convert $   VtruncSat          Signed             => v_opcode 248w
  | V_convert $   VtruncSat        Unsigned             => v_opcode 249w
  | V_convert $   Vconvert   High    Signed             => v_opcode 250w
  | V_convert $   Vconvert   High  Unsigned             => v_opcode 251w
  | V_convert $   VtruncSat0         Signed             => v_opcode 252w
  | V_convert $   VtruncSat0       Unsigned             => v_opcode 253w
  | V_convert $   Vconvert    Low    Signed             => v_opcode 254w
  | V_convert $   Vconvert    Low  Unsigned             => v_opcode 255w
  | V_convert $   Vdemote                               => v_opcode  94w
  | V_convert $   Vpromote                              => v_opcode  95w

  | V_const (w128: word128)                             => (v_opcode 12w) ++ lend128 w128

  | V_lane   (Vextract_           Signed  I8x16)   lidx => (v_opcode 21w) ++ enc_u8 lidx
  | V_lane   (Vextract_         Unsigned  I8x16)   lidx => (v_opcode 22w) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp $ Is3 $ Is2 I8x16)   lidx => (v_opcode 23w) ++ enc_u8 lidx
  | V_lane   (Vextract_           Signed  I16x8)   lidx => (v_opcode 24w) ++ enc_u8 lidx
  | V_lane   (Vextract_         Unsigned  I16x8)   lidx => (v_opcode 25w) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp $ Is3 $ Is2 I16x8)   lidx => (v_opcode 26w) ++ enc_u8 lidx
  | V_lane    VextractI32x4                        lidx => (v_opcode 27w) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp $ Is3       I32x4)   lidx => (v_opcode 28w) ++ enc_u8 lidx
  | V_lane    VextractI64x2                        lidx => (v_opcode 29w) ++ enc_u8 lidx
  | V_lane   (Vreplace $ IShp             I64x2)   lidx => (v_opcode 30w) ++ enc_u8 lidx
  | V_lane   (VextractF                   F32x4)   lidx => (v_opcode 31w) ++ enc_u8 lidx
  | V_lane   (Vreplace $ FShp             F32x4)   lidx => (v_opcode 32w) ++ enc_u8 lidx
  | V_lane   (VextractF                   F64x2)   lidx => (v_opcode 33w) ++ enc_u8 lidx
  | V_lane   (Vreplace $ FShp             F64x2)   lidx => (v_opcode 34w) ++ enc_u8 lidx

  | V_lane (Vshuffle l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 lA lB lC lD lE) lF => (v_opcode 13w) ++
  (FLAT $ MAP enc_u8 [l0; l1; l2; l3; l4; l5; l6; l7; l8; l9; lA; lB; lC; lD; lE; lF])

End

Definition dec_vecI_def:
  dec_vecI ([]:byteSeq) : ((mlstring + vec_instr) # byteSeq) = emErr "dec_vecI" ∧
  dec_vecI (xFD::bs) = let failure = error (xFD::bs) "[dec_vecI]" in

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
  if oc =  77w then (INR $ V_unary       Vnot                                  ,cs) else
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
  if oc = 174w then (INR $ V_binary  $   Vadd $ IShp $ Is3 I32x4               ,cs) else
  if oc = 177w then (INR $ V_binary  $   Vsub $ IShp $ Is3 I32x4               ,cs) else
  if oc = 181w then (INR $ V_binary  $   VmulI32                               ,cs) else
  if oc = 182w then (INR $ V_binary  $   Vmin_    Signed   I32x4               ,cs) else
  if oc = 183w then (INR $ V_binary  $   Vmin_  Unsigned   I32x4               ,cs) else
  if oc = 184w then (INR $ V_binary  $   Vmax_    Signed   I32x4               ,cs) else
  if oc = 185w then (INR $ V_binary  $   Vmax_  Unsigned   I32x4               ,cs) else
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
  if oc = 206w then (INR $ V_binary  $   Vadd $ IShp I64x2                     ,cs) else
  if oc = 209w then (INR $ V_binary  $   Vsub $ IShp I64x2                     ,cs) else
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
  if oc =  94w then (INR $ V_convert     Vdemote                               ,cs) else
  if oc =  95w then (INR $ V_convert     Vpromote                              ,cs) else

  if oc=12w then case unlend128 cs of NONE => failure | SOME (w128, ds) => (INR $ V_const w128,ds) else

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
  dec_tableI ([]:byteSeq) : ((mlstring + table_instr) # byteSeq) = emErr "dec_tableI" ∧
  dec_tableI (b::bs) = let failure = error (b::bs) "[dec_tableI]" in

  if b = 0x25w then   case dec_u32  bs of NONE=>failure| SOME (x,rs) => (INR $ TableSet  x,rs)   else
  if b = 0x26w then   case dec_u32  bs of NONE=>failure| SOME (x,rs) => (INR $ TableGet  x,rs)   else

  if b = 0xFCw then case dec_u32  bs of NONE=>failure| SOME (oc,cs) =>
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
  dec_loadI ([]:byteSeq) : ((mlstring + load_instr) # byteSeq) = emErr "dec_loadI" ∧
  dec_loadI (b::bs) = let failure = error (b::bs) "[dec_loadI]" in

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
  dec_storeI ([]:byteSeq) : ((mlstring + store_instr) # byteSeq) = emErr "dec_storeI" ∧
  dec_storeI (b::bs) = let failure = error (b::bs) "[dec_storeI]" in

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
  dec_memI ([]:byteSeq) : ((mlstring + mem_others) # byteSeq) = emErr "dec_memI" ∧
  dec_memI (b::bs) = let failure = error (b::bs) "[dec_memI]" in

  if b = 0x3Fw then case bs of w0::cs => if B0 w0 then (INR MemorySize,cs) else failure| _ =>failure   else
  if b = 0x40w then case bs of w0::cs => if B0 w0 then (INR MemoryGrow,cs) else failure| _ =>failure   else
  if b = 0xFCw then case dec_u32 bs of NONE=>failure| SOME (oc,cs) =>
    if oc =  8w then case dec_u32 cs of
                     | NONE => failure
                     | SOME (didx,zrst) => case zrst of
                                           | []     => failure
                                           | z::rst => if B0 z then (INR $ MemoryInit didx,rst) else failure
    else
    if oc =  9w then case dec_u32 cs of NONE=>failure| SOME (didx,   rst) =>              (INR $ DataDrop   didx,rst)              else
    if oc = 10w then case cs of z::n::rst => if B0 $ n+z then (INR   MemoryCopy     ,rst) else failure | _ => failure              else
    if oc = 11w then case cs of z::   rst => if B0     z then (INR   MemoryFill     ,rst) else failure | _ => failure              else
    failure
  else
  failure
End



(**********************************************)
(*                                            *)
(*     Top-level Instructions + Controls      *)
(*                                            *)
(**********************************************)

Definition enc_BlkIdx_def:
  enc_BlkIdx (w:word32) = enc_s33 $ w2w w
End

Definition dec_BlkIdx_def:
  dec_BlkIdx (bs:byteSeq) : (word32 # byteSeq) option =
  case dec_s33 bs of NONE=>NONE| SOME (w, rs) =>
    if word_msb w then NONE else SOME ((w2w w):word32,rs)
End

Definition enc_blocktype_def:
  enc_blocktype (bt:blocktype) : byteSeq = case bt of
  | BlkNil    => [0x40w]
  | BlkVal vt => [enc_valtype vt]
  | BlkIdx x  => enc_BlkIdx x
End

Definition dec_blocktype_def:
  dec_blocktype ([]:byteSeq) : ((mlstring + blocktype) # byteSeq) = emErr "dec_blocktype" ∧
  dec_blocktype bs = let failure = error bs "[dec_blocktype]" in

  case bs of []=>failure| b::rs => if b = 0x40w then (INR   BlkNil  , rs) else
  case dec_valtype bs of (INR t ,rs)            =>   (INR $ BlkVal t, rs) | _ =>
  case dec_BlkIdx  bs of SOME (x,rs)            =>   (INR $ BlkIdx x, rs) | _ =>
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
  | Vector     i => SOME $ enc_vecI   i
  | MemRead    i => SOME $ enc_loadI  i
  | MemWrite   i => SOME $ enc_storeI i
  | MemOthers  i => SOME $ enc_memI   i
End

Overload enc_expr       = “enc_instrs T”
Overload enc_instr_list = “enc_instrs F”



(********************)
(*                  *)
(*     Modules      *)
(*                  *)
(********************)

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
  enc_data (d:data) : byteSeq option = ARB
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
(*
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
*)



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
  >> rpt strip_tac
  >> gvs[dec_valtype_def]
  (*
  rw[enc_valtype_def] >> every_case_tac >> rw[dec_valtype_def]
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
  rw[enc_global_def] >> every_case_tac >> rw[dec_global_def, dec_enc_valtype]
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

Theorem NOT_NULL_enc_u32:
  ~(NULL (enc_u32 u))
Proof
  rewrite_tac[enc_unsigned_word_def]
  >> simp[Once enc_num_def]
  >> every_case_tac >> simp[]
QED

Theorem dec_enc_vecI:
  ∀ i rest. dec_vecI (enc_vecI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_vecI i = res’ by simp []
  \\ asm_rewrite_tac []
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_vecI_def]
  \\ simp [AllCaseEqs()]
  \\ rpt strip_tac
  \\ (rpt var_eq_tac
      \\ rewrite_tac [dec_vecI_def,APPEND,NOT_NULL_enc_u32,NULL_APPEND]
      \\ rewrite_tac [GSYM APPEND_ASSOC,dec_enc_u32]
      \\ rewrite_tac [LET_THM]
      \\ CONV_TAC ((RATOR_CONV o RAND_CONV) BETA_CONV)
      \\ rewrite_tac [pair_case_thm,option_case_def]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ rewrite_tac [pair_case_thm,option_case_def]
      \\ CONV_TAC (DEPTH_CONV BETA_CONV)
      \\ rewrite_tac [AllCaseEqs()]
      \\ print_dot_tac
      \\ simp_tac std_ss [n2w_11,EVAL “dimword (:32)”])
  \\ ntac 16 (rewrite_tac [leb128Theory.dec_enc_unsigned_word,GSYM APPEND_ASSOC] \\ simp [])
  \\ (Cases_on `v3` >> rewrite_tac[])
QED

Theorem dec_enc_paraI:
  ∀ i rest. dec_paraI (enc_paraI i ++ rest) = (INR i, rest)
Proof
  rw[enc_paraI_def] >> every_case_tac >>
  rw[dec_paraI_def]
QED

Theorem dec_enc_varI:
  ∀ i rest. dec_varI (enc_varI i ++ rest) = (INR i, rest)
Proof
  rw[enc_varI_def] >> every_case_tac >>
  rw[dec_varI_def, dec_enc_unsigned_word]
QED

Theorem dec_enc_tableI:
  ∀ i rest. dec_tableI (enc_tableI i ++ rest) = (INR i, rest)
Proof
  rw[enc_tableI_def] \\ every_case_tac
    >> simp[dec_tableI_def,GSYM APPEND_ASSOC, Excl"APPEND_ASSOC", enc_2u32_def]
QED

Theorem dec_enc_loadI:
  ∀ i rest. dec_loadI (enc_loadI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_loadI i = res’ by simp [] >> asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_loadI_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac

  \\ (
    pop_assum sym_sub_tac
    >> simp[dec_loadI_def, AllCaseEqs()]
  )
  \\ fs[GSYM APPEND_ASSOC,dec_enc_u32, enc_2u32_def] >> simp[]
  \\ rewrite_tac[GSYM APPEND_ASSOC,dec_enc_u32, enc_2u32_def] >> simp[]
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
  \\ rpt strip_tac
  \\ gvs[dec_storeI_def, dec_enc_2u32]
  \\ rewrite_tac[GSYM APPEND_ASSOC, dec_enc_u32] >> simp[]
  (*
  rw[enc_storeI_def] >> every_case_tac
  >> simp[bvtype_nchotomy]
  >> rw[dec_storeI_def]
  \\ gvs[dec_storeI_def, dec_enc_2u32]
  \\ rewrite_tac[GSYM APPEND_ASSOC, dec_enc_u32] >> simp[]
  *)
QED

Theorem dec_enc_memI:
  ∀ i rest. dec_memI (enc_memI i ++ rest) = (INR i, rest)
Proof
  rpt gen_tac
  \\ ‘∃res. enc_memI i = res’ by simp []
  \\ asm_rewrite_tac []
  \\ pop_assum mp_tac
  \\ rewrite_tac [enc_memI_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
  \\ gvs[dec_memI_def, dec_enc_2u32]
  \\ rewrite_tac [GSYM APPEND_ASSOC, dec_enc_u32]
  \\ simp[dec_enc_u32]
QED

Theorem dec_enc_BlkIdx:
  ∀ w rest. dec_BlkIdx (enc_BlkIdx w ++ rest) = SOME (w, rest)
Proof
  rpt gen_tac
  \\ rw [enc_BlkIdx_def, dec_BlkIdx_def, dec_enc_s33, AllCaseEqs()]
  \\ BBLAST_TAC
QED

Triviality enc_BlkIdx_not_nil:
  ∀ x. enc_BlkIdx x <> []
Proof
  rpt gen_tac
  >> rewrite_tac[enc_BlkIdx_def, enc_s33_def, enc_w7s_def]
  >> gvs[AllCaseEqs()]
QED

Theorem enc_BlkIdx_imp_word_msb:
  ∀ x b bs. enc_BlkIdx x = b::bs ==> word_msb b
Proof
  rpt gen_tac
  \\ rewrite_tac[enc_BlkIdx_def, enc_s33_def, enc_w7s_def, word_msb]
  \\ gvs[AllCaseEqs()]
  \\ rpt strip_tac
  \\
  cheat
QED

Theorem dec_enc_blocktype:
  ∀b rest. dec_blocktype (enc_blocktype b ++ rest) = (INR b, rest)
Proof
  rpt strip_tac
  \\ `∃ val. enc_blocktype b = val` by simp []
  \\ asm_rewrite_tac[]
  \\ pop_assum mp_tac
  \\ rewrite_tac[enc_blocktype_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
  >- gvs[dec_blocktype_def]
  >- (
    gvs[dec_blocktype_def, dec_enc_valtype]
    >> rewrite_tac[enc_valtype_def]
    >> gvs[AllCaseEqs()]
  )
  >- (
    gvs[oneline dec_blocktype_def,dec_valtype_def]
    \\ simp[AllCaseEqs()]
    \\ simp[SF DNF_ss]
    \\ Cases_on `enc_BlkIdx x`
    >> gvs[enc_BlkIdx_not_nil]
    >> reverse $ rpt strip_tac (* reverses the subgoals produced by the following tactic *)
    >- metis_tac[APPEND, dec_enc_BlkIdx]
    >> (
      gvs[]
      >> drule enc_BlkIdx_imp_word_msb
      >> EVAL_TAC
    )
  )
QED

Theorem dec_enc_vector:
  ∀ dec enc x rs1 items encitems rest.
    (dec (enc x ++ rs1) =  (INR x,rs1)) ⇒
    (enc_vector enc items = SOME encitems) ⇒
  (dec_vector dec encitems = (INR items, rest))
Proof
  rpt strip_tac
  \\ pop_assum mp_tac
  \\ rewrite_tac[dec_vector_def, enc_vector_def]
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
  \\
  cheat
QED


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


    if b = 0x02w then (
      case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
        case bs of
        | [] => failure
        | (b::bs) =>
          if b = 0x0Bw then (INR $ Block bTyp body,bs) else failure
    ) else
    if b = 0x03w then
       (case dec_blocktype bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
        case dec_instr_list bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
        case bs of
        | [] => emErr "dec_instr"
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
            error (b::bs) "dec_instr"
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
     case check_len (b::bs) (dec_instr (b::bs)) of (INL err,bs) => (INL err,bs) | (INR i ,bs) =>
     case dec_instr_list bs                     of (INL err,bs) => (INL err,bs) | (INR is,bs) =>
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
  ∀i e. ∃h t. enc_instr e i = SOME (h::t) ⇒ h ≠ 0x0Bw
Proof
  Cases_on ‘i’ >> Cases_on ‘e’ >> simp [Once enc_instr_def]
  >~ [‘enc_varI’] >- (simp [enc_varI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_paraI’] >- (simp [enc_paraI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_numI’] >- (simp [enc_numI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_loadI’] >- (simp [enc_loadI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_storeI’] >- (simp [enc_storeI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_memI’] >- (simp [enc_memI_def] \\ every_case_tac \\ fs [])
  >~ [‘enc_vecI’] >- cheat (* incomplete *)
  >> cheat
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
*)
