(*
  En- & De- coding between CWasm 1.0 AST & Wasm's binary format
*)

Theory      wasm_binary_format
Ancestors   wasmLang leb128 ancillaryOps
Libs        preamble wordsLib

(*  Note:
    enc goes from AST to Wasm Binary format (WBF)
    dec goes from WBF to AST *)

(**********************************)
(*   Misc notations/helpers/etc   *)
(**********************************)

Type byte    = “:word8”
Type byteSeq = “:word8 list”

(* Decoders (take a stream of bytes) and
   produce an element of the CWasm AST
   (or an error) & additionally return
   the remaining bytes (stream) *)
Type dcdr = “:(mlstring + α) # byteSeq”
Overload error = “λ obj str. (INL $ strlit str,obj)”
Overload emErr = “λ str. (INL $ strlit $ "[" ++ str ++ "] : Byte sequence unexpectedly empty.\n",[])”

Overload gt2_32[local] = “λ (n:num). 2 ** 32 ≤ n”
Overload lst_st = “λxs ys. LENGTH xs < LENGTH ys”
Overload lst_se = “λxs ys. LENGTH xs ≤ LENGTH ys”

val _ = monadsyntax.enable_monadsyntax
val _ = monadsyntax.enable_monad "option"

(***************************************************************************)
(*                                                                         *)
(*     (Wasm Binary Format ⇔ WasmCake AST) Functions + shortening thms     *)
(*                                                                         *)
(***************************************************************************)


(*****************************************)
(*   Vectors (not vector instructions)   *)
(*****************************************)

Definition enc_list_def:
  enc_list (encdr:α -> byteSeq) ([]:α list) : byteSeq = []
  ∧
  enc_list encdr (x::xs) = encdr x ++ enc_list encdr xs
End

Definition enc_list_opt_def:
  enc_list_opt (encdr:α -> byteSeq option) ([]:α list) : byteSeq option = SOME []
  ∧
  enc_list_opt encdr (x::xs) = do
    encx  <-              encdr x ;
    encxs <- enc_list_opt encdr xs;
    return $ encx ++ encxs od
End

Definition dec_list_def:
  dec_list (n:num) (dec:byteSeq -> α dcdr) (bs:byteSeq) : α list dcdr =
    let failure = emErr "dec_list" in
    if n = 0 then (INR [],bs)
    else
    case dec                bs of (INL e,rs)=>failure| (INR x , bs) =>
    case dec_list (n-1) dec bs of (INL e,rs)=>failure| (INR xs, bs) =>
    (INR $ x::xs, bs)
End

Theorem dec_list_shortens_maybe_le:
  ∀dec.
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_se rs bs) ⇒
  ∀n bs xs rs. dec_list n dec bs = (INR xs,rs) ⇒
  lst_se rs bs
Proof
     strip_tac \\ strip_tac
  \\ Induct \\ rw[Once dec_list_def, AllCaseEqs()]
  \\ last_x_assum dxrule
  \\ last_x_assum dxrule
  \\ simp[]
QED

Theorem dec_list_shortens_maybe_lt:
  ∀dec.
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_st rs bs) ⇒
  ∀n bs xs rs. dec_list n dec bs = (INR xs,rs) ⇒
  lst_se rs bs
Proof
  rpt strip_tac
  \\ dxrule_at Any dec_list_shortens_maybe_le
  \\ disch_then irule
  \\ rpt strip_tac
  \\ first_x_assum dxrule
  \\ rw[]
QED



Definition enc_vector_def:
  enc_vector (encdr:α -> byteSeq) (xs:α list) : byteSeq option =
    let n = LENGTH xs in
    if gt2_32 n then NONE
    else
    let encxs = enc_list encdr xs in
    SOME $ enc_u32 (n2w n) ++ encxs
End

Definition enc_vector_opt_def:
  enc_vector_opt (encdr:α -> byteSeq option) (xs:α list) : byteSeq option =
    let n = LENGTH xs in
    if gt2_32 n then NONE else
    do
    encxs <- enc_list_opt encdr xs;
    SOME $ enc_u32 (n2w n) ++ encxs od
End

Definition dec_vector_def:
  dec_vector (dec:byteSeq -> α dcdr) (bs:byteSeq) : α list dcdr =
    case dec_u32 bs of
    | NONE => error bs "dec_vec"
    | SOME (w,bs) => dec_list (w2n w) dec bs
End

Theorem dec_vector_shortens_le:
  ∀dec.
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_se rs bs) ⇒
  ∀bs xs rs. dec_vector dec bs = (INR xs,rs) ⇒
  lst_st rs bs
Proof
  rw[dec_vector_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule_all dec_list_shortens_maybe_le
  \\ simp[]
QED

Theorem dec_vector_shortens_lt:
  ∀dec.
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_st rs bs) ⇒
  ∀bs xs rs. dec_vector dec bs = (INR xs,rs) ⇒
  lst_st rs bs
Proof
  rpt strip_tac
  \\ dxrule_at Any dec_vector_shortens_le
  \\ disch_then irule
  \\ rpt strip_tac
  \\ first_x_assum dxrule
  \\ rw[]
QED





(*************)
(*   Types   *)
(*************)

Definition enc_valtype_def:
  enc_valtype (t:valtype) : byteSeq = case t of
  | Tnum   Int W32 => [0x7Fw]
  | Tnum   Int W64 => [0x7Ew]
End

Definition dec_valtype_def:
  dec_valtype ([]:byteSeq) : valtype dcdr = emErr "dec_valtype"
  ∧
  dec_valtype (b::bs) = let failure = error (b::bs) "[dec_valtype]"
  in
  if b = 0x7Fw then (INR $ Tnum   Int W32 ,bs) else
  if b = 0x7Ew then (INR $ Tnum   Int W64 ,bs) else
  failure
End

Theorem dec_valtype_iso:
  ∀b bs t rs. dec_valtype (b::bs) = (INR t,rs) ⇒ rs = bs
Proof
  simp[oneline dec_valtype_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ simp[]
QED

Theorem dec_valtype_shortens:
  ∀bs t rs. dec_valtype bs = (INR t,rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[oneline dec_valtype_def]
QED



Definition enc_functype_def:
  enc_functype (sg:functype) : byteSeq option = do
    argTs <- enc_vector enc_valtype (FST sg);
    resTs <- enc_vector enc_valtype (SND sg);
    return $ 0x60w :: argTs ++ resTs od
End

Definition dec_functype_def:
  dec_functype ([]:byteSeq) : functype dcdr = emErr "dec_functype"
  ∧
  dec_functype (b::bs) = let failure = error (b::bs) "[dec_functype]" in
    if b ≠ 0x60w then failure else
    case dec_vector dec_valtype bs of (INL err, es)=>failure| (INR argTs,cs) =>
    case dec_vector dec_valtype cs of (INL err, es)=>failure| (INR resTs,rs) =>
    (INR (argTs, resTs), rs)
End

Theorem dec_functype_shortens:
  ∀bs xs rs. dec_functype bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’ >> rw[dec_functype_def, AllCaseEqs()]
  \\ assume_tac dec_valtype_shortens
  \\ imp_res_tac dec_vector_shortens_lt
  \\ rw[]
QED



Definition enc_limits_def:
  enc_limits (lim:limits) : byteSeq = case lim of
  | Lunb mn    => 0x00w :: enc_u32  mn
  | Lwmx mn mx => 0x01w :: enc_2u32 mn mx
End

Definition dec_limits_def:
  dec_limits ([]:byteSeq) : limits dcdr = emErr "dec_limits"
  ∧
  dec_limits (b::bs) = let failure = error (b::bs) "[dec_limits]"
  in
  if b = 0x00w then case dec_u32  bs of NONE=>failure| SOME (mn   ,rs) => (INR $ Lunb mn   , rs) else
  if b = 0x01w then case dec_2u32 bs of NONE=>failure| SOME (mn,mx,rs) => (INR $ Lwmx mn mx, rs) else
  failure
End

Theorem dec_limits_shortens:
  ∀bs xs rs. dec_limits bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_limits_def, AllCaseEqs()]
  >>~- ([‘dec_u32’ ], (dxrule dec_u32_shortens  \\ simp[]))
  >>~- ([‘dec_2u32’], (dxrule dec_2u32_shortens \\ simp[]))
QED



Definition enc_globaltype_def:
  enc_globaltype (t:globaltype) : byteSeq = case t of
  | Gconst vt => enc_valtype vt ++ [0x00w]
  | Gmut   vt => enc_valtype vt ++ [0x01w]
End

Definition dec_globaltype_def:
  dec_globaltype (bs:byteSeq) : globaltype dcdr =
    if NULL bs then emErr "dec_globaltype"
    else
    let failure = error bs "[dec_globaltype]"
    in
    case dec_valtype bs of
    | (INR vt,b::bs) => if b = 0x00w then (INR $ Gconst vt, bs) else
                        if b = 0x01w then (INR $ Gmut   vt, bs) else
                        failure
    | _              => failure
End

Theorem dec_globaltype_shortens:
  ∀bs xs rs. dec_globaltype bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_globaltype_def, AllCaseEqs()]
    >> drule dec_valtype_shortens >> rw[]
QED





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
  dec_numI ([]:byteSeq) : num_instr dcdr = emErr "dec_numI"
  ∧
  dec_numI (b::bs) = let failure = error (b::bs) "[dec_numI]"
  in
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
  error (b::bs) "[dec_numI]: Not a numeric instruction"
End

Theorem dec_numI_shortens:
  ∀bs _i rs. dec_numI bs = (INR _i, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_numI_def, AllCaseEqs()]
    >~ [‘dec_s32’] >- (dxrule dec_s32_shortens \\ simp[])
    >~ [‘dec_s64’] >- (dxrule dec_s64_shortens \\ simp[])
    >> rw[]
QED

Theorem dec_numI_error:
  ∀bs e rs. dec_numI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_numI_def, AllCaseEqs()]
QED



Definition enc_paraI_def:
  enc_paraI (i:para_instr) : byteSeq = case i of
  | Drop   => [0x1Aw]
  | Select => [0x1Bw]
End

Definition dec_paraI_def:
  dec_paraI ([]:byteSeq) : para_instr dcdr = emErr "dec_paraI"
  ∧
  dec_paraI (b::bs) = let failure = error (b::bs) "[dec_paraI]"
  in
  if b = 0x1Aw then (INR Drop  , bs) else
  if b = 0x1Bw then (INR Select, bs) else
  failure
End

Theorem dec_paraI_shortens:
  ∀bs _i rs. dec_paraI bs = (INR _i, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_paraI_def, AllCaseEqs()]
  >> rw[]
QED

Theorem dec_paraI_error:
  ∀bs e rs. dec_paraI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_paraI_def, AllCaseEqs()]
QED



Definition enc_varI_def:
  enc_varI (i:var_instr) : byteSeq = case i of
  | LocalGet  x => 0x20w :: enc_unsigned_word x
  | LocalSet  x => 0x21w :: enc_unsigned_word x
  | LocalTee  x => 0x22w :: enc_unsigned_word x
  | GlobalGet x => 0x23w :: enc_unsigned_word x
  | GlobalSet x => 0x24w :: enc_unsigned_word x
End

Definition dec_varI_def:
  dec_varI ([]:byteSeq) : var_instr dcdr = emErr "dec_varI"
  ∧
  dec_varI (b::bs) = let failure = error (b::bs) "[dec_varI]"
  in
  if b = 0x20w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalGet  x,rs) else
  if b = 0x21w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalSet  x,rs) else
  if b = 0x22w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ LocalTee  x,rs) else
  if b = 0x23w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ GlobalGet x,rs) else
  if b = 0x24w then case dec_unsigned_word bs of NONE=>failure| SOME(x,rs) => (INR $ GlobalSet x,rs) else
  error (b::bs) "[dec_varI] : Not a variable instruction.\n"
End

Theorem dec_varI_shortens:
  ∀bs _i rs. dec_varI bs = (INR _i, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_varI_def, AllCaseEqs()]
  >> dxrule dec_u32_shortens
  >> simp[]
QED

Theorem dec_varI_error:
  ∀bs e rs. dec_varI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_varI_def, AllCaseEqs()]
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
  dec_loadI ([]:byteSeq) : load_instr dcdr = emErr "dec_loadI"
  ∧
  dec_loadI (b::bs) = let failure = error (b::bs) "[dec_loadI]"
  in
  if b = 0x28w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  Load    Int                 W32 ofs a,rs) else
  if b = 0x29w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  Load    Int                 W64 ofs a,rs) else
  if b = 0x2Cw then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I8x16    Signed  W32 ofs a,rs) else
  if b = 0x2Dw then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I8x16  Unsigned  W32 ofs a,rs) else
  if b = 0x2Ew then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I16x8    Signed  W32 ofs a,rs) else
  if b = 0x2Fw then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I16x8  Unsigned  W32 ofs a,rs) else
  if b = 0x30w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I8x16    Signed  W64 ofs a,rs) else
  if b = 0x31w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I8x16  Unsigned  W64 ofs a,rs) else
  if b = 0x32w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I16x8    Signed  W64 ofs a,rs) else
  if b = 0x33w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow I16x8  Unsigned  W64 ofs a,rs) else
  if b = 0x34w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow32        Signed      ofs a,rs) else
  if b = 0x35w then case dec_2u32 bs of NONE=>failure|SOME (a,ofs,rs) => (INR $  LoadNarrow32      Unsigned      ofs a,rs) else
  error (b::bs) "[dec_loadI] : Not a load instruction.\n"
End

Theorem dec_loadI_shortens:
  ∀bs _i rs. dec_loadI bs = (INR _i, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_loadI_def, AllCaseEqs()]
  >> dxrule dec_2u32_shortens
  >> simp[]
QED

Theorem dec_loadI_error:
  ∀bs e rs. dec_loadI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_loadI_def, AllCaseEqs()]
QED



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

Definition dec_storeI_def:
  dec_storeI ([]:byteSeq) : store_instr dcdr = emErr "dec_storeI"
  ∧
  dec_storeI (b::bs) = let failure = error (b::bs) "[dec_storeI]"
  in
  if b = 0x36w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store          Int  W32 ofs al,rs) else
  if b = 0x37w then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ Store          Int  W64 ofs al,rs) else
  if b = 0x3Aw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W32 ofs al,rs) else
  if b = 0x3Bw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W32 ofs al,rs) else
  if b = 0x3Cw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I8x16  W64 ofs al,rs) else
  if b = 0x3Dw then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow  I16x8  W64 ofs al,rs) else
  if b = 0x3Ew then case dec_2u32 bs of NONE=>failure| SOME (al,ofs,rs) => (INR $ StoreNarrow32           ofs al,rs) else
  error (b::bs) "[dec_storeI] : Not a store instruction.\n"
End

Theorem dec_storeI_shortens:
  ∀bs _i rs. dec_storeI bs = (INR _i, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_storeI_def, AllCaseEqs()]
  >> dxrule dec_2u32_shortens
  >> simp[]
QED





(**********************************************************************)
(*                                                                    *)
(*     Top-level Instructions (which contains Controlflow instrs)     *)
(*                                                                    *)
(**********************************************************************)

(*******************************)
(*   Ancillary en-/de-coders   *)
(*******************************)

(* Used in enc-dec of Block-y instructions *)
Definition enc_blocktype_def:
  enc_blocktype (bt:blocktype) : byteSeq = case bt of
  | BlkNil    => [0x40w]
  | BlkVal vt => enc_valtype vt
End

Definition dec_blocktype_def:
  dec_blocktype (bs:byteSeq) : blocktype dcdr = let failure = error bs "[dec_blocktype]"
    in
    case bs of [] => emErr "dec_blocktype" | b::rs
    =>
    if   b = 0x40w       then             (INR   BlkNil  , rs) else
    case dec_valtype bs of (INR t ,rs) => (INR $ BlkVal t, rs) | _ => failure
    (* error bs "[dec_blocktype] : Not a blocktype.\n" *)
End

Theorem dec_blocktype_shortens:
  ∀bs _t rs. dec_blocktype bs = (INR _t,rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_blocktype_def, AllCaseEqs()]
    >> imp_res_tac dec_valtype_iso
    >> simp[]
QED



(* Used in BrTable *)
Definition lift_dec_u32_def:
  lift_dec_u32 bs = case dec_u32 bs of
  | NONE        => error bs "[dec_indxs] : not a u32/index."
  | SOME (i,rs) => (INR i,rs) : word32 dcdr
End

Theorem lift_dec_u32_shortens:
  ∀bs xs rs. lift_dec_u32 bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  simp[lift_dec_u32_def, AllCaseEqs()]
QED



(* we specialize/instantiate this particular
   version of enc_/dec_vector just for abstraction *)
Overload enc_indxs = “enc_vector enc_u32”
Overload dec_indxs = “dec_vector lift_dec_u32”

Theorem dec_indxs_shortens:
  ∀ bs xs rs. dec_indxs bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
     rpt strip_tac
  \\ assume_tac lift_dec_u32_shortens
  \\ imp_res_tac dec_vector_shortens_lt
QED



(***************************************************)
(*   Top-level/Control flow instruction EN coder   *)
(***************************************************)

(* As this (following) encoder is a little more complex than
   previously, some notations to cut through the visual noise *)
Overload unrOC = “0x00w:byte”
Overload nopOC = “0x01w:byte”   (* OC := opcode *)
Overload blkOC = “0x02w:byte”
Overload lopOC = “0x03w:byte”
Overload if_OC = “0x04w:byte”
Overload br_OC = “0x0Cw:byte”
Overload briOC = “0x0Dw:byte”
Overload brtOC = “0x0Ew:byte”
Overload retOC = “0x0Fw:byte”
Overload calOC = “0x10w:byte”
Overload rclOC = “0x12w:byte”
Overload cinOC = “0x11w:byte”
Overload rciOC = “0x13w:byte”

(* [Note] "Special"/specific bytes that serve as terminators in byte streams encoding lists
   (not Wasm vectors!) of instructions. Else where in Wasm, "collections/lists" of items
   are encoded as (Wasm) vectors -- which are led with an encoding of the vectors length *)
Overload elseB = “0x05w:byte”
Overload endB  = “0x0Bw:byte”

(* "Expressions" in Wasm are lists of instructions terminated by the
    byte 0x0B (Cf. endB Overload & it's corresponding comment/note)
    (**)
    Most places where lists of instructions show up in WBF encoding, they
    are expressions -- save for the then-arm of an (dual-armed ie, has both
    then and else cases) if instruction -- where the encoding is instead
    terminated with 0x05 (Cf. elseB above)
    (**)
    So we use a boolean flag to indicate which terminator byte to encode
    (**)
    TODO: check that endB & elseB are the only terminating
    bytes for encoding lists of instructions *)
Definition enc_instr_def:
  (enc_instr_list (e:bool) ([]:instr list) : byteSeq option = SOME [if e then endB else elseB]
  ) ∧
  (enc_instr_list _encode_expr (i::is) = do
    enci  <- enc_instr                   i ;
    encis <- enc_instr_list _encode_expr is;
    SOME $ enci ++ encis od
  ) ∧
  enc_instr (inst:instr) : byteSeq option = case inst of
  (* control instructions *)
  | Unreachable => SOME [unrOC]
  | Nop         => SOME [nopOC]
  (* block-y *)
  | Block bT body => do encb <- enc_instr_list T body; SOME $ blkOC :: enc_blocktype bT ++ encb         od
  | Loop  bT body => do encb <- enc_instr_list T body; SOME $ lopOC :: enc_blocktype bT ++ encb         od
  | If bT bdT bdE => do enct <- enc_instr_list F bdT ;
                        ence <- enc_instr_list T bdE ; SOME $ if_OC :: enc_blocktype bT ++ enct ++ ence od
  | If bT bdT []  => do enct <- enc_instr_list T bdT ; SOME $ if_OC :: enc_blocktype bT ++ enct         od
  (* branches *)
  | Br           lbl =>                               SOME $ br_OC ::            enc_u32 lbl
  | BrIf         lbl =>                               SOME $ briOC ::            enc_u32 lbl
  | BrTable lbls lbl => do enclbls <- enc_indxs lbls; SOME $ brtOC :: enclbls ++ enc_u32 lbl od
  (* calls/returns *)
  | Return                    =>                              SOME  [retOC]
  | Call               fdx    =>                              SOME $ calOC ::          enc_u32 fdx
  | ReturnCall         fdx    =>                              SOME $ rclOC ::          enc_u32 fdx
  | CallIndirect       fdx sg => do encsg <- enc_functype sg; SOME $ cinOC :: encsg ++ enc_u32 fdx od
  | ReturnCallIndirect fdx sg => do encsg <- enc_functype sg; SOME $ rciOC :: encsg ++ enc_u32 fdx od
  (* other classes of instructions *)
  | Variable   i => SOME $ enc_varI   i
  | Parametric i => SOME $ enc_paraI  i
  | Numeric    i => SOME $ enc_numI   i
  | MemRead    i => SOME $ enc_loadI  i
  | MemWrite   i => SOME $ enc_storeI i
End

Overload enc_expr = “enc_instr_list T”  (* byte stream terminated with an endB  *)
Overload enc_tArm = “enc_instr_list F”  (* byte stream terminated with an elseB *)



(***************************************************)
(*   Top-level/Control flow instruction DE coder   *)
(***************************************************)

(* Used in termination proof. 2nd argument seems slightly
   mysterious but [shorten] will be called in a specific pattern:
   (**)
   λdec xs. shorten xs (dec xs)
   (**)
   and it helps with termination by saying that if the decoder
   does not produce a shorter byte stream, we explicitly
   replace the byte stream with one that is shorter/equal length *)
Definition shorten_def:
  (shorten bs (INR x,rs) = if lst_st rs bs then (INR x,rs) else (INR x,[])) ∧
  (shorten bs (INL x,rs) = if lst_se rs bs then (INL x,rs) else (INL x,bs))
End

Overload force_shtr = “λdec xs. shorten xs (dec xs)”

Theorem shorten_IMP:
  ∀xs bs x s. shorten bs xs = (INR x,rs)
  ⇒
  (lst_se rs bs) ∧ (bs ≠ [] ⇒ lst_st rs bs)
Proof
  rpt gen_tac
  \\ PairCases_on ‘xs’
  \\ Cases_on ‘xs0’
  >> rw [shorten_def, AllCaseEqs()]
    >> simp[]
    \\ Cases_on ‘bs’ \\ fs[]
QED


(* Decoding lists of instructions additionally returns the terminating byte, allowing
   the decoder to see if the then-arm of an if-instruction is (or is not) followed by
   (the encoding of) an else-arm *)
Definition dec_instr_def:
  (dec_instr_list (_elseB_allowed:bool) ([]:byteSeq) : (byte # instr list) dcdr = emErr "dec_instr_list"
  ) ∧
  (dec_instr_list e (b::bs) =
    let failure = error (b::bs) "[dec_instr_list]"
    in
    if b = endB ∨ (e ∧ b = elseB) then (INR (b,[]),bs)
    else
    case force_shtr dec_instr (b::bs) of (INL err,bs)=>failure| (INR i         ,bs) =>
    case dec_instr_list e bs          of (INL err,bs)=>failure| (INR (termB,is),bs) =>
    (INR $ (termB, i::is), bs)
  ) ∧
  (dec_instr ([]:byteSeq) : instr dcdr = emErr "dec_instr"
  ) ∧
  (dec_instr (b::bs) = let failure = error (b::bs) "[dec_instr]" in
    (* Single-byte encoded instrs *)
    if b = unrOC then (INR Unreachable, bs) else
    if b = nopOC then (INR Nop        , bs) else
    if b = retOC then (INR Return     , bs) else
    (* Br, BrIf *)
    if b = br_OC then case dec_u32 bs of NONE=>failure|SOME (lbl,rs) => (INR $ Br   lbl,rs) else
    if b = briOC then case dec_u32 bs of NONE=>failure|SOME (lbl,rs) => (INR $ BrIf lbl,rs) else
    (* BrTable *)
    if b = brtOC then (
      case dec_indxs bs of (INL _,_) => failure | (INR  lbls,cs) =>
      case dec_u32   cs of      NONE => failure | SOME (lbl ,rs) =>
      (INR $ BrTable lbls lbl, rs)                           ) else
    (* Calls *)
    if b = calOC then case dec_u32 bs of NONE => failure | SOME (f,rs) => (INR $ Call       f, rs) else
    if b = rclOC then case dec_u32 bs of NONE => failure | SOME (f,rs) => (INR $ ReturnCall f, rs) else
    if b = cinOC then case dec_functype bs of (INL _,_)=>failure|(INR sg,cs) =>
                      case dec_u32      cs of NONE     =>failure|SOME (f,rs) => (INR $ CallIndirect       f sg,rs) else
    if b = rciOC then case dec_functype bs of (INL _,_)=>failure|(INR sg,cs) =>
                      case dec_u32      cs of NONE     =>failure|SOME (f,rs) => (INR $ ReturnCallIndirect f sg,rs) else
    (* Block-y instructrions ie, instructions with embedded blocks *)
    (* Block *)
    if b = blkOC then (
      case dec_blocktype    bs of (INL err,bs) =>failure| (INR bTyp    ,bs) =>
      case dec_instr_list F bs of (INL err,bs) =>failure| (INR (_,body),bs) =>
      (INR (Block bTyp body),bs)                                        ) else
    (* Loop *)
    if b = lopOC then (
      case dec_blocktype    bs of (INL err,bs) =>failure| (INR bTyp    ,bs) =>
      case dec_instr_list F bs of (INL err,bs) =>failure| (INR (_,body),bs) =>
      (INR (Loop bTyp body),bs)                                         ) else
    (* If then only *)
    if b = if_OC then (
      case dec_blocktype bs                 of (INL err,bs) =>failure| (INR bTyp        ,bs) =>
      case force_shtr (dec_instr_list T) bs of (INL err,bs) =>failure| (INR (termB,bdyT),bs) =>
      if termB = endB then
      (INR (If bTyp bdyT []),bs)
    else (* termB = elseB *)
    (* If both *)
      case dec_instr_list F bs of (INL err,bs) =>failure| (INR (_,bdyE),bs) =>
      (INR (If bTyp bdyT bdyE),bs)                                      ) else
    (* other classes of instructions *)
    case dec_varI   (b::bs) of (INR i, rs) => (INR $ Variable   i, rs) | _ =>
    case dec_paraI  (b::bs) of (INR i, rs) => (INR $ Parametric i, rs) | _ =>
    case dec_numI   (b::bs) of (INR i, rs) => (INR $ Numeric    i, rs) | _ =>
    case dec_loadI  (b::bs) of (INR i, rs) => (INR $ MemRead    i, rs) | _ =>
    case dec_storeI (b::bs) of (INR i, rs) => (INR $ MemWrite   i, rs) | _ =>
  failure)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL (_, bs) => 2 * LENGTH bs + 1  (* measure for the first (dec_instr_list) fn *)
                            | INR bs      => 2 * LENGTH bs’     (* measure for the second (dec_instr)     fn *)
  \\ rw []
  >> imp_res_tac dec_blocktype_shortens
  >> imp_res_tac shorten_IMP
  >> fs []
End

(* dec_expr _insists_ terminal byte must be endB. Hence, we can throw it away *)
(* dec_tArm _allows_ terminal byte to be elseB (or endB) *)
Overload dec_expr = “λ bs. case dec_instr_list F bs of (INR (_,is), bs) => (INR is, bs) | (INL e,cs) => (INL e,cs)”
Overload dec_tArm = “dec_instr_list T”

Theorem dec_instructions_shorten:
  (∀e xs x rs. dec_instr_list e xs = (INR x,rs) ⇒ lst_st rs xs) ∧
  (∀xs x rs  . dec_instr        xs = (INR x,rs) ⇒ lst_st rs xs)
Proof
  ho_match_mp_tac dec_instr_ind \\ rw []
  >~ [‘dec_instr        []’] >- simp [dec_instr_def]
  >~ [‘dec_instr_list b []’] >- simp [dec_instr_def]
    >> pop_assum mp_tac
    >> simp[Once dec_instr_def]
    >> strip_tac
    >> gvs[AllCaseEqs()]
    >> imp_res_tac shorten_IMP
    >> imp_res_tac dec_u32_shortens
    >> imp_res_tac dec_functype_shortens
    >> imp_res_tac dec_blocktype_shortens
    >> imp_res_tac dec_indxs_shortens
    >> imp_res_tac dec_varI_shortens
    >> imp_res_tac dec_paraI_shortens
    >> imp_res_tac dec_numI_shortens
    >> imp_res_tac dec_loadI_shortens
    >> imp_res_tac dec_storeI_shortens
    >> fs[]
QED

(* In error case, decoder doesn't return a longer byte stream *)
Theorem dec_instructions_error:
  (∀e bs x rs. dec_instr_list e bs = (INL x,rs) ⇒ rs = bs) ∧
  (∀  bs x rs. dec_instr        bs = (INL x,rs) ⇒ rs = bs)
Proof
  conj_tac
    >> Cases_on ‘bs’
    >> simp[Once $ oneline dec_instr_def, AllCaseEqs()]
    >> rpt strip_tac
    >> simp[]
QED

Theorem dec_instructions_short_enough:  (* to never need to be forced to be shorter *)
  (∀e bs. force_shtr (dec_instr_list e) bs = dec_instr_list e bs) ∧
  (∀  bs. force_shtr  dec_instr         bs = dec_instr        bs)
Proof
  conj_tac >> rpt gen_tac
  >-(
    Cases_on ‘dec_instr_list e bs’ \\ Cases_on ‘q’
    >> imp_res_tac dec_instructions_error
    >> imp_res_tac dec_instructions_shorten
    >> simp[shorten_def]
  ) \\
    Cases_on ‘dec_instr bs’ \\ Cases_on ‘q’
    >> imp_res_tac dec_instructions_error
    >> imp_res_tac dec_instructions_shorten
    >> simp[shorten_def]
QED
(* The above thm demonstrates that the force_shtr calls -- while useful/necessary
   for proving termination -- are actually not necessary in general *)

(* So, we can excise those force-shorter calls from the decoders' definitions *)
Theorem dec_instr_def[allow_rebind] = REWRITE_RULE [dec_instructions_short_enough] dec_instr_def;
Theorem dec_instr_ind[allow_rebind] = REWRITE_RULE [dec_instructions_short_enough] dec_instr_ind;



Triviality dec_instr_list_shortens:
  (∀e xs x rs. dec_instr_list e xs = (INR x,rs) ⇒ lst_st rs xs)
Proof
  rewrite_tac[dec_instructions_shorten]
QED



(*******************)
(*                 *)
(*     Modules     *)
(*                 *)
(*******************)

(*******************)
(*   Ancillaries   *)
(*******************)

Definition enc_global_def:
  enc_global (g:global) : byteSeq option = do
    expr <- enc_expr g.ginit;
    SOME $ enc_globaltype g.gtype ++ expr od
End

Definition dec_global_def:
  dec_global (bs:byteSeq) : global dcdr =
    if NULL bs then emErr "dec_global"
    else
    let failure = error bs "[dec_global]"
    in
    case dec_globaltype bs of (INL _,_) => failure | (INR gt, bs) =>
    case dec_expr       bs of (INL _,_) => failure | (INR ex, bs) =>
      (INR <| gtype := gt
            ; ginit := ex
            |> : mlstring + global
      , bs)
End

Theorem dec_global_shortens:
  ∀bs xs rs. dec_global bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  rw[dec_global_def, AllCaseEqs()]
  \\ dxrule dec_globaltype_shortens
  \\ dxrule dec_instr_list_shortens
  \\ rw[]
QED



Definition enc_code_def:
  enc_code (c:valtype list # expr) : byteSeq option = do
    encC <- enc_expr               (SND c);
    encL <- enc_vector enc_valtype (FST c);
    let code = encL ++ encC in
    SOME $ enc_u32 (n2w $ LENGTH code) ++ code od
End

Definition dec_code_def:
  dec_code (bs:byteSeq) : (valtype list # expr) dcdr =
  if NULL bs then emErr "dec_code" else
  let failure = error bs "[dec_code]" in
    case dec_u32                bs of  NONE    =>failure|SOME (len,cs) =>
    case dec_vector dec_valtype cs of (INL _,_)=>failure|(INR vts ,ds) =>
    case dec_expr               ds of (INL _,_)=>failure|(INR code,rs) =>
    (INR (vts, code), rs)
End

Theorem dec_code_shortens:
  ∀ bs xs rs. dec_code bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_code_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ assume_tac dec_valtype_shortens
  \\ dxrule_all dec_vector_shortens_lt
  \\ dxrule dec_instr_list_shortens
  \\ simp[]
QED



Definition enc_data_def:
  enc_data (d:data) : byteSeq option = do
    ini <- enc_vector (λ b. [b]) d.dinit;
    ofs <- enc_expr d.offset            ;
    SOME $ enc_u32 d.data ++ ofs ++ ini od
End

(* Used in dec_data *)
Definition dec_byte_def:
  dec_byte ([]:byteSeq) : byte dcdr = error [] "bogus" ∧
  dec_byte (b::bs) = (INR b, bs)
End

Theorem dec_byte_shortens:
  ∀bs b rs. dec_byte bs = (INR b, rs) ⇒ lst_st rs bs
Proof
  Cases >> rw[dec_byte_def]
QED


Definition dec_data_def:
  dec_data (bs:byteSeq) : data dcdr =
    if NULL bs then emErr "dec_data" else
    let failure = error bs "[dec_data]"
    in
    case dec_u32             bs of  NONE     =>failure| SOME (idx,bs) =>
    case dec_expr            bs of (INL _,_) =>failure| (INR ofse,bs) =>
    case dec_vector dec_byte bs of (INL _,_) =>failure| (INR ini ,rs) =>
      (INR <| data   := idx
            ; offset := ofse
            ; dinit  := ini
            |>
      , rs)
End

Theorem dec_data_shortens:
  ∀bs xs rs. dec_data bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
     rw[dec_data_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule dec_instr_list_shortens
  \\ drule_at Any dec_vector_shortens_lt
  \\ simp[dec_byte_shortens]
QED



(* Used in enc_/dec_module *)
Definition split_funcs_def:
  split_funcs ([]:func list) =
    ( [] :  index                list
    , [] : (valtype list # expr) list
    , [] :  mlstring             list
    , [] :  mlstring list        list )
  ∧
  split_funcs (f::fs) = let
    ( typs
    , lBods
    , func_names
    , local_names ) = split_funcs fs
    in
    ( f.ftype            :: typs
    ,(f.locals, f.body)  :: lBods
    , f.fname            :: func_names
    , f.lnames           :: local_names
    )
End

Definition zip_funcs_def:
  zip_funcs ([] :  index                list)
            (_  : (valtype list # expr) list)
            (_  :  mlstring             list)
            (_  :  mlstring list        list) = [] : func list
  ∧
  zip_funcs _ [] _ _ = [] ∧
  zip_funcs _ _ [] _ = [] ∧
  zip_funcs _ _ _ [] = [] ∧
  zip_funcs ( fi            :: is   )
            ( (vs,e)        :: vles )
            ( func_name     :: fns  )
            ( local_names   :: lns  ) =
  (<| ftype  := fi
    ; locals := vs
    ; body   := e
    ; fname  := func_name
    ; lnames := local_names
    |> : func)
  :: zip_funcs is vles fns lns
End



Definition enc_section_def:
  enc_section (leadByte:byte) (enc:α -> byteSeq)  (xs:α list) : byteSeq option =
    do encxs <- enc_vector enc xs;
    SOME $ leadByte :: enc_u32 (n2w $ LENGTH encxs) ++ encxs od
End

Definition enc_section_opt_def:
  enc_section_opt (leadByte:byte) (enc:α -> byteSeq option) (xs:α list) : byteSeq option =
    do encxs <- enc_vector_opt enc xs;
    SOME $ leadByte :: enc_u32 (n2w $ LENGTH encxs) ++ encxs od
End

Definition dec_section_def:
  dec_section ( _:byte)
              ( _:byteSeq -> α dcdr)
              ([]:byteSeq) : (α list) dcdr = emErr "dec_section"
  ∧
  dec_section leadByte dec (b::bs) =
    let failure = error bs "dec_section"
    in
    if b ≠ leadByte then (INR [], b::bs)
    else
    case dec_u32 bs of NONE => failure | SOME (w,bs) =>
    case dec_vector dec bs of
    | (INR res,bs) => (INR res, bs)
    | _            => failure
End

Theorem dec_section_shortens:
  ∀dec.
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_st rs bs) ⇒
  ∀bs lb dc rs. dec_section lb dec bs = (INR dc, rs) ⇒ lst_se rs bs
Proof
  strip_tac \\ strip_tac
  \\ Cases >> rw[dec_section_def, AllCaseEqs()]
    >> simp[]
    \\ dxrule dec_u32_shortens
    \\ dxrule_all dec_vector_shortens_lt
    \\ simp[]
QED



Definition mod_leader_def:
  (* this magic num/list must lead all WBF encoded modules *)
  mod_leader : byteSeq = [
    0x00w; 0x61w; 0x73w; 0x6Dw;   (* "\0asm"                      *)
    0x01w; 0x00w; 0x00w; 0x00w]   (* version number of Bin format *)
End



(* From CWasm (not Wasm!) modules to WBF *)
Definition enc_module_def:
  enc_module (m:module) : byteSeq option =
    let (fTIdxs, locBods, fns, lns) = split_funcs m.funcs in do
    types'   <- enc_section_opt   1w enc_functype  m.types  ;
    fTIdxs'  <- enc_section       3w enc_u32       fTIdxs   ;
    mems'    <- enc_section       5w enc_limits    m.mems   ;
    globals' <- enc_section_opt   6w enc_global    m.globals;
    code'    <- enc_section_opt  10w enc_code      locBods  ;
    datas'   <- enc_section_opt  11w enc_data      m.datas  ;
      SOME $ mod_leader ++
      types'   ++ fTIdxs' ++ mems'  ++
      globals' ++ code'   ++ datas' ++ [] od
End



Definition dec_module_def:
  dec_module (bs:byteSeq) : module dcdr = case bs of
  | l1::l2::l3::l4::l5::l6::l7::l8::xs => (
    let failure = error bs "[dec_module] : malformed leader"
    in
    if [l1;l2;l3;l4;l5;l6;l7;l8] ≠ mod_leader then failure
    else
    case dec_section  1w dec_functype xs of (INL _,_)=>failure|(INR types'  , xs) =>
    case dec_section  3w lift_dec_u32 xs of (INL _,_)=>failure|(INR fTIdxs  , xs) =>
    case dec_section  5w dec_limits   xs of (INL _,_)=>failure|(INR mems'   , xs) =>
    case dec_section  6w dec_global   xs of (INL _,_)=>failure|(INR globals', xs) =>
    case dec_section 10w dec_code     xs of (INL _,_)=>failure|(INR code    , xs) =>
    case dec_section 11w dec_data     xs of (INL _,_)=>failure|(INR datas'  , rs) =>
    let funcs' = zip_funcs fTIdxs code [] [] in
    let m = <| types   := types' ; funcs   := funcs'
             ; mems    := mems'  ; globals := globals'
             ; datas   := datas' ; mname   := strlit ("")   |> : module
    in
    (INR m, rs) )
  | [] => emErr "dec_module"
  | _  => error bs "[dec_module]: missing leader (less than 8 bytes)"
End

Theorem dec_module_shortens:
  ∀bs x rs. dec_module bs = (INR x, rs) ⇒ lst_se rs bs
Proof
     simp[dec_module_def, AllCaseEqs(), mod_leader_def]
  \\ rpt strip_tac \\ gvs[]
  \\ rpt (dxrule_at Any dec_section_shortens)
  \\ simp[dec_functype_shortens, dec_limits_shortens, dec_code_shortens
         ,lift_dec_u32_shortens, dec_global_shortens, dec_data_shortens]
QED

