(*
  En- & De- coding between CWasm 1.0 AST & Wasm's binary format
*)

Theory      wasm_binary_format
Ancestors   wasmLang leb128 ancillaryOps
Libs        preamble wordsLib

(*  Note:
    enc goes from AST to Wasm Binary format (WBF)
    dec goes from WBF to AST *)

(********************************)
(*   Misc notations/helps/etc   *)
(********************************)

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”

Overload zeroB = “0x00w:byte”
Overload elseB = “0x05w:byte”
Overload endB  = “0x0Bw:byte”
(* Overload b0[local]    = “(λ x. x = zeroB):byte -> bool” *)

Type dcdr[local] = “:(mlstring + α) # byteSeq”
Overload error[local] = “λ obj str. (INL $ strlit str,obj)”
Overload emErr[local] = “λ str. (INL $ strlit $ "[" ++ str ++ "] : Byte sequence unexpectedly empty.\n",[])”

Overload gt2_32[local] = “λ (n:num). 2 ** 32 ≤ n”
Overload lst_st = “λxs ys. LENGTH xs < LENGTH ys”
Overload lst_se = “λxs ys. LENGTH xs ≤ LENGTH ys”

val _ = monadsyntax.enable_monadsyntax
val _ = monadsyntax.enable_monad "option"

(********************************************************)
(*                                                      *)
(*     Wasm Binary Format ⇔ WasmCake AST Functions     *)
(*                                                      *)
(********************************************************)


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
  dec_list (n:num) decdr bs =
    if n = 0 then (INR [],bs) else
    case decdr bs of
    | (INL err, rs) => (INL err, rs)
    | (INR x  , bs) =>
      case dec_list (n-1) decdr bs of
      | (INL err, rs) => (INL err, rs)
      | (INR xs , bs) => (INR $ x::xs, bs)
End

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
    return $ enc_u32 (n2w n) ++ encxs od
End

Definition dec_vector_def:
  dec_vector (dec:byteSeq -> α dcdr) (bs:byteSeq) : α list dcdr =
    case dec_u32 bs of
    | NONE => error bs "dec_vec"
    | SOME (w,bs) => dec_list (w2n w) dec bs
End


Theorem dec_list_shortens_maybe_lt:
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_st rs bs) ⇒
  ∀n bs xs. dec_list n dec bs = (INR xs,rs) ⇒
  lst_se rs bs
Proof
     strip_tac
  \\ Induct \\ rw[Once dec_list_def]
  \\ gvs[AllCaseEqs()]
  \\ first_x_assum drule
  \\ first_x_assum drule
  \\ simp[]
QED

Theorem dec_list_shortens_maybe_le:
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_se rs bs) ⇒
  ∀n bs xs. dec_list n dec bs = (INR xs,rs) ⇒
  lst_se rs bs
Proof
     strip_tac
  \\ Induct \\ rw[Once dec_list_def]
  \\ gvs[AllCaseEqs()]
  \\ first_x_assum drule
  \\ first_x_assum drule
  \\ simp[]
QED

Theorem dec_vector_shortens_le[simp]:
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_se rs bs) ⇒
  ∀bs xs. dec_vector dec bs = (INR xs,rs) ⇒
  lst_st rs bs
Proof
  rw[dec_vector_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule_all dec_list_shortens_maybe_le
  \\ rw[]
QED

Theorem dec_vector_shortens_lt[simp]:
  (∀bs x rs. dec bs = (INR x, rs) ⇒ lst_st rs bs) ⇒
  ∀bs xs. dec_vector dec bs = (INR xs,rs) ⇒
  lst_st rs bs
Proof
  rw[dec_vector_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule_all dec_list_shortens_maybe_lt
  \\ rw[]
QED



(*************)
(*   Types   *)
(*************)

Definition enc_valtype_def:
  enc_valtype (t:valtype) : byte = case t of
  | Tnum   Int W32 => 0x7Fw
  | Tnum   Int W64 => 0x7Ew
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

Overload enc_valtype_Seq = “λ t. [enc_valtype t] : byteSeq”

Theorem dec_valtype_shortens:
  ∀bs t rs. dec_valtype bs = (INR t,rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[oneline dec_valtype_def, AllCaseEqs()]
  >> rw[]
QED

Theorem dec_valtype_iso:
  ∀ b bs t rs. dec_valtype (b::bs) = (INR t,rs) ⇒ bs = rs
Proof
  simp[oneline dec_valtype_def, AllCaseEqs()] \\ rpt strip_tac
QED



Definition enc_functype_def:
  enc_functype (sg:functype) : byteSeq option = do
    argTs <- enc_vector enc_valtype_Seq (FST sg);
    resTs <- enc_vector enc_valtype_Seq (SND sg);
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
  \\ dxrule_all dec_vector_shortens_lt
  \\ assume_tac dec_valtype_shortens
  \\ dxrule_all dec_vector_shortens_lt
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

Theorem dec_limits_shortens[simp]:
  ∀bs xs rs. dec_limits bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_limits_def, AllCaseEqs()]
  >~ [‘dec_u32’]  >- (dxrule dec_u32_shortens  \\ simp[])
  >~ [‘dec_2u32’] >- (dxrule dec_2u32_shortens \\ simp[])
QED



Definition enc_globaltype_def:
  enc_globaltype (t:globaltype) : byteSeq = case t of
  | Gconst vt => enc_valtype vt :: [0x00w]
  | Gmut   vt => enc_valtype vt :: [0x01w]
End

Definition dec_globaltype_def:
  dec_globaltype ([]:byteSeq) : globaltype dcdr = emErr "dec_globaltype"
  ∧
  dec_globaltype bs = let failure = error bs "[dec_globaltype]"
  in
  case dec_valtype bs of (INL _,_) => failure         | (INR vt, bs) =>
  case bs             of [] => emErr "dec_globaltype" |  b  ::   bs  =>
  if b = 0x00w then (INR $ Gconst vt, bs) else
  if b = 0x01w then (INR $ Gmut   vt, bs) else
  failure
End

Theorem dec_globaltype_shortens[simp]:
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

Theorem dec_numI_shortens[simp]:
  ∀bs xs rs. dec_numI bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_numI_def, AllCaseEqs()]
    >~ [‘dec_s32’] >- (dxrule dec_s32_shortens \\ simp[])
    >~ [‘dec_s64’] >- (dxrule dec_s64_shortens \\ simp[])
    >> rw[]
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

Theorem dec_paraI_shortens[simp]:
  ∀bs xs rs. dec_paraI bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_paraI_def, AllCaseEqs()]
  >> rw[]
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

Theorem dec_varI_shortens[simp]:
  ∀bs xs rs. dec_varI bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_varI_def, AllCaseEqs()]
  >> dxrule dec_u32_shortens
  >> simp[]
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

Theorem dec_loadI_shortens[simp]:
  ∀bs xs rs. dec_loadI bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_loadI_def, AllCaseEqs()]
  >> dxrule dec_2u32_shortens
  >> simp[]
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

Theorem dec_storeI_shortens[simp]:
  ∀bs xs rs. dec_storeI bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’
  >> rw[dec_storeI_def, AllCaseEqs()]
  >> dxrule dec_2u32_shortens
  >> simp[]
QED



(*********************************************)
(*                                           *)
(*     Top-level Instructions + Controls     *)
(*                                           *)
(*********************************************)

Definition enc_blocktype_def:
  enc_blocktype (bt:blocktype) : byteSeq = case bt of
  | BlkNil    => [0x40w]
  | BlkVal vt => [enc_valtype vt]
End

Definition dec_blocktype_def:
  dec_blocktype ([]:byteSeq) : blocktype dcdr = emErr "dec_blocktype"
  ∧
  dec_blocktype bs = let failure = error bs "[dec_blocktype]"
  in
  case bs of []=>failure| b::rs => if b = 0x40w then (INR   BlkNil  , rs) else
  case dec_valtype bs of (INR t ,rs)            =>   (INR $ BlkVal t, rs) | _ =>
  error (b::bs) "[dec_blocktype] : Not a blocktype.\n"
End

Theorem dec_blocktype_shortens:
  ∀ bs t rs. dec_blocktype bs = (INR t,rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘bs’ >> simp[dec_blocktype_def]
  \\ rpt gen_tac
  \\ simp[AllCaseEqs()]
  \\ rpt strip_tac
  >> gvs[]
  \\ drule dec_valtype_iso
  \\ simp[]
QED



Definition lift_dec_u32_def:
  lift_dec_u32 bs = case dec_u32 bs of
    | NONE        => error bs "[dec_indxs] : not a u32/index."
    | SOME (i,rs) => (INR i,rs)
End

Overload enc_indxs = “enc_vector enc_u32”
Overload dec_indxs = “dec_vector lift_dec_u32”

Theorem lift_dec_u32_shortens[simp]:
  ∀bs xs rs. lift_dec_u32 bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  Cases_on ‘dec_u32 bs’
  >> rw[lift_dec_u32_def, AllCaseEqs()]
QED

Theorem dec_indxs_shortens:
  ∀ bs xs rs. dec_indxs bs = (INR xs, rs) ⇒ lst_st rs bs
Proof
  rw[dec_vector_def,AllCaseEqs(), lift_dec_u32_def]
  >> dxrule dec_u32_shortens
  >> assume_tac lift_dec_u32_shortens
  >> dxrule_all dec_list_shortens_maybe_lt
  >> simp[]
QED


Definition enc_instr_def:
  (* "Expressions" in Wasm are lists of instructions terminated by
      the byte 0x0B [endB]. Here we use a flag to control whether
      we are encoding expressions, or just lists of instructions.
      cf the If case for an example *)
  (enc_instr_list (exp:bool) ([]:instr list) : byteSeq option = SOME if exp then [endB] else []
  ) ∧
  (enc_instr_list e (i::is) = do
    enci  <- enc_instr        i ;
    encis <- enc_instr_list e is;
    return $ enci ++ encis od
  ) ∧
  enc_instr (inst:instr) : byteSeq option = case inst of
  (* control instructions *)
  | Unreachable => SOME [zeroB]
  | Nop         => SOME [0x01w]
  (* block-y *)
  | Block bT body => do encb <- enc_instr_list T body; return $ 0x02w :: enc_blocktype bT ++ encb od
  | Loop  bT body => do encb <- enc_instr_list T body; return $ 0x03w :: enc_blocktype bT ++ encb od
  | If bT bdT []  => do enct <- enc_instr_list T bdT ; return $ 0x04w :: enc_blocktype bT ++ enct od
  | If bT bdT bdE => do enct <- enc_instr_list F bdT ;
                        ence <- enc_instr_list T bdE ;
                        return $ 0x04w :: enc_blocktype bT ++ enct ++ elseB :: ence od
  (* branches *)
  | Br           lbl =>                                SOME  $ 0x0Cw ::            enc_u32 lbl
  | BrIf         lbl =>                                SOME  $ 0x0Dw ::            enc_u32 lbl
  | BrTable lbls lbl => do enclbls <- enc_indxs lbls; return $ 0x0Ew :: enclbls ++ enc_u32 lbl od
  (* calls/returns *)
  | Return                    =>                                 SOME   [0x0Fw]
  | Call               fdx    =>                                 SOME  $ 0x10w ::            enc_u32 fdx
  | ReturnCall         fdx    =>                                 SOME  $ 0x12w ::            enc_u32 fdx
  | CallIndirect       fdx sg => do encFsig <- enc_functype sg; return $ 0x11w :: encFsig ++ enc_u32 fdx od
  | ReturnCallIndirect fdx sg => do encFsig <- enc_functype sg; return $ 0x13w :: encFsig ++ enc_u32 fdx od
  (* other classes of instructions *)
  | Variable   i => SOME $ enc_varI   i
  | Parametric i => SOME $ enc_paraI  i
  | Numeric    i => SOME $ enc_numI   i
  | MemRead    i => SOME $ enc_loadI  i
  | MemWrite   i => SOME $ enc_storeI i
End

Overload enc_expr   = “enc_instr_list T”
Overload enc_instrs = “enc_instr_list F”

Definition check_len_def:
  (check_len bs (INR x,rs) = if lst_st rs bs then (INR x,rs) else (INR x,[])) ∧
  (check_len bs (INL x,rs) = if lst_se rs bs then (INL x,rs) else (INL x,bs))
End

Theorem check_len_IMP:
  check_len bs xs = (INR x,rs)
  ⇒
  (lst_se rs bs) ∧ (bs ≠ [] ⇒ lst_st rs bs)
Proof
  PairCases_on ‘xs’
  \\ rw [check_len_def]
    >> Cases_on ‘xs0’
    >> gvs [check_len_def,AllCaseEqs()]
      >- (
      Cases_on ‘bs’ \\ fs[]
      )
QED

Definition mk_shorter_def:
  mk_shorter xs f = let fxs = f xs in
    case fxs of                                                (* if f doesn't shorten the list, then *)
    | (INR x, rs) => if lst_st rs xs then fxs else (INR x,[])  (* drop f's result or    , in res case *)
    | (INL x, rs) => if lst_se rs xs then fxs else (INL x,xs)  (* replace w the orig arg, in err case *)
End

Theorem mk_shorter_consq:
  ∀xs f x rs. mk_shorter xs f = (INR x, rs) ⇒
    (          lst_se rs xs) ∧
    (xs ≠ [] ⇒ lst_st rs xs)
Proof
  gvs[mk_shorter_def, AllCaseEqs()]
  \\ rpt strip_tac
  >> gvs[]
  \\ (Cases_on `xs` \\ fs[])
QED

(*
Definition dec_instr_def:
  (dec_instr ([]:byteSeq) : instr dcdr = emErr "dec_instr")
  ∧
  (dec_instr (b::bs) = let failure = error (b::bs) "[dec_instr]" in
    if b = zeroB then (INR Unreachable, bs) else
    if b = 0x01w then (INR Nop        , bs) else
    if b = 0x0Fw then (INR Return     , bs) else
    (* Br, BrIf *)
    if b = 0x0Cw then case dec_u32 bs of NONE=>failure|SOME (lbl,rs) => (INR $ Br   lbl,rs) else
    if b = 0x0Dw then case dec_u32 bs of NONE=>failure|SOME (lbl,rs) => (INR $ BrIf lbl,rs) else
    (* BrTable *)
    if b= 0x0Ew then (
      case dec_indxs bs of (INL _,_) => failure | (INR  lbls,cs) =>
      case dec_u32   cs of      NONE => failure | SOME (lbl ,rs) =>
        (INR $ BrTable lbls lbl, rs)                         ) else
    (* Block *)
    if b = 0x02w then (
      case dec_blocktype   bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case dec_instr_list  bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
      case bs                  of           [] => failure      | (b ::     bs) =>
        if b = 0x0Bw then (INR (Block bTyp body),bs) else failure        ) else
    (* Loop *)
    if b = 0x03w then (
      case dec_blocktype    bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case dec_instr_list  bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
      case bs                  of           [] => failure      | (b ::     bs) =>
        if b = 0x0Bw then (INR (Loop bTyp body),bs) else failure         ) else
    (* If then only *)
    if b = 0x04w then (
      case dec_blocktype bs                  of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case check_len bs (dec_instr_list  bs) of (INL err,bs) => (INL err,bs) | (INR bdT ,bs) =>
      case bs                                of           [] => failure      | (b ::     bs) =>
        if b = 0x0Bw then (INR (If bTyp bdT []),bs)                                       else
    (* If both *)
    if b ≠ 0x05w then failure else
      case dec_instr_list  bs of (INL err,bs) => (INL err,bs) | (INR bdE,bs) =>
      case bs                  of           [] => failure      | (b ::    bs) =>
        if b = 0x0Bw then (INR (If bTyp bdT bdE),bs) else failure         ) else
    (* calls *)
    if b = 0x10w then case dec_u32 bs of NONE => failure | SOME (f,rs) => (INR $ Call       f, rs) else
    if b = 0x12w then case dec_u32 bs of NONE => failure | SOME (f,rs) => (INR $ ReturnCall f, rs) else
    if b = 0x11w then case dec_functype bs of (INL _,_)=>failure|(INR sg,cs) =>
                      case dec_u32      cs of NONE     =>failure|SOME (f,rs) => (INR $ CallIndirect       f sg,rs) else
    if b = 0x13w then case dec_functype bs of (INL _,_)=>failure|(INR sg,cs) =>
                      case dec_u32      cs of NONE     =>failure|SOME (f,rs) => (INR $ ReturnCallIndirect f sg,rs) else
    (* other classes of instructions *)
    case dec_varI   bs of (INR i, rs) => (INR $ Variable   i, rs) | _ =>
    case dec_paraI  bs of (INR i, rs) => (INR $ Parametric i, rs) | _ =>
    case dec_numI   bs of (INR i, rs) => (INR $ Numeric    i, rs) | _ =>
    case dec_loadI  bs of (INR i, rs) => (INR $ MemRead    i, rs) | _ =>
    case dec_storeI bs of (INR i, rs) => (INR $ MemWrite   i, rs) | _ =>
  failure
  ) ∧
  (dec_instr_list ([]:byteSeq) = emErr "dec_instr_list") ∧
  (dec_instr_list (b::bs) =
    if b = endB ∨ b = elseB then (INR [],bs) else
    case check_len (b::bs) (dec_instr (b::bs)) of (INL err,bs) => (INL err,bs) | (INR i ,bs) =>
    case dec_instr_list  bs                    of (INL err,bs) => (INL err,bs) | (INR is,bs) =>
      (INR $ i::is, bs)                                                                       )
    (* case mk_shorter (b::bs) dec_instr of (INL err,bs) => (INL err,bs) | (INR i ,bs) => *)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL bs => 2 * LENGTH bs
                            | INR bs => 2 * LENGTH bs + 1’
  \\ rw []
    >> imp_res_tac dec_blocktype_shortens
    >> imp_res_tac check_len_IMP
    >> fs []
End
*)

Definition dec_instr_def:
  (dec_instr ([]:byteSeq) : instr dcdr = emErr "dec_instr")
  ∧
  (dec_instr (b::bs) = let failure = error (b::bs) "[dec_instr]" in
    if b = zeroB then (INR Unreachable, bs) else
    if b = 0x01w then (INR Nop        , bs) else
    if b = 0x0Fw then (INR Return     , bs) else
    (* Br, BrIf *)
    if b = 0x0Cw then case dec_u32 bs of NONE=>failure|SOME (lbl,rs) => (INR $ Br   lbl,rs) else
    if b = 0x0Dw then case dec_u32 bs of NONE=>failure|SOME (lbl,rs) => (INR $ BrIf lbl,rs) else
    (* BrTable *)
    if b= 0x0Ew then (
      case dec_indxs bs of (INL _,_) => failure | (INR  lbls,cs) =>
      case dec_u32   cs of      NONE => failure | SOME (lbl ,rs) =>
        (INR $ BrTable lbls lbl, rs)                         ) else
    (* Block *)
    if b = 0x02w then (
      case dec_blocktype    bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case dec_instr_list T bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
      case bs                  of           [] => failure      | (b ::     bs) =>
        if b = 0x0Bw then (INR (Block bTyp body),bs) else failure        ) else
    (* Loop *)
    if b = 0x03w then (
      case dec_blocktype    bs of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case dec_instr_list T bs of (INL err,bs) => (INL err,bs) | (INR body,bs) =>
      case bs                  of           [] => failure      | (b ::     bs) =>
        if b = 0x0Bw then (INR (Loop bTyp body),bs) else failure         ) else
    (* If then only *)
    if b = 0x04w then (
      case dec_blocktype bs                   of (INL err,bs) => (INL err,bs) | (INR bTyp,bs) =>
      case check_len bs (dec_instr_list F bs) of (INL err,bs) => (INL err,bs) | (INR bdT ,bs) =>
      case bs                                 of           [] => failure      | (b ::     bs) =>
        if b = 0x0Bw then (INR (If bTyp bdT []),bs)                                       else
    (* If both *)
    if b ≠ 0x05w then failure else
      case dec_instr_list T bs of (INL err,bs) => (INL err,bs) | (INR bdE,bs) =>
      case bs                  of           [] => failure      | (b ::    bs) =>
        if b = 0x0Bw then (INR (If bTyp bdT bdE),bs) else failure         ) else
    (* calls *)
    if b = 0x10w then case dec_u32 bs of NONE => failure | SOME (f,rs) => (INR $ Call       f, rs) else
    if b = 0x12w then case dec_u32 bs of NONE => failure | SOME (f,rs) => (INR $ ReturnCall f, rs) else
    if b = 0x11w then case dec_functype bs of (INL _,_)=>failure|(INR sg,cs) =>
                      case dec_u32      cs of NONE     =>failure|SOME (f,rs) => (INR $ CallIndirect       f sg,rs) else
    if b = 0x13w then case dec_functype bs of (INL _,_)=>failure|(INR sg,cs) =>
                      case dec_u32      cs of NONE     =>failure|SOME (f,rs) => (INR $ ReturnCallIndirect f sg,rs) else
    (* other classes of instructions *)
    case dec_varI   bs of (INR i, rs) => (INR $ Variable   i, rs) | _ =>
    case dec_paraI  bs of (INR i, rs) => (INR $ Parametric i, rs) | _ =>
    case dec_numI   bs of (INR i, rs) => (INR $ Numeric    i, rs) | _ =>
    case dec_loadI  bs of (INR i, rs) => (INR $ MemRead    i, rs) | _ =>
    case dec_storeI bs of (INR i, rs) => (INR $ MemWrite   i, rs) | _ =>
  failure
  ) ∧
  (dec_instr_list (_:bool) ([]:byteSeq) = emErr "dec_instr_list"
  ) ∧
  (dec_instr_list exp (b::bs) = let failure = error (b::bs) "[dec_instr_list]" in
    if exp
    then
        if b = endB then (INR [],bs) else
        case check_len (b::bs) (dec_instr (b::bs)) of (INL err,bs)=>failure| (INR i ,bs) =>
        (* case mk_shorter (b::bs) dec_instr          of (INL err,bs)=>failure| (INR i ,bs) => *)
        case dec_instr_list exp bs                 of (INL err,bs)=>failure| (INR is,bs) =>
          (INR $ i::is, bs)
    else
        case dec_instr (b::bs)     of (INL _  , _) => (INR [], b::bs) | (INR i, bs) =>
        case dec_instr_list exp bs of (INL err,bs) =>     failure     | (INR is,bs) =>
          (INR $ i::is, bs)                                                          )
Termination
  cheat
  (* WF_REL_TAC ‘measure $ λx. case x of
                            | INL bs => 2 * LENGTH bs
                            | INR bs => 2 * LENGTH bs + 1’
  \\ rw []
    >> imp_res_tac dec_blocktype_shortens
    >> imp_res_tac check_len_IMP
    >> fs [] *)
End

Overload dec_expr   = “dec_instr_list T”
Overload dec_instrs = “dec_instr_list F”

(*******************)
(*                 *)
(*     Modules     *)
(*                 *)
(*******************)

Definition enc_global_def:
  enc_global (g:global) : byteSeq option = do
    expr <- enc_expr g.ginit;
    return $ enc_globaltype g.gtype ++ expr od
End

Definition dec_global_def:
  dec_global ([]:byteSeq) : global dcdr = emErr "dec_global"
  ∧
  dec_global (bs:byteSeq) : global dcdr =
    (* if NULL bs then emErr "dec_global"
    else *)
    let failure = error bs "[dec_global]"
    in
    case dec_globaltype bs of (INL _,_) => failure | (INR gt, bs) =>
    case dec_expr       bs of (INL _,_) => failure | (INR ex, bs) =>
      (INR <| gtype := gt
            ; ginit := ex
            |> : mlstring + global
      , bs)
End



Definition enc_code_def:
  enc_code (c:valtype list # expr) : byteSeq option = do
    encC <- enc_expr                   (SND c);
    encL <- enc_vector enc_valtype_Seq (FST c);
    let code = encL ++ encC in
    return $ enc_u32 (n2w $ LENGTH code) ++ code od
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



Definition enc_data_def:
  enc_data (d:data) : byteSeq option = do
    ini <- enc_vector (λ b. [b]) d.dinit;
    ofs <- enc_expr d.offset            ;
    return $ enc_u32 d.data ++ ofs ++ ini od
End

Definition foo_def:
  foo [] = error [] "bogus" ∧
  foo (b::bs) = (INR b, bs)
End

Definition dec_data_def:
  dec_data ([]:byteSeq) : data dcdr = emErr "dec_data"
  ∧
  dec_data bs = let failure = error bs "[dec_data]" in
    case dec_u32        bs of  NONE     =>failure| SOME (idx,cs) =>
    case dec_expr       cs of (INL _,_) =>failure| (INR ofse,ds) =>
    case dec_vector foo ds of (INL _,_) =>failure| (INR ini ,rs) =>
      (INR <| data   := idx
            ; offset := ofse
            ; dinit  := ini
            |> : mlstring + data
      , rs)
End

Definition enc_section_def:
  enc_section (leadByte:byte) (contents:byteSeq) : byteSeq =
    leadByte :: enc_u32 (n2w $ LENGTH contents) ++ contents
End

(* Definition dec_section_def:
  dec_section ([]:byteSeq) : byteSeq dcdr = emErr "dec_section" ∧
  dec_section bs = let failure = error bs "[dec_section]" in

  case dec_u32 of NONE=>NONE| SOME

  dec_section (leadByte:byte) (contents:byteSeq) : byteSeq =
    leadByte :: enc_u32 (n2w $ LENGTH contents) ++ contents
End *)

Definition split_funcs_def:
  split_funcs ([]:func list) =  ( [] :  index                list
                                , [] : (valtype list # expr) list
                                , [] :  mlstring             list
                                , [] :  mlstring list        list ) ∧
  split_funcs (f::fs) =
    let ( typs
        , lBods
        , func_names
        , local_names
        ) = split_funcs fs
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



(* From CWasm (not Wasm!) modules to WBF *)
Definition enc_module_def:
  enc_module (m:module) : byteSeq option =
    let (fTIdxs, locBods, fns, lns) = split_funcs m.funcs in do
    types'   <- enc_vector_opt  enc_functype  m.types  ;
    funcs'   <- enc_vector      enc_u32       fTIdxs   ;
    mems'    <- enc_vector      enc_limits    m.mems   ;
    globals' <- enc_vector_opt  enc_global    m.globals;
    code'    <- enc_vector_opt  enc_code      locBods  ;
    datas'   <- enc_vector_opt  enc_data      m.datas  ;
      return $
      0x00w:: 0x61w:: 0x73w:: 0x6Dw:: (* \0asm - magic number         *)
      0x01w:: 0x00w:: 0x00w:: 0x00w:: (* version number of Bin format *)
      (* Type     *) enc_section  1w    types'    ++
      (* Function *) enc_section  3w    funcs'    ++
      (* Memory   *) enc_section  5w    mems'     ++
      (* Global   *) enc_section  6w    globals'  ++
      (* Code     *) enc_section 10w    code'     ++
      (* Data     *) enc_section 11w    datas'    ++
      (* Names    *) enc_section  0w    []        od
End

Definition dec_module_def:
  dec_module = ARB
End
