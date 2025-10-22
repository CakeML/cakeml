(*
  En- & De- coding between CWasm 1.0 AST & Wasm's binary format
*)
Theory      wbf
Ancestors   wasmLang leb128 wbf_prelim
Libs        preamble wordsLib

(* TODOs:
    - proper & meaningful error msgs
    - [MAYBE] state+error monad syntax *)

(************)
(*   Note   *)
(************)

(* Consult wasm_bf_prelimScript.sml for concepts/types/overloads used here *)

val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

Overload Soli[local] = “(SOME ∘ List): byteSeq -> byteCode”

(***************************************************************************)
(*                                                                         *)
(*     (Wasm Binary Format ⇔ WasmCake AST) Functions + shortening thms     *)
(*                                                                         *)
(***************************************************************************)

(**********************************************)
(*   Wasm Vectors (not vector instructions)   *)
(**********************************************)

Definition enc_list_def:
  enc_list (enc:α -> byteCode) ([]:α list) = Soli []
  ∧
  enc_list enc (x::xs) = do
    encx  <-              enc x ;
    encxs <- enc_list enc xs;
    SOME $ encx +++ encxs od
End

Definition dec_list_def:
  dec_list (n:num) (dec:byteSeq -> α dcdr) bs : α list dcdr =
    let failure = emErr "dec_list"
    in
    if n = 0 then (INR [],bs)
    else
    case dec                bs of (INL e,rs)=>failure| (INR x , bs) =>
    case dec_list (n-1) dec bs of (INL e,rs)=>failure| (INR xs, bs) =>
    ret bs $ x::xs
End

Theorem dec_list_shortens_maybe_le:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [≤] bs) ⇒
  ∀n bs rs xs. dec_list n dec bs = (INR xs,rs) ⇒
  rs [≤] bs
Proof
     strip_tac \\ strip_tac
  \\ Induct >> rw[Once dec_list_def, AllCaseEqs()]
  \\ last_x_assum dxrule
  \\ last_x_assum dxrule
  \\ simp[]
QED

Theorem dec_list_shortens_maybe_lt:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [<] bs) ⇒
  ∀n bs rs xs. dec_list n dec bs = (INR xs,rs) ⇒
  rs [≤] bs
Proof
  rpt strip_tac
  \\ dxrule_at Any dec_list_shortens_maybe_le
  \\ disch_then irule
  \\ rpt strip_tac
  \\ first_x_assum dxrule
  \\ rw[]
QED

Definition enc_vector_def:
  enc_vector (enc:α -> byteCode) (xs:α list) =
    let n = LENGTH xs in
    if 2 ** 32 ≤ n then NONE
    else do
    encxs <- enc_list enc xs;
    encln <- enc_u32 $ n2w n;
    SOME $ encln +++ encxs od
End

Definition dec_vector_def:
  dec_vector (dec:byteSeq -> α dcdr) bs : α list dcdr =
    case dec_u32 bs of
    | (INL _,_ ) => err
    | (INR w,bs) => dec_list (w2n w) dec bs
End

Theorem dec_vector_shortens_le:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [≤] bs) ⇒
  ∀bs rs xs. dec_vector dec bs = (INR xs,rs) ⇒
  rs [<] bs
Proof
  rw[dec_vector_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule_all dec_list_shortens_maybe_le
  \\ simp[]
QED

Theorem dec_vector_shortens_lt:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [<] bs) ⇒
  ∀bs rs xs. dec_vector dec bs = (INR xs,rs) ⇒
  rs [<] bs
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
  enc_valtype (t:valtype) = Soli [case t of
  | Tnum   Int W32 => 0x7Fw
  | Tnum   Int W64 => 0x7Ew]
End

Definition dec_valtype_def:
  dec_valtype [] : valtype dcdr = emErr "dec_valtype"
  ∧
  dec_valtype (b::bs) =
    if b = 0x7Fw then (INR $ Tnum   Int W32 ,bs) else
    if b = 0x7Ew then (INR $ Tnum   Int W64 ,bs) else
    err
End

Theorem dec_valtype_iso:
  ∀bs rs b t. dec_valtype (b::bs) = (INR t,rs) ⇒ rs = bs
Proof
  simp[oneline dec_valtype_def, AllCaseEqs()]
  \\ rpt strip_tac
  \\ simp[]
QED

Theorem dec_valtype_shortens:
  ∀bs rs t. dec_valtype bs = (INR t,rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[oneline dec_valtype_def]
QED



Definition enc_functype_def:
  enc_functype (sg:functype) = do
    argTs <- enc_vector enc_valtype (FST sg);
    resTs <- enc_vector enc_valtype (SND sg);
    SOME $ 0x60w ::: argTs +++ resTs od
End


Definition dec_functype_def:
  dec_functype [] : functype dcdr = emErr "dec_functype"
  ∧
  dec_functype (b::bs) = let failure = error (b::bs) "[dec_functype]" in
    if b ≠ 0x60w then failure else
    case dec_vector dec_valtype bs of (INL _,_)=>failure| (INR argTs,bs) =>
    case dec_vector dec_valtype bs of (INL _,_)=>failure| (INR resTs,rs) =>
    ret rs (argTs, resTs)
End

Theorem dec_functype_shortens:
  ∀bs rs xs. dec_functype bs = (INR xs, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’ >> rw[dec_functype_def, AllCaseEqs()]
  \\ assume_tac dec_valtype_shortens
  \\ imp_res_tac dec_vector_shortens_lt
  \\ rw[]
QED



Definition enc_limits_def:
  enc_limits (lims:limits) = case lims of
  | Lunb mn    => do encm <- enc_u32  mn   ; SOME $ 0x00w ::: encm od
  | Lwmx mn mx => do encm <- enc_2u32 mn mx; SOME $ 0x01w ::: encm od
End

Definition dec_limits_def:
  dec_limits [] : limits dcdr = emErr "dec_limits"
  ∧
  dec_limits (b::bs) = let failure = error (b::bs) "[dec_limits]"
  in
  if b = 0x00w then case dec_u32  bs of (INL _,_)=>failure| (INR  mn    ,rs) => ret rs $ Lunb mn    else
  if b = 0x01w then case dec_2u32 bs of (INL _,_)=>failure| (INR (mn,mx),rs) => ret rs $ Lwmx mn mx else
  failure
End

Theorem dec_limits_shortens:
  ∀bs rs xs. dec_limits bs = (INR xs, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_limits_def, AllCaseEqs()]
  >>~- ([‘dec_u32’ ], (dxrule dec_u32_shortens  \\ simp[]))
  >>~- ([‘dec_2u32’], (dxrule dec_2u32_shortens \\ simp[]))
QED



Definition enc_globaltype_def:
  enc_globaltype (t:globaltype) = case t of
  | Gconst vt => do encvt <- enc_valtype vt; SOME $ encvt +++ List [0x00w] od
  | Gmut   vt => do encvt <- enc_valtype vt; SOME $ encvt +++ List [0x01w] od
End

Definition dec_globaltype_def:
  dec_globaltype bs : globaltype dcdr =
    if NULL bs then emErr "dec_globaltype"
    else
    let failure = error bs "[dec_globaltype]"
    in
    case dec_valtype bs of
    | (INR vt,b::bs) => if b = 0x00w then ret bs $ Gconst vt else
                        if b = 0x01w then ret bs $ Gmut   vt else
                        failure
    | _              => failure
End

Theorem dec_globaltype_shortens:
  ∀bs rs xs. dec_globaltype bs = (INR xs, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_globaltype_def, AllCaseEqs()]
    >> drule dec_valtype_shortens >> rw[]
QED





(*******************************************)
(*   Instructions (hierarchically lower)   *)
(*******************************************)

Definition enc_numI_def:
  enc_numI (i:num_instr) = case i of
  | N_eqz     $   W32                        => Soli [0x45w]
  | N_compare $   Eq  Int      W32           => Soli [0x46w]
  | N_compare $   Ne  Int      W32           => Soli [0x47w]
  | N_compare $   Lt_   Signed W32           => Soli [0x48w]
  | N_compare $   Lt_ Unsigned W32           => Soli [0x49w]
  | N_compare $   Gt_   Signed W32           => Soli [0x4Aw]
  | N_compare $   Gt_ Unsigned W32           => Soli [0x4Bw]
  | N_compare $   Le_   Signed W32           => Soli [0x4Cw]
  | N_compare $   Le_ Unsigned W32           => Soli [0x4Dw]
  | N_compare $   Ge_   Signed W32           => Soli [0x4Ew]
  | N_compare $   Ge_ Unsigned W32           => Soli [0x4Fw]
  | N_eqz     $   W64                        => Soli [0x50w]
  | N_compare $   Eq Int       W64           => Soli [0x51w]
  | N_compare $   Ne Int       W64           => Soli [0x52w]
  | N_compare $   Lt_   Signed W64           => Soli [0x53w]
  | N_compare $   Lt_ Unsigned W64           => Soli [0x54w]
  | N_compare $   Gt_   Signed W64           => Soli [0x55w]
  | N_compare $   Gt_ Unsigned W64           => Soli [0x56w]
  | N_compare $   Le_   Signed W64           => Soli [0x57w]
  | N_compare $   Le_ Unsigned W64           => Soli [0x58w]
  | N_compare $   Ge_   Signed W64           => Soli [0x59w]
  | N_compare $   Ge_ Unsigned W64           => Soli [0x5Aw]
  | N_unary   $   Clz    W32                 => Soli [0x67w]
  | N_unary   $   Ctz    W32                 => Soli [0x68w]
  | N_unary   $   Popcnt W32                 => Soli [0x69w]
  | N_binary  $   Add  Int      W32          => Soli [0x6Aw]
  | N_binary  $   Sub  Int      W32          => Soli [0x6Bw]
  | N_binary  $   Mul  Int      W32          => Soli [0x6Cw]
  | N_binary  $   Div_   Signed W32          => Soli [0x6Dw]
  | N_binary  $   Div_ Unsigned W32          => Soli [0x6Ew]
  | N_binary  $   Rem_   Signed W32          => Soli [0x6Fw]
  | N_binary  $   Rem_ Unsigned W32          => Soli [0x70w]
  | N_binary  $   And           W32          => Soli [0x71w]
  | N_binary  $   Or            W32          => Soli [0x72w]
  | N_binary  $   Xor           W32          => Soli [0x73w]
  | N_binary  $   Shl           W32          => Soli [0x74w]
  | N_binary  $   Shr_   Signed W32          => Soli [0x75w]
  | N_binary  $   Shr_ Unsigned W32          => Soli [0x76w]
  | N_binary  $   Rotl          W32          => Soli [0x77w]
  | N_binary  $   Rotr          W32          => Soli [0x78w]
  | N_unary   $   Clz    W64                 => Soli [0x79w]
  | N_unary   $   Ctz    W64                 => Soli [0x7Aw]
  | N_unary   $   Popcnt W64                 => Soli [0x7Bw]
  | N_binary  $   Add Int       W64          => Soli [0x7Cw]
  | N_binary  $   Sub Int       W64          => Soli [0x7Dw]
  | N_binary  $   Mul Int       W64          => Soli [0x7Ew]
  | N_binary  $   Div_   Signed W64          => Soli [0x7Fw]
  | N_binary  $   Div_ Unsigned W64          => Soli [0x80w]
  | N_binary  $   Rem_   Signed W64          => Soli [0x81w]
  | N_binary  $   Rem_ Unsigned W64          => Soli [0x82w]
  | N_binary  $   And           W64          => Soli [0x83w]
  | N_binary  $   Or            W64          => Soli [0x84w]
  | N_binary  $   Xor           W64          => Soli [0x85w]
  | N_binary  $   Shl           W64          => Soli [0x86w]
  | N_binary  $   Shr_   Signed W64          => Soli [0x87w]
  | N_binary  $   Shr_ Unsigned W64          => Soli [0x88w]
  | N_binary  $   Rotl          W64          => Soli [0x89w]
  | N_binary  $   Rotr          W64          => Soli [0x8Aw]
  | N_convert $   WrapI64                    => Soli [0xA7w]
  | N_unary   $   ExtendI32_   Signed        => Soli [0xACw]
  | N_unary   $   ExtendI32_ Unsigned        => Soli [0xADw]
  | N_unary   $   Extend8s  W32              => Soli [0xC0w]
  | N_unary   $   Extend16s W32              => Soli [0xC1w]
  | N_unary   $   Extend8s  W64              => Soli [0xC2w]
  | N_unary   $   Extend16s W64              => Soli [0xC3w]
  | N_unary   $   Extend32s                  => Soli [0xC4w]
  | N_const32 Int   (c: word32)              => do encc <- enc_s32 c; SOME $ 0x41w ::: encc od
  | N_const64 Int   (c: word64)              => do encc <- enc_s64 c; SOME $ 0x42w ::: encc od
End

Definition dec_numI_def:
  dec_numI [] : num_instr dcdr = emErr "dec_numI"
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
  if b = 0x41w then case dec_s32 bs of (INL _,_) =>failure| (INR s32,bs) => (INR $ N_const32  Int  s32, bs) else
  if b = 0x42w then case dec_s64 bs of (INL _,_) =>failure| (INR s64,bs) => (INR $ N_const64  Int  s64, bs) else
  error (b::bs) "[dec_numI]: Not a numeric instruction"
End

Theorem dec_numI_shortens:
  ∀bs rs _i. dec_numI bs = (INR _i, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_numI_def, AllCaseEqs()]
    >~ [‘dec_s32’] >- (dxrule dec_s32_shortens \\ simp[])
    >~ [‘dec_s64’] >- (dxrule dec_s64_shortens \\ simp[])
    >> rw[]
QED

Theorem dec_numI_error:
  ∀bs rs e. dec_numI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_numI_def, AllCaseEqs()]
QED



Definition enc_paraI_def:
  enc_paraI (i:para_instr) = Soli [case i of
  | Drop   => 0x1Aw
  | Select => 0x1Bw]
End

Definition dec_paraI_def:
  dec_paraI [] : para_instr dcdr = emErr "dec_paraI"
  ∧
  dec_paraI (b::bs) = let failure = error (b::bs) "[dec_paraI]"
  in
  if b = 0x1Aw then (INR Drop  , bs) else
  if b = 0x1Bw then (INR Select, bs) else
  failure
End

Theorem dec_paraI_shortens:
  ∀bs rs _i. dec_paraI bs = (INR _i, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_paraI_def, AllCaseEqs()]
  >> rw[]
QED

Theorem dec_paraI_error:
  ∀bs rs e. dec_paraI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_paraI_def, AllCaseEqs()]
QED



Definition enc_varI_def:
  enc_varI (i:var_instr) = case i of
  | LocalGet  x => do encx <- enc_u32 x; SOME $ 0x20w ::: encx od
  | LocalSet  x => do encx <- enc_u32 x; SOME $ 0x21w ::: encx od
  | LocalTee  x => do encx <- enc_u32 x; SOME $ 0x22w ::: encx od
  | GlobalGet x => do encx <- enc_u32 x; SOME $ 0x23w ::: encx od
  | GlobalSet x => do encx <- enc_u32 x; SOME $ 0x24w ::: encx od
End

Definition dec_varI_def:
  dec_varI [] : var_instr dcdr = emErr "dec_varI"
  ∧
  dec_varI (b::bs) = let failure = error (b::bs) "[dec_varI]"
  in
  case dec_u32 bs of (INL _,_)=>failure| (INR x,rs) =>
  if b = 0x20w then ret rs $ LocalGet  x else
  if b = 0x21w then ret rs $ LocalSet  x else
  if b = 0x22w then ret rs $ LocalTee  x else
  if b = 0x23w then ret rs $ GlobalGet x else
  if b = 0x24w then ret rs $ GlobalSet x else
  error (b::bs) "[dec_varI] : Not a variable instruction.\n"
End

Theorem dec_varI_shortens:
  ∀bs rs _i. dec_varI bs = (INR _i, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_varI_def, AllCaseEqs()]
  >> dxrule dec_u32_shortens
  >> simp[]
QED

Theorem dec_varI_error:
  ∀bs rs e. dec_varI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_varI_def, AllCaseEqs()]
QED



Definition enc_loadI_def:
  enc_loadI (i:load_instr) = case i of
  | Load    Int                  W32 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x28w ::: encao od
  | Load    Int                  W64 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x29w ::: encao od
  | LoadNarrow I8x16    Signed   W32 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x2Cw ::: encao od
  | LoadNarrow I8x16  Unsigned   W32 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x2Dw ::: encao od
  | LoadNarrow I16x8    Signed   W32 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x2Ew ::: encao od
  | LoadNarrow I16x8  Unsigned   W32 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x2Fw ::: encao od
  | LoadNarrow I8x16    Signed   W64 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x30w ::: encao od
  | LoadNarrow I8x16  Unsigned   W64 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x31w ::: encao od
  | LoadNarrow I16x8    Signed   W64 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x32w ::: encao od
  | LoadNarrow I16x8  Unsigned   W64 ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x33w ::: encao od
  | LoadNarrow32        Signed       ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x34w ::: encao od
  | LoadNarrow32      Unsigned       ofs al  => do encao <- enc_2u32 al ofs; SOME $ 0x35w ::: encao od
End

Definition dec_loadI_def:
  dec_loadI [] : load_instr dcdr = emErr "dec_loadI"
  ∧
  dec_loadI (b::bs) = let failure = error (b::bs) "[dec_loadI]"
  in
  case dec_2u32 bs of (INL _,_)=>failure|(INR (a,ofs),rs) =>
  if b = 0x28w then ret rs $ Load    Int                 W32 ofs a else
  if b = 0x29w then ret rs $ Load    Int                 W64 ofs a else
  if b = 0x2Cw then ret rs $ LoadNarrow I8x16    Signed  W32 ofs a else
  if b = 0x2Dw then ret rs $ LoadNarrow I8x16  Unsigned  W32 ofs a else
  if b = 0x2Ew then ret rs $ LoadNarrow I16x8    Signed  W32 ofs a else
  if b = 0x2Fw then ret rs $ LoadNarrow I16x8  Unsigned  W32 ofs a else
  if b = 0x30w then ret rs $ LoadNarrow I8x16    Signed  W64 ofs a else
  if b = 0x31w then ret rs $ LoadNarrow I8x16  Unsigned  W64 ofs a else
  if b = 0x32w then ret rs $ LoadNarrow I16x8    Signed  W64 ofs a else
  if b = 0x33w then ret rs $ LoadNarrow I16x8  Unsigned  W64 ofs a else
  if b = 0x34w then ret rs $ LoadNarrow32        Signed      ofs a else
  if b = 0x35w then ret rs $ LoadNarrow32      Unsigned      ofs a else
  error (b::bs) "[dec_loadI] : Not a load instruction.\n"
End

Theorem dec_loadI_shortens:
  ∀bs rs _i. dec_loadI bs = (INR _i, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_loadI_def, AllCaseEqs()]
  >> dxrule dec_2u32_shortens
  >> simp[]
QED

Theorem dec_loadI_error:
  ∀bs rs e. dec_loadI bs = (INL e, rs) ⇒ bs = rs
Proof
  Cases_on ‘bs’
  >> rw[dec_loadI_def, AllCaseEqs()]
QED



Definition enc_storeI_def:
  enc_storeI (i:store_instr) = case i of
  | Store   Int                  W32 ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x36w ::: encao od
  | Store   Int                  W64 ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x37w ::: encao od
  | StoreNarrow I8x16            W32 ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x3Aw ::: encao od
  | StoreNarrow I16x8            W32 ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x3Bw ::: encao od
  | StoreNarrow I8x16            W64 ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x3Cw ::: encao od
  | StoreNarrow I16x8            W64 ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x3Dw ::: encao od
  | StoreNarrow32                    ofs al => do encao <- enc_2u32 al ofs; SOME $ 0x3Ew ::: encao od
End

Definition dec_storeI_def:
  dec_storeI ([]:byteSeq) : store_instr dcdr = emErr "dec_storeI"
  ∧
  dec_storeI (b::bs) = let failure = error (b::bs) "[dec_storeI]"
  in
  case dec_2u32 bs of (INL _,_)=>failure| (INR (al,ofs),rs) =>
  if b = 0x36w then ret rs $ Store          Int  W32 ofs al else
  if b = 0x37w then ret rs $ Store          Int  W64 ofs al else
  if b = 0x3Aw then ret rs $ StoreNarrow  I8x16  W32 ofs al else
  if b = 0x3Bw then ret rs $ StoreNarrow  I16x8  W32 ofs al else
  if b = 0x3Cw then ret rs $ StoreNarrow  I8x16  W64 ofs al else
  if b = 0x3Dw then ret rs $ StoreNarrow  I16x8  W64 ofs al else
  if b = 0x3Ew then ret rs $ StoreNarrow32           ofs al else
  error (b::bs) "[dec_storeI] : Not a store instruction.\n"
End

Theorem dec_storeI_shortens:
  ∀bs rs _i. dec_storeI bs = (INR _i, rs) ⇒ rs [<] bs
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
  enc_blocktype (bt:blocktype) = case bt of
  | BlkNil    => SOME $ List [0x40w]
  | BlkVal vt => enc_valtype vt
End

Definition dec_blocktype_def:
  dec_blocktype bs : blocktype dcdr = let failure = error bs "[dec_blocktype]"
    in
    case bs of [] => emErr "dec_blocktype" | b::rs
    =>
    if b = 0x40w then ret rs $ BlkNil
    else
    case dec_valtype bs of (INR t ,rs) => ret rs $ BlkVal t | _ => failure
    (* error bs "[dec_blocktype] : Not a blocktype.\n" *)
End

Theorem dec_blocktype_shortens:
  ∀bs rs _t. dec_blocktype bs = (INR _t,rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_blocktype_def, AllCaseEqs()]
    >> imp_res_tac dec_valtype_iso
    >> simp[]
QED



(*  we specialize/instantiate this particular version
    of enc_/dec_vector just for abstraction *)
Overload enc_indxs = “enc_vector enc_u32”
Overload dec_indxs = “dec_vector dec_u32”

Theorem dec_indxs_shortens:
  ∀ bs rs xs. dec_indxs bs = (INR xs, rs) ⇒ rs [<] bs
Proof
     rpt strip_tac
  \\ assume_tac dec_u32_shortens
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
  (enc_instr_list (e:bool) ([]:instr list) = Soli [if e then endB else elseB]
  ) ∧
  (enc_instr_list _encode_expr (i::is) = do
    enci  <- enc_instr                   i ;
    encis <- enc_instr_list _encode_expr is;
    SOME $ enci +++ encis od
  ) ∧
  enc_instr (inst:instr) = case inst of
  (* control instructions *)
  | Unreachable => Soli [unrOC]
  | Nop         => Soli [nopOC]
  (* block-y *)
  | Block bT body => do enct <- enc_blocktype bT; encb <- enc_instr_list T body; SOME $ blkOC ::: enct +++ encb od
  | Loop  bT body => do enct <- enc_blocktype bT; encb <- enc_instr_list T body; SOME $ lopOC ::: enct +++ encb od
  | If bT bdT bdE => do enct <- enc_blocktype bT; enTh <- enc_instr_list F bdT ;
                                                  ence <- enc_instr_list T bdE ; SOME $ if_OC ::: enct +++ enTh +++ ence od
  | If bT bdT []  => do enct <- enc_blocktype bT; encb <- enc_instr_list T body; SOME $ if_OC ::: enct +++ encb od
  (* branches *)
  | Br           lbl => do                            enci <- enc_u32 lbl; SOME $ br_OC :::             enci od
  | BrIf         lbl => do                            enci <- enc_u32 lbl; SOME $ briOC :::             enci od
  | BrTable lbls lbl => do enclbls <- enc_indxs lbls; enci <- enc_u32 lbl; SOME $ brtOC ::: enclbls +++ enci od
  (* calls/returns *)
  | Return                    =>                                                   Soli  [retOC]
  | Call               fdx    => do                           enci <- enc_u32 fdx; SOME $ calOC :::           enci od
  | ReturnCall         fdx    => do                           enci <- enc_u32 fdx; SOME $ rclOC :::           enci od
  | CallIndirect       fdx sg => do encsg <- enc_functype sg; enci <- enc_u32 fdx; SOME $ cinOC ::: encsg +++ enci od
  | ReturnCallIndirect fdx sg => do encsg <- enc_functype sg; enci <- enc_u32 fdx; SOME $ rciOC ::: encsg +++ enci od
  (* other classes of instructions *)
  | Variable   i => enc_varI   i
  | Parametric i => enc_paraI  i
  | Numeric    i => enc_numI   i
  | MemRead    i => enc_loadI  i
  | MemWrite   i => enc_storeI i
End

Overload enc_expr = “enc_instr_list T”  (* byte stream terminated with an endB  *)
Overload enc_tArm = “enc_instr_list F”  (* byte stream terminated with an elseB *)



(***************************************************)
(*   Top-level/Control flow instruction DE coder   *)
(***************************************************)

(* Used in termination proof. While 2nd argument seems
   slightly mysterious, [shorten] is meant to be called
   in a specific pattern:
   (**)
   λdec xs. shorten xs (dec xs)
   (**)
   [shorten] helps with termination by saying that if the decoder
   doesn't produce a shorter byte stream, we explicitly
   replace the byte stream with one that is shorter/equal length *)
Definition shorten_def:
  (shorten bs (INR x,rs) = if rs [<] bs then (INR x,rs) else (INR x,[])) ∧
  (shorten bs (INL x,rs) = if rs [≤] bs then (INL x,rs) else (INL x,bs))
End

Overload force_shtr = “λdec xs. shorten xs (dec xs)”

Theorem shorten_IMP:
  ∀xs bs rs x s. shorten bs xs = (INR x,rs)
  ⇒
  (rs [≤] bs) ∧ (bs ≠ [] ⇒ rs [<] bs)
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
   (the encoding of) an else-arm. (Since the then-block of a dual-armed-if is the only
   place we see an else-byte terminator.)
   (**)
   TODO: Check that this fact about the else byte is actually true *)
Definition dec_instr_def:
  (dec_instr_list (_elseB_allowed:bool) [] : (byte # instr list) dcdr = emErr "dec_instr_list"
  ) ∧
  (dec_instr_list e (b::bs) =
    let failure = error (b::bs) "[dec_instr_list]"
    in
    if b = endB ∨ (e ∧ b = elseB) then ret bs (b,[])
    else
    case force_shtr dec_instr (b::bs) of (INL _,_)=>failure| (INR i         ,bs) =>
    case dec_instr_list e bs          of (INL _,_)=>failure| (INR (termB,is),bs) =>
    ret bs (termB, i::is)
  ) ∧
  (dec_instr [] : instr dcdr = emErr "dec_instr"
  ) ∧
  (dec_instr (b::bs) = let failure = error (b::bs) "[dec_instr]" in
    (* Single-byte encoded instrs *)
    if b = unrOC then ret bs Unreachable else
    if b = nopOC then ret bs Nop         else
    if b = retOC then ret bs Return      else
    (* Br, BrIf *)
    if b = br_OC then case dec_u32 bs of (INL _,_)=>failure| (INR lbl,bs) => ret bs $ Br   lbl else
    if b = briOC then case dec_u32 bs of (INL _,_)=>failure| (INR lbl,bs) => ret bs $ BrIf lbl else
    (* BrTable *)
    if b = brtOC then (
      case dec_indxs bs of (INL _,_) => failure | (INR lbls,bs) =>
      case dec_u32   bs of (INL _,_) => failure | (INR lbl ,bs) =>
      ret bs $ BrTable lbls lbl                             ) else
    (* Calls *)
    if b = calOC then case dec_u32      bs of (INL _,_)=>failure|(INR f ,bs) => ret bs $ Call               f    else
    if b = rclOC then case dec_u32      bs of (INL _,_)=>failure|(INR f ,bs) => ret bs $ ReturnCall         f    else
    if b = cinOC then case dec_functype bs of (INL _,_)=>failure|(INR sg,bs) =>
                      case dec_u32      bs of (INL _,_)=>failure|(INR f ,bs) => ret bs $ CallIndirect       f sg else
    if b = rciOC then case dec_functype bs of (INL _,_)=>failure|(INR sg,bs) =>
                      case dec_u32      bs of (INL _,_)=>failure|(INR f ,bs) => ret bs $ ReturnCallIndirect f sg else
    (* Block-y instructrions ie, instructions with embedded blocks *)
    (* Block *)
    if b = blkOC then (
      case dec_blocktype    bs of (INL _,_) =>failure| (INR bTyp    ,bs) =>
      case dec_instr_list F bs of (INL _,_) =>failure| (INR (_,body),bs) =>
      ret bs $ Block bTyp body                                       ) else
    (* Loop *)
    if b = lopOC then (
      case dec_blocktype    bs of (INL _,_) =>failure| (INR bTyp    ,bs) =>
      case dec_instr_list F bs of (INL _,_) =>failure| (INR (_,body),bs) =>
      ret bs $ Loop bTyp body                                           ) else
    (* If then only *)
    if b = if_OC then (
      case dec_blocktype bs                 of (INL _,_) =>failure| (INR bTyp        ,bs) =>
      case force_shtr (dec_instr_list T) bs of (INL _,_) =>failure| (INR (termB,bdyT),bs) =>
      if termB = endB then
      ret bs $ If bTyp bdyT []
    else (* termB = elseB *)
    (* If both *)
      case dec_instr_list F bs of (INL _,_) =>failure| (INR (_,bdyE),bs) =>
      ret bs $ If bTyp bdyT bdyE                                     ) else
    (* other classes of instructions *)
    case dec_varI   (b::bs) of (INR i, bs) => ret bs $ Variable   i | _ =>
    case dec_paraI  (b::bs) of (INR i, bs) => ret bs $ Parametric i | _ =>
    case dec_numI   (b::bs) of (INR i, bs) => ret bs $ Numeric    i | _ =>
    case dec_loadI  (b::bs) of (INR i, bs) => ret bs $ MemRead    i | _ =>
    case dec_storeI (b::bs) of (INR i, bs) => ret bs $ MemWrite   i | _ =>
  failure)
Termination
  WF_REL_TAC ‘measure $ λx. case x of
                            | INL (_, bs) => 2 * LENGTH bs + 1  (* measure for the first  fn ---dec_instr_list) *)
                            | INR bs      => 2 * LENGTH bs’     (* measure for the second fn ---dec_instr)     *)
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
  (∀e xs x rs. dec_instr_list e xs = (INR x,rs) ⇒ rs [<] xs) ∧
  (∀xs x rs  . dec_instr        xs = (INR x,rs) ⇒ rs [<] xs)
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
  (∀xs rs e x. dec_instr_list e xs = (INR x,rs) ⇒ rs [<] xs)
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

Definition prepend_sz_def:
  prepend_sz (appl: byte app_list) : byteCode = do
    encl <- enc_u32 $ n2w $ LENGTH $ append appl;
    SOME $ encl +++ appl od
End





Definition enc_global_def:
  enc_global (g:global) = do
    expr <- enc_expr g.ginit;
    enct <- enc_globaltype g.gtype;
    SOME $ enct +++ expr od
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
  ∀bs rs xs. dec_global bs = (INR xs, rs) ⇒ rs [<] bs
Proof
  rw[dec_global_def, AllCaseEqs()]
  \\ dxrule dec_globaltype_shortens
  \\ dxrule dec_instr_list_shortens
  \\ rw[]
QED



Definition enc_code_def:
  enc_code (c:valtype list # expr) = do
    encC <- enc_expr               (SND c);
    encL <- enc_vector enc_valtype (FST c);
    let code = encL +++ encC in
    prepend_sz code od
End

Definition dec_code_def:
  dec_code bs : (valtype list # expr) dcdr =
  if NULL bs then emErr "dec_code" else
  let failure = error bs "[dec_code]" in
    case dec_u32                bs of (INL _,_)=>failure|(INR  len,cs) =>
    case dec_vector dec_valtype cs of (INL _,_)=>failure|(INR vts ,ds) =>
    case dec_expr               ds of (INL _,_)=>failure|(INR code,rs) =>
    ret rs (vts, code)
End

Theorem dec_code_shortens:
  ∀ bs rs xs. dec_code bs = (INR xs, rs) ⇒ rs [<] bs
Proof
  Cases_on ‘bs’
  >> rw[dec_code_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ assume_tac dec_valtype_shortens
  \\ dxrule_all dec_vector_shortens_lt
  \\ dxrule dec_instr_list_shortens
  \\ simp[]
QED



Definition enc_byte_def:
  enc_byte (b:byte) = Soli [b]
End

(* Used in dec_data *)
Definition dec_byte_def:
  dec_byte [] : byte dcdr = error [] "bogus"
  ∧
  dec_byte (b::bs) = (INR b, bs)
End

Theorem dec_byte_shortens:
  ∀bs rs b. dec_byte bs = (INR b, rs) ⇒ rs [<] bs
Proof
  Cases >> rw[dec_byte_def]
QED



Definition enc_data_def:
  enc_data (d:data) : byteCode = do
    ini <- enc_vector enc_byte d.dinit;
    ofs <- enc_expr d.offset            ;
    sz  <- enc_u32 d.data               ;
    SOME $ sz +++ ofs +++ ini od
End

Definition dec_data_def:
  dec_data (bs:byteSeq) : data dcdr =
    if NULL bs then emErr "dec_data" else
    let failure = error bs "[dec_data]"
    in
    case dec_u32             bs of (INL _,_) =>failure| (INR idx ,bs) =>
    case dec_expr            bs of (INL _,_) =>failure| (INR ofse,bs) =>
    case dec_vector dec_byte bs of (INL _,_) =>failure| (INR ini ,rs) =>
      (INR <| data   := idx
            ; offset := ofse
            ; dinit  := ini
            |>
      , rs)
End

Theorem dec_data_shortens:
  ∀bs rs xs. dec_data bs = (INR xs, rs) ⇒ rs [<] bs
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
    , [] : (valtype list # expr) list )
  ∧
  split_funcs (f::fs) = let
    ( typs
    , lBods ) = split_funcs fs
    in
    ( f.ftype            :: typs
    ,(f.locals, f.body)  :: lBods
    )
End

Definition zip_funcs_def:
  zip_funcs ([] :  index                list)
            (_  : (valtype list # expr) list) = [] : func list
  ∧
  zip_funcs _ [] = [] ∧
  zip_funcs ( fi            :: is   )
            ( (vs,e)        :: vles ) =
  (<| ftype  := fi
    ; locals := vs
    ; body   := e
    |>            ) :: zip_funcs is vles
End



(* enc_section is our first encoder that can return empty byteCode.
   This is pertinent for the shape of it's dec_enc thm *)
Definition enc_section_def:
  enc_section (leadByte:byte) (enc:α -> byteCode) (xs:α list) =
    if NULL xs then Soli [] else
    do
    encxs <- enc_vector enc xs;
    enced <- prepend_sz encxs ;
    SOME $ leadByte ::: enced od
End

Definition dec_section_def:
  dec_section (_:byte)
              (_:byteSeq -> α dcdr)
              [] : (α list) dcdr = ret [] []
  ∧
  dec_section leadByte dec (b::bs) =
    let failure = error bs "dec_section"
    in
    if b ≠ leadByte then ret (b::bs) []
    else
    case dec_u32 bs of
    | (INL _,_)   => failure
    | (INR _w,bs) => dec_vector dec bs
End

Theorem dec_section_shortens_maybe_lt:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [<] bs) ⇒
  ∀bs rs lb dc. dec_section lb dec bs = (INR dc, rs) ⇒ rs [≤] bs
Proof
  strip_tac \\ strip_tac
  \\ Cases >> rw[dec_section_def, AllCaseEqs()]
    >> simp[]
    \\ dxrule dec_u32_shortens
    \\ dxrule_all dec_vector_shortens_lt
    \\ simp[]
QED





(*******************************)
(*                             *)
(*      The names section      *)
(*                             *)
(*******************************)

(* Format of acceptable identifiers
   - from ascii code points *)
Definition id_OK_def:
  id_OK ("":string) : bool = T
  ∧
  (id_OK (first::str) =
    let alpha_us     x = (isLower  x  ∨  isUpper x  ∨  (ORD x = 95)) in
    let alpha_num_us x = (alpha_us x  ∨  isDigit x)
    in
    alpha_us first ∧
    foldl (λ e sd. alpha_num_us e ∧ sd) T str)
End

Definition string2bytes_def:
  string2bytes : string -> byteSeq = MAP (n2w ∘ ORD)
End

Definition bytes2string_def:
  bytes2string : byteSeq -> string = MAP (CHR ∘ w2n)
End



Definition enc_mls_def:
  enc_mls (str:mlstring) =
    let ascii = explode str
    in
    if id_OK ascii
    then enc_vector enc_byte $ string2bytes ascii
    else NONE
End

Definition dec_mls_def:
  dec_mls bs : mlstring dcdr =
    case dec_vector dec_byte bs of
    | (INL _,_) => err
    | (INR bs, rs) => ret rs $ implode $ bytes2string bs
End

Theorem dec_mls_shortens:
  ∀bs rs x. dec_mls bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rw[dec_mls_def, AllCaseEqs()]
  \\ assume_tac  dec_byte_shortens
  \\ imp_res_tac dec_vector_shortens_lt
QED



(* Encoding a pair of index & an α *)
Definition enc_idx_alpha_def:
  enc_idx_alpha (enc:α -> byteCode) (i:index, a:α) = do
    enci <- enc_u32 i;
    enca <- enc a    ;
    SOME $ enci +++ enca od
End

Definition dec_idx_alpha_def:
  dec_idx_alpha (dec: byteSeq -> α dcdr) bs : (index # α) dcdr =
    case dec_u32 bs of (INL _,_)=>err| (INR idx, bs) =>
    case dec     bs of (INL _,_)=>err| (INR a  , bs) =>
    ret bs (idx,a)
End

Theorem dec_idx_alpha_shortens_le:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [≤] bs) ⇒
  ∀bs rs x. dec_idx_alpha dec bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rw[dec_idx_alpha_def, AllCaseEqs()]
  \\ last_x_assum dxrule
  \\ dxrule dec_u32_shortens
  \\ rw[]
QED

Theorem dec_idx_alpha_shortens_lt:
  ∀dec.
  (∀bs rs x. dec bs = (INR x, rs) ⇒ rs [<] bs) ⇒
  ∀bs rs x. dec_idx_alpha dec bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rw[dec_idx_alpha_def, AllCaseEqs()]
  \\ last_x_assum dxrule
  \\ dxrule dec_u32_shortens
  \\ rw[]
QED



(* In the context of the names section, "Associations"
   are pairings of indices & mlstrings (names) *)
Definition enc_ass_def:
  enc_ass : (index # mlstring) -> byteCode = enc_idx_alpha enc_mls
End

Definition dec_ass_def:
  dec_ass : byteSeq -> (index # mlstring) dcdr = dec_idx_alpha dec_mls
End

Theorem dec_ass_shortens:
  ∀bs rs x. dec_ass  bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rw[dec_ass_def, AllCaseEqs()]
  \\ assume_tac dec_mls_shortens
  \\ imp_res_tac dec_idx_alpha_shortens_lt
QED



(* maps are lists of associations. Cf enc_ass *)
Definition enc_map_def:
  enc_map : (index # mlstring) list -> byteCode = enc_vector enc_ass
End

Definition dec_map_def:
  dec_map : byteSeq -> (index # mlstring) list dcdr = dec_vector dec_ass
End

Theorem dec_map_shortens:
  ∀bs rs x. dec_map  bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rw[dec_map_def, AllCaseEqs()]
  \\ assume_tac dec_ass_shortens
  \\ imp_res_tac dec_vector_shortens_lt
QED


Definition magic_str_def:
  magic_str : string = "name"
End

Definition blank_def:
  blank : names =
  <| mname  := strlit ""
   ; fnames := []
   ; lnames := []
   |>
End


Definition enc_names_section_def:
  enc_names_section (n:names) =
    let ss0Opt : byteCode = let ascii = explode n.mname
                            in
                            if ¬(id_OK ascii) then NONE else
                            enc_section 0w  enc_byte   $ string2bytes ascii in
    let ss1Opt : byteCode = enc_section 1w  enc_ass                n.fnames in
    let ss2Opt : byteCode = enc_section 2w (enc_idx_alpha enc_map) n.lnames in
    do
    ss0      <- ss0Opt;
    ss1      <- ss1Opt;
    ss2      <- ss2Opt;
    ss012   <<- ss0 +++ ss1 +++ ss2;
    contents <- prepend_sz $ List (string2bytes magic_str) +++ ss012;
    if NULL $ append ss012 then NONE
    else
    SOME $ 0w ::: contents od
End

Definition dec_names_section_def:
  dec_names_section [] : names list dcdr = ret [] []
  ∧
  dec_names_section (b::bs) =
    let failure = error (b::bs) ""
    in
    if b ≠ 0w then ret (b::bs) [] (* NS (names section) leadByte *)
    else
    case dec_u32 bs of (INL _,_) => failure | (INR _,bs) (* length of the NS *)
    =>
    case bs of
    | []      => failure
    | [_]     => failure
    | [_;_]   => failure
    | [_;_;_] => failure
    | [n;a;m;e]         => if bytes2string $ [n;a;m;e] ≠ magic_str then failure else ret [] $ [blank]
    | n::a::m::e::b::bs => if bytes2string $ [n;a;m;e] ≠ magic_str then failure else
    case dec_section 0w  dec_byte               bs of (INL _,_)=>failure| (INR so , bs) =>
    case dec_section 1w  dec_ass                bs of (INL _,_)=>failure| (INR fns, bs) =>
    case dec_section 2w (dec_idx_alpha dec_map) bs of (INL _,_)=>failure| (INR lns, bs) =>
    ret bs $ [
    <|  mname  := implode $ bytes2string so
     ;  fnames := fns
     ;  lnames := lns
     |> : names]
End

Theorem dec_names_section_shortens:
  ∀bs rs x. dec_names_section bs = (INR x, rs) ⇒ rs [≤] bs
Proof
  Cases
  >> rw[dec_names_section_def, AllCaseEqs()]
    >- simp[]
    >- simp[]
    \\
       imp_res_tac dec_u32_shortens
    \\ assume_tac dec_byte_shortens
    \\ assume_tac dec_ass_shortens
    \\ assume_tac dec_map_shortens
    \\ dxrule dec_idx_alpha_shortens_lt
    \\ strip_tac
    \\ imp_res_tac dec_section_shortens_maybe_lt
    \\ gvs[]
QED



Definition mod_leader_def:
  (* this is a magic num/list that must lead all WBF encoded modules *)
  mod_leader : byteSeq = [
    0x00w; 0x61w; 0x73w; 0x6Dw;   (* "\0asm"                      *)
    0x01w; 0x00w; 0x00w; 0x00w]   (* version number of Bin format *)
End


(* From CWasm (not Wasm!) modules to WBF *)
Definition enc_module_def:
  enc_module (m:module) (n:names) =
    let (funs, code) = split_funcs m.funcs in do
    m_types    <- enc_section   1w enc_functype  m.types  ;
    m_funs     <- enc_section   3w enc_u32       funs     ;
    m_mems     <- enc_section   5w enc_limits    m.mems   ;
    m_globals  <- enc_section   6w enc_global    m.globals;
    m_code     <- enc_section  10w enc_code      code     ;
    m_datas    <- enc_section  11w enc_data      m.datas  ;
    nms        <- enc_names_section              n        ;
      SOME $ List mod_leader +++
      m_types    +++ m_funs  +++ m_mems   +++
      m_globals  +++ m_code  +++ m_datas  +++ nms od
End



Definition dec_module_def:
  dec_module bs : (module # names) dcdr = case bs of
  | l1::l2::l3::l4::l5::l6::l7::l8::bs => (
    let failure = error bs "[dec_module] : malformed leader"
    in
    if [l1;l2;l3;l4;l5;l6;l7;l8] ≠ mod_leader then failure
    else
    case dec_section  1w dec_functype bs of (INL _,_)=>failure| ret bs m_types   =>
    case dec_section  3w dec_u32      bs of (INL _,_)=>failure| ret bs   funs    =>
    case dec_section  5w dec_limits   bs of (INL _,_)=>failure| ret bs m_mems    =>
    case dec_section  6w dec_global   bs of (INL _,_)=>failure| ret bs m_globals =>
    case dec_section 10w dec_code     bs of (INL _,_)=>failure| ret bs   code    =>
    case dec_section 11w dec_data     bs of (INL _,_)=>failure| ret bs m_datas   =>
    case dec_names_section            bs of ret bs [n]       =>
      let m_funcs = zip_funcs funs code in
      let m = <| types := m_types  ; funcs   := m_funcs
               ; mems  := m_mems   ; globals := m_globals
               ; datas := m_datas  |> : module
      in
      ret bs (m,n)
    | _ => failure )
  | _  => error bs "[dec_module]: missing leader (less than 8 bytes)"
End

Theorem dec_module_shortens:
  ∀bs rs x. dec_module bs = (INR x, rs) ⇒ rs [≤] bs
Proof
     simp[dec_module_def, AllCaseEqs(), mod_leader_def]
  \\ rpt strip_tac \\ gvs[]
  \\ rpt (dxrule_at Any dec_section_shortens_maybe_lt)
  \\ dxrule dec_names_section_shortens
  \\ simp[ dec_limits_shortens, dec_code_shortens, dec_functype_shortens
         , dec_global_shortens, dec_data_shortens, dec_u32_shortens    ]
QED

