(*
  Preliminaries for En- & De- coding between CWasm 1.ε AST & Wasm binary format
  such as:
  - Types
  - General (leb128) en-/de- coders
  - Helpful Corollaries
*)
Theory      wbf_prelim
Ancestors   wasmLang leb128
Libs        preamble wordsLib blastLib

val ssaa = fn xs => [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"] @ xs
val ssa  =          [GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]


(*  Encoders ("encx") have type “:α -> word8 app_list option”
    going from AST (elements) to optional (CakeML) app_lists of bytes
      Though many encoders do not have a failure mode (they always return "SOME"),
      for consistency, we have all encoders return options

    Decoders ("decx") have type “”
    take a stream of bytes and produce elements of the CWasm
    AST (or an error) & additionally return the remaining bytes (stream)   *)

(******************************)
(*                            *)
(*      General concepts      *)
(*                            *)
(******************************)

Type byte[pp]     = “:word8”
Type byteSeq[pp]  = “:word8 list”
Type byteCode[pp] = “:word8 app_list option”
Type dcdr[pp]     = “:(mlstring + α) # byteSeq”

(* Some helpers for the dcdr monad *)
(* errors are a little bit bogus now - they don't report the error very well *)
Overload err   = “          (INL $ implode ""                                                       ,[])”
Overload error = “λ bs str. (INL $ implode str                                                      ,bs)”
Overload emErr = “λ str.    (INL $ implode $ "[" ++ str ++ "] : Byte sequence ended unexpectedly.\n",[])”
Overload ret   = “λ bs a.   (INR a, bs)”
Overload lift  = “ (λ absOpt.
  case absOpt of
  | NONE => err
  | SOME (a,bs) => (INR a, bs)  )”

(* list-shorter-than *)
val _ = set_fixity "[<]" (Infixl 500);
Overload "[<]" =  “(λxs ys. LENGTH xs < LENGTH ys): α list -> α list -> bool”

val _ = set_fixity "[≤]" (Infixl 500);
Overload "[≤]" =  “(λxs ys. LENGTH xs ≤ LENGTH ys): α list -> α list -> bool”

val _ = set_fixity "+++" (Infixr 490);
Overload "+++" = “Append”                       (* cf cakeml/misc/miscScript.sml *)

val _ = set_fixity "a++" (Infixr 490);
Overload "a++" = “λxs ys. append xs ++ ys”      (* cf cakeml/misc/miscScript.sml *)

val _ = set_fixity ":::" (Infixr 485);
Overload ":::" =  “λx ys. Append (List [x:byte]) ys”

Overload Soli[local] = “(SOME ∘ List): byteSeq -> byteCode”



val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

(******************************)
(*                            *)
(*     LEB128 "typecasts"     *)
(*                            *)
(******************************)

Definition enc_s32_def:
  enc_s32 (w:word32) = Soli $ enc_signed_word32 w
End

Definition dec_s32_def:
  dec_s32 bs : word32 dcdr = lift $ dec_signed_word bs
End


Definition enc_s64_def:
  enc_s64 (w:word64) = Soli $ enc_signed_word64 w
End

Definition dec_s64_def:
  dec_s64 bs : word64 dcdr = lift $ dec_signed_word bs
End


(* we need s33 due to a perculiarity of Wasm (cf Block types - Index case from Wasm 2.0) *)
Definition enc_s33_def:
  enc_s33 (w:33 word) = Soli $
    if sw2sw ((w2w w):7 word) = w then
      enc_w7s [w2w w]
    else if sw2sw ((w2w w):14 word) = w then
      let w = (sw2sw w) :14 word in
        enc_w7s [w2w w;
                 w2w (w >>> 7)]
    else if sw2sw ((w2w w):21 word) = w then
      let w = (sw2sw w) :21 word in
        enc_w7s [w2w w;
                 w2w (w >>> 7);
                 w2w (w >>> 14)]
    else if sw2sw ((w2w w):28 word) = w then
      let w = (sw2sw w) :28 word in
        enc_w7s [w2w w;
                 w2w (w >>> 7);
                 w2w (w >>> 14);
                 w2w (w >>> 21)]
    else
      let w = (sw2sw w) :35 word in
        enc_w7s [w2w w;
                 w2w (w >>> 7);
                 w2w (w >>> 14);
                 w2w (w >>> 21);
                 w2w (w >>> 28)]
End

Definition dec_s33_def:
  dec_s33 bs : (33 word) dcdr = lift $ dec_signed_word bs
End





Definition enc_u8_def:
  enc_u8 (w:byte) = Soli $ enc_unsigned_word w
End

Definition dec_u8_def:
  dec_u8 bs : byte dcdr = lift $ dec_unsigned_word bs
End


Definition enc_u32_def:
  enc_u32 (w:word32) = Soli $ enc_unsigned_word w
End

Definition dec_u32_def:
  dec_u32 bs : word32 dcdr = lift $ dec_unsigned_word bs
End


Definition enc_2u32_def:
  enc_2u32 w v : byteCode = do
    a <- enc_u32 w;
    b <- enc_u32 v;
    SOME $ a +++ b od
End

Definition dec_2u32_def:
  dec_2u32 bs : (word32 # word32) dcdr =
    case dec_u32 bs of (INL _, _) => err | (INR n, bs) =>
    case dec_u32 bs of (INL _, _) => err | (INR m, bs) =>
    ret bs (n,m)
End


Definition enc_2u32_u8_def:
  enc_2u32_u8 ofs al lid = do
    a <- enc_2u32 ofs al;
    b <- enc_u8 lid;
    SOME $ a +++ b od
End

Definition dec_2u32_u8_def:
  dec_2u32_u8 bs : (word32 # word32 # byte) dcdr =
    case dec_2u32 bs of (INL _, _) => err | (INR (i,j), bs) =>
    case dec_u8   bs of (INL _, _) => err | (INR k    , bs) =>
    ret bs (i,j,k)
End





(**************************************)
(*                                    *)
(*     LEB128 shortening theorems     *)
(*                                    *)
(**************************************)

Theorem dec_s32_shortens:
  ∀bs rs x. dec_s32 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_s32_def, AllCaseEqs()]
  \\ dxrule dec_signed_word_shortens
  \\ rewrite_tac[]
QED

Theorem dec_s64_shortens:
  ∀bs rs x. dec_s64 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_s64_def, AllCaseEqs()]
  \\ dxrule dec_signed_word_shortens
  \\ rewrite_tac[]
QED

Theorem dec_s33_shortens:
  ∀bs rs x. dec_s33 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_s33_def, AllCaseEqs()]
  \\ dxrule dec_signed_word_shortens
  \\ rewrite_tac[]
QED



Theorem dec_u8_shortens:
  ∀bs rs x. dec_u8 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_u8_def, AllCaseEqs()]
  \\ dxrule dec_unsigned_word_shortens
  \\ rewrite_tac[]
QED

Theorem dec_u32_shortens:
  ∀bs rs x. dec_u32 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_u32_def, AllCaseEqs()]
  \\ dxrule dec_unsigned_word_shortens
  \\ rewrite_tac[]
QED

Theorem dec_2u32_shortens:
  ∀bs rs x. dec_2u32 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_2u32_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule dec_u32_shortens
  \\ simp[]
QED

Theorem dec_2u32_u8_shortens:
  ∀bs rs x. dec_2u32_u8 bs = (INR x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_2u32_u8_def, AllCaseEqs()]
  \\ dxrule dec_2u32_shortens
  \\ dxrule dec_u8_shortens
  \\ simp[]
QED





(***********************************)
(*                                 *)
(*     LEB128 dec-enc theorems     *)
(*                                 *)
(***********************************)

Theorem dec_enc_s32:
  ∀x encx rest. enc_s32 x = SOME encx ⇒
  dec_s32 $ append encx ++ rest = (INR x, rest)
Proof
     rw[enc_s32_def, dec_s32_def, AllCaseEqs()]
  \\ rw[append_def, dec_enc_signed_word32]
QED

Theorem dec_enc_s64:
  ∀x encx rest. enc_s64 x = SOME encx ⇒
  dec_s64 $ append encx ++ rest = (INR x, rest)
Proof
     rw[enc_s64_def, dec_s64_def, AllCaseEqs()]
  \\ rw[append_def, dec_enc_signed_word64]
QED

Theorem dec_enc_s33:
  ∀x encx rest. enc_s33 x = SOME encx ⇒
  dec_s33 $ append encx ++ rest = (INR x, rest)
Proof
     rw[dec_s33_def, AllCaseEqs(), enc_s33_def]
  >> rw[append_def, dec_signed_word_def, dec_enc_w7s, or_w7s_def]
  >> rpt $ pop_assum mp_tac
  >> BBLAST_TAC
QED

Theorem dec_enc_u8:
  ∀x encx rest. enc_u8 x = SOME encx ⇒
  dec_u8 $ append encx ++ rest = (INR x, rest)
Proof
     rw[dec_u8_def, enc_u8_def, AllCaseEqs()]
  \\ rw[append_def, dec_enc_unsigned_word]
QED

Theorem dec_enc_u32:
  ∀x encx rest. enc_u32 x = SOME encx ⇒
  dec_u32 $ append encx ++ rest = (INR x, rest)
Proof
     rw[dec_u32_def, enc_u32_def, AllCaseEqs()]
  \\ rw[append_def, dec_enc_unsigned_word]
QED

Theorem dec_enc_2u32:
  ∀x y encx rest. enc_2u32 x y = SOME encx ⇒
  dec_2u32 $ append encx ++ rest = (INR (x,y), rest)
Proof
     rw[dec_2u32_def, enc_2u32_def, AllCaseEqs()]
  \\ simp $ ssa
  \\ imp_res_tac dec_enc_u32
  \\ asm_rewrite_tac[]
  \\ gvs[]
QED

Theorem dec_enc_2u32_u8:
  ∀x y z encx rest. enc_2u32_u8 x y z = SOME encx ⇒
  dec_2u32_u8 $ append encx ++ rest = (INR (x,y,z), rest)
Proof
     rw[dec_2u32_u8_def, enc_2u32_u8_def, AllCaseEqs()]
  \\ simp $ ssa
  \\ imp_res_tac dec_enc_2u32
  \\ asm_rewrite_tac[]
  \\ gvs[]
  \\ imp_res_tac dec_enc_u8
  \\ gvs[]
QED
