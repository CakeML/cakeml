(*
  Ancillaries for En- & De- coding between CWasm 1.ε AST & Wasm's binary format
  such as:
  - Types
  - General (leb128) en-/de- coders
  - Helpful Corollaries
*)
Theory      wbf_ancil
Ancestors   wasmLang leb128
Libs        preamble wordsLib


(******************************)
(*                            *)
(*      General concepts      *)
(*                            *)
(******************************)

(*  Note:
    Encoders ("enc_X") go from AST (elements) to optional (CakeML) app_lists of bytes
      Though many encoders do not have a failure mode (always "SOME"), for consistency,
      we have all encoders return options

    Decoders ("dec_X") take a stream of bytes and produce elements of the CWasm
    AST (or an error) & additionally return the remaining bytes (stream)     *)

Type byte[pp]     = “:word8”
Type byteSeq[pp]  = “:word8 list”
Type byteCode[pp] = “:word8 app_list option”
Type dcdr[pp]     = “:(mlstring + α) # byteSeq”
(*  *)
Overload ret   = “λ bs a. (INR a, bs)”
Overload err   = “(INL $ strlit "", [])”
Overload error = “λ bs str. (INL $ strlit str,bs)”
Overload emErr = “λ str. (INL $ strlit $ "[" ++ str ++ "] : Byte sequence ended unexpectedly.\n",[])”
Overload lift = “ (λ absOpt.
  case absOpt of
  | NONE => err
  | SOME (a,bs) => (INR a, bs)  )”

(* list-shorter-than *)
val _ = set_fixity "[<]" (Infixl 500);
Overload "[<]" =  “(λxs ys. LENGTH xs < LENGTH ys): α list -> α list -> bool”

val _ = set_fixity "[≤]" (Infixl 500);
Overload "[≤]" =  “(λxs ys. LENGTH xs ≤ LENGTH ys): α list -> α list -> bool”

val _ = set_fixity "+++" (Infixr 490);
Overload "+++" = “Append”               (* cf cakeml/misc/miscScript.sml *)

val _ = set_fixity ":::" (Infixr 485);
Overload ":::" =  “(λx ys. Append (List [x:byte]) ys): byte -> byte app_list -> byte app_list”



val _ = monadsyntax.enable_monadsyntax()
val _ = monadsyntax.enable_monad "option"

(******************************************)
(*                                        *)
(*     LEB128 Overloads and typecasts     *)
(*                                        *)
(******************************************)

(**************************************************)
(*   Functions, or rather, typecastings thereof   *)
(**************************************************)

(* Overload dec_u8  = “dec_unsigned_word : byteSeq -> (byte   # byteSeq) option”
Overload dec_u32 = “dec_unsigned_word : byteSeq -> (word32 # byteSeq) option”
Overload dec_u64 = “dec_unsigned_word : byteSeq -> (word64 # byteSeq) option”

Overload dec_s8  = “dec_signed_word   : byteSeq -> (byte   # byteSeq) option”


Overload enc_u64 = “enc_unsigned_word : word64 -> byteSeq”

Overload enc_s8  = “enc_signed_word8  : byte   -> byteSeq” *)

Definition enc_s32_def:
  enc_s32 (w:word32) = SOME $ List $ enc_signed_word32 w
End

Definition dec_s32_def:
  dec_s32 bs : word32 dcdr = lift $ dec_signed_word bs
End

Theorem dec_s32_shortens:
  ∀bs rs _x. dec_s32 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_s32_def, AllCaseEqs()]
  \\ dxrule dec_signed_word_shortens
  \\ rewrite_tac[]
QED


Definition enc_s64_def:
  enc_s64 (w:word64) = SOME $ List $ enc_signed_word64 w
End

Definition dec_s64_def:
  dec_s64 bs : word64 dcdr = lift $ dec_signed_word bs
End

Theorem dec_s64_shortens:
  ∀bs rs _x. dec_s64 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_s64_def, AllCaseEqs()]
  \\ dxrule dec_signed_word_shortens
  \\ rewrite_tac[]
QED



Definition enc_u8_def:
  enc_u8 (w:byte) = SOME $ List $ enc_unsigned_word w
End

Definition dec_u8_def:
  dec_u8 bs : byte dcdr = lift $ dec_unsigned_word bs
End

Theorem dec_u8_shortens:
  ∀bs rs _x. dec_u8 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_u8_def, AllCaseEqs()]
  \\ dxrule dec_unsigned_word_shortens
  \\ rewrite_tac[]
QED


Definition enc_u32_def:
  enc_u32 (w:word32) = SOME $ List $ enc_unsigned_word w
End

Definition dec_u32_def:
  dec_u32 bs : word32 dcdr = lift $ dec_unsigned_word bs
End

Theorem dec_u32_shortens:
  ∀bs rs _x. dec_u32 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_u32_def, AllCaseEqs()]
  \\ dxrule dec_unsigned_word_shortens
  \\ rewrite_tac[]
QED


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

Theorem dec_2u32_shortens:
  ∀bs rs _x. dec_2u32 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_2u32_def, AllCaseEqs()]
  \\ dxrule dec_u32_shortens
  \\ dxrule dec_u32_shortens
  \\ simp[]
QED


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

Theorem dec_2u32_u8_shortens:
  ∀bs rs _x. dec_2u32_u8 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_2u32_u8_def, AllCaseEqs()]
  \\ dxrule dec_2u32_shortens
  \\ dxrule dec_u8_shortens
  \\ simp[]
QED


(* Due to a perculiarity of Wasm (cf Block types - Index case from Wasm 2.0) *)
Definition enc_s33_def:
  enc_s33 (w:33 word) = SOME $
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

(* Overload dec_s33 = “dec_signed_word : byteSeq -> (33 word # byteSeq) option” *)
Definition dec_s33_def:
  dec_s33 bs : (33 word) dcdr = lift $ dec_signed_word bs
End

Theorem dec_s33_shortens:
  ∀bs rs _x. dec_s33 bs = (INR _x, rs) ⇒ rs [<] bs
Proof
     rpt gen_tac
  \\ rw[dec_s33_def, AllCaseEqs()]
  \\ dxrule dec_signed_word_shortens
  \\ rewrite_tac[]
QED

