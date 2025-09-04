(*
  Some supporting operations
*)

Theory      ancillaryOps
Ancestors   byte words arithmetic list leb128
Libs        preamble wordsLib blastLib

(*****************************)
(*                           *)
(*     General Overloads     *)
(*                           *)
(*****************************)

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”

Overload b2w = “(λ b. if b then 1w else 0w):bool -> α word”

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

Overload dec_u8  = “dec_unsigned_word : byteSeq -> (byte   # byteSeq) option”
Overload dec_u32 = “dec_unsigned_word : byteSeq -> (word32 # byteSeq) option”
Overload dec_u64 = “dec_unsigned_word : byteSeq -> (word64 # byteSeq) option”

Overload dec_s8  = “dec_signed_word   : byteSeq -> (byte   # byteSeq) option”
Overload dec_s32 = “dec_signed_word   : byteSeq -> (word32 # byteSeq) option”
Overload dec_s64 = “dec_signed_word   : byteSeq -> (word64 # byteSeq) option”

Overload enc_u8  = “enc_unsigned_word : byte   -> byteSeq”
Overload enc_u32 = “enc_unsigned_word : word32 -> byteSeq”
Overload enc_u64 = “enc_unsigned_word : word64 -> byteSeq”

Overload enc_s8  = “enc_signed_word8  : byte   -> byteSeq”
Overload enc_s32 = “enc_signed_word32 : word32 -> byteSeq”
Overload enc_s64 = “enc_signed_word64 : word64 -> byteSeq”

Definition enc_2u32_def:
  enc_2u32 w v = enc_u32 w ++ enc_u32 v
End

Definition dec_2u32_def:
  dec_2u32 (bs:byteSeq) : (word32 # word32 # byteSeq) option = do
    (n,bs) <- dec_u32 bs;
    (m,bs) <- dec_u32 bs;
    return (n,m,bs) od
End

Definition enc_2u32_u8_def:
  enc_2u32_u8 ofs al lid = enc_2u32 ofs al ++ enc_u8 lid
End

Definition dec_2u32_u8_def:
  dec_2u32_u8 (bs:byteSeq) : (word32 # word32 # byte # byteSeq) option = do
    (i,j,bs) <- dec_2u32 bs;
    (k,  bs) <- dec_u8   bs;
      return (i,j,k,bs) od
End

(* Due to a perculiarity of Wasm (cf Block types - Index case from Wasm 2.0) *)
Definition enc_s33_def:
  enc_s33 (w:33 word) =
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

Overload dec_s33 = “dec_signed_word : byteSeq ->(33 word # byteSeq) option”

(***********************)
(*   Shortening Thms   *)
(***********************)

(* ASKYK
Theorem dec_num_shortens:
  dec_num bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  Induct_on ‘bs’ >> simp[dec_num_def]
  \\ rpt gen_tac
  \\ Cases_on ‘word_msb h’ >> gvs[]
  \\ Cases_on ‘dec_num bs’ >> gvs[]
  \\ PairCases_on `x'`
  \\ rw[] \\ fs[]
  \\ cheat
QED
*)

Theorem dec_u8_shortens[simp]:
  ∀bs x rs. dec_u8 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_unsigned_word_shortens \\ rewrite_tac[]
QED

Theorem dec_u32_shortens[simp]:
  ∀bs x rs. dec_u32 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_unsigned_word_shortens \\ rewrite_tac[]
QED

Theorem dec_u64_shortens[simp]:
  ∀bs x rs. dec_u64 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_unsigned_word_shortens \\ rewrite_tac[]
QED

Theorem dec_2u32_shortens[simp]:
  ∀bs x y rs. dec_2u32 bs = SOME (x, y, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rw[dec_2u32_def, AllCaseEqs()]
  \\ Cases_on ‘x'’ \\ gvs[]
  \\ Cases_on ‘x'’ \\ gvs[]
  \\ dxrule dec_u32_shortens
  \\ dxrule dec_u32_shortens
  \\ simp[]
QED

Theorem dec_s8_shortens[simp]:
  ∀bs x rs. dec_s8 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_signed_word_shortens \\ rewrite_tac[]
QED

Theorem dec_s32_shortens[simp]:
  ∀bs x rs. dec_s32 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_signed_word_shortens \\ rewrite_tac[]
QED

Theorem dec_s64_shortens[simp]:
  ∀bs x rs. dec_s64 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_signed_word_shortens \\ rewrite_tac[]
QED

Theorem dec_s33_shortens[simp]:
  ∀bs x rs. dec_s33 bs = SOME (x, rs) ⇒ LENGTH rs < LENGTH bs
Proof
  rpt strip_tac \\ dxrule dec_signed_word_shortens \\ rewrite_tac[]
QED



(********************)
(*   Dec-Enc thms   *)
(********************)

(* NOTE: these cannot be trivialities because they also do typecasting *)
Theorem dec_enc_u32[simp]:
  ∀w rest. dec_u32 (enc_u32 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_unsigned_word]
QED

Theorem dec_enc_s8[simp]:
  ∀w rest. dec_s8 (enc_s8 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_signed_word8]
QED

Theorem dec_enc_s32[simp]:
  ∀w rest. dec_s32 (enc_s32 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_signed_word32]
QED

Theorem dec_enc_s64[simp]:
  ∀w rest. dec_s64 (enc_s64 w ++ rest) = SOME (w,rest)
Proof
  rw[dec_enc_signed_word64]
QED

Theorem dec_enc_s33[simp]:
  ∀b xs rest. dec_s33 (enc_s33 b ++ rest) = SOME (b,rest)
Proof
  rw [enc_s33_def,dec_signed_word_def]
  >> fs [dec_enc_w7s,or_w7s_def]
    >> rpt $ pop_assum mp_tac
    >> blastLib.BBLAST_TAC
QED


Theorem dec_enc_2u32[simp]:
  ∀w v rest. dec_2u32 (enc_2u32 w v ++ rest) = SOME (w,v,rest)
Proof
  rw[enc_2u32_def, dec_2u32_def, AllCaseEqs()]
  \\ simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC"]
QED

Theorem dec_enc_2u32_u8[simp]:
  ∀ofs al lid rest. dec_2u32_u8 (enc_2u32_u8 ofs al lid ++ rest) = SOME (ofs,al,lid,rest)
Proof
  rw[dec_2u32_u8_def, enc_2u32_u8_def]
  \\ simp[GSYM APPEND_ASSOC, Excl "APPEND_ASSOC", dec_enc_2u32, dec_enc_unsigned_word]
QED





(***********************************************)
(*                                             *)
(*     Little endian stuff from byteTheory     *)
(*                                             *)
(***********************************************)

(*****************)
(*   Functions   *)
(*****************)

Overload lend    = “λ (w:α word ). (word_to_bytes w F):byteSeq”
Overload lend32  = “λ (w:word32 ). (word_to_bytes w F):byteSeq”
Overload lend64  = “λ (w:word64 ). (word_to_bytes w F):byteSeq”
Overload lend128 = “λ (w:word128). (word_to_bytes w F):byteSeq”

Definition unlend_def:
  unlend (bs:byteSeq): (α word # byteSeq) option =
    let n = dimindex(:α) DIV 8 in
    if LENGTH bs < n then NONE else SOME
    ( word_of_bytes F 0w $ TAKE n bs      (* F selects little endian mode *)
    ,                      DROP n bs)
End

Overload unlend32  = “unlend : byteSeq -> (word32  # byteSeq) option”
Overload unlend64  = “unlend : byteSeq -> (word64  # byteSeq) option”
Overload unlend128 = “unlend : byteSeq -> (word128 # byteSeq) option”



(**************************)
(*   decode-encode thms   *)
(**************************)

Theorem unlend_lend32[simp]:
  unlend32 (lend32 w ++ rest) = SOME (w, rest)
Proof
  simp[unlend_def]
  >> `4 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes]
  >> asm_rewrite_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
  >> rw[word_to_bytes_word_of_bytes_32]
QED

Theorem unlend_lend64[simp]:
  unlend64 (lend64 w ++ rest) = SOME (w, rest)
Proof
  simp[unlend_def]
  >> `8 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes]
  >> asm_rewrite_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
  >> rw[word_to_bytes_word_of_bytes_64]
QED

Theorem unlend_lend128[simp]:
  unlend128 (lend128 w ++ rest) = SOME (w, rest)
Proof
  simp[unlend_def]
  >> `16 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes]
  >> asm_rewrite_tac[TAKE_LENGTH_APPEND, DROP_LENGTH_APPEND]
  >> cheat
QED



(*************************************************************************)
(*                                                                       *)
(*     Ops for Wasm semantics (not already existing in wordsThy/Lib)     *)
(*                                                                       *)
(*************************************************************************)

(***********************************)
(*   Functions (& ancillary fns)   *)
(***********************************)

Overload popcnt = “λ (w:α word). (n2w $ bit_count w): β word”
Overload onehot = “λ (w:α word). (b2w ((popcnt w):γ word = 1w)): β word”

(* sign extend *)
Definition sext_def:
  sext   Signed = sw2sw ∧
  sext Unsigned = w2w
End

(* Conversions/truncates/extends *)
Overload extend8s  = “λ (w:α word). sw2sw (w2w w:word8 ):β word”
Overload extend16s = “λ (w:α word). sw2sw (w2w w:word16):β word”
Overload extend32s = “λ (w:α word). sw2sw (w2w w:word32):β word”
(* Overload extend8s = “λ w. sw2sw $ (w2w w):word8”
Overload extend8s = “λ w. sw2sw $ (w2w w):word8” *)

Definition ctz_def: (* count trailing zeros *)
  ctz (w:α word) : β word = n2w (bit_count (w ⊕ (w-1w)) - 1)
End

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End



(*************)
(*   Specs   *)
(*************)

Theorem ctz_spec_sound:
  ∀ n. n < w2n (ctz w) ⇒ ¬ w ' n
Proof
  (* I kind of don't know where to start here... *)
  (* clearly the "real" coal face is all the way
     inside ctz_def, starting at "w-1w"

     I want some way to be able to capture how
     w-1w is different from w. Or rather
     To characterize "w ⊕ (w-1w)".
  *)
  (* Most of all, such a proof won't proceed
     "structurally" cos I don't think words
     _are_ defined structurally. (MM said this too I think)

     so we would want to appeal to thms about the
     existing word ops that we do already use
     (MM: ditto)
  *)
  cheat
QED

Theorem ctz_spec_complete:
  ∀ w. 0w <+ w >> w2n (ctz w)
Proof
  (* cf ctz_spec1... *)
  cheat
QED



Theorem clz_spec_sound:
  ∀ n. (dimindex(:α) - n) < w2n (ctz (w:α word)) ⇒ w ' n = F
Proof
  cheat
QED





(****************************************)
(*                                      *)
(*     Memory semantics for wasmSem     *)
(*                                      *)
(****************************************)

(* REPLACE ASKYK *)
Definition load_def:
  load (n:num) (i:word32) (offs:α word) (bs:byte list) : (γ word # bool) =
    let ea = w2n i + w2n offs
    in
    ( word_of_bytes F 0w $ TAKE n $ DROP ea bs
    , ea + n <= LENGTH bs )
End

Definition store_def:
  store (payload:α word) (i:word32) (offs:β word) (m:byte list) : (byte list # bool) =
    let ea = w2n i + w2n offs   in
    let n  = dimindex(:α) DIV 8
    in
    ( TAKE ea m  ⧺  word_to_bytes payload F  ⧺  DROP (ea + n) m
    , ea + n ≤ LENGTH m)
End

Theorem load_store:
  ∀n x i ofs m m'.
    n = dimindex(:α) DIV 8 ∧
    store (x:α word) i ofs m = (m',T)
    ⇒
    load n i ofs m'  = (x,T)
Proof
  rpt gen_tac
  \\ gvs[store_def, load_def]
  \\ rpt strip_tac
  \\
  cheat
QED

