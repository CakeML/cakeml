(*
  Some extra operations
  No specs yet
*)

open preamble leb128Theory;
open wordsTheory wordsLib;
open byteTheory;

val _ = new_theory "miscOps";

(*****************************)
(*                           *)
(*     General Overloads     *)
(*                           *)
(*****************************)

Type byte[local]    = “:word8”
Type byteSeq[local] = “:word8 list”

Overload b2w = “(λ b. if b then 1w else 0w):bool -> α word”

(******************************************)
(*                                        *)
(*     LEB128 Overloads and typecasts     *)
(*                                        *)
(******************************************)

Overload dec_u8  = “dec_unsigned_word : byteSeq -> (byte   # byteSeq) option”
Overload dec_u32 = “dec_unsigned_word : byteSeq -> (word32 # byteSeq) option”
Overload dec_u64 = “dec_unsigned_word : byteSeq -> (word64 # byteSeq) option”

Overload dec_s8  = “dec_signed        : byteSeq -> (byte   # byteSeq) option”
Overload dec_s32 = “dec_signed        : byteSeq -> (word32 # byteSeq) option”
Overload dec_s64 = “dec_signed        : byteSeq -> (word64 # byteSeq) option”

Overload enc_u8  = “enc_unsigned_word : byte   -> byteSeq”
Overload enc_u32 = “enc_unsigned_word : word32 -> byteSeq”
Overload enc_u64 = “enc_unsigned_word : word64 -> byteSeq”

Overload enc_s8  = “enc_signed_word8  : byte   -> byteSeq”
Overload enc_s32 = “enc_signed_word32 : word32 -> byteSeq”
Overload enc_s64 = “enc_signed_word64 : word64 -> byteSeq”

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

(* NOTE: these cannot be trivialities because they also do typecasting *)
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
(*     Little endian stuff from byteTheory     *)
(*                                             *)
(***********************************************)

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

Theorem unlend_lend32[simp]:
  unlend32 (lend32 w ++ rest) = SOME (w, rest)
Proof
  simp[unlend_def]
  (* this is how you do asserts *)
  >> `4 = LENGTH (word_to_bytes w F)` by simp[LENGTH_word_to_bytes]
  (* asm_rw additionally uses the assumptions to rewrite *)
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
  (* this doesn't work because we used library functions
     there's no lib thm specialized to 128 bits *)
  (* >> rw[word_to_bytes_word_of_bytes_128] *)
  >> cheat
QED



(*********************************************)
(*                                           *)
(*     Word ops missing from wordsTheory     *)
(*                                           *)
(*********************************************)

Overload popcnt = “λ (w:α word). (n2w $ bit_count w): β word”
Overload onehot = “λ (w:α word). (b2w ((popcnt w):γ word = 1w)): β word”

Definition ctz_def: (* count trailing zeros *)
  ctz (w:α word) : β word = n2w (bit_count (w ⊕ (w-1w)) - 1)
End

Definition clz_def: (* count leading zeros *)
  clz (w:α word) : β word = ctz $ word_reverse w
End



(****************************************)
(*                                      *)
(*     Memory semantics for wasmSem     *)
(*                                      *)
(****************************************)


(* REPLACE ASKMM *)
Definition take_def:
  take (n:num) (xs: α list) : (α list # bool) = (TAKE n xs, n <= LENGTH xs)
End

Definition load_def:
  load (n:num) (offs:α word) (algn:β word) (bs:byteSeq) : (γ word # bool) =
    let ofs = w2n offs in
    let alg = w2n algn in
    let bs' = DROP (ofs * alg) bs in
    case unlend bs' of
    | NONE       => (0w,F)
    | SOME (v,_) => (v ,T)
End

Definition store_def:
  store (x:α word) (offs:β word) (algn:γ word) (bs:byteSeq) : (byteSeq # bool) =
    let oa = (w2n offs) * (w2n algn) in
    let n = dimindex(:α) DIV 8 in
    (TAKE oa bs ⧺ lend x ⧺ DROP (oa + n) bs, oa + n <= LENGTH bs)
End

(* print_match [] "word_to_bytes" *)

Theorem clz_spec:
  ∀ n. (dimindex(:α) - n) < w2n (ctz (w:α word)) ⇒ w ' n = F
Proof
  cheat
QED


Theorem ctz_spec1:
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

Theorem ctz_spec2:
  ∀ w. 0w <+ w >> w2n (ctz w)
Proof
  (* cf ctz_spec1... *)
  cheat
QED





val _ = export_theory();




(* print_match [] ``TAKE (LENGTH xs) (xs ++ ys)`` *)







(*
type_of  ``word_to_bytes_word_of_bytes_32``
print_match [] ``word_to_bytes_word_of_bytes_32``
f ``word_to_bytes_word_of_bytes_32``


Overload unlend32  = “unlend  4 []”
Overload unlend64  = “unlend  8 []”
Overload unlend128 = “unlend 16 []”
*)



(*                vestigial                   *)


(* Definition list_to_def:
  list_to (0:num) : num list = [0] ∧
  list_to n = list_to (n-1) ++ [n]
End *)

(* val it =
   ⊢ (∀f. GENLIST f 0 = []) ∧
     ∀f n. GENLIST f (SUC n) = SNOC (f n) (GENLIST f n): thm *)











(* print_match [] ``word_to_bytes`` *)


(*
byteTheory.word_of_bytes_bytes_to_word (THEOREM)
------------------------------------------------
⊢ ∀be a bs k.
    LENGTH bs ≤ k ⇒ word_of_bytes be a bs = bytes_to_word k a bs 0w be
[$(HOLDIR)/src/n-bit/byteScript.sml:260]


byteTheory.word_of_bytes_def (DEFINITION)
-----------------------------------------
⊢ (∀be a. word_of_bytes be a [] = 0w) ∧
  ∀be a b bs.
    word_of_bytes be a (b::bs) =
    set_byte a b (word_of_bytes be (a + 1w) bs) be
[$(HOLDIR)/src/n-bit/byteScript.sml:129]


byteTheory.word_to_bytes_word_of_bytes_32 (THEOREM)
---------------------------------------------------
⊢ word_of_bytes be 0w (word_to_bytes w be) = w
[$(HOLDIR)/src/n-bit/byteScript.sml:820]


byteTheory.word_to_bytes_word_of_bytes_64 (THEOREM)
---------------------------------------------------
⊢ word_of_bytes be 0w (word_to_bytes w be) = w
[$(HOLDIR)/src/n-bit/byteScript.sml:834]


byteTheory.words_of_bytes_append_word (THEOREM)
-----------------------------------------------
⊢ 0 < LENGTH l1 ∧ LENGTH l1 = w2n bytes_in_word ⇒
  words_of_bytes be (l1 ++ l2) = word_of_bytes be 0w l1::words_of_bytes be l2
[$(HOLDIR)/src/n-bit/byteScript.sml:231]


byteTheory.words_of_bytes_def (THEOREM)
---------------------------------------
⊢ (∀be. words_of_bytes be [] = []) ∧
  ∀v3 v2 be.
    words_of_bytes be (v2::v3) =
    (let
       xs = TAKE (MAX 1 (w2n bytes_in_word)) (v2::v3);
       ys = DROP (MAX 1 (w2n bytes_in_word)) (v2::v3)
     in
       word_of_bytes be 0w xs::words_of_bytes be ys)


byteTheory.bytes_to_word_def (THEOREM)
--------------------------------------
⊢ ∀w k bs be a.
    bytes_to_word k a bs w be =
    if k = 0 then w
    else
      case bs of
        [] => w
      | b::bs' => set_byte a b (bytes_to_word (k − 1) (a + 1w) bs' w be) be
[$(HOLDIR)/src/n-bit/byteScript.sml:243]


byteTheory.bytes_to_word_eq (THEOREM)
-------------------------------------
⊢ bytes_to_word 0 a bs w be = w ∧ bytes_to_word k a [] w be = w ∧
  bytes_to_word (SUC k) a (b::bs) w be =
  set_byte a b (bytes_to_word k (a + 1w) bs w be) be
[$(HOLDIR)/src/n-bit/byteScript.sml:251]


byteTheory.get_byte_set_byte (THEOREM)
--------------------------------------
⊢ 8 ≤ dimindex (:α) ⇒ get_byte a (set_byte a b w be) be = b
[$(HOLDIR)/src/n-bit/byteScript.sml:90]


byteTheory.get_byte_set_byte_irrelevant (THEOREM)
-------------------------------------------------
⊢ 16 ≤ dimindex (:α) ∧
  w2n a MOD (dimindex (:α) DIV 8) ≠ w2n a' MOD (dimindex (:α) DIV 8) ⇒
  get_byte a' (set_byte a b w be) be = get_byte a' w be
[$(HOLDIR)/src/n-bit/byteScript.sml:437]


byteTheory.set_byte_32 (THEOREM)
--------------------------------
⊢ set_byte a b w be =
  (let
     i = byte_index a be
   in
     if i = 0 then w2w b ‖ w && 0xFFFFFF00w
     else if i = 8 then w2w b ≪ 8 ‖ w && 0xFFFF00FFw
     else if i = 16 then w2w b ≪ 16 ‖ w && 0xFF00FFFFw
     else w2w b ≪ 24 ‖ w && 0xFFFFFFw)
[$(HOLDIR)/src/n-bit/byteScript.sml:38]


byteTheory.set_byte_64 (THEOREM)
--------------------------------
⊢ set_byte a b w be =
  (let
     i = byte_index a be
   in
     if i = 0 then w2w b ‖ w && 0xFFFFFFFFFFFFFF00w
     else if i = 8 then w2w b ≪ 8 ‖ w && 0xFFFFFFFFFFFF00FFw
     else if i = 16 then w2w b ≪ 16 ‖ w && 0xFFFFFFFFFF00FFFFw
     else if i = 24 then w2w b ≪ 24 ‖ w && 0xFFFFFFFF00FFFFFFw
     else if i = 32 then w2w b ≪ 32 ‖ w && 0xFFFFFF00FFFFFFFFw
     else if i = 40 then w2w b ≪ 40 ‖ w && 0xFFFF00FFFFFFFFFFw
     else if i = 48 then w2w b ≪ 48 ‖ w && 0xFF00FFFFFFFFFFFFw
     else w2w b ≪ 56 ‖ w && 0xFFFFFFFFFFFFFFw)
[$(HOLDIR)/src/n-bit/byteScript.sml:56]


byteTheory.set_byte_change_a (THEOREM)
--------------------------------------
⊢ w2n a MOD (dimindex (:α) DIV 8) = w2n a' MOD (dimindex (:α) DIV 8) ⇒
  set_byte a b w be = set_byte a' b w be
[$(HOLDIR)/src/n-bit/byteScript.sml:82]


byteTheory.set_byte_cycle (THEOREM)
-----------------------------------
⊢ 8 ≤ dimindex (:α) ⇒
  set_byte (n2w (w2n a MOD (dimindex (:α) DIV 8))) b w be = set_byte a b w be
[$(HOLDIR)/src/n-bit/byteScript.sml:350]


byteTheory.set_byte_def (DEFINITION)
------------------------------------
⊢ ∀a b w is_bigendian.
    set_byte a b w is_bigendian =
    (let
       i = byte_index a is_bigendian
     in
       word_slice_alt (dimindex (:α)) (i + 8) w ‖ w2w b ≪ i ‖
       word_slice_alt i 0 w)
[$(HOLDIR)/src/n-bit/byteScript.sml:30]


byteTheory.set_byte_get_byte (THEOREM)
--------------------------------------
⊢ 8 ≤ dimindex (:α) ⇒ set_byte a (get_byte a w be) w be = w
[$(HOLDIR)/src/n-bit/byteScript.sml:734]


byteTheory.set_byte_get_byte' (THEOREM)
---------------------------------------
⊢ 8 ≤ dimindex (:α) ⇒ set_byte a (get_byte a w be) w be = w
[$(HOLDIR)/src/n-bit/byteScript.sml:789]


byteTheory.set_byte_get_byte_copy (THEOREM)
-------------------------------------------
⊢ 8 ≤ dimindex (:α) ⇒
  set_byte a (get_byte a w be) w' be =
  (byte_index a be + 7 '' byte_index a be) w ‖
  (if byte_index a be + 8 = dimindex (:α) then 0w
   else (dimindex (:α) − 1 '' byte_index a be + 8) w') ‖
  if byte_index a be = 0 then 0w else (byte_index a be − 1 '' 0) w'
[$(HOLDIR)/src/n-bit/byteScript.sml:760]


byteTheory.word_of_bytes_def (DEFINITION)
-----------------------------------------
⊢ (∀be a. word_of_bytes be a [] = 0w) ∧
  ∀be a b bs.
    word_of_bytes be a (b::bs) =
    set_byte a b (word_of_bytes be (a + 1w) bs) be
[$(HOLDIR)/src/n-bit/byteScript.sml:129]


miscTheory.get_byte_set_byte_diff (THEOREM)
-------------------------------------------
⊢ good_dimindex (:α) ∧ a ≠ a' ∧ byte_align a = byte_align a' ⇒
  get_byte a (set_byte a' b w be) be = get_byte a w be
[$(CAKEMLDIR)/misc/miscScript.sml:4386]


miscTheory.good_dimindex_get_byte_set_byte (THEOREM)
----------------------------------------------------
⊢ good_dimindex (:α) ⇒ get_byte a (set_byte a b w be) be = b
[$(CAKEMLDIR)/misc/miscScript.sml:4341]





byteTheory.LENGTH_word_to_bytes (THEOREM)
-----------------------------------------
⊢ LENGTH (word_to_bytes w be) = dimindex (:α) DIV 8
[$(HOLDIR)/src/n-bit/byteScript.sml:320]


byteTheory.word_to_bytes_def (DEFINITION)
-----------------------------------------
⊢ ∀w be. word_to_bytes w be = word_to_bytes_aux (dimindex (:α) DIV 8) w be
[$(HOLDIR)/src/n-bit/byteScript.sml:309]


byteTheory.word_to_bytes_word_of_bytes_32 (THEOREM)
---------------------------------------------------
⊢ word_of_bytes be 0w (word_to_bytes w be) = w
[$(HOLDIR)/src/n-bit/byteScript.sml:820]


byteTheory.word_to_bytes_word_of_bytes_64 (THEOREM)
---------------------------------------------------
⊢ word_of_bytes be 0w (word_to_bytes w be) = w
[$(HOLDIR)/src/n-bit/byteScript.sml:834]



byteTheory.LENGTH_word_to_bytes_aux (THEOREM)
---------------------------------------------
⊢ LENGTH (word_to_bytes_aux n w b) = n
[$(HOLDIR)/src/n-bit/byteScript.sml:314]


byteTheory.word_to_bytes_aux_compute (THEOREM)
----------------------------------------------
⊢ (∀w be. word_to_bytes_aux 0 w be = []) ∧
  (∀n w be.
     word_to_bytes_aux <..num comp'n..> w be =
     word_to_bytes_aux (<..num comp'n..> − 1) w be ++
     [get_byte (n2w (<..num comp'n..> − 1)) w be]) ∧
  ∀n w be.
    word_to_bytes_aux <..num comp'n..> w be =
    word_to_bytes_aux <..num comp'n..> w be ++
    [get_byte (n2w <..num comp'n..> ) w be]


byteTheory.word_to_bytes_aux_def (DEFINITION)
---------------------------------------------
⊢ (∀w be. word_to_bytes_aux 0 w be = []) ∧
  ∀n w be.
    word_to_bytes_aux (SUC n) w be =
    word_to_bytes_aux n w be ++ [get_byte (n2w n) w be]
[$(HOLDIR)/src/n-bit/byteScript.sml:302]


byteTheory.word_to_bytes_def (DEFINITION)
-----------------------------------------
⊢ ∀w be. word_to_bytes w be = word_to_bytes_aux (dimindex (:α) DIV 8) w be
[$(HOLDIR)/src/n-bit/byteScript.sml:309]


*)