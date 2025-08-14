(*
  A foramlisation of LEB128
*)
Theory leb128
Ancestors
  words arithmetic list
Libs
  wordsLib dep_rewrite

(*  API
    enc goes from words/nums to leb stream
    dec goes from leb stream to words/nums

  dec_num : lebStream -> (num # lebStream) option
  enc_num : num -> lebStream
  enc_num_def_primitive :num -> lebStream

  dec_unsigned_word : lebStream -> (α word # lebStream) option
  enc_unsigned_word : α word -> lebStream

  dec_w7s : lebStream -> (7 word list # lebStream) option
  enc_w7s : 7 word list -> lebStream
  or_w7s  : word7 list -> α word

  dec_signed        : lebStream -> (α word # lebStream) option
  enc_signed_byte   : byte -> lebStream
  enc_signed_word32 : word32 -> lebStream
  enc_signed_word64 : word64 -> lebStream
*)

(*----------------------------------------------------------------------------*
   Decoding and encoding natrual numbers from / to LEB128
 *----------------------------------------------------------------------------*)

Definition dec_num_def:
  dec_num ([]:word8 list) : (num # word8 list) option = NONE ∧
  dec_num (b::rest) =
    let bn = w2n b in
    if word_msb b then
      case dec_num rest of
      | SOME (n, left_over) => SOME (n * 128 + bn MOD 128, left_over)
      | NONE => NONE
    else SOME (bn, rest)
End

Definition enc_num_def:
  enc_num (n:num) =
    if n < 128 then [(n2w n):word8]
    else n2w (n MOD 128) + 128w :: enc_num (n DIV 128)
End

Theorem dec_enc_num_id:
  ∀n rest. dec_num (enc_num n ++ rest) = SOME (n,rest)
Proof
  ho_match_mp_tac enc_num_ind \\ rw []
  \\ simp [Once enc_num_def] \\ rw []
  >-
   (simp [Once dec_num_def]
    \\ ‘n DIV 128 = 0’ by gvs [DIV_EQ_X]
    \\ simp [word_msb_n2w,bitTheory.BIT_DEF])
  \\ simp [Once dec_num_def,word_add_n2w]
  \\ simp [word_msb_n2w,bitTheory.BIT_DEF]
  \\ ‘0 < 128:num’ by fs []
  \\ drule ADD_DIV_ADD_DIV
  \\ disch_then $ qspecl_then [‘1’] assume_tac
  \\ gvs []
  \\ ‘(n MOD 128 + 128) < 256’ by
   (‘n MOD 128 < 128’ by simp [MOD_LESS]
    \\ decide_tac)
  \\ simp [LESS_MOD]
  \\ ‘0 < 128:num’ by fs []
  \\ drule DIVISION
  \\ disch_then (fn th => CONV_TAC (RAND_CONV $ ONCE_REWRITE_CONV [th]))
  \\ gvs []
QED

(*----------------------------------------------------------------------------*
   Decoding and encoding unsigned words from / to LEB128
 *----------------------------------------------------------------------------*)

Definition dec_unsigned_word_def:
  dec_unsigned_word input =
  case dec_num input of
  | SOME (n,rest) => if n < dimword(:α) then SOME ((n2w n):α word, rest) else NONE
  | NONE => NONE
End

Definition enc_unsigned_word_def:
  enc_unsigned_word (x:'a word) = enc_num (w2n x)
End

Theorem dec_enc_unsigned_word:
  ∀w rest. dec_unsigned_word (enc_unsigned_word w ++ rest) = SOME (w,rest)
Proof
  fs [dec_unsigned_word_def,enc_unsigned_word_def,dec_enc_num_id,w2n_lt]
QED

(*----------------------------------------------------------------------------*
   Decoding and encoding signed words from / to LEB128
 *----------------------------------------------------------------------------*)

Definition dec_w7s_def:
  dec_w7s ([]:word8 list) = NONE ∧
  dec_w7s (b::bs) =
    if word_msb b then
      (case dec_w7s bs of
       | NONE => NONE
       | SOME (xs,rest) => SOME (((w2w b):7 word) :: xs, rest))
    else
      SOME ([((w2w b):7 word)], bs)
End

Definition enc_w7s_def:
  enc_w7s [] = ([]:word8 list) ∧
  enc_w7s ((b:7 word)::bs) =
    if NULL bs then [w2w b] else (w2w b || 128w) :: enc_w7s bs
End

Theorem dec_enc_w7s:
  ∀xs rest. xs ≠ [] ⇒ dec_w7s (enc_w7s xs ++ rest) = SOME (xs,rest)
Proof
  Induct \\ simp [] \\ rw []
  \\ simp [enc_w7s_def]
  \\ Cases_on ‘xs’ \\ fs []
  >-
   (simp [dec_w7s_def]
    \\ gvs [word_msb_def]
    \\ DEP_REWRITE_TAC [wordsTheory.w2w]
    \\ simp [w2w_w2w]
    \\ blastLib.BBLAST_TAC)
  \\ fs [dec_w7s_def]
  \\ rw []
  >- blastLib.BBLAST_TAC
  \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC
QED

Definition or_w7s_def:
  or_w7s [] = 0w ∧
  or_w7s [b] = sw2sw b ∧
  or_w7s ((b:7 word)::bs) = or_w7s bs << 7 || w2w b
End

Definition dec_signed_def:
  dec_signed input =
    case dec_w7s input of
    | NONE => NONE
    | SOME (xs,rest) => SOME ((or_w7s xs) :'a word, rest)
End

Definition enc_signed_word8_def:
  enc_signed_word8 (w:word8) =
    if sw2sw ((w2w w):7 word) = w then
      enc_w7s [w2w w]
    else
      let w14 = (sw2sw w) :14 word in
        enc_w7s [w2w w14; w2w (w14 >>> 7)]
End

Theorem dec_enc_signed_word8:
  ∀b xs rest. dec_signed (enc_signed_word8 b ++ rest) = SOME (b,rest)
Proof
  rw [enc_signed_word8_def,dec_signed_def]
  \\ simp [dec_enc_w7s,or_w7s_def]
  \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC
QED

Definition enc_signed_word32_def:
  enc_signed_word32 (w:word32) =
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

Theorem dec_enc_signed_word32:
  ∀b xs rest. dec_signed (enc_signed_word32 b ++ rest) = SOME (b,rest)
Proof
  rw [enc_signed_word32_def,dec_signed_def]
  \\ simp [dec_enc_w7s,or_w7s_def]
  \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC
QED

Definition enc_signed_word64_def:
  enc_signed_word64 (w:word64) =
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
    else if sw2sw ((w2w w):35 word) = w then
      let w = (sw2sw w) :35 word in
        enc_w7s [w2w w;
                 w2w (w >>> 7);
                 w2w (w >>> 14);
                 w2w (w >>> 21);
                 w2w (w >>> 28)]
    else
      let w = (sw2sw w) :70 word in
        enc_w7s [w2w w;
                 w2w (w >>> 7);
                 w2w (w >>> 14);
                 w2w (w >>> 21);
                 w2w (w >>> 28);
                 w2w (w >>> 35);
                 w2w (w >>> 42);
                 w2w (w >>> 49);
                 w2w (w >>> 56);
                 w2w (w >>> 63)]
End

Theorem dec_enc_signed_word64:
  ∀b xs rest. dec_signed (enc_signed_word64 b ++ rest) = SOME (b,rest)
Proof
  rw [enc_signed_word64_def,dec_signed_def]
  \\ simp [dec_enc_w7s,or_w7s_def]
  \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC
QED

(*----------------------------------------------------------------------------*
   Some tests
 *----------------------------------------------------------------------------*)

Triviality tests:
  enc_num 5   = [0x05w] ∧
  enc_num 127 = [0x7Fw] ∧
  enc_num 128 = [0x80w; 0x01w] ∧
  enc_unsigned_word (0x7Fw:word32) = [0x7Fw] ∧
  enc_signed_word32 (0x7Fw:word32) = [0xFFw; 0x00w] ∧
  enc_signed_word8  (0x7Fw:word8)  = [0xFFw; 0x00w] ∧
  enc_signed_word8  (0x80w:word8)  = [0x80w; 0x7Fw] ∧
  enc_signed_word8  (0xFFw:word8)  = [0x7Fw]
Proof
  EVAL_TAC
QED

