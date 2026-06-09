(*
  Module about the built-in word8 type.
*)
Theory Word8Prog
Ancestors
  Word64Prog ml_translator
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "Word64Prog";

(* Word8 module -- translated *)

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «byte» (Atapp [] (Short «word8»))`` I);

val _ = ml_prog_update (open_module "Word8");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «word» (Atapp [] (Short «word8»))`` I);

(* to/from int/char *)
val _ = trans "fromInt" ``n2w:num->word8``;
val _ = trans "fromChar" “mlstring$char_to_word8”;
val _ = trans "toInt" ``w2n:word8->num``;
val _ = trans "toIntSigned" ``w2i:word8->int``;

(* bitwise operations *)
val _ = trans "andb" ``word_and:word8->word8->word8``;
val _ = trans "orb" ``word_or:word8->word8->word8``;
val _ = trans "xorb" ``word_xor:word8->word8->word8``;

Theorem word_1comp_eq[local]:
    word_1comp w = word_xor w 0xFFw:word8
Proof
  fs []
QED

val _ = (next_ml_names := ["notb"]);
val _ = translate word_1comp_eq

(* arithmetic *)
val _ = trans "+" ``word_add:word8->word8->word8``;
val _ = trans "-" ``word_sub:word8->word8->word8``;
val _ = trans "=" ``(=):word8->word8->bool``;
val _ = trans "<" ``word_lo:word8->word8->bool``;
val _ = trans ">" ``word_hi:word8->word8->bool``;
val _ = trans "<=" ``word_ls:word8->word8->bool``;
val _ = trans ">=" ``word_hs:word8->word8->bool``;

(* shifts *)

Definition var_word_lsl_def:
  var_word_lsl (w:word8) (n:num) =
    if n < 8 then
    if n < 4 then
      if n < 2 then if n < 1 then w else w << 1
      else if n < 3 then w << 2
      else w << 3
    else if n < 6 then if n < 5 then w << 4 else w << 5
    else if n < 7 then w << 6
    else w << 7 else 0w
End

Theorem var_word_lsl_thm[simp]:
   var_word_lsl w n = word_lsl w n
Proof
  ntac 32 (
    Cases_on `n` \\ fs [ADD1] THEN1 (EVAL_TAC \\ fs [LSL_ADD])
    \\ Cases_on `n'` \\ fs [ADD1] THEN1 (EVAL_TAC \\ fs [LSL_ADD]))
  \\ ntac 9 (once_rewrite_tac [var_word_lsl_def] \\ fs [])
QED

Definition var_word_lsr_def:
  var_word_lsr (w:word8) (n:num) =
    if n < 8 then
    if n < 4 then
      if n < 2 then if n < 1 then w else w >>> 1
      else if n < 3 then w >>> 2
      else w >>> 3
    else if n < 6 then if n < 5 then w >>> 4 else w >>> 5
    else if n < 7 then w >>> 6
    else w >>> 7 else 0w
End

Theorem var_word_lsr_thm[simp]:
   var_word_lsr w n = word_lsr w n
Proof
  ntac 32 (
    Cases_on `n` \\ fs [ADD1] THEN1 (EVAL_TAC \\ fs [LSR_ADD])
    \\ Cases_on `n'` \\ fs [ADD1] THEN1 (EVAL_TAC \\ fs [LSR_ADD]))
  \\ ntac 9 (once_rewrite_tac [var_word_lsr_def] \\ fs [])
QED

Definition var_word_asr_def:
  var_word_asr (w:word8) (n:num) =
    if n < 8 then
    if n < 4 then
      if n < 2 then if n < 1 then w else w >> 1
      else if n < 3 then w >> 2
      else w >> 3
    else if n < 6 then if n < 5 then w >> 4 else w >> 5
    else if n < 7 then w >> 6
    else w >> 7 else w >> 8
End

Theorem var_word_asr_thm[simp]:
   var_word_asr w n = word_asr w n
Proof
  ntac 32 (
    Cases_on `n` \\ fs [ADD1] THEN1 (rw [] \\ EVAL_TAC \\ fs [ASR_ADD])
    \\ Cases_on `n'` \\ fs [ADD1] THEN1 (rw [] \\ EVAL_TAC \\ fs [ASR_ADD]))
  \\ ntac 9 (once_rewrite_tac [var_word_asr_def] \\ fs [])
QED

Theorem word_ror_eq_word_shifts:
  ∀(w:'a word) n.
    word_ror w n =
    word_or (word_lsl w (dimindex (:'a) - (n MOD (dimindex (:'a)))))
            (word_lsr w (n MOD (dimindex (:'a))))
Proof
  rw [fcpTheory.CART_EQ,word_ror_def,word_or_def,word_lsl_def,
      word_lsr_def,fcpTheory.FCP_BETA]
  \\ ‘0 < dimindex (:α)’ by fs []
  \\ once_rewrite_tac[GSYM MOD_PLUS]
  \\ qabbrev_tac ‘k = n MOD dimindex (:α)’ \\ simp []
  \\ Cases_on ‘i + k < dimindex (:'a)’ \\ simp []
  \\ gvs [NOT_LESS]
  \\ ‘k < dimindex (:α)’ by fs[Abbr`k`]
  \\ AP_TERM_TAC
  \\ gvs [LESS_EQ_EXISTS]
QED

Definition var_word_ror_def:
  var_word_ror (w:word8) n =
    word_or (var_word_lsl w (8 - (n MOD 8)))
            (var_word_lsr w (n MOD 8))
End

Theorem var_word_ror_thm[simp]:
  var_word_ror w n = word_ror w n
Proof
  simp [var_word_ror_def,word_ror_eq_word_shifts]
QED

val _ = (next_ml_names := ["<<"]);
val _ = translate var_word_lsl_def;

val _ = (next_ml_names := [">>"]);
val _ = translate var_word_lsr_def;

val _ = (next_ml_names := ["~>>"]);
val _ = translate var_word_asr_def;

val _ = (next_ml_names := ["ror"]);
val _ = translate var_word_ror_def;

Theorem var_word_ror_side[local]:
  ∀w n. var_word_ror_side w n = T
Proof
  rw [fetch "-" "var_word_ror_side_def"]
  \\ irule LESS_IMP_LESS_OR_EQ \\ fs []
QED

val _ = update_precondition var_word_ror_side;

val sigs = module_signatures ["fromInt", "toInt", "andb",
  "orb", "xorb", "notb", "+", "-", "<<", ">>", "~>>", "ror"];

val _ = ml_prog_update (close_module (SOME sigs));

(* if any more theorems get added here, probably should create Word8ProofTheory *)

Theorem WORD_UNICITY_R[xlet_auto_match]:
 !f fv fv'. WORD (f :word8) fv ==> (WORD f fv' <=> fv' = fv)
Proof
fs[WORD_def]
QED

Theorem WORD_UNICITY_L[xlet_auto_match]:
 !f f' fv. WORD (f :word8) fv ==> (WORD f' fv <=> f = f')
Proof
fs[WORD_def]
QED

Theorem n2w_UNICITY[xlet_auto_match]:
  !n1 n2.n1 <= 255 ==> ((n2w n1 :word8 = n2w n2 /\ n2 <= 255) <=> n1 = n2)
Proof
 rw[] >> eq_tac >> fs[]
QED

Theorem WORD_n2w_UNICITY_L[xlet_auto_match]:
  !n1 n2 f. n1 <= 255 /\ WORD (n2w n1 :word8) f ==>
   (WORD (n2w n2 :word8) f /\ n2 <= 255 <=> n1 = n2)
Proof
 rw[] >> eq_tac >> rw[] >> imp_res_tac WORD_UNICITY_L >>
`n1 MOD 256 = n1` by fs[] >> `n2 MOD 256 = n2` by fs[] >> fs[]
QED

Overload WORD8 = ``WORD:word8 -> v -> bool``
