(*
  Module about the built-in word64 type.
*)
Theory Word64Prog
Ancestors
  CharProg
Libs
  preamble ml_translatorLib ml_progLib basisFunctionsLib

val _ = translation_extends "CharProg";

(* Word64 module -- translated *)

val _ = ml_prog_update (open_module "Word64");

val () = generate_sigs := true;

val _ = ml_prog_update (add_dec
  ``Dtabbrev unknown_loc [] «word» (Atapp [] (Short «word64»))`` I);

(* to/from int *)
val _ = trans "fromInt" ``n2w:num->word64``;
val _ = trans "toInt" ``w2n:word64->num``;
val _ = trans "toIntSigned" ``w2i:word64->int``;

(* bitwise operations *)
val _ = trans "andb" ``word_and:word64->word64->word64``;;
val _ = trans "orb" ``word_or:word64->word64->word64``;
val _ = trans "xorb" ``word_xor:word64->word64->word64``;

Theorem word_1comp_eq[local]:
    word_1comp w = word_xor w 0xFFFFFFFFFFFFFFFFw:word64
Proof
  fs []
QED

val _ = (next_ml_names := ["notb"]);
val _ = translate word_1comp_eq

(* arithmetic *)
val _ = trans "+" ``word_add:word64->word64->word64``;
val _ = trans "-" ``word_sub:word64->word64->word64``;
val _ = trans "=" ``(=):word64->word64->bool``;
val _ = trans "<" ``word_lo:word64->word64->bool``;
val _ = trans ">" ``word_hi:word64->word64->bool``;
val _ = trans "<=" ``word_ls:word64->word64->bool``;
val _ = trans ">=" ``word_hs:word64->word64->bool``;

(* shifts *)

Definition var_word_lsl_def:
  var_word_lsl (w:word64) (n:num) = if 64 < n then 0w
    else if n < 8 then
    if n < 4 then
      if n < 2 then if n < 1 then w else w << 1
      else if n < 3 then w << 2
      else w << 3
    else if n < 6 then if n < 5 then w << 4 else w << 5
    else if n < 7 then w << 6
    else w << 7 else var_word_lsl (w << 8) (n − 8)
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
  var_word_lsr (w:word64) (n:num) = if 64 < n then 0w
    else if n < 8 then
    if n < 4 then
      if n < 2 then if n < 1 then w else w >>> 1
      else if n < 3 then w >>> 2
      else w >>> 3
    else if n < 6 then if n < 5 then w >>> 4 else w >>> 5
    else if n < 7 then w >>> 6
    else w >>> 7 else var_word_lsr (w >>> 8) (n − 8)
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
  var_word_asr (w:word64) (n:num) = if 64 < n then w >> 64
    else if n < 8 then
    if n < 4 then
      if n < 2 then if n < 1 then w else w >> 1
      else if n < 3 then w >> 2
      else w >> 3
    else if n < 6 then if n < 5 then w >> 4 else w >> 5
    else if n < 7 then w >> 6
    else w >> 7 else var_word_asr (w >> 8) (n − 8)
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
  \\ drule MOD_PLUS
  \\ disch_then $ once_rewrite_tac o single o GSYM
  \\ qabbrev_tac ‘k = n MOD dimindex (:α)’ \\ simp []
  \\ Cases_on ‘i + k < dimindex (:'a)’ \\ simp []
  \\ gvs [NOT_LESS]
  \\ ‘k < dimindex (:α)’ by fs[Abbr`k`]
  \\ AP_TERM_TAC
  \\ gvs [LESS_EQ_EXISTS]
QED

Definition var_word_ror_def:
  var_word_ror (w:word64) n =
    word_or (var_word_lsl w (64 - (n MOD 64)))
            (var_word_lsr w (n MOD 64))
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

Definition concat_all_def:
  concat_all (a:word8) b c d e f g h =
    concat_word_list [a;b;c;d;e;f;g;h]:64 word
End

val concat_all_impl =
  REWRITE_RULE [concat_word_list_def, dimindex_8, ZERO_SHIFT, WORD_OR_CLAUSES] concat_all_def;

val _ = (next_ml_names := ["concatAll"]);
val _ = translate concat_all_impl;

val sigs = module_signatures ["fromInt", "toInt", "andb",
  "orb", "xorb", "notb", "+", "-", "<<", ">>", "~>>", "concatAll"];

val _ = ml_prog_update (close_module (SOME sigs));
