(*
  Translate md5 function
*)
open preamble basis md5Theory;

val _ = new_theory "md5Prog"

val _ = translation_extends "basisProg";

(* translate md5Theory *)

val res = translate w64_zero_def;
val res = translate packLittle_def;
val res = translate PADDING_def;
val res = translate init_def;
val res = translate DROP_def;
val res = translate subVec_def;

Triviality word_not_thm:
  ¬w = word_xor w (0xFFFFFFFFw:word32)
Proof
  fs []
QED

val res = translate word_not_thm;
val res = translate F'_def;
val res = translate G'_def;
val res = translate H'_def;
val res = translate I'_def;
val res = translate (transform_def |> SIMP_RULE std_ss [XX_def,ROTATE_LEFT_def]);

val res = translate genlist_rev_def;
val res = translate oEL_def;
val res = translate extract_def;
val res = translate take_rev_def;
val res = translate loop_def;

val mul8add_simp = mul8add_def |> Q.SPECL [‘w’,‘1’]
  |> SIMP_RULE std_ss [LET_THM,WORD_MUL_LSL,word_mul_n2w,
       EVAL “(1w ⋙ 29):word32”, WORD_ADD_0,WORD_LO,w2n_n2w,
       EVAL “dimword (:32)”];

val mul8add_thm = mul8add_def
  |> SIMP_RULE std_ss [LET_THM,WORD_MUL_LSL,word_mul_n2w,
       WORD_ADD_0,WORD_LO,w2n_n2w,EVAL “dimword (:32)”];

val res = translate (update1_def |> REWRITE_RULE [mul8add_simp]);

val res = translate mul8add_thm;
val res = translate genlist_rev_def;
val res = translate update_def;
val res = translate final_def;
val res = translate hxd_def;
val res = translate EL;

Theorem el_side_thm:
  ∀n xs. el_side n xs ⇔ n < LENGTH xs
Proof
  Induct
  \\ once_rewrite_tac [fetch "-" "el_side_def"]
  \\ rw [] \\ Cases_on ‘xs’ \\ fs []
QED

val _ = update_precondition el_side_thm;

val res = translate byte2hex_def;

Theorem byte2hex_side_thm:
  ∀n acc. byte2hex_side n acc = T
Proof
  fs [fetch "-" "byte2hex_side_def", EVAL “LENGTH hxd”] \\ fs [DIV_LT_X]
  \\ assume_tac (wordsTheory.w2n_lt |> INST_TYPE [“:'a” |-> “:8”])
  \\ fs []
QED

val _ = update_precondition byte2hex_side_thm;

val res = translate toHexString_def;
val res = translate (md5_def |> SIMP_RULE std_ss [o_DEF]);

val _ = export_theory();
