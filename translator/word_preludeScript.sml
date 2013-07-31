open HolKernel Parse boolLib bossLib; val _ = new_theory "word_prelude";

open arithmeticTheory listTheory wordsTheory wordsLib;
open ml_translatorLib ml_translatorTheory std_preludeTheory;

val _ = translation_extends "std_prelude";


(* bit *)

val res = translate bitTheory.MOD_2EXP_def;
val res = translate bitTheory.DIV_2EXP_def;
val res = translate DIV2_def;

val res = translate bitTheory.BITS_THM2;
val res = translate (SIMP_RULE std_ss [bitTheory.BITS_THM,DECIDE ``SUC n - n = 1``] bitTheory.BIT_def);
val res = translate bitTheory.SBIT_def;

(* words *)

(* perhaps should look at integer_wordTheory too? *)

val WORD_def = Define `WORD w = NUM (w2n w)`;

val EqualityType_WORD = prove(
  ``EqualityType WORD``,
  EVAL_TAC THEN SRW_TAC [] [] THEN EVAL_TAC)
  |> store_eq_thm;

val  res = translate (bitTheory.BITWISE_def)

val  res = translate (bitTheory.BIT_MODIFY_def)

val WORD_LSR_LEMMA = prove(
  ``!w n. (w >>> n) = n2w (w2n w DIV 2**n)``,
  Cases THEN SIMP_TAC std_ss [GSYM w2n_11,w2n_lsr,w2n_n2w,n2w_w2n]
  THEN REPEAT STRIP_TAC
  THEN `n MOD dimword (:'a) DIV 2 ** n' < dimword (:'a)` by ALL_TAC
  THEN FULL_SIMP_TAC std_ss [DIV_LT_X]
  THEN Cases_on `(2:num) ** n'`
  THEN FULL_SIMP_TAC std_ss [ADD1] THEN DECIDE_TAC);

val word_msb_thm = prove(
  ``!w. word_msb (w:'a word) = BIT (dimindex (:'a) - 1) (w2n w)``,
  Cases THEN FULL_SIMP_TAC std_ss [word_msb_n2w,w2n_n2w]);

val word_lsb_thm = prove(
  ``!w. word_lsb (w:'a word) = ~(w2n w MOD 2 = 0)``,
  Cases THEN FULL_SIMP_TAC std_ss [word_lsb_n2w,w2n_n2w,ODD_EVEN,EVEN_MOD2]);

val sub_lemma = SIMP_RULE std_ss [word_2comp_def] word_sub_def

val word_1comp_thm = prove(
  ``!w. word_1comp (w:'a word) = n2w (dimword (:'a) - 1 - (w2n w) MOD dimword (:'a))``,
  STRIP_TAC THEN
  CONV_TAC(LAND_CONV(RAND_CONV(SIMP_CONV std_ss [Once (GSYM n2w_w2n)]))) THEN
  SIMP_TAC std_ss [word_1comp_n2w])

fun translate_word n = let
  val fcp_n = Type[QUOTE (":"^(Int.toString n))]
  val word_n = mk_type("cart",[``:bool``,fcp_n])
  val n_tm = numSyntax.term_of_int n

  val _ = add_type_inv (inst [alpha|->fcp_n] ``WORD``) ``:num``

  val w2n_tm = inst[alpha|->fcp_n]``w2n``
  val Eval_w2n_wordn = prove(
    ``!v. ((NUM --> NUM) (\x.x)) v ==> ((WORD --> NUM) (^w2n_tm)) v``,
  SIMP_TAC std_ss [Arrow_def,AppReturns_def,WORD_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\x.x:num``))
  |> store_eval_thm;

  val n2w_tm = inst[alpha|->fcp_n]``n2w``
  val exp2n = rhs(concl(EVAL(numSyntax.mk_exp(numSyntax.term_of_int 2,n_tm))))
  val Eval_n2w_wordn = prove(
    ``!v. ((NUM --> NUM) (\x.x MOD ^exp2n)) v ==> ((NUM --> WORD) ^n2w_tm) v``,
    SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,WORD_def,w2n_n2w])
    |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\x.x MOD ^exp2n``))
    |> store_eval_thm;

  val res = translate (word_add_def |> INST_TYPE [alpha|->fcp_n]);
  val res = translate (word_mul_def |> INST_TYPE [alpha|->fcp_n]);

  val v_n = mk_var("v",word_n)

  val word_xor_lemma = prove(
    ``!w ^v_n. (w ?? v) = n2w (BITWISE ^n_tm (\x y. x <> y) (w2n w) (w2n v))``,
    REPEAT Cases THEN FULL_SIMP_TAC (srw_ss()) [word_xor_n2w]);

  val res = translate word_xor_lemma

  val word_or_lemma = prove(
    ``!w ^v_n. (w !! v) = n2w (BITWISE ^n_tm (\x y. x \/ y) (w2n w) (w2n v))``,
    REPEAT Cases THEN FULL_SIMP_TAC (srw_ss()) [word_or_n2w]
    THEN `(\x y. x \/ y) = $\/` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    THEN FULL_SIMP_TAC std_ss []);

  val res = translate word_or_lemma

  val word_and_lemma = prove(
    ``!w ^v_n. (w && v) = n2w (BITWISE ^n_tm (\x y. x /\ y) (w2n w) (w2n v))``,
    REPEAT Cases THEN FULL_SIMP_TAC (srw_ss()) [word_and_n2w]
    THEN `(\x y. x /\ y) = (/\)` by FULL_SIMP_TAC std_ss [FUN_EQ_THM]
    THEN FULL_SIMP_TAC std_ss []);

  val res = translate word_and_lemma

  val res = translate (WORD_MUL_LSL |> INST_TYPE [alpha|->fcp_n])

  val res = translate (WORD_LSR_LEMMA |> INST_TYPE [alpha|->fcp_n])

  fun f_n lemma =
    lemma |> INST_TYPE [alpha|->fcp_n] |> SIMP_RULE (srw_ss()) []

  fun ff_n lemma =
    lemma |> INST_TYPE [alpha|->fcp_n] |> SIMP_RULE (std_ss++SIZES_ss) []

  val res = translate (f_n word_msb_thm);
  val res = translate (f_n word_lsb_thm);
  val res = translate (f_n word_asr_n2w);
  val res = translate (ff_n sub_lemma);

  val lemma = prove(
    ``(h--l) ^v_n = n2w (BITS (MIN h ^(numSyntax.term_of_int(n-1))) l (w2n v))``,
    `(h--l) v = (h--l) (n2w (w2n v))` by METIS_TAC [n2w_w2n]
    THEN SRW_TAC [] [word_bits_n2w]);

  val res = translate lemma;
  val res = translate (ff_n wordsTheory.word_ror)
  val res = translate (ff_n wordsTheory.word_rol_def)

  val res = translate (ff_n word_1comp_thm)
in () end

val _ = app translate_word [4,8,16,32,64]

val _ = export_theory();
