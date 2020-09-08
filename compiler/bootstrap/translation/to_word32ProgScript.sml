(*
  Translate the data_to_word part of the 32-bit compiler.
*)

open preamble ml_translatorLib ml_translatorTheory
     sexp_parserProgTheory std_preludeTheory
local open backendTheory in end

val _ = temp_delsimps ["NORMEQ_CONV"]

val _ = new_theory "to_word32Prog"

val _ = translation_extends "sexp_parserProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_word32Prog");
val _ = ml_translatorLib.use_string_type true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);

fun def_of_const tm = let
  val res = dest_thy_const tm handle HOL_ERR _ =>
              failwith ("Unable to translate: " ^ term_to_string tm)
  val name = (#Name res)
  fun def_from_thy thy name =
    DB.fetch thy (name ^ "_pmatch") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_def") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_DEF") handle HOL_ERR _ =>
    DB.fetch thy (name ^ "_thm") handle HOL_ERR _ =>
    DB.fetch thy name
  val def = def_from_thy (#Thy res) name handle HOL_ERR _ =>
            failwith ("Unable to find definition of " ^ name)

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:32``,beta|->``:32``] else []

  val def = def |> RW (!extra_preprocessing)
                |> INST_TYPE insts
                |> CONV_RULE (DEPTH_CONV BETA_CONV)
                (* TODO: This ss messes up defs containing if-then-else
                with constant branches
                |> SIMP_RULE bool_ss [IN_INSERT,NOT_IN_EMPTY]*)
                |> REWRITE_RULE [NOT_NIL_AND_LEMMA]
  in def end

val _ = (find_def_for_const := def_of_const);

val _ = use_long_names:=true;

val spec32 = INST_TYPE[alpha|->``:32``]

val conv32 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val conv32_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec32 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

open data_to_wordTheory

val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

val wcomp_simp = SIMP_RULE std_ss [word_2comp_def]

val _ = translate stack_to_labTheory.is_gen_gc_def

val _ = translate adjust_set_def

val _ = translate (make_header_def |> SIMP_RULE std_ss [word_lsl_n2w]|> conv32_RHS)

val _ = translate (shift_left_def |> conv32)
val _ = translate (shift_right_def |> spec32 |> CONV_RULE fcpLib.INDEX_CONV)

val i2w_eq_n2w_lemma = prove(
  ``i2w (& (k * n)) = n2w (k * n)``,
  fs [integer_wordTheory.i2w_def]);

val lemma2 = prove(
  ``4 * x < (2**32) <=> x < (2**32) DIV 4``,
  fs []) |> SIMP_RULE std_ss []

val _ = translate (get_gen_size_def |> spec32
    |> SIMP_RULE (srw_ss()) [dimword_def,bytes_in_word_def,word_mul_n2w]
    |> REWRITE_RULE [GSYM i2w_eq_n2w_lemma,lemma2]);

val _ = translate (tag_mask_def |> conv32_RHS |> we_simp |> conv32_RHS |> SIMP_RULE std_ss [shift_left_rwt] |> SIMP_RULE std_ss [Once (GSYM shift_left_rwt),word_2comp_def] |> conv32)

val _ = translate (encode_header_def |> conv32_RHS)

(* Manual inlines : shift_def, bytes_in_word because of 'a arg *)
val inline_simp =
    SIMP_RULE std_ss [backend_commonTheory.word_shift_def,bytes_in_word_def];

val _ = register_type ``:32 wordLang$prog``;

(* check 32 prog is known to be an EqualityType *)
val EqualityType_prog = EqualityType_rule [] ``:32 wordLang$prog``;

val _ = translate (StoreEach_def |> inline_simp |> conv32);

val _ = translate (all_ones_def |> conv32_RHS |> we_simp |> SIMP_RULE std_ss [shift_left_rwt,shift_right_rwt] |> wcomp_simp |> conv32 |> wcomp_simp |> conv32)

val _ = translate (maxout_bits_def |> SIMP_RULE std_ss [word_lsl_n2w] |> conv32)

val _ = translate (ptr_bits_def  |> conv32)

val _ = translate (real_addr_def |> inline_simp |> conv32_RHS |> SIMP_RULE std_ss [LET_THM])

val _ = translate (real_offset_def |> inline_simp |> conv32)
val _ = translate (real_byte_offset_def |> inline_simp |> conv32)
val _ = translate (GiveUp_def |> wcomp_simp |> conv32)

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``]

val assign_rw = Q.prove(`
  (i < 0 ⇒ n2w (Num (4 * (0 -i))) = n2w (Num (ABS (4*(0-i))))) ∧
  (¬(i < 0) ⇒ n2w (Num (4 * i)) = n2w (Num (ABS (4*i))))`,
  rw[]
  >-
    (`0 ≤ 4* -i` by intLib.COOPER_TAC>>
    metis_tac[integerTheory.INT_ABS_EQ_ID])
  >>
    `0 ≤ 4*i` by intLib.COOPER_TAC>>
    metis_tac[integerTheory.INT_ABS_EQ_ID])

(* TODO: word_mul should maybe target a real op ?
   TODO: econv might be going too far with case simplification
*)

val _ = translate (WriteWord32_on_32_def |> inline_simp |> conv32)
val _ = translate (WriteWord64_on_32_def |> inline_simp |> conv32)
val _ = translate (WordOp64_on_32_def |> inline_simp |> SIMP_RULE std_ss [word_mul_def,word_2comp_def]|> conv32)

val _ = translate (ShiftVar_def |> inline_simp |> conv32);
val _ = translate (WordShift64_on_32_def |> inline_simp |> conv32)
val _ = translate (LoadBignum_def |> inline_simp |> conv32)

val Smallnum_alt = prove(
  ``Smallnum i =
    if i < 0 then 0w − n2w (Num (ABS (4 * (0 − i))))
             else n2w (Num (ABS (4 * i)))``,
  fs [Smallnum_def] \\ Cases_on `i` \\ fs [integerTheory.INT_ABS_NUM]);

val _ = translate (Smallnum_alt |> inline_simp |> conv32)
val _ = translate (MemEqList_def |> inline_simp |> conv32)

val _ = save_thm("n2mw_ind",multiwordTheory.n2mw_ind |> inline_simp |> conv32);
val _ = translate (multiwordTheory.n2mw_def |> inline_simp |> conv32);
val _ = translate (multiwordTheory.i2mw_def |> inline_simp |> conv32);
val _ = translate (bignum_words_def |> inline_simp |> conv32);
val _ = translate (BignumHalt_def |> inline_simp |> conv32);
val _ = translate(Maxout_bits_code_def |> conv32);
val _ = translate(Make_ptr_bits_code_def |> inline_simp |> conv32);
val _ = translate(SilentFFI_def |> inline_simp |> wcomp_simp |> conv32);
val _ = translate(AllocVar_def |> inline_simp |> wcomp_simp |> conv32);

val _ = translate arg1_def;
val _ = translate arg2_pmatch;
val _ = translate arg3_pmatch;
val _ = translate arg4_pmatch;

fun tweak_assign_def th =
  th |> SIMP_RULE std_ss [assign_rw]
     |> inline_simp |> conv32 |> we_simp
     |> SIMP_RULE std_ss [SHIFT_ZERO,shift_left_rwt]
     |> SIMP_RULE std_ss [word_mul_def,LET_THM] |> gconv;

val res = all_assign_defs |> CONJUNCTS |> map tweak_assign_def |> map translate;
val res = translate (assign_def |> tweak_assign_def);

val lemma = Q.prove(`!A B. A = B ==> B ≠ A ==> F`,metis_tac[])

(*
val data_to_word_assign_side = Q.prove(`
  ∀a b c d e f g. data_to_word_assign_side a b c d e f g ⇔ T`,
  rpt strip_tac>>
  simp[fetch "-" "data_to_word_assign_side_def",NULL]>>
  Cases_on`e`>>fs[]>>
  Cases_on`f`>>fs[]>>
  TRY(Cases_on`t`)>>TRY(Cases_on`t'`)>>
  TRY(Cases_on`w`)>>fs[]>>
  TRY(Cases_on`(encode_header a 3 1):word32 option`)>>
  TRY(Cases_on`o'`)>>
  TRY(Cases_on`s`)>>
  metis_tac[word_op_type_nchotomy,option_nchotomy,NOT_NONE_SOME,list_distinct]) |> update_precondition
*)

val _ = save_thm ("comp_ind",data_to_wordTheory.comp_ind|> conv32|> wcomp_simp)
(* Inlines the let k = 8 manually *)
val _ = translate (comp_def |> conv32 |> wcomp_simp |> conv32 |> SIMP_RULE std_ss[LET_THM |> INST_TYPE [alpha|->``:num``]]);

open word_simpTheory word_allocTheory word_instTheory

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``]

val _ = translate (const_fp_inst_cs_def |> spec32 |> econv)

val rws = Q.prove(`
  ($+ = λx y. x + y) ∧
  ($&& = λx y. x && y) ∧
  ($|| = λx y. x || y) ∧
  ($?? = λx y. x ?? y)`,
  fs[FUN_EQ_THM])

val _ = translate (wordLangTheory.word_op_def |> ONCE_REWRITE_RULE [rws,WORD_NOT_0] |> spec32 |> gconv)

val word_msb_rw = Q.prove(
  `word_msb (a:word32) ⇔ (a>>>31) <> 0w`,
  rw[word_msb_def,fcpTheory.CART_EQ,word_index,word_lsr_def,fcpTheory.FCP_BETA]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  \\ `i = 0` by decide_tac \\ fs[]);

val arith_shift_right_ind_orig = arith_shift_right_ind;

val arith_shift_right_ind = (
  arith_shift_right_ind_orig |> spec32
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE (QUANT_CONV(LAND_CONV fcpLib.INDEX_CONV)) |> gconv)
  |> curry save_thm "arith_shift_right_ind";

val _ = translate (
  arith_shift_right_def |> spec32
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE fcpLib.INDEX_CONV |> gconv);

val res = translate (wordLangTheory.word_sh_def
  |> INST_TYPE [``:'a``|->``:32``]
  |> RW[shift_left_rwt,shift_right_rwt,arith_shift_right_rwt] |> conv32 |> we_simp |> SIMP_RULE (srw_ss()++ARITH_ss) [SHIFT_ZERO,MOD_LESS] |> gconv
  |> RW[shift_left_rwt,shift_right_rwt,arith_shift_right_rwt]  );

val _ = translate (asmTheory.word_cmp_def |> REWRITE_RULE[WORD_LO,WORD_LT] |> spec32 |> REWRITE_RULE[word_msb_rw]);

(* TODO: remove when pmatch is fixed *)
val _ = translate (spec32 const_fp_loop_def)

val _ = translate (spec32 compile_exp_def)

val _ = translate (wordLangTheory.max_var_inst_def |> conv32)
val _ = translate (spec32 wordLangTheory.max_var_def)

val _ = translate (conv32_RHS integer_wordTheory.WORD_LEi)

val _ = translate (asmTheory.offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv32)
val res = translate_no_ind (inst_select_exp_pmatch |> conv32 |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv32)

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ rveq
  THEN1
   (last_x_assum (match_mp_tac o MP_CANON)
    \\ fs [] \\ rveq \\ fs [])
  THEN1
   (Cases_on `exp` \\ fs []
    \\ Cases_on `b` \\ fs []
    \\ Cases_on `l` \\ fs []
    \\ Cases_on `t` \\ fs []
    \\ Cases_on `h'` \\ fs []
    \\ Cases_on `t'` \\ fs [])
  \\ fs []
  \\ Cases_on `e2` \\ fs [])
  |> update_precondition;

val _ = translate (op_consts_pmatch|>conv32|>econv)

val _ = translate (convert_sub_pmatch |> conv32 |> SIMP_RULE std_ss [word_2comp_def,word_mul_def] |> conv32)

val _ = translate (spec32 pull_exp_def(*_pmatch*)) (* TODO: MAP pull_exp inside pmatch seems to throw the translator into an infinite loop *)

val word_inst_pull_exp_side = Q.prove(`
  ∀x. word_inst_pull_exp_side x ⇔ T`,
  ho_match_mp_tac pull_exp_ind>>rw[]>>
  simp[Once (fetch "-" "word_inst_pull_exp_side_def"),
      fetch "-" "word_inst_optimize_consts_side_def",
      wordLangTheory.word_op_def]>>
  metis_tac[]) |> update_precondition

val _ = translate (spec32 inst_select_def(*pmatch*))

val _ = translate (spec32 list_next_var_rename_move_def)

val _ = translate (conv32 ssa_cc_trans_inst_def)
val _ = translate (spec32 full_ssa_cc_trans_def)

val _ = translate (conv32 remove_dead_inst_def)
val _ = translate (conv32 get_live_inst_def)
val _ = translate (spec32 remove_dead_def)

val lem = Q.prove(`
  dimindex(:64) = 64 ∧
  dimindex(:32) = 32`,
  EVAL_TAC);

val _ = translate (INST_TYPE [alpha|->``:32``,beta|->``:32``] get_forced_pmatch
                  |> SIMP_RULE (bool_ss++ARITH_ss) [lem])

val _ = translate (get_delta_inst_def |> conv32)
val _ = translate (wordLangTheory.every_var_inst_def |> conv32)
val _ = translate select_reg_alloc_def
val _ = translate (INST_TYPE [alpha|->``:32``,beta|->``:32``]  word_alloc_def)

val res = translate_no_ind (spec32 three_to_two_reg_pmatch);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ disch_then strip_assume_tac
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac \\ fs []
  \\ rveq \\ fs []
  \\ rename1 `NONE <> a` \\ Cases_on `a` \\ fs [] \\ PairCases_on `x` \\ fs [])
  |> update_precondition;

val word_inst_three_to_two_reg_side = Q.prove(`
∀prog. word_inst_three_to_two_reg_side prog ⇔ T`,
`(∀prog. word_inst_three_to_two_reg_side prog ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = SOME(a,b,c,d,e) ==> word_inst_three_to_two_reg_side c) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = (a,b,c,d,e) ==> word_inst_three_to_two_reg_side c) /\
 (∀opt (a:num) b (c:num) (d:num). opt = SOME(a,b,c,d) ==> word_inst_three_to_two_reg_side b) /\
 (∀opt (a:num_set) b (c:num) (d:num). opt = (a,b,c,d) ==> word_inst_three_to_two_reg_side b) /\
 (∀opt (a:num) b (c:num) (d:num). opt = (a,b,c,d) ==> word_inst_three_to_two_reg_side b) /\
(∀opt a (b:num) (c:num). opt = (a,b,c) ==> word_inst_three_to_two_reg_side a)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:32 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_inst_three_to_two_reg_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_inst_three_to_two_reg_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition

val res = translate_no_ind (spec32 word_removeTheory.remove_must_terminate_pmatch);

val ind_lemma = Q.prove(
  `^(first is_forall (hyp res))`,
  rpt gen_tac
  \\ disch_then strip_assume_tac
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ rveq \\ fs []
  \\ rename1 `NONE <> a`
  \\ Cases_on `a` \\ fs []
  \\ PairCases_on `x` \\ fs [])
  |> update_precondition;

val word_remove_remove_must_terminate_side = Q.prove(`
∀prog. word_remove_remove_must_terminate_side prog ⇔ T`,
`(∀prog. word_remove_remove_must_terminate_side prog ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = SOME(a,b,c,d,e) ==> word_remove_remove_must_terminate_side c) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num). opt = (a,b,c,d,e) ==> word_remove_remove_must_terminate_side c) /\
 (∀opt (a:num) b (c:num) (d:num). opt = SOME(a,b,c,d) ==> word_remove_remove_must_terminate_side b) /\
 (∀opt (a:num_set) b (c:num) (d:num). opt = (a,b,c,d) ==> word_remove_remove_must_terminate_side b) /\
 (∀opt (a:num) b (c:num) (d:num). opt = (a,b,c,d) ==> word_remove_remove_must_terminate_side b) /\
(∀opt a (b:num) (c:num). opt = (a,b,c) ==> word_remove_remove_must_terminate_side a)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:32 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_remove_remove_must_terminate_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_remove_remove_must_terminate_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition;

val res = translate (spec32 word_to_wordTheory.compile_alt);

(* TODO: remove when pmatch is fixed
val word_simp_const_fp_loop_side = Q.prove(`
∀prog nm. word_simp_const_fp_loop_side prog nm ⇔ T`,
`(∀prog nm. word_simp_const_fp_loop_side prog nm ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num) nm. opt = SOME(a,b,c,d,e) ==> word_simp_const_fp_loop_side c nm) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num) nm. opt = (a,b,c,d,e) ==> word_simp_const_fp_loop_side c nm) /\
 (∀opt (a:num) b (c:num) (d:num) nm. opt = SOME(a,b,c,d) ==> word_simp_const_fp_loop_side b nm) /\
 (∀opt (a:num_set) b (c:num) (d:num) nm. opt = (a,b,c,d) ==> word_simp_const_fp_loop_side b nm) /\
 (∀opt (a:num) b (c:num) (d:num) nm. opt = (a,b,c,d) ==> word_simp_const_fp_loop_side b nm) /\
(∀opt a (b:num) (c:num) nm. opt = (a,b,c) ==> word_simp_const_fp_loop_side a nm)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:32 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_simp_const_fp_loop_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_simp_const_fp_loop_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition

val word_simp_const_fp_side = Q.prove(`
  ∀prog. word_simp_const_fp_side prog ⇔ T`,
  fs[fetch "-" "word_simp_const_fp_side_def",
     word_simp_const_fp_loop_side]) |> update_precondition

val word_simp_compile_exp_side = Q.prove(`
  ∀prog. word_simp_compile_exp_side prog ⇔ T`,
  fs[fetch "-" "word_simp_compile_exp_side_def",
     word_simp_const_fp_side]) |> update_precondition
*)

(*
val word_inst_inst_select_side = Q.prove(`
∀prog c n. word_inst_inst_select_side c n prog ⇔ T`,
`(∀prog c n. word_inst_inst_select_side c n prog ⇔ T) /\
 (∀opt (a:num) (b:num_set) c (d:num) (e:num) x n. opt = SOME(a,b,c,d,e) ==> word_inst_inst_select_side x n c) /\
(∀opt (a:num) (b:num_set) c (d:num) (e:num) x n. opt = (a,b,c,d,e) ==> word_inst_inst_select_side x n c) /\
 (∀opt (a:num) b (c:num) (d:num) x n. opt = SOME(a,b,c,d) ==> word_inst_inst_select_side x n b) /\
 (∀opt (a:num_set) b (c:num) (d:num) x n. opt = (a,b,c,d) ==> word_inst_inst_select_side x n b) /\
 (∀opt (a:num) b (c:num) (d:num) x n. opt = (a,b,c,d) ==> word_inst_inst_select_side x n b) /\
(∀opt a (b:num) (c:num) x n. opt = (a,b,c) ==> word_inst_inst_select_side x n a)`
   suffices_by fs[]
>> ho_match_mp_tac(TypeBase.induction_of ``:32 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_inst_inst_select_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_inst_inst_select_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES,fetch "asm" "reg_imm_nchotomy"]) |> update_precondition
*)

(*
val word_to_word_compile_side = Q.prove(`
  ∀x y z. word_to_word_compile_side x y z ⇔ T`,
  fs[fetch"-""word_to_word_compile_side_def",word_to_wordTheory.next_n_oracle_def,word_inst_inst_select_side]) |> update_precondition
*)

val _ = translate(FromList_code_def |> conv32 |> econv)
val _ = translate(FromList1_code_def |> inline_simp |> conv32)
val _ = translate(MakeBytes_def |> conv32)
val _ = translate(WriteLastByte_aux_def |> conv32)
val _ = translate(WriteLastBytes_def |> conv32)
val _ = translate(RefByte_code_def |> inline_simp |> conv32 |> SIMP_RULE std_ss[SmallLsr_def])
val _ = translate(RefArray_code_def |> inline_simp |> conv32|>econv)
val _ = translate(Replicate_code_def|> inline_simp |> conv32)
val _ = translate(AddNumSize_def|> conv32)
val _ = translate(AnyHeader_def|> inline_simp |> conv32)
val _ = translate(AnyArith_code_def|> inline_simp |> conv32)
val _ = translate(Add_code_def|> conv32)
val _ = translate(Sub_code_def|> conv32)
val _ = translate(Mul_code_def|> conv32)
val _ = translate(Div_code_def|> conv32)
val _ = translate(Mod_code_def|> conv32)
val _ = translate(MemCopy_code_def|> inline_simp |> conv32)
val r = translate(ByteCopy_code_def |> inline_simp |> conv32)
val r = translate(ByteCopyAdd_code_def |> conv32)
val r = translate(ByteCopySub_code_def |> conv32 |> econv)
val r = translate(ByteCopyNew_code_def |> conv32)

val r = translate(Install_code_def |> conv32)
val r = translate(InstallCode_code_def |> inline_simp |> conv32)
val r = translate(InstallData_code_def |> inline_simp |> conv32)

val _ = translate(Append_code_def|> inline_simp |> conv32 |> we_simp |> econv |> SIMP_RULE std_ss [shift_left_rwt])
val _ = translate(AppendMainLoop_code_def|> inline_simp |> conv32)
val _ = translate(AppendLenLoop_code_def|> inline_simp |> conv32)
val _ = translate(AppendFastLoop_code_def|> inline_simp |> conv32)

val _ = translate(Compare1_code_def|> inline_simp |> conv32)
val _ = translate(Compare_code_def|> inline_simp |> conv32)

val _ = translate(Equal1_code_def|> inline_simp |> conv32)
val _ = translate(Equal_code_def|> inline_simp |> SIMP_RULE std_ss [backend_commonTheory.closure_tag_def,backend_commonTheory.partial_app_tag_def] |> conv32)

val _ = translate(LongDiv1_code_def|> inline_simp |> wcomp_simp |> conv32)
val _ = translate(LongDiv_code_def|> inline_simp |> conv32)

val _ = translate (word_bignumTheory.generated_bignum_stubs_eq |> inline_simp |> conv32)

val res = translate (data_to_wordTheory.compile_def
                     |> SIMP_RULE std_ss [data_to_wordTheory.stubs_def] |> conv32_RHS);

(* translate some 32/64 specific parts of the tap/explorer
   that can't be translated in explorerProgScript *)
val res = translate (presLangTheory.tap_word_def |> conv32);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
