(*
  Translate the data_to_word part of the 64-bit compiler.
*)

open preamble ml_translatorLib ml_translatorTheory
     printingProgTheory std_preludeTheory
local open backendTheory in end

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = new_theory "to_word64Prog"

val _ = translation_extends "printingProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_word64Prog");
val _ = ml_translatorLib.use_string_type true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Triviality NOT_NIL_AND_LEMMA:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then [alpha |-> ``:64``,beta|->``:64``] else []

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

val spec64 = INST_TYPE[alpha|->``:64``]

val conv64 = GEN_ALL o CONV_RULE (wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val conv64_RHS = GEN_ALL o CONV_RULE (RHS_CONV wordsLib.WORD_CONV) o spec64 o SPEC_ALL

val gconv = CONV_RULE (DEPTH_CONV wordsLib.WORD_GROUND_CONV)

val econv = CONV_RULE wordsLib.WORD_EVAL_CONV

open data_to_wordTheory

val we_simp = SIMP_RULE std_ss [word_extract_w2w_mask,w2w_id]

val wcomp_simp = SIMP_RULE std_ss [word_2comp_def]

val _ = translate stack_to_labTheory.is_gen_gc_def

val _ = translate adjust_set_def

val _ = translate (make_header_def |> SIMP_RULE std_ss [word_lsl_n2w]|> conv64_RHS)

val _ = translate (shift_left_def |> conv64)
val _ = translate (shift_right_def |> spec64 |> CONV_RULE fcpLib.INDEX_CONV)

val i2w_eq_n2w_lemma = prove(
  ``i2w (& (k * n)) = n2w (k * n)``,
  fs [integer_wordTheory.i2w_def]);

val lemma2 = prove(
  ``8 * x < (2**64) <=> x < (2**64) DIV 8``,
  fs []) |> SIMP_RULE std_ss []

val _ = translate (get_gen_size_def |> spec64
    |> SIMP_RULE (srw_ss()) [dimword_def,bytes_in_word_def,word_mul_n2w]
    |> REWRITE_RULE [GSYM i2w_eq_n2w_lemma,lemma2]);

val _ = translate (tag_mask_def |> conv64_RHS |> we_simp |> conv64_RHS |> SIMP_RULE std_ss [shift_left_rwt] |> SIMP_RULE std_ss [Once (GSYM shift_left_rwt),word_2comp_def] |> conv64)

val _ = translate (encode_header_def |> conv64_RHS)

(* Manual inlines : shift_def, bytes_in_word because of 'a arg *)
val inline_simp =
    SIMP_RULE std_ss [backend_commonTheory.word_shift_def,bytes_in_word_def];

val _ = register_type ``:64 wordLang$prog``;

(* check 64 prog is known to be an EqualityType *)
val EqualityType_prog = EqualityType_rule [] ``:64 wordLang$prog``;

val _ = translate (StoreEach_def |> inline_simp |> conv64);

val _ = translate (all_ones_def |> conv64_RHS |> we_simp |> SIMP_RULE std_ss [shift_left_rwt,shift_right_rwt] |> wcomp_simp |> conv64 |> wcomp_simp |> conv64)

val _ = translate (maxout_bits_def |> SIMP_RULE std_ss [word_lsl_n2w] |> conv64)

val _ = translate (ptr_bits_def  |> conv64)

val _ = translate (real_addr_def |> inline_simp |> conv64_RHS |> SIMP_RULE std_ss [LET_THM])

val _ = translate (real_offset_def |> inline_simp |> conv64)
val _ = translate (real_byte_offset_def |> inline_simp |> conv64)
val _ = translate (GiveUp_def |> wcomp_simp |> conv64)

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``]

Triviality assign_rw:
  (i < 0 ⇒ n2w (Num (4 * (0 -i))) = n2w (Num (ABS (4*(0-i))))) ∧
  (¬(i < 0) ⇒ n2w (Num (4 * i)) = n2w (Num (ABS (4*i))))
Proof
  rw[]
  >-
    (`0 ≤ 4* -i` by intLib.COOPER_TAC>>
    metis_tac[integerTheory.INT_ABS_EQ_ID])
  >>
    `0 ≤ 4*i` by intLib.COOPER_TAC>>
    metis_tac[integerTheory.INT_ABS_EQ_ID]
QED

(* TODO: word_mul should maybe target a real op ?
   TODO: econv might be going too far with case simplification
*)

val _ = translate (ShiftVar_def |> inline_simp |> conv64);
val _ = translate (LoadWord64_def |> inline_simp |> conv64)
val _ = translate (WriteWord64_def |> inline_simp |> conv64)
val _ = translate (LoadBignum_def |> inline_simp |> conv64)

val Smallnum_alt = prove(
  ``Smallnum i =
    if i < 0 then 0w − n2w (Num (ABS (4 * (0 − i))))
             else n2w (Num (ABS (4 * i)))``,
  fs [Smallnum_def] \\ Cases_on `i` \\ fs [integerTheory.INT_ABS_NUM]);

val _ = translate (Smallnum_alt |> inline_simp |> conv64)
val _ = translate (MemEqList_def |> inline_simp |> conv64)

Theorem n2mw_ind =
  multiwordTheory.n2mw_ind |> inline_simp |> conv64
val _ = translate (multiwordTheory.n2mw_def |> inline_simp |> conv64);
val _ = translate (multiwordTheory.i2mw_def |> inline_simp |> conv64);
val _ = translate (get_Word_def |> inline_simp |> conv64);
val _ = translate (BignumHalt_def |> inline_simp |> conv64);
val _ = translate(Maxout_bits_code_def |> conv64);
val _ = translate(Make_ptr_bits_code_def |> inline_simp |> conv64);
val _ = translate(SilentFFI_def |> inline_simp |> wcomp_simp |> conv64);
val _ = translate(AllocVar_def |> inline_simp |> wcomp_simp |> conv64);

val _ = register_type ``:64 wordLang$word_loc``;

val _ = translate (byteTheory.byte_index_def |> inline_simp |> conv64);

val _ = translate byteTheory.set_byte_64;
val _ = translate (byteTheory.bytes_to_word_def |> inline_simp |> conv64);
val _ = translate (data_to_wordTheory.getWords_def
                   |> INST_TYPE [alpha|->beta, beta |-> alpha] |> conv64);
val _ = translate (data_to_wordTheory.StoreAnyConsts_def |> inline_simp |> conv64);
val _ = translate (data_to_wordTheory.lookup_mem_def |> conv64);
val _ = translate (data_to_wordTheory.write_bytes_def |> inline_simp |> conv64);

Definition my_lsl_shift_def:
  my_lsl_shift w n = (w << n)
End

val ugly_lsl_lemma =
  “my_lsl_shift (w:'a word) n”
  |> (REWRITE_CONV [my_lsl_shift_def]
      THENC RATOR_CONV (ONCE_REWRITE_CONV [GSYM n2w_w2n])
      THENC REWRITE_CONV [word_lsl_n2w]);

val _ = translate (ugly_lsl_lemma |> conv64);

Definition int_to_words_def:
  int_to_words c i offset =
    ^(data_to_wordTheory.part_to_words_def |> CONJUNCTS |> el 1
     |> SPEC_ALL |> concl |> rand)
End

Definition con_to_words_def:
  con_to_words c m t ns offset =
    ^(data_to_wordTheory.part_to_words_def |> CONJUNCTS |> el 2
     |> SPEC_ALL |> concl |> rand)
End

Definition w64_to_words_def:
  w64_to_words c w offset =
    ^(data_to_wordTheory.part_to_words_def |> CONJUNCTS |> el 3
     |> SPEC_ALL |> concl |> rand)
End

Definition str_to_words_def:
  str_to_words c s offset =
    ^(data_to_wordTheory.part_to_words_def |> CONJUNCTS |> el 4
     |> SPEC_ALL |> concl |> rand)
End

Theorem part_to_words_def =
  data_to_wordTheory.part_to_words_def
  |> REWRITE_RULE [GSYM int_to_words_def,
                   GSYM con_to_words_def,
                   GSYM w64_to_words_def,
                   GSYM str_to_words_def];

Definition bytes_of_string_def:
  bytes_of_string cs = MAP (λc. n2w (ORD c) :word8) (explode cs)
End

val _ = ml_translatorLib.use_string_type false;
val _ = translate bytes_of_string_def;
val _ = ml_translatorLib.use_string_type true;

val r = int_to_words_def
     |> REWRITE_RULE [data_to_wordTheory.small_int_def,
                      data_to_wordTheory.make_ptr_def,GSYM my_lsl_shift_def]
     |> inline_simp |> conv64
     |> translate;

val r = w64_to_words_def
     |> SIMP_RULE std_ss [data_to_wordTheory.small_int_def,LET_THM,LENGTH,
                      data_to_wordTheory.make_ptr_def,GSYM my_lsl_shift_def]
     |> inline_simp |> conv64 |> SIMP_RULE std_ss [LENGTH]
     |> translate;

val r = con_to_words_def
     |> SIMP_RULE std_ss [data_to_wordTheory.small_int_def,LET_THM,LENGTH,
                      data_to_wordTheory.make_ptr_def,GSYM my_lsl_shift_def]
     |> inline_simp |> conv64 |> SIMP_RULE std_ss [LENGTH]
     |> translate;

val r = str_to_words_def
     |> SIMP_RULE std_ss [data_to_wordTheory.small_int_def,LENGTH,
                      data_to_wordTheory.byte_len_def,combinTheory.o_DEF,
                      data_to_wordTheory.make_byte_header_def,
                      data_to_wordTheory.make_ptr_def,GSYM my_lsl_shift_def]
     |> inline_simp |> conv64
     |> SIMP_RULE std_ss [LENGTH,LENGTH_MAP,GSYM bytes_of_string_def]
     |> translate;

val r = part_to_words_def |> conv64 |> translate;

val r = data_to_wordTheory.parts_to_words_def |> inline_simp
        |> REWRITE_RULE [word_mul_n2w] |> conv64 |> translate;
val r = data_to_wordTheory.const_parts_to_words_def |> conv64 |> translate;

val _ = translate arg1_def;
val _ = translate arg2_pmatch;
val _ = translate arg3_pmatch;
val _ = translate arg4_pmatch;

fun tweak_assign_def th =
  th |> SIMP_RULE std_ss [assign_rw]
     |> inline_simp |> conv64 |> we_simp
     |> SIMP_RULE std_ss [SHIFT_ZERO,shift_left_rwt]
     |> SIMP_RULE std_ss [word_mul_def,LET_THM] |> gconv;

val res = all_assign_defs |> CONJUNCTS |> map tweak_assign_def |> map translate;
val res = translate (assign_def |> tweak_assign_def);

Triviality lemma:
  !A B. A = B ==> B ≠ A ==> F
Proof
  metis_tac[]
QED

(*
val data_to_word_assign_side = Q.prove(`
  ∀a b c d e f g. data_to_word_assign_side a b c d e f g ⇔ T`,
  rpt strip_tac>>
  simp[fetch "-" "data_to_word_assign_side_def",NULL]>>
  Cases_on`e`>>fs[]>>
  Cases_on`f`>>fs[]>>
  TRY(Cases_on`t`)>>TRY(Cases_on`t'`)>>
  TRY(Cases_on`w`)>>fs[]>>
  TRY(Cases_on`(encode_header a 3 1):word64 option`)>>
  TRY(Cases_on`o'`)>>
  TRY(Cases_on`s`)>>
  metis_tac[word_op_type_nchotomy,option_nchotomy,NOT_NONE_SOME,list_distinct]) |> update_precondition
*)

Theorem comp_ind =
  data_to_wordTheory.comp_ind|> conv64|> wcomp_simp
(* Inlines the let k = 8 manually *)
val _ = translate (comp_def |> conv64 |> wcomp_simp |> conv64 |> SIMP_RULE std_ss[LET_THM |> INST_TYPE [alpha|->``:num``]]);

open word_simpTheory word_allocTheory word_instTheory

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``]

val res = word_cseTheory.map_insert_def |> DefnBase.one_line_ify NONE |> translate;
val res = translate (word_cseTheory.word_cseInst_def |> spec64);
val res = translate_no_ind (word_cseTheory.word_cse_def |> spec64);

Theorem word_cse_ind[local]:
  word_cse_word_cse_ind
Proof
  rewrite_tac [fetch "-" "word_cse_word_cse_ind_def"]
  \\ rpt gen_tac \\ rpt disch_tac
  \\ ONCE_REWRITE_TAC [SWAP_FORALL_THM]
  \\ ho_match_mp_tac wordLangTheory.max_var_ind
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ fs []
QED
val _ = word_cse_ind |> update_precondition;

val res = translate (word_cseTheory.word_common_subexp_elim_def |> spec64);

val _ = translate (const_fp_inst_cs_def |> spec64 |> econv)

Triviality rws:
  ($+ = λx y. x + y) ∧
  ($&& = λx y. x && y) ∧
  ($|| = λx y. x || y) ∧
  ($?? = λx y. x ?? y)
Proof
  fs[FUN_EQ_THM]
QED

val _ = translate (wordLangTheory.word_op_def |> ONCE_REWRITE_RULE [rws,WORD_NOT_0] |> spec64 |> gconv)

Triviality word_msb_rw:
  word_msb (a:word64) ⇔ (a>>>63) <> 0w
Proof
  rw[word_msb_def,fcpTheory.CART_EQ,word_index,word_lsr_def,fcpTheory.FCP_BETA]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  \\ `i = 0` by decide_tac \\ fs[]
QED

val arith_shift_right_ind_orig = arith_shift_right_ind;

Theorem arith_shift_right_ind =
  arith_shift_right_ind_orig |> spec64
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE (QUANT_CONV(LAND_CONV fcpLib.INDEX_CONV)) |> gconv

val _ = translate (
  arith_shift_right_def |> spec64
  |> SIMP_RULE std_ss [word_msb_rw]
  |> CONV_RULE fcpLib.INDEX_CONV |> gconv);

val _ = translate miscTheory.any_word64_ror_def;

val res = translate (wordLangTheory.word_sh_def
  |> INST_TYPE [``:'a``|->``:64``]
  |> REWRITE_RULE [miscTheory.word_ror_eq_any_word64_ror]
  |> RW[shift_left_rwt,shift_right_rwt,arith_shift_right_rwt] |> conv64)

val _ = translate (asmTheory.word_cmp_def |> REWRITE_RULE[WORD_LO,WORD_LT] |> spec64 |> REWRITE_RULE[word_msb_rw]);

(* TODO: remove when pmatch is fixed *)
val _ = translate (spec64 const_fp_loop_def)

val _ = translate (spec64 is_simple_pmatch_def)
val _ = translate (spec64 dest_Raise_num_pmatch_def)
val _ = translate (spec64 try_if_hoist2_def)
val _ = translate (spec64 try_if_hoist1_def)
val _ = translate (spec64 simp_duplicate_if_def)

val _ = translate (spec64 compile_exp_def)

val _ = translate (wordLangTheory.max_var_inst_def |> conv64)
val _ = translate (spec64 wordLangTheory.max_var_def)

val _ = translate (conv64_RHS integer_wordTheory.WORD_LEi)

val _ = translate (asmTheory.offset_ok_def |> SIMP_RULE std_ss [alignmentTheory.aligned_bitwise_and] |> conv64)
val _ = translate (is_Lookup_CurrHeap_pmatch |> conv64)
val res = translate_no_ind (inst_select_exp_pmatch |> conv64 |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv64)

Triviality inst_select_exp_ind:
  word_inst_inst_select_exp_ind
Proof
  rewrite_tac [fetch "-" "word_inst_inst_select_exp_ind_def"]
  \\ rpt gen_tac
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
  \\ Cases_on `e2` \\ fs []
QED

val _ = inst_select_exp_ind |> update_precondition;

val _ = translate (op_consts_pmatch|>conv64|>econv)

val _ = translate (convert_sub_pmatch |> conv64 |> SIMP_RULE std_ss [word_2comp_def,word_mul_def] |> conv64)

val _ = translate (spec64 pull_exp_def(*_pmatch*)) (* TODO: MAP pull_exp inside pmatch seems to throw the translator into an infinite loop *)

val word_inst_pull_exp_side = Q.prove(`
  ∀x. word_inst_pull_exp_side x ⇔ T`,
  ho_match_mp_tac pull_exp_ind>>rw[]>>
  simp[Once (fetch "-" "word_inst_pull_exp_side_def"),
      fetch "-" "word_inst_optimize_consts_side_def",
      wordLangTheory.word_op_def]>>
  metis_tac[]) |> update_precondition

val _ = translate (spec64 inst_select_def(*pmatch*))

val _ = translate (spec64 list_next_var_rename_move_def)

val _ = translate (conv64 ssa_cc_trans_inst_def)
val _ = translate (spec64 full_ssa_cc_trans_def)

val _ = translate (conv64 remove_dead_inst_def)
val _ = translate (conv64 get_live_inst_def)
val _ = translate (spec64 remove_dead_def)

Triviality lem:
  dimindex(:64) = 64 ∧
  dimindex(:32) = 32
Proof
  EVAL_TAC
QED

val _ = translate (INST_TYPE [alpha|->``:64``,beta|->``:64``] get_forced_pmatch
                  |> SIMP_RULE (bool_ss++ARITH_ss) [lem])

val _ = translate (get_delta_inst_def |> conv64)
val _ = translate (wordLangTheory.every_var_inst_def |> conv64)
val _ = translate select_reg_alloc_def
val _ = translate (INST_TYPE [alpha|->``:64``,beta|->``:64``]  word_alloc_def)

val res = translate_no_ind (spec64 three_to_two_reg_pmatch);

Triviality three_to_two_reg_ind:
  word_inst_three_to_two_reg_ind
Proof
  rewrite_tac [fetch "-" "word_inst_three_to_two_reg_ind_def"]
  \\ rpt gen_tac
  \\ disch_then strip_assume_tac
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac \\ fs []
  \\ rveq \\ fs []
  \\ rename1 `NONE <> a` \\ Cases_on `a` \\ fs [] \\ PairCases_on `x` \\ fs []
QED

val _ = three_to_two_reg_ind |> update_precondition;

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
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_inst_three_to_two_reg_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_inst_three_to_two_reg_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition

val res = translate_no_ind (spec64 word_removeTheory.remove_must_terminate_pmatch);

Triviality remove_must_terminate_ind:
  word_remove_remove_must_terminate_ind
Proof
  rewrite_tac [fetch "-" "word_remove_remove_must_terminate_ind_def"]
  \\ rpt gen_tac
  \\ disch_then strip_assume_tac
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum (match_mp_tac o MP_CANON)
  \\ rpt strip_tac
  \\ fs [FORALL_PROD]
  \\ rveq \\ fs []
  \\ rename1 `NONE <> a`
  \\ Cases_on `a` \\ fs []
  \\ PairCases_on `x` \\ fs []
QED

val _ = remove_must_terminate_ind |> update_precondition;

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
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
>> rpt strip_tac
>> fs[]
>> rw[Once(fetch "-" "word_remove_remove_must_terminate_side_def")]
>> fs[]
>> POP_ASSUM(ASSUME_TAC o RW.PURE_ONCE_RW_RULE[fetch"-" "word_remove_remove_must_terminate_side_def"])
>> fs[]
>> metis_tac[pair_CASES,option_CASES]) |> update_precondition;

val res = translate (spec64 word_to_wordTheory.compile_alt);

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
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
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
>> ho_match_mp_tac(TypeBase.induction_of ``:64 prog``)
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

val _ = translate(FromList_code_def |> conv64 |> econv)
val _ = translate(FromList1_code_def |> inline_simp |> conv64)
val _ = translate(MakeBytes_def |> conv64)
val _ = translate(WriteLastByte_aux_def |> conv64)
val _ = translate(WriteLastBytes_def |> conv64)
val _ = translate(RefByte_code_def |> inline_simp |> conv64 |> SIMP_RULE std_ss[SmallLsr_def])
val _ = translate(RefArray_code_def |> inline_simp |> conv64|>econv)
val _ = translate(Replicate_code_def|> inline_simp |> conv64)
val _ = translate(AddNumSize_def|> conv64)
val _ = translate(AnyHeader_def|> inline_simp |> conv64)
val _ = translate(AnyArith_code_def|> inline_simp |> conv64)
val _ = translate(Add_code_def|> conv64)
val _ = translate(Sub_code_def|> conv64)
val _ = translate(Mul_code_def|> conv64)
val _ = translate(Div_code_def|> conv64)
val _ = translate(Mod_code_def|> conv64)
val _ = translate(MemCopy_code_def|> inline_simp |> conv64)
val r = translate(ByteCopy_code_def |> inline_simp |> conv64)
val r = translate(ByteCopyAdd_code_def |> conv64)
val r = translate(ByteCopySub_code_def |> conv64 |> econv)
val r = translate(ByteCopyNew_code_def |> conv64)

val r = translate(Install_code_def |> conv64)
val r = translate(InstallCode_code_def |> inline_simp |> conv64)
val r = translate(InstallData_code_def |> inline_simp |> conv64)

val _ = translate(Append_code_def|> inline_simp |> conv64 |> we_simp |> econv |> SIMP_RULE std_ss [shift_left_rwt])
val _ = translate(AppendMainLoop_code_def|> inline_simp |> conv64)
val _ = translate(AppendLenLoop_code_def|> inline_simp |> conv64)
val _ = translate(AppendFastLoop_code_def|> inline_simp |> conv64)

val _ = translate(Compare1_code_def|> inline_simp |> conv64)
val _ = translate(Compare_code_def|> inline_simp |> conv64)

val _ = translate(Equal1_code_def|> inline_simp |> conv64)
val _ = translate(Equal_code_def|> inline_simp |> SIMP_RULE std_ss [backend_commonTheory.closure_tag_def,backend_commonTheory.partial_app_tag_def] |> conv64)


val _ = translate(LongDiv1_code_def|> inline_simp |> wcomp_simp |> conv64)
val _ = translate(LongDiv_code_def|> inline_simp |> conv64)

val _ = translate (word_bignumTheory.generated_bignum_stubs_eq |> inline_simp |> conv64)

val _ = translate data_to_wordTheory.stub_names_def
val _ = translate word_to_stackTheory.stub_names_def
val _ = translate stack_allocTheory.stub_names_def
val _ = translate stack_removeTheory.stub_names_def
val res = translate (data_to_wordTheory.compile_def
                     |> SIMP_RULE std_ss [data_to_wordTheory.stubs_def] |> conv64_RHS);


(* explorer specific functions *)

val _ = ml_translatorLib.use_string_type false;
val r = presLangTheory.num_to_hex_def |> translate;
val r = presLangTheory.word_to_display_def |> conv64 |> translate;
val r = presLangTheory.item_with_word_def |> conv64 |> translate;
val r = presLangTheory.asm_binop_to_display_def |> translate;
val r = presLangTheory.asm_reg_imm_to_display_def |> conv64 |> translate;
val r = presLangTheory.asm_arith_to_display_def |> conv64 |> translate;
val r = presLangTheory.word_to_display_def |> INST_TYPE [“:'a”|->“:5”] |> translate
val r = presLangTheory.item_with_word_def |> INST_TYPE [“:'a”|->“:5”] |> translate
val r = presLangTheory.store_name_to_display_def |> conv64 |> translate
val r = presLangTheory.word_exp_to_display_def |> conv64 |> translate
val r = presLangTheory.asm_inst_to_display_def |> conv64 |> translate;
val r = presLangTheory.ws_to_display_def |> conv64 |> translate
val r = presLangTheory.word_seqs_def |> conv64 |> translate

val _ = ml_translatorLib.use_string_type true;
val r = presLangTheory.word_prog_to_display_def
          |> conv64
          |> REWRITE_RULE [presLangTheory.string_imp_def]
          |> translate

val r = presLangTheory.word_fun_to_display_def |> conv64 |> translate

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
