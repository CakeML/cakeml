(*
  Translate the data_to_word part of the compiler.
*)
Theory to_wordProg[no_sig_docs]
Ancestors
  ml_translator printingProg std_prelude data_to_word word_simp
  word_alloc word_inst backend[qualified]
Libs
  preamble ml_translatorLib blastLib[qualified]

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "printingProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_wordProg");
val _ = ml_translatorLib.use_sub_check true;

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

Theorem NOT_NIL_AND_LEMMA[local]:
  (b <> [] /\ x) = if b = [] then F else x
Proof
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []
QED

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

fun def_of_const tm = let
  val {Thy,Name,...} = dest_thy_const tm
  val def = DB.fetch Thy (Name ^ "_pmatch") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_def") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_DEF") handle HOL_ERR _ =>
            DB.fetch Thy (Name ^ "_thm") handle HOL_ERR _ =>
            DB.fetch Thy Name
  val insts = match_type (type_of (prim_mk_const {Thy = Thy, Name = Name}))
                         (type_of tm)
  in def |> INST_TYPE insts |> REWRITE_RULE (!extra_preprocessing)
         |> CONV_RULE (DEPTH_CONV BETA_CONV)
         |> REWRITE_RULE [NOT_NIL_AND_LEMMA] end;

val _ = find_def_for_const := def_of_const;
val _ = use_long_names := true;

(* Signed constants and bit operations are independent of the target width. *)
val _ = translate int_bitwiseTheory.int_not_def;
val _ = translate int_bitwiseTheory.bits_of_num_def;
val _ = translate int_bitwiseTheory.bits_of_int_def;

Theorem int_bitwise_bits_of_int_side[local]:
  ∀i. int_bitwise_bits_of_int_side i
Proof
  rw [fetch "-" "int_bitwise_bits_of_int_side_def",
      int_bitwiseTheory.int_not_def] \\ intLib.COOPER_TAC
QED
val _ = update_precondition int_bitwise_bits_of_int_side;

val _ = translate int_bitwiseTheory.num_of_bits_def;
val _ = translate int_bitwiseTheory.int_of_bits_def;
val _ = translate int_bitwiseTheory.bits_bitwise_def;
val _ = translate int_bitwiseTheory.int_bitwise_def;
Theorem boolean_ops[local]:
  (($/\ : bool -> bool -> bool) = λx y. x /\ y) ∧
  (($\/ : bool -> bool -> bool) = λx y. x \/ y)
Proof
  simp [FUN_EQ_THM]
QED

val _ = translate (int_bitwiseTheory.int_and_def |> SRULE [FUN_EQ_THM]
  |> ONCE_REWRITE_RULE [boolean_ops]);
val _ = translate (int_bitwiseTheory.int_or_def |> SRULE [FUN_EQ_THM] |> ONCE_REWRITE_RULE [boolean_ops]);
val _ = translate (int_bitwiseTheory.int_xor_def |> SRULE [FUN_EQ_THM] |> ONCE_REWRITE_RULE [boolean_ops]);

val _ = translate asmTheory.arch_width_bits_def;
val _ = translate asmTheory.arch_bytes_def;
val _ = translate asmTheory.arch_shift_def;

val _ = register_type “:wordLang$prog”;
val EqualityType_prog = EqualityType_rule [] “:wordLang$prog”;

val inline_simp = SIMP_RULE std_ss [backend_commonTheory.word_shift_def];
val _ = translate stack_to_labTheory.is_gen_gc_def;
val _ = translate data_to_wordTheory.adjust_set_def;
val _ = translate data_to_wordTheory.make_header_def;
val _ = translate data_to_wordTheory.get_gen_size_def;
val _ = translate data_to_wordTheory.tag_mask_def;
val _ = translate data_to_wordTheory.encode_header_def;
val _ = translate data_to_wordTheory.StoreEach_def;
val _ = translate data_to_wordTheory.all_ones_def;
val _ = translate data_to_wordTheory.maxout_bits_def;
val _ = translate data_to_wordTheory.ptr_bits_def;
val _ = translate (data_to_wordTheory.real_addr_def |> inline_simp);
val _ = translate data_to_wordTheory.real_offset_def;
val _ = translate data_to_wordTheory.real_byte_offset_def;
val _ = translate data_to_wordTheory.real_bit_offset_def;
val _ = translate data_to_wordTheory.GiveUp_def;
val _ = translate data_to_wordTheory.WriteWord32_on_32_def;
val _ = translate data_to_wordTheory.WriteWord64_on_32_def;
val _ = translate data_to_wordTheory.WordOp64_on_32_def;
val _ = translate data_to_wordTheory.ShiftVar_def;
Theorem data_to_word_shiftvar_side[local]:
  ∀bits sh v n. data_to_word_shiftvar_side bits sh v n ⇔
    bits ≠ 0 ∨ sh ≠ Ror
Proof
  Cases_on `bits` \\ simp [fetch "-" "data_to_word_shiftvar_side_def"]
QED
val _ = update_precondition data_to_word_shiftvar_side;
val res = translate data_to_wordTheory.WordShift64_on_32_def;
val _ = if null (hyp res) then () else let
  val total = Q.prove (
    `∀sh n. data_to_word_wordshift64_on_32_side sh n`,
    simp [fetch "-" "data_to_word_wordshift64_on_32_side_def",
          fetch "-" "data_to_word_shiftvar_side_def"])
  val _ = save_thm ("data_to_word_wordshift64_on_32_side_total", total)
 in update_precondition total; () end;
val _ = translate data_to_wordTheory.WordShiftVar64_on_32_def;
val _ = translate data_to_wordTheory.WordShiftVar64_def;
val _ = translate data_to_wordTheory.ShiftW8_def;
val _ = translate data_to_wordTheory.LoadWord64_def;
val _ = translate data_to_wordTheory.WriteWord64_def;
val _ = translate data_to_wordTheory.LoadBignum_def;
val _ = translate data_to_wordTheory.Smallnum_def;
val _ = translate data_to_wordTheory.MemEqList_def;
val _ = translate data_to_wordTheory.SmallDivMod_def;

(* Constant construction converts through both fixed HOL word widths. *)
fun translate_word_conversions ty = let
  val spec = INST_TYPE [alpha |-> ty]
  val conv = GEN_ALL o CONV_RULE wordsLib.WORD_CONV o spec o SPEC_ALL
  val _ = translate (integer_wordTheory.w2i_eq_w2n |> conv)
  val r = translate_no_ind (multiwordTheory.n2mw_def |> conv)
  val pre_tm = hd (hyp r)
  val pre_name = fst (dest_const pre_tm)
  val pre_def = fetch "-" (pre_name ^ "_def")
  val total = prove (pre_tm,
    rw [pre_def] \\ completeInduct_on `v1` \\ last_x_assum irule
    \\ rw [] \\ first_x_assum irule \\ simp [DIV_LT_X])
  val _ = save_thm (pre_name ^ "_total", total)
  val _ = update_precondition total
  val _ = translate (multiwordTheory.i2mw_def |> conv)
  val _ = translate (byteTheory.byte_index_def |> conv)
  val _ = translate (if ty = “:32” then byteTheory.set_byte_32 else byteTheory.set_byte_64)
  val _ = translate (byteTheory.bytes_to_word_def |> conv)
 in () end;
val _ = List.app translate_word_conversions [“:32”,“:64”];
val _ = translate data_to_wordTheory.lookup_mem_def;
val _ = translate (data_to_wordTheory.write_bytes_def |> SRULE [LET_THM]);
val _ = translate (data_to_wordTheory.part_to_words_def |> inline_simp
  |> SRULE [data_to_wordTheory.small_int_def, data_to_wordTheory.byte_len_def, combinTheory.o_DEF, GSYM GREATER_DEF]);
val _ = translate data_to_wordTheory.parts_to_words_def;
val _ = translate data_to_wordTheory.const_parts_to_words_def;
val _ = translate data_to_wordTheory.StoreAnyConsts_def;
val _ = translate data_to_wordTheory.SetBool_def;
val _ = translate data_to_wordTheory.AssignCmp_def;
val _ = translate data_to_wordTheory.arg1_def;
val _ = translate data_to_wordTheory.arg2_pmatch;
val _ = translate data_to_wordTheory.arg3_pmatch;
val _ = translate data_to_wordTheory.arg4_pmatch;

val loc_values = find "location_def"
  |> filter (fn ((m,_),_) => m = "data_to_word")
  |> map (fn (_,(d,_,_)) => d |> concl |> dest_eq |> fst |> EVAL)
  |> LIST_CONJ;

fun tweak_assign_def th =
  th |> SIMP_RULE std_ss [loc_values] |> inline_simp;
val res = data_to_wordTheory.all_assign_defs |> CONJUNCTS |> rev |> map tweak_assign_def |> map translate;
Theorem arch_width_bits_nonzero[local,simp]:
  arch_width_bits aw ≠ 0
Proof
  Cases_on `aw` \\ EVAL_TAC
QED

fun prove_assign_side name = let
  val def = fetch "-" (name ^ "_def")
  val (vs,eq) = strip_forall (concl def)
  val total = prove (list_mk_forall (vs,lhs eq),
    simp [def,data_to_word_shiftvar_side,arch_width_bits_nonzero])
  val _ = save_thm (name ^ "_total", total)
 in update_precondition total; () end;
val _ = List.app prove_assign_side
  ["data_to_word_assign_boundscheckbyte_side",
   "data_to_word_assign_boundscheckbit_side",
   "data_to_word_assign_boundscheckarray_side",
   "data_to_word_assign_boundscheckblock_side"];

val res = translate (data_to_wordTheory.assign_def |> tweak_assign_def);
val _ = translate data_to_wordTheory.force_thunk_def;
val _ = translate (data_to_wordTheory.comp_def |> SIMP_RULE std_ss [LET_THM]);

val res = word_cseTheory.map_insert_def |> DefnBase.one_line_ify NONE |> translate;

val res = translate word_cseTheory.bm_inter_eq_def;
val res = translate sptreeTheory.inter_eq_def;
val res = translate word_cseTheory.merge_data_def;

val _ = translate word_cseTheory.intToNum_def;

Theorem word_cse_inttonum_side:
  word_cse_inttonum_side i
Proof
  rw [fetch "-" "word_cse_inttonum_side_def"] \\ intLib.COOPER_TAC
QED
val _ = word_cse_inttonum_side |> update_precondition;

val res = translate (word_cseTheory.word_cseInst_def);
val res = translate_no_ind (word_cseTheory.word_cse_def);

Theorem word_cse_ind[local]:
  word_cse_word_cse_ind
Proof
  rewrite_tac [fetch "-" "word_cse_word_cse_ind_def"]
  \\ rpt gen_tac \\ rpt disch_tac
  \\ ONCE_REWRITE_TAC [SWAP_FORALL_THM]
  \\ ho_match_mp_tac (wordLangTheory.max_var_ind
       |> Q.SPEC `λbits p. P p` |> SRULE [] |> Q.GEN `P`)
  \\ rpt strip_tac
  \\ last_x_assum irule
  \\ fs []
QED
val _ = word_cse_ind |> update_precondition;

val res = translate (word_cseTheory.word_common_subexp_elim_def);

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "word_cseTheory.word_common_subexp_elim_def.");

val res = translate (word_copyTheory.copy_prop_def);

val res = translate_no_ind miscTheory.anub_def;

Theorem misc_anub_ind[local]:
  misc_anub_ind (:'a) (:'b)
Proof
  once_rewrite_tac [fetch "-" "misc_anub_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ gvs [FORALL_PROD]
QED

val _ = misc_anub_ind |> update_precondition;

val res = translate (word_unreachTheory.remove_unreach_def);

val _ = translate (word_simpTheory.const_fp_inst_cs_def)

val _ = translate word_simpTheory.int_op_def;
val _ = translate word_simpTheory.int_unsigned_def;
val _ = translate word_simpTheory.int_signed_def;
val _ = translate word_simpTheory.int_sh_def;
Theorem int_unsigned_nonnegative[local,simp]:
  ∀bits i. 0 ≤ int_unsigned bits i
Proof
  rw [word_simpTheory.int_unsigned_def]
  \\ mp_tac (Q.SPECL [`i`,`&(2 ** bits)`] integerTheory.INT_MOD_BOUNDS)
  \\ simp []
QED

Theorem word_simp_int_sh_side[local]:
  ∀bits sh i j. word_simp_int_sh_side bits sh i j
Proof
  simp [fetch "-" "word_simp_int_sh_side_def", int_unsigned_nonnegative]
QED
val _ = update_precondition word_simp_int_sh_side;

val _ = translate word_simpTheory.int_cmp_def;

(* TODO: remove when pmatch is fixed *)
val _ = translate (word_simpTheory.const_fp_loop_def)

val _ = translate (word_simpTheory.is_simple_pmatch_def)
val _ = translate (word_simpTheory.dest_Raise_num_pmatch_def)
val _ = translate (word_simpTheory.try_if_hoist2_def)
val _ = translate (word_simpTheory.try_if_hoist1_def)
val _ = translate (word_simpTheory.Seq_assoc_def)
val _ = translate (word_simpTheory.simp_duplicate_if_def)

val _ = translate (word_simpTheory.compile_exp_def)

val _ = translate (wordLangTheory.max_var_inst_def)
val _ = translate (wordLangTheory.max_var_def)


val _ = translate (asmTheory.offset_ok_def |> SIMP_RULE (srw_ss()) [alignmentTheory.aligned_bitwise_and, integerTheory.INT_DIVIDES_MOD0])
val _ = translate (word_instTheory.is_Lookup_CurrHeap_pmatch)
val res = translate_no_ind (word_instTheory.inst_select_exp_pmatch |> SIMP_RULE std_ss [word_mul_def,word_2comp_def])

Theorem inst_select_exp_ind[local]:
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

val _ = translate (word_instTheory.op_consts_pmatch)

val _ = translate (word_instTheory.convert_sub_pmatch |> SIMP_RULE std_ss [word_2comp_def,word_mul_def])

val r = translate (word_instTheory.pull_exp_def(*_pmatch*)) (* TODO: MAP pull_exp inside pmatch seems to throw the translator into an infinite loop *)

val word_inst_pull_exp_side = Q.prove(`
  ∀x. word_inst_pull_exp_side x ⇔ T`,
  ho_match_mp_tac word_instTheory.pull_exp_ind>>rw[]>>
  simp[Once (fetch "-" "word_inst_pull_exp_side_def"),
      fetch "-" "word_inst_optimize_consts_side_def",
      word_simpTheory.int_op_def]>>
  metis_tac[]) |> update_precondition

val _ = translate (word_instTheory.inst_select_def(*pmatch*))

val _ = translate (word_allocTheory.list_next_var_rename_move_def)
val _ = translate word_allocTheory.force_rename_def

val _ = translate (word_allocTheory.ssa_reconcile_def);
val _ = translate (word_allocTheory.loop_setup_def);

val _ = translate (word_allocTheory.ssa_cc_trans_inst_def)
val _ = translate (word_allocTheory.full_ssa_cc_trans_def)

val _ = translate (word_allocTheory.remove_dead_inst_def)
val _ = translate (word_allocTheory.get_live_inst_def)
val _ = translate (word_allocTheory.get_live_def)
val _ = translate (word_allocTheory.remove_dead_def)
val _ = translate (word_allocTheory.remove_dead_prog_def)

Theorem lem[local]:
  dimindex(:64) = 64 ∧
  dimindex(:32) = 32
Proof
  EVAL_TAC
QED

val _ = translate (word_allocTheory.get_forced_pmatch
                  |> SIMP_RULE (bool_ss++ARITH_ss) [lem])

val _ = translate (word_allocTheory.get_delta_inst_def)
val _ = translate (word_allocTheory.get_clash_tree_def)
val _ = translate (wordLangTheory.every_var_inst_def)
val _ = translate word_allocTheory.select_reg_alloc_def
val _ = translate ( word_allocTheory.word_alloc_def)

val _ = translate word_instTheory.three_to_two_reg_def;
val _ = translate word_instTheory.three_to_two_reg_prog_def;
val _ = translate word_removeTheory.remove_must_terminate_def;
val _ = translate word_to_wordTheory.compile_alt;

val _ = translate(data_to_wordTheory.FromList_code_def )
val _ = translate(data_to_wordTheory.FromList1_code_def |> inline_simp)
val _ = translate(data_to_wordTheory.MakeBytes_def)
val _ = translate(data_to_wordTheory.WriteLastByte_aux_def)
val _ = translate(data_to_wordTheory.WriteLastBytes_def)
val _ = translate(data_to_wordTheory.RefByte_code_def |> inline_simp |> SIMP_RULE std_ss[data_to_wordTheory.SmallLsr_def])
val _ = translate(data_to_wordTheory.RefArray_code_def |> inline_simp)
val _ = translate(data_to_wordTheory.Replicate_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.AddNumSize_def)
val _ = translate(data_to_wordTheory.AnyHeader_def|> inline_simp)
val _ = translate(data_to_wordTheory.AnyArith_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.Add_code_def)
val _ = translate(data_to_wordTheory.Sub_code_def)
val _ = translate(data_to_wordTheory.Mul_code_def)
val _ = translate(data_to_wordTheory.Div_code_def)
val _ = translate(data_to_wordTheory.Mod_code_def)
val _ = translate(data_to_wordTheory.MemCopy_code_def|> inline_simp)
val r = translate(data_to_wordTheory.ByteCopy_code_def |> inline_simp)
val r = translate(data_to_wordTheory.ByteCopyAdd_code_def)
val r = translate(data_to_wordTheory.ByteCopySub_code_def )
val r = translate(data_to_wordTheory.ByteCopyNew_code_def)

val r = translate(data_to_wordTheory.Install_code_def |> inline_simp)
val r = translate(data_to_wordTheory.InstallData_code_def |> inline_simp)

val _ = translate(data_to_wordTheory.Append_code_def|> inline_simp   |> SIMP_RULE std_ss [])
val _ = translate(data_to_wordTheory.AppendMainLoop_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.AppendLenLoop_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.XorLoop_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.StringCmpLoop_code_def|> inline_simp)

val _ = translate(data_to_wordTheory.Compare1_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.Compare_code_def|> inline_simp)

val _ = translate(data_to_wordTheory.Equal1_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.Equal_code_def|> inline_simp |> SIMP_RULE std_ss [backend_commonTheory.closure_tag_def,backend_commonTheory.partial_app_tag_def])


val _ = translate(data_to_wordTheory.LongDiv1_code_def|> inline_simp )
val _ = translate(data_to_wordTheory.LongDiv_code_def|> inline_simp)

val _ = translate (word_bignumTheory.generated_bignum_stubs_eq |> inline_simp)

val _ = translate data_to_wordTheory.stub_names_def
val _ = translate word_to_stackTheory.stub_names_def
val _ = translate stack_allocTheory.stub_names_def
val _ = translate stack_removeTheory.stub_names_def
val res = translate (data_to_wordTheory.compile_def
                     |> SIMP_RULE std_ss [data_to_wordTheory.stubs_md_def, data_to_wordTheory.stubs_def, loc_values]
                     );

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "data_to_wordTheory.compile_def.");

(* explorer specific functions *)

val r = presLangTheory.num_to_hex_def |> translate;
val r = presLangTheory.word_to_display_def |> translate;
val r = presLangTheory.item_with_word_def |> translate;
val r = presLangTheory.asm_binop_to_display_def |> translate;
val r = presLangTheory.asm_reg_imm_to_display_def |> translate;
val r = presLangTheory.asm_arith_to_display_def |> translate;
val r = presLangTheory.store_name_to_display_def |> translate
val r = presLangTheory.word_exp_to_display_def |> translate
val r = presLangTheory.asm_inst_to_display_def |> translate;
val r = presLangTheory.ws_to_display_def |> translate
val r = presLangTheory.word_seqs_def |> translate

val r = presLangTheory.word_prog_to_display_def

          |> REWRITE_RULE [presLangTheory.string_imp_def]
          |> translate

val r = presLangTheory.word_fun_to_display_def |> translate


val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);
