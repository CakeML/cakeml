(*
  Translate the backend from dataLang to target code.
*)
Theory from_dataProg[no_sig_docs]
Ancestors
  ml_translator from_wordProg std_prelude data_to_word backend[qualified]
Libs
  preamble ml_translatorLib blastLib[qualified]

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "from_wordProg";
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_dataProg");

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

val inline_simp = SIMP_RULE std_ss [backend_commonTheory.word_shift_def];
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
(* add_Dlet only accepts top-level vals whose code does not call functions
   (no_ptr_eq), so the call to adjust_sets is evaluated away *)
val _ = translate (data_to_wordTheory.GiveUp_def
                   |> REWRITE_RULE [EVAL “adjust_sets (LN:num_set)”]);
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

val _ = translate data_to_wordTheory.SmallnumCompare_def;
val _ = translate data_to_wordTheory.SmallnumMul_def;
val _ = translate data_to_wordTheory.SmallnumDivLoop_def;
val _ = translate data_to_wordTheory.SmallnumUnsignedDiv_def;
val _ = translate data_to_wordTheory.SmallnumDivMod_def;
val _ = translate (data_to_wordTheory.SmallnumDivCall_def
                   |> SIMP_RULE std_ss [loc_values]);
val _ = translate data_to_wordTheory.SmallnumDiv_def;

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
val _ = translate(data_to_wordTheory.SmallnumDivMod_code_def)
val _ = translate(data_to_wordTheory.MemCopy_code_def|> inline_simp)
val r = translate(data_to_wordTheory.ByteCopyWords_code_def)
val r = translate(data_to_wordTheory.ByteCopyShiftWords_code_def)
val r = translate(data_to_wordTheory.ByteCopyLoop_code_def |> inline_simp)
val r = translate(data_to_wordTheory.ByteCopyAlign_code_def |> inline_simp)
val r = translate(data_to_wordTheory.ByteCopy_code_def |> inline_simp)
(* top-level vals must not call functions (no_ptr_eq), so unfold list_Seq *)
val r = translate(data_to_wordTheory.ByteCopyAdd_code_def
                  |> REWRITE_RULE [data_to_wordTheory.list_Seq_def])
val r = translate(data_to_wordTheory.ByteCopySub_code_def
                  |> REWRITE_RULE [data_to_wordTheory.list_Seq_def])
val r = translate(data_to_wordTheory.ByteCopyNewInit_code_def |> inline_simp)
val r = translate(data_to_wordTheory.ByteCopyNew_code_def)

val r = translate(data_to_wordTheory.Install_code_def |> inline_simp)
val r = translate(data_to_wordTheory.InstallData_code_def |> inline_simp)

val _ = translate(data_to_wordTheory.Append_code_def|> inline_simp   |> SIMP_RULE std_ss [])
val _ = translate(data_to_wordTheory.AppendMainLoop_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.AppendLenLoop_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.XorLoop_code_def|> inline_simp)
val _ = translate(data_to_wordTheory.StringCmpLoop_code_def|> inline_simp)

val _ = translate data_to_wordTheory.ScanByte_step_def;
val _ = translate (data_to_wordTheory.ScanByte_tail_code_def |> SRULE [LET_THM]);
val _ = translate (data_to_wordTheory.ScanByte_word_body_def |> SRULE [LET_THM]);
val _ = translate (data_to_wordTheory.ScanByte_bulk_def |> SRULE [LET_THM]);
val _ = translate (data_to_wordTheory.ScanByte_code_def |> SRULE [LET_THM]);
val _ = translate data_to_wordTheory.ScanEq_code_def;
val _ = translate data_to_wordTheory.ScanNeq_code_def;

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

val _ = translate backendTheory.from_data_def;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
