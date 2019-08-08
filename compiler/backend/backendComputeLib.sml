(*
  A compset for evaluating the compiler backend inside the logic of HOL.
*)
structure backendComputeLib :> backendComputeLib =
struct

local

open HolKernel boolLib bossLib computeLib
open semanticsComputeLib reg_allocComputeLib
open backendTheory

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars (merge_grammars ["backend"])
end

open Parse

fun theory_computes thy
  = ThmSetData.theory_data {settype = "compute", thy = thy}
    |> ThmSetData.added_thms
in

val add_backend_compset = computeLib.extend_compset
  [computeLib.Tys
    [ (* ---- configurations ---- *)
     ``:source_to_flat$config``
    ,``:clos_to_bvl$config``
    ,``:bvl_to_bvi$config``
    ,``:data_to_word$config``
    ,``:word_to_word$config``
    ,``:'a word_to_stack$config``
    ,``:stack_to_lab$config``
    ,``:'a lab_to_target$config``
    ,``:'a asm_config``
    ,``:'a backend$config``
    ]

  ,computeLib.Defs
    [ (* --- backend_common --- *)
     backend_commonTheory.bind_tag_def
    ,backend_commonTheory.chr_tag_def
    ,backend_commonTheory.div_tag_def
    ,backend_commonTheory.subscript_tag_def
    ,backend_commonTheory.false_tag_def
    ,backend_commonTheory.true_tag_def
    ,backend_commonTheory.nil_tag_def
    ,backend_commonTheory.cons_tag_def
    ,backend_commonTheory.none_tag_def
    ,backend_commonTheory.some_tag_def
    ,backend_commonTheory.tuple_tag_def
    ,backend_commonTheory.closure_tag_def
    ,backend_commonTheory.partial_app_tag_def
    ,backend_commonTheory.clos_tag_shift_def
    ,backend_commonTheory.orphan_trace_def
    ,backend_commonTheory.mk_cons_def
    ,backend_commonTheory.mk_union_def
    ,backend_commonTheory.bool_to_tag_def
    ,backend_commonTheory.stack_num_stubs_def
    ,backend_commonTheory.word_num_stubs_def
    ,backend_commonTheory.data_num_stubs_def
    ,backend_commonTheory.bvl_num_stubs_def
    ,backend_commonTheory.bvl_to_bvi_namespaces_def
    ,backend_commonTheory.small_enough_int_def
    ]
  ,computeLib.Tys
    [``:backend_common$tra``
    ]

  ,computeLib.Defs
    [ (* ---- source_to_flat ---- *)
     flatLangTheory.bool_id_def
    ,flatLangTheory.Bool_def
    ]
  ,computeLib.Defs (theory_computes "source_to_flat")
      (* ---- flat_elim ---- *)
  ,computeLib.Defs (theory_computes "flat_elim")
  ,computeLib.Tys
    [``:flatLang$op``
    ,``:flatLang$pat``
    ,``:flatLang$exp``
    ,``:flatLang$dec``
    ,``:source_to_flat$environment``
    ,``:source_to_flat$next_indices``
    ,``:source_to_flat$config``
    ]

  ,computeLib.Defs (theory_computes "flat_reorder_match")

  ,computeLib.Defs (theory_computes "flat_exh_match")

  ,computeLib.Defs (theory_computes "flat_uncheck_ctors")

  ,computeLib.Tys
    [ (* ---- patLang ---- *)
     ``:patLang$exp``
    ,``:patLang$op``
    ]

      (* ---- flat_to_pat ---- *)
  ,computeLib.Defs
    [flat_to_patTheory.Bool_def
    ,flat_to_patTheory.isBool_def
    ,flat_to_patTheory.sIf_def
    ,flat_to_patTheory.pure_op_op_eqn (* could put this in the compute set and avoid listing explicitly *)
    ,flat_to_patTheory.pure_op_def
    ,flat_to_patTheory.pure_def
    ,flat_to_patTheory.ground_def
    ,flat_to_patTheory.sLet_def
    ,flat_to_patTheory.Let_Els_def_compute
    ,flat_to_patTheory.compile_pat_def
    ,flat_to_patTheory.compile_row_def
    ,flat_to_patTheory.compile_exp_def
    ,flat_to_patTheory.compile_def
    ]

  ,computeLib.Tys
    [ (* ---- closLang ---- *)
     ``:closLang$exp``
    ,``:closLang$op``
    ,``:clos_known$val_approx``
    ,``:clos_known$globalOpt``
    ,``:clos_known$inliningDecision``
    ,``:clos_known$config``
    ]
  ,computeLib.Defs
    [closLangTheory.pure_def
    ,closLangTheory.pure_op_def
      (* ---- pat_to_clos ---- *)
    ,pat_to_closTheory.dest_WordToInt_def
    ,pat_to_closTheory.CopyByteStr_def
    ,pat_to_closTheory.CopyByteAw8_def
    ,pat_to_closTheory.vector_tag_def
    ,pat_to_closTheory.compile_def
      (*,pat_to_closTheory.pat_tag_shift_def*)
      (* ---- clos_mti ---- *)
    ,clos_mtiTheory.intro_multi_def
    ,clos_mtiTheory.collect_args_def
    ,clos_mtiTheory.collect_apps_def
    ,clos_mtiTheory.compile_def
      (* ---- clos_number ---- *)
    ,clos_numberTheory.renumber_code_locs_def
    ]
  ,computeLib.Defs
    [clos_callTheory.calls_def
    ,clos_callTheory.free_def
    ,clos_callTheory.closed_def
    ,clos_callTheory.code_list_def
    ,clos_callTheory.compile_def
    ,clos_callTheory.calls_list_def
    ,clos_callTheory.insert_each_def_compute
    ,clos_callTheory.GENLIST_Var_def
      (* ---- clos_annotate ---- *)
    ,clos_annotateTheory.get_var_def
    ,clos_annotateTheory.shifted_env_def
    ,clos_annotateTheory.annotate_def
    ,clos_annotateTheory.shift_def
    ,clos_annotateTheory.compile_def
    ,clos_annotateTheory.const_0_def
    ,clos_annotateTheory.no_overlap_def_compute
    ,clos_annotateTheory.alt_free_def
      (* ---- clos_known---- *)
    ,clos_knownTheory.get_size_sc_aux_def
    ,clos_knownTheory.get_size_sc_def
    ,clos_knownTheory.get_size_aux_def
    ,clos_knownTheory.get_size_def
    ,clos_knownTheory.free_def
    ,clos_knownTheory.closed_def
    ,clos_knownTheory.contains_closures_def
    ,clos_knownTheory.decide_inline_def
    ,clos_knownTheory.merge_def
    ,clos_knownTheory.known_op_def
    ,clos_knownTheory.clos_gen_noinline_def
    ,clos_knownTheory.isGlobal_def
    ,clos_knownTheory.gO_destApx_def
    ,clos_knownTheory.mk_Ticks_def
    ,clos_knownTheory.dec_inline_factor_def
    ,clos_knownTheory.known_def
    ,clos_knownTheory.compile_def
    ,clos_knownTheory.clos_approx_def
      (* ---- clos_ticks---- *)
    ,clos_ticksTheory.remove_ticks_def
      (* ---- clos_letop---- *)
    ,clos_letopTheory.var_list_def
    ,clos_letopTheory.dest_op_def
    ,clos_letopTheory.let_op_def
    ]
  ,computeLib.Defs (theory_computes "clos_fvs")
  ,computeLib.Tys
    [ (* ---- bvl ---- *)
     ``:bvl$exp``
    ]
  ,computeLib.Defs
    [ (* ---- clos_to_bvl ---- *)
     backend_commonTheory.closure_tag_def
    ,backend_commonTheory.clos_tag_shift_def
    ,backend_commonTheory.partial_app_tag_def
    ,backend_commonTheory.bool_to_tag_def
    ,bvlTheory.mk_tick_def
    ,bvlTheory.Bool_def
    ,clos_to_bvlTheory.recc_Let0_def
    ,clos_to_bvlTheory.partial_app_fn_location_def
    ,clos_to_bvlTheory.default_config_def
    ,clos_to_bvlTheory.chain_exps_def
    ,clos_to_bvlTheory.compile_common_def
    ,clos_to_bvlTheory.compile_def
    ,clos_to_bvlTheory.compile_prog_def
    ,clos_to_bvlTheory.init_code_def
    ,clos_to_bvlTheory.check_closure_def
    ,clos_to_bvlTheory.generic_app_fn_location_def
    ,clos_to_bvlTheory.generate_partial_app_closure_fn_def
    ,clos_to_bvlTheory.generate_generic_app_def
    ,clos_to_bvlTheory.num_added_globals_def
    ,clos_to_bvlTheory.partial_app_label_table_loc_def
    ,clos_to_bvlTheory.partial_app_fn_location_code_def
    ,clos_to_bvlTheory.init_globals_def
    ,clos_to_bvlTheory.mk_cl_call_def
    ,clos_to_bvlTheory.num_stubs_def
    ,clos_to_bvlTheory.build_recc_lets_def
    ,clos_to_bvlTheory.recc_Let_def
    ,clos_to_bvlTheory.recc_Lets_def
    ,clos_to_bvlTheory.mk_el_def
    ,clos_to_bvlTheory.build_aux_def
    ,clos_to_bvlTheory.code_for_recc_case_def
    ,clos_to_bvlTheory.free_let_def
    ,clos_to_bvlTheory.mk_label_def
    ,clos_to_bvlTheory.compile_op_def
    ,clos_to_bvlTheory.mk_const_def
    ,bvlTheory.Bool_def
    ,clos_to_bvlTheory.compile_exps_def
    ,clos_to_bvlTheory.code_merge_def
    ,clos_to_bvlTheory.code_split_def
    ,clos_to_bvlTheory.code_sort_def
      (* ---- bvl_inline ---- *)
    ,bvl_inlineTheory.tick_inline_def
    ,bvl_inlineTheory.is_small_aux_def
    ,bvl_inlineTheory.is_small_def
    ,bvl_inlineTheory.is_rec_def
    ,bvl_inlineTheory.must_inline_def
    ,bvl_inlineTheory.tick_inline_all_def
    ,bvl_inlineTheory.tick_compile_prog_def
    ,bvl_inlineTheory.remove_ticks_def
    ,bvl_inlineTheory.var_list_def
    ,bvl_inlineTheory.dest_op_def
    ,bvl_inlineTheory.let_op_def
    ,bvl_inlineTheory.let_op_sing_def
    ,bvl_inlineTheory.optimise_def
    ,bvl_inlineTheory.compile_inc_def
    ,bvl_inlineTheory.compile_prog_def
      (* ---- bvl_const ---- *)
    ,bvl_constTheory.dest_simple_def
    ,bvl_constTheory.case_op_const_def
    ,bvl_constTheory.SmartOp_flip_def
    ,bvl_constTheory.SmartOp2_def
    ,bvl_constTheory.SmartOp_def
    ,bvl_constTheory.extract_def
    ,bvl_constTheory.extract_list_def
    ,bvl_constTheory.delete_var_def
    ,bvl_constTheory.compile_def
    ,bvl_constTheory.compile_exp_def
      (* ---- bvl_handle ---- *)
    ,bvl_handleTheory.LetLet_def
    ,bvl_handleTheory.SmartLet_def
    ,bvl_handleTheory.OptionalLetLet_def
    ,bvl_handleTheory.compile_def
    ,bvl_handleTheory.compile_exp_def
    ,bvl_handleTheory.dest_Seq_def
    ,bvl_handleTheory.compile_seqs_compute
    ,bvl_handleTheory.compile_any_def
      (* ---- bvl_jump ---- *)
    ,bvl_jumpTheory.JumpList_def
    ,bvl_jumpTheory.Jump_def
    ]
  ,computeLib.Tys
    [ (* ---- bvi ---- *)
     ``:bvi$exp``
    ,``:bvi_tailrec$assoc_op``
    ,``:bvi_tailrec$v_ty``
    ]
  ,computeLib.Defs
    [ (* ---- bvl_to_bvi ---- *)
     bvl_to_bviTheory.destLet_def
    ,bvl_to_bviTheory.alloc_glob_count_def
    ,bvl_to_bviTheory.compile_prog_def
    ,bvl_to_bviTheory.compile_list_def
    ,bvl_to_bviTheory.compile_single_def
    ,bvl_to_bviTheory.compile_def
    ,bvl_to_bviTheory.compile_op_def
    ,bvl_to_bviTheory.stubs_def
    ,bvl_to_bviTheory.CopyGlobals_code_def
    ,bvl_to_bviTheory.AllocGlobal_code_def
    ,bvl_to_bviTheory.InitGlobals_code_def
    ,bvl_to_bviTheory.ListLength_code_def
    ,bvl_to_bviTheory.FromListByte_code_def
    ,bvl_to_bviTheory.ToListByte_code_def
    ,bvl_to_bviTheory.SumListLength_code_def
    ,bvl_to_bviTheory.ConcatByte_code_def
    ,bvl_to_bviTheory.CopyGlobals_location_eq
    ,bvl_to_bviTheory.AllocGlobal_location_eq
    ,bvl_to_bviTheory.InitGlobals_max_def
    ,bvl_to_bviTheory.InitGlobals_location_eq
    ,bvl_to_bviTheory.ListLength_location_eq
    ,bvl_to_bviTheory.FromListByte_location_eq
    ,bvl_to_bviTheory.ToListByte_location_eq
    ,bvl_to_bviTheory.SumListLength_location_eq
    ,bvl_to_bviTheory.ConcatByte_location_eq
    ,bvl_to_bviTheory.compile_int_def
    ,bvl_to_bviTheory.compile_exps_def
    ,bvl_to_bviTheory.compile_aux_def
    ,bvl_to_bviTheory.default_config_def
      (* ---- bvi_let ---- *)
    ,bvi_letTheory.extract_def
    ,bvi_letTheory.extract_list_def
    ,bvi_letTheory.delete_var_def
    ,bvi_letTheory.compile_def
    ,bvi_letTheory.compile_exp_def
      (* ---- bvi_tailrec ---- *)
    ,bvi_tailrecTheory.dummy_def
    ,bvi_tailrecTheory.small_int_def
    ,bvi_tailrecTheory.is_rec_def
    ,bvi_tailrecTheory.is_const_def
    ,bvi_tailrecTheory.op_type_def
    ,bvi_tailrecTheory.to_op_def
    ,bvi_tailrecTheory.from_op_def
    ,bvi_tailrecTheory.op_eq_def
    ,bvi_tailrecTheory.apply_op_def
    ,bvi_tailrecTheory.id_from_op_def
    ,bvi_tailrecTheory.index_of_def
    ,bvi_tailrecTheory.args_from_def
    ,bvi_tailrecTheory.get_bin_args_def
    ,bvi_tailrecTheory.opbinargs_def
    ,bvi_tailrecTheory.try_update_def
    ,bvi_tailrecTheory.is_arith_def
    ,bvi_tailrecTheory.is_rel_def
    ,bvi_tailrecTheory.term_ok_int_def
    ,bvi_tailrecTheory.term_ok_any_def
    ,bvi_tailrecTheory.term_ok_def
    ,bvi_tailrecTheory.try_swap_def
    ,bvi_tailrecTheory.check_op_def
    ,bvi_tailrecTheory.decide_ty_def
    ,bvi_tailrecTheory.LAST1_def
    ,bvi_tailrecTheory.update_context_def
    ,bvi_tailrecTheory.arg_ty_def
    ,bvi_tailrecTheory.op_ty_def
    ,bvi_tailrecTheory.scan_expr_def
    ,bvi_tailrecTheory.push_call_def
    ,bvi_tailrecTheory.rewrite_def
    ,bvi_tailrecTheory.has_rec_def
    ,bvi_tailrecTheory.has_rec1_def
    ,bvi_tailrecTheory.check_exp_def
    ,bvi_tailrecTheory.let_wrap_def
    ,bvi_tailrecTheory.mk_aux_call_def
    ,bvi_tailrecTheory.compile_exp_def
    ,bvi_tailrecTheory.compile_prog_def
    ]
  ,computeLib.Tys
    [ (* ---- data ---- *)
     ``:dataLang$prog``
      (* ---- data_to_word ---- *)
    ,``:data_to_word$word_op_type``
    ,``:data_to_word$gc_kind``
    ]
  ,computeLib.Defs
    [dataLangTheory.mk_ticks_def
    ,dataLangTheory.op_space_reset_def
      (* ---- bvi_to_data ---- *)
    ,bvi_to_dataTheory.op_requires_names_eqn
    ,bvi_to_dataTheory.optimise_def
    ,bvi_to_dataTheory.compile_prog_def
    ,bvi_to_dataTheory.compile_part_def
    ,bvi_to_dataTheory.compile_exp_def
    ,bvi_to_dataTheory.compile_def
    ,bvi_to_dataTheory.iAssign_def
      (* ---- data_simp ---- *)
    ,data_simpTheory.pSeq_def
    ,data_simpTheory.simp_def
      (* ---- data_space ---- *)
    ,data_spaceTheory.pMakeSpace_def
    ,data_spaceTheory.space_def
    ,data_spaceTheory.op_space_req_def
    ,data_spaceTheory.compile_def
      (* ---- data_live ---- *)
    ,data_liveTheory.is_pure_def
    ,data_liveTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* wordLang *)
     ``:'a wordLang$exp``
    ,``:'a wordLang$prog``
      (* word_bignum *)
    ,``:word_bignum$address``
    ,``:'a word_bignum$mini``
    ]
  ,computeLib.Defs
    [wordLangTheory.every_var_exp_def
    ,wordLangTheory.word_sh_def
    ,wordLangTheory.word_op_def
    ,wordLangTheory.every_var_imm_def
    ,wordLangTheory.every_stack_var_def
    ,wordLangTheory.every_var_def
    ,wordLangTheory.every_name_def
    ,wordLangTheory.every_var_inst_def
    ,wordLangTheory.max_var_def
    ,wordLangTheory.max_var_inst_def
    ,wordLangTheory.max_var_exp_def
    ,wordLangTheory.raise_stub_location_eq
      (* ---- data_to_word ---- *)
    ,data_to_wordTheory.adjust_var_def
    ,data_to_wordTheory.adjust_set_def
    ,data_to_wordTheory.Unit_def
    ,data_to_wordTheory.GiveUp_def
    ,data_to_wordTheory.BignumHalt_def
    ,data_to_wordTheory.make_header_def
    ,data_to_wordTheory.tag_mask_def
    ,data_to_wordTheory.encode_header_def
    ,data_to_wordTheory.list_Seq_def
    ,data_to_wordTheory.StoreEach_def
    ,data_to_wordTheory.small_shift_length_def
    ,data_to_wordTheory.shift_length_def
    ,data_to_wordTheory.max_heap_limit_def
    ,data_to_wordTheory.all_ones_def
    ,data_to_wordTheory.maxout_bits_def
    ,data_to_wordTheory.ptr_bits_def
    ,data_to_wordTheory.real_addr_def
    ,data_to_wordTheory.real_offset_def
    ,data_to_wordTheory.real_byte_offset_def
    ,data_to_wordTheory.lookup_word_op_def
    ,data_to_wordTheory.FromList_location_eq
    ,data_to_wordTheory.FromList1_location_eq
    ,data_to_wordTheory.RefByte_location_eq
    ,data_to_wordTheory.RefArray_location_eq
    ,data_to_wordTheory.Replicate_location_eq
    ,data_to_wordTheory.AnyArith_location_eq
    ,data_to_wordTheory.Add_location_eq
    ,data_to_wordTheory.Sub_location_eq
    ,data_to_wordTheory.Mul_location_eq
    ,data_to_wordTheory.Div_location_eq
    ,data_to_wordTheory.Mod_location_eq
    ,data_to_wordTheory.Compare1_location_eq
    ,data_to_wordTheory.Compare_location_eq
    ,data_to_wordTheory.Equal1_location_eq
    ,data_to_wordTheory.Equal_location_eq
    ,data_to_wordTheory.LongDiv1_location_eq
    ,data_to_wordTheory.LongDiv_location_eq
    ,data_to_wordTheory.MemCopy_location_eq
    ,data_to_wordTheory.Dummy_location_eq
    ,data_to_wordTheory.Install_location_eq
    ,data_to_wordTheory.InstallCode_location_eq
    ,data_to_wordTheory.InstallData_location_eq
    ,data_to_wordTheory.Append_location_eq
    ,data_to_wordTheory.AppendMainLoop_location_eq
    ,data_to_wordTheory.AppendLenLoop_location_eq
    ,data_to_wordTheory.AppendFastLoop_location_eq
    ,data_to_wordTheory.Bignum_location_eq
    ,data_to_wordTheory.ByteCopy_location_eq
    ,data_to_wordTheory.ByteCopyAdd_location_eq
    ,data_to_wordTheory.ByteCopySub_location_eq
    ,data_to_wordTheory.ByteCopyNew_location_eq
    ,data_to_wordTheory.Bignum_location_eq
    ,data_to_wordTheory.get_gen_size_def
    ,data_to_wordTheory.SilentFFI_def
    ,data_to_wordTheory.AllocVar_def
    ,data_to_wordTheory.MakeBytes_def
    ,data_to_wordTheory.WriteLastByte_aux_def
    ,data_to_wordTheory.WriteLastBytes_def
    ,data_to_wordTheory.SmallLsr_def
    ,data_to_wordTheory.RefByte_code_def
    ,data_to_wordTheory.Maxout_bits_code_def
    ,data_to_wordTheory.Make_ptr_bits_code_def
    ,data_to_wordTheory.FromList_code_def
    ,data_to_wordTheory.FromList1_code_def
    ,data_to_wordTheory.RefArray_code_def
    ,data_to_wordTheory.Replicate_code_def
    ,data_to_wordTheory.AnyArith_code_def
    ,data_to_wordTheory.Add_code_def
    ,data_to_wordTheory.Sub_code_def
    ,data_to_wordTheory.Mul_code_def
    ,data_to_wordTheory.Div_code_def
    ,data_to_wordTheory.Mod_code_def
    ,data_to_wordTheory.Install_code_def
    ,data_to_wordTheory.InstallCode_code_def
    ,data_to_wordTheory.InstallData_code_def
    ,data_to_wordTheory.Append_code_def
    ,data_to_wordTheory.AppendMainLoop_code_def
    ,data_to_wordTheory.AppendLenLoop_code_def
    ,data_to_wordTheory.AppendFastLoop_code_def
    ,data_to_wordTheory.Compare1_code_def
    ,data_to_wordTheory.Compare_code_def
    ,data_to_wordTheory.Equal1_code_def
    ,data_to_wordTheory.Equal_code_def
    ,data_to_wordTheory.LongDiv_code_def
    ,data_to_wordTheory.LongDiv1_code_def
    ,data_to_wordTheory.MemCopy_code_def
    ,data_to_wordTheory.ByteCopy_code_def
    ,data_to_wordTheory.ByteCopyAdd_code_def
    ,data_to_wordTheory.ByteCopySub_code_def
    ,data_to_wordTheory.ByteCopyNew_code_def
    ,data_to_wordTheory.get_names_def
    ,data_to_wordTheory.LoadWord64_def
    ,data_to_wordTheory.LoadBignum_def
    ,data_to_wordTheory.WriteWord64_def
    ,data_to_wordTheory.WriteWord64_on_32_def
    ,data_to_wordTheory.WriteWord32_on_32_def
    ,data_to_wordTheory.WordOp64_on_32_def
    ,data_to_wordTheory.WordShift64_on_32_def
    ,data_to_wordTheory.ShiftVar_def
    ,data_to_wordTheory.AnyHeader_def
    ,data_to_wordTheory.AddNumSize_def
    ,multiwordTheory.n2mw_def
    ,multiwordTheory.i2mw_def
    ,data_to_wordTheory.bignum_words_def
    ,data_to_wordTheory.Smallnum_def
    ,data_to_wordTheory.MemEqList_def
    ,data_to_wordTheory.arg1_def
    ,data_to_wordTheory.arg2_def
    ,data_to_wordTheory.arg3_def
    ,data_to_wordTheory.arg4_def
    ,data_to_wordTheory.all_assign_defs
    ,data_to_wordTheory.assign_def
    ,data_to_wordTheory.fp_cmp_inst_def
    ,data_to_wordTheory.fp_bop_inst_def
    ,data_to_wordTheory.fp_uop_inst_def
    ,data_to_wordTheory.comp_def
    ,data_to_wordTheory.compile_part_def
    ,data_to_wordTheory.stubs_def
    ,data_to_wordTheory.compile_def
      (* word_bignum *)
    ,word_bignumTheory.mc_cmp_code_def
    ,word_bignumTheory.mc_sub_loop2_code_def
    ,word_bignumTheory.generated_bignum_stubs_def
    ,word_bignumTheory.compile_def
    ,word_bignumTheory.DivCode_def
    ,word_bignumTheory.div_location_def
    ,word_bignumTheory.SeqIndex_def
    ,word_bignumTheory.SeqTempImmNot_def
    ,word_bignumTheory.SeqTempImm_def
    ,word_bignumTheory.SeqTemp_def
    ,word_bignumTheory.TempOut_def
    ,word_bignumTheory.TempIn2_def
    ,word_bignumTheory.TempIn1_def
    ,word_bignumTheory.compile_exp_def
    ,word_bignumTheory.install_def
    ,word_bignumTheory.code_acc_next_def
    ,word_bignumTheory.has_compiled_def
    ,word_bignumTheory.mc_iop_code_def
    ,word_bignumTheory.mc_isub_flip_code_def
    ,word_bignumTheory.mc_imul_code_def
    ,word_bignumTheory.mc_mul_code_def
    ,word_bignumTheory.mc_mul_pass_code_def
    ,word_bignumTheory.mc_imul1_code_def
    ,word_bignumTheory.mc_iadd_code_def
    ,word_bignumTheory.mc_sub_code_def
    ,word_bignumTheory.mc_sub_loop_code_def
    ,word_bignumTheory.mc_sub1_code_def
    ,word_bignumTheory.mc_sub_loop1_code_def
    ,word_bignumTheory.mc_iadd2_code_def
    ,word_bignumTheory.mc_iadd3_code_def
    ,word_bignumTheory.mc_add_code_def
    ,word_bignumTheory.mc_add_loop_code_def
    ,word_bignumTheory.mc_add_loop2_code_def
    ,word_bignumTheory.mc_add_loop1_code_def
    ,word_bignumTheory.mc_iadd1_code_def
    ,word_bignumTheory.mc_idiv_code_def
    ,word_bignumTheory.mc_idiv0_code_def
    ,word_bignumTheory.mc_idiv_mod_header_code_def
    ,word_bignumTheory.mc_div_sub_call_code_def
    ,word_bignumTheory.mc_div_sub1_code_def
    ,word_bignumTheory.mc_div_sub_aux_code_def
    ,word_bignumTheory.mc_div_sub_aux1_code_def
    ,word_bignumTheory.mc_add1_call_code_def
    ,word_bignumTheory.mc_add1_code_def
    ,word_bignumTheory.mc_div_code_def
    ,word_bignumTheory.mc_div3_code_def
    ,word_bignumTheory.mc_div2_code_def
    ,word_bignumTheory.mc_copy_down_code_def
    ,word_bignumTheory.mc_fix_code_def
    ,word_bignumTheory.mc_simple_div1_code_def
    ,word_bignumTheory.mc_div_loop_code_def
    ,word_bignumTheory.mc_div_sub_loop_code_def
    ,word_bignumTheory.mc_div_sub_code_def
    ,word_bignumTheory.mc_div_adjust_code_def
    ,word_bignumTheory.mc_adjust_aux_code_def
    ,word_bignumTheory.mc_adj_cmp_code_def
    ,word_bignumTheory.mc_div_guess_code_def
    ,word_bignumTheory.mc_div_test_code_def
    ,word_bignumTheory.mc_cmp2_code_def
    ,word_bignumTheory.mc_top_two_code_def
    ,word_bignumTheory.mc_cmp_mul2_code_def
    ,word_bignumTheory.mc_cmp3_code_def
    ,word_bignumTheory.mc_mul_by_single2_code_def
    ,word_bignumTheory.mc_div_r1_code_def
    ,word_bignumTheory.mc_single_mul_add_code_def
    ,word_bignumTheory.mc_single_mul_code_def
    ,word_bignumTheory.mc_mul_by_single_code_def
    ,word_bignumTheory.mc_simple_div_code_def
    ,word_bignumTheory.mc_calc_d_code_def
    ,word_bignumTheory.mc_div1_code_def
    ,word_bignumTheory.mc_single_div_code_def
    ,word_bignumTheory.mc_div0_code_def
    ,word_bignumTheory.mc_compare_code_def
    ,word_bignumTheory.mc_copy_over_code_def
    ,word_bignumTheory.mc_mul_zero_code_def
      (* ---- wordLang word_to_word ---- *)
    ,word_to_wordTheory.compile_single_def
    ,word_to_wordTheory.full_compile_single_def
    ,word_to_wordTheory.next_n_oracle_def
    ,word_to_wordTheory.compile_def
      (* ---- wordLang word_simp ---- *)
    ,word_simpTheory.SmartSeq_def
    ,word_simpTheory.Seq_assoc_def
    ,word_simpTheory.dest_Seq_def
    ,word_simpTheory.dest_If_def
    ,word_simpTheory.dest_If_Eq_Imm_def
    ,word_simpTheory.dest_Seq_Assign_Const_def
    ,word_simpTheory.apply_if_opt_def
    ,word_simpTheory.simp_if_def
    ,word_simpTheory.strip_const_def
    ,word_simpTheory.const_fp_exp_def
    ,word_simpTheory.const_fp_move_cs_def
    ,word_simpTheory.const_fp_inst_cs_def
    ,word_simpTheory.get_var_imm_cs_def
    ,word_simpTheory.is_gc_const_def
    ,word_simpTheory.const_fp_loop_def
    ,word_simpTheory.const_fp_def
    ,word_simpTheory.compile_exp_def
      (* ---- wordLang remove must terminate ---- *)
    ,word_removeTheory.remove_must_terminate_def
      (* ---- wordLang inst_select and inst flattening ---- *)
    ,word_instTheory.three_to_two_reg_def
    ,word_instTheory.pull_exp_def
    ,word_instTheory.inst_select_def
    ,word_instTheory.inst_select_exp_def
    ,word_instTheory.flatten_exp_def
    ,word_instTheory.op_consts_def
    ,word_instTheory.optimize_consts_def
    ,word_instTheory.pull_ops_def
    ,word_instTheory.convert_sub_def
    ,word_instTheory.rm_const_def
    ,word_instTheory.is_const_def
      (* ---- wordLang ssa form and interface to reg allocator ---- *)
    ,word_allocTheory.get_forced_def
    ,word_allocTheory.big_union_def
    ,word_allocTheory.select_reg_alloc_def
    ,word_allocTheory.word_alloc_def
    ,word_allocTheory.full_ssa_cc_trans_def
    ,word_allocTheory.limit_var_def
    ,word_allocTheory.setup_ssa_def
    ,word_allocTheory.total_colour_def
    ,word_allocTheory.oracle_colour_ok_def
    ,word_allocTheory.every_even_colour_def
    ,word_allocTheory.check_colouring_ok_alt_def
    ,word_allocTheory.get_prefs_def
    ,word_allocTheory.get_clash_tree_def
    ,word_allocTheory.get_reads_exp_def
    ,word_allocTheory.get_delta_inst_def
    ,word_allocTheory.ssa_cc_trans_def
    ,word_allocTheory.get_live_def
    ,word_allocTheory.numset_list_insert_def
    ,word_allocTheory.get_live_exp_def
    ,word_allocTheory.get_live_inst_def
    ,word_allocTheory.apply_colour_def
    ,word_allocTheory.apply_colour_inst_def
    ,word_allocTheory.apply_colour_imm_def
    ,word_allocTheory.apply_colour_exp_def
    ,word_allocTheory.ssa_cc_trans_exp_def
    ,word_allocTheory.list_next_var_rename_move_def
    ,word_allocTheory.ssa_cc_trans_inst_def
    ,word_allocTheory.fix_inconsistencies_def
    ,word_allocTheory.fake_moves_def
    ,word_allocTheory.merge_moves_def
    ,word_allocTheory.fake_move_def
    ,word_allocTheory.list_next_var_rename_def
    ,word_allocTheory.next_var_rename_def
    ,word_allocTheory.even_list_def
    ,word_allocTheory.option_lookup_def
    ,word_allocTheory.apply_nummap_key_def
    ,word_allocTheory.remove_dead_def
    ,word_allocTheory.remove_dead_inst_def
    ,word_allocTheory.add1_lhs_const_def
    ,word_allocTheory.add1_lhs_reg_def
    ,word_allocTheory.add1_lhs_mem_def
    ,word_allocTheory.add1_rhs_reg_def
    ,word_allocTheory.add1_rhs_mem_def
    ,word_allocTheory.get_heu_inst_def
    ,word_allocTheory.heu_max_def
    ,word_allocTheory.heu_max_all_def
    ,word_allocTheory.heu_merge_call_def
    ,word_allocTheory.add_call_def
    ,word_allocTheory.get_heuristics_def
    ,word_allocTheory.canonize_moves_aux_def
    ,word_allocTheory.canonize_moves_def
    ,word_allocTheory.get_coalescecost_def
    ,word_allocTheory.get_spillcost_def
    ,word_allocTheory.get_heu_def
    ,sptreeTheory.spt_fold_def
    ,sptreeTheory.mapi_def
    ,sptreeTheory.mapi0_def
    ]
  ,computeLib.Tys
    [ (* ---- stackLang ---- *)
     ``:'a stackLang$prog``
    ,``:stackLang$store_name``
    ]
  ,computeLib.Defs
    [stackLangTheory.list_Seq_def
    ,backend_commonTheory.word_shift_def
    ,backend_commonTheory.stack_num_stubs_def
    ,stackLangTheory.gc_stub_location_eq
      (* ---- word_to_stack ---- *)
    ,word_to_stackTheory.wReg1_def
    ,word_to_stackTheory.wReg2_def
    ,word_to_stackTheory.wRegImm2_def
    ,word_to_stackTheory.wRegWrite1_def
    ,word_to_stackTheory.wStackLoad_def
    ,word_to_stackTheory.wStackStore_def
    ,word_to_stackTheory.wMoveSingle_def
    ,word_to_stackTheory.wMoveAux_def
    ,word_to_stackTheory.format_var_def
    ,word_to_stackTheory.wMove_def
    ,word_to_stackTheory.wInst_def
    ,word_to_stackTheory.bits_to_word_def
    ,word_to_stackTheory.word_list_def
    ,word_to_stackTheory.write_bitmap_def
    ,word_to_stackTheory.insert_bitmap_def
    ,word_to_stackTheory.wLive_def
    ,word_to_stackTheory.SeqStackFree_def
    ,word_to_stackTheory.stack_arg_count_def
    ,word_to_stackTheory.stack_free_def
    ,word_to_stackTheory.stack_move_def_compute
    ,word_to_stackTheory.StackArgs_def
    ,word_to_stackTheory.comp_def
    ,word_to_stackTheory.raise_stub_def
    ,word_to_stackTheory.compile_prog_def
    ,word_to_stackTheory.compile_word_to_stack_def
    ,word_to_stackTheory.compile_def
    ,word_to_stackTheory.call_dest_def
    ,word_to_stackTheory.StackHandlerArgs_def
    ,word_to_stackTheory.PopHandler_def
    ,word_to_stackTheory.PushHandler_def
      (* ---- stack_alloc ---- *)
    ,stack_allocTheory.memcpy_code_def
    ,stack_allocTheory.word_gc_move_loop_code_def
    ,stack_allocTheory.compile_def
    ,stack_allocTheory.prog_comp_def
    ,stack_allocTheory.comp_def
    ,stack_allocTheory.next_lab_def
    ,stack_allocTheory.stubs_def
    ,stack_allocTheory.SetNewTrigger_def
    ,stack_allocTheory.word_gc_code_def
    ,stack_allocTheory.word_gc_partial_or_full_def
    ,stack_allocTheory.word_gc_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gc_move_bitmaps_code_def
    ,stack_allocTheory.word_gc_move_bitmap_code_def
    ,stack_allocTheory.word_gc_move_code_def
    ,stack_allocTheory.word_gc_move_list_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_list_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def
    ,stack_allocTheory.word_gen_gc_partial_move_data_code_def
    ,stack_allocTheory.word_gen_gc_move_code_def
    ,stack_allocTheory.word_gen_gc_move_bitmap_code_def
    ,stack_allocTheory.word_gen_gc_move_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def
    ,stack_allocTheory.word_gen_gc_move_list_code_def
    ,stack_allocTheory.word_gen_gc_move_data_code_def
    ,stack_allocTheory.word_gen_gc_move_refs_code_def
    ,stack_allocTheory.word_gen_gc_move_loop_code_def
    ,stack_allocTheory.clear_top_inst_def
      (* ---- stack_remove ---- *)
    ,stack_removeTheory.max_stack_alloc_def
    ,stack_removeTheory.upshift_def
    ,stack_removeTheory.compile_def
    ,stack_removeTheory.init_stubs_def
    ,stack_removeTheory.init_code_def
    ,stack_removeTheory.store_init_def
    ,stack_removeTheory.init_memory_def
    ,stack_removeTheory.store_list_code_def
    ,stack_removeTheory.halt_inst_def
    ,stack_removeTheory.prog_comp_def
    ,stack_removeTheory.comp_def
    ,stack_removeTheory.stack_load_def
    ,stack_removeTheory.stack_store_def
    ,stack_removeTheory.downshift_def
    ,stack_removeTheory.store_offset_def
    ,stack_removeTheory.stack_free_def
    ,stack_removeTheory.single_stack_free_def
    ,stack_removeTheory.stack_alloc_def
    ,stack_removeTheory.single_stack_alloc_def
    ,stack_removeTheory.stack_err_lab_def
    ,stack_removeTheory.store_length_def
    ,stack_removeTheory.store_list_def
    ,stack_removeTheory.store_pos_def
    ,stack_removeTheory.word_offset_def
    ]
  ,computeLib.Tys
    [ (* ---- db_vars ---- *)
     ``:db_var_set``
    ]
  ,computeLib.Defs
    [db_varsTheory.mk_Union_def
    ,db_varsTheory.vars_to_list_def
    ,db_varsTheory.vars_from_list_def
    ,db_varsTheory.vars_flatten_def
    ,db_varsTheory.has_var_def
    ,db_varsTheory.db_to_set_acc_def
    ,db_varsTheory.db_to_set_def
    ,db_varsTheory.list_mk_Union_def
      (* ---- stack names ---- *)
    ,stack_namesTheory.ri_find_name_def
    ,stack_namesTheory.inst_find_name_def
    ,stack_namesTheory.dest_find_name_def
    ,stack_namesTheory.comp_def
    ,stack_namesTheory.prog_comp_def
    ,stack_namesTheory.compile_def
    (* ---- stack_to_lab ---- *)
    ,stack_to_labTheory.is_gen_gc_def
    ,stack_to_labTheory.compile_jump_def
    ,stack_to_labTheory.negate_def
    ,stack_to_labTheory.flatten_def
    ,stack_to_labTheory.prog_to_section_def
    ,stack_to_labTheory.compile_def
    ]
  ,computeLib.Tys
    [ (* ---- labLang ---- *)
     ``:lab``
    ,``:'a asm_with_lab``
    ,``:'a asm_or_cbw``
    ,``:'a line``
    ,``:'a sec``
    ]
  ,computeLib.Defs
    [labLangTheory.Section_num_def
    ,labLangTheory.Section_lines_def
      (* ---- lab_filter ---- *)
    ,lab_filterTheory.not_skip_def
    ,lab_filterTheory.filter_skip_def
      (* ---- lab_to_target ---- *)
    ,lab_to_targetTheory.ffi_offset_def
    ,lab_to_targetTheory.lab_inst_def
    ,lab_to_targetTheory.cbw_to_asm_def
    ,lab_to_targetTheory.enc_line_def
    ,lab_to_targetTheory.enc_sec_def
    ,lab_to_targetTheory.enc_sec_list_def
    ,lab_to_targetTheory.section_labels_def
    ,lab_to_targetTheory.compute_labels_alt_def
    ,lab_to_targetTheory.find_pos_def
    ,lab_to_targetTheory.get_label_def
    ,lab_to_targetTheory.get_jump_offset_def
    ,lab_to_targetTheory.enc_lines_again_def
    ,lab_to_targetTheory.enc_secs_again_def
    ,lab_to_targetTheory.lines_upd_lab_len_def
    ,lab_to_targetTheory.upd_lab_len_def
    ,lab_to_targetTheory.line_ok_light_def
    ,lab_to_targetTheory.sec_ok_light_def
    ,lab_to_targetTheory.pad_bytes_def
    ,lab_to_targetTheory.add_nop_def
    ,lab_to_targetTheory.pad_section_def
    ,lab_to_targetTheory.pad_code_def
    ,lab_to_targetTheory.remove_labels_loop_def
    ,lab_to_targetTheory.remove_labels_def
    ,lab_to_targetTheory.line_bytes_def
    ,lab_to_targetTheory.prog_to_bytes_def
    ,lab_to_targetTheory.find_ffi_names_def
    ,lab_to_targetTheory.list_add_if_fresh_def
    ,lab_to_targetTheory.get_ffi_index_def
    ,lab_to_targetTheory.sec_length_def
    ,lab_to_targetTheory.compile_lab_def
    ,lab_to_targetTheory.compile_def
    ]
      (* ---- Everything in backend theory ---- *)
  ,computeLib.Defs (theory_computes "backend")
  ,computeLib.Tys
    [
     ``:architecture``
    ,``:'a asm_config``
    ,``:'a reg_imm``
    ,``:binop``
    ,``:cmp``
    ,``:shift``
    ,``:'a arith``
    ,``:'a addr``
    ,``:memop``
    ,``:'a inst``
    ,``:'a asm``
    ]
  ,computeLib.Extenders
    [basicComputeLib.add_basic_compset
    ,basisComputeLib.add_basis_compset
    ,semanticsComputeLib.add_ast_compset
    ,semanticsComputeLib.add_namespace_compset
    ,reg_allocComputeLib.add_reg_alloc_compset
    ]
  ]

end

end
