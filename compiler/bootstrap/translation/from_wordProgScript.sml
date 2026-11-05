(*
  Translate wordLang optimization and lowering to target code.
*)
Theory from_wordProg[no_sig_docs]
Ancestors
  ml_translator reg_allocProg std_prelude word_to_stack word_simp
  word_alloc word_inst backend[qualified]
Libs
  preamble ml_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "reg_allocProg";
val _ = ml_translatorLib.use_sub_check true;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_wordProg");

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

val _ = register_type “:wordLang$prog”;
val EqualityType_prog = EqualityType_rule [] “:wordLang$prog”;

(* ------------------------------------------------------------------------- *)
(* word_to_word                                                              *)
(* ------------------------------------------------------------------------- *)

val res = word_cseTheory.map_insert_def |> DefnBase.one_line_ify NONE |> translate;

val res = translate word_cseTheory.bm_inter_eq_def;
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

(* ------------------------------------------------------------------------- *)
(* word_to_stack                                                             *)
(* ------------------------------------------------------------------------- *)

val _ = translate word_to_stackTheory.bits_to_word_def;
val _ = translate word_to_stackTheory.word_list_def;
val _ = translate word_to_stackTheory.chunk_to_bits_def;
val _ = translate word_to_stackTheory.chunk_to_bitmap_def;
val _ = translate word_to_stackTheory.const_words_to_bitmap_def;
Theorem word_to_stack_chunk_to_bitmap_side_total[local]:
  ∀bits ws. word_to_stack_chunk_to_bitmap_side bits ws
Proof
  rw [fetch "-" "word_to_stack_chunk_to_bitmap_side_def"]
  \\ mp_tac (Q.SPECL [`v1`,`&(2 ** bits)`] integerTheory.INT_MOD_BOUNDS)
  \\ simp []
QED
val _ = update_precondition word_to_stack_chunk_to_bitmap_side_total;

Theorem word_to_stack_const_words_to_bitmap_side_total[local]:
  ∀bits ws ws_len. word_to_stack_const_words_to_bitmap_side bits ws ws_len
Proof
  ho_match_mp_tac word_to_stackTheory.const_words_to_bitmap_ind
  \\ rpt strip_tac
  \\ once_rewrite_tac [fetch "-" "word_to_stack_const_words_to_bitmap_side_def"]
  \\ gvs [word_to_stack_chunk_to_bitmap_side_total]
QED
val _ = update_precondition word_to_stack_const_words_to_bitmap_side_total;

val _ = translate (word_to_stackTheory.write_bitmap_def
  |> REWRITE_RULE (!extra_preprocessing));
val _ = translate (word_to_stackTheory.wLive_def |> SIMP_RULE std_ss [LET_THM]);

val _ = translate parmoveTheory.fstep_def

val parmove_fstep_side = Q.prove(`
  ∀x. parmove_fstep_side x ⇔ T`,
  EVAL_TAC>>rw[]>>Cases_on`v18`>>fs[]) |> update_precondition

val _ = translate (word_to_stackTheory.wMove_def)

val _ = translate (word_to_stackTheory.call_dest_def)

val _ = translate (word_to_stackTheory.wInst_def)

val _ = translate (word_to_stackTheory.perf_call_prefix_def)
(* top-level vals must not call functions (no_ptr_eq), so unfold list_Seq *)
val _ = translate (word_to_stackTheory.perf_call_suffix_def
                   |> REWRITE_RULE [stackLangTheory.list_Seq_def])

val _ = translate (word_to_stackTheory.num_stack_ret_def |> INST_TYPE [alpha|->``:num``])
val _ = translate (word_to_stackTheory.skip_free_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.copy_ret_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.stack_arg_count_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.StackArgs_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.StackHandlerArgs_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.PushHandler_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])
val _ = translate (word_to_stackTheory.PopHandler_def |> INST_TYPE [alpha|->``:num``,beta|->``:num``])

val _ = translate word_to_stackTheory.comp_def;
val _ = translate (word_to_stackTheory.compile_word_to_stack_def
  |> INST_TYPE [alpha |-> “:num”]);
val _ = translate word_to_stackTheory.compile_def;

val _ = translate backendTheory.from_word_def;

val _ = translate backendTheory.from_word_0_def;

val r = presLangTheory.word_exp_to_display_def |> translate
val r = presLangTheory.ws_to_display_def |> translate
val r = presLangTheory.word_seqs_def |> translate

val r = presLangTheory.word_prog_to_display_def

          |> REWRITE_RULE [presLangTheory.string_imp_def]
          |> translate

val r = presLangTheory.word_fun_to_display_def |> translate

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
