(*
  Translate the backend from labelled assembly to target code.
*)
Theory from_labProg[no_sig_docs]
Ancestors
  evaluate ml_translator decProg std_prelude lab_filter lab_to_target
  asm monadic_enc monadic_enc64 backend[qualified]
Libs
  preamble ml_translatorLib ml_monad_translatorLib

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "decProg";
val _ = ml_translatorLib.use_sub_check true;

(* Monadic runners share these top-level result constructors. *)
val _ = register_type “:('a, 'b) ml_monadBase$exc”;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "from_labProg");

val _ = computeLib.upd_compset (fn c => computeLib.set_skip c “COND” (SOME 1));

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

val _ = translate asmTheory.arch_width_bits_def;
val _ = translate asmTheory.arch_bytes_def;
val _ = translate asmTheory.arch_shift_def;

val _ = translate (asmTheory.offset_ok_def |> SIMP_RULE (srw_ss()) [alignmentTheory.aligned_bitwise_and, integerTheory.INT_DIVIDES_MOD0])
(* The record types used for the monadic state and exceptions *)
val exn_type   = ``:monadic_enc64$state_exn_64``;
val _          = register_exn_type exn_type;
val STATE_EXN_TYPE_def =  theorem "MONADIC_ENC64_STATE_EXN_64_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;

val exn_functions = [
    (monadic_enc64Theory.raise_Fail_def, monadic_enc64Theory.handle_Fail_def),
    (monadic_enc64Theory.raise_Subscript_def, monadic_enc64Theory.handle_Subscript_def)
];
val refs_manip_list = [] : (string * thm * thm) list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

val state_type_64 = ``:enc_state_64``;
val store_hprop_name_64   = "ENC_STATE_64";
val farrays_manip_list_64 = [
    ("hash_tab_64", monadic_enc64Theory.get_hash_tab_64_def,
     monadic_enc64Theory.set_hash_tab_64_def,
     monadic_enc64Theory.hash_tab_64_length_def,
     monadic_enc64Theory.hash_tab_64_sub_def,
     monadic_enc64Theory.update_hash_tab_64_def)];

val _ = translate (monadic_encTheory.hash_reg_imm_def)
val _ = translate monadic_encTheory.hash_binop_def
val _ = translate monadic_encTheory.hash_cmp_def
val _ = translate monadic_encTheory.hash_shift_def
val _ = translate (monadic_encTheory.hash_arith_def |> SIMP_RULE std_ss [monadic_encTheory.roll_hash_def])
val _ = translate monadic_encTheory.hash_memop_def
val _ = translate (monadic_encTheory.hash_fp_def |> SIMP_RULE std_ss [monadic_encTheory.roll_hash_def])
val _ = translate (monadic_encTheory.hash_inst_def |> SIMP_RULE std_ss [monadic_encTheory.roll_hash_def])
val _ = translate (monadic_encTheory.hash_asm_def |> SIMP_RULE std_ss [monadic_encTheory.roll_hash_def])

(* Initialization *)

val res = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list_64
            store_hprop_name_64
            state_type_64
            exn_ri_def
            exn_functions
            add_type_theories
            store_pinv_def_opt;

val _ = translate (lab_to_targetTheory.lab_inst_def)
val _ = translate (lab_to_targetTheory.compile_shmem_def)
val _ = m_translate monadic_enc64Theory.lookup_ins_table_64_def;
val _ = m_translate monadic_enc64Theory.enc_line_hash_64_def;
val _ = m_translate monadic_enc64Theory.enc_line_hash_64_ls_def;
val _ = m_translate monadic_enc64Theory.enc_sec_hash_64_ls_def;
val _ = m_translate monadic_enc64Theory.enc_sec_hash_64_ls_full_def;

val _ = m_translate_run monadic_enc64Theory.enc_secs_64_aux_def;

val _ = translate monadic_enc64Theory.enc_secs_64_def;

Theorem monadic_enc64_enc_line_hash_64_ls_side_def[local]:
  ∀a b c d e.
  d ≠ 0 ⇒
  monadic_enc64_enc_line_hash_64_ls_side a b c d e ⇔ T
Proof
  Induct_on`e`>>
  simp[Once (fetch "-" "monadic_enc64_enc_line_hash_64_ls_side_def")]>>
  EVAL_TAC>>rw[]>>fs[]
QED

Theorem monadic_enc64_enc_sec_hash_64_ls_side_def[local]:
  ∀a b c d e.
  d ≠ 0 ⇒
  monadic_enc64_enc_sec_hash_64_ls_side a b c d e ⇔ T
Proof
  Induct_on`e`>>
  simp[Once (fetch "-" "monadic_enc64_enc_sec_hash_64_ls_side_def")]>>
  metis_tac[monadic_enc64_enc_line_hash_64_ls_side_def]
QED

Theorem monadic_enc64_enc_secs_64_side_def[allow_rebind] = Q.prove(`
  monadic_enc64_enc_secs_64_side a b c ⇔ T`,
  EVAL_TAC>>
  rw[]>>
  metis_tac[monadic_enc64_enc_sec_hash_64_ls_side_def,DECIDE``1n ≠ 0``])
  |> update_precondition;

val _ = translate (lab_filterTheory.filter_skip_def)

val _ = translate (lab_to_targetTheory.get_jump_offset_def)

Theorem word_2compl_eq[local]:
    !w:'a word. -w = 0w - w
Proof
  fs []
QED

val _ = translate (asmTheory.reg_imm_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,
                                               word_2compl_eq])

val _ = translate (asmTheory.arith_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

val _ = translate (asmTheory.fp_ok_def)
val _ = translate (asmTheory.inst_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

val _ = translate (asmTheory.asm_ok_def)

val res = translate (lab_to_targetTheory.zero_labs_acc_of_def)
val res = translate (lab_to_targetTheory.line_get_zero_labs_acc_def)
val res = translate (lab_to_targetTheory.sec_get_zero_labs_acc_def)
val res = translate (lab_to_targetTheory.get_zero_labs_acc_def)
val res = translate (lab_to_targetTheory.zero_labs_acc_exist_def |> INST_TYPE[alpha |-> ``:num``])

(* Add in hidden argument to compile_lab *)
Definition remove_labels_hash_def:
  remove_labels_hash init_clock c pos labs ffis hash_size sec_list =
    remove_labels_loop init_clock c pos labs ffis (enc_secs_64 c.encode hash_size sec_list)
End

Theorem remove_labels_hash_correct[local]:
  remove_labels_hash c.init_clock ac c.pos c.labels ffis c.hash_size sec_list =
  remove_labels c.init_clock ac c.pos c.labels ffis sec_list
Proof
  simp [FUN_EQ_THM, remove_labels_hash_def, lab_to_targetTheory.remove_labels_def,
        monadic_enc64Theory.enc_secs_64_correct]
QED

val res = translate (remove_labels_hash_def);

val res = translate $ INST_TYPE[alpha|->``:8``] $ lab_to_targetTheory.get_memop_info_def;

val res = translate lab_to_targetTheory.get_shmem_info_def;

val compile_lab_thm = lab_to_targetTheory.compile_lab_def
  |> REWRITE_RULE [GSYM remove_labels_hash_correct];

val res = translate compile_lab_thm;

val res = translate (lab_to_targetTheory.compile_def);

val _ = translate backendTheory.attach_bitmaps_def;

val _ = translate backendTheory.from_lab_def;

(* explorer specific functions *)

val r = presLangTheory.num_to_hex_def |> translate;
val r = presLangTheory.word_to_display_def |> translate;
val r = presLangTheory.item_with_word_def |> translate;
val r = presLangTheory.asm_binop_to_display_def |> translate;
val r = presLangTheory.asm_reg_imm_to_display_def |> translate;
val r = presLangTheory.asm_arith_to_display_def |> translate;
val r = presLangTheory.asm_inst_to_display_def |> translate;
val res = presLangTheory.asm_cmp_to_display_def |> translate;
val res = presLangTheory.asm_asm_to_display_def |> translate;
val res = presLangTheory.lab_asm_to_display_def
          |> REWRITE_RULE [presLangTheory.string_imp_def] |> translate;
val res = presLangTheory.lab_line_to_display_def |> translate;
val res = presLangTheory.lab_fun_to_display_def |> translate;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);
val _ = ml_translatorLib.clean_on_exit := true;
