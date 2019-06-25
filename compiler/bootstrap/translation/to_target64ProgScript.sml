(*
  Translate the final part of the compiler backend for 64-bit targets.
*)
open preamble;
open terminationTheory
open ml_translatorLib ml_translatorTheory;
open to_word64ProgTheory std_preludeTheory;

val _ = new_theory "to_target64Prog"

val _ = translation_extends "to_word64Prog";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "to_target64Prog");

val RW = REWRITE_RULE

val _ = add_preferred_thy "-";

val NOT_NIL_AND_LEMMA = Q.prove(
  `(b <> [] /\ x) = if b = [] then F else x`,
  Cases_on `b` THEN FULL_SIMP_TAC std_ss []);

val extra_preprocessing = ref [MEMBER_INTRO,MAP];

val matches = ref ([]: term list);
val inst_tyargs = ref ([]:hol_type list);

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

  val insts = if exists (fn term => can (find_term (can (match_term term))) (concl def)) (!matches) then map (fn x => x |-> ``:64``) (!inst_tyargs)  else []

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

val _ = matches:= [``foo:'a wordLang$prog``,``foo:'a wordLang$exp``,``foo:'a word``,``foo: 'a reg_imm``,``foo:'a arith``,``foo: 'a addr``,``foo:'a stackLang$prog``]

val _ = inst_tyargs := [alpha]

open word_to_stackTheory;

val _ = translate (conv64 write_bitmap_def|> (RW (!extra_preprocessing)))

(* TODO: The paired let trips up the translator's single line def mechanism, unable to find a smaller failing example yet *)
val _ = translate (conv64 (wLive_def |> SIMP_RULE std_ss [LET_THM]))

(* TODO: the name is messed up (pair_) *)
val _ = translate PAIR_MAP

val _ = translate parmoveTheory.fstep_def

val parmove_fstep_side = Q.prove(`
  ∀x. parmove_fstep_side x ⇔ T`,
  EVAL_TAC>>rw[]>>Cases_on`v18`>>fs[]) |> update_precondition

val _ = translate (spec64 word_to_stackTheory.wMove_def)

val _ = translate (spec64 call_dest_def)

val _ = translate (wInst_def |> conv64)
val _ = translate (spec64 comp_def)

val _ = translate (compile_word_to_stack_def |> INST_TYPE [beta |-> ``:64``])

val _ = translate (compile_def |> INST_TYPE [alpha|->``:64``,beta|->``:64``]);

open stack_allocTheory;

val inline_simp = SIMP_RULE std_ss [bytes_in_word_def,
                                    backend_commonTheory.word_shift_def]
val _ = translate (SetNewTrigger_def |> inline_simp |> conv64)
val _ = translate (conv64 clear_top_inst_def)
val _ = translate (memcpy_code_def |> inline_simp |> conv64)
val _ = translate (word_gc_move_code_def |> inline_simp |> conv64)

val _ = translate (word_gc_move_bitmap_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_roots_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_list_code_def |> inline_simp |> conv64);
val _ = translate (word_gc_move_loop_code_def |> inline_simp |> conv64);

val _ = translate (stack_allocTheory.word_gen_gc_move_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmap_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_roots_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_list_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_data_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_refs_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_move_loop_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmap_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_roots_bitmaps_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_list_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_ref_list_code_def |> inline_simp |> conv64);
val _ = translate (stack_allocTheory.word_gen_gc_partial_move_data_code_def |> inline_simp |> conv64);
val r = translate (stack_allocTheory.word_gc_partial_or_full_def |> inline_simp |> conv64);
val r = translate (stack_allocTheory.word_gc_code_def |> inline_simp |> conv64);

val _ = translate (spec64 stubs_def);

val _ = translate (spec64 comp_def(*pmatch*));

val _ = translate (spec64 compile_def);

(*
val stack_alloc_comp_side = Q.prove(`
  ∀n m prog. stack_alloc_comp_side n m prog ⇔ T`,
`(∀prog n m. stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) (z:num) n m. opt = SOME(prog,x,y,z) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) (z:num) n m. opt = (prog,x,y,z) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) n m. opt = SOME(prog,x,y) ⇒ stack_alloc_comp_side n m prog ⇔ T) ∧
 (∀opt prog (x:num) (y:num) n m. opt = (prog,x,y) ⇒ stack_alloc_comp_side n m prog ⇔ T)`
  suffices_by fs[]
  >> ho_match_mp_tac(TypeBase.induction_of ``:64 stackLang$prog``)
  >> fs[]
  >> rpt strip_tac
  >> rw[Once(fetch "-" "stack_alloc_comp_side_def")]
  >> fs[]
  >> metis_tac[option_nchotomy, pair_CASES]) |> update_precondition

val stack_alloc_prog_comp_side = Q.prove(`∀prog. stack_alloc_prog_comp_side prog ⇔ T`,
  fs[fetch "-" "stack_alloc_prog_comp_side_def", stack_alloc_comp_side]) |> update_precondition;

val stack_alloc_compile_side = Q.prove(`∀conf prog. stack_alloc_compile_side conf prog ⇔ T`,
  fs[fetch "-" "stack_alloc_compile_side_def", stack_alloc_prog_comp_side]) |> update_precondition;
*)

open stack_removeTheory;

(* Might be better to inline this *)
val _ = translate (conv64 word_offset_def)
val _ = translate (conv64 store_offset_def |> SIMP_RULE std_ss [word_mul_def,word_2comp_def] |> conv64)

val _ = translate (comp_def |> inline_simp |> conv64)

val _ = translate (prog_comp_def |> INST_TYPE [beta|->``:64``])

val _ = translate (store_list_code_def |> inline_simp |> conv64)
val _ = translate (init_memory_def |> inline_simp |> conv64)
val _ = translate (init_code_def |> inline_simp |> conv64 |> SIMP_RULE std_ss [word_mul_def]|>gconv|>SIMP_RULE std_ss[w2n_n2w] |> conv64)

val _ = translate (spec64 compile_def)

open stack_namesTheory;

val _ = translate (spec64 comp_def)
val _ = translate (prog_comp_def |> INST_TYPE [beta |-> ``:64``])
val _ = translate (compile_def |> INST_TYPE [beta |-> ``:64``])

open stack_to_labTheory;

val _ = matches := [``foo:'a labLang$prog``,``foo:'a
  labLang$sec``,``foo:'a labLang$line``,``foo:'a
  labLang$asm_with_lab``,``foo:'a labLang$line list``,``foo:'a
  inst``,``foo:'a asm_config``] @ (!matches)

val _ = translate (flatten_def |> spec64)

val _ = translate (compile_def |> spec64)

open lab_filterTheory lab_to_targetTheory asmTheory;
open monadic_encTheory monadic_enc64Theory ml_monad_translatorLib;

(* The record types used for the monadic state and exceptions *)
val exn_type   = ``:monadic_enc64$state_exn_64``;
val _          = register_exn_type exn_type;
val STATE_EXN_TYPE_def =  theorem "MONADIC_ENC64_STATE_EXN_64_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;

val exn_functions = [
    (raise_Fail_def, handle_Fail_def),
    (raise_Subscript_def, handle_Subscript_def)
];
val refs_manip_list = [] : (string * thm * thm) list;
val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;

val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

val state_type_64 = ``:enc_state_64``;
val store_hprop_name_64   = "ENC_STATE_64";
val farrays_manip_list_64 = [
    ("hash_tab_64", get_hash_tab_64_def, set_hash_tab_64_def, hash_tab_64_length_def, hash_tab_64_sub_def, update_hash_tab_64_def)];

val _ = translate (hash_reg_imm_def |> INST_TYPE [alpha|->``:64``])
val _ = translate hash_binop_def
val _ = translate hash_cmp_def
val _ = translate hash_shift_def
val _ = translate (hash_arith_def |> INST_TYPE [alpha|->``:64``] |> SIMP_RULE std_ss [roll_hash_def])
val _ = translate hash_memop_def
val _ = translate (hash_fp_def |> SIMP_RULE std_ss [roll_hash_def])
val _ = translate (hash_inst_def |> INST_TYPE [alpha|->``:64``] |> SIMP_RULE std_ss [roll_hash_def])
val _ = translate (hash_asm_def |> INST_TYPE [alpha|->``:64``] |> SIMP_RULE std_ss [roll_hash_def])

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

val _ = translate (lab_inst_def |> INST_TYPE [alpha |-> ``:64``])
val _ = translate (cbw_to_asm_def |> INST_TYPE [alpha |-> ``:64``])
val _ = m_translate lookup_ins_table_64_def;
val _ = m_translate enc_line_hash_64_def;
val _ = m_translate enc_line_hash_64_ls_def;
val _ = m_translate enc_sec_hash_64_ls_def;
val _ = m_translate enc_sec_hash_64_ls_full_def;

val _ = m_translate_run enc_secs_64_aux_def;

val _ = translate enc_secs_64_def;

val monadic_enc64_enc_line_hash_64_ls_side_def = Q.prove(`
  ∀a b c d e.
  d ≠ 0 ⇒
  monadic_enc64_enc_line_hash_64_ls_side a b c d e ⇔ T`,
  Induct_on`e`>>
  simp[Once (fetch "-" "monadic_enc64_enc_line_hash_64_ls_side_def")]>>
  EVAL_TAC>>rw[]>>fs[]);

val monadic_enc64_enc_sec_hash_64_ls_side_def = Q.prove(`
  ∀a b c d e.
  d ≠ 0 ⇒
  monadic_enc64_enc_sec_hash_64_ls_side a b c d e ⇔ T`,
  Induct_on`e`>>
  simp[Once (fetch "-" "monadic_enc64_enc_sec_hash_64_ls_side_def")]>>
  metis_tac[monadic_enc64_enc_line_hash_64_ls_side_def]);

Theorem monadic_enc64_enc_secs_64_side_def = Q.prove(`
  monadic_enc64_enc_secs_64_side a b c ⇔ T`,
  EVAL_TAC>>
  rw[]>>
  metis_tac[monadic_enc64_enc_sec_hash_64_ls_side_def,DECIDE``1n ≠ 0``])
  |> update_precondition;

val _ = translate (spec64 filter_skip_def)

val _ = translate (get_jump_offset_def |>INST_TYPE [alpha|->``:64``,beta |-> ``:64``])

val word_2compl_eq = prove(
  ``!w:'a word. -w = 0w - w``,
  fs []);

val _ = translate (conv64 reg_imm_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY,
                                               word_2compl_eq])

val _ = translate (conv64 arith_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

val _ = translate (fp_ok_def |> conv64)
val _ = translate (conv64 inst_ok_def |> SIMP_RULE std_ss [IN_INSERT,NOT_IN_EMPTY])

(* TODO: there may be a better rewrite for aligned (in to_word64Prog's translation of offset_ok) *)

val _ = translate (spec64 asmTheory.asm_ok_def)

(* Add in hidden argument to compile_lab *)
val remove_labels_hash_def = Define `
  remove_labels_hash init_clock c pos labs ffis hash_size sec_list =
    remove_labels_loop init_clock c pos labs ffis (enc_secs_64 c.encode hash_size sec_list)`;

val res = translate (remove_labels_hash_def |> spec64);

val compile_lab_thm = Q.prove(`
  compile_lab c sec_list =
    let current_ffis = find_ffi_names sec_list in
    let (ffis,ffis_ok) =
      case c.ffi_names of SOME ffis => (ffis, list_subset current_ffis ffis) | _ => (current_ffis,T)
    in
    if ffis_ok then
      case remove_labels_hash c.init_clock c.asm_conf c.pos c.labels ffis c.hash_size sec_list of
      | SOME (sec_list,l1) =>
          SOME (prog_to_bytes sec_list,
                c with <| labels := l1;
                          pos := FOLDL (λpos sec. sec_length (Section_lines sec) pos) c.pos sec_list;
                          ffi_names := SOME ffis
                        |>)
      | NONE => NONE
    else NONE`,
  rw[compile_lab_def,remove_labels_hash_def,remove_labels_def]>>
  simp[enc_secs_64_correct]);

val res = translate compile_lab_thm;

val res = translate (spec64 compile_def);

val () = Feedback.set_trace "TheoryPP.include_docs" 0;

val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();
