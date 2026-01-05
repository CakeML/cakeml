(*
  Adds Candle specific functions to the kernel module from ml_hol_kernel_funsProg
*)
Theory candle_kernelProg
Libs
  preamble ml_translatorLib ml_monad_translatorLib ml_progLib
  basisFunctionsLib runtime_checkLib
Ancestors
  ml_hol_kernel_funsProg compute print_thm
  (* compute: *) compute_syntax compute_eval compute_pmatch
  runtime_check

val _ = m_translation_extends "ml_hol_kernel_funsProg"

val _ = (use_long_names := false);

val _ = ml_prog_update open_local_block;

val r = translate ty_to_v_def;
val r = translate term_to_v_def;
val r = translate thm_to_v_def;
val r = translate update_to_v_def;
val r = translate thm_to_string_def;

val _ = ml_prog_update open_local_in_block;

val _ = (append_prog o process_topdecs) `
  val print_thm = fn th => case th of Sequent tms c =>
    let
      val ctxt = !the_context
      val str = thm_to_string ctxt th
      val arr = Word8Array.array 0 (Word8.fromInt 0)
    in
      #(kernel_ffi) str arr
    end;
`
(* compute primitive *)

val _ = ml_prog_update open_local_block;

val r = translate dest_num_PMATCH;
val r = m_translate dest_numeral_PMATCH;
val r = translate dest_numeral_opt_PMATCH;
val r = translate list_dest_comb_def;
val r = translate mapOption_def;
val r = translate app_type_def;
val r = translate dest_cexp_def;

Theorem dest_cexp_side[local]:
  ∀x. dest_cexp_side x
Proof
  ho_match_mp_tac dest_cexp_ind \\ rw []
  \\ once_rewrite_tac [fetch "-" "dest_cexp_side_def"] \\ rw []
QED

val _ = update_precondition dest_cexp_side;

val r = m_translate option_def;
val r = m_translate check_def;
val r = translate SAFEMOD_def;
val r = translate SAFEDIV_def;
val r = translate num2bit_def;
val r = translate compute_execTheory.cv2term_def

val r = compute_thms_def |> EVAL_RULE |> translate;

val r = m_translate dest_binary_PMATCH;

val r = check [‘ths’] compute_init_def |> translate;

val r = m_translate check_var_def;

val _ = use_mem_intro := true;
val res = translate_no_ind check_cexp_closed_def;

Theorem check_cexp_closed_ind[local]:
  check_cexp_closed_ind
Proof
  rewrite_tac [fetch "-" "check_cexp_closed_ind_def"]
  \\ rpt gen_tac
  \\ rpt (disch_then strip_assume_tac)
  \\ match_mp_tac (latest_ind ())
  \\ rpt strip_tac
  \\ last_x_assum match_mp_tac
  \\ rpt strip_tac
  \\ fs [FORALL_PROD, GSYM ml_translatorTheory.MEMBER_INTRO]
QED

val _ = check_cexp_closed_ind |> update_precondition;
val _ = use_mem_intro := false;

val r = translate var_list_def;

val r = translate const_list_def;
val r = m_translate map_def;

val _ = use_mem_intro := true;
val r = m_translate check_consts_def;
val r = m_translate check_eqn_def;
val _ = use_mem_intro := false;

val r = translate compute_default_clock; (* TODO _def *)
val r = translate indexedListsTheory.findi_def
val r = translate compute_execTheory.monop_fst_def
val r = translate compute_execTheory.monop_snd_def
val r = translate compute_execTheory.monop_ispair_def
val r = translate compute_execTheory.monop_def
val r = translate compute_execTheory.to_num_def
val r = translate compute_execTheory.cv_T_def
val r = translate compute_execTheory.cv_F_def
val r = translate compute_execTheory.binop_add_def
val r = translate (compute_execTheory.binop_sub_def |> REWRITE_RULE [GSYM ml_translatorTheory.sub_check_def]);
val r = translate compute_execTheory.binop_mul_def
val r = translate compute_execTheory.binop_div_def
val r = translate compute_execTheory.binop_mod_def
val r = translate compute_execTheory.binop_eq_def
val r = translate compute_execTheory.binop_less_def
val r = translate compute_execTheory.binop_def
val r = translate compute_execTheory.to_ce_def
val r = translate compute_execTheory.compile_to_ce_def
val r = translate compute_execTheory.build_funs_def
val r = translate compute_execTheory.env_lookup_def

val r = m_translate compute_execTheory.get_code_def
val r = m_translate compute_execTheory.exec_def

val _ = ml_prog_update open_local_in_block;

val r = check [‘ths’,‘tm’] compute_add_def |> m_translate;
val r = compute_def
        |> SIMP_RULE(srw_ss()) [combinTheory.C_DEF]
        |> check [‘ths’,‘ceqs’,‘tm’]
        |> m_translate;

val _ = ml_prog_update close_local_blocks;
val _ = ml_prog_update (close_module NONE);

(* extract the interesting theorem *)

val _ = Globals.max_print_depth := 10;

fun define_abbrev_conv name tm = let
  val def = define_abbrev true name tm
  in GSYM def |> SPEC_ALL end

Theorem candle_prog_thm =
  get_Decls_thm (get_ml_prog_state())
  |> CONV_RULE ((RATOR_CONV o RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_code"))
  |> CONV_RULE ((RATOR_CONV o RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_env"))
  |> CONV_RULE ((RAND_CONV)
                (EVAL THENC define_abbrev_conv "candle_init_state"));

(* extract some other other theorems *)

Theorem EqualityType_TYPE_TYPE = EqualityType_rule [] “:type”;

Theorem EqualityType_TERM_TYPE = EqualityType_rule [] “:term”;

Theorem EqualityType_THM_TYPE = EqualityType_rule [] “:thm”;

Theorem EqualityType_UPDATE_TYPE = EqualityType_rule [] “:update”;

val _ = (print_asts := true);
