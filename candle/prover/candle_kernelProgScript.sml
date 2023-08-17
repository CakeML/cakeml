(*
  Adds Candle specific functions to the kernel module from ml_hol_kernel_funsProg
*)
open preamble;
open ml_translatorLib ml_monad_translatorLib ml_progLib ml_hol_kernel_funsProgTheory;
open basisFunctionsLib print_thmTheory;
open (* lisp: *) lisp_parsingTheory lisp_valuesTheory lisp_printingTheory;
open (* compute: *) compute_syntaxTheory compute_evalTheory computeTheory
                    compute_pmatchTheory;
open runtime_checkTheory runtime_checkLib;

val _ = new_theory "candle_kernelProg";

val _ = set_grammar_ancestry [ "ml_hol_kernel_funsProg", "compute"
  ];

val _ = m_translation_extends "ml_hol_kernel_funsProg"

val _ = (use_long_names := false);

val _ = ml_prog_update open_local_block;

val r = translate lisp_valuesTheory.name_def;
val r = translate lisp_printingTheory.num2ascii_def;
val r = translate lisp_printingTheory.ascii_name_def;

val lemma = prove(“ascii_name_side v3”,
  fs [fetch "-" "ascii_name_side_def"]
  \\ fs [Once lisp_printingTheory.num2ascii_def,AllCaseEqs()])
  |> update_precondition;

val r = translate num2str_def;

val lemma = prove(“∀n. num2str_side n”,
  ho_match_mp_tac lisp_printingTheory.num2str_ind
  \\ rw [] \\ simp [Once (fetch "-" "num2str_side_def")]
  \\ rw [] \\ gvs [DIV_LT_X]
  \\ ‘n MOD 10 < 10’ by fs []
  \\ decide_tac)
  |> update_precondition;

val r = translate lisp_printingTheory.name2str_def;
val r = translate lisp_valuesTheory.list_def;
val r = translate nil_list_def;
val r = translate str_to_v_def;
val r = translate ty_to_v_def;
val r = translate term_to_v_def;
val r = translate thm_to_v_def;
val r = translate update_to_v_def;
val r = translate dest_quote_def;
val r = translate dest_list_def;
val r = translate newlines_def;
val r = translate v2pretty_def;
val r = translate get_size_def;
val r = translate get_next_size_def;
val r = translate annotate_def;
val r = translate remove_all_def;
val r = translate smart_remove_def;
val r = translate flatten_def;
val r = translate dropWhile_def;
val r = translate is_comment_def;
val r = translate v2str_def;
val r = translate vs2str_def;
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

Triviality check_cexp_closed_ind:
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
val r = translate compute_execTheory.monop_def
val r = translate compute_execTheory.to_num_def
val r = translate compute_execTheory.cv_T_def
val r = translate compute_execTheory.cv_F_def
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

val _ = export_theory();
