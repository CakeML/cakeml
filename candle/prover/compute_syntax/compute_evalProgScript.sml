(*
  Translation of the compute_eval interpreter into code using local state and
  exceptions.
*)

open preamble ml_translatorLib ml_monad_translatorLib ml_progLib
     basisProgTheory basisFunctionsLib holKernelTheory compute_syntaxTheory
     compute_evalTheory;

val _ = new_theory "compute_evalProg";

val _ = translation_extends "basisProg"

val _ = (use_long_names := false);
val _ = (use_full_type_names := false);

val _ = register_type “:type”;
val _ = register_type “:term”;
val _ = register_type “:thm”;

val exn_type = “:cv_exn”;
val state_type = “:cv_state”;
val _ = register_exn_type exn_type;

val STATE_EXN_TYPE_def = theorem "CV_EXN_TYPE_def"
val exn_ri_def         = STATE_EXN_TYPE_def;
val store_hprop_name   = "CV_STATE";

val exn_functions = [
    (raise_Type_error_def, handle_Type_error_def),
    (raise_Timeout_def, handle_Timeout_def)
  ];

val refs_manip_list = [
    ("dummy", get_dummy_def, set_dummy_def)
  ];

val rarrays_manip_list = [] : (string * thm * thm * thm * thm * thm * thm) list;
val farrays_manip_list = [] : (string * thm * thm * thm * thm * thm) list;
val add_type_theories  = ([] : string list);
val store_pinv_def_opt = NONE : thm option;

(* Initialization *)

val _ = start_dynamic_init_fixed_store_translation
            refs_manip_list
            rarrays_manip_list
            farrays_manip_list
            store_hprop_name
            state_type
            exn_ri_def
            exn_functions
            add_type_theories
            store_pinv_def_opt;

val r = m_translate option_def;
val r = m_translate check_def;
val r = m_translate do_arith_def;
val r = m_translate do_reln_def;
val r = translate SAFEMOD_def;
val r = translate SAFEDIV_def;
val r = m_translate do_binop_def;
val r = m_translate do_fst_def;
val r = m_translate do_snd_def;
val r = m_translate do_ispair_def;
val r = translate subst_def;
val r = m_translate compute_eval_def;

val r = translate compute_init_state_def;
val r = m_translate_run compute_eval_run_def;

val () = Feedback.set_trace "TheoryPP.include_docs" 0;
val _ = (ml_translatorLib.clean_on_exit := true);

val _ = export_theory();

