(*
  Shared CakeML compiler translation for the native entry points.
*)
Theory compiler_commonProg[no_sig_docs]
Ancestors
  printingProg compiler compiler_common export ml_translator basis_ffi[qualified]
Libs
  preamble ml_translatorLib cfLib basis

val _ = temp_delsimps ["NORMEQ_CONV", "lift_disj_eq", "lift_imp_disj"]

val _ = translation_extends "printingProg";

val _ = ml_translatorLib.ml_prog_update (ml_progLib.open_module "compilerProg");
val _ = ml_translatorLib.use_sub_check true;

val _ = (ml_translatorLib.trace_timing_to
         := SOME "compiler_commonProg_translate_timing.txt")

val () = Globals.max_print_depth := 15;

val () = use_long_names := true;

val r = translate presLangTheory.default_tap_config_def;


val r = backend_passesTheory.to_flat_all_def |> translate;
val r = backend_passesTheory.to_clos_all_def |> translate;
val r = backend_passesTheory.to_bvl_all_def |> translate;
val r = backend_passesTheory.to_bvi_all_def |> translate;

Theorem backend_passes_to_bvi_all_side[local]:
  backend_passes_to_bvi_all_side c p
Proof
  fs [fetch "-" "backend_passes_to_bvi_all_side_def"]
  \\ rewrite_tac [GSYM LENGTH_NIL,bvl_inlineTheory.LENGTH_remove_ticks]
  \\ fs []
QED

val _ = update_precondition backend_passes_to_bvi_all_side

val r = backend_passesTheory.to_data_all_def |> translate;

val r = backend_passesTheory.to_word_all_def
          |> REWRITE_RULE [data_to_wordTheory.stubs_md_def,
                           data_to_wordTheory.stubs_def,APPEND] |> translate;

val r = backend_passesTheory.to_stack_all_def |> translate;

val r = backend_passesTheory.to_lab_all_def |> translate;

val r = backend_passesTheory.to_target_all_def |> translate;

val r = backend_passesTheory.compile_tap_def |> translate;

val _ = r |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "backend_passesTheory.compile_tap_def.");

(* compilerTheory *)

val _ = translate compilerTheory.ast_locs_to_string_def;
val _ = translate compilerTheory.parse_cml_input_def;
val _ = translate compilerTheory.parse_sexp_input_def;

val res = translate compilerTheory.compile_def;

val res = translate (primTypesTheory.prim_tenv_def
                       |> CONV_RULE (RAND_CONV EVAL));

(* top-level vals must not call functions (no_ptr_eq), so evaluate the
   projections from prim_tenv *)
val res = translate (inferTheory.init_config_def
                     |> CONV_RULE (RAND_CONV EVAL));

val res = translate error_to_str_def;

val res = translate (parse_top_config_def |> SIMP_RULE (srw_ss()) []);

(* Leave the module now, so that key things are available in the toplevel
   namespace for main. *)
val _ = ml_translatorLib.ml_prog_update (ml_progLib.close_module NONE);

(* Rest of the translation *)

val res = format_compiler_result_def
            |> Q.GENL[`bytes`,`c`]
            |> Q.ISPECL[`bytes:word8 list`,`c:backend$config`]

            |> translate;


val res = translate compile_main_def;

val _ = res |> hyp |> null orelse
        failwith ("Unproved side condition in the translation of " ^
                  "compile_main_def.");

val res = translate current_build_info_str_def
val res = translate compilerTheory.help_string_def;

Definition nonzero_exit_code_for_error_msg_def:
  nonzero_exit_code_for_error_msg e =
  if compiler_common$is_error_msg e then
    (let a = empty_ffi «nonzero_exit» in
       ml_translator$force_out_of_memory_error ())
  else ()
End

val res = translate nonzero_exit_code_for_error_msg_def;
