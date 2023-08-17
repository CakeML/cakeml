(*
  Evaluation of compilation of a timeLang program
*)
open preamble
     time_to_targetTheory time_to_panTheory compilationLib taParserTheory;

val _ = new_theory "time_eval";

Definition comp_def:
  comp prog =
    let pan = time_to_pan$compile_prog prog in
    let word_prog = pan_to_word$compile_prog pan in
    let c = x64_backend_config in
    let c = c with clos_conf updated_by (λc. c with start := first_name) in
      from_word_0 c LN word_prog
End

(* evaluation *)

fun compile name prog = let
  fun ABBREV_CONV name tm = SYM (mk_abbrev name tm);
  val to_word_0_thm =
    “comp ^prog”
    |> REWR_CONV comp_def
    |> CONV_RULE (PATH_CONV "rr" EVAL THENC
                  PATH_CONV "r" (REWR_CONV LET_THM) THENC
                  PATH_CONV "r" BETA_CONV)
    |> CONV_RULE (PATH_CONV "rr" EVAL THENC
                  PATH_CONV "r" (REWR_CONV LET_THM) THENC
                  PATH_CONV "r" BETA_CONV)
    |> SIMP_RULE std_ss [crep_to_loopTheory.first_name_def,LET_THM]
    |> CONV_RULE (PATH_CONV "rr" (ABBREV_CONV "word_0_p"))
    |> CONV_RULE (PATH_CONV "rlr" (ABBREV_CONV "word_0_names"))
    |> CONV_RULE (PATH_CONV "rllr" (ABBREV_CONV "word_0_c"))
  val conf_tm = x64_backend_config_def |> concl |> dest_eq |> fst
  val word_0_tm = “(word_0_c, word_0_p, word_0_names)”
  val lab_prog_name = name
  val stack_to_lab_thm = compile_to_lab_new conf_tm word_0_tm lab_prog_name;
  val lab_prog_def = definition(mk_abbrev_name lab_prog_name)
  val code_name = (!intermediate_prog_prefix) ^ "code"
  val data_name = (!intermediate_prog_prefix) ^ "data"
  val config_name = (!intermediate_prog_prefix) ^ "config";
  val cbv_to_bytes = cbv_to_bytes_x64
  val from_word_0_thm =
    cbv_to_bytes stack_to_lab_thm lab_prog_def code_name
                 data_name config_name (name^".S");
  in from_word_0_thm end

(* example *)

val name = "flashing_led"
val prog = flashing_led_def |> concl |> rand;
val thm = compile name prog;

val name = "flashing_led_with_button"
val prog = flashing_led_with_button_def |> concl |> rand;
val thm = compile name prog;

val name = "flashing_led_with_invariant"
val prog = flashing_led_with_invariant_def |> concl |> rand;
val thm = compile name prog;

val _ = export_theory();
