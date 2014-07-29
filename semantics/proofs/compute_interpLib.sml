structure compute_interpLib = struct
open HolKernel boolLib bossLib lcsymtacs bigStepTheory replTheory

  val add_datatype = compute_basicLib.add_datatype
  fun add_interp_compset compset = let
    local open interpTheory in
      val () = compute_semanticsLib.add_ast_compset compset
      
      val () = computeLib.add_thms
      [run_eval_def
      ,run_eval_dec_def
      ,run_eval_decs_def
      ,run_eval_top_def
      ,run_eval_prog_def
      ,run_eval_whole_prog_def
      ,result_return_def
      ,result_bind_def
      ,result_raise_def
      ,no_dup_types_def
      ,decs_to_types_def
      ,no_dup_mods_def
      ,prog_to_mods_def
      ,no_dup_top_types_def
      ,prog_to_top_types_def
      ,bigClockTheory.set_counter_def
      ] compset
    end
    in
      ()
    end

  val the_interp_compset = let
    val c = wordsLib.words_compset ()
    val () = add_interp_compset c
    in
      c
    end

end
