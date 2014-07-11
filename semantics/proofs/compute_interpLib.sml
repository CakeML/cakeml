structure compute_interpLib = struct
open HolKernel boolLib bossLib lcsymtacs replTheory

  val add_datatype = compute_basicLib.add_datatype
  fun add_interp_compset compset = let
    local open interpTheory in
      val () = computeLib.add_thms
      [run_eval_def
      ,run_eval_dec_def
      ,run_eval_decs_def
      ,run_eval_top_def
      ,run_eval_prog_def
      ,result_return_def
      ] compset
    end
    in
      ()
    end

  val the_interp_compset = let 
    val c = wordsLib.words_compset ()
    val () = compute_basicLib.add_basic_compset c
    val () = compute_semanticsLib.add_ast_compset c
    val () = add_interp_compset c
    in
      c
    end

end
