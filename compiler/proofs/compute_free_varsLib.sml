structure compute_free_varsLib = struct local
open HolKernel boolLib bossLib computeLib
open evalPropsTheory free_varsTheory
in
  val add_free_vars_compset = add_thms
    [closed_prog_def
    ,FV_prog_def
    ,new_top_vs_def
    ,new_dec_vs_def
    ,FV_top_def
    ,global_dom_def
    ,FV_decs_def
    ,FV_dec_def
    ,FV_def
    ]

  fun the_free_vars_compset () =
    let
      val c = compute_basicLib.the_basic_compset
      val () = compute_semanticsLib.add_ast_compset c
      val () = add_free_vars_compset c
    in c end
end
end
