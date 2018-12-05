(*
  Compset for evaluating the functional big-step semantics.
*)
structure interpComputeLib = struct
open HolKernel boolLib bossLib
open semanticPrimitivesTheory bigStepTheory interpTheory

  val add_interp_compset = computeLib.extend_compset
    [computeLib.Extenders [semanticsComputeLib.add_ast_compset]
    ,computeLib.Tys [``:'ffi semanticPrimitives$state``]
    ,computeLib.Defs
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
      ,extend_top_env_def
      ,extend_dec_env_def
      ]
    ]

  val interp_conv = computeLib.compset_conv (wordsLib.words_compset())
    [computeLib.Extenders
       [basicComputeLib.add_basic_compset, add_interp_compset]]

end
