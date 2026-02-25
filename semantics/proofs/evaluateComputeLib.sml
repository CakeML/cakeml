(*
  A compset for the operational semantics.
*)
structure evaluateComputeLib = struct
open HolKernel boolLib bossLib
open semanticPrimitivesTheory evaluateTheory

  val add_evaluate_compset = computeLib.extend_compset
    [computeLib.Extenders [semanticsComputeLib.add_ast_compset,semanticsComputeLib.add_namespace_compset]
    ,computeLib.Tys [``:'ffi semanticPrimitives$state``]
    ,computeLib.Defs
      [full_evaluate_def
      (*
      ,evaluate_tops_def
      ,evaluate_prog_def
      ,no_dup_types_def
      ,decs_to_types_def
      ,no_dup_mods_def
      ,prog_to_mods_def
      ,no_dup_top_types_def
      ,prog_to_top_types_def *)
      ,extend_dec_env_def
      (*,type_defs_to_new_tdecs_def*)
      ]
    ]

  val evaluate_conv = computeLib.compset_conv wordsLib.words_compset
    [computeLib.Extenders
       [basicComputeLib.add_basic_compset, add_evaluate_compset]]

end
