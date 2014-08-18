structure compute_inferenceLib = struct
  open HolKernel boolLib bossLib lcsymtacs

  fun add_inference_compset compset =
  let

    val () = compute_semanticsLib.add_ast_compset compset

    val get_wfs = unifyLib.add_unify_compset compset

    open inferTheory
    val () = computeLib.add_thms
    [infer_prog_def
    ,infer_top_def
    ,infer_d_def
    ,infer_ds_def
    ,infer_e_def
    ,infer_p_def
    ,st_ex_bind_def
    ,st_ex_return_def
    ,failwith_def
    ,lookup_tenvC_st_ex_def
    ,lookup_st_ex_def
    ,init_state_def
    ,init_infer_state_def
    ,get_next_uvar_def
    ,fresh_uvar_def
    ,n_fresh_uvar_def
    ,guard_def
    ,add_constraint_def
    ,add_constraints_def
    ,read_def
    ,generalise_def
    ,apply_subst_list_def
    ,append_decls_def
    ,constrain_op_def
    ,infer_deBruijn_subst_def
    ,Infer_Tfn_def
    ,Infer_Tint_def
    ,Infer_Tbool_def
    ,Infer_Tref_def
    ,Infer_Tunit_def
    ,infer_type_subst_def
    ,check_signature_def
    ,exc_case_def
    ] compset

    val () = compute_basicLib.add_datatype ``:infer_t`` compset
    val () = compute_basicLib.add_datatype ``:atom`` compset
    val () = compute_basicLib.add_datatype ``:('a,'b)exc`` compset
    val () = compute_basicLib.add_datatype ``:'a infer_st`` compset
  in
   get_wfs
  end

  val the_inference_compset = let
    val c = wordsLib.words_compset ()
    val get_wfs = add_inference_compset c
  in
    c
  end

end
