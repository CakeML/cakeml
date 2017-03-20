structure inferenceComputeLib = struct
  open HolKernel boolLib bossLib lcsymtacs
  open inferTheory

  val add_inference_compset = computeLib.extend_compset
  [computeLib.Defs
    [infer_prog_def
    ,infer_top_def
    ,infer_d_def
    ,infer_ds_def
    ,infer_e_def
    ,infer_p_def
    ,st_ex_bind_def
    ,st_ex_return_def
    ,failwith_def
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
    (*,apply_subst_def*)
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
    ,check_specs_def
    ,t_to_freevars_def
    ,check_weak_decls_def
    ,check_weak_ienv_def
    ,check_tscheme_inst_def
    ,list_subset_def
    ,init_config_def
    ,infertype_prog_def
    ,empty_inf_decls_def
    ,extend_dec_ienv_def
    ,ienvLift_def
    ,id_to_string_def
    ,list_set_eq_def
    ,list_subset_def
    ,astTheory.TC_word_def (* TODO: Maybe should be in semantics compset? the inferencer is the only thing that ever uses this though*)
    ],
   computeLib.Tys
    [``:infer_t``
    ,``:atom``
    ,``:('a,'b)exc``
    ,``:'a infer_st``
    ,``:inferencer_config``
    ,``:inf_decls``
    ,``:inf_env``
    ]
    ,computeLib.Extenders
    [semanticsComputeLib.add_ast_compset
    ,semanticsComputeLib.add_namespace_compset
    ,fn compset => (unifyLib.add_unify_compset compset; ())
    ]
  ]

end
