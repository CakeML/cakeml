structure inferenceComputeLib = struct
  open HolKernel boolLib bossLib lcsymtacs
  open infer_tTheory inferTheory

  (* TODO: this should be in another syntax lib *)
  val (Success_tm,mk_Success,dest_Success,is_Success) = syntax_fns1 "ml_monadBase" "Success"
  (* -- *)

  val add_inference_compset = computeLib.extend_compset
  [computeLib.Defs (* TODO: these should probably be in another computeLib instead *)
   [ml_monadBaseTheory.st_ex_bind_def
   ,ml_monadBaseTheory.st_ex_return_def
   ,ml_monadBaseTheory.run_def
   ], computeLib.Tys [``:('a,'b)exc``],
   computeLib.Defs
    [id_to_string_def
    ,inf_type_to_string_def
    ,tc_to_string_def
    ,infer_prog_def
    ,infer_top_def
    ,infer_d_def
    ,infer_ds_def
    ,infer_e_def
    ,infer_p_def
    ,guard_def
    ,raise_Exc_def
    ,handle_Exc_def
    ,set_next_uvar_def
    ,get_next_uvar_def
    ,set_subst_def
    ,get_subst_def
    ,lookup_st_ex_def
    ,sub_completion_def
    ,t_to_freevars_def
    ,check_s_def
    ,ienv_val_ok_def
    ,check_t_def
    ,pure_add_constraints_def
    ,infer_subst_def
    ,infer_deBruijn_inc_def
    ,Infer_Tref_def
    ,Infer_Tunit_def
    ,Infer_Tbool_def
    ,Infer_Tint_def
    ,Infer_Tfn_def
    ,init_config_def
    ,infertype_prog_def
    ,infertype_prog_aux_def
    ,ienvLift_def
    ,check_signature_def
    ,check_weak_ienv_def
    ,check_tscheme_inst_def
    ,check_tscheme_inst_aux_def
    ,run_check_tscheme_inst_aux_def
    ,check_weak_decls_def
    ,check_specs_def
    ,extend_dec_ienv_def
    ,append_decls_def
    ,empty_inf_decls_def
    ,constrain_op_def
    ,infer_deBruijn_subst_def
    ,infer_type_subst_def
    ,generalise_def
    ,apply_subst_list_def
    ,apply_subst_def
    ,get_next_uvar_def
    ,add_constraints_def
    ,add_constraint_def
    ,init_state_def
    ,init_infer_state_def
    ,n_fresh_uvar_def
    ,fresh_uvar_def
    ],
   computeLib.Tys
    [``:infer_t``
    ,``:infer_st``
    ,``:inferencer_config``
    ,``:inf_decls``
    ,``:inf_env``
    ]
    ,computeLib.Extenders
    [semanticsComputeLib.add_ast_compset
    ,semanticsComputeLib.add_namespace_compset
     (* add_unify_compset returns a function to retrieve the wfs theorems, which we ignore *)
    ,ignore o unifyLib.add_unify_compset
    ]
  ]

end
