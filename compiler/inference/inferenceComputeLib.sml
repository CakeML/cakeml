(*
  A compset for the type inferencer. This is to make it easy to
  evaluate the type inferencers inside the logic. See tests.
*)
structure inferenceComputeLib = struct
  open HolKernel boolLib bossLib lcsymtacs
  open infer_tTheory inferTheory

  (* val (Success_tm,mk_Success,dest_Success,is_Success) = syntax_fns1 "ml_monadBase" "Success" *)

  val add_inference_compset = computeLib.extend_compset
  [computeLib.Defs
    [id_to_string_def
    ,op_to_string_def
    ,type_name_check_subst_def
    ,check_dups_def
    ,check_type_definition_def
    ,check_ctors_def
    ,check_ctor_types_def
    ,inf_type_to_string_def
    ,infer_d_def
    ,infer_e_def
    ,infer_p_def
    (*,ml_monadBaseTheory.run_def
    ,ml_monadBaseTheory.st_ex_bind_def
    ,ml_monadBaseTheory.st_ex_return_def*)
    ,inferTheory.st_ex_bind_def
    ,inferTheory.st_ex_return_def
    ,inferTheory.guard_def
    ,lookup_st_ex_def
    ,sub_completion_def
    ,check_s_def
    ,ienv_val_ok_def
    ,check_t_def
    ,pure_add_constraints_def
    ,infer_subst_def
    ,infer_deBruijn_inc_def
    ,init_config_def
    ,infertype_prog_def
    ,get_next_uvar_def
    ,extend_dec_ienv_def
    ,constrain_op_dtcase_def
    ,op_simple_constraints_def
    ,op_n_args_msg_def
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
    ,inferTheory.n_fresh_id_def
    ,inferTheory.start_type_id_def
    ,read_def
    ,write_def
    ,failwith_def
    ,locationTheory.unknown_loc_def
    ,mlstringTheory.implode_def
    ,mlstringTheory.concat_def
    ,typeSystemTheory.Tarray_num_def
    ,typeSystemTheory.Tbool_num_def
    ,typeSystemTheory.Tchar_num_def
    ,typeSystemTheory.Texn_num_def
    ,typeSystemTheory.Tfn_num_def
    ,typeSystemTheory.Tint_num_def
    ,typeSystemTheory.Tlist_num_def
    ,typeSystemTheory.Tref_num_def
    ,typeSystemTheory.Tstring_num_def
    ,typeSystemTheory.Ttup_num_def
    ,typeSystemTheory.Tvector_num_def
    ,typeSystemTheory.Tword64_num_def
    ,typeSystemTheory.Tword8_num_def
    ,typeSystemTheory.Tword8array_num_def

    ,typeSystemTheory.Tlist_def
    ,typeSystemTheory.Tarray_def
    ,typeSystemTheory.Tbool_def
    ,typeSystemTheory.Tchar_def
    ,typeSystemTheory.Texn_def
    ,typeSystemTheory.Tfn_def
    ,typeSystemTheory.Tint_def
    ,typeSystemTheory.Tref_def
    ,typeSystemTheory.Tstring_def
    ,typeSystemTheory.Ttup_def
    ,typeSystemTheory.Tvector_def
    ,typeSystemTheory.Tword64_def
    ,typeSystemTheory.Tword8_def
    ,typeSystemTheory.Tword8array_def

    ,primTypesTheory.prim_tenv_def
    ,inferTheory.lift_ienv_def
    ,infer_tTheory.ty_var_name_def
    ,infer_tTheory.get_tyname_def
    ,infer_tTheory.commas_def
    ,infer_tTheory.add_parens_def
    ,infer_tTheory.type_ident_to_string_def
    ,mlintTheory.toString_def
    ,mlintTheory.toChar_def
    ,mlintTheory.maxSmall_DEC_def
    ,mlstringTheory.str_def
    ,inferTheory.word_tc_def
    ],
   computeLib.Tys
    [``:infer_t``
    (*,``:('a,'b)exc``*)
    ,``:('a,'b)infer$exc``
    ,``:infer_st``
    ,``:inf_env``
    ,``:mlstring``
    ,``:tenv_ctor``
    ,``:tenv_abbrev``
    ,``:type_env``
    ,``:loc_err_info``
    ]
    ,computeLib.Extenders
    [semanticsComputeLib.add_ast_compset
    ,semanticsComputeLib.add_namespace_compset
     (* add_unify_compset returns a function to retrieve the wfs theorems, which we ignore *)
    ,ignore o unifyLib.add_unify_compset
    ]
  ]

end
