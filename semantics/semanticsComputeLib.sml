structure semanticsComputeLib =
struct

open HolKernel boolLib bossLib
(*
open astTheory gramTheory semanticPrimitivesTheory terminationTheory
     lexer_funTheory tokenUtilsTheory cmlPtreeConversionTheory
*)

val add_ast_compset = computeLib.extend_compset
  [computeLib.Defs
    [gramTheory.nt_distinct_ths
    ,libTheory.opt_bind_def
    ,terminationTheory.is_value_def
    ,astTheory.pat_bindings_def
    ,astTheory.mk_id_def
    ,typeSystemTheory.check_ctor_tenv_def
    ,terminationTheory.type_subst_def
    ,terminationTheory.check_freevars_def
    ,terminationTheory.check_type_names_def
    ,terminationTheory.type_name_subst_def
    ,typeSystemTheory.check_exn_tenv_def
    ,typeSystemTheory.merge_mod_env_def
    ,typeSystemTheory.lookup_mod_env_def
    ,typeSystemTheory.tid_exn_to_tc_def
    ,typeSystemTheory.build_ctor_tenv_def
    ,terminationTheory.check_dup_ctors_thm
    ,semanticPrimitivesTheory.int_to_string_def
    ,semanticPrimitivesTheory.string_to_string_def
    ,semanticPrimitivesTheory.string_escape_def
    ,semanticPrimitivesTheory.build_tdefs_def
    ,semanticPrimitivesTheory.result_case_def
    ,semanticPrimitivesTheory.merge_alist_mod_env_def
    ,semanticPrimitivesTheory.match_result_case_def
    ,semanticPrimitivesTheory.combine_dec_result_def
    ,semanticPrimitivesTheory.lookup_alist_mod_env_def
    ,semanticPrimitivesTheory.build_rec_env_def
    ,terminationTheory.pmatch_def
    ,semanticPrimitivesTheory.no_dup_mods_def
    ,semanticPrimitivesTheory.no_dup_top_types_def
    ,astTheory.Texn_def
    ,astTheory.Tfn_def
    ,astTheory.Tint_def
    ,astTheory.Tref_def
    ,astTheory.Tstring_def
    ,astTheory.Tword8_def
    ,astTheory.Tword8array_def
    ,primTypesTheory.prim_types_program_def
    ],
   computeLib.Tys
    [``:MMLnonT``
    ,``:ast$top``
    ,``:ast$spec``
    ,``:ast$dec``
    ,``:ast$pat``
    ,``:ast$exp``
    ,``:tid_or_exn``
    ,``:ast$op``
    ,``:ast$lop``
    ,``:ast$lit``
    ,``:opb``
    ,``:opn``
    ,``:opw``
    ,``:ast$shift``
    ,``:'a ast$id``
    ,``:ast$word_size``
    ,``:eq_result``
    ,``:ast$tctor``
    ,``:ast$t``
    ,``:'a environment``
    ]]

val add_lexparse_compset = computeLib.extend_compset
  [computeLib.Defs
    let open lexer_funTheory in
      [next_token_def
      ,next_sym_def
      ,token_of_sym_def
      ,read_while_def
      ,read_string_def
      ,skip_comment_def
      ,isSymbol_def
      ,isAlphaNumPrime_def
      ,is_single_char_symbol_def
      ,processIdent_def
      ,mkCharS_def
      ,lexer_fun_def
      ]
    end,
   computeLib.Defs
    let open tokenUtilsTheory in
      [isInt_def
      ,isTyvarT_def
      ,destStringT_def
      ,destIntT_def
      ,destSymbolT_def
      ,destAlphaT_def
      ,destTOK_def
      ,destLf_def
      ,destTyvarPT_def
      ,destLongidT_def
      ,destCharT_def
      ,isLongidT_def
      ,isWhitespaceT_def
      ,isString_def
      ,isAlphaSym_def
      ,isSymbolT_def
      ,isAlphaT_def
      ,isCharT_def
      ]
    end,
   computeLib.Tys
    [``:symbol``
    ,``:token``
    ],
   computeLib.Defs
    let open cmlPtreeConversionTheory in
      [tuplify_def
      ,ptree_TopLevelDecs_def
      ,ptree_TopLevelDec_def
      ,ptree_Structure_def
      ,ptree_StructName_def
      ,ptree_SignatureValue_def
      ,ptree_SpeclineList_def
      ,ptree_SpecLine_def
      ,ptree_Decls_def
      ,ptree_Decl_def
      ,ptree_Expr_def
      ,mkAst_App_def
      ,Eseq_encode_def
      ,ptree_Pattern_def
      ,mkPatApp_def
      ,ptree_FQV_def
      ,ptree_V_def
      ,ptree_Op_def
      ,ptree_TypeDec_def
      ,ptree_DtypeDecl_def
      ,ptree_Dconstructor_def
      ,detuplify_def
      ,ptree_ConstructorName_def
      ,ptree_UQConstructorName_def
      ,ptree_TypeName_def
      ,ptree_Type_def
      ,ptree_linfix_def
      ,ptree_Tyop_def
      ,ptree_TyvarN_def
      ,ptree_UQTyop_def
      ,ptree_TypeAbbrevDec_def
      ,ptree_OptTypEqn_def
      ,mk_binop_def
      ,ptree_PbaseList1_def
      ,mkFun_def
      ,dePat_def
      ]
    end
  ]

val add_semantics_compset = computeLib.extend_compset
  [computeLib.Extenders [add_ast_compset, add_lexparse_compset]]

end
