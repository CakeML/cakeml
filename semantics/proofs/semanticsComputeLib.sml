(*
  compset for parts of the semantics, including the lexer.
*)
structure semanticsComputeLib :> semanticsComputeLib =
struct

open HolKernel boolLib bossLib
(*
open astTheory gramTheory semanticPrimitivesTheory evaluateTheory
     lexer_funTheory tokenUtilsTheory cmlPtreeConversionTheory
*)

structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars
                      (merge_grammars ["ast", "gram", "semanticPrimitives",
                                       "lexer_fun"])
end

open Parse

val add_namespace_compset = computeLib.extend_compset
  [computeLib.Defs
    [namespaceTheory.mk_id_def
(*  ,namespacePropsTheory.nsSub_compute_thm *)
    ,namespacePropsTheory.nsSub_compute_def
    ,namespacePropsTheory.alistSub_def
    ,namespacePropsTheory.alist_rel_restr_def
    ,namespaceTheory.nsDomMod_def
    ,namespaceTheory.nsDom_def
    ,namespaceTheory.nsAll2_def
    ,namespaceTheory.nsAll_def
    ,namespaceTheory.nsOptBind_def
    ,namespaceTheory.nsSing_def
    ,namespaceTheory.nsLift_def
    ,namespaceTheory.nsBindList_def
    ,namespaceTheory.nsBind_def
    ,namespaceTheory.alist_to_ns_def
    ,namespaceTheory.nsAppend_def
    ,namespaceTheory.nsEmpty_def
    ,namespaceTheory.nsLookupMod_def
    ,namespaceTheory.nsLookup_def
    ,namespaceTheory.id_to_mods_def
    ,namespaceTheory.id_to_n_def
    ,namespaceTheory.nsMap_def
    ],
   computeLib.Tys
    [``:('a,'b) namespace$id``
    ,``:('a,'b,'c) namespace$namespace``
    ]
  ]


val add_ast_compset = computeLib.extend_compset
  [computeLib.Defs
    [gramTheory.nt_distinct_ths
    ,miscTheory.opt_bind_def
    ,typeSystemTheory.is_value_def
    ,astTheory.pat_bindings_def
    ,typeSystemTheory.check_ctor_tenv_def
    ,typeSystemTheory.type_subst_def
    ,typeSystemTheory.check_freevars_def
    ,typeSystemTheory.check_freevars_ast_def
    ,typeSystemTheory.check_type_names_def
    ,typeSystemTheory.type_name_subst_def
    (*,typeSystemTheory.check_exn_tenv_def*)
    (*,typeSystemTheory.tid_exn_to_tc_def*)
    ,typeSystemTheory.build_ctor_tenv_def
    ,semanticPrimitivesTheory.check_dup_ctors_def
    ,semanticPrimitivesTheory.build_constrs_def
    ,semanticPrimitivesTheory.build_tdefs_def
    ,semanticPrimitivesTheory.result_case_def
    ,semanticPrimitivesTheory.match_result_case_def
    ,semanticPrimitivesTheory.combine_dec_result_def
    ,semanticPrimitivesTheory.build_rec_env_def
    ,semanticPrimitivesTheory.pmatch_def
    (*,astTheory.Texn_def
    ,astTheory.Tfn_def
    ,astTheory.Tint_def
    ,astTheory.Tref_def
    ,astTheory.Tstring_def
    ,astTheory.Tword8_def
    ,astTheory.Tword8array_def
    ,astTheory.TC_word_def*)
    ,primTypesTheory.prim_types_program_def
    ],
   computeLib.Tys
    [``:MMLnonT``
    (*,``:ast$top``
    ,``:ast$spec``*)
    ,``:ast$dec``
    ,``:ast$pat``
    ,``:ast$exp``
    ,``:stamp``
    ,``:ast$op``
    ,``:ast$lit``
    ,``:opb``
    ,``:ast$shift``
    ,``:ast$word_size``
    ,``:eq_result``
    ,``:'a sem_env``
    ,``:ast$ast_t``
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
      ,init_loc_def
      ,next_loc_def
      ,next_line_def
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
      ,ptree_StructName_def
      (*
      ,ptree_SignatureValue_def
      ,ptree_SpeclineList_def
      ,ptree_SpecLine_def
      *)
      ,ptree_Decl_def
      ,ptree_Expr_def
      ,mkAst_App_def
      ,Eseq_encode_def
      ,ptree_Pattern_def
      ,Papply_def
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
  [computeLib.Extenders [add_ast_compset, add_lexparse_compset,add_namespace_compset]]

end
