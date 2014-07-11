structure compute_semanticsLib = struct
open HolKernel boolLib bossLib lcsymtacs replTheory

  val add_datatype = compute_basicLib.add_datatype

  fun add_ast_compset compset =
  let
    val () = computeLib.add_thms
    [gramTheory.nt_distinct_ths
    ,libTheory.merge_def
    ,libTheory.bind_def
    ,libTheory.lookup_def
    ,libTheory.opt_bind_def
    ,libTheory.emp_def
    ,terminationTheory.is_value_def
    ,astTheory.pat_bindings_def
    ,astTheory.mk_id_def
    ,typeSystemTheory.merge_tenvC_def
    ,typeSystemTheory.check_ctor_tenv_def
    ,terminationTheory.check_freevars_def
    ,typeSystemTheory.check_exn_tenv_def
    ,typeSystemTheory.tid_exn_to_tc_def
    ,typeSystemTheory.build_ctor_tenv_def
    ,terminationTheory.check_dup_ctors_thm
    ,semanticPrimitivesTheory.int_to_string_def
    ,semanticPrimitivesTheory.string_to_string_def
    ,semanticPrimitivesTheory.string_escape_def
    ,semanticPrimitivesTheory.build_tdefs_def
    ,semanticPrimitivesTheory.all_env_to_menv_def
    ,semanticPrimitivesTheory.all_env_to_cenv_def
    ,semanticPrimitivesTheory.all_env_to_env_def
    ,semanticPrimitivesTheory.result_case_def
    ,semanticPrimitivesTheory.merge_envC_def
    ,semanticPrimitivesTheory.match_result_case_def
    ,terminationTheory.pmatch_def
    ] compset
    val () = add_datatype ``:MMLnonT`` compset
    val () = add_datatype ``:top`` compset
    val () = add_datatype ``:dec`` compset
    val () = add_datatype ``:pat`` compset
    val () = add_datatype ``:exp`` compset
    val () = add_datatype ``:tid_or_exn`` compset
    val () = add_datatype ``:op`` compset
    val () = add_datatype ``:lop`` compset
    val () = add_datatype ``:lit`` compset
    val () = add_datatype ``:opb`` compset
    val () = add_datatype ``:opn`` compset
    val () = add_datatype ``:'a id`` compset
    val () = add_datatype ``:eq_result`` compset
  in
    ()
  end

  fun add_lexparse_compset compset = let
    local open lexer_funTheory in
      val () = computeLib.add_thms
      [next_token_def
      ,next_sym_def
      ,token_of_sym_def
      ,read_while_def
      ,read_string_def
      ,skip_comment_def
      ,isSymbol_def
      ,isAlphaNumPrime_def
      ,is_single_char_symbol_def
      ,get_token_def
      ,processIdent_def
      ] compset
    end

    local open tokenUtilsTheory in
      val () = computeLib.add_thms
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
      ,isLongidT_def
      ,isWhitespaceT_def
      ,isString_def
      ,isAlphaSym_def
      ,isSymbolT_def
      ,isAlphaT_def
      ] compset
    end
    val () = add_datatype ``:symbol`` compset
    val () = add_datatype ``:token`` compset

    local open cmlPtreeConversionTheory in
      val () = computeLib.add_thms
      [tuplify_def
      ,ptree_REPLTop_def
      ,ptree_REPLPhrase_def
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
      ,ptree_Vlist1_def
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
      ,safeTL_def
      ,oHD_def
      ] compset
    end
    in
      ()
    end

  fun add_elab_compset compset = let
    local open elabTheory in
      val () = computeLib.add_thms
      [elab_prog_def
      ,elab_top_def
      ,elab_dec_def
      ,elab_decs_def
      ,terminationTheory.elab_t_def
      ,elab_td_def
      ,elab_spec_def
      ] compset
    end
    in
      ()
    end

  val the_semantics_compset = let 
    val c = wordsLib.words_compset ()
    val () = compute_basicLib.add_basic_compset c
    val () = add_ast_compset c
    val () = add_lexparse_compset c
    val () = add_elab_compset c
    in
      c
    end

end
