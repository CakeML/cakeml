structure compute_parsingLib = struct
open HolKernel boolLib bossLib lcsymtacs

  val add_datatype = compute_basicLib.add_datatype

  fun add_parsing_compset compset = let

    local open cmlParseTheory cmlPEGTheory in
      val () = computeLib.add_thms
      [destResult_def
      ,parse_top_def
      ,cmlParseREPLTop_def
      ,cmlParseExpr_def
      ,sumID_def
      ,tokeq_def
      ,cmlPEG_exec_thm
      ,peg_StructName_def
      ,peg_EbaseParen_def
      ,peg_EbaseParenFn_def
      ,peg_longV_def
      ,peg_V_def
      ,peg_TypeDec_def
      ,peg_UQConstructorName_def
      ,pnt_def
      ,try_def
      ,peg_nonfix_def
      ,pegf_def
      ,seql_def
      ,choicel_def
      ,mktokLf_def
      ,bindNT_def
      ,peg_linfix_def
      ,mk_linfix_def
      ,mk_rinfix_def
      ] compset
    end

    local open lexer_implTheory in
      val () = computeLib.add_thms
      [lex_until_toplevel_semicolon_def
      ,get_token_eqn
      ,lex_aux_def
      ] compset
    end

    in
      ()
    end

  val the_parsing_compset = let
    val c = wordsLib.words_compset ()
    val () = compute_semanticsLib.add_ast_compset c
    val () = compute_semanticsLib.add_lexparse_compset c
    val () = add_parsing_compset c
    in
      c
    end

end
