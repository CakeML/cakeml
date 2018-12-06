(*
  compset for the lexer and parser.
*)
structure parsingComputeLib =
struct

open HolKernel boolLib bossLib
open cmlParseTheory cmlPEGTheory lexer_implTheory semanticsComputeLib

val add_parsing_compset = computeLib.extend_compset
  [computeLib.Defs
    [destResult_def
    (* ,parse_top_def
       ,cmlParseREPLTop_def *)
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
    ,pegf_def
    ,seql_def
    ,choicel_def
    ,mktokLf_def
    ,bindNT_def
    ,peg_linfix_def
    ,mk_linfix_def
    ,mk_rinfix_def
    ,parse_prog_def
    ]
  ,computeLib.Defs
    [lex_until_toplevel_semicolon_def
    ,get_token_eqn
    ,lex_aux_def
    ]
  ,computeLib.Extenders
    [semanticsComputeLib.add_ast_compset
    ,semanticsComputeLib.add_lexparse_compset
    ]
  ]

end
