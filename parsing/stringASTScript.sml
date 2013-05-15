open HolKernel Parse boolLib bossLib

open mmlParseTheory lexer_funTheory
open monadsyntax ASCIInumbersLib

val _ = new_theory "stringAST"

val stringAST_def = Define`
  stringAST s =
    do
      toks <- SOME (lexer_fun s) ;
      mmlParseREPLPhrase toks
    od
`

val stringDecs_def = Define`
  stringDecs s = OPTION_MAP (elab_prog [] [] init_env o SND) (stringAST s)
`

val t = time (rhs o concl o EVAL)
        ``stringAST "structure s = struct\n\
                    \  datatype 'a list = Nil \n\
                    \                   | Cons of 'a * 'a list;\n\
                    \end\n\
                    \val x = 3 fun f x = x + 1 val y = 4;"``
val expected =
  ``SOME
    ([] : token list,
     [Ast_Tmod "s" NONE [Ast_Dtype
        [(["'a"],"list",
          [("Nil",[]);
           ("Cons",[Ast_Tvar "'a"; Ast_Tapp [Ast_Tvar "'a"] (Short "list")])])]];
      Ast_Tdec (Ast_Dlet (Ast_Pvar "x") (Ast_Lit (IntLit 3)));
      Ast_Tdec (Ast_Dletrec
        [("f","x",
          Ast_App (Ast_App (Ast_Var (Short "+")) (Ast_Var (Short "x")))
            (Ast_Lit (IntLit 1)))]);
      Ast_Tdec (Ast_Dlet (Ast_Pvar "y") (Ast_Lit (IntLit 4)))])``
val _ = assert (aconv expected) t

val _ = export_theory()
