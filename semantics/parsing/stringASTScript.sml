open HolKernel Parse boolLib bossLib

open mmlParseTheory lexer_funTheory
open monadsyntax

val _ = new_theory "stringAST"

val stringAST_def = Define`
  stringAST s =
    do
      toks0 <- lexer_fun s ;
      let toks = FILTER (\t. ¬isWhitespaceT t) toks0 in
      mmlParseDecls toks
    od
`

val t = time (rhs o concl o EVAL)
        ``stringAST "datatype 'a list = Nil | Cons of 'a * 'a list;\n\
                    \val x = 3; fun f x = x + 1 val y = 4;"``
val expected =
  ``SOME
    ([] : token list,
     [Ast_Dtype
        [(["'a"],"list",
          [("Nil",[]);
           ("Cons",[Ast_Tvar "'a"; Ast_Tapp [Ast_Tvar "'a"] "list"])])];
      Ast_Dlet (Ast_Pvar "x") (Ast_Lit (IntLit 3));
      Ast_Dletrec
        [("f","x",
          Ast_App (Ast_App (Ast_Var "+") (Ast_Var "x"))
            (Ast_Lit (IntLit 1)))];
      Ast_Dlet (Ast_Pvar "y") (Ast_Lit (IntLit 4))])``
val _ = assert (aconv expected) t

val _ = export_theory()
