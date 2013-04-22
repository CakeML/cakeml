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

val _ = time EVAL ``stringAST "datatype 'a list = Nil | Cons of 'a * 'a list;\n\
                              \val x = 3; fun f x = x + 1 val y = 4;"``

val _ = export_theory()
