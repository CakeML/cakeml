open HolKernel Parse boolLib bossLib

open mmlPEGTheory mmlPtreeConversionTheory
open monadsyntax

val _ = new_theory "mmlParse"

val _ = overload_on ("mmlpegexec",
                     ``λn t. peg_exec mmlPEG (nt (mkNT n) I) t [] done failed``)

val destResult_def = Define`
  destResult (Result x) = x ∧
  destResult _ = NONE
`

val mmlParseExpr_def = Define`
  mmlParseExpr toks = do
    (toks', pts) <- destResult (mmlpegexec nE toks);
    ast <- ptree_Expr nE (HD pts);
    SOME(toks',ast)
  od
`;

val mmlParseDecls_def = Define`
  mmlParseDecls toks = do
    (toks', pts) <- destResult (mmlpegexec nDecls toks);
    ast <- ptree_Decls (HD pts);
    SOME(toks',ast)
  od
`

val parse_def = Define ` (* parses a few declarations, no junk is allowed at the end *)
  (parse : token list -> ast_prog option) tokens =
    OPTION_BIND (mmlParseDecls tokens)
      (\(ts,ast_decs).
          if ts <> [] then NONE else SOME (MAP Ast_Tdec ast_decs))
`;

val _ = export_theory()
