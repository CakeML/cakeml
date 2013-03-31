open HolKernel Parse boolLib bossLib

open mmlPEGTheory mmlPtreeConversionTheory
open monadsyntax

val _ = new_theory "mmlParse"

val destResult_def = Define`
  destResult (Result x) = x ∧
  destResult _ = NONE
`

val mmlParseExpr_def = Define`
  mmlParseExpr toks = do
    (toks', pts) <-
      destResult (peg_exec mmlPEG (nt (mkNT nE) I) toks [] done failed);
    ast <- ptree_Expr nE (HD pts);
    SOME(toks',ast)
  od
`;

val _ = export_theory()
