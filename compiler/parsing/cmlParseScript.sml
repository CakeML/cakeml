open HolKernel Parse boolLib bossLib
     cmlPEGTheory cmlPtreeConversionTheory

val _ = new_theory "cmlParse"
val _ = set_grammar_ancestry ["cmlPEG", "cmlPtreeConversion"]
val _ = monadsyntax.temp_add_monadsyntax()

val _ = overload_on ("cmlpegexec",
                     ``λn t. peg_exec cmlPEG (pnt n) t [] done failed``)

val destResult_def = Define`
  destResult (Result (SOME x)) = SOME x ∧
  destResult _ = NONE
`;

val cmlParseExpr_def = Define`
  cmlParseExpr toks = do
    (toks', pts) <- destResult (cmlpegexec nE toks);
    pt <- oHD pts;
    ast <- ptree_Expr nE pt;
    SOME(toks', ast)
  od
`;

val parse_prog_def = Define`
  parse_prog toks =
    do
      (toks',pts) <- destResult (cmlpegexec nTopLevelDecs toks);
      pt <- oHD pts;
      tds <- ptree_TopLevelDecs pt;
      if toks' <> [] then NONE else SOME tds
    od
`;

val _ = export_theory()
