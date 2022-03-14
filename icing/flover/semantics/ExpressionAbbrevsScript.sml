(**
  Some abbreviations that require having defined expressions beforehand
  If we would put them in the Abbrevs file, this would create a circular
  dependency
**)
open FloverMapTheory ExpressionsTheory;
open preambleFloVer;

val _ = new_theory "ExpressionAbbrevs";

(**
We treat a function mapping an exprression arguing on fractions as value type
to pairs of intervals on rationals and rational errors as the analysis result
**)

val _ = type_abbrev ("fMap", ``:(real expr # 'a) binTree``);
val _ = type_abbrev ("typeMap", ``:mType fMap``);
val _ = type_abbrev ("analysisResult", ``:((real # real) # real) fMap``);

val updDefVars_def = Define `
  updDefVars (x:real expr) (m:mType) (defVars:real expr -> mType option)
    (y:real expr) :mType option =
    if y = x then SOME m else defVars y`;

val toRExpMap_def = Define `
  toRExpMap (tMap:typeMap) =
  \e. FloverMapTree_find e tMap`;

val toRTMap_def = Define `
  toRTMap (Gamma: real expr -> mType option) (Var v) =
    (case Gamma (Var v) of
    |SOME m => SOME REAL
    |_ => NONE) /\
  toRTMap tMap e = SOME REAL`;


val no_cycle_unop = store_thm (
  "no_cycle_unop",
  ``!e u. e <> Unop u e``,
  Induct_on `e` \\ fs[expr_distinct]);

val no_cycle_cast = store_thm (
  "no_cycle_cast",
  ``!e m. e <> Downcast m e``,
  Induct_on `e` \\ fs[expr_distinct])

val no_cycle_binop_left = store_thm (
  "no_cycle_binop_left",
  ``!e1 e2 b. e1 <> Binop b e1 e2``,
  Induct_on `e1` \\ fs[expr_distinct]);

val no_cycle_binop_right = store_thm (
  "no_cycle_binop_right",
  ``!e1 e2 b. e2 <> Binop b e1 e2``,
  Induct_on `e2` \\ fs[expr_distinct]);

val no_cycle_fma_left = store_thm (
  "no_cycle_fma_left",
  ``!e1 e2 e3. e1 <> Fma e1 e2 e3``,
  Induct_on `e1` \\ fs[expr_distinct]);

val no_cycle_fma_center = store_thm (
  "no_cycle_fma_center",
  ``!e1 e2 e3. e2 <> Fma e1 e2 e3``,
  Induct_on `e2` \\ fs[expr_distinct]);

val no_cycle_fma_right = store_thm (
  "no_cycle_fma_right",
  ``!e1 e2 e3. e3 <> Fma e1 e2 e3``,
  Induct_on `e3` \\ fs[expr_distinct]);

val _ = export_theory()
