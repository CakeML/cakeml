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

Type fMap = ``:(real expr # 'a) binTree``
Type typeMap = ``:mType fMap``
Type analysisResult = ``:((real # real) # real) fMap``

Definition updDefVars_def:
  updDefVars (x:real expr) (m:mType) (defVars:real expr -> mType option)
    (y:real expr) :mType option =
    if y = x then SOME m else defVars y
End

Definition toRExpMap_def:
  toRExpMap (tMap:typeMap) =
  \e. FloverMapTree_find e tMap
End

Definition toRTMap_def:
  toRTMap (Gamma: real expr -> mType option) (Var v) =
    (case Gamma (Var v) of
    |SOME m => SOME REAL
    |_ => NONE) /\
  toRTMap tMap e = SOME REAL
End

Theorem no_cycle_unop:
  !e u. e <> Unop u e
Proof
  Induct_on `e` \\ fs[expr_distinct]
QED

Theorem no_cycle_cast:
  !e m. e <> Downcast m e
Proof
  Induct_on `e` \\ fs[expr_distinct]
QED

Theorem no_cycle_binop_left:
  !e1 e2 b. e1 <> Binop b e1 e2
Proof
  Induct_on `e1` \\ fs[expr_distinct]
QED

Theorem no_cycle_binop_right:
  !e1 e2 b. e2 <> Binop b e1 e2
Proof
  Induct_on `e2` \\ fs[expr_distinct]
QED

Theorem no_cycle_fma_left:
  !e1 e2 e3. e1 <> Fma e1 e2 e3
Proof
  Induct_on `e1` \\ fs[expr_distinct]
QED

Theorem no_cycle_fma_center:
  !e1 e2 e3. e2 <> Fma e1 e2 e3
Proof
  Induct_on `e2` \\ fs[expr_distinct]
QED

Theorem no_cycle_fma_right:
  !e1 e2 e3. e3 <> Fma e1 e2 e3
Proof
  Induct_on `e3` \\ fs[expr_distinct]
QED

val _ = export_theory()
