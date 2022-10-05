(**
  Example file for libmGen, generates an approximation of
  tan^-1 with degree 3
**)
open realZeroLib bitArithLib libmLib preambleDandelion;

val _ = new_theory "atnDeg3";

val _ = realZeroLib.useBinary := false;
val _ = realZeroLib.createMetiTarskiQuery := false;

Definition cos_example_def:
  cos_example =
  <|
  transc := Fun Atn (Var "x");
  poly := [
     -6809284315197713  * inv ( 2 pow  84 );
     8979859070570549  * inv ( 2 pow  53 );
     2502429001398681  * inv ( 2 pow  78 );
     -2531269759855903  * inv ( 2 pow  53 );
    ];
  eps :=  77569196655847480248172279652945299732867702355  * inv (2 pow 167 );
  iv := [ ("x",
    ( -1  * inv (2 pow 1 ),
      1  * inv (2 pow 1 )))];
|>
End

Theorem atn_cml_code_corr = implement cos_example_def "atn"

val _ = export_theory();
