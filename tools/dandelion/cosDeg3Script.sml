(*
  Simple cosine of degree 3
*)
open realZeroLib bitArithLib preambleDandelion;

val _ = new_theory "cosDeg3";

val _ = realZeroLib.useBinary := false;

Definition cos_example_def:
  cos_example =
  <|
    transc := Fun Cos (Var "x") ;
poly := [
     4289449735  * inv ( 2 pow  32 );
     139975391  * inv ( 2 pow  33 );
     -2408138823  * inv ( 2 pow  32 );
     2948059219  * inv ( 2 pow  35 );
    ];
  eps :=  582015  * inv (2 pow 31 );
  iv := [ ("x",
    ( 858993459  * inv (2 pow 33 ),
      1  * inv (2 pow 0 )))];
  |>
End

Theorem checkerSucceeds = validateCert cos_example_def “8:num”;

val _ = export_theory();
