open realLib realZeroLib bitArithLib;
open preambleDandelion;

val _ = new_theory "cosDeg5";

Definition cos_example_def:
  cos_example =
<|
  transc := Fun Cos (Var "x");
  poly := [
     2147500729  * inv ( 2 pow  31 );
     -1335232053  * inv ( 2 pow  43 );
     -4286087759  * inv ( 2 pow  33 );
     -1814406069  * inv ( 2 pow  39 );
     3231673215  * inv ( 2 pow  36 );
     -2371596027  * inv ( 2 pow  39 );
    ];
  eps :=  30519469678010330798002460719449001203933634455913  * inv (2 pow 186 );
  iv := [ ("x",
    ( 37414441915671114706014331717536845303191873100185  * inv (2 pow 168 ),
      1  * inv (2 pow 0 )))];
|>
End

Theorem checkerSucceeds = validateCert cos_example_def “16:num”;

val _ = export_theory();
