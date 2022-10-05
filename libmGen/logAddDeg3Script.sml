open realZeroLib bitArithLib libmLib preambleDandelion;

val _ = new_theory "logAddDeg3";



Definition log_example_def:
  log_example =
  <|
    transc := Fun Log (Bop Add (Var "x") (Cst (1/10))) ;
  poly := [
     -1550808607  * inv ( 2 pow  30 );
     641406787  * inv ( 2 pow  28 );
     -573949725  * inv ( 2 pow  29 );
     3766713447  * inv ( 2 pow  34 );
    ];
  eps :=  10535917144680386079769337698113777809575837070019  * inv (2 pow 186 );
  iv := [ ("x",
    ( 23407410223491741137950216280783988842809415608303  * inv (2 pow 164 ),
      12861214408511945680192426527903290572972206378189  * inv (2 pow 163 )))];
|>
End

Theorem log_cml_code_corr = implement log_example_def "log"

val _ = export_theory();
