open realZeroLib bitArithLib preambleDandelion;

val _ = new_theory "expDeg4";



Definition exp_example_def:
  exp_example =
  <|
    transc := Fun Exp (Var "x");
    poly := [
        2251860978014963  * inv ( 2 pow  51 );
        2248839599087155  * inv ( 2 pow  51 );
        1148731941443245  * inv ( 2 pow  51 );
        2516578118969257  * inv ( 2 pow  54 );
        5022738147898817  * inv ( 2 pow  56 );
      ];
    eps :=  61174722613  * inv (2 pow 51 );
    iv := [
        ("x",
         ( 0 * inv (2 pow 0 ),
           1 * inv (2 pow 0 )))
      ];
  |>
End

Theorem checkerSucceeds = validateCert exp_example_def “16:num”;

val _ = export_theory();
