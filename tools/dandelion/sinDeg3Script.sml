(*
  Simple approximation of sine of degree 3
*)
(* open bitArithLib; *)

(* val _ = bitArithLib.use_karatsuba(); *)

open realZeroLib;

val _ = new_theory "sinDeg3";

Definition sin_example_def:
  sin_example = <|
    transc := Fun Sin (Var "x") ;
    poly := [
        -1499276771  * inv ( 2 pow  41 );
        541190871  * inv ( 2 pow  29 );
        -3581686363  * inv ( 2 pow  37 );
        -1202115613  * inv ( 2 pow  33 );
      ];
    eps :=  946027  * inv (2 pow 32 );
    iv := [ ("x",
             ( 858993459  * inv (2 pow 33 ),
               1  * inv (2 pow 0 )))];
  |>
End

Theorem checkerSucceeds = validateCert sin_example_def “8:num”;

val _ = export_theory();
