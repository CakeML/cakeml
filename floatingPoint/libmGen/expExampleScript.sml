(*
  Example libm function generated from cosine certificate of Dandelion
*)
open libmLib;

val _ = new_theory "expExample";

Definition exp_example_def:
  exp_example =
  <|
    transc := Bop Add (Fun Exp (Bop Mul (Var "x") (Cst (1/2:real)))) (Fun Cos (Bop Mul (Var "x") (Cst (1/2:real))));
poly := [
     9007199045267507  * inv ( 2 pow  52 );
     4503607326537297  * inv ( 2 pow  53 );
     -3241616109733325  * inv ( 2 pow  69 );
     375588665660545  * inv ( 2 pow  54 );
     5979080956143783  * inv ( 2 pow  60 );
     5038332231908613  * inv ( 2 pow  64 );
    ];
  eps :=  27896958177787588423236394485375286824270176601341  * inv (2 pow 192 );
  iv := [ ("x",
    ( 37414441915671114706014331717536845303191873100185  * inv (2 pow 168 ),
      1  * inv (2 pow 0 )))];
  |>
End

Theorem cos_cml_code_corr = implement exp_example_def "exp_add_cos"

val _ = export_theory();
