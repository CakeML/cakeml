(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
Theory invertedPendulumProgComp
Libs
  exampleLib

val _ = translation_extends "cfSupport";

(** Precondition **)
Definition theAST_pre_def:
  theAST_pre =
    λ (x:(string, string) id).
      if x = Short "s1"
      then ((-50/1, 50/1):real#real)
      else if x = Short "s2"
      then (-10/1, 10/1)
      else if x = Short "s3"
      then (-785/1000, 785/1000)
      else if x = Short "s4"
      then (-785/1000, 785/1000)
      else (0,0)
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
Definition theAST_def:
  theAST =
    [Dlet unknown_loc (Pvar "invertedPendulum")
      (Fun "s1" (Fun "s2" (Fun "s3" (Fun "s4"
        (FpOptimise Opt
         (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Add)
             [
               (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Mul)
                   [
                     (App FpFromWord [Lit (Word64 (4607182418800017408w:word64))]);
                     Var (Short  "s1")
                   ]);
                  (App (FP_bop FP_Mul)
                   [
                     (App FpFromWord [Lit (Word64 (4610139932675311613w:word64))]);
                     Var (Short  "s2")
                   ])
                ]);
               (App (FP_bop FP_Mul)
                [
                  (App FpFromWord [Lit (Word64 (-4597419346642817620w:word64))]);
                  Var (Short  "s3")
                ])
             ]);
            (App (FP_bop FP_Mul)
             [
               (App FpFromWord [Lit (Word64 (-4608399741779295653w:word64))]);
               Var (Short  "s4")
             ])
          ]))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

