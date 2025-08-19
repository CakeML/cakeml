(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
Theory rigidBodyProgComp
Libs
  exampleLib

val _ = translation_extends "cfSupport";

(** Precondition **)
Definition theAST_pre_def:
  theAST_pre =
  λ (x:(string,string) id).
    if x = (Short "x1")
    then ((- 15/1, 15/1):real#real)
    else if x = Short "x2"
    then ((- 15/1, 15/1))
    else if x = Short "x3"
    then ((- 15/1, 15/1))
    else (0,0)
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
Definition theAST_def:
theAST =
[Dlet unknown_loc (Pvar "rigidBody")
(Fun "x1" (Fun "x2" (Fun "x3" (FpOptimise Opt
(App (FP_bop FP_Sub) [
  (App (FP_bop FP_Add) [
    (App (FP_bop FP_Sub) [
      (App (FP_bop FP_Add) [
        (App (FP_bop FP_Mul) [
          (App (FP_bop FP_Mul) [
            (App (FP_bop FP_Mul) [
              (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))]);
              Var (Short  "x1") ]);
            Var (Short  "x2") ]);
          Var (Short  "x3") ]);
        (App (FP_bop FP_Mul) [
          (App (FP_bop FP_Mul) [
            (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))]);
            Var (Short  "x3") ]);
          Var (Short  "x3") ]) ]);
      (App (FP_bop FP_Mul) [
        (App (FP_bop FP_Mul) [
          (App (FP_bop FP_Mul) [
            Var (Short  "x2");
            Var (Short  "x1") ]);
        Var (Short  "x2") ]);
        Var (Short  "x3") ]) ]);
    (App (FP_bop FP_Mul) [
      (App (FP_bop FP_Mul) [
        (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))]);
        Var (Short  "x3") ]);
      Var (Short  "x3") ]) ]);
    Var (Short  "x2") ])))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

