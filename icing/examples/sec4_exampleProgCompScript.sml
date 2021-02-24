(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "sec4_exampleProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "x" then (((1001)/(1000), (2)/(1)):real#real)
  else if x = Short "y" then (((1001)/(1000), (2)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "sec4_example")
    (Fun "x"(Fun "y"
      (FpOptimise Opt
        (Let (SOME "t")
        (App (FP_bop FP_Mul)
          [
            Var (Short  "x");
            Var (Short  "y")
          ])
        ((App (FP_bop FP_Div)
          [
            (App (FP_bop FP_Sub)
            [
              Var (Short  "t");
              (App FpFromWord [Lit (Word64 (4607182418800017408w:word64))])
            ]);
            (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Mul)
              [
                Var (Short  "t");
                Var (Short  "t")
              ]);
              (App FpFromWord [Lit (Word64 (4607182418800017408w:word64))])
            ])
          ]))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()