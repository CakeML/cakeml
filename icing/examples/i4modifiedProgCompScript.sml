(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "i4modifiedProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "x" then (((1)/(10), (10)/(1)):real#real)
  else if x = Short "y" then (((0)/(1), (5)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "i4modified")
    (Fun "x"(Fun "y"
      (FpOptimise Opt
(App (FP_uop FP_Sqrt)
        [
          (App (FP_bop FP_Add)
          [
            Var (Short  "x");
            (App (FP_bop FP_Mul)
            [
              Var (Short  "y");
              Var (Short  "y")
            ])
          ])
        ]))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()
