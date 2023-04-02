(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "intro_exampleProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "t" then (((0)/(1), (999)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "intro_example")
    (Fun "t"
      (FpNoOptimise NoOpt
(App (FP_bop FP_Div)
        [
          Var (Short  "t");
          (App (FP_bop FP_Add)
          [
            Var (Short  "t");
            (App FpFromWord [Lit (Word64 (4607182418800017408w:word64))])
          ])
        ])))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()