(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "sineOrder3ProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "x" then (((-2)/(1), (2)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "sineOrder3")
    (Fun "x"
      (FpOptimise Opt
(App (FP_bop FP_Sub)
        [
          (App (FP_bop FP_Mul)
          [
            (App FpFromWord [Lit (Word64 (4606776461254110404w:word64))]);
            Var (Short  "x")
          ]);
          (App (FP_bop FP_Mul)
          [
            (App FpFromWord [Lit (Word64 (4593815956241110911w:word64))]);
            (App (FP_bop FP_Mul)
            [
              (App (FP_bop FP_Mul)
              [
                Var (Short  "x");
                Var (Short  "x")
              ]);
              Var (Short  "x")
            ])
          ])
        ])))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()