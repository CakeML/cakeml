(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "sumProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "x0" then (((1)/(1), (2)/(1)):real#real)
  else if x = Short "x1" then (((1)/(1), (2)/(1)):real#real)
  else if x = Short "x2" then (((1)/(1), (2)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "sum")
    (Fun "x0"(Fun "x1"(Fun "x2"
      (FpOptimise Opt
        (Let (SOME "p0")
        (App (FP_bop FP_Sub)
          [
            (App (FP_bop FP_Add)
            [
              Var (Short  "x0");
              Var (Short  "x1")
            ]);
            Var (Short  "x2")
          ])
        (          (Let (SOME "p1")
          (App (FP_bop FP_Sub)
            [
              (App (FP_bop FP_Add)
              [
                Var (Short  "x1");
                Var (Short  "x2")
              ]);
              Var (Short  "x0")
            ])
          (            (Let (SOME "p2")
            (App (FP_bop FP_Sub)
              [
                (App (FP_bop FP_Add)
                [
                  Var (Short  "x2");
                  Var (Short  "x0")
                ]);
                Var (Short  "x1")
              ])
            ((App (FP_bop FP_Add)
              [
                (App (FP_bop FP_Add)
                [
                  Var (Short  "p0");
                  Var (Short  "p1")
                ]);
                Var (Short  "p2")
              ])))))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()