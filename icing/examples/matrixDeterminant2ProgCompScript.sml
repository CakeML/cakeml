(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "matrixDeterminant2ProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "a" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "b" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "c" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "d" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "e" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "f" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "g" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "h" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "i" then (((-10)/(1), (10)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "matrixDeterminant2")
    (Fun "a"(Fun "b"(Fun "c"(Fun "d"(Fun "e"(Fun "f"(Fun "g"(Fun "h"(Fun "i"
      (FpOptimise Opt
(App (FP_bop FP_Sub)
        [
          (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Mul)
            [
              Var (Short  "a");
              (App (FP_bop FP_Mul)
              [
                Var (Short  "e");
                Var (Short  "i")
              ])
            ]);
            (App (FP_bop FP_Add)
            [
              (App (FP_bop FP_Mul)
              [
                Var (Short  "g");
                (App (FP_bop FP_Mul)
                [
                  Var (Short  "b");
                  Var (Short  "f")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                Var (Short  "c");
                (App (FP_bop FP_Mul)
                [
                  Var (Short  "d");
                  Var (Short  "h")
                ])
              ])
            ])
          ]);
          (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Mul)
            [
              Var (Short  "e");
              (App (FP_bop FP_Mul)
              [
                Var (Short  "c");
                Var (Short  "g")
              ])
            ]);
            (App (FP_bop FP_Add)
            [
              (App (FP_bop FP_Mul)
              [
                Var (Short  "i");
                (App (FP_bop FP_Mul)
                [
                  Var (Short  "b");
                  Var (Short  "d")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                Var (Short  "a");
                (App (FP_bop FP_Mul)
                [
                  Var (Short  "f");
                  Var (Short  "h")
                ])
              ])
            ])
          ])
        ])))))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()