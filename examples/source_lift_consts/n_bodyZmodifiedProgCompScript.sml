(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "n_bodyZmodifiedProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "z0" then (((1)/(1000), (1)/(5)):real#real)
  else if x = Short "y0" then (((1)/(1000), (6)/(1)):real#real)
  else if x = Short "x0" then (((1)/(1000), (6)/(1)):real#real)
  else if x = Short "vz0" then (((-1)/(10), (1)/(10)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "n_bodyZmodified")
    (Fun "x0"(Fun "y0"(Fun "z0"(Fun "vz0"
      (FpNoOptimise NoOpt
        (Let (SOME "dt")
        (App FpFromWord [Lit (Word64 (4591870180066957722w:word64))])
        (          (Let (SOME "solarMass")
          (App FpFromWord [Lit (Word64 (4630752910647379422w:word64))])
          (            (Let (SOME "distance")
            (App (FP_uop FP_Sqrt)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Add)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      Var (Short  "x0");
                      Var (Short  "x0")
                    ]);
                    (App (FP_bop FP_Mul)
                    [
                      Var (Short  "y0");
                      Var (Short  "y0")
                    ])
                  ]);
                  (App (FP_bop FP_Mul)
                  [
                    Var (Short  "z0");
                    Var (Short  "z0")
                  ])
                ])
              ])
            (              (Let (SOME "mag")
              (App (FP_bop FP_Div)
                [
                  Var (Short  "dt");
                  (App (FP_bop FP_Mul)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      Var (Short  "distance");
                      Var (Short  "distance")
                    ]);
                    Var (Short  "distance")
                  ])
                ])
              (                (Let (SOME "vzNew")
                (App (FP_bop FP_Sub)
                  [
                    Var (Short  "vz0");
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        Var (Short  "z0");
                        Var (Short  "solarMass")
                      ]);
                      Var (Short  "mag")
                    ])
                  ])
                (                  (Let (SOME "z_2")
                  (App (FP_bop FP_Add)
                    [
                      Var (Short  "z0");
                      (App (FP_bop FP_Mul)
                      [
                        Var (Short  "dt");
                        Var (Short  "vzNew")
                      ])
                    ])
                  (Var (Short  "z_2"))))))))))))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def false;

val _ = export_theory()
