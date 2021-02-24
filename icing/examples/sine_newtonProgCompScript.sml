(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "sine_newtonProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "x0" then (((-1)/(1), (1)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "sine_newton")
    (Fun "x0"
      (FpOptimise Opt
        (Let (SOME "x_2")
        (App (FP_bop FP_Sub)
          [
            Var (Short  "x0");
            (App (FP_bop FP_Div)
            [
              (App (FP_bop FP_Add)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Sub)
                  [
                    Var (Short  "x0");
                    (App (FP_bop FP_Div)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          Var (Short  "x0");
                          Var (Short  "x0")
                        ]);
                        Var (Short  "x0")
                      ]);
                      (App FpFromWord [Lit (Word64 (4618441417868443648w:word64))])
                    ])
                  ]);
                  (App (FP_bop FP_Div)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            Var (Short  "x0");
                            Var (Short  "x0")
                          ]);
                          Var (Short  "x0")
                        ]);
                        Var (Short  "x0")
                      ]);
                      Var (Short  "x0")
                    ]);
                    (App FpFromWord [Lit (Word64 (4638144666238189568w:word64))])
                  ])
                ]);
                (App (FP_bop FP_Div)
                [
                  (App (FP_bop FP_Mul)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              Var (Short  "x0");
                              Var (Short  "x0")
                            ]);
                            Var (Short  "x0")
                          ]);
                          Var (Short  "x0")
                        ]);
                        Var (Short  "x0")
                      ]);
                      Var (Short  "x0")
                    ]);
                    Var (Short  "x0")
                  ]);
                  (App FpFromWord [Lit (Word64 (4662263553305083904w:word64))])
                ])
              ]);
              (App (FP_bop FP_Add)
              [
                (App (FP_bop FP_Add)
                [
                  (App (FP_bop FP_Sub)
                  [
                    (App FpFromWord [Lit (Word64 (4607182418800017408w:word64))]);
                    (App (FP_bop FP_Div)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        Var (Short  "x0");
                        Var (Short  "x0")
                      ]);
                      (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))])
                    ])
                  ]);
                  (App (FP_bop FP_Div)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          Var (Short  "x0");
                          Var (Short  "x0")
                        ]);
                        Var (Short  "x0")
                      ]);
                      Var (Short  "x0")
                    ]);
                    (App FpFromWord [Lit (Word64 (4627448617123184640w:word64))])
                  ])
                ]);
                (App (FP_bop FP_Div)
                [
                  (App (FP_bop FP_Mul)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            Var (Short  "x0");
                            Var (Short  "x0")
                          ]);
                          Var (Short  "x0")
                        ]);
                        Var (Short  "x0")
                      ]);
                      Var (Short  "x0")
                    ]);
                    Var (Short  "x0")
                  ]);
                  (App FpFromWord [Lit (Word64 (4649544402794971136w:word64))])
                ])
              ])
            ])
          ])
        (Var (Short  "x_2")))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()