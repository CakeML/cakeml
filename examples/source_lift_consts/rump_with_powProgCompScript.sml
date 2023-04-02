(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "rump_with_powProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "a" then (((70000)/(1), (80000)/(1)):real#real)
  else if x = Short "b" then (((30000)/(1), (34000)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "rump_with_pow")
    (Fun "a"(Fun "b"
      (FpNoOptimise NoOpt
(App (FP_bop FP_Add)
        [
          (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Add)
            [
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (4644579008283934720w:word64))]);
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
                          Var (Short  "b");
                          Var (Short  "b")
                        ]);
                        Var (Short  "b")
                      ]);
                      Var (Short  "b")
                    ]);
                    Var (Short  "b")
                  ]);
                  Var (Short  "b")
                ])
              ]);
              (App (FP_bop FP_Mul)
              [
                (App (FP_bop FP_Mul)
                [
                  Var (Short  "a");
                  Var (Short  "a")
                ]);
                (App (FP_bop FP_Sub)
                [
                  (App (FP_bop FP_Sub)
                  [
                    (App (FP_bop FP_Sub)
                    [
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App FpFromWord [Lit (Word64 (4622382067542392832w:word64))]);
                          (App (FP_bop FP_Mul)
                          [
                            Var (Short  "a");
                            Var (Short  "a")
                          ])
                        ]);
                        (App (FP_bop FP_Mul)
                        [
                          Var (Short  "b");
                          Var (Short  "b")
                        ])
                      ]);
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
                                Var (Short  "b");
                                Var (Short  "b")
                              ]);
                              Var (Short  "b")
                            ]);
                            Var (Short  "b")
                          ]);
                          Var (Short  "b")
                        ]);
                        Var (Short  "b")
                      ])
                    ]);
                    (App (FP_bop FP_Mul)
                    [
                      (App FpFromWord [Lit (Word64 (4638215034982367232w:word64))]);
                      (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            Var (Short  "b");
                            Var (Short  "b")
                          ]);
                          Var (Short  "b")
                        ]);
                        Var (Short  "b")
                      ])
                    ])
                  ]);
                  (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))])
                ])
              ])
            ]);
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4617878467915022336w:word64))]);
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
                          (App (FP_bop FP_Mul)
                          [
                            Var (Short  "b");
                            Var (Short  "b")
                          ]);
                          Var (Short  "b")
                        ]);
                        Var (Short  "b")
                      ]);
                      Var (Short  "b")
                    ]);
                    Var (Short  "b")
                  ]);
                  Var (Short  "b")
                ]);
                Var (Short  "b")
              ])
            ])
          ]);
          (App (FP_bop FP_Div)
          [
            Var (Short  "a");
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))]);
              Var (Short  "b")
            ])
          ])
        ]))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()