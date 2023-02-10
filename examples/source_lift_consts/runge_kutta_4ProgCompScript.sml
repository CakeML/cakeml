(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "runge_kutta_4ProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "c" then (((50)/(1), (200)/(1)):real#real)
  else if x = Short "h" then (((1)/(100000), (1)/(10)):real#real)
  else if x = Short "y_n" then (((0)/(1), (100)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "runge_kutta_4")
    (Fun "h"(Fun "y_n"(Fun "c"
      (FpNoOptimise NoOpt
        (Let (SOME "sixieme")
        (App FpFromWord [Lit (Word64 (0w:word64))])
        (          (Let (SOME "eps")
          (App FpFromWord [Lit (Word64 (4572414629676717179w:word64))])
          (            (Let (SOME "k")
            (App FpFromWord [Lit (Word64 (4608083138725491507w:word64))])
            (              (Let (SOME "v_1")
              (App (FP_bop FP_Sub)
                [
                  Var (Short  "c");
                  Var (Short  "y_n")
                ])
              (                (Let (SOME "k1")
                (App (FP_bop FP_Mul)
                  [
                    (App (FP_bop FP_Mul)
                    [
                      Var (Short  "k");
                      Var (Short  "v_1")
                    ]);
                    Var (Short  "v_1")
                  ])
                (                  (Let (SOME "v_2")
                  (App (FP_bop FP_Sub)
                    [
                      Var (Short  "c");
                      (App (FP_bop FP_Add)
                      [
                        Var (Short  "y_n");
                        (App (FP_bop FP_Mul)
                        [
                          (App (FP_bop FP_Mul)
                          [
                            (App FpFromWord [Lit (Word64 (4602678819172646912w:word64))]);
                            Var (Short  "h")
                          ]);
                          Var (Short  "k1")
                        ])
                      ])
                    ])
                  (                    (Let (SOME "k2")
                    (App (FP_bop FP_Mul)
                      [
                        (App (FP_bop FP_Mul)
                        [
                          Var (Short  "k");
                          Var (Short  "v_2")
                        ]);
                        Var (Short  "v_2")
                      ])
                    (                      (Let (SOME "v_3")
                      (App (FP_bop FP_Sub)
                        [
                          Var (Short  "c");
                          (App (FP_bop FP_Add)
                          [
                            Var (Short  "y_n");
                            (App (FP_bop FP_Mul)
                            [
                              (App (FP_bop FP_Mul)
                              [
                                (App FpFromWord [Lit (Word64 (4602678819172646912w:word64))]);
                                Var (Short  "h")
                              ]);
                              Var (Short  "k2")
                            ])
                          ])
                        ])
                      (                        (Let (SOME "k3")
                        (App (FP_bop FP_Mul)
                          [
                            (App (FP_bop FP_Mul)
                            [
                              Var (Short  "k");
                              Var (Short  "v_3")
                            ]);
                            Var (Short  "v_3")
                          ])
                        (                          (Let (SOME "v_4")
                          (App (FP_bop FP_Sub)
                            [
                              Var (Short  "c");
                              (App (FP_bop FP_Add)
                              [
                                Var (Short  "y_n");
                                (App (FP_bop FP_Mul)
                                [
                                  Var (Short  "h");
                                  Var (Short  "k3")
                                ])
                              ])
                            ])
                          (                            (Let (SOME "k4")
                            (App (FP_bop FP_Mul)
                              [
                                (App (FP_bop FP_Mul)
                                [
                                  Var (Short  "k");
                                  Var (Short  "v_4")
                                ]);
                                Var (Short  "v_4")
                              ])
                            ((App (FP_bop FP_Add)
                              [
                                Var (Short  "y_n");
                                (App (FP_bop FP_Mul)
                                [
                                  (App (FP_bop FP_Mul)
                                  [
                                    Var (Short  "sixieme");
                                    Var (Short  "h")
                                  ]);
                                  (App (FP_bop FP_Add)
                                  [
                                    (App (FP_bop FP_Add)
                                    [
                                      (App (FP_bop FP_Add)
                                      [
                                        Var (Short  "k1");
                                        (App (FP_bop FP_Mul)
                                        [
                                          (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))]);
                                          Var (Short  "k2")
                                        ])
                                      ]);
                                      (App (FP_bop FP_Mul)
                                      [
                                        (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))]);
                                        Var (Short  "k3")
                                      ])
                                    ]);
                                    Var (Short  "k4")
                                  ])
                                ])
                              ])))))))))))))))))))))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()