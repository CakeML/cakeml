(*
  Auto-generated by Daisy (https://gitlab.mpi-sws.org/AVA/daisy
  *)
(* INCLUDES, do not change those *)
open exampleLib;

val _ = new_theory "pidProgComp";

val _ = translation_extends "cfSupport";

Definition theAST_pre_def:
  theAST_pre = \ (x:(string, string) id).
  if x = Short "c" then (((-10)/(1), (10)/(1)):real#real)
  else if x = Short "m" then (((-10)/(1), (10)/(1)):real#real)
  else (0,0)
End

Definition theAST_def:
  theAST =
  [ Dlet unknown_loc (Pvar "pid")
    (Fun "m"(Fun "c"
      (FpOptimise Opt
        (Let (SOME "ki")
        (App FpFromWord [Lit (Word64 (4604390727463002985w:word64))])
        (          (Let (SOME "kp")
          (App FpFromWord [Lit (Word64 (4621510283244524588w:word64))])
          (            (Let (SOME "kd")
            (App FpFromWord [Lit (Word64 (4613589689989877413w:word64))])
            (              (Let (SOME "i_0")
              (App FpFromWord [Lit (Word64 (0w:word64))])
              (                (Let (SOME "dt")
                (App FpFromWord [Lit (Word64 (4596373779694328218w:word64))])
                (                  (Let (SOME "invdt")
                  (App FpFromWord [Lit (Word64 (4617315517961601024w:word64))])
                  (                    (Let (SOME "eold")
                    (App FpFromWord [Lit (Word64 (0w:word64))])
                    (                      (Let (SOME "e_1")
                      (App (FP_bop FP_Sub)
                        [
                          Var (Short  "c");
                          Var (Short  "m")
                        ])
                      (                        (Let (SOME "p_1")
                        (App (FP_bop FP_Mul)
                          [
                            Var (Short  "kp");
                            Var (Short  "e_1")
                          ])
                        (                          (Let (SOME "i_1")
                          (App (FP_bop FP_Add)
                            [
                              Var (Short  "i_0");
                              (App (FP_bop FP_Mul)
                              [
                                (App (FP_bop FP_Mul)
                                [
                                  Var (Short  "ki");
                                  Var (Short  "dt")
                                ]);
                                Var (Short  "e_1")
                              ])
                            ])
                          (                            (Let (SOME "d_1")
                            (App (FP_bop FP_Mul)
                              [
                                (App (FP_bop FP_Mul)
                                [
                                  Var (Short  "kd");
                                  Var (Short  "invdt")
                                ]);
                                (App (FP_bop FP_Sub)
                                [
                                  Var (Short  "e_1");
                                  Var (Short  "eold")
                                ])
                              ])
                            (                              (Let (SOME "r_1")
                              (App (FP_bop FP_Add)
                                [
                                  (App (FP_bop FP_Add)
                                  [
                                    Var (Short  "p_1");
                                    Var (Short  "i_1")
                                  ]);
                                  Var (Short  "d_1")
                                ])
                              ((App (FP_bop FP_Add)
                                [
                                  Var (Short  "m");
                                  (App (FP_bop FP_Mul)
                                  [
                                    (App FpFromWord [Lit (Word64 (4576918229304087675w:word64))]);
                                    Var (Short  "r_1")
                                  ])
                                ]))))))))))))))))))))))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

val _ = export_theory()