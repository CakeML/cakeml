(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
Theory nn1LayerProgComp
Libs
  exampleLib

val _ = translation_extends "cfSupport";

(** Precondition **)
Definition theAST_pre_def:
  theAST_pre = λ (x:(string,string) id).
 if x = Short "x1"
 then ((- (48/100), 48/100):(real#real))
 else if x = Short "x2"
 then (- 10/1, 10/1)
 else if x = Short "x3"
 then (- 24/1, 24/1)
 else if x = Short "x4"
 then (-10/1, 10/1)
 else (0,0)
End


(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
Definition theAST_def:
  theAST = [Dlet unknown_loc (Pvar "nn1Layer")
(Fun "x1" (Fun "x2" (Fun "x3" (Fun "x4" (FpOptimise Opt
(Let (SOME "dot1")
  (App (FP_bop FP_Add)
    [
      (App (FP_bop FP_Sub)
      [
        (App (FP_bop FP_Sub)
        [
          (App (FP_bop FP_Sub)
          [
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (-4623678203515150061w:word64))]);
              Var (Short  "x1")
            ]);
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4599812728369788328w:word64))]);
              Var (Short  "x2")
            ])
          ]);
          (App (FP_bop FP_Mul)
          [
            (App FpFromWord [Lit (Word64 (4614369037905393877w:word64))]);
            Var (Short  "x3")
          ])
        ]);
        (App (FP_bop FP_Mul)
        [
          (App FpFromWord [Lit (Word64 (4609904394414800136w:word64))]);
          Var (Short  "x4")
        ])
      ]);
      (App FpFromWord [Lit (Word64 (4598694034222349497w:word64))])
    ])
  (Let (SOME "dot2")
    (App (FP_bop FP_Add)
      [
        (App (FP_bop FP_Sub)
        [
          (App (FP_bop FP_Add)
          [
            (App (FP_bop FP_Add)
            [
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (-4629260865613238528w:word64))]);
                Var (Short  "x1")
              ]);
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (4593826543745087465w:word64))]);
                Var (Short  "x2")
              ])
            ]);
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4615768531489599259w:word64))]);
              Var (Short  "x3")
            ])
          ]);
          (App (FP_bop FP_Mul)
          [
            (App FpFromWord [Lit (Word64 (4611127572073593962w:word64))]);
            Var (Short  "x4")
          ])
        ]);
        (App FpFromWord [Lit (Word64 (4598685027023094756w:word64))])
      ])
    (App (FP_bop FP_Sub)
      [
        Var (Short  "dot1");
        Var (Short  "dot2")
      ]))))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

