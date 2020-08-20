(**
  Compute and compare errors for nn1LayerProg example
**)

open astTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open nn1LayerProgCompTheory;
open preamble;

val _ = new_theory "nn1LayerProgError";

(*val _ = computeLib.del_funs [sptreeTheory.subspt_def]; *)
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) nn1Layer_pre theErrBound’);

Theorem errorbound_opt =
  EVAL (Parse.Term
       ‘getError ^(concl theAST_opt |> rhs) nn1Layer_pre theErrBound’);

val nn1Layer =
(** REPLACE AST BELOW THIS LINE **)
“[
Dlet unknown_loc (Pvar "nn1Layer")
(Fun "x1" (Fun "x2" (Fun "x3" (Fun "x4" (FpOptimise NoOpt
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
      ]))))))))]”;

Theorem errorbound_unopt =
  EVAL (Parse.Term
       ‘getError ^nn1Layer nn1Layer_pre theErrBound’);

val _ = export_theory();
