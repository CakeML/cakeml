(**
  Compute and compare errors for invertedPendulum example
**)

open astTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open invertedPendulumProgCompTheory;
open preamble;

val _ = new_theory "invertedPendulumProgError";

(* val _ = computeLib.del_funs [sptreeTheory.subspt_def]; *)
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) invertedPendulum_pre theErrBound’);

Theorem errorbound_opt =
  EVAL (Parse.Term
       ‘getError ^(concl theAST_opt |> rhs) invertedPendulum_pre theErrBound’);

val invertedPendulum =
“[Dlet unknown_loc (Pvar "invertedPendulum")
  (Fun "s1" (Fun "s2" (Fun "s3" (Fun "s4"
    (FpOptimise NoOpt
     (App (FP_bop FP_Add)
      [
        (App (FP_bop FP_Add)
         [
           (App (FP_bop FP_Add)
            [
              (App (FP_bop FP_Mul)
               [
                 (App FpFromWord [Lit (Word64 (4607182418800017408w:word64))]);
                 Var (Short  "s1")
               ]);
              (App (FP_bop FP_Mul)
               [
                 (App FpFromWord [Lit (Word64 (4610139932675311613w:word64))]);
                 Var (Short  "s2")
               ])
            ]);
           (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (-4597419346642817620w:word64))]);
              Var (Short  "s3")
            ])
         ]);
        (App (FP_bop FP_Mul)
         [
           (App FpFromWord [Lit (Word64 (-4608399741779295653w:word64))]);
           Var (Short  "s4")
         ])
      ]))))))]”


Theorem errorbound_unopt =
  EVAL (Parse.Term
       ‘getError ^invertedPendulum invertedPendulum_pre theErrBound’);

val _ = export_theory();
