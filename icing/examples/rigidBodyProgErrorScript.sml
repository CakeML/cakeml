(**
  Compute and compare errors for rigidBody example
**)

open astTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open rigidBodyProgCompTheory;
open preamble;

val _ = new_theory "rigidBodyProgError";

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) rigidBody_pre theErrBound’);

Theorem errorbound_opt =
  EVAL (Parse.Term
       ‘getError ^(concl theAST_opt |> rhs) rigidBody_pre theErrBound’);

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val rigidBody =
(** REPLACE AST BELOW THIS LINE **)
“[Dlet unknown_loc (Pvar "rigidBody")
(Fun "x1" (Fun "x2" (Fun "x3" (FpOptimise NoOpt
(App (FP_bop FP_Sub)
  [
    (App (FP_bop FP_Add)
    [
      (App (FP_bop FP_Sub)
      [
        (App (FP_bop FP_Add)
        [
          (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
            [
              (App (FP_bop FP_Mul)
              [
                (App FpFromWord [Lit (Word64 (4611686018427387904w:word64))]);
                Var (Short  "x1")
              ]);
              Var (Short  "x2")
            ]);
            Var (Short  "x3")
          ]);
          (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
            [
              (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))]);
              Var (Short  "x3")
            ]);
            Var (Short  "x3")
          ])
        ]);
        (App (FP_bop FP_Mul)
        [
          (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
            [
              Var (Short  "x2");
              Var (Short  "x1")
            ]);
            Var (Short  "x2")
          ]);
          Var (Short  "x3")
        ])
      ]);
      (App (FP_bop FP_Mul)
      [
        (App (FP_bop FP_Mul)
        [
          (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))]);
          Var (Short  "x3")
        ]);
        Var (Short  "x3")
      ])
    ]);
    Var (Short  "x2")
  ])))))]”

Theorem errorbound_unopt =
  EVAL (Parse.Term
       ‘getError ^rigidBody rigidBody_pre theErrBound’);

val _ = export_theory();
