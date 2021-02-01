(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open astTheory cfTacticsLib ml_translatorLib;
open basis_ffiTheory cfHeapsBaseTheory basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory cfSupportTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "out2ProgComp";

val _ = translation_extends "cfSupport";

val out2 =
“[Dlet unknown_loc (Pvar "out2")
(Fun "x1" (Fun "x2" (Fun "x3"
(FpOptimise Opt
(App (FP_bop FP_Add) [
    (App (FP_bop FP_Add) [
      (App (FP_bop FP_Add) [
        (App (FP_bop FP_Add) [
          (App (FP_bop FP_Mul) [
            (App (FP_bop FP_Mul) [
              (App (FP_bop FP_Mul) [
                Var (Short  "x3");
                Var (Short  "x3") ]);
              Var (Short  "x3") ]);
            Var (Short  "x3") ]);
          (App (FP_bop FP_Mul) [
            (App (FP_bop FP_Mul) [
              Var (Short  "x3");
              Var (Short  "x3") ]);
            Var (Short  "x3") ]) ]);
        (App (FP_bop FP_Mul) [
          Var (Short  "x3");
          Var (Short  "x3") ]) ]);
      Var (Short  "x3") ]);
    (App FpFromWord [Lit (Word64 (4616189618054758400w:word64))])
  ])))))]”

Definition theAST_def:
  theAST = ^out2
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    fp_comm_gen FP_Add;
    fp_fma_intro
  ]
End

Theorem theAST_plan = EVAL (Parse.Term ‘generate_plan_decs theOpts theAST’);

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (no_opt_decs theOpts
       (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST))’);

Theorem only_opt_body = EVAL (
  Parse.Term ‘
   compose_plan_generation [
       canonicalize;
      (* apply_distributivity; *)
     ] (
     (FpOptimise Opt
      (App (FP_bop FP_Add)
       [
         (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
             [
               (App (FP_bop FP_Mul)
                [
                  Var (Short  "x3");
                  Var (Short  "x3")
                ]);
               Var (Short  "x3")
             ]);
            Var (Short  "x3")
          ]);
         (App (FP_bop FP_Mul)
          [
            (App (FP_bop FP_Mul)
             [
               Var (Short  "x3");
               Var (Short  "x3")
             ]);
            Var (Short  "x3")
          ])
       ])
     )
     ) theOpts’
  );

Theorem opt_linint_test_only_opt = EVAL (
  Parse.Term ‘
     (optimise_linear_interpolation theOpts linear_interpolation)
  ’);

Theorem theAST_lifted =
  EVAL
    (Parse.Term ‘
      lift_fp_constants (
        (no_opt_decs theOpts (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST)))’);
