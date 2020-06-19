(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open compilerTheory fromSexpTheory cfTacticsLib ml_translatorLib basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble astToSexprLib;

val _ = new_theory "invertedPendulumProgComp";

val _ = translation_extends "basisProg";

(** Precondition **)
val invertedPendulum_pre =
“λ (x:(string, string) id).
 if x = Short "s1"
 then ((-50/1, 50/1):real#real)
 else if x = Short "s2"
 then (-10/1, 10/1)
 else if x = Short "s3"
 then (-785/1000, 785/1000)
 else if x = Short "s4"
 then (-785/1000, 785/1000)
 else (0,0)”

Definition invertedPendulum_pre_def:
  invertedPendulum_pre = ^invertedPendulum_pre
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val invertedPendulum =
“[Dlet unknown_loc (Pvar "invertedPendulum")
  (Fun "s1" (Fun "s2" (Fun "s3" (Fun "s4"
    (FpOptimise Opt
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

Definition theAST_def:
  theAST =
  (** REPLACE AST BELOW THIS LINE **)
  ^invertedPendulum
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    (Binop FP_Add (Var 0) (Binop FP_Mul (Var 1) (Var 2)),
     Binop FP_Add (Binop FP_Mul (Var 1) (Var 2)) (Var 0))
    ;
    (Binop FP_Add (Binop FP_Mul (Var 0) (Var 1)) (Var 2),
    Terop FP_Fma (Var 2) (Var 0) (Var 1))
  ]
End

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (source_to_source$no_opt_decs theOpts (source_to_source$stos_pass_decs theOpts
       theAST))’);

val invertedPendulum_opt = theAST_opt |> concl |> rhs;

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

Definition theProg_def:
  theProg = ^invertedPendulum
End

Definition theOptProg_def:
  theOptProg = ^invertedPendulum_opt
End

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) ^invertedPendulum_pre theErrBound’);

val _ = export_theory();
