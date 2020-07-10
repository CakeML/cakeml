(**
  Compute and compare errors for doppler example
**)

open astTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open dopplerProgCompTheory;
open preamble;

val _ = new_theory "dopplerProgError";

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) doppler_pre theErrBound’);

Theorem errorbound_opt =
  EVAL (Parse.Term
       ‘getError ^(concl theAST_opt |> rhs) doppler_pre theErrBound’);

val doppler_unopt =
“[Dlet unknown_loc (Pvar "doppler")
 (Fun "u" (Fun "v" (Fun "t"
  (** Numerical kernel **)
  (FpOptimise NoOpt
   (Let (SOME "t1")
    (App (FP_bop FP_Add)
     [
       (App FpFromWord [Lit (Word64 (4644537666646730342w:word64))]);
       (App (FP_bop FP_Mul)
        [
          (App FpFromWord [Lit (Word64 (4603579539098121011w:word64))]);
          Var (Short  "t")
        ])
     ])
    (App (FP_bop FP_Div)
     [
       (App (FP_bop FP_Mul)
        [
          (App (FP_uop FP_Neg)
           [Var (Short "t1")]);
          Var (Short "v")
        ]);
       (App (FP_bop FP_Mul)
        [
          (App (FP_bop FP_Add)
           [Var (Short "t1");
            Var (Short "u")]);
          (App (FP_bop FP_Add)
           [Var (Short "t1");
            Var (Short "u")])
        ])
     ])
     )))))]”;

Theorem errorbound_unopt =
  EVAL (Parse.Term
       ‘getError ^(doppler_unopt) doppler_pre theErrBound’);

val _ = export_theory();
