(**
  Compute and compare errors for nn2LayerProg example
**)

open astTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open nn2LayerProgCompTheory;
open preamble;

val _ = new_theory "nn2LayerProgError";

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) nn2LayerProg_pre theErrBound’);

val _ = export_theory();
