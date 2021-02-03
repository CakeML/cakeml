(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open astTheory cfTacticsLib ml_translatorLib;
open basis_ffiTheory cfHeapsBaseTheory basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory
     CertificateCheckerTheory;
open floatToRealProofsTheory source_to_sourceTheory CakeMLtoFloVerTheory
     cfSupportTheory optPlannerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open exampleLib preamble;

val _ = new_theory "dopplerProgComp";

val _ = translation_extends "cfSupport";

(** Precondition **)
val theAST_pre =
“λ (x:(string,string) id).
 if x = (Short "u")
 then ((- 100/1, 100/1):real#real)
 else if x = Short "v"
 then (20/1, 20000/1)
 else if x = Short "t"
 then (- 30/1, 50/1)
 else (0,0)”

val theAST_pre_def = Define ‘theAST_pre = ^theAST_pre’;

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val theAST =
“[Dlet unknown_loc (Pvar "doppler")
  (Fun "u" (Fun "v" (Fun "t"
  (** Numerical kernel **)
  (FpOptimise Opt
   (Let (SOME "t1")
     (App (FP_bop FP_Add) [
       (App FpFromWord [Lit (Word64 (4644537666646730342w:word64))]);
       (App (FP_bop FP_Mul) [
         (App FpFromWord [Lit (Word64 (4603579539098121011w:word64))]);
         Var (Short  "t") ])
       ]) (* let bound val end *)
     (App (FP_bop FP_Div) [
       (App (FP_bop FP_Mul) [
         (App (FP_uop FP_Neg) [Var (Short "t1")]);
         Var (Short "v") ]);
       (App (FP_bop FP_Mul) [
         (App (FP_bop FP_Add) [
           Var (Short "t1");
           Var (Short "u") ]);
         (App (FP_bop FP_Add) [
           Var (Short "t1");
           Var (Short "u")])
        ])
     ]))))))]”;

val theAST_def = Define ‘theAST = ^theAST’;

val x = do_stuff theAST theAST_pre;

val _ = export_theory();
