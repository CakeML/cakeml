(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open astTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "dopplerProgComp";

(** Precondition **)
val doppler_pre =
“λ (x:(string,string) id).
 if x = (Short "u")
 then ((- 100/1, 100/1):real#real)
 else if x = Short "v"
 then (20/1, 20000/1)
 else if x = Short "t"
 then (- 30/1, 50/1)
 else (0,0)”

Definition doppler_pre_def:
  doppler_pre = ^doppler_pre
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val doppler =
(** REPLACE AST BELOW THIS LINE **)
“[Dlet unknown_loc (Pvar "doppler")
  (Fun "u" (Fun "v" (Fun "t"
  (** Numerical kernel **)
  (FpOptimise Opt
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
   )))))]”

Definition theAST_def:
  theAST =
  ^doppler
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    fp_comm_gen FP_Add
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

val doppler_opt = theAST_opt |> concl |> rhs;

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

Definition theProg_def:
  theProg = ^doppler
End

Definition theOptProg_def:
  theOptProg = ^doppler_opt
End

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) ^doppler_pre theErrBound’);

val _ = export_theory();
