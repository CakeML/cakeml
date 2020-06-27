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

val _ = new_theory "nn1LayerProgComp";

(** Precondition **)
val nn1Layer_pre =
“λ (x:(string,string) id).
 if x = Short "x1"
 then ((- (48/100), 48/100):(real#real))
 else if x = Short "x2"
 then (- 10/1, 10/1)
 else if x = Short "x3"
 then (- 24/1, 24/1)
 else if x = Short "x4"
 then (-10/1, 10/1)
 else (0,0)”

Definition nn1Layer_pre_def:
  nn1Layer_pre = ^nn1Layer_pre
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
val nn1Layer =
(** REPLACE AST BELOW THIS LINE **)
“[
Dlet unknown_loc (Pvar "oneLayer")
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
      ]))))))))]”;

Definition theAST_def:
  theAST =
  ^nn1Layer
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
    (Binop FP_Add (Binop FP_Mul (Var 0) (Var 1)) (Var 2),
    Terop FP_Fma (Var 2) (Var 0) (Var 1));
    (Binop FP_Sub (Var 0) (Var 1),
    Binop FP_Add (Var 0) (Unop FP_Neg (Var 1)));
    (Binop FP_Add (Var 0) (Unop FP_Neg (Binop FP_Mul (Var 1) (Var 2))),
     Binop FP_Add (Binop FP_Mul (Var 1) (Unop FP_Neg (Var 2))) (Var 0));
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

val nn1Layer_opt = theAST_opt |> concl |> rhs;

Definition theErrBound_def:
  theErrBound = inv (2 pow (10))
End

Definition theProg_def:
  theProg = ^nn1Layer
End

Definition theOptProg_def:
  theOptProg = ^nn1Layer_opt
End

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

Theorem errorbounds_AST =
  EVAL (Parse.Term
       ‘isOkError ^(concl theAST_opt |> rhs) ^nn1Layer_pre theErrBound’);

val _ = export_theory();
