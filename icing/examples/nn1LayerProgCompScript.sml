(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open astTheory ml_translatorLib;
open basis_ffiTheory cfHeapsBaseTheory basis;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory cfSupportTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "nn1LayerProgComp";

val _ = translation_extends "cfSupport";

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
Dlet unknown_loc (Pvar "nn1Layer")
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
    fp_sub_add;
    fp_comm_gen FP_Add;
    fp_neg_push_mul_r;
    fp_fma_intro
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

val main =
“[Dlet unknown_loc (Pvar "main")
  (Fun "a"
   (Let (SOME "u") (Con NONE [])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader4"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
     [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s"; Pvar "d4s"]]]),
       (Let (SOME "d1")
        (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
        (Let (SOME "d2")
         (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
         (Let (SOME "d3")
          (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
          (Let (SOME "d4")
           (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
           (Let (SOME "x" )
            (App Opapp [
               App Opapp [
                 App Opapp [
                   App Opapp [Var (Short "nn1Layer"); Var (Short "d1")];
                   Var (Short "d2")];
                 Var (Short "d3")];
               Var (Short "d4")])
           (Let (SOME "y")
            (App FpToWord [Var (Short "x")])
            (App Opapp [
               Var (Short "printer");
               Var (Short "y")])))))))]))))]”;

val iter_code = process_topdecs ‘
 fun iter n s f =
     if (n = 0) then s else iter (n-1) (f s) f;’

val iter_count = “10000000:int”

val call_code = Parse.Term ‘
[Dlet unknown_loc (Pvar "it")
(Let (SOME "u") (App FpFromWord [Lit (Word64 (4613937818241073152w:word64))])
 (Let (SOME "strArgs")
  (App Opapp [Var (Short "reader4"); Var (Short "u")])
  (Mat (Var (Short "strArgs"))
     [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pcon NONE [Pvar "d3s"; Pvar "d4s"]]]),
       (Let (SOME "d1")
        (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
        (Let (SOME "d2")
         (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
         (Let (SOME "d3")
          (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
          (Let (SOME "d4")
           (App Opapp [Var (Short "intToFP"); Var (Short "d4s")])
        (Let (SOME "b")
         (Fun "x"
          (Let (SOME "y")
           (App Opapp [
           App Opapp [
              App Opapp [
                App Opapp [Var (Short "nn1Layer"); Var (Short "d1")];
                Var (Short "d2")];
              Var (Short "d3")];
              Var (Short "d4")])
           (Var (Short "y"))))
         (App Opapp [
            App Opapp [
              App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
              Var (Short "u")]; Var (Short "b")]))))))])))]’;

Definition theBenchmarkMain_def:
  theBenchmarkMain =
  (HD (^iter_code)) :: (^call_code)
End

val st_no_nn1Layer = get_ml_prog_state ();

val nn1Layer_env = st_no_nn1Layer
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_env;

val _ = append_prog (theOptProg_def |> concl |> rhs)

val _ = append_prog main;

Definition nn1Layer_env_def:
  nn1Layer_env = ^nn1Layer_env
End

val _ =
  supportLib.write_code_to_file true theAST_def theAST_opt
(Parse.Term ‘APPEND ^(reader4_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    (Parse.Term ‘APPEND ^(reader4_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^main))’)
    "nn1Layer";

val _ = export_theory();
