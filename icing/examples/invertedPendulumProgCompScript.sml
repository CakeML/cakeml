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

val _ = new_theory "invertedPendulumProgComp";

val _ = translation_extends "cfSupport";

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
                   App Opapp [Var (Short "invertedPendulum"); Var (Short "d1")];
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
(Let (SOME "u") (Con NONE [])
 (Let (SOME "strArgs")
  (App Opapp [Var (Short "reader3"); Var (Short "u")])
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
          (Let NONE
           (App Opapp [
           App Opapp [
              App Opapp [
                App Opapp [Var (Short "invertedPendulum"); Var (Short "d1")];
                Var (Short "d2")];
              Var (Short "d3")];
              Var (Short "d4")])
           (Con NONE [])))
         (App Opapp [
            App Opapp [
              App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
              Var (Short "u")]; Var (Short "b")]))))))])))]’;

Definition theBenchmarkMain_def:
  theBenchmarkMain =
  (HD (^iter_code)) :: (^call_code)
End

val st_no_invertedPendulum = get_ml_prog_state ();

val invertedPendulum_env = st_no_invertedPendulum
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_env;

val _ = append_prog (theOptProg_def |> concl |> rhs)

val _ = append_prog main;

Definition invertedPendulum_env:
  invertedPendulum_env = ^invertedPendulum_env
End

val _ = supportLib.write_code_to_file true theAST_def theAST_opt theBenchmarkMain_def main;

val _ = export_theory();
