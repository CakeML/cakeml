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
open preamble;

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

(** Optimizations to be applied by Icing **)
val theOpts_def = Define ‘theOpts = no_fp_opt_conf’

fun flatMap (ll:'a list list) =
  case ll of [] => []
  | l1 :: ls => l1 @ flatMap ls

fun dedup l =
  case l of
  [] => []
  | l1::ls =>
      let val lclean = dedup ls in
        if (List.exists (fn x => x = l1) lclean)
        then lclean
        else l1::lclean
      end;

val theAST_plan = save_thm ("theAST_plan", EVAL (Parse.Term ‘generate_plan_decs theOpts theAST’));

val thePlan_def = EVAL “HD ^(theAST_plan |> concl |> rhs)”
(*
val hotRewrites = thePlan_def |> concl |> rhs |> listSyntax.dest_list |> #1
                       |> map (#2 o dest_pair)
                       |> map (#1 o listSyntax.dest_list)
                       |> flatMap
                       |> map (fn t => DB.apropos_in t (DB.thy "icing_optimisations"))
                       |> flatMap
                       |> map (#2 o #1)
                       |> dedup
                       |> List.foldl (fn (elem, acc) => acc ^ " " ^ elem ^ " ;") "Used rewrites:"

val _ = adjoin_to_theory
        { sig_ps =
          SOME (fn _ => PP.add_string
                    ("val hotRewrites = \""^hotRewrites^"\";")),
          struct_ps = NONE };
*)

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
val theAST_opt = save_thm ("theAST_opt",
  EVAL
    (Parse.Term ‘
      (no_opt_decs theOpts
       (MAP FST (stos_pass_with_plans_decs theOpts (generate_plan_decs theOpts theAST) theAST)))’));

val doppler_opt = theAST_opt |> concl |> rhs;

val theProg_def = Define ‘theProg = ^theAST’

val theOptProg_def = Define ‘theOptProg = ^doppler_opt’;

val theErrBound_def = Define ‘theErrBound = inv (2 pow (10))’;

val main =
“[Dlet unknown_loc (Pvar "main")
  (Fun "a"
   (Let (SOME "u") (Con NONE [])
   (Let (SOME "strArgs")
    (App Opapp [Var (Short "reader3"); Var (Short "u")])
    (Mat (Var (Short "strArgs"))
     [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pvar "d3s"]],
       (Let (SOME "d1")
        (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
        (Let (SOME "d2")
         (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
         (Let (SOME "d3")
          (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
          (Let (SOME "x" )
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "doppler"); Var (Short "d1")];
                Var (Short "d2")];
              Var (Short "d3")])
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
  (App Opapp [Var (Short "reader3"); Var (Short "u")])
  (Mat (Var (Short "strArgs"))
   [(Pcon NONE [Pvar "d1s"; Pcon NONE [Pvar "d2s"; Pvar "d3s"]],
     (Let (SOME "d1")
      (App Opapp [Var (Short "intToFP"); Var (Short "d1s")])
      (Let (SOME "d2")
       (App Opapp [Var (Short "intToFP"); Var (Short "d2s")])
       (Let (SOME "d3")
        (App Opapp [Var (Short "intToFP"); Var (Short "d3s")])
        (Let (SOME "b")
         (Fun "x"
          (Let (SOME "y")
           (App Opapp [
              App Opapp [
                App Opapp [Var (Short "doppler"); Var (Short "d1")];
                Var (Short "d2")];
              Var (Short "d3")])
           (Var (Short "y"))))
         (App Opapp [
            App Opapp [
              App Opapp [Var (Short "iter"); Lit (IntLit ^iter_count)];
              Var (Short "u")]; Var (Short "b")]))))))])))]’;

Definition theBenchmarkMain_def:
  theBenchmarkMain =
  (HD (^iter_code)) :: (^call_code)
End

val st_no_doppler = get_ml_prog_state ();

val doppler_env = st_no_doppler
  |> ml_progLib.clean_state
  |> ml_progLib.remove_snocs
  |> ml_progLib.get_env;

val _ = append_prog (theOptProg_def |> concl |> rhs)

val _ = append_prog main;

val doppler_env_def = Define ‘doppler_env = ^doppler_env’;

(*
val _ =
  supportLib.write_code_to_file true theAST_def theAST_opt
(Parse.Term ‘APPEND ^(reader3_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    (Parse.Term ‘APPEND ^(reader3_def |> concl |> rhs) (APPEND ^(intToFP_def |> concl |> rhs) (APPEND ^(printer_def |> concl |> rhs) ^(theBenchmarkMain_def |> concl |> rhs)))’)
    "doppler";
*)

val _ = export_theory();
