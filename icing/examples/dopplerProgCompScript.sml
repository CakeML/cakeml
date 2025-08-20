(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
Theory dopplerProgComp
Libs
  exampleLib

val _ = translation_extends "cfSupport";

(** Precondition **)
Definition theAST_pre_def:
  theAST_pre =
    λ (x:(string,string) id).
      if x = (Short "u")
      then ((- 100/1, 100/1):real#real)
      else if x = Short "v"
      then (20/1, 20000/1)
      else if x = Short "t"
      then (- 30/1, 50/1)
      else (0,0)
End

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
Definition theAST_def:
  theAST =
    [Dlet unknown_loc (Pvar "doppler")
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
           ]))))))]
End

Definition theErrBound_def:
  theErrBound = inv (2 pow (5))
End

val x = define_benchmark theAST_def theAST_pre_def true;

