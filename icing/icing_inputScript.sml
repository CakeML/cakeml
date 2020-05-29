(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open compilerTheory fromSexpTheory;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble astToSexprLib;

val _ = new_theory "icingInput";

(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
Definition theAST_def:
  theAST =
  (** REPLACE AST BELOW THIS LINE **)
  Dletrec unknown_loc
    [("doppler","",
      Fun "u" (Fun "v" (Fun "t"
        (** Precondition **)
        (Let NONE
         (App Opapp
          [Var (Long "RuntimeProg" (Short "assert"));
           (Log And
            (Log And
            (App (FP_cmp FP_LessEqual)
             [App FpFromWord [Lit (Word64 4621819117588971520w)]; Var (Short "u")])
            (App (FP_cmp FP_LessEqual)
             [Var (Short "u"); App FpFromWord [Lit (Word64 4621819117588971520w)]]))
           (Log And
            (Log And
            (App (FP_cmp FP_LessEqual)
             [App FpFromWord [Lit (Word64 4621819117588971520w)]; Var (Short "v")])
            (App (FP_cmp FP_LessEqual)
             [Var (Short "v"); App FpFromWord [Lit (Word64 4621819117588971520w)]]))
           (Log And
            (App (FP_cmp FP_LessEqual)
             [App FpFromWord [Lit (Word64 4621819117588971520w)]; Var (Short "t")])
            (App (FP_cmp FP_LessEqual)
             [Var (Short "t"); App FpFromWord [Lit (Word64 4621819117588971520w)]]))))])
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
           ))))))]
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts =
    <| optimisations := [
      (* WRITE OPTIMISATIONS HERE AS ; SEPARATED LIST *)
       (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
       Terop FP_Fma (Var 0) (Var 1) (Var 2));
       (Binop FP_Mul (Var 0) (Binop FP_Mul (Var 1) (Var 2)),
       Binop FP_Mul (Binop FP_Mul (Var 0) (Var 1)) (Var 2))
       (* OPTIIMISATIONS END *)
       ];
       canOpt := T |>
End

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (source_to_source$compile_decs
       theOpts [theAST])’);

Definition theProg_def:
  theProg =
  ^(theAST_opt |> concl |> rhs)
End

val filename = "theSexp.cml";
val _ = ((write_ast_to_file filename) o rhs o concl) theAST_opt;

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

(** If evaluation gets stuck, uncomment the code below to see when evaluation
    enters a function **)
(**
val  all_funs =
  map (fn s => hd (decls s))
    ["getFunctions", "prepare_kernel", "prepareVars", "prepareGamma",
     "toFloVerCmd", "toFloVerPre", "inferIntervalboundsCmd", "getValidMapCmd",
     "inferErrorboundCmd", "CertificateCheckerCmd"];
computeLib.monitoring := SOME (fn x => List.exists (fn t => same_const t x) all_funs);
**)

Theorem errorbounds_AST =
  EVAL (Parse.Term
      ‘getErrorbounds
      (HD ^(concl theAST_opt |> rhs))’);

  (*
Theorem ast_whole_prog_spec:
 EVERY (inFS_fname fs) (TL cl) ∧ hasFreeFD fs ⇒
   whole_prog_spec ^(concl theAST_opt |> rhs) cl fs NONE
    ((=) (add_stdout fs (catfiles_string fs (TL cl))))
Proof
  *)

  (*
(** Next we compile the program to ARMv8 assembly *)
Theorem compile_ast_opt =
   compilationLib.compile_arm8 1000 1000 "doppler" theAST_def
*)

val _ = export_theory();
