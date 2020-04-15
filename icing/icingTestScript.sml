(*
  First test of Icing infrastructure
*)
(* CakeML *)
open compilerTheory basisFunctionsLib basisComputeLib basisProgTheory;
(* FloVer *)
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
(* Icing *)
open source_to_sourceTheory CakeMLtoFloVerTheory;
(* HOL libs *)
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "icingTest";

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad "option";

Definition doppler_cml_def:
  doppler_cml =
  Dletrec unknown_loc
    [("doppler","",
      Fun "u" (Fun "v" (Fun "t"
        (Let NONE
         (App Opapp
          [Var (Long "RuntimeProg" (Short "assert"));
           (App Opapp
            [App Opapp [Var (Short "="); Lit (IntLit 1)]; Lit (IntLit 1)])])
         (FpOptimise Opt
          (Let (SOME "t1")
            (App (FP_bop FP_Add)
              [
                Lit (Word64 (4644537666646730342w:word64));
                (App (FP_bop FP_Mul)
                 [
                   Lit (Word64 (4603579539098121011w:word64));
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

Definition doppler_opt_def:
  doppler_opt =
  HD (source_to_source$compile_decs
           <| optimisations := [
               (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
                Terop FP_Fma (Var 0) (Var 1) (Var 2))];
               canOpt := T |>
           [doppler_cml])
End

Definition doppler_body_def:
doppler_body = getFunctions doppler_cml
End

Definition doppler_opt_body_def:
doppler_opt_body = getFunctions doppler_opt
End

Definition optimised_doppler_body_def:
  optimised_doppler_body = prepare_kernel doppler_opt_body
End

Definition Gamma_def:
  Gamma =
    let (vars, varMap, freshId) = prepareVars (FST (THE optimised_doppler_body)) in
      prepareGamma vars
End

val P = ``λ x:num. (0,100):(real#real)``;

val _ = computeLib.del_funs [sptreeTheory.subspt_def];

val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER, binary_ieeeTheory.float_to_real_def, sptreeTheory.subspt_eq, sptreeTheory.lookup_def];

val test =
EVAL (Parse.Term `
      getErrorbounds
      (THE optimised_doppler_body)
      ^P`);

val _ = export_theory();
