(*
  First test of Icing infrastructure
*)
(* CakeML *)
open compilerTheory;
(* FloVer *)
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
(* Icing *)
open source_to_sourceTheory CakeMLtoFloVerTheory CakeMLtoFloVerLemsTheory;
(* HOL libs *)
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble;

val _ = new_theory "icingTest";

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

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

val dest_trip = (fn t => let val (t1, t2) = dest_pair t; val (t2, t3) = dest_pair t2 in (t1,t2,t3) end);

val (ids, cake_P, f) =
  EVAL (Parse.Term ‘prepareKernel (getFunctions (HD ^(theProg_def |> concl |> rhs)))’)
  |> concl |> rhs |> optionSyntax.dest_some |> dest_trip;

val (floverVars, varMap, freshId) =
  EVAL (Parse.Term ‘prepareVars ^ids’)
  |> concl |> rhs
  |> optionSyntax.dest_some |> dest_trip;

val checkFvars =
  curry Term.compare “T”
  (EVAL (Parse.Term ‘checkFreevars (MAP FST ^varMap) (freevars_list [^f])’) |> concl |> rhs)

val Gamma = EVAL (Parse.Term ‘prepareGamma ^floverVars’) |> concl |> rhs;

val (theIds, freshId, theCmd) =
  EVAL (Parse.Term ‘toFloVerCmd ^varMap ^freshId ^f’) |> concl |> rhs
  |> optionSyntax.dest_some |> dest_trip;

val (P, dVars) =
  EVAL (Parse.Term ‘toFloVerPre [^cake_P] ^varMap’) |> concl |> rhs
  |> optionSyntax.dest_some |> dest_pair;

val theCmd =
  EVAL (Parse.Term ‘toRCmd ^theCmd’) |> concl |> rhs;

val theRealBounds =
  EVAL (Parse.Term ‘inferIntervalboundsCmd ^theCmd ^P FloverMapTree_empty ’)
  |> concl |> rhs
  |> optionSyntax.dest_some;

val typeMap =
  EVAL (Parse.Term ‘case getValidMapCmd ^Gamma ^theCmd FloverMapTree_empty of Succes Gamma => Gamma’)
  |> concl |> rhs;

val theErrBounds =
  EVAL (Parse.Term ‘inferErrorboundCmd ^theCmd ^typeMap ^theRealBounds FloverMapTree_empty’)
  |> concl |> rhs |> optionSyntax.dest_some;

val theResult =
  EVAL (Parse.Term ‘CertificateCheckerCmd ^theCmd ^theErrBounds ^P ^Gamma’)

val Gamma2 =
  EVAL (Parse.Term ‘case getValidMapCmd ^Gamma ^theCmd FloverMapTree_empty of |Succes Gamma => Gamma’)
  |> concl |> rhs;

val validSSA_check =
  EVAL (Parse.Term ‘validSSA ^theCmd (freeVars ^theCmd)’)

val validIVbounds =
  EVAL (Parse.Term ‘validIntervalboundsCmd ^theCmd ^theErrBounds ^P ’)

val validIVbounds =
  EVAL (Parse.Term ‘validIntervalbounds ((Var 3)) ^theErrBounds ^P (insert 3 () LN)’)

val validIVbounds =
  EVAL (Parse.Term ‘validIntervalbounds (Binop Mult (Unop Neg (Var 3)) (Var 1)) ^theErrBounds ^P (insert 3 () LN)’)

val validIVbounds =
  EVAL (Parse.Term ‘validIntervalbounds (Binop Plus (Var 3) (Var 2)) ^theErrBounds ^P (insert 3 () LN)’)

val validIVbounds =
  EVAL (Parse.Term ‘validIntervalbounds (Fma (Var 3) (Var 2) (Binop Plus (Var 3) (Var 2))) ^theErrBounds ^P (insert 3 () LN)’)

val validIVbounds =
  EVAL (Parse.Term ‘validIntervalbounds (Binop Div (Binop Mult (Unop Neg (Var 3)) (Var 1))
            (Fma (Var 3) (Var 2) (Binop Plus (Var 3) (Var 2)))) ^theErrBounds ^P LN’)

val validFPRanges =
  EVAL (Parse.Term ‘FPRangeValidatorCmd ^theCmd ^theErrBounds ^Gamma2 LN’)

val validErrBounds =
  EVAL (Parse.Term ‘validErrorboundCmd ^theCmd ^Gamma2 ^theErrBounds LN’)

val _ = export_theory();
