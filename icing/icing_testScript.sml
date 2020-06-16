(**
  Icing benchmark input file
  Use this file to run a CakeML AST through the Icing optimizer
**)

(* INCLUDES, do not change those *)
open compilerTheory fromSexpTheory cfTacticsLib;
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory CertificateCheckerTheory;
open source_to_sourceTheory CakeMLtoFloVerTheory;
open machine_ieeeTheory binary_ieeeTheory realTheory realLib RealArith;
open preamble astToSexprLib;

val _ = new_theory "icing_test";

(*
(**
  Define the CakeML source AST as a polyML/HOL4 declaration
**)
Definition theAST_def:
  theAST =
  (** REPLACE AST BELOW THIS LINE **)
  Dletrec unknown_loc
    [("doppler","u",
      (Fun "v" (Fun "t"
        (** Precondition **)
        (Let NONE
         (App Opapp
          [Var (Long "Runtime" (Short "assert"));
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

Definition theMain_def:
  theMain =
  [Dlet unknown_loc (Pvar "it")
   (Let (SOME "x" )
     (App Opapp [
        App Opapp [
          App Opapp [
              Var (Short "doppler");
            App FpFromWord [Lit (Word64 4607182418800017408w)]];
          App FpFromWord [Lit (Word64 4607182418800017408w)]];
        App FpFromWord [Lit (Word64 4607182418800017408w)]])
     (App Opapp [
        Var (Long "TextIO" (Short "print"));
        App Opapp [
          Var (Long "Int" (Short "toString"));
          App Opapp [
            Var (Long "Word64" (Short "toInt"));
            App FpToWord [Var (Short "x")]
          ]
        ]
      ])
   )]
End

(** Optimizations to be applied by Icing **)
Definition theOpts_def:
  theOpts = extend_conf no_fp_opt_conf
  [
      (* WRITE OPTIMISATIONS HERE AS ; SEPARATED LIST *)
       (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
       Terop FP_Fma (Var 0) (Var 1) (Var 2));
       (Binop FP_Mul (Var 0) (Binop FP_Mul (Var 1) (Var 2)),
       Binop FP_Mul (Binop FP_Mul (Var 0) (Var 1)) (Var 2))
       (* OPTIIMISATIONS END *)
  ]
End

(** The code below stores in theorem theAST_opt the optimized version of the AST
    from above and in errorbounds_AST the inferred FloVer roundoff error bounds
 **)
Theorem theAST_opt =
  EVAL
    (Parse.Term ‘
      (source_to_source$stos_pass_decs theOpts
       [theAST])’);

val fullProg =
(EVAL
     (Parse.Term ‘[(^(theAST_def |> concl |> rhs)); HD (^(theMain_def |> concl |> rhs))]’)
  |> concl |> rhs);

val fullOptProg =
(EVAL
     (Parse.Term ‘[HD (^(theAST_opt |> concl |> rhs)); HD (^(theMain_def |> concl |> rhs))]’)
  |> concl |> rhs);

Definition theProg_def:
  theProg = ^fullProg
End

Definition theOptProg_def:
  theOptProg = ^fullOptProg
End

val _ = computeLib.del_funs [sptreeTheory.subspt_def];
val _ = computeLib.add_funs [realTheory.REAL_INV_1OVER,
                             binary_ieeeTheory.float_to_real_def,
                             binary_ieeeTheory.float_tests,
                             sptreeTheory.subspt_eq,
                             sptreeTheory.lookup_def];

val dest_trip = (fn t => let val (t1, t2) = dest_pair t; val (t2, t3) = dest_pair t2 in (t1,t2,t3) end);

val get = fn t => EVAL (Parse.Term t) |> concl |> rhs;

val (loc, p, e) =
  get ‘case ^(theAST_opt |> concl |> rhs) of | [Dlet loc p e] => (loc, p, e)’
  |> dest_trip;

val (vars, body) = get ‘stripFuns ^e’ |> dest_pair;

val (floverVars, varMap, freshId) =
  get ‘getFloVerVarMap ^vars’ |> optionSyntax.dest_some |> dest_trip;

val checkFvars =
  curry Term.compare “T”
  (get ‘checkFreevars ^vars (freevars_list [^body])’)

val Gamma = get ‘buildFloVerTypeMap ^floverVars’;

val (theIds, freshId, theCmd) =
  get ‘toFloVerCmd ^varMap ^freshId ^body’

val f = “(Let (SOME "t1")
         (App (FP_bop FP_Add)
            [App FpFromWord [Lit (Word64 4644537666646730342w)];
             App (FP_bop FP_Mul)
               [App FpFromWord [Lit (Word64 4603579539098121011w)];
                Var (Short "t")]])
         (App (FP_bop FP_Div)
            [App (FP_bop FP_Mul)
               [App (FP_uop FP_Neg) [Var (Short "t1")]; Var (Short "v")];
             App (FP_bop FP_Mul)
               [App (FP_bop FP_Add) [Var (Short "t1"); Var (Short "u")];
                App (FP_bop FP_Add) [Var (Short "t1"); Var (Short "u")]]]))”;

val (theIds, freshId, theCmd) =
  EVAL (Parse.Term ‘toFloVerCmd ^varMap ^freshId ^f’) |> concl |> rhs
  |> optionSyntax.dest_some |> dest_trip;

val (P, dVars) =
  EVAL (Parse.Term ‘toFloVerPre [^cake_P] ^varMap’) |> concl |> rhs
  |> optionSyntax.dest_some |> dest_pair;

val theCmd =
  EVAL (Parse.Term ‘toRCmd ^theCmd’) |> concl |> rhs;

val letBounds =
  EVAL (Parse.Term ‘
       inferIntervalbounds (Fma (Const M64 (5404319552844595 / 9007199254740992)) (Var 0)
         (Const M64 (2915025227559731 / 8796093022208)))  ^P FloverMapTree_empty’)
|> concl |> rhs |> optionSyntax.dest_some;

val retBounds =
  EVAL (Parse.Term ‘
       inferIntervalbounds (Binop Mult (Unop Neg (Var 3)) (Var 1))
               ^P (FloverMapTree_insert (Var 3) (-89544170671082091725 / 9007199254740992,
                 149254695970611071795 / 9007199254740992) ^letBounds)’)
|> concl |> rhs |> optionSyntax.dest_some;

val retBounds2 =
  EVAL (Parse.Term ‘
       inferIntervalbounds (Binop Mult (Binop Plus (Var 3) (Var 2))
               (Binop Plus (Var 3) (Var 2))) ^P (FloverMapTree_insert (Var 3) (-89544170671082091725 / 9007199254740992,
                 149254695970611071795 / 9007199254740992) ^retBounds)’)

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
*)

val _ = export_theory();
