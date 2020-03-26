(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open compilerTheory;
(* FloVer *)
open ExpressionsTheory CommandsTheory;
(* Icing *)
open CakeMLtoFloVerTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVerProofs";

Theorem CakeML_FloVer_real_equiv:
! e (st st2:'a semanticPrimitives$state) env e r.
  (* the CakeML code can be translated into FloVer input *)
  isFloVerCmd e ==>
  ? ids f.
    (* the translation to FloVer does not fail *)
    toFloVerCmd [] 0 e = SOME (ids, f) /\
    (* evaluation on reals in CakeML is equivalent to evaluation in FloVer *)
    (evaluate st env [toRealExp e] = (st2, Rval [Real r]) <=>
     bstep f (toFloVerEnv env ids) Gamma r REAL)
Proof
  cheat
QED

Theorem CakeML_FloVer_infer_error:
! e (st st2:'a semanticPrimitives$state) env e w Gamma P analysisResult.
  (* the CakeML code can be translated into FloVer input *)
  isFloVerCmd e /\
  (* the CakeML code returns a valid floating-point word *)
  evaluate st env [e] = (st2, Rval [FP_WordTree w]) /\
  (* translating to FloVer, running the pipeline succeeds *)
  getErrorbounds e Gamma P = SOME analysisResult ==>
  ? ids f iv err r.
    (* the translation to FloVer does not fail *)
    toFloVerCmd [] 0 e = SOME (ids, f) /\
    (* the analysis result returned contains an error bound *)
    FloverMapTree_find (getRetExp f) analysisResult = SOME (iv,err) /\
    (* we can evaluate with a real-valued semantics *)
    evaluate st env [toRealExp e] = (st2, Rval [Real r]) /\
    (* the roundoff error is sound *)
    real$abs ((fp64_to_real (case (compress (FP_WordTree w)) of Litv (Word64 w) => w) - r))
      <= err
Proof
  cheat
QED

val _ = export_theory ();
