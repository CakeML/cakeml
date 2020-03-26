(* CakeML *)
open compilerTheory;
(* FloVer *)
open RealIntervalInferenceTheory ErrorIntervalInferenceTheory
     CertificateCheckerTheory ExpressionsTheory CommandsTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVer";

Definition isFloVerExps_def:
  isFloVerExps [Var x] = T ∧
  isFloVerExps [App op exps] =
    (isFloVerExps exps  ∧
    (case op of
     | FP_bop _ => T
     | FP_uop FP_neg => T
     | FP_top _ => T
     | _ =>  F)) ∧
  isFloVerExps [e] = F ∧
  isFloVerExps (e1::es) = (isFloVerExps [e1] ∧ isFloVerExps es)
Termination
  wf_rel_tac `measure exp6_size`
End

Definition isFloVerCmd_def:
  isFloVerCmd (Let so e1 e2) =
  (case so of
   | SOME x => isFloVerExps [e1] ∧ isFloVerCmd e2
   | NONE => F) ∧
  isFloVerCmd (App op exps) = isFloVerExps exps ∧
  isFloVerCmd (Var x) = T ∧
  isFloVerCmd _ = F
End

Definition fpBopToFloVer_def:
  fpBopToFloVer (FP_Add) = Expressions$Plus ∧
  fpBopToFloVer (FP_Sub) = Sub ∧
  fpBopToFloVer (FP_Mul) = Mult ∧
  fpBopToFloVer (FP_Div) = Div
End

Definition lookupCMLVar_def:
  lookupCMLVar n ns = FIND (λ (m,i). n = m) ns
End

Definition lookupFloVerVar_def:
  lookupFloVerVar n ns = FIND (λ (m,i). n = i) ns
End

Definition appendCMLVar_def:
  appendVar n i ns =
  case (lookupCMLVar n ns) of
  | SOME _ => ns
  | NONE => (n,i)::ns
End

Definition toFloVerExp_def:
  expToFloVer ids freshId (ast$Var x) =
  (case (lookupCMLVar x ids) of
  | SOME (_,i) => SOME (ids, freshId, Expressions$Var i)
  | NONE => SOME (appendVar x freshId ids, freshId+1, Expressions$Var freshId)) ∧
  expToFloVer ids freshId (Lit (Word64 w)) =
    SOME (ids, freshId, Expressions$Const M64 (fp64_to_real w)) ∧
  expToFloVer ids freshId (App op exps) =
  (case (op, exps) of
   | (Opapp, [Var (Long "Double" (Short "fromString")); Lit s]) =>
     SOME (appendVar (Long "Double" (Short "fromString")) freshId ids, freshId+1, Expressions$Var freshId)
   | (FP_bop bop, [e1; e2]) =>
   (case expToFloVer ids freshId e1 of
    | NONE => NONE
    | SOME (ids2, freshId2, fexp1) =>
    (case expToFloVer ids2 freshId2 e2 of
     | NONE => NONE
     | SOME (ids3, freshId3, fexp2) =>
     SOME (ids3, freshId3, Expressions$Binop (fpBopToFloVer bop) fexp1 fexp2)))
   | (FP_uop FP_neg, [e1]) =>
   (case expToFloVer ids freshId e1 of
    | NONE => NONE
    | SOME (ids2, freshId2, fexp1) =>
    SOME (ids2, freshId2, Expressions$Unop Neg fexp1))
   | (FP_top _, [e1; e2; e3]) =>
   (case expToFloVer ids freshId e1 of
    | NONE => NONE
    | SOME (ids2, freshId2, fexp1) =>
    (case expToFloVer ids2 freshId2 e2 of
     | NONE => NONE
     | SOME (ids3, freshId3, fexp2) =>
     (case expToFloVer ids3 freshId3 e3 of
      | NONE => NONE
      | SOME (ids4, freshId4, fexp3) =>
      SOME (ids4, freshId4, Expressions$Fma fexp1 fexp2 fexp3))))
   | (_, _) => NONE)
  ∧
  expToFloVer _ _ _ = NONE
Termination
  wf_rel_tac `measure (λ (ids, n:num, e). ast$exp_size e)`
End

Definition toFloVerCmd_def:
  toFloVerCmd ids freshId (ast$Let so e1 e2) =
    (case so of
     | NONE => NONE
     | SOME x =>
     (case expToFloVer ids freshId e1 of
      |NONE => NONE
      |SOME (ids2, freshId2, fexp1) =>
      (case lookupCMLVar (Short x) ids of
       | SOME _ => NONE (* no SSA form*)
       | NONE =>
       case toFloVerCmd (appendVar (Short x) freshId2 ids2) (freshId2+1) e2 of
       | NONE => NONE
       | SOME (ids3, cmd1) => SOME (ids3, Commands$Let M64 freshId2 fexp1 cmd1)))) ∧
    toFloVerCmd ids freshId e =
    (case expToFloVer ids freshId e of
    | NONE => NONE
    | SOME (ids2, _, fexp1) => SOME (ids2, Commands$Ret fexp1))
End

Definition toFloVerEnv_def:
  toFloVerEnv (env:v sem_env)
              (idMap:((string, string) id # num) list)=
  λ (x:num).
  case lookupFloVerVar x idMap of
  |NONE => NONE
  |SOME (n,i) =>
  (case nsLookup env.v n of
   |SOME (Real r) => SOME r
   |_ => NONE)
End

Definition getRealCmp_def:
  getRealCmp (FP_Less) = Real_Less ∧
  getRealCmp (FP_LessEqual) = Real_LessEqual ∧
  getRealCmp (FP_Greater) = Real_Greater ∧
  getRealCmp (FP_GreaterEqual) = Real_GreaterEqual ∧
  getRealCmp (FP_Equal) = Real_Equal
End

Definition getRealUop_def:
  getRealUop (FP_Abs) = Real_Abs ∧
  getRealUop (FP_Neg) = Real_Neg ∧
  getRealUop (FP_Sqrt) = Real_Sqrt
End

Definition getRealBop_def:
  getRealBop (FP_Add) = Real_Add ∧
  getRealBop (FP_Sub) = Real_Sub ∧
  getRealBop (FP_Mul) = Real_Mul ∧
  getRealBop (FP_Div) = Real_Div
End

Definition toRealExp_def:
  toRealExp (Lit (Word64 w)) = App RealFromFP [Lit (Word64 w)] ∧
  toRealExp (Lit l) = Lit l ∧
  toRealExp (Var x) = Var x ∧
  toRealExp (Raise e) = Raise (toRealExp e) ∧
  toRealExp (Handle e pes) =
    Handle (toRealExp e) (MAP (\ (p,e). (p, toRealExp e)) pes) ∧
  toRealExp (Con mod exps) = Con mod (MAP toRealExp exps) ∧
  toRealExp (Fun s e) = Fun s (toRealExp e) ∧
  toRealExp (App op exps) =
    (let exps_real = MAP toRealExp exps in
     case op of
     | FP_cmp cmp => App (Real_cmp (getRealCmp cmp)) exps_real
     | FP_uop uop => App (Real_uop (getRealUop uop)) exps_real
     | FP_bop bop => App (Real_bop (getRealBop bop)) exps_real
     | FP_top _ =>
     (case exps of
      | [e1; e2; e3] => App (Real_bop (Real_Add)) [
                          App (Real_bop (Real_Mul)) [e2; e3]; e1]
      | _ => App op exps_real) (* malformed expression, return garbled output *)
     | _ => App op exps_real) ∧
  toRealExp (Log lop e2 e3) =
    Log lop (toRealExp e2) (toRealExp e3) ∧
  toRealExp (If e1 e2 e3) =
    If (toRealExp e1) (toRealExp e2) (toRealExp e3) ∧
  toRealExp (Mat e pes) =
    Mat (toRealExp e) (MAP (λ(p,e). (p, toRealExp e)) pes) ∧
  toRealExp (Let so e1 e2) =
    Let so (toRealExp e1) (toRealExp e2) ∧
  toRealExp (Letrec ses e) =
    Letrec (MAP (λ (s1,s2,e). (s1, s2, toRealExp e)) ses) (toRealExp e) ∧
  toRealExp (Tannot e t) = Tannot (toRealExp e) t ∧
  toRealExp (Lannot e l) = Lannot (toRealExp e) l ∧
  toRealExp (FpOptimise sc e) = FpOptimise sc (toRealExp e)
Termination
  wf_rel_tac ‘measure exp_size’ \\ fs[astTheory.exp_size_def] \\ rpt conj_tac
  >- (Induct_on `ses` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `mod'` assume_tac) \\ fs[])
End

Definition strip_def:
  strip (FpOptimise _ e) = strip e ∧
  strip e = e
End

Definition rm_top_match_def:
  rm_top_match (Mat _ [(Pcon NONE _, e)]) = e ∧
  rm_top_match e = e
End

Definition getErrorbounds_def:
  getErrorbounds f Gamma P =
    let
      (theIds, theCmd) = THE (toFloVerCmd [] 0 (rm_top_match (strip f)));
      theRealBounds = THE (inferIntervalboundsCmd theCmd P FloverMapTree_empty);
      typeMap = case (getValidMapCmd Gamma theCmd FloverMapTree_empty) of
                | Succes t => t;
    in
      inferErrorboundCmd theCmd typeMap theRealBounds FloverMapTree_empty
End

val _ = export_theory ();
