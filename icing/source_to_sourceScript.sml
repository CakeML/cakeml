(*
  Source to source pass, applying Icing optimizations
*)
open semanticPrimitivesTheory evaluateTheory terminationTheory
     icing_rewriterTheory icing_optimisationsTheory;

open preamble;

val _ = new_theory "source_to_source";

(**
  Rewriter configuration
  optimisations is the list of Icing-optimisations that may be applied by the
  rewriter
  canOpt is a flag that memorizes whether or not optimisation has passed through
  a "Opt" annotation
**)
Datatype:
  config = <|
    optimisations : (fp_pat # fp_pat) list;
    canOpt : bool |>
End

(**
  Define an empty configuration
**)
Definition no_fp_opt_conf_def:
  no_fp_opt_conf = <| optimisations := []; canOpt := F |>
End

Definition extend_conf_def:
  extend_conf (cfg:config) rws =
    cfg with optimisations := cfg.optimisations ++ rws
End

Theorem extend_conf_canOpt[simp]:
  (extend_conf cfg rws).canOpt = cfg.canOpt
Proof
  fs[extend_conf_def]
QED

(** Optimisation pass starts below **)

(** Step 1:
    optimise walks over the body of a function declaration/letrec and
    applies the optimisations in the configuration depending on whether a
    Opt scope was already encountered or not
 **)
Definition optimise_def:
  optimise cfg (Lit l) = Lit l /\
  optimise cfg (Var x) = Var x /\
  optimise (cfg:config) (Raise e) =
    Raise (optimise cfg e) /\
  (* We cannot support "Handle" expressions because we must be able to reorder exceptions *)
  optimise cfg (Handle e pes) = Handle e pes ∧
  optimise cfg (Con mod exps) =
    Con mod (MAP (optimise cfg) exps) /\
  optimise cfg (Fun s e) =
    Fun s e (* (optimise cfg e)*) /\
  optimise cfg (App op exps) =
    (let exps_opt = MAP (optimise cfg) exps in
      if (cfg.canOpt)
      then (rewriteFPexp (cfg.optimisations) (App op exps_opt))
      else (App op exps_opt)) /\
  optimise cfg (Log lop e2 e3) =
    Log lop (optimise cfg e2) (optimise cfg e3) /\
  optimise cfg (If e1 e2 e3) =
    If (optimise cfg e1) (optimise cfg e2) (optimise cfg e3) /\
  optimise cfg (Mat e pes) =
    Mat (optimise cfg e) (MAP (\ (p,e). (p, optimise cfg e)) pes) /\
  optimise cfg (Let so e1 e2) =
    Let so (optimise cfg e1) (optimise cfg e2) /\
  optimise cfg (Letrec ses e) =
    Letrec ses (* (MAP (\ (s1,s2,e). (s1, s2, optimise cfg e)) ses) *) (optimise cfg e) /\
  optimise cfg (Tannot e t) =
    Tannot (optimise cfg e) t /\
  optimise cfg (Lannot e l) =
    Lannot (optimise cfg e) l /\
  optimise cfg (FpOptimise sc e) =
    FpOptimise sc (optimise (cfg with canOpt := if sc = Opt then T else F) e)
Termination
  WF_REL_TAC `measure (\ (c,e). exp_size e)` \\ fs[]
  \\ rpt conj_tac
  (*
  >- (Induct_on `ses` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[]) *)
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[])
     (*
  >- (Induct_on `pes` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `e` assume_tac) \\ fs[]) *)
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `op` assume_tac) \\ fs[])
  >- (Induct_on `exps` \\ fs[astTheory.exp_size_def]
      \\ rpt strip_tac \\ res_tac \\ rveq \\ fs[astTheory.exp_size_def]
      \\ first_x_assum (qspec_then `mod` assume_tac) \\ fs[])
End

(**
  Step 2: Lifting of optimise to expression lists
  stos_pass walks over a list of expressions and calls optimise on
  function bodies
**)
Definition stos_pass_def:
  stos_pass cfg [] = [] ∧
  stos_pass cfg (e1::e2::es) =
    (stos_pass cfg [e1]) ++ (stos_pass cfg (e2::es))  ∧
  stos_pass cfg [Fun s e] =
    [Fun s (HD (stos_pass cfg [e]))] ∧
  stos_pass cfg [e] = [optimise cfg e]
End

(* Step 3: Disallow further optimisations *)
Definition no_optimisations_def:
  no_optimisations cfg (Lit l) = Lit l /\
  no_optimisations cfg (Var x) = Var x /\
  no_optimisations (cfg:config) (Raise e) =
    Raise (no_optimisations cfg e) /\
  no_optimisations cfg (Handle e pes) =
    Handle (no_optimisations cfg e) (MAP (\ (p,e). (p, no_optimisations cfg e)) pes) /\
  no_optimisations cfg (Con mod exps) =
    Con mod (MAP (no_optimisations cfg) exps) /\
  no_optimisations cfg (Fun s e) =
    Fun s (no_optimisations cfg e) /\
  no_optimisations cfg (App op exps) = App op (MAP (no_optimisations cfg) exps) /\
  no_optimisations cfg (Log lop e2 e3) =
    Log lop (no_optimisations cfg e2) (no_optimisations cfg e3) /\
  no_optimisations cfg (If e1 e2 e3) =
    If (no_optimisations cfg e1) (no_optimisations cfg e2) (no_optimisations cfg e3) /\
  no_optimisations cfg (Mat e pes) =
    Mat (no_optimisations cfg e) (MAP (\ (p,e). (p, no_optimisations cfg e)) pes) /\
  no_optimisations cfg (Let so e1 e2) =
    Let so (no_optimisations cfg e1) (no_optimisations cfg e2) /\
  no_optimisations cfg (Letrec ses e) =
    Letrec (MAP (\ (s1,s2,e). (s1, s2, no_optimisations cfg e)) ses) (no_optimisations cfg e) /\
  no_optimisations cfg (Tannot e t) =
    Tannot (no_optimisations cfg e) t /\
  no_optimisations cfg (Lannot e l) =
    Lannot (no_optimisations cfg e) l /\
  no_optimisations cfg (FpOptimise sc e) = FpOptimise NoOpt (no_optimisations cfg e)
Termination
  WF_REL_TAC `measure (\ (c,e). exp_size e)` \\ fs[]
  \\ rpt conj_tac
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
      \\ first_x_assum (qspec_then `mod` assume_tac) \\ fs[])
End

(**
Definition compile_exps_def:
  compile_exps (cfg:config) exps = MAP (\e. FpOptimise NoOpt (no_optimisations cfg (optimise cfg e))) exps
End
**)

(**
  stos_pass_decs: Lift stos_pass to declarations
**)
Definition stos_pass_decs_def:
  stos_pass_decs cfg [] = [] ∧
  stos_pass_decs cfg (d1::d2::ds) =
    (stos_pass_decs cfg [d1] ++ stos_pass_decs cfg (d2::ds)) ∧
  stos_pass_decs cfg [Dlet loc p e] =
    [Dlet loc p (HD (stos_pass cfg [e]))] ∧
  (* No Dletrec support for now -- stos_pass_decs cfg [Dletrec ls exps] =
    [Dletrec ls (MAP (λ (fname, param, e). (fname, param, HD (stos_pass cfg [e]))) exps)] ∧ *)
  stos_pass_decs cfg [d] = [d]
End

Definition no_opt_decs_def:
  no_opt_decs cfg [] = [] ∧
  no_opt_decs cfg (e1::e2::es) =
    (no_opt_decs cfg [e1] ++ no_opt_decs cfg (e2::es)) ∧
  no_opt_decs cfg [Dlet loc p e] =
    [Dlet loc p (no_optimisations cfg e)] ∧
  no_opt_decs cfg [Dletrec ls exps] =
    [Dletrec ls (MAP (λ (fname, param, e). (fname, param, no_optimisations cfg e)) exps)] ∧
  no_opt_decs cfg [d] = [d]
End

(*
Definition compile_decs_def:
  compile_decs (cfg:config) [] = [] /\
  compile_decs (cfg:config) [Dlet l p e] = [Dlet l p (HD (compile_exps cfg [e]))] /\
  compile_decs cfg [Dletrec ls vexps] =
    [Dletrec ls (MAP (\ (v1,v2,e). (v1,v2,HD (compile_exps cfg [e]))) vexps)] /\
  compile_decs cfg [Dtype l t] = [Dtype l t] /\
  compile_decs cfg [Dtabbrev l vars t ast] = [Dtabbrev l vars t ast] /\
  compile_decs cfg [Dexn l c asts] = [Dexn l c asts] /\
  compile_decs cfg [Dmod m decls] = [Dmod m (compile_decs cfg decls)] /\
  compile_decs cfg [Dlocal decls1 decls2] =
    [Dlocal (compile_decs cfg decls1) (compile_decs cfg decls2)] /\
  compile_decs cfg (d1::d2::ds) = compile_decs cfg [d1] ++ compile_decs cfg (d2::ds)
Termination
  wf_rel_tac `measure (\ (cfg,decls). dec1_size decls)`
End
*)

(** Translation from FP ops to Real ops **)
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

Definition realify_def:
  realify (Lit (Word64 w)) = Lit (Word64 w) (* RealFromFP added in App case *)∧
  realify (Lit l) = Lit l ∧
  realify (Var x) = Var x ∧
  realify (Raise e) = Raise (realify e) ∧
  realify (Handle e pes) =
    Handle (realify e) (MAP (\ (p,e). (p, realify e)) pes) ∧
  realify (Con mod exps) = Con mod (MAP realify exps) ∧
  realify (Fun s e) = Fun s (realify e) ∧
  realify (App op exps) =
    (let exps_real = MAP realify exps in
     case op of
     | FpFromWord => App  RealFromFP exps_real
     | FP_cmp cmp => App (Real_cmp (getRealCmp cmp)) exps_real
     | FP_uop uop => App (Real_uop (getRealUop uop)) exps_real
     | FP_bop bop => App (Real_bop (getRealBop bop)) exps_real
     | FP_top _ =>
     (case exps of
      | [e1; e2; e3] => App (Real_bop (Real_Add)) [
                          App (Real_bop (Real_Mul)) [realify e2; realify e3]; realify e1]
      | _ => App op exps_real) (* malformed expression, return garbled output *)
     | _ => App op exps_real) ∧
  realify (Log lop e2 e3) =
    Log lop (realify e2) (realify e3) ∧
  realify (If e1 e2 e3) =
    If (realify e1) (realify e2) (realify e3) ∧
  realify (Mat e pes) =
    Mat (realify e) (MAP (λ(p,e). (p, realify e)) pes) ∧
  realify (Let so e1 e2) =
    Let so (realify e1) (realify e2) ∧
  realify (Letrec ses e) =
    Letrec (MAP (λ (s1,s2,e). (s1, s2, realify e)) ses) (realify e) ∧
  realify (Tannot e t) = Tannot (realify e) t ∧
  realify (Lannot e l) = Lannot (realify e) l ∧
  realify (FpOptimise sc e) = FpOptimise sc (realify e)
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
      \\ first_x_assum (qspec_then `mod` assume_tac) \\ fs[])
End

val _ = export_theory();
