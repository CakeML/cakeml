(*
  Source to source pass, applying Icing optimizations
*)
open semanticPrimitivesTheory evaluateTheory source_rewriterTheory;
open terminationTheory;

open preamble;

val _ = new_theory "source_to_source";

(**
  Source to source optimization definitions
**)

(*
  Commutativity
*)
Definition fp_comm_gen_def:
  fp_comm_gen op = (Binop op (Var 0) (Var 1), Binop op (Var 1) (Var 0))
End

val fp_add_comm_def =
  curry save_thm "fp_add_comm_def" (Q.SPEC `FP_Add` fp_comm_gen_def);

val fp_mul_comm_def =
  curry save_thm "fp_mul_comm_def" (Q.SPEC `FP_Mul` fp_comm_gen_def);

(*
  Associativity
*)
Definition fp_assoc_gen_def:
  fp_assoc_gen op = (Binop op (Binop op (Var 0) (Var 1)) (Var 2),
                     Binop op (Var 0) (Binop op (Var 1) (Var 2)))
End

val fp_add_assoc_def =
  curry save_thm "fp_add_assoc_def"
    (Q.SPEC `FP_Add` fp_assoc_gen_def);

val fp_mul_assoc_def =
  curry save_thm "fp_mul_assoc_def"
    (Q.SPEC `FP_Mul` fp_assoc_gen_def);

(*
  Double negation
*)
Definition fp_double_neg_def:
  fp_double_neg = (Unop FP_Neg (Unop FP_Neg (Var 0)), Var 0)
End

(*
  Distributivity of multiplication over addition
*)
Definition fp_mul_distrib_def:
  fp_mul_distrib = (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
                    Binop FP_Add (Binop FP_Mul (Var 0) (Var 1))
                                 (Binop FP_Mul (Var 0) (Var 2)))
End

(*
  FMA introudction
*)
Definition fp_fma_intro_def:
  fp_fma_intro = (Binop FP_Add (Binop FP_Mul (Var 0) (Var 1)) (Var 2),
                  Terop FP_Fma (Var 0) (Var 1) (Var 2))
End

Datatype:
  config = <|
    optimisations : (fp_pat # fp_pat) list;
    canOpt : bool |>
End
(**
  TODO: Compilation
  Step 1) Apply rewrites when applicable, introduce preconditions by preceding with an assert statement
  Step 2) Remove any occurrences of Opt scopes to disallow further optimizations
**)

(* Step 1 *)
Definition optimise_def:
  optimise cfg (Lit l) = Lit l /\
  optimise cfg (Var x) = Var x /\
  optimise (cfg:config) (Raise e) =
    Raise (optimise cfg e) /\
  optimise cfg (Handle e pes) =
    Handle (optimise cfg e) (MAP (\ (p,e). (p, optimise cfg e)) pes) /\
  optimise cfg (Con mod exps) =
    Con mod (MAP (optimise cfg) exps) /\
  optimise cfg (Fun s e) =
    Fun s (optimise cfg e) /\
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
    Letrec (MAP (\ (s1,s2,e). (s1, s2, optimise cfg e)) ses) (optimise cfg e) /\
  optimise cfg (Tannot e t) =
    Tannot (optimise cfg e) t /\
  optimise cfg (Lannot e l) =
    Lannot (optimise cfg e) l /\
  optimise cfg (FpOptimise sc e) =
    FpOptimise sc (optimise (cfg with canOpt := if sc = Opt then T else F) e)
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

(*
  Step 2
*)
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
    Fun s e (* (no_optimisations cfg e)*) /\
  no_optimisations cfg (App op exps) =
    App op (MAP (no_optimisations cfg) exps) /\
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
  no_optimisations cfg (FpOptimise sc e) =
    FpOptimise NoOpt (no_optimisations cfg e)
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

Definition compile_def:
  compile (cfg:config) e = no_optimisations cfg (optimise cfg e)
End

val _ = export_theory();
