(*
  Source to source pass, applying Icing optimizations
*)
open semanticPrimitivesTheory evaluateTheory;
open terminationTheory;

open preamble;

val _ = new_theory "source_to_sourceIcing";

val _  = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option"];

Definition isPureOp_def:
  isPureOp op =
    case op of
    | AallocEmpty => F
    | Aalloc => F
    | Aupdate => F
    | Aw8alloc => F
    | Aw8update => F
    | Aw8length => F
    | Aw8sub => F
    | Alength => F
    | Asub => F
    | CopyAw8Aw8 => F
    | CopyStrAw8 => F
    | CopyAw8Str => F
    | FFI _ => F
    | Opassign => F
    | Opapp => F
    | Opderef => F
    | Opref => F
    | _ => T
End

Definition isPurePat_def:
  (isPurePat (Pvar _) = T) /\
  (isPurePat (Plit _) = T) /\
  (isPurePat (Pcon _ pl) = isPurePatList pl) /\
  (isPurePat (Ptannot p _) = isPurePat p) /\
  (isPurePat _ = F)
  /\
  (isPurePatList [] = T) /\
  (isPurePatList (p::pl) = (isPurePat p /\ isPurePatList pl))
Termination
  wf_rel_tac `measure (\x. case x of |INL p =>  pat_size p | INR pl => pat1_size pl)`
End

Definition isPureExp_def:
  (isPureExp (Raise e) = F) /\
  (isPureExp (Handle e l) = F) /\
  (isPureExp (Lit _) = T) /\
  (isPureExp (Con _ exl) = isPureExpList exl) /\
  (isPureExp (Var _) = T) /\
  (isPureExp (Fun _ _) = F) /\
  (isPureExp (App op exl) = (isPureOp op /\ isPureExpList exl)) /\
  (isPureExp (Log _ e1 e2) = (isPureExp e1 /\ isPureExp e2)) /\
  (isPureExp (If e1 e2 e3) = (isPureExp e1 /\ isPureExp e2 /\ isPureExp e3)) /\
  (isPureExp (Mat e pel) = (isPureExp e /\ isPurePatExpList pel)) /\
  (isPureExp (Let _ e1 e2) = (isPureExp e1 /\ isPureExp e2)) /\
  (isPureExp (Letrec _ _) = F) /\
  (isPureExp (Tannot e a) = isPureExp e) /\
  (isPureExp (Lannot e l) = isPureExp e) /\
  (isPureExp (FpOptimise _ e) = isPureExp e)
  /\
    isPureExpList [] = T /\
    isPureExpList (e::exl) = (isPureExp e /\ isPureExpList exl)
  /\
    isPurePatExpList [] = T /\
    isPurePatExpList ((p,e)::pel) = (isPurePat p /\ isPureExp e /\ isPurePatExpList pel)
Termination
  wf_rel_tac (`measure
    \ x. case x of
          | INL e => exp_size e
          | INR (INL exl) => exp6_size exl
          | INR (INR pel) => exp3_size pel`)
End

(* matching function for expressions *)
Definition matchesFPexp_def:
  matchesFPexp p e s =
    case (p, e) of
    | Word w1, Lit (Word64 w2) =>
      if (w1 = w2) then SOME s else NONE
    | Var n, _ =>
      (case substLookup s n of
      | SOME e1 => if e1 = e  then SOME s else NONE
      | NONE => substUpdate n e s)
    | Unop op1 p, App (FP_uop op2) [e1] =>
      (if (op1 = op2)
      then matchesFPexp p e1 s
      else NONE)
    | Binop op1 p1 p2, App (FP_bop op2) [e1;e2] =>
      (if (op1 = op2)
      then do
        s1 <- matchesFPexp p1 e1 s;
        matchesFPexp p2 e2 s1;
        od
      else NONE)
    | Terop op1 p1 p2 p3, App (FP_top op2) [e1;e2;e3] =>
      (if (op1 = op2)
      then do
        s1 <- matchesFPexp p1 e1 s;
        s2 <- matchesFPexp p2 e2 s1;
        matchesFPexp p3 e3 s2;
        od
      else NONE)
  (*
    | Scope sc1 p, App (FP_sc sc2) [e1] =>
      (if sc1 = sc2
      then matchesFPexp p e1 s
      else NONE) *)
    | _, _ => NONE
Termination
  wf_rel_tac (`measure \ (x,y,z). fp_pat_size x`)
End

Definition matchesFPcexp_def:
  matchesFPcexp p e s =
    case p, e of
    | Pred p1 p, App (FP_pred p2) [e1] =>
      (if (p1 = p2) then matchesFPexp p e1 s else NONE)
    | Cmp cmp1 p1 p2, App (FP_cmp cmp2) [e1; e2] =>
      (if (cmp1 = cmp2)
      then do
        s1 <- matchesFPexp p1 e1 s;
        matchesFPexp p2 e2 s1;
        od
      else NONE)
    (*
    | Scope sc1 p, App (FP_sc sc2) [e1] =>
      (if sc1 = sc2 then matchesFPcexp p e1 s else NONE) *)
    | _, _ => NONE
End

(* Instantiate a given fp_pattern with a substitution into an expression *)
Definition appFPexp_def:
  appFPexp (Word w) s = SOME (Lit (Word64 w)) /\
  appFPexp (Var n) s = substLookup s n /\
  appFPexp (Unop u p) s = (do e <- appFPexp p s; return (App (FP_uop u) [e]); od) /\
  appFPexp (Binop op p1 p2) s =
    (do
      e1 <- appFPexp p1 s;
      e2 <- appFPexp p2 s;
      return (App (FP_bop op) [e1; e2]);
    od) /\
  appFPexp (Terop op p1 p2 p3) s =
    (do
      e1 <- appFPexp p1 s;
      e2 <- appFPexp p2 s;
      e3 <- appFPexp p3 s;
      return (App (FP_top op) [e1; e2; e3]);
    od) /\
  (*
  appFPexp (Scope sc p) s =
    (do
      e <- appFPexp p s;
      return (App (FP_sc sc) [e]);
    od) /\ *)
  appFPexp _ _ = NONE
End

Definition appFPcexp_def:
  appFPcexp (Pred pr p) s =
    (do
      e <- appFPexp p s;
      return (App (FP_pred pr) [e]);
    od) /\
  appFPcexp (Cmp cmp p1 p2) s =
    (do
      e1 <- appFPexp p1 s;
      e2 <- appFPexp p2 s;
      return (App (FP_cmp cmp) [e1; e2]);
    od) /\
  (*
  appFPcexp (Scope sc p) s =
    (do
      e <- appFPcexp p s;
      return (App (FP_sc sc) [e]);
    od) /\ *)
  appFPcexp _ _ = NONE
End

(* rewriteExp: Recursive, expression rewriting function applying all rewrites that match.
  A non-matching rewrite is silently ignored *)
Definition rewriteFPexp_def:
  rewriteFPexp ([]:fp_rw list) (e:exp) = e /\
  rewriteFPexp ((lhs,rhs)::rwtl) e =
    if (isPureExp e)
    then
      (case matchesFPexp lhs e [] of
      |  SOME subst =>
          (case appFPexp rhs subst of
          | SOME e_opt => rewriteFPexp rwtl e_opt
          | NONE => rewriteFPexp rwtl e)
      | NONE => rewriteFPexp rwtl e)
    else e
End

Definition rewriteFPcexp_def:
  rewriteFPcexp ([]:fp_rw list) (ce:exp) = ce /\
  rewriteFPcexp ((lhs, rhs)::rwtl) ce =
    if (isPureExp ce)
    then
      (case matchesFPcexp lhs ce [] of
        | SOME subst =>
          (case appFPcexp rhs subst of
            | SOME ce_opt => rewriteFPcexp rwtl ce_opt
            | NONE => rewriteFPcexp rwtl ce)
        | NONE => rewriteFPcexp rwtl ce)
    else ce
End

Definition fp_comm_gen_def:
  fp_comm_gen op = (Binop op (Var 0) (Var 1), Binop op (Var 1) (Var 0))
End

val fp_add_comm_def =
  curry save_thm "fp_add_comm_def" (Q.SPEC `FP_Add` fp_comm_gen_def);

val fp_mul_comm_def =
  curry save_thm "fp_mul_comm_def" (Q.SPEC `FP_Mul` fp_comm_gen_def);

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

Definition fp_double_neg_def:
  fp_double_neg = (Unop FP_Neg (Unop FP_Neg (Var 0)), Var 0)
End

Definition fp_mul_distrib_def:
  fp_mul_distrib = (Binop FP_Mul (Var 0) (Binop FP_Add (Var 1) (Var 2)),
                    Binop FP_Add (Binop FP_Mul (Var 0) (Var 1))
                                 (Binop FP_Mul (Var 0) (Var 2)))
End

Definition fp_fma_intro_def:
  fp_fma_intro = (Binop FP_Add (Binop FP_Mul (Var 0) (Var 1)) (Var 2),
                  Terop FP_Fma (Var 0) (Var 1) (Var 2))
End

(**
  TODO: Compilation
  Step 1) Apply rewrites when applicable, introduce preconditions by preceding with an assert statement
  Step 2) Remove any occurrences of Opt scopes to disallow further optimizations
**)

(**
  FIXME: Step 1
**)
Definition Icing_optimize_def:
  Icing_optimize e rws = e
End

(**
  FIXME: Step 2
**)
Definition Icing_finish_def:
  Icing_finish e = e
End

Definition do_Icing_def:
  do_Icing e rws = Icing_finish (Icing_optimize e rws)
End

val _ = export_theory();
