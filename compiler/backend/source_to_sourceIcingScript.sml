(*
  Source to source pass, applying Icing optimizations
*)

open semanticPrimitivesTheory evaluateTheory;
open terminationTheory;

open preamble;

val _ = new_theory "source_to_sourceIcing";

val _  = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option"];

Definition isFFIstable_def:
  isFFIstable e = ARB
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
    (case matchesFPexp lhs e [] of
    |  SOME subst =>
      (case appFPexp rhs subst of
      | SOME e_opt => rewriteFPexp rwtl e_opt
      | NONE => rewriteFPexp rwtl e)
    | NONE => rewriteFPexp rwtl e)
End

Definition rewriteFPcexp_def:
  rewriteFPcexp ([]:fp_rw list) (ce:exp) = ce /\
  rewriteFPcexp ((lhs, rhs)::rwtl) ce =
    (case matchesFPcexp lhs ce [] of
      | SOME subst =>
        (case appFPcexp rhs subst of
          | SOME ce_opt => rewriteFPcexp rwtl ce_opt
          | NONE => rewriteFPcexp rwtl ce)
      | NONE => rewriteFPcexp rwtl ce)
End

Definition fp_add_comm_def:
  fp_add_comm:fp_rw = (Binop FP_Add (Var 0) (Var 1), Binop FP_Add (Var 1) (Var 0))
End

val _ = export_theory();
