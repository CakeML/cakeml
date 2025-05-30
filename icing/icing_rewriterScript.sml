(*
  Implementation of the source to source floating-point rewriter
  This file defines the basic rewriter, used by the optimisation pass later.
  Correctness proofs are in icing_rewriterProofsScript.
*)
open bossLib fpValTreeTheory pureExpsTheory;

open preamble;

val _ = new_theory "icing_rewriter";

val _  = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option"];

(* matching function for expressions *)
Definition matchesFPexp_def:
  (matchesFPexp (Word w1) e s =
    case e of
    | App FpFromWord [Lit (Word64 w2)] =>
      if (w1 = w2) then SOME s else NONE
    | _ => NONE) /\
  (matchesFPexp (PatVar n) e s =
    case substLookup s n of
    | SOME e1 => if e1 = e then SOME s else NONE
    | NONE => SOME (substAdd n e s)) /\
  (matchesFPexp (Unop op1 p1) e s =
    case e of
    | App (FP_uop op2) [e1] =>
      (if (op1 = op2)
      then matchesFPexp p1 e1 s
      else NONE)
    | _ => NONE) /\
  (matchesFPexp (Binop op1 p1 p2) e s =
    case e of
    | App (FP_bop op2) [e1;e2] =>
      (if (op1 = op2)
       then
       (case matchesFPexp p1 e1 s of
        | NONE => NONE
        | SOME s1 => matchesFPexp p2 e2 s1)
       else NONE)
    | _ => NONE) /\
  (matchesFPexp (Terop op1 p1 p2 p3) e s =
   case e of
   | App (FP_top op2) [e1;e2;e3] =>
      (if (op1 = op2)
      then
       (case matchesFPexp p1 e1 s of
        | NONE => NONE
        | SOME s1 =>
        (case matchesFPexp p2 e2 s1 of
         | NONE => NONE
         | SOME s2 => matchesFPexp p3 e3 s2))
       else NONE)
      | _ => NONE) ∧
  (matchesFPexp (Cmp cmp1 p1 p2) e s =
   case e of
   | App (FP_cmp cmp2) [e1; e2] =>
     (if (cmp1 = cmp2) then
       (case matchesFPexp p1 e1 s of
        | NONE => NONE
        | SOME s1 => matchesFPexp p2 e2 s1)
       else NONE)
   | _ => NONE) ∧
  (matchesFPexp (Optimise sc1 p1) e s = NONE)
End

(* Instantiate a given fp_pattern with a substitution into an expression *)
Definition appFPexp_def:
  appFPexp (Word w) s = SOME (App FpFromWord [Lit (Word64 w)]) /\
  appFPexp (PatVar n) s = substLookup s n /\
  appFPexp (Unop u p) s = (do e <- appFPexp p s; return (App (FP_uop u) [e]); od) /\
  appFPexp (Binop op p1 p2) s =
    (case appFPexp p1 s of
    | NONE => NONE
    | SOME e1 =>
      (case appFPexp p2 s of
      | NONE => NONE
      | SOME e2 => SOME (App (FP_bop op) [e1; e2]))) /\
  appFPexp (Terop op p1 p2 p3) s =
    (case appFPexp p1 s of
    | NONE => NONE
    | SOME e1 =>
      (case appFPexp p2 s of
      | NONE => NONE
      | SOME e2 =>
        (case appFPexp p3 s of
        | NONE => NONE
        | SOME e3 => SOME (App (FP_top op) [e1; e2; e3])))) /\
  appFPexp (Cmp cmp p1 p2) s =
    (case appFPexp p1 s of
    | NONE => NONE
    | SOME e1 =>
      (case appFPexp p2 s of
      | NONE => NONE
      | SOME e2 => SOME (App (FP_cmp cmp) [e1; e2]))) /\
  appFPexp (Optimise fpopt p) s = NONE
End

Definition isFpArithPat_def:
  isFpArithPat (Word w) = T ∧
  isFpArithPat (PatVar n) = T ∧
  isFpArithPat (Unop u p) = isFpArithPat p ∧
  isFpArithPat (Binop b p1 p2) = (isFpArithPat p1 ∧ isFpArithPat p2) ∧
  isFpArithPat (Terop t p1 p2 p3) =
    (isFpArithPat p1 ∧ isFpArithPat p2 ∧ isFpArithPat p3) ∧
  isFpArithPat (Cmp _ _ _) = F ∧
  isFpArithPat (Optimise _ p) = isFpArithPat p
End

Definition isFpArithExp_def:
  isFpArithExp (Var x) = T ∧
  isFpArithExp (App FpFromWord [Lit (Word64 w)]) = T ∧
  isFpArithExp (App (FP_uop _) exps) = (LENGTH exps = 1 ∧ isFpArithExpList exps) ∧
  isFpArithExp (App (FP_bop _) exps) = (LENGTH exps = 2 ∧ isFpArithExpList exps) ∧
  isFpArithExp (App (FP_top _) exps) = (LENGTH exps = 3 ∧ isFpArithExpList exps) ∧
  (* isFpArithExp (Let x e1 e2) = (isFpArithExp e1 ∧ isFpArithExp e2) ∧ *)
  isFpArithExp _ = F ∧
  isFpArithExpList [] = T ∧
  isFpArithExpList (e1 :: es) = (isFpArithExp e1 ∧ isFpArithExpList es)
Termination
  wf_rel_tac ‘measure (λ x. case x of |INR exps => exp6_size exps |INL e => exp_size e)’
End

(* rewriteExp: Recursive, expression rewriting function applying all rewrites that match.
  A non-matching rewrite is silently ignored *)
Definition rewriteFPexp_def:
  rewriteFPexp ([]:fp_rw list) (e:exp) = e /\
  rewriteFPexp ((lhs,rhs)::rwtl) e =
    if (isPureExp e ∧ isFpArithPat lhs ∧ isFpArithPat rhs ∧ isFpArithExp e)
    then
      (case matchesFPexp lhs e [] of
      |  SOME subst =>
          (case appFPexp rhs subst of
          | SOME e_opt => rewriteFPexp rwtl e_opt
          | NONE => rewriteFPexp rwtl e)
      | NONE => rewriteFPexp rwtl e)
    else e
End

val _ = export_theory ();
