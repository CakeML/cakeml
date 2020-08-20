(*
  Implementation of the source to source floating-point rewriter
  This file defines the basic rewriter, used by the optimisation pass later.
  Correctness proofs are in icing_rewriterProofsScript.
*)
open bossLib fpValTreeTheory;
open terminationTheory;

open preamble;

val _ = new_theory "icing_rewriter";

val _  = monadsyntax.enable_monadsyntax();
val _ = List.app monadsyntax.enable_monad ["option"];

Definition isPureOp_def:
  isPureOp op =
    case op of
    | AallocEmpty => F
    | Aalloc => F
    | Aupdate => F
    | Aupdate_unsafe => F
    | Asub_unsafe => F
    | Aw8alloc => F
    | Aw8sub_unsafe => F
    | Aw8update => F
    | Aw8update_unsafe => F
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
  (matchesFPexp (Word w1) e s =
    case e of
    | Lit (Word64 w2) =>
      if (w1 = w2) then SOME s else NONE
    | _ => NONE) /\
  (matchesFPexp (Var n) e s =
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
  appFPexp (Word w) s = SOME (Lit (Word64 w)) /\
  appFPexp (Var n) s = substLookup s n /\
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
  appFPexp (Optimise sc p) s = NONE
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

val _ = export_theory ();
