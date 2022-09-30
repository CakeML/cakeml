(*
  Theorems and definitions to support adding runtime type checking annotations.
 *)

open preamble ml_translatorTheory ml_translatorLib holKernelTheory
     mlstringTheory;

val _ = new_theory "runtime_check";

Theorem pure_seq_intro:
  x = y ⇒ ∀z. x = pure_seq z y
Proof
  fs [pure_seq_def]
QED

(* It's annoying but these few functions need to appear here and in checkLib *)

fun type_check ty =
  “case ^ty of Tyvar _ => () | _ => abc” |> subst [“abc:unit”|->“()”];

fun term_check tm =
  “case ^tm of Const _ _ => () | _ => abc” |> subst [“abc:unit”|->“()”];

fun thm_check th =
  “case ^th of Sequent _ _ => ()”;

val t1 = type_check “t1:type”
val t2 = type_check “t2:type”
val tm = term_check “tm:term”
val tm' = term_check “tm':term”
val th = PmatchHeuristics.with_classic_heuristic thm_check “th:thm”

Definition check_ty_def:
  check_ty [] = () ∧
  check_ty (t1::l) = pure_seq ^t1 (check_ty l)
End

Definition check_tm_def:
  check_tm [] = () ∧
  check_tm (tm::l) = pure_seq ^tm (check_tm l)
End

Definition check_thm_def:
  check_thm [] = () ∧
  check_thm (th::l) = pure_seq ^th (check_thm l)
End

Definition check_ty_ty_def:
  check_ty_ty [] = () ∧
  check_ty_ty ((t1,t2)::l) = pure_seq ^t1 (pure_seq ^t2 (check_ty_ty l))
End

Definition check_tm_tm_def:
  check_tm_tm [] = () ∧
  check_tm_tm ((tm,tm')::l) = pure_seq ^tm (pure_seq ^tm' (check_tm_tm l))
End

val _ = export_theory ();

