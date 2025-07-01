(*
  TODO Add to astScript
*)

open preamble
open astTheory

val _ = new_theory "extension_ast";

Definition Seqs_def:
  Seqs [] = Con NONE [] ∧
  Seqs (x::xs) = Let NONE x (Seqs xs)
End

(* TODO rename apps -> Apps *)
Definition apps_def:
  apps f [] = f ∧
  apps f (x::xs) = apps (App Opapp [f; x]) xs
End

Definition Funs_def:
  Funs [] e = e ∧
  Funs (x::xs) e = Fun x (Funs xs e)
End

val _ = export_theory ();
