(*
  Simple definitions of things lem expects
*)
open HolKernel Parse boolLib bossLib;
open intLib;

val _ = new_theory "lem_list";

Definition list_index_def:
  list_index xs n =
  if n < LENGTH xs
  then SOME (EL n xs)
  else NONE
End

Theorem list_index_cond_simps:
  (list_index (CONS x xs) n =
    (if n = 0 then SOME x else list_index xs (PRE n))) /\
  (list_index xs (SUC n) =
    (if NULL xs then NONE else list_index (TL xs) n))
Proof
  rw [list_index_def]
  \\ Cases_on `xs` \\ Cases_on `n` \\ fs []
QED

Theorem list_index_simps[simp]:
  (list_index (CONS x xs) 0 = SOME x) /\
  (list_index (CONS x xs) (SUC n) = list_index xs n) /\
  (list_index [] n = NONE)
Proof
  simp [list_index_cond_simps]
  \\ simp [list_index_def]
QED

val _ = export_theory ();
