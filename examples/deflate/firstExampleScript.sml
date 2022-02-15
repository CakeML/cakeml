(*
First simple compressor
*)

open preamble;
open stringLib stringTheory;
open rich_listTheory;

val _ = new_theory "compression";

Definition append_char_def:
  append_char s (c:char) = s ++ [c]
End

Definition remove_last_def:
  remove_last [] = [] ∧
  remove_last ((x::[]): char list)  = [] ∧
  remove_last ((x::xs ): char list) = [x] ++ remove_last xs
End


EVAL “remove_last (append_char "hello" #"s")”;
EVAL “remove_last "hello"”;
EVAL “append_char "hello" #"s"”;

Theorem append_char_length:
  ∀s c. STRLEN s + 1 = STRLEN (append_char s c )
Proof
  rpt strip_tac
  \\  rw[append_char_def]
QED

Theorem remove_last_length:
  ∀s. STRLEN s >= 1 ⇒ STRLEN s -1 = STRLEN (remove_last s) ∧ STRLEN s = 0 ⇒ STRLEN s = STRLEN (remove_last s)
Proof
  Induct_on ‘s’
  \\ rw[remove_last_def]
QED

Theorem correctness:
  ∀c s. FRONT ( SNOC c s) = s
Proof
  Induct_on ‘s’
  \\ rw[FRONT_SNOC]
  \\ Induct_on ‘s’
  \\ rw[FRONT_CONS]
QED


val _ = export_theory();
