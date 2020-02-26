(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory

val _ = new_theory "pan_simp"

val _ = set_grammar_ancestry ["panLang","backend_common"];

Definition skip_seq_def:
   skip_seq p q =
    if p = Skip then q else Seq p q
End

Definition seq_assoc_def:
  (seq_assoc p Skip = p) /\
  (seq_assoc p (Dec v e q) =
    skip_seq p (Dec v e (seq_assoc Skip q))) /\
  (seq_assoc p (Seq q r) = seq_assoc (seq_assoc p q) r) /\
  (seq_assoc p (If e q r) =
    skip_seq p (If e (seq_assoc Skip q) (seq_assoc Skip r))) /\
  (seq_assoc p (While e q) =
    skip_seq p (While e (seq_assoc Skip q))) /\
  (seq_assoc p (Call rtyp name args) =
    skip_seq p (Call
                 (case rtyp of
                   | Tail => Tail
                   | Ret v => Ret v
                   | Handle v v' s q => Handle v v' s (seq_assoc Skip q))
                name args)) /\
  (seq_assoc p others = skip_seq p others)
End

val _ = export_theory();
