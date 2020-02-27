(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory

val _ = new_theory "pan_simp"

val _ = set_grammar_ancestry ["panLang","backend_common"];

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

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
                 (dtcase rtyp of
                   | Tail => Tail
                   | Ret v => Ret v
                   | Handle v v' s q => Handle v v' s (seq_assoc Skip q))
                name args)) /\
  (seq_assoc p others = skip_seq p others)
End

(* we need to have a recusive def *)

Definition retcall_ret_to_tail_def:
  retcall_ret_to_tail prog =
   case prog of
    | Seq (RetCall v trgt args) (Return (Var v)) =>
      TailCall trgt args
    | other => other
End

Definition retcall_elim_def:
  (retcall_elim Skip = Skip) /\
  (retcall_elim (Dec v e q) = Dec v e (retcall_elim q)) /\
  (retcall_elim (Seq p q) =  retcall_ret_to_tail (Seq (retcall_elim p) (retcall_elim q))) /\
  (retcall_elim (If e p q) = If e (retcall_elim p) (retcall_elim q)) /\
  (retcall_elim (While e p) = While e (retcall_elim p)) /\
  (retcall_elim (Call rtyp name args) =
    Call
     (dtcase rtyp of
       | Tail => Tail
       | Ret v => Ret v
       | Handle v v' s q => Handle v v' s (retcall_elim q))
    name args) /\
  (retcall_elim others = others)
End


Definition compile_prog_def:
 compile_prog prog =
 let prog = seq_assoc Skip prog in
 let prog = retcall_elim prog in
     prog
End

val _ = export_theory();
