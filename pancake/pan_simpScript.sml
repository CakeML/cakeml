(*
  Compilation from panLang to crepLang.
*)
open preamble panLangTheory

val _ = new_theory "pan_simp"

val _ = set_grammar_ancestry ["panLang","backend_common"];

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

Definition SmartSeq_def[simp]:
   SmartSeq p q =
    if p = Skip then q else Seq p q
End

Definition seq_assoc_def:
  (seq_assoc p Skip = p) /\
  (seq_assoc p (Dec v e q) =
    SmartSeq p (Dec v e (seq_assoc Skip q))) /\
  (seq_assoc p (Seq q r) = seq_assoc (seq_assoc p q) r) /\
  (seq_assoc p (If e q r) =
    SmartSeq p (If e (seq_assoc Skip q) (seq_assoc Skip r))) /\
  (seq_assoc p (While e q) =
    SmartSeq p (While e (seq_assoc Skip q))) /\
  (seq_assoc p (Call rtyp name args) =
    SmartSeq p (Call
                 (dtcase rtyp of
                   | Tail => Tail
                   | Ret v => Ret v
                   | Handle v v' s q => Handle v v' s (seq_assoc Skip q))
                name args)) /\
  (seq_assoc p others = SmartSeq p others)
End

Theorem seq_assoc_pmatch:
  !p prog.
  seq_assoc p prog =
  case prog of
  | Skip => p
  | (Dec v e q) => SmartSeq p (Dec v e (seq_assoc Skip q))
  | (Seq q r) => seq_assoc (seq_assoc p q) r
  | (If e q r) =>
     SmartSeq p (If e (seq_assoc Skip q) (seq_assoc Skip r))
  | (While e q) =>
     SmartSeq p (While e (seq_assoc Skip q))
  | (Call rtyp name args) =>
     SmartSeq p (Call
                 (dtcase rtyp of
                   | Tail => Tail
                   | Ret v => Ret v
                   | Handle v v' s q => Handle v v' s (seq_assoc Skip q))
                name args)
  | other => SmartSeq p other
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  every_case_tac >> fs[seq_assoc_def]
QED

Definition retcall_ret_to_tail_def:
  retcall_ret_to_tail prog =
   dtcase prog of
    | Seq (RetCall v trgt args) (Return (Var v')) =>
      if v = v' then TailCall trgt args else Seq (RetCall v trgt args) (Return (Var v'))
    | other => other
End

(*
Definition retcall_ret_to_tail_def:
  retcall_ret_to_tail prog =
   case prog of
    | Seq (RetCall v trgt args) (Return (Var v)) =>
      TailCall trgt args
    | other => other
End


Theorem retcall_ret_to_tail_pmatch:
  !prog.
  retcall_ret_to_tail prog =
  case prog of
  | Seq (RetCall v trgt args) (Return (Var v)) =>
      TailCall trgt args
  | other => other
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  every_case_tac >> fs[seq_assoc_def]
QED
*)

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


Theorem retcall_elim_pmatch:
  !p.
  retcall_elim p =
  case p of
  | Skip => Skip
  | (Dec v e q) => Dec v e (retcall_elim q)
  | (Seq q r) => retcall_ret_to_tail (Seq (retcall_elim q) (retcall_elim r))
  | (If e q r) =>
     If e (retcall_elim q) (retcall_elim r)
  | (While e q) =>
     While e (retcall_elim q)
  | (Call rtyp name args) =>
     Call
     (dtcase rtyp of
       | Tail => Tail
       | Ret v => Ret v
       | Handle v v' s q => Handle v v' s (retcall_elim q))
    name args
  | other => other
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  every_case_tac >> fs[retcall_elim_def]
QED


Definition compile_prog_def:
 compile_prog prog =
 let prog = seq_assoc Skip prog in
 let prog = retcall_elim prog in
     prog
End

val _ = export_theory();
