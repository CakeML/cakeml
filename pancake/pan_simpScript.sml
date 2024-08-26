(*
  Simplification of panLang.
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
  (seq_assoc p (Call NONE name args) =
    SmartSeq p (Call NONE name args)) /\
  (seq_assoc p (Call (SOME (rv , exp)) name args) =
    SmartSeq p (Call
                 (dtcase exp of
                   | NONE => SOME (rv , NONE)
                   | SOME (eid , ev , ep) =>
                      SOME (rv , (SOME (eid , ev , (seq_assoc Skip ep)))))
                 name args)) /\
  (seq_assoc p (DecCall v s e es q) =
    SmartSeq p (DecCall v s e es (seq_assoc Skip q))) /\
  (seq_assoc p (Annot _) = p) /\
  (seq_assoc p q = SmartSeq p q)
End

Definition seq_call_ret_def:
  seq_call_ret prog =
   dtcase prog of
    | Seq (AssignCall rv1 NONE trgt args) (Return (Var (rv2:mlstring))) =>
      if rv1 = rv2 then (TailCall trgt args) else prog
    | other => other
End

Definition ret_to_tail_def:
  (ret_to_tail Skip = Skip) /\
  (ret_to_tail (Dec v e q) = Dec v e (ret_to_tail q)) /\
  (ret_to_tail (Seq p q) =
    seq_call_ret (Seq (ret_to_tail p) (ret_to_tail q))) /\
  (ret_to_tail (If e p q) = If e (ret_to_tail p) (ret_to_tail q)) /\
  (ret_to_tail (While e p) = While e (ret_to_tail p)) /\
  (ret_to_tail (Call NONE name args) = Call NONE name args) /\
  (ret_to_tail (Call (SOME (rv , exp)) name args) =
   Call (SOME (rv, (dtcase exp of
                    | NONE => NONE
                    | SOME (eid , ev , ep) =>
                        SOME (eid, ev, (ret_to_tail ep)))))
        name args) /\
  (ret_to_tail (DecCall v s e es q) = DecCall v s e es (ret_to_tail q)) /\
  (ret_to_tail p = p)
End

Definition compile_def:
 compile p =
  let p = seq_assoc Skip p in
   ret_to_tail p
End

Definition compile_prog_def:
  compile_prog prog =
    MAP (λ(name, params, body).
          (name,
           params,
           compile body)) prog
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
                   | NONE => NONE
                   | SOME (rv , NONE) => SOME (rv,  NONE)
                   | SOME (rv , (SOME (eid , ev , ep))) =>
                       SOME (rv , (SOME (eid , ev , (seq_assoc Skip ep)))))
                  name args)
  | (DecCall v s e es q) => SmartSeq p (DecCall v s e es (seq_assoc Skip q))
  | (Annot _) => p
  | q => SmartSeq p q
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  every_case_tac >> fs[seq_assoc_def]
QED

Theorem ret_to_tail_pmatch:
  !p.
  ret_to_tail p =
  case p of
   | Skip => Skip
   | (Dec v e q) => Dec v e (ret_to_tail q)
   | (Seq q r) => seq_call_ret (Seq (ret_to_tail q) (ret_to_tail r))
   | (If e q r) =>
      If e (ret_to_tail q) (ret_to_tail r)
   | (While e q) =>
      While e (ret_to_tail q)
   | (Call rtyp name args) =>
      Call
      (dtcase rtyp of
                    | NONE => NONE
                    | SOME (rv , NONE) => SOME (rv , NONE)
                    | SOME (rv , (SOME (eid , ev , ep))) =>
                       SOME (rv , (SOME (eid , ev , (ret_to_tail ep)))))
      name args
   | (DecCall v s e es q) => DecCall v s e es (ret_to_tail q)
   | p => p
Proof
  rpt strip_tac >>
  CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >>
  every_case_tac >> fs[ret_to_tail_def]
QED

val _ = export_theory();
