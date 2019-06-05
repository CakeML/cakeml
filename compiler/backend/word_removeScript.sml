(*
  This simple compiler phase removes `MustTerminate`, which is a
  semantic-device used to help keep the logical clocks in sync in the
  data_to_word correctness proofs.
*)
open preamble wordLangTheory

val _ = new_theory "word_remove";

val _ = patternMatchesLib.ENABLE_PMATCH_CASES();

(*Removes MustTerminate*)

val remove_must_terminate_def = Define`
  (remove_must_terminate (Seq p0 p1) = Seq (remove_must_terminate p0) (remove_must_terminate p1)) ∧
  (remove_must_terminate (If cmp r1 ri e2 e3) =
    If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)) ∧
  (remove_must_terminate (MustTerminate p) = remove_must_terminate p) ∧
  (remove_must_terminate (Call ret dest args h) =
    let ret = dtcase ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (v,cutset,remove_must_terminate ret_handler,l1,l2) in
    let h = dtcase h of NONE => NONE
                    | SOME (v,prog,l1,l2) => SOME (v,remove_must_terminate prog,l1,l2) in
      Call ret dest args h) ∧
  (remove_must_terminate prog = prog)`

Theorem remove_must_terminate_pmatch:
  !prog.
  remove_must_terminate prog =
  case prog of
  | (Seq p0 p1) => Seq (remove_must_terminate p0) (remove_must_terminate p1)
  | (If cmp r1 ri e2 e3) =>
    If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)
  | (MustTerminate p) => remove_must_terminate p
  | (Call ret dest args h) =>
    (let ret = case ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (v,cutset,remove_must_terminate ret_handler,l1,l2) in
    let h = case h of NONE => NONE
                    | SOME (v,prog,l1,l2) => SOME (v,remove_must_terminate prog,l1,l2) in
      Call ret dest args h)
  | prog => prog
Proof
  rpt(
    rpt strip_tac
    >> rpt(CONV_TAC(RAND_CONV patternMatchesLib.PMATCH_ELIM_CONV) >> every_case_tac >>
         PURE_ONCE_REWRITE_TAC[LET_DEF] >> BETA_TAC)
    >> fs[remove_must_terminate_def])
QED
val _ = export_theory();
