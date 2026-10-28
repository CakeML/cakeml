(*
  This simple compiler phase removes `MustTerminate`, which is a
  semantic-device used to help keep the logical clocks in sync in the
  data_to_word correctness proofs.
*)
Theory word_remove
Ancestors
  wordLang
Libs
  preamble

val _ = patternMatchesSyntax.temp_enable_pmatch();

(*Removes MustTerminate*)

Definition remove_must_terminate_def:
  (remove_must_terminate (Seq p0 p1) = Seq (remove_must_terminate p0) (remove_must_terminate p1)) ∧
  (remove_must_terminate (If cmp r1 ri e2 e3) =
    If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)) ∧
  (remove_must_terminate (MustTerminate p) = remove_must_terminate p) ∧
  (remove_must_terminate (Call ret dest args h) =
    let ret = case ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (v,cutset,remove_must_terminate ret_handler,l1,l2) in
    let h = case h of NONE => NONE
                    | SOME (v,prog,l1,l2) => SOME (v,remove_must_terminate prog,l1,l2) in
      Call ret dest args h) ∧
  (remove_must_terminate (Loop names body exit_names) =
    Loop names (remove_must_terminate body) exit_names) ∧
  (remove_must_terminate prog = prog)
End

Theorem remove_must_terminate_pmatch:
  !prog.
  remove_must_terminate prog =
  pmatch prog of
  | (Seq p0 p1) => Seq (remove_must_terminate p0) (remove_must_terminate p1)
  | (If cmp r1 ri e2 e3) =>
    If cmp r1 ri (remove_must_terminate e2) (remove_must_terminate e3)
  | (MustTerminate p) => remove_must_terminate p
  | (Call ret dest args h) =>
    (let ret = pmatch ret of NONE => NONE
                        | SOME (v,cutset,ret_handler,l1,l2) =>
                          SOME (v,cutset,remove_must_terminate ret_handler,l1,l2) in
    let h = pmatch h of NONE => NONE
                    | SOME (v,prog,l1,l2) => SOME (v,remove_must_terminate prog,l1,l2) in
      Call ret dest args h)
  | (Loop names body exit_names) =>
    Loop names (remove_must_terminate body) exit_names
  | prog => prog
Proof
  Cases_on `prog`
  >> simp[remove_must_terminate_def, patternMatchesTheory.PMATCH_EVAL,
          patternMatchesTheory.PMATCH_ROW_COND_def, pairTheory.FORALL_PROD,
          pairTheory.EXISTS_PROD, pairTheory.ELIM_UNCURRY]
  >> pure_rewrite_tac[GSYM pairTheory.PAIR_EQ, pairTheory.PAIR]
  >> simp[]
  >> conj_tac
  >- (namedCases_on `o'` ["", "ret"] >> simp[]
      >> PairCases_on `ret`
      >> simp[])
  >> namedCases_on `o0` ["", "handler"] >> simp[]
  >> PairCases_on `handler`
  >> simp[]
QED
