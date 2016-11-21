open preamble wordLangTheory

val _ = new_theory "word_remove";

(*Removes MustTerminate*)

val remove_must_terminate_def = Define`
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
  (remove_must_terminate prog = prog)`

val _ = export_theory();
