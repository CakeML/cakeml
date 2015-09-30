open preamble
     systemSemTheory
     compilerTheory
     targetSemTheory

val _ = new_theory"compilerProof";

val compile_correct = Q.store_thm("compile_correct",
  `∀tokens.
    case parse tokens of
    | NONE => compile c tokens = Failure "parse error"
    | SOME prog =>
      (∀io_list. sem st prog (Terminate io_list) ⇒
         ∃bytes c'. compile c tokens = Success (bytes, c') ∧
                    F (* TODO *)) ∧
      (∀io_trace. sem st prog (Diverge io_trace) ⇒
         ∃bytes c'. compile c tokens = Success (bytes, c') ∧
                    F (* TODO *)) ∧
      (sem st prog Fail ⇒
        compile c tokens = Failure "type error")`,
  cheat);

val _ = export_theory();
