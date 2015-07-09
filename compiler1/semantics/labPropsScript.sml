open preamble labSemTheory;

val _ = new_theory"labProps";

val update_simps = store_thm("update_simps[simp]",
  ``((upd_pc x s).io_events = s.io_events) /\
    ((dec_clock s).io_events = s.io_events) /\
    ((upd_pc x s).pc = x) /\
    ((dec_clock s).pc = s.pc) /\
    ((upd_pc x s).clock = s.clock) /\
    ((dec_clock s).clock = s.clock - 1)``,
  EVAL_TAC);

val _ = export_theory();
