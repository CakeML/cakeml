open preamble labSemTheory lab_to_targetTheory;

val _ = new_theory"labProps";

val update_simps = store_thm("update_simps[simp]",
  ``((upd_pc x s).io_events = s.io_events) /\
    ((dec_clock s).io_events = s.io_events) /\
    ((upd_pc x s).pc = x) /\
    ((dec_clock s).pc = s.pc) /\
    ((upd_pc x s).clock = s.clock) /\
    ((dec_clock s).clock = s.clock - 1)``,
  EVAL_TAC);

val line_length_def = Define `
  (line_length (Label k1 k2 l) = if l = 0 then 0 else 1) /\
  (line_length (Asm b bytes l) = LENGTH bytes) /\
  (line_length (LabAsm a w bytes l) = LENGTH bytes)`

val LENGTH_line_bytes = Q.store_thm("LENGTH_line_bytes[simp]",
  `!x2. LENGTH (line_bytes x2 b) = line_length x2`,
  Cases \\ fs [line_bytes_def,line_length_def] \\ rw []);

val no_Label_def = Define `
  (no_Label (Section k (x::xs)::ys) = ~(is_Label x)) /\ (no_Label _ = F)`;
val _ = export_rewrites["no_Label_def"];

val no_Label_eq = store_thm("no_Label_eq",
  ``no_Label p = ?k x xs ys. (p = Section k (x::xs)::ys) /\ ~is_Label x``,
  Cases_on `p` \\ fs [] \\ Cases_on `h` \\ fs [] \\ Cases_on `l` \\ fs []);

val _ = export_theory();
