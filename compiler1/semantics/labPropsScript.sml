open preamble ffiTheory labSemTheory lab_to_targetTheory;

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

val evaluate_pres_io_events_NONE = store_thm("evaluate_pres_io_events_NONE",
  ``!s1.
      (evaluate s1 = (res,s2)) /\ (s1.io_events = NONE) ==> (s2.io_events = NONE)``,
  completeInduct_on `s1.clock`
  \\ rpt strip_tac \\ fs [PULL_FORALL] \\ rw []
  \\ ntac 2 (POP_ASSUM MP_TAC) \\ simp_tac std_ss [Once evaluate_def,LET_DEF]
  \\ Cases_on `s1.clock = 0` \\ fs []
  \\ `0 < s1.clock` by decide_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [LET_DEF] \\ rpt strip_tac
  \\ fs [AND_IMP_INTRO]
  \\ res_tac \\ fs [inc_pc_def,dec_clock_def,asm_inst_consts,upd_reg_def]
  \\ rfs [call_FFI_def] \\ res_tac \\ fs []);

val write_bytearray_simp_lemma = prove(
  ``!new_bytes c1 s1 x.
      (read_bytearray (c1:'a word) (LENGTH new_bytes) s1 = SOME x) ==>
      (write_bytearray c1 new_bytes s1 =
         s1 with mem := (write_bytearray c1 new_bytes s1).mem)``,
  Induct \\ fs [write_bytearray_def]
  THEN1 (fs [state_component_equality])
  \\ fs [read_bytearray_def]
  \\ REPEAT STRIP_TAC
  \\ every_case_tac
  \\ (fs [state_component_equality])
  \\ fs [mem_store_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [upd_mem_def] \\ rw[]);

val read_bytearray_LENGTH = store_thm("read_bytearray_LENGTH",
  ``!n a s x.
      (read_bytearray a n s = SOME x) ==> (LENGTH x = n)``,
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac);

val write_bytearray_simp = prove(
  ``(read_bytearray (c1:'a word) (w2n (c2:'a word)) s1 = SOME x) /\
    (call_FFI index x s1.io_events = (new_bytes,new_io)) ==>
    (write_bytearray c1 new_bytes s1 =
       s1 with mem := (write_bytearray c1 new_bytes s1).mem)``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL write_bytearray_simp_lemma)
  \\ imp_res_tac read_bytearray_LENGTH
  \\ fs [call_FFI_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac
  \\ fs [listTheory.LENGTH_MAP]) |> SPEC_ALL
  |> curry save_thm "write_bytearray_simp";

val write_bytearray_const = store_thm("write_bytearray_const[simp]",
  ``!xs c1 s1. (write_bytearray c1 xs s1).mem_domain = s1.mem_domain /\
               (write_bytearray c1 xs s1).be = s1.be``,
  Induct \\ fs [write_bytearray_def,mem_store_byte_aux_def]
  \\ rpt strip_tac \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [labSemTheory.upd_mem_def]);

val _ = export_theory();
