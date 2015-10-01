open preamble ffiTheory labSemTheory lab_to_targetTheory;

val _ = new_theory"labProps";

val update_simps = store_thm("update_simps[simp]",
  ``((upd_pc x s).ffi = s.ffi) /\
    ((dec_clock s).ffi = s.ffi) /\
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
  `!x2. ~is_Label x2 ==> (LENGTH (line_bytes x2) = line_length x2)`,
  Cases \\ fs [is_Label_def,line_bytes_def,line_length_def] \\ rw []);

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

val good_dimindex_def = Define `
  good_dimindex (:'a) <=> dimindex (:'a) = 32 \/ dimindex (:'a) = 64`;

val get_byte_set_byte = store_thm("get_byte_set_byte",
  ``good_dimindex (:'a) ==>
    (get_byte a (set_byte (a:'a word) b w be) be = b)``,
  fs [get_byte_def,set_byte_def,LET_DEF]
  \\ fs [fcpTheory.CART_EQ,w2w,good_dimindex_def] \\ rpt strip_tac
  \\ `i < dimindex (:'a)` by decide_tac
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def]
  \\ `i + byte_index a be < dimindex (:'a)` by
   (fs [byte_index_def,LET_DEF] \\ rw []
    \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ decide_tac)
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def,
         word_slice_alt_def,w2w] \\ rfs []
  \\ `~(i + byte_index a be < byte_index a be)` by decide_tac
  \\ `~(byte_index a be + 8 <= i + byte_index a be)` by decide_tac
  \\ fs [])

val byte_index_LESS_IMP = prove(
  ``(dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
    byte_index (a:'a word) be < byte_index (a':'a word) be /\ i < 8 ==>
    byte_index a be + i < byte_index a' be /\
    byte_index a be <= i + byte_index a' be /\
    byte_index a be + 8 <= i + byte_index a' be /\
    i + byte_index a' be < byte_index a be + dimindex (:α)``,
  fs [byte_index_def,LET_DEF] \\ Cases_on `be` \\ fs []
  \\ rpt strip_tac \\ rfs [] \\ fs []
  \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ decide_tac);

val NOT_w2w_bit = prove(
  ``8 <= i /\ i < dimindex (:'b) ==> ~((w2w:word8->'b word) w ' i)``,
  rpt strip_tac \\ rfs [w2w] \\ decide_tac);

val LESS4 = DECIDE ``n < 4 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``
val LESS8 = DECIDE ``n < 8 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num) \/
                               (n = 4) \/ (n = 5) \/ (n = 6) \/ (n = 7)``

val DIV_EQ_DIV_IMP = prove(
  ``0 < d /\ n <> n' /\ (n DIV d * d = n' DIV d * d) ==> n MOD d <> n' MOD d``,
  rpt strip_tac \\ Q.PAT_ASSUM `n <> n'` mp_tac \\ fs []
  \\ MP_TAC (Q.SPEC `d` DIVISION) \\ fs []
  \\ rpt strip_tac \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs []);

val get_byte_set_byte_diff = store_thm("get_byte_set_byte_diff",
  ``good_dimindex (:'a) /\ a <> a' /\ (byte_align a = byte_align a') ==>
    (get_byte a (set_byte (a':'a word) b w be) be = get_byte a w be)``,
  fs [get_byte_def,set_byte_def,LET_DEF] \\ rpt strip_tac
  \\ `byte_index a be <> byte_index a' be` by
   (fs [good_dimindex_def]
    THENL
     [`w2n a MOD 4 < 4 /\ w2n a' MOD 4 < 4` by fs []
      \\ `w2n a MOD 4 <> w2n a' MOD 4` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 4 * 4 + n MOD 4) < dimword (:'a) /\
            (n' DIV 4 * 4 + n' MOD 4) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<4:num``])
        \\ `(n DIV 4 * 4) < dimword (:'a) /\
            (n' DIV 4 * 4) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs []),
      `w2n a MOD 8 < 8 /\ w2n a' MOD 8 < 8` by fs []
      \\ `w2n a MOD 8 <> w2n a' MOD 8` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 8 * 8 + n MOD 8) < dimword (:'a) /\
            (n' DIV 8 * 8 + n' MOD 8) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<8:num``])
        \\ `(n DIV 8 * 8) < dimword (:'a) /\
            (n' DIV 8 * 8) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs [])]
    \\ full_simp_tac bool_ss [LESS4,LESS8] \\ fs [] \\ rfs []
    \\ fs [byte_index_def,LET_DEF] \\ rw [])
  \\ fs [fcpTheory.CART_EQ,w2w,good_dimindex_def] \\ rpt strip_tac
  \\ `i' < dimindex (:'a)` by decide_tac
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def]
  \\ `i' + byte_index a be < dimindex (:'a)` by
   (fs [byte_index_def,LET_DEF] \\ rw []
    \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ decide_tac)
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def,
         word_slice_alt_def,w2w] \\ rfs []
  \\ fs [DECIDE ``m <> n <=> m < n \/ n < m:num``]
  \\ Cases_on `w ' (i' + byte_index a be)` \\ fs []
  \\ imp_res_tac byte_index_LESS_IMP
  \\ fs [w2w] \\ TRY (match_mp_tac NOT_w2w_bit)
  \\ fs [] \\ decide_tac)

val evaluate_io_events_NONE_IMP = store_thm("evaluate_io_events_NONE_IMP",
  ``!k s io q r.
      s.io_events = SOME io /\ evaluate s = (q,r) /\ r.io_events = NONE ==>
      q = Error IO_mismatch``,
  cheat (* easy *));

val evaluate_ADD_clock = store_thm("evaluate_ADD_clock",
  ``!s res r k.
      evaluate s = (res,r) /\ res <> TimeOut ==>
      evaluate (s with clock := s.clock + k) = (res,r)``,
  cheat (* easy *));

val _ = export_theory();
