open preamble ffiTheory wordSemTheory labSemTheory lab_to_targetTheory;

val _ = new_theory"labProps";

(* TODO: move *)

val reg_imm_with_clock = Q.store_thm("reg_imm_with_clock[simp]",
  `reg_imm r (s with clock := z) = reg_imm r s`,
  Cases_on`r`>>EVAL_TAC);

val asm_inst_with_clock = Q.store_thm("asm_inst_with_clock[simp]",
  `asm_inst i (s with clock := z) = asm_inst i s with clock := z`,
  Cases_on`i`>>EVAL_TAC >- (
    Cases_on`a`>>EVAL_TAC >>
    every_case_tac >> fs[] >>
    Cases_on`b`>>EVAL_TAC>>
    fs[state_component_equality] >>
    Cases_on`r`>>fs[reg_imm_def]) >>
  Cases_on`m`>>EVAL_TAC>>
  Cases_on`a`>>EVAL_TAC>>
  every_case_tac >> fs[]);

val upd_pc_simps = Q.store_thm("upd_pc_simps[simp]",
  `((asmSem$upd_pc x s).align = s.align) ∧
   ((asmSem$upd_pc x s).mem_domain = s.mem_domain) ∧
   ((asmSem$upd_pc x s).failed = s.failed) ∧
   ((asmSem$upd_pc x s).be = s.be) ∧
   ((asmSem$upd_pc x s).mem = s.mem) ∧
   ((asmSem$upd_pc x s).regs = s.regs) ∧
   ((asmSem$upd_pc x s).lr = s.lr) ∧
   ((asmSem$upd_pc x s).pc = x)`,
  EVAL_TAC);

val read_reg_inc_pc = Q.store_thm("read_reg_inc_pc[simp]",
  `read_reg r (inc_pc s) = read_reg r s`,
  EVAL_TAC);

(* -- *)

val with_same_clock = Q.store_thm("with_same_clock[simp]",
  `(s with clock := s.clock) = s`,
  rw[state_component_equality]);

val inc_pc_dec_clock = Q.store_thm("inc_pc_dec_clock",
  `inc_pc (dec_clock x) = dec_clock (inc_pc x)`,
  EVAL_TAC);

val update_simps = store_thm("update_simps[simp]",
  ``((labSem$upd_pc x s).ffi = s.ffi) /\
    ((labSem$dec_clock s).ffi = s.ffi) /\
    ((labSem$upd_pc x s).pc = x) /\
    ((labSem$dec_clock s).pc = s.pc) /\
    ((labSem$upd_pc x s).clock = s.clock) /\
    ((labSem$upd_pc x s).ffi = s.ffi) /\
    ((labSem$dec_clock s).clock = s.clock - 1) /\
    ((labSem$dec_clock s).len_reg = s.len_reg) ∧
    ((labSem$dec_clock s).link_reg = s.link_reg) ∧
    ((labSem$dec_clock s).code = s.code) ∧
    ((labSem$dec_clock s).ptr_reg = s.ptr_reg) ∧
    ((labSem$dec_clock s).ffi = s.ffi) ∧
    ((labSem$upd_pc x s).len_reg = s.len_reg) ∧
    ((labSem$upd_pc x s).link_reg = s.link_reg) ∧
    ((labSem$upd_pc x s).code = s.code) ∧
    ((labSem$upd_pc x s).ptr_reg = s.ptr_reg) ∧
    ((labSem$upd_pc x s).mem_domain = s.mem_domain) ∧
    ((labSem$upd_pc x s).failed = s.failed) ∧
    ((labSem$upd_pc x s).be = s.be) ∧
    ((labSem$upd_pc x s).mem = s.mem) ∧
    ((labSem$upd_pc x s).regs = s.regs) ∧
    ((labSem$upd_pc x s).ffi = s.ffi) ∧
    ((labSem$inc_pc s).ptr_reg = s.ptr_reg) ∧
    ((labSem$inc_pc s).len_reg = s.len_reg) ∧
    ((labSem$inc_pc s).link_reg = s.link_reg) ∧
    ((labSem$inc_pc s).code = s.code) ∧
    ((labSem$inc_pc s).be = s.be) ∧
    ((labSem$inc_pc s).failed = s.failed) ∧
    ((labSem$inc_pc s).mem_domain = s.mem_domain) ∧
    ((labSem$inc_pc s).io_regs = s.io_regs) ∧
    ((labSem$inc_pc s).mem = s.mem) ∧
    ((labSem$inc_pc s).pc = s.pc + 1) ∧
    ((labSem$inc_pc s).ffi = s.ffi)``,
  EVAL_TAC);

val binop_upd_consts = Q.store_thm("binop_upd_consts[simp]",
  `(labSem$binop_upd a b c d x).mem_domain = x.mem_domain ∧
   (labSem$binop_upd a b c d x).ptr_reg = x.ptr_reg ∧
   (labSem$binop_upd a b c d x).len_reg = x.len_reg ∧
   (labSem$binop_upd a b c d x).link_reg = x.link_reg ∧
   (labSem$binop_upd a b c d x).code = x.code ∧
   (labSem$binop_upd a b c d x).be = x.be ∧
   (labSem$binop_upd a b c d x).mem = x.mem ∧
   (labSem$binop_upd a b c d x).io_regs = x.io_regs ∧
   (labSem$binop_upd a b c d x).pc = x.pc ∧
   (labSem$binop_upd a b c d x).ffi = x.ffi`,
  Cases_on`b`>>EVAL_TAC);

val arith_upd_consts = Q.store_thm("arith_upd_consts[simp]",
  `(labSem$arith_upd a x).mem_domain = x.mem_domain ∧
   (labSem$arith_upd a x).ptr_reg = x.ptr_reg ∧
   (labSem$arith_upd a x).len_reg = x.len_reg ∧
   (labSem$arith_upd a x).link_reg = x.link_reg ∧
   (labSem$arith_upd a x).code = x.code ∧
   (labSem$arith_upd a x).be = x.be ∧
   (labSem$arith_upd a x).mem = x.mem ∧
   (labSem$arith_upd a x).io_regs = x.io_regs ∧
   (labSem$arith_upd a x).pc = x.pc ∧
   (labSem$arith_upd a x).ffi = x.ffi`,
  Cases_on`a` >> EVAL_TAC >>
  every_case_tac >> EVAL_TAC >> rw[]);

val LENGTH_line_bytes = Q.store_thm("LENGTH_line_bytes[simp]",
  `!x2. ~is_Label x2 ==> (LENGTH (line_bytes x2) = line_length x2)`,
  Cases \\ fs [is_Label_def,line_bytes_def,line_length_def] \\ rw []);

val read_bytearray_LENGTH = store_thm("read_bytearray_LENGTH",
  ``!n a s x.
      (read_bytearray a n m dm be = SOME x) ==> (LENGTH x = n)``,
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac);

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

val evaluate_pres_final_event = store_thm("evaluate_pres_final_event",
  ``!s1.
      (evaluate s1 = (res,s2)) /\ s1.ffi.final_event ≠ NONE ==> s2.ffi = s1.ffi``,
  completeInduct_on `s1.clock`
  \\ rpt strip_tac \\ fs [PULL_FORALL] \\ rw []
  \\ ntac 2 (POP_ASSUM MP_TAC) \\ simp_tac std_ss [Once evaluate_def,LET_DEF]
  \\ Cases_on `s1.clock = 0` \\ fs []
  \\ `0 < s1.clock` by decide_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [LET_DEF] \\ rpt strip_tac
  \\ fs [AND_IMP_INTRO]
  \\ res_tac \\ fs [inc_pc_def,dec_clock_def,asm_inst_consts,upd_reg_def]
  \\ rfs [call_FFI_def] \\ fs[] \\ res_tac \\ fs []);

val evaluate_io_events_mono = Q.store_thm("evaluate_io_events_mono",
  `∀s1 r s2. evaluate s1 = (r,s2) ⇒ s1.ffi.io_events ≼ s2.ffi.io_events`,
  ho_match_mp_tac evaluate_ind >> rw[] >>
  Cases_on`s1.clock=0`>-fs[Once evaluate_def]>>fs[]>>
  rator_x_assum`evaluate`mp_tac >>
  simp[Once evaluate_def] >>
  Cases_on`asm_fetch s1`>>fs[] >>
  Cases_on`x`>>fs[] >- (
    every_case_tac >> rw[] >> fs[] >>
    fs[inc_pc_def,dec_clock_def,asm_inst_consts] ) >>
  Cases_on`a`>>fs[] >>
  every_case_tac >> rw[] >> fs[] >>
  fs[inc_pc_def,dec_clock_def,asm_inst_consts,upd_reg_def] >>
  split_pair_tac >> fs[] >>
  fs[call_FFI_def] >>
  every_case_tac >> fs[] >> rfs[] >>
  rpt var_eq_tac >> fs[] >>
  fs[IS_PREFIX_APPEND]);

val evaluate_ADD_clock = store_thm("evaluate_ADD_clock",
  ``!s res r k.
      evaluate s = (res,r) /\ res <> TimeOut ==>
      evaluate (s with clock := s.clock + k) = (res,r with clock := r.clock + k)``,
  ho_match_mp_tac evaluate_ind >> rw[] >>
  rator_x_assum`evaluate`mp_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> fs[] >> strip_tac >>
  simp[Once evaluate_def] >>
  fs[asm_fetch_def] >>
  Cases_on`asm_fetch_aux s.pc s.code`>>fs[] >>
  Cases_on`x`>>fs[] >>
  Cases_on`a`>>fs[] >>
  every_case_tac >> fs[] >>
  fs[inc_pc_def,dec_clock_def,asm_inst_consts,upd_pc_def,get_pc_value_def,get_ret_Loc_def,upd_reg_def] >>
  fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >> rfs[] >>
  TRY split_pair_tac >> fs[] >>
  first_x_assum(qspec_then`k`mp_tac)>>simp[]);

val evaluate_add_clock_io_events_mono = Q.store_thm("evaluate_add_clock_io_events_mono",
  `∀s.
   (SND(evaluate s)).ffi.io_events ≼
   (SND(evaluate (s with clock := s.clock + extra))).ffi.io_events ∧
   (IS_SOME((SND(evaluate s)).ffi.final_event) ⇒
    (SND(evaluate (s with clock := s.clock + extra))).ffi =
    (SND(evaluate s)).ffi)`,
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  CONV_TAC(DEPTH_CONV(REWR_CONV evaluate_def)) >>
  simp[] >>
  IF_CASES_TAC >> fs[] >- (
    IF_CASES_TAC >> fs[] >>
    simp[asm_fetch_def] >>
    Cases_on`asm_fetch_aux s.pc s.code`>>fs[] >>
    Cases_on`x`>>fs[] >>
    Cases_on`a`>>fs[] >>
    every_case_tac >> fs[] >>
    TRY
    (conj_tac >- (
       qmatch_abbrev_tac`s0.ffi.io_events ≼ (SND(evaluate s1)).ffi.io_events` >>
       Cases_on`evaluate s1` >>
       drule (GEN_ALL evaluate_io_events_mono) >>
       unabbrev_all_tac >> simp[] >> EVAL_TAC >>
       simp[asm_inst_consts] ) >>
     qmatch_abbrev_tac`IS_SOME s0.ffi.final_event ⇒ ((SND (evaluate s1)).ffi = _)` >>
     Cases_on`evaluate s1` >>
     drule(GEN_ALL evaluate_pres_final_event) >>
     unabbrev_all_tac >> simp[] >> EVAL_TAC >>
     simp[asm_inst_consts,IS_SOME_EXISTS] >> rw[] >>
     first_x_assum match_mp_tac >> simp[]) >>
    (fn g => (subterm split_applied_pair_tac (#2 g) g)) >>
    simp[] >>
    fs[call_FFI_def] >>
    qmatch_abbrev_tac`s0.ffi.io_events ≼ (SND(evaluate s1)).ffi.io_events ∧ _` >>
    Cases_on`evaluate s1` >>
    drule (GEN_ALL evaluate_io_events_mono) >>
    drule (GEN_ALL evaluate_pres_final_event) >>
    unabbrev_all_tac >> fs[] >>
    every_case_tac >> fs[] >> rw[] >>
    fs[IS_PREFIX_APPEND] ) >>
  fs[asm_fetch_def] >>
  Cases_on`asm_fetch_aux s.pc s.code`>>fs[] >>
  Cases_on`x`>>fs[] >>
  Cases_on`a`>>fs[] >>
  every_case_tac >> fs[] >>
  fs[inc_pc_def,dec_clock_def,asm_inst_consts,upd_pc_def,get_pc_value_def,get_ret_Loc_def,upd_reg_def] >>
  fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >> rfs[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  (fn g => (subterm split_applied_pair_tac (#2 g) g)) >>
  simp[] >> fs[call_FFI_def]);

val _ = export_theory();
