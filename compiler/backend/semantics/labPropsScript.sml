(*
  Properties about labLang and its semantics
*)
open preamble ffiTheory wordSemTheory labSemTheory lab_to_targetTheory
     semanticsPropsTheory;

val _ = new_theory"labProps";

val _ = Parse.hide"mem";

Definition extract_labels_def:
  (extract_labels [] = []) ∧
  (extract_labels ((Label l1 l2 _)::xs) = (l1,l2):: extract_labels xs) ∧
  (extract_labels (x::xs) = extract_labels xs)
End
val _ = export_rewrites["extract_labels_def"];

val extract_labels_ind = theorem"extract_labels_ind";

Theorem extract_labels_append:
    ∀A B.
  extract_labels (A++B) = extract_labels A ++ extract_labels B
Proof
  Induct>>fs[extract_labels_def]>>Cases_on`h`>>rw[extract_labels_def]
QED

Definition labs_of_def:
  labs_of (LocValue _ (Lab n1 n2)) = {(n1,n2)} ∧
  labs_of (Jump (Lab n1 n2)) = {(n1,n2)} ∧
  labs_of (JumpCmp _ _ _ (Lab n1 n2)) = {(n1,n2)} ∧
  labs_of _ = {}
End
val _ = export_rewrites["labs_of_def"];

Definition line_get_labels_def:
  line_get_labels (LabAsm a _ _ _) = labs_of a ∧
  line_get_labels _ = {}
End

Definition sec_get_labels_def:
  sec_get_labels (Section _ lines) =
    BIGUNION (IMAGE line_get_labels (set lines))
End

Definition get_labels_def:
  get_labels code = BIGUNION (IMAGE sec_get_labels (set code))
End

Theorem get_labels_cons:
   get_labels (x::xs) = sec_get_labels x ∪ get_labels xs
Proof
  rw[get_labels_def]
QED

Definition line_get_code_labels_def:
  line_get_code_labels (Label _ l _) = {l} ∧
  line_get_code_labels _ = {}
End
val _ = export_rewrites["line_get_code_labels_def"];

Definition sec_get_code_labels_def:
  sec_get_code_labels (Section n1 lines) =
    (n1,0) INSERT
    IMAGE (λn2. (n1,n2)) (BIGUNION (IMAGE line_get_code_labels (set lines)))
End

Definition get_code_labels_def:
  get_code_labels code = BIGUNION (IMAGE sec_get_code_labels (set code))
End

Theorem get_code_labels_nil[simp]:
   get_code_labels [] = {}
Proof
EVAL_TAC \\ rw[]
QED

Theorem get_code_labels_cons:
   get_code_labels (s::secs) = sec_get_code_labels s ∪ get_code_labels secs
Proof
  rw[get_code_labels_def]
QED

Definition sec_ends_with_label_def:
  sec_ends_with_label (Section _ ls) ⇔
    ¬NULL ls ∧ is_Label (LAST ls)
End

Theorem reg_imm_with_clock[simp]:
   reg_imm r (s with clock := z) = reg_imm r s
Proof
  Cases_on`r`>>EVAL_TAC
QED

Theorem asm_inst_with_clock[simp]:
   asm_inst i (s with clock := z) = asm_inst i s with clock := z
Proof
  Cases_on`i`>>EVAL_TAC
  >-
    (Cases_on`a`>>EVAL_TAC >>
    every_case_tac >> fs[] >>
    Cases_on`b`>>EVAL_TAC>>
    fs[state_component_equality] >>
    Cases_on`r`>>fs[reg_imm_def])
  >-
    (Cases_on`m`>>EVAL_TAC>>
    Cases_on`a`>>EVAL_TAC>>
    every_case_tac >> fs[])
  >>
    Cases_on`f`>>EVAL_TAC>>
    every_case_tac>>fs[]>>
    EVAL_TAC>>fs[]
QED

Theorem read_reg_inc_pc[simp]:
   read_reg r (inc_pc s) = read_reg r s
Proof
  EVAL_TAC
QED

Theorem with_same_clock[simp]:
   (s with clock := s.clock) = s
Proof
  rw[state_component_equality]
QED

Theorem inc_pc_dec_clock:
   inc_pc (dec_clock x) = dec_clock (inc_pc x)
Proof
  EVAL_TAC
QED

Theorem update_simps[simp]:
   ((labSem$upd_pc x s).ffi = s.ffi) /\
    ((labSem$dec_clock s).ffi = s.ffi) /\
    ((labSem$upd_pc x s).pc = x) /\
    ((labSem$dec_clock s).pc = s.pc) /\
    ((labSem$upd_pc x s).clock = s.clock) /\
    ((labSem$upd_pc x s).ffi = s.ffi) /\
    ((labSem$dec_clock s).clock = s.clock - 1) /\
    ((labSem$dec_clock s).len_reg = s.len_reg) ∧
    ((labSem$dec_clock s).len2_reg = s.len2_reg) ∧
    ((labSem$dec_clock s).link_reg = s.link_reg) ∧
    ((labSem$dec_clock s).code = s.code) ∧
    ((labSem$dec_clock s).ptr_reg = s.ptr_reg) ∧
    ((labSem$dec_clock s).ptr2_reg = s.ptr2_reg) ∧
    ((labSem$dec_clock s).ffi = s.ffi) ∧
    ((labSem$upd_pc x s).len_reg = s.len_reg) ∧
    ((labSem$upd_pc x s).len2_reg = s.len2_reg) ∧
    ((labSem$upd_pc x s).link_reg = s.link_reg) ∧
    ((labSem$upd_pc x s).code = s.code) ∧
    ((labSem$upd_pc x s).ptr_reg = s.ptr_reg) ∧
    ((labSem$upd_pc x s).ptr2_reg = s.ptr2_reg) ∧
    ((labSem$upd_pc x s).mem_domain = s.mem_domain) ∧
    ((labSem$upd_pc x s).shared_mem_domain = s.shared_mem_domain) ∧
    ((labSem$upd_pc x s).failed = s.failed) ∧
    ((labSem$upd_pc x s).be = s.be) ∧
    ((labSem$upd_pc x s).mem = s.mem) ∧
    ((labSem$upd_pc x s).regs = s.regs) ∧
    ((labSem$upd_pc x s).fp_regs = s.fp_regs) ∧
    ((labSem$upd_pc x s).ffi = s.ffi) ∧
    ((labSem$inc_pc s).ptr_reg = s.ptr_reg) ∧
    ((labSem$inc_pc s).ptr2_reg = s.ptr2_reg) ∧
    ((labSem$inc_pc s).len_reg = s.len_reg) ∧
    ((labSem$inc_pc s).len2_reg = s.len2_reg) ∧
    ((labSem$inc_pc s).link_reg = s.link_reg) ∧
    ((labSem$inc_pc s).code = s.code) ∧
    ((labSem$inc_pc s).be = s.be) ∧
    ((labSem$inc_pc s).failed = s.failed) ∧
    ((labSem$inc_pc s).mem_domain = s.mem_domain) ∧
    ((labSem$inc_pc s).shared_mem_domain = s.shared_mem_domain) ∧
    ((labSem$inc_pc s).io_regs = s.io_regs) ∧
    ((labSem$inc_pc s).cc_regs = s.cc_regs) ∧
    ((labSem$inc_pc s).compile = s.compile) ∧
    ((labSem$inc_pc s).compile_oracle = s.compile_oracle) ∧
    ((labSem$inc_pc s).code_buffer = s.code_buffer) ∧
    ((labSem$inc_pc s).mem = s.mem) ∧
    ((labSem$inc_pc s).regs = s.regs) ∧
    ((labSem$inc_pc s).fp_regs = s.fp_regs) ∧
    ((labSem$inc_pc s).pc = s.pc + 1) ∧
    ((labSem$inc_pc s).ffi = s.ffi)
Proof
  EVAL_TAC
QED

Theorem binop_upd_consts[simp]:
   (labSem$binop_upd a b c d x).mem_domain = x.mem_domain ∧
   (labSem$binop_upd a b c d x).shared_mem_domain = x.shared_mem_domain ∧
   (labSem$binop_upd a b c d x).ptr_reg = x.ptr_reg ∧
   (labSem$binop_upd a b c d x).ptr2_reg = x.ptr2_reg ∧
   (labSem$binop_upd a b c d x).len_reg = x.len_reg ∧
   (labSem$binop_upd a b c d x).len2_reg = x.len2_reg ∧
   (labSem$binop_upd a b c d x).link_reg = x.link_reg ∧
   (labSem$binop_upd a b c d x).code = x.code ∧
   (labSem$binop_upd a b c d x).be = x.be ∧
   (labSem$binop_upd a b c d x).mem = x.mem ∧
   (labSem$binop_upd a b c d x).io_regs = x.io_regs ∧
   (labSem$binop_upd a b c d x).cc_regs = x.cc_regs ∧
   (labSem$binop_upd a b c d x).compile = x.compile ∧
   (labSem$binop_upd a b c d x).compile_oracle = x.compile_oracle ∧
   (labSem$binop_upd a b c d x).code_buffer = x.code_buffer ∧
   (labSem$binop_upd a b c d x).pc = x.pc ∧
   (labSem$binop_upd a b c d x).ffi = x.ffi
Proof
  Cases_on`b`>>EVAL_TAC
QED

Theorem arith_upd_consts[simp]:
   (labSem$arith_upd a x).mem_domain = x.mem_domain ∧
   (labSem$arith_upd a x).shared_mem_domain = x.shared_mem_domain ∧
   (labSem$arith_upd a x).ptr_reg = x.ptr_reg ∧
   (labSem$arith_upd a x).ptr2_reg = x.ptr2_reg ∧
   (labSem$arith_upd a x).len_reg = x.len_reg ∧
   (labSem$arith_upd a x).len2_reg = x.len2_reg ∧
   (labSem$arith_upd a x).link_reg = x.link_reg ∧
   (labSem$arith_upd a x).code = x.code ∧
   (labSem$arith_upd a x).be = x.be ∧
   (labSem$arith_upd a x).mem = x.mem ∧
   (labSem$arith_upd a x).io_regs = x.io_regs ∧
   (labSem$arith_upd a x).cc_regs = x.cc_regs ∧
   (labSem$arith_upd a x).compile = x.compile ∧
   (labSem$arith_upd a x).compile_oracle = x.compile_oracle ∧
   (labSem$arith_upd a x).code_buffer = x.code_buffer ∧
   (labSem$arith_upd a x).pc = x.pc ∧
   (labSem$arith_upd a x).ffi = x.ffi
Proof
  Cases_on`a` >> EVAL_TAC >>
  every_case_tac >> EVAL_TAC >> rw[]
QED

Theorem fp_upd_consts[simp]:
   (labSem$fp_upd f x).mem_domain = x.mem_domain ∧
   (labSem$fp_upd f x).shared_mem_domain = x.shared_mem_domain ∧
   (labSem$fp_upd f x).ptr_reg = x.ptr_reg ∧
   (labSem$fp_upd f x).len_reg = x.len_reg ∧
   (labSem$fp_upd f x).ptr2_reg = x.ptr2_reg ∧
   (labSem$fp_upd f x).len2_reg = x.len2_reg ∧
   (labSem$fp_upd f x).link_reg = x.link_reg ∧
   (labSem$fp_upd f x).code = x.code ∧
   (labSem$fp_upd f x).cc_regs = x.cc_regs ∧
   (labSem$fp_upd f x).code_buffer = x.code_buffer ∧
   (labSem$fp_upd f x).compile = x.compile ∧
   (labSem$fp_upd f x).compile_oracle = x.compile_oracle ∧
   (labSem$fp_upd f x).be = x.be ∧
   (labSem$fp_upd f x).mem = x.mem ∧
   (labSem$fp_upd f x).io_regs = x.io_regs ∧
   (labSem$fp_upd f x).pc = x.pc ∧
   (labSem$fp_upd f x).ffi = x.ffi
Proof
  Cases_on`f` >> EVAL_TAC >>
  every_case_tac >> EVAL_TAC >> rw[]
QED

Definition line_length_def:
  (line_length (Label k1 k2 l) = if l = 0 then 0 else 1) /\
  (line_length (Asm b bytes l) = LENGTH bytes) /\
  (line_length (LabAsm a w bytes l) = LENGTH bytes)
End

Theorem LENGTH_line_bytes[simp]:
   !x2. ~is_Label x2 ==> (LENGTH (line_bytes x2) = line_length x2)
Proof
  Cases \\ fs [is_Label_def,line_bytes_def,line_length_def] \\ rw []
QED

fun get_thms ty = { case_def = TypeBase.case_def_of ty, nchotomy = TypeBase.nchotomy_of ty }
Theorem case_eq_thms =
  (pair_case_eq::
   bool_case_eq::
   map (prove_case_eq_thm o get_thms)
       [``:'a line``,``:'a option``,``:'a asm_with_lab``,``:'a asm_or_cbw``,
        ``:'a asm``, ``:'a word_loc``,``:'a list``,``:'a sec``,``:'a ffi_result``])
  |> LIST_CONJ

Theorem evaluate_io_events_mono:
   ∀s1 r s2. evaluate s1 = (r,s2) ⇒ s1.ffi.io_events ≼ s2.ffi.io_events
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >>
  Cases_on`s1.clock=0`>-fs[Once evaluate_def]>>fs[]>>
  qhdtm_x_assum`evaluate`mp_tac >>
  simp[Once evaluate_def] >>
  Cases_on`asm_fetch s1`>>fs[] >>
  Cases_on`x`>>fs[] >- (
    every_case_tac >> rw[] >> fs[] >>
    fs[inc_pc_def,dec_clock_def,asm_inst_consts] >>
    Cases_on `m` >>
    fs[share_mem_op_def,share_mem_load_def,share_mem_store_def,AllCaseEqs()] >>
    qpat_x_assum `call_FFI _ _ _ _ = _` mp_tac >>
    gvs[inc_pc_def,dec_clock_def,call_FFI_def] >>
    TOP_CASE_TAC >>
    TOP_CASE_TAC >>
    rw[] >>
    fs[IS_PREFIX_APPEND]
  ) >>
  Cases_on`a`>>fs[case_eq_thms] >> rw[] >> fs[] >>
  fs[inc_pc_def,dec_clock_def,asm_inst_consts,upd_reg_def] >>
  TRY(qpat_x_assum`(_,_) = _`(assume_tac o SYM)) \\ fs[] \\
  fs[call_FFI_def] >>
  every_case_tac >> fs[] >> rfs[] >>
  rpt var_eq_tac >> fs[] >>
  fs[IS_PREFIX_APPEND]
  \\ Cases_on `s1.compile_oracle 0` \\ fs []
  \\ fs[case_eq_thms] \\ rveq \\ fs []
  \\ first_x_assum match_mp_tac
  \\ qpat_x_assum `(_,_) = _` (assume_tac o GSYM) \\ fs []
QED

Theorem evaluate_ADD_clock:
   !s res r k.
      evaluate s = (res,r) /\ res <> TimeOut ==>
      evaluate (s with clock := s.clock + k) = (res,r with clock := r.clock + k)
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >>
  qhdtm_x_assum`evaluate`mp_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> gvs[] >> strip_tac >>
  fs[asm_fetch_def,case_eq_thms] >> rw[] >>
  fsrw_tac[ARITH_ss][] >> rw[] >> gvs[] >>
  simp[Once evaluate_def] >>
  gvs[asm_fetch_def] >>
  gvs[inc_pc_def,dec_clock_def,asm_inst_consts,upd_pc_def,get_pc_value_def,get_ret_Loc_def,upd_reg_def]
  >~ [`s.compile_oracle`]
  >-(pairarg_tac >> fs[case_eq_thms] >> rw[]) >>
  qpat_x_assum `share_mem_op _ _ _ _ = _` mp_tac >>
  Cases_on `m` >>
  Cases_on `ad` >>
  fs[share_mem_op_def,share_mem_load_def,share_mem_store_def,addr_def] >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  rw[] >> gvs[inc_pc_def,dec_clock_def]
QED

Theorem addr_add_clock_eq:
  addr a (s with clock := extra + s.clock) = addr a s
Proof
  Cases_on `a` >> simp[addr_def]
QED

Theorem share_mem_op_add_clock_same:
   (s.clock <> 0 /\ share_mem_op m n a s = NONE ==>
    share_mem_op m n a (s with clock := extra + s.clock) = NONE) /\
   (s.clock <> 0 /\ share_mem_op m n a s = SOME (FFI_return f l', r) ==>
    share_mem_op m n a (s with clock := extra + s.clock) =
      SOME (FFI_return f l', r with clock := extra + r.clock)) /\
   (s.clock <> 0 /\ share_mem_op m n a s = SOME (FFI_final f2, r2) ==>
    share_mem_op m n a (s with clock := extra + s.clock) =
      SOME (FFI_final f2, (r2 with clock := extra + r2.clock)))
Proof
  Cases_on `m` >>
  rw[share_mem_op_def,share_mem_load_def,share_mem_store_def] >>
  rpt (TOP_CASE_TAC >> fs[addr_add_clock_eq]) >>
  gvs[state_component_equality,dec_clock_def,inc_pc_def]
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀s.
   (SND(evaluate s)).ffi.io_events ≼
   (SND(evaluate (s with clock := s.clock + extra))).ffi.io_events
Proof
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
    TRY(pairarg_tac >> fs[]) >>
    every_case_tac >> fs[] >>
    TRY
      (qmatch_abbrev_tac`s0.ffi.io_events ≼ (SND(evaluate s1)).ffi.io_events` >>
       Cases_on`evaluate s1` >>
       drule (GEN_ALL evaluate_io_events_mono) >>
       unabbrev_all_tac >> simp[] >> EVAL_TAC >>
       simp[asm_inst_consts] >> NO_TAC) >>
    simp[] >>
    fs[call_FFI_def]
    >~ [`read_bytearray`] >- (
    qmatch_abbrev_tac`s0.ffi.io_events ≼ (SND(evaluate s1)).ffi.io_events` >>
    Cases_on`evaluate s1` >>
    drule (GEN_ALL evaluate_io_events_mono) >>
    unabbrev_all_tac >> fs[] >>
    every_case_tac >> fs[] >> rw[] >>
    fs[IS_PREFIX_APPEND,IS_SOME_EXISTS] )
    >- (
      Cases_on `m` >>
      fs[share_mem_op_def,share_mem_load_def,share_mem_store_def,AllCaseEqs()] >>
      qpat_x_assum `call_FFI _ _ _ _ = _` mp_tac >>
      gvs[inc_pc_def,dec_clock_def,call_FFI_def] >>
      TOP_CASE_TAC >>
      TOP_CASE_TAC >>
      rw[] >>
      qmatch_abbrev_tac `s0.ffi.io_events ≼ (SND(evaluate s1)).ffi.io_events` >>
      Cases_on `evaluate s1` >>
      drule evaluate_io_events_mono >>
      unabbrev_all_tac >> fs[] >>
      rw[] >>
      fs[IS_PREFIX_APPEND,IS_SOME_EXISTS]
    )
    >- (
      Cases_on `m` >>
      fs[share_mem_op_def,share_mem_load_def,share_mem_store_def,AllCaseEqs()] >>
      qpat_x_assum `call_FFI _ _ _ _ = _` mp_tac >>
      gvs[inc_pc_def,dec_clock_def,call_FFI_def] >>
      rpt TOP_CASE_TAC >>
      rw[] >>
      fs[IS_PREFIX_APPEND]
    )
  ) >>
  fs[asm_fetch_def] >>
  Cases_on`asm_fetch_aux s.pc s.code`>>fs[] >>
  Cases_on`x`>>fs[] >>
  Cases_on`a`>>fs[] >>
  TRY(pairarg_tac >> fs[]) >>
  every_case_tac >> fs[] >>
  fs[inc_pc_def,dec_clock_def,asm_inst_consts,upd_pc_def,get_pc_value_def,get_ret_Loc_def,upd_reg_def] >>
  fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >> rfs[] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
  rpt (
    drule_all $ cj 1 share_mem_op_add_clock_same >>
    disch_then $ qspecl_then [`extra`] assume_tac >>
    gvs[]
  ) >>
  rpt (
    drule_all $ cj 2 share_mem_op_add_clock_same >>
    disch_then $ qspecl_then [`extra`] assume_tac >>
    gvs[]
  ) >>
  rpt (
    drule_all $ cj 3 share_mem_op_add_clock_same >>
    disch_then $ qspecl_then [`extra`] assume_tac >>
    gvs[]
  )
QED

Definition align_dm_def:
  align_dm (s:('a,'c,'ffi) labSem$state) =
    (s with mem_domain := s.mem_domain INTER byte_aligned)
End

Theorem align_dm_const[simp]:
   (align_dm s).clock = s.clock ∧
   (align_dm s).pc = s.pc ∧
   (align_dm s).code = s.code ∧
   (align_dm s).mem = s.mem ∧
   (align_dm s).shared_mem_domain = s.shared_mem_domain ∧
   (align_dm s).be = s.be ∧
   (align_dm s).len_reg = s.len_reg ∧
   (align_dm s).link_reg = s.link_reg ∧
   (align_dm s).ptr_reg = s.ptr_reg ∧
   (align_dm s).ptr2_reg = s.ptr2_reg ∧
   (align_dm s).len2_reg = s.len2_reg ∧
   (align_dm s).io_regs = s.io_regs ∧
   (align_dm s).code_buffer = s.code_buffer ∧
   (align_dm s).compile = s.compile ∧
   (align_dm s).compile_oracle = s.compile_oracle ∧
   (align_dm s).ffi = s.ffi ∧
   (align_dm s).failed = s.failed
Proof
  EVAL_TAC
QED

Theorem align_dm_with_clock:
   align_dm (s with clock := k) = align_dm s with clock := k
Proof
  EVAL_TAC
QED

Theorem asm_fetch_align_dm[simp]:
   asm_fetch (align_dm s) = asm_fetch s
Proof
  rw[asm_fetch_def]
QED

Theorem read_reg_align_dm[simp]:
   read_reg n (align_dm s) = read_reg n s
Proof
  EVAL_TAC
QED

Theorem upd_reg_align_dm[simp]:
   upd_reg x y (align_dm s) = align_dm (upd_reg x y s)
Proof
  EVAL_TAC
QED

Theorem upd_mem_align_dm[simp]:
   upd_mem x y (align_dm s) = align_dm (upd_mem x y s)
Proof
  EVAL_TAC
QED

Theorem binop_upd_align_dm[simp]:
   binop_upd x y z w (align_dm s) = align_dm (binop_upd x y z w s)
Proof
  Cases_on`y` \\ simp[binop_upd_def]
QED

Theorem reg_imm_align_dm[simp]:
   reg_imm r (align_dm s) = reg_imm r s
Proof
  Cases_on`r` \\ EVAL_TAC
QED

Theorem assert_align_dm[simp]:
   assert b (align_dm s) = align_dm (assert b s)
Proof
  EVAL_TAC
QED

Theorem arith_upd_align_dm[simp]:
   arith_upd x (align_dm s) = align_dm (arith_upd x s)
Proof
  Cases_on`x` \\ rw[arith_upd_def]
  \\ every_case_tac \\ fs[]
QED

Theorem fp_upd_align_dm[simp]:
   fp_upd f (align_dm s) = align_dm (fp_upd f s)
Proof
  Cases_on`f` \\ EVAL_TAC
  \\ every_case_tac \\ fs[] \\ EVAL_TAC \\fs[]
QED

Theorem addr_align_dm[simp]:
   addr a (align_dm s) = addr a s
Proof
  Cases_on`a` \\ EVAL_TAC
QED

Theorem mem_load_align_dm:
   good_dimindex (:α) ⇒
   mem_load n (a:α addr) (align_dm s) = align_dm (mem_load n a s)
Proof
  strip_tac
  \\ simp[mem_load_def]
  \\ every_case_tac \\ fs[]
  \\ AP_TERM_TAC
  \\ EVAL_TAC
  \\ simp[state_component_equality]
  \\ rw[EQ_IMP_THM] \\ rw[]
  \\ fs[alignmentTheory.byte_aligned_def,IN_DEF]
  \\ fs[good_dimindex_def]
  \\ fs[alignmentTheory.aligned_def]
  \\ Cases_on`x` \\ rfs[alignmentTheory.align_w2n]
  \\ rfs[]
  \\ rfs[dimword_def]
  \\ spose_not_then strip_assume_tac
  \\ fs[DIV_MOD_MOD_DIV]
  \\ qpat_x_assum`_ ≠ _`mp_tac \\ simp[]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  >- (
    CONV_TAC(RAND_CONV(REWR_CONV(Q.SPECL[`4`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[])))
    \\ first_assum (CHANGED_TAC o SUBST1_TAC)
    \\ CONV_TAC(RAND_CONV(SIMP_CONV(srw_ss())[]))
    \\ match_mp_tac LESS_MOD
    \\ metis_tac[Q.SPECL[`4`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[],ADD_0])
  >- (
    CONV_TAC(RAND_CONV(REWR_CONV(Q.SPECL[`8`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[])))
    \\ first_assum (CHANGED_TAC o SUBST1_TAC)
    \\ CONV_TAC(RAND_CONV(SIMP_CONV(srw_ss())[]))
    \\ match_mp_tac LESS_MOD
    \\ metis_tac[Q.SPECL[`8`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[],ADD_0])
QED

Theorem mem_load_byte_aux_align_dm:
   mem_load_byte_aux s.mem s.mem_domain be x = SOME y ⇒
   mem_load_byte_aux s.mem (align_dm s).mem_domain be x = SOME y
Proof
  rw[mem_load_byte_aux_def]
  \\ every_case_tac \\ fs[]
  \\ fs[align_dm_def]
  \\ last_x_assum mp_tac \\ simp[]
  \\ fs[IN_DEF,alignmentTheory.byte_aligned_def,alignmentTheory.byte_align_def]
  \\ fs[alignmentTheory.aligned_align]
QED

Theorem mem_load_byte_align_dm:
   good_dimindex (:α) ⇒
   mem_load_byte n (a:α addr) (align_dm s) = align_dm (mem_load_byte n a s)
Proof
  strip_tac
  \\ simp[mem_load_byte_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac mem_load_byte_aux_align_dm
  \\ fs[]
  \\ fs[mem_load_byte_aux_def]
  \\ fs[align_dm_def]
  \\ every_case_tac \\ fs[]
QED

Theorem mem_store_align_dm:
   good_dimindex (:α) ⇒
   mem_store n (a:α addr) (align_dm s) = align_dm (mem_store n a s)
Proof
  strip_tac
  \\ simp[mem_store_def]
  \\ every_case_tac \\ fs[]
  \\ AP_TERM_TAC
  \\ EVAL_TAC
  \\ simp[state_component_equality]
  \\ rw[EQ_IMP_THM] \\ rw[]
  \\ fs[alignmentTheory.byte_aligned_def,IN_DEF]
  \\ fs[good_dimindex_def]
  \\ fs[alignmentTheory.aligned_def]
  \\ Cases_on`x` \\ rfs[alignmentTheory.align_w2n]
  \\ rfs[]
  \\ rfs[dimword_def]
  \\ spose_not_then strip_assume_tac
  \\ fs[DIV_MOD_MOD_DIV]
  \\ qpat_x_assum`_ ≠ _`mp_tac \\ simp[]
  \\ ONCE_REWRITE_TAC[MULT_COMM]
  >- (
    CONV_TAC(RAND_CONV(REWR_CONV(Q.SPECL[`4`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[])))
    \\ first_assum (CHANGED_TAC o SUBST1_TAC)
    \\ CONV_TAC(RAND_CONV(SIMP_CONV(srw_ss())[]))
    \\ match_mp_tac LESS_MOD
    \\ metis_tac[Q.SPECL[`4`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[],ADD_0])
  >- (
    CONV_TAC(RAND_CONV(REWR_CONV(Q.SPECL[`8`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[])))
    \\ first_assum (CHANGED_TAC o SUBST1_TAC)
    \\ CONV_TAC(RAND_CONV(SIMP_CONV(srw_ss())[]))
    \\ match_mp_tac LESS_MOD
    \\ metis_tac[Q.SPECL[`8`,`n`](MP_CANON DIVISION) |> SIMP_RULE(srw_ss())[],ADD_0])
QED

Theorem mem_store_byte_aux_align_dm:
   mem_store_byte_aux mem s.mem_domain be x c = SOME y ⇒
   mem_store_byte_aux mem (align_dm s).mem_domain be x c = SOME y
Proof
  rw[mem_store_byte_aux_def]
  \\ every_case_tac \\ fs[]
  \\ fs[align_dm_def]
  \\ last_x_assum mp_tac \\ simp[]
  \\ fs[IN_DEF,alignmentTheory.byte_aligned_def,alignmentTheory.byte_align_def]
  \\ fs[alignmentTheory.aligned_align]
QED

Theorem mem_store_byte_align_dm:
   good_dimindex (:α) ⇒
   mem_store_byte n (a:α addr) (align_dm s) = align_dm (mem_store_byte n a s)
Proof
  strip_tac
  \\ simp[mem_store_byte_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac mem_store_byte_aux_align_dm
  \\ fs[]
  \\ fs[mem_store_byte_aux_def]
  \\ fs[align_dm_def]
  \\ every_case_tac \\ fs[]
QED

Theorem mem_op_align_dm:
   good_dimindex (:α) ⇒
   mem_op m n (a:α addr) (align_dm s) = align_dm (mem_op m n a s)
Proof
  Cases_on`m`
  \\ simp[mem_op_def,
          mem_load_align_dm,mem_load_byte_align_dm,
          mem_store_align_dm,mem_store_byte_align_dm]
QED

Theorem asm_inst_align_dm:
   good_dimindex (:α) ⇒
   asm_inst (i:α inst) (align_dm s) = align_dm (asm_inst i s)
Proof
  Cases_on`i` \\ simp[asm_inst_def,mem_op_align_dm]
QED

Theorem dec_clock_align_dm[simp]:
   dec_clock (align_dm s) = align_dm (dec_clock s)
Proof
  EVAL_TAC
QED

Theorem inc_pc_align_dm[simp]:
   inc_pc (align_dm s) = align_dm (inc_pc s)
Proof
  EVAL_TAC
QED

Theorem upd_pc_align_dm[simp]:
   upd_pc p (align_dm s) = align_dm (upd_pc p s)
Proof
  EVAL_TAC
QED

Theorem get_pc_value_align_dm[simp]:
   get_pc_value x (align_dm s) = get_pc_value x s
Proof
  EVAL_TAC \\ every_case_tac
QED

Theorem get_ret_Loc_align_dm[simp]:
   get_ret_Loc (align_dm s) = get_ret_Loc s
Proof
  EVAL_TAC
QED

Theorem read_bytearray_mem_load_byte_aux_align_dm[simp]:
   ∀y x.
    read_bytearray x y (mem_load_byte_aux s.mem (align_dm s).mem_domain s.be) =
   read_bytearray x y (mem_load_byte_aux s.mem s.mem_domain s.be)
Proof
  Induct \\ rw[read_bytearray_def]
  \\ match_mp_tac EQ_SYM
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    fs[mem_load_byte_aux_def]
    \\ Cases_on`s.mem (byte_align x)` \\ fs[]
    \\ simp[align_dm_def] )
  \\ imp_res_tac mem_load_byte_aux_align_dm
  \\ simp[]
QED

Theorem write_bytearray_align_dm[simp]:
   ∀y x. write_bytearray x y s.mem (align_dm s).mem_domain s.be =
   write_bytearray x y s.mem s.mem_domain s.be
Proof
  Induct \\ rw[write_bytearray_def]
  \\ match_mp_tac EQ_SYM
  \\ BasicProvers.TOP_CASE_TAC
  >- (
    fs[mem_store_byte_aux_def]
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ pop_assum mp_tac
    \\ BasicProvers.TOP_CASE_TAC \\ fs[]
    \\ simp[align_dm_def] )
  \\ imp_res_tac mem_store_byte_aux_align_dm \\ fs[]
QED

Theorem share_mem_op_align_dm_simp[simp]:
  (share_mem_op m r a s = NONE ==> share_mem_op m r a (align_dm s) = NONE) /\
  (share_mem_op m r a s = SOME (FFI_final f, s') ==>
  share_mem_op m r a (align_dm s) = SOME (FFI_final f, align_dm s')) /\
  (share_mem_op m r a s = SOME (FFI_return fs l, s') ==>
  share_mem_op m r a (align_dm s) = SOME (FFI_return fs l, align_dm s'))
Proof
  Cases_on `m` \\
  rw[inc_pc_def,dec_clock_def,share_mem_op_def,share_mem_load_def,share_mem_store_def] \\
  rpt (TOP_CASE_TAC >> fs[]) \\
  gvs[align_dm_def]
QED

Theorem evaluate_align_dm:
   good_dimindex(:α) ⇒
   ∀(s:(α,'c,'ffi) labSem$state).
      evaluate (align_dm s) =
      let (r,s') = evaluate s in (r, align_dm s')
Proof
  strip_tac
  \\ ho_match_mp_tac evaluate_ind
  \\ rpt strip_tac
  \\ simp[Once evaluate_def]
  \\ IF_CASES_TAC >- ( simp[Once evaluate_def] )
  \\ BasicProvers.TOP_CASE_TAC >- ( simp[Once evaluate_def] )
  \\ BasicProvers.TOP_CASE_TAC >- ( simp[Once evaluate_def] )
  >- (
    BasicProvers.TOP_CASE_TAC
    \\BasicProvers.TOP_CASE_TAC
    \\ simp[asm_inst_align_dm]
    \\ simp[Once evaluate_def,SimpRHS]
    \\ BasicProvers.TOP_CASE_TAC
    \\ simp[asm_inst_align_dm]
    \\ rw[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ fs[inc_pc_def,align_dm_def,dec_clock_def]
    >- (
      drule $ cj 3 $ PURE_REWRITE_RULE [align_dm_def] share_mem_op_align_dm_simp
      \\ disch_then assume_tac >> gvs[]
    )
    >- (
      drule $ cj 2 $ PURE_REWRITE_RULE [align_dm_def] share_mem_op_align_dm_simp
      \\ disch_then assume_tac >> gvs[]
    )
    >> (
      namedCases_on `x` ["q s'"] >> gvs[ELIM_UNCURRY]
      \\ TOP_CASE_TAC
      >- (drule $ cj 3 $ PURE_REWRITE_RULE [align_dm_def] share_mem_op_align_dm_simp
         \\ disch_then assume_tac >> gvs[])
      >- (drule $ cj 2 $ PURE_REWRITE_RULE [align_dm_def] share_mem_op_align_dm_simp
         \\ disch_then assume_tac >> gvs[])
    )
  )
  \\ BasicProvers.TOP_CASE_TAC
  \\ simp[Once evaluate_def,SimpRHS]
  \\ simp[case_eq_thms]
  \\ rpt(pairarg_tac \\ fs[] \\ rveq \\ fs[]) \\ fs[align_dm_def,case_eq_thms]
  \\ rveq \\ fs[] \\ pairarg_tac \\ fs[] \\ rfs[]
QED

Theorem implements_align_dm:
   good_dimindex(:α) ⇒
   implements' T {semantics (s:(α,'c,'ffi) labSem$state)} {semantics (align_dm s)}
Proof
  strip_tac
  \\ fs [semanticsPropsTheory.implements'_def]
  \\ fs [semanticsPropsTheory.extend_with_resource_limit'_def]
  \\ simp[semantics_def,GSYM align_dm_with_clock]
  \\ simp[evaluate_align_dm,UNCURRY_eq_pair,PULL_EXISTS]
  \\ simp[UNCURRY]
  \\ IF_CASES_TAC \\ fs[]
  \\ strip_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ METIS_TAC[]
QED

(** align_sdm **)

Definition align_sdm_def:
  align_sdm (s:('a,'c,'ffi) labSem$state) =
    (s with shared_mem_domain := s.shared_mem_domain INTER byte_aligned)
End

Theorem align_sdm_const[simp]:
   (align_sdm s).clock = s.clock ∧
   (align_sdm s).pc = s.pc ∧
   (align_sdm s).code = s.code ∧
   (align_sdm s).mem = s.mem ∧
   (align_sdm s).mem_domain = s.mem_domain ∧
   (align_sdm s).be = s.be ∧
   (align_sdm s).len_reg = s.len_reg ∧
   (align_sdm s).link_reg = s.link_reg ∧
   (align_sdm s).ptr_reg = s.ptr_reg ∧
   (align_sdm s).ptr2_reg = s.ptr2_reg ∧
   (align_sdm s).len2_reg = s.len2_reg ∧
   (align_sdm s).io_regs = s.io_regs ∧
   (align_sdm s).code_buffer = s.code_buffer ∧
   (align_sdm s).compile = s.compile ∧
   (align_sdm s).compile_oracle = s.compile_oracle ∧
   (align_sdm s).ffi = s.ffi ∧
   (align_sdm s).failed = s.failed
Proof
  EVAL_TAC
QED

Theorem align_sdm_with_clock:
   align_sdm (s with clock := k) = align_sdm s with clock := k
Proof
  EVAL_TAC
QED

Theorem asm_fetch_align_sdm[simp]:
   asm_fetch (align_sdm s) = asm_fetch s
Proof
  rw[asm_fetch_def]
QED

Theorem read_reg_align_sdm[simp]:
   read_reg n (align_sdm s) = read_reg n s
Proof
  EVAL_TAC
QED

Theorem upd_reg_align_sdm[simp]:
   upd_reg x y (align_sdm s) = align_sdm (upd_reg x y s)
Proof
  EVAL_TAC
QED

Theorem upd_mem_align_sdm[simp]:
   upd_mem x y (align_sdm s) = align_sdm (upd_mem x y s)
Proof
  EVAL_TAC
QED

Theorem binop_upd_align_sdm[simp]:
   binop_upd x y z w (align_sdm s) = align_sdm (binop_upd x y z w s)
Proof
  Cases_on`y` \\ simp[binop_upd_def]
QED

Theorem reg_imm_align_sdm[simp]:
   reg_imm r (align_sdm s) = reg_imm r s
Proof
  Cases_on`r` \\ EVAL_TAC
QED

Theorem assert_align_sdm[simp]:
   assert b (align_sdm s) = align_sdm (assert b s)
Proof
  EVAL_TAC
QED

Theorem arith_upd_align_sdm[simp]:
   arith_upd x (align_sdm s) = align_sdm (arith_upd x s)
Proof
  Cases_on`x` \\ rw[arith_upd_def]
  \\ every_case_tac \\ fs[]
QED

Theorem fp_upd_align_sdm[simp]:
   fp_upd f (align_sdm s) = align_sdm (fp_upd f s)
Proof
  Cases_on`f` \\ EVAL_TAC
  \\ every_case_tac \\ fs[] \\ EVAL_TAC \\fs[]
QED

Theorem addr_align_sdm[simp]:
   addr a (align_sdm s) = addr a s
Proof
  Cases_on`a` \\ EVAL_TAC
QED

Theorem mem_load_align_sdm:
   mem_load n (a:α addr) (align_sdm s) = align_sdm (mem_load n a s)
Proof
  simp[mem_load_def]
  \\ every_case_tac \\ fs[]
QED

Theorem mem_load_byte_align_sdm:
   mem_load_byte n (a:α addr) (align_sdm s) = align_sdm (mem_load_byte n a s)
Proof
  simp[mem_load_byte_def]
  \\ every_case_tac \\ fs[]
QED

Theorem mem_store_align_sdm:
   mem_store n (a:α addr) (align_sdm s) = align_sdm (mem_store n a s)
Proof
  simp[mem_store_def]
  \\ every_case_tac \\ fs[]
QED

Theorem mem_store_byte_align_sdm:
   mem_store_byte n (a:α addr) (align_sdm s) = align_sdm (mem_store_byte n a s)
Proof
  simp[mem_store_byte_def]
  \\ every_case_tac \\ fs[align_sdm_def]
QED

Theorem mem_op_align_sdm:
   mem_op m n (a:α addr) (align_sdm s) = align_sdm (mem_op m n a s)
Proof
  Cases_on`m`
  \\ simp[mem_op_def,
          mem_load_align_sdm,mem_load_byte_align_sdm,
          mem_store_align_sdm,mem_store_byte_align_sdm]
QED

Theorem asm_inst_align_sdm:
   asm_inst (i:α inst) (align_sdm s) = align_sdm (asm_inst i s)
Proof
  Cases_on`i` \\ simp[asm_inst_def,mem_op_align_sdm]
QED

Theorem dec_clock_align_sdm[simp]:
   dec_clock (align_sdm s) = align_sdm (dec_clock s)
Proof
  EVAL_TAC
QED

Theorem inc_pc_align_sdm[simp]:
   inc_pc (align_sdm s) = align_sdm (inc_pc s)
Proof
  EVAL_TAC
QED

Theorem upd_pc_align_sdm[simp]:
   upd_pc p (align_sdm s) = align_sdm (upd_pc p s)
Proof
  EVAL_TAC
QED

Theorem get_pc_value_align_sdm[simp]:
   get_pc_value x (align_sdm s) = get_pc_value x s
Proof
  EVAL_TAC \\ every_case_tac
QED

Theorem get_ret_Loc_align_sdm[simp]:
   get_ret_Loc (align_sdm s) = get_ret_Loc s
Proof
  EVAL_TAC
QED

Theorem read_bytearray_mem_load_byte_aux_align_sdm[simp]:
   ∀y x.
    read_bytearray x y (mem_load_byte_aux s.mem (align_sdm s).mem_domain s.be) =
   read_bytearray x y (mem_load_byte_aux s.mem s.mem_domain s.be)
Proof
  EVAL_TAC>>fs[]
QED

Theorem write_bytearray_align_sdm[simp]:
   ∀y x. write_bytearray x y s.mem (align_sdm s).mem_domain s.be =
   write_bytearray x y s.mem s.mem_domain s.be
Proof
  EVAL_TAC>>fs[]
QED

Theorem align_sdm_aligned:
  good_dimindex (:'a) ⇒
  (((x:'a word) ∈ s.shared_mem_domain ∧ w2n x MOD (dimindex (:'a) DIV 8) = 0) ⇔
    x ∈ (align_sdm s).shared_mem_domain)
Proof
  rw[EQ_IMP_THM,align_sdm_def]>>EVAL_TAC
  \\ simp[state_component_equality]
  \\ fs[alignmentTheory.byte_aligned_def,IN_DEF]
  \\ fs[good_dimindex_def]
  \\ fs[alignmentTheory.aligned_def]
  \\ Cases_on`x` \\ rfs[alignmentTheory.align_w2n]
  \\ rfs[]
  \\ rfs[dimword_def]>>fs[]>>
  TRY (fs[MOD_EQ_0_DIVISOR]>>
   gvs[]>>NO_TAC)>- (
  ‘0 < (4:num)’ by simp[]>>
  drule DA>> strip_tac>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
  fs[GSYM DIV_EQ_0]>>
  fs[DIV_EQ_0])>>
  ‘0 < (8:num)’ by simp[]>>
  drule DA>> strip_tac>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
  fs[GSYM DIV_EQ_0]>>
  fs[DIV_EQ_0]
QED

Theorem share_mem_load_align_sdm:
  good_dimindex (:'a) ⇒
  (share_mem_load r (ad:'a addr) (align_sdm s) n = NONE ⇔
     share_mem_load r ad s n = NONE) ∧
  (share_mem_load r ad s n = SOME (res, s') ⇒
   share_mem_load r ad (align_sdm s) n = SOME (res, align_sdm s'))
Proof
  strip_tac>>conj_tac>> (
  rw[EQ_IMP_THM]>>
  fs[share_mem_load_def,ffiTheory.call_FFI_def]>>
  every_case_tac>>fs[]>>
  TRY (drule_all (iffRL align_sdm_aligned)>>strip_tac>>
       fs[state_component_equality,align_sdm_def]>>NO_TAC)>>
  TRY (drule_all (iffLR align_sdm_aligned)>>strip_tac>>fs[])>> (
    drule_then drule (iffLR align_sdm_aligned)>>
    simp[MOD_EQ_0_DIVISOR]>>
    irule (iffRL MOD_EQ_0_DIVISOR)>>
    fs[good_dimindex_def,byte_align_def,align_w2n]>- (
      assume_tac $ Q.SPECL [‘w2n x’, ‘4’] DA>>fs[]>>
      fs[GSYM DIV_EQ_0]>>
      irule_at Any EQ_TRANS>>
      irule_at Any LESS_MOD>>
      irule_at Any LESS_EQ_LESS_TRANS>>
      irule_at Any w2n_lt>>
      qexists ‘x’>>fs[])>>
    assume_tac $ Q.SPECL [‘w2n x’, ‘8’] DA>>fs[]>>
    fs[GSYM DIV_EQ_0]>>
    irule_at Any EQ_TRANS>>
    irule_at Any LESS_MOD>>
    irule_at Any LESS_EQ_LESS_TRANS>>
    irule_at Any w2n_lt>>
    qexists ‘x’>>fs[]))
QED

Theorem share_mem_store_align_sdm:
  good_dimindex (:'a) ⇒
  (share_mem_store r (ad:'a addr) (align_sdm s) n = NONE ⇔
     share_mem_store r ad s n = NONE) ∧
  (share_mem_store r ad s n = SOME (res, s') ⇒
   share_mem_store r ad (align_sdm s) n = SOME (res, align_sdm s'))
Proof
  strip_tac>>conj_tac>> (
  rw[EQ_IMP_THM]>>
  fs[share_mem_store_def,ffiTheory.call_FFI_def]>>
  every_case_tac>>fs[inc_pc_def,dec_clock_def]>>
  TRY (drule_all (iffRL align_sdm_aligned)>>strip_tac>>
       fs[state_component_equality,align_sdm_def]>>NO_TAC)>>
  TRY (drule_all (iffLR align_sdm_aligned)>>strip_tac>>gvs[])>> (
    drule_then drule (iffLR align_sdm_aligned)>>
    simp[MOD_EQ_0_DIVISOR]>>
    irule (iffRL MOD_EQ_0_DIVISOR)>>
    fs[good_dimindex_def,byte_align_def,align_w2n]>- (
      assume_tac $ Q.SPECL [‘w2n x’, ‘4’] DA>>fs[]>>
      fs[GSYM DIV_EQ_0]>>
      irule_at Any EQ_TRANS>>
      irule_at Any LESS_MOD>>
      irule_at Any LESS_EQ_LESS_TRANS>>
      irule_at Any w2n_lt>>
      qexists ‘x’>>fs[])>>
    assume_tac $ Q.SPECL [‘w2n x’, ‘8’] DA>>fs[]>>
    fs[GSYM DIV_EQ_0]>>
    irule_at Any EQ_TRANS>>
    irule_at Any LESS_MOD>>
    irule_at Any LESS_EQ_LESS_TRANS>>
    irule_at Any w2n_lt>>
    qexists ‘x’>>fs[]))
QED

Theorem share_mem_op_align_sdm_simp[simp]:
  good_dimindex (:'a) ⇒
  (share_mem_op m r (a:'a addr) s = NONE ⇔ share_mem_op m r a (align_sdm s) = NONE) /\
  (share_mem_op m r a s = SOME (res, s') ==>
  share_mem_op m r a (align_sdm s) = SOME (res, align_sdm s'))
Proof
  Cases_on `m` \\
  rw[share_mem_op_def]>>
  fs[share_mem_load_align_sdm,share_mem_store_align_sdm]
QED

Theorem evaluate_align_sdm:
   good_dimindex(:α) ⇒
   ∀(s:(α,'c,'ffi) labSem$state).
      evaluate (align_sdm s) =
      let (r,s') = evaluate s in (r, align_sdm s')
Proof
  strip_tac
  \\ ho_match_mp_tac evaluate_ind
  \\ rpt strip_tac
  \\ simp[Once evaluate_def]
  \\ IF_CASES_TAC >- ( simp[Once evaluate_def] )
  \\ BasicProvers.TOP_CASE_TAC >- ( simp[Once evaluate_def] )
  \\ BasicProvers.TOP_CASE_TAC >- ( simp[Once evaluate_def] )
  >- (
    BasicProvers.TOP_CASE_TAC
    \\BasicProvers.TOP_CASE_TAC
    \\ simp[asm_inst_align_sdm]
    \\ simp[Once evaluate_def,SimpRHS]
    \\ BasicProvers.TOP_CASE_TAC
    \\ simp[asm_inst_align_sdm]
    \\ rw[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ simp[]
    \\ fs[inc_pc_def,align_sdm_def,dec_clock_def]
    >- (
      drule_all $ cj 2 $ PURE_REWRITE_RULE [align_sdm_def] share_mem_op_align_sdm_simp
      \\ disch_then assume_tac >> fs[]
    )
    >- (
      drule_all $ cj 2 $ PURE_REWRITE_RULE [align_sdm_def] share_mem_op_align_sdm_simp
      \\ disch_then assume_tac >> fs[]
    )
    >- (
    drule_all $ iffLR $ cj 1 $ PURE_REWRITE_RULE [align_sdm_def] share_mem_op_align_sdm_simp
        \\ disch_then assume_tac >> fs[]
)
    >- (
Cases_on ‘x’>>rename1 ‘(res, t)’>>fs[]>>
        TOP_CASE_TAC>>fs[]>>TRY (pairarg_tac>>fs[])>>
drule_all $ cj 2 $ PURE_REWRITE_RULE [align_sdm_def] share_mem_op_align_sdm_simp
        \\ disch_then assume_tac >> gvs[])
    >- (drule_all $ iffLR $ cj 1 $ PURE_REWRITE_RULE [align_sdm_def] share_mem_op_align_sdm_simp
        \\ disch_then assume_tac >> fs[])>>
Cases_on ‘x’>>fs[]>>
        TOP_CASE_TAC>>fs[]>>TRY (pairarg_tac>>fs[])>>
drule_all $ cj 2 $ PURE_REWRITE_RULE [align_sdm_def] share_mem_op_align_sdm_simp
        \\ disch_then assume_tac >> gvs[])
  \\ BasicProvers.TOP_CASE_TAC
  \\ simp[Once evaluate_def,SimpRHS]
  \\ simp[case_eq_thms]
  \\ rpt(pairarg_tac \\ fs[] \\ rveq \\ fs[]) \\ fs[align_sdm_def,case_eq_thms]
  \\ rveq \\ fs[] \\ pairarg_tac \\ fs[] \\ rfs[]
QED

Theorem implements_align_sdm:
   good_dimindex(:α) ⇒
   implements' T {semantics (s:(α,'c,'ffi) labSem$state)} {semantics (align_sdm s)}
Proof
  strip_tac
  \\ fs [semanticsPropsTheory.implements'_def]
  \\ fs [semanticsPropsTheory.extend_with_resource_limit'_def]
  \\ simp[semantics_def,GSYM align_sdm_with_clock]
  \\ simp[evaluate_align_sdm,UNCURRY_eq_pair,PULL_EXISTS]
  \\ simp[UNCURRY]
  \\ IF_CASES_TAC \\ fs[]
  \\ strip_tac
  \\ rpt (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ simp[FUN_EQ_THM]
  \\ METIS_TAC[]
QED


(* asm_ok checks coming into lab_to_target *)
Definition line_ok_pre_def:
  (line_ok_pre (c:'a asm_config) (Asm b bytes l) ⇔ asm_ok (cbw_to_asm b) c) ∧
  (line_ok_pre c _ ⇔ T)
End

Definition sec_ok_pre_def:
  sec_ok_pre c (Section k ls) ⇔
    EVERY (line_ok_pre c) ls
End
val _ = export_rewrites["sec_ok_pre_def"];

Overload all_enc_ok_pre = ``λc ls. EVERY (sec_ok_pre c) ls``

(* invariant: labels have correct section number and are non-zero *)

Definition sec_label_ok_def:
  (sec_label_ok k (Label l1 l2 len) ⇔ l1 = k ∧ l2 ≠ 0) ∧
  (sec_label_ok _ _ = T)
End
val _ = export_rewrites["sec_label_ok_def"];

Definition sec_labels_ok_def:
  sec_labels_ok (Section k ls) ⇔ EVERY (sec_label_ok k) ls
End
val _ = export_rewrites["sec_labels_ok_def"];

Theorem sec_label_ok_extract_labels:
   EVERY (sec_label_ok n1) lines ∧
   MEM (n1',n2) (extract_labels lines) ⇒
   n1' = n1 ∧ n2 ≠ 0
Proof
  Induct_on`lines` \\ simp[]
  \\ Cases \\ rw[] \\ fs[]
QED

Theorem EVERY_sec_label_ok:
   EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels l) (*∧
    ALL_DISTINCT (extract_labels l) *)⇔
    EVERY (sec_label_ok n) l
Proof
  Induct_on`l`>>simp[extract_labels_def]>>
  Cases>>simp[extract_labels_def]
QED

Theorem line_get_code_labels_extract_labels:
   ∀l.
   BIGUNION (IMAGE line_get_code_labels (set l)) =
   IMAGE SND (set (extract_labels l))
Proof
  recInduct extract_labels_ind
  \\ rw[extract_labels_def]
  \\ rw[EXTENSION]
QED

Theorem get_code_labels_extract_labels:
   ∀code.
   EVERY sec_labels_ok code ⇒
   get_code_labels code =
   IMAGE (λs. (Section_num s, 0)) (set code) ∪
   set (FLAT (MAP (extract_labels o Section_lines) code))
Proof
  Induct \\ simp[get_code_labels_cons] \\ Cases
  \\ rw[sec_get_code_labels_def, LIST_TO_SET_FLAT]
  \\ rw[line_get_code_labels_extract_labels]
  \\ rw[UNION_ASSOC]
  \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ rw[Once EXTENSION, EXISTS_PROD, FORALL_PROD]
  \\ metis_tac[sec_label_ok_extract_labels]
QED

Definition no_install_def:
  no_install code <=>
  !p w bytes l.
    asm_fetch_aux p code <>
      SOME (LabAsm Install w bytes l)
End

Definition no_share_mem_inst_def:
  no_share_mem_inst code <=>
  !p op re a inst len.
    asm_fetch_aux p code <>
      SOME (Asm (ShareMem op re a) inst len)
End

val _ = export_theory();
