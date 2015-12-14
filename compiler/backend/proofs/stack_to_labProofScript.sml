open preamble
     stackSemTheory
     stack_to_labTheory
     labSemTheory labPropsTheory

val _ = new_theory"stack_to_labProof";

(* TODO: move *)

val word_sh_word_shift = Q.store_thm("word_sh_word_shift",
  `word_sh a b c = SOME z ⇒ z = word_shift a b c`,
  EVAL_TAC >> rw[] >> every_case_tac >> fs[] >>
  EVAL_TAC >> rw[]);

val assert_T = Q.store_thm("assert_T[simp]",
  `assert T s = s`,
  rw[assert_def,state_component_equality]);

val good_syntax_def = Define `
  (good_syntax ((Seq p1 p2):'a stackLang$prog) ptr len ret <=>
     good_syntax p1 ptr len ret /\
     good_syntax p2 ptr len ret) /\
  (good_syntax ((If c r ri p1 p2):'a stackLang$prog) ptr len ret <=>
     good_syntax p1 ptr len ret /\
     good_syntax p2 ptr len ret) /\
  (good_syntax (Halt n) ptr len ret <=> (n = len)) /\
  (good_syntax (FFI ffi_index ptr' len') ptr len ret <=>
     ptr' = ptr /\ len' = len) /\
  (good_syntax (Call x1 _ x2) ptr len ret <=>
     (case x1 of
      | SOME (y,r,_,_) => good_syntax y ptr len ret /\ r = ret
      | NONE => T) /\
     (case x2 of SOME (y,_,_) => good_syntax y ptr len ret | NONE => T)) /\
  (good_syntax _ ptr len ret <=> T)`

val word_cmp_word_cmp = Q.store_thm("word_cmp_word_cmp",
  `(word_cmp cmp (Word w1) (Word w2) = SOME T) ⇔ word_cmp cmp w1 w2`,
  Cases_on`cmp`>>rw[labSemTheory.word_cmp_def]>>
  rw[asmSemTheory.word_cmp_def]);

(* -- *)

val code_installed_def = Define`
  (code_installed n [] code = T) ∧
  (code_installed n (x::xs) code ⇔
   asm_fetch_aux n code = SOME x ∧
   code_installed (n+1) xs code)`;

val code_installed_append_imp = Q.store_thm("code_installed_append_imp",
  `∀l1 pc l2 code. code_installed pc (l1 ++ l2) code ⇒
   code_installed pc l1 code ∧
   code_installed (pc+LENGTH l1) l2 code`,
  Induct>>simp[code_installed_def]>>rw[] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1]);

val state_rel_def = Define`
  state_rel (s:('a,'b)stackSem$state) (t:('a,'b)labSem$state) ⇔
    (∀n v. FLOOKUP n s.regs = SOME v ⇒ t.regs n = v) ∧
    t.mem = s.memory ∧
    t.mem_domain = s.mdomain ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    (∀n prog. lookup n s.code = SOME prog ⇒
      good_syntax prog t.len_reg t.ptr_reg t.link_reg ∧
      ∃pc. code_installed pc (FST (flatten prog n (max_lab prog))) t.code ∧
           loc_to_pc n 0 t.code = SOME pc) ∧
    ¬t.failed ∧
    is_word (read_reg t.ptr_reg t) ∧
    (∀x. x ∈ s.mdomain ⇒ w2n x MOD (dimindex (:'a) DIV 8) = 0) ∧
    ¬s.use_stack ∧
    ¬s.use_store ∧
    ¬s.use_alloc`;

val state_rel_dec_clock = Q.store_thm("state_rel_dec_clock",
  `state_rel s t ⇒ state_rel (dec_clock s) (dec_clock t)`,
  rw[state_rel_def,stackSemTheory.dec_clock_def,labSemTheory.dec_clock_def] >>
  metis_tac[])

val state_rel_with_pc = Q.store_thm("state_rel_with_pc",
  `state_rel s t ⇒ state_rel s (upd_pc pc t)`,
  rw[state_rel_def,upd_pc_def] >>
  metis_tac[])

val set_var_upd_reg = Q.store_thm("set_var_upd_reg",
  `state_rel s t ∧ is_word b ⇒
   state_rel (set_var a b s) (upd_reg a b t)`,
  rw[state_rel_def,upd_reg_def,set_var_def,FUN_EQ_THM,APPLY_UPDATE_THM,FAPPLY_FUPDATE_THM] >>
  rw[]>>fs[]>>rfs[] \\ metis_tac [])

val set_var_Word_upd_reg = Q.store_thm("set_var_Word_upd_reg[simp]",
  `state_rel s t ⇒
   state_rel (set_var a (Word b) s) (upd_reg a (Word b) t)`,
   METIS_TAC[set_var_upd_reg,wordSemTheory.is_word_def])

val mem_store_upd_mem = Q.store_thm("mem_store_upd_mem",
  `state_rel s t ∧ mem_store x y s = SOME s1 ⇒
   state_rel s1 (upd_mem x y t)`,
  rw[state_rel_def,upd_mem_def,stackSemTheory.mem_store_def,FUN_EQ_THM,APPLY_UPDATE_THM] >>
  rw[APPLY_UPDATE_THM] >> rfs[] >> metis_tac []);

val state_rel_read_reg_FLOOKUP_regs = Q.store_thm("state_rel_read_reg_FLOOKUP_regs",
  `state_rel s t ∧
   FLOOKUP s.regs x = SOME y ⇒
   y = read_reg x t`,
  rw[state_rel_def]>>fs[FLOOKUP_DEF]);

val inst_correct = Q.store_thm("inst_correct",
  `inst i s1 = SOME s2 ∧
   state_rel s1 t1 ⇒
   state_rel s2 (asm_inst i t1)`,
  simp[inst_def] >>
  every_case_tac >> fs[] >>
  rw[assign_def,word_exp_def] >> rw[] >>
  fs[LET_THM] >>
  every_case_tac >> fs[] >> rw[] >>
  imp_res_tac state_rel_read_reg_FLOOKUP_regs >> fs[] >> rfs[] >>
  imp_res_tac word_sh_word_shift >>
  fs[wordSemTheory.num_exp_def,wordSemTheory.word_op_def] >> rw[] >>
  TRY ( Cases_on`b`>>fs[binop_upd_def] >> NO_TAC) >>
  TRY (
    fs[stackSemTheory.mem_load_def,labSemTheory.mem_load_def,labSemTheory.addr_def] >>
    qpat_assum`Word _ = _`(assume_tac o SYM) >> fs[] >>
    `t1.mem_domain = s1.mdomain ∧ t1.mem = s1.memory` by ( fs[state_rel_def] ) >> fs[] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    simp[] ) >>
  fs[stackSemTheory.word_exp_def,LET_THM,IS_SOME_EXISTS] >>
  every_case_tac >> fs[] >> rpt var_eq_tac >>
  fs[wordSemTheory.word_op_def,stackSemTheory.get_var_def] >> rpt var_eq_tac >>
  res_tac >>
  qpat_assum`Word _ = _`(assume_tac o SYM) >> fs[] >>
  `t1.mem_domain = s1.mdomain ∧ t1.mem = s1.memory` by ( fs[state_rel_def] ) >> fs[] >>
  fs[labSemTheory.mem_store_def,labSemTheory.addr_def] >>
  qmatch_assum_abbrev_tac`mem_store cc _ _ = _` >>
  `cc ∈ s1.mdomain` by fs[stackSemTheory.mem_store_def] >>
  first_assum(fn th => first_assum(
    tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
  simp[] >>
  imp_res_tac mem_store_upd_mem);

val flatten_leq = Q.store_thm("flatten_leq",
  `∀x y z. z ≤ SND (flatten x y z)`,
  ho_match_mp_tac flatten_ind >> rw[]>>
  ONCE_REWRITE_TAC[flatten_def] >>
  CASE_TAC >> simp[] >> fs[] >>
  every_case_tac >> fs[] >>
  split_pair_tac >> fs[] >>
  split_pair_tac >> fs[] >>
  simp[]);

val flatten_correct = Q.store_thm("flatten_correct",
  `∀prog s1 r s2 n l t1.
     evaluate (prog,s1) = (r,s2) ∧ r ≠ SOME Error ∧
     state_rel s1 t1 ∧
     good_syntax prog t1.len_reg t1.ptr_reg t1.link_reg ∧
     code_installed t1.pc (FST (flatten prog n l)) t1.code ∧
     max_lab prog ≤ l
     ⇒
     ∃ck t2.
     case r of SOME (Halt w) =>
         evaluate (t1 with clock := t1.clock + ck) =
           ((case w of
             | Word 0w => Halt Success
             | Word _ => Halt Resource_limit_hit
             | _ => Error),
            t2) ∧
         t2.ffi = s2.ffi
     | _ =>
       (∀ck1. evaluate (t1 with clock := t1.clock + ck + ck1) =
         evaluate (t2 with clock := t2.clock + ck1)) ∧
       t2.len_reg = t1.len_reg ∧
       t2.ptr_reg = t1.ptr_reg ∧
       t2.link_reg = t1.link_reg ∧
       t2.code = t1.code ∧
       case r of
       | NONE =>
         t2.pc = t1.pc + LENGTH (FST(flatten prog n l)) ∧
         state_rel s2 t2
       | SOME (Result (Loc n1 n2)) =>
           ∀w. loc_to_pc n1 n2 t2.code = SOME w ⇒
               w = t2.pc ∧
               state_rel s2 t2
       | SOME (Exception (Loc n1 n2)) =>
           ∀w. loc_to_pc n1 n2 t2.code = SOME w ⇒
               w = t2.pc ∧
               state_rel s2 t2
       | SOME TimeOut => t2.ffi = s2.ffi ∧ t2.clock = 0
       | _ => F`,
  recInduct stackSemTheory.evaluate_ind >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    qexists_tac`0`>>simp[] >>
    METIS_TAC[with_same_clock,state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var v s`>>fs[] >> rpt var_eq_tac >>
    simp[] >>
    fs[code_installed_def] >>
    qexists_tac`1`>>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    fs[get_var_def,FLOOKUP_DEF] >> var_eq_tac >>
    fs [good_syntax_def,state_rel_def] >> rfs [] >>
    every_case_tac >> fs []) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`inst i s`>>fs[]>>rpt var_eq_tac>>simp[]>>
    imp_res_tac inst_correct >>
    qexists_tac`1`>>
    fs[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    Cases_on`(asm_inst i t1).failed` >- fs[state_rel_def] >>
    simp[dec_clock_def,asm_inst_consts] >>
    qexists_tac`inc_pc (asm_inst i t1)` >>
    simp[inc_pc_def,asm_inst_consts] >>
    fs[state_rel_def,asm_inst_consts] >>
    METIS_TAC[]) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    fs[state_rel_def] ) >>
  (* Tick *)
  conj_tac >- (
    simp[stackSemTheory.evaluate_def,flatten_def] >>
    rpt gen_tac >> strip_tac >>
    fs[code_installed_def] >>
    Cases_on`s.clock=0`>>fs[]>>rpt var_eq_tac>>fs[]>-(
      qexists_tac`1`>>simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      Cases_on`t1.failed`>>fs[]>-fs[state_rel_def]>>
      simp[dec_clock_def] >>
      `t1.clock = 0` by fs[state_rel_def] >>
      qexists_tac`inc_pc t1` >>
      simp[inc_pc_def,empty_env_def] >>
      fs[state_rel_def]) >>
    qexists_tac`0`>>simp[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    Cases_on`t1.failed`>>fs[]>-fs[state_rel_def]>>
    qexists_tac`inc_pc (dec_clock t1)` >>
    fs[inc_pc_def,stackSemTheory.dec_clock_def,labSemTheory.dec_clock_def] >>
    fs[state_rel_def] >>
    fsrw_tac[ARITH_ss][] >>
    metis_tac[]) >>
  (* Seq *)
  conj_tac >- (
    rw[] >>
    rator_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    strip_tac >>
    split_pair_tac >> fs[] >>
    rator_x_assum`code_installed`mp_tac >>
    simp[Once flatten_def] >>
    simp[UNCURRY] >> strip_tac >>
    imp_res_tac code_installed_append_imp >>
    fs[Q.SPEC`Seq _ _`max_lab_def] >>
    fs[good_syntax_def] >>
    reverse (Cases_on`res`)>>fs[]>-(
      rpt var_eq_tac >> fs[] >>
      first_x_assum drule >>
      disch_then drule >>
      disch_then drule >>
      strip_tac >>
      CASE_TAC >> fs[] >>
      TRY CASE_TAC >> fs[] >>
      res_tac >>
      qexists_tac`ck`>>fsrw_tac[ARITH_ss][]>>
      TRY ( qexists_tac`t2` >> simp[] >> NO_TAC) >>
      metis_tac[] ) >>
    first_x_assum drule >>
    disch_then drule >>
    simp[] >>
    disch_then drule >> simp[] >>
    strip_tac >>
    first_x_assum drule >>
    CONV_TAC(LAND_CONV(STRIP_QUANT_CONV(LAND_CONV(lift_conjunct_conv(same_const``code_installed`` o fst o strip_comb))))) >>
    fsrw_tac[ARITH_ss][] >>
    disch_then drule >>
    discharge_hyps >- (
      metis_tac[flatten_leq,LESS_EQ_TRANS] ) >>
    strip_tac >>
    CASE_TAC >> fs[] >- (
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``state_rel`` o fst o strip_comb))) >>
      asm_exists_tac >> simp[] >>
      simp[Q.SPEC`Seq _ _`flatten_def,UNCURRY] >>
      qexists_tac`ck+ck'`>>simp[]>>rw[] >>
      last_x_assum(qspec_then`ck1+ck'`strip_assume_tac) >>
      fsrw_tac[ARITH_ss][]) >>
    CASE_TAC >> fs[] >>
    TRY CASE_TAC >> fs[] >>
    res_tac >>
    ((CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``state_rel`` o fst o strip_comb))) >>
      asm_exists_tac >> simp[] ) ORELSE
     (CONV_TAC SWAP_EXISTS_CONV >> qexists_tac`t2'` >> simp[])) >>
    qexists_tac`ck+ck'`>>simp[]>>rw[] >>
    last_x_assum(qspec_then`ck1+ck'`strip_assume_tac) >>
    fsrw_tac[ARITH_ss][] ) >>
  (* Return *)
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var n s`>>fs[]>> Cases_on`x`>>fs[]>>
    Cases_on`get_var m s`>>fs[]>>
    rpt var_eq_tac >> simp[] >>
    fs[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    `get_var n s = SOME (read_reg n t1)` by (
      fs[state_rel_def,get_var_def] >>
      fs[FLOOKUP_DEF] ) >>
    fs[] >>
    qexists_tac`1`>>simp[] >> rfs[] >>
    CASE_TAC >> fs[] >- (
      qexists_tac`t1 with clock := t1.clock + 1` >> simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] ) >>
    simp[dec_clock_def] >>
    qmatch_assum_rename_tac`_ = SOME pc` >>
    qexists_tac`upd_pc pc t1` >>
    simp[upd_pc_def] >>
    fs[state_rel_def] >>
    metis_tac[]) >>
  (* Raise *)
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var n s`>>fs[]>>
    Cases_on`x`>>fs[]>>
    rpt var_eq_tac >> simp[] >>
    qexists_tac`1`>>simp[]>>
    fs[code_installed_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    `get_var n s = SOME (read_reg n t1)` by (
      fs[state_rel_def,get_var_def] >>
      fs[FLOOKUP_DEF] ) >>
    fs[] >>
    CASE_TAC >> fs[] >- (
      qexists_tac`t1 with clock := t1.clock + 1` >> simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] ) >>
    simp[dec_clock_def] >>
    qmatch_assum_rename_tac`_ = SOME pc` >>
    qexists_tac`upd_pc pc t1` >>
    simp[upd_pc_def] >>
    fs[state_rel_def] >>
    metis_tac[]) >>
  (* If *)
  conj_tac >- (
    cheat
  ) >>
  (* JumpLess *)
  conj_tac >- (
    rw[] >>
    fs[Q.SPEC`JumpLess _ _ _`flatten_def] >>
    rator_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    Cases_on`get_var r1 s`>>fs[]>> Cases_on`x`>>fs[]>>
    Cases_on`get_var r2 s`>>fs[]>> Cases_on`x`>>fs[]>>
    fs[code_installed_def] >>
    `get_var r1 s = SOME (read_reg r1 t1) ∧
     get_var r2 s = SOME (read_reg r2 t1)` by (
      fs[state_rel_def,get_var_def] >>
      fs[FLOOKUP_DEF] ) >>
    reverse IF_CASES_TAC >> fs[] >- (
      rw[] >> simp[] >>
      qexists_tac`1`>>simp[]>>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      fs[GSYM word_cmp_word_cmp] >>
      CASE_TAC >> fs[] >- (
        fs[labSemTheory.word_cmp_def] ) >>
      qexists_tac`inc_pc t1` >>
      simp[dec_clock_def,inc_pc_def]>>
      fs[state_rel_def] >>
      metis_tac[]) >>
    ntac 2 CASE_TAC >> fs[] >- (
      rw[] >> simp[empty_env_def] >>
      `t1.clock = 0` by fs[state_rel_def] >>
      qexists_tac`0`>>simp[]>>
      qexists_tac`t1`>>simp[]>>
      fs[state_rel_def] ) >>
    ntac 2 CASE_TAC >> fs[]>>
    rw[] >> simp[] >> fs[] >>
    fs[find_code_def] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    imp_res_tac state_rel_dec_clock >>
    drule state_rel_with_pc >>
    pop_assum kall_tac >> strip_tac >>
    first_x_assum drule >> fs[] >>
    disch_then drule >> simp[] >>
    strip_tac >>
    CASE_TAC >> fs[] >>
    TRY CASE_TAC >> fs[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    fs[GSYM word_cmp_word_cmp,get_pc_value_def] >>
    `t1.clock ≠ 0` by fs[state_rel_def] >> simp[] >>
    fs[dec_clock_def,upd_pc_def] >>
    qexists_tac`ck`>>
    fsrw_tac[ARITH_ss][] >>
    qexists_tac`t2` >>
    simp[] ) >>
  (* Call *)
  conj_tac >- (
    rw[] >>
    rator_x_assum`code_installed`mp_tac >>
    simp[Once flatten_def] >> strip_tac >>
    rator_x_assum`evaluate`mp_tac >>
    simp[Once stackSemTheory.evaluate_def] >>
    Cases_on`find_code dest s.regs s.code`>>fs[]>>
    Cases_on`ret`>>fs[]>-(
      Cases_on`handler`>>fs[]>>
      IF_CASES_TAC >> fs[] >- (
        rw[] >> simp[] >>
        map_every qexists_tac[`0`,`t1`] >>
        fs[] >> fs[state_rel_def,empty_env_def] ) >>
      `t1.clock ≠ 0` by fs[state_rel_def] >>
      CASE_TAC >> fs[] >>
      CASE_TAC >> fs[] >>
      rw[] >> simp[] >> fs[] >>
      imp_res_tac state_rel_dec_clock >>
      Cases_on`dest`>>fs[find_code_def,compile_jump_def,code_installed_def] >- (
        first_assum(fn th => first_assum(
          tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
        drule state_rel_with_pc >>
        rator_x_assum`state_rel`kall_tac >>
        strip_tac >>
        first_x_assum drule >>
        simp[] >>
        disch_then drule >> simp[] >>
        strip_tac >> fs[] >>
        CASE_TAC >> fs[] >>
        TRY CASE_TAC >> fs[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
        fs[dec_clock_def,upd_pc_def] >>
        map_every qexists_tac[`ck`,`t2`]>>fs[] ) >>
      qpat_assum`_ = SOME _`mp_tac >>
      CASE_TAC >> fs[] >>
      CASE_TAC >> fs[] >>
      CASE_TAC >> fs[] >>
      strip_tac >>
      first_assum(fn th => first_assum(
        tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
      drule state_rel_with_pc >>
      rator_x_assum`state_rel`kall_tac >>
      strip_tac >>
      first_x_assum drule >>
      simp[] >>
      disch_then drule >> simp[] >>
      strip_tac >> fs[] >>
      qmatch_assum_rename_tac`FLOOKUP s.regs r = SOME _` >>
      `read_reg r t1 = Loc n 0` by (
        fs[state_rel_def,FLOOKUP_DEF] ) >>
      CASE_TAC >> fs[] >>
      TRY CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
      fs[dec_clock_def,upd_pc_def] >>
      map_every qexists_tac[`ck`,`t2`]>>fs[] ) >>
    cheat ) >>
  (* FFI *)
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var ptr s`>>fs[]>>Cases_on`x`>>fs[]>>
    Cases_on`get_var len s`>>fs[]>>Cases_on`x`>>fs[]>>
    last_x_assum mp_tac >> CASE_TAC >> simp[] >>
    split_pair_tac >> simp[] >> rw[] >> simp[] >>
    fs [good_syntax_def] >> rw [] >>
    simp[Once labSemTheory.evaluate_def] >>
    qexists_tac `1` >> fs [] >>
    fs [code_installed_def,asm_fetch_def] >>
    cheat ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  conj_tac >- (
    rw[stackSemTheory.evaluate_def] >>
    fs[state_rel_def] ) >>
  rw[stackSemTheory.evaluate_def] >>
  fs[state_rel_def]);

val _ = export_theory();
