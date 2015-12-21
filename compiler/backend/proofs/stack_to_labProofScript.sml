open preamble
     stackSemTheory
     stack_to_labTheory
     stack_allocTheory
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
  (good_syntax (FFI ffi_index ptr' len' ret') ptr len ret <=>
     ptr' = ptr /\ len' = len /\ ret' = ret) /\
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

val asm_fetch_aux_no_label = Q.store_thm("asm_fetch_aux_no_label",
  `∀pc code.
   asm_fetch_aux pc code = SOME (Label l1 l2 x) ⇒ F`,
  ho_match_mp_tac asm_fetch_aux_ind >>
  rw[asm_fetch_aux_def] >> Cases_on`y`>>fs[]);

val dest_to_loc_def = Define`
  dest_to_loc regs dest =
    case dest of INL p => p | INR r => case FAPPLY regs r of Loc loc _ => loc`;

val dest_to_loc'_def = Define`
  dest_to_loc' regs dest =
    case dest of INL p => p | INR r => case regs r of Loc loc _ => loc`;

val find_code_lookup = Q.store_thm("find_code_lookup",
  `find_code dest regs code = SOME p ⇒
    lookup (dest_to_loc regs dest) code = SOME p ∧
    (∀r. dest = INR r ⇒ r ∈ FDOM regs)`,
  Cases_on`dest`>>rw[find_code_def,dest_to_loc_def] >>
  every_case_tac >> fs[] >> fs[FLOOKUP_DEF] >> rw[]);

val not_is_Label_compile_jump = Q.store_thm("not_is_Label_compile_jump[simp]",
  `is_Label (compile_jump dest) ⇔ F`,
  Cases_on`dest`>>EVAL_TAC);

val word_cmp_not_NONE = Q.store_thm("word_cmp_not_NONE[simp]",
  `word_cmp cmp (Word w1) (Word w2) ≠ NONE`,
  Cases_on`cmp`>>rw[labSemTheory.word_cmp_def]);

val word_cmp_negate = Q.store_thm("word_cmp_negate[simp]",
  `word_cmp (negate cmp) w1 w2 ⇔ ¬word_cmp cmp w1 w2`,
  Cases_on`cmp`>>EVAL_TAC);

val word_cmp_negate = Q.store_thm("word_cmp_negate[simp]",
  `word_cmp (negate cmp) (Word w1) (Word w2) =
   OPTION_MAP $~ (word_cmp cmp (Word w1) (Word w2))`,
  Cases_on`word_cmp cmp (Word w1) (Word w2)`>>fs[]>>
  Cases_on`word_cmp (negate cmp) (Word w1) (Word w2)`>>fs[] >>
  Cases_on`x`>>fs[word_cmp_word_cmp]>>
  Cases_on`x'`>>fs[word_cmp_word_cmp]>>
  Cases_on`cmp`>>fs[word_cmp_def]);

(* -- *)

val code_installed_def = Define`
  (code_installed n [] code = T) ∧
  (code_installed n (x::xs) code ⇔
   if is_Label x then
     (case x of Label l1 l2 _ => loc_to_pc l1 l2 code = SOME n) ∧
     code_installed n xs code
   else
     asm_fetch_aux n code = SOME x ∧
     code_installed (n+1) xs code)`;

val code_installed_append_imp = Q.store_thm("code_installed_append_imp",
  `∀l1 pc l2 code. code_installed pc (l1 ++ l2) code ⇒
   code_installed pc l1 code ∧
   code_installed (pc+LENGTH (FILTER ($~ o is_Label) l1)) l2 code`,
  Induct>>simp[code_installed_def]>>rw[] >>
  res_tac >> fsrw_tac[ARITH_ss][ADD1]);

val state_rel_def = Define`
  state_rel (s:('a,'b)stackSem$state) (t:('a,'b)labSem$state) ⇔
    (∀n v. FLOOKUP s.regs n = SOME v ⇒ t.regs n = v) ∧
    t.mem = s.memory ∧
    t.mem_domain = s.mdomain ∧
    t.be = s.be ∧
    t.ffi = s.ffi ∧
    t.clock = s.clock ∧
    (∀n prog. lookup n s.code = SOME prog ⇒
      good_syntax prog t.len_reg t.ptr_reg t.link_reg ∧
      ∃pc. code_installed pc (FST (flatten prog n (next_lab prog))) t.code ∧
           loc_to_pc n 0 t.code = SOME pc) ∧
    ¬t.failed ∧
    t.link_reg ≠ t.len_reg ∧ t.link_reg ≠ t.ptr_reg ∧
    ~(t.link_reg ∈ s.ffi_save_regs) /\
    (!k n. k ∈ s.ffi_save_regs ==> t.io_regs n k = NONE) /\
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
  rw[state_rel_def,upd_reg_def,set_var_def,FUN_EQ_THM,APPLY_UPDATE_THM,FLOOKUP_UPDATE] >>
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
  TRY CASE_TAC >> fs[] >>
  every_case_tac >> fs[] >>
  split_pair_tac >> fs[] >>
  TRY split_pair_tac >> fs[] >>
  simp[]);

val no_ret_correct = Q.store_thm("no_ret_correct",
  `∀p. no_ret p ⇒ ∀s. IS_SOME (FST (evaluate (p,s)))`,
  ho_match_mp_tac no_ret_ind >> rw[] >>
  Cases_on`p`>>simp[stackSemTheory.evaluate_def] >>
  fs[Once no_ret_def] >>
  fs[GSYM no_ret_def] >>
  every_case_tac >> fs[] >> rw[] >>
  rfs[IS_SOME_EXISTS] >>
  TRY split_pair_tac >> fs[] >>
  METIS_TAC[NOT_SOME_NONE,FST,option_CASES] );

val compile_jump_correct = Q.store_thm("compile_jump_correct",
  `asm_fetch_aux pc code = SOME (compile_jump dest) ∧
   loc_to_pc (dest_to_loc' regs dest) 0 code = SOME pc' ∧
   (∀r. dest = INR r ⇒ ∃p. read_reg r s = Loc p 0) ∧
   s.pc = pc ∧ s.code = code ∧ s.regs = regs ∧ s.clock ≠ 0
   ⇒
   evaluate s = evaluate (upd_pc pc' (dec_clock s))`,
  Cases_on`dest`>>rw[compile_jump_def,dest_to_loc'_def] >>
  simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
  CASE_TAC >> fs[]);

val flatten_correct = Q.store_thm("flatten_correct",
  `∀prog s1 r s2 n l t1.
     evaluate (prog,s1) = (r,s2) ∧ r ≠ SOME Error ∧
     state_rel s1 t1 ∧
     good_syntax prog t1.len_reg t1.ptr_reg t1.link_reg ∧
     code_installed t1.pc (FST (flatten prog n l)) t1.code
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
         t2.pc = t1.pc + LENGTH (FILTER ($~ o is_Label) (FST(flatten prog n l))) ∧
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
    fs[get_var_def] >>
    fs [good_syntax_def,state_rel_def] >> rfs [] >>
    res_tac >> fs[] >>
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
    fs[Q.SPEC`Seq _ _`next_lab_def] >>
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
    strip_tac >>
    CASE_TAC >> fs[] >- (
      CONV_TAC(STRIP_QUANT_CONV(lift_conjunct_conv(same_const``state_rel`` o fst o strip_comb))) >>
      asm_exists_tac >> simp[] >>
      simp[Q.SPEC`Seq _ _`flatten_def,UNCURRY] >>
      qexists_tac`ck+ck'`>>simp[FILTER_APPEND]>>rw[] >>
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
    rw[] >>
    fs[stackSemTheory.evaluate_def] >>
    Cases_on`get_var r1 s`>>fs[]>>Cases_on`x`>>fs[]>>
    Cases_on`get_var_imm ri s`>>fs[]>>Cases_on`x`>>fs[]>>
    fs[Q.SPEC`If _ _ _ _ _`flatten_def,LET_THM] >>
    split_pair_tac >> fs[] >>
    split_pair_tac >> fs[] >>
    Cases_on`c1=Skip`>>fs[]>-(
      Cases_on`c2=Skip`>>fs[] >- (
        fs[Q.SPEC`Skip`flatten_def]>>
        rpt var_eq_tac >>
        fs[stackSemTheory.evaluate_def]>>
        rpt var_eq_tac >> simp[] >>
        map_every qexists_tac[`0`,`t1`] >>
        simp[] ) >>
      fs[Q.SPEC`Skip`flatten_def]>>
      rpt var_eq_tac >>
      fs[stackSemTheory.evaluate_def]>>
      fs[code_installed_def] >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        qpat_assum`word_cmp _ _ _ ⇒ _`kall_tac >>
        qpat_assum`¬word_cmp _ _ _ ⇒ _`kall_tac >>
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      fs[GSYM word_cmp_word_cmp] >>
      qmatch_assum_rename_tac`read_reg _ _ = Word w1` >>
      qmatch_assum_rename_tac`reg_imm _ _ = Word w2` >>
      Cases_on`word_cmp cmp (Word w1) (Word w2)`>>fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      Cases_on`x`>>fs[] >- (
        rpt var_eq_tac >> simp[] >>
        simp[get_pc_value_def] >>
        imp_res_tac code_installed_append_imp >>
        fs[code_installed_def] >>
        simp[dec_clock_def,ADD1,upd_pc_def] >>
        qpat_abbrev_tac`pc = LENGTH _ + _` >>
        drule state_rel_with_pc >> strip_tac >>
        first_x_assum drule >>
        simp[good_syntax_def,next_lab_def] >>
        simp[upd_pc_def] >> strip_tac >>
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      fs[Q.SPEC`If _ _ _ _ _`next_lab_def] >>
      drule (GEN_ALL state_rel_with_pc) >>
      disch_then(qspec_then`t1.pc+1`strip_assume_tac) >>
      first_x_assum drule >>
      fs[good_syntax_def] >>
      imp_res_tac code_installed_append_imp >>
      disch_then(qspecl_then[`n`,`l`]mp_tac)>>simp[] >>
      strip_tac >>
      simp[dec_clock_def,ADD1] >>
      fs[inc_pc_def,upd_pc_def] >>
      Cases_on`r`>>fs[] >- (
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>fs[FILTER_APPEND] ) >>
      CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[dec_clock_def,inc_pc_def] >>
      qexists_tac`ck`>>simp[] >>
      qexists_tac`t2`>>simp[]) >>
    Cases_on`c2=Skip`>>fs[]>-(
      fs[Q.SPEC`Skip`flatten_def]>>
      rpt var_eq_tac >>
      fs[stackSemTheory.evaluate_def]>>
      fs[code_installed_def] >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        qpat_assum`word_cmp _ _ _ ⇒ _`kall_tac >>
        qpat_assum`¬word_cmp _ _ _ ⇒ _`kall_tac >>
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      fs[GSYM word_cmp_word_cmp] >>
      qmatch_assum_rename_tac`read_reg _ _ = Word w1` >>
      qmatch_assum_rename_tac`reg_imm _ _ = Word w2` >>
      Cases_on`word_cmp cmp (Word w1) (Word w2)`>>fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      reverse(Cases_on`x`)>>fs[] >- (
        rpt var_eq_tac >> simp[] >>
        simp[get_pc_value_def] >>
        imp_res_tac code_installed_append_imp >>
        fs[code_installed_def] >>
        simp[dec_clock_def,ADD1,upd_pc_def] >>
        qpat_abbrev_tac`pc = LENGTH _ + _` >>
        drule state_rel_with_pc >> strip_tac >>
        first_x_assum drule >>
        simp[good_syntax_def,next_lab_def] >>
        simp[upd_pc_def] >> strip_tac >>
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      fs[Q.SPEC`If _ _ _ _ _`next_lab_def] >>
      drule (GEN_ALL state_rel_with_pc) >>
      disch_then(qspec_then`t1.pc+1`strip_assume_tac) >>
      first_x_assum drule >>
      fs[good_syntax_def] >>
      imp_res_tac code_installed_append_imp >>
      disch_then(qspecl_then[`n`,`l`]mp_tac)>>simp[] >>
      strip_tac >>
      simp[dec_clock_def,ADD1] >>
      fs[inc_pc_def,upd_pc_def] >>
      Cases_on`r`>>fs[] >- (
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>fs[FILTER_APPEND] ) >>
      CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[dec_clock_def,inc_pc_def] >>
      qexists_tac`ck`>>simp[] >>
      qexists_tac`t2`>>simp[]) >>
    Cases_on`no_ret c1`>>fs[] >- (
      fs[code_installed_def] >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        qpat_assum`word_cmp _ _ _ ⇒ _`kall_tac >>
        qpat_assum`¬word_cmp _ _ _ ⇒ _`kall_tac >>
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      fs[GSYM word_cmp_word_cmp] >>
      qmatch_assum_rename_tac`read_reg _ _ = Word w1` >>
      qmatch_assum_rename_tac`reg_imm _ _ = Word w2` >>
      Cases_on`word_cmp cmp (Word w1) (Word w2)`>>fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      (Cases_on`x`)>>fs[] >- (
        `IS_SOME r` by metis_tac[no_ret_correct,FST] >>
        fs[IS_SOME_EXISTS] >>
        rpt var_eq_tac >> simp[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        simp[get_pc_value_def] >>
        imp_res_tac code_installed_append_imp >>
        imp_res_tac code_installed_append_imp >>
        fs[code_installed_def] >>
        simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
        drule (GEN_ALL state_rel_with_pc) >>
        disch_then(qspec_then`t1.pc+1`mp_tac) >>
        strip_tac >>
        first_x_assum drule >>
        fs[good_syntax_def] >>
        disch_then(qspecl_then[`n`,`l`]mp_tac)>>simp[] >>
        fs[Q.SPEC`If _ _ _ _ _ `next_lab_def] >>
        simp[upd_pc_def] >> strip_tac >>
        CASE_TAC >> fs[] >- (
          qexists_tac`ck+1`>>simp[] >>
          qexists_tac`t2`>>simp[] ) >>
        qexists_tac`ck+1`>>simp[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        simp[inc_pc_def,dec_clock_def] >>
        qexists_tac`t2`>>simp[]) >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      simp[get_pc_value_def] >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      fs[code_installed_def] >>
      simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
      qpat_abbrev_tac`pc = LENGTH _ + _` >>
      drule state_rel_with_pc >> strip_tac >>
      first_x_assum drule >>
      fs[good_syntax_def] >>
      fs[Q.SPEC`If _ _ _ _ _ `next_lab_def] >>
      disch_then(qspecl_then[`n`,`m'`]mp_tac)>>simp[] >>
      fs[FILTER_APPEND] >>
      fsrw_tac[ARITH_ss][] >>
      strip_tac >>
      fs[upd_pc_def] >>
      CASE_TAC >> fs[] >>
      TRY CASE_TAC >> fs[] >- (
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[get_pc_value_def,upd_pc_def,dec_clock_def] >>
      qexists_tac`ck`>>simp[]>>
      qexists_tac`t2`>>simp[] ) >>
    Cases_on`no_ret c2`>>fs[] >- (
      fs[code_installed_def] >>
      `get_var r1 s = SOME (read_reg r1 t1) ∧
       get_var_imm ri s = SOME (reg_imm ri t1)` by (
        qpat_assum`word_cmp _ _ _ ⇒ _`kall_tac >>
        qpat_assum`¬word_cmp _ _ _ ⇒ _`kall_tac >>
        fs[state_rel_def] >>
        Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
      rfs[] >>
      ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
      fs[GSYM word_cmp_word_cmp] >>
      qmatch_assum_rename_tac`read_reg _ _ = Word w1` >>
      qmatch_assum_rename_tac`reg_imm _ _ = Word w2` >>
      Cases_on`word_cmp cmp (Word w1) (Word w2)`>>fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      reverse (Cases_on`x`)>>fs[] >- (
        `IS_SOME r` by metis_tac[no_ret_correct,FST] >>
        fs[IS_SOME_EXISTS] >>
        rpt var_eq_tac >> simp[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        simp[get_pc_value_def] >>
        imp_res_tac code_installed_append_imp >>
        imp_res_tac code_installed_append_imp >>
        fs[code_installed_def] >>
        simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
        drule (GEN_ALL state_rel_with_pc) >>
        disch_then(qspec_then`t1.pc+1`mp_tac) >>
        strip_tac >>
        first_x_assum drule >>
        fs[good_syntax_def] >>
        disch_then(qspecl_then[`n`,`m'`]mp_tac)>>simp[] >>
        fs[Q.SPEC`If _ _ _ _ _ `next_lab_def] >>
        simp[upd_pc_def] >> strip_tac >>
        CASE_TAC >> fs[] >- (
          qexists_tac`ck+1`>>simp[] >>
          qexists_tac`t2`>>simp[] ) >>
        qexists_tac`ck+1`>>simp[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
        simp[inc_pc_def,dec_clock_def] >>
        qexists_tac`t2`>>simp[]) >>
      Ho_Rewrite.ONCE_REWRITE_TAC[EXISTS_NUM] >> disj2_tac >>
      simp[get_pc_value_def] >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      fs[code_installed_def] >>
      simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
      qpat_abbrev_tac`pc = LENGTH _ + _` >>
      drule state_rel_with_pc >> strip_tac >>
      first_x_assum drule >>
      fs[good_syntax_def] >>
      fs[Q.SPEC`If _ _ _ _ _ `next_lab_def] >>
      disch_then(qspecl_then[`n`,`l`]mp_tac)>>simp[] >>
      fs[FILTER_APPEND] >>
      fsrw_tac[ARITH_ss][] >>
      strip_tac >>
      fs[upd_pc_def] >>
      CASE_TAC >> fs[] >>
      TRY CASE_TAC >> fs[] >- (
        qexists_tac`ck`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[get_pc_value_def,upd_pc_def,dec_clock_def] >>
      qexists_tac`ck`>>simp[]>>
      qexists_tac`t2`>>simp[] ) >>
    fs[code_installed_def] >>
    `get_var r1 s = SOME (read_reg r1 t1) ∧
     get_var_imm ri s = SOME (reg_imm ri t1)` by (
      qpat_assum`word_cmp _ _ _ ⇒ _`kall_tac >>
      qpat_assum`¬word_cmp _ _ _ ⇒ _`kall_tac >>
      fs[state_rel_def] >>
      Cases_on`ri`>>fs[get_var_def,get_var_imm_def] ) >>
    rfs[] >>
    ntac 2 (pop_assum (mp_tac o SYM)) >> ntac 2 strip_tac >>
    fs[GSYM word_cmp_word_cmp] >>
    qmatch_assum_rename_tac`read_reg _ _ = Word w1` >>
    qmatch_assum_rename_tac`reg_imm _ _ = Word w2` >>
    Cases_on`word_cmp cmp (Word w1) (Word w2)`>>fs[] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    Cases_on`x`>>fs[] >- (
      simp[get_pc_value_def] >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      imp_res_tac code_installed_append_imp >>
      fs[code_installed_def] >>
      simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
      qpat_abbrev_tac`pc = LENGTH _ + _` >>
      drule state_rel_with_pc >> strip_tac >>
      first_x_assum drule >>
      fs[good_syntax_def] >>
      fs[Q.SPEC`If _ _ _ _ _ `next_lab_def] >>
      disch_then(qspecl_then[`n`,`l`]mp_tac)>>simp[] >>
      fs[FILTER_APPEND] >>
      fsrw_tac[ARITH_ss][] >>
      strip_tac >>
      fs[upd_pc_def] >>
      CASE_TAC >> fs[] >>
      TRY CASE_TAC >> fs[] >- (
        qexists_tac`ck+1`>>simp[] >>
        qexists_tac`t2`>>simp[] >>
        simp[Abbr`pc`,FILTER_APPEND] ) >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[get_pc_value_def,upd_pc_def,dec_clock_def] >>
      qexists_tac`ck+1`>>simp[]>>
      qexists_tac`t2`>>simp[] ) >>
    imp_res_tac code_installed_append_imp >>
    imp_res_tac code_installed_append_imp >>
    imp_res_tac code_installed_append_imp >>
    fs[code_installed_def] >>
    simp[dec_clock_def,ADD1,upd_pc_def,inc_pc_def] >>
    qpat_abbrev_tac`pc = t1.pc + 1` >>
    drule state_rel_with_pc >> strip_tac >>
    first_x_assum drule >>
    fs[good_syntax_def] >>
    fs[Q.SPEC`If _ _ _ _ _ `next_lab_def] >>
    disch_then(qspecl_then[`n`,`m'`]mp_tac)>>simp[] >>
    strip_tac >>
    fs[upd_pc_def] >>
    CASE_TAC >> fs[] >>
    TRY CASE_TAC >> fs[] >- (
      qexists_tac`ck+2`>>simp[] >>
      first_x_assum(strip_assume_tac o CONV_RULE(HO_REWR_CONV FORALL_NUM)) >>
      fsrw_tac[ARITH_ss][ADD1] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[get_pc_value_def,dec_clock_def,upd_pc_def,Abbr`pc`] >>
      qpat_abbrev_tac`pc = LENGTH _ + _` >>
      qexists_tac`upd_pc pc t2`>>simp[upd_pc_def] >>
      simp[Abbr`pc`,FILTER_APPEND] >>
      metis_tac[state_rel_with_pc,upd_pc_def]) >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    simp[get_pc_value_def,upd_pc_def,dec_clock_def,inc_pc_def] >>
    qexists_tac`ck+1`>>simp[]>>
    qexists_tac`t2`>>simp[] ) >>
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
      CASE_TAC >> fs[] >>
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
    BasicProvers.TOP_CASE_TAC>>fs[]>-(
      BasicProvers.TOP_CASE_TAC>>fs[]>>
      BasicProvers.TOP_CASE_TAC>>fs[]>>
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
        `t1.clock = s.clock` by fs[state_rel_def] >>
        CASE_TAC >> fs[] >>
        TRY CASE_TAC >> fs[] >>
        simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
        fs[dec_clock_def,upd_pc_def] >>
        map_every qexists_tac[`ck`,`t2`]>>fs[]>>
        rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
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
      `t1.clock = s.clock` by fs[state_rel_def] >>
      CASE_TAC >> fs[] >>
      TRY CASE_TAC >> fs[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def,get_pc_value_def] >>
      fs[dec_clock_def,upd_pc_def] >>
      map_every qexists_tac[`ck`,`t2`]>>fs[] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[]) >>
    (fn g => subterm split_pair_case_tac (#2 g) g) >>
    var_eq_tac >> fs[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    IF_CASES_TAC >> fs[] >- (
      rw[] >> rw[] >>
      map_every qexists_tac[`0`,`t1`] >>
      fs[] >> fs[state_rel_def,empty_env_def] ) >>
    `t1.clock ≠ 0` by fs[state_rel_def] >>
    (fn g => subterm split_pair_case_tac (#2 g) g) >>
    simp[] >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    split_pair_tac >> fs[] >>
    fs[code_installed_def] >>
    strip_tac >>
    qho_match_abbrev_tac`∃ck t2.
      case r of NONE => P ck t2 r | SOME (Result _) => P ck t2 r | SOME (Halt w) => PH ck t2 w | SOME TimeOut => P ck t2 r
              | SOME (Exception _) => P ck t2 r | SOME Error => P ck t2 r` >>
    `∃ck t2.
      case r of NONE => P ck t2 NONE | SOME (Result zzz) => P ck t2 (SOME (Result zzz))
              | SOME (Halt w) => PH ck t2 w | SOME TimeOut => P ck t2 (SOME TimeOut)
              | SOME (Exception zzz) => P ck t2 (SOME (Exception zzz))
              | SOME Error => P ck t2 (SOME Error)`
    suffices_by (CASE_TAC >> simp[] >> CASE_TAC >> simp[] ) >>
    simp[Abbr`P`,Abbr`PH`] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def,lab_to_loc_def] >>
    fs[good_syntax_def] >> var_eq_tac >>
    simp[inc_pc_def,dec_clock_def,upd_reg_def] >>
    imp_res_tac find_code_lookup >>
    `dest_to_loc (s.regs \\ t1.link_reg) dest = dest_to_loc' t1.regs dest` by (
      EVAL_TAC >>
      CASE_TAC >> fs[] >>
      rator_x_assum`state_rel`mp_tac >>
      simp[DOMSUB_FAPPLY_THM] >>
      simp[state_rel_def,FLOOKUP_DEF] ) >>
    fs[] >>
    first_assum(fn th => first_assum(
      tryfind (strip_assume_tac o C MATCH_MP th) o CONJUNCTS o CONV_RULE (REWR_CONV state_rel_def))) >>
    qpat_abbrev_tac`regs = _ t1.regs` >>
    `loc_to_pc (dest_to_loc' regs dest) 0 t1.code = SOME pc` by (
      ntac 2 (last_x_assum(qspec_then`ARB`kall_tac))>>
      qpat_assum`_ ⇒ ∀x. _`kall_tac >>
      rator_x_assum`loc_to_pc`mp_tac >>
      simp[dest_to_loc'_def] >>
      CASE_TAC >> simp[] >>
      fs[Abbr`regs`,APPLY_UPDATE_THM] ) >>
    drule(GEN_ALL compile_jump_correct) >>
    disch_then drule >>
    strip_tac >>
    qmatch_assum_abbrev_tac`code_installed pc (FST (flatten _ nx lx)) _` >>
    last_x_assum(qspecl_then[`nx`,`lx`,`t1 with <| pc := pc; regs := regs; clock := s.clock-1 |>`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      conj_tac >- ( strip_tac >> fs[] ) >>
      ntac 2 (last_x_assum(qspec_then`ARB`kall_tac)) >>
      qpat_assum`_ ⇒ ∀x. _`kall_tac >>
      fs[state_rel_def,stackSemTheory.dec_clock_def,set_var_def,FLOOKUP_UPDATE] >>
      simp[Abbr`regs`,APPLY_UPDATE_THM] >> rw[] >>
      metis_tac[] ) >>
    strip_tac >>
    `t1.clock = s.clock` by metis_tac[state_rel_def] >>
    Cases_on`r`>>fs[] >- (
      first_x_assum(qspec_then`t1 with <| regs := regs; pc := t1.pc+1; clock := ck + (ck1+t1.clock)|>`
        (mp_tac o Q.GENL[`ck1`,`ck`])) >> simp[] >>
      simp[RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- (
        ntac 2 (last_x_assum(qspec_then`ARB`kall_tac))>>
        qpat_assum`_ ⇒ ∀x. _`kall_tac >>
        qpat_assum`_ _ _ _`kall_tac >>
        qpat_assum`_ = (_,_)`kall_tac >>
        rpt strip_tac >> fs[] >>
        simp[Abbr`regs`,APPLY_UPDATE_THM] >>
        fs[find_code_def,DOMSUB_FLOOKUP_THM] >>
        fs[FLOOKUP_DEF] >>
        fs[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> fs[]) >>
      strip_tac >>
      CONV_TAC(HO_REWR_CONV EXISTS_NUM) >> disj2_tac >>
      simp[ADD1] >> pop_assum kall_tac >>
      simp[dec_clock_def,upd_pc_def] >>
      first_x_assum(fn th => mp_tac th >> BasicProvers.TOP_CASE_TAC) >> fs[] >>
      BasicProvers.TOP_CASE_TAC >> fs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
      rw[] >- (
        qpat_assum`_ = (_,_)`mp_tac >>
        IF_CASES_TAC >> simp[] >>
        BasicProvers.TOP_CASE_TAC >> simp[] >>
        BasicProvers.TOP_CASE_TAC >> simp[] >> rw[] >>
        qpat_assum`¬ _`mp_tac >> simp_tac bool_ss [] >> strip_tac >> rveq >>
        rfs[] >>
        first_x_assum drule >>
        simp[] >> fs[] >>
        imp_res_tac code_installed_append_imp >>
        disch_then(qspecl_then[`n`,`l`]mp_tac)>>simp[] >>
        strip_tac >>
        Cases_on`handler`>>fs[]>-(
          qexists_tac`ck+ck'` >>
          qexists_tac`t2'` >>
          conj_tac >- (
            gen_tac >>
            first_x_assum(qspec_then`ck1`mp_tac) >>
            first_x_assum(qspec_then`ck'+ck1`mp_tac) >>
            simp[] ) >>
          simp[] >>
          simp[Once flatten_def,ADD1] ) >>
        qexists_tac`ck+ck'+1` >>
        simp[Once flatten_def] >>
        (fn g => subterm (split_pair_case_tac o assert (C free_in (#2 g))) (#2 g) g) >> fs[] >>
        split_pair_tac >> fs[] >>
        fs[code_installed_def] >>
        imp_res_tac code_installed_append_imp >>
        fs[code_installed_def] >>
        simp[ADD1,FILTER_APPEND] >>
        qpat_abbrev_tac`pc3 = LENGTH _ + _` >>
        qexists_tac`t2' with pc := pc3` >> simp[] >>
        conj_tac >- (
          gen_tac >>
          first_x_assum(qspec_then`ck1+1`mp_tac) >>
          first_x_assum(qspec_then`ck1+ck'+1`mp_tac) >>
          simp[] >> rw[] >>
          fsrw_tac[ARITH_ss][] >>
          simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
          simp[get_pc_value_def,upd_pc_def,dec_clock_def,Abbr`pc3`] >>
          qpat_assum`_ = t2.pc`(assume_tac o SYM) >> simp[] ) >>
        imp_res_tac state_rel_with_pc >>
        fs[upd_pc_def] ) >>
      rfs[] >>
      first_x_assum(fn th => mp_tac th >> BasicProvers.TOP_CASE_TAC >> fs[]) >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >> rw[] >> fs[] >>
      split_pair_tac >> fs[] >> rfs[] >>
      imp_res_tac code_installed_append_imp >>
      fsrw_tac[ARITH_ss][code_installed_def] >>
      imp_res_tac code_installed_append_imp >>
      fsrw_tac[ARITH_ss][code_installed_def] >>
      qpat_assum`_ = t2.pc`(assume_tac o SYM) >>
      first_x_assum drule >> simp[] >>
      disch_then(qspecl_then[`n`,`m'`]mp_tac)>>simp[] >>
      strip_tac >>
      simp[Once flatten_def] >>
      simp[FILTER_APPEND,ADD1] >>
      map_every qexists_tac[`ck+ck'`,`t2'`] >>
      simp[] >> gen_tac >>
      first_x_assum(qspec_then`ck1`mp_tac) >>
      first_x_assum(qspec_then`ck1+ck'`mp_tac) >>
      simp[] ) >>
    qpat_assum`_ = (SOME _,_)`mp_tac >>
    rveq >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    TRY (
      strip_tac >> var_eq_tac >> rveq >> simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[upd_reg_def,dec_clock_def,inc_pc_def,lab_to_loc_def] >>
      qexists_tac`ck+1`>>simp[] >>
      qpat_abbrev_tac`ss:('a,'ffi)labSem$state = _ _` >>
      first_x_assum(qspec_then`ss`mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`ss`] >>
        rw[] >> fs[Abbr`regs`,APPLY_UPDATE_THM] >>
        fs[find_code_def,DOMSUB_FLOOKUP_THM] >>
        fs[FLOOKUP_DEF] >>
        fs[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> fs[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
      NO_TAC) >>
    TRY (
      strip_tac >> var_eq_tac >> rveq >> simp[] >>
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[upd_reg_def,dec_clock_def,inc_pc_def,lab_to_loc_def] >>
      qexists_tac`ck+1`>>simp[] >>
      qexists_tac`t2`>>simp[] >>
      gen_tac >>
      qpat_abbrev_tac`ss:('a,'ffi)labSem$state = _ _` >>
      first_x_assum(qspec_then`ss`mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`ss`] >>
        rw[] >> fs[Abbr`regs`,APPLY_UPDATE_THM] >>
        fs[find_code_def,DOMSUB_FLOOKUP_THM] >>
        fs[FLOOKUP_DEF] >>
        fs[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> fs[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
      first_x_assum(qspec_then`ck1`mp_tac)>>simp[] >>
      NO_TAC) >>
    TRY (
      IF_CASES_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] >>
      BasicProvers.TOP_CASE_TAC >> simp[] ) >>
    BasicProvers.TOP_CASE_TAC >> simp[] >>
    strip_tac >> rveq >> fs[] >- (
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[upd_reg_def,dec_clock_def,inc_pc_def,lab_to_loc_def] >>
      qexists_tac`ck+1`>>simp[] >>
      qexists_tac`t2`>>simp[] >>
      gen_tac >>
      qpat_abbrev_tac`ss:('a,'ffi)labSem$state = _ _` >>
      first_x_assum(qspec_then`ss`mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`ss`] >>
        rw[] >> fs[Abbr`regs`,APPLY_UPDATE_THM] >>
        fs[find_code_def,DOMSUB_FLOOKUP_THM] >>
        fs[FLOOKUP_DEF] >>
        fs[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> fs[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
      first_x_assum(qspec_then`ck1`mp_tac)>>simp[] >>
      NO_TAC) >>
    pop_assum mp_tac >>
    (fn g => subterm (split_pair_case_tac o assert (C free_in (#2 g))) (#2 g) g) >> fs[] >>
    IF_CASES_TAC >> simp[] >> strip_tac >> fs[] >>
    rveq >> fs[] >>
    split_pair_tac >> fs[] >>
    imp_res_tac code_installed_append_imp >>
    pop_assum mp_tac >>
    simp_tac(srw_ss()++ARITH_ss)[code_installed_def] >>
    strip_tac >>
    qpat_assum`∀x. (loc_to_pc _ _ _ = _) ⇒ _`mp_tac >>
    simp[] >> strip_tac >> rfs[] >>
    first_x_assum drule >>
    disch_then(qspecl_then[`n`,`m'`]mp_tac)>>simp[] >>
    discharge_hyps >- (
      qpat_assum`_ = t2.pc`(assume_tac o SYM) >>
      imp_res_tac code_installed_append_imp >>
      fs[code_installed_def] ) >>
    strip_tac >>
    BasicProvers.TOP_CASE_TAC >> fs[] >>
    TRY (
      simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
      simp[upd_reg_def,dec_clock_def,inc_pc_def,lab_to_loc_def] >>
      map_every qexists_tac[`ck+ck'+1`,`t2'`] >> simp[] >>
      gen_tac >>
      qpat_abbrev_tac`ss:('a,'ffi)labSem$state = _ _` >>
      first_x_assum(qspec_then`ss`mp_tac) >>
      discharge_hyps >- (
        simp[Abbr`ss`] >>
        rw[] >> fs[Abbr`regs`,APPLY_UPDATE_THM] >>
        fs[find_code_def,DOMSUB_FLOOKUP_THM] >>
        fs[FLOOKUP_DEF] >>
        fs[state_rel_def,FLOOKUP_DEF] >>
        every_case_tac >> fs[]) >>
      simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
      strip_tac >>
      last_x_assum(qspec_then`ck1+ck'`mp_tac) >>
      last_x_assum(qspec_then`ck1+ck'`mp_tac) >>
      simp[] >> NO_TAC ) >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    simp[upd_reg_def,dec_clock_def,inc_pc_def,lab_to_loc_def] >>
    map_every qexists_tac[`ck+ck'+1`,`t2'`] >> simp[] >>
    qpat_abbrev_tac`ss:('a,'ffi)labSem$state = _ _` >>
    first_x_assum(qspec_then`ss`mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`ss`] >>
      rw[] >> fs[Abbr`regs`,APPLY_UPDATE_THM] >>
      fs[find_code_def,DOMSUB_FLOOKUP_THM] >>
      fs[FLOOKUP_DEF] >>
      fs[state_rel_def,FLOOKUP_DEF] >>
      every_case_tac >> fs[]) >>
    simp[upd_pc_def,dec_clock_def,Abbr`ss`] >>
    strip_tac >>
    last_x_assum(qspec_then`ck'`mp_tac) >>
    last_x_assum(qspec_then`ck'`mp_tac) >>
    simp[]) >>
  (* FFI *)
  conj_tac >- (
    rw[stackSemTheory.evaluate_def,flatten_def] >>
    Cases_on`get_var ptr s`>>fs[]>>Cases_on`x`>>fs[]>>
    Cases_on`get_var len s`>>fs[]>>Cases_on`x`>>fs[]>>
    last_x_assum mp_tac >> CASE_TAC >> simp[] >>
    split_pair_tac >> simp[] >> rw[] >> simp[] >>
    fs[code_installed_def,good_syntax_def] >>
    qexists_tac`2` >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def] >>
    rpt var_eq_tac >>
    simp[lab_to_loc_def] >>
    simp[Once labSemTheory.evaluate_def,asm_fetch_def,upd_reg_def,dec_clock_def,inc_pc_def,APPLY_UPDATE_THM] >>
    IF_CASES_TAC >- fs[state_rel_def] >>
    IF_CASES_TAC >- fs[state_rel_def] >>
    `get_var t1.ptr_reg s = SOME (read_reg t1.ptr_reg t1) ∧
     get_var t1.len_reg s = SOME (read_reg t1.len_reg t1)` by (
      fs[state_rel_def,get_var_def] >> res_tac >> fs[] ) >>
    fs[] >>
    `s.memory = t1.mem ∧ s.mdomain = t1.mem_domain ∧ s.be = t1.be` by fs[state_rel_def] >>
    fs[] >>
    split_pair_tac >> fs[] >>
    (fn g => subterm (fn tm => qexists_tac `^tm with <| clock := t1.clock|>` g) (#2 g)) >> simp[] >>
    fs[state_rel_def,FLOOKUP_DRESTRICT] >> rfs[] >>
    reverse conj_tac
    >- (fs [targetSemTheory.shift_seq_def] >>
        rw [] >> res_tac >> fs []) >>
    rpt strip_tac >>
    qmatch_assum_rename_tac `FLOOKUP s.regs k = SOME v` >>
    res_tac >>
    Cases_on `t1.io_regs 0 k` >> fs [get_reg_value_def] >>
    rw [] >> fs []) >>
  conj_tac >-
   (rw[stackSemTheory.evaluate_def]
    \\ fs [flatten_def,code_installed_def]
    \\ simp [Once evaluate_def] \\ qexists_tac `1`
    \\ fs [asm_fetch_def,lab_to_loc_def]
    \\ fs [inc_pc_def,dec_clock_def,upd_reg_def]
    \\ (fn g => subterm (fn tm =>
         qexists_tac `^tm with <| clock := t1.clock|>` g) (#2 g))
    \\ fs [state_rel_def,set_var_def,FLOOKUP_UPDATE,APPLY_UPDATE_THM]
    \\ rw [] \\ res_tac) >>
  rw[stackSemTheory.evaluate_def] >>
  fs[state_rel_def]);

val _ = export_theory();
