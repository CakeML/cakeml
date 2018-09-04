open preamble asmSemTheory

val () = new_theory "asmProps"

(* -- semantics is deterministic -- *)

val asm_deterministic = Q.store_thm("asm_deterministic",
  `!c i s1 s2 s3. asm_step c s1 i s2 /\ asm_step c s1 i s3 ==> (s2 = s3)`,
  rw [asm_step_def])

(* -- well-formedness of encoding -- *)

val offset_monotonic_def = Define `
  offset_monotonic enc c a1 a2 i1 i2 <=>
  asm_ok i1 c /\ asm_ok i2 c ==>
  (0w <= a1 /\ 0w <= a2 /\ a1 <= a2 ==> LENGTH (enc i1) <= LENGTH (enc i2)) /\
  (a1 < 0w /\ a2 < 0w /\ a2 <= a1 ==> LENGTH (enc i1) <= LENGTH (enc i2))`

val enc_ok_def = Define `
  enc_ok (c : 'a asm_config) <=>
    (* code alignment and length *)
    (2 EXP c.code_alignment = LENGTH (c.encode (Inst Skip))) /\
    (!w. (LENGTH (c.encode w) MOD 2 EXP c.code_alignment = 0) /\
          LENGTH (c.encode w) <> 0) /\
    (* label instantiation predictably affects length of code *)
    (!w1 w2. offset_monotonic c.encode c w1 w2 (Jump w1) (Jump w2)) /\
    (!cmp r ri w1 w2.
       offset_monotonic c.encode c w1 w2
          (JumpCmp cmp r ri w1) (JumpCmp cmp r ri w2)) /\
    (!w1 w2. offset_monotonic c.encode c w1 w2 (Call w1) (Call w2)) /\
    (!w1 w2 r. offset_monotonic c.encode c w1 w2 (Loc r w1) (Loc r w2))`

(* -- correctness property to be proved for each backend -- *)

val () = Datatype `
  target =
    <| config : 'a asm_config
     ; next : 'b -> 'b
     ; get_pc : 'b -> 'a word
     ; get_reg : 'b -> num -> 'a word
     ; get_fp_reg : 'b -> num -> word64
     ; get_byte : 'b -> 'a word -> word8
     ; state_ok : 'b -> bool
     ; proj : 'a word set -> 'b -> 'c
     |>`

val target_state_rel_def = Define`
  target_state_rel t s ms <=>
  t.state_ok ms /\ (t.get_pc ms = s.pc) /\
  (!a. a IN s.mem_domain ==> (t.get_byte ms a = s.mem a)) /\
  (!i. i < t.config.reg_count /\ ~MEM i t.config.avoid_regs ==>
       (t.get_reg ms i = s.regs i)) /\
  (!i. i < t.config.fp_reg_count ==> (t.get_fp_reg ms i = s.fp_regs i))`

val target_ok_def = Define`
  target_ok t <=>
  enc_ok t.config /\
  !ms1 ms2 s.
    (t.proj s.mem_domain ms1 = t.proj s.mem_domain ms2) ==>
    (target_state_rel t s ms1 = target_state_rel t s ms2) /\
    (t.state_ok ms1 = t.state_ok ms2) /\
    (t.get_pc ms1 = t.get_pc ms2) /\
    (!a. a IN s.mem_domain ==> t.get_byte ms1 a = t.get_byte ms2 a)`

val interference_ok_def = Define `
  interference_ok env proj <=> !i:num ms. proj (env i ms) = proj ms`;

val all_pcs_def = Define`
  (all_pcs 0n a k = {}) ∧
  (all_pcs n a k = a INSERT all_pcs (n-(2 ** k)) (a + n2w (2 ** k)) k)`

val all_pcs_thm = Q.store_thm("all_pcs_thm",
  `all_pcs n a k = { a + n2w (i * (2 ** k)) | i | i * (2 ** k) < n }`,
  qid_spec_tac`a`
  \\ qid_spec_tac`k`
  \\ completeInduct_on`n`
  \\ Cases_on`n` \\ rw[all_pcs_def]
  \\ rw[EXTENSION]
  \\ Cases_on`a = x` \\ fs[]
  >- ( qexists_tac`0` \\ fs[] )
  \\ rewrite_tac[word_add_n2w,GSYM WORD_ADD_ASSOC,GSYM ADD1]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`SUC i` \\ simp[ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB] )
  \\ qexists_tac`i-1`
  \\ Cases_on`i` \\ fs[ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]);

val asserts_def = zDefine `
  (asserts 0 next ms _ Q <=> Q (next 0 ms)) /\
  (asserts (SUC n) next ms P Q <=>
     let ms' = next (SUC n) ms in P ms' /\ asserts n next ms' P Q)`

val backend_correct_def = Define `
  backend_correct t <=>
    target_ok t /\
    !s1 i s2 ms.
      asm_step t.config s1 i s2 /\ target_state_rel t s1 ms ==>
      ?n. !env.
            interference_ok (env:num->'b->'b) (t.proj s1.mem_domain) ==>
            let pcs = all_pcs (LENGTH (t.config.encode i)) s1.pc in
            asserts n (\k s. env (n - k) (t.next s)) ms
              (\ms'. t.state_ok ms' /\
                     (∀pc. pc ∈ pcs 0 ⇒ t.get_byte ms' pc = t.get_byte ms pc) ∧
                     t.get_pc ms' IN pcs t.config.code_alignment)
              (\ms'. target_state_rel t s2 ms')`

(* lemma for proofs *)

val bytes_in_memory_APPEND = Q.store_thm("bytes_in_memory_APPEND",
  `!l1 l2 pc mem mem_domain.
      bytes_in_memory pc (l1 ++ l2) mem mem_domain <=>
      bytes_in_memory pc l1 mem mem_domain /\
      bytes_in_memory (pc + n2w (LENGTH l1)) l2 mem mem_domain`,
  Induct
  THEN ASM_SIMP_TAC list_ss
         [bytes_in_memory_def, wordsTheory.WORD_ADD_0, wordsTheory.word_add_n2w,
          GSYM wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD1]
  THEN DECIDE_TAC
  )

val bytes_in_memory_all_pcs = Q.store_thm("bytes_in_memory_all_pcs",
  `!xs pc. bytes_in_memory pc xs m d ==> all_pcs (LENGTH xs) pc k SUBSET d`,
  gen_tac
  \\ completeInduct_on`LENGTH xs`
  \\ rw[]
  \\ fs[all_pcs_thm]
  \\ fs[SUBSET_DEF, PULL_EXISTS, PULL_FORALL] \\ rw[]
  \\ Cases_on`i=0` \\ fs[]
  >- ( Cases_on`xs` \\ fs[bytes_in_memory_def] )
  \\ Cases_on`2 ** k < LENGTH xs`
  >- (
    first_x_assum(qspec_then`DROP (2 ** k) xs`mp_tac)
    \\ simp[]
    \\ Q.ISPECL_THEN[`TAKE (2 ** k) xs`,`DROP (2 ** k) xs`]mp_tac bytes_in_memory_APPEND
    \\ simp[]
    \\ disch_then(drule o #1 o EQ_IMP_RULE o SPEC_ALL)
    \\ strip_tac
    \\ disch_then drule
    \\ disch_then(qspec_then`i-1`mp_tac)
    \\ simp[LEFT_SUB_DISTRIB, RIGHT_SUB_DISTRIB]
    \\ rewrite_tac[GSYM WORD_ADD_ASSOC]
    \\ rewrite_tac[word_add_n2w]
    \\ simp[SUB_LEFT_ADD, SUB_RIGHT_ADD]
    \\ IF_CASES_TAC \\ fs[]
    \\ `i = 1` by fs[] \\ fs[] )
  \\ Cases_on`i` \\ fs[ADD1, RIGHT_ADD_DISTRIB]);

val bytes_in_memory_change_domain = Q.store_thm("bytes_in_memory_change_domain",
  `∀a bs m md1 md2.
    bytes_in_memory a bs m md1 ∧
   (∀n. n < LENGTH bs ⇒ (a + n2w n ∈ md1 ⇔ a + n2w n ∈ md2))
  ⇒ bytes_in_memory a bs m md2`,
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[ADD1,GSYM word_add_n2w]);

val bytes_in_memory_change_mem = Q.store_thm("bytes_in_memory_change_mem",
  `∀a bs m1 m2 md.
    bytes_in_memory a bs m1 md ∧
   (∀n. n < LENGTH bs ⇒ (m1 (a + n2w n) = m2 (a + n2w n)))
  ⇒ bytes_in_memory a bs m2 md`,
  Induct_on`bs`
  \\ rw[bytes_in_memory_def]
  >- ( first_x_assum(qspec_then`0`mp_tac) \\ rw[] )
  \\ first_x_assum irule
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ strip_tac
  \\ first_x_assum(qspec_then`SUC n`mp_tac)
  \\ simp[ADD1,GSYM word_add_n2w]);

val sym_target_state_rel_def = Q.store_thm("sym_target_state_rel",
  `!t s ms.
     target_state_rel t s ms <=>
     t.state_ok ms /\ (s.pc = t.get_pc ms) /\
     (!a. a IN s.mem_domain ==> (s.mem a = t.get_byte ms a)) /\
     (!i. i < t.config.reg_count /\ ~MEM i t.config.avoid_regs ==>
          (s.regs i = t.get_reg ms i)) /\
     (!i. i < t.config.fp_reg_count ==> (s.fp_regs i = t.get_fp_reg ms i))`,
  metis_tac [target_state_rel_def]
  )

val all_pcs = Theory.save_thm ("all_pcs", numLib.SUC_RULE all_pcs_def)

val asserts_eval = save_thm("asserts_eval",let
  fun genlist f 0 = []
    | genlist f n = genlist f (n-1) @ [f (n-1)]
  fun suc_num 0 = ``0:num``
    | suc_num n = mk_comb(``SUC``,suc_num (n-1))
  fun gen_rw n =
    ``asserts ^(suc_num n) next (s:'a) P Q``
    |> ONCE_REWRITE_CONV [asserts_def] |> SIMP_RULE std_ss []
  in LIST_CONJ (genlist gen_rw 20) end)

val asserts_IMP_FOLDR_COUNT_LIST = Q.store_thm("asserts_IMP_FOLDR_COUNT_LIST",
  `∀n next ms P Q. asserts n next ms P Q ⇒
      Q (FOLDR next (next n ms) (COUNT_LIST n))`,
  Induct
  >- rw[COUNT_LIST_def, asserts_def]
  \\ rw[asserts_def]
  \\ rw[COUNT_LIST_SNOC, FOLDR_SNOC]
  \\ first_x_assum drule \\ rw[]);

val asserts_IMP_FOLDR_COUNT_LIST_LESS = Q.store_thm("asserts_IMP_FOLDR_COUNT_LIST_LESS",
  `∀k n next ms P Q. asserts n next ms P Q ∧ k < n ⇒
      P (FOLDR next ms (REVERSE (GENLIST ((-) n) (SUC k))))`,
  simp[GSYM MAP_COUNT_LIST]
  \\ Induct_on`k` \\ rw[]
  \\ Cases_on`n` \\ fs[asserts_def]
  >- (EVAL_TAC \\ fs[])
  \\ first_x_assum drule
  \\ simp[]
  \\ simp[COUNT_LIST_GENLIST,MAP_GENLIST,REVERSE_GENLIST,GENLIST_CONS,PRE_SUB1,FOLDR_APPEND]);

val upd_pc_simps = Q.store_thm("upd_pc_simps[simp]",
  `((asmSem$upd_pc x s).align = s.align) ∧
   ((asmSem$upd_pc x s).mem_domain = s.mem_domain) ∧
   ((asmSem$upd_pc x s).failed = s.failed) ∧
   ((asmSem$upd_pc x s).be = s.be) ∧
   ((asmSem$upd_pc x s).mem = s.mem) ∧
   ((asmSem$upd_pc x s).regs = s.regs) ∧
   ((asmSem$upd_pc x s).fp_regs = s.fp_regs) ∧
   ((asmSem$upd_pc x s).lr = s.lr) ∧
   ((asmSem$upd_pc x s).pc = x)`,
  EVAL_TAC);

val asm_failed_ignore_new_pc = Q.store_thm("asm_failed_ignore_new_pc",
  `!i v w s. (asm i w s).failed <=> (asm i v s).failed`,
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val asm_mem_ignore_new_pc = Q.store_thm("asm_mem_ignore_new_pc",
  `!i v w s. (asm i w s).mem = (asm i v s).mem`,
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val SND_read_mem_word_consts = Q.prove(
  `!n a s. ((SND (read_mem_word a n s)).be = s.be) /\
            ((SND (read_mem_word a n s)).lr = s.lr) /\
            ((SND (read_mem_word a n s)).align = s.align) /\
            ((SND (read_mem_word a n s)).mem_domain = s.mem_domain)`,
  Induct \\ full_simp_tac(srw_ss())[read_mem_word_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[assert_def])

val write_mem_word_consts = Q.prove(
  `!n a w s. ((write_mem_word a n w s).be = s.be) /\
              ((write_mem_word a n w s).lr = s.lr) /\
              ((write_mem_word a n w s).align = s.align) /\
              ((write_mem_word a n w s).mem_domain = s.mem_domain)`,
  Induct \\ full_simp_tac(srw_ss())[write_mem_word_def,LET_DEF,assert_def,upd_mem_def])

val binop_upd_consts = Q.store_thm("binop_upd_consts[simp]",
  `((binop_upd a b c d x).mem_domain = x.mem_domain) ∧
   ((binop_upd a b c d x).align = x.align) ∧
   ((binop_upd a b c d x).failed = x.failed) ∧
   ((binop_upd a b c d x).mem = x.mem) ∧
   ((binop_upd a b c d x).lr = x.lr) ∧
   ((binop_upd a b c d x).be = x.be)`,
  Cases_on`b`>>EVAL_TAC);

val arith_upd_consts = Q.store_thm("arith_upd_consts[simp]",
  `((arith_upd a x).mem_domain = x.mem_domain) ∧
   ((arith_upd a x).align = x.align) ∧
   ((arith_upd a x).mem = x.mem) ∧
   ((arith_upd a x).lr = x.lr) ∧
   ((arith_upd a x).be = x.be)`,
  Cases_on`a` >> EVAL_TAC >> srw_tac[][]);

val fp_upd_consts = Q.store_thm("fp_upd_consts[simp]",
  `((fp_upd a x).mem_domain = x.mem_domain) ∧
   ((fp_upd a x).align = x.align) ∧
   ((fp_upd a x).mem = x.mem) ∧
   ((fp_upd a x).lr = x.lr) ∧
   ((fp_upd a x).be = x.be)`,
  Cases_on`a`
  \\ rpt (EVAL_TAC \\ srw_tac[][] \\ CASE_TAC \\ rw []));

val asm_consts = Q.store_thm("asm_consts[simp]",
  `!i w s. ((asm i w s).be = s.be) /\
            ((asm i w s).lr = s.lr) /\
            ((asm i w s).align = s.align) /\
            ((asm i w s).mem_domain = s.mem_domain)`,
  Cases
  \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ TRY (Cases_on `i'`) \\ full_simp_tac(srw_ss())[inst_def]
  \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ TRY (Cases_on `m`)
  \\ TRY (Cases_on `a`) \\ full_simp_tac(srw_ss())[arith_upd_def,mem_op_def]
  \\ TRY (Cases_on `b`)
  \\ TRY (Cases_on `r`)
  \\ EVAL_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[SND_read_mem_word_consts,write_mem_word_consts])

val () = export_theory ()
