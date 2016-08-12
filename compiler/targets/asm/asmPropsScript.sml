open preamble asmSemTheory

val () = new_theory "asmProps"

(* -- semantics is deterministic -- *)

val asm_deterministic = Q.store_thm("asm_deterministic",
  `!c i s1 s2 s3. asm_step c s1 i s2 /\ asm_step c s1 i s3 ==> (s2 = s3)`,
  rw [asm_step_def])

val bytes_in_memory_concat = Q.store_thm("bytes_in_memory_concat",
  `!l1 l2 pc mem mem_domain.
      bytes_in_memory pc (l1 ++ l2) mem mem_domain =
      bytes_in_memory pc l1 mem mem_domain /\
      bytes_in_memory (pc + n2w (LENGTH l1)) l2 mem mem_domain`,
  Induct
  THEN ASM_SIMP_TAC list_ss
         [bytes_in_memory_def, wordsTheory.WORD_ADD_0, wordsTheory.word_add_n2w,
          GSYM wordsTheory.WORD_ADD_ASSOC, arithmeticTheory.ADD1]
  THEN DECIDE_TAC
  )

(* -- well-formedness of encoding -- *)

val offset_monotonic_def = Define `
  offset_monotonic enc c a1 a2 i1 i2 =
  asm_ok i1 c /\ asm_ok i2 c ==>
  (0w <= a1 /\ 0w <= a2 /\ a1 <= a2 ==> LENGTH (enc i1) <= LENGTH (enc i2)) /\
  (a1 < 0w /\ a2 < 0w /\ a2 <= a1 ==> LENGTH (enc i1) <= LENGTH (enc i2))`

val enc_ok_def = Define `
  enc_ok (c : 'a asm_config) =
    (* code alignment and length *)
    (2 EXP c.code_alignment = LENGTH (c.encode (Inst Skip))) /\
    (!w. asm_ok w c ==> (LENGTH (c.encode w) MOD 2 EXP c.code_alignment = 0) /\
                        (LENGTH (c.encode w) <> 0)) /\
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
    <| get_pc : 'b -> 'a word
     ; get_reg : 'b -> num -> 'a word
     ; get_byte : 'b -> 'a word -> word8
     ; state_ok : 'b -> bool
     ; state_rel : 'a asm_state -> 'b -> bool
     ; proj : 'a word set -> 'b -> 'c
     ; next : 'b -> 'b
     ; config : 'a asm_config
     |>`

val interference_ok_def = Define `
  interference_ok env proj <=> !i:num ms. proj (env i ms) = proj ms`;

val all_pcs_def = Define `
  (all_pcs 0 a = {}) /\
  (all_pcs (SUC n) a = a INSERT all_pcs n (a + 1w))`

val asserts_def = zDefine `
  (asserts 0 next ms _ Q <=> Q (next 0 ms)) /\
  (asserts (SUC n) next ms P Q <=>
     let ms' = next (SUC n) ms in P ms' /\ asserts n next ms' P Q)`

val backend_correct_def = Define `
  backend_correct t <=>
    enc_ok t.config /\
    (!ms1 ms2 s.
        (t.proj s.mem_domain ms1 = t.proj s.mem_domain ms2) ==>
        (t.state_rel s ms1 = t.state_rel s ms2) /\
        (t.state_ok ms1 = t.state_ok ms2)) /\
    (!ms s. t.state_rel s ms ==>
            t.state_ok ms /\ (t.get_pc ms = s.pc) /\
            (!a. a IN s.mem_domain ==> (t.get_byte ms a = s.mem a)) /\
            (!i. i < t.config.reg_count /\ ~MEM i t.config.avoid_regs ==>
                 (t.get_reg ms i = s.regs i))) /\
    !s1 i s2 ms.
      asm_step t.config s1 i s2 /\ t.state_rel s1 ms ==>
      ?n. !env.
            interference_ok (env:num->'b->'b) (t.proj s1.mem_domain) ==>
            asserts n (\k s. env (n - k) (t.next s)) ms
              (\ms'. t.state_ok ms' /\
                     t.get_pc ms' IN all_pcs (LENGTH (t.config.encode i)) s1.pc)
              (\ms'. t.state_rel s2 ms')`

(* lemma for proofs *)

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

val bytes_in_memory_APPEND = Q.store_thm("bytes_in_memory_APPEND",
  `!bs bs1 p.
     bytes_in_memory p (bs ++ bs1) m dm <=>
     bytes_in_memory p bs m dm /\
     bytes_in_memory (p + n2w (LENGTH bs)) bs1 m dm`,
  Induct \\ fs [bytes_in_memory_def,ADD1,word_add_n2w]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w,CONJ_ASSOC])

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

val asm_failed_ignore_new_pc = store_thm("asm_failed_ignore_new_pc",
  ``!i v w s. (asm i w s).failed <=> (asm i v s).failed``,
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val asm_mem_ignore_new_pc = store_thm("asm_mem_ignore_new_pc",
  ``!i v w s. (asm i w s).mem = (asm i v s).mem``,
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val SND_read_mem_word_consts = prove(
  ``!n a s. ((SND (read_mem_word a n s)).be = s.be) /\
            ((SND (read_mem_word a n s)).lr = s.lr) /\
            ((SND (read_mem_word a n s)).align = s.align) /\
            ((SND (read_mem_word a n s)).mem_domain = s.mem_domain)``,
  Induct \\ full_simp_tac(srw_ss())[read_mem_word_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[assert_def])

val write_mem_word_consts = prove(
  ``!n a w s. ((write_mem_word a n w s).be = s.be) /\
              ((write_mem_word a n w s).lr = s.lr) /\
              ((write_mem_word a n w s).align = s.align) /\
              ((write_mem_word a n w s).mem_domain = s.mem_domain)``,
  Induct \\ full_simp_tac(srw_ss())[write_mem_word_def,LET_DEF,assert_def,upd_mem_def])

val asm_consts = store_thm("asm_consts[simp]",
  ``!i w s. ((asm i w s).be = s.be) /\
            ((asm i w s).lr = s.lr) /\
            ((asm i w s).align = s.align) /\
            ((asm i w s).mem_domain = s.mem_domain)``,
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
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
