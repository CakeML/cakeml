(*
  Proofs of general properties of the asm language
*)
open preamble asmSemTheory

val () = new_theory "asmProps"

(* -- semantics is deterministic -- *)

Theorem asm_deterministic:
   !c i s1 s2 s3. asm_step c s1 i s2 /\ asm_step c s1 i s3 ==> (s2 = s3)
Proof
  rw [asm_step_def]
QED

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

Theorem all_pcs_thm:
   all_pcs n a k = { a + n2w (i * (2 ** k)) | i | i * (2 ** k) < n }
Proof
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
  \\ Cases_on`i` \\ fs[ADD1,LEFT_ADD_DISTRIB,RIGHT_ADD_DISTRIB]
QED

val asserts_def = zDefine `
  (asserts 0 next ms _ Q <=> Q (next 0 ms)) /\
  (asserts (SUC n) next ms P Q <=>
     let ms' = next (SUC n) ms in P ms' /\ asserts n next ms' P Q)`

val asserts2_def = zDefine`
  (asserts2 n fi fc ms P =
   if n = 0n then T else
     P ms (fc ms) ∧
     asserts2 (n-1) fi fc (fi n (fc ms)) P)`;

val encoder_correct_def = Define `
  encoder_correct t <=>
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
              (\ms'. target_state_rel t s2 ms') ∧
            asserts2 (n + 1) (λk. env (n + 1 - k)) t.next ms
              (λms1 ms2. ∀x. x ∉ s1.mem_domain ⇒ t.get_byte ms1 x = t.get_byte ms2 x)`

(* lemma for proofs *)

Theorem bytes_in_memory_all_pcs:
   !xs pc. bytes_in_memory pc xs m d ==> all_pcs (LENGTH xs) pc k SUBSET d
Proof
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
  \\ Cases_on`i` \\ fs[ADD1, RIGHT_ADD_DISTRIB]
QED

Theorem read_bytearray_IMP_bytes_in_memory:
   ∀p n m ba m' md.
   (n = LENGTH ba) ∧
   (∀k. k ∈ all_words p n ⇒ k ∈ md ∧ (m k = SOME (m' k))) ∧
   (read_bytearray (p:'a word) n m = SOME ba) ⇒
   bytes_in_memory p ba m' md
Proof
  Induct_on`ba` \\ rw[] >- EVAL_TAC
  \\ simp[bytes_in_memory_def]
  \\ fs[read_bytearray_def, CaseEq"option"]
  \\ first_assum(qspec_then`p`mp_tac)
  \\ impl_tac >- simp[all_words_def]
  \\ rw[]
  \\ first_x_assum irule
  \\ fs [all_words_def]
  \\ metis_tac []
QED

Theorem sym_target_state_rel:
   !t s ms.
     target_state_rel t s ms <=>
     t.state_ok ms /\ (s.pc = t.get_pc ms) /\
     (!a. a IN s.mem_domain ==> (s.mem a = t.get_byte ms a)) /\
     (!i. i < t.config.reg_count /\ ~MEM i t.config.avoid_regs ==>
          (s.regs i = t.get_reg ms i)) /\
     (!i. i < t.config.fp_reg_count ==> (s.fp_regs i = t.get_fp_reg ms i))
Proof
  metis_tac [target_state_rel_def]
QED

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

Theorem asserts_IMP_FOLDR_COUNT_LIST:
   ∀n next ms P Q. asserts n next ms P Q ⇒
      Q (FOLDR next (next n ms) (COUNT_LIST n))
Proof
  Induct
  >- rw[COUNT_LIST_def, asserts_def]
  \\ rw[asserts_def]
  \\ rw[COUNT_LIST_SNOC, FOLDR_SNOC]
  \\ first_x_assum drule \\ rw[]
QED

Theorem asserts_IMP_FOLDR_COUNT_LIST_LESS:
   ∀k n next ms P Q. asserts n next ms P Q ∧ k < n ⇒
      P (FOLDR next ms (REVERSE (GENLIST ((-) n) (SUC k))))
Proof
  simp[GSYM MAP_COUNT_LIST]
  \\ Induct_on`k` \\ rw[]
  \\ Cases_on`n` \\ fs[asserts_def]
  >- (EVAL_TAC \\ fs[])
  \\ first_x_assum drule
  \\ simp[]
  \\ simp[COUNT_LIST_GENLIST,MAP_GENLIST,REVERSE_GENLIST,GENLIST_CONS,PRE_SUB1,FOLDR_APPEND]
QED

Theorem asserts_WEAKEN:
   !n next s P Q.
      (!k. k <= n ==>
        (next k = next' k) ∧
        (P (FOLDR next s (REVERSE (GENLIST ((-) n) (SUC k)))) ⇒
         P' (FOLDR next s (REVERSE (GENLIST ((-) n) (SUC k)))))) ==>
      asserts n next s P Q ==>
      asserts n next' s P' Q
Proof
  Induct \\ fs[asserts_def]
  \\ rpt gen_tac \\ strip_tac \\ strip_tac
  \\ conj_tac
  >- (
    first_assum(qspec_then`0`mp_tac)
    \\ impl_tac >- fs[]
    \\ first_x_assum(qspec_then`SUC n`mp_tac)
    \\ impl_tac >- fs[]
    \\ rw[] )
  >- (
    first_assum irule
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ ntac 2 strip_tac
    \\ conj_tac
    >- (
      first_assum(qspec_then`k`mp_tac)
      \\ impl_tac >- fs[] \\ rw[] )
    \\ first_assum(qspec_then`SUC k`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp_tac(srw_ss())[GENLIST_CONS, FOLDR_APPEND]
    \\ simp_tac(srw_ss())[o_DEF]
    \\ strip_tac
    \\ first_assum(qspec_then`SUC n`mp_tac)
    \\ impl_tac >- fs[]
    \\ strip_tac \\ fs[] )
QED

val asserts2_eval = save_thm("asserts2_eval",let
  fun gen_rw n =
    ``asserts2 ^(numSyntax.term_of_int n) fi fc (s:'a) P``
    |> ONCE_REWRITE_CONV [asserts2_def] |> SIMP_RULE std_ss []
  in LIST_CONJ (List.tabulate(21,gen_rw)) end)

Theorem asserts2_change_interfer:
   asserts2 n fi fc ms P  ∧
   (∀k. k ≤ n ⇒ fi k = fi2 k)
  ⇒
   asserts2 n fi2 fc ms P
Proof
  qid_spec_tac`ms`
  \\ Induct_on`n`
  \\ rw[Once asserts2_def]
  \\ rw[Once asserts2_def]
  \\ first_x_assum match_mp_tac
  \\ rw[]
  \\ METIS_TAC[LESS_OR_EQ]
QED

Theorem asserts2_first:
   1 ≤ n ∧ asserts2 n fi fc ms P ⇒ P ms (fc ms)
Proof
  rw[Once asserts2_def] \\ fs[]
QED

Theorem asserts2_every:
   ∀n ms j.
   asserts2 n (λk. f) g ms P ∧ j < n ⇒
   P (FUNPOW (f o g) j ms) (g (FUNPOW (f o g) j ms))
Proof
  Induct
  \\ rw[Once asserts2_def]
  \\ Cases_on`j` \\ fs[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ simp[FUNPOW]
QED

Theorem upd_pc_simps[simp]:
   ((asmSem$upd_pc x s).align = s.align) ∧
   ((asmSem$upd_pc x s).mem_domain = s.mem_domain) ∧
   ((asmSem$upd_pc x s).failed = s.failed) ∧
   ((asmSem$upd_pc x s).be = s.be) ∧
   ((asmSem$upd_pc x s).mem = s.mem) ∧
   ((asmSem$upd_pc x s).regs = s.regs) ∧
   ((asmSem$upd_pc x s).fp_regs = s.fp_regs) ∧
   ((asmSem$upd_pc x s).lr = s.lr) ∧
   ((asmSem$upd_pc x s).pc = x)
Proof
  EVAL_TAC
QED

Theorem asm_failed_ignore_new_pc:
   !i v w s. (asm i w s).failed <=> (asm i v s).failed
Proof
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

Theorem asm_mem_ignore_new_pc:
   !i v w s. (asm i w s).mem = (asm i v s).mem
Proof
  Cases \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
QED

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

Theorem binop_upd_consts[simp]:
   ((binop_upd a b c d x).mem_domain = x.mem_domain) ∧
   ((binop_upd a b c d x).align = x.align) ∧
   ((binop_upd a b c d x).failed = x.failed) ∧
   ((binop_upd a b c d x).mem = x.mem) ∧
   ((binop_upd a b c d x).lr = x.lr) ∧
   ((binop_upd a b c d x).be = x.be)
Proof
  Cases_on`b`>>EVAL_TAC
QED

Theorem arith_upd_consts[simp]:
   ((arith_upd a x).mem_domain = x.mem_domain) ∧
   ((arith_upd a x).align = x.align) ∧
   ((arith_upd a x).mem = x.mem) ∧
   ((arith_upd a x).lr = x.lr) ∧
   ((arith_upd a x).be = x.be)
Proof
  Cases_on`a` >> EVAL_TAC >> srw_tac[][]
QED

Theorem fp_upd_consts[simp]:
   ((fp_upd a x).mem_domain = x.mem_domain) ∧
   ((fp_upd a x).align = x.align) ∧
   ((fp_upd a x).mem = x.mem) ∧
   ((fp_upd a x).lr = x.lr) ∧
   ((fp_upd a x).be = x.be)
Proof
  Cases_on`a`
  \\ rpt (EVAL_TAC \\ srw_tac[][] \\ CASE_TAC \\ rw [])
QED

Theorem asm_consts[simp]:
   !i w s. ((asm i w s).be = s.be) /\
            ((asm i w s).lr = s.lr) /\
            ((asm i w s).align = s.align) /\
            ((asm i w s).mem_domain = s.mem_domain)
Proof
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
  \\ full_simp_tac(srw_ss())[SND_read_mem_word_consts,write_mem_word_consts]
QED

Theorem RTC_asm_step_consts:
   RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2
  ⇒ (s2.mem_domain = s1.mem_domain) ∧
    (s2.lr = s1.lr) ∧
    (s2.align = s1.align) ∧
    (s2.be = s1.be)
Proof
  rw[]
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac \\ rw[]
  \\ fs[asmSemTheory.asm_step_def]
  \\ rw[]
QED

Theorem read_mem_word_IMP_mem_eq:
   !a k s w s'. (read_mem_word a k s = (w,s')) ==> (s'.mem = s.mem)
Proof
  Induct_on `k` \\ fs [asmSemTheory.read_mem_word_def]
  \\ rw [] \\ pairarg_tac \\ fs []
  \\ res_tac \\ fs [asmSemTheory.assert_def]
  \\ rveq \\ fs []
QED

Theorem write_mem_word_mem_domain:
   !k b a s. (write_mem_word b k a s).mem_domain = s.mem_domain
Proof
  Induct \\ fs [asmSemTheory.write_mem_word_def,
                asmSemTheory.assert_def,asmSemTheory.upd_mem_def]
QED

Theorem write_mem_word_mem_eq:
   !k b a s x.
      ~(write_mem_word b k a s).failed /\ x ∉ s.mem_domain ==>
      ((write_mem_word b k a s).mem x = s.mem x)
Proof
  Induct \\ fs [asmSemTheory.write_mem_word_def,APPLY_UPDATE_THM,
                asmSemTheory.assert_def,asmSemTheory.upd_mem_def]
  \\ fs [write_mem_word_mem_domain]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem mem_op_outside_mem_domain:
   ∀m n a s x. x ∉ s.mem_domain ∧ ¬(mem_op m n a s).failed ⇒
               ((asmSem$mem_op m n a s).mem x = s.mem x)
Proof
  Cases \\ rw[asmSemTheory.mem_op_def]
  \\ fs[asmSemTheory.mem_load_def,
        asmSemTheory.mem_store_def,
        asmSemTheory.upd_reg_def, asmSemTheory.assert_def]
  \\ TRY pairarg_tac \\ fs[]
  \\ imp_res_tac read_mem_word_IMP_mem_eq \\ fs []
  \\ match_mp_tac write_mem_word_mem_eq \\ fs []
QED

Theorem inst_outside_mem_domain:
   ∀i. x ∉ s.mem_domain ∧ ¬(inst i s).failed ⇒ ((inst i s).mem x = s.mem x)
Proof
  Cases \\ rw[asmSemTheory.inst_def]
  >- EVAL_TAC
  \\ rw[mem_op_outside_mem_domain]
QED

Theorem asm_outside_mem_domain:
   ∀i p s x. x ∉ s.mem_domain ∧ ¬(asm i p s).failed ⇒ ((asm i p s).mem x = s.mem x)
Proof
  ho_match_mp_tac asmTheory.asm_induction
  \\ rw[asmSemTheory.asm_def]
  >- rw[inst_outside_mem_domain]
  >- rw[asmSemTheory.jump_to_offset_def]
  >- rw[asmSemTheory.jump_to_offset_def]
  >- (rw[asmSemTheory.jump_to_offset_def] >- EVAL_TAC)
  >- EVAL_TAC
  >- EVAL_TAC
QED

Theorem asm_step_outside_mem_domain:
   asm_step c s1 i s2 ⇒
   (∀x. x ∉ s1.mem_domain ⇒ (s2.mem x = s1.mem x))
Proof
  rw[asmSemTheory.asm_step_def]
  \\ rw[asm_outside_mem_domain]
QED

Theorem RTC_asm_step_outside_mem_domain:
   ∀s1 s2. RTC (λs1 s2. ∃i. asm_step c s1 i s2) s1 s2
  ⇒ (∀a. a ∉ s1.mem_domain ⇒ (s2.mem a = s1.mem a))
Proof
  ho_match_mp_tac RTC_INDUCT
  \\ rw[]
  \\ drule asm_step_outside_mem_domain
  \\ disch_then drule \\ rw[]
  \\ fs[asmSemTheory.asm_step_def]
  \\ metis_tac[asm_consts]
QED

val () = export_theory ()
