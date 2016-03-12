open preamble ffiTheory BasicProvers
     wordSemTheory labSemTheory labPropsTheory
     lab_to_targetTheory lab_filterProofTheory
     asmTheory asmSemTheory asmPropsTheory
     targetSemTheory targetPropsTheory
local open stack_removeProofTheory in end

val aligned_w2n = stack_removeProofTheory.aligned_w2n;

val _ = new_theory "lab_to_targetProof";

(* TODO: move *)

val EXP2_EVEN = Q.store_thm("EXP2_EVEN",
  `∀n. EVEN (2 ** n) ⇔ n ≠ 0`,
  Induct >> simp[EXP,EVEN_DOUBLE]);

val LENGTH_FLAT_REPLICATE = Q.store_thm("LENGTH_FLAT_REPLICATE",
  `∀n. LENGTH (FLAT (REPLICATE n ls)) = n * LENGTH ls`,
  Induct >> simp[REPLICATE,MULT]);

val SUM_MAP_LENGTH_REPLICATE = Q.store_thm("SUM_MAP_LENGTH_REPLICATE",
  `∀n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls`,
  Induct >> simp[REPLICATE,MULT]);

val call_FFI_LENGTH = prove(
  ``(call_FFI st index x = (new_st,new_bytes)) ==>
    (LENGTH x = LENGTH new_bytes)``,
  full_simp_tac(srw_ss())[call_FFI_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[listTheory.LENGTH_MAP]);

val SUM_REPLICATE = store_thm("SUM_REPLICATE",
  ``!n k. SUM (REPLICATE n k) = n * k``,
  Induct \\ full_simp_tac(srw_ss())[REPLICATE,MULT_CLAUSES,AC ADD_COMM ADD_ASSOC]);

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

val EXP_IMP_ZERO_LT = Q.prove(
  `(2n ** y = x) ⇒ 0 < x`,
  metis_tac[bitTheory.TWOEXP_NOT_ZERO,NOT_ZERO_LT_ZERO]);

(* -- *)

val FLAT_REPLICATE_NIL = store_thm("FLAT_REPLICATE_NIL",
  ``!n. FLAT (REPLICATE n []) = []``,
  Induct \\ fs [REPLICATE]);

val enc_with_nop_thm = prove(
  ``enc_with_nop enc (b:'a asm) bytes =
      ?n. bytes = enc b ++ FLAT (REPLICATE n (enc (asm$Inst Skip)))``,
  fs [enc_with_nop_def,LENGTH_NIL]
  \\ IF_CASES_TAC \\ fs [FLAT_REPLICATE_NIL]
  \\ EQ_TAC \\ rw [] THEN1 metis_tac []
  \\ fs [LENGTH_APPEND,LENGTH_FLAT,map_replicate,SUM_REPLICATE]
  \\ fs [GSYM LENGTH_NIL] \\ fs [MULT_DIV]);

val asm_step_nop_def = Define `
  asm_step_nop enc bytes c s1 i s2 <=>
    bytes_in_memory s1.pc bytes s1.mem s1.mem_domain /\
    enc_with_nop enc i bytes /\
    (case c.link_reg of NONE => T | SOME r => s1.lr = r) /\
    (s1.be <=> c.big_endian) /\ s1.align = c.code_alignment /\
    asm i (s1.pc + n2w (LENGTH bytes)) s1 = s2 /\ ~s2.failed /\
    asm_ok i c`

val evaluate_nop_step =
  asm_step_IMP_evaluate_step
    |> SIMP_RULE std_ss [asm_step_def]
    |> SPEC_ALL |> Q.INST [`i`|->`Inst Skip`]
    |> SIMP_RULE (srw_ss()) [asm_def,inst_def,asm_ok_def,inst_ok_def,
         Once upd_pc_def,GSYM CONJ_ASSOC]

val shift_interfer_0 = prove(
  ``shift_interfer 0 = I``,
  full_simp_tac(srw_ss())[shift_interfer_def,FUN_EQ_THM,shift_seq_def,
      machine_config_component_equality]);

val upd_pc_with_pc = prove(
  ``upd_pc s1.pc s1 = s1:'a asm_state``,
  full_simp_tac(srw_ss())[asm_state_component_equality,upd_pc_def]);

val shift_interfer_twice = store_thm("shift_interfer_twice[simp]",
  ``shift_interfer l' (shift_interfer l c) =
    shift_interfer (l + l') c``,
  full_simp_tac(srw_ss())[shift_interfer_def,shift_seq_def,AC ADD_COMM ADD_ASSOC]);

val evaluate_nop_steps = prove(
  ``!n s1 ms1 c.
      backend_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc (FLAT (REPLICATE n (c.target.encode (Inst Skip)))) s1.mem
        s1.mem_domain /\
      (case c.target.config.link_reg of NONE => T | SOME r => s1.lr = r) /\
      (s1.be <=> c.target.config.big_endian) /\
      s1.align = c.target.config.code_alignment /\ ~s1.failed /\
      c.target.state_rel (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2.
        !k.
          evaluate c io (k + l) ms1 =
          evaluate (shift_interfer l c) io k ms2 /\
          c.target.state_rel
            (upd_pc (s1.pc + n2w (n * LENGTH (c.target.encode (Inst Skip)))) s1)
            ms2``,
  Induct \\ full_simp_tac(srw_ss())[] THEN1
   (rpt strip_tac \\ Q.LIST_EXISTS_TAC [`0`,`ms1`]
    \\ full_simp_tac(srw_ss())[shift_interfer_0,upd_pc_with_pc])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[REPLICATE,bytes_in_memory_APPEND]
  \\ mp_tac evaluate_nop_step \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ first_x_assum (mp_tac o
       Q.SPECL [`(upd_pc (s1.pc +
          n2w (LENGTH ((c:('a,'state,'b) machine_config).target.encode
            (Inst Skip)))) s1)`,`ms2`,`shift_interfer l c`])
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[shift_interfer_def,upd_pc_def,interference_ok_def,shift_seq_def])
  \\ rpt strip_tac
  \\ `(shift_interfer l c).target = c.target` by full_simp_tac(srw_ss())[shift_interfer_def]
  \\ full_simp_tac(srw_ss())[upd_pc_def]
  \\ Q.LIST_EXISTS_TAC [`l'+l`,`ms2'`]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,
       word_add_n2w,AC ADD_COMM ADD_ASSOC,MULT_CLAUSES]
  \\ full_simp_tac(srw_ss())[ADD_ASSOC] \\ rpt strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k`)
  \\ first_x_assum (mp_tac o Q.SPEC `k+l'`)
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]);

val asm_step_IMP_evaluate_step_nop = prove(
  ``!c s1 ms1 io i s2 bytes.
      backend_correct c.target /\
      c.prog_addresses = s1.mem_domain /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      bytes_in_memory s1.pc bytes s2.mem s1.mem_domain /\
      asm_step_nop c.target.encode bytes c.target.config s1 i s2 /\
      s2 = asm i (s1.pc + n2w (LENGTH bytes)) s1 /\
      c.target.state_rel (s1:'a asm_state) (ms1:'state) /\
      (!x. i <> Call x) ==>
      ?l ms2.
        !k.
          evaluate c io (k + l) ms1 =
          evaluate (shift_interfer l c) io k ms2 /\
          c.target.state_rel s2 ms2 /\ l <> 0``,
  full_simp_tac(srw_ss())[asm_step_nop_def] \\ rpt strip_tac
  \\ (asm_step_IMP_evaluate_step
      |> SIMP_RULE std_ss [asm_step_def] |> SPEC_ALL |> mp_tac) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[enc_with_nop_thm]
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1
   (full_simp_tac(srw_ss())[bytes_in_memory_APPEND] \\ Cases_on `i`
    \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def,
           LET_DEF,assert_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ Cases_on `?w. i = Jump w` \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[asm_def] \\ Q.LIST_EXISTS_TAC [`l`,`ms2`] \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `?c n r w. (i = JumpCmp c n r w) /\
                  word_cmp c (read_reg n s1) (reg_imm r s1)` \\ full_simp_tac(srw_ss())[]
  THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[asm_def] \\ Q.LIST_EXISTS_TAC [`l`,`ms2`] \\ full_simp_tac(srw_ss())[])
  \\ Cases_on `?r. (i = JumpReg r)` \\ full_simp_tac(srw_ss())[]
  THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[asm_def,LET_DEF] \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
               \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[])
  \\ qspecl_then [`n`,`asm i (s1.pc + n2w (LENGTH (c.target.encode i))) s1`,`ms2`,
       `shift_interfer l c`] mp_tac evaluate_nop_steps
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (full_simp_tac(srw_ss())[shift_interfer_def] \\ rpt strip_tac
    THEN1 (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def])
    THEN1
     (Q.ABBREV_TAC `mm = (asm i (s1.pc + n2w (LENGTH (c.target.encode i))) s1).mem`
      \\ full_simp_tac(srw_ss())[Once (asm_mem_ignore_new_pc |> Q.SPECL [`i`,`0w`])]
      \\ `!w. (asm i w s1).pc = w` by (Cases_on `i` \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def])
      \\ full_simp_tac(srw_ss())[bytes_in_memory_APPEND])
    \\ metis_tac [asm_failed_ignore_new_pc])
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
  \\ Q.LIST_EXISTS_TAC [`l+l'`,`ms2'`]
  \\ full_simp_tac(srw_ss())[PULL_FORALL] \\ strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k:num`)
  \\ qpat_assum `!k. xx = yy` (mp_tac o Q.SPEC `k+l':num`)
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC]
  \\ full_simp_tac(srw_ss())[shift_interfer_def]
  \\ qpat_assum `c.target.state_rel xx yy` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x = z) ==> (f x y ==> f z y)``)
  \\ Cases_on `i` \\ full_simp_tac(srw_ss())[asm_def]
  \\ full_simp_tac(srw_ss())[LENGTH_FLAT,SUM_REPLICATE,map_replicate]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  THEN1 (Cases_on `i'` \\ full_simp_tac(srw_ss())[inst_def,upd_pc_def]
    \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w])
  \\ full_simp_tac(srw_ss())[jump_to_offset_def,upd_pc_def]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]);

(* -- *)

val _ = Parse.temp_overload_on("option_ldrop",``λn l. OPTION_JOIN (OPTION_MAP (LDROP n) l)``)

val option_ldrop_0 = prove(
  ``!ll. option_ldrop 0 ll = ll``,
  Cases \\ full_simp_tac(srw_ss())[]);

val option_ldrop_SUC = prove(
  ``!k1 ll. option_ldrop (SUC k1) ll = option_ldrop 1 (option_ldrop k1 ll)``,
  Cases_on `ll` \\ full_simp_tac(srw_ss())[]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[LDROP_ADD]
  \\ Cases_on `LDROP k1 x` \\ full_simp_tac(srw_ss())[]);

val option_ldrop_option_ldrop = prove(
  ``!k1 ll k2.
      option_ldrop k1 (option_ldrop k2 ll) = option_ldrop (k1 + k2) ll``,
  Induct \\ full_simp_tac(srw_ss())[option_ldrop_0]
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[option_ldrop_SUC,ADD_CLAUSES]);

(*
val option_ldrop_lemma = prove(
  ``(call_FFI index x io = (new_bytes,new_io)) /\ new_io <> NONE ==>
    (new_io = option_ldrop 1 io)``,
  full_simp_tac(srw_ss())[call_FFI_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ srw_tac[][]
  \\ Q.MATCH_ASSUM_RENAME_TAC `LTL ll <> NONE`
  \\ `(ll = [||]) \/ ?h t. ll = h:::t` by metis_tac [llistTheory.llist_CASES]
  \\ full_simp_tac(srw_ss())[llistTheory.LDROP1_THM]);
*)

val IMP_IMP2 = METIS_PROVE [] ``a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)``

val lab_lookup_IMP = prove(
  ``(lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)``,
  full_simp_tac(srw_ss())[lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC);

val has_odd_inst_def = Define `
  (has_odd_inst [] = F) /\
  (has_odd_inst ((Section k [])::xs) = has_odd_inst xs) /\
  (has_odd_inst ((Section k (y::ys))::xs) <=>
     ~EVEN (line_length y) \/ has_odd_inst ((Section k ys)::xs))`

val line_similar_def = Define `
  (line_similar (Label k1 k2 l) (Label k1' k2' l') <=> (k1 = k1') /\ (k2 = k2')) /\
  (line_similar (Asm b bytes l) (Asm b' bytes' l') <=> (b = b')) /\
  (line_similar (LabAsm a w bytes l) (LabAsm a' w' bytes' l') <=> (a = a')) /\
  (line_similar _ _ <=> F)`

val code_similar_def = Define `
  (code_similar [] [] = T) /\
  (code_similar ((Section s1 lines1)::rest1) ((Section s2 lines2)::rest2) <=>
     code_similar rest1 rest2 /\
     EVERY2 line_similar lines1 lines2 /\ (s1 = s2)) /\
  (code_similar _ _ = F)`

val code_similar_ind = theorem "code_similar_ind";

val word_loc_val_def = Define `
  (word_loc_val p labs (Word w) = SOME w) /\
  (word_loc_val p labs (Loc k1 k2) =
     case lab_lookup k1 k2 labs of
     | NONE => NONE
     | SOME q => SOME (p + n2w q))`;

val word8_loc_val_def = Define `
  (word8_loc_val p labs (Byte w) = SOME w) /\
  (word8_loc_val p labs (LocByte k1 k2 n) =
     case lookup k1 labs of
     | NONE => NONE
     | SOME f => case lookup k2 f of
                 | NONE => NONE
                 | SOME q => SOME (w2w (p + n2w q) >> (8 * n)))`;

val bytes_in_mem_def = Define `
  (bytes_in_mem a [] m md k <=> T) /\
  (bytes_in_mem a (b::bs) m md k <=>
     a IN md /\ ~(a IN k) /\ (m a = b) /\
     bytes_in_mem (a+1w) bs m md k)`

val bytes_in_mem_IMP = prove(
  ``!xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm``,
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def,bytes_in_memory_def]);

val pos_val_def = Define `
  (pos_val i pos [] = pos) /\
  (pos_val i pos ((Section k [])::xs) = pos_val i pos xs) /\
  (pos_val i pos ((Section k (y::ys))::xs) =
     if is_Label y
     then pos_val i (pos + line_length y) ((Section k ys)::xs)
     else if i = 0:num then pos
          else pos_val (i-1) (pos + line_length y) ((Section k ys)::xs))`;

val has_io_index_def = Define `
  (has_io_index index [] = F) /\
  (has_io_index index ((Section k [])::xs) = has_io_index index xs) /\
  (has_io_index index ((Section k (y::ys))::xs) <=>
     has_io_index index ((Section k ys)::xs) \/
     case y of LabAsm (CallFFI i) _ _ _ => (i = index) | _ => F)`

val asm_write_bytearray_def = Define `
  (asm_write_bytearray a [] (m:'a word -> word8) = m) /\
  (asm_write_bytearray a (x::xs) m = (a =+ x) (asm_write_bytearray (a+1w) xs m))`

val word_loc_val_byte_def = Define `
  word_loc_val_byte p labs m a be =
    case word_loc_val p labs (m (byte_align a)) of
    | SOME w => SOME (get_byte a w be)
    | NONE => NONE`

val state_rel_def = Define `
  state_rel (mc_conf, code2, labs, p, check_pc) (s1:('a,'ffi) labSem$state) t1 ms1 <=>
    mc_conf.target.state_rel t1 ms1 /\ good_dimindex (:'a) /\
    (mc_conf.prog_addresses = t1.mem_domain) /\
    ~(mc_conf.halt_pc IN mc_conf.prog_addresses) /\
    reg_ok s1.ptr_reg mc_conf.target.config /\ (mc_conf.ptr_reg = s1.ptr_reg) /\
    reg_ok s1.len_reg mc_conf.target.config /\ (mc_conf.len_reg = s1.len_reg) /\
    reg_ok s1.link_reg mc_conf.target.config /\
    (!ms2 k index new_bytes t1 x.
       mc_conf.target.state_rel
         (t1 with pc := p - n2w ((3 + index) * ffi_offset)) ms2 /\
       (read_bytearray (t1.regs s1.ptr_reg) (LENGTH new_bytes)
         (\a. if a ∈ t1.mem_domain then SOME (t1.mem a) else NONE) =
           SOME x) ==>
       mc_conf.target.state_rel
         (t1 with
         <|regs := (\a. get_reg_value (s1.io_regs k a) (t1.regs a) I);
           mem := asm_write_bytearray (t1.regs s1.ptr_reg) new_bytes t1.mem;
           pc := t1.regs s1.link_reg|>)
        (mc_conf.ffi_interfer k index new_bytes ms2)) /\
    (!l1 l2 x.
       (lab_lookup l1 l2 labs = SOME x) ==> (1w && (p + n2w x)) = 0w) /\
    (!index.
       has_io_index index s1.code ==>
       ~(p - n2w ((3 + index) * ffi_offset) IN mc_conf.prog_addresses) /\
       ~(p - n2w ((3 + index) * ffi_offset) = mc_conf.halt_pc) /\
       (find_index (p - n2w ((3 + index) * ffi_offset))
          mc_conf.ffi_entry_pcs 0 = SOME index)) /\
    (p - n2w ffi_offset = mc_conf.halt_pc) /\
    interference_ok mc_conf.next_interfer (mc_conf.target.proj t1.mem_domain) /\
    (!q n. ((n2w (2 ** t1.align - 1) && q + n2w n) = 0w:'a word) <=>
           (n MOD 2 ** t1.align = 0)) /\
    (!l1 l2 x2.
       (loc_to_pc l1 l2 s1.code = SOME x2) ==>
       (lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))) /\
    (!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)) /\
    (!a. byte_align a IN s1.mem_domain ==>
         a IN t1.mem_domain /\ a IN s1.mem_domain /\
         (word_loc_val_byte p labs s1.mem a s1.be = SOME (t1.mem a))) /\
    (has_odd_inst code2 ==> (mc_conf.target.config.code_alignment = 0)) /\
    bytes_in_mem p (prog_to_bytes code2)
      t1.mem t1.mem_domain s1.mem_domain /\
    ~s1.failed /\ ~t1.failed /\ (s1.be = t1.be) /\
    (check_pc ==> (t1.pc = p + n2w (pos_val s1.pc 0 code2))) /\
    ((p && n2w (2 ** t1.align - 1)) = 0w) /\
    (case mc_conf.target.config.link_reg of NONE => T | SOME r => t1.lr = r) /\
    (t1.be <=> mc_conf.target.config.big_endian) /\
    (t1.align = mc_conf.target.config.code_alignment) /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    code_similar s1.code code2`

val pos_val_0 = prove(
  ``!xs c enc labs pos.
      all_enc_ok c enc labs pos xs ==> (pos_val 0 pos xs = pos)``,
  Induct \\ full_simp_tac(srw_ss())[pos_val_def] \\ Cases_on `h`
  \\ Induct_on `l` \\ full_simp_tac(srw_ss())[pos_val_def,all_enc_ok_def]
  \\ rpt strip_tac  \\ res_tac  \\ srw_tac[][]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[line_ok_def,line_length_def,is_Label_def]);

val prog_to_bytes_lemma = Q.prove(
  `!code2 code1 pc i pos.
      code_similar code1 code2 /\
      all_enc_ok (mc_conf:('a,'state,'b) machine_config).target.config
        mc_conf.target.encode labs pos code2 /\
      (asm_fetch_aux pc code1 = SOME i) ==>
      ?bs j bs2.
        (prog_to_bytes code2 = bs ++ line_bytes j ++ bs2) /\
        (LENGTH bs + pos = pos_val pc pos code2) /\
        (LENGTH bs + pos + LENGTH (line_bytes j) = pos_val (pc+1) pos code2) /\
        line_similar i j /\
        line_ok mc_conf.target.config mc_conf.target.encode
          labs (pos_val pc pos code2) j`,
  HO_MATCH_MP_TAC asm_code_length_ind \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def,asm_fetch_aux_def])
  THEN1
   (Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def]
    \\ Cases_on `h` \\ full_simp_tac(srw_ss())[code_similar_def]
    \\ Cases_on `l` \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,pos_val_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,all_enc_ok_def] \\ metis_tac [])
  \\ Cases_on `code1` \\ full_simp_tac(srw_ss())[code_similar_def]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[code_similar_def]
  \\ Cases_on`l` \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,pos_val_def]
  \\ rpt var_eq_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `line_similar x1 x2`
  \\ Q.MATCH_ASSUM_RENAME_TAC `LIST_REL line_similar ys1 ys2`
  \\ `is_Label x2 = is_Label x1` by
    (Cases_on `x1` \\ Cases_on `x2` \\ full_simp_tac(srw_ss())[line_similar_def,is_Label_def])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `is_Label x1` \\ full_simp_tac(srw_ss())[]
  THEN1
   (full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
    \\ full_simp_tac(srw_ss())[all_enc_ok_def,code_similar_def] \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
    \\ Cases_on `x2` \\ full_simp_tac(srw_ss())[line_ok_def,is_Label_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[line_length_def,line_bytes_def]
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])
  \\ Cases_on `pc = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (full_simp_tac(srw_ss())[listTheory.LENGTH_NIL] \\ qexists_tac `x2`
    \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF,all_enc_ok_def] \\ full_simp_tac(srw_ss())[pos_val_0]
    \\ imp_res_tac pos_val_0
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `x2`
    \\ full_simp_tac(srw_ss())[line_ok_def,is_Label_def,line_bytes_def,line_length_def] \\ srw_tac[][])
  \\ full_simp_tac(srw_ss())[prog_to_bytes_def,LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc-1`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
  \\ full_simp_tac(srw_ss())[all_enc_ok_def,code_similar_def]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
  \\ Q.LIST_EXISTS_TAC [`line_bytes x2 ++ bs`,
        `j`,`bs2`] \\ full_simp_tac(srw_ss())[] \\ `pc - 1 + 1 = pc` by decide_tac
  \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC])

val prog_to_bytes_lemma = prog_to_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [];

val bytes_in_mem_APPEND = prove(
  ``!xs ys a m md md1.
      bytes_in_mem a (xs ++ ys) m md md1 <=>
      bytes_in_mem a xs m md md1 /\
      bytes_in_mem (a + n2w (LENGTH xs)) ys m md md1``,
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def,ADD1,GSYM word_add_n2w,CONJ_ASSOC]);

val s1 = ``s1:('a,'ffi) labSem$state``;

val IMP_bytes_in_memory = prove(
  ``code_similar code1 code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    (asm_fetch_aux pc code1 = SOME i) /\
    bytes_in_mem p (prog_to_bytes code2) m (dm:'a word set) dm1 ==>
    ?j.
      bytes_in_mem (p + n2w (pos_val pc 0 code2)) (line_bytes j) m dm dm1 /\
      line_ok (mc_conf:('a,'state,'b) machine_config).target.config
        mc_conf.target.encode labs (pos_val pc 0 code2) j /\
      (pos_val (pc+1) 0 code2 = pos_val pc 0 code2 + LENGTH (line_bytes j)) /\
      line_similar i j``,
  rpt strip_tac
  \\ mp_tac prog_to_bytes_lemma \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[bytes_in_mem_APPEND]
  \\ Q.EXISTS_TAC `j` \\ full_simp_tac(srw_ss())[] \\ decide_tac);

val IMP_bytes_in_memory_JumpReg = prove(
  ``code_similar s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (JumpReg r1) l n)) ==>
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      (mc_conf.target.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    asm_ok (JumpReg r1) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,enc_with_nop_thm] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val IMP_bytes_in_memory_Jump = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val IMP_bytes_in_memory_JumpCmp = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.target.encode (JumpCmp cmp rr ri tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val IMP_bytes_in_memory_JumpCmp_1 = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)) ==>
    ?tt bytes.
      (tt = n2w (find_pos jtarget labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.encode (JumpCmp cmp rr ri tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (JumpCmp cmp rr ri tt) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ qexists_tac `n'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][]);

val IMP_bytes_in_memory_Call = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok (mc_conf: ('a,'state,'b) machine_config).target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem
      (t1:'a asm_state).mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Call ww) l bytes n)) ==>
    F``,
  rpt strip_tac
  \\ full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ imp_res_tac IMP_bytes_in_memory
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def] \\ rev_full_simp_tac(srw_ss())[]);

val IMP_bytes_in_memory_LocValue = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) l bytes n)) ==>
    ?tt bytes.
      (tt = n2w (find_pos (Lab l1 l2) labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      enc_with_nop mc_conf.target.encode (Loc reg tt) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Loc reg tt) (mc_conf: ('a,'state,'b) machine_config).target.config /\
      lab_lookup l1 l2 labs <> NONE``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ qexists_tac `n'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][]);

val IMP_bytes_in_memory_Inst = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (Inst i) bytes len)) ==>
    ?bytes.
      enc_with_nop mc_conf.target.encode (Inst i) bytes /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain /\
      bytes_in_mem ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        bytes t1.mem t1.mem_domain s1.mem_domain /\
      (pos_val (s1.pc+1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes) /\
      asm_ok (Inst i) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,LET_DEF] \\ srw_tac[][]
  \\ Q.EXISTS_TAC `l` \\ full_simp_tac(srw_ss())[enc_with_nop_thm,PULL_EXISTS,line_length_def]
  \\ qexists_tac `n` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ srw_tac[][]);

val IMP_bytes_in_memory_CallFFI = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + (3 + index) * ffi_offset)) /\
      (enc = mc_conf.target.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val IMP_bytes_in_memory_Halt = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Halt l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + ffi_offset)) /\
      (enc = mc_conf.target.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  full_simp_tac(srw_ss())[asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ full_simp_tac(srw_ss())[line_similar_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[line_ok_def,enc_with_nop_thm,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[LET_DEF,lab_inst_def,get_label_def] \\ srw_tac[][]
  \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val ADD_MODULUS_LEMMA = prove(
  ``!k m n. 0 < n ==> (m + k * n) MOD n = m MOD n``,
  Induct \\ full_simp_tac(srw_ss())[MULT_CLAUSES,ADD_ASSOC,ADD_MODULUS]);

val line_length_MOD_0 = prove(
  ``backend_correct mc_conf.target /\
    (~EVEN p ==> (mc_conf.target.config.code_alignment = 0)) /\
    line_ok mc_conf.target.config mc_conf.target.encode labs p h ==>
    (line_length h MOD 2 ** mc_conf.target.config.code_alignment = 0)``,
  Cases_on `h` \\ TRY (Cases_on `a`) \\ full_simp_tac(srw_ss())[line_ok_def,line_length_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[backend_correct_def,enc_ok_def]
  \\ full_simp_tac(srw_ss())[LET_DEF,enc_with_nop_thm] \\ srw_tac[][LENGTH_FLAT,LENGTH_REPLICATE]
  \\ qpat_assum `2 ** nn = xx:num` (ASSUME_TAC o GSYM) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[LET_DEF,map_replicate,SUM_REPLICATE] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[ADD_MODULUS_LEMMA]);

val pos_val_MOD_0_lemma = prove(
  ``(0 MOD 2 ** mc_conf.target.config.code_alignment = 0)``,
  full_simp_tac(srw_ss())[]);

val pos_val_MOD_0 = prove(
  ``!x pos code2.
      backend_correct mc_conf.target /\
      (has_odd_inst code2 ==> (mc_conf.target.config.code_alignment = 0)) /\
      (~EVEN pos ==> (mc_conf.target.config.code_alignment = 0)) /\
      (pos MOD 2 ** mc_conf.target.config.code_alignment = 0) /\
      all_enc_ok mc_conf.target.config mc_conf.target.encode labs pos code2 ==>
      (pos_val x pos code2 MOD 2 ** mc_conf.target.config.code_alignment = 0)``,
  reverse (Cases_on `backend_correct mc_conf.target`)
  \\ asm_simp_tac pure_ss [] THEN1 full_simp_tac(srw_ss())[]
  \\ HO_MATCH_MP_TAC (theorem "pos_val_ind")
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[pos_val_def] \\ full_simp_tac(srw_ss())[all_enc_ok_def]
  THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[PULL_FORALL,AND_IMP_INTRO,has_odd_inst_def])
  \\ Cases_on `is_Label y` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x = 0` \\ full_simp_tac(srw_ss())[]
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[has_odd_inst_def]
  \\ Cases_on `EVEN pos` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVEN_ADD]
  \\ `0:num < 2 ** mc_conf.target.config.code_alignment` by full_simp_tac(srw_ss())[]
  \\ imp_res_tac (GSYM MOD_PLUS)
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ imp_res_tac line_length_MOD_0 \\ full_simp_tac(srw_ss())[])
  |> Q.SPECL [`x`,`0`,`y`] |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [pos_val_MOD_0_lemma]
  |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];

val state_rel_weaken = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
    state_rel (mc_conf,code2,labs,p,F) s1 t1 ms1``,
  full_simp_tac(srw_ss())[state_rel_def] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[] \\ metis_tac []);

val read_bytearray_state_rel = prove(
  ``!n a x.
      state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 /\
      (read_bytearray a n s1.mem s1.mem_domain s1.be = SOME x) ==>
      (read_bytearray a n
        (\a. if a IN mc_conf.prog_addresses then SOME (t1.mem a) else NONE) =
       SOME x)``,
  Induct
  \\ full_simp_tac(srw_ss())[wordSemTheory.read_bytearray_def,targetSemTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux a s1.mem s1.mem_domain s1.be` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray (a + 1w) n s1.mem s1.mem_domain s1.be` \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def,mem_load_byte_aux_def]
  \\ Cases_on `s1.mem (byte_align a)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `a`) \\ full_simp_tac(srw_ss())[]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[word_loc_val_def]
  \\ rev_full_simp_tac(srw_ss())[word_loc_val_byte_def,word_loc_val_def]);

val IMP_has_io_index = prove(
  ``(asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    has_io_index index s1.code``,
  full_simp_tac(srw_ss())[asm_fetch_def]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`)
  \\ Q.SPEC_TAC (`s1.code`,`code`)
  \\ HO_MATCH_MP_TAC asm_code_length_ind \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[asm_fetch_aux_def,has_io_index_def] \\ res_tac
  \\ Cases_on `is_Label y` \\ full_simp_tac(srw_ss())[]
  THEN1 (Cases_on `y` \\ full_simp_tac(srw_ss())[is_Label_def] \\ res_tac)
  \\ Cases_on `pc = 0` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[]);

val bytes_in_mem_asm_write_bytearray_lemma = prove(
  ``!xs p.
      (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
      bytes_in_mem p xs m1 d k ==>
      bytes_in_mem p xs m2 d k``,
  Induct \\ full_simp_tac(srw_ss())[bytes_in_mem_def]);

val bytes_in_mem_asm_write_bytearray = prove(
  ``state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,p,T) s1 t1 ms1 /\
    (read_bytearray c1 (LENGTH new_bytes) s1.mem s1.mem_domain s1.be = SOME x) ==>
    bytes_in_mem p xs t1.mem t1.mem_domain s1.mem_domain ==>
    bytes_in_mem p xs
      (asm_write_bytearray c1 new_bytes t1.mem) t1.mem_domain s1.mem_domain``,
  STRIP_TAC \\ match_mp_tac bytes_in_mem_asm_write_bytearray_lemma
  \\ POP_ASSUM MP_TAC
  \\ Q.SPEC_TAC (`c1`,`a`)
  \\ Q.SPEC_TAC (`x`,`x`)
  \\ Q.SPEC_TAC (`t1.mem`,`m`)
  \\ Induct_on `new_bytes`
  \\ full_simp_tac(srw_ss())[asm_write_bytearray_def]
  \\ REPEAT STRIP_TAC
  \\ full_simp_tac(srw_ss())[wordSemTheory.read_bytearray_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ res_tac
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ full_simp_tac(srw_ss())[mem_load_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ srw_tac[][combinTheory.APPLY_UPDATE_THM]
  \\ full_simp_tac(srw_ss())[state_rel_def] \\ res_tac);

val write_bytearray_NOT_Loc = prove(
  ``!xs c1 s1 a c.
      (s1.mem a = Word c) ==>
      (write_bytearray c1 xs s1.mem s1.mem_domain s1.be) a <> Loc n n0``,
  Induct \\ full_simp_tac(srw_ss())[write_bytearray_def,mem_store_byte_aux_def]
  \\ rpt strip_tac \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[labSemTheory.upd_mem_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]);

val CallFFI_bytearray_lemma = prove(
  ``byte_align (a:'a word) IN s1.mem_domain /\ good_dimindex (:'a) /\
    a IN t1.mem_domain /\
    a IN s1.mem_domain /\
    (s1.be = mc_conf.target.config.big_endian) /\
    (read_bytearray c1 (LENGTH new_bytes) s1.mem s1.mem_domain s1.be = SOME x) /\
    (word_loc_val_byte p labs s1.mem a mc_conf.target.config.big_endian =
       SOME (t1.mem a)) ==>
    (word_loc_val_byte p labs (write_bytearray c1 new_bytes s1.mem s1.mem_domain s1.be) a
       mc_conf.target.config.big_endian =
     SOME (asm_write_bytearray c1 new_bytes t1.mem a))``,
  Q.SPEC_TAC (`s1`,`s1`) \\ Q.SPEC_TAC (`t1`,`t1`) \\ Q.SPEC_TAC (`c1`,`c1`)
  \\ Q.SPEC_TAC (`x`,`x`) \\ Q.SPEC_TAC (`new_bytes`,`xs`) \\ Induct
  \\ full_simp_tac(srw_ss())[asm_write_bytearray_def,write_bytearray_def,wordSemTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux c1 s1.mem s1.mem_domain s1.be` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `read_bytearray (c1 + 1w) (LENGTH xs) s1.mem s1.mem_domain s1.be`
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ qmatch_assum_rename_tac
       `read_bytearray (c1 + 1w) (LENGTH xs) s1.mem s1.mem_domain s1.be = SOME y`
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y`,`c1+1w`,`t1`,`s1`])
  \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[mem_store_byte_aux_def]
  \\ reverse (Cases_on `(write_bytearray (c1 + 1w)
       xs s1.mem s1.mem_domain mc_conf.target.config.big_endian) (byte_align c1)`)
  \\ full_simp_tac(srw_ss())[] THEN1
   (full_simp_tac(srw_ss())[mem_load_byte_aux_def]
    \\ Cases_on `s1.mem (byte_align c1)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac write_bytearray_NOT_Loc \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])
  \\ `byte_align c1 IN s1.mem_domain` by
    (full_simp_tac(srw_ss())[mem_load_byte_aux_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[labSemTheory.upd_mem_def,word_loc_val_byte_def,APPLY_UPDATE_THM]
  \\ Cases_on `a = c1` \\ full_simp_tac(srw_ss())[word_loc_val_def,get_byte_set_byte]
  \\ Cases_on `byte_align c1 = byte_align a` \\ full_simp_tac(srw_ss())[word_loc_val_def]
  \\ full_simp_tac(srw_ss())[get_byte_set_byte_diff]);

val word_cmp_lemma = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 /\
    (word_cmp cmp (read_reg rr s1) (reg_imm ri s1) = SOME x) ==>
    (x = word_cmp cmp (read_reg rr t1) (reg_imm ri t1))``,
  Cases_on `ri` \\ full_simp_tac(srw_ss())[labSemTheory.reg_imm_def,asmSemTheory.reg_imm_def]
  \\ full_simp_tac(srw_ss())[asmSemTheory.read_reg_def]
  \\ Cases_on `s1.regs rr` \\ full_simp_tac(srw_ss())[]
  \\ TRY (Cases_on `s1.regs n`) \\ full_simp_tac(srw_ss())[] \\ Cases_on `cmp`
  \\ full_simp_tac(srw_ss())[labSemTheory.word_cmp_def,asmSemTheory.word_cmp_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ first_assum (assume_tac o Q.SPEC `rr:num`)
  \\ first_x_assum (assume_tac o Q.SPEC `n:num`)
  \\ rev_full_simp_tac(srw_ss())[word_loc_val_def] \\ srw_tac[][]
  \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ rpt (qpat_assum `1w = xxx` (fn th => full_simp_tac(srw_ss())[GSYM th]))
  \\ rpt (qpat_assum `p + n2w xxx = t1.regs rr` (fn th => full_simp_tac(srw_ss())[GSYM th]))
  \\ res_tac \\ full_simp_tac(srw_ss())[]);

val bytes_in_mem_IMP_memory = prove(
  ``!xs a.
      (!a. ~(a IN dm1) ==> m a = m1 a) ==>
      bytes_in_mem a xs m dm dm1 ==>
      bytes_in_memory a xs m1 dm``,
  Induct \\ full_simp_tac(srw_ss())[bytes_in_memory_def,bytes_in_mem_def]);

val state_rel_shift_interfer = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 x ==>
    state_rel (shift_interfer l mc_conf,code2,labs,p,T) s1 t1 x``,
  full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def]
  \\ rpt strip_tac \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ res_tac
  \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]);

val state_rel_clock = prove(
  ``state_rel x s1 t1 ms ==>
    state_rel x (s1 with clock := k) (t1) ms``,
  PairCases_on `x`
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ metis_tac []);

(* TODO: move *)

val TODO_MOVE_binop_upd_consts = Q.store_thm("TODO_MOVE_binop_upd_consts[simp]",
  `(asmSem$binop_upd a b c d x).mem_domain = x.mem_domain ∧
   (asmSem$binop_upd a b c d x).align = x.align ∧
   (asmSem$binop_upd a b c d x).failed = x.failed ∧
   (asmSem$binop_upd a b c d x).mem = x.mem ∧
   (asmSem$binop_upd a b c d x).lr = x.lr ∧
   (asmSem$binop_upd a b c d x).be = x.be`,
  Cases_on`b`>>EVAL_TAC);

val TODO_MOVE_arith_upd_consts = Q.store_thm("TODO_MOVE_arith_upd_consts[simp]",
  `(asmSem$arith_upd a x).mem_domain = x.mem_domain ∧
   (asmSem$arith_upd a x).align = x.align ∧
   (asmSem$arith_upd a x).failed = x.failed ∧
   (asmSem$arith_upd a x).mem = x.mem ∧
   (asmSem$arith_upd a x).lr = x.lr ∧
   (asmSem$arith_upd a x).be = x.be`,
  Cases_on`a` >> EVAL_TAC >> srw_tac[][]);

(* -- *)

val arith_upd_lemma = Q.prove(
  `(∀r. word_loc_val p labs (read_reg r s1) = SOME (t1.regs r)) ∧ ¬(arith_upd a s1).failed ⇒
   ∀r. word_loc_val p labs (read_reg r (arith_upd a s1)) =
       SOME ((arith_upd a t1).regs r)`,
  Cases_on`a`>>srw_tac[][arith_upd_def]>- (
    every_case_tac >> full_simp_tac(srw_ss())[] >>
    EVAL_TAC >> srw_tac[][] >>
    metis_tac[] )
  >- (
    pop_assum mp_tac >>
    reverse BasicProvers.TOP_CASE_TAC >- EVAL_TAC >>
    reverse BasicProvers.TOP_CASE_TAC >- EVAL_TAC >>
    qmatch_assum_rename_tac`read_reg rr _ = _` >>
    first_assum(qspec_then`rr`mp_tac) >>
    first_assum(SUBST1_TAC) >>
    EVAL_TAC >> strip_tac >>
    Cases_on`b` >> EVAL_TAC >> srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    EVAL_TAC >>
    qpat_assum`_ = Word c`mp_tac >>
    Cases_on`r` >> EVAL_TAC >> srw_tac[][] >>
    qmatch_assum_rename_tac`read_reg r2 _ = _` >>
    first_x_assum(qspec_then`r2`mp_tac) >>
    simp[] >> EVAL_TAC >> srw_tac[][])
  >- (
    EVAL_TAC >>
    every_case_tac >> full_simp_tac(srw_ss())[APPLY_UPDATE_THM] >> srw_tac[][] >>
    pop_assum mp_tac >>
    EVAL_TAC >>
    qmatch_assum_rename_tac`read_reg r _ = _` >>
    first_x_assum(qspec_then`r`mp_tac) >>
    simp[] >> EVAL_TAC >> srw_tac[][] ));

val MULT_ADD_LESS_MULT = prove(
  ``!m n k l j. m < l /\ n < k /\ j <= k ==> m * j + n < l * k:num``,
  rpt strip_tac
  \\ `SUC m <= l` by asm_rewrite_tac [GSYM LESS_EQ]
  \\ `m * k + k <= l * k` by asm_simp_tac bool_ss [LE_MULT_RCANCEL,GSYM MULT]
  \\ `m * j <= m * k` by asm_simp_tac bool_ss [LE_MULT_LCANCEL]
  \\ decide_tac);

val aligned_IMP_ADD_LESS_dimword = prove(
  ``aligned k (x:'a word) /\ k <= dimindex (:'a) ==>
    w2n x + (2 ** k - 1) < dimword (:'a)``,
  Cases_on `x` \\ fs [aligned_w2n,dimword_def] \\ rw []
  \\ full_simp_tac std_ss [ONCE_REWRITE_RULE [ADD_COMM]LESS_EQ_EXISTS]
  \\ pop_assum (fn th => full_simp_tac std_ss [th])
  \\ full_simp_tac std_ss [MOD_EQ_0_DIVISOR]
  \\ var_eq_tac
  \\ full_simp_tac std_ss [EXP_ADD]
  \\ match_mp_tac MULT_ADD_LESS_MULT \\ fs []);

val aligned_2_imp = store_thm("aligned_2_imp",
  ``aligned 2 (x:'a word) /\ dimindex (:'a) = 32 ==>
    byte_align x = x ∧
    byte_align (x + 1w) = x ∧
    byte_align (x + 2w) = x ∧
    byte_align (x + 3w) = x``,
  rw [alignmentTheory.byte_align_def, GSYM alignmentTheory.aligned_def]
  \\ match_mp_tac alignmentTheory.align_add_aligned
  \\ simp [wordsTheory.dimword_def])

val aligned_2_not_eq = store_thm("aligned_2_not_eq",
  ``aligned 2 (x:'a word) ∧ dimindex(:'a) = 32 ∧
    x ≠ byte_align a ⇒
    x ≠ a ∧
    x+1w ≠ a ∧
    x+2w ≠ a ∧
    x+3w ≠ a``,
  metis_tac[aligned_2_imp])

val aligned_3_imp = store_thm("aligned_3_imp",
  ``aligned 3 (x:'a word) /\ dimindex (:'a) = 64 ==>
    byte_align x = x ∧
    byte_align (x + 1w) = x ∧
    byte_align (x + 2w) = x ∧
    byte_align (x + 3w) = x ∧
    byte_align (x + 4w) = x ∧
    byte_align (x + 5w) = x ∧
    byte_align (x + 6w) = x ∧
    byte_align (x + 7w) = x``,
  rw [alignmentTheory.byte_align_def, GSYM alignmentTheory.aligned_def]
  \\ match_mp_tac alignmentTheory.align_add_aligned
  \\ simp [wordsTheory.dimword_def])

val aligned_3_not_eq = store_thm("aligned_3_not_eq",
  ``aligned 3 (x:'a word) ∧ dimindex(:'a) = 64 ∧
    x ≠ byte_align a ⇒
    x ≠ a ∧
    x+1w ≠ a ∧
    x+2w ≠ a ∧
    x+3w ≠ a ∧
    x+4w ≠ a ∧
    x+5w ≠ a ∧
    x+6w ≠ a ∧
    x+7w ≠ a``,
    metis_tac[aligned_3_imp])

val ADD_MOD_EQ_LEMMA = prove(
  ``k MOD d = 0 /\ n < d ==> (k + n) MOD d = n``,
  rw [] \\ `0 < d` by decide_tac
  \\ fs [MOD_EQ_0_DIVISOR]
  \\ pop_assum kall_tac
  \\ drule MOD_MULT
  \\ fs []);

val dimword_eq_32_imp_or_bytes = prove(
  ``dimindex (:'a) = 32 ==>
    (w2w ((w2w (x:'a word)):word8) ‖
     w2w ((w2w (x ⋙ 8)):word8) ≪ 8 ‖
     w2w ((w2w (x ⋙ 16)):word8) ≪ 16 ‖
     w2w ((w2w (x ⋙ 24)):word8) ≪ 24) = x``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [])

val dimword_eq_64_imp_or_bytes = prove(
  ``dimindex (:'a) = 64 ==>
    (w2w ((w2w (x:'a word)):word8) ‖
     w2w ((w2w (x ⋙ 8)):word8) ≪ 8 ‖
     w2w ((w2w (x ⋙ 16)):word8) ≪ 16 ‖
     w2w ((w2w (x ⋙ 24)):word8) ≪ 24 ‖
     w2w ((w2w (x ⋙ 32)):word8) ≪ 32 ‖
     w2w ((w2w (x ⋙ 40)):word8) ≪ 40 ‖
     w2w ((w2w (x ⋙ 48)):word8) ≪ 48 ‖
     w2w ((w2w (x ⋙ 56)):word8) ≪ 56) = x``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [])

val byte_align_32_eq = prove(``
  dimindex (:'a) = 32 ⇒
  byte_align (a:'a word) +n2w (w2n a MOD 4) = a``,
  Cases_on`a`>>
  rw[alignmentTheory.byte_align_def]>>
  fs[alignmentTheory.align_w2n,word_add_n2w]>>rfs[dimword_def]>>
  Q.SPEC_THEN `4n` mp_tac DIVISION>>
  fs[]>>disch_then (Q.SPEC_THEN`n` assume_tac)>>
  simp[])

val byte_align_64_eq = prove(``
  dimindex (:'a) = 64 ⇒
  byte_align (a:'a word) +n2w (w2n a MOD 8) = a``,
  Cases_on`a`>>
  rw[alignmentTheory.byte_align_def]>>
  fs[alignmentTheory.align_w2n,word_add_n2w]>>rfs[dimword_def]>>
  Q.SPEC_THEN `8n` mp_tac DIVISION>>
  fs[]>>disch_then (Q.SPEC_THEN`n` assume_tac)>>
  simp[])

val byte_align_32_IMP = prove(``
  dimindex(:'a) = 32 ⇒
  (byte_align a = a ⇒ w2n a MOD 4 = 0) ∧
  (byte_align a + (1w:'a word) = a ⇒ w2n a MOD 4 = 1) ∧
  (byte_align a + (2w:'a word) = a ⇒ w2n a MOD 4 = 2) ∧
  (byte_align a + (3w:'a word) = a ⇒ w2n a MOD 4 = 3)``,
  rw[]>>imp_res_tac byte_align_32_eq>>fs[]>>
  qpat_assum`A=a` mp_tac>>
  qabbrev_tac`ba = byte_align a`>>
  qabbrev_tac`ca = w2n a MOD 4`>>
  first_x_assum(qspec_then`a` (SUBST1_TAC o SYM))>>
  unabbrev_all_tac>>
  fs[dimword_def,addressTheory.WORD_EQ_ADD_CANCEL]>>
  Q.ISPECL_THEN[`32n`,`w2n a MOD 4`] assume_tac bitTheory.MOD_ZERO_GT>>
  fs[]>>
  Q.ISPECL_THEN [`w2n a`,`4n`] assume_tac MOD_LESS>>
  DECIDE_TAC)

val MOD4_CASES = prove(``
  ∀n. n MOD 4 = 0 ∨ n MOD 4 = 1 ∨ n MOD 4 = 2 ∨ n MOD 4 = 3``,
  rw[]>>`n MOD 4 < 4` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 4 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``)
  \\ fs [])

val byte_align_32_CASES = prove(``
  dimindex(:'a) = 32 ⇒
  byte_align a + (3w:'a word) = a ∨
  byte_align a + (2w:'a word) = a ∨
  byte_align a + (1w:'a word) = a ∨
  byte_align a = a``,
  rw[]>>imp_res_tac byte_align_32_eq>>
  pop_assum(qspec_then`a` assume_tac)>>
  Q.SPEC_THEN `w2n a` mp_tac MOD4_CASES>>rw[]>>
  fs[])

val MOD8_CASES = prove(``
  ∀n. n MOD 8 = 0 ∨ n MOD 8 = 1 ∨ n MOD 8 = 2 ∨ n MOD 8 = 3 ∨
      n MOD 8 = 4 ∨ n MOD 8 = 5 ∨ n MOD 8 = 6 ∨ n MOD 8 = 7``,
  rw[]>>`n MOD 8 < 8` by fs []
  \\ IMP_RES_TAC (DECIDE
       ``n < 8 ==> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num) \/
                   (n = 4) \/ (n = 5) \/ (n = 6) \/ (n = 7)``)
  \\ fs [])

val byte_align_64_CASES = prove(``
  dimindex(:'a) = 64 ⇒
  byte_align a + (7w:'a word) = a ∨
  byte_align a + (6w:'a word) = a ∨
  byte_align a + (5w:'a word) = a ∨
  byte_align a + (4w:'a word) = a ∨
  byte_align a + (3w:'a word) = a ∨
  byte_align a + (2w:'a word) = a ∨
  byte_align a + (1w:'a word) = a ∨
  byte_align a = a``,
  rw[]>>imp_res_tac byte_align_64_eq>>
  pop_assum(qspec_then`a` assume_tac)>>
  Q.SPEC_THEN `w2n a` mp_tac MOD8_CASES>>rw[]>>
  fs[])

val byte_align_64_IMP = prove(``
  dimindex(:'a) = 64 ⇒
  (byte_align a + (7w:'a word) = a ⇒ w2n a MOD 8 = 7) ∧
  (byte_align a + (6w:'a word) = a ⇒ w2n a MOD 8 = 6) ∧
  (byte_align a + (5w:'a word) = a ⇒ w2n a MOD 8 = 5) ∧
  (byte_align a + (4w:'a word) = a ⇒ w2n a MOD 8 = 4) ∧
  (byte_align a + (3w:'a word) = a ⇒ w2n a MOD 8 = 3) ∧
  (byte_align a + (2w:'a word) = a ⇒ w2n a MOD 8 = 2) ∧
  (byte_align a + (1w:'a word) = a ⇒ w2n a MOD 8 = 1) ∧
  (byte_align a = a ⇒ w2n a MOD 8 = 0)``,
  rw[]>>imp_res_tac byte_align_64_eq>>fs[]>>
  qpat_assum`A=a` mp_tac>>
  qabbrev_tac`ba = byte_align a`>>
  qabbrev_tac`ca = w2n a MOD 8`>>
  first_x_assum(qspec_then`a` (SUBST1_TAC o SYM))>>
  unabbrev_all_tac>>
  fs[dimword_def,addressTheory.WORD_EQ_ADD_CANCEL]>>
  Q.ISPECL_THEN[`64n`,`w2n a MOD 8`] assume_tac bitTheory.MOD_ZERO_GT>>
  fs[]>>
  Q.ISPECL_THEN [`w2n a`,`8n`] assume_tac MOD_LESS>>
  DECIDE_TAC)

val Inst_lemma = Q.prove(
  `~(asm_inst i s1).failed /\
   state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,p,T) s1 t1 ms1 /\
   (pos_val (s1.pc + 1) 0 code2 = pos_val s1.pc 0 code2 + LENGTH bytes') ==>
   ~(inst i t1).failed /\
    (!a. ~(a IN s1.mem_domain) ==> (inst i t1).mem a = t1.mem a) /\
   (mc_conf.target.state_rel
      (upd_pc (t1.pc + n2w (LENGTH bytes')) (inst i t1)) ms2 ==>
    state_rel (mc_conf,code2,labs,p,T)
      (inc_pc (dec_clock (asm_inst i s1)))
      (upd_pc (t1.pc + n2w (LENGTH (bytes':word8 list))) (inst i t1)) ms2)`,
  Cases_on `i` \\ full_simp_tac(srw_ss())[asm_inst_def,inst_def]
  THEN1
   (full_simp_tac(srw_ss())[state_rel_def,inc_pc_def,shift_interfer_def,upd_pc_def,dec_clock_def]
    \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[GSYM word_add_n2w])
  THEN1
   (full_simp_tac(srw_ss())[state_rel_def,inc_pc_def,shift_interfer_def,upd_pc_def,
        dec_clock_def,asmSemTheory.upd_reg_def,labSemTheory.upd_reg_def]
    \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[GSYM word_add_n2w]
    \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][word_loc_val_def])
  THEN1
   (strip_tac >>
    conj_tac >- (
      Cases_on`a`>> full_simp_tac(srw_ss())[asmSemTheory.arith_upd_def,labSemTheory.arith_upd_def] >>
      every_case_tac >> full_simp_tac(srw_ss())[labSemTheory.assert_def] >> srw_tac[][] >>
      full_simp_tac(srw_ss())[reg_imm_def,binop_upd_def,labSemTheory.binop_upd_def] >>
      full_simp_tac(srw_ss())[upd_reg_def,labSemTheory.upd_reg_def,state_rel_def] >>
      TRY (Cases_on`b`)>>EVAL_TAC >> full_simp_tac(srw_ss())[state_rel_def]) >>
    srw_tac[][] >>
    simp[inc_pc_dec_clock] >>
    simp[dec_clock_def] >>
    match_mp_tac state_rel_clock >>
    full_simp_tac(srw_ss())[state_rel_def] >>
    simp[GSYM word_add_n2w] >>
    fsrw_tac[ARITH_ss][] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- ( srw_tac[][] >> first_x_assum drule >> simp[] ) >>
    match_mp_tac arith_upd_lemma >> srw_tac[][])
  \\ strip_tac >>
  Cases_on`m`>>fs[mem_op_def,labSemTheory.assert_def]
  >-
    (`good_dimindex(:'a)` by fs[state_rel_def]>>
    fs[good_dimindex_def]>>
    Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_load_byte_def,labSemTheory.assert_def,labSemTheory.upd_reg_def,dec_clock_def,assert_def,read_mem_word_def_compute,mem_load_def,upd_reg_def,upd_pc_def,mem_load_byte_aux_def,labSemTheory.addr_def,addr_def,read_reg_def,labSemTheory.mem_load_def]>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    ntac 2 strip_tac>>fs[state_rel_def]>>
    `t1.regs n' = c'` by
      (first_x_assum(qspec_then`n'` assume_tac)>>
      rfs[word_loc_val_def])>>
    fs[]
    >-
      (`aligned 2 x` by fs [aligned_w2n]>>
       drule aligned_2_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
          fs[read_mem_def]>>
          res_tac>>
          fs[word_loc_val_byte_def]>>
          ntac 4 (FULL_CASE_TAC>>fs[])>>
          rfs[get_byte_def,byte_index_def]>>rveq>>
          Cases_on `c + t1.regs n'`>>
          qcase_tac `k < dimword (:α)`>>
          drule aligned_IMP_ADD_LESS_dimword >>
          full_simp_tac std_ss [] \\ fs [] >>
          strip_tac \\ fs [word_add_n2w] >>
          rfs [ADD_MOD_EQ_LEMMA] >>
          rpt (qpat_assum `w2w _ = _` (mp_tac o GSYM)) >>
          imp_res_tac dimword_eq_32_imp_or_bytes >> fs [])))
    >>
      `aligned 3 x` by fs [aligned_w2n]>>
       drule aligned_3_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
      `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align (x+4w) ∈ s1.mem_domain ∧
       byte_align (x+5w) ∈ s1.mem_domain ∧
       byte_align (x+6w) ∈ s1.mem_domain ∧
       byte_align (x+7w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
          fs[read_mem_def]>>
          res_tac>>
          fs[word_loc_val_byte_def]>>
          ntac 8 (FULL_CASE_TAC>>fs[])>>
          rfs[get_byte_def,byte_index_def]>>rveq>>
          Cases_on `c + t1.regs n'`>>
          qcase_tac `k < dimword (:α)`>>
          drule aligned_IMP_ADD_LESS_dimword >>
          full_simp_tac std_ss [] \\ fs [] >>
          strip_tac \\ fs [word_add_n2w] >>
          rfs [ADD_MOD_EQ_LEMMA] >>
          rpt (qpat_assum `w2w _ = _` (mp_tac o GSYM)) >>
          imp_res_tac dimword_eq_64_imp_or_bytes >> fs [])))
  >- (*Load8*)
    (Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_load_byte_def,labSemTheory.assert_def,labSemTheory.upd_reg_def,dec_clock_def,state_rel_def,assert_def,read_mem_word_def_compute,mem_load_def,upd_reg_def,upd_pc_def,mem_load_byte_aux_def,labSemTheory.addr_def,addr_def,read_reg_def]>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 2 (pop_assum mp_tac)>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 2 strip_tac>>
    res_tac>>fs[word_loc_val_byte_def]>>
    FULL_CASE_TAC>>fs[]>>
    first_assum(qspec_then`n'` assume_tac)>>
    qpat_assum`A=Word c'` SUBST_ALL_TAC>>
    fs[word_loc_val_def,GSYM word_add_n2w,alignmentTheory.aligned_extract]>>
    rw[]
    >- metis_tac[]
    >-
      (Cases_on`n=r`>>fs[APPLY_UPDATE_THM,word_loc_val_def]>>
      fs[read_mem_def]>>
      rfs[word_loc_val_def]))
  >-
    (*Store*)
    (`good_dimindex(:'a)` by fs[state_rel_def]>>
    fs[good_dimindex_def]>>
    Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_store_byte_def,labSemTheory.assert_def,mem_store_byte_aux_def,mem_store_def,labSemTheory.addr_def,addr_def,write_mem_word_def_compute,upd_pc_def,read_reg_def,assert_def,upd_mem_def,dec_clock_def,labSemTheory.mem_store_def,read_reg_def,labSemTheory.upd_mem_def]>>
    TOP_CASE_TAC>>fs[]>>
    pop_assum mp_tac>>TOP_CASE_TAC>>fs[]>>
    ntac 2 strip_tac>>fs[state_rel_def]>>
    `t1.regs n' = c'` by
      (first_x_assum(qspec_then`n'` assume_tac)>>
      rfs[word_loc_val_def])>>
    fs[]
    >-
      (`aligned 2 x` by fs [aligned_w2n]>>
       drule aligned_2_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
       `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         (simp[APPLY_UPDATE_THM]>>
         res_tac>>fs[]>>
         rpt(IF_CASES_TAC>>fs[]))
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         (simp[word_loc_val_byte_def,APPLY_UPDATE_THM]>>
         IF_CASES_TAC>>fs[]
         >-
           (fs[get_byte_def,byte_index_def]>>
           drule byte_align_32_IMP>>
           rpt IF_CASES_TAC>>fs[]>>
           metis_tac[byte_align_32_CASES])
         >>
           res_tac>>
           imp_res_tac aligned_2_not_eq>>fs[word_loc_val_byte_def])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>HINT_EXISTS_TAC>>fs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[])))
     >>
       (`aligned 3 x` by fs [aligned_w2n]>>
       drule aligned_3_imp>>
       disch_then (strip_assume_tac o UNDISCH)>>
       `byte_align (x+1w) ∈ s1.mem_domain ∧
       byte_align (x+2w) ∈ s1.mem_domain ∧
       byte_align (x+3w) ∈ s1.mem_domain ∧
       byte_align (x+4w) ∈ s1.mem_domain ∧
       byte_align (x+5w) ∈ s1.mem_domain ∧
       byte_align (x+6w) ∈ s1.mem_domain ∧
       byte_align (x+7w) ∈ s1.mem_domain ∧
       byte_align x ∈ s1.mem_domain` by fs[]>>
       IF_CASES_TAC>>simp[GSYM word_add_n2w]>>
       (rw[]
       >-
         (simp[APPLY_UPDATE_THM]>>
         res_tac>>fs[]>>
         rpt(IF_CASES_TAC>>fs[]))
       >-
         metis_tac[]
       >-
         metis_tac[]
       >-
         (simp[word_loc_val_byte_def,APPLY_UPDATE_THM]>>
         IF_CASES_TAC>>fs[]
         >-
           (fs[get_byte_def,byte_index_def]>>
           drule byte_align_64_IMP>>
           rpt IF_CASES_TAC>>fs[]>>
           metis_tac[byte_align_64_CASES])
         >>
           res_tac>>
           imp_res_tac aligned_3_not_eq>>fs[word_loc_val_byte_def])
       >-
         (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>HINT_EXISTS_TAC>>fs[]>>
         rw[APPLY_UPDATE_THM]>>
         rfs[]))))
  >-
    (Cases_on`a`>>last_x_assum mp_tac>>
    fs[mem_store_byte_def,labSemTheory.assert_def,mem_store_byte_aux_def,mem_store_def,labSemTheory.addr_def,addr_def,write_mem_word_def_compute,upd_pc_def,read_reg_def,assert_def,upd_mem_def,dec_clock_def]>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>
    ntac 3 (pop_assum mp_tac)>>
    ntac 2 (TOP_CASE_TAC>>fs[])>>
    ntac 3 strip_tac>>
    fs[state_rel_def]>>
    res_tac>>fs[word_loc_val_byte_def]>>
    FULL_CASE_TAC>>fs[]>>
    first_assum(qspec_then`n'` assume_tac)>>
    qpat_assum`A=Word c''` SUBST_ALL_TAC>>
    fs[word_loc_val_def,GSYM word_add_n2w,alignmentTheory.aligned_extract]>>
    rw[]
    >-
      (fs[APPLY_UPDATE_THM]>>
      IF_CASES_TAC>>fs[])
    >- metis_tac[]
    >-
      (simp[APPLY_UPDATE_THM]>>
      IF_CASES_TAC>>fs[word_loc_val_def]>>
      IF_CASES_TAC>>fs[]
      >-
        (simp[get_byte_set_byte]>>
        first_x_assum(qspec_then`n` assume_tac)>>rfs[word_loc_val_def])
      >>
      simp[get_byte_set_byte_diff]>>
      first_x_assum(qspec_then`a` mp_tac)>>
      TOP_CASE_TAC>>rfs[word_loc_val_def])
    >-
      (match_mp_tac (GEN_ALL bytes_in_mem_asm_write_bytearray_lemma|>REWRITE_RULE[AND_IMP_INTRO])>>HINT_EXISTS_TAC>>fs[]>>
      rw[APPLY_UPDATE_THM]>>
      rfs[])))

val state_rel_ignore_io_events = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
    state_rel (mc_conf,code2,labs,p,T) (s1 with ffi := io) t1 ms1``,
  full_simp_tac(srw_ss())[state_rel_def] \\ rpt strip_tac
  \\ res_tac \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]);

val compile_correct = Q.prove(
  `!^s1 res (mc_conf: ('a,'state,'b) machine_config) s2 code2 labs t1 ms1.
     (evaluate s1 = (res,s2)) /\ (res <> Error) /\
     s1.ffi.final_event = NONE /\
     backend_correct mc_conf.target /\
     state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
     ?k t2 ms2.
       (evaluate mc_conf s1.ffi (s1.clock + k) ms1 =
          ((case s2.ffi.final_event of NONE => res
            | SOME e => Halt (FFI_outcome e)),
           ms2,s2.ffi))`,
  HO_MATCH_MP_TAC labSemTheory.evaluate_ind \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [labSemTheory.evaluate_def]
  \\ Cases_on `s1.clock = 0` \\ full_simp_tac(srw_ss())[]
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ full_simp_tac(srw_ss())[Once targetSemTheory.evaluate_def]
         \\ metis_tac [state_rel_weaken])
  \\ Cases_on `asm_fetch s1` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ Cases_on `a` \\ full_simp_tac(srw_ss())[]
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ full_simp_tac(srw_ss())[LET_DEF]
  THEN1 (* Asm Inst *)
   (qmatch_assum_rename_tac `asm_fetch s1 = SOME (Asm (Inst i) bytes len)`
    \\ mp_tac IMP_bytes_in_memory_Inst \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Inst i` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
         asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ `~(asm_inst i s1).failed` by (rpt strip_tac \\ full_simp_tac(srw_ss())[])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (imp_res_tac Inst_lemma \\ pop_assum (K all_tac)
      \\ full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def]
      \\ qpat_assum `bytes_in_mem ww bytes' t1.mem
            t1.mem_domain s1.mem_domain` mp_tac
      \\ match_mp_tac bytes_in_mem_IMP_memory \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac \\ rpt strip_tac \\ full_simp_tac(srw_ss())[asm_def]
      THEN1 (full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,asm_inst_consts])
      THEN1 (full_simp_tac(srw_ss())[shift_interfer_def])
      \\ full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ match_mp_tac state_rel_shift_interfer
      \\ imp_res_tac Inst_lemma \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k` mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l - 1` \\ full_simp_tac(srw_ss())[]
    \\ `^s1.clock - 1 + k + l = ^s1.clock + (k + l - 1)` by decide_tac
    \\ full_simp_tac(srw_ss())[asm_inst_consts])
  THEN1 (* Asm JumpReg *)
   (Cases_on `read_reg n' s1` \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac `read_reg r1 s1 = Loc l1 l2`
    \\ Cases_on `loc_to_pc l1 l2 s1.code` \\ full_simp_tac(srw_ss())[]
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`JumpReg r1`]MP_TAC
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[IMP_bytes_in_memory_JumpReg,asmSemTheory.upd_pc_def,
             asmSemTheory.assert_def]
      \\ imp_res_tac IMP_bytes_in_memory_JumpReg \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.read_reg_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_ASSUM `xx = t1.regs r1` (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[alignmentTheory.aligned_bitwise_and]
      \\ match_mp_tac pos_val_MOD_0 \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,`(asm (JumpReg r1)
            (t1.pc + n2w (LENGTH (mc_conf.target.encode (JumpReg r1)))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def,dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
      \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ Q.PAT_ASSUM `xx = t1.regs r1` (fn th => full_simp_tac(srw_ss())[GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ RES_TAC \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ res_tac \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[alignmentTheory.aligned_bitwise_and]
      \\ match_mp_tac pos_val_MOD_0 \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ srw_tac[][]
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `t2` \\ full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def])
  THEN1 (* Jump *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)`
    \\ Cases_on `get_pc_value jtarget s1` \\ full_simp_tac(srw_ss())[]
    \\ mp_tac IMP_bytes_in_memory_Jump \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.encode jj))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ Cases_on `jtarget` \\ full_simp_tac(srw_ss())[]
      \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ imp_res_tac lab_lookup_IMP \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ srw_tac[][]
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ full_simp_tac(srw_ss())[]
    \\ Q.EXISTS_TAC `t2` \\ full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def])
  THEN1 (* JumpCmp *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)`
    \\ `word_cmp cmp (read_reg rr s1) (labSem$reg_imm ri s1) =
        SOME (asmSem$word_cmp cmp (read_reg rr t1) (reg_imm ri t1))` by
     (Cases_on `word_cmp cmp (read_reg rr s1) (reg_imm ri s1)` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac word_cmp_lemma \\ full_simp_tac(srw_ss())[])
    \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `word_cmp cmp (read_reg rr t1) (reg_imm ri t1)` \\ full_simp_tac(srw_ss())[]
    THEN1
     (Cases_on `get_pc_value jtarget s1` \\ full_simp_tac(srw_ss())[]
      \\ mp_tac IMP_bytes_in_memory_JumpCmp \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac IMP_IMP \\ strip_tac
      THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
      \\ rpt strip_tac \\ pop_assum mp_tac
      \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
      \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
           asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
        \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
        \\ imp_res_tac bytes_in_mem_IMP
        \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
        \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
        \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def])
      \\ rpt strip_tac
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
           `code2`,`labs`,
           `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.encode jj))) t1)`,`ms2`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (unabbrev_all_tac
        \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
               asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
               labSemTheory.assert_def,asm_def,
               jump_to_offset_def]
        \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
        \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
              WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
        \\ Cases_on `jtarget` \\ full_simp_tac(srw_ss())[]
        \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ imp_res_tac lab_lookup_IMP \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
      \\ rpt strip_tac
      \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ srw_tac[][]
      \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
      \\ Q.EXISTS_TAC `k + l' - 1` \\ full_simp_tac(srw_ss())[]
      \\ Q.EXISTS_TAC `t2` \\ full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def])
    \\ mp_tac (IMP_bytes_in_memory_JumpCmp_1) \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
             labSemTheory.upd_reg_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ rpt strip_tac \\ res_tac \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l' - 1` \\ full_simp_tac(srw_ss())[]
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by decide_tac \\ full_simp_tac(srw_ss())[])
  THEN1 (* Call *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Call lab) x1 x2 x3)`
    \\ Cases_on `lab`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Call (Lab l1 l2)) l bytes len)`
    \\ (Q.SPECL_THEN [`Lab l1 l2`,`len`]mp_tac
            (Q.GENL[`n`,`ww`]IMP_bytes_in_memory_Call))
    \\ match_mp_tac IMP_IMP \\ strip_tac \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
  THEN1 (* LocValue *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (LocValue reg lab) x1 x2 x3)`
    \\ Cases_on `lab`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) ww bytes len)`
    \\ full_simp_tac(srw_ss())[lab_to_loc_def]
    \\ mp_tac (Q.INST [`l`|->`ww`,`n`|->`len`]
               IMP_bytes_in_memory_LocValue) \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def]
           \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Loc reg lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_nop) \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asm_step_nop_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_def,upd_pc_def,upd_reg_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[shift_interfer_def,state_rel_def,asm_def,LET_DEF]
      \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,asm_def,
             jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
             labSemTheory.upd_reg_def]
      \\ full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ full_simp_tac(srw_ss())[APPLY_UPDATE_THM] \\ srw_tac[][word_loc_val_def]
      \\ res_tac \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac lab_lookup_IMP \\ srw_tac[][])
    \\ rpt strip_tac
    \\ full_simp_tac(srw_ss())[inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN`s1.clock - 1 + k`mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l - 1` \\ full_simp_tac(srw_ss())[]
    \\ `s1.clock - 1 + k + l = s1.clock + (k + l - 1)` by decide_tac
    \\ full_simp_tac(srw_ss())[])
  THEN1 (* CallFFI *)
   (qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm (CallFFI n') l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)`
    \\ Cases_on `s1.regs s1.len_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.link_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.ptr_reg` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `read_bytearray c' (w2n c) s1.mem s1.mem_domain s1.be`
    \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac
         `read_bytearray c1 (w2n c2) s1.mem s1.mem_domain s1.be = SOME x`
    \\ qmatch_assum_rename_tac `s1.regs s1.link_reg = Loc n1 n2`
    \\ Cases_on `call_FFI s1.ffi index x` \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac
         `call_FFI s1.ffi index x = (new_ffi,new_bytes)`
    \\ mp_tac IMP_bytes_in_memory_CallFFI \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def]
           \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
           asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
           asmSemTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ Cases_on `loc_to_pc n1 n2 s1.code` \\ full_simp_tac(srw_ss())[]
    \\ qmatch_assum_rename_tac `loc_to_pc n1 n2 s1.code = SOME new_pc`
    \\ `mc_conf.target.get_pc ms2 = p - n2w ((3 + index) * ffi_offset)` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[backend_correct_def]
      \\ Q.PAT_ASSUM `!ms s. mc_conf.target.state_rel s ms ==> bbb` imp_res_tac
      \\ full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asm_def,asmSemTheory.jump_to_offset_def,
           asmSemTheory.upd_pc_def]
      \\ rewrite_tac [GSYM word_sub_def,WORD_SUB_PLUS,
           GSYM word_add_n2w,WORD_ADD_SUB]) \\ full_simp_tac(srw_ss())[]
    \\ `has_io_index index s1.code` by
          (imp_res_tac IMP_has_io_index \\ NO_TAC)
    \\ `~(mc_conf.target.get_pc ms2 IN mc_conf.prog_addresses) /\
        ~(mc_conf.target.get_pc ms2 = mc_conf.halt_pc) /\
        (find_index (mc_conf.target.get_pc ms2) mc_conf.ffi_entry_pcs 0 =
           SOME index)` by
      (full_simp_tac(srw_ss())[state_rel_def]
       \\ Q.PAT_ASSUM `!kk. has_io_index kk s1.code ==> bbb` imp_res_tac
       \\ rev_full_simp_tac(srw_ss())[] \\ NO_TAC)
    \\ `(mc_conf.target.get_reg ms2 mc_conf.ptr_reg = t1.regs mc_conf.ptr_reg) /\
        (mc_conf.target.get_reg ms2 mc_conf.len_reg = t1.regs mc_conf.len_reg) /\
        !a. a IN mc_conf.prog_addresses ==>
            (mc_conf.target.get_byte ms2 a = t1.mem a)` by
     (full_simp_tac(srw_ss())[GSYM PULL_FORALL]
      \\ full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[backend_correct_def]
      \\ Q.PAT_ASSUM `!ms s. mc_conf.target.state_rel s ms ==> bbb` imp_res_tac
      \\ full_simp_tac(srw_ss())[backend_correct_def |> REWRITE_RULE [GSYM reg_ok_def]]
      \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[state_rel_def,asm_def,
           jump_to_offset_def,asmSemTheory.upd_pc_def,AND_IMP_INTRO]
      \\ rpt strip_tac \\ first_x_assum match_mp_tac
      \\ full_simp_tac(srw_ss())[reg_ok_def] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[]
    \\ `(t1.regs mc_conf.ptr_reg = c1) /\
        (t1.regs mc_conf.len_reg = c2)` by
     (full_simp_tac(srw_ss())[state_rel_def]
      \\ Q.PAT_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (fn th =>
          MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).ptr_reg` th)
          \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).len_reg` th))
      \\ Q.PAT_ASSUM `xx = s1.ptr_reg` (ASSUME_TAC o GSYM)
      \\ Q.PAT_ASSUM `xx = s1.len_reg` (ASSUME_TAC o GSYM)
      \\ full_simp_tac(srw_ss())[word_loc_val_def] \\ NO_TAC)
    \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac read_bytearray_state_rel \\ full_simp_tac(srw_ss())[]
    \\ reverse(Cases_on `new_ffi.final_event = NONE`) THEN1
     (imp_res_tac evaluate_pres_final_event \\ full_simp_tac(srw_ss())[]
      \\ rev_full_simp_tac(srw_ss())[]
      \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ rpt strip_tac
      \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[ADD_ASSOC]
      \\ once_rewrite_tac [targetSemTheory.evaluate_def]
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[shift_interfer_def,LET_DEF]
      \\ BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[])
      \\ full_simp_tac(srw_ss())[]
    \\ FIRST_X_ASSUM (Q.SPECL_THEN [
         `shift_interfer l' mc_conf with
          ffi_interfer := shift_seq 1 mc_conf.ffi_interfer`,
         `code2`,`labs`,
         `t1 with <| pc := p + n2w (pos_val new_pc 0 (code2:'a sec list)) ;
                     mem := asm_write_bytearray c1 new_bytes t1.mem ;
                     regs := \a. get_reg_value (s1.io_regs 0 a) (t1.regs a) I |>`,
         `mc_conf.ffi_interfer 0 index new_bytes ms2`]mp_tac)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (rpt strip_tac
      THEN1 (full_simp_tac(srw_ss())[backend_correct_def,shift_interfer_def]
             \\ metis_tac [])
      \\ unabbrev_all_tac
      \\ imp_res_tac bytes_in_mem_asm_write_bytearray
      \\ full_simp_tac(srw_ss())[state_rel_def,shift_interfer_def,
             asm_def,jump_to_offset_def,
             asmSemTheory.upd_pc_def] \\ rev_full_simp_tac(srw_ss())[]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ full_simp_tac bool_ss [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[get_pc_value_def]
      \\ `interference_ok (shift_seq l' mc_conf.next_interfer)
            (mc_conf.target.proj t1.mem_domain)` by
               (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def]
                \\ NO_TAC) \\ full_simp_tac(srw_ss())[]
      \\ `p + n2w (pos_val new_pc 0 code2) = t1.regs s1.link_reg` by
       (Q.PAT_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (Q.SPEC_THEN `s1.link_reg`mp_tac)
        \\ full_simp_tac(srw_ss())[word_loc_val_def]
        \\ Cases_on `lab_lookup n1 n2 labs` \\ full_simp_tac(srw_ss())[]
        \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[]
        \\ res_tac \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
      \\ `w2n c2 = LENGTH new_bytes` by
       (imp_res_tac read_bytearray_LENGTH
        \\ imp_res_tac call_FFI_LENGTH \\ full_simp_tac(srw_ss())[])
      \\ res_tac \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac
      THEN1
       (full_simp_tac(srw_ss())[PULL_FORALL,AND_IMP_INTRO]
        \\ rev_full_simp_tac(srw_ss())[]
        \\ Q.PAT_ASSUM `t1.regs s1.ptr_reg = c1` (ASSUME_TAC o GSYM)
        \\ full_simp_tac(srw_ss())[] \\ first_x_assum match_mp_tac
        \\ full_simp_tac(srw_ss())[] \\ qexists_tac `new_io`
        \\ full_simp_tac(srw_ss())[option_ldrop_0])
      THEN1
       (full_simp_tac(srw_ss())[shift_seq_def,PULL_FORALL,AND_IMP_INTRO])
      THEN1 res_tac
      THEN1
       (Cases_on `s1.io_regs 0 r`
        \\ full_simp_tac(srw_ss())[get_reg_value_def,word_loc_val_def])
      \\ qpat_assum `!a.
           byte_align a IN s1.mem_domain ==> bbb` (MP_TAC o Q.SPEC `a`)
      \\ full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
      \\ match_mp_tac (SIMP_RULE std_ss [] CallFFI_bytearray_lemma)
      \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock + k`mp_tac) \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l'` \\ full_simp_tac(srw_ss())[ADD_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`ms2'`] \\ full_simp_tac(srw_ss())[]
    \\ simp_tac std_ss [Once evaluate_def]
    \\ full_simp_tac(srw_ss())[shift_interfer_def]
    \\ full_simp_tac(srw_ss())[AC ADD_COMM ADD_ASSOC,AC MULT_COMM MULT_ASSOC]
    \\ rev_full_simp_tac(srw_ss())[LET_DEF]
    \\ `k + s1.clock - 1 = k + (s1.clock - 1)` by decide_tac
    \\ full_simp_tac(srw_ss())[])
  THEN1 (* Halt *)
   (srw_tac[][]
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l1 l2 l3)`
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l bytes n)`
    \\ mp_tac IMP_bytes_in_memory_Halt \\ full_simp_tac(srw_ss())[]
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (full_simp_tac(srw_ss())[state_rel_def]
           \\ imp_res_tac bytes_in_mem_IMP \\ full_simp_tac(srw_ss())[])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ full_simp_tac(srw_ss())[]
    \\ MATCH_MP_TAC IMP_IMP2 \\ STRIP_TAC THEN1
     (full_simp_tac(srw_ss())[state_rel_def,asm_def,LET_DEF]
      \\ full_simp_tac(srw_ss())[asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
            asmSemTheory.upd_pc_def]
      \\ rev_full_simp_tac(srw_ss())[] \\ unabbrev_all_tac
      \\ full_simp_tac(srw_ss())[asmSemTheory.jump_to_offset_def,
            asmSemTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ unabbrev_all_tac \\ full_simp_tac(srw_ss())[asm_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ srw_tac[][]
    \\ Q.EXISTS_TAC `l'` \\ full_simp_tac(srw_ss())[]
    \\ once_rewrite_tac [evaluate_def] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[shift_interfer_def]
    \\ `mc_conf.target.get_pc ms2 = mc_conf.halt_pc` by
     (full_simp_tac(srw_ss())[backend_correct_def] \\ res_tac
      \\ full_simp_tac(srw_ss())[]
      \\ full_simp_tac(srw_ss())[jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ full_simp_tac(srw_ss())[state_rel_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
           WORD_ADD_SUB] \\ full_simp_tac(srw_ss())[])
    \\ `~(mc_conf.target.get_pc ms2 IN t1.mem_domain)` by
            full_simp_tac(srw_ss())[state_rel_def]
    \\ full_simp_tac(srw_ss())[state_rel_def,jump_to_offset_def,
          asmSemTheory.upd_pc_def]
    \\ Cases_on `s1.regs s1.ptr_reg` \\ full_simp_tac(srw_ss())[]
    \\ `word_loc_val p labs (s1.regs s1.ptr_reg) =
         SOME (t1.regs s1.ptr_reg)` by full_simp_tac(srw_ss())[]
    \\ Cases_on `s1.regs s1.ptr_reg`
    \\ full_simp_tac(srw_ss())[word_loc_val_def] \\ srw_tac[][]
    \\ `s1 = s2` by (Cases_on `t1.regs s1.ptr_reg = 0w`
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]) \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[backend_correct_def]
    \\ res_tac \\ full_simp_tac(srw_ss())[]
    \\ pop_assum (qspec_then `s1.ptr_reg` mp_tac)
    \\ pop_assum (qspec_then `s1.ptr_reg` mp_tac)
    \\ full_simp_tac(srw_ss())[reg_ok_def]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]));

(* relating observable semantics *)

val init_ok_def = Define `
  init_ok (mc_conf, p) s ms <=>
    s.ffi.final_event = NONE /\
    ?code2 labs t1.
      state_rel (mc_conf,code2,labs,p,T) s t1 ms`

val evaluate_ignore_clocks = prove(
  ``evaluate mc_conf ffi k ms = (r1,ms1,st1) /\ r1 <> TimeOut /\
    evaluate mc_conf ffi k' ms = (r2,ms2,st2) /\ r2 <> TimeOut ==>
    (r1,ms1,st1) = (r2,ms2,st2)``,
  srw_tac[][] \\ imp_res_tac evaluate_add_clock \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (qspec_then `k'` mp_tac)
  \\ pop_assum (qspec_then `k` mp_tac)
  \\ full_simp_tac(srw_ss())[AC ADD_ASSOC ADD_COMM])

val machine_sem_EQ_sem = Q.store_thm("machine_sem_EQ_sem",
  `!mc_conf p (ms:'state) ^s1.
     backend_correct mc_conf.target /\
     init_ok (mc_conf,p) s1 ms /\ semantics s1 <> Fail ==>
     machine_sem mc_conf s1.ffi ms = { semantics s1 }`,
  simp[GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 2 strip_tac >>
  full_simp_tac(srw_ss())[init_ok_def] >>
  simp[semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >>
  conj_tac
  >- (
    qx_gen_tac`ffi`>>strip_tac>> full_simp_tac(srw_ss())[]
    \\ drule compile_correct \\ full_simp_tac(srw_ss())[]
    \\ `r ≠ Error` by (Cases_on`r`>>every_case_tac>>
                    full_simp_tac(srw_ss())[]>>metis_tac[FST]) >> simp[]
    \\ disch_then drule
    \\ imp_res_tac state_rel_clock
    \\ pop_assum (qspec_then `k` assume_tac)
    \\ disch_then drule \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[machine_sem_def,EXTENSION] \\ full_simp_tac(srw_ss())[IN_DEF]
    \\ Cases \\ full_simp_tac(srw_ss())[machine_sem_def]
    THEN1 (disj1_tac \\ qexists_tac `k+k'` \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
    THEN1
     (eq_tac THEN1
       (srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ drule (GEN_ALL evaluate_ignore_clocks) \\ full_simp_tac(srw_ss())[]
        \\ pop_assum (K all_tac)
        \\ disch_then drule \\ full_simp_tac(srw_ss())[])
      \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
    \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[FST_EQ_EQUIV]
    \\ PairCases_on `z`
    \\ drule (GEN_ALL evaluate_ignore_clocks) \\ full_simp_tac(srw_ss())[]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[]
    \\ pop_assum (K all_tac)
    \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[machine_sem_def,EXTENSION] \\ full_simp_tac(srw_ss())[IN_DEF]
  \\ strip_tac
  \\ Cases \\ full_simp_tac(srw_ss())[machine_sem_def]
  \\ imp_res_tac state_rel_clock
  THEN1 (
    qmatch_abbrev_tac`a ∧ b ⇔ c` >>
    `a` by (
      unabbrev_all_tac >> gen_tac >>
      qspec_then `s1 with clock := k` mp_tac compile_correct >>
      Cases_on`evaluate (s1 with clock := k)`>>simp[]>>
      last_assum(qspec_then`k`mp_tac)>>
      pop_assum mp_tac >> simp_tac(srw_ss())[] >>
      ntac 2 strip_tac >>
      disch_then drule >>
      first_x_assum(qspec_then`k`strip_assume_tac) >>
      disch_then drule >> strip_tac >>
      first_x_assum(qspec_then`k`mp_tac)>>simp[]>>
      strip_tac >>
      spose_not_then strip_assume_tac >>
      Cases_on`r.ffi.final_event`>>full_simp_tac(srw_ss())[]>>
      Cases_on`q`>>full_simp_tac(srw_ss())[]>>
      `∃x y z. evaluate mc_conf s1.ffi k ms = (x,y,z)` by metis_tac[PAIR] >>
      `x = TimeOut` by (
        spose_not_then strip_assume_tac >>
        drule (GEN_ALL evaluate_add_clock) >>
        simp[] >> qexists_tac`k'`>>simp[] ) >>
      full_simp_tac(srw_ss())[] >>
      metis_tac[evaluate_add_clock_io_events_mono,SND,option_CASES,
                IS_SOME_EXISTS,LESS_EQ_EXISTS]) >>
    simp[] >> full_simp_tac(srw_ss())[Abbr`a`] >>
    unabbrev_all_tac >> simp[] >>
    qmatch_abbrev_tac`lprefix_lub l1 l ⇔ l = build_lprefix_lub l2` >>
    `lprefix_chain l1 ∧ lprefix_chain l2` by (
      unabbrev_all_tac >>
      conj_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      metis_tac[
        targetPropsTheory.evaluate_add_clock_io_events_mono,
        labPropsTheory.evaluate_add_clock_io_events_mono
        |> Q.SPEC`s with clock := k` |> SIMP_RULE (srw_ss())[],
        LESS_EQ_EXISTS]) >>
    `equiv_lprefix_chain l1 l2` by (
      simp[equiv_lprefix_chain_thm] >>
      unabbrev_all_tac >> simp[PULL_EXISTS] >>
      ntac 2 (pop_assum kall_tac) >>
      simp[LNTH_fromList,PULL_EXISTS] >>
      simp[GSYM FORALL_AND_THM] >>
      rpt gen_tac >>
      qspec_then `s1 with clock := k` mp_tac compile_correct >>
      Cases_on`evaluate (s1 with clock := k)`>>full_simp_tac(srw_ss())[] >>
      last_assum(qspec_then`k`mp_tac)>>
      pop_assum mp_tac >> simp_tac(srw_ss())[] >>
      ntac 2 strip_tac >>
      disch_then drule >>
      first_x_assum(qspec_then`k`(fn th => assume_tac th >> disch_then drule)) >>
      strip_tac >>
      reverse conj_tac >> strip_tac >- (
        qexists_tac`k+k'`>>simp[] ) >>
      qmatch_assum_abbrev_tac`n < (LENGTH (_ ffi))` >>
      qexists_tac`k`>>simp[] >>
      `ffi.io_events ≼ r.ffi.io_events` by (
        qunabbrev_tac`ffi` >>
        metis_tac[
          targetPropsTheory.evaluate_add_clock_io_events_mono,
          SND,LESS_EQ_EXISTS] ) >>
      full_simp_tac(srw_ss())[IS_PREFIX_APPEND] >>
      simp[EL_APPEND1]) >>
    metis_tac[build_lprefix_lub_thm,unique_lprefix_lub,lprefix_lub_new_chain])
  THEN1 (
    spose_not_then strip_assume_tac >> var_eq_tac >>
    qspec_then `s1 with clock := k` mp_tac compile_correct >>
    Cases_on`evaluate (s1 with clock := k)`>>simp[]>>
    last_assum(qspec_then`k`mp_tac)>>
    pop_assum mp_tac >> simp_tac(srw_ss())[] >> rpt strip_tac >>
    asm_exists_tac >> simp[] >>
    first_x_assum(qspec_then`k`strip_assume_tac) >>
    asm_exists_tac >> simp[] >>
    rpt gen_tac >>
    drule (GEN_ALL evaluate_add_clock) >> simp[] >>
    disch_then kall_tac >>
    first_x_assum(qspec_then`k`mp_tac) >> simp[] >>
    Cases_on`r.ffi.final_event`>>full_simp_tac(srw_ss())[])
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[FST_EQ_EQUIV]
  \\ last_x_assum (qspec_then `k` mp_tac) \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `evaluate (s1 with clock := k)` \\ full_simp_tac(srw_ss())[]
  \\ drule compile_correct
  \\ Cases_on `q = Error` \\ full_simp_tac(srw_ss())[]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (qspec_then `k` assume_tac)
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[] \\ gen_tac
  \\ PairCases_on `z`
  \\ drule (GEN_ALL evaluate_add_clock) \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

(* syntactic properties of remove_labels *)

val good_syntax_def = Define `
  good_syntax mc_conf (code:'a sec list) l = T` (* needs completing *)

val good_syntax_filter_skip = store_thm("good_syntax_filter_skip[simp]",
  ``good_syntax c (filter_skip prog) l = good_syntax c prog l``,
  srw_tac[][good_syntax_def]);

val lines_ok_def = Define`
  (lines_ok c enc labs pos [] = T) ∧
  (lines_ok c enc labs pos (y::ys) ⇔
   line_ok c enc labs pos y ∧
   lines_ok c enc labs (pos + line_length y) ys)`;

val all_enc_ok_cons = Q.store_thm("all_enc_ok_cons",
  `∀ls pos.
   all_enc_ok c enc labs pos (Section k ls::xs) ⇔
   all_enc_ok c enc labs (pos + SUM (MAP line_length ls)) xs ∧
   EVEN (pos + SUM (MAP line_length ls)) ∧
   lines_ok c enc labs pos ls`,
  Induct >> srw_tac[][all_enc_ok_def,lines_ok_def] >>
  simp[] >> metis_tac[]);

val line_similar_sym = Q.store_thm("line_similar_sym",
  `line_similar l1 l2 ⇒ line_similar l2 l1`,
  Cases_on`l1`>>Cases_on`l2`>>EVAL_TAC>>srw_tac[][]);

val code_similar_sym = Q.store_thm("code_similar_sym",
  `∀code1 code2. code_similar code1 code2 ⇒ code_similar code2 code1`,
  Induct >> simp[code_similar_def]
  >> Cases_on`code2`>>simp[code_similar_def]
  >> Cases >> simp[code_similar_def]
  >> Cases_on`h` >> simp[code_similar_def]
  >> srw_tac[][]
  >> match_mp_tac (GEN_ALL (MP_CANON EVERY2_sym))
  >> metis_tac[line_similar_sym]);

val line_similar_refl = Q.store_thm("line_similar_refl[simp]",
  `∀l. line_similar l l`,
  Cases >> EVAL_TAC);

val code_similar_refl = Q.store_thm("code_similar_refl[simp]",
  `∀code. code_similar code code`,
  Induct >> simp[code_similar_def] >>
  Cases >> simp[code_similar_def] >>
  match_mp_tac EVERY2_refl >> simp[]);

val line_similar_pad_section = Q.store_thm("line_similar_pad_section",
  `∀nop n l2 aux l1.
     LIST_REL line_similar l1 (REVERSE aux ++ l2) ⇒
     LIST_REL line_similar l1 (pad_section nop n l2 aux)`,
  cheat
(*
      ho_match_mp_tac pad_section_ind >>
   srw_tac[][pad_section_def] >>
   first_x_assum match_mp_tac >>
   imp_res_tac LIST_REL_LENGTH >> full_simp_tac(srw_ss())[] >>
   qmatch_assum_rename_tac`LIST_REL _ ls (_ ++ _)` >>
   qmatch_assum_abbrev_tac`LENGTH ls = m + _` >>
   qispl_then[`m`,`ls`]strip_assume_tac TAKE_DROP >>
   ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
   pop_assum(SUBST1_TAC o SYM) >>
   match_mp_tac EVERY2_APPEND_suff >>
   qispl_then[`m`,`ls`]strip_assume_tac TAKE_DROP >>
   pop_assum(fn th => last_x_assum(fn a =>
     assume_tac(ONCE_REWRITE_RULE[SYM th]a))) >>
   drule LIST_REL_APPEND_IMP >>
   (discharge_hyps >- simp[] ) >>
   strip_tac >> full_simp_tac(srw_ss())[] >>
   qmatch_rename_tac`line_similar line _` >>
   Cases_on`line`>>full_simp_tac(srw_ss())[line_similar_def] *));

val code_similar_pad_code = Q.store_thm("code_similar_pad_code",
  `∀code1 code2.
   code_similar code1 code2 ⇒
   code_similar code1 (pad_code nop code2)`,
  cheat
(*
  Induct
  >- ( Cases >> simp[code_similar_def,pad_code_def] )
  >> Cases_on`code2` >- simp[code_similar_def]
  >> Cases >> simp[code_similar_def]
  >> Cases_on`h` >> simp[code_similar_def,pad_code_def]
  >> strip_tac >> rveq
  >> match_mp_tac line_similar_pad_section
  >> simp[] *));

val code_similar_enc_sec_list = Q.store_thm("code_similar_enc_sec_list[simp]",
  `∀code1 code2 n.
     code_similar (enc_sec_list n code1) code2 ⇔
     code_similar code1 code2`,
   simp[enc_sec_list_def]
   >> Induct >> simp[]
   >> Cases_on`code2`>>simp[code_similar_def]
   >> Cases_on`h`>>simp[code_similar_def]
   >> Cases>>simp[code_similar_def,enc_sec_def]
   >> cheat);

val label_zero_def = Define`
  (label_zero (Label _ _ n) ⇔ n = 0) ∧
  (label_zero _ ⇔ T)`;
val _ = export_rewrites["label_zero_def"];

val sec_label_zero_def = Define`
  sec_label_zero (Section _ ls) = EVERY label_zero ls`;

val pos_val_0_0 = Q.store_thm("pos_val_0_0",
  `EVERY sec_label_zero ls ⇒ pos_val 0 0 ls = 0`,
  Induct_on`ls`>>srw_tac[][pos_val_def]>>full_simp_tac(srw_ss())[]
  >> Cases_on`h`>>srw_tac[][pos_val_def]
  >> Induct_on`l`
  >> srw_tac[][pos_val_def]
  >> full_simp_tac(srw_ss())[sec_label_zero_def]
  >> Cases_on`h`>>full_simp_tac(srw_ss())[]
  >> srw_tac[][line_length_def]);

val EVERY_label_zero_pad_section = Q.store_thm("EVERY_label_zero_pad_section[simp]",
 `∀nop k xs aux. EVERY label_zero aux ⇒
       EVERY label_zero (pad_section nop k xs aux)`,
  cheat (* ho_match_mp_tac pad_section_ind
  >> srw_tac[][pad_section_def]
  >> srw_tac[][EVERY_REVERSE] *));

val EVERY_sec_label_zero_pad_code = Q.store_thm("EVERY_sec_label_zero_pad_code[simp]",
  `∀nop ls. EVERY sec_label_zero (pad_code nop ls)`,
  cheat (* ho_match_mp_tac pad_code_ind
  >> srw_tac[][pad_code_def]
  >> srw_tac[][sec_label_zero_def] *));

val sec_length_add = Q.store_thm("sec_length_add",
  `∀ls n m. sec_length ls (n+m) = sec_length ls n + m`,
  ho_match_mp_tac sec_length_ind >>
  simp[sec_length_def]);

val code_similar_nil = Q.store_thm("code_similar_nil",
  `(code_similar [] l ⇔ l = []) ∧
   (code_similar l [] ⇔ l = [])`,
   Cases_on`l`>>EVAL_TAC);

val code_similar_loc_to_pc = Q.store_thm("code_similar_loc_to_pc",
  `∀l1 l2 c1 c2. code_similar c1 c2 ⇒
     loc_to_pc l1 l2 c1 = loc_to_pc l1 l2 c2`,
  ho_match_mp_tac loc_to_pc_ind
  >> simp[code_similar_nil]
  >> srw_tac[][]
  >> Cases_on`c2`>>full_simp_tac(srw_ss())[code_similar_def]
  >> Cases_on`h`>>full_simp_tac(srw_ss())[code_similar_def]
  >> Cases_on`xs`>>full_simp_tac(srw_ss())[]
  >- (
    srw_tac[][Once loc_to_pc_def]
    >> srw_tac[][Once loc_to_pc_def,SimpRHS]
    >> first_x_assum (match_mp_tac o MP_CANON)
    >> full_simp_tac(srw_ss())[] )
  \\ rveq
  \\ simp[Once loc_to_pc_def]
  \\ simp[Once loc_to_pc_def,SimpRHS]
  \\ match_mp_tac COND_CONG \\ simp[]
  \\ disch_then assume_tac
  \\ match_mp_tac COND_CONG \\ simp[]
  \\ conj_asm1_tac >- (
    Cases_on`h`>>Cases_on`y`>>full_simp_tac(srw_ss())[line_similar_def] )
  \\ disch_then assume_tac
  \\ match_mp_tac COND_CONG
  \\ conj_asm1_tac >- (
    Cases_on`h`>>Cases_on`y`>>full_simp_tac(srw_ss())[line_similar_def] )
  \\ srw_tac[][] >> full_simp_tac(srw_ss())[] >>
  rveq >> rev_full_simp_tac(srw_ss())[]
  \\ TRY (ntac 2 AP_THM_TAC >> AP_TERM_TAC)
  \\ first_x_assum (match_mp_tac o MP_CANON)
  \\ srw_tac[][code_similar_def]);

val LENGTH_pad_bytes = Q.store_thm("LENGTH_pad_bytes",
  `0 < LENGTH nop ∧ LENGTH bytes ≤ l ⇒
    LENGTH (pad_bytes bytes l nop) = l`,
  srw_tac[][pad_bytes_def] >> srw_tac[][] >> fsrw_tac[ARITH_ss][]
  \\ match_mp_tac LENGTH_TAKE
  \\ simp[LENGTH_FLAT,SUM_MAP_LENGTH_REPLICATE]
  \\ Cases_on`LENGTH nop`>>full_simp_tac(srw_ss())[]>>simp[MULT,Once MULT_COMM]);

val line_ok_alignment = Q.store_thm("line_ok_alignment",
  `∀c enc labs pos line.
   enc_ok enc c
   ∧ line_ok c enc labs pos line
   ∧ ODD (line_length line)
   ⇒ c.code_alignment = 0`,
  ho_match_mp_tac line_ok_ind
  \\ srw_tac[][line_ok_def,line_length_def,LET_THM]
  \\ full_simp_tac(srw_ss())[enc_ok_def]
  \\ first_x_assum drule
  \\ full_simp_tac(srw_ss())[enc_with_nop_thm]
  \\ rveq >> full_simp_tac(srw_ss())[]
  \\ srw_tac[][]
  \\ spose_not_then (assume_tac o MATCH_MP (#2(EQ_IMP_RULE (SPEC_ALL EXP2_EVEN))))
  \\ rev_full_simp_tac(srw_ss())[LENGTH_FLAT_REPLICATE]
  \\ full_simp_tac(srw_ss())[ODD_ADD,ODD_EVEN,EVEN_MULT]
  \\ imp_res_tac EXP_IMP_ZERO_LT
  \\ imp_res_tac MOD_EQ_0_DIVISOR
  \\ full_simp_tac(srw_ss())[EVEN_MULT]);

val has_odd_inst_alignment = Q.store_thm("has_odd_inst_alignment",
  `∀c enc labs pos code.
   enc_ok enc c
   ∧ all_enc_ok c enc labs pos code
   ∧ has_odd_inst code
   ⇒ c.code_alignment = 0`,
  ho_match_mp_tac all_enc_ok_ind
  \\ simp[all_enc_ok_def,has_odd_inst_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ metis_tac[line_ok_alignment,ODD_EVEN]);

val enc_secs_again_IMP_similar = prove(
  ``enc_secs_again pos labs enc code = (code1,ok) ==> code_similar code code1``,
  cheat);

val line_similar_trans = prove(
  ``line_similar x y /\ line_similar y z ==> line_similar x z``,
  Cases_on `x` \\ Cases_on `y` \\ Cases_on `z` \\ fs[line_similar_def]);

val EVERY2_TRANS = prove(
  ``!xs ys zs. EVERY2 P xs ys /\ EVERY2 P ys zs /\
               (!x y z. P x y /\ P y z ==> P x z) ==> EVERY2 P xs zs``,
  Induct \\ fs [PULL_EXISTS] \\ rw [] \\ res_tac \\ fs []);

val code_similar_trans = store_thm("code_similar_trans",
  ``!c1 c2 c3. code_similar c1 c2 /\ code_similar c2 c3 ==> code_similar c1 c3``,
  HO_MATCH_MP_TAC code_similar_ind \\ fs [] \\ rw []
  \\ Cases_on `c3` \\ fs [code_similar_def] \\ rw []
  \\ Cases_on `h` \\ fs [code_similar_def] \\ rw []
  \\ metis_tac [line_similar_trans,EVERY2_TRANS]);

val lines_upd_lab_len_AUX = prove(
  ``!l aux pos.
      REVERSE aux ++ lines_upd_lab_len pos l [] =
      lines_upd_lab_len pos l aux``,
  Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ simp_tac std_ss [lines_upd_lab_len_def,LET_DEF]
  \\ pop_assum (fn th => once_rewrite_tac [GSYM th]) \\ fs []) |> GSYM

val line_similar_lines_upd_lab_len = prove(
  ``!l aux pos l1.
      LIST_REL line_similar (lines_upd_lab_len pos l []) l1 =
      LIST_REL line_similar l l1``,
  Induct \\ fs [lines_upd_lab_len_def]
  \\ Cases \\ fs [lines_upd_lab_len_def]
  \\ once_rewrite_tac [lines_upd_lab_len_AUX]
  \\ fs [] \\ rw [] \\ eq_tac \\ rw []
  \\ Cases_on `y` \\ fs [line_similar_def]);

val code_similar_upd_lab_len = prove(
  ``!code pos code1.
      code_similar (upd_lab_len pos code) code1 = code_similar code code1``,
  Induct \\ fs [code_similar_def] \\ Cases
  \\ Cases_on `code1` \\ fs [upd_lab_len_def,code_similar_def]
  \\ Cases_on `h` \\ fs [upd_lab_len_def,code_similar_def]
  \\ rw [] \\ fs [line_similar_lines_upd_lab_len]);

val enc_secs_again_T_IMP = prove(
  ``enc_secs_again pos (compute_labels pos code l) enc code = (sec_list,T) ==>
    compute_labels pos code l = compute_labels pos sec_list l``,
  cheat);

val pos_val_pad_code = prove(
  ``pos_val x2 0 (pad_code skip sec_list) = pos_val x2 0 sec_list``,
  cheat (* probably needs to assume more *));

val lab_lookup_compute_labels = prove(
  ``loc_to_pc l1 l2 sec_list = SOME x2 ==>
    lab_lookup l1 l2 (compute_labels 0 sec_list l) =
    SOME (pos_val x2 0 sec_list)``,
  cheat);

val remove_labels_loop_thm = Q.prove(
  `∀n c e code l code2 labs.
    remove_labels_loop n c e code l = SOME (code2,labs) ∧
    good_syntax mc_conf code l ∧
    c = mc_conf.target.config ∧
    e = mc_conf.target.encode ∧
    enc_ok mc_conf.target.encode mc_conf.target.config
    ⇒
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    code_similar code code2 /\ (pos_val 0 0 code2 = 0) /\
    (has_odd_inst code2 ⇒ mc_conf.target.config.code_alignment = 0) /\
    !l1 l2 x2.
      loc_to_pc l1 l2 code = SOME x2 ==>
      lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2)`,
  HO_MATCH_MP_TAC remove_labels_loop_ind
  >> rpt gen_tac >> strip_tac
  >> simp[Once remove_labels_loop_def]
  >> rpt gen_tac
  >> split_pair_tac \\ fs []
  >> reverse IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >> strip_tac >> rveq THEN1
   (full_simp_tac(srw_ss())[]
    >> last_x_assum mp_tac
    >> discharge_hyps >- srw_tac[][good_syntax_def]
    >> simp[] >> strip_tac >> fs []
    >> drule enc_secs_again_IMP_similar
    >> metis_tac [code_similar_trans,code_similar_loc_to_pc])
  \\ split_pair_tac \\ fs []
  \\ rpt var_eq_tac \\ fs []
  \\ conj_tac
  THEN1 (match_mp_tac code_similar_pad_code
         \\ imp_res_tac enc_secs_again_IMP_similar
         \\ fs [code_similar_upd_lab_len]
         \\ metis_tac [code_similar_trans,code_similar_sym])
  \\ conj_tac THEN1 (match_mp_tac pos_val_0_0 \\ simp[])
  \\ conj_tac THEN1
   (strip_tac
    \\ match_mp_tac has_odd_inst_alignment
    \\ asm_exists_tac \\ srw_tac[][]
    \\ asm_exists_tac \\ srw_tac[][])
  \\ rw []
  \\ imp_res_tac enc_secs_again_T_IMP
  \\ fs [pos_val_pad_code]
  \\ imp_res_tac enc_secs_again_IMP_similar
  \\ fs [code_similar_upd_lab_len]
  \\ match_mp_tac lab_lookup_compute_labels
  \\ metis_tac [code_similar_trans,code_similar_loc_to_pc]);

val loc_to_pc_enc_sec_list = Q.store_thm("loc_to_pc_enc_sec_list[simp]",
  `∀l1 l2 code.
     loc_to_pc l1 l2 (enc_sec_list e code) = loc_to_pc l1 l2 code`,
  cheat
(*
simp[enc_sec_list_def]
  >> ho_match_mp_tac loc_to_pc_ind
  >> srw_tac[][]
  >> srw_tac[][Once loc_to_pc_def,enc_sec_def]
  >> srw_tac[][Once loc_to_pc_def,SimpRHS]
  >> match_mp_tac EQ_SYM
  >> BasicProvers.TOP_CASE_TAC
  >- full_simp_tac(srw_ss())[]
  >> simp[]
  >> IF_CASES_TAC
  >- full_simp_tac(srw_ss())[enc_line_def]
  >> IF_CASES_TAC
  >- (
    Cases_on`h`>>full_simp_tac(srw_ss())[enc_line_def]
    >> rev_full_simp_tac(srw_ss())[enc_sec_def] >> full_simp_tac(srw_ss())[])
  >> IF_CASES_TAC
  >- ( Cases_on`h`>>full_simp_tac(srw_ss())[enc_line_def,LET_THM] )
  >> IF_CASES_TAC
  >- ( Cases_on`h`>>full_simp_tac(srw_ss())[enc_line_def,LET_THM] )
  >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[enc_sec_def]
  >> BasicProvers.TOP_CASE_TAC >> full_simp_tac(srw_ss())[] *));

val remove_labels_thm = Q.store_thm("remove_labels_thm",
  `good_syntax mc_conf code l /\
   enc_ok mc_conf.target.encode mc_conf.target.config /\
   remove_labels clock mc_conf.target.config mc_conf.target.encode code l =
     SOME (code2,labs) ==>
   all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
   code_similar code code2 /\ (pos_val 0 0 code2 = 0) /\
   (has_odd_inst code2 ⇒ mc_conf.target.config.code_alignment = 0) /\
   !l1 l2 x2.
     loc_to_pc l1 l2 code = SOME x2 ==>
     lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2)`,
  simp[remove_labels_def]
  >> strip_tac
  >> drule (GEN_ALL remove_labels_loop_thm)
  >> disch_then(qspec_then`mc_conf`mp_tac)
  >> discharge_hyps
  >- ( simp[good_syntax_def] )
  >> strip_tac >> simp[] >> full_simp_tac(srw_ss())[]);

(* introducing make_init *)

val set_bytes_def = Define `
  (set_bytes a be [] = 0w) /\
  (set_bytes a be (b::bs) = set_byte a b (set_bytes (a+1w) be bs) be) `

val make_word_def = Define `
  make_word be m (a:'a word) =
    if dimindex (:'a) = 32 then
      Word (set_bytes a be [m a; m (a+1w); m (a+2w); m (a+3w)])
    else
      Word (set_bytes a be [m a; m (a+1w); m (a+2w); m (a+3w);
                            m (a+4w); m (a+5w); m (a+6w); m (a+7w)]) `

val make_init_def = Define `
  make_init mc_conf (ffi:'ffi ffi_state) save_regs io_regs t m (ms:'state) code =
    <| regs       := \k. Word ((t.regs k):'a word)
     ; mem        := m
     ; mem_domain := { t.regs mc_conf.ptr_reg + w |w| w <+ t.regs mc_conf.len_reg }
     ; pc         := 0
     ; be         := mc_conf.target.config.big_endian
     ; ffi        := ffi
     ; io_regs    := \n k. if k IN save_regs then NONE else (io_regs n k)
     ; code       := code
     ; clock      := 0
     ; failed     := F
     ; ptr_reg    := mc_conf.ptr_reg
     ; len_reg    := mc_conf.len_reg
     ; link_reg   := case mc_conf.target.config.link_reg of SOME n => n | _ => 0
     |>`;

val IMP_LEMMA = METIS_PROVE [] ``(a ==> b) ==> (b ==> c) ==> (a ==> c)``

val good_init_state_def = Define `
  good_init_state (mc_conf: ('a,'state,'b) machine_config) t m ms
        ffi_index_limit bytes io_regs save_regs <=>
    mc_conf.target.state_rel t ms /\ ~t.failed /\
    good_dimindex (:'a) /\
    mc_conf.prog_addresses = t.mem_domain /\
    mc_conf.halt_pc NOTIN mc_conf.prog_addresses /\
    t.be = mc_conf.target.config.big_endian /\
    t.pc = mc_conf.target.get_pc ms /\
    t.align = mc_conf.target.config.code_alignment /\
    (1w && mc_conf.target.get_pc ms) = 0w /\
    (n2w (2 ** t.align - 1) && mc_conf.target.get_pc ms) = 0w /\
    reg_ok mc_conf.ptr_reg mc_conf.target.config /\
    reg_ok mc_conf.len_reg mc_conf.target.config /\
    reg_ok (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n)
      mc_conf.target.config /\
    (!index.
       index < ffi_index_limit ==>
       mc_conf.target.get_pc ms - n2w ((3 + index) * ffi_offset) NOTIN
       mc_conf.prog_addresses /\
       mc_conf.target.get_pc ms - n2w ((3 + index) * ffi_offset) <>
       mc_conf.halt_pc /\
       find_index
         (mc_conf.target.get_pc ms - n2w ((3 + index) * ffi_offset))
         mc_conf.ffi_entry_pcs 0 = SOME index) /\
    mc_conf.target.get_pc ms - n2w ffi_offset = mc_conf.halt_pc /\
    interference_ok mc_conf.next_interfer (mc_conf.target.proj t.mem_domain) /\
    (!q n.
       (n2w (2 ** t.align - 1) && q + (n2w n):'a word) = 0w <=>
       n MOD 2 ** t.align = 0) /\
    (!a w.
       byte_align a = w + t.regs mc_conf.ptr_reg /\
       w <+ t.regs mc_conf.len_reg ==>
       a IN t.mem_domain) /\
    (case mc_conf.target.config.link_reg of NONE => T | SOME r => t.lr = r) /\
    code_loaded bytes mc_conf ms /\
    bytes_in_mem (mc_conf.target.get_pc ms) bytes t.mem t.mem_domain
      {w + t.regs mc_conf.ptr_reg | w | w <+ t.regs mc_conf.len_reg} /\
    (!ms2 k index new_bytes t1 x.
       mc_conf.target.state_rel
         (t1 with
          pc := -n2w ((3 + index) * ffi_offset) + mc_conf.target.get_pc ms)
       ms2 /\
       read_bytearray (t1.regs mc_conf.ptr_reg) (LENGTH new_bytes)
         (\a. if a IN t1.mem_domain then SOME (t1.mem a) else NONE) =
       SOME x ==>
       mc_conf.target.state_rel
        (t1 with
         <|regs :=
            (\a.
             get_reg_value
               (if a IN save_regs then NONE else io_regs k a)
               (t1.regs a) I);
           mem := asm_write_bytearray (t1.regs mc_conf.ptr_reg) new_bytes t1.mem;
           pc := t1.regs (case mc_conf.target.config.link_reg of NONE => 0
                  | SOME n => n)|>)
        (mc_conf.ffi_interfer k index new_bytes ms2)) /\
    !a w labs.
      byte_align a = w + t.regs mc_conf.ptr_reg /\
      w <+ t.regs mc_conf.len_reg ==>
      ?w'.
        (a = w' + t.regs mc_conf.ptr_reg /\ w' <+ t.regs mc_conf.len_reg) /\
        word_loc_val_byte (mc_conf.target.get_pc ms) labs m a
          mc_conf.target.config.big_endian = SOME (t.mem a)`

val LESS_find_ffi_index_limit = store_thm("LESS_find_ffi_index_limit",
  ``!code i. has_io_index i code ==> i < find_ffi_index_limit code``,
  recInduct find_ffi_index_limit_ind
  \\ fs [find_ffi_index_limit_def,has_io_index_def]
  \\ rpt strip_tac \\ CASE_TAC \\ fs [] \\ CASE_TAC \\ fs []);

val aligned_1_intro = prove(
  ``((1w && w) = 0w) <=> aligned 1 w``,
  fs [alignmentTheory.aligned_bitwise_and]);

val IMP_state_rel_make_init = prove(
  ``good_syntax mc_conf code l /\
    enc_ok mc_conf.target.encode mc_conf.target.config /\
    remove_labels clock mc_conf.target.config mc_conf.target.encode code l =
      SOME (code2,labs) /\
    good_init_state mc_conf t m ms (find_ffi_index_limit code)
      (prog_to_bytes code2) io_regs save_regs ==>
    state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,
        mc_conf.target.get_pc ms,T)
      (make_init mc_conf (ffi:'ffi ffi_state) save_regs io_regs t m ms code) t ms``,
  srw_tac[][] \\ drule remove_labels_thm
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_rel_def,make_init_def,
        word_loc_val_def,PULL_EXISTS]
  \\ full_simp_tac(srw_ss())[good_init_state_def,LESS_find_ffi_index_limit]
  \\ fs [aligned_1_intro]
  \\ `aligned 1 (mc_conf.target.get_pc ms)` by
         fs [alignmentTheory.aligned_bitwise_and]
  \\ fs [alignmentTheory.aligned_add_sub]
  \\ fs [alignmentTheory.aligned_1_lsb]
  \\ cheat (* should be true with current goal *));

val semantics_make_init = save_thm("semantics_make_init",
  machine_sem_EQ_sem |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
  |> UNDISCH |> REWRITE_RULE []
  |> SIMP_RULE std_ss [init_ok_def,PULL_EXISTS,GSYM CONJ_ASSOC,GSYM AND_IMP_INTRO]
  |> SPEC_ALL |> Q.GEN `s1` |> Q.GEN `p`
  |> Q.GEN `t1` |> Q.SPEC `t`
  |> Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).target.get_pc ms`
  |> Q.SPEC `make_init (mc_conf: ('a,'state,'b) machine_config)
       ffi save_regs io_regs t m (ms:'state) code`
  |> SIMP_RULE std_ss [EVAL ``(make_init mc_conf ffi s i t m ms code).ffi``]
  |> UNDISCH |> MATCH_MP (MATCH_MP IMP_LEMMA IMP_state_rel_make_init)
  |> DISCH_ALL |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC]);

val make_init_filter_skip = store_thm("make_init_filter_skip",
  ``semantics (make_init mc_conf ffi save_regs io_regs t m ms (filter_skip code)) =
    semantics (make_init mc_conf ffi save_regs io_regs t m ms code)``,
  match_mp_tac filter_skip_semantics \\ full_simp_tac(srw_ss())[make_init_def]);

val find_ffi_index_limit_filter_skip = store_thm("find_ffi_index_limit_filter_skip",
  ``!code. find_ffi_index_limit (filter_skip code) = find_ffi_index_limit code``,
  recInduct find_ffi_index_limit_ind
  \\ fs [lab_filterTheory.filter_skip_def,find_ffi_index_limit_def]
  \\ rpt strip_tac \\ every_case_tac
  \\ fs [lab_filterTheory.not_skip_def,find_ffi_index_limit_def]);

val semantics_compile = store_thm("semantics_compile",
  ``ffi.final_event = NONE /\
    backend_correct mc_conf.target /\
    good_syntax mc_conf code c.labels /\
    c.asm_conf = mc_conf.target.config /\
    c.encoder = mc_conf.target.encode /\
    compile c code = SOME (bytes,ffi_limit) /\
    good_init_state mc_conf t m ms ffi_limit bytes io_regs save_regs /\
    semantics (make_init mc_conf ffi save_regs io_regs t m ms code) <> Fail ==>
    machine_sem mc_conf ffi ms =
    {semantics (make_init mc_conf ffi save_regs io_regs t m ms code)}``,
  full_simp_tac(srw_ss())[compile_def,compile_lab_def,GSYM AND_IMP_INTRO]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [GSYM make_init_filter_skip] \\ srw_tac[][]
  \\ match_mp_tac (GEN_ALL semantics_make_init) \\ full_simp_tac(srw_ss())[]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `x1`
  \\ qexists_tac `x0`
  \\ qexists_tac `c.init_clock`
  \\ full_simp_tac(srw_ss())[backend_correct_def]
  \\ full_simp_tac(srw_ss())[find_ffi_index_limit_filter_skip])

val _ = export_theory();
