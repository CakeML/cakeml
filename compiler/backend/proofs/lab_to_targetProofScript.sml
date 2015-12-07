open preamble ffiTheory
     wordSemTheory labSemTheory labPropsTheory
     lab_to_targetTheory
     asmTheory asmSemTheory asmPropsTheory
     targetSemTheory targetPropsTheory;

val _ = new_theory "lab_to_targetProof";

(* TODO: move *)

val call_FFI_LENGTH = prove(
  ``(call_FFI st index x = (new_st,new_bytes)) ==>
    (LENGTH x = LENGTH new_bytes)``,
  fs [call_FFI_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ rw [] \\ fs [listTheory.LENGTH_MAP]);

val SUM_REPLICATE = store_thm("SUM_REPLICATE",
  ``!n k. SUM (REPLICATE n k) = n * k``,
  Induct \\ fs [REPLICATE,MULT_CLAUSES,AC ADD_COMM ADD_ASSOC]);

val asm_failed_ignore_new_pc = store_thm("asm_failed_ignore_new_pc",
  ``!i v w s. (asm i w s).failed <=> (asm i v s).failed``,
  Cases \\ fs [asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ rw [] \\ fs []);

val asm_mem_ignore_new_pc = store_thm("asm_mem_ignore_new_pc",
  ``!i v w s. (asm i w s).mem = (asm i v s).mem``,
  Cases \\ fs [asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
  \\ rw [] \\ fs []);

val FST_EQ_EQUIV = prove(
  ``(FST x = y) <=> ?z. x = (y,z)``,
  Cases_on `x` \\ fs []);

local
  val SND_read_mem_word_consts = prove(
    ``!n a s. ((SND (read_mem_word a n s)).be = s.be) /\
              ((SND (read_mem_word a n s)).lr = s.lr) /\
              ((SND (read_mem_word a n s)).align = s.align) /\
              ((SND (read_mem_word a n s)).mem_domain = s.mem_domain)``,
    Induct \\ fs [read_mem_word_def,LET_DEF]
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ fs [assert_def])
  val write_mem_word_consts = prove(
    ``!n a w s. ((write_mem_word a n w s).be = s.be) /\
                ((write_mem_word a n w s).lr = s.lr) /\
                ((write_mem_word a n w s).align = s.align) /\
                ((write_mem_word a n w s).mem_domain = s.mem_domain)``,
    Induct \\ fs [write_mem_word_def,LET_DEF,assert_def,upd_mem_def])
in
  val asm_consts = store_thm("asm_consts[simp]",
    ``!i w s. ((asm i w s).be = s.be) /\
              ((asm i w s).lr = s.lr) /\
              ((asm i w s).align = s.align) /\
              ((asm i w s).mem_domain = s.mem_domain)``,
    Cases \\ fs [asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
    \\ TRY (Cases_on `i'`) \\ fs [inst_def]
    \\ fs [asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def]
    \\ TRY (Cases_on `m`)
    \\ TRY (Cases_on `a`) \\ fs [arith_upd_def,mem_op_def]
    \\ TRY (Cases_on `b`)
    \\ TRY (Cases_on `r`)
    \\ EVAL_TAC \\ fs [] \\ rw []
    \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
    \\ fs [SND_read_mem_word_consts,write_mem_word_consts])
end

(* -- *)

val enc_with_nop_def = Define `
  enc_with_nop enc (b:'a asm) bytes =
    ?n. bytes = enc b ++ FLAT (REPLICATE n (enc (asm$Inst Skip)))`

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
  fs [shift_interfer_def,FUN_EQ_THM,shift_seq_def,
      machine_config_component_equality]);

val upd_pc_with_pc = prove(
  ``upd_pc s1.pc s1 = s1:'a asm_state``,
  fs [asm_state_component_equality,upd_pc_def]);

val shift_interfer_twice = store_thm("shift_interfer_twice[simp]",
  ``shift_interfer l' (shift_interfer l c) =
    shift_interfer (l + l') c``,
  fs [shift_interfer_def,shift_seq_def,AC ADD_COMM ADD_ASSOC]);

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
  Induct \\ fs [] THEN1
   (rpt strip_tac \\ Q.LIST_EXISTS_TAC [`0`,`ms1`]
    \\ fs [shift_interfer_0,upd_pc_with_pc])
  \\ rpt strip_tac \\ fs [REPLICATE,bytes_in_memory_APPEND]
  \\ mp_tac evaluate_nop_step \\ fs [] \\ rpt strip_tac
  \\ fs [GSYM PULL_FORALL]
  \\ first_x_assum (mp_tac o
       Q.SPECL [`(upd_pc (s1.pc +
          n2w (LENGTH ((c:('a,'state,'b) machine_config).target.encode
            (Inst Skip)))) s1)`,`ms2`,`shift_interfer l c`])
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [shift_interfer_def,upd_pc_def,interference_ok_def,shift_seq_def])
  \\ rpt strip_tac
  \\ `(shift_interfer l c).target = c.target` by fs [shift_interfer_def]
  \\ fs [upd_pc_def]
  \\ Q.LIST_EXISTS_TAC [`l'+l`,`ms2'`]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,
       word_add_n2w,AC ADD_COMM ADD_ASSOC,MULT_CLAUSES]
  \\ fs [ADD_ASSOC] \\ rpt strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k`)
  \\ first_x_assum (mp_tac o Q.SPEC `k+l'`)
  \\ fs [AC ADD_COMM ADD_ASSOC]);

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
  fs [asm_step_nop_def] \\ rpt strip_tac
  \\ (asm_step_IMP_evaluate_step
      |> SIMP_RULE std_ss [asm_step_def] |> SPEC_ALL |> mp_tac) \\ fs []
  \\ fs [enc_with_nop_def]
  \\ match_mp_tac IMP_IMP \\ strip_tac THEN1
   (fs [bytes_in_memory_APPEND] \\ Cases_on `i`
    \\ fs [asm_def,upd_pc_def,jump_to_offset_def,upd_reg_def,
           LET_DEF,assert_def] \\ rw [] \\ fs [] \\ rfs [])
  \\ rpt strip_tac \\ fs [GSYM PULL_FORALL]
  \\ Cases_on `?w. i = Jump w` \\ fs []
  THEN1 (fs [asm_def] \\ Q.LIST_EXISTS_TAC [`l`,`ms2`] \\ fs [])
  \\ Cases_on `?c n r w. (i = JumpCmp c n r w) /\
                  word_cmp c (read_reg n s1) (reg_imm r s1)` \\ fs []
  THEN1 (rw [] \\ fs [asm_def] \\ Q.LIST_EXISTS_TAC [`l`,`ms2`] \\ fs [])
  \\ Cases_on `?r. (i = JumpReg r)` \\ fs []
  THEN1 (rw [] \\ fs [asm_def,LET_DEF] \\ Q.LIST_EXISTS_TAC [`l`,`ms2`]
               \\ fs [] \\ rfs [])
  \\ qspecl_then [`n`,`asm i (s1.pc + n2w (LENGTH (c.target.encode i))) s1`,`ms2`,
       `shift_interfer l c`] mp_tac evaluate_nop_steps
  \\ match_mp_tac IMP_IMP \\ strip_tac
  THEN1 (fs [shift_interfer_def] \\ rpt strip_tac
    THEN1 (fs [interference_ok_def,shift_seq_def])
    THEN1
     (Q.ABBREV_TAC `mm = (asm i (s1.pc + n2w (LENGTH (c.target.encode i))) s1).mem`
      \\ fs [Once (asm_mem_ignore_new_pc |> Q.SPECL [`i`,`0w`])]
      \\ `!w. (asm i w s1).pc = w` by (Cases_on `i` \\ fs [asm_def,upd_pc_def])
      \\ fs [bytes_in_memory_APPEND])
    \\ metis_tac [asm_failed_ignore_new_pc])
  \\ rpt strip_tac \\ fs [GSYM PULL_FORALL]
  \\ Q.LIST_EXISTS_TAC [`l+l'`,`ms2'`]
  \\ fs [PULL_FORALL] \\ strip_tac
  \\ first_x_assum (mp_tac o Q.SPEC `k:num`)
  \\ qpat_assum `!k. xx = yy` (mp_tac o Q.SPEC `k+l':num`)
  \\ rpt strip_tac \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ fs [shift_interfer_def]
  \\ qpat_assum `c.target.state_rel xx yy` mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``(x = z) ==> (f x y ==> f z y)``)
  \\ Cases_on `i` \\ fs [asm_def]
  \\ fs [LENGTH_FLAT,SUM_REPLICATE,map_replicate]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]
  THEN1 (Cases_on `i'` \\ fs [inst_def,upd_pc_def]
    \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w])
  \\ fs [jump_to_offset_def,upd_pc_def]
  \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,word_add_n2w]);

(* -- *)

val _ = Parse.temp_overload_on("option_ldrop",``λn l. OPTION_JOIN (OPTION_MAP (LDROP n) l)``)

val option_ldrop_0 = prove(
  ``!ll. option_ldrop 0 ll = ll``,
  Cases \\ fs []);

val option_ldrop_SUC = prove(
  ``!k1 ll. option_ldrop (SUC k1) ll = option_ldrop 1 (option_ldrop k1 ll)``,
  Cases_on `ll` \\ fs []
  \\ REPEAT STRIP_TAC \\ fs [ADD1] \\ fs [LDROP_ADD]
  \\ Cases_on `LDROP k1 x` \\ fs []);

val option_ldrop_option_ldrop = prove(
  ``!k1 ll k2.
      option_ldrop k1 (option_ldrop k2 ll) = option_ldrop (k1 + k2) ll``,
  Induct \\ fs [option_ldrop_0]
  \\ REPEAT STRIP_TAC \\ fs [option_ldrop_SUC,ADD_CLAUSES]);

(*
val option_ldrop_lemma = prove(
  ``(call_FFI index x io = (new_bytes,new_io)) /\ new_io <> NONE ==>
    (new_io = option_ldrop 1 io)``,
  fs [call_FFI_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ rw []
  \\ Q.MATCH_ASSUM_RENAME_TAC `LTL ll <> NONE`
  \\ `(ll = [||]) \/ ?h t. ll = h:::t` by metis_tac [llistTheory.llist_CASES]
  \\ fs [llistTheory.LDROP1_THM]);
*)

val IMP_IMP2 = METIS_PROVE [] ``a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)``

val lab_lookup_def = Define `
  lab_lookup k1 k2 labs =
    case lookup k1 labs of
    | NONE => NONE
    | SOME f => lookup k2 f`

val lab_lookup_IMP = prove(
  ``(lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)``,
  fs [lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC);

val line_ok_def = Define `
  (line_ok (c:'a asm_config) enc labs pos (Label _ _ l) <=>
     EVEN pos /\ (l = 0)) /\
  (line_ok c enc labs pos (Asm b bytes l) <=>
     enc_with_nop enc b bytes /\
     (LENGTH bytes = l) /\ asm_ok b c) /\
  (line_ok c enc labs pos (LabAsm Halt w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + ffi_offset) in
       enc_with_nop enc (Jump w1) bytes /\
       (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c enc labs pos (LabAsm ClearCache w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + 2 * ffi_offset) in
       enc_with_nop enc (Jump w1) bytes /\
       (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c enc labs pos (LabAsm (CallFFI index) w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + (3 + index) * ffi_offset) in
       enc_with_nop enc (Jump w1) bytes /\
       (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c enc labs pos (LabAsm (Call v24) w bytes l) <=>
     F (* Call not yet supported *)) /\
  (line_ok c enc labs pos (LabAsm a w bytes l) <=>
     let target = find_pos (get_label a) labs in
     let w1 = n2w target - n2w pos in
       enc_with_nop enc (lab_inst w1 a) bytes /\
       (LENGTH bytes = l) /\ asm_ok (lab_inst w1 a) c /\
       (case get_label a of Lab l1 l2 => (lab_lookup l1 l2 labs <> NONE)))`

val all_enc_ok_def = Define `
  (all_enc_ok c enc labs pos [] = T) /\
  (all_enc_ok c enc labs pos ((Section k [])::xs) <=>
     EVEN pos /\ all_enc_ok c enc labs pos xs) /\
  (all_enc_ok c enc labs pos ((Section k (y::ys))::xs) <=>
     line_ok c enc labs pos y /\
     all_enc_ok c enc labs (pos + line_length y) ((Section k ys)::xs))`

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
  Induct \\ fs [bytes_in_mem_def,bytes_in_memory_def]);

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
  Induct \\ fs [pos_val_def] \\ Cases_on `h`
  \\ Induct_on `l` \\ fs [pos_val_def,all_enc_ok_def]
  \\ rpt strip_tac  \\ res_tac  \\ rw []
  \\ Cases_on `h` \\ fs [line_ok_def,line_length_def,is_Label_def]);

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
  THEN1 (Cases_on `code1` \\ fs [code_similar_def,asm_fetch_aux_def])
  THEN1
   (Cases_on `code1` \\ fs [code_similar_def]
    \\ Cases_on `h` \\ fs [code_similar_def]
    \\ Cases_on `l` \\ fs [asm_fetch_aux_def,pos_val_def] \\ rw []
    \\ fs [prog_to_bytes_def,all_enc_ok_def] \\ metis_tac [])
  \\ Cases_on `code1` \\ fs [code_similar_def]
  \\ Cases_on `h` \\ fs [code_similar_def]
  \\ Cases_on`l` \\ fs [asm_fetch_aux_def,pos_val_def]
  \\ rpt var_eq_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `line_similar x1 x2`
  \\ Q.MATCH_ASSUM_RENAME_TAC `LIST_REL line_similar ys1 ys2`
  \\ `is_Label x2 = is_Label x1` by
    (Cases_on `x1` \\ Cases_on `x2` \\ fs [line_similar_def,is_Label_def])
  \\ fs [] \\ Cases_on `is_Label x1` \\ fs []
  THEN1
   (fs [prog_to_bytes_def,LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
    \\ fs [all_enc_ok_def,code_similar_def] \\ rpt strip_tac
    \\ fs [prog_to_bytes_def,LET_DEF]
    \\ Cases_on `x2` \\ fs [line_ok_def,is_Label_def] \\ rw []
    \\ fs [line_length_def,line_bytes_def]
    \\ fs [AC ADD_COMM ADD_ASSOC])
  \\ Cases_on `pc = 0` \\ fs [] \\ rw []
  THEN1
   (fs [listTheory.LENGTH_NIL] \\ qexists_tac `x2`
    \\ fs [prog_to_bytes_def,LET_DEF,all_enc_ok_def] \\ fs [pos_val_0]
    \\ imp_res_tac pos_val_0
    \\ fs [] \\ Cases_on `x2`
    \\ fs [line_ok_def,is_Label_def,line_bytes_def,line_length_def] \\ rw [])
  \\ fs [prog_to_bytes_def,LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc-1`,`i`,
       `(pos + LENGTH (line_bytes x2))`])
  \\ fs [all_enc_ok_def,code_similar_def]
  \\ rpt strip_tac \\ fs []
  \\ Q.LIST_EXISTS_TAC [`line_bytes x2 ++ bs`,
        `j`,`bs2`] \\ fs [] \\ `pc - 1 + 1 = pc` by decide_tac
  \\ fs [AC ADD_COMM ADD_ASSOC])

val prog_to_bytes_lemma = prog_to_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [];

val bytes_in_mem_APPEND = prove(
  ``!xs ys a m md md1.
      bytes_in_mem a (xs ++ ys) m md md1 <=>
      bytes_in_mem a xs m md md1 /\
      bytes_in_mem (a + n2w (LENGTH xs)) ys m md md1``,
  Induct \\ fs [bytes_in_mem_def,ADD1,GSYM word_add_n2w,CONJ_ASSOC]);

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
  \\ mp_tac prog_to_bytes_lemma \\ fs [] \\ rpt strip_tac
  \\ fs [bytes_in_mem_APPEND]
  \\ Q.EXISTS_TAC `j` \\ fs [] \\ decide_tac);

val IMP_bytes_in_memory_JumpReg = prove(
  ``code_similar s1.code code2 /\
    all_enc_ok mc_conf.target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem t1.mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (JumpReg r1) l n)) ==>
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      (mc_conf.target.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    asm_ok (JumpReg r1) (mc_conf: ('a,'state,'b) machine_config).target.config``,
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,enc_with_nop_def] \\ rw [] \\ fs []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,enc_with_nop_def,LET_DEF] \\ rw []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,enc_with_nop_def,LET_DEF] \\ rw []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,LET_DEF] \\ rw []
  \\ Q.EXISTS_TAC `l'` \\ fs [enc_with_nop_def,PULL_EXISTS]
  \\ qexists_tac `n'` \\ fs []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ rw []);

val IMP_bytes_in_memory_Call = prove(
  ``code_similar ^s1.code code2 /\
    all_enc_ok (mc_conf: ('a,'state,'b) machine_config).target.config mc_conf.target.encode labs 0 code2 /\
    bytes_in_mem p (prog_to_bytes code2) t1.mem
      (t1:'a asm_state).mem_domain s1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Call ww) l bytes n)) ==>
    F``,
  rpt strip_tac
  \\ fs [asm_fetch_def,LET_DEF]
  \\ imp_res_tac IMP_bytes_in_memory
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def] \\ rfs []);

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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,LET_DEF] \\ rw []
  \\ Q.EXISTS_TAC `l'` \\ fs [enc_with_nop_def,PULL_EXISTS]
  \\ qexists_tac `n'` \\ fs []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ rw []);

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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,LET_DEF] \\ rw []
  \\ Q.EXISTS_TAC `l` \\ fs [enc_with_nop_def,PULL_EXISTS]
  \\ qexists_tac `n` \\ fs []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ rw []);

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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,enc_with_nop_def,LET_DEF] \\ rw []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
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
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`dm1`,`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def,enc_with_nop_def,LET_DEF] \\ rw []
  \\ fs [LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ imp_res_tac bytes_in_mem_IMP \\ fs []
  \\ fs [asm_fetch_aux_def,prog_to_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val ADD_MODULUS_LEMMA = prove(
  ``!k m n. 0 < n ==> (m + k * n) MOD n = m MOD n``,
  Induct \\ fs [MULT_CLAUSES,ADD_ASSOC,ADD_MODULUS]);

val line_length_MOD_0 = prove(
  ``backend_correct mc_conf.target /\
    (~EVEN p ==> (mc_conf.target.config.code_alignment = 0)) /\
    line_ok mc_conf.target.config mc_conf.target.encode labs p h ==>
    (line_length h MOD 2 ** mc_conf.target.config.code_alignment = 0)``,
  Cases_on `h` \\ TRY (Cases_on `a`) \\ fs [line_ok_def,line_length_def]
  \\ rw [] \\ fs [backend_correct_def,enc_ok_def]
  \\ fs [LET_DEF,enc_with_nop_def] \\ rw [LENGTH_FLAT,LENGTH_REPLICATE]
  \\ qpat_assum `2 ** nn = xx:num` (ASSUME_TAC o GSYM) \\ fs []
  \\ fs [LET_DEF,map_replicate,SUM_REPLICATE] \\ rw []
  \\ res_tac \\ fs [ADD_MODULUS_LEMMA]);

val pos_val_MOD_0_lemma = prove(
  ``(0 MOD 2 ** mc_conf.target.config.code_alignment = 0)``,
  fs []);

val pos_val_MOD_0 = prove(
  ``!x pos code2.
      backend_correct mc_conf.target /\
      (has_odd_inst code2 ==> (mc_conf.target.config.code_alignment = 0)) /\
      (~EVEN pos ==> (mc_conf.target.config.code_alignment = 0)) /\
      (pos MOD 2 ** mc_conf.target.config.code_alignment = 0) /\
      all_enc_ok mc_conf.target.config mc_conf.target.encode labs pos code2 ==>
      (pos_val x pos code2 MOD 2 ** mc_conf.target.config.code_alignment = 0)``,
  reverse (Cases_on `backend_correct mc_conf.target`)
  \\ asm_simp_tac pure_ss [] THEN1 fs []
  \\ HO_MATCH_MP_TAC (theorem "pos_val_ind")
  \\ rpt strip_tac \\ fs [pos_val_def] \\ fs [all_enc_ok_def]
  THEN1 (rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO,has_odd_inst_def])
  \\ Cases_on `is_Label y` \\ fs []
  \\ Cases_on `x = 0` \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [] \\ rw []
  \\ fs [has_odd_inst_def]
  \\ Cases_on `EVEN pos` \\ fs []
  \\ fs [EVEN_ADD]
  \\ `0:num < 2 ** mc_conf.target.config.code_alignment` by fs []
  \\ imp_res_tac (GSYM MOD_PLUS)
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ imp_res_tac line_length_MOD_0 \\ fs [])
  |> Q.SPECL [`x`,`0`,`y`] |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [pos_val_MOD_0_lemma]
  |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];

val state_rel_weaken = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
    state_rel (mc_conf,code2,labs,p,F) s1 t1 ms1``,
  fs [state_rel_def] \\ rpt strip_tac \\ fs [] \\ metis_tac []);

val read_bytearray_state_rel = prove(
  ``!n a x.
      state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 /\
      (read_bytearray a n s1.mem s1.mem_domain s1.be = SOME x) ==>
      (read_bytearray a n
        (\a. if a IN mc_conf.prog_addresses then SOME (t1.mem a) else NONE) =
       SOME x)``,
  Induct
  \\ fs [wordSemTheory.read_bytearray_def,targetSemTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux a s1.mem s1.mem_domain s1.be` \\ fs []
  \\ Cases_on `read_bytearray (a + 1w) n s1.mem s1.mem_domain s1.be` \\ fs []
  \\ res_tac \\ fs [] \\ fs [state_rel_def,mem_load_byte_aux_def]
  \\ Cases_on `s1.mem (byte_align a)` \\ fs [] \\ rw []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `a`) \\ fs []
  \\ rpt strip_tac \\ fs [word_loc_val_def]
  \\ rfs [word_loc_val_byte_def,word_loc_val_def]);

val IMP_has_io_index = prove(
  ``(asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    has_io_index index s1.code``,
  fs [asm_fetch_def]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`)
  \\ Q.SPEC_TAC (`s1.code`,`code`)
  \\ HO_MATCH_MP_TAC asm_code_length_ind \\ rpt strip_tac
  \\ fs [asm_fetch_aux_def,has_io_index_def] \\ res_tac
  \\ Cases_on `is_Label y` \\ fs []
  THEN1 (Cases_on `y` \\ fs [is_Label_def] \\ res_tac)
  \\ Cases_on `pc = 0` \\ fs [] \\ res_tac \\ fs []);

val bytes_in_mem_asm_write_bytearray_lemma = prove(
  ``!xs p.
      (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
      bytes_in_mem p xs m1 d k ==>
      bytes_in_mem p xs m2 d k``,
  Induct \\ fs [bytes_in_mem_def]);

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
  \\ fs [asm_write_bytearray_def]
  \\ REPEAT STRIP_TAC
  \\ fs [wordSemTheory.read_bytearray_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ fs [PULL_FORALL]
  \\ res_tac
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ fs [mem_load_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ rw [combinTheory.APPLY_UPDATE_THM]
  \\ fs [state_rel_def] \\ res_tac);

val write_bytearray_NOT_Loc = prove(
  ``!xs c1 s1 a c.
      (s1.mem a = Word c) ==>
      (write_bytearray c1 xs s1.mem s1.mem_domain s1.be) a <> Loc n n0``,
  Induct \\ fs [write_bytearray_def,mem_store_byte_aux_def]
  \\ rpt strip_tac \\ res_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ fs [labSemTheory.upd_mem_def] \\ rw [] \\ fs [APPLY_UPDATE_THM]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rfs []);

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
  \\ fs [asm_write_bytearray_def,write_bytearray_def,wordSemTheory.read_bytearray_def]
  \\ rpt strip_tac
  \\ Cases_on `mem_load_byte_aux c1 s1.mem s1.mem_domain s1.be` \\ fs []
  \\ Cases_on `read_bytearray (c1 + 1w) (LENGTH xs) s1.mem s1.mem_domain s1.be`
  \\ fs [] \\ rw []
  \\ qmatch_assum_rename_tac
       `read_bytearray (c1 + 1w) (LENGTH xs) s1.mem s1.mem_domain s1.be = SOME y`
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`y`,`c1+1w`,`t1`,`s1`])
  \\ fs [] \\ rpt strip_tac \\ fs [mem_store_byte_aux_def]
  \\ reverse (Cases_on `(write_bytearray (c1 + 1w)
       xs s1.mem s1.mem_domain mc_conf.target.config.big_endian) (byte_align c1)`)
  \\ fs [] THEN1
   (fs [mem_load_byte_aux_def]
    \\ Cases_on `s1.mem (byte_align c1)` \\ fs [] \\ rw []
    \\ imp_res_tac write_bytearray_NOT_Loc \\ rfs [] \\ fs [])
  \\ `byte_align c1 IN s1.mem_domain` by
    (fs [mem_load_byte_aux_def] \\ every_case_tac \\ fs [])
  \\ fs [labSemTheory.upd_mem_def,word_loc_val_byte_def,APPLY_UPDATE_THM]
  \\ Cases_on `a = c1` \\ fs [word_loc_val_def,get_byte_set_byte]
  \\ Cases_on `byte_align c1 = byte_align a` \\ fs [word_loc_val_def]
  \\ fs [get_byte_set_byte_diff]);

val word_cmp_lemma = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 /\
    (word_cmp cmp (read_reg rr s1) (reg_imm ri s1) = SOME x) ==>
    (x = word_cmp cmp (read_reg rr t1) (reg_imm ri t1))``,
  Cases_on `ri` \\ fs [labSemTheory.reg_imm_def,asmSemTheory.reg_imm_def]
  \\ fs [labSemTheory.read_reg_def,asmSemTheory.read_reg_def]
  \\ Cases_on `s1.regs rr` \\ fs []
  \\ TRY (Cases_on `s1.regs n`) \\ fs [] \\ Cases_on `cmp`
  \\ fs [labSemTheory.word_cmp_def,asmSemTheory.word_cmp_def]
  \\ rw [] \\ fs [state_rel_def]
  \\ first_assum (assume_tac o Q.SPEC `rr:num`)
  \\ first_x_assum (assume_tac o Q.SPEC `n:num`)
  \\ rfs [word_loc_val_def] \\ rw []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []
  \\ rpt (qpat_assum `1w = xxx` (fn th => fs [GSYM th]))
  \\ rpt (qpat_assum `p + n2w xxx = t1.regs rr` (fn th => fs [GSYM th]))
  \\ res_tac \\ fs []);

val bytes_in_mem_IMP_memory = prove(
  ``!xs a.
      (!a. ~(a IN dm1) ==> m a = m1 a) ==>
      bytes_in_mem a xs m dm dm1 ==>
      bytes_in_memory a xs m1 dm``,
  Induct \\ fs [bytes_in_memory_def,bytes_in_mem_def]);

val state_rel_shift_interfer = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 x ==>
    state_rel (shift_interfer l mc_conf,code2,labs,p,T) s1 t1 x``,
  fs [state_rel_def,shift_interfer_def]
  \\ rpt strip_tac \\ fs [] \\ rfs [] \\ res_tac
  \\ fs [interference_ok_def,shift_seq_def]);

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
  Cases_on `i` \\ fs [asm_inst_def,inst_def]
  THEN1
   (fs [state_rel_def,inc_pc_def,shift_interfer_def,upd_pc_def,dec_clock_def]
    \\ rpt strip_tac \\ rfs [] \\ res_tac \\ fs [GSYM word_add_n2w])
  THEN1
   (fs [state_rel_def,inc_pc_def,shift_interfer_def,upd_pc_def,
        dec_clock_def,asmSemTheory.upd_reg_def,labSemTheory.upd_reg_def]
    \\ rpt strip_tac \\ rfs [] \\ res_tac \\ fs [GSYM word_add_n2w]
    \\ fs [APPLY_UPDATE_THM] \\ rw [word_loc_val_def])
  >- (
    strip_tac >>
    conj_tac >- (
      Cases_on`a`>> fs[asmSemTheory.arith_upd_def,labSemTheory.arith_upd_def] >>
      every_case_tac >> fs[labSemTheory.assert_def] >- (
        Cases_on`b`>>EVAL_TAC >> fs[state_rel_def] )
      >> EVAL_TAC >> fs[state_rel_def] ) >>
    conj_tac >- (
      rw[] >>
      Cases_on`a`>>fs[asmSemTheory.arith_upd_def,labSemTheory.arith_upd_def] >>
      every_case_tac >> fs[labSemTheory.assert_def] >- (
        Cases_on`b`>>EVAL_TAC ) >>
      EVAL_TAC ) >>
    rw[] >>
    cheat )
  \\ cheat (* long and messy, use set_byte_get_byte lemmas for memop cases *));

val state_rel_ignore_io_events = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
    state_rel (mc_conf,code2,labs,p,T) (s1 with ffi := io) t1 ms1``,
  fs [state_rel_def] \\ rpt strip_tac \\ res_tac \\ rfs [] \\ fs []);

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
  \\ Cases_on `s1.clock = 0` \\ fs []
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ fs [Once targetSemTheory.evaluate_def]
         \\ metis_tac [state_rel_weaken])
  \\ Cases_on `asm_fetch s1` \\ fs []
  \\ Cases_on `x` \\ fs [] \\ Cases_on `a` \\ fs []
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ fs [LET_DEF]
  THEN1 (* Asm Inst *)
   (qmatch_assum_rename_tac `asm_fetch s1 = SOME (Asm (Inst i) bytes len)`
    \\ mp_tac IMP_bytes_in_memory_Inst \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Inst i` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
         asm_step_IMP_evaluate_step_nop) \\ fs []
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ `~(asm_inst i s1).failed` by (rpt strip_tac \\ fs [])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (imp_res_tac Inst_lemma \\ pop_assum (K all_tac)
      \\ fs [state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ fs []
      \\ fs [asm_step_nop_def,asm_def,LET_DEF]
      \\ fs [asm_def,upd_pc_def,upd_reg_def]
      \\ qpat_assum `bytes_in_mem ww bytes' t1.mem
            t1.mem_domain s1.mem_domain` mp_tac
      \\ match_mp_tac bytes_in_mem_IMP_memory \\ fs [])
    \\ rpt strip_tac \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac \\ rpt strip_tac \\ fs [asm_def]
      THEN1 (fs [inc_pc_def,dec_clock_def,asm_inst_consts])
      THEN1 (fs [shift_interfer_def])
      \\ fs [GSYM PULL_FORALL]
      \\ match_mp_tac state_rel_shift_interfer
      \\ imp_res_tac Inst_lemma \\ fs [])
    \\ rpt strip_tac \\ fs [inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k` mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l - 1` \\ fs []
    \\ `^s1.clock - 1 + k + l = ^s1.clock + (k + l - 1)` by decide_tac
    \\ fs [asm_inst_consts])
  THEN1 (* Asm JumpReg *)
   (Cases_on `read_reg n' s1` \\ fs []
    \\ qmatch_assum_rename_tac `read_reg r1 s1 = Loc l1 l2`
    \\ Cases_on `loc_to_pc l1 l2 s1.code` \\ fs []
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`JumpReg r1`]MP_TAC
         asm_step_IMP_evaluate_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [IMP_bytes_in_memory_JumpReg,asmSemTheory.upd_pc_def,
             asmSemTheory.assert_def]
      \\ imp_res_tac IMP_bytes_in_memory_JumpReg \\ fs []
      \\ fs [asmSemTheory.read_reg_def,labSemTheory.read_reg_def]
      \\ fs [interference_ok_def,shift_seq_def,labSemTheory.read_reg_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rfs []
      \\ fs [word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ fs []
      \\ Q.PAT_ASSUM `xx = t1.regs r1` (fn th => fs [GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
      \\ fs [alignmentTheory.aligned_bitwise_and]
      \\ match_mp_tac pos_val_MOD_0 \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,`(asm (JumpReg r1)
            (t1.pc + n2w (LENGTH (mc_conf.target.encode (JumpReg r1)))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
      \\ fs [asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def,dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,labSemTheory.read_reg_def]
      \\ fs [interference_ok_def,shift_seq_def,labSemTheory.read_reg_def]
      \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rfs []
      \\ fs [word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ fs []
      \\ Q.PAT_ASSUM `xx = t1.regs r1` (fn th => fs [GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
      \\ RES_TAC \\ fs [] \\ rpt strip_tac \\ res_tac \\ rw []
      \\ fs [alignmentTheory.aligned_bitwise_and]
      \\ match_mp_tac pos_val_MOD_0 \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ rw []
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
    \\ Q.EXISTS_TAC `t2` \\ fs [state_rel_def,shift_interfer_def])
  THEN1 (* Jump *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump jtarget) l bytes n)`
    \\ Cases_on `get_pc_value jtarget s1` \\ fs []
    \\ mp_tac IMP_bytes_in_memory_Jump \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]MP_TAC
         asm_step_IMP_evaluate_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ rfs [] \\ unabbrev_all_tac
      \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.encode jj))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
      \\ fs [asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,labSemTheory.read_reg_def,asm_def,
             jump_to_offset_def]
      \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ Cases_on `jtarget` \\ fs []
      \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
      \\ imp_res_tac lab_lookup_IMP \\ fs [] \\ metis_tac [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ rw []
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
    \\ Q.EXISTS_TAC `t2` \\ fs [state_rel_def,shift_interfer_def])
  THEN1 (* JumpCmp *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (JumpCmp cmp rr ri jtarget) l bytes n)`
    \\ `word_cmp cmp (labSem$read_reg rr s1) (labSem$reg_imm ri s1) =
        SOME (asmSem$word_cmp cmp (read_reg rr t1) (reg_imm ri t1))` by
     (Cases_on `word_cmp cmp (read_reg rr s1) (reg_imm ri s1)` \\ fs []
      \\ imp_res_tac word_cmp_lemma \\ fs [])
    \\ fs []
    \\ Cases_on `word_cmp cmp (read_reg rr t1) (reg_imm ri t1)` \\ fs []
    THEN1
     (Cases_on `get_pc_value jtarget s1` \\ fs []
      \\ mp_tac IMP_bytes_in_memory_JumpCmp \\ fs []
      \\ match_mp_tac IMP_IMP \\ strip_tac
      THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
      \\ rpt strip_tac \\ pop_assum mp_tac
      \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
      \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
           asm_step_IMP_evaluate_step) \\ fs []
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (fs [state_rel_def,asm_def,LET_DEF]
        \\ unabbrev_all_tac \\ fs [asm_step_def,asm_def,LET_DEF]
        \\ imp_res_tac bytes_in_mem_IMP
        \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
        \\ rfs [] \\ unabbrev_all_tac
        \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def])
      \\ rpt strip_tac
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
           `code2`,`labs`,
           `(asm jj (t1.pc + n2w (LENGTH (mc_conf.target.encode jj))) t1)`,`ms2`])
      \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
       (unabbrev_all_tac
        \\ fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
        \\ fs [asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
               asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
               labSemTheory.assert_def,labSemTheory.read_reg_def,asm_def,
               jump_to_offset_def]
        \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
        \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
              WORD_ADD_SUB] \\ fs [get_pc_value_def]
        \\ Cases_on `jtarget` \\ fs []
        \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
        \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
        \\ imp_res_tac lab_lookup_IMP \\ fs [] \\ metis_tac [])
      \\ rpt strip_tac
      \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`MP_TAC) \\ rw []
      \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
      \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
      \\ Q.EXISTS_TAC `t2` \\ fs [state_rel_def,shift_interfer_def])
    \\ mp_tac (IMP_bytes_in_memory_JumpCmp_1) \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$JumpCmp cmp rr ri lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_nop) \\ fs []
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ fs []
      \\ fs [asm_step_nop_def,asm_def,LET_DEF]
      \\ fs [asm_def,upd_pc_def,upd_reg_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
      \\ fs [asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,labSemTheory.read_reg_def,asm_def,
             jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
             labSemTheory.upd_reg_def]
      \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ rpt strip_tac \\ res_tac \\ fs [])
    \\ rpt strip_tac \\ fs [inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock - 1 + k`mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by decide_tac \\ fs [])
  THEN1 (* Call *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Call lab) x1 x2 x3)`
    \\ Cases_on `lab`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Call (Lab l1 l2)) l bytes len)`
    \\ (Q.SPECL_THEN [`Lab l1 l2`,`len`]mp_tac
            (Q.GENL[`n`,`ww`]IMP_bytes_in_memory_Call))
    \\ match_mp_tac IMP_IMP \\ strip_tac \\ fs []
    \\ fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
  THEN1 (* LocValue *)
   (qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (LocValue reg lab) x1 x2 x3)`
    \\ Cases_on `lab`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (LocValue reg (Lab l1 l2)) ww bytes len)`
    \\ fs [lab_to_loc_def]
    \\ mp_tac (Q.INST [`l`|->`ww`,`n`|->`len`]
               IMP_bytes_in_memory_LocValue) \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Loc reg lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step_nop) \\ fs []
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPEC `bytes'`)
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF] \\ unabbrev_all_tac \\ fs []
      \\ fs [asm_step_nop_def,asm_def,LET_DEF]
      \\ fs [asm_def,upd_pc_def,upd_reg_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (bytes':word8 list))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
      \\ fs [asmSemTheory.upd_pc_def,asmSemTheory.assert_def,
             asmSemTheory.read_reg_def, dec_clock_def,labSemTheory.upd_pc_def,
             labSemTheory.assert_def,labSemTheory.read_reg_def,asm_def,
             jump_to_offset_def,inc_pc_def,asmSemTheory.upd_reg_def,
             labSemTheory.upd_reg_def]
      \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ fs [APPLY_UPDATE_THM] \\ rw [word_loc_val_def]
      \\ res_tac \\ fs []
      \\ Cases_on `lab_lookup l1 l2 labs` \\ fs []
      \\ imp_res_tac lab_lookup_IMP \\ rw [])
    \\ rpt strip_tac \\ fs [inc_pc_def,dec_clock_def,labSemTheory.upd_reg_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN`s1.clock - 1 + k`mp_tac)
    \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l - 1` \\ fs []
    \\ `s1.clock - 1 + k + l = s1.clock + (k + l - 1)` by decide_tac \\ fs [])
  THEN1 (* CallFFI *)
   (qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm (CallFFI n') l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)`
    \\ Cases_on `s1.regs s1.len_reg` \\ fs []
    \\ Cases_on `s1.regs s1.link_reg` \\ fs []
    \\ Cases_on `s1.regs s1.ptr_reg` \\ fs []
    \\ Cases_on `read_bytearray c' (w2n c) s1.mem s1.mem_domain s1.be` \\ fs []
    \\ qmatch_assum_rename_tac
         `read_bytearray c1 (w2n c2) s1.mem s1.mem_domain s1.be = SOME x`
    \\ qmatch_assum_rename_tac `s1.regs s1.link_reg = Loc n1 n2`
    \\ Cases_on `call_FFI s1.ffi index x` \\ fs []
    \\ qmatch_assum_rename_tac
         `call_FFI s1.ffi index x = (new_ffi,new_bytes)`
    \\ mp_tac IMP_bytes_in_memory_CallFFI \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ rfs [] \\ unabbrev_all_tac
      \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ Cases_on `loc_to_pc n1 n2 s1.code` \\ fs []
    \\ qmatch_assum_rename_tac `loc_to_pc n1 n2 s1.code = SOME new_pc`
    \\ `mc_conf.target.get_pc ms2 = p - n2w ((3 + index) * ffi_offset)` by
     (fs [GSYM PULL_FORALL]
      \\ fs [state_rel_def] \\ rfs []
      \\ fs [backend_correct_def]
      \\ Q.PAT_ASSUM `!ms s. mc_conf.target.state_rel s ms ==> bbb` imp_res_tac
      \\ fs [] \\ unabbrev_all_tac
      \\ fs [asm_def,asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ rewrite_tac [GSYM word_sub_def,WORD_SUB_PLUS,
           GSYM word_add_n2w,WORD_ADD_SUB]) \\ fs[]
    \\ `has_io_index index s1.code` by
          (imp_res_tac IMP_has_io_index \\ NO_TAC)
    \\ `~(mc_conf.target.get_pc ms2 IN mc_conf.prog_addresses) /\
        ~(mc_conf.target.get_pc ms2 = mc_conf.halt_pc) /\
        (find_index (mc_conf.target.get_pc ms2) mc_conf.ffi_entry_pcs 0 =
           SOME index)` by
      (fs [state_rel_def]
       \\ Q.PAT_ASSUM `!kk. has_io_index kk s1.code ==> bbb` imp_res_tac
       \\ rfs [] \\ NO_TAC)
    \\ `(mc_conf.target.get_reg ms2 mc_conf.ptr_reg = t1.regs mc_conf.ptr_reg) /\
        (mc_conf.target.get_reg ms2 mc_conf.len_reg = t1.regs mc_conf.len_reg) /\
        !a. a IN mc_conf.prog_addresses ==>
            (mc_conf.target.get_byte ms2 a = t1.mem a)` by
     (fs [GSYM PULL_FORALL]
      \\ fs [state_rel_def] \\ rfs []
      \\ fs [backend_correct_def]
      \\ Q.PAT_ASSUM `!ms s. mc_conf.target.state_rel s ms ==> bbb` imp_res_tac
      \\ fs [backend_correct_def |> REWRITE_RULE [GSYM reg_ok_def]]
      \\ unabbrev_all_tac \\ fs [state_rel_def,asm_def,
           jump_to_offset_def,asmSemTheory.upd_pc_def,AND_IMP_INTRO]
      \\ rpt strip_tac \\ first_x_assum match_mp_tac
      \\ fs [reg_ok_def] \\ NO_TAC) \\ fs []
    \\ `(t1.regs mc_conf.ptr_reg = c1) /\
        (t1.regs mc_conf.len_reg = c2)` by
     (fs [state_rel_def]
      \\ Q.PAT_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (fn th =>
          MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).ptr_reg` th)
          \\ MP_TAC (Q.SPEC `(mc_conf: ('a,'state,'b) machine_config).len_reg` th))
      \\ Q.PAT_ASSUM `xx = s1.ptr_reg` (ASSUME_TAC o GSYM)
      \\ Q.PAT_ASSUM `xx = s1.len_reg` (ASSUME_TAC o GSYM)
      \\ fs [word_loc_val_def] \\ NO_TAC) \\ fs []
    \\ imp_res_tac read_bytearray_state_rel \\ fs []
    \\ reverse(Cases_on `new_ffi.final_event = NONE`) THEN1
     (imp_res_tac evaluate_pres_final_event \\ fs [] \\ rfs []
      \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ rpt strip_tac
      \\ Q.EXISTS_TAC `l'` \\ fs [ADD_ASSOC]
      \\ once_rewrite_tac [targetSemTheory.evaluate_def] \\ fs []
      \\ fs [shift_interfer_def,LET_DEF]
      \\ BasicProvers.CASE_TAC >> fs[]) \\ fs []
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
      THEN1 (fs [backend_correct_def,shift_interfer_def] \\ metis_tac [])
      \\ unabbrev_all_tac
      \\ imp_res_tac bytes_in_mem_asm_write_bytearray
      \\ fs [state_rel_def,shift_interfer_def,asm_def,jump_to_offset_def,
             asmSemTheory.upd_pc_def] \\ rfs[]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ full_simp_tac bool_ss [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ `interference_ok (shift_seq l' mc_conf.next_interfer)
            (mc_conf.target.proj t1.mem_domain)` by
               (fs [interference_ok_def,shift_seq_def] \\ NO_TAC) \\ fs []
      \\ `p + n2w (pos_val new_pc 0 code2) = t1.regs s1.link_reg` by
       (Q.PAT_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (Q.SPEC_THEN `s1.link_reg`mp_tac) \\ fs [word_loc_val_def]
        \\ Cases_on `lab_lookup n1 n2 labs` \\ fs []
        \\ ONCE_REWRITE_TAC [EQ_SYM_EQ] \\ fs []
        \\ res_tac \\ fs []) \\ fs []
      \\ `w2n c2 = LENGTH new_bytes` by
       (imp_res_tac read_bytearray_LENGTH
        \\ imp_res_tac call_FFI_LENGTH \\ fs [])
      \\ res_tac \\ fs [] \\ rpt strip_tac
      THEN1
       (fs [PULL_FORALL,AND_IMP_INTRO] \\ rfs[]
        \\ Q.PAT_ASSUM `t1.regs s1.ptr_reg = c1` (ASSUME_TAC o GSYM)
        \\ fs [] \\ first_x_assum match_mp_tac
        \\ fs [] \\ qexists_tac `new_io` \\ fs [option_ldrop_0])
      THEN1
       (fs [shift_seq_def,PULL_FORALL,AND_IMP_INTRO])
      THEN1 res_tac
      THEN1
       (Cases_on `s1.io_regs 0 r`
        \\ fs [get_reg_value_def,word_loc_val_def])
      \\ qpat_assum `!a.
           byte_align a IN s1.mem_domain ==> bbb` (MP_TAC o Q.SPEC `a`)
      \\ fs [] \\ REPEAT STRIP_TAC
      \\ match_mp_tac (SIMP_RULE std_ss [] CallFFI_bytearray_lemma) \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock + k`mp_tac) \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l'` \\ fs [ADD_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`ms2'`] \\ fs []
    \\ simp_tac std_ss [Once evaluate_def]
    \\ fs [shift_interfer_def]
    \\ fs [AC ADD_COMM ADD_ASSOC,AC MULT_COMM MULT_ASSOC] \\ rfs [LET_DEF]
    \\ `k + s1.clock - 1 = k + (s1.clock - 1)` by decide_tac \\ fs [])
  THEN1 (* Halt *)
   (rw []
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l1 l2 l3)`
    \\ qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm Halt l bytes n)`
    \\ mp_tac IMP_bytes_in_memory_Halt \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ (Q.ISPECL_THEN [`mc_conf`,`t1`,`ms1`,`s1.ffi`,`jj`]mp_tac
         asm_step_IMP_evaluate_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP2 \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def]
      \\ rfs [] \\ unabbrev_all_tac
      \\ fs [asmSemTheory.jump_to_offset_def,asmSemTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ unabbrev_all_tac \\ fs [asm_def]
    \\ FIRST_X_ASSUM (Q.SPEC_THEN `s1.clock`mp_tac) \\ rw []
    \\ Q.EXISTS_TAC `l'` \\ fs []
    \\ once_rewrite_tac [evaluate_def] \\ fs []
    \\ fs [shift_interfer_def]
    \\ `mc_conf.target.get_pc ms2 = mc_conf.halt_pc` by
     (fs [backend_correct_def] \\ res_tac \\ fs []
      \\ fs [jump_to_offset_def,asmSemTheory.upd_pc_def] \\ fs [state_rel_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
           WORD_ADD_SUB] \\ fs [])
    \\ `~(mc_conf.target.get_pc ms2 IN t1.mem_domain)` by fs [state_rel_def]
    \\ fs [state_rel_def,jump_to_offset_def,asmSemTheory.upd_pc_def]
    \\ Cases_on `s1.regs s1.ptr_reg` \\ fs []
    \\ `word_loc_val p labs (s1.regs s1.ptr_reg) = SOME (t1.regs s1.ptr_reg)` by fs []
    \\ Cases_on `s1.regs s1.ptr_reg` \\ fs [word_loc_val_def] \\ rw []
    \\ `s1 = s2` by (Cases_on `t1.regs s1.ptr_reg = 0w` \\ fs [] \\ rw []) \\ rw []
    \\ fs [backend_correct_def] \\ res_tac \\ fs []
    \\ pop_assum (qspec_then `s1.ptr_reg` mp_tac)
    \\ pop_assum (qspec_then `s1.ptr_reg` mp_tac)
    \\ fs [reg_ok_def] \\ rw [] \\ fs []));

(* relating observable semantics *)

val init_ok_def = Define `
  init_ok (mc_conf, p) s ms <=>
    s.ffi.final_event = NONE /\
    ?code2 labs t1.
      state_rel (mc_conf,code2,labs,p,T) s t1 ms`

val state_rel_clock = prove(
  ``state_rel x s1 t1 ms ==>
    state_rel x (s1 with clock := k) (t1) ms``,
  PairCases_on `x`
  \\ fs [state_rel_def]
  \\ fs [] \\ rw [] \\ fs []
  \\ metis_tac []);

val evaluate_add_clock = store_thm("evaluate_add_clock",
  ``evaluate mc_conf ffi k ms = (r,ms1,st1) /\ r <> TimeOut ==>
    evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)``,
  metis_tac[targetPropsTheory.evaluate_without_TimeOut,FST]);

val evaluate_ignore_clocks = prove(
  ``evaluate mc_conf ffi k ms = (r1,ms1,st1) /\ r1 <> TimeOut /\
    evaluate mc_conf ffi k' ms = (r2,ms2,st2) /\ r2 <> TimeOut ==>
    (r1,ms1,st1) = (r2,ms2,st2)``,
  rw [] \\ imp_res_tac evaluate_add_clock \\ fs []
  \\ pop_assum (qspec_then `k'` mp_tac)
  \\ pop_assum (qspec_then `k` mp_tac)
  \\ fs [AC ADD_ASSOC ADD_COMM])

val machine_sem_EQ_sem = Q.prove(
  `!mc_conf p (ms:'state) ^s1.
     backend_correct mc_conf.target /\
     init_ok (mc_conf,p) s1 ms /\ semantics s1 <> Fail ==>
     machine_sem mc_conf s1.ffi ms = { semantics s1 }`,
  simp[GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 2 strip_tac >>
  fs [init_ok_def] >>
  simp[semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >>
  conj_tac
  >- (
    qx_gen_tac`ffi`>>strip_tac>> fs []
    \\ drule compile_correct \\ fs []
    \\ `r ≠ Error` by (Cases_on`r`>>every_case_tac>>fs[]>>metis_tac[FST]) >> simp[]
    \\ disch_then drule
    \\ imp_res_tac state_rel_clock
    \\ pop_assum (qspec_then `k` assume_tac)
    \\ disch_then drule \\ rw [] \\ fs []
    \\ fs [machine_sem_def,EXTENSION] \\ fs [IN_DEF]
    \\ Cases \\ fs [machine_sem_def]
    THEN1 (disj1_tac \\ qexists_tac `k+k'` \\ fs [] \\ every_case_tac \\ fs[])
    THEN1
     (eq_tac THEN1
       (rw [] \\ every_case_tac \\ fs[] \\ rw[]
        \\ drule (GEN_ALL evaluate_ignore_clocks) \\ fs []
        \\ pop_assum (K all_tac)
        \\ disch_then drule \\ fs [])
      \\ rw [] \\ every_case_tac \\ fs [] \\ asm_exists_tac \\ fs [])
    \\ CCONTR_TAC \\ fs [FST_EQ_EQUIV]
    \\ PairCases_on `z`
    \\ drule (GEN_ALL evaluate_ignore_clocks) \\ fs []
    \\ every_case_tac \\ fs []
    \\ pop_assum (K all_tac)
    \\ asm_exists_tac \\ fs [])
  \\ fs [machine_sem_def,EXTENSION] \\ fs [IN_DEF]
  \\ strip_tac
  \\ Cases \\ fs [machine_sem_def]
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
      Cases_on`r.ffi.final_event`>>fs[]>>
      Cases_on`q`>>fs[]>>
      `∃x y z. evaluate mc_conf s1.ffi k ms = (x,y,z)` by metis_tac[PAIR] >>
      `x = TimeOut` by (
        spose_not_then strip_assume_tac >>
        drule (GEN_ALL evaluate_add_clock) >>
        simp[] >> qexists_tac`k'`>>simp[] ) >>
      fs[] >>
      metis_tac[targetPropsTheory.evaluate_TimeOut,PAIR_EQ]) >>
    simp[] >> fs[Abbr`a`] >>
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
      cheat ) >>
      (* evaluate_add_clock_io_events_mono for lab and target *)
    `equiv_lprefix_chain l1 l2` by (
      simp[equiv_lprefix_chain_thm] >>
      unabbrev_all_tac >> simp[PULL_EXISTS] >>
      ntac 2 (pop_assum kall_tac) >>
      simp[LNTH_fromList,PULL_EXISTS] >>
      simp[GSYM FORALL_AND_THM] >>
      rpt gen_tac >>
      (* should be similar to clos_to_bvlProof *)
      cheat ) >>
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
    Cases_on`r.ffi.final_event`>>fs[])
  \\ CCONTR_TAC \\ fs [FST_EQ_EQUIV]
  \\ last_x_assum (qspec_then `k` mp_tac) \\ fs []
  \\ Cases_on `evaluate (s1 with clock := k)` \\ fs []
  \\ drule compile_correct
  \\ Cases_on `q = Error` \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ first_x_assum (qspec_then `k` assume_tac)
  \\ asm_exists_tac \\ fs [] \\ gen_tac
  \\ PairCases_on `z`
  \\ drule (GEN_ALL evaluate_add_clock) \\ fs []
  \\ every_case_tac \\ fs []);

(*

TODO:
 - add support for skipping sections of code
 - define an incremental version of the compiler
 - add ability to install code

*)

val _ = export_theory();
