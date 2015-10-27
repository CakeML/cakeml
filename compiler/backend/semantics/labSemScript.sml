open preamble labLangTheory wordSemTheory;
local open alignmentTheory targetSemTheory in end;

val _ = new_theory"labSem";

(* TODO: awaiting HOL issue #168 *)
val () = Parse.temp_type_abbrev ("prog", ``:('a labLang$sec) list``);

val _ = Datatype `
  word8_loc = Byte word8 | LocByte num num num`;

val _ = Datatype `
  state =
    <| regs       : num -> 'a word_loc
     ; mem        : 'a word -> 'a word_loc
     ; mem_domain : 'a word set
     ; pc         : num
     ; be         : bool
     ; ffi        : 'ffi ffi_state  (* oracle *)
     ; io_regs    : num -> num -> 'a word option  (* oracle *)
     ; code       : 'a prog
     ; clock      : num
     ; failed     : bool
     ; ptr_reg    : num
     ; len_reg    : num
     ; link_reg   : num
     |>`

val is_Label_def = Define `
  (is_Label (Label _ _ _) = T) /\
  (is_Label _ = F)`;

val asm_fetch_aux_def = Define `
  (asm_fetch_aux pos [] = NONE) /\
  (asm_fetch_aux pos ((Section k [])::xs) = asm_fetch_aux pos xs) /\
  (asm_fetch_aux pos ((Section k (y::ys))::xs) =
     if is_Label y
     then asm_fetch_aux pos ((Section k ys)::xs)
     else if pos = 0:num
          then SOME y
          else asm_fetch_aux (pos-1) ((Section k ys)::xs))`

val asm_fetch_def = Define `
  asm_fetch s = asm_fetch_aux s.pc s.code`

val upd_pc_def   = Define `upd_pc pc s = s with pc := pc`
val upd_reg_def  = Define `upd_reg r w s = s with regs := (r =+ w) s.regs`
val upd_mem_def  = Define `upd_mem a w s = s with mem := (a =+ w) s.mem`
val read_reg_def = Define `read_reg r s = s.regs r`

val assert_def = Define `assert b s = s with failed := (~b \/ s.failed)`

val reg_imm_def = Define `
  (reg_imm (Reg r) s = read_reg r s) /\
  (reg_imm (Imm w) s = Word w)`

val binop_upd_def = Define `
  (binop_upd r Add w1 w2 = upd_reg r (Word (w1 + w2))) /\
  (binop_upd r Sub w1 w2 = upd_reg r (Word (w1 - w2))) /\
  (binop_upd r And w1 w2 = upd_reg r (Word (word_and w1 w2))) /\
  (binop_upd r Or  w1 w2 = upd_reg r (Word (word_or w1 w2))) /\
  (binop_upd r Xor w1 w2 = upd_reg r (Word (word_xor w1 w2)))`

val word_cmp_def = Define `
  (word_cmp Equal (Word w1) (Word w2) = SOME (w1 = w2)) /\
  (word_cmp Less  (Word w1) (Word w2) = SOME (w1 < w2)) /\
  (word_cmp Lower (Word w1) (Word w2) = SOME (w1 <+ w2)) /\
  (word_cmp Test  (Word w1) (Word w2) = SOME ((w1 && w2) = 0w)) /\
  (word_cmp Test  (Loc _ _) (Word w2) = if w2 = 1w then SOME T else NONE) /\
  (word_cmp _ _ _ = NONE)`

val word_shift_def = Define `
  (word_shift Lsl w n = w << n) /\
  (word_shift Lsr w n = w >>> n) /\
  (word_shift Asr w n = w >> n)`

val arith_upd_def = Define `
  (arith_upd (Binop b r1 r2 (ri:'a reg_imm)) s =
     case (read_reg r2 s, reg_imm ri s) of
     | (Word w1, Word w2) => binop_upd r1 b w1 w2 s
     | _ => assert F s) /\
  (arith_upd (Shift l r1 r2 n) s =
     case read_reg r2 s of
     | Word w1 => upd_reg r1 (Word (word_shift l w1 n)) s
     | _ => assert F s)`

val addr_def = Define `
  addr (Addr r offset) s =
    case read_reg r s of
    | Word w => SOME (w + offset)
    | _ => NONE`

val is_Loc_def = Define `(is_Loc (Loc _ _) = T) /\ (is_Loc _ = F)`;

val mem_store_def = Define `
  mem_store r a (s:('a,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w => assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                        w IN s.mem_domain)
                  (upd_mem w (read_reg r s) s)`

val mem_load_def = Define `
  mem_load r a (s:('a,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w => assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                        w IN s.mem_domain)
                  (upd_reg r (s.mem w) s)`

val mem_load_byte_def = Define `
  mem_load_byte r a (s:('a,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w =>
        case mem_load_byte_aux w s.mem s.mem_domain s.be of
        | SOME v => upd_reg r (Word (w2w v)) s
        | NONE => assert F s`

val mem_store_byte_def = Define `
  mem_store_byte r a (s:('a,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w =>
        case read_reg r s of
        | Word b =>
           (case mem_store_byte_aux w (w2w b) s.mem s.mem_domain s.be of
            | SOME m => (s with mem := m)
            | NONE => assert F s)
        | _ => assert F s`

val mem_op_def = Define `
  (mem_op Load r a = mem_load r a) /\
  (mem_op Store r a = mem_store r a) /\
  (mem_op Load8 r a = mem_load_byte r a) /\
  (mem_op Store8 r a = mem_store_byte r a) /\
  (mem_op Load32 r (a:'a addr) = assert F) /\
  (mem_op Store32 r (a:'a addr) = assert F)`;

val asm_inst_def = Define `
  (asm_inst Skip s = (s:('a,'ffi) labSem$state)) /\
  (asm_inst (Const r imm) s = upd_reg r (Word imm) s) /\
  (asm_inst (Arith x) s = arith_upd x s) /\
  (asm_inst (Mem m r a) s = mem_op m r a s)`;

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`

val inc_pc_def = Define `
  inc_pc s = s with pc := s.pc + 1`

val asm_code_length_def = Define `
  (asm_code_length [] = 0) /\
  (asm_code_length ((Section k [])::xs) = asm_code_length xs) /\
  (asm_code_length ((Section k (y::ys))::xs) =
     asm_code_length ((Section k ys)::xs) + if is_Label y then 0 else 1:num)`

val asm_fetch_IMP = prove(
  ``(asm_fetch s = SOME x) ==>
    s.pc < asm_code_length s.code``,
  fs [asm_fetch_def,asm_code_length_def]
  \\ Q.SPEC_TAC (`s.pc`,`pc`)
  \\ Q.SPEC_TAC (`s.code`,`xs`)
  \\ HO_MATCH_MP_TAC (theorem "asm_code_length_ind")
  \\ rpt strip_tac \\ fs [asm_fetch_aux_def,asm_code_length_def]
  \\ Cases_on `is_Label y` \\ fs []
  \\ Cases_on `pc = 0` \\ fs []
  \\ res_tac \\ decide_tac);

val lab_to_loc_def = Define `
  lab_to_loc (Lab n1 n2) = Loc n1 n2`

val loc_to_pc_def = Define `
  (loc_to_pc n1 n2 [] = NONE) /\
  (loc_to_pc n1 n2 ((Section k xs)::ys) =
     if (k = n1) /\ (n2 = 0) then SOME (0:num) else
       case xs of
       | [] => loc_to_pc n1 n2 ys
       | (z::zs) =>
         if (?k. z = Label n1 (n2-1) k) /\ n2 <> 0 then SOME 0 else
           case loc_to_pc n1 n2 ((Section k zs)::ys) of
           | NONE => NONE
           | SOME pos => SOME (pos + 1))`;

val asm_inst_consts = store_thm("asm_inst_consts",
  ``((asm_inst i s).pc = s.pc) /\
    ((asm_inst i s).code = s.code) /\
    ((asm_inst i s).clock = s.clock) /\
    ((asm_inst i s).ffi = s.ffi)``,
  Cases_on `i` \\ fs [asm_inst_def,upd_reg_def,arith_upd_def]
  \\ TRY (Cases_on `a`)
  \\ fs [asm_inst_def,upd_reg_def,arith_upd_def,read_reg_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ TRY (Cases_on `b`)
  \\ fs [binop_upd_def,upd_reg_def,assert_def] \\ Cases_on `m`
  \\ fs [mem_op_def,mem_load_def,LET_DEF,mem_load_byte_def,upd_mem_def,
         assert_def,upd_reg_def,mem_store_def,mem_store_byte_def,
         mem_store_byte_aux_def,addr_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs []);

val get_pc_value_def = Define `
  get_pc_value lab (s:('a,'ffi) labSem$state) =
    case lab of
    | Lab n1 n2 => loc_to_pc n1 n2 s.code`;

val next_label_def = Define `
  (next_label [] = NONE) /\
  (next_label ((Section k [])::xs) = next_label xs) /\
  (next_label ((Section k (Label n1 n2 _::ys))::xs) = SOME (Loc n1 n2)) /\
  (next_label ((Section k (y::ys))::xs) = NONE)`

val get_lab_after_pos_def = Define `
  (get_lab_after pos [] = NONE) /\
  (get_lab_after pos ((Section k [])::xs) = get_lab_after pos xs) /\
  (get_lab_after pos ((Section k (y::ys))::xs) =
     if pos = 0:num
     then next_label ((Section k ys)::xs)
     else if is_Label y
          then get_lab_after pos ((Section k ys)::xs)
          else get_lab_after (pos-1) ((Section k ys)::xs))`

val get_ret_Loc_def = Define `
  get_ret_Loc s = get_lab_after s.pc s.code`;

val get_reg_value_def = Define `
  (get_reg_value NONE w f = w) /\
  (get_reg_value (SOME v) _ f = f v)`

val evaluate_def = tDefine "evaluate" `
  evaluate (s:('a,'ffi) labSem$state) =
    if s.clock = 0 then (TimeOut,s) else
    case asm_fetch s of
    | SOME (Asm a _ _) =>
        (case a of
         | Inst i =>
            (let s1 = asm_inst i s in
               if s1.failed then (Error,s)
               else evaluate (inc_pc (dec_clock s1)))
         | JumpReg r =>
            (case read_reg r s of
             | Loc n1 n2 =>
                 (case loc_to_pc n1 n2 s.code of
                  | NONE => (Error,s)
                  | SOME p =>
                      evaluate (upd_pc p (dec_clock s)))
             | _ => (Error,s))
         | _ => (Error,s))
    | SOME (LabAsm Halt _ _ _) =>
       (case s.regs s.ptr_reg of
        | Word 0w => (Halt Success,s)
        | Word _ => (Halt Resource_limit_hit,s)
        | _ => (Error,s))
    | SOME (LabAsm (LocValue r lab) _ _ _) =>
        let s1 = upd_reg r (lab_to_loc lab) s in
          evaluate (inc_pc (dec_clock s1))
    | SOME (LabAsm (Jump l) _ _ _) =>
       (case get_pc_value l s of
        | NONE => (Error,s)
        | SOME p => evaluate (upd_pc p (dec_clock s)))
    | SOME (LabAsm (JumpCmp c r ri l) _ _ _) =>
       (case word_cmp c (read_reg r s) (reg_imm ri s) of
        | NONE => (Error,s)
        | SOME F => evaluate (inc_pc (dec_clock s))
        | SOME T =>
         (case get_pc_value l s of
          | NONE => (Error,s)
          | SOME p => evaluate (upd_pc p (dec_clock s))))
    | SOME (LabAsm (Call l) _ _ _) =>
       (case get_pc_value l s of
        | NONE => (Error,s)
        | SOME p =>
         (case get_ret_Loc s of
          | NONE => (Error,s)
          | SOME k =>
             let s1 = upd_reg s.link_reg k s in
               evaluate (upd_pc p (dec_clock s1))))
    | SOME (LabAsm (CallFFI ffi_index) _ _ _) =>
       (case (s.regs s.len_reg,s.regs s.ptr_reg,s.regs s.link_reg) of
        | (Word w, Word w2, Loc n1 n2) =>
         (case (read_bytearray w2 (w2n w) s.mem s.mem_domain s.be,
                loc_to_pc n1 n2 s.code) of
          | (SOME bytes, SOME new_pc) =>
              let (new_ffi,new_bytes) = call_FFI s.ffi ffi_index bytes in
              let new_io_regs = shift_seq 1 s.io_regs in
              let new_m = write_bytearray w2 new_bytes s.mem s.mem_domain s.be in
                evaluate (s with <|
                                 mem := new_m ;
                                 ffi := new_ffi ;
                                 io_regs := new_io_regs ;
                                 regs := (\a. get_reg_value (s.io_regs 0 a)
                                                (s.regs a) Word);
                                 pc := new_pc ;
                                 clock := s.clock - 1 |>)
          | _ => (Error,s))
        | _ => (Error,s))
    | _ => (Error,s)`
 (WF_REL_TAC `measure (\s. s.clock)`
  \\ fs [inc_pc_def] \\ rw [] \\ IMP_RES_TAC asm_fetch_IMP
  \\ fs [asm_inst_consts,upd_reg_def,upd_pc_def,dec_clock_def]
  \\ decide_tac)

val semantics_def = Define `
  (semantics s1 (Terminate outcome io_list) <=>
     ?k s2 t.
       evaluate (s1 with clock := k) = (t,s2) /\
       (case outcome of
        | FFI_outcome e => (s2.ffi.final_event = SOME e /\ t <> Error)
        | _ => (s2.ffi.final_event = NONE) /\ (t = Halt outcome)) /\
       s2.ffi.io_events = io_list) /\
  (semantics s1 (Diverge io_trace) <=>
     (!k. ?s2. (evaluate (s1 with clock := k) = (TimeOut,s2)) /\
               s2.ffi.final_event = NONE) /\
     lprefix_lub (IMAGE (\k. fromList
       (SND (evaluate (s1 with clock := k))).ffi.io_events) UNIV) io_trace) /\
  (semantics s1 Fail <=>
     ?k. FST (evaluate (s1 with clock := k)) = Error)`

val _ = export_theory();
