(*
  The formal semantics of labLang
*)
open preamble labLangTheory wordSemTheory;
local open alignmentTheory targetSemTheory in end;

val _ = new_theory"labSem";

val _ = Datatype `
  word8_loc = Byte word8 | LocByte num num num`;

val _ = Datatype.big_record_size := 50;
val _ = Datatype `
  state =
    <| regs       : num -> 'a word_loc
     ; fp_regs    : num -> word64
     ; mem        : 'a word -> 'a word_loc
     ; mem_domain : 'a word set
     ; pc         : num
     ; be         : bool
     ; ffi        : 'ffi ffi_state  (* oracle *)
                  (* oracle: sequence of havoc on registers at each FFI call *)
     ; io_regs    : num (* seq number *) -> string (* ffi name *) -> num (* register *) -> 'a word option
     ; cc_regs    : num -> num -> 'a word option (* same as io_regs but for calling clear cache *)
     ; code       : 'a labLang$prog
     ; compile    : 'c -> 'a labLang$prog -> (word8 list # 'c) option
     ; compile_oracle : num -> 'c # 'a labLang$prog
     ; code_buffer : ('a,8) buffer
     ; clock      : num
     ; failed     : bool
     ; ptr_reg    : num
     ; len_reg    : num
     ; ptr2_reg    : num
     ; len2_reg    : num
     ; link_reg   : num
     |>`

val is_Label_def = Define `
  (is_Label (Label _ _ _) = T) /\
  (is_Label _ = F)`;
val _ = export_rewrites["is_Label_def"];

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
val _ = overload_on("read_reg",``λr s. s.regs r``);

val assert_def = Define `assert b s = s with failed := (~b \/ s.failed)`

val reg_imm_def = Define `
  (reg_imm (Reg r) s = read_reg r s) /\
  (reg_imm (Imm w) s = Word w)`
val _ = export_rewrites["reg_imm_def"];

val binop_upd_def = Define `
  (binop_upd r Add w1 w2 = upd_reg r (Word (w1 + w2))) /\
  (binop_upd r Sub w1 w2 = upd_reg r (Word (w1 - w2))) /\
  (binop_upd r And w1 w2 = upd_reg r (Word (word_and w1 w2))) /\
  (binop_upd r Or  w1 w2 = upd_reg r (Word (word_or w1 w2))) /\
  (binop_upd r Xor w1 w2 = upd_reg r (Word (word_xor w1 w2)))`

val word_cmp_def = Define `
  (word_cmp Equal    (Word w1) (Word w2) = SOME (w1 = w2)) /\
  (word_cmp Less     (Word w1) (Word w2) = SOME (w1 < w2)) /\
  (word_cmp Lower    (Word w1) (Word w2) = SOME (w1 <+ w2)) /\
  (word_cmp Test     (Word w1) (Word w2) = SOME ((w1 && w2) = 0w)) /\
  (word_cmp Test     (Loc _ _) (Word w2) = if w2 = 1w then SOME T else NONE) /\
  (word_cmp NotEqual (Word w1) (Word w2) = SOME (w1 <> w2)) /\
  (word_cmp NotLess  (Word w1) (Word w2) = SOME (~(w1 < w2))) /\
  (word_cmp NotLower (Word w1) (Word w2) = SOME (~(w1 <+ w2))) /\
  (word_cmp NotTest  (Word w1) (Word w2) = SOME ((w1 && w2) <> 0w)) /\
  (word_cmp NotTest  (Loc _ _) (Word w2) = if w2 = 1w then SOME F else NONE) /\
  (word_cmp _ _ _ = NONE)`

val arith_upd_def = Define `
  (arith_upd (Binop b r1 r2 (ri:'a reg_imm)) s =
     case (read_reg r2 s, reg_imm ri s) of
     | (Word w1, Word w2) => binop_upd r1 b w1 w2 s
     | (x,_) => if b = Or /\ ri = Reg r2 then upd_reg r1 x s else assert F s) /\
  (arith_upd (Shift l r1 r2 n) s =
     case read_reg r2 s of
     | Word w1 => upd_reg r1 (Word (word_shift l w1 n)) s
     | _ => assert F s) /\
  (arith_upd (Div r1 r2 r3) s =
     case (read_reg r3 s,read_reg r2 s) of
     | (Word q,Word w2) =>
       assert (q <> 0w) (upd_reg r1 (Word (w2 / q)) s)
     | _ => assert F s) /\
  (arith_upd (AddCarry r1 r2 r3 r4) s =
     case (read_reg r2 s, read_reg r3 s, read_reg r4 s) of
     | (Word w2, Word w3, Word w4) =>
       let r = w2n w2 + w2n w3 + (if w4 = 0w then 0 else 1)
       in
         upd_reg r4 (Word (if dimword(:'a) <= r then 1w else 0w))
            (upd_reg r1 (Word (n2w r)) s)
     | _ => assert F s) /\
  (arith_upd (LongMul r1 r2 r3 r4) s =
     case (read_reg r3 s, read_reg r4 s) of
     | (Word w3, Word w4) =>
       let r = w2n w3 * w2n w4 in
      upd_reg r2 (Word (n2w r))
       (upd_reg r1 (Word (n2w (r DIV dimword(:'a)))) s)
     | _ => assert F s)
     /\
  (arith_upd (LongDiv r1 r2 r3 r4 r5) s =
     case (read_reg r3 s, read_reg r4 s, read_reg r5 s) of
     | (Word w3, Word w4, Word w5) =>
       let n = w2n w3 * dimword (:'a) + w2n w4 in
       let d = w2n w5 in
       let q = n DIV d in
       assert (d ≠ 0 ∧ q < dimword(:'a))
         (upd_reg r1 (Word (n2w q)) (upd_reg r2 (Word (n2w (n MOD d))) s))
     | _ => assert F s)
      /\
  (arith_upd (AddOverflow r1 r2 r3 r4) s =
     case (read_reg r2 s, read_reg r3 s) of
     | (Word w2, Word w3) =>
         upd_reg r4 (Word (if w2i (w2 + w3) ≠ w2i w2 + w2i w3 then 1w else 0w))
            (upd_reg r1 (Word (w2 + w3)) s)
     | _ => assert F s) /\
  (arith_upd (SubOverflow r1 r2 r3 r4) s =
     case (read_reg r2 s, read_reg r3 s) of
     | (Word w2, Word w3) =>
         upd_reg r4 (Word (if w2i (w2 - w3) ≠ w2i w2 - w2i w3 then 1w else 0w))
            (upd_reg r1 (Word (w2 - w3)) s)
     | _ => assert F s)`


val upd_fp_reg_def  = Define `upd_fp_reg r v s = s with fp_regs := (r =+ v) s.fp_regs`
val read_fp_reg_def = Define `read_fp_reg r s = s.fp_regs r`

val fp_upd_def = Define `
  (fp_upd (FPLess r d1 d2) (s:('a,'c,'ffi) state) =
     upd_reg r (Word (if fp64_lessThan (read_fp_reg d1 s) (read_fp_reg d2 s)
                      then 1w
                      else 0w)) s) /\
  (fp_upd (FPLessEqual r d1 d2) s =
     upd_reg r (Word (if fp64_lessEqual (read_fp_reg d1 s) (read_fp_reg d2 s)
                      then 1w
                      else 0w)) s) /\
  (fp_upd (FPEqual r d1 d2) s =
     upd_reg r (Word (if fp64_equal (read_fp_reg d1 s) (read_fp_reg d2 s)
                      then 1w
                      else 0w)) s) /\
  (fp_upd (FPMov d1 d2) s = upd_fp_reg d1 (read_fp_reg d2 s) s) /\
  (fp_upd (FPAbs d1 d2) s = upd_fp_reg d1 (fp64_abs (read_fp_reg d2 s)) s) /\
  (fp_upd (FPNeg d1 d2) s = upd_fp_reg d1 (fp64_negate (read_fp_reg d2 s)) s) /\
  (fp_upd (FPSqrt d1 d2) s =
     upd_fp_reg d1 (fp64_sqrt roundTiesToEven (read_fp_reg d2 s)) s) /\
  (fp_upd (FPAdd d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_add roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPSub d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_sub roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPMul d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_mul roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPDiv d1 d2 d3) s =
     upd_fp_reg d1
       (fp64_div roundTiesToEven (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPFma d1 d2 d3) s =
     upd_fp_reg d1
       (fpSem$fpfma (read_fp_reg d1 s) (read_fp_reg d2 s) (read_fp_reg d3 s)) s) /\
  (fp_upd (FPMovToReg r1 r2 d) s =
     if dimindex(:'a) = 64 then
       upd_reg r1 (Word (w2w (read_fp_reg d s))) s
     else let v = read_fp_reg d s in
       upd_reg r2 (Word ((63 >< 32) v)) (upd_reg r1 (Word ((31 >< 0) v)) s)) /\
  (fp_upd (FPMovFromReg d r1 r2) s =
     if dimindex(:'a) = 64 then
       case read_reg r1 s of
         Word w1 => upd_fp_reg d (w2w w1) s
       | _ => assert F s
     else
       case (read_reg r1 s,read_reg r2 s) of
         (Word w1,Word w2) => upd_fp_reg d (w2 @@ w1) s
       | _ => assert F s) /\
  (fp_upd (FPToInt d1 d2) s =
     case fp64_to_int roundTiesToEven (read_fp_reg d2 s) of
         SOME i =>
           let w = i2w i : word32 in
             (if dimindex(:'a) = 64 then
                upd_fp_reg d1 (w2w w)
              else let (h, l) = if ODD d1 then (63, 32) else (31, 0) in
                     upd_fp_reg (d1 DIV 2)
                       (bit_field_insert h l w (read_fp_reg (d1 DIV 2) s)))
                (assert (w2i w = i) s)
      | _ => assert F s) /\
  (fp_upd (FPFromInt d1 d2) s =
     let i = if dimindex(:'a) = 64 then
               w2i ((31 >< 0) (read_fp_reg d2 s) : word32)
             else let v = read_fp_reg (d2 DIV 2) s in
               w2i (if ODD d2 then (63 >< 32) v else (31 >< 0) v : 'a word)
     in
       upd_fp_reg d1 (int_to_fp64 roundTiesToEven i) s)`

val addr_def = Define `
  addr (Addr r offset) s =
    case read_reg r s of
    | Word w => SOME (w + offset)
    | _ => NONE`

val is_Loc_def = Define `(is_Loc (Loc _ _) = T) /\ (is_Loc _ = F)`;

val mem_store_def = Define `
  mem_store r a (s:('a,'c,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w => assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                        w IN s.mem_domain)
                  (upd_mem w (read_reg r s) s)`

val mem_load_def = Define `
  mem_load r a (s:('a,'c,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w => assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                        w IN s.mem_domain)
                  (upd_reg r (s.mem w) s)`

val mem_load_byte_def = Define `
  mem_load_byte r a (s:('a,'c,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w =>
        case mem_load_byte_aux s.mem s.mem_domain s.be w of
        | SOME v => upd_reg r (Word (w2w v)) s
        | NONE => assert F s`

val mem_store_byte_def = Define `
  mem_store_byte r a (s:('a,'c,'ffi) labSem$state) =
    case addr a s of
    | NONE => assert F s
    | SOME w =>
        case read_reg r s of
        | Word b =>
           (case mem_store_byte_aux s.mem s.mem_domain s.be w (w2w b) of
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
  (asm_inst Skip s = (s:('a,'c,'ffi) labSem$state)) /\
  (asm_inst (Const r imm) s = upd_reg r (Word imm) s) /\
  (asm_inst (Arith x) s = arith_upd x s) /\
  (asm_inst (Mem m r a) s = mem_op m r a s) /\
  (asm_inst (FP fp) s = fp_upd fp s)`;

val _ = export_rewrites["mem_op_def","asm_inst_def","arith_upd_def","fp_upd_def"]

val dec_clock_def = Define `
  dec_clock s = s with clock := s.clock - 1`

val inc_pc_def = Define `
  inc_pc s = s with pc := s.pc + 1`

val asm_code_length_def = Define `
  (asm_code_length [] = 0) /\
  (asm_code_length ((Section k [])::xs) = asm_code_length xs) /\
  (asm_code_length ((Section k (y::ys))::xs) =
     asm_code_length ((Section k ys)::xs) + if is_Label y then 0 else 1:num)`

val asm_fetch_IMP = Q.prove(
  `(asm_fetch s = SOME x) ==>
    s.pc < asm_code_length s.code`,
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
     if (k = n1) /\ (n2 = 0n) then SOME (0:num) else
       case xs of
       | [] => loc_to_pc n1 n2 ys
       | (z::zs) =>
         if (?k. z = Label n1 n2 k) /\ n2 <> 0 then SOME 0n else
           if is_Label z then loc_to_pc n1 n2 ((Section k zs)::ys)
           else
             case loc_to_pc n1 n2 ((Section k zs)::ys) of
             | NONE => NONE
             | SOME pos => SOME (pos + 1:num))`;

Theorem asm_inst_consts:
   ((asm_inst i s).pc = s.pc) /\
   ((asm_inst i s).code = s.code) /\
   ((asm_inst i s).clock = s.clock) /\
   ((asm_inst i s).ffi = s.ffi) ∧
   ((asm_inst i s).ptr_reg = s.ptr_reg) ∧
   ((asm_inst i s).len_reg = s.len_reg) ∧
   ((asm_inst i s).ptr2_reg = s.ptr2_reg) ∧
   ((asm_inst i s).len2_reg = s.len2_reg) ∧
   ((asm_inst i s).link_reg = s.link_reg)
Proof
  Cases_on `i` \\ fs [asm_inst_def,upd_reg_def,arith_upd_def]
  >-
    (Cases_on `a`
    \\ fs [asm_inst_def,upd_reg_def,arith_upd_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ TRY (Cases_on `b`)
    \\ fs [binop_upd_def,upd_reg_def,assert_def])
  >-
    (Cases_on `m`
    \\ fs [mem_op_def,mem_load_def,LET_DEF,mem_load_byte_def,upd_mem_def,
         assert_def,upd_reg_def,mem_store_def,mem_store_byte_def,
         mem_store_byte_aux_def,addr_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [])
  >>
    Cases_on`f`
    \\ fs[fp_upd_def,upd_reg_def,upd_fp_reg_def,assert_def]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs[upd_fp_reg_def]
QED ;

val get_pc_value_def = Define `
  get_pc_value lab (s:('a,'c,'ffi) labSem$state) =
    case lab of
    | Lab n1 n2 => loc_to_pc n1 n2 s.code`;

val next_label_def = Define `
  (next_label [] = NONE) /\
  (next_label ((Section k [])::xs) = next_label xs) /\
  (next_label ((Section k (Label n1 n2 _::ys))::xs) = SOME (Loc n1 n2)) /\
  (next_label ((Section k (y::ys))::xs) = next_label (Section k ys::xs))`

val get_lab_after_pos_def = Define `
  (get_lab_after pos [] = NONE) /\
  (get_lab_after pos ((Section k [])::xs) = get_lab_after pos xs) /\
  (get_lab_after pos ((Section k (y::ys))::xs) =
     if is_Label y
     then get_lab_after pos ((Section k ys)::xs)
     else if pos = 0:num
          then next_label ((Section k ys)::xs)
          else get_lab_after (pos-1) ((Section k ys)::xs))`

val get_ret_Loc_def = Define `
  get_ret_Loc s = get_lab_after s.pc s.code`;

val evaluate_def = tDefine "evaluate" `
  evaluate (s:('a,'c,'ffi) labSem$state) =
    if s.clock = 0 then (TimeOut,s) else
    case asm_fetch s of
    | SOME (Asm (Asmi a) _ _) =>
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
    | SOME (Asm (Cbw r1 r2) _ _) =>
      (case (read_reg r1 s,read_reg r2 s) of
      | (Word w1, Word w2) =>
        (case buffer_write s.code_buffer w1 (w2w w2) of
        | SOME new_cb =>
          evaluate (inc_pc (dec_clock (s with code_buffer:= new_cb)))
        | _ => (Error,s))
      | _ => (Error,s))
    | SOME (LabAsm Halt _ _ _) =>
       (case s.regs s.ptr_reg of
        | Word 0w => (Halt Success,s)
        | Word _ => (Halt Resource_limit_hit,s)
        | _ => (Error,s))
    | SOME (LabAsm (LocValue r lab) _ _ _) =>
       (if get_pc_value lab s = NONE then (Error,s) else
          let s1 = upd_reg r (lab_to_loc lab) s in
            evaluate (inc_pc (dec_clock s1)))
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
    | SOME (LabAsm Install _ _ _) =>
       (case (s.regs s.ptr_reg,s.regs s.len_reg,s.regs s.link_reg) of
        | (Word w1, Word w2, Loc n1 n2) =>
           (case (buffer_flush s.code_buffer w1 w2, loc_to_pc n1 n2 s.code) of
            | (SOME (bytes, cb), SOME new_pc) =>
              let (cfg,prog) = s.compile_oracle 0 in (* the next oracle program *)
              let new_oracle = shift_seq 1 s.compile_oracle in
                (case (s.compile cfg prog, prog) of
                 | (SOME (bytes',cfg'), Section k _ :: _) =>
                   if bytes = bytes' ∧ FST(new_oracle 0) = cfg' then (* the oracle was correct *)
                     evaluate
                       (s with <|
                                pc := new_pc
                              ; code_buffer := cb
                              ; code := s.code ++ prog
                              ; cc_regs := shift_seq 1 s.cc_regs
                              ; regs := (s.ptr_reg =+ Loc k 0)
                                          (λa. get_reg_value  (s.cc_regs 0 a)
                                                   (s.regs a) Word)
                              ; compile_oracle := new_oracle
                              ; clock := s.clock - 1
                              |>)
                   else
                     (Error,s)
                 | _ => (Error, s))
                 | _ => (Error, s))
        | _ => (Error, s))
    | SOME (LabAsm (CallFFI ffi_index) _ _ _) =>
       (case (s.regs s.len_reg,s.regs s.ptr_reg,
              s.regs s.len2_reg,s.regs s.ptr2_reg,s.regs s.link_reg) of
        | (Word w, Word w2, Word w3, Word w4, Loc n1 n2) =>
         (case (read_bytearray w2 (w2n w) (mem_load_byte_aux s.mem s.mem_domain s.be),
                read_bytearray w4 (w2n w3) (mem_load_byte_aux s.mem s.mem_domain s.be),
                loc_to_pc n1 n2 s.code) of
          | (SOME bytes, SOME bytes2, SOME new_pc) =>
             (case call_FFI s.ffi ffi_index bytes bytes2 of
              | FFI_final outcome => (Halt (FFI_outcome outcome),s)
              | FFI_return new_ffi new_bytes =>
                  let new_io_regs = shift_seq 1 s.io_regs in
                  let new_m = write_bytearray w4 new_bytes s.mem s.mem_domain s.be in
                    evaluate (s with <|
                                   mem := new_m ;
                                   ffi := new_ffi ;
                                   io_regs := new_io_regs ;
                                   regs := (\a. get_reg_value (s.io_regs 0 ffi_index a)
                                                  (s.regs a) Word);
                                   pc := new_pc ;
                                   clock := s.clock - 1 |>))
          | _ => (Error,s))
        | _ => (Error,s))
    | _ => (Error,s)`
 (WF_REL_TAC `measure (\s. s.clock)`
  \\ fs [inc_pc_def] \\ rw [] \\ IMP_RES_TAC asm_fetch_IMP
  \\ fs [asm_inst_consts,upd_reg_def,upd_pc_def,dec_clock_def]
  \\ decide_tac)

val semantics_def = Define `
  semantics s =
  if ∃k. FST(evaluate (s with clock := k)) = Error then Fail
  else
    case some res.
      ∃k t outcome.
        evaluate (s with clock := k) = (Halt outcome,t) ∧
        res = Terminate outcome t.ffi.io_events
      of
    | SOME res => res
    | NONE =>
      Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList (SND (evaluate (s with clock := k))).ffi.io_events) UNIV))`;

val _ = export_theory();
