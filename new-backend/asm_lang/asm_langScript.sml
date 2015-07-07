open HolKernel Parse boolLib bossLib;
open asmTheory wordsTheory wordsLib sptreeTheory ffiTheory;
open target_semTheory word_locTheory lcsymtacs;
open arithmeticTheory alignmentTheory

val _ = new_theory "asm_lang";


(* -- SYNTAX -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)

(* A label refers to either a section name or a local label definition
   within the current section. *)

val () = Datatype `
  lab = Lab num num`

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

val () = Datatype `
  asm_with_lab = Jump lab
               | JumpCmp cmp reg ('a reg_imm) lab
               | Call lab
               | LocValue reg lab
               (* following have no label, but have similar semantics *)
               | CallFFI num
               | ClearCache
               | Halt`;

val () = Datatype `
  asm_line = Label num num num
           | Asm ('a asm) (word8 list) num
           | LabAsm ('a asm_with_lab) ('a word) (word8 list) num`

(* A section consists a name (num) and a list of assembly lines. *)

val () = Datatype `
  sec = Section num (('a asm_line) list)`

(* A full assmebly program consists of a list of sections. *)

val () = Parse.temp_type_abbrev ("asm_prog", ``:('a sec) list``);


(* -- SEMANTICS -- *)

val _ = Datatype `
  word8_loc = Byte word8 | LocByte num num num`;

val _ = Datatype `
  asml_state =
    <| regs       : num -> 'a word_loc
     ; mem        : 'a word -> 'a word_loc
     ; mem_domain : 'a word set
     ; pc         : num
     ; be         : bool
     ; io_events  : io_trace  (* oracle *)
     ; io_regs    : num -> num -> 'a word option  (* oracle *)
     ; code       : 'a asm_prog
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
  (word_cmp Test  (Word w1) (Word w2) = SOME (w1 && w2 = 0w)) /\
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
  mem_store r a (s:'a asml_state) =
    case addr a s of
    | NONE => assert F s
    | SOME w => assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                        w IN s.mem_domain)
                  (upd_mem w (read_reg r s) s)`

val mem_load_def = Define `
  mem_load r a (s:'a asml_state) =
    case addr a s of
    | NONE => assert F s
    | SOME w => assert ((w2n w MOD (dimindex (:'a) DIV 8) = 0) /\
                        w IN s.mem_domain)
                  (upd_reg r (s.mem w) s)`

val get_byte_def = Define `
  get_byte (a:'a word) (w:'a word) is_bigendian =
    let d = dimindex (:'a) DIV 8 in
      if is_bigendian
      then (w2w (w >>> ((d - 1) - w2n a MOD d))):word8
      else (w2w (w >>> (w2n a MOD d))):word8`

val mem_load_byte_aux_def = Define `
  mem_load_byte_aux w s =
    case s.mem (byte_align w) of
    | Loc _ _ => NONE
    | Word v =>
        if byte_align w IN s.mem_domain
        then SOME (get_byte w v s.be) else NONE`

val read_bytearray_def = Define `
  (read_bytearray a 0 s = SOME []) /\
  (read_bytearray a (SUC n) s =
     case mem_load_byte_aux a s of
     | NONE => NONE
     | SOME b => case read_bytearray (a + 1w) n s of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))`

val mem_load_byte_def = Define `
  mem_load_byte r a (s:'a asml_state) =
    case addr a s of
    | NONE => assert F s
    | SOME w =>
        case mem_load_byte_aux w s of
        | SOME v => upd_reg r (Word (w2w v)) s
        | NONE => assert F s`

val upd_byte_def = Define `
  upd_byte i (w:'a word) (b:word8) =
    (dimindex (:'a) - 1 '' 8 * i + 8) w || w2w b << (8 * i) ||
    (8 * i - 1 '' 0) w`;

val set_byte_def = Define `
  set_byte (a:'a word) (b:word8) (w:'a word) is_bigendian =
    let d = dimindex (:'a) DIV 8 in
      if is_bigendian
      then upd_byte ((d - 1) - (w2n a MOD d)) w b
      else upd_byte (w2n a MOD d) w b`

val mem_store_byte_aux_def = Define `
  mem_store_byte_aux w b s =
    case s.mem (byte_align w) of
    | Word v =>
        if byte_align w IN s.mem_domain
        then SOME (upd_mem (byte_align w) (Word (set_byte w b v s.be)) s)
        else NONE
    | _ => NONE`

val mem_store_byte_def = Define `
  mem_store_byte r a (s:'a asml_state) =
    case addr a s of
    | NONE => assert F s
    | SOME w =>
        case read_reg r s of
        | Word b =>
           (case mem_store_byte_aux w (w2w b) s of
            | SOME s1 => s1
            | NONE => assert F s)
        | _ => assert F s`

val write_bytearray_def = Define `
  (write_bytearray a [] s = s) /\
  (write_bytearray a (b::bs) s =
     case mem_store_byte_aux a b (write_bytearray (a+1w) bs s) of
     | SOME s => s
     | NONE => s)`;

val mem_op_def = Define `
  (mem_op Load r a = mem_load r a) /\
  (mem_op Store r a = mem_store r a) /\
  (mem_op Load8 r a = mem_load_byte r a) /\
  (mem_op Store8 r a = mem_store_byte r a) /\
  (mem_op Load32 r (a:'a addr) = assert F) /\
  (mem_op Store32 r (a:'a addr) = assert F)`;

val asm_inst_def = Define `
  (asm_inst Skip s = (s:'a asml_state)) /\
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

val asm_inst_consts = prove(
  ``((asm_inst i s).pc = s.pc) /\
    ((asm_inst i s).code = s.code) /\
    ((asm_inst i s).clock = s.clock) /\
    ((asm_inst i s).io_events = s.io_events)``,
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
  get_pc_value lab (s:'a asml_state) =
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

val aEval_def = tDefine "aEval" `
  aEval (s:'a asml_state) =
    if s.clock = 0 then (TimeOut,s) else
    case asm_fetch s of
    | SOME (Asm a _ _) =>
        (case a of
         | Inst i =>
            (let s1 = asm_inst i s in
               if s1.failed then (Error Internal,s)
               else aEval (inc_pc (dec_clock s1)))
         | JumpReg r =>
            (case read_reg r s of
             | Loc n1 n2 =>
                 (case loc_to_pc n1 n2 s.code of
                  | NONE => (Error Internal,s)
                  | SOME p =>
                      aEval (upd_pc p (dec_clock s)))
             | _ => (Error Internal,s))
         | _ => (Error Internal,s))
    | SOME (LabAsm Halt _ _ _) => (Result,s)
    | SOME (LabAsm (LocValue r lab) _ _ _) =>
        let s1 = upd_reg r (lab_to_loc lab) s in
          aEval (inc_pc (dec_clock s1))
    | SOME (LabAsm (Jump l) _ _ _) =>
       (case get_pc_value l s of
        | NONE => (Error Internal,s)
        | SOME p => aEval (upd_pc p (dec_clock s)))
    | SOME (LabAsm (JumpCmp c r ri l) _ _ _) =>
       (case word_cmp c (read_reg r s) (reg_imm ri s) of
        | NONE => (Error Internal,s)
        | SOME F => aEval (inc_pc (dec_clock s))
        | SOME T =>
         (case get_pc_value l s of
          | NONE => (Error Internal,s)
          | SOME p => aEval (upd_pc p (dec_clock s))))
    | SOME (LabAsm (Call l) _ _ _) =>
       (case get_pc_value l s of
        | NONE => (Error Internal,s)
        | SOME p =>
         (case get_ret_Loc s of
          | NONE => (Error Internal,s)
          | SOME k =>
             let s1 = upd_reg s.link_reg k s in
               aEval (upd_pc p (dec_clock s1))))
    | SOME (LabAsm (CallFFI ffi_index) _ _ _) =>
       (case (s.regs s.len_reg,s.regs s.ptr_reg,s.regs s.link_reg) of
        | (Word w, Word w2, Loc n1 n2) =>
         (case (read_bytearray w2 (w2n w) s,loc_to_pc n1 n2 s.code) of
          | (SOME bytes, SOME new_pc) =>
              let (new_bytes,new_io) = call_FFI ffi_index bytes s.io_events in
              let new_io_regs = shift_seq 1 s.io_regs in
                aEval (write_bytearray w2 new_bytes s
                         with <| io_events := new_io ;
                                 io_regs := new_io_regs ;
                                 regs := (\a. get_reg_value (s.io_regs 0 a)
                                                (s.regs a) Word);
                                 pc := new_pc ;
                                 clock := s.clock - 1 |>)
          | _ => (Error Internal,s))
        | _ => (Error Internal,s))
    | _ => (Error Internal,s)`
 (WF_REL_TAC `measure (\s. s.clock)`
  \\ fs [inc_pc_def] \\ rw [] \\ IMP_RES_TAC asm_fetch_IMP
  \\ fs [asm_inst_consts,upd_reg_def,upd_pc_def,dec_clock_def]
  \\ decide_tac)

val aEval_ind = fetch "-" "aEval_ind"

(* properties *)

val update_simps = store_thm("update_simps[simp]",
  ``((upd_pc x s).io_events = s.io_events) /\
    ((dec_clock s).io_events = s.io_events) /\
    ((upd_pc x s).pc = x) /\
    ((dec_clock s).pc = s.pc) /\
    ((upd_pc x s).clock = s.clock) /\
    ((dec_clock s).clock = s.clock - 1)``,
  EVAL_TAC);

(* -- ASSEMBLER FUNCTION -- *)

val ffi_offset_def = Define `
  ffi_offset = 8:num`;

(* basic assemble function *)

val lab_inst_def = Define `
  (lab_inst w (Jump _) = Jump w) /\
  (lab_inst w (JumpCmp c r ri _) = JumpCmp c r ri w) /\
  (lab_inst w (Call _) = Call w) /\
  (lab_inst w (LocValue r _) = Loc r (w:'a word)) /\
  (lab_inst w (Halt) = Jump w) /\
  (lab_inst w (ClearCache) = Jump w) /\
  (lab_inst w (CallFFI n) = Jump w)`;

val enc_line_def = Define `
  (enc_line enc (Label n1 n2 n3) = Label n1 n2 0) /\
  (enc_line enc (Asm a _ _) =
     let bs = enc a in Asm a bs (LENGTH bs)) /\
  (enc_line enc (LabAsm l _ _ _) =
     let bs = enc (lab_inst 0w l) in
       LabAsm l 0w bs (LENGTH bs))`

val enc_sec_def = Define `
  enc_sec enc (Section k xs) = Section k (MAP (enc_line enc) xs)`;

val enc_sec_list_def = Define `
  enc_sec_list enc xs = MAP (enc_sec enc) xs`;

(* compute labels *)

val asm_line_labs_def = Define `
  (asm_line_labs pos [] acc = (acc,pos)) /\
  (asm_line_labs pos ((Label k1 k2 l)::xs) acc =
     asm_line_labs (pos+l) xs (insert (k2+1) (pos+l) acc)) /\
  (asm_line_labs pos ((Asm _ _ l)::xs) acc =
     asm_line_labs (pos+l) xs acc) /\
  (asm_line_labs pos ((LabAsm _ _ _ l)::xs) acc =
     asm_line_labs (pos+l) xs acc)`

val sec_labs_def = Define `
  sec_labs pos (Section k lines) =
    asm_line_labs pos lines (insert 0 pos LN)`;

val sec_name_def = Define `
  sec_name (Section k _) = k`;

val compute_labels_def = Define `
  (compute_labels pos [] = LN) /\
  (compute_labels pos (s::rest) =
     let (labs,new_pos) = sec_labs pos s in
     let rest_labs = compute_labels new_pos rest in
       insert (sec_name s) labs rest_labs)`

(* update code *)

val lookup_any_def = Define `
  lookup_any x sp d =
    case lookup x sp of
    | NONE => d
    | SOME m => m`;

val find_pos_def = Define `
  find_pos (Lab k1 k2) labs =
    (lookup_any k2 (lookup_any k1 labs LN) 0):num`;

val get_label_def = Define `
  (get_label (Jump l) = l) /\
  (get_label (JumpCmp c r ri l) = l) /\
  (get_label (Call l) = l) /\
  (get_label (LocValue r l) = l)`;

val get_jump_offset_def = Define `
  (get_jump_offset (CallFFI i) labs pos =
     0w - n2w (pos + (3 + i) * ffi_offset)) /\
  (get_jump_offset ClearCache labs pos =
     0w - n2w (pos + 2 * ffi_offset)) /\
  (get_jump_offset Halt labs pos =
     0w - n2w (pos + ffi_offset)) /\
  (get_jump_offset a labs pos =
     n2w (find_pos (get_label a) labs) - n2w pos)`

val enc_line_again_def = Define `
  (enc_line_again labs pos enc [] = []) /\
  (enc_line_again labs pos enc ((Label k1 k2 l)::xs) =
     (Label k1 k2 l) :: enc_line_again labs (pos+l) enc xs) /\
  (enc_line_again labs pos enc ((Asm x1 x2 l)::xs) =
     (Asm x1 x2 l) :: enc_line_again labs (pos+l) enc xs) /\
  (enc_line_again labs pos enc ((LabAsm a w bytes l)::xs) =
     let w1 = get_jump_offset a labs pos in
       if w = w1 then
         (LabAsm a w bytes l)::enc_line_again labs (pos + l) enc xs
       else
         let bs = enc (lab_inst w1 a) in
         let l = LENGTH bs in
           LabAsm a w1 bs l::enc_line_again labs (pos + l) enc xs)`

val sec_length_def = Define `
  (sec_length [] k = k) /\
  (sec_length ((Label _ _ l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((Asm x1 x2 l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((LabAsm a w bytes l)::xs) k = sec_length xs (k+l))`

val full_sec_length_def = Define `
  full_sec_length xs =
    let k = sec_length xs 0 in
      if ODD k then k+1 else k`;

val enc_secs_again_def = Define `
  (enc_secs_again pos labs enc [] = []) /\
  (enc_secs_again pos labs enc ((Section s lines)::rest) =
     let lines1 = enc_line_again labs pos enc lines in
     let pos1 = pos + full_sec_length lines1 in
       (Section s lines1)::enc_secs_again pos1 labs enc rest)`

(* check/update length annotations *)

val sec_lengths_ok_def = Define `
  (sec_lengths_ok pos [] <=> T) /\
  (sec_lengths_ok pos ((Label _ _ l)::xs) <=>
     if (if EVEN pos then (l = 0) else (l = 1)) then
       sec_lengths_ok (pos+l) xs
     else F) /\
  (sec_lengths_ok pos ((Asm x1 x2 l)::xs) <=> sec_lengths_ok (pos+l) xs) /\
  (sec_lengths_ok pos ((LabAsm a w bytes l)::xs) <=>
     if LENGTH bytes <= l then sec_lengths_ok (pos+l) xs else F)`

val all_lengths_ok_def = Define `
  (all_lengths_ok pos [] = T) /\
  (all_lengths_ok pos ((Section s lines)::rest) =
     if sec_lengths_ok pos lines
     then all_lengths_ok (pos + sec_length lines 0) rest
     else F)`

val sec_lengths_update_def = Define `
  (sec_lengths_update pos [] = []) /\
  (sec_lengths_update pos ((Label k1 k2 l)::xs) =
     let l = if EVEN pos then 0 else 1 in
       (Label k1 k2 l) :: sec_lengths_update (pos+l) xs) /\
  (sec_lengths_update pos ((Asm x1 x2 l)::xs) <=>
     (Asm x1 x2 l) :: sec_lengths_update (pos+l) xs) /\
  (sec_lengths_update pos ((LabAsm a w bytes l)::xs) <=>
     let m = LENGTH bytes in
       (LabAsm a w bytes (if l < m then m else l)) ::
          sec_lengths_update pos xs)`

val all_lengths_update_def = Define `
  (all_lengths_update pos [] = []) /\
  (all_lengths_update pos ((Section s lines)::rest) =
     Section s (sec_lengths_update pos lines) ::
       all_lengths_update (pos + sec_length lines 0) rest)`;

(* checking that all labelled asm instructions are asm_ok *)

val sec_asm_ok_def = Define `
  (sec_asm_ok c [] <=> T) /\
  (sec_asm_ok c ((Label _ _ l)::xs) <=> sec_asm_ok c xs) /\
  (sec_asm_ok c ((Asm x1 x2 l)::xs) <=> sec_asm_ok c xs) /\
  (sec_asm_ok c ((LabAsm a w bytes l)::xs) <=>
     if asm_ok (lab_inst w a) c then sec_asm_ok c xs else F)`

val all_asm_ok_def = Define `
  (all_asm_ok c [] = T) /\
  (all_asm_ok c ((Section s lines)::rest) =
     if sec_asm_ok c lines then all_asm_ok c rest else F)`

(* top-level assembler function *)

val remove_labels_loop_def = Define `
  remove_labels_loop clock c enc sec_list =
    (* compute labels *)
    let labs = compute_labels 0 sec_list in
    (* update jump encodings *)
    let xs = enc_secs_again 0 labs enc sec_list in
    (* check length annotations *)
    if all_lengths_ok 0 xs then
      if all_asm_ok c xs then SOME xs else NONE
    else
    (* update length annotations *)
    let ys = all_lengths_update 0 xs in
    (* repeat *)
    if clock = 0:num then NONE else
      remove_labels_loop (clock-1) c enc ys`

val remove_labels_def = Define `
  remove_labels c enc sec_list =
    (* Here the magic constant 1000000 puts an upper limit on the
       number of times the lengths can be adjusted. In most cases,
       clock = 0 should be enough. If this were to hit the clock limit
       then something is badly wrong. Worth testing with the clock
       limit set to low values to see how many iterations are used. *)
    remove_labels_loop 1000000 c enc (enc_sec_list enc sec_list)`;

(* code extraction *)

val line_bytes_def = Define `
  (line_bytes (Label _ _ l) nop = if l = 0 then [] else [nop]) /\
  (line_bytes (Asm _ bytes _) nop = bytes) /\
  (line_bytes (LabAsm _ _ bytes _) nop = bytes)`

val all_bytes_def = Define `
  (all_bytes pos nop [] = []) /\
  (all_bytes pos nop ((Section k [])::xs) =
     if EVEN pos then all_bytes pos nop xs
                 else [nop] ++ all_bytes (pos+1) nop xs) /\
  (all_bytes pos nop ((Section k (y::ys))::xs) =
     let bytes = line_bytes y nop in
       bytes ++
       all_bytes (pos + LENGTH bytes) nop ((Section k ys)::xs))`

val nop_byte_def = Define `
  nop_byte enc = (case enc (Inst Skip) of [] => 0w | (x::xs) => x)`;

val prog_to_bytes_def = Define `
  prog_to_bytes enc sec_list = all_bytes 0 (nop_byte enc) sec_list`

(* compile asm_lang *)

val aComp_def = Define `
  aComp c enc sec_list =
    case remove_labels c enc sec_list of
    | SOME sec_list => SOME (prog_to_bytes enc sec_list)
    | NONE => NONE`;

(* prove that asm_step implies mEval steps *)

val IMP_IMP = METIS_PROVE [] ``a /\ (b ==> c) ==> ((a ==> b) ==> c)``
val IMP_IMP2 = METIS_PROVE [] ``a /\ (a /\ b ==> c) ==> ((a ==> b) ==> c)``

val asserts_restrict = prove(
  ``!n next1 next2 s P Q.
      (!k. k <= n ==> (next1 k = next2 k)) ==>
      (asserts n next1 s P Q ==> asserts n next2 s P Q)``,
  Induct \\ fs [asserts_def,LET_DEF]
  \\ REPEAT STRIP_TAC \\ POP_ASSUM MP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC
  \\ FIRST_X_ASSUM MATCH_MP_TAC
  \\ DECIDE_TAC);

val shift_interfer_def = Define `
  shift_interfer k s =
    s with next_interfer := shift_seq k s.next_interfer`

val shift_interfer_intro = prove(
  ``shift_interfer k1 (shift_interfer k2 c) = shift_interfer (k1+k2) c``,
  fs [shift_interfer_def,shift_seq_def,ADD_ASSOC]);

val mEval_EQ_mEval_lemma = prove(
  ``!n ms1 c.
      c.f.get_pc ms1 IN c.prog_addresses /\ c.f.state_ok ms1 /\
      interference_ok c.next_interfer (c.f.proj dm) /\
      (!s ms. c.f.state_rel s ms ==> c.f.state_ok ms) /\
      (!ms1 ms2. (c.f.proj dm ms1 = c.f.proj dm ms2) ==>
                 (c.f.state_ok ms1 = c.f.state_ok ms2)) /\
      (!env.
         interference_ok env (c.f.proj dm) ==>
         asserts n (\k s. env k (c.f.next s)) ms1
           (\ms'. c.f.state_ok ms' /\ c.f.get_pc ms' IN c.prog_addresses)
           (\ms'. c.f.state_rel s2 ms')) ==>
      ?ms2.
        !k. (mEval c io (k + (n + 1)) ms1 =
             mEval (shift_interfer (n+1) c) io k ms2) /\
            c.f.state_rel s2 ms2``,
  Induct THEN1
   (fs [] \\ REPEAT STRIP_TAC
    \\ fs [asserts_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once mEval_def] \\ fs [LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `K (c.next_interfer 0)`)
    \\ fs [interference_ok_def] \\ RES_TAC \\ fs []
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs [shift_interfer_def]
    \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ fs []
  \\ fs [arithmeticTheory.ADD_CLAUSES]
  \\ SIMP_TAC std_ss [Once mEval_def] \\ fs [ADD1] \\ fs [LET_DEF]
  \\ Q.PAT_ASSUM `!i. bbb`
       (fn th => ASSUME_TAC th THEN MP_TAC (Q.SPEC
         `\i. c.next_interfer 0` th))
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (fs [interference_ok_def])
  \\ fs [] \\ REPEAT STRIP_TAC
  \\ FULL_SIMP_TAC bool_ss [GSYM ADD1,asserts_def] \\ fs [LET_DEF]
  \\ `c.f.state_ok (c.f.next ms1)` by METIS_TAC [interference_ok_def] \\ fs []
  \\ Q.PAT_ASSUM `!ms1 c. bbb ==> ?x. bb`
        (MP_TAC o Q.SPECL [`(c.next_interfer 0 (c.f.next ms1))`,
                    `(c with next_interfer := shift_seq 1 c.next_interfer)`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (fs [] \\ REPEAT STRIP_TAC
    THEN1 (fs [interference_ok_def,shift_seq_def])
    THEN1 RES_TAC
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC
         `\k. if k = SUC n then c.next_interfer 0 else env k`) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP
    \\ STRIP_TAC THEN1 (fs [interference_ok_def] \\ rw [])
    \\ MATCH_MP_TAC asserts_restrict
    \\ rw [FUN_EQ_THM] \\ `F` by decide_tac)
  \\ REPEAT STRIP_TAC \\ fs [] \\ Q.EXISTS_TAC `ms2` \\ STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.SPEC `k`)
  \\ fs [GSYM shift_interfer_def,shift_interfer_intro] \\ fs [GSYM ADD1]);

val enc_ok_not_empty = prove(
  ``enc_ok enc c /\ asm_ok w c ==> (enc w <> [])``,
  METIS_TAC [listTheory.LENGTH_NIL,enc_ok_def]);

val SUBSET_IMP = prove(
  ``s SUBSET t ==> (x IN s ==> x IN t)``,
  fs [pred_setTheory.SUBSET_DEF]);

val bytes_in_memory_IMP_SUBSET = prove(
  ``!xs a. bytes_in_memory a xs m d ==> all_pcs a xs SUBSET d``,
  Induct \\ fs [all_pcs_def,bytes_in_memory_def]);

val asserts_WEAKEN = prove(
  ``!n next s P Q.
      (!x. P x ==> P' x) /\ (!k. k <= n ==> (next k = next' k)) ==>
      asserts n next s P Q ==>
      asserts n next' s P' Q``,
  Induct \\ fs [asserts_def,LET_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ `!k. k <= n ==> (next k = next' k)` by ALL_TAC \\ RES_TAC
  \\ REPEAT STRIP_TAC \\ FIRST_X_ASSUM MATCH_MP_TAC \\ decide_tac);

val asm_step_IMP_mEval_step = prove(
  ``!c s1 ms1 io i s2.
      backend_correct_alt c.f c.asm_config /\
      (c.prog_addresses = s1.mem_domain) /\
      interference_ok c.next_interfer (c.f.proj s1.mem_domain) /\
      asm_step_alt c.f.encode c.asm_config s1 i s2 /\
      (s2 = asm i (s1.pc + n2w (LENGTH (c.f.encode i))) s1) /\
      c.f.state_rel (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2. !k. (mEval c io (k + l) ms1 =
                   mEval (shift_interfer l c) io k ms2) /\
                  c.f.state_rel s2 ms2 /\ l <> 0``,
  fs [backend_correct_alt_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ fs [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ Q.EXISTS_TAC `n+1` \\ fs []
  \\ MATCH_MP_TAC (GEN_ALL mEval_EQ_mEval_lemma) \\ fs []
  \\ Q.EXISTS_TAC `s1.mem_domain` \\ fs []
  \\ REPEAT STRIP_TAC \\ TRY (RES_TAC \\ NO_TAC)
  THEN1 (fs [asm_step_alt_def] \\ IMP_RES_TAC enc_ok_not_empty
         \\ Cases_on `c.f.encode i` \\ fs [bytes_in_memory_def])
  \\ fs [LET_DEF] \\ Q.PAT_ASSUM `!k. bb` (K ALL_TAC)
  \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPECL [`\k. env (n - k)`]) \\ fs []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`\k. env (n - k)`]) \\ fs []
  \\ MATCH_MP_TAC IMP_IMP
  \\ STRIP_TAC THEN1 fs [interference_ok_def]
  \\ MATCH_MP_TAC asserts_WEAKEN \\ fs []
  \\ SRW_TAC [] [] \\ fs []
  THEN1 (POP_ASSUM MP_TAC \\ MATCH_MP_TAC SUBSET_IMP
         \\ fs [asm_step_alt_def] \\ IMP_RES_TAC bytes_in_memory_IMP_SUBSET)
  \\ fs [FUN_EQ_THM] \\ REPEAT STRIP_TAC
  \\ `n - (n - k) = k` by decide_tac \\ fs [])
  |> SIMP_RULE std_ss [GSYM PULL_FORALL];

(* compiler correctness proof *)

val line_ok_def = Define `
  (line_ok (c:'a asm_config) enc labs pos (Label _ _ l) <=>
     if EVEN pos then (l = 0) else (l = 1)) /\
  (line_ok c enc labs pos (Asm b bytes l) <=>
     (bytes = enc b) /\ (LENGTH bytes = l) /\ asm_ok b c) /\
  (line_ok c enc labs pos (LabAsm Halt w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + ffi_offset) in
     let bs = enc (Jump w1) in
       (bytes = bs) /\ (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c enc labs pos (LabAsm ClearCache w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + 2 * ffi_offset) in
     let bs = enc (Jump w1) in
       (bytes = bs) /\ (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c enc labs pos (LabAsm (CallFFI index) w bytes l) <=>
     let w1 = (0w:'a word) - n2w (pos + (3 + index) * ffi_offset) in
     let bs = enc (Jump w1) in
       (bytes = bs) /\ (LENGTH bytes = l) /\ asm_ok (Jump w1) c) /\
  (line_ok c enc labs pos (LabAsm a w bytes l) <=>
     let target = find_pos (get_label a) labs in
     let w1 = n2w target - n2w pos in
     let bs = enc (lab_inst w1 a) in
       (bytes = bs) /\ (LENGTH bytes = l) /\ asm_ok (lab_inst w1 a) c)`

val line_length_def = Define `
  (line_length (Label k1 k2 l) = if l = 0 then 0 else 1) /\
  (line_length (Asm b bytes l) = LENGTH bytes) /\
  (line_length (LabAsm a w bytes l) = LENGTH bytes)`

val all_enc_ok_def = Define `
  (all_enc_ok c enc labs pos [] = T) /\
  (all_enc_ok c enc labs pos ((Section k [])::xs) =
     all_enc_ok c enc labs (if EVEN pos then pos else pos+1) xs) /\
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

val lab_lookup_def = Define `
  lab_lookup k1 k2 labs =
    case lookup k1 labs of
    | NONE => NONE
    | SOME f => lookup k2 f`

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

val pos_val_def = Define `
  (pos_val i pos [] =
     if EVEN pos then pos else pos + 1) /\
  (pos_val i pos ((Section k [])::xs) =
     if EVEN pos then pos_val i pos xs else pos_val i (pos + 1) xs) /\
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

val option_ldrop_def = Define `
  (option_ldrop n NONE = NONE) /\
  (option_ldrop n (SOME l) = LDROP n l)`

val asm_write_bytearray_def = Define `
  (asm_write_bytearray a [] (m:'a word -> word8) = m) /\
  (asm_write_bytearray a (x::xs) m = asm_write_bytearray (a+1w) xs ((a =+ x) m))`

val state_rel_def = Define `
  state_rel (mc_conf, code2, labs, p, check_pc) (s1:'a asml_state) t1 ms1 <=>
    mc_conf.f.state_rel t1 ms1 /\
    (mc_conf.prog_addresses = t1.mem_domain) /\
    ~(mc_conf.halt_pc IN mc_conf.prog_addresses) /\
    reg_ok s1.ptr_reg mc_conf.asm_config /\ (mc_conf.ptr_reg = s1.ptr_reg) /\
    reg_ok s1.len_reg mc_conf.asm_config /\ (mc_conf.len_reg = s1.len_reg) /\
    reg_ok s1.link_reg mc_conf.asm_config /\
    (!ms2 k index new_bytes new_io t1 x.
       mc_conf.f.state_rel
         (t1 with pc := p - n2w ((3 + index) * ffi_offset)) ms2 /\
       (read_bytearray (t1.regs s1.ptr_reg) (LENGTH new_bytes)
         (\a. if a ∈ t1.mem_domain then SOME (t1.mem a) else NONE) = SOME x) /\
       (call_FFI index x (option_ldrop k s1.io_events) = (new_bytes,new_io)) /\
       new_io <> NONE ==>
       mc_conf.f.state_rel
         (t1 with
         <|regs := (\a. get_reg_value (s1.io_regs k a) (t1.regs a) I);
           mem := asm_write_bytearray (t1.regs s1.ptr_reg) new_bytes t1.mem;
           pc := t1.regs s1.link_reg|>)
        (mc_conf.ffi_interfer k index new_bytes ms2)) /\
    (!index.
       has_io_index index s1.code ==>
       ~(p - n2w ((3 + index) * ffi_offset) IN mc_conf.prog_addresses) /\
       ~(p - n2w ((3 + index) * ffi_offset) = mc_conf.halt_pc) /\
       (list_find (p - n2w ((3 + index) * ffi_offset))
          mc_conf.ffi_entry_pcs = SOME index)) /\
    (p - n2w ffi_offset = mc_conf.halt_pc) /\
    interference_ok mc_conf.next_interfer (mc_conf.f.proj t1.mem_domain) /\
    (!q n. (n2w (t1.align - 1) && q + n2w n = 0w:'a word) <=>
           (n MOD t1.align = 0)) /\
    (!l1 l2 x2.
       (loc_to_pc l1 l2 s1.code = SOME x2) ==>
       (lab_lookup l1 l2 labs = SOME (pos_val x2 0 code2))) /\
    (!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)) /\
    (!a. byte_align a IN s1.mem_domain ==>
         a IN t1.mem_domain /\ a IN s1.mem_domain /\
         ?w. (word_loc_val p labs (s1.mem (byte_align a)) = SOME w) /\
             (get_byte a w s1.be = t1.mem a)) /\
    (has_odd_inst code2 ==> (mc_conf.asm_config.code_alignment = 1)) /\
    bytes_in_mem p (prog_to_bytes mc_conf.f.encode code2)
      t1.mem t1.mem_domain s1.mem_domain /\
    ~s1.failed /\ ~t1.failed /\ (s1.be = t1.be) /\
    (check_pc ==> (t1.pc = p + n2w (pos_val s1.pc 0 code2))) /\
    (p && n2w (t1.align - 1) = 0w) /\
    (case mc_conf.asm_config.link_reg of NONE => T | SOME r => t1.lr = r) /\
    (t1.be <=> mc_conf.asm_config.big_endian) /\
    (t1.align = mc_conf.asm_config.code_alignment) /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    code_similar s1.code code2`

val LENGTH_line_bytes = prove(
  ``!x2. LENGTH (line_bytes x2 b) = line_length x2``,
  Cases \\ fs [line_bytes_def,line_length_def] \\ rw []);

val no_Label_def = Define `
  (no_Label (Section k (x::xs)::ys) = ~(is_Label x)) /\ (no_Label _ = F)`;

val _ = augment_srw_ss [rewrites [no_Label_def]];

val all_bytes_lemma = prove(
  ``!code2 code1 pc i pos.
       code_similar code1 code2 /\
       all_enc_ok (mc_conf:('a,'state,'b) machine_config).asm_config
         mc_conf.f.encode labs pos code2 /\
       (asm_fetch_aux pc code1 = SOME i) ==>
       ?bs code2' j.
         (all_bytes pos (nop_byte mc_conf.f.encode) code2  =
          bs ++ all_bytes (pos + LENGTH bs) (nop_byte mc_conf.f.encode) code2') /\
         (LENGTH bs + pos = pos_val pc pos code2) /\
         (asm_fetch_aux 0 code2' = SOME j) /\
         line_similar i j /\ no_Label code2' /\
         line_ok mc_conf.asm_config mc_conf.f.encode
           labs (pos_val pc pos code2) j``,
  HO_MATCH_MP_TAC (theorem "asm_code_length_ind") \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `code1` \\ fs [code_similar_def,asm_fetch_aux_def])
  THEN1
   (Cases_on `code1` \\ fs [code_similar_def]
    \\ Cases_on `h` \\ fs [code_similar_def]
    \\ Cases_on `l` \\ fs [asm_fetch_aux_def,pos_val_def] \\ rw []
    \\ fs [all_bytes_def,all_enc_ok_def] THEN1 (metis_tac [])
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`t`,`pc`,`i`,`pos + 1`]) \\ fs []
    \\ rpt strip_tac \\ fs []
    \\ Q.EXISTS_TAC `nop_byte mc_conf.f.encode::bs` \\ fs []
    \\ Q.EXISTS_TAC `code2'` \\ fs []
    \\ rpt strip_tac
    \\ fs [ADD1,AC ADD_COMM ADD_ASSOC])
  \\ Cases_on `code1` \\ fs [code_similar_def]
  \\ Cases_on `h` \\ fs [code_similar_def]
  \\ Cases_on `l` \\ fs [asm_fetch_aux_def,pos_val_def]
  \\ Q.PAT_ASSUM `n = k` (fn th => fs [th])
  \\ Q.MATCH_ASSUM_RENAME_TAC `line_similar x1 x2`
  \\ Q.MATCH_ASSUM_RENAME_TAC `LIST_REL line_similar ys1 ys2`
  \\ `is_Label x2 = is_Label x1` by
    (Cases_on `x1` \\ Cases_on `x2` \\ fs [line_similar_def,is_Label_def])
  \\ fs [] \\ Cases_on `is_Label x1` \\ fs []
  THEN1
   (fs [all_bytes_def,LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc`,`i`,
       `(pos + LENGTH (line_bytes x2 (nop_byte mc_conf.f.encode)))`])
    \\ fs [all_enc_ok_def,LENGTH_line_bytes,code_similar_def] \\ rpt strip_tac
    \\ fs [prog_to_bytes_def,LET_DEF]
    \\ Q.LIST_EXISTS_TAC [`line_bytes x2 (nop_byte mc_conf.f.encode) ++ bs`,
         `code2'`]
    \\ fs [AC ADD_COMM ADD_ASSOC,LENGTH_line_bytes])
  \\ Cases_on `pc = 0` \\ fs [] \\ rw []
  THEN1
   (fs [listTheory.LENGTH_NIL]
    \\ Q.EXISTS_TAC `Section k (x2::ys2)::xs`
    \\ fs [asm_fetch_aux_def,all_enc_ok_def])
  \\ fs [all_bytes_def,LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc-1`,`i`,
       `(pos + LENGTH (line_bytes x2 (nop_byte mc_conf.f.encode)))`])
  \\ fs [all_enc_ok_def,LENGTH_line_bytes,code_similar_def]
  \\ rpt strip_tac \\ fs []
  \\ Q.LIST_EXISTS_TAC [`line_bytes x2 (nop_byte mc_conf.f.encode) ++ bs`,
        `code2'`,`j`] \\ fs []
  \\ fs [AC ADD_COMM ADD_ASSOC,LENGTH_line_bytes])

val prog_to_bytes_lemma = all_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [GSYM prog_to_bytes_def];

val bytes_in_mem_IMP = prove(
  ``!xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm``,
  Induct \\ fs [bytes_in_mem_def,bytes_in_memory_def]);

val bytes_in_memory_APPEND = prove(
  ``!bs bs1 p.
      bytes_in_memory p (bs ++ bs1) m dm <=>
      bytes_in_memory p bs m dm /\
      bytes_in_memory (p + n2w (LENGTH bs)) bs1 m dm``,
  Induct \\ fs [bytes_in_memory_def,ADD1,word_add_n2w]
  \\ REWRITE_TAC [GSYM WORD_ADD_ASSOC,word_add_n2w,CONJ_ASSOC])

val IMP_bytes_in_memory = prove(
  ``code_similar code1 code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    (asm_fetch_aux pc code1 = SOME i) /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) m (dm:'a word set) ==>
    ?j code2'.
      bytes_in_memory (p + n2w (pos_val pc 0 code2))
        (all_bytes (pos_val pc 0 code2) (nop_byte mc_conf.f.encode) code2') m dm /\
      line_ok (mc_conf:('a,'state,'b) machine_config).asm_config
        mc_conf.f.encode labs (pos_val pc 0 code2) j /\
      (asm_fetch_aux 0 code2' = SOME j) /\
      line_similar i j /\ no_Label code2'``,
  rpt strip_tac
  \\ mp_tac prog_to_bytes_lemma \\ fs [] \\ rpt strip_tac
  \\ fs [bytes_in_memory_APPEND]
  \\ Q.EXISTS_TAC `j` \\ Q.EXISTS_TAC `code2'` \\ fs []);

val no_Label_eq = prove(
  ``no_Label p = ?k x xs ys. (p = Section k (x::xs)::ys) /\ ~is_Label x``,
  Cases_on `p` \\ fs [] \\ Cases_on `h` \\ fs [] \\ Cases_on `l` \\ fs []);

val IMP_bytes_in_memory_JumpReg = prove(
  ``code_similar s1.code code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) t1.mem
      t1.mem_domain /\
    (asm_fetch s1 = SOME (Asm (JumpReg r1) l n)) ==>
    bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
      (mc_conf.f.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    asm_ok (JumpReg r1) (mc_conf: ('a,'state,'b) machine_config).asm_config``,
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def] \\ rw [] \\ fs [no_Label_eq]
  \\ fs [asm_fetch_aux_def,all_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND]);

val IMP_bytes_in_memory_Jump = prove(
  ``code_similar s1.code code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) t1.mem
      t1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (Jump target) l bytes n)) ==>
    ?tt enc.
      (tt = n2w (find_pos target labs) -
            n2w (pos_val s1.pc 0 code2)) /\
      (enc = mc_conf.f.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).asm_config``,
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def] \\ rw []
  \\ fs [no_Label_eq,LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ fs [asm_fetch_aux_def,all_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ rw []);

val IMP_bytes_in_memory_CallFFI = prove(
  ``code_similar s1.code code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) t1.mem
      t1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + (3 + index) * ffi_offset)) /\
      (enc = mc_conf.f.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).asm_config``,
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def] \\ rw []
  \\ fs [no_Label_eq,LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ fs [asm_fetch_aux_def,all_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ rw []);

val IMP_bytes_in_memory_Halt = prove(
  ``code_similar s1.code code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) t1.mem
      t1.mem_domain /\
    (asm_fetch s1 = SOME (LabAsm Halt l bytes n)) ==>
    ?tt enc.
      (tt = 0w - n2w (pos_val s1.pc 0 code2 + ffi_offset)) /\
      (enc = mc_conf.f.encode (Jump tt)) /\
      bytes_in_memory ((p:'a word) + n2w (pos_val s1.pc 0 code2))
        enc t1.mem t1.mem_domain /\
      asm_ok (Jump tt) (mc_conf: ('a,'state,'b) machine_config).asm_config``,
  fs [asm_fetch_def,LET_DEF]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`) \\ strip_tac
  \\ Q.SPEC_TAC (`s1.code`,`code1`) \\ strip_tac \\ strip_tac
  \\ mp_tac (IMP_bytes_in_memory |> Q.GENL [`i`,`dm`,`m`]) \\ fs []
  \\ strip_tac \\ res_tac
  \\ Cases_on `j` \\ fs [line_similar_def] \\ rw []
  \\ fs [line_ok_def] \\ rw []
  \\ fs [no_Label_eq,LET_DEF,lab_inst_def,get_label_def] \\ rw []
  \\ fs [asm_fetch_aux_def,all_bytes_def,LET_DEF,line_bytes_def,
         bytes_in_memory_APPEND] \\ rw []);

val line_length_MOD_0 = prove(
  ``backend_correct_alt mc_conf.f mc_conf.asm_config /\
    (~EVEN p ==> (mc_conf.asm_config.code_alignment = 1)) /\
    line_ok mc_conf.asm_config mc_conf.f.encode labs p h ==>
    (line_length h MOD mc_conf.asm_config.code_alignment = 0)``,
  Cases_on `h` \\ TRY (Cases_on `a`) \\ fs [line_ok_def,line_length_def]
  \\ rw [] \\ fs [backend_correct_alt_def,enc_ok_def]
  \\ Q.PAT_ASSUM `xxx = LENGTH yy` (ASSUME_TAC o GSYM)
  \\ `0 < mc_conf.asm_config.code_alignment` by
       (fs [backend_correct_alt_def,enc_ok_def] \\ DECIDE_TAC)
  \\ fs [LET_DEF] \\ rw []
  \\ Q.PAT_ASSUM `l = xxx` (fn th => once_rewrite_tac [th]) \\ fs []);

val pos_val_MOD_0_lemma = prove(
  ``backend_correct_alt mc_conf.f mc_conf.asm_config ==>
    (0 MOD mc_conf.asm_config.code_alignment = 0)``,
  rpt strip_tac
  \\ `0 < mc_conf.asm_config.code_alignment` by ALL_TAC
  THEN1 (fs [backend_correct_alt_def,enc_ok_def] \\ DECIDE_TAC) \\ fs []);

val pos_val_MOD_0 = prove(
  ``!x pos code2.
      backend_correct_alt mc_conf.f mc_conf.asm_config /\
      (has_odd_inst code2 ==> (mc_conf.asm_config.code_alignment = 1)) /\
      (~EVEN pos ==> (mc_conf.asm_config.code_alignment = 1)) /\
      (pos MOD mc_conf.asm_config.code_alignment = 0) /\
      all_enc_ok mc_conf.asm_config mc_conf.f.encode labs pos code2 ==>
      (pos_val x pos code2 MOD mc_conf.asm_config.code_alignment = 0)``,
  REVERSE (Cases_on `backend_correct_alt mc_conf.f mc_conf.asm_config`)
  \\ asm_simp_tac pure_ss [] THEN1 fs []
  \\ `0 < mc_conf.asm_config.code_alignment` by ALL_TAC
  THEN1 (fs [backend_correct_alt_def,enc_ok_def] \\ DECIDE_TAC)
  \\ HO_MATCH_MP_TAC (theorem "pos_val_ind")
  \\ rpt strip_tac \\ fs [pos_val_def] \\ fs [all_enc_ok_def]
  THEN1 (rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO,has_odd_inst_def])
  THEN1 (rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO,has_odd_inst_def])
  \\ Cases_on `is_Label y` \\ fs []
  \\ Cases_on `x = 0` \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs [] \\ rw []
  \\ fs [has_odd_inst_def]
  \\ Cases_on `EVEN pos` \\ fs []
  \\ fs [EVEN_ADD]
  \\ imp_res_tac (GSYM MOD_PLUS)
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ imp_res_tac line_length_MOD_0 \\ fs [])
  |> Q.SPECL [`x`,`0`,`y`] |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO]
  |> SIMP_RULE std_ss [pos_val_MOD_0_lemma]
  |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC];

val lab_lookup_IMP = prove(
  ``(lab_lookup l1 l2 labs = SOME x) ==>
    (find_pos (Lab l1 l2) labs = x)``,
  fs [lab_lookup_def,find_pos_def,lookup_any_def]
  \\ BasicProvers.EVERY_CASE_TAC);

val state_rel_weaken = prove(
  ``state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
    state_rel (mc_conf,code2,labs,p,F) s1 t1 ms1``,
  fs [state_rel_def] \\ rpt strip_tac \\ fs [] \\ metis_tac []);

val read_bytearray_state_rel = prove(
  ``!n a x.
      state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 /\
      (read_bytearray a n s1 = SOME x) ==>
      (read_bytearray a n
        (\a. if a IN mc_conf.prog_addresses then SOME (t1.mem a) else NONE) =
       SOME x)``,
  Induct \\ fs [read_bytearray_def,target_semTheory.read_bytearray_def]
  \\ rpt strip_tac \\ Cases_on `mem_load_byte_aux a s1` \\ fs []
  \\ Cases_on `read_bytearray (a + 1w) n s1` \\ fs []
  \\ res_tac \\ fs [] \\ fs [state_rel_def,mem_load_byte_aux_def]
  \\ Cases_on `s1.mem (byte_align a)` \\ fs [] \\ rw []
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `a`) \\ fs []
  \\ rpt strip_tac \\ fs [word_loc_val_def]);

val aEval_pres_io_events_NONE = prove(
  ``!s1.
      (aEval s1 = (res,s2)) /\ (s1.io_events = NONE) ==> (s2.io_events = NONE)``,
  completeInduct_on `s1.clock`
  \\ rpt strip_tac \\ fs [PULL_FORALL] \\ rw []
  \\ ntac 2 (POP_ASSUM MP_TAC) \\ simp_tac std_ss [Once aEval_def,LET_DEF]
  \\ Cases_on `s1.clock = 0` \\ fs []
  \\ `0 < s1.clock` by decide_tac
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [LET_DEF] \\ rpt strip_tac
  \\ fs [AND_IMP_INTRO]
  \\ res_tac \\ fs [inc_pc_def,dec_clock_def,asm_inst_consts,upd_reg_def]
  \\ rfs [call_FFI_def] \\ res_tac \\ fs []);

val IMP_has_io_index = prove(
  ``(asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)) ==>
    has_io_index index s1.code``,
  fs [asm_fetch_def]
  \\ Q.SPEC_TAC (`s1.pc`,`pc`)
  \\ Q.SPEC_TAC (`s1.code`,`code`)
  \\ HO_MATCH_MP_TAC (theorem "asm_code_length_ind") \\ rpt strip_tac
  \\ fs [asm_fetch_aux_def,has_io_index_def] \\ res_tac
  \\ Cases_on `is_Label y` \\ fs []
  THEN1 (Cases_on `y` \\ fs [is_Label_def] \\ res_tac)
  \\ Cases_on `pc = 0` \\ fs [] \\ res_tac \\ fs []);

val write_bytearray_simp_lemma = prove(
  ``!new_bytes c1 s1 x.
      (read_bytearray (c1:'a word) (LENGTH new_bytes) s1 = SOME x) ==>
      (write_bytearray c1 new_bytes s1 =
         s1 with mem := (write_bytearray c1 new_bytes s1).mem)``,
  Induct \\ fs [write_bytearray_def]
  THEN1 (fs [theorem "asml_state_component_equality"])
  \\ fs [read_bytearray_def]
  \\ REPEAT STRIP_TAC
  \\ Cases_on `mem_load_byte_aux c1 s1` \\ fs []
  \\ Cases_on `read_bytearray (c1 + 1w) (LENGTH new_bytes) s1` \\ fs []
  \\ rw [] \\ res_tac \\ fs []
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
  \\ Cases_on `mem_store_byte_aux c1 h
     (s1 with mem := (write_bytearray (c1 + 1w) new_bytes s1).mem)` \\ fs []
  THEN1 (fs [theorem "asml_state_component_equality"])
  \\ fs [mem_store_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs [upd_mem_def] \\ rw []);

val read_bytearray_LENGTH = prove(
  ``!n a s x.
      (read_bytearray a n s = SOME x) ==> (LENGTH x = n)``,
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac);

val write_bytearray_simp = prove(
  ``(read_bytearray (c1:'a word) (w2n (c2:'a word)) s1 = SOME x) /\
    (call_FFI index x s1.io_events = (new_bytes,new_io)) ==>
    (write_bytearray c1 new_bytes s1 =
       s1 with mem := (write_bytearray c1 new_bytes s1).mem)``,
  REPEAT STRIP_TAC
  \\ MATCH_MP_TAC (GEN_ALL write_bytearray_simp_lemma)
  \\ imp_res_tac read_bytearray_LENGTH
  \\ fs [call_FFI_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac
  \\ fs [listTheory.LENGTH_MAP]) |> SPEC_ALL;

val call_FFI_LENGTH = prove(
  ``(call_FFI index x io = (new_bytes,new_io)) ==>
    (LENGTH x = LENGTH new_bytes)``,
  fs [call_FFI_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ rw [] \\ fs [listTheory.LENGTH_MAP]);

val bytes_in_mem_asm_write_bytearray_lemma = prove(
  ``!xs p.
      (!a. ~(a IN k) ==> (m1 a = m2 a)) ==>
      bytes_in_mem p xs m1 d k ==>
      bytes_in_mem p xs m2 d k``,
  Induct \\ fs [bytes_in_mem_def]);

val bytes_in_mem_asm_write_bytearray = prove(
  ``state_rel ((mc_conf: ('a,'state,'b) machine_config),code2,labs,p,T) s1 t1 ms1 /\
    (read_bytearray c1 (LENGTH new_bytes) s1 = SOME x) ==>
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
  \\ fs [read_bytearray_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ fs [PULL_FORALL]
  \\ res_tac
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ fs [mem_load_byte_aux_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw []
  \\ rw [combinTheory.APPLY_UPDATE_THM]
  \\ fs [state_rel_def] \\ res_tac);

val option_ldrop_0 = prove(
  ``!ll. option_ldrop 0 ll = ll``,
  Cases \\ fs [option_ldrop_def]);

val LDROP_ADD = prove(
  ``!k1 k2 x.
      LDROP (k1 + k2) x = case LDROP k1 x of
                          | NONE => NONE
                          | SOME ll => LDROP k2 ll``,
  Induct \\ fs [ADD_CLAUSES] \\ fs [llistTheory.LDROP] \\ REPEAT STRIP_TAC
  \\ Cases_on `LTL x` \\ fs []
  \\ Cases_on `LDROP k1 x'` \\ fs []);

val option_ldrop_SUC = prove(
  ``!k1 ll. option_ldrop (SUC k1) ll = option_ldrop 1 (option_ldrop k1 ll)``,
  Cases_on `ll` \\ fs [option_ldrop_def]
  \\ REPEAT STRIP_TAC \\ fs [ADD1] \\ fs [LDROP_ADD]
  \\ Cases_on `LDROP k1 x` \\ fs [option_ldrop_def]);

val option_ldrop_option_ldrop = prove(
  ``!k1 ll k2.
      option_ldrop k1 (option_ldrop k2 ll) = option_ldrop (k1 + k2) ll``,
  Induct \\ fs [option_ldrop_def,option_ldrop_0]
  \\ REPEAT STRIP_TAC \\ fs [option_ldrop_SUC,ADD_CLAUSES]);

val option_ldrop_lemma = prove(
  ``(call_FFI index x io = (new_bytes,new_io)) /\ new_io <> NONE ==>
    (new_io = option_ldrop 1 io)``,
  fs [call_FFI_def] \\ BasicProvers.EVERY_CASE_TAC
  \\ rw [option_ldrop_def]
  \\ Q.MATCH_ASSUM_RENAME_TAC `LTL ll <> NONE`
  \\ `(ll = [||]) \/ ?h t. ll = h:::t` by metis_tac [llistTheory.llist_CASES]
  \\ fs [llistTheory.LDROP1_THM]);

val aEval_IMP_mEval = prove(
  ``!s1 res (mc_conf: ('a,'state,'b) machine_config) s2 code2 labs t1 ms1.
      (aEval s1 = (res,s2)) /\ (res <> Error Internal) /\ s1.io_events <> NONE /\
      backend_correct_alt mc_conf.f mc_conf.asm_config /\
      state_rel (mc_conf,code2,labs,p,T) s1 t1 ms1 ==>
      ?k t2 ms2.
        (mEval mc_conf s1.io_events (s1.clock + k) ms1 =
           (if s2.io_events = NONE then Error IO_mismatch
            else res,ms2,s2.io_events))``,

  HO_MATCH_MP_TAC aEval_ind \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [aEval_def]
  \\ Cases_on `s1.clock = 0` \\ fs []
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ fs [Once mEval_def] \\ metis_tac [state_rel_weaken])
  \\ Cases_on `asm_fetch s1` \\ fs []
  \\ Cases_on `x` \\ fs [] \\ Cases_on `a` \\ fs []
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ fs [LET_DEF]
  THEN1 (* Asm Inst *) cheat
  THEN1 (* Asm JumpReg *)
   (Cases_on `read_reg n' s1` \\ fs []
    \\ qmatch_assum_rename_tac `read_reg r1 s1 = Loc l1 l2`
    \\ Cases_on `loc_to_pc l1 l2 s1.code` \\ fs []
    \\ MP_TAC (Q.SPECL [`mc_conf`,`t1`,`ms1`,`s1.io_events`,`JumpReg r1`]
         asm_step_IMP_mEval_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_alt_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [IMP_bytes_in_memory_JumpReg,asmTheory.upd_pc_def,asmTheory.assert_def]
      \\ imp_res_tac IMP_bytes_in_memory_JumpReg \\ fs []
      \\ fs [asmTheory.read_reg_def,read_reg_def]
      \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rfs []
      \\ fs [word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ fs []
      \\ Q.PAT_ASSUM `xx = t1.regs r1` (fn th => fs [GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
      \\ MATCH_MP_TAC pos_val_MOD_0 \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,`(asm (JumpReg r1)
            (t1.pc + n2w (LENGTH (mc_conf.f.encode (JumpReg r1)))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
      \\ fs [asmTheory.upd_pc_def,asmTheory.assert_def,asmTheory.read_reg_def,
             dec_clock_def,upd_pc_def,assert_def,read_reg_def]
      \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
      \\ FIRST_X_ASSUM (K ALL_TAC o Q.SPEC `r1:num`)
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `r1:num`)
      \\ strip_tac \\ rfs []
      \\ fs [word_loc_val_def]
      \\ Cases_on `lab_lookup l1 l2 labs` \\ fs []
      \\ Q.PAT_ASSUM `xx = t1.regs r1` (fn th => fs [GSYM th])
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
      \\ RES_TAC \\ fs [] \\ rpt strip_tac \\ res_tac \\ rw []
      \\ MATCH_MP_TAC pos_val_MOD_0 \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s1.clock - 1 + k`) \\ rw []
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
    \\ Q.EXISTS_TAC `t2` \\ fs [state_rel_def,shift_interfer_def]
    \\ rpt strip_tac \\ res_tac \\ rfs [])
  THEN1 (* Jump *)
   (qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm (Jump target) l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (Jump target) l bytes n)`
    \\ Cases_on `get_pc_value target s1` \\ fs []
    \\ mp_tac IMP_bytes_in_memory_Jump \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ MP_TAC (Q.SPECL [`mc_conf`,`t1`,`ms1`,`s1.io_events`,`jj`]
         asm_step_IMP_mEval_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_alt_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [asmTheory.jump_to_offset_def,asmTheory.upd_pc_def]
      \\ rfs [] \\ unabbrev_all_tac
      \\ fs [asmTheory.jump_to_offset_def,asmTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer l' mc_conf`,
         `code2`,`labs`,
         `(asm jj (t1.pc + n2w (LENGTH (mc_conf.f.encode jj))) t1)`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (unabbrev_all_tac
      \\ fs [shift_interfer_def,state_rel_def,asm_def,LET_DEF] \\ rfs[]
      \\ fs [asmTheory.upd_pc_def,asmTheory.assert_def,asmTheory.read_reg_def,
             dec_clock_def,upd_pc_def,assert_def,read_reg_def,asm_def,
             jump_to_offset_def]
      \\ fs [interference_ok_def,shift_seq_def,read_reg_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ Cases_on `target` \\ fs []
      \\ qmatch_assum_rename_tac `loc_to_pc l1 l2 s1.code = SOME x`
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`l1`,`l2`]) \\ fs [] \\ rw []
      \\ imp_res_tac lab_lookup_IMP \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s1.clock - 1 + k`) \\ rw []
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
    \\ Q.EXISTS_TAC `t2` \\ fs [state_rel_def,shift_interfer_def]
    \\ rpt strip_tac \\ res_tac \\ rfs [])
  THEN1 (* JumpCmp *) cheat
  THEN1 (* Call *) cheat
  THEN1 (* LocValue *) cheat

  THEN1 (* CallFFI *)

   (

    qmatch_assum_rename_tac `asm_fetch s1 = SOME (LabAsm (CallFFI n') l1 l2 l3)`
    \\ qmatch_assum_rename_tac
         `asm_fetch s1 = SOME (LabAsm (CallFFI index) l bytes n)`
    \\ Cases_on `s1.regs s1.len_reg` \\ fs []
    \\ Cases_on `s1.regs s1.ptr_reg` \\ fs []
    \\ Cases_on `s1.regs s1.link_reg` \\ fs []
    \\ Cases_on `read_bytearray c' (w2n c) s1` \\ fs []
    \\ qmatch_assum_rename_tac `read_bytearray c1 (w2n c2) s1 = SOME x`
    \\ qmatch_assum_rename_tac `s1.regs s1.link_reg = Loc n1 n2`
    \\ Cases_on `call_FFI index x s1.io_events` \\ fs []
    \\ qmatch_assum_rename_tac `call_FFI index x s1.io_events = (new_bytes,new_io)`
    \\ mp_tac IMP_bytes_in_memory_CallFFI \\ fs []
    \\ match_mp_tac IMP_IMP \\ strip_tac
    THEN1 (fs [state_rel_def] \\ imp_res_tac bytes_in_mem_IMP \\ fs [])
    \\ rpt strip_tac \\ pop_assum mp_tac
    \\ qpat_abbrev_tac `jj = asm$Jump lll` \\ rpt strip_tac
    \\ MP_TAC (Q.SPECL [`mc_conf`,`t1`,`ms1`,`s1.io_events`,`jj`]
         asm_step_IMP_mEval_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_alt_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [asmTheory.jump_to_offset_def,asmTheory.upd_pc_def]
      \\ rfs [] \\ unabbrev_all_tac
      \\ fs [asmTheory.jump_to_offset_def,asmTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ Cases_on `loc_to_pc n1 n2 s1.code` \\ fs []
    \\ qmatch_assum_rename_tac `loc_to_pc n1 n2 s1.code = SOME new_pc`
    \\ `mc_conf.f.get_pc ms2 = p - n2w ((3 + index) * ffi_offset)` by
     (fs [state_rel_def] \\ rfs []
      \\ fs [backend_correct_alt_def]
      \\ Q.PAT_ASSUM `!ms s. mc_conf.f.state_rel s ms ==> bbb` imp_res_tac
      \\ fs [] \\ unabbrev_all_tac
      \\ fs [asm_def,jump_to_offset_def,asmTheory.upd_pc_def]
      \\ rewrite_tac [GSYM word_sub_def,WORD_SUB_PLUS,
           GSYM word_add_n2w,WORD_ADD_SUB]) \\ fs []
    \\ `has_io_index index s1.code` by
          (imp_res_tac IMP_has_io_index \\ NO_TAC)
    \\ `~(mc_conf.f.get_pc ms2 IN mc_conf.prog_addresses) /\
        ~(mc_conf.f.get_pc ms2 = mc_conf.halt_pc) /\
        (list_find (mc_conf.f.get_pc ms2) mc_conf.ffi_entry_pcs =
           SOME index)` by
      (fs [state_rel_def]
       \\ Q.PAT_ASSUM `!kk. has_io_index kk s1.code ==> bbb` imp_res_tac
       \\ rfs [])
    \\ `(mc_conf.f.get_reg ms2 mc_conf.ptr_reg = t1.regs mc_conf.ptr_reg) /\
        (mc_conf.f.get_reg ms2 mc_conf.len_reg = t1.regs mc_conf.len_reg) /\
        !a. a IN mc_conf.prog_addresses ==>
            (mc_conf.f.get_byte ms2 a = t1.mem a)` by
     (fs [backend_correct_alt_def |> REWRITE_RULE [GSYM reg_ok_def]]
      \\ res_tac \\ unabbrev_all_tac \\ fs [state_rel_def,asm_def,
           jump_to_offset_def,asmTheory.upd_pc_def] \\ NO_TAC) \\ fs []
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
    \\ Cases_on `new_io = NONE` THEN1
     (imp_res_tac aEval_pres_io_events_NONE \\ fs [] \\ rfs []
      \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s1.clock`) \\ rpt strip_tac
      \\ Q.EXISTS_TAC `l'` \\ fs [ADD_ASSOC]
      \\ once_rewrite_tac [mEval_def] \\ fs []
      \\ fs [shift_interfer_def,LET_DEF]) \\ fs []
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [
         `shift_interfer l' mc_conf with
          ffi_interfer := shift_seq 1 mc_conf.ffi_interfer`,
         `code2`,`labs`,
         `t1 with <| pc := p + n2w (pos_val new_pc 0 (code2:'a asm_prog)) ;
                     mem := asm_write_bytearray c1 new_bytes t1.mem ;
                     regs := \a. get_reg_value (s1.io_regs 0 a) (t1.regs a) I |>`,
         `mc_conf.ffi_interfer 0 index new_bytes ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1

     (

      rpt strip_tac
      THEN1 (fs [backend_correct_alt_def,shift_interfer_def] \\ metis_tac [])
      \\ unabbrev_all_tac
      \\ imp_res_tac bytes_in_mem_asm_write_bytearray
      \\ fs [state_rel_def,shift_interfer_def,asm_def,jump_to_offset_def,
             asmTheory.upd_pc_def] \\ rfs[]
      \\ mp_tac write_bytearray_simp \\ fs []
      \\ strip_tac \\ pop_assum (fn th => once_rewrite_tac [th] THEN fs [] THEN
                         fs [GSYM th])
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ full_simp_tac bool_ss [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
            WORD_ADD_SUB] \\ fs [get_pc_value_def]
      \\ `interference_ok (shift_seq l' mc_conf.next_interfer)
            (mc_conf.f.proj t1.mem_domain)` by
               (fs [interference_ok_def,shift_seq_def] \\ NO_TAC) \\ fs []
      \\ `p + n2w (pos_val new_pc 0 code2) = t1.regs s1.link_reg` by
       (Q.PAT_ASSUM `!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)`
           (MP_TAC o Q.SPEC `s1.link_reg`) \\ fs [word_loc_val_def]
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
       (fs [shift_seq_def,PULL_FORALL,AND_IMP_INTRO]
        \\ Q.PAT_ASSUM `!(ms:'state) x2 x3 x4 x5 x6 x7. bbb` match_mp_tac
        \\ qexists_tac `new_io'` \\ qexists_tac `x'` \\ fs []
        \\ imp_res_tac option_ldrop_lemma \\ fs [] \\ rfs []
        \\ fs [option_ldrop_option_ldrop])
      THEN1
       (Cases_on `s1.io_regs 0 r`
        \\ fs [get_reg_value_def,word_loc_val_def])
      \\ cheat (* requires messing around with bytearrays *))

    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s1.clock + k`) \\ rpt strip_tac
    \\ Q.EXISTS_TAC `k + l'` \\ fs [ADD_ASSOC]
    \\ Q.LIST_EXISTS_TAC [`ms2'`] \\ fs []
    \\ simp_tac std_ss [Once mEval_def]
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
    \\ MP_TAC (Q.SPECL [`mc_conf`,`t1`,`ms1`,`s1.io_events`,`jj`]
         asm_step_IMP_mEval_step) \\ fs []
    \\ MATCH_MP_TAC IMP_IMP2 \\ STRIP_TAC THEN1
     (fs [state_rel_def,asm_def,LET_DEF]
      \\ fs [asm_step_alt_def,asm_def,LET_DEF]
      \\ imp_res_tac bytes_in_mem_IMP
      \\ fs [asmTheory.jump_to_offset_def,asmTheory.upd_pc_def]
      \\ rfs [] \\ unabbrev_all_tac
      \\ fs [asmTheory.jump_to_offset_def,asmTheory.upd_pc_def,asm_def])
    \\ rpt strip_tac
    \\ unabbrev_all_tac \\ fs [asm_def]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s1.clock`) \\ rw []
    \\ Q.EXISTS_TAC `l'` \\ fs []
    \\ once_rewrite_tac [mEval_def] \\ fs []
    \\ fs [shift_interfer_def]
    \\ `mc_conf.f.get_pc ms2 = mc_conf.halt_pc` by
     (fs [backend_correct_alt_def] \\ res_tac \\ fs []
      \\ fs [jump_to_offset_def,asmTheory.upd_pc_def] \\ fs [state_rel_def]
      \\ rewrite_tac [GSYM word_add_n2w,GSYM word_sub_def,WORD_SUB_PLUS,
           WORD_ADD_SUB] \\ fs [])
    \\ `~(mc_conf.f.get_pc ms2 IN t1.mem_domain)` by fs [state_rel_def]
    \\ fs [state_rel_def,jump_to_offset_def,asmTheory.upd_pc_def]));

(*

TODO:
 - fix semantics of CallFFI, finish proof
 - weaken all_enc_ok
 - define an incremental version of the compiler
 - add ability to install code

*)

val _ = export_theory();
