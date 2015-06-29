open HolKernel Parse boolLib bossLib;
open asmTheory wordsTheory wordsLib sptreeTheory ffiTheory;
open target_semTheory word_locTheory lcsymtacs;
open arithmeticTheory

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
     ; mem        : 'a word -> word8_loc
     ; mem_domain : 'a word set
     ; pc         : num
     ; be         : bool
     ; io_events  : io_trace
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
val upd_reg_def  = Define `upd_reg r v s = s with regs := (r =+ v) s.regs`
val upd_mem_def  = Define `upd_mem a b s = s with mem := (a =+ b) s.mem`
val read_reg_def = Define `read_reg r s = s.regs r`
val read_mem_def = Define `read_mem a s = s.mem a`

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

val read_mem_list_def = Define `
  (read_mem_list a 0 s = ([],s)) /\
  (read_mem_list a (SUC n) s =
     let (w,s1) = read_mem_list (if s.be then a - 1w else a + 1w) n s in
       (w ++ [read_mem a s1], assert (a IN s1.mem_domain) s1))`

val list_to_word_loc_def = Define `
  (list_to_word_loc [] = NONE) /\
  (list_to_word_loc [Byte b] = SOME (Word (w2w b))) /\
  (list_to_word_loc (Byte b::rest) =
     case list_to_word_loc rest of
     | SOME (Word w) => SOME (Word (word_or (w << 8) (w2w b)))
     | _ => NONE) /\
  (list_to_word_loc [LocByte n1 n2 i] =
     if i = 0 then SOME (Loc n1 n2) else NONE) /\
  (list_to_word_loc (LocByte n1 n2 i::rest) =
     if (LENGTH rest = i) /\
        (list_to_word_loc rest = SOME (Loc n1 n2))
     then SOME (Loc n1 n2)
     else NONE)`

val is_Loc_def = Define `(is_Loc (Loc _ _) = T) /\ (is_Loc _ = F)`;

val mem_load_def = Define `
  mem_load n r a (s:'a asml_state) =
    let ax = addr a s in
    let a = THE ax in
    let a = if s.be then a + n2w (n - 1) else a in
    let (l,s) = read_mem_list a n s in
    let lx = list_to_word_loc l in
    let s = upd_reg r (THE lx) s in
      assert ((a && n2w (n - 1) = 0w) /\ lx <> NONE /\ ax <> NONE /\
              (is_Loc (THE lx) ==> (n = dimindex (:'a) DIV 8))) s`

val write_mem_list_def = Define `
  (write_mem_list a [] s = s) /\
  (write_mem_list a (l::ls) s =
     let s1 = write_mem_list (if s.be then a - 1w else a + 1w) ls s in
       assert (a IN s1.mem_domain) (upd_mem a l s1))`

val word_loc_to_list_def = Define `
  (word_loc_to_list (Loc n1 n2) n =
     GENLIST (\n. LocByte n1 n2 n) n) /\
  (word_loc_to_list (Word w) n =
     GENLIST (\n. Byte (w2w (w >>> (8 * n)))) n)`;

val mem_store_def = Define `
  mem_store n r a (s:'a asml_state) =
    let ax = addr a s in
    let a = THE ax in
    let a = if s.be then a + n2w (n - 1) else a in
    let w = read_reg r s in
    let l = word_loc_to_list w n in
    let s = write_mem_list a l s in
      assert ((a && n2w (n - 1) = 0w) /\ ax <> NONE /\
              (is_Loc w ==> (n = dimindex (:'a) DIV 8))) s`

val mem_op_def = Define `
  (mem_op Load r a = mem_load (dimindex (:'a) DIV 8) r a) /\
  (mem_op Store r a = mem_store (dimindex (:'a) DIV 8) r a) /\
  (mem_op Load8 r a = mem_load 1 r a) /\
  (mem_op Store8 r a = mem_store 1 r a) /\
  (mem_op Load32 r (a:'a addr) = mem_load 4 r a) /\
  (mem_op Store32 r (a:'a addr) = mem_store 4 r a)`

val asm_inst_def = Define `
  (asm_inst Skip s = (s:'a asml_state)) /\
  (asm_inst (Const r imm) s = upd_reg r (Word imm) s) /\
  (asm_inst (Arith x) s = arith_upd x s) /\
  (asm_inst (Mem m r a) s = mem_op m r a s)`

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

val read_mem_list_consts = prove(
  ``!n a s. ((SND (read_mem_list a n s)).pc = s.pc) /\
            ((SND (read_mem_list a n s)).code = s.code) /\
            ((SND (read_mem_list a n s)).clock = s.clock) /\
            ((SND (read_mem_list a n s)).io_events = s.io_events)``,
  Induct \\ fs [read_mem_list_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [assert_def]);

val write_mem_list_consts = prove(
  ``!n a s. (((write_mem_list a n s)).pc = s.pc) /\
            (((write_mem_list a n s)).code = s.code) /\
            (((write_mem_list a n s)).clock = s.clock) /\
            (((write_mem_list a n s)).io_events = s.io_events)``,
  Induct \\ fs [write_mem_list_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [assert_def,upd_mem_def]);

val asm_inst_consts = prove(
  ``((asm_inst i s).pc = s.pc) /\
    ((asm_inst i s).code = s.code) /\
    ((asm_inst i s).clock = s.clock) /\
    ((asm_inst i s).io_events = s.io_events)``,
  Cases_on `i` \\ fs [asm_inst_def,upd_reg_def,arith_upd_def]
  \\ TRY (Cases_on `a`)
  \\ fs [asm_inst_def,upd_reg_def,arith_upd_def,read_reg_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ TRY (Cases_on `b`)
  \\ fs [binop_upd_def,upd_reg_def,assert_def]
  \\ Cases_on `m`
  \\ fs [mem_op_def,mem_load_def,LET_DEF,
         assert_def,upd_reg_def,mem_store_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [read_mem_list_consts,write_mem_list_consts]);

val get_pc_value_def = Define `
  get_pc_value lab (s:'a asml_state) =
    case lab of
    | Lab n1 n2 => loc_to_pc n1 n2 s.code`;

val read_bytearray_def = Define `
  (read_bytearray a 0 s = SOME []) /\
  (read_bytearray a (SUC n) s =
     if ~(a IN s.mem_domain) then NONE else
       case s.mem a of
       | Byte b =>
        (case read_bytearray (a+1w) n s of
         | SOME bytes => SOME (b::bytes)
         | _ => NONE)
       | _ => NONE)`

val write_bytearray_def = Define `
  (write_bytearray a [] m = m) /\
  (write_bytearray a (b::bs) m =
     let s' = write_bytearray (a+1w) bs m in
       (a =+ Byte b) m)`

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
       (case (s.regs s.len_reg,s.regs s.ptr_reg) of
        | (Word w, Word w2) =>
         (case read_bytearray w2 (w2n w) s of
          | NONE => (Error Internal,s)
          | SOME bytes =>
              let (new_bytes,new_io) = call_FFI ffi_index bytes s.io_events in
                aEval (s with <| io_events := new_io ;
                                 mem := write_bytearray w2 new_bytes s.mem ;
                                 pc := s.pc + 1 ;
                                 clock := s.clock - 1 |>))
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

(* basic assemble function *)

val lab_inst_def = Define `
  (lab_inst w (Jump _) = Jump w) /\
  (lab_inst w (JumpCmp c r ri _) = JumpCmp c r ri w) /\
  (lab_inst w (Call _) = Call w) /\
  (lab_inst w (LocValue r _) = Loc r (w:'a word)) /\
  (lab_inst w (Halt) = Jump w) /\
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

val get_label_def = Define `
  (get_label (Jump l) = l) /\
  (get_label (JumpCmp c r ri l) = l) /\
  (get_label (Call l) = l) /\
  (get_label (LocValue r l) = l)`;

val lookup_any_def = Define `
  lookup_any x sp d =
    case lookup x sp of
    | NONE => d
    | SOME m => m`;

val find_pos_def = Define `
  find_pos (Lab k1 k2) labs =
    (lookup_any k2 (lookup_any k1 labs LN) 0):num`;

val enc_line_again_def = Define `
  (enc_line_again labs pos enc [] = []) /\
  (enc_line_again labs pos enc ((Label k1 k2 l)::xs) =
     (Label k1 k2 l) :: enc_line_again labs (pos+l) enc xs) /\
  (enc_line_again labs pos enc ((Asm x1 x2 l)::xs) =
     (Asm x1 x2 l) :: enc_line_again labs (pos+l) enc xs) /\
  (enc_line_again labs pos enc ((LabAsm a w bytes l)::xs) =
     let pos = pos + l in
     let target = find_pos (get_label a) labs in
     let w1 = n2w target - n2w pos in
       if w = w1 then
         (LabAsm a w bytes l)::enc_line_again labs pos enc xs
       else
         let bs = enc (lab_inst w1 a) in
           LabAsm a 0w bs (LENGTH bs)::enc_line_again labs pos enc xs)`

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
  (line_ok c enc labs pos (Label _ _ l) <=>
     if EVEN pos then (l = 0) else (l = 1)) /\
  (line_ok c enc labs pos (Asm b bytes l) <=>
     (bytes = enc b) /\ (LENGTH bytes = l) /\ asm_ok b c) /\
  (line_ok c enc labs pos (LabAsm a w bytes l) <=>
     let pos = pos + l in
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
  (pos_val i pos [] = pos) /\
  (pos_val i pos ((Section k [])::xs) =
     if EVEN pos then pos_val i pos xs else pos_val i (pos + 1) xs) /\
  (pos_val i pos ((Section k (y::ys))::xs) =
     if is_Label y
     then pos_val i (pos + line_length y) ((Section k ys)::xs)
     else if i = 0:num then pos
          else pos_val (i-1) (pos + line_length y) ((Section k ys)::xs))`

val state_rel_def = Define `
  state_rel (mc_conf, code2, labs, p) (s1:'a asml_state) t1 ms1 <=>
    mc_conf.f.state_rel t1 ms1 /\
    (mc_conf.prog_addresses = t1.mem_domain) /\
    interference_ok mc_conf.next_interfer (mc_conf.f.proj t1.mem_domain) /\
    (!q n. (n2w (t1.align - 1) && q + n2w n = 0w:'a word) <=> (n MOD t1.align = 0)) /\
    (!l1 l2 x1 x2.
       (lab_lookup l1 l2 labs = SOME x1) /\
       (loc_to_pc l1 l2 s1.code = SOME x2) ==>
       (pos_val x2 0 code2 = x1)) /\
    (!r. word_loc_val p labs (s1.regs r) = SOME (t1.regs r)) /\
    (!a. a IN s1.mem_domain ==>
         a IN t1.mem_domain /\
         (word8_loc_val p labs (s1.mem a) = SOME (t1.mem a))) /\
    bytes_in_mem p (prog_to_bytes mc_conf.f.encode code2)
      t1.mem t1.mem_domain s1.mem_domain /\
    ~s1.failed /\ ~t1.failed /\ (s1.be = t1.be) /\
    (t1.pc = p + n2w (pos_val s1.pc 0 code2)) /\
    (p && n2w (t1.align - 1) = 0w) /\
    (case mc_conf.asm_config.link_reg of NONE => T | SOME r => t1.lr = r) /\
    (t1.be <=> mc_conf.asm_config.big_endian) /\
    (t1.align = mc_conf.asm_config.code_alignment) /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    code_similar s1.code code2`

val all_bytes_lemma = prove(
  ``!code2 code1 pc i pos.
       code_similar code1 code2 /\
       (asm_fetch_aux pc code1 = SOME i) ==>
       ?bs code2' j.
         (all_bytes pos (nop_byte mc_conf.f.encode) code2  =
          bs ++ all_bytes (pos + LENGTH bs) (nop_byte mc_conf.f.encode) code2') /\
         (LENGTH bs + pos = pos_val pc pos code2) /\
         code_similar code1 code2 /\
         (asm_fetch_aux 0 code2' = SOME j) /\
         line_similar i j``,
  HO_MATCH_MP_TAC (theorem "asm_code_length_ind") \\ REPEAT STRIP_TAC
  THEN1 (Cases_on `code1` \\ fs [code_similar_def,asm_fetch_aux_def])
  THEN1
   (Cases_on `code1` \\ fs [code_similar_def]
    \\ Cases_on `h` \\ fs [code_similar_def]
    \\ Cases_on `l` \\ fs [asm_fetch_aux_def,pos_val_def] \\ rw []
    \\ fs [all_bytes_def] THEN1 (metis_tac [])
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
    \\ fs [code_similar_def] \\ REPEAT STRIP_TAC
    \\ fs [prog_to_bytes_def,LET_DEF]
    \\ Q.LIST_EXISTS_TAC [`line_bytes x2 (nop_byte mc_conf.f.encode) ++ bs`,
         `code2'`]
    \\ fs [AC ADD_COMM ADD_ASSOC]
    \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
    \\ Cases_on `x2` \\ fs [line_bytes_def,line_length_def] \\ rw [])
  \\ Cases_on `pc = 0` \\ fs [] \\ rw []
  THEN1
   (fs [listTheory.LENGTH_NIL]
    \\ Q.EXISTS_TAC `Section k (x2::ys2)::xs`
    \\ fs [asm_fetch_aux_def])
  \\ fs [all_bytes_def,LET_DEF]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`(Section k ys1)::t`,`pc-1`,`i`,
       `(pos + LENGTH (line_bytes x2 (nop_byte mc_conf.f.encode)))`])
  \\ fs [code_similar_def] \\ rpt strip_tac \\ fs []
  \\ Q.LIST_EXISTS_TAC [`line_bytes x2 (nop_byte mc_conf.f.encode) ++ bs`,
        `code2'`,`j`] \\ fs []
  \\ fs [AC ADD_COMM ADD_ASSOC]
  \\ REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC)
  \\ Cases_on `x2` \\ fs [line_bytes_def,line_length_def] \\ rw [])

val prog_to_bytes_lemma = all_bytes_lemma
  |> Q.SPECL [`code2`,`code1`,`pc`,`i`,`0`]
  |> SIMP_RULE std_ss [GSYM prog_to_bytes_def];


(*

val IMP_mem_load_failed = prove(
  ``~s.failed /\ ((addr a s) && n2w (n - 1) = 0w) /\
    { addr a s + n2w k | k < n } SUBSET s.mem_domain ==>
    ~(asm$mem_load n r a s).failed``,
  cheat);

val mem_load_failed_IMP = prove(
  ``~(mem_load n r a s).failed ==>
    ((THE (addr a s)) && n2w (n - 1) = 0w) /\
    { THE (addr a s) + n2w k | k < n } SUBSET s.mem_domain``,
  cheat);

val mem_load_failed = prove(
  ``(!a. a IN s1.mem_domain ==> a IN t1.mem_domain) /\ ~t1.failed /\
    (addr (Addr n' c) s1 = SOME (addr (Addr n' c) t1)) ==>
    ~(mem_load k n (Addr n' c) s1).failed ==>
    ~(asm$mem_load k n (Addr n' c) t1).failed``,
  STRIP_TAC \\ STRIP_TAC
  \\ MATCH_MP_TAC IMP_mem_load_failed \\ fs []
  \\ IMP_RES_TAC mem_load_failed_IMP
  \\ rfs [] \\ fs [pred_setTheory.SUBSET_DEF]);

val mem_store_failed = prove(
  ``(!a. a IN s1.mem_domain ==> a IN t1.mem_domain) ==>
    ~(mem_store k n (Addr n' c) s1).failed ==>
    ~(asm$mem_store k n (Addr n' c) t1).failed``,
  cheat);

val asm_fetch_ok = prove(
  ``(asm_fetch s1 = SOME (Asm (Inst i) l n)) /\
    all_enc_ok asm_conf enc labs 0 code2 /\
    code_similar s1.code code2 ==>
    bytes_in_memory (p + n2w (pos_val s1.pc code2))
      (mc_conf.f.encode (Inst i)) t1.mem t1.mem_domain /\
    asm_ok (Inst i) mc_conf.asm_config``,
  cheat); (* provable? -- but there should be a more general lemma *)

val asm_inst_failed_IMP_inst_failed = prove(
  ``state_rel (asm_conf,mc_conf,enc,code2,labs,p) s1 t1 ms1 /\
    ~(asm_inst i s1).failed ==> ~(inst i t1).failed``,
  Cases_on `i`
  \\ TRY (Cases_on `a`) \\ TRY (Cases_on `b`) \\ TRY (Cases_on `m`)
  \\ fs [inst_def,state_rel_def,asmTheory.upd_reg_def,asm_inst_def,
         asmTheory.arith_upd_def,asmTheory.binop_upd_def,mem_op_def,
         asmTheory.mem_op_def]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM MP_TAC \\ fs []
  \\ POP_ASSUM MP_TAC \\ fs []
  \\ TRY (MATCH_MP_TAC mem_load_failed \\ fs [] \\ NO_TAC)
  \\ TRY (MATCH_MP_TAC mem_store_failed \\ fs [] \\ NO_TAC)
  \\ cheat);

val IMP_asm_step_alt = prove(
  ``(asm_fetch s1 = SOME (Asm (Inst i) l n)) /\
    ~(asm_inst i s1).failed /\
    state_rel (asm_conf,mc_conf,enc,code2,labs,p) s1 t1 ms1 ==>
    asm_step_alt mc_conf.f.encode mc_conf.asm_config t1 (Inst i)
      (asm (Inst i) (t1.pc + n2w (LENGTH (mc_conf.f.encode (Inst i)))) t1)``,
  fs [asm_step_alt_def,asm_def,asmTheory.upd_pc_def] \\ STRIP_TAC
  \\ IMP_RES_TAC asm_inst_failed_IMP_inst_failed \\ fs [state_rel_def]
  \\ MATCH_MP_TAC asm_fetch_ok \\ fs []);




val prog_to_bytes_Section_NIL = prove(
  ``prog_to_bytes mc_conf.f.encode (Section k []::code2) =
    prog_to_bytes mc_conf.f.encode code2``,
  fs [prog_to_bytes_def,LET_DEF,all_sec_bytes_def,sec_length_def]);


prog_to_bytes_def
pos_val_def






all_sec_bytes_def







    \\ cheat)
  \\ cheat);


  all_enc_ok_def

val IMP_bytes_in_memory = prove(
  ``code_similar code1 code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    (asm_fetch_aux pc code1 = SOME i) /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) t1.mem
      (t1:'a asm_state).mem_domain ==>
    ?j.
      (get_bytes j = SOME bytes) /\ line_similar i j /\
      bytes_in_memory (p + n2w (pos_val pc code2)) bytes t1.mem t1.mem_domain /\
      line_ok (mc_conf:('a,'state,'b) machine_config).asm_config
        mc_conf.f.encode labs (pos_val pc code2) j``,
  cheat);

all_enc_ok_def


*)



val bytes_in_mem_IMP = prove(
  ``!xs p. bytes_in_mem p xs m dm dm1 ==> bytes_in_memory p xs m dm``,
  Induct \\ fs [bytes_in_mem_def,bytes_in_memory_def]);

val IMP_bytes_in_memory = prove(
  ``code_similar code1 code2 /\
    all_enc_ok mc_conf.asm_config mc_conf.f.encode labs 0 code2 /\
    (asm_fetch_aux pc code1 = SOME (Asm (JumpReg r1) l n)) /\
    bytes_in_memory p (prog_to_bytes mc_conf.f.encode code2) t1.mem
      (t1:'a asm_state).mem_domain ==>
    bytes_in_memory (p + n2w (pos_val pc 0 code2))
      (mc_conf.f.encode (JumpReg r1)) t1.mem t1.mem_domain /\
    line_ok (mc_conf:('a,'state,'b) machine_config).asm_config
      mc_conf.f.encode labs (pos_val pc 0 code2) (Asm (JumpReg r1) l n)``,
  cheat);

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
  \\ mp_tac IMP_bytes_in_memory \\ fs []
  \\ rpt strip_tac \\ fs [line_ok_def]);

val line_length_MOD_0 = prove(
  ``backend_correct_alt mc_conf.f mc_conf.asm_config /\
    (~EVEN p ==> (mc_conf.asm_config.code_alignment = 1)) /\
    line_ok mc_conf.asm_config mc_conf.f.encode labs p h ==>
    (line_length h MOD mc_conf.asm_config.code_alignment = 0)``,
  Cases_on `h` \\ fs [line_ok_def,line_length_def]
  \\ rw [] \\ fs [backend_correct_alt_def,enc_ok_def]
  \\ Q.PAT_ASSUM `xxx = LENGTH yy` (ASSUME_TAC o GSYM)
  \\ `0 < mc_conf.asm_config.code_alignment` by
       (fs [backend_correct_alt_def,enc_ok_def] \\ DECIDE_TAC)
  \\ fs [LET_DEF] \\ rw []
  \\ Q.PAT_ASSUM `l = xxx` (fn th => once_rewrite_tac [th]) \\ fs []);

val pos_val_MOD_0 = prove(
  ``!x pos code2 p.
      backend_correct_alt mc_conf.f mc_conf.asm_config /\
      (~EVEN p ==> (mc_conf.asm_config.code_alignment = 1)) /\
      (pos MOD mc_conf.asm_config.code_alignment = 0) /\
      all_enc_ok mc_conf.asm_config mc_conf.f.encode labs p code2 ==>
      (pos_val x pos code2 MOD mc_conf.asm_config.code_alignment = 0)``,
  cheat)
(*
  REVERSE (Cases_on `backend_correct_alt mc_conf.f mc_conf.asm_config`)
  \\ asm_simp_tac pure_ss [] THEN1 fs []
  \\ `0 < mc_conf.asm_config.code_alignment` by ALL_TAC
  THEN1 (fs [backend_correct_alt_def,enc_ok_def] \\ DECIDE_TAC)
  \\ HO_MATCH_MP_TAC (theorem "pos_val_ind")
  \\ rpt strip_tac \\ fs [pos_val_def] \\ fs [all_enc_ok_def]

    rw [] \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ FIRST_X_ASSUM MATCH_MP_TAC


  THEN1 (FIRST_X_ASSUM MATCH_MP_TAC \\ METIS_TAC [])
  \\ Cases_on `x = 0` \\ fs []
  \\ Cases_on `is_Label y` \\ fs []
  \\ imp_res_tac (GSYM MOD_PLUS)
  \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ imp_res_tac line_length_MOD_0 \\ fs []
  \\ FIRST_X_ASSUM MATCH_MP_TAC \\ fs []
  \\ Q.EXISTS_TAC `p + line_length y` \\ fs [] \\ rpt strip_tac
  \\ Cases_on `EVEN p` \\ fs [EVEN_ADD]
  \\ `?n. mc_conf.asm_config.code_alignment = 2 ** n` by
        cheat (* move this requirement to enc_ok ? *)
  \\ Cases_on `n` \\ fs []
  \\ rfs [MOD_EQ_0_DIVISOR,EXP,EVEN_EXISTS] \\ rw []
  \\ fs [] \\ metis_tac [MULT_ASSOC,MULT_COMM])*)
  |> Q.SPECL [`x`,`0`,`y`,`0`] |> SIMP_RULE std_ss [];

val aEval_IMP_mEval = prove(
  ``!s1 res (mc_conf: ('a,'state,'b) machine_config) s2 code2 labs t1 ms1.
      (aEval s1 = (res,s2)) /\ (res <> Error Internal) /\
      backend_correct_alt mc_conf.f mc_conf.asm_config /\
      state_rel (mc_conf,code2,labs,p) s1 t1 ms1 ==>
      ?k t2 ms2.
        (mEval mc_conf s1.io_events (s1.clock + k) ms1 =
           (res,ms2,s2.io_events)) /\
        state_rel (mc_conf,code2,labs,p) s2 t2 ms2``,
  HO_MATCH_MP_TAC aEval_ind \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [aEval_def]
  \\ Cases_on `s1.clock = 0` \\ fs []
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ REPEAT STRIP_TAC
  THEN1 (Q.EXISTS_TAC `0` \\ fs [Once mEval_def] \\ metis_tac [])
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
      \\ `pos_val x 0 code2 = x'` by metis_tac [] \\ rw []
      \\ MATCH_MP_TAC pos_val_MOD_0 \\ fs []
      \\ `0 < mc_conf.asm_config.code_alignment` by
        (fs [backend_correct_alt_def,enc_ok_def] \\ decide_tac) \\ fs [])
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
      \\ RES_TAC \\ fs [] \\ rpt strip_tac \\ res_tac \\ rw []
      \\ MATCH_MP_TAC pos_val_MOD_0 \\ fs []
      \\ `0 < mc_conf.asm_config.code_alignment` by
        (fs [backend_correct_alt_def,enc_ok_def] \\ decide_tac) \\ fs [])
    \\ rpt strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `s1.clock - 1 + k`) \\ rw []
    \\ `s1.clock - 1 + k + l' = s1.clock + (k + l' - 1)` by DECIDE_TAC
    \\ Q.EXISTS_TAC `k + l' - 1` \\ fs []
    \\ Q.EXISTS_TAC `t2` \\ fs [state_rel_def,shift_interfer_def]
    \\ rpt strip_tac \\ res_tac)
  THEN1 (* Jump *) cheat
  THEN1 (* JumpCmp *) cheat
  THEN1 (* Call *) cheat
  THEN1 (* LocValue *) cheat
  THEN1 (* CallFFI *) cheat
  THEN1 (* Halt *)
   (rw [] \\ cheat));



(*

TODO:
 - fix compilation of FFI and Halt calls
 - define an incremental version of the compiler
 - add ability to install code



   ((* Asm (Inst ...) *)
    Cases_on `(asm_inst i s1).failed` \\ fs [] \\ REPEAT STRIP_TAC \\ fs []
    \\ `?t2. asm_step_alt mc_conf.f.encode
             mc_conf.asm_config t1 (Inst i) t2 /\
      (t2 = (asm (Inst i) (t1.pc + n2w (LENGTH (mc_conf.f.encode (Inst i)))) t1))` by
      (fs [] \\ MATCH_MP_TAC IMP_asm_step_alt \\ fs [])
    \\ `mc_conf.f.state_rel t1 ms1 /\
        (mc_conf.prog_addresses = t1.mem_domain) /\
        interference_ok mc_conf.next_interfer mc_conf.f.proj` by
      fs [state_rel_def]
    \\ IMP_RES_TAC asm_step_IMP_mEval_step

    \\ POP_ASSUM (STRIP_ASSUME_TAC o Q.SPEC `s1.io_events`)
    \\ Q.MATCH_ASSUM_RENAME_TAC `ll <> 0:num`
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`shift_interfer ll mc_conf`,
         `code2`,`labs`,`t2`,`ms2`])
    \\ MATCH_MP_TAC IMP_IMP \\ REPEAT STRIP_TAC
    THEN1 (fs [shift_interfer_def])
    THEN1 (fs [state_rel_def,shift_interfer_def]
      \\ fs [inc_pc_def,dec_clock_def,asmTheory.asm_def,asmTheory.upd_pc_def]
      \\ cheat)
    \\ `((inc_pc (dec_clock (asm_inst i s1))).io_events = s1.io_events) /\
        ((inc_pc (dec_clock (asm_inst i s1))).clock = s1.clock - 1)` by
      fs [inc_pc_def,dec_clock_def,asm_inst_consts] \\ fs []
    \\ FIRST_X_ASSUM (ASSUME_TAC o Q.SPEC `(s1.clock - 1 + k)`)
    \\ Q.EXISTS_TAC `k + ll - 1`
    \\ `s1.clock + (k + ll - 1) = s1.clock - 1 + k + ll` by DECIDE_TAC \\ fs []
    \\ Q.EXISTS_TAC `t2'` \\ fs [state_rel_def,shift_interfer_def])


*)




(* show that remove_labels only adds aEval-irrelevant annotations

fun add_rewrite th = (augment_srw_ss [rewrites [th]];th)

val merge_lines_def = Define `
  (merge_lines [] _ = []) /\
  (merge_lines (Label x _::xs1) (Label _ z::xs2) =
     Label x z :: merge_lines xs1 xs2) /\
  (merge_lines (Asm x _ _::xs1) (Asm _ bs l::xs2) =
     Asm x bs l :: merge_lines xs1 xs2) /\
  (merge_lines (LabAsm a _ _ _::xs1) (LabAsm _ w bs l::xs2) =
     LabAsm a w bs l :: merge_lines xs1 xs2) /\
  (merge_lines xs ys = xs)` |> add_rewrite

val merge_code_def = Define `
  (merge_code [] xs = []) /\
  (merge_code (Section k lines1 :: xs1) (Section _ lines2 :: xs2) =
     Section k (merge_lines lines1 lines2) :: merge_code xs1 xs2) /\
  (merge_code xs _ = xs)` |> add_rewrite

val asm_fetch_merge_code = prove(
  ``asm_fetch (s with code := merge_code code code2) = asm_fetch s``,
  cheat) |> add_rewrite

val inc_pc_with_code = prove(
  ``(inc_pc (s with code := d)) = (inc_pc s) with code := d``,
  cheat) |> add_rewrite

val upd_pc_with_code = prove(
  ``(upd_pc p (s with code := d)) = (upd_pc p s) with code := d``,
  cheat) |> add_rewrite

val dec_clock_with_code = prove(
  ``(dec_clock (s with code := d)) = (dec_clock s) with code := d``,
  cheat) |> add_rewrite

val asm_inst_with_code = prove(
  ``(asm_inst i (s with code := d)) = (asm_inst i s) with code := d``,
  cheat) |> add_rewrite

val read_reg_with_code = prove(
  ``read_reg n (s with code := c) = read_reg n s``,
  cheat) |> add_rewrite

val upd_reg_with_code = prove(
  ``upd_reg n w (s with code := c) = (upd_reg n w s) with code := c``,
  cheat) |> add_rewrite

val reg_imm_with_code = prove(
  ``reg_imm n (s with code := c) = reg_imm n s``,
  cheat) |> add_rewrite

val loc_to_pc_merge_code = prove(
  ``loc_to_pc n1 n2 (merge_code code code2) =
    loc_to_pc n1 n2 code``,
  cheat) |> add_rewrite

val get_pc_value_merge_code = prove(
  ``get_pc_value l (s with code := merge_code s.code code2) =
    get_pc_value l s``,
  cheat) |> add_rewrite

val get_ret_Loc_merge_code = prove(
  ``get_ret_Loc (t with code := merge_code t.code c) =
    get_ret_Loc t``,
  cheat) |> add_rewrite

val lab_to_loc_merge_code = prove(
  ``lab_to_loc l (t with code := merge_code t.code c) =
    lab_to_loc l t``,
  fs [lab_to_loc_def]) |> add_rewrite

val read_bytearray_with_code = prove(
  ``!n a s. read_bytearray a n (s with code := code2) = read_bytearray a n s``,
  Induct \\ fs [read_bytearray_def]) |> add_rewrite

val aEval_merge_code = prove(
  ``!s res t c enc.
      (aEval s = (res,t)) ==>
      (aEval (s with code := merge_code s.code code2) =
         (res, t with code := merge_code s.code code2)) /\
      (t.code = s.code)``,
  HO_MATCH_MP_TAC aEval_ind \\ NTAC 6 STRIP_TAC
  \\ ONCE_REWRITE_TAC [aEval_def] \\ fs [asm_fetch_merge_code]
  \\ Cases_on `asm_fetch s` \\ fs []
  \\ Cases_on `x` \\ fs []
  THEN1
   (Cases_on `a` \\ fs [LET_DEF,asm_inst_with_code,inc_pc_with_code]
    THEN1
     (BasicProvers.EVERY_CASE_TAC \\ fs []
      \\ REPEAT STRIP_TAC \\ RES_TAC
      \\ fs [inc_pc_def,asm_inst_consts])
    \\ fs [read_reg_def,loc_to_pc_merge_code]
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [dec_clock_with_code,upd_pc_with_code]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ fs [upd_pc_def,dec_clock_def])
  \\ Cases_on `a` \\ fs []
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [LET_DEF]
  \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ fs [upd_pc_def,inc_pc_def,dec_clock_def,upd_reg_def])

val merge_code_remove_labels = prove(
  ``(remove_labels c enc code = SOME code2) ==>
    (merge_code code code2 = code2)``,
  cheat) |> add_rewrite

val aEval_remove_labels = prove(
  ``(aEval s = (res,t)) /\ (remove_labels c enc s.code = SOME code2) ==>
    (aEval (s with code := code2) = (res,t with code := code2))``,
  REPEAT STRIP_TAC \\ IMP_RES_TAC merge_code_remove_labels
  \\ POP_ASSUM (fn th => ONCE_REWRITE_TAC [GSYM th])
  \\ IMP_RES_TAC aEval_merge_code \\ fs []);

*)

val _ = export_theory();
