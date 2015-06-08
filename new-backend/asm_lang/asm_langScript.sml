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

val flat_Section_def = Define `
  flat_Section (Section _ xs) = FILTER (\x. ~(is_Label x)) xs`;

val asm_fetch_def = Define `
  asm_fetch s =
    let code = FLAT (MAP flat_Section s.code) in
      if s.pc < LENGTH code then
        SOME (EL s.pc code)
      else
        NONE`;

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
    let a = if s.be then a + n2w n else a in
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
    let a = if s.be then a + n2w n else a in
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
  asm_code_length code = LENGTH (FLAT (MAP flat_Section code))`;

val asm_fetch_IMP = prove(
  ``(asm_fetch s = SOME x) ==>
    s.pc < asm_code_length s.code``,
  fs [asm_fetch_def,LET_DEF,asm_code_length_def]);

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
            ((SND (read_mem_list a n s)).clock = s.clock)``,
  Induct \\ fs [read_mem_list_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [assert_def]);

val write_mem_list_consts = prove(
  ``!n a s. (((write_mem_list a n s)).pc = s.pc) /\
            (((write_mem_list a n s)).code = s.code) /\
            (((write_mem_list a n s)).clock = s.clock)``,
  Induct \\ fs [write_mem_list_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ fs [assert_def,upd_mem_def]);

val asm_inst_consts = prove(
  ``((asm_inst i s).pc = s.pc) /\
    ((asm_inst i s).code = s.code) /\
    ((asm_inst i s).clock = s.clock)``,
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
    case asm_fetch s of
    | SOME (Asm a _ _) =>
        (case a of
         | Inst i =>
            (let s1 = asm_inst i s in
               if s1.failed then (Error Internal,s)
               else aEval (inc_pc s1))
         | JumpReg r =>
            (case read_reg r s of
             | Loc n1 n2 =>
                 (case loc_to_pc n1 n2 s.code of
                  | NONE => (Error Internal,s)
                  | SOME p =>
                      if s.clock = 0 then (TimeOut,s)
                      else aEval (upd_pc p (dec_clock s)))
             | _ => (Error Internal,s))
         | _ => (Error Internal,s))
    | SOME (LabAsm Halt _ _ _) => (Result,s)
    | SOME (LabAsm (LocValue r lab) _ _ _) =>
        let s1 = upd_reg r (lab_to_loc lab) s in
          aEval (inc_pc s1)
    | SOME (LabAsm (Jump l) _ _ _) =>
       (case get_pc_value l s of
        | NONE => (Error Internal,s)
        | SOME p => if s.clock = 0 then (TimeOut,s)
                    else aEval (upd_pc p (dec_clock s)))
    | SOME (LabAsm (JumpCmp c r ri l) _ _ _) =>
       (case word_cmp c (read_reg r s) (reg_imm ri s) of
        | NONE => (Error Internal,s)
        | SOME F => aEval (inc_pc s)
        | SOME T =>
         (case get_pc_value l s of
          | NONE => (Error Internal,s)
          | SOME p => if s.clock = 0 then (TimeOut,s)
                      else aEval (upd_pc p (dec_clock s))))
    | SOME (LabAsm (Call l) _ _ _) =>
       (case get_pc_value l s of
        | NONE => (Error Internal,s)
        | SOME p =>
         (case get_ret_Loc s of
          | NONE => (Error Internal,s)
          | SOME k =>
             let s1 = upd_reg s.link_reg k s in
               if s.clock = 0 then (TimeOut,s)
               else aEval (upd_pc p (dec_clock s1))))
    | SOME (LabAsm (CallFFI ffi_index) _ _ _) =>
       (case (s.regs s.len_reg,s.regs s.ptr_reg) of
        | (Word w, Word w2) =>
         (case read_bytearray w2 (w2n w) s of
          | NONE => (Error Internal,s)
          | SOME bytes =>
           (case call_FFI ffi_index bytes s.io_events of
            | NONE => (Error IO_mismatch,s)
            | SOME (new_bytes,new_io) =>
                aEval (s with <| io_events := new_io ;
                                 mem := write_bytearray w2 new_bytes s.mem ;
                                 pc := s.pc + 1 |>)))
        | _ => (Error Internal,s))
    | _ => (Error Internal,s)`
 (WF_REL_TAC `(inv_image (measure I LEX
                          measure (\s. asm_code_length s.code - s.pc))
                 (\s. (s.clock,s)))`
  \\ fs [inc_pc_def] \\ rw [] \\ IMP_RES_TAC asm_fetch_IMP
  \\ fs [asm_inst_consts,upd_reg_def,upd_pc_def,dec_clock_def] \\ DECIDE_TAC)

val aEval_ind = fetch "-" "aEval_ind"


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

val sec_bytes_def = Define `
  (sec_bytes [] nop aux = aux) /\
  (sec_bytes ((Label _ _ l)::xs) nop aux =
     sec_bytes xs nop (if l < 1 then aux else nop::aux)) /\
  (sec_bytes ((Asm x1 x2 l)::xs) nop aux =
     sec_bytes xs nop (REVERSE x2 ++ aux)) /\
  (sec_bytes ((LabAsm a w bytes l)::xs) nop aux =
     sec_bytes xs nop (REVERSE bytes ++ aux))`

val all_sec_bytes_def = Define `
  (all_sec_bytes [] nop aux = REVERSE aux) /\
  (all_sec_bytes ((Section s lines)::rest) nop aux =
     let k = sec_length lines 0 in
     let aux1 = sec_bytes lines nop aux in
       all_sec_bytes rest nop (if ODD k then nop :: aux else aux))`

val prog_to_bytes_def = Define `
  prog_to_bytes enc sec_list =
    let nop = (case enc (Inst Skip) of [] => 0w | (x::xs) => x) in
      all_sec_bytes sec_list nop []`

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
      interference_ok c.next_interfer c.f.proj /\
      (!s ms. c.f.state_rel s ms ==> c.f.state_ok ms) /\
      (!ms1 ms2. (c.f.proj ms1 = c.f.proj ms2) ==>
                 (c.f.state_ok ms1 = c.f.state_ok ms2)) /\
      (!env.
         interference_ok env c.f.proj ==>
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
    \\ fs [interference_ok_def] \\ RES_TAC
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
    \\ cheat)
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
  ``!xs a. bytes_in_memory a xs c m d ==> all_pcs a xs SUBSET d``,
  Induct \\ fs [all_pcs_def,bytes_in_memory_def]);

val asserts_WEAKEN = prove(
  ``!n next s P Q.
      (!x. P x ==> P' x) ==>
      asserts n next s P Q ==>
      asserts n next s P' Q``,
  Induct \\ fs [asserts_def,LET_DEF] \\ REPEAT STRIP_TAC \\ RES_TAC);




val asm_step_IMP_mEval_step = prove(
  ``backend_correct_alt c.f c.asm_config /\
    (c.prog_addresses = s1.mem_domain) /\
    interference_ok c.next_interfer c.f.proj /\
    asm_step_alt c.f.encode c.asm_config s1 i s2 /\
    c.f.state_rel (s1:'a asm_state) (ms1:'state) ==>
    ?l ms2. (mEval c io (k + l) ms1 = mEval c io k ms2) /\
            c.f.state_rel s2 ms2 /\ l <> 0``,
  fs [backend_correct_alt_def] \\ REPEAT STRIP_TAC \\ RES_TAC
  \\ fs [] \\ NTAC 2 (POP_ASSUM (K ALL_TAC))
  \\ Q.EXISTS_TAC `n+1` \\ fs []
  \\ MATCH_MP_TAC mEval_EQ_mEval_lemma \\ fs []
  \\ REPEAT STRIP_TAC \\ TRY (RES_TAC \\ NO_TAC)
  THEN1 (fs [asm_step_alt_def] \\ IMP_RES_TAC enc_ok_not_empty
         \\ Cases_on `c.f.encode i` \\ fs [bytes_in_memory_def])
  \\ fs [LET_DEF] \\ Q.PAT_ASSUM `!k. bb` (K ALL_TAC)
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`env`]) \\ fs []
  \\ MATCH_MP_TAC asserts_WEAKEN \\ fs []
  \\ SRW_TAC [] [] \\ fs []
  \\ POP_ASSUM MP_TAC \\ MATCH_MP_TAC SUBSET_IMP
  \\ fs [asm_step_alt_def] \\ IMP_RES_TAC bytes_in_memory_IMP_SUBSET);


(* compiler correctness proof *)

val sec_enc_ok_def = Define `
  (sec_enc_ok c enc labs pos [] <=> T) /\
  (sec_enc_ok c enc labs pos ((Label _ _ l)::xs) <=>
     (if EVEN pos then (l = 0) else (l = 1)) /\
     sec_enc_ok c enc labs (pos+l) xs) /\
  (sec_enc_ok c enc labs pos ((Asm b bytes l)::xs) <=>
     (bytes = enc b) /\ (LENGTH bytes = l) /\ asm_ok b c /\
     sec_enc_ok c enc labs (pos+l) xs) /\
  (sec_enc_ok c enc labs pos ((LabAsm a w bytes l)::xs) <=>
     let pos = pos + l in
     let target = find_pos (get_label a) labs in
     let w1 = n2w target - n2w pos in
     let bs = enc (lab_inst w1 a) in
       (bytes = bs) /\ (LENGTH bytes = l) /\ asm_ok (lab_inst w1 a) c /\
       sec_enc_ok c enc labs (pos+l) xs)`

val all_enc_ok_def = Define `
  (all_enc_ok c enc labs pos [] = T) /\
  (all_enc_ok c enc labs pos ((Section s lines)::rest) <=>
     sec_enc_ok c enc labs pos lines /\
     all_enc_ok c enc labs (pos + sec_length lines 0) rest)`

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
     case lookup k1 labs of
     | NONE => NONE
     | SOME f => case lookup k2 f of
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

val line_length_def = Define `
  (line_length (Label k1 k2 l) = l) /\
  (line_length (Asm b bytes l) = l) /\
  (line_length (LabAsm a w bytes l) = l)`

val pos_val_def = Define `
  (pos_val pos [] = 0) /\
  (pos_val pos ((Section k [])::xs) = pos_val pos xs) /\
  (pos_val pos ((Section k (y::ys))::xs) =
     if pos = 0:num then 0
     else if is_Label y
          then pos_val pos ((Section k ys)::xs) + line_length y
          else pos_val (pos-1) ((Section k ys)::xs) + line_length y)`

val state_rel_def = Define `
  state_rel (asm_conf, mc_conf, enc, code2, labs, p) (s1:'a asml_state) ms1 <=>
    (!r. word_loc_val p labs (s1.regs r) = SOME (ms1.regs r)) /\
    (!a. a IN s1.mem_domain ==>
         a IN ms1.mem_domain /\
         (word8_loc_val p labs (s1.mem a) = SOME (ms1.mem a))) /\
    bytes_in_mem p (prog_to_bytes enc code2) ms1.mem ms1.mem_domain s1.mem_domain /\
    ~s1.failed /\ ~ms1.failed /\ (s1.be = ms1.be) /\
    (ms1.pc = p + n2w (pos_val s1.pc code2)) /\
    (p && n2w (ms1.align - 1) = 0w) /\
    all_enc_ok asm_conf enc labs 0 code2 /\
    code_similar s1.code code2`


(*

val aEval_IMP_mEval = prove(
  ``!s1 res s2 code2 labs ms1.
      (aEval s1 = (res,s2)) /\ (res <> Error Internal) /\
      state_rel (asm_conf,mc_conf,enc,code2,labs,p) s1 ms1 ==>
      ?k ms2.
        (mEval mc_conf s1.io_events (s1.clock + k) ms1 =
           (res,ms2,s2.io_events)) /\
        (s2.code = s1.code) /\
        state_rel (asm_conf,mc_conf,enc,code2,labs,p) s2 ms2``,

  HO_MATCH_MP_TAC aEval_ind \\ NTAC 2 STRIP_TAC
  \\ ONCE_REWRITE_TAC [aEval_def]
  \\ Cases_on `asm_fetch s1` \\ fs []
  \\ Cases_on `x` \\ fs [] \\ Cases_on `a` \\ fs []
  \\ REPEAT (Q.PAT_ASSUM `T` (K ALL_TAC)) \\ fs [LET_DEF]

    (* Asm (Inst ...) *)
    Cases_on `(asm_inst i s1).failed` \\ fs [] \\ REPEAT STRIP_TAC \\ fs []

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
