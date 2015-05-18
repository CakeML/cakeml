open HolKernel Parse boolLib bossLib;
open asmTheory wordsTheory wordsLib sptreeTheory ffiTheory;
open target_semTheory word_locTheory;

val _ = new_theory "asm_lang";


(* -- SYNTAX -- *)

val () = Parse.temp_type_abbrev ("reg", ``:num``)

(* A label refers to either a section name or a local label definition
   within the current section. *)

val () = Datatype `
  lab = Local num | Sec num`

(* Each line of a section consists of either a label, an assembly
   instruction (without a label) or some labelled asm instruction. *)

val () = Datatype `
  asm_with_lab = Jump lab
               | JumpCmp cmp reg ('a reg_imm) lab
               | Call lab
               | LocValue reg lab
               | CallFFI num
               | Halt`;

val () = Datatype `
  asm_line = Label num num
           | Asm ('a inst) (word8 list) num
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
     ; lr         : reg
     ; align      : num
     ; be         : bool
     ; io_events  : io_trace
     ; code       : 'a asm_prog
     ; clock      : num
     ; failed     : bool
     |>`

val is_Label_def = Define `
  (is_Label (Label _ _) = T) /\
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
  (word_cmp Equal w1 w2 = (w1 = w2)) /\
  (word_cmp Less w1 w2  = (w1 < w2)) /\
  (word_cmp Lower w1 w2 = (w1 <+ w2)) /\
  (word_cmp Test w1 w2  = (w1 && w2 = 0w))`

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
     | Word w1 => upd_reg r1 (Word (word_shift l w1 n)) s)`

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

val asm_eval_def = tDefine "asm_eval" `
  asm_eval s =
    case asm_fetch s of
    | SOME (Asm i _ _) =>
        (let s1 = asm_inst i s in
           if s1.failed then (Error Internal,s) else
             asm_eval s1)
    | SOME (LabAsm al _ _ _) => ARB
    | _ => (Error Internal,s)` cheat


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
  (enc_line enc (Label n1 n2) = Label n1 n2) /\
  (enc_line enc (Asm a _ _) =
     let bs = enc (Inst a) in Asm a bs (LENGTH bs)) /\
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
  (asm_line_labs pos ((Label k l)::xs) acc =
     asm_line_labs (pos+l) xs (insert (k+1) (pos+l) acc)) /\
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
  (find_pos s (Local k) labs =
     (lookup_any (k+1) (lookup_any s labs LN) 0):num) /\
  (find_pos s (Sec i) labs =
     lookup_any 0 (lookup_any i labs LN) 0)`;

val enc_line_again_def = Define `
  (enc_line_again s labs pos enc [] = []) /\
  (enc_line_again s labs pos enc ((Label k l)::xs) =
     (Label k l) :: enc_line_again s labs (pos+l) enc xs) /\
  (enc_line_again s labs pos enc ((Asm x1 x2 l)::xs) =
     (Asm x1 x2 l) :: enc_line_again s labs (pos+l) enc xs) /\
  (enc_line_again s labs pos enc ((LabAsm a w bytes l)::xs) =
     let pos = pos + l in
     let target = find_pos s (get_label a) labs in
     let w1 = n2w target - n2w pos in
       if w = w1 then
         (LabAsm a w bytes l)::enc_line_again s labs pos enc xs
       else
         let bs = enc (lab_inst w1 a) in
           LabAsm a 0w bs (LENGTH bs)::enc_line_again s labs pos enc xs)`

val sec_length_def = Define `
  (sec_length [] k = k) /\
  (sec_length ((Label _ l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((Asm x1 x2 l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((LabAsm a w bytes l)::xs) k = sec_length xs (k+l))`

val full_sec_length_def = Define `
  full_sec_length xs =
    let k = sec_length xs 0 in
      if ODD k then k+1 else k`;

val enc_secs_again_def = Define `
  (enc_secs_again pos labs enc [] = []) /\
  (enc_secs_again pos labs enc ((Section s lines)::rest) =
     let lines1 = enc_line_again s labs pos enc lines in
     let pos1 = pos + full_sec_length lines1 in
       (Section s lines1)::enc_secs_again pos1 labs enc rest)`

(* check/update length annotations *)

val sec_lengths_ok_def = Define `
  (sec_lengths_ok pos [] <=> T) /\
  (sec_lengths_ok pos ((Label _ l)::xs) <=>
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
  (sec_lengths_update pos ((Label n l)::xs) =
     let l = if EVEN pos then 0 else 1 in
       (Label n l) :: sec_lengths_update (pos+l) xs) /\
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
  (sec_asm_ok c ((Label _ l)::xs) <=> sec_asm_ok c xs) /\
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
    if clock = 0 then NONE else
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
  (sec_bytes ((Label _ l)::xs) nop aux =
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

(* compile asm_lang *)

val aComp_def = Define `
  aComp enc sec_list =
    let nop = (case enc (Inst Skip) of [] => 0w | (x::xs) => x) in
      all_sec_bytes sec_list nop []`;

val _ = export_theory();
