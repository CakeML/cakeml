open preamble labLangTheory lab_filterTheory;

val _ = new_theory"lab_to_target";

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

(* pad with nop byte, and nop instruction *)

val pad_bytes_def = Define `
  pad_bytes bytes len nop =
    let len_bytes = LENGTH bytes in
      if len <= len_bytes then bytes else
        TAKE len (bytes ++ FLAT (REPLICATE len nop))`

val pad_section_def = Define `
  (pad_section nop n [] aux = REVERSE aux) /\
  (pad_section nop n ((Label l1 l2 len)::xs) aux =
     pad_section nop (n+len) xs ((Label l1 l2 0)::aux)) /\
  (pad_section nop n ((Asm x bytes len)::xs) aux =
     let len = len + n in
       pad_section nop 0 xs (Asm x (pad_bytes bytes len nop) len::aux)) /\
  (pad_section nop n ((LabAsm y w bytes len)::xs) aux =
     let len = len + n in
       pad_section nop 0 xs (LabAsm y w (pad_bytes bytes len nop) len::aux))`

val pad_code_def = Define `
  (pad_code nop [] = []) /\
  (pad_code nop ((Section n xs)::ys) =
     let k = if EVEN (sec_length xs 0) then 0 else 1 in
       Section n (pad_section nop k (REVERSE xs) []) :: pad_code nop ys)`

(* top-level assembler function *)

val remove_labels_loop_def = Define `
  remove_labels_loop clock c enc sec_list =
    (* compute labels *)
    let labs = compute_labels 0 sec_list in
    (* update jump encodings *)
    let xs = enc_secs_again 0 labs enc sec_list in
    (* check length annotations *)
    if all_lengths_ok 0 xs then
      if all_asm_ok c xs then SOME (pad_code (enc (Inst Skip)) xs) else NONE
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
  (line_bytes (Label _ _ l) = []) /\
  (line_bytes (Asm _ bytes _) = bytes) /\
  (line_bytes (LabAsm _ _ bytes _) = bytes)`

val prog_to_bytes_def = Define `
  (prog_to_bytes [] = []) /\
  (prog_to_bytes ((Section k [])::xs) = prog_to_bytes xs) /\
  (prog_to_bytes ((Section k (y::ys))::xs) =
     line_bytes y ++ prog_to_bytes ((Section k ys)::xs))`

(* compile labels *)

val compile_lab_def = Define `
  compile_lab c enc sec_list =
    case remove_labels c enc sec_list of
    | SOME sec_list => SOME (prog_to_bytes sec_list)
    | NONE => NONE`;

(* compile labLang *)

val compile_def = Define `
  compile c enc sec_list =
    compile_lab c enc (filter_skip sec_list)`;

val _ = export_theory();
