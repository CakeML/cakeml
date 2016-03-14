open preamble labLangTheory lab_filterTheory;

val _ = new_theory"lab_to_target";

val ffi_offset_def = Define `
  ffi_offset = 8:num`;

(* length of a section *)

val sec_length_def = Define `
  (sec_length [] k = k) /\
  (sec_length ((Label _ _ l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((Asm x1 x2 l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((LabAsm a w bytes l)::xs) k = sec_length xs (k+l))`

val full_sec_length_def = Define `
  full_sec_length xs =
    let k = sec_length xs 0 in
      if ODD k then k+1 else k`;

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
  (enc_line enc skip_len (Label n1 n2 n3) = Label n1 n2 skip_len) /\
  (enc_line enc skip_len (Asm a _ _) =
     let bs = enc a in Asm a bs (LENGTH bs)) /\
  (enc_line enc skip_len (LabAsm l _ _ _) =
     let bs = enc (lab_inst 0w l) in
       LabAsm l 0w bs (LENGTH bs))`

val enc_sec_def = Define `
  enc_sec enc skip_len (Section k xs) =
    Section k (MAP (enc_line enc skip_len) xs)`;

val enc_sec_list_def = Define `
  enc_sec_list enc xs =
    let skip_len = LENGTH (enc (Inst Skip)) in
      MAP (enc_sec enc skip_len) xs`;

(* compute labels *)

val asm_line_labs_def = Define `
  (asm_line_labs pos [] acc = (acc,pos)) /\
  (asm_line_labs pos ((Label k1 k2 l)::xs) acc =
     asm_line_labs (pos+l) xs (union acc (insert k2 (pos+l) LN))) /\
  (asm_line_labs pos ((Asm _ _ l)::xs) acc =
     asm_line_labs (pos+l) xs acc) /\
  (asm_line_labs pos ((LabAsm _ _ _ l)::xs) acc =
     asm_line_labs (pos+l) xs acc)`

val sec_labs_def = Define `
  sec_labs pos lines =
    asm_line_labs pos lines (insert 0 pos LN)`;

val compute_labels_def = Define `
  (compute_labels pos [] aux = aux) /\
  (compute_labels pos ((Section k lines)::rest) aux =
     let (labs,new_pos) = sec_labs pos lines in
     let new_pos = pos + full_sec_length lines in
       compute_labels new_pos rest (union aux (insert k labs LN)))`

(* update code, but not label lengths *)

val find_pos_def = Define `
  find_pos (Lab k1 k2) labs =
    (lookup_any k2 (lookup_any k1 labs LN) 0):num`;

val get_label_def = Define `
  (get_label (Jump l) = l) /\
  (get_label (JumpCmp c r ri l) = l) /\
  (get_label (Call l) = l) /\
  (get_label (LocValue r l) = l) /\
  (* cannot happen *)
  (get_label _ = Lab 0 0)`;

val get_jump_offset_def = Define `
  (get_jump_offset (CallFFI i) labs pos =
     0w - n2w (pos + (3 + i) * ffi_offset)) /\
  (get_jump_offset ClearCache labs pos =
     0w - n2w (pos + 2 * ffi_offset)) /\
  (get_jump_offset Halt labs pos =
     0w - n2w (pos + ffi_offset)) /\
  (get_jump_offset a labs pos =
     n2w (find_pos (get_label a) labs) - n2w pos)`

val enc_lines_again_def = Define `
  (enc_lines_again labs pos enc [] (acc,ok) = (REVERSE acc,ok:bool)) /\
  (enc_lines_again labs pos enc ((Label k1 k2 l)::xs) (acc,ok) =
     enc_lines_again labs (pos+l) enc xs ((Label k1 k2 l)::acc,ok)) /\
  (enc_lines_again labs pos enc ((Asm x1 x2 l)::xs) (acc,ok) =
     enc_lines_again labs (pos+l) enc xs ((Asm x1 x2 l) :: acc,ok)) /\
  (enc_lines_again labs pos enc ((LabAsm a w bytes l)::xs) (acc,ok) =
     let w1 = get_jump_offset a labs pos in
       if w = w1 then
         enc_lines_again labs (pos + l) enc xs ((LabAsm a w bytes l)::acc,ok)
       else
         let bs = enc (lab_inst w1 a) in
         let l1 = MAX (LENGTH bs) l in
           enc_lines_again labs (pos + l1) enc xs
             ((LabAsm a w1 bs l1)::acc, ok /\ (l1 = l)))`

val enc_secs_again_def = Define `
  (enc_secs_again pos labs enc [] = ([],T)) /\
  (enc_secs_again pos labs enc ((Section s lines)::rest) =
     let (lines1,ok) = enc_lines_again labs pos enc lines ([],T) in
     let pos1 = pos + full_sec_length lines1 in
     let (rest1,ok1) = enc_secs_again pos1 labs enc rest in
       ((Section s lines1)::rest1,ok /\ ok1))`

(* update labels *)

val lines_upd_lab_len_def = Define `
  (lines_upd_lab_len pos [] acc = REVERSE acc) /\
  (lines_upd_lab_len pos ((Label k1 k2 l)::xs) acc =
     let l1 = if EVEN pos then 0 else 1 in
       lines_upd_lab_len (pos+l1) xs ((Label k1 k2 l1::acc))) /\
  (lines_upd_lab_len pos ((Asm x1 x2 l)::xs) acc =
     lines_upd_lab_len (pos+l) xs ((Asm x1 x2 l) :: acc)) /\
  (lines_upd_lab_len pos ((LabAsm a w bytes l)::xs) acc =
     lines_upd_lab_len (pos+l) xs ((LabAsm a w bytes l) :: acc))`

val upd_lab_len_def = Define `
  (upd_lab_len pos [] = []) /\
  (upd_lab_len pos ((Section s lines)::rest) =
     let lines1 = lines_upd_lab_len pos lines [] in
     let pos1 = pos + full_sec_length lines1 in
     let rest1 = upd_lab_len pos1 rest in
       (Section s lines1)::rest1)`

(* checking that all labelled asm instructions are asm_ok *)

(*

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

*)

val enc_with_nop_def = Define `
  enc_with_nop enc (b:'a asm) bytes =
    let init = enc b in
    let step = enc (asm$Inst Skip) in
      if LENGTH step = 0 then bytes = init else
        let n = (LENGTH bytes - LENGTH init) DIV LENGTH step in
          bytes = init ++ FLAT (REPLICATE n step)`

val lab_lookup_def = Define `
  lab_lookup k1 k2 labs =
    case lookup k1 labs of
    | NONE => NONE
    | SOME f => lookup k2 f`

val line_length_def = Define `
  (line_length (Label k1 k2 l) = if l = 0 then 0 else 1) /\
  (line_length (Asm b bytes l) = LENGTH bytes) /\
  (line_length (LabAsm a w bytes l) = LENGTH bytes)`

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

(* pad with nop byte, and nop instruction *)

val pad_bytes_def = Define `
  pad_bytes bytes len nop =
    let len_bytes = LENGTH bytes in
      if len <= len_bytes then bytes else
        TAKE len (bytes ++ FLAT (REPLICATE len nop))`

val add_nop_def = Define `
  (add_nop nop [] = []) /\
  (add_nop nop ((Label l1 l2 len)::xs) =
    (Label l1 l2 len)::add_nop nop xs) /\
  (add_nop nop ((Asm x bytes len)::xs) =
    Asm x (bytes ++ [nop]) (len+1) :: xs) /\
  (add_nop nop ((LabAsm y w bytes len)::xs) =
    LabAsm y w (bytes ++ [nop]) (len+1) :: xs)`;

val append_nop_def = Define `
  append_nop nop xs = REVERSE (add_nop nop (REVERSE xs))`

val pad_section_def = Define `
  (pad_section nop n [] aux = REVERSE aux) /\
  (pad_section nop n ((Label l1 l2 len)::xs) aux =
     pad_section nop (n+len) xs ((Label l1 l2 0)::
     if len = 0 then aux else add_nop (HD nop) aux)) /\
  (pad_section nop n ((Asm x bytes len)::xs) aux =
     pad_section nop 0 xs (Asm x (pad_bytes bytes len nop) (len+n)::aux)) /\
  (pad_section nop n ((LabAsm y w bytes len)::xs) aux =
     pad_section nop 0 xs (LabAsm y w (pad_bytes bytes len nop) (len+n)::aux))`

val pad_code_def = Define `
  (pad_code nop [] = []) /\
  (pad_code nop ((Section n xs)::ys) =
     let f = if EVEN (sec_length xs 0) then I else append_nop (HD nop) in
       Section n (f (pad_section nop 0 xs [])) :: pad_code nop ys)`

(* top-level assembler function *)

val remove_labels_loop_def = Define `
  remove_labels_loop clock c enc sec_list =
    (* compute labels *)
    let labs = compute_labels 0 sec_list LN in
    (* update encodings and lengths (but not label lengths) *)
    let (sec_list,done) = enc_secs_again 0 labs enc sec_list in
      (* done ==> labs are still fine *)
      if done then
        (* adjust label lengths *)
        let sec_list = upd_lab_len 0 sec_list in
        (* compute labels a last time *)
        let labs = compute_labels 0 sec_list LN in
        (* update encodings *)
        let (sec_list,done) = enc_secs_again 0 labs enc sec_list in
        (* move label padding into instructions *)
        let sec_list = pad_code (enc (Inst Skip)) sec_list in
        (* it ought to be impossible for done to be false here *)
          if done /\ all_enc_ok c enc labs 0 sec_list then
            SOME (sec_list,labs)
          else NONE
      else
        (* repeat *)
        if clock = 0:num then NONE else
          remove_labels_loop (clock-1) c enc sec_list`

val remove_labels_def = Define `
  remove_labels init_clock c enc sec_list =
    (* Here init_clock puts an upper limit on the number of times the
       lengths can be adjusted. In many cases, clock = 0 should be
       enough. If this were to hit the clock limit for large values of
       init_clock, then something is badly wrong. Worth testing with
       the clock limit set to low values to see how many iterations
       are used. *)
    remove_labels_loop init_clock c enc (enc_sec_list enc sec_list)`;

(* code extraction *)

val line_bytes_def = Define `
  (line_bytes (Label _ _ _) = []) /\
  (line_bytes (Asm _ bytes _) = bytes) /\
  (line_bytes (LabAsm _ _ bytes _) = bytes)`

val prog_to_bytes_def = Define `
  (prog_to_bytes [] = []) /\
  (prog_to_bytes ((Section k [])::xs) = prog_to_bytes xs) /\
  (prog_to_bytes ((Section k (y::ys))::xs) =
     line_bytes y ++ prog_to_bytes ((Section k ys)::xs))`

(* compile labels *)

val _ = Datatype`
  config = <| encoder : 'a asm -> word8 list
            ; labels : num num_map num_map
            ; asm_conf : 'a asm_config
            ; init_clock : num
            |>`;

val find_ffi_index_limit_def = Define `
  (find_ffi_index_limit [] = 0) /\
  (find_ffi_index_limit (Section k []::rest) =
     find_ffi_index_limit rest) /\
  (find_ffi_index_limit (Section k (x::xs)::rest) =
     MAX (find_ffi_index_limit (Section k xs::rest))
         (case x of LabAsm (CallFFI i) _ _ _ => i+1 | _ => 0n))`

val compile_lab_def = Define `
  compile_lab c sec_list =
    let limit = find_ffi_index_limit sec_list in
      case remove_labels c.init_clock c.asm_conf c.encoder sec_list of
      | SOME (sec_list,l1) => SOME (prog_to_bytes sec_list,limit)
      | NONE => NONE`;

(* compile labLang *)

val compile_def = Define `
  compile lc sec_list = compile_lab lc (filter_skip sec_list)`;

(*

TODO:
 - Ensure that stack_to_lab makes every section end in a label.
   This would remove the need for append_nop and full_sec_length.

*)

val _ = export_theory();
