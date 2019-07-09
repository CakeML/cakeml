(*
  This compiler phase generates concrete (ARM, x64, ag32, RISC-V,
  MIPS) machine code from labLang assmebly programs. This phase is the
  CakeML compiler's assmebler: it computes label offsets and encodes
  all instructions according to the instruction encoder stored in the
  compiler configuration.
*)
open preamble labLangTheory lab_filterTheory;

val _ = new_theory"lab_to_target";

(* Number of bytes per FFI *)
val ffi_offset_def = Define `
  ffi_offset = 16:num`;

(* basic assemble function *)

val lab_inst_def = Define `
  (lab_inst w (Jump _) = Jump w) /\
  (lab_inst w (JumpCmp c r ri _) = JumpCmp c r ri w) /\
  (lab_inst w (Call _) = Call w) /\
  (lab_inst w (LocValue r _) = Loc r (w:'a word)) /\
  (lab_inst w (Halt) = Jump w) /\
  (lab_inst w (Install) = Jump w) /\
  (lab_inst w (CallFFI n) = Jump w)`;

val cbw_to_asm_def = Define`
  cbw_to_asm a =
  case a of
    Asmi a => a
  | Cbw r1 r2 => Inst (Mem Store8 r2 (Addr r1 0w))`

val _ = export_rewrites ["cbw_to_asm_def"]

val enc_line_def = Define `
  (enc_line enc skip_len (Label n1 n2 n3) = Label n1 n2 skip_len) /\
  (enc_line enc skip_len (Asm a _ _) =
     let bs = enc (cbw_to_asm a) in Asm a bs (LENGTH bs)) /\
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

val section_labels_def = Define `
  (section_labels pos [] labs = (pos,labs)) /\
  (section_labels pos (Label _ l2 len :: xs) labs =
     (*Ignore 0 labels*)
     if l2 = 0 then
       section_labels (pos+len) xs labs
     else
       section_labels (pos+len) xs ((l2,pos+len)::labs)) /\
  (section_labels pos (Asm _ _ len :: xs) labs =
     section_labels (pos+len) xs labs) /\
  (section_labels pos (LabAsm _ _ _ len :: xs) labs =
     section_labels (pos+len) xs labs)`

val compute_labels_alt_def = Define `
  (compute_labels_alt pos [] labs = labs) /\
  (compute_labels_alt pos (Section k lines::rest) labs =
    let (new_pos,sec_labs) = section_labels pos lines [] in
    compute_labels_alt new_pos rest
      (insert k (fromAList ((0,pos)::sec_labs)) labs))`

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

(* It should never happen that get_ffi_index returns the default 0 ---
   nonetheless, having a default prevents the translator from generating
   painful side conditions.
 *)
val get_ffi_index_def = Define `
  get_ffi_index ffis s =
    the 0 (find_index s ffis 0)`

val get_jump_offset_def = Define `
  (get_jump_offset (CallFFI s) ffis labs pos =
     0w - n2w (pos + (3 + get_ffi_index ffis s) * ffi_offset)) /\
  (get_jump_offset Install ffis labs pos =
     0w - n2w (pos + 2 * ffi_offset)) /\
  (get_jump_offset Halt ffis labs pos =
     0w - n2w (pos + ffi_offset)) /\
  (get_jump_offset a ffis labs pos =
     n2w (find_pos (get_label a) labs) - n2w pos)`

val enc_lines_again_def = Define `
  (enc_lines_again labs ffis pos enc [] (acc,ok) = (REVERSE acc,pos,ok:bool)) /\
  (enc_lines_again labs ffis pos enc ((Label k1 k2 l)::xs) (acc,ok) =
     enc_lines_again labs ffis (pos+l) enc xs ((Label k1 k2 l)::acc,ok)) /\
  (enc_lines_again labs ffis pos enc ((Asm x1 x2 l)::xs) (acc,ok) =
     enc_lines_again labs ffis (pos+l) enc xs ((Asm x1 x2 l) :: acc,ok)) /\
  (enc_lines_again labs ffis pos enc ((LabAsm a w bytes l)::xs) (acc,ok) =
     let w1 = get_jump_offset a ffis labs pos in
       if w = w1 then
         enc_lines_again labs ffis (pos + l) enc xs ((LabAsm a w bytes l)::acc,ok)
       else
         let bs = enc (lab_inst w1 a) in
         let l1 = MAX (LENGTH bs) l in
           enc_lines_again labs ffis (pos + l1) enc xs
             ((LabAsm a w1 bs l1)::acc, ok /\ (l1 = l)))`

val enc_secs_again_def = Define `
  (enc_secs_again pos labs ffis enc [] = ([],T)) /\
  (enc_secs_again pos labs ffis enc ((Section s lines)::rest) =
     let (lines1,pos1,ok) = enc_lines_again labs ffis pos enc lines ([],T) in
     let (rest1,ok1) = enc_secs_again pos1 labs ffis enc rest in
       ((Section s lines1)::rest1,ok /\ ok1))`

(* update labels *)

val lines_upd_lab_len_def = Define `
  (lines_upd_lab_len pos [] acc = (REVERSE acc,pos)) /\
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
     let (lines1,pos1) = lines_upd_lab_len pos lines [] in
     let rest1 = upd_lab_len pos1 rest in
       (Section s lines1)::rest1)`

(* checking that all labelled asm instructions are asm_ok *)

val line_ok_light_def = Define `
  (line_ok_light (c:'a asm_config) (Label _ _ l) <=> T) /\
  (line_ok_light c (Asm b bytes l) <=> T) /\
  (line_ok_light c (LabAsm Halt w bytes l) <=>
     asm_ok (Jump w) c) /\
  (line_ok_light c (LabAsm Install w bytes l) <=>
     asm_ok (Jump w) c) /\
  (line_ok_light c (LabAsm (CallFFI index) w bytes l) <=>
     asm_ok (Jump w) c) /\
  (line_ok_light c (LabAsm (Call v24) w bytes l) <=>
     F (* Call not yet supported *)) /\
  (line_ok_light c (LabAsm a w bytes l) <=>
     asm_ok (lab_inst w a) c)`

val sec_ok_light_def = Define`
  sec_ok_light c (Section k ls) ⇔
    EVERY (line_ok_light c) ls`;
val _ = export_rewrites["sec_ok_light_def"];

val _ = overload_on("all_enc_ok_light",``λc ls.
  EVERY (sec_ok_light c) ls``);

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
    Asm x (bytes ++ nop) (len+1) :: xs) /\
  (add_nop nop ((LabAsm y w bytes len)::xs) =
    LabAsm y w (bytes ++ nop) (len+1) :: xs)`;

val pad_section_def = Define `
  (pad_section nop [] aux = REVERSE aux) /\
  (pad_section nop ((Label l1 l2 len)::xs) aux =
     pad_section nop xs ((Label l1 l2 0)::
     if len = 0 then aux else add_nop nop aux)) /\
  (pad_section nop ((Asm x bytes len)::xs) aux =
     pad_section nop xs (Asm x (pad_bytes bytes len nop) len::aux)) /\
  (pad_section nop ((LabAsm y w bytes len)::xs) aux =
     pad_section nop xs (LabAsm y w (pad_bytes bytes len nop) len::aux))`

val pad_code_def = Define `
(pad_code nop [] = []) /\
(pad_code nop ((Section n xs)::ys) =
  Section n (pad_section nop xs []) :: pad_code nop ys)`

Theorem pad_code_MAP:
   pad_code nop =
    MAP (λx. Section (Section_num x) (pad_section nop (Section_lines x) []))
Proof
  simp[FUN_EQ_THM] \\ Induct \\ simp[pad_code_def]
  \\ Cases \\ simp[pad_code_def]
QED

val sec_length_def = Define `
  (sec_length [] k = k) /\
  (sec_length ((Label _ _ l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((Asm x1 x2 l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((LabAsm a w bytes l)::xs) k = sec_length xs (k+l))`

(* top-level assembler function *)

val remove_labels_loop_def = Define `
  remove_labels_loop clock c pos init_labs ffis sec_list =
    (* compute labels *)
    let labs = compute_labels_alt pos sec_list init_labs in
    (* update encodings and lengths (but not label lengths) *)
    let (sec_list,done) = enc_secs_again pos labs ffis c.encode sec_list in
      (* done ==> labs are still fine *)
      if done then
        (* adjust label lengths *)
        let sec_list = upd_lab_len pos sec_list in
        (* compute labels again *)
        let labs = compute_labels_alt pos sec_list init_labs in
        (* update encodings *)
        let (sec_list,done) = enc_secs_again pos labs ffis c.encode sec_list in
        (* move label padding into instructions *)
        let sec_list = pad_code (c.encode (Inst Skip)) sec_list in
        (* it ought to be impossible for done to be false here *)
          if done /\ all_enc_ok_light c sec_list
          then SOME (sec_list,labs)
          else NONE
      else
        (* repeat *)
        if clock = 0:num then NONE else
          remove_labels_loop (clock-1) c pos init_labs ffis sec_list`

val remove_labels_def = Define `
  remove_labels init_clock c pos labs ffis sec_list =
    (* Here init_clock puts an upper limit on the number of times the
       lengths can be adjusted. In many cases, clock = 0 should be
       enough. If this were to hit the clock limit for large values of
       init_clock, then something is badly wrong. Worth testing with
       the clock limit set to low values to see how many iterations
       are used. *)
    remove_labels_loop init_clock c pos labs ffis (enc_sec_list c.encode sec_list)`;

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

val prog_to_bytes_ind = theorem"prog_to_bytes_ind";

Theorem prog_to_bytes_MAP:
   ∀ls. prog_to_bytes ls = FLAT
          (MAP (FLAT o MAP line_bytes o Section_lines) ls)
Proof
  ho_match_mp_tac prog_to_bytes_ind \\ rw[prog_to_bytes_def]
QED

(* compile labels *)

val _ = Datatype`
  config = <| labels : num num_map num_map
            ; pos : num
            ; asm_conf : 'a asm_config
            ; init_clock : num
            ; ffi_names : string list option
            ; hash_size : num
            |>`;

val list_add_if_fresh_def = Define `
  (list_add_if_fresh e [] = [e]) /\
  (list_add_if_fresh e (f::r) =
    if e = f then f::r else f::list_add_if_fresh e r)`

val find_ffi_names_def = Define `
  (find_ffi_names [] = []) /\
  (find_ffi_names (Section k []::rest) =
     find_ffi_names rest) /\
  (find_ffi_names (Section k (x::xs)::rest) =
   (case x of LabAsm (CallFFI s) _ _ _ =>
       list_add_if_fresh s (find_ffi_names (Section k xs::rest))
   | _ => find_ffi_names (Section k xs::rest)))`

val compile_lab_def = Define `
  compile_lab c sec_list =
    let current_ffis = find_ffi_names sec_list in
    let (ffis,ffis_ok) =
      case c.ffi_names of SOME ffis => (ffis, list_subset current_ffis ffis) | _ => (current_ffis,T)
    in
    if ffis_ok then
      case remove_labels c.init_clock c.asm_conf c.pos c.labels ffis sec_list of
      | SOME (sec_list,l1) =>
          SOME (prog_to_bytes sec_list,
                c with <| labels := l1;
                          pos := FOLDL (λpos sec. sec_length (Section_lines sec) pos) c.pos sec_list;
                          ffi_names := SOME ffis
                        |>)
      | NONE => NONE
    else NONE`;

(* compile labLang *)

val compile_def = Define `
  compile lc sec_list = compile_lab lc (filter_skip sec_list)`;

val _ = export_theory();
