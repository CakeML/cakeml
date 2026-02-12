(*
  This compiler phase generates concrete (ARM, x64, ag32, RISC-V,
  MIPS) machine code from labLang assembly programs. This phase is the
  CakeML compiler's assembler: it computes label offsets and encodes
  all instructions according to the instruction encoder stored in the
  compiler configuration.
*)
Theory lab_to_target
Ancestors
  labLang lab_filter ffi
Libs
  preamble

(* Number of bytes per FFI *)
Definition ffi_offset_def:
  ffi_offset = 16:num
End

(* basic assemble function *)

Definition lab_inst_def:
  (lab_inst w (Jump _) = Jump w) /\
  (lab_inst w (JumpCmp c r ri _) = JumpCmp c r ri w) /\
  (lab_inst w (Call _) = Call w) /\
  (lab_inst w (LocValue r _) = Loc r (w:'a word)) /\
  (lab_inst w (Halt) = Jump w) /\
  (lab_inst w (Install) = Jump w) /\
  (lab_inst w (CallFFI n) = Jump w)
End

Definition cbw_to_asm_def[simp]:
  cbw_to_asm a =
  case a of
    Asmi a => a
  | Cbw r1 r2 => Inst (Mem Store8 r2 (Addr r1 0w))
  | ShareMem m r ad => Inst (Mem m r ad)
End


Definition enc_line_def:
  (enc_line enc skip_len (Label n1 n2 n3) = Label n1 n2 skip_len) /\
  (enc_line enc skip_len (Asm a _ _) =
     let bs = enc (cbw_to_asm a) in Asm a bs (LENGTH bs)) /\
  (enc_line enc skip_len (LabAsm l _ _ _) =
     let bs = enc (lab_inst 0w l) in
       LabAsm l 0w bs (LENGTH bs))
End

Definition enc_sec_def:
  enc_sec enc skip_len (Section k xs) =
    Section k (MAP (enc_line enc skip_len) xs)
End

Definition enc_sec_list_def:
  enc_sec_list enc xs =
    let skip_len = LENGTH (enc (Inst Skip)) in
      MAP (enc_sec enc skip_len) xs
End

(* compute labels *)

Definition section_labels_def:
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
     section_labels (pos+len) xs labs)
End

Definition compute_labels_alt_def:
  (compute_labels_alt pos [] labs = labs) /\
  (compute_labels_alt pos (Section k lines::rest) labs =
    let (new_pos,sec_labs) = section_labels pos lines [] in
    compute_labels_alt new_pos rest
      (insert k (fromAList ((0,pos)::sec_labs)) labs))
End

(* update code, but not label lengths *)

Definition find_pos_def:
  find_pos (Lab k1 k2) labs =
    (lookup_any k2 (lookup_any k1 labs LN) 0):num
End

Definition get_label_def:
  (get_label (Jump l) = l) /\
  (get_label (JumpCmp c r ri l) = l) /\
  (get_label (Call l) = l) /\
  (get_label (LocValue r l) = l) /\
  (* cannot happen *)
  (get_label _ = Lab 0 0)
End

(* It should never happen that get_ffi_index returns the default 0 ---
   nonetheless, having a default prevents the translator from generating
   painful side conditions.
 *)
Definition get_ffi_index_def:
  get_ffi_index ffis s =
    the 0 (find_index s ffis 0)
End

Definition get_jump_offset_def:
  (get_jump_offset (CallFFI s) ffis labs pos =
     0w - n2w (pos + (3 + get_ffi_index ffis (ExtCall s)) * ffi_offset)) /\
  (get_jump_offset Install ffis labs pos =
     0w - n2w (pos + 2 * ffi_offset)) /\
  (get_jump_offset Halt ffis labs pos =
     0w - n2w (pos + ffi_offset)) /\
  (get_jump_offset a ffis labs pos =
     n2w (find_pos (get_label a) labs) - n2w pos)
End

Definition enc_lines_again_def:
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
             ((LabAsm a w1 bs l1)::acc, ok /\ (l1 = l)))
End

Definition enc_secs_again_def:
  (enc_secs_again pos labs ffis enc [] = ([],T)) /\
  (enc_secs_again pos labs ffis enc ((Section s lines)::rest) =
     let (lines1,pos1,ok) = enc_lines_again labs ffis pos enc lines ([],T) in
     let (rest1,ok1) = enc_secs_again pos1 labs ffis enc rest in
       ((Section s lines1)::rest1,ok /\ ok1))
End

(* update labels *)

Definition lines_upd_lab_len_def:
  (lines_upd_lab_len pos [] acc = (REVERSE acc,pos)) /\
  (lines_upd_lab_len pos ((Label k1 k2 l)::xs) acc =
     let l1 = if EVEN pos then 0 else 1 in
       lines_upd_lab_len (pos+l1) xs ((Label k1 k2 l1::acc))) /\
  (lines_upd_lab_len pos ((Asm x1 x2 l)::xs) acc =
     lines_upd_lab_len (pos+l) xs ((Asm x1 x2 l) :: acc)) /\
  (lines_upd_lab_len pos ((LabAsm a w bytes l)::xs) acc =
     lines_upd_lab_len (pos+l) xs ((LabAsm a w bytes l) :: acc))
End

Definition upd_lab_len_def:
  (upd_lab_len pos [] = []) /\
  (upd_lab_len pos ((Section s lines)::rest) =
     let (lines1,pos1) = lines_upd_lab_len pos lines [] in
     let rest1 = upd_lab_len pos1 rest in
       (Section s lines1)::rest1)
End

(* checking that all labelled asm instructions are asm_ok *)

Definition line_ok_light_def:
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
     asm_ok (lab_inst w a) c)
End

Definition sec_ok_light_def[simp]:
  sec_ok_light c (Section k ls) ⇔
    EVERY (line_ok_light c) ls
End

Overload all_enc_ok_light = ``λc ls. EVERY (sec_ok_light c) ls``

(* pad with nop byte, and nop instruction *)

Definition pad_bytes_def:
  pad_bytes bytes len nop =
    let len_bytes = LENGTH bytes in
      if len <= len_bytes then bytes else
        TAKE len (bytes ++ FLAT (REPLICATE len nop))
End

Definition add_nop_def:
  (add_nop nop [] = []) /\
  (add_nop nop ((Label l1 l2 len)::xs) =
    (Label l1 l2 len)::add_nop nop xs) /\
  (add_nop nop ((Asm x bytes len)::xs) =
    Asm x (bytes ++ nop) (len+1) :: xs) /\
  (add_nop nop ((LabAsm y w bytes len)::xs) =
    LabAsm y w (bytes ++ nop) (len+1) :: xs)
End

Definition pad_section_def:
  (pad_section nop [] aux = REVERSE aux) /\
  (pad_section nop ((Label l1 l2 len)::xs) aux =
     pad_section nop xs ((Label l1 l2 0)::
     if len = 0 then aux else add_nop nop aux)) /\
  (pad_section nop ((Asm x bytes len)::xs) aux =
     pad_section nop xs (Asm x (pad_bytes bytes len nop) len::aux)) /\
  (pad_section nop ((LabAsm y w bytes len)::xs) aux =
     pad_section nop xs (LabAsm y w (pad_bytes bytes len nop) len::aux))
End

Definition pad_code_def:
(pad_code nop [] = []) /\
(pad_code nop ((Section n xs)::ys) =
  Section n (pad_section nop xs []) :: pad_code nop ys)
End

Theorem pad_code_MAP:
   pad_code nop =
    MAP (λx. Section (Section_num x) (pad_section nop (Section_lines x) []))
Proof
  simp[FUN_EQ_THM] \\ Induct \\ simp[pad_code_def]
  \\ Cases \\ simp[pad_code_def]
QED

Definition sec_length_def:
  (sec_length [] k = k) /\
  (sec_length ((Label _ _ l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((Asm x1 x2 l)::xs) k = sec_length xs (k+l)) /\
  (sec_length ((LabAsm a w bytes l)::xs) k = sec_length xs (k+l))
End

Definition get_symbols_def:
  (get_symbols pos [] = []) /\
  (get_symbols pos ((Section k l)::secs) =
    let len = sec_length l 0 in (k, pos, len)::get_symbols (pos+len) secs)
End

(* Compute the labels whose second part is 0 *)
Definition zero_labs_acc_of_def[simp]:
  (zero_labs_acc_of (LocValue _ (Lab n1 n2)) acc =
    if n2 = 0 then insert n1 () acc else acc) ∧
  (zero_labs_acc_of (Jump (Lab n1 n2)) acc =
    if n2 = 0 then insert n1 () acc else acc) ∧
  (zero_labs_acc_of (JumpCmp _ _ _ (Lab n1 n2)) acc =
    if n2 = 0 then insert n1 () acc else acc) ∧
  (zero_labs_acc_of _ acc = acc)
End


Definition line_get_zero_labs_acc_def:
  line_get_zero_labs_acc (LabAsm a _ _ _) acc = zero_labs_acc_of a acc ∧
  line_get_zero_labs_acc _ acc = acc
End

Definition sec_get_zero_labs_acc_def:
  sec_get_zero_labs_acc (Section _ lines) acc =
    FOLDR line_get_zero_labs_acc acc lines
End

Definition get_zero_labs_acc_def:
  get_zero_labs_acc code =
    FOLDR sec_get_zero_labs_acc LN code
End

Definition zero_labs_acc_exist_def:
  zero_labs_acc_exist labs code ⇔
    let zlabs = toAList (get_zero_labs_acc code)
    in
    EVERY ( λ(n,_).
    case lookup n labs of
    | NONE => F
    | SOME l => lookup 0 l ≠ NONE) zlabs
End

(* top-level assembler function *)

Definition remove_labels_loop_def:
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
          if done /\ all_enc_ok_light c sec_list ∧
             zero_labs_acc_exist labs sec_list
          then SOME (sec_list,labs)
          else NONE
      else
        (* repeat *)
        if clock = 0:num then NONE else
          remove_labels_loop (clock-1) c pos init_labs ffis sec_list
End

Definition remove_labels_def:
  remove_labels init_clock c pos labs ffis sec_list =
    (* Here init_clock puts an upper limit on the number of times the
       lengths can be adjusted. In many cases, clock = 0 should be
       enough. If this were to hit the clock limit for large values of
       init_clock, then something is badly wrong. Worth testing with
       the clock limit set to low values to see how many iterations
       are used. *)
    remove_labels_loop init_clock c pos labs ffis (enc_sec_list c.encode sec_list)
End

(* code extraction *)

Definition line_bytes_def:
  (line_bytes (Label _ _ _) = []) /\
  (line_bytes (Asm _ bytes _) = bytes) /\
  (line_bytes (LabAsm _ _ bytes _) = bytes)
End

Definition prog_to_bytes_def:
  (prog_to_bytes [] = []) /\
  (prog_to_bytes ((Section k [])::xs) = prog_to_bytes xs) /\
  (prog_to_bytes ((Section k (y::ys))::xs) =
     line_bytes y ++ prog_to_bytes ((Section k ys)::xs))
End

val prog_to_bytes_ind = theorem"prog_to_bytes_ind";

Theorem prog_to_bytes_MAP:
   ∀ls. prog_to_bytes ls = FLAT
          (MAP (FLAT o MAP line_bytes o Section_lines) ls)
Proof
  ho_match_mp_tac prog_to_bytes_ind \\ rw[prog_to_bytes_def]
QED

(* compile labels *)
Datatype:
  shmem_rec = <| entry_pc: 'a word
               ; nbytes: word8
               ; access_addr: 'a addr
               ; reg: num
               ; exit_pc: 'a word
               |>
End

Type shmem_info = ``:'a shmem_rec list``;

Datatype:
  config = <| labels : num num_map num_map
            ; sec_pos_len : (num # num # num) list
            ; pos : num
            ; asm_conf : 'a asm_config
            ; init_clock : num
            ; ffi_names : ffiname list option
            (* shmem_info is
            * a list of (entry pc, no. of bytes, address of the shared memory, register
            * to be load/store and the end pc)s for each share memory access *)
            ; shmem_extra: 'a shmem_info
            ; hash_size : num
            |>
End

Definition list_add_if_fresh_def:
  (list_add_if_fresh e [] = [e]) /\
  (list_add_if_fresh e (f::r) =
    if e = f then f::r else f::list_add_if_fresh e r)
End

Definition find_ffi_names_def:
  (find_ffi_names [] = []) /\
  (find_ffi_names (Section k []::rest) =
     find_ffi_names rest) /\
  (find_ffi_names (Section k (x::xs)::rest) =
   (case x of LabAsm (CallFFI s) _ _ _ =>
       list_add_if_fresh (ExtCall s) (find_ffi_names (Section k xs::rest))
   | _ => find_ffi_names (Section k xs::rest)))
End

Definition get_memop_info_def:
  get_memop_info Load = (MappedRead, 0w) /\
  get_memop_info Load32 = (MappedRead,4w) /\
  get_memop_info Load16 = (MappedRead,2w) /\
  get_memop_info Load8 = (MappedRead,1w) /\
  get_memop_info Store = (MappedWrite, 0w) /\
  get_memop_info Store32 = (MappedWrite,4w) /\
  get_memop_info Store16 = (MappedWrite,2w) /\
  get_memop_info Store8 =(MappedWrite,1w)
End

(* produce a list of ffi_names for shared memory instructions and
  a list of shmem_infos (e.g. pc of the shared memory instruction) *)
Definition get_shmem_info_def:
  (get_shmem_info [] pos ffi_names (shmem_info: 'a shmem_info) =
    (ffi_names, shmem_info)) /\
  (get_shmem_info (Section k []::rest) pos ffi_names shmem_info =
    get_shmem_info rest pos ffi_names shmem_info) /\
  (get_shmem_info (Section k ((Label _ _ _)::xs)::rest) pos ffi_names shmem_info =
    get_shmem_info (Section k xs::rest) pos ffi_names shmem_info) /\
  (get_shmem_info (Section k ((Asm (ShareMem m r ad) bytes _)::xs)::rest) pos
  ffi_names shmem_info =
    let (name,nb) = get_memop_info m in
    get_shmem_info (Section k xs::rest) (pos+LENGTH bytes) (ffi_names ++ [SharedMem name])
      (shmem_info ++ [
        <|entry_pc:=n2w pos
        ; nbytes:=nb
        ;access_addr:=ad
        ;reg:=r
        ;exit_pc:=n2w $ pos+LENGTH bytes|>])) /\
  (get_shmem_info (Section k ((LabAsm _ _ bytes _)::xs)::rest) pos ffi_names shmem_info =
    get_shmem_info (Section k xs::rest) (pos+LENGTH bytes) ffi_names shmem_info) /\
  (get_shmem_info (Section k ((Asm _ bytes _)::xs)::rest) pos ffi_names shmem_info =
    get_shmem_info (Section k xs::rest) (pos+LENGTH bytes) ffi_names shmem_info)
End

(*
Definition compile_lab_def:
  compile_lab c sec_list =
    let current_ffis = FILTER (\x. x <> "MappedRead" /\ x <> "MappedWrite") $
      find_ffi_names sec_list in
    let (ffis,ffis_ok) =
      case c.ffi_names of SOME ffis => (ffis, list_subset current_ffis ffis) | _ => (current_ffis,T)
    in
    if ffis_ok then
      case remove_labels c.init_clock c.asm_conf c.pos c.labels ffis sec_list of
      | SOME (sec_list,l1) =>
          let bytes = prog_to_bytes sec_list in
          let (new_ffis,shmem_infos) = get_shmem_info sec_list c.pos [] [] in
          SOME (bytes,
                c with <| labels := l1; pos := LENGTH bytes + c.pos;
                          sec_pos_len := get_symbols c.pos sec_list;
                          ffi_names := SOME $ ffis ++ new_ffis;
                          shmem_extra := shmem_infos |>)
      | NONE => NONE
    else NONE
End
*)

Definition compile_lab_def:
  compile_lab c sec_list =
    let current_ffis = find_ffi_names sec_list in
    let (ffis,ffis_ok) =
      case c.ffi_names of SOME ffis => (ffis, list_subset current_ffis ffis) | _ => (current_ffis, T)
    in
    if ffis_ok then
      case remove_labels c.init_clock c.asm_conf c.pos c.labels ffis sec_list of
      | SOME (sec_list,l1) =>
          let bytes = prog_to_bytes sec_list in
          let (new_ffis,shmem_infos) = get_shmem_info sec_list c.pos [] [] in
          SOME (bytes,
                c with <| labels := l1; pos := LENGTH bytes + c.pos;
                          sec_pos_len := get_symbols c.pos sec_list;
                          ffi_names := SOME $ ffis ++ new_ffis;
                          shmem_extra := shmem_infos |>)
      | NONE => NONE
    else NONE
End

(* compile labLang *)

Definition compile_def:
  compile lc sec_list = compile_lab lc (filter_skip sec_list)
End

(* config without asm conf *)

Datatype:
  shmem_info_num
  = <| entry_pc: num
       ; nbytes: word8
       ; addr_reg: num
       ; addr_off: num
       ; reg: num
       ; exit_pc: num
    |>
End

Datatype:
  inc_config = <|
    inc_labels : num num_map num_map
    ; inc_sec_pos_len : (num # num # num) list
    ; inc_pos : num
    ; inc_init_clock : num
    ; inc_ffi_names : ffiname list option
    ; inc_shmem_extra: shmem_info_num list
    ; inc_hash_size : num
    |>
End

Definition to_inc_shmem_info_def:
  to_inc_shmem_info info =
  <| entry_pc := w2n info.entry_pc
     ; nbytes := info.nbytes
     ; addr_reg := (case info.access_addr of Addr r off => r)
     ; addr_off := (case info.access_addr of Addr r off => w2n off)
     ; reg := info.reg
     ; exit_pc := w2n info.exit_pc |>
End

Definition to_shmem_info_def:
  to_shmem_info ninfo =
  <| entry_pc := n2w ninfo.entry_pc
     ; nbytes := ninfo.nbytes
     ; access_addr := Addr ninfo.addr_reg (n2w ninfo.addr_off)
     ; reg := ninfo.reg
     ; exit_pc := n2w ninfo.exit_pc |>
End

Definition config_to_inc_config_def:
  config_to_inc_config (c : 'a config) = <|
    inc_labels := c.labels; inc_sec_pos_len := c.sec_pos_len;
    inc_pos := c.pos; inc_init_clock := c.init_clock;
    inc_ffi_names := c.ffi_names; inc_shmem_extra := MAP to_inc_shmem_info c.shmem_extra;
    inc_hash_size := c.hash_size;
  |>
End

Definition inc_config_to_config_def:
  inc_config_to_config (asm : 'a asm_config) (c : inc_config) = <|
    labels := c.inc_labels; sec_pos_len := c.inc_sec_pos_len;
    pos := c.inc_pos; asm_conf := asm; init_clock := c.inc_init_clock;
    ffi_names := c.inc_ffi_names; shmem_extra := MAP to_shmem_info c.inc_shmem_extra;
    hash_size := c.inc_hash_size;
  |>
End

