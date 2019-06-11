(*
  The formal semantics of the target machine language. This semantics
  is parametrised by the target configuration, which includes the next
  state function of the target architecture.
*)
open preamble ffiTheory lab_to_targetTheory wordSemTheory
     evaluatePropsTheory asmPropsTheory;

val _ = new_theory "targetSem";

(* -- execute target machine with interference from environment -- *)

val () = Datatype `
  machine_result = Halt outcome | Error | TimeOut `;

val _ = Datatype `
  machine_config =
   <| prog_addresses : ('a word) set
    (* FFI-specific configurations *)
    ; ffi_entry_pcs : ('a word) list
    ; ffi_names : string list
    ; ptr_reg : num
    ; len_reg : num
    ; ptr2_reg : num
    ; len2_reg : num
    ; ffi_regs : num list  (* should we keep ptr_reg etc intact? *)
    ; ffi_rval : num  
    (* major interference by FFI calls *)
    ; ffi_interfer : num -> num # word8 list # 'b -> 'b
    ; callee_saved_regs : num list
    (* minor interference during execution *)
    ; next_interfer : num -> 'b -> 'b
    (* program exits successfully at halt_pc *)
    ; halt_pc : 'a word
    (* entry point for calling clear_cache *)
    ; ccache_pc : 'a word
    (* major interference by calling clear_cache *)
    ; ccache_interfer : num -> 'a word # 'a word # 'b -> 'b
    (* target next-state function etc. *)
    ; target : ('a,'b,'c) target
    |>`

val apply_oracle_def = Define `
  apply_oracle oracle x =
    (oracle (0:num) x, shift_seq 1 oracle)`

val encoded_bytes_in_mem_def = Define`
  encoded_bytes_in_mem c pc m md ⇔
    ∃i k. k * (2 ** c.code_alignment) < LENGTH (c.encode i) ∧
      bytes_in_memory pc
        (DROP (k * (2 ** c.code_alignment)) (c.encode i))
        m md`;


val get_carg_tar_def = Define `
  (get_carg_tar mc (C_array conf) n (SOME n') ms = (* with_length *)
    if conf.mutable then
     (case read_bytearray (mc.target.get_reg ms n)
      (w2n (mc.target.get_reg ms n'))
      (λa.
        if a ∈ mc.prog_addresses then
          SOME (mc.target.get_byte ms a)
        else NONE) of 
                       | SOME bytes => SOME(C_arrayv bytes)
                       | NONE => NONE)
    else NONE)

/\  (get_carg_tar mc (C_array conf) n NONE ms = (* fixed-length *)
    if conf.mutable then
   (case  read_bytearray (mc.target.get_reg ms n)
       8
       (λa.
         if a ∈ mc.prog_addresses then
           SOME (mc.target.get_byte ms a)
         else NONE) of
                       | SOME bytes => SOME(C_arrayv bytes)
                       | NONE => NONE)
    else NONE)

/\ (get_carg_tar mc C_bool n NONE ms =
    if (mc.target.get_reg ms n) = n2w 2 then
      SOME(C_primv(C_boolv T))
    else if (mc.target.get_reg ms n) = n2w 18 then
      SOME(C_primv(C_boolv F))
    else NONE)

/\ (get_carg_tar mc C_int n NONE ms =
    if word_lsb (mc.target.get_reg ms n) then NONE (* big num *)
                         else SOME(C_primv(C_intv (w2i ((mc.target.get_reg ms n) >>2)))))
/\ (get_carg_tar _ _ _ _ _ = NONE)`




val get_cargs_tar_def = Define
  `(get_cargs_tar mc [] [] [] ms = SOME [])
/\ (get_cargs_tar mc (ty::tys) (arg::args) (len::lens) ms =
    OPTION_MAP2 CONS (get_carg_tar mc ty arg len ms) (get_cargs_tar mc tys args lens ms))
/\ (get_cargs_tar _ _ _ _ _ = NONE)
`


val len_repl_ctypes = Define `
  len_repl_ctypes tys = LENGTH tys + LENGTH (FILTER (\x. ?conf. x = C_array conf /\ conf.with_length) tys)
`
(*

val evaluate_ffi_def = Define `
   evaluate_ffi ffi mc ms ms1 ffi_index = 
    case FIND (\x.x.mlname = (EL ffi_index mc.ffi_names)) ffi.signatures of
     | SOME sign => if len_repl_ctypes sign.args <= LENGTH (mc.ffi_regs) then 
                      case get_cargs_tar mc sign.args (len_filter sign.args mc.ffi_regs) (len_args sign.args mc.ffi_regs) ms of
		       | SOME cargs => 


            (case call_FFI ffi (EL ffi_index mc.ffi_names) cargs (als_args_final_word (loc_typ_val sign.args (len_filter sign.args mc.ffi_regs))) of
             | FFI_final outcome => (Halt (FFI_outcome outcome),ms,ffi)
             | FFI_return new_ffi vs retv =>
               let (ms1,new_oracle) = apply_oracle mc.ffi_interfer
                  (ffi_index,new_bytes,ms) in
                let mc = mc with ffi_interfer := new_oracle in
                  evaluate mc new_ffi (k - 1:num) ms1)
            | NONE => (Error,ms,ffi)
                    else (Error,ms,ffi)
     | NONE  => (Error,ms,ffi) `

*)

val read_ffi_bytearray_def = Define`
  read_ffi_bytearray mc ptr_reg len_reg ms =
    read_bytearray (mc.target.get_reg ms ptr_reg)
      (w2n (mc.target.get_reg ms len_reg))
      (λa.
        if a ∈ mc.prog_addresses then
          SOME (mc.target.get_byte ms a)
        else NONE)`;

val read_ffi_bytearrays_def = Define`
  read_ffi_bytearrays mc ms =
    (read_ffi_bytearray mc mc.ptr_reg mc.len_reg ms,
     read_ffi_bytearray mc mc.ptr2_reg mc.len2_reg ms)`;

val evaluate_def = Define `
  evaluate mc (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0 then (TimeOut,ms,ffi)
    else
      if mc.target.get_pc ms IN mc.prog_addresses then
        if encoded_bytes_in_mem
            mc.target.config (mc.target.get_pc ms)
            (mc.target.get_byte ms) mc.prog_addresses then
          let ms1 = mc.target.next ms in
          let (ms2,new_oracle) = apply_oracle mc.next_interfer ms1 in
          let mc = mc with next_interfer := new_oracle in
            if EVERY mc.target.state_ok [ms;ms1;ms2] ∧
               (∀x. x ∉ mc.prog_addresses ⇒
                   mc.target.get_byte ms1 x =
                   mc.target.get_byte ms x)
            then
              evaluate mc ffi (k - 1) ms2
            else
              (Error,ms,ffi)
        else (Error,ms,ffi)
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Halt Success else Halt Resource_limit_hit,ms,ffi)
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
        let mc = mc with ccache_interfer := new_oracle in
          evaluate mc ffi (k-1) ms1
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => (Error,ms,ffi)
        | SOME ffi_index => 
    (*  ms or ms1 ?*)
      case FIND (\x.x.mlname = (EL ffi_index mc.ffi_names)) ffi.signatures of
     | SOME sign => if len_repl_ctypes sign.args <= LENGTH (mc.ffi_regs) then 
                      case get_cargs_tar mc sign.args (len_filter sign.args mc.ffi_regs) (len_args sign.args mc.ffi_regs) ms of
		       | SOME cargs => 
            (case call_FFI ffi (EL ffi_index mc.ffi_names) cargs (als_args_final_word (loc_typ_val sign.args (len_filter sign.args mc.ffi_regs))) of
             | FFI_final outcome => (Halt (FFI_outcome outcome),ms,ffi)
             | FFI_return new_ffi vs retv =>
               let (ms1,new_oracle) = apply_oracle mc.ffi_interfer
                  (ffi_index,vs (*new_bytes*),ms) in
                let mc = mc with ffi_interfer := new_oracle in
                  evaluate mc new_ffi (k - 1:num) ms1)
            | NONE => (Error,ms,ffi)
                    else (Error,ms,ffi)
     | NONE  => (Error,ms,ffi)
`

(*
          case read_ffi_bytearrays mc ms of
          | SOME bytes, SOME bytes2 =>
            (case call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 of
             | FFI_final outcome => (Halt (FFI_outcome outcome),ms,ffi)
             | FFI_return new_ffi new_bytes =>
                let (ms1,new_oracle) = apply_oracle mc.ffi_interfer
                  (ffi_index,new_bytes,ms) in
                let mc = mc with ffi_interfer := new_oracle in
                  evaluate mc new_ffi (k - 1:num) ms1)
          | _ => (Error,ms,ffi)   *)


val machine_sem_def = Define `
  (machine_sem mc st ms (Terminate t io_list) <=>
     ?k ms' st'.
       evaluate mc st k ms = (Halt t,ms',st') ∧
       st'.io_events = io_list) /\
  (machine_sem mc st ms (Diverge io_trace) <=>
     (!k. ?ms' st'. evaluate mc st k ms = (TimeOut,ms',st')) /\
     lprefix_lub
       (IMAGE
         (\k. fromList (SND (SND (evaluate mc st k ms))).io_events) UNIV)
       io_trace) /\
  (machine_sem mc st ms Fail <=>
     ?k. FST (evaluate mc st k ms) = Error)`

(* define what it means for code to be loaded and ready to run *)

val code_loaded_def = Define`
  code_loaded (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) <=>
    read_bytearray (mc.target.get_pc ms) (LENGTH bytes)
      (\a. if a IN mc.prog_addresses
           then SOME (mc.target.get_byte ms a) else NONE) = SOME bytes`;

(* target_configured: target and mc_conf are compatible
   will be proved at the top-level by creating an appropriate t *)
val target_configured_def = Define`
  target_configured (t:'a asm_state) mc_conf ⇔
    ~t.failed /\
    (*
    (!q n.
       (n2w (2 ** t.align - 1) && q + (n2w n):'a word) = 0w <=>
       n MOD 2 ** t.align = 0) ∧
    *)
    t.be = mc_conf.target.config.big_endian /\
    t.align = mc_conf.target.config.code_alignment /\
    t.mem_domain = mc_conf.prog_addresses /\
    (* byte_aligned (t.regs mc_conf.ptr_reg) ∧ *)
    (* byte_aligned (t.regs mc_conf.ptr2_reg) ∧ *)
    (case mc_conf.target.config.link_reg of NONE => T | SOME r => t.lr = r)
    `;

(* start_pc_ok: machine configuration's saved pcs and initial pc are ok *)
val start_pc_ok_def = Define`
  start_pc_ok mc_conf pc ⇔
    mc_conf.halt_pc NOTIN mc_conf.prog_addresses /\
    mc_conf.ccache_pc NOTIN mc_conf.prog_addresses /\
    pc - n2w ffi_offset = mc_conf.halt_pc /\
    pc - n2w (2*ffi_offset) = mc_conf.ccache_pc /\
    (1w && pc) = 0w /\
    (!index.
       index < LENGTH mc_conf.ffi_names ==>
       pc - n2w ((3 + index) * ffi_offset) NOTIN
       mc_conf.prog_addresses /\
       pc - n2w ((3 + index) * ffi_offset) <>
       mc_conf.halt_pc /\
       pc - n2w ((3 + index) * ffi_offset) <>
       mc_conf.ccache_pc /\
       find_index
         (pc - n2w ((3 + index) * ffi_offset))
         mc_conf.ffi_entry_pcs 0 = SOME index)`;

val get_reg_value_def = Define `
  (get_reg_value NONE w f = w) /\
  (get_reg_value (SOME v) _ f = f v)`

(* ffi_interfer_ok: the FFI interference oracle is ok:
   target_state_rel is preserved for any FFI behaviour *)
val ffi_interfer_ok_def = Define`
  ffi_interfer_ok ffi pc io_regs mc_conf ⇔
    (!ms2 k index new_bytes t1 bytes bytes2 st new_st.
       index < LENGTH mc_conf.ffi_names ∧
       read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) ∧
       call_FFI_rel^* ffi st ∧
       call_FFI st (EL index mc_conf.ffi_names) bytes bytes2 = FFI_return new_st new_bytes ∧
       (mc_conf.prog_addresses = t1.mem_domain) ∧
       target_state_rel mc_conf.target
         (t1 with
          pc := -n2w ((3 + index) * ffi_offset) + pc)
       ms2 /\
       aligned mc_conf.target.config.code_alignment (t1.regs (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n)) ==>
       target_state_rel mc_conf.target
        (t1 with
         <|regs :=
            (\a.
             get_reg_value
               (if MEM a mc_conf.callee_saved_regs then NONE else io_regs k (EL index mc_conf.ffi_names) a)
               (t1.regs a) I);
           mem := asm_write_bytearray (t1.regs mc_conf.ptr2_reg) new_bytes t1.mem;
           pc := t1.regs (case mc_conf.target.config.link_reg of NONE => 0
                  | SOME n => n)|>)
        (mc_conf.ffi_interfer k (index,new_bytes,ms2)))`;

val ccache_interfer_ok_def = Define`
  ccache_interfer_ok pc cc_regs mc_conf ⇔
    (!ms2 t1 k a1 a2.
       target_state_rel mc_conf.target
         (t1 with
          pc := -n2w (2 * ffi_offset) + pc)
       ms2 /\
       aligned mc_conf.target.config.code_alignment (t1.regs (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n)) ==>
       target_state_rel mc_conf.target
        (t1 with
         <|regs :=
            (mc_conf.ptr_reg =+ t1.regs mc_conf.ptr_reg)
            (\a.
             get_reg_value
               (if MEM a mc_conf.callee_saved_regs then NONE else cc_regs k a)
               (t1.regs a) I);
           pc := t1.regs (case mc_conf.target.config.link_reg of NONE => 0
                  | SOME n => n)|>)
        (mc_conf.ccache_interfer k (a1,a2,ms2)))`;

(*
  good_init_state:
    intermediate invariant describing how
    code (bytes) and ffi is installed in the machine (mc_conf, ms)
    using labLang (m, dm, cbspace) and
    target semantics (t, io_regs, cc_regs) information as an intermediary
  these are all destined to be assumptions on the top-level correctness theorem
*)

val good_init_state_def = Define `
  good_init_state
    (mc_conf: ('a,'state,'b) machine_config) ms ffi bytes
    cbspace
    t m dm
    io_regs cc_regs
    <=>
    target_state_rel mc_conf.target t ms /\
    target_configured t mc_conf ∧

    (* starting pc assumptions *)
    t.pc = mc_conf.target.get_pc ms /\
    start_pc_ok mc_conf t.pc ∧
    (n2w (2 ** t.align - 1) && t.pc) = 0w /\

    interference_ok mc_conf.next_interfer (mc_conf.target.proj mc_conf.prog_addresses) /\
    ffi_interfer_ok ffi t.pc io_regs mc_conf ∧
    ccache_interfer_ok t.pc cc_regs mc_conf ∧

    (* code memory relation *)
    code_loaded bytes mc_conf ms /\
    bytes_in_mem t.pc bytes t.mem t.mem_domain dm /\
    (* data memory relation -- note that this implies m contains no labels *)
    dm SUBSET t.mem_domain /\
    (!a. byte_align a ∈ dm ==> a ∈ dm) /\
    (!a. ∃w.
      t.mem a = get_byte a w mc_conf.target.config.big_endian ∧
      m (byte_align a) = Word w) /\
    (* code buffer constraints *)
    (∀n. n < cbspace ⇒
      n2w (n + LENGTH bytes) + t.pc ∈ t.mem_domain  ∧
      n2w (n + LENGTH bytes) + t.pc NOTIN dm) ∧
    cbspace + LENGTH bytes < dimword(:'a)`;

(* CakeML code, bytes, and code buffer space, cspace, and FFI functions, ffi,
   are installed into the machine, mc_conf + ms
   r1 and r2 are the names of registers containing
   the first address of the CakeML heap and the first address past the CakeML stack
   i.e., the range of the data memory
*)
val installed_def = Define`
  installed bytes cbspace bitmaps data_sp ffi_names ffi (r1,r2) mc_conf ms ⇔
    ∃t m io_regs cc_regs bitmap_ptr bitmaps_dm.
      let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
      good_init_state mc_conf ms ffi bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) io_regs cc_regs ∧
      byte_aligned (t.regs r1) /\
      byte_aligned (t.regs r2) /\
      byte_aligned bitmap_ptr /\
      t.regs r1 ≤₊ t.regs r2 /\
      1024w * bytes_in_word ≤₊ t.regs r2 - t.regs r1 /\
      DISJOINT heap_stack_dm bitmaps_dm ∧
      m (t.regs r1) = Word bitmap_ptr ∧
      m (t.regs r1 + bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) ∧
      m (t.regs r1 + 2w * bytes_in_word) =
        Word (bitmap_ptr + bytes_in_word * n2w data_sp +
              bytes_in_word * n2w (LENGTH bitmaps)) ∧
      m (t.regs r1 + 3w * bytes_in_word) =
        Word (mc_conf.target.get_pc ms + n2w (LENGTH bytes)) ∧
      m (t.regs r1 + 4w * bytes_in_word) =
        Word (mc_conf.target.get_pc ms + n2w cbspace + n2w (LENGTH bytes)) ∧
      (word_list bitmap_ptr (MAP Word bitmaps) *
        word_list_exists (bitmap_ptr + bytes_in_word * n2w (LENGTH bitmaps)) data_sp)
       (fun2set (m,byte_aligned ∩ bitmaps_dm)) ∧
      ffi_names = SOME mc_conf.ffi_names`;

val _ = export_theory();
