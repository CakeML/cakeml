(*
  The formal semantics of the target machine language. This semantics
  is parametrised by the target configuration, which includes the next
  state function of the target architecture.
*)
Theory targetSem
Ancestors
  ffi lab_to_target wordSem evaluateProps asmProps
Libs
  preamble

(* -- execute target machine with interference from environment -- *)

Datatype:
  machine_result = Halt outcome | Error | TimeOut
End

Datatype:
  machine_config =
   <| prog_addresses : ('a word) set
    ; shared_addresses : ('a word) set
    (* FFI-specific configurations *)
    ; ffi_entry_pcs : ('a word) list
    ; ffi_names : ffiname list
    ; ptr_reg : num
    ; len_reg : num
    ; ptr2_reg : num
    ; len2_reg : num
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
    (* ffi_index -> byte_size, address, register to be updated/ stored, new pc value *)
    ; mmio_info : (num # (word8 # 'a addr # num # 'a word)) list
    |>
End

Definition apply_oracle_def:
  apply_oracle oracle x =
    (oracle (0:num) x, shift_seq 1 oracle)
End

Definition encoded_bytes_in_mem_def:
  encoded_bytes_in_mem c pc m md ⇔
    ∃i k. k * (2 ** c.code_alignment) < LENGTH (c.encode i) ∧
      bytes_in_memory pc
        (DROP (k * (2 ** c.code_alignment)) (c.encode i))
        m md
End

Definition read_ffi_bytearray_def:
  read_ffi_bytearray mc ptr_reg len_reg ms =
    read_bytearray (mc.target.get_reg ms ptr_reg)
      (w2n (mc.target.get_reg ms len_reg))
      (λa.
        if a ∈ mc.prog_addresses then
          SOME (mc.target.get_byte ms a)
        else NONE)
End

Definition read_ffi_bytearrays_def:
  read_ffi_bytearrays mc ms =
    (read_ffi_bytearray mc mc.ptr_reg mc.len_reg ms,
     read_ffi_bytearray mc mc.ptr2_reg mc.len2_reg ms)
End

Definition is_valid_mapped_read_def:
  is_valid_mapped_read pc (nb: word8) (ad: 'a addr) r pc' t ms md =
    if nb = 1w
    then
      (bytes_in_memory pc (t.config.encode (Inst (Mem Load8 r ad)))
        (t.get_byte ms) md)
    else if nb = 0w
    then
      (bytes_in_memory pc (t.config.encode (Inst (Mem Load r ad)))
        (t.get_byte ms) md)
    else if nb = 2w
    then
      (bytes_in_memory pc (t.config.encode (Inst (Mem Load16 r ad)))
        (t.get_byte ms) md)
    else if nb = 4w
    then
      (bytes_in_memory pc (t.config.encode (Inst (Mem Load32 r ad)))
        (t.get_byte ms) md)
    else F
End

Definition is_valid_mapped_write_def:
  is_valid_mapped_write pc (nb:word8) (ad: 'a addr) r pc' t ms md =
    if nb = 1w
    then
        (bytes_in_memory pc (t.config.encode (Inst (Mem Store8 r ad)))
          (t.get_byte ms) md)
    else if nb = 0w
    then
        (bytes_in_memory pc (t.config.encode (Inst (Mem Store r ad)))
          (t.get_byte ms) md)
    else if nb = 2w
    then
        (bytes_in_memory pc (t.config.encode (Inst (Mem Store16 r ad)))
          (t.get_byte ms) md)
    else if nb = 4w
    then
        (bytes_in_memory pc (t.config.encode (Inst (Mem Store32 r ad)))
          (t.get_byte ms) md)
    else F
End

Definition evaluate_def:
  evaluate (mc:('b,'a,'c) machine_config) (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0 then (TimeOut,ms,ffi)
    else
      if (mc.target.get_pc ms) IN (mc.prog_addresses DIFF (set mc.ffi_entry_pcs)) then
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
            (case EL ffi_index mc.ffi_names of
             | SharedMem op =>
                 (case ALOOKUP mc.mmio_info ffi_index of
                  | NONE => (Error, ms, ffi)
                  | SOME (nb,a,reg,pc') =>
                      (case op of
                         | MappedRead =>
                             (case a of
                              | Addr r off =>
                                  let ad = mc.target.get_reg ms r + off in
                                    (if (if nb = 0w
                                         then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
                                        (ad IN mc.shared_addresses) ∧
                                        is_valid_mapped_read (mc.target.get_pc ms) nb a reg pc'
                                                             mc.target ms mc.prog_addresses
                                     then
                                       (case call_FFI ffi (EL ffi_index mc.ffi_names) [nb]
                                                      (word_to_bytes ad F) of
                                        | FFI_final outcome =>
                                            (Halt (FFI_outcome outcome),ms,ffi)
                                        | FFI_return new_ffi new_bytes =>
                                            let (ms1,new_oracle)
                                                = apply_oracle mc.ffi_interfer
                                                               (ffi_index,new_bytes,ms) in
                                              let mc = mc with ffi_interfer := new_oracle in
                                                evaluate mc new_ffi (k - 1:num) ms1)
                                     else (Error,ms,ffi)))
                         | MappedWrite =>
                             (case a of
                              | Addr r off =>
                                  let ad = (mc.target.get_reg ms r) + off in
                                    (if (if nb = 0w
                                         then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
                                        (ad IN mc.shared_addresses) ∧
                                        is_valid_mapped_write (mc.target.get_pc ms) nb a reg pc'
                                                              mc.target ms mc.prog_addresses
                                     then
                                       (case call_FFI ffi (EL ffi_index mc.ffi_names) [nb]
                                                      ((let w = mc.target.get_reg ms reg in
                                                          if nb = 0w then word_to_bytes w F
                                                          else word_to_bytes_aux (w2n nb) w F)
                                                       ++ (word_to_bytes ad F)) of
                                        | FFI_final outcome =>
                                            (Halt (FFI_outcome outcome),ms,ffi)
                                        | FFI_return new_ffi new_bytes =>
                                            let (ms1,new_oracle)
                                                = apply_oracle mc.ffi_interfer
                                                               (ffi_index,new_bytes,ms) in
                                              let mc = mc with ffi_interfer := new_oracle in
                                                evaluate mc new_ffi (k - 1:num) ms1)
                                     else (Error,ms,ffi)))))
             | ExtCall _ =>
                 (case ALOOKUP mc.mmio_info ffi_index of
                  | SOME _ => (Error, ms, ffi)
                  | NONE =>
                      (case read_ffi_bytearrays mc ms of
                       | (SOME bytes, SOME bytes2) =>
                           (case call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 of
                            | FFI_final outcome => (Halt (FFI_outcome outcome),ms,ffi)
                            | FFI_return new_ffi new_bytes =>
                                let (ms1,new_oracle)
                                    = apply_oracle mc.ffi_interfer
                                                   (ffi_index,new_bytes,ms) in
                                  let mc = mc with ffi_interfer := new_oracle in
                                    evaluate mc new_ffi (k - 1:num) ms1)
                       | _ => (Error,ms,ffi))))
End

Definition machine_sem_def:
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
     ?k. FST (evaluate mc st k ms) = Error)
End

(* define what it means for code to be loaded and ready to run *)

Definition code_loaded_def:
  code_loaded (bytes:word8 list) (mc:(α,β,γ)machine_config) (ms:β) <=>
    read_bytearray (mc.target.get_pc ms) (LENGTH bytes)
      (\a. if a IN mc.prog_addresses
           then SOME (mc.target.get_byte ms a) else NONE) = SOME bytes
End

(* target_configured: target and mc_conf are compatible
   will be proved at the top-level by creating an appropriate t *)
Definition target_configured_def:
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
End

Definition get_reg_value_def:
  (get_reg_value NONE w f = w) /\
  (get_reg_value (SOME v) _ f = f v)
End

Definition mmio_pcs_min_index_def:
  mmio_pcs_min_index ffi_names =
  some x.
    ((x <= LENGTH ffi_names) /\
    (!j. j < x ==> (∃s.
      EL j ffi_names =  ExtCall s)) /\
    (!j. x <= j /\ j < LENGTH ffi_names ==>
         (∃op. EL j ffi_names = SharedMem op)))
End

(* start_pc_ok: machine configuration's saved pcs and initial pc are ok *)
Definition start_pc_ok_def:
  start_pc_ok mc_conf pc ⇔
    mc_conf.halt_pc NOTIN mc_conf.prog_addresses /\
    mc_conf.ccache_pc NOTIN mc_conf.prog_addresses /\
    mc_conf.halt_pc NOTIN mc_conf.shared_addresses /\
    mc_conf.ccache_pc NOTIN mc_conf.shared_addresses /\
    pc - n2w ffi_offset = mc_conf.halt_pc /\
    pc - n2w (2*ffi_offset) = mc_conf.ccache_pc /\
    (1w && pc) = 0w /\
    ?i. mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
    (!index.
       index < i ==>
       pc - n2w ((3 + index) * ffi_offset) NOTIN
       mc_conf.prog_addresses /\
       pc - n2w ((3 + index) * ffi_offset) NOTIN
       mc_conf.shared_addresses /\
       pc - n2w ((3 + index) * ffi_offset) <>
       mc_conf.halt_pc /\
       pc - n2w ((3 + index) * ffi_offset) <>
       mc_conf.ccache_pc /\
       find_index
         (pc - n2w ((3 + index) * ffi_offset))
         mc_conf.ffi_entry_pcs 0 = SOME index) /\
    (!index.
      index < LENGTH mc_conf.ffi_names /\ i <= index ==>
      mc_conf.halt_pc <> (EL index mc_conf.ffi_entry_pcs) /\
      mc_conf.ccache_pc <> (EL index mc_conf.ffi_entry_pcs)) /\
    LENGTH mc_conf.ffi_names = LENGTH mc_conf.ffi_entry_pcs
End

(* ffi_interfer_ok: the FFI interference oracle is ok:
   target_state_rel is preserved for any FFI behaviour *)
Definition ffi_interfer_ok_def:
  ffi_interfer_ok pc io_regs mc_conf ⇔
    (∀ms2 k index new_bytes t1 bytes bytes2 i.
       index < LENGTH mc_conf.ffi_names ∧
       mmio_pcs_min_index mc_conf.ffi_names = SOME i /\
       mc_conf.prog_addresses = t1.mem_domain ==>
         (index < i ==>
           read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) ∧
           LENGTH new_bytes = LENGTH bytes2 ∧
           (EL index mc_conf.ffi_names = ExtCall "" ⇒ new_bytes = bytes2) ∧
           target_state_rel mc_conf.target
             (t1 with pc := -n2w ((3 + index) * ffi_offset) + pc) ms2 ∧
           aligned mc_conf.target.config.code_alignment
            (t1.regs (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n))
        ⇒
        target_state_rel mc_conf.target
            (t1 with
             <|regs :=
                (λa.
                 get_reg_value
                   (if MEM a mc_conf.callee_saved_regs then NONE else io_regs k (EL index mc_conf.ffi_names) a)
                   (t1.regs a) I);
               mem := asm_write_bytearray (t1.regs mc_conf.ptr2_reg) new_bytes t1.mem;
               pc := t1.regs (case mc_conf.target.config.link_reg of NONE => 0
                      | SOME n => n)|>)
            (mc_conf.ffi_interfer k (index,new_bytes,ms2))) /\
         (i <= index /\
           target_state_rel mc_conf.target
            (t1 with pc := EL index mc_conf.ffi_entry_pcs) ms2 ==>
              (∃info. ALOOKUP mc_conf.mmio_info index = SOME info ∧
               (EL index mc_conf.ffi_names = SharedMem MappedRead ==>
               !new_bytes.
               target_state_rel mc_conf.target
                 (t1 with
                 <|pc := SND(SND(SND info))
                  (* it is possible that there is a side effect that
                  * affects other register e.g. temp in arm8, but we don't have to
                  * worry about it as target_state_rel ignore members of
                  * avoid_regs *)
                  (* assume the byte array to be in little endian *)
                  ;regs := (\n. if n = FST(SND(SND info)) then
                      (word_of_bytes F 0w new_bytes) else t1.regs n)|>)
                  (mc_conf.ffi_interfer k (index,new_bytes,ms2))) /\
               (EL index mc_conf.ffi_names = SharedMem MappedWrite ==>
               target_state_rel mc_conf.target
                 (t1 with
                 <|pc := SND(SND(SND info))|>)
                 (mc_conf.ffi_interfer k (index,new_bytes,ms2))))))
End

Definition ccache_interfer_ok_def:
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
                  | SOME n => n) |> )
        (mc_conf.ccache_interfer k (a1,a2,ms2)))
End

(*
  good_init_state:
    intermediate invariant describing how
    code (bytes) and ffi is installed in the machine (mc_conf, ms)
    using labLang (m, dm, cbspace) and
    target semantics (t, io_regs, cc_regs) information as an intermediary
  these are all destined to be assumptions on the top-level correctness theorem
*)

Definition good_init_state_def:
  good_init_state
    (mc_conf: ('a,'state,'b) machine_config) ms bytes
    cbspace
    t m dm sdm
    io_regs cc_regs
    <=>
    target_state_rel mc_conf.target t ms /\
    target_configured t mc_conf ∧

    (* starting pc assumptions *)
    t.pc = mc_conf.target.get_pc ms /\
    start_pc_ok mc_conf t.pc ∧
    (n2w (2 ** t.align - 1) && t.pc) = 0w /\

    interference_ok mc_conf.next_interfer (mc_conf.target.proj mc_conf.prog_addresses) /\
    ffi_interfer_ok t.pc io_regs mc_conf ∧
    ccache_interfer_ok t.pc cc_regs mc_conf ∧

    (* code memory relation *)
    code_loaded bytes mc_conf ms /\
    bytes_in_mem t.pc bytes t.mem t.mem_domain dm /\
    (* data memory relation -- note that this implies m contains no labels *)
    dm SUBSET t.mem_domain /\
    (!a. byte_align a ∈ dm ==> a ∈ dm) /\
    sdm = mc_conf.shared_addresses /\
    (!a. byte_align a IN sdm ==> a IN sdm) /\
    DISJOINT mc_conf.prog_addresses mc_conf.shared_addresses /\
    (!a. ∃w.
      t.mem a = get_byte a w mc_conf.target.config.big_endian ∧
      m (byte_align a) = Word w) /\
    (* code buffer constraints *)
    (∀n. n < cbspace ⇒
      n2w (n + LENGTH bytes) + t.pc ∈ t.mem_domain  ∧
      n2w (n + LENGTH bytes) + t.pc NOTIN dm) ∧
    cbspace + LENGTH bytes < dimword(:'a)
End

(* CakeML code, bytes, and code buffer space, cspace, and FFI functions, ffi,
   are installed into the machine, mc_conf + ms
   r1 and r2 are the names of registers containing
   the first address of the CakeML heap and the first address past the CakeML stack
   i.e., the range of the data memory
*)
Definition installed_def:
  installed bytes cbspace bitmaps data_sp ffi_names (r1,r2) (mc_conf:('a,'state,'b) machine_config) shmem_extra ms ⇔
    ∃t m io_regs cc_regs bitmap_ptr bitmaps_dm sdm.
      let heap_stack_dm = { w | t.regs r1 <=+ w ∧ w <+ t.regs r2 } in
      good_init_state mc_conf ms bytes cbspace t m (heap_stack_dm ∪ bitmaps_dm) sdm io_regs cc_regs ∧
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
      ffi_names = SOME mc_conf.ffi_names /\
   (!i. mmio_pcs_min_index mc_conf.ffi_names = SOME i ==>
     MAP (\rec. rec.entry_pc + mc_conf.target.get_pc ms) shmem_extra =
      DROP i mc_conf.ffi_entry_pcs /\
     mc_conf.mmio_info = ZIP (GENLIST (λindex. index + i) (LENGTH shmem_extra),
                              (MAP (\rec. (rec.nbytes, rec.access_addr, rec.reg,
                                           rec.exit_pc + mc_conf.target.get_pc ms))
                                   shmem_extra)) /\
    cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a))
End

