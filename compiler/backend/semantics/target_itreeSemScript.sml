(*
  An itree-based semantics for the target machine code
*)
Theory target_itreeSem
Ancestors
  targetSem itree
Libs
  preamble

Overload get_ffi_string = “MAP (λx. case x of ExtCall s => s)”;

Datatype:
  result = Termination
         | OutOfMemory
         | Error
         | FinalFFI (ffiname # word8 list # word8 list) ffi_outcome
End

Definition eval_to_def:
  eval_to k (mc:('b,'a,'c) machine_config) (ms:'a) =
    if k = 0n then Div'
    else
      if mc.target.get_pc ms IN (mc.prog_addresses DIFF (set mc.ffi_entry_pcs)) then
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
              eval_to (k - 1) mc ms2
            else
              Ret' Error
        else Ret' Error
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Ret' Termination else Ret' OutOfMemory)
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
        let mc = mc with ccache_interfer := new_oracle in
          eval_to (k-1) mc ms1
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => Ret' Error
        | SOME ffi_index =>
            case EL ffi_index mc.ffi_names of
              | SharedMem op =>
                  (case ALOOKUP mc.mmio_info ffi_index of
                   | NONE => Ret' Error
                   | SOME (nb,a,reg,pc') =>
                       (case op of
                        | MappedRead =>
                            (case a of
                             | Addr r off =>
                                 let ad = mc.target.get_reg ms r + off in
                                   if (if nb = 0w
                                       then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
                                      ad IN mc.shared_addresses ∧
                                      is_valid_mapped_read (mc.target.get_pc ms) nb a reg pc'
                                                           mc.target ms mc.prog_addresses
                                   then
                                     let mc1 =
                                         mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                                       Vis' (SharedMem MappedRead,[nb],word_to_bytes ad F)
                                            (\new_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms)))
                                   else Ret' Error)
                        | MappedWrite =>
                            (case a of
                             | Addr r off =>
                                 let ad = (mc.target.get_reg ms r) + off in
                                   if (if nb = 0w
                                       then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
                                      (ad IN mc.shared_addresses) ∧
                                      is_valid_mapped_write (mc.target.get_pc ms) nb a reg pc'
                                                            mc.target ms mc.prog_addresses
                                   then
                                     let mc1 =
                                         mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                                       Vis'
                                       (SharedMem MappedWrite,[nb],
                                        ((let w = mc.target.get_reg ms reg in
                                            if nb = 0w then word_to_bytes w F
                                            else word_to_bytes_aux (w2n nb) w F) ++
                                         (word_to_bytes ad F)))
                                       (\new_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms)))
                                   else Ret' Error)))
              | ExtCall _ =>
                  (case ALOOKUP mc.mmio_info ffi_index of
                   | SOME _ => Ret' Error
                   | NONE =>
                       (case read_ffi_bytearrays mc ms of
                        | (SOME bytes, SOME bytes2) =>
                            let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                              if EL ffi_index mc.ffi_names = ExtCall «»
                              then
                                eval_to (k - 1) mc1 (mc.ffi_interfer 0 (ffi_index,bytes2,ms))
                              else Vis' (EL ffi_index mc.ffi_names, bytes, bytes2)
                                        (λnew_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms)))
                              | _ => Ret' Error))
End

Definition eval_def:
  eval (mc, ms) =
    case some k. eval_to k mc (ms:'a) ≠ Div' of
      NONE => Div'
    | SOME k => eval_to k mc (ms:'a)
End

Definition machine_sem_itree_def:
  machine_sem_itree (mc, ms) =
    itree_unfold_err eval
      ((λ(_,_,ws) r. LENGTH ws = LENGTH r),
      FinalFFI, (λe. FinalFFI e FFI_failed)) (mc, ms)
End

(**********)
