(*
  Properties about the target semantics
*)
Theory targetProps
Ancestors
  ffi asm targetSem misc[qualified] asmSem asmProps
Libs
  preamble

Definition shift_interfer_def:
  shift_interfer k s =
    s with next_interfer := shift_seq k s.next_interfer
End

Theorem shift_interfer_intro[local]:
  shift_interfer k1 (shift_interfer k2 c) =
    shift_interfer (k1+k2) c
Proof
  full_simp_tac(srw_ss())[shift_interfer_def,shift_seq_def,ADD_ASSOC]
QED

Theorem bytes_in_memory_SUBSET:
  !p.
  dm SUBSET dm2 /\ bytes_in_memory p xs m dm ==>
  bytes_in_memory p xs m dm2
Proof
  Induct_on `xs` >>
  fs[bytes_in_memory_def] >>
  rpt strip_tac >>
  fs[SUBSET_DEF]
QED

Theorem bytes_in_memory_DIFF:
!p.
    (dm = dm2 DIFF pcs /\ bytes_in_memory p xs m dm2 /\
    DISJOINT pcs {p + n2w i | i | i < LENGTH xs}) ==>
    bytes_in_memory p xs m dm
Proof
  Induct_on `xs` >>
  gvs[bytes_in_memory_def,DISJOINT_DEF,INTER_DEF,EMPTY_DEF,EXTENSION,DIFF_DEF] >>
  rpt strip_tac
  >- (
    first_x_assum $ drule >>
    rw[] >>
    qexists `p + 1w` >>
    rw[] >>
    fs[]
    >- (
       first_x_assum $ qspec_then `x` assume_tac >>
       rw[addressTheory.word_arith_lemma1] >>
       fs[] >>
       `!i. x = p + (n2w (i + 1:num)) ==> ~(i < LENGTH xs)` by (
          rpt strip_tac >>
          first_x_assum $ qspec_then `i+1` drule >>
          disch_then assume_tac >>
          imp_res_tac LESS_MONO_ADD >>
          first_x_assum $ qspec_then `1` assume_tac >>
          fs[]) >>
       fs[]
    )
    >- (
      first_x_assum $ qspec_then `p` assume_tac >>
      rw[] >>
      first_x_assum $ qspec_then `0` assume_tac >>
      fs[]
    )
  )
  >- (
    last_x_assum $ qspec_then `p + 1w` irule >>
    rw[] >>
    first_x_assum $ qspec_then `x` assume_tac >>
    fs[] >>
    rw[addressTheory.word_arith_lemma1] >>
    fs[] >>
    `!i. x = p + (n2w (i + 1:num)) ==> ~(i < LENGTH xs)` by (
      rpt strip_tac >>
      first_x_assum $ qspec_then `i+1` drule >>
      disch_then assume_tac >>
      imp_res_tac LESS_MONO_ADD >>
      first_x_assum $ qspec_then `1` assume_tac >>
      fs[]) >>
    fs[]
  )
QED

Definition ffi_entry_pcs_disjoint_def:
  ffi_entry_pcs_disjoint mc s1 len =
    DISJOINT (set mc.ffi_entry_pcs) {s1.pc + n2w a | a < len}
End

(* -- the interference-application trace of a machine run -- *)

Datatype:
  interference_app =
      FfiApp num (word8 list) 'state 'state
    | CcApp ('a word) ('a word) 'state 'state
End

Definition is_ffi_app_def[simp]:
  (is_ffi_app (FfiApp index new_bytes ms_pre ms_post) = T) ∧
  (is_ffi_app (CcApp a1 a2 ms_pre ms_post) = F)
End

Definition app_post_def[simp]:
  (app_post (FfiApp index new_bytes ms_pre ms_post) = ms_post) ∧
  (app_post (CcApp a1 a2 ms_pre ms_post) = ms_post)
End

(* clocked clone of evaluate that stops at the first interference
   application (FFI, shared-memory or cache-clear) and returns its data
   together with the continuation configuration and ffi state *)
Definition find_next_interference_def:
  find_next_interference (mc:('b,'a,'c) machine_config) (ffi:'ffi ffi_state) k (ms:'a) =
    if k = 0n then NONE
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
              find_next_interference mc ffi (k - 1) ms2
            else NONE
        else NONE
      else if mc.target.get_pc ms = mc.halt_pc then NONE
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
          SOME (CcApp (mc.target.get_reg ms mc.ptr_reg)
                      (mc.target.get_reg ms mc.len_reg) ms ms1,
                mc with ccache_interfer := new_oracle, ffi)
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => NONE
        | SOME ffi_index =>
            (case EL ffi_index mc.ffi_names of
             | SharedMem op =>
                 (case ALOOKUP mc.mmio_info ffi_index of
                  | NONE => NONE
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
                                        | FFI_final outcome => NONE
                                        | FFI_return new_ffi new_bytes =>
                                            let (ms1,new_oracle)
                                                = apply_oracle mc.ffi_interfer
                                                               (ffi_index,new_bytes,ms) in
                                              SOME (FfiApp ffi_index new_bytes ms ms1,
                                                    mc with ffi_interfer := new_oracle,
                                                    new_ffi))
                                     else NONE))
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
                                        | FFI_final outcome => NONE
                                        | FFI_return new_ffi new_bytes =>
                                            let (ms1,new_oracle)
                                                = apply_oracle mc.ffi_interfer
                                                               (ffi_index,new_bytes,ms) in
                                              SOME (FfiApp ffi_index new_bytes ms ms1,
                                                    mc with ffi_interfer := new_oracle,
                                                    new_ffi))
                                     else NONE))))
             | ExtCall _ =>
                 (case ALOOKUP mc.mmio_info ffi_index of
                  | SOME _ => NONE
                  | NONE =>
                      (case read_ffi_bytearrays mc ms of
                       | (SOME bytes, SOME bytes2) =>
                           (case call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 of
                            | FFI_final outcome => NONE
                            | FFI_return new_ffi new_bytes =>
                                let (ms1,new_oracle)
                                    = apply_oracle mc.ffi_interfer
                                                   (ffi_index,new_bytes,ms) in
                                  SOME (FfiApp ffi_index new_bytes ms ms1,
                                        mc with ffi_interfer := new_oracle,
                                        new_ffi))
                       | _ => NONE)))
End

(* the limit of find_next_interference over all clocks *)
Definition next_interference_def:
  next_interference mc ffi ms =
    some res. ∃k. find_next_interference mc ffi k ms = SOME res
End

(* the sequence of interference applications of a run *)
Definition interference_app_seq_def:
  (interference_app_seq mc ffi ms 0 = next_interference mc ffi ms) ∧
  (interference_app_seq mc ffi ms (SUC n) =
     case next_interference mc ffi ms of
     | NONE => NONE
     | SOME (app,mc',ffi') => interference_app_seq mc' ffi' (app_post app) n)
End

(* number of applications satisfying P among the first n applications *)
Definition interference_count_def:
  (interference_count P mc ffi ms 0 = 0n) ∧
  (interference_count P mc ffi ms (SUC n) =
     interference_count P mc ffi ms n +
     case interference_app_seq mc ffi ms n of
     | SOME (app,mc',ffi') => if P app then 1 else 0
     | NONE => 0)
End

(* position in the application sequence of the k-th application
   satisfying P *)
Definition interference_pos_def:
  interference_pos P mc ffi ms k =
    some n. interference_count P mc ffi ms n = k ∧
            ∃app mc' ffi'.
              interference_app_seq mc ffi ms n = SOME (app,mc',ffi') ∧
              P app
End

(* the lab-level oracle sequences, constructed from the machine run:
   caller-saved register and FP-register residues are read off each
   application's post state; callee-saved (and avoid / out-of-range)
   registers are marked NONE, i.e. preserved *)
Definition target_io_regs_def:
  target_io_regs mc ffi ms k (name:ffiname) r =
    case interference_pos is_ffi_app mc ffi ms k of
    | NONE => NONE
    | SOME n =>
      (case interference_app_seq mc ffi ms n of
       | SOME (FfiApp index new_bytes ms_pre ms_post, mc', ffi') =>
           (if MEM r mc.callee_saved_regs ∨
               ¬(r < mc.target.config.reg_count) ∨
               MEM r mc.target.config.avoid_regs
            then NONE
            else SOME (mc.target.get_reg ms_post r))
       | _ => NONE)
End

Definition target_io_fp_regs_def:
  target_io_fp_regs mc ffi ms k (i:num) =
    case interference_pos is_ffi_app mc ffi ms k of
    | NONE => (0w:word64)
    | SOME n =>
      (case interference_app_seq mc ffi ms n of
       | SOME (FfiApp index new_bytes ms_pre ms_post, mc', ffi') =>
           mc.target.get_fp_reg ms_post i
       | _ => 0w)
End

Definition target_cc_regs_def:
  target_cc_regs mc ffi ms k r =
    case interference_pos (λapp. ¬is_ffi_app app) mc ffi ms k of
    | NONE => NONE
    | SOME n =>
      (case interference_app_seq mc ffi ms n of
       | SOME (CcApp a1 a2 ms_pre ms_post, mc', ffi') =>
           (if MEM r mc.callee_saved_regs ∨ r = mc.ptr_reg ∨
               ¬(r < mc.target.config.reg_count) ∨
               MEM r mc.target.config.avoid_regs
            then NONE
            else SOME (mc.target.get_reg ms_post r))
       | _ => NONE)
End

Definition target_cc_fp_regs_def:
  target_cc_fp_regs mc ffi ms k (i:num) =
    case interference_pos (λapp. ¬is_ffi_app app) mc ffi ms k of
    | NONE => (0w:word64)
    | SOME n =>
      (case interference_app_seq mc ffi ms n of
       | SOME (CcApp a1 a2 ms_pre ms_post, mc', ffi') =>
           mc.target.get_fp_reg ms_post i
       | _ => 0w)
End

Theorem find_next_interference_mono:
  ∀k mc ffi ms res i.
    find_next_interference mc ffi k ms = SOME res ⇒
    find_next_interference mc ffi (k + i) ms = SOME res
Proof
  Induct
  >- simp[Once find_next_interference_def]
  \\ rpt gen_tac
  \\ once_rewrite_tac [find_next_interference_def]
  \\ simp[apply_oracle_def]
  \\ rpt (TOP_CASE_TAC \\ simp[])
  \\ rw[] \\ fs[ADD_CLAUSES]
QED

Theorem find_next_interference_unique:
  find_next_interference mc ffi k1 ms = SOME res1 ∧
  find_next_interference mc ffi k2 ms = SOME res2 ⇒
  res1 = res2
Proof
  rw[]
  \\ ‘find_next_interference mc ffi (k1 + k2) ms = SOME res1’
       by simp[find_next_interference_mono]
  \\ ‘find_next_interference mc ffi (k2 + k1) ms = SOME res2’
       by simp[find_next_interference_mono]
  \\ ‘k2 + k1 = k1 + k2’ by decide_tac
  \\ gvs[]
QED

Theorem next_interference_intro:
  find_next_interference mc ffi k ms = SOME res ⇒
  next_interference mc ffi ms = SOME res
Proof
  rw[next_interference_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[]
  \\ metis_tac[find_next_interference_unique]
QED

Theorem next_interference_shift:
  (∀k. find_next_interference mc1 ffi1 (k + l) ms1 =
       find_next_interference mc2 ffi2 k ms2) ⇒
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2
Proof
  rw[next_interference_def]
  \\ AP_TERM_TAC
  \\ simp[FUN_EQ_THM]
  \\ metis_tac[find_next_interference_mono]
QED

Theorem find_next_interference_const:
  ∀k mc ffi ms app mc' ffi'.
    find_next_interference mc ffi k ms = SOME (app,mc',ffi') ⇒
    mc'.target = mc.target ∧
    mc'.callee_saved_regs = mc.callee_saved_regs ∧
    mc'.ptr_reg = mc.ptr_reg
Proof
  Induct
  >- simp[Once find_next_interference_def]
  \\ rpt gen_tac
  \\ once_rewrite_tac [find_next_interference_def]
  \\ simp[apply_oracle_def]
  \\ rpt (TOP_CASE_TAC \\ simp[])
  \\ rw[] \\ res_tac \\ simp[]
QED

Theorem next_interference_const:
  next_interference mc ffi ms = SOME (app,mc',ffi') ⇒
  mc'.target = mc.target ∧
  mc'.callee_saved_regs = mc.callee_saved_regs ∧
  mc'.ptr_reg = mc.ptr_reg
Proof
  rw[next_interference_def]
  \\ qpat_x_assum ‘_ = SOME _’ mp_tac
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[]
  \\ metis_tac[find_next_interference_const]
QED

Theorem interference_app_seq_EQ:
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ⇒
  ∀n. interference_app_seq mc1 ffi1 ms1 n =
      interference_app_seq mc2 ffi2 ms2 n
Proof
  strip_tac \\ Cases \\ simp[interference_app_seq_def]
QED

Theorem interference_app_seq_tail:
  next_interference mc ffi ms = SOME (app,mc',ffi') ⇒
  ∀n. interference_app_seq mc ffi ms (SUC n) =
      interference_app_seq mc' ffi' (app_post app) n
Proof
  simp[interference_app_seq_def]
QED

Theorem interference_count_mono:
  ∀i m. interference_count P mc ffi ms m ≤
        interference_count P mc ffi ms (m + i)
Proof
  Induct >- simp[]
  \\ gen_tac
  \\ first_x_assum (qspec_then ‘m’ assume_tac)
  \\ fs[ADD_CLAUSES, interference_count_def]
  \\ every_case_tac \\ fs[]
  \\ qpat_x_assum ‘_ ≤ _’ mp_tac \\ decide_tac
QED

Theorem interference_count_lt:
  interference_app_seq mc ffi ms n = SOME (app,mc',ffi') ∧ P app ∧ n < n2 ⇒
  interference_count P mc ffi ms n < interference_count P mc ffi ms n2
Proof
  rw[]
  \\ ‘interference_count P mc ffi ms (SUC n) =
      interference_count P mc ffi ms n + 1’ by simp[interference_count_def]
  \\ ‘∃i. n2 = SUC n + i’ by (qexists_tac ‘n2 - SUC n’ \\ decide_tac)
  \\ ‘interference_count P mc ffi ms (SUC n) ≤
      interference_count P mc ffi ms (SUC n + i)’
        by simp[interference_count_mono]
  \\ gvs[]
QED

Theorem interference_pos_unique:
  interference_app_seq mc ffi ms n1 = SOME (app1,mc1',ffi1') ∧ P app1 ∧
  interference_app_seq mc ffi ms n2 = SOME (app2,mc2',ffi2') ∧ P app2 ∧
  interference_count P mc ffi ms n1 = interference_count P mc ffi ms n2 ⇒
  n1 = n2
Proof
  rpt strip_tac
  \\ CCONTR_TAC
  \\ ‘n1 < n2 ∨ n2 < n1’ by decide_tac
  \\ metis_tac[interference_count_lt, prim_recTheory.LESS_REFL]
QED

Theorem interference_count_tail:
  next_interference mc ffi ms = SOME (app0,mcc,ffic) ⇒
  ∀n. interference_count P mc ffi ms (SUC n) =
      (if P app0 then 1 else 0) +
      interference_count P mcc ffic (app_post app0) n
Proof
  strip_tac \\ Induct
  >- simp[interference_count_def, interference_app_seq_def]
  \\ simp[interference_count_def]
  \\ drule interference_app_seq_tail \\ simp[]
QED

Theorem interference_pos_head:
  next_interference mc ffi ms = SOME (app0,mcc,ffic) ∧ P app0 ⇒
  interference_pos P mc ffi ms 0 = SOME 0
Proof
  rw[interference_pos_def]
  \\ DEEP_INTRO_TAC some_intro
  \\ rw[]
  >- (rename1 ‘interference_count P mc ffi ms n = 0’
      \\ CCONTR_TAC
      \\ ‘interference_app_seq mc ffi ms 0 = SOME (app0,mcc,ffic)’
           by simp[interference_app_seq_def]
      \\ ‘0 < n’ by fs[]
      \\ drule_all interference_count_lt
      \\ simp[interference_count_def])
  \\ qexists_tac ‘0’
  \\ simp[interference_count_def, interference_app_seq_def]
  \\ metis_tac[]
QED

Theorem interference_pos_tail_hit:
  next_interference mc ffi ms = SOME (app0,mcc,ffic) ∧ P app0 ⇒
  interference_pos P mc ffi ms (SUC k) =
  OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k)
Proof
  strip_tac
  \\ ‘∀n. interference_app_seq mc ffi ms (SUC n) =
          interference_app_seq mcc ffic (app_post app0) n’
       by simp[interference_app_seq_tail]
  \\ ‘∀n. interference_count P mc ffi ms (SUC n) =
          1 + interference_count P mcc ffic (app_post app0) n’
       by (drule interference_count_tail \\ simp[])
  \\ simp[interference_pos_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  >- (rename1 ‘interference_app_seq mc ffi ms n = SOME _’
      \\ Cases_on ‘n’
      >- fs[interference_count_def]
      \\ rename1 ‘interference_app_seq mc ffi ms (SUC m) = SOME _’
      \\ gvs[]
      \\ ‘interference_count P mcc ffic (app_post app0) m = k’ by fs[]
      \\ DEEP_INTRO_TAC some_intro \\ rw[]
      >- metis_tac[interference_pos_unique]
      \\ metis_tac[])
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ rename1 ‘interference_app_seq mcc ffic (app_post app0) m = SOME _’
  \\ first_x_assum (qspec_then ‘SUC m’ mp_tac)
  \\ simp[]
  \\ metis_tac[]
QED

Theorem interference_pos_tail_miss:
  next_interference mc ffi ms = SOME (app0,mcc,ffic) ∧ ¬P app0 ⇒
  interference_pos P mc ffi ms k =
  OPTION_MAP SUC (interference_pos P mcc ffic (app_post app0) k)
Proof
  strip_tac
  \\ ‘∀n. interference_app_seq mc ffi ms (SUC n) =
          interference_app_seq mcc ffic (app_post app0) n’
       by simp[interference_app_seq_tail]
  \\ ‘∀n. interference_count P mc ffi ms (SUC n) =
          interference_count P mcc ffic (app_post app0) n’
       by (drule interference_count_tail \\ simp[])
  \\ simp[interference_pos_def]
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  >- (rename1 ‘interference_app_seq mc ffi ms n = SOME _’
      \\ Cases_on ‘n’
      >- gvs[interference_app_seq_def]
      \\ rename1 ‘interference_app_seq mc ffi ms (SUC m) = SOME _’
      \\ gvs[]
      \\ DEEP_INTRO_TAC some_intro \\ rw[]
      >- metis_tac[interference_pos_unique]
      \\ metis_tac[])
  \\ DEEP_INTRO_TAC some_intro \\ rw[]
  \\ rename1 ‘interference_app_seq mcc ffic (app_post app0) m = SOME _’
  \\ first_x_assum (qspec_then ‘SUC m’ mp_tac)
  \\ simp[]
  \\ metis_tac[]
QED

Theorem constructed_oracles_ffi_step:
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms_pre ms_post, mc', ffi') ⇒
  target_io_regs mc ffi ms 0 name r =
    (if MEM r mc.callee_saved_regs ∨
        ¬(r < mc.target.config.reg_count) ∨
        MEM r mc.target.config.avoid_regs
     then NONE else SOME (mc.target.get_reg ms_post r)) ∧
  target_io_fp_regs mc ffi ms 0 i = mc.target.get_fp_reg ms_post i ∧
  target_io_regs mc ffi ms (SUC k) name r =
    target_io_regs mc' ffi' ms_post k name r ∧
  target_io_fp_regs mc ffi ms (SUC k) i =
    target_io_fp_regs mc' ffi' ms_post k i ∧
  target_cc_regs mc ffi ms k r = target_cc_regs mc' ffi' ms_post k r ∧
  target_cc_fp_regs mc ffi ms k i = target_cc_fp_regs mc' ffi' ms_post k i
Proof
  strip_tac
  \\ imp_res_tac next_interference_const
  \\ ‘interference_pos is_ffi_app mc ffi ms 0 = SOME 0’
       by (drule interference_pos_head \\ simp[])
  \\ ‘∀k. interference_pos is_ffi_app mc ffi ms (SUC k) =
          OPTION_MAP SUC (interference_pos is_ffi_app mc' ffi' ms_post k)’
       by (drule interference_pos_tail_hit \\ simp[])
  \\ ‘∀k. interference_pos (λapp. ¬is_ffi_app app) mc ffi ms k =
          OPTION_MAP SUC
            (interference_pos (λapp. ¬is_ffi_app app) mc' ffi' ms_post k)’
       by (drule interference_pos_tail_miss \\ simp[])
  \\ ‘∀n. interference_app_seq mc ffi ms (SUC n) =
          interference_app_seq mc' ffi' ms_post n’
       by (drule interference_app_seq_tail \\ simp[])
  \\ rw[target_io_regs_def, target_io_fp_regs_def, target_cc_regs_def,
        target_cc_fp_regs_def]
  \\ simp[Once interference_app_seq_def]
  \\ rpt (CASE_TAC \\ gvs[])
QED

Theorem constructed_oracles_cc_step:
  next_interference mc ffi ms =
    SOME (CcApp a1 a2 ms_pre ms_post, mc', ffi') ⇒
  target_cc_regs mc ffi ms 0 r =
    (if MEM r mc.callee_saved_regs ∨ r = mc.ptr_reg ∨
        ¬(r < mc.target.config.reg_count) ∨
        MEM r mc.target.config.avoid_regs
     then NONE else SOME (mc.target.get_reg ms_post r)) ∧
  target_cc_fp_regs mc ffi ms 0 i = mc.target.get_fp_reg ms_post i ∧
  target_cc_regs mc ffi ms (SUC k) r = target_cc_regs mc' ffi' ms_post k r ∧
  target_cc_fp_regs mc ffi ms (SUC k) i =
    target_cc_fp_regs mc' ffi' ms_post k i ∧
  target_io_regs mc ffi ms k name r =
    target_io_regs mc' ffi' ms_post k name r ∧
  target_io_fp_regs mc ffi ms k i = target_io_fp_regs mc' ffi' ms_post k i
Proof
  strip_tac
  \\ imp_res_tac next_interference_const
  \\ ‘interference_pos (λapp. ¬is_ffi_app app) mc ffi ms 0 = SOME 0’
       by (drule interference_pos_head \\ simp[])
  \\ ‘∀k. interference_pos (λapp. ¬is_ffi_app app) mc ffi ms (SUC k) =
          OPTION_MAP SUC
            (interference_pos (λapp. ¬is_ffi_app app) mc' ffi' ms_post k)’
       by (drule interference_pos_tail_hit \\ simp[])
  \\ ‘∀k. interference_pos is_ffi_app mc ffi ms k =
          OPTION_MAP SUC (interference_pos is_ffi_app mc' ffi' ms_post k)’
       by (drule interference_pos_tail_miss \\ simp[])
  \\ ‘∀n. interference_app_seq mc ffi ms (SUC n) =
          interference_app_seq mc' ffi' ms_post n’
       by (drule interference_app_seq_tail \\ simp[])
  \\ rw[target_io_regs_def, target_io_fp_regs_def, target_cc_regs_def,
        target_cc_fp_regs_def]
  \\ simp[Once interference_app_seq_def]
  \\ rpt (CASE_TAC \\ gvs[])
QED

Theorem interference_count_EQ:
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ⇒
  ∀n. interference_count P mc1 ffi1 ms1 n =
      interference_count P mc2 ffi2 ms2 n
Proof
  strip_tac \\ Induct
  \\ simp[interference_count_def]
  \\ drule interference_app_seq_EQ \\ simp[]
QED

Theorem constructed_oracles_EQ:
  next_interference mc1 ffi1 ms1 = next_interference mc2 ffi2 ms2 ∧
  mc1.target = mc2.target ∧
  mc1.callee_saved_regs = mc2.callee_saved_regs ∧
  mc1.ptr_reg = mc2.ptr_reg ⇒
  target_io_regs mc1 ffi1 ms1 = target_io_regs mc2 ffi2 ms2 ∧
  target_io_fp_regs mc1 ffi1 ms1 = target_io_fp_regs mc2 ffi2 ms2 ∧
  target_cc_regs mc1 ffi1 ms1 = target_cc_regs mc2 ffi2 ms2 ∧
  target_cc_fp_regs mc1 ffi1 ms1 = target_cc_fp_regs mc2 ffi2 ms2
Proof
  strip_tac
  \\ ‘∀n. interference_app_seq mc1 ffi1 ms1 n =
          interference_app_seq mc2 ffi2 ms2 n’
       by simp[interference_app_seq_EQ]
  \\ ‘∀P n. interference_count P mc1 ffi1 ms1 n =
            interference_count P mc2 ffi2 ms2 n’
       by simp[interference_count_EQ]
  \\ ‘∀P k. interference_pos P mc1 ffi1 ms1 k =
            interference_pos P mc2 ffi2 ms2 k’
       by (rw[interference_pos_def] \\ AP_TERM_TAC \\ simp[FUN_EQ_THM])
  \\ rw[FUN_EQ_THM, target_io_regs_def, target_io_fp_regs_def,
        target_cc_regs_def, target_cc_fp_regs_def]
  \\ rpt (CASE_TAC \\ gvs[])
QED

Theorem next_interference_ExtCall:
  mc.target.get_pc ms ∉ mc.prog_addresses DIFF set mc.ffi_entry_pcs ∧
  mc.target.get_pc ms ≠ mc.halt_pc ∧
  mc.target.get_pc ms ≠ mc.ccache_pc ∧
  find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME index ∧
  EL index mc.ffi_names = ExtCall name ∧
  ALOOKUP mc.mmio_info index = NONE ∧
  read_ffi_bytearrays mc ms = (SOME bytes, SOME bytes2) ∧
  call_FFI ffi (ExtCall name) bytes bytes2 = FFI_return new_ffi new_bytes ⇒
  next_interference mc ffi ms =
    SOME (FfiApp index new_bytes ms (mc.ffi_interfer 0 (index,new_bytes,ms)),
          mc with ffi_interfer := shift_seq 1 mc.ffi_interfer,
          new_ffi)
Proof
  rw[]
  \\ irule next_interference_intro
  \\ qexists_tac ‘1’
  \\ simp[Once find_next_interference_def, apply_oracle_def]
QED

Theorem next_interference_ccache:
  mc.target.get_pc ms ∉ mc.prog_addresses DIFF set mc.ffi_entry_pcs ∧
  mc.target.get_pc ms ≠ mc.halt_pc ∧
  mc.target.get_pc ms = mc.ccache_pc ⇒
  next_interference mc ffi ms =
    SOME (CcApp (mc.target.get_reg ms mc.ptr_reg)
                (mc.target.get_reg ms mc.len_reg) ms
                (mc.ccache_interfer 0
                   (mc.target.get_reg ms mc.ptr_reg,
                    mc.target.get_reg ms mc.len_reg, ms)),
          mc with ccache_interfer := shift_seq 1 mc.ccache_interfer,
          ffi)
Proof
  rw[]
  \\ irule next_interference_intro
  \\ qexists_tac ‘1’
  \\ simp[Once find_next_interference_def, apply_oracle_def]
QED

Theorem evaluate_EQ_evaluate_lemma:
  !n ms1 c.
      c.target.get_pc ms1 IN (c.prog_addresses DIFF (set c.ffi_entry_pcs)) /\
      c.target.state_ok ms1 /\
      (c.prog_addresses = dm) ∧
      interference_ok c.next_interfer (c.target.proj dm) /\
      (!s ms. target_state_rel c.target s ms ==> c.target.state_ok ms) /\
      (!ms1 ms2. (c.target.proj dm ms1 = c.target.proj dm ms2) ==>
           (c.target.state_ok ms1 = c.target.state_ok ms2) /\
           (c.target.get_pc ms1 = c.target.get_pc ms2) /\
           (∀a. a ∈ dm ⇒ c.target.get_byte ms1 a = c.target.get_byte ms2 a)) /\
      (!env.
         interference_ok env (c.target.proj dm) ==>
         asserts n (\k s. env k (c.target.next s)) ms1
           (\ms'. c.target.state_ok ms' /\
                  (∀pc. pc ∈ all_pcs (LENGTH (c.target.config.encode i)) init_pc 0 ⇒
                   c.target.get_byte ms' pc = c.target.get_byte ms1 pc) /\
                  c.target.get_pc ms' ∈
                    all_pcs (LENGTH (c.target.config.encode i)) init_pc c.target.config.code_alignment)
           (\ms'. target_state_rel c.target s2 ms')) /\
      (asserts2 (n + 1) (λk. c.next_interfer (n + 1 - k)) c.target.next ms1
        (λms1 ms2. ∀x. x ∉ dm ⇒ c.target.get_byte ms1 x = c.target.get_byte ms2 x)) ∧
      (∃k.
        c.target.get_pc ms1 = init_pc + n2w (k * (2 ** c.target.config.code_alignment)) /\
        k * (2 ** c.target.config.code_alignment) < LENGTH (c.target.config.encode i) /\
        bytes_in_memory init_pc (c.target.config.encode i)
          (c.target.get_byte ms1) (c.prog_addresses DIFF set c.ffi_entry_pcs)) ==>
      ?ms2.
        !k. (evaluate c io (k + (n + 1)) ms1 =
             evaluate (shift_interfer (n+1) c) io k ms2) /\
            (find_next_interference c io (k + (n + 1)) ms1 =
             find_next_interference (shift_interfer (n+1) c) io k ms2) /\
            target_state_rel c.target s2 ms2
Proof
  Induct THEN1
   (full_simp_tac(srw_ss())[] \\ REPEAT STRIP_TAC
    \\ full_simp_tac(srw_ss())[asserts_def,LET_DEF]
    \\ SIMP_TAC std_ss [Once evaluate_def, Once find_next_interference_def]
    \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPEC `K (c.next_interfer 0)`)
    \\ full_simp_tac(srw_ss())[interference_ok_def] \\ RES_TAC \\ full_simp_tac(srw_ss())[]
    \\ REPEAT STRIP_TAC \\ RES_TAC \\ full_simp_tac(srw_ss())[shift_interfer_def,apply_oracle_def]
    \\ reverse TOP_CASE_TAC
    >- (
      `F` suffices_by fs[]
      \\ pop_assum mp_tac
      \\ fs[encoded_bytes_in_mem_def]
      \\ asm_exists_tac
      \\ qmatch_goalsub_abbrev_tac`DROP m ls`
      \\ qmatch_goalsub_abbrev_tac`bytes_in_memory _ _ mm dm`
      \\ Q.ISPECL_THEN[`TAKE m ls`,`DROP m ls`,`init_pc`,`mm`,`dm`]mp_tac bytes_in_memory_APPEND
      \\ rfs[]
      \\ metis_tac[DIFF_SUBSET,bytes_in_memory_SUBSET])
    \\ reverse TOP_CASE_TAC
    >- (
      `F` suffices_by fs[]
      \\ pop_assum mp_tac
      \\ fs[Once asserts2_def]
      \\ METIS_TAC[] )
    \\ METIS_TAC [])
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[arithmeticTheory.ADD_CLAUSES]
  \\ SIMP_TAC std_ss [Once evaluate_def, Once find_next_interference_def]
  \\ full_simp_tac(srw_ss())[ADD1] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Q.PAT_ASSUM `!i. bbb`(qspec_then`λi. c.next_interfer 0`mp_tac)
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def])
  \\ full_simp_tac(srw_ss())[]
  \\ SIMP_TAC bool_ss [GSYM ADD1,asserts_def] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ strip_tac
  \\ `c.target.state_ok (c.target.next ms1)` by METIS_TAC [interference_ok_def]
  \\ full_simp_tac(srw_ss())[]
  \\ Q.PAT_X_ASSUM `!ms1 c. bbb ==> ?x. bb`
        (MP_TAC o Q.SPECL [`(c.next_interfer 0 (c.target.next ms1))`,
                    `(c with next_interfer := shift_seq 1 c.next_interfer)`])
  \\ MATCH_MP_TAC IMP_IMP \\ STRIP_TAC THEN1
   (full_simp_tac(srw_ss())[]
    \\ conj_tac >- (
      fs[all_pcs_thm,SUBSET_DEF,PULL_EXISTS]
      \\ first_assum(mp_then Any mp_tac (GEN_ALL bytes_in_memory_all_pcs))
      \\ fs[SUBSET_DEF]
      \\ disch_then match_mp_tac
      \\ simp[all_pcs_thm]
      \\ METIS_TAC[])
    \\ conj_tac THEN1 (full_simp_tac(srw_ss())[interference_ok_def,shift_seq_def])
    \\ conj_tac THEN1 (rpt strip_tac \\ RES_TAC)
    \\ conj_tac >- (
      rpt strip_tac
      \\ FIRST_ASSUM (MP_TAC o Q.SPEC
           `\k. if k = SUC n then c.next_interfer 0 else env k`) \\ full_simp_tac(srw_ss())[]
      \\ MATCH_MP_TAC IMP_IMP
      \\ STRIP_TAC THEN1 (full_simp_tac(srw_ss())[interference_ok_def] \\ srw_tac[][])
      \\ simp[GSYM ADD1, asserts_def]
      \\ MATCH_MP_TAC asserts_WEAKEN
      \\ simp_tac(srw_ss())[FUN_EQ_THM]
      \\ rw[])
    \\ conj_tac >-  (
      qhdtm_x_assum`asserts2`mp_tac
      \\ simp[Once asserts2_def, shift_seq_def]
      \\ rw[]
      \\ irule asserts2_change_interfer
      \\ simp[]
      \\ goal_assum(first_assum o mp_then Any mp_tac)
      \\ simp[] )
    \\ `c.target.proj dm (c.next_interfer 0 (c.target.next ms1)) =
        c.target.proj dm (c.target.next ms1)` by fs[interference_ok_def]
    \\ qpat_x_assum`∀ms1 ms2. _ ⇒ _` drule
    \\ strip_tac \\ fs[]
    \\ rfs[all_pcs_thm]
    \\ qmatch_asmsub_rename_tac`x * _ < _`
    \\ qexists_tac`x` \\ simp[]
    \\ irule bytes_in_memory_change_mem
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ qx_gen_tac`j` \\ strip_tac
    \\ first_x_assum(qspec_then`init_pc + n2w j`mp_tac)
    \\ impl_tac
    >- (
      imp_res_tac bytes_in_memory_all_pcs
      \\ first_x_assum(qspec_then`0`mp_tac)
      \\ fs[all_pcs_thm,SUBSET_DEF,PULL_EXISTS] )
    \\ rw[]
    \\ first_x_assum(qspec_then`λi x. x`mp_tac)
    \\ impl_tac >- fs[interference_ok_def]
    \\ strip_tac
    \\ drule asserts_IMP_FOLDR_COUNT_LIST_LESS
    \\ disch_then(qspec_then`0`mp_tac)
    \\ impl_tac >- fs[]
    \\ simp[]
    \\ strip_tac
    \\ first_x_assum (match_mp_tac o GSYM)
    \\ qexists_tac`j`
    \\ simp[] )
  \\ strip_tac \\ fs[]
  \\ qexists_tac`ms2`
  \\ reverse TOP_CASE_TAC
  >- (
    `F` suffices_by fs[]
    \\ pop_assum mp_tac
    \\ simp[encoded_bytes_in_mem_def]
    \\ qexists_tac`i`
    \\ qmatch_assum_abbrev_tac`k * a < LENGTH bs`
    \\ Q.ISPECL_THEN[`TAKE (k * a) bs`,`DROP (k * a) bs`,`init_pc`]mp_tac bytes_in_memory_APPEND
    \\ simp[]
    \\ METIS_TAC[MULT_COMM,bytes_in_memory_SUBSET,DIFF_SUBSET] )
  \\ rw[]
  \\ fs[GSYM shift_interfer_def, shift_interfer_intro,apply_oracle_def]
  \\ fs[GSYM ADD1]
  \\ simp[ADD1]
  \\ TOP_CASE_TAC
  \\ `F` suffices_by fs[]
  \\ pop_assum mp_tac \\ simp[]
  \\ imp_res_tac asserts2_first \\ fs[]
QED

Theorem enc_ok_not_empty[local]:
  enc_ok c /\ asm_ok w c ==> (c.encode w <> [])
Proof
  METIS_TAC [listTheory.LENGTH_NIL,enc_ok_def]
QED

Theorem asm_step_IMP_evaluate_step_find_next:
  !c s1 ms1 io i.
      encoder_correct c.target /\
      (c.prog_addresses = s1.mem_domain) /\
      ffi_entry_pcs_disjoint c s1 (LENGTH $ c.target.config.encode i) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      asm_step c.target.config s1 i
        (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1) /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2. !k. (evaluate c io (k + l) ms1 =
                   evaluate (shift_interfer l c) io k ms2) /\
                  (find_next_interference c io (k + l) ms1 =
                   find_next_interference (shift_interfer l c) io k ms2) /\
                  target_state_rel c.target
                    (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1)
                    ms2 /\ l <> 0
Proof
  fs[encoder_correct_def,target_ok_def,LET_DEF,ffi_entry_pcs_disjoint_def]
  \\ rw[]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ qexists_tac`n+1` \\ fs[]
  \\ MATCH_MP_TAC (GEN_ALL evaluate_EQ_evaluate_lemma)
  \\ qexists_tac`s1.pc`
  \\ qexists_tac`i`
  \\ Q.EXISTS_TAC `s1.mem_domain`
  \\ fs[]
  \\ conj_tac
  >- (
    fs[asm_step_def]
    \\ fs[target_state_rel_def]
    \\ imp_res_tac bytes_in_memory_all_pcs
    \\ fs[SUBSET_DEF,all_pcs_thm,PULL_EXISTS]
    \\ conj_tac >- (
      first_x_assum(qspec_then`1`mp_tac)
      \\ simp[]
      \\ disch_then(qspec_then`0`mp_tac)
      \\ simp[]
      \\ disch_then irule
      \\ Cases_on`c.target.config.encode i` \\ fs[]
      \\ pop_assum mp_tac \\ simp[]
      \\ match_mp_tac enc_ok_not_empty
      \\ fs[] )
    >- (
      fs[DISJOINT_DEF,INTER_DEF,EXTENSION,EMPTY_DEF]
      \\ qpat_x_assum `!x. ~(MEM x c.ffi_entry_pcs) \/ _` $ qspec_then `s1.pc`
        assume_tac
      \\ fs[]
      \\ first_x_assum $ qspec_then `0` assume_tac
      \\ gvs[]
      \\ drule enc_ok_not_empty
      \\ strip_tac
      \\ first_x_assum $ qspec_then `i` drule
      \\ fs[]
    ))
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- METIS_TAC[]
  \\ conj_tac >- (
    ntac 2 strip_tac
    \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`\k. env (n - k)`])
    \\ simp[]
    \\ impl_tac
    >- fs[interference_ok_def]
    \\ disch_then(mp_tac o CONJUNCT1)
    \\ match_mp_tac asserts_WEAKEN
    \\ simp[] )
  \\ conj_tac >- (
    FIRST_X_ASSUM (MP_TAC o Q.SPECL [`c.next_interfer`])
    \\ impl_tac >- fs[interference_ok_def]
    \\ disch_then(MATCH_ACCEPT_TAC o CONJUNCT2) )
  \\ qexists_tac`0`
  \\ conj_tac >- fs[target_state_rel_def]
  \\ conj_tac >- (
    CCONTR_TAC \\ fs[]
    \\ pop_assum mp_tac
    \\ simp[]
    \\ match_mp_tac enc_ok_not_empty
    \\ fs[asm_step_def] )
  \\ fs[asm_step_def]
  \\ irule bytes_in_memory_change_mem
  \\ qexists `s1.mem`
  \\ conj_tac >- (
    fs[target_state_rel_def]
    \\ rw[]
    \\ first_x_assum (irule o GSYM)
    \\ drule (GEN_ALL bytes_in_memory_all_pcs)
    \\ simp[SUBSET_DEF, all_pcs_thm, PULL_EXISTS]
    \\ disch_then(qspec_then`0`mp_tac) \\ simp[]
  )
  >- (
    irule bytes_in_memory_DIFF
    \\ qexistsl [`s1.mem_domain`, `set c.ffi_entry_pcs`]
    \\ gvs[]
  )
QED

Theorem asm_step_IMP_evaluate_step:
  !c s1 ms1 io i.
      encoder_correct c.target /\
      (c.prog_addresses = s1.mem_domain) /\
      ffi_entry_pcs_disjoint c s1 (LENGTH $ c.target.config.encode i) /\
      interference_ok c.next_interfer (c.target.proj s1.mem_domain) /\
      asm_step c.target.config s1 i
        (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1) /\
      target_state_rel c.target (s1:'a asm_state) (ms1:'state) ==>
      ?l ms2.
        (!k. evaluate c io (k + l) ms1 =
             evaluate (shift_interfer l c) io k ms2) /\
        target_state_rel c.target
          (asm i (s1.pc + n2w (LENGTH (c.target.config.encode i))) s1) ms2 /\
        l <> 0
Proof
  rpt strip_tac
  \\ drule_all asm_step_IMP_evaluate_step_find_next
  \\ disch_then (qspec_then ‘io’ strip_assume_tac)
  \\ qexistsl_tac [‘l’,‘ms2’]
  \\ metis_tac[]
QED

(* basic properties *)

Theorem evaluate_add_clock:
   ∀mc_conf ffi k ms k1 r ms1 st1.
    evaluate mc_conf ffi k ms = (r,ms1,st1) /\ r <> TimeOut ==>
    evaluate mc_conf ffi (k + k1) ms = (r,ms1,st1)
Proof
  ho_match_mp_tac evaluate_ind >> srw_tac[][] >>
  qhdtm_x_assum`evaluate` mp_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  simp[Once evaluate_def,SimpR``$==>``] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[apply_oracle_def] >- (
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
    first_x_assum(qspec_then`k1`mp_tac) >> simp[] ) >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> fs[] \\
  rpt (TOP_CASE_TAC \\ fs[])
QED

Theorem evaluate_io_events_mono:
   ∀mc_conf ffi k ms.
     ffi.io_events ≼ (SND(SND(evaluate mc_conf ffi k ms))).io_events
Proof
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  simp[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  qabbrev_tac `pc_cond = (mc_conf.target.get_pc ms ∈ mc_conf.prog_addresses ∧
                          (¬MEM (mc_conf.target.get_pc ms) mc_conf.ffi_entry_pcs))` >>
  IF_CASES_TAC >> fs[apply_oracle_def] >- (
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  IF_CASES_TAC >> fs[] >>
  TOP_CASE_TAC >> fs[] >>
  IF_CASES_TAC >> fs[ELIM_UNCURRY] \\
  Cases_on `(mc_conf.mmio_info x)` \\
  PairCases_on `r` \\
  rpt (TOP_CASE_TAC >> fs[])) \\
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[ELIM_UNCURRY]
  >- (unabbrev_all_tac >> fs[]) >>
  rpt (TOP_CASE_TAC >> fs[]) >>
  gvs[call_FFI_def,bool_case_eq] \\
  rpt (FULL_CASE_TAC >> gvs[]) >>
  irule IS_PREFIX_TRANS>>
  first_assum $ irule_at Any>>fs[IS_PREFIX_APPEND]
QED

Theorem evaluate_add_clock_io_events_mono:
   ∀mc_conf ffi k ms k'.
   k ≤ k' ⇒
   (SND(SND(evaluate mc_conf ffi k ms))).io_events ≼
   (SND(SND(evaluate mc_conf ffi k' ms))).io_events
Proof
  ho_match_mp_tac evaluate_ind >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  simp_tac(srw_ss())[Once evaluate_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[]
  >- METIS_TAC[evaluate_io_events_mono] >>
  `k <= k' + 1` by decide_tac >>
  rpt (TOP_CASE_TAC >> fs[apply_oracle_def]) >>
  res_tac >>
  CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once evaluate_def])) >>
  fs [apply_oracle_def]
  >- (
    TOP_CASE_TAC >> fs[] >>
    METIS_TAC[evaluate_io_events_mono]
  ) >>
  namedCases_on `mc_conf.mmio_info x` ["r0 r1 r2 r3"] >>
  gvs[] >>
  rpt (TOP_CASE_TAC >> fs[])
QED

Theorem machine_sem_total:
   ∃b. machine_sem mc st ms b
Proof
  Cases_on`∃k t. FST (evaluate mc st k ms) = Halt t`
  >- (
    fs[]
    \\ qexists_tac`Terminate t (SND(SND(evaluate mc st k ms))).io_events`
    \\ simp[targetSemTheory.machine_sem_def]
    \\ Cases_on`evaluate mc st k ms`
    \\ qexists_tac`k` \\ fs[]
    \\ Cases_on`r` \\ fs[] )
  \\ Cases_on`∃k. FST (evaluate mc st k ms) = Error`
  >- ( qexists_tac`Fail` \\ simp[targetSemTheory.machine_sem_def] )
  \\ qexists_tac`Diverge (lprefix_lub$build_lprefix_lub (IMAGE (λk. fromList (SND(SND(evaluate mc st k ms))).io_events) UNIV))`
  \\ simp[targetSemTheory.machine_sem_def]
  \\ conj_tac
  >- (
    rw[]
    \\ Cases_on`evaluate mc st k ms`
    \\ fs[GSYM EXISTS_PROD]
    \\ metis_tac[targetSemTheory.machine_result_nchotomy, FST] )
  \\ irule build_lprefix_lub_thm
  \\ simp[IMAGE_COMPOSE, GSYM o_DEF]
  \\ irule prefix_chain_lprefix_chain
  \\ simp[prefix_chain_def, PULL_EXISTS]
  \\ qx_genl_tac[`k1`,`k2`]
  \\ metis_tac[LESS_EQ_CASES,evaluate_add_clock_io_events_mono]
QED

Theorem machine_sem_unique:
  machine_sem mc ffi ms b1 ∧ machine_sem mc ffi ms b2 ⇒ b1 = b2
Proof
  rw[DefnBase.one_line_ify NONE machine_sem_def] >>
  Cases_on `b1` >> gvs[] >> Cases_on `b2` >> gvs[]
  >- imp_res_tac unique_lprefix_lub
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (
    Cases_on `k < k'` >> gvs[LESS_OR_EQ, NOT_LESS] >>
    imp_res_tac LESS_ADD >> gvs[] >> imp_res_tac evaluate_add_clock >> gvs[]
    )
  >- (
    qmatch_asmsub_abbrev_tac `FST ev = Error` >> PairCases_on `ev` >> gvs[] >>
    Cases_on `k < k'` >> gvs[LESS_OR_EQ, NOT_LESS] >>
    imp_res_tac LESS_ADD >> gvs[] >> imp_res_tac evaluate_add_clock >> gvs[]
    )
  >- (last_x_assum $ qspec_then `k` assume_tac >> gvs[])
  >- (
    qmatch_asmsub_abbrev_tac `FST ev = Error` >> PairCases_on `ev` >> gvs[] >>
    Cases_on `k < k'` >> gvs[LESS_OR_EQ, NOT_LESS] >>
    imp_res_tac LESS_ADD >> gvs[] >> imp_res_tac evaluate_add_clock >> gvs[]
    )
QED

Theorem read_ffi_bytearray_IMP_SUBSET_prog_addresses:
   (read_ffi_bytearray mc a l ms = SOME bytes) ==>
    all_words (mc.target.get_reg ms a) (LENGTH bytes) SUBSET
      mc.prog_addresses
Proof
  fs [targetSemTheory.read_ffi_bytearray_def]
  \\ qspec_tac (`mc.target.get_reg ms a`,`x`)
  \\ qspec_tac (`(w2n (mc.target.get_reg ms l))`,`n`)
  \\ qspec_tac (`bytes`,`res`)
  \\ Induct_on `n` \\ fs [read_bytearray_def,all_words_def]
  \\ rw [] \\ fs[option_case_eq] \\ rveq \\ fs []
  \\ fs [all_words_def]
QED

Theorem encoder_correct_asm_step_target_state_rel:
   encoder_correct t ∧
   target_state_rel t s1 ms ∧
   asm_step t.config s1 i s2
   ⇒
   ∃n.
   target_state_rel t s2 (FUNPOW t.next n ms) ∧
   (∀j. j < n ⇒
     (∀pc. pc ∈ all_pcs (LENGTH (t.config.encode i)) s1.pc 0 ⇒
             (t.get_byte (FUNPOW t.next j ms) pc = t.get_byte ms pc)) ∧
     (t.get_pc (FUNPOW t.next j ms) ∈
       all_pcs (LENGTH (t.config.encode i)) s1.pc t.config.code_alignment) ∧
     (t.state_ok (FUNPOW t.next j ms))) ∧
   (∀j x. j ≤ n ∧ x ∉ s1.mem_domain ⇒ (t.get_byte (FUNPOW t.next j ms) x = t.get_byte ms x))
Proof
  rw[asmPropsTheory.encoder_correct_def]
  \\ first_x_assum drule
  \\ disch_then drule
  \\ strip_tac
  \\ first_x_assum(qspec_then`K I`mp_tac)
  \\ impl_tac >- ( EVAL_TAC \\ rw[] )
  \\ srw_tac[ETA_ss][]
  \\ imp_res_tac asmPropsTheory.asserts_IMP_FOLDR_COUNT_LIST
  \\ fs[FOLDR_FUNPOW, LENGTH_COUNT_LIST]
  \\ qexists_tac`SUC n`
  \\ simp[FUNPOW]
  \\ simp[GSYM FORALL_AND_THM]
  \\ gen_tac
  \\ Cases_on`j` \\ fs[]
  >- (
    fs[asmSemTheory.asm_step_def, asmPropsTheory.target_state_rel_def]
    \\ `t.config.encode i <> []`
    by ( fs[asmPropsTheory.target_ok_def, asmPropsTheory.enc_ok_def] )
    \\ Cases_on`t.config.encode i` \\ fs[bytes_in_memory_def]
    \\ fs[asmPropsTheory.all_pcs_thm]
    \\ qexists_tac`0` \\ fs[])
  \\ conj_tac
  >- (
    strip_tac
    \\ drule asmPropsTheory.asserts_IMP_FOLDR_COUNT_LIST_LESS
    \\ disch_then drule
    \\ simp[FOLDR_FUNPOW] )
  \\ ntac 2 strip_tac
  \\ drule asmPropsTheory.asserts2_every
  \\ strip_tac
  \\ qmatch_goalsub_rename_tac`SUC m`
  \\ qho_match_abbrev_tac`P ms (FUNPOW t.next (SUC m) ms)`
  \\ irule FUNPOW_refl_trans_chain
  \\ fs[ADD1,Abbr`P`]
  \\ simp[reflexive_def,transitive_def]
QED

Theorem encoder_correct_RTC_asm_step_target_state_rel:
   encoder_correct t ∧
   target_state_rel t s1 ms ∧
   RTC (λs1 s2. ∃i. asm_step t.config s1 i s2) s1 s2
   ⇒
   ∃n. target_state_rel t s2 (FUNPOW t.next n ms)
Proof
  strip_tac
  \\ first_assum(mp_then (Pat`RTC`) mp_tac (GEN_ALL RTC_lifts_invariants))
  \\ disch_then ho_match_mp_tac
  \\ reverse conj_tac
  >- ( qexists_tac`0` \\ rw[] )
  \\ rw[]
  \\ drule (GEN_ALL encoder_correct_asm_step_target_state_rel)
  \\ disch_then drule
  \\ disch_then drule
  \\ rw[GSYM FUNPOW_ADD]
  \\ asm_exists_tac \\ rw[]
QED

(* -- interface lemmas for the interference contracts -- *)

Theorem ffi_interfer_ok_post_ffi_asm:
  ffi_interfer_ok pc mc_conf ∧
  index < LENGTH mc_conf.ffi_names ∧
  mmio_pcs_min_index mc_conf.ffi_names = SOME i ∧
  index < i ∧
  mc_conf.prog_addresses = t1.mem_domain ∧
  read_ffi_bytearrays mc_conf ms2 = (SOME bytes, SOME bytes2) ∧
  LENGTH new_bytes = LENGTH bytes2 ∧
  (EL index mc_conf.ffi_names = ExtCall «» ⇒ new_bytes = bytes2) ∧
  target_state_rel mc_conf.target
    (t1 with pc := -n2w ((3 + index) * ffi_offset) + pc) ms2 ∧
  aligned mc_conf.target.config.code_alignment
    (t1.regs (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n))
  ⇒
  target_state_rel mc_conf.target
    (post_ffi_asm mc_conf t1 new_bytes
       (mc_conf.ffi_interfer k (index,new_bytes,ms2)))
    (mc_conf.ffi_interfer k (index,new_bytes,ms2))
Proof
  rw[ffi_interfer_ok_def]
  \\ first_x_assum (qspecl_then
       [‘ms2’,‘k’,‘index’,‘new_bytes’,‘t1’,‘bytes’,‘bytes2’,‘i’] mp_tac)
  \\ simp[]
  \\ strip_tac
  \\ gvs[target_state_rel_def, post_ffi_asm_def]
  \\ rw[] \\ gvs[]
QED

Theorem ccache_interfer_ok_post_ccache_asm:
  ccache_interfer_ok pc mc_conf ∧
  target_state_rel mc_conf.target
    (t1 with pc := -n2w (2 * ffi_offset) + pc) ms2 ∧
  aligned mc_conf.target.config.code_alignment
    (t1.regs (case mc_conf.target.config.link_reg of NONE => 0 | SOME n => n))
  ⇒
  target_state_rel mc_conf.target
    (post_ccache_asm mc_conf t1 (mc_conf.ccache_interfer k (a1,a2,ms2)))
    (mc_conf.ccache_interfer k (a1,a2,ms2))
Proof
  rw[ccache_interfer_ok_def]
  \\ first_x_assum (qspecl_then [‘ms2’,‘t1’,‘k’,‘a1’,‘a2’] mp_tac)
  \\ simp[]
  \\ strip_tac
  \\ gvs[target_state_rel_def, post_ccache_asm_def]
  \\ rw[] \\ gvs[]
QED

(* the old packaged conclusions imply the per-call clauses; used to
   re-discharge verified-environment instantiations (e.g. ag32) *)

Theorem target_state_rel_IMP_ffi_clauses:
  target_state_rel t
    (t1 with <|regs := (λa. get_reg_value
                              (if MEM a cs then NONE else or a)
                              (t1.regs a) I);
               mem := m; pc := p|>) ms' ⇒
  t.state_ok ms' ∧ t.get_pc ms' = p ∧
  (∀a. a ∈ t1.mem_domain ⇒ t.get_byte ms' a = m a) ∧
  (∀r. MEM r cs ∧ r < t.config.reg_count ∧ ¬MEM r t.config.avoid_regs ⇒
       t.get_reg ms' r = t1.regs r)
Proof
  rw[target_state_rel_def]
  \\ first_x_assum (qspec_then ‘r’ mp_tac)
  \\ simp[get_reg_value_def]
QED

Theorem target_state_rel_IMP_ccache_clauses:
  target_state_rel t
    (t1 with <|regs := (r0 =+ t1.regs r0)
                 (λa. get_reg_value (if MEM a cs then NONE else or a)
                        (t1.regs a) I);
               pc := p|>) ms' ⇒
  t.state_ok ms' ∧ t.get_pc ms' = p ∧
  (∀a. a ∈ t1.mem_domain ⇒ t.get_byte ms' a = t1.mem a) ∧
  (∀r. (MEM r cs ∨ r = r0) ∧ r < t.config.reg_count ∧
       ¬MEM r t.config.avoid_regs ⇒
       t.get_reg ms' r = t1.regs r)
Proof
  rw[target_state_rel_def]
  \\ first_x_assum (qspec_then ‘r’ mp_tac)
  \\ rw[combinTheory.APPLY_UPDATE_THM, get_reg_value_def]
QED

