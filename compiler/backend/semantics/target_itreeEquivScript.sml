(*
  Theorem expressing `machine_sem` in terms of target itree semantics
*)
Theory target_itreeEquiv
Ancestors
  semanticsProps evaluateProps ffi targetSem targetProps
  target_itreeSem target_itreeProps itree_semantics
  itree_semanticsProps
Libs
  preamble


(*********** evaluate' **********)

Definition evaluate'_def:
  evaluate' (mc:('b,'a,'c) machine_config) (ffi:'ffi ffi_state) (k:num) (ms:'a) =
    if k = 0 then (TimeOut,mc,ms,ffi)
    else
      if mc.target.get_pc ms ∈ mc.prog_addresses DIFF set mc.ffi_entry_pcs then
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
              evaluate' mc ffi (k - 1) ms2
            else
              (Error,mc,ms,ffi)
        else (Error,mc,ms,ffi)
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then Halt Success else Halt Resource_limit_hit,mc,ms,ffi)
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
        let mc = mc with ccache_interfer := new_oracle in
          evaluate' mc ffi (k-1) ms1
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => (Error,mc,ms,ffi)
        | SOME ffi_index =>
            case EL ffi_index mc.ffi_names of
            | SharedMem op =>
                (case ALOOKUP mc.mmio_info ffi_index of
                 | NONE => (Error,mc,ms,ffi)
                 | SOME (nb,a,reg,pc') =>
                     (case op of
                        | MappedRead =>
                            (case a of
                             | Addr r off =>
                                 let ad = mc.target.get_reg ms r + off in
                                   (if (if nb = 0w
                                        then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T)
                                       ∧ (ad IN mc.shared_addresses) /\
                                       is_valid_mapped_read (mc.target.get_pc ms) nb a reg pc'
                                                            mc.target ms mc.prog_addresses
                                    then
                                      (case call_FFI ffi (EL ffi_index mc.ffi_names)
                                                     [nb]
                                                     (word_to_bytes ad F) of
                                       | FFI_final outcome =>
                                           (Halt (FFI_outcome outcome),mc,ms,ffi)
                                       | FFI_return new_ffi new_bytes =>
                                           let (ms1,new_oracle) =
                                               apply_oracle mc.ffi_interfer
                                                            (ffi_index,new_bytes,ms) in
                                             let mc = mc with ffi_interfer := new_oracle in
                                               evaluate' mc new_ffi (k - 1) ms1)
                                    else (Error,mc,ms,ffi)))
                        | MappedWrite =>
                            (case a of
                             | Addr r off =>
                                 let ad = (mc.target.get_reg ms r) + off in
                                   (if (if nb = 0w
                                        then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T)
                                       /\ (ad IN mc.shared_addresses) /\
                                       is_valid_mapped_write (mc.target.get_pc ms) nb a reg pc'
                                                             mc.target ms mc.prog_addresses
                                    then
                                      (case call_FFI ffi (EL ffi_index mc.ffi_names)
                                                     [nb]
                                                     ((let w = mc.target.get_reg ms reg in
                                                         if nb = 0w then word_to_bytes w F
                                                         else word_to_bytes_aux (w2n nb) w F)
                                                      ++ (word_to_bytes ad F)) of
                                       | FFI_final outcome =>
                                           (Halt (FFI_outcome outcome),mc,ms,ffi)
                                       | FFI_return new_ffi new_bytes =>
                                           let (ms1,new_oracle) =
                                               apply_oracle mc.ffi_interfer
                                                            (ffi_index,new_bytes,ms) in
                                             let mc = mc with ffi_interfer := new_oracle in
                                               evaluate' mc new_ffi (k - 1) ms1)
                                    else (Error,mc,ms,ffi)))))
            | ExtCall _ =>
                (case ALOOKUP mc.mmio_info ffi_index of
                 | SOME _ => (Error,mc,ms,ffi)
                 | NONE =>
                     case read_ffi_bytearrays mc ms of
                     | (SOME bytes, SOME bytes2) =>
                         (case call_FFI ffi (EL ffi_index mc.ffi_names) bytes bytes2 of
                          | FFI_final outcome => (Halt (FFI_outcome outcome),mc,ms,ffi)
                          | FFI_return new_ffi new_bytes =>
                              let (ms1,new_oracle) = apply_oracle mc.ffi_interfer
                                                                  (ffi_index,new_bytes,ms) in
                                let mc = mc with ffi_interfer := new_oracle in
                                  evaluate' mc new_ffi (k - 1) ms1)
                     | _ => (Error,mc,ms,ffi))
End

Theorem evaluate'_0[simp]:
  evaluate' mc ffi 0 ms = (TimeOut,mc,ms,ffi)
Proof
  rw[Once evaluate'_def]
QED

Theorem evaluate_evaluate':
  ∀mc ffi k ms. evaluate mc ffi k ms = (λ(a,b,c,d).(a,c,d)) (evaluate' mc ffi k ms)
Proof
  ho_match_mp_tac evaluate_ind >> rw[] >>
  simp[Once evaluate_def, Once evaluate'_def] >>
  rpt (TOP_CASE_TAC >> gvs[apply_oracle_def]) >>
  rpt (pairarg_tac >> gvs[]) >> rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem evaluate'_step:
  evaluate' mc ffi 0 ms = (TimeOut,mc,ms,ffi) ∧
  evaluate' mc ffi (SUC n) ms =
    case evaluate' mc ffi 1 ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' n ms'
    | res => res
Proof
  simp[] >> simp[Once evaluate'_def, SimpRHS] >> simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
  pairarg_tac >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem evaluate'_step_alt:
  evaluate' mc ffi 0 ms = (TimeOut,mc,ms,ffi) ∧
  evaluate' mc ffi (SUC n) ms =
    case evaluate' mc ffi n ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' 1 ms'
    | res => res
Proof
  simp[] >> map_every qid_spec_tac [`ms`,`ffi`,`mc`,`n`] >>
  Induct >- rw[] >> rpt gen_tac >>
  rewrite_tac[evaluate'_step] >>
  qabbrev_tac `ev = evaluate' mc ffi 1 ms` >> PairCases_on `ev` >> gvs[] >>
  TOP_CASE_TAC >> simp[] >> simp[GSYM evaluate'_step]
QED

Theorem evaluate'_add:
  ∀a b.
    evaluate' mc ffi (a + b) ms =
    case evaluate' mc ffi b ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' a ms'
    | res => res
Proof
  Induct >> rw[evaluate'_step, ADD_CLAUSES] >>
  qabbrev_tac `ev = evaluate' mc ffi b ms` >> PairCases_on `ev` >> gvs[] >>
  Cases_on `ev0` >> gvs[] >> simp[GSYM evaluate'_step] >> simp[evaluate'_step_alt]
QED

Theorem evaluate'_add_alt:
  ∀a b.
    evaluate' mc ffi (a + b) ms =
    case evaluate' mc ffi a ms of
    | (TimeOut,mc',ms',ffi') => evaluate' mc' ffi' b ms'
    | res => res
Proof
  once_rewrite_tac[ADD_COMM] >> simp[evaluate'_add]
QED

Theorem evaluate'_io_events_mono:
   ∀mc ffi k ms res mc' ms' ffi'.
    evaluate' mc ffi k ms = (res,mc',ms',ffi') ⇒ io_events_mono ffi ffi'
Proof
  ho_match_mp_tac evaluate'_ind >>
  strip_tac >>
  rw[] >>
  pop_assum mp_tac >> simp[Once evaluate'_def] >>
  rpt (TOP_CASE_TAC >> gvs[apply_oracle_def]) >>
  rw[] >> gvs[] >>
  irule io_events_mono_trans >> goal_assum $ drule_at Any >>
  irule call_FFI_rel_io_events_mono >>
  irule RTC_SUBSET >> simp[call_FFI_rel_def, SF SFY_ss]
QED

Theorem evaluate'_add_clock:
  ∀mc ffi k ms res.
  evaluate' mc ffi k ms = res ∧ FST res ≠ TimeOut
  ⇒ ∀k'. k ≤ k' ⇒ evaluate' mc ffi k' ms = res
Proof
  recInduct evaluate'_ind >> rw[] >>
  qpat_x_assum `FST _ ≠ _` mp_tac >> once_rewrite_tac[evaluate'_def] >>
  rpt (TOP_CASE_TAC >> gvs[apply_oracle_def]) >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem evaluate'_agree:
  evaluate' mc ffi k1 ms = res1 ∧
  evaluate' mc ffi k2 ms = res2 ∧
  FST res1 ≠ TimeOut ∧ FST res2 ≠ TimeOut
  ⇒ res1 = res2
Proof
  rw[] >> wlog_tac `k1 < k2` [`k1`,`k2`] >- gvs[NOT_LESS, LESS_OR_EQ] >>
  Cases_on `evaluate' mc ffi k1 ms` >> Cases_on `evaluate' mc ffi k2 ms` >>
  gvs[] >> PairCases_on `r` >> PairCases_on `r'` >>
  rev_dxrule evaluate'_add_clock >> simp[] >>
  disch_then $ qspec_then `k2` assume_tac >> gvs[]
QED

Theorem evaluate'_remove_clock:
  evaluate' mc ffi k ms = res ∧ FST res = TimeOut ∧ k' ≤ k ⇒
  FST (evaluate' mc ffi k' ms) = TimeOut
Proof
  metis_tac[evaluate'_add_clock, PAIR]
QED

Theorem evaluate'_min:
  ∀k mc ffi ms res.
  evaluate' mc ffi k ms = res ∧ FST res ≠ TimeOut
  ⇒ ∃k'. k' ≤ k ∧ evaluate' mc ffi k' ms = res ∧
         ∀m. m < k' ⇒ ∃mc' ms' ffi'. evaluate' mc ffi m ms = (TimeOut,mc',ms',ffi')
Proof
  Induct >> rw[] >>
  qabbrev_tac `res = evaluate' mc ffi (SUC k) ms` >> PairCases_on `res` >> gvs[] >>

  gvs[evaluate'_step_alt] >>
  Cases_on `evaluate' mc ffi k ms` >> gvs[] >> Cases_on `q` >> gvs[]
  >- (
  first_x_assum $ qspecl_then [`mc`,`ffi`,`ms`] assume_tac >> gvs[] >>
  qexists_tac `k'` >> simp[]
  )
  >- (
  first_x_assum $ qspecl_then [`mc`,`ffi`,`ms`] assume_tac >> gvs[] >>
  qexists_tac `k'` >> simp[]
  ) >>
  PairCases_on `r` >> gvs[] >>
  qexists_tac `SUC k` >> simp[evaluate'_step_alt] >> rw[] >>
  drule evaluate'_remove_clock >> simp[] >>
  disch_then $ qspec_then `m` mp_tac >> simp[] >> metis_tac[PAIR]
QED

Theorem evaluate'_1_ffi_unchanged:
  evaluate' mc (ffi:'ffi ffi_state) 1 ms = (res,mc',ms',ffi') ∧ res ≠ TimeOut
  ⇒ ffi = ffi'
Proof
  simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >>
  rpt (TOP_CASE_TAC >> gvs[]) >>
  rw[] >> gvs[] >>
  pairarg_tac >> gvs[AllCaseEqs()]
QED

Theorem evaluate'_1_ffi_changed:
  evaluate' (mc:('b,'a,'c) machine_config) (ffi:'ffi ffi_state) 1 ms
  = (res,mc',ms',ffi') ∧ ffi' ≠ ffi ⇔
    res = TimeOut ∧
    mc.target.get_pc ms ∉ (mc.prog_addresses DIFF set mc.ffi_entry_pcs) ∧
    mc.target.get_pc ms ≠ mc.halt_pc ∧
    mc.target.get_pc ms ≠ mc.ccache_pc ∧
    mc' = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer ∧
    ∃n ws1 ws2 l.
  find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME n ∧
  (
  (EL n mc.ffi_names = SharedMem MappedRead /\
   ?nb ad r off reg pc'.
          ALOOKUP mc.mmio_info n = SOME (nb, Addr r off,reg,pc') /\
          ad = mc.target.get_reg ms r + off /\
          (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
          ad IN mc.shared_addresses /\
          is_valid_mapped_read (mc.target.get_pc ms) nb (Addr r off) reg
            pc' mc.target ms mc.prog_addresses /\
          ws1 = [nb] /\
          ws2 = word_to_bytes ad F) \/
         (EL n mc.ffi_names = SharedMem MappedWrite /\
         ?nb ad r off reg pc'.
           ALOOKUP mc.mmio_info n = SOME (nb,Addr r off,reg,pc') /\
           ad = mc.target.get_reg ms r + off /\
           (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
           ad IN mc.shared_addresses /\
           is_valid_mapped_write (mc.target.get_pc ms) nb (Addr r off) reg
             pc' mc.target ms mc.prog_addresses /\
           ws1 = [nb] /\
           ws2 = (let w = mc.target.get_reg ms reg in
                      if nb = 0w then word_to_bytes w F
                      else word_to_bytes_aux (w2n nb) w F) ++
                 word_to_bytes ad F) \/
         ((∃s. EL n mc.ffi_names = ExtCall s ∧ s ≠ "") ∧
           ALOOKUP mc.mmio_info n = NONE ∧
          read_ffi_bytearrays mc ms = (SOME ws1,SOME ws2))
      ) ∧
      call_FFI ffi (EL n mc.ffi_names) ws1 ws2 = FFI_return ffi' l ∧
      ms' = mc.ffi_interfer 0 (n,l,ms)
Proof
  simp[Once evaluate'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[apply_oracle_def] >>
  IF_CASES_TAC >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[]) >>
  rpt ( pairarg_tac >> gvs[AllCaseEqs()] ) >>
  eq_tac >> rw[] >>
  gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality] >>
  qpat_x_assum `_ = f.io_events` $ assume_tac o GSYM >> simp[] >>
  Cases_on ‘EL x mc.ffi_names’>>fs[]>>
  rename1 ‘SharedMem s’>>Cases_on ‘s’>>fs[]
QED

Theorem evaluate'_1_ffi_failed:
  evaluate' (mc:('b,'a,'c) machine_config) (ffi:'ffi ffi_state) 1 ms
  = (Halt (FFI_outcome outcome),mc',ms',ffi') ⇔
    mc.target.get_pc ms ∉ (mc.prog_addresses DIFF set mc.ffi_entry_pcs) ∧
    mc.target.get_pc ms ≠ mc.halt_pc ∧
    mc.target.get_pc ms ≠ mc.ccache_pc ∧
    ms = ms' ∧ mc = mc' ∧ ffi = ffi' ∧
    ∃n ws1 ws2 l.
      find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME n ∧
      (
        (EL n mc.ffi_names = SharedMem MappedRead /\
        ?nb ad r off reg pc'.
          ALOOKUP mc.mmio_info n = SOME (nb, Addr r off,reg,pc') /\
          ad = mc.target.get_reg ms r + off /\
          (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
          ad IN mc.shared_addresses /\
          is_valid_mapped_read (mc.target.get_pc ms) nb (Addr r off) reg
            pc' mc.target ms mc.prog_addresses /\
          ws1 = [nb] /\
          ws2 = word_to_bytes ad F) \/
         (EL n mc.ffi_names = SharedMem MappedWrite /\
         ?nb ad r off reg pc'.
           ALOOKUP mc.mmio_info n = SOME (nb,Addr r off,reg,pc') /\
           ad = mc.target.get_reg ms r + off /\
           (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
           ad IN mc.shared_addresses /\
           is_valid_mapped_write (mc.target.get_pc ms) nb (Addr r off) reg
             pc' mc.target ms mc.prog_addresses /\
           ws1 = [nb] /\
           ws2 = (let w = mc.target.get_reg ms reg in
                      if nb = 0w then word_to_bytes w F
                      else word_to_bytes_aux (w2n nb) w F) ++
            word_to_bytes ad F) \/
         ((∃s. EL n mc.ffi_names = ExtCall s /\ s ≠ "") /\
          ALOOKUP mc.mmio_info n = NONE ∧
          read_ffi_bytearrays mc ms = (SOME ws1,SOME ws2))
      ) ∧
      call_FFI ffi (EL n mc.ffi_names) ws1 ws2 = FFI_final outcome
Proof
  simp[Once evaluate'_def] >>
  rpt (TOP_CASE_TAC >> gvs[apply_oracle_def]) >>
  TRY eq_tac >> rw[] >> gvs[call_FFI_def, AllCaseEqs()]>>
  Cases_on ‘EL x mc.ffi_names’>>fs[]>>
  rename1 ‘SharedMem s’>>Cases_on ‘s’>>fs[]
QED


(*********** halt_rel **********)

Definition halt_rel_def:
  halt_rel Termination h = (h = Success) ∧
  halt_rel OutOfMemory h = (h = Resource_limit_hit) ∧
  halt_rel _ _ = F
End

Theorem halt_rel_alt_def[local]:
  halt_rel h Success = (h = Termination) ∧
  halt_rel h Resource_limit_hit = (h = OutOfMemory) ∧
  halt_rel h (FFI_outcome _) = F
Proof
  Cases_on `h` >> rw[halt_rel_def]
QED

Theorem halt_rel_imps[local]:
  halt_rel r h ⇒ r ≠ Error ∧ (∀p out. r ≠ FinalFFI p out)
Proof
  rw[] >> CCONTR_TAC >> gvs[halt_rel_def]
QED


(*********** eval_to' / evaluate' - non-FFI steps **********)

Theorem eval_to'_evaluate'_halt_rel:
  halt_rel r h ⇒ (
  eval_to' k mc ms = (Ret' r,mc',ms') ⇔
  evaluate' mc (ffi :'ffi ffi_state) k ms = (Halt h,mc',ms',ffi))
Proof
  rw[] >> imp_res_tac halt_rel_imps >>
  eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`ffi`,`ms`,`mc`,`k`] >>
    ho_match_mp_tac eval_to'_ind >> rw[] >>
    pop_assum mp_tac >> simp[Once eval_to'_def, Once evaluate'_def] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
    >- (IF_CASES_TAC >> gvs[] >> pairarg_tac >> gvs[] >> IF_CASES_TAC >> gvs[])
    >> (
      IF_CASES_TAC >> gvs[] >- (rw[] >> gvs[halt_rel_def]) >>
      IF_CASES_TAC >> gvs[] >- (pairarg_tac >> gvs[]) >>
      rpt (TOP_CASE_TAC >> gvs[]) >>
      rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
      rpt (TOP_CASE_TAC >> gvs[]) >>
      strip_tac >> gvs[call_FFI_def, apply_oracle_def]
      )
    )>>
  map_every qid_spec_tac [`ms`,`k`,`ffi`,`mc`] >>
  ho_match_mp_tac evaluate'_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once eval_to'_def, Once evaluate'_def] >>
  rpt (TOP_CASE_TAC>>gvs[apply_oracle_def])>>
  TRY (rw[]>>Cases_on ‘r’>>gvs[halt_rel_def]>>NO_TAC)>>
  TRY (strip_tac >>
       gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality]>>
       NO_TAC) >>
  (strip_tac>>fs[]>>
   qsuff_tac `ffi = f`
   >- (strip_tac >> gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality]) >>
   irule io_events_mono_antisym >>
   imp_res_tac evaluate'_io_events_mono >> simp[] >>
   irule call_FFI_rel_io_events_mono >> irule RTC_SUBSET >>
   simp[call_FFI_rel_def, SF SFY_ss])
QED

Theorem eval_to'_evaluate'_error:
  eval_to' k mc ms = (Ret' Error,mc',ms') ⇔
  evaluate' mc (ffi :'ffi ffi_state) k ms = (Error,mc',ms', ffi)
Proof
  eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`ffi`,`ms`,`mc`,`k`] >>
    ho_match_mp_tac eval_to'_ind >> rw[] >>
    pop_assum mp_tac >> simp[Once eval_to'_def, Once evaluate'_def] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
    >- (IF_CASES_TAC >> gvs[] >> pairarg_tac >> gvs[] >> IF_CASES_TAC >> gvs[])
    >> (
      rpt (TOP_CASE_TAC >> gvs[]) >>
      rpt (pairarg_tac >> gvs[]) >>
      strip_tac >> gvs[call_FFI_def, apply_oracle_def]
      )
    )>>
  map_every qid_spec_tac [`ms`,`k`,`ffi`,`mc`] >>
  ho_match_mp_tac evaluate'_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once eval_to'_def, Once evaluate'_def] >>
  rpt (TOP_CASE_TAC>>gvs[apply_oracle_def])>>
  TRY (rw[]>>Cases_on ‘r’>>gvs[halt_rel_def]>>NO_TAC)>>
  TRY (strip_tac >>
       gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality]>>
       NO_TAC) >>
  (strip_tac>>fs[]>>
   qsuff_tac `ffi = f`
   >- (strip_tac >> gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality]) >>
   irule io_events_mono_antisym >>
   imp_res_tac evaluate'_io_events_mono >> simp[] >>
   irule call_FFI_rel_io_events_mono >> irule RTC_SUBSET >>
   simp[call_FFI_rel_def, SF SFY_ss])
QED

Theorem eval_to'_evaluate'_timeout:
  eval_to' k mc ms = (Div',mc',ms') ⇔
  evaluate' mc (ffi :'ffi ffi_state) k ms = (TimeOut,mc',ms',ffi)
Proof
  eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`ffi`,`ms`,`mc`,`k`] >>
    ho_match_mp_tac eval_to_ind >> rw[] >>
    pop_assum mp_tac >> simp[Once eval_to'_def, Once evaluate'_def] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[]
    >- (IF_CASES_TAC >> gvs[] >> pairarg_tac >> gvs[] >> IF_CASES_TAC >> gvs[])
    >> (
      rpt (TOP_CASE_TAC >> gvs[]) >>
      rpt (pairarg_tac >> gvs[AllCaseEqs()]) >>
      strip_tac >> gvs[call_FFI_def, apply_oracle_def]
      )
    )>>
  map_every qid_spec_tac [`ms`,`k`,`ffi`,`mc`] >>
  ho_match_mp_tac evaluate'_ind >> rw[] >>
  pop_assum mp_tac >> simp[Once eval_to'_def, Once evaluate'_def] >>
  rpt (TOP_CASE_TAC>>gvs[apply_oracle_def])>>
  TRY (rw[]>>Cases_on ‘r’>>gvs[halt_rel_def]>>NO_TAC)>>
  TRY (strip_tac >>
       gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality]>>
       NO_TAC) >>
  (strip_tac>>fs[]>>
   qsuff_tac `ffi = f`
   >- (strip_tac >> gvs[call_FFI_def, AllCaseEqs(), ffi_state_component_equality]) >>
   irule io_events_mono_antisym >>
   imp_res_tac evaluate'_io_events_mono >> simp[] >>
   irule call_FFI_rel_io_events_mono >> irule RTC_SUBSET >>
   simp[call_FFI_rel_def, SF SFY_ss])
QED


(*********** eval / evaluate - non-FFI steps **********)

Theorem eval_evaluate_halt_rel:
  halt_rel r h ⇒ (
  eval (mc,ms) = Ret' r ⇔
  ∃k ms'. evaluate mc (ffi :'ffi ffi_state) k ms = (Halt h, ms', ffi))
Proof
  rw[] >> simp[eval_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[] >>
  gvs[eval_to_eval_to', evaluate_evaluate']
  >- (
    CCONTR_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
    drule_all $ SRULE [PULL_EXISTS] $ iffRL eval_to'_evaluate'_halt_rel >> rw[] >>
    first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
    Cases_on `eval_to' k mc ms` >> gvs[]
    ) >>
  eq_tac >> rw[]
  >- (
    qmatch_asmsub_abbrev_tac `FST res = _` >> PairCases_on `res` >> gvs[] >>
    drule_all $ iffLR eval_to'_evaluate'_halt_rel >>
    rw[] >> qexists_tac `x` >> pairarg_tac >> gvs[]
    )
  >- (
    pairarg_tac >> gvs[] >>
    drule_all $ SRULE [PULL_EXISTS] $ iffRL eval_to'_evaluate'_halt_rel >> rw[] >>
    dxrule eval_to'_agree >> simp[] >> disch_then drule >>
    disch_then $ assume_tac o GSYM >> gvs[]
    )
QED

Theorem eval_evaluate_error:
  eval (mc,ms) = Ret' Error ⇔
  ∃k ms'. evaluate mc (ffi :'ffi ffi_state) k ms = (Error, ms', ffi)
Proof
  rw[] >> simp[eval_def] >> DEEP_INTRO_TAC some_intro >> reverse $ rw[] >>
  gvs[eval_to_eval_to', evaluate_evaluate']
  >- (
    CCONTR_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
    drule_all $ SRULE [PULL_EXISTS] $ iffRL eval_to'_evaluate'_error >> rw[] >>
    first_x_assum $ qspec_then `k` assume_tac >> gvs[] >>
    Cases_on `eval_to' k mc ms` >> gvs[]
    ) >>
  eq_tac >> rw[]
  >- (
    qmatch_asmsub_abbrev_tac `FST res = _` >> PairCases_on `res` >> gvs[] >>
    drule_all $ iffLR eval_to'_evaluate'_error >>
    rw[] >> qexists_tac `x` >> pairarg_tac >> gvs[]
    )
  >- (
    pairarg_tac >> gvs[] >>
    drule_all $ SRULE [PULL_EXISTS] $ iffRL eval_to'_evaluate'_error >> rw[] >>
    drule eval_to'_agree >> simp[] >> disch_then drule >>
    disch_then $ assume_tac o GSYM >> gvs[]
    )
QED

Theorem eval_evaluate_timeout:
  eval (mc,ms) = Div' ⇔
  ∀k. ∃ms'. evaluate mc (ffi :'ffi ffi_state) k ms = (TimeOut, ms', ffi)
Proof
  eq_tac >> simp[eval_def] >> DEEP_INTRO_TAC some_intro >> rw[] >>
  gvs[eval_to_eval_to', evaluate_evaluate']
  >- (
    pairarg_tac >> gvs[] >>
    first_x_assum $ qspec_then `k` assume_tac >>
    qmatch_asmsub_abbrev_tac `FST res` >> PairCases_on `res` >> gvs[] >>
    imp_res_tac eval_to'_evaluate'_timeout >> gvs[]
    )
  >- (
    CCONTR_TAC >> gvs[] >> last_x_assum mp_tac >> simp[] >>
    first_x_assum $ qspec_then `x` assume_tac >> pairarg_tac >> gvs[] >>
    imp_res_tac eval_to'_evaluate'_timeout >> gvs[]
    )
QED


(*********** eval_to' / evaluate' - FFI steps **********)

Theorem evaluate'_1_ffi_changed_eval_to':
  evaluate' mc (ffi:'ffi ffi_state) 1 ms = (res,mc',ms',ffi') ∧ ffi' ≠ ffi ⇒
  ∃s conf ws f ms''. eval_to' 1 mc ms = (Vis' (s,conf,ws) f,mc',ms'')
Proof
  rw[evaluate'_1_ffi_changed, eval_to'_1_Vis] >> simp[SF SFY_ss]
QED

Theorem evaluate'_1_ffi_failed_eval_to':
  evaluate' mc (ffi:'ffi ffi_state) 1 ms = (Halt (FFI_outcome outcome),mc',ms',ffi') ⇒
  ∃s conf ws f mc''. eval_to' 1 mc ms = (Vis' (s,conf,ws) f,mc'',ms')
Proof
  rw[evaluate'_1_ffi_failed, eval_to'_1_Vis] >> simp[SF SFY_ss]
QED

Theorem eval_to'_1_ffi_evaluate:
  eval_to' 1 mc ms = (Vis' (s,conf,ws) f,mc',ms') ⇒
  (∃ms'' ffi'.
    evaluate' mc (ffi:'ffi ffi_state) 1 ms = (TimeOut,mc',ms'',ffi') ∧ ffi' ≠ ffi) ∨
  (∃out mc''.  evaluate' mc ffi 1 ms = (Halt (FFI_outcome out),mc'',ms',ffi))
Proof
  rw[evaluate'_1_ffi_changed, evaluate'_1_ffi_failed,eval_to'_1_Vis] >>
  simp[call_FFI_def, AllCaseEqs(), SF DNF_ss] >>
  qmatch_goalsub_abbrev_tac `ffi.oracle ffi_name ffi.ffi_state conf wb` >>
  Cases_on `ffi.oracle ffi_name ffi.ffi_state conf wb` >> simp[]>>
  gvs[Abbr ‘ffi_name’]
QED


(*********** trace_prefix **********)

Overload mk_ffi[local] =
  ``λffi oracle st. ffi with <| oracle := oracle; ffi_state := st |>``;

Theorem mk_ffi_I[local,simp]:
  mk_ffi ffi ffi.oracle ffi.ffi_state = ffi
Proof
  rw[ffi_state_component_equality]
QED

Theorem trace_prefix_machine_error:
  (∃n. trace_prefix n (oracle, ffi_st:'ffi)
        (machine_sem_itree (mc,ms)) = (io, SOME Error)) ⇔
  (∃k mc' ms' ffi'.
    evaluate' mc (mk_ffi ffi oracle ffi_st) k ms = (Error,mc',ms',ffi') ∧
    ffi'.io_events = ffi.io_events ++ io)
Proof
  eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`ms`,`mc`,`ffi`,`ffi_st`,`oracle`,`io`,`n`] >>
    Induct >> rw[trace_prefix_machine_sem_itree] >>
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[]
    >- (
      rw[] >> gvs[] >> gvs[eval_alt_def] >> every_case_tac >> gvs[] >>
      pairarg_tac >> gvs[] >>
      drule $ iffLR eval_to'_evaluate'_error >>
      disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> gvs[] >>
      goal_assum drule >> unabbrev_all_tac >> gvs[]
      ) >>
    PairCases_on `e` >> gvs[] >>
    every_case_tac >> gvs[] >> simp[trace_prefix_def] >>
    pairarg_tac >> rw[] >> gvs[] >>
    qpat_x_assum `eval _ = _` mp_tac >> simp[eval_alt_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >> pairarg_tac >> gvs[] >>
    drule eval_to'_min >> rw[] >> gvs[] >>
    qpat_x_assum `_ ≤ _` kall_tac >> qpat_x_assum `eval_to' x _ _ = _` kall_tac >>
    Cases_on `k'` >> gvs[] >> pop_assum $ qspec_then `n'` assume_tac >> gvs[] >>
    gvs[eval_to'_step_alt] >>
    drule eval_to'_1_ffi_evaluate >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> reverse $ gvs[]
    >- (
      gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis] >>
      unabbrev_all_tac >> gvs[call_FFI_def, AllCaseEqs()]
      ) >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> strip_tac >> gvs[] >>
    gvs[eval_to'_1_Vis, call_FFI_def, AllCaseEqs()] >>
    Q.REFINE_EXISTS_TAC `k + SUC n'` >> simp[evaluate'_add, evaluate'_step_alt] >>
    drule $ iffLR eval_to'_evaluate'_timeout >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate' mc0 (mk_ffi ffi0 _ _)` >>
    last_x_assum drule >> disch_then $ qspec_then `ffi0` assume_tac >> gvs[] >>
    goal_assum drule >> unabbrev_all_tac >> gvs[]
    )
  >- (
    map_every qid_spec_tac
      [`ms'`,`mc'`,`ffi'`,`ms`,`mc`,`ffi`,`ffi_st`,`oracle`,`io`,`k`] >>
    Induct >> rw[evaluate'_step] >>
    qabbrev_tac `res = evaluate' mc (mk_ffi ffi oracle ffi_st) 1 ms` >>
    PairCases_on `res` >> gvs[] >> FULL_CASE_TAC >> gvs[]
    >- (
      imp_res_tac evaluate'_1_ffi_unchanged >> gvs[] >>
      gvs[GSYM eval_to'_evaluate'_error] >>
      simp[machine_sem_itree, eval_alt_def] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `1` >> simp[]) >>
      dxrule eval_to'_agree >> simp[] >> disch_then $ qspec_then `x` $ mp_tac o GSYM >>
      impl_tac >- metis_tac[PAIR] >> rw[] >> gvs[] >>
      qexists_tac `SUC n` >> rw[trace_prefix_def]
      ) >>
    Cases_on `res3 = mk_ffi ffi oracle ffi_st` >> gvs[]
    >- (
      last_x_assum drule >> disch_then drule >> rw[] >>
      qsuff_tac `eval (mc,ms) = eval (res1,res2)`
      >- (rw[] >> imp_res_tac machine_sem_itree_eq >> gvs[SF SFY_ss]) >>
      irule eval_prefix >> gvs[GSYM eval_to'_evaluate'_timeout] >> goal_assum drule
      ) >>
    drule_all evaluate'_1_ffi_changed_eval_to' >> rw[] >> gvs[] >>
    simp[machine_sem_itree, eval_alt_def] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
    >- (qexists_tac `1` >> simp[]) >>
    pairarg_tac >> gvs[] >> dxrule_then drule eval_to'_agree >> rw[] >> gvs[] >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> strip_tac >> gvs[eval_to'_1_Vis] >>
    gvs[call_FFI_def, AllCaseEqs()] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> simp[trace_prefix_def] >>
    gvs[ffi_state_component_equality] >>
    imp_res_tac evaluate'_io_events_mono >> gvs[io_events_mono_def] >>
    Cases_on `io` >> gvs[] >>
    last_x_assum drule >> simp[] >> rw[] >> qexists_tac `n'` >> simp[]
    )
QED

Theorem trace_prefix_machine_halt:
  halt_rel r h ⇒ (
  (∃n. trace_prefix n (oracle, ffi_st:'ffi)
        (machine_sem_itree (mc,ms)) = (io, SOME r)) ⇔
  (∃k mc' ms' ffi'.
    evaluate' mc (mk_ffi ffi oracle ffi_st) k ms = (Halt h,mc',ms',ffi') ∧
    ffi'.io_events = ffi.io_events ++ io))
Proof
  rw[] >> imp_res_tac halt_rel_imps >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`ms`,`mc`,`ffi`,`ffi_st`,`oracle`,`io`,`n`] >>
    Induct >> rw[trace_prefix_machine_sem_itree] >>
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[]
    >- (
      rw[] >> gvs[] >> gvs[eval_alt_def] >> every_case_tac >> gvs[] >>
      pairarg_tac >> gvs[] >>
      drule_all $ iffLR eval_to'_evaluate'_halt_rel >>
      disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> gvs[] >>
      goal_assum drule >> unabbrev_all_tac >> gvs[]
      ) >>
    PairCases_on `e` >> gvs[] >>
    every_case_tac >> gvs[] >> simp[trace_prefix_def] >>
    pairarg_tac >> rw[] >> gvs[] >>
    qpat_x_assum `eval _ = _` mp_tac >> simp[eval_alt_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >> pairarg_tac >> gvs[] >>
    drule eval_to'_min >> rw[] >> gvs[] >>
    qpat_x_assum `_ ≤ _` kall_tac >> qpat_x_assum `eval_to' x _ _ = _` kall_tac >>
    Cases_on `k'` >> gvs[] >> pop_assum $ qspec_then `n'` assume_tac >> gvs[] >>
    gvs[eval_to'_step_alt] >>
    drule eval_to'_1_ffi_evaluate >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> reverse $ gvs[]
    >- (
      gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis] >>
      unabbrev_all_tac >> gvs[call_FFI_def, AllCaseEqs()]
      ) >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> strip_tac >> gvs[] >>
    gvs[eval_to'_1_Vis, call_FFI_def, AllCaseEqs()] >>
    Q.REFINE_EXISTS_TAC `k + SUC n'` >> simp[evaluate'_add, evaluate'_step_alt] >>
    drule $ iffLR eval_to'_evaluate'_timeout >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `evaluate' mc0 (mk_ffi ffi0 _ _)` >>
    last_x_assum drule >> disch_then $ qspec_then `ffi0` assume_tac >> gvs[] >>
    goal_assum drule >> unabbrev_all_tac >> gvs[]
    )
  >- (
    map_every qid_spec_tac
      [`ms'`,`mc'`,`ffi'`,`ms`,`mc`,`ffi`,`ffi_st`,`oracle`,`io`,`k`] >>
    Induct >> rw[evaluate'_step] >>
    qabbrev_tac `res = evaluate' mc (mk_ffi ffi oracle ffi_st) 1 ms` >>
    PairCases_on `res` >> gvs[] >> FULL_CASE_TAC >> gvs[]
    >- (
      imp_res_tac evaluate'_1_ffi_unchanged >> gvs[] >>
      drule $ GSYM eval_to'_evaluate'_halt_rel >> disch_then $ gvs o single >>
      simp[machine_sem_itree, eval_alt_def] >>
      DEEP_INTRO_TAC some_intro >> reverse $ rw[]
      >- (qexists_tac `1` >> simp[]) >>
      dxrule eval_to'_agree >> simp[] >> disch_then $ qspec_then `x` $ mp_tac o GSYM >>
      impl_tac >- metis_tac[PAIR] >> rw[] >> gvs[] >>
      qexists_tac `SUC n` >> rw[trace_prefix_def]
      ) >>
    Cases_on `res3 = mk_ffi ffi oracle ffi_st` >> gvs[]
    >- (
      last_x_assum drule >> disch_then drule >> rw[] >>
      qsuff_tac `eval (mc,ms) = eval (res1,res2)`
      >- (rw[] >> imp_res_tac machine_sem_itree_eq >> gvs[SF SFY_ss]) >>
      irule eval_prefix >> gvs[GSYM eval_to'_evaluate'_timeout] >> goal_assum drule
      ) >>
    drule_all evaluate'_1_ffi_changed_eval_to' >> rw[] >> gvs[] >>
    simp[machine_sem_itree, eval_alt_def] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
    >- (qexists_tac `1` >> simp[]) >>
    pairarg_tac >> gvs[] >> dxrule_then drule eval_to'_agree >> rw[] >> gvs[] >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> strip_tac >> gvs[eval_to'_1_Vis] >>
    gvs[call_FFI_def, AllCaseEqs()] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> simp[trace_prefix_def] >>
    gvs[ffi_state_component_equality] >>
    imp_res_tac evaluate'_io_events_mono >> gvs[io_events_mono_def] >>
    Cases_on `io` >> gvs[] >>
    last_x_assum drule >> simp[] >> rw[] >> qexists_tac `n'` >> simp[]
    )
QED

Theorem trace_prefix_machine_ffi_error:
  (∃n. trace_prefix n (oracle, ffi_st:'ffi)
        (machine_sem_itree (mc,ms)) = (io, SOME (FinalFFI (s,conf,ws) out))) ⇔
  (∃k mc' ms' ffi'.
    evaluate' mc (mk_ffi ffi oracle ffi_st) k ms =
      (Halt (FFI_outcome (Final_event s conf ws out)),mc',ms',ffi') ∧
    ffi'.io_events = ffi.io_events ++ io)
Proof
  rw[] >> imp_res_tac halt_rel_imps >> eq_tac >> rw[] >> rpt $ pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`ms`,`mc`,`ffi`,`ffi_st`,`oracle`,`io`,`n`] >>
    Induct >> rw[trace_prefix_machine_sem_itree] >>
    pop_assum mp_tac >> TOP_CASE_TAC >> gvs[]
    >- (
      rw[] >> gvs[] >> gvs[eval_alt_def] >> every_case_tac >> gvs[] >>
      pairarg_tac >> gvs[eval_to'_Ret_FinalFFI]
      ) >>
    PairCases_on `e` >> gvs[] >>
    every_case_tac >> gvs[] >> rw[trace_prefix_def] >> gvs[] >>
    qpat_x_assum `eval _ = _` mp_tac >> simp[eval_alt_def] >>
    DEEP_INTRO_TAC some_intro >> rw[] >> gvs[] >> pairarg_tac >> gvs[] >>
    drule eval_to'_min >> rw[] >> gvs[] >>
    qpat_x_assum `_ ≤ _` kall_tac >> qpat_x_assum `eval_to' x _ _ = _` kall_tac >>
    Cases_on `k'` >> gvs[] >> pop_assum $ qspec_then `n'` assume_tac >> gvs[] >>
    gvs[eval_to'_step_alt] >>
    drule eval_to'_1_ffi_evaluate >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> reverse $ gvs[]
    >- (
      qexists_tac `SUC n'` >> simp[evaluate'_step_alt] >>
      drule $ iffLR eval_to'_evaluate'_timeout >>
      disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> simp[] >>
      gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis] >>
      unabbrev_all_tac >> gvs[call_FFI_def, AllCaseEqs()]
      )
    >- (
      drule_all $ iffLR evaluate'_1_ffi_changed >> rw[] >> gvs[] >>
      gvs[call_FFI_def, AllCaseEqs(), eval_to'_1_Vis]
      )
    >- (
      qexists_tac `SUC n'` >> simp[evaluate'_step_alt] >>
      drule $ iffLR eval_to'_evaluate'_timeout >>
      disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> simp[] >>
      gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis] >>
      unabbrev_all_tac >> gvs[call_FFI_def, AllCaseEqs()]
      )
    >- (
      pairarg_tac >> gvs[] >> rename [`Div',mc1,ms1`,`Vis' _ _,mc2,ms2`] >>
      drule $ iffLR eval_to'_evaluate'_timeout >>
      disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >>
      Q.REFINE_EXISTS_TAC `SUC n' + k` >>
      simp[evaluate'_add_alt, evaluate'_step_alt] >>
      drule_all $ iffLR evaluate'_1_ffi_changed >> rw[] >> gvs[] >>
      gvs[call_FFI_def, AllCaseEqs(), eval_to'_1_Vis, ffi_state_component_equality] >>
      qmatch_goalsub_abbrev_tac `evaluate' mc1' _ _ ms1'` >>
      last_x_assum drule >> disch_then $ qspec_then `ffi'` assume_tac >> gvs[SF SFY_ss]
      )
    >- (
      qexists_tac `SUC n'` >> simp[evaluate'_step_alt] >>
      drule $ iffLR eval_to'_evaluate'_timeout >>
      disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> simp[] >>
      gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis] >>
      unabbrev_all_tac >> gvs[call_FFI_def, AllCaseEqs()]
      )
    >- (
      drule_all $ iffLR evaluate'_1_ffi_changed >> rw[] >> gvs[] >>
      gvs[call_FFI_def, AllCaseEqs(), eval_to'_1_Vis]
      )
    )
  >- (
    map_every qid_spec_tac
      [`ms'`,`mc'`,`ffi'`,`ms`,`mc`,`ffi`,`ffi_st`,`oracle`,`io`,`k`] >>
    Induct >> rw[evaluate'_step] >>
    qabbrev_tac `res = evaluate' mc (mk_ffi ffi oracle ffi_st) 1 ms` >>
    PairCases_on `res` >> gvs[] >> FULL_CASE_TAC >> gvs[]
    >- (
      imp_res_tac evaluate'_1_ffi_failed_eval_to' >>
      gvs[evaluate'_1_ffi_failed, call_FFI_def, AllCaseEqs()] >>
      simp[machine_sem_itree, eval_alt_def] >>
      (DEEP_INTRO_TAC some_intro >> reverse $ rw[] >- (qexists_tac `1` >> simp[])) >>
      pairarg_tac >> gvs[] >>
      dxrule_then drule eval_to'_agree >> rw[] >> gvs[] >>
      qexists_tac `SUC (SUC n)` >> gvs[eval_to'_1_Vis, trace_prefix_def]
      ) >>
    Cases_on `res3 = mk_ffi ffi oracle ffi_st` >> gvs[]
    >- (
      last_x_assum drule >> disch_then drule >> rw[] >>
      qsuff_tac `eval (mc,ms) = eval (res1,res2)`
      >- (rw[] >> imp_res_tac machine_sem_itree_eq >> gvs[SF SFY_ss]) >>
      irule eval_prefix >> gvs[GSYM eval_to'_evaluate'_timeout] >> goal_assum drule
      ) >>
    drule_all evaluate'_1_ffi_changed_eval_to' >> rw[] >> gvs[] >>
    simp[machine_sem_itree, eval_alt_def] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >> gvs[]
    >- (qexists_tac `1` >> simp[]) >>
    pairarg_tac >> gvs[] >> dxrule_then drule eval_to'_agree >> rw[] >> gvs[] >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> strip_tac >> gvs[eval_to'_1_Vis] >>
    gvs[call_FFI_def, AllCaseEqs()] >>
    Q.REFINE_EXISTS_TAC `SUC m` >> simp[trace_prefix_def] >>
    gvs[ffi_state_component_equality] >>
    imp_res_tac evaluate'_io_events_mono >> gvs[io_events_mono_def] >>
    Cases_on `io` >> gvs[] >>
    last_x_assum drule >> simp[] >> rw[] >> qexists_tac `n'` >> simp[]
    )
QED

Theorem trace_prefix_evaluate'_io_events:
  ∀n oracle ffi ffi_st mc ms io.
    trace_prefix n (oracle, ffi_st:'ffi)
      (machine_sem_itree (mc,ms)) = (io, NONE)
  ⇒ ∃k mc' ms' ffi'.
      evaluate' mc (mk_ffi ffi oracle ffi_st) k ms =
        (TimeOut,mc',ms',ffi') ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  Induct >> rw[trace_prefix_def] >- (qexists_tac `0` >> simp[]) >>
  gvs[trace_prefix_machine_sem_itree, eval_alt_def] >>
  pop_assum mp_tac >> DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (qexists_tac `0` >> simp[]) >>
  pop_assum mp_tac >> pairarg_tac >> gvs[] >>
  TOP_CASE_TAC >> gvs[] >> PairCases_on `e` >> gvs[] >>
  every_case_tac >> rw[] >> gvs[]
  >- (qexists_tac `0` >> simp[])
  >- (
    gvs[trace_prefix_def] >>
    drule eval_to'_min >> rw[] >> gvs[] >>
    qpat_x_assum `_ ≤ _` kall_tac >> qpat_x_assum `eval_to' x _ _ = _` kall_tac >>
    Cases_on `k'` >> gvs[] >> pop_assum $ qspec_then `n` assume_tac >> gvs[] >>
    gvs[eval_to'_step_alt] >>
    drule $ iffLR eval_to'_evaluate'_timeout >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >>
    qexists_tac `SUC n` >> simp[evaluate'_step_alt] >>
    drule eval_to'_1_ffi_evaluate >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> reverse $ gvs[]
    >- gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis, call_FFI_def] >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> rw[] >> gvs[] >>
    gvs[eval_to'_1_Vis, call_FFI_def]
    )
  >- (qexists_tac `0` >> simp[])
  >- (
    pairarg_tac >> gvs[] >>
    drule eval_to'_min >> rw[] >> gvs[] >>
    qpat_x_assum `_ ≤ _` kall_tac >> qpat_x_assum `eval_to' x _ _ = _` kall_tac >>
    Cases_on `k'` >> gvs[] >> pop_assum $ qspec_then `n'` assume_tac >> gvs[] >>
    gvs[eval_to'_step_alt] >>
    drule $ iffLR eval_to'_evaluate'_timeout >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >>
    Q.REFINE_EXISTS_TAC `SUC n' + k` >>
    simp[evaluate'_add_alt, evaluate'_step_alt] >>
    drule eval_to'_1_ffi_evaluate >>
    disch_then $ qspec_then `mk_ffi ffi oracle ffi_st` assume_tac >> reverse $ gvs[]
    >- gvs[evaluate'_1_ffi_failed, eval_to'_1_Vis, call_FFI_def] >>
    drule_all $ iffLR evaluate'_1_ffi_changed >> rw[] >> gvs[] >>
    gvs[eval_to'_1_Vis, call_FFI_def] >>
    qmatch_goalsub_abbrev_tac `mk_ffi ffi0 _ _` >>
    last_x_assum drule >> disch_then $ qspec_then `ffi0` assume_tac >> gvs[] >>
    goal_assum drule >> unabbrev_all_tac >> gvs[]
    )
QED

Theorem evaluate'_trace_prefix_io_events:
  ∀k mc (ffi:'ffi ffi_state) ms mc' ms' ffi'.
    evaluate' mc ffi k ms = (TimeOut,mc',ms',ffi')
  ⇒ ∃n io.
      trace_prefix n (ffi.oracle,ffi.ffi_state)
        (machine_sem_itree (mc,ms)) = (io,NONE) ∧
      ffi'.io_events = ffi.io_events ++ io
Proof
  Induct >> rw[evaluate'_step] >- (qexists_tac `0` >> rw[trace_prefix_def]) >>
  qabbrev_tac `res = evaluate' mc ffi 1 ms` >> PairCases_on `res` >> gvs[] >>
  Cases_on `res0` >> gvs[] >> Cases_on `res3 = ffi` >> gvs[]
  >- (
    last_x_assum drule >> rw[] >>
    qsuff_tac `eval (mc,ms) = eval (res1,res2)`
    >- (rw[] >> imp_res_tac machine_sem_itree_eq >> gvs[SF SFY_ss]) >>
    irule eval_prefix >> gvs[GSYM eval_to'_evaluate'_timeout] >> goal_assum drule
    ) >>
  drule_all evaluate'_1_ffi_changed_eval_to' >> rw[] >> gvs[] >>
  simp[machine_sem_itree, eval_alt_def] >>
  DEEP_INTRO_TAC some_intro >> reverse $ rw[]
  >- (pop_assum $ qspec_then `1` assume_tac >> gvs[]) >>
  pairarg_tac >> gvs[] >> dxrule_then drule eval_to'_agree >> rw[] >> gvs[] >>
  drule_all $ iffLR evaluate'_1_ffi_changed >> strip_tac >> gvs[eval_to'_1_Vis] >>
  gvs[call_FFI_def, AllCaseEqs()] >>
  Q.REFINE_EXISTS_TAC `SUC m` >> simp[trace_prefix_def] >>
  gvs[ffi_state_component_equality] >>
  last_x_assum drule >> rw[] >> qexists_tac `n'` >> simp[]
QED

Theorem evaluate'_trace_prefix_diverge:
  (∀n. ∃io. trace_prefix n (oracle,ffi_st:'ffi)
    (machine_sem_itree (mc,ms)) = (io,NONE)) ⇔
  (∀k. ∃mc' ms' ffi'.
    evaluate' mc (mk_ffi ffi oracle ffi_st) k ms = (TimeOut,mc',ms',ffi'))
Proof
  eq_tac >> rw[]
  >- (
    CCONTR_TAC >> gvs[] >>
    qabbrev_tac `res = evaluate' mc (mk_ffi ffi oracle ffi_st) k ms` >>
    PairCases_on `res` >> gvs[] >> imp_res_tac evaluate'_io_events_mono >>
    gvs[io_events_mono_def, IS_PREFIX_APPEND] >>
    reverse $ Cases_on `res0` >> gvs[]
    >- (
      drule_all $ SRULE [PULL_EXISTS] $ iffRL trace_prefix_machine_error >>
      strip_tac >> gvs[] >> last_x_assum $ qspec_then `n` mp_tac >> simp[]
      ) >>
    Cases_on `∃h. halt_rel h o'` >> gvs[]
    >- (
      drule_all $ SRULE [PULL_EXISTS] $ iffRL trace_prefix_machine_halt >>
      strip_tac >> gvs[] >> last_x_assum $ qspec_then `n` mp_tac >> simp[]
      ) >>
    Cases_on `o'` >> gvs[halt_rel_alt_def] >> Cases_on `f` >>
    drule_all $ SRULE [PULL_EXISTS] $ iffRL trace_prefix_machine_ffi_error >>
    strip_tac >> gvs[] >> last_x_assum $ qspec_then `n` mp_tac >> simp[]
    )
  >- (
    CCONTR_TAC >> gvs[] >>
    Cases_on `trace_prefix n (oracle,ffi_st) (machine_sem_itree (mc,ms))` >> gvs[] >>
    Cases_on `r` >> gvs[] >> Cases_on `x` >> gvs[]
    >- (
      `halt_rel Termination Success` by gvs[halt_rel_def] >>
      drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_halt >>
      disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
      last_x_assum $ qspec_then `k` assume_tac >> gvs[]
      )
    >- (
      `halt_rel OutOfMemory Resource_limit_hit` by gvs[halt_rel_def] >>
      drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_halt >>
      disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
      last_x_assum $ qspec_then `k` assume_tac >> gvs[]
      )
    >- (
      drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_error >>
      disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
      last_x_assum $ qspec_then `k` assume_tac >> gvs[]
      )
    >- (
      PairCases_on `p` >>
      drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_ffi_error >>
      disch_then $ qspec_then `ffi` assume_tac >> gvs[] >>
      last_x_assum $ qspec_then `k` assume_tac >> gvs[]
      )
    )
QED

Theorem trace_prefix_machine_halt_alt[local] =
  Q.INST [`oracle` |-> `ffi.oracle`, `ffi_st` |-> `ffi.ffi_state`]
    trace_prefix_machine_halt |> SRULE [];

Theorem trace_prefix_machine_error_alt[local] =
  Q.INST [`oracle` |-> `ffi.oracle`, `ffi_st` |-> `ffi.ffi_state`]
    trace_prefix_machine_error |> SRULE [];

Theorem trace_prefix_machine_ffi_error_alt[local] =
  Q.INST [`oracle` |-> `ffi.oracle`, `ffi_st` |-> `ffi.ffi_state`]
    trace_prefix_machine_ffi_error |> SRULE [];

Theorem lprefix_chain_evaluate':
  lprefix_chain
    (IMAGE (λk. fromList (SND (SND (SND (evaluate' mc st k ms)))).io_events) 𝕌(:num))
Proof
  rw[lprefix_chain_def] >> simp[LPREFIX_fromList, from_toList] >>
  wlog_tac `k ≤ k'` [`k`,`k'`] >- (`k' ≤ k` by gvs[] >> metis_tac[]) >>
  disj1_tac >> imp_res_tac LESS_EQUAL_ADD >> gvs[] >>
  simp[evaluate'_add_alt] >>
  qabbrev_tac `res = evaluate' mc st k ms` >> PairCases_on `res` >> gvs[] >>
  CASE_TAC >> gvs[] >>
  qpat_abbrev_tac `res' = evaluate' _ _ _ _` >> PairCases_on `res'` >> gvs[] >>
  imp_res_tac evaluate'_io_events_mono >> gvs[io_events_mono_def]
QED

Theorem itree_machine_semantics:
  (machine_sem mc (ffi:'ffi ffi_state) ms (Terminate outcome io_list) ⇔
    ∃n io res.
      trace_prefix n (ffi.oracle, ffi.ffi_state)
        (machine_sem_itree (mc,ms)) = (io, SOME res) ∧
      io_list = ffi.io_events ++ io ∧
      if outcome = Success then res = Termination
      else if outcome = Resource_limit_hit then res = OutOfMemory
      else ∃s conf ws f.
              outcome = FFI_outcome (Final_event s conf ws f) ∧
              res = FinalFFI (s,conf,ws) f) ∧

  (machine_sem mc ffi ms (Diverge io_trace) ⇔
    (∀n. ∃io. trace_prefix n (ffi.oracle, ffi.ffi_state)
                (machine_sem_itree (mc,ms)) = (io, NONE)) ∧
    lprefix_lub
      { fromList (ffi.io_events ++ io) | io |
          ∃n res. trace_prefix n (ffi.oracle, ffi.ffi_state)
                    (machine_sem_itree (mc,ms)) = (io, res) }
      io_trace) ∧

  (machine_sem mc ffi ms Fail ⇔
    ∃n io. trace_prefix n (ffi.oracle, ffi.ffi_state)
            (machine_sem_itree (mc,ms)) = (io, SOME Error))
Proof
  rw[machine_sem_def, evaluate_evaluate']
  >- ( (* termination *)
    Cases_on `∃h. halt_rel h outcome` >> gvs[]
    >- (
      eq_tac >> rw[]
      >- (
        pairarg_tac >> gvs[] >> imp_res_tac evaluate'_io_events_mono >>
        gvs[io_events_mono_def, IS_PREFIX_APPEND] >>
        drule_all $ SRULE [PULL_EXISTS] $ iffRL trace_prefix_machine_halt_alt >>
        strip_tac >> goal_assum drule >>
        Cases_on `h` >> gvs[halt_rel_def]
        )
      >- (
        `res = h` by (Cases_on `h` >> gvs[halt_rel_def]) >> gvs[] >>
        drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_halt_alt >>
        rw[] >> qexists_tac `k` >> simp[]
        )
      )
    >- (
      Cases_on `outcome` >> gvs[halt_rel_alt_def] >> eq_tac >> rw[]
      >- (
        pairarg_tac >> gvs[] >> imp_res_tac evaluate'_io_events_mono >>
        gvs[io_events_mono_def, IS_PREFIX_APPEND] >> Cases_on `f` >>
        drule_all $ SRULE [PULL_EXISTS] $ iffRL trace_prefix_machine_ffi_error_alt >>
        strip_tac >> goal_assum drule >> simp[]
        )
      >- (
        drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_ffi_error_alt >>
        rw[] >> qexists_tac `k` >> simp[]
        )
      )
    )
  >- ( (* divergence *)
    irule $ DECIDE ``a = c ∧ (a ∧ c ⇒ b = d) ⇒ (a ∧ b ⇔ c ∧ d)`` >> rw[]
    >- (
      eq_tac >> rw[]
      >- (
        irule $ iffRL evaluate'_trace_prefix_diverge >> qexists_tac `ffi` >> rw[] >>
        pop_assum $ qspec_then `k` assume_tac >> pairarg_tac >> gvs[]
        )
      >- (
        pairarg_tac >> gvs[] >> drule $ iffLR evaluate'_trace_prefix_diverge >>
        disch_then $ qspecl_then [`ffi`,`k`] assume_tac >> gvs[]
        )
      ) >>
    irule lprefix_lub_equiv_chain >> irule_at Any IMP_equiv_lprefix_chain >>
    simp[UNCURRY, lprefix_chain_trace_prefix, lprefix_chain_evaluate'] >>
    rw[lprefix_rel_def, PULL_EXISTS, LPREFIX_fromList, from_toList]
    >- (
      last_x_assum $ qspec_then `k` assume_tac >> pairarg_tac >> gvs[] >>
      drule evaluate'_trace_prefix_io_events >> rw[] >> goal_assum drule >> simp[]
      )
    >- (
      first_x_assum $ qspec_then `n` assume_tac >> gvs[] >>
      drule trace_prefix_evaluate'_io_events >>
      disch_then $ qspec_then `ffi` assume_tac >> gvs[] >> qexists_tac `k` >> simp[]
      )
    )
  >- ( (* type error *)
    eq_tac >> rw[]
    >- (
      pairarg_tac >> gvs[] >> imp_res_tac evaluate'_io_events_mono >>
      gvs[io_events_mono_def, IS_PREFIX_APPEND] >>
      drule_all $ SRULE [PULL_EXISTS] $ iffRL trace_prefix_machine_error_alt >>
      strip_tac >> goal_assum drule
      )
    >- (
      drule_all $ SRULE [PULL_EXISTS] $ iffLR trace_prefix_machine_error_alt >>
      rw[] >> qexists_tac `k` >> simp[]
      )
    )
QED


(**********)
