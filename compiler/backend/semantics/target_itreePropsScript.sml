(*
  Properties about the itree target semantics
*)
Theory target_itreeProps
Ancestors
  targetSem targetProps itree target_itreeSem itree_semantics
  itree_semanticsProps
Libs
  preamble

(********** machine_sem_itree **********)

Theorem machine_sem_itree:
  machine_sem_itree (mc, ms) =
  case eval (mc, ms) of
  | Ret' r => Ret r
  | Div' => Div
  | Vis' (s, ws1, ws2) f =>
      Vis (s, ws1, ws2) (λa.
        case a of
        | INL x => Ret (FinalFFI (s, ws1, ws2) x)
        | INR y =>
            if LENGTH ws2 = LENGTH y then machine_sem_itree (f y)
            else Ret $ FinalFFI (s, ws1, ws2) FFI_failed)
Proof
  rw[machine_sem_itree_def, Once itree_unfold_err] >>
  CASE_TAC >> gvs[] >> PairCases_on `e` >> gvs[] >>
  rw[FUN_EQ_THM] >> CASE_TAC >> gvs[] >> CASE_TAC >> gvs[] >>
  Cases_on `f y` >> simp[machine_sem_itree_def]
QED

Theorem trace_prefix_machine_sem_itree:
  trace_prefix 0 (oracle,ffi_st) (machine_sem_itree (mc, ms)) = ([], NONE) ∧
  trace_prefix (SUC n) (oracle,ffi_st) (machine_sem_itree (mc, ms)) =
    case eval (mc, ms) of
    | Ret' r => ([], SOME r)
    | Div' => ([], NONE)
    | Vis' (s, conf, ws) f =>
        case oracle s ffi_st conf ws of
        | Oracle_return ffi_st' ws' =>
            if LENGTH ws ≠ LENGTH ws' ∧ n = 0 then ([],NONE)
            else if LENGTH ws ≠ LENGTH ws' then
              ([],SOME (FinalFFI (s,conf,ws) FFI_failed))
            else let
              (io,res) = trace_prefix n (oracle,ffi_st') (machine_sem_itree (f ws')) in
              (IO_event s conf (ZIP (ws,ws'))::io,res)
        | Oracle_final outcome =>
            if n = 0 then ([], NONE)
            else ([], SOME (FinalFFI (s,conf,ws) outcome))
Proof
  rw[trace_prefix_def] >> rw[Once machine_sem_itree] >>
  CASE_TAC >> gvs[trace_prefix_def] >>
  PairCases_on `e` >> gvs[trace_prefix_def] >>
  reverse CASE_TAC >> gvs[]
  >- (Cases_on `n` >> gvs[trace_prefix_def]) >>
  IF_CASES_TAC >> gvs[] >>
  Cases_on `n` >> gvs[trace_prefix_def]
QED

Theorem machine_sem_itree_eq:
  eval (mc,ms) = eval (mc',ms') ⇒
  machine_sem_itree (mc,ms) = machine_sem_itree (mc',ms')
Proof
  rw[machine_sem_itree]
QED


(*********** eval_to' **********)

Definition eval_to'_def:
  eval_to' k (mc:('b,'a,'c) machine_config) (ms:'a) =
    if k = 0n then (Div',mc,ms)
    else
      if mc.target.get_pc ms IN (mc.prog_addresses DIFF set mc.ffi_entry_pcs) then
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
              eval_to' (k - 1) mc ms2
            else
              (Ret' Error,mc,ms)
        else (Ret' Error,mc,ms)
      else if mc.target.get_pc ms = mc.halt_pc then
        (if mc.target.get_reg ms mc.ptr_reg = 0w
         then (Ret' Termination,mc,ms) else (Ret' OutOfMemory,mc,ms))
      else if mc.target.get_pc ms = mc.ccache_pc then
        let (ms1,new_oracle) =
          apply_oracle mc.ccache_interfer
            (mc.target.get_reg ms mc.ptr_reg,
             mc.target.get_reg ms mc.len_reg,
             ms) in
        let mc = mc with ccache_interfer := new_oracle in
          eval_to' (k-1) mc ms1
      else
        case find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 of
        | NONE => (Ret' Error,mc,ms)
        | SOME ffi_index =>
            case EL ffi_index mc.ffi_names of
              | SharedMem op =>
                  (case ALOOKUP mc.mmio_info ffi_index of
                   | NONE => (Ret' Error,mc,ms)
                   | SOME (nb,a,reg,pc') =>
                       (case op of
                        | MappedRead =>
                            (case a of
                             | Addr r off =>
                               let ad = mc.target.get_reg ms r + off in
                                 if (if nb = 0w
                                     then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
                                    (ad IN mc.shared_addresses) ∧
                                    is_valid_mapped_read (mc.target.get_pc ms) nb a reg pc'
                                                         mc.target ms mc.prog_addresses
                                 then
                                   let mc1 =
                                       mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                                     (Vis' (SharedMem MappedRead,[nb],word_to_bytes ad F)
                                           (\new_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms))),
                                      mc1,ms)
                                 else (Ret' Error,mc,ms))

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
                                   let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                                     (Vis'
                                      (SharedMem MappedWrite,[nb],
                                       ((let w = mc.target.get_reg ms reg in
                                           if nb = 0w then word_to_bytes w F
                                           else word_to_bytes_aux (w2n nb) w F) ++
                                        (word_to_bytes ad F)))
                                      (\new_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms))),
                                       mc1,ms)
                                  else (Ret' Error,mc,ms))))
                  | ExtCall _ =>
                      (case ALOOKUP mc.mmio_info ffi_index of
                       | SOME _ => (Ret' Error, mc, ms)
                       | NONE =>
                           (case read_ffi_bytearrays mc ms of
                            | (SOME bytes, SOME bytes2) =>
                                let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                                  if EL ffi_index mc.ffi_names = ExtCall "" then
                                    eval_to' (k - 1) mc1 (mc.ffi_interfer 0 (ffi_index,bytes2,ms))
                                  else (Vis' (EL ffi_index mc.ffi_names, bytes, bytes2)
                                             (λnew_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms))),
                                        mc1,ms)
                            | _ => (Ret' Error,mc,ms)))
End

Theorem eval_to'_0[simp]:
  eval_to' 0 mc ms = (Div',mc,ms)
Proof
  rw[Once eval_to'_def]
QED

Theorem eval_to_eval_to':
  ∀k mc ms. eval_to k mc ms = FST (eval_to' k mc ms)
Proof
  recInduct eval_to_ind >> rw[] >>
  simp[Once eval_to_def, Once eval_to'_def] >>
  IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[apply_oracle_def] >> IF_CASES_TAC >> gvs[] >>
  rpt (TOP_CASE_TAC >> gvs[]) >>
  pairarg_tac >> gvs[] >> rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem eval_to'_step:
  eval_to' 0 mc ms = (Div',mc,ms) ∧
  eval_to' (SUC n) mc ms =
  case eval_to' 1 mc ms of
  | (Div',mc',ms') => eval_to' n mc' ms'
  | res => res
Proof
  simp[]>> simp[Once eval_to'_def, SimpRHS] >>simp[Once eval_to'_def] >>
  IF_CASES_TAC >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[apply_oracle_def]) >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem eval_to'_step_alt:
  eval_to' 0 mc ms = (Div',mc,ms) ∧
  eval_to' (SUC n) mc ms =
    case eval_to' n mc ms of
    | (Div',mc',ms') => eval_to' 1 mc' ms'
    | res => res
Proof
  simp[] >> map_every qid_spec_tac [`ms`,`mc`,`n`] >>
  Induct >- rw[] >> rpt gen_tac >>
  rewrite_tac[eval_to'_step] >>
  qabbrev_tac `ev = eval_to' 1 mc ms` >> PairCases_on `ev` >> gvs[] >>
  TOP_CASE_TAC >> simp[] >> simp[GSYM eval_to'_step]
QED

Theorem eval_to'_add:
  ∀a b.
    eval_to' (a + b) mc ms =
    case eval_to' b mc ms of
    | (Div',mc',ms') => eval_to' a mc' ms'
    | res => res
Proof
  Induct >> rw[eval_to'_step, ADD_CLAUSES] >>
  qabbrev_tac `ev = eval_to' b mc ms` >> PairCases_on `ev` >> gvs[] >>
  Cases_on `ev0` >> gvs[] >> simp[GSYM eval_to'_step] >> simp[eval_to'_step_alt]
QED

Theorem eval_to'_add_alt:
  ∀a b.
    eval_to' (a + b) mc ms =
    case eval_to' a mc ms of
    | (Div',mc',ms') => eval_to' b mc' ms'
    | res => res
Proof
  once_rewrite_tac[ADD_COMM] >> simp[eval_to'_add]
QED

Theorem eval_to'_add_clock:
  ∀k mc ms res k'.
    eval_to' k mc ms = res ∧ FST res ≠ Div' ∧ k ≤ k'
  ⇒ eval_to' k' mc ms = res
Proof
  recInduct eval_to'_ind >> rw[] >>
  qpat_x_assum `FST _ ≠ _` mp_tac >> once_rewrite_tac[eval_to'_def] >>
  TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
  TOP_CASE_TAC >> gvs[apply_oracle_def] >> rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem eval_to'_agree:
  ∀k mc ms res1 res2 k'.
    eval_to' k mc ms = res1 ∧ eval_to' k' mc ms = res2 ∧
    FST res1 ≠ Div' ∧ FST res2 ≠ Div'
  ⇒ res1 = res2
Proof
  recInduct eval_to_ind >> rw[] >>
  ntac 2 $ pop_assum mp_tac >> once_rewrite_tac[eval_to'_def] >> strip_tac >>
  Cases_on `k = 0` >> Cases_on `k' = 0` >> gvs[] >>
  TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[apply_oracle_def] >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem eval_to'_remove_clock:
  eval_to' k mc ms = res ∧ FST res = Div' ∧ k' ≤ k ⇒
  FST (eval_to' k' mc ms) = Div'
Proof
  metis_tac[eval_to'_add_clock, PAIR]
QED

Theorem eval_to'_min:
  ∀k mc ffi ms res.
    eval_to' k mc ms = res ∧ FST res ≠ Div'
  ⇒ ∃k'. k' ≤ k ∧ eval_to' k' mc ms = res ∧
      ∀m. m < k' ⇒ ∃mc' ms'. eval_to' m mc ms = (Div',mc',ms')
Proof
  Induct >> rw[] >>
  qabbrev_tac `res = eval_to' (SUC k) mc ms` >> PairCases_on `res` >> gvs[] >>
  gvs[eval_to'_step_alt] >>
  Cases_on `eval_to' k mc ms` >> gvs[] >> Cases_on `q` >> gvs[]
  >- (
    first_x_assum $ qspecl_then [`mc`,`ms`] assume_tac >> gvs[] >>
    qexists_tac `k'` >> simp[]
    )
  >- (
    PairCases_on `r` >> gvs[] >>
    qexists_tac `SUC k` >> simp[eval_to'_step_alt] >> rw[] >>
    drule eval_to'_remove_clock >> simp[] >>
    disch_then $ qspec_then `m` mp_tac >> simp[] >> metis_tac[PAIR]
    )
  >- (
    first_x_assum $ qspecl_then [`mc`,`ms`] assume_tac >> gvs[] >>
    qexists_tac `k'` >> simp[]
    )
QED

Theorem eval_to'_Ret_FinalFFI:
  ∀k mc ms p out mc' ms'. eval_to' k mc ms ≠ (Ret' (FinalFFI p out),mc',ms')
Proof
  ho_match_mp_tac eval_to'_ind >> rw[] >> simp[Once eval_to'_def] >>
  gvs[AllCaseEqs(), apply_oracle_def] >>
  rw[DISJ_EQ_IMP] >> gvs[]
  >> metis_tac[]
QED

Theorem Sh_not_Ext:
  (∃s. x = SharedMem s) ⇔ (∀s. x ≠ ExtCall s)
Proof
  Cases_on ‘x’>>gvs[]
QED

Theorem not_Sh_Ext:
  (∀s. x ≠ SharedMem s) ⇔ (∃s. x = ExtCall s)
Proof
  Cases_on ‘x’>>gvs[]
QED

Theorem eval_to'_1_Vis:
  eval_to' 1 (mc:('b,'a,'c) machine_config) ms = (Vis' (s,conf,ws) f,mc',ms') ⇔
    mc.target.get_pc ms ∉ (mc.prog_addresses DIFF set mc.ffi_entry_pcs) ∧
    mc.target.get_pc ms ≠ mc.halt_pc ∧
    mc.target.get_pc ms ≠ mc.ccache_pc ∧
    ∃n.
      find_index (mc.target.get_pc ms) mc.ffi_entry_pcs 0 = SOME n ∧
      ((s = SharedMem MappedRead /\
        ?nb ad r off reg pc'.
          ALOOKUP mc.mmio_info n = SOME (nb,Addr r off,reg,pc') /\
          ad = mc.target.get_reg ms r + off /\
          (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
          ad IN mc.shared_addresses /\
          is_valid_mapped_read (mc.target.get_pc ms) nb (Addr r off) reg
            pc' mc.target ms mc.prog_addresses /\
          conf = [nb] /\
          ws = word_to_bytes ad F
       ) \/
      (s = SharedMem MappedWrite /\
      ?nb ad r off reg pc'.
        ALOOKUP mc.mmio_info n = SOME (nb,Addr r off,reg,pc') /\
        ad = mc.target.get_reg ms r + off /\
        (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
        ad IN mc.shared_addresses /\

        is_valid_mapped_write (mc.target.get_pc ms) nb (Addr r off) reg
          pc' mc.target ms mc.prog_addresses /\
        conf = [nb] /\
        ws = (if nb = 0w then word_to_bytes (mc.target.get_reg ms reg) F
             else word_to_bytes_aux (w2n nb) (mc.target.get_reg ms reg) F) ++
              word_to_bytes ad F) \/
      (∃t. s = ExtCall t /\
        ALOOKUP mc.mmio_info n = NONE ∧
        read_ffi_bytearrays mc ms = (SOME conf,SOME ws))) ∧
      s ≠ ExtCall "" ∧ s = EL n mc.ffi_names ∧
      mc' = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer ∧ ms' = ms ∧
      f = (λnew_bytes. (mc', mc.ffi_interfer 0 (n,new_bytes,ms)))
Proof
  simp[Once eval_to'_def] >>
  rpt (TOP_CASE_TAC>>gvs[apply_oracle_def]) >>
  eq_tac >> rw[] >> gvs[]
QED


(*********** eval **********)

Theorem eval:
  eval (mc:('b,'a','c) machine_config, ms) =
    if mc.target.get_pc ms IN (mc.prog_addresses DIFF set mc.ffi_entry_pcs)
    then
      if encoded_bytes_in_mem
          mc.target.config (mc.target.get_pc ms)
          (mc.target.get_byte ms) mc.prog_addresses
      then
        let ms1 = mc.target.next ms in
        let (ms2,new_oracle) = apply_oracle mc.next_interfer ms1 in
        let mc = mc with next_interfer := new_oracle in
          if EVERY mc.target.state_ok [ms;ms1;ms2] ∧
             (∀x. x ∉ mc.prog_addresses ⇒
                 mc.target.get_byte ms1 x =
                 mc.target.get_byte ms x)
          then eval (mc, ms2)
          else Ret' Error
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
        eval (mc, ms1)
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
                                  (ad IN mc.shared_addresses) /\
                                  is_valid_mapped_read (mc.target.get_pc ms) nb a reg pc'
                                                       mc.target ms mc.prog_addresses
                               then
                                 let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                                   Vis' (SharedMem MappedRead,[nb],word_to_bytes ad F)
                                        (\new_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms)))
                               else Ret' Error)
                    | MappedWrite =>
                        (case a of
                         | Addr r off =>
                             let ad = (mc.target.get_reg ms r) + off in
                               if (if nb = 0w then (w2n ad MOD (dimindex (:'b) DIV 8)) = 0 else T) ∧
                                  (ad IN mc.shared_addresses) /\
                                  is_valid_mapped_write (mc.target.get_pc ms) nb a reg pc'
                                                        mc.target ms mc.prog_addresses
                               then
                                 let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
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
                   case read_ffi_bytearrays mc ms of
                   | (SOME bytes, SOME bytes2) =>
                       let mc1 = mc with ffi_interfer := shift_seq 1 mc.ffi_interfer in
                         if EL ffi_index mc.ffi_names = ExtCall "" then
                           eval (mc1, mc.ffi_interfer 0 (ffi_index,bytes2,ms))
                         else Vis' (EL ffi_index mc.ffi_names, bytes, bytes2)
                                   (λnew_bytes. (mc1, mc.ffi_interfer 0 (ffi_index,new_bytes,ms)))
                         | _ => Ret' Error)
Proof
  simp[Once eval_def] >>
  DEEP_INTRO_TAC some_intro >> simp[] >> conj_tac >> rpt strip_tac >> gvs[]
  >- (
    pop_assum mp_tac >> once_rewrite_tac[eval_to_def] >>
    IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[apply_oracle_def] >>
    rpt (TOP_CASE_TAC >> gvs[]) >>
    rw[eval_def] >> DEEP_INTRO_TAC some_intro >> rw[] >>
    gvs[eval_to_eval_to'] >> AP_TERM_TAC >> irule eval_to'_agree >> simp[] >>
    metis_tac[]
    )
  >- (
    pop_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >> simp[Once eval_to_def] >>
    IF_CASES_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    TOP_CASE_TAC >> gvs[apply_oracle_def] >>
    simp[eval_def] >> rpt (TOP_CASE_TAC >> gvs[])
    )
QED

Theorem eval_alt_def:
  eval (mc,ms) =
    case some k. ∀mc' ms'. eval_to' k mc ms ≠ (Div',mc',ms') of
    | NONE => Div'
    | SOME k => let (t,mc',ms') = eval_to' k mc ms in t
Proof
  rw[eval_def, eval_to_eval_to'] >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (
    qmatch_goalsub_abbrev_tac `FST res` >> PairCases_on `res` >> gvs[] >>
    DEEP_INTRO_TAC some_intro >> reverse $ rw[] >- (qexists_tac `x` >> simp[]) >>
    pairarg_tac >> gvs[] >> dxrule_then dxrule eval_to'_agree >> simp[]
    )
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >>
    pairarg_tac >> gvs[] >> metis_tac[FST]
    )
QED

Theorem eval_prefix:
  eval_to' k mc ms = (Div',mc',ms') ⇒ eval (mc,ms) = eval (mc',ms')
Proof
  rw[eval_alt_def] >>
  reverse (DEEP_INTRO_TAC some_intro >> rw[] >> DEEP_INTRO_TAC some_intro >> rw[]) >>
  rpt (pairarg_tac >> gvs[])
  >- (first_x_assum $ qspec_then `x + k` assume_tac >> gvs[eval_to'_add])
  >- (
    `k < x` by (
      CCONTR_TAC >> gvs[NOT_LESS] >>
      rev_dxrule eval_to'_remove_clock >> simp[] >> goal_assum drule >> simp[]) >>
    imp_res_tac LESS_ADD >> gvs[eval_to'_add_alt] >>
    first_x_assum $ qspec_then `p` assume_tac >> gvs[]
    )
  >- (
    `k < x` by (
      CCONTR_TAC >> gvs[NOT_LESS] >>
      rev_dxrule eval_to'_remove_clock >> simp[] >> goal_assum drule >> simp[]) >>
    imp_res_tac LESS_ADD >> gvs[eval_to'_add_alt] >>
    dxrule eval_to'_agree >> disch_then dxrule >> simp[]
    )
QED

(**********)

