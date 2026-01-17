(*
    Proof of correspondence between functional big-step semantics
    and itree semantics for Pancake.
*)
Theory pan_itreeEquivProof
Libs
  preamble
Ancestors
 mlstring panProps itreeTau panSem pan_itreeSem pan_itreeProps panLang ffi

val _ = gen_remove_ovl_mapping "mrec_sem";

(**************************)

val evaluate_invariant_oracle = cj 7 panPropsTheory.evaluate_invariants;

Theorem explode_eq_implode[local]:
  ∀x y. explode x = y ⇔ x = implode y
Proof
  rpt Cases \\ simp [implode_def]
QED

Theorem nondiv_evaluate:
  ltree (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) =
  FUNPOW Tau n (Ret (INR r)) : 'a ptree
  ∧ evaluate (p,s with clock := k) = (res, t) ∧ res ≠ SOME TimeOut ⇒
  res = FST r ∧ bst t = SND r ∧
  t.ffi.ffi_state = SND (comp_ffi (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))))
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘r’,‘k’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>
  rpt gen_tac>>strip_tac>>
  Cases_on ‘p’>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]
  >~ [‘ExtCall’]>-
   (fs[mrec_ExtCall,call_FFI_def]>>
    rpt (PURE_TOP_CASE_TAC>>fs[])>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    gvs[set_var_defs,bst_def,empty_locals_defs,
        explode_eq_implode,implode_def])>>
  fs[mrec_prog_simps,mrec_Seq,mrec_If,Once mrec_While,mrec_Call,
     mrec_DecCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
     empty_locals_defs,dec_clock_def,kvar_defs2]>>gvs[FUNPOW_SUC]>>
  TRY (gvs[AllCaseEqs()]>>NO_TAC)
  (* Dec *)
  >- (rpt (CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[FUNPOW_SUC]>>
      Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      FULL_CASE_TAC>>gvs[]>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      rename [‘ltree _ _ = FUNPOW _ _ (Ret (INR (q, r)))’]>>
      qmatch_asmsub_abbrev_tac ‘ltree _ (mrec _ (h_prog (pp, bst ss))) = _’>>
      disch_then $ qspecl_then [‘pp’,‘ss’,‘k’,‘(q,r)’,‘st’,‘res’] mp_tac>>
      simp[Abbr‘ss’,Abbr‘pp’]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* Seq *)
  >- (rpt (pairarg_tac>>fs[])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[FUNPOW_SUC]>>
      (* NONE *)
      Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      (rpt (FULL_CASE_TAC>>fs[])
       >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
           Cases_on ‘n’>>fs[FUNPOW_SUC]>>
           drule nondiv_ltree_bind_lemma'>>simp[]>>
           strip_tac>>fs[FUNPOW_Tau_bind]>>
           drule nondiv_INR>>strip_tac>>gs[]>>
           FULL_CASE_TAC>>fs[]>>gvs[]>>
           (*rename [‘Ret _ = FUNPOW Tau n _’]>>
           Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>*)
           rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
           last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
           disch_then $ drule_at Any>>
           disch_then $ drule_at Any>>
           strip_tac>>gvs[]>>
           rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
           last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
           pop_assum $ assume_tac o GSYM>>fs[]>>
           drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
           fs[]>>
           disch_then $ drule_at Any>>
           disch_then $ drule_at Any>>
           disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
           ‘s1 with clock := s1.clock = s1’
             by simp[state_component_equality]>>
           fs[]>>strip_tac>>
           imp_res_tac comp_ffi_bind>>gvs[]))>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      strip_tac>>res_tac>>fs[]>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* If *)
  >- (rpt (FULL_CASE_TAC>>fs[])>>
      gvs[AllCaseEqs()]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      drule nondiv_INR>>strip_tac>>gs[]>>
      FULL_CASE_TAC>>fs[]>>gvs[]>>
      rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      strip_tac>>gvs[]>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* While *)
  >- (rewrite_tac[Once mrec_While]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      strip_tac>>gvs[]>>
      FULL_CASE_TAC>>fs[]>>gvs[]>>
      TRY (imp_res_tac comp_ffi_bind>>gvs[]>>NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      qpat_x_assum ‘_ = SND _’ $ assume_tac o GSYM>>fs[]>>
      qpat_x_assum ‘evaluate (p',_)=_’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      disch_then $ rev_drule_at Any>>
      disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
      ‘s1 with clock := s1.clock = s1’
        by simp[state_component_equality]>>
      fs[]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* Call *)
  >- (
  rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>
  Cases_on ‘k=0’>>fs[]>>
  rename [‘Tau _ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
  drule nondiv_ltree_bind_lemma'>>simp[]>>
  strip_tac>>fs[FUNPOW_Tau_bind]>>
  imp_res_tac nondiv_INR>>fs[]>>gs[]>>
  gvs[]>>
  qpat_x_assum ‘_ = (res,t)’ mp_tac>>
  qpat_abbrev_tac ‘Y = evaluate _’>>
  rpt (TOP_CASE_TAC>>fs[])>>
  rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
  last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
  disch_then $ qspecl_then [‘q’,‘s with locals := r'’] mp_tac>>
  simp[]>>
  disch_then $ drule_at Any>>
  strip_tac>>gvs[]>>
  gvs[mrec_h_handle_call_ret_lemma,o_DEF,kvar_defs2,AllCaseEqs()]>>
  rpt (PURE_TOP_CASE_TAC>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>rw[]>>gvs[]>>
  TRY (imp_res_tac comp_ffi_bind>>gvs[]>>
       rw[]>>gvs[empty_locals_defs,set_var_defs]>>
       NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gvs[]>>
      FULL_CASE_TAC>>fs[]>>
      rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      qpat_x_assum ‘_ = SND _’ $ assume_tac o GSYM>>fs[]>>
      qpat_x_assum ‘evaluate _ = (SOME (Exception _ _), _)’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,s1)=(res,t)’>>
      ‘r''.ffi = s1.ffi’ by simp[Abbr‘s1’]>>fs[]>>
      fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
      disch_then $ rev_drule_at Any>>
      ‘s1 with clock := s1.clock = s1’
        by simp[state_component_equality]>>
      fs[]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  (* DecCall *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>
      Cases_on ‘k=0’>>fs[]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gs[]>>
      gvs[]>>
      qpat_x_assum ‘_ = (res,t)’ mp_tac>>
      qpat_abbrev_tac ‘Y = evaluate _’>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ qspecl_then [‘q’,‘s with locals := r'’] mp_tac>>
      simp[]>>
      disch_then $ drule_at Any>>
      strip_tac>>gvs[]>>
      gvs[mrec_h_handle_deccall_ret_lemma,o_DEF,set_var_defs]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>rw[]>>gvs[]>>
      TRY (imp_res_tac comp_ffi_bind>>gvs[]>>
           rw[]>>gvs[empty_locals_defs,set_var_defs]>>
           NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>simp[]>>
      strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>gvs[]>>
      FULL_CASE_TAC>>fs[]>>
      rename [‘ltree (_,SND _) _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      qpat_x_assum ‘_ = SND _’ $ assume_tac o GSYM>>fs[]>>
      qpat_x_assum ‘evaluate _ = (SOME (Return _), _)’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,s1)=(res,t)’>>
      ‘r''.ffi = s1.ffi’ by simp[Abbr‘s1’]>>fs[]>>
      fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ qspecl_then [‘s1.clock’] mp_tac>>
      disch_then $ rev_drule_at Any>>
      ‘s1 with clock := s1.clock = s1’
        by simp[state_component_equality]>>
      fs[]>>strip_tac>>
      imp_res_tac comp_ffi_bind>>gvs[])
  >- (rpt (FULL_CASE_TAC>>fs[])>>gvs[])>>
  (* ShMemLoad / ShMemStore *)
  rpt (TOP_CASE_TAC>>fs[])>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  gvs[set_var_defs,bst_def,AllCaseEqs()]
QED

Theorem nondiv_evaluate':
  ltree fs (mrec h_prog (h_prog (p,bst s))) =
  FUNPOW Tau n (Ret (INR r)) : 'a ptree
  ∧ evaluate (p,s with clock := k) = (res, t) ∧ res ≠ SOME TimeOut ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
  res = FST r ∧ bst t = SND r ∧
  t.ffi.ffi_state = SND (comp_ffi (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))))
Proof
  strip_tac>>
  Cases_on ‘fs’>>gs[]>>
  imp_res_tac nondiv_evaluate>>gvs[]
QED

(******* evaluate <-> Ret ************)

Theorem evaluate_imp_nondiv:
  evaluate (p,s) = (res,t) ∧ res ≠ SOME TimeOut ⇒
  ∃n. ltree (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘evaluate _ = (_,_)’ mp_tac>>
  simp[Once evaluate_def,mrec_prog_simps]>>strip_tac>>
  TRY (rpt (TOP_CASE_TAC>>fs[empty_locals_defs,kvar_defs2])>>
       qexists ‘0’>>simp[FUNPOW]>>NO_TAC)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      pairarg_tac>>fs[]>>gvs[]>>
      qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>
      gvs[FUNPOW_Tau_bind])
  >- (* shmemload *)
   (simp[mrec_ShMemLoad]>>
    fs[sh_mem_load_def,call_FFI_def,kvar_defs2,AllCaseEqs()]>>
    gvs[bst_def,empty_locals_defs]>>
    metis_tac[FUNPOW])
  >- (* shmemstore *)
   (simp[mrec_ShMemStore]>>
    fs[sh_mem_store_def,call_FFI_def,set_var_defs,AllCaseEqs()]>>
    gvs[bst_def,empty_locals_defs]>>
    metis_tac[FUNPOW])
  >~ [‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    fs[sh_mem_store_def,call_FFI_def,set_var_defs,AllCaseEqs()]>>
    rpt (TOP_CASE_TAC>>fs[])>>
    gvs[empty_locals_defs,bst_def,explode_eq_implode,implode_def]>>
    metis_tac[FUNPOW])
  >- (* Seq *)
   (rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    simp[mrec_Seq,FUNPOW_Tau_bind]>>
    drule nondiv_evaluate>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘evaluate (c1,_) = (rr,tt)’>>
    disch_then $ qspecl_then [‘tt’,‘rr’,‘s.clock’] mp_tac>>
    ‘s with clock := s.clock = s’ by simp[state_component_equality]>>
    simp[]>>
    fs[]>>strip_tac>>TRY (fs[Abbr‘rr’])>>
    pop_assum $ assume_tac o GSYM>>fs[]>>
    ‘s.ffi.oracle = tt.ffi.oracle’ by
      (irule EQ_SYM>>irule evaluate_invariant_oracle>>metis_tac[])>>
    gvs[FUNPOW_Tau_bind]>>
    simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
    rpt (FULL_CASE_TAC>>fs[]))
   >- (* If *)
    (simp[mrec_If]>>
     rpt (TOP_CASE_TAC>>fs[])>>gvs[FUNPOW_Tau_bind]>>
     metis_tac[FUNPOW,FUNPOW_SUC])
  >- (* While *)
   (simp[Once mrec_While,dec_clock_def]>>
    TOP_CASE_TAC>>fs[]>>
    reverse TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    TOP_CASE_TAC>>fs[]>>
    rpt (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[dec_clock_def,FUNPOW_Tau_bind]>>
    TRY (simp[GSYM FUNPOW_SUC]>>qrefine ‘SUC n'’>>simp[]>>NO_TAC)>>
    qpat_x_assum ‘ltree (s.ffi.oracle,_) _ = _’ assume_tac>>
    drule nondiv_evaluate'>>gvs[]>>
    disch_then $ drule_at Any>>
    simp[]>>strip_tac>>
    pop_assum $ assume_tac o GSYM>>fs[]>>
    ‘(s with clock := s.clock -1).ffi.oracle = s1.ffi.oracle’ by
      (irule EQ_SYM>>irule evaluate_invariant_oracle>>metis_tac[])>>
    gvs[FUNPOW_Tau_bind]>>
    simp[GSYM FUNPOW_SUC]>>rewrite_tac[GSYM FUNPOW_ADD]>>
    metis_tac[FUNPOW_SUC])
  >- (rpt (FULL_CASE_TAC>>fs[])>>
      gvs[dec_clock_def,empty_locals_defs]>>
      metis_tac[FUNPOW])>>
  (* Call / DecCall *)
  simp[mrec_Call,mrec_DecCall]>>
  fs[AllCaseEqs(),kvar_defs2,
     empty_locals_defs,dec_clock_def,FUNPOW_Tau_bind]>>
  rpt (pairarg_tac>>fs[])>>
  simp[mrec_h_handle_call_ret_lemma]>>
  gvs[FUNPOW_Tau_bind]>>
  TRY (qexists ‘0’>>simp[FUNPOW]>>NO_TAC)>>
  drule nondiv_evaluate'>>gvs[]>>
  disch_then $ drule_at Any>>
  strip_tac>>fs[]>>
  pop_assum $ assume_tac o GSYM>>fs[]>>
  ‘(s with <|locals :=newlocals;clock :=s.clock -1|>).ffi.oracle = st.ffi.oracle’ by
    (irule EQ_SYM>>irule evaluate_invariant_oracle>>metis_tac[])>>
  simp[mrec_h_handle_call_ret_lemma,empty_locals_defs,kvar_defs2,
       mrec_h_handle_deccall_ret_lemma]>>
  gvs[FUNPOW_Tau_bind]>>
  TRY (TOP_CASE_TAC>>fs[])>>
  simp[GSYM FUNPOW_SUC]>>rewrite_tac[GSYM FUNPOW_ADD]>>
  metis_tac[FUNPOW_SUC]
QED

Theorem nondiv_not_timeout:
  ltree fs (mrec h_prog (h_prog (p,s))) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree ⇒
  res ≠ SOME TimeOut
Proof
  map_every qid_spec_tac [‘res’,‘fs’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>strip_tac>>
  Cases_on ‘p’
  >~ [‘ExtCall’]>-
   (fs[mrec_ExtCall,call_FFI_def]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>
    rename [‘_ = FUNPOW Tau n _’]>>
    Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         Cases_on ‘n’>>fs[FUNPOW_SUC])>>
    gvs[set_var_defs,bst_def,empty_locals_defs])>>
  fs[mrec_prog_simps,mrec_Seq,mrec_If,Once mrec_While,mrec_Call,
     mrec_DecCall,
     mrec_ExtCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
     panPropsTheory.eval_upd_clock_eq,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  rpt (FULL_CASE_TAC>>fs[])>>fs[FUNPOW_SUC]>>
  TRY (rename [‘Tau _ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
       drule nondiv_ltree_bind_lemma'>>
       simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
       imp_res_tac nondiv_INR>>fs[]>>
       FULL_CASE_TAC>>fs[]>>
       rename [‘ltree _ _ = FUNPOW Tau n _’]>>
       qmatch_asmsub_abbrev_tac ‘h_prog (pp,ss)’>>
       qmatch_asmsub_abbrev_tac ‘ltree _ _ = FUNPOW _ n (Ret (INR (q,rr)))’>>
       last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
       first_x_assum $ qspecl_then [‘pp’,‘ss’,‘rr’,‘fs’] assume_tac>>fs[]>>
       gvs[])
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])
      (* NONE *)
      >- (rename [‘_ _ = FUNPOW Tau n _’]>>
          Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
          drule nondiv_ltree_bind_lemma'>>
          simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
          fs[GSYM FUNPOW_ADD]>>gs[]>>
          imp_res_tac nondiv_INR>>fs[]>>
          FULL_CASE_TAC>>fs[]>>
          rename [‘ltree _ _ = FUNPOW Tau n _’]>>
          last_x_assum $ qspec_then ‘n’ assume_tac>>gvs[]>>
          qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (q,rr)))’>>
          first_x_assum $ qspecl_then [‘p0’,‘r’,‘rr’,‘fs'’] assume_tac>>
          gvs[])>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>gvs[]>>
      metis_tac[])
  (* While *)
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      gvs[GSYM FUNPOW_SUC]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      rename [‘ltree (_, SND _ ) _ = FUNPOW Tau n _’]>>
      qmatch_asmsub_abbrev_tac ‘h_prog (While _ _,rr)’>>
      qmatch_asmsub_abbrev_tac ‘h_prog (pp,rr)’>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (qq,tt)))’>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
      first_x_assum $ qspecl_then [‘pp’,‘rr’,‘tt’,‘fs'’] assume_tac>>
      gvs[Abbr‘qq’])
  (* call *)
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      fs[mrec_h_handle_call_ret_lemma]>>
      rename [‘FUNPOW _ n (Ret (INR (res,t)))’]>>
      qpat_x_assum ‘_ = FUNPOW _ n _’ mp_tac>>
      rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>rw[]>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      FULL_CASE_TAC>>fs[]>>gvs[]>>
      fs[set_var_defs]>>
      rename [‘ltree (_, SND _ ) _ = FUNPOW Tau n _’]>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (qq,tt)))’>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' (_ _ (_ (pp,rr)))’>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
      first_x_assum $ qspecl_then [‘pp’,‘rr’,‘tt’,‘fs'’] assume_tac>>
      gvs[])
  (* deccall *)
  >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs]>>
      rename [‘FUNPOW _ n (Ret (INR (res,t)))’]>>
      qpat_x_assum ‘_ = FUNPOW _ n _’ mp_tac>>
      rpt (TOP_CASE_TAC>>fs[])>>rw[]
      >- (fs[]>>‘n'' < SUC n''’ by simp[]>>res_tac)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      FULL_CASE_TAC>>gvs[set_var_defs]>>
      rename [‘ltree (_, SND _ ) _ = FUNPOW Tau n _’]>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' _ = FUNPOW _ n (Ret (INR (qq,tt)))’>>
      qmatch_asmsub_abbrev_tac ‘ltree fs' (_ _ (_ (pp,rr)))’>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>fs[]>>
      first_x_assum $ qspecl_then [‘pp’,‘rr’,‘tt’,‘fs'’] assume_tac>>
      gvs[])>>
  rename [‘_ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  TRY (rename [‘_ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC])>>
  gvs[set_var_defs,bst_def,empty_locals_defs]
QED

Theorem nondiv_imp_evaluate:
  ltree (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree ⇒
    ∃k t'. evaluate (p,s with clock := k) = (res,t')
           ∧ bst t' = t
         ∧ res ≠ SOME TimeOut
Proof
  strip_tac>>
  imp_res_tac nondiv_not_timeout>>
  pop_assum mp_tac>>
  pop_assum mp_tac>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>ntac 2 strip_tac>>
  Cases_on ‘p’
  >~ [‘ExtCall’] >-
   (fs[Once evaluate_def,mrec_ExtCall,call_FFI_def,
       panPropsTheory.eval_upd_clock_eq]>>
    rpt (PURE_CASE_TAC>>fs[])>>gvs[]>>
    gvs[dec_clock_def,empty_locals_defs,explode_eq_implode,implode_def]>>
    rpt (rename [‘FUNPOW Tau n _’]>>
         Cases_on ‘n’>>gvs[FUNPOW_SUC])>>
    simp[bst_def,empty_locals_defs,set_var_defs])>>
  fs[mrec_prog_simps,mrec_Seq,mrec_If,Once mrec_While,mrec_Call,
     mrec_DecCall,Once evaluate_def,
     mrec_ExtCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
     panPropsTheory.eval_upd_clock_eq,
     sh_mem_load_def,sh_mem_store_def,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  gvs[FUNPOW_SUC]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>gvs[empty_locals_defs,kvar_defs2]>>
       rename [‘Ret _ = FUNPOW Tau n _’]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>
       TRY (rpt (TOP_CASE_TAC>>fs[])>>gvs[]>>
            rename [‘_ _ = FUNPOW Tau n _’]>>
            Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])>>NO_TAC)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>fs[]>>
      qmatch_asmsub_abbrev_tac ‘h_prog (pp,bst ss)’>>
      qmatch_asmsub_abbrev_tac ‘Ret (INR (res,rr))’>>
      disch_then $ qspecl_then [‘pp’,‘ss’,‘rr’,‘res’] assume_tac>>
      gvs[Abbr‘ss’]>>
      qexists ‘k’>>fs[])
  (* Seq *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])
      >- (rename [‘Tau _ = FUNPOW Tau n _’]>>
          Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
          drule nondiv_ltree_bind_lemma'>>
          simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
          imp_res_tac nondiv_INR>>fs[]>>
          rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
          last_assum $ qspec_then ‘n''’ mp_tac>>
          (impl_tac >- simp[])>>
          disch_then drule>>strip_tac>>fs[]>>
          dxrule evaluate_min_clock>>
          strip_tac>>fs[]>>
          drule_then drule nondiv_evaluate'>>simp[]>>strip_tac>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          imp_res_tac evaluate_invariant_oracle>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          qhdtm_x_assum ‘bst’ $ assume_tac o GSYM>>fs[]>>
          rename [‘ltree _ _ = FUNPOW Tau n _’]>>
          last_x_assum $ qspec_then ‘n’ mp_tac>>
          (impl_tac >- simp[])>>
          disch_then rev_drule>>simp[]>>
          strip_tac>>fs[]>>
          dxrule evaluate_min_clock>>simp[]>>
          strip_tac>>fs[]>>
          qexists ‘k' + k''’>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          disch_then $ qspec_then ‘k''’ assume_tac>>fs[])>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      disch_then drule>>strip_tac>>gvs[]>>
      qexists ‘k’>>simp[])
  >- (rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      Cases_on ‘n'''’>>fs[FUNPOW_SUC]>>gvs[])
  (* While *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[dec_clock_def]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      rename [‘ltree _ _ = FUNPOW Tau n _’]>>
      last_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      disch_then drule>>strip_tac>>fs[]>>
      TRY (qexists ‘SUC k’>>fs[]>>NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      dxrule evaluate_min_clock>>
      strip_tac>>fs[]>>
      drule_then drule nondiv_evaluate'>>simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      imp_res_tac evaluate_invariant_oracle>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      rename1 ‘ltree (_,t''.ffi.ffi_state) _ = FUNPOW Tau n _’>>
      last_x_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      disch_then drule>>simp[]>>
      strip_tac>>fs[]>>
      dxrule evaluate_min_clock>>simp[]>>
      strip_tac>>fs[]>>
      qexists ‘SUC (k' + k'')’>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘k''’ assume_tac>>fs[])
  (* call *)
  >- (rpt (PURE_CASE_TAC>>fs[])>>gvs[dec_clock_def,empty_locals_defs]>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[]>>
      fs[mrec_h_handle_call_ret_lemma,kvar_defs2]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      rename [‘_ = FUNPOW Tau n _’]>>
      TRY (last_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
           ‘s.ffi = (s with locals := r).ffi’ by simp[]>>
           rename [‘h_prog (q, bst _)’]>>
           disch_then $ qspecl_then [‘q’,‘s with locals := r’] mp_tac>>
           fs[]>>strip_tac>>
           qexists ‘SUC k’>>gvs[bst_def]>>NO_TAC)>>
      TRY (rename [‘Tau _ = FUNPOW Tau n _’]>>
           Cases_on ‘n’>>gvs[FUNPOW_SUC,empty_locals_defs]>>
           drule nondiv_ltree_bind_lemma'>>
           simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
           fs[GSYM FUNPOW_ADD]>>gs[]>>
           imp_res_tac nondiv_INR>>fs[]>>
           rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[])>>
      rename1 ‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’>>
      last_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      rename [‘h_prog (q, bst _)’]>>
      disch_then $ qspecl_then [‘q’,‘s with locals := r’] mp_tac>>
      disch_then $ mp_tac o SIMP_RULE (srw_ss()) []>>
      disch_then drule>>strip_tac>>fs[]>>
      dxrule evaluate_min_clock>>strip_tac>>gvs[]>>
      TRY (qexists ‘SUC k'’>>simp[]>>
           rpt (FULL_CASE_TAC>>fs[])>>gvs[kvar_defs2]>>NO_TAC)>>
      rev_drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      fs[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      imp_res_tac evaluate_invariant_oracle>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      rename1 ‘ltree (_,t''.ffi.ffi_state) _ = FUNPOW Tau n' _’>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>
      (impl_tac >- simp[])>>
      fs[set_var_defs]>>
      TRY (qhdtm_x_assum ‘bst’ $ assume_tac o GSYM)>>fs[]>>
      qpat_x_assum ‘ltree _ _ = FUNPOW _ _ (Ret _)’ assume_tac>>
      qmatch_asmsub_abbrev_tac ‘h_prog (rrr, bst X)’>>
      ‘t''.ffi = X.ffi’ by simp[Abbr‘X’]>>fs[]>>
      disch_then drule>>strip_tac>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>pop_assum kall_tac>>
      strip_tac>>gvs[Abbr‘X’]>>
      qexists ‘SUC (k' + k'')’>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>fs[]>>
      disch_then $ qspec_then ‘k''’ assume_tac>>fs[])
  (* deccall *)
  >- (rpt (PURE_CASE_TAC>>fs[])>>gvs[dec_clock_def,empty_locals_defs]>>
      rename [‘_ _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[]>>
      fs[mrec_h_handle_deccall_ret_lemma]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      TRY (last_x_assum $ qspec_then ‘n''’ mp_tac>>simp[]>>
           ‘s.ffi = (s with locals := r).ffi’ by simp[]>>
           rename [‘h_prog (q, bst _)’]>>
           disch_then $ qspecl_then [‘q’,‘s with locals := r’] mp_tac>>
           fs[]>>strip_tac>>
           qexists ‘SUC k’>>gvs[bst_def]>>NO_TAC)>>
      rename [‘Tau _ = FUNPOW Tau n _’]>>
      Cases_on ‘n’>>gvs[FUNPOW_SUC,empty_locals_defs]>>
      drule nondiv_ltree_bind_lemma'>>
      simp[]>>strip_tac>>fs[FUNPOW_Tau_bind]>>
      fs[GSYM FUNPOW_ADD]>>gs[]>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘r' = INR x'’]>>Cases_on ‘x'’>>gvs[]>>
      rename1 ‘ltree (_,s.ffi.ffi_state) _ = FUNPOW Tau n _’>>
      last_assum $ qspec_then ‘n’ mp_tac>>
      (impl_tac >- simp[])>>
      rename [‘h_prog (q, bst _)’]>>
      qpat_x_assum ‘ltree _ _ = FUNPOW _ n (Ret _)’ assume_tac>>
      qmatch_asmsub_abbrev_tac ‘h_prog (pp, bst X)’>>
      disch_then $ qspecl_then [‘pp’,‘X’] mp_tac>>
      ‘X.ffi = s.ffi’ by fs[Abbr‘X’]>>
      pop_assum (fn h => rewrite_tac[h])>>
      disch_then drule>>rw[]>>
      dxrule evaluate_min_clock>>strip_tac>>gvs[]>>
      rev_drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      fs[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      imp_res_tac evaluate_invariant_oracle>>
      pop_assum $ assume_tac o GSYM>>fs[Abbr‘X’]>>
      rename1 ‘ltree (_,t''.ffi.ffi_state) _ = FUNPOW Tau n' _’>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      fs[set_var_defs]>>
      qmatch_asmsub_abbrev_tac ‘h_prog (p', bst X)’>>
      ‘t''.ffi = X.ffi’ by simp[Abbr‘X’]>>fs[]>>
      disch_then drule>>strip_tac>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>pop_assum kall_tac>>
      strip_tac>>gvs[Abbr‘X’]>>
      qexists ‘SUC (k' + k'')’>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>fs[]>>
      disch_then $ qspec_then ‘k''’ assume_tac>>fs[])>>
  rpt (PURE_CASE_TAC>>fs[])>>
(*  rename [‘_ _ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>*)
  gvs[dec_clock_def,empty_locals_defs,kvar_defs2]>>
  rpt (PURE_CASE_TAC>>fs[])>>
  rpt (rename [‘FUNPOW Tau n _’]>>
       Cases_on ‘n’>>gvs[FUNPOW_SUC])>>
  simp[bst_def,empty_locals_defs,set_var_defs]>>
  qexists ‘SUC 0’>>gvs[]
QED

Theorem nondiv_imp_evaluate':
  ltree fs (mrec h_prog (h_prog (p,bst s))) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree
  ∧ FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
    ∃k t'. evaluate (p,s with clock := k) = (res,t')
           ∧ bst t' = t
         ∧ res ≠ SOME TimeOut
Proof
  Cases_on ‘fs’>>rw[]>>metis_tac[nondiv_imp_evaluate]
QED

(**************************)

Theorem div_imp_timeout:
  div fs (mrec h_prog (h_prog (p,bst s))) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
  ∀k. ∃t. evaluate (p,s with clock := k) = (SOME TimeOut,t)
Proof
  CCONTR_TAC>>fs[]>>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,ss)’>>
  ‘bst s = bst ss ∧ s.ffi = ss.ffi’
    by simp[bst_def,Abbr‘ss’]>>fs[]>>
  Cases_on ‘evaluate (p,ss)’>>fs[]>>
  drule_all evaluate_imp_nondiv>>strip_tac>>
  last_x_assum mp_tac>>gvs[]>>
  Cases_on ‘fs’>>gs[]
QED

Theorem evaluate_nondiv_trace_eq:
  evaluate (p,s) = (r,t) ∧ r ≠ SOME TimeOut ⇒
  fromList t.ffi.io_events =
  LAPPEND (fromList s.ffi.io_events)
          (trace_prefix (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))))
Proof
  map_every qid_spec_tac [‘r’,‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘evaluate _ = _’ mp_tac
  >~ [‘ExtCall’] >-
   (simp[Once evaluate_def,mrec_ExtCall,call_FFI_def]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    strip_tac>>gvs[LAPPEND_NIL_2ND]>>
    fs[LAPPEND_NIL_2ND,dec_clock_def,
       empty_locals_defs,GSYM LAPPEND_fromList,explode_eq_implode,implode_def])>>
  simp[mrec_prog_simps,
       mrec_If,
       Once evaluate_def,kvar_defs2,
       mrec_ExtCall,call_FFI_def,mrec_ShMemLoad,mrec_ShMemStore,
       panPropsTheory.eval_upd_clock_eq,
       sh_mem_load_def,sh_mem_store_def,
       panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  gvs[FUNPOW_SUC,LAPPEND_NIL_2ND]
  >~ [‘Seq’] >-
   (pairarg_tac>>fs[]>>
    simp[mrec_Seq]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    strip_tac>>gvs[]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    imp_res_tac trace_prefix_bind_append>>fs[]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]
    >- (AP_TERM_TAC>>
        rev_drule nondiv_evaluate'>>
        disch_then $ qspecl_then [‘s1’,‘NONE’,‘s.clock’] assume_tac>>
        fs[]>>
        ‘s with clock := s.clock = s’
          by simp[state_component_equality]>>
        gs[]>>pop_assum kall_tac>>
        pop_assum (assume_tac o GSYM)>>fs[]>>
        rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
        fs[]>>
        simp[LAPPEND_NIL_2ND])>>
    CASE_TAC>>fs[]>>
    simp[LAPPEND_NIL_2ND])
  >~ [‘While’] >-
   (fs[dec_clock_def,empty_locals_defs]>>
    simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    rpt (pairarg_tac>>fs[])>>gvs[]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    rpt (CASE_TAC>>fs[])>>
    strip_tac>>gvs[LAPPEND_NIL_2ND]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]>>
    imp_res_tac trace_prefix_bind_append>>gs[]>>
    simp[LAPPEND_NIL_2ND]>>
    rev_drule nondiv_evaluate'>>
    qmatch_asmsub_abbrev_tac ‘evaluate _ = (res0,s1)’>>
    disch_then $ qspecl_then [‘s1’,‘res0’,‘s.clock-1’] assume_tac>>
    fs[]>>
    gs[Abbr‘res0’]>>
    pop_assum (assume_tac o GSYM)>>fs[]>>
    rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
    fs[])
  >~ [‘Call’]>-
   (simp[mrec_Call,empty_locals_defs,dec_clock_def]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    rpt (pairarg_tac>>fs[])>>gvs[dec_clock_def]>>
    strip_tac>>
    gvs[LAPPEND_NIL_2ND,dec_clock_def,set_var_defs]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    imp_res_tac trace_prefix_bind_append>>gs[]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]>>
    gvs[mrec_h_handle_call_ret_lemma,LAPPEND_NIL_2ND,kvar_defs2,LAPPEND_ASSOC]>>
    rpt (CASE_TAC>>fs[])>>fs[LAPPEND_NIL_2ND]>>
    qpat_x_assum ‘evaluate (q'',_) = _’ assume_tac>>
    rev_drule nondiv_evaluate'>>
    qmatch_asmsub_abbrev_tac ‘evaluate (q'',_) = (res0,s1)’>>
    disch_then $ qspecl_then [‘s1’,‘res0’,‘s.clock-1’] assume_tac>>
    gvs[Abbr‘res0’]>>
    pop_assum (assume_tac o GSYM)>>fs[]>>
    drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
    fs[LAPPEND_NIL_2ND])
  >~ [‘DecCall’]>-
   (simp[mrec_DecCall,empty_locals_defs,set_var_defs,dec_clock_def]>>
    rpt (CASE_TAC>>fs[LAPPEND_NIL_2ND])>>
    rpt (pairarg_tac>>fs[])>>gvs[dec_clock_def]>>
    strip_tac>>
    gvs[LAPPEND_NIL_2ND,dec_clock_def,set_var_defs]>>
    imp_res_tac evaluate_imp_nondiv>>fs[]>>
    imp_res_tac trace_prefix_bind_append>>gs[]>>
    simp[Once LAPPEND_ASSOC]>>
    simp[LFINITE_fromList,LAPPEND11_FINITE1]>>
    gvs[mrec_h_handle_deccall_ret_lemma,
        LAPPEND_NIL_2ND,set_var_defs]>>
    qpat_x_assum ‘evaluate (q,_) = _’ assume_tac>>
    rev_drule nondiv_evaluate'>>
    qmatch_asmsub_abbrev_tac ‘evaluate (q,_) = (res0,s1)’>>
    disch_then $ qspecl_then [‘s1’,‘res0’,‘s.clock-1’] assume_tac>>
    gvs[Abbr‘res0’]>>
    pop_assum (assume_tac o GSYM)>>fs[]>>
    drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
    fs[LAPPEND_NIL_2ND])>>
  rpt (CASE_TAC>>fs[])>>
  rpt (pairarg_tac>>fs[])>>gvs[]>>
  rpt (PURE_FULL_CASE_TAC>>fs[])>>
  strip_tac>>gvs[LAPPEND_NIL_2ND]>>
  imp_res_tac evaluate_imp_nondiv>>
  imp_res_tac trace_prefix_bind_append>>
  fs[LAPPEND_NIL_2ND,dec_clock_def,
     empty_locals_defs,GSYM LAPPEND_fromList]
QED

(**** divergence ****)

Theorem nondiv_timeout_add_clock:
  evaluate (p,s) = (SOME TimeOut, t) ∧
  ltree fs ((mrec h_prog (h_prog (p,bst s))):'a ptree) =
  FUNPOW Tau n (Ret r): 'a ptree ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ⇒
  ∃k q t'. evaluate (p,s with clock := s.clock + k) = (q, t') ∧
           r = INR (q, bst t') ∧ q ≠ SOME TimeOut ∧
           ∃l. t'.ffi.io_events = t.ffi.io_events ++ l
Proof
  rw[]>>
  imp_res_tac nondiv_INR>>fs[]>>
  rename [‘INR x’]>>Cases_on ‘x’>>
  Cases_on ‘fs’>>fs[]>>
  drule nondiv_imp_evaluate>>rw[]>>
  Cases_on ‘s.clock < k’>>fs[NOT_LESS]
  >- (imp_res_tac (GSYM LESS_ADD)>>
  mp_tac (Q.SPECL [‘p’,‘s’,‘p'’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
      rw[IS_PREFIX_APPEND]>>gvs[]>>
      qexists ‘p'’>>metis_tac[])>>
  imp_res_tac (GSYM LESS_EQUAL_ADD)>>fs[]>>
  drule panPropsTheory.evaluate_add_clock_eq>>
  disch_then $ qspec_then ‘p'’ assume_tac>>fs[]>>
  gvs[]>>
  ‘s with clock := s.clock = s’
  by simp[state_component_equality]>>gvs[]
QED

Theorem timeout_div_LPREFIX:
  evaluate (p,s) = (SOME TimeOut, t) ∧
  div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) ⇒
  LPREFIX
  (fromList t.ffi.io_events)
  (LAPPEND (fromList s.ffi.io_events)
           (trace_prefix (s.ffi.oracle,s.ffi.ffi_state) ((mrec h_prog (h_prog (p,bst s))):'a ptree)))
Proof
  map_every qid_spec_tac [‘t’,‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  qpat_x_assum ‘evaluate _ = _’ mp_tac>>
  simp[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>
  fs[mrec_prog_simps,kvar_defs2]>>
  TRY (
    rpt (TOP_CASE_TAC>>fs[])>>
    strip_tac>>
    rpt (pairarg_tac>>fs[])>>gvs[]>>NO_TAC)
  >- (rpt (CASE_TAC>>fs[])>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘X ⇒ _’>>
      Cases_on ‘X’>>fs[]
      >- (imp_res_tac trace_prefix_bind_div>>fs[])>>
      imp_res_tac div_bind2>>fs[])

  (* Seq *)
  >- (qhdtm_x_assum ‘div’ mp_tac>>
      simp[mrec_Seq]>>
      rpt (pairarg_tac>>fs[])>>
      rpt (CASE_TAC>>fs[])>>strip_tac>>strip_tac
      >- (imp_res_tac evaluate_imp_nondiv>>fs[]>>
          drule_all (iffLR div_bind2)>>strip_tac>>gvs[]>>
          drule nondiv_evaluate'>>
          disch_then $ qspecl_then [‘s1’,‘NONE’,‘s.clock’] mp_tac>>
          ‘s with clock := s.clock = s’
            by simp[state_component_equality]>>gvs[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          fs[LAPPEND_ASSOC]>>
          gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>fs[]>>
          gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          qmatch_goalsub_abbrev_tac ‘trace_prefix fs _’>>
          qmatch_goalsub_abbrev_tac ‘itree_bind X _’>>
          Cases_on ‘div fs X’>>fs[]
          >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
              metis_tac[])>>
          fs[Abbr‘fs’,Abbr‘X’]>>
          drule_then drule nondiv_timeout_add_clock>>rw[]>>
          mp_tac (Q.SPECL [‘c2’,‘s1’,‘k’] panPropsTheory.evaluate_add_clock_io_events_mono)>>
          rw[IS_PREFIX_APPEND]>>
          drule (SRULE [PULL_EXISTS] trace_prefix_bind_append)>>
          rw[LAPPEND_NIL_2ND]>>
          drule_all evaluate_nondiv_trace_eq>>
          rw[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[LAPPEND_ASSOC]>>
          gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          pop_assum $ assume_tac o GSYM>>fs[]>>metis_tac[])>>
      gvs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[])>>
      drule_then drule nondiv_timeout_add_clock>>rw[]>>fs[]>>
      FULL_CASE_TAC>>fs[]>>
      drule nondiv_evaluate'>>
      disch_then $ drule_at Any>>simp[]>>rw[]>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      fs[LAPPEND_ASSOC]>>
      gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      qhdtm_x_assum ‘LAPPEND’ $ assume_tac o GSYM>>fs[]>>
      gs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      fs[LAPPEND_ASSOC]>>
      gs[LFINITE_fromList,LAPPEND11_FINITE1])
  >- (fs[mrec_If]>>
      rpt (CASE_TAC>>fs[])>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘X ⇒ _’>>
      (Cases_on ‘X’>>fs[]
       >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
      imp_res_tac div_bind2>>fs[])
  (* While *)
  >- (pop_assum mp_tac>>
      once_rewrite_tac[mrec_While]>>
      rpt (TOP_CASE_TAC>>fs[])
      >- (rw[]>>gvs[empty_locals_defs]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1])>>
      strip_tac>>
      rpt (pairarg_tac>>fs[])>>
      rpt (CASE_TAC>>fs[])>>
      strip_tac>>fs[empty_locals_defs,dec_clock_def]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      imp_res_tac IS_PREFIX_APPEND>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]
      >-
       (rev_drule evaluate_imp_nondiv>>
        simp[]>>strip_tac>>
        imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
        imp_res_tac trace_prefix_bind_append>>gvs[]>>
        fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
        fs[LAPPEND_ASSOC]>>
        fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
        qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
        simp[LAPPEND_ASSOC]>>
        fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
        drule div_bind2>>strip_tac>>fs[]>>
        drule_then drule nondiv_evaluate'>>
        simp[]>>strip_tac>>
        pop_assum $ assume_tac o GSYM>>fs[]>>
        rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
        gs[]>>metis_tac[])
      >-
       (gvs[div_bind_cases]
        >- (imp_res_tac trace_prefix_bind_div>>fs[]>>metis_tac[])>>
        drule nondiv_timeout_add_clock>>simp[]>>
        disch_then $ drule_at Any>>rw[]>>fs[]>>
        FULL_CASE_TAC>>fs[]>>
        drule nondiv_evaluate'>>
        disch_then $ drule_at Any>>simp[]>>rw[]>>
        pop_assum $ assume_tac o GSYM>>fs[]>>
        drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
        fs[]>>
        drule_then assume_tac panPropsTheory.evaluate_io_events_mono>>
        fs[IS_PREFIX_APPEND]>>gvs[]>>
        imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
        imp_res_tac trace_prefix_bind_append>>gvs[]>>
        fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
        fs[LAPPEND_ASSOC]>>
        fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
        qhdtm_x_assum ‘LAPPEND’ $ assume_tac o GSYM>>fs[]>>
        fs[LAPPEND_ASSOC]>>
        metis_tac[])>>
      rev_drule evaluate_imp_nondiv>>simp[]>>
      strip_tac>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      simp[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      drule div_bind2>>strip_tac>>fs[]>>
      drule_then drule nondiv_evaluate'>>
      simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      gs[]>>metis_tac[])>>
  (* Call / DecCall *)
  (pop_assum mp_tac>>
   simp[mrec_Call,mrec_DecCall]>>
   rpt (TOP_CASE_TAC>>fs[])
   >- (rw[]>>gvs[empty_locals_defs]>>
       fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
       fs[LFINITE_fromList,LAPPEND11_FINITE1])>>
   rw[]>>fs[dec_clock_def,empty_locals_defs,set_var_defs]
   >-
    ((gvs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
     drule nondiv_timeout_add_clock>>simp[]>>
     disch_then $ drule_at Any>>rw[]>>
     drule nondiv_evaluate'>>
     disch_then $ drule_at Any>>
     disch_then $ qspecl_then [‘t'’,‘k + s.clock - 1’] mp_tac>>gs[]>>
     disch_then $ assume_tac o GSYM>>fs[]>>
     drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
     fs[]>>
     imp_res_tac panPropsTheory.evaluate_io_events_mono>>
     fs[IS_PREFIX_APPEND]>>gvs[]>>
     imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
     imp_res_tac trace_prefix_bind_append>>gvs[]>>
     fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
     fs[LAPPEND_ASSOC]>>
     fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
     qhdtm_x_assum ‘LAPPEND’ $ assume_tac o GSYM>>
     simp[LAPPEND_ASSOC]>>
     fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
     fs[mrec_h_handle_call_ret_lemma,
        mrec_h_handle_deccall_ret_lemma,kvar_defs2])>>
   rpt (pairarg_tac>>fs[])>>
   rev_drule evaluate_imp_nondiv>>
   simp[]>>strip_tac>>
   imp_res_tac panPropsTheory.evaluate_io_events_mono>>
   fs[IS_PREFIX_APPEND]>>gvs[]>>
   imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
   imp_res_tac trace_prefix_bind_append>>gvs[]>>
   fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
   fs[LAPPEND_ASSOC]>>
   fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
   qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
   simp[LAPPEND_ASSOC]>>
   fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
   drule_then dxrule (iffLR div_bind2)>>strip_tac>>fs[]>>
   gvs[mrec_h_handle_call_ret_lemma,
       mrec_h_handle_deccall_ret_lemma,kvar_defs2]>>
   drule nondiv_evaluate'>>fs[]>>
   disch_then $ drule_at Any>>
   simp[]>>strip_tac>>
   pop_assum $ assume_tac o GSYM>>fs[]>>
   rev_drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
   fs[]>>
   (gvs[div_bind_cases]
    >- (imp_res_tac trace_prefix_bind_div>>fs[]>>metis_tac[])))
QED

(* move to panProps? *)
Theorem not_less_opt_lemma:
  (∀k. ¬less_opt
       n (SOME
          (LENGTH
           (SND (evaluate (prog:'a panLang$prog,s with clock := k))).ffi.io_events))) ⇒
  ∃k'. (∀k. k' ≤ k ⇒
            LENGTH
            (SND (evaluate (prog,s with clock := k))).ffi.io_events =
            LENGTH
            (SND (evaluate (prog,s with clock := k'))).ffi.io_events)
Proof
  strip_tac>>
  fs[less_opt_def,NOT_LESS]>>
  qabbrev_tac ‘f = (λx. LENGTH (SND (evaluate (prog:'a panLang$prog,s with clock := x))).ffi.io_events)’>>
  fs[]>>
  ‘∀k k'. k ≤ k' ⇒ f k ≤ f k'’
    by (fs[Abbr‘f’]>>
        rpt strip_tac>>
        drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
        assume_tac (Q.SPECL [‘prog’,‘s with clock := k’,‘p’]
                     panPropsTheory.evaluate_add_clock_io_events_mono)>>
        fs[IS_PREFIX_APPEND])>>
  ‘∃k. ∀k'. k ≤ k' ⇒ f k' ≤  f k’ by
    (CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
     last_x_assum mp_tac>>fs[NOT_LESS_EQUAL]>>
     Cases_on ‘n < f k’>>fs[NOT_LESS]>- metis_tac[]>>
     drule LESS_EQUAL_ADD>>strip_tac>>
     gvs[]>>
     pop_assum mp_tac>>
     qid_spec_tac ‘p’>>
     Induct>>rw[]
     >- (first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
         qexists ‘k'’>>rw[])>>
     fs[PULL_FORALL]>>
     first_x_assum $ qspec_then ‘k'’ assume_tac>>fs[]>>
     simp[GSYM ADD_SUC,GSYM LESS_EQ_IFF_LESS_SUC]>>
     irule_at Any LESS_LESS_EQ_TRANS>>
     irule_at Any (iffRL LESS_MONO_EQ)>>
     first_assum $ irule_at Any>>
     simp[LESS_EQ_IFF_LESS_SUC]>>
     metis_tac[])>>
  qexists ‘k’>>rw[]>>
  metis_tac[LESS_EQUAL_ANTISYM]
QED

(*** some analysis on termination at Vis ***)

Theorem mrec_Ret_evaluate:
  mrec h_prog (h_prog (p,s)) = Ret (INR (res, t)):'a ptree ⇒
  ∃k k'. ∀ffi.
    evaluate (p,ext s k ffi) = (res,ext t k' ffi) ∧
    res ≠ SOME TimeOut ∧ (∀fe. res ≠ SOME (FinalFFI fe)) ∧ k' ≤ k
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[]>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If,mrec_ExtCall]
  >~[‘ExtCall’]>-
   (simp[Once evaluate_def]>>
    pop_assum mp_tac>>
    rpt (PURE_CASE_TAC>>fs[])>>rw[]>>
    gvs[ext_def,call_FFI_def,explode_eq_implode,implode_def])
  >~[‘While’]>-
   (simp[Once evaluate_def]>>
    pop_assum mp_tac>>
    rpt (CASE_TAC>>fs[])>>gvs[ext_def])>>
  simp[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]>>
  pop_assum mp_tac>>
  fs[ext_def,empty_locals_defs,dec_clock_def,kvar_defs2]>>
  rpt (CASE_TAC>>fs[])>>rw[]>>gvs[]>>
  qexistsl [‘2’,‘1’]>>fs[dec_clock_def]
QED

(* move to HOL - llistTheory *)
Theorem LFINITE_LAPPEND_EQ_NIL:
  LFINITE ll ⇒ (LAPPEND ll l1 = ll ⇔ l1 = [||])
Proof
  rw[EQ_IMP_THM] >- metis_tac[LFINITE_LAPPEND_IMP_NIL]>>
  simp[LAPPEND_NIL_2ND]
QED

Theorem mrec_FUNPOW_Ret_evaluate:
  mrec h_prog (h_prog (p,s)) = FUNPOW Tau n (Ret (INR (res,t))):'a ptree ⇒
  ∃k k'. (∀ffi. evaluate (p,ext s k ffi) = (res, ext t k' ffi)) ∧ k' ≤ k ∧
             res ≠ SOME TimeOut ∧ (∀fe. res ≠ SOME (FinalFFI fe))
Proof
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>strip_tac>>
  Cases_on ‘n’>>fs[FUNPOW]
  >- (imp_res_tac mrec_Ret_evaluate>>gvs[]>>metis_tac[])>>
  rename1 ‘SUC n’>>
  fs[GSYM FUNPOW,FUNPOW_SUC]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘res’,‘t’,‘s’,‘p’]>>
  Induct>>rw[]>>
  pop_assum mp_tac>>
  once_rewrite_tac[evaluate_def]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  fs[mrec_prog_simps,mrec_If,empty_locals_defs,mrec_ExtCall,
     panPropsTheory.eval_upd_clock_eq,call_FFI_def,kvar_defs2,
     iterateTheory.LAMBDA_PAIR,mrec_ShMemLoad,mrec_ShMemStore,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       rpt (pairarg_tac>>fs[])>>rw[]>>
       fs[FUNPOW_SUC]>>gvs[]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>
       simp[ext_def]>>NO_TAC)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>rw[]>>
      simp[FUNPOW_SUC]>>gvs[]>>
      imp_res_tac bind_FUNPOW_Ret>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>gvs[]>>
      fs[FUNPOW_Tau_bind]>>
      rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
      first_x_assum $ qspec_then ‘n’ mp_tac>>simp[]>>
      disch_then $ drule>>rw[]>>gvs[]>>
      qexistsl [‘k’,‘k'’]>>strip_tac>>
      first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[])
  >~ [‘Seq’] >-
   (fs[mrec_Seq]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    fs[FUNPOW_Tau_bind]>>
    rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]
    >- (Cases_on ‘m’>>fs[FUNPOW_SUC]>>
        imp_res_tac bind_FUNPOW_Ret>>
        imp_res_tac mrec_FUNPOW_Ret_INR>>gvs[]>>
        rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
        fs[FUNPOW_Tau_bind]>>gvs[]>>
        first_assum $ qspec_then ‘n’ mp_tac>>
        first_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
        disch_then drule>>strip_tac>>
        disch_then drule>>strip_tac>>gvs[]>>
        (Cases_on ‘k' ≤ k''’
         >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
             qexistsl [‘k+p''’,‘k'''’]>>simp[]>>
             strip_tac>>fs[]>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘p''’ assume_tac>>gvs[]))>>
        fs[NOT_LESS_EQUAL]>>
        drule LESS_ADD>>
        disch_then $ assume_tac o GSYM>>fs[]>>
        qexistsl [‘k’,‘k''' + p''’]>>simp[]>>
        strip_tac>>fs[]>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
        rev_drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘p''’ assume_tac>>fs[])>>
    ‘n' < SUC n'’ by simp[]>>
    res_tac>>
    qexistsl [‘k’,‘k'’]>>fs[]>>gvs[])
   (* If *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
      imp_res_tac bind_FUNPOW_Ret>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
      fs[FUNPOW_Tau_bind])
  >~ [‘Call’] >-
   (simp[mrec_Call,empty_locals_defs]>>
    ntac 4 (TOP_CASE_TAC>>fs[])>>
    TRY (TOP_CASE_TAC>>fs[])>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>
    fs[FUNPOW_Ret_simp]>>
    fs[mrec_h_handle_call_ret_lemma,empty_locals_defs,
       kvar_defs2]>>
    gvs[AllCaseEqs()]>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         ‘n < SUC n’ by simp[]>>
         res_tac>>gvs[]>>
         qexistsl [‘SUC k’,‘k'’]>>simp[]>>
         rpt (PURE_CASE_TAC>>fs[])>>NO_TAC)
    >- (rename [‘_ = FUNPOW Tau n _’]>>
        ‘n < SUC n’ by simp[]>>
        last_x_assum drule>>
        disch_then drule>>simp[]>>rw[]>>
        qexistsl [‘SUC k’,‘k'’]>>simp[]>>
        simp[ext_def])>>
    rename [‘Tau _ = FUNPOW Tau n _’]>>
    Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>gvs[]>>
    FULL_CASE_TAC>>gvs[]>>
    rename1 ‘_ = FUNPOW Tau n (Ret (INR (q'',r'')))’>>
    rename1 ‘_ = FUNPOW Tau n' (Ret (INR (SOME (Exception _ _),_)))’>>
    last_assum $ qspec_then ‘n’ mp_tac>>
    last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
    disch_then drule>>strip_tac>>
    disch_then drule>>strip_tac>>gvs[]>>
    (Cases_on ‘k' ≤ k''’
     >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
         rename1 ‘k'' = k' + pp’>>
         qexistsl [‘SUC (k+pp)’,‘k'''’]>>simp[]>>
         strip_tac>>fs[]>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>
         first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
         drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘pp’ assume_tac>>gvs[]))>>
    fs[NOT_LESS_EQUAL]>>
    drule LESS_ADD>>
    disch_then $ assume_tac o GSYM>>fs[]>>
    rename1 ‘k' = k'' + pp’>>
    qexistsl [‘SUC k’,‘k''' + pp’]>>simp[]>>
    strip_tac>>fs[]>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>
    first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
    rev_drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘pp’ assume_tac>>fs[])
  >~ [‘DecCall’] >-
   (simp[mrec_DecCall,empty_locals_defs]>>
    ntac 3 (TOP_CASE_TAC>>fs[])>>rw[]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>
    fs[FUNPOW_Ret_simp]>>
    fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,
       kvar_defs2]>>
    gvs[AllCaseEqs()]>>
    TRY (rename [‘_ = FUNPOW Tau n _’]>>
         ‘n < SUC n’ by simp[]>>
         res_tac>>TRY (gvs[]>>NO_TAC)>>
         qexistsl [‘SUC k’,‘k'’]>>simp[]>>gvs[]>>
         rpt (FULL_CASE_TAC>>fs[])>>NO_TAC)>>
    rename [‘Tau _ = FUNPOW Tau n _’]>>
    Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Ret>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>
    rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
    fs[FUNPOW_Tau_bind]>>gvs[]>>
    rename1 ‘_ = FUNPOW Tau n (Ret (INR (q',_)))’>>
    rename1 ‘_ = FUNPOW Tau n' (Ret (INR (SOME (Return _),_)))’>>
    last_assum $ qspec_then ‘n’ mp_tac>>
    last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
    disch_then drule>>strip_tac>>
    disch_then drule>>strip_tac>>gvs[]>>
        (Cases_on ‘k' ≤ k''’
         >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
             rename1 ‘k'' = k' + pp’>>
             qexistsl [‘SUC (k+pp)’,‘k'''’]>>simp[]>>
             strip_tac>>fs[]>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>
             first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘pp’ assume_tac>>gvs[]))>>
        fs[NOT_LESS_EQUAL]>>
        drule LESS_ADD>>
        disch_then $ assume_tac o GSYM>>fs[]>>
        qexistsl [‘SUC k’,‘k''' + p'’]>>simp[]>>
        strip_tac>>fs[]>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>
        first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
        rev_drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘p'’ assume_tac>>fs[])>>
  (* While *)
  simp[Once mrec_While]>>
  rpt (TOP_CASE_TAC>>fs[])>>simp[FUNPOW_SUC]>>gvs[]>>rw[]>>
  imp_res_tac bind_FUNPOW_Ret>>
  imp_res_tac mrec_FUNPOW_Ret_INR>>
  fs[FUNPOW_Tau_bind]>>
  fs[FUNPOW_Ret_simp]>>
  rename1 ‘Ret (INR y)’>>Cases_on ‘y’>>gvs[]>>
  rpt (FULL_CASE_TAC>>fs[])>>
  TRY (rename [‘mrec _ _ = FUNPOW Tau n (Ret _)’]>>
       ‘n < SUC n’ by simp[]>>
       res_tac>>gvs[]>>
       qexistsl [‘SUC k’,‘k'’]>>simp[]>>gvs[]>>NO_TAC)>>
  rename [‘Tau _ = FUNPOW Tau n _’]>>
  Cases_on ‘n’>>gvs[FUNPOW_SUC]>>
  rename1 ‘mrec _ (_ (While _ _,_)) = FUNPOW Tau n _’>>
  rename1 ‘mrec _ (_ (p,_)) = FUNPOW Tau n' _’>>
  first_assum $ qspec_then ‘n’ mp_tac>>
  first_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
  disch_then drule>>strip_tac>>
  disch_then drule>>strip_tac>>gvs[]>>
  (Cases_on ‘k' ≤ k''’
   >- (drule LESS_EQUAL_ADD>>strip_tac>>fs[]>>
       qexistsl [‘SUC (k+p')’,‘k'''’]>>simp[]>>
       strip_tac>>fs[]>>
       first_x_assum $ qspec_then ‘ffi’ assume_tac>>
       first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
       drule panPropsTheory.evaluate_add_clock_eq>>
       disch_then $ qspec_then ‘p'’ assume_tac>>gvs[]))>>
  fs[NOT_LESS_EQUAL]>>
  drule LESS_ADD>>
  disch_then $ assume_tac o GSYM>>fs[]>>
  qexistsl [‘SUC k’,‘k''' + p'’]>>simp[]>>
  strip_tac>>fs[]>>
  first_x_assum $ qspec_then ‘ffi’ assume_tac>>
  first_x_assum $ qspec_then ‘ffi’ assume_tac>>fs[]>>
  rev_drule panPropsTheory.evaluate_add_clock_eq>>
  disch_then $ qspec_then ‘p'’ assume_tac>>fs[]
QED

(********)

Theorem mrec_Vis_no_trace_lemma:
  mrec h_prog (h_prog (p, bst s)) = FUNPOW Tau n (Vis a g:'a ptree) ∧
  (∀k. s.ffi.io_events =
       (SND (evaluate(p,s with clock := k + s.clock))).ffi.io_events) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ∧ s.clock = 0 ∧
  (FST fs) (FST a) (SND fs) (FST (SND a)) (SND (SND a)) = X ⇒
  (∃f l. X = Oracle_return f l ∧ LENGTH (SND (SND a)) ≠ LENGTH l) ∨
  (∃f. X = Oracle_final f)
Proof
  simp[]>>rw[]>>
  ‘∀k. s.ffi = (SND (evaluate (p, s with clock := k + s.clock))).ffi’
    by (strip_tac>>
        Cases_on ‘evaluate (p, s with clock := k + s.clock)’>>fs[]>>
        drule io_events_eq_imp_ffi_eq>>
        first_assum $ qspec_then ‘k’ assume_tac>>simp[]>>gvs[])>>
  qpat_x_assum ‘∀x. s.ffi.io_events = _’ kall_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rw[]>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’]>>
  Induct>>rw[]>>
  ntac 5 (pop_assum mp_tac)>>
  simp[Once evaluate_def]>>
  simp[mrec_prog_simps,mrec_If,mrec_Dec,
       mrec_ShMemLoad,mrec_ShMemStore]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  fs[panPropsTheory.eval_upd_clock_eq,call_FFI_def,
     iterateTheory.LAMBDA_PAIR,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       simp[FUNPOW_Ret_simp]>>NO_TAC)>>
  TRY (simp[mrec_ExtCall]>>
       rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
       gvs[empty_locals_defs,set_var_defs]>>
       gvs[AllCaseEqs()]>>
       gvs[ffi_state_component_equality]>>
       Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[]>>NO_TAC)
  >- (CASE_TAC>>fs[]>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then drule>>simp[])
  >- (simp[mrec_Seq]>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
      >- (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
          disch_then drule>>simp[]>>
          disch_then drule>>simp[]>>
          impl_tac >-
           (strip_tac>>
            first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>
            qmatch_goalsub_abbrev_tac ‘FST X’>>
            Cases_on ‘X’>>gvs[]>>
            FULL_CASE_TAC>>gvs[]>>
            qmatch_goalsub_abbrev_tac ‘SND X’>>
            Cases_on ‘X’>>gvs[]>>
            imp_res_tac panPropsTheory.evaluate_io_events_mono>>
            fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
            drule_all io_events_eq_imp_ffi_eq>>rw[])>>rw[])>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      Cases_on ‘q’>>fs[]>>
      Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
      ‘s with <|clock := k; ffi := s.ffi|> = s with clock := k’
        by simp[state_component_equality]>>fs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      ‘n < SUC n'’ by simp[]>>
      first_x_assum drule>>
      disch_then $ qspecl_then [‘p'’,‘ext r 0 s.ffi’,‘g'’,‘a’,‘fs’] mp_tac>>
      simp[]>>
      impl_tac>-
       (strip_tac>>
        first_x_assum $ qspec_then ‘k''+k'''’ mp_tac>>simp[]>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘k'''’ assume_tac>>fs[]>>
        qmatch_goalsub_abbrev_tac ‘SND X’>>
        Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[])
  (* If *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then drule>>simp[])
  >~ [‘While’]>-
   (simp[Once mrec_While]>>
    rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
    Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    (imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
     >- (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
         disch_then drule>>simp[]>>
         disch_then drule>>simp[]>>
         (impl_tac >-
           (strip_tac>>
            first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[]>>
            qmatch_goalsub_abbrev_tac ‘FST X’>>
            Cases_on ‘X’>>gvs[empty_locals_defs,dec_clock_def]>>
            rpt (FULL_CASE_TAC>>gvs[])>>
            qmatch_goalsub_abbrev_tac ‘SND X’>>
            Cases_on ‘X’>>gvs[]>>
            imp_res_tac panPropsTheory.evaluate_io_events_mono>>
            fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
            drule_all io_events_eq_imp_ffi_eq>>rw[])>>rw[])))>>
    imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
    rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
    Cases_on ‘q’>>fs[]>>
    TRY (rename [‘INR (SOME xx,_)’]>>Cases_on ‘xx’>>fs[])>>
    Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
    imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
    first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
    ‘s with <|clock := k; ffi := s.ffi|> = s with clock := k’
      by simp[state_component_equality]>>fs[]>>
    dxrule evaluate_min_clock>>rw[]>>
    ‘n < SUC n'’ by simp[]>>
    first_x_assum drule>>
    disch_then $ qspecl_then [‘While e p’,‘ext r 0 s.ffi’,‘g’,‘a’,‘fs’] mp_tac>>
    simp[]>>
    (impl_tac>-
      (strip_tac>>
       first_x_assum $ qspec_then ‘SUC (k''+k''')’ mp_tac>>simp[]>>
       drule panPropsTheory.evaluate_add_clock_eq>>
       disch_then $ qspec_then ‘k'''’ assume_tac>>fs[dec_clock_def]>>
       qmatch_goalsub_abbrev_tac ‘SND X’>>
       Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[]))
  >~ [‘Call’] >-
   (simp[mrec_Call,empty_locals_defs,kvar_defs]>>
    rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
    Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
    TRY (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
         disch_then drule>>simp[]>>
         disch_then drule>>simp[]>>
         (impl_tac >-
           (strip_tac>>
            first_x_assum $ qspec_then ‘SUC k’ mp_tac>>fs[dec_clock_def]>>
            rpt (CASE_TAC>>gvs[])>>rw[]>>
            qmatch_goalsub_abbrev_tac ‘SND X’>>
            Cases_on ‘X’>>gvs[]>>
            imp_res_tac panPropsTheory.evaluate_io_events_mono>>
            fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
            drule io_events_eq_imp_ffi_eq>>rw[])>>rw[]))>>
    TRY (imp_res_tac mrec_FUNPOW_Ret_INR>>
         rename1 ‘_ = INR y’>>Cases_on ‘y’>>gvs[]>>
         fs[mrec_h_handle_call_ret_lemma,empty_locals_defs,
            kvar_defs2]>>
         gvs[AllCaseEqs()])>>
    Cases_on ‘n' - m'’>>fs[FUNPOW_SUC]>>
    imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
    imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
    first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>
    ‘s with <|locals:=r;clock := k; ffi := s.ffi|> =
     s with <|locals:=r;clock := k|>’
      by simp[state_component_equality]>>fs[]>>
    dxrule evaluate_min_clock>>rw[]>>
    ‘n < SUC n'’ by simp[]>>
    first_x_assum drule>>
    qmatch_asmsub_abbrev_tac ‘mrec _ (_ (pp,ss)) = FUNPOW _ _ (Vis a g')’>>
    disch_then $ qspecl_then [‘pp’,‘ext ss 0 s.ffi’,‘g'’,‘a’,‘fs’] mp_tac>>
    simp[Abbr‘ss’,Abbr‘pp’]>>
    (impl_tac>-
      (strip_tac>>
       first_x_assum $ qspec_then ‘SUC (k''+k''')’ mp_tac>>simp[]>>
       drule panPropsTheory.evaluate_add_clock_eq>>
       disch_then $ qspec_then ‘k'''’ assume_tac>>fs[dec_clock_def]>>
       qmatch_goalsub_abbrev_tac ‘SND X’>>
       Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[]))>>
  (* DecCall *)
  simp[mrec_DecCall,empty_locals_defs,set_var_defs]>>
  rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>
  imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
  >- (last_x_assum $ qspec_then ‘n'’ mp_tac>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then drule>>simp[]>>
      (impl_tac >-
        (strip_tac>>
         first_x_assum $ qspec_then ‘SUC k’ mp_tac>>fs[dec_clock_def]>>
         rpt (CASE_TAC>>gvs[])>>rw[]>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>
         Cases_on ‘X’>>gvs[]>>
         imp_res_tac panPropsTheory.evaluate_io_events_mono>>
         fs[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
         drule io_events_eq_imp_ffi_eq>>rw[])>>rw[]))>>
  imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
  rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
  fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,
     kvar_defs2]>>
  gvs[AllCaseEqs()]>>
  Cases_on ‘n' - m'’>>fs[FUNPOW_SUC]>>
  imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
  imp_res_tac mrec_FUNPOW_Ret_evaluate>>fs[]>>
  first_x_assum $ qspec_then ‘s'.ffi’ assume_tac>>
  ‘s' with <|locals:=r;clock := k; ffi := s'.ffi|> =
   s' with <|locals:=r;clock := k|>’
    by simp[state_component_equality]>>fs[]>>
  dxrule evaluate_min_clock>>rw[]>>
  ‘n < SUC n'’ by simp[]>>
  first_x_assum drule>>
  qmatch_asmsub_abbrev_tac ‘mrec _ (_ (pp,ss)) = FUNPOW _ _ (Vis a g')’>>
  disch_then $ qspecl_then [‘pp’,‘ext ss 0 s'.ffi’,‘g'’,‘a’,‘fs’] mp_tac>>
  simp[Abbr‘ss’,Abbr‘pp’]>>
  (impl_tac>-
    (strip_tac>>
     first_x_assum $ qspec_then ‘SUC (k''+k''')’ mp_tac>>simp[]>>
     drule panPropsTheory.evaluate_add_clock_eq>>
     disch_then $ qspec_then ‘k'''’ assume_tac>>fs[dec_clock_def]>>
     qmatch_goalsub_abbrev_tac ‘SND X’>>
     Cases_on ‘X’>>gvs[]>>rw[]>>gvs[])>>rw[])
QED

(*** evaluate -> itree (no ffi update) ***)

Theorem evaluate_mrec_FUNPOW_Ret_io_events:
  evaluate (p, s0) = (res,t) ∧ s0 = ext s k ffi ∧ t.ffi.io_events = ffi.io_events ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. mrec h_prog (h_prog (p, s)) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  map_every qid_spec_tac [‘k’,‘ffi’, ‘res’,‘t’,‘s’,‘s0’, ‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac >> simp[]>>
  fs[Once evaluate_def,sh_mem_load_def,sh_mem_store_def]
  >~[‘ShMemLoad’]>-
   (simp[mrec_ShMemLoad]>>fs[call_FFI_def,kvar_defs2]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘ShMemStore’]>-
   (simp[mrec_ShMemStore]>>fs[call_FFI_def,set_var_defs]>>
    rpt (CASE_TAC>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘ExtCall’]>-
   (simp[mrec_ExtCall]>>
    rpt (PURE_CASE_TAC>>fs[])>>
    fs[call_FFI_def,set_var_defs]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]
    >>~- ([‘Error’],metis_tac[FUNPOW])>>
    qexists ‘0’>>simp[FUNPOW]>>
    simp[bst_def,ext_def,bstate_component_equality])
  >~[‘Dec’]>-
   (fs[mrec_Dec]>>
    rpt (CASE_TAC>>fs[])
    >- (gvs[]>>metis_tac[FUNPOW])>>
    pairarg_tac>>fs[]>>
    simp[Once itree_unfold]>>rw[]>>
    qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
    qpat_abbrev_tac ‘X = s' with locals := _’>>
    first_x_assum $ qspecl_then [‘X’,‘ffi’,‘k’] assume_tac>>
    rfs[]>>fs[FUNPOW_Tau_bind])
  >~[‘If’]>-
   (fs[mrec_If]>>rw[]>>
    rpt (CASE_TAC>>fs[])>>
    TRY (qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
         res_tac>>
         pop_assum kall_tac>>
         first_x_assum $ qspecl_then [‘s'’,‘k’,‘ffi’] assume_tac>>
         rfs[]>>fs[FUNPOW_Tau_bind]>>NO_TAC)>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘While’]>-
   (simp[Once mrec_While]>>
    rpt (CASE_TAC>>fs[])>>gvs[]>>
    pairarg_tac>>fs[]>>
    Cases_on ‘k=0’>>fs[]
    >- (qpat_x_assum ‘_ = (NONE,t)’ mp_tac>>
        rpt (CASE_TAC>>fs[])>>
        first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k-1’] assume_tac>>
        rw[]>>imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        gvs[IS_PREFIX_ANTISYM]>>simp[FUNPOW_Tau_bind]
        >~ [‘Break’]>- (gvs[]>>metis_tac[GSYM FUNPOW_SUC])>>
        qpat_x_assum ‘evaluate (While _ _,_)=_’ mp_tac>>
        simp[Once evaluate_def]>>
        rpt (CASE_TAC>>fs[])>>rw[]>>
        TRY (pairarg_tac>>fs[])>>
        rpt (FULL_CASE_TAC>>fs[])>>
        first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
        rfs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW_SUC,GSYM FUNPOW]>>
        metis_tac[GSYM FUNPOW_ADD])>>
    qpat_x_assum ‘_ = (SOME _,t)’ mp_tac>>
    rpt (CASE_TAC>>fs[])>>
    first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k-1’] assume_tac>>
    rw[]>>imp_res_tac panPropsTheory.evaluate_io_events_mono>>
    gvs[IS_PREFIX_ANTISYM]>>simp[FUNPOW_Tau_bind]>>
    TRY (qpat_x_assum ‘evaluate (While _ _,_)=_’ mp_tac>>
         simp[Once evaluate_def]>>
         rpt (CASE_TAC>>fs[])>>rw[]>>
         TRY (pairarg_tac>>fs[])>>
         rpt (FULL_CASE_TAC>>fs[])>>
         first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
         rfs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind]>>
         simp[GSYM FUNPOW_SUC,GSYM FUNPOW]>>
         metis_tac[GSYM FUNPOW_ADD])>>
    rw[]>>gvs[]>>metis_tac[GSYM FUNPOW_SUC])
  >~[‘Seq’]>-
   (fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[]>>
    rpt (CASE_TAC>>fs[])>>
    TRY (pairarg_tac>>fs[])>>
    rpt (FULL_CASE_TAC>>fs[])>>
    simp[Once itree_unfold,call_FFI_def]>>rw[]
    >- (qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
        first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k’] assume_tac>>
        imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        rfs[]>>fs[IS_PREFIX_ANTISYM,FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW]>>
        first_x_assum $ qspecl_then [‘bst s1’,‘s1.ffi’,‘s1.clock’] assume_tac>>
        gvs[IS_PREFIX_ANTISYM]>>fs[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
        qexists ‘n' + SUC n’>>fs[GSYM FUNPOW_ADD])>>
    qrefine ‘SUC n’>>simp[FUNPOW_SUC]>>fs[]>>
    first_x_assum $ qspecl_then [‘s'’,‘ffi’,‘k’] assume_tac>>
    fs[FUNPOW_Tau_bind]>>
    rpt (CASE_TAC>>fs[]))
  >~[‘Call’]>-
   (simp[mrec_Call]>>
    rpt (CASE_TAC>>fs[])
    >~[‘TimeOut’]>-
     (Cases_on ‘k=0’>>fs[]>>rw[]>>
      FULL_CASE_TAC>>fs[]
      >- (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
          first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
          gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
          simp[h_handle_call_ret_def]>>
          gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[kvar_defs2]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      gvs[empty_locals_defs]>>fs[FUNPOW_Tau_bind]>>
      rpt (CASE_TAC>>fs[])>>
      simp[h_handle_call_ret_def,mrec_bind,kvar_defs2]>>
      rpt (FULL_CASE_TAC>>fs[])>>simp[empty_locals_defs]>>
      TRY (irule_at Any (GSYM FUNPOW_SUC))>>
      TRY (simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
           simp[h_handle_call_ret_def,mrec_bind,kvar_defs2])>>

      imp_res_tac panPropsTheory.evaluate_io_events_mono>>gvs[]>>
      drule_all IS_PREFIX_ANTISYM>>rw[]>>fs[]>>
      simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
      simp[h_handle_call_ret_def,mrec_bind,kvar_defs2]>>

      qmatch_goalsub_abbrev_tac ‘h_prog (_,ss)’>>
      first_x_assum $ qspecl_then [‘ss’,‘r'.ffi’,‘r'.clock’] mp_tac>>
      (impl_tac >- fs[Abbr‘ss’,state_component_equality])>>rw[]>>
      simp[FUNPOW_Tau_bind,GSYM FUNPOW_SUC]>>
      simp[GSYM FUNPOW_ADD])>>
    gvs[]>>metis_tac[FUNPOW])
  >~[‘DecCall’]>-
   (simp[mrec_DecCall]>>
    rpt (CASE_TAC>>fs[])
    >~[‘TimeOut’]>-
     (Cases_on ‘k=0’>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[empty_locals_defs]>>
      first_x_assum $ qspecl_then [‘s' with locals := r’,‘ffi’,‘k-1’] assume_tac>>
      fs[FUNPOW_Tau_bind]>>gvs[]>>
      fs[h_handle_deccall_ret_def,mrec_bind,set_var_defs,res_var_def]
      >~ [‘TimeOut’]>-
       (pairarg_tac>>fs[]>>
        first_x_assum $ qspecl_then [‘bst r' with locals := s'.locals |+ (rt,v)’,‘r'.ffi’,‘r'.clock’] assume_tac>>
        imp_res_tac panPropsTheory.evaluate_io_events_mono>>
        gvs[IS_PREFIX_ANTISYM]>>rw[]>>fs[FUNPOW_Tau_bind]>>
        simp[h_handle_deccall_ret_def,mrec_bind,set_var_defs]>>
        fs[FUNPOW_Tau_bind]>>
        simp[GSYM FUNPOW_SUC]>>simp[GSYM FUNPOW_ADD])>>
      gvs[empty_locals_defs]>>metis_tac[GSYM FUNPOW_SUC])>>
    gvs[]>>metis_tac[FUNPOW])>>
  fs[Once mrec_While,mrec_prog_nonrec,mrec_If]>>gvs[kvar_defs2]>>
  rpt (CASE_TAC>>fs[])>>
  TRY (pairarg_tac>>fs[])>>
  rpt (FULL_CASE_TAC>>fs[])>>
  simp[Once itree_unfold,call_FFI_def]>>rw[]>>
  TRY (metis_tac[FUNPOW])
QED

Theorem evaluate_mrec_FUNPOW_Ret:
  evaluate (p, s) = (res,t) ∧ t.ffi = s.ffi ∧
  (∀fe. res ≠ SOME (FinalFFI fe)) ∧ res ≠ SOME TimeOut ⇒
  ∃n. mrec h_prog (h_prog (p, bst s)) = FUNPOW Tau n (Ret (INR (res,bst t))):'a ptree
Proof
  rw[]>>irule evaluate_mrec_FUNPOW_Ret_io_events>>rw[]>>
  irule_at Any EQ_REFL>>
  qexists ‘s.clock’>>
  qmatch_goalsub_abbrev_tac ‘evaluate (_, ss) = _’>>
  ‘ss = s’ by simp[Abbr‘ss’,state_component_equality]>>simp[]
QED

(*****)

(* could do with some speedup *)
Theorem mrec_Vis_nondiv_lemma:
  mrec h_prog (h_prog (p,bst s)) = FUNPOW Tau n (Vis a g) :'a ptree ∧
  (∀k. s.ffi.io_events =
       (SND (evaluate (p,s with clock := k + s.clock))).ffi.io_events) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ∧ s.clock = 0 ⇒
  ¬ div fs (mrec h_prog (h_prog (p,bst s)))
Proof
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>rpt gen_tac>>
  disch_then assume_tac>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘fs’,‘a’,‘g’,‘s’,‘p’]>>
  Induct>>rw[]>>
  ntac 5 (pop_assum mp_tac)>>
  simp[Once evaluate_def]>>
  simp[mrec_prog_simps,mrec_If,mrec_Dec,
       mrec_ShMemLoad,mrec_ShMemStore]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  fs[panPropsTheory.eval_upd_clock_eq,call_FFI_def,
     iterateTheory.LAMBDA_PAIR,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1]>>
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       simp[FUNPOW_Ret_simp]>>NO_TAC)
  >- ((* Dec *)
  CASE_TAC>>fs[]>>rw[]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>
  imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
  ‘n' < SUC n'’ by simp[]>>
  first_assum drule>>
  disch_then drule>>
  disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>strip_tac>>
  fs[FUNPOW_Ret_simp]>>
  drule mrec_Vis_no_trace_lemma>>simp[]>>
  disch_then drule>>simp[]>>rw[]>>
  PairCases_on ‘a’>>gvs[]>>
  Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
  simp[FUNPOW_Tau_bind]>>
  simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD])
  >~ [‘Seq’]
  >- (simp[mrec_Seq]>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
      >- (‘n' < SUC n'’ by simp[]>>
          first_assum drule>>
          disch_then drule>>simp[]>>
          disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>
          ‘∀k. s.ffi.io_events =
               (SND (evaluate (p,s with clock := k))).ffi.io_events’ by
            (strip_tac>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>
             CASE_TAC>>fs[]>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             imp_res_tac panPropsTheory.evaluate_io_events_mono>>
             fs[IS_PREFIX_APPEND])>>rw[]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          ‘ltree fs (mrec h_prog (h_prog (p,bst s))) =
           FUNPOW Tau n'' (Ret r):'a ptree’
            by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
          imp_res_tac nondiv_INR>>
          rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
          drule nondiv_evaluate'>>
          drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
          disch_then drule>>simp[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          drule mrec_Vis_no_trace_lemma>>
          disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
          PairCases_on ‘a’>>gvs[]>>
          Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          Cases_on ‘fs’>>fs[]>>
          (rpt (CASE_TAC>>fs[])
           >- (drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
               ‘s.ffi = t'.ffi’ by
                 (first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>
                  drule io_events_eq_imp_ffi_eq>>rw[])>>rw[])>>
           irule_at Any LESS_EQ_REFL>>simp[FUNPOW]))>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      (* write a lemma on ext (bst s) k s.ffi = s with clock := k *)
(*      ‘∀k. ext (bst s) k s.ffi = s with clock := k’
        by simp[state_component_equality]>>fs[]>>*)
      rpt (FULL_CASE_TAC>>fs[])>>
      Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_x_assum drule>>
      ‘(ext r 0 s.ffi).clock = 0’ by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>simp[]>>
      ‘∀k. s.ffi.io_events =
           (SND (evaluate (p',ext r k s.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
         first_assum $ qspec_then ‘k''’ assume_tac>>
         first_x_assum $ qspec_then ‘k'' + k'''’ assume_tac>>gs[]>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[]>>gvs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      ‘ltree fs (mrec h_prog (h_prog (p',bst (ext r 0 s.ffi)))) =
       FUNPOW Tau n'' (Ret r'):'a ptree’
        by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
      imp_res_tac nondiv_INR>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[Excl"bst_ext_id"]>>
      drule nondiv_evaluate'>>
      drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
      disch_then drule>>simp[]>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      ‘(ext r 0 s.ffi).clock = 0’ by simp[]>>
      drule_at Any mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n’>>fs[FUNPOW_SUC]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      Cases_on ‘fs’>>fs[]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])
  (* If *)
  >- (rpt (CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n' < SUC n'’ by simp[]>>
      first_x_assum drule>>
      disch_then drule>>gs[]>>
      disch_then $ qspec_then ‘fs’ assume_tac>>gvs[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>simp[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
      simp[FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD])
  >~ [‘While’]
  >- (simp[Once mrec_While]>>
      rpt (CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]
      (* p: Vis *)
      >- (‘n' < SUC n'’ by simp[]>>
          first_assum drule>>
          disch_then drule>>simp[]>>
          disch_then $ qspec_then ‘fs’ mp_tac>>
          fs[dec_clock_def,empty_locals_defs]>>
          ‘∀k. s.ffi.io_events =
               (SND (evaluate (p,s with clock := k))).ffi.io_events’ by
            (strip_tac>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[]>>
             qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
             rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
             imp_res_tac panPropsTheory.evaluate_io_events_mono>>
             fs[IS_PREFIX_APPEND])>>rw[]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          ‘ltree fs (mrec h_prog (h_prog (p,bst s))) =
           FUNPOW Tau n'' (Ret r):'a ptree’
            by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
          imp_res_tac nondiv_INR>>
          rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
          drule nondiv_evaluate'>>
          drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
          disch_then drule>>simp[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          drule mrec_Vis_no_trace_lemma>>
          disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
          PairCases_on ‘a’>>gvs[]>>
          Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
          fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          rpt (CASE_TAC>>fs[])>>
          TRY (irule_at Any LESS_EQ_REFL>>simp[FUNPOW])>>
          drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
          first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>
          drule io_events_eq_imp_ffi_eq>>rw[])>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      Cases_on ‘n' - m’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_x_assum drule>>
      ‘(ext r 0 s.ffi).clock = 0’ by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>simp[]>>
      ‘∀k. s.ffi.io_events =
           (SND (evaluate (While e p,ext r k s.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[dec_clock_def]>>
         first_assum $ qspec_then ‘SUC k''’ assume_tac>>
         first_x_assum $ qspec_then ‘SUC (k'' + k''')’ assume_tac>>gs[]>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[]>>gvs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])
  >~ [‘Call’]
  >- (simp[mrec_Call,kvar_defs2]>>
      ntac 4 (TOP_CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      TRY (‘n' < SUC n'’ by simp[]>>
           first_assum drule>>
           disch_then drule>>simp[]>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[dec_clock_def,empty_locals_defs]>>
           ‘∀k. s.ffi.io_events =
                (SND (evaluate (q,s with <|locals:=r;clock := k|>))).ffi.io_events’ by
             (strip_tac>>
              first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[set_var_defs]>>
              rpt (CASE_TAC>>fs[])>>
              qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              fs[IS_PREFIX_APPEND]>>
              rw[]>>gvs[])>>rw[]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           ‘ltree fs (mrec h_prog (h_prog (q,bst (s with locals := r)))) =
            FUNPOW Tau n'' (Ret r'):'a ptree’
             by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
           imp_res_tac nondiv_INR>>
           rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
           drule nondiv_evaluate'>>
           drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
           disch_then drule>>simp[]>>
           disch_then $ assume_tac o GSYM>>fs[]>>
           drule mrec_Vis_no_trace_lemma>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
           PairCases_on ‘a’>>gvs[]>>
           Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
           Cases_on ‘fs’>>
           fs[mrec_h_handle_call_ret_lemma,empty_locals_defs,kvar_defs2]>>
           rpt (CASE_TAC>>fs[])>>
           irule_at Any LESS_EQ_REFL>>simp[FUNPOW] (* )*) >>
           drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
           first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[]>>rw[]>>
           qmatch_asmsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
           imp_res_tac panPropsTheory.evaluate_io_events_mono>>
           fs[IS_PREFIX_APPEND]>>gvs[]>>
           rev_drule io_events_eq_imp_ffi_eq>>rw[])>>
      TRY (first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>NO_TAC)>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      qpat_x_assum ‘mrec _ _ = FUNPOW _ _ (Vis _ _)’ mp_tac>>
      simp[mrec_h_handle_call_ret_lemma,empty_locals_defs,kvar_defs2]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rw[]>>
      Cases_on ‘n'-m'’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_assum drule>>
      ‘(ext (r' with locals := s.locals |+ (q''',v)) 0 s.ffi).clock = 0’
        by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then $ qspec_then ‘fs’ mp_tac>>
      fs[dec_clock_def,empty_locals_defs,set_var_defs]>>
      ‘s with <|locals := r; clock := k''; ffi := s.ffi|> =
       s with <|locals := r; clock := k''|>’
        by simp[state_component_equality]>>fs[]>>
      pop_assum kall_tac>>
      ‘∀k. s.ffi.io_events =
           (SND (evaluate (r''',ext (r' with locals:=s.locals |+ (q''',v)) k s.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[dec_clock_def]>>
         first_assum $ qspec_then ‘SUC k''’ mp_tac>>
         first_x_assum $ qspec_then ‘SUC (k'' + k''')’ mp_tac>>simp[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      ‘ltree fs (mrec h_prog (h_prog (r''',bst (ext (r' with locals:=s.locals|+(q''',v)) 0 s.ffi)))) =
       FUNPOW Tau n'' (Ret r''):'a ptree’
        by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
      imp_res_tac nondiv_INR>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[Excl"bst_ext_id"]>>
      drule nondiv_evaluate'>>
      drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
      disch_then drule>>simp[]>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      ‘(ext (r' with locals := s.locals |+ (q''',v)) 0 s.ffi).clock = 0’ by simp[]>>
      drule_at Any mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n’>>fs[FUNPOW_SUC]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      Cases_on ‘fs’>>fs[]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])
 >~ [‘DecCall’]
  >- (simp[mrec_DecCall]>>
      rpt (TOP_CASE_TAC>>fs[])>>rw[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      TRY (‘n' < SUC n'’ by simp[]>>
           first_assum drule>>
           disch_then drule>>simp[]>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[dec_clock_def,empty_locals_defs]>>
           ‘∀k. s'.ffi.io_events =
                (SND (evaluate (q,s' with <|locals:=r;clock := k|>))).ffi.io_events’ by
             (strip_tac>>
              first_x_assum $ qspec_then ‘SUC k’ mp_tac>>simp[set_var_defs]>>
              rpt (CASE_TAC>>fs[])>>
              qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              fs[IS_PREFIX_APPEND]>>
              rw[]>>gvs[])>>rw[]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           ‘ltree fs (mrec h_prog (h_prog (q,bst (s' with locals := r)))) =
            FUNPOW Tau n'' (Ret r'):'a ptree’
             by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
           imp_res_tac nondiv_INR>>
           rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
           drule nondiv_evaluate'>>
           drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
           disch_then drule>>simp[]>>
           disch_then $ assume_tac o GSYM>>fs[]>>
           drule mrec_Vis_no_trace_lemma>>
           disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
           PairCases_on ‘a’>>gvs[]>>
           Cases_on ‘n''-n'’>>fs[FUNPOW_SUC]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
           fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
           drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
           Cases_on ‘fs’>>
           fs[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,set_var_defs]>>
           rpt (CASE_TAC>>fs[])>>
           irule_at Any LESS_EQ_REFL>>simp[FUNPOW]>>
           drule evaluate_mrec_FUNPOW_Ret>>simp[]>>
           first_x_assum $ qspec_then ‘k’ mp_tac>>simp[]>>rw[]>>
           rev_drule io_events_eq_imp_ffi_eq>>rw[])>>
      imp_res_tac mrec_FUNPOW_Ret_INR>>
      rename [‘_ = INR y’]>>Cases_on ‘y’>>fs[]>>
      imp_res_tac mrec_FUNPOW_Ret_evaluate>>
      first_x_assum $ qspec_then ‘s'.ffi’ assume_tac>>simp[]>>
      dxrule evaluate_min_clock>>rw[]>>
      qpat_x_assum ‘mrec _ _ = FUNPOW _ _ (Vis _ _)’ mp_tac>>
      simp[mrec_h_handle_deccall_ret_lemma,empty_locals_defs,set_var_defs]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rw[]>>
      Cases_on ‘n'-m'’>>fs[FUNPOW_SUC]>>
      imp_res_tac bind_FUNPOW_Vis>>fs[FUNPOW_Tau_bind]>>
      ‘n < SUC n'’ by simp[]>>
      first_assum drule>>
      ‘(ext (r' with locals := s'.locals |+ (m0,v)) 0 s'.ffi).clock = 0’
        by simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      disch_then drule>>simp[]>>
      disch_then $ qspec_then ‘fs’ mp_tac>>
      fs[dec_clock_def,empty_locals_defs,set_var_defs]>>
      ‘s' with <|locals := r; clock := k''; ffi := s'.ffi|> =
       s' with <|locals := r; clock := k''|>’
        by simp[state_component_equality]>>fs[]>>
      pop_assum kall_tac>>
      ‘∀k. s'.ffi.io_events =
           (SND (evaluate (p,ext (r' with locals:=s'.locals |+ (m0,v)) k s'.ffi))).ffi.io_events’ by
        (strip_tac>>
         qmatch_goalsub_abbrev_tac ‘SND X’>>Cases_on ‘X’>>fs[dec_clock_def]>>
         first_assum $ qspec_then ‘SUC k''’ mp_tac>>
         first_x_assum $ qspec_then ‘SUC (k'' + k''')’ mp_tac>>simp[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k'''’ assume_tac>>fs[])>>rw[]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,FUNPOW_Ret_simp]>>
      ‘ltree fs (mrec h_prog (h_prog (p,bst (ext (r' with locals:=s'.locals|+(m0,v)) 0 s'.ffi)))) =
       FUNPOW Tau n'' (Ret r''):'a ptree’
        by gvs[GSYM FUNPOW,FUNPOW_Ret_simp]>>
      imp_res_tac nondiv_INR>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[Excl"bst_ext_id"]>>
      drule nondiv_evaluate'>>
      drule nondiv_imp_evaluate'>>fs[]>>strip_tac>>
      disch_then drule>>simp[]>>
      disch_then $ assume_tac o GSYM>>fs[]>>
      ‘(ext (r' with locals := s'.locals |+ (m0,v)) 0 s'.ffi).clock = 0’ by simp[]>>
      drule_at Any mrec_Vis_no_trace_lemma>>simp[]>>
      disch_then drule>>
      disch_then $ qspec_then ‘fs’ mp_tac>>fs[]>>rw[]>>
      PairCases_on ‘a’>>gvs[]>>
      Cases_on ‘n''-n’>>fs[FUNPOW_SUC]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      simp[GSYM FUNPOW_SUC,GSYM FUNPOW_ADD]>>
      fs[FUNPOW_Ret_simp,FUNPOW_Tau_bind]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      Cases_on ‘fs’>>fs[]>>
      irule_at Any (GSYM ADD_SUB)>>simp[])>>
  simp[mrec_ExtCall]>>
  rw[]>>gvs[AllCaseEqs()]>>
  Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[empty_locals_defs]>>
  rpt (CASE_TAC>>fs[])>>qexists ‘SUC (SUC 0)’>>simp[FUNPOW]
QED

Theorem div_no_trace_LNIL:
  div fs (mrec h_prog (h_prog (p,bst s)):'a ptree) ∧
  (∀k. s.ffi.io_events =
       (SND (evaluate(p,s with clock := k + s.clock))).ffi.io_events) ∧
  FST fs = s.ffi.oracle ∧ SND fs = s.ffi.ffi_state ∧ s.clock = 0 ⇒
  trace_prefix fs (mrec h_prog (h_prog (p,bst s))) = [||]
Proof
  rw[]>>
  Cases_on ‘∃t. strip_tau (mrec h_prog (h_prog (p,bst s))) (t:'a ptree)’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>
      Cases_on ‘t’>>fs[]>>
      drule mrec_Vis_nondiv_lemma>>
      disch_then $ qspec_then ‘fs’ assume_tac>>
      gvs[div_def,FUNPOW_Ret_simp])>>
  imp_res_tac strip_tau_spin>>gvs[trace_prefix_spin]
QED

Theorem bounded_trace_eq:
  (∀k'. (SND(evaluate(p,s))).ffi.io_events
        = (SND(evaluate(p,s with clock:=k' + s.clock))).ffi.io_events) ∧
  div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s))) ⇒
  LAPPEND (fromList (s.ffi.io_events)) (trace_prefix (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (p,bst s)))) =
  fromList (SND (evaluate (p, s:('a,'b) state))).ffi.io_events
Proof
  map_every qid_spec_tac [‘s’,‘p’]>>
  recInduct evaluate_ind>>rw[]>>
  pop_assum mp_tac>>
  pop_assum mp_tac>>
  once_rewrite_tac[evaluate_def]>>
  simp[sh_mem_load_def,sh_mem_store_def]>>
  simp[mrec_prog_simps,mrec_Dec,mrec_If,mrec_ExtCall,
       mrec_ShMemLoad,mrec_ShMemStore]>>
  fs[panPropsTheory.eval_upd_clock_eq,call_FFI_def,kvar_defs2,
     panPropsTheory.opt_mmap_eval_upd_clock_eq1,explode_eq_implode,implode_def]>>
  (* TODO Remove TRY; it is easy for a subgoal to slide past this TRY silently,
     causing situations were ones tries to debug at the wrong place :( *)
  (* 10 subgoals *)
  TRY (rpt (TOP_CASE_TAC>>fs[])>>
       rpt (pairarg_tac>>fs[])>>
       rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
       imp_res_tac trace_prefix_bind_div>>
       fs[LFINITE_fromList,GSYM LAPPEND_fromList,
          LAPPEND_NIL_2ND,empty_locals_defs]>>NO_TAC)
  (* 6 subgoals *)
(* Dec *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
      (fs[div_bind_cases]
       >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
      imp_res_tac div_bind2>>fs[])
  (* Seq *)
  >~ [‘Seq’]
  >- (simp[mrec_Seq]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]
      >- (imp_res_tac evaluate_imp_nondiv>>gs[]>>
          fs[div_bind_cases]>- gvs[div_def]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          drule nondiv_evaluate'>>
          disch_then $ qspecl_then [‘s1’,‘NONE’,‘s.clock’] mp_tac>>gs[]>>
          ‘s with clock := s.clock = s’
            by simp[state_component_equality]>>gvs[]>>
          disch_then $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          imp_res_tac trace_prefix_bind_div>>fs[]>>
          first_assum irule>>
          rw[]>>
          imp_res_tac panPropsTheory.evaluate_add_clock_eq>>fs[]>>
          first_x_assum $ qspec_then ‘k' - s1.clock’ assume_tac>>
          first_x_assum $ qspec_then ‘k'- s1.clock + s.clock’ assume_tac>>
          gvs[])>>
      fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          first_x_assum irule>>rw[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>
          imp_res_tac div_imp_timeout>>fs[]>>
          first_x_assum $ qspec_then ‘k' + s.clock’ assume_tac>>
          gvs[])>>
      Cases_on ‘res ≠ SOME TimeOut’>>fs[]
      >- (imp_res_tac nondiv_INR>>gvs[]>>
          Cases_on ‘x’>>fs[]>>
          Cases_on ‘q’>>fs[]>>
          imp_res_tac nondiv_imp_evaluate>>fs[]>>
          Cases_on ‘s.clock < k’>>fs[NOT_LESS]
          >- (dxrule (GSYM LESS_ADD)>>strip_tac>>
              rev_drule panPropsTheory.evaluate_add_clock_eq>>simp[]>>
              disch_then $ qspec_then ‘p’ assume_tac>>fs[])>>
          dxrule LESS_EQUAL_ADD>>strip_tac>>
          drule panPropsTheory.evaluate_add_clock_eq>>simp[]>>
          disch_then $ qspec_then ‘p’ assume_tac>>
          ‘s with clock := s.clock = s’
            by simp[state_component_equality]>>gvs[])>>
      gvs[div_bind_cases]>>
      drule_then drule nondiv_timeout_add_clock>>rw[]>>fs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      Cases_on ‘q’>>fs[]>>
      gvs[div_bind_cases]>>
      Cases_on ‘evaluate (c2,t' with clock := 0)’>>fs[]>>
      drule evaluate_add_clock_or_timeout>>simp[]>>
      disch_then $ qspecl_then [‘s1’,‘SOME TimeOut’,‘s.clock’] mp_tac>>
      ‘s with clock := s.clock = s’ by simp[state_component_equality]>>
      fs[]>>rw[]>>
      ‘s1.ffi.io_events = r.ffi.io_events’ by
        (first_x_assum $ qspec_then ‘k' - s.clock’ mp_tac>>gvs[])>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      drule nondiv_evaluate'>>
      disch_then $ drule_at Any>>rw[]>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      fs[]>>
      drule trace_prefix_bind_div>>rw[]>>fs[]>>
      qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>fs[]>>
      ‘(t' with clock := 0).clock = 0’ by simp[]>>
      drule_at Any div_no_trace_LNIL>>simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      impl_tac >-
       (strip_tac>>
      first_x_assum $ qspec_then ‘k + k' - s.clock’ assume_tac>>fs[]>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘k’ assume_tac>>gvs[])>>rw[])
     (* If (the same as Dec) *)
  >- (rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
      (fs[div_bind_cases]
       >- (imp_res_tac trace_prefix_bind_div>>fs[]))>>
      imp_res_tac div_bind2>>fs[])
  >- (once_rewrite_tac[mrec_While]>>
      rpt (TOP_CASE_TAC>>fs[])>>
      rpt (pairarg_tac>>fs[])>>
      rw[]>>gvs[iterateTheory.LAMBDA_PAIR]>>
      fs[dec_clock_def,empty_locals_defs]>>
      fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_assum $ qspec_then ‘0’ assume_tac>>fs[]>>
          last_assum $ qspec_then ‘SUC 0’ mp_tac>>
          strip_tac>>gvs[]>>
          drule div_no_trace_LNIL>>fs[]>>
          impl_tac >-
           (strip_tac>>
            first_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
            last_assum $ qspec_then ‘SUC k’ mp_tac>>
            strip_tac>>fs[])>>
          strip_tac>>gvs[LAPPEND_NIL_2ND])
      >- (imp_res_tac nondiv_INR>>fs[]>>
          Cases_on ‘x’>>fs[]>>
          imp_res_tac nondiv_imp_evaluate>>gvs[]>>
          dxrule evaluate_min_clock>>rw[]>>
          Cases_on ‘q’>>fs[]>>
          TRY (rename [‘evaluate _ = (SOME x,_)’]>>Cases_on ‘x’)>>gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          simp[LAPPEND_ASSOC]>>
          last_assum $ qspec_then ‘SUC k'’ mp_tac>>
          strip_tac>>fs[]>>gvs[]>>
          drule nondiv_evaluate'>>fs[]>>
          disch_then $ drule_at Any>>
          simp[]>>strip_tac>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_assum $ qspec_then ‘0’ assume_tac>>fs[]>>
          drule_then mp_tac panPropsTheory.evaluate_io_events_mono>>
          simp[IS_PREFIX_APPEND]>>rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          ‘(t' with clock := 0).clock = 0’ by simp[]>>
          drule_at Any div_no_trace_LNIL>>simp[]>>
          disch_then $ drule_at Any>>simp[]>>
          (impl_tac >-
            (strip_tac>>
             last_x_assum $ qspec_then ‘SUC (k' + k)’ (mp_tac o GSYM)>>
             simp[]>>
             rev_drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘k’ assume_tac>>fs[]))>>rw[])
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_x_assum $ qspec_then ‘s.clock - 1’ assume_tac>>gvs[]>>
          last_assum $ irule>>
          strip_tac>>
          drule div_imp_timeout>>fs[]>>rw[]>>
          first_x_assum $ qspec_then ‘k' + s.clock - 1’ assume_tac>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[])>>
      imp_res_tac nondiv_INR>>fs[]>>
      Cases_on ‘x’>>fs[]>>
      imp_res_tac nondiv_imp_evaluate>>gvs[]>>
      Cases_on ‘q’>>fs[]>>
      TRY (rename [‘evaluate _ = (SOME x,_)’]>>Cases_on ‘x’)>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,s with clock := k) = (X,t')’>>
      (Cases_on ‘res ≠ SOME TimeOut’>>fs[]
      >- (‘res = X ∧ t' = s1 with clock := t'.clock’ by
            ((Cases_on ‘s.clock - 1 < k’
             >- (dxrule (GSYM LESS_ADD)>>strip_tac>>
                 rev_drule panPropsTheory.evaluate_add_clock_eq>>
                 disch_then $ qspec_then ‘p’ assume_tac>>fs[]>>
                 gvs[]))>>
             fs[NOT_LESS]>>dxrule LESS_EQUAL_ADD>>strip_tac>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘p’ assume_tac>>fs[]>>
             gvs[state_component_equality,Abbr‘X’])>>
          gvs[]>>
          ‘bst t' = bst s1’ by
            (pop_assum (fn h => rewrite_tac[Once h])>>simp[bst_def])>>
          fs[]>>
          qpat_x_assum ‘_ = (X,t')’ kall_tac>>
          qpat_x_assum ‘t' = _’ kall_tac>>
          pop_assum kall_tac>>fs[Abbr‘X’]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          drule nondiv_evaluate'>>
          disch_then $ drule_at Any>>rw[]>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          imp_res_tac div_imp_timeout>>gvs[]>>
          first_x_assum $ qspec_then ‘s1.clock’ assume_tac>>fs[]>>
          ‘s1 with clock := s1.clock = s1’
            by simp[state_component_equality]>>gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          last_x_assum irule>>
          strip_tac>>
          drule div_imp_timeout>>rw[]>>
          first_x_assum $ qspec_then ‘k' + s1.clock’ assume_tac>>fs[]>>
          last_x_assum $ qspec_then ‘k'’ mp_tac>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          strip_tac>>fs[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[]))>>
      gvs[]>>
      dxrule evaluate_min_clock>>
      ‘X ≠ SOME TimeOut’ by simp[Abbr‘X’]>>rw[]>>
      drule evaluate_add_clock_or_timeout>>
      disch_then $ qspecl_then [‘s1’,‘SOME TimeOut’,‘s.clock - 1’] mp_tac>>
      simp[]>>rw[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘X’]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      drule nondiv_evaluate'>>
      disch_then $ drule_at Any>>rw[]>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      gvs[]>>
      imp_res_tac div_imp_timeout>>fs[]>>
      first_x_assum $ qspec_then ‘0’ assume_tac>>fs[]>>
      ‘t.ffi.io_events = s.ffi.io_events ++ l'’ by
        (last_x_assum $ qspec_then ‘k' - (s.clock - 1)’ mp_tac>>simp[])>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      assume_tac (Q.SPECL [‘c’,‘s with clock := s.clock -1’,‘k' - (s.clock - 1)’]
                   panPropsTheory.evaluate_add_clock_io_events_mono)>>
      gvs[]>>
      fs[IS_PREFIX_APPEND]>>
      simp[LFINITE_LAPPEND_EQ_NIL]>>
      ‘(t' with clock := 0).clock = 0’ by simp[]>>
      drule_at Any div_no_trace_LNIL>>simp[]>>
      disch_then $ drule_at Any>>simp[]>>
      (impl_tac >-
        (strip_tac>>
         first_x_assum $ qspec_then ‘k + k' - (s.clock - 1)’ mp_tac>>fs[]>>
         qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
         drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k’ assume_tac>>gvs[])>>rw[]))
(* Call *)
  >- (simp[mrec_Call,empty_locals_defs,kvar_defs2]>>
      ntac 4 (TOP_CASE_TAC>>fs[])
      >- (rw[]>>fs[div_bind_cases]
          >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
              imp_res_tac div_imp_timeout>>fs[]>>
              drule div_no_trace_LNIL>>simp[]>>
              impl_tac >-
               (strip_tac>>
                last_x_assum $ qspec_then ‘SUC k’ mp_tac>>
                simp[dec_clock_def]>>
                first_x_assum $ qspec_then ‘k’ assume_tac>>fs[])>>
              first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
              imp_res_tac panPropsTheory.evaluate_io_events_mono>>
              strip_tac>>fs[LAPPEND_NIL_2ND])>>
          imp_res_tac nondiv_INR>>fs[]>>
          rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
          imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
          dxrule evaluate_min_clock>>rw[]>>
          rename [‘s with <|locals:=r;clock := k|>’]>>
          drule nondiv_evaluate'>>fs[]>>
          disch_then $ drule_at Any>>
          disch_then $ drule_at Any>>
          simp[]>>strip_tac>>
          pop_assum $ assume_tac o GSYM>>fs[]>>
          drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
          fs[]>>
          imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
          imp_res_tac trace_prefix_bind_append>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
          fs[LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
          last_assum $ qspec_then ‘SUC k’ (mp_tac o GSYM)>>
          rpt (TOP_CASE_TAC>>
               fs[kvar_defs2,empty_locals_defs,dec_clock_def,
                  div_bind_cases,kvar_defs2,
                  mrec_h_handle_call_ret_lemma])>>
          imp_res_tac trace_prefix_bind_div>>gvs[]>>
          (drule evaluate_add_clock_or_timeout>>fs[]>>
           disch_then $ drule_at Any>>strip_tac>>fs[])
          (** 3 goals **)
          >- (qmatch_goalsub_abbrev_tac ‘evaluate (_,tt)’>>
              qpat_abbrev_tac ‘X = evaluate _’>>
              Cases_on ‘X’>>fs[]>>rw[]>>
              drule panPropsTheory.evaluate_io_events_mono>>
              simp[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
              simp[LFINITE_LAPPEND_EQ_NIL]>>
              ‘tt.clock = 0’ by simp[Abbr‘tt’]>>
              drule_at Any div_no_trace_LNIL>>simp[]>>fs[Abbr‘tt’]>>
              disch_then $ drule_at Any>>simp[]>>
              impl_tac >-
               (strip_tac>>
                drule div_imp_timeout>>
                disch_then $ qspec_then ‘k'’ assume_tac>>fs[]>>
                first_x_assum $ qspec_then ‘SUC (k + k')’ mp_tac>>
                fs[]>>
                qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
                drule panPropsTheory.evaluate_add_clock_eq>>
                disch_then $ qspec_then ‘k'’ assume_tac>>rw[]>>gvs[])>>rw[])>>
          (** the remaining two **)
          imp_res_tac div_imp_timeout>>fs[]>>
          first_assum $ qspec_then ‘0’ mp_tac>>
          first_x_assum $ qspec_then ‘k' - (k + 1)’ mp_tac>>simp[]>>rw[]>>
          gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          first_assum $ qspec_then ‘SUC k’ (mp_tac o SIMP_RULE (srw_ss())[])>>
          simp[]>>rw[]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_,t'')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>
          drule_at Any div_no_trace_LNIL>>simp[]>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          (impl_tac >-
            (strip_tac>>
             drule div_imp_timeout>>
             disch_then $ qspec_then ‘k''’ assume_tac>>fs[]>>
             first_x_assum $ qspec_then ‘SUC (k + k'')’ mp_tac>>
             fs[]>>
             qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
             drule panPropsTheory.evaluate_add_clock_eq>>
             disch_then $ qspec_then ‘k''’ assume_tac>>rw[]>>gvs[])>>rw[]))>>
      (** s.clock ≠ 0 **)
      rw[]>>fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[dec_clock_def]>>
          drule div_imp_timeout>>simp[]>>
          disch_then $ qspec_then ‘s.clock - 1’ assume_tac>>fs[]>>
          gvs[]>>
          first_x_assum irule>>
          strip_tac>>
          drule div_imp_timeout>>simp[]>>
          disch_then $ qspec_then ‘k' + s.clock - 1’ assume_tac>>fs[]>>
          first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[])>>
      imp_res_tac nondiv_INR>>fs[dec_clock_def]>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
      imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      (**)
      qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>rw[]>>
      qabbrev_tac ‘tt = s.clock -1’>>
      Cases_on ‘k' ≤ tt’>>fs[NOT_LESS_EQUAL]
      >- (dxrule_then strip_assume_tac LESS_EQUAL_ADD>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          disch_then $ qspec_then ‘p’ assume_tac>>gvs[]>>
          rpt (TOP_CASE_TAC>>
               fs[kvar_defs2,empty_locals_defs,dec_clock_def,
                  div_bind_cases,
                  mrec_h_handle_call_ret_lemma])>>
          imp_res_tac trace_prefix_bind_div>>gvs[]>>
          (drule evaluate_add_clock_or_timeout>>fs[]>>
           disch_then $ drule_at Any>>strip_tac>>fs[])>>gvs[]>>
          qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          last_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
          qpat_x_assum ‘evaluate (q,_) = _’ assume_tac>>
          first_assum (fn h => rewrite_tac[h])>>simp[]>>
          qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
          first_x_assum irule>>
          strip_tac>>
          last_x_assum $ qspec_then ‘k'''’ mp_tac>>gvs[]>>
          rev_drule panPropsTheory.evaluate_add_clock_eq>>
          disch_then $ qspec_then ‘k''' + p’ assume_tac>>rw[]>>
          ‘k' + k''' + p = k''' + s.clock - 1’ by gvs[]>>gvs[])>>
      (** timeout at s.clock - 1 **)
      drule evaluate_add_clock_or_timeout>>fs[]>>
      disch_then $ drule_at Any>>strip_tac>>fs[]>>
      drule panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      first_assum $ qspec_then ‘k' - tt’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      ‘k' - tt + s.clock - 1 = k'’ by gvs[Abbr‘tt’]>>
      pop_assum (fn h => rewrite_tac[h])>>simp[]>>
      rpt (TOP_CASE_TAC>>
           fs[kvar_defs2,empty_locals_defs,dec_clock_def,
              div_bind_cases,
              mrec_h_handle_call_ret_lemma])>>
      imp_res_tac trace_prefix_bind_div>>gvs[]>>
      qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := _ + s.clock - 1|>) = _’ assume_tac>>
      (drule evaluate_add_clock_or_timeout>>fs[]>>
       disch_then $ drule_at Any>>strip_tac>>fs[])>>
      fs[div_bind_cases]>>
      imp_res_tac trace_prefix_bind_div>>gvs[]
      (*** 3 goals *)
      >- (qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
                       panPropsTheory.evaluate_add_clock_io_events_mono)>>
          gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
          first_assum $ qspec_then ‘0’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
          qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := s.clock - 1|>) = _’ assume_tac>>
          first_assum (fn h => rewrite_tac[h])>>simp[]>>
          rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, r''')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
          drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          impl_tac >-
           (strip_tac>>
            irule EQ_TRANS>>first_x_assum $ irule_at Any>>
            qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
            rev_drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[])>>rw[])
      (**2/3*)
      >- (qmatch_goalsub_abbrev_tac ‘_ = (SND X).ffi.io_events’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
                       panPropsTheory.evaluate_add_clock_io_events_mono)>>
          gvs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          fs[IS_PREFIX_APPEND]>>gvs[]>>
          fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
          fs[Once LAPPEND_ASSOC]>>
          fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
          first_assum $ qspec_then ‘0’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
          qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := s.clock - 1|>) = _’ assume_tac>>
          first_assum (fn h => rewrite_tac[h])>>simp[]>>
          rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, r'')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
          drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          impl_tac >-
           (strip_tac>>
            irule EQ_TRANS>>first_x_assum $ irule_at Any>>
            qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
            rev_drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[])>>rw[])>>
      (**1/3*)
      rpt (FULL_CASE_TAC>>gvs[]))>>
  (* DecCall *)
  simp[mrec_DecCall,empty_locals_defs]>>
  ntac 4 (TOP_CASE_TAC>>fs[])
  >- (rw[]>>fs[div_bind_cases]
      >- (imp_res_tac trace_prefix_bind_div>>fs[]>>
          imp_res_tac div_imp_timeout>>fs[]>>
          drule div_no_trace_LNIL>>simp[]>>
          impl_tac >-
           (strip_tac>>
            last_x_assum $ qspec_then ‘SUC k’ mp_tac>>
            simp[dec_clock_def]>>
            first_x_assum $ qspec_then ‘k’ assume_tac>>fs[])>>
          first_x_assum $ qspec_then ‘k’ assume_tac>>fs[]>>
          imp_res_tac panPropsTheory.evaluate_io_events_mono>>
          strip_tac>>fs[LAPPEND_NIL_2ND])>>
      imp_res_tac nondiv_INR>>fs[]>>
      rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
      imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
      dxrule evaluate_min_clock>>rw[]>>
      rename [‘s with <|locals:=r;clock := k|>’]>>
      drule nondiv_evaluate'>>fs[]>>
      disch_then $ drule_at Any>>
      disch_then $ drule_at Any>>
      simp[]>>strip_tac>>
      pop_assum $ assume_tac o GSYM>>fs[]>>
      drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
      fs[]>>
      imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
      imp_res_tac trace_prefix_bind_append>>fs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      last_assum $ qspec_then ‘SUC k’ (mp_tac o GSYM)>>
      rpt (TOP_CASE_TAC>>
           fs[kvar_defs2,empty_locals_defs,dec_clock_def,
              div_bind_cases,
              mrec_h_handle_deccall_ret_lemma])>>
      imp_res_tac trace_prefix_bind_div>>gvs[]>>
      (drule evaluate_add_clock_or_timeout>>fs[]>>
       disch_then $ drule_at Any>>strip_tac>>fs[])
      >- (qpat_abbrev_tac ‘X = evaluate _’>>
          Cases_on ‘X’>>fs[]>>rw[]>>
          drule panPropsTheory.evaluate_io_events_mono>>
          simp[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
          simp[LFINITE_LAPPEND_EQ_NIL]>>
          qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, r')’>>
          ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
          drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
          disch_then $ drule_at Any>>simp[]>>
          impl_tac >-
           (strip_tac>>
            irule EQ_TRANS>>first_x_assum $ irule_at Any>>
            qexists ‘SUC (k + k')’>>simp[]>>
            rev_drule panPropsTheory.evaluate_add_clock_eq>>
            disch_then $ qspec_then ‘k'’ assume_tac>>rw[]>>gvs[]>>
            pairarg_tac>>fs[])>>rw[])>>
      (* 2/3 & 3/3 *)
      rpt (pairarg_tac>>fs[])>>rw[]>>gvs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>
      first_assum $ qspec_then ‘SUC k’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      simp[]>>rw[]>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, st')’>>
      ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
      drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
      disch_then $ drule_at Any>>simp[]>>
      (impl_tac >-
        (strip_tac>>
         irule EQ_TRANS>>first_x_assum $ irule_at Any>>
         qexists ‘SUC (k'' + k)’>>simp[]>>
         rev_drule panPropsTheory.evaluate_add_clock_eq>>
         disch_then $ qspec_then ‘k''’ assume_tac>>rw[]>>
         gvs[]>>pairarg_tac>>fs[])>>rw[]))>>
  (* s.clock ≠ 0 *)
  rw[]>>fs[div_bind_cases]
  >- (imp_res_tac trace_prefix_bind_div>>fs[dec_clock_def]>>
      drule div_imp_timeout>>simp[]>>
      disch_then $ qspec_then ‘s.clock - 1’ assume_tac>>fs[]>>
      drule panPropsTheory.evaluate_io_events_mono>>
      simp[IS_PREFIX_APPEND]>>rw[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      first_x_assum irule>>
      strip_tac>>
      drule div_imp_timeout>>simp[]>>
      disch_then $ qspec_then ‘k' + s.clock - 1’ assume_tac>>fs[]>>
      first_x_assum $ qspec_then ‘k'’ assume_tac>>gvs[])>>
  imp_res_tac nondiv_INR>>fs[dec_clock_def]>>
  rename [‘_ = INR x’]>>Cases_on ‘x’>>fs[]>>
  imp_res_tac nondiv_imp_evaluate'>>fs[]>>gvs[]>>
  dxrule evaluate_min_clock>>rw[]>>
  drule nondiv_evaluate'>>fs[]>>
  disch_then $ drule_at Any>>
  disch_then $ drule_at Any>>
  simp[]>>strip_tac>>
  pop_assum $ assume_tac o GSYM>>fs[]>>
  drule_then (assume_tac o GSYM) evaluate_invariant_oracle>>
  fs[]>>
  imp_res_tac evaluate_nondiv_trace_eq>>fs[]>>
  imp_res_tac trace_prefix_bind_append>>fs[]>>
  imp_res_tac panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>gvs[]>>
  fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
  qhdtm_x_assum ‘fromList’ $ assume_tac o GSYM>>
  fs[LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
  (**)
  qpat_abbrev_tac ‘X = evaluate _’>>
  Cases_on ‘X’>>fs[]>>rw[]>>
  qabbrev_tac ‘tt = s.clock -1’>>
  Cases_on ‘k' ≤ tt’>>fs[NOT_LESS_EQUAL]
  >- (dxrule_then strip_assume_tac LESS_EQUAL_ADD>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘p’ assume_tac>>gvs[]>>
      rpt (TOP_CASE_TAC>>
           fs[kvar_defs2,empty_locals_defs,dec_clock_def,
              div_bind_cases,
              mrec_h_handle_deccall_ret_lemma])>>
      imp_res_tac trace_prefix_bind_div>>gvs[]>>
      (drule evaluate_add_clock_or_timeout>>fs[]>>
       disch_then $ drule_at Any>>strip_tac>>fs[])>>gvs[]>>
      qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>rw[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      last_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      qpat_x_assum ‘evaluate (q,_) = _’ assume_tac>>
      first_assum (fn h => rewrite_tac[h])>>simp[]>>
      qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>rw[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
      first_x_assum irule>>
      strip_tac>>
      last_x_assum $ qspec_then ‘k'''’ mp_tac>>gvs[]>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘k''' + p’ assume_tac>>rw[]>>
      ‘k' + k''' + p = k''' + s.clock - 1’ by gvs[]>>gvs[]>>
      pairarg_tac>>fs[])>>
  (** timeout at s.clock - 1 **)
  drule evaluate_add_clock_or_timeout>>fs[]>>
  disch_then $ drule_at Any>>strip_tac>>fs[]>>
  drule panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>gvs[]>>rw[]>>
  fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[]>>
  first_assum $ qspec_then ‘k' - tt’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
  ‘k' - tt + s.clock - 1 = k'’ by gvs[Abbr‘tt’]>>
  pop_assum (fn h => rewrite_tac[h])>>simp[]>>
  rpt (TOP_CASE_TAC>>
       fs[kvar_defs2,empty_locals_defs,dec_clock_def,
          div_bind_cases,
          mrec_h_handle_deccall_ret_lemma])>>
  imp_res_tac trace_prefix_bind_div>>gvs[]>>
  qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := _ + s.clock - 1|>) = _’ assume_tac>>
  drule evaluate_add_clock_or_timeout>>fs[]>>
  disch_then $ drule_at Any>>strip_tac>>fs[]>>
  fs[div_bind_cases]>>
  imp_res_tac trace_prefix_bind_div>>gvs[]
  (*** 2 goals ***)
  >- (pairarg_tac>>fs[]>>
      assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
                   panPropsTheory.evaluate_add_clock_io_events_mono)>>
      gvs[]>>
      imp_res_tac panPropsTheory.evaluate_io_events_mono>>
      fs[IS_PREFIX_APPEND]>>gvs[]>>
      fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
      fs[Once LAPPEND_ASSOC]>>
      fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
      rw[]>>gvs[]>>
      first_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
      qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := k'' + s.clock - 1|>) = _’ assume_tac>>
      first_assum (fn h => rewrite_tac[h])>>simp[]>>
      rw[]>>gvs[]>>
      simp[LFINITE_LAPPEND_EQ_NIL]>>
      qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_, st')’>>
      ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
      drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
      disch_then $ drule_at Any>>simp[]>>
      impl_tac >-
       (strip_tac>>
        irule EQ_TRANS>>first_x_assum $ irule_at Any>>
        qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
        qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := k'|>) = _’ assume_tac>>
        drule panPropsTheory.evaluate_add_clock_eq>>
        disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[]>>
        pairarg_tac>>fs[])>>rw[])>>
  (** last **)
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  assume_tac (Q.SPECL [‘q’,‘s with <|locals:=r;clock := s.clock -1|>’,‘k' - (s.clock - 1)’]
               panPropsTheory.evaluate_add_clock_io_events_mono)>>
  gvs[]>>
  imp_res_tac panPropsTheory.evaluate_io_events_mono>>
  fs[IS_PREFIX_APPEND]>>gvs[]>>
  fs[GSYM LAPPEND_fromList,LPREFIX_APPEND]>>
  fs[Once LAPPEND_ASSOC]>>
  fs[LFINITE_fromList,LAPPEND11_FINITE1]>>gvs[Abbr‘tt’]>>
  first_assum $ qspec_then ‘k''’ (mp_tac o SIMP_RULE (srw_ss()) [])>>
  qpat_x_assum ‘evaluate (q,s with <|locals := r; clock := k'' + s.clock - 1|>) = _’ assume_tac>>
  first_assum (fn h => rewrite_tac[h])>>simp[]>>
  rw[]>>gvs[]>>
  simp[LFINITE_LAPPEND_EQ_NIL]>>
  qmatch_asmsub_abbrev_tac ‘evaluate (_,tt) = (_,st'')’>>
  ‘tt.clock = 0’ by simp[Abbr‘tt’]>>fs[]>>
  drule_at Any div_no_trace_LNIL>>fs[Abbr‘tt’]>>
  disch_then $ drule_at Any>>simp[]>>
  impl_tac >-
   (strip_tac>>
    irule EQ_TRANS>>first_x_assum $ irule_at Any>>
    qexists ‘k + k' - (s.clock - 1)’>>simp[]>>
    qpat_x_assum ‘evaluate _ = (_,t' with clock := 0)’ assume_tac>>
    drule panPropsTheory.evaluate_add_clock_eq>>
    disch_then $ qspec_then ‘k’ assume_tac>>rw[]>>gvs[]>>
    pairarg_tac>>fs[])>>rw[]
QED

(**************************)

Definition evaluate_behaviour_def:
  evaluate_behaviour (prog,s) =
    if ∃k. case FST (evaluate (prog,s with clock := k)) of
            | SOME TimeOut => F
            | SOME (FinalFFI _) => F
            | SOME (Return _) => F
            | _ => T
    then Fail
    else
     case some res.
      ∃k t r outcome.
        evaluate (prog, s with clock := k) = (r,t) ∧
        (case r of
         | (SOME (FinalFFI e)) => outcome = FFI_outcome e
         | (SOME (Return _))   => outcome = Success
         | _ => F) ∧
        res = Terminate outcome t.ffi.io_events
      of
    | SOME res => res
    | NONE =>
      Diverge
         (build_lprefix_lub
           (IMAGE (λk. fromList
              (SND (evaluate (prog,s with clock := k))).ffi.io_events) UNIV))
End

Definition itree_behaviour_def:
  itree_behaviour pre fs (prog, s) =
  let trace = trace_prefix0 fs (itree_evaluate (prog,s)) in
    case some r.
           ∃n s'. ltree fs (mrec h_prog (h_prog (prog,s)))
               = FUNPOW Tau n (Ret (INR (r, s'))): 'a ptree
    of
      SOME r =>
        (case r of
           SOME (FinalFFI e) =>
             (case llist$toList trace of
                NONE => Fail
              | SOME io => Terminate (FFI_outcome e) (pre++io))
         | SOME (Return _) =>
             (case llist$toList trace of
                NONE => Fail
              | SOME io => Terminate Success (pre++io))
         | _ => Fail)
    | NONE => Diverge (LAPPEND (fromList pre) trace)
End

(* main proof : evaluate -> itree *)
(* the behaviour of the evaluate semantics is equal the behaviour of the
   corresponding itree evaluated using the ffi state from the evaluate semantics *)

Theorem evaluate_to_itree:
  evaluate_behaviour (prog,s) =
  itree_behaviour s.ffi.io_events (s.ffi.oracle,s.ffi.ffi_state) (prog,bst s)
Proof
  simp[evaluate_behaviour_def,itree_behaviour_def,trace_prefix0_eq_trace_prefix]>>
  rw[]>>
  DEEP_INTRO_TAC some_intro>>
  rw[]
  (* Fail *)
  >- (imp_res_tac nondiv_imp_evaluate>>
      dxrule evaluate_min_clock>>strip_tac>>gs[]>>
      Cases_on ‘evaluate (prog, s with clock := k)’>>fs[]>>
      ‘q ≠ SOME TimeOut ⇒ k'' ≤ k’ by
        (strip_tac>>
         CCONTR_TAC>>fs[NOT_LESS_EQUAL]>>
         imp_res_tac (GSYM LESS_ADD)>>fs[]>>
         drule panPropsTheory.evaluate_add_clock_eq>>fs[]>>
         qexists ‘p’>>strip_tac>>gvs[state_component_equality])>>
      rpt (FULL_CASE_TAC>>fs[])>>
      imp_res_tac LESS_EQUAL_ADD>>fs[]>>
      rev_drule panPropsTheory.evaluate_add_clock_eq>>
      disch_then $ qspec_then ‘p’ assume_tac>>fs[])
  >- (Cases_on ‘evaluate (prog, s with clock := k)’>>fs[]>>
      rpt (FULL_CASE_TAC>>fs[])>>
      imp_res_tac evaluate_imp_nondiv>>gvs[])
  >- (fs[]>>
      first_x_assum $ qspec_then ‘k’ assume_tac>>
      gvs[]>>
      Cases_on ‘r’>>fs[]>>
      rename [‘(SOME x,_)’]>>
      Cases_on ‘x’>>fs[]>>
      imp_res_tac evaluate_imp_nondiv>>gvs[]>>
      drule evaluate_nondiv_trace_eq>>fs[]>>
      strip_tac>>simp[]>>
      ‘LFINITE (fromList t.ffi.io_events)’
        by simp[LFINITE_fromList]>>
      pop_assum mp_tac>>
      first_assum (fn h => rewrite_tac[h])>>
      rewrite_tac[LFINITE_APPEND]>>strip_tac>>
      imp_res_tac to_fromList>>fs[from_toList]>>gvs[]>>
      qpat_x_assum ‘fromList _ = LAPPEND _ _’ mp_tac>>
      first_assum (fn h => once_rewrite_tac[GSYM h])>>
      rewrite_tac[LAPPEND_fromList]>>
      rewrite_tac[fromList_11]>>strip_tac>>
      simp[from_toList])>>
  DEEP_INTRO_TAC some_intro>>
  rw[]
  >- (rpt (CASE_TAC>>fs[])>>
      imp_res_tac nondiv_imp_evaluate>>gvs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[]>>
      last_x_assum $ qspec_then ‘k’ assume_tac>>gs[])>>
  irule EQ_SYM>>
  irule (iffLR lprefix_lubTheory.build_prefix_lub_intro)>>
  irule_at Any evaluate_io_events_lprefix_chain>>
  simp[lprefix_lubTheory.lprefix_lub_def]>>fs[]>>
  conj_asm1_tac>>rpt strip_tac>>gvs[]
  >- (qpat_abbrev_tac ‘X = evaluate _’>>
      Cases_on ‘X’>>fs[]>>
      ‘div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (prog,bst s)):'a ptree)’
        by (gvs[div_def]>>rw[]>>
            strip_tac>>
            imp_res_tac nondiv_INR>>gvs[]>>
            rename [‘Ret (INR x)’]>>Cases_on ‘x’>>gvs[])>>
      drule div_imp_timeout>>
      disch_then $ qspec_then ‘k’ assume_tac>>gvs[]>>
      drule timeout_div_LPREFIX>>simp[])>>
  (* least upper bound *)
  Cases_on ‘∀n. (∃k. less_opt n (SOME (LENGTH (SND (evaluate(prog,s with clock := k))).ffi.io_events)))’>>fs[]
  >- fs[LPREFIX_NTH]>>
  (* evaluate traces are bounded *)
  dxrule not_less_opt_lemma>>
  strip_tac>>gvs[]>>
  qabbrev_tac ‘x= s with clock := k'’>>
  ‘∀k. x.clock < k ⇒
       (SND (evaluate (prog,x))).ffi.io_events =
       (SND (evaluate (prog,x with clock := k))).ffi.io_events’
    by (rpt strip_tac>>
        first_x_assum $ qspec_then ‘k’ assume_tac>>
        qspecl_then [‘prog’,‘x’,‘k-x.clock’] assume_tac (panPropsTheory.evaluate_add_clock_io_events_mono)>>
        rfs[Abbr‘x’]>>
        gvs[GSYM IS_PREFIX_LENGTH_ANTI])>>
  ‘div (s.ffi.oracle,s.ffi.ffi_state) (mrec h_prog (h_prog (prog,bst s)):'a ptree)’
    by (gvs[div_def]>>rw[]>>
        strip_tac>>
        imp_res_tac nondiv_INR>>gvs[]>>
        rename [‘Ret (INR x)’]>>Cases_on ‘x’>>gvs[])>>
  ‘∀k. (SND (evaluate (prog,x))).ffi.io_events =
       (SND (evaluate (prog,x with clock := k + x.clock))).ffi.io_events’
    by (strip_tac>>
        Cases_on ‘k’>>simp[state_component_equality,Abbr‘x’])>>
  drule bounded_trace_eq>>fs[Abbr‘x’]>>
  strip_tac>>simp[]>>
  first_assum irule>>metis_tac[]
QED

(**************************)
(**************************)
