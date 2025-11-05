(*
    Misc Lemmas for Pancake ITree semantics and correspondence proof.
*)
Theory pan_itreeProps
Ancestors
  itreeTau pan_itreeSem panLang panSem
(*  misc[qualified] (* for read_bytearray *)
  wordLang[qualified] (* for word_op and word_sh *)*)
  ffi[qualified]
Libs
  preamble

(*** ltree / comp_ffi / div ***)

Theorem ltree_FUNPOW_Tau[simp]:
  ltree fs (FUNPOW Tau n t) = FUNPOW Tau n (ltree fs t)
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]
QED

Theorem ltree_not_Vis[simp]:
  ∀n e k. ltree fs t ≠ FUNPOW Tau n (Vis e k)
Proof
  qid_spec_tac ‘t’>>simp[Once SWAP_FORALL_THM]>>
  qid_spec_tac ‘fs’>>simp[Once SWAP_FORALL_THM]>>
  Induct>>rw[]
  >- (Cases_on ‘t’>>fs[]>>
      PairCases_on ‘a’>>simp[]>>
      CASE_TAC>>simp[]>>
      CASE_TAC>>simp[])>>
  Cases_on ‘t’>>fs[FUNPOW_SUC]>>
  PairCases_on ‘a’>>simp[]>>
  CASE_TAC>>simp[]>>
  CASE_TAC>>simp[]
QED

Theorem ltree_spin:
  ltree fs spin = spin
Proof
  simp[Once itree_bisimulation]>>
  qexists ‘CURRY {(ltree fs spin, spin)|T}’>>
  rw[]>>simp[]>- metis_tac[]>>
  pop_assum mp_tac>>simp[Once spin]>>rw[]>>
  irule_at Any (GSYM spin)>>metis_tac[]
QED

Theorem comp_ffi_FUNPOW_Tau[simp]:
comp_ffi fs (FUNPOW Tau n t) = comp_ffi fs t
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]
QED

Theorem ltree_bind[simp]:
  ltree (fs:'b fst) (itree_bind t k) =
  itree_bind (ltree fs t) (ltree (FST fs,SND (comp_ffi fs t)) o k)
Proof
  simp[Once itree_strong_bisimulation] >>
  qexists ‘CURRY {(ltree (fs:'b fst) (itree_bind t k),
                   itree_bind (ltree fs t) (ltree (FST fs, SND (comp_ffi fs t)) o k))|T}’ >>
  rw[EXISTS_PROD]>-metis_tac[PAIR]>>
  rename [‘ltree _ (itree_bind t _)’]
  >- (Cases_on ‘t’>>fs[itree_bind_thm]>>
      PairCases_on ‘a’>>simp[]>>
      CASE_TAC>>fs[]>>
      CASE_TAC>>fs[])
  >- (Cases_on ‘t’ >>fs[itree_bind_thm]
      >- metis_tac[]
      >- metis_tac[]>>
      PairCases_on ‘a’>>fs[]>>
      rpt (CASE_TAC>>fs[])>>
      metis_tac[])>>
  Cases_on ‘t’ >>fs[itree_bind_thm]
  >- metis_tac[]>>
  PairCases_on ‘a'’>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]
QED

Theorem comp_ffi_bind[simp]:
  ltree fs t = FUNPOW Tau n (Ret r) ⇒
  comp_ffi fs (itree_bind t k) =
  comp_ffi (FST fs, SND (comp_ffi fs t)) (k r)
Proof
  map_every qid_spec_tac [‘t’,‘fs’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>
  Cases_on ‘t’>>fs[]>>
  PairCases_on ‘a’>>fs[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]
QED

Theorem div_FUNPOW_Tau[simp]:
  div fs (FUNPOW Tau n X) = div fs X
Proof
  eq_tac>>
  Cases_on ‘fs’>>rw[div_def]
  >- (first_x_assum $ qspecl_then [‘n+n'’,‘r'’] assume_tac>>
      fs[FUNPOW_ADD,FUNPOW_eq_elim])>>
  strip_tac>>
  fs[FUNPOW_Ret_simp]
QED

Theorem ltree_div_bind[simp]:
  div fs X ⇒
  ltree fs (itree_bind X k) = ltree fs X:'a ptree
Proof
  strip_tac>>
  irule EQ_SYM>>
  rewrite_tac[Once itree_bisimulation]>>
  qexists ‘CURRY {(ltree fs X, ltree fs (itree_bind X k):'a ptree) | div fs X}’ >>
  fs[div_def]>>rw[EXISTS_PROD]>- metis_tac[PAIR]
  >- metis_tac[FUNPOW]
  >- (rename1 ‘ltree _ t’>>
      Cases_on ‘t’>>fs[]>>
      TRY (PairCases_on ‘a’>>fs[])>>
      rpt (CASE_TAC>>fs[])>>
      irule_at Any EQ_REFL>>
      irule_at Any EQ_REFL>>
      rpt strip_tac>>fs[GSYM FUNPOW_SUC])>>
  rename1 ‘ltree _ t’>>
  Cases_on ‘t’>>fs[]>>
  PairCases_on ‘a'’>>fs[]>>
  rpt (CASE_TAC>>fs[])
QED

Theorem div_bind1[simp]:
  div fs (X:'a ptree) ⇒ div fs (itree_bind X Y)
Proof
  rw[div_def]
QED

Theorem div_bind2[simp]:
  ltree fs X = FUNPOW Tau n (Ret r):'a ptree ⇒
  div fs (itree_bind X Y) = div (FST fs, SND (comp_ffi fs X)) (Y r)
Proof
  rw[]>>
  simp[]>>eq_tac>>rw[div_def]>>gs[FUNPOW_Tau_bind]>>
  strip_tac>>fs[]
  >- metis_tac[FUNPOW_ADD]>>
  fs[FUNPOW_Ret_simp]
QED

(* this should be the first to try with div + itree_bind case *)
Theorem div_bind_cases:
  div fs (itree_bind X k:'a ptree) =
  (div fs (X:'a ptree) ∨
   (∃n r. ltree fs X = FUNPOW Tau n (Ret r) :'a ptree ∧
          div (FST fs, SND (comp_ffi fs X)) (k r)))
Proof
  EQ_TAC>>strip_tac
  >- (Cases_on ‘div fs X’ >- simp[] >>
      irule OR_INTRO_THM2>>fs[]>>
      imp_res_tac div_bind2)
  >- simp[]>>
  simp[div_def,FUNPOW_Tau_bind]>>rw[]>>strip_tac>>
  fs[FUNPOW_Ret_simp]>>
  fs[div_def]
QED

Theorem div_imp_spin:
  div fs t ⇒ ltree fs t = spin:'a ptree
Proof
  rw[]>>
  irule EQ_SYM>>
  simp[Once itree_bisimulation] >>
  qexists ‘CURRY {(spin,ltree fs t)|fs,t| div fs t}’>>
  rw[EXISTS_PROD]>- metis_tac[PAIR]>>
  TRY (qpat_x_assum ‘_ = spin’ mp_tac >> rw[Once spin]>>NO_TAC)>>
  last_x_assum kall_tac>>
  rename1 ‘ltree fs t’ >>
  Cases_on ‘t’ >>fs[]
  >- (qpat_x_assum ‘_ = spin’ mp_tac>>simp[Once spin]>>rw[]>>
      Cases_on ‘fs’>>fs[]>>
      first_x_assum $ irule_at Any>>simp[])>>
  PairCases_on ‘a’>>fs[]>>
  CASE_TAC>>fs[]>>
  qpat_x_assum ‘_ = spin’ mp_tac>>simp[Once spin]>>
  Cases_on ‘fs’>>fs[div_def]>>
  metis_tac[FUNPOW_SUC]
QED

Theorem div_eq_ltree_spin:
  div fs t ⇔ ltree fs t = spin:'a ptree
Proof
  EQ_TAC >- metis_tac[div_imp_spin]>>
  simp[div_def]>>rw[]>>strip_tac>>
  pop_assum mp_tac>>
  rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
  strip_tac>>gvs[FUNPOW_Ret_simp]
QED

Theorem nondiv_ltree_bind_lemma:
  itree_bind (ltree fs t) (ltree (FST fs,SND (comp_ffi fs t)) ∘ k) =
  FUNPOW Tau n (Ret r) : 'a ptree ⇒
  ∃n' r'.
    ltree fs t = FUNPOW Tau n' (Ret r') : 'a ptree ∧
    ∃n''.
      ltree (FST fs,SND (comp_ffi fs t)) (k r') = FUNPOW Tau n'' (Ret r) : 'a ptree
      ∧ n' + n'' = n
Proof
  strip_tac>>
  Cases_on ‘div fs t’>>fs[]
  >- (imp_res_tac ltree_div_bind>>fs[div_def])>>
  fs[FUNPOW_Tau_bind]>>fs[FUNPOW_Ret_simp]
QED

Theorem nondiv_ltree_bind_lemma':
  itree_bind (ltree fs t) (ltree fs' ∘ k) =
  FUNPOW Tau n (Ret r) : 'a ptree
  ∧ fs' = (FST fs,SND (comp_ffi fs t)) ⇒
  ∃n' r'.
    ltree fs t = FUNPOW Tau n' (Ret r') : 'a ptree ∧
    ∃n''.
      ltree (FST fs,SND (comp_ffi fs t)) (k r') = FUNPOW Tau n'' (Ret r) : 'a ptree
      ∧ n' + n'' = n
Proof
  rw[]>>
  imp_res_tac nondiv_ltree_bind_lemma>>
  gvs[]
QED

(**************************)

Theorem nondiv_INR:
  ltree fs (mrec h_prog (h_prog (p,s))) = FUNPOW Tau n (Ret r): 'a ptree ⇒
  ∃x. r = INR x
Proof
  map_every qid_spec_tac [‘r’,‘fs’,‘s’,‘p’,‘n’]>>
  completeInduct_on ‘n’>>fs[]>>
  Cases_on ‘n’>>rw[]
  >- (rpt (pop_assum mp_tac)>>
      map_every qid_spec_tac [‘r’,‘fs’,‘s’,‘p’]>>
      Induct>>
      rw[mrec_prog_simps,mrec_If,Once mrec_While,mrec_Call,mrec_DecCall,
         mrec_Seq]>>
      TRY (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>NO_TAC)>>
      fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
      rpt (PURE_FULL_CASE_TAC>>fs[])>>
      gvs[]>>
      FULL_CASE_TAC>>fs[]>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>rename1 ‘FUNPOW Tau n _’>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>rename1 ‘FUNPOW Tau n _’>>
      Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])>>
  rpt (pop_assum mp_tac)>>
  map_every qid_spec_tac [‘r’,‘fs’,‘s’,‘p’]>>
  rename1 ‘SUC n’>>fs[FUNPOW_SUC]>>
  Induct>>
  rw[mrec_prog_simps]>>
  TRY (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>NO_TAC)
  >~ [‘ExtCall’]>-
   (fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])
  >~ [‘ShMemLoad’]>-
   (fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])
  >~ [‘ShMemStore’]>-
   (fs[mrec_ExtCall,mrec_ShMemLoad,mrec_ShMemStore]>>
    rpt (PURE_FULL_CASE_TAC>>fs[])>>gvs[]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>
    rename1 ‘FUNPOW Tau n _’>>Cases_on ‘n’>>fs[FUNPOW_SUC]>>gvs[])
  (* Dec *) >-
   (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>gvs[])
  >~ [‘Seq’] >-
   (fs[mrec_Seq]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[GSYM FUNPOW]>>
    fs[FUNPOW_Ret_simp]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ Y) _’>>
    Cases_on ‘div (FST fs, SND (comp_ffi fs X)) Y’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>gvs[])
  >~ [‘If’] >-
   (fs[mrec_If]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]>>
    fs[FUNPOW_Tau_bind]>>gvs[]>>
    imp_res_tac div_imp_spin>>fs[spin_bind]
    >- (qhdtm_x_assum ‘FUNPOW’ mp_tac>>  (* ??? *)
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    qhdtm_x_assum ‘FUNPOW’ mp_tac>>
    rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
    rw[]>>fs[FUNPOW_Ret_simp])
  >~ [‘While’] >-
   (fs[Once mrec_While]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
    Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])>>
    fs[FUNPOW_Tau_bind]>>
    rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
    fs[GSYM FUNPOW]>>
    fs[FUNPOW_Ret_simp]>>
    ‘n - SUC n' < SUC n’ by simp[]>>
    res_tac>>gvs[])
  (* Call / DecCall *)
  >- (fs[mrec_Call,mrec_DecCall]>>
      rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
      (Cases_on ‘div fs X’>>fs[]
       >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
           qhdtm_x_assum ‘FUNPOW’ mp_tac>>
           rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
           rw[]>>fs[FUNPOW_Ret_simp]))>>
      fs[FUNPOW_Tau_bind]>>
      fs[mrec_h_handle_call_ret_lemma]>>
      fs[mrec_h_handle_deccall_ret_lemma]>>
      (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
      fs[GSYM FUNPOW]>>
      fs[FUNPOW_Ret_simp]>>
      qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ Y) _’>>
      Cases_on ‘div (FST fs, SND (comp_ffi fs X)) Y’>>fs[]>>
      fs[FUNPOW_Tau_bind]>>gvs[]>>
      imp_res_tac div_imp_spin>>fs[spin_bind]
       >- (qhdtm_x_assum ‘FUNPOW’ mp_tac>>
           rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
           rw[]>>fs[FUNPOW_Ret_simp]))>>
      qhdtm_x_assum ‘FUNPOW’ mp_tac>>
      rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
      rw[]>>fs[FUNPOW_Ret_simp])>>
  (fs[mrec_Call,mrec_DecCall]>>
   rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
   qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ X) _’>>
   (Cases_on ‘div fs X’>>fs[]
    >- (imp_res_tac div_imp_spin>>fs[spin_bind]>>
        qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC n’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp]))>>
   fs[FUNPOW_Tau_bind]>>
   fs[mrec_h_handle_call_ret_lemma]>>
   fs[mrec_h_handle_deccall_ret_lemma]>>
   (rpt (FULL_CASE_TAC>>fs[])>>gvs[]>>
   fs[GSYM FUNPOW]>>
   fs[FUNPOW_Ret_simp]>>
   qmatch_asmsub_abbrev_tac ‘itree_bind (ltree _ Y) _’>>
   Cases_on ‘div (FST fs, SND (comp_ffi fs X)) Y’>>fs[]>>
   fs[FUNPOW_Tau_bind]>>gvs[]>>
   (imp_res_tac div_imp_spin>>fs[spin_bind]
    >- (qhdtm_x_assum ‘FUNPOW’ mp_tac>>
        rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
        rw[]>>fs[FUNPOW_Ret_simp])))>>
   qhdtm_x_assum ‘FUNPOW’ mp_tac>>
   rewrite_tac[Once (Q.SPEC ‘SUC (n - SUC n')’ spin_FUNPOW_Tau)]>>
   rw[]>>fs[FUNPOW_Ret_simp])
QED

(*** trace_prefix ***)

(* move to HOL - llistTheory? *)
Definition lnil_def:
 lnil = LUNFOLD (λu. SOME ((),[||])) ()
End

Theorem lnil:
  [||]:::lnil = lnil
Proof
  simp[lnil_def]>>
  simp[SimpR“$=”,Once LUNFOLD]
QED
(* end of move *)

Theorem trace_prefix_spin:
  trace_prefix fs spin = [||]
Proof
  Cases_on ‘fs’>>
  simp[trace_prefix_def]>>
  simp[LFLATTEN_EQ_NIL]>>
  irule every_coind>>
  qexists ‘{lnil}’>>
  simp[]>>rw[]>>
  TRY (fs[Once (GSYM lnil)]>>NO_TAC)>>
  simp[lnil_def]>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qexists ‘CURRY {((r,spin),())|fs|T}’>>
  rw[] >>
  simp[Once spin]   
QED

Theorem trace_prefix_bind_append:
  (∃n. ltree fs t = FUNPOW Tau n (Ret r)) ⇒
  trace_prefix fs (itree_bind t k) =
    LAPPEND (trace_prefix fs t) (trace_prefix (FST fs,SND (comp_ffi fs t)) (k r))
Proof
  simp[PULL_EXISTS]>>
  map_every qid_spec_tac [‘fs’,‘r’,‘k’,‘t’] >>
  Induct_on ‘n’ >>
  rw[FUNPOW_SUC]
  >- (Cases_on ‘t’ >> fs[]>>
      PairCases_on ‘a’>>fs[]>>
      rpt (CASE_TAC>>fs[]))>>
  Cases_on ‘t’ >> fs[] >>
  PairCases_on ‘a’>>fs[]>>
  rpt (CASE_TAC>>fs[])>>
  last_x_assum $ qspecl_then [‘g (INL (INR l))’,‘k’,‘r’,‘(FST fs,f)’] assume_tac>>gvs[]
QED

Theorem trace_prefix_FUNPOW_Tau[simp]:
  trace_prefix fs (FUNPOW Tau n t) = trace_prefix fs t
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>simp[]
QED

Theorem trace_prefix_bind_div:
  div fs t ⇒
  trace_prefix fs (itree_bind t k) = trace_prefix fs t
Proof
  rw[trace_prefix_def]>>
  Cases_on ‘fs’>>rename [‘(x,x')’]>>
  AP_TERM_TAC>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qexists ‘CURRY {((x', itree_bind t k),(x',t))| div (x,x') t}’>>
  rw[EXISTS_PROD] >>simp[]>>
  last_x_assum kall_tac>>
  rpt (CASE_TAC>>fs[])>>
  gvs[div_def]>>rw[]>>
  first_assum $ qspec_then ‘SUC n’ assume_tac>>
  fs[FUNPOW_SUC]
QED

Theorem trace_prefpix0_spin:
  trace_prefix0 fs spin = [||]
Proof
  Cases_on ‘fs’>>
  simp[trace_prefix0_def]>>
  simp[LFLATTEN_EQ_NIL]>>
  irule every_coind>>
  qexists ‘{lnil}’>>
  simp[]>>rw[]>>
  TRY (fs[Once (GSYM lnil)]>>NO_TAC)>>
  simp[lnil_def]>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qexists ‘CURRY {((r,spin),())|fs|T}’>>
  rw[] >>
  simp[Once spin]
QED

Theorem trace_prefix0_FUNPOW_Tau[simp]:
  trace_prefix0 fs (FUNPOW Tau n t) = trace_prefix0 fs t
Proof
  map_every qid_spec_tac [‘fs’,‘t’,‘n’]>>
  Induct>>rw[FUNPOW_SUC]>>simp[]
QED

(* move to itreeTauTheory *)
Theorem itree_unfold_spin:
  (∀u. f (Tau u) = Tau' u) ⇒
  itree_unfold f spin = spin
Proof
  rw[]>>
  simp[Once itree_bisimulation]>>
  qexists‘CURRY {(itree_unfold f spin, spin)}’>>
  rw[]>>pop_assum mp_tac>>
  simp[Once spin]>>simp[Once itree_unfold]>>rw[]>>
  irule (GSYM spin)
QED

Theorem trace_eq_lemma:
  trace_prefix0 fs
          (itree_unfold
             (λx.
                  case x of
                    Ret r => Ret' (case r of INL l => ARB | INR r => r)
                  | Tau t => Tau' t
                  | Vis e f => Vis' e (λx. f (INL x))) (t: 'a ptree)) =
  trace_prefix fs (t: 'a ptree)
Proof
  Cases_on ‘fs’>>
  simp[trace_prefix0_def,trace_prefix_def]>>
  AP_TERM_TAC>>
  simp[Once LUNFOLD_BISIMULATION]>>
  qmatch_goalsub_abbrev_tac ‘itree_unfold f t’>>
  qexists ‘CURRY {((r, itree_unfold f t),(r,t))|r,t|T}’>>
  simp[Abbr‘f’]>>rw[EXISTS_PROD]>>simp[]>>
  CASE_TAC>>fs[]>>
  CASE_TAC>>fs[]>>
  TRY (fs[Once itree_unfold]>>NO_TAC)>>
  ntac 2 (CASE_TAC>>gvs[])>>
  CASE_TAC>>gvs[]>>
  TRY (CASE_TAC>>gvs[])>>
  qhdtm_x_assum ‘itree_unfold’ mp_tac>>
  fs[Once itree_unfold]>>rw[]>>simp[o_DEF]
QED

Theorem trace_prefix0_eq_trace_prefix:
  trace_prefix0 fs (itree_evaluate (p, s)) = trace_prefix fs (mrec h_prog (h_prog (p,s)):'a ptree)
Proof
  Cases_on ‘fs’>>fs[]>>
  qpat_abbrev_tac ‘X = mrec _ _’>>
  fs[itree_evaluate_def]>>
  Cases_on ‘∃t. strip_tau X t’>>fs[]
  >- (imp_res_tac strip_tau_FUNPOW>>fs[]>>
      Cases_on ‘t’>>fs[itree_unfold_FUNPOW_Tau]
      >- (fs[Abbr‘X’]>>
          imp_res_tac mrec_FUNPOW_Ret_INR>>fs[]>>
          simp[Once itree_unfold])>>
      irule trace_eq_lemma)>>
  imp_res_tac strip_tau_spin>>fs[]>>
  simp[itree_unfold_spin,trace_prefix_spin,trace_prefix0_spin]
QED
