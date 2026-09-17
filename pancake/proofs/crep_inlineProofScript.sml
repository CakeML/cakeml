(*
  Correctness proof for function inlining pass
*)
Theory crep_inlineProof
Ancestors
  crepLang crepSem crepProps crep_inline
  pan_commonProps pan_common
  prim_rec iterate
Libs
  preamble

Definition state_rel_def:
  state_rel s t ⇔
    s.globals = t.globals ∧
    s.code = t.code ∧
    s.memory = t.memory ∧
    s.memaddrs = t.memaddrs ∧
    s.sh_memaddrs = t.sh_memaddrs ∧
    s.clock = t.clock ∧
    s.be = t.be ∧
    s.ffi = t.ffi ∧
    s.base_addr = t.base_addr ∧
    s.top_addr = t.top_addr
End

Definition locals_rel_def:
  locals_rel s t ⇔
    s.locals SUBMAP t.locals
End

Definition locals_strong_rel_def:
  locals_strong_rel s t ⇔
    s.locals = t.locals
End

Theorem OPT_MMAP_SOME_ALL:
  ∀f l.
    ((∃x. OPT_MMAP f l = SOME x) ⇔ (∀x. MEM x l ⇒ ?y. f x = SOME y))
Proof
  rpt strip_tac >>
  Induct_on `l` >> simp[OPT_MMAP_def] >>
  strip_tac >>
  eq_tac >>
  rpt strip_tac >> gvs[]
QED

Theorem OPT_MMAP_ALL_EQ:
  ∀f g l.
    (∀x. MEM x l ==> f x = g x) ==> (OPT_MMAP f l = OPT_MMAP g l)
Proof
  rpt strip_tac >>
  Induct_on `l` >> gs[]
QED

Theorem eval_original_extend_locals:
  ∀s e wl l.
    eval s e = SOME wl /\
    s.locals SUBMAP l ⇒
    eval (s with locals := l) e = SOME wl
Proof
  recInduct eval_ind >>
  rpt strip_tac >> gs[eval_def] >>
  imp_res_tac SUBMAP_FLOOKUP_EQN >>
  qpat_x_assum `_ = SOME wl` mp_tac
  >>~- ([`OPT_MMAP`],
    TOP_CASE_TAC >>
    imp_res_tac $ iffLR OPT_MMAP_SOME_ALL >> gs[] >>
    `!a. MEM a es ⇒ eval s a = eval (s with locals := l) a` by (
       rpt strip_tac >> qpat_x_assum `!_. MEM _ _ ⇒ ?_. _` imp_res_tac >>
       res_tac >> simp[]
    ) >>
    drule OPT_MMAP_ALL_EQ >> gvs[] >>
    disch_tac >>
    `OPT_MMAP (\a. eval (s with locals := l) a) es = SOME x` by metis_tac[] >> gvs[]) >>
  last_x_assum imp_res_tac >> fs[] >>
  every_case_tac >> gs[mem_load_def]
QED

Theorem eval_original_extend_locals_rel:
  ∀s e wl t.
    eval s e = SOME wl ==>
    locals_rel s t ∧ state_rel s t ⇒
    eval t e = SOME wl
Proof
  simp[locals_rel_def, state_rel_def] >>
  rpt strip_tac >>
  drule eval_original_extend_locals >>
  disch_then $ qspec_then `t.locals` assume_tac >> gs[] >>
  `s with locals := t.locals = t` by simp[state_component_equality] >> gvs[]
QED

Theorem eval_state_locals_rel:
  ∀s e wl t.
    eval s e = SOME wl ∧  state_rel s t ∧ locals_rel s t ⇒
    eval t e = SOME wl
Proof
  rpt strip_tac >>
  irule eval_original_extend_locals_rel >>
  qrefine `s` >> simp[]
QED


Theorem eval_optmmap_state_locals_rel:
  ∀s es ws t.
    OPT_MMAP (eval s) es = SOME ws ∧ state_rel s t ∧ locals_rel s t ⇒
    OPT_MMAP (eval t) es = SOME ws
Proof
  gen_tac >> gen_tac >> qid_spec_tac `s` >>
  Induct_on `es` >> gs[OPT_MMAP_def] >>
  rpt strip_tac >>
  `eval t h = SOME h'` by metis_tac[eval_state_locals_rel] >>
  qrefine `h'` >> gs[] >>
  last_x_assum $ qspecl_then [`s`, `t'`, `t`] assume_tac >> gs[]
QED


Theorem SUBMAP_IMP_FUPDATE_SUBMAP:
  ∀f g x y.
    f SUBMAP g ⇒  f |+ (x, y) SUBMAP g |+ (x, y)
Proof
   rpt strip_tac >>
   gs[SUBMAP_DEF] >>
   rpt strip_tac >>
   gvs[FAPPLY_FUPDATE_THM]
QED

Theorem SUBMAP_IMP_DOMSUB_SUBMAP:
  ∀f g x.
    f SUBMAP g ⇒ f \\ x SUBMAP g \\ x
Proof
  rpt strip_tac >> gs[SUBMAP_DEF] >>
  rpt strip_tac >> gvs[DOMSUB_FAPPLY_THM]
QED

Theorem SUBMAP_IMP_DOMSUB_FUPDATE:
  ∀f g x y.
    f SUBMAP g ⇒ f \\ x SUBMAP g |+ (x, y)
Proof
 rpt strip_tac >> gs[SUBMAP_DEF] >>
 rpt strip_tac >> gvs[DOMSUB_FAPPLY_THM, FAPPLY_FUPDATE_THM]
QED

Theorem SUBMAP_IMP_FUPDATE_LIST_SUBMAP:
  ∀x y f g.
    f SUBMAP g ∧ LENGTH x = LENGTH y ⇒ f |++ ZIP(x, y) SUBMAP g |++ ZIP(x, y)
Proof
  Induct >> fs[FUPDATE_LIST_THM]
  >> rpt strip_tac
  >> Cases_on `y` >> fs[FUPDATE_LIST_THM]
  >> last_x_assum irule >> fs[SUBMAP_IMP_FUPDATE_SUBMAP]
QED


Theorem res_var_submap_res_var:
  ∀f g x y.
    f SUBMAP g ⇒ res_var f (x,y) SUBMAP res_var g (x, y)
Proof
  rpt strip_tac >>
  Cases_on `y` >> gs[res_var_def] >> gs[SUBMAP_IMP_DOMSUB_SUBMAP, SUBMAP_IMP_FUPDATE_SUBMAP]
QED

Definition locals_ext_rel_def:
  locals_ext_rel a b a' b' ⇔
    FDIFF a'.locals (FDOM a.locals) = FDIFF b'.locals (FDOM b.locals)
End

Theorem locals_rel_dec_clock:
  ∀s t.
    locals_rel s t ∧ state_rel s t ⇒
    locals_rel (dec_clock s) (dec_clock t) ∧ state_rel (dec_clock s) (dec_clock t)
Proof
  gvs[dec_clock_def, locals_rel_def, state_rel_def]
QED

Theorem opt_mmap_some_then_subset_fdom:
  ∀vs fm vals. OPT_MMAP (FLOOKUP fm) vs = SOME vals ⇒ set vs ⊆ FDOM fm
Proof
  Induct >> rw[flookup_thm] >> fs[]
QED

Theorem evaluate_locals_same_fdom:
  ∀p s r s'.
    evaluate (p, s) = (r, s') ∧
    (case r of
      | NONE => T
      | SOME (Continue n) => T
      | SOME (Break n) => T
      | _ => F) = T ⇒
    FDOM s.locals = FDOM s'.locals
Proof
  recInduct evaluate_ind >> rpt conj_tac
  >~ [`evaluate (While _ _, _) = _`]
  >- (
    rpt strip_tac >>
    qpat_x_assum `evaluate _ = (r, s')` mp_tac >>
    simp[Once evaluate_def] >>
    rpt TOP_CASE_TAC
    >- (
      disch_tac >> fs[CaseEq "result"]
    ) >>
    disch_tac >>
    `(dec_clock s).locals = s.locals` by fs[dec_clock_def] >>
    pairarg_tac >> gs[CaseEq "option", CaseEq "result", CaseEq "num"]
  )
  >~ [`evaluate (Dec _ _ _, _) = _`]
  >- (
    gs[evaluate_def, CaseEq "option", state_component_equality] >> rpt strip_tac >>
    TRY (imp_res_tac EQ_FDOM_SUBMAP) >>
    pairarg_tac >> gs[] >>
    Cases_on `FLOOKUP s.locals v` >> gvs[res_var_def, flookup_thm] >>
    fs[ABSORPTION_RWT] >>
    qpat_x_assum `_ = FDOM st.locals` $ gs o single o GSYM >> fs[DELETE_INSERT, DELETE_NON_ELEMENT_RWT, ABSORPTION_RWT]
  )
  >~ [`evaluate (Seq _ _, _) = _`]
  >- (
    gs[evaluate_def] >> rpt strip_tac >>
    pairarg_tac >> fs[] >>
    Cases_on `res = NONE` >> fs[]
  )
  >~ [`evaluate (If _ _ _, _) = _`]
  >- (
    rpt strip_tac >>
   fs[evaluate_def, CaseEq "option", CaseEq "word_lab"]
  )
  >~ [`evaluate (Call _ _ _, _) = _`]
  >- (
    rpt strip_tac >>
    Cases_on `s.clock` >>
    fs[evaluate_def, CaseEq "option", CaseEq "pair$prod", CaseEq "word_lab", CaseEq "result", CaseEq "bool"] >> gvs[]
    >> fs [FDOM_FUPDATE_LIST]
    >> simp[Once UNION_COMM] >> irule EQ_SYM
    >> simp[GSYM SUBSET_UNION_ABSORPTION]
    >> DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] >> fs[]
    >> imp_res_tac opt_mmap_some_then_subset_fdom
  )
  >~ [‘evaluate (Primitive _ _ _, _) = _’] >-
   (rpt strip_tac
    >> gvs [evaluate_def, AllCaseEqs()]
    >> gvs [FDOM_FUPDATE_LIST, MAP_ZIP, EVERY_MEM, FLOOKUP_DEF,
            IS_SOME_EXISTS, EXTENSION]
    >> metis_tac [])
  >> rpt strip_tac >>
  gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", state_component_equality,
    set_globals_def, CaseEq "ffi_result"
  ]
  >- (
    qpat_x_assum `_ = s'.locals` $ rw o single o GSYM >>
    gvs[flookup_thm, ABSORPTION_RWT]
  )
  >>~- ([`sh_mem_op _ _ _ _`],
  qpat_x_assum `_ = (_, s')` mp_tac >>
  Cases_on `op` >>
  fs[CaseEq "option", CaseEq "word_lab", sh_mem_op_def, sh_mem_load_def, sh_mem_store_def] >>
  TRY (IF_CASES_TAC) >> fs[CaseEq "ffi_result", set_var_def] >>
  TRY (TOP_CASE_TAC) >> fs[CaseEq "ffi_result"] >>
  disch_tac >> gvs[flookup_thm, state_component_equality, CaseEq "result"] >>
  qpat_x_assum `_ = s'.locals` $ rw o single o GSYM >> fs[ABSORPTION_RWT]
  ) >>
  Cases_on `s.clock` >> gvs[dec_clock_def]
QED

Theorem evaluate_locals_same_fdom':
  ∀p s r s'.
    evaluate (p, s) = (r, s') ∧
    (r = NONE ∨ (∃n. r = SOME (Break n)) ∨ (∃n. r = SOME (Continue n))) ⇒
    FDOM s.locals = FDOM s'.locals
Proof
  rpt strip_tac >>
  drule evaluate_locals_same_fdom >> fs[]
QED

(* Need *)
Theorem evaluate_state_locals_rel_strong:
  ∀p s r s' t.
    evaluate (p, s) = (r, s') ∧
    r ≠ SOME Error ∧
    locals_rel s t ∧ state_rel s t ⇒
    ∃t'.
      evaluate (p, t) = (r, t') ∧ state_rel s' t' ∧
      case r of
        | NONE => locals_rel s' t' ∧ locals_ext_rel s s' t t'
        | SOME (Break n) => locals_rel s' t' ∧ locals_ext_rel s s' t t'
        | SOME (Continue n) => locals_rel s' t' ∧ locals_ext_rel s s' t t'
        | SOME Error => F
        | _ => T
Proof
  recInduct evaluate_ind >>
  rpt conj_tac
  >~ [`evaluate (While _ _, _)`]
  >- (
    completeInduct_on `s.clock` >>
    rpt strip_tac >>
    qpat_x_assum `_ = (r, s')` mp_tac >>
    PURE_ONCE_REWRITE_TAC[evaluate_def] >>
    imp_res_tac eval_state_locals_rel >> fs[] >>
    fs[CaseEq "option", CaseEq "word_lab"] >>
    disch_tac >> fs[] >>
    qpat_x_assum `!_ _. eval _ _ = _ ⇒ eval _ _ = _` imp_res_tac >> fs[] >>
    Cases_on `w = 0w` >> fs[]
    >- gs[locals_ext_rel_def] >>
    `t.clock = s.clock` by fs[state_rel_def] >> fs[] >>
    Cases_on `s.clock = 0` >> fs[]
    >- gvs[empty_locals_def, state_rel_def] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> gvs[] >>
    imp_res_tac locals_rel_dec_clock >>
    qpat_x_assum `!_. _ < s.clock ⇒ _` $ qspec_then `s1'.clock` mp_tac >> impl_tac
    >- (
      drule evaluate_clock >> disch_tac >>
      irule LET_TRANS >>
      qrefine `(dec_clock s).clock` >> fs[dec_clock_def]
    ) >>
    disch_then $ qspec_then `s1'` mp_tac >> fs[] >>
    disch_tac >>
    qpat_x_assum `!_. res' ≠ SOME Error ∧ _ ∧ _ ⇒ _` imp_res_tac >> fs[] >>
    Cases_on `res' = SOME Error` >> fs[] >>
    gvs[CaseEq "option", CaseEq "result", CaseEq "num"] >>
    TRY (
      qpat_x_assum `!_. locals_rel s1' _ ∧ state_rel s1' _ ⇒ _` $ qspec_then `s1` mp_tac >> fs[] >>
      disch_tac >> fs[] >>
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[locals_ext_rel_def, dec_clock_def] >>
      NO_TAC
    ) >>
    `(dec_clock t).locals = t.locals` by fs[dec_clock_def] >>
    `(dec_clock s).locals = s.locals` by fs[dec_clock_def] >>
    fs[locals_ext_rel_def]
  )
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    rpt strip_tac >> fs[evaluate_def] >>
    imp_res_tac eval_state_locals_rel >>
    gs[CaseEq "option", CaseEq "word_lab"] >>
    first_x_assum imp_res_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    gvs[CaseEq "option" , CaseEq "result"] >>
    last_x_assum $ qspec_then `t with locals := t.locals |+ (v, value)` mp_tac >> impl_tac
    >- (
      fs[state_rel_def, locals_rel_def] >>
      imp_res_tac SUBMAP_IMP_FUPDATE_SUBMAP >>
      pop_assum $ fs o single
    ) >>
    disch_tac >> gvs[] >>
    conj_tac
    >- gs[state_rel_def] >>
    Cases_on `r` >> TRY (Cases_on `x`) >> fs[] >>
    fs[locals_rel_def, locals_ext_rel_def] >>
    conj_tac
    >>~- ([`res_var _ _ SUBMAP res_var _ _`],
      Cases_on `FLOOKUP s.locals v` >> fs[res_var_def] >>
      rev_drule $ iffLR SUBMAP_FLOOKUP_EQN >>
      disch_tac >>
      pop_assum imp_res_tac >> fs[res_var_def, SUBMAP_IMP_FUPDATE_SUBMAP] >>
      Cases_on `FLOOKUP t.locals v` >> fs[res_var_def, SUBMAP_IMP_DOMSUB_FUPDATE, SUBMAP_IMP_DOMSUB_SUBMAP]) >>
    Cases_on `FLOOKUP s.locals v` >> fs[res_var_def] >>
    rev_drule $ iffLR SUBMAP_FLOOKUP_EQN >>
    disch_then imp_res_tac >>
    TRY (qpat_assum `FLOOKUP t.locals _ = SOME _` kall_tac >> gs[res_var_def]) >>
    gs[flookup_thm] >>
    imp_res_tac evaluate_locals_same_fdom' >> gs[] >>
    `v ∈  FDOM st'.locals` by metis_tac[COMPONENT] >>
    `v ∈  FDOM st.locals` by metis_tac[COMPONENT] >>
    fs[ABSORPTION_RWT, GSYM DRESTRICT_DOMSUB] >>
    qpat_x_assum `v INSERT FDOM s.locals = _` $ gs o single o GSYM >>
    qpat_x_assum `v INSERT FDOM t.locals = _` $ gs o single o GSYM >>
    fs[DELETE_INSERT, FDIFF_FUPDATE]
    >>~- ([`t.locals ' v`], fs[ABSORPTION_RWT]) >>
    Cases_on `FLOOKUP t.locals v` >> fs[res_var_def, FDIFF_FUPDATE, FDIFF_FDOMSUB_INSERT, DELETE_NON_ELEMENT_RWT]
    >>~- ([`FLOOKUP t.locals v = NONE`],
      fs[FDIFF_def, compl_insert, GSYM DRESTRICT_DOMSUB] >>
      qpat_x_assum `_ \\ _ = _ \\ _` $ fs o single o GSYM >>
      irule EQ_SYM >> fs[] >>
      irule DOMSUB_NOT_IN_DOM >> fs[FDOM_DRESTRICT, flookup_thm]
    ) >>
    fs[FDIFF_def, compl_insert, GSYM DRESTRICT_DOMSUB, flookup_thm, fmap_eq_flookup, DOMSUB_FLOOKUP_THM] >>
    rpt strip_tac >>
    Cases_on `v = x'` >>
    qpat_x_assum `!_. _` $ qspec_then `x'` assume_tac >> gs[] >>
    fs[FLOOKUP_SIMP] >> metis_tac[flookup_thm]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    rpt strip_tac >> fs[evaluate_def] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    Cases_on `res' = NONE` >> fs[] >>
    qpat_x_assum `!_. locals_rel s _ ∧ state_rel s _ ⇒ _` $ qspec_then `t` assume_tac >> gs[] >>
    TRY (last_x_assum $ qspec_then `s1` assume_tac >> gs[]) >>
    Cases_on `r` >> fs[locals_rel_def, locals_ext_rel_def]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rpt strip_tac >> fs[evaluate_def] >>
    imp_res_tac eval_state_locals_rel >> fs[] >>
    gs[CaseEq "option", CaseEq "word_lab"] >>
    pop_assum imp_res_tac >> fs[]
  )
  >~ [`evaluate (Call _ _ _, _)`]
  >- suspend "Call"
  >~ [‘evaluate (Primitive _ _ _, _)’] >-
   (rpt strip_tac
    >> gvs [evaluate_def, PULL_EXISTS, AllCaseEqs()]
    >> rename1 `OPT_MMAP _ rvs = SOME arg_vals`
    >> rename1 `crep_primop _ arg_vals = SOME result_vals`
    >> rename1 `EVERY _ lvs`
    >> qexistsl_tac [`arg_vals`, `result_vals`]
    >> simp[]
    >> `set lvs ⊆ FDOM s.locals` by (
         fs[EVERY_MEM, SUBSET_DEF, IS_SOME_EXISTS, FLOOKUP_DEF] >> metis_tac[])
    >> `set lvs ⊆ FDOM t.locals` by (
         fs[locals_rel_def, SUBMAP_DEF, SUBSET_DEF] >> metis_tac[])
    >> rpt conj_tac
    >- (`∀a. MEM a rvs ⇒ FLOOKUP s.locals a = FLOOKUP t.locals a` by (
          rpt strip_tac >>
          `∃y. FLOOKUP s.locals a = SOME y` by metis_tac[OPT_MMAP_SOME_ALL] >>
          fs[locals_rel_def] >>
          imp_res_tac (iffLR SUBMAP_FLOOKUP_EQN) >> simp[]) >>
        drule OPT_MMAP_ALL_EQ >> disch_tac >> fs[])
    >- (fs[EVERY_MEM, locals_rel_def] >> rpt strip_tac >>
        first_x_assum drule >> simp[IS_SOME_EXISTS] >> strip_tac >>
        imp_res_tac (iffLR SUBMAP_FLOOKUP_EQN) >> metis_tac[])
    >- fs[state_rel_def]
    >- (fs[locals_rel_def] >>
        irule SUBMAP_mono_FUPDATE_LIST >>
        simp[MAP_ZIP] >>
        irule SUBMAP_DRESTRICT_MONOTONE >> simp[])
    >> simp[locals_ext_rel_def, fmap_eq_flookup, FLOOKUP_FDIFF]
    >> qx_gen_tac `k`
    >> `k ∈ FDOM (s.locals |++ ZIP (lvs,result_vals)) ⇔ k ∈ FDOM s.locals` by (
         simp[FDOM_FUPDATE_LIST, MAP_ZIP] >>
         fs[SUBSET_DEF] >> metis_tac[])
    >> simp[]
    >> Cases_on `k ∈ FDOM s.locals` >> simp[]
    >> `k ∉ set lvs` by (fs[SUBSET_DEF] >> metis_tac[])
    >> `FLOOKUP (t.locals |++ ZIP (lvs, result_vals)) k = FLOOKUP t.locals k`
         by (irule flookup_fupdate_zip_not_mem >> fs[])
    >> simp[])
  >> fs[evaluate_def] >> rpt strip_tac
  >- fs[locals_ext_rel_def] >>
  imp_res_tac eval_optmmap_state_locals_rel >> fs[] >>
  imp_res_tac eval_state_locals_rel >> fs[] >>
  gs[CaseEq "option", CaseEq "word_lab"]
  >~ [`SOME (Return _) = _`]
  >- ( (* Return case *)
    pop_assum kall_tac
    >> pop_assum imp_res_tac >> fs[]
    >> every_case_tac >> gvs[state_rel_def, empty_locals_def]
  )
  >> pop_assum imp_res_tac >> fs[]
  >>~- ([`locals_ext_rel a a b b`], fs[locals_ext_rel_def])
  >>~- ([`_ with memory := _ = _`],
    qrefine `t with memory := m` >>
    gvs[state_rel_def, locals_rel_def, locals_ext_rel_def]
  )
  >- (
    (* Assign *)
    fs[locals_rel_def] >>
    imp_res_tac SUBMAP_FLOOKUP_EQN >> fs[] >> conj_tac
    >- gvs[state_rel_def] >>
    gvs[SUBMAP_IMP_FUPDATE_SUBMAP] >>
    gs[locals_ext_rel_def, FDIFF_def, compl_insert, flookup_thm, GSYM DRESTRICT_DOMSUB] >>
    irule EQ_SYM >>
    irule DOMSUB_NOT_IN_DOM >> fs[FDOM_DRESTRICT]
  )
  >- (
    (* StoreGlob *)
    `t.globals = s.globals` by fs[state_rel_def] >>
    gvs[set_globals_def, state_rel_def, locals_rel_def, locals_ext_rel_def]
  )
  >- (
    (* ShMem *)
    fs[locals_rel_def] >>
    Cases_on `is_load op` >> gs[CaseEq "option"] >>
    drule $ iffLR SUBMAP_FLOOKUP_EQN >>
    disch_then imp_res_tac >>
    Cases_on `op` >>
    fs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def] >>
    `t.ffi = s.ffi ∧ t.sh_memaddrs = s.sh_memaddrs` by fs[state_rel_def] >> gs[CaseEq "word_lab"]
    >>~- ([`addr ∈ _.sh_memaddrs `],
      Cases_on `addr ∈ s.sh_memaddrs` >> gs[CaseEq "ffi_result"]
      >- gvs[set_var_def, state_rel_def, locals_rel_def, locals_ext_rel_def, SUBMAP_IMP_FUPDATE_SUBMAP, flookup_thm, ABSORPTION, FDIFF_def] >>
      gvs[state_rel_def, empty_locals_def, locals_rel_def, locals_ext_rel_def]
    )
  )
  >- (
    (* Likely Raise *)
    fs[state_rel_def, empty_locals_def]
  )
  >- (
    (* Tick *)
    `t.clock = s.clock` by fs[state_rel_def] >> fs[] >>
    Cases_on `s.clock = 0` >>
    gvs[state_rel_def, dec_clock_def, locals_rel_def, locals_ext_rel_def, empty_locals_def]
  ) >>
  fs[locals_rel_def] >>
  drule $ iffLR SUBMAP_FLOOKUP_EQN >>
  disch_then imp_res_tac >>
  gvs[state_rel_def, CaseEq "ffi_result", locals_ext_rel_def]
QED

Theorem opt_mmap_flookup_some_then_same_fdom:
  ∀vs fm vals upd_vals.
    OPT_MMAP (FLOOKUP fm) vs = SOME vals ∧ LENGTH vs = LENGTH upd_vals
      ⇒  FDOM (fm |++ ZIP(vs, upd_vals)) = FDOM fm
Proof
  rpt strip_tac
  >> imp_res_tac opt_mmap_some_then_subset_fdom
  >> metis_tac[FDOM_FUPDATE_LIST, MAP_ZIP, UNION_COMM, SUBSET_UNION_ABSORPTION]
QED

Resume evaluate_state_locals_rel_strong[Call]:
  rpt strip_tac >> fs[evaluate_def] >>
  gs[CaseEq "option", CaseEq "word_lab", CaseEq "prod"] >>
  qpat_x_assum `_ = (r, s')` mp_tac >>
  TOP_CASE_TAC >> fs[] >>
  disch_tac >>
  imp_res_tac eval_optmmap_state_locals_rel >>
  imp_res_tac eval_state_locals_rel >> fs[] >>
  first_assum imp_res_tac >>
  `t.clock = s.clock` by fs[state_rel_def] >> fs[] >>
  `t.code = s.code` by fs[state_rel_def] >> fs[] >>
  Cases_on `s.clock = 0` >> fs[]
  >- gvs[state_rel_def, empty_locals_def] >>
  gs[CaseEq "option", CaseEq "prod", CaseEq "result", CaseEq "bool"] >>
  first_x_assum $ qspec_then `dec_clock t with locals := newlocals` mp_tac >> impl_tac
  >>~- ([`locals_rel (dec_clock _ with locals := _) (dec_clock _ with locals := _)`],
    fs[locals_rel_def, state_rel_def, empty_locals_def, dec_clock_def])
  >> disch_tac >> gvs[]
  >>~- ([`state_rel (empty_locals _) (empty_locals _)`],
    fs[state_rel_def, empty_locals_def])
  >- (
    (* Return-assign case *)
    fs[lookup_locals_eq_map_vars]
    >> imp_res_tac eval_optmmap_state_locals_rel >> fs[]
    >> conj_tac
    >- fs[state_rel_def]
    >> fs[locals_rel_def, locals_ext_rel_def]
    >> conj_tac
    >- (
      drule SUBMAP_IMP_FUPDATE_LIST_SUBMAP
      >> disch_then $ qspecl_then [`rts`, `retvs`] assume_tac >> fs[]
    )
    >> fs[FDIFF_def]
    >> simp[fmap_eq_flookup, FLOOKUP_DRESTRICT]
    >> rpt strip_tac >> Cases_on `x ∈ FDOM s.locals` >> fs[]
    >> Cases_on `MEM x rts` >> fs[]
    >- (
      fs[FDOM_FLOOKUP, MEM_EL]
      >> DEP_REWRITE_TAC [update_eq_zip_flookup]
      >> fs[]
    )
    >> fs[GSYM flookup_thm, GSYM lookup_locals_eq_map_vars]
    >> DEP_REWRITE_TAC [flookup_fupdate_zip_not_mem] >> fs[flookup_thm]
    >> gvs[MEM_EL, GSYM flookup_thm]
    >> imp_res_tac opt_mmap_el >> fs[]
  )
  (* Exception, with handler case *)
  >> first_x_assum $ qspec_then `t'' with locals := t.locals` mp_tac >> impl_tac
  >- fs[locals_rel_def, state_rel_def]
  >> disch_tac >> fs[]
  >> every_case_tac >> fs[locals_ext_rel_def]
QED

Finalise evaluate_state_locals_rel_strong;


Theorem evaluate_state_locals_rel:
  ∀p s r s' t.
    evaluate (p, s) = (r, s') ⇒
    r ≠ SOME Error ==>
    locals_rel s t ∧ state_rel s t ⇒
    ∃t'.
      evaluate (p, t) = (r, t') ∧ state_rel s' t' ∧
      case r of
        | NONE => locals_rel s' t'
        | SOME (Break n) => locals_rel s' t'
        | SOME (Continue n) => locals_rel s' t'
        | SOME Error => F
        | _ => T
Proof
  rpt strip_tac >>
  drule_all evaluate_state_locals_rel_strong >>
  disch_tac >>
  Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
QED

Theorem single_dec_evaluate:
  ∀p s r s' v e val .
    eval s e = SOME val ∧
    evaluate (p, s with locals := s.locals |+ (v, val)) = (r, s') ∧
    r ≠ SOME Error ==>
    ∃t'. evaluate (Dec v e p, s) = (r, t') ∧ state_rel s' t'
Proof
  rpt strip_tac >> gs[evaluate_def, state_rel_def]
QED

Theorem nested_decs_evaluate:
  !vs es p s r s' vals.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH es ∧
    ALL_DISTINCT vs /\
    (!v. MEM v vs ⇒ !e. MEM e es ⇒ ¬MEM v (var_cexp e)) ∧
    evaluate (p, s with locals := s.locals |++ ZIP (vs, vals)) = (r, s') ∧
    r ≠ SOME Error ==>
    ∃t'.
      evaluate (nested_decs vs es p, s) = (r, t') ∧ state_rel s' t'
Proof
  Induct_on `vs` >> gs[nested_decs_def, evaluate_def]
  >- (
    rpt strip_tac >> gs[FUPDATE_LIST, FUPDATE_DEF] >>
    `s with locals := s.locals = s` by simp[state_component_equality] >> gvs[state_rel_def]
  ) >>
  rpt strip_tac >>
  Cases_on `es` >> gs[nested_decs_def] >>
  Cases_on `vals` >> gvs[FUPDATE_LIST_THM] >>
  drule opt_mmap_length_eq >> disch_tac >> fs[] >>
  `OPT_MMAP (eval (s with locals := s.locals |+ (h, h''))) t = SOME t'` by (
    qpat_x_assum `OPT_MMAP (eval s) t = SOME t'` $ gvs o single o GSYM >>
    irule OPT_MMAP_ALL_EQ >>
    rpt strip_tac >>
    irule update_locals_not_vars_eval_eq' >> gs[]
  ) >>
  last_x_assum drule >> gs[] >>
  disch_then $ qspecl_then [`p`, `r`, `s'`] assume_tac >> gs[] >>
  rev_drule single_dec_evaluate >>
  disch_then $ qspecl_then [`nested_decs vs t p`, `r`, `t''`, `h`] assume_tac >> gs[state_rel_def]
QED

Theorem genlist_less_than:
  ∀n a v. MEM v (GENLIST (λx. (a:num) + SUC x) n) ⇒ a < v
Proof
  Induct >> gs[GENLIST] >>
  rpt strip_tac >> gs[LESS_ADD_SUC]
QED

Theorem genlist_not_in:
  ∀n a v. v ≤ a ⇒ ¬MEM v (GENLIST (λx. (a:num) + SUC x) n)
Proof
  spose_not_then assume_tac >> gs[] >>
  drule genlist_less_than >> decide_tac
QED

Theorem genlist_all_distinct:
  ∀n a. ALL_DISTINCT (GENLIST (λx. a + SUC x) n)
Proof
  Induct >> gs[GENLIST, ALL_DISTINCT_SNOC, MEM_GENLIST]
QED

Theorem eval_dec_clock_eq:
  ∀s e. eval (dec_clock s) e = eval s e
Proof
  simp[eval_upd_clock_eq, dec_clock_def]
QED

Theorem opt_mmap_eval_dec_clock_eq:
  ∀s es. OPT_MMAP (eval (dec_clock s)) es = OPT_MMAP (eval s) es
Proof
  rpt gen_tac >>
  irule OPT_MMAP_CONG >> fs[] >>
  rpt strip_tac >> gs[eval_dec_clock_eq]
QED

Theorem not_has_return_not_evaluate_return:
  ∀p s.
    ¬has_return p ⇒
    ∃r s'.
      evaluate (p, s) = (r, s') ∧
      case r of
        | SOME (Return retv) => F
        | _ => T
Proof
  recInduct evaluate_ind >>
  rw[has_return_def]
  >~ [`While _ _`]
  >- (
    simp[Once evaluate_def] >> every_case_tac >> gs[] >> every_case_tac >> gs[]
  ) >>
  gs[evaluate_def]
  >~ [`sh_mem_op`]
  >- (
    rpt (TOP_CASE_TAC >> gs[]) >>
    Cases_on `op` >> gs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def] >>
    rpt (TOP_CASE_TAC >> gs[])
  ) >>
  every_case_tac >> gs[]
QED

Theorem not_has_return_not_evaluate_return':
  ∀p s r s' retv.
    ¬(has_return p) ∧
    evaluate (p, s) = (r, s') ⇒
    r ≠ SOME (Return retv)
Proof
  rpt strip_tac >>
  dxrule not_has_return_not_evaluate_return >> gvs[] >>
  qrefine `s` >> gvs[]
QED

Theorem res_var_commutes_strong:
  res_var (res_var lc (h,FLOOKUP lc' h)) (n,FLOOKUP lc' n) =
  res_var (res_var lc (n,FLOOKUP lc' n)) (h,FLOOKUP lc' h)
Proof
  Cases_on `n ≠ h` >> metis_tac[res_var_commutes]
QED

Theorem res_var_foldl_commutes_strong:
  ∀h vs lc1 lc2.
    res_var (FOLDL res_var lc1 (ZIP (vs, MAP (FLOOKUP lc2) vs))) (h, FLOOKUP lc2 h) =
    FOLDL res_var (res_var lc1 (h, FLOOKUP lc2 h)) (ZIP (vs, MAP (FLOOKUP lc2) vs))
Proof
  Induct_on `vs` >> fs[] >>
  rpt strip_tac >>
  fs[res_var_commutes_strong]
QED

Theorem evaluate_nested_decs_locals_nested_res_var:
 ∀p s r s' vs es vals.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH es ∧
    ALL_DISTINCT vs /\
    (!v. MEM v vs ⇒ !e. MEM e es ⇒ ¬MEM v (var_cexp e)) ∧
    evaluate (p, s with locals := s.locals |++ ZIP (vs, vals)) = (r, s') ==>
    ∃t'.
      evaluate (nested_decs vs es p, s) = (r, t') ∧ state_rel s' t' ∧
        t'.locals = FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs))
Proof
  Induct_on `vs` >> rw[]
  >- (
    Cases_on `vals` >> fs[FUPDATE_LIST, nested_decs_def] >>
    qrefine `s'` >> fs[state_rel_def] >>
    `s with locals := s.locals = s` by fs[state_component_equality] >> fs[]
  ) >>
  Cases_on `es` >> Cases_on `vals` >> gs[nested_decs_def, FUPDATE_LIST_THM, evaluate_def] >>
  pairarg_tac >> gs[] >>
  last_x_assum $ qspecl_then [`p`, `s with locals := s.locals |+ (h, h'')`, `r`, `s'`, `t`, `t'`] mp_tac >> impl_tac
  >- (
    fs[] >>
    qpat_x_assum `OPT_MMAP _ _ = SOME _` $ rw o single o GSYM >>
    irule OPT_MMAP_ALL_EQ >>
    rpt strip_tac >>
    first_x_assum $ qspec_then `h` assume_tac >> rfs[] >>
    pop_assum imp_res_tac >>
    imp_res_tac update_locals_not_vars_eval_eq'' >> fs[state_component_equality] >>
    `s with locals := s.locals = s` by fs[state_component_equality] >> simp[]
  ) >>
  disch_tac >> fs[] >>
  `MAP (FLOOKUP (s.locals |+ (h, h''))) vs = MAP (FLOOKUP s.locals) vs` by (
    fs[MAP_EQ_f] >>
    rpt strip_tac >>
    qpat_x_assum `!_. _` imp_res_tac >>
    fs[FLOOKUP_UPDATE] >>
    Cases_on `h = e` >> fs[]
  ) >> fs[] >>
  conj_tac
  >- (
    Cases_on `FLOOKUP s.locals h` >> gvs[res_var_def, state_rel_def]
  ) >>
  gvs[res_var_foldl_commutes_strong]
QED

Theorem evaluate_nested_decs_locals_nested_res_var_drule:
 ∀p s r s' vs es vals r1 t'.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH es ∧
    ALL_DISTINCT vs /\
    (!v. MEM v vs ⇒ !e. MEM e es ⇒ ¬MEM v (var_cexp e)) ∧
    evaluate (p, s with locals := s.locals |++ ZIP (vs, vals)) = (r, s') ∧
    evaluate (nested_decs vs es p, s) = (r1, t') ==>
      r1 = r ∧ state_rel s' t' ∧
        t'.locals = FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs))
Proof
  rpt gen_tac >> rpt disch_tac >> fs[]
  >> drule_all evaluate_nested_decs_locals_nested_res_var
  >> disch_tac >> gvs[]
QED


Theorem not_some_is_none:
  ∀a. (∀v. a ≠ SOME v) ⇔ a = NONE
Proof
  Cases >> fs[]
QED

Theorem fdom_eq_flookup_thm:
  ∀f1 f2.
    FDOM f1 = FDOM f2 ⇔
    (∀x. (∃v. FLOOKUP f1 x = SOME v) ⇒ (∃v. FLOOKUP f2 x = SOME v)) ∧
    (∀x. FLOOKUP f1 x = NONE ⇒ FLOOKUP f2 x = NONE)
Proof
  fs[GSYM SUBSET_ANTISYM_EQ, SUBSET_DEF, FDOM_FLOOKUP] >>
  rpt strip_tac >>
  `∀x. ((∃v. FLOOKUP f2 x = SOME v) ⇒ (∃v. FLOOKUP f1 x = SOME v)) = (FLOOKUP f1 x = NONE ⇒ FLOOKUP f2 x = NONE)` by (
    gen_tac >>
    gs[Once MONO_NOT_EQ] >>
    qspec_then `FLOOKUP f1 x` assume_tac not_some_is_none >>
    qspec_then `FLOOKUP f2 x` assume_tac not_some_is_none >>
    metis_tac[]
  ) >>
  metis_tac[]
QED

Theorem flookup_res_var_is_mem_zip_eq:
  ∀xs x lc1 lc2.
    MEM x xs ⇒
    FLOOKUP (FOLDL res_var lc1 (ZIP (xs, MAP (FLOOKUP lc2) xs))) x = FLOOKUP lc2 x
Proof
  Induct_on `xs` >>
  gs[] >>
  rpt strip_tac >>
  gs[GSYM res_var_foldl_commutes_strong] >>
  Cases_on `FLOOKUP lc2 h` >> gs[res_var_def, FLOOKUP_UPDATE]
QED

Theorem not_var_prog_flookup_eqn:
  ∀p s r s' x.
    evaluate (p, s) = (r, s') ∧
    ¬MEM x (var_prog p) ∧
    (case r of
      | NONE => T
      | SOME (Break n) => T
      | SOME (Continue n) => T
      | _ => F) = T ⇒
    FLOOKUP s'.locals x = FLOOKUP s.locals x
Proof
  recInduct evaluate_ind >>
  rpt conj_tac >>
  gs[var_prog_def]
  >~ [`evaluate (While _ _, _)`]
  >- (
    rpt strip_tac >>
    qpat_x_assum `_ = (r, s')` mp_tac >>
    simp[Once evaluate_def] >>
    gs[CaseEq "option", CaseEq "word_lab"] >>
    disch_tac >> fs[] >>
    Cases_on `w = 0w` >> Cases_on `s.clock = 0` >> fs[] >>
    pairarg_tac >> gs[CaseEq "option", CaseEq "result", dec_clock_def, CaseEq "num"]
  )
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    gs[evaluate_def, CaseEq "option"] >>
    rpt strip_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    qpat_x_assum `_ = s'` $ fs o single o GSYM >>
    fs[flookup_res_var_thm, FLOOKUP_UPDATE]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    rpt strip_tac >>
    gs[evaluate_def] >>
    pairarg_tac >> fs[] >>
    Cases_on `res = NONE` >> fs[]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rpt strip_tac >> gs[evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    Cases_on `w ≠ 0w` >> fs[]
  )
  >~ [`evaluate (Call _ _ _, _)`]
  >- (
    rpt strip_tac >> gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod", CaseEq "bool", CaseEq "option", CaseEq "result"]
    >> `~MEM x rts` by (every_case_tac >> fs[])
    >> metis_tac[flookup_fupdate_zip_not_mem]
  )
  >~ [`evaluate (ShMem _ _ _, _)`]
  >- (
    rpt strip_tac >> gvs[evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    Cases_on `op` >> fs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def, set_var_def]
    >>~ [`addr ∈  s.sh_memaddrs`] >>
    Cases_on `addr ∈ s.sh_memaddrs` >>
    gvs[CaseEq "option", CaseEq "ffi_result", CaseEq "result", FLOOKUP_UPDATE, CaseEq "word_lab"]
  )
  >~ [`evaluate (Primitive _ _ _, _)`]
  >- (
    rpt strip_tac >> gvs[evaluate_def, AllCaseEqs()] >>
    irule flookup_fupdate_zip_not_mem >> fs[]
  ) >>
  rpt strip_tac >>
  gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "ffi_result", set_globals_def, FLOOKUP_UPDATE] >>
  Cases_on `s.clock = 0` >> gvs[dec_clock_def]
QED

Theorem SUBMAP_DIFF_LIST:
  ∀l vs vals.
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    (∀v. MEM v vs ⇒ v ∉ FDOM l) ⇒
    l SUBMAP l |++ ZIP (vs, vals)
Proof
  Induct_on `vs` >>
  rpt strip_tac >>
  Cases_on `vals` >> fs[]
  >- fs[FUPDATE_LIST] >>
  fs[FUPDATE_LIST_THM] >>
  `~MEM h (MAP FST (ZIP (vs, t)))` by fs[MAP_ZIP] >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then $ qspecl_then [`h'`, `l`] assume_tac >> fs[] >>
  last_x_assum $ qspecl_then [`l`, `t`] mp_tac >> fs[] >>
  disch_tac >>
  drule SUBMAP_TRANS >> disch_then irule >>
  fs[SUBMAP_FUPDATE_FLOOKUP] >>
  disj1_tac >>
  drule_all flookup_fupdate_zip_not_mem >>
  disch_then $ qspec_then `l` assume_tac >> fs[] >>
  fs[flookup_thm]
QED

Theorem nested_decs_evaluate_sublocals_strong:
  !vs es p s r s' vals t.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH es ∧
    ALL_DISTINCT vs /\
    (!v. MEM v vs ⇒ !e. MEM e es ⇒ ¬MEM v (var_cexp e)) ∧
    (!v. MEM v vs ⇒ v ∉ FDOM t) ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    t SUBMAP s.locals ∧
    (case r of
      | NONE => T
      | SOME (Break n) => T
      | SOME (Continue n) => T
      | _ => F) = T ==>
    ∃t'.
      evaluate (nested_decs vs es p, s) = (r, t') ∧ state_rel s' t' ∧
      (FDIFF s.locals (FDOM t)) SUBMAP t'.locals
Proof
  rpt strip_tac >>
  drule evaluate_state_locals_rel_strong >>
  `r ≠ SOME Error` by gs[CaseEq "option", CaseEq "result"] >>
  simp[] >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      simp[locals_rel_def] >>
      irule SUBMAP_mono_FUPDATE_LIST >>
      imp_res_tac opt_mmap_length_eq >> fs[] >>
      imp_res_tac MAP_ZIP >> simp[] >>
      irule SUBMAP_DRESTRICT_MONOTONE >> simp[]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos last) evaluate_nested_decs_locals_nested_res_var >>
  disch_then drule >> simp[] >>
  disch_tac >> fs[] >>
  Cases_on `r` >> TRY (Cases_on `x`) >> fs[locals_rel_def] >>
  conj_tac
  >>~ [`FDIFF _ _ SUBMAP _`]
  >>~- ([`FDIFF _ _ SUBMAP _`],
    fs[locals_ext_rel_def] >>
    simp[SUBMAP_FLOOKUP_EQN] >>
    rpt strip_tac >>
    Cases_on `MEM x vs`
    >- (
      drule $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] flookup_res_var_is_mem_zip_eq >>
      disch_then $ qspecl_then [`t'.locals`, `s.locals`] assume_tac >> fs[FLOOKUP_FDIFF]
    ) >>
    drule_at (Pos last) $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] flookup_res_var_distinct_zip_eq >>
    disch_then $ qspecl_then [`MAP (FLOOKUP s.locals) vs`, `t'.locals`] mp_tac >> impl_tac
    >- (
      simp[LENGTH_MAP]
    ) >>
    disch_tac >>
    qpat_x_assum `FDIFF _ _ = FDIFF _ _` $ assume_tac o SRULE [GSYM SUBMAP_ANTISYM] >> fs[] >>
    qpat_x_assum `FDIFF (_ |++ _) _ SUBMAP FDIFF _ _` mp_tac >>
    simp[SUBMAP_FLOOKUP_EQN, FLOOKUP_FDIFF] >>
    imp_res_tac evaluate_locals_same_fdom' >> fs[] >>
    disch_then irule >> fs[FLOOKUP_FDIFF] >>
    qpat_x_assum `FDOM (t |++ _) = FDOM _` $ rewrite_tac o single o GSYM >>
    simp[GSYM flookup_thm] >>
    conj_tac
    >- (
      qpat_assum `_ ∉ FDOM _` $ assume_tac o SRULE [GSYM flookup_thm] >>
      pop_assum $ rewrite_tac o single o GSYM >>
      irule flookup_fupdate_zip_not_mem >>
      imp_res_tac opt_mmap_length_eq >> gs[]
    ) >>
    qpat_x_assum `FLOOKUP _.locals _ = SOME _` $ rewrite_tac o single o GSYM >>
    irule flookup_fupdate_zip_not_mem >>
    imp_res_tac opt_mmap_length_eq >> gs[]
  ) >>
  gs[state_rel_def]
QED

(* Need *)
Theorem general_simulate_arg_load_correct:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (∀x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (∀x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t'
Proof
  rpt strip_tac >>
  drule evaluate_state_locals_rel >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (tmp_vars, vals) |++ ZIP (vs, vals) ` mp_tac >> impl_tac
  >- (
    conj_tac
    >- fs[] >>
    conj_tac
    >- (
      fs[locals_rel_def]
      >> irule SUBMAP_IMP_FUPDATE_LIST_SUBMAP >> fs[]
      >> irule SUBMAP_DIFF_LIST >> fs[]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  drule evaluate_state_locals_rel >> fs[] >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (tmp_vars, vals) |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      fs[locals_rel_def]
      >> irule SUBMAP_IMP_FUPDATE_LIST_SUBMAP >> fs[]
      >> irule SUBMAP_IMP_FUPDATE_LIST_SUBMAP >> fs[]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  rev_drule_at (Pos $ el 3) nested_decs_evaluate >>
  disch_then $ qspecl_then [`MAP Var tmp_vars`, `p`, `s with locals := s.locals |++ ZIP (tmp_vars, vals)`, `r`, `t''`, `vals`] mp_tac >>
  impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> fs[LENGTH_GENLIST]
    )
    >- simp[LENGTH_MAP]
    >- (
      rpt strip_tac >> gvs[MEM_MAP, var_cexp_def]
    ) >>
    fs[]
  ) >>
  disch_tac >> fs[] >>
  drule nested_decs_evaluate >>
  disch_then $ drule_at (Pos $ el 2) >>
  disch_then $ drule_at (Pos last) >>
  disch_then $ drule_at (Pos last) >> impl_tac
  >- (
    conj_tac
    >- (
      imp_res_tac opt_mmap_length_eq >> gvs[LENGTH_GENLIST]
    ) >>
    rpt strip_tac >> res_tac >> fs[MEM_FLAT, MEM_MAP]
    >> metis_tac[]
  ) >>
  disch_tac >>
  gvs[state_rel_def]
QED

(* Need *)
Theorem general_simulate_arg_load_preserve_locals:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    (case r of
      | NONE => T
      | SOME (Break n) => T
      | SOME (Continue n) => T
      | _ => F) = T ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
Proof
  rpt strip_tac >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (tmp_vars, vals) |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      gs[CaseEq "option", CaseEq "result"]
    )
    >- (
      simp[locals_rel_def] >>
      irule SUBMAP_IMP_FUPDATE_LIST_SUBMAP >> fs[]
      >> irule SUBMAP_DIFF_LIST >> fs[]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  rev_drule_at (Pos $ el 3) evaluate_nested_decs_locals_nested_res_var >>
  disch_then $ qspecl_then [`p`, `s with locals := t |++ ZIP (tmp_vars, vals)`, `r`, `t'`, `MAP Var tmp_vars`, `vals`] mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> simp[] >>
      imp_res_tac opt_mmap_length_eq >> simp[LENGTH_GENLIST]
    )
    >- (
      simp[LENGTH_MAP] >>
      imp_res_tac opt_mmap_length_eq >> simp[LENGTH_GENLIST]
    )
    >- (
      rpt strip_tac >> gvs[MEM_MAP, MEM_FLAT, var_cexp_def]
    ) >>
    simp[state_component_equality]
  ) >>
  disch_tac >> fs[] >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (tmp_vars, vals)` mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    )
    >- (
      simp[locals_rel_def] >>
      irule SUBMAP_IMP_FUPDATE_LIST_SUBMAP >> fs[]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos $ el 3) evaluate_nested_decs_locals_nested_res_var >>
  disch_then $ qspecl_then [`nested_decs vs (MAP Var tmp_vars) p`, `s`, `r`, `t'''`, `es`, `vals`] mp_tac >> gs[] >> impl_tac
  >- (
    conj_tac
    >- (
      imp_res_tac opt_mmap_length_eq >> simp[LENGTH_GENLIST]
    ) >>
    rpt strip_tac >> res_tac
    >> fs[MEM_FLAT, MEM_MAP]
    >> metis_tac[]
  ) >>
  disch_tac >> fs[] >>
  Cases_on `r` >> TRY (Cases_on `x`) >> gs[] >> conj_tac
  >>~- ([`FOLDL res_var _ _ SUBMAP FOLDL res_var _ _`],
    gvs[locals_rel_def, locals_ext_rel_def] >>
    `distinct_lists tmp_vars vs` by (
      simp[distinct_lists_def, EVERY_MEM]
    ) >>
    drule_all $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] map_flookup_fupdate_zip_not_mem >>
    disch_then $ qspecl_then [`t`, `ARB`] assume_tac >> fs[] >>
    simp[SUBMAP_FLOOKUP_EQN] >>
    rpt strip_tac >>
    Cases_on `MEM x vs`
    >- (
      imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_is_mem_zip_eq >>
      pop_assum $ qspecl_then [`s.locals`, `s'.locals`] assume_tac >> gs[] >>
      qpat_x_assum `FDIFF (_.locals |++ _) _ = FDIFF _.locals _` $ assume_tac o SRULE [GSYM SUBMAP_ANTISYM] >> fs[] >>
      qpat_x_assum `FDIFF (_.locals |++ _) _ SUBMAP FDIFF _.locals _` $ assume_tac o SRULE [SUBMAP_FLOOKUP_EQN] >>
      pop_assum mp_tac >>
      disch_then $ qspecl_then [`x`, `y`] mp_tac >> impl_tac
      >- (
        simp[FLOOKUP_FDIFF, GSYM flookup_thm] >>
        conj_tac
        >- (
          qpat_x_assum `!_. MEM _ _ ∨ MEM _ _ ⇒ _ ∉ FDOM _` $ qspec_then `x` assume_tac >> rfs[GSYM flookup_thm] >>
          pop_assum $ rewrite_tac o single o GSYM >>
          irule flookup_fupdate_zip_not_mem >> simp[]
          >> CCONTR_TAC >> metis_tac[]
        ) >>
        qpat_x_assum `FLOOKUP _.locals _ = SOME _` $ rewrite_tac o single o GSYM >>
        irule flookup_fupdate_zip_not_mem >> simp[]
        >> CCONTR_TAC >> metis_tac[]
      ) >>
      simp[FLOOKUP_FDIFF] >> disch_tac >> fs[] >>
      `~MEM x tmp_vars` by metis_tac[] >>
      imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_distinct_zip_eq >>
      pop_assum $ qspec_then `MAP (FLOOKUP s.locals) tmp_vars` mp_tac >> simp[LENGTH_MAP]
    ) >>
    imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_distinct_zip_eq >>
    pop_assum $ qspec_then `MAP (FLOOKUP s.locals) vs` mp_tac >> simp[LENGTH_MAP] >>
    disch_tac >>
    first_x_assum $ qspec_then `s'.locals` assume_tac >> fs[] >>
    imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_distinct_zip_eq >>
    pop_assum $ qspec_then `MAP (FLOOKUP t) vs` mp_tac >> simp[LENGTH_MAP] >>
    qpat_x_assum `FOLDL res_var _.locals _ SUBMAP _.locals` $ assume_tac o SRULE [SUBMAP_FLOOKUP_EQN] >>
    qpat_x_assum `_.locals SUBMAP _.locals` $ mp_tac o SRULE [SUBMAP_FLOOKUP_EQN] >>
    disch_then imp_res_tac >>
    disch_then $ qspec_then `t'.locals` assume_tac >>
    rfs[] >>
    qpat_x_assum `!_ _. FLOOKUP (FOLDL res_var _ _) _ = _ ⇒ FLOOKUP _ _ = _` imp_res_tac >>
    Cases_on `¬MEM x tmp_vars`
    >- (
      imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_distinct_zip_eq >>
      pop_assum kall_tac >>
      pop_assum $ qspec_then `MAP (FLOOKUP s.locals) tmp_vars` mp_tac >> simp[LENGTH_MAP]
    ) >>
    fs[] >>
    imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_is_mem_zip_eq >>
    pop_assum $ qspecl_then [`s.locals`, `t'''.locals`] assume_tac >> simp[] >>
    qpat_x_assum `FDIFF (_ |++ _ |++ _) _ = FDIFF _ _` $ assume_tac o SRULE [GSYM SUBMAP_ANTISYM] >>
    fs[] >>
    pop_assum kall_tac >>
    pop_assum $ assume_tac o SRULE [SUBMAP_FLOOKUP_EQN, flookup_thm] >>
    pop_assum $ qspec_then `x` mp_tac >> impl_tac
    >- (
      simp[FDOM_FUPDATE_LIST] >>
      conj_tac
      >- (
        disj1_tac >>
        drule MAP_ZIP >>
        disch_then $ qspecl_then [`ARB`, `ARB`] assume_tac >> fs[]
      ) >>
      rev_drule MAP_ZIP >>
      disch_then $ qspecl_then [`ARB`, `ARB`] assume_tac >> fs[]
    ) >>
    simp[GSYM flookup_thm]
  )
  >> fs[state_rel_def]
QED

Theorem general_simulate_arg_load_strong:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    (case r of
       | NONE => T
       | SOME (Break n) => T
       | SOME (Continue n) => T
       | _ => F) = T ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     (FDIFF s.locals (FDOM t)) SUBMAP t'.locals
Proof
  rpt strip_tac >>
  `r ≠ SOME Error` by gs[CaseEq "option", CaseEq "result"] >>
  drule_all general_simulate_arg_load_correct >>
  disch_tac >>
  drule evaluate_state_locals_rel_strong >> gs[] >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (tmp_vars, vals) |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      simp[locals_rel_def] >>
      irule SUBMAP_IMP_FUPDATE_LIST_SUBMAP >> fs[] >>
      irule SUBMAP_DIFF_LIST >> fs[]
    ) >>
    gvs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  fs[] >>
  rev_drule_at (Pos $ el 3) nested_decs_evaluate_sublocals_strong >>
  disch_then $ qspecl_then [`MAP Var tmp_vars`, `p`, `s with locals := t |++ ZIP (tmp_vars, vals)`, `r`, `s'`, `vals`, `t`] mp_tac >> simp[] >> impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> simp[]
    )
    >> rpt strip_tac
    >> gvs[MEM_MAP, var_cexp_def]
    >> irule SUBMAP_DIFF_LIST >> fs[]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos $ el 6) nested_decs_evaluate_sublocals_strong >>
  disch_then $ qspec_then `es` mp_tac >> simp[] >> impl_tac
  >- (
    conj_tac
    >- (
      imp_res_tac opt_mmap_length_eq >> simp[LENGTH_GENLIST]
    ) >>
    rpt strip_tac >> res_tac >> fs[MEM_FLAT, MEM_MAP]
    >> metis_tac[]
  ) >>
  disch_tac >> fs[]
QED

Theorem general_simulate_arg_load_strong_1:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    (case r of
       | NONE => T
       | SOME (Break n) => T
       | SOME (Continue n) => T
       | _ => F) = T ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒  ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒  ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧
     FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
Proof
  rpt strip_tac >>
  drule_all general_simulate_arg_load_preserve_locals >>
  disch_tac >>
  drule_all general_simulate_arg_load_strong >>
  disch_tac >>
  gs[]
QED

Theorem general_simulate_arg_load_strong_all:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Break n) => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Continue n) => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Error => F
       | _ => T)
Proof
  rpt strip_tac >>
  drule_all general_simulate_arg_load_correct >>
  disch_tac >>
  drule general_simulate_arg_load_strong_1 >>
  rpt $ disch_then drule >>
  Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
QED

Theorem general_simulate_arg_load_strong_all_drule:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars r1 t'.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ∧
    evaluate
      (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r1, t') ⇒
     r1 = r ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Break n) => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Continue n) => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Error => F
       | _ => T)
Proof
  rpt gen_tac >> rpt disch_tac >> fs[]
  >> drule_all general_simulate_arg_load_strong_all
  >> disch_tac >> gvs[]
QED


Theorem arg_load_correct:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (arg_load tmp_vars es vs p, s) = (r, t') ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Break n) => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Continue n) => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Error => F
       | _ => T)
Proof
  rpt strip_tac >>
  simp[arg_load_def] >>
  drule_all general_simulate_arg_load_strong_all >>
  disch_tac >> fs[] >>
  qrefine `t'` >>
  Cases_on `r` >> TRY (Cases_on `x`) >> gs[]
QED

Theorem arg_load_stronger:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT tmp_vars ∧ LENGTH tmp_vars = LENGTH vs ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x vs) ∧
    (!x. MEM x tmp_vars ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ⇒
    ∃t'.
      evaluate
        (arg_load tmp_vars es vs p, s) = (r, t') ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t)) ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Break n) => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t)) ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME (Continue n) => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t)) ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Error => F
       | _ => T)
Proof
  rpt strip_tac >>
  drule_all arg_load_correct >>
  disch_tac >> fs[] >>
  Cases_on `r` >> TRY (Cases_on `x`) >> fs[] >>
  drule evaluate_locals_same_fdom' >> fs[] >>
  disch_tac >> fs[EQ_FDOM_SUBMAP] >>
  fs[FDIFF_def, FDOM_DRESTRICT, SUBMAP_FLOOKUP_EQN, FLOOKUP_SIMP]
QED

Definition state_rel_code_def:
  state_rel_code s t ⇔
    s.globals = t.globals ∧
    s.memory = t.memory ∧
    s.memaddrs = t.memaddrs ∧
    s.sh_memaddrs = t.sh_memaddrs ∧
    s.clock = t.clock ∧
    s.be = t.be ∧
    s.ffi = t.ffi ∧
    s.base_addr = t.base_addr ∧
    s.top_addr = t.top_addr
End


Theorem fdom_subset_flookup_thm:
  ∀f g.
    FDOM f ⊆ FDOM g ⇔ (∀x p. FLOOKUP f x = SOME p ⇒ ∃q. FLOOKUP g x = SOME q)
Proof
  rpt strip_tac >> eq_tac >> simp[SUBSET_DEF]
  >- (
    rpt strip_tac >> fs[flookup_thm]
  ) >>
  rpt strip_tac >> fs[FDOM_FLOOKUP]
QED

Theorem eval_state_locals_same_code_fdom_same:
  ∀s e val s1.
    eval s e = SOME val ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    FDOM s.code ⊆ FDOM s1.code ⇒
    eval s1 e = SOME val
Proof
  recInduct eval_ind >> rpt strip_tac >>
  imp_res_tac fdom_eq_flookup_thm >>
  gvs[eval_def, CaseEq "option", CaseEq "word_lab", fdom_subset_flookup_thm]
  >>~- ([`OPT_MMAP _ _ = _`],
    qrefine `ws` >> fs[] >>
    drule opt_mmap_mem_func >>
    qpat_x_assum `OPT_MMAP _ _ = SOME _` $ rw o single o GSYM >>
    irule OPT_MMAP_CONG >>
    rpt strip_tac >> simp[] >>
    last_x_assum drule >>
    qpat_x_assum `!_. _` imp_res_tac >>
    disch_then imp_res_tac >> simp[])
  >- (
    fs[locals_strong_rel_def]
  )
  >~ [`_.base_addr = _`]
  >- fs[state_rel_code_def]
  >~ [`_.top_addr = _`]
  >- fs[state_rel_code_def]
  >~ [`_.globals`]
  >- (
    gvs[state_rel_code_def]
  ) >>
  last_x_assum imp_res_tac >> fs[mem_load_def]
  >>~- ([`_.memory`],
    gvs[state_rel_code_def]) >>
  last_x_assum imp_res_tac >> simp[]
QED

Definition code_inl_rel_def:
  code_inl_rel inl_fs s t ⇔
    ∀fname args prog.
      FLOOKUP s.code fname = SOME (args, prog) ⇒
      ∃inl_bag.
        inl_bag SUBMAP inl_fs ∧
        FLOOKUP t.code fname = SOME (args, inline_prog inl_bag prog)
End

Theorem eval_code_inl:
  ∀s e val s1 inl_fs.
    eval s e = SOME val ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    code_inl_rel inl_fs s s1 ⇒
    eval s1 e = SOME val
Proof
  rpt strip_tac >>
  irule eval_state_locals_same_code_fdom_same >> fs[] >>
  qrefine `s` >> fs[code_inl_rel_def, fdom_subset_flookup_thm] >>
  rpt strip_tac >>
  Cases_on `p` >>
  first_x_assum drule >>
  disch_tac >> fs[]
QED

Theorem opt_mmap_eval_code_inl:
  ∀s es vals s1 inl_fs.
    OPT_MMAP (eval s) es = SOME vals ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    code_inl_rel inl_fs s s1 ⇒
    OPT_MMAP (eval s1) es = SOME vals
Proof
  rpt strip_tac >>
  drule opt_mmap_mem_func >>
  qpat_x_assum `OPT_MMAP _ _ = SOME _` $ rw o single o GSYM >>
  irule OPT_MMAP_CONG >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!_. _` imp_res_tac >>
  imp_res_tac eval_code_inl >> simp[]
QED

Theorem evaluate_is_total:
  ∀p s.
    (∃r s'. evaluate (p, s) = (r, s'))
Proof
  recInduct evaluate_ind >> rpt strip_tac >> rw[Once evaluate_def, eval_def] >>
  every_case_tac >> gvs[]
  >~ [`While _ _`]
  >- (
    Cases_on `r` >> TRY (Cases_on `x`) >> gvs[]
    >> Cases_on `n` >> fs[]
  ) >>
  Cases_on `op` >> gvs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def] >>
  every_case_tac >> gvs[]
QED

Theorem MORE_THEN_NOT_MAX_LIST:
  ∀l x. MAX_LIST l < x ⇒ ¬MEM x l
Proof
  rpt strip_tac >>
  imp_res_tac MAX_LIST_PROPERTY >> fs[]
QED

Theorem unreach_elim_not_none_evaluate:
  ∀p s r s' p1 e.
    unreach_elim p = (p1, SOME e) ∧
    evaluate (p, s) = (r, s') ⇒
    ∃e. r = SOME e
Proof
  recInduct evaluate_ind >> rpt strip_tac >> fs[unreach_elim_def]
  >~ [`evaluate (While _ _, _)`]
  >- (
    pop_assum mp_tac >>
    simp[Once evaluate_def] >>
    disch_tac >> gvs[CaseEq "option", CaseEq "word_lab"] >>
    rpt (pairarg_tac >> gs[])
  )
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    pairarg_tac >> gvs[evaluate_def, CaseEq "option"] >>
    pairarg_tac >> fs[]
 )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rpt (pairarg_tac >> gvs[CaseEq "option", CaseEq "early_exit", CaseEq "word_lab", CaseEq "bool", evaluate_def]) >>
    Cases_on `w ≠ 0w` >> gvs[]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    rpt (pairarg_tac >> gvs[evaluate_def]) >>
    Cases_on `res = NONE` >> gvs[] >>
    Cases_on `r1 = NONE` >> gvs[] >>
    Cases_on `r` >> fs[]
  )
  >~ [`evaluate (Call _ _ _, _)`]
  >- (
    gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod", lookup_code_def, CaseEq "bool", CaseEq "result"] >>
    rpt (pairarg_tac >> gvs[CaseEq "early_exit", CaseEq "option"])
  ) >>
  gvs[evaluate_def, CaseEq "option"]
QED

Theorem unreach_elim_correct:
  ∀p s r s' p1 s1.
    evaluate (p, s) = (r, s') ∧
    r ≠ SOME Error ∧
    unreach_elim p = (p1, s1) ==>
    evaluate (p1, s) = (r, s')
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >~ [`evaluate (While _ _, _)`]
  >- (
    fs[unreach_elim_def] >>
    pairarg_tac >> gvs[] >>
    qpat_x_assum `evaluate _ = _` mp_tac >>
    PURE_ONCE_REWRITE_TAC[evaluate_def] >>
    disch_tac >>
    gvs[CaseEq "option", CaseEq "word_lab", CaseEq "early_exit", CaseEq "num"] >>
    Cases_on `w = 0w` >> fs[] >>
    Cases_on `s.clock = 0` >> fs[] >>
    rpt (pairarg_tac >> fs[]) >>
    Cases_on `res'` >> TRY (Cases_on `x`) >> gvs[] >>
    Cases_on `n` >> fs[]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    fs[unreach_elim_def, evaluate_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    Cases_on `res = NONE` >> gvs[] >>
    Cases_on `r1` >> gvs[evaluate_def] >>
    imp_res_tac unreach_elim_not_none_evaluate >> gs[]
  )
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    fs[unreach_elim_def, evaluate_def] >>
    rpt (pairarg_tac >> gvs[CaseEq "option", CaseEq "word_lab", evaluate_def])
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    fs[unreach_elim_def, evaluate_def] >>
    rpt (pairarg_tac >> gvs[CaseEq "option", CaseEq "word_lab"]) >>
    Cases_on `w = 0w` >> gvs[evaluate_def]
  )
  >~ [`evaluate (Call _ _ _, _)`]
  >- (
    pop_assum mp_tac >>
    simp[unreach_elim_def] >>
    qpat_x_assum `evaluate _ = _` mp_tac >>
    simp[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod", CaseEq "bool", lookup_code_def] >>
    ntac 2 (disch_tac >> fs[]) >>
    fs[lookup_code_def] >> gvs[evaluate_def, lookup_code_def, CaseEq "option", CaseEq "prod", CaseEq "result"] >>
    rpt (pairarg_tac >> gvs[evaluate_def, lookup_code_def]) >>
    Cases_on `eid = w` >> fs[]
  ) >>
  gvs[unreach_elim_def]
QED

Theorem unreach_elim_converge:
  ∀p q r.
    unreach_elim p = (q, r) ⇒
    unreach_elim q = (q, r)
Proof
  recInduct unreach_elim_ind >> gvs[unreach_elim_def] >> rw[]
  >- ( (* Seq *)
    rpt (pairarg_tac >> gvs[]) >>
    Cases_on `r1 = NONE` >> gvs[unreach_elim_def]
  )
  >- (
    pairarg_tac >> gvs[unreach_elim_def]
  )
  >- (
    rpt (pairarg_tac >> gvs[unreach_elim_def])
  )
  >- (
    pairarg_tac >> gvs[unreach_elim_def]
  ) >>
  gvs[CaseEq "option", CaseEq "prod"] >>
  rpt (gvs[unreach_elim_def] >>pairarg_tac >> gvs[unreach_elim_def])
QED

Theorem unreach_elim_fix_point:
  ∀q r.
    (∃p. unreach_elim p = (q, r)) ⇔
    unreach_elim q = (q, r)
Proof
  rpt gen_tac >> eq_tac >>
  rpt strip_tac >> fs[]
  >- imp_res_tac unreach_elim_converge >>
  qrefine `q` >> fs[]
QED

Theorem unreach_elim_nested_decs:
  ∀vs es p r.
    LENGTH vs = LENGTH es ∧
    unreach_elim p = (p, r) ⇒
    unreach_elim (nested_decs vs es p) = (nested_decs vs es p, r)
Proof
  Induct_on `vs` >> Cases_on `es` >> rw[nested_decs_def, unreach_elim_def] >>
  pairarg_tac >> gvs[unreach_elim_def] >>
  last_x_assum $ qspec_then `t` assume_tac >> fs[] >>
  pop_assum imp_res_tac >> gvs[]
QED

Theorem unreach_elim_arg_load:
  ∀p tmp_vars args args_vname r.
    LENGTH tmp_vars = LENGTH args ∧
    LENGTH args = LENGTH args_vname ∧
    unreach_elim p = (p, r) ⇒
    unreach_elim (arg_load tmp_vars args args_vname p) = (arg_load tmp_vars args args_vname p, r)
Proof
  rpt strip_tac >> fs[arg_load_def] >>
  rpt (irule unreach_elim_nested_decs >> fs[])
QED

Theorem unreach_elim_arg_load_perm:
  ∀p tmp_vars args args_vname r.
    LENGTH tmp_vars = LENGTH args_vname ∧
    LENGTH args = LENGTH args_vname ∧
    unreach_elim p = (p, r) ⇒
    unreach_elim (arg_load tmp_vars args args_vname p) = (arg_load tmp_vars args args_vname p, r)
Proof
  metis_tac[unreach_elim_arg_load]
QED

Theorem unreach_elim_prog_size:
  ∀p q r f.
    unreach_elim p = (q, r) ⇒
    prog_size f q ≤ prog_size f p
Proof
  recInduct unreach_elim_ind >> rpt strip_tac >> gvs[unreach_elim_def, prog_size_def] >>
  rpt (pairarg_tac >> gvs[])
  >- (
    Cases_on `r1 = NONE` >> gvs[]
    >- (
      rpt (last_x_assum $ qspec_then `f` assume_tac) >>
      fs[]
    ) >>
    last_x_assum $ qspec_then `f` assume_tac >> fs[]
  )
  >- (
    rpt (last_x_assum $ qspec_then `f` assume_tac) >> fs[]
  ) >>
  Cases_on `ctyp` >> gvs[prog_size_def] >>
  PairCases_on `x` >> fs[] >>
  Cases_on `x1` >> gvs[]
  >- (
    gvs[prog_size_def]
  ) >>
  PairCases_on `x` >> fs[] >>
  rpt (pairarg_tac >> gvs[prog_size_def])
QED

Theorem not_has_return_imp_not_branch_ret:
  ∀p. ¬has_return p ⇒ not_branch_ret p
Proof
  recInduct has_return_ind >> rw[has_return_def, not_branch_ret_def] >>
  every_case_tac >> gvs[]
QED

Theorem not_has_return_imp_unreach_elim:
  ∀p r. ¬has_return p ∧ unreach_elim p = (p, r) ⇒ r ≠ SOME Ret
Proof
  recInduct has_return_ind >> rw[has_return_def, unreach_elim_def] >>
  rpt (pairarg_tac >> gvs[])
  >- (
    every_case_tac >> gvs[] >>
    imp_res_tac unreach_elim_prog_size >> gvs[prog_size_def]
  )
  >- (
    every_case_tac >> gvs[]
  ) >>
  every_case_tac >> rpt (pairarg_tac >> gvs[]) >>
  every_case_tac >> gvs[]
QED

Theorem not_branch_ret_evaluate_return_unreach_elim:
  ∀p s r s'.
    unreach_elim p = (p, NONE) ∧
    not_branch_ret p ∧
    evaluate (p, s) = (r, s') ⇒
      ∀rv. r ≠ SOME (Return rv)
Proof
  recInduct evaluate_ind >> rw[unreach_elim_def, not_branch_ret_def] >>
  gvs[Once evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
  rpt (pairarg_tac >> gvs[]) >>
  every_case_tac >> gvs[] >>
  imp_res_tac not_has_return_not_evaluate_return' >> gvs[]
  >- (
    Cases_on `op` >> fs[sh_mem_op_def, sh_mem_store_def, sh_mem_load_def] >>
    every_case_tac >> gvs[]
  ) >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `evaluate _ = _` $ assume_tac o SRULE[Once evaluate_def] >>
  gvs[has_return_def]
QED

Theorem opt_mmap_some_imp_fupdate_exist_some:
  ∀vs fm vals nv.
    OPT_MMAP (FLOOKUP fm) vs = SOME vals ⇒
      ∃z. OPT_MMAP (FLOOKUP (fm |+ nv)) vs = SOME z
Proof
  Induct >> rw[]
  >> last_x_assum imp_res_tac
  >> pop_assum $ qspec_then `nv` assume_tac >> fs[]
  >> Cases_on `nv` >> fs[FLOOKUP_UPDATE]
  >> TOP_CASE_TAC >> fs[]
QED

Theorem opt_mmap_some_imp_fupdate_list_exist_some:
  ∀xs ys vs fm vals.
    OPT_MMAP (FLOOKUP fm) vs = SOME vals ∧ LENGTH xs = LENGTH ys ⇒
      ∃z. OPT_MMAP (FLOOKUP (fm |++ ZIP(xs, ys))) vs = SOME z
Proof
  Induct >> rw[]
  >- fs[FUPDATE_LIST]
  >> Cases_on `ys` >> fs[FUPDATE_LIST_THM]
  >> last_x_assum irule >> fs[opt_mmap_some_imp_fupdate_exist_some]
QED

Theorem opt_mmap_flookup_not_mem_domsub:
  ∀vs fm vals x.
   OPT_MMAP (FLOOKUP fm) vs = SOME vals ∧ ¬MEM x vs ⇒
    OPT_MMAP (FLOOKUP (fm \\ x)) vs = SOME vals
Proof
  Induct >> rw[DOMSUB_FLOOKUP_THM]
QED

Theorem fdoms_eq_opt_mmap_flookup_some:
  ∀vs fm fm' vals.
    FDOM fm = FDOM fm' ∧ OPT_MMAP (FLOOKUP fm) vs = SOME vals ⇒
    ∃z. OPT_MMAP (FLOOKUP fm') vs = SOME z
Proof
  Induct >> rw[]
  >> imp_res_tac panPropsTheory.fdoms_eq_flookup_some_none >> gvs[]
  >> metis_tac[]
QED

Theorem opt_mmap_update_locals_not_vars_eval_eq:
  ∀es n vs w s.
    ¬MEM n (FLAT (MAP var_cexp es)) ∧ OPT_MMAP (eval s) es = SOME vs ⇒
    OPT_MMAP (eval (s with locals := s.locals |+ (n,w))) es = SOME vs
Proof
  Induct >> rw[update_locals_not_vars_eval_eq]
QED

Theorem evaluate_nested_seq_assign:
  ∀ns s es ws vals.
    OPT_MMAP (eval s) es = SOME ws ∧
    (!x. MEM x ns ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ∧
    OPT_MMAP (FLOOKUP s.locals) ns = SOME vals ∧
    LENGTH ns = LENGTH ws ∧
    ALL_DISTINCT ns ⇒
    ∃s'.
      evaluate (nested_seq (MAP2 Assign ns es), s) = (NONE, s') ∧
      state_rel s s' ∧
      (∀x. ¬MEM x ns ⇒ FLOOKUP s'.locals x = FLOOKUP s.locals x) ∧
      OPT_MMAP (FLOOKUP s'.locals) ns = SOME ws
Proof
  Induct >> rw[nested_seq_def, evaluate_def]
  >- fs[state_rel_def]
  >> Cases_on `es` >> gvs[nested_seq_def, evaluate_def, DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM]
  >> last_x_assum $ qspec_then `s with locals := s.locals |+ (h,h''')` mp_tac
  >> disch_then $ drule_at Any
  >> disch_then $ qspecl_then [`t''`, `t`] mp_tac >> fs[] >> impl_tac
  >- fs[opt_mmap_update_locals_not_vars_eval_eq, opt_mmap_flookup_update]
  >> disch_tac >> fs[state_rel_def]
  >> rpt strip_tac >> fs[FLOOKUP_UPDATE]
QED

Theorem evaluate_nested_seq_assign_drule:
  ∀ns s es ws vals r s'.
    OPT_MMAP (eval s) es = SOME ws ∧
    (!x. MEM x ns ⇒ ¬MEM x (FLAT (MAP var_cexp es))) ∧
    OPT_MMAP (FLOOKUP s.locals) ns = SOME vals ∧
    LENGTH ns = LENGTH ws ∧
    ALL_DISTINCT ns ∧
    evaluate (nested_seq (MAP2 Assign ns es), s) = (r, s') ⇒
      r = NONE ∧
      state_rel s s' ∧
      (∀x. ¬MEM x ns ⇒ FLOOKUP s'.locals x = FLOOKUP s.locals x) ∧
      OPT_MMAP (FLOOKUP s'.locals) ns = SOME ws
Proof
  rpt gen_tac >> rpt disch_tac >> fs[]
  >> drule_all evaluate_nested_seq_assign
  >> disch_tac >> gvs[]
QED

Theorem transform_eoc_correct:
  ∀p s r s' res rts.
   evaluate (p, s) = (r, s') ∧
   unreach_elim p = (p, res) ∧
   not_branch_ret p ∧
   (!retvs. r = SOME (Return retvs) ⇒ LENGTH rts = LENGTH retvs) ∧
   (!x. MEM x rts ⇒ ¬MEM x (var_prog p)) ∧
   (∃z. OPT_MMAP (FLOOKUP s.locals) rts = SOME z) ∧
   ALL_DISTINCT rts ∧
   r ≠ SOME Error ⇒
   ∃r1 s1'.
    evaluate (transform_eoc rts p, s) = (r1, s1') ∧
    state_rel s' s1' ∧
    case r of
      | NONE => r1 = NONE ∧ locals_strong_rel s' s1'
      | SOME (Break n) => r1 = SOME (Break n) ∧ locals_strong_rel s' s1'
      | SOME (Continue n) => r1 = SOME (Continue n) ∧ locals_strong_rel s' s1'
      | SOME (Return retvs) => r1 = NONE ∧ OPT_MMAP (FLOOKUP s1'.locals) rts = SOME retvs
      | SOME Error => F
      | res => r1 = res
Proof
  recInduct evaluate_ind >> rpt conj_tac
  >~ [`evaluate (While _ _, _)`]
  >- suspend "While"
  >~ [`evaluate (Call _ _ _, _)`]
  >- suspend "Call"
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    rw[transform_eoc_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> rpt (pairarg_tac >> gvs[])
    >> last_x_assum drule
    >> imp_res_tac opt_mmap_some_imp_fupdate_exist_some
    >> pop_assum $ qspec_then `(v,value)` assume_tac >> fs[]
    >> disch_tac >> fs[]
    >> Cases_on `FLOOKUP s.locals v` >> fs[res_var_def]
    >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[state_rel_def, locals_strong_rel_def]
    >- (
      metis_tac[opt_mmap_flookup_not_mem_domsub]
    )
    >> Cases_on `x'` >> fs[]
    >> metis_tac[opt_mmap_flookup_update]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rw[transform_eoc_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> rpt (pairarg_tac >> gvs[])
    >> imp_res_tac not_has_return_imp_not_branch_ret
    >> Cases_on `w = 0w` >> fs[]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    rw[transform_eoc_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> rpt (pairarg_tac >> gvs[])
    >> Cases_on `r1 <> NONE` >> gvs[]
    >- (imp_res_tac unreach_elim_prog_size >> fs[prog_size_def])
    >> Cases_on `res'' = NONE` >> fs[]
    >- (
      first_x_assum drule >> fs[]
      >> disch_tac >> fs[]
      >> last_x_assum drule >> fs[]
      >> drule evaluate_locals_same_fdom' >> fs[]
      >> disch_tac >> imp_res_tac fdoms_eq_opt_mmap_flookup_some >> gvs[]
      >> disch_tac >> fs[]
      >> `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >> gvs[]
    )
    >> gvs[]
    >> first_x_assum drule >> fs[]
    >> disch_tac >> fs[]
    >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    >> imp_res_tac not_branch_ret_evaluate_return_unreach_elim >> fs[]
  )
  >~ [`evaluate (Return _, _)`]
  >- (
    rw[transform_eoc_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> imp_res_tac evaluate_nested_seq_assign >> gvs[state_rel_def, empty_locals_def]
  )
  >> rw[transform_eoc_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
  >> gvs[AllCaseEqs(), state_rel_def, locals_strong_rel_def]
  (* ShMem *)
  >> Cases_on `op` >> gvs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def, AllCaseEqs()]
QED

Resume transform_eoc_correct[While]:
  rw[transform_eoc_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
  >> pairarg_tac >> gvs[]
  >> qpat_x_assum `_ = (r, s')` mp_tac
  >> PURE_ONCE_REWRITE_TAC [evaluate_def]
  >> imp_res_tac not_has_return_imp_not_branch_ret
  >> disch_tac >> gvs[CaseEq "option", CaseEq "word_lab", CaseEq "bool"]
  >- fs[state_rel_def]
  >- (
    rpt (pairarg_tac >> gvs[])
    >> first_x_assum $ qspec_then `rts` mp_tac >> fs[] >> impl_tac
    >- (
      conj_tac
      >- (Cases_on `res'` >> TRY (Cases_on `x`) >> fs[])
      >> fs[dec_clock_def]
      >> Cases_on `res' = SOME Error` >> fs[]
    )
    >> disch_tac >> fs[]
    >> Cases_on `res'` >> TRY (Cases_on `x`) >> gvs[]
    >- (
      (* NONE *)
      last_x_assum drule >> fs[]
      >> drule evaluate_locals_same_fdom' >> simp[dec_clock_def]
      >> disch_tac
      >> imp_res_tac fdoms_eq_opt_mmap_flookup_some >> gvs[]
      >> `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >> fs[]
    )
    >- (
      (* Break *)
      Cases_on `n` >> gvs[]
    )
    >- (
      (* Continue *)
      Cases_on `n` >> gvs[]
      >> last_x_assum drule >> fs[]
      >> drule evaluate_locals_same_fdom' >> simp[dec_clock_def]
      >> disch_tac >> imp_res_tac fdoms_eq_opt_mmap_flookup_some >> gvs[]
      >> `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >> fs[]
    )
    (* Return *)
    >> imp_res_tac not_has_return_not_evaluate_return' >> fs[state_rel_def, locals_strong_rel_def]
  )
  >> fs[state_rel_def, locals_strong_rel_def]
QED

Resume transform_eoc_correct[Call]:
  rw[transform_eoc_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
  >> gvs[AllCaseEqs(), evaluate_def]
  >>~- ([`state_rel x x ∧ locals_strong_rel x x`],
    fs[state_rel_def, locals_strong_rel_def])
  >>~- ([`state_rel x x`],
    fs[state_rel_def])
  >- (
    conj_tac
    >- fs[state_rel_def, empty_locals_def]
    >> fs[opt_mmap_some_eq_zip_flookup]
  )
  >> pairarg_tac >> gvs[]
  >> imp_res_tac not_has_return_imp_not_branch_ret >> fs[]
QED

Finalise transform_eoc_correct;

Theorem transform_branch_correct:
  ∀p s r s' res ld rts.
   evaluate (p, s) = (r, s') ∧
   (!retvs. r = SOME (Return retvs) ⇒ LENGTH rts = LENGTH retvs) ∧
   (!x. MEM x rts ⇒ ¬MEM x (var_prog p)) ∧
   (∃z. OPT_MMAP (FLOOKUP s.locals) rts = SOME z) ∧
   ALL_DISTINCT rts ∧
   r ≠ SOME Error ⇒
   ∃r1 s1'.
    evaluate (transform_branch ld rts p, s) = (r1, s1') ∧
    state_rel s' s1' ∧
    case r of
      | NONE => r1 = NONE ∧ locals_strong_rel s' s1'
      | SOME (Break n) => r1 = SOME (Break n) ∧ locals_strong_rel s' s1'
      | SOME (Continue n) => r1 = SOME (Continue n) ∧ locals_strong_rel s' s1'
      | SOME (Return retvs) => r1 = SOME (Break ld) ∧ OPT_MMAP (FLOOKUP s1'.locals) rts = SOME retvs
      | SOME Error => F
      | res => r1 = res
Proof
  recInduct evaluate_ind >> rpt conj_tac
  >~ [`evaluate (While _ _, _)`]
  >- suspend "While"
  >~ [`evaluate (Call _ _ _, _)`]
  >- suspend "Call"
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    rw[transform_branch_def, evaluate_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> rpt (pairarg_tac >> gvs[])
    >> last_x_assum drule
    >> imp_res_tac opt_mmap_some_imp_fupdate_exist_some
    >> pop_assum $ qspec_then `(v,value)` assume_tac >> fs[]
    >> disch_tac >> fs[]
    >> pop_assum $ qspec_then `ld` assume_tac >> fs[]
    >> Cases_on `FLOOKUP s.locals v` >> fs[res_var_def]
    >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[state_rel_def, locals_strong_rel_def]
    >- (
      metis_tac[opt_mmap_flookup_not_mem_domsub]
    )
    >> Cases_on `x'` >> fs[]
    >> metis_tac[opt_mmap_flookup_update]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rw[transform_branch_def, evaluate_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> imp_res_tac not_has_return_imp_not_branch_ret
    >> Cases_on `w = 0w` >> fs[]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    rw[transform_branch_def, evaluate_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> rpt (pairarg_tac >> gvs[])
    >> Cases_on `res' = NONE` >> fs[]
    >- (
      first_x_assum drule >> fs[]
      >> disch_then $ qspec_then `ld` assume_tac >> fs[]
      >> last_x_assum drule >> fs[]
      >> drule evaluate_locals_same_fdom' >> fs[]
      >> disch_tac >> imp_res_tac fdoms_eq_opt_mmap_flookup_some >> gvs[]
      >> disch_tac >> fs[]
      >> `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >> gvs[]
    )
    >> gvs[]
    >> first_x_assum drule >> fs[]
    >> disch_then $ qspec_then `ld` assume_tac >> gvs[]
    >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    >> imp_res_tac not_branch_ret_evaluate_return_unreach_elim >> fs[]
  )
  >~ [`evaluate (Return _, _)`]
  >- (
    rw[transform_branch_def, evaluate_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
    >> gvs[CaseEq "option", CaseEq "word_lab"]
    >> imp_res_tac evaluate_nested_seq_assign >> gvs[state_rel_def, empty_locals_def]
  )
  >> rw[transform_branch_def, evaluate_def, unreach_elim_def, not_branch_ret_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
  >> gvs[AllCaseEqs(), state_rel_def, locals_strong_rel_def]
  (* ShMem *)
  >> Cases_on `op` >> gvs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def, AllCaseEqs()]
QED

Resume transform_branch_correct[While]:
  rw[transform_branch_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
  >> qpat_x_assum `_ = (r, s')` mp_tac
  >> PURE_ONCE_REWRITE_TAC [evaluate_def]
  >> disch_tac >> gvs[CaseEq "option", CaseEq "word_lab", CaseEq "bool"]
  >- fs[state_rel_def]
  >- (
    rpt (pairarg_tac >> gvs[])
    >> first_x_assum $ qspecl_then [`ld+1`, `rts`] mp_tac >> fs[] >> impl_tac
    >- (
      conj_tac
      >- (Cases_on `res'` >> TRY (Cases_on `x`) >> fs[])
      >> fs[dec_clock_def]
      >> Cases_on `res' = SOME Error` >> fs[]
    )
    >> disch_tac >> fs[]
    >> Cases_on `res'` >> TRY (Cases_on `x`) >> gvs[]
    >- (
      (* NONE *)
      last_x_assum drule >> fs[]
      >> drule evaluate_locals_same_fdom' >> simp[dec_clock_def]
      >> disch_tac
      >> imp_res_tac fdoms_eq_opt_mmap_flookup_some >> gvs[]
      >> `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >> fs[]
    )
    >- (
      (* Break *)
      Cases_on `n` >> gvs[]
    )
    >- (
      (* Continue *)
      Cases_on `n` >> gvs[]
      >> last_x_assum drule >> fs[]
      >> drule evaluate_locals_same_fdom' >> simp[dec_clock_def]
      >> disch_tac >> imp_res_tac fdoms_eq_opt_mmap_flookup_some >> gvs[]
      >> `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >> fs[]
    )
    (* Return *)
    >> Cases_on `ld + 1` >> fs[state_rel_def, locals_strong_rel_def]
  )
  >> fs[state_rel_def, locals_strong_rel_def]
QED


Definition cont_res_def:
  (cont_res NONE = T) ∧ (cont_res (SOME (Break n)) = T) ∧ (cont_res (SOME (Continue n)) = T) ∧
  (cont_res (SOME Error) = T) ∧ (cont_res _ = F)
End

Resume transform_branch_correct[Call]:
  rw[transform_branch_def, evaluate_def, var_prog_def, IMP_CONJ_THM, FORALL_AND_THM]
  >> gvs[AllCaseEqs()]
  >> every_case_tac >> gvs[evaluate_def]
  >>~- ([`state_rel x x ∧ locals_strong_rel x x`],
    fs[state_rel_def, locals_strong_rel_def])
  >>~- ([`state_rel x x`],
    fs[state_rel_def])
  >> conj_tac
  >- fs[state_rel_def, empty_locals_def]
  >> fs[opt_mmap_some_eq_zip_flookup]
QED

Finalise transform_branch_correct;

Theorem wrapped_transform_if:
  ∀p s r s' res rts loc.
   evaluate (p, dec_clock s with locals := loc) = (r, s') ∧
   unreach_elim p = (p, res) ∧
   (!retvs. r = SOME (Return retvs) ⇒ LENGTH rts = LENGTH retvs) ∧
   (!x. MEM x rts ⇒ ¬MEM x (var_prog p)) ∧
   (∃z. OPT_MMAP (FLOOKUP loc) rts = SOME z) ∧
   ALL_DISTINCT rts ∧
   ¬cont_res r ∧
   s.clock ≠ 0 ∧
   r ≠ SOME Error ⇒
   ∃r1 s1'.
    evaluate (if not_branch_ret p then
                Seq Tick (transform_eoc rts p) else
                While (Const 1w) (transform_branch 0 rts p), s with locals := loc) = (r1, s1') ∧
    state_rel s' s1' ∧
    case r of
      | SOME (Return retvs) => r1 = NONE ∧ OPT_MMAP (FLOOKUP s1'.locals) rts = SOME retvs
      | SOME (Exception eid) => r1 = SOME (Exception eid)
      | SOME TimeOut => r1 = SOME TimeOut
      | SOME (FinalFFI ffi) => r1 = SOME (FinalFFI ffi)
      | res => F
Proof
  rpt strip_tac
  >> Cases_on `not_branch_ret p` >> fs[]
  >- (
    drule transform_eoc_correct
    >> rpt (disch_then $ drule_at Any) >> fs[]
    >> disch_tac >> gvs[evaluate_def, dec_clock_def]
    >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[cont_res_def]
  )
  >> drule transform_branch_correct
  >> rpt (disch_then $ drule_at Any) >> fs[]
  >> disch_then $ qspec_then `0` assume_tac >> fs[]
  >> gvs[Once evaluate_def, eval_def, dec_clock_def]
  >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[cont_res_def]
QED

Theorem mem_var_prog_nested_seq:
  ∀ps x.
    MEM x (var_prog (nested_seq ps)) = MEM x (FLAT (MAP var_prog ps))
Proof
  Induct >> fs[nested_seq_def, var_prog_def]
QED

Theorem MEM_MAP2_IMP:
  ∀f l1 l2 x.
    MEM x (MAP2 f l1 l2) ⇒ ∃y1 y2. x = f y1 y2 ∧ MEM y1 l1 ∧ MEM y2 l2
Proof
  recInduct MAP2_IND >> rw[]
  >> metis_tac[]
QED

Theorem mem_var_prog_transform_eoc:
  ∀rts p x.
    MEM x (var_prog (transform_eoc rts p)) ⇒ (MEM x (var_prog p) ∨ MEM x rts)
Proof
  recInduct transform_eoc_ind
  >> rw[] >> gvs[transform_eoc_def, var_prog_def]
  >- (
    fs[mem_var_prog_nested_seq, MEM_MAP, MEM_FLAT]
    >> imp_res_tac MEM_MAP2_IMP  >> gvs[var_prog_def]
    >> metis_tac[]
  )
  >- (
    every_case_tac >> gvs[var_prog_def] >> metis_tac[]
  )
  >> metis_tac[]
QED

Theorem mem_var_prog_transform_branch:
  ∀ld rts p x.
    MEM x (var_prog (transform_branch ld rts p)) ⇒ (MEM x (var_prog p) ∨ MEM x rts)
Proof
  recInduct transform_branch_ind
  >> rw[] >> gvs[transform_branch_def, var_prog_def]
  >- (
    fs[mem_var_prog_nested_seq, MEM_MAP, MEM_FLAT]
    >> imp_res_tac MEM_MAP2_IMP  >> gvs[var_prog_def]
    >> metis_tac[]
  )
  >- (
    every_case_tac >> gvs[var_prog_def] >> metis_tac[]
  )
  >> metis_tac[]
QED

Theorem unreach_elim_preserve_has_return:
  ∀p q r.
    ¬has_return p ∧
    unreach_elim p = (q, r) ⇒
    ¬has_return q
Proof
  recInduct has_return_ind >> rw[has_return_def, unreach_elim_def] >>
  rpt (pairarg_tac >> gvs[has_return_def]) >>
  every_case_tac >> rpt (pairarg_tac >> gvs[has_return_def]) >>
  gvs[has_return_def]
QED

Theorem unreach_elim_preserve_not_branch_ret:
  ∀p q r.
    not_branch_ret p ∧
    unreach_elim p = (q, r) ⇒
    not_branch_ret q
Proof
  recInduct not_branch_ret_ind >> rw[not_branch_ret_def, unreach_elim_def] >>
  rpt (pairarg_tac >> gvs[not_branch_ret_def]) >>
  imp_res_tac unreach_elim_preserve_has_return >>
  every_case_tac >> rpt (pairarg_tac >> gvs[has_return_def, not_branch_ret_def]) >>
  gvs[not_branch_ret_def, has_return_def] >>
  imp_res_tac unreach_elim_preserve_has_return >> gvs[]
QED

Theorem inline_prog_correct:
  ∀p s r s' inl_fs s1 inl_bag.
    evaluate (p, s) = (r, s') ∧
    r ≠ SOME Error ∧
    inl_fs SUBMAP s.code ∧
    inl_bag SUBMAP inl_fs ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    code_inl_rel inl_fs s s1 ⇒
    ∃s1'.
      evaluate (inline_prog inl_bag p, s1) = (r, s1') ∧
      state_rel_code s' s1' ∧
      code_inl_rel inl_fs s' s1' ∧
      case r of
        | NONE => locals_strong_rel s' s1'
        | SOME (Break n) => locals_strong_rel s' s1'
        | SOME (Continue n) => locals_strong_rel s' s1'
        | SOME Error => F
        | _ => T
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >~ [`evaluate (Call _ _ _, _)`]
  >- suspend "Call"
  >~ [`evaluate (While _ _, _) = _`]
  >- (
    qpat_assum `evaluate _ = _` $ assume_tac o SRULE [Once evaluate_def, CaseEq "option", CaseEq "word_lab"] >> gvs[] >>
    imp_res_tac eval_code_inl >> fs[] >>
    pairarg_tac >> fs[] >>
    simp[inline_prog_def] >>
    simp[Once evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    pairarg_tac >> fs[] >>
    `s1.clock = s.clock` by fs[state_rel_code_def] >> fs[] >>
    gs[CaseEq "bool"]
    >- gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def] >>
    first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1`, `inl_bag`] mp_tac >> impl_tac
    >- gs[AllCaseEqs(), dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
    disch_tac >> fs[] >>
    Cases_on `res` >> gs[]
    >- (
      imp_res_tac evaluate_code_invariant >> fs[] >>
      first_x_assum $ qspecl_then [`inl_fs`, `s1''`, `inl_bag`] mp_tac >> impl_tac
      >- fs[dec_clock_def, state_rel_code_def, code_inl_rel_def, locals_strong_rel_def] >>
      disch_tac >> fs[inline_prog_def]
    ) >>
    Cases_on `x` >> gs[]
    >- (
      (* Break *)
      Cases_on `n` >> gvs[]
    )
    >- (
      (* Continue *)
      Cases_on `n` >> gvs[]
      >> imp_res_tac evaluate_code_invariant >> gvs[dec_clock_def]
      >> last_x_assum drule
      >> rpt $ disch_then drule
      >> disch_tac >> fs[inline_prog_def]
    ) >>
    gvs[]
  )
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    imp_res_tac eval_code_inl >>
    fs[inline_prog_def, evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    pop_assum imp_res_tac >> fs[] >>
    rpt (pairarg_tac >> gvs[]) >>
    qpat_assum `locals_strong_rel _ _` $ fs o single o SRULE [locals_strong_rel_def, fmap_eq_flookup] >>
    first_x_assum $ qspecl_then [`inl_fs`, `s1 with locals := s1.locals |+ (v, value)`, `inl_bag`] mp_tac >> impl_tac
    >- fs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
    disch_tac >> fs[] >>
    imp_res_tac evaluate_code_invariant >>
    Cases_on `FLOOKUP s1.locals v` >> gvs[AllCaseEqs(), res_var_def, state_rel_code_def, code_inl_rel_def, locals_strong_rel_def] >>
    every_case_tac >> gvs[]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    imp_res_tac eval_code_inl >>
    fs[inline_prog_def, evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    pop_assum imp_res_tac >> fs[] >>
    last_x_assum $ qspecl_then [`inl_fs`, `s1`, `inl_bag`] mp_tac >> fs[] >>
    disch_tac >> gvs[AllCaseEqs(), state_rel_code_def, code_inl_rel_def, locals_strong_rel_def] >>
    every_case_tac >> gvs[]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    fs[inline_prog_def, evaluate_def] >>
    rpt (pairarg_tac >> fs[]) >>
    Cases_on `res' = NONE` >> fs[]
    >- (
      first_x_assum $ qspecl_then [`inl_fs`, `s1`, `inl_bag`] assume_tac >> gs[] >>
      imp_res_tac evaluate_code_invariant >>
      first_x_assum $ qspecl_then [`inl_fs`, `s1'`, `inl_bag`] assume_tac >> gs[]
    ) >>
    first_x_assum $ qspecl_then [`inl_fs`, `s1`, `inl_bag`] assume_tac >> gvs[] >>
    `res ≠ NONE` by (every_case_tac >> gvs[]) >> fs[]
  )
  >~ [`evaluate (Return _, _)`]
  >- (
    gvs[inline_prog_def, evaluate_def, CaseEq "option", CaseEq "prod"]
    >> imp_res_tac opt_mmap_eval_code_inl >> fs[state_rel_code_def, empty_locals_def, code_inl_rel_def]
  ) >>
  imp_res_tac eval_code_inl >>
  gvs[AllCaseEqs(), inline_prog_def, evaluate_def, state_rel_code_def,
      code_inl_rel_def, locals_strong_rel_def, empty_locals_def,
      set_globals_def, dec_clock_def] >> first_x_assum imp_res_tac >> gvs[] >>
  (* ShMem *)
  Cases_on `op` >> gvs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def, AllCaseEqs(), set_var_def, empty_locals_def]
QED

Resume inline_prog_correct[Call]:
  gvs[inline_prog_def] >> TOP_CASE_TAC >> fs[]
  >- (
    (* Non-distinct return variables *)
    Cases_on `caltyp` >> fs[]
    >> Cases_on `x` >> fs[]
    >> Cases_on `r'` >> gvs[evaluate_def, CaseEq "option", CaseEq "prod"]
    >> imp_res_tac opt_mmap_eval_code_inl
    >> Cases_on `x` >> fs[]
  )
  >> Cases_on `FLOOKUP inl_bag fname` >> fs[]
  >- (
    (* Callee is not marked "inlined" *)
    Cases_on `caltyp` >> fs[]
    >- (
      (* tail call *)
      gvs[evaluate_def, lookup_code_def, CaseEq "option", CaseEq "prod"]
      >> imp_res_tac opt_mmap_eval_code_inl >> fs[]
      >> qpat_assum `code_inl_rel _ _ _` $ imp_res_tac o SRULE[code_inl_rel_def] >> fs[]
      >> Cases_on `s.clock = 0` >> fs[]
      >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
      >> Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> fs[]
      >> Cases_on `q = SOME Error` >> fs[dec_clock_def]
      >> last_x_assum drule
      >> disch_then drule
      >> disch_then $ qspec_then `s1 with <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock - 1|>` mp_tac >> impl_tac
      >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
      >> disch_tac >> fs[]
      >> every_case_tac >> gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
    )
    (* assign call *)
    >> Cases_on `x` >> fs[]
    >> Cases_on `r'` >> fs[]
    >> `s1.clock = s.clock` by fs[state_rel_code_def]
    >- (
      (* No handlers *)
      gvs[evaluate_def, lookup_code_def, CaseEq "option", CaseEq "prod"]
      >> imp_res_tac opt_mmap_eval_code_inl >> fs[]
      >> qpat_assum `code_inl_rel _ _ _` $ imp_res_tac o SRULE[code_inl_rel_def] >> fs[]
      >> Cases_on `s.clock = 0` >> fs[]
      >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
      >> Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> fs[]
      >> Cases_on `q' = SOME Error` >> fs[dec_clock_def]
      >> last_x_assum drule
      >> disch_then drule
      >> disch_then $ qspec_then `s1 with <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock - 1|>` mp_tac >> impl_tac
      >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
      >> disch_tac >> fs[]
      >> Cases_on `q'` >> TRY (Cases_on `x`) >> gvs[]
      >>~- ([`state_rel_code (empty_locals _) (empty_locals _)`],
        gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def])
      >> TOP_CASE_TAC >> fs[]
      >> `s1.locals = s.locals` by fs[locals_strong_rel_def] >> fs[]
      >> TOP_CASE_TAC >> gvs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def]
    )
    (* With handlers *)
    >> TOP_CASE_TAC >> fs[]
    >> gvs[evaluate_def, lookup_code_def, CaseEq "option", CaseEq "prod"]
    >> imp_res_tac opt_mmap_eval_code_inl >> fs[]
    >> qpat_assum `code_inl_rel _ _ _` $ imp_res_tac o SRULE[code_inl_rel_def] >> fs[]
    >> Cases_on `s.clock = 0` >> fs[]
    >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
    >> Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> fs[]
    >> Cases_on `q'' = SOME Error` >> fs[dec_clock_def]
    >> last_x_assum drule
    >> disch_then drule
    >> disch_then $ qspec_then `s1 with <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock - 1|>` mp_tac >> impl_tac
    >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
    >> disch_tac >> fs[]
    >> Cases_on `q''` >> TRY (Cases_on `x`) >> gvs[]
    >>~- ([`state_rel_code (empty_locals _) (empty_locals _)`],
      gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def])
    >- ( (* Return case *)
      TOP_CASE_TAC >> fs[]
      >> `s1.locals = s.locals` by fs[locals_strong_rel_def] >> fs[]
      >> TOP_CASE_TAC >> gvs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def]
    )
    (* Exception case *)
    >> reverse TOP_CASE_TAC >> gvs[]
    >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
    >> imp_res_tac evaluate_code_invariant >> fs[]
    >> first_x_assum drule
    >> disch_then rev_drule
    >> disch_then $ qspec_then `s1'' with locals := s1.locals` mp_tac >> impl_tac
    >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
    >> disch_tac >> fs[]
  )
  (* The main case, where the callee is marked inlined and this is the first occurence of the callee in this possibly recursive call chain *)
  >> Cases_on `x` >> fs[]
  >> pairarg_tac >> fs[]
  >> TOP_CASE_TAC >> fs[]
  >- suspend "Tail"
  >> Cases_on `x` >> fs[]
  >> Cases_on `r''` >> fs[]
  >- suspend "Nontail"
  >> gvs[evaluate_def, lookup_code_def, CaseEq "option", CaseEq "prod"]
  >> imp_res_tac opt_mmap_eval_code_inl >> fs[]
  >> qpat_assum `code_inl_rel _ _ _` $ imp_res_tac o SRULE[code_inl_rel_def] >> fs[]
  >> `s1.clock = s.clock` by fs[state_rel_code_def] >> fs[]
  >> Cases_on `s.clock = 0` >> fs[]
  >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
  >> Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> fs[]
  >> Cases_on `q'' = SOME Error` >> fs[dec_clock_def]
  >> last_x_assum drule
  >> disch_then drule
  >> disch_then $ qspec_then `s1 with <|locals := FEMPTY |++ ZIP (ns,args); clock := s.clock - 1|>` mp_tac >> impl_tac
  >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
  >> disch_tac >> fs[]
  >> Cases_on `q''` >> TRY (Cases_on `x`) >> gvs[]
  >>~- ([`state_rel_code (empty_locals _) (empty_locals _)`],
    gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def])
  >- ( (* Return case *)
    TOP_CASE_TAC >> fs[]
    >> `s1.locals = s.locals` by fs[locals_strong_rel_def] >> fs[]
    >> TOP_CASE_TAC >> gvs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def]
  )
  (* Exception case *)
  >> reverse TOP_CASE_TAC >> gvs[]
  >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
  >> imp_res_tac evaluate_code_invariant >> fs[]
  >> first_x_assum drule
  >> disch_then rev_drule
  >> disch_then $ qspec_then `s1'' with locals := s1.locals` mp_tac >> impl_tac
  >- fs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
  >> disch_tac >> fs[]
QED

Resume inline_prog_correct[Tail]:
  fs[inline_tail_def, evaluate_def]
  >> pairarg_tac
  >> fs[lookup_code_def, CaseEq "option", CaseEq "prod"]
  >> `s1.clock = s.clock` by fs[state_rel_code_def] >> fs[lookup_code_def]
  >> Cases_on `s.clock = 0` >> fs[]
  >- gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]
  >> gvs[arg_load_def]
  >> qmatch_goalsub_abbrev_tac `evaluate (nested_decs tmpvars _ wrapped, _)`
  >> Cases_on `evaluate (nested_decs tmpvars argexps wrapped, dec_clock s1)` >> fs[]
  >> qunabbrev_tac `wrapped`
  >> drule_at (Pos last) general_simulate_arg_load_strong_all_drule
  >> imp_res_tac eval_code_inl
  >> imp_res_tac opt_mmap_eval_code_inl >> gvs[opt_mmap_eval_dec_clock_eq, dec_clock_simp]
  >> qpat_assum `inl_bag SUBMAP _` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
  >> qpat_assum `_ SUBMAP s.code` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
  >> gvs[]
  >> disch_then $ qspec_then `FEMPTY` mp_tac >> fs[]
  >> qpat_x_assum `_ = (r, s')` mp_tac
  >> TOP_CASE_TAC >> fs[]
  >> disch_tac >> Cases_on `q = SOME Error` >> fs[]
  >> first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag \\ fname`] mp_tac >> impl_tac
  >- (fs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def] >> metis_tac[SUBMAP_TRANS, SUBMAP_DOMSUB])
  >> disch_tac >> fs[]
  >> drule_all unreach_elim_correct
  >> disch_tac >> fs[] >> impl_tac
  >- (
    rw[Abbr `tmpvars`, LENGTH_GENLIST, ALL_DISTINCT_GENLIST]
    >> imp_res_tac mem_genlist_add_suc_val
    >> fs[]
    >> metis_tac[MAX_LIST_PROPERTY, NOT_LE]
  )
  >> disch_tac >> fs[]
  >> Cases_on `q` >> TRY (Cases_on `x`) >> gvs[empty_locals_def, state_rel_code_def, state_rel_def, code_inl_rel_def]
QED


Theorem evaluate_replicate_const:
  ∀n s. OPT_MMAP (eval s) (REPLICATE n (Const 0w)) = SOME (REPLICATE n (Word 0w))
Proof
  Induct >> fs[eval_def]
QED

Theorem max_list_genlist_add_suc_val:
 n ≠ 0 ⇒  MAX_LIST (GENLIST (λx. SUC x + k) n) = n + k
Proof
  Induct_on `n` >> fs[GENLIST]
  >> Cases_on `n` >> fs[MAX_DEF]
QED

Theorem update_list_locals_not_vars_eval_eq:
  ∀vs s res e vals.
    (!x. MEM x vs ⇒ ¬MEM x (var_cexp e)) ∧ eval s e = res ∧ LENGTH vs = LENGTH vals ⇒
    eval (s with locals := s.locals |++ ZIP (vs, vals)) e = res
Proof
  Induct >> rw[]
  >- (fs[FUPDATE_LIST] >> `s with locals := s.locals = s` by fs[state_component_equality] >> fs[])
  >> Cases_on `vals` >> fs[FUPDATE_LIST_THM, DISJ_IMP_THM, FORALL_AND_THM]
  >> imp_res_tac update_locals_not_vars_eval_eq'
  >> pop_assum $ qspecl_then [`h'`, `s`] assume_tac >> fs[]
  >> last_x_assum imp_res_tac >> fs[]
  >> pop_assum $ qspec_then `t` mp_tac >> fs[]
  >> disch_then $ qspec_then `s with locals := s.locals |+ (h, h')` assume_tac >> fs[]
QED

Theorem opt_mmap_update_list_locals_not_vars_eval_eq:
  ∀es vs vals s res.
    (!x. MEM x vs ==> ¬MEM x (FLAT (MAP var_cexp es))) ∧ OPT_MMAP (eval s) es = res ∧ LENGTH vs = LENGTH vals ⇒
      OPT_MMAP (eval (s with locals := s.locals |++ ZIP (vs, vals))) es = res
Proof
  Induct >> rw[IMP_CONJ_THM, FORALL_AND_THM]
  >> imp_res_tac update_list_locals_not_vars_eval_eq
  >> res_tac >> fs[]
QED

Theorem opt_mmap_update_list_locals_not_vars_eval_eq':
  ∀es vs ws vals s locs.
    (!x. MEM x vs ==> ¬MEM x (FLAT (MAP var_cexp es))) ∧ LENGTH vs = LENGTH vals ⇒
      OPT_MMAP (eval (s with locals := locs |++ ZIP (vs, vals))) es = OPT_MMAP (eval (s with locals := locs)) es
Proof
  rpt strip_tac
  >> imp_res_tac $ INST_TYPE [beta |-> gamma] opt_mmap_update_list_locals_not_vars_eval_eq >> fs[]
  >> pop_assum kall_tac
  >> pop_assum $ qspec_then `s with locals := locs` assume_tac >> fs[]
QED

Theorem FDIFF_fupdate_list_empty_flookup_var[local]:
  ∀fm zs val val2 fm' x v.
  FDIFF (fm |++ ZIP (zs, REPLICATE (LENGTH zs) val)) (FDOM (FEMPTY |++ ZIP (zs, REPLICATE (LENGTH zs) val2))) SUBMAP fm' ∧
  FLOOKUP fm x = SOME v ∧
  ¬MEM x zs
  ⇒
    FLOOKUP fm' x = SOME v
Proof
  rpt strip_tac
  >> fs[SUBMAP_FLOOKUP_EQN, FLOOKUP_SIMP, FDOM_FUPDATE_LIST]
  >> last_x_assum mp_tac
  >> DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] >> fs[]
  >> disch_then imp_res_tac
  >> pop_assum mp_tac
  >> DEP_REWRITE_TAC [flookup_fupdate_zip_not_mem] >> fs[]
QED

Theorem FDIFF_fupdate_list_empty_flookup[local]:
  !xs fm zs val val2 fm' vs.
  FDIFF (fm |++ ZIP (zs, REPLICATE (LENGTH zs) val)) (FDOM (FEMPTY |++ ZIP (zs, REPLICATE (LENGTH zs) val2))) SUBMAP fm' ∧
  OPT_MMAP (FLOOKUP fm) xs = SOME vs ∧
  (!x. MEM x xs ⇒ ¬MEM x zs)
  ⇒
    OPT_MMAP (FLOOKUP fm') xs = SOME vs
Proof
  rpt strip_tac
  >> fs[SUBMAP_FLOOKUP_EQN, FLOOKUP_SIMP, FDOM_FUPDATE_LIST]
  >> last_x_assum mp_tac
  >> DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] >> fs[]
  >> disch_tac >> fs[]
  >> last_assum $ PURE_REWRITE_TAC o single o Once o GSYM
  >> irule OPT_MMAP_CONG >> fs[]
  >> rpt strip_tac
  >> imp_res_tac opt_mmap_mem_func >> gvs[]
  >> res_tac >> fs[]
  >> qpat_x_assum `!_ _. _` mp_tac
  >> metis_tac[flookup_fupdate_zip_not_mem, LENGTH_REPLICATE]
QED

Theorem FOLDL_res_var_ZIP_lookup_var[local]:
  ∀l ns l' l1 x v.
  FOLDL res_var l (ZIP (ns, MAP (FLOOKUP l') ns)) SUBMAP l1 ∧
  FLOOKUP l x = SOME v ∧
  ¬MEM x ns ⇒
    FLOOKUP l1 x = SOME v
Proof
  rpt strip_tac
  >> fs[SUBMAP_FLOOKUP_EQN]
  >> last_x_assum $ qspec_then `x` mp_tac >> fs[]
  >> DEP_REWRITE_TAC [flookup_res_var_distinct_zip_eq] >> fs[LENGTH_MAP]
QED


Theorem FOLDL_res_var_ZIP_lookup[local]:
  ∀l ns l' l1 xs vs.
  FOLDL res_var l (ZIP (ns, MAP (FLOOKUP l') ns)) SUBMAP l1 ∧
  OPT_MMAP (FLOOKUP l) xs = SOME vs ∧
  (!x. MEM x xs ⇒ ¬MEM x ns) ⇒
    OPT_MMAP (FLOOKUP l1) xs = SOME vs
Proof
  rpt strip_tac
  >> fs[SUBMAP_FLOOKUP_EQN]
  >> qpat_assum `OPT_MMAP _ _ = _` $ PURE_REWRITE_TAC o single o Once o GSYM
  >> irule OPT_MMAP_CONG >> fs[]
  >> rpt strip_tac
  >> res_tac >> fs[]
  >> last_x_assum $ qspec_then `x` mp_tac >> fs[]
  >> DEP_REWRITE_TAC [flookup_res_var_distinct_zip_eq] >> fs[LENGTH_MAP]
  >> metis_tac[opt_mmap_mem_func]
QED

Theorem submap_finish_flookup[local]:
 ∀fm q l fm' ns.
  (∀x y. ¬MEM x q ∧ ¬MEM x ns ∧ FLOOKUP fm x = SOME y ⇒  FLOOKUP fm' x = SOME y) ∧
  (∀x. MEM x q ⇒ ¬MEM x ns) ∧
  ALL_DISTINCT q ∧
  OPT_MMAP (FLOOKUP fm') q = SOME l ⇒
  fm |++ ZIP (q, l) SUBMAP (FOLDL res_var fm' (ZIP (ns, MAP (FLOOKUP fm) ns)))
Proof
  rpt strip_tac >> fs[SUBMAP_FLOOKUP_EQN]
  >> rpt gen_tac
  >> imp_res_tac opt_mmap_length_eq
  >> Cases_on `MEM x q` >> fs[]
  >- (
    res_tac
    >> DEP_REWRITE_TAC [flookup_res_var_distinct_zip_eq] >> fs[LENGTH_MAP, MEM_EL]
    >> DEP_REWRITE_TAC [update_eq_zip_flookup]
    >> imp_res_tac opt_mmap_el >> fs[]
  )
  >> DEP_REWRITE_TAC [flookup_fupdate_zip_not_mem] >> fs[]
  >> res_tac >> fs[]
  >> disch_tac >> fs[]
  >> Cases_on `MEM x ns` >> fs[]
  >- (imp_res_tac flookup_res_var_is_mem_zip_eq >> gvs[])
  >> DEP_REWRITE_TAC [flookup_res_var_distinct_zip_eq] >> fs[LENGTH_MAP]
QED

Resume inline_prog_correct[Nontail]:
  qmatch_goalsub_abbrev_tac `inline_nontail _ _ _ tmp_vars _ _`
  >> qmatch_goalsub_abbrev_tac `transform_eoc rts _`
  >> Cases_on `caltyp` >> fs[]
  >> Cases_on `x` >> fs[]
  >> reverse $ Cases_on `r''` >> gvs[]
  >- (Cases_on `x` >> fs[])
  >> gvs[evaluate_def, CaseEq "prod", CaseEq "option", lookup_code_def]
  >> `s1.clock = s.clock` by fs[state_rel_code_def]
  >> qpat_assum `inl_bag SUBMAP _` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
  >> qpat_assum `_ SUBMAP _.code` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
  >> gvs[]
  >> Cases_on `s.clock = 0` >> fs[]
  >- (
    fs[inline_nontail_def, arg_load_def]
    >> qmatch_goalsub_abbrev_tac `evaluate (nested_decs _ _ wrapped_block, _)`
    >> Cases_on `evaluate (nested_decs rts (REPLICATE (LENGTH rts) (Const 0w)) wrapped_block, s1)`
    >> drule_at (Pos last) evaluate_nested_decs_locals_nested_res_var_drule
    >> qspecl_then [`LENGTH rts`, `s1`] assume_tac evaluate_replicate_const >> fs[]
    >> Cases_on `evaluate (wrapped_block, s1 with locals := s1.locals |++ ZIP (rts, REPLICATE (LENGTH rts) (Word 0w)))` >> fs[] >> impl_tac
    >- fs[Abbr `rts`, ALL_DISTINCT_GENLIST, var_cexp_def]
    >> disch_tac >> fs[Abbr `wrapped_block`, Once evaluate_def]
    >> pairarg_tac >> fs[]
    >> drule_at (Pos last) general_simulate_arg_load_strong_all_drule >> fs[]
    >> disch_then $ qspecl_then [`args`, `FEMPTY`] mp_tac >> gvs[]
    >> qmatch_goalsub_abbrev_tac `evaluate (case_prog, simpstate)`
    >> Cases_on `evaluate (case_prog, simpstate)` >> fs[Abbr `case_prog`, Abbr `simpstate`, Ntimes evaluate_def 10, eval_def]
    >> impl_tac
    >- (
      rpt conj_tac
      >- (
        DEP_REWRITE_TAC[opt_mmap_update_list_locals_not_vars_eval_eq']
        >> fs[]
        >> `s1 with locals := s1.locals = s1` by fs[state_component_equality] >> fs[]
        >> imp_res_tac opt_mmap_eval_code_inl >> fs[]
        >> rpt strip_tac
        >> fs[Abbr `rts`] >> imp_res_tac mem_genlist_add_suc_val
        >> imp_res_tac MAX_LIST_PROPERTY
        >> fs[Abbr `tmp_vars`]
        >> imp_res_tac mem_genlist_add_suc_val >> fs[]
        >> Cases_on `LENGTH args = 0`
        >- (imp_res_tac opt_mmap_length_eq >> gvs[])
        >> imp_res_tac max_list_genlist_add_suc_val
        >> pop_assum $ fs o single
        >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
      )
      >- (
        Cases_on `not_branch_ret inlined_callee` >> gvs[Ntimes evaluate_def 10, eval_def]
      )
      >- fs[Abbr `tmp_vars`, ALL_DISTINCT_GENLIST]
      >- fs[Abbr `tmp_vars`, LENGTH_GENLIST]
      >- (
        rpt strip_tac >> fs[Abbr `tmp_vars`]
        >> imp_res_tac mem_genlist_add_suc_val
        >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
      )
      >> rpt strip_tac >> fs[Abbr `tmp_vars`]
      >> imp_res_tac mem_genlist_add_suc_val
      >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
    )
    >> disch_tac
    >> Cases_on `not_branch_ret inlined_callee`
    >> gvs[Ntimes evaluate_def 10, eval_def, state_rel_code_def, state_rel_def, empty_locals_def, code_inl_rel_def]
  )
  >> simp[inline_nontail_def]
  >> qmatch_goalsub_abbrev_tac `evaluate (nested_decs _ _ wrapped_block, _)`
  >> Cases_on `evaluate (nested_decs rts (REPLICATE (LENGTH rts) (Const 0w)) wrapped_block, s1)`
  >> drule_at (Pos last) evaluate_nested_decs_locals_nested_res_var_drule
  >> qspecl_then [`LENGTH rts`, `s1`] assume_tac evaluate_replicate_const >> fs[]
  >> Cases_on `evaluate (wrapped_block, s1 with locals := s1.locals |++ ZIP (rts, REPLICATE (LENGTH rts) (Word 0w)))` >> fs[] >> impl_tac
  >- fs[Abbr `rts`, ALL_DISTINCT_GENLIST, var_cexp_def]
  >> disch_tac >> gvs[Abbr `wrapped_block`, Once evaluate_def]
  >> pairarg_tac >> gvs[arg_load_def]
  >> qpat_x_assum `_ = (r, s')` mp_tac
  >> TOP_CASE_TAC >> fs[]
  >> disch_tac >> fs[]
  >> Cases_on `q'' = SOME Error` >> fs[dec_clock_simp]
  >> first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP(ns, args)`, `inl_bag \\ fname`] mp_tac >> impl_tac
  >- (
    fs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]
    >> metis_tac[SUBMAP_DOMSUB, SUBMAP_TRANS]
  )
  >> disch_tac >> fs[]
  >> drule_all unreach_elim_correct
  >> disch_tac >> fs[arg_load_def, inline_nontail_def]
  >> drule evaluate_state_locals_rel_strong >> fs[]
  >> disch_then $ qspec_then `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args) |++ ZIP (rts, REPLICATE (LENGTH rts) (Word 0w))` mp_tac >> fs[] >> impl_tac
  >- (
    fs[state_rel_def, locals_rel_def]
    >> irule SUBMAP_DIFF_LIST >> fs[Abbr `rts`, ALL_DISTINCT_GENLIST, LENGTH_GENLIST, LENGTH_REPLICATE]
    >> fs[FDOM_FUPDATE_LIST]
    >> DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] >> fs[Abbr `tmp_vars`]
    >> rpt strip_tac
    >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    >> Cases_on `LENGTH args = 0` >- gvs[]
    >> imp_res_tac max_list_genlist_add_suc_val
    >> pop_assum kall_tac
    >> pop_assum $ fs o single
    >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
    >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
  )
  >> disch_tac >> fs[]
  >> qpat_x_assum `evaluate _ = (res, s1')` assume_tac
  >> drule_at (Pos last) general_simulate_arg_load_strong_all_drule >> fs[]
  >> disch_then $ qspecl_then [`args`, `FEMPTY |++ ZIP (rts, REPLICATE (LENGTH rts) (Word 0w))`] mp_tac
  >> qmatch_goalsub_abbrev_tac `evaluate (if_prog, subloc)`
  >> Cases_on `evaluate (if_prog, subloc)` >> fs[] >> impl_tac
  >- (
    rpt conj_tac
    >- (
      DEP_REWRITE_TAC [opt_mmap_update_list_locals_not_vars_eval_eq']
      >> fs[Abbr `rts`]
      >> conj_tac
      >- (
        rpt strip_tac
        >> imp_res_tac mem_genlist_add_suc_val
        >> fs[Abbr `tmp_vars`]
        >> Cases_on `LENGTH args = 0`
        >- (
          gvs[]
          >> imp_res_tac opt_mmap_length_eq >> fs[]
        )
        >> imp_res_tac max_list_genlist_add_suc_val
        >> pop_assum kall_tac
        >> pop_assum $ fs o single
        >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
        >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
      )
      >> `s1 with locals := s1.locals = s1` by fs[state_component_equality, dec_clock_def] >> fs[opt_mmap_eval_dec_clock_eq]
      >> imp_res_tac opt_mmap_eval_code_inl
    )
    >- metis_tac[SUBMAP_FEMPTY, LENGTH_REPLICATE, SUBMAP_IMP_FUPDATE_LIST_SUBMAP]
    >- (
      fs[FDOM_FUPDATE_LIST]
      >> DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] >> fs[]
      >> rpt strip_tac >> fs[Abbr `rts`]
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
      >- (
        imp_res_tac MAX_LIST_PROPERTY >> fs[Abbr `tmp_vars`]
        >> Cases_on `LENGTH args = 0` >- gvs[]
        >> imp_res_tac max_list_genlist_add_suc_val
        >> pop_assum kall_tac
        >> pop_assum $ fs o single >> fs[]
        >> imp_res_tac mem_genlist_add_suc_val >> fs[]
        >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
      )
      >> imp_res_tac MAX_LIST_PROPERTY
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    )
    >- (
      fs[Abbr `if_prog`, Abbr `subloc`]
      >> qpat_x_assum `_ = (q'', t')` assume_tac
      >> drule wrapped_transform_if
      >> imp_res_tac unreach_elim_converge >> fs[]
      >> disch_then $ qspec_then `rts` mp_tac >> fs[] >> impl_tac
      >- (
        rpt conj_tac
        >- (
          rpt strip_tac >> gvs[CaseEq "bool", CaseEq "prod", Abbr `rts`, LENGTH_GENLIST]
        )
        >- (
          rpt strip_tac
          >> fs[Abbr `rts`]
          >> imp_res_tac mem_genlist_add_suc_val
          >> imp_res_tac MAX_LIST_PROPERTY >> fs[vmax_prog_def]
        )
        >- (
          DEP_REWRITE_TAC[opt_mmap_some_eq_zip_flookup] >> fs[Abbr `rts`, ALL_DISTINCT_GENLIST, LENGTH_GENLIST]
        )
        >- fs[Abbr `rts`, ALL_DISTINCT_GENLIST]
        >> Cases_on `q''` >> TRY (Cases_on `x`) >> fs[cont_res_def]
      )
      >> disch_tac >> gvs[]
      >> qpat_x_assum `evaluate (if _ then _ else _, _) = _` mp_tac
      >> DEP_PURE_ONCE_REWRITE_TAC [FUPDATE_LIST_APPEND_COMMUTES]
      >> conj_tac
      >- (
        DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP]
        >> fs[LENGTH_REPLICATE, GSYM distinct_lists_eq_disjoint, distinct_lists_def, EVERY_MEM]
        >> rpt strip_tac >> fs[Abbr `rts`]
        >> imp_res_tac mem_genlist_add_suc_val >> fs[Abbr `tmp_vars`]
        >> imp_res_tac mem_genlist_add_suc_val >> fs[]
        >> Cases_on `LENGTH args = 0` >- gvs[]
        >> imp_res_tac max_list_genlist_add_suc_val
        >> pop_assum kall_tac
        >> pop_assum $ fs o single
        >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
        >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
      )
      >> disch_tac >> gvs[]
      >> every_case_tac >> fs[]
    )
    >- fs[Abbr `tmp_vars`, ALL_DISTINCT_GENLIST]
    >- fs[Abbr `tmp_vars`, LENGTH_GENLIST]
    >- (
      rpt strip_tac >> fs[Abbr `tmp_vars`]
      >> imp_res_tac MAX_LIST_PROPERTY
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    )
    >> rpt strip_tac >> fs[Abbr `tmp_vars`]
    >> imp_res_tac MAX_LIST_PROPERTY
    >> imp_res_tac mem_genlist_add_suc_val >> fs[]
  )
  >> disch_tac >> gvs[]
  >> fs[Abbr `if_prog`, Abbr `subloc`]
  >> qpat_x_assum `_ = (q'', t')` assume_tac
  >> drule wrapped_transform_if >> fs[]
  >> imp_res_tac unreach_elim_converge >> fs[]
  >> disch_then $ qspec_then `rts` mp_tac >> fs[] >> impl_tac
  >- (
    rpt conj_tac
    >- (
      rpt strip_tac >> gvs[CaseEq "bool", CaseEq "prod", Abbr `rts`, LENGTH_GENLIST]
    )
    >- (
      rpt strip_tac
      >> fs[Abbr `rts`]
      >> imp_res_tac mem_genlist_add_suc_val
      >> imp_res_tac MAX_LIST_PROPERTY >> fs[vmax_prog_def]
    )
    >- (
      DEP_REWRITE_TAC[opt_mmap_some_eq_zip_flookup] >> fs[Abbr `rts`, ALL_DISTINCT_GENLIST, LENGTH_GENLIST]
    )
    >- fs[Abbr `rts`, ALL_DISTINCT_GENLIST]
    >> Cases_on `q''` >> TRY (Cases_on `x`) >> fs[cont_res_def]
  )
  >> disch_tac >> gvs[]
  >> qpat_x_assum `evaluate (if _ then _ else _, _) = _` mp_tac
  >> DEP_PURE_ONCE_REWRITE_TAC [FUPDATE_LIST_APPEND_COMMUTES]
  >> conj_tac
  >- (
    DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP]
    >> fs[LENGTH_REPLICATE, GSYM distinct_lists_eq_disjoint, distinct_lists_def, EVERY_MEM]
    >> rpt strip_tac >> fs[Abbr `rts`]
    >> imp_res_tac mem_genlist_add_suc_val >> fs[Abbr `tmp_vars`]
    >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    >> Cases_on `LENGTH args = 0` >- gvs[]
    >> imp_res_tac max_list_genlist_add_suc_val
    >> pop_assum kall_tac
    >> pop_assum $ fs o single
    >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
    >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
  )
  >> disch_tac >> gvs[]
  >> Cases_on `q''` >> TRY (Cases_on `x`) >> gvs[cont_res_def]
  >>~- ([`state_rel_code (empty_locals _) _ ∧ code_inl_rel _ (empty_locals _) _`],
    gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def, state_rel_def])
  >> gvs[CaseEq "option", CaseEq "bool"]
  >> qpat_x_assum `FOLDL res_var _ _ SUBMAP _` mp_tac
  >> DEP_REWRITE_TAC [map_flookup_fupdate_zip_not_mem]
  >> conj_tac
  >- (
    fs[Abbr `rts`, distinct_lists_def, EVERY_MEM]
    >> rpt strip_tac >> fs[]
    >> imp_res_tac mem_genlist_add_suc_val >> fs[Abbr `tmp_vars`]
    >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    >> Cases_on `LENGTH args = 0` >- gvs[]
    >> imp_res_tac max_list_genlist_add_suc_val
    >> pop_assum kall_tac
    >> pop_assum $ fs o single
    >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
    >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
  )
  >> disch_tac
  >> drule_at (Pos last) evaluate_nested_seq_assign_drule
  >> disch_then $ qspecl_then [`l`, `v1`] mp_tac >> fs[] >> impl_tac
  >- (
    simp[GSYM lookup_locals_eq_map_vars]
    >> rpt conj_tac
    >- (
      irule FOLDL_res_var_ZIP_lookup
      >> qrefine `r''''.locals` >> fs[]
      >> qrefine `s1.locals` >> fs[]
      >> qrefine `ns` >> fs[]
      >> rpt strip_tac >> fs[Abbr `rts`]
      >> imp_res_tac mem_genlist_add_suc_val >> fs[Abbr `tmp_vars`]
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
      >> Cases_on `LENGTH args = 0` >- gvs[]
      >> imp_res_tac max_list_genlist_add_suc_val
      >> pop_assum kall_tac
      >> pop_assum $ fs o single
      >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
      >> metis_tac[MAX_LT, NOT_LE, LET_TRANS, LESS_TRANS, iterateTheory.LE_ADDR]
    )
    >- (
      fs[map_var_cexp_eq_var]
      >> rpt strip_tac >> fs[Abbr `rts`]
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
      >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
    )
    >> irule $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``, gamma |-> ``:'a word_lab``] FDIFF_fupdate_list_empty_flookup
    >> MAP_EVERY qrefine [`s1.locals`, `Word 0w`, `Word 0w`, `rts`] >> fs[]
    >> conj_tac
    >- (
      rpt strip_tac >> fs[Abbr `rts`]
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
      >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
    )
    >> gvs[locals_strong_rel_def]
  )
  >> disch_tac >> gvs[]
  >> rpt conj_tac
  >- gvs[state_rel_code_def, state_rel_def]
  >- gvs[code_inl_rel_def, state_rel_def]
  >> fs[locals_strong_rel_def]
  >> imp_res_tac evaluate_locals_same_fdom' >> gvs[]
  >> simp[EQ_FDOM_SUBMAP]
  >> DEP_REWRITE_TAC[opt_mmap_flookup_some_then_same_fdom] >> fs[]
  >> irule submap_finish_flookup >> fs[]
  >> conj_tac
  >- (
    rpt strip_tac
    >> imp_res_tac FDIFF_fupdate_list_empty_flookup_var
  )
  >> rpt strip_tac >> fs[Abbr `rts`]
  >> imp_res_tac mem_genlist_add_suc_val
  >> imp_res_tac MAX_LIST_PROPERTY >> fs[]
QED

Finalise inline_prog_correct;


Theorem exps_of_nested_seq_assign:
  ∀ns es e.
    MEM e (exps_of (nested_seq (MAP2 Assign ns es))) ⇒
    MEM e es
Proof
  Induct >> rw[nested_seq_def, exps_of_def]
  >> Cases_on `es` >> fs[nested_seq_def, exps_of_def]
QED

Theorem exps_of_nested_decs:
  ∀e vs es p.
   MEM e (exps_of (nested_decs vs es p)) ⇒
   MEM e es ∨ MEM e (exps_of p)
Proof
  Induct_on `es` >> Cases_on `vs` >> rw[nested_decs_def, exps_of_def] >>
  res_tac >> fs[]
QED

Theorem exps_of_arg_load:
  ∀e tmp_vars args args_vname p.
  MEM e (exps_of (arg_load tmp_vars args args_vname p)) ⇒
  MEM e args ∨ (∃c. MEM c tmp_vars ∧ e = Var c) ∨ MEM e (exps_of p)
Proof
  rw[arg_load_def] >>
  imp_res_tac exps_of_nested_decs >> fs[] >>
  imp_res_tac exps_of_nested_decs >> fs[MEM_MAP]
QED

Theorem submap_flookup_alist_to_fmap:
  ∀s t x v.
   s SUBMAP (alist_to_fmap t) ∧
   FLOOKUP s x = SOME v ⇒
   MEM (x, v) t
Proof
  rpt strip_tac >>
  fs[SUBMAP_FLOOKUP_EQN] >>
  res_tac >>
  imp_res_tac ALOOKUP_MEM >> fs[]
QED

Theorem exps_of_unreach_elim:
  ∀p q r e rt.
    unreach_elim p = (q, r) ∧
    MEM e (exps_of q) ⇒
    MEM e (exps_of p)
Proof
  recInduct unreach_elim_ind >> rw[exps_of_def, unreach_elim_def] >>
  rpt (pairarg_tac >> gvs[exps_of_def]) >> gvs[exps_of_def] >>
  every_case_tac >> rpt (pairarg_tac >> gvs[]) >> gvs[exps_of_def]
QED

Theorem exps_of_transform_eoc:
  ∀rts p e.
    MEM e (exps_of (transform_eoc rts p)) ⇒
    MEM e (exps_of p)
Proof
  recInduct transform_eoc_ind >> rw[transform_eoc_def, exps_of_def]
  >- imp_res_tac exps_of_nested_seq_assign
  >- (
    Cases_on `ctyp` >> fs[exps_of_def]
    >> Cases_on `x` >> fs[]
    >> Cases_on `r` >> fs[]
    >> Cases_on `x` >> fs[exps_of_def]
  )
  >> res_tac
  >> metis_tac[]
QED

Theorem exps_of_transform_branch:
  ∀ld rts p e.
    MEM e (exps_of (transform_branch ld rts p)) ⇒
    MEM e (exps_of p)
Proof
  recInduct transform_branch_ind >> rw[transform_branch_def, exps_of_def]
  >- imp_res_tac exps_of_nested_seq_assign
  >- (
    Cases_on `ctyp` >> fs[exps_of_def]
    >> Cases_on `x` >> fs[]
    >> Cases_on `r` >> fs[]
    >> Cases_on `x` >> fs[exps_of_def]
  )
  >> res_tac
  >> metis_tac[]
QED


Theorem exps_of_inst_inline:
  !inl_fs prog crep_code e.
    inl_fs SUBMAP (alist_to_fmap crep_code) ∧
    MEM e (exps_of (inline_prog inl_fs prog)) ⇒
    (MEM e (exps_of prog)) ∨
    (∃c. e = Const c) ∨
    (∃v. e = Var v) ∨
    (∃name params body.
      MEM (name, params, body) crep_code ∧
      MEM e (exps_of body))
Proof
  recInduct inline_prog_ind >> rpt conj_tac
  >> gvs[exps_of_def, inline_prog_def] >> rw[]
  >- (
    (* Call, w handler *)
    Cases_on `ctyp` >> fs[]
    >> Cases_on `x` >> fs[]
    >> Cases_on `r` >> fs[]
    >> Cases_on `x` >> fs[exps_of_def]
    >> res_tac >> fs[]
    >> ntac 3 disj2_tac >> fs[]
    >> MAP_EVERY qrefine [`name`, `params`, `body`] >> fs[]
  )
  >- (
    (* Call, no handlers *)
    Cases_on `FLOOKUP inlineable_fs e` >> fs[]
    >- (
      (* Function not found *)
      Cases_on `ctyp` >> fs[]
      >> Cases_on `x` >> fs[]
      >> Cases_on `r` >> fs[]
      >> Cases_on `x` >> fs[exps_of_def]
      >> res_tac >> fs[]
      >> ntac 3 disj2_tac >> fs[]
      >> MAP_EVERY qrefine [`name`, `params`, `body`] >> fs[]
    )
    >> Cases_on `x` >> fs[]
    >> pairarg_tac >> fs[]
    >> Cases_on `ctyp` >> fs[]
    >- (
      (* Tail *)
      fs[inline_tail_def, exps_of_def]
      >> drule_at (Pos last) SUBMAP_TRANS
      >> disch_then $ qspec_then `inlineable_fs \\ e` assume_tac >> fs[]
      >> res_tac >> fs[]
      >> imp_res_tac exps_of_arg_load >> fs[]
      >> imp_res_tac exps_of_unreach_elim >> fs[]
      >> res_tac >> fs[]
      >- (
        qpat_x_assum `inlineable_fs SUBMAP alist_to_fmap _` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
        >> imp_res_tac ALOOKUP_MEM
        >> ntac 3 disj2_tac >> fs[]
        >> MAP_EVERY qrefine [`e`, `q`,`r`] >> fs[]
      )
      >> ntac 3 disj2_tac >> fs[]
      >> MAP_EVERY qrefine [`name`, `params`, `body`] >> fs[]
    )
    >> Cases_on `x` >> fs[]
    >> Cases_on `r'` >> TRY (Cases_on `x`) >> fs[exps_of_def]
    >- (
      qmatch_asmsub_abbrev_tac `transform_eoc rts _`
      >> fs[inline_nontail_def]
      >> imp_res_tac exps_of_nested_decs
      >- (imp_res_tac MEM_REPLICATE_IMP >> fs[])
      >> fs[exps_of_def]
      >- (
        imp_res_tac exps_of_arg_load >> fs[]
        >> Cases_on `not_branch_ret inlined_callee` >> fs[exps_of_def]
        >- (
          imp_res_tac exps_of_transform_eoc
          >> imp_res_tac exps_of_unreach_elim
          >> drule_at (Pos last) SUBMAP_TRANS
          >> disch_then $ qspec_then `inlineable_fs \\ e` assume_tac >> fs[]
          >> res_tac >> fs[]
          >- (
            qpat_x_assum `inlineable_fs SUBMAP alist_to_fmap _` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
            >> imp_res_tac ALOOKUP_MEM
            >> ntac 3 disj2_tac >> fs[]
            >> MAP_EVERY qrefine [`e`, `q`,`r`] >> fs[]
          )
          >> ntac 3 disj2_tac >> fs[]
          >> MAP_EVERY qrefine [`name`, `params`, `body`] >> fs[]
        )
        >> imp_res_tac exps_of_transform_branch
        >> imp_res_tac exps_of_unreach_elim
        >> drule_at (Pos last) SUBMAP_TRANS
        >> disch_then $ qspec_then `inlineable_fs \\ e` assume_tac >> fs[]
        >> res_tac >> fs[]
        >- (
          qpat_x_assum `inlineable_fs SUBMAP alist_to_fmap _` $ imp_res_tac o SRULE[SUBMAP_FLOOKUP_EQN]
          >> imp_res_tac ALOOKUP_MEM
          >> ntac 3 disj2_tac >> fs[]
          >> MAP_EVERY qrefine [`e`, `q`,`r`] >> fs[]
        )
        >> ntac 3 disj2_tac >> fs[]
        >> MAP_EVERY qrefine [`name`, `params`, `body`] >> fs[]
      )
      >> imp_res_tac exps_of_nested_seq_assign
      >> fs[MEM_MAP]
    )
    >> res_tac >> fs[]
    >> ntac 3 disj2_tac >> fs[]
    >> MAP_EVERY qrefine [`name`, `params`, `body`] >> fs[]
  )
  >> res_tac >> metis_tac[]
QED

Theorem every_inst_crep_inline:
  ∀crep_code inl_fs.
   (∀e. MEM e crep_code ==>
          (λ(name,params,body).
             ∀e. MEM e (exps_of body) ⇒
                   every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)
                       e) e) ∧
   inl_fs SUBMAP (alist_to_fmap crep_code)
   ⇒
   (∀e. MEM e (compile_inl_prog inl_fs crep_code) ==>
          (λ(name,params,body).
             ∀e. MEM e (exps_of body) ⇒
                   every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)
                       e) e)
Proof
  rw[compile_inl_prog_def, MEM_MAP] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  last_assum drule >>
  disch_tac >> fs[] >>
  drule_at (Pos last) exps_of_inst_inline >>
  disch_then $ qspec_then `crep_code` mp_tac >> impl_tac
  >- (irule SUBMAP_TRANS >> qrefine `inl_fs` >> fs[]) >>
  disch_tac >> fs[every_exp_def] >>
  last_x_assum imp_res_tac >> fs[]
QED

Theorem fst_map_3_f:
  ∀inl_fs x. FST x = (FST o (λ(name, params, body). (name, params, inline_prog (inl_fs \\ name) body))) x
Proof
  rpt strip_tac >> PairCases_on `x` >> fs[]
QED


Theorem compile_inline_distinct:
  ∀crep_code inl_fs.
    ALL_DISTINCT (MAP FST crep_code) ⇒ ALL_DISTINCT (MAP FST (compile_inl_prog inl_fs crep_code))
Proof
  rpt strip_tac >> fs[compile_inl_prog_def, MAP_MAP_o] >>
  qspec_then `inl_fs` assume_tac $ INST_TYPE [alpha |-> beta, beta |-> alpha] fst_map_3_f >>
  subgoal `MAP FST crep_code = MAP (FST o (λ(name, params, body). (name, params, inline_prog (inl_fs \\ name) body))) crep_code` >> simp[]
  >- (
    irule MAP_CONG >>
    rpt strip_tac >> first_x_assum $ qspec_then `x` assume_tac >> fs[]
  ) >>
  fs[]
QED

Theorem evaluate_call_same_result_state:
  ∀e args s r s' t inl_fs.
    evaluate (Call NONE e args, s) = (r, s') ∧
    state_rel_code s t ∧
    inl_fs SUBMAP s.code ∧
    locals_strong_rel s t ∧
    code_inl_rel inl_fs s t ∧
    r ≠ SOME Error ⇒
    FST (evaluate (Call NONE e args, t)) = FST (evaluate (Call NONE e args, s)) ∧
    state_rel_code (SND (evaluate (Call NONE e args, s))) (SND (evaluate (Call NONE e args, t)))
Proof
  rpt gen_tac >> rpt disch_tac >> gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod", lookup_code_def] >>
  imp_res_tac opt_mmap_eval_code_inl >> fs[] >>
  qpat_assum `code_inl_rel _ _ _` $ imp_res_tac o SRULE [code_inl_rel_def] >> fs[] >>
  `t.clock = s.clock` by fs[state_rel_code_def] >> Cases_on `s.clock = 0` >> fs[]
  >- gvs[state_rel_code_def, empty_locals_def] >>
  Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args'))` >> gs[] >>
  drule inline_prog_correct >> fs[] >>
  disch_then $ qspecl_then [`inl_fs`, `dec_clock t with locals := FEMPTY |++ ZIP (ns, args')`, `inl_bag`] mp_tac >> impl_tac
  >- (
    gvs[dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, AllCaseEqs()]
  ) >>
  disch_tac >> gvs[AllCaseEqs(), state_rel_code_def, empty_locals_def]
QED

Theorem state_rel_imp_semantics_local:
  ∀s t crep_code start inl_fs ns prog.
    state_rel_code s t ∧
    locals_strong_rel s t ∧
    ALL_DISTINCT (MAP FST crep_code) ∧
    s.code = alist_to_fmap crep_code ∧
    inl_fs SUBMAP s.code ∧
    t.code = alist_to_fmap (compile_inl_prog inl_fs crep_code) ∧
    FLOOKUP s.code start = SOME (ns, prog) ∧
    semantics s start ≠ Fail ⇒
      semantics t start = semantics s start
Proof
  rw[] >>
  subgoal `code_inl_rel inl_fs s t`
  >- (
    rw[code_inl_rel_def, compile_inl_prog_def] >>
    qrefine `inl_fs \\ fname` >> fs[] >>
    imp_res_tac MEM_ALOOKUP >>
    imp_res_tac $ INST_TYPE [alpha |-> ``:mlstring # num list # 'a prog``, beta |-> ``:mlstring # num list # 'a prog``] MEM_MAP_f >>
    pop_assum $ qspec_then `λ(name, params, body). (name, params, inline_prog (inl_fs \\ name) body)` assume_tac >> fs[] >>
    drule compile_inline_distinct >>
    disch_then $ qspec_then `inl_fs` assume_tac >> fs[compile_inl_prog_def] >>
    drule MEM_ALOOKUP >>
    disch_then $ qspecl_then [`fname`, `(args, inline_prog (inl_fs \\ fname) prog')`] assume_tac >> gvs[]
  ) >>
  Cases_on `semantics s start` >> fs[]
  >- (
    gs[semantics_def, CaseEq "bool"] >>
    conj_tac
    >- (
      rpt strip_tac >>
      first_x_assum $ qspec_then `k` assume_tac >> fs[] >>
      Cases_on `evaluate (Call NONE start [], s with clock := k)` >> fs[] >>
      subgoal `q ≠ SOME Error`
      >- (
        Cases_on `q = SOME Error` >> fs[]
      ) >>
      drule evaluate_call_same_result_state >>
      disch_then $ qspecl_then [`t with clock := k`, `inl_fs`] mp_tac >> impl_tac
      >- (
        gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
      ) >>
      disch_tac >> gvs[]
    ) >>
    pop_assum mp_tac >>
    DEEP_INTRO_TAC some_intro >>
    rpt strip_tac >> fs[] >>
    DEEP_INTRO_TAC some_intro >>
    rpt strip_tac >> fs[]
    >- (
      last_assum $ qspec_then `k` assume_tac >>
      Cases_on `evaluate (Call NONE start [],s with clock := k)` >> gs[] >>
      first_x_assum $ qspecl_then [`k`, `r'`, `q`, `outcome`] assume_tac >> gs[] >>
      drule evaluate_call_same_result_state >>
      disch_then $ qspecl_then [`t with clock := k`, `inl_fs`] mp_tac >> impl_tac
      >- (
        gvs[AllCaseEqs(), state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
        Cases_on `q` >> TRY (Cases_on `x`) >> fs[]
      ) >>
      disch_tac >> gvs[]
    ) >>
    qsuff_tac `!k. (SND (evaluate (Call NONE start [],s with clock := k))).ffi = (SND (evaluate (Call NONE start [],t with clock := k))).ffi`
    >- (
      disch_tac >> gvs[]
    ) >>
    strip_tac >>
    last_assum $ qspec_then `k` assume_tac >> fs[] >>
    Cases_on `evaluate (Call NONE start [],s with clock := k)` >> gs[] >>
    Cases_on `evaluate (Call NONE start [],t with clock := k)` >> gs[] >>
    subgoal `q ≠ SOME Error`
    >- (Cases_on `q` >> TRY (Cases_on `x`) >> gs[]) >>
    rev_drule evaluate_call_same_result_state >>
    disch_then $ qspecl_then [`t with clock := k`, `inl_fs`] mp_tac >> impl_tac
    >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
    disch_tac >> gvs[state_rel_code_def]
  ) >>
  gs[semantics_def, CaseEq "bool"] >>
  conj_tac
  >- (
    rpt strip_tac >>
    first_x_assum $ qspec_then `k` assume_tac >> fs[] >>
    Cases_on `evaluate (Call NONE start [], s with clock := k)` >> fs[] >>
    subgoal `q ≠ SOME Error`
    >- (
      Cases_on `q = SOME Error` >> fs[]
    ) >>
    drule evaluate_call_same_result_state >>
    disch_then $ qspecl_then [`t with clock := k`, `inl_fs`] mp_tac >> impl_tac
    >- (
      gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
    ) >>
    disch_tac >> gvs[]
  ) >>
  pop_assum mp_tac >>
  DEEP_INTRO_TAC some_intro >>
  rpt strip_tac >> fs[] >>
  DEEP_INTRO_TAC some_intro >>
  rpt strip_tac >> gvs[]
  >- (
    subgoal `r ≠ SOME Error`
    >- (Cases_on `r` >> TRY (Cases_on `x`) >> gs[]) >>
    rev_drule evaluate_call_same_result_state >>
    disch_then $ qspecl_then [`t with clock := k`, `inl_fs`] mp_tac >> impl_tac
    >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
    disch_tac >> gvs[] >>
    Cases_on `k < k'`
    >- (
      Cases_on `evaluate (Call NONE start [], t with clock := k)` >> gs[] >>
      Cases_on `q = SOME TimeOut` >> gs[] >>
      drule evaluate_add_clock_eq >>
      disch_then $ qspec_then `k' - k` assume_tac >> gvs[state_rel_code_def] >>
      Cases_on `q` >> TRY (Cases_on `x`) >> fs[]
    ) >>
    Cases_on `evaluate (Call NONE start [], t with clock := k)` >> gs[] >>
    `k' ≤ k` by fs[] >>
    Cases_on `r' = SOME TimeOut` >> gs[] >>
    qpat_x_assum `evaluate (Call _ _ _, t with clock := k') = _` assume_tac >>
    drule evaluate_add_clock_eq >>
    disch_then $ qspec_then `k - k'` assume_tac >> gvs[state_rel_code_def] >>
    Cases_on `q` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  Cases_on `r = SOME Error` >> fs[] >>
  drule evaluate_call_same_result_state >>
  disch_then $ qspecl_then [`t with clock := k`, `inl_fs`] mp_tac >> impl_tac
  >- gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
  disch_tac >> fs[] >>
  last_x_assum $ qspec_then `k` assume_tac >> gs[] >>
  Cases_on `evaluate (Call NONE start [], t with clock := k)` >> gvs[] >>
  first_x_assum $ qspecl_then [`k`, `r'`, `q`] assume_tac >> fs[]
QED

Theorem state_rel_imp_semantics:
  ∀s t crep_code start inl_fname ns prog.
    state_rel_code s t ∧
    locals_strong_rel s t ∧
    ALL_DISTINCT (MAP FST crep_code) ∧
    s.code = alist_to_fmap crep_code ∧
    t.code = alist_to_fmap (compile_inl_top inl_fname crep_code) ∧
    FLOOKUP s.code start = SOME (ns, prog) ∧
    semantics s start ≠ Fail ⇒
      semantics t start = semantics s start
Proof
  rw[compile_inl_top_def] >>
  drule state_rel_imp_semantics_local >> simp[] >>
  disch_then $ qspecl_then [`crep_code`, `start`, `alist_to_fmap (FILTER (λ(x, y). MEM x inl_fname) crep_code)`, `ns`, `prog`] mp_tac >> gvs[] >> impl_tac >>
  fs[SUBMAP_FLOOKUP_EQN, ALOOKUP_EQ_FLOOKUP, ALOOKUP_FILTER]
QED
