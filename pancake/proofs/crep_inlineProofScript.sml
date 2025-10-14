(*
  Correctness proof for function inlining pass
*)
(*
open HolKernel Parse bossLib boolLib numLib stringLib preamble;i
open preamble;
open crepLangTheory crepSemTheory crepPropsTheory;
open pan_commonPropsTheory pan_commonTheory;
open crep_inlineTheory;
open prim_recTheory iterateTheory;
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

Theorem evaluate_locals_same_fdom:
  ∀p s r s'.
    evaluate (p, s) = (r, s') ∧
    (case r of
      | NONE => T
      | SOME Continue => T
      | SOME Break => T
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
    pairarg_tac >> gs[CaseEq "option", CaseEq "result"]
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
    fs[evaluate_def, CaseEq "option", CaseEq "pair$prod", CaseEq "word_lab", CaseEq "result"] >> gvs[]
    >>~- ([`FLOOKUP s.locals _ = SOME _`],
    fs[flookup_thm] >>
    qpat_x_assum `_ = FDOM s'.locals` $ rw o single o GSYM >> fs[ABSORPTION_RWT]) >>
    Cases_on `eid = eid'` >> fs[]
  ) >>
  rpt strip_tac >>
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
    (r = NONE ∨ r = SOME Break ∨ r = SOME Continue) ⇒
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
    ∃r' t'.
      evaluate (p, t) = (r, t') ∧ state_rel s' t' ∧
      case r of
        | NONE => r' = NONE ∧ locals_rel s' t' ∧ locals_ext_rel s s' t t'
        | SOME Break => r' = SOME Break ∧ locals_rel s' t' ∧ locals_ext_rel s s' t t'
        | SOME Continue => r' = SOME Continue ∧ locals_rel s' t' ∧ locals_ext_rel s s' t t'
        | SOME (Return retv) => r' = SOME (Return retv)
        | SOME (FinalFFI f) => r' = SOME (FinalFFI f)
        | SOME TimeOut => r' = SOME TimeOut
        | SOME (Exception e) => r' = SOME (Exception e)
        | _ => F
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
    gs[CaseEq "option", CaseEq "result"] >>
    TRY (
      qpat_x_assum `!_. locals_rel s1' _ ∧ state_rel s1' _ ⇒ _` $ qspec_then `s1` mp_tac >> fs[] >>
      disch_tac >> fs[] >>
      qrefine `r''` >>
      Cases_on `r` >> fs[]
    ) >>
    TRY (
      Cases_on `x` >> fs[]
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
    qrefine `r` >> gvs[CaseEq "option" , CaseEq "result"] >>
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
    qpat_x_assum `!_ _ _. _` kall_tac >>
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
    Cases_on `r` >> fs[locals_rel_def, locals_ext_rel_def] >>
    Cases_on `x` >> fs[]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rpt strip_tac >> fs[evaluate_def] >>
    imp_res_tac eval_state_locals_rel >> fs[] >>
    gs[CaseEq "option", CaseEq "word_lab"] >>
    pop_assum imp_res_tac >> fs[]
  )
  >~ [`evaluate (Call _ _ _, _)`]
  >- (
    rpt strip_tac >> fs[evaluate_def] >>
    imp_res_tac eval_optmmap_state_locals_rel >>
    imp_res_tac eval_state_locals_rel >>
    gs[CaseEq "option", CaseEq "word_lab", CaseEq "prod"] >>
    first_assum imp_res_tac >>
    `t.clock = s.clock` by fs[state_rel_def] >> fs[] >>
    `t.code = s.code` by fs[state_rel_def] >> fs[] >>
    qpat_assum `!_ _. OPT_MMAP _ _ = _ ⇒ _` imp_res_tac >> fs[] >>
    Cases_on `s.clock = 0` >> fs[]
    >- gvs[state_rel_def, empty_locals_def] >>
    qpat_x_assum `_ = (r, s')` mp_tac >>
    TOP_CASE_TAC >> fs[] >>
    TOP_CASE_TAC >> fs[] >>
    TOP_CASE_TAC >> fs[]
    >>~- ([`_ = _ ∧ empty_locals _ = _ ⇒ _`],
    disch_tac >> gvs[] >>
    pop_assum $ qspec_then `dec_clock t with locals := newlocals` mp_tac >> impl_tac
    >- fs[locals_rel_def, state_rel_def, dec_clock_def] >>
    disch_tac >> fs[state_rel_def, empty_locals_def]) >>
    gs[CaseEq "option", CaseEq "prod"] >> disch_tac >> gvs[] >>
    qpat_x_assum `!_. locals_rel (dec_clock s with locals := newlocals) _ ∧ state_rel _ _ ⇒ _` $ qspec_then `dec_clock t with locals := newlocals` mp_tac >> impl_tac
    >>~- ([`locals_rel (dec_clock _ with locals := _) (dec_clock _ with locals := _)`],
      fs[locals_rel_def, state_rel_def, dec_clock_def]) >>
    disch_tac >> fs[]
    >>~- ([`state_rel (empty_locals _) (empty_locals _)`],
      fs[state_rel_def, empty_locals_def])
    >- (
      qpat_x_assum `!_. locals_rel _ _ ∧ state_rel _ _ ⇒ _` $ qspec_then `t' with locals := t.locals` mp_tac >> impl_tac
      >- fs[state_rel_def, locals_rel_def] >>
      disch_tac >> fs[locals_rel_def, locals_ext_rel_def] >>
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    )
    >- (
      qpat_x_assum `!_. locals_rel _ _ ∧ state_rel _ _ ⇒ _` $ qspec_then `t' with locals := t.locals |+ (rt, w)` mp_tac >> impl_tac
      >- fs[locals_rel_def, state_rel_def, SUBMAP_IMP_FUPDATE_SUBMAP] >>
      fs[locals_rel_def] >>
      drule $ iffLR SUBMAP_FLOOKUP_EQN >>
      disch_then imp_res_tac >> fs[] >>
      disch_tac >> fs[] >>
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[locals_ext_rel_def] >>
      fs[FDIFF_def, compl_insert, GSYM DRESTRICT_DOMSUB] >>
      pop_assum $ fs o single o GSYM >>
      irule EQ_SYM >>
      irule DOMSUB_NOT_IN_DOM >>
      fs[FDOM_DRESTRICT, flookup_thm]
    ) >>
    Cases_on `c = eid'` >> gs[]
    >- (
      qpat_x_assum `!_. locals_rel _ _ ∧ state_rel _ _ ⇒ _` $ qspec_then `t' with locals := t.locals` mp_tac >> impl_tac
      >- fs[locals_rel_def, state_rel_def] >>
      disch_tac >> fs[locals_ext_rel_def] >>
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    ) >>
    qrefine `r` >> conj_tac
    >- gvs[state_rel_def, empty_locals_def] >>
    Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  fs[evaluate_def] >> rpt strip_tac
  >- fs[locals_ext_rel_def] >>
  imp_res_tac eval_state_locals_rel >> fs[] >>
  gs[CaseEq "option", CaseEq "word_lab"] >>
  pop_assum imp_res_tac >> fs[]
  >>~- ([`locals_ext_rel a a b b`], fs[locals_ext_rel_def])
  >>~- ([`_ with memory := _ = _`],
    qrefine `t with memory := m` >>
    gvs[state_rel_def, locals_rel_def, locals_ext_rel_def]
  )
  >- (
    fs[locals_rel_def] >>
    imp_res_tac SUBMAP_FLOOKUP_EQN >> fs[] >> conj_tac
    >- gvs[state_rel_def] >>
    gvs[SUBMAP_IMP_FUPDATE_SUBMAP] >>
    gs[locals_ext_rel_def, FDIFF_def, compl_insert, flookup_thm, GSYM DRESTRICT_DOMSUB] >>
    irule EQ_SYM >>
    irule DOMSUB_NOT_IN_DOM >> fs[FDOM_DRESTRICT]
  )
  >- (
    `t.globals = s.globals` by fs[state_rel_def] >>
    gvs[set_globals_def, state_rel_def, locals_rel_def, locals_ext_rel_def]
  )
  >- (
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
    gvs[state_rel_def, empty_locals_def, locals_rel_def, locals_ext_rel_def]
  )
  >- (
    fs[state_rel_def, empty_locals_def]
  )
  >- (
    `t.clock = s.clock` by fs[state_rel_def] >> fs[] >>
    Cases_on `s.clock = 0` >>
    gvs[state_rel_def, dec_clock_def, locals_rel_def, locals_ext_rel_def, empty_locals_def]
  ) >>
  fs[locals_rel_def] >>
  drule $ iffLR SUBMAP_FLOOKUP_EQN >>
  disch_then imp_res_tac >>
  gvs[state_rel_def, CaseEq "ffi_result", locals_ext_rel_def]
QED



Theorem evaluate_state_locals_rel:
  ∀p s r s' t.
    evaluate (p, s) = (r, s') ⇒
    r ≠ SOME Error ==>
    locals_rel s t ∧ state_rel s t ⇒
    ∃r' t'.
      evaluate (p, t) = (r, t') ∧ state_rel s' t' ∧
      case r of
        | NONE => r' = NONE ∧ locals_rel s' t'
        | SOME Break => r' = SOME Break ∧ locals_rel s' t'
        | SOME Continue => r' = SOME Continue ∧ locals_rel s' t'
        | SOME (Return retv) => r' = SOME (Return retv)
        | SOME (FinalFFI f) => r' = SOME (FinalFFI f)
        | SOME TimeOut => r' = SOME TimeOut
        | SOME (Exception e) => r' = SOME (Exception e)
        | _ => F
Proof
  rpt strip_tac >>
  drule_all evaluate_state_locals_rel_strong >>
  disch_tac >>
  Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
QED


Theorem evaluate_state_locals_rel_conj:
  ∀p s r s' t l.
    evaluate (p, s) = (r, s') /\
    r ≠ SOME Error /\
    locals_rel s t ∧ state_rel s t ⇒
    ∃r' t'.
      evaluate (p, t) = (r, t') ∧ state_rel s' t' ∧
      case r of
        | NONE => r' = NONE ∧ locals_rel s' t'
        | SOME Break => r' = SOME Break ∧ locals_rel s' t'
        | SOME Continue => r' = SOME Continue ∧ locals_rel s' t'
        | SOME (Return retv) => r' = SOME (Return retv)
        | SOME (FinalFFI f) => r' = SOME (FinalFFI f)
        | SOME TimeOut => r' = SOME TimeOut
        | SOME (Exception e) => r' = SOME (Exception e)
        | _ => F
Proof
  rpt strip_tac >>
  irule evaluate_state_locals_rel >> conj_tac >> fs[] >>
  qexists `s` >> simp[]
QED


Theorem MAX_LIST_MORE_NOT_MEM:
  ∀e l. MAX_LIST l < e ⇒ ¬MEM e l
Proof
  rpt strip_tac >>
  imp_res_tac MAX_LIST_PROPERTY >> fs[]
QED

Theorem domsub_locals_not_vars_eval_eq:
  ∀s e r v.
    ¬ MEM v (var_cexp e) ∧
    eval s e = r  ⇒
    eval (s with locals := s.locals \\ v) e = r
Proof
  ho_match_mp_tac eval_ind >>
  rpt conj_tac >>
  rpt strip_tac >>
  gs[eval_def, var_cexp_def, DOMSUB_FLOOKUP_THM, CaseEq "option", CaseEq "word_lab", mem_load_def, MEM_MAP, MEM_FLAT] >>
  TRY (
    qpat_assum `OPT_MMAP _ _ = NONE` kall_tac >>
    disj1_tac
  ) >>
  TRY (
    qpat_assum `OPT_MMAP _ _ = SOME _` kall_tac >>
    disj2_tac >>
    qrefine `ws` >> fs[]
  ) >>
  qpat_x_assum `OPT_MMAP _ _ = _` $ fs o single o GSYM >>
  irule OPT_MMAP_CONG >>
  rpt strip_tac >> fs[] >>
  last_x_assum imp_res_tac >>
  last_x_assum $ qspec_then `var_cexp x` assume_tac >> gs[]
QED

Theorem res_var_not_vars_eval_eq:
  ∀v e s r u.
    ¬MEM v (var_cexp e) ∧
    eval s e = r ==>
    eval (s with locals := res_var s.locals (v, u)) e = r
Proof
  rpt strip_tac >>
  Cases_on `u` >>
  gs[res_var_def, update_locals_not_vars_eval_eq', domsub_locals_not_vars_eval_eq]
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

Theorem MAX_LIST_APPEND:
  ∀l1 l2. MAX_LIST l1 ≤ MAX_LIST (l1 ++ l2) ∧ MAX_LIST l2 ≤ MAX_LIST (l1 ++ l2)
Proof
  rpt gen_tac >>
  Induct_on `l1` >> gs[APPEND]
QED

Theorem ret_in_loop_imp_has_return:
  ∀p. return_in_loop p ⇒ has_return p
Proof
  recInduct has_return_ind >> gs[has_return_def, return_in_loop_def] >>
  rw[] >>
  gvs[] >>
  every_case_tac >> gs[]
QED

Theorem not_has_return_imp_not_ret_in_loop:
  ∀p. (¬has_return p) ⇒ (¬return_in_loop p)
Proof
  spose_not_then assume_tac >>
  gvs[ret_in_loop_imp_has_return]
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

Theorem transform_standalone_correct:
  ∀p s r s' f.
    evaluate (p, s) = (r, s') ∧
    f = standalone_ret ∧
    ¬ return_in_loop p ∧
    r ≠ SOME Error ⇒
    ∃r1 s1'.
    evaluate (transform_rec f p, s) = (r1, s1') ∧
    state_rel s' s1' ∧
    case r of
        | NONE => r1 = NONE ∧ locals_rel s' s1'
        | SOME Break => r1 = SOME Break ∧ locals_rel s' s1'
        | SOME Continue => r1 = SOME Continue ∧ locals_rel s' s1'
        | SOME (Return v) => r1 = SOME Break
        | SOME (Exception e) => r1 = SOME (Exception e)
        | SOME TimeOut => r1 = SOME TimeOut
        | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
        | _ => F
Proof
  recInduct evaluate_ind >> gs[transform_rec_def, standalone_ret_def] >>
  rw[]
  >>~- ([`state_rel s' s'`], gs[state_rel_def])
  >~ [`While _ _`]
  >- (
    gs[return_in_loop_def, has_return_def] >>
    TOP_CASE_TAC >> gs[]
    >- (
      gs[locals_rel_def]
    ) >>
    TOP_CASE_TAC >> gs[]
    >- gs[locals_rel_def]
    >- gs[locals_rel_def] >>
    `~has_return (While e c)` by gs[has_return_def] >>
    drule_all not_has_return_not_evaluate_return' >> gs[]
  ) >>
  gs[evaluate_def]
  >- gs[locals_rel_def]
  >- ( (* Dec *)
    TOP_CASE_TAC >> gs[] >>
    pairarg_tac >> gs[] >>
    pairarg_tac >> gvs[return_in_loop_def] >>
    TOP_CASE_TAC >> gvs[state_rel_def, locals_rel_def, res_var_submap_res_var] >>
    TOP_CASE_TAC >> gvs[res_var_submap_res_var]
  )
  >~ [`Seq _ _`]
  >- (
    pairarg_tac >> gs[] >>
    pairarg_tac >> gs[return_in_loop_def] >>
    qpat_x_assum `_ = (r, s')` mp_tac >>
    TOP_CASE_TAC >> gs[] >> disch_tac >>
    TOP_CASE_TAC >> gs[]
    >- (
      rev_drule evaluate_state_locals_rel >> gs[] >>
      disch_then $ qspec_then `s1` assume_tac >> gs[state_rel_def, locals_rel_def] >>
      irule SUBMAP_TRANS >> qrefine `s1'''.locals` >> gs[]
    )
    >- (
      rev_drule evaluate_state_locals_rel >> gs[] >>
      disch_then $ qspec_then `s1` assume_tac >> gs[] >>
      Cases_on `x` >> gs[locals_rel_def, state_rel_def] >>
      irule SUBMAP_TRANS >> qrefine `s1'''.locals` >> gs[]
    ) >>
    TOP_CASE_TAC >> gs[] >>
    TOP_CASE_TAC >> gs[] >>
    TOP_CASE_TAC >> gs[]
  )
  >~ [`If _ _ _`]
  >- (
    TOP_CASE_TAC >> gs[] >>
    TOP_CASE_TAC >> gs[] >>
    TOP_CASE_TAC >> gs[return_in_loop_def]
  )
  >~ [`Call _ _ _`]
  >- (
    gvs[CaseEq "option", CaseEq "word_lab", CaseEq "prod", lookup_code_def] >> 
    Cases_on `caltyp` >> fs[]
    >- (
      fs[evaluate_def] >>
      pairarg_tac >> gs[lookup_code_def, CaseEq "bool"]
      >- fs[state_rel_def] >>
      gvs[CaseEq "option", CaseEq "result", CaseEq "prod", state_rel_def, empty_locals_def]
    ) >>
    Cases_on `x` >> fs[] >>
    Cases_on `r'` >> fs[] >>
    Cases_on `r''` >> fs[]
    >- (
     fs[evaluate_def, lookup_code_def] >>
     Cases_on `s.clock = 0` >> fs[]
     >- fs[state_rel_def] >>
     gvs[CaseEq "option", CaseEq "result", CaseEq "prod", return_in_loop_def, state_rel_def, empty_locals_def] 
    ) >>
    Cases_on `x` >> fs[] >>
    fs[evaluate_def, lookup_code_def, return_in_loop_def] >>
    gvs[AllCaseEqs(), state_rel_def, empty_locals_def]
  ) >>
  every_case_tac >> gs[locals_rel_def]
  >~ [`return_in_loop (Return _)`]
  >- (
    gvs[state_rel_def, empty_locals_def]
  ) >>
  Cases_on `op` >> gs[sh_mem_op_def, sh_mem_store_def, sh_mem_load_def] >>
  qpat_x_assum `_ = (SOME (Return _), _)` mp_tac >> every_case_tac >> gvs[]
QED

Theorem transform_standalone_correct':
  ∀p s r s'.
    evaluate (p, s) = (r, s') ∧
    ¬return_in_loop p ∧
    r ≠ SOME Error ⇒
    ∃r1 s1'.
      evaluate (transform_rec standalone_ret p, s) = (r1, s1') ∧ state_rel s' s1' ∧
      case r of
        | NONE => r1 = NONE ∧ locals_rel s' s1'
        | SOME Error => F
        | SOME TimeOut => r1 = SOME TimeOut
        | SOME Break => r1 = SOME Break ∧ locals_rel s' s1'
        | SOME Continue => r1 = SOME Continue ∧ locals_rel s' s1'
        | SOME (Return retv) => r1 = SOME Break
        | SOME (Exception e) => r1 = SOME (Exception e)
        | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
Proof
  gs[transform_standalone_correct]
QED

Theorem evaluate_while_not_break_continue:
  ∀p e s r s'.
    evaluate (While e p, s) = (r, s') ⇒
    case r of
      | SOME Break => F
      | SOME Continue => F
      | _ => T
Proof
  completeInduct_on `s.clock` >>
  rpt strip_tac >>
  pop_assum mp_tac >>
  fs[Once evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
  disch_tac >> fs[] >>
  Cases_on `w ≠ 0w` >> fs[] >>
  Cases_on `s.clock = 0` >> fs[] >>
  pairarg_tac >> fs[] >>
  `s1.clock < s.clock` by (
    irule LET_TRANS >>
    qrefine `(dec_clock s).clock` >>
    dxrule evaluate_clock >> fs[dec_clock_def]
  ) >>
  last_x_assum $ qspec_then `s1.clock` mp_tac >> fs[] >>
  disch_then $ qspec_then `s1` mp_tac >> fs[] >>
  disch_tac >>
  qpat_x_assum `_ = (r, s')` mp_tac >>
  PURE_ONCE_REWRITE_TAC[evaluate_def] >>
  disch_tac >> gs[CaseEq "option", CaseEq "result", CaseEq "word_lab"] >>
  res_tac >> gvs[]
QED


Theorem res_var_foldl_commutes:
  ∀h vs lc1 lc2.
    ¬MEM h vs ∧
    ALL_DISTINCT vs ⇒
    res_var (FOLDL res_var lc1 (ZIP (vs, MAP (FLOOKUP lc2) vs))) (h, FLOOKUP lc2 h) =
    FOLDL res_var (res_var lc1 (h, FLOOKUP lc2 h)) (ZIP (vs, MAP (FLOOKUP lc2) vs))
Proof
  Induct_on `vs` >> fs[] >>
  rpt strip_tac >>
  imp_res_tac res_var_commutes >> fs[] >>
  pop_assum $ qspecl_then [`lc2`, `lc1`] assume_tac >>
  irule FOLDL_CONG >> fs[] >>
  rename1 `res_var p q = res_var r s` >> fs[]
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

Definition locals_rel_domsub_def:
  locals_rel_domsub s1 s2 x ⇔ s1.locals \\ x SUBMAP s2.locals \\ x
End

Theorem not_var_prog_flookup_eqn:
  ∀p s r s' x.
    evaluate (p, s) = (r, s') ∧
    ¬MEM x (var_prog p) ∧
    (case r of
      | NONE => T
      | SOME Break => T
      | SOME Continue => T
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
    pairarg_tac >> gs[CaseEq "option", CaseEq "result", dec_clock_def]
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
    rpt strip_tac >> gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod"] >>
    Cases_on `s.clock = 0` >> gvs[CaseEq "option", CaseEq "result", CaseEq "prod"] >>
    TRY(Cases_on `v5` >> TRY (Cases_on `x'`) >> gs[MEM, MEM_APPEND, FLOOKUP_UPDATE]) >>
    Cases_on `eid <> eid'` >> gvs[] >>
    Cases_on `v1` >> TRY (Cases_on `x'`) >> gvs[MEM, MEM_APPEND]
  )
  >~ [`evaluate (ShMem _ _ _, _)`]
  >- (
    rpt strip_tac >> gvs[evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    Cases_on `op` >> fs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def, set_var_def]
    >>~ [`addr ∈  s.sh_memaddrs`] >>
    Cases_on `addr ∈ s.sh_memaddrs` >>
    gvs[CaseEq "option", CaseEq "ffi_result", CaseEq "result", FLOOKUP_UPDATE, CaseEq "word_lab"]
  ) >>
  rpt strip_tac >>
  gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "ffi_result", set_globals_def, FLOOKUP_UPDATE] >>
  Cases_on `s.clock = 0` >> gvs[dec_clock_def]
QED


Theorem transform_assign_correct_strong:
  ∀f p s r s' x.
    evaluate (p, s) = (r, s') ∧
    ¬MEM x (var_prog p) ∧
    f = assign_ret x ∧
    ¬return_in_loop p ∧
    (∃z. FLOOKUP s.locals x = SOME z) ∧
    r ≠ SOME Error ⇒
    ∃r1 s1'.
      evaluate (transform_rec f p, s) = (r1, s1') ∧ state_rel s' s1' ∧
      case r of
        | NONE => r1 = NONE ∧ locals_strong_rel s' s1'
        | SOME Break => r1 = SOME Break ∧ locals_strong_rel s' s1'
        | SOME Continue => r1 = SOME Continue ∧ locals_strong_rel s' s1'
        | SOME (Return v) => r1 = SOME Break ∧ FLOOKUP s1'.locals x = SOME v
        | SOME (Exception e) => r1 = SOME (Exception e)
        | SOME TimeOut => r1 = SOME TimeOut
        | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
        | _ => F
Proof
  recInduct transform_rec_ind >> rpt strip_tac >>
  fs[transform_rec_def, assign_ret_def]
  >~ [`evaluate (While _ _, _)`]
  >- (
    fs[return_in_loop_def] >>
    drule not_has_return_not_evaluate_return' >>
    gs[Once evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
    disch_tac >>
    Cases_on `w = 0w` >> gs[]
    >- gvs[state_rel_def, locals_strong_rel_def] >>
    fs[state_rel_def] >>
    Cases_on `s.clock = 0` >> fs[] >>
    pairarg_tac >> fs[] >>
    qpat_x_assum `!_ _ _. evaluate _ ≠ _` $ qspecl_then [`dec_clock s`, `s1`] assume_tac >> fs[] >>
    gvs[CaseEq "option", CaseEq "result"]
    >- (
      drule evaluate_while_not_break_continue >>
      Cases_on `r` >> TRY (Cases_on `x'`) >> gs[locals_strong_rel_def] >>
      `~has_return (While v25 v26)` by gs[has_return_def] >>
      imp_res_tac not_has_return_not_evaluate_return' >> gs[]
    )
    >- gs[locals_strong_rel_def] >>
    `~has_return (While v25 v26)` by gs[has_return_def] >>
     imp_res_tac not_has_return_not_evaluate_return' >>
     Cases_on `r` >> TRY (Cases_on `x'`) >> gs[locals_strong_rel_def]
  )
  >- (
    (* Return *)
    gvs[evaluate_def, CaseEq "option", empty_locals_def, state_rel_def, FLOOKUP_UPDATE]
  )
  >- (
    (* Dec *)
    gs[evaluate_def, return_in_loop_def, var_prog_def, CaseEq "option"] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> gvs[] >>
    last_x_assum drule >>
    disch_then drule >> fs[] >> impl_tac
    >- gvs[FLOOKUP_UPDATE] >>
    disch_tac >> fs[] >>
    conj_tac
    >- (Cases_on `FLOOKUP s.locals v` >> gvs[state_rel_def, res_var_def]) >>
    Cases_on `FLOOKUP s.locals v` >> Cases_on `r` >> TRY (Cases_on `x'`) >> TRY (Cases_on `x''`) >>
    gs[locals_strong_rel_def, res_var_def, FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM]
  )
  >- (
    (* Seq *)
    gs[evaluate_def, return_in_loop_def, var_prog_def] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    Cases_on `res' = NONE` >> fs[]
    >- (
      qpat_x_assum `!_ _ _ _. evaluate (p1, _) = _ ∧ _ ⇒ _` drule >>
      disch_then drule >> fs[] >>
      disch_tac >> fs[] >>
      last_x_assum drule >>
      disch_then drule >> fs[] >>
      impl_tac
      >- (
        qrefine `z` >>
        qpat_x_assum `_ = SOME z` $ fs o single o GSYM >>
        drule not_var_prog_flookup_eqn >> fs[]
      ) >>
      disch_tac >> fs[] >>
      qrefine `r1` >> fs[] >>
      qrefine `s1''` >> fs[] >>
      `s1' = s1` by fs[state_rel_def, locals_strong_rel_def, state_component_equality] >>
      fs[]
    ) >>
    gvs[] >>
    last_x_assum drule >>
    disch_then drule >> fs[] >>
    disch_tac >> fs[] >>
    Cases_on `res = NONE`
    >- (Cases_on `r` >> TRY (Cases_on `x'`) >> fs[]) >>
    fs[]
  )
  >- (
    (* If *)
    gs[evaluate_def, return_in_loop_def, var_prog_def, CaseEq "option", CaseEq "word_lab"] >>
    Cases_on `w ≠ 0w` >> fs[]
  )
  >- (
    (* Call *)
    gs[evaluate_def, return_in_loop_def, var_prog_def, CaseEq "option", CaseEq "prod"] >>
    Cases_on `ctyp` >> fs[]
    >- (
      gs[evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
      pairarg_tac >> gs[CaseEq "prod"] >>
      Cases_on `s.clock = 0` >> fs[]
      >- gvs[state_rel_def] >>
      gvs[CaseEq "prod", CaseEq "option", CaseEq "result", state_rel_def, empty_locals_def, FLOOKUP_UPDATE]
    ) >>
    Cases_on `x'` >> fs[] >>
    Cases_on `r'` >> fs[] >>
    Cases_on `r''` >> fs[]
    >- (
      gs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod"] >>
      Cases_on `s.clock = 0` >> fs[]
      >- gvs[state_rel_def] >>
      gvs[CaseEq "prod", CaseEq "option", CaseEq "result"]
      >>~- ([`state_rel (empty_locals _) _`], gvs[state_rel_def, empty_locals_def]) >>
      last_x_assum drule >>
      disch_then drule >> fs[FLOOKUP_UPDATE]
    ) >>
    Cases_on `x'` >> fs[] >>
    gs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod"] >>
    Cases_on `s.clock = 0` >> fs[]
    >- gvs[state_rel_def] >>
    gvs[CaseEq "prod", CaseEq "option", CaseEq "result"]
    >>~- ([`state_rel (empty_locals _) _`], gvs[state_rel_def, empty_locals_def])
    >- (
      first_x_assum drule >>
      disch_then drule >> fs[FLOOKUP_UPDATE]
    ) >>
    `~MEM x (var_prog r')` by (
      Cases_on `q` >> fs[]
    ) >>
    Cases_on `eid = q''` >> fs[] >>
    gvs[state_rel_def, locals_rel_def]
  )
  >~ [`evaluate (ShMem _ _ _, _)`]
  >- (
    gs[evaluate_def, CaseEq "option", CaseEq "word_lab", var_prog_def] >>
    Cases_on `v37` >> fs[sh_mem_op_def, sh_mem_load_def, sh_mem_store_def]
    >>~ [`addr ∈ s.sh_memaddrs`] >>
    Cases_on `addr ∈ s.sh_memaddrs` >>
    gvs[AllCaseEqs(), set_var_def, locals_strong_rel_def, state_rel_def]
  ) >>
  gvs[evaluate_def, CaseEq "option", CaseEq "word_lab", CaseEq "ffi_result", state_rel_def, locals_strong_rel_def, var_prog_def] >>
  Cases_on `s.clock = 0` >> fs[]
QED

Theorem transform_assign_correct_strong':
  ∀p s r s' x.
    evaluate (p, s) = (r, s') ∧
    ¬MEM x (var_prog p) ∧
    ¬return_in_loop p ∧
    (∃z. FLOOKUP s.locals x = SOME z) ∧
    r ≠ SOME Error ⇒
    ∃r1 s1'.
      evaluate (transform_rec (assign_ret x) p, s) = (r1, s1') ∧ state_rel s' s1' ∧
      case r of
        | NONE => r1 = NONE ∧ locals_strong_rel s' s1'
        | SOME Break => r1 = SOME Break ∧ locals_strong_rel s' s1'
        | SOME Continue => r1 = SOME Continue ∧ locals_strong_rel s' s1'
        | SOME (Return v) => r1 = SOME Break ∧ FLOOKUP s1'.locals x = SOME v
        | SOME (Exception e) => r1 = SOME (Exception e)
        | SOME TimeOut => r1 = SOME TimeOut
        | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
        | _ => F
Proof
  rpt strip_tac >>
  drule transform_assign_correct_strong >>
  disch_then $ qspecl_then [`assign_ret x`, `x`] assume_tac >> gs[] >>
  Cases_on `r` >> TRY (Cases_on `x'`) >> fs[]
QED

Theorem transform_assign_correct_new':
  ∀p s r s' x.
    evaluate (p, s) = (r, s') ∧
    ¬MEM x (var_prog p) ∧
    ¬return_in_loop p ∧
    (∃z. FLOOKUP s.locals x = SOME z) ∧
    r ≠ SOME Error ⇒
    ∃r1 s1'.
      evaluate (transform_rec (assign_ret x) p, s) = (r1, s1') ∧ state_rel s' s1' ∧
      case r of
        | NONE => r1 = NONE ∧ locals_strong_rel s' s1'
        | SOME Break => r1 = SOME Break ∧ locals_strong_rel s' s1'
        | SOME Continue => r1 = SOME Continue ∧ locals_strong_rel s' s1'
        | SOME (Return v) => r1 = SOME Break ∧ FLOOKUP s1'.locals x = SOME v
        | SOME (Exception e) => r1 = SOME (Exception e)
        | SOME TimeOut => r1 = SOME TimeOut
        | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
        | _ => F
Proof
  rpt strip_tac >>
  drule transform_assign_correct_strong >>
  disch_then $ qspecl_then [`assign_ret x`, `x`] assume_tac >> gs[] >>
  Cases_on `r` >> TRY (Cases_on `x'`) >> fs[]
QED

Theorem not_var_prog_not_affect_evaluate:
  ∀p s r s' v val.
    evaluate (p, s) = (r, s') ∧
    ¬MEM v (var_prog p) ∧
    r ≠ SOME Error ⇒
    ∃t'.
      evaluate (p, s with locals := s.locals |+ (v, val)) = (r, t') ∧
      state_rel s' t' ∧
      case r of
        | NONE => t'.locals = s'.locals |+ (v, val)
        | SOME Break => t'.locals = s'.locals |+ (v, val)
        | SOME Continue => t'.locals = s'.locals |+ (v, val)
        | _ => T
Proof
  recInduct evaluate_ind >>
  rpt conj_tac
  >~ [`evaluate (While _ _, _)`]
  >- (
    rpt strip_tac >>
    qpat_x_assum `_ = (r, s')` mp_tac >>
    once_rewrite_tac[evaluate_def] >>
    gs[CaseEq "option", CaseEq "word_lab", var_prog_def] >>
    disch_tac >> fs[] >>
    drule_all update_locals_not_vars_eval_eq >>
    disch_tac >> fs[] >>
    Cases_on `w = 0w` >> fs[]
    >- gvs[state_rel_def] >>
    Cases_on `s.clock = 0` >> fs[]
    >- gvs[state_rel_def, empty_locals_def] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> gvs[] >>
    `∀s lc. dec_clock (s with locals := lc) = dec_clock s with locals := lc` by fs[dec_clock_def, state_component_equality] >> fs[] >>
    qpat_x_assum `!_ _. ~MEM _ _ ∧ _ ≠ SOME Error ⇒ _` drule >> fs[] >>
    Cases_on `res' = SOME Error` >> gs[] >>
    disch_then $ qspec_then `val` mp_tac >> fs[] >>
    disch_tac >> fs[] >>
    Cases_on `res'` >> TRY (Cases_on `x`) >> `(dec_clock s).locals = s.locals` by fs[dec_clock_def] >>
    gvs[] >>
    last_x_assum drule >> fs[] >>
    disch_then $ qspec_then `val` assume_tac >> fs[] >>
    `s1 = s1' with locals := s1'.locals |+ (v, val)` by fs[state_component_equality, state_rel_def] >>
    gvs[]
  )
  >~ [`evaluate (Dec _ _ _, _)`]
  >- (
    rpt strip_tac >>
    gs[evaluate_def, var_prog_def, CaseEq "option"] >>
    drule_all update_locals_not_vars_eval_eq >> fs[] >>
    disch_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    last_x_assum drule >>
    rev_drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] FUPDATE_COMMUTES >>
    disch_then $ qspec_then `s.locals` mp_tac >>
    disch_then $ fs o single >>
    disch_then $ qspec_then `val` assume_tac >> gvs[] >>
    conj_tac
    >- (
      Cases_on `FLOOKUP s.locals v` >> Cases_on `FLOOKUP (s.locals |+ (v', val)) v` >>
      gvs[state_rel_def, res_var_def]
    ) >>
    Cases_on `r` >> TRY (Cases_on `x`) >> fs[FLOOKUP_UPDATE] >>
    Cases_on `FLOOKUP s.locals v` >> fs[res_var_def] >>
    drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] DOMSUB_FUPDATE_NEQ >>
    disch_tac >>
    drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] FUPDATE_COMMUTES >>
    disch_tac >>
    gvs[]
  )
  >~ [`evaluate (Seq _ _, _)`]
  >- (
    rpt strip_tac >> gs[evaluate_def, var_prog_def] >>
    pairarg_tac >> fs[] >>
    pairarg_tac >> fs[] >>
    qpat_x_assum `!_ _. ¬MEM _ _ ∧ _ ⇒ _` drule >>
    Cases_on `res' = SOME Error` >> fs[] >>
    disch_then $ qspec_then `val` assume_tac >> fs[] >>
    Cases_on `res' = NONE` >> fs[]
    >- (
      last_x_assum drule >>
      disch_then $ qspec_then `val` assume_tac >> gvs[] >>
      `s1 = s1' with locals := s1'.locals |+ (v, val)` by gvs[state_rel_def, state_component_equality] >> fs[]
    ) >>
    gvs[]
  )
  >~ [`evaluate (If _ _ _, _)`]
  >- (
    rpt strip_tac >> gs[evaluate_def, var_prog_def, CaseEq "option", CaseEq "word_lab"] >>
    drule_all update_locals_not_vars_eval_eq >>
    disch_tac >> fs[] >>
    Cases_on `w = 0w` >> fs[]
  )
  >~ [`evaluate (Call _ _ _, _)`]
  >- (
    rpt strip_tac >> gs[evaluate_def, var_prog_def, CaseEq "option", CaseEq "word_lab"] >>
    `OPT_MMAP (eval (s with locals := s.locals |+ (v, val))) argexps = SOME args` by (
      qpat_x_assum `_ = SOME args` $ fs o single o GSYM >>
      irule OPT_MMAP_CONG >> fs[] >>
      rpt strip_tac >>
      fs[MEM_FLAT, MEM_MAP] >>
      qpat_x_assum `!_. (!_. _) ∨ ¬_` $ qspec_then `var_cexp x` assume_tac >> fs[] >>
      TRY (pop_assum $ qspec_then `x` assume_tac >> fs[]) >>
      drule update_locals_not_vars_eval_eq' >> fs[]
    ) >>
    gs[CaseEq "prod"] >>
    Cases_on `s.clock = 0` >> fs[]
    >- gvs[state_rel_def, empty_locals_def] >>
    `dec_clock (s with locals := s.locals |+ (v, val)) with locals := newlocals = dec_clock s with locals := newlocals` by gs[dec_clock_def, state_component_equality] >> fs[] >>
    gs[CaseEq "option", CaseEq "result", CaseEq "prod"]
    >- fs[state_rel_def] >> gvs[]
    >>~- ([`state_rel (empty_locals _) _`], gvs[state_rel_def, empty_locals_def]) >>
    `~MEM v (var_prog p)` by (
      TRY (Cases_on `v5` >> TRY (Cases_on `x`) >> fs[]) >>
      TRY (Cases_on `v1` >> TRY (Cases_on `x`) >> fs[])
    )
    >- (
      last_x_assum drule >>
      disch_then $ qspec_then `val` assume_tac >> fs[]
    )
    >- (
      last_x_assum drule >>
      disch_then $ qspec_then `val` assume_tac >> fs[] >>
      `v ≠ rt` by (
        Cases_on `v5` >> TRY (Cases_on `x`) >> fs[]
      ) >> fs[FLOOKUP_UPDATE] >>
      drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] FUPDATE_COMMUTES >> fs[]
    ) >>
    Cases_on `eid = eid'` >> gvs[state_rel_def]
  )
  >~ [`evaluate (ShMem _ _ _, _)`]
  >- (
    rpt strip_tac >> gs[evaluate_def, CaseEq "option", CaseEq "word_lab", var_prog_def] >>
    drule_all update_locals_not_vars_eval_eq >>
    disch_tac >> fs[FLOOKUP_UPDATE] >>
    Cases_on `op` >> fs[sh_mem_op_def, sh_mem_store_def, sh_mem_load_def, set_var_def]
    >>~ [`addr ∈ s.sh_memaddrs`] >>
    drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] FUPDATE_COMMUTES >>
    disch_then assume_tac >> fs[] >>
    Cases_on `addr ∈ s.sh_memaddrs` >> gvs[AllCaseEqs(), state_rel_def, empty_locals_def, FLOOKUP_UPDATE] >>
    qabbrev_tac `z = Word (word_of_bytes F 0w new_bytes)` >> fs[]
  ) >>
  gs[evaluate_def, var_prog_def, CaseEq "option", CaseEq "word_lab", FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  TRY (imp_res_tac update_locals_not_vars_eval_eq >> gvs[state_rel_def, set_globals_def, empty_locals_def, CaseEq "ffi_result"]) >>
  res_tac
  >- (
    drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] FUPDATE_COMMUTES >> fs[]
  ) >>
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

Theorem nested_decs_evaluate_sublocals:
  !vs es p s r s' vals t.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH es ∧
    ALL_DISTINCT vs /\
    (!v. MEM v vs ⇒ !e. MEM e es ⇒ ¬MEM v (var_cexp e)) ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    t SUBMAP s.locals ∧
    r ≠ SOME Error ==>
    ∃t'.
      evaluate (nested_decs vs es p, s) = (r, t') ∧ state_rel s' t'
Proof
  rpt strip_tac >>
  drule evaluate_state_locals_rel >> fs[] >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      fs[locals_rel_def] >>
      irule SUBMAP_mono_FUPDATE_LIST >>
      irule $ iffRL SUBMAP_FLOOKUP_EQN >> fs[FLOOKUP_SIMP] >>
      rpt strip_tac >>
      drule $ iffLR SUBMAP_FLOOKUP_EQN >> fs[]
    ) >>
    gvs[state_rel_def]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos last) evaluate_nested_decs_locals_nested_res_var >>
  disch_then imp_res_tac >> gs[state_rel_def]
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
      | SOME Break => T
      | SOME Continue => T
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



Theorem nested_decs_evaluate_sublocals_strong_eq:
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
      | SOME Break => T
      | SOME Continue => T
      | _ => F) = T ==>
    ∃t'.
      evaluate (nested_decs vs es p, s) = (r, t') ∧ state_rel s' t' ∧
      (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t))
Proof
  rpt strip_tac >>
  drule_all nested_decs_evaluate_sublocals_strong >>
  disch_tac >> fs[] >>
  drule evaluate_locals_same_fdom >> impl_tac
  >- fs[] >>
  disch_tac >>
  irule $ iffRL EQ_FDOM_SUBMAP >>
  fs[FDIFF_def, FDOM_DRESTRICT, SUBMAP_FLOOKUP_EQN, FLOOKUP_SIMP]
QED

Theorem nested_decs_evaluate_sublocals_full:
  !vs es p s r s' vals t.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH es ∧
    ALL_DISTINCT vs /\
    (!v. MEM v vs ⇒ !e. MEM e es ⇒ ¬MEM v (var_cexp e)) ∧
    (!v. MEM v vs ==> v ∉ FDOM t) ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    t SUBMAP s.locals ∧
    r ≠ SOME Error ==>
    ∃t'.
      evaluate (nested_decs vs es p, s) = (r, t') ∧ state_rel s' t' ∧
      case r of
        | NONE => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t))
        | SOME Break => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t))
        | SOME Continue => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t))
        | SOME Error => F
        | _ => T
Proof
  rpt strip_tac >>
  drule_all nested_decs_evaluate_sublocals >>
  disch_tac >> fs[] >>
  drule nested_decs_evaluate_sublocals_strong_eq >> fs[] >>
  rpt (disch_then drule) >> fs[] >>
  disch_tac >>
  Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
QED



Theorem all_distinct_tmp_vars:
  ∀vs es.
    ALL_DISTINCT (GENLIST (λx. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs))
Proof
  simp[genlist_all_distinct]
QED

Theorem all_distinct_tmp_vars':
  ∀vs es.
    ALL_DISTINCT (GENLIST (λx. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vs))
Proof
  assume_tac all_distinct_tmp_vars >> rpt gen_tac >> rewrite_tac[ADD_ASSOC] >> simp[]
QED


Theorem tmp_vars_distinct:
  ∀vs es tmp_vars.
    tmp_vars = GENLIST (λx. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    (∀v. MEM v vs ⇒ ¬MEM v tmp_vars) ∧
    (∀e. MEM e es ⇒ (∀v. MEM v (var_cexp e) ⇒ ¬MEM v tmp_vars))
Proof
  rpt gen_tac >>
  strip_tac >>
  conj_tac
  >- (
    gen_tac >> strip_tac >> asm_rewrite_tac[] >>
    irule genlist_not_in >>
    drule MAX_LIST_PROPERTY >> disch_tac >> fs[]
  ) >>
  ntac 2 (gen_tac >> strip_tac) >> asm_rewrite_tac[] >>
  irule genlist_not_in >>
  irule LESS_EQ_TRANS >>
  qrefine `MAX_LIST (FLAT (MAP var_cexp es))` >> fs[] >>
  irule MAX_LIST_PROPERTY >>
  fs[MEM_FLAT] >>
  qrefine `var_cexp e` >> fs[MEM_MAP] >>
  qrefine `e` >> fs[]
QED

Theorem tmp_vars_not_mem_vs:
  ∀vs es tmp_vars.
    tmp_vars = GENLIST (λx. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ==>
    (∀v. MEM v vs ⇒ ¬MEM v tmp_vars)
Proof
  rpt gen_tac >> strip_tac >>
  drule tmp_vars_distinct >>
  disch_tac >> fs[]
QED

Theorem tmp_vars_not_var_cexp:
  ∀vs es tmp_vars.
    tmp_vars = GENLIST (λx. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ==>
    (∀e. MEM e es ⇒ (∀v. MEM v (var_cexp e) ⇒ ¬MEM v tmp_vars))
Proof
  rpt gen_tac >> strip_tac >>
  drule tmp_vars_distinct >>
  disch_tac >> fs[]
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
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t'
Proof
  rpt strip_tac >>
  `ALL_DISTINCT tmp_vars` by metis_tac[all_distinct_tmp_vars] >>
  drule tmp_vars_not_mem_vs >>
  disch_tac >>
  drule tmp_vars_not_var_cexp >>
  disch_tac >>
  drule evaluate_state_locals_rel >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (vs, vals) |++ ZIP (tmp_vars, vals) ` mp_tac >> impl_tac
  >- (
    conj_tac
    >- fs[] >>
    conj_tac
    >- (
      gs[locals_rel_def] >>
      qabbrev_tac `arg_swap = GENLIST (\x. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
      irule SUBMAP_DIFF_LIST >>
      conj_tac
      >- (
        simp[GSYM flookup_thm] >>
        rpt strip_tac >>
        `∀v. MEM v arg_swap ⇒ ¬MEM v vs` by (
          rpt strip_tac >>
          qpat_x_assum `!_. MEM _ vs ⇒ _` drule >> fs[]
        ) >>
        drule flookup_fupdate_zip_not_mem >>
        pop_assum drule >> disch_tac >>
        disch_then drule >>
        disch_then $ qspec_then `t` assume_tac >> fs[] >>
        qpat_x_assum `!_. _ ∨ _ ⇒ _ ∉ _` $ qspec_then `v` assume_tac >> gs[flookup_thm]
      ) >>
      gvs[] >>
      qunabbrev_tac `arg_swap` >> fs[LENGTH_GENLIST]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  qabbrev_tac `arg_swap = GENLIST (\x. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
  drule evaluate_state_locals_rel >> fs[] >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (vs, vals) |++ ZIP (tmp_vars, vals)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      simp[locals_rel_def] >>
      irule $ iffRL SUBMAP_FLOOKUP_EQN >>
      rpt strip_tac >>
      Cases_on `MEM x arg_swap`
      >- (
        imp_res_tac MEM_EL >> gvs[] >>
        drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] update_eq_zip_flookup >>
        disch_then $ drule_at (Pos last) >>
        `LENGTH arg_swap = LENGTH vals` by (
          qunabbrev_tac `arg_swap` >> gs[LENGTH_GENLIST]
        ) >>
        disch_then drule >>
        disch_tac >>
        first_assum $ qspec_then `t |++ ZIP (vs, vals)` assume_tac >>
        first_x_assum $ qspec_then `s.locals |++ ZIP (vs, vals)` assume_tac >>
        gvs[]
      ) >>
      `LENGTH arg_swap = LENGTH vals` by (
        qunabbrev_tac `arg_swap` >> gs[LENGTH_GENLIST]
      ) >>
      drule flookup_fupdate_zip_not_mem >>
      disch_then drule >>
      disch_tac >>
      first_assum $ qspec_then `t |++ ZIP (vs, vals)` assume_tac >>
      first_assum $ qspec_then `s.locals |++ ZIP (vs, vals)` assume_tac >>
      gvs[] >>
      Cases_on `MEM x vs`
      >- (
        rev_drule $ INST_TYPE [``:'a`` |-> ``:num``, ``:'b`` |-> ``:'a word_lab``] update_eq_zip_flookup >>
        disch_then rev_drule >>
        drule $ iffLR MEM_EL >>
        disch_tac >> rfs[] >>
        disch_then drule >>
        disch_then $ qspec_then `t` assume_tac >> gvs[]
      ) >>
      rev_drule flookup_fupdate_zip_not_mem >>
      disch_then drule >>
      disch_tac >>
      first_assum $ qspec_then `t` assume_tac >>
      first_assum $ qspec_then `s.locals` assume_tac >>
      gvs[] >>
      drule $ iffLR SUBMAP_FLOOKUP_EQN >>
      disch_then imp_res_tac
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  `∀l. l |++ ZIP (vs, vals) |++ ZIP (arg_swap, vals) = l |++ ZIP (arg_swap, vals) |++ ZIP (vs, vals)` by (
    irule FUPDATE_LIST_APPEND_COMMUTES >>
    `LENGTH arg_swap = LENGTH vals` by (
      qunabbrev_tac `arg_swap` >> fs[LENGTH_GENLIST]
    ) >>
    imp_res_tac MAP_ZIP >> fs[IN_DISJOINT] >>
    rpt strip_tac >>
    spose_not_then assume_tac >> gs[]
  ) >>
  first_assum $ qspec_then `s.locals` assume_tac >> fs[] >>
  rev_drule_at (Pos $ el 3) nested_decs_evaluate >>
  disch_then $ qspecl_then [`MAP Var arg_swap`, `p`, `s with locals := s.locals |++ ZIP (arg_swap, vals)`, `r`, `t''`, `vals`] mp_tac >>
  impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> fs[] >>
      qunabbrev_tac `arg_swap` >> fs[LENGTH_GENLIST]
    )
    >- (
      simp[LENGTH_MAP] >>
      qunabbrev_tac `arg_swap` >> fs[LENGTH_GENLIST]
    )
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
      imp_res_tac opt_mmap_length_eq >>
      qunabbrev_tac `arg_swap` >> gvs[LENGTH_GENLIST]
    ) >>
    rpt strip_tac >>
    qpat_x_assum `!_ _. MEM _ _ ∧ MEM _ _ ⇒ ¬_` imp_res_tac
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
      | SOME Break => T
      | SOME Continue => T
      | _ => F) = T ∧
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
Proof
  rpt strip_tac >>
  `ALL_DISTINCT tmp_vars` by metis_tac[all_distinct_tmp_vars] >>
  drule tmp_vars_not_mem_vs >>
  disch_tac >>
  drule tmp_vars_not_var_cexp >>
  disch_tac >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (tmp_vars, vals) |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      gs[CaseEq "option", CaseEq "result"]
    )
    >- (
      simp[locals_rel_def, SUBMAP_FLOOKUP_EQN] >>
      gs[] >>
      qabbrev_tac `arg_swap = GENLIST (λx. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
      rpt strip_tac >>
      Cases_on `MEM x vs`
      >- (
        pop_assum $ assume_tac o SRULE [MEM_EL] >>
        fs[] >>
        drule_all update_eq_zip_flookup >>
        disch_tac >>
        first_assum $ qspec_then `t` assume_tac >>
        first_assum $ qspec_then `t |++ ZIP (arg_swap, vals)` assume_tac >> gvs[]
      ) >>
      drule_all flookup_fupdate_zip_not_mem >>
      disch_tac >>
      first_assum $ qspec_then `t` assume_tac >>
      first_assum $ qspec_then `t |++ ZIP (arg_swap, vals)` assume_tac >>
      gs[] >>
      qpat_assum `FLOOKUP _ _ = SOME _` $ assume_tac o SRULE [flookup_thm] >> fs[] >>
      qpat_x_assum `!_. MEM _ _ ∨ MEM _ _ ⇒ _ ∉ FDOM _` $ assume_tac o SRULE [Once MONO_NOT_EQ] >>
      pop_assum imp_res_tac >>
      qpat_x_assum `FLOOKUP _ _ = SOME _` $ rewrite_tac o single o GSYM >>
      irule flookup_fupdate_zip_not_mem >> simp[] >>
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  qabbrev_tac `arg_swap = GENLIST (λx. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
  rev_drule_at (Pos $ el 3) evaluate_nested_decs_locals_nested_res_var >>
  disch_then $ qspecl_then [`p`, `s with locals := t |++ ZIP (arg_swap, vals)`, `r`, `t'`, `MAP Var arg_swap`, `vals`] mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> simp[] >>
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    )
    >- (
      simp[LENGTH_MAP] >>
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    )
    >- (
      rpt strip_tac >>
      qpat_x_assum `!_. MEM _ _ ⇒ ¬MEM _ _` imp_res_tac >>
      gvs[MEM_MAP, var_cexp_def]
    ) >>
    simp[state_component_equality]
  ) >>
  disch_tac >> fs[] >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (arg_swap, vals)` mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    )
    >- (
      simp[locals_rel_def, SUBMAP_FLOOKUP_EQN] >>
      rpt strip_tac >>
      Cases_on `MEM x arg_swap`
      >- (
        pop_assum $ assume_tac o SRULE [MEM_EL] >> fs[] >>
        `LENGTH arg_swap = LENGTH vals` by simp[Abbr `arg_swap`, LENGTH_GENLIST] >>
        drule_all update_eq_zip_flookup >>
        disch_tac >>
        first_assum $ qspec_then `t` assume_tac >>
        first_assum $ qspec_then `s.locals` assume_tac >> gvs[]
      ) >>
      `LENGTH arg_swap = LENGTH vals` by simp[Abbr `arg_swap`, LENGTH_GENLIST] >>
      drule_all flookup_fupdate_zip_not_mem >>
      disch_tac >>
      first_assum $ qspec_then `t` assume_tac >>
      first_assum $ qspec_then `s.locals` assume_tac >>
      fs[SUBMAP_FLOOKUP_EQN]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos $ el 3) evaluate_nested_decs_locals_nested_res_var >>
  disch_then $ qspecl_then [`nested_decs vs (MAP Var arg_swap) p`, `s`, `r`, `t'''`, `es`, `vals`] mp_tac >> gs[] >> impl_tac
  >- (
    conj_tac
    >- (
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    ) >>
    rpt strip_tac >>
    qpat_x_assum `!_ _. MEM _ _ ∧ MEM _ _ ⇒ ¬MEM _ _` imp_res_tac
  ) >>
  disch_tac >> fs[] >>
(* cp *)
  Cases_on `r` >> TRY (Cases_on `x`) >> gs[]
  >>~- ([`_`],
    conj_tac
    >- (
      gs[state_rel_def]
    ) >>
    gvs[locals_rel_def, locals_ext_rel_def] >>
    `distinct_lists arg_swap vs` by (
      simp[distinct_lists_def, EVERY_MEM] >>
      rpt strip_tac >>
      qpat_x_assum `!_. MEM _ _ ⇒ ¬MEM _ _` imp_res_tac
    ) >>
    `LENGTH arg_swap = LENGTH vals` by simp[Abbr `arg_swap`, LENGTH_GENLIST] >>
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
        qpat_x_assum `!_. MEM _ _ => ¬MEM _ _` imp_res_tac >>
        conj_tac
        >- (
          qpat_x_assum `!_. MEM _ _ ∨ MEM _ _ ⇒ _ ∉ FDOM _` $ qspec_then `x` assume_tac >> rfs[GSYM flookup_thm] >>
          pop_assum $ rewrite_tac o single o GSYM >>
          irule flookup_fupdate_zip_not_mem >> simp[]
        ) >>
        qpat_x_assum `FLOOKUP _.locals _ = SOME _` $ rewrite_tac o single o GSYM >>
        irule flookup_fupdate_zip_not_mem >> simp[]
      ) >>
      simp[FLOOKUP_FDIFF] >> disch_tac >> fs[] >>
      qpat_x_assum `!_. MEM _ _ ⇒ ¬MEM _ _` imp_res_tac >>
      imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_distinct_zip_eq >>
      pop_assum $ qspec_then `MAP (FLOOKUP s.locals) arg_swap` mp_tac >> simp[LENGTH_MAP]
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
    Cases_on `¬MEM x arg_swap`
    >- (
      imp_res_tac $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``]  flookup_res_var_distinct_zip_eq >>
      pop_assum kall_tac >>
      pop_assum $ qspec_then `MAP (FLOOKUP s.locals) arg_swap` mp_tac >> simp[LENGTH_MAP]
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
QED

Theorem fdiff_update_list_disjoint:
  ∀t a b ls ks.
  (!v. MEM v b ⇒ ¬MEM v a) ∧
  (!v. MEM v b ∨ MEM v a ⇒ v ∉ FDOM t) ∧
  (LENGTH a = LENGTH ls) ∧ ALL_DISTINCT a ∧
  (LENGTH b = LENGTH ks) ∧ ALL_DISTINCT b
  ==>
  FDIFF (t |++ ZIP (a, ls) |++ ZIP (b, ks)) (FDOM (t |++ ZIP (b, ks))) = FEMPTY |++ ZIP (a, ls)
Proof
  rpt strip_tac >>
  simp[fmap_eq_flookup] >>
  strip_tac >>
  Cases_on `MEM x b`
  >- (
    res_tac >>
    drule not_mem_fst_zip_flookup_empty >> fs[] >>
    disch_then $ qspec_then `ls` assume_tac >> fs[FLOOKUP_FDIFF, FDOM_FUPDATE_LIST, MAP_ZIP]
  ) >>
  Cases_on `MEM x a`
  >- (
    first_assum $ assume_tac o SRULE [MEM_EL] >> fs[update_eq_zip_flookup] >>
    simp[FLOOKUP_FDIFF, FDOM_FUPDATE_LIST] >>
    first_x_assum $ qspec_then `x` assume_tac >> gvs[MAP_ZIP] >>
    drule flookup_fupdate_zip_not_mem >>
    disch_then drule >>
    disch_then $ qspec_then `t |++ ZIP (a, ls)` assume_tac >> fs[update_eq_zip_flookup]
  ) >>
  simp[FLOOKUP_FDIFF, FDOM_FUPDATE_LIST, MAP_ZIP] >>
  rev_drule flookup_fupdate_zip_not_mem >>
  disch_then drule >>
  disch_then $ qspec_then `FEMPTY` assume_tac >> fs[] >>
  Cases_on `x ∈ FDOM t` >> fs[] >>
  drule flookup_fupdate_zip_not_mem >>
  disch_then drule >>
  disch_then $ qspec_then `t |++ ZIP (a, ls)` assume_tac >> fs[] >>
  rev_drule flookup_fupdate_zip_not_mem >>
  disch_then drule >>
  disch_then $ qspec_then `t` assume_tac >> fs[] >>
  simp[flookup_thm]
QED

Theorem general_simulate_arg_load_preserve_locals_strong:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    (case r of
      | NONE => T
      | SOME Break => T
      | SOME Continue => T
      | _ => F) = T ∧
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) = t'.locals
Proof
  rpt strip_tac >>
  `ALL_DISTINCT tmp_vars` by metis_tac[all_distinct_tmp_vars] >>
  drule tmp_vars_not_mem_vs >>
  disch_tac >>
  drule tmp_vars_not_var_cexp >>
  disch_tac >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (tmp_vars, vals) |++ ZIP (vs, vals)` mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      gs[CaseEq "option", CaseEq "result"]
    )
    >- (
      simp[locals_rel_def, SUBMAP_FLOOKUP_EQN] >>
      gs[] >>
      qabbrev_tac `arg_swap = GENLIST (λx. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
      rpt strip_tac >>
      Cases_on `MEM x vs`
      >- (
        pop_assum $ assume_tac o SRULE [MEM_EL] >>
        fs[] >>
        drule_all update_eq_zip_flookup >>
        disch_tac >>
        first_assum $ qspec_then `t` assume_tac >>
        first_assum $ qspec_then `t |++ ZIP (arg_swap, vals)` assume_tac >> gvs[]
      ) >>
      drule_all flookup_fupdate_zip_not_mem >>
      disch_tac >>
      first_assum $ qspec_then `t` assume_tac >>
      first_assum $ qspec_then `t |++ ZIP (arg_swap, vals)` assume_tac >>
      gs[] >>
      qpat_assum `FLOOKUP _ _ = SOME _` $ assume_tac o SRULE [flookup_thm] >> fs[] >>
      qpat_x_assum `!_. MEM _ _ ∨ MEM _ _ ⇒ _ ∉ FDOM _` $ assume_tac o SRULE [Once MONO_NOT_EQ] >>
      pop_assum imp_res_tac >>
      qpat_x_assum `FLOOKUP _ _ = SOME _` $ rewrite_tac o single o GSYM >>
      irule flookup_fupdate_zip_not_mem >> simp[] >>
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  qabbrev_tac `arg_swap = GENLIST (λx. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
  rev_drule_at (Pos $ el 3) evaluate_nested_decs_locals_nested_res_var >>
  disch_then $ qspecl_then [`p`, `s with locals := t |++ ZIP (arg_swap, vals)`, `r`, `t'`, `MAP Var arg_swap`, `vals`] mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> simp[] >>
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    )
    >- (
      simp[LENGTH_MAP] >>
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    )
    >- (
      rpt strip_tac >>
      qpat_x_assum `!_. MEM _ _ ⇒ ¬MEM _ _` imp_res_tac >>
      gvs[MEM_MAP, var_cexp_def]
    ) >>
    simp[state_component_equality]
  ) >>
  disch_tac >> fs[] >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `s with locals := s.locals |++ ZIP (arg_swap, vals)` mp_tac >> impl_tac
  >- (
    rpt conj_tac
    >- (
      Cases_on `r` >> TRY (Cases_on `x`) >> fs[]
    )
    >- (
      simp[locals_rel_def, SUBMAP_FLOOKUP_EQN] >>
      rpt strip_tac >>
      Cases_on `MEM x arg_swap`
      >- (
        pop_assum $ assume_tac o SRULE [MEM_EL] >> fs[] >>
        `LENGTH arg_swap = LENGTH vals` by simp[Abbr `arg_swap`, LENGTH_GENLIST] >>
        drule_all update_eq_zip_flookup >>
        disch_tac >>
        first_assum $ qspec_then `t` assume_tac >>
        first_assum $ qspec_then `s.locals` assume_tac >> gvs[]
      ) >>
      `LENGTH arg_swap = LENGTH vals` by simp[Abbr `arg_swap`, LENGTH_GENLIST] >>
      drule_all flookup_fupdate_zip_not_mem >>
      disch_tac >>
      first_assum $ qspec_then `t` assume_tac >>
      first_assum $ qspec_then `s.locals` assume_tac >>
      fs[SUBMAP_FLOOKUP_EQN]
    ) >>
    gs[state_rel_def]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos $ el 3) evaluate_nested_decs_locals_nested_res_var >>
  disch_then $ qspecl_then [`nested_decs vs (MAP Var arg_swap) p`, `s`, `r`, `t'''`, `es`, `vals`] mp_tac >> gs[] >> impl_tac
  >- (
    conj_tac
    >- (
      imp_res_tac opt_mmap_length_eq >>
      simp[Abbr `arg_swap`, LENGTH_GENLIST]
    ) >>
    rpt strip_tac >>
    qpat_x_assum `!_ _. MEM _ _ ∧ MEM _ _ ⇒ ¬MEM _ _` imp_res_tac
  ) >>
  disch_tac >> fs[] >>
  drule $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] fdiff_update_list_disjoint >>
  disch_then $ qspec_then `t` mp_tac >> fs[] >>
  disch_then $ qspecl_then [`vals`, `vals`] mp_tac >> impl_tac
  >- (
    conj_tac
    >- fs[] >>
    fs[Abbr `arg_swap`, LENGTH_GENLIST]
  )  >>
  disch_tac >> fs[locals_ext_rel_def] >>
  conj_tac
  >- gvs[state_rel_def] >>
  drule general_simulate_arg_load_preserve_locals >>
  disch_then drule >> simp[] >>
  disch_then drule >>
  disch_then rev_drule >>
  impl_tac
  >- (gs[] >> gs[]) >>
  disch_tac >> fs[] >>
  simp[fmap_eq_flookup] >>
  strip_tac >>
  Cases_on `r` >> TRY (Cases_on `x'`) >> fs[] >>
  cheat
QED

(* Need this *)
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
       | SOME Break => T
       | SOME Continue => T
       | _ => F) = T ∧
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
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
  `ALL_DISTINCT tmp_vars` by (
    metis_tac[all_distinct_tmp_vars]
  )>>
  drule tmp_vars_not_mem_vs >>
  disch_tac >>
  drule tmp_vars_not_var_cexp >>
  disch_tac >>
  drule evaluate_state_locals_rel_strong >> gs[] >>
  qabbrev_tac `arg_swap = GENLIST (λx. MAX_LIST vs + (MAX_LIST (FLAT (MAP var_cexp es)) + SUC x)) (LENGTH vals)` >>
  disch_then $ qspec_then `s with locals := t |++ ZIP (vs, vals) |++ ZIP (tmp_vars, vals)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      simp[locals_rel_def] >>
      irule SUBMAP_DIFF_LIST >> simp[] >>
      conj_tac
      >- (
        gen_tac >> strip_tac >>
        qpat_x_assum `!_. MEM _ _ ∨ MEM _ _ ⇒ _ ∉ _` $ qspec_then `v` assume_tac >> gs[] >>
        fs[GSYM flookup_thm] >>
        pop_assum $ rewrite_tac o single o GSYM >>
        irule flookup_fupdate_zip_not_mem >> simp[] >>
        assume_tac tmp_vars_not_mem_vs >>
        pop_assum $ qspecl_then [`vs`, `es`, `arg_swap`] mp_tac >> impl_tac
        >- (
          qunabbrev_tac `arg_swap` >> simp[]
        ) >>
        disch_tac >>
        spose_not_then assume_tac >>
        qpat_x_assum `!_. MEM _ _ ⇒ ¬MEM _ _` imp_res_tac
      ) >>
      qunabbrev_tac `arg_swap` >> simp[LENGTH_GENLIST]
    ) >>
    gvs[state_rel_def]
  ) >>
  disch_tac >> gs[] >>
  `t |++ ZIP (vs, vals) |++ ZIP (arg_swap, vals) = t |++ ZIP (arg_swap, vals) |++ ZIP (vs, vals)` by (
    irule FUPDATE_LIST_APPEND_COMMUTES >>
    `LENGTH arg_swap = LENGTH vals` by (qunabbrev_tac `arg_swap` >> fs[LENGTH_GENLIST]) >>
    imp_res_tac MAP_ZIP >> simp[DISJOINT_ALT]
  ) >>
  fs[] >>
  rev_drule_at (Pos $ el 3) nested_decs_evaluate_sublocals_strong >>
  disch_then $ qspecl_then [`MAP Var arg_swap`, `p`, `s with locals := t |++ ZIP (arg_swap, vals)`, `r`, `s'`, `vals`, `t`] mp_tac >> simp[] >> impl_tac
  >- (
    rpt conj_tac
    >- (
      simp[GSYM lookup_locals_eq_map_vars] >>
      irule opt_mmap_some_eq_zip_flookup >> simp[] >>
      qunabbrev_tac `arg_swap` >> simp[LENGTH_GENLIST]
    )
    >- (
      qunabbrev_tac `arg_swap` >> simp[LENGTH_GENLIST]
    )
    >- (
      rpt strip_tac >>
      gvs[MEM_MAP, var_cexp_def]
    ) >>
    simp[SUBMAP_FLOOKUP_EQN] >>
    rpt strip_tac >>
    first_assum $ rewrite_tac o single o GSYM >>
    irule flookup_fupdate_zip_not_mem >>
    conj_tac
    >- (
      spose_not_then assume_tac >>
      res_tac >> fs[GSYM flookup_thm]
    ) >>
    qunabbrev_tac `arg_swap` >> simp[LENGTH_GENLIST]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos $ el 6) nested_decs_evaluate_sublocals_strong >>
  disch_then $ qspec_then `es` mp_tac >> simp[] >> impl_tac
  >- (
    conj_tac
    >- (
      imp_res_tac opt_mmap_length_eq >>
      qunabbrev_tac `arg_swap` >> simp[LENGTH_GENLIST]
    ) >>
    rpt strip_tac >>
    qpat_x_assum `!_ _. MEM _ _ ∧ MEM _ _ ⇒ ¬_` imp_res_tac
  ) >>
  disch_tac >> fs[]
QED


(* Need this *)
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
       | SOME Break => T
       | SOME Continue => T
       | _ => F) = T ∧
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
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

(* Need this *)
Theorem general_simulate_arg_load_strong_all:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    ∃t'.
      evaluate
        (nested_decs tmp_vars es (nested_decs vs (MAP Var tmp_vars) p), s) = (r, t') ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Break => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Continue => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
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


Theorem arg_load_correct:
  ∀s es (vals:('a word_lab) list) vs t p r s' tmp_vars.
    OPT_MMAP (eval s) es = SOME vals ∧
    LENGTH vs = LENGTH vals ∧
    ALL_DISTINCT vs ∧
    t SUBMAP s.locals ∧
    evaluate (p, s with locals := t |++ ZIP (vs, vals)) = (r, s') ∧
    (∀v. MEM v vs ∨ MEM v tmp_vars ⇒  v ∉ FDOM t) ∧
    r ≠ SOME Error ∧
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    ∃t'.
      evaluate
        (arg_load tmp_vars es vs p, s) = (r, t') ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Break => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Continue => (FDIFF s.locals (FDOM t)) SUBMAP t'.locals ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
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
    tmp_vars = GENLIST (\x. MAX_LIST vs + MAX_LIST (FLAT (MAP var_cexp es)) + SUC x) (LENGTH vs) ⇒
    ∃t'.
      evaluate
        (arg_load tmp_vars es vs p, s) = (r, t') ∧
     state_rel s' t' ∧
     (case r of
       | NONE => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t)) ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Break => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t)) ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
       | SOME Continue => (FDIFF s.locals (FDOM t)) = (FDIFF t'.locals (FDOM t)) ∧ FOLDL res_var s'.locals (ZIP (vs, MAP (FLOOKUP s.locals) vs)) SUBMAP t'.locals
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

Definition code_rel_def:
  code_rel inl_fs s t ⇔
   FDOM s.code = FDOM t.code ∧
   ∀n vs p.
     FLOOKUP s.code n = SOME (vs, p) ⇒
     FLOOKUP t.code n = SOME (vs, inline_prog (inl_fs \\ n) p)
End

Theorem eval_code_state_correct:
  ∀s e val s1 inl_fs.
    eval s e = SOME val ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    code_rel inl_fs s s1 ⇒
    eval s1 e = SOME val
Proof
  recInduct eval_ind >> rpt strip_tac >>
  gvs[eval_def, CaseEq "option", CaseEq "word_lab"]
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

Theorem opt_mmap_eval_code_state_correct:
  ∀s es vals s1 inl_fs.
    OPT_MMAP (eval s) es = SOME vals ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    code_rel inl_fs s s1 ⇒
    OPT_MMAP (eval s1) es = SOME vals
Proof
  rpt strip_tac >>
  drule opt_mmap_mem_func >>
  qpat_x_assum `OPT_MMAP _ _ = SOME _` $ rw o single o GSYM >>
  irule OPT_MMAP_CONG >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!_. _` imp_res_tac >>
  imp_res_tac eval_code_state_correct >> simp[]
QED

Theorem nested_decs_not_return_in_loop:
  ∀p vs es.
    ¬return_in_loop p ⇒ ¬return_in_loop (nested_decs vs es p)
Proof
  Induct_on `vs`
  >- (
    Cases_on `es` >> fs[nested_decs_def, return_in_loop_def]
  ) >>
  Cases_on `es` >> fs[nested_decs_def]
  >- fs[return_in_loop_def] >>
  simp[return_in_loop_def]
QED

Theorem not_return_arg_load_not_return:
  ∀p tmp_vars es vs.
    ¬return_in_loop p ⇒ ¬return_in_loop (arg_load tmp_vars es vs p)
Proof
  rw[arg_load_def] >>
  rpt (irule nested_decs_not_return_in_loop) >> simp[]
QED

Theorem unique_var_is_larger:
  ∀v x p tmp_vars ns.
    v = SUC (MAX x (MAX (vmax_prog p) (MAX (MAX_LIST tmp_vars) (MAX_LIST ns)))) ⇒
      x < v ∧
      MAX_LIST (var_prog p) < v ∧
      MAX_LIST tmp_vars < v ∧
      MAX_LIST ns < v
Proof
  rpt gen_tac >> strip_tac >>
  simp[LT_SUC_LE, MAX_LT, vmax_prog_def]
QED

Theorem unique_var_is_unique:
  ∀v x p tmp_vars ns.
    v = SUC (MAX x (MAX (vmax_prog p) (MAX (MAX_LIST tmp_vars) (MAX_LIST ns)))) ⇒
      x < v ∧
      ¬MEM v (var_prog p) ∧
      ¬MEM v tmp_vars ∧
      ¬MEM v ns
Proof
  rpt gen_tac >> strip_tac >>
  rpt conj_tac
  >- (
    `x < v` by simp[LT_SUC_LE] >>
    simp[]
  )
  >- (
    `MAX_LIST (var_prog p) < v` by (
      simp[LT_SUC_LE, MAX_LT, vmax_prog_def]
    ) >>
    strip_tac >> drule MAX_LIST_PROPERTY >> fs[]
  )
  >- (
    `MAX_LIST tmp_vars < v` by (
      simp[LT_SUC_LE, MAX_LT]
    ) >>
    strip_tac >> drule MAX_LIST_PROPERTY >> fs[]
  ) >>
  `MAX_LIST ns < v` by (
    simp[LT_SUC_LE, MAX_LT]
  ) >>
  strip_tac >> drule MAX_LIST_PROPERTY >> fs[]
QED

Theorem inline_tail_correct:
  ∀p s r s' k st argexps args ns tmp_vars.
    evaluate (p, dec_clock s with locals := FEMPTY |++ ZIP (ns, args)) = (k, st) ∧
    (case k of
       | NONE => (SOME Error, st)
       | SOME Error => (SOME Error, empty_locals st)
       | SOME TimeOut => (SOME TimeOut, empty_locals st)
       | SOME Break => (SOME Error, st)
       | SOME Continue => (SOME Error, st)
       | SOME (Return retv) => (SOME (Return retv), empty_locals st)
       | SOME (Exception eid) => (SOME (Exception eid), empty_locals st)
       | SOME (FinalFFI ffi) => (SOME (FinalFFI ffi), empty_locals st))
    = (r, s') ∧
    s.clock ≠ 0 ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT ns ∧ LENGTH ns = LENGTH args ∧
    OPT_MMAP (eval s) argexps = SOME args ∧
    tmp_vars = GENLIST (λx. MAX_LIST ns + MAX_LIST (FLAT (MAP var_cexp argexps)) + SUC x) (LENGTH ns)
   ⇒
    ∃s1'.
      evaluate (inline_tail (arg_load tmp_vars argexps ns p), s) = (r, s1') ∧
      state_rel s' s1'
Proof
  rpt strip_tac >>
  drule_at (Pos $ el 5) arg_load_stronger >>
  disch_then $ qspecl_then [`argexps`, `tmp_vars`] mp_tac >> fs[] >> impl_tac
  >- (
    simp[opt_mmap_eval_dec_clock_eq] >>
    Cases_on `k` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  disch_tac >> fs[] >>
  simp[inline_tail, evaluate_def] >>
  Cases_on `k` >> TRY (Cases_on `x`) >> gvs[state_rel_def, empty_locals_def]
QED

Theorem inline_standalone_correct:
  ∀p s r s' k st q ns args tmp_vars argexps.
    evaluate (p, dec_clock s with locals := FEMPTY |++ ZIP (ns, args)) = (k, st) ∧
    (case k of
       | NONE => (SOME Error, st)
       | SOME Error => (SOME Error, empty_locals st)
       | SOME TimeOut => (SOME TimeOut, empty_locals st)
       | SOME Break => (SOME Error, st)
       | SOME Continue => (SOME Error, st)
       | SOME (Return retv) => evaluate (q, st with locals := s.locals)
       | SOME (Exception eid) => (SOME (Exception eid), empty_locals st)
       | SOME (FinalFFI ffi) => (SOME (FinalFFI ffi), empty_locals st))
    = (r, s') ∧
    s.clock ≠ 0 ∧
    r ≠ SOME Error ∧
    ALL_DISTINCT ns ∧ LENGTH ns = LENGTH args ∧
    OPT_MMAP (eval s) argexps = SOME args ∧
    tmp_vars = GENLIST (λx. MAX_LIST ns + MAX_LIST (FLAT (MAP var_cexp argexps)) + SUC x) (LENGTH ns) ∧
    ¬return_in_loop p
    ⇒
    ∃s1'.
      evaluate (inline_standalone
                 (arg_load tmp_vars argexps ns
                   (transform_rec standalone_ret p)) q, s) = (r, s1') ∧
      state_rel s' s1' ∧
      case r of
        | NONE => locals_strong_rel s' s1'
        | SOME Break => locals_strong_rel s' s1'
        | SOME Continue => locals_strong_rel s' s1'
        | SOME Error => F
        | _ => T
Proof
  rpt strip_tac >>
  drule transform_standalone_correct' >> impl_tac
  >- (
    simp[] >>
    Cases_on `k` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  disch_tac >> fs[] >>
  drule_at (Pos $ el 5) arg_load_stronger >>
  disch_then $ qspecl_then [`argexps`, `tmp_vars`] mp_tac >> fs[] >> impl_tac
  >- (
    simp[opt_mmap_eval_dec_clock_eq] >>
    Cases_on `k` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  disch_tac >> fs[] >>
  simp[inline_standalone, Ntimes evaluate_def 2, eval_def] >>
  pairarg_tac >> fs[] >>
  Cases_on `k` >> TRY (Cases_on `x`) >> gvs[]
  >~ [`evaluate _ = (SOME (Return _), _)`]
  >- (
    qpat_x_assum `evaluate (q, st with locals := s.locals) = _` assume_tac >>
    drule evaluate_state_locals_rel_strong >> fs[] >>
    disch_then $ qspec_then `s1` mp_tac >> impl_tac
    >- (
      fs[locals_rel_def, state_rel_def, dec_clock_def]
    ) >>
    disch_tac >> fs[] >>
    qpat_x_assum `evaluate (q, st with locals := s.locals) = _` assume_tac >>
    imp_res_tac evaluate_locals_same_fdom' >>
    Cases_on `r` >> TRY (Cases_on `x`) >> fs[dec_clock_def,locals_rel_def, locals_strong_rel_def, EQ_FDOM_SUBMAP]
  ) >>
  fs[state_rel_def, empty_locals_def]
QED

Theorem inline_assign_correct:
  ∀p s r s' k st q rt ns args argexps ret_max tmp_vars.
    evaluate (p, dec_clock s with locals := FEMPTY |++ ZIP (ns, args)) = (k, st) ∧
    (case k of
      | NONE => (SOME Error, st)
      | SOME Error => (SOME Error, empty_locals st)
      | SOME TimeOut => (SOME TimeOut, empty_locals st)
      | SOME Break => (SOME Error, st)
      | SOME Continue => (SOME Error, st)
      | SOME (Return retv) =>
          (case FLOOKUP s.locals rt of
            | NONE => (SOME Error, st)
            | SOME vs => evaluate (q, st with locals := s.locals |+ (rt, retv)))
      | SOME (Exception eid) => (SOME (Exception eid), empty_locals st)
      | SOME (FinalFFI ffi) => (SOME (FinalFFI ffi), empty_locals st))
    = (r, s') ∧
    r ≠ SOME Error ∧
    s.clock  ≠ 0 ∧
    (!rv. k = SOME (Return rv) ⇒ ∃v. FLOOKUP s.locals rt = SOME v) ∧ 
    ALL_DISTINCT ns ∧ LENGTH ns = LENGTH args ∧
    OPT_MMAP (eval s) argexps = SOME args ∧
    ¬return_in_loop p ∧
    tmp_vars = GENLIST (λx. MAX_LIST ns + MAX_LIST (FLAT (MAP var_cexp argexps)) + SUC x) (LENGTH ns) ∧
    ret_max ≠ rt ∧
    ¬MEM ret_max (FLAT (MAP var_cexp argexps)) ∧
    ¬MEM ret_max (var_prog p) ∧
    ¬MEM ret_max tmp_vars ∧
    ¬MEM ret_max ns ⇒
    ∃s1'.
      evaluate (inline_assign
                 (arg_load tmp_vars argexps ns
                   (transform_rec (assign_ret ret_max) p)) q ret_max rt, s) = (r, s1') ∧
      state_rel s' s1' ∧
      case r of
        | NONE => locals_strong_rel s' s1'
        | SOME Break => locals_strong_rel s' s1'
        | SOME Continue => locals_strong_rel s' s1'
        | SOME Error => F
        | _ => T
Proof
  rpt strip_tac >>
  Cases_on `evaluate (p, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >>
  drule not_var_prog_not_affect_evaluate >>
  disch_then $ qspecl_then [`ret_max`, `Word 0w`] mp_tac >> fs[] >> impl_tac
  >- (
    Cases_on `k` >> TRY (Cases_on `x`) >> gvs[]
  ) >>
  disch_tac >> fs[] >>
  `¬MEM ret_max (MAP FST (ZIP (ns, args)))` by (
    drule MAP_ZIP >> fs[]
  ) >>
  drule FUPDATE_FUPDATE_LIST_COMMUTES >>
  disch_then $ qspecl_then [`Word 0w`, `FEMPTY`] $ assume_tac o GSYM >> fs[] >>
  drule transform_assign_correct_strong' >>
  disch_then $ qspec_then `ret_max` mp_tac >> fs[] >> impl_tac
  >- (
    drule_at (Pos last) $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] flookup_fupdate_zip_not_mem >>
    imp_res_tac MAP_ZIP >> fs[] >>
    disch_then $ qspecl_then [`args`, `FEMPTY |+ (ret_max, Word 0w)`] assume_tac >> fs[FLOOKUP_UPDATE] >>
    Cases_on `k` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  disch_tac >> fs[] >>
  drule evaluate_state_locals_rel_strong >>
  disch_then $ qspec_then `dec_clock s with locals := s.locals |+ (ret_max, Word 0w) |++ ZIP (ns, args)` mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      Cases_on `k` >> TRY (Cases_on `x`) >> fs[]
    ) >>
    simp[state_rel_def, locals_rel_def, SUBMAP_FLOOKUP_EQN] >>
    rpt strip_tac >>
    Cases_on `MEM x ns`
    >- (
      pop_assum $ assume_tac o SRULE [MEM_EL] >>
      gs[] >>
      drule $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] update_eq_zip_flookup >>
      disch_then imp_res_tac >> rfs[] >> pop_assum imp_res_tac >>
      pop_assum $ qspec_then `FEMPTY |+ (ret_max, Word 0w)` assume_tac >> fs[]
    ) >>
    drule $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] flookup_fupdate_zip_not_mem >>
    disch_then drule >>
    disch_tac >>
    first_assum $ qspec_then `FEMPTY |+ (ret_max, Word 0w)` assume_tac >> fs[] >>
    first_x_assum $ qspec_then `s.locals |+ (ret_max, Word 0w)` assume_tac >> fs[FLOOKUP_UPDATE]
  ) >>
  disch_tac >> fs[] >>
  qspec_then `dec_clock s with locals := s.locals |+ (ret_max, Word 0w)` mp_tac arg_load_stronger >>
  disch_then $ qspecl_then [`argexps`, `args`, `ns`, `FEMPTY |+ (ret_max, Word 0w)`, `transform_rec (assign_ret ret_max) p`, `r1`, `s1'`, `tmp_vars`] mp_tac >> impl_tac
  >- (
    conj_tac
    >- (
      qpat_assum `OPT_MMAP _ _ = SOME _` $ PURE_REWRITE_TAC o single o GSYM >>
      irule OPT_MMAP_CONG >>
      rpt strip_tac
      >- (
        `eval s x = eval (dec_clock s) x` by simp[eval_dec_clock_eq] >> simp[] >>
        `s.locals = (dec_clock s).locals` by simp[dec_clock_def] >> simp[] >>
        irule update_locals_not_vars_eval_eq' >>
        qpat_x_assum `~MEM _ (FLAT (MAP _ _))` assume_tac >>
        fs[MEM_FLAT, MEM_MAP] >>
        pop_assum $ qspec_then `var_cexp x` mp_tac >> fs[] >>
        disch_tac >> fs[] >>
        pop_assum $ qspec_then `x` mp_tac >> fs[]
      ) >>
      simp[]
    ) >>
    fs[] >>
    conj_tac
    >- (
      simp[FLOOKUP_UPDATE, SUBMAP_FLOOKUP_EQN]
    ) >>
    gs[] >>
    Cases_on `k` >> TRY (Cases_on `x`) >> fs[]
  ) >>
  disch_tac >> fs[] >>
  simp[inline_assign, Ntimes evaluate_def 4, eval_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  `dec_clock (s with locals := s.locals |+ (ret_max, Word 0w)) = dec_clock s with locals := s.locals |+ (ret_max, Word 0w)` by fs[dec_clock_def] >> gs[] >>
  Cases_on `k` >> TRY (Cases_on `x`) >> gvs[]
  >>~- ([`state_rel (empty_locals _) (_ with locals := res_var _ _)`],
    Cases_on `FLOOKUP s.locals ret_max` >> gvs[state_rel_def, empty_locals_def, res_var_def]
  ) >>
  qpat_x_assum `evaluate (Assign _ _, _) = _` $ assume_tac o SRULE [evaluate_def] >>
  fs[locals_ext_rel_def, FDIFF_def] >>
  qpat_x_assum `FOLDL _ _ _ SUBMAP _` $ assume_tac o SRULE [SUBMAP_FLOOKUP_EQN] >>
  first_assum $ qspec_then `ret_max` assume_tac >> fs[] >>
  drule_at (Pos last) $ INST_TYPE [alpha |-> ``:num``, beta |-> ``:'a word_lab``] flookup_res_var_distinct_zip_eq >>
  disch_then $ qspecl_then [`MAP (FLOOKUP (s.locals |+ (ret_max, Word 0w))) ns`, `s1'.locals`] assume_tac >> gs[] >>
  imp_res_tac MAP_ZIP >> fs[] >>
  ntac 4 (pop_assum kall_tac) >>
  qpat_assum `!_ _. FLOOKUP _ _ = _ ⇒ FLOOKUP _ _ = _` imp_res_tac >> fs[eval_def] >>
  qpat_assum `DRESTRICT _ (COMPL {_}) = DRESTRICT _ (COMPL _)` $ assume_tac o SRULE [fmap_eq_flookup] >> fs[FLOOKUP_DRESTRICT] >>
  first_x_assum $ qspec_then `rt` $ assume_tac o GSYM >> gs[] >>
  subgoal `state_rel (r' with locals := s.locals |+ (rt, w)) (st with locals := res_var st.locals (ret_max, FLOOKUP s.locals ret_max))`
  >- (
    Cases_on `FLOOKUP s.locals ret_max` >> Cases_on `FLOOKUP s.locals rt` >> gvs[state_rel_def]
  ) >>
  subgoal `locals_rel (r' with locals := s.locals |+ (rt, w)) (st with locals := res_var st.locals (ret_max, FLOOKUP s.locals ret_max))`
  >- (
    fs[locals_rel_def] >>
    Cases_on `FLOOKUP s.locals ret_max` >> Cases_on `FLOOKUP s.locals rt` >> gvs[res_var_def, SUBMAP_FLOOKUP_EQN]
    >- (
      qpat_assum `DRESTRICT _ (COMPL {_}) = DRESTRICT _ (COMPL _)` $ assume_tac o SRULE [fmap_eq_flookup] >> fs[FLOOKUP_DRESTRICT] >>
      rpt strip_tac >>
      Cases_on `x = rt` >> fs[FLOOKUP_UPDATE, DOMSUB_FLOOKUP_THM] >>
      Cases_on `x = ret_max` >> fs[] >>
      first_x_assum $ qspec_then `x` assume_tac >> gs[]
    ) >>
    qpat_assum `DRESTRICT _ (COMPL {_}) = DRESTRICT _ (COMPL _)` $ assume_tac o SRULE [fmap_eq_flookup] >> fs[FLOOKUP_DRESTRICT] >>
    rpt strip_tac >>
    Cases_on `x' = rt` >> fs[FLOOKUP_UPDATE] >>
    Cases_on `x' = ret_max` >> gs[] >>
    first_x_assum $ qspec_then `x'` assume_tac >> gs[]
  ) >>
  Cases_on `FLOOKUP s.locals rt` >> fs[] >>
  rev_drule evaluate_state_locals_rel_strong >> fs[] >>
  disch_then $ drule_at (Pos last) >> fs[] >>
  disch_tac >> fs[] >>
  Cases_on `r` >> TRY (Cases_on `x`) >> TRY (Cases_on `x'`) >> gvs[locals_rel_def, locals_strong_rel_def, locals_ext_rel_def, FDIFF_def] >>
  imp_res_tac evaluate_locals_same_fdom' >> gvs[] >>
  simp[EQ_FDOM_SUBMAP] >>
  qpat_x_assum `rt INSERT FDOM _ = FDOM _` $ simp o single o GSYM >>
  qpat_x_assum `FDOM (res_var _ _) = FDOM _.locals` $ simp o single o GSYM >>
  qpat_x_assum `DRESTRICT _ (COMP {_}) = DRESTRICT _ (COMPL {_})` $ assume_tac o SRULE [EQ_FDOM_SUBMAP, FDOM_DRESTRICT] >> fs[] >>
  Cases_on `FLOOKUP s.locals ret_max` >> gvs[res_var_def, DELETE_INSERT]
  >>~- ([`_ INSERT FDOM _ DELETE _`], 
    pop_assum $ assume_tac o SRULE [flookup_thm] >>
    drule DELETE_NON_ELEMENT_RWT >>
    qpat_x_assum `ret_max INSERT FDOM _ = FDOM _` $ simp o single o GSYM >>
    fs[DELETE_INSERT]
  ) >>
  simp[Once INSERT_COMM] >>
  qpat_x_assum `ret_max INSERT FDOM _ = FDOM _` $ simp o single o GSYM >>
  pop_assum $ assume_tac o SRULE [flookup_thm] >> fs[] >>
  fs[ABSORPTION]
QED

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


Theorem opt_mmap_eval_state_locals_same_code_fdom_same:
  ∀s es vals s1 inl_fs.
    OPT_MMAP (eval s) es = SOME vals ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    FDOM s.code ⊆ FDOM s1.code ⇒
    OPT_MMAP (eval s1) es = SOME vals
Proof
  rpt strip_tac >>
  drule opt_mmap_mem_func >>
  qpat_x_assum `OPT_MMAP _ _ = SOME _` $ rw o single o GSYM >>
  irule OPT_MMAP_CONG >>
  rpt strip_tac >> simp[] >>
  qpat_x_assum `!_. _` imp_res_tac >>
  imp_res_tac eval_state_locals_same_code_fdom_same >> simp[]
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

Theorem inline_correct_all:
  ∀p s r s' inl_fs s1 inl_bag.
    evaluate (p, s) = (r, s') ∧
    r ≠ SOME Error ∧
    inl_fs SUBMAP s.code ∧
    inl_bag SUBMAP inl_fs ∧
    state_rel_code s s1 ∧
    locals_strong_rel s s1 ∧
    code_inl_rel inl_fs s s1 ⇒
    ∃r1 s1'.
      evaluate (inline_prog inl_bag p, s1) = (r1, s1') ∧
      state_rel_code s' s1' ∧
      code_inl_rel inl_fs s' s1' ∧
      case r of
        | NONE => r1 = NONE ∧ locals_strong_rel s' s1'
        | SOME Break => r1 = SOME Break ∧ locals_strong_rel s' s1'
        | SOME Continue => r1 = SOME Continue ∧ locals_strong_rel s' s1'
        | SOME TimeOut => r1 = SOME TimeOut
        | SOME (Return v) => r1 = SOME (Return v)
        | SOME (Exception e) => r1 = SOME (Exception e)
        | SOME (FinalFFI f) => r1 = SOME (FinalFFI f)
        | _ => F
Proof
  recInduct evaluate_ind >> rpt strip_tac
  >~ [`evaluate (Call _ _ _, _)`]
  >- (
    imp_res_tac eval_code_inl >>
    imp_res_tac opt_mmap_eval_code_inl >>
    gvs[evaluate_def, inline_prog_def, CaseEq "option", CaseEq "word_lab", CaseEq "prod", lookup_code_def] >>
    Cases_on `FLOOKUP inl_bag fname` >> fs[]
    >- (
      qpat_x_assum `!_ _. OPT_MMAP _ _ = _ ⇒ _` imp_res_tac >>
      qpat_assum `code_inl_rel  _ _ _` $ imp_res_tac o SRULE [code_inl_rel_def] >>
      `s1.clock = s.clock` by fs[state_rel_code_def] >>
      Cases_on `caltyp` >> fs[evaluate_def, lookup_code_def] >>
      Cases_on `s.clock = 0` >> fs[]
      >>~- ([`state_rel_code _ (empty_locals _)`],
        gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def]) >>
      Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> gs[] >>
      first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag'`] mp_tac >> fs[] >>
      impl_tac
      >>~- ([`q ≠ SOME Error ∧ _ SUBMAP (dec_clock _).code ∧ _`],
        conj_tac
        >- gvs[AllCaseEqs()] >>
        fs[dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]
      ) >>
      disch_tac >> fs[]
      >- (
        gvs[AllCaseEqs(), state_rel_code_def, empty_locals_def, code_inl_rel_def]
      ) >>
      Cases_on `x` >> fs[] >>
      Cases_on `r''` >> fs[] >>
      Cases_on `r'''` >> gvs[]
      >- (
        gvs[CaseEq "result", CaseEq "option"]
        >>~- ([`state_rel_code (empty_locals _) (empty_locals _)`],
          gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def])
        >- (
          last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
          >- (
            imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]
          ) >>
          disch_tac >> fs[]
        ) >>
        last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (rt, retv)`, `inl_bag`] mp_tac >> impl_tac
        >- (
          imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]
        ) >>
        disch_tac >> fs[fmap_eq_flookup, locals_strong_rel_def]
      ) >>
      gvs[CaseEq "result", CaseEq "option"]
      >>~- ([`state_rel_code (empty_locals _) (empty_locals _)`],
        gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def]) >>
      Cases_on `x` >> fs[]
      >~ [`q = eid ⇒ _`]
      >- (
        Cases_on `eid = q` >> fs[]
        >- (
          last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
          >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]) >>
          disch_tac >> fs[]
        ) >>
        imp_res_tac evaluate_code_invariant >>
        gvs[AllCaseEqs(), dec_clock_def, empty_locals_def, state_rel_code_def, code_inl_rel_def, locals_strong_rel_def]
      )
      >- (
        last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
        >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]) >>
        disch_tac >> fs[]
      ) >>
      last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (rt, retv)`, `inl_bag`] mp_tac >> impl_tac
      >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]) >>
      disch_tac >> fs[fmap_eq_flookup, locals_strong_rel_def]
    ) >>
    (* the function name is in the inlining bag *)
    Cases_on `x` >> fs[] >>
    Cases_on `caltyp` >> fs[]
    >- (
      (* Tail *)
      Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> gs[] >>
      Cases_on `s.clock = 0` >> fs[]
      >- (
        simp[inline_tail, evaluate_def] >>
        pairarg_tac >> gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def]
      ) >>
      last_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag \\ fname`] mp_tac >> fs[] >> impl_tac
      >- (
        conj_tac
        >- (Cases_on `q'` >> TRY (Cases_on `x`) >> fs[]) >>
        gvs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def] >>
        irule SUBMAP_TRANS >> qrefine `inl_bag` >> fs[SUBMAP_DOMSUB] 
      ) >>
      disch_tac >> fs[] >>
      qabbrev_tac `tvar = GENLIST (λx. MAX_LIST q + (MAX_LIST (FLAT (MAP var_cexp argexps)) + SUC x)) (LENGTH q)` >>
      drule inline_tail_correct >> gs[] >>
      disch_then $ qspecl_then [`r1`,
                               `(case r1 of
                                  | NONE => (s1'')
                                  | SOME Break => (s1'')
                                  | SOME Continue => (s1'')
                                  | _ => (empty_locals s1''))`,
                               `argexps`] mp_tac >> fs[] >> impl_tac
      >- (
        Cases_on `q'` >> TRY (Cases_on `x`) >> Cases_on `r1` >> fs[state_rel_code_def]
      ) >>
      disch_tac >> fs[] >>
      qpat_x_assum `inl_bag SUBMAP _` $ imp_res_tac o SRULE [SUBMAP_FLOOKUP_EQN] >>
      qpat_x_assum `inl_fs SUBMAP _.code` $ imp_res_tac o SRULE [SUBMAP_FLOOKUP_EQN] >> gvs[eval_def] >>
      imp_res_tac evaluate_code_invariant >> gvs[] >>
      Cases_on `q'` >> TRY (Cases_on `x`) >> Cases_on `r1` >> gvs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, empty_locals_def, dec_clock_def, state_rel_def] 
    ) >>
      (* Non tail *)
    qpat_assum `inl_bag SUBMAP inl_fs` $ imp_res_tac o SRULE [SUBMAP_FLOOKUP_EQN] >>
    qpat_assum `inl_fs SUBMAP _.code` $ imp_res_tac o SRULE [SUBMAP_FLOOKUP_EQN] >> gvs[] >> 
    qpat_x_assum `!_ _. eval _ _ = _ ⇒ _` imp_res_tac >>
    qpat_x_assum `!_ _. OPT_MMAP _ _ = _ ⇒ _` imp_res_tac >>
    qpat_assum `code_inl_rel _ _ _` $ imp_res_tac o SRULE [code_inl_rel_def] >>
    `s1.clock = s.clock` by fs[state_rel_code_def] >>
    Cases_on `return_in_loop (inline_prog (inl_bag \\ fname) prog)` >> fs[]
    >- (
      Cases_on `x` >> fs[] >>
      Cases_on `r'` >> fs[] >>
      Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> gs[] >>
      Cases_on `r''` >> fs[evaluate_def, lookup_code_def]
      >- (
        Cases_on `s.clock = 0` >> fs[]
        >- gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def] >>
        first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag'`] mp_tac >> impl_tac
        >- gvs[AllCaseEqs(), dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
        disch_tac >> gvs[AllCaseEqs()]
        >>~- ([`state_rel_code _ (empty_locals _)`],
          fs[state_rel_code_def, code_inl_rel_def, empty_locals_def])
        >- (
          first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
          >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def]) >>
          disch_tac >> fs[]
        ) >>
        first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (rt, retv)`, `inl_bag`] mp_tac >> impl_tac
        >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def]) >>
        disch_tac >> fs[fmap_eq_flookup, locals_strong_rel_def]
      ) >>
      Cases_on `x` >> fs[evaluate_def, lookup_code_def] >>
      Cases_on `s.clock = 0` >> fs[]
      >- gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def] >>
      first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag'`] mp_tac >> impl_tac
      >- gvs[AllCaseEqs(), dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
      disch_tac >> gvs[AllCaseEqs()]
      >>~- ([`state_rel_code _ (empty_locals _)`],
        fs[state_rel_code_def, code_inl_rel_def, empty_locals_def])
      >- (
        first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
        >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def]) >>
        disch_tac >> fs[]
      )
      >- (
        first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (rt, retv)`, `inl_bag`] mp_tac >> impl_tac
        >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def]) >>
        disch_tac >> fs[fmap_eq_flookup, locals_strong_rel_def]
      ) >>
      first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
      >- (imp_res_tac evaluate_code_invariant >> gs[state_rel_code_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def]) >>
      disch_tac >> fs[]
    ) >>
    (* Non trivial case, is inlined *)
    Cases_on `x` >> fs[] >>
    Cases_on `r'` >> fs[] >>
    Cases_on `r''` >> fs[]
    >- (
      (* Without handler *)
      Cases_on `evaluate (prog,dec_clock s with locals := FEMPTY |++ ZIP (ns,args))` >> gs[] >>
      qabbrev_tac `tvar = GENLIST (λx. MAX_LIST ns + (MAX_LIST (FLAT (MAP var_cexp argexps)) + SUC x)) (LENGTH args)` >> 
      Cases_on `q` >> fs[]
      >- (
        Cases_on `s.clock = 0` >> fs[]
        >- (
          gvs[inline_standalone, Ntimes evaluate_def 2, eval_def, state_rel_code_def, empty_locals_def, code_inl_rel_def]
        ) >>
        first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag \\ fname`] mp_tac >> impl_tac
        >- (
          conj_tac
          >- gvs[AllCaseEqs()] >>
          gvs[dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
          irule SUBMAP_TRANS >> qrefine `inl_bag` >> fs[]
        ) >>
        disch_tac >> fs[] >>
        drule inline_standalone_correct >>
        disch_then $ qspecl_then [`(case r1 of
                                     | NONE => SOME Error
                                     | SOME Break => SOME Error
                                     | SOME Continue => SOME Error
                                     | SOME (Return retv) => 
                                        FST (evaluate (inline_prog inl_bag q', s1'' with locals := s1.locals))
                                     | res => res)`,
                                  `(case r1 of
                                     | NONE => s1''
                                     | SOME Break => s1''
                                     | SOME Continue => s1''
                                     | SOME (Return retv) => SND (evaluate (inline_prog inl_bag q', s1'' with locals := s1.locals))
                                     | _ => empty_locals s1'')`,
                                  `inline_prog inl_bag q'`,
                                  `tvar`,
                                  `argexps`] mp_tac >> impl_tac
        >- (
          conj_tac
          >- (
            Cases_on `q''` >> fs[] >>
            Cases_on `x` >> gvs[]
          ) >>
          fs[Abbr `tvar`] >>
          Cases_on `q''` >> TRY (Cases_on `x`) >> gvs[] >>
          last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
          >- (imp_res_tac evaluate_code_invariant >> gvs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def]) >>
          disch_tac >> gvs[AllCaseEqs()] >> Cases_on `r` >> TRY (Cases_on `x`) >> fs[] 
        ) >>
        disch_tac >> gs[] >>
        Cases_on `q''` >> TRY (Cases_on `x`) >> fs[]
        >~ [`evaluate _ = (SOME (Return _), _)`]
        >- (
          last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
          >- (imp_res_tac evaluate_code_invariant >> gvs[dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]) >>
          disch_tac >> fs[] >>
          imp_res_tac evaluate_code_invariant >> fs[] >>
          Cases_on `r` >> TRY (Cases_on `x`) >> gs[state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, state_rel_def]
        ) >>
        gvs[state_rel_def, state_rel_code_def, code_inl_rel_def, empty_locals_def]
      ) >>
    PURE_ONCE_REWRITE_TAC[evaluate_def] >>
      (* Assign *)
      qabbrev_tac `ret_var = SUC (MAX x (MAX (vmax_prog (inline_prog (inl_bag \\ fname) prog)) (MAX (MAX_LIST tvar) (MAX_LIST ns))))` >>
      Cases_on `s.clock = 0` >> fs[]
      >- (
        gs[inline_assign, Ntimes evaluate_def 4, eval_def] >>
        Cases_on `FLOOKUP s1.locals ret_var` >> gvs[state_rel_code_def, code_inl_rel_def, empty_locals_def, res_var_def]
      ) >>
      gs[] >>
      first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag \\ fname`] mp_tac >> impl_tac
      >- (
        gvs[AllCaseEqs(), state_rel_code_def, locals_strong_rel_def, code_inl_rel_def, dec_clock_def] >>
        irule SUBMAP_TRANS >> qrefine `inl_bag` >> fs[]
      ) >>
      disch_tac >> fs[] >>
      qpat_assum `locals_strong_rel _ _` $ assume_tac o SRULE [locals_strong_rel_def, fmap_eq_flookup] >>
      drule inline_assign_correct >>
      disch_then $ qspecl_then [`(case r1 of
                                   | NONE => SOME Error
                                   | SOME Break => SOME Error
                                   | SOME Continue => SOME Error
                                   | SOME (Return retv) =>
                                       (case FLOOKUP s1.locals x of
                                         | NONE => SOME Error
                                         | SOME vs => FST (evaluate (inline_prog inl_bag q', s1'' with locals := s1.locals |+ (x, retv))))
                                   | res => res)`,
                                `(case r1 of
                                   | NONE => s1''
                                   | SOME Break => s1''
                                   | SOME Continue => s1''
                                   | SOME (Return retv) =>
                                       (case FLOOKUP s1.locals x of
                                         | NONE => s1''
                                         | SOME vs => SND (evaluate (inline_prog inl_bag q', s1'' with locals := s1.locals |+ (x, retv))))
                                   | res => empty_locals s1'')`,
                                `inline_prog inl_bag q'`,
                                `x`,
                                `argexps`,
                                `ret_var`,
                                `tvar`] mp_tac >> impl_tac
      >- (
        qspecl_then [`ret_var`, `x`, `inline_prog (inl_bag \\ fname) prog`, `tvar`, `ns`] mp_tac unique_var_is_unique >> impl_tac
        >- fs[Abbr `ret_var`] >>
        disch_tac >> fs[] >>
        subgoal `¬MEM ret_var (FLAT (MAP var_cexp argexps))`
        >- (
          Cases_on `LENGTH args = 0`
          >- (
            qpat_x_assum `OPT_MMAP _ _ = _` assume_tac >>
            imp_res_tac opt_mmap_length_eq >> rfs[]
          ) >>
          irule MORE_THEN_NOT_MAX_LIST >>
          irule LESS_TRANS >> 
          qrefine `MAX_LIST tvar` >> conj_tac
          >- (
            subgoal `tvar ≠ []`
            >- (
              simp[Abbr `tvar`] >>
              strip_tac >>
              drule $ iffRL LENGTH_NIL >>
              disch_then $ assume_tac o SIMP_RULE bool_ss [LENGTH_GENLIST] >>
              fs[LENGTH_NIL]
            ) >>
            drule MAX_LIST_MEM >>
            qunabbrev_tac `tvar` >> fs[MEM_GENLIST]
          ) >>
          fs[Abbr `ret_var`, LT_SUC_LE]
        ) >>
        fs[] >>
        conj_tac
        >- (
          Cases_on `q''` >> TRY (Cases_on `x'`) >> gvs[] >>
          Cases_on `FLOOKUP s1.locals x` >> fs[] 
        ) >>
        conj_tac
        >- (
          Cases_on `q''` >> TRY (Cases_on `x'`) >> gvs[] >>
          Cases_on `FLOOKUP s1.locals x` >> fs[] >>
          last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (x, w)`, `inl_bag`] mp_tac >> impl_tac
          >- (imp_res_tac evaluate_code_invariant >> gvs[dec_clock_def, state_rel_code_def, locals_strong_rel_def, state_rel_def, code_inl_rel_def]) >>
          disch_tac >> fs[] >>
          Cases_on `r` >> TRY (Cases_on `x''`) >> fs[] 
        ) >>
        Cases_on `q''` >> TRY (Cases_on `x'`) >> gvs[] >>
        Cases_on `FLOOKUP s1.locals x` >> fs[]
      ) >>
      disch_tac >> gs[] >>
      Cases_on `q''` >> TRY (Cases_on `x'`) >> gs[]
      >~ [`r1 = SOME (Return w)`]
      >- (
        Cases_on `FLOOKUP s1.locals x` >> fs[] >>
        last_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (x, w)`, `inl_bag`] mp_tac >> impl_tac
        >- (imp_res_tac evaluate_code_invariant >> gs[dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def]) >>
        disch_tac >> gvs[] >>
        imp_res_tac evaluate_code_invariant >>
        Cases_on `r` >> TRY (Cases_on `x''`) >> fs[state_rel_code_def, state_rel_def, code_inl_rel_def, locals_strong_rel_def, dec_clock_def]
      ) >>
      gvs[] >>
      imp_res_tac evaluate_code_invariant >> gvs[state_rel_code_def, state_rel_def, empty_locals_def, code_inl_rel_def]
    ) >>
    (* With handler *)
    Cases_on `x` >> fs[evaluate_def, eval_def, lookup_code_def] >>
    Cases_on `s.clock = 0` >> fs[]
    >- gvs[state_rel_code_def, empty_locals_def, code_inl_rel_def] >>
    Cases_on `evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (ns, args))` >> gs[] >>
    first_x_assum $ qspecl_then [`inl_fs`, `dec_clock s1 with locals := FEMPTY |++ ZIP (ns, args)`, `inl_bag'`] mp_tac >> impl_tac
    >- gvs[AllCaseEqs(), dec_clock_def, state_rel_code_def, locals_strong_rel_def, code_inl_rel_def] >>
    disch_tac >> fs[] >>
    Cases_on `q'''` >> TRY (Cases_on `x`) >> gvs[]
    >~ [`evaluate _ = (SOME (Return _), _)`]
    >- (
      Cases_on `q` >> fs[]
      >- (
        first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >> impl_tac
        >- (imp_res_tac evaluate_code_invariant >> gvs[state_rel_code_def, dec_clock_def, locals_strong_rel_def, code_inl_rel_def]) >>
        disch_tac >> fs[]
      ) >>
      qpat_assum `locals_strong_rel _ _` $ assume_tac o SRULE [locals_strong_rel_def, fmap_eq_flookup] >>
      Cases_on `FLOOKUP s1.locals x` >> fs[] >>
    gs[Once evaluate_def] >>
      first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals |+ (x, w)`, `inl_bag`] mp_tac >> impl_tac
      >- (imp_res_tac evaluate_code_invariant >> gvs[state_rel_code_def, dec_clock_def, locals_strong_rel_def, code_inl_rel_def]) >>
      disch_tac >> fs[]
    )
    >~ [`evaluate _ = (SOME (Exception _), _)`]
    >- (
      Cases_on `c ≠ q''` >> fs[]
      >- (imp_res_tac evaluate_code_invariant >> gvs[state_rel_code_def, dec_clock_def, locals_strong_rel_def, code_inl_rel_def, empty_locals_def]) >>
      first_x_assum $ qspecl_then [`inl_fs`, `s1'' with locals := s1.locals`, `inl_bag`] mp_tac >>impl_tac
      >- (imp_res_tac evaluate_code_invariant >> gvs[state_rel_code_def, dec_clock_def, locals_strong_rel_def, code_inl_rel_def]) >>
      disch_tac >> fs[]
    ) >>
    imp_res_tac evaluate_code_invariant >>
    gvs[state_rel_code_def, empty_locals_def, dec_clock_def, code_inl_rel_def]
  )
  >~ [`evaluate (While _ _, _) = _`]
  >- (
    fs[Once evaluate_def, CaseEq "option", CaseEq "word_lab"] >>
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
      first_x_assum $ qspecl_then [`inl_fs`, `s1''`, `inl_bag`] mp_tac >> impl_tac
    )
  )
QED

