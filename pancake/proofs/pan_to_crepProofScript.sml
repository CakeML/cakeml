(*
  Correctness proof for pan_to_crep
*)
Theory pan_to_crepProof
Ancestors
(*  crep_inlineProof[qualified] *)
  panSem panProps crepLang crepSem pan_common
  listRange crepProps pan_commonProps pan_to_crep
Libs
  preamble

(* state relation *)

val s = ``(s:('a,'ffi) panSem$state)``

Definition excp_rel_def:
  excp_rel ceids seids <=>
  FDOM seids =  FDOM ceids /\
  (!e e' n n'.
    FLOOKUP ceids e = SOME n /\
    FLOOKUP ceids e' = SOME n' /\
    n = n' ==> e = e')
End

Definition ctxt_fc_def:
  ctxt_fc cvs em vs shs ns =
    <|vars := FEMPTY |++ ZIP (vs, ZIP (shs, with_shape shs ns));
      funcs := cvs; eids := em; vmax := MAX_LIST ns |>
End


Definition code_rel_def:
  code_rel ctxt s_code t_code <=>
  ∀f vshs prog rsh.
  FLOOKUP s_code f = SOME (vshs, prog, rsh) ==>
    localised_prog prog ∧
    FLOOKUP ctxt.funcs f = SOME (vshs, rsh) /\
       let vs  = MAP FST vshs;
           shs = MAP SND vshs;
           ns  = GENLIST I (size_of_shape (Comb shs));
           nctxt = ctxt_fc ctxt.funcs ctxt.eids vs shs ns in
       FLOOKUP t_code f = SOME (ns, compile nctxt prog)
End

Definition state_rel_def:
  state_rel ^s (t:('a,'ffi) crepSem$state) <=>
  s.memory = t.memory ∧
  s.memaddrs = t.memaddrs ∧
  s.sh_memaddrs = t.sh_memaddrs ∧
  s.structs = [] ∧
  s.globals = FEMPTY ∧
  s.clock = t.clock ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  s.base_addr = t.base_addr ∧
  s.top_addr = t.top_addr
End

Theorem state_rel_structs[local]:
  state_rel s t ==> s.structs = []
Proof
  simp [state_rel_def]
QED

Theorem state_rel_globals[local]:
  state_rel s t ==> s.globals = FEMPTY
Proof
  simp [state_rel_def]
QED

Definition locals_rel_def:
  locals_rel ctxt (s_locals:mlstring |-> 'a v) t_locals <=>
  no_overlap ctxt.vars /\ ctxt_max ctxt.vmax ctxt.vars /\
  ∀vname v.
    FLOOKUP s_locals vname = SOME v ==>
    ∃ns vs. FLOOKUP (ctxt.vars) vname = SOME (shape_of v, ns) ∧
    OPT_MMAP (FLOOKUP t_locals) ns = SOME vs ∧ flatten v = vs ∧
    is_wf_shape_nil (shape_of v)
End

Theorem code_rel_imp:
   code_rel ctxt s_code t_code ==>
  ∀f vshs prog.
  FLOOKUP s_code f = SOME (vshs, prog, rsh) ==>
    localised_prog prog ∧
    FLOOKUP ctxt.funcs f = SOME (vshs, rsh) /\
       let vs  = MAP FST vshs;
           shs = MAP SND vshs;
           ns  = GENLIST I (size_of_shape (Comb shs));
           nctxt = ctxt_fc ctxt.funcs ctxt.eids vs shs ns in
       FLOOKUP t_code f = SOME (ns, compile nctxt prog)
Proof
  fs [code_rel_def] >> metis_tac[]
QED

Theorem code_rel_empty_locals:
  code_rel ctxt s.code t.code ==>
  code_rel ctxt (empty_locals s).code (empty_locals t).code
Proof
  rw [code_rel_def, empty_locals_def, panSemTheory.empty_locals_def] >>
  metis_tac[]
QED

Theorem cexp_heads_eq:
  !es. cexp_heads es = cexp_heads_simp es
Proof
  Induct >>
  rw [cexp_heads_def, cexp_heads_simp_def] >>
  fs [] >>
  every_case_tac >> fs []
QED

(* TODO: move to crepProps and (perhaps) replace eval_load_shape_el_rel *)
Theorem load_shape_el_rel:
  ∀m n a t e.
    n < m ⇒
    EL n (load_shape a m e) =
    if a + bytes_in_word * n2w n = 0w then
      Load e
    else
      Load (Op Add [e; Const (a + bytes_in_word * n2w n)])
Proof
  Induct_on ‘n’ >> rw[] >>
  rw[Once $ oneline load_shape_def] >>
  TOP_CASE_TAC >> gvs[] >>
  rw[] >> rw[] >>
  gvs[n2w_SUC,WORD_LEFT_ADD_DISTRIB]
QED

Theorem compile_exp_val_rel:
  ∀s e v (t :('a, 'b) state) ct es sh.
  panSem$eval s e = SOME v ∧
  state_rel s t ∧
  code_rel ct s.code t.code ∧
  locals_rel ct s.locals t.locals ∧
  localised_exp e ∧
  compile_exp ct e = (es, sh) ==>
  MAP (eval t) es = MAP SOME (flatten v) ∧
  LENGTH es = size_of_shape sh ∧
  shape_of v = sh ∧
  is_wf_shape_nil sh
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >~ [‘Const w’] >-
   (rename [‘Const w’] >>
    fs [panSemTheory.eval_def] >> rveq >>
    fs [flatten_def] >>
    fs [compile_exp_def] >> rveq >>
    fs [OPT_MMAP_def, eval_def,
        panLangTheory.size_of_shape_def, shape_of_def,
        panLangTheory.is_wf_shape_def])
  >~ [‘eval s (Var Local vname)’] >-
   (fs [panSemTheory.eval_def] >> rveq >>
    fs [locals_rel_def] >>
    first_x_assum drule >>
    fs [] >> strip_tac >> fs [] >>
    fs [compile_exp_def] >> rveq >>
    fs [lookup_locals_eq_map_vars] >>
    fs [opt_mmap_eq_some] >>
    fs [MAP_MAP_o] >>
    metis_tac [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >~ [‘eval s (Var Global fname)’] >-
   (rename [] >>
    fs[localised_exp_simps])
  >~ [‘eval s (RStruct es)’] >-
   (rpt gen_tac >> strip_tac >> fs [] >>
    fs [panSemTheory.eval_def, option_case_eq,localised_exp_simps] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [panLangTheory.size_of_shape_def, shape_of_def, panLangTheory.is_wf_shape_def] >>
    fs [MAP_MAP_o, MAP_FLAT, flatten_def] >>
    fs [o_DEF,LENGTH_FLAT] >>
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac [‘vs’, ‘es’] >>
    Induct >> fs [] >>
    rpt gen_tac >> strip_tac >> fs [OPT_MMAP_def] >>
    rewrite_tac [AND_IMP_INTRO] >> strip_tac >> rveq >>
    rename [‘_ = SOME vs’] >>
    fs [] >>
    last_x_assum mp_tac >>
    impl_tac >-
     metis_tac [] >>
    strip_tac >> fs [] >>
    last_x_assum (qspec_then ‘h’ mp_tac) >> fs [] >>
    disch_then drule >> disch_then drule >>
    cases_on ‘compile_exp ct h’ >> fs [])
  >~ [‘eval s (RField index e)’] >-
   (rpt gen_tac >> strip_tac >> fs [] >>
    fs [panSemTheory.eval_def, option_case_eq, v_case_eq, localised_exp_simps] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
    first_x_assum drule_all >> fs [shape_of_def] >>
    strip_tac >> fs [] >> rveq >>
    qpat_x_assum ‘_ = SOME (RStruct _)’ kall_tac >>
    qpat_x_assum ‘compile_exp _ _ = _’ kall_tac >>
    rpt (pop_assum mp_tac) >>
    MAP_EVERY qid_spec_tac
              [‘ct’,‘cexp’ ,‘sh’ , ‘es’, ‘t’, ‘s’, ‘index’, ‘vs’] >>
    Induct >> rpt gen_tac >- fs [] >>
    rewrite_tac [AND_IMP_INTRO] >>
    strip_tac >> fs [] >>
    cases_on ‘index’ >> fs []
    >- (
     fs [comp_field_def] >> rveq >>
     fs [MAP_TAKE, flatten_def] >>
     fs [panLangTheory.size_of_shape_def, panLangTheory.is_wf_shape_def] >>
     fs [GSYM length_flatten_eq_size_of_shape] >>
     metis_tac [LENGTH_MAP, TAKE_LENGTH_APPEND]) >>
    fs [comp_field_def] >>
    last_x_assum drule >>
    ntac 4 (disch_then drule) >>
    fs [panLangTheory.size_of_shape_def, flatten_def, panLangTheory.is_wf_shape_def] >>
    drule map_append_eq_drop >>
    fs [LENGTH_MAP, length_flatten_eq_size_of_shape])
  >~ [‘eval s (Load sh e)’] >-
   (rpt gen_tac >> strip_tac >>
    fs [panSemTheory.eval_def, option_case_eq, v_case_eq, localised_exp_simps,
        CaseEq "word_lab"] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
    last_x_assum drule_all >>
    imp_res_tac state_rel_structs >>
    strip_tac >>
    fs [shape_of_def, panLangTheory.size_of_shape_def,flatten_def] >>
    rveq >> fs [] >> rveq >>
    fs [length_load_shape_eq_shape] >>
    drule mem_load_some_shape_eq >>
    strip_tac >> fs [] >>
    fs [MAP_EQ_EVERY2] >> fs [length_load_shape_eq_shape] >>
    rveq >> fs [GSYM length_flatten_eq_size_of_shape] >>
    fs [LIST_REL_EL_EQN] >>  fs [length_load_shape_eq_shape] >>
    rw [] >> fs [state_rel_def] >>
    drule mem_load_flat_rel >>
    disch_then drule >>
    strip_tac >> fs [] >>
    drule eval_load_shape_el_rel >>
    disch_then (qspecl_then [‘0w’, ‘t’,‘x0’] mp_tac) >> fs [] >>
    strip_tac >>
    gs [eval_def, OPT_MMAP_def] >>
    every_case_tac >> fs [] >> rveq >>
    fs[EVERY_DEF] >> cases_on ‘h’ >> fs [] >>
    fs [wordLangTheory.word_op_def] >> rveq >>
    qpat_x_assum ‘mem_load _ _ = _’ (mp_tac o GSYM) >>
    strip_tac >> fs [])
  >~ [‘eval s (LoadByte e)’] >-
   (rpt gen_tac >> strip_tac >>
    fs [panSemTheory.eval_def, option_case_eq, v_case_eq, localised_exp_simps,
        CaseEq "word_lab", option_case_eq] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
    first_x_assum drule_all >> fs [shape_of_def] >>
    strip_tac >> fs [] >> rveq >>
    cases_on ‘cexp’ >> fs [panLangTheory.size_of_shape_def, flatten_def] >> rveq >>
    fs [panLangTheory.size_of_shape_def] >>
    fs [eval_def, state_rel_def])
  >~ [‘eval s (Load32 e)’] >-
   (rpt gen_tac >> strip_tac >>
    fs [panSemTheory.eval_def, option_case_eq, v_case_eq, localised_exp_simps,
        CaseEq "word_lab", option_case_eq] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    pairarg_tac >> fs [CaseEq "shape"] >> rveq >>
    first_x_assum drule_all >> fs [shape_of_def] >>
    strip_tac >> fs [] >> rveq >>
    cases_on ‘cexp’ >> fs [panLangTheory.size_of_shape_def, flatten_def] >> rveq >>
    fs [panLangTheory.size_of_shape_def] >>
    fs [eval_def, state_rel_def])
  >~ [‘eval s (Op op es)’] >-
   (rpt gen_tac >> strip_tac >>
    fs [panSemTheory.eval_def, option_case_eq, v_case_eq, localised_exp_simps,
        CaseEq "word_lab", option_case_eq] >> rveq >>
    fs [compile_exp_def] >> rveq >>
    fs [cexp_heads_eq] >>
    fs [cexp_heads_simp_def] >>
    pop_assum mp_tac >>
    IF_CASES_TAC
    >- (rpt $ disch_then assume_tac >>
        spose_not_then kall_tac >>
        gvs[AllCaseEqs(),MEM_MAP] >>
        drule opt_mmap_mem_func >>
        disch_then drule >>
        strip_tac >> fs [] >>
        rename1 ‘MEM e es’ >>
        cases_on ‘compile_exp ct e’ >> fs [] >>
        ‘shape_of m = One’ by (
          ‘MEM m ws’ by (
            drule opt_mmap_mem_defined >>
            disch_then drule >>
            simp[]) >>
          qpat_x_assum ‘EVERY _ ws’ mp_tac >>
          fs [EVERY_MEM] >>
          disch_then drule >>
          fs [] >> TOP_CASE_TAC >> fs [Once $ oneline panSemTheory.shape_of_def] >>
          TOP_CASE_TAC >> fs [shape_of_def]) >>
        gvs[EVERY_MEM] >>
        res_tac >>
        last_x_assum drule_all >>
        strip_tac >> rveq >> rfs [panLangTheory.size_of_shape_def]) >>
    fs [] >> rveq >>
    fs [panLangTheory.size_of_shape_def, shape_of_def, panLangTheory.is_wf_shape_def] >>
    fs [flatten_def, eval_def, MAP_MAP_o] >>
    ‘OPT_MMAP (λa. eval t a)
     (MAP (HD ∘ FST ∘ (λa. compile_exp ct a)) es) =
     OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es’ by (
      ho_match_mp_tac IMP_OPT_MMAP_EQ >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
      rw [] >>
      drule opt_mmap_length_eq >>
      strip_tac >> fs [] >>
      first_x_assum (qspec_then ‘EL n es’ mp_tac) >>
      impl_tac >- metis_tac [EL_MEM] >>
      drule opt_mmap_el >> fs [] >>
      disch_then drule >>
      strip_tac >> fs [] >>
      disch_then drule >>
      disch_then drule >>
      disch_then (qspecl_then [‘FST (compile_exp ct (EL n es))’,
                               ‘SND(compile_exp ct (EL n es))’] mp_tac) >>
      fs [] >>
      strip_tac >>
      fs [EVERY_EL] >>
      res_tac >>
      fs[] >>
      pop_assum mp_tac >>
      TOP_CASE_TAC >> fs[] >>
      fs[EL_MAP] >>
      fs[flatten_def] >>
      rename1 ‘Val ww’ >> Cases_on ‘ww’ >> fs[v2word_def]) >>
    fs [] >>
    ‘OPT_MMAP (λa. OPTION_MAP v2word (eval s a)) es =
     SOME (MAP v2word ws)’ by (
      ho_match_mp_tac opt_mmap_opt_map >> fs []) >>
    fs [EVERY_MAP, MAP_MAP_o] >>
    strip_tac >> fs [flatten_def] >>
    rveq >>
    fs[] >>
    simp[eval_def] >>
    irule EQ_TRANS >>
    first_x_assum $ irule_at $ Pos last >>
    AP_TERM_TAC >>
    simp[MAP_MAP_o] >>
    simp[MAP_EQ_f] >>
    rw[] >>
    gvs[EVERY_MEM] >>
    res_tac >>
    every_case_tac >> fs[v2word_def])
  >~ [‘Panop’] >-
   (rpt gen_tac >> strip_tac >>
    gvs[compile_exp_def,AllCaseEqs(),eval_def,panLangTheory.size_of_shape_def,
        panSemTheory.eval_def,crepSemTheory.eval_def,flatten_def,shape_of_def,
        DefnBase.one_line_ify NONE pan_op_def,MAP_EQ_CONS,opt_mmap_eq_some,
        cexp_heads_def,PULL_EXISTS, SF DNF_ss,localised_exp_simps
       ] >>
    rpt $ qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
    rpt $ first_x_assum $ drule_then $ drule_then $ drule_then drule >>
    rpt $ disch_then $ resolve_then Any assume_tac $ GSYM PAIR >>
    gvs[flatten_def,shape_of_def,DefnBase.one_line_ify NONE compile_panop_def,crep_op_def])
  >~ [‘Cmp’] >-
   (rpt gen_tac >> strip_tac >>
    fs [panSemTheory.eval_def] >>
    fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
    fs [compile_exp_def,localised_exp_simps] >>
    cases_on ‘compile_exp ct e’ >>
    cases_on ‘compile_exp ct e'’ >>
    first_x_assum drule_all >>
    first_x_assum drule_all >>
    strip_tac >> strip_tac >>
    fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
    rveq >>
    fs [panLangTheory.size_of_shape_def, shape_of_def] >>
    rveq >>
    fs [panLangTheory.size_of_shape_def, shape_of_def] >>
    fs [eval_def] >>
    every_case_tac >> fs [] >> EVAL_TAC)
  >~ [‘Shift’] >-
   (rpt gen_tac >> rpt strip_tac >>
    fs [panSemTheory.eval_def] >>
    fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
    fs [compile_exp_def,localised_exp_simps] >>
    cases_on ‘compile_exp ct e’ >>
    first_x_assum drule_all >>
    rpt strip_tac >> fs [] >>
    fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def] >>
    rveq >>
    fs [panLangTheory.size_of_shape_def, shape_of_def] >> rveq >>
    fs [eval_def] >>  every_case_tac >>
    fs [panLangTheory.size_of_shape_def, shape_of_def])>>
  rpt strip_tac >>
  fs [panSemTheory.eval_def] >>
  fs [option_case_eq, v_case_eq, word_lab_case_eq] >> rveq >>
  fs [compile_exp_def,localised_exp_simps] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def, flatten_def,
    panLangTheory.is_wf_shape_def] >>
  fs [eval_def] >>
  fs[state_component_equality, state_rel_def]
QED

Theorem mem_comp_field_lem:
  ∀i l es x.
  MEM x (FST(comp_field i l es)) ⇒
  MEM x es ∨ x = (Const 0w)
Proof
  Induct_on ‘l’ >> rw[comp_field_def] >>
  imp_res_tac MEM_TAKE >>
  rw[] >>
  res_tac >>
  imp_res_tac MEM_DROP_IMP >>
  gvs[]
QED

Theorem MEM_compile_exp_vmax:
  ∀ctxt exp n e.
    ctxt_max ctxt.vmax ctxt.vars ∧ MEM n (var_cexp e) ∧
    MEM e (FST(compile_exp ctxt exp)) ⇒
    n ≤ ctxt.vmax
Proof
  recInduct compile_exp_ind >>
  rw[compile_exp_def] >>
  gvs[var_cexp_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,UNCURRY_eq_pair,ELIM_UNCURRY, SF DNF_ss] >>
  rpt(PURE_FULL_CASE_TAC >> gvs[var_cexp_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,UNCURRY_eq_pair,ELIM_UNCURRY]) >>
  res_tac
  >- (gvs[ctxt_max_def] >> res_tac >> gvs[])
  >- (imp_res_tac mem_comp_field_lem >> res_tac >> gvs[var_cexp_def])
  >- (imp_res_tac var_exp_load_shape >> gvs[]
     ) >>
  gvs[cexp_heads_eq,cexp_heads_simp_def,MEM_MAP,FORALL_PROD] >>
  first_x_assum drule >>
  disch_then drule >>
  disch_then irule >>
  Cases_on ‘(FST (compile_exp ctxt a'))’ >>
  gvs[] >>
  metis_tac[FST,PAIR,SND]
QED


Definition globals_lookup_def:
  globals_lookup t v =
    OPT_MMAP (FLOOKUP t.globals)
             (GENLIST (λx. n2w x) (size_of_shape (shape_of v)))
End


Theorem pc_compile_correct:
  ∀v v1 res s1 t ctxt.
    evaluate (v,v1) = (res,s1) ∧ res ≠ SOME Error ∧ state_rel v1 t ∧
    code_rel ctxt v1.code t.code ∧ excp_rel ctxt.eids v1.eshapes ∧
    locals_rel ctxt v1.locals t.locals ∧ localised_prog v ⇒
    ∃res1 t1.
      evaluate (compile ctxt v,t) = (res1,t1) ∧ state_rel s1 t1 ∧
      code_rel ctxt s1.code t1.code ∧ excp_rel ctxt.eids s1.eshapes ∧
      case res of
        NONE => res1 = NONE ∧ locals_rel ctxt s1.locals t1.locals
      | SOME Error => F
      | SOME TimeOut => res1 = SOME TimeOut
      | SOME Break => res1 = SOME (Break 0) ∧ locals_rel ctxt s1.locals t1.locals
      | SOME Continue =>
        res1 = SOME (Continue 0) ∧ locals_rel ctxt s1.locals t1.locals
      | SOME (Return v) => res1 = SOME (Return (flatten v))
      | SOME (Exception eid v') =>
        (case FLOOKUP ctxt.eids eid of
           NONE => F
         | SOME n =>
           res1 = SOME (Exception n) ∧
           (1 ≤ size_of_shape (shape_of v') ⇒
            globals_lookup t1 v' = SOME (flatten v') ∧
            size_of_shape (shape_of v') ≤ 32))
      | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
Proof
  recInduct panSemTheory.evaluate_ind
  \\ rpt conj_tac
  >~ [`panLang$Skip`] >- suspend "Skip"
  >~ [`panLang$Break`] >- suspend "Break"
  >~ [`panLang$Continue`] >- suspend "Continue"
  >~ [`panLang$Annot`] >- suspend "Annot"
  >~ [`panLang$Tick`] >- suspend "Tick"
  >~ [`panLang$Assign`] >- suspend "Assign"
  >~ [`panLang$Primitive`] >- suspend "Primitive"
  >~ [`panLang$Dec`] >- suspend "Dec"
  >~ [`panLang$Store`] >- suspend "Store"
  >~ [`panLang$Store32`] >- suspend "Store32"
  >~ [`panLang$StoreByte`] >- suspend "StoreByte"
  >~ [`panLang$ShMemLoad`] >- suspend "ShMemLoad"
  >~ [`panLang$ShMemStore`] >- suspend "ShMemStore"
  >~ [`panLang$Return`] >- suspend "Return"
  >~ [`panLang$Raise`] >- suspend "Raise"
  >~ [`panLang$ExtCall`] >- suspend "ExtCall"
  >~ [`panLang$Seq`] >- suspend "Seq"
  >~ [`panLang$If`] >- suspend "If"
  >~ [`panLang$While`] >- suspend "While"
  >~ [`panLang$Call`] >- suspend "Call"
  >~ [`panLang$DecCall`] >- suspend "DecCall"
QED

Resume pc_compile_correct[Skip]:
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_def,localised_prog_def] >> rveq >> fs []
QED

Resume pc_compile_correct[Break]:
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_def,localised_prog_def] >> rveq >> fs []
QED

Resume pc_compile_correct[Continue]:
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_def,localised_prog_def] >> rveq >> fs []
QED

Resume pc_compile_correct[Annot]:
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_def,localised_prog_def] >> rveq >> fs []
QED

Resume pc_compile_correct[Tick]:
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def, evaluate_def,
      compile_def] >> rveq >> fs [] >>
  every_case_tac >> fs [panSemTheory.empty_locals_def, empty_locals_def,
                        panSemTheory.dec_clock_def, dec_clock_def] >>
  rveq >> fs [state_rel_def]
QED


Theorem locals_rel_lookup_ctxt:
  locals_rel ctxt lcl lcl' /\
  FLOOKUP lcl vr = SOME v ==>
  ?ns. FLOOKUP ctxt.vars vr = SOME (shape_of v,ns) /\
   LENGTH ns = LENGTH (flatten v) /\
   OPT_MMAP (FLOOKUP lcl') ns = SOME (flatten v) /\
   is_wf_shape_nil (shape_of v)
Proof
  rw [locals_rel_def] >>
  metis_tac [opt_mmap_length_eq]
QED


Theorem eval_nested_assign_distinct_eq:
  !es ns t ev vs.
  MAP (eval t) es = MAP SOME ev /\
  OPT_MMAP (FLOOKUP t.locals) ns = SOME vs /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns /\
  LENGTH ns = LENGTH es ==>
  evaluate (nested_seq (MAP2 Assign ns es),t) =
      (NONE, t with locals := t.locals |++ ZIP (ns, ev))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   fs [nested_seq_def, evaluate_def,
       FUPDATE_LIST_THM,
       state_component_equality]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_seq_def] >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  fs [MAP_EQ_CONS] >>
  rveq >> rfs [] >>
  fs [OPT_MMAP_def] >>
  rveq >> rfs [] >>
  rveq >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘FLOOKUP t.locals n = SOME nv’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  drule opt_mmap_flookup_update >>
  disch_then drule >>
  disch_then (qspec_then ‘v’ assume_tac) >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule >>
  fs [state_accfupds] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  fs [FUPDATE_LIST_THM]
QED


Theorem eval_nested_decs_seq_res_var_eq:
  !es ns t ev p.
  MAP (eval t) es = MAP SOME ev /\
  LENGTH ns = LENGTH es /\
  distinct_lists ns (FLAT (MAP var_cexp es)) /\
  ALL_DISTINCT ns ==>
  let (q,r) = evaluate (p, t with locals := t.locals |++ ZIP (ns, ev)) in
  evaluate (nested_decs ns es p, t) =
  (q, r with locals :=
        FOLDL res_var r.locals (ZIP (ns, MAP (FLOOKUP t.locals) ns)))
Proof
  Induct
  >- (
   rpt gen_tac >> strip_tac >>
   cases_on ‘ns’ >> fs [] >>
   pairarg_tac >> fs [] >>
   fs [nested_decs_def, FUPDATE_LIST_THM] >>
   cases_on ‘t’ >> cases_on ‘r’ >>
   fs [state_component_equality, recordtype_state_seldef_locals_fupd_def]) >>
  rpt gen_tac >>
  strip_tac >>
  cases_on ‘ns’ >>
  fs [nested_decs_def] >>
  fs [evaluate_def] >>
  fs [MAP_EQ_CONS] >>
  pairarg_tac >> fs [] >>
  rveq >> rfs [] >>
  pairarg_tac >> fs [] >>
  rename [‘eval t e = SOME v’] >>
  rename [‘MAP (eval t) es = MAP SOME ev’] >>
  rename [‘~MEM n t'’] >>
  qpat_x_assum ‘distinct_lists _ _’
               (assume_tac o REWRITE_RULE [Once CONS_APPEND]) >>
  drule distinct_lists_cons >>
  strip_tac >>
  ‘MAP (eval (t with locals := t.locals |+ (n,v))) es = MAP SOME ev’ by (
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    rw [] >>
    first_x_assum (qspec_then ‘n'’ assume_tac) >>
    rfs [] >>
    ho_match_mp_tac update_locals_not_vars_eval_eq >>
    fs [distinct_lists_def] >>
    CCONTR_TAC >>
    metis_tac [MEM_FLAT, EL_MEM, MEM_MAP]) >>
  qpat_x_assum ‘MAP (eval t) es = MAP SOME ev’ kall_tac >>
  first_x_assum drule_all >>
  disch_then (qspec_then ‘p’ assume_tac) >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [FUPDATE_LIST_THM] >>
  fs [state_component_equality] >>
  ‘MAP (FLOOKUP (t.locals |+ (n,v))) t' =
   MAP (FLOOKUP t.locals) t'’ by
    metis_tac [MAP_EQ_f, FLOOKUP_UPDATE] >>
  fs [] >>
  pop_assum kall_tac >>
  qpat_x_assum ‘~MEM n t'’ mp_tac >>
  rpt (pop_assum kall_tac) >>
  MAP_EVERY qid_spec_tac [‘r’, ‘n’,‘t’, ‘t'’] >>
  Induct >> rw [] >>
  first_x_assum (qspec_then ‘t’ mp_tac) >>
  disch_then (qspec_then ‘n’ mp_tac) >>
  fs [] >>
  disch_then (qspec_then ‘r with locals :=
                          res_var r.locals (h,FLOOKUP t.locals h)’ mp_tac) >>
  fs [] >>
  metis_tac [res_var_commutes]

QED

Theorem mem_comp_field:
  !sh i e shp ce es vs.
   i < LENGTH vs /\
  LENGTH e = size_of_shape (shape_of (RStruct vs)) /\
  comp_field i sh e = (es,shp) /\
  Comb sh = shape_of (RStruct vs) /\
  MEM ce es ==> MEM ce e
Proof
  Induct >> rw [comp_field_def] >>
  fs [] >> rveq
  >- fs [shape_of_def]
  >- (
   cases_on ‘vs’ >> fs [] >>
   fs [panLangTheory.size_of_shape_def, shape_of_def] >>
   rveq >> fs [] >>
   ‘size_of_shape (shape_of h') <= LENGTH e’ by DECIDE_TAC >>
   metis_tac [MEM_TAKE]) >>
  cases_on ‘vs’ >> fs [] >>
  fs [panLangTheory.size_of_shape_def, shape_of_def] >>
  rveq >> fs [] >>
  first_x_assum (qspecl_then  [‘i-1’, ‘(DROP (size_of_shape (shape_of h')) e)’,
                               ‘shp’, ‘ce’, ‘es’, ‘t’] mp_tac) >>
  fs [] >>
  metis_tac [MEM_DROP_IMP]
QED


Theorem eval_var_cexp_present_ctxt:
  ∀(s :('a, 'b) panSem$state) e v (t :('a, 'b) state) ct es sh.
  state_rel s t /\
  eval s e = SOME v /\
  code_rel ct s.code t.code /\
  locals_rel ct s.locals t.locals /\
  localised_exp e ∧
  compile_exp ct e = (es,sh) ==>
  (∀n. MEM n (FLAT (MAP var_cexp es)) ==>
   ?v shp ns. FLOOKUP ct.vars v = SOME (shp,ns)  /\
       MEM n ns)
Proof
  ho_match_mp_tac panSemTheory.eval_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- (
   rename [‘Const w’] >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def])
  >- (
   rename [‘eval s (Var Local vname)’] >>
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   fs [var_cexp_def] >>
   fs [CaseEq "option"] >> rveq
   >- fs [var_cexp_def] >>
   cases_on ‘v'’ >> fs [] >>
   rveq >>
   fs [MEM_MAP, MEM_FLAT] >>
   rveq >>
   fs [var_cexp_def] >>
   metis_tac [])
  >- (
   rename [‘eval s (Var Global vname)’] >>
   fs[localised_exp_simps])
  >- (
   rename [‘eval s (RStruct es)’] >>
   rpt strip_tac >>
   gvs[panSemTheory.eval_def,AllCaseEqs(),MEM_FLAT,MEM_MAP, SF DNF_ss] >>
   first_x_assum irule >>
   simp[PULL_EXISTS] >>
   ntac 2 $ first_assum $ irule_at $ Pos last >>
   simp[] >>
   rpt $ first_assum $ irule_at $ Pos last >>
   gvs[compile_exp_def,MEM_FLAT,MEM_MAP] >>
   rpt $ first_assum $ irule_at $ Pos last >>
   gvs[localised_exp_simps,EVERY_MEM] >>
   irule_at (Pos last) $ GSYM PAIR >>
   gvs[opt_mmap_eq_some] >>
   fs[LIST_EQ_REWRITE,MEM_EL,EL_MAP])
  >- (
   rename [‘eval s (RField index e)’] >>
   rpt strip_tac >>
   gvs[compile_exp_def,localised_exp_simps,UNCURRY_EQ,AllCaseEqs(),
       panSemTheory.eval_def, var_cexp_def,
       MEM_FLAT,MEM_MAP,PULL_EXISTS,SF DNF_ss
      ] >>
   first_x_assum irule >>
   simp[PULL_EXISTS] >>
   rpt $ first_assum $ irule_at $ Pos last >>
   drule_then irule mem_comp_field >>
   simp[PULL_EXISTS] >>
   first_assum $ irule_at $ Pos last >>
   first_x_assum $ irule_at $ Pat ‘_ = _’ >>
   drule_all_then strip_assume_tac compile_exp_val_rel >>
   gvs[])
  >- (
   rename [‘eval s (NStruct nm es)’] >>
   rpt strip_tac >>
   imp_res_tac state_rel_structs >>
   gs[panSemTheory.eval_def]
  )
  >- (
   rename [‘eval s (NField fld e)’] >>
   rpt strip_tac >>
   imp_res_tac state_rel_structs >>
   gs[panSemTheory.eval_def] >>
   fs[option_case_eq, v_case_eq]
  )
  >- (
   rename [‘eval s (Load sh e)’] >>
   rpt strip_tac >>
   gvs[MEM_FLAT,MEM_MAP,var_cexp_def,localised_exp_simps,panSemTheory.eval_def,
       compile_exp_def, UNCURRY_EQ,
       AllCaseEqs(), SF DNF_ss] >>
   first_x_assum irule >>
   simp[PULL_EXISTS] >>
   ntac 3 $ first_assum $ irule_at $ Pos last >>
   drule var_exp_load_shape >>
   strip_tac >> fs[] >>
   metis_tac[])
  >~ [‘Load32’] >-
   (rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab", localised_exp_simps] >> rveq >>
   fs [compile_exp_def] >> rveq >>
   gvs [UNCURRY_EQ, CaseEq "shape", CaseEq "list"] >>
   simp [MEM_FLAT, MEM_MAP, var_cexp_def] >>
   rw [] >>
   fs [var_cexp_def] >>
   last_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e’ >> fs [])
  >- (
   rename [‘eval s (LoadByte e)’] >>
   rpt strip_tac >>
   gvs[panSemTheory.eval_def, AllCaseEqs(),MEM_FLAT,MEM_MAP,
       localised_exp_simps,compile_exp_def,UNCURRY_EQ,
       var_cexp_def, SF DNF_ss, PULL_EXISTS] >>
   first_x_assum irule >>
   simp[PULL_EXISTS] >>
   metis_tac[])
  >- (
   rename [‘eval s (Op op es)’] >>
   rpt strip_tac >>
   gvs[panSemTheory.eval_def, AllCaseEqs(),MEM_FLAT,MEM_MAP,
       localised_exp_simps,compile_exp_def,UNCURRY_EQ,
       var_cexp_def, SF DNF_ss, PULL_EXISTS,
       cexp_heads_eq,cexp_heads_simp_def
      ] >>
   first_x_assum irule >>
   simp[PULL_EXISTS] >>
   ntac 3 $ first_assum $ irule_at $ Pos last >>
   first_assum $ irule_at $ Pos last >>
   first_assum $ irule_at $ Pos last >>
   irule_at Any (GSYM PAIR) >>
   irule_at Any HEAD_MEM >>
   simp[GSYM PULL_EXISTS] >>
   conj_asm1_tac
   >- (CCONTR_TAC >> gvs[]) >>
   conj_asm1_tac
   >- gvs[EVERY_MEM] >>
   gvs[opt_mmap_eq_some] >>
   qpat_x_assum ‘MAP _ _ = MAP _ _’ mp_tac >>
   rw[LIST_EQ_REWRITE] >>
   gvs[MEM_EL,EL_MAP])
  >- (rpt strip_tac >>
      gvs[panSemTheory.eval_def,AllCaseEqs(),
         DefnBase.one_line_ify NONE pan_op_def,
         MAP_EQ_CONS,MEM_MAP,MEM_FLAT,compile_exp_def,
         opt_mmap_eq_some,cexp_heads_def,PULL_EXISTS,
         SF DNF_ss,var_cexp_def,localised_exp_simps
        ] >>
      rpt $ first_x_assum $ resolve_then (Pat ‘_ = (_,_)’) assume_tac $ GSYM PAIR >>
      rpt $ qpat_x_assum ‘SOME _ = _’ $ assume_tac o GSYM >>
      rpt $ first_x_assum $ drule_then $ drule_then $ drule_then $ drule >>
      rpt strip_tac >>
      metis_tac[FST,MEM]
     )
  >- (
   rpt gen_tac >> strip_tac >>
   fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
       CaseEq "word_lab"] >> rveq >>
   fs [compile_exp_def,localised_exp_simps] >> rveq >>
   fs [CaseEq "list", CaseEq "option"] >>
   rveq >> fs [MEM_FLAT, MEM_MAP, var_cexp_def] >>
   rw []
   >- (
    last_x_assum drule >>
    disch_then (qspec_then ‘ct’ mp_tac) >>
    cases_on ‘compile_exp ct e’ >> fs []) >>
   first_x_assum drule >>
   disch_then (qspec_then ‘ct’ mp_tac) >>
   cases_on ‘compile_exp ct e'’ >> fs []) >>
  rpt gen_tac >> strip_tac >>
  fs [panSemTheory.eval_def, option_case_eq, v_case_eq,
      CaseEq "word_lab"] >> rveq >>
  fs [compile_exp_def,localised_exp_simps] >> rveq >>
  fs [CaseEq "list", CaseEq "option"] >>
  rveq >> fs [MEM_FLAT, MEM_MAP, var_cexp_def] >>
  rw [] >> last_x_assum drule >>
  disch_then (qspec_then ‘ct’ mp_tac) >>
  cases_on ‘compile_exp ct e’ >> fs []
QED


Resume pc_compile_correct[Assign]:
  rpt gen_tac >>
  rpt strip_tac >>
  rename [‘Assign vk vr e’] >> Cases_on ‘vk’>>
  fs [panSemTheory.evaluate_def, oneline is_valid_value_def, localised_prog_def] >>
  fs [CaseEq "option", CaseEq "bool",panSemTheory.set_var_def] >> rveq >> fs [] >>
  rename [‘eval _ e = SOME ev’] >>
  rename [‘FLOOKUP _ vr = SOME v’] >>
  (* open compiler def *)
  fs [compile_def] >>
  pairarg_tac >> fs [] >>
  drule locals_rel_lookup_ctxt >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  fs [length_flatten_eq_size_of_shape] >>
  TOP_CASE_TAC >> fs [] >> rveq
  >- (
   ‘ALL_DISTINCT ns’
     by metis_tac [locals_rel_def, no_overlap_def] >>
   drule eval_nested_assign_distinct_eq >>
   disch_then drule >>
   strip_tac >> fs [] >>
   conj_tac
   >- fs [state_rel_def,set_var_def] >>
   fs [locals_rel_def] >>
   rpt gen_tac >> strip_tac >> fs [] >>
   cases_on ‘vr = vname’ >> fs [] >> rveq
   >- (
    pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
    fs [] >> rveq >>
    match_mp_tac opt_mmap_some_eq_zip_flookup >>
    fs [] >>
    metis_tac [all_distinct_flookup_all_distinct,
               length_flatten_eq_size_of_shape]) >>
   fs [FLOOKUP_UPDATE] >>
   last_x_assum drule >>
   strip_tac >> fs [] >>
   rfs [] >>
   drule no_overlap_flookup_distinct >>
   disch_then drule_all >>
   strip_tac >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  (* non-distinct Assign  *)
  qmatch_goalsub_abbrev_tac ‘nested_decs temps es _’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  ‘ALL_DISTINCT ns’ by metis_tac [locals_rel_def, no_overlap_def] >>
  ‘distinct_lists ns temps’ by (
    unabbrev_all_tac >>
    once_rewrite_tac [distinct_lists_commutes] >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten ev’,
                          ‘nested_seq (MAP2 Assign ns (MAP Var temps))’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  ‘MAP (eval (t with locals := t.locals |++ ZIP (temps,flatten ev)))
   (MAP Var temps) = MAP SOME (flatten ev)’ by (
    fs [MAP_MAP_o, MAP_EQ_EVERY2] >>
    fs [LIST_REL_EL_EQN] >>
    rw [] >> rfs [] >>
    ‘n < LENGTH temps’ by (
      unabbrev_all_tac >> fs [MAP_MAP_o, MAP_EQ_EVERY2]>>
      metis_tac []) >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a crepLang$exp``] EL_MAP) >>
    disch_then (qspec_then ‘Var’ assume_tac) >> fs [] >>
    fs [eval_def] >>
    metis_tac [update_eq_zip_flookup]) >>
  drule eval_nested_assign_distinct_eq >>
  disch_then (qspec_then ‘ns’ mp_tac) >>
  disch_then (qspec_then ‘flatten v’ mp_tac) >>
  impl_tac
  >- (
   fs [map_var_cexp_eq_var] >>
   fs [Once distinct_lists_commutes] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten ev’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape]) >>
  strip_tac >> fs [] >>
  rveq >>
  fs [state_rel_def] >>
  fs [locals_rel_def] >>
  rw [] >> fs [] >>
  (* writing in this style for druling below *)
  ‘DISJOINT (set (MAP FST (ZIP (temps,flatten ev))))
   (set (MAP FST (ZIP (ns,flatten ev))))’ by (
    ‘LENGTH ns = LENGTH (flatten ev)’ by
      fs [length_flatten_eq_size_of_shape] >>
    fs [GSYM length_flatten_eq_size_of_shape, MAP_ZIP] >>
    fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
    metis_tac []) >>
  drule FUPDATE_LIST_APPEND_COMMUTES >>
  disch_then (qspec_then ‘t.locals’ assume_tac) >>
  fs [] >>
  pop_assum kall_tac >>
  pop_assum kall_tac >>
  cases_on ‘vr = vname’ >> fs [] >> rveq
  >- (
   pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
   fs [] >> rveq >>
   fs [opt_mmap_eq_some] >>
   fs [Once distinct_lists_commutes] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten ev’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals |++ ZIP (ns,flatten ev)’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape] >>
   strip_tac >>
   fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >> rfs [] >>
   ‘n < LENGTH ns’ by metis_tac [] >>
   metis_tac [update_eq_zip_flookup]) >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  rfs [] >>
  fs [opt_mmap_eq_some] >>
  ‘distinct_lists temps ns'’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``]
         flookup_res_var_zip_distinct) >>
  disch_then (qspecl_then [‘flatten ev’,
                           ‘MAP (FLOOKUP t.locals) temps’,
                           ‘t.locals |++ ZIP (ns,flatten ev)’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >>
  drule no_overlap_flookup_distinct >>
  disch_then drule_all >>
  strip_tac >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >> rfs [] >>
  qpat_x_assum ‘LENGTH _ = LENGTH _’ (assume_tac o GSYM) >>
  fs [] >>
  last_x_assum drule >> strip_tac >>
  ‘~MEM (EL n ns') ns’ by (
    fs [Once distinct_lists_commutes] >>
    fs [distinct_lists_def, EVERY_MEM, EL_MEM]) >>
  metis_tac [flookup_fupdate_zip_not_mem]
QED

Theorem eval_map_comp_exp_flat_eq:
  !argexps args s t ctxt. MAP (eval s) argexps = MAP SOME args /\
  state_rel s t ∧ code_rel ctxt s.code t.code ∧
  locals_rel ctxt s.locals t.locals ∧ EVERY localised_exp argexps ==>
   MAP (eval t) (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) =
        MAP SOME (FLAT (MAP flatten args))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (cases_on ‘args’ >> fs []) >>
  cases_on ‘args’ >> fs [] >>
  fs [MAP_APPEND] >>
  cases_on ‘compile_exp ctxt h’ >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  last_x_assum (qspecl_then [‘t'’] mp_tac) >>
  fs [] >>
  disch_then drule_all >>
  fs []
QED


Theorem eval_map_var_cexp_present_ctxt:
  ∀es vs s t ctxt.
    MAP (eval s) es = MAP SOME vs ∧
    state_rel s t ∧ code_rel ctxt s.code t.code ∧
    locals_rel ctxt s.locals t.locals ∧ EVERY localised_exp es ⇒
    ∀n. MEM n (FLAT (MAP var_cexp
                       (FLAT (MAP FST (MAP (compile_exp ctxt) es))))) ⇒
        ∃vname shp ns.
          FLOOKUP ctxt.vars vname = SOME (shp, ns) ∧ MEM n ns
Proof
  Induct >> rpt strip_tac >> fs [] >>
  Cases_on ‘vs’ >> fs [] >>
  Cases_on ‘compile_exp ctxt h’ >> fs [] >>
  rename1 ‘MEM nn (FLAT _)’ >>
  fs [MEM_APPEND]
  >- metis_tac [eval_var_cexp_present_ctxt]
  >> metis_tac []
QED

Theorem pan_primop_crep_primop:
  ∀pop vs value.
    pan_primop pop vs = SOME value ⇒
    crep_primop pop (FLAT (MAP flatten vs)) = SOME (flatten value)
Proof
  Cases >> rpt strip_tac >>
  gvs [panSemTheory.pan_primop_def, AllCaseEqs(),
       LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
  rename1 ‘flatten v0 ++ flatten v1 ++ flatten v2’ >>
  Cases_on ‘v0’ >> Cases_on ‘v1’ >> Cases_on ‘v2’ >>
  gvs [panSemTheory.isValWord_def] >>
  rename1 ‘flatten (Val w0) ++ flatten (Val w1) ++ flatten (Val w2)’ >>
  Cases_on ‘w0’ >> Cases_on ‘w1’ >> Cases_on ‘w2’ >>
  gvs [panSemTheory.isValWord_def] >>
  pairarg_tac >>
  gvs [panSemTheory.theValWord_def, flatten_def,
       crep_primop_def, isWord_def, theWord_def]
QED

Resume pc_compile_correct[Primitive]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, localised_prog_def] >>
  gvs [AllCaseEqs(),
       oneline panSemTheory.is_valid_value_def,
       panSemTheory.set_var_def] >>
  rename1 ‘OPT_MMAP (eval _) es = SOME vs’ >>
  rename1 ‘pan_primop pop vs = SOME value’ >>
  rename1 ‘Primitive v _ _’ >>
  Cases_on ‘FLOOKUP s.locals v’ >> gvs [] >>
  rename [‘FLOOKUP s.locals v = SOME oldv’] >>
  fs [compile_def] >>
  drule locals_rel_lookup_ctxt >>
  disch_then drule >>
  strip_tac >> fs [] >>
  rename [‘FLOOKUP ctxt.vars v = SOME (shape_of oldv, ns)’] >>
  qpat_x_assum ‘OPT_MMAP (eval _) _ = SOME _’
    (strip_assume_tac o REWRITE_RULE [opt_mmap_eq_some]) >>
  mp_tac (Q.SPECL [`es`, `vs`, `s`, `t`, `ctxt`]
                  eval_map_comp_exp_flat_eq) >>
  impl_tac >- fs [] >>
  disch_tac >>
  qmatch_goalsub_abbrev_tac `nested_decs temps ces _` >>
  `ALL_DISTINCT temps /\ LENGTH ces = LENGTH temps` by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  `distinct_lists temps (FLAT (MAP var_cexp ces))` by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_map_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >> rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    res_tac >> fs []) >>
  `ALL_DISTINCT ns` by metis_tac [locals_rel_def, no_overlap_def] >>
  `distinct_lists ns temps` by (
    unabbrev_all_tac >>
    once_rewrite_tac [distinct_lists_commutes] >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  `LENGTH ns = LENGTH (flatten value)`
    by gvs [length_flatten_eq_size_of_shape] >>
  `LENGTH temps = LENGTH (FLAT (MAP flatten vs))` by (
    `LENGTH ces = LENGTH (FLAT (MAP flatten vs))`
      by metis_tac [LENGTH_MAP] >>
    fs []) >>
  `distinct_lists temps ns`
    by metis_tac [distinct_lists_commutes] >>
  `OPT_MMAP (FLOOKUP (t.locals |++ ZIP (temps,FLAT (MAP flatten vs)))) ns =
   SOME (flatten oldv)` by (
    mp_tac (INST_TYPE [``:'a``|->``:num``, ``:'b``|->``:'a word_lab``]
                      opt_mmap_disj_zip_flookup) >>
    disch_then (qspecl_then [`temps`, `t.locals`, `ns`,
                             `FLAT (MAP flatten vs)`] mp_tac) >>
    fs []) >>
  `evaluate (Primitive ns pop temps,
             t with locals := t.locals |++ ZIP (temps,FLAT (MAP flatten vs))) =
   (NONE, t with locals :=
     (t.locals |++ ZIP (temps,FLAT (MAP flatten vs))) |++
     ZIP (ns, flatten value))` by (
    simp [crepSemTheory.evaluate_def] >>
    qspecl_then [`temps`, `t.locals`, `FLAT (MAP flatten vs)`]
                mp_tac opt_mmap_some_eq_zip_flookup >>
    impl_tac >- fs [] >>
    strip_tac >> simp [] >>
    drule pan_primop_crep_primop >> strip_tac >> simp [] >>
    `EVERY (\v. IS_SOME (FLOOKUP (t.locals |++ ZIP (temps,FLAT (MAP flatten vs))) v)) ns` by (
      gvs [EVERY_MEM, opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL] >>
      rw [] >>
      first_x_assum (qspec_then `n` mp_tac) >>
      simp [EL_MAP]) >>
    simp []) >>
  drule eval_nested_decs_seq_res_var_eq >>
  disch_then (qspecl_then [`temps`, `Primitive ns pop temps`] mp_tac) >>
  impl_tac >- fs [] >>
  simp [] >> strip_tac >>
  `DISJOINT (set (MAP FST (ZIP (temps,FLAT (MAP flatten vs)))))
   (set (MAP FST (ZIP (ns,flatten value))))` by (
    fs [MAP_ZIP] >>
    fs [distinct_lists_def, IN_DISJOINT, EVERY_MEM] >>
    metis_tac []) >>
  drule FUPDATE_LIST_APPEND_COMMUTES >>
  disch_then (qspec_then `t.locals` assume_tac) >>
  fs [] >>
  pop_assum kall_tac >>
  fs [state_rel_def] >>
  fs [locals_rel_def] >>
  rw [] >> fs [] >>
  cases_on `v = vname` >> fs [] >> rveq
  >- (
   pop_assum (assume_tac o REWRITE_RULE [FLOOKUP_DEF]) >>
   fs [] >> rveq >>
   drule (INST_TYPE [``:'a``|->``:num``, ``:'b``|->``:'a word_lab``]
                    flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [`FLAT (MAP flatten vs)`,
                            `MAP (FLOOKUP t.locals) temps`,
                            `t.locals |++ ZIP (ns,flatten v')`] mp_tac) >>
   fs [] >>
   strip_tac >>
   gvs [opt_mmap_eq_some, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   qspecl_then [`ns`, `t.locals`, `flatten v'`, `n`] mp_tac
              (INST_TYPE [``:'a``|->``:num``, ``:'b``|->``:'a word_lab``]
                         update_eq_zip_flookup) >>
   simp []) >>
  fs [FLOOKUP_UPDATE] >>
  last_x_assum drule >>
  strip_tac >> fs [] >>
  rfs [] >>
  fs [opt_mmap_eq_some] >>
  `distinct_lists temps ns'` by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    metis_tac [locals_rel_def, ctxt_max_def]) >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``]
         flookup_res_var_zip_distinct) >>
  disch_then (qspecl_then [`FLAT (MAP flatten vs)`,
                           `MAP (FLOOKUP t.locals) temps`,
                           `t.locals |++ ZIP (ns,flatten value)`] mp_tac) >>
  fs [] >>
  strip_tac >>
  drule no_overlap_flookup_distinct >>
  disch_then drule_all >>
  strip_tac >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >> rfs [] >>
  qpat_x_assum `LENGTH _ = LENGTH _` (assume_tac o GSYM) >>
  fs [] >>
  last_x_assum drule >> strip_tac >>
  `~MEM (EL n ns') ns` by (
    fs [Once distinct_lists_commutes] >>
    fs [distinct_lists_def, EVERY_MEM, EL_MEM]) >>
  metis_tac [flookup_fupdate_zip_not_mem]
QED

Theorem not_mem_context_assigned_mem_gt:
  !ctxt p x.
   ctxt_max ctxt.vmax ctxt.vars /\
   (!v sh ns'. FLOOKUP ctxt.vars v = SOME (sh, ns') ==> ~MEM x ns') ∧
   x <= ctxt.vmax  ==>
   ~MEM x (assigned_free_vars (compile ctxt p))
Proof
  ho_match_mp_tac compile_ind >> rw []
  >- fs [compile_def, assigned_free_vars_def]
  >- (fs [compile_def, assigned_free_vars_def] >>
      pairarg_tac >> fs [] >> rveq >>
      FULL_CASE_TAC >> fs [assigned_free_vars_def] >>
      qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
      ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
      drule assigned_free_vars_nested_decs_append >>
      qmatch_goalsub_abbrev_tac ‘compile nctxt p’ >>
      disch_then (qspec_then ‘compile nctxt p’ assume_tac) >>
      rw [MEM_FILTER,DISJ_EQ_IMP] >>
      last_x_assum match_mp_tac >>
      gvs[ctxt_max_def] >> rw[FLOOKUP_UPDATE,Abbr ‘dvs’] \\ gvs[MEM_GENLIST] \\
      res_tac \\ DECIDE_TAC)
  >- (
   fs [compile_def, assigned_free_vars_def] >>
   pairarg_tac >> fs [] >> rveq >>
   FULL_CASE_TAC >> fs [assigned_free_vars_def] >>
   FULL_CASE_TAC >> FULL_CASE_TAC >> fs []
   >- (
    FULL_CASE_TAC >> fs [assigned_free_vars_def] >>
    drule nested_seq_assigned_free_vars_eq >>
    fs [] >> res_tac >> fs []) >>
   FULL_CASE_TAC >> fs [assigned_free_vars_def] >>
   qmatch_goalsub_abbrev_tac ‘nested_decs dvs es’ >>
   ‘LENGTH dvs = LENGTH es’ by (unabbrev_all_tac >> fs []) >>
   drule assigned_free_vars_nested_decs_append >>
   disch_then (qspec_then ‘nested_seq (MAP2 Assign r (MAP Var dvs))’ assume_tac) >>
   fs [] >>
   rw[MEM_FILTER,DISJ_EQ_IMP] >>
   ‘LENGTH r = LENGTH (MAP Var dvs)’ by fs [Abbr ‘dvs’, LENGTH_GENLIST] >>
   drule nested_seq_assigned_free_vars_eq >>
   fs [] >> res_tac >> fs [])
  >- (gvs[assigned_free_vars_def,compile_def])
  >- (fs [compile_def] >>
      TOP_CASE_TAC >> gvs [assigned_free_vars_def] >>
      TOP_CASE_TAC >> gvs [] >>
      qmatch_goalsub_abbrev_tac `nested_decs dvs ces` >>
      `LENGTH dvs = LENGTH ces` by
        (unabbrev_all_tac >> fs [LENGTH_GENLIST]) >>
      drule assigned_free_vars_nested_decs_append >>
      qmatch_goalsub_abbrev_tac `nested_decs _ _ pp` >>
      disch_then (qspec_then `pp` assume_tac) >>
      gvs [Abbr `pp`, assigned_free_vars_def, MEM_FILTER, DISJ_EQ_IMP] >>
      metis_tac [])
  >- (
   fs [compile_def] >>
   rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
   pairarg_tac >> rw [] >>
   fs [nested_decs_def] >>
   fs [assigned_free_vars_def] >>
   rw[MEM_FILTER,DISJ_EQ_IMP] >>
   dep_rewrite.DEP_ONCE_REWRITE_TAC[assigned_free_vars_nested_decs_append] >>
   rw[MEM_FILTER,DISJ_EQ_IMP] >>
   gvs[MEM_GENLIST] >>
   gvs[assigned_free_vars_seq_store_empty])
  >- (
   fs [compile_def] >>
   rpt (TOP_CASE_TAC >> fs [assigned_free_vars_def]))
  >- (
   fs [compile_def] >>
   rpt (TOP_CASE_TAC >> fs [assigned_free_vars_def]))
  >- (
   fs [compile_def] >>
   pairarg_tac >> fs[] >>
   ntac 4 (TOP_CASE_TAC >> fs [assigned_free_vars_def]) >>
   dep_rewrite.DEP_ONCE_REWRITE_TAC[assigned_free_vars_nested_decs_append] \\
   rw[MEM_FILTER,DISJ_EQ_IMP] \\
   fs [assigned_free_vars_store_globals_empty])
  >- (
   fs [compile_def] >>
   pairarg_tac >> fs [] >>
   ntac 2 (TOP_CASE_TAC >> fs [assigned_free_vars_def]) >>
   dep_rewrite.DEP_ONCE_REWRITE_TAC[assigned_free_vars_nested_decs_append] \\
   rw[MEM_FILTER,DISJ_EQ_IMP] \\
   fs [assigned_free_vars_store_globals_empty])
  >- (fs [compile_def,assigned_free_vars_def] >>
      metis_tac[])
  >- (fs [compile_def,assigned_free_vars_def] >>
      rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
      metis_tac[])
  >- (fs [compile_def,assigned_free_vars_def] >>
      rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
      metis_tac[])
  >- (fs [compile_def,assigned_free_vars_def] >>
      rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
      metis_tac[])
  >- (fs [compile_def,assigned_free_vars_def] >>
      rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
      metis_tac[])
  >- suspend "Call"
  >- suspend "DecCall"
  >- (gvs[compile_def] \\
      rpt(pairarg_tac \\ gvs[]) \\
      rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]))
  >- (gvs[compile_def]>>
       rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def])>>
       res_tac >> fs[])
  >- (gvs[compile_def]>>
       rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def])>>
       res_tac >> fs[])>>
  gvs[compile_def,assigned_free_vars_def]
QED

Resume not_mem_context_assigned_mem_gt[Call]:
  fs [compile_def,assigned_free_vars_def] >>
  rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def, nested_decs_def])
  >>~ [`assigned_free_vars (nested_decs _ _ _)`]
  >- (
    DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append]
    >> conj_tac >- fs[LENGTH_GENLIST, LENGTH_REPLICATE]
    >> fs[MEM_FILTER] >> disj2_tac >> fs[assigned_free_vars_def]
    >> metis_tac[NOT_LE, mem_genlist_add_suc_val]
  )
  >- (
    DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append]
    >> conj_tac >- fs[LENGTH_GENLIST, LENGTH_REPLICATE]
    >> fs[MEM_FILTER] >> disj2_tac >> fs[assigned_free_vars_def]
    >> metis_tac[NOT_LE, mem_genlist_add_suc_val]
  )
  >- (
    DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append]
    >> conj_tac >- fs[LENGTH_GENLIST, LENGTH_REPLICATE]
    >> fs[MEM_FILTER] >> disj2_tac >> fs[assigned_free_vars_def]
    >> rpt conj_tac
    >- metis_tac[NOT_LE, mem_genlist_add_suc_val]
    >- (
      gvs[exp_hdl_def] \\
       rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
       dep_rewrite.DEP_ONCE_REWRITE_TAC[nested_seq_assigned_free_vars_eq] \\
       gvs[length_load_globals_eq_read_size] \\
       metis_tac[])
    >> metis_tac[]
  )
  >> rpt conj_tac
  >>~- ([`assigned_free_vars (exp_hdl _ _)`],
   gvs[exp_hdl_def] \\
   rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def]) \\
   dep_rewrite.DEP_ONCE_REWRITE_TAC[nested_seq_assigned_free_vars_eq] \\
   gvs[length_load_globals_eq_read_size] \\
   metis_tac[]
  )
  >>~- ([`wrap_rt _ = SOME _`],
    gvs[wrap_rt_def, CaseEq "option", CaseEq "shape", CaseEq "list", CaseEq "prod"]
    >> metis_tac[MEM])
  >> metis_tac[]
QED

Theorem filter_not_mem_self:
  FILTER (\x. ~MEM x l) l = []
Proof
  Induct_on `l` >> rw[GSYM FILTER_FILTER]
QED

Resume not_mem_context_assigned_mem_gt[DecCall]:
  fs[compile_def, assigned_free_vars_def]
  \\ rpt(PURE_TOP_CASE_TAC \\ gvs[assigned_free_vars_def, nested_decs_def])
  >- (
    DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append]
    >> conj_tac >> fs[LENGTH_GENLIST, LENGTH_REPLICATE, MEM_FILTER]
    >> disj2_tac
    >> fs[assigned_free_vars_def]
    >> conj_tac
    >- (
      rpt strip_tac
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    ) >>
    last_x_assum irule >>
    rw[FLOOKUP_UPDATE] >>
    rw[MEM_GENLIST] >>
    res_tac >>
    gvs[ctxt_max_def] >>
    rw[FLOOKUP_UPDATE] >>
    gvs[MEM_GENLIST] >>
    res_tac >>
    simp[]
  )
  >> DEP_REWRITE_TAC[assigned_free_vars_nested_decs_append]
  >> conj_tac
  >> fs[LENGTH_GENLIST, LENGTH_REPLICATE, MEM_FILTER]
  >> disj2_tac \\ fs[assigned_free_vars_def]
  >> conj_tac
  >> gvs[wrap_rt_def, CaseEq "option", CaseEq "shape", CaseEq "list"]
  >>~- ([`~MEM _ (GENLIST _ _)`],
    metis_tac[NOT_LE, mem_genlist_add_suc_val]) >>
  last_x_assum irule >>
  rw[FLOOKUP_UPDATE] >>
  rw[MEM_GENLIST] >>
  res_tac >>
  gvs[ctxt_max_def] >>
  rw[FLOOKUP_UPDATE] >>
  gvs[MEM_GENLIST] >>
  res_tac >>
  simp[]
QED

Finalise not_mem_context_assigned_mem_gt;

Theorem rewritten_context_unassigned:
 !p nctxt v ctxt ns nvars sh sh'.
  nctxt = ctxt with
   <|vars := ctxt.vars |+ (v,sh,nvars);
     vmax  := ctxt.vmax + size_of_shape sh|> /\
  FLOOKUP ctxt.vars v = SOME (sh',ns) /\
  no_overlap ctxt.vars /\
  ctxt_max ctxt.vmax ctxt.vars /\
  no_overlap nctxt.vars ∧
  ctxt_max nctxt.vmax nctxt.vars /\
  distinct_lists nvars ns ==>
  distinct_lists ns (assigned_free_vars (compile nctxt p))
Proof
  rw [] >> fs [] >>
  fs [distinct_lists_def] >>
  rw [] >>
  fs [EVERY_MEM] >> rw []>>
  CCONTR_TAC >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘compile nctxt p’ >>
  assume_tac not_mem_context_assigned_mem_gt >>
  pop_assum (qspecl_then [‘nctxt’, ‘p’, ‘x’] mp_tac) >>
  impl_tac
  >- (
   unabbrev_all_tac >> fs[context_component_equality] >>
   rw [FLOOKUP_UPDATE]  >- metis_tac []
   >- (
    fs [no_overlap_def] >>
    first_x_assum (qspecl_then [‘v’, ‘v'’] mp_tac) >>
    fs [FLOOKUP_UPDATE] >>
    metis_tac [IN_DISJOINT]) >>
   fs [ctxt_max_def] >>
   res_tac >> fs [] >>
   DECIDE_TAC) >>
  fs []
QED

Theorem ctxt_max_el_leq:
  ctxt_max ctxt.vmax ctxt.vars /\
  FLOOKUP ctxt.vars v = SOME (sh,ns) /\
  n < LENGTH ns ==> EL n ns <= ctxt.vmax
Proof
  rw [ctxt_max_def] >>
  first_x_assum drule >>
  disch_then (qspec_then ‘EL n ns’ assume_tac) >>
  drule EL_MEM >>
  fs []
QED


Resume pc_compile_correct[Dec]:
  rpt gen_tac >>
  rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [CaseEq "option", localised_prog_def, bool_case_eq] >>
  pairarg_tac >> fs [] >>
  rveq >>
  fs [compile_def] >>
  pairarg_tac >> fs [] >>
  rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >> rveq >>
  qmatch_goalsub_abbrev_tac ‘nested_decs nvars es _’ >>
  ‘ALL_DISTINCT nvars ∧ LENGTH nvars = LENGTH es’ by (
    unabbrev_all_tac >>
    fs [length_flatten_eq_size_of_shape, LENGTH_GENLIST,
        ALL_DISTINCT_GENLIST]) >>
  ‘distinct_lists nvars (FLAT (MAP var_cexp es))’ by (
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_ _ _ p, _)’ >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘nvars’, ‘t’,
                          ‘flatten value’, ‘p’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  last_x_assum (qspecl_then [‘t with locals := t.locals |++ ZIP (nvars,flatten value)’,
                             ‘ctxt with <|vars := ctxt.vars |+ (v,shape_of value,nvars);
                               vmax := ctxt.vmax + size_of_shape (shape_of value)|>’ ]
                mp_tac) >>
  impl_tac
  >- (
   fs [state_rel_def] >>
   conj_tac >- (fs [code_rel_def] >> metis_tac[]) >>
   fs [locals_rel_def] >>
   conj_tac
   >- (
    fs [no_overlap_def] >>
    conj_tac
    >- (
     rw [] >>
     cases_on ‘x = v’ >> fs [FLOOKUP_UPDATE] >>
     metis_tac []) >>
    rw [] >>
    cases_on ‘x = v’ >> cases_on ‘y = v’ >> fs [FLOOKUP_UPDATE] >>
    rveq
    >- (
     qsuff_tac ‘distinct_lists nvars ys’
     >- (
      fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
      metis_tac []) >>
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    qsuff_tac ‘distinct_lists nvars xs’
    >- (
     fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
     metis_tac []) >>
    unabbrev_all_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    fs [ctxt_max_def] >> res_tac >> fs []) >>
   conj_tac
   >- (
    fs [ctxt_max_def]  >> rw [] >>
    cases_on ‘v = v'’ >>  fs [FLOOKUP_UPDATE] >> rveq
    >- (
     unabbrev_all_tac >>
     fs [MEM_GENLIST]) >>
    res_tac >> fs [] >> DECIDE_TAC) >>
   rw [] >>
   cases_on ‘v = vname’ >>  fs [FLOOKUP_UPDATE] >> rveq
   >- (
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``]
           opt_mmap_some_eq_zip_flookup) >>
    disch_then (qspecl_then [‘t.locals’, ‘flatten v'’] mp_tac) >>
    fs [length_flatten_eq_size_of_shape]) >>
   res_tac >> fs [] >>
   ‘distinct_lists nvars ns’ by (
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          opt_mmap_disj_zip_flookup) >>
   disch_then (qspecl_then [‘t.locals’, ‘flatten value’] mp_tac) >>
   fs [length_flatten_eq_size_of_shape])  >>
  strip_tac >> unabbrev_all_tac >> fs [] >> rveq >>
  conj_tac >- fs [state_rel_def] >>
  conj_tac >- (fs [code_rel_def] >> metis_tac[]) >>
  cases_on ‘res = NONE ∨ res = SOME Continue ∨ res = SOME Break’ >>
  fs [] >> rveq >> rfs [] >>
  TRY
  (qmatch_goalsub_abbrev_tac ‘ZIP (nvars, _)’ >>
   qmatch_asmsub_abbrev_tac ‘locals_rel nctxt st.locals r.locals’ >>
   rewrite_tac [locals_rel_def] >>
   conj_tac >- fs [locals_rel_def] >>
   conj_tac >- fs [locals_rel_def] >>
   rw [] >>
   reverse (cases_on ‘v = vname’) >> fs [] >> rveq
   >- (
    drule (INST_TYPE [``:'a``|->``:mlstring``,
                      ``:'b``|->``:'a v``] flookup_res_var_diff_eq_org) >>
    disch_then (qspecl_then [‘FLOOKUP s.locals v’, ‘st.locals’] (mp_tac o GSYM)) >>
    fs [] >> strip_tac >>
    fs [locals_rel_def] >> rfs [] >>
    first_x_assum drule_all >> strip_tac >> fs [] >>
    fs [Abbr ‘nctxt’] >>
    fs [FLOOKUP_UPDATE] >> rfs [] >>
    fs [opt_mmap_eq_some] >>
    ‘distinct_lists nvars ns’ by (
      fs [Abbr ‘nvars’] >> ho_match_mp_tac genlist_distinct_max >>
      rw [] >> fs [ctxt_max_def] >> res_tac >> fs []) >>
    drule (INST_TYPE [``:'a``|->``:num``,
                      ``:'b``|->``:'a word_lab``] flookup_res_var_distinct) >>
    disch_then (qspecl_then [‘MAP (FLOOKUP t.locals) nvars’,
                             ‘r.locals’] mp_tac) >>
    fs [LENGTH_MAP]) >>
   drule flookup_res_var_some_eq_lookup >>
   strip_tac >>
   qpat_x_assum ‘locals_rel ctxt s.locals t.locals’ mp_tac >>
   rewrite_tac [locals_rel_def] >>
   strip_tac >> fs [] >>
   pop_assum drule  >>
   strip_tac >> fs [] >>
   ‘distinct_lists nvars ns’ by (
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
   fs [opt_mmap_eq_some] >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_distinct) >>
   disch_then (qspecl_then [‘MAP (FLOOKUP t.locals) nvars’,
                            ‘r.locals’] mp_tac) >>
   fs [LENGTH_MAP] >>
   strip_tac >>
   pop_assum kall_tac >>
   assume_tac rewritten_context_unassigned >>
   fs [] >>
   first_x_assum drule >>
   disch_then (qspecl_then [‘prog’, ‘nvars’,
                            ‘shape_of value’] mp_tac) >>
   fs [] >>
   impl_tac
   >- (
    conj_tac
    >- (
     fs [no_overlap_def] >>
     rw []
     >- (cases_on ‘x = v’ >> fs [FLOOKUP_UPDATE] >> metis_tac []) >>
     rw [] >>
     cases_on ‘x = v’ >> cases_on ‘y = v’ >> fs [FLOOKUP_UPDATE] >>
     rveq
     >- (
      qsuff_tac ‘distinct_lists nvars ys’
      >- (
       fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
       metis_tac []) >>
      unabbrev_all_tac >>
      ho_match_mp_tac genlist_distinct_max >>
      rw [] >>
      fs [ctxt_max_def] >> res_tac >> fs []) >>
     qsuff_tac ‘distinct_lists nvars xs’
     >- (
      fs [distinct_lists_def, IN_DISJOINT, EVERY_DEF, EVERY_MEM] >>
      metis_tac []) >>
     unabbrev_all_tac >>
     ho_match_mp_tac genlist_distinct_max >>
     rw [] >>
     fs [ctxt_max_def] >> res_tac >> fs []) >>
    fs [ctxt_max_def] >> rw [] >>
    cases_on ‘v = v''’ >>  fs [FLOOKUP_UPDATE] >> rveq
    >- (
     unabbrev_all_tac >>
     fs [MEM_GENLIST]) >>
    res_tac >> fs [] >> DECIDE_TAC) >>
   rewrite_tac [distinct_lists_def] >>
   strip_tac >> fs [EVERY_MEM] >>
   fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
   rw [] >>
   first_x_assum (qspec_then ‘EL n ns’ mp_tac) >>
   fs [EL_MEM] >>
   strip_tac >>
   drule unassigned_vars_evaluate_same >> fs [] >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [] >>
   ‘LENGTH nvars = LENGTH (flatten value)’ by (
     unabbrev_all_tac >> fs [LENGTH_GENLIST]) >>
   drule flookup_fupdate_zip_not_mem >>
   fs [Once distinct_lists_commutes] >>
   disch_then (qspecl_then [‘t.locals’, ‘EL n ns’] mp_tac) >>
   fs [distinct_lists_def, EVERY_MEM] >>
   impl_tac >- metis_tac [EL_MEM] >> fs [] >> NO_TAC) >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  rw [] >> fs [globals_lookup_def]
QED

Resume pc_compile_correct[Store]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab"] >>
  rveq >>
  fs [compile_def,localised_prog_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘stores (Var ad) (MAP Var temps) _’ >>
  ‘ALL_DISTINCT (ad::temps) ∧ LENGTH (ad::temps) = LENGTH (h::es)’ by (
    unabbrev_all_tac >>
    fs [length_flatten_eq_size_of_shape, LENGTH_GENLIST,
        ALL_DISTINCT_GENLIST, MEM_GENLIST]) >>
  ‘distinct_lists (ad::temps) (FLAT (MAP var_cexp (h::es)))’ by (
    unabbrev_all_tac >> fs [MAP] >>
    ‘ctxt.vmax + 1:: GENLIST (λx. SUC x + (ctxt.vmax + 1)) (LENGTH es) =
     GENLIST (λx. SUC x + ctxt.vmax) (SUC(LENGTH es))’ by (
     fs [GENLIST_CONS, o_DEF] >> fs [GENLIST_FUN_EQ])>>
    fs [] >> pop_assum kall_tac >>
    ho_match_mp_tac genlist_distinct_max >>
    rw []
    >- (
     qpat_x_assum ‘compile_exp _ src = (_,_)’ mp_tac >>
     qpat_x_assum ‘eval _ src = _’ mp_tac >>
     drule eval_var_cexp_present_ctxt >>
     ntac 3 (disch_then drule) >>
     fs [MAP] >> disch_then drule >>
     rw [] >> fs [] >>
     rfs [] >>
     fs [locals_rel_def, ctxt_max_def] >>
     first_x_assum drule >> fs []) >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘evaluate (_ _ _ p, _)’ >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘h::es’, ‘ad::temps’, ‘t’,
                          ‘Word addr::flatten value’, ‘p’] mp_tac) >>
  impl_tac >- fs [] >>
  fs [] >>
  pairarg_tac >> fs [] >> rveq >>
  strip_tac >>
  pop_assum kall_tac >>
  fs [state_rel_def] >>
  fs [Abbr ‘p’] >>
  assume_tac evaluate_seq_stores_mem_state_rel >>
  pop_assum (qspecl_then [‘temps’, ‘flatten value’, ‘ad’ ,‘0w’, ‘t’,
                          ‘q’, ‘r’, ‘addr’, ‘m’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >>
  drule evaluate_seq_stroes_locals_eq >> strip_tac >> fs [] >>
  rfs [] >>
  gs [GSYM length_flatten_eq_size_of_shape] >>
  cases_on ‘FLOOKUP t.locals ad’
  >- (
   fs [res_var_def] >>
   fs [FUPDATE_LIST_THM] >>
   ‘~MEM ad (MAP FST (ZIP (temps,flatten value)))’ by (
     drule MAP_ZIP >>
     strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘Word addr’, ‘t.locals’] assume_tac) >>
   fs []  >>
   qpat_x_assum ‘~MEM ad temps’ assume_tac >>
   drule_all domsub_commutes_fupdate >>
   disch_then (qspec_then ‘t.locals’ assume_tac) >>
   fs [] >> pop_assum kall_tac >>
   fs [flookup_thm] >>
   drule DOMSUB_NOT_IN_DOM >> strip_tac >> fs [] >>
   fs [locals_rel_def] >> rw [] >>
   last_x_assum drule >> strip_tac >> fs [] >>
   fs [opt_mmap_eq_some] >>
   ‘distinct_lists temps ns’ by (
     unabbrev_all_tac >>
     once_rewrite_tac [ADD_COMM] >> fs [] >>
     ho_match_mp_tac genlist_distinct_max' >>
     metis_tac [locals_rel_def, ctxt_max_def]) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten value’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >>
   fs []) >>
  fs [res_var_def] >>
  fs [FUPDATE_LIST_THM] >>
  ‘~MEM ad (MAP FST (ZIP (temps,flatten value)))’ by (
    drule MAP_ZIP >>
    strip_tac >> fs []) >>
   drule FUPDATE_FUPDATE_LIST_COMMUTES >>
   disch_then (qspecl_then [‘x’, ‘t.locals |+ (ad,Word addr)’] assume_tac o GSYM) >>
   fs [flookup_thm] >>
   drule_all FUPDATE_ELIM >>
   strip_tac >> fs [] >>
   fs [locals_rel_def] >> rw [] >>
   last_x_assum drule >> strip_tac >> fs [] >>
   fs [opt_mmap_eq_some] >>
   ‘distinct_lists temps ns’ by (
     unabbrev_all_tac >>
     once_rewrite_tac [ADD_COMM] >> fs [] >>
     ho_match_mp_tac genlist_distinct_max' >>
     metis_tac [locals_rel_def, ctxt_max_def]) >>
   drule (INST_TYPE [``:'a``|->``:num``,
                     ``:'b``|->``:'a word_lab``]
          flookup_res_var_zip_distinct) >>
   disch_then (qspecl_then [‘flatten value’,
                            ‘MAP (FLOOKUP t.locals) temps’,
                            ‘t.locals’] mp_tac) >>
   impl_tac >- fs [] >>
   strip_tac >>
   fs []
QED

Resume pc_compile_correct[Store32]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab",
      localised_prog_def] >>
  rveq >>
  fs [compile_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  TOP_CASE_TAC >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  fs [flatten_def] >> rveq >>
  fs [evaluate_def] >> TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [state_rel_def]
QED
Resume pc_compile_correct[StoreByte]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "v", CaseEq "word_lab"] >>
  rveq >>
  fs [compile_def, localised_prog_def] >>
  TOP_CASE_TAC >>
  qpat_x_assum ‘eval s src = _’ mp_tac >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  TOP_CASE_TAC >> fs [flatten_def] >> rveq >>
  strip_tac >>
  TOP_CASE_TAC >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [shape_of_def] >> rveq >>
  fs [panLangTheory.size_of_shape_def] >>
  fs [flatten_def] >> rveq >>
  fs [evaluate_def] >> TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  fs [state_rel_def]
QED

Theorem shape_of_alt:
  ∀x. shape_of(Val x) = One
Proof
  Cases >> rw[panSemTheory.shape_of_def]
QED

Resume pc_compile_correct[ShMemLoad]:
  rpt gen_tac >> rpt strip_tac >>
  rename1 ‘ShMemLoad _ vk’ >> Cases_on ‘vk’ >>
  gvs[AllCaseEqs(),panSemTheory.evaluate_def,compile_def,
      oneline nb_op_def,
      panSemTheory.nb_op_def,panSemTheory.sh_mem_load_def,
      panSemTheory.sh_mem_store_def,panLangTheory.size_of_shape_def,
      asmTheory.is_load_def,panLangTheory.load_op_def,
      localised_prog_def
      ] >>
  PURE_TOP_CASE_TAC >>
  imp_res_tac compile_exp_val_rel >>
  imp_res_tac locals_rel_lookup_ctxt >>
  gvs[shape_of_def,panLangTheory.size_of_shape_def,
      quantHeuristicsTheory.LIST_LENGTH_1,
      flatten_def,panSemTheory.shape_of_def,
      crepSemTheory.evaluate_def
     ] >>
  qpat_x_assum ‘_ = eval _ _’ $ assume_tac o GSYM >>
  rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
  gvs[sh_mem_op_def,
      sh_mem_load_def,
      panLangTheory.load_op_def,
      crepSemTheory.evaluate_def
     ] >>
  gvs[state_rel_def,
      panSemTheory.set_kvar_def,
      panSemTheory.set_var_def,
      panSemTheory.lookup_kvar_def,
      crepSemTheory.set_var_def,
      locals_rel_def,
      FLOOKUP_UPDATE,
      panSemTheory.empty_locals_def,
      crepSemTheory.empty_locals_def
     ] >>
  rw[] >>
  res_tac >> rw[] >> rw[panSemTheory.shape_of_def,shape_of_alt] >>
  gvs[FLOOKUP_UPDATE,flatten_def] >>
  rename1 ‘shape_of (Val vv)’ >> Cases_on ‘vv’ >>
  rw[] >> rw[shape_of_def] >>
  gvs[FLOOKUP_UPDATE,flatten_def] >>
  res_tac >> gvs[] >>
  irule opt_mmap_flookup_update >>
  gvs[no_overlap_def] >>
  strip_tac >>
  res_tac >> rfs[] >> rveq >> rfs[]
QED

Resume pc_compile_correct[ShMemStore]:
  rpt gen_tac >> rpt strip_tac >>
  Cases_on ‘op’ >>
  gvs[AllCaseEqs(),panSemTheory.evaluate_def,compile_def,
      oneline nb_op_def,
      panSemTheory.nb_op_def,panSemTheory.sh_mem_load_def,
      panSemTheory.sh_mem_store_def,panLangTheory.size_of_shape_def,
      asmTheory.is_load_def,panLangTheory.store_op_def,
      localised_prog_def
      ] >>
  PURE_TOP_CASE_TAC >>
  drule_all compile_exp_val_rel >>
  strip_tac >>
  gvs[shape_of_def,panLangTheory.size_of_shape_def,
      quantHeuristicsTheory.LIST_LENGTH_1,
      flatten_def,panSemTheory.shape_of_def,
      crepSemTheory.evaluate_def
     ] >>
  qpat_x_assum ‘_ = eval _ _’ $ assume_tac o GSYM >>
  gvs[] >>
  PURE_TOP_CASE_TAC >>
  drule_all compile_exp_val_rel >>
  strip_tac >>
  gvs[] >>
  gvs[shape_of_def,panLangTheory.size_of_shape_def,
      quantHeuristicsTheory.LIST_LENGTH_1,
      flatten_def,panSemTheory.shape_of_def,
      crepSemTheory.evaluate_def,
      miscTheory.UNCURRY_eq_pair,PULL_EXISTS
     ] >>
  qpat_x_assum ‘_ = eval _ _’ $ assume_tac o GSYM >>
  gvs[shape_of_def,panLangTheory.size_of_shape_def,
      quantHeuristicsTheory.LIST_LENGTH_1,
      flatten_def,panSemTheory.shape_of_def,
      crepSemTheory.evaluate_def,
      miscTheory.UNCURRY_eq_pair,PULL_EXISTS
     ] >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC[update_locals_not_vars_eval_eq'] >>
  simp[FOLDR_MAX_0_MAX_LIST,MAX_LIST_add_not_mem,FLOOKUP_UPDATE,
       sh_mem_op_def,sh_mem_store_def] >>
  gvs[state_rel_def] >>
  gvs[locals_rel_def] >>
  rw[] >>
  res_tac >>
  gvs[] >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at $ Pos last >>
  AP_THM_TAC >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,flookup_res_var_thm] >>
  rw[FLOOKUP_UPDATE]
QED

Theorem compile_exp_not_mem_load_glob:
  ∀ct e s (t :('a, 'b) state) es sh ad.
  compile_exp ct e = (es, sh) ∧
  state_rel s t ∧
  code_rel ct s.code t.code ∧
  locals_rel ct s.locals t.locals
  ==>
  ~MEM (LoadGlob ad) (FLAT (MAP exps es))
Proof
  ho_match_mp_tac compile_exp_ind >>
  rw[compile_exp_def] >>
  gvs[AllCaseEqs(),MEM_FLAT,MEM_MAP,exps_def, SF DNF_ss, UNCURRY_EQ] >>
  rpt strip_tac >>
  gvs[DISJ_EQ_IMP] >>
  rw[]
  >- metis_tac[PAIR]
  >- ((* Field *)
      ‘MEM y cexp ∨ y = Const 0w’ by(metis_tac[mem_comp_field_lem,PAIR,FST,SND]) >>
      gvs[exps_def] >>
      metis_tac[])
  >- (gvs[MEM_EL,load_shape_el_rel,length_load_shape_eq_shape,EL_APPEND] >>
      rw[] >>
      CCONTR_TAC >> gvs[exps_def] >>
      gvs[EL_APPEND,EL_CONS_IF] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[EL_CONS_IF]) >>
      metis_tac[])
  >- metis_tac [PAIR]
  >- metis_tac [PAIR]
  >- (gvs[cexp_heads_eq,cexp_heads_simp_def,AllCaseEqs(),MEM_MAP, SF DNF_ss] >>
      first_x_assum irule >>
      ntac 3 $ first_x_assum $ irule_at $ Pos last >>
      irule_at Any $ GSYM PAIR >>
      irule_at Any HEAD_MEM >>
      metis_tac[])
  >- (gvs[cexp_heads_eq,cexp_heads_simp_def,AllCaseEqs(),MEM_MAP, SF DNF_ss] >>
      first_x_assum irule >>
      ntac 3 $ first_x_assum $ irule_at $ Pos last >>
      irule_at Any $ GSYM PAIR >>
      irule_at Any HEAD_MEM >>
      metis_tac[]) >>
  metis_tac[MEM,PAIR]
QED

Resume pc_compile_correct[Return]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "bool"] >>
  rveq >> fs [] >>
  fs [compile_def, localised_prog_def] >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> rveq >> rfs [] >>
  TOP_CASE_TAC >> fs [] >> rveq >>
  fs [evaluate_def, eval_def, GSYM opt_mmap_eq_some] >>
  fs [state_rel_def,panSemTheory.empty_locals_def,
     empty_locals_def, state_component_equality]
QED

Resume pc_compile_correct[Raise]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def, CaseEq "option", CaseEq "bool"] >>
  rveq >> fs [] >>
  fs [compile_def,localised_prog_def] >>
  pairarg_tac >> fs [] >> rveq >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> rveq >> rfs [] >>
  TOP_CASE_TAC
  >- (
   fs [excp_rel_def] >>
   imp_res_tac fdoms_eq_flookup_some_none >> fs []) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘nested_decs temps es p’ >>
  ‘distinct_lists temps (FLAT (MAP var_cexp es))’ by (
    fs [Abbr ‘temps’] >>
    ho_match_mp_tac genlist_distinct_max >>
    rw [] >>
    drule eval_var_cexp_present_ctxt >>
    disch_then drule_all >>
    rw [] >> fs [] >>
    rfs [] >>
    fs [locals_rel_def, ctxt_max_def] >>
    first_x_assum drule >>
    fs [] >>
    first_x_assum drule >>
    fs [EVERY_MEM] >>
    res_tac >> fs []) >>
  ‘ALL_DISTINCT temps ∧ LENGTH es = LENGTH temps’ by (
    unabbrev_all_tac >>
    fs [LENGTH_GENLIST, ALL_DISTINCT_GENLIST]) >>
  fs [] >>
  assume_tac eval_nested_decs_seq_res_var_eq >>
  pop_assum (qspecl_then [‘es’, ‘temps’, ‘t’, ‘flatten value’,
                          ‘nested_seq (store_globals 0w (MAP Var temps))’] mp_tac) >>
  impl_tac >- (unabbrev_all_tac >> fs []) >>
  fs [] >> pairarg_tac >> fs [] >> rveq >> strip_tac >> rveq >>
  fs [Abbr ‘p’] >>
  drule evaluate_seq_store_globals_res >>
  disch_then (qspecl_then [‘flatten value’, ‘t’, ‘0w’] mp_tac) >>
  fs [length_flatten_eq_size_of_shape] >>
  strip_tac >> fs [] >>
  drule (INST_TYPE [``:'a``|->``:num``,
                    ``:'b``|->``:'a word_lab``] res_var_lookup_original_eq) >>
  disch_then (qspecl_then [‘flatten value’, ‘t.locals’] assume_tac) >>
  gs [length_flatten_eq_size_of_shape, size_of_sh_with_ctxt_eq] >> rveq >>
  conj_tac
  >- fs [state_rel_def,panSemTheory.empty_locals_def,
         empty_locals_def, state_component_equality] >>
  conj_tac >- fs [empty_locals_def, panSemTheory.empty_locals_def] >>
  conj_tac
  >- (
   fs [empty_locals_def, panSemTheory.empty_locals_def, excp_rel_def] >>
   rw [] >> last_x_assum drule_all >> fs []) >>
  strip_tac >>
  fs [empty_locals_def] >>
  fs [globals_lookup_def] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘ALL_DISTINCT (GENLIST (λx. (n2w x): word5) (LENGTH (flatten value)))’ by (
    fs [ALL_DISTINCT_GENLIST] >>
    rw [] >> rfs []) >>
  drule (INST_TYPE [``:'a``|->``:word5``,
                    ``:'b``|->``:'a word_lab``] update_eq_zip_flookup) >>
  disch_then (qspecl_then [‘t.globals’, ‘flatten value’, ‘n’] mp_tac) >>
  fs []
QED


Resume pc_compile_correct[Seq]:
  rpt gen_tac >> rpt strip_tac >>
  fs [compile_def] >>
  fs [panSemTheory.evaluate_def,localised_prog_def] >>
  pairarg_tac >> fs [] >> rveq >>
  cases_on ‘res' = NONE’ >> fs [] >>
  rveq  >> fs []
  >- (
   fs [evaluate_def] >>
   pairarg_tac >> fs [] >> rveq >>
   first_x_assum drule_all >> fs []) >>
  fs [evaluate_def] >>
  pairarg_tac >> fs [] >> rveq >>
  first_x_assum drule_all >> strip_tac >>
  fs [] >> rveq >>
  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  TRY (cases_on ‘FLOOKUP ctxt.eids m’ >> fs [] >> cases_on ‘x’ >> fs []) >>
  cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >>
  cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
QED


Resume pc_compile_correct[If]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_def,localised_prog_def] >>
  cases_on ‘eval s e’ >> fs [] >>
  cases_on ‘x’ >> fs [] >>
  cases_on ‘w’ >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  drule compile_exp_val_rel >>
  disch_then drule_all >>
  strip_tac >> fs [flatten_def] >>
  rveq >> fs [] >>
  fs [evaluate_def] >>
  TOP_CASE_TAC >> fs [] >> rveq >> fs [] >>
  rw[] >> gvs[] >>
  last_x_assum drule_all >>
  strip_tac >> fs [] >>
  rfs [] >>
  cases_on ‘res’ >> fs [] >>
  rveq  >> fs []
QED

Resume pc_compile_correct[While]:
  rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum ‘evaluate (While e c,s) = (res,s1)’ mp_tac >>
  once_rewrite_tac [panSemTheory.evaluate_def] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  TOP_CASE_TAC >> fs [] >>
  strip_tac >>
  fs [compile_def,localised_prog_def] >>
  TOP_CASE_TAC >> fs [] >>
  drule_all compile_exp_val_rel >>
  once_rewrite_tac [shape_of_def] >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  TOP_CASE_TAC >> fs [panLangTheory.size_of_shape_def, flatten_def] >>
  rveq >> fs [MAP] >>
  reverse (cases_on ‘c' ≠ 0w’) >> fs [] >> rveq
  >- fs [Once evaluate_def] >>
  pairarg_tac >> fs [] >>
  cases_on ‘s.clock = 0’ >> fs [] >> rveq >> fs []
  >- (
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   fs [state_rel_def] >> rveq >>
   fs [empty_locals_def, panSemTheory.empty_locals_def]) >>
  ‘t.clock <> 0’ by fs [state_rel_def] >>
  reverse (cases_on ‘res'’) >> fs []
  >- (
   cases_on ‘x’ >> fs [] >> rveq >>
   fs [Once evaluate_def] >>
   pairarg_tac >> fs [] >>
   last_x_assum (qspecl_then [‘dec_clock t’, ‘ctxt’] mp_tac) >>
   impl_tac >>
   TRY (
   fs [dec_clock_def, panSemTheory.dec_clock_def, state_rel_def] >>
   NO_TAC)
   >- (
    strip_tac >> fs [] >> rveq >>
    fs [] >>
    last_x_assum drule_all >>
    strip_tac >> fs [] >> rfs []) >>
   strip_tac >> fs [] >> rveq >>
   cases_on ‘FLOOKUP ctxt.eids m’ >> fs [] >>
   cases_on ‘x’ >> fs []) >>
  fs [Once evaluate_def] >>
  pairarg_tac >> fs [] >>
  last_x_assum (qspecl_then [‘dec_clock t’, ‘ctxt’] mp_tac) >>
  impl_tac
  >- (
   fs [dec_clock_def, panSemTheory.dec_clock_def, state_rel_def]) >>
  strip_tac >> fs [] >> rveq >> fs [] >> rfs [] >>
  last_x_assum drule_all >>
  fs []
QED


Theorem local_rel_gt_vmax_preserved:
  !ct l l' n v.
  locals_rel ct l l' /\ ct.vmax < n ==>
  locals_rel ct l (l' |+ (n,v))
Proof
  rw [] >>
  fs [locals_rel_def] >>
  rw [] >>
  first_x_assum drule_all >>
  strip_tac >> fs [] >>
  fs [opt_mmap_eq_some] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n' ns <= ct.vmax’ by (
    drule ctxt_max_el_leq >> metis_tac []) >>
  fs [FLOOKUP_UPDATE]
QED

Theorem local_rel_le_zip_update_preserved:
  !ct l l' x v sh ns v'.
  locals_rel ct l l' /\
  FLOOKUP l x = SOME v /\
  FLOOKUP ct.vars x = SOME (sh,ns) /\
  shape_of v = shape_of v' ∧ ALL_DISTINCT ns ==>
  locals_rel ct (l |+ (x,v')) (l' |++ ZIP (ns,flatten v'))
Proof
  rw [] >>
  drule_all locals_rel_lookup_ctxt >>
  strip_tac >> fs [] >>
  fs [locals_rel_def] >>
  rw [] >>
  fs [FLOOKUP_UPDATE] >>
  FULL_CASE_TAC >> fs [] >> rveq >>
  first_x_assum drule_all >> gs []
  >- (
   match_mp_tac opt_mmap_some_eq_zip_flookup >>
   fs [opt_mmap_eq_some, MAP_EQ_EVERY2,
       length_flatten_eq_size_of_shape]) >>
  strip_tac >> fs [] >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  irule EQ_TRANS >> irule_at Any opt_mmap_disj_zip_flookup >>
  fs [length_flatten_eq_size_of_shape] >>
  fs [no_overlap_def] >>
  first_x_assum (qspecl_then [‘x’, ‘vname’, ‘shape_of v’,
                              ‘shape_of v''’, ‘ns’, ‘ns''’] mp_tac) >>
  fs []  >> fs [distinct_lists_def, IN_DISJOINT, EVERY_MEM] >>
  metis_tac []
QED

Theorem ctxt_fc_funcs_eq:
    (ctxt_fc cvs em vs shs ns).funcs = cvs
Proof
  rw [ctxt_fc_def]
QED

Theorem ctxt_fc_eids_eq:
    (ctxt_fc cvs em vs shs ns).eids = em
Proof
  rw [ctxt_fc_def]
QED

Theorem ctxt_fc_vmax:
    (ctxt_fc ctxt.funcs em vs shs ns).vmax = MAX_LIST ns
Proof
  rw [ctxt_fc_def]
QED

Definition slc_def:
  slc vshs args = FEMPTY |++ ZIP (MAP FST vshs,args)
End

Definition tlc_def:
  tlc ns args = FEMPTY |++ ZIP (ns,FLAT (MAP flatten args))
End

Theorem slc_tlc_rw:
  FEMPTY |++ ZIP (MAP FST vsh,args) = slc vsh args ∧
  FEMPTY |++ ZIP (ns,FLAT (MAP flatten args)) = tlc ns args
Proof
  rw [slc_def, tlc_def]
QED

Theorem opt_mmap_eval_is_wf_shape_v:
  OPT_MMAP (eval s) es = SOME vs /\
  state_rel s t /\
  locals_rel ctxt s.locals t_locs ==>
  EVERY is_wf_shape_v_nil vs
Proof
  rw [EVERY_MEM]
  \\ drule_then drule OPT_MMAP_MEM_IMP
  \\ rw []
  \\ drule eval_is_wf_shape_v
  \\ fs [state_rel_def, FEVERY_FEMPTY, locals_rel_def]
  \\ disch_then irule
  \\ rw [FEVERY_ALL_FLOOKUP]
  \\ res_tac
  \\ simp [GSYM is_wf_shape_v_nil]
QED

Theorem locals_rel_wf_shape:
  locals_rel ctxt s_locs t_locs /\
  FLOOKUP s_locs nm = SOME v ==>
  is_wf_shape_v_nil v
Proof
  rw [locals_rel_def]
  \\ res_tac
  \\ simp [GSYM is_wf_shape_v_nil]
QED

Theorem call_preserve_state_code_locals_rel:
  ∀rshape.
   ALL_DISTINCT (MAP FST vshs) /\
   LIST_REL (λvshape arg. SND vshape = shape_of arg) vshs args /\
   state_rel s t /\
   code_rel ctxt s.code t.code  /\
   excp_rel ctxt.eids s.eshapes  /\
   locals_rel ctxt s.locals t.locals  /\
   FLOOKUP s.code fname = SOME (vshs,prog,rshape)  /\
   FLOOKUP ctxt.funcs fname = SOME (vshs,rshape)  /\
   ALL_DISTINCT ns  /\
   size_of_shape (Comb (MAP SND vshs)) = LENGTH (FLAT (MAP flatten args))  /\
   FLOOKUP t.code fname = SOME (ns, compile
      (ctxt_fc ctxt.funcs ctxt.eids (MAP FST vshs) (MAP SND vshs) ns) prog)  /\
   LENGTH ns = LENGTH (FLAT (MAP flatten args)) /\
   EVERY is_wf_shape_v_nil args ==>
   state_rel (dec_clock s with locals := slc vshs args) (dec_clock t with locals := tlc ns args) ∧
   code_rel (ctxt_fc ctxt.funcs ctxt.eids (MAP FST vshs) (MAP SND vshs) ns)
            (dec_clock s).code (dec_clock t).code ∧
   excp_rel (ctxt_fc ctxt.funcs ctxt.eids (MAP FST vshs) (MAP SND vshs) ns).eids
             (dec_clock s).eshapes ∧
   locals_rel (ctxt_fc ctxt.funcs ctxt.eids (MAP FST vshs) (MAP SND vshs) ns) (slc vshs args) (tlc ns args)
Proof
  ntac 2 strip_tac >> fs [] >>
  conj_tac >- fs [state_rel_def, dec_clock_def, panSemTheory.dec_clock_def] >>
  conj_tac
  >- (
   fs [code_rel_def, ctxt_fc_def] >>
   rw [] >>
   fs [panSemTheory.dec_clock_def] >>
   last_x_assum drule_all >>
   fs [dec_clock_def]) >>
  conj_tac
  >- fs [ctxt_fc_def, panSemTheory.dec_clock_def] >>
  fs [locals_rel_def] >>
  conj_tac (* replicating because needs to preserve fm in the third conjunct *)
  >- (
   ‘(ctxt_fc ctxt.funcs ctxt.eids (MAP FST vshs) (MAP SND vshs) ns).vars =
    alist_to_fmap (ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)))’ by (
     fs [ctxt_fc_def] >>
     match_mp_tac fm_empty_zip_alist >> fs [length_with_shape_eq_shape]) >> fs [] >>
   metis_tac [all_distinct_alist_no_overlap, LENGTH_MAP]) >>
  conj_tac
  >- (
   ‘(ctxt_fc ctxt.funcs ctxt.eids (MAP FST vshs) (MAP SND vshs) ns).vars =
    alist_to_fmap (ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns)))’ by (
     fs [ctxt_fc_def] >>
     match_mp_tac fm_empty_zip_alist >> fs [length_with_shape_eq_shape]) >> fs [ctxt_fc_vmax] >>
   match_mp_tac all_distinct_alist_ctxt_max >> fs []) >>
  rw [] >> fs [locals_rel_def, ctxt_fc_def, slc_def, tlc_def] >>
  ‘LENGTH (MAP FST vshs) = LENGTH args’ by (drule LIST_REL_LENGTH >> fs []) >>
  drule fm_empty_zip_flookup >> fs [] >>
  disch_then drule >>
  strip_tac >> fs [] >>
  qexists_tac ‘EL n (with_shape (MAP SND vshs) ns)’ >>
  conj_tac
  >- (  (* could be neater *)
   ‘FLOOKUP (FEMPTY |++ ZIP (MAP FST vshs,ZIP (MAP SND vshs,with_shape (MAP SND vshs) ns))) vname =
    SOME (EL n (MAP SND vshs),EL n (with_shape (MAP SND vshs) ns))’ by (
     match_mp_tac fm_empty_zip_flookup_el >>
     fs [] >> ‘LENGTH ns = size_of_shape (Comb (MAP SND vshs))’ by fs [] >>
     drule length_with_shape_eq_shape >> fs [] >> strip_tac >>
     ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
     disch_then (qspec_then ‘n’ mp_tac) >> fs []) >>
   fs [] >>
   ‘n < LENGTH (MAP FST vshs)’ by fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >>
   drule EL_ZIP >>
   disch_then (qspec_then ‘n’ assume_tac) >>
   rfs [] >> rveq >>
   fs [LIST_REL_EL_EQN] >>
   last_x_assum drule >> fs [EL_MAP]) >>
  fs [opt_mmap_eq_some] >>
  reverse conj_tac
  >- (
    simp [is_wf_shape_v_nil] >>
    fs [EVERY_MAP] >>
    fs [EVERY_MEM] >>
    first_x_assum irule >>
    gvs [EL_ZIP, EL_MEM]
  )
  >>
  fs [EVERY_MAP, is_wf_shape_v_nil, SF ETA_ss] >>
  fs [MAP_EQ_EVERY2] >> conj_tac
  >- (
   match_mp_tac list_rel_flatten_with_shape_length >>
   qexists_tac ‘args’ >> fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >> fs [] >>
   strip_tac >> fs [EVERY2_MAP]) >>
  rewrite_tac [LIST_REL_EL_EQN] >> conj_tac
  >- (
   match_mp_tac list_rel_flatten_with_shape_length >>
   qexists_tac ‘args’ >> fs [] >>
   ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
   disch_then (qspec_then ‘n’ mp_tac) >> fs [] >>
   strip_tac >> fs [EVERY2_MAP]) >>
  rw [] >> match_mp_tac list_rel_flatten_with_shape_flookup >> fs [] >>
  ‘LENGTH (MAP FST vshs) = LENGTH args’ by fs [] >> drule EL_ZIP >>
  disch_then (qspec_then ‘n’ mp_tac) >> fs [] >> strip_tac >>
  fs [EVERY2_MAP] >>
  match_mp_tac list_rel_flatten_with_shape_length >>
  qexists_tac ‘args’ >> fs [] >>
  fs [EVERY2_MAP]
QED

Theorem no_overlap_wrap_rt_some_all_distinct:
  no_overlap fm ∧ wrap_rt (FLOOKUP fm r) = SOME (vsh, ns) ⇒ ALL_DISTINCT ns
Proof
  rpt strip_tac >> gvs[no_overlap_def, wrap_rt_def, CaseEq "option", CaseEq "prod", CaseEq "list",
                       CaseEq "shape", ExclSF "list"]
  >> metis_tac[]
QED

Theorem is_wf_shape_nil_length_flatten:
  is_wf_shape_nil (shape_of v) ∧
  (size_of_shape (shape_of v) = 0 ⇒ l = []) ∧
  (0 < size_of_shape (shape_of v) ⇒ l = flatten v) ⇒
  LENGTH l = size_of_shape (shape_of v)
Proof
  Cases_on `v` >> rw[]
  >- (Cases_on `w` >> fs[panSemTheory.shape_of_def, panLangTheory.size_of_shape_def, flatten_def])
  >- (
    qmatch_goalsub_abbrev_tac `LENGTH _ = ssh`
    >> Cases_on `ssh = 0` >> fs[length_flatten_eq_size_of_shape, Abbr `ssh`]
  )
  >> fs[panSemTheory.shape_of_def, panLangTheory.is_wf_shape_def]
QED

val clock_zero_tail_rt_tac =
    fs [evaluate_def] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule list_rel_length_shape_of_flatten >>
    fs [] >>
    strip_tac >>
    fs [ALL_DISTINCT_GENLIST] >>
    drule code_rel_empty_locals >>
    fs [state_rel_def, panSemTheory.empty_locals_def,
        empty_locals_def, ALL_DISTINCT_GENLIST]

val clock_zero_nested_seq_rt_tac =
    fs [nested_seq_def] >>
    fs [evaluate_def] >>
    pairarg_tac >> fs [] >>
    cases_on ‘eval t x0’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >> rveq >>
    fs [panSemTheory.lookup_code_def] >>
    cases_on ‘FLOOKUP s.code fname’ >> fs [] >>
    cases_on ‘x’ >> fs [] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule list_rel_length_shape_of_flatten >>
    fs [] >>
    strip_tac >>
    fs [ALL_DISTINCT_GENLIST] >>
    strip_tac >> fs [] >>
    fs [state_rel_def] >> rveq >> rfs [] >>
    rveq >> fs [] >>
    drule code_rel_empty_locals >>
    fs [panSemTheory.empty_locals_def,
        empty_locals_def, ALL_DISTINCT_GENLIST]

val rels_empty_tac =
    fs [Abbr ‘nctxt’, state_rel_def, ctxt_fc_funcs_eq, ctxt_fc_eids_eq,
        excp_rel_def, empty_locals_def, panSemTheory.empty_locals_def, code_rel_def,
        globals_lookup_def] >> rw[] >> res_tac



val call_tail_ret_impl_tac =
     TRY (imp_res_tac no_overlap_wrap_rt_some_all_distinct >>
     pop_assum mp_tac >> impl_tac >- fs[locals_rel_def] >> disch_tac) >>
     fs [evaluate_def] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule list_rel_length_shape_of_flatten >>
     fs [] >>
     strip_tac >>
     fs [ALL_DISTINCT_GENLIST] >>

     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      gvs [Abbr ‘ns’, ALL_DISTINCT_GENLIST]
      ) >>
     strip_tac >> fs [] >>
     fs [state_rel_def, Abbr ‘nctxt’, code_rel_def, ctxt_fc_funcs_eq,
         panSemTheory.empty_locals_def, empty_locals_def, ctxt_fc_eids_eq, excp_rel_def] >>
     rw[] >> res_tac

val ret_call_shape_retv_one_tac =
     fs [evaluate_def] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule list_rel_length_shape_of_flatten >>
     fs [] >>
     strip_tac >>
     fs [ALL_DISTINCT_GENLIST] >>
     `ALL_DISTINCT (v12::v13)` by (
       drule $ iffLR locals_rel_def
       >> disch_tac >> fs[]
       >> pop_assum imp_res_tac
       >> qpat_x_assum `no_overlap _` $ assume_tac o SRULE [no_overlap_def] >> fs[]
       >> pop_assum kall_tac
       >> pop_assum imp_res_tac >> gvs[]
     )
     >> fs[] >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs [Abbr ‘ns’, ALL_DISTINCT_GENLIST]) >>
     strip_tac >> fs []
     >> imp_res_tac is_wf_shape_of_v
     >> imp_res_tac length_flatten_eq_size_of_shape
     >> qpat_assum `locals_rel _ _ _` $ imp_res_tac o SRULE[locals_rel_def] 
     >> imp_res_tac length_flatten_eq_size_of_shape
     >> drule opt_mmap_length_eq >> disch_tac >> gvs[]
     >> gvs[panSemTheory.set_var_def, state_rel_def, FLOOKUP_UPDATE, Abbr `nctxt`, ctxt_fc_def, locals_rel_def]
     >> conj_tac
     >- (fs[code_rel_def] >> metis_tac[])
     >> strip_tac >> TOP_CASE_TAC >> gvs[ExclSF "list"]
     >- (
       fs[opt_mmap_some_eq_zip_flookup]
     )
     >> rpt strip_tac >> res_tac >> fs[]
     >> DEP_REWRITE_TAC [opt_mmap_disj_zip_flookup] >> gs[]
     >> imp_res_tac no_overlap_flookup_distinct


val ret_call_shape_retv_comb_zero_tac =
     fs [ret_var_def, ret_hdl_def] >>
     fs [evaluate_def] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule list_rel_length_shape_of_flatten >>
     fs [] >>
     strip_tac >>
     res_tac  >>
     fs [ALL_DISTINCT_GENLIST] >>
     `ALL_DISTINCT r''` by (fs[locals_rel_def, no_overlap_def] >> metis_tac[]) >> simp[] >>
     cases_on ‘t.clock = 0’ >- fs [state_rel_def] >>
     fs [] >> rveq >>
     qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs [Abbr ‘ns’, ALL_DISTINCT_GENLIST]
     ) >>
     strip_tac >> fs [] >>
     imp_res_tac length_flatten_eq_size_of_shape
     >> qpat_assum `locals_rel _ _ _` $ imp_res_tac o SRULE[locals_rel_def] 
     >> imp_res_tac length_flatten_eq_size_of_shape
     >> drule opt_mmap_length_eq >> disch_tac >> gvs[]
     >> fs[state_rel_def, panSemTheory.set_var_def, Abbr `nctxt`, ctxt_fc_def, code_rel_def, excp_rel_def]
     >> conj_tac >- metis_tac[]
     >> gvs[FLOOKUP_UPDATE, locals_rel_def]
     >> strip_tac >> TOP_CASE_TAC >> fs[]
     >> rpt strip_tac 
     >> res_tac >> gvs[FUPDATE_LIST]
     

val ret_call_shape_retv_comb_one_tac =
     fs [evaluate_def] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule list_rel_length_shape_of_flatten >>
     fs [] >>
     strip_tac >>
     fs [ALL_DISTINCT_GENLIST] >>       TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
     first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs [Abbr ‘ns’, ALL_DISTINCT_GENLIST]) >>
     strip_tac >> fs [] >>
     ‘size_of_shape (shape_of x) = 1’ by (
       fs [locals_rel_def] >>
       last_x_assum drule >> fs [shape_of_def] >>
       strip_tac >> qpat_x_assum ‘Comb l = shape_of x’ (assume_tac o GSYM) >>
       fs [panLangTheory.size_of_shape_def, shape_of_def]) >> fs [] >>
     drule locals_rel_lookup_ctxt >>
     disch_then drule >> strip_tac >> fs [] >>
     rveq >> fs [OPT_MMAP_def] >> rveq >>
     cases_on ‘ns’ >> fs []
     >- (
      fs [OPT_MMAP_def] >>
      pop_assum (assume_tac o GSYM) >>
      gs [GSYM length_flatten_eq_size_of_shape]) >>
     fs [OPT_MMAP_def] >> rveq >>
     fs [state_rel_def, panSemTheory.set_var_def,set_var_def, set_kvar_def,
         Abbr ‘nctxt’, code_rel_def, ctxt_fc_funcs_eq,ctxt_fc_eids_eq] >>
     ‘size_of_shape (shape_of v) = 1’ by fs [] >>
      rveq >> gs [length_flatten_eq_size_of_shape] >>
      rfs [panLangTheory.size_of_shape_def] >>
      fs [OPT_MMAP_def] >> rveq >>
      fs [locals_rel_def, panSemTheory.set_var_def,set_var_def,set_kvar_def] >>
      rw [] >> rveq >>
      fs [FLOOKUP_UPDATE] >>
      rw [] >> res_tac >>
      FULL_CASE_TAC >> fs [] >> rveq
      >- (
       fs [OPT_MMAP_def, FLOOKUP_UPDATE] >>
       gs [length_flatten_eq_size_of_shape,
           panLangTheory.size_of_shape_def, shape_of_def,
           OPT_MMAP_def]) >>
      res_tac >> fs [] >>
      match_mp_tac opt_mmap_flookup_update >>
      fs [OPT_MMAP_def] >> rveq >>
      drule no_overlap_flookup_distinct >>
      disch_then drule_all >>
      cases_on ‘ns’ >>
      fs [distinct_lists_def]


val ret_call_shape_retv_comb_gt_one_tac =
    fs [ret_var_def, ret_hdl_def] >>
    fs [evaluate_def, assign_ret_def] >>
    ‘OPT_MMAP (eval t)
     (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
    fs [] >>
    fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
    drule code_rel_imp >>
    disch_then drule >>
    strip_tac >> fs [] >>
    fs [lookup_code_def] >>
    drule list_rel_length_shape_of_flatten >>
    fs [] >>
    strip_tac >>
    fs [ALL_DISTINCT_GENLIST] >>
    `ALL_DISTINCT r''` by (fs[locals_rel_def, no_overlap_def] >> metis_tac[]) >> fs[] >>
    cases_on ‘t.clock = 0’ >- fs [state_rel_def] >>
    fs [] >> rveq >>
    qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
    first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
     qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
     match_mp_tac call_preserve_state_code_locals_rel >>
     fs [Abbr ‘ns’, ALL_DISTINCT_GENLIST]) >>
    strip_tac >> fs [] >>
    imp_res_tac length_flatten_eq_size_of_shape
    >> qpat_assum `locals_rel _ _ _` $ imp_res_tac o SRULE[locals_rel_def] 
    >> imp_res_tac length_flatten_eq_size_of_shape
    >> drule opt_mmap_length_eq >> disch_tac >> gvs[]
    >> fs[state_rel_def, panSemTheory.set_var_def, Abbr `nctxt`, ctxt_fc_def, code_rel_def, excp_rel_def]
    >> conj_tac >- metis_tac[]
    >> gvs[FLOOKUP_UPDATE, locals_rel_def]
    >> strip_tac >> TOP_CASE_TAC >> fs[]
    >- (
      DEP_REWRITE_TAC [opt_mmap_some_eq_zip_flookup] >> gvs[]
    )
    >> rpt strip_tac 
    >> res_tac >> gvs[]
    >> DEP_REWRITE_TAC[opt_mmap_disj_zip_flookup] >> fs[]
    >> imp_res_tac no_overlap_flookup_distinct

val eval_call_impl_only_tac =
     fs [evaluate_def] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule list_rel_length_shape_of_flatten >>
     fs [] >>
     strip_tac >>
     fs [ALL_DISTINCT_GENLIST] >>
     TOP_CASE_TAC >- fs [state_rel_def] >>
     qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
     last_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
     impl_tac
     >- (
      fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
      qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
      match_mp_tac call_preserve_state_code_locals_rel >>
      fs [Abbr ‘ns’, ALL_DISTINCT_GENLIST])


val ret_call_excp_reult_handle_none_tac =
    (* exception value with ret call *)
     TOP_CASE_TAC >> fs [] >>
     fs [CaseEq "option", CaseEq "prod",
         CaseEq "shape", CaseEq "list"] >>
     rveq >> fs [ret_var_def, ret_hdl_def] >>
     qpat_assum `locals_rel _ _ _` $ imp_res_tac o SRULE[no_overlap_def] o CONJUNCT1 o SRULE[locals_rel_def] >> fs[]
    >- (
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eids = ctxt.eids’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eids_eq] >>
     rename1 ‘FLOOKUP ctxt.eids m'’ >>
     cases_on ‘FLOOKUP ctxt.eids m'’ >> fs [] >>
     rename1 ‘FLOOKUP ctxt.eids m' = SOME ww’ >>
     cases_on ‘ww’ >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- (fs [shape_of_def, panLangTheory.size_of_shape_def] >> rels_empty_tac) >>
     rels_empty_tac)
    >- (
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eids = ctxt.eids’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eids_eq] >>
     rename1 ‘FLOOKUP ctxt.eids m'’ >>
     cases_on ‘FLOOKUP ctxt.eids m'’ >> fs [] >>
     rename1 ‘FLOOKUP ctxt.eids m' = SOME ww’ >>
     cases_on ‘ww’ >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- (fs [shape_of_def, panLangTheory.size_of_shape_def] >> rels_empty_tac) >>
     rels_empty_tac)
    >- (
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eids = ctxt.eids’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eids_eq] >>
     rename1 ‘FLOOKUP ctxt.eids m'’ >>
     cases_on ‘FLOOKUP ctxt.eids m'’ >> fs [] >>
     rename1 ‘FLOOKUP ctxt.eids m' = SOME ww’ >>
     cases_on ‘ww’ >> fs [] >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- (fs [shape_of_def, panLangTheory.size_of_shape_def] >> rels_empty_tac) >>
     rels_empty_tac
    ) >>
    eval_call_impl_only_tac >>
    strip_tac >> fs [] >>
    ‘nctxt.eids = ctxt.eids’ by
      fs [Abbr ‘nctxt’, ctxt_fc_eids_eq] >>
    rename1 ‘FLOOKUP ctxt.eids m'’ >>
    cases_on ‘FLOOKUP ctxt.eids m'’ >> fs [] >>
    rename1 ‘FLOOKUP ctxt.eids m' = SOME ww’ >>
    cases_on ‘ww’ >> fs [] >>
    cases_on ‘res1’ >> fs [] >> rveq >> fs [] >>
    TRY (cases_on ‘x’ >> fs [] >> rveq >> fs []) >>
    cases_on ‘FLOOKUP ctxt.eids m'’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 0’ >> fs []
    >- rels_empty_tac >>
    cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
    >- (
     fs [shape_of_def, panLangTheory.size_of_shape_def] >>
     rels_empty_tac) >>
    rels_empty_tac

val ret_call_excp_reult_handle_uneq_exp_tac =
    rveq >> fs [] >>
    cases_on ‘FLOOKUP ctxt.eids m0’ >> fs []
    >- ret_call_excp_reult_handle_none_tac >>
    rename [‘geid <> eid’] >>
    TOP_CASE_TAC >> fs [] >>
    fs [CaseEq "option", CaseEq "prod",
        CaseEq "shape", CaseEq "list"] >>
    rveq >> fs [ret_var_def, ret_hdl_def] >>
    qpat_assum `locals_rel _ _ _` $ imp_res_tac o SRULE[no_overlap_def] o CONJUNCT1 o SRULE[locals_rel_def] >> fs[] >>
     eval_call_impl_only_tac >>
     strip_tac >> fs [] >>
     ‘nctxt.eids = ctxt.eids’ by
       fs [Abbr ‘nctxt’, ctxt_fc_eids_eq] >>
     cases_on ‘FLOOKUP ctxt.eids geid’ >> fs [] >>
     rename [‘res1 = SOME (Exception er)’] >>
     ‘er <> x’ by (
       CCONTR_TAC >>
       fs [excp_rel_def]) >>
     cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >> rveq
     >- rels_empty_tac >>
     cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []
     >- rels_empty_tac >>
     rels_empty_tac


val ret_call_excp_handler_tac =
    TRY (
    first_x_assum drule >>
    strip_tac >> rfs []) >>
    TOP_CASE_TAC >> fs [] >>
    fs [CaseEq "option", CaseEq "prod",
        CaseEq "shape", CaseEq "list"] >>
    rveq >> fs [ret_var_def, ret_hdl_def] >>
    qpat_assum `locals_rel _ _ _` $ imp_res_tac o SRULE[no_overlap_def] o CONJUNCT1 o SRULE[locals_rel_def] >> fs[] >>
    (
    eval_call_impl_only_tac >>
    strip_tac >> fs [] >>
    ‘nctxt.eids = ctxt.eids’ by
      fs [Abbr ‘nctxt’, ctxt_fc_eids_eq] >>
    fs [] >>
    cases_on ‘FLOOKUP ctxt.eids eid’ >> fs [] >>
    rename [‘FLOOKUP ctxt.eids eid = SOME ed’] >>
   fs [] >> rveq >> fs [] >>
    fs [is_valid_value_def] >>
    rename1 ‘FLOOKUP s.locals m''’ >>
    cases_on ‘FLOOKUP s.locals m''’ >> fs [] >>
    drule locals_rel_lookup_ctxt >>
    disch_then drule_all >>
    strip_tac >> fs [] >> rveq >>
    rename [‘OPT_MMAP (FLOOKUP t.locals) _ = SOME (flatten ex)’] >>
    fs [exp_hdl_def] >>
    pairarg_tac >> fs [] >>
    ‘ALL_DISTINCT ns’ by
      (fs [locals_rel_def] >> imp_res_tac all_distinct_flookup_all_distinct) >>
    drule evaluate_seq_assign_load_globals >>
    disch_then (qspecl_then [‘t1 with locals :=
                              t.locals’, ‘0w’] mp_tac) >>
    impl_tac
    >- (
     (conj_tac
     >- (
      fs [word_0_n2w] >>
      imp_res_tac locals_rel_lookup_ctxt >> rveq >>
      gs [length_flatten_eq_size_of_shape] >> rfs [] >>
      cases_on ‘size_of_shape (shape_of ex)’ >> fs [])) >>
     (conj_tac
     >- (
      rw [] >> CCONTR_TAC >>
      drule locals_rel_lookup_ctxt >>
      disch_then drule_all >>
      strip_tac >> fs [] >> rveq >>
      fs [opt_mmap_eq_some] >>
      fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN, MEM_EL] >>
      rveq >> fs [] >> rfs [] >>
      res_tac >> rfs []) >>
     rw [] >> rfs [] >>
     CCONTR_TAC >> fs [] >>
     reverse (cases_on ‘1 ≤ size_of_shape (shape_of ex)’) >>
     fs []
     >- gs [MEM_GENLIST, length_flatten_eq_size_of_shape] >>
     rfs [globals_lookup_def] >>
     gs [GSYM length_flatten_eq_size_of_shape] >>
     qpat_x_assum ‘OPT_MMAP (FLOOKUP t1.globals) _ = _’  assume_tac >>
     drule opt_mmap_mem_func >>
     disch_then drule >> strip_tac >> fs [])) >>
    strip_tac >> fs [] >>
    rfs [] >> rveq >>
    qmatch_goalsub_abbrev_tac ‘evaluate (compile ctxt p,tt)’ >>
    first_x_assum (qspecl_then [‘tt’, ‘ctxt’] mp_tac) >>
    impl_tac
    >- (
     fs [Abbr ‘tt’, panSemTheory.set_var_def, set_kvar_def] >>
     fs [state_rel_def, panSemTheory.set_var_def,set_var_def, set_kvar_def,
         Abbr ‘nctxt’, code_rel_def, ctxt_fc_funcs_eq,ctxt_fc_eids_eq] >>
     conj_tac >- (rw[] >> res_tac) >>
     fs [locals_rel_def] >>
     rw [] >> rveq >>
     fs [FLOOKUP_UPDATE] >>
     reverse FULL_CASE_TAC >> fs [] >> rveq
     >- (
      res_tac >> fs [] >>
      qpat_x_assum  ‘OPT_MMAP _ ns' = _’ (assume_tac o GSYM) >>
      fs [] >>
      match_mp_tac opt_mmap_disj_zip_flookup >>
      conj_tac
      >- (
       pop_assum (assume_tac o GSYM) >>
       fs [no_overlap_def] >>
       res_tac >> fs [] >> rveq >>
       fs []  >> fs [distinct_lists_def, IN_DISJOINT, EVERY_MEM] >>
       metis_tac []) >>
      res_tac >> fs []) >>
     reverse (cases_on ‘1 ≤ size_of_shape (shape_of ex)’) >>
     fs [] >> rveq >>
     gs [length_flatten_eq_size_of_shape]
     >- (
      qpat_x_assum ‘shape_of v = shape_of ex’ (assume_tac o GSYM) >>
      fs [] >>
      ‘size_of_shape (shape_of v) = 0’ by fs [] >>
      gs [OPT_MMAP_def, GSYM length_flatten_eq_size_of_shape]) >>
     fs [globals_lookup_def, opt_mmap_eq_some] >>
     simp [Once (GSYM o_DEF),MAP_o] >>
     rewrite_tac [ETA_AX] >>
     rfs [ETA_AX] >>
     fs [MAP_o, MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
     rw [] >>
     fs [MAP_MAP_o] >>
     ‘MAP (THE ∘ SOME) (flatten v) = flatten v’ by fs [map_the_some_cancel] >>
     fs [] >> pop_assum kall_tac >>
     match_mp_tac update_eq_zip_flookup >>
     fs []) >>
    strip_tac >> fs [])

Theorem flatten_nil_no_size[local]:
  is_wf_shape_nil (shape_of x) ⇒
  (flatten x = [] ⇔ size_of_shape(shape_of x) = 0)
Proof
  rw[EQ_IMP_THM,GSYM length_flatten_eq_size_of_shape]
QED

Theorem locals_rel_wf_shape[local]:
  locals_rel ctxt s_locs t_locs /\ ss = TAKE 0 (s.structs) ==>
  FEVERY (\(nm,v). is_wf_shape_v ss v) s_locs
Proof
  simp [locals_rel_def, is_wf_shape_v_nil, FEVERY_ALL_FLOOKUP] >>
  metis_tac []
QED

Theorem evaluate_shape_invariant_ret_inst[local]:
  evaluate (p, s) = (SOME v, s') ∧
  state_rel s t ∧
  locals_rel ctxt s.locals t_locs ⇒
  case v of Return retv => is_wf_shape_v_nil retv
    | Exception eid exn => is_wf_shape_v_nil exn
    | _ => T
Proof
  rw [] >>
  drule evaluate_is_wf_shape_invariant >>
  imp_res_tac evaluate_invariants >>
  drule locals_rel_wf_shape >>
  fs [state_rel_def, FEVERY_FEMPTY]
QED

Theorem evaluate_shape_invariant_ret_inst2[local]:
  OPT_MMAP (eval s) argexps = SOME args ∧
  lookup_code s.code fname args = SOME (p2, newlocals, rsh)  ∧
  evaluate (p, dec_clock s with locals := newlocals) = (SOME v, s') ∧
  state_rel s t ∧
  locals_rel ctxt s.locals t_locs ⇒
  case v of Return retv => is_wf_shape_v_nil retv
    | Exception eid exn => is_wf_shape_v_nil exn
    | _ => T
Proof
  rw [] >>
  drule_then drule lookup_code_wf_shape_invariant_step >>
  drule locals_rel_wf_shape >>
  fs [state_rel_def, FEVERY_FEMPTY] >>
  drule evaluate_is_wf_shape_invariant >>
  simp [panSemTheory.dec_clock_def, FEVERY_FEMPTY]
QED



Theorem evaluate_replicate_const:
  ∀n s. OPT_MMAP (eval s) (REPLICATE n (Const 0w)) = SOME (REPLICATE n (Word 0w))
Proof
  Induct >> fs[eval_def]
QED

Theorem eval_distinct_lists_not_affect:
  ∀vs s e w nvals.
    eval s e = SOME w ∧
    LENGTH vs = LENGTH nvals ∧
    distinct_lists vs (var_cexp e) ⇒
      eval (s with locals := s.locals |++ ZIP (vs, nvals)) e = SOME w
Proof
  Induct >> rw[]
  >- (
    fs[FUPDATE_LIST]
    >> `s with locals := s.locals = s` by fs[state_component_equality] >> fs[]
  )
  >> Cases_on `nvals` >> fs[FUPDATE_LIST_THM, distinct_lists_def]
  >> last_assum drule
  >> disch_then $ qspec_then `t` assume_tac >> gs[]
  >> imp_res_tac update_locals_not_vars_eval_eq
  >> pop_assum $ qspec_then `h'` assume_tac >> fs[]
  >> last_x_assum drule >> fs[]
QED

Theorem opt_mmap_eval_distinct_lists_not_affect:
  ∀es s ws vs nvals.
    OPT_MMAP (eval s) es = SOME ws ∧
    LENGTH vs = LENGTH nvals ∧
    distinct_lists vs (FLAT (MAP var_cexp es)) ⇒
      OPT_MMAP (eval (s with locals := s.locals |++ ZIP (vs, nvals))) es = SOME ws
Proof
  Induct >> rw[]
  >> conj_tac
  >- (
    imp_res_tac distinct_lists_append_right_elim
    >> metis_tac[eval_distinct_lists_not_affect]
  )
  >> imp_res_tac distinct_lists_append_right_elim
  >> metis_tac[]
QED

Theorem genlist_vmax_distinct_lists_compiled_exps:
  ∀ctxt n argexps.
    ctxt_max ctxt.vmax ctxt.vars ⇒
    distinct_lists (GENLIST (\x. SUC x + ctxt.vmax) n) (FLAT (MAP var_cexp (FLAT (MAP FST (MAP (compile_exp ctxt) argexps)))))
Proof
  fs[distinct_lists_def, EVERY_MEM]
  >> rpt strip_tac
  >> imp_res_tac mem_genlist_add_suc_val
  >> gvs[MEM_FLAT, MEM_MAP]
  >> imp_res_tac MEM_compile_exp_vmax >> fs[]
QED


Resume pc_compile_correct[Call]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def] >>
  fs [compile_def] >>
  fs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod"] >>
  rveq >> fs [localised_prog_def] >>
  drule_all opt_mmap_eval_is_wf_shape_v >> strip_tac >>
  cases_on ‘s.clock = 0’ >> fs [] >> rveq
  (* s = 0 case *)
  >- (
    rpt(PURE_TOP_CASE_TAC >> gvs[nested_decs_def])
    (* When the call is standalone, thus we don't know
       how many variables to "invent" at the call site,
       and FLOOKUP ctxt.funcs fname ≠ NONE *)
    >>~- ([`evaluate (nested_decs _ _ _, _)`],
      imp_res_tac opt_mmap_length_eq
      >> qspecl_then [`size_of_shape r`, `t`] mp_tac evaluate_replicate_const
      >> REWRITE_TAC[opt_mmap_eq_some]
      >> disch_tac
      >> qmatch_goalsub_abbrev_tac `nested_decs ntmps _ p`
      >> drule eval_nested_decs_seq_res_var_eq
      >> disch_then $ qspecl_then [`ntmps`, `p`] mp_tac >> fs[] >> impl_tac
      >- fs[Abbr `ntmps`, distinct_lists_def, var_cexp_def, ALL_DISTINCT_GENLIST, FLAT_REPLICATE_NIL]
      >> pairarg_tac >> gvs[]
      >> disch_tac >> gs[Abbr `p`, evaluate_def]
      >> ‘OPT_MMAP (eval t)
        (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
         fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq])
      >> drule opt_mmap_eval_distinct_lists_not_affect
      >> disch_then $ qspecl_then [`ntmps`,`REPLICATE (size_of_shape r) (Word 0w)`] mp_tac >> fs[] >> impl_tac
      >- (
        fs[Abbr `ntmps`, distinct_lists_def, EVERY_MEM]
        >> rpt strip_tac
        >> imp_res_tac mem_genlist_add_suc_val
        >> gvs[MEM_FLAT, MEM_MAP]
        >> drule_all opt_mmap_mem_func
        >> disch_tac >> gvs[]
        >> drule_at Any MEM_compile_exp_vmax
        >> disch_then $ drule_at Any >> impl_tac
        >- fs[locals_rel_def]
        >> disch_tac >> fs[]
      )
      >> disch_tac >> fs[]
      >> imp_res_tac code_rel_imp
      >> gvs[lookup_code_def, panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"]
      >- (pop_assum drule >> disch_tac >> fs[])
      >- (
        pop_assum imp_res_tac >>
        imp_res_tac list_rel_length_shape_of_flatten >> gvs[ALL_DISTINCT_GENLIST]
      )
      >> gvs[Abbr `ntmps`, ALL_DISTINCT_GENLIST, state_rel_def, panSemTheory.empty_locals_def, code_rel_def, excp_rel_def, empty_locals_def]
      >> metis_tac[])
    >> clock_zero_tail_rt_tac >> gvs[locals_rel_def]
    >> imp_res_tac no_overlap_wrap_rt_some_all_distinct >> gvs[]
  ) >>
  (* s <> 0 case *)
  TOP_CASE_TAC >> fs []
  (* Tail call *)
  >- suspend "Call_TailCall" >>
  (* Return case *)
  cases_on ‘evaluate (prog,dec_clock s with locals := newlocals)’ >>
  rename1 ‘evaluate _ = (q, r)’>>
  cases_on ‘q’ >> fs [] >>
  rename1 ‘evaluate _ = (SOME x', r)’>>
  cases_on ‘x'’ >> fs [] >> rveq >>
  TRY (cases_on ‘FLOOKUP s.locals m’ >> fs [] >> NO_TAC)
  (* timed-out in Ret call *)
  >- suspend "Call_Ret_TimeOut"
  (* return in Ret call *)
  >- suspend "Call_Ret_Return"
  (* Exception result *)
  >- suspend "Call_Ret_Exception"
  >- suspend "Call_Ret_FinalFFI"
QED

Resume pc_compile_correct[Call_TailCall]:
   fs [evaluate_def] >>
   ‘OPT_MMAP (eval t)
    (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
     fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
   fs [] >>
   fs [panSemTheory.lookup_code_def] >>
   cases_on ‘FLOOKUP s.code fname’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   cases_on ‘r’ >> fs [] >> rveq >>
   drule code_rel_imp >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [lookup_code_def] >>
   drule list_rel_length_shape_of_flatten >>
   fs [] >>
   strip_tac >>
   fs [ALL_DISTINCT_GENLIST] >>
   TOP_CASE_TAC >- fs [state_rel_def] >>
   cases_on ‘evaluate
             (prog,
              dec_clock s with locals := FEMPTY |++ ZIP (MAP FST q,args))’ >>
   fs [] >>
   cases_on ‘q'’ >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >>
   qmatch_goalsub_abbrev_tac ‘compile nctxt _,nt’ >>
   first_x_assum (qspecl_then [‘nt’, ‘nctxt’] mp_tac) >>
   impl_tac
   >>~- ([`state_rel _ _ ∧ code_rel _ _ _ ∧ excp_rel _ _ ∧ locals_rel _ _ _`],
     fs [Abbr ‘nctxt’, Abbr ‘nt’, slc_tlc_rw] >>
     qmatch_goalsub_abbrev_tac ‘(dec_clock t with locals := tlc ns _)’ >>
     match_mp_tac call_preserve_state_code_locals_rel >>
     fs [Abbr ‘ns’, ALL_DISTINCT_GENLIST]
   )
   >- (strip_tac >> fs [] >> rels_empty_tac)
   >- (
    strip_tac >> fs []
    >> Cases_on `shape_of v ≠ r'` >> gvs[]
    >> rels_empty_tac
   )
   >- (
    strip_tac >> fs [] >>
    cases_on ‘FLOOKUP nctxt.eids m’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    TOP_CASE_TAC >> fs [] >>
    rels_empty_tac
   ) >>
   strip_tac >> rels_empty_tac
QED

Resume pc_compile_correct[Call_Ret_TimeOut]:
  TRY (rpt TOP_CASE_TAC) >> fs []
  >>~- ([`FLOOKUP _.funcs _ = NONE`],
   TRY (imp_res_tac no_overlap_wrap_rt_some_all_distinct >>
   pop_assum mp_tac >> impl_tac >- fs[locals_rel_def] >> disch_tac) >>
   fs [evaluate_def] >>
   ‘OPT_MMAP (eval t)
    (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
     fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
   fs [] >>
   fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
   drule code_rel_imp >>
   disch_then drule >>
   strip_tac >> fs [] >>
   fs [lookup_code_def] >>
   drule list_rel_length_shape_of_flatten >>
   fs [] >>
   strip_tac >>
   fs [ALL_DISTINCT_GENLIST])
  (* Again, this is the "standalone call" case where we don't know
     the shape that might be returned by the function purely looking at the call site, where we can still find the function
     declaration information in the context *)
  >>~- ([`evaluate (nested_decs _ _ _, _)`],
    imp_res_tac opt_mmap_length_eq
    >> qspecl_then [`size_of_shape r'`, `t`] mp_tac evaluate_replicate_const
    >> REWRITE_TAC[opt_mmap_eq_some]
    >> disch_tac
    >> qmatch_goalsub_abbrev_tac `nested_decs ntmps _ p`
    >> drule eval_nested_decs_seq_res_var_eq
    >> disch_then $ qspecl_then [`ntmps`, `p`] mp_tac >> fs[] >> impl_tac
    >- fs[Abbr `ntmps`, distinct_lists_def, var_cexp_def, ALL_DISTINCT_GENLIST, FLAT_REPLICATE_NIL]
    >> pairarg_tac >> gvs[]
    >> disch_tac >> fs[Abbr `p`, evaluate_def]
    >> ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq])
    >> drule opt_mmap_eval_distinct_lists_not_affect
    >> disch_then $ qspecl_then [`ntmps`,`REPLICATE (size_of_shape r') (Word 0w)`] mp_tac >> fs[] >> impl_tac
    >- (
      fs[Abbr `ntmps`, distinct_lists_def, EVERY_MEM]
      >> rpt strip_tac
      >> imp_res_tac mem_genlist_add_suc_val
      >> gvs[MEM_FLAT, MEM_MAP]
      >> drule_all opt_mmap_mem_func
      >> disch_tac >> gvs[]
      >> drule_at Any MEM_compile_exp_vmax
      >> disch_then $ drule_at Any >> impl_tac
      >- fs[locals_rel_def]
      >> disch_tac >> fs[]
    )
    >> disch_tac >> fs[]
    >> imp_res_tac code_rel_imp
    >> gvs[lookup_code_def, panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"]
    >- (pop_assum drule >> fs[])
    >- (
      pop_assum imp_res_tac >>
      imp_res_tac list_rel_length_shape_of_flatten >> gvs[ALL_DISTINCT_GENLIST]
    )
    >> pop_assum imp_res_tac
    >> gvs[Abbr `ntmps`, ALL_DISTINCT_GENLIST]
    >> `t.clock = s.clock` by fs[state_rel_def] >> gvs[]
    >> qmatch_asmsub_abbrev_tac `dec_clock (_ with locals := old_loc) with locals := new_loc`
    >> `dec_clock (t with locals := old_loc) with locals := new_loc = dec_clock t with locals := new_loc` by fs[dec_clock_def, state_component_equality] >> gvs[]
    >> qunabbrev_tac `new_loc`
    >> ntac 2 $ pop_assum kall_tac
    >> qmatch_asmsub_abbrev_tac `compile (ctxt_fc _ _ _ _ ns) prog` 
    >> `LENGTH ns = LENGTH (FLAT (MAP flatten args))` by fs[Abbr `ns`, LENGTH_GENLIST] 
    >> drule call_preserve_state_code_locals_rel
    >> res_tac
    >> rpt (disch_then drule) >> fs[] >> impl_tac
    >- fs[Abbr `ns`, ALL_DISTINCT_GENLIST]
    >> disch_tac >> gvs[tlc_def, slc_def]
    >> last_x_assum drule >> fs[dec_clock_def, panSemTheory.dec_clock_def]
    >> rpt (disch_then drule)
    >> disch_tac >> gvs[state_rel_def, code_rel_def, empty_locals_def, panSemTheory.empty_locals_def, ctxt_fc_def]
    >> metis_tac[]
  )
  >> call_tail_ret_impl_tac
QED

Resume pc_compile_correct[Call_Ret_Return]:
  imp_res_tac code_rel_imp >> gvs[panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] 
  >> res_tac >> fs[] >>
  cases_on ‘x’>> fs[]>>
    PURE_TOP_CASE_TAC >> fs[]
    >- (
    (* Standalone-call, one that throws the whole results away *)
        fs[] >>
        TOP_CASE_TAC >> fs[]
        >- (
          (* Standalone call, without handler *)
            drule_all list_rel_length_shape_of_flatten >> fs[]
            >> disch_tac
            >> drule call_preserve_state_code_locals_rel
            >> rpt (disch_then drule) >> fs[ALL_DISTINCT_GENLIST]
            >> disch_tac >> fs[slc_def, tlc_def]
            >> last_x_assum drule 
            >> qmatch_asmsub_abbrev_tac `code_rel nctxt (dec_clock _).code _`
            >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
            >- fs[Abbr `nctxt`, dec_clock_def, panSemTheory.dec_clock_def]
            >> disch_tac >> fs[]
            >> Cases_on `shape_of v ≠ return_sh` >> fs[]
            >> qmatch_goalsub_abbrev_tac `nested_decs ntmps _ p`
            >> fs[opt_mmap_eq_some]
            >> drule_all eval_map_comp_exp_flat_eq
            >> disch_tac >> fs[]
            >> qspecl_then [`size_of_shape return_sh`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
            >> drule eval_nested_decs_seq_res_var_eq
            >> disch_then $ qspecl_then [`ntmps`, `p`] mp_tac >> impl_tac
            >- fs[Abbr `ntmps`, LENGTH_GENLIST, LENGTH_REPLICATE, var_cexp_def, ALL_DISTINCT_GENLIST, FLAT_REPLICATE_NIL, distinct_lists_def, EVERY_MEM]
            >> disch_tac >> fs[GSYM opt_mmap_eq_some]
            >> pairarg_tac >> gvs[Abbr `p`, evaluate_def]
            >> rev_drule opt_mmap_eval_distinct_lists_not_affect
            >> disch_then $ qspecl_then [`ntmps`, `REPLICATE (size_of_shape (shape_of v)) (Word 0w)`] mp_tac >> impl_tac 
            >- (
              conj_tac
              >- fs[Abbr `ntmps`, LENGTH_GENLIST, LENGTH_REPLICATE]
              >> fs[distinct_lists_def, EVERY_MEM] 
              >> rpt strip_tac
              >> qunabbrev_tac `ntmps`
              >> imp_res_tac mem_genlist_add_suc_val
              >> gvs[MEM_FLAT, MEM_MAP]
              >> drule_all opt_mmap_mem_func
              >> disch_tac >> fs[] 
              >> imp_res_tac $ el 2 o RES_CANON $ iffLR locals_rel_def
              >> imp_res_tac MEM_compile_exp_vmax >> fs[]
            )
            >> disch_tac >> fs[lookup_code_def]
            >> res_tac >> gs[ALL_DISTINCT_GENLIST]
            >> `ALL_DISTINCT ntmps` by fs[Abbr `ntmps`, ALL_DISTINCT_GENLIST] >> fs[]
            >> `t.clock = s.clock` by fs[state_rel_def] >> gs[dec_clock_def]
            >> drule $ INST_TYPE [gamma |-> alpha] evaluate_shape_invariant_ret_inst
            >> rpt (disch_then drule) >> fs[dec_clock_def]
            >> disch_then drule
            >> disch_tac
            >> imp_res_tac is_wf_shape_of_v
            >> imp_res_tac length_flatten_eq_size_of_shape 
            >> fs[Abbr `ntmps`]
            >> qpat_x_assum `_ = (q, r')` mp_tac
            >> DEP_REWRITE_TAC [opt_mmap_some_eq_zip_flookup]
            >> conj_tac
            >- fs[ALL_DISTINCT_GENLIST, LENGTH_GENLIST, LENGTH_REPLICATE]
            >> disch_tac >> gvs[]
            >> rpt conj_tac
            >- fs[state_rel_def]
            >- (fs[Abbr `nctxt`, ctxt_fc_def, code_rel_def] >> metis_tac[])
            >- fs[Abbr `nctxt`, ctxt_fc_def]
            >> DEP_REWRITE_TAC [FUPDATE_LIST_CANCEL] 
            >> conj_tac
            >- (
              DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] 
              >> gvs[LENGTH_GENLIST, LENGTH_REPLICATE]
            )
            >> DEP_REWRITE_TAC [res_var_lookup_original_eq] >> fs[]
          ) >>
        (* Standalone call, with handler 
           Each smaller case in this case has the same exact proof as the previous case (standalone, no handler)
        *)
        PairCases_on ‘x’ >>
        fs[] >>
        PURE_TOP_CASE_TAC
        >- (
           (* Handler's exception id is NOT found in context *) 
           (* This is the same proof script as the standalone, no handler case *)
            fs[]
            >> drule_all list_rel_length_shape_of_flatten >> fs[]
            >> disch_tac
            >> drule call_preserve_state_code_locals_rel
            >> rpt (disch_then drule) >> fs[ALL_DISTINCT_GENLIST]
            >> disch_tac >> fs[slc_def, tlc_def]
            >> last_x_assum drule 
            >> qmatch_asmsub_abbrev_tac `code_rel nctxt (dec_clock _).code _`
            >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
            >- fs[Abbr `nctxt`, dec_clock_def, panSemTheory.dec_clock_def]
            >> disch_tac >> fs[]
            >> Cases_on `shape_of v ≠ return_sh` >> fs[]
            >> qmatch_goalsub_abbrev_tac `nested_decs ntmps _ p`
            >> fs[opt_mmap_eq_some]
            >> drule_all eval_map_comp_exp_flat_eq
            >> disch_tac >> fs[]
            >> qspecl_then [`size_of_shape return_sh`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
            >> drule eval_nested_decs_seq_res_var_eq
            >> disch_then $ qspecl_then [`ntmps`, `p`] mp_tac >> impl_tac
            >- fs[Abbr `ntmps`, LENGTH_GENLIST, LENGTH_REPLICATE, var_cexp_def, ALL_DISTINCT_GENLIST, FLAT_REPLICATE_NIL, distinct_lists_def, EVERY_MEM]
            >> disch_tac >> fs[GSYM opt_mmap_eq_some]
            >> pairarg_tac >> gvs[Abbr `p`, evaluate_def]
            >> rev_drule opt_mmap_eval_distinct_lists_not_affect
            >> disch_then $ qspecl_then [`ntmps`, `REPLICATE (size_of_shape (shape_of v)) (Word 0w)`] mp_tac >> impl_tac 
            >- (
              conj_tac
              >- fs[Abbr `ntmps`, LENGTH_GENLIST, LENGTH_REPLICATE]
              >> fs[distinct_lists_def, EVERY_MEM] 
              >> rpt strip_tac
              >> qunabbrev_tac `ntmps`
              >> imp_res_tac mem_genlist_add_suc_val
              >> gvs[MEM_FLAT, MEM_MAP]
              >> drule_all opt_mmap_mem_func
              >> disch_tac >> fs[] 
              >> imp_res_tac $ el 2 o RES_CANON $ iffLR locals_rel_def
              >> imp_res_tac MEM_compile_exp_vmax >> fs[]
            )
            >> disch_tac >> fs[lookup_code_def]
            >> res_tac >> gs[ALL_DISTINCT_GENLIST]
            >> `ALL_DISTINCT ntmps` by fs[Abbr `ntmps`, ALL_DISTINCT_GENLIST] >> fs[]
            >> `t.clock = s.clock` by fs[state_rel_def] >> gs[dec_clock_def]
            >> drule $ INST_TYPE [gamma |-> alpha] evaluate_shape_invariant_ret_inst
            >> rpt (disch_then drule) >> fs[dec_clock_def]
            >> disch_then drule
            >> disch_tac
            >> imp_res_tac is_wf_shape_of_v
            >> imp_res_tac length_flatten_eq_size_of_shape 
            >> fs[Abbr `ntmps`]
            >> qpat_x_assum `_ = (q, r')` mp_tac
            >> DEP_REWRITE_TAC [opt_mmap_some_eq_zip_flookup]
            >> conj_tac
            >- fs[ALL_DISTINCT_GENLIST, LENGTH_GENLIST, LENGTH_REPLICATE]
            >> disch_tac >> gvs[]
            >> rpt conj_tac
            >- fs[state_rel_def]
            >- (fs[Abbr `nctxt`, ctxt_fc_def, code_rel_def] >> metis_tac[])
            >- fs[Abbr `nctxt`, ctxt_fc_def]
            >> DEP_REWRITE_TAC [FUPDATE_LIST_CANCEL] 
            >> conj_tac
            >- (
              DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] 
              >> gvs[LENGTH_GENLIST, LENGTH_REPLICATE]
            )
            >> DEP_REWRITE_TAC [res_var_lookup_original_eq] >> fs[]
          ) >>
        (* Handler exception id IS found in context *)
        (* This is the exact same proof script as the previous case, could have done it,
           but might be better for de-proofing *)
        fs[]
        >> drule_all list_rel_length_shape_of_flatten >> fs[]
        >> disch_tac
        >> drule call_preserve_state_code_locals_rel
        >> rpt (disch_then drule) >> fs[ALL_DISTINCT_GENLIST]
        >> disch_tac >> fs[slc_def, tlc_def]
        >> last_x_assum drule 
        >> qmatch_asmsub_abbrev_tac `code_rel nctxt (dec_clock _).code _`
        >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
        >- fs[Abbr `nctxt`, dec_clock_def, panSemTheory.dec_clock_def]
        >> disch_tac >> fs[]
        >> Cases_on `shape_of v ≠ return_sh` >> fs[]
        >> qmatch_goalsub_abbrev_tac `nested_decs ntmps _ p`
        >> fs[opt_mmap_eq_some]
        >> drule_all eval_map_comp_exp_flat_eq
        >> disch_tac >> fs[]
        >> qspecl_then [`size_of_shape return_sh`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
        >> drule eval_nested_decs_seq_res_var_eq
        >> disch_then $ qspecl_then [`ntmps`, `p`] mp_tac >> impl_tac
        >- fs[Abbr `ntmps`, LENGTH_GENLIST, LENGTH_REPLICATE, var_cexp_def, ALL_DISTINCT_GENLIST, FLAT_REPLICATE_NIL, distinct_lists_def, EVERY_MEM]
        >> disch_tac >> fs[GSYM opt_mmap_eq_some]
        >> pairarg_tac >> gvs[Abbr `p`, evaluate_def]
        >> rev_drule opt_mmap_eval_distinct_lists_not_affect
        >> disch_then $ qspecl_then [`ntmps`, `REPLICATE (size_of_shape (shape_of v)) (Word 0w)`] mp_tac >> impl_tac 
        >- (
          conj_tac
          >- fs[Abbr `ntmps`, LENGTH_GENLIST, LENGTH_REPLICATE]
          >> fs[distinct_lists_def, EVERY_MEM] 
          >> rpt strip_tac
          >> qunabbrev_tac `ntmps`
          >> imp_res_tac mem_genlist_add_suc_val
          >> gvs[MEM_FLAT, MEM_MAP]
          >> drule_all opt_mmap_mem_func
          >> disch_tac >> fs[] 
          >> imp_res_tac $ el 2 o RES_CANON $ iffLR locals_rel_def
          >> imp_res_tac MEM_compile_exp_vmax >> fs[]
        )
        >> disch_tac >> fs[lookup_code_def]
        >> res_tac >> gs[ALL_DISTINCT_GENLIST]
        >> `ALL_DISTINCT ntmps` by fs[Abbr `ntmps`, ALL_DISTINCT_GENLIST] >> fs[]
        >> `t.clock = s.clock` by fs[state_rel_def] >> gs[dec_clock_def]
        >> drule $ INST_TYPE [gamma |-> alpha] evaluate_shape_invariant_ret_inst
        >> rpt (disch_then drule) >> fs[dec_clock_def]
        >> disch_then drule
        >> disch_tac
        >> imp_res_tac is_wf_shape_of_v
        >> imp_res_tac length_flatten_eq_size_of_shape 
        >> fs[Abbr `ntmps`]
        >> qpat_x_assum `_ = (q, r')` mp_tac
        >> DEP_REWRITE_TAC [opt_mmap_some_eq_zip_flookup]
        >> conj_tac
        >- fs[ALL_DISTINCT_GENLIST, LENGTH_GENLIST, LENGTH_REPLICATE]
        >> disch_tac >> gvs[]
        >> rpt conj_tac
        >- fs[state_rel_def]
        >- (fs[Abbr `nctxt`, ctxt_fc_def, code_rel_def] >> metis_tac[])
        >- fs[Abbr `nctxt`, ctxt_fc_def]
        >> DEP_REWRITE_TAC [FUPDATE_LIST_CANCEL] 
        >> conj_tac
        >- (
          DEP_REWRITE_TAC [hd $ RES_CANON MAP_ZIP] 
          >> gvs[LENGTH_GENLIST, LENGTH_REPLICATE]
        )
        >> DEP_REWRITE_TAC [res_var_lookup_original_eq] >> fs[]
      ) >>
    (* Normal assign call *)
    fs[] >>
    PURE_TOP_CASE_TAC >>
    rename1 ‘(xk:varkind,x)’ >>
    Cases_on ‘xk’ >> fs[] >>
    Cases_on `shape_of v = return_sh` >> fs[] >>
    qmatch_asmsub_abbrev_tac ‘(if X then _ else _) = (res,s1)’ >>
    cases_on ‘X’ >> fs [] >> rveq >>
    fs [is_valid_value_def] >>
    rename1 ‘ FLOOKUP s.locals q’>>
    cases_on ‘FLOOKUP s.locals q’ >> fs [] >>
    fs [wrap_rt_def] >>
    TOP_CASE_TAC >> fs []
    >- (
     (* Variable to assign is not in context *)
     fs [CaseEq "option"]
     >- (
       fs [locals_rel_def] 
       >> qpat_x_assum `!_ _. FLOOKUP s.locals _ = SOME _ ⇒ _` drule >> fs []
     ) >>
     fs [CaseEq "prod", CaseEq "shape", CaseEq "list"] >> rveq >> fs [] >>
     TOP_CASE_TAC >> fs [] >>
     drule locals_rel_lookup_ctxt >>
     disch_then drule >> strip_tac >> fs [] >>
     rveq >> fs [OPT_MMAP_def] >> rveq >>
     pop_assum (assume_tac o GSYM) >>
     rename1 ‘ FLOOKUP s.locals q = SOME x’>>
     ‘size_of_shape (shape_of x) = 1’ by
       fs [panLangTheory.size_of_shape_def] >>
     rfs [GSYM length_flatten_eq_size_of_shape]
    ) >>
    drule_at (Pos last) evaluate_shape_invariant_ret_inst2
    >> rpt (disch_then $ drule_at Any)
    >> disch_then $ qspecl_then [`shape_of x`, `prog`, `fname`] mp_tac >> impl_tac 
    >- gvs[panSemTheory.lookup_code_def]
    >> disch_tac >> fs[]
    >> imp_res_tac is_wf_shape_of_v
    >> fs [CaseEq "option"] >>
    fs [CaseEq "prod", CaseEq "shape", CaseEq "list"] >> rveq >>
    fs [ret_var_def, ret_hdl_def]
    >- (
     (* shape-rtv: One *)
     TRY (rpt TOP_CASE_TAC) >> fs [] 
     >> ret_call_shape_retv_one_tac
    )
    >- (
     (* shape-rtv: Comb *)
     qmatch_asmsub_rename_tac ‘FLOOKUP ctxt.vars m = SOME (Comb l,r'')’ >>
     cases_on ‘size_of_shape (Comb l) = 0’ >> fs []
     >- (
       TRY (rpt TOP_CASE_TAC) >> fs [] 
       >> ret_call_shape_retv_comb_zero_tac
     ) >>
     TRY (rpt TOP_CASE_TAC) >> fs [] 
     >> ret_call_shape_retv_comb_gt_one_tac
    )
    >- (
     gs [] >>
     drule_all locals_rel_lookup_ctxt >>
     simp [] >>
     metis_tac [EVAL ``is_wf_shape [] (Named nm)``]
    )
QED

Theorem not_none_then_some:
  x ≠ NONE ⇔ ∃a. x = SOME a
Proof
  Cases_on `x` >> fs[] 
QED

Theorem distinct_lists_eq_disjoint:
  distinct_lists xs ys ⇔ DISJOINT (set xs) (set ys)
Proof
  fs[DISJOINT_ALT, distinct_lists_def, EVERY_MEM]
QED

Resume pc_compile_correct[Call_Ret_Exception]:
  fs [wrap_rt_def] >>
  fs [] >>
  rename1 ‘x = (_, _)’>>cases_on ‘x’ >> fs[] >>
  PURE_TOP_CASE_TAC
  >- (
    (* Standalone call *)
      fs[] >>
      PURE_TOP_CASE_TAC >> fs[]
      >- (
         (* No handlers *)
          TOP_CASE_TAC >> fs []
          >- (
           (* Callee name not found in context *)
           fs [evaluate_def] >>
           ‘OPT_MMAP (eval t)
            (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
             fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
           fs [] >>
           fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
           drule code_rel_imp >>
           disch_then drule >>
           strip_tac >> fs []
          ) >>
          (* Callee is found in context, generate dummy assign variables *)
          Cases_on `x` >> fs[] >>
          fs [evaluate_def] >>
          ‘OPT_MMAP (eval t)
            (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
            fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
          fs [] >>
          fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
          drule code_rel_imp >>
          disch_then drule >>
          strip_tac >> fs [] >>
          fs [lookup_code_def] >>
          drule list_rel_length_shape_of_flatten >>
          fs [] >>
          strip_tac >>
          drule call_preserve_state_code_locals_rel >> fs[]
          >> rpt (disch_then drule) >> fs[ALL_DISTINCT_GENLIST]
          >> disch_tac >> fs[GSYM slc_def]
          >> last_x_assum drule >> fs[]
          >> qmatch_asmsub_abbrev_tac `compile nctxt prog`
          >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
          >- (fs[Abbr `nctxt`, dec_clock_def, panSemTheory.dec_clock_def, code_rel_def, excp_rel_def, locals_rel_def] >> metis_tac[])
          >> disch_tac >> fs[tlc_def]
          >> qspecl_then [`size_of_shape r'`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
          >> drule eval_nested_decs_seq_res_var_eq
          >> qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts _ p, _)`
          >> disch_then $ qspecl_then [`rts`, `p`] mp_tac >> impl_tac
          >- fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE, ALL_DISTINCT_GENLIST, var_cexp_def, FLAT_REPLICATE_NIL, distinct_lists_def]
          >> disch_tac >> fs[]
          >> pairarg_tac >> fs[Abbr `p`, evaluate_def]
          >> drule opt_mmap_eval_distinct_lists_not_affect
          >> disch_then $ qspecl_then [`rts`, `REPLICATE (size_of_shape r') (Word 0w)`] mp_tac >> impl_tac
          >- (
            fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
            >> irule genlist_vmax_distinct_lists_compiled_exps
            >> fs[locals_rel_def]
          )
          >> disch_tac >> gvs[lookup_code_def, ALL_DISTINCT_GENLIST]
          >> `ALL_DISTINCT rts` by fs[Abbr `rts`, ALL_DISTINCT_GENLIST] >> fs[]
          >> `t.clock = s.clock` by fs[state_rel_def] >> gvs[dec_clock_def]
          >> Cases_on `FLOOKUP nctxt.eids m` >> gvs[state_rel_def, locals_rel_def, code_rel_def, Abbr `nctxt`, panSemTheory.empty_locals_def, empty_locals_def, ctxt_fc_def]
          >> conj_tac >- metis_tac[]
          >> strip_tac >> gvs[globals_lookup_def]
      ) >>
      (* Standalone with handlers *) 
      PairCases_on ‘x’ >>
      fs[] >>
      PURE_TOP_CASE_TAC
      >- (
         (* Exception id in handler not found in context *)
          fs[] >>
          TOP_CASE_TAC >> fs[]
          >- (
           (* Function not found in context *)
           fs [evaluate_def] >>
           ‘OPT_MMAP (eval t)
            (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
             fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
           fs [] >>
           fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
           drule code_rel_imp >>
           disch_then drule >>
           strip_tac >> fs []
          ) >>
          (* Function is found in context, generate dummy names *)
          Cases_on `x` >> fs[] >>
          fs [evaluate_def] >>
          ‘OPT_MMAP (eval t)
            (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
            fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
          fs [] >>
          fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
          drule code_rel_imp >>
          disch_then drule >>
          strip_tac >> fs [] >>
          fs [lookup_code_def] >>
          drule list_rel_length_shape_of_flatten >>
          fs [] >>
          strip_tac >>
          drule call_preserve_state_code_locals_rel >> fs[]
          >> rpt (disch_then drule) >> fs[ALL_DISTINCT_GENLIST]
          >> disch_tac >> fs[GSYM slc_def]
          >> last_x_assum drule >> fs[]
          >> qmatch_asmsub_abbrev_tac `compile nctxt prog`
          >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
          >- (fs[Abbr `nctxt`, dec_clock_def, panSemTheory.dec_clock_def, code_rel_def, excp_rel_def, locals_rel_def] >> metis_tac[])
          >> disch_tac >> fs[tlc_def]
          >> qspecl_then [`size_of_shape r'`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
          >> drule eval_nested_decs_seq_res_var_eq
          >> qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts _ p, _)`
          >> disch_then $ qspecl_then [`rts`, `p`] mp_tac >> impl_tac
          >- fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE, ALL_DISTINCT_GENLIST, var_cexp_def, FLAT_REPLICATE_NIL, distinct_lists_def]
          >> disch_tac >> fs[]
          >> pairarg_tac >> fs[Abbr `p`, evaluate_def]
          >> drule opt_mmap_eval_distinct_lists_not_affect
          >> disch_then $ qspecl_then [`rts`, `REPLICATE (size_of_shape r') (Word 0w)`] mp_tac >> impl_tac
          >- (
            fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
            >> irule genlist_vmax_distinct_lists_compiled_exps
            >> fs[locals_rel_def]
          )
          >> disch_tac >> gvs[lookup_code_def, ALL_DISTINCT_GENLIST]
          >> `ALL_DISTINCT rts` by fs[Abbr `rts`, ALL_DISTINCT_GENLIST] >> fs[]
          >> `t.clock = s.clock` by fs[state_rel_def] >> gvs[dec_clock_def]
          >> Cases_on `FLOOKUP nctxt.eids m` >> gvs[]
          >> Cases_on `m = x0` >> fs[]
          >- fs[Abbr `nctxt`, ctxt_fc_def]
          >> gvs[state_rel_def, locals_rel_def, code_rel_def, Abbr `nctxt`, panSemTheory.empty_locals_def, empty_locals_def, ctxt_fc_def]
          >> conj_tac >- metis_tac[]
          >> strip_tac >> gvs[globals_lookup_def]
      ) >>
      (* Standalone call with handler, exception id is found in context *)
      fs[] >>
      TOP_CASE_TAC >> fs[] 
      >- (
       (* Function/callee name is not found in context *)
       fs [evaluate_def] >>
       ‘OPT_MMAP (eval t)
        (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
         fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
       fs [] >>
       fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
       drule code_rel_imp >>
       disch_then drule >>
       strip_tac >> fs []
      ) >>
      (* Function/callee name is found in context *)
      Cases_on `x'` >> fs[] >>
      fs [evaluate_def] >>
      ‘OPT_MMAP (eval t)
        (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
        fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
      fs [] >>
      fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
      drule code_rel_imp >>
      disch_then drule >>
      strip_tac >> fs [] >>
      fs [lookup_code_def] >>
      drule list_rel_length_shape_of_flatten >>
      fs [] >>
      strip_tac >>
      drule call_preserve_state_code_locals_rel >> fs[]
      >> rpt (disch_then drule) >> fs[ALL_DISTINCT_GENLIST]
      >> disch_tac >> fs[GSYM slc_def]
      >> last_x_assum drule >> fs[]
      >> qmatch_asmsub_abbrev_tac `compile nctxt prog`
      >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
      >- (fs[Abbr `nctxt`, dec_clock_def, panSemTheory.dec_clock_def, code_rel_def, excp_rel_def, locals_rel_def] >> metis_tac[])
      >> disch_tac >> fs[tlc_def]
      >> qspecl_then [`size_of_shape r'`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
      >> drule eval_nested_decs_seq_res_var_eq
      >> qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts _ p, _)`
      >> disch_then $ qspecl_then [`rts`, `p`] mp_tac >> impl_tac
      >- fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE, ALL_DISTINCT_GENLIST, var_cexp_def, FLAT_REPLICATE_NIL, distinct_lists_def]
      >> disch_tac >> fs[]
      >> pairarg_tac >> fs[Abbr `p`, evaluate_def]
      >> drule opt_mmap_eval_distinct_lists_not_affect
      >> disch_then $ qspecl_then [`rts`, `REPLICATE (size_of_shape r') (Word 0w)`] mp_tac >> impl_tac
      >- (
        fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
        >> irule genlist_vmax_distinct_lists_compiled_exps
        >> fs[locals_rel_def]
      )
      >> disch_tac >> gvs[lookup_code_def, ALL_DISTINCT_GENLIST]
      >> `ALL_DISTINCT rts` by fs[Abbr `rts`, ALL_DISTINCT_GENLIST] >> fs[]
      >> `t.clock = s.clock` by fs[state_rel_def] >> gvs[dec_clock_def]
      >> Cases_on `FLOOKUP nctxt.eids m` >> gvs[]
      >> `FLOOKUP ctxt.eids m = SOME x'` by fs[Abbr `nctxt`, ctxt_fc_def]
      >> Cases_on `x' = x` >> gvs[]
      >- (
        rev_drule $ iffLR excp_rel_def
        >> disch_tac >> fs[]
        >> pop_assum drule
        >> disch_then rev_drule >> disch_tac >> fs[]
        >> pop_assum kall_tac
        >> pop_assum $ assume_tac o GSYM
        >> drule_all fdoms_eq_flookup_some_none
        >> disch_tac >> gvs[CaseEq "option", CaseEq "bool"]
        >> pairarg_tac >> fs[exp_hdl_def]
        >> qpat_x_assum `is_valid_value _ _ _ _` mp_tac
        >> simp[is_valid_value_def]
        >> TOP_CASE_TAC >> fs[]
        >> disch_tac >> fs[]
        >> drule_all locals_rel_lookup_ctxt
        >> strip_tac >> fs[]
        >> imp_res_tac length_flatten_eq_size_of_shape >> fs[]
        >> `ALL_DISTINCT ns` by metis_tac[locals_rel_def, no_overlap_def]
        >> drule evaluate_seq_assign_load_globals
        >> qmatch_asmsub_abbrev_tac `evaluate (nested_seq excp_handler, nstate)`
        >> disch_then $ qspecl_then [`nstate`, `0w`] mp_tac >> fs[] >> impl_tac
        >- (
          reverse $ Cases_on `1 ≤ size_of_shape (shape_of x')` >> fs[NOT_LE] 
          >> conj_tac >> fs[Abbr `nstate`]
          >- (
            ntac 2 strip_tac
            >> DEP_REWRITE_TAC[NOT_MEM_FLOOKUP_ZIP]
            >> drule_all opt_mmap_mem_func
            >> disch_tac >> fs[]
            >> qpat_x_assum `locals_rel _ s.locals _` $ assume_tac o CONJUNCT1 o CONJUNCT2 o SRULE[locals_rel_def]
            >> pop_assum $ imp_res_tac o SRULE[ctxt_max_def]
            >> strip_tac
            >> fs[Abbr `rts`]
            >> imp_res_tac mem_genlist_add_suc_val >> fs[]
          )
          >> qpat_x_assum `globals_lookup _ _ = _` $ assume_tac o SRULE[globals_lookup_def]
          >> rpt strip_tac >> gs[]
          >> drule_all opt_mmap_mem_func >> fs[]
        )
        >> disch_tac >> gvs[Abbr `nstate`, panSemTheory.set_var_def]
        >> qmatch_asmsub_abbrev_tac `evaluate (compile _ _, _ with locals := tlocs)` 
        >> last_x_assum $ qspecl_then [`t1 with locals := tlocs`, `ctxt`] mp_tac >> impl_tac
        >- (
          gvs[state_rel_def, code_rel_def, excp_rel_def, Abbr `nctxt`, ctxt_fc_def]
          >> conj_tac >- metis_tac[]
          >> gvs[locals_rel_def, Abbr `tlocs`, FLOOKUP_UPDATE]
          >> rpt strip_tac >> fs[]
          >> Cases_on `x1 = vname` >> gvs[]
          >- (
            DEP_REWRITE_TAC[opt_mmap_some_eq_zip_flookup]
            >> conj_tac >> fs[LENGTH_MAP]
            >> irule map_some_the_map
            >> fs[GSYM opt_mmap_eq_some] 
            >> reverse $ Cases_on `1 ≤ size_of_shape (shape_of x')` >> fs[NOT_LE] 
            >- (
              qpat_x_assum `shape_of _ = shape_of _` $ fs o single o GSYM
              >> metis_tac[flatten_nil_no_size]
            ) 
            >> fs[] 
            >> qpat_x_assum `globals_lookup _ _ = _` $ assume_tac o SRULE[globals_lookup_def] >> gvs[]
          ) >>
          res_tac >> gvs[] 
          >> ntac 2 $ DEP_REWRITE_TAC[opt_mmap_disj_zip_flookup]
          >> fs[LENGTH_REPLICATE, Abbr `rts`]
          >> conj_tac
          >- (
            metis_tac[distinct_lists_eq_disjoint, no_overlap_def]
          )
          >> fs[distinct_lists_def, EVERY_MEM]
          >> rpt strip_tac
          >> fs[ctxt_max_def] >> res_tac >> gvs[]
          >> imp_res_tac mem_genlist_add_suc_val >> fs[]
        ) >>
        disch_tac >> gvs[]
        >> conj_tac
        >- fs[state_rel_def]
        >> Cases_on `res` >> TRY (Cases_on `x''`) >> fs[]
        >>~- ([`locals_rel _ _ (FOLDL _ _ _)`],
          fs[locals_rel_def]
          >> rpt strip_tac >> res_tac >> gvs[]
          >> qpat_assum `OPT_MMAP (FLOOKUP _) _ = SOME (flatten v')` $ PURE_REWRITE_TAC o single o GSYM
          >> irule OPT_MMAP_CONG >> fs[]
          >> rpt strip_tac 
          >> irule flookup_res_var_distinct_zip_eq >> fs[LENGTH_MAP]
          >> strip_tac >> fs[ctxt_max_def] >> res_tac >> gvs[Abbr `rts`]
          >> imp_res_tac mem_genlist_add_suc_val >> fs[])
        >> TOP_CASE_TAC >> fs[]
        >> strip_tac >> fs[globals_lookup_def]
      ) >> 
      Cases_on `x0 = m` >> gvs[state_rel_def, locals_rel_def, panSemTheory.empty_locals_def, empty_locals_def, code_rel_def, locals_rel_def, excp_rel_def, Abbr `nctxt`, ctxt_fc_def]
      >> conj_tac >- metis_tac[]
      >> strip_tac >> fs[globals_lookup_def]
  ) >>
  fs[] >>
  PURE_TOP_CASE_TAC >>
  rename1 ‘(xk:varkind,x)’ >>
  Cases_on ‘xk’ >> fs[] >>
  rename1 ‘r' = SOME (_, _, _)’>>cases_on ‘r'’ >>
  fs []
  >- (
    ret_call_excp_reult_handle_none_tac
  ) >>
  rename1 ‘ww = (m', _, _)’>>PairCases_on ‘ww’ >> fs [] >> rveq >>
  rename1 ‘FLOOKUP ctxt.vars m’ >>
  rename1 ‘FLOOKUP ctxt.eids m0’ >>
  reverse (cases_on ‘m' = m0’) >> fs []
  (* eids mismatch *)
  >- ret_call_excp_reult_handle_uneq_exp_tac >>
  (* handling exception *)
  rename [‘geid = eid’] >>
  cases_on ‘FLOOKUP s.eshapes eid’ >> fs [] >> rveq >>
  cases_on ‘shape_of v = x’ >> fs [] >>
  qmatch_asmsub_abbrev_tac ‘(if X then _ else _) = (res,s1)’ >>
  cases_on ‘X’ >> fs [] >>
  cases_on ‘FLOOKUP ctxt.eids eid’ >> fs []
  >- (fs [excp_rel_def] >>
      imp_res_tac fdoms_eq_flookup_some_none >> fs []) >>
  rename1 ‘FLOOKUP ctxt.eids eid = SOME x'’>>
  cases_on ‘x'’ >> fs [] >> rveq >>
  TOP_CASE_TAC >> fs []>>
  rename1 ‘exp_hdl _ m''’
  >- ret_call_excp_handler_tac >>
  TOP_CASE_TAC >> fs [] >>
  ret_call_excp_handler_tac
QED

Resume pc_compile_correct[Call_Ret_FinalFFI]:
  cases_on ‘x’ >> fs []>>
  cases_on ‘r'’ >> fs []
  >- (
    TRY (rpt TOP_CASE_TAC) >> fs [nested_decs_def] 
    >~ [`evaluate (nested_decs _ _ _, _)`]
    >- (
      qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts _ p, _)`
      >> qspecl_then [`size_of_shape r'`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
      >> drule eval_nested_decs_seq_res_var_eq
      >> disch_then $ qspecl_then [`rts`, `p`] mp_tac >> fs[] >> impl_tac 
      >- fs[Abbr `rts`, distinct_lists_def, EVERY_MEM, ALL_DISTINCT_GENLIST, var_cexp_def, FLAT_REPLICATE_NIL]
      >> disch_tac >> fs[]
      >> pairarg_tac >> fs[Abbr `p`, evaluate_def]
      >> pop_assum mp_tac
      >> ‘OPT_MMAP (eval t)
        (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
        fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq])
      >> drule opt_mmap_eval_distinct_lists_not_affect
      >> disch_then $ qspecl_then [`rts`, `REPLICATE (size_of_shape r') (Word 0w)`] mp_tac >> impl_tac
      >- (
        fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
        >> irule genlist_vmax_distinct_lists_compiled_exps
        >> fs[locals_rel_def]
      )
      >> imp_res_tac code_rel_imp >> fs[]
      >> disch_tac >> gvs[panSemTheory.lookup_code_def, lookup_code_def, CaseEq "option", CaseEq "prod"]
      >> pop_assum kall_tac
      >> pop_assum imp_res_tac >> fs[]
      >> drule_all list_rel_length_shape_of_flatten >> fs[]
      >> disch_tac >> fs[ALL_DISTINCT_GENLIST]
      >> `ALL_DISTINCT rts` by fs[Abbr `rts`, ALL_DISTINCT_GENLIST] >> fs[]
      >> `t.clock = s.clock` by fs[state_rel_def] >> gs[]
      >> qmatch_asmsub_abbrev_tac `FLOOKUP t.code fname = SOME (ns, compile _ _)`
      >> `LENGTH ns = LENGTH (FLAT (MAP flatten args))` by fs[Abbr `ns`, LENGTH_GENLIST]
      >> qpat_x_assum `!_ _ _ _. FLOOKUP s.code _ = SOME _ ⇒ FLOOKUP _.funcs _ = SOME _` imp_res_tac
      >> gvs[]
      >> `ALL_DISTINCT ns` by fs[Abbr `ns`, ALL_DISTINCT_GENLIST]
      >> drule_all call_preserve_state_code_locals_rel
      >> disch_tac >> fs[dec_clock_def, tlc_def]
      >> fs[slc_tlc_rw]
      >> qmatch_goalsub_abbrev_tac `evaluate (compile nctxt _, tnew)`
      >> last_x_assum drule
      >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac >> fs[]
      >- metis_tac[]
      >> disch_tac >> gvs[state_rel_def, locals_rel_def, panSemTheory.empty_locals_def, empty_locals_def, code_rel_def, excp_rel_def, slc_def, tlc_def, Abbr `nctxt`, ctxt_fc_def]
      >> disch_tac >> gvs[]
      >> metis_tac[]
    )
    >-  (
       TRY (imp_res_tac no_overlap_wrap_rt_some_all_distinct >>
       pop_assum mp_tac >> impl_tac >- fs[locals_rel_def] >> disch_tac) >>
       fs [evaluate_def] >>
       ‘OPT_MMAP (eval t)
        (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
         fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
       fs [] >>
       fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
       drule code_rel_imp >>
       disch_then drule >>
       strip_tac >> fs [] >>
       fs [lookup_code_def] >>
       drule list_rel_length_shape_of_flatten >>
       fs [] >>
       strip_tac >>
       fs [ALL_DISTINCT_GENLIST]
    )
    >> call_tail_ret_impl_tac
  ) >>
  PairCases_on ‘x’ >>
  TRY (rpt TOP_CASE_TAC) >> fs [] 
  >>~- ([`evaluate (nested_decs [] [] _, _)`],
     fs[nested_decs_def] >>
     TRY (imp_res_tac no_overlap_wrap_rt_some_all_distinct >>
     pop_assum mp_tac >> impl_tac >- fs[locals_rel_def] >> disch_tac) >>
     fs [evaluate_def] >>
     ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
       fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
     fs [] >>
     fs [panSemTheory.lookup_code_def, CaseEq "option", CaseEq "prod"] >> rveq >>
     drule code_rel_imp >>
     disch_then drule >>
     strip_tac >> fs [] >>
     fs [lookup_code_def] >>
     drule list_rel_length_shape_of_flatten >>
     fs [] >>
     strip_tac >>
     fs [ALL_DISTINCT_GENLIST]
  )
  >>~- ([`evaluate (nested_decs _ _ _, _)`],
    qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts _ p, _)`
    >> qspecl_then [`size_of_shape r'`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const
    >> drule eval_nested_decs_seq_res_var_eq
    >> disch_then $ qspecl_then [`rts`, `p`] mp_tac >> fs[] >> impl_tac 
    >- fs[Abbr `rts`, distinct_lists_def, EVERY_MEM, ALL_DISTINCT_GENLIST, var_cexp_def, FLAT_REPLICATE_NIL]
    >> disch_tac >> fs[]
    >> pairarg_tac >> fs[Abbr `p`, evaluate_def]
    >> pop_assum mp_tac
    >> ‘OPT_MMAP (eval t)
      (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
      fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq])
    >> drule opt_mmap_eval_distinct_lists_not_affect
    >> disch_then $ qspecl_then [`rts`, `REPLICATE (size_of_shape r') (Word 0w)`] mp_tac >> impl_tac
    >- (
      fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
      >> irule genlist_vmax_distinct_lists_compiled_exps
      >> fs[locals_rel_def]
    )
    >> imp_res_tac code_rel_imp >> fs[]
    >> disch_tac >> gvs[panSemTheory.lookup_code_def, lookup_code_def, CaseEq "option", CaseEq "prod"]
    >> pop_assum kall_tac
    >> pop_assum imp_res_tac >> fs[]
    >> drule_all list_rel_length_shape_of_flatten >> fs[]
    >> disch_tac >> fs[ALL_DISTINCT_GENLIST]
    >> `ALL_DISTINCT rts` by fs[Abbr `rts`, ALL_DISTINCT_GENLIST] >> fs[]
    >> `t.clock = s.clock` by fs[state_rel_def] >> gs[]
    >> qmatch_asmsub_abbrev_tac `FLOOKUP t.code fname = SOME (ns, compile _ _)`
    >> `LENGTH ns = LENGTH (FLAT (MAP flatten args))` by fs[Abbr `ns`, LENGTH_GENLIST]
    >> qpat_x_assum `!_ _ _ _. FLOOKUP s.code _ = SOME _ ⇒ FLOOKUP _.funcs _ = SOME _` imp_res_tac
    >> gvs[]
    >> `ALL_DISTINCT ns` by fs[Abbr `ns`, ALL_DISTINCT_GENLIST]
    >> drule_all call_preserve_state_code_locals_rel
    >> disch_tac >> fs[dec_clock_def, tlc_def]
    >> fs[slc_tlc_rw]
    >> qmatch_goalsub_abbrev_tac `evaluate (compile nctxt _, tnew)`
    >> last_x_assum drule
    >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac >> fs[]
    >- metis_tac[]
    >> disch_tac >> gvs[state_rel_def, locals_rel_def, panSemTheory.empty_locals_def, empty_locals_def, code_rel_def, excp_rel_def, slc_def, tlc_def, Abbr `nctxt`, ctxt_fc_def]
    >> disch_tac >> gvs[]
    >> metis_tac[]
  )
  >> call_tail_ret_impl_tac
QED

Theorem locals_id_update[local]:
  t with locals := t.locals = t
Proof
  rw[state_component_equality]
QED

Theorem MAP_SOME_MEM_lemma:
  MAP f (FLAT xs) = MAP SOME (FLAT ys) ∧
  MEM zs xs ∧ MEM z zs ⇒ ∃r y. f z = SOME y ∧ MEM y (FLAT ys)
Proof
  rw[LIST_EQ_REWRITE] >>
  gvs[MEM_EL,PULL_EXISTS] >>
  gvs[EL_MAP] >>
  irule_at (Pos hd) EQ_TRANS >>
  first_x_assum $ irule_at $ Pat ‘_ = SOME _’ >>
  last_x_assum $ SUBST_ALL_TAC o GSYM >>
  ntac 2 $ pop_assum mp_tac >>
  rename1 ‘n < LENGTH _’ >>
  rename1 ‘m < LENGTH(EL _ _)’ >>
  MAP_EVERY qid_spec_tac [‘n’,‘m’] >>
  Induct_on ‘xs’ >>
  rw[] >>
  Cases_on ‘n’ >> gvs[]
  >- (qexists_tac ‘m’ >> rw[EL_APPEND1]) >>
  qrefine ‘LENGTH h + _’ >>
  rw[EL_APPEND2]
QED

Theorem update_locals_not_vars_eval_mmap:
  (∀n e. MEM e es ∧ MEM n (var_cexp e) ⇒ n ≠ x) ⇒
  OPT_MMAP (eval (t with locals := t.locals |+ (x,v))) es = OPT_MMAP (eval t) es
Proof
  strip_tac >>
  irule IMP_OPT_MMAP_EQ >>
  rw[MAP_EQ_f] >>
  unabbrev_all_tac >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [update_locals_not_vars_eval_eq''] >>
  metis_tac[locals_id_update]
QED

Theorem res_var_commutes':
  n ≠ h ⇒
  res_var (res_var lc (h,v)) (n,v') =
  res_var (res_var lc (n,v')) (h,v)
Proof
  rw[fmap_eq_flookup,flookup_res_var_thm] >> rw[]
QED

Theorem EL_load_globals:
  ∀n m w. n < m ⇒ EL n (load_globals w m) = LoadGlob(w + n2w n)
Proof
  Induct_on ‘n’ >>
  Cases >>
  rw[load_globals_def,EL_CONS_IF] >>
  rw[n2w_SUC]
QED

Theorem eval_distinct_lists_not_affect:
  ∀vs s e w nvals.
    LENGTH vs = LENGTH nvals ∧ distinct_lists vs (var_cexp e) ⇒
      eval (s with locals := s.locals |++ ZIP (vs, nvals)) e = eval s e
Proof
  Induct >> rw[] 
  >- (`s with locals := s.locals = s` by fs[state_component_equality] >> fs[FUPDATE_LIST])
  >> Cases_on `nvals` >> fs[FUPDATE_LIST_THM]
  >> last_x_assum $ qspecl_then [`s with locals := s.locals |+ (h, h')`, `e`, `t`] mp_tac >> fs[] >> impl_tac
  >- fs[distinct_lists_def]
  >> disch_tac >> fs[]
  >> irule update_locals_not_vars_eval_eq'
  >> fs[distinct_lists_def]
QED

Theorem opt_mmap_eval_distinct_lists_not_affect':
  ∀es s ws vs nvals.
    LENGTH vs = LENGTH nvals ∧ distinct_lists vs (FLAT (MAP var_cexp es)) ⇒
      OPT_MMAP (eval (s with locals := s.locals |++ ZIP (vs, nvals))) es = OPT_MMAP (eval s) es
Proof
  rw[]
  >> irule OPT_MMAP_CONG >> fs[]
  >> rpt strip_tac >> fs[]
  >> irule eval_distinct_lists_not_affect >> fs[distinct_lists_def, EVERY_MEM]
  >> rpt strip_tac >> res_tac >> fs[MEM_FLAT, MEM_MAP]
  >> metis_tac[]
QED

Theorem evaluate_nested_decs_load_globals:
  globals_lookup s rv = SOME (rvs) ∧ size_of_shape (shape_of rv) ≤ 32 ∧
  ALL_DISTINCT vs ∧
  LENGTH vs = size_of_shape(shape_of rv) ⇒
  evaluate (nested_decs vs (load_globals 0w (size_of_shape(shape_of rv))) p,s) =
  let (res,s') = evaluate (p,s with locals := s.locals |++ ZIP (vs, rvs))
  in  (res,s' with locals := FOLDL res_var s'.locals (ZIP (vs,MAP (FLOOKUP s.locals) vs)))
Proof
  rw[globals_lookup_def] >>
  rename1 ‘LENGTH vs = n’ >>
  gvs[] >>
  drule_at (Pos last) eval_nested_decs_seq_res_var_eq >>
  disch_then(qspec_then ‘(load_globals 0w (LENGTH vs))’ mp_tac) >>
  simp[length_load_globals_eq_read_size] >>
  disch_then(qspec_then ‘s’ mp_tac) >>
  disch_then(qspec_then ‘rvs’ mp_tac) >>
  disch_then(qspec_then ‘p’ mp_tac) >>
  impl_tac
  >- (gvs[opt_mmap_eq_some] >>
      conj_tac
      >- (match_mp_tac EQ_TRANS >>
          first_x_assum $ irule_at $ Pos last >>
          rw[LIST_EQ_REWRITE,length_load_globals_eq_read_size] >>
          rw[EL_MAP,length_load_globals_eq_read_size,EL_load_globals,
             eval_def]) >>
      ntac 2 $ last_x_assum kall_tac >>
      rename1 ‘load_globals w’ >>
      qid_spec_tac ‘w’ >>
      rw[distinct_lists_def,MEM_FLAT,MEM_MAP,PULL_EXISTS,PULL_FORALL,EVERY_MEM] >>
      rename1 ‘MEM e (load_globals w n)’ >>
      ‘MEM e (load_globals w n) ⇒ var_cexp e = []’
        by(rpt $ pop_assum kall_tac >>
           qid_spec_tac ‘w’ >>
           Induct_on ‘n’ >>
           rw[load_globals_def,var_cexp_def] >>
           res_tac >> gvs[var_cexp_def]) >>
      metis_tac[MEM]) >>
  rw[ELIM_UNCURRY]
QED

Theorem locals_rel_extend_new_var:
  ∀ct s t v x ns.
    locals_rel ct s t ∧
    is_wf_shape_nil (shape_of v) ∧
    ALL_DISTINCT ns ∧
    (!x. MEM x ns ⇒ ct.vmax < x ∧ x ≤ ct.vmax + size_of_shape (shape_of v)) ∧
    LENGTH ns = size_of_shape (shape_of v) ⇒
    locals_rel (ct with <|vars := ct.vars |+ (x, (shape_of v, ns));
                          vmax := ct.vmax + size_of_shape (shape_of v)|>) (s |+ (x,v)) (t |++ ZIP(ns, flatten v))
Proof
  rpt strip_tac
  >> fs[locals_rel_def]
  >> rpt conj_tac
  >- (
    fs[no_overlap_def] >> conj_tac
    >- (
      rpt strip_tac >> fs[FLOOKUP_UPDATE]
      >> Cases_on `x = x'` >> gvs[]
      >> res_tac >> fs[]
    )
    >> rpt strip_tac >> fs[FLOOKUP_UPDATE]
    >> every_case_tac >> gvs[]
    >> fs[GSYM distinct_lists_eq_disjoint, distinct_lists_def, EVERY_MEM, ctxt_max_def]
    >> res_tac >> fs[]
  )
  >- (
    fs[ctxt_max_def]
    >> rpt strip_tac >> fs[FLOOKUP_UPDATE]
    >> every_case_tac >> gvs[]
    >> res_tac >> metis_tac[iterateTheory.LE_ADDR, LE_ADD, LE_TRANS]
  )
  >> rpt strip_tac >> fs[FLOOKUP_UPDATE]
  >> every_case_tac >> gvs[]
  >- (
    irule opt_mmap_some_eq_zip_flookup
    >> imp_res_tac length_flatten_eq_size_of_shape >> fs[] 
  )
  >> res_tac >> fs[]
  >> DEP_REWRITE_TAC [opt_mmap_disj_zip_flookup] >> fs[]
  >> conj_tac
  >- (
    fs[ctxt_max_def] >> res_tac >> gvs[distinct_lists_def, EVERY_MEM]
    >> rpt strip_tac >> fs[]
    >> metis_tac[NOT_LE]
  )
  >> metis_tac[length_flatten_eq_size_of_shape]
QED

Theorem flookup_res_var_thm_quant:
  ∀l m v n. FLOOKUP (res_var l (m, v)) n = if n = m then v else FLOOKUP l n
Proof
  metis_tac[flookup_res_var_thm]
QED

Resume pc_compile_correct[DecCall]:
  rpt strip_tac >>
  gvs[panSemTheory.evaluate_def,compile_def,evaluate_def,localised_prog_def] >>
  gvs[shape_of_def,panLangTheory.size_of_shape_def,flatten_def] >>
  Cases_on ‘OPT_MMAP (eval s) argexps’ >> gvs[] >>
  rename1 ‘OPT_MMAP (eval s) argexps = SOME args’ >>
  ‘OPT_MMAP (eval t)
   (FLAT (MAP FST (MAP (compile_exp ctxt) argexps))) = SOME (FLAT (MAP flatten args))’ by (
    fs [opt_mmap_eq_some] >> metis_tac [eval_map_comp_exp_flat_eq]) >>
  gvs[CaseEq "option", pair_case_eq] >>
  drule_then drule lookup_code_wf_shape_invariant_step >>
  impl_tac >- (
    fs [state_rel_def, FEVERY_FEMPTY] >>
    drule locals_rel_wf_shape >>
    simp []
  ) >>
  drule_all opt_mmap_eval_is_wf_shape_v >>
  gvs[panSemTheory.lookup_code_def,CaseEq "option", CaseEq "prod"] >>
  drule_then drule code_rel_imp >>
  rw[] >>
  ‘size_of_shape (Comb (MAP SND vshapes)) = LENGTH (FLAT (MAP flatten args))’
    by(qhdtm_x_assum ‘LIST_REL’ mp_tac >>
       qpat_x_assum `EVERY is_wf_shape_v_nil _` mp_tac >>
       fs [panLangTheory.size_of_shape_def, LENGTH_FLAT, MAP_MAP_o] >>
       rw [] >>
       AP_TERM_TAC (* xs = ys ==> SUM xs = SUM ys *) >>
       fs [EVERY_EL, LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
       simp [length_flatten_eq_size_of_shape, is_wf_shape_v_nil]
  )>>
  Cases_on ‘s.clock = 0’
  >- (
    rw[] >>
    Cases_on `shape = return_sh` >> fs[] >>
    qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts (REPLICATE ret_len _) p, nctxt)` >>

    qspecl_then [`ret_len`, `nctxt`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const >>
    drule eval_nested_decs_seq_res_var_eq >> 
    disch_then $ qspecl_then [`rts`, `p`] mp_tac >> impl_tac
    >- (
      gvs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE, ALL_DISTINCT_GENLIST, var_cexp_def, 
          FLAT_REPLICATE_NIL, distinct_lists_def,
          oneline wrap_rt_def, CaseEq "option", CaseEq "prod", CaseEq "shape", CaseEq "list"]
    )
    >> disch_tac >> fs[]
    >> pairarg_tac 
    >> fs[Abbr `p`, evaluate_def, AllCaseEqs()]
    >> pairarg_tac >> fs[]
    >> drule opt_mmap_eval_distinct_lists_not_affect
    >> disch_then $ qspecl_then [`rts`, `REPLICATE ret_len (Word 0w)`] mp_tac >> fs[] >> impl_tac
    >- (
      gvs[Abbr `rts`, LENGTH_GENLIST]
      >> irule genlist_vmax_distinct_lists_compiled_exps
      >> fs[locals_rel_def]
    )
    >> disch_tac >> gvs[lookup_code_def, ALL_DISTINCT_GENLIST]
    >> `ALL_DISTINCT rts` by gvs[Abbr `rts`, ALL_DISTINCT_GENLIST] 
    >> gvs[state_rel_def, panSemTheory.empty_locals_def, empty_locals_def, code_rel_def, excp_rel_def, ctxt_fc_def]
    >> metis_tac[]
  ) >>
  Cases_on `shape = return_sh` >> fs[] >>
  gvs[] >>
  Cases_on ‘evaluate (prog, dec_clock s with locals := FEMPTY |++ ZIP (MAP FST vshapes,args))’ >>
  rename1 ‘evaluate (_, dec_clock _ with locals := _) = (nres,ns)’ >>
  gvs[] >>
  Cases_on ‘nres = SOME Error’ >> gvs[] >>
  gvs[CaseEq "option"] >>
  rename1 ‘evaluate (_, dec_clock _ with locals := _) = (SOME nres,ns)’ >>
  qhdtm_assum ‘state_rel’ $ strip_assume_tac o REWRITE_RULE[state_rel_def] >>
  gvs[evaluate_def,compile_def,lookup_code_def,ALL_DISTINCT_GENLIST,PULL_EXISTS] >>
  (* Unwrap the nested declarations *)
  qmatch_goalsub_abbrev_tac `evaluate (nested_decs rts (REPLICATE ret_len _) p, _)` >>
  qspecl_then [`ret_len`, `t`] (assume_tac o PURE_REWRITE_RULE[opt_mmap_eq_some]) evaluate_replicate_const >>
  drule eval_nested_decs_seq_res_var_eq >> 
  disch_then $ qspecl_then [`rts`, `p`] mp_tac >> impl_tac
  >- (
    gvs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE, ALL_DISTINCT_GENLIST, var_cexp_def, 
        FLAT_REPLICATE_NIL, distinct_lists_def,
        oneline wrap_rt_def, CaseEq "option", CaseEq "prod", CaseEq "shape", CaseEq "list"]
  )
  >> fs[]
  >> pairarg_tac >> fs[]
  >> disch_tac >> fs[]
  (* Apply the IH for the callee's body *)
  >> `ALL_DISTINCT rts` by fs[Abbr `rts`, ALL_DISTINCT_GENLIST]
  >> fs[slc_tlc_rw]
  >> qmatch_asmsub_abbrev_tac `FLOOKUP t.code fname = SOME(fargs, compile _ _)`
  >> `LENGTH fargs = LENGTH (FLAT (MAP flatten args))` by fs[Abbr `fargs`, LENGTH_GENLIST]
  >> `ALL_DISTINCT fargs` by fs[Abbr `fargs`, ALL_DISTINCT_GENLIST]
  >> drule_all call_preserve_state_code_locals_rel
  >> disch_tac >> fs[]
  >> last_x_assum drule
  >> qmatch_asmsub_abbrev_tac `locals_rel nctxt (slc _ _) (tlc _ _)`
  >> disch_then $ qspec_then `nctxt` mp_tac >> impl_tac
  >- (
    gvs[code_rel_def, dec_clock_def, panSemTheory.dec_clock_def, excp_rel_def, locals_rel_def, slc_def, ctxt_fc_def, Abbr `fargs`] >> metis_tac[]
  )
  (* Unfold the compiled Call *)
  >> disch_tac >> gvs[Abbr `p`, evaluate_def]
  >> pairarg_tac >> gvs[]
  >> pop_assum mp_tac
  >> DEP_REWRITE_TAC[opt_mmap_eval_distinct_lists_not_affect']
  >> conj_tac
  >- (
    fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
    >> irule genlist_vmax_distinct_lists_compiled_exps
    >> fs[locals_rel_def]
  )
  >> fs[lookup_code_def, tlc_def, dec_clock_def]
  (* Split case on the call result *)
  >> Cases_on `nres` >> fs[]
  (* Timeout *)
  >- (
    disch_tac >> gvs[state_rel_def, panSemTheory.empty_locals_def, code_rel_def, excp_rel_def, ctxt_fc_def, empty_locals_def, Abbr `nctxt`]
    >> metis_tac[]
  )
  (* Return *)
  >- (
    pairarg_tac >> gvs[Abbr `ret_len`]
    >> fs[GSYM dec_clock_def]
    >> drule $ INST_TYPE [gamma |-> alpha] evaluate_shape_invariant_ret_inst
    >> fs[slc_tlc_rw]
    >> disch_then $ qspecl_then [`tlc fargs args`, `dec_clock t with locals := tlc fargs args`, `nctxt`] assume_tac >> gs[]
    >> imp_res_tac is_wf_shape_of_v
    >> imp_res_tac length_flatten_eq_size_of_shape 
    >> Cases_on `shape_of v = return_sh` >> fs[]
    >> `LENGTH (flatten v) = LENGTH rts` by fs[Abbr `rts`, LENGTH_GENLIST] >> fs[]
    >> DEP_REWRITE_TAC[opt_mmap_some_eq_zip_flookup]
    >> conj_tac
    >- fs[Abbr `rts`, ALL_DISTINCT_GENLIST, LENGTH_GENLIST, LENGTH_REPLICATE]
    >> disch_tac >> gvs[]
    >> qpat_x_assum `_ = (q, r)` mp_tac
    >> DEP_REWRITE_TAC [FUPDATE_LIST_CANCEL]
    >> conj_tac
    >- (ntac 2 $ DEP_REWRITE_TAC[hd $ RES_CANON MAP_ZIP] >> gvs[LENGTH_REPLICATE])
    >> qmatch_goalsub_abbrev_tac `evaluate (compile upd_ctxt _, tlocs)`
    >> disch_tac >> fs[]
    (* Apply the IH for the scoped body *)
    >> last_x_assum $ qspecl_then [`tlocs`, `upd_ctxt`] mp_tac >> impl_tac
    >- (
      rpt conj_tac
      >- fs[state_rel_def, Abbr `tlocs`, panSemTheory.set_var_def]
      >- (fs[code_rel_def, Abbr `tlocs`, Abbr `upd_ctxt`, panSemTheory.set_var_def, Abbr `nctxt`, ctxt_fc_def] >> metis_tac[])
      >- fs[excp_rel_def, Abbr `tlocs`, Abbr `upd_ctxt`, panSemTheory.set_var_def, Abbr `nctxt`, ctxt_fc_def]
      >> fs[panSemTheory.set_var_def, Abbr `tlocs`]
      >> fs[Abbr `upd_ctxt`]
      >> irule locals_rel_extend_new_var
      >> fs[Abbr `rts`]
      >> rpt strip_tac 
      >> imp_res_tac mem_genlist_add_suc_val
      >> fs[]
    )
    >> disch_tac >> gvs[] 
    >> rpt conj_tac
    >- fs[state_rel_def]
    >- (fs[code_rel_def, Abbr `upd_ctxt`] >> metis_tac[])
    >- fs[excp_rel_def, Abbr `upd_ctxt`]
    >> Cases_on `res` >> TRY (Cases_on `x`) >> fs[]
    >>~- ([`locals_rel _ (res_var _ _) (FOLDL res_var _ _)`],
      fs[locals_rel_def, Abbr `upd_ctxt`]
      >> rpt strip_tac
      >> fs[FLOOKUP_pan_res_var_thm]
      >> reverse $ Cases_on `vname = rt` >> gvs[]
      >- (
        res_tac >> gs[slc_def, tlc_def, FLOOKUP_UPDATE]
        >> qpat_assum `OPT_MMAP _ _ = SOME (flatten _)` $ PURE_REWRITE_TAC o single o GSYM
        >> irule OPT_MMAP_CONG
        >> rpt strip_tac >> fs[]
        >> irule flookup_res_var_distinct_zip_eq >> fs[LENGTH_MAP]
        >> strip_tac
        >> fs[Abbr `rts`]
        >> imp_res_tac mem_genlist_add_suc_val
        >> fs[ctxt_max_def] >> res_tac >> fs[]
      )
      >> res_tac >> fs[] 
      >> qpat_assum `OPT_MMAP _ _ = SOME (flatten _)` $ PURE_REWRITE_TAC o single o GSYM
      >> irule OPT_MMAP_CONG >> fs[] 
      >> rpt strip_tac
      >> DEP_REWRITE_TAC [flookup_res_var_distinct_zip_eq]
      >> conj_tac
      >- (
        fs[Abbr `rts`, LENGTH_MAP]
        >> strip_tac >> imp_res_tac mem_genlist_add_suc_val
        >> fs[ctxt_max_def] >> res_tac >> fs[]
      )
      >> qpat_x_assum `evaluate (nested_decs _ _ _, _) = _` assume_tac
      >> drule unassigned_free_vars_evaluate_same >> fs[]
      >> disch_then $ qspec_then `x` mp_tac >> impl_tac
      >- (
        DEP_REWRITE_TAC [assigned_free_vars_nested_decs_append] 
        >> conj_tac >- fs[Abbr `rts`, LENGTH_GENLIST, LENGTH_REPLICATE]
        >> fs[MEM_FILTER]
        >> disj2_tac
        >> fs[assigned_free_vars_def]
        >> conj_tac
        >- (
          strip_tac 
          >> fs[Abbr `rts`, ctxt_max_def]
          >> imp_res_tac mem_genlist_add_suc_val >> res_tac >> gvs[]
        )
        >> irule not_mem_context_assigned_mem_gt 
        >> rpt conj_tac
        >- (
          rpt strip_tac >> fs[FLOOKUP_UPDATE]
          >> Cases_on `rt = v''` >> gvs[]
          >- (
            fs[Abbr `ns''`, ctxt_max_def]
            >> imp_res_tac mem_genlist_add_suc_val >> res_tac >> fs[]
          )
          >> fs[no_overlap_def] >> res_tac >> gvs[GSYM distinct_lists_eq_disjoint, distinct_lists_def, EVERY_MEM]
          >> metis_tac[]
        )
        >- (
          fs[ctxt_max_def] >> res_tac >> fs[] 
        )
        >> fs[]
      )
      >> DEP_REWRITE_TAC [flookup_res_var_distinct_zip_eq] >> fs[LENGTH_MAP]
      >> strip_tac >> fs[Abbr `rts`, ctxt_max_def] >> res_tac
      >> imp_res_tac mem_genlist_add_suc_val >> fs[]
    ) 
    >> fs[Abbr `upd_ctxt`]
    >> TOP_CASE_TAC >> fs[]
    >> strip_tac >> fs[globals_lookup_def]
  )
  (* Exception *)
  >- (
    qmatch_asmsub_abbrev_tac `FLOOKUP _.eids ev`
    >> Cases_on `FLOOKUP nctxt.eids ev` >> fs[]
    >> disch_tac >> gvs[state_rel_def, panSemTheory.empty_locals_def, code_rel_def, excp_rel_def, ctxt_fc_def, empty_locals_def, Abbr `nctxt`, CaseEq "option", CaseEq "result", CaseEq "prod", CaseEq "bool"]
    >> conj_tac >- metis_tac[]
    >> fs[globals_lookup_def]
  )
  (* FinalFFI *)
  >> disch_tac >> gvs[state_rel_def, panSemTheory.empty_locals_def, code_rel_def, excp_rel_def, ctxt_fc_def, empty_locals_def, Abbr `nctxt`, CaseEq "option", CaseEq "result", CaseEq "prod", CaseEq "bool"]
  >> metis_tac[]
QED

Theorem MAX_LIST_APPEND:
  MAX_LIST(a ++ b) = MAX (MAX_LIST a) (MAX_LIST b)
Proof
  Induct_on ‘a’ \\ rw[MAX_LIST_def] \\
  intLib.COOPER_TAC
QED

Theorem MAX_LIST_NOT_MEM:
  x > MAX_LIST l ⇒ ¬MEM x l
Proof
  Induct_on ‘l’ \\ gvs[MAX_LIST_def,MAX_DEF]
QED

Resume pc_compile_correct[ExtCall]:
  rpt gen_tac >> rpt strip_tac >>
  fs [panSemTheory.evaluate_def,localised_prog_def] >>
  fs[CaseEq"bool"]>>
  fs [compile_def] >>
  fs [CaseEq "option", CaseEq "v", CaseEq "word_lab", CaseEq "prod"] >>
  rveq >> fs [] >>
  ntac 4 (pairarg_tac \\ fs[]) \\
  imp_res_tac compile_exp_val_rel \\
  gvs[shape_of_def,panLangTheory.size_of_shape_def,
      quantHeuristicsTheory.LIST_LENGTH_1,flatten_def] \\
  ntac 4 $ qpat_x_assum ‘SOME _ = eval _ _’ (mp_tac o GSYM) \\ rpt strip_tac \\
  simp[Once evaluate_def] \\
  qmatch_goalsub_abbrev_tac ‘Dec (freshv + 2)’ \\
  rename1 ‘var_cexp e1 ++ var_cexp e2 ++ var_cexp e3 ++ var_cexp e4’ \\
  ‘¬MEM (freshv + 1) (var_cexp e2)’
    by(simp[Abbr ‘freshv’,FOLDR_MAX_0_MAX_LIST,MAX_LIST_APPEND] \\
       rw[MAX_DEF] \\
       match_mp_tac MAX_LIST_NOT_MEM \\
       intLib.COOPER_TAC) \\
  simp[Once evaluate_def] \\
  simp[update_locals_not_vars_eval_eq'] \\
  ‘¬MEM (freshv + 1) (var_cexp e3)’
    by(simp[Abbr ‘freshv’,FOLDR_MAX_0_MAX_LIST,MAX_LIST_APPEND] \\
       rw[MAX_DEF] \\
       match_mp_tac MAX_LIST_NOT_MEM \\
       intLib.COOPER_TAC) \\
  ‘¬MEM (freshv + 2) (var_cexp e3)’
    by(simp[Abbr ‘freshv’,FOLDR_MAX_0_MAX_LIST,MAX_LIST_APPEND] \\
       rw[MAX_DEF] \\
       match_mp_tac MAX_LIST_NOT_MEM \\
       intLib.COOPER_TAC) \\
  simp[Once evaluate_def] \\
  simp[update_locals_not_vars_eval_eq',update_locals_not_vars_eval_eq''] \\
  ‘¬MEM (freshv + 1) (var_cexp e4)’
    by(simp[Abbr ‘freshv’,FOLDR_MAX_0_MAX_LIST,MAX_LIST_APPEND] \\
       rw[MAX_DEF] \\
       match_mp_tac MAX_LIST_NOT_MEM \\
       intLib.COOPER_TAC) \\
  ‘¬MEM (freshv + 2) (var_cexp e4)’
    by(simp[Abbr ‘freshv’,FOLDR_MAX_0_MAX_LIST,MAX_LIST_APPEND] \\
       rw[MAX_DEF] \\
       match_mp_tac MAX_LIST_NOT_MEM \\
       intLib.COOPER_TAC) \\
  ‘¬MEM (freshv + 3) (var_cexp e4)’
    by(simp[Abbr ‘freshv’,FOLDR_MAX_0_MAX_LIST,MAX_LIST_APPEND] \\
       rw[MAX_DEF] \\
       match_mp_tac MAX_LIST_NOT_MEM \\
       intLib.COOPER_TAC) \\
  simp[Once evaluate_def] \\
  simp[update_locals_not_vars_eval_eq',update_locals_not_vars_eval_eq''] \\
  simp[evaluate_def,FLOOKUP_UPDATE] \\
  ‘t.memory = s.memory ∧ t.memaddrs = s.memaddrs ∧
   t.sh_memaddrs = s.sh_memaddrs ∧ t.be = s.be ∧ t.ffi = s.ffi’ by gvs[state_rel_def] \\
  simp[] \\
  gvs[AllCaseEqs()] \\
  gvs[state_rel_def] \\
  gvs[locals_rel_def,panSemTheory.empty_locals_def] \\
  rw[] \\
  res_tac \\ gvs[] \\
  gvs[opt_mmap_eq_some] \\
  irule EQ_TRANS \\
  first_assum (irule_at Any) \\
  irule MAP_CONG \\
  rw[flookup_res_var_thm] \\
  gvs[FLOOKUP_UPDATE]
QED


Finalise pc_compile_correct;

Theorem first_compile_prog_all_distinct:
  ALL_DISTINCT (MAP FST (functions prog)) ==>
  ALL_DISTINCT (MAP FST (pan_to_crep$compile_prog prog))
Proof
  fs [pan_to_crepTheory.compile_prog_def,MAP_MAP_o,ELIM_UNCURRY,o_DEF,ETA_AX,
      pan_to_crepTheory.compile_to_crep_def,
      crep_inlineTheory.compile_inl_top_def,
      crep_inlineTheory.compile_inl_prog_def]
QED

Theorem first_compile_to_crep_all_distinct:
  ALL_DISTINCT (MAP FST (functions prog)) ==>
  ALL_DISTINCT (MAP FST (pan_to_crep$compile_to_crep prog))
Proof
  fs [pan_to_crepTheory.compile_prog_def,MAP_MAP_o,ELIM_UNCURRY,o_DEF,ETA_AX,
      pan_to_crepTheory.compile_to_crep_def,
      crep_inlineTheory.compile_inl_prog_def]
QED

Theorem alookup_compile_prog_code:
  ALL_DISTINCT (MAP FST (functions pan_code)) ∧
  ALOOKUP (functions pan_code) start = SOME ([],prog,rshape) ==>
  ALOOKUP (compile_to_crep pan_code) start =
  SOME ([],
        comp_func (make_funcs(functions pan_code))
                  (get_eids(functions pan_code)) [] prog)
Proof
  rw[compile_to_crep_def, ctxt_fc_def,ELIM_UNCURRY,
     SIMP_RULE std_ss [ELIM_UNCURRY] ALOOKUP_MAP, crep_vars_def,
     panLangTheory.size_of_shape_def]
QED


Theorem el_compile_prog_el_prog_eq:
  !prog n start cprog p rshape.
   EL n (compile_to_crep prog) = (start,[],cprog) /\
   ALL_DISTINCT (MAP FST (functions prog)) /\ n < LENGTH(functions prog) /\
   ALOOKUP (functions prog) start = SOME ([],p,rshape) ==>
     EL n (functions prog) = (start,[],p,rshape)
Proof
  rw[] >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  gvs[compile_to_crep_def,EL_MAP,UNCURRY_eq_pair,
      MEM_EL,EL_ALL_DISTINCT_EL_EQ,EL_MAP,SF DNF_ss] >>
  metis_tac[FST,SND,PAIR]
QED

Theorem mk_ctxt_code_imp_code_rel:
  ∀pan_code. ALL_DISTINCT (MAP FST (functions pan_code)) ∧
   EVERY (localised_prog o FST o SND o SND) (functions pan_code)
  ⇒
  code_rel (mk_ctxt FEMPTY (make_funcs (functions pan_code)) 0 (get_eids (functions pan_code)))
           (alist_to_fmap (functions pan_code))
           (alist_to_fmap (pan_to_crep$compile_to_crep pan_code))
Proof
  rw [code_rel_def, mk_ctxt_def] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[make_funcs_def,MAP3_MAP2,MAP2_MAP,ZIP_MAP_MAP,MAP_MAP_o,o_DEF,
      SIMP_RULE std_ss [ELIM_UNCURRY] ALOOKUP_MAP,ELIM_UNCURRY,
      compile_to_crep_def,crep_vars_def,EVERY_MEM,comp_func_def,
      mk_ctxt_def,ctxt_fc_def,make_vmap_def,MAX_LIST_i_genlist,EVERY_MEM] >>
  res_tac >> fs[]
QED

Theorem mod_eq_lt_eq:
  !n x m.
   (n:num) < x /\ m < x /\ n MOD x = m MOD x ==>
    n = m
Proof
  rw [] >>
  rfs [arithmeticTheory.LESS_MOD]
QED

Theorem pair_map_I[local]:
  (λ(x,y). (x,y)) = I
Proof
  rw[FUN_EQ_THM,ELIM_UNCURRY]
QED

(* TODO: move *)
Theorem size_of_eids_eq:
  size_of_eids pc = LENGTH(nub (FLAT (MAP (exp_ids ∘ FST o SND ∘ SND) (functions pc))))
Proof
  rw[panLangTheory.size_of_eids_def] >>
  Induct_on ‘pc’ using panLangTheory.functions_ind >>
  rw[panLangTheory.functions_def] >>
  rw[nub_append] >>
  ntac 2 AP_TERM_TAC >>
  rw[FILTER_EQ,EQ_IMP_THM,MEM_FLAT,MEM_MAP,functions_eq_FILTER,PULL_EXISTS,MEM_FILTER] >>
  PURE_FULL_CASE_TAC >> gvs[panLangTheory.is_function_def] >>
  first_assum $ irule_at $ Pat ‘MEM _ _’ >>
  gvs[panLangTheory.is_function_def]
QED

Theorem get_eids_imp_excp_rel:
  !seids (pc:'a decl list).
   panLang$size_of_eids pc < dimword (:'a) /\
   FDOM seids =  FDOM (get_eids(functions pc)) ==>
     excp_rel (get_eids(functions pc)) seids
Proof
  rw[excp_rel_def, get_eids_def] >>
  gvs[MAP2_MAP,pair_map_I] >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[MEM_ZIP,size_of_eids_eq]
QED

Theorem mk_ctxt_imp_locals_rel:
  !pc lcl.
    locals_rel (mk_ctxt FEMPTY (make_funcs pc) 0 (get_eids pc)) FEMPTY lcl
Proof
  rw[locals_rel_def,no_overlap_def,mk_ctxt_def,ctxt_max_def]
QED

Theorem compile_prog_distinct_params:
    EVERY (λ(name,params,body). ALL_DISTINCT params) (compile_prog prog)
Proof
  rw[EVERY_MEM] >>
  gvs[compile_prog_def,MEM_MAP,UNCURRY_eq_pair,crep_vars_def,ALL_DISTINCT_GENLIST,
      crep_inlineTheory.compile_inl_prog_def,
      crep_inlineTheory.compile_inl_top_def,
      pan_to_crepTheory.compile_to_crep_def]
QED

Theorem state_rel_imp_semantics_to_crep:
  !(s:('a,'b) panSem$state) (t:('a,'b) crepSem$state) pan_code start.
    state_rel s t ∧
    ALL_DISTINCT (MAP FST (functions pan_code)) ∧
    s.code = alist_to_fmap(functions pan_code) ∧
    t.code = alist_to_fmap (pan_to_crep$compile_to_crep pan_code) ∧
    s.locals = FEMPTY ∧
    EVERY (localised_prog ∘ FST o SND ∘ SND) (functions pan_code) ∧
    panLang$size_of_eids pan_code < dimword (:'a) /\
    FDOM s.eshapes =  FDOM (get_eids(functions pan_code)) ∧
    semantics s start <> Fail ==>
      semantics t start = semantics s start
Proof
  rw [] >>
  drule mk_ctxt_code_imp_code_rel >>
  fs[] >> strip_tac >>
  ‘excp_rel (get_eids(functions pan_code)) s.eshapes’ by (
    match_mp_tac get_eids_imp_excp_rel >> fs []) >>
  ‘locals_rel (mk_ctxt FEMPTY (make_funcs(functions pan_code)) 0
               (get_eids(functions pan_code))) FEMPTY t.locals’ by (
    fs [locals_rel_def] >>
    conj_tac
    >- rw [no_overlap_def, mk_ctxt_def] >>
    fs [ctxt_max_def, mk_ctxt_def]) >>
  qmatch_asmsub_abbrev_tac ‘code_rel nctxt _ _’ >>
  reverse (Cases_on ‘semantics s start’) >> fs []
  >- (
   (* Termination case of pan semantics *)
   fs [panSemTheory.semantics_def] >>
   pop_assum mp_tac >>
   IF_CASES_TAC >> fs [] >>
   DEEP_INTRO_TAC some_intro >> simp[] >>
   rw [] >>
   rw [crepSemTheory.semantics_def]
   >- (
    (* the fail case of crep semantics *)
    qhdtm_x_assum ‘panSem$evaluate’ kall_tac >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >>
    last_x_assum(qspec_then ‘k'’ mp_tac) >> simp[] >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    CCONTR_TAC >> fs [] >>
    drule pc_compile_correct >> fs [] >>
    map_every qexists_tac [‘t with clock := k'’, ‘nctxt’] >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
    conj_tac
    >- (
      fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def] >>
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs [localised_prog_def]) >>
    CCONTR_TAC >>
    fs [] >>
    fs [compile_def] >>
    fs [compile_exp_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 1’ >> fs []) >>
   (* the termination/diverging case of crep semantics *)
   DEEP_INTRO_TAC some_intro >> simp[] >>
   conj_tac
   (* the termination case of crep semantics *)
   >- (
    rw [] >> fs [] >>
    drule pc_compile_correct >> fs [] >>
    ‘r ≠ SOME Error ∧
     r ≠ SOME Break ∧ r ≠ SOME Continue ∧ r ≠ NONE’ by (
      cases_on ‘r’ >> fs [] >>
      cases_on ‘x’ >> fs []) >>
    fs [] >>
    disch_then (qspecl_then [‘t with clock := k’, ‘nctxt’] mp_tac) >>
    impl_tac
    >- fs [Abbr ‘nctxt’, mk_ctxt_def, state_rel_def,localised_prog_def] >>
    strip_tac >> fs [] >>
    fs [compile_def] >>
    fs [compile_exp_def] >>
    dxrule crepPropsTheory.evaluate_add_clock_eq >>
    dxrule crepPropsTheory.evaluate_add_clock_eq >>
    disch_then (qspec_then ‘k’ assume_tac) >>
    disch_then (qspec_then ‘k'’ assume_tac) >>
    fs [] >>
    Cases_on ‘r’ >> fs[] >>
    Cases_on ‘r'’ >> fs [] >>
    Cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
    Cases_on ‘x'’ >> fs [] >> rveq >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >> rveq >> fs [] >>
    cases_on ‘size_of_shape (shape_of v) = 1’ >> fs [] >> rveq >> fs [] >>
    fs [state_rel_def] >>
    fs [crepSemTheory.state_accfupds, crepSemTheory.state_component_equality]) >>
   (* the diverging case of crep semantics *)
   rw[] >> fs[] >> CCONTR_TAC >> fs [] >>
   drule pc_compile_correct >> fs [] >>
   ‘r ≠ SOME Error ∧
    r ≠ SOME Break ∧ r ≠ SOME Continue ∧ r ≠ NONE’ by (
     cases_on ‘r’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
   fs [] >>
   map_every qexists_tac [‘t with clock := k’, ‘nctxt’] >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def, localised_prog_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >> fs [] >>
   fs [compile_def] >>
   fs [compile_exp_def] >>
   first_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   first_x_assum(qspec_then ‘k’ mp_tac) >> simp[] >>
   every_case_tac >> fs[] >> rw[] >> rfs[]) >>
  (* the diverging case of pan semantics *)
  fs [panSemTheory.semantics_def] >>
  pop_assum mp_tac >>
  IF_CASES_TAC >> fs [] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  rw [] >>
  rw [crepSemTheory.semantics_def]
  >- (
   (* the fail case of crep semantics *)
   fs[] >> rveq >> fs[] >>
   last_x_assum (qspec_then ‘k’ mp_tac) >> simp[] >>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   CCONTR_TAC >> fs [] >>
   drule pc_compile_correct >> fs [] >>
   map_every qexists_tac [‘t with clock := k’, ‘nctxt’] >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def, localised_prog_def] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >>
   fs [] >>
   fs [compile_def] >>
   fs [compile_exp_def] >>
   cases_on ‘q’ >> fs [] >>
   cases_on ‘x’ >> fs [] >>
   cases_on ‘size_of_shape (shape_of v) = 0’ >> fs [] >> rveq >> fs [] >>
   cases_on ‘size_of_shape (shape_of v) = 1’ >> fs [] >> rveq >> fs []) >>
  (* the termination/diverging case of crep semantics *)
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
  (* the termination case of crep semantics *)
  >- (
   rw [] >>  fs[] >>
   qpat_x_assum ‘∀x y. _’ (qspec_then ‘k’ mp_tac)>>
   (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
   strip_tac >>
   drule pc_compile_correct >> fs [] >>
   map_every qexists_tac [‘t with clock := k’, ‘nctxt’] >>
   fs [] >>
   Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
   conj_tac
   >- (
    fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def,localised_prog_def] >>
    last_x_assum (qspec_then ‘k’ assume_tac) >>
    rfs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
   CCONTR_TAC >>
   fs [] >>
   fs [compile_def] >>
   fs [compile_exp_def] >>
   cases_on ‘q’ >> fs [] >> rveq >>  fs [] >>
   cases_on ‘x’ >> fs [] >>
   every_case_tac >> fs []) >>
  (* the diverging case of crep semantics *)
  rw [] >>
  qmatch_abbrev_tac ‘build_lprefix_lub l1 = build_lprefix_lub l2’ >>
  ‘(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2’
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac
  >- (
   UNABBREV_ALL_TAC >>
   conj_tac >>
   Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
   REWRITE_TAC[IMAGE_COMPOSE] >>
   match_mp_tac prefix_chain_lprefix_chain >>
   simp[prefix_chain_def,PULL_EXISTS] >>
   qx_genl_tac [‘k1’, ‘k2’] >>
   qspecl_then [‘k1’, ‘k2’] mp_tac LESS_EQ_CASES >>
   simp[LESS_EQ_EXISTS] >>
   rw [] >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               panPropsTheory.evaluate_add_clock_io_events_mono) >>
   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               crepPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_assum (qspecl_then
                [‘Call NONE start []’, ‘t with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE start []’, ‘t with clock := k2’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE start []’, ‘s with clock := k1’, ‘p’] mp_tac) >>
   first_assum (qspecl_then
                [‘Call NONE start []’, ‘s with clock := k2’, ‘p’] mp_tac) >>
   fs []) >>
  simp [equiv_lprefix_chain_thm] >>
  fs [Abbr ‘l1’, Abbr ‘l2’]  >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac
  >- (
   qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
   Cases_on`p` >> pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
   drule pc_compile_correct >> fs [] >>
   ‘q ≠ SOME Error ∧
    q ≠ SOME Break ∧ q ≠ SOME Continue ∧ q ≠ NONE’ by (
     last_x_assum (qspec_then ‘k’ assume_tac) >> rfs [] >>
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs []) >>
   fs [] >>
   disch_then (qspecl_then [‘t with clock := k’, ‘nctxt’] mp_tac) >>
   impl_tac
   >- fs [Abbr ‘nctxt’, mk_ctxt_def, state_rel_def, localised_prog_def] >>
   strip_tac >> fs [] >>
   qexists_tac ‘ck+k’ >> simp[] >>
   fs [compile_def, compile_def] >>
   fs [compile_exp_def] >>
   first_x_assum (qspec_then ‘k’ kall_tac) >>
   first_x_assum (qspec_then ‘k’ mp_tac) >>
   fs [] >>
   strip_tac >>
   cases_on ‘q’ >> fs [] >> rveq >> fs [] >>
   cases_on ‘x’ >> fs [] >> rveq >> fs [] >>

   assume_tac (INST_TYPE [``:'a``|->``:'a``,
                          ``:'b``|->``:'b``]
               crepPropsTheory.evaluate_add_clock_io_events_mono) >>
   first_x_assum (qspecl_then
                  [‘Call NONE start []’,
                   ‘t with clock := k’, ‘ck’] mp_tac) >>
   strip_tac >> rfs [] >>
   fs [state_rel_def, IS_PREFIX_THM]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst[{redex = #1(dest_exists(#2 g)), residue = ``k:num``}]
                                        (assert(has_pair_type)tm))`) (#2 g) g) >>
  drule pc_compile_correct >> fs [] >>
  ‘q ≠ SOME Error ∧
   q ≠ SOME Break ∧ q ≠ SOME Continue ∧ q ≠ NONE’ by (
    last_x_assum (qspec_then ‘k’ assume_tac) >> rfs [] >>
    cases_on ‘q’ >> fs [] >>
    cases_on ‘x’ >> fs []) >>
  fs [] >>
  disch_then (qspecl_then [‘t with clock := k’, ‘nctxt’] mp_tac) >>
  impl_tac
  >- fs [Abbr ‘nctxt’, mk_ctxt_def, state_rel_def, localised_prog_def] >>
  strip_tac >> fs [] >>
  fs [compile_def] >>
  fs [compile_exp_def] >>
  assume_tac (INST_TYPE [``:'a``|->``:'a``,
                         ``:'b``|->``:'b``]
              crepPropsTheory.evaluate_add_clock_io_events_mono) >>
  first_x_assum (qspecl_then
                 [‘Call NONE (Label start) []’,
                  ‘t with clock := k’, ‘ck’] mp_tac) >>
  strip_tac >> rfs [] >>
  qexists_tac ‘k’ >>
  cases_on ‘q’ >> fs [] >>
  cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
   fs [state_rel_def, IS_PREFIX_THM]
QED

Theorem state_rel_imp_semantics_decls_to_crep:
  !(s:('a,'b) panSem$state) (t:('a,'b) crepSem$state) pan_code start.
    state_rel (s with structs := []) t ∧
    ALL_DISTINCT (MAP FST (functions pan_code)) ∧
    s.code = FEMPTY ∧
    t.code = alist_to_fmap (pan_to_crep$compile_to_crep pan_code) ∧
    s.locals = FEMPTY ∧
    EVERY (localised_prog ∘ FST o SND ∘ SND) (functions pan_code) ∧
    EVERY is_function pan_code ∧
    panLang$size_of_eids pan_code < dimword (:'a) /\
    FDOM s.eshapes = FDOM (get_eids(functions pan_code)) ∧
    semantics_decls s start pan_code <> Fail ==>
      semantics t start = semantics_decls s start pan_code
Proof
  rw [semantics_decls_def] >>
  gvs[AllCaseEqs(), GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS] >>
  gvs [] >>
  drule_all_then (gvs o single) evaluate_decls_only_functions >>
  gs [decs_stcnames_only_functions2] >>
  irule EQ_SYM >>
  irule state_rel_imp_semantics_to_crep >>
  simp[PULL_EXISTS] >>
  first_assum $ irule_at $ Pos hd >>
  simp[] >>
  conj_tac
  >- (rw[fmap_eq_flookup,FLOOKUP_FUPDATE_LIST,alookup_distinct_reverse] >>
      TOP_CASE_TAC >> simp[]) >>
  gvs[state_rel_def]
QED

Theorem state_rel_imp_semantics:
  !(s:('a,'b) panSem$state) (t:('a,'b) crepSem$state) pan_code start.
    state_rel s t ∧
    ALL_DISTINCT (MAP FST (functions pan_code)) ∧
    s.code = alist_to_fmap(functions pan_code) ∧
    t.code = alist_to_fmap (pan_to_crep$compile_prog pan_code) ∧
    s.locals = FEMPTY ∧
    EVERY (localised_prog ∘ SND ∘ SND) (functions pan_code) ∧
    panLang$size_of_eids pan_code < dimword (:'a) /\
    FDOM s.eshapes =  FDOM (get_eids(functions pan_code)) ∧
    semantics s start <> Fail ==>
      semantics t start = semantics s start
Proof
  rw[pan_to_crepTheory.compile_prog_def] >>
  qabbrev_tac `inl_funcs = MAP FST (functions (FILTER inlinable pan_code))` >>
  qabbrev_tac `crep_code = compile_to_crep pan_code` >>
  drule_at (Pos $ el 3) state_rel_imp_semantics_to_crep >>
  disch_then $ drule_at (Pos last) >> fs[] >>
  disch_then $ qspec_then `t with code := alist_to_fmap crep_code` mp_tac >> impl_tac
  >- fs[state_rel_def] >>
  disch_tac >>
  qabbrev_tac `t_uninline = t with code := alist_to_fmap crep_code` >>
  `semantics t_uninline start ≠ Fail` by fs[] >>
  drule_at (Pos last) crep_inlineProofTheory.state_rel_imp_semantics >>
  Cases_on `FLOOKUP t_uninline.code start` >> fs[]
  >- fs[semantics_def, evaluate_def, lookup_code_def] >>
  PairCases_on `x` >> fs[] >>
  disch_then $ qspecl_then [`t`, `crep_code`, `inl_funcs`] mp_tac >> impl_tac
  >- (
    fs[crep_inlineProofTheory.state_rel_code_def, state_rel_def,
       crep_inlineProofTheory.locals_strong_rel_def, Abbr `t_uninline`] >>
    imp_res_tac first_compile_to_crep_all_distinct >>
    fs[Abbr `crep_code`]
  ) >>
  rpt strip_tac >> fs[]
QED

Theorem state_rel_imp_semantics_decls:
  !(s:('a,'b) panSem$state) (t:('a,'b) crepSem$state) pan_code start.
    state_rel (s with structs := []) t ∧
    ALL_DISTINCT (MAP FST (functions pan_code)) ∧
    s.code = FEMPTY ∧
    t.code = alist_to_fmap (pan_to_crep$compile_prog pan_code) ∧
    s.locals = FEMPTY ∧
    EVERY (localised_prog ∘ SND ∘ SND) (functions pan_code) ∧
    EVERY is_function pan_code ∧
    panLang$size_of_eids pan_code < dimword (:'a) /\
    FDOM s.eshapes =  FDOM (get_eids(functions pan_code)) ∧
    semantics_decls s start pan_code <> Fail ==>
      semantics t start = semantics_decls s start pan_code
Proof
  rw [semantics_decls_def] >>
  gvs[AllCaseEqs(), GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS] >>
  gvs [] >>
  drule_all_then (gvs o single) evaluate_decls_only_functions >>
  gs [decs_stcnames_only_functions2] >>
  irule EQ_SYM >>
  irule state_rel_imp_semantics >>
  simp[PULL_EXISTS] >>
  first_assum $ irule_at $ Pos hd >>
  simp[] >>
  conj_tac
  >- (rw[fmap_eq_flookup,FLOOKUP_FUPDATE_LIST,alookup_distinct_reverse] >>
      TOP_CASE_TAC >> simp[]) >>
  gvs[state_rel_def]
QED
