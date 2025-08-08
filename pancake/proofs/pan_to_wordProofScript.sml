(*
  Correctness proof for combined pan_to_word compilation.
*)

open preamble pan_to_wordTheory
     pan_simpProofTheory pan_to_crepProofTheory
     crep_to_loopProofTheory loop_to_wordProofTheory
     pan_globalsProofTheory

val _ = new_theory "pan_to_wordProof";


Definition crep_state_def:
  crep_state (s:('a,'b) panSem$state) pan_code mem =
  <| locals   := FEMPTY;
     globals  := FEMPTY;
     code     := alist_to_fmap (pan_to_crep$compile_prog pan_code);
     memory   := mem;
     memaddrs := s.memaddrs;
     sh_memaddrs := s.sh_memaddrs;
     clock    := s.clock;
     be       := s.be;
     ffi      := s.ffi;
     top_addr := s.top_addr;
     base_addr := s.base_addr|>
End

Definition wloc_wlab_def:
  wloc_wlab (wordLang$Word w) = panSem$Word w
End

Theorem wloc_wlab_wlab_wloc[simp]:
  wloc_wlab(wlab_wloc w) = w
Proof
  Cases_on ‘w’ >> rw[wlab_wloc_def,wloc_wlab_def]
QED

Definition no_labels_def:
  no_labels mem dom = (∀a. a ∈ dom ⇒ ∃w. mem a = wordLang$Word w)
End

Definition loop_state_def:
  loop_state (s:('a,'ffi) crepSem$state) c crep_code ck mem =
  <| locals   := LN;
     globals  := FEMPTY;
     memory   := mem;
     mdomain := s.memaddrs;
     sh_mdomain := s.sh_memaddrs;
     code     := fromAList (crep_to_loop$compile_prog c crep_code);
     clock    := ck;
     be       := s.be;
     ffi      := s.ffi;
     top_addr := s.top_addr;
     base_addr := s.base_addr|>
End

Definition distinct_params_def:
  distinct_params prog <=>
  EVERY (λ(name,params,body). ALL_DISTINCT params) prog
End


Theorem first_compile_prog_all_distinct:
  !prog. ALL_DISTINCT (MAP FST(functions prog)) ==>
   ALL_DISTINCT (MAP FST (pan_to_word$compile_prog c prog))
Proof
  rw [] >>
  fs [pan_to_wordTheory.compile_prog_def] >>
  match_mp_tac loop_to_wordProofTheory.first_compile_all_distinct >>
  irule crep_to_loopProofTheory.first_compile_prog_all_distinct
QED


Theorem FDOM_get_eids_pan_simp_compile_eq:
  !prog. FDOM (get_eids(functions prog)) =
  FDOM (get_eids (functions(pan_simp$compile_prog prog)))
Proof
  rw [] >>
  fs [pan_to_crepTheory.get_eids_def] >>
  rpt(AP_THM_TAC ORELSE AP_TERM_TAC) >>
  qmatch_goalsub_abbrev_tac ‘MAP2 _ l1 _ = MAP2 _ l2 _’ >>
  ‘l1 = l2’ suffices_by simp[] >>
  fs [Abbr ‘l1’, Abbr ‘l2’, pan_simpTheory.compile_prog_def,MAP_MAP_o] >>
  fs [MAP_MAP_o] >>
  ntac 2 AP_TERM_TAC >>
  rw[panPropsTheory.functions_eq_FILTER,MAP_MAP_o,FILTER_MAP] >>
  qmatch_goalsub_abbrev_tac ‘is_function o ff’ >>
  ‘is_function o ff = is_function’
    by(rw[FUN_EQ_THM,Abbr ‘ff’] >> PURE_TOP_CASE_TAC >>
       rw[panLangTheory.is_function_def]) >>
  simp[Abbr ‘ff’] >>
  rw[MAP_EQ_f] >>
  PURE_TOP_CASE_TAC >> rw[exp_ids_compile_eq]
QED

Theorem map_map2_fst_lemma:
  ∀xs ys.
    MAP FST (MAP2 (λx y. (x,y)) xs ys) = TAKE (MIN (LENGTH xs) (LENGTH ys)) xs
Proof
  Induct >>
  rw[] >>
  Cases_on ‘ys’ >>
  rw[MIN_DEF]
QED

Theorem exp_ids_nested_seq:
  ∀ps. exp_ids(nested_seq ps) = FLAT (MAP exp_ids ps)
Proof
  Induct >>
  rw[panLangTheory.nested_seq_def, panLangTheory.exp_ids_def]
QED

Theorem exp_ids_compile_globals:
  ∀ctxt p.
    exp_ids (compile ctxt p) = exp_ids p
Proof
  recInduct pan_globalsTheory.compile_ind >>
  rw[pan_globalsTheory.compile_def,ELIM_UNCURRY,panLangTheory.exp_ids_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[panLangTheory.exp_ids_def])
QED

Theorem exp_ids_fperm:
  ∀f g p.
    exp_ids (fperm f g p) = exp_ids p
Proof
  recInduct pan_globalsTheory.fperm_ind >>
  rw[pan_globalsTheory.fperm_def,ELIM_UNCURRY,panLangTheory.exp_ids_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[panLangTheory.exp_ids_def])
QED

Theorem compile_decs_exp_ids:
  ∀ctxt pan_code.
    MAP (exp_ids ∘ SND ∘ SND) (functions(FST(SND(compile_decs ctxt pan_code)))) =
    MAP (exp_ids ∘ SND ∘ SND) (functions pan_code)
Proof
  recInduct pan_globalsTheory.compile_decs_ind >>
  rw[pan_globalsTheory.compile_decs_def,ELIM_UNCURRY,panLangTheory.exp_ids_def,
     panLangTheory.functions_def,exp_ids_compile_globals
    ]
QED

Theorem fperm_exp_ids:
  ∀f g pan_code.
    MAP (exp_ids ∘ SND ∘ SND) (functions(fperm_decs f g pan_code)) =
    MAP (exp_ids ∘ SND ∘ SND) (functions pan_code)
Proof
  recInduct pan_globalsTheory.fperm_decs_ind >>
  rw[pan_globalsTheory.fperm_decs_def,ELIM_UNCURRY,panLangTheory.exp_ids_def,
     panLangTheory.functions_def,exp_ids_fperm
    ]
QED

Theorem compile_decs_no_exp_ids_main:
  ∀ctxt prog.
    EVERY (λx. exp_ids x = []) (FST (compile_decs ctxt prog))
Proof
  recInduct pan_globalsTheory.compile_decs_ind >>
  rw[pan_globalsTheory.compile_decs_def,ELIM_UNCURRY,panLangTheory.exp_ids_def]
QED

Theorem functions_resort_decls:
  functions(resort_decls xs) = functions xs
Proof
  rw[pan_globalsTheory.resort_decls_def,panPropsTheory.functions_eq_FILTER,FILTER_APPEND,FILTER_FILTER,ETA_THM]
QED

Theorem FDOM_get_eids_pan_globals_compile_eq:
  ∀pan_code main args body.
    ALOOKUP (functions pan_code) main = SOME (args,body) ⇒
    FDOM(get_eids (functions (compile_top pan_code main))) =
    FDOM(get_eids(functions pan_code))
Proof
  rw[pan_globalsTheory.compile_top_def,ELIM_UNCURRY,panLangTheory.functions_def,
     pan_to_crepTheory.get_eids_def,map_map2_fst_lemma,
     panLangTheory.exp_ids_def,
     exp_ids_nested_seq,
     compile_decs_exp_ids,
     fperm_exp_ids,
     functions_resort_decls
    ] >>
  qmatch_goalsub_abbrev_tac ‘a1 ∪ _ = _’ >>
  ‘a1 = {}’ suffices_by simp[] >>
  unabbrev_all_tac >> rw[FLAT_EQ_NIL,EVERY_MAP,compile_decs_no_exp_ids_main]
QED

Definition globals_allocatable_def:
  globals_allocatable (s:('a,'ffi) panSem$state) pan_code ⇔
  DISJOINT s.memaddrs
           (addresses s.top_addr
                      (SUM (MAP size_of_shape (dec_shapes (compile_prog pan_code))))) ∧
  s.top_addr +
        bytes_in_word:'a word *
        n2w (SUM (MAP size_of_shape (dec_shapes pan_code))) ∉
        s.memaddrs ∧
  SUM (MAP size_of_shape (dec_shapes pan_code)) * w2n(bytes_in_word:'a word) < dimword (:α)
End

Theorem dec_shapes_compile_prog:
  ∀pan_code. dec_shapes(pan_simp$compile_prog pan_code) = dec_shapes pan_code
Proof
  Induct using pan_globalsTheory.dec_shapes_ind >>
  gvs[pan_simpTheory.compile_prog_def,pan_globalsTheory.dec_shapes_def]
QED

Theorem function_names_compile_prog:
  ∀pan_code. MAP FST (functions(pan_simp$compile_prog pan_code)) = MAP FST (functions pan_code)
Proof
  Induct using panLangTheory.functions_ind >>
  gvs[pan_simpTheory.compile_prog_def,panLangTheory.functions_def]
QED

Theorem semantics_decls_has_main':
  s.code = FEMPTY ∧
  ALL_DISTINCT(MAP FST(functions code)) ∧
  semantics_decls s start code ≠ Fail ⇒
  ∃body.
    ALOOKUP (functions code) start =
    SOME ([],body)
Proof
  rpt strip_tac >>
  drule panPropsTheory.semantics_decls_has_main' >>
  rw[FLOOKUP_FUPDATE_LIST,AllCaseEqs(),alookup_distinct_reverse]
QED

Theorem compile_decs_fun_names:
  ∀ctxt code.
    MAP FST (functions (FST(SND(compile_decs ctxt code)))) =
    MAP FST (functions code)
Proof
  recInduct pan_globalsTheory.compile_decs_ind >>
  rw[pan_globalsTheory.compile_decs_def,panLangTheory.functions_def,ELIM_UNCURRY]
QED

Theorem size_of_eids_compile_top:
  ALOOKUP (functions pan_code) main = SOME(args,body) ⇒
  size_of_eids (compile_top pan_code main) = size_of_eids pan_code
Proof
  rw[panLangTheory.size_of_eids_def] >>
  ntac 2 AP_TERM_TAC >>
  simp[pan_globalsTheory.compile_top_def,ELIM_UNCURRY,
       panLangTheory.exp_ids_def,exp_ids_nested_seq] >>
  qmatch_goalsub_abbrev_tac ‘a1 ++ _ = _’ >>
  ‘a1 = []’
    by(rw[Abbr ‘a1’,FLAT_EQ_NIL,EVERY_MAP,compile_decs_no_exp_ids_main]) >>
  simp[] >> simp[Abbr ‘a1’] >>
  qmatch_goalsub_abbrev_tac ‘FLAT (MAP f l1) = FLAT (MAP f l2)’ >>
  ‘∀ll. FLAT (MAP f ll) = FLAT (MAP (exp_ids o SND o SND) (functions ll))’
    by(recInduct panLangTheory.functions_ind >>
       rw[panLangTheory.functions_def,Abbr ‘f’]) >>
  pop_assum $ simp o single >>
  simp[Abbr ‘l1’, Abbr ‘l2’,compile_decs_exp_ids,fperm_exp_ids,functions_resort_decls]
QED

Theorem FLOOKUP_make_funcs_main:
  ALOOKUP (functions pan_code) main = SOME([],body) ⇒
  FLOOKUP (make_funcs (compile_prog(compile_top pan_code main))) main =
  SOME (first_name,0)
Proof
  rw[pan_globalsTheory.compile_top_def,ELIM_UNCURRY,
     pan_to_crepTheory.compile_prog_def,crep_to_loopTheory.make_funcs_def,
     panLangTheory.functions_def,GENLIST_CONS,FLOOKUP_UPDATE,
     pan_to_crepTheory.crep_vars_def,
     panLangTheory.size_of_shape_def
    ]
QED


Theorem state_rel_imp_semantics:
  (∀addr. addr ∈ s.memaddrs ⇒ t.memory addr = wlab_wloc(s.memory addr)) ∧
  no_labels t.memory t.mdomain ∧
  start = «main» ∧
  globals_size = SUM (MAP size_of_shape (dec_shapes (compile_prog pan_code))) ∧
  distinct_params(functions pan_code) ∧
  t.mdomain = s.memaddrs ∪ addresses s.top_addr globals_size ∧
  t.sh_mdomain = s.sh_memaddrs ∧
  t.be = s.be ∧
  t.ffi = s.ffi ∧
  ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
  ALOOKUP (fmap_to_alist t.store) HeapLength = SOME(Word heap_len) ∧
  s.top_addr = s.base_addr + 2w*heap_len - bytes_in_word * n2w globals_size ∧
  ALL_DISTINCT (MAP FST (functions pan_code)) ∧
  byte_aligned s.top_addr ∧
  globals_allocatable s pan_code ∧
  s.code = FEMPTY ∧
  t.code = fromAList (pan_to_word$compile_prog c pan_code) ∧
  s.globals = FEMPTY ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM (get_eids(functions pan_code)) ∧
  lookup 0 t.locals = SOME (Loc 1 0) /\ good_dimindex (:'a) ∧
  semantics_decls s start pan_code <> Fail ==>
  semantics (t:('a,'b, 'ffi) wordSem$state) (first_name) =
  semantics_decls (s:('a,'ffi) panSem$state) start pan_code
Proof
  rw [] >>
  drule_at (Pos last) pan_simpProofTheory.state_rel_imp_semantics_decls >>
  disch_then $ qspec_then ‘s’ mp_tac >>
  impl_tac
  >- simp[pan_simpProofTheory.state_rel_def,
          panSemTheory.state_component_equality] >>
  strip_tac >>
  gvs[] >>
  drule_at (Pos last) pan_globalsProofTheory.compile_top_semantics_decls >>
  simp[] >>
  disch_then $ qspecl_then [‘wloc_wlab o t.memory’,‘s.locals’] mp_tac >>
  simp[] >>
  impl_keep_tac
  >- (gvs[globals_allocatable_def,dec_shapes_compile_prog,function_names_compile_prog]) >>
  strip_tac >> gvs[] >>
  drule_at (Pos last) pan_to_crepProofTheory.state_rel_imp_semantics_decls >>
  simp[] >>
  qmatch_goalsub_abbrev_tac ‘state_rel s1’ >>
  disch_then $ qspec_then ‘crep_state s1 (compile_top (compile_prog pan_code) «main») s1.memory’ mp_tac >>
  impl_keep_tac
  >- (simp[compile_top_only_functions,compile_top_localised] >>
      dep_rewrite.DEP_ONCE_REWRITE_TAC [FDOM_get_eids_pan_globals_compile_eq] >>
      conj_asm1_tac
      >- (qexists ‘[]’ >>
          drule_then irule semantics_decls_has_main' >>
          simp[]) >>
      simp[GSYM FDOM_get_eids_pan_simp_compile_eq] >>
      conj_tac
      >- gvs[crep_state_def,pan_to_crepProofTheory.state_rel_def] >>
      conj_tac
      >- (gvs[pan_globalsTheory.compile_top_def,ELIM_UNCURRY,
              panLangTheory.functions_def,new_main_name_correct,
              compile_decs_fun_names,functions_fperm_decs,
              MAP_MAP_o,o_DEF,MEM_MAP,FORALL_PROD,
              functions_resort_decls] >>
          conj_tac
          >- (rw[pan_globalsTheory.fperm_name_def] >>
              metis_tac[SIMP_RULE std_ss [FORALL_PROD,MEM_MAP] new_main_name_correct]) >>
          drule_at_then (Pos last)
                        (qspec_then ‘fperm_name «main» (new_main_name (compile_prog pan_code))’ mp_tac)
                        ALL_DISTINCT_MAP_INJ >>
          simp[MAP_MAP_o,o_DEF]) >>
      simp[crep_state_def] >>
      gvs[size_of_eids_compile_top,size_of_eids_compile_eq]
     ) >>
  disch_then $ strip_assume_tac o GSYM >>
  gvs[Abbr ‘s1’] >>
  drule_at (Pos last) crep_to_loopProofTheory.state_rel_imp_semantics >>
  qmatch_goalsub_abbrev_tac ‘crep_state _ pcode’ >>
  qmatch_goalsub_abbrev_tac ‘crepSem$semantics cst’ >>
  disch_then $ qspecl_then [‘loop_state cst c (pan_to_crep$compile_prog pcode) t.clock t.memory’,
                            ‘pan_to_crep$compile_prog pcode’,
                            ‘first_name’,
                            ‘c’
                           ] mp_tac >>
  impl_keep_tac
  >- (simp[loop_state_def,mem_rel_def] >>
      conj_tac
      >- (rw[Abbr ‘cst’, crep_state_def] >> rw[crep_to_loopProofTheory.globals_rel_def] >>
          gvs[no_labels_def,SF DNF_ss] >>
          res_tac >>
          simp[wloc_wlab_def,wlab_wloc_def]) >>
      conj_tac
      >- (rw[Abbr ‘cst’, crep_state_def] >> rw[crep_to_loopProofTheory.globals_rel_def]) >>
      simp[Abbr ‘cst’,crep_state_def] >>
      conj_asm1_tac
      >- (rw[Abbr ‘pcode’] >>
          irule pan_to_crepProofTheory.first_compile_prog_all_distinct >>
          simp[]) >>
      qunabbrev_tac ‘pcode’ >>
      irule FLOOKUP_make_funcs_main >>
      drule_then irule semantics_decls_has_main' >>
      simp[]) >>
  disch_then $ assume_tac o GSYM >> gvs[] >>
  irule fstate_rel_imp_semantics >>
  unabbrev_all_tac >>
  simp[crep_state_def] >>
  ‘∃prog. ALOOKUP (functions (compile_prog pan_code)) «main» = SOME([],prog)’
    by(drule_then irule semantics_decls_has_main' >>
       simp[]) >>
  conj_asm1_tac
  >- (simp[lookup_fromAList] >>
      irule_at Any ALOOKUP_ALL_DISTINCT_MEM >>
      irule_at Any crep_to_loopProofTheory.first_compile_prog_all_distinct >>
      simp [pan_to_crepTheory.compile_prog_def, pan_globalsTheory.compile_top_def,
            ELIM_UNCURRY,panLangTheory.functions_def,
            pan_to_crepTheory.crep_vars_def, panLangTheory.size_of_shape_def,
            crep_to_loopTheory.compile_prog_def,
            crep_to_loopTheory.make_funcs_def,
            pan_to_crepTheory.make_funcs_def,FLOOKUP_UPDATE,
            GENLIST_CONS
           ] >>
      metis_tac[]) >>
  conj_asm1_tac
  >- simp[loop_state_def] >>
  irule_at (Pos hd) EQ_REFL >>
  simp[st_rel_def,pan_to_wordTheory.compile_prog_def] >>
  conj_tac
  >- (simp[loop_removeProofTheory.state_rel_def,loop_state_def] >>
      simp[lookup_fromAList] >>
      ntac 4 strip_tac >>
      conj_tac
      >- (drule ALOOKUP_MEM >>
          fs [crep_to_loopTheory.compile_prog_def] >>
          simp[MAP2_ZIP] >>
          rw[MEM_MAP,MEM_ZIP,ELIM_UNCURRY,
             loop_liveTheory.optimise_def,
             loop_liveTheory.comp_def] >>
          rw[loop_liveProofTheory.mark_all_syntax_ok]
         ) >>
      match_mp_tac loop_removeProofTheory.comp_prog_has_code >>
      reverse conj_tac >- metis_tac[ALOOKUP_MEM] >>
      fs [crep_to_loopProofTheory.first_compile_prog_all_distinct]) >>
  conj_tac
  >- (simp[loop_to_wordProofTheory.state_rel_def] >>
      simp[loop_state_def,loop_to_wordProofTheory.globals_rel_def,
           pan_to_wordTheory.compile_prog_def] >>
      simp[loop_to_wordProofTheory.code_rel_def] >>
      simp[lookup_fromAList] >>
      simp[loop_to_wordTheory.compile_def,loop_to_wordTheory.compile_prog_def] >>
      simp[ELIM_UNCURRY] >>
      Ho_Rewrite.PURE_REWRITE_TAC[SIMP_RULE std_ss [ELIM_UNCURRY] ALOOKUP_MAP_2] >>
      simp[] >>
      rpt strip_tac >>
      imp_res_tac ALOOKUP_MEM >>
      imp_res_tac loop_removeProofTheory.comp_prog_no_loops >>
      drule_then irule loop_removeProofTheory.compile_prog_distinct_params >>
      irule crep_to_loopProofTheory.compile_prog_distinct_params >>
      irule pan_to_crepProofTheory.compile_prog_distinct_params) >>
  simp[loop_to_wordProofTheory.code_rel_def] >>
  simp[lookup_fromAList] >>
  simp[loop_to_wordTheory.compile_def,loop_to_wordTheory.compile_prog_def] >>
  simp[ELIM_UNCURRY] >>
  Ho_Rewrite.PURE_REWRITE_TAC[SIMP_RULE std_ss [ELIM_UNCURRY] ALOOKUP_MAP_2] >>
  simp[] >>
  rpt strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  imp_res_tac loop_removeProofTheory.comp_prog_no_loops >>
  drule_then irule loop_removeProofTheory.compile_prog_distinct_params >>
  irule crep_to_loopProofTheory.compile_prog_distinct_params >>
  irule pan_to_crepProofTheory.compile_prog_distinct_params
QED

(*** no_install/no_alloc/no_mt lemmas ***)

Theorem pan_to_word_compile_prog_no_install_code:
  compile_prog c prog = prog' ⇒
  no_install_code (fromAList prog')
Proof
  gs[compile_prog_def]>>strip_tac>>
  metis_tac[loop_to_wordProofTheory.loop_compile_no_install_code]
QED

Theorem pan_to_word_compile_prog_no_alloc_code:
  compile_prog c prog = prog' ⇒
  no_alloc_code (fromAList prog')
Proof
  gs[compile_prog_def]>>strip_tac>>
  metis_tac[loop_to_wordProofTheory.loop_compile_no_alloc_code]
QED

Theorem pan_to_word_compile_prog_no_mt_code:
  compile_prog c prog = prog' ⇒
  no_mt_code (fromAList prog')
Proof
  gs[compile_prog_def]>>strip_tac>>
  metis_tac[loop_to_wordProofTheory.loop_compile_no_mt_code]
QED

(*** pan_to_word good_handlers ***)

Theorem pan_to_word_good_handlers:
  compile_prog c prog = prog' ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'
Proof
  gs[compile_prog_def,
     loop_to_wordTheory.compile_def]>>
  strip_tac>>
  irule loop_to_wordProofTheory.loop_to_word_good_handlers>>metis_tac[]
QED

(* lab_pres *)

Theorem pan_to_word_compile_lab_pres:
  pan_to_word$compile_prog c prog = prog' ⇒
  EVERY
  (λ(n,m,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) prog'
Proof
  strip_tac>>gs[pan_to_wordTheory.compile_prog_def]>>
  gs[loop_to_wordTheory.compile_def]>>
  drule loop_to_word_compile_prog_lab_pres>>gs[]
QED

(* first_name offset : lab_min *)

Theorem pan_to_word_compile_prog_lab_min:
  compile_prog c pprog = wprog ⇒
  EVERY (λprog. 60 ≤ FST prog) wprog
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>
  strip_tac>>
  drule_then irule loop_to_word_compile_lab_min>>
  irule crep_to_loop_compile_prog_lab_min>>metis_tac[]
QED

(* inst_ok_less *)

Theorem every_inst_ok_loop_call:
  ∀l prog.
    every_prog (loop_inst_ok c) prog ⇒
    every_prog (loop_inst_ok c) (FST(loop_call$comp l prog))
Proof
  ho_match_mp_tac loop_callTheory.comp_ind \\
  rw[loopPropsTheory.every_prog_def,loop_callTheory.comp_def,
     loop_inst_ok_def] \\
  rpt(pairarg_tac \\ gvs[]) \\
  rw[loopPropsTheory.every_prog_def,loop_callTheory.comp_def,
     loop_inst_ok_def] \\
  every_case_tac \\
  rw[loopPropsTheory.every_prog_def,loop_callTheory.comp_def,
     loop_inst_ok_def]
QED

val prog = “prog:'a loopLang$prog”

Theorem every_inst_ok_loop_live:
  ∀prog.
    every_prog (loop_inst_ok c) ^prog ⇒
    every_prog (loop_inst_ok c) (loop_live$comp prog)
Proof
  rw[loop_liveTheory.comp_def] \\
  ‘(∀p prog q. every_prog (loop_inst_ok c) ^prog ⇒ every_prog (loop_inst_ok c) (FST $ shrink p prog q)) ∧
   (∀p q r prog. every_prog (loop_inst_ok c) ^prog ⇒ OPTION_ALL (every_prog (loop_inst_ok c) o FST) (fixedpoint p q r prog))
  ’
    by(pop_assum kall_tac \\
       ho_match_mp_tac loop_liveTheory.shrink_ind \\ rw[] \\
       gvs $ loopPropsTheory.every_prog_def::loop_inst_ok_def::
              butlast(CONJUNCTS loop_liveTheory.shrink_def) \\
       rpt(pairarg_tac \\ gvs[]) \\
       gvs $ loopPropsTheory.every_prog_def::loop_inst_ok_def::
              butlast(CONJUNCTS loop_liveTheory.shrink_def) \\
       rpt TOP_CASE_TAC \\ gvs[loopPropsTheory.every_prog_def,loop_inst_ok_def] \\
       rpt(pairarg_tac \\ gvs[]) \\
       gvs $ loopPropsTheory.every_prog_def::loop_inst_ok_def::
              butlast(CONJUNCTS loop_liveTheory.shrink_def) \\
       simp[Once loop_liveTheory.shrink_def] \\
       rpt(pairarg_tac \\ gvs[]) \\
       rw[]) \\
  ‘∀prog. every_prog (loop_inst_ok c) ^prog ⇒
          every_prog (loop_inst_ok c) (FST $ mark_all prog)’
    by(rpt $ pop_assum kall_tac \\
       ho_match_mp_tac loop_liveTheory.mark_all_ind \\
       rw[loopPropsTheory.every_prog_def,loop_inst_ok_def,
          loop_liveTheory.mark_all_def] \\
       rpt(pairarg_tac \\ gvs[]) \\
       every_case_tac \\
       gvs[loopPropsTheory.every_prog_def,loop_inst_ok_def,
           loop_liveTheory.mark_all_def] \\
       rpt(pairarg_tac \\ gvs[]) \\
       rw[loopPropsTheory.every_prog_def,loop_inst_ok_def,
           loop_liveTheory.mark_all_def]) \\
  metis_tac[]
QED

Theorem every_inst_ok_less_optimise:
  every_prog (loop_inst_ok c) prog ⇒
  every_prog (loop_inst_ok c) (optimise prog)
Proof
  rw[loop_liveTheory.optimise_def] \\
  metis_tac[every_inst_ok_loop_call,every_inst_ok_loop_live]
QED

Theorem every_inst_ok_less_crep_to_loop_compile_exp:
  (∀ctxt n ns (e:'a crepLang$exp).
     ctxt.target = c.ISA ∧
     every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2) e
     ⇒
     EVERY (every_prog (loop_inst_ok c)) (FST $ crep_to_loop$compile_exp ctxt n ns e)) ∧
  (∀ctxt n ns (es: 'a crepLang$exp list).
     ctxt.target = c.ISA ∧
     EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es
     ⇒
     EVERY (every_prog (loop_inst_ok c)) (FST $ crep_to_loop$compile_exps ctxt n ns es))
Proof
  ho_match_mp_tac crep_to_loopTheory.compile_exp_ind \\
  rw $ [loopPropsTheory.every_prog_def,loop_inst_ok_def,crep_to_loopTheory.prog_if_def,crepPropsTheory.every_exp_def] @ butlast(CONJUNCTS crep_to_loopTheory.compile_exp_def) \\
  rpt(pairarg_tac \\ gvs[]) \\
  gvs[loopPropsTheory.every_prog_def,loop_inst_ok_def,crep_to_loopTheory.prog_if_def]
  THEN1 (gvs[DefnBase.one_line_ify NONE crep_to_loopTheory.compile_crepop_def,AllCaseEqs(),
             loopPropsTheory.every_prog_def,loop_inst_ok_def] \\
         rw[EVERY_MEM,MEM_MAPi] \\
         rw[loopPropsTheory.every_prog_def,loop_inst_ok_def] \\
         Cases_on ‘es’ \\ gvs[quantHeuristicsTheory.LIST_LENGTH_1,
                              crep_to_loopProofTheory.compile_exps_alt] \\
         rpt(pairarg_tac \\ gvs[]) \\
         metis_tac[EVERY_MEM])
  THEN1 (gvs[DefnBase.one_line_ify NONE crep_to_loopTheory.compile_crepop_def,AllCaseEqs(),
             loopPropsTheory.every_prog_def,loop_inst_ok_def] \\
         rw[EVERY_MEM,MEM_MAPi] \\
         rw[loopPropsTheory.every_prog_def,loop_inst_ok_def] \\
         Cases_on ‘es’ \\ gvs[quantHeuristicsTheory.LIST_LENGTH_1,
                              crep_to_loopProofTheory.compile_exps_alt] \\
         rpt(pairarg_tac \\ gvs[]) \\
         metis_tac[EVERY_MEM]) \\
  Cases_on ‘es’ \\
  gvs[crep_to_loopProofTheory.compile_exps_alt] \\
  rpt(pairarg_tac \\ gvs[])
QED

Theorem every_prog_loop_inst_ok_nested_seq:
  ∀c ps.
    every_prog (loop_inst_ok c) $ nested_seq ps = EVERY (every_prog (loop_inst_ok c)) ps
Proof
  strip_tac \\ Induct \\
  gvs[loopPropsTheory.every_prog_def,loopLangTheory.nested_seq_def,
      loop_to_wordProofTheory.loop_inst_ok_def]
QED

Theorem every_inst_ok_less_crep_to_loop_compile:
  ∀ctxt ns body.
    ctxt.target = c.ISA ∧
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of body)
    ⇒
    every_prog (loop_inst_ok c) (crep_to_loop$compile ctxt ns body)
Proof
  ho_match_mp_tac crep_to_loopTheory.compile_ind \\
  rw[loopPropsTheory.every_prog_def,loop_inst_ok_def,
     crep_to_loopTheory.compile_def,crepPropsTheory.exps_of_def] \\
  rpt(pairarg_tac \\ gvs[]) \\
  gvs[loopPropsTheory.every_prog_def,loop_inst_ok_def,
      crep_to_loopTheory.compile_def,
      every_prog_loop_inst_ok_nested_seq] \\
  gvs[EVERY_APPEND,loopPropsTheory.every_prog_def,loop_inst_ok_def,
      crep_to_loopTheory.compile_def]
  >~ [‘MAP2’] >-
    (drule $ cj 2 every_inst_ok_less_crep_to_loop_compile_exp \\
     fs [MAP2_ZIP, crep_to_loopTheory.gen_temps_def, EVERY_MAP, UNCURRY,
        loopPropsTheory.every_prog_def, loop_inst_ok_def] \\
     disch_then $ qspecl_then [‘ctxt.vmax + 1’,‘ns’,‘es’] mp_tac \\
     simp [] \\
     gs [CaseEq "prod", CaseEq "option", crepPropsTheory.exps_of_def] \\
     gvs [] \\
     rpt (TOP_CASE_TAC \\ fs []) \\
     gs [crepPropsTheory.exps_of_def] \\
     rw[MAP2_ZIP,EVERY_MEM,crep_to_loopTheory.gen_temps_def,MEM_MAP,MEM_ZIP,PULL_EXISTS,
        loopPropsTheory.every_prog_def,loop_inst_ok_def
       ]) \\
  imp_res_tac (cj 1 every_inst_ok_less_crep_to_loop_compile_exp) \\
  every_case_tac \\
  gvs[loopPropsTheory.every_prog_def,loopLangTheory.nested_seq_def,
      loop_to_wordProofTheory.loop_inst_ok_def,
      every_prog_loop_inst_ok_nested_seq] \\
  metis_tac[FST,SND,PAIR]
QED

Theorem every_inst_ok_less_comp_func:
  EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of body) ⇒
  every_prog (loop_inst_ok c) (comp_func c.ISA (crep_to_loop$make_funcs prog) params body)
Proof
  rw[crep_to_loopTheory.comp_func_def,crep_to_loopTheory.make_funcs_def] \\
  match_mp_tac every_inst_ok_less_crep_to_loop_compile \\
  rw[crep_to_loopTheory.mk_ctxt_def]
QED

Theorem every_inst_ok_arith_simp_exp:
  ! exp.
  every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2) exp ==>
  every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2) (simp_exp exp)
Proof
  ho_match_mp_tac crep_arithTheory.simp_exp_ind
  \\ simp [crep_arithTheory.simp_exp_def, crepPropsTheory.every_exp_def]
  \\ rw [crep_arithTheory.mul_const_def]
  \\ every_case_tac \\ fs []
  \\ gvs [listTheory.MAP_EQ_CONS]
  \\ fs [crepPropsTheory.every_exp_def]
  \\ simp [EVERY_MAP]
  \\ fs [EVERY_MEM]
QED

Theorem every_inst_ok_arith_simp_prog:
  ! prog.
  EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
          (exps_of prog) ==>
  EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
          (exps_of (simp_prog prog))
Proof
  ho_match_mp_tac crep_arithTheory.simp_prog_ind
  \\ simp [crep_arithTheory.simp_prog_def, crepPropsTheory.exps_of_def]
  \\ simp [every_inst_ok_arith_simp_exp]
  \\ rw []
  \\ every_case_tac \\ fs []
  \\ fs [crepPropsTheory.exps_of_def, every_inst_ok_arith_simp_exp]
  \\ fs [EVERY_MAP]
  \\ fs [EVERY_MEM, every_inst_ok_arith_simp_exp]
QED

Theorem every_inst_ok_nested_decs:
  ∀ns ps p.
    LENGTH ns = LENGTH ps ⇒
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of(nested_decs ns ps p)) =
    (EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) ps ∧
     EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of p))
Proof
  ho_match_mp_tac crepLangTheory.nested_decs_ind \\
  rw[crepLangTheory.nested_decs_def,crepPropsTheory.exps_of_def] \\
  metis_tac[]
QED

Theorem every_inst_ok_less_pan_to_crep_comp_field:
  ∀index shapes es es' sh.
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es ∧
    comp_field index shapes es = (es',sh) ⇒
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es'
Proof
  Induct_on ‘shapes’ \\
  rw[pan_to_crepTheory.comp_field_def,crepPropsTheory.every_exp_def,EVERY_TAKE] >>
  res_tac >>
  gvs[EVERY_DROP,EVERY_TAKE]
QED

Theorem every_inst_ok_less_pan_to_crep_load_shape:
  ∀w n e.
    every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2) e ⇒
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
          (load_shape w n e)
Proof
  Induct_on ‘n’ \\
  rw[crepLangTheory.load_shape_def,crepPropsTheory.every_exp_def]
QED

Theorem every_inst_ok_less_pan_to_crep_cexp_heads:
  ∀ces es.
    EVERY (EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))) ces ∧
    cexp_heads ces = SOME es
    ⇒
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es
Proof
  Induct_on ‘ces’ \\
  rw[pan_to_crepTheory.cexp_heads_def] \\
  gvs[AllCaseEqs()]
QED

Theorem every_inst_ok_less_pan_to_crep_compile_exp:
  ∀ctxt e es sh.
    every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) e ∧
    compile_exp ctxt e = (es,sh) ⇒
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es
Proof
  ho_match_mp_tac pan_to_crepTheory.compile_exp_ind \\
  rw[pan_to_crepTheory.compile_exp_def,
     crepPropsTheory.every_exp_def,
     panPropsTheory.every_exp_def
    ] \\
  gvs[crepPropsTheory.every_exp_def,
      panPropsTheory.every_exp_def,
      AllCaseEqs(),EVERY_MAP,EVERY_FLAT] \\
  rpt(pairarg_tac \\ gvs[]) \\
  gvs[AllCaseEqs(),crepPropsTheory.every_exp_def,
      panPropsTheory.every_exp_def] \\
  imp_res_tac every_inst_ok_less_pan_to_crep_comp_field \\
  imp_res_tac every_inst_ok_less_pan_to_crep_load_shape
  >~ [‘cexp_heads’] >-
    (drule_at (Pos last) every_inst_ok_less_pan_to_crep_cexp_heads \\
     reverse impl_tac >- metis_tac[] \\
     gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS] \\
     metis_tac[FST,SND,PAIR])
  >~ [‘cexp_heads’] >-
    (drule_at (Pos last) every_inst_ok_less_pan_to_crep_cexp_heads \\
     impl_keep_tac >-
      (gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS] \\
       metis_tac[FST,SND,PAIR]) \\
     reverse $ rw[]
     >- metis_tac[ETA_AX] \\
     gvs[crepPropsTheory.cexp_heads_simp_def,pan_to_crepProofTheory.cexp_heads_eq]) \\
  gvs[EVERY_MEM,PULL_FORALL] \\
  gvs[EVERY_MAP,MEM_MAP,PULL_FORALL] \\
  metis_tac[FST,SND,PAIR,EVERY_DEF,MEM]
QED

Theorem exps_of_nested_seq:
  ∀es.
    exps_of (nested_seq es) = FLAT (MAP exps_of es)
Proof
  Induct \\
  gvs[crepLangTheory.nested_seq_def,crepPropsTheory.exps_of_def]
QED

Theorem pan_exps_of_nested_seq:
  ∀es.
    exps_of (panLang$nested_seq es) = FLAT (MAP exps_of es)
Proof
  Induct \\
  gvs[panLangTheory.nested_seq_def,panPropsTheory.exps_of_def]
QED

Theorem every_inst_ok_less_stores:
  ∀e es a.
    EVERY
    (λx. EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
               (exps_of x))
    (stores e es a) ⇔
      (es ≠ [] ⇒ every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2) e) ∧
      EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es
Proof
  Induct_on ‘es’ \\
  rw[crepLangTheory.stores_def,crepPropsTheory.exps_of_def,crepPropsTheory.every_exp_def] \\
  metis_tac[]
QED

Theorem every_inst_ok_less_store_globals:
  ∀w es.
    EVERY
    (λx. EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
               (exps_of x))
    (store_globals w es) ⇔
      EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) es
Proof
  Induct_on ‘es’ \\
  rw[crepLangTheory.store_globals_def,crepPropsTheory.exps_of_def,crepPropsTheory.every_exp_def]
QED

Theorem load_globals_alt:
  ∀ad n. load_globals ad n =
         GENLIST (λn. LoadGlob $ ad + n2w n) n
Proof
  Induct_on ‘n’ \\ rw[crepLangTheory.load_globals_def,GENLIST_CONS,o_DEF,n2w_SUC]
QED

Theorem every_inst_ok_less_pan_to_crep_compile:
  ∀ctxt body e.
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of body) ⇒
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of(pan_to_crep$compile ctxt body))
Proof
  ho_match_mp_tac pan_to_crepTheory.compile_ind \\
  rw[panPropsTheory.exps_of_def,pan_to_crepTheory.compile_def,
     crepPropsTheory.exps_of_def] \\
  rpt(pairarg_tac \\ gvs[]) \\
  rw[every_inst_ok_nested_decs,crepPropsTheory.exps_of_def] \\
  rpt(PURE_FULL_CASE_TAC \\ gvs[]) \\
  gvs[panPropsTheory.exps_of_def,pan_to_crepTheory.compile_def,
      crepPropsTheory.exps_of_def,exps_of_nested_seq,
      EVERY_FLAT,EVERY_MAP,every_inst_ok_nested_decs,every_inst_ok_less_stores,
      every_inst_ok_less_store_globals
     ] \\
  imp_res_tac every_inst_ok_less_pan_to_crep_compile_exp
  >~ [‘ret_hdl’] >-
   (gvs[] \\
    conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
    PURE_TOP_CASE_TAC \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def])
  >~ [‘ret_hdl’] >-
   (gvs[] \\
    conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
    PURE_TOP_CASE_TAC \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def])
  >~ [‘exp_hdl’] >-
   (gvs[] \\
    conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.exp_hdl_def] \\
    rpt(PURE_TOP_CASE_TAC \\ gvs[]) \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def])
  >~ [‘exp_hdl’] >-
   (gvs[] \\
    rpt conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.exp_hdl_def,
         DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
    rpt(PURE_TOP_CASE_TAC \\ gvs[]) \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def])
  >~ [‘exp_hdl’] >-
   (gvs[] \\
    rpt conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.exp_hdl_def,
         DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
    rpt(PURE_TOP_CASE_TAC \\ gvs[]) \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def]) \\
  simp[every_inst_ok_nested_decs,crepPropsTheory.exps_of_def,every_inst_ok_nested_decs,crepPropsTheory.length_load_globals_eq_read_size,load_globals_alt] \\
  rw[EVERY_MEM,MAP2_MAP,MEM_ZIP,MEM_MAP,UNCURRY_DEF] \\
  gvs[UNCURRY_DEF,crepPropsTheory.exps_of_def,EVERY_MEM,MEM_EL,PULL_EXISTS,EL_MAP,
      crepPropsTheory.every_exp_def,DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
  metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,MEM_EL,EVERY_MEM,
            FST,SND,PAIR]
QED

Definition good_panops_def:
  good_panops (Function fi) =
  EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of fi.body) ∧
  good_panops (Decl sh v exp) =
  every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) exp
End

Theorem every_inst_ok_less_pan_to_crep_compile_prog:
  EVERY good_panops pan_code ⇒
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of body)) (pan_to_crep$compile_prog pan_code)
Proof
  rw[EVERY_MEM] \\ pairarg_tac \\
  gvs[pan_to_crepTheory.compile_prog_def,MEM_MAP] \\
  pairarg_tac \\ gvs[] \\
  pairarg_tac \\ gvs[] \\
  gvs[panPropsTheory.functions_eq_FILTER,MEM_MAP,MEM_FILTER,
      oneline panLangTheory.is_function_def] \\
  PURE_FULL_CASE_TAC \\ gvs[] \\
  first_x_assum drule \\
  rw[pan_to_crepTheory.comp_func_def] \\
  match_mp_tac $ MP_CANON $ Ho_Rewrite.REWRITE_RULE [EVERY_MEM,PULL_EXISTS,PULL_FORALL] every_inst_ok_less_pan_to_crep_compile \\
  first_assum $ irule_at $ Pos last \\
  gvs[good_panops_def,EVERY_MEM]
QED

Theorem every_inst_ok_less_ret_to_tail:
  ∀p.
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of $ ret_to_tail p) ⇔
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of p)
Proof
  ho_match_mp_tac pan_simpTheory.ret_to_tail_ind \\
  rw[panPropsTheory.exps_of_def,pan_simpTheory.compile_def,
     pan_simpTheory.ret_to_tail_def,pan_simpTheory.seq_assoc_def,
     panPropsTheory.every_exp_def,
     pan_simpTheory.seq_call_ret_def] \\
  rpt(PURE_TOP_CASE_TAC \\ gvs[]) \\
  gvs[panPropsTheory.exps_of_def,pan_simpTheory.compile_def,
      pan_simpTheory.ret_to_tail_def,pan_simpTheory.seq_assoc_def,
      panPropsTheory.every_exp_def,
      pan_simpTheory.seq_call_ret_def] \\
  metis_tac[]
QED

Theorem every_inst_ok_less_seq_assoc:
  ∀p q.
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of $ seq_assoc p q) ⇔
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of p ++ exps_of q)
Proof
  ho_match_mp_tac pan_simpTheory.seq_assoc_ind \\
  rw[panPropsTheory.exps_of_def,pan_simpTheory.compile_def,
     pan_simpTheory.seq_assoc_def,pan_simpTheory.seq_assoc_def,
     panPropsTheory.every_exp_def,
     pan_simpTheory.seq_call_ret_def] \\
  rpt(PURE_TOP_CASE_TAC \\ gvs[]) \\
  gvs[panPropsTheory.exps_of_def,pan_simpTheory.compile_def,
      pan_simpTheory.seq_assoc_def,pan_simpTheory.seq_assoc_def,
      panPropsTheory.every_exp_def,
      pan_simpTheory.seq_call_ret_def] \\
  metis_tac[]
QED

Theorem every_inst_ok_less_pan_simp_compile:
  ∀body.
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of body) ⇒
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of(compile body))
Proof
  Induct \\
  gvs[panPropsTheory.exps_of_def,pan_simpTheory.compile_def,
      pan_simpTheory.ret_to_tail_def,pan_simpTheory.seq_assoc_def,
      every_inst_ok_less_ret_to_tail,
      every_inst_ok_less_seq_assoc]
QED

Theorem every_inst_ok_less_crep_to_loop_compile_prog:
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of body)) crep_code ⇒
  EVERY (λ(name,params,body). every_prog (loop_inst_ok c) body)
    (crep_to_loop$compile_prog c.ISA crep_code)
Proof
  simp [crep_to_loopTheory.compile_prog_def]
  \\ simp [MAP2_MAP, EVERY_MAP]
  \\ simp [ELIM_UNCURRY, every_zip_snd]
  \\ rw [EVERY_MEM]
  \\ irule every_inst_ok_less_optimise
  \\ irule every_inst_ok_less_comp_func
  \\ irule every_inst_ok_arith_simp_prog
  \\ fs [EVERY_MEM]
  \\ res_tac
QED

Theorem every_inst_ok_less_pan_simp_compile_prog:
  ∀pan_code.
    EVERY good_panops pan_code ⇒
    EVERY good_panops (pan_simp$compile_prog pan_code)
Proof
  Induct using panLangTheory.functions_ind >>
  gvs[panLangTheory.functions_def,pan_simpTheory.compile_prog_def,EVERY_MAP,
      good_panops_def] >>
  rw[] >>
  metis_tac[every_inst_ok_less_pan_simp_compile,EVERY_MEM]
QED

Theorem every_inst_ok_less_pan_globals_compile_exp:
  ∀ctxt e.
    every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) e ⇒
    every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2) (pan_globals$compile_exp ctxt e)
Proof
  recInduct pan_globalsTheory.compile_exp_ind >> rw[] >>
  gvs[pan_globalsTheory.compile_exp_def,ELIM_UNCURRY,panPropsTheory.exps_of_def,
      panPropsTheory.every_exp_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  gvs[pan_globalsTheory.compile_exp_def,ELIM_UNCURRY,panPropsTheory.exps_of_def,
      panPropsTheory.every_exp_def,EVERY_MAP] >>
  gvs[EVERY_MEM]
QED

Theorem every_inst_ok_less_pan_globals_compile:
  ∀ctxt code.
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of code) ⇒
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of(pan_globals$compile ctxt code))
Proof
  recInduct pan_globalsTheory.compile_ind >> rw[] >>
  gvs[pan_globalsTheory.compile_def,ELIM_UNCURRY,panPropsTheory.exps_of_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  gvs[pan_globalsTheory.compile_def,ELIM_UNCURRY,panPropsTheory.exps_of_def,
      panPropsTheory.every_exp_def,
      EVERY_MAP] >>
  gvs[EVERY_MEM] >>
  metis_tac[every_inst_ok_less_pan_globals_compile_exp]
QED

Theorem every_inst_ok_less_pan_globals_compile_decs:
  ∀ctxt pan_code.
    EVERY good_panops pan_code ⇒
    EVERY good_panops (FST(SND(pan_globals$compile_decs ctxt pan_code)))
Proof
  recInduct pan_globalsTheory.compile_decs_ind >>
  rw[good_panops_def,pan_globalsTheory.compile_decs_def,ELIM_UNCURRY,every_inst_ok_less_pan_globals_compile]
QED

Theorem every_inst_ok_less_pan_globals_compile_decs_init:
  ∀ctxt pan_code.
    EVERY good_panops pan_code ⇒
    EVERY (EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2))) (MAP exps_of (FST(pan_globals$compile_decs ctxt pan_code)))
Proof
  recInduct pan_globalsTheory.compile_decs_ind >>
  rw[good_panops_def,pan_globalsTheory.compile_decs_def,ELIM_UNCURRY,every_inst_ok_less_pan_globals_compile,panPropsTheory.exps_of_def,panPropsTheory.every_exp_def] >>
  metis_tac[every_inst_ok_less_pan_globals_compile_exp]
QED

Theorem every_inst_ok_less_fperm:
  ∀f g code.
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of code) ⇒
    EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of(fperm f g code))
Proof
  recInduct pan_globalsTheory.fperm_ind >> rw[] >>
  gvs[pan_globalsTheory.fperm_def,ELIM_UNCURRY,panPropsTheory.exps_of_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  gvs[pan_globalsTheory.fperm_def,ELIM_UNCURRY,panPropsTheory.exps_of_def]
QED

Theorem every_inst_ok_less_fperm_decs:
  ∀f g pan_code.
    EVERY good_panops pan_code ⇒
    EVERY good_panops (fperm_decs f g pan_code)
Proof
  recInduct pan_globalsTheory.fperm_decs_ind >>
  rw[good_panops_def,pan_globalsTheory.fperm_decs_def,ELIM_UNCURRY,every_inst_ok_less_fperm]
QED

Theorem every_inst_ok_less_pan_globals_compile_top:
  ∀pan_code main.
    EVERY good_panops pan_code ⇒
    EVERY good_panops (pan_globals$compile_top pan_code main)
Proof
  rw[pan_globalsTheory.compile_top_def] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[panLangTheory.functions_def,ELIM_UNCURRY]) >>
  gvs[good_panops_def,panPropsTheory.exps_of_def,pan_exps_of_nested_seq,
      EVERY_FLAT,EVERY_MAP,panPropsTheory.every_exp_def] >>
  conj_tac
  >- (irule $ REWRITE_RULE [EVERY_MAP] every_inst_ok_less_pan_globals_compile_decs_init >>
      irule every_inst_ok_less_fperm_decs >>
      gvs[EVERY_MEM,pan_globalsTheory.resort_decls_def,MEM_FILTER] >>
      rw[] >>
      res_tac) >>
  irule every_inst_ok_less_pan_globals_compile_decs >>
  irule every_inst_ok_less_fperm_decs >>
  gvs[EVERY_MEM,pan_globalsTheory.resort_decls_def,MEM_FILTER] >>
  rw[] >>
  res_tac
QED

Theorem pan_to_word_every_inst_ok_less:
  pan_to_word$compile_prog c.ISA pan_code = wprog0 ∧
  byte_offset_ok c 0w ∧ addr_offset_ok c 0w ∧
  EVERY good_panops pan_code
  ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  drule_then irule loop_to_word_every_inst_ok_less>>gs[]>>
  last_x_assum kall_tac>>
  irule every_inst_ok_less_crep_to_loop_compile_prog>>
  irule every_inst_ok_less_pan_to_crep_compile_prog>>
  irule every_inst_ok_less_pan_globals_compile_top>>
  irule every_inst_ok_less_pan_simp_compile_prog>>
  simp []
QED

val _ = export_theory();
