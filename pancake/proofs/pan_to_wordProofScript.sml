(*
  Correctness proof for --
*)

open preamble pan_to_wordTheory
     pan_simpProofTheory pan_to_crepProofTheory
     crep_to_loopProofTheory loop_to_wordProofTheory

val _ = new_theory "pan_to_wordProof";


Definition pan_simp_st_def:
  pan_simp_st (s:('a,'ffi) panSem$state) (pan_code:(mlstring # (mlstring # shape) list # α prog) list) =
    s with code := alist_to_fmap (pan_simp$compile_prog pan_code)
End


Definition crep_state_def:
  crep_state (s:('a,'ffi) panSem$state) (pan_code:(mlstring # (mlstring # shape) list # α prog) list) =
  <| locals   := FEMPTY;
     globals  := FEMPTY;
     code     := alist_to_fmap (pan_to_crep$compile_prog pan_code);
     eids     := FRANGE ((get_eids pan_code):mlstring |-> 'a word);
     memory   := s.memory;
     memaddrs := s.memaddrs;
     clock    := s.clock;
     be       := s.be;
     ffi      := s.ffi|>
End


Definition mk_mem_def:
  mk_mem ctxt smem =
        λad. wlab_wloc ctxt (smem ad)
End

Definition loop_state_def:
  loop_state (s:('a,'ffi) crepSem$state) crep_code ck =
  let ctxt = mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code) in
  <| locals   := LN;
     globals  := FEMPTY;
     memory   := mk_mem ctxt s.memory;
     mdomain := s.memaddrs;
     code     := fromAList (crep_to_loop$compile_prog crep_code);
     clock    := ck;
     be       := s.be;
     ffi      := s.ffi|>
End


Definition consistent_labels_def:
  consistent_labels (mem:'a word -> 'a word_lab)
                    (pan_code:(mlstring # (mlstring # shape) list # α prog) list) <=>
  ∀ad f.
   mem ad = Label f ⇒
   ∃n m. FLOOKUP (make_funcs (compile_prog (pan_simp$compile_prog pan_code))) f = SOME (n,m)
End


Theorem FDOM_get_eids_pan_simp_compile_eq:
  !prog. FDOM ((get_eids prog): mlstring |-> α word) =
  FDOM ((get_eids (pan_simp$compile_prog prog)):mlstring |-> α word)
Proof
  rw [] >>
  fs [pan_to_crepTheory.get_eids_def] >>
  qmatch_goalsub_abbrev_tac ‘BIGUNION es’ >>
  qmatch_goalsub_abbrev_tac ‘_ = set (MAP FST (MAP2 (λx y. (x,y))
    (SET_TO_LIST (BIGUNION ces)) _ ))’ >>
  qsuff_tac ‘es = ces’
  >- fs [] >>
  fs [Abbr ‘es’, Abbr ‘ces’, pan_simpTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  fs [pan_simpProofTheory.map_snd_f_eq] >>
  fs [GSYM LIST_TO_SET_MAP] >>
  qsuff_tac ‘MAP exp_ids (MAP compile (MAP (SND ∘ SND) prog)) =
             MAP exp_ids (MAP (SND ∘ SND) prog)’
  >- fs [] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘n < LENGTH  (MAP (SND ∘ SND) prog)’ by fs [] >>
  drule (INST_TYPE [``:'a``|->``:'c``,
                    ``:'b``|->``:'c``] EL_MAP) >>
  disch_then (qspec_then ‘pan_simp$compile’ mp_tac) >>
  fs [] >>
  strip_tac >>
  fs [exp_ids_compile_eq]
QED


Theorem foo:
  !p f.
   (FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option = NONE ==>
   FLOOKUP (crep_to_loop$make_funcs (pan_to_crep$compile_prog (compile_prog p))) f = NONE
Proof
  rw [] >>
  fs [] >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  fs [ALOOKUP_NONE] >>
  fs [MEM_MAP] >>
  CCONTR_TAC >> fs [] >>
  fs [MEM_EL] >> rveq >> fs [] >>
  cheat
QED


Theorem bar:
  !p f x.
   (FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option = SOME x ==>
   FLOOKUP (crep_to_loop$make_funcs (pan_to_crep$compile_prog (compile_prog p))) f = SOME x
Proof
  rw [] >>
  fs [] >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  ho_match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac >-  cheat >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >> fs [] >>
  conj_tac >- cheat >>
  cheat
QED

Theorem abc:
  !p f x.
   (FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option =
   FLOOKUP (crep_to_loop$make_funcs (pan_to_crep$compile_prog (compile_prog p))) f
Proof
  rpt gen_tac >>
  cases_on ‘(FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option’ >>
  metis_tac [foo, bar]
QED


Theorem state_rel_imp_semantics:
  t.memory = mk_mem
             (mk_ctxt FEMPTY (make_funcs (compile_prog pan_code)) 0
              (get_eids (compile_prog pan_code))) s.memory /\
  consistent_labels s.memory pan_code /\
  t.mdomain = s.memaddrs ∧
  t.be = s.be ∧
  t.ffi = s.ffi ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  ALOOKUP pan_code start = SOME ([],prog) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = fromAList (pan_to_word$compile_prog pan_code) ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  FLOOKUP (make_funcs (compile_prog (pan_simp$compile_prog pan_code))) start = SOME (lc,0) /\
  lookup 0 t.locals = SOME (Loc 1 0) /\
  semantics s start <> Fail ==>
  semantics (t:('a,'b, 'ffi) wordSem$state) lc =
  semantics (s:('a,'ffi) panSem$state) start
Proof
  rw [] >>
  (* pan-simp pass *)
  ‘state_rel s (pan_simp_st s pan_code) (pan_simp_st s pan_code).code’ by (
    fs [pan_simpProofTheory.state_rel_def, pan_simp_st_def] >>
    conj_tac >> rw []
    >- (
     fs [pan_simpTheory.compile_prog_def] >>
     fs [ALOOKUP_FAILS] >>
     rw [] >>
     fs [MEM_MAP] >>
     rw [] >>
     cases_on ‘y’ >>
     cases_on ‘r’ >> fs [] >>
     CCONTR_TAC >> fs [] >>
     rveq >> fs [] >> metis_tac []) >>
    fs [pan_simpTheory.compile_prog_def] >>
    fs [ALOOKUP_EXISTS_IFF] >>
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
    conj_tac
    >- (
     fs [MAP_MAP_o] >>
     qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
     ‘MAP ff pan_code = MAP FST pan_code’ by (
       fs [Abbr ‘ff’, MAP_EQ_f] >>
       rw [] >>
       cases_on ‘e’ >> fs [] >>
       cases_on ‘r’ >> fs []) >>
     fs []) >>
    fs [MEM_MAP] >>
    qexists_tac ‘(f,vshs,prog')’ >>
    fs [] >>
    drule ALOOKUP_MEM >> fs []) >>
  drule pan_simpProofTheory.state_rel_imp_semantics >>
  disch_then (qspecl_then [‘pan_code’, ‘start’, ‘prog’] mp_tac) >>
  fs [] >>
  impl_tac >- fs [pan_simp_st_def] >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘semantics pst start’ >>

  (* pan_to_crep pass *)
  qmatch_asmsub_abbrev_tac ‘make_funcs (_ pcode)’ >>
  ‘ALOOKUP pcode start = SOME ([],compile prog)’ by (
    fs [Abbr ‘pcode’, pan_simpTheory.compile_prog_def] >>
    match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
    conj_tac
    >- (
     fs [MAP_MAP_o] >>
     qmatch_goalsub_abbrev_tac ‘MAP ff _’ >>
     ‘MAP ff pan_code = MAP FST pan_code’ by (
       fs [Abbr ‘ff’, MAP_EQ_f] >>
       rw [] >>
       cases_on ‘e’ >> fs [] >>
       cases_on ‘r’ >> fs []) >>
     fs []) >>
    fs [MEM_MAP] >>
    qexists_tac ‘(start,[],prog)’ >>
    fs [] >>
    drule ALOOKUP_MEM >> fs []) >>
  ‘state_rel pst (crep_state pst pcode)’ by
    fs [Abbr ‘pcode’, pan_to_crepProofTheory.state_rel_def, crep_state_def] >>
  drule pan_to_crepProofTheory.state_rel_imp_semantics >>
  disch_then (qspecl_then [‘pcode’,
                           ‘start’, ‘pan_simp$compile prog’] mp_tac) >>
  fs [] >>
  impl_tac
  >- (
   fs [Abbr ‘pcode’, Abbr ‘pst’, pan_simp_st_def, crep_state_def] >>
   conj_tac
   >- (
    match_mp_tac pan_simpProofTheory.first_compile_prog_all_distinct >>
    fs []) >>
   fs [size_of_eids_compile_eq] >>
   fs [Once FDOM_get_eids_pan_simp_compile_eq]) >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘semantics cst start’ >>
  (* crep_to_loop pass *)
  qmatch_asmsub_abbrev_tac ‘make_funcs ccode’ >>
  ‘ALOOKUP ccode start =
   SOME ([],comp_func (make_funcs pcode)
         (get_eids pcode) [] (compile prog))’ by (
    fs [Abbr ‘ccode’, Abbr ‘pcode’, Abbr ‘pst’, Abbr ‘cst’,
        pan_simp_st_def, crep_state_def, loop_state_def] >>
    match_mp_tac alookup_compile_prog_code >>
    conj_tac
    >- (
     match_mp_tac pan_simpProofTheory.first_compile_prog_all_distinct >>
     fs []) >>
    fs [pan_simpTheory.compile_prog_def]) >>
  ‘cst.memaddrs =
   (loop_state cst ccode t.clock).mdomain’ by
    fs [Abbr ‘ccode’, Abbr ‘pcode’, Abbr ‘cst’, Abbr ‘pst’, crep_state_def, loop_state_def] >>
  drule crep_to_loopProofTheory.state_rel_imp_semantics >>
  disch_then (qspecl_then [‘ccode’,
                           ‘start’, ‘comp_func (make_funcs pcode)
                                     (get_eids pcode) [] (compile prog)’,
                           ‘lc’] mp_tac) >>
  impl_tac
  >- (
   fs [Abbr ‘ccode’, Abbr ‘pcode’, Abbr ‘pst’, Abbr ‘cst’, pan_simp_st_def, crep_state_def, loop_state_def] >>
   conj_tac
   >- (
    fs [crep_to_loopTheory.mk_ctxt_def, mk_mem_def, mem_rel_def, consistent_labels_def] >>
    rw [] >> res_tac >> rfs []) >>
   conj_tac
   >- cheat (* fs [get_eids_equivs] *) >>
   conj_tac >- fs [crep_to_loopProofTheory.globals_rel_def] >>
   match_mp_tac first_compile_prog_all_distinct >>
   match_mp_tac pan_simpProofTheory.first_compile_prog_all_distinct >>
   fs []) >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘_ = semantics lst _’ >>
  (* loop_to_word pass *)

  qmatch_asmsub_abbrev_tac ‘_ = SOME ([],cprog)’ >>
  ‘st_rel lst t (compile_prog ccode)’ by (
    fs [st_rel_def] >>
    conj_tac
    >- (
     fs [loop_removeProofTheory.state_rel_def] >>
     qexists_tac ‘fromAList (comp_prog (compile_prog ccode))’ >>
     fs [] >>
     rw [] >>
     cheat (* syntax_ok etc *)) >>
    conj_tac
    >- (
     fs [loop_to_wordProofTheory.state_rel_def] >>
     fs [Abbr ‘lst’, Abbr ‘cst’, Abbr ‘pst’, pan_simp_st_def,
         loop_state_def, crep_state_def] >>
     conj_tac
     >- (
      fs [mk_mem_def, crep_to_loopTheory.mk_ctxt_def] >>
      fs [FUN_EQ_THM] >>
      rw [] >>
      cases_on ‘s.memory ad’ >> fs [wlab_wloc_def, Once abc]) >>
     fs [globals_rel_def] >>
     fs [loop_to_wordProofTheory.code_rel_def] >>
     rw []
     >- (
      fs [lookup_fromAList] >>
      dxrule ALOOKUP_MEM >>
      strip_tac >>
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      conj_tac
      >- cheat >>
      fs [pan_to_wordTheory.compile_prog_def] >>
      cheat)
     >- cheat >>
     cheat) >>
    cheat) >>
  drule fstate_rel_imp_semantics >>

  disch_then (qspecl_then [‘lc’,
     ‘loop_live$optimise (comp_func (make_funcs ccode)
                          (get_eids ccode) [] cprog)’] mp_tac) >>
  impl_tac
  >- (
   fs [Abbr ‘lst’, loop_state_def,
       Abbr ‘ccode’, Abbr ‘pcode’,
       pan_to_wordTheory.compile_prog_def] >>
   fs [lookup_fromAList] >>
   fs [Abbr ‘cprog’] >>
   match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
   conj_tac >- cheat >>
   fs [crep_to_loopTheory.compile_prog_def] >>
   fs [MEM_EL] >>
   cheat) >>
  cheat
QED


val _ = export_theory();
