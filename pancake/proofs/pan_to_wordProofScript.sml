(*
  Correctness proof for --
*)

open preamble pan_to_wordTheory
     pan_to_crepProofTheory crep_to_loopProofTheory
     loop_to_wordProofTheory

val _ = new_theory "pan_to_wordProof";


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


Theorem foo:
  !n prog. n ∈ FRANGE ((get_eids prog):mlstring |-> 'a word) ==>
  ∃params p e. MEM (params,p) (MAP SND prog) /\ e ∈ exp_ids p /\
      FLOOKUP ((get_eids prog):mlstring |-> 'a word) e = SOME n
Proof
  cheat
QED

Theorem get_eids_equivs:
   !prog. equivs (FRANGE ((get_eids prog):mlstring |-> 'a word))
          ((get_eids (compile_prog prog)): 'a word set)
Proof
  rw [] >>
  fs [equivs_def] >>
  rw [] >>
  fs [EQ_IMP_THM] >>
  conj_tac
  >- (
   rw [] >>
   drule foo >>
   strip_tac >>
   drule bar >>
   disch_then (qspecl_then [‘((get_eids prog):mlstring |-> 'a word)’, ‘n’,
                            ‘(mk_ctxt (make_vmap params) (make_funcs prog)
                              (size_of_shape (Comb (MAP SND params)) − 1)
                              (get_eids prog))’] mp_tac) >>
   fs [] >>
   strip_tac >>
   fs [pan_to_crepTheory.compile_prog_def] >>
   fs [pan_to_crepTheory.comp_func_def] >>
   fs [crep_to_loopTheory.get_eids_def] >>
   qmatch_asmsub_abbrev_tac ‘n ∈ exp_ids fs’ >>
   match_mp_tac crepPropsTheory.abc >>
   qexists_tac ‘fs’ >>
   fs [] >>
   fs [MEM_MAP] >> rveq >>
   fs [Abbr ‘fs’] >>
   qexists_tac ‘(FST y, crep_vars params, fs)’ >>
   conj_tac >- fs [Abbr ‘fs’] >>






   fs [pan_to_crepTheory.mk_ctxt_def] >>



   qmatch_goalsub_abbrev_tac ‘n ∈ s’ >>
   ‘FINITE s’ by cheat >>
   drule MEM_SET_TO_LIST >>
   disch_then (qspec_then ‘n’ mp_tac) >>
   strip_tac >>
   qsuff_tac ‘MEM n (SET_TO_LIST s)’
   >- metis_tac [] >>
   pop_assum kall_tac >>
   pop_assum kall_tac >>
   fs [Abbr ‘s’] >>
   qmatch_goalsub_abbrev_tac ‘n ∈ s’ >>





      MEM_MAP





   fs [crep_to_loopTheory.get_eids_def] >>
   fs [MAP_MAP_o] >>
   cheat) >>
  cheat
QED


Theorem state_rel_imp_semantics:
  t.memory = mk_mem
             (mk_ctxt FEMPTY (make_funcs (compile_prog pan_code)) 0
              (get_eids (compile_prog pan_code))) s.memory /\
  t.mdomain = s.memaddrs ∧
  t.be = s.be ∧
  t.ffi = s.ffi ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  ALOOKUP pan_code start = SOME ([],prog) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = fromAList (pan_to_word$compile_prog pan_code) ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  (∀ad f.
   s.memory ad = Label f ⇒
   ∃n m. FLOOKUP (make_funcs (compile_prog pan_code)) f = SOME (n,m)) /\
  FLOOKUP (make_funcs (compile_prog pan_code)) start = SOME (lc,0) /\
  lookup 0 t.locals = SOME (Loc 1 0) /\
  semantics s start <> Fail ==>
  semantics (t:('a,'b, 'ffi) wordSem$state) lc =
  semantics (s:('a,'ffi) panSem$state) start
Proof
  rw [] >>
  ‘state_rel s (crep_state s pan_code)’ by (
    fs [pan_to_crepProofTheory.state_rel_def, crep_state_def]) >>
  drule (GEN_ALL pan_to_crepProofTheory.state_rel_imp_semantics) >>
  disch_then (qspecl_then [‘start’, ‘prog’ , ‘pan_code’] mp_tac) >>
  fs [] >>
  impl_tac
  >- fs [crep_state_def] >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  ‘(crep_state s pan_code).memaddrs =
   (loop_state (crep_state s pan_code) (pan_to_crep$compile_prog pan_code) t.clock).mdomain’ by
    fs [crep_state_def, loop_state_def] >>
  drule (GEN_ALL crep_to_loopProofTheory.state_rel_imp_semantics) >>
  disch_then (qspecl_then [‘start’, ‘comp_func (make_funcs pan_code) (get_eids pan_code) [] prog’,
                           ‘lc’, ‘compile_prog pan_code’] mp_tac) >>
  impl_tac
  >- (
   fs [crep_state_def, loop_state_def] >>
   conj_tac
   >- (
    fs [crep_to_loopTheory.mk_ctxt_def, mk_mem_def, mem_rel_def] >>
    rw [] >> res_tac >> rfs []) >>
   conj_tac
   >- fs [get_eids_equivs] >>
   conj_tac >- fs [crep_to_loopProofTheory.globals_rel_def] >>
   conj_tac >- metis_tac [first_compile_prog_all_distinct] >>
   metis_tac [alookup_compile_prog_code]) >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  pop_assum kall_tac >>
  match_mp_tac (GEN_ALL fstate_rel_imp_semantics) >>
  MAP_EVERY qexists_tac [‘ARB’, ‘compile_prog (compile_prog pan_code)’] >>
  fs [] >>
  conj_tac
  >- (
   fs [st_rel_def] >>
   conj_tac
   >- (
    fs [loop_removeProofTheory.state_rel_def] >>
    qexists_tac ‘fromAList (comp_prog (compile_prog (compile_prog pan_code)))’ >>
    fs [] >>
    rpt gen_tac >>
    strip_tac >>
    fs [loop_state_def, crep_state_def] >>
    cheat) >>
   fs [loop_to_wordProofTheory.state_rel_def] >>
   fs [loop_state_def, crep_state_def] >>
   fs [globals_rel_def] >>
   fs [] >>
   fs [loop_to_wordProofTheory.code_rel_def] >>
   rpt gen_tac >>
   strip_tac >>
   conj_tac
   >- (
    fs [pan_to_wordTheory.compile_prog_def,
        loop_to_wordTheory.compile_def] >>
    fs [loop_to_wordTheory.compile_prog_def] >>
    fs [lookup_fromAList] >>
    drule ALOOKUP_MEM >>
    strip_tac >>
    match_mp_tac wordPropsTheory.ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME >>
    reverse conj_tac
    >- (
     fs [MEM_MAP] >>
     qexists_tac ‘(name,params,body)’ >>
     fs []) >>
    cheat) >>
   conj_tac
   >- cheat >>
   cheat) >>
  fs [loop_state_def, crep_state_def] >>
  fs [pan_to_wordTheory.compile_prog_def] >>
  qpat_x_assum ‘FLOOKUP _ _ = SOME (lc,0)’ assume_tac >>
  match_mp_tac mem_lookup_fromalist_some >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  cheat
QED


val _ = export_theory();
