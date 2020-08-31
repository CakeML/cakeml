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
  loop_state (s:('a,'ffi) crepSem$state) crep_code =
  let ctxt = mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code) in
  <| locals   := LN;
     globals  := FEMPTY;
     memory   := mk_mem ctxt s.memory;
     mdomain := s.memaddrs;
     code     := fromAList (crep_to_loop$compile_prog crep_code);
     clock    := ARB;
     be       := s.be;
     ffi      := s.ffi|>
End

Theorem get_eids_equivs:
   !pan_code. equivs (FRANGE ((get_eids pan_code):mlstring |-> 'a word))
          ((get_eids (compile_prog pan_code)): 'a word set)
Proof
  cheat

QED

Theorem all_distinct_first_compile_prog:
  ALL_DISTINCT (MAP FST pan_code) ==>
  ALL_DISTINCT (MAP FST (pan_to_crep$compile_prog pan_code))
Proof
  cheat
QED

Theorem alookup_compile_prog_code:
  ALOOKUP pan_code start = SOME ([],prog) ==>
  ALOOKUP (pan_to_crep$compile_prog pan_code) start =
  SOME ([],
        comp_func (make_funcs pan_code) (get_eids pan_code) [] prog)
Proof
  cheat
QED


Theorem state_rel_imp_semantics:
  s.memaddrs = t.mdomain ∧
  s.be = t.be ∧
  s.ffi = t.ffi ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = fromAList (pan_to_word$compile_prog pan_code) ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  (∀ad f.
   s.memory ad = Label f ⇒
   ∃n m. FLOOKUP (make_funcs (compile_prog pan_code)) f = SOME (n,m)) /\
  ALOOKUP pan_code start = SOME ([],prog) ∧
  semantics s start <> Fail ==>
  semantics (t:('a,'b, 'ffi) wordSem$state) lc =
  semantics (s:('a,'ffi) panSem$state) start
Proof
  rw [] >>
  ‘state_rel s (crep_state s pan_code)’ by (
    fs [pan_to_crepProofTheory.state_rel_def, crep_state_def]) >>
  drule pan_to_crepProofTheory.state_rel_imp_semantics >>
  disch_then (qspecl_then [‘start’, ‘prog’ , ‘pan_code’] mp_tac) >>
  fs [] >>
  impl_tac
  >- fs [crep_state_def] >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  ‘(crep_state s pan_code).memaddrs =
   (loop_state (crep_state s pan_code) (pan_to_crep$compile_prog pan_code)).mdomain’ by
    fs [crep_state_def, loop_state_def] >>
  drule crep_to_loopProofTheory.state_rel_imp_semantics >>
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
   conj_tac >- metis_tac [all_distinct_first_compile_prog] >>
   conj_tac >- metis_tac [alookup_compile_prog_code] >>
   cheat) >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  pop_assum kall_tac >>
  match_mp_tac fstate_rel_imp_semantics >>
  cheat
QED
val _ = export_theory();
