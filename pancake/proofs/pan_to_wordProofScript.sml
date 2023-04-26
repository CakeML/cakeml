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
     memory   := s.memory;
     memaddrs := s.memaddrs;
     clock    := s.clock;
     be       := s.be;
     ffi      := s.ffi;
     base_addr := s.base_addr|>
End

(* wlab_wloc should have taken only funcs of context *)
Definition mk_mem_def:
  mk_mem funcs smem =
        λad. wlab_wloc funcs (smem ad)
End

Definition loop_state_def:
  loop_state (s:('a,'ffi) crepSem$state) crep_code ck =
  <| locals   := LN;
     globals  := FEMPTY;
     memory   := mk_mem (make_funcs crep_code) s.memory;
     mdomain := s.memaddrs;
     code     := fromAList (crep_to_loop$compile_prog crep_code);
     clock    := ck;
     be       := s.be;
     ffi      := s.ffi;
     base_addr := s.base_addr|>
End


Definition consistent_labels_def:
  consistent_labels (mem:'a word -> 'a word_lab)
                    (pan_code:(mlstring # (mlstring # shape) list # α prog) list) <=>
  ∀ad f.
   mem ad = Label f ⇒
   ∃n m. FLOOKUP (make_funcs (compile_prog (pan_simp$compile_prog pan_code))) f = SOME (n,m)
End

Definition distinct_params_def:
  distinct_params prog <=>
  EVERY (λ(name,params,body). ALL_DISTINCT params) prog
End


Theorem first_compile_prog_all_distinct:
  !prog. ALL_DISTINCT (MAP FST prog) ==>
   ALL_DISTINCT (MAP FST (pan_to_word$compile_prog prog))
Proof
  rw [] >>
  fs [pan_to_wordTheory.compile_prog_def] >>
  match_mp_tac loop_to_wordProofTheory.first_compile_all_distinct >>
  metis_tac [crep_to_loopProofTheory.first_compile_prog_all_distinct]
QED


Theorem FDOM_get_eids_pan_simp_compile_eq:
  !prog. FDOM ((get_eids prog): mlstring |-> α word) =
  FDOM ((get_eids (pan_simp$compile_prog prog)):mlstring |-> α word)
Proof
  rw [] >>
  fs [pan_to_crepTheory.get_eids_def] >>
  qmatch_goalsub_abbrev_tac ‘remove_dup (FLAT es)’ >>
  qmatch_goalsub_abbrev_tac ‘_ = set (MAP FST (MAP2 (λx y. (x,y))
    (remove_dup (FLAT ces)) _ ))’ >>
  qsuff_tac ‘es = ces’
  >- fs [] >>
  fs [Abbr ‘es’, Abbr ‘ces’, pan_simpTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  fs [pan_simpProofTheory.map_snd_f_eq] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  rw [] >>
  ‘EL n (MAP (SND ∘ SND) prog) =
   (SND ∘ SND) (EL n prog)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  fs [exp_ids_compile_eq]
QED


Theorem flookup_pan_simp_mk_funcs_none_eq:
  !p f.
   (FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option = NONE ==>
   FLOOKUP (crep_to_loop$make_funcs (pan_to_crep$compile_prog (compile_prog p))) f = NONE
Proof
  rw [] >>
  fs [flookup_thm] >>
  qmatch_asmsub_abbrev_tac ‘_ ∉ xs’ >>
  qmatch_goalsub_abbrev_tac ‘_ ∉ ys’ >>
  qsuff_tac ‘xs = ys’
  >- (strip_tac >> fs []) >>
  fs [Abbr ‘xs’, Abbr ‘ys’] >>
  pop_assum kall_tac >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  qmatch_goalsub_abbrev_tac ‘set xs = set ys’ >>
  qsuff_tac ‘xs = ys’
  >- fs []  >>
  fs [Abbr ‘xs’, Abbr ‘ys’] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  conj_asm1_tac
  >- fs [pan_to_crepTheory.compile_prog_def, pan_simpTheory.compile_prog_def] >>
  fs [] >>
  rw [] >>
  qmatch_goalsub_abbrev_tac ‘FST (EL n (MAP2 f ws xs)) = FST (EL n (MAP2 g ys zs))’ >>
  ‘EL n (MAP2 f ws xs) = f (EL n ws) (EL n xs)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  ‘EL n (MAP2 g ys zs) = g (EL n ys) (EL n zs)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
  fs [pan_to_crepTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP f _) = EL n (MAP g _)’ >>
  ‘EL n (MAP f p) = f (EL n p)’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >> fs []) >>
  ‘EL n (MAP g (compile_prog p)) = g (EL n (compile_prog p))’ by (
    match_mp_tac EL_MAP >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  ‘EL n (pan_simp$compile_prog p) =
   (λ(name,params,body). (name,params,compile body)) (EL n p)’ by (
    fs [pan_simpTheory.compile_prog_def] >>
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  cases_on ‘EL n p’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem flookup_pan_simp_mk_funcs_some_eq:
  !p f x. ALL_DISTINCT (MAP FST p) ∧
   (FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option = SOME x ==>
   FLOOKUP (crep_to_loop$make_funcs (pan_to_crep$compile_prog (compile_prog p))) f = SOME x
Proof
  rw [] >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  reverse conj_tac
  >- (
   fs [MEM_EL] >>
   qexists_tac ‘n’ >>
   reverse conj_asm1_tac
   >- (
    qmatch_goalsub_abbrev_tac ‘EL n (MAP2 ff ws xs) = EL n (MAP2 gg ys zs)’ >>
    ‘EL n (MAP2 ff ws xs) = ff (EL n ws) (EL n xs)’ by (
      match_mp_tac EL_MAP2 >>
      unabbrev_all_tac >> fs []) >>
    ‘EL n (MAP2 gg ys zs) = gg (EL n ys) (EL n zs)’ by (
      match_mp_tac EL_MAP2 >>
      unabbrev_all_tac >> fs []) >>
    fs [] >>
    unabbrev_all_tac >> fs [] >> rveq >> rfs [] >>
    conj_tac
    >- (
     fs [pan_to_crepTheory.compile_prog_def] >>
     fs [MAP_MAP_o] >>
     qmatch_goalsub_abbrev_tac ‘EL n (MAP ff _) = EL n (MAP gg _)’ >>
     ‘EL n (MAP ff p) = ff (EL n p)’ by (
       match_mp_tac EL_MAP >>
       unabbrev_all_tac >> fs []) >>
     ‘EL n (MAP gg (compile_prog p)) = gg (EL n (compile_prog p))’ by (
       match_mp_tac EL_MAP >>
       unabbrev_all_tac >> fs []) >>
     fs [] >>
     unabbrev_all_tac >> fs [] >>
     ‘EL n (pan_simp$compile_prog p) =
      (λ(name,params,body). (name,params,compile body)) (EL n p)’ by (
       fs [pan_simpTheory.compile_prog_def] >>
       match_mp_tac EL_MAP >>
       fs []) >>
     fs [] >>
     cases_on ‘EL n p’ >> fs [] >>
     cases_on ‘r’ >> fs []) >>
    qmatch_goalsub_abbrev_tac ‘EL n (MAP2 ff ws xs) = EL n (MAP2 gg ys zs)’ >>
    ‘EL n (MAP2 ff ws xs) = ff (EL n ws) (EL n xs)’ by (
      match_mp_tac EL_MAP2 >>
      unabbrev_all_tac >> fs []) >>
    ‘EL n (MAP2 gg ys zs) = gg (EL n ys) (EL n zs)’ by (
      match_mp_tac EL_MAP2 >>
      unabbrev_all_tac >> fs []) >>
    fs [] >>
    unabbrev_all_tac >> fs [] >> rveq >> fs [] >>
    qmatch_goalsub_abbrev_tac ‘EL n (MAP ff pp) = EL n (MAP gg qq)’ >>
    ‘EL n (MAP ff pp) = ff (EL n pp)’ by (
      match_mp_tac EL_MAP >>
      unabbrev_all_tac >> fs []) >>
    ‘EL n (MAP gg qq) = gg (EL n qq)’ by (
      match_mp_tac EL_MAP >>
      unabbrev_all_tac >> fs []) >>
    fs [] >>
    unabbrev_all_tac >> fs [] >> rveq >>
    fs [pan_to_crepTheory.compile_prog_def] >>
    qmatch_goalsub_abbrev_tac
    ‘LENGTH (FST (SND (EL n (MAP ff _)))) =
     LENGTH (FST (SND (EL n (MAP gg _))))’ >>
    ‘EL n (MAP ff p) = ff (EL n p)’ by (
      match_mp_tac EL_MAP >>
      unabbrev_all_tac >> fs []) >>
    ‘EL n (MAP gg (compile_prog p)) = gg (EL n (compile_prog p))’ by (
      match_mp_tac EL_MAP >>
      unabbrev_all_tac >> fs []) >>
    fs [] >>
    unabbrev_all_tac >> fs [] >>
    ‘EL n (pan_simp$compile_prog p) =
     (λ(name,params,body). (name,params,compile body)) (EL n p)’ by (
      fs [pan_simpTheory.compile_prog_def] >>
      match_mp_tac EL_MAP >>
      fs []) >>
    fs [] >>
    cases_on ‘EL n p’ >> fs [] >>
    cases_on ‘r’ >> fs []) >>
   fs [pan_to_crepTheory.compile_prog_def,
       pan_simpTheory.compile_prog_def]) >>
  qmatch_goalsub_abbrev_tac ‘MAP _ xs’ >>
  ‘MAP FST xs = MAP FST (compile_prog (compile_prog p))’ by (
    unabbrev_all_tac >> fs [] >>
    qmatch_goalsub_abbrev_tac ‘MAP _ xs = MAP _ ys’ >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    unabbrev_all_tac >> fs [] >>
    rw [] >>
    qmatch_goalsub_abbrev_tac ‘FST (EL n (MAP2 ff ws xs)) = _’ >>
    ‘EL n (MAP2 ff ws xs) = ff (EL n ws) (EL n xs)’ by (
      match_mp_tac EL_MAP2 >>
      unabbrev_all_tac >> fs []) >>
    fs [] >>
    unabbrev_all_tac >> fs [] >>
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  match_mp_tac pan_to_crepProofTheory.first_compile_prog_all_distinct >>
  match_mp_tac pan_simpProofTheory.first_compile_prog_all_distinct >>
  fs []
QED


Theorem flookup_pan_simp_mk_funcs_eq:
  !p f x. ALL_DISTINCT (MAP FST p) ==>
   (FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option =
   FLOOKUP (crep_to_loop$make_funcs (pan_to_crep$compile_prog (compile_prog p))) f
Proof
  rpt gen_tac >>
  cases_on ‘(FLOOKUP (make_funcs (compile_prog p)) f): (num#num) option’ >>
  metis_tac [flookup_pan_simp_mk_funcs_none_eq, flookup_pan_simp_mk_funcs_some_eq]
QED


Theorem crep_to_loop_intermediate_label:
  ∀pan_code start prog.
    ALOOKUP pan_code start = SOME ([],prog) ∧
    ALL_DISTINCT (MAP FST pan_code) ⇒
    ∃n. n < LENGTH pan_code ∧ EL n pan_code = (start,[],prog) ∧
        FLOOKUP (crep_to_loop$make_funcs
                 (pan_to_crep$compile_prog (pan_simp$compile_prog pan_code))) start = SOME (n+first_name,0)
Proof
  rw [] >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  fs [crep_to_loopTheory.make_funcs_def] >>
  fs [ALOOKUP_EXISTS_IFF] >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [] >>
  match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
  conj_tac
  >- (
  qmatch_goalsub_abbrev_tac ‘MAP _ pp’ >>
  qsuff_tac ‘MAP FST pp = MAP FST pan_code’
  >- fs [] >>
  fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  fs [Abbr ‘pp’] >>
  conj_asm1_tac
  >- (
    fs [pan_to_crepTheory.compile_prog_def,
        pan_simpTheory.compile_prog_def]) >>
  fs [] >>
  rw [] >>
  qmatch_goalsub_abbrev_tac ‘EL n' (MAP2 f xs ys)’ >>
  ‘EL n' (MAP2 f xs ys) = f (EL n' xs) (EL n' ys)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  fs [pan_to_crepTheory.compile_prog_def,
      pan_simpTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n' (MAP ff _)’ >>
  ‘EL n' (MAP ff pan_code) = ff (EL n' pan_code)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  cases_on ‘EL n' pan_code’ >>
  fs [] >> cases_on ‘r’ >> rfs []) >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  conj_asm1_tac
  >- (
  fs [pan_to_crepTheory.compile_prog_def,
      pan_simpTheory.compile_prog_def]) >>
  qmatch_goalsub_abbrev_tac ‘_ = EL n (MAP2 f xs ys)’ >>
  ‘EL n (MAP2 f xs ys) = f (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  conj_tac
  >- (
   fs [pan_to_crepTheory.compile_prog_def,
       pan_simpTheory.compile_prog_def] >>
   fs [MAP_MAP_o] >>
   qmatch_goalsub_abbrev_tac ‘_ = EL n (MAP ff _)’ >>
   ‘EL n (MAP ff pan_code) = ff (EL n pan_code)’ by (
     match_mp_tac EL_MAP >>
     fs []) >>
   fs [] >>
   unabbrev_all_tac >> fs [] >>
   cases_on ‘EL n pan_code’ >>
   fs [] >> cases_on ‘r’ >> rfs []) >>
  qmatch_goalsub_abbrev_tac ‘_ = EL n (MAP2 f xs ys)’ >>
  ‘EL n (MAP2 f xs ys) = f (EL n xs) (EL n ys)’ by (
    match_mp_tac EL_MAP2 >>
    unabbrev_all_tac >> fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP f pp) = _’ >>
  ‘EL n (MAP f pp) = f (EL n pp)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  fs [pan_to_crepTheory.compile_prog_def,
      pan_simpTheory.compile_prog_def] >>
  fs [MAP_MAP_o] >>
  qmatch_goalsub_abbrev_tac ‘EL n (MAP ff _)’ >>
  ‘EL n (MAP ff pan_code) = ff (EL n pan_code)’ by (
    match_mp_tac EL_MAP >>
    fs []) >>
  fs [] >>
  unabbrev_all_tac >> fs [] >>
  cases_on ‘EL n pan_code’ >>
  fs [] >> cases_on ‘r’ >>
  rfs [pan_to_crepTheory.crep_vars_def, panLangTheory.size_of_shape_def]
QED


Theorem state_rel_imp_semantics:
  t.memory = mk_mem (make_funcs (compile_prog pan_code)) s.memory /\
  distinct_params pan_code ∧
  consistent_labels s.memory pan_code /\
  t.mdomain = s.memaddrs ∧
  t.be = s.be ∧
  t.ffi = s.ffi ∧
  ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  ALOOKUP pan_code start = SOME ([],prog) ∧
  lc < LENGTH pan_code ∧ EL lc pan_code = (start,[],prog) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = fromAList (pan_to_word$compile_prog pan_code) ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  lookup 0 t.locals = SOME (Loc 1 0) /\
  semantics s start <> Fail ==>
    semantics (t:('a,'b, 'ffi) wordSem$state) (lc+first_name) =
    semantics (s:('a,'ffi) panSem$state) start
Proof
  rw [] >>
  drule crep_to_loop_intermediate_label >>
  rfs [] >>
  strip_tac >>
  ‘n = lc’ by (
    drule ALL_DISTINCT_EL_IMP >>
    disch_then (qspecl_then [‘n’, ‘lc’] mp_tac) >>
    fs [] >>
    strip_tac >>
    ‘EL n (MAP FST pan_code) = FST (EL n pan_code)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    ‘EL lc (MAP FST pan_code) = FST (EL lc pan_code)’ by (
      match_mp_tac EL_MAP >>
      fs []) >>
    gs [])  >> rveq >>
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
                           ‘lc+first_name’] mp_tac) >>
  impl_tac
  >- (
   fs [Abbr ‘ccode’, Abbr ‘pcode’, Abbr ‘pst’, Abbr ‘cst’,
       pan_simp_st_def, crep_state_def, loop_state_def] >>
   conj_tac
   >- (
    fs [crep_to_loopTheory.mk_ctxt_def, mk_mem_def, mem_rel_def, consistent_labels_def] >>
    rw [] >> res_tac >> rfs []) >>
   conj_tac >- fs [crep_to_loopProofTheory.globals_rel_def] >>
   match_mp_tac pan_to_crepProofTheory.first_compile_prog_all_distinct >>
   match_mp_tac pan_simpProofTheory.first_compile_prog_all_distinct >>
   fs []) >>
  strip_tac >>
  pop_assum (assume_tac o GSYM) >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘_ = semantics lst _’ >>

  (* loop_to_word pass *)
  qmatch_asmsub_abbrev_tac ‘_ = SOME ([],cprog)’ >>
  drule pan_simpProofTheory.first_compile_prog_all_distinct >>
  strip_tac >>
  drule pan_to_crepProofTheory.first_compile_prog_all_distinct >>
  strip_tac >>
  ‘st_rel lst t (compile_prog ccode)’ by (
    fs [st_rel_def] >>
    conj_tac
    >- (
     fs [loop_removeProofTheory.state_rel_def] >>
     qexists_tac ‘fromAList (comp_prog (compile_prog ccode))’ >>
     fs [] >> rw []
     >- (
      fs [Abbr ‘lst’, loop_state_def] >>
      fs [crep_to_loopTheory.compile_prog_def] >>
      drule pan_commonPropsTheory.lookup_some_el >>
      strip_tac >>
      pop_assum mp_tac >>
      qmatch_goalsub_abbrev_tac ‘EL m (MAP2 gg xs ys)’ >>
      ‘EL m (MAP2 gg xs ys) = gg (EL m xs) (EL m ys)’ by (
        ho_match_mp_tac EL_MAP2 >>
        fs [Abbr ‘xs’, Abbr ‘ys’]) >>
      fs [Abbr ‘gg’, Abbr ‘xs’, Abbr ‘ys’] >>
      pop_assum kall_tac >>
      cases_on ‘EL m ccode’ >> fs [] >>
      cases_on ‘r’ >> fs [] >>
      strip_tac >> rveq >> gs [] >>
      fs [loop_liveTheory.optimise_def] >>
      fs [loop_liveTheory.comp_def] >>
      fs [loop_liveProofTheory.mark_all_syntax_ok]) >>
     (* has_code *)
     match_mp_tac loop_removeProofTheory.comp_prog_has_code >>
     reverse conj_tac
     >- (
        fs [Abbr ‘lst’, loop_state_def] >>
        fs [lookup_fromAList] >>
        drule ALOOKUP_MEM >>
        fs []) >>
     fs [crep_to_loopProofTheory.first_compile_prog_all_distinct]) >>
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
      cases_on ‘s.memory ad’ >> fs [wlab_wloc_def, Once flookup_pan_simp_mk_funcs_eq]) >>
     fs [globals_rel_def] >>
     fs [loop_to_wordProofTheory.code_rel_def] >>
     rw []
     >- (
      fs [lookup_fromAList] >>
      dxrule ALOOKUP_MEM >>
      strip_tac >>
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      conj_tac
      >- (
       match_mp_tac first_compile_prog_all_distinct >>
       fs []) >>
      fs [pan_to_wordTheory.compile_prog_def] >>
      fs [loop_to_wordTheory.compile_def] >>
      drule mem_prog_mem_compile_prog >> fs []) >>
     fs [lookup_fromAList] >>
     drule ALOOKUP_MEM >>
     strip_tac >>
     rfs []
     >- (drule loop_removeProofTheory.comp_prog_no_loops >> fs []) >>
     drule loop_removeProofTheory.compile_prog_distinct_params >>
     impl_tac
     >- (
       ho_match_mp_tac crep_to_loopProofTheory.compile_prog_distinct_params >>
       fs [Abbr ‘ccode’] >>
       ho_match_mp_tac pan_to_crepProofTheory.compile_prog_distinct_params >>
       fs [Abbr ‘pcode’] >>
       ho_match_mp_tac pan_simpProofTheory.compile_prog_distinct_params >>
       fs [distinct_params_def]) >>
     fs []) >>
    fs [loop_to_wordProofTheory.code_rel_def] >>
    rw []
    >- (
     fs [lookup_fromAList] >>
     dxrule ALOOKUP_MEM >>
     strip_tac >>
     match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
     conj_tac
     >- (
        match_mp_tac first_compile_prog_all_distinct >>
        fs []) >>
     fs [pan_to_wordTheory.compile_prog_def] >>
     fs [loop_to_wordTheory.compile_def] >>
     drule mem_prog_mem_compile_prog >> fs []) >>
    drule pan_commonPropsTheory.lookup_some_el >>
    strip_tac >>
    drule EL_MEM >>
    strip_tac >>
    rfs []
    >- (drule loop_removeProofTheory.comp_prog_no_loops >> fs []) >>
    drule loop_removeProofTheory.compile_prog_distinct_params >>
    impl_tac
    >- (
      ho_match_mp_tac crep_to_loopProofTheory.compile_prog_distinct_params >>
      fs [Abbr ‘ccode’] >>
      ho_match_mp_tac pan_to_crepProofTheory.compile_prog_distinct_params >>
      fs [Abbr ‘pcode’] >>
      ho_match_mp_tac pan_simpProofTheory.compile_prog_distinct_params >>
      fs [distinct_params_def]) >>
    fs []) >>
  drule fstate_rel_imp_semantics >>
  disch_then (qspecl_then [‘lc+first_name’,
     ‘loop_live$optimise (comp_func (make_funcs ccode) [] cprog)’] mp_tac) >>
  impl_tac
  >- (
   fs [Abbr ‘lst’, loop_state_def,
       Abbr ‘ccode’, Abbr ‘pcode’,
       pan_to_wordTheory.compile_prog_def] >>
   fs [lookup_fromAList] >>
   fs [Abbr ‘cprog’] >>
   match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
   conj_tac
   >- fs [crep_to_loopProofTheory.first_compile_prog_all_distinct] >>
   fs [crep_to_loopTheory.compile_prog_def] >>
   qmatch_goalsub_abbrev_tac ‘MEM ff _’ >>
   pop_assum mp_tac >>
   qpat_x_assum ‘lc < _’ mp_tac >>
   qpat_x_assum ‘EL lc pan_code = _’ mp_tac >>
   qpat_x_assum ‘FLOOKUP _ _ = SOME _’ mp_tac >>
   qpat_x_assum ‘ALOOKUP _ _ = SOME _’ mp_tac >>
   qpat_x_assum ‘ALOOKUP _ _ = SOME _’ mp_tac >>
   qpat_x_assum ‘ALOOKUP _ _ = SOME _’ mp_tac >>
   rpt (pop_assum kall_tac) >>
   rpt strip_tac >>
   qmatch_asmsub_abbrev_tac
   ‘ALOOKUP (_ (_ pan_code)) start = SOME ([],cprog)’ >>
   ‘lc < LENGTH (pan_to_crep$compile_prog (pan_simp$compile_prog pan_code))’ by
     fs [pan_to_crepTheory.compile_prog_def, pan_simpTheory.compile_prog_def] >>
   fs [MEM_EL] >>
   qexists_tac ‘lc’ >>
   rfs [] >>
   qmatch_goalsub_abbrev_tac ‘_ = EL lc (MAP2 gg xs ys)’ >>
   ‘EL lc (MAP2 gg xs ys) = gg (EL lc xs) (EL lc ys)’ by (
     ho_match_mp_tac EL_MAP2 >>
     fs [Abbr ‘xs’, Abbr ‘ys’]) >>
   fs [Abbr ‘gg’, Abbr ‘xs’, Abbr ‘ys’] >>
   pop_assum kall_tac >>
   qmatch_goalsub_abbrev_tac ‘_ = hs x’ >>
   cases_on ‘x’ >> fs [] >>
   cases_on ‘r’ >> fs [] >>
   fs [Abbr ‘hs’, Abbr ‘ff’] >>
   conj_asm1_tac
   >- (
    fs [pan_to_crepTheory.compile_prog_def] >>
    pop_assum mp_tac >>
    qmatch_goalsub_abbrev_tac ‘EL n (MAP ff xs)’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘ff’, Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, Abbr ‘xs’] >>
    pop_assum kall_tac >>
    strip_tac >>
    cases_on ‘EL n (pan_simp$compile_prog pan_code)’ >>
    fs [] >>
    cases_on ‘r’ >> fs [] >>
    unabbrev_all_tac >>
    fs [] >>  rveq >> fs [] >>
    pop_assum mp_tac >>
    fs [pan_simpTheory.compile_prog_def] >>
    qmatch_goalsub_abbrev_tac ‘EL n (MAP ff xs)’ >>
    ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
      match_mp_tac EL_MAP >>
      fs [Abbr ‘ff’, Abbr ‘xs’]) >>
    fs [Abbr ‘ff’, Abbr ‘xs’] >> rveq >> gs [] >>
    fs [pan_to_crepTheory.crep_vars_def, panLangTheory.size_of_shape_def]) >>
   cases_on ‘q'’ >> fs [GENLIST] >>
   qsuff_tac ‘cprog = r'’
   >- fs [] >>
   fs [Abbr ‘cprog’] >>
   pop_assum kall_tac >>
   fs [pan_to_crepTheory.compile_prog_def] >>
   pop_assum mp_tac >>
   qmatch_goalsub_abbrev_tac ‘EL n (MAP ff xs)’ >>
   ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
     match_mp_tac EL_MAP >>
     fs [Abbr ‘ff’, Abbr ‘xs’]) >>
   fs [Abbr ‘ff’, Abbr ‘xs’] >>
   strip_tac >>
   cases_on ‘EL n (pan_simp$compile_prog pan_code)’ >>
   fs [] >>
   cases_on ‘r’ >> fs [] >> rveq >> gs [] >>
   pop_assum mp_tac >>
   fs [pan_simpTheory.compile_prog_def] >>
   qmatch_goalsub_abbrev_tac ‘EL n (MAP ff xs)’ >>
   ‘EL n (MAP ff xs) = ff (EL n xs)’ by (
     match_mp_tac EL_MAP >>
     fs [Abbr ‘ff’, Abbr ‘xs’]) >>
   fs [Abbr ‘ff’, Abbr ‘xs’]) >>
  fs []
QED

(*** no_install/no_alloc/no_mt lemmas ***)

Theorem pan_to_word_compile_prog_no_install_code:
  compile_prog prog = prog' ⇒
  no_install_code (fromAList prog')
Proof
  gs[compile_prog_def]>>strip_tac>>
  metis_tac[loop_to_wordProofTheory.loop_compile_no_install_code]
QED

Theorem pan_to_word_compile_prog_no_alloc_code:
  compile_prog prog = prog' ⇒
  no_alloc_code (fromAList prog')
Proof
  gs[compile_prog_def]>>strip_tac>>
  metis_tac[loop_to_wordProofTheory.loop_compile_no_alloc_code]
QED

Theorem pan_to_word_compile_prog_no_mt_code:
  compile_prog prog = prog' ⇒
  no_mt_code (fromAList prog')
Proof
  gs[compile_prog_def]>>strip_tac>>
  metis_tac[loop_to_wordProofTheory.loop_compile_no_mt_code]
QED

(*** pan_to_word good_handlers ***)

Theorem pan_to_word_good_handlers:
  compile_prog prog = prog' ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'
Proof
  gs[compile_prog_def,
     loop_to_wordTheory.compile_def]>>
  strip_tac>>
  irule loop_to_wordProofTheory.loop_to_word_good_handlers>>metis_tac[]
QED

(* lab_pres *)

Theorem pan_to_word_compile_lab_pres:
  pan_to_word$compile_prog prog = prog' ⇒
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
  compile_prog pprog = wprog ⇒
  EVERY (λprog. 60 ≤ FST prog) wprog
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>
  strip_tac>>
  drule_then irule loop_to_word_compile_lab_min>>
  irule crep_to_loop_compile_prog_lab_min>>metis_tac[]
QED

(* inst_ok_less *)

Theorem pan_to_word_every_inst_ok_less:
  pan_to_word$compile_prog pan_code = wprog0 ∧
  byte_offset_ok c 0w ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  drule_then irule loop_to_word_every_inst_ok_less>>gs[]
QED

val _ = export_theory();
