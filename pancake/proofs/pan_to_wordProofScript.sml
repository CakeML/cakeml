(*
  Correctness proof for combined pan_to_word compilation.
*)
Theory pan_to_wordProof
Ancestors
  pan_to_word pan_simpProof pan_to_crepProof crep_to_loopProof
  loop_to_wordProof
Libs
  preamble

Type prog[local] = “:α panLang$prog”

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
     sh_memaddrs := s.sh_memaddrs;
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
  loop_state (s:('a,'ffi) crepSem$state) c crep_code ck =
  <| locals   := LN;
     globals  := FEMPTY;
     memory   := mk_mem (make_funcs crep_code) s.memory;
     mdomain := s.memaddrs;
     sh_mdomain := s.sh_memaddrs;
     code     := fromAList (crep_to_loop$compile_prog c crep_code);
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
   ALL_DISTINCT (MAP FST (pan_to_word$compile_prog c prog))
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
  t.sh_mdomain = s.sh_memaddrs ∧
  t.be = s.be ∧
  t.ffi = s.ffi ∧
  ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  ALOOKUP pan_code start = SOME ([],prog) ∧
  lc < LENGTH pan_code ∧ EL lc pan_code = (start,[],prog) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = fromAList (pan_to_word$compile_prog c pan_code) ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  lookup 0 t.locals = SOME (Loc 1 0) /\ good_dimindex (:'a) ∧
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
   (loop_state cst c ccode t.clock).mdomain’ by
    fs [Abbr ‘ccode’, Abbr ‘pcode’, Abbr ‘cst’, Abbr ‘pst’, crep_state_def, loop_state_def] >>
  drule crep_to_loopProofTheory.state_rel_imp_semantics >>
  disch_then (qspecl_then [‘ccode’,
                           ‘start’, ‘comp_func (make_funcs pcode)
                                     (get_eids pcode) [] (compile prog)’,
                           ‘lc+first_name’,‘c’] mp_tac) >>
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
  ‘st_rel lst t (compile_prog c ccode)’ by (
    fs [st_rel_def] >>
    conj_tac
    >- (
     fs [loop_removeProofTheory.state_rel_def] >>
     qexists_tac ‘fromAList (comp_prog (compile_prog c ccode))’ >>
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
     drule mem_prog_mem_compile_prog >> fs []
    )
    >- (
      drule pan_commonPropsTheory.lookup_some_el >> rw [] >>
      imp_res_tac EL_MEM >>
      gs [] >>
      drule loop_removeProofTheory.comp_prog_no_loops >> fs []
    )
    >- (
      drule pan_commonPropsTheory.lookup_some_el >> rw [] >>
      imp_res_tac EL_MEM >>
      gs [] >>
      drule_then irule loop_removeProofTheory.compile_prog_distinct_params >>
      irule crep_to_loopProofTheory.compile_prog_distinct_params >>
      fs [Abbr ‘ccode’] >>
      ho_match_mp_tac pan_to_crepProofTheory.compile_prog_distinct_params >>
      fs [Abbr ‘pcode’] >>
      ho_match_mp_tac pan_simpProofTheory.compile_prog_distinct_params >>
      fs [distinct_params_def])
  ) >>
  drule fstate_rel_imp_semantics >>
  disch_then irule >>
  fs [Abbr ‘lst’, loop_state_def,
       Abbr ‘ccode’, Abbr ‘pcode’,
       pan_to_wordTheory.compile_prog_def] >>
  fs [lookup_fromAList] >>
  irule_at Any ALOOKUP_ALL_DISTINCT_MEM >>
  irule_at Any crep_to_loopProofTheory.first_compile_prog_all_distinct >>
  fs [crep_to_loopTheory.compile_prog_def] >>
  simp [MAP2_MAP, MEM_MAP, EXISTS_PROD] >>
  csimp [MEM_ZIP, EL_GENLIST] >>
  fs [pan_to_crepTheory.compile_prog_def, pan_simpTheory.compile_prog_def] >>
  simp [EL_MAP] >>
  simp [pan_to_crepTheory.crep_vars_def, panLangTheory.size_of_shape_def]
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

Theorem call_label_eq_if:
  call_label ctxt e = (dest, indirect_dest) ==>
  indirect_dest = (if dest = NONE then [e] else [])
Proof
  simp [crep_to_loopTheory.call_label_def]
  \\ rw [CaseEq "crepLang$exp"] \\ simp []
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
     disch_then $ qspecl_then [‘ctxt.vmax + 1’,‘ns’,‘es ++ indirect_dest’] mp_tac \\
     drule_then assume_tac call_label_eq_if \\
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

Theorem every_inst_ok_less_exps_of_nested_seq:
  ∀es.
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
          (exps_of (nested_seq es)) =
    EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2))
          (FLAT (MAP exps_of es))
Proof
  Induct \\
  gvs[crepLangTheory.nested_seq_def,crepPropsTheory.exps_of_def]
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
      crepPropsTheory.exps_of_def,every_inst_ok_less_exps_of_nested_seq,
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
    rw[every_inst_ok_less_exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def])
  >~ [‘ret_hdl’] >-
   (gvs[] \\
    conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
    PURE_TOP_CASE_TAC \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[every_inst_ok_less_exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def])
  >~ [‘exp_hdl’] >-
   (gvs[] \\
    conj_tac >-
     (gvs[EVERY_MEM,PULL_FORALL] \\
      metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,EVERY_MEM,FST,SND,PAIR]) \\
    simp[DefnBase.one_line_ify NONE pan_to_crepTheory.exp_hdl_def] \\
    rpt(PURE_TOP_CASE_TAC \\ gvs[]) \\ rw[crepPropsTheory.exps_of_def,crepLangTheory.assign_ret_def] \\
    rw[every_inst_ok_less_exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
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
    rw[every_inst_ok_less_exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
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
    rw[every_inst_ok_less_exps_of_nested_seq,EVERY_FLAT,EVERY_MAP,load_globals_alt,MAP2_MAP,MEM_ZIP] \\
    gvs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,PULL_FORALL,crepPropsTheory.exps_of_def,
        crepPropsTheory.every_exp_def]) \\
  simp[every_inst_ok_nested_decs,crepPropsTheory.exps_of_def,every_inst_ok_nested_decs,crepPropsTheory.length_load_globals_eq_read_size,load_globals_alt] \\
  rw[EVERY_MEM,MAP2_MAP,MEM_ZIP,MEM_MAP,UNCURRY_DEF] \\
  gvs[UNCURRY_DEF,crepPropsTheory.exps_of_def,EVERY_MEM,MEM_EL,PULL_EXISTS,EL_MAP,
      crepPropsTheory.every_exp_def,DefnBase.one_line_ify NONE pan_to_crepTheory.ret_hdl_def] \\
  metis_tac[every_inst_ok_less_pan_to_crep_compile_exp,MEM_EL,EVERY_MEM,
            FST,SND,PAIR]
QED

Theorem every_inst_ok_less_pan_to_crep_compile_prog:
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of body)) pan_code ⇒
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Crepop op es ⇒ LENGTH es = 2)) (exps_of body)) (pan_to_crep$compile_prog pan_code)
Proof
  rw[EVERY_MEM] \\ pairarg_tac \\
  gvs[pan_to_crepTheory.compile_prog_def,MEM_MAP] \\
  pairarg_tac \\ gvs[] \\
  pairarg_tac \\ gvs[] \\
  first_x_assum drule \\
  rw[pan_to_crepTheory.comp_func_def] \\
  match_mp_tac $ MP_CANON $ Ho_Rewrite.REWRITE_RULE [EVERY_MEM,PULL_EXISTS,PULL_FORALL] every_inst_ok_less_pan_to_crep_compile \\
  metis_tac[]
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
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of body)) pan_code ⇒
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of body)) (pan_simp$compile_prog pan_code)
Proof
  rw[pan_simpTheory.compile_prog_def,EVERY_MAP] >>
  gvs[EVERY_MEM] >>
  rw[] >>
  first_x_assum dxrule >>
  pairarg_tac >>
  rw[]>>
  metis_tac[every_inst_ok_less_pan_simp_compile,EVERY_MEM]
QED

Theorem pan_to_word_every_inst_ok_less:
  pan_to_word$compile_prog c.ISA pan_code = wprog0 ∧
  byte_offset_ok c 0w ∧ addr_offset_ok c 0w ∧
  EVERY (λ(name,params,body). EVERY (every_exp (λx. ∀op es. x = Panop op es ⇒ LENGTH es = 2)) (exps_of body)) pan_code
  ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  drule_then irule loop_to_word_every_inst_ok_less>>gs[]>>
  last_x_assum kall_tac>>
  irule every_inst_ok_less_crep_to_loop_compile_prog>>
  irule every_inst_ok_less_pan_to_crep_compile_prog>>
  irule every_inst_ok_less_pan_simp_compile_prog>>
  simp []
QED
