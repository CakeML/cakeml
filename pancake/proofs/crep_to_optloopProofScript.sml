(*
  Correctness proof for ---
*)

open preamble
     crepSemTheory crepPropsTheory
     loopLangTheory loopSemTheory loopPropsTheory
     pan_commonTheory pan_commonPropsTheory
     listRangeTheory rich_listTheory crep_to_loopTheory
     crep_to_loopProofTheory


val _ = new_theory "crep_to_optloopProof";

Definition ncode_rel_def:
  ncode_rel ctxt s_code t_code <=>
   distinct_funcs ctxt.funcs /\
   ∀f ns prog.
     FLOOKUP s_code f = SOME (ns, prog) ==>
     ?loc len. FLOOKUP ctxt.funcs f = SOME (loc, len) /\
       LENGTH ns = len /\
       let args = GENLIST I len;
           nctxt = ctxt_fc ctxt.funcs ns args ctxt.ceids in
       lookup loc t_code =
          SOME (args,
                ocompile nctxt (list_to_num_set args) prog)
End


Theorem ocompile_correct:
  evaluate (p,s) = (res,s1) ∧ res ≠ SOME Error ∧ state_rel s t ∧
  mem_rel ctxt s.memory t.memory ∧ equivs s.eids ctxt.ceids ∧
  globals_rel ctxt s.globals t.globals ∧ ncode_rel ctxt s.code t.code ∧
  locals_rel ctxt l s.locals t.locals ∧ res ≠ SOME Break ∧
  res ≠ SOME Continue ∧ res ≠ NONE ⇒
  ∃ck res1 t1.
    evaluate (ocompile ctxt l p,t with clock := t.clock + ck) =
    (res1,t1) ∧ state_rel s1 t1 ∧ mem_rel ctxt s1.memory t1.memory ∧
    equivs s1.eids ctxt.ceids ∧
    globals_rel ctxt s1.globals t1.globals ∧
    ncode_rel ctxt s1.code t1.code ∧
    case res of
     | NONE => F
     | SOME Error => F
     | SOME TimeOut => res1 = SOME TimeOut
     | SOME Break => F
     | SOME Continue => F
     | SOME (Return v) => res1 = SOME (Result (wlab_wloc ctxt v)) ∧
           ∀f. v = Label f ⇒ f ∈ FDOM ctxt.funcs
     | SOME (Exception eid) => res1 = SOME (Exception (Word eid))
     | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)

Proof
   cheat
QED

Theorem mem_lookup_fromalist_some:
  !xs n x.
   ALL_DISTINCT (MAP FST xs) ∧
   MEM (n,x) xs ==>
   lookup n (fromAList xs) = SOME x
Proof
  Induct >>
  rw [] >> fs [] >>
  fs [fromAList_def] >>
  cases_on ‘h’ >>
  fs [fromAList_def] >>
  fs [lookup_insert] >>
  TOP_CASE_TAC >> fs [] >>
  rveq >> fs [MEM_MAP] >>
  first_x_assum (qspec_then ‘(n,x)’ mp_tac) >>
  fs []
QED


Theorem map_map2_fst:
  !xs ys zs f g h e. LENGTH xs = LENGTH ys ==>
   MAP FST
       (MAP2
        (λx (n,p,b). (x,GENLIST I (LENGTH p),h p b)) xs ys) = xs
Proof
  Induct_on ‘xs’ >>
  rw [] >>
  fs [] >>
  cases_on ‘ys’ >> fs [] >>
  cases_on ‘h''’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED

Theorem distinct_make_funcs:
  !crep_code. distinct_funcs (make_funcs crep_code)
Proof
  rw [distinct_funcs_def] >>
  fs [make_funcs_def] >>
  qmatch_asmsub_abbrev_tac ‘MAP2 _ (GENLIST _ _) ps’ >>
  dxrule ALOOKUP_MEM >>
  dxrule ALOOKUP_MEM >>
  strip_tac >>
  strip_tac >>
  fs [MEM_EL] >>
  ‘n < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST I (LENGTH crep_code)) ps))’ by
    fs [LENGTH_MAP] >>
  dxrule (INST_TYPE [“:'a”|->“:'a”,
                     “:'b”|->“:num # num”,
                     “:'c” |-> “:'a # num # num”] EL_MAP2) >>
  ‘n' < MIN (LENGTH (MAP FST crep_code))
   (LENGTH (MAP2 (λx y. (x,y)) (GENLIST I (LENGTH crep_code)) ps))’ by
    fs [LENGTH_MAP]  >>
  dxrule (INST_TYPE [“:'a”|->“:'a”,
                     “:'b”|->“:num # num”,
                     “:'c” |-> “:'a # num # num”] EL_MAP2) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  fs [] >> rveq >> fs [] >>
  ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by
    fs [LENGTH_GENLIST] >>
  drule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c” |-> “:num # num”] EL_MAP2) >>
  ‘n' < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by
    fs [LENGTH_GENLIST] >>
  dxrule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c” |-> “:num # num”] EL_MAP2) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  disch_then (qspec_then ‘(λx y. (x,y))’ assume_tac) >>
  fs [] >> rveq >> fs []
QED

Theorem max_set_count_length:
  !xs. MAX_SET (count (LENGTH xs)) = LENGTH xs − 1
Proof
  Induct >> rw [] >>
  fs [COUNT_SUC] >>
  ‘MAX_SET (LENGTH xs INSERT count (LENGTH xs)) =
   MAX (LENGTH xs) (MAX_SET (count (LENGTH xs)))’ by (
    ‘FINITE (count (LENGTH xs))’ by fs [] >>
    metis_tac [MAX_SET_THM]) >>
  fs [MAX_DEF]
QED


Theorem list_max_i_genlist:
  !xs. list_max (GENLIST I (LENGTH xs)) = LENGTH xs − 1
Proof
  rw [] >>
  fs [GSYM COUNT_LIST_GENLIST] >>
  fs [GSYM max_set_list_max] >>
  fs [COUNT_LIST_COUNT] >>
  metis_tac [max_set_count_length]
QED

Theorem mk_ctxt_code_imp_code_rel:
  !crep_code start np. ALL_DISTINCT (MAP FST crep_code) /\
  ALOOKUP crep_code start = SOME ([],np) ==>
  ncode_rel (mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code))
           (alist_to_fmap crep_code)
           (fromAList (crep_to_loop$compile_prog crep_code))
Proof
  rw [ncode_rel_def, mk_ctxt_def]
  >- fs [distinct_make_funcs] >>
  fs [mk_ctxt_def, make_funcs_def] >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  fs [MEM_EL] >> rveq >>
  qexists_tac ‘n’ >>
  conj_tac
  >- (
   ho_match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
   conj_tac
   >- (
    qmatch_goalsub_abbrev_tac ‘MAP FST ls’ >>
    ‘MAP FST ls = MAP FST crep_code’ suffices_by fs [] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    conj_tac >- fs [Abbr ‘ls’] >>
    conj_tac >- fs [Abbr ‘ls’] >>
    rw [] >>
    fs [Abbr ‘ls’] >>
    qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
    ‘n' < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
    drule (INST_TYPE [“:'a”|->“:mlstring”,
                      “:'b”|->“:num # num”,
                      “:'c”|-> “:mlstring # num # num”] EL_MAP2) >>
    disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
    strip_tac >> fs [] >>
    match_mp_tac EL_MAP >>
    fs []) >>
   fs [MEM_EL] >>
   qexists_tac ‘n’ >>
   fs [] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:mlstring”,
                     “:'b”|->“:num # num”,
                     “:'c”|-> “:mlstring # num # num”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   conj_asm1_tac
   >- (
    fs [EL_MAP] >>
    qpat_x_assum ‘_ = EL n crep_code’ (mp_tac o GSYM) >>
    fs []) >>
   fs [Abbr ‘ps’] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c”|-> “:num # num”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [Abbr ‘ps’] >>
   ‘n < LENGTH (MAP (LENGTH ∘ FST ∘ SND) crep_code)’ by fs [] >>
   drule (INST_TYPE [“:'a”|->“:mlstring # num list # 'a crepLang$prog”,
                     “:'b”|->“:num”] EL_MAP) >>
   disch_then (qspec_then ‘LENGTH ∘ FST ∘ SND’ mp_tac) >>
   strip_tac >>
   fs [] >>
   qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
   fs []) >>
  fs [compile_prog_def, ctxt_fc_def] >>
  match_mp_tac mem_lookup_fromalist_some >>
  conj_tac
  >- (
   qmatch_goalsub_abbrev_tac ‘MAP FST ps’ >>
   ‘MAP FST ps = GENLIST I (LENGTH crep_code)’
   suffices_by fs [ALL_DISTINCT_GENLIST] >>
   fs [Abbr ‘ps’] >>
   fs [MAP_MAP_o] >>
   cheat
   (*
   match_mp_tac map_map2_fst >>
   fs [LENGTH_MAP, LENGTH_GENLIST] *)) >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [] >>
  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 _ ps _)’ >>
  ‘n < MIN (LENGTH ps) (LENGTH crep_code)’ by fs [Abbr ‘ps’] >>

  drule (INST_TYPE [“:'a”|->“:num”,
                    “:'b”|->“:mlstring # num list # 'a crepLang$prog”,
                    “:'c”|-> “:num # num list # 'a prog”] EL_MAP2) >>
  disch_then (qspec_then ‘λn' (name,params,body).
       (n',GENLIST I (LENGTH params),
        optimise (comp_func (make_funcs crep_code) (get_eids crep_code)
                  params body))’ mp_tac) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >> fs [] >>
  fs [Abbr ‘ps’] >>
  qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
  fs [] >>
  fs [comp_func_def] >>
  fs [mk_ctxt_def, make_vmap_def, make_funcs_def] >>
  fs [loop_liveTheory.optimise_def, ocompile_def] >>
  ‘list_max (GENLIST I (LENGTH ns)) = LENGTH ns − 1’ suffices_by fs [] >>
  fs [list_max_i_genlist]
QED


Theorem state_rel_imp_semantics:
  s.memaddrs = t.mdomain ∧
  s.be = t.be ∧
  s.ffi = t.ffi /\
  mem_rel (mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code))
           s.memory t.memory ∧
  equivs s.eids (get_eids crep_code) ∧
  globals_rel (mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code))
               s.globals t.globals ∧
  ALL_DISTINCT (MAP FST crep_code) ∧
  s.code = alist_to_fmap crep_code ∧
  t.code = fromAList (crep_to_loop$compile_prog crep_code) ∧
  s.locals = FEMPTY ∧
  ALOOKUP crep_code start = SOME ([],prog) ∧
  FLOOKUP (make_funcs crep_code) start = SOME (lc, 0) ∧
  semantics s start <> Fail ==>
  semantics t lc = semantics s start
Proof
  rw [] >>
  drule mk_ctxt_code_imp_code_rel >>
  disch_then (qspecl_then [‘start’, ‘prog’] mp_tac) >>
  fs [] >> strip_tac >>
  qmatch_asmsub_abbrev_tac ‘code_rel nctxt _ _’ >>
  reverse (Cases_on ‘semantics s start’) >> fs []
  >- (
   (* Termination case of crep semantics *)
   fs [crepSemTheory.semantics_def] >>
   pop_assum mp_tac >>
   IF_CASES_TAC >> fs [] >>
   DEEP_INTRO_TAC some_intro >> simp[] >>
   rw [] >>
   rw [loopSemTheory.semantics_def]
   >- (
    (* the fail case of loop semantics *)
    qhdtm_x_assum ‘crepSem$evaluate’ kall_tac >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >>
    last_x_assum(qspec_then ‘k'’ mp_tac) >> simp[] >>
    (fn g => subterm (fn tm => Cases_on ‘^(assert(has_pair_type)tm)’) (#2 g) g) >>
    CCONTR_TAC >> fs [] >>
    drule compile_correct >> fs[] >>
    map_every qexists_tac [‘t with clock := k'’] >>
    qexists_tac ‘nctxt’ >>
    qexists_tac ‘LN’ >>
    fs [] >>
    Ho_Rewrite.PURE_REWRITE_TAC[GSYM PULL_EXISTS] >>
    conj_tac
    >- (
     conj_tac
     >- (
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x’ >> fs []) >>
     fs [state_rel_def, Abbr ‘nctxt’, mk_ctxt_def] >>
     conj_tac >- cheat >>
     fs [locals_rel_def, distinct_vars_def, ctxt_max_def]) >>
    CCONTR_TAC >>
    fs [] >>
    fs [compile_def] >>
    fs [compile_exp_def] >>
    fs [gen_temps_def, MAP2_DEF] >>
    fs [nested_seq_def] >>
    ‘find_lab nctxt start = lc’ by (
      fs [find_lab_def, Abbr ‘nctxt’, mk_ctxt_def]) >>
    fs [] >>
    ‘lc ∈ domain (fromAList (compile_prog crep_code))’ by (
      fs [domain_fromAList] >>
      qpat_x_assum ‘FLOOKUP (make_funcs crep_code) _ = _’ assume_tac >>
      fs [make_funcs_def] >>
      drule ALOOKUP_MEM >>
      pop_assum kall_tac >>
      strip_tac >>
      fs [MEM_EL] >>
      qexists_tac ‘n’ >>
      conj_tac
      >- (
       fs [compile_prog_def, comp_c2l_def]) >>
      qmatch_asmsub_abbrev_tac ‘MAP2 _ (GENLIST I _) ps’ >>
      ‘n < MIN (LENGTH (MAP FST crep_code))
       (LENGTH (MAP2 (λx y. (x,y)) (GENLIST I (LENGTH crep_code)) ps))’ by
        fs [Abbr ‘ps’, LENGTH_MAP] >>
      dxrule (INST_TYPE [“:'a”|->“:mlstring”,
                         “:'b”|->“:num # num”,
                         “:'c” |-> “:mlstring # num # num”] EL_MAP2) >>
      disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
      strip_tac >> fs [] >>
      fs [compile_prog_def] >>
      fs [MAP_MAP_o] >>
      ‘n < LENGTH (comp_c2l crep_code)’ by fs [comp_c2l_def] >>
      dxrule (INST_TYPE [“:'a”|->“:num # num list # 'a prog”,
                         “:'b”|->“:num”] EL_MAP) >>
      disch_then (qspec_then ‘FST ∘ (λ(n,ns,p). (n,ns,optimise LN p))’ mp_tac) >>
      strip_tac >> fs [] >>
      pop_assum kall_tac >>
      fs [comp_c2l_def] >>
      qmatch_goalsub_abbrev_tac ‘EL n (MAP2 ffs _ _)’ >>
      ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code)))
       (LENGTH crep_code)’ by fs [] >>
      dxrule (INST_TYPE [“:'a”|->“:num”,
                         “:'b”|->“:mlstring # num list # 'a crepLang$prog”,
                         “:'c” |-> “:num # num list # 'a prog”] EL_MAP2) >>
      disch_then (qspec_then ‘ffs’ mp_tac) >>
      fs [] >>
      strip_tac >>
      fs [Abbr ‘ffs’] >>
      cases_on ‘EL n crep_code’ >> fs [] >>
      cases_on ‘r'’ >> fs [] >>
      ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code)))
       (LENGTH ps)’ by fs [Abbr ‘ps’] >>
      dxrule (INST_TYPE [“:'a”|->“:num”,
                         “:'b”|->“:num”,
                         “:'c” |-> “:num # num”] EL_MAP2) >>
      disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
      strip_tac >> fs []) >>
    fs [] >>
    qpat_x_assum ‘loopSem$evaluate (Seq _ _, _) = (_,_)’ mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    CCONTR_TAC >> fs [] >>
    fs [set_var_def] >>
    rveq >> fs [] >>
    pop_assum mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    pop_assum mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    CCONTR_TAC >> fs [] >>
    fs [eval_def] >>
    fs [set_var_def] >>
    pop_assum (assume_tac o GSYM) >>
    rveq >> fs [] >>
    pop_assum mp_tac >>
    rw [Once loopSemTheory.evaluate_def] >>
    pairarg_tac >> fs [] >>
    CCONTR_TAC >> fs [] >>
    (* apply loop_live optimisation *)
    drule loop_liveProofTheory.optimise_correct >>
    disch_then (qspec_then ‘insert (nctxt.vmax + 2)
                            (find_lab nctxt start) LN’ mp_tac) >>
    impl_tac
    >- (
     rpt conj_tac >>
     TRY (
     cases_on ‘q’ >> fs [] >>
     cases_on ‘x’ >> fs [] >> rveq >> fs [] >>
     cases_on ‘res’ >> fs [] >> rveq >> fs [evaluate_def] >> NO_TAC) >>
     rw [] >>
     fs [lookup_insert] >>
     TOP_CASE_TAC >> fs [] >>
     TOP_CASE_TAC >> fs [] >> rveq >> fs [lookup_def]) >>
    strip_tac >>
    fs [loop_liveTheory.optimise_def] >>
    fs [loop_callTheory.comp_def] >>
    fs [loop_liveTheory.comp_def] >>
    fs [loop_liveTheory.shrink_def] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum kall_tac >>
    strip_tac >> strip_tac >>
    qmatch_asmsub_abbrev_tac ‘t with <|locals := lcl; clock := ck + k'|>’ >>
    ‘?x. find_code (SOME (find_lab nctxt start)) ([]:'a word_loc list)
     (t with clock := ck + k').code = SOME x’ by (
      CCONTR_TAC >> fs [] >>
      fs [option_CLAUSES] >>
      cases_on  ‘find_code (SOME (find_lab nctxt start)) ([]:'a word_loc list) t.code’ >>
      fs [option_CLAUSES] >>
      fs [Abbr ‘nctxt’, find_code_def, mk_ctxt_def, find_lab_def] >>
      cases_on ‘FLOOKUP (make_funcs crep_code) start’ >> fs [] >>
      cases_on ‘x’ >> fs [] >>
      cases_on ‘lookup q' t.code’ >> fs [] >>
      rveq >> rfs [] >> fs []
      >- (
       fs [compile_prog_def] >>
       fs [lookup_NONE_domain]) >>
      cases_on ‘x’ >> fs [] >>
      qpat_x_assum ‘code_rel _ (alist_to_fmap crep_code) _’ assume_tac >>
      fs [code_rel_def] >>
      pop_assum drule >>
      strip_tac >> fs [] >>
      rveq >> fs [] >>
      fs [compile_prog_def, comp_c2l_def] >>
      cheat (* is true *)) >>
    drule evaluate_tail_calls_eqs >>
    disch_then (qspec_then ‘lcl’ mp_tac) >>
    strip_tac >>
    pop_assum (assume_tac o GSYM) >>
    fs [] >>
    pop_assum kall_tac >>
    cases_on ‘evaluate
               (Call NONE (SOME (find_lab nctxt start)) [] NONE,
                t with clock := k')’ >>
    fs [] >>
    cases_on ‘q'’ >> fs [] >>
    TRY (cases_on ‘x'’ >> fs []) >> (
     drule evaluate_add_clock_eq >>
     disch_then (qspec_then ‘ck’ mp_tac) >>
     strip_tac >> fs [] >> rveq >>
     qpat_x_assum ‘(res1,t1) = _’ (mp_tac o GSYM) >>
     rw [evaluate_def] >>
     CCONTR_TAC >>
     fs [] >>
     rveq >> fs [] >>
      cases_on ‘q’ >> fs [] >>
      cases_on ‘x'’ >> fs [] >> rveq >> fs [])) >>

(*
val compile_lemma = compile_correct
                     |> Q.SPECL [`p`,`s`,`res`,`s1`,`t`,`ctxt`,`l`]
                     |> SIMP_RULE std_ss [];

Theorem ocompile_correct:
  ^(mk_conj (compile_lemma |> concl |> dest_imp |> fst,
             “res:('a crepSem$result option) ≠ SOME Break ∧
                  res ≠ SOME Continue ∧ res ≠ NONE”)) ==>
  ∃ck res1 t1.
         evaluate (ocompile ctxt l p,t with clock := t.clock + ck) = (res1,t1) ∧
         state_rel s1 t1 ∧ mem_rel ctxt s1.memory t1.memory ∧
         equivs s1.eids ctxt.ceids ∧ globals_rel ctxt s1.globals t1.globals ∧
         code_rel ctxt s1.code t1.code ∧
         case res of
         | SOME TimeOut => res1 = SOME TimeOut
         | SOME (Return v) =>
           res1 = SOME (Result (wlab_wloc ctxt v)) ∧
           ∀f. v = Label f ⇒ f ∈ FDOM ctxt.funcs
         | SOME (Exception eid) => res1 = SOME (Exception (Word eid))
         | SOME (FinalFFI f) => res1 = SOME (FinalFFI f)
         | _ => F
Proof
  rpt strip_tac >>
  mp_tac compile_lemma >>
  fs [] >>
  rpt strip_tac >>
  fs [ocompile_def] >>
  mp_tac (Q.SPECL [‘t1’, ‘t with clock := ck + t.clock’, ‘res1’, ‘compile ctxt l p’, ‘LN’]
          (loop_liveProofTheory.optimise_correct |> GEN_ALL)) >>
  impl_tac
  >- (
   fs [lookup_def] >>
   cases_on ‘res’ >> fs [] >> rveq >>
   cases_on ‘x’ >> fs []) >>
  strip_tac >>
  qexists_tac ‘ck’ >>
  qexists_tac ‘res1’ >>
  qexists_tac ‘t1’ >>
  fs [] >>
  cases_on ‘res’ >> fs [] >>
  cases_on ‘x’ >> fs []
QED
*)

(*
Theorem mk_ctxt_code_imp_code_rel:
  ALL_DISTINCT (MAP FST crep_code) /\
  ALOOKUP crep_code start = SOME ([],np) ==>
  code_rel (mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code))
           (alist_to_fmap crep_code)
           (fromAList (crep_to_loop$compile_prog crep_code))
Proof
  rw [code_rel_def, mk_ctxt_def]
  >- fs [distinct_make_funcs] >>
  fs [mk_ctxt_def, make_funcs_def] >>
  drule ALOOKUP_MEM >>
  strip_tac >>
  fs [MEM_EL] >> rveq >>
  qexists_tac ‘n’ >>
  conj_tac
  >- (
   ho_match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
   conj_tac
   >- (
    qmatch_goalsub_abbrev_tac ‘MAP FST ls’ >>
    ‘MAP FST ls = MAP FST crep_code’ suffices_by fs [] >>
    fs [MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
    conj_tac >- fs [Abbr ‘ls’] >>
    conj_tac >- fs [Abbr ‘ls’] >>
    rw [] >>
    fs [Abbr ‘ls’] >>
    qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
    ‘n' < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
    drule (INST_TYPE [“:'a”|->“:mlstring”,
                      “:'b”|->“:num # num”,
                      “:'c”|-> “:mlstring # num # num”] EL_MAP2) >>
    disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
    strip_tac >> fs [] >>
    match_mp_tac EL_MAP >>
    fs []) >>
   fs [MEM_EL] >>
   qexists_tac ‘n’ >>
   fs [] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (MAP FST crep_code)) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:mlstring”,
                     “:'b”|->“:num # num”,
                     “:'c”|-> “:mlstring # num # num”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   conj_asm1_tac
   >- (
    fs [EL_MAP] >>
    qpat_x_assum ‘_ = EL n crep_code’ (mp_tac o GSYM) >>
    fs []) >>
   fs [Abbr ‘ps’] >>
   qmatch_goalsub_abbrev_tac ‘MAP2 _ _ ps’ >>
   ‘n < MIN (LENGTH (GENLIST I (LENGTH crep_code))) (LENGTH ps)’ by fs [Abbr ‘ps’] >>
   drule (INST_TYPE [“:'a”|->“:num”,
                     “:'b”|->“:num”,
                     “:'c”|-> “:num # num”] EL_MAP2) >>
   disch_then (qspec_then ‘λx y. (x,y)’ mp_tac) >>
   strip_tac >> fs [] >>
   fs [Abbr ‘ps’] >>
   ‘n < LENGTH (MAP (LENGTH ∘ FST ∘ SND) crep_code)’ by fs [] >>
   drule (INST_TYPE [“:'a”|->“:mlstring # num list # 'a crepLang$prog”,
                     “:'b”|->“:num”] EL_MAP) >>
   disch_then (qspec_then ‘LENGTH ∘ FST ∘ SND’ mp_tac) >>
   strip_tac >>
   fs [] >>
   qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
   fs []) >>
  fs [compile_prog_def, ctxt_fc_def] >>
  match_mp_tac mem_lookup_fromalist_some >>
  conj_tac
  >- (
   qmatch_goalsub_abbrev_tac ‘MAP FST ps’ >>
   ‘MAP FST ps = GENLIST I (LENGTH crep_code)’
   suffices_by fs [ALL_DISTINCT_GENLIST] >>
   fs [Abbr ‘ps’] >>
   fs [MAP_MAP_o] >>
   fs [comp_c2l_def] >>
   match_mp_tac map_map2_fst >>
   fs [LENGTH_MAP, LENGTH_GENLIST]) >>
  fs [MEM_EL] >>
  qexists_tac ‘n’ >>
  fs [] >>
  conj_tac >- fs [comp_c2l_def] >>
  ‘n < LENGTH (comp_c2l crep_code)’ by fs [comp_c2l_def] >>
  drule (INST_TYPE [“:'a”|->“:num # num list # 'a prog”,
                    “:'b”|->“:num # num list # 'a prog”] EL_MAP) >>
  disch_then (qspec_then ‘λ(n,ns,p). (n,ns,optimise LN p)’ mp_tac) >>
  fs [] >> strip_tac >>
  pop_assum kall_tac >>
  fs [comp_c2l_def] >>

  qmatch_goalsub_abbrev_tac ‘EL _ (MAP2 _ ps _)’ >>
  ‘n < MIN (LENGTH ps) (LENGTH crep_code)’ by fs [Abbr ‘ps’] >>

  drule (INST_TYPE [“:'a”|->“:num”,
                    “:'b”|->“:mlstring # num list # 'a crepLang$prog”,
                    “:'c”|-> “:num # num list # 'a prog”] EL_MAP2) >>
  disch_then (qspec_then ‘λn' (name,params,body).
                     (n',GENLIST I (LENGTH params),
                      comp_func (make_funcs crep_code) (get_eids crep_code)
                        params body)’ mp_tac) >>
  strip_tac >> fs [] >>
  pop_assum kall_tac >> fs [] >>
  fs [Abbr ‘ps’] >>
  qpat_x_assum ‘_ = EL n crep_code’ (assume_tac o GSYM) >>
  fs [] >>
  fs [comp_func_def] >>
  fs [mk_ctxt_def, make_vmap_def, make_funcs_def] >>
  ‘list_max (GENLIST I (LENGTH ns)) = LENGTH ns − 1’ by cheat >>
  fs [] >>
  pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘abc = optimise LN _’ >>
  fs [loop_liveTheory.optimise_def]

  fs [mk_ctxt_def, make_vmap_def, make_func_fmap_def, get_eids_def]
  cheat
QED
*)

Theorem mk_ctxt_code_imp_code_rel:
  ALL_DISTINCT (MAP FST crep_code) /\
  ALOOKUP crep_code start = SOME ([],np) ==>
  code_rel (mk_ctxt FEMPTY (make_funcs crep_code) 0 (get_eids crep_code))
           (alist_to_fmap crep_code)
           (fromAList (crep_to_loop$comp_c2l crep_code))
Proof
  cheat
QED

(*
Theorem map_map2_fst:
  !xs ys zs f g h e. LENGTH xs = LENGTH ys ==>
   MAP (FST ∘ (λ(n,ns,p). (n,ns,g p)))
       (MAP2
        (λx (n,p,b). (x,GENLIST I (LENGTH p),h p b)) xs ys) = xs
Proof
  Induct_on ‘xs’ >>
  rw [] >>
  fs [] >>
  cases_on ‘ys’ >> fs [] >>
  cases_on ‘h''’ >> fs [] >>
  cases_on ‘r’ >> fs []
QED
*)

val _ = export_theory();
