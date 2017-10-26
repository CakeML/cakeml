open preamble permLib;

val _ = new_theory "synchLang"

val _ = Hol_datatype `
 msg_type = M_string | M_int`

(* session =  'principal * 'principal * msg_type  *)

val _ = Hol_datatype `
 action = Send | Receive`

val add_def =
 Define `add s l = (if MEM s l then l else s::l)`

val endpoints_def = Define `
 (endpoints [] = []) /\
 (endpoints ((s,r,_)::l) = add s (add r (endpoints l)))`

val endpoints_ind = fetch "-" "endpoints_ind"

val ALL_DISTINCT_add = Q.store_thm("ALL_DISTINCT_add",
  `!s l. ALL_DISTINCT(add s l) = ALL_DISTINCT l`,
  rw[add_def])

val NOT_MEM_FILTER = Q.store_thm("NOT_MEM_FILTER",
  `!l e. ¬MEM e l ==> (FILTER ($= e) l = [])`,
  rw[FILTER_EQ_NIL,EVERY_MEM]);

val TL_append = Q.prove(`!l l'. l ≠ [] ==> (TL(l ++ l') = TL l ++ l')`,
  Cases_on `l` >> rw[]);

val MEM_add = Q.store_thm("MEM_add",
  `!s l. MEM r (add s l) = ((r = s) \/ MEM r l)`,
  rw[add_def,EQ_IMP_THM] >> pop_assum ACCEPT_TAC)

val ALL_DISTINCT_endpoints = Q.store_thm("ALL_DISTINCT_endpoints",
  `!l. ALL_DISTINCT(endpoints l)`,
  recInduct endpoints_ind >> rw[ALL_DISTINCT_add,endpoints_def])

val project_def = Define
  `(project p [] = []) /\
   (project p ((s,r,t)::l) =
    (if p = s then
       (Send,r,t)::project p l
     else if p = r then
       (Receive,s,t)::project p l
     else
       project p l))`

val project_ind = fetch "-" "project_ind"

val compile_def = Define
  `compile c = MAP (λe. (e, project e c)) (endpoints c)`

val (trans_rules,trans_ind,trans_cases) = Hol_reln `
(!s r l m.
    trans [(s,(Send,r,m)::l)] (SOME(Send,s,r,m)) [(s,l)])
/\ (!s r l m.
    trans [(r,(Receive,s,m)::l)] (SOME(Receive,s,r,m)) [(r,l)])
/\ (!s r m p p' q q'.
    trans p (SOME(Send,s,r,m)) p' /\ trans q (SOME(Receive,s,r,m)) q'
    ==> trans (p++q) (NONE) (p'++q'))
/\ (!s r m p p' q q'.
    trans p (SOME(Receive,s,r,m)) p' /\ trans q (SOME(Send,s,r,m)) q'
    ==> trans (p++q) (NONE) (p'++q'))
/\ (!a p p' q.
    trans p a p' ==> trans (p++q) a (p'++q))
/\ (!a p q q'.
    trans q a q' ==> trans (p++q) a (p++q'))
`

val [trans_send,trans_receive,trans_comm1,trans_comm2,trans_par1,trans_par2] =
    BODY_CONJUNCTS trans_rules |> map GEN_ALL
    |> zip ["trans_send","trans_receive","trans_comm1",
            "trans_comm2","trans_par1","trans_par2"]
    |> map save_thm


val reduction_def = Define `reduction p q = trans p NONE q`

val reduces_def = Define `reduces p = ?p'. reduction p p'`

val transitions_def = Define `transitions p = ?a p'. trans p a p'`

val deadlocked_def = Define `deadlocked p = transitions p /\ ~reduces p`

val not_trans_cons = Q.store_thm("not_trans_cons",
  `(∀a p'. ¬trans((p,ev::l)::sys) a p') = F`,
  fs[] >> PURE_REWRITE_TAC [Once (CONS_APPEND)]
  >> `∃a p'. trans ([(p,ev::l)]) a p'`
     by(Cases_on `ev` >> Cases_on `q` >> Cases_on `r`    
        >> PURE_ONCE_REWRITE_TAC [trans_cases] >> fs[] >> metis_tac[])
  >> imp_res_tac trans_rules >> metis_tac[])

val nil_trans_empty = Q.store_thm("nil_trans_empty",
  `!p a p'. trans p a p' ==> p ≠ []`,
  ho_match_mp_tac trans_ind >> rw[]);

val nil_trans_eq = Q.store_thm("nil_trans_eq",
  `!a p'. trans [] a p' = F`,
  rw[EQ_IMP_THM] >> strip_tac >> imp_res_tac nil_trans_empty >> rw[]);

val nil_transitions = Q.store_thm("nil_transitions",
  `transitions [] = F`,
  rw[transitions_def,nil_trans_eq]);

val nil_nil_trans = Q.store_thm("nil_nil_trans",
  `!p a p'. trans p a p' ==> (?q s. (p = (s,[])::q)) ==> (p' ≠ [] /\ (HD p' = HD p) /\ trans (TL p) a (TL p'))`,
  ho_match_mp_tac (fetch "-" "trans_strongind") >> rpt strip_tac
  >> fs[APPEND_EQ_CONS] >> rveq >> fs[nil_trans_eq]
  >> TRY(fs[GSYM quantHeuristicsTheory.HD_TL_EQ_THMS]
         >> qpat_x_assum `_::_ = _` (fn thm => rw[Once(GSYM thm)]))
  >> imp_res_tac trans_rules >> fs[]);

val nil_nil_trans_eq = Q.store_thm("nil_nil_trans_eq",
  `trans ((p,[])::l) a p' = (p' ≠ [] /\ (HD p' = (p,[])) /\ trans l a (TL p'))`,
  reverse(rw[EQ_IMP_THM])
  >- (fs[GSYM quantHeuristicsTheory.HD_TL_EQ_THMS]
      >> qpat_x_assum `_::_ = _` (fn thm => rw[Once(GSYM thm)])
      >> PURE_ONCE_REWRITE_TAC [CONS_APPEND]
      >> imp_res_tac trans_rules >> metis_tac[])
  >> imp_res_tac nil_nil_trans >> fs[]);

val cons_nil_transitions_eq = Q.store_thm("cons_nil_transitions_eq",
  `transitions((p,[])::l) = transitions l`,
  rw[transitions_def,nil_nil_trans_eq] >> rw[EQ_IMP_THM]
  >- (fs[GSYM quantHeuristicsTheory.HD_TL_EQ_THMS]
      >> qpat_x_assum `_::_ = _` (fn thm => rw[Once(GSYM thm)])
      >> metis_tac [])
  >> qexists_tac `a` >> qexists_tac `(p,[])::p'` >> fs[]);

val cons_cons_transitions_eq = Q.store_thm("cons_cons_transitions_eq",
  `transitions((p,ev::l)::sys)`,
  CCONTR_TAC >> fs[transitions_def] >> imp_res_tac not_trans_cons);

val transitions_eq = Q.store_thm("transitions_eq",
  `!l. transitions l = (EXISTS ($≠ [] o SND) l)`,
  Induct
  >- fs[nil_transitions]
  >> Cases >> Cases_on `r`
   >- fs[cons_nil_transitions_eq]
   >- fs[cons_cons_transitions_eq]);

val wf_chor_def = Define
  `(wf_chor c = EVERY (λ(a,b,c). a ≠ b) c)`

val wf_chor_APPEND_IMP = Q.store_thm("wf_chor_APPEND_IMP",
  `wf_chor(c++c') ==> (wf_chor c /\ wf_chor c')`,
  fs[wf_chor_def])
                                    
val sender_sends = Q.store_thm("sender_sends",
  `MEM (s,(Send,r,m)::evs) l ==> ?l'. trans l (SOME(Send,s,r,m)) l'`,
  Induct_on `l` >> rpt strip_tac >> fs[]
  >- (qpat_x_assum `_ = _` (assume_tac o GSYM)
      >> fs[] >> qexists_tac `(s,evs)::l`
      >> PURE_ONCE_REWRITE_TAC [CONS_APPEND]
      >> metis_tac[trans_rules])
  >> first_x_assum drule
  >> rpt strip_tac
  >> qexists_tac `h::l'` >> PURE_ONCE_REWRITE_TAC [CONS_APPEND]
  >> metis_tac[trans_rules]);

val sends_sender = Q.store_thm("sends_sender",
  `!l a l'. trans l a l' ==> (!s r m. (a = SOME(Send,s,r,m)) ==> ?evs. MEM (s,(Send,r,m)::evs) l)`,
  ho_match_mp_tac (fetch "-" "trans_strongind") >> rpt strip_tac
  >> fs[] >> metis_tac[]);

val sends_sender = Q.store_thm("sends_sender",
  `!l a l'. trans l a l' ==> (!s r m. (a = SOME(Send,s,r,m)) ==> ?evs ll lr. (l = ll ++ (s,(Send,r,m)::evs)::lr) /\ (l' = ll ++ (s,evs)::lr))`,
  ho_match_mp_tac (fetch "-" "trans_strongind") >> rpt strip_tac
  >> fs[]
  >- (CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `[]` >> fs[])
  >- (PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >> metis_tac[])
  >- metis_tac[]);

val receiver_receives = Q.store_thm("receiver_receives",
  `MEM (r,(Receive,s,m)::evs) l ==> ?l'. trans l (SOME(Receive,s,r,m)) l'`,
  Induct_on `l` >> rpt strip_tac >> fs[]
  >- (qpat_x_assum `_ = _` (assume_tac o GSYM)
      >> fs[] >> qexists_tac `(r,evs)::l`
      >> PURE_ONCE_REWRITE_TAC [CONS_APPEND]
      >> metis_tac[trans_rules])
  >> first_x_assum drule
  >> rpt strip_tac
  >> qexists_tac `h::l'` >> PURE_ONCE_REWRITE_TAC [CONS_APPEND]
  >> metis_tac[trans_rules]);

val receives_receiver = Q.store_thm("receives_receiver",
  `!l a l'. trans l a l' ==>
            (!s r m. (a = SOME(Receive,s,r,m))
                      ==> ?evs ll lr. (l = ll ++ (r,(Receive,s,m)::evs)::lr) /\
                                           (l' = ll ++ (r,evs)::lr))`,
  ho_match_mp_tac (fetch "-" "trans_strongind") >> rpt strip_tac
  >> fs[] >> rveq
  >- (* Receive *)
     (CONV_TAC SWAP_EXISTS_CONV >> qexists_tac `[]` >> fs[])
  >- (* Par1 *)
     (PURE_REWRITE_TAC [GSYM APPEND_ASSOC] >> metis_tac[])
     (* Par2 *)
  >- metis_tac[]);

val sender_receiver_reduces = Q.store_thm("sender_receiver_reduces",
  `MEM (s,(Send,r,m)::evs) l /\ MEM (r,(Receive,s,m)::evs') l ==> reduces l`,
  Induct_on `l` >> rpt strip_tac
  >> fs[] >> rveq >> fs[reduces_def,reduction_def]
  >> imp_res_tac receiver_receives
  >> imp_res_tac sender_sends
  >> PURE_ONCE_REWRITE_TAC [CONS_APPEND]
  >> metis_tac[trans_rules]);

val compile_not_deadlocked = Q.store_thm("compile_not_deadlocked",
  `!c. wf_chor c ==> (deadlocked(compile c) = F)`,
  `!c. wf_chor c /\ deadlocked(compile c) ==> F` suffices_by metis_tac[]
  >> Induct
  >- fs[compile_def,endpoints_def,deadlocked_def,nil_transitions]
  >> Cases >> Cases_on `r` >> rpt strip_tac
  >> fs[project_def,endpoints_def,compile_def,deadlocked_def,wf_chor_def]
  >> qpat_x_assum `¬reduces _` mp_tac >> fs[]
  >> match_mp_tac (GEN_ALL sender_receiver_reduces)
  >> fs[MEM_MAP,MEM_add]
  >> rename1 `(Send,r,_)` >> rename1 `(Receive,s,_)`
  >> qexists_tac `s` >> qexists_tac `r` >> fs[]);

val reduces_sender_receiver = Q.store_thm("reduces_sender_receiver",
  `!l a l'. trans l a l'
            ==> (a = NONE)
            ==> (?s r m evs evs' ll lc lr.
                   (((l = ll ++ [(r,(Receive,s,m)::evs)] ++ lc ++ [(s,(Send,r,m)::evs')] ++ lr)
                     /\ (l' = ll ++ [(r,evs)] ++ lc ++ [(s,evs')] ++ lr) \/
                     (l = ll ++ [(s,(Send,r,m)::evs')] ++ lc ++ [(r,(Receive,s,m)::evs)] ++ lr)
                     /\ (l' = ll ++ [(s,evs')] ++ lc ++ [(r,evs)] ++ lr))))`,
  ho_match_mp_tac (fetch "-" "trans_strongind") >> rpt strip_tac
  >> fs[] >> imp_res_tac receives_receiver >> imp_res_tac sends_sender
  >> fs[] >> rveq
  >> metis_tac[APPEND_ASSOC]);

val clean_terminated_def = Define `
    clean_terminated l = FILTER (λ(a,b). b ≠ []) l`

val ALL_DISTINCT_FST_FILTER_IMP = Q.prove(
  `!l. ALL_DISTINCT(MAP FST l) ==> (∀q r. MEM (q,r) l ⇒ (FILTER ($= q o FST) l = [(q,r)]))`,
  Induct >- fs[]
  >> Cases >> rpt strip_tac >> fs[EQ_IMP_THM] >> rpt strip_tac >> fs[FILTER_EQ_NIL,EVERY_MEM,MEM_MAP]
  >> rpt strip_tac >> fs[] >> rveq >> rw[]
  >> fs[GSYM (CONV_RULE(DEPTH_CONV (REWRITE_CONV [Once DISJ_COMM])) IMP_DISJ_THM)]
  >> first_x_assum drule >> fs[])
                                         
val NOT_MEM_FILTER_FST = Q.prove(
  `!l q. ¬MEM q (MAP FST l) ==> (FILTER ($= q o FST) l = [])`,
  Induct >- fs[]
  >> Cases >> rpt strip_tac >> fs[])
                                         
val ALL_DISTINCT_PERM_FILTER = Q.prove(
 `!l l' s. ALL_DISTINCT l /\ ALL_DISTINCT (MAP FST l) /\ PERM l l' ==> (FILTER ($= s o FST) l = (FILTER ($= s o FST) l'))`,
  rpt strip_tac
  >> drule (ISPEC ``FST`` PERM_MAP) >> strip_tac
  >> imp_res_tac ALL_DISTINCT_PERM
  >> imp_res_tac ALL_DISTINCT_FST_FILTER_IMP
  >> Cases_on `MEM s (MAP FST l)`
  >- (fs[MEM_MAP] >> rename [`$= (FST tup)`] >> Cases_on `tup`
      >> fs[] >> imp_res_tac MEM_PERM
      >> rpt(first_x_assum drule) >> fs[])
  >> `¬MEM s (MAP FST l')` by(imp_res_tac MEM_PERM >> fs[])
  >> imp_res_tac NOT_MEM_FILTER
  >> fs[FILTER_MAP]);

val compile_rcv_evs_lemma = Q.prove(
  `wf_chor c /\ s ≠ r ==> ?evs. (FILTER ($= r o FST) (compile((s,r,m)::c)) = [(r,(Receive,s,m)::evs)])`,
  qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_endpoints
  >> rpt strip_tac
  >> fs[compile_def,endpoints_def,add_def,FILTER_MAP,o_DEF]
  >> rw[] >> fs[ALL_DISTINCT_FILTER,project_def,FILTER_EQ_NIL,EVERY_MEM]
  >> metis_tac[])

val project_nonmem_nil = Q.store_thm("project_nonmem_nil",
  `!c r. (¬MEM r (endpoints c) ==> (project r c = []))`,
  simp[compile_def]
  >> ho_match_mp_tac endpoints_ind >> rpt strip_tac
  >> fs[endpoints_def,project_def,MEM_add]);

val nonmem_nil_project = Q.store_thm("project_nonmem_nil",
  `!c r. (project r c = []) ==> ¬MEM r (endpoints c)`,
  simp[compile_def]
  >> ho_match_mp_tac endpoints_ind >> rpt strip_tac
  >> fs[endpoints_def,project_def,MEM_add] >> rveq >> fs[]
  >> every_case_tac >> fs[] >> metis_tac[]);
                                   
val compile_snd_evs_lemma = Q.prove(
`wf_chor c /\ s ≠ r ==> (FILTER ($= s o FST) (compile((s,r,m)::c)) =
                         [(s,(Send,r,m)::
                             case FILTER ($= s o FST) (compile c) of [] => []
                                | l => SND(HD(l)))])`,
  qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_endpoints
  >> rpt strip_tac
  >> fs[compile_def,endpoints_def,add_def,FILTER_MAP,o_DEF]
  >> rw[] >> fs[ALL_DISTINCT_FILTER,project_def,FILTER_EQ_NIL,EVERY_MEM]
  >> first_x_assum(qspec_then `s` mp_tac) >> rw[]
  >> fs[ISPEC ``$= s`` ETA_THM]
  >> imp_res_tac project_nonmem_nil >> fs[]);

val compile_neither_evs_lemma = Q.prove(
`wf_chor c /\ s ≠ r /\ s ≠ x /\ r ≠ x ==> (FILTER ($= x o FST) (compile((s,r,m)::c)) =
                         FILTER ($= x o FST) (compile c))`,
  qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_endpoints
  >> rpt strip_tac
  >> fs[compile_def,endpoints_def,add_def,FILTER_MAP,o_DEF]
  >> rw[] >> fs[ALL_DISTINCT_FILTER,project_def,FILTER_EQ_NIL,EVERY_MEM]
  >> first_x_assum(qspec_then `x` mp_tac) >> rw[]
  >> fs[ISPEC ``$= x`` ETA_THM]
  >> imp_res_tac project_nonmem_nil >> fs[]
  >> Cases_on `MEM x (endpoints c)`
  >> fs[NOT_MEM_FILTER]);

val compile_snd_evs_lemma' = Q.prove(
`wf_chor c /\ s ≠ r ==> (FLAT(MAP SND(FILTER ($= s o FST) (compile((s,r,m)::c)))) =
                             (Send,r,m)::FLAT(MAP SND (FILTER ($= s o FST) (compile c))))`,
  qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_endpoints
  >> rpt strip_tac
  >> fs[compile_def,endpoints_def,add_def,FILTER_MAP,o_DEF]
  >> rw[] >> fs[ALL_DISTINCT_FILTER,project_def,FILTER_EQ_NIL,EVERY_MEM]
  >> first_x_assum(qspec_then `s` mp_tac) >> rw[]
  >> fs[ISPEC ``$= s`` ETA_THM]
  >> imp_res_tac project_nonmem_nil >> fs[]);

val compile_rcv_evs_lemma' = Q.prove(
`wf_chor c /\ s ≠ r ==> (FLAT(MAP SND(FILTER ($= r o FST) (compile((s,r,m)::c)))) =
                             (Receive,s,m)::FLAT(MAP SND (FILTER ($= r o FST) (compile c))))`,
  qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_endpoints
  >> rpt strip_tac
  >> fs[compile_def,endpoints_def,add_def,FILTER_MAP,o_DEF]
  >> rw[] >> fs[ALL_DISTINCT_FILTER,project_def,FILTER_EQ_NIL,EVERY_MEM]
  >> first_x_assum(qspec_then `r` mp_tac) >> rw[]
  >> fs[ISPEC ``$= r`` ETA_THM]
  >> imp_res_tac project_nonmem_nil >> fs[]);

val compile_snd_append_lemma = Q.prove(`!c c'. wf_chor c /\ wf_chor c' ==> (FLAT(MAP SND (FILTER ($= s o FST) (compile (c++c')))) = FLAT(MAP SND (FILTER ($= s o FST) (compile (c))) ++ MAP SND (FILTER ($= s o FST) (compile (c')))))`,
  Induct >- fs[compile_def,endpoints_def]
  >> Cases >> rename [`s1,tup`] >> Cases_on `tup` >> rename [`(s1,r1,m1)`] >> rpt strip_tac
  >> `wf_chor c` by fs[wf_chor_def]
  >> `s1 ≠ r1` by fs[wf_chor_def]
  >> first_x_assum drule >> disch_then(qspec_then `c'` mp_tac) >> disch_then drule
  >> `wf_chor(c++c')` by fs[wf_chor_def]
  >> Cases_on `s1 = s`
  >- (rveq >> rpt strip_tac >> fs[compile_snd_evs_lemma'])
  >> Cases_on `r1 = s`
  >- (rveq >> rpt strip_tac >> fs[compile_rcv_evs_lemma'])
  >> fs[compile_neither_evs_lemma]);

val FILTER_FST_compile_HD_send = Q.prove(
  `!s r m c. ?evs. (FILTER ($= s ∘ FST) (compile ((s,r,m)::c))) = [(s,(Send,r,m)::evs)]`,
  rw[compile_def,endpoints_def,project_def,add_def] >> fs[FILTER_MAP,o_DEF]
  >> qspec_then `c` assume_tac ALL_DISTINCT_endpoints >> rw[]
  >> fs[ALL_DISTINCT_FILTER,FILTER_EQ_NIL,EVERY_MEM] >> metis_tac[]);

val IS_SUBLIST_FILTER_MONO_SINGLE = Q.store_thm("IS_SUBLIST_FILTER_MONO_SINGLE",
  `!l e d f g. (!x. g x ==> f x) /\ (FILTER f l = [e]) /\ (FILTER g l = [d]) ==> (e = d)`,
  rpt strip_tac >> fs[FILTER_EQ_CONS,FILTER_EQ_NIL,EVERY_MEM]
  >> rveq >> fs[APPEND_EQ_APPEND_MID] >> rveq
  >> fs[MEM_APPEND,CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_SING]
  >> metis_tac[]);

val clean_terminated_PERM = Q.store_thm("clean_terminated_PERM",
  `!l l'. PERM l l' ==> (clean_terminated l = l) ==> (clean_terminated l' = l')`,
  fs[clean_terminated_def]
  >> ho_match_mp_tac PERM_IND >> rpt strip_tac
  >- (Cases_on `x` >> fs[] >> rw[] >> fs[]
      >> Q.ISPECL_THEN [`(λ(a,b). b ≠ [])`,`l`] assume_tac LENGTH_FILTER_LEQ
      >> rfs[])
  >- (Cases_on `x` >> Cases_on `y` >> fs[] >> rw[] >> fs[] >> rfs[]
      >> Q.ISPECL_THEN [`(λ(a,b). b ≠ [])`,`l`] assume_tac LENGTH_FILTER_LEQ
      >> rfs[])
  >- metis_tac[]);

val clean_terminated_length = Q.store_thm("clean_terminated_length",
  `!l. LENGTH(clean_terminated l) <= LENGTH l`,
  Induct >> rpt strip_tac >> fs[clean_terminated_def] >> rpt(pairarg_tac >> fs[])
  >> every_case_tac >> fs[]);

val clean_terminated_double_sandwich_IMP = Q.store_thm("clean_terminated_double_sandwich_IMP",
  `(clean_terminated ll ++ [e] ++ clean_terminated lc ++ [r] ++ clean_terminated lr
   = ll ++ [e] ++ lc ++ [r] ++ lr)
  ==> (clean_terminated ll = ll) /\ (clean_terminated lc = lc) /\ (clean_terminated lr = lr)`,
  strip_tac
  >> imp_res_tac LENGTH_EQ >> rfs[]
  >> qspec_then `ll` assume_tac clean_terminated_length
  >> qspec_then `lc` assume_tac clean_terminated_length
  >> qspec_then `lr` assume_tac clean_terminated_length
  >> `LENGTH(clean_terminated ll) = LENGTH ll` by intLib.COOPER_TAC
  >> `LENGTH(clean_terminated lr) = LENGTH lr` by intLib.COOPER_TAC
  >> `LENGTH(clean_terminated lc) = LENGTH lc` by intLib.COOPER_TAC
  >> fs[APPEND_LENGTH_EQ])

val project_append = Q.store_thm("project_append",
  `!p l l'. project p (l ++ l') = project p l ++ project p l'`,
 strip_tac >> Induct >- fs[project_def]
 >> Cases >> Cases_on `r` >> rpt strip_tac >> fs[project_def]
 >> rw[]);

val endpoints_FOLDR = Q.store_thm("endpoints_foldr",
  `!l. endpoints l = FOLDR (λ(s,r,m). add s o add r) [] l`,
  recInduct endpoints_ind >> fs[endpoints_def])

val EVERY_compile_nonempty = Q.store_thm("EVERY_compile_nonempty",
  `!c. EVERY (λ(s,l). l ≠ []) (compile c)`,
  simp[compile_def] >> recInduct endpoints_ind >> rpt strip_tac
  >> fs[endpoints_def,project_def,add_def,EVERY_MAP] >> every_case_tac
  >> rw[]
  >> qpat_x_assum `EVERY _ _` mp_tac
  >> rpt(pop_assum kall_tac)
  >> match_mp_tac EVERY_MONOTONIC >> rw[])

val EVERY_project_nonempty = Q.store_thm("EVERY_project_nonempty",
  `!c. EVERY (λe. project e c ≠ []) (endpoints c)`,
  strip_tac >> qspec_then `c` assume_tac EVERY_compile_nonempty
  >> fs[compile_def,pairTheory.ELIM_UNCURRY,EVERY_MAP]);
                                        
val FILTER_compile_nonempty = Q.store_thm("FILTER_compile_nonempty",
  `!c. FILTER (λ(s,l). l ≠ []) (compile c) = (compile c)`,
  strip_tac >> qspec_then `c` assume_tac EVERY_compile_nonempty
  >> qpat_abbrev_tac `a = compile _` >> pop_assum kall_tac
  >> Induct_on `a` >> fs[]);

val PERM_SANDWICH_IMP = Q.store_thm("PERM_SANDWICH_IMP",
  `!ll e lc r. PERM (ll ++ [e] ++ lc) r ==> ?rl rc. (r = rl ++ [e] ++ rc) /\ PERM(rl++rc) (ll++lc)`,
  Induct >> rpt strip_tac
  >- (fs[PERM_CONS_EQ_APPEND] >> metis_tac[PERM_SYM])
  >> fs[PERM_CONS_EQ_APPEND] >> rveq >> first_x_assum drule >> rpt strip_tac
  >> qpat_x_assum `_ = _ ` (assume_tac o SIMP_RULE std_ss [APPEND_EQ_APPEND])
  >> fs[] >> rveq
  >- (qexists_tac `rl` >> qexists_tac `l ++ [h] ++ N`
      >> rw[Once PERM_SYM] >> fs[PERM_CONS_EQ_APPEND]
      >> metis_tac[PERM_SYM,APPEND_ASSOC])
  >- (qexists_tac `M ++ [h] ++ l'` >> qexists_tac `rc`
      >> rw[Once PERM_SYM] >> fs[PERM_CONS_EQ_APPEND]
      >> metis_tac[PERM_SYM,APPEND_ASSOC])
  >> fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_SING] >> rveq
  >- (qexists_tac `rl` >> qexists_tac `h::rc`
      >> rw[Once PERM_SYM] >> fs[PERM_CONS_EQ_APPEND]
      >> metis_tac[PERM_SYM,APPEND_ASSOC])
  >- (qexists_tac `rl ++ [h]` >> qexists_tac `rc`
      >> rw[Once PERM_SYM] >> fs[PERM_CONS_EQ_APPEND]
      >> metis_tac[PERM_SYM,APPEND_ASSOC]))

val PERM_DOUBLE_SANDWICH_IMP = Q.store_thm("PERM_DOUBLE_SANDWICH_IMP",
  `!ll e lc e' lr r. PERM (ll ++ [e] ++ lc ++ [e'] ++ lr) r ==> ?rl rc rr. ((r = rl ++ [e'] ++ rc ++ [e] ++ rr) \/ (r = rl ++ [e] ++ rc ++ [e'] ++ rr)) /\ PERM(rl++rc++rr) (ll++lc++lr)`,
  rpt strip_tac >> imp_res_tac PERM_SANDWICH_IMP >> rveq
  >> qpat_x_assum `PERM (_ ++ _ ++ _) _` mp_tac
  >> pop_assum (assume_tac o REWRITE_RULE[Once PERM_SYM,GSYM APPEND_ASSOC])
  >> pop_assum (assume_tac o REWRITE_RULE[Once APPEND_ASSOC])
  >> imp_res_tac PERM_SANDWICH_IMP >> strip_tac
  >> qpat_x_assum `_ = _ ` (assume_tac o SIMP_RULE std_ss [APPEND_EQ_APPEND])
  >> fs[] >> rveq
  >- (qexists_tac `rl'` >> qexists_tac `l` >> qexists_tac `rc` >> fs[])
  >- (qexists_tac `rl` >> qexists_tac `l'` >> qexists_tac `rc'` >> fs[])
  >> fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_SING] >> rveq
  >> qexists_tac `rl'` >> qexists_tac `[]` >> qexists_tac `rc'` >> fs[]); 

val trans_perm = Q.store_thm("trans_perm",
  `!p a p'. trans p a p' ==> (!q. PERM p q ==> ?q'. trans q a q' /\ PERM p' q')`,
  rpt strip_tac >> Cases_on `a`
  >- (* Internal *)
     (imp_res_tac reduces_sender_receiver >> fs[] >> rveq
      >> imp_res_tac PERM_DOUBLE_SANDWICH_IMP >> fs[] >> rveq
      >- (qexists_tac `rl ++ [(s,evs')] ++ rc ++ [(r,evs)] ++ rr`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> CONV_TAC PERM_NORMALISE_CONV
          >> NORMALISE_ASM_PERM_TAC
          >> first_x_assum ACCEPT_TAC)
      >- (qexists_tac `rl ++ [(r,evs)] ++ rc ++ [(s,evs')] ++ rr`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> CONV_TAC PERM_NORMALISE_CONV
          >> NORMALISE_ASM_PERM_TAC
          >> first_x_assum ACCEPT_TAC)
      >- (qexists_tac `rl ++ [(r,evs)] ++ rc ++ [(s,evs')] ++ rr`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> CONV_TAC PERM_NORMALISE_CONV
          >> NORMALISE_ASM_PERM_TAC
          >> first_x_assum ACCEPT_TAC)
      >- (qexists_tac `rl ++ [(s,evs')] ++ rc ++ [(r,evs)] ++ rr`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> CONV_TAC PERM_NORMALISE_CONV
          >> NORMALISE_ASM_PERM_TAC
          >> first_x_assum ACCEPT_TAC))
  >> Cases_on `x` >> rename [`(act,tup)`] >> Cases_on `tup` >> Cases_on `act`
  >> rename [`(_,s,tup)`] >> Cases_on `tup` >> rename [`(_,s,r,m)`]
  >- (* Send *)
     (imp_res_tac sends_sender
      >> fs[] >> rveq >> fs[]
      >> imp_res_tac PERM_SANDWICH_IMP
      >> rveq >> fs[]
      >> qexists_tac `rl ++ [(s,evs)] ++ rc`
      >> strip_tac
      >- metis_tac[trans_rules]
      >> CONV_TAC PERM_NORMALISE_CONV
      >> NORMALISE_ASM_PERM_TAC
      >> first_x_assum ACCEPT_TAC)
  >- (* Receive *)
     (imp_res_tac receives_receiver
      >> fs[] >> rveq >> fs[]
      >> imp_res_tac PERM_SANDWICH_IMP
      >> rveq >> fs[]
      >> qexists_tac `rl ++ [(r,evs)] ++ rc`
      >> strip_tac
      >- metis_tac[trans_rules]
      >> CONV_TAC PERM_NORMALISE_CONV
      >> NORMALISE_ASM_PERM_TAC
      >> first_x_assum ACCEPT_TAC))

val clean_terminated_append = Q.store_thm("clean_terminated_append",
  `!c1 c2. clean_terminated(c1 ++ c2) = clean_terminated c1 ++ clean_terminated c2`,
  rw[clean_terminated_def,FILTER_APPEND]);

val clean_terminated_idem = Q.store_thm("clean_terminated_idem",
  `!l. clean_terminated(clean_terminated l) = clean_terminated l`,
  fs[clean_terminated_def,FILTER_FILTER,pairTheory.ELIM_UNCURRY]);

val clean_terminated_single = Q.store_thm("clean_terminated_single",
  `!a b. clean_terminated [(a,b)] = if b = [] then [] else [a,b]`,
  rw[clean_terminated_def]);

val trans_clean_terminated = Q.store_thm("trans_clean_terminated",
  `!p a p'. trans p a p' ==> ?p''. trans (clean_terminated p) a p'' /\ (clean_terminated p' = clean_terminated p'')`,
  rpt strip_tac >> Cases_on `a`
  >- (* Internal *)
     (imp_res_tac reduces_sender_receiver >> fs[] >> rveq
      >> fs[clean_terminated_append,clean_terminated_single] >> rveq
      >- (qexists_tac `clean_terminated ll ++ [(r,evs)] ++ clean_terminated lc ++ [(s,evs')] ++ clean_terminated lr`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> fs[clean_terminated_append,clean_terminated_idem,clean_terminated_single])
      >- (qexists_tac `clean_terminated ll ++ [(s,evs')] ++ clean_terminated lc ++ [(r,evs)] ++ clean_terminated lr`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> fs[clean_terminated_append,clean_terminated_idem,clean_terminated_single]))
  >> Cases_on `x` >> rename [`(act,tup)`] >> Cases_on `tup` >> Cases_on `act`
  >> rename [`(_,s,tup)`] >> Cases_on `tup` >> rename [`(_,s,r,m)`]
  >- (* Send *)
     (imp_res_tac sends_sender
      >> fs[] >> rveq >> fs[clean_terminated_append,clean_terminated_single]
      >> qexists_tac `clean_terminated ll ++ [(s,evs)] ++ clean_terminated lr`
      >> strip_tac
      >- metis_tac[trans_rules]
      >> fs[clean_terminated_append,clean_terminated_idem,clean_terminated_single])
  >- (* Receive *)
     (imp_res_tac receives_receiver
      >> fs[] >> rveq >> fs[clean_terminated_append,clean_terminated_single]
      >> qexists_tac `clean_terminated ll ++ [(r,evs)] ++ clean_terminated lr`
      >> strip_tac
      >- metis_tac[trans_rules]
      >> fs[clean_terminated_append,clean_terminated_idem,clean_terminated_single]));

val FILTER_EQ_TRIPLE_APPEND = Q.store_thm("FILTER_EQ_TRIPLE_APPEND",
  `(FILTER P l = l1 ++ l2 ++ l3) ⇔
     ∃l1' l2' l3'. (l = l1' ++ l2' ++ l3') ∧ (FILTER P l1' = l1) ∧ (FILTER P l2' = l2) ∧ (FILTER P l3' = l3)`,
  fs[FILTER_EQ_APPEND] >> metis_tac[APPEND_ASSOC]);

val FILTER_EQ_QUINTUPLE_APPEND = Q.store_thm("FILTER_EQ_QUINTUPLE_APPEND",
  `(FILTER P l = l1 ++ l2 ++ l3 ++ l4 ++ l5) ⇔
     ∃l1' l2' l3' l4' l5'. (l = l1' ++ l2' ++ l3' ++ l4' ++ l5') ∧ (FILTER P l1' = l1) ∧ (FILTER P l2' = l2) ∧ (FILTER P l3' = l3) ∧ (FILTER P l4' = l4) ∧ (FILTER P l5' = l5)`,
  fs[FILTER_EQ_APPEND] >> metis_tac[APPEND_ASSOC]);

val trans_clean_terminated' = Q.store_thm("trans_clean_terminated'",
  `!p a p'. trans (clean_terminated p) a p' ==> ?p''. trans p a p'' /\ (clean_terminated p' = clean_terminated p'')`,
  rpt strip_tac >> Cases_on `a`
  >- (* Internal *)
     (imp_res_tac reduces_sender_receiver >> fs[] >> rveq
      >> fs[clean_terminated_append,clean_terminated_single]
      >> rveq >> fs[clean_terminated_def,FILTER_EQ_QUINTUPLE_APPEND,FILTER_EQ_CONS,FILTER_IDEM] >> rveq >> fs[FILTER_IDEM]
      >> rename [`l1 ++ l2 ++ _ ++ l3 ++ l4 ++ l5 ++ _ ++ l6 ++ l7`]
      >- (qexists_tac `l1 ++ l2 ++ [(r,evs)] ++ l3 ++ l4 ++ l5 ++ [(s,evs')] ++ l6 ++ l7`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> qexists_tac `l1 ++ l2 ` >> qexists_tac `[(r,evs)]`
          >> qexists_tac `l3 ++ l4 ++ l5 ` >> qexists_tac `[(s,evs')]`
          >> qexists_tac `l6++l7` >> fs[FILTER_APPEND] >> rw[] >> fs[] >> rfs[])
      >- (qexists_tac `l1 ++ l2 ++ [(s,evs')] ++ l3 ++ l4 ++ l5 ++ [(r,evs)] ++ l6 ++ l7`
          >> strip_tac
          >- metis_tac[trans_rules]
          >> qexists_tac `l1 ++ l2 ` >> qexists_tac `[(s,evs')]`
          >> qexists_tac `l3 ++ l4 ++ l5 ` >> qexists_tac `[(r,evs)]`
          >> qexists_tac `l6++l7` >> fs[FILTER_APPEND] >> rw[] >> fs[] >> rfs[]))
  >> Cases_on `x` >> rename [`(act,tup)`] >> Cases_on `tup` >> Cases_on `act`
  >> rename [`(_,s,tup)`] >> Cases_on `tup` >> rename [`(_,s,r,m)`]
  >- (* Send *)
     (imp_res_tac sends_sender
      >> fs[] >> rveq >> fs[clean_terminated_append,clean_terminated_single]
      >> fs[clean_terminated_def,FILTER_EQ_TRIPLE_APPEND] >> rveq >> fs[FILTER_IDEM,FILTER_EQ_CONS]
      >> rveq >> rename [`l1 ++ l2 ++ _ ++ l3 ++ l4`]
      >> qexists_tac `l1 ++ l2 ++ [(s,evs)] ++ l3 ++ l4`
      >> strip_tac
      >- metis_tac[trans_rules]
      >> qexists_tac `l1 ++ l2` >> qexists_tac `[(s,evs)]` >> qexists_tac `l3 ++ l4`
      >> fs[FILTER_APPEND] >> rw[])
  >- (* Receive *)
     (imp_res_tac receives_receiver
      >> fs[] >> rveq >> fs[clean_terminated_append,clean_terminated_single]
      >> fs[clean_terminated_def,FILTER_EQ_TRIPLE_APPEND] >> rveq >> fs[FILTER_IDEM,FILTER_EQ_CONS]
      >> rveq >> rename [`l1 ++ l2 ++ _ ++ l3 ++ l4`]
      >> qexists_tac `l1 ++ l2 ++ [(r,evs)] ++ l3 ++ l4`
      >> strip_tac
      >- metis_tac[trans_rules]
      >> qexists_tac `l1 ++ l2` >> qexists_tac `[(r,evs)]` >> qexists_tac `l3 ++ l4`
      >> fs[FILTER_APPEND] >> rw[] >> rfs[]));

val ext = Q.prove(`!f a b. (a = b) ==> (f a = f b)`,rw[]);

val ALOOKUP_PERM = Q.store_thm("ALOOKUP_PERM",
  `!l1 l2 x. PERM l1 l2 /\ ALL_DISTINCT (MAP FST l1) ==> (ALOOKUP l1 x = ALOOKUP l2 x)`,
  metis_tac[ALOOKUP_ALL_DISTINCT_PERM_same,PERM_MAP,PERM_LIST_TO_SET]);

val ALOOKUP_compile = Q.store_thm("ALOOKUP_compile",
  `ALOOKUP (MAP (λe. (e,project e c)) (endpoints c)) r
  = if project r c = [] then NONE else SOME(project r c)`,
  rw[]
  >> imp_res_tac nonmem_nil_project
  >> imp_res_tac(CONTRAPOS (SPEC_ALL project_nonmem_nil))
  >> fs[ALOOKUP_TABULATE,ALOOKUP_NONE,MEM_MAP]
  >> metis_tac[FST]);

val FST_SND_EQ_JOIN = Q.store_thm("FST_SND_EQ_JOIN",
  `(FST x = FST y) /\ (SND x = SND y) ==> (x = y)`,
  rw[PAIR_FST_SND_EQ]);

val MAP_if_notmem_lemma = Q.prove(
  `!l s r f g h. ¬MEM s l /\ ¬MEM r l ==>
   (MAP (λe. (e, if e = s then f e
                 else if e = r then g e
                 else h e)) l = MAP (λe. (e, h e)) l)`,
  Induct >> fs[]);

val MAP_if_notmem_lemma2 = Q.prove(
  `!l s r f g h. ¬MEM s (MAP FST l) /\ ¬MEM r (MAP FST l) ==>
   (MAP (λ(e,x). if e = s then f s x
                 else if e = r then g r x
                 else h e x) l = MAP (λ(e,x). h e x) l)`,
  Induct >- fs[] >> Cases >> Cases >> rpt strip_tac >> fs[]);

val MAP_if_notmem_lemma3 = Q.prove(
  `!l s f g. ¬MEM s (MAP FST l) ==>
   (MAP (λx. (FST x, if FST x = s then f x
                 else g x)) l = MAP (λx. (FST x, g x)) l)`,
  Induct >> fs[]);

val MAP_if_notmem_lemma4 = Q.prove(
  `!l s r f g e. ¬MEM r (MAP FST l) ==>
   (MAP (λx. (FST x, if FST x = s then f s x
                 else if FST x = r then g r x
                 else e x)) l = (MAP (λx. (FST x, if FST x = s then f s x
                 else e x)) l))`,
  Induct >> fs[]);

val MAP_if_notmem_lemma5 = Q.prove(
  `!l s r f g h. ¬MEM s l ==>
   ((MAP (λe.
                 if e = s then f s
                 else if e = r then g r
                 else h e) l)
    =
   (MAP (λe.
                 if e = r then g r
                 else h e) l))
`,
  Induct >> fs[]);

val MAP_if_notmem_lemma6 = Q.prove(
  `!l s f h. ¬MEM s l ==>
   ((MAP (λe.
                 if e = s then f s else h e) l)
    =
   (MAP h l))
`,
  Induct >> fs[]);

val if_lemma3 = Q.prove(
  `(if e = s then f s
                 else if e = r then f r
    else f e) = f e`, rw[]);

val if_lemma4 = Q.prove(
  `(if e = s then f s
                 else f e) = f e`, rw[]);

val pair_lam_id = Q.prove(`(λ(x,x'). (x,x')) = I`,
  rw[pairTheory.ELIM_UNCURRY,I_DEF,S_DEF,K_DEF]);

val NULL_MAP = Q.prove(`!f l. NULL (MAP f l) = NULL l`,
  strip_tac >> Induct >> fs[]);

val guard_impossible_lemma1 = Q.prove(`((Send,tup)::l =
      if b then
        (Receive,tup')::l'
      else l'') ==> ~b`,rw[])

val guard_impossible_lemma2 = Q.prove(`((Receive,tup)::l =
      if b then
        (Send,tup')::l'
      else l'') ==> ~b`,rw[])

                                     
val MAP_ALL_DISTINCT_SANDWICH = Q.store_thm("MAP_ALL_DISTINCT_SANDWICH",
  `!l f l1 e l2.
  ALL_DISTINCT l /\ ALL_DISTINCT (MAP f l) ==>
  ((MAP f l = l1 ++ [e] ++ l2) = ?l3 e1 l4. (l = l3 ++ [e1] ++ l4) /\ (e = f(e1)) /\ (l1 = MAP f l3)  /\ (l2 = MAP f l4))`,
  rpt strip_tac >> fs[MAP_EQ_APPEND] >> rw[EQ_IMP_THM] >> fs[ALL_DISTINCT_APPEND]
  >> metis_tac []);

val [MAP_ALL_DISTINCT_SANDWICH_I,MAP_ALL_DISTINCT_SANDWICH_E] = 
  MAP_ALL_DISTINCT_SANDWICH |> SPEC_ALL |> UNDISCH_ALL |> REWRITE_RULE [EQ_IMP_THM]
  |> CONJUNCTS |> (fn [I,E] => [UNDISCH_ALL I, E])
  |> map DISCH_ALL |> map (REWRITE_RULE [AND_IMP_INTRO]) |> map GEN_ALL

val MAP_ALL_DISTINCT_DOUBLE_SANDWICH = Q.store_thm("MAP_ALL_DISTINCT_DOUBLE_SANDWICH",
  `!l f l1 e l2 e' l3.
  ALL_DISTINCT l /\ ALL_DISTINCT (MAP f l) ==>
  ((MAP f l = l1 ++ [e] ++ l2 ++ [e'] ++ l3) = ?l4 e1 l5 e1' l6. (l = l4 ++ [e1] ++ l5 ++ [e1'] ++ l6) /\ (e = f(e1)) /\ (e' = f(e1')) /\ (l1 = MAP f l4)  /\ (l2 = MAP f l5)  /\ (l3 = MAP f l6))`,
  rpt strip_tac >> fs[MAP_ALL_DISTINCT_SANDWICH] >> rw[EQ_IMP_THM]
  >- (fs[ALL_DISTINCT_APPEND] >> pop_assum (mp_tac o GSYM) >> fs[MAP_ALL_DISTINCT_SANDWICH]
        >> metis_tac[])
  >> metis_tac[MAP_APPEND,MAP]);

val [MAP_ALL_DISTINCT_DOUBLE_SANDWICH_I,MAP_ALL_DISTINCT_DOUBLE_SANDWICH_E] = 
  MAP_ALL_DISTINCT_DOUBLE_SANDWICH |> SPEC_ALL |> UNDISCH_ALL |> REWRITE_RULE [EQ_IMP_THM]
  |> CONJUNCTS |> (fn [I,E] => [UNDISCH_ALL I, E])
  |> map DISCH_ALL |> map (REWRITE_RULE [AND_IMP_INTRO]) |> map GEN_ALL

val clean_terminated_compile = Q.store_thm("clean_terminated_compile",
  `!c. clean_terminated(compile c) = compile c`,
  rw[clean_terminated_def,FILTER_compile_nonempty]);

val compile_receive_has_exchange = Q.store_thm("compile_receive_has_exchange",
  `
  !c r s m evs.
  wf_chor c
  /\ MEM (r,(Receive,s,m)::evs) (compile c)
     ==> ?c' c''. (c = c' ++ (s,r,m)::c'') /\ EVERY (λx. x ≠ (s,r,m)) c'
                  /\ EVERY (λ(s',r',m'). s' ≠ r /\ r' ≠ r) c'
  `,
  simp[compile_def]
  >> ho_match_mp_tac endpoints_ind >> rpt strip_tac
  >- fs[endpoints_def]
  >> rename [`(s1,r1,m1)::_`]
  >> rename [`[(s2,r2,m2)]`]
  >> qspec_then `c` assume_tac ALL_DISTINCT_endpoints
  >> `ALL_DISTINCT(add s1 (add r1 (endpoints c)))` by fs[ALL_DISTINCT_add]
  >> fs[project_def,endpoints_def,wf_chor_def] >> rveq >> fs[MEM_MAP]
  >> first_x_assum (qspecl_then [`r2`,`s2`,`m2`] assume_tac)
  >> fs[add_def] >> every_case_tac >> fs[] >> rveq >> fs[]
  >- (qexists_tac `[]` >> fs[])
  >- (rfs[] >> first_x_assum (qspec_then `evs` assume_tac) >> rfs[]
      >> qexists_tac `(s1,r1,m1)::c'` >> fs[])
  >- (qexists_tac `[]` >> fs[])
  >- (rfs[] >> first_x_assum (qspec_then `evs` assume_tac) >> rfs[]
      >> qexists_tac `(s1,r1,m1)::c'` >> fs[])
  >- (qexists_tac `[]` >> fs[])
  >- (rfs[] >> first_x_assum (qspec_then `evs` assume_tac) >> rfs[]
      >> qexists_tac `(s1,r1,m1)::c'` >> fs[])
  >- (qexists_tac `[]` >> fs[])
  >- (rfs[] >> first_x_assum (qspec_then `evs` assume_tac) >> rfs[]
      >> qexists_tac `(s1,r1,m1)::c'` >> fs[]));

val compile_send_has_exchange = Q.store_thm("compile_send_has_exchange",
  `
  !c r s m evs.
  wf_chor c
  /\ MEM (s,(Send,r,m)::evs) (compile c)
     ==> ?c' c''. (c = c' ++ (s,r,m)::c'') /\ EVERY (λx. x ≠ (s,r,m)) c'
                  /\ EVERY (λ(s',r',m'). r' ≠ s /\ s' ≠ s) c'
  `,
  simp[compile_def]
  >> ho_match_mp_tac endpoints_ind >> rpt strip_tac
  >- fs[endpoints_def]
  >> rename [`(s1,r1,m1)::_`]
  >> rename [`[(s2,r2,m2)]`]
  >> qspec_then `c` assume_tac ALL_DISTINCT_endpoints
  >> `ALL_DISTINCT(add s1 (add r1 (endpoints c)))` by fs[ALL_DISTINCT_add]
  >> fs[project_def,endpoints_def,wf_chor_def] >> rveq >> fs[MEM_MAP]
  >> first_x_assum (qspecl_then [`r2`,`s2`,`m2`] assume_tac)
  >> fs[add_def] >> every_case_tac >> fs[] >> rveq >> fs[]  
  >- (qexists_tac `[]` >> fs[])
  >- (first_x_assum drule >> disch_then drule
      >> rpt strip_tac >> fs[] >> qexists_tac `(s1,r1,m1)::c'` >> fs[])
  >- (qexists_tac `[]` >> fs[])
  >- (first_x_assum drule >> disch_then drule
      >> rpt strip_tac >> fs[] >> qexists_tac `(s1,r1,m1)::c'` >> fs[])
  >- (qexists_tac `[]` >> fs[])
  >- (first_x_assum drule >> disch_then drule
      >> rpt strip_tac >> fs[] >> qexists_tac `(s1,r1,m1)::c'` >> fs[])
  >- (qexists_tac `[]` >> fs[])
  >- (first_x_assum drule >> disch_then drule
      >> rpt strip_tac >> fs[] >> qexists_tac `(s1,r1,m1)::c'` >> fs[]));

val clean_terminated_append_lemma = Q.prove(`!l l'. (clean_terminated l = l' ++ l) ==> (l' = [])`,
  rpt strip_tac >> qspec_then `l` mp_tac clean_terminated_length
  >> qpat_abbrev_tac `a = clean_terminated _` >> pop_assum kall_tac
  >> pop_assum mp_tac
  >> Q.SPEC_TAC (`l`,`l`) >> Q.SPEC_TAC (`l'`,`l'`)
  >> Q.SPEC_TAC (`a`,`a`) >> Induct >> rpt strip_tac
  >> fs[] >> Cases_on `l'` >> rfs[]);

val ALL_DISTINCT_SANDWICH = Q.store_thm("ALL_DISTINCT_SANDWICH",
  `!a b c d e. ALL_DISTINCT(a ++ [e] ++ c) ==>
  ((a ++ [e] ++ c) = (b ++ [e] ++ d)) ==> ((a = b) /\ (c = d))`,
 Induct_on `a` >> strip_tac
 >- (Cases_on `b` >> fs[])
 >> Cases_on `b` >> rpt strip_tac >> fs[] >> rveq
 >> pop_assum (assume_tac o GSYM) >> fs[]
 >> first_x_assum drule >> pop_assum (assume_tac o GSYM)
 >> disch_then drule >> fs[]);

val ALL_DISTINCT_DOUBLE_SANDWICH = Q.store_thm("ALL_DISTINCT_DOUBLE_SANDWICH",
  `!a b c d e f g h. ALL_DISTINCT(a ++ [e] ++ c ++ [f] ++ g) ==>
  ((a ++ [e] ++ c ++ [f] ++ g) = (b ++ [e] ++ d ++ [f] ++ h)) ==> ((a = b) /\ (c = d) /\ (g = h))`,
  rpt GEN_TAC >> rpt DISCH_TAC >> imp_res_tac ALL_DISTINCT_SANDWICH
  >> `ALL_DISTINCT (a ++ [e] ++ c)` by (fs[ALL_DISTINCT_APPEND] >> metis_tac [])
  >> imp_res_tac ALL_DISTINCT_SANDWICH >> fs[]);

val ALL_DISTINCT_compile = Q.store_thm("ALL_DISTINCT_compile",
  `!c. ALL_DISTINCT (compile c)`,
  rpt strip_tac >> fs[compile_def] >> match_mp_tac ALL_DISTINCT_MAP_INJ
  >> fs[ALL_DISTINCT_endpoints]);

val ALL_DISTINCT_COMPILE_PERM = Q.store_thm("ALL_DISTINCT_COMPILE_PERM",
  `∀c l. PERM (compile c) l ⇒ ALL_DISTINCT l`,
  metis_tac[ALL_DISTINCT_compile,ALL_DISTINCT_PERM])

val ALL_DISTINCT_FST_compile = Q.store_thm("ALL_DISTINCT_FST_compile",
  `!c. ALL_DISTINCT (MAP FST (compile c))`,
  rpt strip_tac >> rw[compile_def,MAP_MAP_o,o_DEF,ALL_DISTINCT_endpoints]);
                                           
val ALL_DISTINCT_FST_COMPILE_PERM = Q.store_thm("ALL_DISTINCT_FST_COMPILE_PERM",
  `∀c l. PERM (compile c) l ⇒ ALL_DISTINCT(MAP FST l)`,
  metis_tac[ALL_DISTINCT_FST_compile,ALL_DISTINCT_PERM,PERM_MAP])
                                               
val MAP_FST_compile = Q.store_thm("MAP_FST_compile",
  `!c. MAP FST (compile c) = endpoints c`,
  rw[compile_def,MAP_MAP_o,o_DEF]);

val EXISTS_SPLITP_NOT_NIL =  Q.store_thm("EXISTS_SPLITP_NOT_NIL",
  `!f l. EXISTS f l ==> SND(SPLITP f l) ≠ []`,
  strip_tac >> Induct >> rw[SPLITP]);

val MEM_SPLITP_lemma =  Q.prove(
  `!f a l. MEM a l ==> SND(SPLITP (λx. FST x = a) (MAP (λe. (e, f e)) l)) ≠ []`,
  ntac 4 strip_tac >> ho_match_mp_tac EXISTS_SPLITP_NOT_NIL >> fs[MEM_EXISTS,EXISTS_MAP]
  >> pop_assum mp_tac >> Induct_on `l` >> fs[] >> metis_tac[]);

val MEM_SPLIT2 = Q.store_thm("MEM_SPLIT2",
  `x ≠ y /\ MEM x l /\ MEM y l ==> ∃l1 l2 l3. (l = l1 ++ x::l2 ++ y::l3) \/ (l = l1 ++ y::l2 ++ x::l3)`,
  rpt strip_tac >> fs[MEM_SPLIT] >> rveq >> pop_assum mp_tac >> fs[Once APPEND_EQ_APPEND_MID]
  >> rpt strip_tac >> fs[] >> rveq >> fs[]
  >> TRY(qpat_x_assum `_ = _` mp_tac >> fs[Once ((CONV_RULE(LHS_CONV SYM_CONV)) APPEND_EQ_APPEND_MID)] >> rpt strip_tac >> rveq) >> fs[(CONV_RULE(LHS_CONV SYM_CONV)) APPEND_EQ_SING]
  >> metis_tac[]);

val exists_every_lemma = Q.prove(
  `!l e. (EXISTS ($= e) l /\ EVERY (λe'. e' ≠ e) l) ==> F`,
  rw[EXISTS_MEM,EVERY_MEM]);

val MEM_SPLITP_lemma2 =  Q.prove(
 `!a b l l' l'' f. a ≠ b /\ MEM a l /\ MEM b l
            /\ (SPLITP (λx. FST x = a) (MAP (λe. (e, f e)) l) = (l',l''))
                     ==> SND(SPLITP (λx. FST x = b) (l' ++ TL l'')) ≠ []`,
  rpt strip_tac
  >> Cases_on `SPLITP (λx. FST x = b) (l' ++ TL l'')`
  >> EVERY(map imp_res_tac [MEM_SPLITP_lemma,SPLITP_IMP,SPLITP_JOIN])
  >> rpt(first_x_assum (qspec_then `f` assume_tac))
  >> fs[] >> rfs[] >> Cases_on `l''` >> fs[]
  >> fs[SPLITP_APPEND,MEM_EXISTS,MAP_EQ_APPEND] >> rfs[] >> rveq
  >> fs[SPLITP_APPEND,o_DEF,EVERY_MAP,EXISTS_MAP]
  >> imp_res_tac exists_every_lemma
  >> rfs[]);

val MEM_SPLITP_lemma3 =  Q.prove(
 `!a b l l' l'' f. a ≠ b /\ MEM a l /\ ¬MEM b l
            /\ (SPLITP (λx. FST x = a) (MAP (λe. (e, f e)) l) = (l',l''))
                     ==> (SND(SPLITP (λx. FST x = b) (l' ++ TL l'')) = [])`,
  rpt strip_tac
  >> Cases_on `SPLITP (λx. FST x = b) (l' ++ TL l'')`
  >> EVERY(map imp_res_tac [MEM_SPLITP_lemma,SPLITP_IMP,SPLITP_JOIN])
  >> rpt(first_x_assum (qspec_then `f` assume_tac))
  >> fs[] >> rfs[] >> Cases_on `l''` >> fs[]
  >> Cases_on `r`
  >> fs[SPLITP_APPEND,MEM_EXISTS,MAP_EQ_APPEND] >> rfs[] >> rveq
  >> fs[SPLITP_APPEND,o_DEF,EVERY_MAP,EXISTS_MAP,EXISTS_MEM,EVERY_MEM]
  >> every_case_tac >> fs[] >> rfs[] >> fs[APPEND_EQ_APPEND,MAP_EQ_APPEND]
  >> rveq >> fs[MAP_EQ_APPEND] >> rveq >> fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_SING]
  >> rveq >> fs[]);

val MEM_SPLITP_lemma4 =  Q.prove(
 `!a b l l' l'' f. a ≠ b /\ MEM a l /\ MEM b l
            /\ (SPLITP (λx. FST x = a) (MAP (λe. (e, f e)) l) = (l',l''))
                     ==> SND(SPLITP (λx. FST x = b) (l' ++ l'')) ≠ []`,
  rpt strip_tac
  >> Cases_on `SPLITP (λx. FST x = b) (l' ++ TL l'')`
  >> EVERY(map imp_res_tac [MEM_SPLITP_lemma,SPLITP_IMP,SPLITP_JOIN])
  >> rpt(first_x_assum (qspec_then `f` assume_tac))
  >> fs[] >> rfs[] >> Cases_on `l''` >> fs[]
  >> fs[SPLITP_APPEND,MEM_EXISTS,MAP_EQ_APPEND] >> rfs[] >> rveq
  >> fs[SPLITP_APPEND,o_DEF,EVERY_MAP,EXISTS_MAP]
  >> imp_res_tac exists_every_lemma
  >> rfs[]);

val MAP_SANDWICH_lemma = Q.prove(
  `!l f a b c x. (MAP (λe. e, f e) l = a ++ [b] ++ c)
   ==> (MAP FST (a ++ [(FST b, x)] ++ c) = l)`,
  Induct >> rpt strip_tac >> fs[]
  >> fs[APPEND_EQ_CONS,CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_SING]
  >> rfs[]
  >- (qpat_x_assum `[] = _` (assume_tac o GSYM) >> fs[]
      >> qpat_x_assum `MAP _ _ = _` mp_tac >> rpt(pop_assum kall_tac)
      >> EVERY (map (Q.SPEC_TAC o W pair) [`l`,`f`,`c`])
      >> Induct >> rpt strip_tac >> fs[] >> Cases_on `l` >> fs[]
      >> metis_tac[FST])
  >- metis_tac[]);

val highly_specific_rewrite = Q.prove(
  `(a ++ [b] ++ c ++ d::e = a ++ [b] ++ c ++ [d] ++ e) /\ (q' ++ [h'] ++ h::t = q' ++ [h';h] ++ t)
   /\ (q ++ h::(l'' ++ [h'] ++ t') = q ++ [h] ++ l'' ++ [h'] ++ t') /\
   (q ++ h::h'::t' = q ++ [h;h'] ++ t')`,
  fs[]);

val APPEND_TWO_SANDWICHES_LEMMA = Q.prove(
  `(a ++ [(l1,r1)] ++ b = c ++ [(l2,r2)] ++ d) /\ l1 ≠ l2  ==>
   ((c = a ++ [(l1,r1)]) /\ (b = (l2,r2)::d)) \/
   ((a = c ++ [(l2,r2)]) /\ (d = (l1,r1)::b)) \/
   (∃l. (c = a ++ [(l1,r1)] ++ l) /\ (b = l ++ [(l2,r2)] ++ d)) \/
   (∃l. (a = c ++ [(l2,r2)] ++ l) /\ (d = l ++ [(l1,r1)] ++ b))`,
  rpt strip_tac >> fs[APPEND_EQ_APPEND,APPEND_EQ_SING] >> rfs[] >> metis_tac[]
    ) |> GEN_ALL

local
  val tac1 =   qspecl_then [`endpoints c`] drule (INST_TYPE [beta|->``:'a # (action, 'a # 'b) alist``] MAP_ALL_DISTINCT_SANDWICH)
    >> qpat_assum `MAP _ _ = _ ++ _ ++ _`
       (fn thm => `ALL_DISTINCT ^(lhs(concl thm))`
                    by ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
    >> disch_then drule >> disch_then (fn thm => fs[thm])
    >> rveq >> fs[] >> rveq >> fs[ALL_DISTINCT_APPEND] >> rfs[]
    >> fs[Q.prove(`!n. SUC n ≤ 1 <=> (n = 0)`,fs[]),quantHeuristicsTheory.LIST_LENGTH_0]
    >> imp_res_tac nonmem_nil_project >> rfs[]
    
  val tac2 = fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS,APPEND_EQ_APPEND]
    >> rveq >> fs[] >> fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS,APPEND_EQ_APPEND]
    >> rveq >> fs[Q.prove(`!n. SUC n ≤ 1 <=> (n = 0)`,fs[]),quantHeuristicsTheory.LIST_LENGTH_0]
    >> imp_res_tac nonmem_nil_project >> rfs[] >> fs[SPLITP] >> rfs[]
    >> qpat_x_assum `_ ≠ []` (fn thm => assume_tac (ISPEC (lhs(rand(concl thm))) list_nchotomy) >> mp_tac thm) >> fs[] >> rveq >> fs[] >> rveq >> fs[]
    >> fs[MAP_EQ_APPEND] >> rveq >> fs[ALL_DISTINCT_APPEND] >> fs[MAP_if_notmem_lemma]
    >> `FST h = e` by metis_tac[FST] >> fs[]
    >> qpat_x_assum `FST h = e` assume_tac >> fs[EVERY_MAP,MEM_MAP]
    >> qpat_x_assum `h = (_,_)` mp_tac >> fs[]
    >> fs[Q.prove(`!n. SUC n ≤ 1 <=> (n = 0)`,fs[]),quantHeuristicsTheory.LIST_LENGTH_0]
    >> imp_res_tac nonmem_nil_project >> rfs[]
    
    val tac3 = match_mp_tac MAP_ALL_DISTINCT_SANDWICH_E >> fs[ALL_DISTINCT_MAP]
    >> qspec_then `c` assume_tac ALL_DISTINCT_compile >> fs[compile_def]
    >> qspecl_then [`endpoints c`] drule (INST_TYPE [beta|->``:'a # (action, 'a # 'b) alist``] MAP_ALL_DISTINCT_SANDWICH)
    >> qpat_assum `MAP _ _ = _ ++ _ ++ _`
       (fn thm => `ALL_DISTINCT ^(lhs(concl thm))`
                    by ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
    >> disch_then drule >> disch_then (fn thm => fs[thm])
    >> fs[] >> rveq >> fs[] >> rfs[]    
    >> rveq >> fs[] >> rveq >> fs[ALL_DISTINCT_APPEND] >> rfs[]
    >> fs[Q.prove(`!n. SUC n ≤ 1 <=> (n = 0)`,fs[]),quantHeuristicsTheory.LIST_LENGTH_0]
    >> imp_res_tac nonmem_nil_project >> rfs[]
    
    val tac4 = fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS,APPEND_EQ_APPEND]
    >> rveq >> fs[] >> fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS,APPEND_EQ_APPEND]
    >> rveq >> fs[Q.prove(`!n. SUC n ≤ 1 <=> (n = 0)`,fs[]),quantHeuristicsTheory.LIST_LENGTH_0]
    >> imp_res_tac nonmem_nil_project >> rfs[] >> fs[SPLITP] >> rfs[]
    >> rfs[MAP_if_notmem_lemma]
    
    val tac5 = Cases_on `r''` >> fs[]
    >- (`endpoints c = MAP FST q'`
         by(metis_tac [MAP_SANDWICH_lemma])
         >> fs[EVERY_MEM,MEM_MAP] >> metis_tac[])
    >> fs[APPEND_EQ_APPEND] >> rfs[] >> fs[APPEND_EQ_SING] >> rfs[]
    >> rveq >> fs[]
    >> FULL_SIMP_TAC bool_ss [EVAL ``[a] ++ [] ++ [b]`` |> GSYM,APPEND_ASSOC]
    >> drule MAP_ALL_DISTINCT_DOUBLE_SANDWICH_I >> fs[]
    >> qpat_assum
    `ALL_DISTINCT (_ ++ _)` (assume_tac o ONCE_REWRITE_RULE[highly_specific_rewrite])
    >> disch_then drule
    >> rpt strip_tac
    >> qpat_x_assum `endpoints _ = _` mp_tac
    >> fs[]
    >> rpt(qpat_x_assum `_ = (_ , if _ then _ else _)`
           (fn thm =>
               `FST ^(lhs(concl thm)) = ^((rand(rator(rhs(concl thm)))))`
                  by(mp_tac thm >> metis_tac[FST])
               >> mp_tac thm)
          )
    >> fs[]
    >> rpt(qpat_x_assum `FST _ = _` kall_tac)
    >> ntac 2 strip_tac >> fs[]
    >> fs[Q.prove(`!n. SUC n ≤ 1 <=> (n = 0)`,fs[]),quantHeuristicsTheory.LIST_LENGTH_0]
    >> imp_res_tac nonmem_nil_project

    val tac7 = Cases_on `q` >> Cases_on `r'` >> fs[] >> rveq >> fs[SPLITP]
    >> match_mp_tac MAP_ALL_DISTINCT_SANDWICH_E >> fs[ALL_DISTINCT_MAP]
    >> qspec_then `c` assume_tac ALL_DISTINCT_compile >> fs[compile_def]
    >> qspecl_then [`endpoints c`] drule (INST_TYPE [beta|->``:'a # (action, 'a # 'b) alist``] MAP_ALL_DISTINCT_SANDWICH)
    >> qpat_assum `MAP _ _ = _ ++ _ ++ _`
       (fn thm => `ALL_DISTINCT ^(lhs(concl thm))`
                    by ASM_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND])
    >> disch_then drule >> disch_then (fn thm => fs[thm])
    >> fs[ALL_DISTINCT_APPEND] >> rfs[MAP_if_notmem_lemma]
    >> `e1 = FST h` by metis_tac[FST] >> rfs[] >> fs[]
    >> rfs[MAP_if_notmem_lemma] >> metis_tac[]
in
    
val compile_CONS_IMP = Q.prove(`!c. wf_chor c /\ s ≠ r /\
    (compile ((s,r,m)::c) = l)
                             ==> (compile c =
                           let laddr = 
                               if MEM r (endpoints c) then
                                 case SPLITP (λ(a,b). a = r) l of
                                     (l,l') => l ++ (if LENGTH(SND(HD l')) <= 1 then [] else [(FST(HD l'),TL(SND(HD l')))]) ++ (TL l')
                               else
                                 TL l
                           in if MEM s (endpoints c) then
                                 case SPLITP (λ(a,b). a = s) laddr of
                                     (l,l') => l ++ (if LENGTH(SND(HD l')) <= 1 then [] else [(FST(HD l'),TL(SND(HD l')))]) ++ (TL l')
                               else
                                 TL laddr)`,
rpt strip_tac
>> qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_compile
>> qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_FST_compile
>> fs[compile_def,endpoints_def,add_def,project_def,pairTheory.ELIM_UNCURRY] >> every_case_tac
>> qpat_x_assum `_ = l` (assume_tac o GSYM) >> fs[]
>> EVERY(map imp_res_tac [SPLITP_IMP,SPLITP_JOIN,                          
                          INST_TYPE [beta|->``:(action, 'a # 'b) alist``] MEM_SPLITP_lemma])
>> qspecl_then [`r`,`s`,`endpoints c`,`q`,`r'`] assume_tac (INST_TYPE [beta|->``:(action, 'a # 'b) alist``] MEM_SPLITP_lemma2)
>> qspecl_then [`r`,`s`,`endpoints c`,`q`,`r'`] assume_tac (INST_TYPE [beta|->``:(action, 'a # 'b) alist``] MEM_SPLITP_lemma3)
>> qspecl_then [`r`,`s`,`endpoints c`,`q`,`r'`] assume_tac (INST_TYPE [beta|->``:(action, 'a # 'b) alist``] MEM_SPLITP_lemma4)
>> rpt
    (first_x_assum (qspec_then `(λe. if e = s then (Send,r,m)::project s c
                                  else if e = r then (Receive,s,m)::project r c
                                     else project e c)` assume_tac))
>> fs[MAP_MAP_o,o_DEF] >> rfs[]
>> rpt(qpat_x_assum `SND _ ≠ []` mp_tac)
>> rpt(qpat_x_assum `_ ≠ []` (fn thm => assume_tac (ISPEC (lhs(rand(concl thm))) list_nchotomy) >> mp_tac thm))
>> rpt strip_tac >> fs[] >> rfs[] >> fs[]

>- tac1
>- tac2
>- tac3
>- tac2
>- tac1
>- tac4
>- tac7
>- tac4
>- tac5
>- (fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS] >> rfs[]
    >> fs[] >> Cases_on `q'` >> fs[SPLITP] >> rfs[]
    >> Cases_on `r'` >> fs[] >> rveq >> fs[]
    >> drule MAP_ALL_DISTINCT_SANDWICH_I
    >> fs[] >> PURE_REWRITE_TAC[Once(GSYM APPEND_ASSOC),APPEND]
    >> fs[] >> rpt strip_tac
    >> qpat_x_assum `endpoints _ = _` mp_tac
    >> rpt(qpat_x_assum `_ = (_ , if _ then _ else _)`
              (fn thm =>
               [ANTIQUOTE(mk_eq(mk_fst(lhs(concl thm)),rand(rator(rhs(concl thm)))))]
               (*`FST ^(lhs(concl thm)) = ^((rand(rator(rhs(concl thm)))))`*)
                  by(mp_tac thm >> metis_tac[FST])
               >> mp_tac thm)
          )
    >> fs[] >> pop_assum kall_tac >> fs[] >> rpt strip_tac
    >> fs[ALL_DISTINCT_APPEND,MAP_if_notmem_lemma])
>- (Cases_on `r''` >> fs[] >> rfs[]
    >- (rveq >> fs[MAP_EQ_APPEND,ALL_DISTINCT_APPEND] >> rfs[] >> fs[] >> rveq >> fs[ALL_DISTINCT_APPEND] >> rfs[]
        >> rpt(qpat_x_assum `_ = (_ , if _ then _ else _)`
           (fn thm =>
               [ANTIQUOTE(mk_eq(mk_fst(lhs(concl thm)),rand(rator(rhs(concl thm)))))]
                  by(mp_tac thm >> metis_tac[FST])
               >> mp_tac thm)
                 )
        >> rpt(qpat_x_assum `_ = (_ , _::_)`
           (fn thm =>
               [ANTIQUOTE(mk_eq(mk_fst(lhs(concl thm)),rand(rator(rhs(concl thm)))))]
                  by(mp_tac thm >> metis_tac[FST])
               >> mp_tac thm)
          )
        >> fs[EVERY_MAP,EVERY_MEM])
    >> Cases_on `h` >> Cases_on `h'`
    >> fs[] >> rename1 `[(_,TL r1)]` >> Cases_on `r1` >> fs[]
    >> rename1 `[(_,TL r2)]` >> Cases_on `r2` >> fs[]
    >> rveq >> fs[]
    >> drule MAP_ALL_DISTINCT_SANDWICH_I
    >> fs[] >> PURE_REWRITE_TAC[Once(GSYM APPEND_ASSOC),APPEND]
    >> fs[] >> rpt strip_tac
    >> drule APPEND_TWO_SANDWICHES_LEMMA
    >> fs[] >> rpt strip_tac
    >> rveq >> fs[MAP_EQ_CONS]
    >> fs[ALL_DISTINCT_APPEND,MAP_if_notmem_lemma,EVERY_MAP,EVERY_MEM]
    >> fs[MAP_EQ_APPEND] >> fs[ALL_DISTINCT_APPEND,MAP_if_notmem_lemma] >> metis_tac[])
>- (fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS] >> rfs[]
    >> fs[] >> Cases_on `q'` >> fs[SPLITP] >> rfs[]
    >> Cases_on `r'` >> fs[] >> rveq >> fs[]
    >> drule MAP_ALL_DISTINCT_SANDWICH_I
    >> fs[] >> PURE_REWRITE_TAC[Once(GSYM APPEND_ASSOC),APPEND]
    >> fs[] >> rpt strip_tac
    >> qpat_x_assum `endpoints _ = _` mp_tac
    >> rpt(qpat_x_assum `_ = (_ , if _ then _ else _)`
              (fn thm =>
               [ANTIQUOTE(mk_eq(mk_fst(lhs(concl thm)),rand(rator(rhs(concl thm)))))]
               (*`FST ^(lhs(concl thm)) = ^((rand(rator(rhs(concl thm)))))`*)
                  by(mp_tac thm >> metis_tac[FST])
               >> mp_tac thm)
          )
    >> fs[] >> pop_assum kall_tac >> fs[] >> rpt strip_tac
    >> fs[ALL_DISTINCT_APPEND,MAP_if_notmem_lemma])
>- tac1
>- tac4
>- tac7
>- tac4)

end

val SPLITP_compile_not_nil = Q.prove(
  `(SPLITP (λ(a,b). a = r) (compile ((s,r,m)::c)) = (q,r')) ==> ~NULL r'`,
  reverse(Cases_on `r'`)
  >- rw[]
  >> fs[SPLITP_NIL_SND_EVERY,o_DEF]
  >> rw[compile_def,add_def,endpoints_def]
  >> fs[EXISTS_MAP,EXISTS_MEM]);

val project_s_r_lemma = Q.prove(
  `(if e = s then (s,project s c)
   else if e = r then (r,project r c)
   else (e,project e c)) = (e,project e c)`,
  rw[]);

val clean_terminated_cons = Q.store_thm("clean_terminated_cons",
  `!a b l. clean_terminated((a,b)::l) = if b = [] then clean_terminated l else (a,b)::clean_terminated l`,
  rw[clean_terminated_def]);

val clean_terminated_nil_cons = Q.store_thm("clean_terminated_nil_cons",
  `!a b l. clean_terminated((a,[])::l) = clean_terminated l`,
  rw[clean_terminated_def]);

val perm_compile_CONS = Q.store_thm("perm_compile_CONS",
  `!s r m c. wf_chor c /\ s ≠ r ==>
  PERM (compile c) (
   clean_terminated(MAP (λ(x,a). if x = s then (s,TL a) else if x = r then (r,TL a) else (x,a))
       (compile ((s,r,m)::c))))`,
  rpt strip_tac
  >> `compile((s,r,m)::c) = compile((s,r,m)::c)` by rw[] 
  >> drule(GEN_ALL compile_CONS_IMP) >> rpt(disch_then drule)
  >> pop_assum kall_tac
  >> rpt strip_tac
  >> qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_endpoints
  >> qspec_then `(s,r,m)::c` assume_tac ALL_DISTINCT_compile
  >> qspec_then `c` assume_tac clean_terminated_compile
  >> every_case_tac >> fs[] >> every_case_tac >> fs[]
  >> imp_res_tac SPLITP_compile_not_nil  
  >> imp_res_tac SPLITP_IMP
  >> imp_res_tac SPLITP_JOIN
  >> fs[compile_def,o_DEF,EVERY_MEM,pairTheory.ELIM_UNCURRY,MAP_MAP_o,o_DEF,ALL_DISTINCT_APPEND,
        endpoints_def,add_def,project_def,project_s_r_lemma]
  >> rfs[]
  >> imp_res_tac project_nonmem_nil
  >> ASM_SIMP_TAC bool_ss [clean_terminated_nil_cons,PERM_REFL]
  >> fs[]);

val add_fst_def =
 Define `add_fst s l = (if MEM (FST s) (MAP FST l) then l else s::l)`

val PERM_add_fst_intro = Q.store_thm("PERM_add_fst_intro",
`!l l' e. PERM l l' ==> PERM(add_fst e l) (add_fst e l')`,
  rpt strip_tac >> fs[add_fst_def] >> rw[]
   >> imp_res_tac MEM_PERM >> fs[MEM_MAP] >> metis_tac[]);

val PERM_FILTER_EQ_ID = Q.store_thm("PERM_FILTER_EQ_ID",
  `PERM (FILTER f l) l = (FILTER f l = l)`,
  rw[EQ_IMP_THM] >> fs[FILTER_EQ_ID]
  >> imp_res_tac PERM_LENGTH
  >> CCONTR_TAC
  >> fs[NOT_EVERY]
  >> imp_res_tac LENGTH_FILTER_LESS
  >> fs[])

val ALL_DISTINCT_SND_EQ = Q.store_thm("ALL_DISTINCT_SND_EQ",
  `!l x y. (FST x = FST y) /\ ALL_DISTINCT (MAP FST l) /\ MEM x l /\ MEM y l ==>
    (SND x = SND y)`,
  Induct >> rpt strip_tac >> fs[]
  >> rveq >> fs[MEM_MAP] >> metis_tac[]);

val NO_FILTER_SANDWICH = Q.store_thm("NO_FILTER_SANDWICH",
  `(FILTER f l1 ++ FILTER f l2 =
      l1 ++ [y1] ++ l2) ==> F`,
  rpt strip_tac >> imp_res_tac LENGTH_EQ
  >> qspecl_then [`f`,`l1`] assume_tac LENGTH_FILTER_LEQ
  >> qspecl_then [`f`,`l2`] assume_tac LENGTH_FILTER_LEQ
  >> fs[]);


val invert_clean_terminated_lemma = Q.prove(
`(clean_terminated l = l) /\ ALL_DISTINCT(MAP FST l) /\ MEM s (MAP FST l) /\ MEM r (MAP FST l)
==>
PERM
(add_fst (s,[]) (add_fst (r,[])
 (FILTER (λ(a,b). b ≠ [])
         (MAP (λ(x,a). if x = s then (s,TL a) else if x = r then (r,TL a) else (x,a)) l))))
(MAP (λ(x,a). if x = s then (s,TL a) else if x = r then (r,TL a) else (x,a)) l)`,
rpt strip_tac >> fs[add_fst_def,FILTER_MAP,MEM_MAP,o_DEF,MEM_FILTER,clean_terminated_def] >> rw[]
>> rpt(pop_assum mp_tac) >> rw[]
>> rpt(pairarg_tac >> fs[]) >> rveq >> fs[]
>> rpt(pop_assum mp_tac) >> rw[]
>> fs[MEM_MAP,MEM_FILTER] >> rveq
>> rpt(pairarg_tac >> fs[])
>> rveq >> fs[]
>> rpt(pop_assum mp_tac) >> rw[]
>> fs[pairTheory.ELIM_UNCURRY]
>> TRY(fs[FILTER_MAP] >> match_mp_tac PERM_MAP
       >> fs[PERM_FILTER_EQ_ID]
       >> fs[FILTER_EQ_ID]
       >> fs[EVERY_MEM] >> rpt strip_tac
       >> pop_assum mp_tac
       >> rpt(IF_CASES_TAC)
       >> rpt strip_tac
       >> fs[] >> rfs[]
       >> metis_tac[ALL_DISTINCT_SND_EQ,FST,SND])
>- metis_tac[FST,SND]
>- metis_tac[FST,SND]
>> TRY(rename [`PERM ((FST y1,[])::MAP _ _) _`]
       >> qpat_assum `FST _ = FST _` kall_tac
       >> imp_res_tac ALL_DISTINCT_SND_EQ >> rfs[]
       >> rpt(qpat_x_assum `T` kall_tac)
       >> first_x_assum (qspec_then `(FST y1,TL(SND y1))` assume_tac) >> fs[]
       >> imp_res_tac FST_SND_EQ_JOIN >> pop_assum (assume_tac o GSYM)
       >> rveq >> fs[]
       >> fs[FILTER_EQ_ID,EVERY_MEM] >> rfs[]
       >> TRY(first_assum (qspec_then `y` assume_tac))
       >> fs[] >> rfs[]
       >> qpat_x_assum `MEM _ _` mp_tac
       >> simp[MEM_SPLIT] >> rpt strip_tac >> rveq >> fs[FILTER_APPEND,ALL_DISTINCT_APPEND]
       >> CONV_TAC PERM_NORMALISE_CONV
       >> match_mp_tac PERM_CONG
       >> strip_tac >> match_mp_tac PERM_MAP
       >> fs[PERM_FILTER_EQ_ID,FILTER_EQ_ID,EVERY_MEM,MEM_MAP]
       >> rpt strip_tac
       >> metis_tac[FST,SND])
>> TRY(rename [`PERM ((FST y1,[])::MAP _ _) _`]
       >> first_x_assum (qspec_then `(FST y1,TL(SND y1))` assume_tac) >> fs[]
       >> fs[FILTER_EQ_ID,EVERY_MEM] >> rfs[]
       >> rename [`MEM (FST y,_) l`]
       >> TRY(first_assum (qspec_then `y` assume_tac))
       >> fs[] >> rfs[]
       >> `FST y ≠ FST y1` by (CCONTR_TAC >> fs[] >> imp_res_tac ALL_DISTINCT_SND_EQ >> rfs[] >> fs[])
       >> qpat_x_assum `MEM y1 l` mp_tac
       >> simp[MEM_SPLIT] >> rpt strip_tac >> rveq >> fs[FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_MAP]
       >> CONV_TAC PERM_NORMALISE_CONV
       >> TRY(first_assum (qspec_then `y1` assume_tac)) >> fs[] >> rfs[]
       >> match_mp_tac PERM_CONG
       >> strip_tac >> match_mp_tac PERM_MAP
       >> fs[PERM_FILTER_EQ_ID,FILTER_EQ_ID,EVERY_MEM,MEM_MAP]
       >> rw[] >> fs[] >> rfs[]
       >> metis_tac[ALL_DISTINCT_SND_EQ,FST,SND])
>- metis_tac[FST,SND]
>- metis_tac[FST,SND]
>> first_x_assum (qspec_then `(FST y',TL(SND y'))` assume_tac)
>> fs[]
>- (first_x_assum (qspec_then `(FST y,TL(SND y))` assume_tac)
    >> fs[] >> `FST y ≠ FST y'` by(CCONTR_TAC >> fs[] >> imp_res_tac ALL_DISTINCT_SND_EQ >> rfs[] >> fs[])
    >> first_x_assum(qspec_then `y` assume_tac) >> fs[] >> rfs[]
    >> fs[FILTER_EQ_ID]
    >> `y ≠ y'` by metis_tac[] >> drule MEM_SPLIT2 >> rpt(disch_then drule) >> strip_tac
    >> fs[FILTER_APPEND]
    >> CONV_TAC PERM_NORMALISE_CONV
    >> rpt(match_mp_tac PERM_CONG >> strip_tac) >> match_mp_tac PERM_MAP
    >> fs[PERM_FILTER_EQ_ID,FILTER_EQ_ID,EVERY_MEM,MEM_MAP,ALL_DISTINCT_APPEND] >> rw[]
    >> fs[] >> rfs[] >> metis_tac[ALL_DISTINCT_SND_EQ,FST,SND])
>> first_x_assum (qspec_then `y'` assume_tac)
>> fs[] >> rfs[]
>> first_x_assum (qspec_then `(FST y,TL(SND y))` assume_tac)
>> fs[] >> rfs[]
>> first_x_assum (qspec_then `y` assume_tac)
>> fs[] >> rfs[]);

val highly_specific_if_tuple_rewrites = Q.prove(
`(FST (if FST x = s then (s,t) else if FST x = r then (r,t') else x)) = (FST x)
`,
rw[] >> fs[]);

val if_id_rewrite = Q.prove(`(if a = s then s else a) = a`,rw[])

val if_tup_pushout = Q.prove(
  `(if a = s then (s,t) else (a,t')) = (a,(if a = s then t else t'))`,rw[]);

val ALOOKUP_TABULATE_IF = Q.store_thm("ALOOKUP_TABULATE_IF",
  `ALOOKUP (MAP (λk. (k,f k)) l) x = if MEM x l then SOME (f x) else NONE`,
  rw[ALOOKUP_TABULATE,ALOOKUP_NONE,MAP_MAP_o,o_DEF]);
                            
val if_reconstruct_list = Q.prove(`!l s r v1 v2. (HD((THE (ALOOKUP l s))) = v1) /\ (HD((THE (ALOOKUP l r))) = v2) /\ ALL_DISTINCT (MAP FST l)
     /\ EVERY (λ(a,b). b ≠ []) l ==> (MAP
     (λx.
        (FST x,
         if FST x = s then v1::TL (SND x)
         else if FST x = r then v2::TL (SND x)
         else SND x)) l = l)`,
  Induct >- fs[]
  >> Cases >> rpt strip_tac >> fs[] >> rw[] >> fs[CONS,NULL_EQ,MAP_if_notmem_lemma3]
  >- metis_tac[MAP_if_notmem_lemma3]
  >> rename [`k2 ≠ k1`] >> first_x_assum(qspecl_then [`k1`,`k2`] assume_tac)
  >> drule (INST_TYPE [gamma|->beta] MAP_if_notmem_lemma4)
  >> strip_tac >> fs[]);

val perm_compile_CONS' = Q.store_thm("perm_compile_CONS'",
  `!s r m c l. wf_chor c /\ s ≠ r /\ (clean_terminated l = l) /\ ALL_DISTINCT(MAP FST l) /\ (HD((THE (ALOOKUP l s))) = (Send,r,m)) /\ (HD((THE (ALOOKUP l r))) = (Receive,s,m)) /\ MEM s (MAP FST l) /\ MEM r (MAP FST l) /\ PERM (clean_terminated(MAP (λ(x,a). if x = s then (s,TL a) else if x = r then (r,TL a) else (x,a)) l)) (compile c) ==>
  PERM (compile ((s,r,m)::c)) l`,
  rpt strip_tac  
  >> `!x. MEM x (endpoints c) ==> MEM x (MAP FST l)`
      by(drule(ISPEC ``FST`` PERM_MAP) >> rpt strip_tac
         >> drule PERM_MEM_EQ >> disch_then (qspec_then `x` assume_tac)
         >> fs[MEM_MAP,clean_terminated_def,MEM_FILTER,FILTER_EQ_ID,
               EVERY_MEM,compile_def,ELIM_UNCURRY]
         >> metis_tac[FST,SND])
  >> pop_assum mp_tac
  >> drule PERM_TRANS
  >> drule perm_compile_CONS >> disch_then drule
  >> disch_then (qspec_then `m` assume_tac)
  >> disch_then drule
  >> ntac 2 (pop_assum kall_tac)
  >> disch_then (assume_tac o PURE_ONCE_REWRITE_RULE [PERM_SYM])
  >> strip_tac
  >> fs[compile_def,clean_terminated_def,(*FILTER_MAP,*)o_DEF,MAP_MAP_o,project_def]
  >> fs[endpoints_def,add_def] >> rw[] >> fs[]
  >> qspec_then `c` assume_tac EVERY_project_nonempty
  >> fs[GSYM FILTER_EQ_ID]
  >> fs[if_lemma3]
  >- (drule PERM_add_fst_intro >> qpat_x_assum `PERM _ _` kall_tac
      >> disch_then (qspec_then `(r,[])` assume_tac)
      >> drule PERM_add_fst_intro >> pop_assum kall_tac
      >> disch_then (qspec_then `(s,[])` mp_tac)
      >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> qpat_x_assum `!x. MEM x (endpoints _) ==> _` imp_res_tac
      >> `clean_terminated l = l` by fs[clean_terminated_def]
      >> drule invert_clean_terminated_lemma >> pop_assum kall_tac
      >> rpt(disch_then drule) >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> drule PERM_TRANS >> pop_assum kall_tac >> disch_then drule
      >> simp[FILTER_MAP,o_DEF] >> simp[add_fst_def,MAP_MAP_o,o_DEF]
      >> strip_tac
      >> drule (INST_TYPE [beta|->alpha] PERM_MAP)
      >> disch_then(qspec_then `(λ(e,l).
                            (e,
                             if e = s then (Send,r,m)::l
                             else if e = r then (Receive,s,m)::l
                             else l))` assume_tac)
      >> fs[MAP_MAP_o,o_DEF]
      >> pop_assum(assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> match_mp_tac PERM_TRANS
      >> asm_exists_tac >> fs[]
      >> pop_assum mp_tac
      >> simp[ELIM_UNCURRY] >> fs[highly_specific_if_tuple_rewrites]
      >> fs[FILTER_EQ_ID,if_reconstruct_list])
  >- (qpat_x_assum `!x. MEM x (endpoints _) ==> _` imp_res_tac
      >> imp_res_tac project_nonmem_nil >> fs[] >> rfs[]
      >> qspec_then `c` assume_tac clean_terminated_compile
      >> fs[clean_terminated_def,compile_def] >> pop_assum kall_tac
      >> `ALOOKUP l r = SOME [(Receive,s,m)]`
           by(drule ALOOKUP_PERM >> disch_then(qspec_then `r` mp_tac)
              >> simp[MAP_MAP_o,o_DEF,ALL_DISTINCT_endpoints]
              >> qpat_x_assum `MEM r (MAP FST l)` mp_tac
              >> fs[FILTER_EQ_ID]
              >> fs[MEM_MAP] >> simp[MEM_SPLIT] >> strip_tac >> fs[]
              >> rveq >> fs[ALL_DISTINCT_APPEND,ALOOKUP_APPEND, GSYM ALOOKUP_NONE] >> rfs[]
              >> rename [`ALOOKUP [tup] _`] >> Cases_on `tup` >> fs[]>> rfs[]
              >> fs[FILTER_APPEND,ALOOKUP_compile,ALOOKUP_NONE]
              >> rpt strip_tac
              >> fs[MEM_MAP,MEM_FILTER]
              >> rpt(first_x_assum(qspec_then `(q,TL r)` assume_tac)) >> fs[]
              >> rfs[] >> TRY(Cases_on `r` >> fs[] >> NO_TAC)
              >> qpat_x_assum `¬MEM _ (if _ then _ else _)` mp_tac >> rw[]
              >> Cases_on `r` >> fs[])
      >> imp_res_tac ALOOKUP_MEM
      >> drule PERM_add_fst_intro >> qpat_x_assum `PERM _ _` kall_tac
      >> disch_then (qspec_then `(r,[])` assume_tac)
      >> drule PERM_add_fst_intro >> pop_assum kall_tac
      >> disch_then (qspec_then `(s,[])` mp_tac)
      >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> `clean_terminated l = l` by fs[clean_terminated_def]
      >> drule invert_clean_terminated_lemma >> pop_assum kall_tac
      >> rpt(disch_then drule) >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> drule PERM_TRANS >> pop_assum kall_tac >> disch_then drule
      >> simp[add_fst_def,MAP_MAP_o,o_DEF]
      >> strip_tac
      >> drule (INST_TYPE [beta|->alpha] PERM_MAP)
      >> disch_then(qspec_then `(λ(e,l).
                                  (e,
                                   if e = s then (Send,r,m)::l
                                   else if e = r then (Receive,s,m)::l
                                   else l))` assume_tac)
      >> fs[MAP_MAP_o,o_DEF]
      >> pop_assum(assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> rfs[]
      >> match_mp_tac PERM_TRANS
      >> asm_exists_tac >> fs[]
      >> pop_assum mp_tac
      >> simp[ELIM_UNCURRY] >> fs[highly_specific_if_tuple_rewrites]
      >> fs[FILTER_EQ_ID,if_reconstruct_list])
  >- (qpat_x_assum `!x. MEM x (endpoints _) ==> _` imp_res_tac
      >> imp_res_tac project_nonmem_nil >> fs[] >> rfs[]
      >> fs[MAP_if_notmem_lemma5] >> fs[if_lemma4]                   
      >> qspec_then `c` assume_tac clean_terminated_compile
      >> fs[clean_terminated_def,compile_def] >> pop_assum kall_tac
      >> `ALOOKUP l s = SOME [(Send,r,m)]`
           by(drule ALOOKUP_PERM >> disch_then(qspec_then `s` mp_tac)
              >> disch_then(mp_tac o REWRITE_RULE [FILTER_MAP])
              >> simp[MAP_MAP_o,o_DEF,ALL_DISTINCT_endpoints]
              >> simp[ISPEC ``(λ(a,b). b ≠ [])`` COND_RAND]
              >> simp[ISPEC ``FST`` COND_RAND]
              >> fs[if_id_rewrite] >> fs[FILTER_ALL_DISTINCT,ALL_DISTINCT_endpoints]
              >> fs[if_tup_pushout,ALOOKUP_TABULATE_IF,MEM_FILTER,ALOOKUP_NONE]
              >> fs[MEM_MAP,MEM_FILTER]
              >> simp[highly_specific_if_tuple_rewrites]
              >> fs[FILTER_EQ_ID]
              >> fs[MEM_MAP]
              >> disch_then (qspec_then `(FST y,TL(SND y))` assume_tac)
              >> rfs[] >> first_x_assum (qspec_then `y` assume_tac)
              >> rfs[] >> fs[] >> Cases_on `y` >> fs[]
              >> imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
              >> fs[] >> Cases_on `r'` >> fs[] >> rfs[EVERY_MEM]
              >> qpat_x_assum `!e. MEM e l ==> _` imp_res_tac >> fs[])
      >> imp_res_tac ALOOKUP_MEM
      >> drule PERM_add_fst_intro >> qpat_x_assum `PERM _ _` kall_tac
      >> disch_then (qspec_then `(r,[])` assume_tac)
      >> drule PERM_add_fst_intro >> pop_assum kall_tac
      >> disch_then (qspec_then `(s,[])` mp_tac)
      >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> `clean_terminated l = l` by fs[clean_terminated_def]
      >> drule invert_clean_terminated_lemma >> pop_assum kall_tac
      >> rpt(disch_then drule) >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> drule PERM_TRANS >> pop_assum kall_tac >> disch_then drule
      >> simp[add_fst_def,MAP_MAP_o,o_DEF]
      >> strip_tac
      >> drule (INST_TYPE [beta|->alpha] PERM_MAP)
      >> disch_then(qspec_then `(λ(e,l).
                                  (e,
                                   if e = s then (Send,r,m)::l
                                   else if e = r then (Receive,s,m)::l
                                   else l))` assume_tac)
      >> fs[MAP_MAP_o,o_DEF]
      >> pop_assum(assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> rfs[]
      >> match_mp_tac PERM_TRANS
      >> asm_exists_tac >> fs[]
      >> pop_assum mp_tac
      >> simp[ELIM_UNCURRY] >> fs[highly_specific_if_tuple_rewrites]
      >> fs[FILTER_EQ_ID,if_reconstruct_list])  
  >- (qpat_x_assum `!x. MEM x (endpoints _) ==> _` imp_res_tac
      >> imp_res_tac project_nonmem_nil >> fs[] >> rfs[]
      >> fs[MAP_if_notmem_lemma6]
      >> qspec_then `c` assume_tac clean_terminated_compile
      >> fs[clean_terminated_def,compile_def] >> pop_assum kall_tac
      >> `ALOOKUP l s = SOME [(Send,r,m)]`
           by(drule ALOOKUP_PERM >> disch_then(qspec_then `s` mp_tac)
              >> disch_then(mp_tac o REWRITE_RULE [FILTER_MAP])
              >> simp[MAP_MAP_o,o_DEF,ALL_DISTINCT_endpoints]
              >> simp[ISPEC ``(λ(a,b). b ≠ [])`` COND_RAND]
              >> simp[ISPEC ``FST`` COND_RAND]
              >> fs[if_id_rewrite] >> fs[FILTER_ALL_DISTINCT,ALL_DISTINCT_endpoints]
              >> fs[if_tup_pushout,ALOOKUP_TABULATE_IF,MEM_FILTER,ALOOKUP_NONE]
              >> fs[MEM_MAP,MEM_FILTER]
              >> simp[highly_specific_if_tuple_rewrites]
              >> fs[FILTER_EQ_ID]
              >> fs[MEM_MAP]
              >> disch_then (qspec_then `(FST y,TL(SND y))` assume_tac)
              >> rfs[] >> first_x_assum (qspec_then `y` assume_tac)
              >> rfs[] >> fs[] >> Cases_on `y` >> fs[]
              >> imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
              >> fs[] >> Cases_on `r'` >> fs[] >> rfs[EVERY_MEM]
              >> qpat_x_assum `!e. MEM e l ==> _` imp_res_tac >> fs[])
      >> `ALOOKUP l r = SOME [(Receive,s,m)]`
           by(drule ALOOKUP_PERM >> disch_then(qspec_then `r` mp_tac)
              >> simp[MAP_MAP_o,o_DEF,ALL_DISTINCT_endpoints]
              >> qpat_x_assum `MEM r (MAP FST l)` mp_tac
              >> fs[FILTER_EQ_ID]
              >> fs[MEM_MAP] >> simp[MEM_SPLIT] >> strip_tac >> fs[]
              >> rveq >> fs[ALL_DISTINCT_APPEND,ALOOKUP_APPEND, GSYM ALOOKUP_NONE] >> rfs[]
              >> rename [`ALOOKUP [tup] _`] >> Cases_on `tup` >> fs[]>> rfs[]
              >> fs[FILTER_APPEND,ALOOKUP_compile,ALOOKUP_NONE]
              >> rpt strip_tac
              >> fs[MEM_MAP,MEM_FILTER]
              >> rpt(first_x_assum(qspec_then `(q,TL r)` assume_tac)) >> fs[]
              >> rfs[] >> TRY(Cases_on `r` >> fs[] >> NO_TAC)
              >> qpat_x_assum `¬MEM _ (if _ then _ else _)` mp_tac >> rw[]
              >> Cases_on `r` >> fs[])
      >> imp_res_tac ALOOKUP_MEM
      >> drule PERM_add_fst_intro >> qpat_x_assum `PERM _ _` kall_tac
      >> disch_then (qspec_then `(r,[])` assume_tac)
      >> drule PERM_add_fst_intro >> pop_assum kall_tac
      >> disch_then (qspec_then `(s,[])` mp_tac)
      >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> `clean_terminated l = l` by fs[clean_terminated_def]
      >> drule invert_clean_terminated_lemma >> pop_assum kall_tac
      >> rpt(disch_then drule) >> disch_then (assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> drule PERM_TRANS >> pop_assum kall_tac >> disch_then drule
      >> simp[add_fst_def,MAP_MAP_o,o_DEF]
      >> strip_tac
      >> drule (INST_TYPE [beta|->alpha] PERM_MAP)
      >> disch_then(qspec_then `(λ(e,l).
                                  (e,
                                   if e = s then (Send,r,m)::l
                                   else if e = r then (Receive,s,m)::l
                                   else l))` assume_tac)
      >> fs[MAP_MAP_o,o_DEF]
      >> pop_assum(assume_tac o CONV_RULE(ONCE_REWRITE_CONV [PERM_SYM]))
      >> rfs[]
      >> match_mp_tac PERM_TRANS
      >> asm_exists_tac >> fs[]
      >> pop_assum mp_tac
      >> simp[ELIM_UNCURRY] >> fs[highly_specific_if_tuple_rewrites]
      >> fs[FILTER_EQ_ID,if_reconstruct_list]));

val PERM_clean_terminated = Q.store_thm("PERM_clean_terminated",
  `!l l'. PERM l l' ==> PERM(clean_terminated l) (clean_terminated l')`,
  metis_tac[clean_terminated_def,PERM_FILTER]);

val compile_ALOOKUP_HD_send = Q.store_thm("compile_ALOOKUP_HD_send",
  `!s r m c. HD(THE(ALOOKUP(compile((s,r,m)::c)) s)) = (Send,r,m)`,
  rpt strip_tac >> rw[compile_def,project_def,endpoints_def,add_def]
  >> fs[] >> rw[ALOOKUP_TABULATE_IF])

val compile_ALOOKUP_HD_receive = Q.store_thm("compile_ALOOKUP_HD_receive",
`!s r m c. s ≠ r ==> (HD(THE(ALOOKUP(compile ((s,r,m)::c)) r)) = (Receive,s,m))`,
  rpt strip_tac >> rw[compile_def,project_def,endpoints_def,add_def]
  >> fs[] >> rw[ALOOKUP_TABULATE_IF]);

val compile_reduce_compile_lemma = Q.prove(
`!p a p'. trans p a p' ==> (a = NONE) ==> (?c. (p = compile c) /\ wf_chor c) ==> (?c. wf_chor c /\ PERM (clean_terminated p') (compile c))`,
  rpt strip_tac >> rveq
  >> imp_res_tac reduces_sender_receiver
  >> qpat_x_assum `trans _ _ _` kall_tac
  >> fs[] >> rveq
  >> `MEM (r,(Receive,s,m)::evs) (compile c)` by fs[]
  >> drule compile_receive_has_exchange >> rpt(disch_then drule)
  >> rpt strip_tac
  >> qexists_tac `c' ++ c''`
  >> fs[wf_chor_def]
  >> qspec_then `c` assume_tac ALL_DISTINCT_compile
  >> qspec_then `c` mp_tac clean_terminated_compile
  >> strip_tac
  >> drule LENGTH_EQ
  >> strip_tac >> qpat_x_assum `_ = compile c` mp_tac
  >> rfs[clean_terminated_append,clean_terminated_single]
  >> disch_then (assume_tac o GSYM)
  >> imp_res_tac ALL_DISTINCT_DOUBLE_SANDWICH
  >> rpt(qpat_x_assum `_ = clean_terminated _` (assume_tac o GSYM))
  >> fs[] >> rveq >> rpt(qpat_x_assum `T` kall_tac)
  >> rpt(qpat_x_assum `clean_terminated _ = _` kall_tac)
  >> rpt(qpat_x_assum `ALL_DISTINCT _` kall_tac)
  >> imp_res_tac PERM_INTRO
  >> qpat_x_assum `compile _ = _` kall_tac
  >> rpt(pop_assum mp_tac)
  >> EVERY(map (Q.SPEC_TAC o W pair) [`evs`,`evs'`,`ll`,`lc`,`lr`,`s`,`r`,`m`,`c''`,`c'`])
  >> (Induct
      >- (rpt strip_tac >> fs[]
          >> qspec_then `[(s,r,m)] ++ c''` assume_tac ALL_DISTINCT_FST_compile
(*          >> `evs = []` by
            (`wf_chor c''` by rw[wf_chor_def]
             >> drule compile_rcv_evs_lemma >> disch_then drule >> strip_tac
             >> qspec_then `[(s,r,m)] ++ c''` assume_tac ALL_DISTINCT_compile
             >> drule ALL_DISTINCT_PERM >> disch_then (fn thm => fs[thm])
             >> fs[ALL_DISTINCT_APPEND] >> fs[PERM_DEF]
             >> qpat_x_assum `!x. FILTER _ _ = _` (qspec_then `(r,evs ++ [(Receive,s,m)] ++ evs')` assume_tac)
             >> fs[FILTER_APPEND]
             >> rfs[NOT_MEM_FILTER]
             >> `!x. ($= (r,evs ++ [(Receive,s,m)] ++ evs')) x ==> ($= r ∘ FST) x`
                  by(Cases_on `x`>>rw[])
             >> drule IS_SUBLIST_FILTER_MONO_SINGLE
             >> rpt(disch_then drule) >> Cases_on `evs` >> fs[] >> Cases_on `h` >> fs[]
             >> Cases_on `r'` >> fs[])*)
          >> rveq >> fs[]          
          >> drule(ISPEC ``FST`` PERM_MAP)
          >> strip_tac >> drule ALL_DISTINCT_PERM
          >> disch_then (fn thm => FULL_SIMP_TAC bool_ss [thm,GSYM CONS_APPEND])
          >> pop_assum kall_tac
          >> fs[ALL_DISTINCT_APPEND]
          >> drule (INST_TYPE [beta|->alpha] PERM_MAP)
          >> disch_then (Q.ISPEC_THEN
                         `(λ(x,a:(action,'a # 'b) alist). if x = s then (s,TL a)
                               else if x = r then (r,TL a)
                               else (x,a))` assume_tac)
          >> fs[MAP_APPEND] >> rfs[] >> rfs[MAP_if_notmem_lemma2]
          >> fs[pair_lam_id]
          >> drule PERM_clean_terminated >> pop_assum kall_tac >> strip_tac
          >> pop_assum mp_tac
          >> imp_res_tac clean_terminated_PERM
          >> fs[clean_terminated_compile,clean_terminated_append,clean_terminated_single]
          >> imp_res_tac clean_terminated_double_sandwich_IMP
          >> fs[] >> strip_tac
          >> `wf_chor c''` by rw[wf_chor_def]
          >> drule perm_compile_CONS >> disch_then(qspecl_then [`s`,`r`] mp_tac) >> fs[]
          >> disch_then (qspec_then `m` (assume_tac o CONV_RULE(ONCE_REWRITE_CONV[PERM_SYM])))
          >> match_mp_tac PERM_TRANS
          >> rpt(qpat_x_assum `PERM (clean_terminated _) _` mp_tac)
          >> rpt(pop_assum kall_tac)
          >> rpt strip_tac >> metis_tac[PERM_SYM]))
  >> rpt strip_tac
  >> Cases_on `h`
  >> rename [`EVERY _ ((s1,tup)::_)`]
  >> Cases_on `tup`
  >> rename [`EVERY _ ((s1,r1,m1)::_)`]
  >> `wf_chor(c' ++ [(s,r,m)] ++ c'')` by fs[wf_chor_def]
  >> `s1 ≠ r1` by fs[]
  >> drule perm_compile_CONS >> disch_then drule
  >> disch_then (qspec_then `m1` mp_tac) >> pop_assum mp_tac
  >> `EVERY (λ(a,b,c). a ≠ b) c'` by fs[]
  >> `EVERY (λx. x ≠ (s,r,m)) c'` by fs[]
  >> `EVERY (λ(s',r',m'). s' ≠ r ∧ r' ≠ r) c'` by fs[]
  >> `r1 ≠ r` by fs[]
  >> `s1 ≠ s`
     by(rpt strip_tac >> fs[] >> rveq
        >> drule (GEN_ALL compile_snd_evs_lemma)
        >> disch_then(qspecl_then [`s`,`r1`,`m1`] mp_tac) >> disch_then drule
        >> qspec_then `(s,r1,m1)::c' ++ [(s,r,m)] ++ c''` assume_tac ALL_DISTINCT_FST_compile
        >> drule (ISPEC ``FST`` PERM_MAP) >> strip_tac
        >> drule ALL_DISTINCT_PERM >> full_simp_tac std_ss [APPEND]
        >> strip_tac >> drule ALL_DISTINCT_FST_FILTER_IMP
        >> disch_then(qspecl_then [`s`,`[(Send,r,m)]`] mp_tac)
        >> simp[]
        >> qspec_then `(s,r1,m1)::c' ++ [(s,r,m)] ++ c''` assume_tac ALL_DISTINCT_compile     
        >> drule ALL_DISTINCT_PERM_FILTER >> fs[] >> disch_then drule >> fs[]
        >> disch_then(qspec_then `s` mp_tac) >> rpt strip_tac
        >> fs[compile_snd_evs_lemma] >> fs[FILTER_APPEND,ALL_DISTINCT_APPEND]
        >> rpt strip_tac >> fs[ALL_DISTINCT_APPEND] >> rfs[NOT_MEM_FILTER_FST])
  >> `r1 ≠ s`
     by(rpt strip_tac >> fs[] >> rveq
        >> drule (GEN_ALL compile_rcv_evs_lemma)
        >> disch_then(qspecl_then [`s1`,`r1`,`m1`] mp_tac) >> disch_then drule
        >> qspec_then `(s1,r1,m1)::c' ++ [(r1,r,m)] ++ c''` assume_tac ALL_DISTINCT_FST_compile
        >> drule (ISPEC ``FST`` PERM_MAP) >> strip_tac
        >> drule ALL_DISTINCT_PERM >> full_simp_tac std_ss [APPEND]
        >> strip_tac >> drule ALL_DISTINCT_FST_FILTER_IMP
        >> disch_then(qspecl_then [`r1`,`(Send,r,m)::evs''`] mp_tac)
        >> simp[]
        >> qspec_then `(s1,r1,m1)::c' ++ [(r1,r,m)] ++ c''` assume_tac ALL_DISTINCT_compile
        >> drule ALL_DISTINCT_PERM_FILTER >> fs[] >> disch_then drule
        >> fs[FILTER_APPEND,APPEND_EQ_SING])
  >> `s1 ≠ r`
     by(rpt strip_tac >> fs[])
  >> ntac 4 (pop_assum mp_tac)
  >> first_x_assum drule >> disch_then drule
  >> disch_then (qspec_then `c''` mp_tac)
  >> ntac 3 (disch_then drule)
  >> rpt strip_tac
  >> PURE_ONCE_REWRITE_TAC[PERM_SYM]
  >> PURE_ONCE_REWRITE_TAC[last(CONJUNCTS APPEND)]
  >> match_mp_tac perm_compile_CONS'
  >> rpt CONJ_TAC
  >> TRY(Q.MATCH_RENAME_TAC `wf_chor(_ ++ _)` >> fs[wf_chor_def])
  >> TRY(Q.MATCH_RENAME_TAC `_ ≠ _` >> fs[])
  >> TRY(Q.MATCH_RENAME_TAC `clean_terminated _ = _`
         >> fs[clean_terminated_append]
         >> ntac 3 (pop_assum mp_tac)
         >> drule clean_terminated_PERM >> simp[clean_terminated_compile]
         >> fs[clean_terminated_append]
         >> strip_tac
         >> fs[clean_terminated_append,clean_terminated_single]
         >> drule clean_terminated_double_sandwich_IMP
         >> rpt strip_tac >> rw[] >> fs[clean_terminated_def])
  >> TRY(Q.MATCH_RENAME_TAC `ALL_DISTINCT (MAP FST _)`
         >> fs[] >> ntac 3 (pop_assum mp_tac)
         >> imp_res_tac(ISPEC ``FST`` PERM_MAP)
         >> drule ALL_DISTINCT_PERM
         >> fs[ALL_DISTINCT_FST_compile]
         >> rpt strip_tac
         >> rw[] >> fs[ALL_DISTINCT_APPEND] >> rpt strip_tac >> rfs[])
  >> TRY(Q.MATCH_RENAME_TAC `HD _ = (Send,_,_)`
         >> ntac 3 (pop_assum kall_tac)
         >> drule ALOOKUP_PERM
         >> simp[ALL_DISTINCT_FST_compile]
         >> disch_then (qspec_then `s1` mp_tac)
(*         >> simp[compile_ALOOKUP_HD_send]*)
         >> disch_then(mp_tac o MATCH_MP (ISPEC ``THE`` ext))
         >> disch_then(mp_tac o MATCH_MP (ISPEC ``HD`` ext))
         >> disch_then(mp_tac o GSYM)
         >> simp[compile_ALOOKUP_HD_send]
         >> simp[ALOOKUP_APPEND]
         >> rpt CASE_TAC >> fs[])
  >> TRY(Q.MATCH_RENAME_TAC `HD _ = (Receive,_,_)`
         >> qpat_x_assum `s1 ≠ r1` mp_tac
         >> ntac 2 (pop_assum kall_tac) >> strip_tac
         >> drule ALOOKUP_PERM
         >> simp[ALL_DISTINCT_FST_compile]
         >> disch_then (qspec_then `r1` mp_tac)
         >> simp[compile_ALOOKUP_HD_receive]
         >> disch_then(mp_tac o MATCH_MP (ISPEC ``THE`` ext))
         >> disch_then(mp_tac o MATCH_MP (ISPEC ``HD`` ext))
         >> disch_then(mp_tac o GSYM)
         >> simp[compile_ALOOKUP_HD_receive]
         >> simp[ALOOKUP_APPEND]
         >> rpt CASE_TAC >> fs[] >> rveq >> Cases_on `evs` >> fs[])
  >> TRY(Q.MATCH_RENAME_TAC `MEM _ (MAP FST _)`
         >> ntac 3 (pop_assum mp_tac)
         >> drule(ISPEC ``FST`` PERM_MAP)
         >> disch_then(mp_tac o MATCH_MP MEM_PERM)
         >> disch_then(fn thm => qspec_then `s1` mp_tac thm >>
                                 qspec_then `r1` mp_tac thm)
         >> simp[MAP_FST_compile,endpoints_def,MEM_add]
         >> imp_res_tac ALL_DISTINCT_FST_COMPILE_PERM
         >> rpt strip_tac >> fs[ALL_DISTINCT_APPEND,ISPEC ``MAP FST`` COND_RAND]
         >> fs[ISPEC ``MEM s`` COND_RAND |> CONV_RULE(DEPTH_CONV BETA_CONV)])
  >> TRY(Q.MATCH_RENAME_TAC `PERM (clean_terminated (MAP _ _)) (compile _)`
         >> pop_assum mp_tac
         >> drule(INST_TYPE[alpha|->beta] PERM_MAP)
         >> disch_then(qspec_then `(λ(x,a). if x = s1 then (s1,TL a)
                                   else if x = r1 then (r1,TL a)
                                            else (x,a))` mp_tac)
         >> simp_tac std_ss [APPEND]
         >> disch_then(assume_tac o MATCH_MP PERM_clean_terminated)
         >> strip_tac >> drule PERM_TRANS >> disch_then drule
         >> ntac 2 (pop_assum kall_tac) >> fs[if_tup_pushout,clean_terminated_append,clean_terminated_single] >> Cases_on `r = r1` >> fs[TL_append] >> rfs[]
         >> TRY(strip_tac >> first_x_assum drule
         >> fs[clean_terminated_single]
         >> fs[ISPEC ``MAP f`` COND_RAND]
         >> fs[ISPEC ``clean_terminated`` COND_RAND,clean_terminated_single]
         >> fs[clean_terminated_def] >> rw[])))

val compile_reduce_compile = Q.store_thm("compile_reduce_compile",
  `!c p. wf_chor c /\ reduction (compile c) p ==> ?c'. wf_chor c' /\ PERM (clean_terminated p) (compile c')`,
  rw[reduction_def] >> imp_res_tac compile_reduce_compile_lemma >>
  metis_tac[])

val compile_reduce_perm_compile = Q.store_thm("compile_reduce_perm_compile",
`!c p p'. wf_chor c /\ PERM (clean_terminated p) (compile c) /\ reduction p p' ==> ?c'. wf_chor c' /\ PERM (clean_terminated p') (compile c')`,
  rpt strip_tac
  >> fs[reduction_def] >> imp_res_tac trans_clean_terminated
  >> imp_res_tac trans_perm
  >> drule compile_reduce_compile >> fs[reduction_def]
  >> disch_then drule >> drule PERM_clean_terminated
  >> rpt strip_tac
  >> asm_exists_tac >> metis_tac[PERM_TRANS]);
                                        
val compile_weak_reduce_compile = Q.store_thm("compile_weak_reduce_compile",
  `!c p. wf_chor c /\ reduction^* (compile c) p ==> ?c'. wf_chor c' /\ PERM (clean_terminated p) (compile c')`,
  rpt strip_tac
  >> Q.ISPECL_THEN [`reduction`,`\p. ?c. (wf_chor c /\ PERM(clean_terminated p) (compile c))`]
                   assume_tac (GEN_ALL RTC_lifts_invariants)
  >> assume_tac (GEN_ALL compile_reduce_perm_compile)
  >> `!c. PERM (clean_terminated (compile c)) (compile c)` by(fs[clean_terminated_compile])
  >> metis_tac[]);

val deadlocked_perm = Q.store_thm("deadlocked_perm",
 `!p q. PERM p q ==> (deadlocked p = deadlocked q)`,
  rpt strip_tac >> fs[deadlocked_def,reduces_def,transitions_def,reduction_def]
  >> metis_tac[trans_perm,PERM_SYM]);

val reduction_perm = Q.store_thm("reduction_perm",
`!p q. PERM p q /\ reduction p p' ==> ?q'. reduction q q' /\ PERM p' q'`,
rpt strip_tac >> fs[reduction_def] >> metis_tac[trans_perm])

val weak_reduction_perm = Q.store_thm("weak_reduction_perm",
  `!p p'. reduction^* p p' ==> !q. PERM p q ==> ?q'. reduction^* q q' /\ PERM p' q'`,
  ho_match_mp_tac RTC_INDUCT
  >> rpt strip_tac
  >- (qexists_tac `q` >> fs[])
  >> imp_res_tac reduction_perm
  >> first_x_assum drule >> rpt strip_tac
  >> metis_tac[PERM_TRANS,RTC_RULES])
                                
val deadlocked_clean_terminated = Q.store_thm("deadlocked_clean_terminated",
 `!p. deadlocked(clean_terminated p) = deadlocked p`,
  fs[deadlocked_def,reduces_def,transitions_def,reduction_def]
  >> metis_tac[trans_clean_terminated,trans_clean_terminated']);

val deadlock_free_def = Define
  `deadlock_free p = (!p'. reduction^* p p' ==> ¬deadlocked p')`;

val deadlock_free_perm = Q.store_thm("deadlock_free_perm",
  `!p q. PERM p q ==> (deadlock_free p = deadlock_free q)`,
  metis_tac[deadlock_free_def,weak_reduction_perm,deadlocked_perm,PERM_SYM]);

val deadlock_free = Q.store_thm("deadlock_free",
  `!c p. wf_chor c /\ reduction^* (compile c) p /\ deadlocked p ==> F`,
  metis_tac[compile_weak_reduce_compile,compile_not_deadlocked,deadlocked_perm,deadlocked_clean_terminated]);

val compile_deadlock_free = Q.store_thm("compile_deadlock_free",
  `!c p. wf_chor c ==> deadlock_free(compile c)`,
  metis_tac[deadlock_free_def,deadlock_free]);

val closed_def = Define
  `closed p = EVERY (λ(a,b). EVERY (λ(c,d,e). a ≠ d ∧ MEM d (MAP FST p)) b) p`

val closed_PERM = Q.store_thm("closed_PERM",
  `!p p'. closed p /\ PERM p p' ==> closed p'`,
  rpt strip_tac >> fs[closed_def]
  >> imp_res_tac PERM_EVERY
  >> imp_res_tac (ISPEC ``FST`` PERM_MAP)
  >> drule MEM_PERM
  >> strip_tac >> fs[]);

val closed_trans_pres = Q.store_thm("closed_trans_pres",
  `!p a p'. trans p a p' /\ closed p ==> closed p'`,
  rpt strip_tac >> Cases_on `a`
  >- (* Internal *)
     (imp_res_tac reduces_sender_receiver >> fs[] >> rveq >> fs[closed_def])
  >> Cases_on `x` >> rename [`(act,tup)`] >> Cases_on `tup` >> Cases_on `act`
  >> rename [`(_,s,tup)`] >> Cases_on `tup` >> rename [`(_,s,r,m)`]
  >- (* Send *)
     (imp_res_tac sends_sender >> fs[] >> rveq >> fs[closed_def])
  >- (* Receive *)
     (imp_res_tac receives_receiver >> fs[] >> rveq >> fs[closed_def]))

val closed_reduction_pres = Q.store_thm("closed_reduction_pres",
  `!p p'. reduction p p' /\ closed p ==> closed p'`,
  rw[reduction_def] >> imp_res_tac closed_trans_pres);

val closed_weak_reduction_pres = Q.store_thm("closed_weak_reduction_pres",
  `!p p'. reduction^* p p' /\ closed p ==> closed p'`,
  rpt strip_tac >> mp_tac closed_reduction_pres
  >> PURE_ONCE_REWRITE_TAC[CONJ_SYM]
  >> strip_tac >> imp_res_tac RTC_lifts_invariants);

val weak_trans_def = Define
  `weak_trans p a p' = ?p'' p'''. reduction^* p p'' /\ trans p'' a p''' /\ reduction^* p''' p'`


val reduction_eats_two = Q.store_thm("reduction_eats_two",
`!p p'. reduction p p' ==> (SUM (MAP (LENGTH o SND) p) > 1 /\
  (SUM (MAP (LENGTH o SND) p') = SUM (MAP (LENGTH o SND) p) - 2))`,
  fs[reduction_def] >> rpt strip_tac
  >> imp_res_tac reduces_sender_receiver >> fs[SUM_APPEND]);

val bound_on_reductions = Q.store_thm("bound_on_reductions",
  `!n p p'. n > SUM(MAP(LENGTH o SND) p) /\
   NRC reduction n p p' ==> F`,
  Induct >> rpt strip_tac >> fs[ADD1]
  >> pop_assum mp_tac >> PURE_ONCE_REWRITE_TAC[ADD_COMM]
  >> PURE_ONCE_REWRITE_TAC[NRC_ADD_EQN] >> rpt strip_tac
  >> fs[] >> imp_res_tac reduction_eats_two
  >> rename [`NRC reduction n p' p''`]
  >> first_x_assum(qspecl_then [`p'`,`p''`] assume_tac)
  >> fs[] >> rfs[])

val maximal_reduction = Q.store_thm("maximal_reduction",
  `!p. ∃p'. reduction^* p p' /\ ¬∃p''. reduction p' p''`,
  rpt strip_tac >> fs[RTC_eq_NRC]
  >> qspecl_then [`SUM(MAP(LENGTH o SND) p) + 1`,`p`] assume_tac bound_on_reductions
  >> fs[] >> pop_assum mp_tac >> qpat_abbrev_tac `n = SUM (MAP (LENGTH o SND) _) + 1`
  >> pop_assum kall_tac >> Q.SPEC_TAC (`p`,`p`)
  >> Induct_on `n`
  >> fs[NRC_SUC_RECURSE_LEFT]
  >> metis_tac[]);

val reduction_CONS_pres = Q.store_thm("reduction_CONS_pres",
  `!p p' n. reduction p p' ==> reduction (n::p) (n::p')`,
  metis_tac[reduction_def,trans_par2,APPEND])

val weak_reduction_CONS_pres = Q.store_thm("weak_reduction_CONS_pres",
  `!p p' n. reduction^* p p' ==> reduction^* (n::p) (n::p')`,
  rpt strip_tac >> assume_tac reduction_CONS_pres
  >> irule RTC_lifts_monotonicities >> fs[])
                                     
val deadlock_free_weak_reduction_send = Q.store_thm("deadlock_free_weak_reduction_send",
  `!ll. deadlock_free((s,(Send,r,m)::l)::ll)
  ==> ∃p'. weak_trans ll (SOME(Receive,s,r,m)) p'`,
  rpt strip_tac >> fs[deadlock_free_def,deadlocked_def]
  >> qspec_then `ll` assume_tac maximal_reduction >> fs[]
  >> drule weak_reduction_CONS_pres
  >> disch_then(qspec_then `(s,(Send,r,m)::l)` assume_tac)
  >> first_x_assum drule >> rpt strip_tac
  >> fs[transitions_def]
  >- metis_tac[APPEND,trans_rules]
  >> fs[reduces_def,reduction_def]
  >> imp_res_tac reduces_sender_receiver >> fs[]
  >> Cases_on `ll'` >> fs[]
  >> fs[weak_trans_def] >> asm_exists_tac
  >> fs[] >> metis_tac[trans_rules,RTC_REFL]);

val (alt_trans_rules,alt_trans_ind,alt_trans_cases) = Hol_reln `
(!s r l m.
    alt_trans [(s,(Send,r,m)::l)] (SOME(Send,s,r,m)) [(s,l)])
/\ (!s r l m.
    alt_trans [(r,(Receive,s,m)::l)] (SOME(Receive,s,r,m)) [(r,l)])
/\ (!s r m p p' q q'.
    alt_trans p (SOME(Send,s,r,m)) p' /\ alt_trans q (SOME(Receive,s,r,m)) q'
    /\ p ≠ [] /\ q ≠ []
    ==> alt_trans (p++q) (NONE) (p'++q'))
/\ (!s r m p p' q q'.
    alt_trans p (SOME(Receive,s,r,m)) p' /\ alt_trans q (SOME(Send,s,r,m)) q'
    /\ p ≠ [] /\ q ≠ []
    ==> alt_trans (p++q) (NONE) (p'++q'))
/\ (!a p p' q.
    alt_trans p a p' /\ p ≠ [] /\ q ≠ [] ==> alt_trans (p++q) a (p'++q))
/\ (!a p q q'.
    alt_trans q a q' /\ p ≠ [] /\ q ≠ [] ==> alt_trans (p++q) a (p++q'))
`

val alt_trans_imp_trans = Q.store_thm("alt_trans_imp_trans",
  `!p a p'. alt_trans p a p' ==> trans p a p'`,
  ho_match_mp_tac alt_trans_ind >> metis_tac[trans_rules])

val trans_imp_alt_trans = Q.store_thm("trans_imp_alt_trans",
  `!p a p'. trans p a p' ==> alt_trans p a p'`,
  ho_match_mp_tac trans_ind >> rpt strip_tac
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules,alt_trans_imp_trans,nil_trans_empty]
  >- metis_tac[alt_trans_rules,alt_trans_imp_trans,nil_trans_empty]
  >- (Cases_on `q = []`
      >- fs[]
      >- metis_tac[alt_trans_rules,alt_trans_imp_trans,nil_trans_empty])
  >- (Cases_on `p = []`
      >- fs[]
      >- metis_tac[alt_trans_rules,alt_trans_imp_trans,nil_trans_empty]));

val trans_eq_alt_trans = Q.store_thm("trans_eq_alt_trans",
  `!p a p'. trans p a p' = alt_trans p a p'`,
  rw[EQ_IMP_THM,trans_imp_alt_trans,alt_trans_imp_trans]);

val trans_deriv_not_eq = Q.store_thm("trans_deriv_not_eq",
  `!p a p'. trans p a p' ==> (LENGTH p = LENGTH p') /\ p ≠ p'`,
  ho_match_mp_tac trans_ind >> rpt strip_tac
  >> fs[] >> rveq >> imp_res_tac APPEND_LENGTH_EQ)

val redex_not_eq = Q.store_thm("redex_not_eq",
  `!p p'. reduction p p' ==> (LENGTH p = LENGTH p') /\ p ≠ p'`,
  rpt strip_tac >> fs[reduction_def] >> imp_res_tac trans_deriv_not_eq >> fs[])
                                    
val alt_trans_CONS_elim_lemma = Q.prove(
  `!p a p'. alt_trans p a p' ==> alt_trans p a p' /\ !ph pr pr'. (LENGTH p = LENGTH p') /\ a ≠ NONE /\ (p = ph::pr) /\ (p' = ph::pr') ==> alt_trans pr a pr'`,
  ho_match_mp_tac alt_trans_ind >> rpt strip_tac
  >> fs[] >> rveq >> fs[nil_trans_eq]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
  >- (Cases_on `p` >> Cases_on `p'` >> fs[] >> rveq
      >> imp_res_tac alt_trans_imp_trans
      >> imp_res_tac nil_trans_empty >> metis_tac[alt_trans_rules])
  >- metis_tac[alt_trans_rules]
  >> Cases_on `p` >> fs[]
  >> Cases_on `t` >> fs[] >> rveq
  >> PURE_ONCE_REWRITE_TAC[GSYM APPEND]
  >> qpat_x_assum `alt_trans _ _ _` mp_tac
  >> PURE_ONCE_REWRITE_TAC[GSYM trans_eq_alt_trans]
  >> metis_tac[trans_par2]);

val trans_CONS_elim_lemma = Q.prove(
  `!h p a p'. trans (h::p) a (h::p') /\ a ≠ NONE ==> trans p a p'`,
  rpt strip_tac >> imp_res_tac trans_deriv_not_eq >> fs[trans_eq_alt_trans]
  >> drule alt_trans_CONS_elim_lemma >> fs[]);

val alt_trans_CONS_elim_lemma2 = Q.prove(
  `!p a p'. alt_trans p a p' ==> alt_trans p a p' /\ !ph pr pr'. (LENGTH p = LENGTH p') /\ (a = NONE) /\ (p = ph::pr) /\ (p' = ph::pr') ==> alt_trans pr a pr'`,
  ho_match_mp_tac alt_trans_ind >> rpt strip_tac
  >> fs[] >> rveq >> fs[nil_trans_eq]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]
(*  >- metis_tac[alt_trans_rules]
  >- metis_tac[alt_trans_rules]*)
  >- (Cases_on `p` >> Cases_on `p'` >> fs[] >> rveq
      >> imp_res_tac alt_trans_imp_trans
      >> imp_res_tac trans_deriv_not_eq
      >> imp_res_tac nil_trans_empty >> fs[]
      >> imp_res_tac trans_CONS_elim_lemma >> fs[]
      >> fs[GSYM trans_eq_alt_trans] >> metis_tac[trans_rules])
  >- metis_tac[alt_trans_rules]  
  >- (Cases_on `p` >> Cases_on `p'` >> fs[] >> rveq
      >> imp_res_tac alt_trans_imp_trans
      >> imp_res_tac trans_deriv_not_eq
      >> imp_res_tac nil_trans_empty >> fs[]
      >> imp_res_tac trans_CONS_elim_lemma >> fs[]
      >> fs[GSYM trans_eq_alt_trans] >> metis_tac[trans_rules])
  >- metis_tac[alt_trans_rules]
  >- (Cases_on `p` >> Cases_on `p'` >> fs[] >> rveq
      >> imp_res_tac alt_trans_imp_trans
      >> imp_res_tac trans_deriv_not_eq
      >> imp_res_tac nil_trans_empty >> fs[]
      >> imp_res_tac trans_CONS_elim_lemma >> fs[]
      >> fs[GSYM trans_eq_alt_trans] >> metis_tac[trans_rules])
  >- metis_tac[alt_trans_rules]
  >- (Cases_on `p` >> fs[GSYM trans_eq_alt_trans] >> rveq >> metis_tac[trans_rules]))

val trans_CONS_elim = Q.store_thm("trans_cons_elim",
  `!h p a p'. trans (h::p) a (h::p') ==> trans p a p'`,
  rpt strip_tac >> Cases_on `a` >> imp_res_tac trans_deriv_not_eq
  >> fs[trans_eq_alt_trans] >> drule alt_trans_CONS_elim_lemma
  >> drule alt_trans_CONS_elim_lemma2
  >> fs[]);

val reduction_CONS_elim = Q.store_thm("reduction_cons_elim",
  `!h p p'. reduction (h::p) (h::p') ==> reduction p p'`,
  rw[reduction_def] >> imp_res_tac trans_CONS_elim);

(*val reduction_CONS_elim = Q.store_thm("reduction_cons_elim",
  `!p p'. reduction p p' ==> reduction (TL_T p) (TL_T p')`,
  Cases_on `p` >- fs[reduction_def,nil_trans_eq]
  rw[reduction_def] >> imp_res_tac trans_CONS_elim);*)

val reduction_CONS_elim_sandwich = Q.prove(
  `reduction(h::p) p' /\ reduction p' (h::p'') ==> ?q. p' = h::q`,
  rpt strip_tac >> fs[reduction_def]
  >> imp_res_tac reduces_sender_receiver
  >> fs[] >> rfs[] >> Cases_on `ll'` >> fs[]
  >> rveq >> Cases_on `ll` >> fs[]
  >> rveq >> imp_res_tac LENGTH_EQ >> rfs[])

val red_rel_def = Define `red_rel p p' = ((p = p') \/ (LENGTH(SND p) > LENGTH(SND p')))`

val reduction_decreases_hd_length = Q.store_thm("reduction_decreases_hd_length",
  `!p p'. reduction p p' ==> red_rel (HD p) (HD p')`,
  rpt strip_tac >> fs[reduction_def,red_rel_def]
  >> imp_res_tac reduces_sender_receiver >> fs[]
  >> Cases_on `ll` >> fs[]);

val weak_reduction_decreases_hd_length = Q.store_thm("weak_reduction_decreases_hd_length",
  `!p p'. reduction^* p p' ==> red_rel (HD p) (HD p')`,
  rpt strip_tac >> irule RTC_lifts_reflexive_transitive_relations
  >- fs[reflexive_def,red_rel_def]
  >- (fs[transitive_def,red_rel_def] >> rpt strip_tac >> fs[])
  >> qexists_tac `reduction` >> fs[]
  >> metis_tac[reduction_decreases_hd_length]);

val trans_MAP_FST = Q.store_thm("trans_MAP_FST",
  `!p a p'. trans p a p' ==> (MAP FST p' = MAP FST p)`,
  ho_match_mp_tac trans_ind >> fs[])

val reduction_MAP_FST = Q.store_thm("reduction_MAP_FST",
  `!p p'. reduction p p' ==> (MAP FST p' = MAP FST p)`,
  rw[reduction_def] >> imp_res_tac trans_MAP_FST);

val weak_reduction_MAP_FST = Q.store_thm("weak_reduction_MAP_FST",
  `!p p'. reduction^* p p' ==> (MAP FST p' = MAP FST p)`,
  rpt strip_tac >> assume_tac reduction_MAP_FST
  >> imp_res_tac (GSYM RTC_lifts_equalities));

val NRC_reduction_CONS_elim_sandwich = Q.prove(
  `!n h p p'. NRC reduction n (h::p) p' /\ reduction p' (h::p'') ==> ?q. p' = h::q`,
  Induct >> rpt strip_tac
  >- (fs[] >> metis_tac[])
  >> fs[NRC_SUC_RECURSE_LEFT]
  >> imp_res_tac NRC_RTC
  >> imp_res_tac weak_reduction_decreases_hd_length
  >> imp_res_tac reduction_decreases_hd_length
  >> imp_res_tac reduction_MAP_FST
  >> imp_res_tac weak_reduction_MAP_FST
  >> Cases_on `p'` >> Cases_on `z` >> fs[]
  >> fs[red_rel_def] >> rveq >> fs[])
                                          
val NRC_reduction_CONS_elim = Q.store_thm("NRC_reduction_CONS_elim",
  `!n h p p'. NRC reduction n (h::p) (h::p') ==> ∃n. NRC reduction n p p'`,
  Induct >> rpt strip_tac
  >- (qexists_tac `0` >> fs[])
  >> fs[NRC_SUC_RECURSE_LEFT]
  >> imp_res_tac NRC_reduction_CONS_elim_sandwich
  >> fs[] >> rveq
  >> first_x_assum drule >> rpt strip_tac
  >> imp_res_tac reduction_CONS_elim
  >> qexists_tac `SUC n'`
  >> fs[NRC_SUC_RECURSE_LEFT] >> asm_exists_tac >> fs[])
  
val weak_reduction_CONS_elim = Q.store_thm("weak_reduction_CONS_elim",
  `!h p p'. reduction^* (h::p) (h::p') ==> reduction^* p p'`,
  rpt strip_tac >> fs[RTC_eq_NRC] >> imp_res_tac NRC_reduction_CONS_elim
  >> asm_exists_tac >> fs[]);

val weak_reduction_CONS_CONS_elim = Q.store_thm("weak_reduction_CONS_CONS_elim",
  `!s h r p p'. reduction^* ((s,h::r)::p) ((s,h::r)::p') ==> reduction^* ((s,r)::p) ((s,r)::p')`,
  rpt strip_tac >> drule weak_reduction_CONS_elim >> strip_tac
  >> irule weak_reduction_CONS_pres >> pop_assum ACCEPT_TAC);



val deadlock_free_weak_reduction_receive = Q.store_thm("deadlock_free_weak_reduction_receive",
  `!ll. deadlock_free((r,(Receive,s,m)::l)::ll)
  ==> ∃p'. weak_trans ll (SOME(Send,s,r,m)) p'`,
  rpt strip_tac >> fs[deadlock_free_def,deadlocked_def]
  >> qspec_then `ll` assume_tac maximal_reduction >> fs[]
  >> drule weak_reduction_CONS_pres
  >> disch_then(qspec_then `(r,(Receive,s,m)::l)` assume_tac)
  >> first_x_assum drule >> rpt strip_tac
  >> fs[transitions_def]
  >- metis_tac[APPEND,trans_rules]
  >> fs[reduces_def,reduction_def]
  >> imp_res_tac reduces_sender_receiver >> fs[]
  >> Cases_on `ll'` >> fs[CONV_RULE (LHS_CONV SYM_CONV) APPEND_EQ_CONS] >> rveq
  >> fs[]
  >> drule weak_reduction_CONS_elim
  >> rpt strip_tac
  >- (fs[weak_trans_def] >> asm_exists_tac >> fs[]
      >> metis_tac[trans_rules,RTC_REFL])
  >- (drule trans_CONS_elim >> rfs[])
  >- (drule trans_CONS_elim >> rfs[]));

val MEM_project_IMP = Q.store_thm("MEM_project_IMP",
  `!r c a s m. MEM (a,s,m) (project r c) ==> (MEM (s,r,m) c \/ MEM (r,s,m) c)`,
  recInduct project_ind >> rpt strip_tac
  >> fs[project_def] >> every_case_tac
  >> fs[] >> rveq >> first_x_assum drule >> strip_tac
  >> fs[]);

val MEM_chor_IMP = Q.store_thm("MEM_project_IMP",
  `!c s r m. MEM (s,r,m) c ==> (MEM s (endpoints c) /\ MEM r (endpoints c))`,
  Induct >> rpt strip_tac >> fs[] >> rveq >> fs[endpoints_def,MEM_add]
  >> Cases_on `h` >> Cases_on `r'` >> fs[endpoints_def,MEM_add] >> metis_tac[]);

val closed_compile = Q.store_thm("closed_compile",
  `!c. wf_chor c ==> closed(compile c)`,
  rw[closed_def,compile_def,EVERY_MEM,MEM_MAP] >> fs[wf_chor_def,EVERY_MEM] >> rw[]
  >> rpt(pairarg_tac >> fs[]) >> imp_res_tac MEM_project_IMP >> first_x_assum drule >> strip_tac
  >> fs[] >> Q.REFINE_EXISTS_TAC `(_, project _ c)` >> fs[] >> imp_res_tac MEM_chor_IMP
  >> fs[] >> metis_tac[]);

val closed_MEM = Q.store_thm("closed_MEM",
  `closed (ll ++ [s,(a,r,m)::l] ++ lr) ==> (s ≠ r /\ MEM r (MAP FST (ll++lr)))`,
  fs[closed_def,EVERY_MEM] >> rw[] >> fs[]);

val closed_HD_MEM = Q.store_thm("closed_HD_MEM",
  `closed ((s,(a,r,m)::l)::ll) ==> (s ≠ r /\ MEM r (MAP FST ll))`,
  metis_tac[APPEND,closed_MEM])

val weak_trans_MAP_FST = Q.store_thm("weak_trans_MAP_FST",
  `!p a p'. weak_trans p a p' ==> (MAP FST p' = MAP FST p)`,
  metis_tac[weak_trans_def,weak_reduction_MAP_FST,trans_MAP_FST]);
                                     
val weak_trans_cons_reduce = Q.store_thm("weak_trans_cons_reduce",
  `!proc s r m l proc'. weak_trans proc (SOME (Receive,s,r,m)) proc'
   ==> reduction^* ((s,(Send,r,m)::l)::proc) ((s,l)::proc')`,
  rpt strip_tac >> fs[weak_trans_def]
  >> qspecl_then [`s`,`r`,`m`,`l`] assume_tac trans_send
  >> imp_res_tac trans_comm1 >> fs[GSYM reduction_def]
  >> pop_assum (assume_tac o MATCH_MP RTC_SINGLE)
  >> metis_tac [weak_reduction_CONS_pres,RTC_RTC]);

val weak_trans_cons_reduce' = Q.store_thm("weak_trans_cons_reduce'",
  `!proc s r m l proc'. weak_trans proc (SOME (Send,s,r,m)) proc'
   ==> reduction^* ((r,(Receive,s,m)::l)::proc) ((r,l)::proc')`,
  rpt strip_tac >> fs[weak_trans_def]
  >> qspecl_then [`s`,`r`,`m`,`l`] assume_tac trans_receive
  >> imp_res_tac trans_comm2 >> fs[GSYM reduction_def]
  >> pop_assum (assume_tac o MATCH_MP RTC_SINGLE)
  >> metis_tac [weak_reduction_CONS_pres,RTC_RTC]);

val deadlock_free_reduction_pres = Q.store_thm("deadlock_free_reduction_pres",
  `!p p'. deadlock_free p /\ reduction p p' ==> deadlock_free p'`,
  rpt strip_tac >> fs[deadlock_free_def]
  >> metis_tac[RTC_RULES]);

val deadlock_free_weak_reduction_pres = Q.store_thm("deadlock_free_weak_reduction_pres",
  `!p p'. deadlock_free p /\ reduction^* p p' ==> deadlock_free p'`,
  rpt strip_tac >> assume_tac deadlock_free_reduction_pres
  >> imp_res_tac RTC_lifts_invariants);

val _ = export_theory ()
