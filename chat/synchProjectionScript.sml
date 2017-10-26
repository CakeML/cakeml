open preamble synchLangTheory ffiTheory astTheory semanticsTheory permLib namespacePropsTheory;

val _ = new_theory "synchProjection"

val project_ffi_state_def = Define
  `project_ffi_state node proc = FILTER ($≠ node o FST) proc`

val project_oracle_def = Define
  `project_oracle node s st node' =
   if s = "Send" then
     case $some (weak_trans st (SOME(Receive,node,node',()))) of
         SOME p' => Oracle_return p' node'
       | NONE => Oracle_diverge
   else if s = "Receive" then
     case $some (weak_trans st (SOME(Send,node',node,()))) of
         SOME p' => Oracle_return p' node'
       | NONE => Oracle_diverge
   else Oracle_fail`

val action_string_def =
  Define `(action_string Send = "Send") /\ (action_string Receive = "Receive")`;

val project_node_def = Define
`(project_node names [] = Con NONE []) /\
 (project_node names ((a,r,m)::l) =
   Let NONE (App (FFI(action_string a)) [Var(THE(ALOOKUP names r))]) (project_node names l)
 )
`

val get_io_events_def = Define
 `get_io_events l =
    MAP (λ(a,r,m). IO_event (action_string a) (ZIP (r,r))) l`

val env_v_same =
  Q.prove(`!env:('a sem_env). env with v := env.v = env`,
          simp[semanticPrimitivesTheory.sem_env_component_equality])

val evaluate_projection_lemma1 = Q.prove(
  `!l node proc names env rfs nv n iolist dt ms st v.
  ¬MEM node (MAP FST proc) /\ ALL_DISTINCT(MAP FST proc)
  /\ PERM(MAP FST names) (node::MAP FST proc)
  /\ closed((node,l)::proc)
  /\ deadlock_free ((node,l)::proc)
  /\ (!node'. MEM node' (MAP FST proc) ==> ?v. (nsLookup env.v (THE(ALOOKUP names node')) = SOME(Loc v)) /\ (store_lookup v rfs = SOME(W8array node')))
  /\ (nsLookup env.v (THE(ALOOKUP names node)) = SOME (Loc nv))
  /\ (store_lookup nv rfs  = SOME(W8array node))
  /\ (evaluate <| clock := n
                ; refs := rfs
                ; ffi :=
                  (<| oracle := project_oracle node
                    ; ffi_state := proc
                    ; final_event := NONE
                    ; io_events := iolist
                                  |>)
                ; defined_types := dt
                ; defined_mods := ms |> env [project_node names l]  = (st,v)) ==> ((st.ffi.final_event = NONE) /\ st.ffi.io_events = iolist ++ get_io_events l)`,
  Induct >> rpt GEN_TAC >> rpt(disch_then STRIP_ASSUME_TAC)
  >> imp_res_tac (GSYM ALOOKUP_NONE)
  >- (fs[project_node_def] >> qpat_x_assum `evaluate _ _ _ = _` mp_tac
      >> EVAL_TAC >> rpt strip_tac >> rveq >> simp[])
  >> rename [`(node,tup::l)`]
  >> Cases_on `tup` >> Cases_on `r` >> Cases_on `q` >> rename [`(act,s,m)`]
  >> Cases_on `act` >> qpat_x_assum `evaluate _ _ _ = _` mp_tac
  >> imp_res_tac closed_HD_MEM
  >> first_assum(qspec_then `s` assume_tac) >> pop_assum drule >> strip_tac >> rfs[] >> fs[semanticPrimitivesTheory.store_lookup_def]
  >> EVAL_TAC >> imp_res_tac closed_HD_MEM >> fs[] >> EVAL_TAC >> fs[]
  >> (drule deadlock_free_weak_reduction_send ORELSE drule deadlock_free_weak_reduction_receive)
  >> simp[some_def,semanticPrimitivesTheory.sem_env_component_equality]
  >> simp[semanticPrimitivesTheory.sem_env_component_equality,env_v_same]
  >> PURE_ONCE_REWRITE_TAC[GSYM SELECT_THM]
  >> qpat_abbrev_tac `proc' = (@x. weak_trans _ _ x)` >> pop_assum kall_tac
  >> disch_then assume_tac
  >> `LUPDATE (W8array s) v' rfs = rfs` by(metis_tac[LUPDATE_SAME])
  >> simp[] >> pop_assum kall_tac
  >> strip_tac
  >> fs[get_io_events_def]
  >> first_x_assum match_mp_tac
  >> qexists_tac `node` >> qexists_tac `proc'`
  >> imp_res_tac weak_trans_MAP_FST >> fs[] >> asm_exists_tac >> fs[]
  >> (drule weak_trans_cons_reduce ORELSE drule weak_trans_cons_reduce')
  >> disch_then (qspec_then `l` assume_tac)
  >> imp_res_tac closed_weak_reduction_pres >> fs[]
  >> imp_res_tac deadlock_free_weak_reduction_pres >> fs[]
  >> rpt(asm_exists_tac >> fs[])
  >> fs[]);

val evaluate_projection_lemma = Q.prove(`MEM node (MAP FST proc) /\ ALL_DISTINCT(MAP FST proc)
/\ MAP FST names = (MAP FST proc)
/\ closed proc
/\ deadlock_free proc
/\ (!node'. MEM node' (MAP FST proc) ==> ?v. (nsLookup env.v (THE(ALOOKUP names node')) = SOME(Loc v)) /\ (store_lookup v rfs = SOME(W8array node')))
/\ (evaluate <| clock := n
              ; refs := rfs
              ; ffi := initial_ffi_state (project_oracle node) (project_ffi_state node proc)
              ; defined_types := dt
              ; defined_mods := ms |> env [project_node names (THE(ALOOKUP proc node))]  = (st,v)) ==> (st.ffi.final_event = NONE /\ st.ffi.io_events = get_io_events(THE(ALOOKUP proc node)))`,
  rpt (disch_then STRIP_ASSUME_TAC)
  >> qpat_x_assum `MEM _ _` mp_tac
  >> imp_res_tac(ISPEC ``MAP FST x`` PERM_INTRO)
  >> simp[MEM_MAP,MEM_SPLIT] >> strip_tac
  >> rename [`proc = ctxtl ++ [tup] ++ ctxtr`]
  >> Cases_on `tup` >> rveq >> rename [`[node,l]`]
  >> `ALOOKUP ctxtl node = NONE` by(fs[ALL_DISTINCT_APPEND,ALOOKUP_NONE])
  >> `ALOOKUP ctxtr node = NONE` by(fs[ALL_DISTINCT_APPEND,ALOOKUP_NONE])
  >> fs[ALOOKUP_APPEND]
  >> `project_ffi_state node (ctxtl ++ [(node,l)] ++ ctxtr) = ctxtl ++ ctxtr`
      by(qpat_x_assum `ALL_DISTINCT _` mp_tac >> rpt(pop_assum kall_tac)
         >> strip_tac >> fs[project_ffi_state_def,ALL_DISTINCT_FILTER]
         >> pop_assum (qspec_then `node` assume_tac)
         >> fs[FILTER_APPEND,FILTER_MAP,APPEND_EQ_SING,FILTER_EQ_NIL,o_DEF,GSYM FILTER_EQ_ID])
  >> fs[initial_ffi_state_def]
  >> PURE_ONCE_REWRITE_TAC[GSYM(ISPEC ``get_io_events l`` (hd(CONJUNCTS APPEND)))]
  >> match_mp_tac evaluate_projection_lemma1
  >> `ALL_DISTINCT(MAP FST(ctxtl++ctxtr)) /\ ¬MEM node (MAP FST (ctxtl++ctxtr))`
     by(fs[ALL_DISTINCT_APPEND])
  >> asm_exists_tac >> fs[]
  >> NORMALISE_ASM_PERM_TAC
  >> imp_res_tac PERM_SYM
  >> asm_exists_tac
  >> fs[]
  >> `closed ((node,l)::(ctxtl ++ ctxtr))`
      by(irule closed_PERM >> asm_exists_tac >> fs[] >> CONV_TAC PERM_NORMALISE_CONV)
  >> asm_exists_tac >> fs[]
  >> `deadlock_free ((node,l)::(ctxtl ++ ctxtr)) = deadlock_free (ctxtl ++ [(node,l)] ++ ctxtr)`
      by(irule deadlock_free_perm >> CONV_TAC PERM_NORMALISE_CONV)
  >> fs[]
  >> metis_tac[]);

val evaluate_compile_projection_lemma = Q.prove(`wf_chor c
/\ MAP FST names = endpoints c
/\ MEM node (endpoints c)
/\ (!node'. MEM node' (endpoints c) ==> ?v. (nsLookup env.v (THE(ALOOKUP names node')) = SOME(Loc v)) /\ (store_lookup v rfs = SOME(W8array node')))
/\ (evaluate <| clock := n
              ; refs := rfs
              ; ffi := initial_ffi_state (project_oracle node) (project_ffi_state node (compile c))
              ; defined_types := dt
              ; defined_mods := ms |> env [project_node names (THE(ALOOKUP (compile c) node))]  = (st,v)) ==> (st.ffi.final_event = NONE /\ st.ffi.io_events = get_io_events(THE(ALOOKUP (compile c) node)))`,
  rpt(disch_then STRIP_ASSUME_TAC)
  >> match_mp_tac (GEN_ALL evaluate_projection_lemma)
  >> fs[GSYM MAP_FST_compile]     
  >> fs[initial_ffi_state_def,ALL_DISTINCT_FST_compile,closed_compile,compile_deadlock_free]
  >> rpt(asm_exists_tac >> fs[]));

val evaluate_compile_projection_lemma = Q.prove(`wf_chor c
/\ MAP FST names = endpoints c
/\ MEM node (endpoints c)
/\ (!node'. MEM node' (endpoints c) ==> ?v. (nsLookup env.v (THE(ALOOKUP names node')) = SOME(Loc v)) /\ (store_lookup v rfs = SOME(W8array node')))
/\ (evaluate <| clock := n
              ; refs := rfs
              ; ffi := initial_ffi_state (project_oracle node) (project_ffi_state node (compile c))
              ; defined_types := dt
              ; defined_mods := ms |> env [project_node names (THE(ALOOKUP (compile c) node))]  = (st,v)) ==> (st.ffi.final_event = NONE /\ st.ffi.io_events = get_io_events(THE(ALOOKUP (compile c) node)))`,
  rpt(disch_then STRIP_ASSUME_TAC)
  >> match_mp_tac (GEN_ALL evaluate_projection_lemma)
  >> fs[GSYM MAP_FST_compile]     
  >> fs[initial_ffi_state_def,ALL_DISTINCT_FST_compile,closed_compile,compile_deadlock_free]
  >> rpt(asm_exists_tac >> fs[]));

val alloc_w8array_then_def = Define
  `alloc_w8array_then name w8 = Let (SOME name) (App Aw8alloc [Lit (IntLit(&LENGTH w8)); Lit(Word8 0w)])`

val write_w8array_then_def = Define
  `(write_w8array_then name n [] exp = exp) /\
   (write_w8array_then name n (w::ws) exp =
    Let NONE (App Aw8update [Var(Short name); Lit(IntLit(&n)); Lit(Word8 w)])
        (write_w8array_then name (SUC n) ws exp))`

val alloc_w8arrayconst_then_def = Define
  `alloc_w8arrayconst_then name w8 exp = alloc_w8array_then name w8 (write_w8array_then name 0 w8 exp)`

val ext = Q.prove(`x = y ==> f x = f y`,rw[]);
val ext2 = Q.prove(`f = g ==> f x = g x`,rw[]);

val evaluate_alloc_w8array_then = Q.store_thm("evaluate_alloc_w8array_then",
`evaluate st env [alloc_w8array_then name w8 exp]  =
 evaluate (st with refs := st.refs ++ [W8array (REPLICATE (LENGTH w8) 0w)])
        (env with v := nsBind name (Loc (LENGTH st.refs)) env.v) [exp]`,
EVAL_TAC
>> fs[integerTheory.INT_GE_REDUCE]
>> rpt(match_mp_tac ext2 ORELSE match_mp_tac ext)
>> fs[semanticPrimitivesTheory.state_component_equality]);

val SUC_MINUS_SUC = Q.prove(`!n m. SUC m <= n ==> (SUC (n - SUC m) = n - m)`,
  intLib.COOPER_TAC);

val TAKE_LUPDATE_lemma = Q.prove(`!l m v. SUC m <= LENGTH l ==> (TAKE (LENGTH l - m)
    (LUPDATE v (LENGTH l - SUC m) l) = TAKE (LENGTH l - SUC m) l ++ [v])`,
  Induct >> rpt strip_tac >> fs[SUB]
  >> Cases_on `LENGTH l - m`
  >> fs[LUPDATE_def]
  >> fs[LUPDATE_def]
  >> `SUC m <= LENGTH l` by fs[]
  >> first_x_assum drule
  >> fs[]
  >> `LENGTH l - SUC m = n` by intLib.COOPER_TAC
  >> fs[]);

val st_ffi_id = Q.prove(`st with ffi:= st.ffi = st`,fs[semanticPrimitivesTheory.state_component_equality])

val evaluate_write_w8array_then_lemma = Q.prove(
  `!w8' w8 st env exp name.
   LENGTH w8' <= LENGTH w8 ==> 
   (evaluate
    (st with refs := st.refs ++ [W8array w8])
    (env with v := nsBind name (Loc (LENGTH st.refs)) env.v)
    [write_w8array_then name (LENGTH w8 - LENGTH w8') w8' exp]
   = evaluate
    (st with refs := st.refs ++ [W8array(TAKE (LENGTH w8 - LENGTH w8') w8 ++ w8')])
    (env with v := nsBind name (Loc (LENGTH st.refs)) env.v)
    [exp])
  `,
  Induct >> rpt strip_tac
  >> EVAL_TAC
  >> fs[TAKE_LENGTH_ID]
  >> EVAL_TAC
  >> fs[EL_APPEND_EQN]
  >> `LENGTH w8' ≤ LENGTH(LUPDATE h (LENGTH w8 - SUC(LENGTH w8')) w8)` by fs[]
  >> first_x_assum drule
  >> disch_then(qspecl_then[`st`,`env`,`exp`,`name`] assume_tac)
  >> fs[SUC_MINUS_SUC,st_ffi_id,TAKE_LUPDATE_lemma]
  >> PURE_REWRITE_TAC[GSYM APPEND_ASSOC,APPEND] >> fs[]);

val evaluate_write_w8array_then = Q.store_thm("evaluate_write_w8array_then",
  `evaluate
    (st with refs := st.refs ++ [W8array (REPLICATE (LENGTH w8) w)])
    (env with v := nsBind name (Loc (LENGTH st.refs)) env.v)
    [write_w8array_then name 0 w8 exp]
   = evaluate
    (st with refs := st.refs ++ [W8array w8])
    (env with v := nsBind name (Loc (LENGTH st.refs)) env.v)
    [exp]`,
  rw[evaluate_write_w8array_then_lemma |> Q.SPEC `w8`
     |> Q.SPEC `REPLICATE (LENGTH (w8:word8 list)) w`
     |> SIMP_RULE std_ss [LENGTH_REPLICATE,SUB_EQUAL_0,write_w8array_then_def]])

val evaluate_alloc_w8arrayconst_then = Q.store_thm("evaluate_alloc_w8array_then",
  `evaluate st env [alloc_w8arrayconst_then name w8 exp]  =
   evaluate (st with refs := st.refs ++ [W8array w8])
            (env with v := nsBind name (Loc (LENGTH st.refs)) env.v) [exp]`,
  rw[alloc_w8arrayconst_then_def,evaluate_alloc_w8array_then,evaluate_write_w8array_then]);

val alloc_w8arrayconsts_then_def = Define
 `(alloc_w8arrayconsts_then ((name,w8)::nws) exp = alloc_w8arrayconst_then name w8 (alloc_w8arrayconsts_then nws exp))
  /\ (alloc_w8arrayconsts_then [] exp = exp)
`

ALL_DISTINCT(MAP FST nws)

val ext3 = Q.prove(`(f = g) /\ (x = y) ==> (f x = g y)`,rw[])

val evaluate_alloc_w8arrayconsts_then_lemma = Q.prove(
 `!nws exp st env. ALL_DISTINCT (MAP FST nws) ==> 
   evaluate st env [alloc_w8arrayconsts_then nws exp]  =
   evaluate (st with refs := st.refs ++ MAP (W8array o SND) nws)
            (env with v := nsBindList (REVERSE(ZIP (MAP FST nws, GENLIST (λn. Loc (LENGTH st.refs + n)) (LENGTH nws)))) env.v) [exp]`,
  Induct
  >- (fs[alloc_w8arrayconsts_then_def,namespaceTheory.nsBindList_def] >> rpt strip_tac
      >> rpt(match_mp_tac ext ORELSE match_mp_tac ext2 ORELSE (match_mp_tac ext3 >> strip_tac))
      >> fs[semanticPrimitivesTheory.state_component_equality,semanticPrimitivesTheory.sem_env_component_equality])
  >> Cases >> rpt strip_tac
  >> fs[alloc_w8arrayconsts_then_def,namespaceTheory.nsBindList_def,evaluate_alloc_w8arrayconst_then]
  >> SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND]
  >> fs[GENLIST_CONS,o_DEF,FOLDR_APPEND,ADD1]);

val gen_alloc_w8arrayconsts_then_def = Define
  `gen_alloc_w8arrayconsts_then w8s exp = alloc_w8arrayconsts_then (ZIP(GENLIST (λn. REPLICATE (SUC n) #"a") (LENGTH w8s), w8s)) exp`

val REPLICATE_EQ_REPLICATE = Q.store_thm("REPLICATE_EQ_REPLICATE",
  `!n a m b. (REPLICATE n a = REPLICATE m a) = (n = m)`,
  fs[EQ_IMP_THM] >> Induct >> rpt strip_tac
  >- fs[CONV_RULE(LHS_CONV SYM_CONV) REPLICATE_NIL]
  >> Cases_on `m` >> fs[] >> metis_tac[]);

val ALL_DISTINCT_gen_names = Q.prove(`!n. ALL_DISTINCT(GENLIST (λn. REPLICATE (SUC n) #"a") n)`,
  Induct >> fs[GENLIST,ALL_DISTINCT_SNOC,MEM_GENLIST,REPLICATE_EQ_REPLICATE]);

val evaluate_gen_alloc_w8arrayconsts_then_lemma = Q.prove(
 `!w8s exp st env.
   evaluate st env [gen_alloc_w8arrayconsts_then w8s exp]  =
   evaluate (st with refs := st.refs ++ MAP W8array w8s)
            (env with v := nsBindList (REVERSE(ZIP(GENLIST (λn. REPLICATE (SUC n) #"a") (LENGTH w8s), GENLIST (λn. Loc (LENGTH st.refs + n)) (LENGTH w8s)))) env.v) [exp]`,
  rpt strip_tac >> qspec_then `LENGTH w8s` assume_tac ALL_DISTINCT_gen_names
  >> qspec_then `ZIP(GENLIST (λn. REPLICATE (SUC n) #"a") (LENGTH w8s),w8s)` assume_tac evaluate_alloc_w8arrayconsts_then_lemma
  >> rfs[MAP_ZIP,gen_alloc_w8arrayconsts_then_def]);

val compile_to_cake_def = Define `
    compile_to_cake c node =
    gen_alloc_w8arrayconsts_then (endpoints c) (project_node (REVERSE(ZIP(endpoints c, GENLIST (λn. Short(REPLICATE (SUC n) #"a")) (LENGTH(endpoints c))))) (THE(ALOOKUP (compile c) node)))`

val GENLIST_LENGTH_MAPi = Q.prove(`!l f. GENLIST f (LENGTH l) = MAPi (λn v. f n) l`,
  Induct >> rpt strip_tac >> fs[GENLIST_CONS,o_DEF]);

val ALOOKUP_NOT_MEM_GENLIST = Q.prove(`!l n. ¬MEM n l ==> (ALOOKUP
              (ZIP
                 (l, GENLIST f (LENGTH l))) n = NONE)`,
  metis_tac[ALOOKUP_ZIP_FAIL,LENGTH_GENLIST]);

val nsLookup_nsBindList = Q.store_thm("nsLookup_nsBindList",
  `!l v n. nsLookup (nsBindList l v) (Short n) =
        case ALOOKUP l n of NONE => nsLookup v (Short n) | SOME x => SOME x`,
  Induct
  >- fs[namespaceTheory.nsBindList_def]
  >> Cases >> Cases >> rpt strip_tac
  >> rename [`(n',v)::l`]
  >> Cases_on `n = n'`
  >> fs[namespaceTheory.nsBindList_def]);

val ALL_DISTINCT_REVERSE_project_node = Q.prove(`!actions l f. ALL_DISTINCT l ==>
  (project_node (REVERSE (ZIP(l,GENLIST f (LENGTH l)))) actions
   = project_node (ZIP(l,GENLIST f (LENGTH l))) actions)
  `,
  Induct
  >- rw[project_node_def]
  >> Cases >> rename [`(tup1,tup2)`] >> Cases_on `tup2`
  >> rpt strip_tac
  >> fs[project_node_def]
  >> match_mp_tac ext
  >> match_mp_tac alookup_distinct_reverse >> fs[MAP_ZIP]);

val evaluate_compile_to_cake = Q.store_thm("evaluate_compile_to_cake",
  `!c node st v env n rfs dt ms.
   wf_chor c /\ MEM node (endpoints c) /\
     (evaluate <| clock := n
                ; refs := rfs
                ; ffi := initial_ffi_state (project_oracle node) (project_ffi_state node (compile c))
                ; defined_types := dt
                ; defined_mods := ms |> env [compile_to_cake c node]  = (st,v)) ==> 
  st.ffi.final_event = NONE /\ st.ffi.io_events = get_io_events(THE(ALOOKUP (compile c) node))
`,
  rpt(GEN_TAC) >> rpt(disch_then STRIP_ASSUME_TAC)
  >> fs[compile_to_cake_def,evaluate_gen_alloc_w8arrayconsts_then_lemma]
  >> irule(GEN_ALL evaluate_compile_projection_lemma)
  >> fs[]
  >> EVERY(map qexists_tac [`dt`,`env with
         v :=
           nsBindList
             (REVERSE
                (ZIP
                   (GENLIST (λn. STRING #"a" (REPLICATE n #"a"))
                      (LENGTH (endpoints c)),
                    GENLIST (λn'. Loc (n' + LENGTH rfs))
                      (LENGTH (endpoints c))))) env.v`,`ms`,`n`,
                            `(ZIP
                             (endpoints c,
                              GENLIST (λn. Short (STRING #"a" (REPLICATE n #"a")))
                                      (LENGTH (endpoints c))))`,
                            `rfs ++ MAP W8array (endpoints c)`,`v`
          ])
  >> rpt strip_tac
  >> Q.ISPEC_THEN `c` assume_tac ALL_DISTINCT_endpoints
  >> fs[MAP_ZIP,ALL_DISTINCT_REVERSE_project_node]
  >> qpat_x_assum `evaluate _ _ _ = _` kall_tac
  >> fs[GENLIST_LENGTH_MAPi]
  >> qpat_x_assum `MEM _ _` mp_tac >> simp[MEM_SPLIT] >> rpt strip_tac
  >> qpat_x_assum `MEM _ _` kall_tac
  >> fs[MAPi_APPEND,ALL_DISTINCT_APPEND] >> fs[GSYM ZIP_APPEND,LENGTH_MAPi]
  >> fs[MAPi_GENLIST,S_DEF]
  >> fs[ALOOKUP_APPEND,ALOOKUP_NOT_MEM_GENLIST]
  >> fs[GENLIST_APPEND,REVERSE_APPEND]
  >> fs[nsLookup_nsBindList,ALOOKUP_APPEND]
  >> CASE_TAC >> fs[semanticPrimitivesTheory.store_lookup_def,EL_APPEND_EQN]
  >> imp_res_tac ALOOKUP_MEM
  >> fs[MEM_REVERSE] >> fs[MEM_ZIP,LENGTH_GENLIST,EL_GENLIST] >> rfs[EL_GENLIST,REPLICATE_EQ_REPLICATE]);

val _ = export_theory ()
