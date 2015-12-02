open preamble bvlSemTheory bvpSemTheory bvpPropsTheory copying_gcTheory
     int_bitwiseTheory bvp_to_wordPropsTheory finite_mapTheory
     bvp_to_wordTheory wordPropsTheory labPropsTheory whileTheory;

val _ = new_theory "bvp_to_wordProof";

(* -------------------------------------------------------
    TODO:
     - sketch compiler proof
       - prove MakeSpace
       - prove Assign Const
   ------------------------------------------------------- *)

(* -------------------------------------------------------
    word_ml_inv: definition and lemmas
   ------------------------------------------------------- *)

val word_ml_inv_def = Define `
  word_ml_inv (heap,be,a,sp) limit c refs stack <=>
    ?hs. abs_ml_inv (MAP FST stack) refs (hs,heap,be,a,sp) limit /\
         EVERY2 (\v w. word_addr c heap v = w) hs (MAP SND stack)`

val EVERY2_MAP_MAP = prove(
  ``!xs. EVERY2 P (MAP f xs) (MAP g xs) = EVERY (\x. P (f x) (g x)) xs``,
  Induct \\ fs []);

val EVERY2_IMP_EVERY = prove(
  ``!xs ys. EVERY2 P xs ys ==> EVERY (\(x,y). P y x) (ZIP(ys,xs))``,
  Induct \\ Cases_on `ys` \\ fs[]);

val IMP_THE_EQ = prove(
  ``x = SOME w ==> THE x = w``,
  fs []);

val MEM_FIRST_EL = prove(
  ``!xs x.
      MEM x xs <=>
      ?n. n < LENGTH xs /\ (EL n xs = x) /\
          !m. m < n ==> (EL m xs <> EL n xs)``,
  rw [] \\ eq_tac
  THEN1 (rw [] \\ qexists_tac `LEAST n. EL n xs = x /\ n < LENGTH xs`
    \\ mp_tac (Q.SPEC `\n. EL n xs = x /\ n < LENGTH xs` (GEN_ALL FULL_LEAST_INTRO))
    \\ fs [MEM_EL] \\ strip_tac \\ pop_assum (qspec_then `n` mp_tac)
    \\ fs [] \\ rw [] \\ imp_res_tac LESS_LEAST \\ fs [] \\ `F` by decide_tac)
  \\ rw [] \\ fs [MEM_EL] \\ qexists_tac `n` \\ fs []);

val ALOOKUP_ZIP_EL = prove(
  ``!xs hs n.
      n < LENGTH xs /\ LENGTH hs = LENGTH xs /\
      (∀m. m < n ⇒ EL m xs ≠ EL n xs) ==>
      ALOOKUP (ZIP (xs,hs)) (EL n xs) = SOME (EL n hs)``,
  Induct \\ Cases_on `hs` \\ fs [] \\ Cases_on `n` \\ fs []
  \\ rpt strip_tac \\ first_assum (qspec_then `0` assume_tac) \\ fs []
  \\ rw [] \\ first_x_assum match_mp_tac \\ fs [] \\ rw []
  \\ first_x_assum (qspec_then `SUC m` mp_tac) \\ fs []);

val word_ml_inv_rearrange = prove(
  ``(!x. MEM x ys ==> MEM x xs) ==>
    word_ml_inv (heap,be,a,sp) limit c refs xs ==>
    word_ml_inv (heap,be,a,sp) limit c refs ys``,
  fs [word_ml_inv_def] \\ rw []
  \\ qexists_tac `MAP (\y. THE (ALOOKUP (ZIP(xs,hs)) y)) ys`
  \\ fs [EVERY2_MAP_MAP,EVERY_MEM]
  \\ reverse (rw [])
  THEN1
   (imp_res_tac EVERY2_IMP_EVERY
    \\ res_tac \\ fs [EVERY_MEM,FORALL_PROD]
    \\ first_x_assum match_mp_tac
    \\ imp_res_tac EVERY2_LENGTH
    \\ fs [MEM_ZIP] \\ fs [MEM_FIRST_EL]
    \\ rw [] \\ qexists_tac `n'` \\ fs [EL_MAP]
    \\ match_mp_tac IMP_THE_EQ
    \\ imp_res_tac ALOOKUP_ZIP_EL)
  \\ qpat_assum `abs_ml_inv (MAP FST xs) refs (hs,heap,be,a,sp) limit` mp_tac
  \\ `MAP FST ys = MAP FST (MAP (\y. FST y, THE (ALOOKUP (ZIP (xs,hs)) y)) ys) /\
      MAP (λy. THE (ALOOKUP (ZIP (xs,hs)) y)) ys =
        MAP SND (MAP (\y. FST y, THE (ALOOKUP (ZIP (xs,hs)) y)) ys)` by
    (imp_res_tac EVERY2_LENGTH \\ fs [MAP_ZIP,MAP_MAP_o,o_DEF]
     \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ fs [])
  \\ fs [] \\ pop_assum (K all_tac) \\ pop_assum (K all_tac)
  \\ `MAP FST xs = MAP FST (ZIP (MAP FST xs, hs)) /\
      hs = MAP SND (ZIP (MAP FST xs, hs))` by
    (imp_res_tac EVERY2_LENGTH \\ fs [MAP_ZIP])
  \\ pop_assum (fn th => simp [Once th])
  \\ pop_assum (fn th => simp [Once th])
  \\ (abs_ml_inv_stack_permute |> Q.INST [`stack`|->`[]`,`roots`|->`[]`]
        |> SIMP_RULE std_ss [APPEND_NIL] |> SPEC_ALL
        |> ONCE_REWRITE_RULE [CONJ_COMM] |> REWRITE_RULE [GSYM AND_IMP_INTRO]
        |> match_mp_tac)
  \\ fs [SUBSET_DEF,FORALL_PROD]
  \\ imp_res_tac EVERY2_LENGTH
  \\ fs [MEM_ZIP,MEM_MAP,PULL_EXISTS,FORALL_PROD]
  \\ rw [] \\ res_tac
  \\ `MEM p_1 (MAP FST xs)` by (fs [MEM_MAP,EXISTS_PROD] \\ metis_tac [])
  \\ fs [MEM_FIRST_EL]
  \\ qexists_tac `n'` \\ rfs [EL_MAP]
  \\ match_mp_tac IMP_THE_EQ
  \\ qpat_assum `EL n' xs = (p_1,p_2')` (fn th => fs [GSYM th])
  \\ match_mp_tac ALOOKUP_ZIP_EL \\ fs []);

val delete_odd_def = Define `
  (delete_odd LN = LN) /\
  (delete_odd (LS x) = LS x) /\
  (delete_odd (BN t1 t2) = mk_wf (BN t1 LN)) /\
  (delete_odd (BS t1 a t2) = mk_wf (BS t1 a LN))`;

val lookup_delete_odd = store_thm("lookup_delete_odd[simp]",
  ``lookup n (delete_odd t) = if EVEN n then lookup n t else NONE``,
  Cases_on `t` \\ fs [delete_odd_def,lookup_def]  \\ rw [] \\ fs [lookup_def])

val join_env_def = Define `
  join_env env vs =
    MAP (\(n,v). (THE (lookup ((n-2) DIV 2) env), v))
      (FILTER (\(n,v). n <> 0 /\ EVEN n) vs)`

val flat_def = Define `
  (flat (Env env::xs) (StackFrame vs _::ys) =
     join_env env vs ++ flat xs ys) /\
  (flat (Exc env _::xs) (StackFrame vs _::ys) =
     join_env env vs ++ flat xs ys) /\
  (flat _ _ = [])`

val ALOOKUP_SKIP_LEMMA = prove(
  ``¬MEM n (MAP FST xs) /\ d = e ==>
    ALOOKUP (xs ++ [(n,d)] ++ ys) n = SOME e``,
  fs [ALOOKUP_APPEND] \\ fs [GSYM ALOOKUP_NONE])

val adjust_var_DIV_2 = prove(
  ``(adjust_var n - 2) DIV 2 = n``,
  fs [ONCE_REWRITE_RULE[MULT_COMM]adjust_var_def,MULT_DIV]);

val EVEN_adjust_var = prove(
  ``EVEN (adjust_var n)``,
  fs [adjust_var_def,EVEN_MOD2,ONCE_REWRITE_RULE[MULT_COMM]MOD_TIMES]);

val adjust_var_NEQ_1 = prove(
  ``adjust_var n <> 1``,
  rpt strip_tac
  \\ `EVEN (adjust_var n) = EVEN 1` by fs []
  \\ fs [EVEN_adjust_var]);

val word_ml_inv_lookup = prove(
  ``word_ml_inv (heap,be,a,sp) limit c s.refs
      (ys ++ join_env l1 (toAList (delete_odd l2)) ++ xs) /\
    lookup n l1 = SOME x /\
    lookup (adjust_var n) l2 = SOME w ==>
    word_ml_inv (heap,be,a,sp) limit c (s:'ffi bvpSem$state).refs
      (ys ++ [(x,w)] ++ join_env l1 (toAList (delete_odd l2)) ++ xs)``,
  fs [toAList_def,foldi_def,LET_DEF]
  \\ fs [GSYM toAList_def] \\ rw []
  \\ `MEM (x,w) (join_env l1 (toAList (delete_odd l2)))` by
   (fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList]
    \\ qexists_tac `adjust_var n` \\ fs [adjust_var_DIV_2,EVEN_adjust_var])
  \\ fs [MEM_SPLIT] \\ fs [] \\ fs [adjust_var_def]
  \\ qpat_assum `word_ml_inv yyy limit c s.refs xxx` mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ fs [MEM] \\ rw [] \\ fs[]);

val word_ml_inv_get_var_IMP = store_thm("word_ml_inv_get_var_IMP",
  ``word_ml_inv (heap,be,a,sp) limit c s.refs
      (join_env s.locals (toAList (delete_odd t.locals))++envs) /\
    get_var n s = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    word_ml_inv (heap,be,a,sp) limit c s.refs
      ([(x,w)]++join_env s.locals (toAList (delete_odd t.locals))++envs)``,
  rw [] \\ match_mp_tac (word_ml_inv_lookup
             |> Q.INST [`ys`|->`[]`] |> SIMP_RULE std_ss [APPEND])
  \\ fs [get_var_def,wordSemTheory.get_var_def]);

val word_ml_inv_get_vars_IMP = store_thm("word_ml_inv_get_vars_IMP",
  ``!n x w envs.
      word_ml_inv (heap,be,a,sp) limit c s.refs
        (join_env s.locals (toAList (delete_odd t.locals))++envs) /\
      get_vars n s = SOME x /\
      get_vars (MAP adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp) limit c s.refs
        (ZIP(x,w)++join_env s.locals (toAList (delete_odd t.locals))++envs)``,
  Induct \\ fs [get_vars_def,wordSemTheory.get_vars_def] \\ rpt strip_tac
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac word_ml_inv_get_var_IMP
  \\ Q.MATCH_ASSUM_RENAME_TAC `bvpSem$get_var h s = SOME x7`
  \\ Q.MATCH_ASSUM_RENAME_TAC `wordSem$get_var (adjust_var h) t = SOME x8`
  \\ `word_ml_inv (heap,be,a,sp) limit c s.refs
        (join_env s.locals (toAList (delete_odd t.locals)) ++ (x7,x8)::envs)` by
   (pop_assum mp_tac \\ match_mp_tac word_ml_inv_rearrange
    \\ fs [MEM] \\ rw [] \\ fs [])
  \\ res_tac \\ pop_assum (K all_tac) \\ pop_assum mp_tac
  \\ match_mp_tac word_ml_inv_rearrange
  \\ fs [MEM] \\ rw [] \\ fs []) |> SPEC_ALL;

val IMP_adjust_var = prove(
  ``n <> 0 /\ EVEN n ==> adjust_var ((n - 2) DIV 2) = n``,
  fs [EVEN_EXISTS] \\ rw [] \\ Cases_on `m` \\ fs [MULT_CLAUSES]
  \\ once_rewrite_tac [MULT_COMM] \\ fs [MULT_DIV]
  \\ fs [adjust_var_def] \\ decide_tac);

val adjust_var_11 = prove(
  ``(adjust_var n = adjust_var m) <=> n = m``,
  fs [adjust_var_def,EQ_MULT_LCANCEL]);

val word_ml_inv_insert = store_thm("word_ml_inv_insert",
  ``word_ml_inv (heap,F,a,sp) limit c s.refs
      ([(x,w)]++join_env d (toAList (delete_odd l))++xs) ==>
    word_ml_inv (heap,F,a,sp) limit c s.refs
      (join_env (insert dest x d)
        (toAList (delete_odd (insert (adjust_var dest) w l)))++xs)``,
  match_mp_tac word_ml_inv_rearrange \\ fs [] \\ rw [] \\ fs []
  \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [] \\ rw [] \\ fs [MEM_toAList]
  \\ fs [lookup_insert]
  \\ Cases_on `dest = (p_1 - 2) DIV 2` \\ fs []
  \\ fs [adjust_var_DIV_2]
  \\ imp_res_tac IMP_adjust_var \\ fs []
  \\ metis_tac [adjust_var_11]);

(* -------------------------------------------------------
    definition and verification of GC function
   ------------------------------------------------------- *)

val word_gc_move_def = Define `
  (word_gc_move (Loc l1 l2,pa,m,dm,c) = (Loc l1 l2,pa,m,c)) /\
  (word_gc_move (Word w,pa,m,dm,c) =
     (Word 0w,pa,m,c))`

val word_gc_move_list_def = Define `
  (word_gc_move_list ([],pa,m,dm,c) = ([],pa,m,c)) /\
  (word_gc_move_list (w::ws,pa,m,dm,c) =
     let (w1,pa1,m1,c1) = word_gc_move (w,pa,m,dm,c) in
     let (ws2,pa2,m2,c2) = word_gc_move_list (ws,pa1,m1,dm,c1) in
       (w1::ws2,pa2,m2,c2))`

val word_gc_fun_def = Define `
  (word_gc_fun c):'a gc_fun_type = \(roots,m,dm,s).
     SOME (roots,m,s)`

val heap_in_memory_store_def = Define `
  heap_in_memory_store heap a sp c s m dm limit =
    ?curr other.
      (FLOOKUP s CurrHeap = SOME (Word curr)) /\
      (FLOOKUP s OtherHeap = SOME (Word other)) /\
      (FLOOKUP s NextFree = SOME (Word (curr + bytes_in_word * n2w a))) /\
      (FLOOKUP s LastFree = SOME (Word (curr + bytes_in_word * n2w (a + sp)))) /\
      (word_heap curr heap c heap *
       word_heap other [Unused (limit-1)] c [Unused (limit-1)]) (fun2set (m,dm))`

val word_gc_fun_lemma = prove(
  ``heap_in_memory_store heap a sp c s m dm limit /\
    abs_ml_inv (v::MAP FST stack) refs (hs,heap,be,a,sp) limit /\
    LIST_REL (\v w. word_addr c heap v = w) hs (s ' Globals::MAP SND stack) /\
    full_gc (hs,heap,limit) = (roots2,heap2,heap_length heap2,T) ==>
    let heap1 = heap2 ++ heap_expand (limit - heap_length heap2) in
      ?stack1 m1 s1 a1 sp1.
        word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
        heap_in_memory_store heap1 (heap_length heap2)
          (limit - heap_length heap2) c s1 m1 dm limit /\
        LIST_REL (λv w. word_addr c heap1 v = w) roots2
          (s1 ' Globals::MAP SND (ZIP (MAP FST stack,stack1))) /\
        LENGTH stack1 = LENGTH stack``,
  cheat) |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [LET_DEF,PULL_EXISTS,GSYM CONJ_ASSOC] |> SPEC_ALL;

val word_gc_fun_correct = prove(
  ``heap_in_memory_store heap a sp c s m dm limit /\
    word_ml_inv (heap,be,a,sp) limit c refs ((v,s ' Globals)::stack) ==>
    ?stack1 m1 s1 heap1 a1 sp1 w.
      word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
      heap_in_memory_store heap1 a1 sp1 c s1 m1 dm limit /\
      word_ml_inv (heap1,be,a1,sp1) limit c refs
        ((v,s1 ' Globals)::ZIP (MAP FST stack,stack1))``,
  fs [word_ml_inv_def] \\ rw [] \\ imp_res_tac full_gc_thm
  \\ fs [PULL_EXISTS] \\ rw []
  \\ mp_tac word_gc_fun_lemma \\ fs [] \\ rw [] \\ fs []
  \\ Q.LIST_EXISTS_TAC [`heap2 ++ heap_expand (limit - heap_length heap2)`,
       `heap_length heap2`,`limit - heap_length heap2`,`v''`,`xs'`]
  \\ fs [MAP_ZIP]);


(* -------------------------------------------------------
    definition of state relation
   ------------------------------------------------------- *)

val isWord_def = Define `
  (isWord (Word w) = T) /\ (isWord _ = F)`;

val theWord_def = Define `
  theWord (Word w) = w`;

val code_rel_def = Define `
  code_rel c s_code t_code <=>
    !n arg_count prog.
      (lookup n s_code = SOME (arg_count:num,prog)) ==>
      (lookup n t_code = SOME (arg_count+1,FST (comp c n 1 prog),arg_count+1))`

val stack_rel_def = Define `
  (stack_rel (Env env) (StackFrame vs NONE) <=>
     !n. IS_SOME (lookup n env) <=>
         IS_SOME (lookup (adjust_var n) (fromAList vs))) /\
  (stack_rel (Exc env n) (StackFrame vs (SOME (x1,x2,x3))) <=>
     stack_rel (Env env) (StackFrame vs NONE) /\ (x1 = n)) /\
  (stack_rel _ _ <=> F)`

val the_global_def = Define `
  the_global g = the (Number 0) (OPTION_MAP RefPtr g)`;

val contains_loc_def = Define `
  contains_loc (StackFrame vs _) (l1,l2) = (ALOOKUP vs 0 = SOME (Loc l1 l2))`

val state_rel_def = Define `
  state_rel c l1 l2 (s:'ffi bvpSem$state) (t:('a,'ffi) wordSem$state) v1 locs <=>
    (* I/O, clock and handler are the same, GC is fixed, code is compiled *)
    (t.ffi = s.ffi) /\
    (t.clock = s.clock) /\
    (t.handler = s.handler) /\
    (t.gc_fun = word_gc_fun c) /\
    code_rel c s.code t.code /\
    good_dimindex (:'a) /\
    (* the store *)
    EVERY (\n. n IN FDOM t.store) [Globals] /\
    (* every local is represented in word lang *)
    (v1 = [] ==> lookup 0 t.locals = SOME (Loc l1 l2)) /\
    (!n. IS_SOME (lookup n s.locals) ==>
         IS_SOME (lookup (adjust_var n) t.locals)) /\
    (* the stacks contain the same names, have same shape *)
    EVERY2 stack_rel s.stack t.stack /\
    EVERY2 contains_loc t.stack locs /\
    (* there exists some GC-compatible abstraction *)
    ?heap limit a sp.
      (* the abstract heap is stored in memory *)
      heap_in_memory_store heap a sp c t.store t.memory t.mdomain limit /\
      (* the abstract heap relates to the values of BVP *)
      word_ml_inv (heap,F,a,sp) limit c s.refs
        (v1 ++ join_env s.locals (toAList (delete_odd t.locals)) ++
           [(the_global s.global,t.store ' Globals)] ++
           flat s.stack t.stack) /\
      s.space <= sp`

(* -------------------------------------------------------
    compiler proof
   ------------------------------------------------------- *)

val adjust_var_NOT_0 = store_thm("adjust_var_NOT_0[simp]",
  ``adjust_var n <> 0``,
  fs [adjust_var_def]);

val state_rel_get_var_IMP = prove(
  ``state_rel c l1 l2 s t [] locs ==>
    (get_var n s = SOME x) ==>
    ?w. get_var (adjust_var n) t = SOME w``,
  fs [bvpSemTheory.get_var_def,wordSemTheory.get_var_def]
  \\ fs [state_rel_def] \\ rpt strip_tac
  \\ `IS_SOME (lookup n s.locals)` by fs [] \\ res_tac
  \\ Cases_on `lookup (adjust_var n) t.locals` \\ fs []);

val state_rel_get_vars_IMP = prove(
  ``!n xs.
      state_rel c l1 l2 s t [] locs ==>
      (get_vars n s = SOME xs) ==>
      ?ws. get_vars (MAP adjust_var n) t = SOME ws /\ (LENGTH xs = LENGTH ws)``,
  Induct \\ fs [bvpSemTheory.get_vars_def,wordSemTheory.get_vars_def]
  \\ rpt strip_tac
  \\ Cases_on `get_var h s` \\ fs []
  \\ Cases_on `get_vars n s` \\ fs [] \\ rw []
  \\ imp_res_tac state_rel_get_var_IMP \\ fs []);

val state_rel_0_get_vars_IMP = prove(
  ``state_rel c l1 l2 s t [] locs ==>
    (get_vars n s = SOME xs) ==>
    ?ws. get_vars (0::MAP adjust_var n) t = SOME ((Loc l1 l2)::ws) /\
         (LENGTH xs = LENGTH ws)``,
  rpt strip_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [wordSemTheory.get_vars_def]
  \\ fs [state_rel_def,wordSemTheory.get_var_def]);

val get_var_T_OR_F = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) state) [] locs /\
    get_var n s = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    6 MOD dimword (:'a) <> 2 MOD dimword (:'a) /\
    ((x = Boolv T) ==> (w = Word 2w)) /\
    ((x = Boolv F) ==> (w = Word 6w))``,
  fs [state_rel_def,get_var_def,wordSemTheory.get_var_def]
  \\ strip_tac \\ strip_tac THEN1 (fs [good_dimindex_def] \\ fs [dimword_def])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac (word_ml_inv_lookup |> Q.INST [`ys`|->`[]`]
                    |> SIMP_RULE std_ss [APPEND])
  \\ pop_assum mp_tac
  \\ simp [word_ml_inv_def,toAList_def,foldi_def,word_ml_inv_def,PULL_EXISTS]
  \\ strip_tac \\ strip_tac
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ pop_assum (fn th => fs [GSYM th])
  \\ fs [Boolv_def] \\ rw [] \\ fs [v_inv_def] \\ fs [word_addr_def]
  \\ EVAL_TAC \\ fs [good_dimindex_def,dimword_def]);

val mk_loc_def = Define `
  mk_loc (SOME (t1,d1,d2)) = Loc d1 d2`;

val LAST_EQ = prove(
  ``(LAST (x::xs) = if xs = [] then x else LAST xs) /\
    (FRONT (x::xs) = if xs = [] then [] else x::FRONT xs)``,
  Cases_on `xs` \\ fs []);

val cut_env_IMP_cut_env = prove(
  ``state_rel c l1 l2 s t [] locs /\
    bvpSem$cut_env r s.locals = SOME x ==>
    ?y. wordSem$cut_env (adjust_set r) t.locals = SOME y``,
  fs [bvpSemTheory.cut_env_def,wordSemTheory.cut_env_def]
  \\ fs [adjust_set_def,domain_fromAList,SUBSET_DEF,MEM_MAP,
         PULL_EXISTS,sptreeTheory.domain_lookup,lookup_fromAList] \\ rw []
  \\ Cases_on `x' = 0` \\ fs [] THEN1 fs [state_rel_def]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ fs [MEM_MAP] \\ rw[] \\ fs [] \\ Cases_on `y` \\ fs [] \\ rw []
  \\ fs [MEM_toAList] \\ res_tac
  \\ fs [state_rel_def] \\ res_tac
  \\ `IS_SOME (lookup q s.locals)` by fs [] \\ res_tac
  \\ Cases_on `lookup (adjust_var q) t.locals` \\ fs []);

val jump_exc_call_env = prove(
  ``wordSem$jump_exc (call_env x s) = jump_exc s``,
  fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def]);

val jump_exc_dec_clock = prove(
  ``mk_loc (wordSem$jump_exc (dec_clock s)) = mk_loc (jump_exc s)``,
  fs [wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def]
  \\ rw [] \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def]);

val LAST_N_ADD1 = miscTheory.LAST_N_LENGTH
  |> Q.SPEC `x::xs` |> SIMP_RULE (srw_ss()) [ADD1]

val jump_exc_push_env_NONE = prove(
  ``mk_loc (jump_exc (push_env y NONE s)) =
    mk_loc (jump_exc (s:('a,'b) wordSem$state))``,
  fs [wordSemTheory.push_env_def,wordSemTheory.jump_exc_def]
  \\ Cases_on `env_to_list y s.permute` \\ fs [LET_DEF]
  \\ Cases_on `s.handler = LENGTH s.stack` \\ fs [LAST_N_ADD1]
  \\ Cases_on `~(s.handler < LENGTH s.stack)` \\ fs [] \\ rw []
  THEN1 (`F` by DECIDE_TAC)
  \\ `LAST_N (s.handler + 1) (StackFrame q NONE::s.stack) =
      LAST_N (s.handler + 1) s.stack` by
    (match_mp_tac miscTheory.LAST_N_TL \\ decide_tac)
  \\ every_case_tac \\ rw [mk_loc_def]
  \\ `F` by decide_tac);

val state_rel_pop_env_set_var_IMP = prove(
  ``state_rel c q l s1 t1 [(a,w)] locs /\
    pop_env s1 = SOME s2 ==>
    ?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9)::ll /\
      state_rel c l8 l9 (set_var q a s2) (set_var (adjust_var q) w t2) [] ll``,
  fs [pop_env_def]
  \\ Cases_on `s1.stack` \\ fs [] \\ Cases_on `h` \\ fs []
  \\ rw[] \\ fs []
  \\ fs [state_rel_def,set_var_def,wordSemTheory.set_var_def]
  \\ rfs [] \\ Cases_on `y` \\ fs [stack_rel_def]
  \\ Cases_on `o'` \\ fs [stack_rel_def,wordSemTheory.pop_env_def]
  \\ fs [stack_rel_def,wordSemTheory.pop_env_def]
  \\ TRY (Cases_on `x` \\ fs [])
  \\ fs [lookup_insert,adjust_var_11]
  \\ rfs[] \\ rw [] \\ Cases_on `y`
  \\ fs [contains_loc_def,lookup_fromAList] \\ rw []
  \\ TRY (Cases_on `r` \\ fs [])
  \\ fs [stack_rel_def,wordSemTheory.pop_env_def] \\ rw []
  \\ fs [lookup_fromAList] \\ rfs[]
  \\ first_assum (match_exists_tac o concl) \\ fs [] (* asm_exists_tac *)
  \\ fs [flat_def]
  \\ `word_ml_inv (heap,F,a',sp) limit c s1.refs
       ((a,w)::(join_env s l ++
         [(the_global s1.global,t1.store ' Globals)] ++ flat t ys))` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ fs [MEM] \\ rw [] \\ fs [])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac (word_ml_inv_insert
       |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ rw [] \\ fs []
  \\ Cases_on `x` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [MEM_toAList,lookup_fromAList]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

val LAST_N_LIST_REL_LEMMA = prove(
  ``!xs1 ys1 xs n y ys x P.
      LAST_N n xs1 = x::xs /\ LIST_REL P xs1 ys1 ==>
      ?y ys. LAST_N n ys1 = y::ys /\ P x y /\ LIST_REL P xs ys``,
  Induct \\ Cases_on `ys1` \\ fs [LAST_N] \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ fs []
  \\ rw [] \\ fs [] \\ rw [] \\ fs []
  \\ every_case_tac \\ fs [] \\ rw [] \\ `F` by decide_tac);

val LAST_N_CONS_IMP_LENGTH = store_thm("LAST_N_CONS_IMP_LENGTH",
  ``!xs n y ys.
      n <= LENGTH xs ==>
      (LAST_N n xs = y::ys) ==> LENGTH (y::ys) = n``,
  Induct \\ fs [LAST_N] \\ rw [] THEN1 decide_tac \\ fs [GSYM NOT_LESS]);

val LAST_N_IMP_APPEND = store_thm("LAST_N_IMP_APPEND",
  ``!xs n ys.
      n <= LENGTH xs /\ (LAST_N n xs = ys) ==>
      ?zs. xs = zs ++ ys /\ LENGTH ys = n``,
  Induct \\ fs [LAST_N] \\ rw [] THEN1 decide_tac
  \\ `n <= LENGTH xs` by decide_tac \\ res_tac \\ fs []
  \\ qpat_assum `xs = zs ++ LAST_N n xs` (fn th => simp [Once th]));

val flat_APPEND = prove(
  ``!xs ys xs1 ys1.
      LENGTH xs = LENGTH ys ==>
      flat (xs ++ xs1) (ys ++ ys1) = flat xs ys ++ flat xs1 ys1``,
  Induct \\ Cases_on `ys` \\ fs [flat_def] \\ rw []
  \\ Cases_on `h'` \\ Cases_on `h`
  \\ TRY (Cases_on `o'`) \\ fs [flat_def]);

val state_rel_jump_exc = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs /\
    get_var n s = SOME x /\
    get_var (adjust_var n) t = SOME w /\
    jump_exc s = SOME s1 ==>
    ?t1 d1 d2 l5 l6 ll.
      jump_exc t = SOME (t1,d1,d2) /\
      LAST_N (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
      !i. state_rel c l5 l6 (set_var i x s1) (set_var (adjust_var i) w t1) [] ll``,
  fs [jump_exc_def] \\ rpt CASE_TAC \\ rw [] \\ fs [] \\ fs [state_rel_def]
  \\ fs [wordSemTheory.set_var_def,set_var_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_var_IMP
  \\ imp_res_tac LAST_N_LIST_REL_LEMMA
  \\ fs [] \\ rw [] \\ fs [wordSemTheory.jump_exc_def]
  \\ every_case_tac \\ fs [stack_rel_def]
  \\ Cases_on `y'` \\ fs [contains_loc_def]
  \\ `s.handler + 1 <= LENGTH s.stack` by decide_tac
  \\ imp_res_tac LAST_N_CONS_IMP_LENGTH \\ fs [ADD1]
  \\ imp_res_tac EVERY2_LENGTH \\ fs []
  \\ fs [lookup_insert,adjust_var_11]
  \\ fs [contains_loc_def,lookup_fromAList] \\ rw []
  \\ first_assum (match_exists_tac o concl) \\ fs [] (* asm_exists_tac *)
  \\ `s.handler + 1 <= LENGTH s.stack /\
      s.handler + 1 <= LENGTH t.stack` by decide_tac
  \\ imp_res_tac LAST_N_IMP_APPEND \\ fs [ADD1]
  \\ rw [] \\ fs [flat_APPEND,flat_def]
  \\ `word_ml_inv (heap,F,a,sp) limit c s.refs
       ((x,w)::(join_env s' l ++
         [(the_global s.global,t.store ' Globals)] ++ flat t' ys))` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ fs [MEM] \\ rw [] \\ fs [])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac (word_ml_inv_insert
       |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ rw [] \\ fs []
  \\ Cases_on `x'` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [MEM_toAList,lookup_fromAList]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

val NOT_NIL_IMP_LAST = prove(
  ``!xs x. xs <> [] ==> LAST (x::xs) = LAST xs``,
  Cases \\ fs []);

val get_vars_IMP_LENGTH = prove(
  ``!x t s. bvpSem$get_vars x s = SOME t ==> LENGTH x = LENGTH t``,
  Induct \\ fs [bvpSemTheory.get_vars_def] \\ rw []
  \\ every_case_tac \\ res_tac \\ fs [] \\ rw [] \\ fs []);

val lookup_adjust_var_fromList2 = prove(
  ``lookup (adjust_var n) (fromList2 (w::ws)) = lookup n (fromList ws)``,
  fs [lookup_fromList2,EVEN_adjust_var,lookup_fromList]
  \\ fs [adjust_var_def]
  \\ once_rewrite_tac [MULT_COMM]
  \\ fs [GSYM MULT_CLAUSES,MULT_DIV]);

val state_rel_call_env = prove(
  ``get_vars args s = SOME q /\
    get_vars (MAP adjust_var args) (t:('a,'ffi) wordSem$state) = SOME ws /\
    state_rel c l5 l6 s t [] locs ==>
    state_rel c l1 l2 (call_env q (dec_clock s))
      (call_env (Loc l1 l2::ws) (dec_clock t)) [] locs``,
  fs [state_rel_def,call_env_def,wordSemTheory.call_env_def,
      dec_clock_def,wordSemTheory.dec_clock_def,lookup_adjust_var_fromList2]
  \\ rw [lookup_fromList2,lookup_fromList] \\ rw []
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ fs []
  \\ first_assum (match_exists_tac o concl) \\ fs [] (* asm_exists_tac *)
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ rw [] \\ fs[]
  \\ Cases_on `x` \\ fs [join_env_def,MEM_MAP,MEM_FILTER]
  \\ Cases_on `y` \\ fs [MEM_toAList] \\ rw [MEM_ZIP]
  \\ fs [lookup_fromList2,lookup_fromList]
  \\ rpt disj1_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ fs [DIV_LT_X]
  \\ `k < 2 + LENGTH q * 2 /\ 0 < LENGTH q * 2` by
   (rfs [] \\ Cases_on `q` \\ fs []
    THEN1 (Cases_on `k` \\ fs [] \\ Cases_on `n` \\ fs [] \\ decide_tac)
    \\ fs [MULT_CLAUSES] \\ decide_tac)
  \\ fs [] \\ qexists_tac `(k - 2) DIV 2` \\ fs []
  \\ fs [DIV_LT_X] \\ rw []
  \\ Cases_on `k` \\ fs []
  \\ Cases_on `n` \\ fs [DECIDE ``SUC (SUC n) = n + 2``]
  \\ simp [MATCH_MP ADD_DIV_RWT (DECIDE ``0<2:num``)]
  \\ fs [GSYM ADD1,EL]);

val bvp_get_vars_SNOC_IMP = prove(
  ``!x2 x. bvpSem$get_vars (SNOC x1 x2) s = SOME x ==>
           ?y1 y2. x = SNOC y1 y2 /\
                   bvpSem$get_var x1 s = SOME y1 /\
                   bvpSem$get_vars x2 s = SOME y2``,
  Induct \\ fs [bvpSemTheory.get_vars_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []) |> SPEC_ALL;

val word_get_vars_SNOC_IMP = prove(
  ``!x2 x. wordSem$get_vars (SNOC x1 x2) s = SOME x ==>
           ?y1 y2. x = SNOC y1 y2 /\
              wordSem$get_var x1 s = SOME y1 /\
              wordSem$get_vars x2 s = SOME y2``,
  Induct \\ fs [wordSemTheory.get_vars_def]
  \\ rw [] \\ every_case_tac \\ fs [] \\ rw []) |> SPEC_ALL;

val word_ml_inv_CodePtr = prove(
  ``word_ml_inv (heap,be,a,sp) limit c s.refs ((CodePtr n,v)::xs) ==>
    (v = Loc n 0)``,
  fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
  \\ fs [abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
  \\ rw [word_addr_def]);

val state_rel_CodePtr = prove(
  ``state_rel c l1 l2 s t [] locs /\
    get_vars args s = SOME x /\
    get_vars (MAP adjust_var args) t = SOME y /\
    LAST x = CodePtr n /\ x <> [] ==>
    y <> [] /\ LAST y = Loc n 0``,
  rpt strip_tac
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  THEN1 (rw [] \\ fs [] \\ Cases_on `x` \\ fs [])
  \\ `args <> []` by (Cases_on `args` \\ fs [] \\ Cases_on `x` \\ fs [])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES]
  \\ full_simp_tac bool_ss [MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ rw []
  \\ full_simp_tac bool_ss [LAST_SNOC] \\ rw []
  \\ fs [state_rel_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_var_IMP \\ fs []
  \\ imp_res_tac word_ml_inv_CodePtr);

val find_code_thm = prove(
  ``!(s:'ffi bvpSem$state) (t:('a,'ffi)wordSem$state).
      state_rel c l1 l2 s t [] locs /\
      get_vars args s = SOME x /\
      get_vars (0::MAP adjust_var args) t = SOME (Loc l1 l2::ws) /\
      find_code dest x s.code = SOME (q,r) ==>
      ?args1 n1 n2.
        find_code dest (Loc l1 l2::ws) t.code = SOME (args1,FST (comp c n1 n2 r)) /\
        state_rel c l1 l2 (call_env q (dec_clock s))
          (call_env args1 (dec_clock t)) [] locs``,
  Cases_on `dest` \\ rw [] \\ fs [find_code_def]
  \\ every_case_tac \\ fs [wordSemTheory.find_code_def] \\ rw []
  \\ `code_rel c s.code t.code` by fs [state_rel_def]
  \\ fs [code_rel_def] \\ res_tac \\ fs [ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma
  \\ fs [wordSemTheory.get_vars_def]
  \\ Cases_on `get_var 0 t` \\ fs []
  \\ Cases_on `get_vars (MAP adjust_var args) t` \\ fs [] \\ rw []
  \\ TRY (imp_res_tac state_rel_CodePtr \\ fs []
          \\ qpat_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ fs [])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  THENL [Q.LIST_EXISTS_TAC [`n`,`1`],Q.LIST_EXISTS_TAC [`x'`,`1`]] \\ fs []
  \\ imp_res_tac state_rel_call_env \\ fs []
  \\ `args <> []` by (Cases_on `args` \\ fs [] \\ Cases_on `x` \\ fs [])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ rw []
  \\ fs [MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP \\ rw []
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ rw []
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ `get_vars (0::MAP adjust_var x2) t = SOME (Loc l1 l2::y2')` by
        fs [wordSemTheory.get_vars_def]
  \\ imp_res_tac state_rel_call_env \\ fs []) |> SPEC_ALL;

val IS_SOME_IF = prove(
  ``IS_SOME (if b then x else y) = if b then IS_SOME x else IS_SOME y``,
  Cases_on `b` \\ fs []);

val PERM_ALL_DISTINCT_MAP = prove(
  ``!xs ys. PERM xs ys ==>
            ALL_DISTINCT (MAP f xs) ==>
            ALL_DISTINCT (MAP f ys) /\ !x. MEM x ys <=> MEM x xs``,
  fs [MEM_PERM] \\ rw []
  \\ `PERM (MAP f xs) (MAP f ys)` by fs [PERM_MAP]
  \\ metis_tac [ALL_DISTINCT_PERM])

val GENLIST_I =
  GENLIST_EL |> Q.SPECL [`xs`,`\i. EL i xs`,`LENGTH xs`]
    |> SIMP_RULE std_ss []

val ALL_DISTINCT_EL = ``ALL_DISTINCT xs``
  |> ONCE_REWRITE_CONV [GSYM GENLIST_I]
  |> SIMP_RULE std_ss [ALL_DISTINCT_GENLIST]

val PERM_list_rearrange = prove(
  ``!f xs. ALL_DISTINCT xs ==> PERM xs (list_rearrange f xs)``,
  rw [] \\ match_mp_tac PERM_ALL_DISTINCT \\ fs [mem_list_rearrange]
  \\ fs [wordSemTheory.list_rearrange_def] \\ rw []
  \\ fs [ALL_DISTINCT_GENLIST] \\ rw []
  \\ fs [BIJ_DEF,INJ_DEF,SURJ_DEF]
  \\ fs [ALL_DISTINCT_EL]);

val ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME = prove(
  ``!xs x y. ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==> ALOOKUP xs x = SOME y``,
  Induct \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []
  \\ res_tac \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []) |> SPEC_ALL;

val env_to_list_lookup_equiv = prove(
  ``env_to_list y f = (q,r) ==>
    (!n. ALOOKUP q n = lookup n y) /\
    (!x1 x2. MEM (x1,x2) q ==> lookup x1 y = SOME x2)``,
  fs [wordSemTheory.env_to_list_def,LET_DEF] \\ rw []
  \\ `ALL_DISTINCT (MAP FST (toAList y))` by fs [ALL_DISTINCT_MAP_FST_toAList]
  \\ imp_res_tac (MATCH_MP PERM_ALL_DISTINCT_MAP
        (QSORT_PERM |> Q.ISPEC `key_val_compare` |> SPEC_ALL))
  \\ `ALL_DISTINCT (QSORT key_val_compare (toAList y))`
        by imp_res_tac ALL_DISTINCT_MAP
  \\ pop_assum (assume_tac o Q.SPEC `f (0:num)` o MATCH_MP PERM_list_rearrange)
  \\ imp_res_tac PERM_ALL_DISTINCT_MAP
  \\ rpt (qpat_assum `!x. pp ==> qq` (K all_tac))
  \\ rpt (qpat_assum `!x y. pp ==> qq` (K all_tac)) \\ rfs []
  \\ rpt (pop_assum (mp_tac o Q.GEN `x` o SPEC_ALL))
  \\ rpt (pop_assum (mp_tac o SPEC ``f:num->num->num``))
  \\ Q.ABBREV_TAC `xs =
       (list_rearrange (f 0) (QSORT key_val_compare (toAList y)))`
  \\ rpt strip_tac \\ rfs[MEM_toAList]
  \\ Cases_on `?i. MEM (n,i) xs` \\ fs [] THEN1
     (imp_res_tac ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME \\ fs []
      \\ UNABBREV_ALL_TAC \\ fs [] \\ rfs [MEM_toAList])
  \\ `~MEM n (MAP FST xs)` by rfs [MEM_MAP,FORALL_PROD]
  \\ fs [GSYM ALOOKUP_NONE]
  \\ UNABBREV_ALL_TAC \\ fs [] \\ rfs [MEM_toAList]
  \\ Cases_on `lookup n y` \\ fs []);

val cut_env_adjust_set_lookup_0 = prove(
  ``wordSem$cut_env (adjust_set r) x = SOME y ==> lookup 0 y = lookup 0 x``,
  fs [wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup,adjust_set_def,
      lookup_fromAList] \\ rw [lookup_inter]
  \\ pop_assum (qspec_then `0` mp_tac) \\ fs []
  \\ rw [] \\ fs [lookup_fromAList,lookup_inter]);

val cut_env_IMP_MEM = prove(
  ``bvpSem$cut_env s r = SOME x ==>
    (IS_SOME (lookup n x) <=> IS_SOME (lookup n s))``,
  fs [cut_env_def,SUBSET_DEF,domain_lookup]
  \\ rw [] \\ fs [lookup_inter] \\ every_case_tac \\ fs []
  \\ res_tac \\ fs[]);

val cut_env_IMP_lookup = prove(
  ``wordSem$cut_env s r = SOME x /\ lookup n x = SOME q ==>
    lookup n r = SOME q``,
  fs [wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ rw [] \\ fs [lookup_inter] \\ every_case_tac \\ fs []);

val cut_env_IMP_lookup_EQ = prove(
  ``bvpSem$cut_env r y = SOME x /\ n IN domain r ==>
    lookup n x = lookup n y``,
  fs [bvpSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ rw [] \\ fs [lookup_inter] \\ every_case_tac \\ fs []);

val cut_env_res_IS_SOME_IMP = prove(
  ``wordSem$cut_env r x = SOME y /\ IS_SOME (lookup k y) ==>
    IS_SOME (lookup k x) /\ IS_SOME (lookup k r)``,
  fs [wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ rw [] \\ fs [lookup_inter] \\ every_case_tac \\ fs []);

val unit_opt_eq = prove(
  ``(x = y:unit option) <=> (IS_SOME x <=> IS_SOME y)``,
  Cases_on `x` \\ Cases_on `y` \\ fs []);

val IS_SOME_ALOOKUP_EQ = prove(
  ``!l x. IS_SOME (ALOOKUP l x) = MEM x (MAP FST l)``,
  Induct \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []);

val lookup_adjust_var_adjust_set = prove(
  ``lookup (adjust_var n) (adjust_set s) = lookup n s``,
  fs [lookup_def,adjust_set_def,lookup_fromAList,unit_opt_eq]
  \\ fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ fs [MEM_toAList] \\ Cases_on `lookup n s` \\ fs []);

val adjust_var_cut_env_IMP_MEM = prove(
  ``wordSem$cut_env (adjust_set s) r = SOME x ==>
    (IS_SOME (lookup (adjust_var n) x) <=> IS_SOME (lookup n s))``,
  fs [wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ rw [] \\ fs [lookup_inter] \\ every_case_tac \\ fs []
  \\ res_tac \\ fs [] \\ rw [] \\ fs [lookup_adjust_var_adjust_set]);

val MEM_IMP_IS_SOME_ALOOKUP = prove(
  ``!l x y. MEM (x,y) l ==> IS_SOME (ALOOKUP l x)``,
  fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD] \\ metis_tac []);

val state_rel_call_env_push_env = prove(
  ``!opt:(num # 'a wordLang$prog # num # num) option.
      state_rel c l1 l2 s (t:('a,'ffi)wordSem$state) [] locs /\
      get_vars args s = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      bvpSem$cut_env r s.locals = SOME x /\
      wordSem$cut_env (adjust_set r) t.locals = SOME y ==>
      state_rel c q l (call_env xs (push_env x (IS_SOME opt) (dec_clock s)))
       (call_env (Loc q l::ws) (push_env y opt (dec_clock t))) []
       ((l1,l2)::locs)``,
  Cases \\ TRY (PairCases_on `x'`) \\ fs []
  \\ fs [state_rel_def,call_env_def,push_env_def,dec_clock_def,
         wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF,stack_rel_def]
  \\ fs [lookup_adjust_var_fromList2,contains_loc_def] \\ strip_tac
  \\ fs [lookup_fromList,lookup_fromAList]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ fs [IS_SOME_IF]
  \\ fs [lookup_fromList2,lookup_fromList]
  \\ imp_res_tac env_to_list_lookup_equiv \\ fs []
  \\ imp_res_tac cut_env_adjust_set_lookup_0 \\ fs []
  \\ imp_res_tac cut_env_IMP_MEM
  \\ imp_res_tac adjust_var_cut_env_IMP_MEM \\ fs []
  \\ imp_res_tac EVERY2_LENGTH \\ fs []
  \\ first_assum (match_exists_tac o concl) \\ fs [] (* asm_exists_tac *)
  \\ fs [flat_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ rw [] \\ fs[]
  \\ TRY (rpt disj1_tac
    \\ Cases_on `x'` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
    \\ fs [MEM_toAList] \\ rw [MEM_ZIP]
    \\ fs [lookup_fromList2,lookup_fromList]
    \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
    \\ fs [DIV_LT_X]
    \\ `k < 2 + LENGTH xs * 2 /\ 0 < LENGTH xs * 2` by
     (rfs [] \\ Cases_on `xs` \\ fs []
      THEN1 (Cases_on `k` \\ fs [] \\ Cases_on `n` \\ fs [] \\ decide_tac)
      \\ fs [MULT_CLAUSES] \\ decide_tac)
    \\ fs [] \\ qexists_tac `(k - 2) DIV 2` \\ fs []
    \\ fs [DIV_LT_X]
    \\ Cases_on `k` \\ fs []
    \\ Cases_on `n` \\ fs [DECIDE ``SUC (SUC n) = n + 2``]
    \\ fs [MATCH_MP ADD_DIV_RWT (DECIDE ``0<2:num``)]
    \\ fs [GSYM ADD1,EL] \\ NO_TAC)
  \\ fs [] \\ disj1_tac \\ disj2_tac
  \\ Cases_on `x'` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [MEM_toAList] \\ rw [MEM_ZIP]
  \\ fs [lookup_fromList2,lookup_fromList]
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ qexists_tac `k` \\ fs [] \\ res_tac
  \\ imp_res_tac cut_env_IMP_lookup \\ fs [] \\ AP_TERM_TAC
  \\ match_mp_tac cut_env_IMP_lookup_EQ \\ fs []
  \\ fs [domain_lookup] \\ imp_res_tac MEM_IMP_IS_SOME_ALOOKUP \\ rfs[]
  \\ imp_res_tac cut_env_res_IS_SOME_IMP
  \\ fs [IS_SOME_EXISTS]
  \\ fs [adjust_set_def,lookup_fromAList] \\ rfs []
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ fs [MEM_MAP] \\ Cases_on `y'` \\ fs []
  \\ fs [ONCE_REWRITE_RULE[MULT_COMM]adjust_var_def,MULT_DIV]
  \\ rw [] \\ fs [MEM_toAList]);

val find_code_thm_ret = prove(
  ``!(s:'ffi bvpSem$state) (t:('a,'ffi)wordSem$state).
      state_rel c l1 l2 s t [] locs /\
      get_vars args s = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      find_code dest xs s.code = SOME (ys,prog) /\
      bvpSem$cut_env r s.locals = SOME x /\
      wordSem$cut_env (adjust_set r) t.locals = SOME y ==>
      ?args1 n1 n2.
        find_code dest (Loc q l::ws) t.code = SOME (args1,FST (comp c n1 n2 prog)) /\
        state_rel c q l (call_env ys (push_env x F (dec_clock s)))
          (call_env args1 (push_env y
             (NONE:(num # ('a wordLang$prog) # num # num) option)
          (dec_clock t))) [] ((l1,l2)::locs)``,
  reverse (Cases_on `dest`) \\ rw [] \\ fs [find_code_def]
  \\ every_case_tac \\ fs [wordSemTheory.find_code_def] \\ rw []
  \\ `code_rel c s.code t.code` by fs [state_rel_def]
  \\ fs [code_rel_def] \\ res_tac \\ fs [ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ fs []
  \\ TRY (imp_res_tac state_rel_CodePtr \\ fs []
          \\ qpat_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ fs [])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  THEN1 (Q.LIST_EXISTS_TAC [`x'`,`1`] \\ fs []
         \\ qspec_then `NONE` mp_tac state_rel_call_env_push_env \\ fs [])
  \\ Q.LIST_EXISTS_TAC [`n`,`1`] \\ fs []
  \\ `args <> []` by (Cases_on `args` \\ fs [] \\ Cases_on `xs` \\ fs [])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ rw []
  \\ fs [MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP \\ rw []
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ rw []
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `NONE`
                   |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ fs [] \\ metis_tac []) |> SPEC_ALL;

val find_code_thm_handler = prove(
  ``!(s:'ffi bvpSem$state) (t:('a,'ffi)wordSem$state).
      state_rel c l1 l2 s t [] locs /\
      get_vars args s = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      find_code dest xs s.code = SOME (ys,prog) /\
      bvpSem$cut_env r s.locals = SOME x /\
      wordSem$cut_env (adjust_set r) t.locals = SOME y ==>
      ?args1 n1 n2.
        find_code dest (Loc q l::ws) t.code = SOME (args1,FST (comp c n1 n2 prog)) /\
        state_rel c q l (call_env ys (push_env x T (dec_clock s)))
          (call_env args1 (push_env y
             (SOME (adjust_var x0,(prog1:'a wordLang$prog),x0,l + 1))
          (dec_clock t))) [] ((l1,l2)::locs)``,
  reverse (Cases_on `dest`) \\ rw [] \\ fs [find_code_def]
  \\ every_case_tac \\ fs [wordSemTheory.find_code_def] \\ rw []
  \\ `code_rel c s.code t.code` by fs [state_rel_def]
  \\ fs [code_rel_def] \\ res_tac \\ fs [ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ fs []
  \\ TRY (imp_res_tac state_rel_CodePtr \\ fs []
          \\ qpat_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ fs [])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
  THEN1 (Q.LIST_EXISTS_TAC [`x'`,`1`] \\ fs []
         \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `SOME xx`
                   |> SIMP_RULE std_ss [] |> GEN_ALL) \\ fs [] \\ metis_tac [])
  \\ Q.LIST_EXISTS_TAC [`n`,`1`] \\ fs []
  \\ `args <> []` by (Cases_on `args` \\ fs [] \\ Cases_on `xs` \\ fs [])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ rw []
  \\ fs [MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP \\ rw []
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ rw []
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `SOME xx`
                   |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ fs [] \\ metis_tac []) |> SPEC_ALL;

val s_key_eq_LENGTH = prove(
  ``!xs ys. s_key_eq xs ys ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ fs [s_key_eq_def]);

val s_key_eq_LAST_N = prove(
  ``!xs ys n. s_key_eq xs ys ==> s_key_eq (LAST_N n xs) (LAST_N n ys)``,
  Induct \\ Cases_on `ys` \\ fs [s_key_eq_def,LAST_N]
  \\ rw [] \\ fs [s_key_eq_def,LAST_N] \\ res_tac
  \\ imp_res_tac s_key_eq_LENGTH \\ fs [] \\ `F` by decide_tac);

val evaluate_mk_loc_EQ = prove(
  ``evaluate (q,t) = (NONE,t1:('a,'b) state) ==>
    mk_loc (jump_exc t1) = ((mk_loc (jump_exc t)):'a word_loc)``,
  qspecl_then [`q`,`t`] mp_tac wordPropsTheory.evaluate_stack_swap \\ rw[]
  \\ fs [] \\ rw [] \\ fs [wordSemTheory.jump_exc_def]
  \\ imp_res_tac s_key_eq_LENGTH \\ fs []
  \\ rw [] \\ imp_res_tac s_key_eq_LAST_N
  \\ pop_assum (qspec_then `t.handler + 1` mp_tac)
  \\ every_case_tac \\ fs [s_key_eq_def,s_frame_key_eq_def,mk_loc_def])

val mk_loc_eq_push_env_exc_Exception = prove(
  ``evaluate
      (c:'a wordLang$prog, call_env args1
            (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l))
               (dec_clock t))) = (SOME (Exception xx w),(t1:('a,'b) state)) ==>
    mk_loc (jump_exc t1) = mk_loc (jump_exc t) :'a word_loc``,
  qspecl_then [`c`,`call_env args1
    (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l)) (dec_clock t))`]
       mp_tac wordPropsTheory.evaluate_stack_swap \\ rw [] \\ fs []
  \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF,LAST_N_ADD1]
  \\ rw [] \\ fs [wordSemTheory.jump_exc_def]
  \\ first_assum (qspec_then `t1.stack` mp_tac)
  \\ imp_res_tac s_key_eq_LENGTH \\ fs [] \\ rw []
  \\ imp_res_tac s_key_eq_LAST_N
  \\ pop_assum (qspec_then `t.handler+1` mp_tac) \\ rw []
  \\ every_case_tac \\ fs [s_key_eq_def,s_frame_key_eq_def,mk_loc_def]);

val evaluate_IMP_domain_EQ = prove(
  ``evaluate (c,call_env args1 (push_env y opt (dec_clock t))) =
      (SOME (Result ll w),t1) /\ pop_env t1 = SOME t2 ==>
    domain t2.locals = domain y``,
  qspecl_then [`c`,`call_env args1 (push_env y opt (dec_clock t))`] mp_tac
      wordPropsTheory.evaluate_stack_swap \\ fs [] \\ rw []
  \\ fs [wordSemTheory.call_env_def]
  \\ Cases_on `opt` \\ fs [] \\ TRY (PairCases_on `x`)
  \\ rw [] \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y (dec_clock t).permute` \\ fs [LET_DEF]
  \\ every_case_tac \\ fs [s_key_eq_def] \\ rw []
  \\ fs [wordSemTheory.env_to_list_def,LET_DEF] \\ rw []
  \\ fs [s_frame_key_eq_def,domain_fromAList] \\ rw []
  \\ qpat_assum `xxx = MAP FST l` (fn th => fs [GSYM th])
  \\ fs [EXTENSION,MEM_MAP,EXISTS_PROD,mem_list_rearrange,QSORT_MEM,
         domain_lookup,MEM_toAList]);

val evaluate_IMP_domain_EQ_Exc = prove(
  ``evaluate (c,call_env args1 (push_env y
      (SOME (x0,prog1:'a wordLang$prog,x1,l))
      (dec_clock (t:('a,'b) state)))) = (SOME (Exception ll w),t1) ==>
    domain t1.locals = domain y``,
  qspecl_then [`c`,`call_env args1
     (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l)) (dec_clock t))`]
     mp_tac wordPropsTheory.evaluate_stack_swap \\ rw [] \\ fs []
  \\ fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF,LAST_N_ADD1] \\ rw []
  \\ first_x_assum (qspec_then `t1.stack` mp_tac) \\ rw []
  \\ imp_res_tac s_key_eq_LAST_N \\ fs []
  \\ first_x_assum (qspec_then `t.handler+1` mp_tac) \\ rw []
  \\ fs [wordSemTheory.env_to_list_def,LET_DEF] \\ rw []
  \\ fs [s_frame_key_eq_def,domain_fromAList] \\ rw []
  \\ qpat_assum `xxx = MAP FST lss` (fn th => fs [GSYM th])
  \\ fs [EXTENSION,MEM_MAP,EXISTS_PROD,mem_list_rearrange,QSORT_MEM,
         domain_lookup,MEM_toAList]);

val mk_loc_jump_exc = prove(
  ``mk_loc
       (jump_exc
          (call_env args1
             (push_env y (SOME (adjust_var x0,prog1,x0,l))
                (dec_clock t)))) = Loc x0 l``,
  fs [wordSemTheory.push_env_def,wordSemTheory.call_env_def,
      wordSemTheory.jump_exc_def]
  \\ Cases_on `env_to_list y (dec_clock t).permute`
  \\ fs [LET_DEF,LAST_N_ADD1,mk_loc_def]);

val assign_thm = prove(
  ``state_rel c l1 l2 s t [] locs /\
    (op_space_reset op ==> names_opt <> NONE) /\
    cut_state_opt names_opt s = SOME s1 /\
    get_vars args s1 = SOME vals /\
    do_app op vals s1 = Rval (v,s2) /\
    evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) /\
    q <> SOME NotEnoughSpace ==>
    state_rel c l1 l2 (set_var dest v s2) r [] locs /\ q = NONE``,
  cheat);

val jump_exc_push_env_NONE_simp = prove(
  ``(jump_exc (dec_clock t) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (push_env y NONE t) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (call_env args s) = NONE <=> jump_exc s = NONE)``,
  fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
      wordSemTheory.dec_clock_def] \\ rw [] THEN1 every_case_tac
  \\ fs [wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF]
  \\ Cases_on `t.handler = LENGTH t.stack` \\ fs [LAST_N_ADD1]
  \\ Cases_on `~(t.handler < LENGTH t.stack)` \\ fs [] \\ rw []
  THEN1 (`F` by DECIDE_TAC)
  \\ `LAST_N (t.handler + 1) (StackFrame q NONE::t.stack) =
      LAST_N (t.handler + 1) t.stack` by
    (match_mp_tac miscTheory.LAST_N_TL \\ decide_tac) \\ fs []
  \\ every_case_tac \\ CCONTR_TAC
  \\ fs [NOT_LESS]
  \\ `SUC (LENGTH t.stack) <= t.handler + 1` by decide_tac
  \\ imp_res_tac (LAST_N_LENGTH_LESS_EQ |> Q.SPEC `x::xs`
       |> SIMP_RULE std_ss [LENGTH]) \\ fs []);

val s_key_eq_handler_eq_IMP = prove(
  ``s_key_eq t.stack t1.stack /\ t.handler = t1.handler ==>
    (jump_exc t1 <> NONE <=> jump_exc t <> NONE)``,
  fs [wordSemTheory.jump_exc_def] \\ rw []
  \\ imp_res_tac s_key_eq_LENGTH \\ fs []
  \\ Cases_on `t1.handler < LENGTH t1.stack` \\ fs []
  \\ imp_res_tac s_key_eq_LAST_N
  \\ pop_assum (qspec_then `t1.handler + 1` mp_tac)
  \\ every_case_tac \\ fs [s_key_eq_def,s_frame_key_eq_def]);

val eval_NONE_IMP_jump_exc_NONE_EQ = prove(
  ``evaluate (q,t) = (NONE,t1) ==> (jump_exc t1 = NONE <=> jump_exc t = NONE)``,
  rw [] \\ mp_tac (wordPropsTheory.evaluate_stack_swap |> Q.SPECL [`q`,`t`])
  \\ fs [] \\ rw [] \\ imp_res_tac s_key_eq_handler_eq_IMP \\ metis_tac []);

val jump_exc_push_env_SOME = prove(
  ``jump_exc (push_env y (SOME (x,prog1,l1,l2)) t) <> NONE``,
  fs [wordSemTheory.jump_exc_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF]
  \\ fs [LAST_N_ADD1]);

val eval_push_env_T_Raise_IMP_stack_length = prove(
  ``evaluate (p,call_env ys (push_env x T (dec_clock s))) =
       (SOME (Rerr (Rraise a)),r') ==>
    LENGTH r'.stack = LENGTH s.stack``,
  qspecl_then [`p`,`call_env ys (push_env x T (dec_clock s))`]
    mp_tac bvpPropsTheory.evaluate_stack_swap
  \\ rw [] \\ fs []
  \\ fs [call_env_def,jump_exc_def,push_env_def,dec_clock_def,LAST_N_ADD1]
  \\ rw [] \\ fs []);

val eval_push_env_SOME_exc_IMP_s_key_eq = prove(
  ``evaluate (p, call_env args1 (push_env y (SOME (x1,x2,x3,x4)) (dec_clock t))) =
      (SOME (Exception l w),t1) ==>
    s_key_eq t1.stack t.stack /\ t.handler = t1.handler``,
  qspecl_then [`p`,`call_env args1 (push_env y (SOME (x1,x2,x3,x4)) (dec_clock t))`]
    mp_tac wordPropsTheory.evaluate_stack_swap
  \\ rw [] \\ fs []
  \\ fs [wordSemTheory.call_env_def,wordSemTheory.jump_exc_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def,LAST_N_ADD1]
  \\ rw [] \\ fs []
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF,LAST_N_ADD1]
  \\ rw [] \\ fs []);

val eval_exc_stack_shorter = prove(
  ``evaluate (c,call_env ys (push_env x F (dec_clock s))) =
      (SOME (Rerr (Rraise a)),r') ==>
    LENGTH r'.stack < LENGTH s.stack``,
  rw [] \\ qspecl_then [`c`,`call_env ys (push_env x F (dec_clock s))`]
             mp_tac bvpPropsTheory.evaluate_stack_swap
  \\ fs [] \\ once_rewrite_tac [EQ_SYM_EQ] \\ rw [] \\ fs []
  \\ fs [bvpSemTheory.jump_exc_def,call_env_def,push_env_def,dec_clock_def]
  \\ qpat_assum `xx = SOME s2` mp_tac
  \\ rpt (pop_assum (K all_tac))
  \\ fs [LAST_N] \\ rw [] \\ fs [ADD1]
  \\ every_case_tac \\ fs [] \\ rw []
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `LENGTH (LAST_N (s.handler + 1) s.stack)`
  \\ fs [LENGTH_LAST_N_LESS]);

val alloc_size_def = Define `
  alloc_size k = if ~(k < dimword (:'a)) then -1w else n2w k:'a word`

val SUBSET_INSERT_EQ_SUBSET = prove(
  ``~(x IN s) ==> (s SUBSET (x INSERT t) <=> s SUBSET t)``,
  fs [EXTENSION]);

val NOT_1_domain = prove(
  ``~(1 IN domain (adjust_set names))``,
  fs [domain_fromAList,adjust_set_def,MEM_MAP,MEM_toAList,
      FORALL_PROD,adjust_var_def] \\ CCONTR_TAC \\ fs [] \\ decide_tac)

val cut_env_adjust_set_insert_1 = prove(
  ``cut_env (adjust_set names) (insert 1 w l) = cut_env (adjust_set names) l``,
  fs [wordSemTheory.cut_env_def,MATCH_MP SUBSET_INSERT_EQ_SUBSET NOT_1_domain]
  \\ rw [] \\ fs [lookup_inter,lookup_insert]
  \\ Cases_on `x = 1` \\ fs [] \\ every_case_tac \\ rw []
  \\ fs [SIMP_RULE std_ss [domain_lookup] NOT_1_domain]);

val case_EQ_SOME_IFF = prove(
  ``(case p of NONE => NONE | SOME x => g x) = SOME y <=>
    ?x. p = SOME x /\ g x = SOME y``,
  Cases_on `p` \\ fs []);

val state_rel_set_store_AllocSize = prove(
  ``state_rel c l1 l2 s (set_store AllocSize (Word w) t) v locs =
    state_rel c l1 l2 s t v locs``,
  fs [state_rel_def,wordSemTheory.set_store_def]
  \\ eq_tac \\ rw []
  \\ fs [heap_in_memory_store_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ metis_tac []);

val delete_odd_insert_1 = prove(
  ``delete_odd (insert 1 x t) = delete_odd t``,
  Cases_on `t` \\ EVAL_TAC);

val state_rel_insert_1 = prove(
  ``state_rel c l1 l2 s (t with locals := insert 1 x t.locals) v locs =
    state_rel c l1 l2 s t v locs``,
  fs [state_rel_def] \\ eq_tac \\ rw []
  \\ fs [lookup_insert,adjust_var_NEQ_1,delete_odd_insert_1]
  \\ metis_tac []);

val state_rel_inc_clock = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs ==>
    state_rel c l1 l2 (s with clock := s.clock + 1)
                      (t with clock := t.clock + 1) [] locs``,
  fs [state_rel_def]);

val dec_clock_inc_clock = prove(
  ``(bvpSem$dec_clock (s with clock := s.clock + 1) = s) /\
    (wordSem$dec_clock (t with clock := t.clock + 1) = t)``,
  fs [bvpSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
  \\ fs [bvpSemTheory.state_component_equality]
  \\ fs [wordSemTheory.state_component_equality])

val join_env_fromList_NIL = prove(
  ``join_env (fromList [])
        (toAList (delete_odd (fromList2 [Loc l1 l2]))) = []``,
  fs [join_env_def,fromList2_def] \\ EVAL_TAC);

val gc_lemma = prove(
  ``let t0 = call_env [Loc l1 l2] (push_env y
        (NONE:(num # 'a wordLang$prog # num # num) option) t) in
      bvpSem$cut_env names (s:'ffi bvpSem$state).locals = SOME x /\
      state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs /\
      FLOOKUP t.store AllocSize = SOME (Word (alloc_size k)) /\
      wordSem$cut_env (adjust_set names) t.locals = SOME y ==>
      ?t2 wl m st w1 w2 stack.
        t0.gc_fun (enc_stack t0.stack,t0.memory,t0.mdomain,t0.store) =
          SOME (wl,m,st) /\
        dec_stack wl t0.stack = SOME stack /\
        pop_env (t0 with <|stack := stack; store := st; memory := m|>) = SOME t2 /\
        FLOOKUP t2.store AllocSize = SOME (Word (alloc_size k)) /\
        state_rel c l1 l2 (s with locals := x) t2 [] locs``,
  rw [] \\ fs [LET_DEF]
  \\ Q.UNABBREV_TAC `t0` \\ fs []
  \\ Cases_on `env_to_list y t.permute` \\ fs [wordSemTheory.enc_stack_def]
  \\ rw [] \\ `t.gc_fun = word_gc_fun c` by fs [state_rel_def] \\ fs []
  \\ imp_res_tac (state_rel_call_env_push_env
      |> Q.SPEC `NONE` |> Q.INST [`args`|->`[]`] |> GEN_ALL
      |> SIMP_RULE std_ss [MAP,get_vars_def,wordSemTheory.get_vars_def]
      |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
      |> (fn th => MATCH_MP th (UNDISCH state_rel_inc_clock))
      |> SIMP_RULE (srw_ss()) [dec_clock_inc_clock] |> DISCH_ALL) \\ fs []
  \\ pop_assum (qspecl_then [`l1`,`l2`] mp_tac) \\ rw []
  \\ rfs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,LET_DEF]
  \\ fs [wordSemTheory.enc_stack_def]
  \\ pop_assum mp_tac \\ simp [Once state_rel_def]
  \\ fs [call_env_def,push_env_def] \\ rw []
  \\ pop_assum (K all_tac) \\ fs [join_env_fromList_NIL]
  \\ fs [flat_def]
  \\ first_x_assum (fn th1 => first_x_assum (fn th2 =>
       mp_tac (MATCH_MP word_gc_fun_correct (CONJ th1 th2))))
  \\ rw [] \\ fs []
  \\ cheat);

val gc_add_call_env = prove(
  ``(case gc (push_env y NONE t5) of
     | NONE => (SOME Error,x)
     | SOME s' => case pop_env s' of
                  | NONE => (SOME Error,s')
                  | SOME s' => f s') = (res,t) ==>
    (case gc (call_env [Loc l1 l2] (push_env y NONE t5)) of
     | NONE => (SOME Error,x)
     | SOME s' => case pop_env s' of
                  | NONE => (SOME Error,s')
                  | SOME s' => f s') = (res,t)``,
  cheat); (* wordSem needs fixing *)

val has_space_state_rel = prove(
  ``has_space (Word (alloc_size k)) r = SOME T /\
    state_rel c l1 l2 s r [] locs ==>
    state_rel c l1 l2 (s with space := s.space + k) r [] locs``,
  cheat); (* bvpSem needs fixing *)

val compile_correct = prove(
  ``!prog (s:'ffi bvpSem$state) c n l l1 l2 res s1 (t:('a,'ffi)wordSem$state) locs.
      (bvpSem$evaluate (prog,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] locs ==>
      ?t1 res1. (wordSem$evaluate (FST (comp c n l prog),t) = (res1,t1)) /\
                (res1 <> SOME NotEnoughSpace ==>
                 case res of
                 | NONE => state_rel c l1 l2 s1 t1 [] locs /\ (res1 = NONE)
                 | SOME (Rval v) =>
                     ?w. state_rel c l1 l2 s1 t1 [(v,w)] locs /\
                         (res1 = SOME (Result (Loc l1 l2) w))
                 | SOME (Rerr (Rraise v)) =>
                     ?w l5 l6 ll.
                       (res1 = SOME (Exception (mk_loc (jump_exc t)) w)) /\
                       (jump_exc t <> NONE ==>
                        LAST_N (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
                        !i. state_rel c l5 l6 (set_var i v s1)
                               (set_var (adjust_var i) w t1) [] ll)
                 | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut))``,
  recInduct bvpSemTheory.evaluate_ind \\ rpt strip_tac \\ fs []
  THEN1 (* Skip *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def] \\ rw [])
  THEN1 (* Move *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var src s` \\ fs [] \\ rw []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.set_vars_def,alist_insert_def]
    \\ fs [state_rel_def,set_var_def,lookup_insert]
    \\ rpt strip_tac \\ fs []
    THEN1 (rw [] \\ Cases_on `n = dest` \\ fs [])
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ fs []
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_insert \\ fs [])
  THEN1 (* Assign *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ imp_res_tac (METIS_PROVE [] ``(if b1 /\ b2 then x1 else x2) = y ==>
                                     b1 /\ b2 /\ x1 = y \/
                                     (b1 ==> ~b2) /\ x2 = y``)
    \\ fs [] \\ rw [] \\ Cases_on `cut_state_opt names_opt s` \\ fs []
    \\ Cases_on `get_vars args x` \\ fs []
    \\ reverse (Cases_on `do_app op x' x`) \\ fs []
    THEN1 (imp_res_tac do_app_Rerr \\ rw [])
    \\ Cases_on `evaluate (FST (assign c n l dest op args names_opt),t)`
    \\ fs [] \\ rw [] \\ Cases_on `a` \\ fs []
    \\ qpat_assum `NONE = res` (fn th => fs [GSYM th])
    \\ metis_tac [assign_thm])
  THEN1 (* Tick *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [] \\ rw [] \\ rpt (pop_assum mp_tac)
    \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def] \\ rw []
    \\ fs [state_rel_def,bvpSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ fs [])
  THEN1 (* MakeSpace *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def,
        GSYM alloc_size_def,LET_DEF]
    \\ rpt (pop_assum mp_tac) \\ BasicProvers.CASE_TAC \\ rpt strip_tac
    \\ rw [] \\ fs [add_space_def,wordSemTheory.word_exp_def,
         wordSemTheory.get_var_def,wordSemTheory.set_var_def]
    \\ Cases_on `(alloc (alloc_size k) (adjust_set names)
         (t with locals := insert 1 (Word (alloc_size k)) t.locals))
             :('a result option)#( ('a,'ffi) wordSem$state)` \\ fs []
    \\ fs [wordSemTheory.alloc_def,LET_DEF]
    \\ Q.ABBREV_TAC `t5 = (set_store AllocSize (Word (alloc_size k))
                 (t with locals := insert 1 (Word (alloc_size k)) t.locals))`
    \\ imp_res_tac cut_env_IMP_cut_env \\ fs [cut_env_adjust_set_insert_1]
    \\ first_x_assum (assume_tac o HO_MATCH_MP gc_add_call_env)
    \\ `FLOOKUP t5.store AllocSize = SOME (Word (alloc_size k)) /\
        cut_env (adjust_set names) t5.locals = SOME y /\
        state_rel c l1 l2 s t5 [] locs` by
     (UNABBREV_ALL_TAC \\ fs [state_rel_set_store_AllocSize]
      \\ fs [cut_env_adjust_set_insert_1,wordSemTheory.set_store_def]
      \\ rw [] \\ fs [SUBSET_DEF,state_rel_insert_1,FLOOKUP_DEF])
    \\ strip_tac
    \\ mp_tac (gc_lemma |> Q.INST [`t`|->`t5`] |> SIMP_RULE std_ss [LET_DEF])
    \\ fs [] \\ strip_tac \\ fs []
    \\ fs [wordSemTheory.gc_def,wordSemTheory.call_env_def,
           wordSemTheory.push_env_def]
    \\ Cases_on `env_to_list y t5.permute` \\ fs [LET_DEF]
    \\ `IS_SOME (has_space (Word (alloc_size k):'a word_loc) t2)` by
      fs [wordSemTheory.has_space_def,state_rel_def,heap_in_memory_store_def]
    \\ Cases_on `has_space (Word (alloc_size k):'a word_loc) t2` \\ fs []
    \\ every_case_tac \\ fs [] \\ rfs [] \\ rw []
    \\ imp_res_tac has_space_state_rel \\ fs [])
  THEN1 (* Raise *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s` \\ fs [] \\ rw []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ Cases_on `jump_exc s` \\ fs [] \\ rw []
    \\ imp_res_tac state_rel_jump_exc \\ fs []
    \\ rw [] \\ fs [] \\ rw [mk_loc_def])
  THEN1 (* Return *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s` \\ fs [] \\ rw []
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          fs [state_rel_def,wordSemTheory.get_var_def]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs [state_rel_def,wordSemTheory.call_env_def,lookup_def,
           bvpSemTheory.call_env_def,fromList_def,
           EVAL ``join_env LN (toAList (delete_odd (fromList2 [])))``]
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ fs []
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ pop_assum mp_tac
    \\ match_mp_tac word_ml_inv_rearrange
    \\ fs [] \\ rw [] \\ fs [])
  THEN1 (* Seq *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `comp c n l c1` \\ fs [LET_DEF]
    \\ Cases_on `comp c n r c2` \\ fs [LET_DEF]
    \\ fs [bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ fs [LET_DEF]
    \\ `q'' <> SOME (Rerr (Rabort Rtype_error))` by
         (Cases_on `q'' = NONE` \\ fs []) \\ fs []
    \\ qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
           first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`l`])
    \\ rpt strip_tac \\ rfs[]
    \\ reverse (Cases_on `q'' = NONE`) \\ fs []
    THEN1 (rpt strip_tac \\ fs [] \\ rw [] \\ Cases_on `q''` \\ fs []
           \\ Cases_on `x` \\ fs [] \\ Cases_on `e` \\ fs [])
    \\ rw [] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
      \\ rpt strip_tac \\ rfs [] \\ rpt strip_tac \\ fs []
      \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def] \\ fs []
      \\ imp_res_tac evaluate_mk_loc_EQ \\ fs []
      \\ metis_tac [eval_NONE_IMP_jump_exc_NONE_EQ])
    \\ Cases_on `res` \\ fs [])
  THEN1 (* If *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `comp c n l c1` \\ fs [LET_DEF]
    \\ Cases_on `comp c n r c2` \\ fs [LET_DEF]
    \\ fs [bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s` \\ fs []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ imp_res_tac get_var_T_OR_F
    \\ Cases_on `x = Boolv T` \\ fs [] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n`,`l`] mp_tac)
      \\ rpt strip_tac \\ rfs[]
      \\ metis_tac [eval_NONE_IMP_jump_exc_NONE_EQ])
    \\ Cases_on `x = Boolv F` \\ fs [] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n`,`r`] mp_tac)
      \\ rpt strip_tac \\ rfs[]
      \\ metis_tac [eval_NONE_IMP_jump_exc_NONE_EQ]))
  THEN1 (* Call *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `ret`
    \\ fs [bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def,
           wordSemTheory.add_ret_loc_def]
    THEN1 (* ret = NONE *)
     (Cases_on `get_vars args s` \\ fs []
      \\ imp_res_tac state_rel_0_get_vars_IMP \\ fs []
      \\ Cases_on `find_code dest x s.code` \\ fs []
      \\ Cases_on `x'` \\ fs [] \\ Cases_on `handler` \\ fs []
      \\ `t.clock = s.clock` by fs [state_rel_def]
      \\ mp_tac find_code_thm \\ fs [] \\ rw [] \\ fs []
      \\ Cases_on `s.clock = 0` \\ fs [] \\ rw [] \\ fs []
      \\ Cases_on `evaluate (r,call_env q (dec_clock s))` \\ fs []
      \\ Cases_on `q'` \\ fs [] \\ rw [] \\ fs [] \\ res_tac
      \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac)
      \\ Cases_on `res1` \\ fs [] \\ rw [] \\ fs []
      \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def]
      \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def]
      \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def])
    \\ Cases_on `x` \\ fs [LET_DEF]
    \\ Cases_on `handler` \\ fs [wordSemTheory.evaluate_def]
    \\ Cases_on `get_vars args s` \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP \\ fs []
    \\ fs [wordSemTheory.add_ret_loc_def]
    THEN1 (* no handler *)
     (Cases_on `find_code dest x s.code` \\ fs [] \\ Cases_on `x'` \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest xs s.code = SOME (ys,prog)`
      \\ Cases_on `bvpSem$cut_env r s.locals` \\ fs []
      \\ imp_res_tac cut_env_IMP_cut_env \\ fs [] \\ rw []
      \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
      \\ mp_tac find_code_thm_ret \\ fs [] \\ rw [] \\ fs []
      \\ Cases_on `s.clock = 0` \\ fs [] \\ rw []
      \\ Cases_on `evaluate (prog,call_env ys (push_env x F (dec_clock s)))`
      \\ fs [] \\ Cases_on `q'` \\ fs []
      \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ fs []
      \\ res_tac (* inst ind hyp *)
      \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs []
      \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
      \\ reverse (Cases_on `x'` \\ fs [])
      THEN1 (Cases_on `e` \\ fs [] \\ rw []
        \\ fs [jump_exc_call_env,jump_exc_dec_clock,jump_exc_push_env_NONE]
        \\ Cases_on `jump_exc t = NONE` \\ fs []
        \\ fs [jump_exc_push_env_NONE_simp]
        \\ `LENGTH r'.stack < LENGTH locs` by ALL_TAC
        \\ imp_res_tac LAST_N_TL \\ fs []
        \\ `LENGTH locs = LENGTH s.stack` by
           (fs [state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs []) \\ fs []
        \\ imp_res_tac eval_exc_stack_shorter)
      \\ Cases_on `pop_env r'` \\ fs [] \\ rw []
      \\ rpt strip_tac \\ fs []
      \\ imp_res_tac state_rel_pop_env_set_var_IMP \\ fs [] \\ rw []
      \\ imp_res_tac evaluate_IMP_domain_EQ \\ fs [])
    (* with handler *)
    \\ PairCases_on `x` \\ fs []
    \\ `?prog1 h1. comp c x0 (l + 2) x1 = (prog1,h1)` by METIS_TAC [PAIR]
    \\ fs [wordSemTheory.evaluate_def,wordSemTheory.add_ret_loc_def]
    \\ Cases_on `find_code dest x' s.code` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `find_code dest xs s.code = SOME (ys,prog)`
    \\ Cases_on `bvpSem$cut_env r s.locals` \\ fs []
    \\ imp_res_tac cut_env_IMP_cut_env \\ fs [] \\ rw []
    \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
    \\ mp_tac find_code_thm_handler \\ fs [] \\ rw [] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs [] \\ rw []
    \\ Cases_on `evaluate (prog,call_env ys (push_env x T (dec_clock s)))`
    \\ fs [] \\ Cases_on `q'` \\ fs []
    \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ fs []
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs []
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
    \\ Cases_on `x'` \\ fs [] THEN1
     (Cases_on `pop_env r'` \\ fs [] \\ rw []
      \\ rpt strip_tac \\ fs []
      \\ imp_res_tac state_rel_pop_env_set_var_IMP \\ fs [] \\ rw []
      \\ imp_res_tac evaluate_IMP_domain_EQ \\ fs [])
    \\ reverse (Cases_on `e`) \\ fs [] THEN1 (fs [] \\ rw [])
    \\ fs [mk_loc_jump_exc]
    \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ fs []
    \\ qpat_assum `!x y z.bbb` (K ALL_TAC)
    \\ fs [jump_exc_push_env_NONE_simp,jump_exc_push_env_SOME]
    \\ imp_res_tac eval_push_env_T_Raise_IMP_stack_length
    \\ `LENGTH s.stack = LENGTH locs` by
         (fs [state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ fs []) \\ fs []
    \\ fs [LAST_N_ADD1] \\ rw []
    \\ first_x_assum (qspec_then `x0` assume_tac)
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum (qspecl_then [`x0`,`l+2`] strip_assume_tac) \\ fs [] \\ rfs []
    \\ `jump_exc (set_var (adjust_var x0) w t1) = jump_exc t1` by
          fs [wordSemTheory.set_var_def,wordSemTheory.jump_exc_def]
    \\ rw [] \\ fs [] \\ Cases_on `res` \\ fs []
    \\ Cases_on `x'` \\ fs [] \\ Cases_on `e` \\ fs []
    \\ imp_res_tac mk_loc_eq_push_env_exc_Exception \\ fs []
    \\ imp_res_tac eval_push_env_SOME_exc_IMP_s_key_eq
    \\ imp_res_tac s_key_eq_handler_eq_IMP
    \\ fs [] \\ metis_tac []));

val _ = export_theory();
