open preamble bvlSemTheory bvpSemTheory bvpPropsTheory copying_gcTheory
     int_bitwiseTheory bvp_to_wordPropsTheory finite_mapTheory
     bvp_to_wordTheory wordPropsTheory labPropsTheory whileTheory
     set_sepTheory semanticsPropsTheory word_to_wordProofTheory
     helperLib alignmentTheory;

val _ = new_theory "bvp_to_wordProof";

(* TODO: move *)

val word_index_test = store_thm("word_index_test",
  ``n < dimindex (:'a) ==> (w ' n <=> ((w && n2w (2 ** n)) <> 0w:'a word))``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [wordsTheory.word_index])

val word_bit_test = store_thm("word_bit_test",
  ``word_bit n w <=> ((w && n2w (2 ** n)) <> 0w:'a word)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
    [wordsTheory.word_index, DECIDE ``0n < d ==> (n <= d - 1) = (n < d)``])

val word_and_one_eq_0_iff = store_thm("word_and_one_eq_0_iff", (* same in stack_alloc *)
  ``!w. ((w && 1w) = 0w) <=> ~(w ' 0)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index])

val get_var_set_var = store_thm("get_var_set_var[simp]",
  ``get_var n (set_var n w s) = SOME w``,
  full_simp_tac(srw_ss())[wordSemTheory.get_var_def,wordSemTheory.set_var_def]);

val set_var_set_var = store_thm("set_var_set_var[simp]",
  ``set_var n v (set_var n w s) = set_var n v s``,
  fs[wordSemTheory.state_component_equality,wordSemTheory.set_var_def,
      insert_shadow]);

val toAList_LN = Q.store_thm("toAList_LN[simp]",
  `toAList LN = []`,
  EVAL_TAC)

val adjust_set_LN = Q.store_thm("adjust_set_LN[simp]",
  `adjust_set LN = insert 0 () LN`,
  srw_tac[][adjust_set_def,fromAList_def]);

val ALOOKUP_SKIP_LEMMA = prove(
  ``¬MEM n (MAP FST xs) /\ d = e ==>
    ALOOKUP (xs ++ [(n,d)] ++ ys) n = SOME e``,
  full_simp_tac(srw_ss())[ALOOKUP_APPEND] \\ fs[GSYM ALOOKUP_NONE])

val LAST_EQ = prove(
  ``(LAST (x::xs) = if xs = [] then x else LAST xs) /\
    (FRONT (x::xs) = if xs = [] then [] else x::FRONT xs)``,
  Cases_on `xs` \\ full_simp_tac(srw_ss())[]);

val LASTN_LIST_REL_LEMMA = prove(
  ``!xs1 ys1 xs n y ys x P.
      LASTN n xs1 = x::xs /\ LIST_REL P xs1 ys1 ==>
      ?y ys. LASTN n ys1 = y::ys /\ P x y /\ LIST_REL P xs ys``,
  Induct \\ Cases_on `ys1` \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ rpt strip_tac
  \\ imp_res_tac LIST_REL_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ `F` by decide_tac);

val LASTN_CONS_IMP_LENGTH = store_thm("LASTN_CONS_IMP_LENGTH",
  ``!xs n y ys.
      n <= LENGTH xs ==>
      (LASTN n xs = y::ys) ==> LENGTH (y::ys) = n``,
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT]
  \\ srw_tac[][] THEN1 decide_tac \\ full_simp_tac(srw_ss())[GSYM NOT_LESS]);

val LASTN_IMP_APPEND = store_thm("LASTN_IMP_APPEND",
  ``!xs n ys.
      n <= LENGTH xs /\ (LASTN n xs = ys) ==>
      ?zs. xs = zs ++ ys /\ LENGTH ys = n``,
  Induct \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][] THEN1 decide_tac
  \\ `n <= LENGTH xs` by decide_tac \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_assum `xs = zs ++ LASTN n xs` (fn th => simp [Once th]));

val NOT_NIL_IMP_LAST = prove(
  ``!xs x. xs <> [] ==> LAST (x::xs) = LAST xs``,
  Cases \\ full_simp_tac(srw_ss())[]);

val IS_SOME_IF = prove(
  ``IS_SOME (if b then x else y) = if b then IS_SOME x else IS_SOME y``,
  Cases_on `b` \\ full_simp_tac(srw_ss())[]);

val PERM_ALL_DISTINCT_MAP = prove(
  ``!xs ys. PERM xs ys ==>
            ALL_DISTINCT (MAP f xs) ==>
            ALL_DISTINCT (MAP f ys) /\ !x. MEM x ys <=> MEM x xs``,
  full_simp_tac(srw_ss())[MEM_PERM] \\ srw_tac[][]
  \\ `PERM (MAP f xs) (MAP f ys)` by full_simp_tac(srw_ss())[PERM_MAP]
  \\ metis_tac [ALL_DISTINCT_PERM])

val GENLIST_I =
  GENLIST_EL |> Q.SPECL [`xs`,`\i. EL i xs`,`LENGTH xs`]
    |> SIMP_RULE std_ss []

val ALL_DISTINCT_EL = ``ALL_DISTINCT xs``
  |> ONCE_REWRITE_CONV [GSYM GENLIST_I]
  |> SIMP_RULE std_ss [ALL_DISTINCT_GENLIST]

val PERM_list_rearrange = prove(
  ``!f xs. ALL_DISTINCT xs ==> PERM xs (list_rearrange f xs)``,
  srw_tac[][] \\ match_mp_tac PERM_ALL_DISTINCT
  \\ full_simp_tac(srw_ss())[mem_list_rearrange]
  \\ full_simp_tac(srw_ss())[wordSemTheory.list_rearrange_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[ALL_DISTINCT_GENLIST] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[BIJ_DEF,INJ_DEF,SURJ_DEF]
  \\ full_simp_tac(srw_ss())[ALL_DISTINCT_EL]);

val ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME = prove(
  ``!xs x y. ALL_DISTINCT (MAP FST xs) /\ MEM (x,y) xs ==> ALOOKUP xs x = SOME y``,
  Induct \\ full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[MEM_MAP,FORALL_PROD]
  \\ rev_full_simp_tac(srw_ss())[]) |> SPEC_ALL;

val IS_SOME_ALOOKUP_EQ = prove(
  ``!l x. IS_SOME (ALOOKUP l x) = MEM x (MAP FST l)``,
  Induct \\ full_simp_tac(srw_ss())[]
  \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def] \\ srw_tac[][]);

val MEM_IMP_IS_SOME_ALOOKUP = prove(
  ``!l x y. MEM (x,y) l ==> IS_SOME (ALOOKUP l x)``,
  full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD] \\ metis_tac []);

val SUBSET_INSERT_EQ_SUBSET = prove(
  ``~(x IN s) ==> (s SUBSET (x INSERT t) <=> s SUBSET t)``,
  full_simp_tac(srw_ss())[EXTENSION]);

val EVERY2_IMP_EL = prove(
  ``!xs ys P n. EVERY2 P xs ys /\ n < LENGTH ys ==> P (EL n xs) (EL n ys)``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[]);

val FST_PAIR_EQ = prove(
  ``!x v. (FST x,v) = x <=> v = SND x``,
  Cases \\ full_simp_tac(srw_ss())[]);

val EVERY2_APPEND_IMP = prove(
  ``!xs1 xs2 zs P.
      EVERY2 P (xs1 ++ xs2) zs ==>
      ?zs1 zs2. zs = zs1 ++ zs2 /\ EVERY2 P xs1 zs1 /\ EVERY2 P xs2 zs2``,
  Induct \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ Q.LIST_EXISTS_TAC [`y::zs1`,`zs2`] \\ full_simp_tac(srw_ss())[]);

val ZIP_ID = prove(
  ``!xs. ZIP (MAP FST xs, MAP SND xs) = xs``,
  Induct \\ full_simp_tac(srw_ss())[]);

(* -- *)

(* -------------------------------------------------------
    word_ml_inv: definition and lemmas
   ------------------------------------------------------- *)

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

val flat_APPEND = prove(
  ``!xs ys xs1 ys1.
      LENGTH xs = LENGTH ys ==>
      flat (xs ++ xs1) (ys ++ ys1) = flat xs ys ++ flat xs1 ys1``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[flat_def] \\ srw_tac[][]
  \\ Cases_on `h'` \\ Cases_on `h`
  \\ TRY (Cases_on `o'`) \\ full_simp_tac(srw_ss())[flat_def]);

val adjust_var_DIV_2 = prove(
  ``(adjust_var n - 2) DIV 2 = n``,
  full_simp_tac(srw_ss())[ONCE_REWRITE_RULE[MULT_COMM]adjust_var_def,MULT_DIV]);

val EVEN_adjust_var = prove(
  ``EVEN (adjust_var n)``,
  full_simp_tac(srw_ss())[adjust_var_def,EVEN_MOD2,
    ONCE_REWRITE_RULE[MULT_COMM]MOD_TIMES]);

val adjust_var_NEQ_0 = prove(
  ``adjust_var n <> 0``,
  rpt strip_tac \\ full_simp_tac(srw_ss())[adjust_var_def]);

val adjust_var_NEQ_1 = prove(
  ``adjust_var n <> 1``,
  rpt strip_tac
  \\ `EVEN (adjust_var n) = EVEN 1` by full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVEN_adjust_var]);

val adjust_var_NEQ = store_thm("adjust_var_NEQ[simp]",
  ``adjust_var n <> 0 /\
    adjust_var n <> 1 /\
    adjust_var n <> 3 /\
    adjust_var n <> 5 /\
    adjust_var n <> 7 /\
    adjust_var n <> 9 /\
    adjust_var n <> 11 /\
    adjust_var n <> 13``,
  rpt strip_tac \\ fs [adjust_var_NEQ_0]
  \\ `EVEN (adjust_var n) = EVEN 1` by full_simp_tac(srw_ss())[]
  \\ `EVEN (adjust_var n) = EVEN 3` by full_simp_tac(srw_ss())[]
  \\ `EVEN (adjust_var n) = EVEN 5` by full_simp_tac(srw_ss())[]
  \\ `EVEN (adjust_var n) = EVEN 7` by full_simp_tac(srw_ss())[]
  \\ `EVEN (adjust_var n) = EVEN 9` by full_simp_tac(srw_ss())[]
  \\ `EVEN (adjust_var n) = EVEN 11` by full_simp_tac(srw_ss())[]
  \\ `EVEN (adjust_var n) = EVEN 13` by full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[EVEN_adjust_var]);

val unit_opt_eq = prove(
  ``(x = y:unit option) <=> (IS_SOME x <=> IS_SOME y)``,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[]);

val adjust_var_11 = prove(
  ``(adjust_var n = adjust_var m) <=> n = m``,
  full_simp_tac(srw_ss())[adjust_var_def,EQ_MULT_LCANCEL]);

val lookup_adjust_var_adjust_set = prove(
  ``lookup (adjust_var n) (adjust_set s) = lookup n s``,
  full_simp_tac(srw_ss())[lookup_def,adjust_set_def,lookup_fromAList,unit_opt_eq,adjust_var_NEQ_0]
  \\ full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ full_simp_tac(srw_ss())[MEM_toAList] \\ Cases_on `lookup n s` \\ full_simp_tac(srw_ss())[]);

val none_opt_eq = prove(
  ``((x = NONE) = (y = NONE)) <=> (IS_SOME x <=> IS_SOME y)``,
  Cases_on `x` \\ Cases_on `y` \\ full_simp_tac(srw_ss())[]);

val lookup_adjust_var_adjust_set_NONE = prove(
  ``lookup (adjust_var n) (adjust_set s) = NONE <=> lookup n s = NONE``,
  full_simp_tac(srw_ss())[lookup_def,adjust_set_def,lookup_fromAList,adjust_var_NEQ_0,none_opt_eq]
  \\ full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ full_simp_tac(srw_ss())[MEM_toAList] \\ Cases_on `lookup n s` \\ full_simp_tac(srw_ss())[]);

val lookup_adjust_var_adjust_set_SOME_UNIT = prove(
  ``lookup (adjust_var n) (adjust_set s) = SOME () <=> IS_SOME (lookup n s)``,
  Cases_on `lookup (adjust_var n) (adjust_set s) = NONE`
  \\ pop_assum (fn th => assume_tac th THEN
       assume_tac (SIMP_RULE std_ss [lookup_adjust_var_adjust_set_NONE] th))
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `lookup n s`
  \\ Cases_on `lookup (adjust_var n) (adjust_set s)` \\ full_simp_tac(srw_ss())[]);

val word_ml_inv_lookup = prove(
  ``word_ml_inv (heap,be,a,sp) limit c refs
      (ys ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs) /\
    lookup n l1 = SOME x /\
    lookup (adjust_var n) l2 = SOME w ==>
    word_ml_inv (heap,be,a,sp) limit c refs
      (ys ++ [(x,w)] ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs)``,
  full_simp_tac(srw_ss())[toAList_def,foldi_def,LET_DEF]
  \\ full_simp_tac(srw_ss())[GSYM toAList_def] \\ srw_tac[][]
  \\ `MEM (x,w) (join_env l1 (toAList (inter l2 (adjust_set l1))))` by
   (full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList,lookup_inter]
    \\ qexists_tac `adjust_var n` \\ full_simp_tac(srw_ss())[adjust_var_DIV_2,EVEN_adjust_var]
    \\ full_simp_tac(srw_ss())[adjust_var_NEQ_0] \\ every_case_tac
    \\ full_simp_tac(srw_ss())[lookup_adjust_var_adjust_set_NONE])
  \\ full_simp_tac(srw_ss())[MEM_SPLIT] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[adjust_var_def]
  \\ qpat_assum `word_ml_inv yyy limit c refs xxx` mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val word_ml_inv_get_var_IMP = store_thm("word_ml_inv_get_var_IMP",
  ``word_ml_inv (heap,be,a,sp) limit c refs
      (join_env s.locals (toAList (inter t.locals (adjust_set s.locals)))++envs) /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    word_ml_inv (heap,be,a,sp) limit c refs
      ([(x,w)]++join_env s.locals
          (toAList (inter t.locals (adjust_set s.locals)))++envs)``,
  srw_tac[][] \\ match_mp_tac (word_ml_inv_lookup
             |> Q.INST [`ys`|->`[]`] |> SIMP_RULE std_ss [APPEND])
  \\ full_simp_tac(srw_ss())[get_var_def,wordSemTheory.get_var_def]);

val word_ml_inv_get_vars_IMP = store_thm("word_ml_inv_get_vars_IMP",
  ``!n x w envs.
      word_ml_inv (heap,be,a,sp) limit c refs
        (join_env s.locals
           (toAList (inter t.locals (adjust_set s.locals)))++envs) /\
      get_vars n s.locals = SOME x /\
      get_vars (MAP adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp) limit c refs
        (ZIP(x,w)++join_env s.locals
           (toAList (inter t.locals (adjust_set s.locals)))++envs)``,
  Induct \\ full_simp_tac(srw_ss())[get_vars_def,wordSemTheory.get_vars_def] \\ rpt strip_tac
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac word_ml_inv_get_var_IMP
  \\ Q.MATCH_ASSUM_RENAME_TAC `bvpSem$get_var h s.locals = SOME x7`
  \\ Q.MATCH_ASSUM_RENAME_TAC `_ (adjust_var h) _ = SOME x8`
  \\ `word_ml_inv (heap,be,a,sp) limit c refs
        (join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
        (x7,x8)::envs)` by
   (pop_assum mp_tac \\ match_mp_tac word_ml_inv_rearrange
    \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ res_tac \\ pop_assum (K all_tac) \\ pop_assum mp_tac
  \\ match_mp_tac word_ml_inv_rearrange
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]) |> SPEC_ALL;

val IMP_adjust_var = prove(
  ``n <> 0 /\ EVEN n ==> adjust_var ((n - 2) DIV 2) = n``,
  full_simp_tac(srw_ss())[EVEN_EXISTS] \\ srw_tac[][] \\ Cases_on `m` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
  \\ once_rewrite_tac [MULT_COMM] \\ full_simp_tac(srw_ss())[MULT_DIV]
  \\ full_simp_tac(srw_ss())[adjust_var_def] \\ decide_tac);

val unit_some_eq_IS_SOME = prove(
  ``!x. (x = SOME ()) <=> IS_SOME x``,
  Cases \\ full_simp_tac(srw_ss())[]);

val word_ml_inv_insert = store_thm("word_ml_inv_insert",
  ``word_ml_inv (heap,F,a,sp) limit c refs
      ([(x,w)]++join_env d (toAList (inter l (adjust_set d)))++xs) ==>
    word_ml_inv (heap,F,a,sp) limit c refs
      (join_env (insert dest x d)
        (toAList (inter (insert (adjust_var dest) w l)
                           (adjust_set (insert dest x d))))++xs)``,
  match_mp_tac word_ml_inv_rearrange \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[MEM_toAList]
  \\ full_simp_tac(srw_ss())[lookup_insert,lookup_inter_alt]
  \\ Cases_on `dest = (p_1 - 2) DIV 2` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[adjust_var_DIV_2]
  \\ imp_res_tac IMP_adjust_var \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[domain_lookup] \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[adjust_var_11] \\ full_simp_tac(srw_ss())[]
  \\ disj1_tac \\ disj2_tac \\ qexists_tac `p_1` \\ full_simp_tac(srw_ss())[unit_some_eq_IS_SOME]
  \\ full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList] \\ rev_full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_insert] \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

(* -------------------------------------------------------
    definition and verification of GC function
   ------------------------------------------------------- *)

val theWord_def = Define `
  theWord (Word w) = w`

val isWord_def = Define `
  (isWord (Word w) = T) /\ (isWord _ = F)`;

val ptr_to_addr_def = Define `
  ptr_to_addr conf base (w:'a word) =
    base + ((w >>> (shift_length conf)) * bytes_in_word)`

val is_fwd_ptr_def = Define `
  (is_fwd_ptr (Word w) = ((w && 3w) = 0w)) /\
  (is_fwd_ptr _ = F)`;

val update_addr_def = Define `
  update_addr conf fwd_ptr (old_addr:'a word) =
    ((fwd_ptr << (shift_length conf)) ||
     ((shift_length conf - 1) -- 0) old_addr)`

val memcpy_def = Define `
  memcpy w a b m dm =
    if w = 0w then (b,m,T) else
      let (b1,m1,c1) = memcpy (w-1w) (a + bytes_in_word) (b + bytes_in_word)
                      ((b =+ m a) m) dm in
        (b1,m1,c1 /\ a IN dm /\ b IN dm)`

val word_gc_move_def = Define `
  (word_gc_move conf (Loc l1 l2,i,pa,old,m,dm) = (Loc l1 l2,i,pa,m,T)) /\
  (word_gc_move conf (Word w,i,pa,old,m,dm) =
     if (w && 1w) = 0w then (Word w,i,pa,m,T) else
       let c = (ptr_to_addr conf old w IN dm) in
       let v = m (ptr_to_addr conf old w) in
         if is_fwd_ptr v then
           (Word (update_addr conf (theWord v >>> 2) w),i,pa,m,c)
         else
           let header_addr = ptr_to_addr conf old w in
           let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
           let len = decode_length conf (theWord (m header_addr)) in
           let v = i + len + 1w in
           let (pa1,m1,c1) = memcpy (len+1w) header_addr pa m dm in
           let c = (c /\ header_addr IN dm /\ c1) in
           let m1 = (header_addr =+ Word (i << 2)) m1 in
             (Word (update_addr conf i w),v,pa1,m1,c))`

val word_gc_move_roots_def = Define `
  (word_gc_move_roots conf ([],i,pa,old,m,dm) = ([],i,pa,m,T)) /\
  (word_gc_move_roots conf (w::ws,i,pa,old,m,dm) =
     let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
     let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ws,i1,pa1,old,m1,dm) in
       (w1::ws2,i2,pa2,m2,c1 /\ c2))`

val word_gc_move_list_def = Define `
  word_gc_move_list conf (a:'a word,l:'a word,i,pa:'a word,old,m,dm) =
   if l = 0w then (a,i,pa,m,T) else
     let w = (m a):'a word_loc in
     let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
     let m1 = (a =+ w1) m1 in
     let (a2,i2,pa2,m2,c2) = word_gc_move_list conf (a+bytes_in_word,l-1w,i1,pa1,old,m1,dm) in
       (a2,i2,pa2,m2,a IN dm /\ c1 /\ c2)`

val word_gc_move_loop_def = Define `
  word_gc_move_loop k conf (pb,i,pa,old,m,dm,c) =
    if pb = pa then (i,pa,m,c) else
    if k = 0 then (i,pa,m,F) else
      let w = m pb in
      let c = (c /\ pb IN dm /\ isWord w) in
      let len = decode_length conf (theWord w) in
        if word_bit 2 (theWord w) then
          let pb = pb + (len + 1w) * bytes_in_word in
            word_gc_move_loop (k-1n) conf (pb,i,pa,old,m,dm,c)
        else
          let pb = pb + bytes_in_word in
          let (pb,i1,pa1,m1,c1) = word_gc_move_list conf (pb,len,i,pa,old,m,dm) in
            word_gc_move_loop (k-1n) conf (pb,i1,pa1,old,m1,dm,c /\ c1)`

val word_full_gc_def = Define `
  word_full_gc conf (all_roots,new,old:'a word,m,dm) =
    let (rs,i1,pa1,m1,c1) = word_gc_move_roots conf (all_roots,0w,new,old,m,dm) in
    let (i1,pa1,m1,c2) =
          word_gc_move_loop (dimword(:'a)) conf (new,i1,pa1,old,m1,dm,c1)
    in (rs,i1,pa1,m1,c2)`

val word_gc_fun_assum_def = Define `
  word_gc_fun_assum (conf:bvp_to_word$config) (s:store_name |-> 'a word_loc) <=>
    {Globals; CurrHeap; OtherHeap; HeapLength} SUBSET FDOM s /\
    isWord (s ' OtherHeap) /\
    isWord (s ' CurrHeap) /\
    isWord (s ' HeapLength) /\
    good_dimindex (:'a) /\
    conf.len_size <> 0 /\
    conf.len_size + 2 < dimindex (:'a) /\
    shift_length conf < dimindex (:'a)`

val word_gc_fun_def = Define `
  (word_gc_fun (conf:bvp_to_word$config)):'a gc_fun_type = \(roots,m,dm,s).
     let c = word_gc_fun_assum conf s in
     let new = theWord (s ' OtherHeap) in
     let old = theWord (s ' CurrHeap) in
     let len = theWord (s ' HeapLength) in
     let all_roots = s ' Globals::roots in
     let (roots1,i1,pa1,m1,c2) = word_full_gc conf (all_roots,new,old,m,dm) in
     let s1 = s |++ [(CurrHeap, Word new);
                     (OtherHeap, Word old);
                     (NextFree, Word pa1);
                     (EndOfHeap, Word (new + len));
                     (Globals, HD roots1)] in
       if c /\ c2 then SOME (TL roots1,m1,s1) else NONE`

val one_and_or_1 = prove(
  ``(1w && (w || 1w)) = 1w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val one_and_or_3 = prove(
  ``(3w && (w || 3w)) = 3w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val ODD_not_zero = prove(
  ``ODD n ==> n2w n <> 0w``,
  CCONTR_TAC \\ full_simp_tac std_ss []
  \\ `((n2w n):'a word) ' 0 = (0w:'a word) ' 0` by metis_tac []
  \\ full_simp_tac(srw_ss())[wordsTheory.word_index,bitTheory.BIT_def,bitTheory.BITS_THM]
  \\ full_simp_tac(srw_ss())[dimword_def,bitTheory.ODD_MOD2_LEM])

val three_not_0 = store_thm("three_not_0[simp]",
  ``3w <> 0w``,
  match_mp_tac ODD_not_zero \\ full_simp_tac(srw_ss())[]);

val DISJ_EQ_IMP = METIS_PROVE [] ``(~b \/ c) <=> (b ==> c)``

val three_and_shift_2 = prove(
  ``(3w && (w << 2)) = 0w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val shift_to_zero = prove(
  ``3w >>> 2 = 0w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val shift_around_under_big_shift = prove(
  ``!w n k. n <= k ==> (w << n >>> n << k = w << k)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val select_shift_out = prove(
  ``n <> 0 ==> ((n - 1 -- 0) (w || v << n) = (n - 1 -- 0) w)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val shift_length_NOT_ZERO = store_thm("shift_length_NOT_ZERO[simp]",
  ``shift_length conf <> 0``,
  full_simp_tac(srw_ss())[shift_length_def] \\ decide_tac);

val get_addr_and_1_not_0 = prove(
  ``(1w && get_addr conf k a) <> 0w``,
  Cases_on `a` \\ full_simp_tac(srw_ss())[get_addr_def,get_lowerbits_def]
  \\ rewrite_tac [one_and_or_1,GSYM WORD_OR_ASSOC] \\ full_simp_tac(srw_ss())[]);

val one_lsr_shift_length = prove(
  ``1w >>> shift_length conf = 0w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss]
    [word_index, shift_length_def])

val ptr_to_addr_get_addr = prove(
  ``k * 2 ** shift_length conf < dimword (:'a) ==>
    ptr_to_addr conf curr (get_addr conf k a) =
    curr + n2w k * bytes_in_word:'a word``,
  strip_tac
  \\ full_simp_tac(srw_ss())[ptr_to_addr_def,bytes_in_word_def,WORD_MUL_LSL,get_addr_def]
  \\ simp_tac std_ss [Once WORD_MULT_COMM] \\ AP_THM_TAC \\ AP_TERM_TAC
  \\ full_simp_tac(srw_ss())[get_lowerbits_LSL_shift_length,word_mul_n2w]
  \\ once_rewrite_tac [GSYM w2n_11]
  \\ rewrite_tac [w2n_lsr] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[MULT_DIV]
  \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
  \\ decide_tac);

val is_fws_ptr_OR_3 = prove(
  ``is_fwd_ptr (Word (w << 2)) /\ ~is_fwd_ptr (Word (w || 3w))``,
  full_simp_tac(srw_ss())[is_fwd_ptr_def] \\ rewrite_tac [one_and_or_3,three_and_shift_2]
  \\ full_simp_tac(srw_ss())[]);

val is_fws_ptr_OR_15 = prove(
  ``~is_fwd_ptr (Word (w || 15w))``,
  full_simp_tac(srw_ss())[is_fwd_ptr_def]
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, get_lowerbits_def]
  \\ qexists_tac `0` \\ fs []);

val select_get_lowerbits = prove(
  ``(shift_length conf − 1 -- 0) (get_lowerbits conf a) =
    get_lowerbits conf a``,
  Cases_on `a`
  \\ srw_tac [wordsLib.WORD_BIT_EQ_ss] [word_index, get_lowerbits_def]
  \\ eq_tac
  \\ rw []
  \\ fs []
  )

val LE_DIV_LT_IMP = prove(
  ``n <= l DIV 2 ** m /\ k < n ==> k * 2 ** m < l``,
  srw_tac[][] \\ `k < l DIV 2 ** m` by decide_tac
  \\ full_simp_tac(srw_ss())[X_LT_DIV,MULT_CLAUSES,GSYM ADD1]
  \\ Cases_on `2 ** m` \\ full_simp_tac(srw_ss())[]
  \\ decide_tac);

val word_bits_eq_slice_shift = store_thm("word_bits_eq_slice_shift",
  ``((k -- n) w) = (((k '' n) w) >>> n)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
  \\ Cases_on `i + n < dimindex (:'a)`
  \\ fs []
  )

val word_slice_or = prove(
  ``(k '' n) (w || v) = ((k '' n) w || (k '' n) v)``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index]
  \\ eq_tac
  \\ rw []
  \\ fs []
  )

val word_slice_lsl_eq_0 = prove(
  ``(k '' n) (w << (k + 1)) = 0w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val word_slice_2_3_eq_0 = prove(
  ``(n '' 2) 3w = 0w``,
  srw_tac [wordsLib.WORD_BIT_EQ_ss, boolSimps.CONJ_ss] [word_index])

val can_select_def = Define `
  can_select k n w <=> ((k - 1 -- n) (w << n) = w)`

val read_length_lemma = prove(
  ``can_select (n+2) 2 (n2w k :'a word) ==>
    (((n + 1 -- 2) (h ≪ (2 + n) ‖ n2w k ≪ 2 ‖ 3w)) = n2w k :'a word)``,
  full_simp_tac(srw_ss())[word_bits_eq_slice_shift,word_slice_or,can_select_def,DECIDE ``n+2-1=n+1n``]
  \\ full_simp_tac(srw_ss())[DECIDE ``2+n=n+1+1n``,word_slice_lsl_eq_0,word_slice_2_3_eq_0]);

val memcpy_thm = prove(
  ``!xs a:'a word c b m m1 dm b1 ys frame.
      memcpy (n2w (LENGTH xs):'a word) a b m dm = (b1,m1,c) /\
      (LENGTH ys = LENGTH xs) /\ LENGTH xs < dimword(:'a) /\
      (frame * word_list a xs * word_list b ys) (fun2set (m,dm)) ==>
      (frame * word_list a xs * word_list b xs) (fun2set (m1,dm)) /\
      b1 = b + n2w (LENGTH xs) * bytes_in_word /\ c``,
  Induct_on `xs` \\ Cases_on `ys`
  THEN1 (simp [LENGTH,Once memcpy_def,LENGTH])
  THEN1 (simp [LENGTH,Once memcpy_def,LENGTH])
  THEN1 (rpt strip_tac \\ full_simp_tac(srw_ss())[LENGTH])
  \\ rpt gen_tac \\ strip_tac
  \\ qpat_assum `_ = (b1,m1,c)`  mp_tac
  \\ once_rewrite_tac [memcpy_def]
  \\ asm_rewrite_tac [n2w_11]
  \\ drule LESS_MOD
  \\ simp_tac (srw_ss()) [ADD1,GSYM word_add_n2w]
  \\ pop_assum mp_tac
  \\ simp_tac (srw_ss()) [word_list_def,LET_THM]
  \\ pairarg_tac
  \\ first_x_assum drule
  \\ full_simp_tac(srw_ss())[] \\ NTAC 2 strip_tac
  \\ qpat_assum `_ = (b1',m1',c1)` mp_tac
  \\ SEP_W_TAC \\ SEP_F_TAC
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
  \\ rpt (disch_then assume_tac)
  \\ full_simp_tac(srw_ss())[] \\ imp_res_tac (DECIDE ``n+1n<k ==> n<k``) \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ SEP_R_TAC \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB]);

val word_payload_IMP = prove(
  ``word_payload addrs ll tags tt1 conf = (h,ts,T) ==> LENGTH ts = ll``,
  Cases_on `tags` \\ full_simp_tac(srw_ss())[word_payload_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val LESS_EQ_IMP_APPEND = prove(
  ``!n xs. n <= LENGTH xs ==> ?ys zs. xs = ys ++ zs /\ LENGTH ys = n``,
  Induct_on `xs` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[LENGTH_NIL]
  \\ srw_tac[][] \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ qexists_tac `h::ys` \\ full_simp_tac(srw_ss())[]);

val NOT_is_fwd_ptr = prove(
  ``word_payload addrs ll tag tt1 conf = (h,ts,c5) ==> ~is_fwd_ptr (Word h)``,
  Cases_on `tag` \\ fs [word_payload_def] \\ rw []
  \\ full_simp_tac std_ss [GSYM WORD_OR_ASSOC,is_fws_ptr_OR_3,is_fws_ptr_OR_15,
      isWord_def,theWord_def,make_header_def,LET_DEF,make_byte_header_def]);

val word_gc_move_thm = prove(
  ``(gc_move (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    (word_heap curr heap conf * word_list pa xs * frame) (fun2set (m,dm)) /\
    (word_gc_move conf (word_addr conf x,n2w a,pa,curr,m,dm) =
      (w:'a word_loc,i1,pa1,m1,c1)) /\
    LENGTH xs = n ==>
    ?xs1.
      (word_heap curr heap1 conf *
       word_heap pa h1 conf *
       word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
      (w = word_addr conf x1) /\
      heap_length heap1 = heap_length heap /\
      c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
      pa1 = pa + bytes_in_word * n2w (heap_length h1)``,
  reverse (Cases_on `x`) \\ full_simp_tac(srw_ss())[gc_move_def] THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[word_heap_def,SEP_CLAUSES]
    \\ Cases_on `a'` \\ full_simp_tac(srw_ss())[word_addr_def,word_gc_move_def]
    \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def])
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `heap_lookup k heap = SOME x`
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_addr_def]
  \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[word_gc_move_def,get_addr_and_1_not_0]
  \\ imp_res_tac copying_gcTheory.heap_lookup_LESS
  \\ drule LE_DIV_LT_IMP \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ full_simp_tac(srw_ss())[ptr_to_addr_get_addr,word_heap_def,SEP_CLAUSES]
  \\ imp_res_tac heap_lookup_SPLIT \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,word_el_def]
  THEN1
   (helperLib.SEP_R_TAC \\ full_simp_tac(srw_ss())[LET_THM,theWord_def,is_fws_ptr_OR_3]
    \\ srw_tac[][] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[update_addr_def,shift_to_zero]
    \\ `2 <= shift_length conf` by (full_simp_tac(srw_ss())[shift_length_def] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[shift_around_under_big_shift]
    \\ full_simp_tac(srw_ss())[get_addr_def,select_shift_out]
    \\ full_simp_tac(srw_ss())[select_get_lowerbits,heap_length_def])
  \\ qcase_tac `_ = SOME (DataElement addrs ll tt)`
  \\ PairCases_on `tt`
  \\ full_simp_tac(srw_ss())[word_el_def]
  \\ `?h ts c5. word_payload addrs ll tt0 tt1 conf =
         (h:'a word,ts,c5)` by METIS_TAC [PAIR]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac bool_ss [word_list_def]
  \\ SEP_R_TAC
  \\ full_simp_tac bool_ss [GSYM word_list_def]
  \\ full_simp_tac std_ss [GSYM WORD_OR_ASSOC,is_fws_ptr_OR_3,isWord_def,theWord_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR,SEP_CLAUSES]
  \\ `~is_fwd_ptr (Word h)` by (imp_res_tac NOT_is_fwd_ptr \\ fs [])
  \\ fs []
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ `n2w (LENGTH ts) + 1w = n2w (LENGTH (Word h::ts)):'a word` by
        full_simp_tac(srw_ss())[LENGTH,ADD1,word_add_n2w]
  \\ full_simp_tac bool_ss []
  \\ drule memcpy_thm
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ full_simp_tac(srw_ss())[gc_forward_ptr_thm] \\ rev_full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def]
  \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
  \\ imp_res_tac word_payload_IMP
  \\ rpt var_eq_tac
  \\ drule LESS_EQ_IMP_APPEND \\ strip_tac
  \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[word_list_APPEND]
  \\ disch_then (qspec_then `ys` assume_tac)
  \\ SEP_F_TAC
  \\ impl_tac THEN1
   (full_simp_tac(srw_ss())[ADD1,SUM_APPEND,X_LE_DIV,RIGHT_ADD_DISTRIB]
    \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES]
    \\ Cases_on `n'` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
  \\ rpt strip_tac
  \\ full_simp_tac(srw_ss())[word_addr_def,word_add_n2w,ADD_ASSOC] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
       SEP_CLAUSES,word_el_def,LET_THM]
  \\ full_simp_tac(srw_ss())[word_list_def]
  \\ SEP_W_TAC \\ qexists_tac `zs` \\ full_simp_tac(srw_ss())[]
  \\ reverse conj_tac THEN1
   (full_simp_tac(srw_ss())[update_addr_def,get_addr_def,
       select_shift_out,select_get_lowerbits,ADD1])
  \\ pop_assum mp_tac
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
  \\ full_simp_tac(srw_ss())[heap_length_def,SUM_APPEND,el_length_def,ADD1]
  \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ srw_tac[][] \\ qexists_tac `ts`
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,SEP_CLAUSES]);

val word_gc_move_roots_thm = prove(
  ``!x a n heap limit pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 w frame.
      (gc_move_list (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
      (word_heap curr heap conf * word_list pa xs * frame) (fun2set (m,dm)) /\
      (word_gc_move_roots conf (MAP (word_addr conf) x,n2w a,pa,curr,m,dm) =
        (w:'a word_loc list,i1,pa1,m1,c1)) /\
      LENGTH xs = n ==>
      ?xs1.
        (word_heap curr heap1 conf *
         word_heap pa h1 conf *
         word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        (w = MAP (word_addr conf) x1) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = pa + n2w (heap_length h1) * bytes_in_word``,
  Induct THEN1
   (full_simp_tac(srw_ss())[gc_move_list_def,word_gc_move_roots_def,word_heap_def,SEP_CLAUSES]
    \\ srw_tac[][] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[gc_move_list_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_list_ALT]
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ `c'` by imp_res_tac gc_move_list_ok \\ full_simp_tac(srw_ss())[]
  \\ drule (word_gc_move_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum drule
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `_ = (xs7,xs8,a7,LENGTH xs9,heap7,T)`
  \\ qexists_tac `xs9` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_heap_APPEND]
  \\ full_simp_tac(srw_ss())[AC STAR_COMM STAR_ASSOC]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB,heap_length_def,SUM_APPEND,GSYM word_add_n2w]);

val word_gc_move_list_thm = prove(
  ``!x a n heap limit pa x1 h1 a1 n1 heap1 pa1 m m1 xs i1 c1 frame k k1.
      (gc_move_list (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
      heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
      (word_gc_move_list conf (k,n2w (LENGTH x),n2w a,pa,curr,m,dm) =
        (k1,i1,pa1,m1,c1)) /\
      (word_heap curr heap conf * word_list pa xs *
       word_list k (MAP (word_addr conf) x) * frame) (fun2set (m,dm)) /\
      LENGTH xs = n /\ LENGTH x < dimword (:'a) ==>
      ?xs1.
        (word_heap curr heap1 conf *
         word_heap (pa:'a word) h1 conf *
         word_list pa1 xs1 *
         word_list k (MAP (word_addr conf) x1) * frame) (fun2set (m1,dm)) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        k1 = k + n2w (LENGTH x) * bytes_in_word /\
        pa1 = pa + n2w (heap_length h1) * bytes_in_word``,
  Induct THEN1
   (full_simp_tac(srw_ss())[gc_move_list_def,Once word_gc_move_list_def,word_heap_def,SEP_CLAUSES]
    \\ srw_tac[][] \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[heap_length_def])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[gc_move_list_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [gc_move_list_ALT]
  \\ full_simp_tac(srw_ss())[LET_THM] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_assum `word_gc_move_list conf _ = _` mp_tac
  \\ simp [Once word_gc_move_list_def,LET_THM] \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,ADD1]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ `c'` by imp_res_tac gc_move_list_ok \\ full_simp_tac(srw_ss())[] \\ pop_assum kall_tac
  \\ NTAC 2 (pop_assum mp_tac)
  \\ full_simp_tac(srw_ss())[word_list_def] \\ SEP_R_TAC \\ rpt strip_tac
  \\ drule (word_gc_move_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum drule
  \\ qpat_assum `word_gc_move_list conf _ = _` mp_tac
  \\ SEP_W_TAC \\ strip_tac
  \\ once_rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM] \\ full_simp_tac(srw_ss())[]
  \\ disch_then imp_res_tac
  \\ `LENGTH x < dimword (:'a)` by decide_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum kall_tac
  \\ SEP_F_TAC \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `_ = (xs7,xs8,a7,LENGTH xs9,heap7,T)`
  \\ qexists_tac `xs9` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_heap_APPEND]
  \\ full_simp_tac(srw_ss())[AC STAR_COMM STAR_ASSOC]
  \\ full_simp_tac(srw_ss())[WORD_LEFT_ADD_DISTRIB,heap_length_def,
        SUM_APPEND,GSYM word_add_n2w]);

val word_payload_swap = prove(
  ``word_payload l5 (LENGTH l5) tag r conf = (h,MAP (word_addr conf) l5,T) /\
    LENGTH xs' = LENGTH l5 ==>
    word_payload xs' (LENGTH l5) tag r conf = (h,MAP (word_addr conf) xs',T)``,
  Cases_on `tag` \\ full_simp_tac(srw_ss())[word_payload_def]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[LENGTH_NIL]);

val word_gc_move_loop_thm = prove(
  ``!h1 h2 a n heap c0 limit h11 a1 n1 heap1 i1 pa1 m1 c1 xs frame m k.
      (gc_move_loop (h1,h2,a,n,heap,c0,limit) = (h11,a1,n1,heap1,T)) /\ c0 /\
      heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
      heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
      conf.len_size + 2 < dimindex (:'a) /\
      (word_heap curr heap conf *
       word_heap new (h1 ++ h2) conf *
       word_list (new + n2w (heap_length (h1++h2)) * bytes_in_word) xs * frame)
         (fun2set (m,dm)) /\
      limit - heap_length h1 <= k /\
      limit = heap_length heap /\ good_dimindex (:'a) /\
      (word_gc_move_loop k conf (new + n2w (heap_length h1) * bytes_in_word,n2w a,
           new + n2w (heap_length (h1++h2)) * bytes_in_word,curr,m,dm,T) =
         (i1,pa1,m1,c1)) /\ LENGTH xs = n ==>
      ?xs1.
        (word_heap curr heap1 conf *
         word_heap (new:'a word) h11 conf *
         word_list pa1 xs1 * frame) (fun2set (m1,dm)) /\
        heap_length heap1 = heap_length heap /\
        c1 /\ (i1 = n2w a1) /\ n1 = LENGTH xs1 /\
        pa1 = new + bytes_in_word * n2w (heap_length h11)``,
  recInduct gc_move_loop_ind \\ rpt strip_tac
  THEN1
   (full_simp_tac(srw_ss())[gc_move_loop_def] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[]
    \\ pop_assum mp_tac \\ once_rewrite_tac [word_gc_move_loop_def]
    \\ full_simp_tac(srw_ss())[]
    \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `xs` \\ full_simp_tac(srw_ss())[AC STAR_COMM STAR_ASSOC])
  \\ qpat_assum `gc_move_loop _ = _` mp_tac
  \\ once_rewrite_tac [gc_move_loop_def]
  \\ IF_CASES_TAC \\ full_simp_tac(srw_ss())[]
  \\ CASE_TAC \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac gc_move_loop_ok \\ full_simp_tac(srw_ss())[]
  \\ qcase_tac `HD h5 = DataElement l5 n5 b5`
  \\ Cases_on `h5` \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ qpat_assum `word_gc_move_loop _ _ _ = _` mp_tac
  \\ once_rewrite_tac [word_gc_move_loop_def]
  \\ IF_CASES_TAC THEN1
   (`F` by all_tac
    \\ full_simp_tac(srw_ss())[heap_length_def,SUM_APPEND,el_length_def,
           WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ pop_assum mp_tac
    \\ Q.PAT_ABBREV_TAC `x = bytes_in_word * n2w (SUM (MAP el_length h1))`
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac std_ss [GSYM WORD_ADD_ASSOC,addressTheory.WORD_EQ_ADD_CANCEL]
    \\ full_simp_tac(srw_ss())[bytes_in_word_def,word_add_n2w,word_mul_n2w]
    \\ full_simp_tac(srw_ss())[NOT_LESS]
    \\ full_simp_tac(srw_ss())[GSYM heap_length_def]
    \\ qpat_assum `_ <= heap_length heap` mp_tac
    \\ qpat_assum `heap_length heap * _ < _ ` mp_tac
    \\ qpat_assum `good_dimindex (:'a)` mp_tac
    \\ rpt (pop_assum kall_tac) \\ srw_tac[][]
    \\ `dimindex (:α) DIV 8 + dimindex (:α) DIV 8 * n5 +
        dimindex (:α) DIV 8 * heap_length h2 < dimword (:α)` by all_tac
    \\ full_simp_tac(srw_ss())[]
    \\ rev_full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]
    \\ rev_full_simp_tac(srw_ss())[good_dimindex_def,dimword_def] \\ decide_tac)
  \\ Cases_on `b5`
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_def,
       SEP_CLAUSES,STAR_ASSOC,word_el_def]
  \\ qpat_assum `_ (fun2set (m,dm))` assume_tac
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pop_assum mp_tac
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac std_ss [word_list_def] \\ SEP_R_TAC
  \\ full_simp_tac(srw_ss())[isWord_def,theWord_def]
  \\ rev_full_simp_tac(srw_ss())[]
  \\ qcase_tac `word_payload _ _ tag _ conf = _`
  \\ drule word_payload_T_IMP
  \\ impl_tac THEN1 (fs []) \\ strip_tac
  \\ `k <> 0` by
   (fs [heap_length_APPEND,el_length_def,heap_length_def] \\ decide_tac)
  \\ full_simp_tac std_ss []
  \\ Cases_on `word_bit 2 h` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[]
  THEN1
   (full_simp_tac(srw_ss())[gc_move_list_def] \\ rpt var_eq_tac
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def,SUM_APPEND]
    \\ qpat_assum `!xx. nn` mp_tac
    \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
    \\ ntac 2 strip_tac \\ full_simp_tac(srw_ss())[SEP_CLAUSES]
    \\ first_x_assum match_mp_tac
    \\ qexists_tac `xs` \\ qexists_tac `m` \\ full_simp_tac(srw_ss())[]
    \\ qexists_tac `k - 1` \\ fs [])
  \\ qpat_assum `gc_move_list _ = _` mp_tac
  \\ once_rewrite_tac [gc_move_list_ALT] \\ strip_tac
  \\ full_simp_tac(srw_ss())[LET_THM]
  \\ pop_assum mp_tac
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ strip_tac
  \\ ntac 5 var_eq_tac
  \\ drule word_gc_move_list_thm \\ full_simp_tac(srw_ss())[]
  \\ ntac 2 strip_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum drule
  \\ disch_then (qspec_then `xs` mp_tac)
  \\ fs [] \\ strip_tac \\ SEP_F_TAC
  \\ impl_tac THEN1
   (full_simp_tac(srw_ss())[NOT_LESS] \\ qpat_assum `_ <= heap_length heap` mp_tac
    \\ qpat_assum `heap_length heap <= _ ` mp_tac
    \\ qpat_assum `heap_length heap <= _ ` mp_tac
    \\ rpt (pop_assum kall_tac) \\ full_simp_tac(srw_ss())[X_LE_DIV]
    \\ full_simp_tac(srw_ss())[heap_length_APPEND,heap_length_def,el_length_def]
    \\ Cases_on `2 ** shift_length conf` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `n` \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
  \\ strip_tac \\ fs []
  \\ ntac 5 var_eq_tac
  \\ `LENGTH xs' = LENGTH l5` by imp_res_tac gc_move_list_IMP_LENGTH
  \\ `word_payload xs' (LENGTH l5) tag r conf =
       (h,MAP (word_addr conf) xs',T)` by
         (match_mp_tac word_payload_swap \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
  \\ first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[heap_length_def,el_length_def,SUM_APPEND]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,SEP_CLAUSES]
  \\ qpat_assum `_ = (i1,pa1,m1,c1)` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ qexists_tac `xs1'` \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `m1'` \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `k-1` \\ fs []
  \\ qpat_assum `_ (fun2set (m1',dm))` mp_tac
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,heap_length_def,el_length_def,SUM_APPEND]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB,SEP_CLAUSES]
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM,word_heap_APPEND]);

val word_el_IMP_word_list_exists = prove(
  ``!temp p curr.
      (p * word_el curr temp conf) s ==>
      (p * word_list_exists curr (el_length temp)) s``,
  Cases \\ fs[word_el_def,el_length_def,GSYM ADD1,word_list_exists_thm]
  THEN1 (full_simp_tac(srw_ss())[SEP_CLAUSES,SEP_EXISTS_THM] \\ metis_tac [])
  \\ Cases_on `b`
  \\ fs[word_el_def,el_length_def,GSYM ADD1,word_list_exists_thm,LET_THM]
  \\ srw_tac[][] \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ srw_tac[][]
  \\ fs[word_list_def,SEP_CLAUSES,SEP_EXISTS_THM,word_list_exists_def]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ imp_res_tac word_payload_IMP \\ asm_exists_tac \\ fs [] \\ metis_tac []);

val word_heap_IMP_word_list_exists = prove(
  ``!temp p curr.
      (p * word_heap curr temp conf) s ==>
      (p * word_list_exists curr (heap_length temp)) s``,
  Induct \\ full_simp_tac(srw_ss())[heap_length_def,
              word_heap_def,word_list_exists_thm]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_el_def,word_list_exists_ADD]
  \\ full_simp_tac(srw_ss())[STAR_ASSOC] \\ res_tac
  \\ pop_assum mp_tac
  \\ once_rewrite_tac [STAR_COMM] \\ full_simp_tac(srw_ss())[STAR_ASSOC]
  \\ metis_tac [word_el_IMP_word_list_exists]);

val word_full_gc_thm = prove(
  ``(full_gc (roots,heap,limit) = (roots1,heap1,a1,T)) /\
    heap_length heap <= dimword (:'a) DIV 2 ** shift_length conf /\
    heap_length heap * (dimindex (:'a) DIV 8) < dimword (:'a) /\
    conf.len_size + 2 < dimindex (:'a) /\
    (word_heap (curr:'a word) heap conf *
     word_heap new (heap_expand limit) conf * frame) (fun2set (m,dm)) /\
    limit = heap_length heap /\ good_dimindex (:'a) /\
    (word_full_gc conf (MAP (word_addr conf) roots,new,curr,m,dm) =
       (rs1,i1,pa1,m1,c1)) ==>
    (word_heap new (heap1 ++ heap_expand (limit - a1)) conf *
     word_heap curr (heap_expand limit) conf * frame) (fun2set (m1,dm)) /\
    c1 /\ i1 = n2w a1 /\
    rs1 = MAP (word_addr conf) roots1 /\
    pa1 = new + bytes_in_word * n2w a1``,
  strip_tac \\ full_simp_tac(srw_ss())[full_gc_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_heap_def,word_el_def]
  \\ full_simp_tac(srw_ss())[SEP_CLAUSES]
  \\ imp_res_tac gc_move_loop_ok \\ full_simp_tac(srw_ss())[]
  \\ drule word_gc_move_roots_thm
  \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,
       SEP_EXISTS_THM,word_heap_heap_expand]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR]
  \\ full_simp_tac(srw_ss())[word_full_gc_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ drule word_gc_move_loop_thm
  \\ full_simp_tac(srw_ss())[heap_length_def]
  \\ once_rewrite_tac [CONJ_COMM] \\ full_simp_tac(srw_ss())[GSYM CONJ_ASSOC]
  \\ `SUM (MAP el_length heap) <= dimword (:'a)` by
   (fs [X_LE_DIV] \\ Cases_on `2n ** shift_length conf` \\ fs [MULT_CLAUSES])
  \\ disch_then drule
  \\ disch_then drule
  \\ strip_tac \\ SEP_F_TAC
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]
  \\ strip_tac \\ rpt var_eq_tac
  \\ full_simp_tac(srw_ss())[word_heap_APPEND,word_heap_heap_expand]
  \\ pop_assum mp_tac
  \\ full_simp_tac(srw_ss())[STAR_ASSOC]
  \\ CONV_TAC ((RATOR_CONV o RAND_CONV) (RATOR_CONV
       (MOVE_OUT_CONV ``word_heap (curr:'a word) (temp:'a ml_heap)``)))
  \\ strip_tac \\ drule word_heap_IMP_word_list_exists
  \\ full_simp_tac(srw_ss())[word_heap_heap_expand]
  \\ full_simp_tac(srw_ss())[word_list_exists_def,SEP_CLAUSES,SEP_EXISTS_THM]
  \\ full_simp_tac (std_ss++sep_cond_ss) [cond_STAR] \\ strip_tac
  \\ qcase_tac `LENGTH ys = heap_length temp`
  \\ qexists_tac `ys` \\ full_simp_tac(srw_ss())[heap_length_def]
  \\ qexists_tac `xs1'` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[AC STAR_ASSOC STAR_COMM]);

val LIST_REL_EQ_MAP = store_thm("LIST_REL_EQ_MAP",
  ``!vs ws f. LIST_REL (λv w. f v = w) vs ws <=> ws = MAP f vs``,
  Induct \\ full_simp_tac(srw_ss())[]);

val full_gc_IMP = prove(
  ``full_gc (xs,heap,limit) = (t,heap2,n,T) ==>
    n <= limit /\ limit = heap_length heap``,
  full_simp_tac(srw_ss())[full_gc_def,LET_THM]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val word_gc_fun_lemma = prove(
  ``good_dimindex (:'a) /\
    heap_in_memory_store heap a sp c s m dm limit /\
    abs_ml_inv c (v::MAP FST stack) refs (hs,heap,be,a,sp) limit /\
    LIST_REL (\v w. word_addr c v = w) hs (s ' Globals::MAP SND stack) /\
    full_gc (hs,heap,limit) = (roots2,heap2,heap_length heap2,T) ==>
    let heap1 = heap2 ++ heap_expand (limit - heap_length heap2) in
      ?stack1 m1 s1 a1 sp1.
        word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
        heap_in_memory_store heap1 (heap_length heap2)
          (limit - heap_length heap2) c s1 m1 dm limit /\
        LIST_REL (λv w. word_addr c v = (w:'a word_loc)) roots2
          (s1 ' Globals::MAP SND (ZIP (MAP FST stack,stack1))) /\
        LENGTH stack1 = LENGTH stack``,
  strip_tac
  \\ rewrite_tac [word_gc_fun_def] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[heap_in_memory_store_def,FLOOKUP_DEF,theWord_def,LET_THM]
  \\ pairarg_tac
  \\ full_simp_tac(srw_ss())[finite_mapTheory.FDOM_FUPDATE_LIST,FUPDATE_LIST,FAPPLY_FUPDATE_THM]
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ `s ' Globals::MAP SND stack = MAP (word_addr c) (v'::xs)` by
    (full_simp_tac(srw_ss())[LIST_REL_EQ_MAP] \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac std_ss [] \\ drule (GEN_ALL word_full_gc_thm)
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ disch_then drule
  \\ disch_then (qspec_then `emp` mp_tac)
  \\ full_simp_tac(srw_ss())[SEP_CLAUSES]
  \\ impl_tac
  THEN1 (imp_res_tac full_gc_IMP \\ fs [])
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac full_gc_IMP_LENGTH
  \\ Cases_on `roots2` \\ full_simp_tac(srw_ss())[]
  \\ `LENGTH xs = LENGTH stack` by metis_tac [LENGTH_MAP]
  \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[listTheory.MAP_ZIP]
  \\ full_simp_tac(srw_ss())[LIST_REL_EQ_MAP]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV) \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac full_gc_IMP \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[heap_length_APPEND,heap_length_heap_expand]
  \\ `heap_length heap2 + (heap_length heap - heap_length heap2) =
      heap_length heap` by decide_tac \\ full_simp_tac(srw_ss())[]
  \\ fs [word_gc_fun_assum_def,isWord_def]) |> GEN_ALL
  |> SIMP_RULE (srw_ss()) [LET_DEF,PULL_EXISTS,GSYM CONJ_ASSOC] |> SPEC_ALL;

val word_gc_fun_correct = prove(
  ``good_dimindex (:'a) /\
    heap_in_memory_store heap a sp c s m dm limit /\
    word_ml_inv (heap:'a ml_heap,be,a,sp) limit c refs ((v,s ' Globals)::stack) ==>
    ?stack1 m1 s1 heap1 a1 sp1.
      word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
      heap_in_memory_store heap1 a1 sp1 c s1 m1 dm limit /\
      word_ml_inv (heap1,be,a1,sp1) limit c refs
        ((v,s1 ' Globals)::ZIP (MAP FST stack,stack1))``,
  full_simp_tac(srw_ss())[word_ml_inv_def] \\ srw_tac[][] \\ imp_res_tac full_gc_thm
  \\ full_simp_tac(srw_ss())[PULL_EXISTS] \\ srw_tac[][]
  \\ mp_tac word_gc_fun_lemma \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Q.LIST_EXISTS_TAC [`heap2 ++ heap_expand (limit - heap_length heap2)`,
       `heap_length heap2`,`limit - heap_length heap2`,`v''`,`xs'`]
  \\ full_simp_tac(srw_ss())[MAP_ZIP]);


(* -------------------------------------------------------
    definition of state relation
   ------------------------------------------------------- *)

val code_rel_def = Define `
  code_rel c s_code t_code <=>
    !n arg_count prog.
      (lookup n s_code = SOME (arg_count:num,prog)) ==>
      (lookup n t_code = SOME (arg_count+1,FST (comp c n 1 prog)))`

val stack_rel_def = Define `
  (stack_rel (Env env) (StackFrame vs NONE) <=>
     EVERY (\(x1,x2). isWord x2 ==> x1 <> 0 /\ EVEN x1) vs /\
     !n. IS_SOME (lookup n env) <=>
         IS_SOME (lookup (adjust_var n) (fromAList vs))) /\
  (stack_rel (Exc env n) (StackFrame vs (SOME (x1,x2,x3))) <=>
     stack_rel (Env env) (StackFrame vs NONE) /\ (x1 = n)) /\
  (stack_rel _ _ <=> F)`

val the_global_def = Define `
  the_global g = the (Number 0) (OPTION_MAP RefPtr g)`;

val contains_loc_def = Define `
  contains_loc (StackFrame vs _) (l1,l2) = (ALOOKUP vs 0 = SOME (Loc l1 l2))`

val state_rel_thm = Define `
  state_rel c l1 l2 (s:'ffi bvpSem$state) (t:('a,'ffi) wordSem$state) v1 locs <=>
    (* I/O, clock and handler are the same, GC is fixed, code is compiled *)
    (t.ffi = s.ffi) /\
    (t.clock = s.clock) /\
    (t.handler = s.handler) /\
    (t.gc_fun = word_gc_fun c) /\
    code_rel c s.code t.code /\
    good_dimindex (:'a) /\
    shift_length c < dimindex (:'a) /\
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
    memory_rel c F s.refs s.space t.store t.memory t.mdomain
      (v1 ++
       join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
       [(the_global s.global,t.store ' Globals)] ++
       flat s.stack t.stack)`

val state_rel_def = state_rel_thm |> REWRITE_RULE [memory_rel_def]

val state_rel_with_clock = Q.store_thm("state_rel_with_clock",
  `state_rel a b c s1 s2 d e ⇒
   state_rel a b c (s1 with clock := k) (s2 with clock := k) d e`,
  srw_tac[][state_rel_def]);

(* -------------------------------------------------------
    init
   ------------------------------------------------------- *)

val flat_NIL = prove(
  ``flat [] xs = []``,
  Cases_on `xs` \\ fs [flat_def]);

val conf_ok_def = Define `
  conf_ok (:'a) c <=>
    shift_length c < dimindex (:α) ∧
    shift (:α) ≤ shift_length c ∧ c.len_size ≠ 0 ∧
    c.len_size + 6 < dimindex (:α)`

val init_store_ok_def = Define `
  init_store_ok c store m (dm:'a word set) <=>
    ?limit curr.
      limit <= max_heap_limit (:'a) c /\
      FLOOKUP store Globals = SOME (Word 0w) /\
      FLOOKUP store CurrHeap = SOME (Word curr) ∧
      FLOOKUP store OtherHeap = FLOOKUP store EndOfHeap ∧
      FLOOKUP store NextFree = SOME (Word curr) ∧
      FLOOKUP store EndOfHeap =
        SOME (Word (curr + bytes_in_word * n2w limit)) ∧
      FLOOKUP store HeapLength =
        SOME (Word (bytes_in_word * n2w limit)) ∧
      (word_list_exists curr (limit + limit)) (fun2set (m,dm)) ∧
      byte_aligned curr`

val state_rel_init = store_thm("state_rel_init",
  ``t.ffi = ffi ∧ t.handler = 0 ∧ t.gc_fun = word_gc_fun c ∧
    code_rel c code t.code ∧
    good_dimindex (:α) ∧
    lookup 0 t.locals = SOME (Loc l1 l2) ∧
    t.stack = [] /\
    conf_ok (:'a) c /\
    init_store_ok c t.store t.memory t.mdomain ==>
    state_rel c l1 l2 (initial_state ffi code t.clock) (t:('a,'ffi) state) [] []``,
  simp_tac std_ss [word_list_exists_ADD,conf_ok_def,init_store_ok_def]
  \\ fs [state_rel_thm,bvpSemTheory.initial_state_def,
    join_env_def,lookup_def,the_global_def,
    libTheory.the_def,flat_NIL,FLOOKUP_DEF] \\ strip_tac \\ fs []
  \\ `FILTER (λ(n,v). n ≠ 0 ∧ EVEN n)
        (toAList (inter t.locals (insert 0 () LN))) = []` by
   (fs [FILTER_EQ_NIL] \\ fs [EVERY_MEM,MEM_toAList,FORALL_PROD]
    \\ fs [lookup_inter_alt]) \\ fs [max_heap_limit_def]
  \\ fs [GSYM (EVAL ``(Smallnum 0)``)]
  \\ match_mp_tac IMP_memory_rel_Number
  \\ fs [] \\ conj_tac
  THEN1 (EVAL_TAC \\ fs [labPropsTheory.good_dimindex_def,dimword_def])
  \\ fs [memory_rel_def]
  \\ rewrite_tac [CONJ_ASSOC]
  \\ once_rewrite_tac [CONJ_COMM]
  \\ `limit * (dimindex (:α) DIV 8) + 1 < dimword (:α)` by
   (fs [labPropsTheory.good_dimindex_def,dimword_def]
    \\ rfs [shift_def] \\ decide_tac)
  \\ asm_exists_tac \\ fs []
  \\ fs [word_ml_inv_def]
  \\ qexists_tac `heap_expand limit`
  \\ qexists_tac `0`
  \\ qexists_tac `limit`
  \\ reverse conj_tac THEN1
   (fs[abs_ml_inv_def,roots_ok_def,heap_ok_def,heap_length_heap_expand,
       unused_space_inv_def,bc_stack_ref_inv_def,FDOM_EQ_EMPTY]
    \\ fs [heap_expand_def,heap_lookup_def]
    \\ rw [] \\ fs [isForwardPointer_def,bc_ref_inv_def,reachable_refs_def])
  \\ fs [heap_in_memory_store_def,heap_length_heap_expand,word_heap_heap_expand]
  \\ fs [FLOOKUP_DEF]
  \\ fs [byte_aligned_def,bytes_in_word_def,labPropsTheory.good_dimindex_def,
         word_mul_n2w]
  \\ simp_tac bool_ss [GSYM (EVAL ``2n**2``),GSYM (EVAL ``2n**3``)]
  \\ once_rewrite_tac [MULT_COMM]
  \\ simp_tac bool_ss [aligned_add_pow] \\ rfs []);

(* -------------------------------------------------------
    compiler proof
   ------------------------------------------------------- *)

val adjust_var_NOT_0 = store_thm("adjust_var_NOT_0[simp]",
  ``adjust_var n <> 0``,
  full_simp_tac(srw_ss())[adjust_var_def]);

val state_rel_get_var_IMP = prove(
  ``state_rel c l1 l2 s t v1 locs ==>
    (get_var n s.locals = SOME x) ==>
    ?w. get_var (adjust_var n) t = SOME w``,
  full_simp_tac(srw_ss())[bvpSemTheory.get_var_def,wordSemTheory.get_var_def]
  \\ full_simp_tac(srw_ss())[state_rel_def] \\ rpt strip_tac
  \\ `IS_SOME (lookup n s.locals)` by full_simp_tac(srw_ss())[] \\ res_tac
  \\ Cases_on `lookup (adjust_var n) t.locals` \\ full_simp_tac(srw_ss())[]);

val state_rel_get_vars_IMP = prove(
  ``!n xs.
      state_rel c l1 l2 s t [] locs ==>
      (get_vars n s.locals = SOME xs) ==>
      ?ws. get_vars (MAP adjust_var n) t = SOME ws /\ (LENGTH xs = LENGTH ws)``,
  Induct \\ full_simp_tac(srw_ss())[bvpSemTheory.get_vars_def,wordSemTheory.get_vars_def]
  \\ rpt strip_tac
  \\ Cases_on `get_var h s.locals` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars n s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac state_rel_get_var_IMP \\ full_simp_tac(srw_ss())[]);

val state_rel_0_get_vars_IMP = prove(
  ``state_rel c l1 l2 s t [] locs ==>
    (get_vars n s.locals = SOME xs) ==>
    ?ws. get_vars (0::MAP adjust_var n) t = SOME ((Loc l1 l2)::ws) /\
         (LENGTH xs = LENGTH ws)``,
  rpt strip_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.get_var_def]);

val get_var_T_OR_F = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) state) [] locs /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    18 MOD dimword (:'a) <> 2 MOD dimword (:'a) /\
    ((x = Boolv T) ==> (w = Word 2w)) /\
    ((x = Boolv F) ==> (w = Word 18w))``,
  full_simp_tac(srw_ss())[state_rel_def,get_var_def,wordSemTheory.get_var_def]
  \\ strip_tac \\ strip_tac THEN1 (full_simp_tac(srw_ss())[good_dimindex_def] \\ full_simp_tac(srw_ss())[dimword_def])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac (word_ml_inv_lookup |> Q.INST [`ys`|->`[]`]
                    |> SIMP_RULE std_ss [APPEND])
  \\ pop_assum mp_tac
  \\ simp [word_ml_inv_def,toAList_def,foldi_def,word_ml_inv_def,PULL_EXISTS]
  \\ strip_tac \\ strip_tac
  \\ full_simp_tac(srw_ss())[abs_ml_inv_def,bc_stack_ref_inv_def]
  \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[Boolv_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[v_inv_def] \\ full_simp_tac(srw_ss())[word_addr_def]
  \\ EVAL_TAC \\ full_simp_tac(srw_ss())[good_dimindex_def,dimword_def]);

val mk_loc_def = Define `
  mk_loc (SOME (t1,d1,d2)) = Loc d1 d2`;

val cut_env_IMP_cut_env = prove(
  ``state_rel c l1 l2 s t [] locs /\
    bvpSem$cut_env r s.locals = SOME x ==>
    ?y. wordSem$cut_env (adjust_set r) t.locals = SOME y``,
  full_simp_tac(srw_ss())[bvpSemTheory.cut_env_def,wordSemTheory.cut_env_def]
  \\ full_simp_tac(srw_ss())[adjust_set_def,domain_fromAList,SUBSET_DEF,MEM_MAP,
         PULL_EXISTS,sptreeTheory.domain_lookup,lookup_fromAList] \\ srw_tac[][]
  \\ Cases_on `x' = 0` \\ full_simp_tac(srw_ss())[] THEN1 full_simp_tac(srw_ss())[state_rel_def]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ full_simp_tac(srw_ss())[unit_some_eq_IS_SOME,IS_SOME_ALOOKUP_EQ,MEM_MAP]
  \\ Cases_on `y'` \\ Cases_on `y''`
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[adjust_var_11] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_rel_def] \\ res_tac
  \\ `IS_SOME (lookup q s.locals)` by full_simp_tac(srw_ss())[] \\ res_tac
  \\ Cases_on `lookup (adjust_var q) t.locals` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[MEM_toAList,unit_some_eq_IS_SOME] \\ res_tac \\ full_simp_tac(srw_ss())[]);

val jump_exc_call_env = prove(
  ``wordSem$jump_exc (call_env x s) = jump_exc s``,
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.call_env_def]);

val jump_exc_dec_clock = prove(
  ``mk_loc (wordSem$jump_exc (dec_clock s)) = mk_loc (jump_exc s)``,
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def]
  \\ srw_tac[][] \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[mk_loc_def]);

val LASTN_ADD1 = LASTN_LENGTH_ID
  |> Q.SPEC `x::xs` |> SIMP_RULE (srw_ss()) [ADD1]

val jump_exc_push_env_NONE = prove(
  ``mk_loc (jump_exc (push_env y NONE s)) =
    mk_loc (jump_exc (s:('a,'b) wordSem$state))``,
  full_simp_tac(srw_ss())[wordSemTheory.push_env_def,wordSemTheory.jump_exc_def]
  \\ Cases_on `env_to_list y s.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Cases_on `s.handler = LENGTH s.stack` \\ full_simp_tac(srw_ss())[LASTN_ADD1]
  \\ Cases_on `~(s.handler < LENGTH s.stack)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1 (`F` by DECIDE_TAC)
  \\ `LASTN (s.handler + 1) (StackFrame q NONE::s.stack) =
      LASTN (s.handler + 1) s.stack` by
    (match_mp_tac LASTN_TL \\ decide_tac)
  \\ every_case_tac \\ srw_tac[][mk_loc_def]
  \\ `F` by decide_tac);

val state_rel_pop_env_IMP = prove(
  ``state_rel c q l s1 t1 [] locs /\
    pop_env s1 = SOME s2 ==>
    ?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9)::ll /\
      state_rel c l8 l9 s2 t2 [] ll``,
  full_simp_tac(srw_ss())[pop_env_def]
  \\ Cases_on `s1.stack` \\ full_simp_tac(srw_ss())[] \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ TRY (Cases_on `y`) \\ full_simp_tac(srw_ss())[stack_rel_def]
  \\ full_simp_tac(srw_ss())[stack_rel_def,wordSemTheory.pop_env_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ Cases_on `y` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `o'` \\ full_simp_tac(srw_ss())[stack_rel_def,wordSemTheory.pop_env_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ Cases_on `y` \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ TRY (Cases_on `r'`) \\ full_simp_tac(srw_ss())[stack_rel_def]
  \\ full_simp_tac(srw_ss())[lookup_fromAList,contains_loc_def]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[flat_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

val state_rel_pop_env_set_var_IMP = prove(
  ``state_rel c q l s1 t1 [(a,w)] locs /\
    pop_env s1 = SOME s2 ==>
    ?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9)::ll /\
      state_rel c l8 l9 (set_var q a s2) (set_var (adjust_var q) w t2) [] ll``,
  full_simp_tac(srw_ss())[pop_env_def]
  \\ Cases_on `s1.stack` \\ full_simp_tac(srw_ss())[] \\ Cases_on `h` \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[state_rel_def,set_var_def,wordSemTheory.set_var_def]
  \\ rev_full_simp_tac(srw_ss())[] \\ Cases_on `y` \\ full_simp_tac(srw_ss())[stack_rel_def]
  \\ Cases_on `o'` \\ full_simp_tac(srw_ss())[stack_rel_def,wordSemTheory.pop_env_def]
  \\ full_simp_tac(srw_ss())[stack_rel_def,wordSemTheory.pop_env_def]
  \\ TRY (Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[lookup_insert,adjust_var_11]
  \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ Cases_on `y`
  \\ full_simp_tac(srw_ss())[contains_loc_def,lookup_fromAList] \\ srw_tac[][]
  \\ TRY (Cases_on `r` \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[stack_rel_def,wordSemTheory.pop_env_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[lookup_fromAList] \\ rev_full_simp_tac(srw_ss())[]
  \\ first_assum (match_exists_tac o concl) \\ full_simp_tac(srw_ss())[] (* asm_exists_tac *)
  \\ full_simp_tac(srw_ss())[flat_def]
  \\ `word_ml_inv (heap,F,a',sp) limit c s1.refs
       ((a,w)::(join_env s l ++
         [(the_global s1.global,t1.store ' Globals)] ++ flat t ys))` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac (word_ml_inv_insert
       |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

val state_rel_jump_exc = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w /\
    jump_exc s = SOME s1 ==>
    ?t1 d1 d2 l5 l6 ll.
      jump_exc t = SOME (t1,d1,d2) /\
      LASTN (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
      !i. state_rel c l5 l6 (set_var i x s1) (set_var (adjust_var i) w t1) [] ll``,
  full_simp_tac(srw_ss())[jump_exc_def] \\ rpt CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[wordSemTheory.set_var_def,set_var_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_var_IMP
  \\ imp_res_tac LASTN_LIST_REL_LEMMA
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[stack_rel_def]
  \\ Cases_on `y'` \\ full_simp_tac(srw_ss())[contains_loc_def]
  \\ `s.handler + 1 <= LENGTH s.stack` by decide_tac
  \\ imp_res_tac LASTN_CONS_IMP_LENGTH \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[lookup_insert,adjust_var_11]
  \\ full_simp_tac(srw_ss())[contains_loc_def,lookup_fromAList] \\ srw_tac[][]
  \\ first_assum (match_exists_tac o concl) \\ full_simp_tac(srw_ss())[] (* asm_exists_tac *)
  \\ `s.handler + 1 <= LENGTH s.stack /\
      s.handler + 1 <= LENGTH t.stack` by decide_tac
  \\ imp_res_tac LASTN_IMP_APPEND \\ full_simp_tac(srw_ss())[ADD1]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[flat_APPEND,flat_def]
  \\ `word_ml_inv (heap,F,a,sp) limit c s.refs
       ((x,w)::(join_env s' l ++
         [(the_global s.global,t.store ' Globals)] ++ flat t' ys))` by
   (first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC,APPEND]
  \\ match_mp_tac (word_ml_inv_insert
       |> SIMP_RULE std_ss [APPEND,GSYM APPEND_ASSOC])
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

val get_vars_IMP_LENGTH = prove(
  ``!x t s. bvpSem$get_vars x s = SOME t ==> LENGTH x = LENGTH t``,
  Induct \\ full_simp_tac(srw_ss())[bvpSemTheory.get_vars_def] \\ srw_tac[][]
  \\ every_case_tac \\ res_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val lookup_adjust_var_fromList2 = prove(
  ``lookup (adjust_var n) (fromList2 (w::ws)) = lookup n (fromList ws)``,
  full_simp_tac(srw_ss())[lookup_fromList2,EVEN_adjust_var,lookup_fromList]
  \\ full_simp_tac(srw_ss())[adjust_var_def]
  \\ once_rewrite_tac [MULT_COMM]
  \\ full_simp_tac(srw_ss())[GSYM MULT_CLAUSES,MULT_DIV]);

val state_rel_call_env = prove(
  ``get_vars args s.locals = SOME q /\
    get_vars (MAP adjust_var args) (t:('a,'ffi) wordSem$state) = SOME ws /\
    state_rel c l5 l6 s t [] locs ==>
    state_rel c l1 l2 (call_env q (dec_clock s))
      (call_env (Loc l1 l2::ws) (dec_clock t)) [] locs``,
  full_simp_tac(srw_ss())[state_rel_def,call_env_def,wordSemTheory.call_env_def,
      dec_clock_def,wordSemTheory.dec_clock_def,lookup_adjust_var_fromList2]
  \\ srw_tac[][lookup_fromList2,lookup_fromList] \\ srw_tac[][]
  \\ imp_res_tac get_vars_IMP_LENGTH
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[]
  \\ first_assum (match_exists_tac o concl) \\ full_simp_tac(srw_ss())[] (* asm_exists_tac *)
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `x` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER]
  \\ Cases_on `y` \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_inter_alt] \\ srw_tac[][MEM_ZIP]
  \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList]
  \\ rpt disj1_tac
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ full_simp_tac(srw_ss())[DIV_LT_X]
  \\ `k < 2 + LENGTH q * 2 /\ 0 < LENGTH q * 2` by
   (rev_full_simp_tac(srw_ss())[] \\ Cases_on `q` \\ full_simp_tac(srw_ss())[]
    THEN1 (Cases_on `k` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
  \\ full_simp_tac(srw_ss())[] \\ qexists_tac `(k - 2) DIV 2` \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[DIV_LT_X] \\ srw_tac[][]
  \\ Cases_on `k` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `n` \\ full_simp_tac(srw_ss())[DECIDE ``SUC (SUC n) = n + 2``]
  \\ simp [MATCH_MP ADD_DIV_RWT (DECIDE ``0<2:num``)]
  \\ full_simp_tac(srw_ss())[GSYM ADD1,EL]);

val bvp_get_vars_SNOC_IMP = prove(
  ``!x2 x. bvpSem$get_vars (SNOC x1 x2) s = SOME x ==>
           ?y1 y2. x = SNOC y1 y2 /\
                   bvpSem$get_var x1 s = SOME y1 /\
                   bvpSem$get_vars x2 s = SOME y2``,
  Induct \\ full_simp_tac(srw_ss())[bvpSemTheory.get_vars_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]) |> SPEC_ALL;

val word_get_vars_SNOC_IMP = prove(
  ``!x2 x. wordSem$get_vars (SNOC x1 x2) s = SOME x ==>
           ?y1 y2. x = SNOC y1 y2 /\
              wordSem$get_var x1 s = SOME y1 /\
              wordSem$get_vars x2 s = SOME y2``,
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]) |> SPEC_ALL;

val word_ml_inv_CodePtr = prove(
  ``word_ml_inv (heap,be,a,sp) limit c s.refs ((CodePtr n,v)::xs) ==>
    (v = Loc n 0)``,
  full_simp_tac(srw_ss())[word_ml_inv_def,PULL_EXISTS] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[abs_ml_inv_def,bc_stack_ref_inv_def,v_inv_def]
  \\ srw_tac[][word_addr_def]);

val state_rel_CodePtr = prove(
  ``state_rel c l1 l2 s t [] locs /\
    get_vars args s.locals = SOME x /\
    get_vars (MAP adjust_var args) t = SOME y /\
    LAST x = CodePtr n /\ x <> [] ==>
    y <> [] /\ LAST y = Loc n 0``,
  rpt strip_tac
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THEN1 (srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES]
  \\ full_simp_tac bool_ss [MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [LAST_SNOC] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_var_IMP \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_ml_inv_CodePtr);

val find_code_thm = prove(
  ``!(s:'ffi bvpSem$state) (t:('a,'ffi)wordSem$state).
      state_rel c l1 l2 s t [] locs /\
      get_vars args s.locals = SOME x /\
      get_vars (0::MAP adjust_var args) t = SOME (Loc l1 l2::ws) /\
      find_code dest x s.code = SOME (q,r) ==>
      ?args1 n1 n2.
        find_code dest (Loc l1 l2::ws) t.code = SOME (args1,FST (comp c n1 n2 r)) /\
        state_rel c l1 l2 (call_env q (dec_clock s))
          (call_env args1 (dec_clock t)) [] locs``,
  Cases_on `dest` \\ srw_tac[][] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[wordSemTheory.find_code_def] \\ srw_tac[][]
  \\ `code_rel c s.code t.code` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma
  \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ Cases_on `get_var 0 t` \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `get_vars (MAP adjust_var args) t` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ TRY (imp_res_tac state_rel_CodePtr \\ full_simp_tac(srw_ss())[]
          \\ qpat_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THENL [Q.LIST_EXISTS_TAC [`n`,`1`],Q.LIST_EXISTS_TAC [`x'`,`1`]] \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac state_rel_call_env \\ full_simp_tac(srw_ss())[]
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ `get_vars (0::MAP adjust_var x2) t = SOME (Loc l1 l2::y2')` by
        full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ imp_res_tac state_rel_call_env \\ full_simp_tac(srw_ss())[]) |> SPEC_ALL;

val env_to_list_lookup_equiv = prove(
  ``env_to_list y f = (q,r) ==>
    (!n. ALOOKUP q n = lookup n y) /\
    (!x1 x2. MEM (x1,x2) q ==> lookup x1 y = SOME x2)``,
  full_simp_tac(srw_ss())[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ `ALL_DISTINCT (MAP FST (toAList y))` by full_simp_tac(srw_ss())[ALL_DISTINCT_MAP_FST_toAList]
  \\ imp_res_tac (MATCH_MP PERM_ALL_DISTINCT_MAP
        (QSORT_PERM |> Q.ISPEC `key_val_compare` |> SPEC_ALL))
  \\ `ALL_DISTINCT (QSORT key_val_compare (toAList y))`
        by imp_res_tac ALL_DISTINCT_MAP
  \\ pop_assum (assume_tac o Q.SPEC `f (0:num)` o MATCH_MP PERM_list_rearrange)
  \\ imp_res_tac PERM_ALL_DISTINCT_MAP
  \\ rpt (qpat_assum `!x. pp ==> qq` (K all_tac))
  \\ rpt (qpat_assum `!x y. pp ==> qq` (K all_tac)) \\ rev_full_simp_tac(srw_ss())[]
  \\ rpt (pop_assum (mp_tac o Q.GEN `x` o SPEC_ALL))
  \\ rpt (pop_assum (mp_tac o SPEC ``f:num->num->num``))
  \\ Q.ABBREV_TAC `xs =
       (list_rearrange (f 0) (QSORT key_val_compare (toAList y)))`
  \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[MEM_toAList]
  \\ Cases_on `?i. MEM (n,i) xs` \\ full_simp_tac(srw_ss())[] THEN1
     (imp_res_tac ALL_DISTINCT_MEM_IMP_ALOOKUP_SOME \\ full_simp_tac(srw_ss())[]
      \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[MEM_toAList])
  \\ `~MEM n (MAP FST xs)` by rev_full_simp_tac(srw_ss())[MEM_MAP,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[GSYM ALOOKUP_NONE]
  \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[MEM_toAList]
  \\ Cases_on `lookup n y` \\ full_simp_tac(srw_ss())[]);

val cut_env_adjust_set_lookup_0 = prove(
  ``wordSem$cut_env (adjust_set r) x = SOME y ==> lookup 0 y = lookup 0 x``,
  full_simp_tac(srw_ss())[wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup,adjust_set_def,
      lookup_fromAList] \\ srw_tac[][lookup_inter]
  \\ pop_assum (qspec_then `0` mp_tac) \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_fromAList,lookup_inter]);

val cut_env_IMP_MEM = prove(
  ``bvpSem$cut_env s r = SOME x ==>
    (IS_SOME (lookup n x) <=> IS_SOME (lookup n s))``,
  full_simp_tac(srw_ss())[cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ res_tac \\ full_simp_tac(srw_ss())[]);

val cut_env_IMP_lookup = prove(
  ``wordSem$cut_env s r = SOME x /\ lookup n x = SOME q ==>
    lookup n r = SOME q``,
  full_simp_tac(srw_ss())[wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val cut_env_IMP_lookup_EQ = prove(
  ``bvpSem$cut_env r y = SOME x /\ n IN domain r ==>
    lookup n x = lookup n y``,
  full_simp_tac(srw_ss())[bvpSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val cut_env_res_IS_SOME_IMP = prove(
  ``wordSem$cut_env r x = SOME y /\ IS_SOME (lookup k y) ==>
    IS_SOME (lookup k x) /\ IS_SOME (lookup k r)``,
  full_simp_tac(srw_ss())[wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val adjust_var_cut_env_IMP_MEM = prove(
  ``wordSem$cut_env (adjust_set s) r = SOME x ==>
    domain x SUBSET EVEN /\
    (IS_SOME (lookup (adjust_var n) x) <=> IS_SOME (lookup n s))``,
  full_simp_tac(srw_ss())[wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter_alt] THEN1
   (full_simp_tac(srw_ss())[domain_lookup,unit_some_eq_IS_SOME,adjust_set_def]
    \\ full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,lookup_fromAList]
    \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[IN_DEF]
    \\ full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP,lookup_fromAList]
    \\ pairarg_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[EVEN_adjust_var])
  \\ full_simp_tac(srw_ss())[domain_lookup,lookup_adjust_var_adjust_set_SOME_UNIT] \\ srw_tac[][]
  \\ metis_tac [lookup_adjust_var_adjust_set_SOME_UNIT,IS_SOME_DEF]);

val state_rel_call_env_push_env = prove(
  ``!opt:(num # 'a wordLang$prog # num # num) option.
      state_rel c l1 l2 s (t:('a,'ffi)wordSem$state) [] locs /\
      get_vars args s.locals = SOME xs /\
      get_vars (MAP adjust_var args) t = SOME ws /\
      bvpSem$cut_env r s.locals = SOME x /\
      wordSem$cut_env (adjust_set r) t.locals = SOME y ==>
      state_rel c q l (call_env xs (push_env x (IS_SOME opt) (dec_clock s)))
       (call_env (Loc q l::ws) (push_env y opt (dec_clock t))) []
       ((l1,l2)::locs)``,
  Cases \\ TRY (PairCases_on `x'`) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[state_rel_def,call_env_def,push_env_def,dec_clock_def,
         wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF,stack_rel_def]
  \\ full_simp_tac(srw_ss())[lookup_adjust_var_fromList2,contains_loc_def] \\ strip_tac
  \\ full_simp_tac(srw_ss())[lookup_fromList,lookup_fromAList]
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[IS_SOME_IF]
  \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList]
  \\ imp_res_tac env_to_list_lookup_equiv \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_adjust_set_lookup_0 \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_IMP_MEM
  \\ imp_res_tac adjust_var_cut_env_IMP_MEM \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ rpt strip_tac \\ TRY
   (imp_res_tac adjust_var_cut_env_IMP_MEM
    \\ full_simp_tac(srw_ss())[domain_lookup,SUBSET_DEF,PULL_EXISTS]
    \\ full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD] \\ ntac 3 strip_tac
    \\ res_tac \\ res_tac \\ full_simp_tac(srw_ss())[IN_DEF] \\ srw_tac[][] \\ strip_tac
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[isWord_def] \\ NO_TAC)
  \\ first_assum (match_exists_tac o concl) \\ full_simp_tac(srw_ss())[] (* asm_exists_tac *)
  \\ full_simp_tac(srw_ss())[flat_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ TRY (rpt disj1_tac
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
    \\ full_simp_tac(srw_ss())[MEM_toAList] \\ srw_tac[][MEM_ZIP]
    \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList,lookup_inter_alt]
    \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
    \\ full_simp_tac(srw_ss())[DIV_LT_X]
    \\ `k < 2 + LENGTH xs * 2 /\ 0 < LENGTH xs * 2` by
     (rev_full_simp_tac(srw_ss())[] \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[]
      THEN1 (Cases_on `k` \\ full_simp_tac(srw_ss())[] \\ Cases_on `n` \\ full_simp_tac(srw_ss())[] \\ decide_tac)
      \\ full_simp_tac(srw_ss())[MULT_CLAUSES] \\ decide_tac)
    \\ full_simp_tac(srw_ss())[] \\ qexists_tac `(k - 2) DIV 2` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[DIV_LT_X]
    \\ Cases_on `k` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `n` \\ full_simp_tac(srw_ss())[DECIDE ``SUC (SUC n) = n + 2``]
    \\ full_simp_tac(srw_ss())[MATCH_MP ADD_DIV_RWT (DECIDE ``0<2:num``)]
    \\ full_simp_tac(srw_ss())[GSYM ADD1,EL] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[] \\ disj1_tac \\ disj2_tac
  \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ full_simp_tac(srw_ss())[MEM_toAList] \\ srw_tac[][MEM_ZIP]
  \\ full_simp_tac(srw_ss())[lookup_fromList2,lookup_fromList,lookup_inter_alt]
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ qexists_tac `k` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][]
  \\ imp_res_tac cut_env_IMP_lookup \\ full_simp_tac(srw_ss())[]
  \\ TRY (AP_TERM_TAC \\ match_mp_tac cut_env_IMP_lookup_EQ) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[domain_lookup] \\ imp_res_tac MEM_IMP_IS_SOME_ALOOKUP \\ rev_full_simp_tac(srw_ss())[]
  \\ imp_res_tac cut_env_res_IS_SOME_IMP
  \\ full_simp_tac(srw_ss())[IS_SOME_EXISTS]
  \\ full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList] \\ rev_full_simp_tac(srw_ss())[]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ full_simp_tac(srw_ss())[unit_some_eq_IS_SOME,IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD]
  \\ srw_tac[][adjust_var_11,adjust_var_DIV_2]
  \\ imp_res_tac MEM_toAList \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[bvpSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ res_tac \\ full_simp_tac(srw_ss())[MEM_toAList]);

val find_code_thm_ret = prove(
  ``!(s:'ffi bvpSem$state) (t:('a,'ffi)wordSem$state).
      state_rel c l1 l2 s t [] locs /\
      get_vars args s.locals = SOME xs /\
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
  reverse (Cases_on `dest`) \\ srw_tac[][] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[wordSemTheory.find_code_def] \\ srw_tac[][]
  \\ `code_rel c s.code t.code` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[]
  \\ TRY (imp_res_tac state_rel_CodePtr \\ full_simp_tac(srw_ss())[]
          \\ qpat_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THEN1 (Q.LIST_EXISTS_TAC [`x'`,`1`] \\ full_simp_tac(srw_ss())[]
         \\ qspec_then `NONE` mp_tac state_rel_call_env_push_env \\ full_simp_tac(srw_ss())[])
  \\ Q.LIST_EXISTS_TAC [`n`,`1`] \\ full_simp_tac(srw_ss())[]
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `NONE`
                   |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ full_simp_tac(srw_ss())[] \\ metis_tac []) |> SPEC_ALL;

val find_code_thm_handler = prove(
  ``!(s:'ffi bvpSem$state) (t:('a,'ffi)wordSem$state).
      state_rel c l1 l2 s t [] locs /\
      get_vars args s.locals = SOME xs /\
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
  reverse (Cases_on `dest`) \\ srw_tac[][] \\ full_simp_tac(srw_ss())[find_code_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[wordSemTheory.find_code_def] \\ srw_tac[][]
  \\ `code_rel c s.code t.code` by full_simp_tac(srw_ss())[state_rel_def]
  \\ full_simp_tac(srw_ss())[code_rel_def] \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ imp_res_tac wordPropsTheory.get_vars_length_lemma \\ full_simp_tac(srw_ss())[]
  \\ TRY (imp_res_tac state_rel_CodePtr \\ full_simp_tac(srw_ss())[]
          \\ qpat_assum `ws <> []` (assume_tac)
          \\ imp_res_tac NOT_NIL_IMP_LAST \\ full_simp_tac(srw_ss())[])
  \\ imp_res_tac get_vars_IMP_LENGTH \\ full_simp_tac(srw_ss())[]
  THEN1 (Q.LIST_EXISTS_TAC [`x'`,`1`] \\ full_simp_tac(srw_ss())[]
         \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `SOME xx`
                   |> SIMP_RULE std_ss [] |> GEN_ALL) \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
  \\ Q.LIST_EXISTS_TAC [`n`,`1`] \\ full_simp_tac(srw_ss())[]
  \\ `args <> []` by (Cases_on `args` \\ full_simp_tac(srw_ss())[] \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[])
  \\ `?x1 x2. args = SNOC x1 x2` by metis_tac [SNOC_CASES] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[MAP_SNOC]
  \\ imp_res_tac bvp_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ imp_res_tac word_get_vars_SNOC_IMP \\ srw_tac[][]
  \\ full_simp_tac bool_ss [GSYM SNOC |> CONJUNCT2]
  \\ full_simp_tac bool_ss [FRONT_SNOC]
  \\ match_mp_tac (state_rel_call_env_push_env |> Q.SPEC `SOME xx`
                   |> SIMP_RULE std_ss [] |> GEN_ALL)
  \\ full_simp_tac(srw_ss())[] \\ metis_tac []) |> SPEC_ALL;

val bvl_find_code = store_thm("bvl_find_code",
  ``bvlSem$find_code dest xs code = SOME(ys,prog) ⇒
  ¬bad_dest_args dest xs``,
  Cases_on`dest`>>
  full_simp_tac(srw_ss())[bvlSemTheory.find_code_def,wordSemTheory.bad_dest_args_def])

val s_key_eq_LENGTH = prove(
  ``!xs ys. s_key_eq xs ys ==> (LENGTH xs = LENGTH ys)``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[s_key_eq_def]);

val s_key_eq_LASTN = prove(
  ``!xs ys n. s_key_eq xs ys ==> s_key_eq (LASTN n xs) (LASTN n ys)``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[s_key_eq_def,LASTN_ALT]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[s_key_eq_def,LASTN_ALT] \\ res_tac
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[] \\ `F` by decide_tac);

val evaluate_mk_loc_EQ = prove(
  ``evaluate (q,t) = (NONE,t1:('a,'b) state) ==>
    mk_loc (jump_exc t1) = ((mk_loc (jump_exc t)):'a word_loc)``,
  qspecl_then [`q`,`t`] mp_tac wordPropsTheory.evaluate_stack_swap \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def]
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ imp_res_tac s_key_eq_LASTN
  \\ pop_assum (qspec_then `t.handler + 1` mp_tac)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def,mk_loc_def])

val mk_loc_eq_push_env_exc_Exception = prove(
  ``evaluate
      (c:'a wordLang$prog, call_env args1
            (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l))
               (dec_clock t))) = (SOME (Exception xx w),(t1:('a,'b) state)) ==>
    mk_loc (jump_exc t1) = mk_loc (jump_exc t) :'a word_loc``,
  qspecl_then [`c`,`call_env args1
    (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l)) (dec_clock t))`]
       mp_tac wordPropsTheory.evaluate_stack_swap \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF,LASTN_ADD1]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def]
  \\ first_assum (qspec_then `t1.stack` mp_tac)
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac s_key_eq_LASTN
  \\ pop_assum (qspec_then `t.handler+1` mp_tac) \\ srw_tac[][]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def,mk_loc_def]);

val evaluate_IMP_domain_EQ = prove(
  ``evaluate (c,call_env (args1:'a word_loc list) (push_env y (opt:(num # ('a wordLang$prog) # num # num) option) (dec_clock t))) =
      (SOME (Result ll w),t1) /\ pop_env t1 = SOME t2 ==>
    domain t2.locals = domain y``,
  qspecl_then [`c`,`call_env args1 (push_env y opt (dec_clock t))`] mp_tac
      wordPropsTheory.evaluate_stack_swap \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def]
  \\ Cases_on `opt` \\ full_simp_tac(srw_ss())[] \\ TRY (PairCases_on `x`)
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y (dec_clock t).permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[s_frame_key_eq_def,domain_fromAList] \\ srw_tac[][]
  \\ qpat_assum `xxx = MAP FST l` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,EXISTS_PROD,mem_list_rearrange,QSORT_MEM,
         domain_lookup,MEM_toAList]);

val evaluate_IMP_domain_EQ_Exc = prove(
  ``evaluate (c,call_env args1 (push_env y
      (SOME (x0,prog1:'a wordLang$prog,x1,l))
      (dec_clock (t:('a,'b) state)))) = (SOME (Exception ll w),t1) ==>
    domain t1.locals = domain y``,
  qspecl_then [`c`,`call_env args1
     (push_env y (SOME (x0,prog1:'a wordLang$prog,x1,l)) (dec_clock t))`]
     mp_tac wordPropsTheory.evaluate_stack_swap \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def,wordSemTheory.push_env_def,
         wordSemTheory.dec_clock_def]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF,LASTN_ADD1] \\ srw_tac[][]
  \\ first_x_assum (qspec_then `t1.stack` mp_tac) \\ srw_tac[][]
  \\ imp_res_tac s_key_eq_LASTN \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (qspec_then `t.handler+1` mp_tac) \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.env_to_list_def,LET_DEF] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[s_frame_key_eq_def,domain_fromAList] \\ srw_tac[][]
  \\ qpat_assum `xxx = MAP FST lss` (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[EXTENSION,MEM_MAP,EXISTS_PROD,mem_list_rearrange,QSORT_MEM,
         domain_lookup,MEM_toAList]);

val mk_loc_jump_exc = prove(
  ``mk_loc
       (jump_exc
          (call_env args1
             (push_env y (SOME (adjust_var x0,prog1,x0,l))
                (dec_clock t)))) = Loc x0 l``,
  full_simp_tac(srw_ss())[wordSemTheory.push_env_def,wordSemTheory.call_env_def,
      wordSemTheory.jump_exc_def]
  \\ Cases_on `env_to_list y (dec_clock t).permute`
  \\ full_simp_tac(srw_ss())[LET_DEF,LASTN_ADD1,mk_loc_def]);

val inc_clock_def = Define `
  inc_clock n (t:('a,'ffi) wordSem$state) = t with clock := t.clock + n`;

val inc_clock_0 = store_thm("inc_clock_0[simp]",
  ``!t. inc_clock 0 t = t``,
  full_simp_tac(srw_ss())[inc_clock_def,wordSemTheory.state_component_equality]);

val inc_clock_inc_clock = store_thm("inc_clock_inc_clock[simp]",
  ``!t. inc_clock n (inc_clock m t) = inc_clock (n+m) t``,
  full_simp_tac(srw_ss())[inc_clock_def,wordSemTheory.state_component_equality,AC ADD_ASSOC ADD_COMM]);

val mk_loc_jmup_exc_inc_clock = store_thm("mk_loc_jmup_exc_inc_clock[simp]",
  ``mk_loc (jump_exc (inc_clock ck t)) = mk_loc (jump_exc t)``,
  full_simp_tac(srw_ss())[mk_loc_def,wordSemTheory.jump_exc_def,inc_clock_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[mk_loc_def]);

val jump_exc_inc_clock_EQ_NONE = prove(
  ``jump_exc (inc_clock n s) = NONE <=> jump_exc s = NONE``,
  full_simp_tac(srw_ss())[mk_loc_def,wordSemTheory.jump_exc_def,inc_clock_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[mk_loc_def]);

val state_rel_lookup_globals = Q.store_thm("state_rel_lookup_globals",
  `state_rel c l1 l2 s t v1 locs ∧ s.global = SOME g (* ∧
   FLOOKUP s.refs g = SOME (ValueArray gs) *)
   ⇒
   ∃x u.
   FLOOKUP t.store Globals = SOME (Word (get_addr c x u))`,
  rw[state_rel_def]
  \\ fs[the_global_def,libTheory.the_def]
  \\ qmatch_assum_abbrev_tac`word_ml_inv heapp limit c refs _`
  \\ qmatch_asmsub_abbrev_tac`[gg]`
  \\ `∃rest. word_ml_inv heapp limit c refs (gg::rest)`
  by (
    qmatch_asmsub_abbrev_tac`a1 ++ [gg] ++ a2`
    \\ qexists_tac`a1++a2`
    \\ simp[Abbr`heapp`]
    \\ match_mp_tac (GEN_ALL (MP_CANON word_ml_inv_rearrange))
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[] \\ metis_tac[] )
  \\ fs[word_ml_inv_def,Abbr`heapp`]
  \\ fs[abs_ml_inv_def]
  \\ fs[bc_stack_ref_inv_def]
  \\ fs[Abbr`gg`,v_inv_def]
  \\ simp[FLOOKUP_DEF]
  \\ first_assum(CHANGED_TAC o SUBST1_TAC o SYM)
  \\ rveq
  \\ simp_tac(srw_ss())[word_addr_def]
  \\ metis_tac[]);

val state_rel_cut_env = store_thm("state_rel_cut_env",
  ``state_rel c l1 l2 s t [] locs /\
    bvpSem$cut_env names s.locals = SOME x ==>
    state_rel c l1 l2 (s with locals := x) t [] locs``,
  full_simp_tac(srw_ss())[state_rel_def,bvpSemTheory.cut_env_def] \\ srw_tac[][]
  THEN1 (full_simp_tac(srw_ss())[lookup_inter] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ rpt disj1_tac
  \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[join_env_def,MEM_MAP]
  \\ Cases_on `y` \\ full_simp_tac(srw_ss())[EXISTS_PROD,MEM_FILTER]
  \\ qexists_tac `q` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1
   (AP_TERM_TAC
    \\ full_simp_tac(srw_ss())[FUN_EQ_THM,lookup_inter_alt,MEM_toAList,domain_lookup]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,IN_DEF,domain_lookup] \\ srw_tac[][]
    \\ imp_res_tac IMP_adjust_var
    \\ `lookup (adjust_var ((q - 2) DIV 2))
           (adjust_set (inter s.locals names)) = NONE` by
     (simp [lookup_adjust_var_adjust_set_NONE,lookup_inter_alt]
      \\ full_simp_tac(srw_ss())[domain_lookup]) \\ rev_full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_inter_alt]
  \\ full_simp_tac(srw_ss())[domain_lookup,unit_some_eq_IS_SOME,adjust_set_def,lookup_fromAList]
  \\ rev_full_simp_tac(srw_ss())[IS_SOME_ALOOKUP_EQ,MEM_MAP] \\ srw_tac[][]
  \\ Cases_on `y'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][EXISTS_PROD,adjust_var_11]
  \\ full_simp_tac(srw_ss())[MEM_toAList,lookup_inter_alt]);

val state_rel_get_var_RefPtr = Q.store_thm("state_rel_get_var_RefPtr",
  `state_rel c l1 l2 s t v1 locs ∧
   get_var n s.locals = SOME (RefPtr p) ⇒
   ∃f u. get_var (adjust_var n) t = SOME (Word (get_addr c (FAPPLY f p) u))`,
  rw[]
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs[state_rel_def,wordSemTheory.get_var_def,bvpSemTheory.get_var_def]
  \\ full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)]
  \\ drule (GEN_ALL word_ml_inv_lookup)
  \\ disch_then drule
  \\ disch_then drule
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`v1 ++ (rr ++ ls)`
  \\ qmatch_abbrev_tac`P (v1 ++ (rr ++ ls)) ⇒ _`
  \\ strip_tac
  \\ `P (rr ++ v1 ++ ls)`
  by (
    unabbrev_all_tac
    \\ match_mp_tac (GEN_ALL (MP_CANON word_ml_inv_rearrange))
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[] \\ metis_tac[] )
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ simp[Abbr`P`,Abbr`rr`,word_ml_inv_def]
  \\ strip_tac \\ rveq
  \\ fs[abs_ml_inv_def]
  \\ fs[bc_stack_ref_inv_def]
  \\ fs[v_inv_def]
  \\ simp[word_addr_def]
  \\ metis_tac[]);

val state_rel_get_var_Block = Q.store_thm("state_rel_get_var_Block",
  `state_rel c l1 l2 s t v1 locs ∧
   get_var n s.locals = SOME (Block tag vs) ⇒
   ∃w. get_var (adjust_var n) t = SOME (Word w)`,
  rw[]
  \\ imp_res_tac state_rel_get_var_IMP
  \\ fs[state_rel_def,wordSemTheory.get_var_def,bvpSemTheory.get_var_def]
  \\ full_simp_tac std_ss [Once (GSYM APPEND_ASSOC)]
  \\ drule (GEN_ALL word_ml_inv_lookup)
  \\ disch_then drule
  \\ disch_then drule
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ qmatch_goalsub_abbrev_tac`v1 ++ (rr ++ ls)`
  \\ qmatch_abbrev_tac`P (v1 ++ (rr ++ ls)) ⇒ _`
  \\ strip_tac
  \\ `P (rr ++ v1 ++ ls)`
  by (
    unabbrev_all_tac
    \\ match_mp_tac (GEN_ALL (MP_CANON word_ml_inv_rearrange))
    \\ ONCE_REWRITE_TAC[CONJ_COMM]
    \\ asm_exists_tac
    \\ simp[] \\ metis_tac[] )
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ simp[Abbr`P`,Abbr`rr`,word_ml_inv_def]
  \\ strip_tac \\ rveq
  \\ fs[abs_ml_inv_def]
  \\ fs[bc_stack_ref_inv_def]
  \\ fs[v_inv_def]
  \\ rator_x_assum`COND`mp_tac
  \\ IF_CASES_TAC \\ simp[word_addr_def]
  \\ strip_tac \\ rveq
  \\ simp[word_addr_def]);

val state_rel_cut_state_opt_get_var = Q.store_thm("state_rel_cut_state_opt_get_var",
  `state_rel c l1 l2 s t [] locs ∧
   cut_state_opt names_opt s = SOME x ∧
   get_var v x.locals = SOME w ⇒
   ∃s'. state_rel c l1 l2 s' t [] locs ∧
        get_var v s'.locals = SOME w`,
  rw[cut_state_opt_def]
  \\ every_case_tac \\ fs[] >- metis_tac[]
  \\ fs[cut_state_def]
  \\ every_case_tac \\ fs[]
  \\ imp_res_tac state_rel_cut_env
  \\ metis_tac[] );

val jump_exc_push_env_NONE_simp = prove(
  ``(jump_exc (dec_clock t) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (push_env y NONE t) = NONE <=> jump_exc t = NONE) /\
    (jump_exc (call_env args s) = NONE <=> jump_exc s = NONE)``,
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
      wordSemTheory.dec_clock_def] \\ srw_tac[][] THEN1 every_case_tac
  \\ full_simp_tac(srw_ss())[wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Cases_on `t.handler = LENGTH t.stack` \\ full_simp_tac(srw_ss())[LASTN_ADD1]
  \\ Cases_on `~(t.handler < LENGTH t.stack)` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  THEN1 (`F` by DECIDE_TAC)
  \\ `LASTN (t.handler + 1) (StackFrame q NONE::t.stack) =
      LASTN (t.handler + 1) t.stack` by
    (match_mp_tac LASTN_TL \\ decide_tac) \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ CCONTR_TAC
  \\ full_simp_tac(srw_ss())[NOT_LESS]
  \\ `SUC (LENGTH t.stack) <= t.handler + 1` by decide_tac
  \\ imp_res_tac (LASTN_LENGTH_LESS_EQ |> Q.SPEC `x::xs`
       |> SIMP_RULE std_ss [LENGTH]) \\ full_simp_tac(srw_ss())[]);

val s_key_eq_handler_eq_IMP = prove(
  ``s_key_eq t.stack t1.stack /\ t.handler = t1.handler ==>
    (jump_exc t1 <> NONE <=> jump_exc t <> NONE)``,
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def] \\ srw_tac[][]
  \\ imp_res_tac s_key_eq_LENGTH \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `t1.handler < LENGTH t1.stack` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac s_key_eq_LASTN
  \\ pop_assum (qspec_then `t1.handler + 1` mp_tac)
  \\ every_case_tac \\ full_simp_tac(srw_ss())[s_key_eq_def,s_frame_key_eq_def]);

val eval_NONE_IMP_jump_exc_NONE_EQ = prove(
  ``evaluate (q,t) = (NONE,t1) ==> (jump_exc t1 = NONE <=> jump_exc t = NONE)``,
  srw_tac[][] \\ mp_tac (wordPropsTheory.evaluate_stack_swap |> Q.SPECL [`q`,`t`])
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ imp_res_tac s_key_eq_handler_eq_IMP \\ metis_tac []);

val jump_exc_push_env_SOME = prove(
  ``jump_exc (push_env y (SOME (x,prog1,l1,l2)) t) <> NONE``,
  full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ full_simp_tac(srw_ss())[LASTN_ADD1]);

val eval_push_env_T_Raise_IMP_stack_length = prove(
  ``evaluate (p,call_env ys (push_env x T (dec_clock s))) =
       (SOME (Rerr (Rraise a)),r') ==>
    LENGTH r'.stack = LENGTH s.stack``,
  qspecl_then [`p`,`call_env ys (push_env x T (dec_clock s))`]
    mp_tac bvpPropsTheory.evaluate_stack_swap
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[call_env_def,jump_exc_def,push_env_def,dec_clock_def,LASTN_ADD1]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val eval_push_env_SOME_exc_IMP_s_key_eq = prove(
  ``evaluate (p, call_env args1 (push_env y (SOME (x1,x2,x3,x4)) (dec_clock t))) =
      (SOME (Exception l w),t1) ==>
    s_key_eq t1.stack t.stack /\ t.handler = t1.handler``,
  qspecl_then [`p`,`call_env args1 (push_env y (SOME (x1,x2,x3,x4)) (dec_clock t))`]
    mp_tac wordPropsTheory.evaluate_stack_swap
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def,wordSemTheory.jump_exc_def,
         wordSemTheory.push_env_def,wordSemTheory.dec_clock_def,LASTN_ADD1]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF,LASTN_ADD1]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val eval_exc_stack_shorter = prove(
  ``evaluate (c,call_env ys (push_env x F (dec_clock s))) =
      (SOME (Rerr (Rraise a)),r') ==>
    LENGTH r'.stack < LENGTH s.stack``,
  srw_tac[][] \\ qspecl_then [`c`,`call_env ys (push_env x F (dec_clock s))`]
             mp_tac bvpPropsTheory.evaluate_stack_swap
  \\ full_simp_tac(srw_ss())[] \\ once_rewrite_tac [EQ_SYM_EQ] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[bvpSemTheory.jump_exc_def,call_env_def,push_env_def,dec_clock_def]
  \\ qpat_assum `xx = SOME s2` mp_tac
  \\ rpt (pop_assum (K all_tac))
  \\ full_simp_tac(srw_ss())[LASTN_ALT] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[ADD1]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ match_mp_tac LESS_LESS_EQ_TRANS
  \\ qexists_tac `LENGTH (LASTN (s.handler + 1) s.stack)`
  \\ full_simp_tac(srw_ss())[LENGTH_LASTN_LESS]);

val alloc_size_def = Define `
  alloc_size k = (if k * (dimindex (:'a) DIV 8) < dimword (:α) then
                    n2w (k * (dimindex (:'a) DIV 8))
                  else (-1w)):'a word`

val NOT_1_domain = prove(
  ``~(1 IN domain (adjust_set names))``,
  full_simp_tac(srw_ss())[domain_fromAList,adjust_set_def,MEM_MAP,MEM_toAList,
      FORALL_PROD,adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac)

val cut_env_adjust_set_insert_1 = prove(
  ``cut_env (adjust_set names) (insert 1 w l) = cut_env (adjust_set names) l``,
  full_simp_tac(srw_ss())[wordSemTheory.cut_env_def,MATCH_MP SUBSET_INSERT_EQ_SUBSET NOT_1_domain]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[lookup_inter,lookup_insert]
  \\ Cases_on `x = 1` \\ full_simp_tac(srw_ss())[] \\ every_case_tac \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[SIMP_RULE std_ss [domain_lookup] NOT_1_domain]);

val case_EQ_SOME_IFF = prove(
  ``(case p of NONE => NONE | SOME x => g x) = SOME y <=>
    ?x. p = SOME x /\ g x = SOME y``,
  Cases_on `p` \\ full_simp_tac(srw_ss())[]);

val state_rel_set_store_AllocSize = prove(
  ``state_rel c l1 l2 s (set_store AllocSize (Word w) t) v locs =
    state_rel c l1 l2 s t v locs``,
  full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.set_store_def]
  \\ eq_tac \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[heap_in_memory_store_def,FLOOKUP_DEF,FAPPLY_FUPDATE_THM]
  \\ metis_tac []);

val inter_insert = store_thm("inter_insert",
  ``inter (insert n x t1) t2 =
    if n IN domain t2 then insert n x (inter t1 t2) else inter t1 t2``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[spt_eq_thm,wf_inter,wf_insert,lookup_inter_alt,lookup_insert]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val lookup_1_adjust_set = prove(
  ``lookup 1 (adjust_set l) = NONE``,
  full_simp_tac(srw_ss())[adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ full_simp_tac(srw_ss())[adjust_var_def] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ decide_tac);

val state_rel_insert_1 = prove(
  ``state_rel c l1 l2 s (t with locals := insert 1 x t.locals) v locs =
    state_rel c l1 l2 s t v locs``,
  full_simp_tac(srw_ss())[state_rel_def] \\ eq_tac \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[lookup_insert,adjust_var_NEQ_1]
  \\ full_simp_tac(srw_ss())[inter_insert,domain_lookup,lookup_1_adjust_set]
  \\ metis_tac []);

val state_rel_inc_clock = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs ==>
    state_rel c l1 l2 (s with clock := s.clock + 1)
                      (t with clock := t.clock + 1) [] locs``,
  full_simp_tac(srw_ss())[state_rel_def]);

val dec_clock_inc_clock = prove(
  ``(bvpSem$dec_clock (s with clock := s.clock + 1) = s) /\
    (wordSem$dec_clock (t with clock := t.clock + 1) = t)``,
  full_simp_tac(srw_ss())[bvpSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
  \\ full_simp_tac(srw_ss())[bvpSemTheory.state_component_equality]
  \\ full_simp_tac(srw_ss())[wordSemTheory.state_component_equality])

val word_gc_move_IMP_isWord = prove(
  ``word_gc_move c' (Word c,i,pa,old,m,dm) = (w1,i1,pa1,m1,c1) ==> isWord w1``,
  full_simp_tac(srw_ss())[word_gc_move_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]);

val word_gc_move_roots_IMP_FILTER = prove(
  ``!ws i pa old m dm ws2 i2 pa2 m2 c2 c.
      word_gc_move_roots c (ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) ==>
      word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                           (FILTER isWord ws2,i2,pa2,m2,c2)``,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def] \\ Cases \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  THEN1
   (srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF] \\ imp_res_tac word_gc_move_IMP_isWord
    \\ Cases_on `word_gc_move_roots c' (ws,i1,pa1,old,m1,dm)` \\ full_simp_tac(srw_ss())[]
    \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
  \\ full_simp_tac(srw_ss())[isWord_def,word_gc_move_def,LET_DEF]
  \\ Cases_on `word_gc_move_roots c (ws,i,pa,old,m,dm)`
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]);

val IMP_EQ_DISJ = METIS_PROVE [] ``(b1 ==> b2) <=> ~b1 \/ b2``

val word_gc_fun_IMP_FILTER = prove(
  ``word_gc_fun c (xs,m,dm,s) = SOME (stack1,m1,s1) ==>
    word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (FILTER isWord stack1,m1,s1)``,
  full_simp_tac(srw_ss())[word_gc_fun_def,LET_THM,word_gc_fun_def,word_full_gc_def]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_FILTER
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[])

val loc_merge_def = Define `
  (loc_merge [] ys = []) /\
  (loc_merge (Loc l1 l2::xs) ys = Loc l1 l2::loc_merge xs ys) /\
  (loc_merge (Word w::xs) (y::ys) = y::loc_merge xs ys) /\
  (loc_merge (Word w::xs) [] = Word w::xs)`

val LENGTH_loc_merge = prove(
  ``!xs ys. LENGTH (loc_merge xs ys) = LENGTH xs``,
  Induct \\ Cases_on `ys` \\ full_simp_tac(srw_ss())[loc_merge_def]
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[loc_merge_def]
  \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[loc_merge_def]);

val word_gc_move_roots_IMP_FILTER = prove(
  ``!ws i pa old m dm ws2 i2 pa2 m2 c2 c.
      word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) ==>
      word_gc_move_roots c (ws,i,pa,old,m,dm) =
                           (loc_merge ws ws2,i2,pa2,m2,c2)``,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,loc_merge_def]
  \\ reverse Cases \\ full_simp_tac(srw_ss())[isWord_def,loc_merge_def,LET_DEF]
  THEN1
   (full_simp_tac(srw_ss())[word_gc_move_def] \\ srw_tac[][]
    \\ Cases_on `word_gc_move_roots c (ws,i,pa,old,m,dm)` \\ full_simp_tac(srw_ss())[]
    \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[])
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,loc_merge_def] \\ srw_tac[][]
  \\ Cases_on `word_gc_move c' (Word c,i,pa,old,m,dm)`
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Cases_on `word_gc_move_roots c' (FILTER isWord ws,r0,r1,old,r2,dm)`
  \\ PairCases_on `r` \\ full_simp_tac(srw_ss())[] \\ res_tac \\ full_simp_tac(srw_ss())[LET_DEF] \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[loc_merge_def]);

val word_gc_fun_loc_merge = prove(
  ``word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (ys,m1,s1) ==>
    word_gc_fun c (xs,m,dm,s) = SOME (loc_merge xs ys,m1,s1)``,
  full_simp_tac(srw_ss())[word_gc_fun_def,LET_THM,word_gc_fun_def,word_full_gc_def]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_FILTER
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[]);

val word_gc_fun_IMP = prove(
  ``word_gc_fun c (xs,m,dm,s) = SOME (ys,m1,s1) ==>
    FLOOKUP s1 AllocSize = FLOOKUP s AllocSize /\
    FLOOKUP s1 Handler = FLOOKUP s Handler /\
    Globals IN FDOM s1``,
  full_simp_tac(srw_ss())[IMP_EQ_DISJ,word_gc_fun_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ srw_tac[][]
  \\ UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ EVAL_TAC)

val word_gc_move_roots_IMP_EVERY2 = prove(
  ``!xs ys pa m i c1 m1 pa1 i1 old dm c.
      word_gc_move_roots c (xs,i,pa,old,m,dm) = (ys,i1,pa1,m1,c1) ==>
      EVERY2 (\x y. (isWord x <=> isWord y) /\ (~isWord x ==> x = y)) xs ys``,
  Induct \\ full_simp_tac(srw_ss())[word_gc_move_roots_def]
  \\ full_simp_tac(srw_ss())[IMP_EQ_DISJ,word_gc_fun_def] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ srw_tac[][] \\ res_tac
  \\ qpat_assum `word_gc_move c (h,i,pa,old,m,dm) = (w1,i1',pa1',m1',c1')` mp_tac
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `h` \\ full_simp_tac(srw_ss())[word_gc_move_def] \\ srw_tac[][]
  \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]
  \\ UNABBREV_ALL_TAC \\ srw_tac[][] \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ CCONTR_TAC \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def]);

val word_gc_IMP_EVERY2 = prove(
  ``word_gc_fun c (xs,m,dm,st) = SOME (ys,m1,s1) ==>
    EVERY2 (\x y. (isWord x <=> isWord y) /\ (~isWord x ==> x = y)) xs ys``,
  full_simp_tac(srw_ss())[word_gc_fun_def,LET_THM,word_gc_fun_def,word_full_gc_def]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[word_gc_move_roots_def,LET_THM]
  \\ rpt (pairarg_tac \\ full_simp_tac(srw_ss())[])
  \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_move_roots_IMP_EVERY2);

val word_gc_fun_LENGTH = store_thm("word_gc_fun_LENGTH",
  ``word_gc_fun c (xs,m,dm,s) = SOME (zs,m1,s1) ==> LENGTH xs = LENGTH zs``,
  srw_tac[][] \\ drule word_gc_IMP_EVERY2 \\ srw_tac[][] \\ imp_res_tac EVERY2_LENGTH);

val gc_fun_ok_word_gc_fun = store_thm("gc_fun_ok_word_gc_fun",
  ``gc_fun_ok (word_gc_fun c1)``,
  fs [gc_fun_ok_def] \\ rpt gen_tac \\ strip_tac
  \\ imp_res_tac word_gc_fun_LENGTH \\ fs []
  \\ imp_res_tac word_gc_fun_IMP
  \\ fs [FLOOKUP_DEF]
  \\ fs [word_gc_fun_def]
  \\ pairarg_tac \\ fs []
  \\ fs [DOMSUB_FAPPLY_THM]
  \\ rpt var_eq_tac \\ fs []
  \\ fs [word_gc_fun_assum_def,DOMSUB_FAPPLY_THM]
  \\ fs [fmap_EXT,FUPDATE_LIST,EXTENSION]
  \\ conj_tac THEN1 metis_tac []
  \\ fs [FAPPLY_FUPDATE_THM,DOMSUB_FAPPLY_THM]
  \\ rw [] \\ fs []);

val word_gc_fun_APPEND_IMP = prove(
  ``word_gc_fun c (xs ++ ys,m,dm,s) = SOME (zs,m1,s1) ==>
    ?zs1 zs2. zs = zs1 ++ zs2 /\ LENGTH xs = LENGTH zs1 /\ LENGTH ys = LENGTH zs2``,
  srw_tac[][] \\ imp_res_tac word_gc_fun_LENGTH \\ full_simp_tac(srw_ss())[LENGTH_APPEND]
  \\ pop_assum mp_tac \\ pop_assum (K all_tac)
  \\ qspec_tac (`zs`,`zs`) \\ qspec_tac (`ys`,`ys`) \\ qspec_tac (`xs`,`xs`)
  \\ Induct \\ full_simp_tac(srw_ss())[] \\ Cases_on `zs` \\ full_simp_tac(srw_ss())[LENGTH_NIL] \\ srw_tac[][]
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ full_simp_tac(srw_ss())[LENGTH_NIL]
  \\ full_simp_tac(srw_ss())[ADD_CLAUSES] \\ res_tac
  \\ full_simp_tac(srw_ss())[] \\ Q.LIST_EXISTS_TAC [`h::zs1`,`zs2`] \\ full_simp_tac(srw_ss())[]);

val IMP_loc_merge_APPEND = prove(
  ``!ts qs xs ys.
      LENGTH (FILTER isWord ts) = LENGTH qs ==>
      loc_merge (ts ++ xs) (qs ++ ys) = loc_merge ts qs ++ loc_merge xs ys``,
  Induct \\ full_simp_tac(srw_ss())[] THEN1 (Cases_on `qs` \\ full_simp_tac(srw_ss())[LENGTH,loc_merge_def])
  \\ Cases \\ full_simp_tac(srw_ss())[isWord_def,loc_merge_def]
  \\ Cases \\ full_simp_tac(srw_ss())[loc_merge_def]) |> SPEC_ALL;

val TAKE_DROP_loc_merge_APPEND = prove(
  ``TAKE (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = loc_merge (MAP SND q) xs /\
    DROP (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = ys``,
  `LENGTH q = LENGTH (loc_merge (MAP SND q) xs)` by full_simp_tac(srw_ss())[LENGTH_loc_merge]
  \\ full_simp_tac(srw_ss())[TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]);

val loc_merge_NIL = prove(
  ``!xs. loc_merge xs [] = xs``,
  Induct \\ full_simp_tac(srw_ss())[loc_merge_def] \\ Cases \\ full_simp_tac(srw_ss())[loc_merge_def]);

val loc_merge_APPEND = prove(
  ``!xs1 xs2 ys.
      ?zs1 zs2. loc_merge (xs1 ++ xs2) ys = zs1 ++ zs2 /\
                LENGTH zs1 = LENGTH xs1 /\ LENGTH xs2 = LENGTH xs2 /\
                ?ts. loc_merge xs2 ts = zs2``,
  Induct \\ full_simp_tac(srw_ss())[loc_merge_def,LENGTH_NIL,LENGTH_loc_merge] THEN1 (metis_tac [])
  \\ Cases THEN1
   (Cases_on `ys` \\ full_simp_tac(srw_ss())[loc_merge_def] \\ srw_tac[][]
    THEN1 (Q.LIST_EXISTS_TAC [`Word c::xs1`,`xs2`] \\ full_simp_tac(srw_ss())[]
           \\ qexists_tac `[]` \\ full_simp_tac(srw_ss())[loc_merge_NIL])
    \\ pop_assum (qspecl_then [`xs2`,`t`] strip_assume_tac)
    \\ full_simp_tac(srw_ss())[] \\ Q.LIST_EXISTS_TAC [`h::zs1`,`zs2`] \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[loc_merge_def]
  \\ pop_assum (qspecl_then [`xs2`,`ys`] strip_assume_tac)
  \\ full_simp_tac(srw_ss())[] \\ Q.LIST_EXISTS_TAC [`Loc n n0::zs1`,`zs2`] \\ full_simp_tac(srw_ss())[] \\ metis_tac [])

val EVERY2_loc_merge = prove(
  ``!xs ys. EVERY2 (\x y. (isWord y ==> isWord x) /\
                          (~isWord x ==> x = y)) xs (loc_merge xs ys)``,
  Induct \\ full_simp_tac(srw_ss())[loc_merge_def,LENGTH_NIL,LENGTH_loc_merge] \\ Cases
  \\ full_simp_tac(srw_ss())[loc_merge_def] \\ Cases_on `ys`
  \\ full_simp_tac(srw_ss())[loc_merge_def,GSYM EVERY2_refl,isWord_def])

val dec_stack_loc_merge_enc_stack = prove(
  ``!xs ys. ?ss. dec_stack (loc_merge (enc_stack xs) ys) xs = SOME ss``,
  Induct \\ full_simp_tac(srw_ss())[wordSemTheory.enc_stack_def,
    loc_merge_def,wordSemTheory.dec_stack_def]
  \\ Cases \\ Cases_on `o'` \\ full_simp_tac(srw_ss())[] \\ TRY (PairCases_on `x`)
  \\ full_simp_tac(srw_ss())[wordSemTheory.enc_stack_def] \\ srw_tac[][]
  \\ qspecl_then [`MAP SND l`,`enc_stack xs`,`ys`] mp_tac loc_merge_APPEND
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[wordSemTheory.dec_stack_def]
  \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ full_simp_tac(srw_ss())[DROP_LENGTH_APPEND]
  \\ first_assum (qspec_then `ts` strip_assume_tac) \\ full_simp_tac(srw_ss())[]
  \\ decide_tac);

val ALOOKUP_ZIP = prove(
  ``!l zs1.
      ALOOKUP l (0:num) = SOME (Loc q r) /\
      LIST_REL (λx y. (isWord y ⇒ isWord x) ∧
        (¬isWord x ⇒ x = y)) (MAP SND l) zs1 ==>
      ALOOKUP (ZIP (MAP FST l,zs1)) 0 = SOME (Loc q r)``,
  Induct \\ full_simp_tac(srw_ss())[] \\ Cases \\ full_simp_tac(srw_ss())[ALOOKUP_def,PULL_EXISTS]
  \\ Cases_on `q' = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[isWord_def] \\ srw_tac[][]);

val stack_rel_dec_stack_IMP_stack_rel = prove(
  ``!xs ys ts stack locs.
      LIST_REL stack_rel ts xs /\ LIST_REL contains_loc xs locs /\
      dec_stack (loc_merge (enc_stack xs) ys) xs = SOME stack ==>
      LIST_REL stack_rel ts stack /\ LIST_REL contains_loc stack locs``,
  Induct_on `ts` \\ Cases_on `xs` \\ full_simp_tac(srw_ss())[]
  THEN1 (full_simp_tac(srw_ss())[wordSemTheory.enc_stack_def,loc_merge_def,wordSemTheory.dec_stack_def])
  \\ full_simp_tac(srw_ss())[PULL_EXISTS] \\ srw_tac[][]
  \\ Cases_on `h` \\ Cases_on `o'` \\ TRY (PairCases_on `x`) \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.enc_stack_def,wordSemTheory.dec_stack_def]
  \\ qspecl_then [`MAP SND l`,`enc_stack t`,`ys`] mp_tac loc_merge_APPEND
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th] THEN assume_tac th)
  \\ full_simp_tac(srw_ss())[DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (fn th => full_simp_tac(srw_ss())[GSYM th])
  \\ res_tac \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `h'` \\ full_simp_tac(srw_ss())[stack_rel_def]
  \\ full_simp_tac(srw_ss())[lookup_fromAList,IS_SOME_ALOOKUP_EQ]
  \\ full_simp_tac(srw_ss())[EVERY_MEM,FORALL_PROD] \\ Cases_on `y`
  \\ full_simp_tac(srw_ss())[contains_loc_def]
  \\ qspecl_then [`MAP SND l ++ enc_stack t`,`ys`] mp_tac EVERY2_loc_merge
  \\ full_simp_tac(srw_ss())[] \\ strip_tac
  \\ `LENGTH (MAP SND l) = LENGTH zs1` by full_simp_tac(srw_ss())[]
  \\ imp_res_tac LIST_REL_APPEND_IMP \\ full_simp_tac(srw_ss())[MAP_ZIP]
  \\ full_simp_tac(srw_ss())[AND_IMP_INTRO]
  \\ `ALOOKUP (ZIP (MAP FST l,zs1)) 0 = SOME (Loc q r)` by
   (`LENGTH (MAP SND l) = LENGTH zs1` by full_simp_tac(srw_ss())[]
    \\ imp_res_tac LIST_REL_APPEND_IMP \\ full_simp_tac(srw_ss())[MAP_ZIP]
    \\ imp_res_tac ALOOKUP_ZIP \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
  \\ full_simp_tac(srw_ss())[] \\ NTAC 3 strip_tac \\ first_x_assum match_mp_tac
  \\ rev_full_simp_tac(srw_ss())[MEM_ZIP] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[EL_MAP]
  \\ Q.MATCH_ASSUM_RENAME_TAC `isWord (EL k zs1)`
  \\ full_simp_tac(srw_ss())[MEM_EL,PULL_EXISTS] \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[FST_PAIR_EQ]
  \\ imp_res_tac EVERY2_IMP_EL \\ rev_full_simp_tac(srw_ss())[EL_MAP]);

val join_env_NIL = prove(
  ``join_env s [] = []``,
  full_simp_tac(srw_ss())[join_env_def]);

val join_env_CONS = prove(
  ``join_env s ((n,v)::xs) =
    if n <> 0 /\ EVEN n then
      (THE (lookup ((n - 2) DIV 2) s),v)::join_env s xs
    else join_env s xs``,
  full_simp_tac(srw_ss())[join_env_def] \\ srw_tac[][]);

val FILTER_enc_stack_lemma = prove(
  ``!xs ys.
      LIST_REL stack_rel xs ys ==>
      FILTER isWord (MAP SND (flat xs ys)) =
      FILTER isWord (enc_stack ys)``,
  Induct \\ Cases_on `ys`
  \\ full_simp_tac(srw_ss())[stack_rel_def,wordSemTheory.enc_stack_def,flat_def]
  \\ Cases \\ Cases_on `h` \\ full_simp_tac(srw_ss())[] \\ Cases_on `o'`
  \\ TRY (PairCases_on `x`) \\ full_simp_tac(srw_ss())[stack_rel_def] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[wordSemTheory.enc_stack_def,flat_def,FILTER_APPEND]
  \\ qpat_assum `EVERY (\(x1,x2). isWord x2 ==> x1 <> 0 /\ EVEN x1) l` mp_tac
  \\ rpt (pop_assum (K all_tac))
  \\ Induct_on `l` \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[join_env_NIL]
  \\ Cases \\ full_simp_tac(srw_ss())[join_env_CONS] \\ srw_tac[][]);

val stack_rel_simp = prove(
  ``(stack_rel (Env s) y <=>
     ?vs. stack_rel (Env s) y /\ (y = StackFrame vs NONE)) /\
    (stack_rel (Exc s n) y <=>
     ?vs x1 x2 x3. stack_rel (Exc s n) y /\ (y = StackFrame vs (SOME (x1,x2,x3))))``,
  Cases_on `y` \\ full_simp_tac(srw_ss())[stack_rel_def] \\ Cases_on `o'`
  \\ full_simp_tac(srw_ss())[stack_rel_def] \\ PairCases_on `x`
  \\ full_simp_tac(srw_ss())[stack_rel_def,CONJ_ASSOC]);

val join_env_EQ_ZIP = prove(
  ``!vs s zs1.
      EVERY (\(x1,x2). isWord x2 ==> x1 <> 0 /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 /\
      LIST_REL (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
         (MAP SND (join_env s vs)) zs1 ==>
      join_env s
        (ZIP (MAP FST vs,loc_merge (MAP SND vs) (FILTER isWord zs1))) =
      ZIP (MAP FST (join_env s vs),zs1)``,
  Induct \\ simp [join_env_NIL,loc_merge_def] \\ rpt strip_tac
  \\ Cases_on `h` \\ simp [] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `r` \\ full_simp_tac(srw_ss())[isWord_def]
  \\ full_simp_tac(srw_ss())[loc_merge_def] \\ full_simp_tac(srw_ss())[join_env_CONS] \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ rev_full_simp_tac(srw_ss())[isWord_def] \\ full_simp_tac(srw_ss())[]
  \\ Cases_on `y` \\ full_simp_tac(srw_ss())[loc_merge_def,join_env_CONS,isWord_def]);

val LENGTH_MAP_SND_join_env_IMP = prove(
  ``!vs zs1 s.
      LIST_REL (\x y. (isWord x = isWord y) /\ (~isWord x ==> x = y))
        (MAP SND (join_env s vs)) zs1 /\
      EVERY (\(x1,x2). isWord x2 ==> x1 <> 0 /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 ==>
      LENGTH (FILTER isWord (MAP SND vs)) = LENGTH (FILTER isWord zs1)``,
  Induct \\ rpt strip_tac THEN1
   (pop_assum mp_tac \\ simp [join_env_NIL]
    \\ Cases_on `zs1` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][])
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[join_env_CONS] \\ srw_tac[][]
  THEN1 (full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[] \\ first_assum match_mp_tac \\ metis_tac[])
  \\ full_simp_tac(srw_ss())[] \\ Cases_on `q <> 0 /\ EVEN q`
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ metis_tac [])

val lemma1 = prove(``(y1 = y2) /\ (x1 = x2) ==> (f x1 y1 = f x2 y2)``,full_simp_tac(srw_ss())[]);

val word_gc_fun_EL_lemma = prove(
  ``!xs ys stack1 m dm st m1 s1 stack.
      LIST_REL stack_rel xs stack /\
      EVERY2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
         (MAP SND (flat xs ys)) stack1 /\
      dec_stack (loc_merge (enc_stack ys) (FILTER isWord stack1)) ys =
        SOME stack /\ LIST_REL stack_rel xs ys ==>
      (flat xs stack =
       ZIP (MAP FST (flat xs ys),stack1))``,
  Induct THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[] \\ EVAL_TAC \\ srw_tac[][] \\ srw_tac[][flat_def])
  \\ Cases_on `h` \\ full_simp_tac(srw_ss())[] \\ once_rewrite_tac [stack_rel_simp]
  \\ full_simp_tac(srw_ss())[PULL_EXISTS,stack_rel_def,flat_def,wordSemTheory.enc_stack_def]
  \\ srw_tac[][] \\ imp_res_tac EVERY2_APPEND_IMP \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[FILTER_APPEND]
  \\ `LENGTH (FILTER isWord (MAP SND vs')) = LENGTH (FILTER isWord zs1)` by
   (imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac LENGTH_MAP_SND_join_env_IMP)
  \\ imp_res_tac IMP_loc_merge_APPEND \\ full_simp_tac(srw_ss())[]
  \\ qpat_assum `dec_stack xx dd = SOME yy` mp_tac
  \\ full_simp_tac(srw_ss())[wordSemTheory.dec_stack_def]
  \\ full_simp_tac(srw_ss())[TAKE_DROP_loc_merge_APPEND,LENGTH_loc_merge,DECIDE ``~(n+m<n:num)``]
  \\ CASE_TAC \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[flat_def] \\ imp_res_tac EVERY2_LENGTH \\ full_simp_tac(srw_ss())[GSYM ZIP_APPEND]
  \\ match_mp_tac lemma1
  \\ rpt strip_tac \\ TRY (first_x_assum match_mp_tac \\ full_simp_tac(srw_ss())[])
  \\ TRY (match_mp_tac join_env_EQ_ZIP) \\ full_simp_tac(srw_ss())[]) |> SPEC_ALL;

val state_rel_gc = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs ==>
    FLOOKUP t.store AllocSize = SOME (Word (alloc_size k)) /\
    s.locals = LN /\
    t.locals = LS (Loc l1 l2) ==>
    ?t2 wl m st w1 w2 stack.
      t.gc_fun (enc_stack t.stack,t.memory,t.mdomain,t.store) =
        SOME (wl,m,st) /\
      dec_stack wl t.stack = SOME stack /\
      FLOOKUP st AllocSize = SOME (Word (alloc_size k)) /\
      state_rel c l1 l2 (s with space := 0)
        (t with <|stack := stack; store := st; memory := m|>) [] locs``,
  full_simp_tac(srw_ss())[state_rel_def] \\ srw_tac[][] \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[lookup_def] \\ srw_tac[][]
  \\ qpat_assum `word_ml_inv (heap,F,a,sp) limit c s.refs xxx` mp_tac
  \\ Q.PAT_ABBREV_TAC `pat = join_env LN _` \\ srw_tac[][]
  \\ `pat = []` by (UNABBREV_ALL_TAC \\ EVAL_TAC) \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[] \\ pop_assum (K all_tac)
  \\ first_x_assum (fn th1 => first_x_assum (fn th2 => first_x_assum (fn th3 =>
       mp_tac (MATCH_MP word_gc_fun_correct (CONJ th1 (CONJ th2 th3))))))
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_fun_IMP_FILTER
  \\ imp_res_tac FILTER_enc_stack_lemma \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac word_gc_fun_loc_merge \\ full_simp_tac(srw_ss())[FILTER_APPEND]
  \\ imp_res_tac word_gc_fun_IMP \\ full_simp_tac(srw_ss())[]
  \\ `?stack. dec_stack (loc_merge (enc_stack t.stack) (FILTER isWord stack1))
        t.stack = SOME stack` by metis_tac [dec_stack_loc_merge_enc_stack]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac stack_rel_dec_stack_IMP_stack_rel \\ full_simp_tac(srw_ss())[]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ full_simp_tac(srw_ss())[MEM] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ disj2_tac
  \\ pop_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``x=y==>(x==>y)``)
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ match_mp_tac (GEN_ALL word_gc_fun_EL_lemma)
  \\ imp_res_tac word_gc_IMP_EVERY2 \\ full_simp_tac(srw_ss())[]);

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
        state_rel c l1 l2 (s with <| locals := x; space := 0 |>) t2 [] locs``,
  srw_tac[][] \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ Q.UNABBREV_TAC `t0` \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac (state_rel_call_env_push_env
      |> Q.SPEC `NONE` |> Q.INST [`args`|->`[]`] |> GEN_ALL
      |> SIMP_RULE std_ss [MAP,get_vars_def,wordSemTheory.get_vars_def]
      |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
      |> (fn th => MATCH_MP th (UNDISCH state_rel_inc_clock))
      |> SIMP_RULE (srw_ss()) [dec_clock_inc_clock] |> DISCH_ALL)
  \\ full_simp_tac(srw_ss())[]
  \\ pop_assum (qspecl_then [`l1`,`l2`] mp_tac) \\ srw_tac[][]
  \\ pop_assum (mp_tac o MATCH_MP state_rel_gc)
  \\ impl_tac THEN1
   (full_simp_tac(srw_ss())[wordSemTheory.call_env_def,call_env_def,
        wordSemTheory.push_env_def,fromList_def]
    \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[fromList2_def,Once insert_def])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[wordSemTheory.call_env_def]
  \\ pop_assum (mp_tac o MATCH_MP
      (state_rel_pop_env_IMP |> REWRITE_RULE [GSYM AND_IMP_INTRO]
         |> Q.GEN `s2`)) \\ srw_tac[][]
  \\ pop_assum (qspec_then `s with <| locals := x ; space := 0 |>` mp_tac)
  \\ impl_tac THEN1
   (full_simp_tac(srw_ss())[pop_env_def,push_env_def,call_env_def,
      bvpSemTheory.state_component_equality])
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]);

val gc_add_call_env = prove(
  ``(case gc (push_env y NONE t5) of
     | NONE => (SOME Error,x)
     | SOME s' => case pop_env s' of
                  | NONE => (SOME Error, call_env [] s')
                  | SOME s' => f s') = (res,t) ==>
    (case gc (call_env [Loc l1 l2] (push_env y NONE t5)) of
     | NONE => (SOME Error,x)
     | SOME s' => case pop_env s' of
                  | NONE => (SOME Error, call_env [] s')
                  | SOME s' => f s') = (res,t)``,
  full_simp_tac(srw_ss())[wordSemTheory.gc_def,wordSemTheory.call_env_def,LET_DEF,
      wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t5.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.pop_env_def]);

val has_space_state_rel = prove(
  ``has_space (Word ((alloc_size k):'a word)) (r:('a,'ffi) state) = SOME T /\
    state_rel c l1 l2 s r [] locs ==>
    state_rel c l1 l2 (s with space := k) r [] locs``,
  full_simp_tac(srw_ss())[state_rel_def] \\ srw_tac[][]
  \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[heap_in_memory_store_def,wordSemTheory.has_space_def]
  \\ full_simp_tac(srw_ss())[GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ full_simp_tac(srw_ss())[alloc_size_def,bytes_in_word_def]
  \\ `(sp * (dimindex (:'a) DIV 8)) + 1 < dimword (:'a)` by
   (imp_res_tac word_ml_inv_SP_LIMIT
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
  \\ `(sp * (dimindex (:'a) DIV 8)) < dimword (:'a)` by decide_tac
  \\ every_case_tac \\ full_simp_tac(srw_ss())[word_mul_n2w]
  \\ full_simp_tac(srw_ss())[good_dimindex_def]
  \\ full_simp_tac(srw_ss())[w2n_minus1] \\ rev_full_simp_tac(srw_ss())[]
  \\ `F` by decide_tac);

val evaluate_IMP_inc_clock = prove(
  ``evaluate (q,t) = (NONE,t1) ==>
    evaluate (q,inc_clock ck t) = (NONE,inc_clock ck t1)``,
  srw_tac[][inc_clock_def] \\ match_mp_tac evaluate_add_clock
  \\ full_simp_tac(srw_ss())[]);

val evaluate_IMP_inc_clock_Ex = prove(
  ``evaluate (q,t) = (SOME (Exception x y),t1) ==>
    evaluate (q,inc_clock ck t) = (SOME (Exception x y),inc_clock ck t1)``,
  srw_tac[][inc_clock_def] \\ match_mp_tac evaluate_add_clock
  \\ full_simp_tac(srw_ss())[]);

val get_var_inc_clock = prove(
  ``get_var n (inc_clock k s) = get_var n s``,
  full_simp_tac(srw_ss())[wordSemTheory.get_var_def,inc_clock_def]);

val get_vars_inc_clock = prove(
  ``get_vars n (inc_clock k s) = get_vars n s``,
  Induct_on `n` \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[get_var_inc_clock]);

val set_var_inc_clock = store_thm("set_var_inc_clock",
  ``set_var n x (inc_clock ck t) = inc_clock ck (set_var n x t)``,
  full_simp_tac(srw_ss())[wordSemTheory.set_var_def,inc_clock_def]);

val do_app = LIST_CONJ [bvpSemTheory.do_app_def,do_space_def,
  bvp_spaceTheory.op_space_req_def,
  bvi_to_bvpTheory.op_space_reset_def, bviSemTheory.do_app_def,
  bviSemTheory.do_app_aux_def, bvlSemTheory.do_app_def]

val alloc_lemma = store_thm("alloc_lemma",
  ``state_rel c l1 l2 s (t:('a,'ffi)wordSem$state) [] locs /\
    bvpSem$cut_env names s.locals = SOME x /\
    alloc (alloc_size k) (adjust_set names)
        (t with locals := insert 1 (Word (alloc_size k)) t.locals) =
      ((q:'a result option),r) ==>
    (q = SOME NotEnoughSpace ⇒ r.ffi = s.ffi) ∧
    (q ≠ SOME NotEnoughSpace ⇒
     state_rel c l1 l2 (s with <|locals := x; space := k|>) r [] locs ∧
     q = NONE)``,
  strip_tac
  \\ full_simp_tac(srw_ss())[wordSemTheory.alloc_def,
       LET_DEF,addressTheory.CONTAINER_def]
  \\ Q.ABBREV_TAC `t5 = (set_store AllocSize (Word (alloc_size k))
               (t with locals := insert 1 (Word (alloc_size k)) t.locals))`
  \\ imp_res_tac cut_env_IMP_cut_env
  \\ full_simp_tac(srw_ss())[cut_env_adjust_set_insert_1]
  \\ first_x_assum (assume_tac o HO_MATCH_MP gc_add_call_env)
  \\ `FLOOKUP t5.store AllocSize = SOME (Word (alloc_size k)) /\
      cut_env (adjust_set names) t5.locals = SOME y /\
      state_rel c l1 l2 s t5 [] locs` by
   (UNABBREV_ALL_TAC \\ full_simp_tac(srw_ss())[state_rel_set_store_AllocSize]
    \\ full_simp_tac(srw_ss())[cut_env_adjust_set_insert_1,
         wordSemTheory.set_store_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[SUBSET_DEF,state_rel_insert_1,FLOOKUP_DEF])
  \\ strip_tac
  \\ mp_tac (gc_lemma |> Q.INST [`t`|->`t5`] |> SIMP_RULE std_ss [LET_DEF])
  \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[wordSemTheory.gc_def,wordSemTheory.call_env_def,
         wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t5.permute` \\ full_simp_tac(srw_ss())[LET_DEF]
  \\ `IS_SOME (has_space (Word (alloc_size k):'a word_loc) t2)` by
       full_simp_tac(srw_ss())[wordSemTheory.has_space_def,
          state_rel_def,heap_in_memory_store_def]
  \\ Cases_on `has_space (Word (alloc_size k):'a word_loc) t2`
  \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ rev_full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ imp_res_tac has_space_state_rel \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac bvpPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
  \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
  \\ UNABBREV_ALL_TAC
  \\ full_simp_tac(srw_ss())[wordSemTheory.set_store_def,state_rel_def])

val evaluate_GiveUp = store_thm("evaluate_GiveUp",
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs ==>
    ?r. evaluate (GiveUp,t) = (SOME NotEnoughSpace,r) /\
        r.ffi = s.ffi /\ t.ffi = s.ffi``,
  fs [GiveUp_def,wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
  \\ strip_tac
  \\ Cases_on `alloc (-1w) (insert 0 () LN) (set_var 1 (Word (-1w)) t)
                  :'a result option # ('a,'ffi) wordSem$state`
  \\ fs [wordSemTheory.set_var_def]
  \\ `-1w = alloc_size (dimword (:'a)):'a word` by
   (fs [alloc_size_def,state_rel_def]
    \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw [])
  \\ pop_assum (fn th => fs [th])
  \\ drule (alloc_lemma |> Q.INST [`names`|->`LN`,`k`|->`dimword(:'a)`] |> GEN_ALL)
  \\ fs [bvpSemTheory.cut_env_def,set_var_def]
  \\ Cases_on `q = SOME NotEnoughSpace` \\ fs []
  \\ CCONTR_TAC \\ fs []
  \\ rpt var_eq_tac
  \\ fs [state_rel_def]
  \\ fs [word_ml_inv_def,abs_ml_inv_def,unused_space_inv_def,heap_ok_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ fs [heap_length_APPEND]
  \\ fs [heap_length_def,el_length_def]
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []
  \\ rfs [] \\ fs []);

val state_rel_cut_IMP = store_thm("state_rel_cut_IMP",
  ``state_rel c l1 l2 s t [] locs /\ cut_state_opt names_opt s = SOME x ==>
    state_rel c l1 l2 x t [] locs``,
  Cases_on `names_opt` \\ fs [bvpSemTheory.cut_state_opt_def]
  THEN1 (rw [] \\ fs [])
  \\ fs [bvpSemTheory.cut_state_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ imp_res_tac state_rel_cut_env);

val get_vars_SING = store_thm("get_vars_SING",
  ``bvpSem$get_vars args s = SOME [w] ==> ?y. args = [y]``,
  Cases_on `args` \\ fs [get_vars_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ Cases_on `t` \\ fs [get_vars_def]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []);

val clean_tac = rpt var_eq_tac \\ rpt (qpat_assum `T` kall_tac)
fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

val eval_tac = fs [wordSemTheory.evaluate_def,
  wordSemTheory.word_exp_def, wordSemTheory.set_var_def, set_var_def,
  bvi_to_bvp_def, wordSemTheory.the_words_def,
  bviSemTheory.bvl_to_bvi_def, bvp_to_bvi_def,
  bviSemTheory.bvi_to_bvl_def,wordSemTheory.mem_load_def,
  wordLangTheory.word_op_def, wordSemTheory.word_sh_def,
  wordLangTheory.num_exp_def]

val INT_EQ_NUM_LEMMA = store_thm("INT_EQ_NUM_LEMMA",
  ``0 <= (i:int) <=> ?index. i = & index``,
  Cases_on `i` \\ fs []);

val get_vars_2_IMP = store_thm("get_vars_2_IMP",
  ``(wordSem$get_vars [x1;x2] s = SOME [v1;v2]) ==>
    get_var x1 s = SOME v1 /\
    get_var x2 s = SOME v2``,
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []);

val get_vars_3_IMP = store_thm("get_vars_3_IMP",
  ``(wordSem$get_vars [x1;x2;x3] s = SOME [v1;v2;v3]) ==>
    get_var x1 s = SOME v1 /\
    get_var x2 s = SOME v2 /\
    get_var x3 s = SOME v3``,
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []);

val memory_rel_get_vars_IMP = prove(
  ``memory_rel c be s.refs sp st m dm
     (join_env s.locals
        (toAList (inter t.locals (adjust_set s.locals))) ++ envs) ∧
    get_vars n (s:'ffi bvpSem$state).locals = SOME x ∧
    get_vars (MAP adjust_var n) (t:('a,'ffi) wordSem$state) = SOME w ⇒
    memory_rel c be s.refs sp st m dm
      (ZIP (x,w) ++
       join_env s.locals
         (toAList (inter t.locals (adjust_set s.locals))) ++ envs)``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ drule word_ml_inv_get_vars_IMP \\ fs []);

val memory_rel_insert = prove(
  ``memory_rel c F refs sp st m dm
     ([(x,w)] ++ join_env d (toAList (inter l (adjust_set d))) ++ xs) ⇒
    memory_rel c F refs sp st m dm
     (join_env (insert dest x d)
        (toAList
           (inter (insert (adjust_var dest) w l)
              (adjust_set (insert dest x d)))) ++ xs)``,
  fs [memory_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ match_mp_tac word_ml_inv_insert \\ fs []);

val get_real_addr_lemma = store_thm("get_real_addr_lemma",
  ``shift_length c < dimindex (:'a) /\
    good_dimindex (:'a) /\
    get_var v t = SOME (Word ptr_w) /\
    get_real_addr c t.store ptr_w = SOME x ==>
    word_exp t (real_addr c v) = SOME (Word (x:'a word))``,
  fs [get_real_addr_def] \\ every_case_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,real_addr_def] \\ eval_tac \\ fs []
  \\ rpt strip_tac \\ fs []
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []
  \\ rfs [shift_def]);

val get_real_offset_lemma = store_thm("get_real_offset_lemma",
  ``get_var v t = SOME (Word i_w) /\
    good_dimindex (:'a) /\
    get_real_offset i_w = SOME y ==>
    word_exp t (real_offset c v) = SOME (Word (y:'a word))``,
  fs [get_real_offset_def] \\ every_case_tac \\ fs []
  \\ fs [wordSemTheory.get_var_def,real_offset_def] \\ eval_tac \\ fs []
  \\ fs [labPropsTheory.good_dimindex_def,dimword_def] \\ rw []);

val reorder_lemma = prove(
  ``memory_rel c F x.refs x.space t.store t.memory t.mdomain (x1::x2::x3::xs) ==>
    memory_rel c F x.refs x.space t.store t.memory t.mdomain (x3::x1::x2::xs)``,
  match_mp_tac memory_rel_rearrange \\ fs [] \\ rw [] \\ fs []);

val evaluate_StoreEach = store_thm("evaluate_StoreEach",
  ``!xs ys t offset m1.
      store_list (a + offset) ys t.memory t.mdomain = SOME m1 /\
      get_vars xs t = SOME ys /\
      get_var i t = SOME (Word a) ==>
      evaluate (StoreEach i xs offset, t) = (NONE,t with memory := m1)``,
  Induct
  \\ fs [store_list_def,StoreEach_def] \\ eval_tac
  \\ fs [wordSemTheory.state_component_equality,
           wordSemTheory.get_vars_def,store_list_def,
           wordSemTheory.get_var_def]
  \\ rw [] \\ fs [] \\ CASE_TAC \\ fs []
  \\ Cases_on `get_vars xs t` \\ fs [] \\ clean_tac
  \\ fs [store_list_def,wordSemTheory.mem_store_def]
  \\ `(t with memory := m1) =
      (t with memory := (a + offset =+ x) t.memory) with memory := m1` by
       (fs [wordSemTheory.state_component_equality] \\ NO_TAC)
  \\ pop_assum (fn th => rewrite_tac [th])
  \\ first_x_assum match_mp_tac \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ qcase_tac `get_vars qs t = SOME ts`
  \\ pop_assum mp_tac
  \\ qspec_tac (`ts`,`ts`)
  \\ qspec_tac (`qs`,`qs`)
  \\ Induct \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
  \\ rw [] \\ every_case_tac \\ fs [])
  |> Q.SPECL [`xs`,`ys`,`t`,`0w`] |> SIMP_RULE (srw_ss()) [] |> GEN_ALL;

val domain_adjust_set_EVEN = store_thm("domain_adjust_set_EVEN",
  ``k IN domain (adjust_set s) ==> EVEN k``,
  fs [adjust_set_def,domain_lookup,lookup_fromAList] \\ rw [] \\ fs []
  \\ imp_res_tac ALOOKUP_MEM \\ fs [MEM_MAP]
  \\ pairarg_tac \\ fs [EVEN_adjust_var]);

val inter_insert_ODD_adjust_set = store_thm("inter_insert_ODD_adjust_set",
  ``!k. ODD k ==>
      inter (insert (adjust_var dest) w (insert k v s)) (adjust_set t) =
      inter (insert (adjust_var dest) w s) (adjust_set t)``,
  fs [spt_eq_thm,wf_inter,lookup_inter_alt,lookup_insert]
  \\ rw [] \\ rw [] \\ fs []
  \\ imp_res_tac domain_adjust_set_EVEN \\ fs [EVEN_ODD]);

val get_vars_adjust_var = prove(
  ``ODD k ==>
    get_vars (MAP adjust_var args) (t with locals := insert k w s) =
    get_vars (MAP adjust_var args) (t with locals := s)``,
  Induct_on `args`
  \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def,lookup_insert]
  \\ rw [] \\ fs [ODD_EVEN,EVEN_adjust_var]);

val get_vars_with_store = store_thm("get_vars_with_store",
  ``!args. get_vars args (t with <| locals := t.locals ; store := s |>) =
           get_vars args t``,
  Induct \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]);

val LEAST_NOT_IN_FDOM = prove(
  ``~((LEAST (ptr:num). ~(ptr IN FDOM refs)) IN FDOM refs)``,
  qabbrev_tac `p = \ptr. ~(ptr IN FDOM refs)`
  \\ `p ($LEAST p)` by all_tac
  \\ TRY (unabbrev_all_tac \\ fs [] \\ NO_TAC)
  \\ match_mp_tac LEAST_INTRO \\ unabbrev_all_tac \\ fs []
  \\ assume_tac (MATCH_MP INFINITE_DIFF_FINITE (CONJ INFINITE_NUM_UNIV
     (FDOM_FINITE |> Q.SPEC `refs`
        |> INST_TYPE [``:'a``|->``:num``,``:'b``|->``:'a``])))
  \\ fs [EXTENSION] \\ metis_tac []);

val word_less_lemma1 = prove(
  ``v2 < (v1:'a word) <=> ~(v1 <= v2)``,
  metis_tac [WORD_NOT_LESS]);

val heap_in_memory_store_IMP_UPDATE = prove(
  ``heap_in_memory_store heap a sp c st m dm l ==>
    heap_in_memory_store heap a sp c (st |+ (Globals,h)) m dm l``,
  fs [heap_in_memory_store_def,FLOOKUP_UPDATE]);

val get_vars_2_imp = prove(
  ``wordSem$get_vars [x1;x2] s = SOME [y1;y2] ==>
    wordSem$get_var x1 s = SOME y1 /\
    wordSem$get_var x2 s = SOME y2``,
  fs [wordSemTheory.get_vars_def] \\ every_case_tac \\ fs []);

val assign_thm = Q.prove(
  `state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs /\
   (op_space_reset op ==> names_opt <> NONE) /\
   cut_state_opt names_opt s = SOME x /\
   get_vars args x.locals = SOME vals /\
   do_app op vals x = Rval (v,s2) ==>
   ?q r.
     evaluate (FST (assign c n l dest op args names_opt),t) = (q,r) /\
     (q = SOME NotEnoughSpace ==> r.ffi = t.ffi) /\
     (q <> SOME NotEnoughSpace ==>
     state_rel c l1 l2 (set_var dest v s2) r [] locs /\ q = NONE)`,
  strip_tac \\ drule (evaluate_GiveUp |> GEN_ALL) \\ rw [] \\ fs []
  \\ imp_res_tac state_rel_cut_IMP \\ pop_assum mp_tac
  \\ qpat_assum `state_rel c l1 l2 s t [] locs` kall_tac \\ strip_tac
  \\ Cases_on `op = Add` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ qpat_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
    \\ strip_tac
    \\ simp_tac std_ss [state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac \\ fs []
    \\ rpt_drule memory_rel_Number_IMP_Word_2
    \\ strip_tac \\ clean_tac
    \\ rpt_drule memory_rel_Add \\ fs [] \\ strip_tac
    \\ fs [assign_def]
    \\ imp_res_tac get_vars_2_imp
    \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
    \\ eval_tac
    \\ fs [asmSemTheory.word_cmp_def]
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
      (rpt_drule (evaluate_GiveUp
         |> Q.INST [`t`|->`(t with locals := insert 1 x t.locals)`]
         |> REWRITE_RULE [state_rel_insert_1])
       \\ disch_then (qspec_then `Word (w1 ‖ w2)` strip_assume_tac) \\ fs [])
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ rw [] \\ fs []
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ drule memory_rel_zero_space \\ fs [])
  \\ Cases_on `op = Sub` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ qpat_assum `state_rel c l1 l2 x t [] locs` (fn th => NTAC 2 (mp_tac th))
    \\ strip_tac
    \\ simp_tac std_ss [state_rel_thm] \\ strip_tac \\ fs [] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac \\ fs []
    \\ rpt_drule memory_rel_Number_IMP_Word_2
    \\ strip_tac \\ clean_tac
    \\ rpt_drule memory_rel_Sub \\ fs [] \\ strip_tac
    \\ fs [assign_def]
    \\ imp_res_tac get_vars_2_imp
    \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
    \\ eval_tac
    \\ fs [asmSemTheory.word_cmp_def]
    \\ reverse IF_CASES_TAC \\ fs []
    THEN1
      (rpt_drule (evaluate_GiveUp
         |> Q.INST [`t`|->`(t with locals := insert 1 x t.locals)`]
         |> REWRITE_RULE [state_rel_insert_1])
       \\ disch_then (qspec_then `Word (w1 ‖ w2)` strip_assume_tac) \\ fs [])
    \\ fs [lookup_insert,adjust_var_NEQ,adjust_var_11]
    \\ rw [] \\ fs []
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
    \\ drule memory_rel_zero_space \\ fs [])
(*
  \\ Cases_on `op = LengthByte` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_1] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ rpt_drule memory_rel_ByteArray_IMP \\ fs [] \\ rw []
    \\ fs [assign_def]
    \\ fs [wordSemTheory.get_vars_def]
    \\ Cases_on `get_var (adjust_var a1) t` \\ fs [] \\ clean_tac
    \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
    \\ fs [asmSemTheory.word_cmp_def,word_and_one_eq_0_iff
             |> SIMP_RULE (srw_ss()) []]
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
         (match_mp_tac (GEN_ALL get_real_addr_lemma)
          \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
    \\ `2 < dimindex (:'a)` by
         (fs [labPropsTheory.good_dimindex_def] \\ fs [])
    \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ fs [WORD_MUL_LSL,WORD_LEFT_ADD_DISTRIB,GSYM word_add_n2w]
    \\ fs [word_mul_n2w]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac (IMP_memory_rel_Number_num3
         |> SIMP_RULE std_ss [WORD_MUL_LSL,word_mul_n2w]) \\ fs [])
*)
 \\ Cases_on `op = IsBlock` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_1] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac THEN1
     (imp_res_tac memory_rel_Number_IMP \\ clean_tac
      \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_imm_def]
      \\ every_case_tac \\ fs [] \\ clean_tac \\ fs []
      \\ fs [assign_def] \\ eval_tac
      \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_imm_def,
             asmSemTheory.word_cmp_def,Smallnum_bits]
      \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
    THEN1
     (rpt_drule memory_rel_Block_IMP \\ strip_tac \\ clean_tac
      \\ pop_assum mp_tac \\ IF_CASES_TAC \\ clean_tac \\ strip_tac
      THEN1
       (fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_imm_def]
        \\ every_case_tac \\ fs [] \\ clean_tac \\ fs []
        \\ fs [assign_def] \\ eval_tac
        \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_imm_def,
               asmSemTheory.word_cmp_def,Smallnum_bits]
        \\ fs [word_index_test]
        \\ IF_CASES_TAC \\ rfs [IsBlock_word_lemma]
        \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
        \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
        \\ match_mp_tac memory_rel_insert \\ fs []
        \\ match_mp_tac memory_rel_Boolv_T \\ fs [])
      \\ fs [word_bit_test]
      \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_imm_def]
      \\ every_case_tac \\ fs [] \\ clean_tac \\ fs []
      \\ fs [assign_def] \\ eval_tac
      \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             asmSemTheory.word_cmp_def,word_index_test]
      \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
      \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
           (match_mp_tac (GEN_ALL get_real_addr_lemma)
            \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
      \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,inter_insert_ODD_adjust_set]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac memory_rel_Boolv_T \\ fs [])
    \\ rpt_drule memory_rel_RefPtr_IMP \\ strip_tac \\ clean_tac
    \\ fs [word_bit_test,word_index_test]
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_imm_def]
    \\ every_case_tac \\ fs [] \\ clean_tac \\ fs []
    \\ fs [assign_def] \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def,
             asmSemTheory.word_cmp_def,word_index_test]
    \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
           (match_mp_tac (GEN_ALL get_real_addr_lemma)
            \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
    \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,inter_insert_ODD_adjust_set]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Boolv_F \\ fs [])
  \\ Cases_on `op = Length` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_1] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ rpt_drule memory_rel_ValueArray_IMP \\ fs [] \\ rw []
    \\ fs [assign_def]
    \\ fs [wordSemTheory.get_vars_def]
    \\ Cases_on `get_var (adjust_var a1) t` \\ fs [] \\ clean_tac
    \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
    \\ fs [asmSemTheory.word_cmp_def,word_and_one_eq_0_iff
             |> SIMP_RULE (srw_ss()) []]
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
         (match_mp_tac (GEN_ALL get_real_addr_lemma)
          \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
    \\ fs [GSYM NOT_LESS,GREATER_EQ]
    \\ `c.len_size <> 0` by
        (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
    \\ fs [NOT_LESS]
    \\ `~(dimindex (:α) <= 2)` by
           (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
    \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ fs [decode_length_def]
    \\ match_mp_tac IMP_memory_rel_Number_num \\ fs [])
  \\ Cases_on `op = LengthBlock` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_1] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ drule memory_rel_Block_IMP \\ fs [] \\ rw []
    \\ fs [assign_def]
    \\ fs [wordSemTheory.get_vars_def]
    \\ Cases_on `get_var (adjust_var a1) t` \\ fs [] \\ clean_tac
    \\ eval_tac
    \\ fs [wordSemTheory.get_var_def,wordSemTheory.get_var_imm_def]
    \\ fs [asmSemTheory.word_cmp_def,word_and_one_eq_0_iff
             |> SIMP_RULE (srw_ss()) []]
    \\ reverse (Cases_on `w ' 0`) \\ fs [] THEN1
     (fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac memory_rel_insert \\ fs []
      \\ match_mp_tac (IMP_memory_rel_Number |> Q.INST [`i`|->`0`]
            |> SIMP_RULE std_ss [EVAL ``Smallnum 0``])
      \\ fs [] \\ fs [labPropsTheory.good_dimindex_def,dimword_def]
      \\ EVAL_TAC \\ rw [labPropsTheory.good_dimindex_def,dimword_def])
    \\ `shift_length c < dimindex (:α)` by (fs [memory_rel_def] \\ NO_TAC)
    \\ `word_exp t (real_addr c (adjust_var a1)) = SOME (Word a)` by
         (match_mp_tac (GEN_ALL get_real_addr_lemma)
          \\ fs [wordSemTheory.get_var_def] \\ NO_TAC) \\ fs []
    \\ fs [GSYM NOT_LESS,GREATER_EQ]
    \\ `c.len_size <> 0` by
        (fs [memory_rel_def,heap_in_memory_store_def] \\ NO_TAC)
    \\ fs [NOT_LESS]
    \\ `~(dimindex (:α) <= 2)` by
           (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
    \\ fs [] \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ fs [decode_length_def]
    \\ match_mp_tac IMP_memory_rel_Number_num \\ fs [])
  \\ Cases_on `op = GreaterEq` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ rpt_drule memory_rel_Number_LESS \\ rw [] \\ fs []
    \\ fs [wordSemTheory.get_vars_def] \\ every_case_tac
    \\ fs [wordSemTheory.get_var_imm_def] \\ clean_tac
    \\ fs [assign_def] \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ fs [intLib.COOPER_PROVE `` i >= j:int <=> ~(i < j)``]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [] \\ NO_TAC)
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [] \\ NO_TAC))
  \\ Cases_on `op = Greater` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ rpt_drule memory_rel_Number_LESS_EQ \\ rw [] \\ fs []
    \\ fs [wordSemTheory.get_vars_def] \\ every_case_tac
    \\ fs [wordSemTheory.get_var_imm_def] \\ clean_tac
    \\ fs [assign_def] \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ simp [word_less_lemma1]
    \\ fs [intLib.COOPER_PROVE `` i > j:int <=> ~(i <= j)``]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [] \\ NO_TAC)
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [] \\ NO_TAC))
  \\ Cases_on `op = LessEq` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ rpt_drule memory_rel_Number_LESS_EQ \\ rw [] \\ fs []
    \\ fs [wordSemTheory.get_vars_def] \\ every_case_tac
    \\ fs [wordSemTheory.get_var_imm_def] \\ clean_tac
    \\ fs [assign_def] \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ fs [WORD_NOT_LESS,intLib.COOPER_PROVE ``~(i < j) <=> j <= i:int``]
    \\ simp [word_less_lemma1]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [] \\ NO_TAC)
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [] \\ NO_TAC))
  \\ Cases_on `op = Less` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ rpt_drule memory_rel_Number_LESS \\ rw [] \\ fs []
    \\ fs [wordSemTheory.get_vars_def] \\ every_case_tac
    \\ fs [wordSemTheory.get_var_imm_def] \\ clean_tac
    \\ fs [assign_def] \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [] \\ NO_TAC)
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [] \\ NO_TAC))
  \\ Cases_on `op = Equal` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ rw []
    \\ fs [do_app] \\ rfs [] \\ every_case_tac \\ fs []
    \\ clean_tac \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [LENGTH_EQ_2] \\ clean_tac
    \\ fs [get_var_def]
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ strip_tac
    \\ TRY (rpt_drule memory_rel_Number_EQ) \\ rw [] \\ fs []
    \\ TRY (rpt_drule memory_rel_RefPtr_EQ) \\ rw [] \\ fs []
    \\ fs [wordSemTheory.get_vars_def] \\ every_case_tac
    \\ fs [wordSemTheory.get_var_imm_def] \\ clean_tac
    \\ fs [assign_def] \\ eval_tac
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ IF_CASES_TAC \\ fs []
    \\ fs [lookup_insert,adjust_var_11] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ TRY (match_mp_tac memory_rel_Boolv_T \\ fs [] \\ NO_TAC)
    \\ TRY (match_mp_tac memory_rel_Boolv_F \\ fs [] \\ NO_TAC))
  \\ Cases_on `?lab. op = Label lab` \\ fs [] THEN1
   (fs [assign_def] \\ fs [do_app] \\ every_case_tac \\ fs []
    \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
    \\ fs [state_rel_thm] \\ eval_tac
    \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
    \\ rw [] \\ fs [] \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_CodePtr \\ fs [])
  \\ Cases_on `op = Ref` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs []
    \\ fs [assign_def] \\ fs [do_app] \\ every_case_tac \\ fs []
    \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
    \\ fs [consume_space_def] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ qabbrev_tac `new = LEAST ptr. ptr ∉ FDOM x.refs`
    \\ `new ∉ FDOM x.refs` by metis_tac [LEAST_NOT_IN_FDOM]
    \\ rpt_drule memory_rel_Ref \\ strip_tac
    \\ fs [list_Seq_def] \\ eval_tac
    \\ fs [wordSemTheory.set_store_def]
    \\ qpat_abbrev_tac `t5 = t with <| locals := _ ; store := _ |>`
    \\ pairarg_tac \\ fs []
    \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
         (unabbrev_all_tac \\ fs []) \\ fs []
    \\ ntac 2 (pop_assum kall_tac)
    \\ drule evaluate_StoreEach
    \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`] mp_tac)
    \\ impl_tac THEN1
     (fs [wordSemTheory.get_vars_def,Abbr`t5`,wordSemTheory.get_var_def,
          lookup_insert,get_vars_with_store,get_vars_adjust_var] \\ NO_TAC)
    \\ clean_tac \\ fs [] \\ UNABBREV_ALL_TAC
    \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
    \\ rw [] \\ fs [] \\ rw [] \\ fs []
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ fs [make_ptr_def])
  \\ Cases_on `op = Update` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs []
    \\ fs [do_app] \\ every_case_tac \\ fs [] \\ clean_tac
    \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule \\ fs []
    \\ imp_res_tac get_vars_3_IMP \\ fs []
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_3] \\ clean_tac
    \\ imp_res_tac get_vars_3_IMP \\ fs [] \\ strip_tac
    \\ drule reorder_lemma \\ strip_tac
    \\ drule (memory_rel_Update |> GEN_ALL) \\ fs []
    \\ strip_tac \\ clean_tac
    \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
        word_exp t (real_addr c (adjust_var a1)) = SOME (Word x')` by
          metis_tac [get_real_offset_lemma,get_real_addr_lemma]
    \\ fs [] \\ eval_tac \\ fs [EVAL ``word_exp s1 Unit``]
    \\ fs [wordSemTheory.mem_store_def]
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ match_mp_tac memory_rel_Unit \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ rw [] \\ fs [])
  \\ Cases_on `op = Deref` \\ fs [] THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs []
    \\ fs [do_app] \\ every_case_tac \\ fs [] \\ clean_tac
    \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule \\ fs []
    \\ imp_res_tac get_vars_2_IMP \\ fs []
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
    \\ drule (memory_rel_Deref |> GEN_ALL) \\ fs []
    \\ strip_tac \\ clean_tac
    \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
        word_exp t (real_addr c (adjust_var a1)) = SOME (Word x')` by
          metis_tac [get_real_offset_lemma,get_real_addr_lemma]
    \\ fs [] \\ eval_tac
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `op = El` \\ fs [] \\ fs [] \\ clean_tac THEN1
   (imp_res_tac get_vars_IMP_LENGTH \\ fs []
    \\ fs [do_app] \\ every_case_tac \\ fs [] \\ clean_tac
    \\ fs [INT_EQ_NUM_LEMMA] \\ clean_tac
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [assign_def] \\ eval_tac \\ fs [state_rel_thm]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule \\ fs []
    \\ imp_res_tac get_vars_2_IMP \\ fs []
    \\ fs [integerTheory.NUM_OF_INT,LENGTH_EQ_2] \\ clean_tac
    \\ imp_res_tac get_vars_2_IMP \\ fs [] \\ strip_tac
    \\ drule (memory_rel_El |> GEN_ALL) \\ fs []
    \\ strip_tac \\ clean_tac
    \\ `word_exp t (real_offset c (adjust_var a2)) = SOME (Word y) /\
        word_exp t (real_addr c (adjust_var a1)) = SOME (Word x')` by
          metis_tac [get_real_offset_lemma,get_real_addr_lemma]
    \\ fs [] \\ eval_tac
    \\ fs [lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac memory_rel_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `?i. op = Const i` \\ fs [] THEN1
   (var_eq_tac \\ fs [do_app]
    \\ every_case_tac \\ fs []
    \\ rpt var_eq_tac
    \\ fs [assign_def]
    \\ Cases_on `i` \\ fs []
    \\ fs [wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
    \\ fs [state_rel_def,wordSemTheory.set_var_def,set_var_def,
          lookup_insert,adjust_var_11]
    \\ rw [] \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac word_ml_inv_insert \\ fs []
    \\ TRY (match_mp_tac word_ml_inv_zero) \\ fs []
    \\ TRY (match_mp_tac word_ml_inv_num) \\ fs []
    \\ TRY (match_mp_tac word_ml_inv_neg_num) \\ fs [])
  \\ Cases_on `op = GlobalsPtr` \\ fs [] THEN1
   (var_eq_tac \\ fs [do_app]
    \\ every_case_tac \\ fs []
    \\ rpt var_eq_tac
    \\ fs [assign_def]
    \\ fs [bvp_to_bvi_def]
    \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def]
    \\ fs [state_rel_def]
    \\ fs [the_global_def,libTheory.the_def]
    \\ fs [FLOOKUP_DEF,wordSemTheory.set_var_def,lookup_insert,
           adjust_var_11,libTheory.the_def,set_var_def]
    \\ rw [] \\ fs []
    \\ asm_exists_tac \\ fs []
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac word_ml_inv_insert \\ fs []
    \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
    \\ fs [] \\ rw [] \\ fs [])
  \\ Cases_on `op = SetGlobalsPtr` \\ fs [] THEN1
   (var_eq_tac \\ fs [do_app]
    \\ every_case_tac \\ fs []
    \\ rpt var_eq_tac
    \\ fs [assign_def]
    \\ imp_res_tac get_vars_SING \\ fs []
    \\ `args <> []` by (strip_tac \\ fs [bvpSemTheory.get_vars_def])
    \\ fs[wordSemTheory.evaluate_def,wordSemTheory.word_exp_def,Unit_def]
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ Cases_on `ws` \\ fs [LENGTH_NIL] \\ rpt var_eq_tac
    \\ pop_assum (fn th => assume_tac th THEN mp_tac th)
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
    \\ every_case_tac \\ fs [] \\ rpt var_eq_tac
    \\ fs [state_rel_def,wordSemTheory.set_var_def,lookup_insert,
           adjust_var_11,libTheory.the_def,set_var_def,bvi_to_bvp_def,
           wordSemTheory.set_store_def,bvp_to_bvi_def]
    \\ rpt_drule heap_in_memory_store_IMP_UPDATE
    \\ disch_then (qspec_then `h` assume_tac)
    \\ rw [] \\ fs []
    \\ asm_exists_tac \\ fs [the_global_def,libTheory.the_def]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (GEN_ALL word_ml_inv_get_vars_IMP)
    \\ disch_then drule
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.get_var_def]
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac word_ml_inv_insert \\ fs []
    \\ match_mp_tac word_ml_inv_Unit
    \\ pop_assum mp_tac \\ fs []
    \\ match_mp_tac word_ml_inv_rearrange \\ rw [] \\ fs [])
  \\ Cases_on `?tag. op = Cons tag` \\ fs [] \\ fs [] THEN1
   (Cases_on `LENGTH args = 0` THEN1
     (fs [assign_def] \\ IF_CASES_TAC \\ fs []
      \\ fs [LENGTH_NIL] \\ rpt var_eq_tac
      \\ fs [do_app] \\ every_case_tac \\ fs []
      \\ imp_res_tac get_vars_IMP_LENGTH \\ fs []
      \\ Cases_on `vals` \\ fs [] \\ clean_tac
      \\ eval_tac \\ clean_tac
      \\ fs [state_rel_def,lookup_insert,adjust_var_11]
      \\ rw [] \\ fs []
      \\ asm_exists_tac \\ fs []
      \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
      \\ match_mp_tac word_ml_inv_insert \\ fs []
      \\ fs [word_ml_inv_def,PULL_EXISTS] \\ rw []
      \\ qexists_tac `Data (Word (n2w (16 * tag + 2)))`
      \\ qexists_tac `hs` \\ fs [word_addr_def]
      \\ reverse conj_tac
      THEN1 (fs [GSYM word_mul_n2w,GSYM word_add_n2w,BlockNil_and_lemma])
      \\ `n2w (16 * tag + 2) = BlockNil tag : 'a word` by
           fs [BlockNil_def,WORD_MUL_LSL,word_mul_n2w,word_add_n2w]
      \\ fs [cons_thm_EMPTY])
    \\ fs [assign_def] \\ CASE_TAC \\ fs []
    \\ fs [do_app] \\ every_case_tac \\ fs []
    \\ imp_res_tac get_vars_IMP_LENGTH \\ fs [] \\ clean_tac
    \\ fs [consume_space_def] \\ clean_tac
    \\ imp_res_tac state_rel_get_vars_IMP
    \\ fs [state_rel_thm] \\ eval_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ drule (memory_rel_get_vars_IMP |> GEN_ALL)
    \\ disch_then drule \\ fs [NOT_LESS,DECIDE ``n + 1 <= m <=> n < m:num``]
    \\ strip_tac
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ `vals <> []` by fs [GSYM LENGTH_NIL]
    \\ rpt_drule memory_rel_Cons \\ strip_tac
    \\ fs [list_Seq_def] \\ eval_tac
    \\ fs [wordSemTheory.set_store_def]
    \\ qpat_abbrev_tac `t5 = t with <| locals := _ ; store := _ |>`
    \\ pairarg_tac \\ fs []
    \\ `t.memory = t5.memory /\ t.mdomain = t5.mdomain` by
         (unabbrev_all_tac \\ fs []) \\ fs []
    \\ ntac 2 (pop_assum kall_tac)
    \\ drule evaluate_StoreEach
    \\ disch_then (qspecl_then [`3::MAP adjust_var args`,`1`] mp_tac)
    \\ impl_tac THEN1
     (fs [wordSemTheory.get_vars_def,Abbr`t5`,wordSemTheory.get_var_def,
          lookup_insert,get_vars_with_store,get_vars_adjust_var] \\ NO_TAC)
    \\ clean_tac \\ fs [] \\ UNABBREV_ALL_TAC
    \\ fs [lookup_insert,FAPPLY_FUPDATE_THM,adjust_var_11,FLOOKUP_UPDATE]
    \\ rw [] \\ fs [] \\ rw [] \\ fs []
    \\ fs [inter_insert_ODD_adjust_set]
    \\ full_simp_tac std_ss [GSYM APPEND_ASSOC]
    \\ match_mp_tac memory_rel_insert \\ fs []
    \\ fs [make_cons_ptr_def,get_lowerbits_def])
  \\ Cases_on `op = BlockCmp` \\ fs [] THEN1 cheat
  \\ Cases_on `?tag len. op = TagLenEq tag len` \\ fs [] THEN1 cheat
  \\ Cases_on `?tag. op = TagEq tag` \\ fs [] THEN1 cheat
  \\ Cases_on `op = ToList` \\ fs [] THEN1 (fs [do_app])
  \\ Cases_on `op = AllocGlobal` \\ fs [] THEN1 (fs [do_app])
  \\ Cases_on `?i. op = Global i` \\ fs [] THEN1 (fs [do_app])
  \\ Cases_on `?i. op = SetGlobal i` \\ fs [] THEN1 (fs [do_app])
  \\ `assign c n l dest op args names_opt = (GiveUp,l)` by
        (Cases_on `op` \\ fs [assign_def] \\ NO_TAC) \\ fs []);

val none = ``NONE:(num # ('a wordLang$prog) # num # num) option``

val bvp_compile_correct = store_thm("bvp_compile_correct",
  ``!prog (s:'ffi bvpSem$state) c n l l1 l2 res s1 (t:('a,'ffi)wordSem$state) locs.
      (bvpSem$evaluate (prog,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] locs ==>
      ?t1 res1.
        (wordSem$evaluate (FST (comp c n l prog),t) = (res1,t1)) /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events ∧
           (IS_SOME t1.ffi.final_event ⇒ t1.ffi = s1.ffi)) /\
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
                LASTN (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
                !i. state_rel c l5 l6 (set_var i v s1)
                       (set_var (adjust_var i) w t1) [] ll)
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)``,
  recInduct bvpSemTheory.evaluate_ind \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
  THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ srw_tac[][])
  THEN1 (* Move *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var src s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[wordSemTheory.get_vars_def,wordSemTheory.set_vars_def,alist_insert_def]
    \\ full_simp_tac(srw_ss())[state_rel_def,set_var_def,lookup_insert]
    \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    THEN1 (srw_tac[][] \\ Cases_on `n = dest` \\ full_simp_tac(srw_ss())[])
    \\ asm_exists_tac
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_insert \\ full_simp_tac(srw_ss())[])
  THEN1 (* Assign *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ imp_res_tac (METIS_PROVE [] ``(if b1 /\ b2 then x1 else x2) = y ==>
                                     b1 /\ b2 /\ x1 = y \/
                                     (b1 ==> ~b2) /\ x2 = y``)
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ Cases_on `cut_state_opt names_opt s` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `get_vars args x.locals` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `do_app op x' x`) \\ full_simp_tac(srw_ss())[]
    THEN1 (imp_res_tac do_app_Rerr \\ srw_tac[][])
    \\ Cases_on `a`
    \\ drule (GEN_ALL assign_thm) \\ full_simp_tac(srw_ss())[]
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [`n`,`l`,`dest`] strip_assume_tac)
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac do_app_io_events_mono \\ rev_full_simp_tac(srw_ss())[]
    \\ `s.ffi = t.ffi` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ `x.ffi = s.ffi` by all_tac
    \\ imp_res_tac do_app_io_events_mono \\ rev_full_simp_tac(srw_ss())[]
    \\ Cases_on `names_opt` \\ full_simp_tac(srw_ss())[cut_state_opt_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[cut_state_def,cut_env_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ rpt (pop_assum mp_tac)
    \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[state_rel_def,bvpSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
    \\ full_simp_tac(srw_ss())[call_env_def,wordSemTheory.call_env_def]
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ full_simp_tac(srw_ss())[])
  THEN1 (* MakeSpace *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,
        wordSemTheory.evaluate_def,
        GSYM alloc_size_def,LET_DEF,wordSemTheory.word_exp_def,
        wordLangTheory.word_op_def,wordSemTheory.get_var_imm_def]
    \\ `?end next.
          FLOOKUP t.store EndOfHeap = SOME (Word end) /\
          FLOOKUP t.store NextFree = SOME (Word next)` by
            full_simp_tac(srw_ss())[state_rel_def,heap_in_memory_store_def]
    \\ full_simp_tac(srw_ss())[wordSemTheory.the_words_def]
    \\ reverse CASE_TAC THEN1
     (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[wordSemTheory.set_var_def,state_rel_insert_1]
      \\ match_mp_tac state_rel_cut_env \\ reverse (srw_tac[][])
      \\ full_simp_tac(srw_ss())[add_space_def] \\ match_mp_tac has_space_state_rel
      \\ full_simp_tac(srw_ss())[wordSemTheory.has_space_def,WORD_LO,NOT_LESS,
             asmSemTheory.word_cmp_def])
    \\ Cases_on `bvpSem$cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[add_space_def,wordSemTheory.word_exp_def,
         wordSemTheory.get_var_def,wordSemTheory.set_var_def]
    \\ Cases_on `(alloc (alloc_size k) (adjust_set names)
         (t with locals := insert 1 (Word (alloc_size k)) t.locals))
             :('a result option)#( ('a,'ffi) wordSem$state)`
    \\ full_simp_tac(srw_ss())[]
    \\ drule (GEN_ALL alloc_lemma)
    \\ rpt (disch_then drule)
    \\ rw [] \\ fs [])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac state_rel_jump_exc \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][mk_loc_def])
  THEN1 (* Return *)
   (full_simp_tac(srw_ss())[comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.get_var_def]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.call_env_def,lookup_def,
           bvpSemTheory.call_env_def,fromList_def,EVAL ``join_env LN []``,
           EVAL ``toAList (inter (fromList2 []) (insert 0 () LN))``]
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ pop_assum mp_tac
    \\ match_mp_tac word_ml_inv_rearrange
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (* Seq *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `comp c n l c1` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `comp c n r c2` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `q'' <> SOME (Rerr (Rabort Rtype_error))` by
         (Cases_on `q'' = NONE` \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
           first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`l`])
    \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `q'' = NONE`) \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ Cases_on `q''` \\ full_simp_tac(srw_ss())[]
           \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ Cases_on `e` \\ full_simp_tac(srw_ss())[])
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[]
      \\ imp_res_tac bvpPropsTheory.evaluate_io_events_mono \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac IS_PREFIX_TRANS \\ full_simp_tac(srw_ss())[] \\ metis_tac []) \\ srw_tac[][]
    \\ qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
    \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[mk_loc_def] \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_mk_loc_EQ \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
    \\ full_simp_tac(srw_ss())[jump_exc_inc_clock_EQ_NONE] \\ metis_tac [])
  THEN1 (* If *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `comp c n l c1` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `comp c n r c2` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP
    \\ full_simp_tac(srw_ss())[wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ imp_res_tac get_var_T_OR_F
    \\ Cases_on `x = Boolv T` \\ full_simp_tac(srw_ss())[] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n`,`l`] mp_tac)
      \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[])
    \\ Cases_on `x = Boolv F` \\ full_simp_tac(srw_ss())[] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n`,`r`] mp_tac)
      \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[]))
  THEN1 (* Call *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret`
    \\ full_simp_tac(srw_ss())[bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def,
           wordSemTheory.add_ret_loc_def,get_vars_inc_clock]
    THEN1 (* ret = NONE *)
     (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]
      \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac state_rel_0_get_vars_IMP \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def]
      \\ mp_tac find_code_thm \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      THEN1 (full_simp_tac(srw_ss())[call_env_def,wordSemTheory.call_env_def,state_rel_def])
      \\ Cases_on `evaluate (r,call_env q (dec_clock s))` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ res_tac
      \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ full_simp_tac(srw_ss())[]
      \\ `t.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def]
      \\ Cases_on `res1` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[mk_loc_def]
      \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def]
      \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[mk_loc_def])
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `domain (adjust_set r) <> {}` by full_simp_tac(srw_ss())[adjust_set_def,domain_fromAList]
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[wordSemTheory.evaluate_def]
    \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac state_rel_get_vars_IMP \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[wordSemTheory.add_ret_loc_def]
    THEN1 (* no handler *)
     (Cases_on `bvlSem$find_code dest x s.code` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac bvl_find_code
      \\ `¬bad_dest_args dest (MAP adjust_var args)` by
        (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
        imp_res_tac get_vars_IMP_LENGTH>>
        metis_tac[LENGTH_NIL])
      \\ Q.MATCH_ASSUM_RENAME_TAC `bvlSem$find_code dest xs s.code = SOME (ys,prog)`
      \\ Cases_on `bvpSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
      \\ mp_tac find_code_thm_ret \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      THEN1 (full_simp_tac(srw_ss())[call_env_def,wordSemTheory.call_env_def,state_rel_def])
      \\ Cases_on `evaluate (prog,call_env ys (push_env x F (dec_clock s)))`
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ full_simp_tac(srw_ss())[]
      \\ res_tac (* inst ind hyp *)
      \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
      THEN1
       (`s1.ffi = r'.ffi` by all_tac \\ full_simp_tac(srw_ss())[]
        \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[set_var_def]
        \\ imp_res_tac bvpPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
        \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[])
      \\ reverse (Cases_on `x'` \\ full_simp_tac(srw_ss())[])
      THEN1 (Cases_on `e` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ full_simp_tac(srw_ss())[jump_exc_call_env,jump_exc_dec_clock,jump_exc_push_env_NONE]
        \\ Cases_on `jump_exc t = NONE` \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp]
        \\ `LENGTH r'.stack < LENGTH locs` by ALL_TAC
        \\ imp_res_tac LASTN_TL \\ full_simp_tac(srw_ss())[]
        \\ `LENGTH locs = LENGTH s.stack` by
           (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
        \\ imp_res_tac eval_exc_stack_shorter)
      \\ Cases_on `pop_env r'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac state_rel_pop_env_set_var_IMP \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ imp_res_tac evaluate_IMP_domain_EQ \\ full_simp_tac(srw_ss())[])
    (* with handler *)
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ `?prog1 h1. comp c x0 (l + 2) x1 = (prog1,h1)` by METIS_TAC [PAIR]
    \\ full_simp_tac(srw_ss())[wordSemTheory.evaluate_def,wordSemTheory.add_ret_loc_def]
    \\ Cases_on `bvlSem$find_code dest x' s.code` \\ full_simp_tac(srw_ss())[] \\ Cases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac bvl_find_code
    \\ `¬bad_dest_args dest (MAP adjust_var args)` by
        (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
        imp_res_tac get_vars_IMP_LENGTH>>
        metis_tac[LENGTH_NIL])
    \\ Q.MATCH_ASSUM_RENAME_TAC `bvlSem$find_code dest xs s.code = SOME (ys,prog)`
    \\ Cases_on `bvpSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ mp_tac find_code_thm_handler \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    THEN1 (full_simp_tac(srw_ss())[call_env_def,wordSemTheory.call_env_def,state_rel_def])
    \\ Cases_on `evaluate (prog,call_env ys (push_env x T (dec_clock s)))`
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ full_simp_tac(srw_ss())[]
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[]
      \\ `r'.ffi.io_events ≼ s1.ffi.io_events ∧
          (IS_SOME t1.ffi.final_event ⇒ r'.ffi = s1.ffi)` by all_tac
      \\ TRY (imp_res_tac IS_PREFIX_TRANS \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac bvpPropsTheory.evaluate_io_events_mono \\ full_simp_tac(srw_ss())[set_var_def]
      \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac bvpPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ metis_tac [])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `pop_env r'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac state_rel_pop_env_set_var_IMP \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ pop_assum mp_tac \\ full_simp_tac(srw_ss())[]
      \\ match_mp_tac (GEN_ALL evaluate_IMP_domain_EQ) \\ full_simp_tac(srw_ss())[]
      \\ asm_exists_tac \\ full_simp_tac(srw_ss())[])
    \\ reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[] \\ srw_tac[][])
    \\ full_simp_tac(srw_ss())[mk_loc_jump_exc]
    \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
    \\ qpat_assum `!x y z.bbb` (K ALL_TAC)
    \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp,jump_exc_push_env_SOME]
    \\ imp_res_tac eval_push_env_T_Raise_IMP_stack_length
    \\ `LENGTH s.stack = LENGTH locs` by
         (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[LASTN_ADD1] \\ srw_tac[][]
    \\ first_x_assum (qspec_then `x0` assume_tac)
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum (qspecl_then [`x0`,`l+2`] strip_assume_tac) \\ full_simp_tac(srw_ss())[] \\ rev_full_simp_tac(srw_ss())[]
    \\ `jump_exc (set_var (adjust_var x0) w t1) = jump_exc t1` by
          full_simp_tac(srw_ss())[wordSemTheory.set_var_def,wordSemTheory.jump_exc_def]
    \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac mk_loc_eq_push_env_exc_Exception \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac eval_push_env_SOME_exc_IMP_s_key_eq
    \\ imp_res_tac s_key_eq_handler_eq_IMP
    \\ full_simp_tac(srw_ss())[jump_exc_inc_clock_EQ_NONE] \\ metis_tac []));

val compile_correct_lemma = store_thm("compile_correct_lemma",
  ``!(s:'ffi bvpSem$state) c l1 l2 res s1 (t:('a,'ffi)wordSem$state) start.
      (bvpSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] [] ==>
      ?t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,t) = (res1,t1)) /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events ∧
           (IS_SOME t1.ffi.final_event ==> t1.ffi = s1.ffi)) /\
        (res1 <> SOME NotEnoughSpace ==>
         case res of
        | NONE => (res1 = NONE)
        | SOME (Rval v) => t1.ffi = s1.ffi /\
                           ?w. (res1 = SOME (Result (Loc l1 l2) w))
        | SOME (Rerr (Rraise v)) => (?v w. res1 = SOME (Exception v w))
        | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)``,
  rpt strip_tac
  \\ drule bvp_compile_correct \\ full_simp_tac(srw_ss())[]
  \\ disch_then drule \\ full_simp_tac(srw_ss())[comp_def]
  \\ strip_tac
  \\ qexists_tac `t1`
  \\ qexists_tac `res1`
  \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[state_rel_def]);

val state_rel_ext_def = Define `
  state_rel_ext (c,t',k',a',c',col) l1 l2 s u <=>
    ?t l.
      state_rel c l1 l2 s t [] [] /\
      (!n v. lookup n t.code = SOME v ==>
             lookup n l = SOME (SND (full_compile_single t' k' a' c' ((n,v),col)))) /\
      u = t with <|code := l;termdep:=0|>`

val compile_correct = store_thm("compile_correct",
  ``!x (s:'ffi bvpSem$state) l1 l2 res s1 (t:('a,'ffi)wordSem$state) start.
      (bvpSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel_ext x l1 l2 s t ==>
      ?ck t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,
           (inc_clock ck t)) = (res1,t1)) /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events ∧
           (IS_SOME t1.ffi.final_event ==> t1.ffi = s1.ffi)) /\
        (res1 <> SOME NotEnoughSpace ==>
         case res of
         | NONE => (res1 = NONE)
         | SOME (Rval v) => t1.ffi = s1.ffi /\
                            ?w. (res1 = SOME (Result (Loc l1 l2) w))
         | SOME (Rerr (Rraise v)) => (?v w. res1 = SOME (Exception v w))
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)``,
  gen_tac \\ PairCases_on `x`
  \\ full_simp_tac(srw_ss())[state_rel_ext_def,PULL_EXISTS] \\ srw_tac[][]
  \\ qcase_tac `state_rel x0 l1 l2 s t [] []`
  \\ `(!n v. lookup n t.code = SOME v ==>
             ?x1 x2 x3 x4 x5.
                lookup n l = SOME (SND (full_compile_single x1 x2 x3 x4 ((n,v),x5))))`
        by (full_simp_tac(srw_ss())[] \\ metis_tac [])
  \\ drule compile_word_to_word_thm \\ srw_tac[][]
  \\ drule compile_correct_lemma \\ full_simp_tac(srw_ss())[]
  \\ `state_rel x0 l1 l2 s (t with permute := perm') [] []` by
   (full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[]
    \\ Cases_on `s.stack` \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
  \\ disch_then drule \\ strip_tac
  \\ qexists_tac `clk` \\ full_simp_tac(srw_ss())[]
  \\ qpat_assum `let prog = Call NONE (SOME start) [0] NONE in _` mp_tac
  \\ full_simp_tac(srw_ss())[LET_THM] \\ strip_tac THEN1 (full_simp_tac(srw_ss())[] \\ every_case_tac \\ full_simp_tac(srw_ss())[])
  \\ pairarg_tac \\ full_simp_tac(srw_ss())[] \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[inc_clock_def]
  \\ strip_tac \\ rpt var_eq_tac \\ full_simp_tac(srw_ss())[]
  \\ srw_tac[][] \\ every_case_tac \\ full_simp_tac(srw_ss())[]);

val state_rel_ext_with_clock = prove(
  ``state_rel_ext a b c s1 s2 ==>
    state_rel_ext a b c (s1 with clock := k) (s2 with clock := k)``,
  PairCases_on `a` \\ full_simp_tac(srw_ss())[state_rel_ext_def] \\ srw_tac[][]
  \\ drule state_rel_with_clock
  \\ strip_tac \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `l` \\ full_simp_tac(srw_ss())[]);

(* observational semantics preservation *)

val compile_semantics_lemma = Q.store_thm("compile_semantics_lemma",
  `state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state) (fromAList prog) t.clock) t /\
   semantics ffi (fromAList prog) start <> Fail ==>
   semantics t start IN
     extend_with_resource_limit { semantics ffi (fromAList prog) start }`,
  simp[GSYM AND_IMP_INTRO] >> ntac 1 strip_tac >>
  simp[bvpSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    qx_gen_tac`r`>>simp[]>>strip_tac>>
    strip_tac >>
    simp[wordSemTheory.semantics_def] >>
    IF_CASES_TAC >- (
      full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
      rator_x_assum`bvpSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >>
      drule compile_correct >> simp[] >> full_simp_tac(srw_ss())[] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      impl_tac >- (
        strip_tac >> full_simp_tac(srw_ss())[] ) >>
      drule(GEN_ALL state_rel_ext_with_clock) >>
      disch_then(qspec_then`k'`strip_assume_tac) >> full_simp_tac(srw_ss())[] >>
      disch_then drule >>
      simp[comp_def] >> strip_tac >>
      qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
      Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
      simp[RIGHT_FORALL_IMP_THM] >>
      impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
      disch_then(qspec_then`ck`mp_tac) >>
      fsrw_tac[ARITH_ss][inc_clock_def] >> srw_tac[][] >>
      every_case_tac >> full_simp_tac(srw_ss())[] ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      srw_tac[][extend_with_resource_limit_def] >> full_simp_tac(srw_ss())[] >>
      Cases_on`s.ffi.final_event`>>full_simp_tac(srw_ss())[] >- (
        Cases_on`r'`>>full_simp_tac(srw_ss())[] >> rveq >>
        drule(bvpPropsTheory.evaluate_add_clock)>>simp[]>>
        disch_then(qspec_then`k'`mp_tac)>>simp[]>>strip_tac>>
        drule(compile_correct)>>simp[]>>
        drule(GEN_ALL state_rel_ext_with_clock)>>simp[]>>
        disch_then(qspec_then`k+k'`mp_tac)>>simp[]>>strip_tac>>
        disch_then drule>>
        simp[comp_def]>>strip_tac>>
        `t'.ffi.io_events ≼ t1.ffi.io_events ∧
         (IS_SOME t'.ffi.final_event ⇒ t1.ffi = t'.ffi)` by (
           qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
           Q.ISPECL_THEN[`exps`,`tt`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
           full_simp_tac(srw_ss())[inc_clock_def,Abbr`tt`] >>
           disch_then(qspec_then`k+ck`mp_tac)>>simp[]>>
           fsrw_tac[ARITH_ss][] ) >>
        Cases_on`r = SOME TimeOut` >- (
          every_case_tac >> full_simp_tac(srw_ss())[]>>
          Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] >>
          full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] ) >>
        rator_x_assum`wordSem$evaluate`mp_tac >>
        drule(GEN_ALL wordPropsTheory.evaluate_add_clock) >>
        simp[] >>
        disch_then(qspec_then`ck+k`mp_tac) >>
        simp[inc_clock_def] >> ntac 2 strip_tac >>
        rveq >> full_simp_tac(srw_ss())[] >>
        every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
        full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[] ) >>
      `∃r s'.
        evaluate
          (Call NONE (SOME start) [] NONE, initial_state ffi (fromAList prog) (k + k')) = (r,s') ∧
        s'.ffi = s.ffi` by (
          srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
          metis_tac[bvpPropsTheory.evaluate_add_clock_io_events_mono,SND,
                    initial_state_with_simp,IS_SOME_EXISTS,initial_state_simp]) >>
      drule compile_correct >> simp[] >>
      simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
      impl_tac >- (
        last_x_assum(qspec_then`k+k'`mp_tac)>>srw_tac[][]>>
        strip_tac>>full_simp_tac(srw_ss())[])>>
      drule(GEN_ALL state_rel_ext_with_clock)>>simp[]>>
      disch_then(qspec_then`k+k'`mp_tac)>>simp[]>>strip_tac>>
      disch_then drule>>
      simp[comp_def]>>strip_tac>>
      `t'.ffi.io_events ≼ t1.ffi.io_events ∧
       (IS_SOME t'.ffi.final_event ⇒ t1.ffi = t'.ffi)` by (
        qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
        Q.ISPECL_THEN[`exps`,`tt`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
        full_simp_tac(srw_ss())[inc_clock_def,Abbr`tt`] >>
        disch_then(qspec_then`k+ck`mp_tac)>>simp[]>>
        fsrw_tac[ARITH_ss][] ) >>
      reverse(Cases_on`t'.ffi.final_event`)>>full_simp_tac(srw_ss())[] >- (
        Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>>
        full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        every_case_tac>>full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]>>
        rveq>>full_simp_tac(srw_ss())[]>>
        last_x_assum(qspec_then`k+k'`mp_tac) >> simp[]) >>
      Cases_on`r`>>full_simp_tac(srw_ss())[]>>
      rator_x_assum`wordSem$evaluate`mp_tac >>
      drule(GEN_ALL wordPropsTheory.evaluate_add_clock) >>
      simp[RIGHT_FORALL_IMP_THM] >>
      impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
      disch_then(qspec_then`k+ck`mp_tac) >>
      fsrw_tac[ARITH_ss][inc_clock_def]>> srw_tac[][] >>
      every_case_tac>>full_simp_tac(srw_ss())[]>>rveq>>rev_full_simp_tac(srw_ss())[]>>
      full_simp_tac(srw_ss())[]>>rev_full_simp_tac(srw_ss())[]) >>
    srw_tac[][] >> full_simp_tac(srw_ss())[] >>
    drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
      srw_tac[][] >> strip_tac >> full_simp_tac(srw_ss())[] ) >>
    drule(state_rel_ext_with_clock) >> simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    full_simp_tac(srw_ss())[inc_clock_def] >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    simp[] >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> srw_tac[][]) >>
  srw_tac[][] >>
  simp[wordSemTheory.semantics_def] >>
  IF_CASES_TAC >- (
    full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- ( strip_tac >> full_simp_tac(srw_ss())[] ) >>
    drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
    Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (strip_tac >> full_simp_tac(srw_ss())[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >> srw_tac[][] >>
    every_case_tac >> full_simp_tac(srw_ss())[] ) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    srw_tac[][extend_with_resource_limit_def] >> full_simp_tac(srw_ss())[] >>
    qpat_assum`∀x y. _`(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule(compile_correct)>>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    impl_tac >- (
      strip_tac >> full_simp_tac(srw_ss())[] >>
      last_x_assum(qspec_then`k`mp_tac) >>
      simp[] ) >>
    drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    `t'.ffi.io_events ≼ t1.ffi.io_events ∧
     (IS_SOME t'.ffi.final_event ⇒ t1.ffi = t'.ffi)` by (
      qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
      Q.ISPECL_THEN[`exps`,`tt`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
      full_simp_tac(srw_ss())[inc_clock_def,Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    full_simp_tac(srw_ss())[] >>
    first_assum(qspec_then`k`mp_tac) >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >>
    rator_x_assum`wordSem$evaluate`mp_tac >>
    drule(GEN_ALL wordPropsTheory.evaluate_add_clock)>>
    simp[]>>
    disch_then(qspec_then`ck`mp_tac)>>
    last_x_assum(qspec_then`k`mp_tac) >>
    every_case_tac >> full_simp_tac(srw_ss())[] >> rev_full_simp_tac(srw_ss())[]>>srw_tac[][]>>full_simp_tac(srw_ss())[] >>
    qpat_abbrev_tac`ll = IMAGE _ _` >>
    `lprefix_chain ll` by (
      unabbrev_all_tac >>
      Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
      REWRITE_TAC[IMAGE_COMPOSE] >>
      match_mp_tac prefix_chain_lprefix_chain >>
      simp[prefix_chain_def,PULL_EXISTS] >>
      qx_genl_tac[`k1`,`k2`] >>
      qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
      simp[LESS_EQ_EXISTS] >>
      metis_tac[
        bvpPropsTheory.evaluate_add_clock_io_events_mono,
        bvpPropsTheory.initial_state_with_simp,
        bvpPropsTheory.initial_state_simp]) >>
    drule build_lprefix_lub_thm >>
    simp[lprefix_lub_def] >> strip_tac >>
    match_mp_tac (GEN_ALL LPREFIX_TRANS) >>
    simp[LPREFIX_fromList] >>
    QUANT_TAC[("l2",`fromList x`,[`x`])] >>
    simp[from_toList] >>
    asm_exists_tac >> simp[] >>
    first_x_assum irule >>
    simp[Abbr`ll`] >>
    qexists_tac`k`>>simp[] ) >>
  srw_tac[][extend_with_resource_limit_def] >>
  qmatch_abbrev_tac`build_lprefix_lub l1 = build_lprefix_lub l2` >>
  `(lprefix_chain l1 ∧ lprefix_chain l2) ∧ equiv_lprefix_chain l1 l2`
    suffices_by metis_tac[build_lprefix_lub_thm,lprefix_lub_new_chain,unique_lprefix_lub] >>
  conj_asm1_tac >- (
    UNABBREV_ALL_TAC >>
    conj_tac >>
    Ho_Rewrite.ONCE_REWRITE_TAC[GSYM o_DEF] >>
    REWRITE_TAC[IMAGE_COMPOSE] >>
    match_mp_tac prefix_chain_lprefix_chain >>
    simp[prefix_chain_def,PULL_EXISTS] >>
    qx_genl_tac[`k1`,`k2`] >>
    qspecl_then[`k1`,`k2`]mp_tac LESS_EQ_CASES >>
    simp[LESS_EQ_EXISTS] >>
    metis_tac[
      wordPropsTheory.evaluate_add_clock_io_events_mono,
      EVAL``((t:('a,'ffi) wordSem$state) with clock := k).clock``,
      EVAL``((t:('a,'ffi) wordSem$state) with clock := k) with clock := k2``,
      bvpPropsTheory.evaluate_add_clock_io_events_mono,
      bvpPropsTheory.initial_state_with_simp,
      bvpPropsTheory.initial_state_simp]) >>
  simp[equiv_lprefix_chain_thm] >>
  unabbrev_all_tac >> simp[PULL_EXISTS] >>
  pop_assum kall_tac >>
  simp[LNTH_fromList,PULL_EXISTS] >>
  simp[GSYM FORALL_AND_THM] >>
  rpt gen_tac >>
  reverse conj_tac >> strip_tac >- (
    qmatch_assum_abbrev_tac`n < LENGTH (_ (_ (SND p)))` >>
    Cases_on`p`>>pop_assum(assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule compile_correct >>
    simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>srw_tac[][]>>
      strip_tac >> full_simp_tac(srw_ss())[] ) >>
    drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    qexists_tac`k+ck`>>full_simp_tac(srw_ss())[inc_clock_def]>>
    Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>-(
      first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
      CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
    ntac 2 (pop_assum mp_tac) >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY CASE_TAC >> full_simp_tac(srw_ss())[] >>
    strip_tac >> full_simp_tac(srw_ss())[] >>
    rveq >>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[]) ) >>
  (fn g => subterm (fn tm => Cases_on`^(replace_term(#1(dest_exists(#2 g)))(``k:num``)(assert(has_pair_type)tm))`) (#2 g) g) >>
  drule compile_correct >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  impl_tac >- (
    last_x_assum(qspec_then`k`mp_tac)>>srw_tac[][]>>
    strip_tac >> full_simp_tac(srw_ss())[] ) >>
  drule(state_rel_ext_with_clock) >>
  simp[] >> strip_tac >>
  disch_then drule >>
  simp[comp_def] >> strip_tac >>
  full_simp_tac(srw_ss())[inc_clock_def] >>
  Cases_on`res1=SOME NotEnoughSpace`>>full_simp_tac(srw_ss())[]>-(
    first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
    CASE_TAC >> full_simp_tac(srw_ss())[] ) >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (evaluate (exps,s))).ffi.io_events` >>
  Q.ISPECL_THEN[`exps`,`s`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`ck`mp_tac)>>simp[Abbr`s`]>>strip_tac>>
  qexists_tac`k`>>simp[]>>
  `r.ffi.io_events = t1.ffi.io_events` by (
    ntac 5 (pop_assum mp_tac) >>
    CASE_TAC >> full_simp_tac(srw_ss())[] >>
    every_case_tac >> full_simp_tac(srw_ss())[]>>srw_tac[][]>>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[])) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[]>>
  fsrw_tac[ARITH_ss][IS_PREFIX_APPEND]>>
  simp[EL_APPEND1]);

fun define_abbrev name tm = let
  val vs = free_vars tm |> sort
    (fn v1 => fn v2 => fst (dest_var v1) <= fst (dest_var v2))
  val vars = foldr mk_pair (last vs) (butlast vs)
  val n = mk_var(name,mk_type("fun",[type_of vars, type_of tm]))
  in Define `^n ^vars = ^tm` end

val code_termdep_equiv = prove(
  ``t' with <|code := l; termdep := 0|> = t <=>
    ?x1 x2.
      t.code = l /\ t.termdep = 0 /\ t' = t with <|code := x1; termdep := x2|>``,
  fs [wordSemTheory.state_component_equality] \\ rw [] \\ eq_tac \\ rw [] \\ fs []);

val compile_semantics = save_thm("compile_semantics",let
  val th1 =
    compile_semantics_lemma |> Q.GEN `conf`
    |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO,FORALL_PROD,PULL_EXISTS] |> SPEC_ALL
    |> REWRITE_RULE [state_rel_ext_def]
    |> ONCE_REWRITE_RULE [EQ_SYM_EQ]
    |> SIMP_RULE std_ss [GSYM AND_IMP_INTRO,
         FORALL_PROD,PULL_EXISTS] |> SPEC_ALL
    |> ONCE_REWRITE_RULE [EQ_SYM_EQ]
    |> REWRITE_RULE [ASSUME ``(t:('a,'ffi) wordSem$state).clock =
                              (t':('a,'ffi) wordSem$state).clock``]
    |> (fn th => MATCH_MP th (UNDISCH state_rel_init
            |> Q.INST [`l1`|->`1`,`l2`|->`0`,`code`|->`fromAList prog`,`t`|->`t'`]))
    |> CONV_RULE (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ]))
    |> Q.GENL [`p_1'`,`p_1''`,`p_1'''`,`p_1''''`,`p_2`]
    |> SIMP_RULE std_ss [METIS_PROVE [] ``(!x. P x ==> Q) <=> ((?x. P x) ==> Q)``]
    |> DISCH ``(t':('a,'ffi) wordSem$state).code = code``
    |> SIMP_RULE std_ss [] |> UNDISCH
  val def = define_abbrev "code_rel_ext" (th1 |> concl |> dest_imp |> fst)
  in th1 |> REWRITE_RULE [GSYM def,code_termdep_equiv]
         |> SIMP_RULE std_ss [PULL_EXISTS,PULL_FORALL] |> SPEC_ALL
         |> DISCH_ALL |> GEN_ALL |> SIMP_RULE (srw_ss()) [] |> SPEC_ALL
         |> REWRITE_RULE [AND_IMP_INTRO,GSYM CONJ_ASSOC] end);

val _ = export_theory();
