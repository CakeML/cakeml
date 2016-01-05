open preamble bvlSemTheory bvpSemTheory bvpPropsTheory copying_gcTheory
     int_bitwiseTheory bvp_to_wordPropsTheory finite_mapTheory
     bvp_to_wordTheory wordPropsTheory labPropsTheory whileTheory
     set_sepTheory semanticsPropsTheory word_to_stackTheory;

val _ = new_theory "bvp_to_wordProof";

(* TODO: move *)

val get_var_set_var = store_thm("get_var_set_var[simp]",
  ``get_var n (set_var n w s) = SOME w``,
  fs [wordSemTheory.get_var_def,wordSemTheory.set_var_def]);

val set_var_set_var = store_thm("set_var_set_var[simp]",
  ``set_var n v (set_var n w s) = set_var n v s``,
  fs [wordSemTheory.state_component_equality,wordSemTheory.set_var_def,
      insert_shadow]);

val toAList_LN = Q.store_thm("toAList_LN[simp]",
  `toAList LN = []`,
  EVAL_TAC)

val adjust_set_LN = Q.store_thm("adjust_set_LN[simp]",
  `adjust_set LN = insert 0 () LN`,
  rw[adjust_set_def,fromAList_def]);

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

val ALOOKUP_SKIP_LEMMA = prove(
  ``¬MEM n (MAP FST xs) /\ d = e ==>
    ALOOKUP (xs ++ [(n,d)] ++ ys) n = SOME e``,
  fs [ALOOKUP_APPEND] \\ fs [GSYM ALOOKUP_NONE])

val LAST_EQ = prove(
  ``(LAST (x::xs) = if xs = [] then x else LAST xs) /\
    (FRONT (x::xs) = if xs = [] then [] else x::FRONT xs)``,
  Cases_on `xs` \\ fs []);

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

val NOT_NIL_IMP_LAST = prove(
  ``!xs x. xs <> [] ==> LAST (x::xs) = LAST xs``,
  Cases \\ fs []);

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

val IS_SOME_ALOOKUP_EQ = prove(
  ``!l x. IS_SOME (ALOOKUP l x) = MEM x (MAP FST l)``,
  Induct \\ fs [] \\ Cases \\ fs [ALOOKUP_def] \\ rw []);

val MEM_IMP_IS_SOME_ALOOKUP = prove(
  ``!l x y. MEM (x,y) l ==> IS_SOME (ALOOKUP l x)``,
  fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD] \\ metis_tac []);

val SUBSET_INSERT_EQ_SUBSET = prove(
  ``~(x IN s) ==> (s SUBSET (x INSERT t) <=> s SUBSET t)``,
  fs [EXTENSION]);

val EVERY2_IMP_EL = prove(
  ``!xs ys P n. EVERY2 P xs ys /\ n < LENGTH ys ==> P (EL n xs) (EL n ys)``,
  Induct \\ Cases_on `ys` \\ fs [] \\ rw [] \\ Cases_on `n` \\ fs []);

val FST_PAIR_EQ = prove(
  ``!x v. (FST x,v) = x <=> v = SND x``,
  Cases \\ fs []);

val EVERY2_APPEND_IMP = prove(
  ``!xs1 xs2 zs P.
      EVERY2 P (xs1 ++ xs2) zs ==>
      ?zs1 zs2. zs = zs1 ++ zs2 /\ EVERY2 P xs1 zs1 /\ EVERY2 P xs2 zs2``,
  Induct \\ fs [] \\ rw [] \\ res_tac \\ fs []
  \\ Q.LIST_EXISTS_TAC [`y::zs1`,`zs2`] \\ fs []);

val ZIP_ID = prove(
  ``!xs. ZIP (MAP FST xs, MAP SND xs) = xs``,
  Induct \\ fs []);

(* -- *)

(* -------------------------------------------------------
    word_ml_inv: definition and lemmas
   ------------------------------------------------------- *)

val word_ml_inv_def = Define `
  word_ml_inv (heap,be,a,sp) limit c refs stack <=>
    ?hs. abs_ml_inv (MAP FST stack) refs (hs,heap,be,a,sp) limit /\
         EVERY2 (\v w. word_addr c v = w) hs (MAP SND stack)`

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
  Induct \\ Cases_on `ys` \\ fs [flat_def] \\ rw []
  \\ Cases_on `h'` \\ Cases_on `h`
  \\ TRY (Cases_on `o'`) \\ fs [flat_def]);

val adjust_var_DIV_2 = prove(
  ``(adjust_var n - 2) DIV 2 = n``,
  fs [ONCE_REWRITE_RULE[MULT_COMM]adjust_var_def,MULT_DIV]);

val EVEN_adjust_var = prove(
  ``EVEN (adjust_var n)``,
  fs [adjust_var_def,EVEN_MOD2,ONCE_REWRITE_RULE[MULT_COMM]MOD_TIMES]);

val adjust_var_NEQ_0 = prove(
  ``adjust_var n <> 0``,
  rpt strip_tac \\ fs [adjust_var_def]);

val adjust_var_NEQ_1 = prove(
  ``adjust_var n <> 1``,
  rpt strip_tac
  \\ `EVEN (adjust_var n) = EVEN 1` by fs []
  \\ fs [EVEN_adjust_var]);

val unit_opt_eq = prove(
  ``(x = y:unit option) <=> (IS_SOME x <=> IS_SOME y)``,
  Cases_on `x` \\ Cases_on `y` \\ fs []);

val adjust_var_11 = prove(
  ``(adjust_var n = adjust_var m) <=> n = m``,
  fs [adjust_var_def,EQ_MULT_LCANCEL]);

val lookup_adjust_var_adjust_set = prove(
  ``lookup (adjust_var n) (adjust_set s) = lookup n s``,
  fs [lookup_def,adjust_set_def,lookup_fromAList,unit_opt_eq,adjust_var_NEQ_0]
  \\ fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ fs [MEM_toAList] \\ Cases_on `lookup n s` \\ fs []);

val none_opt_eq = prove(
  ``((x = NONE) = (y = NONE)) <=> (IS_SOME x <=> IS_SOME y)``,
  Cases_on `x` \\ Cases_on `y` \\ fs []);

val lookup_adjust_var_adjust_set_NONE = prove(
  ``lookup (adjust_var n) (adjust_set s) = NONE <=> lookup n s = NONE``,
  fs [lookup_def,adjust_set_def,lookup_fromAList,adjust_var_NEQ_0,none_opt_eq]
  \\ fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ fs [MEM_toAList] \\ Cases_on `lookup n s` \\ fs []);

val lookup_adjust_var_adjust_set_SOME_UNIT = prove(
  ``lookup (adjust_var n) (adjust_set s) = SOME () <=> IS_SOME (lookup n s)``,
  Cases_on `lookup (adjust_var n) (adjust_set s) = NONE`
  \\ pop_assum (fn th => assume_tac th THEN
       assume_tac (SIMP_RULE std_ss [lookup_adjust_var_adjust_set_NONE] th))
  \\ fs [] \\ Cases_on `lookup n s`
  \\ Cases_on `lookup (adjust_var n) (adjust_set s)` \\ fs []);

val word_ml_inv_lookup = prove(
  ``word_ml_inv (heap,be,a,sp) limit c s.refs
      (ys ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs) /\
    lookup n l1 = SOME x /\
    lookup (adjust_var n) l2 = SOME w ==>
    word_ml_inv (heap,be,a,sp) limit c (s:'ffi bvpSem$state).refs
      (ys ++ [(x,w)] ++ join_env l1 (toAList (inter l2 (adjust_set l1))) ++ xs)``,
  fs [toAList_def,foldi_def,LET_DEF]
  \\ fs [GSYM toAList_def] \\ rw []
  \\ `MEM (x,w) (join_env l1 (toAList (inter l2 (adjust_set l1))))` by
   (fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD,MEM_toAList,lookup_inter]
    \\ qexists_tac `adjust_var n` \\ fs [adjust_var_DIV_2,EVEN_adjust_var]
    \\ fs [adjust_var_NEQ_0] \\ every_case_tac
    \\ fs [lookup_adjust_var_adjust_set_NONE])
  \\ fs [MEM_SPLIT] \\ fs [] \\ fs [adjust_var_def]
  \\ qpat_assum `word_ml_inv yyy limit c s.refs xxx` mp_tac
  \\ match_mp_tac word_ml_inv_rearrange \\ fs [MEM] \\ rw [] \\ fs[]);

val word_ml_inv_get_var_IMP = store_thm("word_ml_inv_get_var_IMP",
  ``word_ml_inv (heap,be,a,sp) limit c s.refs
      (join_env s.locals (toAList (inter t.locals (adjust_set s.locals)))++envs) /\
    get_var n s.locals = SOME x /\
    get_var (adjust_var n) t = SOME w ==>
    word_ml_inv (heap,be,a,sp) limit c s.refs
      ([(x,w)]++join_env s.locals
          (toAList (inter t.locals (adjust_set s.locals)))++envs)``,
  rw [] \\ match_mp_tac (word_ml_inv_lookup
             |> Q.INST [`ys`|->`[]`] |> SIMP_RULE std_ss [APPEND])
  \\ fs [get_var_def,wordSemTheory.get_var_def]);

val word_ml_inv_get_vars_IMP = store_thm("word_ml_inv_get_vars_IMP",
  ``!n x w envs.
      word_ml_inv (heap,be,a,sp) limit c s.refs
        (join_env s.locals
           (toAList (inter t.locals (adjust_set s.locals)))++envs) /\
      get_vars n s.locals = SOME x /\
      get_vars (MAP adjust_var n) t = SOME w ==>
      word_ml_inv (heap,be,a,sp) limit c s.refs
        (ZIP(x,w)++join_env s.locals
           (toAList (inter t.locals (adjust_set s.locals)))++envs)``,
  Induct \\ fs [get_vars_def,wordSemTheory.get_vars_def] \\ rpt strip_tac
  \\ every_case_tac \\ fs [] \\ rw []
  \\ imp_res_tac word_ml_inv_get_var_IMP
  \\ Q.MATCH_ASSUM_RENAME_TAC `bvpSem$get_var h s.locals = SOME x7`
  \\ Q.MATCH_ASSUM_RENAME_TAC `_ (adjust_var h) _ = SOME x8`
  \\ `word_ml_inv (heap,be,a,sp) limit c s.refs
        (join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
        (x7,x8)::envs)` by
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

val unit_some_eq_IS_SOME = prove(
  ``!x. (x = SOME ()) <=> IS_SOME x``,
  Cases \\ fs []);

val word_ml_inv_insert = store_thm("word_ml_inv_insert",
  ``word_ml_inv (heap,F,a,sp) limit c s.refs
      ([(x,w)]++join_env d (toAList (inter l (adjust_set d)))++xs) ==>
    word_ml_inv (heap,F,a,sp) limit c s.refs
      (join_env (insert dest x d)
        (toAList (inter (insert (adjust_var dest) w l)
                           (adjust_set (insert dest x d))))++xs)``,
  match_mp_tac word_ml_inv_rearrange \\ fs [] \\ rw [] \\ fs []
  \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [] \\ rw [] \\ fs [MEM_toAList]
  \\ fs [lookup_insert,lookup_inter_alt]
  \\ Cases_on `dest = (p_1 - 2) DIV 2` \\ fs []
  \\ fs [adjust_var_DIV_2]
  \\ imp_res_tac IMP_adjust_var \\ fs []
  \\ fs [domain_lookup] \\ every_case_tac \\ fs []
  \\ rw [] \\ fs [adjust_var_11] \\ fs []
  \\ disj1_tac \\ disj2_tac \\ qexists_tac `p_1` \\ fs [unit_some_eq_IS_SOME]
  \\ fs [adjust_set_def,lookup_fromAList] \\ rfs []
  \\ fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,PULL_EXISTS,EXISTS_PROD,adjust_var_11]
  \\ fs [MEM_toAList,lookup_insert] \\ every_case_tac \\ fs []);

(* -------------------------------------------------------
    definition and verification of GC function
   ------------------------------------------------------- *)

val theWord_def = Define `
  theWord (Word w) = w`

val isWord_def = Define `
  (isWord (Word w) = T) /\ (isWord _ = F)`;

val ptr_to_addr_def = Define `
  ptr_to_addr conf base (w:'a word) =
    base + ((w >>> (conf.pad_bits + conf.len_bits + conf.tag_bits + 2))
            << (dimindex (:'a) DIV 8))`

val is_fwd_ptr_def = Define `
  is_fwd_ptr w = ((w && 3w) = 3w)`;

val update_addr_def = Define `
  update_addr conf fwd_ptr (old_addr:'a word) =
    let n = conf.pad_bits + conf.len_bits + conf.tag_bits + 2 in
    ((dimindex(:'a) - 1) -- n) fwd_ptr ||
    ((n - 1) -- 0) old_addr`

val is_all_ones_def = Define `
  is_all_ones m n w = ((all_ones m n && w) = all_ones m n)`;

val decode_maxout_def = Define `
  decode_maxout l n w =
    if is_all_ones (n+l) n w then NONE else SOME (((n+l) -- n) w >> n)`

val decode_addr_def = Define `
  decode_addr conf w =
    (decode_maxout conf.len_bits (conf.tag_bits + 2) w,
     decode_maxout conf.tag_bits 2 w)`

val has_header_def = Define `
  has_header conf w <=>
    decode_maxout conf.len_bits (conf.tag_bits + 2) w = NONE \/
    decode_maxout conf.tag_bits 2 w = NONE`

val decode_header_def = Define `
  decode_header conf w =
    (w >>> (2 + conf.len_size),
     ((conf.len_size + 1 -- 2) w) >>> 2)`;

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
         if isWord v /\ is_fwd_ptr (theWord v) then
           (Word (update_addr conf (theWord v) w),i,pa,m,c)
         else if has_header conf w then
           let hd_payload_addr = ptr_to_addr conf old w in
           let header_addr = hd_payload_addr - bytes_in_word in
           let v = ((i + 1w) << 2 || 3w) in
           let c = (c /\ header_addr IN dm /\ isWord (m header_addr)) in
           let (_,len) = decode_header conf (theWord (m header_addr)) in
           let i = i + len + 1w in
           let (pa1,m1,c1) = memcpy (len+1w) header_addr pa m dm in
           let c = (c /\ hd_payload_addr IN dm /\ c1) in
           let m1 = (hd_payload_addr =+ Word v) m1 in
             (Word (update_addr conf v w),i,pa1,m1,c)
         else
           let len = THE (SND (decode_addr conf w)) in
           let v = (i << 2 || 3w) in
           let i = i + len in
           let hd_payload_addr = ptr_to_addr conf old w in
           let (pa1,m1,c1) = memcpy len hd_payload_addr pa m dm in
           let c = (c /\ hd_payload_addr IN dm /\ c1) in
           let m1 = (hd_payload_addr =+ Word v) m1 in
             (Word (update_addr conf v w),i,pa1,m1,c))`

val word_gc_move_roots_def = Define `
  (word_gc_move_roots conf ([],i,pa,old,m,dm) = ([],i,pa,m,T)) /\
  (word_gc_move_roots conf (w::ws,i,pa,old,m,dm) =
     let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
     let (ws2,i2,pa2,m2,c2) = word_gc_move_roots conf (ws,i1,pa1,old,m1,dm) in
       (w1::ws2,i2,pa2,m2,c1 /\ c2))`

val word_gc_loop_def = Define `
  word_gc_loop conf k (pb,i,pa,old,m,dm,c) =
    if k = 0n then (i,pa,m,F) else
    if pb = pa then (i,pa,m,c) else
      let c = (c /\ pb IN dm) in
      let w = m pb in
        if isWord w /\ is_fwd_ptr (theWord w) then
          let len = SND (decode_header conf (theWord w)) in
          let pb = pb + (len + 1w) * bytes_in_word in
            word_gc_loop conf (k-1) (pb,i,pa,old,m,dm,c)
        else
          let (w1,i1,pa1,m1,c1) = word_gc_move conf (w,i,pa,old,m,dm) in
          let m1 = (pb =+ w1) m1 in
          let pb = pb + bytes_in_word in
            word_gc_loop conf (k-1) (pb,i1,pa1,old,m1,dm,c /\ c1)`

val word_gc_fun_def = Define `
  (word_gc_fun (conf:bvp_to_word$config)):'a gc_fun_type = \(roots,m,dm,s).
     let c = (Globals IN FDOM s) in
     let new = theWord (s ' OtherHeap) in
     let old = theWord (s ' CurrHeap) in
     let len = theWord (s ' HeapLength) in
     let all_roots = s ' Globals::roots in
     let (roots1,i1,pa1,m1,c1) = word_gc_move_roots conf (all_roots,0w,new,old,m,dm) in
     let (_,pa1,m1,c) = word_gc_loop conf (dimword(:'a)) (new,i1,pa1,old,m1,dm,c1) in
     let s1 = s |++ [(CurrHeap, Word new);
                     (OtherHeap, Word old);
                     (NextFree, Word pa1);
                     (EndOfHeap, Word (new + len));
                     (Globals, HD roots1)] in
       if c then SOME (TL roots1,m1,s1) else NONE`

(*

val word_gc_move_thm = prove(
  ``(gc_move (x,[],a,n,heap,T,limit) = (x1,h1,a1,n1,heap1,T)) /\
    (word_heap curr heap c heap * one_list pa xs) (fun2set (m,dm)) /\
    (word_gc_move conf (word_addr conf heap x,i,pa,old,m,dm) =
      (word_addr conf heap x1,i1,pa1,m1,c1)) ==>
    ?xs1.
      (word_heap curr heap1 c heap *
       word_heap pa h1 c heap *
       one_list pa1 xs1) (fun2set (m,dm)) /\
      c1``,

  reverse (Cases_on `x`) \\ fs [gc_move_def]

    rw [] \\ fs [word_heap_def,SEP_CLAUSES]
    \\ qexists_tac `xs` \\ fs []
    \\ fs [word_addr_def]

word_addr_def
get_addr_def
word_gc_move_def
word_addr_def
gc_forward_ptr_def
gc_move_def
gc_move_list_def
one_list_def
word_heap_def
word_el_def

*)

val heap_in_memory_store_def = Define `
  heap_in_memory_store heap a sp c s m dm limit =
    ?curr other.
      (FLOOKUP s CurrHeap = SOME (Word curr)) /\
      (FLOOKUP s OtherHeap = SOME (Word other)) /\
      (FLOOKUP s NextFree = SOME (Word (curr + bytes_in_word * n2w a))) /\
      (FLOOKUP s EndOfHeap = SOME (Word (curr + bytes_in_word * n2w (a + sp)))) /\
      (word_heap curr heap c *
       word_heap other [Unused (limit-1)] c) (fun2set (m,dm))`

val word_gc_fun_lemma = prove(
  ``heap_in_memory_store heap a sp c s m dm limit /\
    abs_ml_inv (v::MAP FST stack) refs (hs,heap,be,a,sp) limit /\
    LIST_REL (\v w. word_addr c v = w) hs (s ' Globals::MAP SND stack) /\
    full_gc (hs,heap,limit) = (roots2,heap2,heap_length heap2,T) ==>
    let heap1 = heap2 ++ heap_expand (limit - heap_length heap2) in
      ?stack1 m1 s1 a1 sp1.
        word_gc_fun c (MAP SND stack,m,dm,s) = SOME (stack1,m1,s1) /\
        heap_in_memory_store heap1 (heap_length heap2)
          (limit - heap_length heap2) c s1 m1 dm limit /\
        LIST_REL (λv w. word_addr c v = w) roots2
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
        (v1 ++ join_env s.locals (toAList (inter t.locals (adjust_set s.locals))) ++
           [(the_global s.global,t.store ' Globals)] ++
           flat s.stack t.stack) /\
      limit * (dimindex (:'a) DIV 8) + 1 < dimword (:'a) /\
      s.space <= sp`

val state_rel_with_clock = Q.store_thm("state_rel_with_clock",
  `state_rel a b c s1 s2 d e ⇒
   state_rel a b c (s1 with clock := k) (s2 with clock := k) d e`,
  rw[state_rel_def]);

(* -------------------------------------------------------
    compiler proof
   ------------------------------------------------------- *)

val adjust_var_NOT_0 = store_thm("adjust_var_NOT_0[simp]",
  ``adjust_var n <> 0``,
  fs [adjust_var_def]);

val state_rel_get_var_IMP = prove(
  ``state_rel c l1 l2 s t v1 locs ==>
    (get_var n s.locals = SOME x) ==>
    ?w. get_var (adjust_var n) t = SOME w``,
  fs [bvpSemTheory.get_var_def,wordSemTheory.get_var_def]
  \\ fs [state_rel_def] \\ rpt strip_tac
  \\ `IS_SOME (lookup n s.locals)` by fs [] \\ res_tac
  \\ Cases_on `lookup (adjust_var n) t.locals` \\ fs []);

val state_rel_get_vars_IMP = prove(
  ``!n xs.
      state_rel c l1 l2 s t [] locs ==>
      (get_vars n s.locals = SOME xs) ==>
      ?ws. get_vars (MAP adjust_var n) t = SOME ws /\ (LENGTH xs = LENGTH ws)``,
  Induct \\ fs [bvpSemTheory.get_vars_def,wordSemTheory.get_vars_def]
  \\ rpt strip_tac
  \\ Cases_on `get_var h s.locals` \\ fs []
  \\ Cases_on `get_vars n s.locals` \\ fs [] \\ rw []
  \\ imp_res_tac state_rel_get_var_IMP \\ fs []);

val state_rel_0_get_vars_IMP = prove(
  ``state_rel c l1 l2 s t [] locs ==>
    (get_vars n s.locals = SOME xs) ==>
    ?ws. get_vars (0::MAP adjust_var n) t = SOME ((Loc l1 l2)::ws) /\
         (LENGTH xs = LENGTH ws)``,
  rpt strip_tac
  \\ imp_res_tac state_rel_get_vars_IMP
  \\ fs [wordSemTheory.get_vars_def]
  \\ fs [state_rel_def,wordSemTheory.get_var_def]);

val get_var_T_OR_F = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) state) [] locs /\
    get_var n s.locals = SOME x /\
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

val cut_env_IMP_cut_env = prove(
  ``state_rel c l1 l2 s t [] locs /\
    bvpSem$cut_env r s.locals = SOME x ==>
    ?y. wordSem$cut_env (adjust_set r) t.locals = SOME y``,
  fs [bvpSemTheory.cut_env_def,wordSemTheory.cut_env_def]
  \\ fs [adjust_set_def,domain_fromAList,SUBSET_DEF,MEM_MAP,
         PULL_EXISTS,sptreeTheory.domain_lookup,lookup_fromAList] \\ rw []
  \\ Cases_on `x' = 0` \\ fs [] THEN1 fs [state_rel_def]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ fs [unit_some_eq_IS_SOME,IS_SOME_ALOOKUP_EQ,MEM_MAP]
  \\ Cases_on `y'` \\ Cases_on `y''`
  \\ fs [] \\ rw [] \\ fs [adjust_var_11] \\ rw []
  \\ fs [state_rel_def] \\ res_tac
  \\ `IS_SOME (lookup q s.locals)` by fs [] \\ res_tac
  \\ Cases_on `lookup (adjust_var q) t.locals` \\ fs []
  \\ fs [MEM_toAList,unit_some_eq_IS_SOME] \\ res_tac \\ fs []);

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

val state_rel_pop_env_IMP = prove(
  ``state_rel c q l s1 t1 [] locs /\
    pop_env s1 = SOME s2 ==>
    ?t2 l8 l9 ll.
      pop_env t1 = SOME t2 /\ locs = (l8,l9)::ll /\
      state_rel c l8 l9 s2 t2 [] ll``,
  fs [pop_env_def]
  \\ Cases_on `s1.stack` \\ fs [] \\ Cases_on `h` \\ fs []
  \\ rw[] \\ fs [] \\ fs [state_rel_def]
  \\ TRY (Cases_on `y`) \\ fs [stack_rel_def]
  \\ fs [stack_rel_def,wordSemTheory.pop_env_def]
  \\ rfs [] \\ Cases_on `y` \\ fs []
  \\ Cases_on `o'` \\ fs [stack_rel_def,wordSemTheory.pop_env_def]
  \\ rfs [] \\ rw [] \\ Cases_on `y` \\ fs []
  \\ every_case_tac \\ fs []
  \\ TRY (Cases_on `r'`) \\ fs [stack_rel_def]
  \\ fs [lookup_fromAList,contains_loc_def]
  \\ asm_exists_tac \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [flat_def] \\ rw [] \\ fs []
  \\ Cases_on `x` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
  \\ fs [MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

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
  \\ fs [MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

val state_rel_jump_exc = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs /\
    get_var n s.locals = SOME x /\
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
  \\ fs [MEM_toAList,lookup_fromAList,lookup_inter_alt]
  \\ imp_res_tac alistTheory.ALOOKUP_MEM \\ metis_tac []);

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
  ``get_vars args s.locals = SOME q /\
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
  \\ Cases_on `y` \\ fs [MEM_toAList,lookup_inter_alt] \\ rw [MEM_ZIP]
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
    get_vars args s.locals = SOME x /\
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
      get_vars args s.locals = SOME x /\
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

val adjust_var_cut_env_IMP_MEM = prove(
  ``wordSem$cut_env (adjust_set s) r = SOME x ==>
    domain x SUBSET EVEN /\
    (IS_SOME (lookup (adjust_var n) x) <=> IS_SOME (lookup n s))``,
  fs [wordSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ rw [] \\ fs [lookup_inter_alt] THEN1
   (fs [domain_lookup,unit_some_eq_IS_SOME,adjust_set_def]
    \\ fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,lookup_fromAList]
    \\ every_case_tac \\ fs [] \\ rw [] \\ fs [IN_DEF]
    \\ fs [IS_SOME_ALOOKUP_EQ,MEM_MAP,lookup_fromAList]
    \\ split_pair_tac \\ rw [] \\ fs [EVEN_adjust_var])
  \\ fs [domain_lookup,lookup_adjust_var_adjust_set_SOME_UNIT] \\ rw []
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
  \\ rpt strip_tac \\ TRY
   (imp_res_tac adjust_var_cut_env_IMP_MEM
    \\ fs [domain_lookup,SUBSET_DEF,PULL_EXISTS]
    \\ fs [EVERY_MEM,FORALL_PROD] \\ ntac 3 strip_tac
    \\ res_tac \\ res_tac \\ fs [IN_DEF] \\ rw [] \\ strip_tac
    \\ rw [] \\ fs [] \\ rfs [isWord_def] \\ NO_TAC)
  \\ first_assum (match_exists_tac o concl) \\ fs [] (* asm_exists_tac *)
  \\ fs [flat_def]
  \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
  \\ imp_res_tac word_ml_inv_get_vars_IMP
  \\ first_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ rw [] \\ fs[]
  \\ TRY (rpt disj1_tac
    \\ Cases_on `x'` \\ fs [join_env_def,MEM_MAP,MEM_FILTER,EXISTS_PROD]
    \\ fs [MEM_toAList] \\ rw [MEM_ZIP]
    \\ fs [lookup_fromList2,lookup_fromList,lookup_inter_alt]
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
  \\ fs [lookup_fromList2,lookup_fromList,lookup_inter_alt]
  \\ Q.MATCH_ASSUM_RENAME_TAC `EVEN k`
  \\ qexists_tac `k` \\ fs [] \\ res_tac \\ rw []
  \\ imp_res_tac cut_env_IMP_lookup \\ fs []
  \\ TRY (AP_TERM_TAC \\ match_mp_tac cut_env_IMP_lookup_EQ) \\ fs []
  \\ fs [domain_lookup] \\ imp_res_tac MEM_IMP_IS_SOME_ALOOKUP \\ rfs[]
  \\ imp_res_tac cut_env_res_IS_SOME_IMP
  \\ fs [IS_SOME_EXISTS]
  \\ fs [adjust_set_def,lookup_fromAList] \\ rfs []
  \\ imp_res_tac alistTheory.ALOOKUP_MEM
  \\ fs [unit_some_eq_IS_SOME,IS_SOME_ALOOKUP_EQ,MEM_MAP,EXISTS_PROD]
  \\ rw [adjust_var_11,adjust_var_DIV_2]
  \\ imp_res_tac MEM_toAList \\ fs []
  \\ fs [bvpSemTheory.cut_env_def,SUBSET_DEF,domain_lookup]
  \\ res_tac \\ fs [MEM_toAList]);

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
  ``evaluate (c,call_env (args1:'a word_loc list) (push_env y (opt:(num # ('a wordLang$prog) # num # num) option) (dec_clock t))) =
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

val inc_clock_def = Define `
  inc_clock n (t:('a,'ffi) wordSem$state) = t with clock := t.clock + n`;

val inc_clock_0 = store_thm("inc_clock_0[simp]",
  ``!t. inc_clock 0 t = t``,
  fs [inc_clock_def,wordSemTheory.state_component_equality]);

val inc_clock_inc_clock = store_thm("inc_clock_inc_clock[simp]",
  ``!t. inc_clock n (inc_clock m t) = inc_clock (n+m) t``,
  fs [inc_clock_def,wordSemTheory.state_component_equality,AC ADD_ASSOC ADD_COMM]);

val mk_loc_jmup_exc_inc_clock = store_thm("mk_loc_jmup_exc_inc_clock[simp]",
  ``mk_loc (jump_exc (inc_clock ck t)) = mk_loc (jump_exc t)``,
  fs [mk_loc_def,wordSemTheory.jump_exc_def,inc_clock_def]
  \\ every_case_tac \\ fs [mk_loc_def]);

val jump_exc_inc_clock_EQ_NONE = prove(
  ``jump_exc (inc_clock n s) = NONE <=> jump_exc s = NONE``,
  fs [mk_loc_def,wordSemTheory.jump_exc_def,inc_clock_def]
  \\ every_case_tac \\ fs [mk_loc_def]);

val assign_thm = prove(
  ``state_rel c l1 l2 s (t:('a,'ffi) wordSem$state) [] locs /\
    (op_space_reset op ==> names_opt <> NONE) /\
    cut_state_opt names_opt s = SOME x /\
    get_vars args x.locals = SOME vals /\
    do_app op vals x = Rval (v,s2) ==>
    ?ck q r.
      evaluate (FST (assign c n l dest op args names_opt),inc_clock ck t) = (q,r) /\
      (q = SOME NotEnoughSpace ==> r.ffi = t.ffi) /\
      (q <> SOME NotEnoughSpace ==>
      state_rel c l1 l2 (set_var dest v s2) r [] locs /\ q = NONE)``,
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
  alloc_size k = (if k * (dimindex (:'a) DIV 8) < dimword (:α) then
                    n2w (k * (dimindex (:'a) DIV 8))
                  else (-1w)):'a word`

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

val inter_insert = store_thm("inter_insert",
  ``inter (insert n x t1) t2 =
    if n IN domain t2 then insert n x (inter t1 t2) else inter t1 t2``,
  rw [] \\ fs [spt_eq_thm,wf_inter,wf_insert,lookup_inter_alt,lookup_insert]
  \\ rw [] \\ fs []);

val lookup_1_adjust_set = prove(
  ``lookup 1 (adjust_set l) = NONE``,
  fs [adjust_set_def,lookup_fromAList,ALOOKUP_NONE,MEM_MAP,FORALL_PROD]
  \\ fs [adjust_var_def] \\ CCONTR_TAC \\ fs [] \\ decide_tac);

val state_rel_insert_1 = prove(
  ``state_rel c l1 l2 s (t with locals := insert 1 x t.locals) v locs =
    state_rel c l1 l2 s t v locs``,
  fs [state_rel_def] \\ eq_tac \\ rw []
  \\ fs [lookup_insert,adjust_var_NEQ_1]
  \\ fs [inter_insert,domain_lookup,lookup_1_adjust_set]
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

val word_gc_move_IMP_isWord = prove(
  ``word_gc_move c' (Word c,i,pa,old,m,dm) = (w1,i1,pa1,m1,c1) ==> isWord w1``,
  fs [word_gc_move_def,LET_DEF]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ rw [] \\ fs [isWord_def]);

val word_gc_move_roots_IMP_FILTER = prove(
  ``!ws i pa old m dm ws2 i2 pa2 m2 c2 c.
      word_gc_move_roots c (ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) ==>
      word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) =
                           (FILTER isWord ws2,i2,pa2,m2,c2)``,
  Induct \\ fs [word_gc_move_roots_def] \\ Cases \\ fs []
  \\ rw [] \\ fs [word_gc_move_roots_def]
  THEN1
   (rw [] \\ fs [LET_DEF] \\ imp_res_tac word_gc_move_IMP_isWord
    \\ Cases_on `word_gc_move_roots c' (ws,i1,pa1,old,m1,dm)` \\ fs []
    \\ PairCases_on `r` \\ fs [] \\ res_tac \\ rw [] \\ fs [] \\ rw [])
  \\ fs [isWord_def,word_gc_move_def,LET_DEF]
  \\ Cases_on `word_gc_move_roots c (ws,i,pa,old,m,dm)`
  \\ PairCases_on `r` \\ fs [] \\ rw [] \\ fs [isWord_def]);

val IMP_EQ_DISJ = METIS_PROVE [] ``(b1 ==> b2) <=> ~b1 \/ b2``

val word_gc_fun_IMP_FILTER = prove(
  ``word_gc_fun c (xs,m,dm,s) = SOME (stack1,m1,s1) ==>
    word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (FILTER isWord stack1,m1,s1)``,
  fs [IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ fs [GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ UNABBREV_ALL_TAC \\ fs [] \\ rw []
  \\ fs [word_gc_move_roots_def]
  \\ Cases_on `word_gc_move c (s ' Globals,0w,theWord (s ' OtherHeap),
                               theWord (s ' CurrHeap),m,dm)` \\ fs []
  \\ PairCases_on `r` \\ fs [LET_DEF]
  \\ Cases_on `word_gc_move_roots c (xs,r0,r1,theWord (s ' CurrHeap),r2,dm)`
  \\ PairCases_on `r` \\ fs [LET_DEF]
  \\ imp_res_tac word_gc_move_roots_IMP_FILTER
  \\ fs [] \\ rw [] \\ rfs [] \\ fs [])

val loc_merge_def = Define `
  (loc_merge [] ys = []) /\
  (loc_merge (Loc l1 l2::xs) ys = Loc l1 l2::loc_merge xs ys) /\
  (loc_merge (Word w::xs) (y::ys) = y::loc_merge xs ys) /\
  (loc_merge (Word w::xs) [] = Word w::xs)`

val LENGTH_loc_merge = prove(
  ``!xs ys. LENGTH (loc_merge xs ys) = LENGTH xs``,
  Induct \\ Cases_on `ys` \\ fs [loc_merge_def]
  \\ Cases_on `h` \\ fs [loc_merge_def]
  \\ Cases_on `h'` \\ fs [loc_merge_def]);

val word_gc_move_roots_IMP_FILTER = prove(
  ``!ws i pa old m dm ws2 i2 pa2 m2 c2 c.
      word_gc_move_roots c (FILTER isWord ws,i,pa,old,m,dm) = (ws2,i2,pa2,m2,c2) ==>
      word_gc_move_roots c (ws,i,pa,old,m,dm) =
                           (loc_merge ws ws2,i2,pa2,m2,c2)``,
  Induct \\ fs [word_gc_move_roots_def,loc_merge_def]
  \\ reverse Cases \\ fs [isWord_def,loc_merge_def,LET_DEF]
  THEN1
   (fs [word_gc_move_def] \\ rw []
    \\ Cases_on `word_gc_move_roots c (ws,i,pa,old,m,dm)` \\ fs[]
    \\ PairCases_on `r` \\ fs [] \\ res_tac \\ fs [])
  \\ fs [word_gc_move_roots_def,loc_merge_def] \\ rw []
  \\ Cases_on `word_gc_move c' (Word c,i,pa,old,m,dm)`
  \\ PairCases_on `r` \\ fs [] \\ res_tac \\ fs [LET_DEF]
  \\ Cases_on `word_gc_move_roots c' (FILTER isWord ws,r0,r1,old,r2,dm)`
  \\ PairCases_on `r` \\ fs [] \\ res_tac \\ fs [LET_DEF] \\ fs []
  \\ rw [] \\ fs [loc_merge_def]);

val word_gc_fun_loc_merge = prove(
  ``word_gc_fun c (FILTER isWord xs,m,dm,s) = SOME (ys,m1,s1) ==>
    word_gc_fun c (xs,m,dm,s) = SOME (loc_merge xs ys,m1,s1)``,
  fs [IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ fs [GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ UNABBREV_ALL_TAC \\ fs [] \\ rw []
  \\ fs [word_gc_move_roots_def]
  \\ Cases_on `word_gc_move c (s ' Globals,0w,theWord (s ' OtherHeap),
                               theWord (s ' CurrHeap),m,dm)` \\ fs []
  \\ PairCases_on `r` \\ fs [LET_DEF]
  \\ Cases_on `word_gc_move_roots c (FILTER isWord xs,r0,r1,theWord (s ' CurrHeap),r2,dm)`
  \\ PairCases_on `r` \\ fs [LET_DEF]
  \\ imp_res_tac word_gc_move_roots_IMP_FILTER
  \\ fs [] \\ rw [] \\ fs []);

val word_gc_fun_IMP = prove(
  ``word_gc_fun c (xs,m,dm,s) = SOME (ys,m1,s1) ==>
    FLOOKUP s1 AllocSize = FLOOKUP s AllocSize /\
    FLOOKUP s1 Handler = FLOOKUP s Handler /\
    Globals IN FDOM s1``,
  fs [IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ fs [GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ UNABBREV_ALL_TAC \\ fs [] \\ rw []
  \\ EVAL_TAC)

val word_gc_move_roots_IMP_EVERY2 = prove(
  ``!xs ys pa m i c1 m1 pa1 i1 old dm c.
      word_gc_move_roots c (xs,i,pa,old,m,dm) = (ys,i1,pa1,m1,c1) ==>
      EVERY2 (\x y. (isWord x <=> isWord y) /\ (~isWord x ==> x = y)) xs ys``,
  Induct \\ fs [word_gc_move_roots_def]
  \\ fs [IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw []
  \\ fs [GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ rw [] \\ res_tac
  \\ qpat_assum `word_gc_move c (h,i,pa,old,m,dm) = (w1,i1',pa1',m1',c1')` mp_tac
  \\ fs [] \\ Cases_on `h` \\ fs [word_gc_move_def] \\ rw []
  \\ CCONTR_TAC \\ fs [] \\ rw [] \\ fs [isWord_def]
  \\ UNABBREV_ALL_TAC \\ rw [] \\ pop_assum mp_tac \\ fs []
  \\ rw [] \\ CCONTR_TAC \\ fs[] \\ rw [] \\ fs [isWord_def]);

val word_gc_IMP_EVERY2 = prove(
  ``word_gc_fun c (xs,m,dm,st) = SOME (ys,m1,s1) ==>
    EVERY2 (\x y. (isWord x <=> isWord y) /\ (~isWord x ==> x = y)) xs ys``,
  fs [IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ fs [GSYM IMP_EQ_DISJ,word_gc_fun_def] \\ rw []
  \\ Q.UNABBREV_TAC `all_roots`
  \\ imp_res_tac word_gc_move_roots_IMP_EVERY2
  \\ Cases_on `roots1` \\ fs []
  \\ fs [IMP_EQ_DISJ,word_gc_fun_def] \\ rw []);

val word_gc_fun_LENGTH = prove(
  ``word_gc_fun c (xs,m,dm,s) = SOME (zs,m1,s1) ==> LENGTH xs = LENGTH zs``,
  rw [] \\ drule word_gc_IMP_EVERY2 \\ rw [] \\ imp_res_tac EVERY2_LENGTH);

val word_gc_fun_APPEND_IMP = prove(
  ``word_gc_fun c (xs ++ ys,m,dm,s) = SOME (zs,m1,s1) ==>
    ?zs1 zs2. zs = zs1 ++ zs2 /\ LENGTH xs = LENGTH zs1 /\ LENGTH ys = LENGTH zs2``,
  rw [] \\ imp_res_tac word_gc_fun_LENGTH \\ fs [LENGTH_APPEND]
  \\ pop_assum mp_tac \\ pop_assum (K all_tac)
  \\ qspec_tac (`zs`,`zs`) \\ qspec_tac (`ys`,`ys`) \\ qspec_tac (`xs`,`xs`)
  \\ Induct \\ fs [] \\ Cases_on `zs` \\ fs [LENGTH_NIL] \\ rw []
  \\ once_rewrite_tac [EQ_SYM_EQ] \\ fs [LENGTH_NIL]
  \\ fs [ADD_CLAUSES] \\ res_tac
  \\ fs [] \\ Q.LIST_EXISTS_TAC [`h::zs1`,`zs2`] \\ fs []);

val IMP_loc_merge_APPEND = prove(
  ``!ts qs xs ys.
      LENGTH (FILTER isWord ts) = LENGTH qs ==>
      loc_merge (ts ++ xs) (qs ++ ys) = loc_merge ts qs ++ loc_merge xs ys``,
  Induct \\ fs [] THEN1 (Cases_on `qs` \\ fs [LENGTH,loc_merge_def])
  \\ Cases \\ fs [isWord_def,loc_merge_def]
  \\ Cases \\ fs [loc_merge_def]) |> SPEC_ALL;

val TAKE_DROP_loc_merge_APPEND = prove(
  ``TAKE (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = loc_merge (MAP SND q) xs /\
    DROP (LENGTH q) (loc_merge (MAP SND q) xs ++ ys) = ys``,
  `LENGTH q = LENGTH (loc_merge (MAP SND q) xs)` by fs [LENGTH_loc_merge]
  \\ fs [TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND]);

val loc_merge_NIL = prove(
  ``!xs. loc_merge xs [] = xs``,
  Induct \\ fs [loc_merge_def] \\ Cases \\ fs [loc_merge_def]);

val loc_merge_APPEND = prove(
  ``!xs1 xs2 ys.
      ?zs1 zs2. loc_merge (xs1 ++ xs2) ys = zs1 ++ zs2 /\
                LENGTH zs1 = LENGTH xs1 /\ LENGTH xs2 = LENGTH xs2 /\
                ?ts. loc_merge xs2 ts = zs2``,
  Induct \\ fs [loc_merge_def,LENGTH_NIL,LENGTH_loc_merge] THEN1 (metis_tac [])
  \\ Cases THEN1
   (Cases_on `ys` \\ fs [loc_merge_def] \\ rw []
    THEN1 (Q.LIST_EXISTS_TAC [`Word c::xs1`,`xs2`] \\ fs []
           \\ qexists_tac `[]` \\ fs [loc_merge_NIL])
    \\ pop_assum (qspecl_then [`xs2`,`t`] strip_assume_tac)
    \\ fs [] \\ Q.LIST_EXISTS_TAC [`h::zs1`,`zs2`] \\ fs [] \\ metis_tac [])
  \\ rw [] \\ fs [loc_merge_def]
  \\ pop_assum (qspecl_then [`xs2`,`ys`] strip_assume_tac)
  \\ fs [] \\ Q.LIST_EXISTS_TAC [`Loc n n0::zs1`,`zs2`] \\ fs [] \\ metis_tac [])

val EVERY2_loc_merge = prove(
  ``!xs ys. EVERY2 (\x y. (isWord y ==> isWord x) /\
                          (~isWord x ==> x = y)) xs (loc_merge xs ys)``,
  Induct \\ fs [loc_merge_def,LENGTH_NIL,LENGTH_loc_merge] \\ Cases
  \\ fs [loc_merge_def] \\ Cases_on `ys`
  \\ fs [loc_merge_def,GSYM EVERY2_refl,isWord_def])

val dec_stack_loc_merge_enc_stack = prove(
  ``!xs ys. ?ss. dec_stack (loc_merge (enc_stack xs) ys) xs = SOME ss``,
  Induct \\ fs [wordSemTheory.enc_stack_def,
    loc_merge_def,wordSemTheory.dec_stack_def]
  \\ Cases \\ Cases_on `o'` \\ fs [] \\ TRY (PairCases_on `x`)
  \\ fs [wordSemTheory.enc_stack_def] \\ rw []
  \\ qspecl_then [`MAP SND l`,`enc_stack xs`,`ys`] mp_tac loc_merge_APPEND
  \\ rw [] \\ fs [] \\ fs [wordSemTheory.dec_stack_def]
  \\ pop_assum (fn th => fs [GSYM th])
  \\ fs [DROP_LENGTH_APPEND]
  \\ first_assum (qspec_then `ts` strip_assume_tac) \\ fs []
  \\ decide_tac);

val ALOOKUP_ZIP = prove(
  ``!l zs1.
      ALOOKUP l (0:num) = SOME (Loc q r) /\
      LIST_REL (λx y. (isWord y ⇒ isWord x) ∧
        (¬isWord x ⇒ x = y)) (MAP SND l) zs1 ==>
      ALOOKUP (ZIP (MAP FST l,zs1)) 0 = SOME (Loc q r)``,
  Induct \\ fs [] \\ Cases \\ fs [ALOOKUP_def,PULL_EXISTS]
  \\ Cases_on `q' = 0` \\ fs [] \\ rw [] \\ fs [isWord_def] \\ rw []);

val stack_rel_dec_stack_IMP_stack_rel = prove(
  ``!xs ys ts stack locs.
      LIST_REL stack_rel ts xs /\ LIST_REL contains_loc xs locs /\
      dec_stack (loc_merge (enc_stack xs) ys) xs = SOME stack ==>
      LIST_REL stack_rel ts stack /\ LIST_REL contains_loc stack locs``,
  Induct_on `ts` \\ Cases_on `xs` \\ fs []
  THEN1 (fs [wordSemTheory.enc_stack_def,loc_merge_def,wordSemTheory.dec_stack_def])
  \\ fs [PULL_EXISTS] \\ rw []
  \\ Cases_on `h` \\ Cases_on `o'` \\ TRY (PairCases_on `x`) \\ fs []
  \\ fs [wordSemTheory.enc_stack_def,wordSemTheory.dec_stack_def]
  \\ qspecl_then [`MAP SND l`,`enc_stack t`,`ys`] mp_tac loc_merge_APPEND
  \\ rw [] \\ fs []
  \\ pop_assum (fn th => fs [GSYM th] THEN assume_tac th)
  \\ fs [DROP_LENGTH_APPEND,TAKE_LENGTH_APPEND]
  \\ every_case_tac \\ fs []
  \\ pop_assum (fn th => fs [GSYM th])
  \\ res_tac \\ fs []
  \\ Cases_on `h'` \\ fs [stack_rel_def]
  \\ fs [lookup_fromAList,IS_SOME_ALOOKUP_EQ]
  \\ fs [EVERY_MEM,FORALL_PROD] \\ Cases_on `y`
  \\ fs [contains_loc_def]
  \\ qspecl_then [`MAP SND l ++ enc_stack t`,`ys`] mp_tac EVERY2_loc_merge
  \\ fs [] \\ strip_tac
  \\ `LENGTH (MAP SND l) = LENGTH zs1` by fs []
  \\ imp_res_tac LIST_REL_APPEND_IMP \\ fs [MAP_ZIP]
  \\ fs [AND_IMP_INTRO]
  \\ `ALOOKUP (ZIP (MAP FST l,zs1)) 0 = SOME (Loc q r)` by
   (`LENGTH (MAP SND l) = LENGTH zs1` by fs []
    \\ imp_res_tac LIST_REL_APPEND_IMP \\ fs [MAP_ZIP]
    \\ imp_res_tac ALOOKUP_ZIP \\ fs [] \\ NO_TAC)
  \\ fs [] \\ NTAC 3 strip_tac \\ first_x_assum match_mp_tac
  \\ rfs [MEM_ZIP] \\ rw [] \\ fs [EL_MAP]
  \\ Q.MATCH_ASSUM_RENAME_TAC `isWord (EL k zs1)`
  \\ fs [MEM_EL,PULL_EXISTS] \\ asm_exists_tac \\ fs []
  \\ fs [FST_PAIR_EQ]
  \\ imp_res_tac EVERY2_IMP_EL \\ rfs [EL_MAP]);

val join_env_NIL = prove(
  ``join_env s [] = []``,
  fs [join_env_def]);

val join_env_CONS = prove(
  ``join_env s ((n,v)::xs) =
    if n <> 0 /\ EVEN n then
      (THE (lookup ((n - 2) DIV 2) s),v)::join_env s xs
    else join_env s xs``,
  fs [join_env_def] \\ rw []);

val FILTER_enc_stack_lemma = prove(
  ``!xs ys.
      LIST_REL stack_rel xs ys ==>
      FILTER isWord (MAP SND (flat xs ys)) =
      FILTER isWord (enc_stack ys)``,
  Induct \\ Cases_on `ys`
  \\ fs [stack_rel_def,wordSemTheory.enc_stack_def,flat_def]
  \\ Cases \\ Cases_on `h` \\ fs [] \\ Cases_on `o'`
  \\ TRY (PairCases_on `x`) \\ fs [stack_rel_def] \\ rw []
  \\ fs [wordSemTheory.enc_stack_def,flat_def,FILTER_APPEND]
  \\ qpat_assum `EVERY (\(x1,x2). isWord x2 ==> x1 <> 0 /\ EVEN x1) l` mp_tac
  \\ rpt (pop_assum (K all_tac))
  \\ Induct_on `l` \\ fs [] \\ fs [join_env_NIL]
  \\ Cases \\ fs [join_env_CONS] \\ rw []);

val stack_rel_simp = prove(
  ``(stack_rel (Env s) y <=>
     ?vs. stack_rel (Env s) y /\ (y = StackFrame vs NONE)) /\
    (stack_rel (Exc s n) y <=>
     ?vs x1 x2 x3. stack_rel (Exc s n) y /\ (y = StackFrame vs (SOME (x1,x2,x3))))``,
  Cases_on `y` \\ fs [stack_rel_def] \\ Cases_on `o'`
  \\ fs [stack_rel_def] \\ PairCases_on `x`
  \\ fs [stack_rel_def,CONJ_ASSOC]);

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
  \\ Cases_on `h` \\ simp [] \\ fs []
  \\ Cases_on `r` \\ fs [isWord_def]
  \\ fs [loc_merge_def] \\ fs [join_env_CONS] \\ rfs [] \\ rw []
  \\ fs [] \\ rw [] \\ rfs[isWord_def] \\ fs []
  \\ Cases_on `y` \\ fs [loc_merge_def,join_env_CONS,isWord_def]);

val LENGTH_MAP_SND_join_env_IMP = prove(
  ``!vs zs1 s.
      LIST_REL (\x y. (isWord x = isWord y) /\ (~isWord x ==> x = y))
        (MAP SND (join_env s vs)) zs1 /\
      EVERY (\(x1,x2). isWord x2 ==> x1 <> 0 /\ EVEN x1) vs /\
      LENGTH (join_env s vs) = LENGTH zs1 ==>
      LENGTH (FILTER isWord (MAP SND vs)) = LENGTH (FILTER isWord zs1)``,
  Induct \\ rpt strip_tac THEN1
   (pop_assum mp_tac \\ simp [join_env_NIL]
    \\ Cases_on `zs1` \\ fs [] \\ rw [])
  \\ Cases_on `h` \\ fs [join_env_CONS] \\ rw []
  THEN1 (fs [] \\ rfs[] \\ first_assum match_mp_tac \\ metis_tac[])
  \\ fs [] \\ Cases_on `q <> 0 /\ EVEN q`
  \\ fs [] \\ rw [] \\ fs [] \\ metis_tac [])

val lemma1 = prove(``(y1 = y2) /\ (x1 = x2) ==> (f x1 y1 = f x2 y2)``,fs []);

val word_gc_fun_EL_lemma = prove(
  ``!xs ys stack1 m dm st m1 s1 stack.
      LIST_REL stack_rel xs stack /\
      EVERY2 (\x y. isWord x = isWord y /\ (~isWord x ==> x = y))
         (MAP SND (flat xs ys)) stack1 /\
      dec_stack (loc_merge (enc_stack ys) (FILTER isWord stack1)) ys =
        SOME stack /\ LIST_REL stack_rel xs ys ==>
      (flat xs stack =
       ZIP (MAP FST (flat xs ys),stack1))``,
  Induct THEN1 (EVAL_TAC \\ fs [] \\ EVAL_TAC \\ rw [] \\ rw [flat_def])
  \\ Cases_on `h` \\ fs [] \\ once_rewrite_tac [stack_rel_simp]
  \\ fs [PULL_EXISTS,stack_rel_def,flat_def,wordSemTheory.enc_stack_def]
  \\ rw [] \\ imp_res_tac EVERY2_APPEND_IMP \\ rw []
  \\ fs [FILTER_APPEND]
  \\ `LENGTH (FILTER isWord (MAP SND vs')) = LENGTH (FILTER isWord zs1)` by
   (imp_res_tac EVERY2_LENGTH \\ fs []
    \\ imp_res_tac LENGTH_MAP_SND_join_env_IMP)
  \\ imp_res_tac IMP_loc_merge_APPEND \\ fs []
  \\ qpat_assum `dec_stack xx dd = SOME yy` mp_tac
  \\ fs [wordSemTheory.dec_stack_def]
  \\ fs [TAKE_DROP_loc_merge_APPEND,LENGTH_loc_merge,DECIDE ``~(n+m<n:num)``]
  \\ CASE_TAC \\ rw [] \\ fs []
  \\ fs [flat_def] \\ imp_res_tac EVERY2_LENGTH \\ fs [GSYM ZIP_APPEND]
  \\ match_mp_tac lemma1
  \\ rpt strip_tac \\ TRY (first_x_assum match_mp_tac \\ fs [])
  \\ TRY (match_mp_tac join_env_EQ_ZIP) \\ fs []) |> SPEC_ALL;

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
  fs [state_rel_def] \\ rw [] \\ rfs [] \\ fs [] \\ rfs[lookup_def] \\ rw []
  \\ qpat_assum `word_ml_inv (heap,F,a,sp) limit c s.refs xxx` mp_tac
  \\ Q.PAT_ABBREV_TAC `pat = join_env LN _` \\ rw []
  \\ `pat = []` by (UNABBREV_ALL_TAC \\ EVAL_TAC) \\ fs []
  \\ rfs [] \\ fs [] \\ pop_assum (K all_tac)
  \\ first_x_assum (fn th1 => first_x_assum (fn th2 =>
       mp_tac (MATCH_MP word_gc_fun_correct (CONJ th1 th2))))
  \\ rw [] \\ fs []
  \\ imp_res_tac word_gc_fun_IMP_FILTER
  \\ imp_res_tac FILTER_enc_stack_lemma \\ fs []
  \\ imp_res_tac word_gc_fun_loc_merge \\ fs [FILTER_APPEND]
  \\ imp_res_tac word_gc_fun_IMP \\ fs []
  \\ `?stack. dec_stack (loc_merge (enc_stack t.stack) (FILTER isWord stack1))
        t.stack = SOME stack` by metis_tac [dec_stack_loc_merge_enc_stack]
  \\ asm_exists_tac \\ fs []
  \\ imp_res_tac stack_rel_dec_stack_IMP_stack_rel \\ fs []
  \\ asm_exists_tac \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [MEM] \\ rw [] \\ fs [] \\ disj2_tac
  \\ pop_assum mp_tac
  \\ match_mp_tac (METIS_PROVE [] ``x=y==>(x==>y)``)
  \\ AP_TERM_TAC
  \\ AP_TERM_TAC
  \\ match_mp_tac (GEN_ALL word_gc_fun_EL_lemma)
  \\ imp_res_tac word_gc_IMP_EVERY2 \\ fs []);

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
  rw [] \\ fs [LET_DEF]
  \\ Q.UNABBREV_TAC `t0` \\ fs []
  \\ imp_res_tac (state_rel_call_env_push_env
      |> Q.SPEC `NONE` |> Q.INST [`args`|->`[]`] |> GEN_ALL
      |> SIMP_RULE std_ss [MAP,get_vars_def,wordSemTheory.get_vars_def]
      |> SPEC_ALL |> REWRITE_RULE [GSYM AND_IMP_INTRO]
      |> (fn th => MATCH_MP th (UNDISCH state_rel_inc_clock))
      |> SIMP_RULE (srw_ss()) [dec_clock_inc_clock] |> DISCH_ALL) \\ fs []
  \\ pop_assum (qspecl_then [`l1`,`l2`] mp_tac) \\ rw []
  \\ pop_assum (mp_tac o MATCH_MP state_rel_gc)
  \\ discharge_hyps THEN1
   (fs [wordSemTheory.call_env_def,call_env_def,
        wordSemTheory.push_env_def,fromList_def]
    \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF]
    \\ fs [fromList2_def,Once insert_def])
  \\ rw [] \\ fs [wordSemTheory.call_env_def]
  \\ pop_assum (mp_tac o MATCH_MP
      (state_rel_pop_env_IMP |> REWRITE_RULE [GSYM AND_IMP_INTRO]
         |> Q.GEN `s2`)) \\ rw []
  \\ pop_assum (qspec_then `s with <| locals := x ; space := 0 |>` mp_tac)
  \\ discharge_hyps THEN1
   (fs [pop_env_def,push_env_def,call_env_def,
      bvpSemTheory.state_component_equality])
  \\ rw [] \\ fs []
  \\ fs [wordSemTheory.pop_env_def,wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []);

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
  fs [wordSemTheory.gc_def,wordSemTheory.call_env_def,LET_DEF,
      wordSemTheory.push_env_def]
  \\ Cases_on `env_to_list y t5.permute` \\ fs [LET_DEF]
  \\ every_case_tac \\ fs [] \\ rw [] \\ fs []
  \\ fs [wordSemTheory.pop_env_def]);

val word_ml_inv_SP_LIMIT = prove(
  ``word_ml_inv (heap,be,a,sp) limit c refs stack ==> sp <= limit``,
  rw [] \\ Cases_on `sp = 0`
  \\ fs [word_ml_inv_def,abs_ml_inv_def,heap_ok_def,unused_space_inv_def]
  \\ imp_res_tac heap_lookup_SPLIT \\ rw []
  \\ fs [heap_length_APPEND,heap_length_def,el_length_def] \\ decide_tac);

val has_space_state_rel = prove(
  ``has_space (Word ((alloc_size k):'a word)) (r:('a,'ffi) state) = SOME T /\
    state_rel c l1 l2 s r [] locs ==>
    state_rel c l1 l2 (s with space := k) r [] locs``,
  fs [state_rel_def] \\ rw [] \\ asm_exists_tac \\ fs []
  \\ fs [heap_in_memory_store_def,wordSemTheory.has_space_def]
  \\ fs [GSYM word_add_n2w,WORD_LEFT_ADD_DISTRIB]
  \\ fs [alloc_size_def,bytes_in_word_def]
  \\ `(sp * (dimindex (:'a) DIV 8)) + 1 < dimword (:'a)` by
   (imp_res_tac word_ml_inv_SP_LIMIT
    \\ match_mp_tac LESS_EQ_LESS_TRANS
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs [])
  \\ `(sp * (dimindex (:'a) DIV 8)) < dimword (:'a)` by decide_tac
  \\ every_case_tac \\ fs [word_mul_n2w]
  \\ fs [good_dimindex_def] \\ fs [w2n_minus1] \\ rfs []
  \\ `F` by decide_tac);

val evaluate_IMP_inc_clock = prove(
  ``evaluate (q,t) = (NONE,t1) ==>
    evaluate (q,inc_clock ck t) = (NONE,inc_clock ck t1)``,
  rw [inc_clock_def] \\ match_mp_tac evaluate_add_clock \\ fs []);

val evaluate_IMP_inc_clock_Ex = prove(
  ``evaluate (q,t) = (SOME (Exception x y),t1) ==>
    evaluate (q,inc_clock ck t) = (SOME (Exception x y),inc_clock ck t1)``,
  rw [inc_clock_def] \\ match_mp_tac evaluate_add_clock \\ fs []);

val get_var_inc_clock = prove(
  ``get_var n (inc_clock k s) = get_var n s``,
  fs [wordSemTheory.get_var_def,inc_clock_def]);

val get_vars_inc_clock = prove(
  ``get_vars n (inc_clock k s) = get_vars n s``,
  Induct_on `n` \\ fs [wordSemTheory.get_vars_def]
  \\ every_case_tac \\ fs [get_var_inc_clock]);

val set_var_inc_clock = store_thm("set_var_inc_clock",
  ``set_var n x (inc_clock ck t) = inc_clock ck (set_var n x t)``,
  fs [wordSemTheory.set_var_def,inc_clock_def]);

val state_rel_cut_env = prove(
  ``state_rel c l1 l2 s t [] locs /\
    bvpSem$cut_env names s.locals = SOME x ==>
    state_rel c l1 l2 (s with locals := x) t [] locs``,
  fs [state_rel_def,bvpSemTheory.cut_env_def] \\ rw []
  THEN1 (fs[lookup_inter] \\ every_case_tac \\ fs [])
  \\ asm_exists_tac \\ fs []
  \\ first_x_assum (fn th => mp_tac th THEN match_mp_tac word_ml_inv_rearrange)
  \\ fs [] \\ rw [] \\ fs [] \\ rpt disj1_tac
  \\ PairCases_on `x` \\ fs [join_env_def,MEM_MAP]
  \\ Cases_on `y` \\ fs [EXISTS_PROD,MEM_FILTER]
  \\ qexists_tac `q` \\ fs [] \\ rw []
  THEN1
   (AP_TERM_TAC
    \\ fs [FUN_EQ_THM,lookup_inter_alt,MEM_toAList,domain_lookup]
    \\ fs [SUBSET_DEF,IN_DEF,domain_lookup] \\ rw []
    \\ imp_res_tac IMP_adjust_var
    \\ `lookup (adjust_var ((q - 2) DIV 2))
           (adjust_set (inter s.locals names)) = NONE` by
     (simp [lookup_adjust_var_adjust_set_NONE,lookup_inter_alt]
      \\ fs [domain_lookup]) \\ rfs [])
  \\ fs [MEM_toAList,lookup_inter_alt]
  \\ fs [domain_lookup,unit_some_eq_IS_SOME,adjust_set_def,lookup_fromAList]
  \\ rfs [IS_SOME_ALOOKUP_EQ,MEM_MAP] \\ rw []
  \\ Cases_on `y'` \\ fs [] \\ rw [EXISTS_PROD,adjust_var_11]
  \\ fs [MEM_toAList,lookup_inter_alt]);

val none = ``NONE:(num # ('a wordLang$prog) # num # num) option``

val compile_correct = store_thm("compile_correct",
  ``!prog (s:'ffi bvpSem$state) c n l l1 l2 res s1 (t:('a,'ffi)wordSem$state) locs.
      (bvpSem$evaluate (prog,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] locs ==>
      ?ck t1 res1.
        (wordSem$evaluate (FST (comp c n l prog),inc_clock ck t) = (res1,t1)) /\
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
                LAST_N (LENGTH s1.stack + 1) locs = (l5,l6)::ll /\
                !i. state_rel c l5 l6 (set_var i v s1)
                       (set_var (adjust_var i) w t1) [] ll)
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)``,
  recInduct bvpSemTheory.evaluate_ind \\ rpt strip_tac \\ fs []
  THEN1 (* Skip *)
   (qexists_tac `0`
    \\ fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ rw [])
  THEN1 (* Move *)
   (qexists_tac `0` \\ fs []
    \\ fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var src s.locals` \\ fs [] \\ rw []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs [wordSemTheory.get_vars_def,wordSemTheory.set_vars_def,alist_insert_def]
    \\ fs [state_rel_def,set_var_def,lookup_insert]
    \\ rpt strip_tac \\ fs []
    THEN1 (rw [] \\ Cases_on `n = dest` \\ fs [])
    \\ asm_exists_tac
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ imp_res_tac word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_insert \\ fs [])
  THEN1 (* Assign *)
   (fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ imp_res_tac (METIS_PROVE [] ``(if b1 /\ b2 then x1 else x2) = y ==>
                                     b1 /\ b2 /\ x1 = y \/
                                     (b1 ==> ~b2) /\ x2 = y``)
    \\ fs [] \\ rw [] \\ Cases_on `cut_state_opt names_opt s` \\ fs []
    \\ Cases_on `get_vars args x.locals` \\ fs []
    \\ reverse (Cases_on `do_app op x' x`) \\ fs []
    THEN1 (imp_res_tac do_app_Rerr \\ rw [])
    \\ Cases_on `a`
    \\ mp_tac (assign_thm |> Q.GEN `vals` |> Q.GEN `v` |> Q.GEN `s2`) \\ fs []
    \\ rw [] \\ fs [] \\ qexists_tac `ck` \\ fs [set_var_def]
    \\ `s.ffi = t.ffi` by fs [state_rel_def] \\ fs [] \\ strip_tac
    \\ `x.ffi = s.ffi` by all_tac
    \\ imp_res_tac do_app_io_events_mono \\ rfs []
    \\ Cases_on `names_opt` \\ fs [cut_state_opt_def] \\ rw [] \\ fs []
    \\ fs [cut_state_def,cut_env_def] \\ every_case_tac \\ fs [] \\ rw [] \\ fs [])
  THEN1 (* Tick *)
   (qexists_tac `0` \\ fs []
    \\ fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs [] \\ rw []
    \\ fs [] \\ rw [] \\ rpt (pop_assum mp_tac)
    \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def] \\ rw []
    \\ fs [state_rel_def,bvpSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
    \\ fs [call_env_def,wordSemTheory.call_env_def]
    \\ Q.LIST_EXISTS_TAC [`heap`,`limit`,`a`,`sp`] \\ fs [])
  THEN1 (* MakeSpace *)
   (qexists_tac `0` \\ fs []
    \\ fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def,
        GSYM alloc_size_def,LET_DEF,wordSemTheory.word_exp_def,
        wordLangTheory.word_op_def,wordSemTheory.get_var_imm_def]
    \\ `?end next.
          FLOOKUP t.store EndOfHeap = SOME (Word end) /\
          FLOOKUP t.store NextFree = SOME (Word next)` by
            fs [state_rel_def,heap_in_memory_store_def] \\ fs []
    \\ reverse CASE_TAC THEN1
     (every_case_tac \\ fs [] \\ rw []
      \\ fs [wordSemTheory.set_var_def,state_rel_insert_1]
      \\ match_mp_tac state_rel_cut_env \\ reverse (rw [])
      \\ fs [add_space_def] \\ match_mp_tac has_space_state_rel
      \\ fs [wordSemTheory.has_space_def,WORD_LO,NOT_LESS,
             asmSemTheory.word_cmp_def])
    \\ Cases_on `bvpSem$cut_env names s.locals` \\ fs []
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
    \\ imp_res_tac has_space_state_rel \\ fs []
    \\ imp_res_tac bvpPropsTheory.pop_env_const \\ fs []
    \\ imp_res_tac wordPropsTheory.pop_env_const \\ fs []
    \\ UNABBREV_ALL_TAC \\ fs [wordSemTheory.set_store_def,state_rel_def])
  THEN1 (* Raise *)
   (qexists_tac `0` \\ fs []
    \\ fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs [] \\ rw []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ Cases_on `jump_exc s` \\ fs [] \\ rw []
    \\ imp_res_tac state_rel_jump_exc \\ fs []
    \\ rw [] \\ fs [] \\ rw [mk_loc_def])
  THEN1 (* Return *)
   (qexists_tac `0` \\ fs []
    \\ fs [comp_def,bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs [] \\ rw []
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          fs [state_rel_def,wordSemTheory.get_var_def]
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP \\ fs []
    \\ fs [state_rel_def,wordSemTheory.call_env_def,lookup_def,
           bvpSemTheory.call_env_def,fromList_def,EVAL ``join_env LN []``,
           EVAL ``toAList (inter (fromList2 []) (insert 0 () LN))``]
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
    THEN1 (qexists_tac `ck` \\ fs []
           \\ rpt strip_tac \\ fs [] \\ rw [] \\ Cases_on `q''` \\ fs []
           \\ Cases_on `x` \\ fs [] \\ Cases_on `e` \\ fs [])
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
    THEN1 (qexists_tac `ck` \\ fs []
      \\ imp_res_tac bvpPropsTheory.evaluate_io_events_mono \\ fs []
      \\ imp_res_tac IS_PREFIX_TRANS \\ fs [] \\ metis_tac []) \\ rw []
    \\ qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
    \\ rpt strip_tac \\ rfs [] \\ rpt strip_tac \\ fs []
    \\ imp_res_tac evaluate_IMP_inc_clock \\ fs []
    \\ pop_assum (qspec_then `ck'` assume_tac)
    \\ qexists_tac `ck'+ck` \\ fs []
    \\ rw [] \\ fs []
    \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def] \\ fs []
    \\ imp_res_tac evaluate_mk_loc_EQ \\ fs []
    \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
    \\ fs [jump_exc_inc_clock_EQ_NONE] \\ metis_tac [])
  THEN1 (* If *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `comp c n l c1` \\ fs [LET_DEF]
    \\ Cases_on `comp c n r c2` \\ fs [LET_DEF]
    \\ fs [bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ fs []
    \\ fs [] \\ imp_res_tac state_rel_get_var_IMP
    \\ fs [wordSemTheory.get_var_imm_def,asmSemTheory.word_cmp_def]
    \\ imp_res_tac get_var_T_OR_F
    \\ Cases_on `x = Boolv T` \\ fs [] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n`,`l`] mp_tac)
      \\ rpt strip_tac \\ rfs[]
      \\ fs [get_var_inc_clock]
      \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
      \\ qexists_tac `ck` \\ fs [get_var_inc_clock])
    \\ Cases_on `x = Boolv F` \\ fs [] THEN1
     (qpat_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n`,`r`] mp_tac)
      \\ rpt strip_tac \\ rfs[]
      \\ fs [get_var_inc_clock]
      \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
      \\ qexists_tac `ck` \\ fs [get_var_inc_clock]))
  THEN1 (* Call *)
   (once_rewrite_tac [bvp_to_wordTheory.comp_def] \\ fs []
    \\ Cases_on `ret`
    \\ fs [bvpSemTheory.evaluate_def,wordSemTheory.evaluate_def,
           wordSemTheory.add_ret_loc_def,get_vars_inc_clock]
    THEN1 (* ret = NONE *)
     (Cases_on `get_vars args s.locals` \\ fs []
      \\ imp_res_tac state_rel_0_get_vars_IMP \\ fs []
      \\ Cases_on `find_code dest x s.code` \\ fs []
      \\ Cases_on `x'` \\ fs [] \\ Cases_on `handler` \\ fs []
      \\ `t.clock = s.clock` by fs [state_rel_def]
      \\ mp_tac find_code_thm \\ fs [] \\ rw [] \\ fs []
      \\ fs [EVAL ``(inc_clock ck t).code``,EVAL ``(inc_clock ck t).clock``]
      \\ Cases_on `s.clock = 0` \\ fs [] \\ rw [] \\ fs []
      THEN1 (qexists_tac `0`
        \\ fs [call_env_def,wordSemTheory.call_env_def,state_rel_def])
      \\ Cases_on `evaluate (r,call_env q (dec_clock s))` \\ fs []
      \\ Cases_on `q'` \\ fs [] \\ rw [] \\ fs [] \\ res_tac
      \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac)
      \\ qexists_tac `ck` \\ fs []
      \\ `t.clock <> 0` by fs [state_rel_def]
      \\ `inc_clock ck (call_env args1 (dec_clock t)) =
          call_env args1 (dec_clock (inc_clock ck t))` by
       (fs [wordSemTheory.call_env_def,inc_clock_def,
            wordSemTheory.dec_clock_def,
            wordSemTheory.state_component_equality] \\ decide_tac) \\ fs []
      \\ Cases_on `res1` \\ fs [] \\ rw [] \\ fs []
      \\ every_case_tac \\ fs [mk_loc_def]
      \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def]
      \\ BasicProvers.EVERY_CASE_TAC \\ fs [mk_loc_def])
    \\ Cases_on `x` \\ fs [LET_DEF]
    \\ Cases_on `handler` \\ fs [wordSemTheory.evaluate_def]
    \\ Cases_on `get_vars args s.locals` \\ fs []
    \\ imp_res_tac state_rel_get_vars_IMP \\ fs []
    \\ fs [wordSemTheory.add_ret_loc_def]
    THEN1 (* no handler *)
     (Cases_on `bvlSem$find_code dest x s.code` \\ fs [] \\ Cases_on `x'` \\ fs []
      \\ Q.MATCH_ASSUM_RENAME_TAC `bvlSem$find_code dest xs s.code = SOME (ys,prog)`
      \\ Cases_on `bvpSem$cut_env r s.locals` \\ fs []
      \\ imp_res_tac cut_env_IMP_cut_env \\ fs [] \\ rw []
      \\ `t.clock = s.clock` by fs [state_rel_def] \\ fs []
      \\ fs [get_vars_inc_clock]
      \\ mp_tac find_code_thm_ret \\ fs [] \\ rw [] \\ fs []
      \\ Cases_on `s.clock = 0` \\ fs [] \\ rw []
      \\ fs [EVAL ``(inc_clock ck t).code``,EVAL ``(inc_clock ck t).locals``,
             EVAL ``(inc_clock ck t).clock``]
      THEN1 (qexists_tac `0`
        \\ fs [call_env_def,wordSemTheory.call_env_def,state_rel_def])
      \\ Cases_on `evaluate (prog,call_env ys (push_env x F (dec_clock s)))`
      \\ fs [] \\ Cases_on `q'` \\ fs []
      \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ fs []
      \\ res_tac (* inst ind hyp *)
      \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs []
      \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
      \\ qexists_tac `ck` \\ fs []
      \\ `inc_clock ck (call_env args1 (push_env y ^none (dec_clock t))) =
          call_env args1 (push_env y ^none (dec_clock (inc_clock ck t)))` by
       (fs [inc_clock_def,wordSemTheory.call_env_def,
            wordSemTheory.push_env_def,wordSemTheory.dec_clock_def]
        \\ Cases_on `env_to_list y t.permute` \\ fs [LET_DEF]
        \\ fs [wordSemTheory.state_component_equality]
        \\ `t.clock <> 0` by fs [state_rel_def] \\ decide_tac) \\ fs []
      THEN1
       (`s1.ffi = r'.ffi` by all_tac \\ fs []
        \\ every_case_tac \\ fs [] \\ rw [] \\ fs [set_var_def]
        \\ imp_res_tac bvpPropsTheory.pop_env_const \\ fs []
        \\ imp_res_tac wordPropsTheory.pop_env_const \\ fs [])
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
    \\ Cases_on `bvlSem$find_code dest x' s.code` \\ fs [] \\ Cases_on `x` \\ fs []
    \\ Q.MATCH_ASSUM_RENAME_TAC `bvlSem$find_code dest xs s.code = SOME (ys,prog)`
    \\ Cases_on `bvpSem$cut_env r s.locals` \\ fs []
    \\ imp_res_tac cut_env_IMP_cut_env \\ fs [] \\ rw []
    \\ `t.clock = s.clock` by fs [state_rel_def]
    \\ fs [get_vars_inc_clock,EVAL ``(inc_clock ck t).code``,
           EVAL ``(inc_clock ck t).locals``,EVAL ``(inc_clock ck t).clock``]
    \\ mp_tac find_code_thm_handler \\ fs [] \\ rw [] \\ fs []
    \\ Cases_on `s.clock = 0` \\ fs [] \\ rw []
    THEN1 (qexists_tac `0`
      \\ fs [call_env_def,wordSemTheory.call_env_def,state_rel_def])
    \\ Cases_on `evaluate (prog,call_env ys (push_env x T (dec_clock s)))`
    \\ fs [] \\ Cases_on `q'` \\ fs []
    \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ fs []
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs []
    \\ `call_env args1
          (push_env y (SOME (adjust_var x0,prog1,x0,l + 1))
             (dec_clock (inc_clock ck t))) =
        inc_clock ck
            (call_env args1
               (push_env y (SOME (adjust_var x0,prog1,x0,l + 1))
                  (dec_clock t)))` by
     (fs [inc_clock_def,wordSemTheory.dec_clock_def,LET_DEF,
          wordSemTheory.call_env_def,wordSemTheory.push_env_def]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
      \\ fs [wordSemTheory.state_component_equality] \\ decide_tac)
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ fs []
    THEN1 (qexists_tac `ck` \\ fs []
      \\ `r'.ffi.io_events ≼ s1.ffi.io_events ∧
          (IS_SOME t1.ffi.final_event ⇒ r'.ffi = s1.ffi)` by all_tac
      \\ TRY (imp_res_tac IS_PREFIX_TRANS \\ fs [] \\ NO_TAC)
      \\ every_case_tac \\ fs []
      \\ imp_res_tac bvpPropsTheory.evaluate_io_events_mono \\ fs [set_var_def]
      \\ imp_res_tac wordPropsTheory.pop_env_const \\ fs []
      \\ imp_res_tac bvpPropsTheory.pop_env_const \\ fs [] \\ rw [] \\ fs []
      \\ metis_tac [])
    \\ Cases_on `x'` \\ fs [] THEN1
     (qexists_tac `ck` \\ fs []
      \\ Cases_on `pop_env r'` \\ fs [] \\ rw []
      \\ rpt strip_tac \\ fs []
      \\ imp_res_tac state_rel_pop_env_set_var_IMP \\ fs [] \\ rw []
      \\ pop_assum mp_tac \\ fs []
      \\ match_mp_tac (GEN_ALL evaluate_IMP_domain_EQ)
      \\ qpat_assum `tt = inc_clock ck yy` (assume_tac o GSYM) \\ fs []
      \\ asm_exists_tac \\ fs [])
    \\ reverse (Cases_on `e`) \\ fs []
    THEN1 (qexists_tac `ck` \\ fs [] \\ rw [])
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
    \\ imp_res_tac evaluate_IMP_inc_clock_Ex \\ fs []
    \\ pop_assum (qspec_then `ck'` mp_tac)
    \\ `inc_clock (ck' + ck)
         (call_env args1
          (push_env y (SOME (adjust_var x0,prog1,x0,l + 1))
             (dec_clock t))) =
        call_env args1
            (push_env y (SOME (adjust_var x0,prog1,x0,l + 1))
               (dec_clock (inc_clock (ck' + ck) t)))` by
     (fs [wordSemTheory.call_env_def,wordSemTheory.push_env_def,inc_clock_def,
          wordSemTheory.dec_clock_def,LET_DEF]
      \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
      \\ fs [wordSemTheory.state_component_equality]
      \\ decide_tac)
    \\ fs [] \\ rpt strip_tac \\ fs []
    \\ qexists_tac `ck' + ck` \\ fs []
    \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ fs []
    \\ fs [EVAL ``(inc_clock ck' t1).locals``,set_var_inc_clock]
    \\ rw [] \\ fs [] \\ Cases_on `res` \\ fs []
    \\ rpt (CASE_TAC \\ fs [])
    \\ imp_res_tac mk_loc_eq_push_env_exc_Exception \\ fs []
    \\ imp_res_tac eval_push_env_SOME_exc_IMP_s_key_eq
    \\ imp_res_tac s_key_eq_handler_eq_IMP
    \\ fs [jump_exc_inc_clock_EQ_NONE] \\ metis_tac []));

val compile_correct_lemma = store_thm("compile_correct_lemma",
  ``!(s:'ffi bvpSem$state) c l1 l2 res s1 (t:('a,'ffi)wordSem$state) start.
      (bvpSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] [] ==>
      ?ck t1 res1.
        !perm.
          (wordSem$evaluate (Call NONE (SOME start) [0] NONE,
             inc_clock ck t with permute := perm) = (res1,t1)) /\
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
  cheat); (* the theorem above needs adjusting *)

(* TODO: Move to appropriate theory when done *)
val compile_word_to_word_thm = store_thm("compile_word_to_word_thm",
  ``(!n v. lookup n st.code = SOME v ==>
           lookup n l = SOME (SND (compile_single t k a c ((n,v),col)))) ==>
    ?perm'.
      let prog = Call NONE (SOME start) [0] NONE in
      let (res,rst) = evaluate (prog,st with permute := perm') in
        if res = SOME Error then T else
          let (res1,rst1) = evaluate (prog,st with code := l) in
            res1 = res /\ rst1.clock = rst.clock /\ rst1.ffi = rst.ffi``,
  cheat) (* can this be proved? *)
  |> SIMP_RULE std_ss [Once LET_THM]

val state_rel_ext_def = Define `
  state_rel_ext (c,t',k',a',c',col) l1 l2 s u <=>
    ?t l.
      state_rel c l1 l2 s t [] [] /\
      (!n v. lookup n t.code = SOME v ==>
             lookup n l = SOME (SND (compile_single t' k' a' c' ((n,v),col)))) /\
      u = t with code := l`

val compile_correct = store_thm("compile_correct",
  ``!x (s:'ffi bvpSem$state) l1 l2 res s1 (t:('a,'ffi)wordSem$state) start.
      (bvpSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel_ext x l1 l2 s t ==>
      ?ck t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,
           inc_clock ck t) = (res1,t1)) /\
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
  \\ fs [state_rel_ext_def,PULL_EXISTS]
  \\ rw [] \\ drule compile_correct_lemma \\ fs []
  \\ disch_then drule \\ strip_tac \\ fs []
  \\ qcase_tac `state_rel x0 l1 l2 s t [] []`
  \\ `(!n v. lookup n (inc_clock ck t).code = SOME v ==>
             lookup n l = SOME (SND (compile_single x1 x2 x3 x4 ((n,v),x5))))`
        by fs [inc_clock_def]
  \\ drule compile_word_to_word_thm \\ rw []
  \\ fs [GSYM PULL_FORALL] \\ fs [LET_DEF]
  THEN1 (every_case_tac \\ fs [] \\ rfs [])
  \\ split_pair_tac \\ fs [] \\ rw []
  \\ fs [inc_clock_def]
  \\ qexists_tac `ck` \\ fs []
  \\ rw [] \\ fs []
  \\ every_case_tac \\ fs []);

val state_rel_ext_with_clock = prove(
  ``state_rel_ext a b c s1 s2 ==>
    state_rel_ext a b c (s1 with clock := k) (s2 with clock := k)``,
  PairCases_on `a` \\ fs [state_rel_ext_def] \\ rw []
  \\ drule state_rel_with_clock
  \\ strip_tac \\ asm_exists_tac \\ fs []
  \\ qexists_tac `l` \\ fs []);

(* observational semantics preservation *)

val compile_semantics = Q.store_thm("compile_semantics",
  `state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state) (fromAList prog) t.clock) t /\
   semantics ffi (fromAList prog) start <> Fail ==>
   semantics t start IN
     extend_with_resource_limit { semantics ffi (fromAList prog) start }`,
  simp[GSYM AND_IMP_INTRO] >> ntac 1 strip_tac >>
  simp[bvpSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    qx_gen_tac`r`>>simp[]>>strip_tac>>
    strip_tac >>
    simp[wordSemTheory.semantics_def] >>
    IF_CASES_TAC >- (
      fs[] >> rveq >> fs[] >>
      rator_x_assum`bvpSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      strip_tac >>
      drule compile_correct >> simp[] >> fs [] >>
      simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
      discharge_hyps >- (
        strip_tac >> fs[] ) >>
      drule(GEN_ALL state_rel_ext_with_clock) >>
      disch_then(qspec_then`k'`strip_assume_tac) >> fs[] >>
      disch_then drule >>
      simp[comp_def] >> strip_tac >>
      qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
      Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
      drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
      simp[RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- (strip_tac >> fs[]) >>
      disch_then(qspec_then`ck`mp_tac) >>
      fsrw_tac[ARITH_ss][inc_clock_def] >> rw[] >>
      every_case_tac >> fs[] ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      rw[extend_with_resource_limit_def] >> fs[] >>
      Cases_on`s.ffi.final_event`>>fs[] >- (
        Cases_on`r'`>>fs[] >> rveq >>
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
           fs[inc_clock_def,Abbr`tt`] >>
           disch_then(qspec_then`k+ck`mp_tac)>>simp[]>>
           fsrw_tac[ARITH_ss][] ) >>
        Cases_on`r = SOME TimeOut` >- (
          every_case_tac >> fs[]>>
          Cases_on`res1=SOME NotEnoughSpace`>>fs[] >> rfs[] >>
          fs[] >> rfs[] ) >>
        rator_x_assum`wordSem$evaluate`mp_tac >>
        drule(GEN_ALL wordPropsTheory.evaluate_add_clock) >>
        simp[] >>
        disch_then(qspec_then`ck+k`mp_tac) >>
        simp[inc_clock_def] >> ntac 2 strip_tac >>
        rveq >> fs[] >>
        every_case_tac >> fs[] >> rw[] >>
        fs[] >> rfs[] ) >>
      `∃r s'.
        evaluate
          (Call NONE (SOME start) [] NONE, initial_state ffi (fromAList prog) (k + k')) = (r,s') ∧
        s'.ffi = s.ffi` by (
          srw_tac[QUANT_INST_ss[pair_default_qp]][] >>
          metis_tac[bvpPropsTheory.evaluate_add_clock_io_events_mono,SND,
                    initial_state_with_simp,IS_SOME_EXISTS,initial_state_simp]) >>
      drule compile_correct >> simp[] >>
      simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- (
        last_x_assum(qspec_then`k+k'`mp_tac)>>rw[]>>
        strip_tac>>fs[])>>
      drule(GEN_ALL state_rel_ext_with_clock)>>simp[]>>
      disch_then(qspec_then`k+k'`mp_tac)>>simp[]>>strip_tac>>
      disch_then drule>>
      simp[comp_def]>>strip_tac>>
      `t'.ffi.io_events ≼ t1.ffi.io_events ∧
       (IS_SOME t'.ffi.final_event ⇒ t1.ffi = t'.ffi)` by (
        qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
        Q.ISPECL_THEN[`exps`,`tt`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
        fs[inc_clock_def,Abbr`tt`] >>
        disch_then(qspec_then`k+ck`mp_tac)>>simp[]>>
        fsrw_tac[ARITH_ss][] ) >>
      reverse(Cases_on`t'.ffi.final_event`)>>fs[] >- (
        Cases_on`res1=SOME NotEnoughSpace`>>fs[]>>
        fs[]>>rfs[]>>
        every_case_tac>>fs[]>>rfs[]>>
        rveq>>fs[]>>
        last_x_assum(qspec_then`k+k'`mp_tac) >> simp[]) >>
      Cases_on`r`>>fs[]>>
      rator_x_assum`wordSem$evaluate`mp_tac >>
      drule(GEN_ALL wordPropsTheory.evaluate_add_clock) >>
      simp[RIGHT_FORALL_IMP_THM] >>
      discharge_hyps >- ( strip_tac >> fs[] ) >>
      disch_then(qspec_then`k+ck`mp_tac) >>
      fsrw_tac[ARITH_ss][inc_clock_def]>> rw[] >>
      every_case_tac>>fs[]>>rveq>>rfs[]>>
      fs[]>>rfs[]) >>
    rw[] >> fs[] >>
    drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    discharge_hyps >- (
      last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
      rw[] >> strip_tac >> fs[] ) >>
    drule(state_rel_ext_with_clock) >> simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    fs[inc_clock_def] >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    simp[] >>
    every_case_tac >> fs[] >> rw[]) >>
  rw[] >>
  simp[wordSemTheory.semantics_def] >>
  IF_CASES_TAC >- (
    fs[] >> rveq >> fs[] >>
    last_x_assum(qspec_then`k`mp_tac)>>simp[] >>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule compile_correct >> simp[] >>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    discharge_hyps >- ( strip_tac >> fs[] ) >>
    drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    qmatch_assum_abbrev_tac`option_CASE (FST p) _ _` >>
    Cases_on`p`>>pop_assum(strip_assume_tac o SYM o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    drule (GEN_ALL wordPropsTheory.evaluate_add_clock) >>
    simp[RIGHT_FORALL_IMP_THM] >>
    discharge_hyps >- (strip_tac >> fs[]) >>
    disch_then(qspec_then`ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >> rw[] >>
    every_case_tac >> fs[] ) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[extend_with_resource_limit_def] >> fs[] >>
    qpat_assum`∀x y. _`(qspec_then`k`mp_tac)>>
    (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
    strip_tac >>
    drule(compile_correct)>>
    simp[RIGHT_FORALL_IMP_THM,GSYM AND_IMP_INTRO] >>
    discharge_hyps >- (
      strip_tac >> fs[] >>
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
      fs[inc_clock_def,Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    fs[] >>
    first_assum(qspec_then`k`mp_tac) >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >>
    rator_x_assum`wordSem$evaluate`mp_tac >>
    drule(GEN_ALL wordPropsTheory.evaluate_add_clock)>>
    simp[]>>
    disch_then(qspec_then`ck`mp_tac)>>
    last_x_assum(qspec_then`k`mp_tac) >>
    every_case_tac >> fs[] >> rfs[]>>rw[]>>fs[] >>
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
  rw[extend_with_resource_limit_def] >>
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
    discharge_hyps >- (
      last_x_assum(qspec_then`k`mp_tac)>>rw[]>>
      strip_tac >> fs[] ) >>
    drule(state_rel_ext_with_clock) >>
    simp[] >> strip_tac >>
    disch_then drule >>
    simp[comp_def] >> strip_tac >>
    qexists_tac`k+ck`>>fs[inc_clock_def]>>
    Cases_on`res1=SOME NotEnoughSpace`>>fs[]>-(
      first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
      CASE_TAC >> fs[] ) >>
    ntac 2 (pop_assum mp_tac) >>
    CASE_TAC >> fs[] >>
    TRY CASE_TAC >> fs [] >>
    TRY CASE_TAC >> fs [] >>
    strip_tac >> fs[] >>
    rveq >>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[]) ) >>
  (fn g => subterm (fn tm => Cases_on`^(replace_term(#1(dest_exists(#2 g)))(``k:num``)(assert(has_pair_type)tm))`) (#2 g) g) >>
  drule compile_correct >>
  simp[GSYM AND_IMP_INTRO,RIGHT_FORALL_IMP_THM] >>
  discharge_hyps >- (
    last_x_assum(qspec_then`k`mp_tac)>>rw[]>>
    strip_tac >> fs[] ) >>
  drule(state_rel_ext_with_clock) >>
  simp[] >> strip_tac >>
  disch_then drule >>
  simp[comp_def] >> strip_tac >>
  fs[inc_clock_def] >>
  Cases_on`res1=SOME NotEnoughSpace`>>fs[]>-(
    first_x_assum(qspec_then`k+ck`mp_tac) >> simp[] >>
    CASE_TAC >> fs[] ) >>
  qmatch_assum_abbrev_tac`n < LENGTH (SND (evaluate (exps,s))).ffi.io_events` >>
  Q.ISPECL_THEN[`exps`,`s`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
  disch_then(qspec_then`ck`mp_tac)>>simp[Abbr`s`]>>strip_tac>>
  qexists_tac`k`>>simp[]>>
  `r.ffi.io_events = t1.ffi.io_events` by (
    ntac 5 (pop_assum mp_tac) >>
    CASE_TAC >> fs[] >>
    every_case_tac >> fs[]>>rw[]>>
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[])) >>
  REV_FULL_SIMP_TAC(srw_ss()++ARITH_ss)[]>>
  fsrw_tac[ARITH_ss][IS_PREFIX_APPEND]>>
  simp[EL_APPEND1]);

val _ = export_theory();
