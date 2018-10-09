open preamble bvlSemTheory dataSemTheory dataPropsTheory
     copying_gcTheory int_bitwiseTheory finite_mapTheory
     data_to_word_memoryProofTheory data_to_word_gcProofTheory
     data_to_word_bignumProofTheory data_to_word_assignProofTheory
     data_to_wordTheory wordPropsTheory labPropsTheory whileTheory
     set_sepTheory semanticsPropsTheory word_to_wordProofTheory
     helperLib alignmentTheory blastLib word_bignumTheory
     wordLangTheory word_bignumProofTheory gen_gc_partialTheory
     gc_sharedTheory;
local open gen_gcTheory in end

val _ = new_theory "data_to_wordProof";

val _ = hide "next";

(* TODO: move to sptTheory *)

val eq_shape_def = Define `
  eq_shape LN LN = T /\
  eq_shape (LS _) (LS _) = T /\
  eq_shape (BN t1 t2) (BN u1 u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape (BS t1 _ t2) (BS u1 _ u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape _ _ = F`;

val spt_eq = store_thm("spt_eq",
  ``!t1 t2.
      t1 = t2 <=>
      (eq_shape t1 t2 /\ (!k v. lookup k t1 = SOME v ==> lookup k t2 = SOME v))``,
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,lookup_def]
  THEN1 metis_tac []
  \\ rw [] \\ eq_tac \\ rw [] \\ rw [] \\ fs []
  \\ first_assum (qspec_then `0` mp_tac)
  \\ first_assum (qspec_then `k * 2 + 1` mp_tac)
  \\ first_x_assum (qspec_then `k * 2 + 1 + 1` mp_tac)
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] MULT_DIV]
  \\ fs [ONCE_REWRITE_RULE [MULT_COMM] DIV_MULT,EVEN_ADD]
  \\ fs [GSYM ADD1,EVEN,EVEN_DOUBLE]);

val eq_shape_map = store_thm("eq_shape_map",
  ``!t1 t2 f. eq_shape (map f t1) t2 <=> eq_shape t1 t2``,
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,map_def]);

val eq_shape_IMP_domain = store_thm("eq_shape_IMP_domain",
  ``!t1 t2. eq_shape t1 t2 ==> domain t1 = domain t2``,
  ho_match_mp_tac (fetch "-" "eq_shape_ind")
  \\ rw [] \\ fs [eq_shape_def]);

val copy_shape_def = Define `
  copy_shape LN LN = LN /\
  copy_shape LN (LS y) = LN /\
  copy_shape LN (BN t1 t2) = BN (copy_shape LN t1) (copy_shape LN t2) /\
  copy_shape LN (BS t1 y t2) = LN /\
  copy_shape (LS x) LN = LS x /\
  copy_shape (LS x) (LS y) = LS x /\
  copy_shape (LS x) (BN t1 t2) = LS x /\
  copy_shape (LS x) (BS t1 y t2) = BS (copy_shape LN t1) x (copy_shape LN t2) /\
  copy_shape (BN u1 u2) LN = (if domain (BN u1 u2) = {} then LN else BN u1 u2) /\
  copy_shape (BN u1 u2) (LS y) = BN u1 u2 /\
  copy_shape (BN u1 u2) (BN t1 t2) = BN (copy_shape u1 t1) (copy_shape u2 t2) /\
  copy_shape (BN u1 u2) (BS t1 y t2) = BN u1 u2 /\
  copy_shape (BS u1 x u2) LN = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (LS y) =
     (if domain (BN u1 u2) = {} then LS x else BS u1 x u2) /\
  copy_shape (BS u1 x u2) (BN t1 t2) = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (BS t1 y t2) = BS (copy_shape u1 t1) x (copy_shape u2 t2)`

val eq_shape_copy_shape = prove(
  ``!s. domain s = {} ==> eq_shape (copy_shape LN s) s``,
  Induct \\ fs [copy_shape_def,eq_shape_def]);

val num_lemma = prove(
  ``(!n. 0 <> 2 * n + 2 /\ 0 <> 2 * n + 1:num) /\
    (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
    (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
    (!n m. 2 * n + 2 <> 2 * m + 1n)``,
  rw [] \\ fs [] \\ Cases_on `m = n` \\ fs []);

val shape_eq_copy_shape = store_thm("shape_eq_copy_shape",
  ``!t1 t2. domain t1 = domain t2 ==> eq_shape (copy_shape t1 t2) t2``,
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,copy_shape_def]
  \\ rpt strip_tac \\ TRY (first_x_assum match_mp_tac)
  \\ TRY (match_mp_tac eq_shape_copy_shape) \\ fs []
  \\ rw [] \\ fs [eq_shape_def] \\ fs [EXTENSION]
  \\ TRY (first_assum (qspec_then `0` mp_tac) \\ simp_tac std_ss [])
  \\ rw [] \\ first_assum (qspec_then `2 * x + 2` mp_tac)
  \\ first_x_assum (qspec_then `2 * x + 1` mp_tac)
  \\ fs [num_lemma]);

val lookup_copy_shape_LN = prove(
  ``!s n. lookup n (copy_shape LN s) = NONE``,
  Induct \\ fs [copy_shape_def,lookup_def] \\ rw [] \\ fs []);

val domain_EMPTY_lookup = prove(
  ``domain t = EMPTY ==> !x. lookup x t = NONE``,
  fs [domain_lookup,EXTENSION] \\ rw []
  \\ pop_assum (qspec_then `x` mp_tac)
  \\ Cases_on `lookup x t` \\ fs []);

val lookup_copy_shape = store_thm("lookup_copy_shape",
  ``!t1 t2 n. lookup n (copy_shape t1 t2) = lookup n t1``,
  Induct \\ Cases_on `t2` \\ fs [copy_shape_def,lookup_def] \\ rw []
  \\ fs [lookup_def,lookup_copy_shape_LN,domain_EMPTY_lookup]);

val domain_mapi = store_thm("domain_mapi[simp]",
  ``domain (mapi f x) = domain x``,
  fs [domain_lookup,EXTENSION,sptreeTheory.lookup_mapi]);

(* / TODO *)

val clean_tac = rpt var_eq_tac \\ rpt (qpat_x_assum `T` kall_tac)
fun rpt_drule th = drule (th |> GEN_ALL) \\ rpt (disch_then drule \\ fs [])

val state_rel_def = data_to_word_gcProofTheory.state_rel_def
val code_rel_def = data_to_word_gcProofTheory.code_rel_def

val data_compile_correct = Q.store_thm("data_compile_correct",
  `!prog s c n l l1 l2 res s1 (t:('a,'c,'ffi)wordSem$state) locs.
      (dataSem$evaluate (prog,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel c l1 l2 s t [] locs /\
      t.termdep > 1
      ==>
      ?t1 res1.
        (wordSem$evaluate (FST (comp c n l prog),t) = (res1,t1)) /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events) /\
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
         | SOME (Rerr (Rabort(Rffi_error f))) => (res1 = SOME(FinalFFI f) /\ t1.ffi = s1.ffi)
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)`,
  recInduct dataSemTheory.evaluate_ind \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
  THEN1 (* Skip *)
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ srw_tac[][])
  THEN1 (* Move *)
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
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
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ imp_res_tac (METIS_PROVE [] ``(if b1 /\ b2 then x1 else x2) = y ==>
                                     b1 /\ b2 /\ x1 = y \/
                                     (b1 ==> ~b2) /\ x2 = y``)
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ Cases_on `cut_state_opt names_opt s` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `get_vars args x.locals` \\ full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `do_app op x' x`) \\ full_simp_tac(srw_ss())[]
    THEN1 (imp_res_tac do_app_Rerr \\ srw_tac[][] \\
           imp_res_tac assign_FFI_final \\
           first_x_assum(qspecl_then [`n`,`l`,`dest`] strip_assume_tac) \\
           asm_exists_tac >> fs[] >> rpt strip_tac >> fs[] >>
           imp_res_tac cut_state_opt_const \\ fs[state_rel_def])
    \\ Cases_on `a`
    \\ drule (GEN_ALL assign_thm) \\ full_simp_tac(srw_ss())[]
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [`n`,`l`,`dest`] strip_assume_tac)
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac do_app_io_events_mono \\ rev_full_simp_tac(srw_ss())[]
    \\ `s.ffi = t.ffi` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[]
    \\ sg `x.ffi = s.ffi`
    \\ imp_res_tac do_app_io_events_mono \\ rev_full_simp_tac(srw_ss())[]
    \\ Cases_on `names_opt` \\ full_simp_tac(srw_ss())[cut_state_opt_def] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[cut_state_def,cut_env_def] \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (* Tick *)
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ rpt (pop_assum mp_tac)
    \\ full_simp_tac(srw_ss())[wordSemTheory.jump_exc_def,wordSemTheory.dec_clock_def] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[state_rel_def,dataSemTheory.dec_clock_def,wordSemTheory.dec_clock_def]
    \\ full_simp_tac(srw_ss())[call_env_def,wordSemTheory.call_env_def]
    \\ asm_exists_tac \\ fs [])
  THEN1 (* MakeSpace *)
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,
        wordSemTheory.evaluate_def,
        GSYM alloc_size_def,LET_DEF,wordSemTheory.word_exp_def,
        wordLangTheory.word_op_def,wordSemTheory.get_var_imm_def]
    \\ `?end next.
          FLOOKUP t.store TriggerGC = SOME (Word end) /\
          FLOOKUP t.store NextFree = SOME (Word next)` by
            full_simp_tac(srw_ss())[state_rel_def,heap_in_memory_store_def]
    \\ full_simp_tac(srw_ss())[wordSemTheory.the_words_def]
    \\ reverse CASE_TAC THEN1
     (every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[wordSemTheory.set_var_def,state_rel_insert_1]
      \\ match_mp_tac state_rel_cut_env \\ reverse (srw_tac[][])
      \\ full_simp_tac(srw_ss())[add_space_def] \\ match_mp_tac has_space_state_rel
      \\ full_simp_tac(srw_ss())[wordSemTheory.has_space_def,WORD_LO,NOT_LESS,
             asmTheory.word_cmp_def])
    \\ reverse (Cases_on `c.call_empty_ffi`)
    THEN1
     (fs [SilentFFI_def,wordSemTheory.evaluate_def,list_Seq_def]
      \\ Cases_on `dataSem$cut_env names s.locals` \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][]
      \\ full_simp_tac(srw_ss())[add_space_def,wordSemTheory.word_exp_def,
           wordSemTheory.get_var_def,wordSemTheory.set_var_def]
      \\ Cases_on `(alloc (alloc_size k) (adjust_set names)
           (t with locals := insert 1 (Word (alloc_size k)) t.locals))
               :('a result option)#( ('a,'c,'ffi) wordSem$state)`
      \\ full_simp_tac(srw_ss())[]
      \\ drule (GEN_ALL alloc_lemma)
      \\ rpt (disch_then drule)
      \\ rw [] \\ fs [])
    \\ fs [SilentFFI_def,wordSemTheory.evaluate_def,list_Seq_def,eq_eval]
    \\ fs [wordSemTheory.evaluate_def,SilentFFI_def,wordSemTheory.word_exp_def,
           wordSemTheory.set_var_def,EVAL ``read_bytearray 0w 0 m``,
           ffiTheory.call_FFI_def,EVAL ``write_bytearray a [] m dm b``,
           wordSemTheory.get_var_def,lookup_insert]
    \\ fs [cut_env_adjust_set_insert_1,cut_env_adjust_set_insert_3]
    \\ drule (GEN_ALL cut_env_IMP_cut_env)
    \\ Cases_on `dataSem$cut_env names s.locals` \\ fs []
    \\ disch_then drule \\ strip_tac \\ fs []
    \\ pairarg_tac \\ fs []
    \\ drule (GEN_ALL state_rel_cut_env_cut_env)
    \\ rpt (disch_then drule)
    \\ strip_tac
    \\ drule (GEN_ALL alloc_lemma) \\ fs [] \\ rveq
    \\ `dataSem$cut_env names x = SOME x` by
      (fs [dataSemTheory.cut_env_def] \\ rveq \\ fs [lookup_inter_alt,domain_inter])
    \\ rpt (disch_then drule)
    \\ qmatch_assum_abbrev_tac `alloc _ _ t5 = _`
    \\ `t5 = t with locals := insert 1 (Word (alloc_size k)) y` by
          (unabbrev_all_tac \\ fs [wordSemTheory.state_component_equality])
    \\ fs [] \\ disch_then drule
    \\ strip_tac \\ Cases_on `res' = SOME NotEnoughSpace` \\ fs []
    \\ rveq \\ fs []
    \\ imp_res_tac alloc_NONE_IMP_cut_env \\ fs []
    \\ fs [add_space_def] \\ fs [state_rel_thm])
  THEN1 (* Raise *)
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `jump_exc s` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ imp_res_tac state_rel_jump_exc \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ srw_tac[][mk_loc_def])
  THEN1 (* Return *)
   (full_simp_tac(srw_ss())[comp_def,dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ `get_var 0 t = SOME (Loc l1 l2)` by
          full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.get_var_def]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP
    \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[state_rel_def,wordSemTheory.call_env_def,lookup_def,
           dataSemTheory.call_env_def,fromList_def,EVAL ``join_env LN []``,
           EVAL ``toAList (inter (fromList2 []) (insert 0 () LN))``]
    \\ asm_exists_tac \\ fs []
    \\ full_simp_tac bool_ss [GSYM APPEND_ASSOC]
    \\ rpt_drule word_ml_inv_get_var_IMP
    \\ match_mp_tac word_ml_inv_rearrange
    \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[])
  THEN1 (* Seq *)
   (once_rewrite_tac [data_to_wordTheory.comp_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `comp c n l c1` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ Cases_on `comp c n r c2` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ full_simp_tac(srw_ss())[dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `evaluate (c1,s)` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `q'' <> SOME (Rerr (Rabort Rtype_error))` by
         (Cases_on `q'' = NONE` \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
    \\ fs[GSYM AND_IMP_INTRO]
    \\ qpat_x_assum `state_rel c l1 l2 s t [] locs` (fn th =>
           first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ fs[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`l`])
    \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[]
    \\ reverse (Cases_on `q'' = NONE`) \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ Cases_on `q''` \\ full_simp_tac(srw_ss())[]
           \\ Cases_on `x` \\ full_simp_tac(srw_ss())[] \\ Cases_on `e` \\ full_simp_tac(srw_ss())[] \\ PURE_TOP_CASE_TAC >> fs[])
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[]
      \\ imp_res_tac dataPropsTheory.evaluate_io_events_mono \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac IS_PREFIX_TRANS \\ full_simp_tac(srw_ss())[] \\ metis_tac []) \\ srw_tac[][]
    \\ qpat_x_assum `state_rel c l1 l2 _ _ [] locs` (fn th =>
             first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
    \\ imp_res_tac wordSemTheory.evaluate_clock \\ fs[]
    \\ strip_tac \\ pop_assum (mp_tac o Q.SPECL [`n`,`r`])
    \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[mk_loc_def] \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_mk_loc_EQ \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac eval_NONE_IMP_jump_exc_NONE_EQ
    \\ full_simp_tac(srw_ss())[jump_exc_inc_clock_EQ_NONE] \\ metis_tac [])
  THEN1 (* If *)
   (once_rewrite_tac [data_to_wordTheory.comp_def] \\ full_simp_tac(srw_ss())[]
    \\ fs [LET_DEF]
    \\ pairarg_tac \\ fs [] \\ rename1 `comp c n4 l c1 = (q4,l4)`
    \\ pairarg_tac \\ fs [] \\ rename1 `comp c _ _ _ = (q5,l5)`
    \\ full_simp_tac(srw_ss())[dataSemTheory.evaluate_def,wordSemTheory.evaluate_def]
    \\ Cases_on `get_var n s.locals` \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[] \\ imp_res_tac state_rel_get_var_IMP
    \\ full_simp_tac(srw_ss())[wordSemTheory.get_var_imm_def,
          asmTheory.word_cmp_def]
    \\ imp_res_tac get_var_T_OR_F
    \\ fs[GSYM AND_IMP_INTRO]
    \\ Cases_on `x = Boolv T` \\ full_simp_tac(srw_ss())[] THEN1
     (qpat_x_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n4`,`l`] mp_tac)
      \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[])
    \\ Cases_on `x = Boolv F` \\ full_simp_tac(srw_ss())[] THEN1
     (qpat_x_assum `state_rel c l1 l2 s t [] locs` (fn th =>
               first_x_assum (fn th1 => mp_tac (MATCH_MP th1 th)))
      \\ strip_tac \\ pop_assum (qspecl_then [`n4`,`l4`] mp_tac)
      \\ rpt strip_tac \\ rev_full_simp_tac(srw_ss())[]))
  THEN1 (* Call *)
   (`t.clock = s.clock` by fs [state_rel_def]
    \\ once_rewrite_tac [data_to_wordTheory.comp_def] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `ret`
    \\ full_simp_tac(srw_ss())[dataSemTheory.evaluate_def,wordSemTheory.evaluate_def,
           wordSemTheory.add_ret_loc_def,get_vars_inc_clock]
    THEN1 (* ret = NONE *)
     (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]
      \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac state_rel_0_get_vars_IMP \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `find_code dest x s.code` \\ full_simp_tac(srw_ss())[]
      \\ rename1 `_ = SOME x9` \\ Cases_on `x9` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[]
      \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def]
      \\ drule (GEN_ALL find_code_thm) \\ rpt (disch_then drule)
      \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `s.clock = 0` \\ fs[] \\ srw_tac[][] \\ fs[]
      THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
      \\ Cases_on `evaluate (r,call_env q (dec_clock s))` \\ fs[]
      \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
      \\ srw_tac[][] \\ full_simp_tac(srw_ss())[] \\ res_tac
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac \\ impl_tac
      >-
        fs[wordSemTheory.call_env_def,wordSemTheory.dec_clock_def]
      \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs[]
      \\ `t.clock <> 0` by full_simp_tac(srw_ss())[state_rel_def]
      \\ Cases_on `res1` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ fs[]
      \\ every_case_tac \\ full_simp_tac(srw_ss())[mk_loc_def]
      \\ fs [wordSemTheory.jump_exc_def,wordSemTheory.call_env_def,
             wordSemTheory.dec_clock_def]
      \\ BasicProvers.EVERY_CASE_TAC \\ full_simp_tac(srw_ss())[mk_loc_def])
    \\ Cases_on `x` \\ full_simp_tac(srw_ss())[LET_DEF]
    \\ `domain (adjust_set r) <> {}` by fs[adjust_set_def,domain_fromAList]
    \\ Cases_on `handler` \\ full_simp_tac(srw_ss())[wordSemTheory.evaluate_def]
    \\ Cases_on `get_vars args s.locals` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac state_rel_get_vars_IMP \\ full_simp_tac(srw_ss())[]
    \\ full_simp_tac(srw_ss())[wordSemTheory.add_ret_loc_def]
    THEN1 (* no handler *)
     (Cases_on `bvlSem$find_code dest x s.code` \\ fs[]
      \\ rename1 `_ = SOME x9` \\ Cases_on `x9` \\ full_simp_tac(srw_ss())[]
      \\ rename1 `_ = SOME (actual_args,called_prog)`
      \\ imp_res_tac bvl_find_code
      \\ `¬bad_dest_args dest (MAP adjust_var args)` by
        (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
        imp_res_tac get_vars_IMP_LENGTH>>
        metis_tac[LENGTH_NIL])
      \\ Q.MATCH_ASSUM_RENAME_TAC `bvlSem$find_code dest xs s.code = SOME (ys,prog)`
      \\ Cases_on `dataSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ `t.clock = s.clock` by full_simp_tac(srw_ss())[state_rel_def]
      \\ full_simp_tac(srw_ss())[]
      \\ rpt_drule find_code_thm_ret
      \\ disch_then (qspecl_then [`n`,`l`] strip_assume_tac) \\ fs []
      \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
      \\ Cases_on `evaluate (prog,call_env ys (push_env x F (dec_clock s)))`
      \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ full_simp_tac(srw_ss())[]
      \\ res_tac (* inst ind hyp *)
      \\ pop_assum kall_tac
      \\ pop_assum mp_tac \\ impl_tac >-
        fs[wordSemTheory.call_env_def,wordSemTheory.push_env_def,wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def]
      \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac)
      \\ full_simp_tac(srw_ss())[]
      \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
      THEN1
       (sg `s1.ffi = r'.ffi` \\ full_simp_tac(srw_ss())[]
        \\ every_case_tac \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ full_simp_tac(srw_ss())[set_var_def]
        \\ imp_res_tac dataPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
        \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[])
      \\ reverse (Cases_on `x'` \\ full_simp_tac(srw_ss())[])
      THEN1 (Cases_on `e` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
        \\ full_simp_tac(srw_ss())[jump_exc_call_env,jump_exc_dec_clock,jump_exc_push_env_NONE]
        \\ Cases_on `jump_exc t = NONE` \\ full_simp_tac(srw_ss())[]
        \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp]
        \\ `LENGTH locs = LENGTH s.stack` by
           (full_simp_tac(srw_ss())[state_rel_def] \\ imp_res_tac LIST_REL_LENGTH \\ full_simp_tac(srw_ss())[]) \\ full_simp_tac(srw_ss())[]
        \\ TRY(rename1 `Rraise`
               \\ `LENGTH r'.stack < LENGTH locs`
                 by(imp_res_tac eval_exc_stack_shorter \\ fs[]))
        \\ imp_res_tac LASTN_TL \\ full_simp_tac(srw_ss())[]
        \\ every_case_tac \\ fs[])
      \\ Cases_on `pop_env r'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ rpt_drule state_rel_pop_env_set_var_IMP \\ fs []
      \\ disch_then (qspec_then `q` strip_assume_tac) \\ fs []
      \\ imp_res_tac evaluate_IMP_domain_EQ \\ full_simp_tac(srw_ss())[])
    (* with handler *)
    \\ PairCases_on `x` \\ full_simp_tac(srw_ss())[]
    \\ `?prog1 h1. comp c n (l + 2) x1 = (prog1,h1)` by METIS_TAC [PAIR]
    \\ fs[wordSemTheory.evaluate_def,wordSemTheory.add_ret_loc_def]
    \\ Cases_on `bvlSem$find_code dest x' s.code` \\ fs[] \\ Cases_on `x` \\ fs[]
    \\ imp_res_tac bvl_find_code
    \\ `¬bad_dest_args dest (MAP adjust_var args)` by
        (full_simp_tac(srw_ss())[wordSemTheory.bad_dest_args_def]>>
        imp_res_tac get_vars_IMP_LENGTH>>
        metis_tac[LENGTH_NIL])
    \\ Q.MATCH_ASSUM_RENAME_TAC `bvlSem$find_code dest xs s.code = SOME (ys,prog)`
    \\ Cases_on `dataSem$cut_env r s.locals` \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac cut_env_IMP_cut_env \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    \\ rpt_drule find_code_thm_handler \\ fs []
    \\ disch_then (qspecl_then [`x0`,`n`,`prog1`,`n`,`l`] strip_assume_tac) \\ fs []
    \\ Cases_on `s.clock = 0` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
    THEN1 (fs[call_env_def,wordSemTheory.call_env_def,state_rel_def])
    \\ Cases_on `evaluate (prog,call_env ys (push_env x T (dec_clock s)))`
    \\ full_simp_tac(srw_ss())[] \\ Cases_on `q'` \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `x' = Rerr (Rabort Rtype_error)` \\ full_simp_tac(srw_ss())[]
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ impl_tac >-
        fs[wordSemTheory.call_env_def,wordSemTheory.push_env_def,wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def]
    \\ disch_then (qspecl_then [`n1`,`n2`] strip_assume_tac) \\ fs[]
    \\ Cases_on `res1 = SOME NotEnoughSpace` \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[]
      \\ sg `r'.ffi.io_events ≼ s1.ffi.io_events`
      \\ TRY (imp_res_tac IS_PREFIX_TRANS \\ full_simp_tac(srw_ss())[] \\ NO_TAC)
      \\ every_case_tac \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac dataPropsTheory.evaluate_io_events_mono \\ full_simp_tac(srw_ss())[set_var_def]
      \\ imp_res_tac wordPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[]
      \\ imp_res_tac dataPropsTheory.pop_env_const \\ full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
      \\ metis_tac [])
    \\ Cases_on `x'` \\ full_simp_tac(srw_ss())[] THEN1
     (Cases_on `pop_env r'` \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
      \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
      \\ rpt_drule state_rel_pop_env_set_var_IMP \\ fs []
      \\ disch_then (qspec_then `q` strip_assume_tac) \\ fs []
      \\ imp_res_tac evaluate_IMP_domain_EQ \\ full_simp_tac(srw_ss())[])
    \\ reverse (Cases_on `e`) \\ full_simp_tac(srw_ss())[]
    THEN1 (full_simp_tac(srw_ss())[] \\ srw_tac[][] \\ every_case_tac \\ fs[])
    \\ full_simp_tac(srw_ss())[mk_loc_jump_exc]
    \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
    \\ qpat_x_assum `!x y z.bbb` (K ALL_TAC)
    \\ full_simp_tac(srw_ss())[jump_exc_push_env_NONE_simp,jump_exc_push_env_SOME]
    \\ imp_res_tac eval_push_env_T_Raise_IMP_stack_length
    \\ `LENGTH s.stack = LENGTH locs` by
         (full_simp_tac(srw_ss())[state_rel_def]
          \\ imp_res_tac LIST_REL_LENGTH \\ fs[]) \\ fs []
    \\ full_simp_tac(srw_ss())[LASTN_ADD1] \\ srw_tac[][]
    \\ first_x_assum (qspec_then `x0` assume_tac)
    \\ res_tac (* inst ind hyp *)
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac \\ impl_tac >-
      (imp_res_tac wordSemTheory.evaluate_clock>>
      fs[wordSemTheory.set_var_def,wordSemTheory.call_env_def,wordSemTheory.push_env_def,wordSemTheory.env_to_list_def,wordSemTheory.dec_clock_def])
    \\ disch_then (qspecl_then [`n`,`l+2`] strip_assume_tac) \\ rfs []
    \\ `jump_exc (set_var (adjust_var x0) w t1) = jump_exc t1` by
          fs[wordSemTheory.set_var_def,wordSemTheory.jump_exc_def]
    \\ full_simp_tac(srw_ss())[] \\ rpt strip_tac \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac evaluate_IMP_domain_EQ_Exc \\ full_simp_tac(srw_ss())[]
    \\ srw_tac[][] \\ full_simp_tac(srw_ss())[]
    \\ Cases_on `res` \\ full_simp_tac(srw_ss())[]
    \\ rpt (CASE_TAC \\ full_simp_tac(srw_ss())[])
    \\ imp_res_tac mk_loc_eq_push_env_exc_Exception \\ full_simp_tac(srw_ss())[]
    \\ imp_res_tac eval_push_env_SOME_exc_IMP_s_key_eq
    \\ imp_res_tac s_key_eq_handler_eq_IMP
    \\ full_simp_tac(srw_ss())[jump_exc_inc_clock_EQ_NONE] \\ metis_tac []));

val compile_correct_lemma = Q.store_thm("compile_correct_lemma",
  `!s c l1 l2 res s1 (t:('a,'c,'ffi) wordSem$state) start.
      (dataSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      t.termdep > 1 /\
      state_rel c l1 l2 s t [] [] ==>
      ?t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,t) = (res1,t1)) /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events) /\
        (res1 <> SOME NotEnoughSpace ==>
         case res of
        | NONE => (res1 = NONE)
        | SOME (Rval v) => t1.ffi = s1.ffi /\
                           ?w. (res1 = SOME (Result (Loc l1 l2) w))
        | SOME (Rerr (Rraise v)) => (?v w. res1 = SOME (Exception v w))
        | SOME (Rerr (Rabort(Rffi_error f))) => (res1 = SOME(FinalFFI f) /\ t1.ffi = s1.ffi)
        | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)`,
  rpt strip_tac
  \\ drule data_compile_correct \\ full_simp_tac(srw_ss())[]
  \\ ntac 2 (disch_then drule) \\ full_simp_tac(srw_ss())[comp_def]
  \\ strip_tac
  \\ qexists_tac `t1`
  \\ qexists_tac `res1`
  \\ full_simp_tac(srw_ss())[] \\ strip_tac \\ full_simp_tac(srw_ss())[]
  \\ every_case_tac \\ full_simp_tac(srw_ss())[]
  \\ full_simp_tac(srw_ss())[state_rel_def]);

val state_rel_ext_def = Define `
  state_rel_ext c l1 l2 s u <=>
    ?t l.
      state_rel c l1 l2 s t [] [] /\
      domain t.code = domain l /\
      t.termdep > 1 /\
      (?tt kk aa co.
         u.compile_oracle =
           (I ## MAP (λp. full_compile_single tt kk aa co (p,NONE))) ∘
             t.compile_oracle /\
         t.compile = (λconf progs. u.compile conf
           (MAP (λp. full_compile_single tt kk aa co (p,NONE)) progs))) /\
      (!n v. lookup n t.code = SOME v ==>
             ∃t' k' a' c' col.
             lookup n l = SOME (SND (full_compile_single t' k' a' c' ((n,v),col)))) /\
      u = t with <| code := l; termdep:=0; compile:=u.compile; compile_oracle := u.compile_oracle|>`

val compile_correct = Q.store_thm("compile_correct",
  `!x s l1 l2 res s1 (t:('a,'c,'ffi) wordSem$state) start.
      (dataSem$evaluate (Call NONE (SOME start) [] NONE,s) = (res,s1)) /\
      res <> SOME (Rerr (Rabort Rtype_error)) /\
      state_rel_ext x l1 l2 s t ==>
      ?ck t1 res1.
        (wordSem$evaluate (Call NONE (SOME start) [0] NONE,
           (inc_clock ck t)) = (res1,t1)) /\
        (res1 = SOME NotEnoughSpace ==>
           t1.ffi.io_events ≼ s1.ffi.io_events) /\
        (res1 <> SOME NotEnoughSpace ==>
         case res of
         | NONE => (res1 = NONE)
         | SOME (Rval v) => t1.ffi = s1.ffi /\
                            ?w. (res1 = SOME (Result (Loc l1 l2) w))
         | SOME (Rerr (Rraise v)) => (?v w. res1 = SOME (Exception v w))
         | SOME (Rerr (Rabort(Rffi_error f))) => (res1 = SOME(FinalFFI f) /\ t1.ffi = s1.ffi)
         | SOME (Rerr (Rabort e)) => (res1 = SOME TimeOut) /\ t1.ffi = s1.ffi)`,
  gen_tac
  \\ full_simp_tac(srw_ss())[state_rel_ext_def,PULL_EXISTS] \\ srw_tac[][]
  \\ fs [wordSemTheory.state_component_equality]
  \\ rename1 `state_rel x0 l1 l2 s t2 [] []`
  \\ sg `?l2. code_rel t2.code l2 /\
              map (I ## remove_must_terminate) l2 = l`
  THEN1 (
    fs [boolTheory.SKOLEM_THM,METIS_PROVE [] ``(b ==> ?x. P x) <=> ?x. b ==> P x``]
    \\ fs [spt_eq,lookup_map,eq_shape_map]
    \\ simp [spt_eq,lookup_map,domain_lookup,EXTENSION,PULL_EXISTS,FORALL_PROD]
    \\ fs [word_to_wordProofTheory.code_rel_def,
         word_to_wordTheory.full_compile_single_def]
    \\ sg `?l3. eq_shape l3 l /\ ∀n v.
          lookup n t2.code = SOME v ⇒
          lookup n l3 = SOME (SND
            ((λ(name_num,arg_count,reg_prog).
                (name_num,arg_count,reg_prog))
               (compile_single (f n v) (f' n v) (f'' n v) (f''' n v)
                   ((n,v),f'''' n v))))`
    THEN1
     (qho_match_abbrev_tac `?l3. _ l3 /\ !n v. _ n v ==> _ n l3 = SOME (ff n v)`
      \\ qexists_tac `copy_shape (mapi ff t2.code) l`
      \\ conj_tac THEN1 (fs [] \\ match_mp_tac shape_eq_copy_shape \\ fs [])
      \\ fs [lookup_copy_shape]
      \\ rw [] \\ fs [lookup_mapi])
    \\ qexists_tac `l3`
    \\ rw [] \\ res_tac \\ fs []
    THEN1 (CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) \\ fs [] \\ metis_tac [])
    \\ fs [spt_eq,lookup_map,domain_lookup,EXTENSION,PULL_EXISTS,FORALL_PROD]
    \\ fs [eq_shape_map] \\ rw []
    \\ imp_res_tac eq_shape_IMP_domain
    \\ fs [spt_eq,lookup_map,domain_lookup,EXTENSION,PULL_EXISTS,FORALL_PROD]
    \\ fs [EXISTS_PROD]
    \\ `?v11 v12. lookup k t.code = SOME (v11,v12)` by metis_tac []
    \\ `?v21 v22. lookup k t2.code = SOME (v21,v22)` by metis_tac []
    \\ res_tac
    \\ fs [] \\ rveq \\ pairarg_tac \\ fs [] \\ rveq \\ fs [])
  \\ drule (compile_word_to_word_thm |> GEN_ALL |> SIMP_RULE std_ss [])
  \\ `domain l2' = domain l` by (rveq \\ fs [domain_map])
  \\ `domain t2.code = domain l2'` by fs []
  \\ `gc_fun_const_ok t2.gc_fun` by
         fs [state_rel_def,gc_fun_const_ok_word_gc_fun]
  \\ rpt (disch_then drule)
  \\ disch_then (qspec_then `start` mp_tac)
  \\ strip_tac \\ fs [] \\ rveq
  \\ `state_rel x0 l1 l2 s (t2 with permute := perm') [] []` by
   (full_simp_tac(srw_ss())[state_rel_def] \\ rev_full_simp_tac(srw_ss())[]
    \\ Cases_on `s.stack` \\ full_simp_tac(srw_ss())[] \\ metis_tac [])
  \\ drule compile_correct_lemma \\ fs []
  \\ disch_then (drule o ONCE_REWRITE_RULE [CONJ_COMM])
  \\ fs [] \\ strip_tac \\ fs []
  THEN1 (rveq \\ fs [] \\ every_case_tac \\ fs[])
  \\ pairarg_tac \\ fs [inc_clock_def]
  \\ qexists_tac `clk`
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t6)`
  \\ qpat_x_assum `evaulate _ = _` mp_tac
  \\ qmatch_goalsub_abbrev_tac `evaluate (_,t7)`
  \\ qsuff_tac `t6 = t7` THEN1 (every_case_tac \\ fs [])
  \\ unabbrev_all_tac \\ fs []
  \\ fs [wordSemTheory.state_component_equality]);

val state_rel_ext_with_clock = Q.prove(
  `state_rel_ext a b c s1 s2 ==>
    state_rel_ext a b c (s1 with clock := k) (s2 with clock := k)`,
  full_simp_tac(srw_ss())[state_rel_ext_def] \\ srw_tac[][]
  \\ drule state_rel_with_clock
  \\ strip_tac \\ asm_exists_tac \\ full_simp_tac(srw_ss())[]
  \\ qexists_tac `l` \\ full_simp_tac(srw_ss())[]
  \\ fs [wordSemTheory.state_component_equality]
  \\ metis_tac []);

(* observational semantics preservation *)

val compile_semantics_lemma = Q.store_thm("compile_semantics_lemma",
  `state_rel_ext conf 1 0 (initial_state (ffi:'ffi ffi_state) (fromAList prog) co cc t.clock) (t:('a,'c,'ffi) wordSem$state) /\
   semantics ffi (fromAList prog) co cc start <> Fail ==>
   semantics t start IN
     extend_with_resource_limit { semantics ffi (fromAList prog) co cc start }`,
  simp[GSYM AND_IMP_INTRO] >> ntac 1 strip_tac >>
  simp[dataSemTheory.semantics_def] >>
  IF_CASES_TAC >> full_simp_tac(srw_ss())[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac
 >- (
    qx_gen_tac`r`>>simp[]>>strip_tac>>
    strip_tac >>
    simp[wordSemTheory.semantics_def] >>
    IF_CASES_TAC >- (
      full_simp_tac(srw_ss())[] >> rveq >> full_simp_tac(srw_ss())[] >>
      qhdtm_x_assum`dataSem$evaluate`kall_tac >>
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
      `r' <> Rerr(Rabort Rtype_error)` by(CCONTR_TAC >> fs[]) >>
      `r' <> Rerr(Rabort Rtimeout_error)` by(CCONTR_TAC >> fs[]) >>
      drule(dataPropsTheory.evaluate_add_clock)>>simp[]>>
      disch_then(qspec_then`k'`mp_tac)>>simp[]>>strip_tac>>
      drule(compile_correct)>>simp[]>>
      drule(GEN_ALL state_rel_ext_with_clock)>>simp[]>>
      disch_then(qspec_then `k+k'` assume_tac)>>disch_then drule>>
      simp[inc_clock_def]>>strip_tac>>
      qpat_x_assum `evaluate _ = (r,_)` assume_tac>>
      dxrule(GEN_ALL wordPropsTheory.evaluate_add_clock)>>
      disch_then(qspec_then `ck+k` mp_tac)>>
      impl_tac>-(CCONTR_TAC>>fs[])>>
      simp[inc_clock_def]>>strip_tac>>
      rpt(PURE_FULL_CASE_TAC>>fs[]>>rveq>>fs[])) >>
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
    qpat_x_assum`∀x y. _`(qspec_then`k`mp_tac)>>
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
    `t'.ffi.io_events ≼ t1.ffi.io_events` by (
      qmatch_assum_abbrev_tac`evaluate (exps,tt) = (_,t')` >>
      Q.ISPECL_THEN[`exps`,`tt`]mp_tac wordPropsTheory.evaluate_add_clock_io_events_mono >>
      full_simp_tac(srw_ss())[inc_clock_def,Abbr`tt`] >>
      disch_then(qspec_then`ck`mp_tac)>>simp[]) >>
    full_simp_tac(srw_ss())[] >>
    first_assum(qspec_then`k`mp_tac) >>
    first_x_assum(qspec_then`k+ck`mp_tac) >>
    fsrw_tac[ARITH_ss][inc_clock_def] >>
    qhdtm_x_assum`wordSem$evaluate`mp_tac >>
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
        dataPropsTheory.evaluate_add_clock_io_events_mono,
        dataPropsTheory.initial_state_with_simp,
        dataPropsTheory.initial_state_simp]) >>
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
      EVAL``((t:('a,'c,'ffi) wordSem$state) with clock := k).clock``,
      EVAL``((t:('a,'c,'ffi) wordSem$state) with clock := k) with clock := k2``,
      dataPropsTheory.evaluate_add_clock_io_events_mono,
      dataPropsTheory.initial_state_with_simp,
      dataPropsTheory.initial_state_simp]) >>
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
    rpt(first_x_assum(qspec_then`k+ck`mp_tac)>>simp[]) >>
    every_case_tac >> fs[]) >>
  (fn g => subterm (fn tm => Cases_on`^(Term.subst [{redex = #1(dest_exists(#2 g)), residue = ``k:num``}] (assert(has_pair_type)tm))`) (#2 g) g) >>
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

val code_rel_ext_def = Define`
  code_rel_ext code l ⇔
  (∀n p_1 p_2.
        SOME (p_1,p_2) = lookup n code ⇒
        ∃t' k' a' c' col.
          SOME
            (SND (full_compile_single t' k' a' c' ((n,p_1,p_2),col))) =
          lookup n l)`

val compile_semantics = Q.store_thm("compile_semantics",`
   (* Definitely correct *)
   t:('a,'c,'ffi) state.handler = 0 ∧ t.gc_fun = word_gc_fun c ∧
   init_store_ok c t.store t.memory t.mdomain t.code_buffer t.data_buffer ∧
   good_dimindex (:α) ∧
   lookup 0 t.locals = SOME (Loc 1 0) ∧ t.stack = [] ∧ conf_ok (:α) c ∧
   t.termdep = 0 ∧
   (* Construct an intermediate state *)
   code_rel c (fromAList prog) x1 ∧
   (* Explicitly instantiate code_oracle_rel at the intermediate state *)
   cc = (λcfg.
        OPTION_MAP (I ## MAP upper_w2w ## I) ∘ tcc cfg ∘
        MAP (compile_part c)) ∧
   Abbrev (tco = (I ## MAP (compile_part c)) ∘ co) ∧
   (∀n. EVERY (λ(n,_). data_num_stubs ≤ n) (SND (co n))) ∧
   (* Construct the next composition *)
   code_rel_ext x1 t.code ∧
   domain x1 = domain t.code ∧
   t.compile_oracle = (I ## MAP (λp. full_compile_single tt kk aa coo (p,NONE))) o tco ∧
   Abbrev (tcc = (λconf progs.
    t.compile conf (MAP (λp. full_compile_single tt kk aa coo (p,NONE)) progs))) ∧
   Fail ≠ semantics t.ffi (fromAList prog) co cc start ⇒
   semantics t start ∈
   extend_with_resource_limit
   {semantics t.ffi (fromAList prog) co cc start}`,
   rw[]>>
   match_mp_tac (GEN_ALL compile_semantics_lemma)>>
   qexists_tac`c`>>fs[state_rel_ext_def]>>rw[]>>
   fs[code_rel_ext_def]>>
   qexists_tac`t with <|code := x1; termdep := 2; compile_oracle := tco; compile := tcc |>`>>
   simp[wordSemTheory.state_component_equality]>>
   CONJ_TAC >-
     (qmatch_goalsub_abbrev_tac`state_rel _ _ _ _ ttt`>>
     `t.clock = ttt.clock` by
       fs[Abbr`ttt`]>>
     simp[]>>
     match_mp_tac state_rel_init>>
     unabbrev_all_tac>>fs[code_oracle_rel_def] >>
     fs [init_store_ok_def])>>
   CONJ_TAC>-
     (unabbrev_all_tac>>fs[]>>
     metis_tac[])>>
   fs[FORALL_PROD]>>
   metis_tac[]);

val code_rel_ext_def = definition"code_rel_ext_def";

val _ = (max_print_depth := 15);

val extract_labels_def = wordPropsTheory.extract_labels_def;

val extract_labels_MemEqList = store_thm("extract_labels_MemEqList[simp]",
  ``!a x. extract_labels (MemEqList a x) = []``,
  Induct_on `x`
  \\ asm_rewrite_tac [MemEqList_def,extract_labels_def,APPEND]);

val extract_labels_StoreEach = store_thm("extract_labels_StoreEach",
  ``!xs a d. extract_labels (StoreEach a xs d) = []``,
  Induct \\ fs [StoreEach_def,extract_labels_def]);

(* TODO: goes away on inlineenc branch *)
val extract_labels_WordOp64_on_32 = Q.prove(`
  extract_labels (WordOp64_on_32 f) = []`,
  simp[WordOp64_on_32_def]>>Cases_on`f`>>simp[]>>
  EVAL_TAC);

val extract_labels_WordShift64_on_32 = Q.prove(`
  extract_labels (WordShift64_on_32 f g) = []`,
  simp[WordShift64_on_32_def]>>
  Cases_on`f`>>simp[]>>
  IF_CASES_TAC>>EVAL_TAC);

val extract_labels_assignWordOp = Q.prove(`
  assign a b c d (WordOp e f) g h = (i,j) ⇒
  extract_labels i = [] ∧ c ≤ j`,
  simp[assign_def]>>
  Cases_on`dimindex(:'a) = 64`>> simp[]
  >- (every_case_tac>>rw[]>> EVAL_TAC)
  >>
    every_case_tac>>rw[]>>
    simp[extract_labels_def,list_Seq_def,extract_labels_WordOp64_on_32]>>
    EVAL_TAC);

val extract_labels_assignWordShift = Q.prove(`
  assign a b c d (WordShift e f k) g h = (i,j) ⇒
  extract_labels i = [] ∧ c ≤ j`,
  simp[assign_def]>>
  Cases_on`dimindex(:'a) >= 64`>> simp[]
  >- (every_case_tac>>rw[]>> EVAL_TAC)
  >>
    every_case_tac>>rw[]>>
    simp[extract_labels_def,list_Seq_def,extract_labels_WordShift64_on_32]>>
    EVAL_TAC);

val data_to_word_lab_pres_lem = Q.store_thm("data_to_word_lab_pres_lem",`
  ∀c n l p.
  l ≠ 0 ⇒
  let (cp,l') = comp c n l p in
  l ≤ l' ∧
  EVERY (λ(l1,l2). l1 = n ∧ l ≤ l2 ∧ l2 < l') (extract_labels cp) ∧
  ALL_DISTINCT (extract_labels cp)`,
  HO_MATCH_MP_TAC comp_ind>>Cases_on`p`>>rw[]>>
  once_rewrite_tac[comp_def]>>fs[extract_labels_def]
  >-
    (BasicProvers.EVERY_CASE_TAC>>fs[]>>rveq>>fs[extract_labels_def]>>
    rpt(pairarg_tac>>fs[])>>rveq>>fs[extract_labels_def]>>
    fs[EVERY_MEM,FORALL_PROD]>>rw[]>>
    res_tac>>fs[]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[])
  >-
    (qmatch_goalsub_rename_tac `assign _ _ _ _ opname _ _` >>
    Cases_on `opname`>>
    TRY(
      rename1`WordOp _ _`>>
      pairarg_tac>>drule extract_labels_assignWordOp>>
      simp[])>>
    TRY(
      rename1`WordShift _ _ _`>>
      pairarg_tac>>drule extract_labels_assignWordShift>>
      simp[])>>
    fs[extract_labels_def,GiveUp_def,assign_def,assign_def_extras]>>
    BasicProvers.EVERY_CASE_TAC>>
    fs[extract_labels_def,list_Seq_def,extract_labels_StoreEach,Maxout_bits_code_def])
  >>
    (rpt (pairarg_tac>>fs[])>>rveq>>
          fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
             SilentFFI_def,list_Seq_def]>>
    rw[]>> res_tac>>fs[]>>
    CCONTR_TAC>>fs[]>>res_tac>>fs[] >>
    fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
       SilentFFI_def,list_Seq_def]>>
    every_case_tac >> fs [] >>
    fs[extract_labels_def,EVERY_MEM,FORALL_PROD,ALL_DISTINCT_APPEND,
       SilentFFI_def,list_Seq_def]));

open match_goal;

val labels_rel_emp = Q.prove(`
  labels_rel [] ls ⇒ ls = [] `,
  fs[word_simpProofTheory.labels_rel_def]);

val stub_labels = Q.store_thm("stub_labels",`
  EVERY (λ(n,m,p).
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels p)  ∧ ALL_DISTINCT (extract_labels p))
    (stubs (:'a) data_conf)`,
  simp[data_to_wordTheory.stubs_def,generated_bignum_stubs_eq]>>
  EVAL_TAC>>
  rw[]>>EVAL_TAC);

val stubs_with_has_fp_ops = store_thm("stubs_with_has_fp_ops[simp]",
  ``stubs (:α) (data_conf with has_fp_ops := b) = stubs (:α) data_conf``,
  EVAL_TAC \\ fs []);

val data_to_word_compile_lab_pres = Q.store_thm("data_to_word_compile_lab_pres",`
  let (c,p) = compile data_conf word_conf asm_conf prog in
    MAP FST p = MAP FST (stubs(:α) data_conf) ++ MAP FST prog ∧
    EVERY (λn,m,(p:α wordLang$prog).
      let labs = extract_labels p in
      EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0) labs ∧
      ALL_DISTINCT labs) p`,
  fs[data_to_wordTheory.compile_def]>>
  qpat_abbrev_tac`datap = _ ++ MAP (A B) prog`>>
  mp_tac (compile_to_word_conventions |>GEN_ALL |> Q.SPECL [`word_conf`,`datap`,`asm_conf`])>>
  rw[]>>
  pairarg_tac>>fs[Abbr`datap`]>>
  fs[EVERY_MEM]>>rw[]
  >-
    (match_mp_tac LIST_EQ>>rw[EL_MAP]>>
    Cases_on`EL x prog`>>Cases_on`r`>>fs[compile_part_def]) >>
  qmatch_assum_abbrev_tac`MAP FST p = MAP FST p1 ++ MAP FST p2`>>
  full_simp_tac std_ss [GSYM MAP_APPEND]>>
  qabbrev_tac`pp = p1 ++ p2` >>
  fs[EL_MAP,MEM_EL,FORALL_PROD]>>
  `EVERY (λ(n,m,p).
    EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0) (extract_labels p)  ∧ ALL_DISTINCT (extract_labels p)) pp` by
    (unabbrev_all_tac>>fs[EVERY_MEM]>>CONJ_TAC
    >-
      (assume_tac stub_labels>>
      fs[EVERY_MEM])
    >>
      fs[MEM_MAP,MEM_EL,EXISTS_PROD]>>rw[]>>fs[compile_part_def]>>
      qmatch_goalsub_abbrev_tac `comp data_conf2` >>
      Q.SPECL_THEN [`data_conf2`,`p_1`,`1n`,`p_2`]assume_tac
        data_to_word_lab_pres_lem>>
      fs[]>>pairarg_tac>>fs[EVERY_EL,PULL_EXISTS]>>
      rw[]>>res_tac>>
      pairarg_tac>>fs[])>>
  fs[LIST_REL_EL_EQN,EVERY_EL]>>
  rpt (first_x_assum(qspec_then`n` assume_tac))>>rfs[]>>
  rfs[EL_MAP]>>
  pairarg_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  rw[] >>fs[word_simpProofTheory.labels_rel_def,SUBSET_DEF,MEM_EL,PULL_EXISTS]>>
  first_x_assum(qspec_then`n'''` assume_tac)>>rfs[]>>
  res_tac>>fs[]>>
  pairarg_tac>>fs[]>>
  qpat_x_assum`A=MAP FST pp` mp_tac>>simp[Once LIST_EQ_REWRITE,EL_MAP]>>
  disch_then(qspec_then`n` assume_tac)>>rfs[]);

val StoreEach_no_inst = Q.prove(`
  ∀a ls off.
  every_inst (inst_ok_less ac) (StoreEach a ls off)`,
  Induct_on`ls`>>rw[StoreEach_def,every_inst_def]);

val MemEqList_no_inst = Q.prove(`
  ∀a x.
  every_inst (inst_ok_less ac) (MemEqList a x)`,
  Induct_on `x` \\ fs [MemEqList_def,every_inst_def]);

val assign_no_inst = Q.prove(`
  ((a.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
   (a.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
   (a.has_fp_ops ⇒ 1 < ac.fp_reg_count) ∧
  addr_offset_ok ac 0w /\ byte_offset_ok ac 0w) ⇒
  every_inst (inst_ok_less ac) (FST(assign a b c d e f g))`,
  fs[assign_def]>>
  Cases_on`e`>>fs[every_inst_def]>>
  rw[]>>fs[every_inst_def,GiveUp_def]>>
  every_case_tac>>
  TRY(Cases_on`f'`)>>
  fs[every_inst_def,list_Seq_def,StoreEach_no_inst,
    Maxout_bits_code_def,GiveUp_def,
    inst_ok_less_def,assign_def_extras,MemEqList_no_inst,
    asmTheory.fp_reg_ok_def,fp_uop_inst_def,fp_cmp_inst_def,
    fp_bop_inst_def]>>
  IF_CASES_TAC>>fs[every_inst_def,list_Seq_def,StoreEach_no_inst,
    Maxout_bits_code_def,GiveUp_def,
    inst_ok_less_def,assign_def_extras,MemEqList_no_inst]);

(*
inst_ok_less_def
*)

val comp_no_inst = Q.store_thm("comp_no_inst",`
  ∀c n m p.
  ((c.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
   (c.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
   (c.has_fp_ops ⇒ 1 < ac.fp_reg_count)) ∧
  addr_offset_ok ac 0w /\ byte_offset_ok ac 0w ⇒
  every_inst (inst_ok_less ac) (FST(comp c n m p))`,
  ho_match_mp_tac comp_ind>>Cases_on`p`>>rw[]>>
  simp[Once comp_def,every_inst_def]>>
  every_case_tac>>fs[]>>
  rpt(pairarg_tac>>fs[])>>
  fs[assign_no_inst]>>
  EVAL_TAC>>fs[] >>
  IF_CASES_TAC >> EVAL_TAC >> fs []);

val bounds_lem = Q.prove(`
  (dimindex(:'a) = 32 ∨ dimindex(:'a) = 64) ∧
  (w:'a word = -3w ∨
  w = -2w ∨
  w = -1w ∨
  w = 0w ∨
  w = 1w ∨
  w = 2w ∨
  w = 3w ∨
  w = 4w ∨
  w = 5w ∨
  w = 6w ∨
  w = 7w)
  ⇒
  -8w ≤ w ∧ w ≤ 8w`,
  rw[]>>
  EVAL_TAC>>
  simp[dimword_def]>>
  EVAL_TAC>>
  simp[dimword_def]>>
  EVAL_TAC>>
  simp[numeral_bitTheory.iSUC,numeralTheory.numeral_evenodd,ODD]);

val data_to_word_compile_conventions = Q.store_thm("data_to_word_compile_conventions",`
  good_dimindex(:'a) ==>
  let (c,p) = compile data_conf wc ac prog in
  EVERY (λ(n,m,prog).
    flat_exp_conventions (prog:'a prog) ∧
    post_alloc_conventions (ac.reg_count - (5+LENGTH ac.avoid_regs)) prog ∧
    ((data_conf.has_longdiv ⇒ (ac.ISA = x86_64)) ∧
    (data_conf.has_div ⇒ (ac.ISA ∈ {ARMv8; MIPS;RISC_V})) ∧
    addr_offset_ok ac 0w /\
    (* NOTE: this condition is
       stricter than necessary, but we have much more byte_offset space
       anyway on all the targets *)
    (∀w. -8w <= w ∧ w <= 8w ==> byte_offset_ok ac w)
    ⇒ full_inst_ok_less ac prog) ∧
    (ac.two_reg_arith ⇒ every_inst two_reg_inst prog)) p`,
 fs[data_to_wordTheory.compile_def]>>
 qpat_abbrev_tac`p= stubs(:'a) data_conf ++B`>>
 pairarg_tac>>fs[]>>
 Q.SPECL_THEN [`wc`,`p`,`ac`] mp_tac (GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
 rw[]>>fs[EVERY_MEM,LAMBDA_PROD,FORALL_PROD]>>rw[]>>
 res_tac>>fs[]>>
 first_assum match_mp_tac>>
 simp[Abbr`p`]>>rw[]
 >-
   (pop_assum mp_tac>>
   qpat_x_assum`data_conf.has_longdiv ⇒ P` mp_tac>>
   qpat_x_assum`data_conf.has_div⇒ P` mp_tac>>
   qpat_x_assum`∀w. _ ==> byte_offset_ok _ _ ` mp_tac>>
   qpat_x_assum`addr_offset_ok _ _` mp_tac>>
   qpat_x_assum`good_dimindex _` mp_tac>>
   rpt(pop_assum kall_tac)>>
   fs[stubs_def,generated_bignum_stubs_eq]>>rw[]>>
   TRY(rename1`ByteCopySub_code`>>
   fs[good_dimindex_def,ByteCopySub_code_def,every_inst_def,list_Seq_def,inst_ok_less_def]>>rw[]>>
   fs[]>>
   first_assum match_mp_tac>>
   metis_tac[bounds_lem])>>
   EVAL_TAC>>rw[]>>
   fs[good_dimindex_def] \\ fs[] \\ EVAL_TAC \\ fs[dimword_def] >>
   rw[] >> EVAL_TAC >> simp[]>>
   pairarg_tac \\ fs[]>>
   qmatch_goalsub_abbrev_tac `min ≤ ww ∧ ww ≤ max`>>
   first_x_assum(qspecl_then[`ww`] mp_tac)>>simp[Abbr`ww`]>>
   impl_tac>>simp[asmTheory.offset_ok_def]>>
   metis_tac[bounds_lem])
 >>
   fs[MEM_MAP]>>PairCases_on`y`>>fs[compile_part_def]>>
   match_mp_tac comp_no_inst>>fs[]>>
   first_x_assum match_mp_tac>>
   fs[good_dimindex_def]>>
   metis_tac[bounds_lem]);

val data_to_word_names = Q.store_thm("data_to_word_names",
  `word_to_word$compile c1 c2 (stubs(:α)c.data_conf ++ MAP (compile_part c3) prog) = (col,p) ==>
    MAP FST p = (MAP FST (stubs(:α)c.data_conf))++MAP FST prog`,
  rw[]>>assume_tac(GEN_ALL word_to_wordProofTheory.compile_to_word_conventions)>>
  pop_assum (qspecl_then [`c1`,`stubs(:α)c.data_conf++(MAP (compile_part c3) prog)`,`c2`] assume_tac)>>rfs[]>>
  fs[MAP_MAP_o,MAP_EQ_f,FORALL_PROD,data_to_wordTheory.compile_part_def]);

val ALL_DISTINCT_MAP_FST_stubs = Q.store_thm("ALL_DISTINCT_MAP_FST_stubs",
  `ALL_DISTINCT (MAP FST (stubs a c))`,
  Cases_on`a` \\ EVAL_TAC);

val MAP_FST_stubs_bound = Q.store_thm("MAP_FST_stubs_bound",
  `MEM n (MAP FST (stubs a c)) ⇒ n < data_num_stubs`,
  Cases_on`a` \\ EVAL_TAC
  \\ strip_tac \\ rveq \\ EVAL_TAC);

val code_rel_ext_word_to_word = Q.store_thm("code_rel_ext_word_to_word",
  `∀code c1 col code'.
   compile c1 c2 code = (col,code') ⇒
   code_rel_ext (fromAList code) (fromAList code')`,
  simp[word_to_wordTheory.compile_def,code_rel_ext_def] \\
  ntac 2 gen_tac \\
  map_every qspec_tac (map swap [(`r`,`c1.reg_alg`), (`col`,`c1.col_oracle`)]) \\
  Induct_on`code` \\ rw[] \\
  pairarg_tac \\ fs[lookup_fromAList] \\ rw[] \\
  fs[word_to_wordTheory.next_n_oracle_def] \\ rw[] \\
  simp[GENLIST_CONS] \\ Cases_on`h` \\ fs[] \\
  simp[word_to_wordTheory.full_compile_single_def,SimpRHS] \\
  pairarg_tac \\ fs[] \\
  qmatch_asmsub_rename_tac`((q,p),col 0)` \\
  PairCases_on`p` \\ fs[word_to_wordTheory.compile_single_def] \\
  rveq \\ fs[] \\ IF_CASES_TAC \\ fs[] \\
  simp[word_to_wordTheory.full_compile_single_def,word_to_wordTheory.compile_single_def] \\
  metis_tac[]);

val max_heap_limit_has_fp_ops = store_thm("max_heap_limit_has_fp_ops[simp]",
  ``max_heap_limit (:α) (conf with has_fp_ops := b) =
    max_heap_limit (:α) conf``,
  EVAL_TAC);

val _ = export_theory();
