open preamble integerTheory intLib
     semanticPrimitivesTheory
     patSemTheory patPropsTheory pat_to_closTheory
     closLangTheory closSemTheory closPropsTheory

val _ = new_theory"pat_to_closProof"

(* value translation *)

val compile_v_def = tDefine"compile_v"`
  (compile_v (Litv (IntLit i)) = (Number i):closSem$v) ∧
  (compile_v (Litv (Word8 w)) = (Number (& (w2n w)))) ∧
  (compile_v (Litv (Word64 w)) = (Word64 w)) ∧
  (compile_v (Litv (Char c)) = (Number (& ORD c))) ∧
  (compile_v (Litv (StrLit s)) = (ByteVector (MAP (n2w o ORD) s))) ∧
  (compile_v (Loc m) = (RefPtr m)) ∧
  (compile_v (Conv cn vs) = (Block cn (MAP (compile_v) vs))) ∧
  (compile_v (Vectorv vs) = (Block vector_tag (MAP (compile_v) vs))) ∧
  (compile_v (Closure vs e) = (Closure NONE [] (MAP (compile_v) vs) 1 (compile e))) ∧
  (compile_v (Recclosure vs es k) = (Recclosure NONE [] (MAP (compile_v) vs) (MAP (λe. (1,compile e)) es) k))`
    (WF_REL_TAC`measure (patSem$v_size)` >> simp[patSemTheory.v_size_def] >>
     rpt conj_tac >> rpt gen_tac >>
     Induct_on`vs` >> simp[patSemTheory.v_size_def] >>
     rw[] >> res_tac >> fs[] >> simp[patSemTheory.v_size_def])
val _ = export_rewrites["compile_v_def"]

val compile_sv_def = Define `
  (compile_sv (Refv v) = ValueArray [compile_v v]) ∧
  (compile_sv (Varray vs) = ValueArray (MAP compile_v vs)) ∧
  (compile_sv (W8array bs) = ByteArray F bs)`
val _ = export_rewrites["compile_sv_def"];

val compile_state_def = Define`
  compile_state max_app (s:'ffi patSem$state) =
    <| globals := MAP (OPTION_MAP compile_v) s.globals;
       refs := alist_to_fmap (GENLIST (λi. (i, compile_sv (EL i s.refs))) (LENGTH s.refs));
       ffi := s.ffi;
       clock := s.clock;
       code := FEMPTY;
       max_app := max_app
    |>`;

val compile_state_const = Q.store_thm("compile_state_const[simp]",
  `(compile_state max_app s).clock = s.clock ∧
   (compile_state max_app s).max_app = max_app`,
  EVAL_TAC);

val compile_state_dec_clock = Q.store_thm("compile_state_dec_clock[simp]",
  `compile_state max_app (dec_clock y) = dec_clock 1 (compile_state max_app y)`,
  EVAL_TAC >> simp[])

val compile_state_with_clock = Q.store_thm("compile_state_with_clock[simp]",
  `compile_state max_app (s with clock := k) = compile_state max_app s with clock := k`,
  EVAL_TAC >> simp[])

val compile_state_ffi = Q.store_thm("compile_state_ffi[simp]",
  `(compile_state w s).ffi = s.ffi`,
  EVAL_TAC);

val FLOOKUP_compile_state_refs = Q.store_thm("FLOOKUP_compile_state_refs",
  `FLOOKUP (compile_state w s).refs =
   OPTION_MAP compile_sv o (combin$C store_lookup s.refs) `,
  rw[FUN_EQ_THM,compile_state_def,ALOOKUP_GENLIST,store_lookup_def] \\ rw[]);

val FDOM_compile_state_refs = Q.store_thm("FDOM_compile_state_refs[simp]",
  `FDOM (compile_state w s).refs = count (LENGTH s.refs)`,
  rw[compile_state_def,MAP_GENLIST,o_DEF,LIST_TO_SET_GENLIST]);

val compile_state_with_refs_snoc = Q.store_thm("compile_state_with_refs_snoc",
  `compile_state w (s with refs := s.refs ++ [x]) =
   compile_state w s with refs :=
     (compile_state w s).refs |+ (LENGTH s.refs, compile_sv x)`,
  rw[compile_state_def,fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST]
  \\ rw[EL_APPEND1,EL_APPEND2]);

(* semantic functions respect translation *)

val do_eq = Q.store_thm("do_eq",
  `(∀v1 v2. do_eq v1 v2 ≠ Eq_type_error ⇒
      (do_eq v1 v2 = do_eq (compile_v v1) (compile_v v2))) ∧
    (∀vs1 vs2. do_eq_list vs1 vs2 ≠ Eq_type_error ⇒
      (do_eq_list vs1 vs2 = do_eq_list (MAP compile_v vs1) (MAP compile_v vs2)))`,
  ho_match_mp_tac patSemTheory.do_eq_ind >>
  simp[patSemTheory.do_eq_def,closSemTheory.do_eq_def] >>
  conj_tac >- (
    Cases >> Cases >> simp[lit_same_type_def,closSemTheory.do_eq_def] >>
    rw[LIST_EQ_REWRITE,EL_MAP,EQ_IMP_THM] \\ rfs[EL_MAP] \\ res_tac
    \\ fs[ORD_11,ORD_BOUND]) >>
  conj_tac >- rw[ETA_AX] >>
  conj_tac >- rw[ETA_AX] >>
  rw[] >>
  Cases_on`v1`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  Cases_on`v2`>>fs[]>>TRY(Cases_on`l:lit`>>fs[])>>
  fs[closSemTheory.do_eq_def,patSemTheory.do_eq_def,lit_same_type_def,ORD_11] >>
  rw[]>>fs[]>>rfs[ETA_AX]>>
  BasicProvers.CASE_TAC>>fs[]>>
  rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]);

val v_to_list_def = closSemTheory.v_to_list_def;

val v_to_char_list = Q.store_thm("v_to_char_list",
  `∀v ls. (v_to_char_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP (Number o $& o ORD) ls))`,
  ho_match_mp_tac v_to_char_list_ind >>
  simp[v_to_char_list_def,v_to_list_def] >>
  rw[] >>
  Cases_on`v`>>fs[v_to_char_list_def] >>
  Cases_on`l`>>fs[v_to_char_list_def,v_to_list_def] >>
  rw[]>>fs[]>>
  Cases_on`h`>>fs[v_to_char_list_def,v_to_list_def] >>
  Cases_on`l`>>fs[v_to_char_list_def,v_to_list_def] >>
  Cases_on`t`>>fs[v_to_char_list_def,v_to_list_def] >>
  Cases_on`t'`>>fs[v_to_char_list_def,v_to_list_def] >>
  rw[]>>fs[]>>
  Cases_on`v_to_char_list h`>>fs[]>> rw[])

val v_to_list = Q.store_thm("v_to_list",
  `∀v ls. (v_to_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP compile_v ls))`,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def,v_to_list_def] >>
  rw[] >> Cases_on`v_to_list v`>>fs[]>> rw[])

val vs_to_w8s = Q.store_thm("vs_to_w8s",
  `∀refs vs ws. vs_to_w8s refs vs = SOME ws ⇒
   ∃ps wss.
     MAP compile_v vs = MAP RefPtr ps ∧
     MAP (OPTION_MAP compile_sv o combin$C store_lookup refs) ps =
     MAP (SOME o ByteArray F) wss ∧ ws = FLAT wss`,
  ho_match_mp_tac vs_to_w8s_ind
  \\ rw[vs_to_w8s_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ rename1`store_lookup p refs = SOME (W8array ws)`
  \\ qexists_tac`p::ps` \\ qexists_tac`ws::wss`
  \\ simp[]);

val vs_to_string = Q.store_thm("vs_to_string",
  `∀vs ws. vs_to_string vs = SOME ws ⇒
    ∃wss. MAP compile_v vs = MAP ByteVector wss ∧
      FLAT wss = MAP (n2w o ORD) ws`,
  ho_match_mp_tac vs_to_string_ind
  \\ rw[vs_to_string_def]
  \\ every_case_tac \\ fs[] \\ rveq
  \\ qmatch_goalsub_abbrev_tac`ByteVector ws1`
  \\ qexists_tac`ws1::wss` \\ simp[]);

val Boolv = Q.store_thm("Boolv[simp]",
  `compile_v (Boolv b) = Boolv b`,
  Cases_on`b`>>EVAL_TAC)

(* compiler correctness *)

val true_neq_false = EVAL``true_tag = false_tag`` |> EQF_ELIM;

val arw = srw_tac[ARITH_ss]

val do_app_def = closSemTheory.do_app_def

val build_rec_env_pat_def = patSemTheory.build_rec_env_def
val do_opapp_pat_def = patSemTheory.do_opapp_def
val do_app_pat_def = patSemTheory.do_app_def
val evaluate_def = closSemTheory.evaluate_def
val evaluate_pat_def = patSemTheory.evaluate_def

val s = mk_var("s",
  ``patSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 2
  |> type_subst[alpha |-> ``:'ffi``])

val LENGTH_eq = Q.prove(
  `(LENGTH ls = 1 ⇔ ∃y. ls = [y]) ∧
   (LENGTH ls = 2 ⇔ ∃y z. ls = [y; z]) ∧
   (LENGTH ls = 0 ⇔ ls = []) ∧
   (0 = LENGTH ls ⇔ LENGTH ls = 0) ∧
   (1 = LENGTH ls ⇔ LENGTH ls = 1) ∧
   (2 = LENGTH ls ⇔ LENGTH ls = 2)`,
  Cases_on`ls`>>simp[]>> Cases_on`t`>>simp[LENGTH_NIL])

val compile_evaluate = Q.store_thm("compile_evaluate",
  `0 < max_app ⇒
   (∀env ^s es res. evaluate env s es = res ∧ SND res ≠ Rerr (Rabort Rtype_error) ⇒
      evaluate (MAP compile es,MAP compile_v env,compile_state max_app s) =
        (map_result (MAP compile_v) compile_v (SND res), compile_state max_app (FST res)))`,
  strip_tac >>
  ho_match_mp_tac patSemTheory.evaluate_ind >>
  strip_tac >- (rw[evaluate_pat_def,evaluate_def]>>rw[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum`X = res`mp_tac >>
    simp[Once evaluate_cons] >>
    split_pair_case_tac >> fs[] >>
    simp[Once evaluate_CONS] >> strip_tac >>
    every_case_tac >> fs[] >>
    imp_res_tac evaluate_sing >> rw[] >>fs[] >> rfs[]) >>
  strip_tac >- (
    Cases_on`l`>>
    rw[evaluate_def,do_app_def] >> rw[] >>
    simp[GSYM MAP_REVERSE,evaluate_MAP_Op_Const,combinTheory.o_DEF]) >>
  strip_tac >- (
    rw[evaluate_def,evaluate_pat_def] >>
    every_case_tac >> fs[] >>
    imp_res_tac evaluate_sing >> fs[]) >>
  strip_tac >- (
    rw[evaluate_def,evaluate_pat_def] >>
    every_case_tac >> fs[] >> rw[] ) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def,do_app_def] >>
    every_case_tac >> fs[ETA_AX,MAP_REVERSE] ) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def,EL_MAP] >> rw[] >>
    spose_not_then strip_assume_tac >> rw[] >> fs[]) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def,do_app_def,get_global_def,compile_state_def,EL_MAP,IS_SOME_EXISTS] >>
    rw[] >> fs[] >>
    spose_not_then strip_assume_tac >> rw[] >> fs[]) >>
  strip_tac >- (
    rw[evaluate_pat_def,evaluate_def] >> rw[ETA_AX] ) >>
  strip_tac >- (
    rw[evaluate_def,evaluate_pat_def] >>
    Cases_on`op=Op(Op Opapp)`>>fs[] >- (
      split_pair_case_tac >> fs[] >>
      qmatch_assum_rename_tac `_ = (s1,r1)` >>
      reverse(Cases_on`r1`)>>fs[] >- (
        rw[]>>fs[evaluate_def,MAP_REVERSE,ETA_AX] >>
        Cases_on`es`>>fs[] >> Cases_on`t`>>fs[LENGTH_NIL] >>
        fs[Once evaluate_CONS] >>
        every_case_tac >> fs[] >> rw[] >>
        fs[evaluate_def] >> rw[] >> fs[] ) >>
      imp_res_tac evaluate_length >>
      fs[MAP_REVERSE,ETA_AX] >>
      IF_CASES_TAC >> fs[LENGTH_eq] >- (
        simp[evaluate_def,do_app_def] >>
        rw[do_opapp_def] >>
        Cases_on`a`>>fs[LENGTH_NIL_SYM]>>
        Cases_on`t`>>fs[LENGTH_eq]>>rw[]>>fs[]>>
        Cases_on`REVERSE t' ++ [h'] ++ [h]`>>fs[]>>
        Cases_on`t`>>fs[]>>
        Cases_on`t''`>>fs[LENGTH_eq] >>
        every_case_tac >> fs[] ) >>
      rpt var_eq_tac >> fs[LENGTH_eq] >> var_eq_tac >>
      simp[evaluate_def] >>
      fs[Once evaluate_CONS] >>
      split_pair_case_tac >> fs[] >>
      fs[evaluate_def] >>
      pop_assum mp_tac >>
      split_pair_case_tac >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> strip_tac >>
      rpt var_eq_tac >> fs[] >>
      split_pair_case_tac >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> rpt var_eq_tac >>
      imp_res_tac evaluate_IMP_LENGTH >> fs[LENGTH_eq] >> rw[] >>
      qmatch_assum_rename_tac`_ = (s1,Rval [d; c])` >>
      Cases_on`do_opapp [c; d]`>>fs[] >>
      split_pair_case_tac >> fs[] >>
      rpt var_eq_tac >>
      IF_CASES_TAC >> fs[] >- (
        simp[evaluate_def] >> fs[do_opapp_def] >>
        Cases_on`c`>>fs[dest_closure_def,check_loc_def,LET_THM] >>
        simp[state_component_equality,EL_MAP]) >>
      simp[evaluate_def] >> fs[do_opapp_def] >>
      Cases_on`c`>>fs[dest_closure_def,check_loc_def,EL_MAP,LET_THM,ETA_AX] >>simp[] >>
      rpt var_eq_tac >> fs[build_rec_env_pat_def] >>
      split_pair_case_tac >> fs[] >>
      fs[MAP_GENLIST,o_DEF,ETA_AX] >>
      fsrw_tac[boolSimps.ETA_ss][] >>
      BasicProvers.CASE_TAC >> fs[] >>
      imp_res_tac evaluate_IMP_LENGTH >> fs[LENGTH_eq] >>
      simp[evaluate_def] >> rw[] >>
      imp_res_tac evaluate_IMP_LENGTH >> fs[LENGTH_eq] ) >>
    split_pair_case_tac >> fs[] >>
    reverse BasicProvers.CASE_TAC >> fs[] >> rfs[] >- (
      reverse(Cases_on`op`)>>fs[evaluate_def,ETA_AX,MAP_REVERSE] >- (
        rw[] >> fs[LENGTH_eq,evaluate_def,do_app_def] >>
        rw[] >> fs[] ) >>
      qmatch_assum_rename_tac`op ≠ Op Opapp` >>
      reverse(Cases_on`op`)>>fs[evaluate_def,ETA_AX] >>
      qmatch_assum_rename_tac`op ≠ Opapp` >>
      Cases_on`op`>>fs[evaluate_def,ETA_AX,MAP_REVERSE] >>
      TRY ( qmatch_goalsub_rename_tac`Opn op` >> Cases_on`op`) >>
      TRY ( qmatch_goalsub_rename_tac`Opb op` >> Cases_on`op`) >>
      TRY ( qmatch_goalsub_rename_tac`Chopb op` >> Cases_on`op`) >>
      TRY ( qmatch_goalsub_rename_tac`WordFromInt wz` >> Cases_on`wz`) >>
      TRY ( qmatch_goalsub_rename_tac`WordToInt wz` >> Cases_on`wz`) >>
      fs[evaluate_def,ETA_AX,MAP_REVERSE] >- (
        rw[] >> fs[LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE] >>
        rw[] >> fs[] >> pop_assum mp_tac >>
        simp[Once evaluate_CONS] >>
        every_case_tac >> fs[do_app_def] )
      >- (
        rw[Once evaluate_CONS,evaluate_def] >>
        rw[do_app_def] )
      >- (
        rw[Once evaluate_CONS,evaluate_def] >>
        rw[do_app_def] )
      >> (
        rw[] >> fs[LENGTH_eq,evaluate_def,ETA_AX,MAP_REVERSE] >>
        rw[] >> fs[] >>
        fs[do_app_def])) >>
    BasicProvers.CASE_TAC >> fs[] >>
    BasicProvers.CASE_TAC >> fs[] >>
    fs[patSemTheory.do_app_cases] >> rw[] >>
    fsrw_tac[ETA_ss][SWAP_REVERSE_SYM] >>
    fs[evaluate_def,MAP_REVERSE,do_app_def,PULL_EXISTS,
       store_alloc_def,FLOOKUP_compile_state_refs,int_gt,
       prim_exn_def,NOT_LESS,LEAST_LESS_EQ,EL_MAP,GREATER_EQ] >>
    imp_res_tac evaluate_length >> fs[LENGTH_EQ_NUM_compute] >>
    rveq \\
    fs[evaluate_def,do_app_def,FLOOKUP_compile_state_refs,
       compile_state_with_refs_snoc,case_eq_thms,pair_case_eq,
       INT_NOT_LT,int_ge,PULL_EXISTS,IMPLODE_EXPLODE_I,
       INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd] >>
    simp[MAP_MAP_o,n2w_ORD_CHR_w2n,EL_MAP,Unit_def] >>
    rfs[INT_ABS_EQ_ID |> SPEC_ALL |> EQ_IMP_RULE |> snd] >>
    TRY (
      rename1`do_shift sh n wz w`
      \\ Cases_on`wz` \\ Cases_on`w` \\ fs[]
      \\ rw[] \\ NO_TAC) >>
    TRY (
      rename1`do_word_from_int wz i`
      \\ Cases_on`wz` \\ fs[evaluate_def,do_app_def,integer_wordTheory.w2n_i2w]
      \\ NO_TAC) >>
    TRY (
      rename1`do_word_to_int wz w`
      \\ Cases_on`wz` \\ Cases_on`w` \\ fs[evaluate_def,do_app_def]
      \\ NO_TAC) >>
    TRY (
      rename1`ORD(CHR(Num i))`
      \\ `Num i < 256` by COOPER_TAC
      \\ simp[ORD_CHR,INT_OF_NUM]
      \\ COOPER_TAC ) >>
    TRY (
      rename1`Opn opn`
      \\ Cases_on`opn`
      \\ fs[evaluate_def,do_app_def,opn_lookup_def,
            closSemTheory.do_eq_def]
      \\ NO_TAC) >>
    TRY (
      rename1`do_eq (Number 0) (Number 0)`
      \\ simp[closSemTheory.do_eq_def]
      \\ NO_TAC ) >>
    TRY (
      rename1`Opb opb`
      \\ Cases_on`opb`
      \\ fs[evaluate_def,do_app_def,opb_lookup_def]
      \\ NO_TAC) >>
    TRY (
      rename1`Chopb op` >>
      Cases_on`op`>>fs[evaluate_def,ETA_AX,do_app_def,opb_lookup_def] >>
      NO_TAC) >>
    TRY (
      rename1`do_word_op op wz w1 w2`
      \\ Cases_on`wz` \\ Cases_on`w1` \\ Cases_on`w2` \\ fs[evaluate_def]
      \\ rveq \\ fs[]
      \\ DEEP_INTRO_TAC some_intro
      \\ simp[FORALL_PROD]
      \\ NO_TAC) >>
    imp_res_tac v_to_list \\ fs[] >>
    TRY (
      rename1`vs_to_w8s` >>
      DEEP_INTRO_TAC some_intro >>
      imp_res_tac vs_to_w8s \\ fs[] >>
      reverse conj_tac >- metis_tac[] >>
      rw[] >>
      imp_res_tac INJ_MAP_EQ >> fs[INJ_DEF] >>
      imp_res_tac INJ_MAP_EQ >> fs[INJ_DEF] >>
      NO_TAC ) >>
    TRY (
      rename1`v_to_char_list` >>
      imp_res_tac v_to_char_list \\ fs[] >>
      DEEP_INTRO_TAC some_intro >> fs[PULL_EXISTS] >>
      qexists_tac`MAP ORD ls` \\
      simp[MAP_MAP_o,EVERY_MAP,ORD_BOUND] \\
      rw[LIST_EQ_REWRITE,EL_MAP,ORD_BOUND] \\ rfs[]
      \\ fs[EL_MAP] \\ metis_tac[ORD_BOUND]) >>
    TRY (
      rename1`vs_to_string` >>
      imp_res_tac vs_to_string \\ fs[] >>
      DEEP_INTRO_TAC some_intro \\ fs[PULL_EXISTS] >>
      qexists_tac`wss` \\ rw[] >>
      imp_res_tac INJ_MAP_EQ \\ fs[INJ_DEF]
      \\ NO_TAC) >>
    TRY (
      rename1`get_global` >>
      simp[compile_state_def,get_global_def,EL_MAP] >>
      simp[LUPDATE_MAP] >> NO_TAC) >>
    TRY (
      rename1`patSem$do_eq v1 v2`
      \\ Cases_on`do_eq v1 v2 = Eq_type_error` \\ fs[]
      \\ imp_res_tac do_eq \\ fs[] \\ rw[]
      \\ NO_TAC ) >>
    TRY (
      IF_CASES_TAC \\ TRY (`F` by COOPER_TAC)
      \\ simp[EL_MAP,ORD_BOUND] ) >>
    TRY (
      rename1`store_lookup`
      \\ fs[store_lookup_def,store_assign_def]
      \\ qmatch_assum_rename_tac`store_v_same_type (EL lnum t.refs) _`
      \\ Cases_on`EL lnum t.refs` \\ fs[store_v_same_type_def] ) >>
    fs[state_component_equality,compile_state_def,fmap_eq_flookup,
       ALOOKUP_GENLIST,FLOOKUP_UPDATE,store_assign_def,store_lookup_def]
    \\ rveq \\ simp[EL_LUPDATE] \\ rw[LUPDATE_def,map_replicate,LUPDATE_MAP]) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def,patSemTheory.do_if_def] >> rw[] >>
    every_case_tac >> fs[] >>
    imp_res_tac evaluate_length >> fs[LENGTH_eq] >> rw[] >> fs[] ) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >> rw[] >>
    every_case_tac >> fs[] >>
    imp_res_tac evaluate_length >> fs[LENGTH_eq] >> rw[] >> fs[] ) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >> rw[] >>
    every_case_tac >> fs[] >>
    qmatch_assum_abbrev_tac`SND x = _` >>
    Cases_on`x`>>fs[markerTheory.Abbrev_def] >> rw[] >>
    pop_assum(assume_tac o SYM) >>
    imp_res_tac evaluate_length >> fs[LENGTH_eq] >> rw[] >> fs[] >>
    fsrw_tac[ARITH_ss][]) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >>
    rw[] >> fs[EXISTS_MAP] >>
    fs[build_rec_env_pat_def,build_recc_def,MAP_GENLIST,
       combinTheory.o_DEF,ETA_AX,MAP_MAP_o,clos_env_def] >>
    fsrw_tac[ETA_ss][] ) >>
  strip_tac >- (
    simp[evaluate_def,evaluate_pat_def] >>
    simp[evaluate_REPLICATE_Op_AllocGlobal,do_app_def,backend_commonTheory.tuple_tag_def] >>
    rpt gen_tac >>
    simp[compile_state_def] >>
    simp[MAP_GENLIST,combinTheory.o_DEF,combinTheory.K_DEF] ));

val compile_semantics = Q.store_thm("compile_semantics",
  `0 < max_app ⇒
   semantics env st es ≠ Fail ⇒
   semantics (MAP compile_v env) (compile_state max_app st) (MAP compile es) =
   semantics env st es`,
  strip_tac >>
  simp[patSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    rw[] >>
    simp[closSemTheory.semantics_def] >>
    IF_CASES_TAC >> fs[] >- (
      qhdtm_x_assum`patSem$evaluate`kall_tac >>
      last_x_assum(qspec_then`k'`mp_tac)>>simp[] >>
      (fn g => subterm (fn tm => Cases_on`^(assert(has_pair_type)tm)`) (#2 g) g) >>
      spose_not_then strip_assume_tac >>
      drule (UNDISCH compile_evaluate) >>
      impl_tac >- ( rw[] >> strip_tac >> fs[] ) >>
      strip_tac >> fs[] ) >>
    DEEP_INTRO_TAC some_intro >> simp[] >>
    conj_tac >- (
      rw[] >>
      qmatch_assum_abbrev_tac`patSem$evaluate env ss es = _` >>
      qmatch_assum_abbrev_tac`closSem$evaluate bp = _` >>
      qspecl_then[`env`,`ss`,`es`](mp_tac o Q.GEN`extra`) patPropsTheory.evaluate_add_to_clock_io_events_mono >>
      Q.ISPEC_THEN`bp`(mp_tac o Q.GEN`extra`) (CONJUNCT1 closPropsTheory.evaluate_add_to_clock_io_events_mono) >>
      simp[Abbr`ss`,Abbr`bp`] >>
      disch_then(qspec_then`k`strip_assume_tac) >>
      disch_then(qspec_then`k'`strip_assume_tac) >>
      Cases_on`s.ffi.final_event`>>fs[]>-(
        Cases_on`s'.ffi.final_event`>>fs[]>-(
          unabbrev_all_tac >>
          drule (UNDISCH compile_evaluate) >>
          impl_tac >- fs[] >>
          strip_tac >>
          drule (GEN_ALL(SIMP_RULE std_ss [](CONJUNCT1 closPropsTheory.evaluate_add_to_clock))) >>
          simp[] >>
          disch_then(qspec_then`k'`mp_tac)>>simp[]>>
          qhdtm_x_assum`closSem$evaluate`mp_tac >>
          drule (GEN_ALL(SIMP_RULE std_ss [](CONJUNCT1 closPropsTheory.evaluate_add_to_clock))) >>
          simp[] >>
          disch_then(qspec_then`k`mp_tac)>>simp[]>>
          ntac 3 strip_tac >> rveq >> fs[] >>
          fs[state_component_equality] >>
          simp[compile_state_def]) >>
        first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> fs[] >>
        unabbrev_all_tac >>
        drule (UNDISCH compile_evaluate) >>
        impl_tac >- (
          last_x_assum(qspec_then`k+k'`mp_tac)>>
          rpt strip_tac >> fsrw_tac[ARITH_ss][] >> rfs[] ) >>
        strip_tac >>
        qhdtm_x_assum`patSem$evaluate`mp_tac >>
        drule (GEN_ALL patPropsTheory.evaluate_add_to_clock) >>
        simp[] >>
        disch_then(qspec_then`k'`mp_tac)>>simp[] >>
        strip_tac >> spose_not_then strip_assume_tac >>
        rveq >> fsrw_tac[ARITH_ss][compile_state_def] >> rfs[]) >>
      first_assum(subterm (fn tm => Cases_on`^(assert has_pair_type tm)`) o concl) >> fs[] >>
      unabbrev_all_tac >>
      drule (UNDISCH compile_evaluate) >>
      simp[] >>
      impl_tac >- (
        last_x_assum(qspec_then`k+k'`mp_tac)>>
        rpt strip_tac >> fsrw_tac[ARITH_ss][] >> rfs[] ) >>
      strip_tac >> rveq >>
      fsrw_tac[ARITH_ss][] >>
      reverse(Cases_on`s'.ffi.final_event`)>>fs[]>>rfs[]>>
      qhdtm_x_assum`closSem$evaluate`mp_tac >>
      drule (GEN_ALL(SIMP_RULE std_ss [](CONJUNCT1 closPropsTheory.evaluate_add_to_clock))) >>
      simp[] >>
      disch_then(qspec_then`k`mp_tac)>>simp[] >>
      rpt strip_tac >> spose_not_then strip_assume_tac >>
      rveq >> fsrw_tac[ARITH_ss][] >>
      fs[compile_state_def,state_component_equality] >> rfs[]) >>
    drule (UNDISCH compile_evaluate) >> simp[] >>
    impl_tac >- (
      last_x_assum(qspec_then`k`mp_tac)>>
      fs[] >> rpt strip_tac >> fs[] ) >>
    strip_tac >>
    asm_exists_tac >> simp[] >>
    simp[compile_state_def] >>
    asm_exists_tac >> simp[]) >>
  strip_tac >>
  simp[closSemTheory.semantics_def] >>
  IF_CASES_TAC >> fs[] >- (
    last_x_assum(qspec_then`k`strip_assume_tac) >>
    qmatch_assum_abbrev_tac`SND p ≠ _` >>
    Cases_on`p`>>fs[markerTheory.Abbrev_def] >>
    pop_assum(assume_tac o SYM) >>
    first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO](UNDISCH compile_evaluate))) >>
    rw[compile_state_with_clock] >>
    strip_tac >> fs[]) >>
  DEEP_INTRO_TAC some_intro >> simp[] >>
  conj_tac >- (
    spose_not_then strip_assume_tac >>
    last_x_assum(qspec_then`k`mp_tac) >>
    (fn g => subterm (fn tm => Cases_on`^(assert (can dest_prod o type_of) tm)` g) (#2 g)) >>
    strip_tac >>
    drule (UNDISCH compile_evaluate) >> simp[] >>
    spose_not_then strip_assume_tac >>
    rveq >> fs[] >>
    last_x_assum(qspec_then`k`mp_tac) >>
    simp[] >>
    fs[compile_state_def] >>
    asm_exists_tac >> fs[]) >>
  strip_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  simp[FUN_EQ_THM] >> gen_tac >>
  rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
  specl_args_of_then``patSem$evaluate``(UNDISCH compile_evaluate) mp_tac >>
  simp[compile_state_def])

(* more correctness properties *)

val compile_contains_App_SOME = Q.store_thm("compile_contains_App_SOME",
  `0 < max_app ⇒ ∀e. ¬contains_App_SOME max_app [compile e]`,
  strip_tac >>
  ho_match_mp_tac compile_ind >>
  simp[compile_def,contains_App_SOME_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_App_SOME_def]);

val compile_every_Fn_vs_NONE = Q.store_thm("compile_every_Fn_vs_NONE",
  `∀e. every_Fn_vs_NONE[compile e]`,
  ho_match_mp_tac compile_ind >>
  rw[compile_def] >>
  rw[Once every_Fn_vs_NONE_EVERY] >>
  simp[EVERY_REVERSE,EVERY_MAP] >>
  fs[EVERY_MEM,REPLICATE_GENLIST,MEM_GENLIST] >>
  rw[] >> rw[]);

val set_globals_eq = Q.store_thm("set_globals_eq",
  `∀e. set_globals e = set_globals (compile e)`,
  ho_match_mp_tac compile_ind >>
  rw[compile_def,patPropsTheory.op_gbag_def,op_gbag_def,elist_globals_reverse]
  >>
    TRY
    (TRY(qpat_x_assum`LENGTH es ≠ A` kall_tac)>>
    TRY(qpat_x_assum`LENGTH es = A` kall_tac)>>
    Induct_on`es`>>fs[]>>NO_TAC)
  >>
    fs[LENGTH_eq]>>
    TRY(pop_assum SUBST_ALL_TAC>>fs[bagTheory.COMM_BAG_UNION])>>
    Induct_on`n`>>fs[REPLICATE,op_gbag_def])

val compile_esgc_free = Q.store_thm("compile_esgc_free",
  `∀e. esgc_free e ⇒ esgc_free (compile e)`,
  ho_match_mp_tac compile_ind >>
  rw[compile_def] >>
  fs[EVERY_REVERSE,EVERY_MAP,EVERY_MEM]>>
  fs[set_globals_eq,LENGTH_eq]
  >- (Induct_on`es`>>fs[set_globals_eq])
  >> Induct_on`n`>>rw[REPLICATE]>> metis_tac[esgc_free_def,EVERY_DEF])

val compile_distinct_setglobals = Q.store_thm("compile_distinct_setglobals",
  `∀e. BAG_ALL_DISTINCT (set_globals e) ⇒
       BAG_ALL_DISTINCT (set_globals (compile e))`,
  fs[set_globals_eq])

val _ = export_theory()
