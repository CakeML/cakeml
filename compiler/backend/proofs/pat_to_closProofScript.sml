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
  (compile_v (Litv (StrLit s)) =
    (Block string_tag (MAP (Number o $& o ORD) s))) ∧
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
  (compile_sv (W8array bs) = ByteArray bs)`
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

(* semantic functions respect translation *)

val do_eq = store_thm("do_eq",
  ``(∀v1 v2. do_eq v1 v2 ≠ Eq_type_error ⇒
      (do_eq v1 v2 = do_eq (compile_v v1) (compile_v v2))) ∧
    (∀vs1 vs2. do_eq_list vs1 vs2 ≠ Eq_type_error ⇒
      (do_eq_list vs1 vs2 = do_eq_list (MAP compile_v vs1) (MAP compile_v vs2)))``,
  ho_match_mp_tac patSemTheory.do_eq_ind >>
  simp[patSemTheory.do_eq_def,closSemTheory.do_eq_def] >>
  conj_tac >- (
    Cases >> Cases >> simp[lit_same_type_def,closSemTheory.do_eq_def,ORD_11] >>
    TRY(rw[] >> pop_assum mp_tac >> rw[] >> NO_TAC) >>
    qid_spec_tac`s'` >>
    Induct_on`s` >> simp[LENGTH_NIL_SYM,closSemTheory.do_eq_def] >> rw[] >>
    TRY (
      spose_not_then strip_assume_tac >> rw[] >> fs[] >> NO_TAC) >>
    Cases_on`s'`>>fs[closSemTheory.do_eq_def,ORD_11] >> rw[]) >>
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

val list_to_v = store_thm("list_to_v",
  ``∀ls. list_to_v (MAP (Number o $& o ORD) ls) =
         compile_v (char_list_to_v ls)``,
  Induct >> simp[list_to_v_def,char_list_to_v_def])

val v_to_list_def = closSemTheory.v_to_list_def;

val v_to_char_list = store_thm("v_to_char_list",
  ``∀v ls. (v_to_char_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP (Number o $& o ORD) ls))``,
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

val v_to_list = store_thm("v_to_list",
  ``∀v ls. (v_to_list v = SOME ls) ⇒
           (v_to_list (compile_v v) = SOME (MAP compile_v ls))``,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def,v_to_list_def] >>
  rw[] >> Cases_on`v_to_list v`>>fs[]>> rw[])

val Boolv = store_thm("Boolv[simp]",
  ``compile_v (Boolv b) = Boolv b``,
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
    simp[GSYM MAP_REVERSE,evaluate_MAP_Op_Const,combinTheory.o_DEF] >>
    every_case_tac \\ simp[]) >>
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
    imp_res_tac patSemTheory.do_app_cases >>
    fs[do_app_pat_def] >> rw[]
    >- ( (* Opn *)
      Cases_on`z`>>fs[evaluate_def,ETA_AX,do_app_def,MAP_REVERSE,SWAP_REVERSE_SYM,PULL_EXISTS] >>
      rw[opn_lookup_def,closSemTheory.do_eq_def] >>
      TRY IF_CASES_TAC >> fs[] >> fsrw_tac[ARITH_ss][] >>
      BasicProvers.EVERY_CASE_TAC >> fs[conLangTheory.false_tag_def,conLangTheory.true_tag_def] >>
      rw[prim_exn_def,opn_lookup_def] )
    >- ( (* Opb *)
      Cases_on`z`>>fs[evaluate_def,ETA_AX,do_app_def,opb_lookup_def,
                      MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[] >>
      rw[] >> COOPER_TAC )
    >- ( (* Opw *)
         every_case_tac \\ fs[] \\ rveq
         \\ fs[SWAP_REVERSE_SYM] \\ rveq
         \\ Cases_on`wz`\\Cases_on`w1`\\Cases_on`w2`\\fs[]\\rveq
         \\ fs[ETA_AX,MAP_REVERSE]
         \\ simp[evaluate_def,do_app_def]
         \\ DEEP_INTRO_TAC some_intro
         \\ simp[FORALL_PROD] )
    >- ( (* Shift *)
         every_case_tac \\ fs[] \\ rveq
         \\ Cases_on`wz`\\Cases_on`w`\\fs[]\\rveq
         \\ fs[ETA_AX,MAP_REVERSE]
         \\ simp[evaluate_def,do_app_def] )
    >- ( (* Equal *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      Cases_on`do_eq v1 v2 = Eq_type_error`>>fs[] >>
      imp_res_tac do_eq >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> rw[] >>
      fsrw_tac[ARITH_ss][prim_exn_def] >>
      EVAL_TAC)
    >- ( (* wrong args for Update *)
      imp_res_tac evaluate_length >>
      fs[LENGTH_eq,Once SWAP_REVERSE_SYM] >>
      rw[] >> fs[LENGTH_eq] >> fs[])
    >- ( (* Update *)
      fs[LENGTH_eq] >>
      simp[evaluate_def,ETA_AX,do_app_def] >> rw[] >>
      Cases_on`a`>>fs[]>>rw[]>>
      fs[store_assign_def] >> simp[] >>
      pop_assum mp_tac >> IF_CASES_TAC >> simp[] >> rw[] >>
      fs[evaluate_def] >>
      BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[] >>
      BasicProvers.CASE_TAC >- (
        fs[compile_state_def] >>
        imp_res_tac ALOOKUP_FAILS >> fs[MEM_GENLIST] ) >>
      pop_assum mp_tac >> simp[Once compile_state_def] >> strip_tac >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_GENLIST] >>
      rpt var_eq_tac >> qmatch_assum_abbrev_tac`lnum < LENGTH s21` >>
      Cases_on`EL lnum s21`>> fs[store_v_same_type_def,compile_sv_def] >>
      simp[compile_state_def,Unit_def] >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST,EL_LUPDATE] >>
      rw[] >> fs[compile_sv_def] >> EVAL_TAC )
    >- ( (* Deref *)
      simp[ETA_AX,evaluate_def,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      fs[store_lookup_def] >>
      imp_res_tac evaluate_length >>
      Cases_on`es`>>fs[LENGTH_NIL] >>
      simp[Once evaluate_CONS,evaluate_def,do_app_def] >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      rw[]>>fs[] >>
      ntac 2 (pop_assum mp_tac )>> BasicProvers.CASE_TAC >>
      fs[compile_sv_def] >> rw[] )
    >- ( (* Ref *)
      simp[ETA_AX,evaluate_def,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      fs[store_alloc_def,LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[compile_state_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qpat_abbrev_tac`ll = LENGTH _` >>
        qexists_tac`ll`>>simp[]>>rw[]>>
        `¬(ll< ll)` by simp[] >>
        `¬(ll < n)` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_APPEND2,compile_sv_def] )
    >- ( (* SetGlobal *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[compile_state_def,get_global_def,EL_MAP] >>
      pop_assum mp_tac >> BasicProvers.CASE_TAC >>fs[] >>
      strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      simp[LUPDATE_MAP,dec_to_exhTheory.tuple_tag_def] )
    >- ( (* TagLenEq *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] )
    >- ( (* wrong args for El *)
      imp_res_tac evaluate_length >> fs[])
    >- ( (* El *)
      fs[LENGTH_eq] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[EL_MAP] )
    >- ( (* RefByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[] >>
      fs[store_alloc_def,LET_THM] >>
      Cases_on`n<0`>>fs[prim_exn_def] >- srw_tac[ARITH_ss][] >>
      `0 ≤ n` by COOPER_TAC >>
      simp[PULL_EXISTS] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[compile_state_def,true_neq_false] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qpat_abbrev_tac`ll = LENGTH _` >>
        qexists_tac`ll`>>simp[]>>rw[]>>
        `¬(ll< ll)` by simp[] >>
        `¬(ll < n')` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_LENGTH_APPEND,compile_sv_def] >>
      metis_tac[INT_ABS_EQ_ID])
    >- ( (* DerefByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[] >>
      fs[store_lookup_def,LET_THM] >>
      ntac 2 (pop_assum mp_tac) >>
      IF_CASES_TAC >> fs[] >> strip_tac >>
      Cases_on`i < 0` >> fs[] >- (
        every_case_tac >> fs[] >>
        srw_tac[ARITH_ss][prim_exn_def] ) >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      ntac 2 (pop_assum mp_tac) >>
      BasicProvers.CASE_TAC >> fs[] >> strip_tac >> strip_tac >>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        srw_tac[ARITH_ss][prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def] >> rw[] )
    >- ( (* LengthByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM,store_lookup_def] >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      pop_assum mp_tac >> BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.CASE_TAC >> fs[compile_sv_def] >> rw[] )
    >- ( (* UpdateByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[] >>
      fs[store_lookup_def,LET_THM] >>
      ntac 2 (pop_assum mp_tac) >>
      BasicProvers.CASE_TAC >> fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        BasicProvers.CASE_TAC >> fs[] >>
        arw[prim_exn_def] ) >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      BasicProvers.CASE_TAC >>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        arw[prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def] >>
      fs[store_assign_def,store_v_same_type_def] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> fs[EL_LUPDATE,compile_sv_def,dec_to_exhTheory.tuple_tag_def,true_neq_false])
    >- ( (* WordToInt *)
      every_case_tac \\ fs[] \\ rveq
      \\ imp_res_tac evaluate_length \\ fs[quantHeuristicsTheory.LIST_LENGTH_1]
      \\ Cases_on`wz` \\ Cases_on`w` \\ fs[ETA_AX] \\ rveq
      \\ simp[evaluate_def,do_app_def])
    >- ( (* WordFromInt *)
      Cases_on`wz`\\fs[ETA_AX,MAP_REVERSE]
      >- (
        simp[Once evaluate_CONS,evaluate_def,do_app_def]
        \\ simp[integer_wordTheory.w2n_i2w] )
      \\ simp[evaluate_def,do_app_def])
    >- ( (* wrong args for Chr *)
      imp_res_tac evaluate_length >> fs[] )
    >- ( (* Chr *)
      Cases_on`es`>>fs[LENGTH_NIL])
    >- (
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def,prim_exn_def])
    >- (
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def,prim_exn_def] >>
      Cases_on`n < 0` >> fs[] >>
      `255 < n` by COOPER_TAC >> simp[])
    >- (
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def,prim_exn_def] >> fs[] >>
      `¬(255 < n)` by COOPER_TAC >> simp[] >>
      `ABS n = n` by COOPER_TAC >>
      `Num n < 256` by COOPER_TAC >>
      `0 ≤ n` by COOPER_TAC >>
      EVAL_TAC >>
      simp[ORD_CHR,INT_OF_NUM])
    >- ( (* Chopb *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      Cases_on`z`>>fs[evaluate_def,ETA_AX,do_app_def,opb_lookup_def] >>
      simp[] >> rw[] >> COOPER_TAC )
    >- ( (* Explode *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      simp[list_to_v,IMPLODE_EXPLODE_I])
    >- ( (* Implode *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      imp_res_tac v_to_char_list >>
      simp[IMPLODE_EXPLODE_I])
    >- ( (* Strlen *)fs[MAP_REVERSE] >>simp[evaluate_def,ETA_AX,do_app_def] )
    >- ( (* FromList *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      imp_res_tac v_to_list >>
      simp[])
    >- ( (* LengthBlock *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      Cases_on`i < 0` >> fs[LET_THM] >- (
        arw[prim_exn_def] ) >>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH vs' ⇔ ¬(Num i ≥ LENGTH vs')` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH vs'`>>fs[] >- (
        arw[prim_exn_def] ) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[EL_MAP,true_neq_false] )
    >- ( fs[MAP_REVERSE] >> simp[evaluate_def,ETA_AX,do_app_def])
    >- ( (* RefArray *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_alloc_def,LET_THM] >>
      Cases_on`n<0`>>fs[prim_exn_def] >- arw[] >>
      `0 ≤ n` by COOPER_TAC >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[compile_state_def,true_neq_false] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qpat_abbrev_tac`ll = LENGTH _` >>
        qexists_tac`ll`>>simp[]>>rw[]>>
        `¬(ll< ll)` by simp[] >>
        `¬(ll < n')` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_LENGTH_APPEND,compile_sv_def] >>
      simp[REPLICATE_GENLIST,MAP_GENLIST] >>
      metis_tac[INT_ABS_EQ_ID])
    >- ( (* Deref *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_lookup_def,LET_THM] >>
      ntac 2 (pop_assum mp_tac) >> BasicProvers.CASE_TAC >> fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        BasicProvers.CASE_TAC >> fs[] >>
        arw[prim_exn_def] ) >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      BasicProvers.CASE_TAC>>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        arw[prim_exn_def] ) >>
      rpt strip_tac >> rpt var_eq_tac >>
      simp[ALOOKUP_GENLIST,compile_sv_def,EL_MAP] )
    >- ( (* Length *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_lookup_def] >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      pop_assum mp_tac >> BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.CASE_TAC>>fs[compile_sv_def] >> rw[] )
    >- ( (* Update *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_lookup_def,LET_THM] >>
      rpt var_eq_tac >>
      pop_assum mp_tac >> BasicProvers.CASE_TAC >> fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        BasicProvers.CASE_TAC>>fs[]>>
        arw[prim_exn_def] ) >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      BasicProvers.CASE_TAC>>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        arw[prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def] >>
      fs[store_assign_def,store_v_same_type_def] >>
      rw[fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> fs[EL_LUPDATE,compile_sv_def,LUPDATE_MAP,dec_to_exhTheory.tuple_tag_def,true_neq_false])
    >- ( (* FFI *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      simp[compile_state_def,ALOOKUP_GENLIST] >>
      fs[store_lookup_def] >>
      IF_CASES_TAC >> fs[] >>
      ntac 2 (pop_assum mp_tac) >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >>
      fs[store_assign_def] >> rfs[] >>
      fs[store_v_same_type_def] >>
      BasicProvers.CASE_TAC >> fs[] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Unit_def] >>
      simp[fmap_eq_flookup,ALOOKUP_GENLIST,FLOOKUP_UPDATE,EL_LUPDATE] >>
      rw[] >> fs[])) >>
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
    simp[evaluate_REPLICATE_Op_AllocGlobal,do_app_def,dec_to_exhTheory.tuple_tag_def] >>
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
      rator_x_assum`patSem$evaluate`kall_tac >>
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
          rator_x_assum`closSem$evaluate`mp_tac >>
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
        rator_x_assum`patSem$evaluate`mp_tac >>
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
      reverse(Cases_on`s'.ffi.final_event`)>>fs[]>>rfs[]>- (
        fs[] >> rfs[compile_state_def] ) >>
      rator_x_assum`closSem$evaluate`mp_tac >>
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

val compile_contains_App_SOME = store_thm("compile_contains_App_SOME",
  ``0 < max_app ⇒ ∀e. ¬contains_App_SOME max_app [compile e]``,
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
  >-
    (Induct_on`s`>>fs[op_gbag_def])
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
