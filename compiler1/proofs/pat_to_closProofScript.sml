open preamble integerTheory intLib
     semanticPrimitivesTheory
     patSemTheory patPropsTheory pat_to_closTheory
     closLangTheory closSemTheory closPropsTheory

val _ = new_theory"pat_to_closProof"

(* value translation *)

val compile_v_def = tDefine"compile_v"`
  (compile_v (Litv (IntLit i)) = (Number i):closSem$v) ∧
  (compile_v (Litv (Word8 w)) = (Number (&w2n w))) ∧
  (compile_v (Litv (Char c)) = (Number (& ORD c))) ∧
  (compile_v (Litv (StrLit s)) =
    (Block string_tag (MAP (Number o $& o ORD) s))) ∧
  (compile_v (Loc m) = (RefPtr m)) ∧
  (compile_v (Conv cn vs) = (Block cn (MAP (compile_v) vs))) ∧
  (compile_v (Vectorv vs) = (Block vector_tag (MAP (compile_v) vs))) ∧
  (compile_v (Closure vs e) = (Closure 0 [] (MAP (compile_v) vs) 1 (compile e))) ∧
  (compile_v (Recclosure vs es k) = (Recclosure 0 [] (MAP (compile_v) vs) (MAP (λe. (1,compile e)) es) k))`
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

val compile_csg_def = Define`
  compile_csg (((c,(s,t)),g):patSem$v count_store_genv) =
    <| globals := MAP (OPTION_MAP compile_v) g;
       refs := alist_to_fmap (GENLIST (λi. (i, compile_sv (EL i s))) (LENGTH s));
       io := t;
       clock := c;
       code := FEMPTY;
       restrict_envs := F |>`;

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

val compile_csg_restrict_envs = prove(
  ``~(compile_csg s).restrict_envs``,
  PairCases_on `s` \\ fs [compile_csg_def]);

val true_neq_false = EVAL``true_tag = false_tag`` |> EQF_ELIM;

val arw = srw_tac[ARITH_ss]

val do_app_def = closSemTheory.do_app_def

val build_rec_env_pat_def = patSemTheory.build_rec_env_def
val do_opapp_pat_def = patSemTheory.do_opapp_def
val do_app_pat_def = patSemTheory.do_app_def

val compile_correct = Q.store_thm("compile_correct",
  `(∀ck env s e res. evaluate ck env s e res ⇒
      ck ⇒
      evaluate ([compile e],MAP compile_v env,compile_csg s) =
        (map_result (λv. [compile_v v]) compile_v (SND res), compile_csg (FST res))) ∧
   (∀ck env s es res. evaluate_list ck env s es res ⇒
      ck ⇒
      evaluate (MAP compile es,MAP compile_v env,compile_csg s) =
        (map_result (MAP compile_v) compile_v (SND res), compile_csg (FST res)))`,
  ho_match_mp_tac patSemTheory.evaluate_strongind >>
  strip_tac >- (
    Cases_on`l`>>
    rw[evaluate_def,do_app_def] >>
    simp[GSYM MAP_REVERSE,evaluate_MAP_Op_Const,combinTheory.o_DEF] ) >>
  strip_tac >- simp[evaluate_def] >>
  strip_tac >- (
    simp[evaluate_def] >>
    Cases_on`err`>>simp[] >>
    Cases_on`a`>>simp[]) >>
  strip_tac >- simp[evaluate_def] >>
  strip_tac >- (
    simp[evaluate_def] >>
    rw[] >> first_x_assum match_mp_tac >>
    fs[SUBSET_DEF,PULL_EXISTS] >>
    Cases >> rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    simp[evaluate_def] >>
    Cases_on`err`>>simp[] ) >>
  strip_tac >- simp[evaluate_def,ETA_AX,do_app_def,MAP_REVERSE] >>
  strip_tac >- (
    Cases_on`err`>>
    simp[evaluate_def,ETA_AX,do_app_def,MAP_REVERSE] ) >>
  strip_tac >- simp[evaluate_def,EL_MAP] >>
  strip_tac >- (
    simp[evaluate_def,do_app_def] >>
    rpt gen_tac >>
    PairCases_on`s`>>simp[compile_csg_def,get_global_def,EL_MAP] ) >>
  strip_tac >- simp[evaluate_def,ETA_AX,compile_csg_restrict_envs,clos_env_def,max_app_def] >>
  strip_tac >- (
    simp[evaluate_def,MAP_REVERSE,ETA_AX] >>
    rw[evaluate_def] >>
    imp_res_tac evaluate_list_length >>
    Cases_on`REVERSE vs`>>fs[do_opapp_pat_def] >>
    Cases_on`t`>>fs[do_opapp_pat_def] >>
    Cases_on`t'`>>fs[do_opapp_pat_def] >>
    fs[SWAP_REVERSE_SYM] >>
    Cases_on`es`>>fs[]>>
    Cases_on`t`>>fs[LENGTH_NIL]>>
    fs[evaluate_def] >>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    imp_res_tac evaluate_IMP_LENGTH >>
    Cases_on`a`>>fs[LENGTH_NIL] >> rw[] >>
    rw[evaluate_def,dest_closure_def] >>
    Cases_on`h`>>fs[check_loc_def,compile_csg_def,ETA_AX,dec_clock_def,max_app_def] >>
    rw[] >> fs[] >> rfs[EL_MAP] >> fs[build_rec_env_pat_def] >>
    fsrw_tac[ARITH_ss][] >>
    fs[MAP_GENLIST,combinTheory.o_DEF,ETA_AX] >>
    fsrw_tac[ETA_ss][] >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    rw[evaluate_def] ) >>
  strip_tac >- (
    simp[evaluate_def,MAP_REVERSE,ETA_AX] >>
    rw[evaluate_def] >>
    imp_res_tac evaluate_list_length >>
    Cases_on`REVERSE vs`>>fs[do_opapp_pat_def] >>
    Cases_on`t`>>fs[do_opapp_pat_def] >>
    Cases_on`t'`>>fs[do_opapp_pat_def] >>
    fs[SWAP_REVERSE_SYM] >>
    Cases_on`es`>>fs[]>>
    Cases_on`t`>>fs[LENGTH_NIL]>>
    fs[evaluate_def] >>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[]>>
    imp_res_tac evaluate_IMP_LENGTH >>
    Cases_on`a`>>fs[LENGTH_NIL] >> rw[] >>
    rw[evaluate_def,dest_closure_def] >>
    Cases_on`h`>>fs[check_loc_def,compile_csg_def,ETA_AX,dec_clock_def,max_app_def] >>
    rw[] >> rw[] >>
    fsrw_tac[ARITH_ss][] >>
    rfs[EL_MAP]) >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >>
    PairCases_on`s2` >>
    imp_res_tac patPropsTheory.do_app_cases >>
    fs[do_app_pat_def] >> rw[]
    >- ( (* Opn *)
      Cases_on`z`>>fs[evaluate_def,ETA_AX,do_app_def,MAP_REVERSE,SWAP_REVERSE_SYM] >>
      rw[opn_lookup_def,closSemTheory.do_eq_def] >>
      TRY IF_CASES_TAC >> fs[] >> fsrw_tac[ARITH_ss][] >>
      BasicProvers.EVERY_CASE_TAC >> fs[conLangTheory.false_tag_def,conLangTheory.true_tag_def] >>
      rw[prim_exn_def,opn_lookup_def] )
    >- ( (* Opb *)
      Cases_on`z`>>fs[evaluate_def,ETA_AX,do_app_def,opb_lookup_def,
                      MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[] >>
      rw[] >> COOPER_TAC )
    >- ( (* Equal *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      Cases_on`do_eq v1 v2 = Eq_type_error`>>fs[] >>
      imp_res_tac do_eq >> fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> rw[] >>
      fsrw_tac[ARITH_ss][prim_exn_def] >>
      EVAL_TAC)
    >- ( (* wrong args for Update *)
      imp_res_tac evaluate_list_length >>
      Cases_on`vs`>>fs[]>>rw[]>>fs[])
    >- ( (* Update *)
      Cases_on`es`>>fs[]>>Cases_on`t`>>fs[LENGTH_NIL] >>
      simp[evaluate_def,ETA_AX,do_app_def] >> rw[] >>
      Cases_on`vs`>>fs[]>>rw[]>>
      fs[store_assign_def,Once compile_csg_def] >> simp[] >>
      pop_assum mp_tac >> IF_CASES_TAC >> simp[] >> rw[] >>
      fs[evaluate_def] >>
      BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[] >>
      BasicProvers.CASE_TAC >> fs[] >> Cases_on`q`>>fs[] >>
      BasicProvers.CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[MEM_GENLIST] ) >>
      imp_res_tac ALOOKUP_MEM >> fs[MEM_GENLIST] >>
      Cases_on`EL lnum s21`>> fs[store_v_same_type_def,compile_sv_def] >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[compile_csg_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST,EL_LUPDATE] >>
      rw[] >> fs[compile_sv_def] >- EVAL_TAC >>
      simp[LIST_EQ_REWRITE] >>
      REWRITE_TAC[GSYM EL] >>
      simp[EL_LUPDATE] )
    >- ( (* Deref *)
      simp[ETA_AX,evaluate_def,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      fs[store_lookup_def] >>
      imp_res_tac evaluate_list_length >>
      Cases_on`es`>>fs[LENGTH_NIL] >>
      simp[Once evaluate_CONS,evaluate_def,do_app_def] >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      rw[]>>fs[] >>
      Cases_on`EL n s21`>>fs[compile_sv_def] >>
      rw[compile_csg_def] )
    >- ( (* Ref *)
      simp[ETA_AX,evaluate_def,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      fs[store_alloc_def,LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[compile_csg_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qexists_tac`LENGTH s21`>>simp[]>>rw[]>>
        `¬(LENGTH s21 < LENGTH s21)` by simp[] >>
        `¬(LENGTH s21 < n)` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_APPEND2,compile_sv_def] )
    >- ( (* SetGlobal *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[compile_csg_def,get_global_def,EL_MAP] >>
      Cases_on`EL idx s23`>>fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[compile_csg_def,LUPDATE_MAP,dec_to_exhTheory.tuple_tag_def] )
    >- ( (* TagLenEq *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] )
    >- ( (* wrong args for El *)
      imp_res_tac evaluate_list_length >>
      Cases_on`es`>>fs[] )
    >- ( (* El *)
      Cases_on`es`>>fs[LENGTH_NIL] >> rw[] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[EL_MAP] )
    >- ( (* RefByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[] >>
      fs[store_alloc_def,LET_THM] >>
      Cases_on`n<0`>>fs[prim_exn_def] >- srw_tac[ARITH_ss][] >>
      `0 ≤ n` by COOPER_TAC >>
      Q.ISPEC_THEN`w`mp_tac wordsTheory.w2n_lt >>
      simp[wordsTheory.dimword_8] >> strip_tac >>
      rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
      simp[compile_csg_def,true_neq_false] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qexists_tac`LENGTH s21`>>simp[]>>rw[]>>
        `¬(LENGTH s21 < LENGTH s21)` by simp[] >>
        `¬(LENGTH s21 < n')` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_LENGTH_APPEND,compile_sv_def] >>
      metis_tac[INT_ABS_EQ_ID])
    >- ( (* DerefByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >> simp[] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        srw_tac[ARITH_ss][prim_exn_def] ) >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        srw_tac[ARITH_ss][compile_csg_def,prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def] >>
      rw[compile_csg_def] >> fs[true_neq_false])
    >- ( (* LengthByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM,store_lookup_def] >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      Cases_on`n < LENGTH s21`>>fs[]>>
      Cases_on`EL n s21`>>fs[compile_sv_def] >>
      rw[compile_csg_def] )
    >- ( (* UpdateByte *)
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        arw[prim_exn_def] ) >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        arw[compile_csg_def,prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def] >>
      fs[store_assign_def,store_v_same_type_def] >>
      Q.ISPEC_THEN`w`mp_tac wordsTheory.w2n_lt >>
      simp[wordsTheory.dimword_8] >> strip_tac >>
      rw[compile_csg_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> fs[EL_LUPDATE,compile_sv_def,dec_to_exhTheory.tuple_tag_def,true_neq_false])
    >- ( (* wrong args for Ord *)
      imp_res_tac evaluate_list_length >> fs[] )
    >- ( Cases_on`es`>>fs[LENGTH_NIL] )
    >- ( (* Chr *)
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
        arw[compile_csg_def,prim_exn_def] ) >>
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
      simp[compile_csg_def,true_neq_false] >>
      conj_asm1_tac >- (
        numLib.LEAST_ELIM_TAC >>
        simp[MEM_MAP,MAP_GENLIST,PULL_EXISTS,MEM_GENLIST] >>
        qexists_tac`LENGTH s21`>>simp[]>>rw[]>>
        `¬(LENGTH s21 < LENGTH s21)` by simp[] >>
        `¬(LENGTH s21 < n')` by metis_tac[] >>
        DECIDE_TAC ) >>
      simp[fmap_eq_flookup,FLOOKUP_UPDATE,ALOOKUP_GENLIST] >>
      rw[] >> simp[EL_APPEND1,EL_LENGTH_APPEND,compile_sv_def] >>
      simp[REPLICATE_GENLIST,MAP_GENLIST] >>
      metis_tac[INT_ABS_EQ_ID])
    >- ( (* Deref *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        arw[prim_exn_def] ) >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        arw[compile_csg_def,prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def,EL_MAP] >>
      rw[compile_csg_def,true_neq_false] )
    >- ( (* Length *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_lookup_def] >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      Cases_on`n < LENGTH s21`>>fs[]>>
      Cases_on`EL n s21`>>fs[compile_sv_def] >>
      rw[compile_csg_def] )
    >- ( (* Update *)
      fs[MAP_REVERSE,SWAP_REVERSE_SYM] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      fs[store_lookup_def,LET_THM] >>
      Cases_on`lnum < LENGTH s21`>>fs[] >>
      Cases_on`i < 0` >> fs[] >- (
        Cases_on`EL lnum s21`>>fs[]>>
        arw[prim_exn_def] ) >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      Cases_on`EL lnum s21`>>fs[compile_sv_def]>>
      `0 ≤ i` by COOPER_TAC >>
      `ABS i = i` by metis_tac[INT_ABS_EQ_ID] >> fs[] >>
      `i < &LENGTH l ⇔ ¬(Num i ≥ LENGTH l)` by COOPER_TAC >> simp[] >>
      Cases_on`Num i ≥ LENGTH l`>>fs[] >- (
        arw[compile_csg_def,prim_exn_def] ) >>
      simp[ALOOKUP_GENLIST,compile_sv_def] >>
      fs[store_assign_def,store_v_same_type_def] >>
      rw[compile_csg_def,fmap_eq_flookup,FLOOKUP_UPDATE] >>
      simp[ALOOKUP_GENLIST] >>
      rw[] >> fs[EL_LUPDATE,compile_sv_def,LUPDATE_MAP,dec_to_exhTheory.tuple_tag_def,true_neq_false])
    >- ( (* FFI *)
      fs[MAP_REVERSE] >>
      simp[evaluate_def,ETA_AX,do_app_def] >>
      simp[compile_csg_def,ALOOKUP_GENLIST] >>
      fs[store_lookup_def] >>
      IF_CASES_TAC >> fs[] >>
      Cases_on`EL lnum s21`>>fs[] >>
      Cases_on`call_FFI n l s22`>>fs[] >- rw[compile_csg_def] >>
      BasicProvers.CASE_TAC >> fs[] >>
      fs[store_assign_def] >> rfs[] >>
      fs[store_v_same_type_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      simp[Unit_def,compile_csg_def] >>
      simp[fmap_eq_flookup,ALOOKUP_GENLIST,FLOOKUP_UPDATE,EL_LUPDATE] >>
      rw[] >> fs[])) >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >>
    fs[MAP_REVERSE] >>
    Cases_on`op`>>simp[evaluate_def,ETA_AX] >>
    TRY (
      CHANGED_TAC(rw[]) >- (
        simp[evaluate_def] ) >>
      Cases_on`es`>>fs[LENGTH_NIL] >>
      simp[evaluate_def,do_app_def] >> NO_TAC) >>
    Cases_on`o'`>>simp[evaluate_def,ETA_AX] >>
    Cases_on`o''`>>simp[evaluate_def,ETA_AX] >>
    rw[evaluate_def] >>
    TRY(Cases_on`o'`>>simp[evaluate_def,ETA_AX] >>
        Cases_on`err`>>fs[] >> NO_TAC) >>
    TRY(
      simp[Once evaluate_CONS] >>
      simp[evaluate_def,do_app_def] >>
      Cases_on`err`>>fs[] >> NO_TAC) >>
    Cases_on`es`>>fs[LENGTH_NIL] >>
    Cases_on`t`>>fs[LENGTH_NIL] >>
    TRY(CHANGED_TAC(fs[Once evaluate_CONS]) >>
        BasicProvers.CASE_TAC>>fs[]>>Cases_on`q`>>fs[evaluate_def]>>rw[]>>
        Cases_on`err`>>fs[]>>
        BasicProvers.CASE_TAC>>fs[]>>Cases_on`q`>>fs[evaluate_def]>>
        NO_TAC) >>
    fs[evaluate_def] >>
    BasicProvers.CASE_TAC>>fs[]>>Cases_on`q`>>fs[evaluate_def]>>rw[]>>
    simp[do_app_def] >>
    BasicProvers.CASE_TAC>>fs[]>>Cases_on`q`>>fs[evaluate_def]>>rw[]) >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >>
    Cases_on`v`>>fs[]>>rw[]>>fs[patSemTheory.do_if_def]>>
    fsrw_tac[ARITH_ss][patSemTheory.Boolv_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
    fs[closSemTheory.Boolv_def,true_neq_false]) >>
  strip_tac >- simp[evaluate_def] >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >>
    Cases_on`err`>>fs[] ) >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >>
    simp[] ) >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >> fs[] >>
    rw[] >>
    Cases_on`res`>>fs[]>>
    Cases_on`r`>>fs[]>>simp[]>>
    Cases_on`e''`>>simp[]) >>
  strip_tac >- (
    simp[evaluate_def] >>
    Cases_on`err`>>simp[] ) >>
  strip_tac >- (
    simp[evaluate_def] >>
    rw[] >> fs[EXISTS_MAP,max_app_def] >>
    fs[build_rec_env_pat_def,build_recc_def,MAP_GENLIST,compile_csg_restrict_envs,
       combinTheory.o_DEF,ETA_AX,MAP_MAP_o,clos_env_def] >>
    fsrw_tac[ETA_ss][] ) >>
  strip_tac >- (
    simp[evaluate_def] >>
    simp[evaluate_REPLICATE_Op_AllocGlobal,do_app_def,dec_to_exhTheory.tuple_tag_def] >>
    rpt gen_tac >>
    PairCases_on`s`>>simp[compile_csg_def,MAP_GENLIST,combinTheory.o_DEF,combinTheory.K_DEF] ) >>
  strip_tac >- simp[evaluate_def] >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >>
    simp[Once evaluate_CONS] >> fs[] ) >>
  strip_tac >- (
    simp[evaluate_def] >> rw[] >> fs[] >>
    simp[Once evaluate_CONS] >>
    Cases_on`err`>>fs[]) >>
  simp[evaluate_def] >> rw[] >>
  simp[Once evaluate_CONS] );

(* more correctness properties *)

val compile_contains_App_SOME = store_thm("compile_contains_App_SOME",
  ``∀e. ¬contains_App_SOME[compile e]``,
  ho_match_mp_tac compile_ind >>
  simp[compile_def,contains_App_SOME_def] >>
  rw[] >> srw_tac[ETA_ss][] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  rw[Once contains_App_SOME_EXISTS,EVERY_MAP] >>
  rw[contains_App_SOME_def] >> rw[EVERY_MEM] >>
  fs[REPLICATE_GENLIST,MEM_GENLIST, MEM_MAP] >>
  rw[contains_App_SOME_def,max_app_def]);

val _ = export_theory()
