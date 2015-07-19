open preamble
     semanticPrimitivesTheory evalPropsTheory
     exhLangTheory exh_to_patTheory
     patLangTheory patPropsTheory

val _ = new_theory"exh_to_patProof"

val _ = temp_bring_to_front_overload"pure_op"{Name="pure_op",Thy="exh_to_pat"};
val _ = temp_bring_to_front_overload"Loc"{Name="Loc",Thy="patSem"};

val map_csg_def = decPropsTheory.map_csg_def
val map_csg_count = decPropsTheory.map_csg_count
val csg_rel_count = decPropsTheory.csg_rel_count

val evaluate_pat_cases = patSemTheory.evaluate_cases
val pmatch_exh_def = exhSemTheory.pmatch_def

val TAKE_CONS = prove(
  ``TAKE (n+1) env = v::TAKE n env2 ⇔ ∃env1. env = v::env1 ∧ TAKE n env1 = TAKE n env2``,
  Cases_on`env`>>simp[])

(* value translation *)

val compile_v_def = tDefine"compile_v"`
  (compile_v (Litv l) = Litv l) ∧
  (compile_v (Conv tag vs) = Conv tag (compile_vs vs)) ∧
  (compile_v (Closure env x e) =
    Closure
      (MAP compile_v (MAP SND env))
      (compile_exp (SOME x :: MAP (SOME o FST) env) e)) ∧
  (compile_v (Recclosure env funs f) =
    Recclosure
      (MAP compile_v (MAP SND env))
      (compile_funs (MAP (SOME o FST) funs ++ MAP (SOME o FST) env) funs)
      (the (LENGTH funs) (find_index f (MAP FST funs) 0))) ∧
  (compile_v (Loc n) = Loc n) ∧
  (compile_v (Vectorv vs) = Vectorv (compile_vs vs)) ∧
  (compile_vs [] = []) ∧
  (compile_vs (v::vs) = compile_v v :: compile_vs vs)`
(WF_REL_TAC`inv_image $< (\x. case x of INL v => v_size v
                                      | INR vs => v3_size vs)` >>
 simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[] >>
 Cases >> simp[exhSemTheory.v_size_def] >> rw[] >> res_tac >> simp[])
val compile_v_def = save_thm("compile_v_def",
  compile_v_def |> SIMP_RULE (srw_ss()++ETA_ss) [MAP_MAP_o])
val _ = export_rewrites["compile_v_def"]

val compile_vs_map = store_thm("compile_vs_map",
  ``∀vs. compile_vs vs = MAP compile_v vs``,
  Induct >> simp[])
val _ = export_rewrites["compile_vs_map"]

(* semantic functions obey translation *)

val do_eq = prove(
  ``(∀v1 v2. do_eq v1 v2 = do_eq (compile_v v1) (compile_v v2)) ∧
    (∀vs1 vs2. do_eq_list vs1 vs2 = do_eq_list (compile_vs vs1) (compile_vs vs2))``,
  ho_match_mp_tac exhSemTheory.do_eq_ind >>
  simp[exhSemTheory.do_eq_def,patSemTheory.do_eq_def] >>
  rw[] >> BasicProvers.CASE_TAC >> rw[])

val do_opapp = prove(
  ``∀vs env exp.
    do_opapp vs = SOME (env,exp) ⇒
    do_opapp (compile_vs vs) =
      SOME (MAP (compile_v o SND) env, compile_exp (MAP (SOME o FST) env) exp)``,
  rpt gen_tac >> simp[exhSemTheory.do_opapp_def] >>
  BasicProvers.CASE_TAC >>
  Cases_on`t`>>simp[]>>
  Cases_on`t'`>>simp[]>>
  Cases_on`h`>>simp[patSemTheory.do_opapp_def]>>
  TRY(rw[] >> rw[]>>NO_TAC) >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  fs[find_recfun_ALOOKUP,compile_funs_map,patSemTheory.build_rec_env_def,exhPropsTheory.build_rec_env_merge,FST_triple] >>
  imp_res_tac ALOOKUP_find_index_SOME >>
  simp[EL_MAP,UNCURRY,LIST_EQ_REWRITE,compile_funs_map,libTheory.the_def] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
  `∃x y z. EL i l0 = (x,y,z)` by metis_tac[PAIR]>>fs[]>>
  imp_res_tac find_index_ALL_DISTINCT_EL >>
  fs[EL_MAP,libTheory.the_def])

val v_to_list = Q.prove (
  `!v1 v2 vs1.
    compile_v v1 = v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      compile_vs vs1 = vs2`,
  ho_match_mp_tac exhSemTheory.v_to_list_ind >>
  rw [exhSemTheory.v_to_list_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [compile_v_def, patSemTheory.v_to_list_def] >>
  rw [] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [compile_v_def, patSemTheory.v_to_list_def] >>
  rw [] >>
  metis_tac [optionTheory.NOT_SOME_NONE, optionTheory.SOME_11]);

val char_list_to_v = prove(
  ``∀ls. char_list_to_v ls = compile_v (char_list_to_v ls)``,
  Induct >> simp[exhSemTheory.char_list_to_v_def,patSemTheory.char_list_to_v_def])

val v_to_char_list = Q.prove (
  `!v1 v2 vs1.
    compile_v v1 = v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1`,
  ho_match_mp_tac exhSemTheory.v_to_char_list_ind >>
  rw [exhSemTheory.v_to_char_list_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [compile_v_def, patSemTheory.v_to_char_list_def]);

val tac =
  rw [patSemTheory.do_app_def, exhSemTheory.prim_exn_def, patSemTheory.prim_exn_def,
      patSemTheory.Boolv_def, exhSemTheory.Boolv_def] >>
  rw [] >>
  fs [] >>
  rw [] >>
  fs [] >>
  rw [] >>
  fs [store_assign_def, store_lookup_def, store_alloc_def, LET_THM] >>
  rw [] >>
  fs [] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  rw [] >>
  fs [LUPDATE_MAP, EL_MAP] >>
  fs [store_v_same_type_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [] >>
  rw [exhSemTheory.prim_exn_def, compile_v_def];

val do_app = prove(
  ``∀op vs s0 s0_pat env s res.
     do_app s0 op vs = SOME (s,res)
     ⇒
     do_app (map_csg compile_v s0) (Op op) (compile_vs vs) = SOME (map_csg compile_v s,map_result compile_v compile_v res)``,
  rw [decPropsTheory.map_csg_def] >>
  imp_res_tac exhPropsTheory.do_app_cases >>
  PairCases_on `s0` >>
  fs [exhSemTheory.do_app_def]
  >- tac
  >- tac
  >- (BasicProvers.EVERY_CASE_TAC >>
      fs [do_eq, patSemTheory.do_app_def] >>
      rw [exhSemTheory.prim_exn_def, patSemTheory.prim_exn_def, patSemTheory.Boolv_def, exhSemTheory.Boolv_def])
  >- tac
  >- (tac >>
      metis_tac [EL_MAP, map_sv_def, store_v_distinct, store_v_11])
  >- tac
  >- (tac >>
      metis_tac [EL_MAP, compile_v_def, optionTheory.NOT_SOME_NONE,
                 optionTheory.OPTION_MAP_DEF])
  >- (tac >>
      metis_tac [EL_MAP, map_sv_def, store_v_distinct, store_v_11])
  >- (tac >>
      metis_tac [EL_MAP, map_sv_def, store_v_distinct, store_v_11])
  >- (tac >>
      metis_tac [EL_MAP, map_sv_def, store_v_distinct, store_v_11])
  >- (tac >>
      metis_tac [EL_MAP, map_sv_def, store_v_distinct, store_v_11])
  >- tac
  >- tac
  >- tac
  >- (tac >> simp[char_list_to_v])
  >- (imp_res_tac v_to_char_list >> tac)
  >- tac
  >- (rw [patSemTheory.do_app_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      imp_res_tac v_to_list >>
      fs [])
  >- (tac >>
      UNABBREV_ALL_TAC >>
      fs [DECIDE ``~(x ≥ y:num) ⇔ x < y``, EL_MAP])
  >- tac
  >- (tac >>
      rw [rich_listTheory.map_replicate])
  >- (tac >>
      metis_tac [DECIDE ``~(x ≥ y:num) ⇔ x < y``, EL_MAP, map_sv_def, store_v_distinct, store_v_11, LENGTH_MAP])
  >- (tac >>
      metis_tac [DECIDE ``~(x ≥ y:num) ⇔ x < y``, EL_MAP, map_sv_def, store_v_distinct, store_v_11, LENGTH_MAP])
  >- (tac >>
      metis_tac [DECIDE ``~(x ≥ y:num) ⇔ x < y``, EL_MAP, map_sv_def, store_v_distinct, store_v_11, LENGTH_MAP])
  >- (tac >>
      rfs[EL_MAP] >> fs[] >> rw[] >> fs[]));

(* pattern compiler correctness *)

val sIf_correct = store_thm("sIf_correct",
  ``∀ck env s e1 e2 e3 res.
    evaluate ck env s (If e1 e2 e3) res ∧
    (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
    evaluate ck env s (sIf e1 e2 e3) res``,
  rpt gen_tac >>
  Cases_on`e2=(Bool T) ∧ e3=(Bool F)` >- (
    simp[sIf_def] >>
    simp[Once patSemTheory.evaluate_cases,patSemTheory.do_if_def] >>
    rw[] >> simp[] >> fs[] >>
    qpat_assum`X = Y`mp_tac >> rw[] >> fs[] >>
    fs[Bool_def,evaluate_Con_nil,patSemTheory.Boolv_def]) >>
  simp[sIf_def] >>
  Cases_on`e1`>>simp[]>>
  Cases_on`l`>>simp[]>>
  simp[Once patSemTheory.evaluate_cases] >>
  simp[patSemTheory.do_if_def] >> rw[] >> fs[evaluate_Con_nil] >>
  BasicProvers.EVERY_CASE_TAC >> fs[patPropsTheory.Boolv_disjoint] >> rw[] >>
  fs[patSemTheory.Boolv_def,conLangTheory.true_tag_def,conLangTheory.false_tag_def])

val v_to_list_no_closures = Q.prove (
  `!v vs.
    v_to_list v = SOME vs ∧
    no_closures v
    ⇒
    EVERY no_closures vs`,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  rw [patSemTheory.v_to_list_def] >>
  rw [] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs [compile_v_def, patSemTheory.v_to_list_def] >>
  rw []);

val char_list_to_v_no_closures = prove(
  ``∀ls. no_closures (char_list_to_v ls)``,
  Induct >> simp[patSemTheory.char_list_to_v_def])

val fo_correct = prove(
  ``(∀e. fo e ⇒
       ∀ck env s s' v.
         evaluate ck env s e (s',Rval v) ⇒
         no_closures v) ∧
    (∀es. fo_list es ⇒
       ∀ck env s s' vs.
         (evaluate_list ck env s es (s',Rval vs) ∨
          evaluate_list ck env s (REVERSE es) (s',Rval vs)) ⇒
         EVERY no_closures vs)``,
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``))>>
  simp[] >> reverse(rpt conj_tac) >> rpt gen_tac >> strip_tac >>
  simp[Once patSemTheory.evaluate_cases] >> rpt gen_tac >>
  TRY strip_tac >> fs[] >> simp[PULL_EXISTS,ETA_AX] >>
  TRY (metis_tac[])
  >- (
    rw[] >> rw[] >> TRY(metis_tac[]) >>
    imp_res_tac evaluate_list_append_Rval >>
    imp_res_tac evaluate_list_length >> fs[] >>
    Cases_on`v2`>>fs[LENGTH_NIL] >>
    fs[Q.SPECL[`ck`,`env`,`s1`,`[e]`](CONJUNCT2 patSemTheory.evaluate_cases)] >>
    metis_tac[] )
  >- (pop_assum mp_tac >> simp[Once patSemTheory.evaluate_cases])
  >- (pop_assum mp_tac >> simp[Once patSemTheory.evaluate_cases,PULL_EXISTS])
  >- (
    simp[patSemTheory.do_if_def]>>
    rpt gen_tac >>
    rw[] >> metis_tac[] )
  >- (
    rw[] >>
    PairCases_on`s2` >>
    imp_res_tac patPropsTheory.do_app_cases >> fs[patSemTheory.do_app_def] >> rw[] >> fs[] >>
    BasicProvers.EVERY_CASE_TAC >> fs[LET_THM,UNCURRY] >> rw[] >>
    fs[store_assign_def,store_lookup_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[LET_THM,UNCURRY] >> rw[] >>
    res_tac >> fs[] >>
    TRY (
      fs[Once SWAP_REVERSE_SYM] >> rw[] >>
      fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
      first_x_assum(match_mp_tac) >>
      simp[] >> NO_TAC) >>
    metis_tac [v_to_list_no_closures, char_list_to_v_no_closures])
  >- (
    metis_tac[rich_listTheory.EVERY_REVERSE]))
  |> SIMP_RULE (srw_ss())[];

val do_eq_no_closures = store_thm("do_eq_no_closures",
  ``(∀v1 v2. no_closures v1 ∧ no_closures v2 ⇒ do_eq v1 v2 ≠ Eq_closure) ∧
    (∀vs1 vs2. EVERY no_closures vs1 ∧ EVERY no_closures vs2 ⇒ do_eq_list vs1 vs2 ≠ Eq_closure)``,
  ho_match_mp_tac patSemTheory.do_eq_ind >>
  rw[patSemTheory.do_eq_def,ETA_AX] >> fs[] >>
  BasicProvers.CASE_TAC >> rw[] >> fs[])

val pure_correct = Q.store_thm("pure_correct",
  `(∀e. pure e ⇒
        ∀ck env s. (∃v. evaluate ck env s e (s,Rval v)) ∨
                   (∀res. ¬evaluate ck env s e res)) ∧
   (∀es. pure_list es ⇒
        ∀ck env s. ((∃vs. evaluate_list ck env s es (s,Rval vs)) ∨
                    (∀res. ¬evaluate_list ck env s es res)) ∧
                   ((∃vs. evaluate_list ck env s (REVERSE es) (s,Rval vs)) ∨
                    (∀res. ¬evaluate_list ck env s (REVERSE es) res)))`,
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  simp[pure_def] >> rw[] >> fs[]
  >- (simp[Once patSemTheory.evaluate_cases] >>
      last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac)
      >- metis_tac[] >> disj2_tac >>
      simp[Once patSemTheory.evaluate_cases])
  >- (simp[Once patSemTheory.evaluate_cases] >>
      last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac)
      >> TRY(metis_tac[] ) >> disj2_tac >>
      simp[Once patSemTheory.evaluate_cases])
  >- (simp[Once patSemTheory.evaluate_cases] >>
      simp[Once patSemTheory.evaluate_cases])
  >- (ntac 2 (simp[Once patSemTheory.evaluate_cases]) >>
      PROVE_TAC[patSemTheory.evaluate_rules,pair_CASES,optionTheory.option_CASES])
  >- (simp[Once patSemTheory.evaluate_cases] >> PROVE_TAC[patSemTheory.evaluate_rules])
  >- (
    first_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >>
    TRY (
      simp[Once patSemTheory.evaluate_cases] >>
      qmatch_assum_rename_tac`pure_op op` >>
      qmatch_assum_rename_tac`evaluate_list ck env s (REVERSE es) (s,Rval vsr)` >>
      Cases_on`do_app s op (REVERSE vsr)` >- (
        disj2_tac >>
        simp[Once patSemTheory.evaluate_cases] >>
        Cases >> simp[] >>
        Cases_on`op = Op(Op Opapp)`>>fs[] >>
        metis_tac[evaluate_determ,result_distinct,optionTheory.NOT_SOME_NONE,PAIR_EQ,result_11]) >>
      disj1_tac >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      PairCases_on`x`>>PairCases_on`s` >>
      imp_res_tac patPropsTheory.do_app_cases >> fs[patSemTheory.do_app_def] >> rw[] >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[pure_op_def,LET_THM] >> rw[] >>
      NO_TAC) >>
    disj2_tac >>
    simp[Once patSemTheory.evaluate_cases] )
  >- (
    last_x_assum(qspecl_then[`ck`,`env`,`s`](reverse o strip_assume_tac)) >>
    TRY (
      disj2_tac >> simp[Once patSemTheory.evaluate_cases] >> NO_TAC) >>
    qmatch_assum_rename_tac`evaluate_list ck env s (REVERSE es) (s,Rval vsr)` >> (
    reverse(Cases_on`LENGTH vsr = 2`) >- (
      disj2_tac >> simp[Once patSemTheory.evaluate_cases] >>
      Cases >> simp[] >>
      reverse conj_tac >-
        metis_tac[evaluate_determ,result_distinct,PAIR_EQ] >>
      spose_not_then strip_assume_tac >>
      imp_res_tac evaluate_determ >> fs[] >> rw[] >>
      PairCases_on`s` >>
      fs[patSemTheory.do_app_def] >>
      BasicProvers.EVERY_CASE_TAC>>
      fsrw_tac[ARITH_ss][LIST_EQ_REWRITE])) >>
    simp[Once patSemTheory.evaluate_cases] >>
    simp[Once (CONJUNCT1 patSemTheory.evaluate_cases)] >> (
    Cases_on`do_app s (Op (Op Equality)) (REVERSE vsr)` >- (
      disj2_tac >> Cases >> simp[] >>
      metis_tac[result_11,evaluate_determ,optionTheory.NOT_SOME_NONE,result_distinct,PAIR_EQ])) >>
    disj1_tac >>
    first_assum(match_exists_tac o concl) >> rw[] >>
    imp_res_tac fo_correct >>
    PairCases_on`s`>>fs[patSemTheory.do_app_def] >>
    Cases_on`REVERSE vsr`>>fs[]>>
    Cases_on`t`>>fs[]>>
    Cases_on`t'`>>fs[]>>
    BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
    fs[Once SWAP_REVERSE_SYM] >>
    imp_res_tac do_eq_no_closures )
  >- (
    qmatch_abbrev_tac`X ∨ Y`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def]>>
    Cases_on`X`>>fs[markerTheory.Abbrev_def]>-metis_tac[]>>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`If e1 e2 e3`](CONJUNCT1 patSemTheory.evaluate_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    imp_res_tac evaluate_determ >> fs[] >> rw[] >>
    qmatch_assum_rename_tac`do_if v e1 e2 = SOME x` >>
    fs[patSemTheory.do_if_def] >>
    first_x_assum(qspecl_then[`s`,`x`,`v`]strip_assume_tac o CONV_RULE(RESORT_FORALL_CONV List.rev)) >>
    every_case_tac >> fs[] >> rw[] >>
    metis_tac[])
  >- (
    qmatch_abbrev_tac`X ∨ Y`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def]>>rw[]>>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`Let e1 e2`](CONJUNCT1 patSemTheory.evaluate_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    imp_res_tac evaluate_determ >> fs[] >> rw[] >>
    metis_tac[] )
  >- (
    qmatch_abbrev_tac`X ∨ Y`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def]>>rw[]>>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`Seq e1 e2`](CONJUNCT1 patSemTheory.evaluate_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    imp_res_tac evaluate_determ >> fs[] >> rw[] >>
    metis_tac[] )
  >- (
    simp[Once patSemTheory.evaluate_cases] >>
    Q.PAT_ABBREV_TAC`renv = build_rec_env X Y ++ z` >>
    first_x_assum(qspecl_then[`ck`,`renv`,`s`]strip_assume_tac) >> fs[] >-
      metis_tac[] >>
    simp[Once patSemTheory.evaluate_cases] )
  >- simp[Once patSemTheory.evaluate_cases]
  >- (
    simp[Once patSemTheory.evaluate_cases] >>
    simp[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`e::es`](CONJUNCT2 patSemTheory.evaluate_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    TRY(metis_tac[]) >>
    disj2_tac >> Cases >> simp[] >>
    metis_tac[evaluate_determ,PAIR_EQ,result_11,result_distinct] )
  >- (
    rw[evaluate_list_append_Rval_iff] >>
    rw[not_evaluate_list_append] >>
    simp[(Q.SPECL[`ck`,`env`,`s`,`X::[]`](CONJUNCT2(patSemTheory.evaluate_cases))),PULL_EXISTS] >>
    simp[(Q.SPECL[`ck`,`env`,`s`,`[]`](CONJUNCT2(patSemTheory.evaluate_cases)))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`](reverse o strip_assume_tac)) >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`](reverse o strip_assume_tac)) >>
    metis_tac[]));

val ground_correct = store_thm("ground_correct",
  ``(∀e n. ground n e ⇒
      (∀ck env1 env2 s res.
          n ≤ LENGTH env1 ∧ n ≤ LENGTH env2 ∧
          (TAKE n env2 = TAKE n env1) ∧
          evaluate ck env1 s e res ⇒
          evaluate ck env2 s e res)) ∧
    (∀es n. ground_list n es ⇒
      (∀ck env1 env2 s res.
          n ≤ LENGTH env1 ∧ n ≤ LENGTH env2 ∧
          (TAKE n env2 = TAKE n env1) ⇒
          (evaluate_list ck env1 s es res ⇒
           evaluate_list ck env2 s es res) ∧
          (evaluate_list ck env1 s (REVERSE es) res ⇒
           evaluate_list ck env2 s (REVERSE es) res)))``,
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  rw[] >> pop_assum mp_tac >- (
    rw[Once patSemTheory.evaluate_cases] >>
    simp[Once patSemTheory.evaluate_cases] >>
    metis_tac[] )
  >- (
    first_x_assum(qspec_then`n+1`strip_assume_tac)>>
    first_x_assum(qspec_then`n`strip_assume_tac)>>
    rfs[] >>
    first_x_assum(qspecl_then[`ck`,`env1`,`env2`,`s`]mp_tac) >>
    simp[] >> strip_tac >>
    rw[Once evaluate_pat_cases] >>
    res_tac >>
    simp[Once evaluate_pat_cases] >>
    fsrw_tac[ARITH_ss][TAKE_CONS,PULL_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    fs[LIST_EQ_REWRITE] >>
    rfs[rich_listTheory.EL_TAKE] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    metis_tac[] )
  >- (
    reverse(rw[Once evaluate_pat_cases]) >>
    simp[Once evaluate_pat_cases]
    >- metis_tac[] >>
    disj1_tac >>
    qexists_tac`v` >>
    qpat_assum`do_if X Y Z = A`mp_tac >>
    simp[patSemTheory.do_if_def] >>
    rw[] >>
    metis_tac[] )
  >- (
    first_x_assum(qspec_then`n+1`strip_assume_tac)>>
    first_x_assum(qspec_then`n`strip_assume_tac)>>
    rfs[] >>
    first_x_assum(qspecl_then[`ck`,`env1`,`env2`,`s`]mp_tac) >>
    simp[] >> strip_tac >>
    rw[Once evaluate_pat_cases] >>
    res_tac >>
    simp[Once evaluate_pat_cases] >>
    fsrw_tac[ARITH_ss][TAKE_CONS,PULL_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    metis_tac[] )
  >- (
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`ck`,`env1`,`env2`]mp_tac) >> simp[] >> strip_tac >>
    last_x_assum(qspec_then`n`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`ck`,`env1`,`env2`]mp_tac) >> simp[] >> strip_tac >>
    Cases_on`res`>>Cases_on`r`>>
    rw[evaluate_list_append_Rval_iff,evaluate_list_append_Rerr] >>
    fs[(Q.SPECL[`ck`,`env`,`Y`,`[X]`](CONJUNCT2(evaluate_pat_cases))),PULL_EXISTS] >>
    fs[(Q.SPECL[`ck`,`env`,`Y`,`[]`](CONJUNCT2(evaluate_pat_cases))),PULL_EXISTS] >>
    metis_tac[]))

val sLet_correct = store_thm("sLet_correct",
  ``∀ck env s e1 e2 res.
    evaluate ck env s (Let e1 e2) res ∧
    SND res ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate ck env s (sLet e1 e2) res``,
  rw[sLet_def] >- (
    last_x_assum mp_tac >>
    simp[Once evaluate_pat_cases] >>
    rw[] >> rw[] >>
    pop_assum mp_tac >>
    rw[Once evaluate_pat_cases] )
  >- (
    qpat_assum`evaluate_pat A B C D E` mp_tac >>
    imp_res_tac pure_correct >>
    first_x_assum(qspecl_then[`s`,`env`,`ck`]strip_assume_tac) >>
    rw[Once evaluate_pat_cases] >> rw[] >>
    imp_res_tac evaluate_determ >> fs[] >> rw[] >>
    qspecl_then[`e2`,`0`]mp_tac(CONJUNCT1 ground_correct) >>
    rw[] >> res_tac >>
    metis_tac[]) >>
  qpat_assum`evaluate A B C D E` mp_tac >>
  rw[Once evaluate_pat_cases] >>
  qspecl_then[`e2`,`0`]mp_tac(CONJUNCT1 ground_correct) >>
  rw[] >> res_tac >>
  rw[Once evaluate_pat_cases] >> rw[] >>
  metis_tac[])

val Let_Els_correct = prove(
  ``∀n k e tag vs env ck s res us.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate ck (TAKE k vs ++ us ++ (Conv tag vs::env)) s e res ∧
    SND res ≠ Rerr (Rabort Rtype_error) ⇒
    evaluate ck (us ++ (Conv tag vs::env)) s (Let_Els n k e) res``,
  ho_match_mp_tac Let_Els_ind >> rw[Let_Els_def] >>
  match_mp_tac sLet_correct >>
  rw[Once evaluate_pat_cases] >>
  disj1_tac >>
  rw[Once evaluate_pat_cases] >>
  rw[Once evaluate_pat_cases] >>
  rw[Once evaluate_pat_cases] >>
  rw[Once evaluate_pat_cases] >>
  simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
  PairCases_on`s`>>simp[patSemTheory.do_app_def] >>
  qmatch_assum_rename_tac`SUC k ≤ LENGTH vs` >>
  first_x_assum(qspecl_then[`tag`,`vs`,`env`,`ck`,`(s0,s1,s2),s3`,`res`,`EL k vs::us`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    fs[arithmeticTheory.ADD1] >>
    `k < LENGTH vs` by simp[] >>
    fs[rich_listTheory.TAKE_EL_SNOC] >>
    fs[SNOC_APPEND] >>
    metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
  rw[])
val Let_Els_correct = prove(
  ``∀n k e tag vs env ck s res us enve.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate ck (TAKE k vs ++ us ++ (Conv tag vs::env)) s e res ∧
    (enve = us ++ (Conv tag vs::env)) ∧ SND res ≠ Rerr (Rabort Rtype_error)
    ⇒
    evaluate ck enve s (Let_Els n k e) res``,
  metis_tac[Let_Els_correct]);

val compile_pat_correct = prove(
  ``(∀p v s env res env4 ck count genv.
       pmatch (FST s) p v env = res ∧ res ≠ Match_type_error ⇒
       evaluate ck
         (compile_v v::env4)
         (map_csg compile_v ((count,s),genv))
         (compile_pat p)
         (map_csg compile_v ((count,s),genv)
         ,Rval (Boolv (∃env'. res = Match env')))) ∧
    (∀n ps qs vs s env env' res env4 ck count genv.
       pmatch_list (FST s) qs (TAKE n vs) env = Match env' ∧
       pmatch_list (FST s) ps (DROP n vs) env = res ∧ res ≠ Match_type_error ∧
       (n = LENGTH qs) ∧ n ≤ LENGTH vs ⇒
       evaluate ck
         (compile_vs vs ++ env4)
         (map_csg compile_v ((count,s),genv))
         (compile_pats n ps)
         (map_csg compile_v ((count,s),genv)
         ,Rval (Boolv (∃env'. res = Match env'))))``,
  ho_match_mp_tac compile_pat_ind >>
  rw[exhSemTheory.pmatch_def,compile_pat_def]
  >- rw[Bool_def,evaluate_Con_nil,patSemTheory.Boolv_def]
  >- (
    (Cases_on`v`>>fs[exhSemTheory.pmatch_def]>>pop_assum mp_tac >> rw[]) >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[decPropsTheory.map_csg_def,patSemTheory.do_app_def,EXISTS_PROD] >>
    rw[patSemTheory.do_eq_def] >>
    metis_tac[lit_same_type_sym])
  >- (
    Cases_on`v`>>fs[exhSemTheory.pmatch_def]>>pop_assum mp_tac >> rw[LENGTH_NIL_SYM] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[patSemTheory.do_app_def,decPropsTheory.map_csg_def] >>
    rw[patSemTheory.do_eq_def] >>
    simp[exhSemTheory.pmatch_def] >>
    fs[LENGTH_NIL])
  >- (
    match_mp_tac sIf_correct >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    fs[LENGTH_NIL_SYM,exhSemTheory.pmatch_def] >>
    fs[patSemTheory.do_app_def,decPropsTheory.map_csg_def] >>
    Cases_on`v`>>fs[exhSemTheory.pmatch_def]>>
    simp[patSemTheory.do_if_def] >>
    IF_CASES_TAC >> fs[] >> fs[] >>
    TRY ( simp[Bool_def,evaluate_Con_nil,patSemTheory.Boolv_def] >> NO_TAC) >>
    match_mp_tac Let_Els_correct >>
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt])
  >- (
    match_mp_tac sLet_correct >> simp[] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[Once evaluate_pat_cases] >>
    rw[patSemTheory.do_app_def,decPropsTheory.map_csg_def] >>
    Cases_on`v`>>fs[exhSemTheory.pmatch_def]>>
    fs[store_lookup_def] >>
    rw[] >> fs[] >> simp[EL_MAP] >>
    Cases_on`EL n (FST s)`>>
    fs[decPropsTheory.map_csg_def])
  >- (
    simp[Bool_def,evaluate_Con_nil,patSemTheory.Boolv_def] >> rw[] >>
    Cases_on`DROP (LENGTH qs) vs`>>fs[exhSemTheory.pmatch_def]) >>
  match_mp_tac sIf_correct >> simp[] >>
  rw[Once evaluate_pat_cases] >>
  qho_match_abbrev_tac`∃v e s2. evaluate ck B C (sLet D E) (s2,Rval v) ∧ P v e s2` >>
  qsuff_tac`∃v e s2. evaluate ck B C (Let D E) (s2,Rval v) ∧ P v e s2` >- (
    rw[] >> map_every qexists_tac[`v`,`e`,`s2`] >> simp[] >>
    match_mp_tac sLet_correct >> simp[] ) >>
  unabbrev_all_tac >>
  rw[Once evaluate_pat_cases] >>
  rw[Once evaluate_pat_cases] >>
  Cases_on`LENGTH qs = LENGTH vs` >- (
    fs[rich_listTheory.DROP_LENGTH_NIL_rwt,exhSemTheory.pmatch_def] ) >>
  simp[rich_listTheory.EL_APPEND1,EL_MAP] >>
  imp_res_tac exhPropsTheory.pmatch_list_pairwise >>
  Cases_on`DROP (LENGTH qs) vs` >> fs[exhSemTheory.pmatch_def] >>
  qmatch_assum_rename_tac`DROP (LENGTH qs) vs = v::ws` >>
  Q.PAT_ABBREV_TAC`env5 = X ++ env4` >>
  `LENGTH qs < LENGTH vs` by simp[] >>
  fs[rich_listTheory.DROP_EL_CONS] >>
  first_x_assum(qspecl_then[`v`,`s`,`env`,`env5`,`ck`]mp_tac) >>
  Cases_on`pmatch (FST s) p v env`>>fs[] >- (
    strip_tac >> qexists_tac`Boolv F` >>
    simp[patSemTheory.do_if_def,patPropsTheory.Boolv_disjoint,evaluate_Con_nil,Bool_def] >>
    simp[patSemTheory.Boolv_def]) >>
  strip_tac >> qexists_tac`Boolv T` >>
  simp[patSemTheory.do_if_def] >>
  Q.PAT_ABBREV_TAC`s2 = map_csg compile_v Y` >>
  qexists_tac`s2` >>
  simp[Abbr`s2`,Abbr`env5`] >>
  first_x_assum(qspecl_then[`qs++[p]`,`vs`,`s`,`env`]mp_tac) >>
  simp[] >>
  simp[rich_listTheory.TAKE_EL_SNOC,GSYM SNOC_APPEND] >>
  simp[exhPropsTheory.pmatch_list_snoc] >>
  imp_res_tac exhPropsTheory.pmatch_any_match >>
  qmatch_assum_rename_tac`pmatch_list (FST s) qs _ env = Match env2` >>
  last_x_assum(qspec_then`env2`strip_assume_tac)>>simp[]>>
  qmatch_assum_rename_tac`pmatch (FST s) p v env = Match env3`>>
  Cases_on`pmatch_list (FST s) ps ws env`>>simp[]>>
  Cases_on`pmatch_list (FST s) ps ws env3`>>fs[]>>
  metis_tac[exhPropsTheory.pmatch_any_match_error
           ,exhPropsTheory.pmatch_any_match
           ,exhPropsTheory.pmatch_any_no_match
           ,match_result_distinct])

val compile_row_correct = Q.prove(
  `(∀Nbvs0 p bvs0 s v menv bvs1 n f.
      (Nbvs0 = NONE::bvs0) ∧
      (pmatch (FST s) p v [] = Match menv) ∧
      (compile_row Nbvs0 p = (bvs1,n,f))
    ⇒ ∃menv4 bvs.
       (bvs1 = bvs ++ bvs0) ∧
       (LENGTH bvs = SUC n) ∧
       (LENGTH menv4 = SUC n) ∧
       (FILTER (IS_SOME o FST) (ZIP(bvs,menv4)) =
        MAP (λ(x,v). (SOME x, compile_v v)) menv) ∧
       ∀ck env count genv e res.
         evaluate ck (menv4++env) ((count, MAP (map_sv compile_v) (FST s), SND s),genv) e res ∧
         SND res ≠ Rerr (Rabort Rtype_error) ⇒
         evaluate ck (compile_v v::env) ((count, MAP (map_sv compile_v) (FST s), SND s),genv) (f e) res) ∧
   (∀bvsk0 nk k ps tag s qs vs menvk menv4k menv bvsk bvs0 bvs1 n1 f.
     (pmatch_list (FST s) qs (TAKE k vs) [] = Match menvk) ∧
     (pmatch_list (FST s) ps (DROP k vs) [] = Match menv) ∧
     (compile_cols bvsk0 nk k ps = (bvs1,n1,f)) ∧
     (bvsk0 = bvsk ++ NONE::bvs0) ∧
     (k = LENGTH qs) ∧ k ≤ LENGTH vs ∧ (LENGTH bvsk = nk) ∧
     (LENGTH menv4k = LENGTH bvsk) ∧
     (FILTER (IS_SOME o FST) (ZIP(bvsk,menv4k)) =
      MAP (λ(x,v). (SOME x, compile_v v)) menvk)
   ⇒ ∃menv4 bvs.
       (bvs1 = bvs ++ bvsk ++ NONE::bvs0) ∧
       (LENGTH bvs = n1) ∧ (LENGTH menv4 = n1) ∧
       (FILTER (IS_SOME o FST) (ZIP(bvs,menv4)) =
        MAP (λ(x,v). (SOME x, compile_v v)) menv) ∧
       ∀ck env count genv e res.
         evaluate ck (menv4++menv4k++(Conv tag (MAP compile_v vs))::env) ((count, MAP (map_sv compile_v) (FST s),SND s),genv) e res ∧
         SND res ≠ Rerr (Rabort Rtype_error) ⇒
         evaluate ck (menv4k++(Conv tag (MAP compile_v vs))::env) ((count, MAP (map_sv compile_v) (FST s),SND s),genv) (f e) res)`,
  ho_match_mp_tac compile_row_ind >>
  strip_tac >- (
    rw[pmatch_exh_def,compile_row_def] >> rw[] >>
    qexists_tac`[compile_v v]` >> rw[] ) >>
  strip_tac >- (
    rw[pmatch_exh_def,compile_row_def] >> rw[] >>
    qexists_tac`[compile_v v]` >> rw[] >>
    Cases_on`v`>>fs[pmatch_exh_def] >>
    pop_assum mp_tac >> rw[] ) >>
  strip_tac >- (
    rw[pmatch_exh_def,compile_row_def] >> fs[] >>
    Cases_on`v`>>fs[pmatch_exh_def] >>
    qpat_assum`X = Match menv`mp_tac >> rw[] >>
    qmatch_assum_rename_tac`pmatch_list (FST s) ps vs [] = Match menv` >>
    fs[LENGTH_NIL,pmatch_exh_def,LENGTH_NIL_SYM] >>
    Q.PAT_ABBREV_TAC`w = Conv X Y` >>
    qmatch_assum_rename_tac`Abbrev(w = Conv tag (MAP compile_v vs))` >>
    first_x_assum(qspecl_then[`tag`,`s`,`vs`]mp_tac) >> rw[] >> rw[] >>
    simp[] >>
    qexists_tac`menv4++[w]` >>
    simp[GSYM rich_listTheory.ZIP_APPEND,rich_listTheory.FILTER_APPEND] >>
    REWRITE_TAC[Once (GSYM APPEND_ASSOC),Once(GSYM rich_listTheory.CONS_APPEND)] >>
    rpt strip_tac >> res_tac >> fs[] ) >>
  strip_tac >- (
    rw[compile_row_def] >>
    Cases_on`v`>>fs[pmatch_exh_def] >>
    qpat_assum`X = Match menv`mp_tac >> BasicProvers.CASE_TAC >>
    BasicProvers.CASE_TAC >>
    rw[] >> fs[UNCURRY,LET_THM] >> rw[] >>
    qmatch_assum_rename_tac`pmatch (FST s) p v [] = Match menv` >>
    first_x_assum(qspecl_then[`s`,`v`]mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`t = compile_row X Y` >>
    `∃bvs1 n f. t = (bvs1,n,f)` by simp[GSYM EXISTS_PROD] >>
    qunabbrev_tac`t` >> simp[] >> rw[] >> simp[] >>
    Q.PAT_ABBREV_TAC`w = Loc X` >>
    qexists_tac`menv4++[w]` >>
    simp[GSYM rich_listTheory.ZIP_APPEND,rich_listTheory.FILTER_APPEND] >>
    REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
    rpt strip_tac >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rfs[] >>
    match_mp_tac sLet_correct >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[Once evaluate_pat_cases] >>
    simp[patSemTheory.do_app_def] >> simp[Abbr`w`] >>
    fs[store_lookup_def] >>
    simp[EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_row_def] >>
    imp_res_tac exhPropsTheory.pmatch_list_pairwise >>
    imp_res_tac EVERY2_LENGTH >>
    fs[LENGTH_NIL,pmatch_exh_def] ) >>
  rw[compile_row_def] >>
  `∃bvsk1 nk1 f1. compile_row (NONE::(bvsk++[NONE]++bvs0)) p = (bvsk1,nk1,f1)` by
    simp[GSYM EXISTS_PROD] >> fs[LET_THM] >>
  `∃bvs n fs. compile_cols bvsk1 (LENGTH bvsk + 1 + nk1) (LENGTH qs + 1) ps = (bvs,n,fs)` by
    simp[GSYM EXISTS_PROD] >> fs[] >>
  rw[] >>
  Cases_on`DROP (LENGTH qs) vs`>>fs[pmatch_exh_def] >>
  qmatch_assum_rename_tac`DROP (LENGTH qs) vs = v::ws` >>
  Cases_on`pmatch (FST s) p v []`>>fs[] >>
  first_x_assum(qspecl_then[`s`,`v`]mp_tac) >> simp[] >>
  strip_tac >> rw[] >>
  first_x_assum(qspecl_then[`tag`,`s`,`qs++[p]`,`vs`]mp_tac) >>
  Cases_on`LENGTH vs = LENGTH qs`>>fs[rich_listTheory.DROP_LENGTH_NIL_rwt] >>
  `LENGTH qs < LENGTH vs` by simp[] >>
  fs[rich_listTheory.DROP_EL_CONS] >>
  simp[rich_listTheory.TAKE_EL_SNOC,Once(GSYM SNOC_APPEND)] >>
  simp[exhPropsTheory.pmatch_list_snoc] >>
  imp_res_tac (CONJUNCT1 exhPropsTheory.pmatch_any_match) >>
  pop_assum(qspec_then`menvk`strip_assume_tac) >> simp[] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac (CONJUNCT2 exhPropsTheory.pmatch_any_match) >>
  rpt(pop_assum(qspec_then`[]`mp_tac)) >>
  ntac 2 strip_tac >> simp[] >>
  disch_then(qspec_then`bvs0`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
  simp[] >>
  qmatch_assum_rename_tac`FILTER _ (ZIP(bvs2,menv4)) = MAP _ env2` >>
  disch_then(qspec_then`menv4 ++ menv4k`mp_tac) >>
  simp[rich_listTheory.FILTER_APPEND,GSYM(rich_listTheory.ZIP_APPEND)] >>
  discharge_hyps >- (
    qpat_assum`pmatch (FST s) p v menvk = X`mp_tac >>
    simp[Once (CONJUNCT1 exhPropsTheory.pmatch_nil)] >>
    REWRITE_TAC[GSYM MAP_APPEND] >> PROVE_TAC[] ) >>
  rw[] >> rw[] >> simp[] >>
  qmatch_assum_rename_tac`LENGTH bvs3 = LENGTH menv3` >>
  qexists_tac`menv3 ++ menv4` >> simp[] >>
  simp[rich_listTheory.FILTER_APPEND,GSYM(rich_listTheory.ZIP_APPEND)] >>
  conj_tac >- (
    qpat_assum`pmatch_list (FST s) ps ww env2 = X`mp_tac >>
    simp[Once (CONJUNCT2 exhPropsTheory.pmatch_nil)] >>
    REWRITE_TAC[GSYM MAP_APPEND] >> PROVE_TAC[] ) >>
  rw[] >>
  match_mp_tac sLet_correct >>
  simp[Once evaluate_pat_cases] >>
  simp[Once evaluate_pat_cases] >>
  simp[Once evaluate_pat_cases] >>
  simp[Once evaluate_pat_cases] >>
  simp[Once evaluate_pat_cases] >>
  simp[patSemTheory.do_app_def] >>
  simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
  simp[EL_MAP])

(* value relation *)

val bind_def = Define`
  (bind V 0 0 ⇔ T) ∧
  (bind V (SUC n1) (SUC n2) ⇔ V n1 n2) ∧
  (bind V _ _ ⇔ F)`

val bind_mono = store_thm("bind_mono",
  ``(∀x y. V1 x y ⇒ V2 x y) ⇒ bind V1 x y ⇒ bind V2 x y``,
  Cases_on`x`>>Cases_on`y`>>rw[bind_def])
val _ = export_mono"bind_mono"

val bindn_def = Define`bindn = FUNPOW bind`

val bind_thm = store_thm("bind_thm",
  ``∀V x y. bind V x y =
      if x = 0 then y = 0 else
      if y = 0 then x = 0 else
      V (x-1) (y-1)``,
  gen_tac >> Cases >> Cases >> rw[bind_def])

val bindn_mono = store_thm("bindn_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ⇒
    bindn n R1 x y ⇒ bindn n R2 x y``,
  rw[bindn_def] >>
  match_mp_tac (MP_CANON FUNPOW_mono) >>
  simp[] >> metis_tac[bind_mono] )
val _ = export_mono"bindn_mono"

val bindn_thm = store_thm("bindn_thm",
  ``∀n k1 k2.
    bindn n R k1 k2 ⇔
    if k1 < n ∧ k2 < n then k1 = k2
    else n ≤ k1 ∧ n ≤ k2 ∧ R (k1-n) (k2-n)``,
  Induct>>simp[bindn_def,arithmeticTheory.FUNPOW_SUC] >>
  Cases>>Cases>>simp[bind_def,GSYM bindn_def])

val (exp_rel_rules,exp_rel_ind,exp_rel_cases) = Hol_reln`
  (exp_rel z1 z2 V e1 e2
   ⇒ exp_rel z1 z2 V (Raise e1) (Raise e2)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel (z1+1) (z2+1) (bind V) e12 e22
   ⇒ exp_rel z1 z2 V (Handle e11 e12) (Handle e21 e22)) ∧
  (exp_rel z1 z2 V (Lit l) (Lit l)) ∧
  (LIST_REL (exp_rel z1 z2 V) es1 es2
   ⇒ exp_rel z1 z2 V (Con tag es1) (Con tag es2)) ∧
  ((k1 < z1 ∧ k2 < z2 ∧ V k1 k2) ∨ (z1 ≤ k1 ∧ z2 ≤ k2 ∧ (k1 = k2))
   ⇒ exp_rel z1 z2 V (Var_local k1) (Var_local k2)) ∧
  (exp_rel z1 z2 V (Var_global k) (Var_global k)) ∧
  (exp_rel (z1+1) (z2+1) (bind V) e1 e2
   ⇒ exp_rel z1 z2 V (Fun e1) (Fun e2)) ∧
  (LIST_REL (exp_rel z1 z2 V) es1 es2
   ⇒ exp_rel z1 z2 V (App op es1) (App op es2)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel z1 z2 V e12 e22 ∧ exp_rel z1 z2 V e13 e23
   ⇒ exp_rel z1 z2 V (If e11 e12 e13) (If e21 e22 e23)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel (z1+1) (z2+1) (bind V) e12 e22
   ⇒ exp_rel z1 z2 V (Let e11 e12) (Let e21 e22)) ∧
  (exp_rel z1 z2 V e11 e21 ∧ exp_rel z1 z2 V e12 e22
   ⇒ exp_rel z1 z2 V (Seq e11 e12) (Seq e21 e22)) ∧
  (LIST_REL (exp_rel (z1+(SUC(LENGTH es1))) (z2+(SUC(LENGTH es2))) (bindn (SUC (LENGTH es1)) V)) es1 es2 ∧
   exp_rel (z1+(LENGTH es1)) (z2+(LENGTH es2)) (bindn (LENGTH es1) V) e1 e2
   ⇒ exp_rel z1 z2 V (Letrec es1 e1) (Letrec es2 e2)) ∧
  (exp_rel z1 z2 V (Extend_global n) (Extend_global n))`;

val exp_rel_refl = store_thm("exp_rel_refl",
  ``(∀e z V. (∀k. k < z ⇒ V k k) ⇒ exp_rel z z V e e) ∧
    (∀es z V. (∀k. k < z ⇒ V k k) ⇒ LIST_REL (exp_rel z z V) es es)``,
  ho_match_mp_tac(TypeBase.induction_of``:patLang$exp``) >> rw[] >>
  TRY (first_x_assum match_mp_tac) >>
  rw[Once exp_rel_cases] >>
  TRY (first_x_assum match_mp_tac) >>
  TRY (metis_tac[]) >>
  TRY (Cases>>simp[bind_def]>>NO_TAC) >>
  TRY (Cases_on`n < z` >>simp[] >> NO_TAC) >>
  rw[bindn_thm] >>
  Cases_on`k < SUC (LENGTH es)` >> simp[] >>
  Cases_on`k < LENGTH es` >> simp[])

val exp_rel_mono = store_thm("exp_rel_mono",
  ``(∀x y. V1 x y ⇒ V2 x y) ⇒
    exp_rel z1 z2 V1 e1 e2 ⇒
    exp_rel z1 z2 V2 e1 e2``,
  strip_tac >> strip_tac >> last_x_assum mp_tac >>
  qid_spec_tac`V2` >> pop_assum mp_tac >>
  map_every qid_spec_tac[`e2`,`e1`,`V1`,`z2`,`z1`] >>
  ho_match_mp_tac exp_rel_ind >>
  strip_tac >- ( rw[] >> rw[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_mono >> rw[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_rel_cases] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_rel_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_mono >> rw[] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_rel_cases] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_mono >> rw[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_rel_cases] >> TRY (
      match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
      HINT_EXISTS_TAC >> simp[] >> rw[] >>
      first_x_assum match_mp_tac >>
      match_mp_tac bindn_mono >>
      simp[] ) >>
    first_x_assum match_mp_tac >>
    match_mp_tac bindn_mono >>
    simp[] ) >>
  ( rw[] >> rw[Once exp_rel_cases] ))
val _ = export_mono"exp_rel_mono";

val exp_rel_lit = store_thm("exp_rel_lit",
  ``(exp_rel z1 z2 V (Lit l) e2 ⇔ (e2 = Lit l)) ∧
    (exp_rel z1 z2 V e1 (Lit l) ⇔ (e1 = Lit l)) ∧
    (exp_rel z1 z2 V (Bool b) e2 ⇔ (e2 = Bool b)) ∧
    (exp_rel z1 z2 V e1 (Bool b) ⇔ (e1 = Bool b))``,
  rw[Once exp_rel_cases] >>
  rw[Once exp_rel_cases,Bool_def] )
val _ = export_rewrites["exp_rel_lit"];

val bind_O = store_thm("bind_O",
  ``∀R1 R2. bind (R2 O R1) = bind R2 O bind R1``,
  rw[] >> simp[FUN_EQ_THM] >>
  simp[relationTheory.O_DEF] >>
  rw[bind_thm,relationTheory.O_DEF,EQ_IMP_THM] >> rfs[] >- (
    qexists_tac`SUC y` >> simp[] ) >>
  qexists_tac`y-1` >> simp[])
val _ = export_rewrites["bind_O"];

val bindn_O = store_thm("bindn_O",
  ``∀R1 R2 n. bindn n (R2 O R1) = bindn n R2 O bindn n R1``,
  rw[FUN_EQ_THM,bindn_thm,relationTheory.O_DEF] >>
  rw[EQ_IMP_THM] >> simp[] >> fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>fsrw_tac[ARITH_ss][]
  >- (qexists_tac`y+n` >> simp[]) >>
  (qexists_tac`y-n` >> simp[]))
val _ = export_rewrites["bindn_O"];

val exp_rel_trans = prove(
  ``∀z1 z2 V1 e1 e2. exp_rel z1 z2 V1 e1 e2 ⇒
      ∀z3 V2 e3. exp_rel z2 z3 V2 e2 e3 ⇒ exp_rel z1 z3 (V2 O V1) e1 e3``,
   ho_match_mp_tac (theorem"exp_rel_strongind") >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) >>
     rfs[EVERY2_EVERY,EVERY_MEM] >>
     fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) >>
     simp[relationTheory.O_DEF] >> metis_tac[]) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) >>
     rfs[EVERY2_EVERY,EVERY_MEM] >>
     fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) >>
     rfs[EVERY2_EVERY,EVERY_MEM] >>
     fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_rel_cases]) ))
val exp_rel_trans = store_thm("exp_rel_trans",
  ``∀z1 z2 z3 V1 V2 V3 e1 e2 e3.
      exp_rel z1 z2 V1 e1 e2 ∧
      exp_rel z2 z3 V2 e2 e3 ∧
      (V3 = V2 O V1) ⇒
      exp_rel z1 z3 V3 e1 e3``,
  metis_tac[exp_rel_trans])

val env_rel_def = Define`
  env_rel R env1 env2 k1 k2 ⇔
    k1 < LENGTH env1 ∧ k2 < LENGTH env2 ∧ R (EL k1 env1) (EL k2 env2)`

val env_rel_mono = store_thm("env_rel_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ⇒
    env_rel R1 env1 env2 k1 k2 ⇒
    env_rel R2 env1 env2 k1 k2``,
  rw[env_rel_def])
val _ = export_mono"env_rel_mono";

val env_rel_cons = prove(
  ``R v1 v2 ∧
    bind (env_rel R env1 env2) k1 k2
    ⇒ env_rel R (v1::env1) (v2::env2) k1 k2``,
  Cases_on`k1`>>Cases_on`k2`>>rw[env_rel_def,bind_def])

val (v_rel_rules,v_rel_ind,v_rel_cases) = Hol_reln`
  (v_rel (Litv l) (Litv l)) ∧
  (LIST_REL v_rel vs1 vs2
   ⇒ v_rel (Conv tag vs1) (Conv tag vs2)) ∧
  (exp_rel (SUC(LENGTH env1)) (SUC(LENGTH env2))
    (bind (env_rel v_rel env1 env2)) exp1 exp2
   ⇒ v_rel (Closure env1 exp1) (Closure env2 exp2)) ∧
  (LIST_REL (exp_rel (SUC(LENGTH funs1)+LENGTH env1) (SUC(LENGTH funs2)+LENGTH env2)
              (bindn (SUC (LENGTH funs1)) (env_rel v_rel env1 env2)))
            funs1 funs2
   ⇒ v_rel (Recclosure env1 funs1 n) (Recclosure env2 funs2 n)) ∧
  (v_rel (Loc n) (Loc n)) ∧
  (LIST_REL v_rel vs1 vs2
   ⇒ v_rel (Vectorv vs1) (Vectorv vs2))`;

val v_rel_lit = store_thm("v_rel_lit",
  ``(v_rel (Litv l) v2 ⇔ (v2 = Litv l)) ∧
    (v_rel v1 (Litv l) ⇔ (v1 = Litv l)) ∧
    (v_rel (Boolv b) v2 ⇔ (v2 = Boolv b)) ∧
    (v_rel v1 (Boolv b) ⇔ (v1 = Boolv b))``,
  rw[Once v_rel_cases] >> rw[Once v_rel_cases,patSemTheory.Boolv_def] )
val _ = export_rewrites["v_rel_lit"]

val v_rel_loc = store_thm("v_rel_loc",
  ``(v_rel (Loc l) v2 ⇔ (v2 = Loc l)) ∧
    (v_rel v1 (Loc l) ⇔ (v1 = Loc l))``,
  rw[Once v_rel_cases] >> rw[Once v_rel_cases] )
val _ = export_rewrites["v_rel_loc"]

val v_rel_refl = store_thm("v_rel_refl",
  ``∀v. v_rel v v``,
  qsuff_tac`(∀v. v_rel v v) ∧ (∀vs. LIST_REL v_rel vs vs)`>-rw[]>>
  ho_match_mp_tac(TypeBase.induction_of``:patSem$v``)>>
  rw[] >> rw[Once v_rel_cases] >>
  TRY (
    match_mp_tac (CONJUNCT1 exp_rel_refl) >>
    Cases>>simp[bind_def,env_rel_def]>>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] ) >>
  match_mp_tac (CONJUNCT2 exp_rel_refl) >>
  simp[bindn_thm] >> rw[env_rel_def] >>
  qmatch_assum_rename_tac`k < LENGTH vs + SUC (LENGTH ls)` >>
  Cases_on`k < SUC (LENGTH ls)`>>simp[] >>
  fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
  simp[])
val _ = export_rewrites["v_rel_refl"]

val v_rel_trans = store_thm("v_rel_trans",
  ``∀v1 v2. v_rel v1 v2 ⇒ ∀v3. v_rel v2 v3 ⇒ v_rel v1 v3``,
  ho_match_mp_tac (theorem"v_rel_strongind") >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    match_mp_tac LIST_REL_trans >>
    qexists_tac`vs2` >> simp[] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >> rw[] >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`exp_rel z1 z2 V1 exp1 exp2` >>
    qmatch_assum_abbrev_tac`exp_rel z2 z3 V2 exp2 exp3` >>
    match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
    qexists_tac`V2 O V1` >>
    conj_tac >- (
      simp[relationTheory.O_DEF,Abbr`V1`,Abbr`V2`] >>
      simp[bind_thm,env_rel_def] >>
      rw[] >> fsrw_tac[ARITH_ss][] >> rfs[] ) >>
    match_mp_tac exp_rel_trans >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_rel_cases,PULL_EXISTS] >> rw[] >>
    simp[Once v_rel_cases,PULL_EXISTS] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS,MEM_EL] >> rw[] >>
    res_tac >>
    qmatch_assum_abbrev_tac`exp_rel z1 z2 V1 exp1 exp2` >>
    qmatch_assum_abbrev_tac`exp_rel z2 z3 V2 exp2 exp3` >>
    match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
    qexists_tac`V2 O V1` >>
    conj_tac >- (
      simp[relationTheory.O_DEF,Abbr`V1`,Abbr`V2`] >>
      simp[bindn_thm,env_rel_def] >>
      simp[arithmeticTheory.ADD1] >>
      rw[] >> fsrw_tac[ARITH_ss][] >>
      rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
      fsrw_tac[ARITH_ss][] ) >>
    metis_tac[exp_rel_trans]) >>
  rpt gen_tac >> strip_tac >>
  simp[Once v_rel_cases,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  simp[Once v_rel_cases,PULL_EXISTS] >>
  match_mp_tac LIST_REL_trans >>
  qexists_tac`vs2` >> simp[] >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS,MEM_EL] );

val bind_inv = store_thm("bind_inv",
  ``∀V. bind (inv V) = inv (bind V)``,
  rw[FUN_EQ_THM,bind_thm,relationTheory.inv_DEF] >>
  rw[])
val _ = export_rewrites["bind_inv"]

val bindn_inv = store_thm("bindn_inv",
  ``∀V n. bindn n (inv V) = inv (bindn n V)``,
  rw[FUN_EQ_THM,bindn_thm,relationTheory.inv_DEF] >>
  rw[] >> simp[] >> fs[] >> simp[])
val _ = export_rewrites["bindn_inv"]

val exp_rel_sym = store_thm("exp_rel_sym",
  ``∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒ exp_rel z2 z1 (inv V) e2 e1``,
  ho_match_mp_tac exp_rel_ind >> rw[] >>
  simp[Once exp_rel_cases] >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS,relationTheory.inv_DEF] )

val v_rel_sym = store_thm("v_rel_sym",
  ``∀v1 v2. v_rel v1 v2 ⇒ v_rel v2 v1``,
  ho_match_mp_tac v_rel_ind >> rw[] >>
  simp[Once v_rel_cases] >>
  fs[LIST_REL_EL_EQN] >> rw[] >> rfs[] >>
  TRY(first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th))) >>
  first_x_assum (strip_assume_tac o MATCH_MP exp_rel_sym) >>
  match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
  fsrw_tac[ARITH_ss][] >>
  HINT_EXISTS_TAC >>
  simp[relationTheory.inv_DEF,bind_thm,bindn_thm] >>
  rw[] >> fsrw_tac[ARITH_ss][env_rel_def])

(* semantic functions respect relation *)

val do_eq_def = patSemTheory.do_eq_def

val do_eq_v_rel = store_thm("do_eq_v_rel",
  ``∀v1 v2. v_rel v1 v2 ⇒ ∀v3 v4. v_rel v3 v4 ⇒ do_eq v1 v3 = do_eq v2 v4``,
  ho_match_mp_tac v_rel_ind >>
  simp[do_eq_def] >> rw[] >>
  Cases_on`v3`>>Cases_on`v4`>>fs[do_eq_def] >>
  pop_assum mp_tac >> simp[Once v_rel_cases] >> rw[] >>
  imp_res_tac EVERY2_LENGTH >> fs[] >> rw[] >>
  ntac 2 (pop_assum kall_tac) >>
  qmatch_assum_rename_tac`LIST_REL v_rel l1 l2` >>
  ntac 3 (pop_assum mp_tac) >>
  map_every qid_spec_tac[`l2`,`l1`,`vs2`,`vs1`] >>
  Induct >> simp[PULL_EXISTS] >>
  Cases_on`l1`>>Cases_on`l2`>>simp[do_eq_def] >>
  rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  res_tac >> fs[])

val do_opapp_v_rel = store_thm("do_opapp_v_rel",
  ``∀vs vs'.
    LIST_REL v_rel vs vs' ⇒
    OPTION_REL
      (λ(env1,e1) (env2,e2).
        exp_rel (LENGTH env1) (LENGTH env2) (env_rel v_rel env1 env2) e1 e2)
      (do_opapp vs)
      (do_opapp vs')``,
  rw[patSemTheory.do_opapp_def] >>
  BasicProvers.CASE_TAC >> fs[quotient_optionTheory.OPTION_REL_def] >> rw[] >>
  Cases_on`t`>>fs[quotient_optionTheory.OPTION_REL_def] >> rw[] >>
  Cases_on`t'`>>fs[quotient_optionTheory.OPTION_REL_def] >> rw[] >>
  Cases_on`h`>>fs[quotient_optionTheory.OPTION_REL_def] >>
  last_x_assum mp_tac >>
  simp[Once v_rel_cases] >> rw[] >>
  rw[quotient_optionTheory.OPTION_REL_def] >>
  TRY (imp_res_tac LIST_REL_LENGTH >> fs[] >> NO_TAC) >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS] >>
  match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
  simp[patSemTheory.build_rec_env_def] >> res_tac >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  qmatch_assum_abbrev_tac`exp_rel z1 z2 V e1 e2` >>
  qexists_tac`V` >>
  simp[Abbr`V`,bindn_thm,bind_thm,env_rel_def] >>
  TRY (
    Cases >> Cases >> simp[] >>
    unabbrev_all_tac >> simp[] >> NO_TAC) >>
  reverse conj_tac >- metis_tac[arithmeticTheory.ADD_SYM,arithmeticTheory.ADD_ASSOC] >>
  Cases >> Cases >> rw[env_rel_def] >> fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
  simp[Once v_rel_cases] >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS,arithmeticTheory.ADD1,Abbr`z1`,Abbr`z2`] >>
  simp[])

val v_to_list_SOME = prove(
  ``∀v ls.
    v_to_list v = SOME ls ⇒
         (v = Conv nil_tag []) ∨
         (∃v1 v2 t.
           v = Conv cons_tag [v1;v2] ∧
           v_to_list v2 = SOME t ∧
           ls = v1::t)``,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val v_to_list_v_rel = prove(
  ``∀l1 l2 n l3.
    v_rel l1 l2 ∧ v_to_list l1 = SOME l3 ⇒
    ∃l4. v_to_list l2 = SOME l4 ∧
         LIST_REL v_rel l3 l4``,
  ho_match_mp_tac patSemTheory.v_to_list_ind >>
  simp[patSemTheory.v_to_list_def] >> rw[] >- (
    fs[Once v_rel_cases]>>
    simp[patSemTheory.v_to_list_def] ) >>
  last_x_assum mp_tac >>
  simp[Once v_rel_cases] >> rw[] >>
  simp[patSemTheory.v_to_list_def] >>
  last_x_assum mp_tac >>
  BasicProvers.CASE_TAC >> rw[] >>
  res_tac >> simp[])

val v_to_char_list_v_rel = prove(
  ``∀l1 l2 n l3.
    v_rel l1 l2 ∧ v_to_char_list l1 = SOME l3 ⇒
    v_to_char_list l2 = SOME l3``,
  ho_match_mp_tac patSemTheory.v_to_char_list_ind >>
  simp[patSemTheory.v_to_char_list_def] >> rw[] >- (
    fs[Once v_rel_cases]>>
    simp[patSemTheory.v_to_char_list_def] ) >>
  last_x_assum mp_tac >>
  simp[Once v_rel_cases] >> rw[] >>
  simp[patSemTheory.v_to_char_list_def] >>
  last_x_assum mp_tac >>
  BasicProvers.CASE_TAC >> rw[] >>
  res_tac >> simp[])

val do_app_def = patSemTheory.do_app_def
val csg_rel_def = decPropsTheory.csg_rel_def

val do_app_v_rel = store_thm("do_app_v_rel",
  ``∀env s op env' s' vs vs'.
      LIST_REL v_rel vs vs' ⇒
      csg_rel v_rel s s' ⇒
      OPTION_REL
        (λ(s1,res1) (s2,res2).
          csg_rel v_rel s1 s2 ∧
          result_rel v_rel v_rel res1 res2)
        (do_app s op vs)
        (do_app s' op vs')``,
  rw[] >>
  rw[optionTheory.OPTREL_def] >>
  Cases_on`do_app s op vs`>>rw[]>-(
    PairCases_on`s` >>
    PairCases_on`s'` >>
    fs[csg_rel_def] >> rw[] >>
    fs[patSemTheory.do_app_def] >>
    Cases_on`vs`>>fs[]>>
    Cases_on`ys`>>fs[]>-(
      rw[]>>fs[]>>
      Cases_on`op`>>fs[]>>rw[]>>
      TRY(Cases_on`o'`>>fs[LET_THM])>>
      TRY(Cases_on`o''`>>fs[LET_THM])>>
      BasicProvers.EVERY_CASE_TAC>>fs[LET_THM,UNCURRY]>>rw[]>>
      fs[LIST_REL_EL_EQN,optionTheory.OPTREL_def] >>
      fs[Once v_rel_cases,store_lookup_def,store_assign_def] >>
      rw[] >>
      fs[patSemTheory.v_to_list_def,patSemTheory.v_to_char_list_def] >>
      imp_res_tac v_to_list_v_rel >>
      imp_res_tac v_to_char_list_v_rel >>
      TRY(CHANGED_TAC(fs[store_v_same_type_def]) >> every_case_tac >> fs[]) >>
      metis_tac[v_rel_cases,v_rel_sym,optionTheory.NOT_SOME_NONE,LIST_REL_LENGTH,sv_rel_def]) >>
    rw[] >> fs[] >>
    Cases_on`xs`>>fs[] >- (
      Cases_on`op`>>fs[]>>rw[]>>
      Cases_on`o'`>>fs[]>>
      Cases_on`o''`>>fs[]
      >- (BasicProvers.EVERY_CASE_TAC >>
          fs [LET_THM, store_alloc_def])
      >- (BasicProvers.EVERY_CASE_TAC >>
          fs [LET_THM, store_alloc_def])
      >- (
        imp_res_tac do_eq_v_rel >>
        BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[]>>fs[] )
      >- (
        BasicProvers.EVERY_CASE_TAC >>
        fs[store_assign_def] >>
        rw[] >> imp_res_tac LIST_REL_LENGTH >> fs[] >>
        fs[store_v_same_type_def] >>
        BasicProvers.EVERY_CASE_TAC >> fs[LIST_REL_EL_EQN] >>
        metis_tac[sv_rel_def])
      >- (
        BasicProvers.EVERY_CASE_TAC >>
        fs[store_alloc_def,LET_THM] )
      >- (
        Cases_on`x`>>fs[]>>TRY(Cases_on`l:lit`)>>fs[]>>
        Cases_on`y`>>fs[]>>TRY(Cases_on`l:lit`)>>fs[]>>
        rw[] >> fs[] >> rw[] >>
        fs[store_lookup_def] >>
        rw[] >> fs[] >>
        imp_res_tac LIST_REL_LENGTH >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[LET_THM] >> rw[] >>
        fs[LIST_REL_EL_EQN] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        metis_tac[sv_rel_def] )
      >- (BasicProvers.EVERY_CASE_TAC >> fs[])
      >- (
        Cases_on`x`>>fs[]>>TRY(Cases_on`l:lit`)>>fs[]>>
        Cases_on`y`>>fs[]>>TRY(Cases_on`l:lit`)>>fs[]>>
        rw[] >> fs[] >> rw[] >>
        fs[store_lookup_def] >>
        rw[] >> fs[] >>
        imp_res_tac LIST_REL_LENGTH >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[LET_THM] >> rw[] >>
        fs[LIST_REL_EL_EQN] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        pop_assum mp_tac >>
        simp[Once v_rel_cases])
      >- (BasicProvers.EVERY_CASE_TAC >>
          fs [LET_THM, store_alloc_def])
      >- (BasicProvers.EVERY_CASE_TAC >>
          fs [LET_THM, store_lookup_def] >>
          imp_res_tac LIST_REL_LENGTH >> fs[] >>
          rw [] >>
          fs[LIST_REL_EL_EQN] >>
          rpt (pop_assum mp_tac) >>
          rw [] >>
          res_tac >>
          pop_assum mp_tac >>
          ASM_REWRITE_TAC [sv_rel_def]) ) >>
    rw[] >>
    Cases_on`h'`>>fs[]>>Cases_on`l`>>fs[]>>rw[]>>fs[]>>
    Cases_on`y`>>fs[]>>rw[]>>fs[]>>
    BasicProvers.EVERY_CASE_TAC>>fs[LET_THM]>>rw[] >>
    fs[store_lookup_def,store_assign_def,
       store_v_same_type_def,LIST_REL_EL_EQN] >>
    rw[] >> rfs[] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    metis_tac[sv_rel_def] ) >>
  PairCases_on`s`>>PairCases_on`s'`>>
  imp_res_tac patPropsTheory.do_app_cases >>
  fs[patSemTheory.do_app_def,csg_rel_def] >>
  rw[]>>fs[csg_rel_def]>>
  fs[UNCURRY]>>rw[csg_rel_def] >>
  fs[store_assign_def,store_lookup_def]>>
  fs[store_alloc_def,LET_THM]>>
  imp_res_tac LIST_REL_LENGTH >> rw[]>>fs[]>>rw[csg_rel_def,sv_rel_def] >>
  imp_res_tac do_eq_v_rel >> fs[] >>
  imp_res_tac v_to_list_v_rel >> simp[] >>
  imp_res_tac v_to_char_list_v_rel >> simp[] >>
  BasicProvers.EVERY_CASE_TAC>>fs[]>>rw[csg_rel_def]>>
  fs[LIST_REL_EL_EQN,EL_LUPDATE]>>rw[sv_rel_def] >>
  fs[rich_listTheory.LENGTH_REPLICATE,rich_listTheory.EL_REPLICATE] >>
  TRY(
    simp[Once v_rel_cases] >>
    simp[LIST_REL_EL_EQN] >> NO_TAC) >>
  TRY(fs[Once v_rel_cases]>>NO_TAC)>>
  fs[optionTheory.OPTREL_def] >>
  TRY(
    qmatch_assum_rename_tac`v_rel (Conv t1 v1) (Conv t2 v2)` >>
    rator_x_assum`v_rel`mp_tac >>
    simp[Once v_rel_cases,LIST_REL_EL_EQN] >> NO_TAC) >>
  TRY(
    qmatch_assum_rename_tac`v_rel (Vectorv l1) (Vectorv l2)` >>
    rator_x_assum`v_rel`mp_tac >>
    simp[Once v_rel_cases,LIST_REL_EL_EQN] >> NO_TAC) >>
  TRY (
    CHANGED_TAC(fs[store_v_same_type_def]) >>
    BasicProvers.EVERY_CASE_TAC>>fs[])>>
  TRY (
    qmatch_assum_rename_tac`EL lnum s1 = Varray l1` >>
    last_x_assum(qspec_then`lnum`mp_tac) >>
    simp[Once sv_rel_cases,LIST_REL_EL_EQN] >>
    simp[EL_LUPDATE] >> rw[] >> rw[] >> NO_TAC) >>
  metis_tac[sv_rel_def,optionTheory.NOT_SOME_NONE,optionTheory.SOME_11,PAIR_EQ])

val evaluate_exp_rel = store_thm("evaluate_exp_rel",
  ``(∀ck env1 s1 e1 res1. evaluate ck env1 s1 e1 res1 ⇒
       ∀env2 s2 e2.
         exp_rel (LENGTH env1) (LENGTH env2) (env_rel v_rel env1 env2) e1 e2 ∧
         csg_rel v_rel s1 s2 ⇒
         ∃res2.
           evaluate ck env2 s2 e2 res2 ∧
           csg_rel v_rel (FST res1) (FST res2) ∧
           result_rel v_rel v_rel (SND res1) (SND res2)) ∧
    (∀ck env1 s1 es1 res1. evaluate_list ck env1 s1 es1 res1 ⇒
       ∀env2 s2 es2.
         LIST_REL (exp_rel (LENGTH env1) (LENGTH env2) (env_rel v_rel env1 env2)) es1 es2 ∧
         csg_rel v_rel s1 s2 ⇒
         ∃res2.
           evaluate_list ck env2 s2 es2 res2 ∧
           csg_rel v_rel (FST res1) (FST res2) ∧
           result_rel (LIST_REL v_rel) v_rel (SND res1) (SND res2))``,
  ho_match_mp_tac patSemTheory.evaluate_ind >>
  strip_tac >- (
    rw[Once exp_rel_cases] >>
    rw[Once v_rel_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >>
    rw[] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`v_rel v1 v2` >>
    qmatch_assum_rename_tac`exp_rel _ _ _ e12 e22` >>
    qmatch_assum_abbrev_tac`csg_rel v_rel s3 s4` >>
    first_x_assum(qspecl_then[`v2::env2`,`s4`,`e22`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    discharge_hyps >- ( metis_tac[exp_rel_mono,env_rel_cons] ) >>
    rw[] >> Cases_on`res2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    rw[Once v_rel_cases] >>
    metis_tac[EVERY2_REVERSE]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[EVERY2_REVERSE]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_rel_def] >>
    simp[] >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_rel_def] >>
    PairCases_on`s` >> fs[csg_rel_def] >> rw[] >>
    rfs[EVERY2_EVERY,EVERY_MEM,PULL_EXISTS] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[optionTheory.OPTREL_def] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once v_rel_cases,PULL_EXISTS] >>
    rw[Once evaluate_pat_cases,arithmeticTheory.ADD1] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th) o MATCH_MP EVERY2_REVERSE)) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> fs[] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    first_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(strip_assume_tac o MATCH_MP do_opapp_v_rel o MATCH_MP EVERY2_REVERSE) >>
    rfs[OPTREL_SOME] >>
    qmatch_assum_rename_tac`do_opapp_pat _ = SOME p` >>
    PairCases_on`p`>>fs[GSYM AND_IMP_INTRO] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    fs[csg_rel_def]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[Once exp_rel_cases,PULL_EXISTS] >>
    simp[Once evaluate_pat_cases] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th) o MATCH_MP EVERY2_REVERSE)) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> fs[] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    first_assum(split_pair_match o concl) >> fs[] >>
    fs[csg_rel_def] >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(strip_assume_tac o MATCH_MP do_opapp_v_rel o MATCH_MP EVERY2_REVERSE) >>
    rfs[OPTREL_SOME] >>
    simp[GSYM EXISTS_PROD] ) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[Once exp_rel_cases,PULL_EXISTS] >>
    simp[Once evaluate_pat_cases] >> rw[] >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th) o MATCH_MP EVERY2_REVERSE)) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> fs[] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    first_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(mp_tac o MATCH_MP do_app_v_rel o MATCH_MP EVERY2_REVERSE) >>
    disch_then(qspec_then`s2`(fn th => (first_assum (mp_tac o (MATCH_MP th))))) >>
    disch_then(qspec_then`op`mp_tac) >>
    simp[optionTheory.OPTREL_def] >>
    disch_then(qx_choose_then`p`strip_assume_tac) >> Cases_on`p` >>
    fs[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    simp[Once exp_rel_cases,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(fn th => first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] th) o MATCH_MP EVERY2_REVERSE)) >>
    disch_then(fn th => (first_assum(strip_assume_tac o MATCH_MP th))) >> fs[] >>
    simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    rpt disj2_tac >>
    first_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`do_if v e2 e3 = SOME en` >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >>
    simp[] >> disch_then(qx_choose_then`res2`strip_assume_tac) >>
    Cases_on`∃b. v = (Boolv b)`>>fs[patSemTheory.do_if_def]>>fs[]>>rw[]>>
    last_x_assum(qspecl_then[`env2`,`FST res2`,`if b then e22 else e23`]mp_tac) >>
    discharge_hyps >- (rw[]>>fs[patPropsTheory.Boolv_disjoint]>>rw[]) >>
    disch_then(qx_choose_then`res3`strip_assume_tac) >>
    qexists_tac`res3` >> simp[] >>
    disj1_tac >>
    qexists_tac`(Boolv b)` >> simp[patPropsTheory.Boolv_11] >>
    Cases_on`res2` >> rw[] >> fs[patPropsTheory.Boolv_disjoint] >> rw[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >>
    rw[] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`v_rel v1 v2` >>
    qmatch_assum_rename_tac`exp_rel _ _ _ e12 e22` >>
    qmatch_assum_abbrev_tac`csg_rel v_rel s3 s4` >>
    first_x_assum(qspecl_then[`v2::env2`,`s4`,`e22`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    discharge_hyps >- ( metis_tac[exp_rel_mono,env_rel_cons] ) >>
    rw[] >> Cases_on`res2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`exp_rel _ _ _ e1 e2` >>
    first_x_assum(qspecl_then[`build_rec_env es2 env2 ++ env2`,`s2`,`e2`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      match_mp_tac (MP_CANON (GEN_ALL exp_rel_mono)) >>
      simp[env_rel_def,patSemTheory.build_rec_env_def] >>
      HINT_EXISTS_TAC >> simp[bindn_thm,GSYM bindn_def] >>
      imp_res_tac EVERY2_LENGTH >>
      rw[] >> simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
      fsrw_tac[ARITH_ss][env_rel_def] >>
      simp[Once v_rel_cases]) >>
    simp[] ) >>
  strip_tac >- (
    rpt gen_tac >>
    rw[Once exp_rel_cases] >>
    rw[Once evaluate_pat_cases,PULL_EXISTS] >>
    PairCases_on`s` >>
    PairCases_on`s2`>>fs[csg_rel_def] >>
    match_mp_tac rich_listTheory.EVERY2_APPEND_suff >>
    simp[] >> simp[EVERY2_EVERY,EVERY_MEM] >>
    simp[MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] ) >>
  strip_tac >- ( rw[] >> rw[Once evaluate_pat_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    Cases_on`es2`>>simp[] >>
    simp[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    Cases_on`es2`>>simp[] >>
    simp[Once evaluate_pat_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  Cases_on`es2`>>simp[] >>
  simp[Once evaluate_pat_cases,PULL_EXISTS] >>
  fs[EXISTS_PROD,PULL_EXISTS] >>
  metis_tac[] )

val csg_v_rel_trans =
  decPropsTheory.csg_rel_trans
  |> Q.ISPEC`v_rel`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[v_rel_trans])

val result_rel_v_v_rel_trans =
  result_rel_trans
  |> Q.GENL[`R2`,`R1`]
  |> Q.ISPECL[`v_rel`,`v_rel`]
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[v_rel_trans])

val LIST_REL_v_rel_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`v_rel`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[v_rel_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l3`,`l2`,`l1`]

val LIST_REL_OPTREL_v_rel_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`OPTREL v_rel`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[OPTREL_trans,v_rel_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l3`,`l2`,`l1`]

val exc_rel_v_rel_trans =
  exc_rel_trans
  |> Q.GEN`R`
  |> Q.ISPEC`v_rel`
  |> UNDISCH
  |> prove_hyps_by(metis_tac[v_rel_trans])

val bvs_V_def = Define`
  bvs_V bvs1 bvs2 V ⇔
  ∀x k1 k2.
      find_index (SOME x) bvs1 0 = SOME k1 ∧
      find_index (SOME x) bvs2 0 = SOME k2
      ⇒ V k1 k2`

val bind_bvs_V_NONE = prove(
  ``∀bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (NONE::bvs1) (NONE::bvs2) (bind V)``,
  rw[bvs_V_def,bind_thm] >>
  imp_res_tac find_index_is_MEM >>
  imp_res_tac find_index_MEM >>
  ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
  simp[] >>
  Cases_on`k1=0`>>simp[]>>
  Cases_on`k2=0`>>simp[]>>
  rpt strip_tac >>
  first_x_assum match_mp_tac >>
  fs[find_index_def] >>
  fs[Once find_index_shift_0] >>
  metis_tac[])

val bind_bvs_V_SOME = prove(
  ``∀bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (SOME x::bvs1) (SOME x::bvs2) (bind V)``,
  rw[bvs_V_def,bind_thm] >>
  imp_res_tac find_index_is_MEM >>
  imp_res_tac find_index_MEM >>
  ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
  simp[] >>
  Cases_on`k1=0`>>simp[]>>
  Cases_on`k2=0`>>simp[]>>
  rw[] >> TRY (
    spose_not_then strip_assume_tac >>
    fs[find_index_def] >> NO_TAC) >>
  first_x_assum match_mp_tac >>
  fs[find_index_def] >> fs[] >>
  last_x_assum mp_tac >> rw[] >> fs[] >>
  fs[Once find_index_shift_0] >>
  metis_tac[])

val bind_bvs_V = store_thm("bind_bvs_V",
  ``∀x bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (x::bvs1) (x::bvs2) (bind V)``,
  Cases >> metis_tac[bind_bvs_V_NONE,bind_bvs_V_SOME])

val bindn_bvs_V = store_thm("bindn_bvs_V",
  ``∀ls n bvs1 bvs2 V.
     bvs_V bvs1 bvs2 V ∧ n = LENGTH ls ⇒
     bvs_V (ls++bvs1) (ls++bvs2) (bindn n V)``,
  Induct >> simp[bindn_def,arithmeticTheory.FUNPOW_SUC] >>
  metis_tac[bind_bvs_V,bindn_def])

val exp_rel_Con =
  SIMP_RULE(srw_ss())[](Q.SPECL[`z1`,`z2`,`V`,`Con X Y`]exp_rel_cases)

val exp_rel_sIf = store_thm("exp_rel_sIf",
  ``exp_rel z1 z2 V (If e1 e2 e3) (If f1 f2 f3) ⇒
    exp_rel z1 z2 V (sIf e1 e2 e3) (sIf f1 f2 f3)``,
  rw[sIf_def] >> pop_assum mp_tac >>
  simp[Once exp_rel_cases] >> rw[] >>
  FULL_SIMP_TAC std_ss [GSYM Bool_eqns] >> fs[] >>
  (Cases_on`e1 = (Bool T)`>>rw[Bool_def]>-fs[])>>
  (Cases_on`e1 = (Bool F)`>>rw[Bool_def]>-fs[])>> fs[] >>
  (Cases_on`∃t. e1 = (Con t [])`>>rw[]>-(fs[exp_rel_Con]))>>
  qmatch_abbrev_tac`exp_rel z1 z2 V ea eb` >>
  `ea = If e1 e2 e3` by (
    Cases_on`e1`>>fs[Abbr`ea`]>>
    BasicProvers.CASE_TAC>>rw[] >>
    BasicProvers.CASE_TAC>>rw[] ) >>
  (Cases_on`f1 = Bool T`>>rw[]>-fs[Bool_def])>>
  (Cases_on`f1 = Bool F`>>rw[]>-fs[Bool_def])>>
  `eb = If f1 f2 f3` by (
    Cases_on`f1`>>fs[Abbr`eb`]>>
    BasicProvers.CASE_TAC>>rw[] >>
    TRY(BasicProvers.CASE_TAC>>rw[]) >>
    pop_assum mp_tac >> simp[Once exp_rel_cases]) >>
  simp[Once exp_rel_cases])

val exp_rel_fo = store_thm("exp_rel_fo",
  ``∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
      (fo e1 ⇔ fo e2)``,
  ho_match_mp_tac exp_rel_ind >>
  simp[fo_def] >>
  rw[EVERY_MEM,EVERY2_EVERY,EQ_IMP_THM] >>
  rfs[MEM_ZIP,PULL_EXISTS] >>
  rfs[MEM_EL,PULL_EXISTS] )

val exp_rel_pure = store_thm("exp_rel_pure",
  ``∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
    (pure e1 ⇔ pure e2)``,
  ho_match_mp_tac (theorem"exp_rel_strongind") >>
  simp[pure_def] >>
  rw[EVERY_MEM,EVERY2_EVERY,EQ_IMP_THM] >>
  rfs[MEM_ZIP,PULL_EXISTS] >>
  rfs[MEM_EL,PULL_EXISTS] >>
  fs[] >> imp_res_tac exp_rel_fo >> rw[] >>
  metis_tac[exp_rel_fo])

val exp_rel_imp_ground = store_thm("exp_rel_imp_ground",
  ``∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
      ∀n. (∀k1 k2. k1 ≤ n ⇒ (V k1 k2 ⇔ (k1 = k2))) ∧ ground n e1 ⇒ ground n e2``,
  ho_match_mp_tac exp_rel_ind >>
  simp[] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    simp[bind_thm] >>
    rw[] >> simp[] >> NO_TAC) >>
  TRY (DECIDE_TAC) >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS] >>
  rfs[MEM_EL,PULL_EXISTS] >>
  fs[arithmeticTheory.LESS_OR_EQ] >>
  res_tac >> rw[])

val bindn_0 = store_thm("bindn_0",
  ``∀V. bindn 0 V = V``,
  rw[bindn_def])
val _ = export_rewrites["bindn_0"]

val bind_bindn = store_thm("bind_bindn",
  ``(bind (bindn n V) = bindn (SUC n) V) ∧
    (bindn n (bind V) = bindn (SUC n) V)``,
  conj_tac >- simp[bindn_def,arithmeticTheory.FUNPOW_SUC] >>
  simp[bindn_def,arithmeticTheory.FUNPOW])
val _ = export_rewrites["bind_bindn"]

val exp_rel_unbind = store_thm("exp_rel_unbind",
  ``∀z1 z2 V e1 e2. exp_rel z1 z2 V e1 e2 ⇒
      ∀k n m U.
        V = bindn n U ∧ n ≤ z1 ∧ n ≤ z2 ∧
        ground k e1 ∧ ground k e2 ∧
        k ≤ n-m ∧ m ≤ n
        ⇒
        exp_rel (z1-m) (z2-m) (bindn (n-m) U) e1 e2``,
  ho_match_mp_tac exp_rel_ind >>
  simp[] >> rw[] >>
  simp[Once exp_rel_cases] >> fs[] >>
  rw[] >>
  TRY (
      first_x_assum match_mp_tac >>
      simp[arithmeticTheory.ADD1] >>
      metis_tac[]) >>
  TRY (
    first_x_assum(qspecl_then[`k+1`,`SUC n`,`m`,`U`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    NO_TAC) >>
  TRY (
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    rfs[MEM_EL,PULL_EXISTS] >>
    metis_tac[]) >>
  qpat_assum`bindn n U k1 k2`mp_tac >>
  simp[bindn_thm] >> rw[])

val exp_rel_sLet = store_thm("exp_rel_sLet",
  ``exp_rel z1 z2 V (Let e1 e2) (Let f1 f2) ⇒
    exp_rel z1 z2 V (sLet e1 e2) (sLet f1 f2)``,
  rw[sLet_def] >>
  qpat_assum`exp_rel z1 z2 V X Y`mp_tac >>
  simp[Once exp_rel_cases] >> strip_tac >>
  TRY (
    qpat_assum`exp_rel Z1 Z2 VV (Var_local A) B`mp_tac >>
    simp[Once exp_rel_cases] >> rw[bind_thm] ) >>
  TRY (
    qpat_assum`exp_rel Z1 Z2 VV B (Var_local A)`mp_tac >>
    simp[Once exp_rel_cases] >> rw[bind_thm] ) >>
  imp_res_tac exp_rel_pure >> fs[] >>
  TRY (
    imp_res_tac exp_rel_sym >>
    imp_res_tac exp_rel_imp_ground >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- (
      simp[bind_thm,relationTheory.inv_DEF] ) >>
    rw[] >> NO_TAC) >>
  simp[Once(SIMP_RULE(srw_ss())[](Q.SPECL[`z1`,`z2`,`V`,`Seq e1 e2`]exp_rel_cases))] >>
  qspecl_then[`z1+1`,`z2+1`,`bind V`,`e2`,`f2`]mp_tac exp_rel_unbind >> simp[] >>
  disch_then(qspecl_then[`0`,`1`,`1`,`V`]mp_tac) >>
  simp[bindn_def] )

val ground_sIf = store_thm("ground_sIf",
  ``ground n (If e1 e2 e3) ⇒
    ground n (sIf e1 e2 e3)``,
  rw[sIf_def] >>
  Cases_on`e1`>> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[] )

val ground_inc = store_thm("ground_inc",
  ``(∀e n. ground n e ⇒ ∀m. n ≤ m ⇒ ground m e) ∧
    (∀es n. ground_list n es ⇒ ∀m. n ≤ m ⇒ ground_list m es)``,
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  simp[] >> rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[arithmeticTheory.LE_ADD_RCANCEL])

val ground_sLet = store_thm("ground_sLet",
  ``ground n (Let e1 e2) ⇒
    ground n (sLet e1 e2)``,
  rw[sLet_def] >>
  match_mp_tac(MP_CANON(CONJUNCT1 ground_inc))>>
  qexists_tac`0`>>simp[])

val ground_Let_Els = store_thm("ground_Let_Els",
  ``∀k m n e.
    ground (n+k) e ∧ m < n ⇒
    ground n (Let_Els m k e)``,
  Induct >> simp[Let_Els_def] >>
  rw[] >>
  match_mp_tac ground_sLet >>
  simp[] >>
  first_x_assum match_mp_tac >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1])

val compile_pat_ground = store_thm("compile_pat_ground",
  ``(∀p. ground 1 (compile_pat p)) ∧
    (∀n ps. ground (n + LENGTH ps) (compile_pats n ps))``,
  ho_match_mp_tac compile_pat_ind >>
  simp[compile_pat_def] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac ground_sIf >>
    simp[] >>
    match_mp_tac ground_Let_Els >>
    simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 ground_inc)) >>
    HINT_EXISTS_TAC >> simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac ground_sLet >> simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 ground_inc)) >>
    qexists_tac`1`>>simp[] ) >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac ground_sIf >> simp[] >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  match_mp_tac ground_sLet >> simp[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 ground_inc)) >>
  HINT_EXISTS_TAC >> simp[])

val ground_exp_rel_refl = store_thm("ground_exp_rel_refl",
  ``(∀e n. ground n e ⇒
       ∀z1 z2 V. n ≤ z1 ∧ n ≤ z2 ⇒ exp_rel z1 z2 (bindn n V) e e) ∧
    (∀es n. ground_list n es ⇒
       ∀z1 z2 V. n ≤ z1 ∧ n ≤ z2 ⇒ EVERY2 (exp_rel z1 z2 (bindn n V)) es es)``,
  ho_match_mp_tac(TypeBase.induction_of(``:patLang$exp``)) >>
  simp[] >> rw[] >>
  simp[Once exp_rel_cases] >> TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[arithmeticTheory.ADD1] >>
    NO_TAC) >>
  simp[bindn_thm])

val compile_row_acc = store_thm("compile_row_acc",
  ``(∀Nbvs p bvs1 N. Nbvs = N::bvs1 ⇒
       ∀bvs2 r1 n1 f1 r2 n2 f2.
         compile_row (N::bvs1) p = (r1,n1,f1) ∧
         compile_row (N::bvs2) p = (r2,n2,f2) ⇒
         n1 = n2 ∧ f1 = f2 ∧
         ∃ls. r1 = ls ++ bvs1 ∧
              r2 = ls ++ bvs2 ∧
              LENGTH ls = SUC n1) ∧
    (∀bvsk0 n k ps bvsk N bvs1.
        bvsk0 = bvsk ++ (N::bvs1) ∧ LENGTH bvsk = n ⇒
      ∀bvs2 r1 n1 f1 r2 n2 f2.
        compile_cols (bvsk++(N::bvs1)) n k ps = (r1,n1,f1) ∧
        compile_cols (bvsk++(N::bvs2)) n k ps = (r2,n2,f2) ⇒
        n1 = n2 ∧ f1 = f2 ∧
        ∃ls. r1 = ls ++ bvsk ++ (N::bvs1) ∧
             r2 = ls ++ bvsk ++ (N::bvs2) ∧
             LENGTH ls = n1)``,
  ho_match_mp_tac compile_row_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rw[compile_row_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rw[compile_row_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> simp[LENGTH_NIL] >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp_tac std_ss [compile_row_def] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspec_then`bvs2`mp_tac) >>
    simp[] >> strip_tac >>
    qexists_tac`ls++[N]` >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp_tac std_ss [compile_row_def] >>
    simp[] >>
    `∃r1 n1 f1. compile_row (NONE::N::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    fs[] >> rpt gen_tac >>
    `∃r2 n2 f2. compile_row (NONE::N::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    fs[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum(qspec_then`N::bvs2`mp_tac) >>
    simp[] >> rw[] >> simp[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[compile_row_def] ) >>
  strip_tac >- simp[compile_row_def] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >>
  simp_tac std_ss [compile_row_def] >>
  `∃r01 n01 f01. compile_row (NONE::(bvsk ++ (N::bvs1))) p = (r01,n01,f01)` by simp[GSYM EXISTS_PROD] >>
  `∃r02 n02 f02. compile_row (NONE::(bvsk ++ (N::bvs2))) p = (r02,n02,f02)` by simp[GSYM EXISTS_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >>
  `∃r11 n11 f11. compile_cols r01 (LENGTH bvsk + 1 + n01) (k+1) ps = (r11,n11,f11)` by simp[GSYM EXISTS_PROD] >>
  `∃r12 n12 f12. compile_cols r02 (LENGTH bvsk + 1 + n02) (k+1) ps = (r12,n12,f12)` by simp[GSYM EXISTS_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >>
  ntac 5 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_assum`∀X. Y`mp_tac >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss) [] >>
  ntac 2 strip_tac >>
  disch_then(qspec_then`bvsk ++ N::bvs2`mp_tac) >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss) [] >>
  ntac 3 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qpat_assum`∀X. Y`mp_tac >>
  ntac 3 (pop_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss) [] >>
  ntac 3 strip_tac >>
  disch_then(qspec_then`ls ++ bvsk`mp_tac) >>
  pop_assum mp_tac >>
  simp_tac (std_ss++listSimps.LIST_ss++ARITH_ss) [arithmeticTheory.ADD1] >>
  strip_tac >>
  disch_then(qspec_then`bvs2`mp_tac) >>
  ntac 2 (last_x_assum mp_tac) >>
  simp_tac (std_ss++listSimps.LIST_ss++ARITH_ss) [arithmeticTheory.ADD1] >>
  ntac 3 strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[])

val compile_row_shift = store_thm("compile_row_shift",
  ``(∀bvs p bvs1 n1 f z1 z2 V e1 e2.
       compile_row bvs p = (bvs1,n1,f) ∧ 0 < z1 ∧ 0 < z2 ∧ V 0 0 ∧ bvs ≠ [] ∧
       exp_rel (z1 + n1) (z2 + n1) (bindn n1 V) e1 e2
       ⇒
       exp_rel z1 z2 V (f e1) (f e2)) ∧
    (∀bvs n k ps bvs1 n1 f z1 z2 V e1 e2.
       compile_cols bvs n k ps = (bvs1,n1,f) ∧ bvs ≠ [] ∧ ps ≠ [] ∧
       n < z1 ∧ n < z2 ∧ V n n ∧
       exp_rel (z1 + n1) (z2 + n1) (bindn (n1) V) e1 e2
       ⇒
       exp_rel z1 z2 V (f e1) (f e2))``,
  ho_match_mp_tac compile_row_ind >>
  simp[compile_row_def] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    `∃bvs1 n1 f. compile_cols bvs 0 0 ps = (bvs1,n1,f)` by simp[GSYM EXISTS_PROD] >>
    Cases_on`ps`>>fs[compile_row_def] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    `∃bvs1 n f. compile_row (NONE::bvs) p = (bvs1,n,f)` by simp[GSYM EXISTS_PROD] >>
    fs[] >>
    rpt gen_tac >> strip_tac >>
    match_mp_tac exp_rel_sLet >>
    simp[Once exp_rel_cases] >>
    simp[Once exp_rel_cases] >>
    simp[Once exp_rel_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    simp[bind_thm] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `∃bvs0 n0 f0. compile_row (NONE::bvs) p = (bvs0,n0,f0)` by simp[GSYM EXISTS_PROD] >>
  fs[] >>
  `∃bvs2 n2 f2. compile_cols bvs0 (n0+n+1) (k+1) ps = (bvs2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
  fsrw_tac[ARITH_ss][] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >>
  match_mp_tac exp_rel_sLet >>
  simp[Once exp_rel_cases] >>
  simp[Once exp_rel_cases] >>
  simp[Once exp_rel_cases] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[bind_thm] >>
  Cases_on`ps=[]`>>fs[compile_row_def] >- (
    rw[] >> fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] ) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  qspecl_then[`NONE::bvs`,`p`]mp_tac(CONJUNCT1 compile_row_acc) >>
  simp[] >> disch_then(qspec_then`bvs`mp_tac) >> simp[] >>
  strip_tac >> Cases_on`bvs0`>>fs[] >>
  conj_tac >- simp[bindn_thm,arithmeticTheory.ADD1] >>
  fs[bindn_def,GSYM arithmeticTheory.FUNPOW_ADD,arithmeticTheory.ADD1] >>
  fsrw_tac[ARITH_ss][])

val compile_exp_shift = store_thm("compile_exp_shift",
  ``(∀bvs1 e z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = LENGTH bvs1) ∧ (z2 = LENGTH bvs2) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       exp_rel z1 z2 V (compile_exp bvs1 e) (compile_exp bvs2 e)) ∧
    (∀bvs1 es z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = LENGTH bvs1) ∧ (z2 = LENGTH bvs2) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       LIST_REL (exp_rel z1 z2 V) (compile_exps bvs1 es) (compile_exps bvs2 es)) ∧
    (∀bvs1 funs z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = SUC(LENGTH bvs1)) ∧
       (z2 = SUC(LENGTH bvs2)) ∧
       (bvs_V bvs1 bvs2 V)
       ⇒
       LIST_REL (exp_rel z1 z2 (bind V))
         (compile_funs bvs1 funs) (compile_funs bvs2 funs)) ∧
    (∀Nbvs1 pes bvs1 z1 z2 bvs2 V.
       (Nbvs1 = NONE::bvs1) ∧
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = SUC(LENGTH bvs1)) ∧ (z2 = SUC(LENGTH bvs2)) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       exp_rel z1 z2 (bind V) (compile_pes (NONE::bvs1) pes) (compile_pes (NONE::bvs2) pes))``,
  ho_match_mp_tac compile_exp_ind >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    metis_tac[bind_bvs_V] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once exp_rel_cases] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >>
    BasicProvers.CASE_TAC >- (
      fs[GSYM find_index_NOT_MEM] >>
      `¬MEM (SOME x) bvs2` by (
        fs[Once pred_setTheory.EXTENSION,MEM_FILTER] >>
        spose_not_then strip_assume_tac >>
        res_tac >> fs[] ) >>
      imp_res_tac find_index_NOT_MEM >>
      ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
      simp[] >>
      simp[Once exp_rel_cases] ) >>
    imp_res_tac find_index_is_MEM >>
    fs[Once pred_setTheory.EXTENSION,MEM_FILTER] >>
    res_tac >> fs[] >>
    imp_res_tac find_index_MEM >>
    ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
    rw[] >> simp[] >>
    simp[Once exp_rel_cases] >>
    fs[bvs_V_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`(SOME x)::bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    fs[bvs_V_def] >>
    simp[find_index_def] >>
    rw[] >> rw[bind_def] >>
    imp_res_tac find_index_LESS_LENGTH >>
    Cases_on`k1`>>Cases_on`k2`>>fs[]>>
    simp[bind_def] >>
    fs[Once find_index_shift_0] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_rel_sLet >>
    simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    metis_tac[bind_bvs_V] ) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_rel_sLet >>
    simp[Once exp_rel_cases] >>
    first_x_assum (qspecl_then[`SOME x::bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    match_mp_tac bind_bvs_V >> rw[] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once exp_rel_cases] >>
    fs[compile_funs_map] >>
    reverse conj_tac >- (
      qmatch_abbrev_tac`exp_rel z1 z2 V1 (compile_exp bvs10 e) (compile_exp bvs20 e)` >>
      last_x_assum (qspecl_then[`bvs20`,`V1`]mp_tac) >>
      unabbrev_all_tac >> simp[] >>
      disch_then match_mp_tac >>
      conj_tac >- (
        fs[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
        metis_tac[] ) >>
      match_mp_tac bindn_bvs_V >>
      simp[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(bvs20 = MAP f funs ++ bvs2)` >>
    qmatch_assum_abbrev_tac`Abbrev(bvs10 = MAP f funs ++ bvs1)` >>
    first_x_assum(qspecl_then[`bvs20`,`bindn (LENGTH funs) V`]mp_tac) >>
    unabbrev_all_tac >> simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    conj_tac >- (
      fs[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    match_mp_tac bindn_bvs_V >>
    simp[] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_rel_cases] ) >>
  strip_tac >- (
    rw[] >>
    last_x_assum(qspecl_then[`SOME x::bvs2`,`bind V`]mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    match_mp_tac bind_bvs_V >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_acc) >> simp[] >>
    disch_then(qspec_then`bvs2`mp_tac) >>
    `∃r1 n1 f1. compile_row (NONE::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    `∃r2 n2 f2. compile_row (NONE::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    simp[] >> strip_tac >> fs[] >>
    first_x_assum(qspecl_then[`ls++bvs2`,`bindn (LENGTH ls) V`]mp_tac) >>
    simp[rich_listTheory.FILTER_APPEND,bindn_bvs_V] >>
    rpt BasicProvers.VAR_EQ_TAC >> strip_tac >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_shift) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[bind_thm] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_rel_sIf >>
    simp[Once exp_rel_cases] >>
    conj_tac >- (
      qspecl_then[`compile_pat p`,`1`]mp_tac(CONJUNCT1 ground_exp_rel_refl) >>
      simp[compile_pat_ground,bindn_def] ) >>
    `∃r1 n1 f1. compile_row (NONE::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    `∃r2 n2 f2. compile_row (NONE::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_acc) >> simp[] >>
    disch_then(qspec_then`bvs2`mp_tac) >>
    simp[] >> strip_tac >> fs[] >>
    last_x_assum(qspecl_then[`ls++bvs2`,`bindn (LENGTH ls) V`]mp_tac) >>
    simp[rich_listTheory.FILTER_APPEND,bindn_bvs_V] >>
    rpt BasicProvers.VAR_EQ_TAC >> strip_tac >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 compile_row_shift) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[bind_thm] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]) >>
   rw[])

val use_assum_tac =
  first_assum(split_pair_match o concl) >> fs[] >>
  first_assum(match_exists_tac o concl) >> simp[]

val csg_rel_unpair = store_thm("csg_rel_unpair",
  ``csg_rel R x1 x2 ⇔
    (FST (FST x1) = FST (FST x2)) ∧
    LIST_REL (sv_rel R) (FST(SND(FST x1))) (FST(SND(FST x2))) ∧
    SND(SND(FST x1)) = SND(SND(FST x2)) ∧
    LIST_REL (OPTREL R) (SND x1) (SND x2)``,
  PairCases_on`x1`>>PairCases_on`x2`>>simp[csg_rel_def])

val lookup_find_index_SOME = prove(
  ``∀env. ALOOKUP env n = SOME v ⇒
      ∀m. ∃i. (find_index (SOME n) (MAP (SOME o FST) env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))``,
  Induct >> simp[] >> Cases >> rw[find_index_def] >-
    (qexists_tac`0`>>simp[]) >> fs[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>rw[]>>rw[]>>
  qexists_tac`SUC i`>>simp[]);

val compile_v_Boolv = EVAL``compile_v (Boolv b) = Boolv b`` |> EQT_ELIM

val compile_exp_correct = store_thm("compile_exp_correct",
  ``(∀ck env s exp res. evaluate ck env s exp res ⇒
     (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
     ∃res4.
       evaluate ck
         (MAP (compile_v o SND) env)
         (map_csg compile_v s)
         (compile_exp (MAP (SOME o FST) env) exp) res4 ∧
       csg_rel v_rel (map_csg compile_v (FST res)) (FST res4) ∧
       result_rel v_rel v_rel (map_result compile_v compile_v (SND res)) (SND res4)) ∧
    (∀ck env s exps ress. evaluate_list ck env s exps ress ⇒
     (SND ress ≠ Rerr (Rabort Rtype_error)) ⇒
     ∃ress4.
       evaluate_list ck
         (MAP (compile_v o SND) env)
         (map_csg compile_v s)
         (compile_exps (MAP (SOME o FST) env) exps) ress4 ∧
       csg_rel v_rel (map_csg compile_v (FST ress)) (FST ress4) ∧
       result_rel (LIST_REL v_rel) v_rel (map_result compile_vs compile_v (SND ress)) (SND ress4)) ∧
    (∀ck env s v pes res. evaluate_match ck env s v pes res ⇒
     (SND res ≠ Rerr (Rabort Rtype_error)) ⇒
     ∃res4.
       evaluate ck
         (compile_v v::(MAP (compile_v o SND) env))
         (map_csg compile_v s)
         (compile_pes (NONE::(MAP (SOME o FST) env)) pes) res4 ∧
       csg_rel v_rel (map_csg compile_v (FST res)) (FST res4) ∧
       result_rel v_rel v_rel (map_result compile_v compile_v (SND res)) (SND res4))``,
  ho_match_mp_tac exhSemTheory.evaluate_strongind >>
  strip_tac >- rw[Once evaluate_pat_cases] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    use_assum_tac) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >> fs[] >>
    use_assum_tac) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    use_assum_tac) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >> fs[] >> rw[] >>
    qmatch_assum_rename_tac`result_rel _ _ _ (SND res5)` >>
    qmatch_assum_abbrev_tac`evaluate ck (v5::env5) s5 e5 res5` >>
    qmatch_assum_abbrev_tac`v_rel v5 v6` >>
    qspecl_then[`ck`,`v5::env5`,`s5`,`e5`,`res5`]mp_tac(CONJUNCT1 evaluate_exp_rel) >>
    simp[] >> disch_then(qspecl_then[`v6::env5`,`FST res4`,`e5`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      match_mp_tac (CONJUNCT1 exp_rel_refl) >>
      Cases >> simp[env_rel_def] ) >>
    disch_then(qx_choose_then`res6`strip_assume_tac) >>
    qexists_tac`res6` >>
    reverse conj_tac >- metis_tac[csg_v_rel_trans,result_rel_v_v_rel_trans] >>
    Cases_on`res4`>>fs[] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >> fs[] >>
    use_assum_tac) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][Once v_rel_cases] >>
    fs[compile_exps_reverse] >>
    use_assum_tac >>
    simp[rich_listTheory.MAP_REVERSE,EVERY2_REVERSE]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    fs[EXISTS_PROD,compile_exps_reverse] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    imp_res_tac lookup_find_index_SOME >>
    first_x_assum(qspec_then`0`mp_tac) >>
    rw[] >> rw[] >>
    simp[Once evaluate_pat_cases] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[] >> simp[EL_MAP] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    simp[map_csg_def,EL_MAP] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_pat_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> simp[] >>
    strip_tac >> strip_tac >>
    simp[Once evaluate_pat_cases] >>
    fs[] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    fs[compile_exps_reverse] >>
    use_assum_tac >>
    imp_res_tac do_opapp >>
    first_assum(strip_assume_tac o MATCH_MP do_opapp_v_rel o MATCH_MP EVERY2_REVERSE) >>
    rfs[compile_vs_map,OPTREL_SOME,rich_listTheory.MAP_REVERSE] >>
    first_assum(split_applied_pair_tac o concl) >> fs[] >>
    fs[map_csg_def,csg_rel_def] >>
    rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP(CONJUNCT1 evaluate_exp_rel)) >>
    disch_then(exists_suff_then mp_tac) >>
    discharge_hyps >- ( simp[exp_rel_refl,env_rel_def,csg_rel_def] ) >>
    strip_tac >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    metis_tac[csg_v_rel_trans,result_rel_v_v_rel_trans] ) >>
  strip_tac >- (
    rpt gen_tac >> simp[] >>
    strip_tac >>
    simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    imp_res_tac csg_rel_count >>
    fs[map_csg_count] >>
    fs[compile_exps_reverse] >>
    use_assum_tac >>
    imp_res_tac do_opapp >>
    first_assum(strip_assume_tac o MATCH_MP do_opapp_v_rel o MATCH_MP EVERY2_REVERSE) >>
    rfs[OPTREL_SOME,GSYM EXISTS_PROD,rich_listTheory.MAP_REVERSE] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    asm_simp_tac(srw_ss()++DNF_ss)[Once evaluate_pat_cases] >>
    disj1_tac >>
    fs[compile_exps_reverse] >>
    use_assum_tac >>
    imp_res_tac do_app >>
    first_assum(strip_assume_tac o MATCH_MP do_app_v_rel o MATCH_MP EVERY2_REVERSE) >>
    res_tac >>
    first_x_assum(qspec_then`Op op`mp_tac)  >>
    pop_assum kall_tac >>
    fs[compile_vs_map,rich_listTheory.MAP_REVERSE] >>
    fs[OPTREL_SOME,map_csg_def] >>
    strip_tac >>
    first_assum(split_applied_pair_tac o concl) >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    asm_simp_tac(srw_ss()++DNF_ss)[Once evaluate_pat_cases] >>
    rpt disj2_tac >>
    fs[compile_exps_reverse] >>
    use_assum_tac ) >>
  strip_tac >- (
    rw[] >>
    qho_match_abbrev_tac`∃res4. evaluate ck env4 s4 (sLet a1 a2) res4 ∧ P res4` >>
    qsuff_tac`∃res4. evaluate ck env4 s4 (Let a1 a2) res4 ∧ P res4 ∧ SND res4 ≠ Rerr (Rabort Rtype_error)`
      >-metis_tac[sLet_correct] >>
    simp[Once evaluate_pat_cases,Abbr`P`] >> fs[] >>
    qmatch_assum_abbrev_tac`evaluate ck (v4::env4) s5 a2 res5` >>
    qspecl_then[`ck`,`v4::env4`,`s5`,`a2`,`res5`]mp_tac(CONJUNCT1 evaluate_exp_rel) >>
    qmatch_assum_rename_tac`v_rel v4 v5` >>
    simp[] >> disch_then(qspecl_then[`v5::env4`,`FST res4`,`a2`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      match_mp_tac (CONJUNCT1 exp_rel_refl) >>
      Cases >> simp[env_rel_def] ) >>
    disch_then(qx_choose_then`res6`strip_assume_tac) >>
    qexists_tac`res6` >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disj1_tac >>
    map_every qexists_tac[`v5`,`FST res4`] >>
    Cases_on`res4`>>fs[]>>
    conj_asm1_tac >- metis_tac[csg_v_rel_trans,result_rel_v_v_rel_trans] >>
    spose_not_then strip_assume_tac >> fs[]) >>
  strip_tac >- (
    rw[] >> fs[] >>
    exists_match_mp_then exists_suff_tac sLet_correct >>
    simp[Once evaluate_pat_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[] >>
    Cases_on`err`>>fs[]) >>
  strip_tac >- (
    Cases_on`n`>> rw[] >- (
      fs[libTheory.opt_bind_def] >>
      simp[Once evaluate_pat_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      last_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      first_x_assum (mp_tac o MATCH_MP (CONJUNCT1 evaluate_exp_rel)) >>
      disch_then (exists_match_mp_then mp_tac) >>
      discharge_hyps >- simp[exp_rel_refl,env_rel_def] >> strip_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      metis_tac[csg_v_rel_trans,result_rel_v_v_rel_trans] ) >>
    fs[libTheory.opt_bind_def] >>
    exists_match_mp_then exists_suff_tac sLet_correct >>
    simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    last_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum (mp_tac o MATCH_MP (CONJUNCT1 evaluate_exp_rel)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      match_mp_tac (CONJUNCT1 exp_rel_refl) >>
      Cases >> simp[env_rel_def] ) >>
    strip_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    reverse conj_tac >- (
      metis_tac[csg_v_rel_trans,result_rel_v_v_rel_trans] ) >>
    spose_not_then strip_assume_tac >>
    fs[] >> fs[]) >>
  strip_tac >- (
    Cases_on`n`>>rw[]>>fs[] >- (
      simp[Once evaluate_pat_cases] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] ) >>
    exists_match_mp_then exists_suff_tac sLet_correct >>
    simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once evaluate_pat_cases] >>
    fs[] >>
    simp[markerTheory.Abbrev_def] >>
    qho_match_abbrev_tac`∃e. evaluate a b c d e ∧ P e` >>
    qmatch_assum_abbrev_tac`evaluate a b' c d' e` >>
    `b = b'` by (
      unabbrev_all_tac >>
      fs[patSemTheory.build_rec_env_def,exhPropsTheory.build_rec_env_merge,compile_funs_map] >>
      rw[LIST_EQ_REWRITE,EL_MAP,UNCURRY,compile_funs_map] >>
      imp_res_tac find_index_ALL_DISTINCT_EL >>
      first_x_assum(qspec_then`x`mp_tac) >>
      discharge_hyps >- simp[] >>
      disch_then(qspec_then`0`mp_tac) >>
      asm_simp_tac(std_ss)[EL_MAP] >>
      simp[libTheory.the_def]) >>
    `d = d'` by (
      unabbrev_all_tac >>
      simp[exhPropsTheory.build_rec_env_merge] >>
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[FUN_EQ_THM,FORALL_PROD] ) >>
    unabbrev_all_tac >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  strip_tac >- (
    rw[] >>
    simp[Once evaluate_pat_cases] >>
    simp[map_csg_def,MAP_GENLIST,combinTheory.o_DEF] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_pat_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    last_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT2 evaluate_exp_rel)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- simp[exp_rel_refl,env_rel_def] >> strip_tac >>
    first_assum(split_pair_match o concl) >> rfs[] >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    metis_tac[csg_v_rel_trans,LIST_REL_v_rel_trans]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >>
    last_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT2 evaluate_exp_rel)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- simp[exp_rel_refl,env_rel_def] >> strip_tac >>
    first_assum(split_pair_match o concl) >> rfs[] >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    metis_tac[csg_v_rel_trans,exc_rel_v_rel_trans]) >>
  strip_tac >- (
    rw[] >>
    Cases_on`pes`>>simp[]>>fs[]
    >|[ALL_TAC,
      exists_match_mp_then exists_suff_tac sIf_correct >>
      simp[Once evaluate_pat_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`Boolv T` >>
      simp[patSemTheory.do_if_def] >>
      qspecl_then[`p`,`v`,`s,t`,`env`]mp_tac (CONJUNCT1 compile_pat_correct) >>
      simp[] >> strip_tac >>
      Q.PAT_ABBREV_TAC`s2 = X:patSem$v count_store_genv` >>
      CONV_TAC SWAP_EXISTS_CONV  >>
      qexists_tac`s2` >> simp[Abbr`s2`] >>
      pop_assum kall_tac
    ]
    >>> USE_SG_THEN (fn th => metis_tac[th]) 2 1 >>
    `∃bvs n f. compile_row (NONE::MAP (SOME o FST) env) p = (bvs,n,f)` by (
      simp[GSYM EXISTS_PROD] ) >> simp[] >>
    fs[Once(CONJUNCT1 exhPropsTheory.pmatch_nil)] >>
    Cases_on`pmatch s p v []`>>fs[]>>
    qmatch_assum_rename_tac`menv ++ env = envX` >> BasicProvers.VAR_EQ_TAC >>
    qho_match_abbrev_tac`∃res4. evaluate ck (v4::env4) s4 (f (compile_exp bvs exp)) res4 ∧ P res4` >>
    fs[] >>
    qmatch_assum_abbrev_tac`compile_row (NONE::bvs0) p = X` >>
    (compile_row_correct
     |> CONJUNCT1
     |> SIMP_RULE (srw_ss())[]
     |> Q.SPECL[`p`,`bvs0`,`s,t`,`v`]
     |> mp_tac) >>
    simp[Abbr`X`] >> strip_tac >>
    qmatch_assum_abbrev_tac`evaluate ck env3 s4 exp3 res4` >>
    qspecl_then[`ck`,`env3`,`s4`,`exp3`,`res4`]mp_tac (CONJUNCT1 evaluate_exp_rel) >>
    simp[] >>
    disch_then(qspecl_then[`menv4 ++ env4`,`s4`,`compile_exp bvs exp`]mp_tac) >>
    (discharge_hyps >- (
       simp[Abbr`env3`,Abbr`env4`,Abbr`exp3`] >>
       match_mp_tac(CONJUNCT1 compile_exp_shift) >>
       simp[Abbr`bvs0`] >> conj_tac >- (
         qpat_assum`X = MAP Y menv`mp_tac >>
         disch_then(mp_tac o Q.AP_TERM`set`) >>
         simp[pred_setTheory.EXTENSION,MEM_FILTER,MEM_ZIP,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
         simp[MEM_EL,PULL_EXISTS,FORALL_PROD] >>metis_tac[] ) >>
       simp[bvs_V_def,env_rel_def] >>
       rpt gen_tac >> strip_tac >>
       imp_res_tac find_index_LESS_LENGTH >> fs[] >> rfs[] >> simp[] >>
       fs[find_index_APPEND] >>
       qpat_assum`X = SOME k2`mp_tac >>
       BasicProvers.CASE_TAC >- (
         qpat_assum`X = SOME k1`mp_tac >>
         BasicProvers.CASE_TAC >- (
           simp[Once find_index_shift_0] >> strip_tac >>
           simp[Once find_index_shift_0] >> strip_tac >>
           rw[] >>
           simp[rich_listTheory.EL_APPEND2] ) >>
         fs[GSYM find_index_NOT_MEM] >>
         imp_res_tac find_index_is_MEM >>
         qpat_assum`X = MAP Y Z`(mp_tac o Q.AP_TERM`set`) >>
         fs[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,UNCURRY] >>
         simp[EQ_IMP_THM,FORALL_AND_THM] >> strip_tac >>
         fs[PULL_EXISTS] >>
         first_x_assum(qspec_then`y`mp_tac) >>
         rfs[MEM_ZIP,PULL_EXISTS] >>
         rfs[MEM_EL,PULL_EXISTS] >>
         metis_tac[] ) >>
       qpat_assum`X = SOME k1`mp_tac >>
       BasicProvers.CASE_TAC >- (
         fs[GSYM find_index_NOT_MEM] >>
         imp_res_tac find_index_is_MEM >>
         qpat_assum`X = MAP Y Z`(mp_tac o Q.AP_TERM`set`) >>
         fs[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,UNCURRY] >>
         simp[EQ_IMP_THM,FORALL_AND_THM] >> strip_tac >>
         fs[PULL_EXISTS] >>
         rfs[MEM_ZIP,PULL_EXISTS] >>
         rfs[MEM_EL,PULL_EXISTS] >>
         qmatch_assum_rename_tac`z < SUC n` >>
         last_x_assum(qspec_then`z`mp_tac) >>
         qpat_assum`SOME x = Y`(assume_tac o SYM) >>
         simp[] >> rw[] >>
         metis_tac[] ) >>
       rw[] >>
       imp_res_tac find_index_LESS_LENGTH >>
       fs[] >> simp[rich_listTheory.EL_APPEND1,EL_MAP] >>
       qmatch_assum_rename_tac`k2 < LENGTH l2` >>
       Q.ISPEC_THEN`l2`mp_tac(CONV_RULE SWAP_FORALL_CONV (INST_TYPE[beta|->``:patSem$v``]find_index_in_FILTER_ZIP_EQ)) >>
       disch_then(qspec_then`IS_SOME`mp_tac) >>
       disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(op@ o (partition(equal"v1" o fst o dest_var))))) >>
       disch_then(qspec_then`menv4`mp_tac) >>
       simp[] >>
       disch_then(qspecl_then[`SOME x`,`0`,`0`]mp_tac) >>
       simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
       fs[combinTheory.o_DEF,UNCURRY] >>
       simp[EL_ZIP,EL_MAP,UNCURRY])) >>
    disch_then(qx_choose_then`res5`strip_assume_tac) >>
    fs[Abbr`s4`,map_csg_def] >>
    qexists_tac`res5` >> simp[Abbr`P`] >>
    (reverse conj_asm2_tac >- (
      TRY(conj_tac >- (
        spose_not_then strip_assume_tac >>
        PairCases_on`res4`>>PairCases_on`res5`>>
        fs[csg_rel_def])) >>
      metis_tac[csg_v_rel_trans,result_rel_v_v_rel_trans] )) >>
    first_x_assum match_mp_tac >> rfs[]) >>
  strip_tac >- (
    rw[] >>
    Cases_on`pes`>>fs[]>-(
      fs[Once exhSemTheory.evaluate_cases] >>
      rw[] >> fs[] ) >>
    exists_match_mp_then exists_suff_tac sIf_correct >>
    simp[Once evaluate_pat_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`(Boolv F)` >>
    simp[patSemTheory.do_if_def] >>
    qspecl_then[`p`,`v`,`s,t`,`env`]mp_tac (CONJUNCT1 compile_pat_correct) >>
    simp[] >> strip_tac >>
    Q.PAT_ABBREV_TAC`s2 = X:patSem$v count_store_genv` >>
    CONV_TAC SWAP_EXISTS_CONV  >>
    qexists_tac`s2` >> simp[Abbr`s2`] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[] ))

val _ = export_theory()
