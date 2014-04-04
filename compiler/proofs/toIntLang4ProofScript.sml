open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory alistTheory pairTheory
open Defn miscLib miscTheory intLang2Theory intLang3Theory intLang4Theory compilerTerminationTheory
val _ = new_theory"toIntLang4Proof"

val v_to_i4_def = tDefine"v_to_i4"`
  (v_to_i4 (Litv_i2 l) = Litv_i4 l) ∧
  (v_to_i4 (Conv_i2 tag vs) = Conv_i4 tag (vs_to_i4 vs)) ∧
  (v_to_i4 (Closure_i2 env x e) =
    Closure_i4
      (MAP v_to_i4 (MAP SND env))
      (exp_to_i4 (SOME x :: MAP (SOME o FST) env) e)) ∧
  (v_to_i4 (Recclosure_i2 env funs f) =
    Recclosure_i4
      (MAP v_to_i4 (MAP SND env))
      (funs_to_i4 (MAP (SOME o FST) funs ++ MAP (SOME o FST) env) funs)
      (the (LENGTH funs) (find_index f (MAP FST funs) 0))) ∧
  (v_to_i4 (Loc_i2 n) = Loc_i4 n) ∧
  (vs_to_i4 [] = []) ∧
  (vs_to_i4 (v::vs) = v_to_i4 v :: vs_to_i4 vs)`
(WF_REL_TAC`inv_image $< (\x. case x of INL v => v_i2_size v
                                      | INR vs => v_i23_size vs)` >>
 simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[] >>
 Cases >> simp[v_i2_size_def] >> rw[] >> res_tac >> simp[])
val v_to_i4_def = save_thm("v_to_i4_def",
  v_to_i4_def |> SIMP_RULE (srw_ss()++ETA_ss) [MAP_MAP_o])
val _ = export_rewrites["v_to_i4_def"]

val good_v_i2_def = tDefine"good_v_i2"`
  (good_v_i2 (Litv_i2 _) ⇔ T) ∧
  (good_v_i2 (Conv_i2 _ vs) ⇔ good_vs_i2 vs) ∧
  (good_v_i2 (Closure_i2 env _ _) ⇔ good_vs_i2 (MAP SND env)) ∧
  (good_v_i2 (Recclosure_i2 env funs f) ⇔
   good_vs_i2 (MAP SND env) ∧
   ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v_i2 (Loc_i2 _) ⇔ T) ∧
  (good_vs_i2 [] ⇔ T) ∧
  (good_vs_i2 (v::vs) ⇔ good_v_i2 v ∧ good_vs_i2 vs)`
(WF_REL_TAC`inv_image $< (\x. case x of INL v => v_i2_size v
                                      | INR vs => v_i23_size vs)` >>
 simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[v_i2_size_def] >>
 Cases >> simp[v_i2_size_def] >> rw[] >> res_tac >> simp[])
val _ = export_rewrites["good_v_i2_def"]

val good_vs_i2_EVERY = store_thm("good_vs_i2_EVERY",
  ``∀vs. good_vs_i2 vs ⇔ EVERY good_v_i2 vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_i2_EVERY"]

(* TODO: move *)

val exc_rel_def = Define`
  (exc_rel R (Rraise v1) (Rraise v2) = R v1 v2) ∧
  (exc_rel _ Rtype_error Rtype_error = T) ∧
  (exc_rel _ Rtimeout_error Rtimeout_error = T) ∧
  (exc_rel _ _ _ = F)`
val _ = export_rewrites["exc_rel_def"]

val exc_rel_raise1 = store_thm("exc_rel_raise1",
  ``exc_rel R (Rraise v) e = ∃v'. (e = Rraise v') ∧ R v v'``,
  Cases_on`e`>>rw[])
val exc_rel_raise2 = store_thm("exc_rel_raise2",
  ``exc_rel R e (Rraise v) = ∃v'. (e = Rraise v') ∧ R v' v``,
  Cases_on`e`>>rw[])
val exc_rel_type_error = store_thm("exc_rel_type_error",
  ``(exc_rel R Rtype_error e = (e = Rtype_error)) ∧
    (exc_rel R e Rtype_error = (e = Rtype_error))``,
  Cases_on`e`>>rw[])
val exc_rel_timeout_error = store_thm("exc_rel_timeout_error",
  ``(exc_rel R Rtimeout_error e = (e = Rtimeout_error)) ∧
    (exc_rel R e Rtimeout_error = (e = Rtimeout_error))``,
  Cases_on`e`>>rw[])
val _ = export_rewrites["exc_rel_raise1","exc_rel_raise2","exc_rel_type_error","exc_rel_timeout_error"]

val exc_rel_refl = store_thm(
"exc_rel_refl",
  ``(∀x. R x x) ⇒ ∀x. exc_rel R x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["exc_rel_refl"];

val exc_rel_trans = store_thm(
"exc_rel_trans",
``(∀x y z. R x y ∧ R y z ⇒ R x z) ⇒ (∀x y z. exc_rel R x y ∧ exc_rel R y z ⇒ exc_rel R x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[])

val result_rel_def = Define`
(result_rel R1 _ (Rval v1) (Rval v2) = R1 v1 v2) ∧
(result_rel _ R2 (Rerr e1) (Rerr e2) = exc_rel R2 e1 e2) ∧
(result_rel _ _ _ _ = F)`
val _ = export_rewrites["result_rel_def"]

val result_rel_Rval = store_thm(
"result_rel_Rval",
``result_rel R1 R2 (Rval v) r = ∃v'. (r = Rval v') ∧ R1 v v'``,
Cases_on `r` >> rw[])
val result_rel_Rerr1 = store_thm(
"result_rel_Rerr1",
``result_rel R1 R2 (Rerr e) r = ∃e'. (r = Rerr e') ∧ exc_rel R2 e e'``,
Cases_on `r` >> rw[EQ_IMP_THM])
val result_rel_Rerr2 = store_thm(
"result_rel_Rerr2",
``result_rel R1 R2 r (Rerr e) = ∃e'. (r = Rerr e') ∧ exc_rel R2 e' e``,
Cases_on `r` >> rw[EQ_IMP_THM])
val _ = export_rewrites["result_rel_Rval","result_rel_Rerr1","result_rel_Rerr2"]

val result_rel_refl = store_thm(
"result_rel_refl",
``(∀x. R1 x x) ∧ (∀x. R2 x x) ⇒ ∀x. result_rel R1 R2 x x``,
strip_tac >> Cases >> rw[])
val _ = export_rewrites["result_rel_refl"]

val result_rel_trans = store_thm(
"result_rel_trans",
``(∀x y z. R1 x y ∧ R1 y z ⇒ R1 x z) ∧ (∀x y z. R2 x y ∧ R2 y z ⇒ R2 x z) ⇒ (∀x y z. result_rel R1 R2 x y ∧ result_rel R1 R2 y z ⇒ result_rel R1 R2 x z)``,
rw[] >>
Cases_on `x` >> fs[] >> rw[] >> fs[] >> PROVE_TAC[exc_rel_trans])

val map_error_result_def = Define`
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f Rtype_error = Rtype_error) ∧
  (map_error_result f Rtimeout_error = Rtimeout_error)`
val _ = export_rewrites["map_error_result_def"]

val map_error_result_Rtype_error = store_thm("map_error_result_Rtype_error",
  ``map_error_result f e = Rtype_error ⇔ e = Rtype_error``,
  Cases_on`e`>>simp[])
val map_error_result_Rtimeout_error = store_thm("map_error_result_Rtimeout_error",
  ``map_error_result f e = Rtimeout_error ⇔ e = Rtimeout_error``,
  Cases_on`e`>>simp[])
val _ = export_rewrites["map_error_result_Rtimeout_error","map_error_result_Rtype_error"]

val every_error_result_def = Define`
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P Rtype_error = T) ∧
  (every_error_result P Rtimeout_error = T)`
val _ = export_rewrites["every_error_result_def"]

val map_result_def = Define`
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`
val _ = export_rewrites["map_result_def"]

val map_result_Rerr = store_thm("map_result_Rerr",
  ``map_result f1 f2 e = Rerr e' ⇔ ∃a. e = Rerr a ∧ map_error_result f2 a = e'``,
  Cases_on`e`>>simp[EQ_IMP_THM])
val _ = export_rewrites["map_result_Rerr"]

val every_result_def = Define`
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))`
val _ = export_rewrites["every_result_def"]

val map_count_store_genv_def = Define`
  map_count_store_genv f (csg:'a count_store_genv) =
    ((FST(FST csg), MAP f (SND(FST csg))), MAP (OPTION_MAP f) (SND csg))`

val lookup_ALOOKUP = store_thm(
"lookup_ALOOKUP",
``lookup = combin$C ALOOKUP``,
fs[FUN_EQ_THM] >> gen_tac >> Induct >- rw[] >> Cases >> rw[])
(*
val _ = augment_srw_ss[rewrites [lookup_ALOOKUP]];
*)

(* TODO: move *)
val ALOOKUP_find_index_SOME = prove(
  ``∀env. ALOOKUP env k = SOME v ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))``,
  Induct >> simp[] >> Cases >> rw[find_index_def] >-
    (qexists_tac`0`>>simp[]) >> fs[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>rw[]>>rw[]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]
val ALOOKUP_find_index_SOME = prove(
  ``ALOOKUP env k = SOME v ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env))``,
  rw[] >> imp_res_tac ALOOKUP_find_index_SOME >>
  imp_res_tac find_index_LESS_LENGTH >> fs[EL_MAP])
val ALOOKUP_find_index_NONE = prove(
  ``(ALOOKUP env k = NONE) ⇒ (find_index k (MAP FST env) m = NONE)``,
  rw[ALOOKUP_FAILS] >> rw[GSYM find_index_NOT_MEM,MEM_MAP,EXISTS_PROD])

val build_rec_env_i2_MAP = store_thm("build_rec_env_i2_MAP",
  ``build_rec_env_i2 funs cle env = MAP (λ(f,cdr). (f, (Recclosure_i2 cle funs f))) funs ++ env``,
  rw[build_rec_env_i2_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val lookup_find_index_SOME = prove(
  ``∀env. lookup n env = SOME v ⇒
      ∀m. ∃i. (find_index (SOME n) (MAP (SOME o FST) env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))``,
  Induct >> simp[] >> Cases >> rw[find_index_def] >-
    (qexists_tac`0`>>simp[]) >> fs[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>rw[]>>rw[]>>
  qexists_tac`SUC i`>>simp[])

val find_recfun_ALOOKUP = store_thm(
"find_recfun_ALOOKUP",
``∀funs n. find_recfun n funs = ALOOKUP funs n``,
Induct >- rw[semanticPrimitivesTheory.find_recfun_def] >>
qx_gen_tac `d` >>
PairCases_on `d` >>
rw[semanticPrimitivesTheory.find_recfun_def])

val vs_to_i4_MAP = store_thm("vs_to_i4_MAP",
  ``∀vs. vs_to_i4 vs = MAP v_to_i4 vs``,
  Induct >> simp[])
val _ = export_rewrites["vs_to_i4_MAP"]

val funs_to_i4_MAP = store_thm("funs_to_i4_MAP",
  ``∀funs bvs. funs_to_i4 bvs funs = MAP (λ(f,x,e). exp_to_i4 (SOME x::bvs) e) funs``,
  Induct >> simp[FORALL_PROD])

val do_eq_i4_correct = prove(
  ``(∀v1 v2. do_eq_i2 v1 v2 = do_eq_i4 (v_to_i4 v1) (v_to_i4 v2)) ∧
    (∀vs1 vs2. do_eq_list_i2 vs1 vs2 = do_eq_list_i4 (vs_to_i4 vs1) (vs_to_i4 vs2))``,
  ho_match_mp_tac do_eq_i2_ind >>
  simp[do_eq_i2_def,do_eq_i4_def] >>
  rw[] >> BasicProvers.CASE_TAC >> rw[])

val the_less_rwt = prove(
  ``the X Y < (X:num) ⇔ ∃z. (Y = SOME z) ∧ z < X``,
  Cases_on`Y`>>simp[compilerLibTheory.the_def])

val do_app_i4_correct = prove(
  ``∀op v1 v2 env s.
     good_v_i2 v1 ⇒
     (do_app_i4 (MAP (v_to_i4 o SND) env) (MAP v_to_i4 s) op (v_to_i4 v1) (v_to_i4 v2) =
      OPTION_MAP (λ(env,s,exp). (MAP (v_to_i4 o SND) env, MAP v_to_i4 s, exp_to_i4 (MAP (SOME o FST) env) exp))
        (do_app_i2 env s op v1 v2))``,
  Cases_on`op`>>TRY(Cases_on`o':opn`)>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
  simp[do_app_i2_def,do_app_i4_def,exn_env_i4_def,exn_env_i2_def
      ,libTheory.emp_def,libTheory.bind_def,do_eq_i4_correct,do_eq_i4_def]>>rw[]>>
  fs[find_recfun_ALOOKUP,funs_to_i4_MAP] >- (
    BasicProvers.CASE_TAC >> simp[] >> rw[] >>
    BasicProvers.CASE_TAC >> simp[] >> rw[] ) >>
  fs[the_less_rwt] >>
  BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_find_index_NONE >>
  imp_res_tac ALOOKUP_find_index_SOME >>
  fs[] >> rw[] >> fs[semanticPrimitivesTheory.store_assign_def] >> rw[] >>
  TRY ( rw[LIST_EQ_REWRITE] >> simp[EL_MAP,EL_LUPDATE] >> rw[funs_to_i4_MAP] >> NO_TAC) >>
  simp[build_rec_env_i2_MAP,build_rec_env_i4_def,EXISTS_PROD,EL_MAP,UNCURRY] >>
  BasicProvers.CASE_TAC >> rw[MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
  rw[LIST_EQ_REWRITE,EL_MAP,funs_to_i4_MAP] >>
  imp_res_tac find_index_ALL_DISTINCT_EL >>
  first_x_assum(qspec_then`x`mp_tac) >>
  (discharge_hyps >- simp[]) >>
  disch_then(qspec_then`0`mp_tac) >>
  ntac 2 (pop_assum kall_tac) >>
  asm_simp_tac(std_ss)[EL_MAP] >>
  simp[])

val good_env_s_i2_def = Define`
  good_env_s_i2 env (s:v_i2 count_store_genv) ⇔
    EVERY good_v_i2 (MAP SND env) ∧
    EVERY good_v_i2 (SND (FST s)) ∧
    EVERY (OPTION_EVERY good_v_i2) (SND s)`

val do_uapp_i3_preserves_good = prove(
  ``∀env s uop v s' v'. good_env_s_i2 env s ∧ good_v_i2 v ∧
    (do_uapp_i3 (SND(FST s),SND s) uop v = SOME (s',v')) ⇒
    good_env_s_i2 env ((FST(FST s),(FST s')),SND s') ∧
    good_v_i2 v'``,
  rpt gen_tac >> Cases_on`uop`>>EVAL_TAC>>
  TRY(BasicProvers.CASE_TAC) >>
  rw[] >>
  fs[EVERY_MEM,EVERY_MAP] >>
  TRY (fs[MEM_EL,PULL_EXISTS]>>NO_TAC) >>
  rw[] >> imp_res_tac MEM_LUPDATE_E >> rw[])

val do_app_i2_preserves_good = prove(
  ``∀env s op v1 v2 env' s' exp'.
     (do_app_i2 env s op v1 v2 = SOME (env', s', exp')) ∧
     EVERY good_v_i2 (MAP SND env) ∧
     EVERY good_v_i2 s ∧
     good_v_i2 v1 ∧ good_v_i2 v2
     ⇒
     EVERY good_v_i2 (MAP SND env') ∧
     EVERY good_v_i2 s'``,
  Cases_on`op`>>TRY(Cases_on`o':opn`)>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
  simp[do_app_i2_def,exn_env_i2_def,libTheory.emp_def,libTheory.bind_def,do_eq_i2_def]>>rw[]>>rw[]>>
  last_x_assum mp_tac >> BasicProvers.CASE_TAC >> rw[] >> rw[] >>
  fs[pair_CASE_def,semanticPrimitivesTheory.store_assign_def] >> rw[build_rec_env_i2_MAP] >>
  fs[EVERY_MAP,EVERY_MEM,UNCURRY,MEM_MAP] >>
  rw[] >> imp_res_tac MEM_LUPDATE_E >> rw[] >>
  rw[EVERY_MAP,EVERY_MEM] >> metis_tac[MEM_MAP])

val pmatch_i2_preserves_good = prove(
  ``(∀s p v env env'.
     EVERY good_v_i2 (MAP SND env) ∧
     EVERY good_v_i2 s ∧
     good_v_i2 v ∧
     pmatch_i2 s p v env = Match env' ⇒
     EVERY good_v_i2 (MAP SND env')) ∧
    (∀s ps vs env env'.
     EVERY good_v_i2 (MAP SND env) ∧
     EVERY good_v_i2 s ∧
     EVERY good_v_i2 vs ∧
     pmatch_list_i2 s ps vs env = Match env' ⇒
     EVERY good_v_i2 (MAP SND env'))``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def,libTheory.bind_def] >> fs[] >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >>fs[]>>rw[]>>
  first_x_assum match_mp_tac >>
  fs[semanticPrimitivesTheory.store_lookup_def,EVERY_MEM]>>
  fs[MEM_EL,PULL_EXISTS] >> rw[])

val evaluate_i3_preserves_good = store_thm("evaluate_i3_preserves_good",
  ``(∀ck env s exp res. evaluate_i3 ck env s exp res ⇒
      good_env_s_i2 env s ⇒
      good_env_s_i2 env (FST res) ∧
      every_result good_v_i2 good_v_i2 (SND res)) ∧
    (∀ck env s exps ress. evaluate_list_i3 ck env s exps ress ⇒
      good_env_s_i2 env s ⇒
      good_env_s_i2 env (FST ress) ∧
      every_result good_vs_i2 good_v_i2 (SND ress)) ∧
    (∀ck env s v pes res. evaluate_match_i3 ck env s v pes res ⇒
      good_env_s_i2 env s ∧ good_v_i2 v ⇒
      good_env_s_i2 env (FST res) ∧
      every_result good_v_i2 good_v_i2 (SND res))``,
  ho_match_mp_tac evaluate_i3_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[lookup_ALOOKUP,good_env_s_i2_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MAP,EVERY_MEM,FORALL_PROD] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    fs[good_env_s_i2_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    `n < LENGTH genv` by simp[] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> fs[good_env_s_i2_def] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    qpat_assum`good_env_s_i2 env s`mp_tac >>
    qmatch_assum_abbrev_tac`good_env_s_i2 env ss` >>
    Q.ISPECL_THEN[`env`,`ss`,`uop`,`v`]mp_tac do_uapp_i3_preserves_good  >>
    simp[Abbr`ss`] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    qspecl_then[`env`,`s3`,`op`,`v1`,`v2`]mp_tac do_app_i2_preserves_good >>
    simp[] >> fs[good_env_s_i2_def] ) >>
  strip_tac >- (
    rw[] >>
    qspecl_then[`env`,`s3`,`Opapp`,`v1`,`v2`]mp_tac do_app_i2_preserves_good >>
    simp[] >> fs[good_env_s_i2_def] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 2 gen_tac >>
    Cases >> rw[libTheory.opt_bind_def] >>
    fs[good_env_s_i2_def] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[build_rec_env_i2_MAP,good_env_s_i2_def] >>
    first_x_assum match_mp_tac >>
    fs[FST_triple,EVERY_MAP,UNCURRY] >>
    simp[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[good_env_s_i2_def,EVERY_GENLIST] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    imp_res_tac pmatch_i2_preserves_good >>
    fs[good_env_s_i2_def]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  rw[])

val evaluate_i4_lit = store_thm("evaluate_i4_lit",
  ``∀ck env s l res.
      evaluate_i4 ck env s (Lit_i4 l) res ⇔ (res = (s,Rval(Litv_i4 l)))``,
  rw[Once evaluate_i4_cases])
val _ = export_rewrites["evaluate_i4_lit"]

val sIf_i4_correct = store_thm("sIf_i4_correct",
  ``∀ck env s e1 e2 e3 res.
    evaluate_i4 ck env s (If_i4 e1 e2 e3) res ∧
    (SND res ≠ Rerr Rtype_error) ⇒
    evaluate_i4 ck env s (sIf_i4 e1 e2 e3) res``,
  rpt gen_tac >>
  Cases_on`e2=Lit_i4(Bool T) ∧ e3=Lit_i4(Bool F)` >- (
    simp[sIf_i4_def] >>
    simp[Once evaluate_i4_cases,do_if_i4_def] >>
    rw[] >> simp[] >> fs[] >>
    qpat_assum`X = Y`mp_tac >> rw[] >> fs[] ) >>
  simp[sIf_i4_def] >>
  Cases_on`e1`>>simp[]>>
  Cases_on`l`>>simp[]>>
  simp[Once evaluate_i4_cases] >>
  simp[do_if_i4_def] >> rw[])

val no_closures_i4_def = tDefine"no_closures_i4"`
  (no_closures_i4 (Litv_i4 _) ⇔ T) ∧
  (no_closures_i4 (Conv_i4 _ vs) ⇔ EVERY no_closures_i4 vs) ∧
  (no_closures_i4 (Closure_i4 _ _) = F) ∧
  (no_closures_i4 (Recclosure_i4 _ _ _) = F) ∧
  (no_closures_i4 (Loc_i4 _) = T)`
(WF_REL_TAC`measure v_i4_size`>>gen_tac>>Induct>>
 simp[v_i4_size_def]>>rw[]>>res_tac>>simp[])
val _ = export_rewrites["no_closures_i4_def"]

val evaluate_i4_raise_rval = store_thm("evaluate_i4_raise_rval",
  ``∀ck env s e s' v. ¬evaluate_i4 ck env s (Raise_i4 e) (s', Rval v)``,
  rw[Once evaluate_i4_cases])
val _ = export_rewrites["evaluate_i4_raise_rval"]

val fo_i4_correct = store_thm("fo_i4_correct",
  ``(∀e. fo_i4 e ⇒
       ∀ck env s s' v.
         evaluate_i4 ck env s e (s',Rval v) ⇒
         no_closures_i4 v) ∧
    (∀es. fo_list_i4 es ⇒
       ∀ck env s s' vs.
         evaluate_list_i4 ck env s es (s',Rval vs) ⇒
         EVERY no_closures_i4 vs)``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_i4``))>>
  simp[] >> reverse(rpt conj_tac) >> rpt gen_tac >> strip_tac >>
  simp[Once evaluate_i4_cases] >> rpt gen_tac >>
  TRY strip_tac >> fs[] >> simp[PULL_EXISTS,ETA_AX] >>
  TRY (metis_tac[])
  >- (pop_assum mp_tac >> simp[Once evaluate_i4_cases])
  >- (pop_assum mp_tac >> simp[Once evaluate_i4_cases,PULL_EXISTS])
  >- (
    simp[do_if_i4_def]>>
    rpt gen_tac >>
    rw[] >> metis_tac[] )
  >- (
    qmatch_assum_rename_tac`op ≠ Opapp`[]>>
    rpt gen_tac >>
    Cases_on`op`>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
    simp[do_app_i4_def]>>rw[]>>fs[do_eq_i4_def]>>rw[]>>fs[]>>
    qpat_assum`X = Y`mp_tac >> BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[] >>
    qpat_assum`X = Y`mp_tac >> BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[] )
  >- (
    qmatch_assum_rename_tac`uop ≠ Opderef_i4`[]>>
    rpt gen_tac >>
    Cases_on`uop`>>fs[do_uapp_i4_def,LET_THM,semanticPrimitivesTheory.store_alloc_def]>>
    TRY BasicProvers.CASE_TAC >> rw[] >> rw[]))

val do_eq_no_closures_i4 = store_thm("do_eq_no_closures_i4",
  ``(∀v1 v2. no_closures_i4 v1 ∧ no_closures_i4 v2 ⇒ do_eq_i4 v1 v2 ≠ Eq_closure) ∧
    (∀vs1 vs2. EVERY no_closures_i4 vs1 ∧ EVERY no_closures_i4 vs2 ⇒ do_eq_list_i4 vs1 vs2 ≠ Eq_closure)``,
  ho_match_mp_tac do_eq_i4_ind >>
  rw[do_eq_i4_def,ETA_AX] >> fs[] >>
  BasicProvers.CASE_TAC >> rw[] >> fs[])

val evaluate_i4_determ = store_thm("evaluate_i4_determ",
  ``(∀ck env s e res1. evaluate_i4 ck env s e res1 ⇒
       ∀res2. evaluate_i4 ck env s e res2 ⇒ (res2 = res1)) ∧
    (∀ck env s e res1. evaluate_list_i4 ck env s e res1 ⇒
       ∀res2. evaluate_list_i4 ck env s e res2 ⇒ (res2 = res1))``,
  ho_match_mp_tac evaluate_i4_ind >>
  rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp_tac(srw_ss())[Once evaluate_i4_cases] >>
  gen_tac >> strip_tac >>
  rpt (res_tac >> fs[] >> rpt BasicProvers.VAR_EQ_TAC))

val pure_i4_correct = store_thm("pure_i4_correct",
  ``(∀e. pure_i4 e ⇒
         ∀ck env s. (∃v. evaluate_i4 ck env s e (s,Rval v)) ∨
                    evaluate_i4 ck env s e (s,Rerr Rtype_error)) ∧
    (∀es. pure_list_i4 es ⇒
         ∀ck env s. (∃vs. evaluate_list_i4 ck env s es (s,Rval vs)) ∨
                    evaluate_list_i4 ck env s es (s,Rerr Rtype_error))``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_i4``)) >>
  simp[pure_i4_def] >> rw[] >> fs[]
  >- (simp[Once evaluate_i4_cases] >> PROVE_TAC[evaluate_i4_rules])
  >- (simp[Once evaluate_i4_cases] >> PROVE_TAC[evaluate_i4_rules])
  >- (simp[Once evaluate_i4_cases] >> PROVE_TAC[evaluate_i4_rules])
  >- (ntac 2 (simp[Once evaluate_i4_cases]) >> PROVE_TAC[evaluate_i4_rules,pair_CASES,optionTheory.option_CASES])
  >- (simp[Once evaluate_i4_cases] >> PROVE_TAC[evaluate_i4_rules])
  >- (
    first_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >- (
      simp[Once evaluate_i4_cases] >>
      PairCases_on`s` >> simp[] >>
      qmatch_abbrev_tac`X ∨ Y` >> qunabbrev_tac`Y` >>
      simp[Once evaluate_i4_cases] >>
      Cases_on`u`>>fs[do_uapp_i4_def,Abbr`X`] >>
      simp[DISJ_ASSOC] >> disj1_tac >>
      qho_match_abbrev_tac`(∃v1 v2 s1 s2. P v2 s1 s2 ∧ Q v1 v2 s1 s2) ∨ (∃v2. P2 v2 ∧ Q2 v2)` >>
      `P2 v = P v s1 s2` by ( unabbrev_all_tac >> simp[] ) >>
      `Q2 v = ¬(∃v1. Q v1 v s1 s2)` by (
        unabbrev_all_tac >> simp[] >>
        BasicProvers.CASE_TAC >>
        BasicProvers.CASE_TAC ) >>
      metis_tac[] ) >>
    disj2_tac >>
    simp[Once evaluate_i4_cases] )
  >- (
    qmatch_assum_rename_tac`pure_op op`[] >>
    qmatch_assum_rename_tac`pure_i4 e2`[] >>
    qpat_assum`pure_i4 e2`mp_tac >>
    qmatch_assum_rename_tac`pure_i4 e1`[] >>
    strip_tac >>
    Cases_on`evaluate_i4 ck env s (App_i4 op e1 e2) (s,Rerr Rtype_error)` >> simp[] >>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`App_i4 op e1 e2`](CONJUNCT1 evaluate_i4_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    first_x_assum(qspecl_then[`v`,`s`]mp_tac)>>simp[]>>strip_tac>>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    qmatch_assum_rename_tac`evaluate_i4 ck env s e2 (s,Rval v2)`[]>>
    PairCases_on`s`>>fs[]>>
    first_x_assum(qspecl_then[`v`,`v2`,`((s0,s1),s2)`]mp_tac)>>simp[]>>strip_tac>>
    Cases_on`do_app_i4 env s1 op v v2`>>fs[]>>
    PairCases_on`x`>>
    first_x_assum(qspecl_then[`v`,`v2`,`x0`,`x2`,`(s0,s1),s2`,`s1`,`s0`,`x1`,`s2`]mp_tac)>>
    simp[]>>
    Cases_on`op=Opapp`>>fs[]>>strip_tac>>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`s2`,`x1`,`s0`,`s1`,`(s0,s1),s2`,`x2`,`x0`,`v2`,`v`]>>
    simp[]>>
    Cases_on`op`>>Cases_on`v`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
    fs[do_app_i4_def] >> rfs[] >> rw[bigStepTheory.dec_count_def] )
  >- (
    qmatch_assum_rename_tac`pure_i4 e2`[] >>
    qpat_assum`pure_i4 e2`mp_tac >>
    qmatch_assum_rename_tac`pure_i4 e1`[] >>
    strip_tac >>
    Cases_on`evaluate_i4 ck env s (App_i4 Equality e1 e2) (s,Rerr Rtype_error)` >> simp[] >>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`App_i4 op e1 e2`](CONJUNCT1 evaluate_i4_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    first_x_assum(qspecl_then[`v`,`s`]mp_tac)>>simp[]>>strip_tac>>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    qmatch_assum_rename_tac`evaluate_i4 ck env s e2 (s,Rval v2)`[]>>
    PairCases_on`s`>>fs[]>>
    first_x_assum(qspecl_then[`v`,`v2`,`((s0,s1),s2)`]mp_tac)>>simp[]>>strip_tac>>
    Cases_on`do_app_i4 env s1 Equality v v2`>>fs[]>>
    PairCases_on`x`>>
    first_x_assum(qspecl_then[`v`,`v2`,`x0`,`x2`,`(s0,s1),s2`,`s1`,`s0`,`x1`,`s2`]mp_tac)>>
    simp[]>> strip_tac>>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`s2`,`x1`,`s0`,`s1`,`(s0,s1),s2`,`x2`,`x0`,`v2`,`v`]>>
    fs[do_app_i4_def] >>
    imp_res_tac fo_i4_correct >>
    Cases_on`do_eq_i4 v v2`>>fs[]>>rw[bigStepTheory.dec_count_def]>>
    imp_res_tac do_eq_no_closures_i4 )
  >- (
    qmatch_abbrev_tac`X ∨ Y`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def]>>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`If_i4 e1 e2 e3`](CONJUNCT1 evaluate_i4_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    first_x_assum(qspec_then`v`strip_assume_tac)>>fs[]>>
    qmatch_assum_rename_tac`do_if_i4 v1 e2 e3 ≠ NONE`[]>>
    Cases_on`do_if_i4 v1 e2 e3`>>fs[]>>
    first_x_assum(qspecl_then[`v1`,`x`,`s`]strip_assume_tac)>>fs[]>>
    rw[] >> fs[do_if_i4_def] >>
    CONV_TAC(RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`s`,`x`,`v1`] >>
    rw[] >>
    qpat_assum`X = Y`mp_tac >> rw[] >>
    metis_tac[] )
  >- (
    qmatch_abbrev_tac`X ∨ Y`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def]>>rw[]>>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`Let_i4 e1 e2`](CONJUNCT1 evaluate_i4_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    first_x_assum(qspecl_then[`v`,`s`]strip_assume_tac)>>fs[]>>
    metis_tac[] )
  >- (
    qmatch_abbrev_tac`X ∨ Y`>>
    Cases_on`Y`>>fs[markerTheory.Abbrev_def]>>rw[]>>
    fs[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`Seq_i4 e1 e2`](CONJUNCT1 evaluate_i4_cases))] >>
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >> fs[] >>
    first_x_assum(qspecl_then[`v`,`s`]strip_assume_tac)>>fs[]>>
    metis_tac[] )
  >- (
    simp[Once evaluate_i4_cases] >>
    Q.PAT_ABBREV_TAC`renv = build_rec_env_i4 X Y ++ z` >>
    first_x_assum(qspecl_then[`ck`,`renv`,`s`]strip_assume_tac) >> fs[] >-
      metis_tac[] >>
    disj2_tac >>
    simp[Once evaluate_i4_cases] )
  >- simp[Once evaluate_i4_cases]
  >- (
    simp[Once evaluate_i4_cases] >>
    simp[SIMP_RULE(srw_ss())[](Q.SPECL [`ck`,`env`,`s`,`e::es`](CONJUNCT2 evaluate_i4_cases))] >>
    metis_tac[]))

val TAKE_CONS = prove(
  ``TAKE (n+1) env = v::TAKE n env2 ⇔ ∃env1. env = v::env1 ∧ TAKE n env1 = TAKE n env2``,
  Cases_on`env`>>simp[])

val ground_i4_correct = store_thm("ground_i4_correct",
  ``(∀e n. ground_i4 n e ⇒
      (∀ck env1 env2 s res.
          n ≤ LENGTH env1 ∧ n ≤ LENGTH env2 ∧
          (TAKE n env2 = TAKE n env1) ∧
          evaluate_i4 ck env1 s e res ⇒
          evaluate_i4 ck env2 s e res)) ∧
    (∀es n. ground_list_i4 n es ⇒
      (∀ck env1 env2 s res.
          n ≤ LENGTH env1 ∧ n ≤ LENGTH env2 ∧
          (TAKE n env2 = TAKE n env1) ∧
          evaluate_list_i4 ck env1 s es res ⇒
          evaluate_list_i4 ck env2 s es res))``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_i4``)) >>
  rw[] >> pop_assum mp_tac >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] )
  >- (
    first_x_assum(qspec_then`n+1`strip_assume_tac)>>
    first_x_assum(qspec_then`n`strip_assume_tac)>>
    rfs[] >>
    first_x_assum(qspecl_then[`ck`,`env1`,`env2`,`s`]mp_tac) >>
    simp[] >> strip_tac >>
    rw[Once evaluate_i4_cases] >>
    res_tac >>
    simp[Once evaluate_i4_cases] >>
    fsrw_tac[ARITH_ss][TAKE_CONS,PULL_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    fs[LIST_EQ_REWRITE] >>
    rfs[rich_listTheory.EL_TAKE] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] )
  >- (
    rpt(first_x_assum(qspec_then`n`strip_assume_tac)) >> rfs[] >>
    first_x_assum(qspecl_then[`ck`,`env1`,`env2`,`s`]mp_tac) >>
    simp[] >> strip_tac >>
    reverse(rw[Once evaluate_i4_cases])
    >- simp[Once evaluate_i4_cases]
    >- (
      simp[Once evaluate_i4_cases] >>
      metis_tac[] ) >>
    TRY (
      qmatch_assum_rename_tac`do_app_i4 env1 s3 Opapp v1 v2 = SOME X`["X"] >>
      rw[Once evaluate_i4_cases] >>
      disj2_tac >> disj1_tac >>
      map_every qexists_tac[`v1`,`v2`] >>
      fs[do_app_i4_def]>>Cases_on`v1`>>fs[]>>rw[]>>
      metis_tac[] )
    >- (
      qmatch_assum_rename_tac`do_app_i4 env1 s3 op v1 v2 = X`["X"] >>
      simp[Once evaluate_i4_cases] >>
      disj2_tac >> disj1_tac >>
      map_every qexists_tac[`v1`,`v2`,`s2`] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- metis_tac[] >>
      Cases_on`op`>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>fs[do_app_i4_def]>>
      Cases_on`v2`>>TRY(Cases_on`l:lit`)>>fs[do_app_i4_def,do_eq_i4_def]>>
      rw[]>>fs[]>>fs[]>>rfs[]>>
      pop_assum mp_tac >> BasicProvers.CASE_TAC ) >>
    qmatch_assum_rename_tac`do_app_i4 env1 s3 op v1 v2 = X`["X"] >>
    simp[Once evaluate_i4_cases] >>
    disj1_tac >>
    map_every qexists_tac[`v1`,`v2`] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    qexists_tac`genv3` >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`count'` >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`s3` >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`s2` >>
    simp[GSYM PULL_EXISTS] >>
    conj_tac >- metis_tac[] >>
    Cases_on`op`>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>fs[do_app_i4_def]>>
    Cases_on`v2`>>TRY(Cases_on`l:lit`)>>fs[do_app_i4_def,do_eq_i4_def]>>
    rw[]>>fs[]>>fs[]>>rfs[]>>rw[]>>fs[]>>
    BasicProvers.CASE_TAC>>fs[]>>rw[]>>fs[])
  >- (
    reverse(rw[Once evaluate_i4_cases]) >>
    simp[Once evaluate_i4_cases]
    >- metis_tac[]
    >- metis_tac[] >>
    disj1_tac >>
    qexists_tac`v` >>
    qpat_assum`do_if_i4 X Y Z = A`mp_tac >>
    simp[do_if_i4_def] >>
    rw[] >>
    metis_tac[] )
  >- (
    first_x_assum(qspec_then`n+1`strip_assume_tac)>>
    first_x_assum(qspec_then`n`strip_assume_tac)>>
    rfs[] >>
    first_x_assum(qspecl_then[`ck`,`env1`,`env2`,`s`]mp_tac) >>
    simp[] >> strip_tac >>
    rw[Once evaluate_i4_cases] >>
    res_tac >>
    simp[Once evaluate_i4_cases] >>
    fsrw_tac[ARITH_ss][TAKE_CONS,PULL_EXISTS,arithmeticTheory.ADD1] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] )
  >- (
    rw[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    metis_tac[] ))

val sLet_i4_thm = store_thm("sLet_i4_thm",
  ``sLet_i4 e1 e2 =
    if e2 = Var_local_i4 0 then e1 else
    if ground_i4 0 e2 then
      if pure_i4 e1 then e2 else Seq_i4 e1 e2
    else Let_i4 e1 e2``,
  Cases_on`e2`>>rw[sLet_i4_def]>>
  Cases_on`n`>>rw[sLet_i4_def])

val sLet_i4_correct = store_thm("sLet_i4_correct",
  ``∀ck env s e1 e2 res.
    evaluate_i4 ck env s (Let_i4 e1 e2) res ∧
    SND res ≠ Rerr Rtype_error ⇒
    evaluate_i4 ck env s (sLet_i4 e1 e2) res``,
  rw[sLet_i4_thm] >- (
    last_x_assum mp_tac >>
    simp[Once evaluate_i4_cases] >>
    rw[] >> rw[] >>
    pop_assum mp_tac >>
    rw[Once evaluate_i4_cases] )
  >- (
    qpat_assum`evaluate_i4 A B C D E` mp_tac >>
    imp_res_tac pure_i4_correct >>
    first_x_assum(qspecl_then[`s`,`env`,`ck`]strip_assume_tac) >>
    rw[Once evaluate_i4_cases] >> rw[] >>
    imp_res_tac evaluate_i4_determ >> fs[] >> rw[] >>
    qspecl_then[`e2`,`0`]mp_tac(CONJUNCT1 ground_i4_correct) >>
    rw[] >> res_tac >>
    metis_tac[]) >>
  qpat_assum`evaluate_i4 A B C D E` mp_tac >>
  rw[Once evaluate_i4_cases] >>
  qspecl_then[`e2`,`0`]mp_tac(CONJUNCT1 ground_i4_correct) >>
  rw[] >> res_tac >>
  rw[Once evaluate_i4_cases] >> rw[] >>
  metis_tac[])

val Let_Els_i4_correct = prove(
  ``∀n k e tag vs env ck s res us.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate_i4 ck (TAKE k vs ++ us ++ (Conv_i4 tag vs::env)) s e res ∧
    SND res ≠ Rerr Rtype_error ⇒
    evaluate_i4 ck (us ++ (Conv_i4 tag vs::env)) s (Let_Els_i4 n k e) res``,
  ho_match_mp_tac Let_Els_i4_ind >> rw[Let_Els_i4_def] >>
  match_mp_tac sLet_i4_correct >>
  rw[Once evaluate_i4_cases] >>
  disj1_tac >>
  rw[Once evaluate_i4_cases] >>
  rw[Once evaluate_i4_cases] >>
  simp[rich_listTheory.EL_APPEND2] >>
  simp[do_uapp_i4_def,PULL_EXISTS] >>
  qmatch_assum_rename_tac`SUC k ≤ LENGTH vs`[] >>
  first_x_assum(qspecl_then[`tag`,`vs`,`env`,`ck`,`s`,`res`,`EL k vs::us`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    fs[arithmeticTheory.ADD1] >>
    `k < LENGTH vs` by simp[] >>
    fs[TAKE_EL_SNOC] >>
    fs[SNOC_APPEND] >>
    metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
  PairCases_on`s` >> rw[])
val Let_Els_i4_correct = prove(
  ``∀n k e tag vs env ck s res us enve.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate_i4 ck (TAKE k vs ++ us ++ (Conv_i4 tag vs::env)) s e res ∧
    (enve = us ++ (Conv_i4 tag vs::env)) ∧ SND res ≠ Rerr Rtype_error
    ⇒
    evaluate_i4 ck enve s (Let_Els_i4 n k e) res``,
  metis_tac[Let_Els_i4_correct])

val pmatch_i2_any_match = store_thm("pmatch_i2_any_match",
  ``(∀s p v env env'. pmatch_i2 s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch_i2 s p v env = Match env') ∧
    (∀s ps vs env env'. pmatch_list_i2 s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list_i2 s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_i2_any_no_match = store_thm("pmatch_i2_any_no_match",
  ``(∀s p v env. pmatch_i2 s p v env = No_match ⇒
       ∀env. pmatch_i2 s p v env = No_match) ∧
    (∀s ps vs env. pmatch_list_i2 s ps vs env = No_match ⇒
       ∀env. pmatch_list_i2 s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  imp_res_tac pmatch_i2_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_i2_any_match_error = store_thm("pmatch_i2_any_match_error",
  ``(∀s p v env. pmatch_i2 s p v env = Match_type_error ⇒
       ∀env. pmatch_i2 s p v env = Match_type_error) ∧
    (∀s ps vs env. pmatch_list_i2 s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list_i2 s ps vs env = Match_type_error)``,
  rw[] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> fs[markerTheory.Abbrev_def] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct
           ,pmatch_i2_any_no_match,pmatch_i2_any_match])

val pmatch_list_i2_pairwise = store_thm("pmatch_list_i2_pairwise",
  ``∀ps vs s env env'. pmatch_list_i2 s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch_i2 s p v env = Match env') ps vs``,
  Induct >> Cases_on`vs` >> simp[pmatch_i2_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_i2_any_match])

val pmatch_list_i2_SNOC_nil = store_thm("pmatch_list_i2_SNOC_nil",
  ``∀p ps v vs s env.
      (pmatch_list_i2 s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list_i2 s (SNOC p ps) [] env = Match_type_error)``,
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_i2_def])
val _ = export_rewrites["pmatch_list_i2_SNOC_nil"]

val pmatch_list_i2_SNOC = store_thm("pmatch_list_i2_SNOC",
  ``∀ps vs p v s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list_i2 s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list_i2 s ps vs env of
      | Match env' => pmatch_i2 s p v env'
      | res => res``,
  Induct >> Cases_on`vs` >> simp[pmatch_i2_def] >> rw[] >>
  BasicProvers.CASE_TAC)

val pat_to_i4_correct = prove(
  ``(∀p v s env res env4 ck count genv.
       pmatch_i2 s p v env = res ∧ res ≠ Match_type_error ⇒
       evaluate_i4 ck
         (v_to_i4 v::env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pat_to_i4 p)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool (∃env'. res = Match env'))))) ∧
    (∀n ps qs vs s env env' res env4 ck count genv.
       pmatch_list_i2 s qs (TAKE n vs) env = Match env' ∧
       pmatch_list_i2 s ps (DROP n vs) env = res ∧ res ≠ Match_type_error ∧
       (n = LENGTH qs) ∧ n ≤ LENGTH vs ⇒
       evaluate_i4 ck
         (vs_to_i4 vs ++ env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pats_to_i4 n ps)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool (∃env'. res = Match env')))))``,
  ho_match_mp_tac pat_to_i4_ind >>
  rw[pmatch_i2_def,pat_to_i4_def]
  >- (
    (Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[]) >>
    rw[Once evaluate_i4_cases] >>
    rw[do_app_i4_def] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_eq_i4_def] >>
    rw[Once evaluate_i4_cases] >>
    rw[bigStepTheory.dec_count_def,map_count_store_genv_def] )
  >- (
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[LENGTH_NIL_SYM] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_app_i4_def] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_eq_i4_def] >>
    rw[Once evaluate_i4_cases] >>
    rw[bigStepTheory.dec_count_def,map_count_store_genv_def] >>
    simp[pmatch_i2_def])
  >- (
    match_mp_tac sIf_i4_correct >>
    simp[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    simp[do_uapp_i4_def] >>
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> reverse(rw[]) >- (
      simp[PULL_EXISTS,do_if_i4_def] >>
      fs[map_count_store_genv_def] ) >>
    rw[PULL_EXISTS] >>
    rw[do_if_i4_def] >>
    fs[map_count_store_genv_def] >>
    match_mp_tac Let_Els_i4_correct >>
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt] >>
    fs[LENGTH_NIL_SYM,pmatch_i2_def])
  >- (
    match_mp_tac sLet_i4_correct >> simp[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def,PULL_EXISTS] >>
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[] >>
    fs[map_count_store_genv_def] >>
    fs[semanticPrimitivesTheory.store_lookup_def] >>
    rw[] >> fs[] >> simp[EL_MAP])
  >- (Cases_on`DROP (LENGTH qs) vs`>>fs[pmatch_i2_def]) >>
  match_mp_tac sIf_i4_correct >> simp[] >>
  rw[Once evaluate_i4_cases] >>
  qho_match_abbrev_tac`∃v e s2. evaluate_i4 ck B C (sLet_i4 D E) (s2,Rval v) ∧ P v e s2` >>
  qsuff_tac`∃v e s2. evaluate_i4 ck B C (Let_i4 D E) (s2,Rval v) ∧ P v e s2` >- (
    rw[] >> map_every qexists_tac[`v`,`e`,`s2`] >> simp[] >>
    match_mp_tac sLet_i4_correct >> simp[] ) >>
  unabbrev_all_tac >>
  rw[Once evaluate_i4_cases] >>
  rw[Once evaluate_i4_cases] >>
  Cases_on`LENGTH qs = LENGTH vs` >- (
    fs[DROP_LENGTH_NIL_rwt,pmatch_i2_def] ) >>
  simp[rich_listTheory.EL_APPEND1,EL_MAP] >>
  imp_res_tac pmatch_list_i2_pairwise >>
  Cases_on`DROP (LENGTH qs) vs` >> fs[pmatch_i2_def] >>
  qmatch_assum_rename_tac`DROP (LENGTH qs) vs = v::ws`[] >>
  Q.PAT_ABBREV_TAC`env5 = X ++ env4` >>
  `LENGTH qs < LENGTH vs` by simp[] >>
  fs[DROP_EL_CONS] >>
  first_x_assum(qspecl_then[`v`,`s`,`env`,`env5`,`ck`]mp_tac) >>
  Cases_on`pmatch_i2 s p v env`>>fs[] >- (
    strip_tac >> qexists_tac`Litv_i4 (Bool F)` >>
    simp[do_if_i4_def] ) >>
  strip_tac >> qexists_tac`Litv_i4 (Bool T)` >>
  simp[do_if_i4_def] >>
  Q.PAT_ABBREV_TAC`s2 = map_count_store_genv v_to_i4 Y` >>
  qexists_tac`s2` >>
  simp[Abbr`s2`,Abbr`env5`] >>
  first_x_assum(qspecl_then[`qs++[p]`,`vs`,`s`,`env`]mp_tac) >>
  simp[] >>
  simp[TAKE_EL_SNOC,GSYM SNOC_APPEND] >>
  simp[pmatch_list_i2_SNOC] >>
  imp_res_tac pmatch_i2_any_match >>
  qmatch_assum_rename_tac`pmatch_list_i2 s qs X env = Match env2`["X"] >>
  last_x_assum(qspec_then`env2`strip_assume_tac)>>simp[]>>
  qmatch_assum_rename_tac`pmatch_i2 s p v env = Match env3`[]>>
  Cases_on`pmatch_list_i2 s ps ws env`>>simp[]>>
  Cases_on`pmatch_list_i2 s ps ws env3`>>fs[]>>
  metis_tac[pmatch_i2_any_match_error
           ,pmatch_i2_any_match
           ,pmatch_i2_any_no_match
           ,semanticPrimitivesTheory.match_result_distinct])

val map_match_def = Define`
  (map_match f (Match env) = Match (f env)) ∧
  (map_match f x = x)`
val _ = export_rewrites["map_match_def"]

val pmatch_i2_APPEND = store_thm("pmatch_i2_APPEND",
  ``(∀s p v env n.
      (pmatch_i2 s p v env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_i2 s p v (TAKE n env)))) ∧
    (∀s ps vs env n.
      (pmatch_list_i2 s ps vs env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_list_i2 s ps vs (TAKE n env))))``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def,libTheory.bind_def]
  >- ( BasicProvers.CASE_TAC >> fs[] ) >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch_i2 s p v (TAKE n env)`>>fs[] >>
  strip_tac >> res_tac >>
  qmatch_assum_rename_tac`pmatch_i2 s p v (TAKE n env) = Match env1`[] >>
  pop_assum(qspec_then`LENGTH env1`mp_tac) >>
  simp_tac(srw_ss())[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND] )

val pmatch_i2_nil = save_thm("pmatch_i2_nil",
  LIST_CONJ [
    pmatch_i2_APPEND
    |> CONJUNCT1
    |> Q.SPECL[`s`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_i2_APPEND
    |> CONJUNCT2
    |> Q.SPECL[`s`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

val row_to_i4_correct = prove(
  ``(∀Nbvs0 p bvs0 s v menv bvs1 n f.
       (Nbvs0 = NONE::bvs0) ∧
       (pmatch_i2 s p v [] = Match menv) ∧
       (row_to_i4 Nbvs0 p = (bvs1,n,f))
     ⇒ ∃menv4 bvs.
        (bvs1 = bvs ++ bvs0) ∧
        (LENGTH bvs = SUC n) ∧
        (LENGTH menv4 = SUC n) ∧
        (FILTER (IS_SOME o FST) (ZIP(bvs,menv4)) =
         MAP (λ(x,v). (SOME x, v_to_i4 v)) menv) ∧
        ∀ck env count genv e res.
          evaluate_i4 ck (menv4++env) ((count, MAP v_to_i4 s),genv) e res ∧
          SND res ≠ Rerr Rtype_error ⇒
          evaluate_i4 ck (v_to_i4 v::env) ((count, MAP v_to_i4 s),genv) (f e) res) ∧
    (∀bvsk0 nk k ps tag s qs vs menvk menv4k menv bvsk bvs0 bvs1 n1 f.
      (pmatch_list_i2 s qs (TAKE k vs) [] = Match menvk) ∧
      (pmatch_list_i2 s ps (DROP k vs) [] = Match menv) ∧
      (cols_to_i4 bvsk0 nk k ps = (bvs1,n1,f)) ∧
      (bvsk0 = bvsk ++ NONE::bvs0) ∧
      (k = LENGTH qs) ∧ k ≤ LENGTH vs ∧ (LENGTH bvsk = nk) ∧
      (LENGTH menv4k = LENGTH bvsk) ∧
      (FILTER (IS_SOME o FST) (ZIP(bvsk,menv4k)) =
       MAP (λ(x,v). (SOME x, v_to_i4 v)) menvk)
    ⇒ ∃menv4 bvs.
        (bvs1 = bvs ++ bvsk ++ NONE::bvs0) ∧
        (LENGTH bvs = n1) ∧ (LENGTH menv4 = n1) ∧
        (FILTER (IS_SOME o FST) (ZIP(bvs,menv4)) =
         MAP (λ(x,v). (SOME x, v_to_i4 v)) menv) ∧
        ∀ck env count genv e res.
          evaluate_i4 ck (menv4++menv4k++(Conv_i4 tag (MAP v_to_i4 vs))::env) ((count, MAP v_to_i4 s),genv) e res ∧
          SND res ≠ Rerr Rtype_error ⇒
          evaluate_i4 ck (menv4k++(Conv_i4 tag (MAP v_to_i4 vs))::env) ((count, MAP v_to_i4 s),genv) (f e) res)``,
  ho_match_mp_tac row_to_i4_ind >>
  strip_tac >- (
    rw[pmatch_i2_def,row_to_i4_def,libTheory.bind_def] >> rw[] >>
    qexists_tac`[v_to_i4 v]` >> rw[] ) >>
  strip_tac >- (
    rw[pmatch_i2_def,row_to_i4_def] >> rw[] >>
    qexists_tac`[v_to_i4 v]` >> rw[] >>
    Cases_on`v`>>fs[pmatch_i2_def] >>
    pop_assum mp_tac >> rw[] ) >>
  strip_tac >- (
    rw[pmatch_i2_def,row_to_i4_def] >> fs[] >>
    Cases_on`v`>>fs[pmatch_i2_def] >>
    qpat_assum`X = Match menv`mp_tac >> rw[] >>
    qmatch_assum_rename_tac`pmatch_list_i2 s ps vs [] = Match menv`[] >>
    fs[LENGTH_NIL,pmatch_i2_def,LENGTH_NIL_SYM] >>
    Q.PAT_ABBREV_TAC`w = Conv_i4 X Y` >>
    qmatch_assum_rename_tac`Abbrev(w = Conv_i4 tag (MAP v_to_i4 vs))`[] >>
    first_x_assum(qspecl_then[`tag`,`s`,`vs`]mp_tac) >> rw[] >> rw[] >>
    simp[] >>
    qexists_tac`menv4++[w]` >>
    simp[GSYM rich_listTheory.ZIP_APPEND,rich_listTheory.FILTER_APPEND] >>
    REWRITE_TAC[Once (GSYM APPEND_ASSOC),Once(GSYM rich_listTheory.CONS_APPEND)] >>
    rpt strip_tac >> res_tac >> fs[] ) >>
  strip_tac >- (
    rw[row_to_i4_def] >>
    Cases_on`v`>>fs[pmatch_i2_def] >>
    qpat_assum`X = Match menv`mp_tac >> BasicProvers.CASE_TAC >>
    rw[] >> fs[UNCURRY,LET_THM] >> rw[] >>
    qmatch_assum_rename_tac`pmatch_i2 s p v [] = Match menv`[] >>
    first_x_assum(qspecl_then[`s`,`v`]mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`t = row_to_i4 X Y` >>
    `∃bvs1 n f. t = (bvs1,n,f)` by simp[GSYM EXISTS_PROD] >>
    qunabbrev_tac`t` >> simp[] >> rw[] >> simp[] >>
    Q.PAT_ABBREV_TAC`w = Loc_i4 X` >>
    qexists_tac`menv4++[w]` >>
    simp[GSYM rich_listTheory.ZIP_APPEND,rich_listTheory.FILTER_APPEND] >>
    REWRITE_TAC[Once (GSYM APPEND_ASSOC)] >>
    rpt strip_tac >> res_tac >> fs[] >>
    match_mp_tac sLet_i4_correct >>
    simp[Once evaluate_i4_cases] >>
    simp[Once evaluate_i4_cases] >>
    simp[do_uapp_i4_def,PULL_EXISTS] >>
    simp[Once evaluate_i4_cases,Abbr`w`] >>
    fs[semanticPrimitivesTheory.store_lookup_def] >>
    simp[EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[row_to_i4_def] >>
    imp_res_tac pmatch_list_i2_pairwise >>
    imp_res_tac EVERY2_LENGTH >>
    fs[LENGTH_NIL,pmatch_i2_def] ) >>
  rw[row_to_i4_def] >>
  `∃bvsk1 nk1 f1. row_to_i4 (NONE::(bvsk++[NONE]++bvs0)) p = (bvsk1,nk1,f1)` by
    simp[GSYM EXISTS_PROD] >> fs[LET_THM] >>
  `∃bvs n fs. cols_to_i4 bvsk1 (LENGTH bvsk + 1 + nk1) (LENGTH qs + 1) ps = (bvs,n,fs)` by
    simp[GSYM EXISTS_PROD] >> fs[] >>
  rw[] >>
  Cases_on`DROP (LENGTH qs) vs`>>fs[pmatch_i2_def] >>
  qmatch_assum_rename_tac`DROP (LENGTH qs) vs = v::ws`[] >>
  Cases_on`pmatch_i2 s p v []`>>fs[] >>
  first_x_assum(qspecl_then[`s`,`v`]mp_tac) >> simp[] >>
  strip_tac >> rw[] >>
  first_x_assum(qspecl_then[`tag`,`s`,`qs++[p]`,`vs`]mp_tac) >>
  Cases_on`LENGTH vs = LENGTH qs`>>fs[DROP_LENGTH_NIL_rwt] >>
  `LENGTH qs < LENGTH vs` by simp[] >>
  fs[DROP_EL_CONS] >>
  simp[TAKE_EL_SNOC,Once(GSYM SNOC_APPEND)] >>
  simp[pmatch_list_i2_SNOC] >>
  imp_res_tac (CONJUNCT1 pmatch_i2_any_match) >>
  pop_assum(qspec_then`menvk`strip_assume_tac) >> simp[] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac (CONJUNCT2 pmatch_i2_any_match) >>
  rpt(pop_assum(qspec_then`[]`mp_tac)) >>
  ntac 2 strip_tac >> simp[] >>
  disch_then(qspec_then`bvs0`mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
  simp[] >>
  qmatch_assum_rename_tac`FILTER P (ZIP(bvs2,menv4)) = MAP Z env2`["P","Z"] >>
  disch_then(qspec_then`menv4 ++ menv4k`mp_tac) >>
  simp[rich_listTheory.FILTER_APPEND,GSYM(rich_listTheory.ZIP_APPEND)] >>
  discharge_hyps >- (
    qpat_assum`pmatch_i2 s p v menvk = X`mp_tac >>
    simp[Once (CONJUNCT1 pmatch_i2_nil)] >>
    REWRITE_TAC[GSYM MAP_APPEND] >> PROVE_TAC[] ) >>
  rw[] >> rw[] >> simp[] >>
  qmatch_assum_rename_tac`LENGTH bvs3 = LENGTH menv3`[] >>
  qexists_tac`menv3 ++ menv4` >> simp[] >>
  simp[rich_listTheory.FILTER_APPEND,GSYM(rich_listTheory.ZIP_APPEND)] >>
  conj_tac >- (
    qpat_assum`pmatch_list_i2 s ps ww env2 = X`mp_tac >>
    simp[Once (CONJUNCT2 pmatch_i2_nil)] >>
    REWRITE_TAC[GSYM MAP_APPEND] >> PROVE_TAC[] ) >>
  rw[] >>
  match_mp_tac sLet_i4_correct >>
  simp[Once evaluate_i4_cases] >>
  simp[Once evaluate_i4_cases] >>
  simp[do_uapp_i4_def] >>
  simp[Once evaluate_i4_cases] >>
  simp[rich_listTheory.EL_APPEND2] >>
  simp[EL_MAP])

val bind_i4_def = Define`
  (bind_i4 V 0 0 ⇔ T) ∧
  (bind_i4 V (SUC n1) (SUC n2) ⇔ V n1 n2) ∧
  (bind_i4 V _ _ ⇔ F)`

val bind_i4_mono = store_thm("bind_i4_mono",
  ``(∀x y. V1 x y ⇒ V2 x y) ⇒ bind_i4 V1 x y ⇒ bind_i4 V2 x y``,
  Cases_on`x`>>Cases_on`y`>>rw[bind_i4_def])
val _ = export_mono"bind_i4_mono"

val bindn_i4_def = Define`bindn_i4 = FUNPOW bind_i4`

val bind_i4_thm = store_thm("bind_i4_thm",
  ``∀V x y. bind_i4 V x y =
      if x = 0 then y = 0 else
      if y = 0 then x = 0 else
      V (x-1) (y-1)``,
  gen_tac >> Cases >> Cases >> rw[bind_i4_def])

val FUNPOW_mono = store_thm("FUNPOW_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ∧
    (∀R1 R2. (∀x y. R1 x y ⇒ R2 x y) ⇒ ∀x y. f R1 x y ⇒ f R2 x y) ⇒
    ∀n x y. FUNPOW f n R1 x y ⇒ FUNPOW f n R2 x y``,
  strip_tac >> Induct >> simp[] >>
  simp[arithmeticTheory.FUNPOW_SUC] >>
  first_x_assum match_mp_tac >> rw[])

val bindn_i4_mono = store_thm("bindn_i4_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ⇒
    bindn_i4 n R1 x y ⇒ bindn_i4 n R2 x y``,
  rw[bindn_i4_def] >>
  match_mp_tac (MP_CANON FUNPOW_mono) >>
  simp[] >> metis_tac[bind_i4_mono] )
val _ = export_mono"bindn_i4_mono"

val bindn_i4_thm = store_thm("bindn_i4_thm",
  ``∀n k1 k2.
    bindn_i4 n R k1 k2 ⇔
    if k1 < n ∧ k2 < n then k1 = k2
    else n ≤ k1 ∧ n ≤ k2 ∧ R (k1-n) (k2-n)``,
  Induct>>simp[bindn_i4_def,arithmeticTheory.FUNPOW_SUC] >>
  Cases>>Cases>>simp[bind_i4_def,GSYM bindn_i4_def])

val (exp_i4_rules,exp_i4_ind,exp_i4_cases) = Hol_reln`
  (exp_i4 z1 z2 V e1 e2
   ⇒ exp_i4 z1 z2 V (Raise_i4 e1) (Raise_i4 e2)) ∧
  (exp_i4 z1 z2 V e11 e21 ∧ exp_i4 (z1+1) (z2+1) (bind_i4 V) e12 e22
   ⇒ exp_i4 z1 z2 V (Handle_i4 e11 e12) (Handle_i4 e21 e22)) ∧
  (exp_i4 z1 z2 V (Lit_i4 l) (Lit_i4 l)) ∧
  (LIST_REL (exp_i4 z1 z2 V) es1 es2
   ⇒ exp_i4 z1 z2 V (Con_i4 tag es1) (Con_i4 tag es2)) ∧
  ((k1 < z1 ∧ k2 < z2 ∧ V k1 k2) ∨ (z1 ≤ k1 ∧ z2 ≤ k2 ∧ (k1 = k2))
   ⇒ exp_i4 z1 z2 V (Var_local_i4 k1) (Var_local_i4 k2)) ∧
  (exp_i4 z1 z2 V (Var_global_i4 k) (Var_global_i4 k)) ∧
  (exp_i4 (z1+1) (z2+1) (bind_i4 V) e1 e2
   ⇒ exp_i4 z1 z2 V (Fun_i4 e1) (Fun_i4 e2)) ∧
  (exp_i4 z1 z2 V e1 e2
   ⇒ exp_i4 z1 z2 V (Uapp_i4 uop e1) (Uapp_i4 uop e2)) ∧
  (exp_i4 z1 z2 V e11 e21 ∧ exp_i4 z1 z2 V e12 e22
   ⇒ exp_i4 z1 z2 V (App_i4 op e11 e12) (App_i4 op e21 e22)) ∧
  (exp_i4 z1 z2 V e11 e21 ∧ exp_i4 z1 z2 V e12 e22 ∧ exp_i4 z1 z2 V e13 e23
   ⇒ exp_i4 z1 z2 V (If_i4 e11 e12 e13) (If_i4 e21 e22 e23)) ∧
  (exp_i4 z1 z2 V e11 e21 ∧ exp_i4 (z1+1) (z2+1) (bind_i4 V) e12 e22
   ⇒ exp_i4 z1 z2 V (Let_i4 e11 e12) (Let_i4 e21 e22)) ∧
  (exp_i4 z1 z2 V e11 e21 ∧ exp_i4 z1 z2 V e12 e22
   ⇒ exp_i4 z1 z2 V (Seq_i4 e11 e12) (Seq_i4 e21 e22)) ∧
  (LIST_REL (exp_i4 (z1+(SUC(LENGTH es1))) (z2+(SUC(LENGTH es2))) (bindn_i4 (SUC (LENGTH es1)) V)) es1 es2 ∧
   exp_i4 (z1+(LENGTH es1)) (z2+(LENGTH es2)) (bindn_i4 (LENGTH es1) V) e1 e2
   ⇒ exp_i4 z1 z2 V (Letrec_i4 es1 e1) (Letrec_i4 es2 e2)) ∧
  (exp_i4 z1 z2 V (Extend_global_i4 n) (Extend_global_i4 n))`

val exp_i4_refl = store_thm("exp_i4_refl",
  ``(∀e z V. (∀k. k < z ⇒ V k k) ⇒ exp_i4 z z V e e) ∧
    (∀es z V. (∀k. k < z ⇒ V k k) ⇒ LIST_REL (exp_i4 z z V) es es)``,
  ho_match_mp_tac(TypeBase.induction_of``:exp_i4``) >> rw[] >>
  TRY (first_x_assum match_mp_tac) >>
  rw[Once exp_i4_cases] >>
  TRY (first_x_assum match_mp_tac) >>
  TRY (metis_tac[]) >>
  TRY (Cases>>simp[bind_i4_def]>>NO_TAC) >>
  TRY (Cases_on`n < z` >>simp[] >> NO_TAC) >>
  rw[bindn_i4_thm] >>
  Cases_on`k < SUC (LENGTH es)` >> simp[] >>
  Cases_on`k < LENGTH es` >> simp[])

val exp_i4_mono = store_thm("exp_i4_mono",
  ``(∀x y. V1 x y ⇒ V2 x y) ⇒
    exp_i4 z1 z2 V1 e1 e2 ⇒
    exp_i4 z1 z2 V2 e1 e2``,
  strip_tac >> strip_tac >> last_x_assum mp_tac >>
  qid_spec_tac`V2` >> pop_assum mp_tac >>
  map_every qid_spec_tac[`e2`,`e1`,`V1`,`z2`,`z1`] >>
  ho_match_mp_tac exp_i4_ind >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once exp_i4_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_i4_mono >> rw[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_i4_cases] >>
    match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
    HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_i4_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_i4_mono >> rw[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_i4_cases] >>
    first_x_assum match_mp_tac >>
    match_mp_tac bind_i4_mono >> rw[] ) >>
  strip_tac >- ( rw[] >> rw[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >> rw[Once exp_i4_cases] >> TRY (
      match_mp_tac (MP_CANON (GEN_ALL EVERY2_mono)) >>
      HINT_EXISTS_TAC >> simp[] >> rw[] >>
      first_x_assum match_mp_tac >>
      match_mp_tac bindn_i4_mono >>
      simp[] ) >>
    first_x_assum match_mp_tac >>
    match_mp_tac bindn_i4_mono >>
    simp[] ) >>
  ( rw[] >> rw[Once exp_i4_cases] ))
val _ = export_mono"exp_i4_mono"

val exp_i4_lit = store_thm("exp_i4_lit",
  ``(exp_i4 z1 z2 V (Lit_i4 l) e2 ⇔ (e2 = Lit_i4 l)) ∧
    (exp_i4 z1 z2 V e1 (Lit_i4 l) ⇔ (e1 = Lit_i4 l))``,
  rw[Once exp_i4_cases] >>
  rw[Once exp_i4_cases] )
val _ = export_rewrites["exp_i4_lit"]

val bind_i4_O = store_thm("bind_i4_O",
  ``∀R1 R2. bind_i4 (R2 O R1) = bind_i4 R2 O bind_i4 R1``,
  rw[] >> simp[FUN_EQ_THM] >>
  simp[relationTheory.O_DEF] >>
  rw[bind_i4_thm,relationTheory.O_DEF,EQ_IMP_THM] >> rfs[] >- (
    qexists_tac`SUC y` >> simp[] ) >>
  qexists_tac`y-1` >> simp[])
val _ = export_rewrites["bind_i4_O"]

val bindn_i4_O = store_thm("bindn_i4_O",
  ``∀R1 R2 n. bindn_i4 n (R2 O R1) = bindn_i4 n R2 O bindn_i4 n R1``,
  rw[FUN_EQ_THM,bindn_i4_thm,relationTheory.O_DEF] >>
  rw[EQ_IMP_THM] >> simp[] >> fsrw_tac[ARITH_ss][] >>
  rev_full_simp_tac(srw_ss()++ARITH_ss)[]>>fsrw_tac[ARITH_ss][]
  >- (qexists_tac`y+n` >> simp[]) >>
  (qexists_tac`y-n` >> simp[]))
val _ = export_rewrites["bindn_i4_O"]

val LIST_REL_trans = store_thm("LIST_REL_trans",
  ``∀l1 l2 l3. (∀n. n < LENGTH l1 ∧ R (EL n l1) (EL n l2) ∧ R (EL n l2) (EL n l3) ⇒ R (EL n l1) (EL n l3)) ∧
      LIST_REL R l1 l2 ∧ LIST_REL R l2 l3 ⇒ LIST_REL R l1 l3``,
  Induct >> simp[] >> rw[] >> fs[] >> rw[] >- (
    first_x_assum(qspec_then`0`mp_tac)>>rw[] ) >>
  first_x_assum match_mp_tac >>
  qexists_tac`ys` >> rw[] >>
  first_x_assum(qspec_then`SUC n`mp_tac)>>simp[])

val exp_i4_trans = prove(
  ``∀z1 z2 V1 e1 e2. exp_i4 z1 z2 V1 e1 e2 ⇒
      ∀z3 V2 e3. exp_i4 z2 z3 V2 e2 e3 ⇒ exp_i4 z1 z3 (V2 O V1) e1 e3``,
   ho_match_mp_tac (theorem"exp_i4_strongind") >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) >>
     rfs[EVERY2_EVERY,EVERY_MEM] >>
     fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) >>
     simp[relationTheory.O_DEF] >> metis_tac[]) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ) >>
   strip_tac >- (
     rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) >>
     rfs[EVERY2_EVERY,EVERY_MEM] >>
     fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
   strip_tac >- ( rw[] >> pop_assum mp_tac >> ntac 2 (rw[Once exp_i4_cases]) ))
val exp_i4_trans = store_thm("exp_i4_trans",
  ``∀z1 z2 z3 V1 V2 V3 e1 e2 e3.
      exp_i4 z1 z2 V1 e1 e2 ∧
      exp_i4 z2 z3 V2 e2 e3 ∧
      (V3 = V2 O V1) ⇒
      exp_i4 z1 z3 V3 e1 e3``,
  metis_tac[exp_i4_trans])

val env_i4_def = Define`
  env_i4 R env1 env2 k1 k2 ⇔
    k1 < LENGTH env1 ∧ k2 < LENGTH env2 ∧ R (EL k1 env1) (EL k2 env2)`

val env_i4_mono = store_thm("env_i4_mono",
  ``(∀x y. R1 x y ⇒ R2 x y) ⇒
    env_i4 R1 env1 env2 k1 k2 ⇒
    env_i4 R2 env1 env2 k1 k2``,
  rw[env_i4_def])
val _ = export_mono"env_i4_mono"

val env_i4_cons = prove(
  ``R v1 v2 ∧
    bind_i4 (env_i4 R env1 env2) k1 k2
    ⇒ env_i4 R (v1::env1) (v2::env2) k1 k2``,
  Cases_on`k1`>>Cases_on`k2`>>rw[env_i4_def,bind_i4_def])

val (v_i4_rules,v_i4_ind,v_i4_cases) = Hol_reln`
  (v_i4 (Litv_i4 l) (Litv_i4 l)) ∧
  (LIST_REL v_i4 vs1 vs2
   ⇒ v_i4 (Conv_i4 tag vs1) (Conv_i4 tag vs2)) ∧
  (exp_i4 (SUC(LENGTH env1)) (SUC(LENGTH env2))
    (bind_i4 (env_i4 v_i4 env1 env2)) exp1 exp2
   ⇒ v_i4 (Closure_i4 env1 exp1) (Closure_i4 env2 exp2)) ∧
  (LIST_REL (exp_i4 (SUC(LENGTH funs1)+LENGTH env1) (SUC(LENGTH funs2)+LENGTH env2)
              (bindn_i4 (SUC (LENGTH funs1)) (env_i4 v_i4 env1 env2)))
            funs1 funs2
   ⇒ v_i4 (Recclosure_i4 env1 funs1 n) (Recclosure_i4 env2 funs2 n)) ∧
  (v_i4 (Loc_i4 n) (Loc_i4 n))`

val v_i4_lit = store_thm("v_i4_lit",
  ``(v_i4 (Litv_i4 l) v2 ⇔ (v2 = Litv_i4 l)) ∧
    (v_i4 v1 (Litv_i4 l) ⇔ (v1 = Litv_i4 l))``,
  rw[Once v_i4_cases] >> rw[Once v_i4_cases] )
val _ = export_rewrites["v_i4_lit"]

val v_i4_loc = store_thm("v_i4_loc",
  ``(v_i4 (Loc_i4 l) v2 ⇔ (v2 = Loc_i4 l)) ∧
    (v_i4 v1 (Loc_i4 l) ⇔ (v1 = Loc_i4 l))``,
  rw[Once v_i4_cases] >> rw[Once v_i4_cases] )
val _ = export_rewrites["v_i4_loc"]

val v_i4_refl = store_thm("v_i4_refl",
  ``∀v. v_i4 v v``,
  qsuff_tac`(∀v. v_i4 v v) ∧ (∀vs. LIST_REL v_i4 vs vs)`>-rw[]>>
  ho_match_mp_tac(TypeBase.induction_of``:v_i4``)>>
  rw[] >> rw[Once v_i4_cases] >>
  TRY (
    match_mp_tac (CONJUNCT1 exp_i4_refl) >>
    Cases>>simp[bind_i4_def,env_i4_def]>>
    fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] ) >>
  match_mp_tac (CONJUNCT2 exp_i4_refl) >>
  simp[bindn_i4_thm] >> rw[env_i4_def] >>
  qmatch_assum_rename_tac`k < LENGTH vs + SUC (LENGTH ls)`[] >>
  Cases_on`k < SUC (LENGTH ls)`>>simp[] >>
  fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
  simp[])
val _ = export_rewrites["v_i4_refl"]

val v_i4_trans = store_thm("v_i4_trans",
  ``∀v1 v2. v_i4 v1 v2 ⇒ ∀v3. v_i4 v2 v3 ⇒ v_i4 v1 v3``,
  ho_match_mp_tac (theorem"v_i4_strongind") >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_i4_cases,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    simp[Once v_i4_cases,PULL_EXISTS] >>
    match_mp_tac LIST_REL_trans >>
    qexists_tac`vs2` >> simp[] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once v_i4_cases,PULL_EXISTS] >> rw[] >>
    simp[Once v_i4_cases,PULL_EXISTS] >>
    qmatch_assum_abbrev_tac`exp_i4 z1 z2 V1 exp1 exp2` >>
    qmatch_assum_abbrev_tac`exp_i4 z2 z3 V2 exp2 exp3` >>
    match_mp_tac (MP_CANON (GEN_ALL exp_i4_mono)) >>
    qexists_tac`V2 O V1` >>
    conj_tac >- (
      simp[relationTheory.O_DEF,Abbr`V1`,Abbr`V2`] >>
      simp[bind_i4_thm,env_i4_def] >>
      rw[] >> fsrw_tac[ARITH_ss][] >> rfs[] ) >>
    match_mp_tac exp_i4_trans >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once v_i4_cases,PULL_EXISTS] >> rw[] >>
  simp[Once v_i4_cases,PULL_EXISTS] >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS,MEM_EL] >> rw[] >>
  res_tac >>
  qmatch_assum_abbrev_tac`exp_i4 z1 z2 V1 exp1 exp2` >>
  qmatch_assum_abbrev_tac`exp_i4 z2 z3 V2 exp2 exp3` >>
  match_mp_tac (MP_CANON (GEN_ALL exp_i4_mono)) >>
  qexists_tac`V2 O V1` >>
  conj_tac >- (
    simp[relationTheory.O_DEF,Abbr`V1`,Abbr`V2`] >>
    simp[bindn_i4_thm,env_i4_def] >>
    simp[arithmeticTheory.ADD1] >>
    rw[] >> fsrw_tac[ARITH_ss][] >>
    rev_full_simp_tac(srw_ss()++ARITH_ss)[] >>
    fsrw_tac[ARITH_ss][] ) >>
  metis_tac[exp_i4_trans])

val do_eq_i4_v_i4 = store_thm("do_eq_i4_v_i4",
  ``∀v1 v2. v_i4 v1 v2 ⇒ ∀v3 v4. v_i4 v3 v4 ⇒ do_eq_i4 v1 v3 = do_eq_i4 v2 v4``,
  ho_match_mp_tac v_i4_ind >>
  simp[do_eq_i4_def] >> rw[] >>
  Cases_on`v3`>>Cases_on`v4`>>fs[do_eq_i4_def] >>
  pop_assum mp_tac >> simp[Once v_i4_cases] >> rw[] >>
  imp_res_tac EVERY2_LENGTH >> fs[] >> rw[] >>
  ntac 2 (pop_assum kall_tac) >>
  qmatch_assum_rename_tac`LIST_REL v_i4 l1 l2`[] >>
  ntac 3 (pop_assum mp_tac) >>
  map_every qid_spec_tac[`l2`,`l1`,`vs2`,`vs1`] >>
  Induct >> simp[PULL_EXISTS] >>
  Cases_on`l1`>>Cases_on`l2`>>simp[do_eq_i4_def] >>
  rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  BasicProvers.CASE_TAC >> rw[] >>
  res_tac >> fs[])

val csg_i4_def = Define`
  csg_i4 R ((c1,s1),g1) (((c2,s2),g2):'a count_store_genv) ⇔
    c1 = c2 ∧ LIST_REL R s1 s2 ∧ LIST_REL (OPTION_REL R) g1 g2`

val csg_i4_refl = store_thm("csg_i4_refl",
  ``∀V x. (∀x. V x x) ⇒ csg_i4 V x x``,
  rpt gen_tac >> PairCases_on`x` >> simp[csg_i4_def] >>
  rw[] >> match_mp_tac EVERY2_refl >>
  rw[optionTheory.OPTREL_def] >>
  Cases_on`x` >> rw[])
val _ = export_rewrites["csg_i4_refl"]

val csg_i4_trans = store_thm("csg_i4_trans",
  ``∀V. (∀x y z. V x y ∧ V y z ⇒ V x z) ⇒ ∀x y z. csg_i4 V x y ∧ csg_i4 V y z ⇒ csg_i4 V x z``,
  rw[] >> map_every PairCases_on [`x`,`y`,`z`] >>
  fs[csg_i4_def] >>
  conj_tac >>
  match_mp_tac (MP_CANON EVERY2_trans)
  >- metis_tac[] >>
  simp[optionTheory.OPTREL_def] >>
  qexists_tac`y2` >> simp[] >>
  Cases >> Cases >> Cases >> simp[] >>
  metis_tac[])

val do_app_i4_v_i4 = store_thm("do_app_i4_v_i4",
  ``∀env s op v1 v2 env' s' v1' v2'.
      LIST_REL v_i4 s s' ∧
      v_i4 v1 v1' ∧ v_i4 v2 v2' ⇒
      OPTION_REL
        (λ(env1,s1,e1) (env2,s2,e2).
          LIST_REL v_i4 s1 s2 ∧
          exp_i4 (LENGTH env1) (LENGTH env2) (env_i4 v_i4 env1 env2) e1 e2)
        (do_app_i4 env s op v1 v2)
        (do_app_i4 env' s' op v1' v2')``,
  Cases_on`op`>>fs[do_app_i4_def] >- (
    Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
    Cases_on`v1`>>TRY(Cases_on`l:lit`)>>
    fs[optionTheory.OPTREL_def]>>
    TRY ( simp[Once v_i4_cases,PULL_EXISTS] >> NO_TAC ) >>
    TRY ( ntac 2 (simp[Once v_i4_cases,PULL_EXISTS]) >> NO_TAC ) >>
    BasicProvers.CASE_TAC >- ( ntac 2 (simp[Once exp_i4_cases])) >>
    simp[Once exp_i4_cases] )
  >- (
    Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
    Cases_on`v1`>>TRY(Cases_on`l:lit`)>>
    fs[optionTheory.OPTREL_def]>>
    TRY ( simp[Once v_i4_cases,PULL_EXISTS] >> NO_TAC ) >>
    TRY ( ntac 2 (simp[Once v_i4_cases,PULL_EXISTS]) >> NO_TAC ) >>
    simp[Once exp_i4_cases] )
  >- (
    rw[] >>
    BasicProvers.CASE_TAC >>
    imp_res_tac do_eq_i4_v_i4 >>
    fs[optionTheory.OPTREL_def] >>
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] )
  >- (
    Cases_on`v1`>>fs[optionTheory.OPTREL_def]>>
    simp[Once v_i4_cases,PULL_EXISTS] >> rw[] >- (
      match_mp_tac (MP_CANON (GEN_ALL exp_i4_mono)) >>
      HINT_EXISTS_TAC >>
      simp[bind_i4_thm,env_i4_def] >>
      Cases >> Cases >> simp[] ) >>
    qmatch_abbrev_tac`X ∨ Y` >>
    imp_res_tac EVERY2_LENGTH >>
    qsuff_tac`¬X ⇒ Y`>-metis_tac[]>>
    unabbrev_all_tac >> simp[] >>
    strip_tac >> simp[] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    match_mp_tac (MP_CANON (GEN_ALL exp_i4_mono)) >>
    simp[build_rec_env_i4_def] >> res_tac >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    qmatch_assum_abbrev_tac`exp_i4 z1 z2 V e1 e2` >>
    qexists_tac`V` >>
    simp[Abbr`V`,bindn_i4_thm] >>
    reverse conj_tac >- metis_tac[arithmeticTheory.ADD_SYM,arithmeticTheory.ADD_ASSOC] >>
    Cases >> Cases >> rw[env_i4_def] >> fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
    simp[Once v_i4_cases] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS,arithmeticTheory.ADD1,Abbr`z1`,Abbr`z2`] >>
    PROVE_TAC[arithmeticTheory.ADD_SYM,arithmeticTheory.ADD_ASSOC] )
  >- (
    Cases_on`v1`>>fs[optionTheory.OPTREL_def]>>
    TRY(simp[Once v_i4_cases,PULL_EXISTS]>>NO_TAC) >>
    rw[semanticPrimitivesTheory.store_assign_def] >>
    fs[EVERY2_EVERY,EVERY_MEM] >> simp[] >>
    rfs[MEM_ZIP,PULL_EXISTS,EL_LUPDATE] >>
    rw[] >> rw[Once exp_i4_cases]))

val evaluate_i4_exp_i4 = store_thm("evaluate_i4_exp_i4",
  ``(∀ck env1 s1 e1 res1. evaluate_i4 ck env1 s1 e1 res1 ⇒
       ∀env2 s2 e2.
         exp_i4 (LENGTH env1) (LENGTH env2) (env_i4 v_i4 env1 env2) e1 e2 ∧
         csg_i4 v_i4 s1 s2 ⇒
         ∃res2.
           evaluate_i4 ck env2 s2 e2 res2 ∧
           csg_i4 v_i4 (FST res1) (FST res2) ∧
           result_rel v_i4 v_i4 (SND res1) (SND res2)) ∧
    (∀ck env1 s1 es1 res1. evaluate_list_i4 ck env1 s1 es1 res1 ⇒
       ∀env2 s2 es2.
         LIST_REL (exp_i4 (LENGTH env1) (LENGTH env2) (env_i4 v_i4 env1 env2)) es1 es2 ∧
         csg_i4 v_i4 s1 s2 ⇒
         ∃res2.
           evaluate_list_i4 ck env2 s2 es2 res2 ∧
           csg_i4 v_i4 (FST res1) (FST res2) ∧
           result_rel (LIST_REL v_i4) v_i4 (SND res1) (SND res2))``,
  ho_match_mp_tac evaluate_i4_ind >>
  strip_tac >- (
    rw[Once exp_i4_cases] >>
    rw[Once v_i4_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >>
    rw[] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`v_i4 v1 v2`[] >>
    qmatch_assum_rename_tac`exp_i4 A B R e12 e22`["A","B","R"] >>
    qmatch_assum_abbrev_tac`csg_i4 v_i4 s3 s4` >>
    first_x_assum(qspecl_then[`v2::env2`,`s4`,`e22`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    discharge_hyps >- ( metis_tac[exp_i4_mono,env_i4_cons] ) >>
    rw[] >> Cases_on`res2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    rw[Once v_i4_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_i4_def] >>
    simp[] >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_i4_def] >>
    simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_i4_def] >>
    PairCases_on`s` >> fs[csg_i4_def] >> rw[] >>
    rfs[EVERY2_EVERY,EVERY_MEM,PULL_EXISTS] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[optionTheory.OPTREL_def] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_i4_def] >>
    PairCases_on`s` >> fs[csg_i4_def] >> rw[] >>
    rfs[EVERY2_EVERY,EVERY_MEM,PULL_EXISTS] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    first_assum(qspec_then`n`mp_tac) >>
    discharge_hyps >- simp[] >>
    rw[optionTheory.OPTREL_def] >>
    map_every qexists_tac[`s21`,`s22`] >>
    simp[MEM_ZIP,PULL_EXISTS] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    PairCases_on`s2` >> fs[env_i4_def] >>
    PairCases_on`s` >> fs[csg_i4_def] >> rw[] >>
    metis_tac[EVERY2_LENGTH] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once v_i4_cases,PULL_EXISTS] >>
    rw[Once evaluate_i4_cases,arithmeticTheory.ADD1] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`exp_i4 A B (env_i4 v_i4 env1 env2) e1 e2`["A","B"] >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s1 s4`[] >>
    first_x_assum(qspecl_then[`env2`,`s4`,`e2`]mp_tac) >>
    rw[EXISTS_PROD,PULL_EXISTS] >>
    fs[csg_i4_def] >> rw[] >>
    qmatch_assum_rename_tac`evaluate_i4 ck env2 s4 e2 (((c,s),g),Rval w)`[] >>
    CONV_TAC (RESORT_EXISTS_CONV List.rev) >>
    map_every qexists_tac[`g`,`s`,`w`] >> rw[] >>
    Cases_on`uop`>>
    fs[do_uapp_i4_def,semanticPrimitivesTheory.store_alloc_def,LET_THM] >> rw[] >>
    imp_res_tac EVERY2_LENGTH >>
    TRY ( rw[Once v_i4_cases] >> rw[] >> NO_TAC ) >>
    TRY ( match_mp_tac EVERY2_APPEND_suff >> rw[] >> NO_TAC ) >>
    TRY (
      fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] >>
      res_tac >> fs[] >> rw[MEM_ZIP] >> rw[optionTheory.OPTREL_def,EL_LUPDATE] >>
      rw[Once v_i4_cases] >> NO_TAC) >>
    qpat_assum`v_i4 v w`mp_tac >>
    Cases_on`v`>>fs[] >>
    simp[SIMP_RULE(srw_ss())[](Q.SPECL[`Conv_i4 X Y`,`z`]v_i4_cases)]>>
    rw[] >>
    fs[semanticPrimitivesTheory.store_lookup_def] >>
    rw[]>>fs[]>>rw[]>>fs[EVERY2_EVERY,EVERY_MEM]>>
    fs[MEM_ZIP,PULL_EXISTS] >> rfs[MEM_ZIP,PULL_EXISTS] >>
    rw[Once v_i4_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`exp_i4 A B (env_i4 v_i4 env1 env2) e1 e2`["A","B"] >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s1 s4`[] >>
    first_x_assum(qspecl_then[`env2`,`s4`,`e2`]mp_tac) >>
    rw[EXISTS_PROD,PULL_EXISTS] >>
    fs[csg_i4_def] >> rw[] >>
    qmatch_assum_rename_tac`evaluate_i4 ck env2 s4 e2 (((c,s),g),Rval w)`[] >>
    map_every qexists_tac[`s`,`g`] >>
    simp[] >> disj1_tac >>
    qexists_tac`w` >> simp[] >>
    fs[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,PULL_EXISTS] >>
    Cases_on`uop`>>
    fs[do_uapp_i4_def,LET_THM
      ,semanticPrimitivesTheory.store_alloc_def
      ,semanticPrimitivesTheory.store_lookup_def] >>
    rw[]>>fs[]>>TRY(
      res_tac >> fs[optionTheory.OPTREL_def] >> fs[] >> NO_TAC) >>
    qpat_assum`v_i4 v w`mp_tac >>
    Cases_on`v`>>fs[]>>simp[Once v_i4_cases]>>rw[]>>rw[]>>
    imp_res_tac EVERY2_LENGTH >> simp[] >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >> rw[] >>
    qmatch_assum_rename_tac`exp_i4 A B (env_i4 v_i4 env1 env2) e2 e22`["A","B"] >>
    qmatch_assum_rename_tac`v_i4 v1 v11`[] >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s11 (FST res11)`[] >>
    last_x_assum(qspecl_then[`env2`,`FST res11`,`e22`]mp_tac) >>
    rw[] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    CONV_TAC(RESORT_EXISTS_CONV(fn ls => tl ls @[hd ls])) >>
    qexists_tac`v11` >>
    qmatch_assum_rename_tac`v_i4 v2 v22`[] >>
    qexists_tac`v22` >>
    qspecl_then[`env1`,`s3`,`op`,`v1`,`v2`]mp_tac do_app_i4_v_i4 >>
    simp[optionTheory.OPTREL_def] >>
    disch_then(qspecl_then[`env2`,`SND(FST(FST res2))`,`v11`,`v22`]mp_tac) >>
    discharge_hyps >- (
      PairCases_on`res2`>>fs[csg_i4_def] ) >>
    disch_then(qx_choose_then`res5`strip_assume_tac) >>
    PairCases_on`res5`>>fs[] >>
    map_every qexists_tac[`res50`,`res52`,`FST res11`,`SND(FST(FST res2))`,`FST(FST(FST res2))`,`res51`] >>
    Cases_on`res11`>>fs[] >>
    qexists_tac`SND (FST res2)` >>
    PairCases_on`res2`>>fs[] >>
    Q.PAT_ABBREV_TAC`s50:v_i4 count_store_genv = X` >>
    first_x_assum(qspecl_then[`res50`,`s50`,`res52`]mp_tac) >>
    simp[] >>
    discharge_hyps >- ( fs[Abbr`s50`,csg_i4_def] ) >>
    disch_then(qx_choose_then`res6`strip_assume_tac) >>
    qexists_tac`res6`>>simp[] >>
    fs[csg_i4_def] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >> rw[] >>
    qmatch_assum_rename_tac`exp_i4 A B (env_i4 v_i4 env1 env2) e2 e22`["A","B"] >>
    qmatch_assum_rename_tac`v_i4 v1 v11`[] >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s11 (FST res11)`[] >>
    last_x_assum(qspecl_then[`env2`,`FST res11`,`e22`]mp_tac) >>
    rw[] >>
    fs[do_app_i4_def] >>
    Cases_on`v1`>>fs[]>>rw[]>>
    qexists_tac`FST res2,Rerr Rtimeout_error` >>
    simp[] >>
    disj2_tac >> disj1_tac >>
    PairCases_on`res2` >>
    fs[csg_i4_def] >> rw[] >>
    qexists_tac`v11` >>
    qmatch_assum_rename_tac`v_i4 v2 v4`[] >>
    qexists_tac`v4` >>
    qpat_assum`v_i4 X v11`mp_tac >>
    simp[Once v_i4_cases] >> rw[] >>
    rw[] >>
    PairCases_on`res11`>>fs[] >>
    imp_res_tac EVERY2_LENGTH >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >> rw[] >>
    qmatch_assum_rename_tac`exp_i4 A B (env_i4 v_i4 env1 env2) e2 e22`["A","B"] >>
    qmatch_assum_rename_tac`v_i4 v1 v11`[] >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s11 (FST res11)`[] >>
    last_x_assum(qspecl_then[`env2`,`FST res11`,`e22`]mp_tac) >>
    rw[] >>
    qexists_tac`FST res2,Rerr Rtype_error` >>
    simp[] >>
    disj2_tac >> disj1_tac >>
    PairCases_on`res2` >>
    fs[csg_i4_def] >> rw[] >>
    qexists_tac`v11` >>
    qmatch_assum_rename_tac`v_i4 v2 v4`[] >>
    qexists_tac`v4` >>
    Cases_on`res11`>>fs[]>>
    qmatch_assum_rename_tac`csg_i4 v_i4 s11 s12`[] >>
    qexists_tac`s12` >> rw[] >>
    Cases_on`op=Equality`>-(
      fs[do_app_i4_def] >>
      imp_res_tac do_eq_i4_v_i4 >>
      fs[] >>
      BasicProvers.CASE_TAC >> fs[] ) >>
    rpt(qpat_assum`v_i4 X Y`mp_tac) >>
    Cases_on`op`>>TRY(Cases_on`o':opn`)>>
    Cases_on`v1`>>TRY(Cases_on`l:lit`)>>
    Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
    fs[do_app_i4_def]>>
    simp[Once v_i4_cases]>>
    simp[Once v_i4_cases]>>
    rw[]>>rw[]>>fs[semanticPrimitivesTheory.store_assign_def]>>
    imp_res_tac EVERY2_LENGTH >> fs[] >> rfs[] >>
    rw[] >> fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`do_if_i4 v e2 e3 = SOME en`[] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >>
    simp[] >> disch_then(qx_choose_then`res2`strip_assume_tac) >>
    Cases_on`∃b. v = Litv_i4 (Bool b)`>>fs[do_if_i4_def]>>fs[]>>rw[]>>
    last_x_assum(qspecl_then[`env2`,`FST res2`,`if b then e22 else e23`]mp_tac) >>
    discharge_hyps >- (rw[]>>fs[]>>rw[]) >>
    disch_then(qx_choose_then`res3`strip_assume_tac) >>
    qexists_tac`res3` >> simp[] >>
    disj1_tac >>
    qexists_tac`Litv_i4 (Bool b)` >> simp[] >>
    Cases_on`res2` >> rw[] >> fs[] >> rw[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    simp[Once EXISTS_PROD,PULL_EXISTS] >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s1 s4`[] >>
    last_x_assum(qspecl_then[`env2`,`s4`,`e21`]mp_tac) >>
    simp[] >> disch_then(qx_choose_then`res2`strip_assume_tac) >>
    qexists_tac`FST res2` >> simp[] >>
    disj2_tac >> disj1_tac >>
    Cases_on`res2`>>fs[] >>
    HINT_EXISTS_TAC >>
    fs[do_if_i4_def] >>
    rw[]>>fs[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    last_x_assum(qspecl_then[`env2`,`s2`,`e21`]mp_tac) >>
    rw[] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`v_i4 v1 v2`[] >>
    qmatch_assum_rename_tac`exp_i4 A B R e12 e22`["A","B","R"] >>
    qmatch_assum_abbrev_tac`csg_i4 v_i4 s3 s4` >>
    first_x_assum(qspecl_then[`v2::env2`,`s4`,`e22`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    discharge_hyps >- ( metis_tac[exp_i4_mono,env_i4_cons] ) >>
    rw[] >> Cases_on`res2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    qmatch_assum_rename_tac`exp_i4 A B R e1 e2`["A","B","R"] >>
    first_x_assum(qspecl_then[`build_rec_env_i4 es2 env2 ++ env2`,`s2`,`e2`]mp_tac) >>
    simp[] >>
    discharge_hyps >- (
      match_mp_tac (MP_CANON (GEN_ALL exp_i4_mono)) >>
      simp[env_i4_def,build_rec_env_i4_def] >>
      HINT_EXISTS_TAC >> simp[bindn_i4_thm,GSYM bindn_i4_def] >>
      imp_res_tac EVERY2_LENGTH >>
      rw[] >> simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
      fsrw_tac[ARITH_ss][env_i4_def] >>
      simp[Once v_i4_cases]) >>
    simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rw[Once exp_i4_cases] >>
    rw[Once evaluate_i4_cases,PULL_EXISTS] >>
    PairCases_on`s` >>
    PairCases_on`s2`>>fs[csg_i4_def] >>
    match_mp_tac EVERY2_APPEND_suff >>
    simp[] >> simp[EVERY2_EVERY,EVERY_MEM] >>
    simp[MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] ) >>
  strip_tac >- ( rw[] >> rw[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    Cases_on`es2`>>simp[] >>
    simp[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    Cases_on`es2`>>simp[] >>
    simp[Once evaluate_i4_cases,PULL_EXISTS] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  Cases_on`es2`>>simp[] >>
  simp[Once evaluate_i4_cases,PULL_EXISTS] >>
  fs[EXISTS_PROD,PULL_EXISTS] >>
  metis_tac[] )

val csg_v_i4_trans =
  csg_i4_trans
  |> Q.ISPEC`v_i4`
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[v_i4_trans])

val result_rel_v_v_i4_trans =
  result_rel_trans
  |> Q.GENL[`R2`,`R1`]
  |> Q.ISPECL[`v_i4`,`v_i4`]
  |> UNDISCH_ALL
  |> prove_hyps_by(metis_tac[v_i4_trans])

val LIST_REL_v_i4_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`v_i4`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[v_i4_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l3`,`l2`,`l1`]

val OPTREL_trans = store_thm("OPTREL_trans",
  ``∀R x y z. (∀a b c. x = SOME a ∧ y = SOME b ∧ z = SOME c ∧ R a b ∧ R b c ⇒ R a c)
    ∧ OPTREL R x y ∧ OPTREL R y z ⇒ OPTREL R x z``,
  rw[optionTheory.OPTREL_def])

val LIST_REL_OPTREL_v_i4_trans =
  LIST_REL_trans
  |> Q.GEN`R`
  |> Q.ISPEC`OPTREL v_i4`
  |> SPEC_ALL
  |> SIMP_RULE (srw_ss())[GSYM AND_IMP_INTRO]
  |> UNDISCH
  |> prove_hyps_by(metis_tac[OPTREL_trans,v_i4_trans])
  |> SIMP_RULE std_ss [AND_IMP_INTRO]
  |> Q.GENL[`l3`,`l2`,`l1`]

val exc_rel_v_i4_trans =
  exc_rel_trans
  |> Q.GEN`R`
  |> Q.ISPEC`v_i4`
  |> UNDISCH
  |> prove_hyps_by(metis_tac[v_i4_trans])

val LIST_REL_APPEND_SING = store_thm("LIST_REL_APPEND_SING",
  ``LIST_REL R (l1 ++ [x1]) (l2 ++ [x2]) ⇔
    LIST_REL R l1 l2 ∧ R x1 x2``,
  rw[EQ_IMP_THM] >> TRY (
    match_mp_tac EVERY2_APPEND_suff >> simp[]) >>
  imp_res_tac EVERY2_APPEND >> fs[])
val _ = export_rewrites["LIST_REL_APPEND_SING"]

val bvs_V_def = Define`
  bvs_V bvs1 bvs2 V ⇔
  ∀x k1 k2.
      find_index (SOME x) bvs1 0 = SOME k1 ∧
      find_index (SOME x) bvs2 0 = SOME k2
      ⇒ V k1 k2`

val bind_i4_bvs_V_NONE = prove(
  ``∀bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (NONE::bvs1) (NONE::bvs2) (bind_i4 V)``,
  rw[bvs_V_def,bind_i4_thm] >>
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

val bind_i4_bvs_V_SOME = prove(
  ``∀bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (SOME x::bvs1) (SOME x::bvs2) (bind_i4 V)``,
  rw[bvs_V_def,bind_i4_thm] >>
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

val bind_i4_bvs_V = store_thm("bind_i4_bvs_V",
  ``∀x bvs1 bvs2 V.
    bvs_V bvs1 bvs2 V ⇒
    bvs_V (x::bvs1) (x::bvs2) (bind_i4 V)``,
  Cases >> metis_tac[bind_i4_bvs_V_NONE,bind_i4_bvs_V_SOME])

val bindn_i4_bvs_V = store_thm("bindn_i4_bvs_V",
  ``∀ls n bvs1 bvs2 V.
     bvs_V bvs1 bvs2 V ∧ n = LENGTH ls ⇒
     bvs_V (ls++bvs1) (ls++bvs2) (bindn_i4 n V)``,
  Induct >> simp[bindn_i4_def,arithmeticTheory.FUNPOW_SUC] >>
  metis_tac[bind_i4_bvs_V,bindn_i4_def])

val exp_i4_sIf = store_thm("exp_i4_sIf",
  ``exp_i4 z1 z2 V (If_i4 e1 e2 e3) (If_i4 f1 f2 f3) ⇒
    exp_i4 z1 z2 V (sIf_i4 e1 e2 e3) (sIf_i4 f1 f2 f3)``,
  rw[sIf_i4_def] >> pop_assum mp_tac >>
  simp[Once exp_i4_cases] >> rw[] >>
  Cases_on`e1 = Lit_i4 (Bool T)`>>rw[]>-fs[]>>
  Cases_on`e1 = Lit_i4 (Bool F)`>>rw[]>-fs[]>>
  qmatch_abbrev_tac`exp_i4 z1 z2 V ea eb` >>
  `ea = If_i4 e1 e2 e3` by (
    Cases_on`e1`>>fs[Abbr`ea`]>>
    BasicProvers.CASE_TAC>>rw[] ) >>
  Cases_on`f1 = Lit_i4 (Bool T)`>>rw[]>-fs[]>>
  Cases_on`f1 = Lit_i4 (Bool F)`>>rw[]>-fs[]>>
  `eb = If_i4 f1 f2 f3` by (
    Cases_on`f1`>>fs[Abbr`eb`]>>
    BasicProvers.CASE_TAC>>rw[] ) >>
  simp[Once exp_i4_cases])

val fo_list_i4_EVERY = store_thm("fo_list_i4_EVERY",
  ``∀ls. fo_list_i4 ls ⇔ EVERY fo_i4 ls``,
  Induct >> simp[fo_i4_def])
val _ = export_rewrites["fo_list_i4_EVERY"]

val pure_list_i4_EVERY = store_thm("pure_list_i4_EVERY",
  ``∀ls. pure_list_i4 ls ⇔ EVERY pure_i4 ls``,
  Induct >> simp[pure_i4_def])
val _ = export_rewrites["pure_list_i4_EVERY"]

val exp_i4_fo = store_thm("exp_i4_fo",
  ``∀z1 z2 V e1 e2. exp_i4 z1 z2 V e1 e2 ⇒
      (fo_i4 e1 ⇔ fo_i4 e2)``,
  ho_match_mp_tac exp_i4_ind >>
  simp[fo_i4_def] >>
  rw[EVERY_MEM,EVERY2_EVERY,EQ_IMP_THM] >>
  rfs[MEM_ZIP,PULL_EXISTS] >>
  rfs[MEM_EL,PULL_EXISTS] )

val exp_i4_pure = store_thm("exp_i4_pure",
  ``∀z1 z2 V e1 e2. exp_i4 z1 z2 V e1 e2 ⇒
    (pure_i4 e1 ⇔ pure_i4 e2)``,
  ho_match_mp_tac (theorem"exp_i4_strongind") >>
  simp[pure_i4_def] >>
  rw[EVERY_MEM,EVERY2_EVERY,EQ_IMP_THM] >>
  rfs[MEM_ZIP,PULL_EXISTS] >>
  rfs[MEM_EL,PULL_EXISTS] >>
  fs[] >> imp_res_tac exp_i4_fo >> rw[])

val bind_i4_inv = store_thm("bind_i4_inv",
  ``∀V. bind_i4 (inv V) = inv (bind_i4 V)``,
  rw[FUN_EQ_THM,bind_i4_thm,relationTheory.inv_DEF] >>
  rw[])
val _ = export_rewrites["bind_i4_inv"]

val bindn_i4_inv = store_thm("bindn_i4_inv",
  ``∀V n. bindn_i4 n (inv V) = inv (bindn_i4 n V)``,
  rw[FUN_EQ_THM,bindn_i4_thm,relationTheory.inv_DEF] >>
  rw[] >> simp[] >> fs[] >> simp[])
val _ = export_rewrites["bindn_i4_inv"]

val exp_i4_sym = store_thm("exp_i4_sym",
  ``∀z1 z2 V e1 e2. exp_i4 z1 z2 V e1 e2 ⇒ exp_i4 z2 z1 (inv V) e2 e1``,
  ho_match_mp_tac exp_i4_ind >> rw[] >>
  simp[Once exp_i4_cases] >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS,relationTheory.inv_DEF] )

val ground_list_i4_EVERY = store_thm("ground_list_i4_EVERY",
  ``∀n ls. ground_list_i4 n ls ⇔ EVERY (ground_i4 n) ls``,
  gen_tac >> Induct >> simp[])
val _ = export_rewrites["ground_list_i4_EVERY"]

val exp_i4_imp_ground = store_thm("exp_i4_imp_ground",
  ``∀z1 z2 V e1 e2. exp_i4 z1 z2 V e1 e2 ⇒
      ∀n. (∀k1 k2. k1 ≤ n ⇒ (V k1 k2 ⇔ (k1 = k2))) ∧ ground_i4 n e1 ⇒ ground_i4 n e2``,
  ho_match_mp_tac exp_i4_ind >>
  simp[] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    simp[bind_i4_thm] >>
    rw[] >> simp[] >> NO_TAC) >>
  TRY (DECIDE_TAC) >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS] >>
  rfs[MEM_EL,PULL_EXISTS] >>
  fs[arithmeticTheory.LESS_OR_EQ] >>
  res_tac >> rw[])

val bindn_i4_0 = store_thm("bindn_i4_0",
  ``∀V. bindn_i4 0 V = V``,
  rw[bindn_i4_def])
val _ = export_rewrites["bindn_i4_0"]

val bind_bindn_i4 = store_thm("bind_bindn_i4",
  ``(bind_i4 (bindn_i4 n V) = bindn_i4 (SUC n) V) ∧
    (bindn_i4 n (bind_i4 V) = bindn_i4 (SUC n) V)``,
  conj_tac >- simp[bindn_i4_def,arithmeticTheory.FUNPOW_SUC] >>
  simp[bindn_i4_def,arithmeticTheory.FUNPOW])
val _ = export_rewrites["bind_bindn_i4"]

val exp_i4_unbind = store_thm("exp_i4_unbind",
  ``∀z1 z2 V e1 e2. exp_i4 z1 z2 V e1 e2 ⇒
      ∀k n m U.
        V = bindn_i4 n U ∧ n ≤ z1 ∧ n ≤ z2 ∧
        ground_i4 k e1 ∧ ground_i4 k e2 ∧
        k ≤ n-m ∧ m ≤ n
        ⇒
        exp_i4 (z1-m) (z2-m) (bindn_i4 (n-m) U) e1 e2``,
  ho_match_mp_tac exp_i4_ind >>
  simp[] >> rw[] >>
  simp[Once exp_i4_cases] >> fs[] >>
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
  qpat_assum`bindn_i4 n U k1 k2`mp_tac >>
  simp[bindn_i4_thm] >> rw[])

val exp_i4_sLet = store_thm("exp_i4_sLet",
  ``exp_i4 z1 z2 V (Let_i4 e1 e2) (Let_i4 f1 f2) ⇒
    exp_i4 z1 z2 V (sLet_i4 e1 e2) (sLet_i4 f1 f2)``,
  rw[sLet_i4_thm] >>
  qpat_assum`exp_i4 z1 z2 V X Y`mp_tac >>
  simp[Once exp_i4_cases] >> strip_tac >>
  TRY (
    qpat_assum`exp_i4 Z1 Z2 VV (Var_local_i4 A) B`mp_tac >>
    simp[Once exp_i4_cases] >> rw[bind_i4_thm] ) >>
  TRY (
    qpat_assum`exp_i4 Z1 Z2 VV B (Var_local_i4 A)`mp_tac >>
    simp[Once exp_i4_cases] >> rw[bind_i4_thm] ) >>
  imp_res_tac exp_i4_pure >> fs[] >>
  TRY (
    imp_res_tac exp_i4_sym >>
    imp_res_tac exp_i4_imp_ground >>
    qpat_assum`P ⇒ Q`mp_tac >>
    discharge_hyps >- (
      simp[bind_i4_thm,relationTheory.inv_DEF] ) >>
    rw[] >> NO_TAC) >>
  simp[Once(SIMP_RULE(srw_ss())[](Q.SPECL[`z1`,`z2`,`V`,`Seq_i4 e1 e2`]exp_i4_cases))] >>
  qspecl_then[`z1+1`,`z2+1`,`bind_i4 V`,`e2`,`f2`]mp_tac exp_i4_unbind >> simp[] >>
  disch_then(qspecl_then[`0`,`1`,`1`,`V`]mp_tac) >>
  simp[bindn_i4_def] )

val ground_i4_sIf = store_thm("ground_i4_sIf",
  ``ground_i4 n (If_i4 e1 e2 e3) ⇒
    ground_i4 n (sIf_i4 e1 e2 e3)``,
  rw[sIf_i4_def] >>
  Cases_on`e1`>> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >> rw[])

val ground_i4_inc = store_thm("ground_i4_inc",
  ``(∀e n. ground_i4 n e ⇒ ∀m. n ≤ m ⇒ ground_i4 m e) ∧
    (∀es n. ground_list_i4 n es ⇒ ∀m. n ≤ m ⇒ ground_list_i4 m es)``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_i4``)) >>
  simp[] >> rw[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[arithmeticTheory.LE_ADD_RCANCEL])

val ground_i4_sLet = store_thm("ground_i4_sLet",
  ``ground_i4 n (Let_i4 e1 e2) ⇒
    ground_i4 n (sLet_i4 e1 e2)``,
  rw[sLet_i4_thm] >>
  match_mp_tac(MP_CANON(CONJUNCT1 ground_i4_inc))>>
  qexists_tac`0`>>simp[])

val ground_i4_Let_Els = store_thm("ground_i4_Let_Els",
  ``∀k m n e.
    ground_i4 (n+k) e ∧ m < n ⇒
    ground_i4 n (Let_Els_i4 m k e)``,
  Induct >> simp[Let_Els_i4_def] >>
  rw[] >>
  match_mp_tac ground_i4_sLet >>
  simp[] >>
  first_x_assum match_mp_tac >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1])

val pat_to_i4_ground = store_thm("pat_to_i4_ground",
  ``(∀p. ground_i4 1 (pat_to_i4 p)) ∧
    (∀n ps. ground_i4 (n + LENGTH ps) (pats_to_i4 n ps))``,
  ho_match_mp_tac pat_to_i4_ind >>
  simp[pat_to_i4_def] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac ground_i4_sIf >>
    simp[] >>
    match_mp_tac ground_i4_Let_Els >>
    simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 ground_i4_inc)) >>
    HINT_EXISTS_TAC >> simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    match_mp_tac ground_i4_sLet >> simp[] >>
    match_mp_tac (MP_CANON(CONJUNCT1 ground_i4_inc)) >>
    qexists_tac`1`>>simp[] ) >>
  rpt gen_tac >> strip_tac >>
  match_mp_tac ground_i4_sIf >> simp[] >>
  fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
  match_mp_tac ground_i4_sLet >> simp[] >>
  match_mp_tac (MP_CANON(CONJUNCT1 ground_i4_inc)) >>
  HINT_EXISTS_TAC >> simp[])

val ground_exp_i4_refl = store_thm("ground_exp_i4_refl",
  ``(∀e n. ground_i4 n e ⇒
       ∀z1 z2 V. n ≤ z1 ∧ n ≤ z2 ⇒ exp_i4 z1 z2 (bindn_i4 n V) e e) ∧
    (∀es n. ground_list_i4 n es ⇒
       ∀z1 z2 V. n ≤ z1 ∧ n ≤ z2 ⇒ EVERY2 (exp_i4 z1 z2 (bindn_i4 n V)) es es)``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_i4``)) >>
  simp[] >> rw[] >>
  simp[Once exp_i4_cases] >> TRY (
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[arithmeticTheory.ADD1] >>
    NO_TAC) >>
  simp[bindn_i4_thm])

(*
val Let_Els_i4_exp_i4 = store_thm("Let_Els_i4_exp_i4",
  ``∀k n e1 e2 z1 z2 V.
      exp_i4 (z1+n) (z2+n) (bindn_i4 n V) e1 e2 ⇒
      exp_i4 z1 z2 V (Let_Els_i4 n k e1) (Let_Els_i4 n k e2)``,
  Induct >> simp[Let_Els_i4_def] >- (
    rpt gen_tac >> strip_tac >>
    qspecl_then[`z1`,`z2`,`V`,`e1`,`e2`]mp_tac exp_i4_unbind >>
    simp[]
    exp_i4_imp_ground
    bindn_i4_def
    exps
  conj_tac >- (
    Cases >> simp[Let_Els_i4_def] >- simp[bindn_i4_def] >>
    rpt gen_tac >> strip_tac >>
    match_mp_tac exp_i4_sLet >>
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>

    simp[bindn_i4_thm]

val pat_to_i4_exp_i4_refl = store_thm("pat_to_i4_exp_i4_refl",
  ``(∀p z1 z2 V. exp_i4 (SUC z1) (SUC z2) (bind_i4 V) (pat_to_i4 p) (pat_to_i4 p)) ∧
    (∀n ps z1 z2 V. exp_i4 (z1+n) (z2+n) (bindn_i4 n V) (pats_to_i4 n ps) (pats_to_i4 n ps))``,
  ho_match_mp_tac pat_to_i4_ind >>
  simp[pat_to_i4_def] >>
  strip_tac >- (
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>
    simp[bind_i4_thm] ) >>
  strip_tac >- (
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>
    simp[bind_i4_thm] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    match_mp_tac exp_i4_sIf >>
    simp[Once exp_i4_cases] >>
    conj_tac >- (
      simp[Once exp_i4_cases] >>
      simp[Once exp_i4_cases] >>
      simp[bind_i4_thm] ) >>
    Let_Els_i4_correct
*)

val row_to_i4_acc = store_thm("row_to_i4_acc",
  ``(∀Nbvs p bvs1 N. Nbvs = N::bvs1 ⇒
       ∀bvs2 r1 n1 f1 r2 n2 f2.
         row_to_i4 (N::bvs1) p = (r1,n1,f1) ∧
         row_to_i4 (N::bvs2) p = (r2,n2,f2) ⇒
         n1 = n2 ∧ f1 = f2 ∧
         ∃ls. r1 = ls ++ bvs1 ∧
              r2 = ls ++ bvs2 ∧
              LENGTH ls = SUC n1) ∧
    (∀bvsk0 n k ps bvsk N bvs1.
        bvsk0 = bvsk ++ (N::bvs1) ∧ LENGTH bvsk = n ⇒
      ∀bvs2 r1 n1 f1 r2 n2 f2.
        cols_to_i4 (bvsk++(N::bvs1)) n k ps = (r1,n1,f1) ∧
        cols_to_i4 (bvsk++(N::bvs2)) n k ps = (r2,n2,f2) ⇒
        n1 = n2 ∧ f1 = f2 ∧
        ∃ls. r1 = ls ++ bvsk ++ (N::bvs1) ∧
             r2 = ls ++ bvsk ++ (N::bvs2) ∧
             LENGTH ls = n1)``,
  ho_match_mp_tac row_to_i4_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rw[row_to_i4_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rw[row_to_i4_def] >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> simp[LENGTH_NIL] >>
    strip_tac >> rpt gen_tac >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp_tac std_ss [row_to_i4_def] >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspec_then`bvs2`mp_tac) >>
    simp[] >> strip_tac >>
    qexists_tac`ls++[N]` >>
    simp[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp_tac std_ss [row_to_i4_def] >>
    simp[] >>
    `∃r1 n1 f1. row_to_i4 (NONE::N::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    fs[] >> rpt gen_tac >>
    `∃r2 n2 f2. row_to_i4 (NONE::N::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    fs[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum(qspec_then`N::bvs2`mp_tac) >>
    simp[] >> rw[] >> simp[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >> simp[] >> strip_tac >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[row_to_i4_def] ) >>
  strip_tac >- simp[row_to_i4_def] >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >>
  simp_tac std_ss [row_to_i4_def] >>
  `∃r01 n01 f01. row_to_i4 (NONE::(bvsk ++ (N::bvs1))) p = (r01,n01,f01)` by simp[GSYM EXISTS_PROD] >>
  `∃r02 n02 f02. row_to_i4 (NONE::(bvsk ++ (N::bvs2))) p = (r02,n02,f02)` by simp[GSYM EXISTS_PROD] >>
  ntac 2 (pop_assum mp_tac) >>
  simp_tac (srw_ss()) [LET_THM] >>
  `∃r11 n11 f11. cols_to_i4 r01 (LENGTH bvsk + 1 + n01) (k+1) ps = (r11,n11,f11)` by simp[GSYM EXISTS_PROD] >>
  `∃r12 n12 f12. cols_to_i4 r02 (LENGTH bvsk + 1 + n02) (k+1) ps = (r12,n12,f12)` by simp[GSYM EXISTS_PROD] >>
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

val row_to_i4_nil = store_thm("row_to_i4_nil",
  ``row_to_i4 (N::bvs1) p = let (r1,n1,f1) = row_to_i4 [N] p in (r1++bvs1,n1,f1)``,
  rw[] >>
  qspecl_then[`[N]`,`p`]mp_tac (CONJUNCT1 row_to_i4_acc) >>
  simp[] >>
  disch_then(qspec_then`bvs1`mp_tac) >>
  `∃x y z. row_to_i4 (N::bvs1) p = (x,y,z)` by simp[GSYM EXISTS_PROD] >>
  simp[])

val row_to_i4_shift = store_thm("row_to_i4_shift",
  ``(∀bvs p bvs1 n1 f z1 z2 V e1 e2.
       row_to_i4 bvs p = (bvs1,n1,f) ∧ 0 < z1 ∧ 0 < z2 ∧ V 0 0 ∧ bvs ≠ [] ∧
       exp_i4 (z1 + n1) (z2 + n1) (bindn_i4 n1 V) e1 e2
       ⇒
       exp_i4 z1 z2 V (f e1) (f e2)) ∧
    (∀bvs n k ps bvs1 n1 f z1 z2 V e1 e2.
       cols_to_i4 bvs n k ps = (bvs1,n1,f) ∧ bvs ≠ [] ∧ ps ≠ [] ∧
       n < z1 ∧ n < z2 ∧ V n n ∧
       exp_i4 (z1 + n1) (z2 + n1) (bindn_i4 (n1) V) e1 e2
       ⇒
       exp_i4 z1 z2 V (f e1) (f e2))``,
  ho_match_mp_tac row_to_i4_ind >>
  simp[row_to_i4_def] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    `∃bvs1 n1 f. cols_to_i4 bvs 0 0 ps = (bvs1,n1,f)` by simp[GSYM EXISTS_PROD] >>
    Cases_on`ps`>>fs[row_to_i4_def] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    `∃bvs1 n f. row_to_i4 (NONE::bvs) p = (bvs1,n,f)` by simp[GSYM EXISTS_PROD] >>
    fs[] >>
    rpt gen_tac >> strip_tac >>
    match_mp_tac exp_i4_sLet >>
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>
    simp[Once exp_i4_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    simp[bind_i4_thm] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `∃bvs0 n0 f0. row_to_i4 (NONE::bvs) p = (bvs0,n0,f0)` by simp[GSYM EXISTS_PROD] >>
  fs[] >>
  `∃bvs2 n2 f2. cols_to_i4 bvs0 (n0+n+1) (k+1) ps = (bvs2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
  fsrw_tac[ARITH_ss][] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[] >>
  match_mp_tac exp_i4_sLet >>
  simp[Once exp_i4_cases] >>
  simp[Once exp_i4_cases] >>
  simp[Once exp_i4_cases] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[bind_i4_thm] >>
  Cases_on`ps=[]`>>fs[row_to_i4_def] >- (
    rw[] >> fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] ) >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  qspecl_then[`NONE::bvs`,`p`]mp_tac(CONJUNCT1 row_to_i4_acc) >>
  simp[] >> disch_then(qspec_then`bvs`mp_tac) >> simp[] >>
  strip_tac >> Cases_on`bvs0`>>fs[] >>
  conj_tac >- simp[bindn_i4_thm,arithmeticTheory.ADD1] >>
  fs[bindn_i4_def,GSYM arithmeticTheory.FUNPOW_ADD,arithmeticTheory.ADD1] >>
  fsrw_tac[ARITH_ss][])

val exp_to_i4_shift = store_thm("exp_to_i4_shift",
  ``(∀bvs1 e z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = LENGTH bvs1) ∧ (z2 = LENGTH bvs2) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       exp_i4 z1 z2 V (exp_to_i4 bvs1 e) (exp_to_i4 bvs2 e)) ∧
    (∀bvs1 es z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = LENGTH bvs1) ∧ (z2 = LENGTH bvs2) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       LIST_REL (exp_i4 z1 z2 V) (exps_to_i4 bvs1 es) (exps_to_i4 bvs2 es)) ∧
    (∀bvs1 funs z1 z2 bvs2 V.
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = SUC(LENGTH bvs1)) ∧
       (z2 = SUC(LENGTH bvs2)) ∧
       (bvs_V bvs1 bvs2 V)
       ⇒
       LIST_REL (exp_i4 z1 z2 (bind_i4 V))
         (funs_to_i4 bvs1 funs) (funs_to_i4 bvs2 funs)) ∧
    (∀Nbvs1 pes bvs1 z1 z2 bvs2 V.
       (Nbvs1 = NONE::bvs1) ∧
       (set (FILTER IS_SOME bvs1) = set (FILTER IS_SOME bvs2)) ∧
       (z1 = SUC(LENGTH bvs1)) ∧ (z2 = SUC(LENGTH bvs2)) ∧ (bvs_V bvs1 bvs2 V)
       ⇒
       exp_i4 z1 z2 (bind_i4 V) (pes_to_i4 (NONE::bvs1) pes) (pes_to_i4 (NONE::bvs2) pes))``,
  ho_match_mp_tac exp_to_i4_ind >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once exp_i4_cases] >>
    first_x_assum (qspecl_then[`bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    metis_tac[bind_i4_bvs_V] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once exp_i4_cases] >> metis_tac[] ) >>
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
      simp[Once exp_i4_cases] ) >>
    imp_res_tac find_index_is_MEM >>
    fs[Once pred_setTheory.EXTENSION,MEM_FILTER] >>
    res_tac >> fs[] >>
    imp_res_tac find_index_MEM >>
    ntac 2 (first_x_assum(qspec_then`0`mp_tac)) >>
    rw[] >> simp[] >>
    simp[Once exp_i4_cases] >>
    fs[bvs_V_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once exp_i4_cases] >>
    first_x_assum (qspecl_then[`(SOME x)::bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    fs[bvs_V_def] >>
    simp[find_index_def] >>
    rw[] >> rw[bind_i4_def] >>
    imp_res_tac find_index_LESS_LENGTH >>
    Cases_on`k1`>>Cases_on`k2`>>fs[]>>
    simp[bind_i4_def] >>
    fs[Once find_index_shift_0] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1] >>
    metis_tac[] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_i4_sIf >>
    simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_i4_sLet >>
    simp[Once exp_i4_cases] >>
    first_x_assum (qspecl_then[`bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    metis_tac[bind_i4_bvs_V] ) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_i4_sLet >>
    simp[Once exp_i4_cases] >>
    first_x_assum (qspecl_then[`SOME x::bvs2`]mp_tac) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    match_mp_tac bind_i4_bvs_V >> rw[] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once exp_i4_cases] >>
    fs[funs_to_i4_MAP] >>
    reverse conj_tac >- (
      qmatch_abbrev_tac`exp_i4 z1 z2 V1 (exp_to_i4 bvs10 e) (exp_to_i4 bvs20 e)` >>
      last_x_assum (qspecl_then[`bvs20`,`V1`]mp_tac) >>
      unabbrev_all_tac >> simp[] >>
      disch_then match_mp_tac >>
      conj_tac >- (
        fs[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
        metis_tac[] ) >>
      match_mp_tac bindn_i4_bvs_V >>
      simp[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(bvs20 = MAP f funs ++ bvs2)` >>
    qmatch_assum_abbrev_tac`Abbrev(bvs10 = MAP f funs ++ bvs1)` >>
    first_x_assum(qspecl_then[`bvs20`,`bindn_i4 (LENGTH funs) V`]mp_tac) >>
    unabbrev_all_tac >> simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >>
    conj_tac >- (
      fs[pred_setTheory.EXTENSION,MEM_FILTER,MEM_MAP,EXISTS_PROD,PULL_EXISTS] >>
      metis_tac[] ) >>
    match_mp_tac bindn_i4_bvs_V >>
    simp[] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once exp_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    last_x_assum(qspecl_then[`SOME x::bvs2`,`bind_i4 V`]mp_tac) >>
    simp[] >> disch_then match_mp_tac >>
    match_mp_tac bind_i4_bvs_V >> rw[] ) >>
  strip_tac >- (
    rw[] >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 row_to_i4_acc) >> simp[] >>
    disch_then(qspec_then`bvs2`mp_tac) >>
    `∃r1 n1 f1. row_to_i4 (NONE::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    `∃r2 n2 f2. row_to_i4 (NONE::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    simp[] >> strip_tac >> fs[] >>
    first_x_assum(qspecl_then[`ls++bvs2`,`bindn_i4 (LENGTH ls) V`]mp_tac) >>
    simp[rich_listTheory.FILTER_APPEND,bindn_i4_bvs_V] >>
    rpt BasicProvers.VAR_EQ_TAC >> strip_tac >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 row_to_i4_shift) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[bind_i4_thm] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]) >>
  strip_tac >- (
    rw[] >>
    match_mp_tac exp_i4_sIf >>
    simp[Once exp_i4_cases] >>
    conj_tac >- (
      qspecl_then[`pat_to_i4 p`,`1`]mp_tac(CONJUNCT1 ground_exp_i4_refl) >>
      simp[pat_to_i4_ground,bindn_i4_def] ) >>
    `∃r1 n1 f1. row_to_i4 (NONE::bvs1) p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >>
    `∃r2 n2 f2. row_to_i4 (NONE::bvs2) p = (r2,n2,f2)` by simp[GSYM EXISTS_PROD] >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 row_to_i4_acc) >> simp[] >>
    disch_then(qspec_then`bvs2`mp_tac) >>
    simp[] >> strip_tac >> fs[] >>
    last_x_assum(qspecl_then[`ls++bvs2`,`bindn_i4 (LENGTH ls) V`]mp_tac) >>
    simp[rich_listTheory.FILTER_APPEND,bindn_i4_bvs_V] >>
    rpt BasicProvers.VAR_EQ_TAC >> strip_tac >>
    qspecl_then[`NONE::bvs1`,`p`]mp_tac(CONJUNCT1 row_to_i4_shift) >>
    simp[arithmeticTheory.ADD1] >>
    disch_then match_mp_tac >> simp[bind_i4_thm] >>
    fsrw_tac[ARITH_ss][arithmeticTheory.ADD1]) >>
   rw[])

(* provide witnesses to make the first conjunct under the goal's existential
   prefix match the given term *)
fun match_exists_tac tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val (tms,_) = match_term c tm
    val xs = map #redex tms
    val ys = map #residue tms
    fun sorter ls = xs@(List.filter(not o Lib.C Lib.mem xs)ls)
  in
    CONV_TAC(RESORT_EXISTS_CONV sorter) >>
    map_every exists_tac ys
  end g

(* if the first conjunct under the goal's existential prefix matches the term
   except for some places where it has structure and the term just has variables,
   then pair split all those variables *)
fun split_pair_match tm (g as (_,w)) =
  let
    val (vs,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val cs = op::(strip_comb c)
    val ts = op::(strip_comb tm)
    val ss = map2 (total o match_term) ts cs
    val vs = map ((fn x => map #redex (Option.valOf x) handle _ => []) o
                  (Option.map fst)) ss
    val vs = flatten vs
    val _ = assert (not o (equal [])) vs
  in
    map_every PairCases_on (map (C cons [] o ANTIQUOTE) vs)
  end g

(* the theorem is of the form [!x1 ... xn. P ==> ?y1 ... ym. Q /\ ...]
   the goal is of the form [?z1 ... zk. Q' /\ ...]
   instantiate the xs as necessary to make Q and Q' match as much as possible
   (complete match impossible if some of Q's variables are the ys) *)
fun exists_match_mp_then (ttac:thm_tactic) th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val cs = strip_conj b val c = hd cs
    val (vs,t) = strip_forall (concl th)
    val vs = map (fst o dest_var o variant (free_vars b)) vs
    val th = CONV_RULE (RENAME_VARS_CONV vs) th
    val (vs,t) = strip_forall (concl th)
    val (_,b) = dest_imp t
    val (_,b) = strip_exists b
    val ts = strip_conj b val t = hd ts
    val (tms,_) = match_term t c
    val tms = filter (C mem vs o #redex) tms
    val tms = filter (not o C mem ws o #residue) tms
    val xs = map #redex tms
    val ys = map #residue tms
    fun sorter ls = xs@(filter(not o C mem xs) ls)
    val th = SPECL ys (CONV_RULE (RESORT_FORALL_CONV sorter) th)
  in
    ttac th
  end g

(* the theorem is of the form [!x1..n. P ==> Q]
   the goal is of the form [?y1..n. Q' /\ ...]
   replace the goal with [?y1..n. P /\ ...] by
   making the Q and Q' match *)
fun exists_suff_tac th (g as (_,w)) =
  let
    val (ws,b) = strip_exists w
    val bs = strip_conj b
    val th = GEN_ALL(PART_MATCH (snd o dest_imp) th (hd bs))
    val (vs,c) = strip_forall (concl th)
    val (b',_) = dest_imp c
  in
    suff_tac(list_mk_exists(ws,list_mk_conj(b'::tl bs))) >- metis_tac[th]
  end g

val csg_i4_count = prove(
  ``csg_i4 R csg1 csg2 ⇒ FST(FST csg2) = FST(FST csg1)``,
  PairCases_on`csg1` >>
  PairCases_on`csg2` >>
  simp[csg_i4_def])

val map_count_store_genv_count = prove(
  ``FST(FST (map_count_store_genv f csg)) = FST(FST csg)``,
  PairCases_on`csg`>>simp[map_count_store_genv_def])

val find_index_APPEND = store_thm("find_index_APPEND",
  ``∀l1 l2 x n. find_index x (l1 ++ l2) n =
    case find_index x l1 n of
    | NONE => find_index x l2 (n + LENGTH l1)
    | SOME x => SOME x``,
  Induct >> simp[find_index_def] >> rw[] >>
  BasicProvers.CASE_TAC >>
  simp[arithmeticTheory.ADD1])

val find_index_in_FILTER_EQ = store_thm("find_index_in_FILTER_EQ",
  ``∀P l1 l2 x n1 n2 j1 j2.
      FILTER P l1 = l2 ∧
      find_index x l1 n1 = SOME (n1+j1) ∧
      find_index x l2 n2 = SOME (n2+j2) ∧
      P x
      ⇒
      j1 < LENGTH l1 ∧ j2 < LENGTH l2 ∧
      EL j1 l1 = EL j2 l2``,
  gen_tac >> Induct >> simp[find_index_def] >>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >- (
    strip_tac >> fs[] >>
    Cases_on`j1`>>fsrw_tac[ARITH_ss][]>>
    fs[find_index_def] >>
    Cases_on`j2`>>fsrw_tac[ARITH_ss][]) >>
  strip_tac >>
  Cases_on`P h`>>fs[find_index_def] >- (
    rfs[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fsrw_tac[ARITH_ss][] >>
    first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
    simp[] >>
    disch_then(qspec_then`n2+1`mp_tac) >> simp[] >>
    Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`j2=0`>>fsrw_tac[ARITH_ss][]>>
    disch_then(qspecl_then[`PRE j1`,`PRE j2`]mp_tac) >>
    simp[rich_listTheory.EL_CONS] ) >>
  first_x_assum(qspecl_then[`x`,`n1+1`]mp_tac) >>
  simp[] >>
  disch_then(qspec_then`n2`mp_tac) >> simp[] >>
  imp_res_tac find_index_LESS_LENGTH >>
  fsrw_tac[ARITH_ss][] >>
  Cases_on`j1=0`>>fsrw_tac[ARITH_ss][]>>
  disch_then(qspec_then`PRE j1`mp_tac) >>
  simp[rich_listTheory.EL_CONS] )

val exp_to_i4_correct = store_thm("exp_to_i4_correct",
  ``(∀ck env s exp res. evaluate_i3 ck env s exp res ⇒
     (SND res ≠ Rerr Rtype_error) ∧ good_env_s_i2 env s ⇒
     ∃res4.
       evaluate_i4 ck
         (MAP (v_to_i4 o SND) env)
         (map_count_store_genv v_to_i4 s)
         (exp_to_i4 (MAP (SOME o FST) env) exp) res4 ∧
       csg_i4 v_i4 (map_count_store_genv v_to_i4 (FST res)) (FST res4) ∧
       result_rel v_i4 v_i4 (map_result v_to_i4 v_to_i4 (SND res)) (SND res4)) ∧
    (∀ck env s exps ress. evaluate_list_i3 ck env s exps ress ⇒
     (SND ress ≠ Rerr Rtype_error) ∧ good_env_s_i2 env s ⇒
     ∃ress4.
       evaluate_list_i4 ck
         (MAP (v_to_i4 o SND) env)
         (map_count_store_genv v_to_i4 s)
         (exps_to_i4 (MAP (SOME o FST) env) exps) ress4 ∧
       csg_i4 v_i4 (map_count_store_genv v_to_i4 (FST ress)) (FST ress4) ∧
       result_rel (LIST_REL v_i4) v_i4 (map_result vs_to_i4 v_to_i4 (SND ress)) (SND ress4)) ∧
    (∀ck env s v pes res. evaluate_match_i3 ck env s v pes res ⇒
     (SND res ≠ Rerr Rtype_error) ∧ good_env_s_i2 env s ∧ good_v_i2 v ⇒
     ∃res4.
       evaluate_i4 ck
         (v_to_i4 v::(MAP (v_to_i4 o SND) env))
         (map_count_store_genv v_to_i4 s)
         (pes_to_i4 (NONE::(MAP (SOME o FST) env)) pes) res4 ∧
       csg_i4 v_i4 (map_count_store_genv v_to_i4 (FST res)) (FST res4) ∧
       result_rel v_i4 v_i4 (map_result v_to_i4 v_to_i4 (SND res)) (SND res4))``,
  ho_match_mp_tac evaluate_i3_strongind >>
  strip_tac >- rw[Once evaluate_i4_cases] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >> fs[] >> rw[] >>
    qmatch_assum_abbrev_tac`P ⇒ Q` >>
    `P` by ( imp_res_tac evaluate_i3_preserves_good >> fs[Abbr`P`]) >>
    fs[Abbr`P`,Abbr`Q`] >>
    qmatch_assum_rename_tac`result_rel X Y Z (SND res5)`["X","Y","Z"] >>
    qmatch_assum_abbrev_tac`evaluate_i4 ck (v5::env5) s5 e5 res5` >>
    qmatch_assum_abbrev_tac`v_i4 v5 v6` >>
    qspecl_then[`ck`,`v5::env5`,`s5`,`e5`,`res5`]mp_tac(CONJUNCT1 evaluate_i4_exp_i4) >>
    simp[] >> disch_then(qspecl_then[`v6::env5`,`FST res4`,`e5`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      match_mp_tac (CONJUNCT1 exp_i4_refl) >>
      Cases >> simp[env_i4_def] ) >>
    disch_then(qx_choose_then`res6`strip_assume_tac) >>
    qexists_tac`res6` >>
    reverse conj_tac >- metis_tac[csg_v_i4_trans,result_rel_v_v_i4_trans] >>
    Cases_on`res4`>>fs[] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    rfs[EXISTS_PROD] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD] >> rw[Once v_i4_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD] >> metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac lookup_find_index_SOME >>
    first_x_assum(qspec_then`0`mp_tac) >>
    rw[] >> rw[] >>
    imp_res_tac find_index_LESS_LENGTH >>
    fs[] >> simp[EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    simp[map_count_store_genv_def,EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >> fs[EXISTS_PROD] >>
    Cases_on`uop`>>
    fs[do_uapp_i3_def,do_uapp_i4_def,LET_THM,semanticPrimitivesTheory.store_alloc_def] >>
    rw[] >>
    pop_assum kall_tac >>
    TRY (pop_assum mp_tac >> BasicProvers.CASE_TAC) >>
    simp[semanticPrimitivesTheory.store_lookup_def] >> rw[] >>
    fs[map_count_store_genv_def,PULL_EXISTS,csg_i4_def] >>
    TRY (metis_tac[EVERY2_LENGTH,LENGTH_MAP]) >>
    qmatch_assum_abbrev_tac`evaluate_i4 A B C D (((X,Y),Z),Rval V)` >>
    CONV_TAC(RESORT_EXISTS_CONV(List.rev))>>
    map_every qexists_tac[`Z`,`Y`,`V`] >>
    unabbrev_all_tac >> simp[EL_MAP] >>
    simp[LIST_EQ_REWRITE] >> rw[] >>
    simp[EL_MAP,EL_LUPDATE] >> rw[] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >> fs[MEM_ZIP,PULL_EXISTS,EL_MAP] >>
    fs[optionTheory.OPTREL_def] >>
    res_tac >> simp[MEM_ZIP,PULL_EXISTS,EL_MAP,EL_LUPDATE,optionTheory.OPTREL_def] >>
    rw[] >> fs[] >>
    metis_tac[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD] >> metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    qpat_assum`P ⇒ ∃X. Q X`mp_tac >>
    qpat_assum`P ⇒ ∃X. Q X`mp_tac >>
    discharge_hyps >- metis_tac[evaluate_i3_preserves_good,FST] >>
    disch_then(qx_choose_then`res5`strip_assume_tac) >>
    discharge_hyps >- (
      imp_res_tac evaluate_i3_preserves_good >>
      fs[good_env_s_i2_def] >>
      imp_res_tac do_app_i2_preserves_good >> fs[] ) >>
    disch_then(qx_choose_then`res6`strip_assume_tac) >>
    simp_tac(srw_ss()++DNF_ss)[Once evaluate_i4_cases] >>
    disj1_tac >>
    qmatch_assum_abbrev_tac`evaluate_i4 A B C D res5` >>
    qspecl_then[`A`,`B`,`C`,`D`,`res5`]mp_tac (CONJUNCT1 evaluate_i4_exp_i4) >>
    simp[] >>
    disch_then(qspecl_then[`B`,`FST res4`,`D`]mp_tac) >>
    simp[exp_i4_refl,env_i4_def] >>
    disch_then(qx_choose_then`res55`strip_assume_tac) >>
    unabbrev_all_tac >>
    qmatch_assum_rename_tac`SND res4 = Rval v3`[] >>
    qmatch_assum_rename_tac`SND res55 = Rval v4`[] >>
    CONV_TAC(RESORT_EXISTS_CONV(fn ls => tl ls @[hd ls])) >>
    map_every qexists_tac[`v3`,`v4`] >>
    CONV_TAC(RESORT_EXISTS_CONV(fn ls => tl ls @[hd ls])) >>
    CONV_TAC(RESORT_EXISTS_CONV(fn ls => tl ls @[hd ls])) >>
    qexists_tac`FST res4` >>
    Cases_on`res4`>>fs[]>>
    PairCases_on`res55`>>
    map_every qexists_tac[`res551`,`res550`] >>
    CONV_TAC(RESORT_EXISTS_CONV(fn ls => tl ls @[hd ls])) >>
    qexists_tac`res552` >> fs[] >>
    qspecl_then[`op`,`v1`,`v2`,`env`,`s3`]mp_tac do_app_i4_correct >>
    discharge_hyps >- (
      imp_res_tac evaluate_i3_preserves_good >> fs[] ) >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`do_app_i4 env7 s7 op v17 v27 = SOME r7` >>
    qspecl_then[`env7`,`s7`,`op`,`v17`,`v27`]mp_tac do_app_i4_v_i4 >>
    simp[optionTheory.OPTREL_def,Abbr`r7`] >>
    disch_then(qspecl_then[`env7`,`res551`,`v3`,`v4`]mp_tac) >>
    discharge_hyps >- (
      PairCases_on`res5`>>fs[map_count_store_genv_def,csg_i4_def] >>
      metis_tac[v_i4_trans,LIST_REL_v_i4_trans] ) >>
    disch_then(qx_choose_then`res7`strip_assume_tac) >>
    PairCases_on`res7` >> simp[] >> fs[] >>
    qmatch_assum_abbrev_tac`evaluate_i4 ck env8 s8 e8 res6` >>
    Q.PAT_ABBREV_TAC`s9:v_i4 count_store_genv = X` >>
    qspecl_then[`ck`,`env8`,`s8`,`e8`,`res6`]mp_tac (CONJUNCT1 evaluate_i4_exp_i4) >>
    simp[] >>
    disch_then(qspecl_then[`res70`,`s9`,`res72`]mp_tac) >>
    discharge_hyps >- (
      unabbrev_all_tac >>
      PairCases_on`res5`>>
      fs[map_count_store_genv_def,csg_i4_def] >>
      metis_tac[LIST_REL_OPTREL_v_i4_trans] ) >>
    disch_then(qx_choose_then`res9`strip_assume_tac) >>
    qexists_tac`res9` >> simp[] >>
    unabbrev_all_tac >>
    PairCases_on`res`>>
    PairCases_on`res5`>>
    PairCases_on`res6`>>
    PairCases_on`res9`>>
    fs[map_count_store_genv_def,csg_i4_def] >>
    metis_tac[LIST_REL_v_i4_trans,LIST_REL_OPTREL_v_i4_trans,result_rel_v_v_i4_trans] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >> disj1_tac >>
    imp_res_tac evaluate_i3_preserves_good >> fs[] >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_i4_exp_i4)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- simp[exp_i4_refl,env_i4_def] >>
    strip_tac >>
    first_assum (split_pair_match o concl) >>
    imp_res_tac csg_i4_count >>
    rfs[] >> fs[map_count_store_genv_count] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    qspecl_then[`Opapp`,`v1`,`v2`,`env`,`s3`]mp_tac do_app_i4_correct >>
    simp[] >>
    disch_then(fn th =>
      assume_tac th >>
      mp_tac(SPECL(snd(strip_comb(lhs(concl th)))) do_app_i4_v_i4)) >>
    disch_then(fn th =>
      fn (g as (_,w)) =>
         (mp_tac(SPECL(filter(not o (equal``Opapp``))
                       (snd(strip_comb(lhs(hd(strip_conj(snd(strip_exists w))))))))
                 th)) g) >>
    discharge_hyps >- (
      qmatch_assum_abbrev_tac`csg_i4 v_i4 X (FST Y)` >>
      PairCases_on`Y`>>fs[markerTheory.Abbrev_def] >>
      fs[map_count_store_genv_def,csg_i4_def] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      metis_tac[LIST_REL_v_i4_trans,v_i4_trans] ) >>
    simp[optionTheory.OPTREL_def,EXISTS_PROD] >> strip_tac >> simp[] >>
    qmatch_assum_abbrev_tac`csg_i4 v_i4 X (FST Y)` >>
    PairCases_on`Y`>>fs[markerTheory.Abbrev_def] >>
    fs[map_count_store_genv_def,csg_i4_def] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    metis_tac[LIST_REL_OPTREL_v_i4_trans]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac evaluate_i3_preserves_good >>
    srw_tac[DNF_ss][] >> fs[] >>
    ntac 2 disj2_tac >> disj1_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT1 evaluate_i4_exp_i4)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- simp[exp_i4_refl,env_i4_def] >>
    strip_tac >>
    first_assum (split_pair_match o concl) >>
    rfs[] >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    metis_tac[csg_v_i4_trans,exc_rel_v_i4_trans]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >>
    imp_res_tac evaluate_i3_preserves_good >> fs[] >>
    qho_match_abbrev_tac`∃res4. evaluate_i4 ck env4 s4 (sIf_i4 a1 a2 a3) res4 ∧ P res4` >>
    qsuff_tac`∃res4. evaluate_i4 ck env4 s4 (If_i4 a1 a2 a3) res4 ∧ P res4 ∧ SND res4 ≠ Rerr Rtype_error`
      >-metis_tac[sIf_i4_correct] >>
    simp[Once evaluate_i4_cases,Abbr`P`] >>
    fs[do_if_i2_def,do_if_i4_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disj1_tac >>
    CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
    qexists_tac`FST res4` >>
    CONV_TAC(SWAP_EXISTS_CONV) >>
    qmatch_assum_rename_tac`SND res4 = Rval v1`[] >>
    qexists_tac`v1` >>
    Cases_on`v`>>fs[]>>
    Cases_on`l`>>fs[]>>
    Cases_on`res4`>>fs[]>>
    qmatch_assum_abbrev_tac`evaluate_i4 ck env4 s5 e5 res5` >>
    qspecl_then[`ck`,`env4`,`s5`,`e5`,`res5`]mp_tac(CONJUNCT1 evaluate_i4_exp_i4) >>
    qmatch_assum_rename_tac`csg_i4 v_i4 s5 s6`[] >>
    simp[] >> disch_then(qspecl_then[`env4`,`s6`,`e5`]mp_tac) >>
    simp[exp_i4_refl,env_i4_def] >>
    disch_then(qx_choose_then`res7`strip_assume_tac) >>
    map_every qexists_tac[`e5`,`res7`] >>
    unabbrev_all_tac >>
    conj_tac >- (rw[] >> fs[]) >>
    conj_asm1_tac >- metis_tac[csg_v_i4_trans,result_rel_v_v_i4_trans] >>
    spose_not_then strip_assume_tac >> fs[] >>
    qpat_assum`Rtype_error = X`(assume_tac o SYM) >> fs[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fs[] >>
    qho_match_abbrev_tac`∃res4. evaluate_i4 ck env4 s4 (sIf_i4 a1 a2 a3) res4 ∧ P res4` >>
    qsuff_tac`∃res4. evaluate_i4 ck env4 s4 (If_i4 a1 a2 a3) res4 ∧ P res4 ∧ SND res4 ≠ Rerr Rtype_error`
      >-metis_tac[sIf_i4_correct] >>
    simp[Once evaluate_i4_cases,Abbr`P`] >>
    qexists_tac`res4` >> simp[] >>
    PairCases_on`res4` >>
    Cases_on`err`>>fs[]>>rw[]) >>
  strip_tac >- (
    rw[] >>
    qho_match_abbrev_tac`∃res4. evaluate_i4 ck env4 s4 (sLet_i4 a1 a2) res4 ∧ P res4` >>
    qsuff_tac`∃res4. evaluate_i4 ck env4 s4 (Let_i4 a1 a2) res4 ∧ P res4 ∧ SND res4 ≠ Rerr Rtype_error`
      >-metis_tac[sLet_i4_correct] >>
    simp[Once evaluate_i4_cases,Abbr`P`] >> fs[] >>
    imp_res_tac evaluate_i3_preserves_good >> fs[] >>
    qmatch_assum_abbrev_tac`evaluate_i4 ck (v4::env4) s5 a2 res5` >>
    qspecl_then[`ck`,`v4::env4`,`s5`,`a2`,`res5`]mp_tac(CONJUNCT1 evaluate_i4_exp_i4) >>
    qmatch_assum_rename_tac`v_i4 v4 v5`[] >>
    simp[] >> disch_then(qspecl_then[`v5::env4`,`FST res4`,`a2`]mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      match_mp_tac (CONJUNCT1 exp_i4_refl) >>
      Cases >> simp[env_i4_def] ) >>
    disch_then(qx_choose_then`res6`strip_assume_tac) >>
    qexists_tac`res6` >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disj1_tac >>
    map_every qexists_tac[`v5`,`FST res4`] >>
    Cases_on`res4`>>fs[]>>
    conj_asm1_tac >- metis_tac[csg_v_i4_trans,result_rel_v_v_i4_trans] >>
    spose_not_then strip_assume_tac >> fs[] >>
    qpat_assum`Rtype_error = X`(assume_tac o SYM) >> fs[]) >>
  strip_tac >- (
    rw[] >> fs[] >>
    exists_match_mp_then exists_suff_tac sLet_i4_correct >>
    simp[Once evaluate_i4_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[] >>
    Cases_on`err`>>fs[]) >>
  strip_tac >- (
    Cases_on`n`>> rw[] >- (
      fs[libTheory.opt_bind_def] >>
      imp_res_tac evaluate_i3_preserves_good >> fs[] >>
      simp[Once evaluate_i4_cases] >>
      srw_tac[DNF_ss][] >>
      disj1_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      first_x_assum (mp_tac o MATCH_MP (CONJUNCT1 evaluate_i4_exp_i4)) >>
      disch_then (exists_match_mp_then mp_tac) >>
      discharge_hyps >- simp[exp_i4_refl,env_i4_def] >> strip_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] >>
      metis_tac[csg_v_i4_trans,result_rel_v_v_i4_trans] ) >>
    imp_res_tac evaluate_i3_preserves_good >>
    fs[libTheory.opt_bind_def] >>
    exists_match_mp_then exists_suff_tac sLet_i4_correct >>
    simp[Once evaluate_i4_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    qpat_assum`P ⇒ ∃Y. Q`mp_tac >>
    discharge_hyps >- fs[good_env_s_i2_def] >> strip_tac >>
    first_x_assum (mp_tac o MATCH_MP (CONJUNCT1 evaluate_i4_exp_i4)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- (
      simp[] >>
      match_mp_tac (CONJUNCT1 exp_i4_refl) >>
      Cases >> simp[env_i4_def] ) >>
    strip_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    reverse conj_tac >- (
      metis_tac[csg_v_i4_trans,result_rel_v_v_i4_trans] ) >>
    spose_not_then strip_assume_tac >>
    fs[] >> fs[] >>
    qpat_assum`Rtype_error = X`(assume_tac o SYM) >> fs[]) >>
  strip_tac >- (
    Cases_on`n`>>rw[]>>fs[] >- (
      simp[Once evaluate_i4_cases] >>
      srw_tac[DNF_ss][] >>
      disj2_tac >>
      first_assum (split_pair_match o concl) >> fs[] >>
      first_assum (match_exists_tac o concl) >> simp[] ) >>
    exists_match_mp_then exists_suff_tac sLet_i4_correct >>
    simp[Once evaluate_i4_cases] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >>
    first_assum (split_pair_match o concl) >> fs[] >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[] ) >>
  strip_tac >- (
    rw[] >>
    simp[Once evaluate_i4_cases] >>
    `good_env_s_i2 (build_rec_env_i2 funs env env) s` by (
      simp[build_rec_env_i2_MAP] >>
      fs[good_env_s_i2_def,EVERY_MAP,EVERY_MEM,FST_triple,UNCURRY] >>
      simp[MEM_MAP] >> metis_tac[] ) >>
    fs[] >>
    simp[markerTheory.Abbrev_def] >>
    qho_match_abbrev_tac`∃e. evaluate_i4 a b c d e ∧ P e` >>
    qmatch_assum_abbrev_tac`evaluate_i4 a b' c d' e` >>
    `b = b'` by (
      unabbrev_all_tac >>
      fs[build_rec_env_i4_def,build_rec_env_i2_MAP,funs_to_i4_MAP] >>
      rw[LIST_EQ_REWRITE,EL_MAP,UNCURRY,funs_to_i4_MAP] >- (
        rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
        simp[FUN_EQ_THM,FORALL_PROD] ) >>
      fs[FST_triple] >>
      imp_res_tac find_index_ALL_DISTINCT_EL >>
      first_x_assum(qspec_then`x`mp_tac) >>
      discharge_hyps >- simp[] >>
      disch_then(qspec_then`0`mp_tac) >>
      asm_simp_tac(std_ss)[EL_MAP] >>
      simp[]) >>
    `d = d'` by (
      unabbrev_all_tac >>
      simp[build_rec_env_i2_MAP] >>
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      rpt (AP_THM_TAC ORELSE AP_TERM_TAC) >>
      simp[FUN_EQ_THM,FORALL_PROD] ) >>
    unabbrev_all_tac >> rw[] >>
    first_assum(match_exists_tac o concl) >> simp[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    simp[Once evaluate_i4_cases] >>
    simp[map_count_store_genv_def,MAP_GENLIST,combinTheory.o_DEF] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac evaluate_i3_preserves_good >> fs[] >>
    srw_tac[DNF_ss][] >>
    last_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT2 evaluate_i4_exp_i4)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- simp[exp_i4_refl,env_i4_def] >> strip_tac >>
    first_assum(split_pair_match o concl) >> rfs[] >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    metis_tac[csg_v_i4_trans,LIST_REL_v_i4_trans]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[EXISTS_PROD,PULL_EXISTS] >>
    metis_tac[]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac evaluate_i3_preserves_good >> fs[] >>
    srw_tac[DNF_ss][] >>
    disj2_tac >>
    last_assum(split_pair_match o concl) >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_x_assum(mp_tac o MATCH_MP (CONJUNCT2 evaluate_i4_exp_i4)) >>
    disch_then (exists_match_mp_then mp_tac) >>
    discharge_hyps >- simp[exp_i4_refl,env_i4_def] >> strip_tac >>
    first_assum(split_pair_match o concl) >> rfs[] >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    metis_tac[csg_v_i4_trans,exc_rel_v_i4_trans]) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >>
    Cases_on`pes`>>simp[]>>fs[]>>
    qpat_assum`P ⇒ Q`mp_tac >>
    (discharge_hyps >- (
      fs[good_env_s_i2_def] >>
      metis_tac[CONJUNCT1 pmatch_i2_preserves_good] )) >>
    strip_tac
    >|[ALL_TAC,
      exists_match_mp_then exists_suff_tac sIf_i4_correct >>
      simp[Once evaluate_i4_cases] >>
      srw_tac[DNF_ss][] >> disj1_tac >>
      CONV_TAC SWAP_EXISTS_CONV >>
      qexists_tac`Litv_i4 (Bool T)` >>
      simp[do_if_i4_def] >>
      imp_res_tac(CONJUNCT1 pat_to_i4_correct) >> fs[] >>
      Q.PAT_ABBREV_TAC`s2 = X:v_i4 count_store_genv` >>
      CONV_TAC SWAP_EXISTS_CONV  >>
      qexists_tac`s2` >> simp[Abbr`s2`] >>
      pop_assum kall_tac
    ] >>
    `∃bvs n f. row_to_i4 (NONE::MAP (SOME o FST) env) p = (bvs,n,f)` by (
      simp[GSYM EXISTS_PROD] ) >> simp[] >>
    fs[Once(CONJUNCT1 pmatch_i2_nil)] >>
    Cases_on`pmatch_i2 s p v []`>>fs[]>>
    qmatch_assum_rename_tac`menv ++ env = envX`[] >> BasicProvers.VAR_EQ_TAC >>
    qho_match_abbrev_tac`∃res4. evaluate_i4 ck (v4::env4) s4 (f (exp_to_i4 bvs exp)) res4 ∧ P res4` >>
    fs[] >>
    qmatch_assum_abbrev_tac`row_to_i4 (NONE::bvs0) p = X` >>
    (row_to_i4_correct
     |> CONJUNCT1
     |> SIMP_RULE (srw_ss())[]
     |> Q.SPECL[`p`,`bvs0`,`s`,`v`]
     |> mp_tac) >>
    simp[Abbr`X`] >> strip_tac >>
    qmatch_assum_abbrev_tac`evaluate_i4 ck env3 s4 exp3 res4` >>
    qspecl_then[`ck`,`env3`,`s4`,`exp3`,`res4`]mp_tac (CONJUNCT1 evaluate_i4_exp_i4) >>
    simp[] >>
    disch_then(qspecl_then[`menv4 ++ env4`,`s4`,`exp_to_i4 bvs exp`]mp_tac) >>
    (discharge_hyps >- (
       simp[Abbr`env3`,Abbr`env4`,Abbr`exp3`] >>
       match_mp_tac(CONJUNCT1 exp_to_i4_shift) >>
       simp[Abbr`bvs0`] >> conj_tac >- (
         qpat_assum`X = MAP Y menv`mp_tac >>
         disch_then(mp_tac o Q.AP_TERM`set`) >>
         simp[pred_setTheory.EXTENSION,MEM_FILTER,MEM_ZIP,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
         simp[MEM_EL,PULL_EXISTS,FORALL_PROD] >>metis_tac[] ) >>
       simp[bvs_V_def,env_i4_def] >>
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
         qmatch_assum_rename_tac`z < SUC n`[] >>
         last_x_assum(qspec_then`z`mp_tac) >>
         qpat_assum`SOME x = Y`(assume_tac o SYM) >>
         simp[] >> rw[] >>
         metis_tac[] ) >>
       rw[] >>
       imp_res_tac find_index_LESS_LENGTH >>
       fs[] >> simp[rich_listTheory.EL_APPEND1,EL_MAP] >>
       qmatch_assum_rename_tac`k2 < LENGTH l2`[] >>
       `MAP (SOME o FST) menv = FILTER IS_SOME l2` by (
         qpat_assum`X = MAP Y Z`(mp_tac o Q.AP_TERM`MAP FST`) >>
         simp[GSYM rich_listTheory.FILTER_MAP,MAP_MAP_o,MAP_ZIP,combinTheory.o_DEF,UNCURRY] ) >>
       Q.ISPEC_THEN`l2`mp_tac(CONV_RULE SWAP_FORALL_CONV find_index_in_FILTER_EQ) >>
       disch_then(qspec_then`IS_SOME`mp_tac) >>
       pop_assum(SUBST1_TAC o SYM) >> simp[] >>
       disch_then(qspecl_then[`SOME x`,`0`,`0`]mp_tac) >>
       simp[EL_MAP] >>
       cheat )) >>
    disch_then(qx_choose_then`res5`strip_assume_tac) >>
    fs[Abbr`s4`,map_count_store_genv_def] >>
    qexists_tac`res5` >> simp[Abbr`P`] >>
    (reverse conj_asm2_tac >- (
      TRY(conj_tac >- (
        spose_not_then strip_assume_tac >>
        PairCases_on`res4`>>PairCases_on`res5`>>
        fs[csg_i4_def])) >>
      metis_tac[csg_v_i4_trans,result_rel_v_v_i4_trans] )) >>
    first_x_assum match_mp_tac >> rfs[] >>
    spose_not_then strip_assume_tac >>
    PairCases_on`res4`>>PairCases_on`res5`>>
    fs[csg_i4_def]) >>
  strip_tac >- (
    rw[] >>
    Cases_on`pes`>>fs[]>-(
      fs[Once evaluate_i3_cases] >>
      rw[] >> fs[] ) >>
    exists_match_mp_then exists_suff_tac sIf_i4_correct >>
    simp[Once evaluate_i4_cases] >>
    srw_tac[DNF_ss][] >>
    disj1_tac >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`Litv_i4 (Bool F)` >>
    simp[do_if_i4_def] >>
    imp_res_tac(CONJUNCT1 pat_to_i4_correct) >> fs[] >>
    Q.PAT_ABBREV_TAC`s2 = X:v_i4 count_store_genv` >>
    CONV_TAC SWAP_EXISTS_CONV  >>
    qexists_tac`s2` >> simp[Abbr`s2`] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    spose_not_then strip_assume_tac >> fs[] ) >>
  strip_tac >- rw[] >>
  rw[])

(*
(* 0 = SOME, 1 = NONE, 2 = INL, 3 = INR, 4 = NIL, 5 = CONS, 6 = PAIR *)

(*
case x of
  (SOME (INL n) :: ys) => (* something with n ys *) ...
| [NONE] => ...
| ... =>
*)

val th =
EVAL
``exp_to_i4 [SOME "y";SOME "x"]
  (Mat_i2 (Var_local_i2 "x")
    [((Pcon_i2 5 [Pcon_i2 0 [Pcon_i2 2 [Pvar_i2 "n"]]; Pvar_i2 "ys"])
     ,(Con_i2 6 [Var_local_i2 "n"; Var_local_i2 "ys"])
     );
     ((Pcon_i2 5 [Pcon_i2 1 []; Pcon_i2 4 []])
     ,(Con_i2 6 [Lit_i2 (IntLit 0); Var_local_i2 "y"])
     )]
  )``

val _ = Parse.overload_on("COND",``If_i4``)
val _ = Parse.overload_on("tageq", ``λn v. Uapp_i4 (Tag_eq_i4 n) (Var_local_i4 v)``)
val _ = Parse.overload_on("isSOME", ``λv. Uapp_i4 (Tag_eq_i4 0) (Var_local_i4 v)``)

val _ = Parse.overload_on("isNONE", ``λv. App_i4 Equality (Var_local_i4 v) (Con_i4 1 [])``)
val _ = Parse.overload_on("isINL", ``λv. Uapp_i4 (Tag_eq_i4 2) (Var_local_i4 v)``)
val _ = Parse.overload_on("isNILtag", ``λv. Uapp_i4 (Tag_eq_i4 4) (Var_local_i4 v)``)
val _ = Parse.overload_on("isNIL", ``λv. App_i4 Equality (Var_local_i4 v) (Con_i4 4 [])``)
val _ = Parse.overload_on("isCONS", ``λv. Uapp_i4 (Tag_eq_i4 5) (Var_local_i4 v)``)
val _ = Parse.overload_on("el", ``λn v. Uapp_i4 (El_i4 n) (Var_local_i4 v)``)
val _ = Parse.overload_on("true", ``Lit_i4 (Bool T)``)
val _ = Parse.overload_on("false", ``Lit_i4 (Bool F)``)
val _ = Parse.overload_on("pair", ``λx y. Con_i4 6 [x;y]``)
val _ = Parse.overload_on("Let", ``Let_i4``)
val _ = Parse.overload_on("Var", ``Var_local_i4``)
val tm = rhs(concl th)

*)

val _ = export_theory()
