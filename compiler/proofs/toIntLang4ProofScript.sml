open HolKernel boolLib boolSimps bossLib lcsymtacs listTheory alistTheory pairTheory
open Defn miscLib miscTheory intLang2Theory toIntLang2ProofTheory intLang3Theory intLang4Theory
val _ = new_theory"toIntLang4Proof"

fun register name def ind =
  let val _ = save_thm (name ^ "_def", def);
      val _ = save_thm (name ^ "_ind", ind);
      val _ = computeLib.add_persistent_funs [name ^ "_def"];
  in
    ()
  end;

val (exp_to_i4_def, exp_to_i4_ind) =
  tprove_no_defn ((exp_to_i4_def, exp_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,e) => exp_i2_size e
                                        | INR (INL (bvs,es)) => exp_i26_size es
                                        | INR (INR (INL (bvs,funs))) => exp_i21_size funs
                                        | INR (INR (INR (bvs,pes))) => exp_i23_size pes)`);
val _ = register "exp_to_i4" exp_to_i4_def exp_to_i4_ind;
val _ = export_rewrites["exp_to_i4_def"
  ,"intLang4.uop_to_i4_def"
  ,"intLang4.pure_uop_i4_def"
  ,"intLang4.pure_op_def"]

val (pat_to_i4_def, pat_to_i4_ind) =
  tprove_no_defn ((pat_to_i4_def, pat_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL p => pat_i2_size p
                                        | INR (n,ps) => pat_i21_size ps)`);
val _ = register "pat_to_i4" pat_to_i4_def pat_to_i4_ind;

val (row_to_i4_def, row_to_i4_ind) =
  tprove_no_defn ((row_to_i4_def, row_to_i4_ind),
  WF_REL_TAC `inv_image $< (\x. case x of INL (bvs,p) => pat_i2_size p
                                        | INR (bvs,n,k,ps) => pat_i21_size ps)`);
val _ = register "row_to_i4" row_to_i4_def row_to_i4_ind;

val (Let_Els_i4_def, Let_Els_i4_ind) =
  tprove_no_defn ((Let_Els_i4_def, Let_Els_i4_ind),
  WF_REL_TAC `measure (FST o SND)`);
val _ = register "Let_els_i4" Let_Els_i4_def Let_Els_i4_ind;

val (do_eq_i4_def, do_eq_i4_ind) =
  tprove_no_defn ((do_eq_i4_def, do_eq_i4_ind),
  WF_REL_TAC`inv_image $< (\x. case x of INL (v1,v2) => v_i4_size v1
                                       | INR (vs1,vs2) => v_i41_size vs1)`);
val _ = register "do_eq_i4" do_eq_i4_def do_eq_i4_ind;

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

val map_error_result_def = Define`
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f Rtype_error = Rtype_error) ∧
  (map_error_result f Rtimeout_error = Rtimeout_error)`
val _ = export_rewrites["map_error_result_def"]

val every_error_result_def = Define`
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P Rtype_error = T) ∧
  (every_error_result P Rtimeout_error = T)`
val _ = export_rewrites["every_error_result_def"]

val map_result_def = Define`
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))`
val _ = export_rewrites["map_result_def"]

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

val evaluate_i3_preserves_good = store_thm("evaluate_i3_preserves_good",
  ``(∀ck env s exp res. evaluate_i3 ck env s exp res ⇒
      good_env_s_i2 env s ⇒
      good_env_s_i2 env (FST res) ∧
      every_result good_v_i2 good_v_i2 (SND res)) ∧
    (∀ck env s exps ress. evaluate_list_i3 ck env s exps ress ⇒
      good_env_s_i2 env s ⇒
      good_env_s_i2 env (FST ress) ∧
      every_result good_vs_i2 good_v_i2 (SND ress)) ∧
    (∀ck env s v pes ev res. evaluate_match_i3 ck env s v pes ev res ⇒
      good_env_s_i2 env s ∧ good_v_i2 v ∧ good_v_i2 ev ⇒
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
  strip_tac >- ( rw[libTheory.bind_def] >> fs[good_env_s_i2_def] ) >>
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
  strip_tac >- ( rw[] >> cheat ) >>
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

(*
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
    last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >- (
      simp[Once evaluate_i4_cases] >>
      qmatch_abbrev_tac`X ∨ Y` >> qunabbrev_tac`Y` >>
      simp[Once evaluate_i4_cases] >>
      Cases_on`op`>>fs[do_app_i4_def,Abbr`X`]

      last_x_assum(qspecl_then[`ck`,`env`,`s`]strip_assume_tac) >- (
        simp[Once evaluate_i4_cases] >>
        Cases_on`op`>>fs[do_app_i4_def]


  simp[Once evaluate_i4_cases] >>

val sLet_i4_correct = store_thm("sLet_i4_correct",
  ``∀ck env s e1 e2 res.
    evaluate_i4 ck env s (Let_i4 e1 e2) res ⇒
    evaluate_i4 ck env s (sLet_i4 e1 e2) res``,
  rpt gen_tac >>
  reverse(Cases_on`e2`) >> rw[sLet_i4_def] >- (
    Cases_on`n`>>rw[sLet_i4_def]>>
    pop_assum mp_tac >>
    rw[Once evaluate_i4_cases] >> rw[] >>
    pop_assum mp_tac >>
    simp[Once evaluate_i4_cases] ) >>
  pop_assum mp_tac >>
  rw[Once evaluate_i4_cases]
*)

val Let_Els_i4_correct = prove(
  ``∀n k e tag vs env ck s res us.
    LENGTH us = n ∧ k ≤ LENGTH vs ∧
    evaluate_i4 ck (TAKE k vs ++ us ++ (Conv_i4 tag vs::env)) s e res ⇒
    evaluate_i4 ck (us ++ (Conv_i4 tag vs::env)) s (Let_Els_i4 n k e) res``,
  ho_match_mp_tac Let_Els_i4_ind >> rw[Let_Els_i4_def] >>
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
    (enve = us ++ (Conv_i4 tag vs::env))
    ⇒
    evaluate_i4 ck enve s (Let_Els_i4 n k e) res``,
  metis_tac[Let_Els_i4_correct])

(* TODO: move *)

(*
val pat_bindings_i2_acc = store_thm("pat_bindings_i2_acc",
  ``(∀p l. pat_bindings_i2 p l = pat_bindings_i2 p [] ++ l) ∧
    (∀ps l. pats_bindings_i2 ps l = pats_bindings_i2 ps [] ++ l)``,
  ho_match_mp_tac (TypeBase.induction_of``:pat_i2``) >> rw[] >>
  simp_tac std_ss [pat_bindings_i2_def] >>
  metis_tac[APPEND,APPEND_ASSOC])

val pmatch_tac =
  ho_match_mp_tac pmatch_i2_ind >>
  strip_tac >- (
    rw[pmatch_i2_def,libTheory.bind_def,pat_bindings_i2_def] >> rw[] ) >>
  strip_tac >- (
    rw[pmatch_i2_def,pat_bindings_i2_def] >> rw[] ) >>
  strip_tac >- ( rw[pmatch_i2_def,pat_bindings_i2_def] ) >>
  strip_tac >- (
    rw[pmatch_i2_def,pat_bindings_i2_def] >>
    Cases_on `store_lookup lnum s`>>
    fsrw_tac[DNF_ss][semanticPrimitivesTheory.store_lookup_def,EVERY_MEM,MEM_EL]) >>
  strip_tac >- ( rw[pmatch_i2_def,pat_bindings_i2_def]) >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- ( rw[pmatch_i2_def] >> rw[] ) >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- rw[pmatch_i2_def] >>
  strip_tac >- (rw[pmatch_i2_def,pat_bindings_i2_def] >> rw[]) >>
  strip_tac >- (
    rpt gen_tac >>
    strip_tac >>
    simp_tac(srw_ss())[pmatch_i2_def,pat_bindings_i2_def] >>
    Cases_on `pmatch_i2 s p v env` >> fs[] >>
    qmatch_assum_rename_tac `pmatch_i2 s p v env = Match env0`[] >>
    Cases_on `pmatch_list_i2 s ps vs env0` >> fs[] >>
    simp[Once pat_bindings_i2_acc,SimpRHS]) >>
  rw[pmatch_i2_def]

val pmatch_i2_dom = store_thm("pmatch_i2_dom",
  ``(∀s p v env env'.
      (pmatch_i2 s p v env = Match env') ⇒
      (MAP FST env' = pat_bindings_i2 p [] ++ (MAP FST env))) ∧
    (∀s ps vs env env'.
      (pmatch_list_i2 s ps vs env = Match env') ⇒
      (MAP FST env' = pats_bindings_i2 ps [] ++ MAP FST env))``,
    pmatch_tac)
*)

(*
val pmatch_list_i2_match_lengths = store_thm("pmatch_list_i2_match_lengths",
  ``∀ps vs s env env'. pmatch_list_i2 s ps vs env = Match env' ⇒ LENGTH ps = LENGTH vs``,
  Induct >> TRY(Cases >> simp[pmatch_i2_def] >> NO_TAC) >>
  gen_tac >> Cases >> simp[pmatch_i2_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >>
  rw[] >> res_tac)
*)

val pmatch_list_i2_any = store_thm("pmatch_list_i2_any",
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

val pmatch_list_i2_pairwise = store_thm("pmatch_list_i2_pairwise",
  ``∀ps vs s env env'. pmatch_list_i2 s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch_i2 s p v env = Match env') ps vs``,
  Induct >> Cases_on`vs` >> simp[pmatch_i2_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_list_i2_any])

val pat_to_i4_Match = prove(
  ``(∀p v s env env' env4 ck count genv.
       pmatch_i2 s p v env = Match env' ⇒
       evaluate_i4 ck
         (v_to_i4 v::env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pat_to_i4 p)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool T)))) ∧
    (∀n ps qs pps vs s env env' env4 ck count genv.
       pmatch_list_i2 s pps vs env = Match env' ∧
       (pps = qs ++ ps) ∧ (LENGTH qs = n) ⇒
       evaluate_i4 ck
         (vs_to_i4 vs ++ env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pats_to_i4 n ps)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool T))))``,
  ho_match_mp_tac pat_to_i4_ind >>
  rw[pmatch_i2_def,pat_to_i4_def]
  >- ( rw[Once evaluate_i4_cases] )
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
    rw[bigStepTheory.dec_count_def,map_count_store_genv_def] )
  >- (
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def] >>
    rw[PULL_EXISTS] >>
    rw[do_if_i4_def] >>
    fs[map_count_store_genv_def] >>
    match_mp_tac Let_Els_i4_correct >>
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt] >>
    first_x_assum match_mp_tac >>
    simp[LENGTH_NIL] >>
    metis_tac[])
  >- (
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def,PULL_EXISTS] >>
    fs[map_count_store_genv_def] >>
    fs[semanticPrimitivesTheory.store_lookup_def] >>
    rw[] >> fs[] >> simp[EL_MAP] >>
    first_x_assum match_mp_tac >>
    metis_tac[])
  >- (
    rw[pat_to_i4_def] >>
    rw[Once evaluate_i4_cases] ) >>
  rw[Once evaluate_i4_cases] >>
  rw[Once evaluate_i4_cases] >>
  rw[Once evaluate_i4_cases] >>
  imp_res_tac pmatch_list_i2_pairwise >>
  `∃ws v rs. (vs = ws ++ v::rs) ∧ LENGTH qs = LENGTH ws` by (
    qexists_tac`TAKE (LENGTH qs) vs` >>
    fs[EVERY2_EVERY] >> simp[LENGTH_TAKE] >>
    qexists_tac`HD (DROP (LENGTH qs) vs)` >>
    qexists_tac`TL (DROP (LENGTH qs) vs)` >>
    match_mp_tac EQ_TRANS  >>
    qexists_tac`TAKE (LENGTH qs) vs ++ DROP (LENGTH qs) vs` >>
    conj_tac >- metis_tac[TAKE_DROP] >>
    simp[] >>
    Cases_on`DROP (LENGTH qs) vs`>>simp[] >>
    fs[DROP_NIL] >>
    DECIDE_TAC ) >>
  rw[] >>
  simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
  qmatch_assum_abbrev_tac`LIST_REL R (l1 ++ l2) (l3 ++ l4)` >>
  `LIST_REL R l1 l3 ∧ LIST_REL R l2 l4` by (
    simp[EVERY2_APPEND] >> fs[EVERY2_EVERY] ) >>
  fs[Abbr`l2`,Abbr`l4`,Abbr`R`] >>
  first_x_assum(qspec_then`[]`mp_tac) >>
  disch_then(qx_choose_then`env1`strip_assume_tac) >>
  first_x_assum(qspecl_then[`v`,`s`,`[]`]mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac`Litv_i4 (Bool T)` >>
  fs[map_count_store_genv_def] >>
  simp[do_if_i4_def] >>
  Q.PAT_ABBREV_TAC`s2 = X:v_i4 count_store_genv` >>
  qexists_tac`s2` >>
  conj_tac >- (
    qunabbrev_tac`s2` >>
    metis_tac[] ) >>
  qunabbrev_tac`s2` >>
  REWRITE_TAC[Once rich_listTheory.CONS_APPEND] >>
  REWRITE_TAC[APPEND_ASSOC] >>
  `MAP v_to_i4 l3 ++ [v_to_i4 v] = MAP v_to_i4 (l3 ++ [v])` by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[GSYM MAP_APPEND] >>
  first_x_assum match_mp_tac >>
  qexists_tac`l1 ++ [p]` >>
  qexists_tac`env` >>
  REWRITE_TAC[GSYM (APPEND_ASSOC)] >>
  REWRITE_TAC[Once (GSYM rich_listTheory.CONS_APPEND)] >>
  REWRITE_TAC[GSYM (APPEND_ASSOC)] >>
  REWRITE_TAC[Once (GSYM rich_listTheory.CONS_APPEND)] >>
  simp[])

(*
val drop_def = Define`drop = DROP`
val pat_to_i4_correct = prove(
  ``(∀p v s env res env4 ck count genv.
       pmatch_i2 s p v env = res ∧ res ≠ Match_type_error ⇒
       evaluate_i4 ck
         (v_to_i4 v::env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pat_to_i4 p)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool (∃env'. res = Match env'))))) ∧
    (∀n ps qs pps vs s env env' res env4 ck count genv.
       pmatch_list_i2 s (TAKE n pps) (TAKE n vs) env = Match env' ∧
       pmatch_list_i2 s pps vs env = res ∧ res ≠ Match_type_error ∧
       (LENGTH ps = LENGTH vs) ∧ n ≤ LENGTH ps ⇒
       evaluate_i4 ck
         (vs_to_i4 vs ++ env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pats_to_i4 n ps)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool (∃env'. res = Match env')))))``,
  ho_match_mp_tac pat_to_i4_ind >>
  rw[pmatch_i2_def,pat_to_i4_def]
  >- ( rw[Once evaluate_i4_cases] )
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
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def] >>
    rw[PULL_EXISTS] >>
    rw[do_if_i4_def] >>
    fs[map_count_store_genv_def] >>
    TRY(simp[Once evaluate_i4_cases] >> NO_TAC) >>
    match_mp_tac Let_Els_i4_correct >>
    simp[LENGTH_NIL,TAKE_LENGTH_ID_rwt] >>
    fs[drop_def])
  >- (
    Cases_on`v`>>fs[pmatch_i2_def]>>pop_assum mp_tac >> rw[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def,PULL_EXISTS] >>
    fs[map_count_store_genv_def] >>
    fs[semanticPrimitivesTheory.store_lookup_def] >>
    rw[] >> fs[] >> simp[EL_MAP])
  >- (
    fs[LENGTH_NIL_SYM,drop_def] >> rw[pmatch_i2_def] >>
    rw[Once evaluate_i4_cases] )
  rw[Once evaluate_i4_cases] >>
  rw[Once evaluate_i4_cases] >>
  rw[Once evaluate_i4_cases] >>
  Cases_on`vs`>>fs[]
  imp_res_tac pmatch_list_i2_pairwise >>
  `∃ws v rs. (vs = ws ++ v::rs) ∧ LENGTH qs = LENGTH ws` by (
    qexists_tac`TAKE (LENGTH qs) vs` >>
    fs[EVERY2_EVERY] >> simp[LENGTH_TAKE] >>
    qexists_tac`HD (DROP (LENGTH qs) vs)` >>
    qexists_tac`TL (DROP (LENGTH qs) vs)` >>
    match_mp_tac EQ_TRANS  >>
    qexists_tac`TAKE (LENGTH qs) vs ++ DROP (LENGTH qs) vs` >>
    conj_tac >- metis_tac[TAKE_DROP] >>
    simp[] >>
    Cases_on`DROP (LENGTH qs) vs`>>simp[] >>
    fs[DROP_NIL] >>
    DECIDE_TAC ) >>
  rw[] >>
  simp[rich_listTheory.EL_APPEND2,rich_listTheory.EL_APPEND1] >>
  qmatch_assum_abbrev_tac`LIST_REL R (l1 ++ l2) (l3 ++ l4)` >>
  `LIST_REL R l1 l3 ∧ LIST_REL R l2 l4` by (
    simp[EVERY2_APPEND] >> fs[EVERY2_EVERY] ) >>
  fs[Abbr`l2`,Abbr`l4`,Abbr`R`] >>
  first_x_assum(qspec_then`[]`mp_tac) >>
  disch_then(qx_choose_then`env1`strip_assume_tac) >>
  first_x_assum(qspecl_then[`v`,`s`,`[]`]mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac`Litv_i4 (Bool T)` >>
  fs[map_count_store_genv_def] >>
  simp[do_if_i4_def] >>
  Q.PAT_ABBREV_TAC`s2 = X:v_i4 count_store_genv` >>
  qexists_tac`s2` >>
  conj_tac >- (
    qunabbrev_tac`s2` >>
    metis_tac[] ) >>
  qunabbrev_tac`s2` >>
  REWRITE_TAC[Once rich_listTheory.CONS_APPEND] >>
  REWRITE_TAC[APPEND_ASSOC] >>
  `MAP v_to_i4 l3 ++ [v_to_i4 v] = MAP v_to_i4 (l3 ++ [v])` by simp[] >>
  pop_assum SUBST1_TAC >>
  REWRITE_TAC[GSYM MAP_APPEND] >>
  first_x_assum match_mp_tac >>
  qexists_tac`l1 ++ [p]` >>
  qexists_tac`env` >>
  REWRITE_TAC[GSYM (APPEND_ASSOC)] >>
  REWRITE_TAC[Once (GSYM rich_listTheory.CONS_APPEND)] >>
  REWRITE_TAC[GSYM (APPEND_ASSOC)] >>
  REWRITE_TAC[Once (GSYM rich_listTheory.CONS_APPEND)] >>
  simp[])
*)

(*
val pat_to_i4_No_match = prove(
  ``(∀p v s env env4 ck count genv.
       pmatch_i2 s p v env = No_match ⇒
       evaluate_i4 ck
         (v_to_i4 v::env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pat_to_i4 p)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool F)))) ∧
    (∀n ps vs s env env4 ck count genv.
       n ≤ LENGTH ps ∧ (LENGTH ps = LENGTH vs) ∧
       pmatch_list_i2 s (DROP n ps) (DROP n vs) env = No_match ⇒
       evaluate_i4 ck
         (vs_to_i4 vs ++ env4)
         (map_count_store_genv v_to_i4 ((count,s),genv))
         (pats_to_i4 n ps)
         (map_count_store_genv v_to_i4 ((count,s),genv)
         ,Rval (Litv_i4 (Bool F))))``,
  ho_match_mp_tac pat_to_i4_ind >>
  rw[pmatch_i2_def,pat_to_i4_def] >- (
    Cases_on`v`>>fs[pmatch_i2_def]>>
    pop_assum mp_tac >> rw[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_app_i4_def] >>
    rw[do_eq_i4_def] >>
    rw[Once evaluate_i4_cases] >>
    fs[map_count_store_genv_def] >>
    rw[bigStepTheory.dec_count_def] )
  >- (
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_app_i4_def] >>
    Cases_on`v`>>fs[pmatch_i2_def]>>
    pop_assum mp_tac >> rw[LENGTH_NIL_SYM,pmatch_i2_def] >>
    rw[do_eq_i4_def] >>
    rw[Once evaluate_i4_cases] >>
    fs[map_count_store_genv_def] >>
    rw[bigStepTheory.dec_count_def] )
  >- (
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def] >>
    Cases_on`v`>>fs[pmatch_i2_def]>>
    pop_assum mp_tac >> rw[] >- (
      fs[LENGTH_NIL] >>
      simp[PULL_EXISTS] >>
      simp[do_if_i4_def] >>
      fs[map_count_store_genv_def] >>
      match_mp_tac Let_Els_i4_correct >>
      simp[LENGTH_NIL] >>
      simp[TAKE_LENGTH_ID_rwt] >>
      first_x_assum match_mp_tac >>
      metis_tac[] ) >>
    simp[PULL_EXISTS] >>
    simp[do_if_i4_def] >>
    simp[Once evaluate_i4_cases] >>
    simp[map_count_store_genv_def] )
  >- (
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[do_uapp_i4_def] >>
    Cases_on`v`>>fs[pmatch_i2_def]>>
    simp[PULL_EXISTS] >>
    fs[map_count_store_genv_def] >>
    fs[semanticPrimitivesTheory.store_lookup_def] >>
    rw[] >> fs[] >>
    simp[EL_MAP] >>
    first_x_assum match_mp_tac >>
    metis_tac[] )
  >- (
    fs[LENGTH_NIL_SYM] >>
    rfs[pmatch_i2_def] )
  >- (
    Cases_on`vs`>>fs[] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    rw[Once evaluate_i4_cases] >>
    fs[pmatch_i2_def] >>
    pop_assum mp_tac >> BasicProvers.CASE_TAC >- (
      qexists_tac`Litv_i4 (Bool F)` >>
      simp[do_if_i4_def] >>
      metis_tac[CONJUNCT1 evaluate_i4_rules] ) >>
    rw[] >>
    qexists_tac`Litv_i4 (Bool T)` >>
    rw[do_if_i4_def] >>
    imp_res_tac(CONJUNCT1 pat_to_i4_Match)


      res_tac >> pop_assum mp_tac >>
      simp[Once evaluate_i4_cases] >>
      simp[Once evaluate_i4_cases] >>
*)

val exp_to_i4_correct = store_thm("exp_to_i4_correct",
  ``(∀ck env s exp res. evaluate_i3 ck env s exp res ⇒
     (SND res ≠ Rerr Rtype_error) ∧ good_env_s_i2 env s ⇒
     evaluate_i4 ck
       (MAP (v_to_i4 o SND) env)
       (map_count_store_genv v_to_i4 s)
       (exp_to_i4 (MAP (SOME o FST) env) exp)
       (map_count_store_genv v_to_i4 (FST res)
       ,map_result v_to_i4 v_to_i4 (SND res))) ∧
    (∀ck env s exps ress. evaluate_list_i3 ck env s exps ress ⇒
     (SND ress ≠ Rerr Rtype_error) ∧ good_env_s_i2 env s ⇒
     evaluate_list_i4 ck
       (MAP (v_to_i4 o SND) env)
       (map_count_store_genv v_to_i4 s)
       (exps_to_i4 (MAP (SOME o FST) env) exps)
       (map_count_store_genv v_to_i4 (FST ress)
       ,map_result vs_to_i4 v_to_i4 (SND ress))) ∧
    (∀ck env s v pes ev res. evaluate_match_i3 ck env s v pes ev res ⇒
      (SND res ≠ Rerr Rtype_error) ∧ good_env_s_i2 env s ⇒
      evaluate_i4 ck
      (v_to_i4 v::(MAP (v_to_i4 o SND) env))
      (map_count_store_genv v_to_i4 s)
      (pes_to_i4 (NONE::(MAP (SOME o FST) env)) pes)
      (map_count_store_genv v_to_i4 (FST res)
      ,map_result v_to_i4 v_to_i4 (SND res)))``
  ho_match_mp_tac evaluate_i3_strongind >>
  strip_tac >- rw[Once evaluate_i4_cases] >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >> metis_tac[evaluate_i3_preserves_good,FST] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
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
    rw[] >> simp[Once evaluate_i4_cases] >>
    Cases_on`uop`>>
    fs[do_uapp_i3_def,do_uapp_i4_def,LET_THM,semanticPrimitivesTheory.store_alloc_def] >>
    rw[] >>
    pop_assum kall_tac >>
    TRY (pop_assum mp_tac >> BasicProvers.CASE_TAC) >>
    simp[semanticPrimitivesTheory.store_lookup_def] >> rw[] >>
    fs[map_count_store_genv_def] >>
    qmatch_assum_abbrev_tac`evaluate_i4 A B C D (((X,Y),Z),Rval V)` >>
    map_every qexists_tac[`V`,`Y`,`Z`] >>
    unabbrev_all_tac >> simp[EL_MAP] >>
    simp[LIST_EQ_REWRITE] >> rw[] >>
    simp[EL_MAP,EL_LUPDATE] >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    simp[Once evaluate_i4_cases] >> disj1_tac >>
    map_every qexists_tac[`v_to_i4 v1`,`v_to_i4 v2`] >>
    qmatch_assum_abbrev_tac`P ⇒ evaluate_i4 A B C D E` >>
    map_every qexists_tac[`B`,`D`] >>
    qmatch_assum_abbrev_tac`evaluate_i4 a b c d (e,Rval (v_to_i4 v1))` >>
    qexists_tac`e` >> unabbrev_all_tac >>
    fs[map_count_store_genv_def] >>
    qmatch_assum_abbrev_tac`p ⇒ evaluate_i4 a b c d (((e,f),g),Rval (v_to_i4 v2))` >>
    `p` by metis_tac[evaluate_i3_preserves_good,FST] >>
    map_every qexists_tac[`f`,`e`] >> qunabbrev_tac`p` >> fs[] >>
    qmatch_assum_abbrev_tac`q ⇒ evaluate_i4 A B ((C,D),E) G H` >>
    `good_v_i2 v1 ∧ q` by (
      unabbrev_all_tac >>
      imp_res_tac evaluate_i3_preserves_good >>
      imp_res_tac do_app_i2_preserves_good >>
      rfs[good_env_s_i2_def] ) >>
    fs[Abbr`q`] >>
    map_every qexists_tac[`D`,`E`] >> unabbrev_all_tac >>
    simp[] >>
    simp[do_app_i4_correct] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac evaluate_i3_preserves_good >>
    rfs[] >> fs[] >>
    qspecl_then[`Opapp`,`v1`,`v2`,`env`,`s3`]mp_tac do_app_i4_correct >>
    simp[] >> fs[map_count_store_genv_def] >> metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac evaluate_i3_preserves_good >>
    fs[] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    imp_res_tac evaluate_i3_preserves_good >>
    fs[do_if_i2_def,do_if_i4_def] >>
    disj1_tac >>
    qexists_tac`v_to_i4 v` >>
    Cases_on`v`>>fs[]>>
    Cases_on`l`>>fs[]>>
    Cases_on`b`>>fs[]>>
    metis_tac[]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    metis_tac[evaluate_i3_preserves_good,FST] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    fs[libTheory.bind_def] >>
    disj1_tac >>
    imp_res_tac evaluate_i3_preserves_good >>
    fs[good_env_s_i2_def] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    `good_env_s_i2 (build_rec_env_i2 funs env env) s` by (
      simp[build_rec_env_i2_MAP] >>
      fs[good_env_s_i2_def,EVERY_MAP,EVERY_MEM,FST_triple,UNCURRY] >>
      simp[MEM_MAP] >> metis_tac[] ) >>
    fs[] >>
    qmatch_abbrev_tac`evaluate_i4 a b c d e` >>
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
    rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    simp[Once evaluate_i4_cases] >>
    simp[map_count_store_genv_def,MAP_GENLIST,combinTheory.o_DEF] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    metis_tac[evaluate_i3_preserves_good,FST] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    metis_tac[evaluate_i3_preserves_good,FST] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >>
    cheat (* false - want i3 pattern matches to be exhaustive but they aren't *) ) >>
  strip_tac >- (
    rw[] >>
    simp[Once evaluate_i4_cases] >>
    disj1_tac >>
    qexists_tac`Litv_i4 (Bool T)` >>
    simp[do_if_i4_def] >>
    imp_res_tac(CONJUNCT1 pat_to_i4_Match) >>
    Q.PAT_ABBREV_TAC`s2 = X:v_i4 count_store_genv` >>
    qexists_tac`s2` >> simp[Abbr`s2`] >>
    cheat ) >>
  strip_tac >- (
    rw[] >> cheat ) >>
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
val _ = Parse.overload_on("isNONEtag", ``λv. Uapp_i4 (Tag_eq_i4 1) (Var_local_i4 v)``)
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
