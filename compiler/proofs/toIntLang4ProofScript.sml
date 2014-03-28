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
val _ = export_rewrites["exp_to_i4_def","intLang4.uop_to_i4_def"]

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

val good_v_i2_def = Define`
  (good_v_i2 (Litv_i2 _) ⇔ T) ∧
  (good_v_i2 (Conv_i2 _ _) ⇔ T) ∧
  (good_v_i2 (Closure_i2 _ _ _) ⇔ T) ∧
  (good_v_i2 (Recclosure_i2 _ funs f) ⇔
   ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v_i2 (Loc_i2 _) ⇔ T) ∧
  (good_vs_i2 [] ⇔ T) ∧
  (good_vs_i2 (v::vs) ⇔ good_v_i2 v ∧ good_vs_i2 vs)`
val _ = export_rewrites["good_v_i2_def"]

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
  imp_res_tac find_index_LESS_LENGTH >> fs[[L_MAP])
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

(*
val IS_SOME_exists = prove(
  ``IS_SOME X ⇔ ∃x. X = SOME x``,
  Cases_on`X`>>simp[])

val do_app_i4_SOME = prove(
  ``∀op v1 v2 env s env' s' exp'.
     (do_app_i2 env s op v1 v2 = SOME (env',s',exp')) ⇒
     (do_app_i4 (MAP (v_to_i4 o SND) env) (MAP v_to_i4 s) op (v_to_i4 v1) (v_to_i4 v2) =
       SOME (MAP (v_to_i4 o SND) env', MAP v_to_i4 s', exp_to_i4 (MAP (SOME o FST) env') exp'))``,
  Cases_on`op`>>TRY(Cases_on`o':opn`)>>Cases_on`v1`>>TRY(Cases_on`l:lit`)>>Cases_on`v2`>>TRY(Cases_on`l:lit`)>>
  simp[do_app_i2_def,do_app_i4_def,exn_env_i4_def,exn_env_i2_def
      ,libTheory.emp_def,libTheory.bind_def,do_eq_i4_correct,do_eq_i4_def]>>rw[]>>
  fs[find_recfun_ALOOKUP,funs_to_i4_MAP] >- (
    BasicProvers.CASE_TAC >> simp[] >> fs[] >> rw[]) >>
  pop_assum mp_tac >> BasicProvers.CASE_TAC >>
  fs[optionTheory.option_case_compute,IS_SOME_exists] >> rfs[pair_CASE_def] >>
  simp[the_less_rwt] >>
  imp_res_tac ALOOKUP_find_index_SOME >>
  rw[build_rec_env_i4_def,build_rec_env_i2_MAP] >>
  simp[EL_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
  rw[LIST_EQ_REWRITE] >>
  simp[EL_MAP,UNCURRY,funs_to_i4_MAP,MAP_MAP_o]
*)

(*
val exp_to_i4_correct = store_thm("exp_to_i4_correct",
  ``(∀ck env s exp res. evaluate_i3 ck env s exp res ⇒
     (SND res ≠ Rerr Rtype_error) ∧ every_result good_v_i2 good_v_i2 (SND res) ⇒
     evaluate_i4 ck
       (MAP (v_to_i4 o SND) env)
       (map_count_store_genv v_to_i4 s)
       (exp_to_i4 (MAP (SOME o FST) env) exp)
       (map_count_store_genv v_to_i4 (FST res)
       ,map_result v_to_i4 v_to_i4 (SND res))) ∧
    (∀ck env s exps ress. evaluate_list_i3 ck env s exps ress ⇒
     (SND ress ≠ Rerr Rtype_error) ∧ every_result good_vs_i2 good_v_i2 (SND ress) ⇒
     evaluate_list_i4 ck
       (MAP (v_to_i4 o SND) env)
       (map_count_store_genv v_to_i4 s)
       (exps_to_i4 (MAP (SOME o FST) env) exps)
       (map_count_store_genv v_to_i4 (FST ress)
       ,map_result vs_to_i4 v_to_i4 (SND ress))) ∧
    (∀ck env s v pes ev res. evaluate_match_i3 ck env s v pes ev res ⇒
      (SND res ≠ Rerr Rtype_error) ∧ every_result good_v_i2 good_v_i2 (SND res) ⇒
      evaluate_i4 ck
      (v_to_i4 v::(MAP (v_to_i4 o SND) env))
      (map_count_store_genv v_to_i4 s)
      (pes_to_i4 (NONE::(MAP (SOME o FST) env)) pes)
      (map_count_store_genv v_to_i4 (FST res)
      ,map_result v_to_i4 v_to_i4 (SND res)))``
  ho_match_mp_tac evaluate_i3_ind >>
  strip_tac >- rw[Once evaluate_i4_cases] >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- ( rw[] >> simp[Once evaluate_i4_cases] ) >>
  strip_tac >- (
    rw[] >> simp[Once evaluate_i4_cases] >> metis_tac[] ) >>
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
    qmatch_assum_abbrev_tac`evaluate_i4 A B C D E` >>
    map_every qexists_tac[`B`,`D`] >>
    qmatch_assum_abbrev_tac`evaluate_i4 a b c d (e,Rval (v_to_i4 v1))` >>
    qexists_tac`e` >> unabbrev_all_tac >>
    fs[map_count_store_genv_def] >>
    qmatch_assum_abbrev_tac`evaluate_i4 a b c d (((e,f),g),Rval (v_to_i4 v2))` >>
    map_every qexists_tac[`f`,`e`] >>
    qmatch_assum_abbrev_tac`evaluate_i4 A B ((C,D),E) G H` >>
    map_every qexists_tac[`D`,`E`] >> unabbrev_all_tac >>
    simp[] >>
    qpat_assum`do_app_i2 A B C D E = G`mp_tac >>
*)


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
val tm = rhs(concl th)

*)

val _ = export_theory()
