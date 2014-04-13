open preamble;
open alistTheory optionTheory rich_listTheory;
open miscLib miscTheory;
open astTheory;
open semanticPrimitivesTheory;
open libTheory;
open libPropsTheory;
open conLangTheory;
open decLangTheory;
open exhLangTheory;
open evalPropsTheory;
open compilerTerminationTheory;

val _ = new_theory "exhLangProof";

val v_to_exh_def = tDefine "v_to_exh" `
(v_to_exh exh (Litv_i2 l) =
  Litv_exh l) ∧
(v_to_exh exh (Conv_i2 t vs) =
  Conv_exh (FST t) (vs_to_exh exh vs)) ∧
(v_to_exh exh (Closure_i2 env x e) =
  Closure_exh (env_to_exh exh env) x (exp_to_exh exh e)) ∧
(v_to_exh exh (Recclosure_i2 env funs x) =
  Recclosure_exh (env_to_exh exh env) (funs_to_exh exh funs) x) ∧
(v_to_exh exh (Loc_i2 l) =
  Loc_exh l) ∧
(vs_to_exh exh [] = []) ∧
(vs_to_exh exh (v::vs) = v_to_exh exh v :: vs_to_exh exh vs) ∧
(env_to_exh exh [] = []) ∧
(env_to_exh exh ((x,v)::env) = (x,v_to_exh exh v) :: env_to_exh exh env)`
(WF_REL_TAC`inv_image $< (\x. case x of
  | INL (_,v) => v_i2_size v
  | INR (INL (_,vs)) => v_i23_size vs
  | INR (INR (_,env)) => v_i21_size env)`)

val store_to_exh_def = Define `
store_to_exh exh (s,genv) =
  ((FST s, MAP (v_to_exh exh) (SND s)), MAP (OPTION_MAP (v_to_exh exh)) genv)`;

val result_to_exh_def = Define `
(result_to_exh r exh (s,res) =
  (store_to_exh exh s,
   case res of
     | Rval v => Rval (r exh v)
     | Rerr (Rraise v) => Rerr (Rraise (v_to_exh exh v))
     | Rerr Rtimeout_error => Rerr Rtimeout_error
     | Rerr Rtype_error => Rerr Rtype_error))`;

val exists_match_def = Define `
exists_match exh s ps v ⇔
  !env. ?p. MEM p ps ∧ pmatch_i2 exh s p v env ≠ No_match`;

val pmatch_list_i2_all_vars_not_No_match = prove(
  ``∀l1 l2 a b c. EVERY is_var l1 ⇒ pmatch_list_i2 a b l1 l2 c ≠ No_match``,
  Induct >> Cases_on`l2` >> simp[pmatch_i2_def,is_var_def] >>
  Cases >> simp[pmatch_i2_def])

val get_tags_lemma = prove(
  ``∀ps ts. get_tags ps = SOME ts ⇒
      (∀p. MEM p ps ⇒ ∃t x vs. (p = Pcon_i2 (t,x) vs) ∧ EVERY is_var vs ∧ MEM t ts) ∧
      (∀t. MEM t ts ⇒ ∃x vs. MEM (Pcon_i2 (t,x) vs) ps ∧ EVERY is_var vs)``,
  Induct >> simp[get_tags_def] >> Cases >> simp[] >>
  every_case_tac >> rw[] >> fs[] >> metis_tac[])

val pmatch_i2_Pcon_No_match = prove(
  ``EVERY is_var ps ⇒
    ((pmatch_i2 exh s (Pcon_i2 (c,SOME (TypeId t)) ps) v env = No_match) ⇔
     ∃cv vs tags.
       v = Conv_i2 (cv,SOME (TypeId t)) vs ∧
       FLOOKUP exh t = SOME tags ∧
       MEM c tags ∧ MEM cv tags ∧
       c ≠ cv)``,
  Cases_on`v`>>rw[pmatch_i2_def]>>
  PairCases_on`p`>>
  Cases_on`p1`>>simp[pmatch_i2_def]>>
  Cases_on`x`>>simp[pmatch_i2_def]>>
  rw[] >> BasicProvers.CASE_TAC >> rw[] >>
  metis_tac[pmatch_list_i2_all_vars_not_No_match])

val exh_to_exists_match = Q.prove (
`!exh ps. exhaustive_match exh ps ⇒ !s v. exists_match exh s ps v`,
 rw [exhaustive_match_def, exists_match_def] >>
 every_case_tac >>
 fs [get_tags_def, pmatch_i2_def]
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     cases_on `l` >>
     fs [lit_same_type_def])
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     PairCases_on `p` >>
     Cases_on `p1` >>
     fs [pmatch_i2_def] >>
     rw[] >>
     metis_tac[pmatch_list_i2_all_vars_not_No_match])
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     PairCases_on `p` >>
     Cases_on `p1` >>
     fs [pmatch_i2_def] >>
     Cases_on `x` >>
     fs [pmatch_i2_def])
 >- (cases_on `v` >>
     rw [pmatch_i2_def] >>
     every_case_tac)
 >- (every_case_tac >>
     fs [] >> rw[] >>
     Q.PAT_ABBREV_TAC`pp1 = Pcon_i2 X l` >>
     Q.PAT_ABBREV_TAC`pp2 = Pcon_i2 X Y` >>
     qmatch_assum_rename_tac`Abbrev(pp2 = Pcon_i2 (a,b) c)`[] >>
     srw_tac[boolSimps.DNF_ss][]>>
     simp[Abbr`pp1`,pmatch_i2_Pcon_No_match]>>
     simp[METIS_PROVE[]``a \/ b <=> ~a ==> b``] >>
     strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
     Cases_on`b`>>simp[Abbr`pp2`,pmatch_i2_def]>>
     Cases_on`x`>>simp[pmatch_i2_def]>>
     rw[] >- metis_tac[pmatch_list_i2_all_vars_not_No_match] >>
     qmatch_assum_rename_tac`get_tags ws = SOME ts`[] >>
     imp_res_tac get_tags_lemma >>
     fs[EXTENSION] >>
     `MEM cv ts` by metis_tac[] >>
     first_x_assum(qspec_then`cv`mp_tac) >>
     simp[] >> strip_tac >>
     qmatch_assum_abbrev_tac`MEM p ws` >>
     qexists_tac`p` >>
     simp[Abbr`p`] >>
     Cases_on`x`>>simp[pmatch_i2_Pcon_No_match,pmatch_i2_def] >>
     qmatch_assum_rename_tac`MEM (Pcon_i2 (cv, SOME z) ps) ws`[] >>
     Cases_on`z`>>simp[pmatch_i2_def] >> rw[] >>
     metis_tac[pmatch_list_i2_all_vars_not_No_match]))

val vs_to_exh_MAP = prove(
  ``∀vs exh. vs_to_exh exh vs = MAP (v_to_exh exh) vs``,
  Induct >> simp[v_to_exh_def])

val find_recfun_funs_to_exh = prove(
  ``∀ls f exh. find_recfun f (funs_to_exh exh ls) =
               OPTION_MAP (λ(x,y). (x,exp_to_exh exh y)) (find_recfun f ls)``,
  Induct >> simp[] >- (
    simp[exp_to_exh_def,Once find_recfun_def] >>
    simp[Once find_recfun_def] ) >>
  qx_gen_tac`p`>>PairCases_on`p`>>
  simp[exp_to_exh_def] >>
  simp[Once find_recfun_def] >>
  rw[] >- (
    rw[Once find_recfun_def] ) >>
  rw[Once find_recfun_def,SimpRHS] )

val build_rec_env_i2_MAP = prove(
  ``build_rec_env_i2 funs cle env = MAP (λ(f,cdr). (f, (Recclosure_i2 cle funs f))) funs ++ env``,
  rw[build_rec_env_i2_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val build_rec_env_exh_MAP = prove(
  ``build_rec_env_exh funs cle env = MAP (λ(f,cdr). (f, (Recclosure_exh cle funs f))) funs ++ env``,
  rw[build_rec_env_exh_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val env_to_exh_MAP = prove(
  ``env_to_exh exh env = MAP (λ(x,y). (x, v_to_exh exh y)) env``,
  Induct_on`env`>>simp[v_to_exh_def]>>Cases>>simp[v_to_exh_def])

val funs_to_exh_MAP = prove(
  ``funs_to_exh exh ls = MAP (λ(x,y,z). (x,y,exp_to_exh exh z)) ls``,
  Induct_on`ls`>>simp[exp_to_exh_def]>>qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_exh_def])

val env_to_exh_build_rec_env_i2 = prove(
  ``∀l1 l2 l3 exh.
    env_to_exh exh (build_rec_env_i2 l1 l2 l3) =
    build_rec_env_exh (funs_to_exh exh l1) (env_to_exh exh l2) (env_to_exh exh l3)``,
  simp[build_rec_env_i2_MAP,build_rec_env_exh_MAP,env_to_exh_MAP,funs_to_exh_MAP
      ,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,v_to_exh_def])

val _ = augment_srw_ss[rewrites[vs_to_exh_MAP,find_recfun_funs_to_exh,env_to_exh_build_rec_env_i2]]

val do_eq_exh_correct = prove(
  ``(∀v1 v2 exh.
      do_eq_i2 v1 v2 ≠ Eq_type_error ⇒
      do_eq_exh (v_to_exh exh v1) (v_to_exh exh v2) =
                 do_eq_i2 v1 v2) ∧
    (∀vs1 vs2 exh.
      do_eq_list_i2 vs1 vs2 ≠ Eq_type_error ⇒
      do_eq_list_exh (vs_to_exh exh vs1) (vs_to_exh exh vs2) =
                   do_eq_list_i2 vs1 vs2)``,
  ho_match_mp_tac do_eq_i2_ind >>
  reverse(rw[do_eq_i2_def,do_eq_exh_def,v_to_exh_def]) >>
  rw[] >> fs[] >> every_case_tac >> fs[] )
val _ = augment_srw_ss[rewrites[do_eq_exh_correct]]

val evaluate_exh_lit = prove(
  ``evaluate_exh ck env csg (Lit_exh l) res ⇔ (res = (csg,Rval (Litv_exh l)))``,
  simp[Once evaluate_exh_cases])

val if_cons = prove(
  ``(if b then a::c1 else a::c2) = a::(if b then c1 else c2)``,
  rw[])

val exp_to_exh_correct = Q.store_thm ("exp_to_exh_correct",
`(!ck env s e r.
  evaluate_i3 ck env s e r
  ⇒
  !exh env'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ⇒
    evaluate_exh ck (env_to_exh exh env') (store_to_exh exh s) (exp_to_exh exh e) (result_to_exh v_to_exh exh r)) ∧
 (!ck env s es r.
  evaluate_list_i3 ck env s es r
  ⇒
  !exh env'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ⇒
    evaluate_list_exh ck (env_to_exh exh env') (store_to_exh exh s) (exps_to_exh exh es) (result_to_exh vs_to_exh exh r)) ∧
 (!ck env s v pes err_v r.
  evaluate_match_i3 ck env s v pes err_v r
  ⇒
  !exh env' pes' is_handle.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    (is_handle ⇒ err_v = v) ∧
    (¬is_handle ⇒ err_v = Conv_i2 (bind_tag, SOME(TypeExn(Short "Bind"))) []) ∧
    (pes' = add_default is_handle F pes ∨
     exists_match exh (SND (FST s)) (MAP FST pes) v ∧
     pes' = add_default is_handle T pes)
     ⇒
    evaluate_match_exh ck (env_to_exh exh env') (store_to_exh exh s) (v_to_exh exh v)
                          (pat_exp_to_exh exh pes')
                          (result_to_exh v_to_exh exh r))`,
 ho_match_mp_tac evaluate_i3_ind >>
 rw [exp_to_exh_def, v_to_exh_def, result_to_exh_def] >>
 ONCE_REWRITE_TAC [evaluate_exh_cases] >>
 fs [v_to_exh_def, result_to_exh_def, store_to_exh_def] >>
 TRY (Cases_on `err`) >>
 fs [] >>
 rw []
 >- (cases_on `exhaustive_match exh (MAP FST pes)` >>
     fs [] >>
     metis_tac [pair_CASES, exh_to_exists_match])
 >- (induct_on `env` >>
     rw [] >>
     PairCases_on `h` >>
     fs [v_to_exh_def] >>
     rw [] >>
     fs [])
 >- (`n < LENGTH genv` by decide_tac >>
     rw [EL_MAP])
 >- (fs [do_uapp_exh_def, do_uapp_i3_def] >>
     every_case_tac >>
     fs [v_to_exh_def] >>
     rw []
     >- (MAP_EVERY qexists_tac [`Loc_exh n`, `MAP (v_to_exh exh) s2`] >>
         rw [] >>
         fs [store_lookup_def, EL_MAP])
     >- (fs [LET_THM, store_alloc_def] >>
         rw [v_to_exh_def])
     >- (MAP_EVERY qexists_tac [`v_to_exh exh v`, `MAP (v_to_exh exh) s2`, `MAP (OPTION_MAP (v_to_exh exh)) genv2`] >>
         rw [LUPDATE_MAP, EL_MAP, v_to_exh_def]))
 >- (disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[do_app_i2_def] >>
     every_case_tac >>
     fs[do_app_exh_def,v_to_exh_def,do_eq_i2_def] >>
     rw[] >> fs[] >>
     fs[exp_to_exh_def,exn_env_i2_def] >>
     fs[v_to_exh_def,bind_def,emp_def] >>
     fs[store_assign_def,evaluate_exh_lit] >>
     rw[LUPDATE_MAP,v_to_exh_def])
 >- (disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[do_app_i2_def] >>
     every_case_tac >>
     fs[do_app_exh_def,v_to_exh_def,do_eq_i2_def] >>
     rw[] >> fs[] >>
     fs[exp_to_exh_def,exn_env_i2_def] >>
     fs[v_to_exh_def,bind_def,emp_def] >>
     fs[store_assign_def,evaluate_exh_lit] >>
     rw[LUPDATE_MAP,v_to_exh_def])
 >- (disj2_tac >> disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[do_app_i2_def] >>
     every_case_tac >> fs[v_to_exh_def,do_app_exh_def] )
 >- metis_tac []
 >- metis_tac []
 >- (fs [do_if_i2_def, do_if_exh_def] >>
     every_case_tac >>
     fs [] >>
     rw [] >>
     res_tac >>
     fs [] >>
     disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     simp[v_to_exh_def])
 >- (res_tac >>
     fs [] >>
     cases_on `exhaustive_match exh (MAP FST pes)` >>
     fs []  >>
     metis_tac [exh_to_exists_match])
 >- (
   disj1_tac >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   fs[opt_bind_def] >> every_case_tac >> fs[v_to_exh_def] )
 >- (
   simp[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
   fs[ETA_AX,FST_triple] )
 >- (induct_on `n` >>
     rw [GENLIST])
 >- metis_tac []
 >- metis_tac []
 >- metis_tac []
 >- (
     rw [add_default_def, exp_to_exh_def, pat_bindings_exh_def, pat_to_exh_def, pmatch_exh_def] >>
     fs [] >>
     ONCE_REWRITE_TAC [evaluate_exh_cases] >>
     rw [] >>
     ONCE_REWRITE_TAC [evaluate_exh_cases] >>
     rw [v_to_exh_def] >>
     ONCE_REWRITE_TAC [evaluate_exh_cases] >>
     rw [lookup_def,bind_def] >>
     CONV_TAC SWAP_EXISTS_CONV >>
     rw[GSYM EXISTS_PROD])
 >- fs [exists_match_def]
 >- (
   disj2_tac >>
   disj1_tac >>
   simp[add_default_def] >>
   simp[if_cons,exp_to_exh_def] >>
   cheat )
 >- (rw [add_default_def, exp_to_exh_def] >>
     disj1_tac >>
     cheat)
 >- (rw[add_default_def, exp_to_exh_def] >>
     cheat )
 >- cheat);

val _ = export_theory ();
