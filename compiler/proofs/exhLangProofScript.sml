open preamble boolSimps;
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

val (v_to_exh_rules, v_to_exh_ind, v_to_exh_cases) = Hol_reln `
(!exh l.
  v_to_exh exh (Litv_i2 l) (Litv_exh l)) ∧
(!exh t vs vs'.
  vs_to_exh exh vs vs'
  ⇒
  v_to_exh exh (Conv_i2 t vs) (Conv_exh (FST t) vs')) ∧
(!exh env x e env' exh'.
  exh' SUBMAP exh ∧
  env_to_exh exh' env env'
  ⇒
  v_to_exh exh (Closure_i2 env x e) (Closure_exh env' x (exp_to_exh exh' e))) ∧
(!exh env x funs exh'.
  exh' SUBMAP exh ∧
  env_to_exh exh' env env'
  ⇒
  v_to_exh exh (Recclosure_i2 env funs x) (Recclosure_exh env' (funs_to_exh exh' funs) x)) ∧
(!exh l.
  v_to_exh exh (Loc_i2 l) (Loc_exh l)) ∧
(!exh.
  vs_to_exh exh [] []) ∧
(!exh v v' vs vs'.
  v_to_exh exh v v' ∧
  vs_to_exh exh vs vs'
  ⇒
  vs_to_exh exh (v::vs) (v'::vs')) ∧
(!exh.
  env_to_exh exh [] []) ∧
(!exh x v v' env env'.
  v_to_exh exh v v' ∧
  env_to_exh exh env env'
  ⇒
  env_to_exh exh ((x,v)::env) ((x,v')::env'))`;

val v_to_exh_eqn = Q.prove (
`(!exh l v.
  v_to_exh exh (Litv_i2 l) v ⇔
   v = Litv_exh l) ∧
 (!exh t vs v.
  v_to_exh exh (Conv_i2 t vs) v ⇔
   ?vs'.
    vs_to_exh exh vs vs' ∧
    v = Conv_exh (FST t) vs') ∧
 (!exh l.
  v_to_exh exh (Loc_i2 l) v ⇔
   v = Loc_exh l) ∧
 (!exh vs. vs_to_exh exh [] vs ⇔ vs = []) ∧
 (!exh v vs vs'. 
  vs_to_exh exh (v::vs) vs' ⇔ 
  ?v' vs''. 
    vs' = v'::vs'' ∧
    v_to_exh exh v v' ∧
    vs_to_exh exh vs vs'') ∧
 (!exh env. env_to_exh exh [] env ⇔ env = []) ∧
 (!exh x v env env'.
  env_to_exh exh ((x,v)::env) env' ⇔ 
  ?v' env''.
    env' = (x,v') :: env'' ∧
    v_to_exh exh v v' ∧
    env_to_exh exh env env'')`,
 rw [] >>
 rw [Once v_to_exh_cases] >>
 metis_tac []);

val store_to_exh_def = Define `
store_to_exh exh (s,genv) (s_exh,genv_exh) ⇔
  FST s = FST s_exh ∧
  LIST_REL (v_to_exh exh) (SND s) (SND s_exh) ∧
  LIST_REL (OPTION_REL (v_to_exh exh)) genv genv_exh`;

val (result_to_exh_rules, result_to_exh_ind, result_to_exh_cases) = Hol_reln `
(∀exh v v' s s'.
  f exh v v' ∧
  store_to_exh exh s s'
  ⇒
  result_to_exh f exh (s,Rval v) (s',Rval v')) ∧
(∀exh v v' s s'.
  v_to_exh exh v v' ∧
  store_to_exh exh s s'
  ⇒
  result_to_exh f exh (s,Rerr (Rraise v)) (s',Rerr (Rraise v'))) ∧
(!exh s s'.
  store_to_exh exh s s'
  ⇒
  result_to_exh f exh (s,Rerr Rtimeout_error) (s',Rerr Rtimeout_error)) ∧
(!exh s s'.
  store_to_exh exh s s'
  ⇒
  result_to_exh f exh (s,Rerr Rtype_error) (s',Rerr Rtype_error))`;

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

val vs_to_exh_LIST_REL = prove(
  ``∀vs vs' exh. vs_to_exh exh vs vs' = LIST_REL (v_to_exh exh) vs vs'``,
  Induct >> simp[v_to_exh_eqn])

val funs_to_exh_MAP = prove(
  ``funs_to_exh exh ls = MAP (λ(x,y,z). (x,y,exp_to_exh exh z)) ls``,
  Induct_on`ls`>>simp[exp_to_exh_def]>>qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_exh_def]);

val find_recfun_funs_to_exh = prove(
  ``∀ls f exh. find_recfun f (funs_to_exh exh ls) =
               OPTION_MAP (λ(x,y). (x,exp_to_exh exh y)) (find_recfun f ls)``,
  Induct >> simp[funs_to_exh_MAP] >- (
    simp[find_recfun_def] ) >>
  simp[Once find_recfun_def] >>
  simp[Once find_recfun_def,SimpRHS] >>
  rpt gen_tac >>
  every_case_tac >>
  simp[] >> fs[funs_to_exh_MAP]);

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

val env_to_exh_LIST_REL = Q.prove(
  `!exh env env'. env_to_exh exh env env' = LIST_REL (λ(x,y) (x',y'). x = x' ∧ v_to_exh exh y y') env env'`,
  Induct_on`env`>>simp[v_to_exh_eqn]>>Cases>>simp[v_to_exh_eqn] >>
  rw [EXISTS_PROD]);

  (*
val env_to_exh_build_rec_env_i2 = prove(
  ``∀l1 l2 l3 exh.
    env_to_exh exh (build_rec_env_i2 l1 l2 l3) =
    build_rec_env_exh (funs_to_exh exh l1) (env_to_exh exh l2) (env_to_exh exh l3)``,
  simp[build_rec_env_i2_MAP,build_rec_env_exh_MAP,env_to_exh_MAP,funs_to_exh_MAP
      ,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,v_to_exh_eqn])
      *)

val _ = augment_srw_ss[rewrites[vs_to_exh_LIST_REL,find_recfun_funs_to_exh(*,env_to_exh_build_rec_env_i2*)]]

val do_eq_exh_correct = Q.prove (
`(!v1 v2 tagenv r v1_exh v2_exh exh.
  do_eq_i2 v1 v2 = r ∧
  v_to_exh exh v1 v1_exh ∧
  v_to_exh exh v2 v2_exh
  ⇒
  do_eq_exh v1_exh v2_exh = r) ∧
 (!vs1 vs2 tagenv r vs1_exh vs2_exh exh.
  do_eq_list_i2 vs1 vs2 = r ∧
  vs_to_exh exh vs1 vs1_exh ∧
  vs_to_exh exh vs2 vs2_exh
  ⇒
  do_eq_list_exh vs1_exh vs2_exh = r)`,
 ho_match_mp_tac do_eq_i2_ind >>
 reverse(rw[do_eq_exh_def,do_eq_i2_def,v_to_exh_eqn]) >>
 rw[v_to_exh_eqn, do_eq_exh_def] >> 
 fs[do_eq_exh_def]
 >- (every_case_tac >>
     rw [] >>
     fs [] >>
     metis_tac [eq_result_distinct, eq_result_11]) >>
 fs [Once v_to_exh_cases] >>
 rw [do_eq_exh_def] >>
 fs [] >>
 metis_tac [LIST_REL_LENGTH]);
 
  (*
val _ = augment_srw_ss[rewrites[do_eq_exh_correct]]
*)


val evaluate_exh_lit = prove(
  ``evaluate_exh ck env csg (Lit_exh l) res ⇔ (res = (csg,Rval (Litv_exh l)))``,
  simp[Once evaluate_exh_cases])

val if_cons = prove(
  ``(if b then a::c1 else a::c2) = a::(if b then c1 else c2)``,
  rw[])

val match_result_to_exh_def = Define
`(match_result_to_exh exh (Match env) (Match env_exh) ⇔
   env_to_exh exh env env_exh) ∧
 (match_result_to_exh exh No_match No_match = T) ∧
 (match_result_to_exh exh Match_type_error Match_type_error = T) ∧
 (match_result_to_exh exh _ _ = F)`;

val match_result_error = Q.prove (
`(!exh r. match_result_to_exh exh r Match_type_error ⇔ r = Match_type_error) ∧
 (!exh r. match_result_to_exh exh Match_type_error r ⇔ r = Match_type_error)`,
 rw [] >>
 cases_on `r` >>
 rw [match_result_to_exh_def]);

val match_result_nomatch = Q.prove (
`(!exh r. match_result_to_exh exh r No_match ⇔ r = No_match) ∧
 (!exh r. match_result_to_exh exh No_match r ⇔ r = No_match)`,
 rw [] >>
 cases_on `r` >>
 rw [match_result_to_exh_def]);

val pmatch_exh_correct = Q.prove (
`(!exh s p v env r env_exh s_exh v_exh.
  r ≠ Match_type_error ∧
  pmatch_i2 exh s p v env = r ∧
  vs_to_exh exh s s_exh ∧
  v_to_exh exh v v_exh ∧
  env_to_exh exh env env_exh
  ⇒
  ?r_exh.
    pmatch_exh s_exh (pat_to_exh p) v_exh env_exh = r_exh ∧
    match_result_to_exh exh r r_exh) ∧
 (!exh s ps vs env r env_exh s_exh vs_exh.
  r ≠ Match_type_error ∧
  pmatch_list_i2 exh s ps vs env = r ∧
  vs_to_exh exh s s_exh ∧
  vs_to_exh exh vs vs_exh ∧
  env_to_exh exh env env_exh
  ⇒
  ?r_exh.
    pmatch_list_exh s_exh (MAP pat_to_exh ps) vs_exh env_exh = r_exh ∧
    match_result_to_exh exh r r_exh)`,
 ho_match_mp_tac pmatch_i2_ind >>
 rw [pmatch_i2_def, pmatch_exh_def, pat_to_exh_def, match_result_to_exh_def] >>
 fs [match_result_to_exh_def, bind_def, v_to_exh_eqn] >>
 rw [pmatch_exh_def, match_result_to_exh_def, match_result_error] >>
 imp_res_tac LIST_REL_LENGTH >>
 fs []
 >- metis_tac []
 >- (every_case_tac >>
     fs [] >>
     metis_tac [])
 >- (every_case_tac >>
     fs [] >>
     metis_tac [])
 >- (every_case_tac >>
     fs [match_result_to_exh_def])
 >- metis_tac []
 >- (every_case_tac >>
     fs [match_result_error, store_lookup_def, LIST_REL_EL_EQN] >>
     metis_tac [])
 >- (every_case_tac >>
     rw [match_result_to_exh_def] >>
     res_tac >>
     fs [match_result_nomatch] >>
     cases_on `pmatch_exh s_exh (pat_to_exh p) y env_exh` >>
     fs [match_result_to_exh_def] >>
     metis_tac []));

val pat_bindings_exh_correct = prove(
  ``(∀p ls. pat_bindings_exh (pat_to_exh p) ls = pat_bindings_i2 p ls) ∧
    (∀ps ls. pats_bindings_exh (MAP pat_to_exh ps) ls = pats_bindings_i2 ps ls)``,
  ho_match_mp_tac(TypeBase.induction_of(``:pat_i2``)) >>
  simp[pat_bindings_i2_def,pat_bindings_exh_def,pat_to_exh_def] >>
  rw[] >> cases_on`p` >> rw[pat_to_exh_def,pat_bindings_exh_def,ETA_AX])

val pmatch_i2_any_match = store_thm("pmatch_i2_any_match",
  ``(∀exh s p v env env'. pmatch_i2 exh s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch_i2 exh s p v env = Match env') ∧
    (∀exh s ps vs env env'. pmatch_list_i2 exh s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list_i2 exh s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_i2_any_no_match = store_thm("pmatch_i2_any_no_match",
  ``(∀exh s p v env. pmatch_i2 exh s p v env = No_match ⇒
       ∀env. pmatch_i2 exh s p v env = No_match) ∧
    (∀exh s ps vs env. pmatch_list_i2 exh s ps vs env = No_match ⇒
       ∀env. pmatch_list_i2 exh s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  imp_res_tac pmatch_i2_any_match >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct]);

fun exists_lift_conj_tac tm =
  CONV_TAC(
    STRIP_BINDER_CONV(SOME existential)
      (lift_conjunct_conv(same_const tm o fst o strip_comb)))

val exp_to_exh_correct = Q.store_thm ("exp_to_exh_correct",
`(!ck env s e r.
  evaluate_i3 ck env s e r
  ⇒
  !exh env' env_exh s_exh.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    env_to_exh exh env' env_exh ∧
    store_to_exh exh s s_exh
    ⇒
    ?r_exh.
    result_to_exh v_to_exh exh r r_exh ∧
    evaluate_exh ck env_exh s_exh (exp_to_exh exh e) r_exh) ∧
 (!ck env s es r.
  evaluate_list_i3 ck env s es r
  ⇒
  !exh env' env_exh s_exh. ?r_exh.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    env_to_exh exh env' env_exh ∧
    store_to_exh exh s s_exh
    ⇒
    ?r_exh.
    result_to_exh vs_to_exh exh r r_exh ∧
    evaluate_list_exh ck env_exh s_exh (exps_to_exh exh es) r_exh) ∧
 (!ck env s v pes err_v r.
  evaluate_match_i3 ck env s v pes err_v r
  ⇒
  !exh env' pes' is_handle env_exh s_exh v_exh.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    env_to_exh exh env' env_exh ∧
    store_to_exh exh s s_exh ∧
    v_to_exh exh v v_exh ∧
    (is_handle ⇒ err_v = v) ∧
    (¬is_handle ⇒ err_v = Conv_i2 (bind_tag, SOME(TypeExn(Short "Bind"))) []) ∧
    (pes' = add_default is_handle F pes ∨
     exists_match exh (SND (FST s)) (MAP FST pes) v ∧
     pes' = add_default is_handle T pes)
     ⇒
    ?r_exh.
    result_to_exh v_to_exh exh r r_exh ∧
    evaluate_match_exh ck env_exh s_exh v_exh (pat_exp_to_exh exh pes') r_exh)`,
 ho_match_mp_tac evaluate_i3_ind >>
 strip_tac >- (
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[exp_to_exh_def] >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] ) >>
 strip_tac >- (
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[exp_to_exh_def] >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   metis_tac[]) >>
 strip_tac >- (
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[exp_to_exh_def] >> fs[] >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   metis_tac[]) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >> fs[] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj2_tac >> disj1_tac >>
   fs[GSYM AND_IMP_INTRO] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >> fs[] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   qexists_tac`T`>>simp[] >>
   simp[add_default_def] >> rw[] >>
   metis_tac[exh_to_exists_match] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >> fs[] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj2_tac >> disj2_tac >>
   simp[Once result_to_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   pop_assum kall_tac >>
   rpt (pop_assum mp_tac) >>
   map_every qid_spec_tac[`env_exh`,`n`,`v`,`env`] >>
   Induct >> simp[] >>
   Cases >> fs[env_to_exh_LIST_REL] >>
   rw[EXISTS_PROD] >> simp[] ) >>
 strip_tac >- simp[] >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   Cases_on`s_exh`>>simp[] >>
   fs[store_to_exh_def] >>
   rfs[EVERY2_EVERY,EVERY_MEM] >>
   fs[MEM_ZIP,PULL_EXISTS] >>
   first_x_assum(qspec_then`n`mp_tac) >>
   simp[optionTheory.OPTREL_def] >>
   metis_tac[] ) >>
 strip_tac >- simp[] >>
 strip_tac >- simp[] >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   simp[Once v_to_exh_cases] >>
   HINT_EXISTS_TAC >> simp[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases,PULL_EXISTS] >>
   fs[do_uapp_i3_def, do_uapp_exh_def] >>
   every_case_tac >> fs[v_to_exh_eqn,LET_THM] >>
   fs[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   fs[EXISTS_PROD,store_lookup_def,store_alloc_def] >> rw[] >>
   simp[v_to_exh_eqn] >- (
     exists_lift_conj_tac``evaluate_exh`` >>
     res_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[store_to_exh_def] >>
     imp_res_tac EVERY2_LENGTH >> simp[] >>
     fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] )
   >- (
     res_tac >>
     exists_lift_conj_tac``evaluate_exh`` >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[store_to_exh_def] >>
     fs[EVERY2_EVERY] )
   >- (
     res_tac >>
     exists_lift_conj_tac``evaluate_exh`` >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[store_to_exh_def] >>
     exists_lift_conj_tac``LIST_REL`` >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     qmatch_assum_rename_tac`LIST_REL R genv2 genv3`["R"] >>
     qmatch_assum_rename_tac`v_to_exh exh v v3`[] >>
     qexists_tac`LUPDATE (SOME v3) n genv3` >>
     conj_tac >- (
       match_mp_tac EVERY2_LUPDATE_same >>
       simp[optionTheory.OPTREL_def] ) >>
     imp_res_tac EVERY2_LENGTH >>
     fs[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
     fs[optionTheory.OPTREL_def] >>
     res_tac >> rfs[] )) >>
 strip_tac >- simp[] >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj1_tac >>
   fs[GSYM AND_IMP_INTRO] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   exists_lift_conj_tac``evaluate_exh`` >>
   first_assum(split_pair_match o concl) >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >>
   BasicProvers.VAR_EQ_TAC >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_assum(split_pair_match o concl) >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >>
   BasicProvers.VAR_EQ_TAC >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   cheat ) >>
 cheat)

(*
 >- (disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[do_app_i2_def] >>
     every_case_tac >>
     fs[do_app_exh_def,v_to_exh_eqn,do_eq_i2_def] >>
     rw[] >> fs[] >>
     fs[exp_to_exh_def,exn_env_i2_def] >>
     fs[v_to_exh_eqn,bind_def,emp_def] >>
     fs[store_assign_def,evaluate_exh_lit] >>
     rw[LUPDATE_MAP,v_to_exh_eqn] >>
     fs[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,FST_triple,ETA_AX])
 >- (disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[do_app_i2_def] >>
     every_case_tac >>
     fs[do_app_exh_def,v_to_exh_eqn,do_eq_i2_def] >>
     rw[] >> fs[] >>
     fs[exp_to_exh_def,exn_env_i2_def] >>
     fs[v_to_exh_eqn,bind_def,emp_def] >>
     fs[store_assign_def,evaluate_exh_lit] >>
     rw[LUPDATE_MAP,v_to_exh_eqn] >>
     fs[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,FST_triple,ETA_AX])
 >- (disj2_tac >> disj1_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     fs[do_app_i2_def] >>
     every_case_tac >> fs[v_to_exh_eqn,do_app_exh_def] >>
     fs[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,FST_triple,ETA_AX])
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
     simp[v_to_exh_eqn])
 >- (res_tac >>
     fs [] >>
     cases_on `exhaustive_match exh (MAP FST pes)` >>
     fs []  >>
     metis_tac [exh_to_exists_match])
 >- (
   disj1_tac >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   fs[opt_bind_def] >> every_case_tac >> fs[v_to_exh_eqn] )
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
     rw [v_to_exh_eqn] >>
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
   simp[pmatch_exh_correct,pat_bindings_exh_correct])
 >- (rw [add_default_def, exp_to_exh_def] >>
     simp[pmatch_exh_correct,pat_bindings_exh_correct])
 >- (rw[add_default_def, exp_to_exh_def] >>
     simp[pmatch_exh_correct,pat_bindings_exh_correct] >>
     first_x_assum match_mp_tac >>
     ((qexists_tac`T` >> simp[add_default_def] >> fs[] >> NO_TAC) ORELSE
     (qexists_tac`F` >> simp[add_default_def] >> fs[] >> NO_TAC)))
 >- (rw[add_default_def, exp_to_exh_def] >>
     simp[pmatch_exh_correct,pat_bindings_exh_correct] >>
     first_x_assum match_mp_tac >>
     first_assum(match_exists_tac o concl) >> simp[] >>
     simp[add_default_def] >>
     fs[exists_match_def] >>
     metis_tac[pmatch_i2_any_no_match]))
*)

val v_to_exh_extend_disjoint_helper = Q.prove (
`(!exh v1 v2.
  v_to_exh exh v1 v2 ⇒
  !exh'. DISJOINT (FDOM exh') (FDOM exh)
    ⇒
    v_to_exh (exh' ⊌ exh) v1 v2) ∧
 (!exh vs1 vs2.
  vs_to_exh exh vs1 vs2 ⇒
  !exh'. DISJOINT (FDOM exh') (FDOM exh)
    ⇒
    vs_to_exh (exh' ⊌ exh) vs1 vs2) ∧
 (!exh env1 env2.
  env_to_exh exh env1 env2 ⇒
  !exh'. DISJOINT (FDOM exh') (FDOM exh)
    ⇒
    env_to_exh (exh' ⊌ exh) env1 env2)`,
 ho_match_mp_tac v_to_exh_ind >>
 rw [] >>
 rw [Once v_to_exh_cases] >>
 qexists_tac `exh'` >>
 rw [] >>
 `DISJOINT (FDOM exh') (FDOM exh'') ∧ DISJOINT (FDOM (FEMPTY:exh_ctors_env)) (FDOM exh')` 
       by (fs [SUBMAP_DEF, DISJOINT_DEF, EXTENSION] >>
           rw [] >>
           metis_tac []) >>
 metis_tac [FUNION_FEMPTY_1, SUBMAP_FUNION]);

val v_to_exh_extend_disjoint = store_thm("v_to_exh_extend_disjoint",
  ``∀exh v1 v2 exh'. v_to_exh exh v1 v2 ∧ DISJOINT (FDOM exh') (FDOM exh) ⇒
                     v_to_exh (exh ⊌ exh') v1 v2``,
  metis_tac [v_to_exh_extend_disjoint_helper, FUNION_COMM])

(* exhLangExtra *)

val free_vars_exh_def = tDefine"free_vars_exh"`
  free_vars_exh (Raise_exh e) = free_vars_exh e ∧
  free_vars_exh (Handle_exh e pes) = free_vars_exh e ∪ free_vars_pes_exh pes ∧
  free_vars_exh (Lit_exh _) = {} ∧
  free_vars_exh (Con_exh _ es) = free_vars_list_exh es ∧
  free_vars_exh (Var_local_exh n) = {n} ∧
  free_vars_exh (Var_global_exh _) = {} ∧
  free_vars_exh (Fun_exh x e) = free_vars_exh e DIFF {x} ∧
  free_vars_exh (Uapp_exh _ e) = free_vars_exh e ∧
  free_vars_exh (App_exh _ e1 e2) = free_vars_exh e1 ∪ free_vars_exh e2 ∧
  free_vars_exh (If_exh e1 e2 e3) = free_vars_exh e1 ∪ free_vars_exh e2 ∪ free_vars_exh e3 ∧
  free_vars_exh (Mat_exh e pes) = free_vars_exh e ∪ free_vars_pes_exh pes ∧
  free_vars_exh (Let_exh bn e1 e2) = free_vars_exh e1 ∪ (free_vars_exh e2 DIFF (case bn of NONE => {} | SOME x => {x})) ∧
  free_vars_exh (Letrec_exh defs e) = (free_vars_defs_exh defs ∪ free_vars_exh e) DIFF set(MAP FST defs) ∧
  free_vars_exh (Extend_global_exh _) = {} ∧
  free_vars_list_exh [] = {} ∧
  free_vars_list_exh (e::es) = free_vars_exh e ∪ free_vars_list_exh es ∧
  free_vars_defs_exh [] = {} ∧
  free_vars_defs_exh ((f,x,e)::ds) = (free_vars_exh e DIFF {x}) ∪ free_vars_defs_exh ds ∧
  free_vars_pes_exh [] = {} ∧
  free_vars_pes_exh ((p,e)::pes) = (free_vars_exh e DIFF (set (pat_bindings_exh p []))) ∪ free_vars_pes_exh pes`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_exh_size e
  | INR (INL es) => exp_exh6_size es
  | INR (INR (INL defs)) => exp_exh1_size defs
  | INR (INR (INR pes)) => exp_exh3_size pes)`)
val _ = export_rewrites["free_vars_exh_def"]

val free_vars_pes_exh_MAP = store_thm("free_vars_pes_exh_MAP",
  ``∀pes. free_vars_pes_exh pes = BIGUNION (set (MAP (λ(p,e). free_vars_exh e DIFF set (pat_bindings_exh p [])) pes))``,
  Induct >> simp[] >> Cases >> simp[])

val _ = export_theory ();
