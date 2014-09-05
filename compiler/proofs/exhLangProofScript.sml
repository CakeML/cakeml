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
  env_to_exh exh env env'
  ⇒
  v_to_exh exh (Closure_i2 env x e) (Closure_exh env' x (exp_to_exh exh' e))) ∧
(!exh env x funs exh'.
  exh' SUBMAP exh ∧
  env_to_exh exh env env'
  ⇒
  v_to_exh exh (Recclosure_i2 env funs x) (Recclosure_exh env' (funs_to_exh exh' funs) x)) ∧
(!exh l.
  v_to_exh exh (Loc_i2 l) (Loc_exh l)) ∧
(!exh vs vs'.
  vs_to_exh exh vs vs'
  ⇒
  v_to_exh exh (Vectorv_i2 vs) (Vectorv_exh vs')) ∧
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
 (!exh vs v.
  v_to_exh exh (Vectorv_i2 vs) v ⇔
   ?vs'.
    vs_to_exh exh vs vs' ∧
    v = Vectorv_exh vs') ∧
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

val sv_to_exh_def = Define`
  sv_to_exh exh (Refv v1) (Refv v2) = v_to_exh exh v1 v2 ∧
  sv_to_exh exh (W8array w1) (W8array w2) = (w1 = w2) ∧
  sv_to_exh exh (Varray vs1) (Varray vs2) = vs_to_exh exh vs1 vs2 ∧
  sv_to_exh exh _ _ = F`

val store_to_exh_def = Define `
store_to_exh exh ((s,genv):v_i2 count_store_genv) (s_exh,genv_exh) ⇔
  FST s = FST s_exh ∧
  LIST_REL (sv_to_exh exh) (SND s) (SND s_exh) ∧
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

val is_unconditional_thm = prove(
  ``∀p a b c d. is_unconditional p ⇒ pmatch_i2 a b p c d ≠ No_match``,
  ho_match_mp_tac is_unconditional_ind >>
  Cases >> rw[] >>
  Cases_on`c`>>rw[pmatch_i2_def]
  >- (
    fs[is_unconditional_def] >>
    every_case_tac >> fs[lit_same_type_def] >>
    every_case_tac >> fs[] )
  >- (
    pop_assum mp_tac >>
    rw[Once is_unconditional_def] >>
    every_case_tac >> fs[] >>
    Cases_on`p`>>Cases_on`r`>>rw[pmatch_i2_def]>>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`l'`,`a`,`b`,`d`] >>
    Induct_on`l` >> simp[LENGTH_NIL_SYM,pmatch_i2_def] >>
    rw[] >> Cases_on`l'`>>fs[] >>
    rw[pmatch_i2_def] >>
    BasicProvers.CASE_TAC >>
    metis_tac[] )
  >- (
    pop_assum mp_tac >>
    rw[Once is_unconditional_def] >>
    BasicProvers.EVERY_CASE_TAC >>
    metis_tac[]))

val is_unconditional_list_thm = prove(
  ``∀l1 l2 a b c. EVERY is_unconditional l1 ⇒ pmatch_list_i2 a b l1 l2 c ≠ No_match``,
  Induct >> Cases_on`l2` >> simp[pmatch_i2_def] >>
  rw[] >>
  BasicProvers.CASE_TAC >>
  metis_tac[is_unconditional_thm])

val get_tags_acc = prove(
  ``∀ls acc ts. get_tags ls acc = SOME ts ⇒ domain acc ⊆ domain ts``,
  Induct >> simp[get_tags_def] >> Cases >> simp[] >> every_case_tac >> simp[] >>
  rw[] >> res_tac >> fs[SUBSET_DEF])

val gen_get_tags_lemma = prove(
  ``!ps ts acc. get_tags ps acc = SOME ts ==>
         (!p. MEM p ps ==> ?t x vs. (p = Pcon_i2 (t,x) vs) /\ EVERY is_unconditional vs /\ t IN (domain ts))
         /\
         (!t. t IN (domain ts) /\ t NOTIN (domain acc) ==> ?x vs. MEM (Pcon_i2(t,x) vs) ps /\ EVERY is_unconditional vs)``,
  Induct >> simp[get_tags_def] >>
  Cases >> simp[] >>
  Cases_on`p` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  imp_res_tac get_tags_acc >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >>
  conj_tac >- (
    gen_tac >> reverse strip_tac >- metis_tac[] >>
    simp[] >> fs[SUBSET_DEF] ) >>
  gen_tac >> strip_tac >>
  Cases_on`t=q` >>
  rw[] >> metis_tac[])

val get_tags_lemma =
  gen_get_tags_lemma
  |> CONV_RULE (RESORT_FORALL_CONV List.rev)
  |> Q.SPEC`LN`
  |> SIMP_RULE (srw_ss())[]
  |> GEN_ALL

val pmatch_i2_Pcon_No_match = prove(
  ``EVERY is_unconditional ps ⇒
    ((pmatch_i2 exh s (Pcon_i2 (c,SOME (TypeId t)) ps) v env = No_match) ⇔
     ∃cv vs tags.
       v = Conv_i2 (cv,SOME (TypeId t)) vs ∧
       FLOOKUP exh t = SOME tags ∧
       c ∈ domain tags ∧ cv ∈ domain tags ∧
       c ≠ cv)``,
  Cases_on`v`>>rw[pmatch_i2_def]>>
  PairCases_on`p`>>
  Cases_on`p1`>>simp[pmatch_i2_def]>>
  Cases_on`x`>>simp[pmatch_i2_def]>>
  rw[] >> BasicProvers.CASE_TAC >> rw[] >>
  metis_tac[is_unconditional_list_thm])

val exh_to_exists_match = Q.prove (
`!exh ps. exhaustive_match exh ps ⇒ !s v. exists_match exh s ps v`,
  rw [exhaustive_match_def, exists_match_def] >- (
    fs[EXISTS_MEM] >>
    metis_tac[is_unconditional_thm] ) >>
  every_case_tac >>
  fs [get_tags_def, pmatch_i2_def] >> rw[] >>
  imp_res_tac get_tags_lemma >>
  Q.PAT_ABBREV_TAC`pp1 = Pcon_i2 X l` >>
  Cases_on`v`>>
  TRY(qexists_tac`pp1`>>simp[pmatch_i2_def,Abbr`pp1`]>>NO_TAC) >>
  srw_tac[boolSimps.DNF_ss][]>>
  simp[Abbr`pp1`,pmatch_i2_Pcon_No_match]>>
  simp[METIS_PROVE[]``a \/ b <=> ~a ==> b``] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
  res_tac >> HINT_EXISTS_TAC >> simp[] >>
  Cases_on`x'`>>simp[pmatch_i2_def] >>
  Cases_on`x''`>>simp[pmatch_i2_def] >>
  rw[] >>
  metis_tac[is_unconditional_list_thm])

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
`(!v1 v2 tagenv r v1_exh v2_exh (exh:exh_ctors_env).
  do_eq_i2 v1 v2 = r ∧
  v_to_exh exh v1 v1_exh ∧
  v_to_exh exh v2 v2_exh
  ⇒
  do_eq_exh v1_exh v2_exh = r) ∧
 (!vs1 vs2 tagenv r vs1_exh vs2_exh (exh:exh_ctors_env).
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
`(!(exh:exh_ctors_env) s p v env r env_exh s_exh v_exh.
  r ≠ Match_type_error ∧
  pmatch_i2 exh s p v env = r ∧
  LIST_REL (sv_to_exh exh) s s_exh ∧
  v_to_exh exh v v_exh ∧
  env_to_exh exh env env_exh
  ⇒
  ?r_exh.
    pmatch_exh s_exh (pat_to_exh p) v_exh env_exh = r_exh ∧
    match_result_to_exh exh r r_exh) ∧
 (!(exh:exh_ctors_env) s ps vs env r env_exh s_exh vs_exh.
  r ≠ Match_type_error ∧
  pmatch_list_i2 exh s ps vs env = r ∧
  LIST_REL (sv_to_exh exh) s s_exh ∧
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
     rfs[] >> metis_tac [sv_to_exh_def])
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
  ``(∀(exh:exh_ctors_env) s p v env env'. pmatch_i2 exh s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch_i2 exh s p v env = Match env') ∧
    (∀(exh:exh_ctors_env) s ps vs env env'. pmatch_list_i2 exh s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list_i2 exh s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_i2_ind >>
  rw[pmatch_i2_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[semanticPrimitivesTheory.match_result_distinct])

val pmatch_i2_any_no_match = store_thm("pmatch_i2_any_no_match",
  ``(∀(exh:exh_ctors_env) s p v env. pmatch_i2 exh s p v env = No_match ⇒
       ∀env. pmatch_i2 exh s p v env = No_match) ∧
    (∀(exh:exh_ctors_env) s ps vs env. pmatch_list_i2 exh s ps vs env = No_match ⇒
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

val v_to_exh_lit_loc = store_thm("v_to_exh_lit_loc",
  ``(v_to_exh exh (Litv_i2 l) lh ⇔ lh = Litv_exh l) ∧
    (v_to_exh exh l2 (Litv_exh l) ⇔ l2 = Litv_i2 l) ∧
    (v_to_exh exh (Loc_i2 n) lh ⇔ lh = Loc_exh n) ∧
    (v_to_exh exh l2 (Loc_exh n) ⇔ l2 = Loc_i2 n)``,
  rw[] >> rw[Once v_to_exh_cases])
val _ = export_rewrites["v_to_exh_lit_loc"];

val v_to_exh_extend_disjoint_helper = Q.prove (
`(!(exh:exh_ctors_env) v1 v2.
  v_to_exh exh v1 v2 ⇒
  !exh'. DISJOINT (FDOM exh') (FDOM exh)
    ⇒
    v_to_exh (exh' ⊌ exh) v1 v2) ∧
 (!(exh:exh_ctors_env) vs1 vs2.
  vs_to_exh exh vs1 vs2 ⇒
  !exh'. DISJOINT (FDOM exh') (FDOM exh)
    ⇒
    vs_to_exh (exh' ⊌ exh) vs1 vs2) ∧
 (!(exh:exh_ctors_env) env1 env2.
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

val env_to_exh_submap = prove(
  ``∀(exh:exh_ctors_env) env1 env2 exh'. env_to_exh exh env1 env2 ⇒ exh ⊑ exh' ⇒ env_to_exh exh' env1 env2``,
  rw[] >>
  first_x_assum(mp_tac o MATCH_MP(CONJUNCT2(CONJUNCT2 v_to_exh_extend_disjoint_helper))) >>
  disch_then(qspec_then`DRESTRICT exh' (COMPL (FDOM exh)) `mp_tac) >>
  discharge_hyps >- (
    simp[IN_DISJOINT,FDOM_DRESTRICT] >>
    fs[SUBMAP_DEF] >> metis_tac[] ) >>
  Q.PAT_ABBREV_TAC`exh'' = X ⊌ exh` >>
  `exh'' = exh'` by (
   simp[Abbr`exh''`,GSYM fmap_EQ_THM,DRESTRICT_DEF,FUNION_DEF] >>
   fs[SUBMAP_DEF,EXTENSION] >>
   conj_tac >- metis_tac[] >> rw[] ) >> rw[]);

val v_to_list_exh_correct = Q.prove (
`!v1 v2 vs1.
  v_to_exh genv v1 v2 ∧
  v_to_list_i2 v1 = SOME vs1
  ⇒
  ?vs2.
    v_to_list_exh v2 = SOME vs2 ∧
    vs_to_exh genv vs1 vs2`,
 ho_match_mp_tac v_to_list_i2_ind >>
 rw [v_to_list_i2_def] >>
 every_case_tac >>
 fs [v_to_exh_eqn, v_to_list_exh_def] >>
 rw [] >>
 every_case_tac >>
 fs [v_to_exh_eqn, v_to_list_exh_def] >>
 rw [] >>
 metis_tac [NOT_SOME_NONE, SOME_11]);

val do_app_i2_cases = Q.store_thm("do_app_i2_cases",
  `do_app_i2 s op vs = SOME x ⇒
    (∃z n1 n2. op = (Op_i2 (Opn z)) ∧ vs = [Litv_i2 (IntLit n1); Litv_i2 (IntLit n2)]) ∨
    (∃z n1 n2. op = (Op_i2 (Opb z)) ∧ vs = [Litv_i2 (IntLit n1); Litv_i2 (IntLit n2)]) ∨
    (∃v1 v2. op = (Op_i2 Equality) ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = (Op_i2 Opassign) ∧ vs = [Loc_i2 lnum; v]) ∨
    (∃n. op = (Op_i2 Opderef) ∧ vs = [Loc_i2 n]) ∨
    (∃v. op = (Op_i2 Opref) ∧ vs = [v]) ∨
    (∃n w. op = (Op_i2 Aw8alloc) ∧ vs = [Litv_i2 (IntLit n); Litv_i2 (Word8 w)]) ∨
    (∃lnum i. op = (Op_i2 Aw8sub) ∧ vs = [Loc_i2 lnum; Litv_i2 (IntLit i)]) ∨
    (∃n. op = (Op_i2 Aw8length) ∧ vs = [Loc_i2 n]) ∨
    (∃lnum i w. op = (Op_i2 Aw8update) ∧ vs = [Loc_i2 lnum; Litv_i2 (IntLit i); Litv_i2 (Word8 w)]) ∨
    (∃v vs'. op = (Op_i2 VfromList) ∧ vs = [v] ∧ (v_to_list_i2 v = SOME vs')) ∨
    (∃vs' i. op = (Op_i2 Vsub) ∧ vs = [Vectorv_i2 vs'; Litv_i2 (IntLit i)]) ∨
    (∃vs'. op = (Op_i2 Vlength) ∧ vs = [Vectorv_i2 vs']) ∨
    (∃v n. op = (Op_i2 Aalloc) ∧ vs = [Litv_i2 (IntLit n); v]) ∨
    (∃lnum i. op = (Op_i2 Asub) ∧ vs = [Loc_i2 lnum; Litv_i2 (IntLit i)]) ∨
    (∃n. op = (Op_i2 Alength) ∧ vs = [Loc_i2 n]) ∨
    (∃lnum i v. op = (Op_i2 Aupdate) ∧ vs = [Loc_i2 lnum; Litv_i2 (IntLit i); v])`,
  rw[do_app_i2_def] >>
  every_case_tac >> 
  fs[]);

val tac =
  rw [do_app_exh_def, result_to_exh_cases, store_to_exh_def, prim_exn_i2_def,
      prim_exn_exh_def, v_to_exh_eqn] >>
  fs [] >>
  fs [store_assign_def,store_to_exh_def, store_lookup_def, store_alloc_def,
      LET_THM] >>
  rw [] >>
  imp_res_tac LIST_REL_LENGTH >>
  fs [prim_exn_i2_def, v_to_exh_eqn] >>
  every_case_tac >>
  fs [store_to_exh_def, LIST_REL_EL_EQN, EL_LUPDATE] >>
  rw [store_to_exh_def, EL_LUPDATE, sv_to_exh_def] >>
  res_tac >>
  pop_assum mp_tac >>
  ASM_REWRITE_TAC [sv_to_exh_def] >>
  fs [v_to_exh_eqn, store_v_same_type_def] >>
  every_case_tac >>
  fs [];

val do_app_exh_i2 = Q.prove (
`!(exh:exh_ctors_env) s1 op vs s2 res s1_exh vs_exh c g.
  do_app_i2 s1 op vs = SOME (s2, res) ∧
  store_to_exh exh ((c,s1),g) s1_exh ∧
  vs_to_exh exh vs vs_exh
  ⇒
   ∃s2_exh res_exh.
     result_to_exh v_to_exh exh (((c,s2),g),res) (s2_exh,res_exh) ∧
     do_app_exh s1_exh op vs_exh = SOME (s2_exh, res_exh)`,
 rw [] >>
 PairCases_on `s1_exh` >>
 imp_res_tac do_app_i2_cases >>
 fs [] >>
 rw [] >>
 fs [do_app_i2_def, store_to_exh_def]
 >- tac
 >- tac
 >- (every_case_tac >>
     imp_res_tac do_eq_exh_correct >>
     fs [] >>
     rw [do_app_exh_def, result_to_exh_cases, store_to_exh_def,
         prim_exn_i2_def, prim_exn_exh_def, v_to_exh_eqn])
 >- (tac >>
     metis_tac [v_to_exh_eqn, store_v_distinct, sv_to_exh_def])
 >- tac
 >- tac
 >- tac
 >- (tac >>
     metis_tac [v_to_exh_eqn, store_v_distinct, sv_to_exh_def])
 >- tac
 >- (tac >>
     metis_tac [v_to_exh_eqn, store_v_distinct, sv_to_exh_def])
 >- (imp_res_tac v_to_list_exh_correct >>
     rw [do_app_exh_def, result_to_exh_cases, v_to_exh_eqn, store_to_exh_def] >>
     fs [vs_to_exh_LIST_REL])
 >- (tac >>
     full_simp_tac (srw_ss()++ARITH_ss) [])
 >- tac
 >- (tac >>
     rw [LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE])
 >- (tac >>
     rw []
     >- (CCONTR_TAC >>
         fs [] >>
         imp_res_tac LIST_REL_LENGTH >> 
         full_simp_tac (srw_ss()++ARITH_ss) [])
     >- (CCONTR_TAC >>
         fs [] >>
         imp_res_tac LIST_REL_LENGTH >> 
         full_simp_tac (srw_ss()++ARITH_ss) [])
     >- (fs [LIST_REL_EL_EQN] >>
         `Num (ABS i) < LENGTH l'` by decide_tac >>
         res_tac))
 >- (tac >>
     metis_tac [LIST_REL_LENGTH])
 >- (tac >>
     rw []
     >- (CCONTR_TAC >>
         fs [] >>
         imp_res_tac LIST_REL_LENGTH >> 
         full_simp_tac (srw_ss()++ARITH_ss) [])
     >- (CCONTR_TAC >>
         fs [] >>
         imp_res_tac LIST_REL_LENGTH >> 
         full_simp_tac (srw_ss()++ARITH_ss) [])
     >- (CCONTR_TAC >>
         fs [] >>
         imp_res_tac LIST_REL_LENGTH >> 
         full_simp_tac (srw_ss()++ARITH_ss) [])
     >- (fs [LIST_REL_EL_EQN] >>
         `Num (ABS i) < LENGTH l'` by decide_tac >>
         res_tac >>
         pop_assum mp_tac >>
         ASM_REWRITE_TAC [sv_to_exh_def, vs_to_exh_LIST_REL] >>
         rw [EL_LUPDATE] >>
         fs [] >>
         every_case_tac >>
         fs [])));

val do_app_exh_i3 = prove(
  ``∀s1 op vs s2 res exh s1 s1_exh vs_exh.
      do_app_i3 s1 op vs = SOME (s2,res) ∧
      store_to_exh exh s1 s1_exh ∧
      vs_to_exh exh vs vs_exh ⇒
      ∃s2_exh res_exh.
        do_app_exh s1_exh op vs_exh = SOME (s2_exh,res_exh) ∧
        result_to_exh v_to_exh exh (s2,res) (s2_exh,res_exh)``,
  rpt gen_tac >>
  PairCases_on`s1` >>
  PairCases_on`s1_exh` >>
  rw[do_app_i3_def] >>
  Cases_on`op`>>fs[] >- (
    every_case_tac >> fs[] >>
    first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]do_app_exh_i2)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[vs_to_exh_LIST_REL] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    metis_tac[] ) >>
  simp[do_app_exh_def] >>
  fs[store_to_exh_def,LIST_REL_EL_EQN] >>
  every_case_tac >> fs[] >> rw[] >>
  fs[result_to_exh_cases,store_to_exh_def,LIST_REL_EL_EQN,OPTREL_def,EL_LUPDATE] >>
  rw[] >> metis_tac[NOT_SOME_NONE]);

val exhaustive_match_submap = prove(
  ``exhaustive_match exh pes ∧ exh ⊑ exh2 ⇒ exhaustive_match exh2 pes``,
  rw[exhaustive_match_def] >>
  every_case_tac >> fs[] >>
  imp_res_tac FLOOKUP_SUBMAP >> fs[])

val do_opapp_exh = prove(
  ``∀vs env e exh vs_exh.
    do_opapp_i2 vs = SOME (env,e) ∧
    vs_to_exh exh vs vs_exh
    ⇒
    ∃exh' env_exh.
      env_to_exh exh env env_exh ∧
      exh' ⊑ exh ∧
      do_opapp_exh vs_exh = SOME (env_exh,exp_to_exh exh' e)``,
  rw[do_opapp_i2_def,do_opapp_exh_def] >>
  every_case_tac >> fs[] >> rw[] >>
  TRY (fs[Once v_to_exh_cases]>>NO_TAC) >>
  fs[Q.SPECL[`exh`,`Closure_i2 X Y Z`](CONJUNCT1 v_to_exh_cases),bind_def,env_to_exh_LIST_REL] >>
  fs[Q.SPECL[`exh`,`Recclosure_i2 X Y Z`](CONJUNCT1 v_to_exh_cases),bind_def,env_to_exh_LIST_REL] >>
  rw[] >> fs[find_recfun_funs_to_exh] >> rw[] >>
  fs[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,FST_triple,ETA_AX]
  >- metis_tac[SUBMAP_REFL] >>
  simp[build_rec_env_exh_MAP,build_rec_env_i2_MAP] >>
  qexists_tac`exh'`>>simp[] >>
  match_mp_tac EVERY2_APPEND_suff >>
  simp[EVERY2_MAP,UNCURRY] >>
  simp[Once v_to_exh_cases,funs_to_exh_MAP,MAP_EQ_f] >>
  match_mp_tac EVERY2_refl >>
  simp[UNCURRY,env_to_exh_LIST_REL] >>
  metis_tac[]);

val exp_to_exh_correct = Q.store_thm ("exp_to_exh_correct",
`(!ck env s e r.
  evaluate_i3 ck env s e r
  ⇒
  !(exh:exh_ctors_env) env' env_exh s_exh exh'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    env_to_exh exh env' env_exh ∧
    store_to_exh exh s s_exh ∧
    exh' ⊑ exh
    ⇒
    ?r_exh.
    result_to_exh v_to_exh exh r r_exh ∧
    evaluate_exh ck env_exh s_exh (exp_to_exh exh' e) r_exh) ∧
 (!ck env s es r.
  evaluate_list_i3 ck env s es r
  ⇒
  !(exh:exh_ctors_env) env' env_exh s_exh exh'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    env_to_exh exh env' env_exh ∧
    store_to_exh exh s s_exh ∧
    exh' ⊑ exh
    ⇒
    ?r_exh.
    result_to_exh vs_to_exh exh r r_exh ∧
    evaluate_list_exh ck env_exh s_exh (exps_to_exh exh' es) r_exh) ∧
 (!ck env s v pes err_v r.
  evaluate_match_i3 ck env s v pes err_v r
  ⇒
  !(exh:exh_ctors_env) env' pes' is_handle env_exh s_exh v_exh exh'.
    SND r ≠ Rerr Rtype_error ∧
    env = (exh,env') ∧
    env_to_exh exh env' env_exh ∧
    store_to_exh exh s s_exh ∧
    v_to_exh exh v v_exh ∧
    (is_handle ⇒ err_v = v) ∧
    (¬is_handle ⇒ err_v = Conv_i2 (bind_tag, SOME(TypeExn(Short "Bind"))) []) ∧
    (pes' = add_default is_handle F pes ∨
     exists_match exh (SND (FST s)) (MAP FST pes) v ∧
     pes' = add_default is_handle T pes) ∧
    exh' ⊑ exh
     ⇒
    ?r_exh.
    result_to_exh v_to_exh exh r r_exh ∧
    evaluate_match_exh ck env_exh s_exh v_exh (pat_exp_to_exh exh' pes') r_exh)`,
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
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >>
   exists_lift_conj_tac``evaluate_exh`` >> fs[] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   qexists_tac`T`>>simp[] >>
   simp[add_default_def] >> rw[] >>
   metis_tac[exh_to_exists_match,exhaustive_match_submap] ) >>
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
   HINT_EXISTS_TAC >> simp[]) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS] >>
   strip_tac >>
   rpt gen_tac >> strip_tac >>
   last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   strip_tac >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj1_tac >>
   exists_lift_conj_tac``evaluate_list_exh`` >>
   PairCases_on`s'` >>
   PairCases_on`s_exh` >>
   first_assum(match_exists_tac o concl) >>
   simp[] >>
   first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]do_opapp_exh)) >>
   simp[vs_to_exh_LIST_REL] >>
   disch_then(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_assum(match_exists_tac o concl) >> simp[] >> fs[] >>
   fs[store_to_exh_def] >>
   last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   simp[FORALL_PROD,store_to_exh_def] >>
   ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   strip_tac >>
   first_assum(match_exists_tac o concl) >> simp[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   simp[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   strip_tac >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   simp[Once evaluate_exh_cases] >>
   disj2_tac >> disj1_tac >>
   exists_lift_conj_tac``evaluate_list_exh`` >>
   PairCases_on`s''`>>fs[store_to_exh_def]>>rw[]>>
   first_assum(match_exists_tac o concl) >> simp[] >>
   imp_res_tac do_opapp_exh >>
   metis_tac[vs_to_exh_LIST_REL] ) >>
 strip_tac >- simp[] >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >> fs[] >>
   last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
   simp[Once result_to_exh_cases] >> strip_tac >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj1_tac >>
   exists_lift_conj_tac``evaluate_list_exh`` >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] do_app_exh_i3)) >>
   disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
   simp[vs_to_exh_LIST_REL] ) >>
 strip_tac >- simp[] >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   fs[] >>
   fs[GSYM AND_IMP_INTRO] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >>
   rpt disj2_tac >>
   fs[result_to_exh_cases,PULL_EXISTS] >> rw[] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >>
   fs[GSYM AND_IMP_INTRO] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj1_tac >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   exists_lift_conj_tac``evaluate_exh`` >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >> fs[] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   fs[do_if_i2_def,do_if_exh_def] >>
   rw[] >> fs[] >> rw[] >>
   every_case_tac >> fs[] >>
   metis_tac[] ) >>
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
   fs[GSYM AND_IMP_INTRO] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj1_tac >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   exists_lift_conj_tac``evaluate_exh`` >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >> fs[] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   qexists_tac`F` >> simp[] >>
   Cases_on`exhaustive_match exh' (MAP FST pes)`>>simp[] >>
   metis_tac[exhaustive_match_submap,exh_to_exists_match] ) >>
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
   srw_tac[DNF_ss][] >> disj1_tac >>
   fs[GSYM AND_IMP_INTRO] >>
   last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
   rator_x_assum`result_to_exh`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_to_exh_cases]) >>
   exists_lift_conj_tac``evaluate_exh`` >> fs[] >>
   first_assum(match_exists_tac o concl) >> simp[] >>
   ONCE_REWRITE_TAC[CONJ_COMM] >>
   first_x_assum (match_mp_tac o MP_CANON) >>
   simp[env_to_exh_LIST_REL,opt_bind_def] >>
   BasicProvers.CASE_TAC >> fs[env_to_exh_LIST_REL] ) >>
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
   srw_tac[DNF_ss][] >> disj1_tac >>
   fs[FST_triple,funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
   first_x_assum (match_mp_tac o MP_CANON) >> simp[] >>
   fs[env_to_exh_LIST_REL,build_rec_env_i2_MAP,build_rec_env_exh_MAP] >>
   match_mp_tac EVERY2_APPEND_suff >>
   simp[EVERY2_MAP] >>
   match_mp_tac EVERY2_refl >>
   simp[FORALL_PROD] >>
   simp[Once v_to_exh_cases,funs_to_exh_MAP,MAP_EQ_f,FORALL_PROD,env_to_exh_LIST_REL] >>
   metis_tac[] ) >>
 strip_tac >- rw[] >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rw[] >>
   rw[Once evaluate_exh_cases] >>
   rw[Once result_to_exh_cases] >>
   srw_tac[DNF_ss][] >>
   simp[store_to_exh_def] >>
   Cases_on`s_exh`>>simp[] >>
   fs[store_to_exh_def] >>
   match_mp_tac EVERY2_APPEND_suff >>
   simp[] >>
   simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] ) >>
 strip_tac >- (
   rw[] >>
   rw[Once result_to_exh_cases,PULL_EXISTS] >>
   simp[Once evaluate_exh_cases,exp_to_exh_def] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >> fs[] >>
   fs[Once result_to_exh_cases,PULL_EXISTS] >>
   simp[Once evaluate_exh_cases,PULL_EXISTS] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >> fs[] >>
   fs[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rpt gen_tac >> strip_tac >>
   rpt gen_tac >> strip_tac >> fs[] >>
   fs[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >>
   metis_tac[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rw[add_default_def] >>
   simp[Once evaluate_exh_cases,exp_to_exh_def,pat_bindings_exh_def,pat_to_exh_def,pmatch_exh_def,bind_def] >>
   rw[Once evaluate_exh_cases] >>
   fs[Once result_to_exh_cases,PULL_EXISTS,v_to_exh_eqn] >>
   fs[exists_match_def] >>
   rw[Once evaluate_exh_cases] >>
   rw[Once evaluate_exh_cases] >>
   rw[Once evaluate_exh_cases] >>
   rw[Once evaluate_exh_cases] >>
   PairCases_on`s_exh`>>simp[] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rw[add_default_def] >> rw[exp_to_exh_def] >>
   PairCases_on`s_exh` >> fs[store_to_exh_def] >> rw[] >>
   full_simp_tac std_ss[GSYM vs_to_exh_LIST_REL] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj1_tac >>
   imp_res_tac (CONJUNCT1 pmatch_exh_correct) >>
   Cases_on`pmatch_exh s_exh1 (pat_to_exh p) v_exh env_exh`>>
   fs[match_result_to_exh_def] >>
   simp[pat_bindings_exh_correct] >>
   first_x_assum match_mp_tac >>
   simp[store_to_exh_def] ) >>
 strip_tac >- (
   simp[exp_to_exh_def] >>
   rw[add_default_def] >> rw[exp_to_exh_def] >>
   PairCases_on`s_exh` >> fs[store_to_exh_def] >> rw[] >>
   full_simp_tac std_ss[GSYM vs_to_exh_LIST_REL] >>
   simp[Once evaluate_exh_cases] >>
   srw_tac[DNF_ss][] >> disj2_tac >> disj1_tac >>
   imp_res_tac (CONJUNCT1 pmatch_exh_correct) >>
   Cases_on`pmatch_exh s_exh1 (pat_to_exh p) v_exh env_exh`>>
   fs[match_result_to_exh_def] >>
   simp[pat_bindings_exh_correct] >>
   first_x_assum match_mp_tac >>
   simp[store_to_exh_def] >>
   TRY (qexists_tac`T` >> simp[] >> NO_TAC) >>
   TRY (qexists_tac`F` >> simp[] >> NO_TAC) >>
   qexists_tac`is_handle`>>simp[] >> rw[] >> fs[] >>
   fs[exists_match_def,PULL_EXISTS] >>
   metis_tac[pmatch_i2_any_no_match] ) >>
 rw[])

val v_to_exh_extend_disjoint = store_thm("v_to_exh_extend_disjoint",
  ``∀(exh:exh_ctors_env) v1 v2 exh'. v_to_exh exh v1 v2 ∧ DISJOINT (FDOM exh') (FDOM exh) ⇒
                     v_to_exh (exh ⊌ exh') v1 v2``,
  metis_tac [v_to_exh_extend_disjoint_helper, FUNION_COMM])

(* TODO: move *)

val csg_rel_def = Define`
  csg_rel R ((c1,s1),g1) (((c2,s2),g2):'a count_store_genv) ⇔
    c1 = c2 ∧ LIST_REL (sv_rel R) s1 s2 ∧ LIST_REL (OPTION_REL R) g1 g2`

val csg_rel_refl = store_thm("csg_rel_refl",
  ``∀V x. (∀x. V x x) ⇒ csg_rel V x x``,
  rpt gen_tac >> PairCases_on`x` >> simp[csg_rel_def] >>
  rw[] >> match_mp_tac EVERY2_refl >>
  rw[optionTheory.OPTREL_def] >>
  Cases_on`x` >> rw[])
val _ = export_rewrites["csg_rel_refl"]

val csg_rel_trans = store_thm("csg_rel_trans",
  ``∀V. (∀x y z. V x y ∧ V y z ⇒ V x z) ⇒ ∀x y z. csg_rel V x y ∧ csg_rel V y z ⇒ csg_rel V x z``,
  rw[] >> map_every PairCases_on [`x`,`y`,`z`] >>
  fs[csg_rel_def] >>
  conj_tac >>
  match_mp_tac (MP_CANON EVERY2_trans)
  >- metis_tac[sv_rel_trans] >>
  simp[optionTheory.OPTREL_def] >>
  qexists_tac`y2` >> simp[] >>
  Cases >> Cases >> Cases >> simp[] >>
  metis_tac[])

val csg_rel_count = store_thm("csg_rel_count",
  ``csg_rel R csg1 csg2 ⇒ FST(FST csg2) = FST(FST csg1)``,
  PairCases_on`csg1` >>
  PairCases_on`csg2` >>
  simp[csg_rel_def])

val map_count_store_genv_def = Define`
  map_count_store_genv f (csg:'a count_store_genv) =
    ((FST(FST csg), MAP (map_sv f) (SND(FST csg))), MAP (OPTION_MAP f) (SND csg))`

val csg_every_def = Define`
  csg_every P ((c,s),g) ⇔ EVERY (sv_every P) s ∧ EVERY (OPTION_EVERY P) g`

(* exhLangExtra *)

val free_vars_exh_def = tDefine"free_vars_exh"`
  free_vars_exh (Raise_exh e) = free_vars_exh e ∧
  free_vars_exh (Handle_exh e pes) = free_vars_exh e ∪ free_vars_pes_exh pes ∧
  free_vars_exh (Lit_exh _) = {} ∧
  free_vars_exh (Con_exh _ es) = free_vars_list_exh es ∧
  free_vars_exh (Var_local_exh n) = {n} ∧
  free_vars_exh (Var_global_exh _) = {} ∧
  free_vars_exh (Fun_exh x e) = free_vars_exh e DIFF {x} ∧
  free_vars_exh (App_exh _ es) = free_vars_list_exh es ∧
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

val sv_to_exh_sv_rel = store_thm("sv_to_exh_sv_rel",
  ``sv_to_exh exh = sv_rel (v_to_exh exh)``,
  simp[FUN_EQ_THM] >> Cases >> Cases >> rw[sv_rel_def,sv_to_exh_def])

val store_to_exh_csg_rel = store_thm("store_to_exh_csg_rel",
  ``store_to_exh exh = csg_rel (v_to_exh exh)``,
  simp[FUN_EQ_THM,FORALL_PROD,store_to_exh_def,csg_rel_def,sv_to_exh_sv_rel])

val build_rec_env_exh_MAP = store_thm("build_rec_env_exh_MAP",
  ``build_rec_env_exh funs cle env = MAP (λ(f,cdr). (f, (Recclosure_exh cle funs f))) funs ++ env``,
  rw[build_rec_env_exh_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val pmatch_exh_any_match = store_thm("pmatch_exh_any_match",
  ``(∀s p v env env'. pmatch_exh s p v env = Match env' ⇒
       ∀env. ∃env'. pmatch_exh s p v env = Match env') ∧
    (∀s ps vs env env'. pmatch_list_exh s ps vs env = Match env' ⇒
       ∀env. ∃env'. pmatch_list_exh s ps vs env = Match env')``,
  ho_match_mp_tac pmatch_exh_ind >>
  rw[pmatch_exh_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  metis_tac[match_result_distinct])

val pmatch_exh_any_no_match = store_thm("pmatch_exh_any_no_match",
  ``(∀s p v env. pmatch_exh s p v env = No_match ⇒
       ∀env. pmatch_exh s p v env = No_match) ∧
    (∀s ps vs env. pmatch_list_exh s ps vs env = No_match ⇒
       ∀env. pmatch_list_exh s ps vs env = No_match)``,
  ho_match_mp_tac pmatch_exh_ind >>
  rw[pmatch_exh_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  fs[] >> strip_tac >> fs[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  imp_res_tac pmatch_exh_any_match >>
  metis_tac[match_result_distinct])

val pmatch_exh_any_match_error = store_thm("pmatch_exh_any_match_error",
  ``(∀s p v env. pmatch_exh s p v env = Match_type_error ⇒
       ∀env. pmatch_exh s p v env = Match_type_error) ∧
    (∀s ps vs env. pmatch_list_exh s ps vs env = Match_type_error ⇒
       ∀env. pmatch_list_exh s ps vs env = Match_type_error)``,
  rw[] >> qmatch_abbrev_tac`X = Y` >> Cases_on`X` >> fs[markerTheory.Abbrev_def] >>
  metis_tac[match_result_distinct
           ,pmatch_exh_any_no_match,pmatch_exh_any_match])

val pmatch_list_exh_pairwise = store_thm("pmatch_list_exh_pairwise",
  ``∀ps vs s env env'. pmatch_list_exh s ps vs env = Match env' ⇒
      EVERY2 (λp v. ∀env. ∃env'. pmatch_exh s p v env = Match env') ps vs``,
  Induct >> Cases_on`vs` >> simp[pmatch_exh_def] >>
  rpt gen_tac >> BasicProvers.CASE_TAC >> strip_tac >>
  res_tac >> simp[] >> metis_tac[pmatch_exh_any_match])

val pmatch_list_exh_SNOC_nil = store_thm("pmatch_list_exh_SNOC_nil",
  ``∀p ps v vs s env.
      (pmatch_list_exh s [] (SNOC v vs) env = Match_type_error) ∧
      (pmatch_list_exh s (SNOC p ps) [] env = Match_type_error)``,
  Cases_on`ps`>>Cases_on`vs`>>simp[pmatch_exh_def])
val _ = export_rewrites["pmatch_list_exh_SNOC_nil"]

val pmatch_list_exh_SNOC = store_thm("pmatch_list_exh_SNOC",
  ``∀ps vs p v s env. LENGTH ps = LENGTH vs ⇒
      pmatch_list_exh s (SNOC p ps) (SNOC v vs) env =
      case pmatch_list_exh s ps vs env of
      | Match env' => pmatch_exh s p v env'
      | res => res``,
  Induct >> Cases_on`vs` >> simp[pmatch_exh_def] >> rw[] >>
  BasicProvers.CASE_TAC)

val pmatch_exh_APPEND = store_thm("pmatch_exh_APPEND",
  ``(∀s p v env n.
      (pmatch_exh s p v env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_exh s p v (TAKE n env)))) ∧
    (∀s ps vs env n.
      (pmatch_list_exh s ps vs env =
       map_match (combin$C APPEND (DROP n env)) (pmatch_list_exh s ps vs (TAKE n env))))``,
  ho_match_mp_tac pmatch_exh_ind >>
  rw[pmatch_exh_def,libTheory.bind_def]
  >- ( BasicProvers.CASE_TAC >> fs[] >>
       BasicProvers.CASE_TAC >> fs[]) >>
  pop_assum (qspec_then`n`mp_tac) >>
  Cases_on `pmatch_exh s p v (TAKE n env)`>>fs[] >>
  strip_tac >> res_tac >>
  qmatch_assum_rename_tac`pmatch_exh s p v (TAKE n env) = Match env1`[] >>
  pop_assum(qspec_then`LENGTH env1`mp_tac) >>
  simp_tac(srw_ss())[rich_listTheory.TAKE_LENGTH_APPEND,rich_listTheory.DROP_LENGTH_APPEND] )

val pmatch_exh_nil = save_thm("pmatch_exh_nil",
  LIST_CONJ [
    pmatch_exh_APPEND
    |> CONJUNCT1
    |> Q.SPECL[`s`,`p`,`v`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ,
    pmatch_exh_APPEND
    |> CONJUNCT2
    |> Q.SPECL[`s`,`ps`,`vs`,`env`,`0`]
    |> SIMP_RULE(srw_ss())[]
  ])

val _ = export_theory ();
