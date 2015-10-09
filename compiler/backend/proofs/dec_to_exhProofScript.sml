open preamble
     semanticPrimitivesTheory
     dec_to_exhTheory
     exhSemTheory exhPropsTheory

val _ = new_theory "dec_to_exhProof";

val find_recfun_compile_funs = prove(
  ``∀ls f exh. find_recfun f (compile_funs exh ls) =
               OPTION_MAP (λ(x,y). (x,compile_exp exh y)) (find_recfun f ls)``,
  Induct >> simp[compile_funs_map] >- (
    simp[semanticPrimitivesTheory.find_recfun_def] ) >>
  simp[Once semanticPrimitivesTheory.find_recfun_def] >>
  simp[Once semanticPrimitivesTheory.find_recfun_def,SimpRHS] >>
  rpt gen_tac >>
  every_case_tac >>
  simp[] >> fs[compile_funs_map]);

val exhaustive_match_submap = prove(
  ``exhaustive_match exh pes ∧ exh ⊑ exh2 ⇒ exhaustive_match exh2 pes``,
  rw[exhaustive_match_def] >>
  every_case_tac >> fs[] >>
  imp_res_tac FLOOKUP_SUBMAP >> fs[] >> rw[])

(* value relation *)

val get_tag_def = Define`
  get_tag NONE = tuple_tag ∧
  get_tag (SOME p) = FST p`
val _ = export_rewrites["get_tag_def"]

val (v_rel_rules, v_rel_ind, v_rel_cases) = Hol_reln `
  (!exh l.
    v_rel exh (Litv l) (Litv l)) ∧
  (!exh t vs vs'.
    vs_rel exh vs vs'
    ⇒
    v_rel exh (Conv t vs) (Conv (get_tag t) vs')) ∧
  (!exh env x e env' exh'.
    exh' SUBMAP exh ∧
    env_rel exh env env'
    ⇒
    v_rel exh (Closure env x e) (Closure env' x (compile_exp exh' e))) ∧
  (!exh env x funs exh'.
    exh' SUBMAP exh ∧
    env_rel exh env env'
    ⇒
    v_rel exh (Recclosure env funs x) (Recclosure env' (compile_funs exh' funs) x)) ∧
  (!exh l.
    v_rel exh (Loc l) (Loc l)) ∧
  (!exh vs vs'.
    vs_rel exh vs vs'
    ⇒
    v_rel exh (Vectorv vs) (Vectorv vs')) ∧
  (!exh.
    vs_rel exh [] []) ∧
  (!exh v v' vs vs'.
    v_rel exh v v' ∧
    vs_rel exh vs vs'
    ⇒
    vs_rel exh (v::vs) (v'::vs')) ∧
  (!exh.
    env_rel exh [] []) ∧
  (!exh x v v' env env'.
    v_rel exh v v' ∧
    env_rel exh env env'
    ⇒
    env_rel exh ((x,v)::env) ((x,v')::env'))`;

val v_rel_eqn = Q.prove (
  `(!exh l v.
    v_rel exh (Litv l) v ⇔
     v = Litv l) ∧
   (!exh t vs v.
    v_rel exh (Conv t vs) v ⇔
     ?vs'.
      vs_rel exh vs vs' ∧
      v = Conv (get_tag t) vs') ∧
   (!exh l.
    v_rel exh (Loc l) v ⇔
     v = Loc l) ∧
   (!exh vs v.
    v_rel exh (Vectorv vs) v ⇔
     ?vs'.
      vs_rel exh vs vs' ∧
      v = Vectorv vs') ∧
   (!exh vs. vs_rel exh [] vs ⇔ vs = []) ∧
   (!exh v vs vs'.
    vs_rel exh (v::vs) vs' ⇔
    ?v' vs''.
      vs' = v'::vs'' ∧
      v_rel exh v v' ∧
      vs_rel exh vs vs'') ∧
   (!exh env. env_rel exh [] env ⇔ env = []) ∧
   (!exh x v env env'.
    env_rel exh ((x,v)::env) env' ⇔
    ?v' env''.
      env' = (x,v') :: env'' ∧
      v_rel exh v v' ∧
      env_rel exh env env'')`,
   rw [] >>
   rw [Once v_rel_cases] >>
   metis_tac []);

val vs_rel_LIST_REL = prove(
  ``∀vs vs' exh. vs_rel exh vs vs' = LIST_REL (v_rel exh) vs vs'``,
  Induct >> simp[v_rel_eqn])

val env_rel_LIST_REL = Q.prove(
  `!exh env env'. env_rel exh env env' = LIST_REL (λ(x,y) (x',y'). x = x' ∧ v_rel exh y y') env env'`,
  Induct_on`env`>>simp[v_rel_eqn]>>Cases>>simp[v_rel_eqn] >>
  rw [EXISTS_PROD]);

val env_rel_MAP = store_thm("env_rel_MAP",
  ``∀exh env1 env2. env_rel exh env1 env2 ⇔ MAP FST env1 = MAP FST env2 ∧
      LIST_REL (v_rel exh) (MAP SND env1) (MAP SND env2)``,
  Induct_on`env1`>>simp[Once v_rel_cases] >>
  Cases >> Cases_on`env2` >> rw[] >>
  Cases_on`h`>>rw[] >> metis_tac[])

val _ = augment_srw_ss[rewrites[vs_rel_LIST_REL,find_recfun_compile_funs]]

val v_rel_lit_loc = store_thm("v_rel_lit_loc[simp]",
  ``(v_rel exh (Litv l) lh ⇔ lh = Litv l) ∧
    (v_rel exh l2 (Litv l) ⇔ l2 = Litv l) ∧
    (v_rel exh (Loc n) lh ⇔ lh = Loc n) ∧
    (v_rel exh l2 (Loc n) ⇔ l2 = Loc n) ∧
    (v_rel exh (Conv t []) lh ⇔ lh = Conv (get_tag t) []) ∧
    (v_rel exh (Boolv b) lh ⇔ lh = Boolv b)``,
  rw[] >> rw[Once v_rel_cases, conSemTheory.Boolv_def, exhSemTheory.Boolv_def])

val (result_rel_rules, result_rel_ind, result_rel_cases) = Hol_reln `
  (∀exh v v' s s'.
    f exh v v' ∧
    csg_rel (v_rel exh) s s'
    ⇒
    result_rel f exh (s,Rval v) (s',Rval v')) ∧
  (∀exh v v' s s'.
    v_rel exh v v' ∧
    csg_rel (v_rel exh) s s'
    ⇒
    result_rel f exh (s,Rerr (Rraise v)) (s',Rerr (Rraise v'))) ∧
  (!exh s s' a.
    csg_rel (v_rel exh) s s'
    ⇒
    result_rel f exh (s,Rerr (Rabort a)) (s',Rerr (Rabort a)))`;

val match_result_rel_def = Define
  `(match_result_rel exh (Match env) (Match env_exh) ⇔
     env_rel exh env env_exh) ∧
   (match_result_rel exh No_match No_match = T) ∧
   (match_result_rel exh Match_type_error Match_type_error = T) ∧
   (match_result_rel exh _ _ = F)`;

val match_result_error = Q.prove (
  `(!exh r. match_result_rel exh r Match_type_error ⇔ r = Match_type_error) ∧
   (!exh r. match_result_rel exh Match_type_error r ⇔ r = Match_type_error)`,
  rw [] >>
  cases_on `r` >>
  rw [match_result_rel_def]);

val match_result_nomatch = Q.prove (
  `(!exh r. match_result_rel exh r No_match ⇔ r = No_match) ∧
   (!exh r. match_result_rel exh No_match r ⇔ r = No_match)`,
  rw [] >>
  cases_on `r` >>
  rw [match_result_rel_def]);

(* semantic functions preserve relation *)

val do_eq = Q.prove (
  `(!v1 v2 tagenv r v1_exh v2_exh (exh:exh_ctors_env).
    do_eq v1 v2 = r ∧ r ≠ Eq_type_error ∧
    v_rel exh v1 v1_exh ∧
    v_rel exh v2 v2_exh
    ⇒
    do_eq v1_exh v2_exh = r) ∧
   (!vs1 vs2 tagenv r vs1_exh vs2_exh (exh:exh_ctors_env).
    do_eq_list vs1 vs2 = r ∧ r ≠ Eq_type_error ∧
    vs_rel exh vs1 vs1_exh ∧
    vs_rel exh vs2 vs2_exh
    ⇒
    do_eq_list vs1_exh vs2_exh = r)`,
  ho_match_mp_tac conSemTheory.do_eq_ind >>
  reverse(rw[exhSemTheory.do_eq_def,conSemTheory.do_eq_def,v_rel_eqn]) >>
  rw[v_rel_eqn, exhSemTheory.do_eq_def] >>
  fs[exhSemTheory.do_eq_def]
  >- (every_case_tac >>
      rw [] >>
      fs [] >>
      metis_tac [eq_result_distinct, eq_result_11]) >>
  fs [Once v_rel_cases] >>
  rw [exhSemTheory.do_eq_def] >>
  fs [] >>
  TRY(metis_tac [LIST_REL_LENGTH])
  >> (
    Cases_on`t1`>>fs[] >>
    Cases_on`t2`>>fs[] >>
    rfs[] >> rw[] >> fs[])) ;

val pmatch = Q.prove (
  `(!(exh:exh_ctors_env) s p v env r env_exh s_exh v_exh.
    r ≠ Match_type_error ∧
    pmatch exh s p v env = r ∧
    LIST_REL (sv_rel (v_rel exh)) s s_exh ∧
    v_rel exh v v_exh ∧
    env_rel exh env env_exh
    ⇒
    ?r_exh.
      pmatch s_exh (compile_pat p) v_exh env_exh = r_exh ∧
      match_result_rel exh r r_exh) ∧
   (!(exh:exh_ctors_env) s ps vs env r env_exh s_exh vs_exh.
    r ≠ Match_type_error ∧
    pmatch_list exh s ps vs env = r ∧
    LIST_REL (sv_rel (v_rel exh)) s s_exh ∧
    vs_rel exh vs vs_exh ∧
    env_rel exh env env_exh
    ⇒
    ?r_exh.
      pmatch_list s_exh (MAP compile_pat ps) vs_exh env_exh = r_exh ∧
      match_result_rel exh r r_exh)`,
  ho_match_mp_tac conSemTheory.pmatch_ind >>
  rw [conSemTheory.pmatch_def, exhSemTheory.pmatch_def, compile_pat_def, match_result_rel_def] >>
  fs [match_result_rel_def, v_rel_eqn] >>
  rw [exhSemTheory.pmatch_def, match_result_rel_def, match_result_error] >>
  imp_res_tac LIST_REL_LENGTH >>
  fs []
  >- metis_tac []
  >- (every_case_tac >>
      fs [LET_THM] >>
      pop_assum mp_tac >> simp[] >>
      rw[] >> rfs[] >> fs[] >>
      metis_tac [])
  >- (every_case_tac >>
      fs [LET_THM] >>
      pop_assum mp_tac >> simp[] >>
      BasicProvers.CASE_TAC >> simp[]>>
      rw[match_result_rel_def])
  >- (every_case_tac >>
      fs[LET_THM] >>
      pop_assum mp_tac >> simp[] >>
      BasicProvers.CASE_TAC >> simp[]>>
      rw[match_result_rel_def])
  >- metis_tac []
  >- (every_case_tac >>
      fs [match_result_error, store_lookup_def, LIST_REL_EL_EQN] >>
      rfs[] >> metis_tac [evalPropsTheory.sv_rel_def])
  >- (every_case_tac >>
      rw [match_result_rel_def] >>
      res_tac >>
      fs [match_result_nomatch] >>
      cases_on `pmatch s_exh (compile_pat p) y env_exh` >>
      fs [match_result_rel_def] >>
      metis_tac []));

val pat_bindings = prove(
  ``(∀p ls. pat_bindings (compile_pat p) ls = pat_bindings p ls) ∧
    (∀ps ls. pats_bindings (MAP compile_pat ps) ls = pats_bindings ps ls)``,
  ho_match_mp_tac(TypeBase.induction_of(``:conLang$pat``)) >>
  simp[conSemTheory.pat_bindings_def,exhSemTheory.pat_bindings_def,compile_pat_def] >>
  rw[] >> cases_on`o'` >>
  TRY(cases_on`x`)>>
  rw[compile_pat_def,exhSemTheory.pat_bindings_def,ETA_AX])

val v_to_list = Q.prove (
  `!v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_list v1 = SOME vs1
    ⇒
    ?vs2.
      v_to_list v2 = SOME vs2 ∧
      vs_rel genv vs1 vs2`,
  ho_match_mp_tac conSemTheory.v_to_list_ind >>
  rw [conSemTheory.v_to_list_def] >>
  every_case_tac >>
  fs [v_rel_eqn, exhSemTheory.v_to_list_def] >>
  rw [] >>
  every_case_tac >>
  fs [v_rel_eqn, exhSemTheory.v_to_list_def] >>
  rw [] >>
  metis_tac [NOT_SOME_NONE, SOME_11]);

val char_list_to_v = prove(
  ``∀ls. v_rel exh (char_list_to_v ls) (char_list_to_v ls)``,
  Induct >> simp[conSemTheory.char_list_to_v_def,exhSemTheory.char_list_to_v_def] >>
  simp[v_rel_eqn])

val v_to_char_list = Q.prove (
  `!v1 v2 vs1.
    v_rel genv v1 v2 ∧
    v_to_char_list v1 = SOME vs1
    ⇒
    v_to_char_list v2 = SOME vs1`,
  ho_match_mp_tac conSemTheory.v_to_char_list_ind >>
  rw [conSemTheory.v_to_char_list_def] >>
  every_case_tac >>
  fs [v_rel_eqn, exhSemTheory.v_to_char_list_def]);

val tac =
  rw [exhSemTheory.do_app_def, result_rel_cases, conSemTheory.prim_exn_def, conSemTheory.exn_tag_def,
      exhSemTheory.prim_exn_def, v_rel_eqn, conSemTheory.Boolv_def, exhSemTheory.Boolv_def] >>
  fs [] >>
  fs [store_assign_def,store_lookup_def, store_alloc_def,
      LET_THM] >>
  rw [] >>
  imp_res_tac LIST_REL_LENGTH >>
  fs [conSemTheory.prim_exn_def, v_rel_eqn, conSemTheory.exn_tag_def] >>
  every_case_tac >>
  fs [LIST_REL_EL_EQN, EL_LUPDATE,decPropsTheory.csg_rel_def] >>
  rw [EL_LUPDATE, evalPropsTheory.sv_rel_def] >>
  res_tac >>
  pop_assum mp_tac >>
  ASM_REWRITE_TAC [evalPropsTheory.sv_rel_def] >>
  fs [v_rel_eqn, store_v_same_type_def] >>
  every_case_tac >>
  fs [] >> rfs[];

val do_app_lem = Q.prove (
  `!(exh:exh_ctors_env) s1 op vs s2 res s1_exh vs_exh c g.
    conSem$do_app s1 op vs = SOME (s2, res) ∧
    csg_rel (v_rel exh) ((c,s1),g) s1_exh ∧
    vs_rel exh vs vs_exh
    ⇒
     ∃s2_exh res_exh.
       result_rel v_rel exh (((c,s2),g),res) (s2_exh,res_exh) ∧
       do_app s1_exh op vs_exh = SOME (s2_exh, res_exh)`,
  rw [] >>
  PairCases_on `s1` >>
  PairCases_on `s1_exh` >>
  imp_res_tac conPropsTheory.do_app_cases >>
  fs [] >>
  rw [] >>
  fs [conSemTheory.do_app_def]
  >- tac
  >- tac
  >- (every_case_tac >>
      imp_res_tac do_eq >>
      fs [] >>
      rw [exhSemTheory.do_app_def, result_rel_cases, conSemTheory.exn_tag_def,
          conSemTheory.prim_exn_def, exhSemTheory.prim_exn_def, v_rel_eqn,
          conSemTheory.Boolv_def, exhSemTheory.Boolv_def])
  >- (tac >>
      metis_tac [v_rel_eqn, store_v_distinct, evalPropsTheory.sv_rel_def])
  >- tac
  >- (tac >>
    Cases_on`n < LENGTH s1_exh1`>>simp[EL_APPEND1,EL_APPEND2] >>
    strip_tac >> `n = LENGTH s1_exh1` by simp[] >> simp[])
  >- ( tac >>
    Cases_on`n' < LENGTH s1_exh1`>>simp[EL_APPEND1,EL_APPEND2] >>
    strip_tac >> `n' = LENGTH s1_exh1` by simp[] >> simp[])
  >- (tac >>
      metis_tac [v_rel_eqn, store_v_distinct, evalPropsTheory.sv_rel_def])
  >- tac
  >- (tac >>
      metis_tac [v_rel_eqn, store_v_distinct, evalPropsTheory.sv_rel_def])
  >- tac
  >- tac
  >- tac
  >- ( tac >> metis_tac[char_list_to_v] )
  >- ( imp_res_tac v_to_char_list >> tac)
  >- tac
  >- (imp_res_tac v_to_list >>
      rw [exhSemTheory.do_app_def, result_rel_cases, v_rel_eqn] >>
      fs [vs_rel_LIST_REL])
  >- (tac >>
      full_simp_tac (srw_ss()++ARITH_ss) [])
  >- tac
  >- (tac >>
      rw [LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE] >>
    Cases_on`n' < LENGTH s1_exh1`>>simp[EL_APPEND1,EL_APPEND2] >>
    `n' = LENGTH s1_exh1` by simp[] >> simp[] >>
      rw [LIST_REL_EL_EQN, LENGTH_REPLICATE, EL_REPLICATE] )
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
  >- (tac >> rw []
      >- (CCONTR_TAC >>
          fs [] >>
          imp_res_tac LIST_REL_LENGTH >>
          full_simp_tac (srw_ss()++ARITH_ss) [])
      >- (CCONTR_TAC >>
          fs [] >>
          imp_res_tac LIST_REL_LENGTH >>
          full_simp_tac (srw_ss()++ARITH_ss) [])
      >- (ASM_REWRITE_TAC [evalPropsTheory.sv_rel_def, vs_rel_LIST_REL] >>
          match_mp_tac EVERY2_LUPDATE_same >>
          fs [] ))
   >- (tac >>
       `l = l'` by metis_tac[evalPropsTheory.sv_rel_def] >>
       fs[]));

val do_app = prove(
  ``∀s1 op vs s2 res exh s1 s1_exh vs_exh.
      decSem$do_app s1 op vs = SOME (s2,res) ∧
      csg_rel (v_rel exh) s1 s1_exh ∧
      vs_rel exh vs vs_exh ⇒
      ∃s2_exh res_exh.
        do_app s1_exh op vs_exh = SOME (s2_exh,res_exh) ∧
        result_rel v_rel exh (s2,res) (s2_exh,res_exh)``,
  rpt gen_tac >>
  PairCases_on`s1` >>
  PairCases_on`s1_exh` >>
  rw[decSemTheory.do_app_def] >>
  Cases_on`op`>>fs[] >- (
    every_case_tac >> fs[] >>
    first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]do_app_lem)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    simp[vs_rel_LIST_REL] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    metis_tac[] ) >>
  simp[exhSemTheory.do_app_def] >>
  fs[LIST_REL_EL_EQN,decPropsTheory.csg_rel_def,result_rel_cases] >>
  every_case_tac >> fs[] >> rw[] >> fs[decPropsTheory.csg_rel_def] >>
  fs[LIST_REL_EL_EQN,OPTREL_def,EL_LUPDATE,evalPropsTheory.sv_rel_cases] >>
  rw[] >> metis_tac[NOT_SOME_NONE]);

val do_opapp = prove(
  ``∀vs env e exh vs_exh.
    do_opapp vs = SOME (env,e) ∧
    vs_rel exh vs vs_exh
    ⇒
    ∃exh' env_exh.
      env_rel exh env env_exh ∧
      exh' ⊑ exh ∧
      do_opapp vs_exh = SOME (env_exh,compile_exp exh' e)``,
  rw[conSemTheory.do_opapp_def,exhSemTheory.do_opapp_def] >>
  every_case_tac >> fs[] >> rw[] >>
  TRY (fs[Once v_rel_cases]>>NO_TAC) >>
  fs[Q.SPECL[`exh`,`Closure X Y Z`](CONJUNCT1 v_rel_cases),env_rel_LIST_REL] >>
  fs[Q.SPECL[`exh`,`Recclosure X Y Z`](CONJUNCT1 v_rel_cases),env_rel_LIST_REL] >>
  rw[] >> fs[find_recfun_compile_funs] >> rw[] >>
  fs[compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,FST_triple,ETA_AX]
  >- metis_tac[SUBMAP_REFL] >>
  simp[exhPropsTheory.build_rec_env_merge,conPropsTheory.build_rec_env_merge] >>
  qexists_tac`exh'`>>simp[] >>
  match_mp_tac EVERY2_APPEND_suff >>
  simp[EVERY2_MAP,UNCURRY] >>
  simp[Once v_rel_cases,compile_funs_map,MAP_EQ_f] >>
  match_mp_tac EVERY2_refl >>
  simp[UNCURRY,env_rel_LIST_REL] >>
  metis_tac[]);

(* compiler correctness *)

val exists_match_def = Define `
  exists_match exh s ps v ⇔
    !env. ?p. MEM p ps ∧ pmatch exh s p v env ≠ No_match`;

val is_unconditional_thm = prove(
  ``∀p a b c d. is_unconditional p ⇒ pmatch a b p c d ≠ No_match``,
  ho_match_mp_tac is_unconditional_ind >>
  Cases >> rw[] >>
  Cases_on`c`>>rw[conSemTheory.pmatch_def]
  >- (
    fs[is_unconditional_def] )
  >- (
    pop_assum mp_tac >>
    rw[Once is_unconditional_def] >>
    every_case_tac >> fs[] >>
    Cases_on`o''`>>rw[conSemTheory.pmatch_def] >>
    fs[PULL_FORALL] >> rfs[EVERY_MEM] >>
    pop_assum mp_tac >>
    map_every qid_spec_tac[`l'`,`a`,`b`,`d`] >>
    Induct_on`l` >> simp[LENGTH_NIL_SYM,conSemTheory.pmatch_def] >>
    rw[] >> Cases_on`l'`>>fs[] >>
    rw[conSemTheory.pmatch_def] >>
    BasicProvers.CASE_TAC >>
    metis_tac[] )
  >- (
    pop_assum mp_tac >>
    rw[Once is_unconditional_def] >>
    BasicProvers.EVERY_CASE_TAC >>
    metis_tac[]))

val is_unconditional_list_thm = prove(
  ``∀l1 l2 a b c. EVERY is_unconditional l1 ⇒ pmatch_list a b l1 l2 c ≠ No_match``,
  Induct >> Cases_on`l2` >> simp[conSemTheory.pmatch_def] >>
  rw[] >>
  BasicProvers.CASE_TAC >>
  metis_tac[is_unconditional_thm])

val get_tags_thm = Q.prove(
  `∀ps t1 t2. get_tags ps t1 = SOME t2 ⇒
      (∀p. MEM p ps ⇒ ∃t x vs left.
             (p = Pcon (SOME (t,x)) vs) ∧ EVERY is_unconditional vs ∧
             lookup (LENGTH vs) t2 = SOME left ∧ t ∉ domain left) ∧
      (∀a tags.
        lookup a t1 = SOME tags ⇒
        ∃left. lookup a t2 = SOME left ∧ domain left ⊆ domain tags ∧
               (∀t. t ∈ domain tags ∧ t ∉ domain left ⇒
                    ∃x vs. MEM (Pcon (SOME (t,x)) vs) ps ∧ EVERY is_unconditional vs ∧
                           LENGTH vs = a))`,
  Induct >> simp[get_tags_def] >>
  Cases >> simp[] >>
  Cases_on`o'`>>simp[]>>
  Cases_on`x`>>simp[]>>
  rpt gen_tac >>
  BasicProvers.CASE_TAC >>
  strip_tac >>
  first_x_assum(fn th=> first_x_assum(mp_tac o MATCH_MP th)) >>
  strip_tac >>
  conj_tac >- (
    gen_tac >> strip_tac >- (
      simp[] >>
      first_x_assum(qspec_then`LENGTH l`mp_tac) >>
      simp[sptreeTheory.lookup_insert] >>
      simp[SUBSET_DEF] >>
      strip_tac >> simp[] >>
      metis_tac[] ) >>
    metis_tac[] ) >>
  rw[] >>
  first_x_assum(qspec_then`a`mp_tac) >>
  simp[sptreeTheory.lookup_insert] >>
  rw[] >- (
    simp[] >> rfs[] >>
    fs[SUBSET_DEF] >>
    metis_tac[] ) >>
  metis_tac[])

val pmatch_Pcon_No_match = prove(
  ``EVERY is_unconditional ps ⇒
    ((pmatch exh s (Pcon (SOME(c,TypeId t)) ps) v env = No_match) ⇔
     ∃cv vs tags max maxv.
       v = Conv (SOME(cv,TypeId t)) vs ∧
       FLOOKUP exh t = SOME tags ∧
       lookup (LENGTH ps) tags = SOME max ∧
       lookup (LENGTH vs) tags = SOME maxv ∧
       c < max ∧ cv < maxv ∧
       (LENGTH ps = LENGTH vs ⇒ c ≠ cv))``,
  Cases_on`v`>>rw[conSemTheory.pmatch_def]>>
  Cases_on`o'`>>simp[conSemTheory.pmatch_def] >>
  PairCases_on`x`>>simp[conSemTheory.pmatch_def]>>
  Cases_on`x1`>>simp[conSemTheory.pmatch_def]>>
  rw[] >> every_case_tac >> rw[] >> fs[] >>
  metis_tac[is_unconditional_list_thm])

val exh_to_exists_match = Q.prove (
  `!exh ps. exhaustive_match exh ps ⇒ !s v. exists_match exh s ps v`,
  rw [exhaustive_match_def, exists_match_def] >- (
    fs[EXISTS_MEM] >>
    metis_tac[is_unconditional_thm] ) >>
  every_case_tac >>
  fs [get_tags_def, conSemTheory.pmatch_def] >> rw[] >>
  imp_res_tac get_tags_thm >>
  Q.PAT_ABBREV_TAC`pp1 = Pcon X l` >>
  Cases_on`v`>>
  TRY(qexists_tac`pp1`>>simp[conSemTheory.pmatch_def,Abbr`pp1`]>>NO_TAC) >>
  srw_tac[boolSimps.DNF_ss][]>>
  simp[Abbr`pp1`,pmatch_Pcon_No_match]>>
  simp[METIS_PROVE[]``a \/ b <=> ~a ==> b``] >>
  strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  fs[sptreeTheory.lookup_map,sptreeTheory.domain_fromList,PULL_EXISTS] >>
  res_tac >>
  rfs[EVERY_MEM,sptreeTheory.MEM_toList,PULL_EXISTS] >>
  res_tac >> fs[] >> rfs[] >> rw[] >>
  first_assum(match_exists_tac o concl) >>
  simp[conSemTheory.pmatch_def] >>
  Cases_on`x'''`>>simp[conSemTheory.pmatch_def] >>
  rw[] >>
  metis_tac[is_unconditional_list_thm,EVERY_MEM])

fun exists_lift_conj_tac tm =
  CONV_TAC(
    STRIP_BINDER_CONV(SOME existential)
      (lift_conjunct_conv(same_const tm o fst o strip_comb)))

val Boolv_disjoint = LIST_CONJ [
  EVAL``conSem$Boolv T = Boolv F``,
  EVAL``exhSem$Boolv T = Boolv F``]

val s = mk_var("s",
  ``decSem$evaluate`` |> type_of |> strip_fun |> #1 |> el 3
  |> type_subst[alpha |-> ``:'ffi``])

val compile_exp_correct = Q.store_thm ("compile_exp_correct",
  `(!ck env ^s e r.
    evaluate ck env s e r
    ⇒
    !(exh:exh_ctors_env) env' env_exh s_exh exh'.
      SND r ≠ Rerr (Rabort Rtype_error) ∧
      env = (exh,env') ∧
      env_rel exh env' env_exh ∧
      csg_rel (v_rel exh) s s_exh ∧
      exh' ⊑ exh
      ⇒
      ?r_exh.
      result_rel v_rel exh r r_exh ∧
      evaluate ck env_exh s_exh (compile_exp exh' e) r_exh) ∧
   (!ck env ^s es r.
    evaluate_list ck env s es r
    ⇒
    !(exh:exh_ctors_env) env' env_exh s_exh exh'.
      SND r ≠ Rerr (Rabort Rtype_error) ∧
      env = (exh,env') ∧
      env_rel exh env' env_exh ∧
      csg_rel (v_rel exh) s s_exh ∧
      exh' ⊑ exh
      ⇒
      ?r_exh.
      result_rel vs_rel exh r r_exh ∧
      evaluate_list ck env_exh s_exh (compile_exps exh' es) r_exh) ∧
   (!ck env ^s v pes err_v r.
    evaluate_match ck env s v pes err_v r
    ⇒
    !(exh:exh_ctors_env) env' pes' is_handle env_exh s_exh v_exh exh'.
      SND r ≠ Rerr (Rabort Rtype_error) ∧
      env = (exh,env') ∧
      env_rel exh env' env_exh ∧
      csg_rel (v_rel exh) s s_exh ∧
      v_rel exh v v_exh ∧
      (is_handle ⇒ err_v = v) ∧
      (¬is_handle ⇒ err_v = Conv (SOME (bind_tag, (TypeExn(Short "Bind")))) []) ∧
      (pes' = add_default is_handle F pes ∨
       exists_match exh (FST (SND (FST s))) (MAP FST pes) v ∧
       pes' = add_default is_handle T pes) ∧
      exh' ⊑ exh
       ⇒
      ?r_exh.
      result_rel v_rel exh r r_exh ∧
      evaluate_match ck env_exh s_exh v_exh (compile_pes exh' pes') r_exh)`,
  ho_match_mp_tac decSemTheory.evaluate_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[compile_exp_def] >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_exp_def] >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_exp_def] >> fs[] >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    metis_tac[]) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >> disj1_tac >>
    fs[GSYM AND_IMP_INTRO] >>
    last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rator_x_assum`result_rel`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_rel_cases]) >>
    exists_lift_conj_tac``exhSem$evaluate`` >> fs[] >>
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
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >> disj2_tac >>
    simp[Once result_rel_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    Cases_on`tag`>>TRY(Cases_on`x`)>>simp[compile_exp_def] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    metis_tac[EVERY2_REVERSE, compile_exps_map, MAP_REVERSE] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    Cases_on`tag`>>TRY(Cases_on`x`)>>simp[compile_exp_def] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    fs [compile_exps_map, MAP_REVERSE] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    metis_tac[EVERY2_REVERSE] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    pop_assum kall_tac >>
    rpt (pop_assum mp_tac) >>
    map_every qid_spec_tac[`env_exh`,`n`,`v`,`env`] >>
    Induct >> simp[] >>
    Cases >> fs[env_rel_LIST_REL] >>
    rw[EXISTS_PROD] >> simp[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    PairCases_on`s`>>PairCases_on`s_exh`>>simp[] >>
    fs[decPropsTheory.csg_rel_def] >>
    rfs[EVERY2_EVERY,EVERY_MEM] >>
    fs[MEM_ZIP,PULL_EXISTS] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[optionTheory.OPTREL_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    simp[Once v_rel_cases] >>
    HINT_EXISTS_TAC >> simp[]) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >>
    simp[Once result_rel_cases,PULL_EXISTS] >>
    strip_tac >>
    rpt gen_tac >> strip_tac >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    strip_tac >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    exists_lift_conj_tac``exhSem$evaluate_list`` >>
    PairCases_on`s'` >>
    PairCases_on`s_exh` >>
    fs [compile_exps_map, MAP_REVERSE] >>
    first_assum(match_exists_tac o concl) >>
    simp[] >>
    first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]do_opapp)) >>
    simp[vs_rel_LIST_REL] >>
    imp_res_tac EVERY2_REVERSE >>
    disch_then(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_assum(match_exists_tac o concl) >> simp[] >> fs[] >>
    fs[] >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    simp[FORALL_PROD] >>
    fs[decPropsTheory.csg_rel_def] >>
    ONCE_REWRITE_TAC[GSYM CONJ_ASSOC] >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    strip_tac >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    strip_tac >>
    fs [compile_exps_map, MAP_REVERSE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    disj2_tac >> disj1_tac >>
    exists_lift_conj_tac``exhSem$evaluate_list`` >>
    PairCases_on`s''`>>fs[]>>rw[]>>
    imp_res_tac decPropsTheory.csg_rel_count >> rfs[] >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    imp_res_tac do_opapp >>
    metis_tac[vs_rel_LIST_REL, EVERY2_REVERSE] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
    simp[Once result_rel_cases] >> strip_tac >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    exists_lift_conj_tac``exhSem$evaluate_list`` >>
    fs [compile_exps_map, MAP_REVERSE] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    first_assum(mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] do_app)) >>
    disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
    simp[vs_rel_LIST_REL, EVERY2_REVERSE] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[] >>
    fs[GSYM AND_IMP_INTRO] >>
    last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >>
    rpt disj2_tac >>
    fs[result_rel_cases,PULL_EXISTS] >> rw[] >>
    metis_tac[compile_exps_map, MAP_REVERSE] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[GSYM AND_IMP_INTRO] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    exists_lift_conj_tac``exhSem$evaluate`` >>
    rator_x_assum`result_rel`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_rel_cases]) >> fs[] >>
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
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    fs[GSYM AND_IMP_INTRO] >>
    last_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    first_x_assum(fn th => first_assum(strip_assume_tac o MATCH_MP th)) >>
    rator_x_assum`result_rel`(strip_assume_tac o SIMP_RULE(srw_ss())[Once result_rel_cases]) >>
    exists_lift_conj_tac``exhSem$evaluate`` >> fs[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    simp[env_rel_LIST_REL,libTheory.opt_bind_def] >>
    BasicProvers.CASE_TAC >> fs[env_rel_LIST_REL] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    fs[FST_triple,compile_funs_map,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    first_x_assum (match_mp_tac o MP_CANON) >> simp[] >>
    fs[env_rel_LIST_REL,conPropsTheory.build_rec_env_merge,exhPropsTheory.build_rec_env_merge] >>
    match_mp_tac EVERY2_APPEND_suff >>
    simp[EVERY2_MAP] >>
    match_mp_tac EVERY2_refl >>
    simp[FORALL_PROD] >>
    simp[Once v_rel_cases,compile_funs_map,MAP_EQ_f,FORALL_PROD,env_rel_LIST_REL] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rw[] >>
    rw[Once exhSemTheory.evaluate_cases] >>
    rw[Once result_rel_cases] >>
    srw_tac[DNF_ss][] >>
    simp[] >>
    PairCases_on`s`>>PairCases_on`s_exh`>>simp[] >>
    fs[decPropsTheory.csg_rel_def] >>
    match_mp_tac EVERY2_APPEND_suff >>
    simp[] >>
    simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] ) >>
  strip_tac >- (
    rw[] >>
    rw[Once result_rel_cases,PULL_EXISTS] >>
    simp[Once exhSemTheory.evaluate_cases,compile_exp_def] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    fs[Once result_rel_cases,PULL_EXISTS] >>
    simp[Once exhSemTheory.evaluate_cases,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    fs[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> fs[] >>
    fs[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    last_x_assum(fn th => first_assum(mp_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    rpt(disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th))) >> rw[] >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rw[add_default_def] >>
    simp[Once exhSemTheory.evaluate_cases,compile_exp_def,
         exhSemTheory.pat_bindings_def,compile_pat_def,exhSemTheory.pmatch_def] >>
    rw[Once exhSemTheory.evaluate_cases] >>
    fs[Once result_rel_cases,PULL_EXISTS,v_rel_eqn] >>
    fs[exists_match_def] >>
    rw[Once exhSemTheory.evaluate_cases] >>
    rw[Once exhSemTheory.evaluate_cases] >>
    rw[Once exhSemTheory.evaluate_cases] >>
    rw[Once exhSemTheory.evaluate_cases] >>
    PairCases_on`s_exh`>>simp[] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rw[add_default_def] >> rw[compile_exp_def] >>
    PairCases_on`s_exh` >> fs[decPropsTheory.csg_rel_def] >> rw[] >>
    full_simp_tac std_ss[GSYM vs_rel_LIST_REL] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj1_tac >>
    imp_res_tac (CONJUNCT1 pmatch) >>
    Cases_on`pmatch s_exh1 (compile_pat p) v_exh env_exh`>>
    fs[match_result_rel_def] >>
    simp[pat_bindings] >>
    first_x_assum match_mp_tac >>
    simp[decPropsTheory.csg_rel_def] ) >>
  strip_tac >- (
    simp[compile_exp_def] >>
    rw[add_default_def] >> rw[compile_exp_def] >>
    PairCases_on`s_exh` >> fs[decPropsTheory.csg_rel_def] >> rw[] >>
    full_simp_tac std_ss[GSYM vs_rel_LIST_REL] >>
    simp[Once exhSemTheory.evaluate_cases] >>
    srw_tac[DNF_ss][] >> disj2_tac >>
    imp_res_tac (CONJUNCT1 pmatch) >>
    Cases_on`pmatch s_exh1 (compile_pat p) v_exh env_exh`>>
    fs[match_result_rel_def] >>
    simp[pat_bindings] >>
    first_x_assum match_mp_tac >>
    simp[decPropsTheory.csg_rel_def] >>
    TRY (qexists_tac`T` >> simp[] >> NO_TAC) >>
    TRY (qexists_tac`F` >> simp[] >> NO_TAC) >>
    qexists_tac`is_handle`>>simp[] >> rw[] >> fs[] >>
    fs[exists_match_def,PULL_EXISTS] >>
    metis_tac[conPropsTheory.pmatch_any_no_match] ) >>
  rw[]);

val _ = export_theory ();
