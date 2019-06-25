(*
  A few properties about the relational big-step semantics.
*)
open preamble;
open semanticPrimitivesTheory;
open bigStepTheory;

val _ = new_theory "bigStepProps";

(* TODO see if this is actually needed
Theorem evaluate_decs_evaluate_prog_MAP_Tdec:
   ∀ck env cs tids ds res.
      evaluate_decs ck NONE env (cs,tids) ds res
      ⇔
      case res of ((s,tids'),envC,r) =>
      evaluate_prog ck env (cs,tids,{}) (MAP Tdec ds) ((s,tids',{}),([],envC),map_result(λenvE. ([],envE))(I)r)
Proof
  Induct_on`ds`>>simp[Once evaluate_decs_cases,Once evaluate_prog_cases] >- (
    rpt gen_tac >> BasicProvers.EVERY_CASE_TAC >> simp[] >>
    Cases_on`r'`>>simp[] ) >>
  srw_tac[DNF_ss][] >>
  PairCases_on`res`>>srw_tac[DNF_ss][]>>
  PairCases_on`env`>>srw_tac[DNF_ss][]>>
  simp[evaluate_top_cases] >> srw_tac[DNF_ss][] >>
  srw_tac[DNF_ss][EQ_IMP_THM] >- (
    Cases_on`e`>>simp[] )
  >- (
    disj1_tac >>
    CONV_TAC(STRIP_BINDER_CONV(SOME existential)(move_conj_left(equal``evaluate_dec`` o fst o strip_comb))) >>
    first_assum(split_pair_match o concl) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fsrw_tac[DNF_ss][EQ_IMP_THM] >>
    first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
    simp[] >> strip_tac >>
    full_simp_tac(srw_ss())[] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    Cases_on`r`>> simp[combine_dec_result_def,combine_mod_result_def,merge_alist_mod_env_def] )
  >- (
    disj2_tac >>
    CONV_TAC(STRIP_BINDER_CONV(SOME existential)(move_conj_left(equal``evaluate_dec`` o fst o strip_comb))) >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    fsrw_tac[DNF_ss][EQ_IMP_THM,FORALL_PROD,merge_alist_mod_env_def] >>
    `∃z. r' = map_result (λenvE. ([],envE)) I z` by (
      Cases_on`r'`>>full_simp_tac(srw_ss())[combine_mod_result_def] >>
      TRY(METIS_TAC[]) >>
      Cases_on`a`>>full_simp_tac(srw_ss())[]>>
      Cases_on`res4`>>full_simp_tac(srw_ss())[]>>srw_tac[][]>>
      qexists_tac`Rval r` >> simp[] ) >>
    PairCases_on`new_tds'`>>full_simp_tac(srw_ss())[merge_alist_mod_env_def]>>srw_tac[][]>>
    first_assum(match_exists_tac o concl) >> simp[] >>
    full_simp_tac(srw_ss())[combine_dec_result_def,combine_mod_result_def] >>
    BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[] >>
    TRY (Cases_on`res4`>>full_simp_tac(srw_ss())[]) >>
    Cases_on`a`>>Cases_on`e`>>full_simp_tac(srw_ss())[]>>srw_tac[][])
  >- (
    Cases_on`a`>>full_simp_tac(srw_ss())[])
QED

Theorem evaluate_decs_ctors_in:
   ∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
      ∀cn.
        IS_SOME (ALOOKUP (FST(SND res)) cn) ⇒
        MEM cn (FLAT (MAP ctors_of_dec decs))
Proof
  HO_MATCH_MP_TAC evaluate_decs_ind >>
  simp[] >>
  srw_tac[][Once evaluate_dec_cases] >> simp[] >>
  full_simp_tac(srw_ss())[ALOOKUP_APPEND] >>
  full_simp_tac(srw_ss())[] >>
  BasicProvers.EVERY_CASE_TAC >>
  full_simp_tac(srw_ss())[FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  full_simp_tac(srw_ss())[miscTheory.IS_SOME_EXISTS] >>
  full_simp_tac(srw_ss())[flookup_fupdate_list,MEM_MAP,semanticPrimitivesTheory.build_tdefs_def,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
  BasicProvers.EVERY_CASE_TAC >> full_simp_tac(srw_ss())[] >>
  imp_res_tac ALOOKUP_MEM >>
  full_simp_tac(srw_ss())[MEM_FLAT, MEM_MAP] >>
  srw_tac[][] >>
  PairCases_on `y` >>
  full_simp_tac(srw_ss())[MEM_MAP] >>
  srw_tac[][] >>
  PairCases_on `y` >>
  full_simp_tac(srw_ss())[] >>
  srw_tac[][] >>
  METIS_TAC[pair_CASES]
QED

  *)

val st = ``st:'ffi state``

Theorem evaluate_no_new_types_exns:
 (!ck env ^st e r. evaluate ck env st e r ⇒
   st.next_type_stamp = (FST r).next_type_stamp ∧
   st.next_exn_stamp = (FST r).next_exn_stamp) ∧
 (!ck env ^st es r. evaluate_list ck env st es r ⇒
   st.next_type_stamp = (FST r).next_type_stamp ∧
   st.next_exn_stamp = (FST r).next_exn_stamp) ∧
 (!ck env ^st v pes err_v r. evaluate_match ck env st v pes err_v r ⇒
   st.next_type_stamp = (FST r).next_type_stamp ∧
   st.next_exn_stamp = (FST r).next_exn_stamp)
Proof
 ho_match_mp_tac bigStepTheory.evaluate_ind >>
 srw_tac[][]
QED

Theorem evaluate_ignores_types_exns:
 (∀ck env ^st e r.
   evaluate ck env st e r ⇒
   !x y. evaluate ck env (st with <| next_type_stamp := x; next_exn_stamp := y |>) e
            ((FST r) with <| next_type_stamp := x; next_exn_stamp := y |>, SND r)) ∧
 (∀ck env ^st es r.
   evaluate_list ck env st es r ⇒
   !x y. evaluate_list ck env (st with <| next_type_stamp := x; next_exn_stamp := y |>) es
            ((FST r) with <| next_type_stamp := x; next_exn_stamp := y |>, SND r)) ∧
 (∀ck env ^st v pes err_v r.
   evaluate_match ck env st v pes err_v r ⇒
   !x y. evaluate_match ck env (st with <| next_type_stamp := x; next_exn_stamp := y |>) v pes err_v
            ((FST r) with <| next_type_stamp := x; next_exn_stamp := y |>, SND r))
Proof
 ho_match_mp_tac bigStepTheory.evaluate_ind >>
 srw_tac[][] >>
 srw_tac[][Once evaluate_cases, state_component_equality] >>
 metis_tac [state_accfupds, K_DEF]
QED

(*

Theorem eval_d_no_new_mods:
 !ck mn env st d r. evaluate_dec ck mn env st d r ⇒ st.defined_mods = (FST r).defined_mods
Proof
 srw_tac[][evaluate_dec_cases] >>
 imp_res_tac evaluate_no_new_types_mods >>
 full_simp_tac(srw_ss())[]
QED

Theorem eval_ds_no_new_mods:
 !ck mn env ^st ds r. evaluate_decs ck mn env st ds r ⇒ st.defined_mods = (FST r).defined_mods
Proof
 ho_match_mp_tac evaluate_decs_ind >>
 srw_tac[][] >>
 imp_res_tac eval_d_no_new_mods >>
 full_simp_tac(srw_ss())[]
QED
 *)

(* REPL bootstrap lemmas *)

(* TODO
val evaluate_decs_last3 = Q.prove(
  `∀ck mn env s decs a b c k i j s1 x y decs0 decs1 v p q r.
      evaluate_decs ck mn env s decs (((k,s1),a),b,Rval c) ∧
      decs = decs0 ++ [Dlet (Pvar x) (App Opref [Con i []]);Dlet(Pvar y)(App Opref [Con j []]);Dlet (Pvar p) (Fun q r)]
      ⇒
      ∃n ls1 ls2 ls iv jv.
      c = ((p,(Closure(FST env,merge_alist_mod_env([],b)(FST(SND env)),ls1 ++ SND(SND env)) q r))::ls1) ∧
      ls1 = ((y,Loc (n+1))::ls2) ∧ n+1 < LENGTH s1 ∧
      ls2 = ((x,Loc n)::ls) ∧
      build_conv (merge_alist_mod_env([],b)(FST(SND env))) i [] = SOME iv ∧
      build_conv (merge_alist_mod_env([],b)(FST(SND env))) j [] = SOME jv ∧
      (EL n s1 = Refv iv) ∧
      (EL (n+1) s1 = Refv jv)`,
  Induct_on`decs0` >>
  srw_tac[][Once bigStepTheory.evaluate_decs_cases] >- (
    full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases]>>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.combine_dec_result_def] >>
    full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_dec_cases] >>
    full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_cases] >>
    full_simp_tac(srw_ss())[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] >>
    full_simp_tac(srw_ss())[Once (CONJUNCT2 bigStepTheory.evaluate_cases)] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.do_app_def] >>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.store_alloc_def,LET_THM] >>
    full_simp_tac(srw_ss())[terminationTheory.pmatch_def] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases]>>
    full_simp_tac(srw_ss())[semanticPrimitivesTheory.combine_dec_result_def] >>
    full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_dec_cases] >>
    qhdtm_x_assum`evaluate`mp_tac >>
    simp[Once bigStepTheory.evaluate_cases] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[Once bigStepTheory.evaluate_decs_cases]>>
    srw_tac[][] >>
    full_simp_tac(srw_ss())[pmatch_def] >> srw_tac[][] >>
    full_simp_tac(srw_ss())[Once evaluate_cases] >>
    full_simp_tac(srw_ss())[Once evaluate_cases] >> srw_tac[][] >>
    PairCases_on`cenv` >>
    srw_tac[][merge_alist_mod_env_def] >>
    simp[rich_listTheory.EL_APPEND1,rich_listTheory.EL_APPEND2] >>
    full_simp_tac(srw_ss())[build_conv_def,merge_alist_mod_env_def,lookup_alist_mod_env_def,all_env_to_cenv_def]) >>
  Cases_on`r'`>>full_simp_tac(srw_ss())[semanticPrimitivesTheory.combine_dec_result_def]>>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP(REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
  rev_full_simp_tac(srw_ss())[semanticPrimitivesTheory.all_env_to_cenv_def] >>
  PairCases_on`cenv` >>
  full_simp_tac(srw_ss())[semanticPrimitivesTheory.merge_alist_mod_env_def, FUNION_ASSOC])

Theorem evaluate_Tmod_last3 = Q.prove(`
  evaluate_top ck env0 st (Tmod mn NONE decs) ((cs,u),envC,Rval ([(mn,env)],v)) ⇒
    decs = decs0 ++[Dlet (Pvar x) (App Opref [Con i []]);Dlet (Pvar y) (App Opref [Con j []]);Dlet (Pvar p) (Fun q z)]
  ⇒
    ∃n ls1 ls iv jv.
    env = (p,(Closure (FST env0,merge_alist_mod_env ([],THE (ALOOKUP (FST envC) mn)) (FST(SND env0)),ls++(SND(SND env0))) q z))::ls ∧
    (ls = (y,Loc (n+1))::(x,Loc n)::ls1) ∧
    n+1 < LENGTH (SND cs) ∧
    build_conv (merge_alist_mod_env ([],THE (ALOOKUP (FST envC) mn)) (FST(SND env0))) i [] = SOME iv ∧
    build_conv (merge_alist_mod_env ([],THE (ALOOKUP (FST envC) mn)) (FST(SND env0))) j [] = SOME jv ∧
    (EL n (SND cs) = Refv iv) ∧
    (EL (n+1) (SND cs) = Refv jv)`,
  Cases_on`cs`>>srw_tac[][bigStepTheory.evaluate_top_cases]>>
  imp_res_tac evaluate_decs_last3 >> full_simp_tac(srw_ss())[]) |> GEN_ALL

val evaluate_decs_tys = Q.prove(
  `∀decs0 decs1 decs ck mn env s s' tys c tds tvs tn cts cn as.
    evaluate_decs ck (SOME mn) env s decs (s',tys,Rval c) ∧
    decs = decs0 ++ [Dtype tds] ++ decs1 ∧
    MEM (tvs,tn,cts) tds ∧ MEM (cn,as) cts ∧
    ¬MEM cn (FLAT (MAP ctors_of_dec decs1))
    ⇒
    (ALOOKUP tys cn = SOME (LENGTH as, TypeId (Long mn tn)))`,
  Induct >> srw_tac[][Once evaluate_decs_cases] >- (
    full_simp_tac(srw_ss())[Once evaluate_dec_cases] >> srw_tac[][] >>
    simp[ALOOKUP_APPEND] >>
    imp_res_tac evaluate_decs_ctors_in >> full_simp_tac(srw_ss())[] >>
    BasicProvers.CASE_TAC >> full_simp_tac(srw_ss())[] >>
    Cases_on`ALOOKUP  (build_tdefs (SOME mn) tds) cn` >- (
      full_simp_tac(srw_ss())[FDOM_FUPDATE_LIST, ALOOKUP_NONE, semanticPrimitivesTheory.build_tdefs_def,MEM_MAP,MEM_FLAT,PULL_EXISTS,EXISTS_PROD] >>
      METIS_TAC[] ) >>
    pop_assum mp_tac >>
    simp[build_tdefs_def] >>
    simp[] >>
    srw_tac[][] >>
    imp_res_tac ALOOKUP_MEM >> full_simp_tac(srw_ss())[] >> srw_tac[][] >>
    qmatch_assum_abbrev_tac`ALOOKUP al k = SOME v` >>
    `ALL_DISTINCT (MAP FST al)` by (
      simp[Abbr`al`,ALL_DISTINCT_REVERSE,rich_listTheory.MAP_REVERSE] >>
      simp[MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
      full_simp_tac(srw_ss())[check_dup_ctors_thm,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,LAMBDA_PROD] ) >>
    qmatch_abbrev_tac`v = w` >>
    `MEM (k,w) al` by (
      simp[Abbr`al`] >>
      simp[Abbr`w`,MEM_FLAT,MEM_MAP,PULL_EXISTS,EXISTS_PROD,mk_id_def] >>
      METIS_TAC[]) >>
    imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> full_simp_tac(srw_ss())[]) >>
  simp[ALOOKUP_APPEND] >>
  Cases_on`r`>>full_simp_tac(srw_ss())[semanticPrimitivesTheory.combine_dec_result_def] >>
  first_x_assum(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO] th))) >>
  simp[])

Theorem evaluate_Tmod_tys
  `evaluate_top F env s (Tmod mn NONE decs) (s',([(m,tys)],e),Rval r) ⇒
    decs = decs0 ++ [Dtype tds] ++ decs1 ⇒
    MEM (tvs,tn,cts) tds ∧ MEM (cn,as) cts ∧
    ¬MEM cn (FLAT (MAP ctors_of_dec decs1))
    ⇒
    (ALOOKUP tys cn = SOME (LENGTH as, TypeId (Long mn tn)))`
  (srw_tac[][evaluate_top_cases,miscTheory.FEMPTY_FUPDATE_EQ] >>
  METIS_TAC[evaluate_decs_tys]) |> GEN_ALL
  *)

val _ = export_theory ();
