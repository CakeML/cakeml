open HolKernel bossLib boolLib boolSimps lcsymtacs ml_translatorLib ml_translatorTheory miscLib rich_listTheory
open compilerTerminationTheory semanticsExtraTheory intLangExtraTheory toIntLangProofsTheory toBytecodeProofsTheory compilerProofsTheory ml_repl_stepTheory oneshotTheory sideTheory BytecodeTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeTerminationTheory bootstrap_lemmaTheory
val _ = new_theory"bootstrap"

val _ = translation_extends"ml_repl_step"

(*
val _ = Globals.max_print_depth := 25

val bootstrap_result_def = Define`
  bootstrap_result = ^(rhs(concl(compiled)))`

val compiled1 = ONCE_REWRITE_RULE[GSYM bootstrap_result_def]compiled

val [ct,m,renv,rsz,cs] =
compiled1 |> concl |> lhs |> rator |> rand |> strip_pair
*)

val ct = ``init_compiler_state.contab``
val m = ``<|bvars:=["input"];mvars:=FEMPTY;cnmap:=cmap(^ct)|>``
val cs = ``<|out:=[];next_label:=init_compiler_state.rnext_label|>``
val renv = ``[CTDec 0]``
val rsz = ``1:num``

(*
val no_locs_Cv_bv = store_thm("no_locs_Cv_bv",
``∀Cv bv. all_Clocs Cv = {} ⇒ ∀bv pp pp'. (FST pp').cls = (FST pp).cls ∧ (SND pp') = SND pp ∧  Cv_bv pp Cv bv ⇒ Cv_bv pp' Cv bv``,
  ho_match_mp_tac intLangExtraTheory.all_Clocs_ind >>
  simp[] >> rw[] >>
  TRY (
    simp[Once Cv_bv_cases] >>
    fs[Once Cv_bv_cases] >>
    NO_TAC) >>
  >- (
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >>
    pop_assum mp_tac >>
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >> rw[] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    PairCases_on`pp`>>PairCases_on`pp'`>>fs[]>>
    fs[miscTheory.IMAGE_EQ_SING] >>
    simp[EXISTS_PROD] >>
    metis_tac[MEM_EL])
  >- (
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >>
    pop_assum mp_tac >>
    REWRITE_TAC[Once Cv_bv_cases] >> simp[] >> rw[] >>
    PairCases_on`pp'`>>fs[]>>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP] >>
    rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >> rw[] >>
    first_x_assum (match_mp_tac o MP_CANON) >>
    PairCases_on`pp`>>PairCases_on`pp'`>>fs[]>>
    fs[miscTheory.IMAGE_EQ_SING] >>
    simp[EXISTS_PROD] >>
    metis_tac[MEM_EL])
*)

(*
val result_state = EVAL``let (ct,m,renv,rsz,cs) = bootstrap_result in (rsz,LENGTH m.bvars,m.bvars)``

val ndecs = rand(rator(rhs(concl result_state)))
*)

val HD_new_vs_oneshot_decs = prove(
  ``∃xs. new_decs_vs oneshot_decs = "it"::xs``,
  simp[oneshot_decs_def] >>
  simp[pat_bindings_def])

val FV_decs_oneshot_decs = ``FV_decs oneshot_decs = {Short "input"}``
val decs_cns_oneshot_decs = ``decs_cns NONE oneshot_decs = {}``
val check_dup_ctors_oneshot_decs = ``
(∀i tds.
    i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dtype tds ⇒
        check_dup_ctors NONE (SemanticPrimitives$decs_to_cenv NONE (TAKE i oneshot_decs) ++ init_envC)
              tds)``
val check_dup_exns_oneshot_decs = ``
(∀i cn ts.
     i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dexn cn ts ⇒
     mk_id NONE cn ∉
     set (MAP FST (SemanticPrimitives$decs_to_cenv NONE (TAKE i oneshot_decs) ++ init_envC)))``

val bootstrap_result = ``compile_decs NONE FEMPTY ^ct ^m ^renv ^rsz ^cs oneshot_decs``

val oneshot_thm = store_thm("oneshot_thm",
  ``∀i s cenv env.
      evaluate_decs NONE [] init_envC [] [("input",i)] oneshot_decs (s,cenv,Rval env) ∧
      ^FV_decs_oneshot_decs ∧ ^decs_cns_oneshot_decs ∧ ^check_dup_ctors_oneshot_decs ∧ ^check_dup_exns_oneshot_decs ∧
      closed [] i ∧ all_cns i = {} ∧ all_locs i = {} ∧ ¬(contains_closure i)
      ⇒
      let (ct,m,rsz,cs) = ^bootstrap_result in
      ∀bs bi pp.
        bs.code = REVERSE cs.out
      ∧ bs.pc = 0
      ∧ bs.stack = [bi]
      ∧ bs.clock = NONE
      ∧ Cv_bv pp (v_to_Cv FEMPTY (cmap init_compiler_state.contab) i) bi
      ⇒ ∃bs' Cv bv st rd.
        bc_eval bs = SOME bs'
      ∧ bs'.pc = next_addr bs.inst_length bs.code
      ∧ bs'.stack = bv::st
      ∧ syneq (v_to_Cv FEMPTY (cmap ct) (THE (lookup "it" env))) Cv
      ∧ Cv_bv (mk_pp rd bs') Cv bv``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`init_envC`,`[]`,`[("input",i)]`,`oneshot_decs`,`(s,cenv,Rval env)`]mp_tac compile_decs_thm >>
  simp[] >>
  disch_then(CHOOSE_THEN mp_tac) >>
  disch_then(qspecl_then[`^m`,`^cs`]mp_tac) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))) >>
  disch_then(qspecl_then[`init_compiler_state with <|renv:=[("input",0)];rsz:=1|>`,`0`,`<|sm:=[];cls:=FEMPTY|>`
                        ,`bs with <|clock := SOME ck|>`]mp_tac) >>
  assume_tac(prove(``init_compiler_state.rmenv = FEMPTY``,rw[CompilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.renv = []``,rw[CompilerTheory.init_compiler_state_def])) >>
  simp[] >>
  disch_then(qspecl_then[`[]`,`REVERSE cs.out`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[] >>
    conj_tac >- (
      simp[closed_context_def,closed_under_cenv_def,closed_under_menv_def] ) >>
    conj_tac >- (
      simp[env_rs_def] >>
      assume_tac (GEN_ALL env_rs_empty) >>
      fs[env_rs_def,LET_THM] >>
      pop_assum(qspecl_then[`<|sm:=[];cls:=FEMPTY|>`,`ARB`,`<|stack:=[];clock:=NONE|>`]mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac`env_to_Cenv FEMPTY (cmap init_compiler_state.contab) [("input",i)]` >>
      simp[] >>
      simp[Once pmatchTheory.env_to_Cenv_MAP] >>
      simp[closed_Clocs_def,closed_vlabs_def] >>
      conj_tac >- ( simp[all_Clocs_v_to_Cv] ) >>
      conj_tac >- (
        simp[pmatchTheory.env_to_Cenv_MAP,no_closures_all_vlabs] >>
        simp[intLangExtraTheory.all_vlabs_menv_def,intLangExtraTheory.vlabs_menv_def] >>
        simp[no_closures_vlabs] ) >>
      simp[Cenv_bs_def] >>
      simp[s_refs_def,good_rd_def,finite_mapTheory.FEVERY_DEF] >>
      simp[env_renv_def,CompilerLibTheory.el_check_def,pmatchTheory.env_to_Cenv_MAP] >>
      match_mp_tac (MP_CANON no_closures_no_locs_Cv_bv) >>
      simp[no_closures_v_to_Cv] >>
      simp[all_Clocs_v_to_Cv] >>
      metis_tac[] ) >>
    simp[good_labels_def] ) >>
  strip_tac >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  qmatch_assum_abbrev_tac`RTC bc_next bs1 bs2` >>
  `bc_next^* (bs1 with code := bs.code) (bs2 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs1`,`bs2`] >>
    simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality] ) >>
  qmatch_assum_abbrev_tac`RTC bc_next bs1 bs2` >>
  qexists_tac`bs2` >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >>
    `bs1 = bs` by (
      simp[Abbr`bs1`,bc_state_component_equality] ) >>
    fs[] >>
    `bc_fetch bs2 = NONE` by (
      simp[bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      imp_res_tac RTC_bc_next_preserves >> fs[] >>
      simp[Abbr`bs2`] ) >>
    simp[bc_eval1_thm,bc_eval1_def] ) >>
  conj_tac >- simp[Abbr`bs2`] >>
  rator_x_assum`env_rs`mp_tac >>
  simp[env_rs_def] >> strip_tac >>
  rator_x_assum`Cenv_bs`mp_tac >>
  simp[Cenv_bs_def] >> strip_tac >>
  rator_x_assum`env_renv`mp_tac >>
  simp[env_renv_def] >>
  `rsz = LENGTH m.bvars ∧ 2 ≤ rsz ∧ ∃junk. m.bvars = "it"::junk` by (
    qmatch_assum_abbrev_tac`compile_decs NONE FEMPTY ct0 m0 renv0 rsz0 cs0 ds0 = X` >>
    qspecl_then[`ds0`,`NONE`,`FEMPTY`,`ct0`,`m0`,`renv0`,`rsz0`,`cs0`]mp_tac compile_decs_append_out >>
    simp[Abbr`X`,Abbr`m0`,Abbr`rsz0`,Abbr`renv0`] >> strip_tac >>
    simp[] >>
    simp[Abbr`ds0`] >>
    simp[oneshot_decs_def,pat_bindings_def] >>
    simp[REVERSE_APPEND]) >>
  simp[MAP_ZIP,MAP_GENLIST] >>
  Cases_on`bvs`>>fs[] >>rfs[]>>
  simp[EVERY2_EVERY,miscTheory.option_case_NONE_F] >>
  simp[EVERY_MEM,GSYM AND_IMP_INTRO,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
  strip_tac >>
  disch_then(qspec_then`0`mp_tac) >>
  simp[] >>
  simp[GENLIST_CONS] >>
  simp[CompilerLibTheory.el_check_def] >>
  imp_res_tac evaluate_decs_new_decs_vs >> fs[] >>
  assume_tac HD_new_vs_oneshot_decs >> fs[] >>
  Cases_on`env`>>fs[] >>
  simp[REVERSE_APPEND,EL_APPEND1,EL_APPEND2,ADD1] >>
  qmatch_assum_rename_tac`FST p = "it"`[]>>
  PairCases_on`p` >> fs[] >>
  fs[pmatchTheory.env_to_Cenv_MAP] >>
  strip_tac >>
  simp[Abbr`bs2`] >>
  HINT_EXISTS_TAC >>
  simp[] >>
  qexists_tac`rd'` >>
  simp[] >>fs[Abbr`bs1`])

val (Eval_peic,side_def) = get_cert"parse_elaborate_infertype_compile"

val Eval =
  Eval_peic
  |>DISCH_ALL
  |>SIMP_RULE std_ss [PRECONDITION_def,parse_elaborate_infertype_compile_side_thm]
  |>UNDISCH_ALL
  |>Q.GENL[`v12`,`v13`]
  |>SIMP_RULE std_ss[Eval_FUN_FORALL_EQ]
  |>SIMP_RULE std_ss[FUN_QUANT_SIMP]

val lemma1 =
  bootstrap_lemma1
  |> DISCH_ALL
  |> REWRITE_RULE[AND_IMP_INTRO]
  |> ONCE_REWRITE_RULE[CONJ_COMM]
  |> ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]

val lemma2 =
  Eval
  |> DISCH``DeclAssum ml_repl_step_decls env``
  |> Q.GEN`env`

val lemma3 =
MATCH_MP lemma1 lemma2
|> DISCH_ALL
|> SIMP_RULE std_ss [PRECONDITION_def,parse_elaborate_infertype_compile_side_thm,empty_store_def,Once Eq_def]
|> funpow 4 UNDISCH

val oneshot_def' = oneshot_decs_def |> REWRITE_RULE[GSYM SNOC_APPEND]

(*
val bootstrap_thm_lemma = prove(
``^(list_mk_conj (hyp lemma3)) ∧
  eval_ctor_inv [] [] [("input",i)] ∧
  check_ctors_decs NONE [] oneshot_decs ∧
  Decls NONE [] [] [] [] ml_repl_step_decls cenv2 s2 env2 ∧
  Decls NONE [] [] [] [("input",i)] ml_repl_step_decls cenv2 s2 env2 ∧
  lookup "input" env2 = NONE ∧ LIST_TYPE TOKEN_TYPE input i ⇒
  ∃env cenv s v.
   (lookup "it" env = SOME v ∧
      (REPL_FUN_STATE_TYPE -->
       EXC_TYPE
         (PAIR_TYPE (LIST_TYPE BC_INST_TYPE)
            (PAIR_TYPE REPL_FUN_STATE_TYPE REPL_FUN_STATE_TYPE))
         (LIST_TYPE CHAR)) (parse_elaborate_infertype_compile input)
        v) ∧
     evaluate_decs NONE [] [] [] [("input",i)] oneshot_decs (s,cenv,Rval env) ∧
     FV_decs oneshot_decs = {Short "input"} ∧
     decs_cns NONE oneshot_decs = ∅ ∧
     (∀i tds.
        i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dtype tds ⇒
        check_dup_ctors NONE (decs_to_cenv NONE (TAKE i oneshot_decs))
          tds) ∧ closed [] i ∧ all_cns i = ∅ ∧ all_locs i = ∅ ∧
     ¬contains_closure i ⇒
     (let (ct,m,renv,rsz,cs) = bootstrap_result
      in
        ∀bs bi pp.
          bs.code = REVERSE cs.out ∧ bs.pc = 0 ∧ bs.stack = [bi] ∧
          bs.clock = NONE ∧
          Cv_bv pp (v_to_Cv FEMPTY (cmap init_compiler_state.contab) i)
            bi ⇒
          ∃bs' Cv bv st rd.
            bc_eval bs = SOME bs' ∧
            bs'.pc = next_addr bs.inst_length bs.code ∧
            bs'.stack = bv::st ∧
            syneq (v_to_Cv FEMPTY (cmap ct) (THE (lookup "it" env)))
              Cv ∧ Cv_bv (mk_pp rd bs') Cv bv)``,
  rpt strip_tac >>
  mp_tac (Q.INST[`env`|->`env2`]lemma3)  >>
  rw[] >>
  `evaluate_decs NONE [] [] [] [("input",i)] oneshot_decs (s2',cenv2',Rval env')` by (
    fs[GSYM oneshot_def'] >>
    metis_tac[bootstrap_lemma2,result_distinct] ) >>
  map_every qexists_tac[`env'`,`cenv2'`,`s2'`,`v`] >>
  rw[] >>
  imp_res_tac oneshot_thm >>
  fs[LET_THM] >>
  Cases_on`bootstrap_result` >>
  PairCases_on`r` >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rfs[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[])
*)

val bootstrap_thm_lemma = prove(
``^(list_mk_conj (hyp lemma3)) ∧
  eval_ctor_inv [] [] [("input",i)] ∧
  check_ctors_decs NONE [] oneshot_decs ∧
  Decls NONE [] [] [] [] ml_repl_step_decls cenv2 s2 env2 ∧
  Decls NONE [] [] [] [("input",i)] ml_repl_step_decls cenv2 s2 env2 ∧
  lookup "input" env2 = NONE ∧ LIST_TYPE TOKEN_TYPE input i ⇒
  ∃env cenv s v.
   (lookup "it" env = SOME v ∧
      (REPL_FUN_STATE_TYPE -->
       EXC_TYPE
         (PAIR_TYPE (LIST_TYPE BC_INST_TYPE)
            (PAIR_TYPE REPL_FUN_STATE_TYPE REPL_FUN_STATE_TYPE))
         (LIST_TYPE CHAR)) (parse_elaborate_infertype_compile input)
        v) ∧
     evaluate_decs NONE [] init_envC [] [("input",i)] oneshot_decs (s,cenv,Rval env) ∧
   (
     FV_decs oneshot_decs = {Short "input"} ∧
     decs_cns NONE oneshot_decs = ∅ ∧
     (∀i tds.
        i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dtype tds ⇒
        check_dup_ctors NONE (decs_to_cenv NONE (TAKE i oneshot_decs))
          tds) ∧ closed [] i ∧ all_cns i = ∅ ∧ all_locs i = ∅ ∧
     ¬contains_closure i ⇒
     (let (ct,m,rsz,cs) = ^bootstrap_result
      in
        ∀bs bi pp.
          bs.code = REVERSE cs.out ∧ bs.pc = 0 ∧ bs.stack = [bi] ∧
          bs.clock = NONE ∧
          Cv_bv pp (v_to_Cv FEMPTY (cmap init_compiler_state.contab) i)
            bi ⇒
          ∃bs' Cv bv st rd.
            bc_eval bs = SOME bs' ∧
            bs'.pc = next_addr bs.inst_length bs.code ∧
            bs'.stack = bv::st ∧
            syneq (v_to_Cv FEMPTY (cmap ct) (THE (lookup "it" env)))
              Cv ∧ Cv_bv (mk_pp rd bs') Cv bv))``,
  rpt strip_tac >>
  mp_tac (Q.INST[`env`|->`env2`]lemma3)  >>
  rw[] >>
  `evaluate_decs NONE [] [] [] [("input",i)] oneshot_decs (s2',cenv2',Rval env')` by (
    fs[GSYM oneshot_def'] >>
    metis_tac[bootstrap_lemma2,result_distinct] ) >>
  map_every qexists_tac[`env'`,`cenv2'`,`s2'`,`v`] >>
  rw[] >>
  imp_res_tac oneshot_thm >>
  fs[LET_THM] >>
  qmatch_assum_abbrev_tac`X Y` >>
  Cases_on`Y` >>
  PairCases_on`r` >> fs[markerTheory.Abbrev_def] >>
  pop_assum(assume_tac o SYM)>>fs[]>>
  rpt BasicProvers.VAR_EQ_TAC >>
  rfs[] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  metis_tac[])

val bootstrap_lemma6 =
  bootstrap_thm_lemma
|> SIMP_RULE std_ss [METIS_PROVE[]``(Q ==> (?x. P x)) ⇔ ?x. Q ==> P x``]
|> SIMP_RULE (srw_ss()) [bigBigEquivTheory.eval_ctor_inv_def]
|> SIMP_RULE std_ss [AND_IMP_INTRO]

val bootstrap_thm = store_thm("bootstrap_thm",
``
(* These hypotheses the translator should prove automatically *)
 EqualityType EXP_TYPE ∧
 EqualityType (PARSETREE_TYPE TOKEN_TYPE MMLNONT_TYPE) ∧
 EqualityType PAT_TYPE ∧ EqualityType T_TYPE ∧
(* These hypotheses are true by evaluation, but it takes a long time to evaluate in the logic *)
 check_ctors_decs NONE [] oneshot_decs ∧
 Decls NONE [] [] [] [] ml_repl_step_decls cenv2 s2 env2 ∧
 Decls NONE [] [] [] [("input",i)] ml_repl_step_decls cenv2 s2 env2 ∧
 ALOOKUP env2 "input" = NONE ∧
 FV_decs oneshot_decs = {Short "input"} ∧
 decs_cns NONE oneshot_decs = ∅ ∧
 (∀i tds.
   i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dtype tds ⇒
   check_dup_ctors NONE (decs_to_cenv NONE (TAKE i oneshot_decs)) tds)

 ⇒

∃env cenv s v.

(* these are conditions on the input to the compiler: it must be a list of tokens *)
check_ctors_v [] i ∧ LIST_TYPE TOKEN_TYPE input i ∧
closed [] i ∧ all_cns i = ∅ ∧ all_locs i = ∅ ∧ ¬contains_closure i

 ⇒

(* the conclusion follows: *)

     (ALOOKUP env "it" = SOME v ∧
      (REPL_FUN_STATE_TYPE -->
       EXC_TYPE
         (PAIR_TYPE (LIST_TYPE BC_INST_TYPE)
            (PAIR_TYPE REPL_FUN_STATE_TYPE REPL_FUN_STATE_TYPE))
         (LIST_TYPE CHAR)) (parse_elaborate_infertype_compile input)
        v) ∧

     evaluate_decs NONE [] [] [] [("input",i)] oneshot_decs (s,cenv,Rval env) ∧

      (let (ct,m,rsz,cs) = ^bootstrap_result
       in
         ∀bs bi pp.
           ∃bs' Cv bv st rd.
             bs.code = REVERSE cs.out ∧ bs.pc = 0 ∧ bs.stack = [bi] ∧
             bs.clock = NONE ∧
             Cv_bv pp
               (v_to_Cv FEMPTY (cmap init_compiler_state.contab) i) bi ⇒
             bc_eval bs = SOME bs' ∧
             bs'.pc = next_addr bs.inst_length (REVERSE cs.out) ∧
             bs'.stack = bv::st ∧
             syneq (v_to_Cv FEMPTY (cmap ct) (THE (ALOOKUP env "it")))
               Cv ∧ Cv_bv (mk_pp rd bs') Cv bv)``,
metis_tac[bootstrap_lemma6])


val _ = export_theory()
