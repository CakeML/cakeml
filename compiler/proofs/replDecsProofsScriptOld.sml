open HolKernel bossLib boolLib boolSimps lcsymtacs miscLib arithmeticTheory listTheory rich_listTheory
open bytecodeTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeTerminationTheory compilerTerminationTheory semanticsExtraTheory toIntLangProofsTheory toBytecodeProofsTheory compilerProofsTheory bigClockTheory
val _ = new_theory"replDecsProofs"

val ct = ``init_compiler_state.contab``
val m = ``<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap(^ct)|>``
val cs = ``<|out:=[];next_label:=init_compiler_state.rnext_label|>``
val renv = ``[]:ctenv``
val rsz = ``0:num``

val FV_decs_repl_decs = ``FV_decs repl_decs = {}``
val decs_cns_repl_decs = ``decs_cns NONE repl_decs = {}``
val check_dup_ctors_repl_decs = ``
(∀i tds.
    i < LENGTH repl_decs ∧ EL i repl_decs = Dtype tds ⇒
        check_dup_ctors NONE (decs_to_cenv NONE (TAKE i repl_decs) ++ init_envC)
              tds)``
val check_dup_exns_repl_decs = ``
(∀i cn ts.
    i < LENGTH repl_decs ∧ EL i repl_decs = Dexn cn ts ⇒
        mk_id NONE cn ∉ set (MAP FST (decs_to_cenv NONE (TAKE i repl_decs) ++ init_envC)))``

val bootstrap_result = ``compile_decs NONE FEMPTY ^ct ^m ^renv ^rsz ^cs repl_decs``

val compile_repl_decs_thm = store_thm("compile_repl_decs_thm",
  ``∀s cenv env.
      evaluate_decs NONE [] init_envC [] [] repl_decs (s,cenv,Rval env) ∧
      ^FV_decs_repl_decs ∧ ^decs_cns_repl_decs ∧ ^check_dup_ctors_repl_decs ∧ ^check_dup_exns_repl_decs
      ⇒
      let (ct,m,rsz,cs) = ^bootstrap_result in
      ∀bs.
        bs.code = REVERSE cs.out
      ∧ bs.pc = 0
      ∧ bs.stack = []
      ∧ bs.clock = NONE
      ⇒ ∃bs' rd.
        let rs = init_compiler_state with
          <|contab := ct
           ;renv := ZIP(m.bvars,REVERSE(GENLIST I rsz))
           ;rsz := rsz
           ;rnext_label := cs.next_label
           |> in
        bc_eval bs = SOME bs'
      ∧ bs'.pc = next_addr bs.inst_length bs.code
      ∧ env_rs [] (cenv++init_envC) (0,s) env rs 0 rd bs'
      ∧ good_labels rs.rnext_label bs.code``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`init_envC`,`[]`,`[]`,`repl_decs`,`(s,cenv,Rval env)`]mp_tac compile_decs_thm >>
  simp[] >>
  disch_then(CHOOSE_THEN mp_tac) >>
  disch_then(qspecl_then[`^m`,`^cs`]mp_tac) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))) >>
  disch_then(qspecl_then[`init_compiler_state`,`0`,`<|sm:=[];cls:=FEMPTY|>`
                        ,`bs with <|clock := SOME ck|>`]mp_tac) >>
  assume_tac(prove(``init_compiler_state.rmenv = FEMPTY``,rw[compilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.renv = []``,rw[compilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.rsz = 0``,rw[compilerTheory.init_compiler_state_def])) >>
  simp[] >>
  disch_then(qspecl_then[`[]`,`REVERSE cs.out`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    conj_tac >- metis_tac[] >>
    conj_tac >- (
      simp[closed_context_def,closed_under_cenv_def,closed_under_menv_def] ) >>
    conj_tac >- (
      match_mp_tac env_rs_empty >> simp[]) >>
    simp[good_labels_def] ) >>
  strip_tac >>
  simp[markerTheory.Abbrev_def] >>
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
  qmatch_assum_abbrev_tac`env_rs [] cenv2 (0,s) env rs 0 rd' bs'` >>
  Q.PAT_ABBREV_TAC`rs':compiler_state = X` >>
  qmatch_assum_abbrev_tac`compile_decs rmn rmenv rct rm renv msz rcs rdecs = rX` >>
  qspecl_then[`rdecs`,`rmn`,`rmenv`,`rct`,`rm`,`renv`,`msz`,`rcs`]mp_tac compile_decs_append_out >>
  simp[Abbr`rX`,Abbr`rm`,Abbr`msz`,Abbr`renv`,Abbr`rcs`,Abbr`rs`] >> strip_tac >>
  qmatch_assum_abbrev_tac`env_rs [] cenv2 (0,s) env rs 0 rd' bs'` >>
  `rs' = rs` by (
    simp[Abbr`rs`,Abbr`rs'`,compilerTheory.compiler_state_component_equality] >>
    simp[REVERSE_GENLIST,PRE_SUB1] ) >>
  qexists_tac`rd'` >>
  conj_tac >- (
    match_mp_tac env_rs_remove_clock >>
    qexists_tac`0,s` >> simp[] >>
    qexists_tac`bs'` >> simp[]) >>
  fs[good_labels_def,between_labels_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,miscTheory.between_def,MEM_MAP])

val compile_call_repl_step_thm = store_thm("compile_call_repl_step_thm",
  ``∀mn cenv ck s env s' fn n cs rs csz rd bs bc0.
      evaluate_dec mn [] cenv s env (Dlet (Plit Unit) (App Opapp (Var(Short fn)) (Lit Unit))) (s',Rval([],[]))
      ∧ find_index fn (MAP FST env) 0 = SOME n
      ∧ compile FEMPTY (MAP (CTDec o SND) rs.renv) TCNonTail rs.rsz <|out:=[];next_label:=rs.rnext_label|>
          (CCall T (CVar(Short n)) [CLit Unit]) = cs
      ∧ closed_context [] cenv s env
      ∧ env_rs [] cenv (ck,s) env rs csz rd bs
      ∧ good_labels rs.rnext_label bs.code
      ∧ bs.code = bc0 ++ REVERSE cs.out ++ [Stack Pop]
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ bs.clock = NONE
      ⇒
      ∃bs' rd'.
      bc_eval bs = SOME bs'
      ∧ bs'.pc = next_addr bs.inst_length bs.code
      ∧ bs'.output = bs.output
      ∧ env_rs [] cenv (ck,s') env rs csz rd' bs'``,
   rw[bigStepTheory.evaluate_dec_cases] >>
   imp_res_tac big_unclocked >> rw[] >>
   fs[big_clocked_unclocked_equiv] >>
   `env_rs [] cenv (count',s) env rs csz rd bs` by (
     fs[LET_THM,env_rs_def] >>
     qpat_assum`FEMPTY = X`(assume_tac o SYM) >> fs[] >>
     Q.LIST_EXISTS_TAC[`Cenv`,`Cs`] >>
     fs[Cenv_bs_def] >>
     rfs[s_refs_def] >> fs[] ) >>
   qpat_assum`env_rs [] cenv (ck,s) env rs csz rd bs`kall_tac >>
   qmatch_assum_abbrev_tac`evaluate T [] cenv cs env e res` >>
   qspecl_then[`T`,`[]`,`cenv`,`cs`,`env`,`e`,`res`] mp_tac (CONJUNCT1 exp_to_Cexp_thm1) >>
   simp[] >>
   discharge_hyps >- (
     simp[Abbr`e`] >>
     fs[closed_context_def] >>
     fs[env_rs_def,Abbr`cs`,Abbr`res`] >>
     `find_index fn (MAP FST env) 0 ≠ NONE` by fs[] >>
     fs[GSYM miscTheory.find_index_NOT_MEM] >>
     fs[MEM_MAP] >> metis_tac[] ) >>
   disch_then(qspec_then`cmap rs.contab`mp_tac) >>
   discharge_hyps >- fs[env_rs_def] >>
   simp[pairTheory.EXISTS_PROD,Abbr`res`] >>
   Cases_on`v`>>fs[terminationTheory.pmatch_def] >>
   qpat_assum`X = Match []`mp_tac >>
   rw[] >> fs[v_to_Cv_def,libTheory.emp_def] >> rw[] >>
   rfs[Abbr`e`,exp_to_Cexp_def,LET_THM] >>
   qmatch_assum_abbrev_tac`Cevaluate FEMPTY Cs0 Cenv0 exp Cres0` >>
   qpat_assum`bs.code = X`(assume_tac o SYM) >>
   `∃Cenv Cs.
     LIST_REL syneq (SND Cs0) Cs ∧
     LIST_REL syneq Cenv0 Cenv ∧
     EVERY all_vlabs Cs ∧
     EVERY all_vlabs Cenv ∧
     BIGUNION (IMAGE all_Clocs (set Cenv)) ⊆ count (LENGTH Cs) ∧
     BIGUNION (IMAGE all_Clocs (set Cs)) ⊆ count (LENGTH Cs) ∧
     (∀cd. cd ∈ vlabs_list Cs ⇒ code_env_cd FEMPTY bs.code cd) ∧
     (∀cd. cd ∈ vlabs_list Cenv ⇒ code_env_cd FEMPTY bs.code cd) ∧
     Cenv_bs rd FEMPTY (count',Cs) Cenv FEMPTY (MAP (CTDec o SND) rs.renv) rs.rsz csz (bs with clock := SOME count')` by (
     fs[env_rs_def,LET_THM,Abbr`Cs0`,Abbr`cs`] >>
     qexists_tac`Cenv`>>simp[] >>
     qpat_assum`FEMPTY  = X `(assume_tac o SYM) >>
     qexists_tac`Cs`>>fs[] >>
     `FDOM (MAP FST o_f rs.rmenv) = {}` by (
       pop_assum SUBST1_TAC >> simp[] ) >>
     fs[] >>
     fs[finite_mapTheory.FDOM_EQ_EMPTY] >>
     rfs[] >>
     rfs[Cenv_bs_def,s_refs_def,good_rd_def,env_renv_def] >>
     fs[intLangExtraTheory.closed_vlabs_def] >>
     fs[intLangExtraTheory.closed_Clocs_def]) >>
   `∃Cs'. Cevaluate FEMPTY (FST cs,Cs) Cenv exp ((0,Cs'),SND Cres0) ∧
          LIST_REL syneq (SND(FST Cres0)) Cs'` by (
     qspecl_then[`FEMPTY`,`Cs0`,`Cenv0`,`exp`,`Cres0`]mp_tac(CONJUNCT1 intLangExtraTheory.Cevaluate_syneq) >>
     simp[] >>
     disch_then(qspecl_then[`$=`,`(FST cs,Cs)`,`Cenv`,`exp`]mp_tac) >>
     fs[EVERY2_EVERY] >>
     simp[intLangExtraTheory.syneq_exp_refl,Abbr`Cs0`] >>
     rfs[EVERY_MEM,MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
     simp[Abbr`Cres0`,pairTheory.FORALL_PROD] >>
     metis_tac[] ) >>
   qmatch_assum_abbrev_tac`Cevaluate FEMPTY Css Cenv exp Cres` >>
   qspecl_then[`FEMPTY`,`Css`,`Cenv`,`exp`,`Cres`]mp_tac(CONJUNCT1 compile_val) >>
   simp[Abbr`Cres`,Abbr`Cres0`] >>
   qabbrev_tac`cst = <|out := []; next_label := rs.rnext_label|>` >>
   disch_then(qspecl_then[`rd`,`FEMPTY`,`cst`,`MAP (CTDec o SND) rs.renv`,`rs.rsz`,`csz`,`bs with clock := SOME count'`,`bs.code`,`[]`,`bc0`]mp_tac) >>
   qmatch_assum_abbrev_tac`bc0 ++ code ++ [Stack Pop] = bs.code` >>
   disch_then(qspecl_then[`code`,`[Stack Pop]`]mp_tac) >>
   simp[Abbr`Css`,Abbr`cs`,Abbr`cst`,Abbr`code`] >>
   discharge_hyps >- (
     `free_labs (LENGTH Cenv) exp = [] ∧ all_labs exp ∧ free_vars exp = [n]` by (
       simp[Abbr`exp`,compilerLibTheory.lunion_def] ) >>
     simp[intLangExtraTheory.all_vlabs_menv_def,intLangExtraTheory.vlabs_menv_def] >>
     fs[good_labels_def] >>
     imp_res_tac miscTheory.find_index_LESS_LENGTH >>
     `LENGTH rs.renv = LENGTH env` by fs[env_rs_def,LET_THM,LIST_EQ_REWRITE] >>
     fs[] >>
     Q.PAT_ABBREV_TAC`bs1:bc_state = bc_state_fupd_code X Y` >>
     `bs1 = bs with clock := SOME count'` by (
       simp[Abbr`bs1`,bc_state_component_equality] ) >>
     pop_assum SUBST1_TAC >>
     simp[] >>
     qpat_assum`X = bs.code`(assume_tac o SYM) >>
     fs[FILTER_APPEND,ALL_DISTINCT_APPEND] ) >>
   disch_then (mp_tac o CONJUNCT1) >>
   simp[code_for_push_def] >>
   simp_tac(srw_ss()++DNF_ss)[] >>
   simp[Once Cv_bv_cases] >>
   qx_genl_tac[`rf`,`rd'`,`ck'`] >>
   strip_tac >>
   qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
   `bc_next bs1 (bs1 with <| pc := next_addr bs.inst_length bs.code; stack := TL bs1.stack |>)` by (
     `bc_fetch bs1 = SOME(Stack Pop)` by (
       simp[Abbr`bs1`] >>
       match_mp_tac bc_fetch_next_addr >>
       simp[] >>
       Q.PAT_ABBREV_TAC`ls = bc0 ++ X` >>
       qexists_tac`ls` >>
       simp[] ) >>
     simp[Once bc_next_cases,bump_pc_def] >>
     simp[Abbr`bs1`,bc_state_component_equality,Once bc_stack_op_cases] >>
     qpat_assum`X = bs.code`(assume_tac o SYM) >>
     simp[SUM_APPEND,FILTER_APPEND,SUM_REVERSE,FILTER_REVERSE] ) >>
   qmatch_assum_abbrev_tac`bc_next bs1 bs2` >>
   `bc_next^* bs0 bs2` by metis_tac[relationTheory.RTC_CASES2] >>
   qexists_tac`bs2 with clock := NONE` >>
   simp[Abbr`bs2`] >>
   qexists_tac`rd'` >>
   conj_tac >- (
     imp_res_tac RTC_bc_next_bc_eval >>
     match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >>
     reverse conj_tac >- (
       Q.PAT_ABBREV_TAC`bs2:bc_state = X` >>
       `bc_fetch bs2 = NONE` by (
         simp[bc_fetch_def,Abbr`bs2`] >>
         match_mp_tac bc_fetch_aux_end_NONE >>
         simp[] ) >>
       simp[Once bc_next_cases,Abbr`bs1`] ) >>
     imp_res_tac RTC_bc_next_can_be_unclocked >>
     fs[Abbr`bs0`] >>
     `bs = bs with clock := NONE` by simp[bc_state_component_equality] >>
     metis_tac[] ) >>
   fs[env_rs_def,LET_THM,Abbr`bs1`] >>
   Q.LIST_EXISTS_TAC[`Cenv`,`Cs'`] >>
   conj_tac >- (
     match_mp_tac intLangExtraTheory.EVERY2_syneq_trans >>
     metis_tac[] ) >>
   `rs.rmenv = FEMPTY` by (
     simp[GSYM finite_mapTheory.FDOM_EQ_EMPTY] >>
     fs[GSYM finite_mapTheory.fmap_EQ_THM] ) >>
   qpat_assum`FEMPTY = X`(assume_tac o SYM) >>
   simp[] >>
   qmatch_assum_abbrev_tac`Cevaluate menv xs xenv exp ((0,Cs'),res)` >>
   qspecl_then[`menv`,`xs`,`xenv`,`exp`,`((0,Cs'),res)`]mp_tac intLangExtraTheory.Cevaluate_closed_Clocs >>
   qspecl_then[`menv`,`xs`,`xenv`,`exp`,`((0,Cs'),res)`]mp_tac intLangExtraTheory.Cevaluate_closed_vlabs >>
   simp[Abbr`res`,Abbr`xs`,Abbr`exp`,Abbr`xenv`,Abbr`menv`] >>
   strip_tac >> strip_tac >>
   conj_tac >- (
     first_x_assum match_mp_tac >>
     simp[intLangExtraTheory.closed_Clocs_def] ) >>
   conj_tac >- (
     first_x_assum match_mp_tac >>
     simp[intLangExtraTheory.closed_vlabs_def,intLangExtraTheory.all_vlabs_menv_def,intLangExtraTheory.vlabs_menv_def] ) >>
   Q.PAT_ABBREV_TAC`bs2:bc_state = X Y` >>
   match_mp_tac Cenv_bs_change_store >>
   Q.LIST_EXISTS_TAC[`rd'`,`0,Cs'`,`bs2 with clock := ck'`,`bs2.refs`,`bs2.clock`] >>
   simp[bc_state_component_equality] >>
   conj_asm1_tac >- (
     match_mp_tac Cenv_bs_pops >>
     Q.LIST_EXISTS_TAC[`[Block 2 []]`,`bs2 with <|stack := (Block 2 [])::bs.stack; clock := ck'|>`] >>
     simp[bc_state_component_equality,Abbr`bs2`] >>
     rfs[] >>
     conj_tac >- (
       match_mp_tac Cenv_bs_with_irr >>
       HINT_EXISTS_TAC >>
       simp[] ) >>
     simp[MEM_MAP] >>
     fs[Cenv_bs_def,env_renv_def] >>
     fs[EVERY2_EVERY,EVERY_MEM] >>
     rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM] >>
     simp[MEM_EL, GSYM LEFT_FORALL_IMP_THM] >>
     rw[] >> res_tac >>
     fs[] >> rfs[EL_MAP] >>
     res_tac >> fs[compilerLibTheory.el_check_def] >>
     spose_not_then strip_assume_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   fs[Cenv_bs_def,s_refs_def,Abbr`bs2`,good_rd_def])

(*
val FV_dec_call_repl_step_dec = ``FV_dec call_repl_step_dec = {Short"call_repl_step"}``
val dec_cns_call_repl_step_dec = ``dec_cns call_repl_step_dec = {}``

val compile_call_repl_step_thm = store_thm("compile_call_repl_step_thm",
  ``∀mn cenv s env s' rs csz rd ck cs bs.
    evaluate_dec mn [] cenv s env call_repl_step_dec (s',Rval([],[]))
    ∧ ^FV_dec_call_repl_step_dec
    ∧ ^dec_cns_call_repl_step_dec
    ∧ MEM "call_repl_step" (MAP FST env)
    ∧ compile_dec FEMPTY <|bvars := MAP FST env; mvars := FEMPTY; cnmap := cmap rs.contab|> (MAP (CTDec o SND) rs.renv) rs.rsz <|out:=[];next_label:=rs.rnext_label|> call_repl_step_dec = (SOME [],cs)
    ∧ closed_context [] cenv s env
    ∧ env_rs [] cenv (ck,s) env rs csz rd bs
    ∧ good_labels rs.rnext_label bs.code (* TODO: add this to env_rs? *)
    ∧ bs.clock = NONE
    ⇒
    ∃bs' rd'.
    bc_eval (bs with <|code := bs.code ++ REVERSE (Stack Pop::cs.out); pc := next_addr bs.inst_length bs.code|>) = SOME bs'
    ∧ bs'.pc = next_addr bs.inst_length (bs.code ++ REVERSE (Stack Pop::cs.out))
    ∧ bs'.output = bs.output
    ∧ env_rs [] cenv (ck,s') env rs csz rd' bs'``,
  rw[] >>
  qspecl_then[`mn`,`[]`,`cenv`,`s`,`env`,`call_repl_step_dec`,`s',Rval([],[])`]mp_tac compile_dec_thm >>
  simp[] >>
  disch_then(CHOOSE_THEN mp_tac) >>
  qmatch_assum_abbrev_tac`compile_dec FEMPTY m renv rsz cs0 d = (SOME [],cs)` >>
  Q.PAT_ABBREV_TAC`bs1 = bc_state_code_fupd (K (x++z)) y` >>
  `rs.rmenv = FEMPTY` by (
    fs[env_rs_def,LET_THM] >>
    fs[GSYM finite_mapTheory.fmap_EQ_THM] >>
    qpat_assum`{} = X`(assume_tac o SYM)>>simp[] ) >>
  disch_then(qspecl_then[`m`,`cs0`,`SOME []`,`cs`,`rs`,`rd`,`bs1 with <| code := bs.code ++ REVERSE cs.out; clock := SOME ck'|>`]mp_tac) >> simp[] >>
  disch_then(qspecl_then[`bs.code`,`REVERSE cs.out`,`csz`]mp_tac) >> simp[] >>
  discharge_hyps >- (
    simp[Abbr`d`,Abbr`m`,Abbr`cs0`,Abbr`bs1`] >>
    conj_tac >- (
      fs[MEM_MAP,pairTheory.EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    match_mp_tac env_rs_with_bs_irr >>
    qexists_tac`bs with clock := SOME ck'` >> simp[] >>
    match_mp_tac env_rs_change_clock >> simp[] >>
    qexists_tac`ck,s`>>simp[] >>
    qexists_tac`bs` >> simp[] ) >>
  simp[pmatchTheory.vs_to_Cvs_MAP] >>
  disch_then(qx_choosel_then[`rf`,`rd'`,`Cs'`]strip_assume_tac) >>
  qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
  `bc_next^* (bs2 with code := bs1.code) (bs3 with code := bs1.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    map_every qexists_tac[`bs2`,`bs3`] >>
    simp[Abbr`bs2`,Abbr`bs3`,bc_state_component_equality,Abbr`bs1`] ) >>
  qpat_assum`bc_next^* bs2 bs3`kall_tac >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  pop_assum mp_tac >> pop_assum kall_tac >> strip_tac >>
  map_every qunabbrev_tac[`bs2`,`bs3`] >>
  qmatch_assum_abbrev_tac`bc_next^* bs2 bs3` >>
  `bc_fetch bs3 = SOME(Stack Pop)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`BUTLAST bs3.code` >>
    simp[Abbr`bs3`,Abbr`bs1`,FRONT_APPEND] ) >>
  Q.PAT_ABBREV_TAC`pc = next_addr x y` >>
  `bc_next bs3 (bs3 with <|stack:=bs.stack;pc:=pc|>)` by (
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def,bc_eval_stack_def,Abbr`bs3`] >>
    simp[bc_state_component_equality,Abbr`bs1`,Abbr`pc`] >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  qmatch_assum_abbrev_tac`bc_next bs3 bs4` >>
  qexists_tac`bs4` >>
  qexists_tac`rd'` >>
  conj_tac >- (
    match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >>
    `bs2 = bs1` by (
      simp[Abbr`bs2`,Abbr`bs1`,bc_state_component_equality] ) >>
    conj_tac >- metis_tac[relationTheory.RTC_TRANSITIVE,relationTheory.transitive_def,relationTheory.RTC_SUBSET] >>
    simp[bc_eval1_thm] >>
    `bc_fetch bs4 = NONE` by (
      simp[bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      simp[Abbr`bs4`,Abbr`pc`,Abbr`bs3`,Abbr`bs1`] ) >>
    simp[bc_eval1_def] ) >>
  simp[CONJ_ASSOC] >>
  conj_tac >- simp[Abbr`bs4`,Abbr`bs3`,Abbr`bs1`] >>
  match_mp_tac env_rs_change_store >>
  map_every qexists_tac[`rd`,`ck,s`,`bs1 with pc := bs4.pc`] >>
  simp[bc_state_component_equality,Abbr`bs4`,Abbr`bs3`] >>
  qexists_tac`Cs'` >>
  simp[Abbr`bs1`,pmatchTheory.vs_to_Cvs_MAP] >>
  `ALL_DISTINCT (FILTER is_Label (bs.code ++ REVERSE cs.out))` by (
    qspecl_then[`FEMPTY`,`m`,`renv`,`rsz`,`cs0`,`d`]mp_tac compile_dec_append_out >>
    simp[Abbr`renv`,Abbr`m`,Abbr`d`] >>
    discharge_hyps >- fs[env_rs_def,LET_THM,LIST_EQ_REWRITE] >> strip_tac >>
    fs[good_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_APPEND,Abbr`cs0`,between_labels_def] >>
    fsrw_tac[DNF_ss][EVERY_MEM,miscTheory.between_def,MEM_MAP,MEM_FILTER,is_Label_rwt] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    match_mp_tac env_rs_append_code >>
    qexists_tac`bs with pc := pc` >>
    simp[bc_state_component_equality] >>
    conj_tac >- (
      match_mp_tac env_rs_with_bs_irr >>
      HINT_EXISTS_TAC >> simp[] ) >>
    fs[FILTER_APPEND] ) >>
  conj_tac >- (
    fs[] >>
    ntac 5 (pop_assum kall_tac) >>
    qmatch_assum_abbrev_tac`s_refs rd' (0,Cs') bs0` >>
    qmatch_abbrev_tac`s_refs rd' (ck,Cs') bs1` >>
    match_mp_tac s_refs_append_code >>
    qexists_tac`bs1 with code := bs0.code` >>
    simp[bc_state_component_equality,Abbr`bs1`,Abbr`bs0`] >>
    fs[s_refs_def,good_rd_def] ) >>
  rw[] >>
  match_mp_tac code_env_cd_append >>
  simp[] >>
  fs[FILTER_APPEND])

val EVERY2_APPEND_IMP = store_thm("EVERY2_APPEND_IMP",
  ``∀R l1 l2 l3. LIST_REL R (l1 ++ l2) l3 ⇔ ∃l4 l5. l3 = l4 ++ l5 ∧ LENGTH l4 = LENGTH l1 ∧ LENGTH l5 = LENGTH l2 ∧ EVERY2 R l1 l4 ∧ EVERY2 R l2 l5``,
  rw[EQ_IMP_THM] >- (
    qexists_tac`TAKE (LENGTH l1) l3` >>
    qexists_tac`DROP (LENGTH l1) l3` >>
    simp[TAKE_DROP] >>
    imp_res_tac EVERY2_LENGTH >> fs[] >>
    simp[LENGTH_TAKE] >>
    simp[miscTheory.EVERY2_APPEND] ) >>
  simp[miscTheory.EVERY2_APPEND_suff])
*)

(*
val env_rs_remove_call_code = store_thm("env_rs_remove_call_code",
  ``∀cenv ck s env rs csz rd bs s' rd' bs' rest.
     env_rs [] cenv (ck,s) env rs csz rd bs ∧
     bs'.code = bs.code ++ rest ∧
     ¬EXISTS contains_closure s' ∧
     env_rs [] cenv (ck,s') env rs csz rd' bs'
     ⇒
     env_rs [] cenv (ck,s') env rs csz rd' (bs' with code := bs.code)``,
   rw[env_rs_def,LET_THM] >>
   qpat_assum`FEMPTY = X`(assume_tac o SYM) >> fs[] >>
   rpt HINT_EXISTS_TAC >> simp[] >>
   conj_tac >- (
     fs[intLangExtraTheory.closed_vlabs_def] >>
     fs[intLangExtraTheory.vlabs_list_MAP,GSYM LEFT_FORALL_IMP_THM] >>
     conj_tac >- (
       rw[] >>
       qmatch_assum_abbrev_tac`LIST_REL syneq (MAP f s') Cs'` >>
       fs[EVERY2_EVERY,EVERY_MEM] >>
       rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
       `∃n. x = EL n Cs' ∧ n < LENGTH Cs'` by metis_tac[MEM_EL] >>
       `syneq (f (EL n s')) (EL n Cs')` by metis_tac[] >>
       `no_closures (f (EL n s'))` by metis_tac[no_closures_contains_closure,MEM_EL] >>
       `EL n Cs' = f (EL n s')` by metis_tac[intLangExtraTheory.no_closures_syneq_equal] >>
       `vlabs x = {}` by metis_tac[no_closures_vlabs,MEM_EL] >>
       fs[] ) >>
     cheat ) >>
   fs[Cenv_bs_def,finite_mapTheory.fmap_rel_def]


       `
       print_find"fmap_rel_d"

       fs[EVERY2_APPEND_IMP] >>
       rpt BasicProvers.VAR_EQ_TAC >>
       fs[] >- (
         intLangExtraTheory.no_closures_syneq_equal
         qmatch_assum_abbrev_tac`LIST_REL syneq (MAP f s0) l4` >>
         print_find"vlabs_def"

       LIST_REL_APPEND
       print_apropos``EVERY2 R (l1 ++ l2)``
       Cases_on`MEM x Cs` >- metis_tac[] >>
       qmatch_assum_abbrev_tac`LIST_REL syneq (MAP f s) Cs` >>
       fs[EVERY2_EVERY,EVERY_MEM] >>
       rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,EL_MAP] >>
       `∃n. x = EL n Cs' ∧ n < LENGTH Cs'` by metis_tac[MEM_EL] >>
       `syneq (f (EL n s')) (EL n Cs')` by metis_tac[] >>

       `¬contains_closure (EL n s')` by metis_tac[MEM_EL]
       qsuff_tac`no_closures x`

     print_find"no_closures_vlabs"

   Q.LIST_EXISTS_TAC[`
*)

val _ = export_theory()
