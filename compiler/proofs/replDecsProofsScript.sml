open HolKernel bossLib boolLib boolSimps lcsymtacs miscLib arithmeticTheory listTheory rich_listTheory
open bytecodeTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeTerminationTheory compilerTerminationTheory semanticsExtraTheory toIntLangProofsTheory toBytecodeProofsTheory compilerProofsTheory
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

val _ = export_theory()
