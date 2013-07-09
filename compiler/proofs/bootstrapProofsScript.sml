open HolKernel boolLib bossLib boolSimps lcsymtacs miscLib miscTheory
open finite_mapTheory listTheory rich_listTheory relationTheory pred_setTheory
open IntLangTheory intLangExtraTheory  CompilerTheory compilerTerminationTheory toBytecodeProofsTheory compilerProofsTheory
open BytecodeTheory bytecodeExtraTheory bytecodeClockTheory bytecodeEvalTheory
val _ = new_theory"bootstrapProofs"

val env_rs_empty = store_thm("env_rs_empty",
  ``bs.stack = [] ∧ (∀n. bs.clock = SOME n ⇒ n = ck) ∧ rd.sm = [] ∧ rd.cls = FEMPTY ∧ cs = init_compiler_state ⇒
    env_rs [] [] [] cs 0 rd (ck,[]) bs``,
  simp[env_rs_def,init_compiler_state_def,intLangExtraTheory.good_cmap_def,FLOOKUP_UPDATE
      ,good_contab_def,IntLangTheory.tuple_cn_def,toIntLangProofsTheory.cmap_linv_def] >>
  simp[pmatchTheory.env_to_Cenv_MAP,intLangExtraTheory.all_vlabs_menv_def
      ,intLangExtraTheory.vlabs_menv_def,pred_setTheory.SUM_IMAGE_THM
      ,closed_Clocs_def,closed_vlabs_def] >>
  strip_tac >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_DEF])

val closed_context_empty = store_thm("closed_context_empty",
  ``closed_context [] [] [] []``,
  simp[closed_context_def,toIntLangProofsTheory.closed_under_cenv_def,closed_under_menv_def])

val env_rs_remove_clock = store_thm("env_rs_remove_clock",
   ``∀menv cenv env rs cz rd cs bs cs' ck' bs'.
     env_rs menv cenv env rs cz rd cs bs ∧ cs' = (ck',SND cs) ∧
     bs' = bs with clock := NONE ⇒
     env_rs menv cenv env rs cz rd cs' bs'``,
  rw[env_rs_def] >> fs[LET_THM] >>
  rpt HINT_EXISTS_TAC >>
  qexists_tac`Cs` >> simp[] >>
  match_mp_tac Cenv_bs_change_store >>
  map_every qexists_tac[`rd`,`FST cs,Cs`,`bs`,`bs.refs`,`NONE`] >>
  simp[bc_state_component_equality] >> rfs[] >>
  fs[Cenv_bs_def,s_refs_def,good_rd_def])

val tac =
  strip_tac >>
  imp_res_tac RTC_bc_next_can_be_unclocked >>
  rator_x_assum`env_rs`mp_tac >>
  Q.PAT_ABBREV_TAC`rs = compiler_state_contab_fupd x y` >>
  strip_tac >>
  map_every qexists_tac[`bvs`,`rf`,`rs`,`rd'`] >>
  conj_tac >- (
    qmatch_abbrev_tac`bc_eval bs = SOME bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs' bs1'` >>
    `bs' = bs ∧ bs1' = bs1` by (
      simp[Abbr`bs'`,Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] ) >>
    match_mp_tac (MP_CANON RTC_bc_next_bc_eval) >> fs[] >>
    simp[bc_eval1_thm] >>
    `bc_fetch bs1 = NONE` by (
      simp[bc_fetch_def] >>
      match_mp_tac bc_fetch_aux_end_NONE >>
      simp[Abbr`bs1`] ) >>
    simp[bc_eval1_def] ) >>
  match_mp_tac env_rs_remove_clock >>
  qmatch_assum_abbrev_tac`env_rs [] cenv env rs 0 rd' cs' bs'` >>
  map_every qexists_tac[`cs'`,`bs'`,`0`] >>
  simp[Abbr`cs'`] >>
  simp[Abbr`bs'`,bc_state_component_equality]

val compile_decs_from_empty = store_thm("compile_decs_from_empty",
  ``∀decs cenv env. evaluate_decs NONE [] [] [] [] decs ([],cenv,Rval env)
    ∧ FV_decs decs = {}
    ∧ (∀i tds.  i < LENGTH decs ∧ EL i decs = Dtype tds ⇒ check_dup_ctors NONE (decs_to_cenv NONE (TAKE i decs)) tds)
    ∧ "" ∉ new_decs_cns decs
    ∧ decs_cns NONE decs = {}
    ⇒
    ∃ct m rsz cs.
    compile_decs NONE FEMPTY
      init_compiler_state.contab
      <|bvars:=[];mvars:=FEMPTY;cnmap:=cmap(init_compiler_state.contab)|>
      [] 0 <|out:=[];next_label:=0|> decs
    = (ct,m,rsz,cs) ∧
    ∀bs.
    bs.code = REVERSE cs.out
    ∧ bs.pc = 0
    ∧ bs.stack = []
    ∧ bs.clock = NONE
    ∧ bs.output = ""
    ⇒
    ∃st rf rs rd.
    let bs' = bs with <| pc    := next_addr bs.inst_length bs.code
                       ; stack := st
                       ; refs  := rf
                       |> in
    bc_eval bs = SOME bs'
    ∧ env_rs [] cenv env rs 0 rd (0,[]) bs'``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`[]`,`[]`,`[]`,`decs`,`[],cenv,Rval env`]mp_tac compile_decs_thm >>
  simp[closed_context_empty] >>
  disch_then(Q.X_CHOOSE_THEN`ck`strip_assume_tac) >>
  Q.PAT_ABBREV_TAC`m = exp_to_Cexp_state_bvars_fupd x y` >>
  Q.PAT_ABBREV_TAC`cs = compiler_result_out_fupd x y` >>
  Q.PAT_ABBREV_TAC`ct = init_compiler_state.contab` >>
  Q.PAT_ABBREV_TAC`p = compile_decs a b ct m d e f g` >> PairCases_on`p` >> simp[] >>
  rpt strip_tac >>
  first_x_assum(qspecl_then[`m`,`cs`]mp_tac) >>
  disch_then(qspec_then`<|rmenv:=FEMPTY;renv:=[];rsz:=0;contab:=ct;rnext_label:=cs.next_label|>`mp_tac o
    CONV_RULE(RESORT_FORALL_CONV(fn l => List.drop(l,5)@List.take(l,5)))) >> fs[] >>
  disch_then(qspecl_then[`0`,`<|cls := FEMPTY; sm := []|>`,`bs with clock := SOME ck`,`[]`]mp_tac) >>
  simp[markerTheory.Abbrev_def] >>
  discharge_hyps >- (
    qspecl_then[`decs`,`NONE`,`FEMPTY`,`ct`,`m`,`[]`,`0`,`cs`]mp_tac compile_decs_append_out >>
    simp[Abbr`m`,Abbr`cs`] >> strip_tac >>
    simp[good_labels_def] >>
    match_mp_tac env_rs_empty >>
    simp[compiler_state_component_equality,init_compiler_state_def]) >>
  tac)

val compile_decs_wrap_from_empty = store_thm("compile_decs_wrap_from_empty",
  ``∀decs cenv env. evaluate_decs NONE [] [] [] [] decs ([],cenv,Rval env)
    ∧ FV_decs decs = {}
    ∧ (∀i tds.  i < LENGTH decs ∧ EL i decs = Dtype tds ⇒ check_dup_ctors NONE (decs_to_cenv NONE (TAKE i decs)) tds)
    ∧ "" ∉ new_decs_cns decs
    ∧ decs_cns NONE decs = {}
    ⇒
    ∃ct renv cs.
    compile_decs_wrap NONE init_compiler_state decs = (ct,renv,cs) ∧
    ∀bs.
    bs.code = REVERSE cs.out
    ∧ bs.pc = 0
    ∧ bs.stack = []
    ∧ bs.clock = NONE
    ∧ bs.output = ""
    ⇒
    ∃st rf rs rd.
    let bs' = bs with <| pc    := next_addr bs.inst_length bs.code
                       ; stack := st
                       ; refs  := rf
                       |> in
    bc_eval bs = SOME bs'
    ∧ env_rs [] cenv env rs 0 rd (0,[]) bs'``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`[]`,`[]`,`[]`,`decs`,`[],cenv,Rval env`]mp_tac compile_decs_wrap_thm >>
  simp[closed_context_empty] >>
  disch_then(qspec_then`init_compiler_state`mp_tac) >>
  strip_tac >> simp[] >>
  gen_tac >> strip_tac >>
  simp[markerTheory.Abbrev_def] >>
  first_x_assum(qspecl_then[`<|cls := FEMPTY; sm := []|>`,`bs with clock := SOME ck`,`[]`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    simp[good_labels_def] >>
    match_mp_tac env_rs_empty >>
    simp[compiler_state_component_equality,init_compiler_state_def]) >>
  tac)

val compile_body_val = store_thm("compile_body_val",
  ``∀menv s env' b s' v vs rd renv env rmenv csz bs bc0 cc bc1 st cs bce bcr bvs ret az cl benv.
    Cevaluate menv s env' b (s',Cval v)
    ∧ set (free_vars b) ⊆ count (LENGTH renv)
    ∧ env' = REVERSE vs ++ env
    ∧ Cenv_bs rd menv s env' rmenv renv 0 csz (bs with code := bce)
    ∧ closed_Clocs menv env' (SND s)
    ∧ closed_vlabs menv env' (SND s) rmenv bce
    ∧ all_labs b
    ∧ EVERY (code_env_cd rmenv bce) (free_labs (LENGTH env') b)
    ∧ (compile rmenv renv (TCTail az 0) 0 cs b).out = cc ++ cs.out
    ∧ bs.code = bce ++ bcr
    ∧ bs.code = bc0 ++ REVERSE cc ++ bc1
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ bs.clock = SOME (FST s)
    ∧ bs.stack = benv::(CodePtr ret)::REVERSE bvs++cl::st
    ∧ LENGTH bvs = az
    ∧ LIST_REL (Cv_bv (mk_pp rd (bs with code := bce))) vs bvs
    ∧ csz ≤ LENGTH st
    ∧ good_labels cs.next_label bc0
    ∧ ALL_DISTINCT (FILTER is_Label bce)
    ⇒
    code_for_return rd bs bce st ret bs.handler v s s'``,
  rw[] >>
  qspecl_then[`menv`,`s`,`REVERSE vs ++ env`,`b`,`s',Cval v`]mp_tac(CONJUNCT1 compile_val) >> simp[] >>
  disch_then(qspecl_then[`rd`,`rmenv`,`cs`,`renv`,`0`,`csz`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cc`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    fs[closed_Clocs_def] >>
    fs[closed_vlabs_def] >>
    fs[good_labels_def] >>
    fsrw_tac[ARITH_ss][]) >>
  disch_then(match_mp_tac o CONJUNCT2) >>
  simp[] >>
  CONV_TAC(RESORT_EXISTS_CONV(List.rev)) >>
  qexists_tac`bvs` >> simp[] >>
  qexists_tac`vs` >> simp[])

val Cevaluate_list_MAP_Var = store_thm("Cevaluate_list_MAP_Var",
  ``∀vs menv s env. set vs ⊆ count (LENGTH env) ⇒
      Cevaluate_list menv s env (MAP (CVar o Short) vs) (s,Cval (MAP (combin$C EL env) vs))``,
  Induct >> simp[Once Cevaluate_cases])

val Cevaluate_list_MAP_Var_rwt = store_thm("Cevaluate_list_MAP_Var_rwt",
  ``∀vs menv s env res. set vs ⊆ count (LENGTH env) ⇒
      (Cevaluate_list menv s env (MAP (CVar o Short) vs) res ⇔
       res = (s,Cval (MAP (combin$C EL env) vs)))``,
  metis_tac[Cevaluate_list_MAP_Var,intLangExtraTheory.Cevaluate_determ])

val compile_call_val = store_thm("compile_call_val",
  ``Cevaluate FEMPTY (ck,[]) env (CCall F (CVar(Short f)) (MAP (CVar o Short) xs)) ((0,[]),Cval v)
    ∧ el_check f env = SOME (CRecClos clenv [(SOME cd,LENGTH es,b)] 0)
    ∧ bind_fv (LENGTH es,ue) 1 0 = (FST(SND cd),SND(SND cd),ue')
    ∧ MAP (combin$C el_check env) xs = MAP SOME vs
    ∧ (compile FEMPTY (MAP CTEnv (FST(SND cd))) (TCTail (LENGTH es) 0) 0 cs b).out = REVERSE cc ++ cs.out
    ∧ set (free_vars b) ⊆ count (LENGTH (FST(SND cd)))
    ∧ all_labs b
    ∧ EVERY all_vlabs clenv
    ∧ EVERY all_vlabs env
    ∧ EVERY (λv. all_Clocs v = {}) clenv
    ∧ EVERY (λv. all_Clocs v = {}) env
    ∧ EVERY (λv. (∀cd. cd ∈ vlabs v ⇒ code_env_cd FEMPTY bce cd)) clenv
    ∧ EVERY (λv. (∀cd. cd ∈ vlabs v ⇒ code_env_cd FEMPTY bce cd)) env
    ∧ EVERY (λcd. code_env_cd FEMPTY bce cd) (free_labs (LENGTH es + LENGTH (SND(SND(SND cd))) + 1) b)
    ∧ bs.code = bce ++ bcr
    ∧ bc3 ++ [Label (FST cd)] = bc0
    ∧ bc3 ++ [Label (FST cd)] ++ cc ++ bc2 = bce
    ∧ bs.code = bc0 ++ cc ++ bc1 ++ [CallPtr]
    ∧ bs.pc = next_addr bs.inst_length (bc0 ++ cc ++ bc1)
    ∧ bs.stack = CodePtr a::Block 0 benv::REVERSE bvs++[Block closure_tag [CodePtr a; Block 0 benv]]
    ∧ bc_find_loc_aux bce bs.inst_length (FST cd) 0 = SOME a
    ∧ next_addr bs.inst_length bc0 = a
    ∧ bs.clock = SOME ck
    ∧ LENGTH bvs = LENGTH es
    ∧ rd.sm = []
    ∧ s_refs rd (ck,[]) (bs with code := bce)
    ∧ benv_bvs (mk_pp rd (bs with code := bce)) benv (SND(SND cd)) clenv [(SOME cd,LENGTH es,b)]
    ∧ LIST_REL (Cv_bv (mk_pp rd (bs with code := bce))) vs bvs
    ∧ good_labels cs.next_label bc0
    ∧ ALL_DISTINCT (FILTER is_Label bce)
    ⇒
    ∃bv rf rd' ck'.
    let bs' = bs with <|stack := [bv]; pc := next_addr bs.inst_length bs.code; refs := rf; clock := ck' |> in
    bc_next^* bs bs'
    ∧ Cv_bv (mk_pp rd' (bs' with code := bce)) v bv
    ∧ DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf (COMPL (set rd'.sm))
    ∧ rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls``,
  simp[] >> strip_tac >>
  `bc_fetch bs = SOME CallPtr` by (
    match_mp_tac bc_fetch_next_addr >>
    CONV_TAC SWAP_EXISTS_CONV >>
    qexists_tac`[]`>>simp[] >>
    simp[SUM_APPEND,FILTER_APPEND] ) >>
  simp[markerTheory.Abbrev_def] >>
  qho_match_abbrev_tac`∃bv rf rd' ck. bc_next^* bs (bs2 bv rf ck) ∧ P bv rf rd' ck` >>
  qsuff_tac`∃bs1. bc_next bs bs1 ∧ ∃bv rf rd' ck. bc_next^* bs1 (bs2 bv rf ck) ∧ P bv rf rd' ck`
    >- metis_tac[RTC_CASES1] >>
  simp[bc_eval1_thm,bc_eval1_def] >>
  rator_x_assum`Cevaluate`mp_tac >>
  simp[Once Cevaluate_cases] >>
  last_x_assum mp_tac >>
  simp[CompilerLibTheory.el_check_def] >> strip_tac >>
  `set xs ⊆ count (LENGTH env)` by (
    fs[SUBSET_DEF,LIST_EQ_REWRITE,MEM_EL,GSYM LEFT_FORALL_IMP_THM] >>
    rw[] >> res_tac >> fs[EL_MAP,CompilerLibTheory.el_check_def] >>
    rfs[EL_MAP] ) >>
  simp[Cevaluate_list_MAP_Var_rwt] >>
  PairCases_on`cd`>>simp[]>>
  Q.PAT_ABBREV_TAC`env0:Cv list = MAP X xs` >>
  Q.PAT_ABBREV_TAC`recs:Cv list = MAP X cd2` >>
  Q.PAT_ABBREV_TAC`envs:Cv list = MAP X cd3` >>
  Q.PAT_ABBREV_TAC`CRC = CRecClos X Y` >>
  strip_tac >>
  Q.PAT_ABBREV_TAC`bs1 = bc_state_stack_fupd x y` >>
  qmatch_assum_abbrev_tac`Cevaluate menv Cs env' b (s,Cval v)` >>
  qspecl_then[`menv`,`Cs`,`env'`,`b`,`s`,`v`]mp_tac compile_body_val >>
  simp[Abbr`env'`] >>
  disch_then(qspecl_then[`env0`,`rd`,`MAP CTEnv cd1`]mp_tac)>>simp[]>>
  disch_then(qspecl_then[`FEMPTY`,`0`,`bs1`,`bc0`,`REVERSE cc`]mp_tac)>>
  simp[Abbr`bs1`]>>
  disch_then(qspecl_then[`[]`,`cs`,`bce`,`bcr`]mp_tac)>>simp[] >>
  qpat_assum`x = bce++bcr`(assume_tac o SYM) >> simp[] >> fs[] >> simp[Abbr`Cs`] >>
  discharge_hyps >- (
    `cd2 = []` by (
      fs[ToBytecodeTheory.bind_fv_def,LET_THM] ) >>
    `MAP (combin$C EL env) xs = vs` by (
      qpat_assum`MAP x y = MAP c d`mp_tac >>
      simp[LIST_EQ_REWRITE,EL_MAP] >> strip_tac >>
      pop_assum mp_tac >>
      simp[EL_MAP,CompilerLibTheory.el_check_def] ) >>
    conj_tac >- (
      match_mp_tac Cenv_bs_bind_fv >>
      simp[Abbr`menv`] >>
      qexists_tac`cd1`>>simp[] >>
      qexists_tac`bvs`>>simp[] >>
      simp[Abbr`CRC`] >>
      Q.PAT_ABBREV_TAC`defs:def list = X` >>
      map_every qexists_tac[`clenv`,`defs`,`0`] >>
      simp[Abbr`envs`,Abbr`recs`] >>
      map_every qexists_tac[`[]`,`cd3`] >>
      simp[] >>
      qexists_tac`ue` >>
      simp[Abbr`env0`,Abbr`defs`] >> fs[] >>
      match_mp_tac s_refs_with_irr >>
      HINT_EXISTS_TAC >>
      simp[] ) >>
    conj_tac >- (
      simp[Abbr`menv`,closed_Clocs_def,Abbr`env0`,Abbr`CRC`,Abbr`recs`,Abbr`envs`,IMAGE_EQ_SING,MEM_MAP] >>
      simp[GSYM LEFT_FORALL_IMP_THM] >>
      fs[EVERY_MEM,IMAGE_EQ_SING] >>
      reverse conj_tac >- (
        Cases_on`cd3=[]`>>simp[] >>
        metis_tac[MEM_EL] ) >>
      Cases_on`vs=[]`>>simp[] >>
      BasicProvers.VAR_EQ_TAC >>
      fs[MEM_MAP,SUBSET_DEF] >> metis_tac[MEM_EL] ) >>
    conj_tac >- (
      simp[closed_vlabs_def,Abbr`menv`,vlabs_menv_def,all_vlabs_menv_def] >>
      simp[vlabs_list_APPEND,vlabs_list_REVERSE,Abbr`CRC`] >>
      simp[Abbr`recs`,Abbr`envs`,EVERY_MAP,Abbr`env0`,EVERY_REVERSE] >>
      conj_tac >- (
        fs[EVERY_MEM] >>
        fs[SUBSET_DEF] >>
        metis_tac[MEM_EL] ) >>
      gen_tac >> strip_tac
      >- (
        BasicProvers.VAR_EQ_TAC >>
        fs[vlabs_list_MAP,MEM_MAP,SUBSET_DEF,EVERY_MEM] >>
        metis_tac[MEM_EL] )
      >- (
        fs[vlabs_list_MAP,MEM_MAP,EVERY_MEM] >>
        metis_tac[MEM_EL] )
      >- (
        simp[] >>
        simp[code_env_cd_def] >>
        conj_tac >- (
          simp[good_cd_def] >>
          metis_tac[] ) >>
        qexists_tac`cs` >>
        simp[] >>
        qexists_tac`bc3` >>
        qexists_tac`bc2` >>
        simp[] >>
        fs[good_labels_def] >>
        qpat_assum`X = bc0`(assume_tac o SYM) >>
        fs[FILTER_APPEND] )
      >- ( fs[EVERY_MEM] )
      >- (
        BasicProvers.VAR_EQ_TAC >>
        fs[vlabs_list_MAP,MEM_MAP] >>
        BasicProvers.VAR_EQ_TAC >>
        BasicProvers.VAR_EQ_TAC >>
        fs[EVERY_MEM] >>
        metis_tac[MEM_EL])) >>
    conj_tac >- (
      simp[Abbr`env0`,Abbr`envs`,Abbr`recs`] >>
      fsrw_tac[ETA_ss][] ) >>
    simp[Abbr`env0`] ) >>
  simp[code_for_return_def] >>
  disch_then(qx_choosel_then[`bv`,`rf`,`rd'`,`ck'`]strip_assume_tac) >>
  map_every qexists_tac[`bv`,`rf`,`rd'`,`ck'`] >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2'` >>
  `bs2' = bs2 bv rf ck'` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality] >>
    simp[bump_pc_def,FILTER_APPEND,SUM_APPEND] ) >>
  simp[Abbr`P`] >> BasicProvers.VAR_EQ_TAC >> simp[])


(*
val CCall_thm = store_thm("CCall_thm",
  ``Cevaluate menv cs env exp (cs',Cval v)
    ∧ 
    print_find"code_env_cd"
*)

(*
val Cenv_bs_call_thm = store_thm("Cenv_bs_call_thm",
  ``let f = Closure closed x body in
    evaluate F menv cenv s ((x,a)::env) body (s,Rval v)

    ∧ LIST_REL syneq (vs_to_Cvs mv m s) Cs
    ∧ LIST_REL syneq (env_to_Cenv mv m ((x,a)::env)) Cenv
    ∧ syneq (v_to_Cv mv m f) Cf


    ∧ bc_fetch bs = SOME CallPtr
    ∧ bs.stack = CodePtr ptr::benv::barg::cl::[]

    ⇒
    bc_
  env_rs_def
*)

  (*
  ∃ptr benv st str rf h rd.
  let cl = Block closure_tag [CodePtr ptr;benv] in
  let bs1 = bs0 with <| pc := next_addr bs0.inst_length bs0.code
                      ; stack := cl::st
                      ; output := str
                      ; refs := rf
                      ; handler := h
                      |> in
  bc_eval bs0 = SOME bs1 ∧
  env_rs [] cenv env rs (LENGTH bs1.stack) rd (0,[]) bs1 ∧

val call_decl_thm = store_thm("call_decl_thm",
``let decs = ds++[Dlet (Pvar fun) (Fun _a _b)] in
  evaluate_decs NONE [] [] [] [] decs ([],cenv,Rval env) ∧
  FV_decs decs = {} ∧
  "" ∉ new_decs_cns decs ∧
  decs_cns NONE decs = {} ∧
  (∀i tds.
    i < LENGTH decs ∧ EL i decs = Dtype tds ⇒
    check_dup_ctors NONE (decs_to_cenv NONE (TAKE i decs)) tds) ∧
  compile_decs_wrap NONE init_compiler_state decs = (ct,renv,cs) ∧
  bs0.code = REVERSE cs.out ∧
  bs0.pc = 0 ∧
  bs0.stack = [] ∧
  bs0.clock = NONE
⇒
  ∃ptr benv st str rf h rd.
  let cl = Block closure_tag [CodePtr ptr;benv] in
  let bs1 = bs0 with <| pc := next_addr bs0.inst_length bs0.code
                      ; stack := cl::st
                      ; output := str
                      ; refs := rf
                      ; handler := h
                      |> in
  bc_eval bs0 = SOME bs1 ∧
  env_rs [] cenv env rs (LENGTH bs1.stack) rd (0,[]) bs1 ∧
  ∀bs ret mid barg cenv arg v.
    bs.code = [CallPtr] ∧ (* this can't work: where's the code for the function you're going to call? *)
    bs.pc = 0 ∧            (* it would be nice if possible to have [] instead of mid++st *)
    bs.stack = CodePtr ptr::benv::barg::cl::mid++st ∧
    bs.handler = h ∧
    bs.clock = NONE ∧
    Cenv_bs rd FEMPTY (0,[]) Cenv FEMPTY (MAP (CTDec o SND) rs.renv) rs.rsz rs.rsz bs ∧ (* not true!
      the call stuff on the stack gets in the way, and
      the rs.renv probably needs to know about "x", and
      need to connect cenv to Cenv and env to rs.renv *)
    evaluate F [] cenv (0,[]) (("x",arg)::env) (App Opapp (Var (Short fun)) (Var(Short "x"))) ((0,[]),Rval v)
                (* this should provably be the same as [("x",arg);(fun,lookup fun env)] *)
   (* use do_app instead of evaluate? *)
   (* just need something that says: lookup fun env applied to arg returns v, semantically *)
    ⇒
    ∃bv rf'.
    let bs' = bs with <| stack := bv::mid++st
                       ; pc := next_addr bs.inst_length bs.code
                       ; refs := rf'
                       |> in
    Cenv_bs rd FEMPTY (0,[]) Cenv FEMPTY (MAP (CTDec o SND) rs.renv) rs.rsz rs.rsz bs' ∧
    bc_eval bs = SOME bs' ∧
    Cv_bv (mk_pp rd bs') (v_to_Cv FEMPTY (cmap rs.contab) v) bv``,
cheat)
*)

val _ = export_theory()
