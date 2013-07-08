open HolKernel boolLib bossLib lcsymtacs miscLib
open finite_mapTheory
open CompilerTheory compilerTerminationTheory toBytecodeProofsTheory compilerProofsTheory
open BytecodeTheory bytecodeExtraTheory bytecodeClockTheory bytecodeEvalTheory
val _ = new_theory"bootstrapProofs"

val env_rs_empty = store_thm("env_rs_empty",
  ``bs.stack = [] ∧ (∀n. bs.clock = SOME n ⇒ n = ck) ∧ rd.sm = [] ∧ rd.cls = FEMPTY ⇒
    env_rs [] [] [] init_compiler_state 0 rd (ck,[]) bs``,
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

val compile_decs_from_empty = store_thm("compile_decs_from_empty",
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
    simp[] ) >>
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
  simp[Abbr`bs'`,bc_state_component_equality])

val compile_body_val = store_thm("compile_body_val",
  ``  Cevaluate menv s env' b (s',Cval v)
    ∧ set (free_vars b) ⊆ count (LENGTH renv)
    ∧ env' = REVERSE vs ++ env
    ∧ Cenv_bs rd menv s env' rmenv renv 0 csz (bs with code := bce)
    ∧ closed_Clocs menv env' (SND s)
    ∧ closed_vlabs menv env' (SND s) rmenv bce
    ∧ all_labs b
    ∧ EVERY (code_env_cd rmenv bce) (free_labs (LENGTH env') b)
    ∧ (compile rmenv renv (TCTail az 0) 0 cs b).out = cc ++ cs.out
    ∧ bs.code = bce ++ bcr
    ∧ bs.code = bc0 ++ Label l::REVERSE cc ++ bc1
    ∧ bs.pc = next_addr bs.inst_length (bc0 ++ [Label l])
    ∧ bs.clock = SOME (FST s)
    ∧ bs.stack = benv::(CodePtr ret)::REVERSE bvs++cl::st
    ∧ LENGTH bvs = az
    ∧ LIST_REL (Cv_bv (mk_pp rd (bs with code := bce))) vs bvs
    ∧ csz ≤ LENGTH st
    ∧ good_labels cs.next_label (bc0 ++ [Label l])
    ∧ ALL_DISTINCT (FILTER is_Label bce)
    ⇒
    code_for_return rd bs bce st ret bs.handler v s s'``,
  rw[] >>
  qspecl_then[`menv`,`s`,`REVERSE vs ++ env`,`b`,`s',Cval v`]mp_tac(CONJUNCT1 compile_val) >> simp[] >>
  disch_then(qspecl_then[`rd`,`rmenv`,`cs`,`renv`,`0`,`csz`,`bs`,`bce`,`bcr`,`bc0 ++ [Label l]`,`REVERSE cc`]mp_tac) >>
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
