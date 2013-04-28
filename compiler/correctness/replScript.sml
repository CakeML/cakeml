open HolKernel bossLib boolLib boolSimps listTheory rich_listTheory pred_setTheory relationTheory arithmeticTheory whileTheory pairTheory quantHeuristicsLib lcsymtacs
open miniMLExtraTheory miscTheory intLangTheory expToCexpTheory compileTerminationTheory compileCorrectnessTheory bytecodeTerminationTheory bytecodeExtraTheory bytecodeEvalTheory pmatchTheory  labelClosuresTheory
open miscLib MiniMLTerminationTheory finite_mapTheory
val _ = new_theory"repl"

val good_contab_def = Define`
  good_contab (m,w,n) =
    fmap_linv m w`

val env_rs_def = Define`
  env_rs env rs c rd s bs =
    (rs.rbvars = MAP FST env) ∧
    let Cenv = env_to_Cenv (cmap rs.contab) env in
    Cenv_bs c rd s Cenv rs.renv rs.rsz bs`

(* TODO: move *)
val Cevaluate_mono_c = store_thm("Cevaluate_mono_c",
  ``(∀c s env exp res. Cevaluate c s env exp res ⇒
       ∀c'. c ⊑ c' ⇒ Cevaluate c' s env exp res) ∧
    (∀c s env es res. Cevaluate_list c s env es res ⇒
       ∀c'. c ⊑ c' ⇒ Cevaluate_list c' s env es res)``,
  ho_match_mp_tac Cevaluate_ind >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[]) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> fs[SUBMAP_DEF] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> fs[SUBMAP_DEF] >> metis_tac[] ) >>
  strip_tac >- (
    rw[] >> rw[Once Cevaluate_cases] >>
    disj1_tac >>
    map_every qexists_tac[`s'`,`cenv`,`defs`,`n`] >> simp[] >>
    Cases_on`EL n defs`>>TRY(PairCases_on`x`)>>fs[] >>
    fs[LET_THM,UNCURRY] >>
    metis_tac[SUBMAP_DEF] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> fs[SUBMAP_DEF] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ) >>
  strip_tac >- ( rw[] >> rw[Once Cevaluate_cases] >> metis_tac[] ))

val label_closures_Cexp_pred = store_thm("label_closures_Cexp_pred",
  ``(∀ez j e. Cexp_pred e ⇒ Cexp_pred(FST(label_closures ez j e))) ∧
    (∀ez j es. EVERY Cexp_pred es ⇒ EVERY Cexp_pred (FST(label_closures_list ez j es))) ∧
    (∀(ez:num) (j:num) (nz:num) (k:num) (defs:(num#Cexp)list). T)``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- ( ntac 2 (rw[EVERY_MEM]) ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- (
    simp[UNCURRY] >>
    rw[] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    fs[] >>
    first_x_assum match_mp_tac >>
    metis_tac[pairTheory.pair_CASES,SND] ) >>
  strip_tac >- ( rw[] >> rw[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- ( ntac 2 (rw[EVERY_MEM]) >> fs[]) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ) >>
  strip_tac >- ( rw[] >> fs[] ))

(*
val syneq_exp_Cexp_pred = store_thm("syneq_exp_Cexp_pred",
  ``(∀c z1 z2 V e1 e2. syneq_exp c z1 z2 V e1 e2 ⇒ Cexp_pred e1 ⇒ Cexp_pred e2) ∧
    (∀c z1 z2 V defs1 defs2 U. syneq_defs c z1 z2 V defs1 defs2 U ⇒
      EVERY Cexp_pred (MAP (SND o OUTL) (FILTER ISL defs1)) ⇒
      ∀n1 n2. n1 < LENGTH defs1 ∧ U n1 n2 ∧ n2 < LENGTH defs2 ∧ ISL (EL n2 defs2) ⇒ Cexp_pred (SND (OUTL (EL n2 defs2))))``,
  ho_match_mp_tac syneq_exp_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY_MEM,EVERY2_EVERY,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY_MEM] >>
    syneq_exp_rules
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> Cases >> rw[EVERY_MEM] >>
    PairCases_on`x`>>TRY(Cases_on`x'`)>>fs[]) >>
  strip_tac >- (
    rw[EVERY_MEM,EVERY2_EVERY,FORALL_PROD] >>
    rfs[MEM_ZIP,MEM_EL,GSYM LEFT_FORALL_IMP_THM] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY_MEM,MEM_MAP,MEM_FILTER,GSYM LEFT_FORALL_IMP_THM] >>
    Cases_on`y`>>fs[]>>
    PairCases_on`x`>>fs[]
*)

val repl_exp_val = store_thm("repl_exp_val",
  ``∀cenv s c env exp s' v rd rs rs' bc0 bc bs bs'.
      exp_pred exp ∧
      evaluate cenv s env exp (s', Rval v) ∧
      EVERY closed s ∧
      EVERY closed (MAP (FST o SND) env) ∧
      FV exp ⊆ set (MAP FST env) ∧
      closed_under_cenv cenv env s ∧
      LENGTH s' ≤ LENGTH rd.sm ∧
      good_cenv cenv ∧
      good_cmap cenv (cmap rs.contab) ∧
      set (MAP FST cenv) ⊆ FDOM (cmap rs.contab) ∧
      good_contab rs.contab ∧
      env_rs env rs c rd (MAP (v_to_Cv (cmap rs.contab)) s) (bs with code := bc0) ∧
      (repl_exp rs exp = (rs',bc)) ∧
      (bs.code = bc0 ++ bc) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ALL_DISTINCT (FILTER is_Label bc0) ∧
      EVERY (combin$C $< rs.rnext_label o dest_Label) (FILTER is_Label bc0)
      ⇒
      ∃bv rf rd' c'.
      let bs' = bs with <|pc := next_addr bs.inst_length (bc0 ++ bc);
                          stack := bv :: bs.stack; refs := rf|> in
      bc_next^* bs bs' ∧
      (v_to_ov rd'.sm v = bv_to_ov (FST(SND(rs'.contab))) bv) ∧
      env_rs env rs' c' rd' (MAP (v_to_Cv (cmap rs'.contab)) s') bs'``,
  rpt gen_tac >>
  simp[repl_exp_def,compile_Cexp_def,GSYM LEFT_FORALL_IMP_THM] >>
  Q.PAT_ABBREV_TAC`Ce0 = exp_to_Cexp X exp` >>
  Q.PAT_ABBREV_TAC`p = label_closures Y X Ce0` >>
  PairCases_on`p`>>simp[]>> strip_tac >>
  qspecl_then[`cenv`,`s`,`env`,`exp`,`(s',Rval v)`] mp_tac (CONJUNCT1 exp_to_Cexp_thm1) >>
  simp[] >>
  disch_then (qspec_then `cmap rs.contab` mp_tac) >>
  fs[env_rs_def] >>
  simp[FORALL_PROD,GSYM LEFT_FORALL_IMP_THM] >>
  simp_tac(srw_ss()++DNF_ss)[] >>
  map_every qx_gen_tac [`Cs'`,`Cv`] >> strip_tac >>
  `Cexp_pred Ce0` by PROVE_TAC[exp_pred_Cexp_pred] >>
  qspecl_then[`LENGTH env`,`rs.rnext_label`,`Ce0`]mp_tac(CONJUNCT1 label_closures_thm) >>
  discharge_hyps >- (
    simp[Abbr`Ce0`] >>
    match_mp_tac free_vars_exp_to_Cexp_matchable >>
    simp[] ) >>
  simp[] >> strip_tac >>
  qpat_assum`X = bc`mp_tac >>
  Q.PAT_ABBREV_TAC`cce = compile_code_env X Y Z` >>
  `Cexp_pred p0` by metis_tac[label_closures_Cexp_pred,FST] >>
  qmatch_assum_abbrev_tac `Cevaluate FEMPTY Cs Cenv Ce0 (Cs'0, Rval Cv0)` >>
  qmatch_assum_rename_tac`body_count Ce = 0`[] >>
  qabbrev_tac`Cc = alist_to_fmap p1` >>
  `Cevaluate Cc Cs Cenv Ce0 (Cs'0, Rval Cv0)` by (
    match_mp_tac (MP_CANON (CONJUNCT1 Cevaluate_mono_c)) >>
    qexists_tac`FEMPTY`>>simp[SUBMAP_FEMPTY] ) >>
  qspecl_then[`Cc`,`Cs`,`Cenv`,`Ce0`,`(Cs'0,Rval Cv0)`]mp_tac(CONJUNCT1 Cevaluate_syneq) >>
  `LENGTH Cenv = LENGTH env` by simp[Abbr`Cenv`,env_to_Cenv_MAP] >>
  simp[] >> disch_then(qspecl_then[`$=`,`Cs`,`Cenv`,`Ce`]mp_tac) >> simp[] >>

  fs[compile_code_env_def,LET_THM] >>
  qmatch_assum_abbrev_tac `Cevaluate Cc Cd Cs Cenv Ce (Cs', Rval Cv)` >>
  Q.PAT_ABBREV_TAC`cs = compiler_result_out_fupd X Y` >>
  Q.PAT_ABBREV_TAC`d = X:closure_data` >>
  Q.PAT_ABBREV_TAC`tf = X:call_context` >>
  qho_match_abbrev_tac `∃bv rfs. bc_next^* bs (bs1 bv rfs) ∧ P bv rfs` >>
  qabbrev_tac`bs0 = bs with pc := next_addr bs.inst_length (bc0 ++ (REVERSE cs.out))` >>
  qspecl_then[`d`,`rs.renv`,`tf`,`rs.rsz`,`cs`,`Ce`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
  `bc_next^* bs bs0` by (
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC 0` >>
    rw[] >>
    rw[bc_eval1_thm] >>
    `bc_fetch bs = SOME (Jump (Lab rs.rnext_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0` >>
      fs[Abbr`cs`] ) >>
    rw[bc_eval1_def] >>
    rw[bc_find_loc_def] >>
    rw[Abbr`bs0`,bc_state_component_equality] >>
    match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
    rfs[FILTER_APPEND] >>
    fs[Abbr`cs`,FILTER_APPEND,SUM_APPEND] >>
    qexists_tac `LENGTH bc0 + 1` >>
    fs[REVERSE_APPEND] >>
    simp_tac std_ss [GSYM APPEND_ASSOC] >>
    simp_tac (std_ss++ARITH_ss) [EL_APPEND2] >>
    simp_tac pure_ss [ONE,EL] >>
    EVAL_TAC >>
    simp[REV_REVERSE_LEM] >>
    simp_tac (std_ss++ARITH_ss) [TAKE_APPEND2] >>
    simp[SUM_APPEND,FILTER_APPEND] >>
    fsrw_tac[][ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt] >>
    fsrw_tac[QUANT_INST_ss[std_qp]][] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP] >>
    fsrw_tac[ARITH_ss][between_def] >>
    fs[FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    fs[GSYM ADD1,GSYM LESS_EQ] >>
    metis_tac[prim_recTheory.LESS_REFL,LESS_TRANS] ) >>
  `∃bv rfs. bc_next^* bs0 (bs1 bv rfs) ∧ P bv rfs` by (
    qspecl_then[`Cc`,`Cd`,`Cs`,`Cenv`,`Ce`,`Cs', Rval Cv`]mp_tac (CONJUNCT1 compile_val) >>
    fs[] >>
    disch_then (qspecl_then[`sm`,`cls`,`cs`,`d`,`rs.renv`,`rs.rsz`,`bs0`,`bc0 ++ REVERSE cs.out`,`REVERSE bc`,`bc0 ++ REVERSE cs.out`] mp_tac) >>
    simp[Abbr`bs0`,Abbr`P`] >>
    `d.ecs = FEMPTY` by rw[Abbr`d`] >> simp[good_ecs_def] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- cheat >> (* need to assume source language has distinct binders and show that exp_to_Cexp preserves that *)
      conj_tac >- cheat >> (* need to assume source language has distinct binders and show that exp_to_Cexp preserves that *)
      conj_tac >- (
        fsrw_tac[DNF_ss][Abbr`Cenv`,SUBSET_DEF,Abbr`Cs`] >>
        gen_tac >> simp[Once CONJ_COMM] >> simp[GSYM AND_IMP_INTRO] >>
        simp[env_to_Cenv_MAP] >>
        simp[SIMP_RULE(srw_ss())[UNCURRY,LAMBDA_PROD](Q.ISPEC`v_to_Cv (cmap rs.contab) o FST`alist_to_fmap_MAP_values)] >>
        ho_match_mp_tac IN_FRANGE_o_f_suff >>
        simp[all_Clocs_v_to_Cv] >>
        PROVE_TAC[] ) >>
      conj_tac >- (
        fsrw_tac[DNF_ss][Abbr`Cs`,SUBSET_DEF,FRANGE_store_to_Cstore,MEM_MAP,all_Clocs_v_to_Cv] >>
        PROVE_TAC[] ) >>
      simp[Cexp_pred_free_labs] >>
      fs[env_rs_def,LET_THM] >>
      fs[Abbr`Cc`,Abbr`Cd`,good_code_env_def,FEVERY_DEF] >>
      conj_tac >- cheat >> (* need to assume something about sm *)
      conj_tac >- cheat >> (* need to assume something about cls *)
      fs[Abbr`Ce`] >>
      reverse conj_asm2_tac >- (
        conj_tac >- (
          fs[Cenv_bs_def,fmap_rel_def,Abbr`Cenv`] >>
          fs[env_to_Cenv_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
          srw_tac[ETA_ss][] ) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_append_code >>
          Q.PAT_ABBREV_TAC`pc = next_addr X Y` >>
          qexists_tac `bs with <| pc := pc; code := bc0|>` >>
          rw[Abbr`cs`,bc_state_component_equality,Cenv_bs_with_pc] >>
          cheat (* need to fix env_rs_def *)) >>
        fs[Abbr`cs`,FILTER_APPEND,ALL_DISTINCT_APPEND,EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
        fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
        conj_tac >- (spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
        rw[] >> res_tac >> DECIDE_TAC) >>
      fs[] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    disch_then(mp_tac o CONJUNCT1) >>
    disch_then(qspecl_then[`REVERSE bc`,`[]`]mp_tac) >>
    simp[code_for_push_def] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`rf`,`bv`] >>
    rw[LET_THM,Abbr`bs1`,REVERSE_APPEND] >>
    map_every qexists_tac [`bv`,`rf`] >> rw[] >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `Cv_to_ov (FST(SND rs.contab)) (DRESTRICT sm (FDOM Cs')) (v_to_Cv (cmap rs.contab) v)` >>
    `count (LENGTH s') = FDOM Cs'` by fs[fmap_rel_def] >> fs[] >>
    conj_tac >- (
      match_mp_tac EQ_SYM >>
      match_mp_tac (CONJUNCT1 v_to_Cv_ov) >>
      qabbrev_tac`ct=rs.contab` >>
      PairCases_on`ct` >> fs[good_contab_def] >>
      qspecl_then[`cenv`,`s`,`env`,`exp`,`s',Rval v`]mp_tac (CONJUNCT1 evaluate_all_cns) >>
      fs[good_cmap_def] >>
      fs[SUBSET_DEF] >>
      metis_tac[] ) >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `Cv_to_ov (FST(SND rs.contab)) (DRESTRICT sm (FDOM Cs')) Cv` >>
    conj_tac >- (
      match_mp_tac syneq_ov >>
      metis_tac[syneq_sym] ) >>
    match_mp_tac (MP_CANON Cv_bv_ov) >>
    metis_tac[FST] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

set_trace"goalstack print goal at top"0

(* must read an expression followed by all space until the start of another
   expression (or end of string) *)
val parse_def = Define`
  (parse : string -> (t exp # string) option) s = ARB`

val _ = Hol_datatype`
  swhile_result = Terminate of 'a | Diverge`

val _ = Hol_datatype`
  swhile_step_result = Success of 'a | Fail of 'b`

val SWHILE_def = Define`
  SWHILE f x = case OWHILE (ISL o f) (OUTL o f) x of NONE => Diverge | SOME y => Terminate (OUTR (f y))`

val SWHILE_thm = store_thm("SWHILE_thm",
  ``SWHILE f x = case f x of INL x => SWHILE f x | INR y => Terminate y``,
  rw[SWHILE_def] >> Cases_on `f x` >> rw[Once OWHILE_THM])

val intersperse_def = Define`
  (intersperse _ [] = []) ∧
  (intersperse _ [x] = [x]) ∧
  (intersperse a (x::xs) = x::a::intersperse a xs)`

val ov_to_string_def = tDefine "ov_to_string"`
  (ov_to_string (OLit (IntLit i)) = if i < 0 then "-"++(num_to_dec_string (Num (-i)))
                                             else num_to_dec_string (Num i)) ∧
  (ov_to_string (OLit (Bool T)) = "true") ∧
  (ov_to_string (OLit (Bool F)) = "false") ∧
  (ov_to_string (OConv cn vs) = cn++"("++CONCAT(intersperse "," (MAP ov_to_string vs))++")") ∧
  (ov_to_string OFn = "fn")`
  (WF_REL_TAC`measure ov_size` >>
   gen_tac >> Induct >> rw[CompileTheory.ov_size_def] >>
   res_tac >> srw_tac[ARITH_ss][])

(*
``ov_to_string (OConv "Cons" [OLit(IntLit (-3));OConv "Nil"[]]) = X ``
rw[ov_to_string_def,intersperse_def,
   ASCIInumbersTheory.num_to_dec_string_def,
   ASCIInumbersTheory.n2s_def,
   ASCIInumbersTheory.HEX_def,
   Once numposrepTheory.n2l_def ]
*)

val init_bc_state_def =  Define`
  init_bc_state = <|
    stack := [];
    code := [];
    pc := 0;
    refs := FEMPTY;
    handler := 0;
    inst_length := ARB |>`

val repl_def = Define`
  repl s = SWHILE
   (λ(rs,bs,inp:string,out:string).
     if inp = "" then INR (Success out) else
     case parse inp of NONE => INR (Fail "parse error") |
     SOME (exp,inp) =>
       (* typecheck? *)
       let (rs',bc) = repl_exp rs exp in
       let bs' = bs with <|code := bs.code ++ bc;
                           pc := next_addr bs.inst_length bs.code|> in
       case SWHILE (λbs.
         if bs.pc = next_addr bs.inst_length (bs.code ++ bc) then INR (Success bs)
         else case bc_eval1 bs of NONE => INR (Fail "runtime error") | SOME bs => INL bs)
         bs'
       of | Diverge => INR (Fail "divergence")
          | Terminate (Fail s) => INR (Fail s)
          | Terminate (Success bs'') =>
       (* let vals = extract_bindings rs' bs'' in *)
       let v = HD bs''.stack in
       INL (rs',bs'',inp,(out ++ "\n" ++ (ov_to_string (bv_to_ov (FST (SND rs'.contab)) v)))))
  (init_repl_state,init_bc_state,s,"")`

val _ = export_theory()
