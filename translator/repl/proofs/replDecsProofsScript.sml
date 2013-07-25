open HolKernel bossLib boolLib boolSimps lcsymtacs ml_translatorLib ml_translatorTheory miscLib rich_listTheory
open BytecodeTheory bytecodeClockTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeTerminationTheory compilerTerminationTheory semanticsExtraTheory toIntLangProofsTheory toBytecodeProofsTheory compilerProofsTheory ml_repl_stepTheory sideTheory replDecsTheory bootstrap_lemmaTheory
val _ = new_theory"replDecsProofs"

val _ = translation_extends"ml_repl_step"

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
        check_dup_ctors NONE (decs_to_cenv NONE (TAKE i repl_decs))
              tds)``

val bootstrap_result = ``compile_decs NONE FEMPTY ^ct ^m ^renv ^rsz ^cs repl_decs``

val compile_repl_decs_thm = store_thm("compile_repl_decs_thm",
  ``∀s cenv env.
      evaluate_decs NONE [] [] [] [] repl_decs (s,cenv,Rval env) ∧
      ^FV_decs_repl_decs ∧ ^decs_cns_repl_decs ∧ ^check_dup_ctors_repl_decs
      ⇒
      let (ct,m,rsz,cs) = ^bootstrap_result in
      ∀bs bi pp.
        bs.code = REVERSE cs.out
      ∧ bs.pc = 0
      ∧ bs.stack = []
      ∧ bs.clock = NONE
      ∧ Cv_bv pp (v_to_Cv FEMPTY (cmap init_compiler_state.contab) i) bi
      ⇒ ∃bs' rs rd.
        bc_eval bs = SOME bs'
      ∧ bs'.pc = next_addr bs.inst_length bs.code
      ∧ env_rs [] cenv env rs 0 rd (0,s) bs'``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`[]`,`[]`,`[]`,`repl_decs`,`(s,cenv,Rval env)`]mp_tac compile_decs_thm >>
  simp[] >>
  disch_then(CHOOSE_THEN mp_tac) >>
  disch_then(qspecl_then[`^m`,`^cs`]mp_tac) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))) >>
  disch_then(qspecl_then[`init_compiler_state`,`0`,`<|sm:=[];cls:=FEMPTY|>`
                        ,`bs with <|clock := SOME ck|>`]mp_tac) >>
  assume_tac(prove(``init_compiler_state.rmenv = FEMPTY``,rw[CompilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.renv = []``,rw[CompilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.rsz = 0``,rw[CompilerTheory.init_compiler_state_def])) >>
  simp[] >>
  disch_then(qspecl_then[`[]`,`REVERSE cs.out`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    conj_tac >- (
      simp[closed_context_def,closed_under_cenv_def,closed_under_menv_def] ) >>
    conj_tac >- (
      match_mp_tac env_rs_empty >> simp[]) >>
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
  qmatch_assum_abbrev_tac`env_rs [] cenv env rs 0 rd' (0,s) bs'` >>
  map_every qexists_tac[`rs`,`rd'`] >>
  match_mp_tac env_rs_remove_clock >>
  qexists_tac`0,s` >> simp[] >>
  qexists_tac`bs'` >> simp[])

(*
val compile_call_repl_step_thm = store_thm("compile_call_repl_step_thm",
 if bs ~ env,s then bs with code = compile_dec (call_repl_step()) evaluates to bs' with bs' ~ env,s'
*)

val _ = export_theory()
