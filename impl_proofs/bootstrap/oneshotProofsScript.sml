open HolKernel bossLib boolLib lcsymtacs ml_translatorLib ml_translatorTheory miscLib
open compilerTerminationTheory toIntLangProofsTheory toBytecodeProofsTheory compilerProofsTheory bootstrapProofsTheory ml_repl_stepTheory oneshotTheory compile_oneshotTheory sideTheory
val _ = new_theory"oneshotProofs"

val _ = Globals.max_print_depth := 25

val _ = translation_extends"ml_repl_step"

val bootstrap_result_def = Define`
  bootstrap_result = ^(rhs(concl(compiled)))`

val compiled1 = ONCE_REWRITE_RULE[GSYM bootstrap_result_def]compiled

val [ct,m,renv,rsz,cs] =
compiled1 |> concl |> lhs |> rator |> rand |> strip_pair

val FV_decs_oneshot_decs = prove(``FV_decs oneshot_decs = {Short "input"}``,cheat)
val decs_cns_oneshot_decs = prove(``decs_cns NONE oneshot_decs = {}``,cheat)
val check_dup_ctors_oneshot_decs = prove(``
(∀i tds.
    i < LENGTH oneshot_decs ∧ EL i oneshot_decs = Dtype tds ⇒
        check_dup_ctors NONE (decs_to_cenv NONE (TAKE i oneshot_decs))
              tds)``, cheat)

val no_closures_all_vlabs = store_thm("no_closures_all_vlabs",
  ``∀v. no_closures v ⇒ all_vlabs (v_to_Cv mv m v)``,
  ho_match_mp_tac no_closures_ind >>
  simp[no_closures_def,compilerTerminationTheory.v_to_Cv_def] >>
  simp[pmatchTheory.vs_to_Cvs_MAP,EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM])

val no_closures_vlabs = store_thm("no_closures_vlabs",
  ``∀v. no_closures v ⇒ vlabs (v_to_Cv mv m v) = {}``,
  ho_match_mp_tac no_closures_ind >>
  simp[compilerTerminationTheory.v_to_Cv_def,no_closures_def] >>
  simp[no_closures_def,compilerTerminationTheory.v_to_Cv_def,intLangExtraTheory.vlabs_list_MAP] >>
  simp[pmatchTheory.vs_to_Cvs_MAP,EVERY_MEM,MEM_MAP,GSYM LEFT_FORALL_IMP_THM,miscTheory.IMAGE_EQ_SING])

print_find"no_closures"

val oneshot_thm = store_thm("oneshot_thm",
  ``∀i s cenv env.
      evaluate_decs NONE [] [] [] [("input",i)] oneshot_decs (s,cenv,Rval env) ∧
      closed [] i ∧ all_cns i = {} ∧ all_locs i = {} ∧ no_closures i
      ⇒
      let (ct,m,renv,rsz,cs) = bootstrap_result in
      ∀bs bi.
        bs.code = REVERSE cs.out
      ∧ bs.pc = 0
      ∧ bs.stack = [bi]
      ∧ Cv_bv 

      ⇒ ∃bs' junk.
        bc_eval bs = SOME bs'
      ∧ bs'.pc = next_addr bs.inst_length bs.code
      ∧ bs'.output = junk ++ print_v (THE (lookup "it" env))``,
  rw[] >>
  qspecl_then[`NONE`,`[]`,`[]`,`[]`,`[("input",i)]`,`oneshot_decs`,`(s,cenv,Rval env)`]mp_tac compile_decs_thm >>
  simp[compile_decs_FOLDL] >>
  disch_then(CHOOSE_THEN mp_tac) >>
  disch_then(qspecl_then[`^m`,`^cs`]mp_tac) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))) >>
  disch_then(qspecl_then[`init_compiler_state with <|renv:=[("input",0)];rsz:=1|>`,`0`,`<|sm:=[];cls:=FEMPTY|>`,`bs with clock := SOME ck`]mp_tac) >>
  assume_tac(prove(``init_compiler_state.rmenv = FEMPTY``,rw[CompilerTheory.init_compiler_state_def])) >>
  assume_tac(prove(``init_compiler_state.renv = []``,rw[CompilerTheory.init_compiler_state_def])) >>
  simp[compiled1] >>
  disch_then(qspecl_then[`[]`,`REVERSE cs.out`]mp_tac) >>
  simp[FV_decs_oneshot_decs,decs_cns_oneshot_decs,check_dup_ctors_oneshot_decs] >>
  discharge_hyps >- (
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

      print_find"Cenv_bs_def"

        no_closures_all_vlabs
      print_find"vlabs_menv"
  
  env_rs
                 

  disch_then strip_assume_tac >>
  first_x_assum(qspecl_then[`<|

      ∀
      ∃

(*
val (Eval_peic,peic_side_def) = get_cert"parse_elaborate_infertype_compile"

val ml_repl_step_DeclAssumC =
DeclAssumC_def
|> Q.SPECL[`ml_repl_step_decls`,`envC`,`envE`]
|> EQ_IMP_RULE
|> fst
|> UNDISCH

val FV_decs_ml_repl_step_decls = prove(``FV_decs ml_repl_step_decls = {}``,cheat)
val decs_cns_ml_repl_step_decls = prove(``decs_cns NONE ml_repl_step_decls = {}``,cheat)
val check_dup_ctors_ml_repl_step_decs = prove(
``(∀i tds. i < LENGTH ml_repl_step_decls ∧ EL i ml_repl_step_decls = Dtype tds ⇒
     check_dup_ctors NONE (decs_to_cenv NONE (TAKE i ml_repl_step_decls)) tds)``,cheat)

val bootstrap_result_def = Define`
  bootstrap_result = ^(rhs(concl(compiled)))`

val bootstrap_ct = Define`
  bootstrap_ct = FST(bootstrap_result)`

val bootstrap_cs = Define`
  bootstrap_cs = (SND(SND(SND(SND(bootstrap_result)))))`

val bootstrap_m = Define`
  bootstrap_m = (FST(SND(bootstrap_result)))`

val bootstrap_env = Define`
  bootstrap_env = (FST(SND(SND(bootstrap_result))))`

val bootstrap_rsz = Define`
  bootstrap_rsz = (FST(SND(SND(SND(bootstrap_result)))))`

val compiled1 = ONCE_REWRITE_RULE[GSYM bootstrap_result_def]compiled

val bootstrap_result_split = prove(
  ``bootstrap_result = (bootstrap_ct,bootstrap_m,bootstrap_env,bootstrap_rsz,bootstrap_cs)``,
  rw[bootstrap_ct,bootstrap_cs,bootstrap_m,bootstrap_env,bootstrap_rsz])

val ml_repl_step_compiler_correctness1 =
compile_decs_thm
|> CONV_RULE (RESORT_FORALL_CONV(List.rev))
|> Q.SPEC`(s2,envC,Rval envE)`
|> SIMP_RULE (srw_ss()) []
|> SIMP_RULE (srw_ss()) [compile_decs_FOLDL]
|> CONV_RULE (RESORT_FORALL_CONV(List.rev))
|> Q.SPECL[`NONE`,`[]`,`[]`,`empty_store`,`[]`,`ml_repl_step_decls`]
|> SIMP_RULE (srw_ss()) [GSYM DeclsC_def]
|> UNDISCH
|> SIMP_RULE (srw_ss()) [closed_context_def,empty_store_def,closed_under_cenv_def,closed_under_menv_def
                        ,decs_cns_ml_repl_step_decls,FV_decs_ml_repl_step_decls,check_dup_ctors_ml_repl_step_decs]

val (ck,t) = dest_exists(concl ml_repl_step_compiler_correctness1)
val ml_repl_step_compiler_correctness2 =
ASSUME t
|> Q.SPECL[`<|bvars:=[];mvars:=FEMPTY;cnmap:=cmap init_compiler_state.contab|>`,`<|out:=[];next_label:=4|>`]
|> SIMP_RULE(srw_ss())[]
|> CONV_RULE(RESORT_FORALL_CONV(fn ls => (List.drop(ls,5))@(List.take(ls,5))))
|> Q.SPECL[`init_compiler_state`,`0`,`<|sm:=[];cls:=FEMPTY|>`
          ,`bs with <|clock := SOME ck; pc := 0; stack := []; code := bootstrap_cs.out|>`,`[]`]
|> SIMP_RULE(srw_ss())[CompilerTheory.init_compiler_state_def,good_labels_def]
|> SIMP_RULE(srw_ss())[(SIMP_RULE(srw_ss())[CompilerTheory.init_compiler_state_def]env_rs_empty)]
|> ONCE_REWRITE_RULE[CONV_RULE(LAND_CONV(SIMP_CONV(srw_ss())[CompilerTheory.init_compiler_state_def]))compiled1]
|> SIMP_RULE(srw_ss())[bootstrap_result_split]
|> ONCE_REWRITE_RULE[LET_THM]
|> PairRules.PBETA_RULE
|> SIMP_RULE pure_ss [PAIR_EQ]

pairTheory.

val ml_repl_step_compiler_correctness3 =
ml_repl_step_compiler_correctness2
|> SIMP_[LET_THM]
compiled
LET_SS

AND_IMP_INTRO
LEFT_FORALL_IMP_THM
RIGHT_FORALL_IMP_THM
LEFT_EXISTS_IMP_THM
RIGHT_EXISTS_IMP_THM

FORALL_AND_THM
SKOLEM_THM

|> UNDISCH

hyp it

help"CHOOSE"

CHOOSE (v,|- ?x. s) (s[v/x]|-t) = |- t
EXISTS (?x. p, u)   |- p[u/x]   = |- ?x. p

|> MP ml_repl_step_DeclAssumC

print_find"DeclsC"

*)

val _ = export_theory()
