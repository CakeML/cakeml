open HolKernel bossLib boolLib boolSimps listTheory pairTheory rich_listTheory pred_setTheory arithmeticTheory finite_mapTheory relationTheory sortingTheory stringTheory
open miscLib miscTheory bigStepTheory semanticPrimitivesTheory bigClockTheory replTheory terminationTheory
open bytecodeTheory bytecodeExtraTheory bytecodeEvalTheory bytecodeClockTheory bytecodeLabelsTheory bytecodeTerminationTheory
open modLangTheory conLangTheory decLangTheory intLangTheory toIntLangTheory toBytecodeTheory compilerTheory intLangExtraTheory modLangProofTheory conLangProofTheory decLangProofTheory exhLangProofTheory intLangProofTheory bytecodeProofTheory compilerTerminationTheory
open patLangProofTheory

val _ = new_theory"compilerProof"

(* TODO: remove

val good_v_def = tDefine"good_v"`
  (good_v (Litv _) ⇔ T) ∧
  (good_v (Conv _ vs) ⇔ good_vs vs) ∧
  (good_v (Closure (envM,envC,envE) _ _) ⇔
    good_envM envM ∧ good_envE envE) ∧
  (good_v (Recclosure (envM,envC,envE) funs f) ⇔
   good_envM envM ∧ good_envE envE ∧
   ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v (Loc _) ⇔ T) ∧
  (good_vs [] ⇔ T) ∧
  (good_vs (v::vs) ⇔ good_v v ∧ good_vs vs) ∧
  (good_envE [] ⇔ T) ∧
  (good_envE ((_,v)::envE) ⇔ good_v v ∧ good_envE envE) ∧
  (good_envM [] ⇔ T) ∧
  (good_envM ((_,envE)::envM) ⇔ good_envE envE ∧ good_envM envM)`
(WF_REL_TAC`inv_image $< (\x. case x of
  | INL v => v_size v
  | INR (INL vs) => v7_size vs
  | INR (INR (INL envE)) => v5_size envE
  | INR (INR (INR envM)) => v3_size envM)`)
val _ = export_rewrites["good_v_def"]

val good_vs_EVERY = store_thm("good_vs_EVERY",
  ``∀vs. good_vs vs ⇔ EVERY good_v vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_EVERY"]

val good_envE_EVERY = store_thm("good_envE_EVERY",
  ``∀envE. good_envE envE ⇔ EVERY good_v (MAP SND envE)``,
  Induct >> simp[] >> Cases >> simp[])

val good_envM_EVERY = store_thm("good_envM_EVERY",
  ``∀envM. good_envM envM ⇔ EVERY good_envE (MAP SND envM)``,
  Induct >> simp[] >> Cases >> simp[])

val _ = export_rewrites["good_envM_EVERY","good_envE_EVERY","good_vs_EVERY"]

val good_v_i1_def = tDefine"good_v_i1"`
  (good_v_i1 (Litv_i1 _) ⇔ T) ∧
  (good_v_i1 (Conv_i1 _ vs) ⇔ good_vs_i1 vs) ∧
  (good_v_i1 (Closure_i1 (_,env) _ _) ⇔ good_vs_i1 (MAP SND env)) ∧
  (good_v_i1 (Recclosure_i1 (_,env) funs f) ⇔
   good_vs_i1 (MAP SND env) ∧ ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v_i1 (Loc_i1 _) ⇔ T) ∧
  (good_vs_i1 [] ⇔ T) ∧
  (good_vs_i1 (v::vs) ⇔ good_v_i1 v ∧ good_vs_i1 vs)`
  (WF_REL_TAC`inv_image $< (\x. case x of INL v => v_i1_size v | INR vs => v_i14_size vs)` >>
   simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[v_i1_size_def] >>
   Cases >> simp[v_i1_size_def] >> rw[] >> res_tac >> simp[])
val _ = export_rewrites["good_v_i1_def"]

val good_vs_i1_EVERY = store_thm("good_vs_i1_EVERY",
  ``∀vs. good_vs_i1 vs ⇔ EVERY good_v_i1 vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_i1_EVERY"]

val good_v_i2_def = tDefine"good_v_i2"`
  (good_v_i2 (Litv_i2 _) ⇔ T) ∧
  (good_v_i2 (Conv_i2 _ vs) ⇔ good_vs_i2 vs) ∧
  (good_v_i2 (Closure_i2 env _ _) ⇔ good_vs_i2 (MAP SND env)) ∧
  (good_v_i2 (Recclosure_i2 env funs f) ⇔
   good_vs_i2 (MAP SND env) ∧ ALL_DISTINCT (MAP FST funs) ∧ MEM f (MAP FST funs)) ∧
  (good_v_i2 (Loc_i2 _) ⇔ T) ∧
  (good_vs_i2 [] ⇔ T) ∧
  (good_vs_i2 (v::vs) ⇔ good_v_i2 v ∧ good_vs_i2 vs)`
  (WF_REL_TAC`inv_image $< (\x. case x of INL v => v_i2_size v | INR vs => v_i23_size vs)` >>
   simp[] >> conj_tac >> rpt gen_tac >> Induct_on`env` >> simp[v_i2_size_def] >>
   Cases >> simp[v_i2_size_def] >> rw[] >> res_tac >> simp[])
val _ = export_rewrites["good_v_i2_def"]

val good_vs_i2_EVERY = store_thm("good_vs_i2_EVERY",
  ``∀vs. good_vs_i2 vs ⇔ EVERY good_v_i2 vs``,
  Induct >> simp[])
val _ = export_rewrites["good_vs_i2_EVERY"]

val v_to_i1_preserves_good = store_thm("v_to_i1_preserves_good",
  ``(∀genv v v1. v_to_i1 genv v v1 ⇒ good_v v ⇒ good_v_i1 v1) ∧
    (∀genv vs vs1. vs_to_i1 genv vs vs1 ⇒ good_vs vs ⇒ good_vs_i1 vs1) ∧
    (∀genv env env1. env_to_i1 genv env env1 ⇒ good_envE env ⇒ good_vs_i1 (MAP SND env1)) ∧
    (∀genv tops shadowers env. global_env_inv_flat genv tops shadowers env ⇒
      good_envE env ∧
      (∀n. n < LENGTH genv ∧ IS_SOME (EL n genv) ⇒
        ∃x. x ∉ shadowers ∧ IS_SOME (lookup x env) ∧ FLOOKUP tops x = SOME n) ⇒
      EVERY (OPTION_EVERY good_v_i1) genv) ∧
    (∀genv mods tops menv shadowers env. global_env_inv genv mods tops menv shadowers env ⇒
      good_envE env ∧ good_envM menv
      ⇒ EVERY (OPTION_EVERY good_v_i1) genv)``,
  ho_match_mp_tac v_to_i1_ind >> simp[] >>
  conj_tac >- (
    simp[funs_to_i1_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX]) >>
  conj_tac >- (
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> res_tac >>
    Cases_on`EL n genv`>>fs[] >>
    qmatch_assum_rename_tac`z ∉ shadowers`[] >>
    Cases_on`lookup z env`>>fs[] >>
    res_tac >> fs[] >> rw[] >> fs[] >> rw[] >>
    imp_res_tac libPropsTheory.lookup_in >>
    fs[MEM_EL] ) >>
  rw[] >> fs[] >>
  cheat (* false? TODO: need help fixing the statement *))

val v_to_i2_preserves_good = store_thm("v_to_i2_preserves_good",
  ``(∀g v v2. v_to_i2 g v v2 ⇒ good_v_i1 v ⇒ good_v_i2 v2) ∧
    (∀g vs vs2. vs_to_i2 g vs vs2 ⇒ good_vs_i1 vs ⇒ good_vs_i2 vs2) ∧
    (∀g env env2. env_to_i2 g env env2 ⇒ good_vs_i1 (MAP SND env) ⇒ good_vs_i2 (MAP SND env2))``,
  ho_match_mp_tac v_to_i2_ind >>
  simp[funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val v_to_exh_preserves_good = store_thm("v_to_exh_preserves_good",
  ``(∀v exh. good_v_i2 v ⇒ good_v_exh (v_to_exh exh v)) ∧
    (∀env exh. good_vs_i2 (MAP SND env) ⇒ good_vs_exh (MAP SND (env_to_exh exh env))) ∧
    (∀(p:string#v_i2) exh. good_v_i2 (SND p) ⇒ good_v_exh (v_to_exh exh (SND p))) ∧
    (∀vs exh. good_vs_i2 vs ⇒ good_vs_exh (vs_to_exh exh vs))``,
  ho_match_mp_tac (TypeBase.induction_of(``:v_i2``)) >>
  simp[v_to_exh_def] >>
  conj_tac >- (
    Induct >> simp[v_to_exh_def] >- (
      simp[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
    Cases >> simp[v_to_exh_def] >>
    metis_tac[] ) >>
  Cases >> simp[v_to_exh_def])

val genv_to_exh_preserves_good = prove(
  ``∀exh genv2.
    EVERY (OPTION_EVERY good_v_i2) genv2 ⇒
    EVERY (OPTION_EVERY good_v_exh)
      (MAP (OPTION_MAP (v_to_exh exh)) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_exh_preserves_good])

val genv_to_i2_preserves_good = prove(
  ``∀g genv genv2. genv_to_i2 g genv genv2 ⇒
      EVERY (OPTION_EVERY good_v_i1) genv ⇒
      EVERY (OPTION_EVERY good_v_i2) genv2``,
  ho_match_mp_tac genv_to_i2_ind >>
  simp[] >> metis_tac[v_to_i2_preserves_good])
*)

val funs_to_exh_MAP = store_thm("funs_to_exh_MAP",
  ``∀exh funs. funs_to_exh exh funs = MAP (λ(f,x,e). (f,x,exp_to_exh exh e)) funs``,
  Induct_on`funs` >> simp[exp_to_exh_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_exh_def])

val funs_to_i2_MAP = store_thm("funs_to_i2_MAP",
  ``∀g funs. funs_to_i2 g funs = MAP (λ(f,x,e). (f,x,exp_to_i2 g e)) funs``,
  Induct_on`funs` >> simp[exp_to_i2_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i2_def])

val funs_to_i1_MAP = store_thm("funs_to_i1_MAP",
  ``∀menv env funs. funs_to_i1 menv env funs = MAP (λ(f,x,e). (f,x,exp_to_i1 menv (env \\ x) e)) funs``,
  Induct_on`funs` >> simp[exp_to_i1_def] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[exp_to_i1_def])

val vs_to_exh_MAP = store_thm("vs_to_exh_MAP",
  ``∀exh vs. vs_to_exh exh vs = MAP (v_to_exh exh) vs``,
  Induct_on`vs`>>simp[v_to_exh_def])

val (closed_exh_rules,closed_exh_ind,closed_exh_cases) = Hol_reln`
(closed_exh (Litv_exh l)) ∧
(EVERY (closed_exh) vs ⇒ closed_exh (Conv_exh cn vs)) ∧
(EVERY (closed_exh) (MAP SND env) ∧ free_vars_exh b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_exh (Closure_exh env x b)) ∧
(EVERY (closed_exh) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_exh e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_exh (Recclosure_exh env defs d)) ∧
(closed_exh (Loc_exh n))`;

val closed_exh_lit_loc_conv = store_thm("closed_exh_lit_loc_conv",
  ``closed_exh (Litv_exh l) ∧ closed_exh (Loc_exh n) ∧
    (closed_exh (Conv_exh a bs) ⇔ EVERY closed_exh bs)``,
  rw[closed_exh_cases])
val _ = export_rewrites["closed_exh_lit_loc_conv"]

val v_to_pat_closed = store_thm("v_to_pat_closed",
  ``(∀v. closed_exh v ⇒ closed_pat (v_to_pat v)) ∧
    (∀vs. EVERY closed_exh vs ⇒  EVERY closed_pat (vs_to_pat vs))``,
  ho_match_mp_tac v_to_pat_ind >>
  simp[v_to_exh_def] >>
  rw[] >- (
    simp[Once closed_pat_cases] >>
    pop_assum mp_tac >>
    simp[Once closed_exh_cases] >>
    strip_tac >>
    specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat) mp_tac >>
    fs[SUBSET_DEF,PULL_EXISTS,EVERY_MAP,MEM_MAP,EVERY_MEM] >> rw[] >>
    res_tac >> rw[] >>
    qho_match_abbrev_tac`THE (find_index a ls n) < z` >>
    qho_match_abbrev_tac`P (THE (find_index a ls n))` >>
    match_mp_tac THE_find_index_suff >>
    simp[Abbr`P`,Abbr`n`,Abbr`z`,Abbr`ls`,Abbr`a`,MEM_MAP] ) >>
  simp[Once closed_pat_cases] >>
  pop_assum mp_tac >>
  simp[Once closed_exh_cases] >>
  strip_tac >>
  simp[funs_to_pat_MAP] >>
  fs[EVERY_MAP,EVERY_MEM,SUBSET_DEF,PULL_FORALL,FORALL_PROD,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
  rpt gen_tac >> strip_tac >- metis_tac[] >>
  strip_tac >- (
    qho_match_abbrev_tac`the d (find_index a b c) < d` >>
    qho_match_abbrev_tac`P (the d (find_index a b c))` >>
    match_mp_tac the_find_index_suff >>
    simp[Abbr`P`,Abbr`a`,Abbr`d`,Abbr`c`,Abbr`b`,MEM_MAP] >>
    simp[EXISTS_PROD] >> metis_tac[] ) >>
  strip_tac >>
  specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat) mp_tac >>
  fs[SUBSET_DEF,PULL_EXISTS,EVERY_MAP,MEM_MAP,EVERY_MEM,EXISTS_PROD] >>
  discharge_hyps >- metis_tac[] >> rw[] >>
  res_tac >> rw[] >>
  qho_match_abbrev_tac`THE (find_index a ls n) < z` >>
  qho_match_abbrev_tac`P (THE (find_index a ls n))` >>
  match_mp_tac THE_find_index_suff >>
  simp[Abbr`P`,Abbr`n`,Abbr`z`,Abbr`ls`,Abbr`a`,MEM_MAP,EXISTS_PROD] >>
  metis_tac[])

val free_vars_i2_def = tDefine"free_vars_i2"`
  free_vars_i2 (Raise_i2 e) = free_vars_i2 e ∧
  free_vars_i2 (Handle_i2 e pes) = free_vars_i2 e ∪ free_vars_pes_i2 pes ∧
  free_vars_i2 (Lit_i2 _) = {} ∧
  free_vars_i2 (Con_i2 _ es) = free_vars_list_i2 es ∧
  free_vars_i2 (Var_local_i2 n) = {n} ∧
  free_vars_i2 (Var_global_i2 _) = {} ∧
  free_vars_i2 (Fun_i2 x e) = free_vars_i2 e DIFF {x} ∧
  free_vars_i2 (Uapp_i2 _ e) = free_vars_i2 e ∧
  free_vars_i2 (App_i2 _ e1 e2) = free_vars_i2 e1 ∪ free_vars_i2 e2 ∧
  free_vars_i2 (If_i2 e1 e2 e3) = free_vars_i2 e1 ∪ free_vars_i2 e2 ∪ free_vars_i2 e3 ∧
  free_vars_i2 (Mat_i2 e pes) = free_vars_i2 e ∪ free_vars_pes_i2 pes ∧
  free_vars_i2 (Let_i2 bn e1 e2) = free_vars_i2 e1 ∪ (free_vars_i2 e2 DIFF (case bn of NONE => {} | SOME x => {x})) ∧
  free_vars_i2 (Letrec_i2 defs e) = (free_vars_defs_i2 defs ∪ free_vars_i2 e) DIFF set(MAP FST defs) ∧
  free_vars_i2 (Extend_global_i2 _) = {} ∧
  free_vars_list_i2 [] = {} ∧
  free_vars_list_i2 (e::es) = free_vars_i2 e ∪ free_vars_list_i2 es ∧
  free_vars_defs_i2 [] = {} ∧
  free_vars_defs_i2 ((f,x,e)::ds) = (free_vars_i2 e DIFF {x}) ∪ free_vars_defs_i2 ds ∧
  free_vars_pes_i2 [] = {} ∧
  free_vars_pes_i2 ((p,e)::pes) = (free_vars_i2 e DIFF (set (pat_bindings_i2 p []))) ∪ free_vars_pes_i2 pes`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_i2_size e
  | INR (INL es) => exp_i26_size es
  | INR (INR (INL defs)) => exp_i21_size defs
  | INR (INR (INR pes)) => exp_i23_size pes)`)
val _ = export_rewrites["free_vars_i2_def"]

val free_vars_pes_i2_MAP = store_thm("free_vars_pes_i2_MAP",
  ``∀pes. free_vars_pes_i2 pes = BIGUNION (set (MAP (λ(p,e). free_vars_i2 e DIFF set (pat_bindings_i2 p [])) pes))``,
  Induct >> simp[] >> Cases >> simp[])

open astTheory exhLangTheory compilerTerminationTheory

val pat_bindings_exh_pat_to_exh = store_thm("pat_bindings_exh_pat_to_exh",
  ``∀p ls. pat_bindings_exh (pat_to_exh p) ls = pat_bindings_i2 p ls``,
  ho_match_mp_tac pat_to_exh_ind >>
  simp[pat_bindings_i2_def,pat_to_exh_def,pat_bindings_exh_def,ETA_AX] >>
  Induct >> simp[pat_bindings_i2_def,pat_bindings_exh_def])
val _ = export_rewrites["pat_bindings_exh_pat_to_exh"]

val free_vars_exh_exp_to_exh = store_thm("free_vars_exh_exp_to_exh",
  ``(∀exh e. free_vars_exh (exp_to_exh exh e) = free_vars_i2 e) ∧
    (∀exh es. free_vars_list_exh (exps_to_exh exh es) = free_vars_list_i2 es) ∧
    (∀exh pes. free_vars_pes_exh (pat_exp_to_exh exh pes) = free_vars_pes_i2 pes) ∧
    (∀exh funs. free_vars_defs_exh (funs_to_exh exh funs) = free_vars_defs_i2 funs)``,
  ho_match_mp_tac exp_to_exh_ind >>
  simp[exp_to_exh_def] >>
  conj_tac >- (
    rw[add_default_def,pat_bindings_i2_def,free_vars_pes_i2_MAP] ) >>
  conj_tac >- (
    rw[add_default_def,pat_bindings_i2_def,free_vars_pes_i2_MAP] ) >>
  rw[funs_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] )
val _ = export_rewrites["free_vars_exh_exp_to_exh"]

val (closed_i2_rules,closed_i2_ind,closed_i2_cases) = Hol_reln`
(closed_i2 (Litv_i2 l)) ∧
(EVERY (closed_i2) vs ⇒ closed_i2 (Conv_i2 cn vs)) ∧
(EVERY (closed_i2) (MAP SND env) ∧ free_vars_i2 b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_i2 (Closure_i2 env x b)) ∧
(EVERY (closed_i2) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_i2 e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_i2 (Recclosure_i2 env defs d)) ∧
(closed_i2 (Loc_i2 n))`;

val closed_i2_lit_loc_conv = store_thm("closed_i2_lit_loc_conv",
  ``closed_i2 (Litv_i2 l) ∧ closed_i2 (Loc_i2 n) ∧
    (closed_i2 (Conv_i2 a bs) ⇔ EVERY closed_i2 bs)``,
  rw[closed_i2_cases])
val _ = export_rewrites["closed_i2_lit_loc_conv"]

val env_to_exh_MAP = store_thm("env_to_exh_MAP",
  ``∀exh env. env_to_exh exh env = MAP (λ(x,e). (x, v_to_exh exh e)) env``,
  Induct_on`env`>>simp[v_to_exh_def] >> Cases >> simp[v_to_exh_def])

val v_to_exh_closed = store_thm("v_to_exh_closed",
  ``(∀exh v. closed_i2 v ⇒ closed_exh (v_to_exh exh v)) ∧
    (∀exh vs. EVERY closed_i2 vs ⇒  EVERY closed_exh (vs_to_exh exh vs)) ∧
    (∀exh env. EVERY closed_i2 (MAP SND env) ⇒ EVERY closed_exh (MAP SND (env_to_exh exh env)))``,
  ho_match_mp_tac v_to_exh_ind >> simp[v_to_exh_def] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_i2_cases] >>
    simp[Once closed_exh_cases] >>
    simp[env_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once closed_i2_cases] >>
  simp[Once closed_exh_cases] >>
  simp[funs_to_exh_MAP,EVERY_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,ETA_AX] >>
  simp[LAMBDA_PROD,env_to_exh_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,FST_pair])

val free_vars_i1_def = tDefine"free_vars_i1"`
  free_vars_i1 (Raise_i1 e) = free_vars_i1 e ∧
  free_vars_i1 (Handle_i1 e pes) = free_vars_i1 e ∪ free_vars_pes_i1 pes ∧
  free_vars_i1 (Lit_i1 _) = {} ∧
  free_vars_i1 (Con_i1 _ es) = free_vars_list_i1 es ∧
  free_vars_i1 (Var_local_i1 n) = {n} ∧
  free_vars_i1 (Var_global_i1 _) = {} ∧
  free_vars_i1 (Fun_i1 x e) = free_vars_i1 e DIFF {x} ∧
  free_vars_i1 (Uapp_i1 _ e) = free_vars_i1 e ∧
  free_vars_i1 (App_i1 _ e1 e2) = free_vars_i1 e1 ∪ free_vars_i1 e2 ∧
  free_vars_i1 (If_i1 e1 e2 e3) = free_vars_i1 e1 ∪ free_vars_i1 e2 ∪ free_vars_i1 e3 ∧
  free_vars_i1 (Mat_i1 e pes) = free_vars_i1 e ∪ free_vars_pes_i1 pes ∧
  free_vars_i1 (Let_i1 bn e1 e2) = free_vars_i1 e1 ∪ (free_vars_i1 e2 DIFF (case bn of NONE => {} | SOME x => {x})) ∧
  free_vars_i1 (Letrec_i1 defs e) = (free_vars_defs_i1 defs ∪ free_vars_i1 e) DIFF set(MAP FST defs) ∧
  free_vars_list_i1 [] = {} ∧
  free_vars_list_i1 (e::es) = free_vars_i1 e ∪ free_vars_list_i1 es ∧
  free_vars_defs_i1 [] = {} ∧
  free_vars_defs_i1 ((f,x,e)::ds) = (free_vars_i1 e DIFF {x}) ∪ free_vars_defs_i1 ds ∧
  free_vars_pes_i1 [] = {} ∧
  free_vars_pes_i1 ((p,e)::pes) = (free_vars_i1 e DIFF (set (pat_bindings p []))) ∪ free_vars_pes_i1 pes`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_i1_size e
  | INR (INL es) => exp_i16_size es
  | INR (INR (INL defs)) => exp_i11_size defs
  | INR (INR (INR pes)) => exp_i13_size pes)`)
val _ = export_rewrites["free_vars_i1_def"]

val (closed_i1_rules,closed_i1_ind,closed_i1_cases) = Hol_reln`
(closed_i1 (Litv_i1 l)) ∧
(EVERY (closed_i1) vs ⇒ closed_i1 (Conv_i1 cn vs)) ∧
(EVERY (closed_i1) (MAP SND env) ∧ free_vars_i1 b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_i1 (Closure_i1 (envC,env) x b)) ∧
(EVERY (closed_i1) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_i1 e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_i1 (Recclosure_i1 (envC,env) defs d)) ∧
(closed_i1 (Loc_i1 n))`;

val closed_i1_lit_loc_conv = store_thm("closed_i1_lit_loc_conv",
  ``closed_i1 (Litv_i1 l) ∧ closed_i1 (Loc_i1 n) ∧
    (closed_i1 (Conv_i1 a bs) ⇔ EVERY closed_i1 bs)``,
  rw[closed_i1_cases])
val _ = export_rewrites["closed_i1_lit_loc_conv"]

val pat_bindings_i2_pat_to_i2 = store_thm("pat_bindings_i2_pat_to_i2",
  ``∀t p ls. pat_bindings_i2 (pat_to_i2 t p) ls = pat_bindings p ls``,
  ho_match_mp_tac pat_to_i2_ind >>
  simp[pat_bindings_def,pat_to_i2_def,pat_bindings_i2_def,ETA_AX] >>
  gen_tac >> Induct >> simp[pat_bindings_def,pat_bindings_i2_def])
val _ = export_rewrites["pat_bindings_i2_pat_to_i2"]

val free_vars_i2_exp_to_i2 = store_thm("free_vars_i2_exp_to_i2",
  ``(∀exh e. free_vars_i2 (exp_to_i2 exh e) = free_vars_i1 e) ∧
    (∀exh es. free_vars_list_i2 (exps_to_i2 exh es) = free_vars_list_i1 es) ∧
    (∀exh pes. free_vars_pes_i2 (pat_exp_to_i2 exh pes) = free_vars_pes_i1 pes) ∧
    (∀exh funs. free_vars_defs_i2 (funs_to_i2 exh funs) = free_vars_defs_i1 funs)``,
  ho_match_mp_tac exp_to_i2_ind >>
  simp[exp_to_i2_def] >>
  rw[funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] )
val _ = export_rewrites["free_vars_i2_exp_to_i2"]

val v_to_i2_closed = store_thm("v_to_i2_closed",
  ``(∀g v1 v2. v_to_i2 g v1 v2 ⇒ closed_i1 v1 ⇒ closed_i2 v2) ∧
    (∀g v1 v2. vs_to_i2 g v1 v2 ⇒ EVERY closed_i1 v1 ⇒ EVERY closed_i2 v2) ∧
    (∀g v1 v2. env_to_i2 g v1 v2 ⇒
      set (MAP FST v1) = set (MAP FST v2) ∧
      (EVERY closed_i1 (MAP SND v1) ⇒ EVERY closed_i2 (MAP SND v2)))``,
  ho_match_mp_tac v_to_i2_ind >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_i1_cases] >>
    simp[Once closed_i2_cases] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once closed_i1_cases] >>
  simp[Once closed_i2_cases] >>
  simp[funs_to_i2_MAP,EVERY_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,ETA_AX] >>
  simp[LAMBDA_PROD,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,FST_pair])

val FV_def = tDefine "FV"`
  (FV (Raise e) = FV e) ∧
  (FV (Handle e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Lit _) = {}) ∧
  (FV (Con _ ls) = FV_list ls) ∧
  (FV (Var id) = {id}) ∧
  (FV (Fun x e) = FV e DIFF {Short x}) ∧
  (FV (Uapp _ e) = FV e) ∧
  (FV (App _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
  (FV (Mat e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Let xo e b) = FV e ∪ (FV b DIFF (case xo of NONE => {} | SOME x => {Short x}))) ∧
  (FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF set (MAP (Short o FST) defs)) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p [])))) ∪ FV_pes pes) ∧
  (FV_defs [] = {}) ∧
  (FV_defs ((_,x,e)::defs) =
     (FV e DIFF {Short x}) ∪ FV_defs defs)`
  (WF_REL_TAC `inv_image $< (λx. case x of
     | INL e => exp_size e
     | INR (INL es) => exp6_size es
     | INR (INR (INL pes)) => exp3_size pes
     | INR (INR (INR (defs))) => exp1_size defs)`)
val _ = export_rewrites["FV_def"]

val _ = Parse.overload_on("SFV",``λe. {x | Short x ∈ FV e}``)

val (closed_rules,closed_ind,closed_cases) = Hol_reln`
(closed (Litv l)) ∧
(EVERY closed vs ⇒ closed (Conv cn vs)) ∧
(EVERY closed (MAP SND envE) ∧
 EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
 FV b ⊆ (IMAGE Short ({x} ∪ set (MAP FST envE))) ∪ { Long mn x | ∃env. MEM (mn,env) envM ∧ MEM x (MAP FST env)}
⇒ closed (Closure (envM,envC,envE) x b)) ∧
(EVERY closed (MAP SND envE) ∧
 EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
 MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). FV e ⊆ (IMAGE Short ({x} ∪ set (MAP FST defs) ∪ set (MAP FST envE))) ∪
                         { Long mn x | ∃env. MEM (mn,env) envM ∧ MEM x (MAP FST env) }) defs
⇒ closed (Recclosure (envM,envC,envE) defs d)) ∧
(closed (Loc n))`;

val closed_lit_loc_conv = store_thm("closed_lit_loc_conv",
  ``closed (Litv l) ∧ closed (Loc n) ∧
    (closed (Conv a bs) ⇔ EVERY closed bs)``,
  rw[closed_cases])
val _ = export_rewrites["closed_lit_loc_conv"]

val FV_defs_MAP = store_thm("FV_defs_MAP",
  ``∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls))``,
  Induct_on`ls`>>simp[FORALL_PROD])

val FDOM_FOLDR_DOMSUB = store_thm("FDOM_FOLDR_DOMSUB",
  ``∀ls fm. FDOM (FOLDR (λk m. m \\ k) fm ls) = FDOM fm DIFF set ls``,
  Induct >> simp[] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  simp[] >> metis_tac[])

val free_vars_i1_exp_to_i1 = store_thm("free_vars_i1_exp_to_i1",
  ``(∀menv env e. free_vars_i1 (exp_to_i1 menv env e) = SFV e DIFF FDOM env) ∧
    (∀menv env es. free_vars_list_i1 (exps_to_i1 menv env es) = {x | Short x ∈ FV_list es} DIFF FDOM env) ∧
    (∀menv env pes. free_vars_pes_i1 (pat_exp_to_i1 menv env pes) = {x | Short x ∈ FV_pes pes} DIFF FDOM env) ∧
    (∀menv env funs. free_vars_defs_i1 (funs_to_i1 menv env funs) = {x | Short x ∈ FV_defs funs} DIFF FDOM env)``,
  ho_match_mp_tac exp_to_i1_ind >>
  simp[exp_to_i1_def] >> rpt conj_tac >>
  TRY (
    rpt gen_tac >> strip_tac >>
    TRY (BasicProvers.CASE_TAC >> fs[]) >>
    ONCE_REWRITE_TAC[EXTENSION] >>
    simp[] >> metis_tac[] ) >>
  TRY (
    rpt gen_tac >> BasicProvers.CASE_TAC >>
    fs[FLOOKUP_DEF] >> rw[] >> NO_TAC)
  >- (
    rpt gen_tac >> strip_tac >>
    simp[funs_to_i1_MAP] >>
    simp[MAP_MAP_o,FST_triple,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
    ONCE_REWRITE_TAC[EXTENSION] >>
    simp[MEM_MAP,FDOM_FOLDR_DOMSUB] >>
    simp[FV_defs_MAP,PULL_EXISTS,EXISTS_PROD,MEM_MAP,FORALL_PROD] >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    simp[FDOM_FOLDR_DOMSUB] >>
    ONCE_REWRITE_TAC[EXTENSION] >>
    simp[] >> metis_tac[] ))
val _ = export_rewrites["free_vars_i1_exp_to_i1"]

val v_to_i1_closed = store_thm("v_to_i1_closed",
  ``(∀g v1 v2. v_to_i1 g v1 v2 ⇒ closed v1 ⇒ closed_i1 v2) ∧
    (∀g v1 v2. vs_to_i1 g v1 v2 ⇒ EVERY closed v1 ⇒ EVERY closed_i1 v2) ∧
    (∀g v1 v2. env_to_i1 g v1 v2 ⇒
      set (MAP FST v1) = set (MAP FST v2) ∧
      (EVERY closed (MAP SND v1) ⇒ EVERY closed_i1 (MAP SND v2))) ∧
    (∀g m s e. global_env_inv_flat g m s e ⇒ T) ∧
    (∀g mods tops menv s env. global_env_inv g mods tops menv s env ⇒ T)``,
  ho_match_mp_tac v_to_i1_ind >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_cases] >>
    simp[Once closed_i1_cases] >>
    fs[SUBSET_DEF,PULL_EXISTS,FDOM_DRESTRICT] >>
    rw[] >> res_tac >> fs[] >> metis_tac[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_cases] >>
    simp[Once closed_i1_cases] >>
    fs[SUBSET_DEF,PULL_EXISTS,FDOM_DRESTRICT] >>
    simp[funs_to_i1_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,EVERY_MAP] >>
    strip_tac >>
    match_mp_tac (MP_CANON (GEN_ALL MONO_EVERY)) >>
    HINT_EXISTS_TAC >> simp[] >>
    simp[FORALL_PROD,PULL_EXISTS,PULL_FORALL,FDOM_DRESTRICT] >>
    rw[] >> res_tac >> fs[] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  simp[Once closed_cases] >>
  simp[Once closed_i1_cases] >>
  strip_tac >>
  pop_assum mp_tac >>
  simp[EVERY_MEM] >>
  disch_then(qspec_then`x,y,e`mp_tac) >>
  discharge_hyps >- metis_tac[find_recfun_lookup,libPropsTheory.lookup_in3] >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >>
  qx_gen_tac`z` >> strip_tac >>
  first_x_assum(qspec_then`Short z`mp_tac) >>
  simp[] >>
  fs[FDOM_FUPDATE_LIST] >>
  rw[] >>
  fs[FLOOKUP_DEF,FDOM_FUPDATE_LIST] >>
  metis_tac[SUBSET_DEF] )

val FV_dec_def = Define`
  (FV_dec (Dlet p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec defs) = FV (Letrec defs (Lit ARB))) ∧
  (FV_dec (Dtype _) = {}) ∧
  (FV_dec (Dexn _ _) = {})`
val _ = export_rewrites["FV_dec_def"]

val new_dec_vs_def = Define`
  (new_dec_vs (Dtype _) = []) ∧
  (new_dec_vs (Dexn _ _) = []) ∧
  (new_dec_vs (Dlet p e) = pat_bindings p []) ∧
  (new_dec_vs (Dletrec funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_vs_def"]

val _ = Parse.overload_on("new_decs_vs",``λdecs. FLAT (REVERSE (MAP new_dec_vs decs))``)

val FV_decs_def = Define`
  (FV_decs [] = {}) ∧
  (FV_decs (d::ds) = FV_dec d ∪ ((FV_decs ds) DIFF (set (MAP Short (new_dec_vs d)))))`

val FV_top_def = Define`
  (FV_top (Tdec d) = FV_dec d) ∧
  (FV_top (Tmod mn _ ds) = FV_decs ds)`
val _ = export_rewrites["FV_top_def"]

val free_vars_dec_i2_def = Define`
  free_vars_dec_i2 (Dlet_i2 n e) = free_vars_i2 e ∧
  free_vars_dec_i2 (Dletrec_i2 defs) = free_vars_i2 (Letrec_i2 defs (Lit_i2 ARB))`
val _ = export_rewrites["free_vars_dec_i2_def"]

(*
val new_dec_i2_vs_def = Define`
  (new_dec_i2_vs (Dlet_i2 n e) = []) ∧
  (new_dec_i2_vs (Dletrec_i2 funs) = MAP FST funs)`
val _ = export_rewrites["new_dec_i2_vs_def"]
*)

val free_vars_decs_i2_def = Define`
  free_vars_decs_i2 ls = free_vars_i2 (decs_to_i3 0 ls)`

val free_vars_prompt_i2_def = Define`
  free_vars_prompt_i2 (Prompt_i2 ds) = free_vars_decs_i2 ds`
val _ = export_rewrites["free_vars_prompt_i2_def"]

val free_vars_i2_init_globals = store_thm("free_vars_i2_init_globals",
  ``∀ls n. free_vars_i2 (init_globals ls n) = set ls``,
  Induct >> simp[init_globals_def,EXTENSION])
val _ = export_rewrites["free_vars_i2_init_globals"]

val pats_bindings_i2_MAP_Pvar_i2 = store_thm("pats_bindings_i2_MAP_Pvar_i2",
  ``∀ls ly. set (pats_bindings_i2 (MAP Pvar_i2 ls) ly) = set ls ∪ set ly``,
  Induct >> simp[pat_bindings_i2_def,EXTENSION] >> metis_tac[])

val free_vars_i2_init_global_funs = store_thm("free_vars_i2_init_global_funs",
  ``∀ls n. free_vars_i2 (init_global_funs n ls) = BIGUNION (set (MAP (λ(f,x,e). free_vars_i2 (Fun_i2 x e)) ls))``,
  Induct >> simp[FORALL_PROD,init_global_funs_def])

val free_vars_i2_decs_to_i3 = store_thm("free_vars_i2_decs_to_i3",
  ``∀l m. free_vars_i2 (decs_to_i3 m l) = free_vars_decs_i2 l``,
  Induct >> simp[decs_to_i3_def,free_vars_decs_i2_def] >>
  Cases >> simp[pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2] >>
  simp[free_vars_i2_init_global_funs])

val free_vars_i2_prompt_to_i3 = store_thm("free_vars_i2_prompt_to_i3",
  ``∀x s m p n e.
    prompt_to_i3 x s m p = (n,e) ⇒
    free_vars_i2 e = free_vars_prompt_i2 p``,
  rw[prompt_to_i3_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  fs[LET_THM] >> rw[pat_bindings_i2_def] >>
  rw[free_vars_i2_decs_to_i3])

val free_vars_decs_i1_def = Define`
  free_vars_decs_i1 ds = free_vars_decs_i2 (SND(SND(decs_to_i2 ARB ds)))`

val free_vars_prompt_i1_def = Define`
  free_vars_prompt_i1 (Prompt_i1 mn decs) = free_vars_decs_i1 decs`

val free_vars_decs_i2_decs_to_i2_any = store_thm("free_vars_decs_i2_decs_to_i2_any",
  ``∀l a b. free_vars_decs_i2 (SND(SND (decs_to_i2 a l))) =
            free_vars_decs_i2 (SND(SND (decs_to_i2 b l)))``,
  Induct_on`l`>>simp[decs_to_i2_def] >>
  Cases >> simp[UNCURRY] >>
  fs[free_vars_decs_i2_def,decs_to_i3_def] >>
  simp[pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2] >>
  fs[free_vars_i2_decs_to_i3,free_vars_i2_init_global_funs] >>
  fs[EXTENSION,funs_to_i2_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF] >>
  metis_tac[])

val free_vars_prompt_to_i2 = store_thm("free_vars_prompt_to_i2",
  ``∀x p y z p2.
    prompt_to_i2 x p = (y,z,p2) ⇒
    free_vars_prompt_i2 p2 = free_vars_prompt_i1 p``,
  Cases_on`p`>>rw[prompt_to_i2_def,LET_THM,free_vars_prompt_i1_def] >>
  fs[UNCURRY] >> rw[free_vars_decs_i1_def] >>
  metis_tac[free_vars_decs_i2_decs_to_i2_any])

val free_vars_list_i1_MAP_Var_local_i1 = store_thm("free_vars_list_i1_MAP_Var_local_i1",
  ``∀ls. free_vars_list_i1 (MAP Var_local_i1 ls) = set ls``,
  Induct >> simp[EXTENSION])

val alloc_defs_GENLIST = store_thm("alloc_defs_GENLIST",
  ``∀n ls. alloc_defs n ls = ZIP(ls,GENLIST(λx. x + n)(LENGTH ls))``,
  Induct_on`ls`>>simp[alloc_defs_def,GENLIST_CONS] >>
  simp[combinTheory.o_DEF,ADD1])

val free_vars_dec_to_i1 = store_thm("free_vars_dec_to_i1",
  ``∀n a m e d. free_vars_decs_i1 [SND (SND (dec_to_i1 n a m e d))] =
                {x | Short x ∈ FV_dec d} DIFF FDOM e``,
  Cases_on`d`>>
  simp[free_vars_decs_i1_def,dec_to_i1_def,
       decs_to_i2_def,free_vars_decs_i2_def,decs_to_i3_def,
       pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2,
       free_vars_list_i1_MAP_Var_local_i1,
       funs_to_i1_MAP,free_vars_i2_init_global_funs,
       funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,
       FV_defs_MAP,PULL_EXISTS] >>
  simp[Once EXTENSION,PULL_EXISTS,MEM_MAP,FST_triple,alloc_defs_GENLIST] >>
  simp[(Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST|>SIMP_RULE(srw_ss())[LAMBDA_PROD])] >>
  simp[FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MAP_ZIP] >>
  rw[MEM_MAP,PULL_EXISTS] >>
  metis_tac[])

val free_vars_decs_to_i1 = store_thm("free_vars_decs_to_i1",
  ``∀n a m e d. free_vars_decs_i1 (SND (SND (decs_to_i1 n a m e d))) =
                {x | Short x ∈ FV_decs d} DIFF FDOM e``,
  Induct_on`d`>- (
    simp[FV_decs_def,decs_to_i1_def,free_vars_decs_i1_def,free_vars_decs_i2_def] >>
    simp[decs_to_i2_def,decs_to_i3_def] ) >>
  simp[FV_decs_def,decs_to_i1_def,UNCURRY,MEM_MAP] >>
  Cases >> simp[dec_to_i1_def] >>
  fs[free_vars_decs_i1_def,free_vars_decs_i2_def] >>
  fs[free_vars_i2_decs_to_i3] >>
  simp[decs_to_i1_def,decs_to_i2_def] >>
  simp[UNCURRY] >>
  fs[free_vars_decs_i2_def,decs_to_i3_def] >> simp[] >>
  fs[free_vars_i2_decs_to_i3,pat_bindings_i2_def,pats_bindings_i2_MAP_Pvar_i2] >>
  simp[(Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST|>SIMP_RULE(srw_ss())[LAMBDA_PROD])] >>
  simp[alloc_defs_GENLIST,free_vars_list_i1_MAP_Var_local_i1,FDOM_FUPDATE_LIST,
       MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MAP_ZIP,free_vars_i2_init_global_funs] >>
  TRY ( metis_tac[free_vars_decs_i2_decs_to_i2_any] ) >>
  simp[Once EXTENSION] >- metis_tac[] >>
  simp[funs_to_i1_MAP,funs_to_i2_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY
      ,FDOM_FUPDATE_LIST,ETA_AX,MAP_ZIP,FST_triple,MAP_REVERSE,MEM_MAP,PULL_EXISTS] >>
  simp[FV_defs_MAP,PULL_EXISTS,UNCURRY] >>
  metis_tac[])

val FV_top_to_i1 = store_thm("FV_top_to_i1",
  ``∀n m e t x y z p. top_to_i1 n m e t = (x,y,z,p) ⇒
      free_vars_prompt_i1 p = {x | Short x ∈ FV_top t} DIFF FDOM e``,
  Cases_on`t`>>simp[top_to_i1_def,UNCURRY] >>
  simp[free_vars_prompt_i1_def,free_vars_dec_to_i1] >>
  simp[free_vars_decs_to_i1])

val IS_SOME_EXISTS = store_thm("IS_SOME_EXISTS",
  ``∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x``,
  Cases >> simp[])

val global_env_inv_inclusion = store_thm("global_env_inv_inclusion",
  ``∀genv mods tops menv s env.
     global_env_inv genv mods tops menv s env ⇒
     set (MAP FST env) DIFF s ⊆ FDOM tops ∧
     set (MAP FST menv) ⊆ FDOM mods``,
  rw[Once v_to_i1_cases,SUBSET_DEF] >>
  TRY (
    (libPropsTheory.lookup_notin
     |> SPEC_ALL |> EQ_IMP_RULE |> fst
     |> CONTRAPOS
     |> SIMP_RULE std_ss []
     |> imp_res_tac) >>
    fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
    res_tac >> fs[FLOOKUP_DEF] >> NO_TAC) >>
  last_x_assum mp_tac >>
  simp[Once v_to_i1_cases] >> strip_tac >>
  (libPropsTheory.lookup_notin
   |> SPEC_ALL |> EQ_IMP_RULE |> fst
   |> CONTRAPOS
   |> SIMP_RULE std_ss []
   |> imp_res_tac) >>
  fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
  res_tac >> fs[FLOOKUP_DEF] >> NO_TAC)

val genv_to_pat_closed = prove(
  ``∀genv2.
    EVERY (OPTION_EVERY closed_exh) genv2 ⇒
    EVERY (OPTION_EVERY closed_pat)
      (MAP (OPTION_MAP v_to_pat) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_pat_closed])

val genv_to_exh_closed = prove(
  ``∀exh genv2.
    EVERY (OPTION_EVERY closed_i2) genv2 ⇒
    EVERY (OPTION_EVERY closed_exh)
      (MAP (OPTION_MAP (v_to_exh exh)) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_exh_closed])

val genv_to_i2_closed = store_thm("genv_to_i2_closed",
  ``∀g x y. genv_to_i2 g x y ⇒ EVERY (OPTION_EVERY closed_i1) x ⇒ EVERY (OPTION_EVERY closed_i2) y``,
  ho_match_mp_tac genv_to_i2_ind >> simp[] >>
  metis_tac[v_to_i2_closed])

val global_env_inv_closed = store_thm("global_env_inv_closed",
  ``∀genv mods tops menv s env.
    global_env_inv genv mods tops menv s env ∧
    EVERY closed (MAP SND env) ∧
    EVERY closed (MAP SND (FLAT (MAP SND menv))) ∧
    (∀n. n < LENGTH genv ∧ IS_SOME (EL n genv) ⇒
         (∃x. x ∉ s ∧ IS_SOME (lookup x env) ∧ FLOOKUP tops x = SOME n) ∨
         (∃mn ee e x.
           lookup mn menv = SOME ee ∧
           IS_SOME (lookup x ee) ∧
           FLOOKUP mods mn = SOME e ∧
           FLOOKUP e x = SOME n))
    ⇒
    EVERY (OPTION_EVERY closed_i1) genv``,
  rw[Once v_to_i1_cases] >>
  rw[EVERY_MEM,MEM_EL] >>
  Cases_on`EL n genv`>>fs[] >>
  first_x_assum(qspec_then`n`mp_tac) >>
  simp[] >> simp[IS_SOME_EXISTS] >>
  strip_tac >- (
    res_tac >>
    rator_x_assum`global_env_inv_flat`mp_tac >>
    simp[Once v_to_i1_cases] >> rw[] >>
    res_tac >> fs[] >> rw[] >> fs[] >>
    fs[EVERY_MEM,PULL_EXISTS] >>
    metis_tac[v_to_i1_closed,libPropsTheory.lookup_in] ) >>
  first_x_assum(qspec_then`mn`mp_tac) >> simp[] >>
  simp[Once v_to_i1_cases] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  simp[] >>
  imp_res_tac libPropsTheory.lookup_in >>
  imp_res_tac libPropsTheory.lookup_in2 >>
  fs[EVERY_MEM,MAP_FLAT,MEM_MAP,PULL_EXISTS,MEM_FLAT] >>
  metis_tac[v_to_i1_closed])

(* misc *)

val code_env_cd_append = store_thm("code_env_cd_append",
  ``∀code cd code'. code_env_cd code cd ∧ ALL_DISTINCT (FILTER is_Label (code ++ code')) ⇒ code_env_cd (code ++ code') cd``,
  rw[] >> PairCases_on`cd` >>
  fs[code_env_cd_def] >>
  HINT_EXISTS_TAC>>simp[]>>
  HINT_EXISTS_TAC>>simp[])

val FOLDL_emit_thm = store_thm("FOLDL_emit_thm",
  ``∀ls s. FOLDL (λs i. s with out := i::s.out) s ls = s with out := REVERSE ls ++ s.out``,
  Induct >> simp[compiler_result_component_equality])

(* label_closures *)

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀ez j e. (no_labs e) ∧ set (free_vars e) ⊆ count ez ⇒
     let (e',j') = label_closures ez j e in
     (j' = j + (LENGTH (free_labs ez e'))) ∧
     (MAP (FST o FST o SND) (free_labs ez e') = (GENLIST ($+ j) (LENGTH (free_labs ez e')))) ∧
     set (free_vars e') ⊆ set (free_vars e) ∧
     all_labs e' ∧ EVERY good_cd (free_labs ez e') ∧
     syneq_exp ez ez $= e e') ∧
    (∀ez j es.
     (no_labs_list es) ∧ set (free_vars_list es) ⊆ count ez ⇒
     let (es',j') = label_closures_list ez j es in
     (j' = j + LENGTH (free_labs_list ez es')) ∧
     (MAP (FST o FST o SND) (free_labs_list ez es') = (GENLIST ($+ j) (LENGTH (free_labs_list ez es')))) ∧
     set (free_vars_list es') ⊆ set (free_vars_list es) ∧
     all_labs_list es' ∧ EVERY good_cd (free_labs_list ez es') ∧
     EVERY2 (syneq_exp ez ez $=) es es') ∧
    (∀ez j nz k defs ds0 ls0.
     (no_labs_defs (ls0 ++ MAP ($, NONE) defs)) ∧
     set (free_vars_defs nz (MAP ($, NONE) defs)) ⊆ count ez ∧
     (LENGTH ds0 = k) ∧ (LENGTH defs = nz - k) ∧ k ≤ nz ∧ (LENGTH ls0 = k) ∧
     syneq_defs ez ez $= (ls0 ++ MAP ($, NONE) defs) (ds0 ++ MAP ($, NONE) defs) (λv1 v2. v1 < nz ∧ (v2 = v1))
     ⇒
     let (defs',j') = label_closures_defs ez j nz k defs in
     (j' = j + LENGTH (free_labs_defs ez nz k defs')) ∧
     (MAP (FST o FST o SND) (free_labs_defs ez nz k defs') = GENLIST ($+ j) (LENGTH (free_labs_defs ez nz k defs'))) ∧
     set (free_vars_defs nz defs') ⊆ set (free_vars_defs nz (MAP ($, NONE) defs)) ∧
     (LENGTH defs' = LENGTH defs) ∧
     all_labs_defs defs' ∧
     EVERY good_cd (free_labs_defs ez nz k defs') ∧
     syneq_defs ez ez $= (ls0 ++ (MAP ($, NONE) defs)) (ds0 ++ defs') (λv1 v2. v1 < nz ∧ (v2 = v1)))``,
  ho_match_mp_tac label_closures_ind >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    `set (free_vars e2) ⊆ count (ez + 1)` by (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
      Cases >> rw[ADD1] >>
      res_tac >>
      disj2_tac >> HINT_EXISTS_TAC >>
      fsrw_tac[ARITH_ss][] ) >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (rw[] >> rw[syneq_exp_refl]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fs[LET_THM,UNCURRY] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >>
    rw[Once syneq_exp_cases] >> rfs[]) >>
  strip_tac >- (
    Cases_on`bd` >- (
      ntac 2 gen_tac >>
      map_every qx_gen_tac[`e1`,`e2`] >>
      rpt strip_tac >> fs[] >>
      `set (free_vars e2) ⊆ count (ez + 1)` by (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
        Cases>>fsrw_tac[ARITH_ss][] ) >> fs[] >>
      qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
      qabbrev_tac`q = label_closures (ez+1) (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
      simp[LIST_EQ_REWRITE] >>
      conj_tac >- (
        gen_tac >>
        Cases_on`x<LENGTH (free_labs ez p0)`>>
        lrw[EL_APPEND1,EL_APPEND2] ) >>
      rfs[] >>
      conj_tac >- (
        fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] >>
        Cases >> rw[ADD1] >>
        res_tac >>
        disj2_tac >> HINT_EXISTS_TAC >>
        fsrw_tac[ARITH_ss][] ) >>
      simp[Once syneq_exp_cases] >>
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
      HINT_EXISTS_TAC >>
      simp[]) >>
    simp[] >>
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    simp[Once syneq_exp_cases] >>
    qabbrev_tac`p = label_closures ez j e1` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >>
    PairCases_on`q`>>fs[LET_THM] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,PRE_SUB1] ) >>
  strip_tac >- (
    rpt strip_tac >>
    simp[] >>
    `FILTER (IS_NONE o FST) defs = defs` by (
      simp[FILTER_EQ_ID] >>
      fs[FLAT_EQ_NIL,EVERY_MAP] >>
      fs[EVERY_MEM,FORALL_PROD] >>
      qx_gen_tac`z` >> rpt strip_tac >>
      res_tac >> Cases_on`z`>>fs[] ) >>
    full_simp_tac std_ss [LET_THM] >>
    full_simp_tac std_ss [FILTER_EQ_ID,LENGTH_MAP] >>
    qabbrev_tac`p = label_closures_defs ez j (LENGTH defs) 0 (MAP SND defs)` >>
    PairCases_on`p`>>
    `no_labs e`by fs[] >>
    `set (free_vars e) ⊆ count (ez + LENGTH defs)` by (
      qpat_assum`set (free_vars X) ⊆ Y`mp_tac >>
      rpt (pop_assum kall_tac) >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,LET_THM] >>
      srw_tac[ARITH_ss][ADD1] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    full_simp_tac std_ss [] >>
    qabbrev_tac`q = label_closures (ez + LENGTH defs) p1 e` >>
    PairCases_on`q` >>
    full_simp_tac std_ss [] >>
    `MAP ($, NONE) (MAP SND defs) = defs` by (
      fs[EVERY_MEM] >>
      lrw[MAP_MAP_o] >>
      CONV_TAC(RAND_CONV(REWRITE_CONV[Once (CONJUNCT2 (GSYM MAP_ID)),SimpRHS])) >>
      lrw[MAP_EQ_f,FORALL_PROD] >> res_tac >> fs[]) >>
    full_simp_tac std_ss [] >>
    first_x_assum(qspecl_then[`[]`,`[]`]mp_tac) >>
    simp[syneq_defs_refl,EVERY_MAP] >>
    fs[LET_THM] >>
    strip_tac >>
    fsrw_tac[ETA_ss][] >>
    rfs[] >> simp[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs_defs ez (LENGTH defs) 0 p0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,free_vars_defs_MAP] >>
      gen_tac >> strip_tac >>
      disj2_tac >>
      qexists_tac`m` >>
      simp[] ) >>
    simp[Once syneq_exp_cases] >>
    HINT_EXISTS_TAC >> simp[] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  strip_tac >- (
    ntac 3 gen_tac >>
    map_every qx_gen_tac[`e`,`es`] >>
    rpt strip_tac >>
    qabbrev_tac`p = label_closures ez j e` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >> PairCases_on`q`>>fs[] >>
    fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >>
      Cases_on`x<LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    rfs[] >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    rw[] >> fs[LET_THM] >> rfs[] >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`p2`,`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2]) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    map_every qx_gen_tac[`e1`,`e2`,`e3`] >>
    rpt strip_tac >> fs[] >>
    qabbrev_tac`p = label_closures ez j e1` >> PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures ez (j + LENGTH (free_labs ez p0)) e2` >> PairCases_on`q`>>fs[] >>
    qabbrev_tac`r = label_closures ez (j + LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)) e3` >> PairCases_on`r`>>fs[] >>
    simp[LIST_EQ_REWRITE] >>
    conj_tac >- (
      gen_tac >> strip_tac >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] >>
      Cases_on`x < LENGTH (free_labs ez p0) + LENGTH (free_labs ez q0)` >>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      rfs[] >>
      fsrw_tac[DNF_ss,ARITH_ss][SUBSET_DEF,MEM_GENLIST] ) >>
    simp[Once syneq_exp_cases]) >>
  strip_tac >- (
    simp[] >> simp[Once syneq_exp_cases] ) >>
  strip_tac >- simp[] >>
  strip_tac >- (
    rpt strip_tac >>
    fs[] >>
    qabbrev_tac`p = label_closures ez j e` >>
    PairCases_on`p`>>fs[LET_THM] >>
    qabbrev_tac`q = label_closures_list ez (j + LENGTH (free_labs ez p0)) es` >>
    PairCases_on`q`>>fs[] >> simp[] >> rfs[] >>
    conj_tac >- (
      lrw[LIST_EQ_REWRITE] >>
      Cases_on`x < LENGTH (free_labs ez p0)`>>
      lrw[EL_APPEND1,EL_APPEND2] ) >>
    conj_tac >- (
      fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  strip_tac >- (
    simp[] >> rw[FUNION_FEMPTY_2] >>
    fs[LENGTH_NIL]) >>
  rpt gen_tac >> rpt strip_tac >>
  full_simp_tac (std_ss++ARITH_ss) [] >>
  last_x_assum mp_tac >>
  last_x_assum mp_tac >>
  simp[] >> ntac 2 strip_tac >>
  Q.PAT_ABBREV_TAC`r = bind_fv X Y Z` >>
  PairCases_on`r`>>fs[] >>
  Q.PAT_ABBREV_TAC`ezz:num = az + (X + (Y + 1))` >>
  qabbrev_tac`p = label_closures ezz (j+1) r3` >>
  PairCases_on`p` >> full_simp_tac std_ss [] >>
  qabbrev_tac`q = label_closures_defs ez p1 nz (k+1) defs` >>
  PairCases_on`q` >> full_simp_tac std_ss [] >>
  `no_labs r3` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] ) >>
  `set (free_vars r3) ⊆ count ezz` by (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    first_x_assum(qspec_then`[]`kall_tac) >>
    qpat_assum`P⇒Q`kall_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    srw_tac[ARITH_ss][] >- (
      qho_match_abbrev_tac`(the n (find_index x ls n)) < y` >>
      qho_match_abbrev_tac`P (the n (find_index x ls n))` >>
      ho_match_mp_tac the_find_index_suff >>
      simp[Abbr`P`,Abbr`x`,Abbr`ls`,MEM_FILTER,ADD1,MEM_GENLIST,Abbr`n`,Abbr`y`] >>
      rw[] >>
      qmatch_abbrev_tac`m < A + B` >>
      Cases_on`m=A`>>fsrw_tac[ARITH_ss][]>>
      Cases_on`B=0`>>fsrw_tac[ARITH_ss][]>>
      fs[LENGTH_NIL_SYM,FILTER_EQ_NIL,EVERY_MEM,QSORT_MEM,markerTheory.Abbrev_def] >>
      res_tac >> fsrw_tac[ARITH_ss][]) >>
    qho_match_abbrev_tac`(the 0 (find_index x ls n)) < y` >>
    qho_match_abbrev_tac`P (the 0 (find_index x ls n))` >>
    ho_match_mp_tac the_find_index_suff >>
    `n ≤ nz` by (
      unabbrev_all_tac >>
      simp[GSYM ADD1] >>
      simp[GSYM LESS_EQ] >>
      qmatch_abbrev_tac`LENGTH (FILTER P ls) < nz` >>
      `nz = LENGTH ls` by rw[Abbr`ls`] >> pop_assum SUBST1_TAC >>
      match_mp_tac LENGTH_FILTER_LESS >>
      simp[Abbr`P`,Abbr`ls`,EXISTS_MEM,MEM_GENLIST] >>
      qexists_tac`LENGTH ls0` >>
      simp[] ) >>
    reverse conj_tac >- (
      unabbrev_all_tac >>
      simp[MEM_MAP,MEM_FILTER,sortingTheory.QSORT_MEM] >>
      qexists_tac`v` >> simp[] ) >>
    simp[Abbr`P`,Abbr`y`] >>
    qx_gen_tac`m`>>strip_tac >>
    qmatch_abbrev_tac`m + n < l1 + l2` >>
    `l2 = LENGTH ls + 1` by rw[Abbr`l2`,Abbr`ls`] >> rw[] >>
    qsuff_tac`n ≤ l1 + 1` >- DECIDE_TAC >>
    simp[Abbr`n`]) >>
  full_simp_tac std_ss [LET_THM] >>
  Q.PAT_ABBREV_TAC`cd:def = (SOME X,az,p0)` >>
  last_x_assum(qspecl_then[`ds0++[cd]`,`ls0++[(NONE,az,b)]`]mp_tac) >>
  discharge_hyps >- (
    simp[] >>
    rator_x_assum`syneq_defs`mp_tac >>
    simp[Once syneq_exp_cases] >>
    simp[EVERY_MAP] >> strip_tac >>
    simp[Once syneq_exp_cases,EVERY_MAP] >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >> simp[] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    Cases_on`v < k`>>simp[EL_APPEND1,EL_APPEND2,ADD1,EL_MAP] >- (
      strip_tac >>
      ntac 2 (first_x_assum (mp_tac o SYM)) >>
      ntac 2 strip_tac >>
      fsrw_tac[ARITH_ss][ADD1] ) >>
    Cases_on`v=k` >- (
      simp[Abbr`cd`] >> strip_tac >>
      simp[syneq_cb_aux_def] >>
      fsrw_tac[ARITH_ss][ADD1] >>
      simp[syneq_cb_aux_def] >>
      conj_asm1_tac >- (
        fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
        simp[EVERY_MEM,MEM_MAP,MEM_FILTER,QSORT_MEM,MEM_FILTER,MEM_GENLIST] >>
        simp[GSYM LEFT_FORALL_IMP_THM] >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        qpat_assum`Y ⊆ count ez` mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        metis_tac[] ) >>
      qmatch_abbrev_tac`syneq_exp z1 ezz V b p0` >>
      qsuff_tac`syneq_exp z1 ezz V b r3` >- (
        strip_tac >>
        `V = $= O V` by metis_tac[Id_O] >> pop_assum SUBST1_TAC >>
        match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
        PROVE_TAC[] ) >>
      qpat_assum`Abbrev(X = bind_fv A Y Z)`mp_tac >>
      simp[bind_fv_def,markerTheory.Abbrev_def] >> rw[] >>
      match_mp_tac mkshift_thm >>
      simp[Abbr`z1`,Abbr`ezz`] >>
      conj_tac >- simp[Abbr`V`,syneq_cb_V_def] >>
      reverse conj_tac >- (
        qpat_assum`Y ⊆ count ez`mp_tac >>
        qpat_assum`Y ⊆ count ez`mp_tac >>
        simp[SUBSET_DEF,GSYM LEFT_FORALL_IMP_THM] >>
        srw_tac[DNF_ss,ARITH_ss][NOT_LESS] >>
        Cases_on`az + nz ≤ x`>>simp[]) >>
      gen_tac >> strip_tac >>
      reverse conj_tac >- (
        rw[] >- (
          qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
          qunabbrev_tac`X` >>
          qho_match_abbrev_tac`P (the c (find_index a w c))` >>
          match_mp_tac the_find_index_suff >>
          reverse conj_tac >- (
            unabbrev_all_tac >>
            fs[SUBSET_DEF] >>
            simp[MEM_FILTER,MEM_GENLIST] ) >>
          simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
        qho_match_abbrev_tac`the 0 (find_index a w c) < X` >>
        qunabbrev_tac`X` >>
        qho_match_abbrev_tac`P (the 0 (find_index a w c))` >>
        match_mp_tac the_find_index_suff >>
        reverse conj_tac >- (
          unabbrev_all_tac >>
          simp[MEM_MAP,MEM_FILTER,QSORT_MEM] >>
          qexists_tac`x`>>simp[]) >>
        simp[Abbr`w`,Abbr`c`,Abbr`P`]) >>
      Q.PAT_ABBREV_TAC`envs:num list = MAP X (FILTER Y Z)` >>
      `¬(x < az + nz) ⇒ MEM (x-(az+nz)) envs` by (
        simp[Abbr`envs`,MEM_MAP,MEM_FILTER,QSORT_MEM] >>
        strip_tac >>
        qexists_tac`x` >> simp[] ) >>
      Q.PAT_ABBREV_TAC`recs = LENGTH ls0::X` >>
      `x < az + nz ⇒ MEM (x - az) recs` by (
        simp[Abbr`recs`,MEM_FILTER,MEM_GENLIST] ) >>
      simp[Abbr`V`] >>
      reverse(rw[]) >- (
        fs[] >>
        simp[syneq_cb_V_def] >>
        Q.PAT_ABBREV_TAC`rz = LENGTH (FILTER X Y) + 1` >>
        Q.ISPECL_THEN[`envs`,`x-(az+nz)`,`rz`]mp_tac find_index_MEM >>
        simp[] >> disch_then strip_assume_tac >> simp[] >>
        simp[Abbr`rz`] ) >>
      simp[syneq_cb_V_def] >> fs[] >>
      Q.ISPECL_THEN[`recs`,`x-az`,`0:num`]mp_tac find_index_MEM >>
      simp[] >> disch_then strip_assume_tac >> simp[] >>
      Cases_on`i=0` >- (
        simp[] >> fs[Abbr`recs`]) >>
      simp[] >>
      qpat_assum`EL X Y = x - def0`mp_tac >>
      simp[Abbr`recs`,EL_CONS,PRE_SUB1] >>
      fsrw_tac[ARITH_ss][]) >>
    lrw[EL_CONS] >>
    ntac 2 (qpat_assum`X = Y`(mp_tac o SYM)) >>
    simp[PRE_SUB1,EL_MAP] >>
    Q.PAT_ABBREV_TAC`p = EL X defs` >>
    PairCases_on`p` >>
    simp[syneq_cb_aux_def] >>
    ntac 2 strip_tac >>
    fsrw_tac[ARITH_ss][] >> rw[] >> fs[] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `LENGTH defs + (LENGTH ls0 + 1) = nz` by simp[] >>
    pop_assum SUBST1_TAC >>
    match_mp_tac (MP_CANON(CONJUNCT1 syneq_exp_mono_V)) >>
    HINT_EXISTS_TAC >>
    simp[]) >>
  simp[] >> strip_tac >>
  simp[Abbr`cd`,ADD1]>>
  conj_tac >- (
    fsrw_tac[ARITH_ss][] >>
    lrw[LIST_EQ_REWRITE,EL_CONS,ADD1] >>
    Cases_on`x=0` >> lrw[EL_CONS,PRE_SUB1] >>
    Cases_on`x < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2] >>
    Cases_on `x-1 < LENGTH (free_labs ezz p0)` >>
    lrw[EL_APPEND1,EL_APPEND2]) >>
  conj_tac >- (
    rev_full_simp_tac std_ss [] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] ) >>
  reverse conj_tac >- (
    metis_tac[CONS_APPEND,APPEND_ASSOC] ) >>
  simp[good_cd_def] >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    simp[EVERY_MAP,EVERY_FILTER] >>
    simp[EVERY_MEM,QSORT_MEM] >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    qpat_assum`Y ⊆ count ez` mp_tac >>
    srw_tac[DNF_ss][SUBSET_DEF] >>
    res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    fs[bind_fv_def,LET_THM,markerTheory.Abbrev_def] >>
    qpat_assum`set (free_vars p0) ⊆ X`mp_tac >>
    simp[SUBSET_DEF] >> strip_tac >>
    gen_tac >> strip_tac >>
    first_x_assum(qspec_then`x`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`v<az`>>fsrw_tac[ARITH_ss][]>>
    Cases_on`v<az+nz`>>fsrw_tac[ARITH_ss][]>- (
      qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
      qho_match_abbrev_tac`P (the n (find_index a ls n))` >>
      match_mp_tac the_find_index_suff >>
      simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] ) >>
    rw[] >>
    qho_match_abbrev_tac`the 0 (find_index a ls n) < X` >>
    qho_match_abbrev_tac`P (the 0 (find_index a ls n))` >>
    match_mp_tac the_find_index_suff >>
    simp[Abbr`ls`,Abbr`P`,Abbr`X`,MEM_FILTER,MEM_GENLIST,Abbr`n`,Abbr`a`,MEM_MAP,QSORT_MEM] >>
    HINT_EXISTS_TAC >> simp[] ) >>
  map_every qexists_tac[`b`,`r3`] >>
  simp[])

(* compile_code_env *)

val FOLDL_cce_aux_thm = store_thm("FOLDL_cce_aux_thm",
  ``∀c s. let s' = FOLDL cce_aux s c in
     ALL_DISTINCT (MAP (FST o FST) c) ∧
     EVERY (combin$C $< s.next_label) (MAP (FST o FST) c)
      ⇒
     ∃code.
     (s'.out = REVERSE code ++ s.out) ∧
     (s.next_label ≤ s'.next_label) ∧
     ALL_DISTINCT (FILTER is_Label code) ∧
     EVERY (λn. MEM n (MAP (FST o FST) c) ∨ between s.next_label s'.next_label n)
       (MAP dest_Label (FILTER is_Label code)) ∧
     (EVERY all_labs (MAP (SND o SND) c) ⇒ ∀l. uses_label code l ⇒
       MEM (Label l) code ∨ MEM l (MAP (FST o FST o SND) (FLAT (MAP (λ(p,p3,p4). free_labs (LENGTH (FST(SND p))) p4) c)))) ∧
     (∀l. MEM l (MAP (FST o FST) c) ⇒ MEM (Label l) code) ∧
     ∃cs.
     ∀i. i < LENGTH c ⇒ let ((l,ccenv,ce),(az,body)) = EL i c in
         s.next_label ≤ (cs i).next_label ∧
         (∀j. j < i ⇒ (cs j).next_label ≤ (cs i).next_label) ∧
         ∃cc. ((compile (MAP CTEnv ccenv) (TCTail az 0) 0 (cs i) body).out = cc ++ (cs i).out) ∧
              l < (cs i).next_label ∧
              ∃bc0 bc1. (code = bc0 ++ Label l::REVERSE cc ++ bc1) ∧
                        EVERY (combin$C $< (cs i).next_label o dest_Label)
                          (FILTER is_Label bc0)``,
   Induct >- ( simp[Once SWAP_REVERSE] ) >>
   simp[] >>
   qx_gen_tac`p`>> PairCases_on`p` >>
   rpt gen_tac >>
   simp[cce_aux_def] >>
   strip_tac >>
   Q.PAT_ABBREV_TAC`s0 = s with out := X::y` >>
   qspecl_then[`MAP CTEnv p1`,`TCTail p3 0`,`0`,`s0`,`p4`]
     strip_assume_tac(CONJUNCT1 compile_append_out) >>
   Q.PAT_ABBREV_TAC`s1 = compile X Y Z A B` >>
   first_x_assum(qspecl_then[`s1`]mp_tac) >>
   simp[] >>
   discharge_hyps >- (
     fsrw_tac[ARITH_ss][EVERY_MEM,Abbr`s0`] >>
     rw[] >> res_tac >> DECIDE_TAC ) >>
   disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
   simp[Abbr`s0`] >>
   simp[Once SWAP_REVERSE] >>
   fs[] >> simp[] >>
   simp[FILTER_APPEND,FILTER_REVERSE,MEM_FILTER,ALL_DISTINCT_REVERSE,ALL_DISTINCT_APPEND] >>
   conj_tac >- (
     rfs[FILTER_APPEND] >>
     fs[EVERY_MAP,EVERY_FILTER,EVERY_REVERSE,between_def] >>
     fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,MEM_MAP] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][]
       >- metis_tac[] >>
     res_tac >> fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     fs[EVERY_MAP,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
     fsrw_tac[DNF_ss][EVERY_MEM,between_def] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >>
     fsrw_tac[ARITH_ss][] ) >>
   conj_tac >- (
     rw[] >>
     Cases_on`l=p0`>>rw[]>>
     Cases_on`MEM (Label l)c0`>>rw[]>>
     Cases_on`MEM (Label l)bc`>>rw[]>>
     fs[uses_label_thm,EXISTS_REVERSE] >>
     metis_tac[] ) >>
   conj_tac >- metis_tac[] >>
   qexists_tac`λi. if i = 0 then (s with out := Label p0::s.out) else cs (i-1)` >>
   Cases >> simp[] >- (
     map_every qexists_tac[`[]`,`c0`] >> simp[] ) >>
   strip_tac >>
   first_x_assum(qspec_then`n`mp_tac) >>
   simp[UNCURRY] >> strip_tac >>
   simp[] >>
   conj_asm1_tac >- ( Cases >> simp[] ) >>
   qexists_tac`Label p0::(REVERSE bc ++ bc0)` >>
   simp[FILTER_APPEND,FILTER_REVERSE,EVERY_REVERSE,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM] >>
   qpat_assum`EVERY X (FILTER is_Label bc0)`mp_tac >>
   qpat_assum`EVERY X (MAP Y (FILTER is_Label bc))`mp_tac >>
   simp[EVERY_FILTER,EVERY_MAP,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
   asm_simp_tac(srw_ss()++ARITH_ss++DNF_ss)[EVERY_MEM] >>
   rw[] >> res_tac >> DECIDE_TAC)

val compile_code_env_thm = store_thm("compile_code_env_thm",
  ``∀ez s e. let s' = compile_code_env s e in
      ALL_DISTINCT (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY (combin$C $< s.next_label) (MAP (FST o FST o SND) (free_labs ez e)) ∧
      EVERY good_cd (free_labs ez e)
      ⇒
      ∃code.
      (s'.out = REVERSE code ++ s.out) ∧
      (s.next_label < s'.next_label) ∧
      ALL_DISTINCT (FILTER is_Label code) ∧
      EVERY (λn. MEM n (MAP (FST o FST o SND) (free_labs ez e)) ∨ between s.next_label s'.next_label n)
        (MAP dest_Label (FILTER is_Label code)) ∧
      (EVERY all_labs (MAP (SND o SND o SND) (free_labs ez e)) ⇒
       ∀l. uses_label code l ⇒ MEM (Label l) code ∨
         MEM l (MAP (FST o FST o SND)
           (FLAT (MAP (λ(p,p3,p4). free_labs (LENGTH (FST (SND p))) p4) (MAP SND (free_labs ez e)))))) ∧
      (∀l. MEM l (MAP (FST o FST o SND) (free_labs ez e)) ⇒ MEM (Label l) code) ∧
      ∀bs bc0 bc1.
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        (∀l1 l2. MEM l1 (MAP dest_Label (FILTER is_Label bc0)) ∧ ((l2 = s.next_label) ∨ MEM l2 (MAP (FST o FST o SND) (free_labs ez e))) ⇒ l1 < l2)
        ⇒
        EVERY (code_env_cd (bc0++code)) (free_labs ez e) ∧
        bc_next bs (bs with pc := next_addr bs.inst_length (bc0++code))``,
  rw[compile_code_env_def] >> rw[] >>
  `MAP SND (free_labs 0 e) = MAP SND (free_labs ez e)` by metis_tac[MAP_SND_free_labs_any_ez] >>
  fs[] >>
  Q.ISPECL_THEN[`MAP SND (free_labs ez e)`,`s''`]mp_tac FOLDL_cce_aux_thm >>
  simp[Abbr`s''`] >>
  discharge_hyps >- (
    fsrw_tac[ARITH_ss][EVERY_MEM,MAP_MAP_o] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  simp[Once SWAP_REVERSE,Abbr`s''''`] >>
  conj_tac >- (
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER] >>
    fs[EVERY_MAP,EVERY_FILTER] >> fs[EVERY_MEM] >>
    spose_not_then strip_assume_tac >> res_tac >>
    fsrw_tac[ARITH_ss][between_def,MEM_MAP,MAP_MAP_o] >>
    res_tac >> rw[] >> DECIDE_TAC ) >>
  conj_tac >- (
    fs[EVERY_MAP,EVERY_FILTER,is_Label_rwt,GSYM LEFT_FORALL_IMP_THM,between_def] >>
    reverse conj_tac >- (disj2_tac >> DECIDE_TAC) >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    rw[] >> res_tac >>
    TRY(metis_tac[]) >>
    disj2_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    rw[] >>
    fs[MAP_MAP_o] >>
    fs[uses_label_thm] >>
    metis_tac[] ) >>
  conj_tac >- fs[MAP_MAP_o] >>
  rpt gen_tac >>
  strip_tac >>
  conj_tac >- (
    fs[EVERY_MEM] >>
    qx_gen_tac`z` >>
    PairCases_on`z` >> strip_tac >>
    simp[code_env_cd_def] >>
    qmatch_assum_abbrev_tac`MEM cd (free_labs ez e)` >>
    `∃i. i < LENGTH (free_labs ez e) ∧ (EL i (free_labs ez e) = cd)` by metis_tac[MEM_EL] >>
    qpat_assum`∀i. P ⇒ Q`(qspec_then`i`mp_tac) >>
    simp[EL_MAP] >>
    simp[Abbr`cd`] >> strip_tac >>
    qexists_tac`cs i`>>simp[] >>
    qexists_tac`bc0++Jump (Lab s.next_label)::bc0'` >>
    simp[] >>
    fs[EVERY_MEM,MEM_MAP,FILTER_APPEND] >>
    fsrw_tac[DNF_ss][] >- (
      rpt strip_tac >> res_tac >> DECIDE_TAC) >>
    rpt strip_tac >> res_tac >> DECIDE_TAC) >>
  `bc_fetch bs = SOME (Jump (Lab s.next_label))` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >> simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bc_state_component_equality,bc_find_loc_def] >>
  match_mp_tac bc_find_loc_aux_append_code >>
  match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  qexists_tac`LENGTH bc0 + 1 + LENGTH c0` >>
  simp[EL_APPEND2,TAKE_APPEND2,FILTER_APPEND,SUM_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER] >>
  fs[EVERY_MAP,EVERY_FILTER,between_def] >>
  fsrw_tac[DNF_ss][EVERY_MEM,is_Label_rwt,MEM_MAP,EXISTS_PROD,FORALL_PROD,MEM_FILTER] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

(* printing *)

val _ = Parse.overload_on("print_bv",``λm. ov_to_string o bv_to_ov m``)
val print_bv_str_def = Define`print_bv_str m t v w = "val "++v++":"++(tystr t v)++" = "++(print_bv m w)++"\n"`

val append_cons_lemma = prove(``ls ++ [x] ++ a::b = ls ++ x::a::b``,lrw[])

val MAP_PrintC_thm = store_thm("MAP_PrintC_thm",
  ``∀ls bs bc0 bc1 bs'.
    bs.code = bc0 ++ (MAP PrintC ls) ++ bc1 ∧
    bs.pc = next_addr bs.inst_length bc0 ∧
    bs' = bs with <| output := bs.output ++ ls; pc := next_addr bs.inst_length (bc0 ++ (MAP PrintC ls))|>
    ⇒
    bc_next^* bs bs'``,
  Induct >- (
    simp[] >> rw[] >>
    simp[Once RTC_CASES1] >> disj1_tac >>
    simp[bc_state_component_equality] ) >>
  simp[] >> rw[] >>
  simp[Once RTC_CASES1] >> disj2_tac >>
  `bc_fetch bs = SOME (PrintC h)` by (
    match_mp_tac bc_fetch_next_addr >>
    qexists_tac`bc0` >>
    simp[] ) >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality,IMPLODE_EXPLODE_I] >>
  qexists_tac`bc0 ++ [PrintC h]` >>
  simp[FILTER_APPEND,SUM_APPEND])

val _ = Parse.overload_on("print_bv_list",``λm t vs ws. FLAT (MAP (UNCURRY (print_bv_str m t)) (ZIP (vs,ws)))``)

val print_envE_cons = store_thm("print_envE_cons",
  ``print_envE types (x::xs) = print_envE types [x]++print_envE types xs``,
  rw[print_envE_def]);

val v_to_ov_exh_def = tDefine"v_to_ov_exh"`
  (v_to_ov_exh m (Litv l) = Litv_exh l) ∧
  (v_to_ov_exh m (Conv c vs) = Conv_exh (m c) (MAP (v_to_ov_exh m) vs)) ∧
  (v_to_ov_exh m (Loc n) = Loc_exh n) ∧
  (v_to_ov_exh m _ = Closure_exh [] "" (Extend_global_exh 0))`
(WF_REL_TAC`measure (v_size o SND)` >>
 gen_tac >> Induct >> simp[v_size_def] >> rw[] >>
 res_tac >> fsrw_tac[ARITH_ss][])
val _ = export_rewrites["v_to_ov_exh_def"]

val print_v_ov = store_thm("print_v_ov",
  ``(∀v m1 m2 sm. ov_to_string (Cv_to_ov m2 sm (v_to_Cv (v_to_pat (v_to_ov_exh m1 v)))) = print_v v)
    ∧ (∀x:all_env. T)
    ∧ (∀x:envC#envE. T)
    ∧ (∀x:envM. T)
    ∧ (∀x:string#envE. T)
    ∧ (∀x:envE. T)
    ∧ (∀x:string#v. T)
    ∧ (∀vs:v list. T)``,
  ho_match_mp_tac(TypeBase.induction_of``:v``) >>
  simp[print_v_def,v_to_Cv_def,printerTheory.ov_to_string_def] >>
  Cases >> simp[printerTheory.ov_to_string_def,print_lit_def] >>
  Cases_on`b`>>simp[printerTheory.ov_to_string_def,print_lit_def])

val print_bv_list_print_envE = store_thm("print_bv_list_print_envE",
  ``∀cm pp vars vs m Cvs bvs types env.
    EVERY2 syneq (MAP (v_to_Cv o v_to_pat o v_to_ov_exh cm) vs) Cvs ∧
    EVERY2 (Cv_bv pp) Cvs bvs ∧ LENGTH vars = LENGTH vs ∧
    set vars ⊆ FDOM types ∧
    env = ZIP(vars,vs)
    ⇒
    print_bv_list m types vars bvs = print_envE types env``,
  ntac 2 gen_tac >>
  Induct >- ( Cases >> simp[print_envE_def] ) >>
  qx_gen_tac`x`>>
  qx_gen_tac`ws`>>
  gen_tac >>
  map_every qx_gen_tac[`wvs`,`wbs`] >>
  ntac 3 strip_tac >>
  `∃v vs. ws = v::vs` by ( Cases_on`ws`>>fs[] ) >>
  `∃Cv Cvs. wvs = Cv::Cvs` by ( Cases_on`wvs`>>fs[EVERY2_EVERY] ) >>
  `∃bv bvs. wbs = bv::bvs` by ( Cases_on`wbs`>>fs[EVERY2_EVERY] ) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[Once print_envE_cons] >>
  first_x_assum(qspecl_then[`vs`,`m`,`Cvs`,`bvs`,`types`]mp_tac) >>
  simp[] >>
  discharge_hyps >- fs[EVERY2_EVERY] >> rw[] >>
  rw[print_envE_def,print_bv_str_def] >>
  fs[EVERY2_EVERY] >>
  imp_res_tac Cv_bv_ov >>
  `bv_to_ov m bv = Cv_to_ov m (FST pp).sm (v_to_Cv (v_to_pat (v_to_ov_exh cm v)))` by
    metis_tac[syneq_ov] >>
  pop_assum SUBST1_TAC >>
  simp[print_v_ov,tystr_def,FLOOKUP_DEF])

val code_labels_ok_MAP_PrintC = store_thm("code_labels_ok_MAP_PrintC",
  ``∀ls. code_labels_ok (MAP PrintC ls)``,
  Induct>>simp[]>>rw[]>>match_mp_tac code_labels_ok_cons>>simp[])
val _ = export_rewrites["code_labels_ok_MAP_PrintC"]

val can_Print_list_EVERY = store_thm("can_Print_list_EVERY",
  ``∀ls. can_Print_list ls = EVERY can_Print ls``,
  Induct >> simp[])
val _ = export_rewrites["can_Print_list_EVERY"]

val compile_print_vals_thm = store_thm("compile_print_vals_thm",
  ``∀vs types map cs. let cs' = compile_print_vals types map vs cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
         ∧ cs'.next_label = cs.next_label
         ∧ EVERY ($~ o is_Label) code ∧
         code_labels_ok code ∧
    ∀bs bc0 bvs.
    bs.code = bc0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ LIST_REL (λv bv. ∃n. FLOOKUP map v = SOME n ∧ el_check n bs.globals = SOME (SOME bv) ∧ can_Print bv) vs bvs
    ⇒
    let bs' = bs with <|pc := next_addr bs.inst_length (bc0++code)
                       ;output := bs.output ++ print_bv_list bs.cons_names types vs bvs|> in
    bc_next^* bs bs'``,
  Induct >> simp[compile_print_vals_def] >- (
    simp[Once SWAP_REVERSE] >> rw[] >>
    simp[Once RTC_CASES1] >>
    simp[bc_state_component_equality] )>>
  simp[FOLDL_emit_thm] >>
  qx_gen_tac`v` >>
  rpt strip_tac >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  first_x_assum(qspecl_then[`types`,`map`,`cs1`]mp_tac) >>
  simp[] >>
  disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE] >>
  simp[EVERY_MAP] >> fs[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd X Y` >>
  qmatch_assum_abbrev_tac`(compile_print_vals types map vs cs1').next_label = X` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  fs[Abbr`cs1'`] >> pop_assum kall_tac >>
  conj_tac >- (
    rpt(match_mp_tac code_labels_ok_cons>>simp[])>>
    match_mp_tac code_labels_ok_append>>simp[IMPLODE_EXPLODE_I]>>
    rpt(match_mp_tac code_labels_ok_append>>simp[]>>(TRY conj_tac)>>TRY(simp[code_labels_ok_def,uses_label_thm]>>NO_TAC))) >>
  rpt gen_tac >>
  strip_tac >>
  fs[IMPLODE_EXPLODE_I] >>
  `bs.code = bc0 ++ (MAP PrintC ("val "++v++":"++tystr types v++" = ")) ++ [Gread n;Print;PrintC(#"\n")] ++ c1` by (
    simp[] ) >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc:=next_addr bs.inst_length (bc0++l1)
                          ;output:=STRCAT bs.output ("val "++v++":"++tystr types v++" = ")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`"val "++v++":"++tystr types v++" = "`>>
    qexists_tac`bc0` >>
    simp[Abbr`l1`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  `bc_fetch bs1 = SOME (Gread n)` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`] >>
    qexists_tac`bc0++l1` >>
    simp[Abbr`l2`] ) >>
  `bc_next^* bs1 (bs1 with <|pc:=next_addr bs.inst_length(bc0++l1++l2)
                            ;output := STRCAT bs1.output (print_bv bs.cons_names bv)++"\n"|>)` by (
    simp[RTC_eq_NRC] >>
    qexists_tac`SUC(SUC(SUC 0))` >>
    simp[NRC] >>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def,EL_APPEND1]>>
    fs[compilerLibTheory.el_check_def] >>
    simp[Abbr`P`]>>
    qho_match_abbrev_tac`∃z. bc_next bs1 z ∧ P z` >>
    `bc_fetch bs1 = SOME Print` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++l1++[HD l2]` >>
      simp[Abbr`bs1`,Abbr`l2`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def]>>
    simp[Abbr`bs1`]>>
    simp[Abbr`P`] >>
    qmatch_abbrev_tac`bc_next bs1 bs2` >>
    `bc_fetch bs1 = SOME (PrintC(#"\n"))` by (
      match_mp_tac bc_fetch_next_addr >>
      qexists_tac`bc0++l1++FRONT l2` >>
      simp[Abbr`bs1`,Abbr`l2`] >>
      simp[FILTER_APPEND,SUM_APPEND] ) >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,Abbr`bs2`,bc_state_component_equality,IMPLODE_EXPLODE_I] >>
    simp[FILTER_APPEND,SUM_APPEND,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_next^* bs bs2` by metis_tac[RTC_TRANSITIVE,transitive_def] >>
  pop_assum mp_tac >>
  rpt(qpat_assum`bc_next^* a Y`kall_tac) >>
  first_x_assum(qspecl_then[`bs2`,`bc0++l1++l2`,`ys`]mp_tac) >>
  simp[Abbr`bs2`,Abbr`bs1`,ADD1] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
  strip_tac >>
  qmatch_abbrev_tac`bc_next^* bs bs2'` >>
  `bs2' = bs2` by (
    simp[Abbr`bs2`,Abbr`bs2'`,bc_state_component_equality,Abbr`l1`] >>
    conj_tac >- (
      simp[SUM_APPEND,FILTER_APPEND] ) >>
    simp[print_bv_str_def]) >>
  metis_tac[RTC_TRANSITIVE,transitive_def] )

val _ = Parse.overload_on("print_ctor",``λx. STRCAT x " = <constructor>\n"``)
val _ = Parse.overload_on("print_ctors",``λls. FLAT (MAP (λ(x,y). print_ctor x) ls)``)

val compile_print_ctors_thm = store_thm("compile_print_ctors_thm",
  ``∀ls cs. let cs' = compile_print_ctors ls cs in
    ∃code. cs'.out = REVERSE code ++ cs.out
      ∧ EVERY ($~ o is_Label) code
      ∧ code_labels_ok code
      ∧ cs'.next_label = cs.next_label ∧
      ∀bs bc0.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ⇒
      let bs' = bs with <|pc := next_addr bs.inst_length bs.code
           ; output := STRCAT bs.output (print_ctors ls)|> in
      bc_next^* bs bs'``,
  Induct >- (
    simp[compile_print_ctors_def,Once SWAP_REVERSE] >>
    rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  simp[compile_print_ctors_def,FOLDL_emit_thm,IMPLODE_EXPLODE_I] >>
  rw[] >>
  Q.PAT_ABBREV_TAC`cs1 = compiler_result_out_fupd x y` >>
  first_x_assum(qspec_then`cs1`mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs1`,Once SWAP_REVERSE,EVERY_MAP] >> fs[] >>
  qmatch_assum_abbrev_tac`(compile_print_ctors ls cs1).next_label = X` >>
  conj_tac >- (
    match_mp_tac code_labels_ok_append >> simp[]>>
    match_mp_tac code_labels_ok_append >> simp[]>>
    rpt(match_mp_tac code_labels_ok_cons >> simp[]) ) >>
  qmatch_abbrev_tac`((compile_print_ctors ls cs1').next_label = X) ∧ Y` >>
  `cs1' = cs1` by (
    simp[Abbr`cs1`,Abbr`cs1'`,compiler_result_component_equality] ) >>
  simp[Abbr`X`,Abbr`Y`] >>
  rpt strip_tac >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ l1 ++ l2 ++ c1` >>
  `bc_next^* bs (bs with <|pc := next_addr bs.inst_length (bc0++l1++l2)
                          ;output := bs.output ++ (x0++" = <constructor>\n")|>)` by (
    match_mp_tac MAP_PrintC_thm >>
    qexists_tac`x0 ++ " = <constructor>\n"` >>
    qexists_tac`bc0` >>
    simp[Abbr`l1`,Abbr`l2`] ) >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  first_x_assum(qspecl_then[`bs1`,`bc0++l1++l2`]mp_tac) >>
  simp[Abbr`bs1`] >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
  qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
  `bs1' = bs1` by (
    simp[Abbr`bs1'`,Abbr`bs1`,bc_state_component_equality] ) >>
  qmatch_abbrev_tac`bc_next^* bs bs3` >>
  `bs2 = bs3` by (
    simp[Abbr`bs3`,bc_state_component_equality,semanticPrimitivesTheory.id_to_string_def] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

val compile_print_dec_thm = store_thm("compile_print_dec_thm",
  ``∀types map d cs. let cs' = compile_print_dec types map d cs in
      ∃code. cs'.out = REVERSE code ++ cs.out
        ∧ EVERY ($~ o is_Label) code
        ∧ cs'.next_label = cs.next_label
        ∧ code_labels_ok code ∧
      ∀bs bc0 bvs.
      bs.code = bc0 ++ code
      ∧ bs.pc = next_addr bs.inst_length bc0
      ∧ LIST_REL
        (λv bv. ∃n. FLOOKUP map v = SOME n ∧ el_check n bs.globals = SOME (SOME bv) ∧ can_Print bv)
        (new_dec_vs d) bvs
      ⇒
      let str =
        case d of
        | Dtype ts => print_envC ([],REVERSE(build_tdefs NONE ts))
        | Dexn cn ts => print_envC ([],[(cn, (LENGTH ts, TypeExn))])
        | d => print_bv_list bs.cons_names types (new_dec_vs d) bvs in
      let bs' = bs with
        <|pc := next_addr bs.inst_length (bc0++code)
         ;output := bs.output ++ str|> in
      bc_next^* bs bs'``,
  Cases_on`d` >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    qspecl_then[`pat_bindings p []`,`types`, `map`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[])
  >- (
    simp[compile_print_dec_def] >>
    rw[] >>
    Q.PAT_ABBREV_TAC`vs:string list = MAP X l` >>
    qspecl_then[`vs`,`types`,`map`,`cs`]mp_tac compile_print_vals_thm >>
    simp[] >> rw[] >> simp[] >> rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`bs`,`bc0`,`bvs`]mp_tac) >>
    `vs = MAP FST l` by (
      simp[Abbr`vs`,MAP_EQ_f,FORALL_PROD] ) >>
    simp[TAKE_LENGTH_ID_rwt])
  >- (
    simp[] >>
    simp[compile_print_dec_def] >>
    Induct_on`l` >- (
      simp[compile_print_types_def,Once SWAP_REVERSE] >>
      simp[print_envC_def,semanticPrimitivesTheory.build_tdefs_def,LENGTH_NIL] >>
      rw[] >> simp[Once RTC_CASES1] >> simp[bc_state_component_equality] ) >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    simp[compile_print_types_def] >>
    gen_tac >>
    qspecl_then[`x2`,`cs`]mp_tac (INST_TYPE[alpha|->``:t list``]compile_print_ctors_thm) >>
    simp[] >>
    disch_then(qx_choosel_then[`c1`]strip_assume_tac) >>
    first_x_assum(qspec_then`compile_print_ctors x2 cs`mp_tac) >>
    simp[] >>
    disch_then(qx_choosel_then[`c2`]strip_assume_tac) >>
    simp[] >>
    simp[Once SWAP_REVERSE] >>
    conj_tac >- (
      simp[code_labels_ok_append]>>simp[] ) >>
    rpt strip_tac >>
    last_x_assum(qspecl_then[`bs with code := bc0 ++ c1`,`bc0`]mp_tac) >>
    simp[] >> strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] ) >>
    first_x_assum(qspecl_then[`bs1 with code := bs.code`]mp_tac) >>
    simp[Abbr`bs1`] >>
    simp[LENGTH_NIL] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    `bs1' = bs1` by (
      simp[Abbr`bs1`,Abbr`bs1'`] ) >>
    qmatch_abbrev_tac`bc_next^* bs bs2'` >>
    `bs2' = bs2` by (
      simp[Abbr`bs2`,Abbr`bs2'`] >>
      simp[bc_state_component_equality] >>
      simp[semanticPrimitivesTheory.build_tdefs_def,print_envC_def] >>
      simp[MAP_MAP_o,combinTheory.o_DEF] >>
      simp[UNCURRY,astTheory.mk_id_def] >>
      simp[LAMBDA_PROD] ) >>
    metis_tac[RTC_TRANSITIVE,transitive_def])
  >- (
    simp[] >>
    simp[compile_print_dec_def] >>
    simp[compile_print_types_def] >>
    rw[] >>
    qspecl_then[`[s,l]`,`cs`]mp_tac (INST_TYPE[alpha|->``:t list``]compile_print_ctors_thm) >>
    simp[] >> rw[] >> simp[] >>
    simp[print_envC_def]))

val only_chars_lemma = prove(
  ``∀s. only_chars (MAP (Number o $& o ORD) s)``,
  Induct >> simp [only_chars_def,is_char_def,stringTheory.ORD_BOUND]);

val Cv_bv_can_Print = save_thm("Cv_bv_can_Print",prove(
  ``(∀Cv bv. Cv_bv pp Cv bv ⇒ can_Print bv) ∧
    (∀bvs ce env defs. benv_bvs pp bvs ce env defs ⇒ T)``,
  ho_match_mp_tac Cv_bv_ind >> simp[only_chars_lemma,only_chars_def] >>
  simp[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >> rw[] >>
  rfs[MEM_ZIP,GSYM LEFT_FORALL_IMP_THM,MEM_EL])
  |> CONJUNCT1)

val new_top_vs_def = Define`
  (new_top_vs (Tdec dec) = new_dec_vs dec) ∧
  (new_top_vs (Tmod _ _ _) = [])`

val between_labels_def = Define`
  between_labels bc l1 l2 ⇔
  ALL_DISTINCT (FILTER is_Label bc) ∧
  EVERY (between l1 l2) (MAP dest_Label (FILTER is_Label bc)) ∧
  l1 ≤ l2`

val good_labels_def = Define`
  good_labels nl code ⇔
    ALL_DISTINCT (FILTER is_Label code) ∧
    EVERY (combin$C $< nl o dest_Label) (FILTER is_Label code)`

val FILTER_F = store_thm("FILTER_F",
  ``∀ls. FILTER (λx. F) ls = []``,
  Induct >> simp[])
val _ = export_rewrites["FILTER_F"]

fun sorter [] l2 = l2
  | sorter (s::l1) l2 =
    let
      val (s,l2) = partition (equal s o fst o dest_var) l2
    in
      s @ (sorter l1 l2)
    end

val compile_print_top_thm = store_thm("compile_print_top_thm",
  ``∀tys map t cs.
    let cs' = compile_print_top tys map t cs in
    ∃code.
      cs'.out = [Stop] ++ REVERSE code ++ cs.out ∧
      between_labels code cs.next_label cs'.next_label ∧
      code_labels_ok code ∧
      ∀bs bc0 st0 tag bv bvs.
        bs.code = bc0 ++ code ++ [Stop] ∧
        good_labels cs.next_label bc0 ∧
        bs.pc = next_addr bs.inst_length bc0 ∧
        bs.stack = (Block(block_tag+tag)(if tag = none_tag then [] else [bv]))::st0 ∧
        (tag ≠ none_tag ⇒ can_Print bv) ∧
        (∀d. tag = none_tag ∧ IS_SOME tys ∧ t = Tdec d ⇒
         LIST_REL
         (λv bv. ∃n. FLOOKUP map v = SOME n ∧ el_check n bs.globals = SOME (SOME bv) ∧ can_Print bv)
         (new_dec_vs d) bvs)
        ⇒
        (let str =
          if tag ≠ none_tag then "raise " ++ print_bv bs.cons_names bv ++ "\n" else
          (case tys of NONE => ""
          | SOME types => (case t of
            | Tmod mn _ _ => "structure "++mn++" = <structure>\n"
            | Tdec d => (case d of
              | Dtype ts => print_envC ([],REVERSE(build_tdefs NONE ts))
              | Dexn cn ts => print_envC ([],[(cn, (LENGTH ts, TypeExn))])
              | d => print_bv_list bs.cons_names types (new_dec_vs d) bvs))) in
         let bs' = bs with <| pc := next_addr bs.inst_length (bc0 ++ code)
                            ; stack := st0
                            ; output := bs.output ++ str |> in
          bc_next^* bs bs')``,
  Cases_on`tys` >> Cases_on`t` >>
  simp[compile_print_top_def,FOLDL_emit_thm] >>
  rpt gen_tac >> simp[Once SWAP_REVERSE] >>
  TRY (
    specl_args_of_then``compile_print_dec``compile_print_dec_thm mp_tac >>
    simp[] >> strip_tac >> simp[Once SWAP_REVERSE] ) >>
  (conj_tac >- (
     EVAL_TAC >>
     REWRITE_TAC[FILTER_APPEND] >>
     simp[MEM_FILTER,EVERY_FILTER,EVERY_MAP,MEM_MAP] >>
     REWRITE_TAC[FILTER_APPEND] >> EVAL_TAC >>
     simp[ALL_DISTINCT_APPEND,MEM_FILTER,MEM_MAP] >>
     simp[FILTER_MAP,combinTheory.o_DEF] >>
     fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
     fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt,PULL_EXISTS] >>
     CCONTR_TAC >> fs[] >> res_tac >> fs[])) >>
  (conj_tac >-
    (rpt(match_mp_tac code_labels_ok_cons >> simp[]) >>
     EVAL_TAC >> simp[MEM_MAP] >>
     rator_x_assum`code_labels_ok`mp_tac >>
     EVAL_TAC >> metis_tac[])) >>
  rpt gen_tac >> strip_tac >>
  Q.PAT_ABBREV_TAC`str:string = if tag ≠ none_tag then X else Y` >>
  (`bc_fetch bs = SOME(Stack(Load 0))` by (
     match_mp_tac bc_fetch_next_addr >>
     qexists_tac`bc0` >> simp[] )) >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME(Stack(TagEq(block_tag+none_tag)))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp_tac (srw_ss()) [Abbr`bs1`] >>
    qexists_tac`TAKE (LENGTH bc0 + 1) bs.code` >>
    simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND,IMPLODE_EXPLODE_I] >>
    NO_TAC) >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs1`,bc_eval_stack_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME(JumpIf (Lab cs.next_label))` by (
    match_mp_tac bc_fetch_next_addr >>
    simp_tac (srw_ss()) [Abbr`bs1`] >>
    qexists_tac`TAKE (LENGTH bc0 + 2) bs.code` >>
    simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >>
    NO_TAC) >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs1`] >>
  simp[PULL_EXISTS,bc_find_loc_def] >>
  exists_suff_gen_then mp_tac bc_find_loc_aux_ALL_DISTINCT >>
  disch_then(qspec_then`LENGTH bc0 + 13`mp_tac o CONV_RULE (RESORT_FORALL_CONV(sorter["k"]))) >>
  disch_then exists_suff_tac >>
  simp[EL_APPEND1,EL_APPEND2,RIGHT_EXISTS_AND_THM] >>
  (conj_tac >- (
     rator_x_assum`good_labels`mp_tac >>
     TRY(rator_x_assum`code_labels_ok`mp_tac) >>
     TRY(qpat_assum`EVERY ($~ o is_Label) X`mp_tac) >>
     rpt(pop_assum kall_tac) >>
     simp[GSYM FILTER_EQ_NIL,combinTheory.o_DEF,IMPLODE_EXPLODE_I] >>
     REWRITE_TAC[FILTER_APPEND] >>
     EVAL_TAC >> rpt strip_tac >>
     fsrw_tac[ARITH_ss][ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,PULL_EXISTS,EVERY_MEM,FILTER_MAP] >>
     fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt,PULL_FORALL,combinTheory.o_DEF,MEM_MAP] >>
     rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC )) >>
  (reverse(Cases_on`tag=none_tag`>>fs[]) >- (
     rfs[bc_fetch_def] >>
     qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
     `bc_fetch bs1 = SOME(Stack(El 0))` by (
       match_mp_tac bc_fetch_next_addr >>
       simp_tac (srw_ss()) [Abbr`bs1`] >>
       qexists_tac`TAKE (LENGTH bc0 + 3) bs.code` >>
       simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] >>
       NO_TAC) >>
     rw[Once RTC_CASES1] >> disj2_tac >>
     simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
     simp[Abbr`bs1`,bc_eval_stack_def] >>
     qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
     match_mp_tac (RTC_TRANSITIVE |> SIMP_RULE std_ss [transitive_def]) >>
     exists_suff_gen_then (qspec_then`"raise "`mp_tac o CONV_RULE SWAP_FORALL_CONV) MAP_PrintC_thm >>
     simp[] >> disch_then(qspec_then`bs1`mp_tac) >>
     simp[Abbr`bs1`] >>
     disch_then(qspec_then`TAKE (LENGTH bc0 + 4) bs.code`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
     simp[TAKE_APPEND1,TAKE_APPEND2] >>
     discharge_hyps >- ( simp[SUM_APPEND,FILTER_APPEND] ) >>
     qmatch_abbrev_tac`bc_next^* bs1' bs3 ⇒ Z` >>
     strip_tac >> simp[Abbr`Z`] >> qexists_tac`bs3` >>
     qmatch_abbrev_tac`bc_next^* bs1 bs3 ∧ bc_next^* bs3 bs2` >>
     `bs1' = bs1` by (
       simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] >>
       simp[SUM_APPEND,FILTER_APPEND] ) >>
     rw[] >>
     `bc_fetch bs3 = SOME(Print)` by (
       match_mp_tac bc_fetch_next_addr >>
       simp_tac (srw_ss()) [Abbr`bs3`] >>
       qexists_tac`TAKE (LENGTH bc0 + 10) bs.code` >>
       simp[TAKE_APPEND1,TAKE_APPEND2,SUM_APPEND,FILTER_APPEND] ) >>
     rw[Once RTC_CASES1] >> disj2_tac >>
     simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
     simp[Abbr`bs3`,Abbr`bs1`] >>
     qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
     match_mp_tac (RTC_TRANSITIVE |> SIMP_RULE std_ss [transitive_def]) >>
     exists_suff_gen_then (qspec_then`"\n"`mp_tac o CONV_RULE SWAP_FORALL_CONV) MAP_PrintC_thm >>
     simp[] >> disch_then(qspec_then`bs1`mp_tac) >>
     simp[Abbr`bs1`] >>
     disch_then(qspec_then`TAKE (LENGTH bc0 + 11) bs.code`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
     simp[TAKE_APPEND1,TAKE_APPEND2] >>
     discharge_hyps >- ( simp[SUM_APPEND,FILTER_APPEND] ) >>
     qmatch_abbrev_tac`bc_next^* bs1' bs3 ⇒ Z` >>
     strip_tac >> simp[Abbr`Z`] >> qexists_tac`bs3` >>
     qmatch_abbrev_tac`bc_next^* bs1 bs3 ∧ bc_next^* bs3 bs2` >>
     `bs1' = bs1` by (
       simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] >>
       simp[SUM_APPEND,FILTER_APPEND] ) >>
     rw[] >>
     `bc_fetch bs3 = SOME(Jump (Lab (cs.next_label + 1)))` by (
       match_mp_tac bc_fetch_next_addr >>
       simp_tac (srw_ss()) [Abbr`bs3`] >>
       qexists_tac`TAKE (LENGTH bc0 + 12) bs.code` >>
       simp[TAKE_APPEND1,TAKE_APPEND2] >>
       REWRITE_TAC[FILTER_APPEND] >>
       EVAL_TAC >>
       REWRITE_TAC[GSYM SUM_SUM_ACC] >>
       simp[SUM_APPEND,FILTER_APPEND]) >>
     rw[Once RTC_CASES1] >> disj2_tac >>
     simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
     simp[Abbr`bs3`,Abbr`bs1`] >>
     rw[PULL_EXISTS] >>
     simp[bc_find_loc_def] >>
     exists_suff_gen_then mp_tac bc_find_loc_aux_ALL_DISTINCT >>
     disch_then(qspec_then`LENGTH bs.code - 2`mp_tac o CONV_RULE(RESORT_FORALL_CONV(sorter["k"]))) >>
     disch_then exists_suff_tac >>
     simp[EL_APPEND1,EL_APPEND2] >>
     conj_tac >- (
       rator_x_assum`good_labels`mp_tac >>
       TRY(rator_x_assum`code_labels_ok`mp_tac) >>
       TRY(qpat_assum`EVERY ($~ o is_Label) X`mp_tac) >>
       rpt(pop_assum kall_tac) >>
       simp[GSYM FILTER_EQ_NIL,combinTheory.o_DEF,IMPLODE_EXPLODE_I] >>
       REWRITE_TAC[FILTER_APPEND] >>
       EVAL_TAC >> rpt strip_tac >>
       fsrw_tac[ARITH_ss][ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,PULL_EXISTS,EVERY_MEM,FILTER_MAP] >>
       fs[FILTER_EQ_NIL,EVERY_MEM,is_Label_rwt,PULL_FORALL,combinTheory.o_DEF,MEM_MAP] >>
       rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
     rw[Once RTC_CASES1] >> disj1_tac >>
     simp[bc_state_component_equality,Abbr`bs2`,Abbr`str`] >>
     simp[TAKE_APPEND1,TAKE_APPEND2] >>
     simp[IMPLODE_EXPLODE_I] >>
     REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
     EVAL_TAC >>
     REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
     EVAL_TAC >>
     REWRITE_TAC[MAP_APPEND] >>
     EVAL_TAC >>
     simp[GSYM SUM_SUM_ACC,SUM_APPEND])) >>
  TRY (
    qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
    `bc_fetch bs1 = SOME(Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp_tac (srw_ss()) [Abbr`bs1`] >>
      qexists_tac`TAKE (LENGTH bc0 + 14) bs.code` >>
      simp[TAKE_APPEND2] >>
      simp_tac std_ss [FILTER_APPEND,SUM_APPEND] >>
      EVAL_TAC ) >>
    rw[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs1`,bc_eval_stack_def] >>
    rw[Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs2`,bc_state_component_equality] >>
    simp[TAKE_APPEND2] >>
    simp_tac std_ss [FILTER_APPEND,SUM_APPEND] >>
    EVAL_TAC >> simp[ADD1] >>
    REWRITE_TAC[GSYM SUM_SUM_ACC] >>
    simp[SUM_APPEND] >> NO_TAC)
  >- (
    simp[TAKE_APPEND1,TAKE_APPEND2] >>
    qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
    match_mp_tac (RTC_TRANSITIVE |> SIMP_RULE std_ss [transitive_def]) >>
    exists_suff_gen_then (qspec_then`"structure "++s++" = <structure>\n"`mp_tac o CONV_RULE SWAP_FORALL_CONV) MAP_PrintC_thm >>
    simp[] >> disch_then(qspec_then`bs1`mp_tac) >>
    simp[Abbr`bs1`] >>
    disch_then(qspec_then`TAKE (LENGTH bc0 + 14) bs.code`mp_tac o CONV_RULE SWAP_FORALL_CONV) >>
    simp[TAKE_APPEND1,TAKE_APPEND2,IMPLODE_EXPLODE_I] >>
    discharge_hyps >- ( REWRITE_TAC[FILTER_APPEND] >> EVAL_TAC) >>
    qmatch_abbrev_tac`bc_next^* bs1' bs3 ⇒ Z` >>
    strip_tac >> simp[Abbr`Z`] >> qexists_tac`bs3` >>
    conj_tac >- (
      qmatch_abbrev_tac`bc_next^* bs1 bs3` >>
      `bs1' = bs1` by (
        simp[Abbr`bs1`,Abbr`bs1'`,bc_state_component_equality] >>
        REWRITE_TAC[FILTER_APPEND] >>
        EVAL_TAC ) >>
      rw[] ) >>
    `bc_fetch bs3 = SOME(Stack Pop)` by (
      match_mp_tac bc_fetch_next_addr >>
      simp[Abbr`bs3`] >>
      qexists_tac`TAKE (LENGTH bs.code - 3) bs.code` >>
      simp[TAKE_APPEND1,TAKE_APPEND2,IMPLODE_EXPLODE_I] >>
      REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
      EVAL_TAC >>
      REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
      EVAL_TAC >>
      simp[GSYM SUM_SUM_ACC,SUM_APPEND] ) >>
    rw[Once RTC_CASES1] >> disj2_tac >>
    simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
    simp[Abbr`bs3`,bc_eval_stack_def] >>
    rw[Once RTC_CASES1] >> disj1_tac >>
    simp[Abbr`bs2`,bc_state_component_equality] >>
    simp[TAKE_APPEND1,TAKE_APPEND2,IMPLODE_EXPLODE_I] >>
    REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
    EVAL_TAC >>
    REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
    EVAL_TAC >>
    simp[GSYM SUM_SUM_ACC,SUM_APPEND] ) >>
  simp[TAKE_APPEND1,TAKE_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qmatch_assum_abbrev_tac`bs.code = bc0 ++ c1 ++ code ++ c2` >>
  first_x_assum(qspecl_then[`bs1 with code := bc0 ++ c1 ++ code`,`bc0 ++ c1`,`bvs`]mp_tac) >>
  simp[Abbr`bs1`] >>
  discharge_hyps >- (
    qunabbrev_tac`c1` >>
    REWRITE_TAC[FILTER_APPEND] >>
    EVAL_TAC ) >>
  strip_tac >>
  qmatch_assum_abbrev_tac`bc_next^* bs10 bs20` >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bs1 = bs10 with code := bs.code` by (
    simp[Abbr`bs1`,Abbr`bs10`,bc_state_component_equality] >>
    qunabbrev_tac`c1` >>
    REWRITE_TAC[FILTER_APPEND] >>
    EVAL_TAC ) >>
  `bc_next^* bs1 (bs20 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    first_assum (match_exists_tac o concl) >>
    simp[Abbr`bs10`,bc_state_component_equality] >>
    simp[Abbr`bs20`] ) >>
  match_mp_tac (RTC_TRANSITIVE |> SIMP_RULE std_ss [transitive_def]) >>
  HINT_EXISTS_TAC >> simp[] >> rw[] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  `bc_fetch bs1 = SOME (Stack Pop)` by (
    match_mp_tac bc_fetch_next_addr >>
    simp[Abbr`bs1`,Abbr`bs20`] >>
    qexists_tac`bc0 ++ c1 ++ code` >>
    unabbrev_all_tac >> simp[] ) >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  simp[bc_eval1_thm,bc_eval1_def,bump_pc_def] >>
  simp[Abbr`bs1`,Abbr`bs20`,bc_eval_stack_def] >>
  rw[Once RTC_CASES1] >> disj1_tac >>
  simp[Abbr`bs2`,bc_state_component_equality] >>
  unabbrev_all_tac >>
  REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
  EVAL_TAC >>
  REWRITE_TAC[FILTER_APPEND,FILTER_MAP,combinTheory.o_DEF] >>
  EVAL_TAC >>
  simp[GSYM SUM_SUM_ACC,SUM_APPEND] )

(* compile_Cexp *)

val compile_Cexp_thm = store_thm("compile_Cexp_thm",
  ``∀renv rsz cs exp.
      set (free_vars exp) ⊆ count (LENGTH renv)
    ∧ no_labs exp
    ⇒
    let cs' = compile_Cexp renv rsz cs exp in
    ∃c0 code. cs'.out = REVERSE code ++ REVERSE c0 ++ cs.out ∧ between_labels (code++c0) cs.next_label cs'.next_label ∧
    code_labels_ok (c0++code) ∧
    ∀s env res rd csz bs bc0 bc00.
      Cevaluate s env exp res
    ∧ closed_vlabs env s bc0
    ∧ Cenv_bs rd s env renv rsz (bs with code := bc00)
    ∧ (bc00 = bc0 ∨ bc00 = bc0 ++ c0)
    ∧ bs.code = bc0 ++ c0 ++ code
    ∧ bs.pc = next_addr bs.inst_length bc0
    ∧ bs.clock = SOME (FST (FST s))
    ∧ good_labels cs.next_label bc0
    ⇒
    case SND res of
    | Rval v =>
        ∃s' w. syneq v w ∧
        csg_rel syneq (FST res) s' ∧
        closed_vlabs env s' (bc0++c0) ∧
        all_vlabs w ∧ (∀cd. cd ∈ vlabs w ⇒ code_env_cd (bc0++c0) cd) ∧
        code_for_push rd bs (bc0++c0) bc0 (c0++code) s' env [w] renv rsz
    | Rerr (Rraise err) =>
      ∀st hdl sp ig.
        bs.stack = ig++StackPtr sp::CodePtr hdl::st
      ∧ bs.handler = LENGTH st + 1
      ⇒
        ∃s' w. syneq err w ∧
         csg_rel syneq (FST res) s' ∧
         closed_vlabs env s' (bc0++c0) ∧
         code_for_return rd bs (bc0++c0) st hdl sp w s'
    | Rerr Rtimeout_error =>
      ∃bs'. bc_next^* bs bs' ∧ bs'.clock = SOME 0 ∧ bc_fetch bs' = SOME Tick ∧ bs'.output = bs.output
    | _ => T``,
  rw[compile_Cexp_def] >>
  qspecl_then[`LENGTH renv`,`cs.next_label`,`exp`]mp_tac (CONJUNCT1 label_closures_thm) >>
  simp[] >> strip_tac >>
  qspecl_then[`LENGTH renv`,`cs with next_label := nl`,`Ce`]mp_tac compile_code_env_thm >>
  simp[] >>
  discharge_hyps >- (
    simp[ALL_DISTINCT_GENLIST,EVERY_GENLIST] ) >>
  disch_then(Q.X_CHOOSE_THEN`c0`strip_assume_tac) >>
  qspecl_then[`renv`,`TCNonTail`,`rsz`,`cs'`,`Ce`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`c1`strip_assume_tac) >>
  simp[Abbr`cs''`] >>
  qexists_tac`c0` >> simp[Once SWAP_REVERSE] >>
  conj_tac >- (
    simp[between_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >>
    fsrw_tac[DNF_ss][MEM_GENLIST] >>
    res_tac >> DECIDE_TAC ) >>
  conj_tac >- (
    rfs[code_labels_ok_def,uses_label_thm,EXISTS_REVERSE] >>
    qmatch_assum_abbrev_tac`P ⇒ Q` >>
    `P` by (
      simp[Abbr`P`] >>
      imp_res_tac all_labs_free_labs >>
      fs[all_labs_list_MAP] ) >>
    qunabbrev_tac`P`>>fs[Abbr`Q`] >>
    reverse(rw[])>- metis_tac[] >>
    last_x_assum(qspec_then`l`mp_tac) >>
    simp[] >> strip_tac >> fs[] >>
    qsuff_tac`MEM l (MAP (FST o FST o SND) (free_labs (LENGTH renv) Ce))`>-metis_tac[] >>
    qmatch_assum_abbrev_tac`MEM l a` >>
    qmatch_abbrev_tac`MEM l b` >>
    qsuff_tac`set a ⊆ set b`>-rw[SUBSET_DEF]>>
    unabbrev_all_tac >>
    simp[LIST_TO_SET_FLAT,MAP_MAP_o,LIST_TO_SET_MAP,GSYM IMAGE_COMPOSE] >>
    simp[combinTheory.o_DEF,LAMBDA_PROD] >>
    metis_tac[SIMP_RULE(srw_ss())[combinTheory.o_DEF,LAMBDA_PROD](CONJUNCT1 free_labs_free_labs)] ) >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`bc00A = (X ∨ Y)` >>
  strip_tac >>
  first_x_assum(qspecl_then[`bs`,`bc0`]mp_tac) >>
  simp[] >>
  discharge_hyps >- (
    simp[MEM_MAP,MEM_GENLIST,MEM_FILTER,is_Label_rwt] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,good_labels_def] >>
    rw[] >> res_tac >> DECIDE_TAC ) >>
  strip_tac >>
  `LENGTH renv = LENGTH env` by (
    fs[Cenv_bs_def,env_renv_def,EVERY2_EVERY] ) >>
  fs[] >>
  qmatch_assum_abbrev_tac`bc_next bs bs0` >>
  qspecl_then[`s`,`env`,`exp`,`res`]mp_tac (CONJUNCT1 Cevaluate_syneq) >>
  simp[] >>
  disch_then(qspecl_then[`$=`,`s`,`env`,`Ce`]mp_tac) >>
  simp[] >>
  disch_then(Q.X_CHOOSE_THEN`Cres`strip_assume_tac) >>
  qspecl_then[`s`,`env`,`Ce`,`Cres`]mp_tac(CONJUNCT1 compile_val) >>
  PairCases_on`Cres`>>simp[]>>
  disch_then(qspecl_then[`rd`,`cs'`,`renv`,`rsz`,`bs0`,`bc0 ++ c0`,`REVERSE c1`,`bc0 ++ c0`,`REVERSE c1`,`[]`]mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`bs0`] >>
    simp[CONJ_ASSOC] >>
    qmatch_abbrev_tac`(A ∧ B) ∧ C` >>
    `B ∧ C` by (
      simp[Abbr`A`,Abbr`B`,Abbr`C`,FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,good_labels_def] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[Abbr`A`,Abbr`B`,Abbr`C`,GSYM CONJ_ASSOC] >>
    fs[closed_vlabs_def,vlabs_csg_def] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[code_env_cd_append] >>
    conj_tac >- metis_tac[SUBSET_TRANS] >>
    match_mp_tac Cenv_bs_with_irr >>
    qexists_tac`bs with code := bc0 ++ c0` >> simp[] >>
    Cases_on`bc00 = bc0` >- (
      match_mp_tac Cenv_bs_append_code >>
      HINT_EXISTS_TAC >>
      simp[bc_state_component_equality] ) >>
    `bc0 ++ c0 = bc00` by metis_tac[] >>
    pop_assum SUBST1_TAC >>
    simp[] ) >>
  PairCases_on`res`>>fs[]>>
  strip_tac >>
  Cases_on`res3`>>fs[]>>rfs[]>-(
    rpt HINT_EXISTS_TAC >>
    simp[] >>
    qspecl_then[`s`,`env`,`Ce`,`(((Cres0,Cres1),Cres2),Cres3)`,`bc0++c0`]mp_tac Cevaluate_closed_vlabs >>
    simp[] >>
    discharge_hyps >- (
      fs[EVERY_MEM] >>
      fs[closed_vlabs_def] >>
      `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0))` by (
        simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
        fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      metis_tac[code_env_cd_append] ) >>
    simp[] >> strip_tac >>
    conj_tac >- (
      fs[closed_vlabs_def,SUBSET_DEF] >>
      fs[EVERY_MEM] >>
      rw[] >> res_tac >> TRY(metis_tac[]) >>
      match_mp_tac code_env_cd_append >>
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    rw[] >>
    ntac 4 (pop_assum kall_tac) >>
    pop_assum mp_tac >>
    simp[code_for_push_def] >>
    simp_tac(srw_ss()++DNF_ss)[]>>
    simp[Abbr`bs0`] >>
    map_every qx_gen_tac [`rf`,`rd'`,`ck`,`gv`,`bv`] >>
    strip_tac >>
    map_every qexists_tac [`rf`,`rd'`,`ck`,`gv`,`bv`] >>
    simp[] >>
    simp[Once RTC_CASES1] >>
    disj2_tac >>
    HINT_EXISTS_TAC >>
    simp[] ) >>
  rw[] >>
  reverse BasicProvers.CASE_TAC >> fs[] >- (
    first_x_assum(qspec_then`TCNonTail`mp_tac) >>
    simp[Abbr`bs0`] >>
    metis_tac[RTC_SUBSET,RTC_TRANSITIVE,transitive_def] ) >>
  rpt gen_tac >> strip_tac >>
  rpt HINT_EXISTS_TAC >>
  fs[] >>
  qmatch_assum_abbrev_tac`Cevaluate s env Ce Cres` >>
  qspecl_then[`s`,`env`,`Ce`,`Cres`,`bc0++c0`]mp_tac Cevaluate_closed_vlabs >>
  simp[] >>
  discharge_hyps >- (
    fs[EVERY_MEM] >>
    fs[closed_vlabs_def] >>
    `ALL_DISTINCT (FILTER is_Label (bc0 ++ c0))` by (
      simp[FILTER_APPEND,ALL_DISTINCT_APPEND] >>
      fsrw_tac[DNF_ss][good_labels_def,MEM_FILTER,is_Label_rwt,MEM_MAP,MEM_GENLIST,between_def,EVERY_MEM] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    metis_tac[code_env_cd_append] ) >>
  rw[Abbr`Cres`] >>
  first_x_assum(qspec_then`TCNonTail`mp_tac) >>
  simp[Abbr`bs0`] >>
  disch_then(qspec_then`ig`mp_tac) >>
  simp[] >>
  simp[code_for_return_def] >>
  simp_tac(srw_ss()++DNF_ss)[]>>
  map_every qx_gen_tac [`bv`,`rf`,`rd'`,`gv`,`ck`] >>
  strip_tac >>
  map_every qexists_tac [`bv`,`rf`,`rd'`,`gv`,`ck`] >>
  simp[] >>
  simp[Once RTC_CASES1] >>
  disj2_tac >>
  HINT_EXISTS_TAC >>
  simp[] )

(* env_rs *)

val good_globals_def = Define`
  good_globals e (m:num) l g ⇔ l = m ∧ g = m ∧
  (∀n. n ∈ FRANGE (SND e) ∨
       n ∈ BIGUNION (IMAGE FRANGE (FRANGE (FST e))) ⇒
       n < m)`

val i2_Cv_def = Define`
  i2_Cv exh0 v Cv ⇔
    ∃vp. ∀exh. DISJOINT (FDOM exh) (FDOM exh0) ⇒
      v_pat (v_to_pat (v_to_exh (exh0 ⊌ exh) v)) vp ∧ closed_pat vp ∧
      syneq (v_to_Cv vp) Cv`

val closed_genv_def = Define`
  closed_genv genv (mods,tops) (envM,envE) ⇔
  ∀n. n < LENGTH genv ∧ IS_SOME (EL n genv) ⇒
       (∃x. IS_SOME (lookup x envE) ∧ FLOOKUP tops x = SOME n) ∨
       (∃mn map env x. lookup mn envM = SOME map ∧ IS_SOME (lookup x map) ∧
                       FLOOKUP mods mn = SOME env ∧ FLOOKUP env x = SOME n)`

val env_rs_def = Define`
  env_rs ((envM,envC,envE):all_env) ((cnt,s):v count_store) (genv,(tids,gtagenv),rd)
    (rs:compiler_state) (bs:bc_state)
  ⇔
    good_labels rs.rnext_label bs.code ∧
    good_globals rs.globals_env rs.next_global (LENGTH bs.globals) (LENGTH genv) ∧
    closed_genv genv rs.globals_env (envM,envE) ∧
    bs.stack = [] ∧
    EVERY closed s ∧
    EVERY closed (MAP SND envE) ∧
    EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
    ∃s1 s2 genv2 Cs Cg.
      to_i1_invariant
        genv (FST rs.globals_env) (SND rs.globals_env)
        envM envE (cnt,s) (cnt,s1) (set (MAP FST envM)) ∧
      to_i2_invariant
        tids envC rs.exh rs.contags_env gtagenv
        (cnt,s1) (cnt,s2) genv genv2 ∧
      LIST_REL (i2_Cv rs.exh) s2 Cs ∧
      LIST_REL (OPTREL (i2_Cv rs.exh)) genv2 Cg ∧
      closed_vlabs [] ((cnt,Cs),Cg) bs.code ∧
      Cenv_bs rd ((cnt,Cs),Cg) [] [] 0 bs`

val env_rs_empty = store_thm("env_rs_empty",
  ``∀envs s cs genv tids gtagenv rd grd bs ck.
    bs.stack = [] ∧ bs.globals = [] ∧ FILTER is_Label bs.code = [] ∧
    (∀n. bs.clock = SOME n ⇒ n = ck) ∧ envs = ([],init_envC,[]) ∧ s = (ck,[]) ∧
    grd = ([],(tids,gtagenv),rd) ∧
    rd.sm = [] ∧ rd.cls = FEMPTY ∧ cs = init_compiler_state ⇒
    env_rs envs s grd cs bs``,
  rpt gen_tac >>
  simp[env_rs_def,to_i1_invariant_def,to_i2_invariant_def] >>
  strip_tac >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  rw[init_compiler_state_def,get_tagenv_def,cenv_inv_def] >>
  rw[Once v_to_i1_cases] >> rw[Once v_to_i1_cases] >>
  rw[Once s_to_i1_cases] >> rw[Once s_to_i1'_cases] >> rw[Once v_to_i1_cases] >>
  rw[Once genv_to_i2_cases] >>
  simp[Once s_to_i2_cases] >> simp[Once s_to_i2'_cases] >> simp[Once v_to_i2_cases] >>
  simp[Cenv_bs_def,env_renv_def,s_refs_def,good_rd_def,FEVERY_ALL_FLOOKUP] >>
  simp[all_vlabs_csg_def,vlabs_csg_def,closed_vlabs_def,closed_genv_def] >>
  cheat)

(* TODO: move *)
val to_i1_invariant_change_clock = store_thm("to_i1_invariant_change_clock",
  ``to_i1_invariant genv mods tops menv env s s_i1 mod_names ∧
    SND s' = SND s ∧ SND s_i1' = SND s_i1 ∧ FST s' = FST s_i1'
    ⇒
    to_i1_invariant genv mods tops menv env s' s_i1' mod_names``,
  simp[to_i1_invariant_def] >>
  rw[Once s_to_i1_cases] >>
  rw[Once s_to_i1_cases] >>
  metis_tac[pair_CASES,PAIR_EQ,SND,FST])

(* TODO: move *)
val to_i2_invariant_change_clock = store_thm("to_i2_invariant_change_clock",
  ``to_i2_invariant tids envC exh tagenv_st gtagenv s s_i2 genv genv_i2 ∧
    SND s' = SND s ∧ SND s_i2' = SND s_i2 ∧ FST s' = FST s_i2'
    ⇒
    to_i2_invariant tids envC exh tagenv_st gtagenv s' s_i2' genv genv_i2``,
  simp[to_i2_invariant_def] >>
  rw[Once s_to_i2_cases] >>
  rw[Once s_to_i2_cases] >>
  metis_tac[pair_CASES,PAIR_EQ,SND,FST])

val env_rs_change_clock = store_thm("env_rs_change_clock",
   ``∀env cs grd rs bs cs' ck' bs' new_clock.
     env_rs env cs grd rs bs ∧ cs' = (ck',SND cs) ∧
     (bs' = bs with clock := new_clock) ∧
     (new_clock = NONE ∨ new_clock = SOME ck')
     ⇒
     env_rs env cs' grd rs bs'``,
  qx_gen_tac`p` >> PairCases_on`p` >>
  qx_gen_tac`q` >> PairCases_on`q` >>
  qx_gen_tac`r` >> PairCases_on`r` >>
  simp[env_rs_def] >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`d = (a ∨ b)` >>
  strip_tac >>
  map_every qexists_tac[`s1`] >>
  simp[RIGHT_EXISTS_AND_THM] >>
  conj_tac >- (
    metis_tac[to_i1_invariant_change_clock,FST,SND] ) >>
  map_every qexists_tac[`s2`,`genv2`] >>
  conj_tac >- (
    metis_tac[to_i2_invariant_change_clock,FST,SND] ) >>
  simp[PULL_EXISTS] >>
  rpt HINT_EXISTS_TAC >>
  simp[] >>
  conj_tac >- (
    fs[all_vlabs_csg_def,vlabs_csg_def,closed_vlabs_def] >>
    metis_tac[] ) >>
  match_mp_tac Cenv_bs_change_store >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[bc_state_component_equality] >>
  fs[Cenv_bs_def,s_refs_def,Abbr`d`,good_rd_def])

(*
val env_rs_change_store = store_thm("env_rs_change_store",
  ``∀env cs rs rd bs rd' cs' Cs' bs' ck' rf'.
    env_rs env cs rs rd bs ∧
    (IS_SOME ck' ⇒ ck' = SOME (FST cs')) ∧
    bs' = bs with <| refs := rf'; clock := ck'|> ∧
    LENGTH (SND cs) ≤ LENGTH (SND cs') ∧
    s_refs rd' (FST cs',Cs') bs' ∧
    LIST_REL syneq (vs_to_Cvs (MAP FST o_f rs.rmenv) (cmap rs.contab) (SND cs')) Cs' ∧
    DRESTRICT bs.refs (COMPL (set rd.sm)) ⊑ DRESTRICT rf' (COMPL (set rd'.sm)) ∧
    rd.sm ≼ rd'.sm ∧ rd.cls ⊑ rd'.cls ∧
    EVERY all_vlabs Cs' ∧
    (∀cd. cd ∈ vlabs_list Cs' ⇒ code_env_cd (MAP SND o_f rs.rmenv) bs.code cd)
    ⇒
    env_rs env cs' rs rd' bs'``,
  rw[] >>
  fs[env_rs_def,LET_THM] >> rfs[] >> fs[] >>
  rpt HINT_EXISTS_TAC >> simp[] >>
  qexists_tac`Cs'` >>
  fs[vs_to_Cvs_MAP] >>
  simp[CONJ_ASSOC] >>
  reverse conj_tac >- (
    match_mp_tac bytecodeProofTheory.Cenv_bs_change_store >>
    map_every qexists_tac[`rd`,`(FST cs,Cs)`,`bs`,`rf'`,`ck'`] >>
    simp[bytecodeTheory.bc_state_component_equality] ) >>
  fs[closed_Clocs_def,closed_vlabs_def] >>
  fs[EVERY2_EVERY] >>
  full_simp_tac pure_ss [SUBSET_DEF,IN_COUNT] >>
  metis_tac[LESS_LESS_EQ_TRANS])
*)

val env_rs_with_bs_irr = store_thm("env_rs_with_bs_irr",
  ``∀env cs grd rs bs bs'.
    env_rs env cs grd rs bs
    ∧ bs'.globals = bs.globals
    ∧ bs'.stack = bs.stack
    ∧ bs'.refs = bs.refs
    ∧ bs'.clock = bs.clock
    ∧ bs'.code = bs.code
    ∧ bs'.inst_length = bs.inst_length
    ⇒
    env_rs env cs grd rs bs'``,
  simp[FORALL_PROD] >> rw[env_rs_def] >>
  rpt(first_assum(match_exists_tac o concl) >> simp[]) >>
  match_mp_tac Cenv_bs_with_irr >>
  HINT_EXISTS_TAC >> rfs[])

val env_rs_append_code = store_thm("env_rs_append_code",
  ``∀env cs grd rs bs bs' rs' c nl.
    env_rs env cs grd rs bs ∧
    bs' = bs with code := bs.code ++ c ∧
    rs' = rs with rnext_label := nl ∧
    good_labels nl bs'.code
    ⇒
    env_rs env cs grd rs' bs'``,
  simp[FORALL_PROD] >>
  simp[env_rs_def] >>
  rpt gen_tac >> strip_tac  >>
  rpt(first_assum(match_exists_tac o concl) >> simp[]) >>
  conj_tac >- (
    fs[closed_vlabs_def] >> rw[]>>
    match_mp_tac code_env_cd_append >>
    fs[good_labels_def]) >>
  match_mp_tac Cenv_bs_append_code >>
  metis_tac[])

val env_rs_can_Print = store_thm("env_rs_can_Print",
  ``∀env cs grd rs bs n v.
    env_rs env cs grd rs bs ∧
    EL n bs.globals = SOME v ∧
    n ∈ (FRANGE (SND rs.globals_env) ∪
         BIGUNION (IMAGE FRANGE (FRANGE (FST rs.globals_env))))
    ⇒
    can_Print v``,
  simp_tac std_ss [FORALL_PROD] >>
  rpt gen_tac >>
  Q.PAT_ABBREV_TAC`ss:num set = x ∪ y` >>
  rw[env_rs_def,Cenv_bs_def,s_refs_def] >>
  rfs[EVERY2_EVERY] >>
  fs[EVERY_MEM,MEM_ZIP,PULL_EXISTS,optionTheory.OPTREL_def] >>
  fs[good_globals_def] >>
  `n < LENGTH bs.globals` by (
    fs[Abbr`ss`] >> res_tac >> fs[] >> metis_tac[] ) >>
  match_mp_tac (GEN_ALL Cv_bv_can_Print) >>
  metis_tac[optionTheory.NOT_SOME_NONE,optionTheory.SOME_11])

(* compile_top *)

val global_dom_def = Define`
  global_dom (me,e) = IMAGE Short (FDOM e) ∪ { Long m x | ∃e. FLOOKUP me m = SOME e ∧ x ∈ FDOM e}`

val compile_top_labels = store_thm("compile_top_labels",
  ``∀types rs top.
      FV_top top ⊆ global_dom rs.globals_env
      ⇒
      between_labels (SND(compile_top types rs top)) rs.rnext_label (FST(compile_top types rs top)).rnext_label ∧
      code_labels_ok (SND(compile_top types rs top))``,
   simp[compile_top_def,UNCURRY,pair_CASE_def] >>
   rpt gen_tac >> strip_tac >>
   specl_args_of_then``compile_Cexp``compile_Cexp_thm mp_tac >>
   discharge_hyps >- (
     simp[] >>
     qmatch_abbrev_tac`x = []` >>
     qsuff_tac`set x ⊆ {}` >- rw[] >>
     qunabbrev_tac`x` >>
     specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
     match_mp_tac(METIS_PROVE[]``(p ∧ (p ∧ q ⇒ r)) ⇒ ((p ⇒ q) ⇒ r)``) >>
     conj_tac >- (
       simp[] >>
       Q.PAT_ABBREV_TAC`p = prompt_to_i3 X Y Z A` >>
       PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
       pop_assum(ASSUME_TAC o SYM) >>
       imp_res_tac free_vars_i2_prompt_to_i3 >> simp[] >>
       Q.PAT_ABBREV_TAC`p = prompt_to_i2 X A` >>
       PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
       pop_assum(ASSUME_TAC o SYM) >>
       imp_res_tac free_vars_prompt_to_i2 >> simp[] >>
       Q.PAT_ABBREV_TAC`p = top_to_i1 A B C D` >>
       PairCases_on`p` >> fs[markerTheory.Abbrev_def] >>
       pop_assum(ASSUME_TAC o SYM) >>
       imp_res_tac FV_top_to_i1 >>
       simp[Once EXTENSION] >> fs[SUBSET_DEF] >>
       Cases_on`rs.globals_env`>> fs[global_dom_def] >>
       rw[] >> CCONTR_TAC >> fs[] >> res_tac >> fs[] ) >>
     strip_tac >> rfs[] ) >>
   Q.PAT_ABBREV_TAC`Cexp = exp_to_Cexp Z` >>
   simp[] >> strip_tac >>
   specl_args_of_then``compile_print_top``compile_print_top_thm mp_tac >>
   simp[] >> strip_tac >>
   simp[] >>
   pop_assum kall_tac >>
   conj_tac >- (
     rpt(rator_x_assum`between_labels`mp_tac) >>
     rpt(rator_x_assum`code_labels_ok`mp_tac) >>
     rpt (pop_assum kall_tac) >>
     simp[between_labels_def,FILTER_APPEND,FILTER_REVERSE,ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,MAP_REVERSE,EVERY_REVERSE] >>
     simp[EVERY_MAP,EVERY_FILTER,is_Label_rwt,PULL_EXISTS] >>
     simp[EVERY_MEM,MEM_FILTER,is_Label_rwt,PULL_EXISTS] >>
     rw[] >> res_tac >> fsrw_tac[ARITH_ss][between_def] >>
     spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
   match_mp_tac code_labels_ok_cons >> simp[] >>
   REWRITE_TAC[GSYM APPEND_ASSOC] >>
   match_mp_tac code_labels_ok_append >>
   simp[code_labels_ok_REVERSE] >>
   REWRITE_TAC[GSYM REVERSE_APPEND] >>
   simp[code_labels_ok_REVERSE] )

(* TODO: move *)
val genv_to_i2_LENGTH_EQ = store_thm("genv_to_i2_LENGTH_EQ",
  ``∀x y z. genv_to_i2 x y z ⇒ LENGTH y = LENGTH z``,
  ho_match_mp_tac genv_to_i2_ind >> simp[])

val genv_to_i2_LIST_REL = store_thm("genv_to_i2_LIST_REL",
  ``∀x y z. genv_to_i2 x y z ⇒ LIST_REL (OPTREL (v_to_i2 x)) y z``,
  ho_match_mp_tac genv_to_i2_ind >> simp[optionTheory.OPTREL_def])

val build_rec_env_MAP = store_thm("build_rec_env_MAP",
  ``build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val pmatch_dom = store_thm("pmatch_dom",
  ``(∀cenv s p v env env'.
      (pmatch cenv s p v env = Match env') ⇒
      (MAP FST env' = pat_bindings p [] ++ (MAP FST env))) ∧
    (∀cenv s ps vs env env'.
      (pmatch_list cenv s ps vs env = Match env') ⇒
      (MAP FST env' = pats_bindings ps [] ++ MAP FST env))``,
  ho_match_mp_tac pmatch_ind >>
  rw[pmatch_def,pat_bindings_def,libTheory.bind_def] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  ONCE_REWRITE_TAC[pat_bindings_accum,SimpRHS] >>
  simp[])

val shift_thm =
  mkshift_thm
  |> Q.SPEC`λv. v + n`
  |> SIMP_RULE std_ss [GSYM shift_def]
  |> Q.GEN`n`

val syneq_exp_shift_both = store_thm("syneq_exp_shift_both",
  ``∀z1 z2 V e1 e2 n k z1' z2' V'. syneq_exp z1 z2 V e1 e2 ∧
      set (free_vars e1) ⊆ count z1 ∧ k ≤ z1 ∧ no_labs e1 ∧
      set (free_vars e2) ⊆ count z2 ∧ k ≤ z2 ∧ no_labs e2 ∧
      (let R = λx y. if x < k then y = x else y = x+n in
         (∀x y. (R O V O inv R) x y ⇒ V' x y)) ∧
      k ≤ z1' ∧ k ≤ z2' ∧
      (∀x. MEM x (free_vars e1) ∧ k ≤ x ⇒ x+n < z1') ∧
      (∀x. MEM x (free_vars e2) ∧ k ≤ x ⇒ x+n < z2')
      ⇒
      syneq_exp z1' z2' V' (shift n k e1) (shift n k e2)``,
  rw[] >>
  match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
  qabbrev_tac`R = λx y. if x < k then y = x else y = x + n` >>
  qexists_tac`(R O V) O (inv R)` >>
  conj_tac >- (
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
    map_every qexists_tac[`z1`,`e1`] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_sym_no_labs)) >>
      simp[] >>
      match_mp_tac shift_thm >>
      simp[] >>
      simp[Abbr`R`] >>
      fsrw_tac[ARITH_ss][] ) >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_trans)) >>
    first_assum (match_exists_tac o concl) >> simp[] >>
    match_mp_tac shift_thm >>
    simp[] >>
    simp[Abbr`R`] >>
    fsrw_tac[ARITH_ss][] ) >>
  fs[LET_THM,O_ASSOC])

val exp_pat_syneq_exp = store_thm("exp_pat_syneq_exp",
  ``∀z1 z2 V e1 e2. exp_pat z1 z2 V e1 e2 ⇒
      set (free_vars_pat e1) ⊆ count z1 ∧
      set (free_vars_pat e2) ⊆ count z2 ∧
      (∀x y. V x y ⇒ (x < z1 ⇔ y < z2) ∧ (z1 ≤ x ⇒ y = x))
      ⇒
      syneq_exp z1 z2 V (exp_to_Cexp e1) (exp_to_Cexp e2)``,
  ho_match_mp_tac exp_pat_ind >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once syneq_exp_cases] >>
    metis_tac[]) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    fs[] >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      conj_tac >- (
        fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      Cases >> Cases >> simp[bind_pat_def,ADD1] >>
      metis_tac[]) >>
    strip_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    Cases >> Cases >> simp[bind_pat_def]) >>
  strip_tac >- (
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases,EVERY2_MAP] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >>
    imp_res_tac EVERY2_LENGTH >>
    simp[UNCURRY,MEM_ZIP,PULL_EXISTS] >>
    rw[] >> first_x_assum match_mp_tac >>
    fs[SUBSET_DEF,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
    metis_tac[MEM_EL]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] >>
    qexists_tac`λx y. x = 0 ∧ y = 0` >>
    reverse conj_tac >- (
      simp[Once syneq_exp_cases] ) >>
    simp[Once syneq_exp_cases] >>
    simp[syneq_cb_aux_def] >>
    match_mp_tac syneq_exp_shift_both >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps_keep >- (
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      conj_tac >- (
        fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      Cases >> Cases >> simp[bind_pat_def,ADD1] >>
      metis_tac[]) >>
    strip_tac >>
    first_assum (match_exists_tac o concl) >>
    simp[inv_DEF,O_DEF,PULL_EXISTS] >>
    conj_tac >- (
      ntac 2 gen_tac >> Cases >> Cases >> simp[syneq_cb_V_def,bind_pat_def,ADD1] >>
      rw[] >> CCONTR_TAC >> fs[] >> rw[] >> res_tac >> rw[] >>
      fsrw_tac[ARITH_ss][] ) >>
    fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    Cases_on`op`>>simp[] >>
    cheat ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] >>
    match_mp_tac (MP_CANON (CONJUNCT1 syneq_exp_mono_V)) >>
    fs[] >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      ONCE_REWRITE_TAC[CONJ_ASSOC] >>
      conj_tac >- (
        fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      Cases >> Cases >> simp[bind_pat_def,ADD1] >>
      metis_tac[]) >>
    strip_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    Cases >> Cases >> simp[bind_pat_def]) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> rpt strip_tac >>
    simp[Once syneq_exp_cases] >>
    cheat ) >>
  simp[Once syneq_exp_cases] )

val v_pat_syneq = store_thm("v_pat_syneq",
  ``∀v1 v2. v_pat v1 v2 ⇒ closed_pat v1 ∧ closed_pat v2 ⇒ syneq (v_to_Cv v1) (v_to_Cv v2)``,
  ho_match_mp_tac v_pat_ind >> simp[] >>
  strip_tac >- (
    rw[] >>
    simp[Once syneq_cases] >>
    simp[EVERY2_MAP] >>
    match_mp_tac EVERY2_MEM_MONO >>
    HINT_EXISTS_TAC >>
    imp_res_tac EVERY2_LENGTH >>
    simp[UNCURRY,MEM_ZIP,PULL_EXISTS] >>
    rw[] >> first_x_assum match_mp_tac >>
    fs[EVERY_MEM] >> metis_tac[MEM_EL]) >>
  strip_tac >- (
    rw[] >>
    simp[Once syneq_cases] >>
    last_x_assum mp_tac >>
    Q.PAT_ABBREV_TAC`V = env_pat X env1 env2` >>
    strip_tac >>
    qexists_tac`V` >>
    qexists_tac`λx y. x = 0 ∧ y = 0` >>
    simp[Abbr`V`,env_pat_def,EL_MAP] >>
    simp[Once syneq_exp_cases] >>
    simp[syneq_cb_aux_def] >>
    ntac 2 (last_x_assum mp_tac) >>
    simp[Once closed_pat_cases] >>
    simp[Once closed_pat_cases] >>
    ntac 2 strip_tac >>
    conj_tac >- (
      rw[] >>
      first_x_assum match_mp_tac >>
      fs[EVERY_MEM] >>
      metis_tac[MEM_EL] ) >>
    match_mp_tac syneq_exp_shift_both >>
    simp[] >>
    first_assum(mp_tac o MATCH_MP exp_pat_syneq_exp) >>
    discharge_hyps_keep >- (
      simp[ADD1] >>
      Cases >> Cases >> simp[bind_pat_def,ADD1] >>
      simp[env_pat_def] ) >>
    strip_tac >>
    first_assum(match_exists_tac o concl) >>
    simp[] >>
    reverse conj_tac >- (
      fsrw_tac[ARITH_ss][SUBSET_DEF] >>
      rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    simp[O_DEF,inv_DEF,PULL_EXISTS] >>
    ntac 2 gen_tac >>
    Cases >> Cases >> simp[bind_pat_def,syneq_cb_V_def,ADD1] >>
    simp[env_pat_def] ) >>
  rw[] >>
  simp[Once syneq_cases] >>
  ntac 2 (pop_assum mp_tac) >>
  ntac 2 (simp[Once closed_pat_cases]) >>
  ntac 2 (strip_tac) >>
  last_x_assum mp_tac >>
  Q.PAT_ABBREV_TAC`V = env_pat X env1 env2` >>
  strip_tac >>
  qexists_tac`V` >>
  qexists_tac`λx y. x = y ∧ x < LENGTH funs1 ∧ y < LENGTH funs2` >>
  simp[Abbr`V`,env_pat_def,EL_MAP] >>
  simp[Once syneq_exp_cases,EL_MAP] >>
  simp[syneq_cb_aux_def] >>
  conj_tac >- (
    rw[] >>
    first_x_assum match_mp_tac >>
    fs[EVERY_MEM] >>
    metis_tac[MEM_EL] ) >>
  rw[] >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS] >>
  match_mp_tac (MP_CANON exp_pat_syneq_exp) >>
  conj_tac >- (
    match_mp_tac (GEN_ALL (MP_CANON exp_pat_mono)) >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[ADD1,AC ADD_COMM ADD_ASSOC] >>
    strip_tac >>
    first_assum(match_exists_tac o concl) >>
    simp[] >>
    simp[bindn_pat_thm,syneq_cb_V_def] >>
    rw[env_pat_def] >> simp[] ) >>
  fs[MEM_EL,PULL_EXISTS] >>
  simp[syneq_cb_V_def] >>
  rw[env_pat_def] >> simp[] )

val exp_pat_free_vars = store_thm("exp_pat_free_vars",
  ``∀z1 z2 V e1 e2. exp_pat z1 z2 V e1 e2 ⇒
      (∀x y. V x y ⇒ (x < z1 ⇔ y < z2)) ∧
      set (free_vars_pat e1) ⊆ count z1 ⇒
      set (free_vars_pat e2) ⊆ count z2``,
  ho_match_mp_tac exp_pat_ind >> simp[] >>
  conj_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      conj_tac >- (
        Cases >> Cases >> simp[bind_pat_def,ADD1] ) >>
      Cases >> simp[] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    simp[SUBSET_DEF,MEM_FLAT,PULL_EXISTS,EVERY2_EVERY,EVERY_MEM,MEM_MAP] >> rw[] >>
    rfs[MEM_ZIP,PULL_EXISTS,MEM_EL] >>
    metis_tac[] ) >>
  conj_tac >- (
    rw[] >> rw[] >> simp[] ) >>
  conj_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      conj_tac >- (
        Cases >> Cases >> simp[bind_pat_def,ADD1] ) >>
      Cases >> simp[] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  conj_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> ntac 2 strip_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      conj_tac >- (
        Cases >> Cases >> simp[bind_pat_def,ADD1] ) >>
      Cases >> simp[] >> rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  rpt gen_tac >> ntac 2 strip_tac >>
  rfs[EVERY2_EVERY,EVERY_MEM] >>
  fs[MEM_ZIP,PULL_EXISTS] >>
  conj_tac >- (
    fs[MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
    simp[Once MEM_EL,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    last_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    discharge_hyps >- (
      simp[bindn_pat_thm,ADD1] >>
      rfs[MEM_EL,PULL_EXISTS] >>
      rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
  gen_tac >> strip_tac >>
  qpat_assum`p ⇒ q`mp_tac >>
  discharge_hyps >- (
    fs[MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
    simp[bindn_pat_thm] >>
    rw[] >> res_tac >> fsrw_tac[ARITH_ss][ADD1] ) >>
  strip_tac >>
  res_tac >> simp[])

(*
  this is false since v_pat doesn't constrain the values in environments more
  than required by the expression
  so we add a closed_pat assumption to i2_Cv instead
val v_pat_closed = store_thm("v_pat_closed",
  ``∀v1 v2. v_pat v1 v2 ⇒ closed_pat v1 ⇒ closed_pat v2``,
  ho_match_mp_tac v_pat_ind >> simp[] >>
  conj_tac >- (
    rw[EVERY2_EVERY,EVERY_MEM] >>
    rfs[MEM_ZIP,PULL_EXISTS,MEM_EL] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once closed_pat_cases] >>
    simp[Once closed_pat_cases] >>
    strip_tac >>
    first_assum(mp_tac o MATCH_MP exp_pat_free_vars) >>
    discharge_hyps >- (
      simp[ADD1] >>
      Cases >> Cases >> simp[bind_pat_def,env_pat_def] ) >>
    simp[ADD1] >>
*)

val v_bv_def = Define`
  v_bv (genv,gtagenv,exh,pp) v bv ⇔
    ∃v1 v2 Cv.
    v_to_i1 genv v v1 ∧
    v_to_i2 gtagenv v1 v2 ∧
    i2_Cv exh v2 Cv ∧
    Cv_bv pp Cv bv`

val closed_top_def = Define`
  closed_top (envM,envC,envE) top ⇔
    FV_top top ⊆ IMAGE Short (set (MAP FST envE)) ∪ { Long m x | ∃e. lookup m envM = SOME e ∧ MEM x (MAP FST e) }`

val compile_top_thm = store_thm("compile_top_thm",
  ``∀ck env stm top res. evaluate_top ck env stm top res ⇒
     ∀rs types grd rs' bc bs bc0.
      env_rs env (FST stm) grd rs (bs with code := bc0) ∧
      (FST(FST(SND grd)) = FST (SND stm)) ∧
      (compile_top types rs top = (rs',Stop::bc)) ∧
      (IS_SOME types ⇒ set (new_top_vs top) ⊆ FDOM (THE types)) ∧
      closed_top env top ∧
      (bs.code = bc0 ++ REVERSE bc ++ [Stop]) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ck ∧ IS_SOME bs.clock ∧
      SND(SND res) ≠ Rerr Rtype_error
      ⇒
      case res of ((s,tdecls,mdecls),envC,env_or_err) =>
        ∃bs' grd'.
        bc_next^* bs bs' ∧
        bs'.pc = next_addr bs'.inst_length (bc0 ++ bc) ∧
        let (new_env,str) =
          case env_or_err of Rval(envM,envE) =>
            ((envM++FST env,merge_envC envC (FST(SND env)),envE ++ (SND(SND env))),
             (case types of NONE => "" | SOME types =>
              print_result types top envC env_or_err))
          | Rerr(Rraise _) =>
            (env,print_result (THE types) top envC env_or_err) in
        bs'.output = bs.output ++ str ∧
        env_rs new_env s grd' rs' bs'``,
  ho_match_mp_tac evaluate_top_ind >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >>
    simp[compile_top_def] >>
    Q.PAT_ABBREV_TAC`non = (none_tag,(X:tid_or_exn option))` >>
    Q.PAT_ABBREV_TAC`som = (some_tag,(X:tid_or_exn option))` >>
    strip_tac >>
    `∃m10 m20. rs.globals_env = (m10,m20)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    qspecl_then[`m10`,`m20`,`Tdec d`]mp_tac top_to_i1_correct >>
    PairCases_on`grd`>>PairCases_on`env`>>PairCases_on`s1`>>fs[env_rs_def] >>
    REWRITE_TAC[Once CONJ_COMM] >>
    REWRITE_TAC[Once (GSYM CONJ_ASSOC)] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    `∃v m1 m2 p1. top_to_i1 rs.next_global m10 m20 (Tdec d) = (v,m1,m2,p1)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    `rs.next_global = LENGTH grd0` by ( fs[good_globals_def] ) >> fs[] >>
    simp[Once evaluate_top_cases] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    disch_then(mp_tac o CONJUNCT1) >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    disch_then(qx_choosel_then[`s2_i1`,`new_genv`]strip_assume_tac) >>
    `∃c exh p. prompt_to_i2 rs.contags_env p1 = (c,exh,p)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      CONV_RULE (
        ONCE_REWRITE_CONV[CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[CONJ_COMM] THENC
        ONCE_REWRITE_CONV[GSYM CONJ_ASSOC] THENC
        ONCE_REWRITE_CONV[GSYM AND_IMP_INTRO]) prompt_to_i2_correct))) >>
    REWRITE_TAC[Once EQ_SYM_EQ] >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    REWRITE_TAC[Once (GSYM AND_IMP_INTRO)] >>
    disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[] >>
    disch_then(qx_choosel_then[`new_genv_i2`,`s2_i2`,`gtagenv2`]strip_assume_tac) >>
    `∃n e. prompt_to_i3 non som (LENGTH grd0) p = (n,e)` by simp[GSYM EXISTS_PROD] >> fs[] >>
    first_assum (mp_tac o (MATCH_MP (
      ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]
        prompt_to_i3_correct))) >>
    simp[] >>
    `LENGTH genv2 = LENGTH grd0` by (
      fs[to_i2_invariant_def] >>
      imp_res_tac genv_to_i2_LENGTH_EQ >>
      fs[] ) >>
    simp[] >>
    simp[Once result_to_i3_cases] >>
    strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_exh_correct)) >>
    simp[] >> strip_tac >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_pat_correct)) >>
    simp[result_to_exh_def] >>
    disch_then(qx_choosel_then[`res4`]strip_assume_tac) >>
    first_assum (mp_tac o MATCH_MP (CONJUNCT1 exp_to_Cexp_correct)) >>
    simp[] >>
    `∀x. env_to_exh x [] = []` by simp[v_to_exh_def] >> fs[] >>
    discharge_hyps_keep >- (
      conj_asm1_tac >- (
        specl_args_of_then``exp_to_pat``(CONJUNCT1 free_vars_pat_exp_to_pat)mp_tac >>
        simp[] >> disch_then match_mp_tac >>
        imp_res_tac free_vars_i2_prompt_to_i3 >>
        imp_res_tac free_vars_prompt_to_i2 >>
        imp_res_tac FV_top_to_i1 >>
        simp[] >>
        fs[closed_top_def,SUBSET_DEF,PULL_EXISTS] >>
        simp[EXTENSION] >> rw[] >>
        CCONTR_TAC >> fs[] >> res_tac >> fs[] >> rw[] >>
        fs[to_i1_invariant_def] >>
        imp_res_tac global_env_inv_inclusion >>
        fs[SUBSET_DEF]) >>
      simp[csg_closed_pat_def,map_count_store_genv_def,store_to_exh_def] >>
      conj_tac >- (
        (v_to_pat_closed |> CONJUNCT2 |> SIMP_RULE(srw_ss())[] |> match_mp_tac) >>
        (v_to_exh_closed |> CONJUNCT2 |> CONJUNCT1
         |> SIMP_RULE(srw_ss())[vs_to_exh_MAP] |> match_mp_tac) >>
        fs[to_i2_invariant_def] >>
        fs[Once s_to_i2_cases] >>
        fs[Once s_to_i2'_cases] >>
        (v_to_i2_closed |> CONJUNCT2 |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
        first_assum(match_exists_tac o concl) >> simp[] >>
        (v_to_i1_closed |> CONJUNCT2 |> CONJUNCT1 |> MP_CANON |> match_mp_tac) >>
        fs[to_i1_invariant_def] >>
        fs[Once s_to_i1_cases] >>
        fs[Once s_to_i1'_cases] >>
        first_assum(match_exists_tac o concl) >> simp[]) >>
      match_mp_tac genv_to_pat_closed >>
      match_mp_tac genv_to_exh_closed >>
      fs[to_i2_invariant_def] >>
      match_mp_tac (MP_CANON genv_to_i2_closed) >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      fs[to_i1_invariant_def] >>
      fs[Once s_to_i1_cases] >>
      fs[Once s_to_i1'_cases] >>
      match_mp_tac global_env_inv_closed >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      fs[closed_genv_def]) >>
    disch_then(qx_choosel_then[`Cres0`]strip_assume_tac) >>
    qpat_assum`X = Stop::bc`mp_tac >>
    specl_args_of_then``compile_Cexp`` compile_Cexp_thm mp_tac >>
    simp[] >> strip_tac >>
    first_assum(mp_tac o MATCH_MP (CONJUNCT1 Cevaluate_syneq)) >>
    simp[] >>
    Q.PAT_ABBREV_TAC`Cexp = exp_to_Cexp Z` >>
    (* Q.PAT_ABBREV_TAC`Csg = map_count_store_genv v_to_Cv X` >> *)
    qmatch_assum_abbrev_tac`closed_vlabs [] Csg bc0` >>
    disch_then(qspecl_then[`$=`,`Csg`,`[]`,`Cexp`]mp_tac) >>
    discharge_hyps >- (
      simp[syneq_exp_refl] >>
      fs[Abbr`Csg`,csg_rel_unpair,map_count_store_genv_def,store_to_exh_def] >>
      simp[MAP_MAP_o,optionTheory.OPTION_MAP_COMPOSE,combinTheory.o_DEF] >>
      simp[EVERY2_MAP] >>
      conj_tac >- (
        match_mp_tac EVERY2_MEM_MONO >>
        HINT_EXISTS_TAC >>
        simp[i2_Cv_def,UNCURRY,PULL_EXISTS] >>
        rpt gen_tac >> strip_tac >>
        pop_assum(qspec_then`exh`mp_tac) >>
        simp[Once FUNION_COMM] >> strip_tac >>
        first_assum(mp_tac o MATCH_MP v_pat_syneq) >>
        discharge_hyps >- (
          simp[] >>
          fs[csg_closed_pat_def,EVERY_MAP,EVERY_MEM] >>
          first_x_assum match_mp_tac >>
          simp[MEM_MAP,PULL_EXISTS] >>
          simp[Once FUNION_COMM] >>
          qexists_tac`FST x` >> simp[] >>
          imp_res_tac MEM_ZIP_MEM_MAP >>
          imp_res_tac EVERY2_LENGTH >> fs[] ) >>
        metis_tac[syneq_trans] ) >>
      match_mp_tac EVERY2_MEM_MONO >>
      HINT_EXISTS_TAC >>
      simp[i2_Cv_def,optionTheory.OPTREL_def,UNCURRY] >>
      Cases >> simp[PULL_EXISTS] >>
      strip_tac >> simp[] >>
      first_x_assum(qspec_then`exh`mp_tac) >>
      simp[Once FUNION_COMM] >> strip_tac >>
      first_assum(mp_tac o MATCH_MP v_pat_syneq) >>
      discharge_hyps >- (
        simp[] >>
        fs[csg_closed_pat_def,EVERY_MAP,EVERY_MEM] >>
        fs[MEM_MAP,PULL_EXISTS] >>
        first_x_assum(qspec_then`q`mp_tac) >>
        simp[Once FUNION_COMM] >>
        disch_then match_mp_tac >>
        imp_res_tac MEM_ZIP_MEM_MAP >>
        imp_res_tac EVERY2_LENGTH >> fs[] ) >>
      metis_tac[syneq_trans] ) >>
    strip_tac >>
    first_x_assum(fn th => first_assum (mp_tac o MATCH_MP (ONCE_REWRITE_RULE[GSYM AND_IMP_INTRO]th))) >>
    specl_args_of_then``compile_print_top``compile_print_top_thm mp_tac >>
    simp[] >>
    disch_then(qx_choose_then`bcp`strip_assume_tac) >>
    disch_then(qspecl_then[`grd3`,`bs with code := bc0 ++ c0 ++ code`,`bc0`,`bc0`]mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`Csg`] >>
      fs[Cenv_bs_def,s_refs_def,IS_SOME_EXISTS] ) >>
    strip_tac >>
    rator_x_assum`v_pat`mp_tac >>
    simp[v_to_exh_def] >> simp[Once v_pat_cases] >>
    strip_tac >> BasicProvers.VAR_EQ_TAC >>
    rpt (
      qpat_assum`syneq (X Y) Z`mp_tac >>
      simp[Once syneq_cases] >> strip_tac >>
      BasicProvers.VAR_EQ_TAC ) >>
    strip_tac >>
    rator_x_assum`code_for_push`mp_tac >>
    simp[code_for_push_def,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    rator_x_assum`Cv_bv`mp_tac >>
    simp[Once Cv_bv_cases] >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[Abbr`bs0`,Abbr`bs1`,bc_state_component_equality] >>
      rw[] ) >>
    first_x_assum(qspec_then`bs1 with code := bs.code`mp_tac) >>
    simp[] >> BasicProvers.VAR_EQ_TAC >> simp[] >>
    simp[Abbr`bs1`] >>
    simp[Abbr`non`] >>
    disch_then(qspec_then`MAP (λv. THE (EL (m2 ' v) gv)) (new_dec_vs d)`mp_tac) >>
    discharge_hyps_keep >- (
      conj_tac >- (
        fs[good_labels_def,between_labels_def,FILTER_APPEND,ALL_DISTINCT_APPEND
          ,MEM_FILTER,is_Label_rwt,PULL_EXISTS,EVERY_FILTER,EVERY_MEM,PULL_FORALL
          ,MEM_MAP,between_def] >>
        rw[] >> res_tac >> fsrw_tac[ARITH_ss][] >>
        spose_not_then strip_assume_tac >> res_tac >> fsrw_tac[ARITH_ss][] ) >>
      rw[IS_SOME_EXISTS] >>
      last_x_assum mp_tac >>
      Cases_on`d`>>fs[] >>
      simp[Once evaluate_dec_cases,PULL_EXISTS] >>
      simp[libTheory.emp_def,FST_triple] >>
      simp[build_rec_env_MAP] >>
      rpt gen_tac >> strip_tac >>
      simp[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,PULL_EXISTS,EL_MAP] >>
      simp[FLOOKUP_DEF,compilerLibTheory.el_check_def] >>
      gen_tac >> strip_tac >>
      rator_x_assum`to_i1_invariant`mp_tac >>
      simp[to_i1_invariant_def] >>
      simp[Once v_to_i1_cases] >>
      simp[Once v_to_i1_cases] >>
      fs[libTheory.emp_def] >>
      simp[libPropsTheory.lookup_append] >>
      (Q.PAT_ABBREV_TAC`pv:string = EL n X` ORELSE
       Q.PAT_ABBREV_TAC`pv:string = FST(EL n X)`) >>
      disch_then(qspec_then`pv`mp_tac o CONJUNCT1 o CONJUNCT1) >>
      (BasicProvers.CASE_TAC >- (
         imp_res_tac libPropsTheory.lookup_notin >>
         imp_res_tac pmatch_dom >>
         fs[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,MEM_MAP,PULL_EXISTS] >>
         metis_tac[MEM_EL,EL_MAP,LENGTH_MAP] )) >>
      simp[FLOOKUP_DEF] >> strip_tac >> simp[] >>
      `LENGTH gv = LENGTH grd0 + LENGTH new_genv` by (
        fs[gvrel_def,Cenv_bs_def,s_refs_def] >>
        fs[csg_rel_unpair,map_count_store_genv_def] >>
        imp_res_tac EVERY2_LENGTH >> fs[] >> rw[] >>
        fs[Abbr`Csg`,store_to_exh_def] >>
        rator_x_assum`to_i2_invariant`mp_tac >>
        simp[to_i2_invariant_def] >> strip_tac >>
        imp_res_tac genv_to_i2_LENGTH_EQ >> fs[] >>
        metis_tac[] ) >>
      simp[] >>
      fs[gvrel_def,Cenv_bs_def,s_refs_def] >>
      qpat_assum`LIST_REL R X gv`mp_tac >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] >> strip_tac >>
      disch_then(qspec_then`m2 ' pv`mp_tac) >> simp[] >>
      (reverse strip_tac >- ( simp[] >> metis_tac[Cv_bv_can_Print] )) >>
      fs[csg_rel_unpair,map_count_store_genv_def] >>
      pop_assum kall_tac >> pop_assum mp_tac >> simp[] >>
      qmatch_abbrev_tac`EL nn l2 ≠ NONE` >>
      imp_res_tac EVERY2_LENGTH >> fs[store_to_exh_def] >>
      qpat_assum`LIST_REL R X l2`mp_tac >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] >>
      disch_then(qspec_then`nn`mp_tac) >> simp[] >>
      reverse strip_tac >> simp[] >>
      pop_assum kall_tac >> pop_assum mp_tac >> simp[Abbr`l2`] >>
      qmatch_abbrev_tac`EL nn l2 ≠ NONE` >>
      qpat_assum`LIST_REL R X l2`mp_tac >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] >>
      disch_then(qspec_then`nn`mp_tac) >> simp[] >>
      reverse strip_tac >> simp[] >>
      pop_assum kall_tac >> pop_assum mp_tac >> simp[Abbr`l2`] >>
      qmatch_abbrev_tac`EL nn l2 ≠ NONE` >>
      qpat_assum`LIST_REL R X l2`mp_tac >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] >>
      disch_then(qspec_then`nn`mp_tac) >> simp[] >>
      reverse strip_tac >> simp[] >>
      pop_assum kall_tac >> pop_assum mp_tac >> simp[Abbr`l2`] >>
      simp[EL_MAP] >>
      qmatch_abbrev_tac`EL nn l2 ≠ NONE` >>
      qpat_assum`LIST_REL R X l2`mp_tac >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] >>
      disch_then(qspec_then`nn`mp_tac) >> simp[] >>
      reverse strip_tac >> simp[] >>
      pop_assum kall_tac >> pop_assum mp_tac >> simp[Abbr`l2`] >>
      REWRITE_TAC[GSYM MAP_APPEND] >> simp[EL_MAP] >>
      rator_x_assum`to_i2_invariant`mp_tac >>
      simp[to_i2_invariant_def] >> strip_tac >>
      imp_res_tac genv_to_i2_LIST_REL >>
      pop_assum mp_tac >>
      simp[EVERY2_EVERY,GSYM AND_IMP_INTRO,EVERY_MEM,MEM_ZIP,PULL_EXISTS] >>
      simp[optionTheory.OPTREL_def] >>
      disch_then(qspec_then`nn`mp_tac) >> simp[] >>
      strip_tac >> simp[] ) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1' bs2` >>
    `bs1' = bs1` by (
      simp[Abbr`bs1`,Abbr`bs1'`] >>
      simp[REVERSE_APPEND] ) >>
    qexists_tac`bs2` >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    conj_tac >- (
      simp[Abbr`bs2`,SUM_APPEND,FILTER_APPEND,SUM_REVERSE,FILTER_REVERSE,MAP_REVERSE] ) >>
    conj_tac >- (
      simp[Abbr`bs2`] >>
      simp[optionTheory.option_case_compute] >>
      simp[print_result_def] >>
      Q.PAT_ABBREV_TAC`b = IS_SOME Z` >>
      Cases_on`b = F` >> simp[] >>
      qunabbrev_tac`b` >>
      fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
      last_x_assum mp_tac >>
      BasicProvers.CASE_TAC >>
      simp[Once evaluate_dec_cases] >>
      simp[libTheory.emp_def] >> strip_tac >>
      simp[print_envC_def,Q.SPECL[`X`,`[]`]print_envE_def,libTheory.bind_def] >>
      cheat ) >>
    simp[EXISTS_PROD,libTheory.emp_def,merge_envC_def,libTheory.merge_def] >>
    PairCases_on`s2` >> simp[env_rs_def] >>
    cheat) >> cheat)

(*
val compile_top_divergence = store_thm("compile_top_divergence",
  ``∀menv cenv s env top rs rd ck types bc0 bs ss sf code. (∀res. ¬evaluate_top menv cenv s env top res) ∧
      closed_top menv cenv s env top
      ∧ (∀mn spec ds. top = Tmod mn spec ds ⇒
          ∀i. i < LENGTH ds ⇒
            (∀tds. (EL i ds = Dtype tds) ⇒ check_dup_ctors (SOME mn) (decs_to_cenv (SOME mn) (TAKE i ds) ++ cenv) tds) ∧
            (∀cn ts. (EL i ds = Dexn cn ts) ⇒ mk_id (SOME mn) cn ∉ set (MAP FST (decs_to_cenv (SOME mn) (TAKE i ds) ++ cenv)))) ∧
      env_rs menv cenv (ck,s) env rs (LENGTH bs.stack) rd (bs with code := bc0) ∧
      (compile_top types rs top = (ss,sf,code)) ∧
      bs.code = bc0 ++ REVERSE code ∧
      bs.pc = next_addr bs.inst_length bc0 ∧
      IS_SOME bs.clock ∧
      good_labels rs.rnext_label bc0
      ⇒
      ∃bs'. bc_next^* bs bs' ∧ bc_fetch bs' = SOME Tick ∧ bs'.clock = SOME 0 ∧ bs'.output = bs.output``,
  rw[closed_top_def] >>
  Cases_on`top`>- (
    fs[Once evaluate_top_cases] >>
    qmatch_assum_rename_tac`compile_top types rs (Tmod mn specs ds) = X`["X"] >>
    Cases_on`∃r. evaluate_decs (SOME mn) menv cenv s env ds r`>>fs[]>-(
      PairCases_on`r`>>fs[]>>
      Cases_on`r2`>>fs[]>>
      TRY(PairCases_on`a`)>>fs[FORALL_PROD]>>
      metis_tac[] ) >>
    qabbrev_tac`p = compile_decs_wrap (SOME mn) rs ds` >>
    PairCases_on`p` >>
    fs[compile_top_def,LET_THM] >>
    fs[FOLDL_emit_thm] >>
    qspecl_then[`SOME mn`,`menv`,`cenv`,`s`,`env`,`ds`,`rs`]mp_tac compile_decs_wrap_divergence >>
    simp[] >>
    qmatch_assum_abbrev_tac`pc ++ p4.out = code` >>
    disch_then(qspecl_then[`ck`,`bs with code := bc0 ++ REVERSE p4.out`,`bc0`]mp_tac) >>
    simp[] >>
    disch_then(qspecl_then[`rd`]mp_tac) >>
    simp[] >>
    discharge_hyps >- metis_tac[] >>
    disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      simp[bc_state_component_equality,Abbr`bs0`] >>
      BasicProvers.VAR_EQ_TAC >> simp[] >>
      imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
    HINT_EXISTS_TAC >> simp[] >>
    fs[bc_fetch_def] >>
    BasicProvers.VAR_EQ_TAC >>
    imp_res_tac RTC_bc_next_preserves >> fs[] >>
    simp[REVERSE_APPEND] >>
    match_mp_tac bc_fetch_aux_append_code >>
    simp[] ) >>
  fs[Once evaluate_top_cases] >>
  Cases_on`∃r. evaluate_decs NONE menv cenv s env [d] r`>>fs[]>-(
    `∃res. r = (FST r,(case res of Rval (x,y) => x | Rerr _ => []),map_result SND res)` by (
      PairCases_on`r`>>simp[]>>
      Cases_on`r2` >- (
        qexists_tac`Rval (r1,a)` >> simp[] ) >>
      qexists_tac`Rerr e` >> simp[] >>
      Cases_on`d`>>fs[Once evaluate_decs_cases,libTheory.emp_def,libTheory.merge_def] >>
      fs[Once evaluate_decs_cases,libTheory.merge_def,libTheory.emp_def] >>
      fs[Once evaluate_dec_cases,libTheory.merge_def,libTheory.emp_def] >>
      fs[semanticPrimitivesTheory.combine_dec_result_def] ) >>
    `evaluate_dec NONE menv cenv s env d (FST r,res)` by metis_tac[evaluate_dec_decs] >>
    Cases_on`res`>>fs[] >>
    TRY(PairCases_on`a`)>>fs[FORALL_PROD]>>
    metis_tac[] ) >>
  qabbrev_tac`p = compile_decs_wrap NONE rs [d]` >>
  PairCases_on`p` >>
  fs[compile_top_def,LET_THM] >>
  qspecl_then[`NONE`,`menv`,`cenv`,`s`,`env`,`[d]`,`rs`]mp_tac compile_decs_wrap_divergence >>
  simp[] >>
  qspecl_then[`d`,`types`,`p4`]mp_tac compile_print_dec_thm >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`code = pc ++ p4.out` >>
  disch_then(qspecl_then[`ck`,`bs with code := bc0 ++ REVERSE p4.out`,`bc0`]mp_tac) >>
  simp[] >>
  disch_then(qspecl_then[`rd`]mp_tac) >>
  simp[FV_decs_def] >>
  discharge_hyps >- (
    simp[decs_to_cenv_def,decs_cns_def] >> rw[] >>
    fs[Once evaluate_dec_cases] >>
    spose_not_then strip_assume_tac >> fs[] >>
    fs[Once evaluate_decs_cases] >>
    fs[Once evaluate_dec_cases] >>
    metis_tac[ALOOKUP_NONE]) >>
  disch_then(qx_choosel_then[`bs1`]strip_assume_tac) >>
  `bc_next^* bs (bs1 with code := bs.code)` by (
    match_mp_tac RTC_bc_next_append_code >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    map_every qexists_tac[`bs0`,`bs1`] >>
    simp[bc_state_component_equality,Abbr`bs0`] >>
    BasicProvers.VAR_EQ_TAC >> simp[] >>
    imp_res_tac RTC_bc_next_preserves >> fs[] ) >>
  HINT_EXISTS_TAC >> simp[] >>
  fs[bc_fetch_def] >>
  BasicProvers.VAR_EQ_TAC >>
  imp_res_tac RTC_bc_next_preserves >> fs[] >>
  simp[REVERSE_APPEND] >>
  match_mp_tac bc_fetch_aux_append_code >>
  simp[] )
*)

val _ = export_theory()
