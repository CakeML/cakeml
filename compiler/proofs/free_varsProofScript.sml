open HolKernel boolLib bossLib lcsymtacs pred_setTheory arithmeticTheory listTheory pairTheory finite_mapTheory rich_listTheory
open miscLib miscTheory boolSimps bigStepTheory astTheory semanticPrimitivesTheory libTheory terminationTheory evalPropsTheory
open modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory toIntLangTheory compilerTerminationTheory
open free_varsTheory modLangProofTheory conLangProofTheory exhLangProofTheory patLangProofTheory
val _ = new_theory"free_varsProof"

(* TODO: move? *)
val vs_to_i1_MAP = store_thm("vs_to_i1_MAP",
  ``∀g vs1 vs2. vs_to_i1 g vs1 vs2 ⇔ LIST_REL (v_to_i1 g) vs1 vs2``,
  gen_tac >> Induct >> simp[Once v_to_i1_cases])
val vs_to_i2_MAP = store_thm("vs_to_i2_MAP",
  ``∀g vs1 vs2. vs_to_i2 g vs1 vs2 ⇔ LIST_REL (v_to_i2 g) vs1 vs2``,
  gen_tac >> Induct >> simp[Once v_to_i2_cases])
val vs_to_exh_MAP = store_thm("vs_to_exh_MAP",
  ``∀exh vs1 vs2. vs_to_exh exh vs1 vs2 = LIST_REL (v_to_exh exh) vs1 vs2``,
  Induct_on`vs1`>>simp[Once v_to_exh_cases])
val env_to_exh_MAP = store_thm("env_to_exh_MAP",
  ``∀exh env1 env2. env_to_exh exh env1 env2 ⇔ MAP FST env1 = MAP FST env2 ∧
      LIST_REL (v_to_exh exh) (MAP SND env1) (MAP SND env2)``,
  Induct_on`env1`>>simp[Once v_to_exh_cases] >>
  Cases >> Cases_on`env2` >> rw[] >>
  Cases_on`h`>>rw[] >> metis_tac[])
val sv_to_i1_sv_rel = store_thm("sv_to_i1_sv_rel",
  ``∀g. sv_to_i1 g = sv_rel (v_to_i1 g)``,
  rw[FUN_EQ_THM,sv_to_i1_cases,EQ_IMP_THM,sv_rel_cases,vs_to_i1_MAP])
val sv_to_i2_sv_rel = store_thm("sv_to_i2_sv_rel",
  ``∀g. sv_to_i2 g = sv_rel (v_to_i2 g)``,
  rw[FUN_EQ_THM,sv_to_i2_cases,EQ_IMP_THM,sv_rel_cases,vs_to_i2_MAP])
(* -- *)

val v_to_pat_closed = store_thm("v_to_pat_closed",
  ``(∀v. closed_exh v ⇒ closed_pat (v_to_pat v)) ∧
    (∀vs. EVERY closed_exh vs ⇒  EVERY closed_pat (vs_to_pat vs))``,
  ho_match_mp_tac v_to_pat_ind >>
  simp[] >>
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

val v_to_exh_closed = store_thm("v_to_exh_closed",
  ``(∀exh v1 v2. v_to_exh exh v1 v2 ⇒ closed_i2 v1 ⇒ closed_exh v2) ∧
    (∀exh v1 v2. vs_to_exh exh v1 v2 ⇒ EVERY closed_i2 v1 ⇒ EVERY closed_exh v2) ∧
    (∀exh v1 v2. env_to_exh exh v1 v2 ⇒ EVERY closed_i2 (MAP SND v1) ⇒ EVERY closed_exh (MAP SND v2))``,
  ho_match_mp_tac v_to_exh_strongind >> rw[]
  >- (
    simp[Once closed_exh_cases] >>
    pop_assum mp_tac >>
    simp[Once closed_i2_cases] >>
    fs[env_to_exh_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] ) >>
  simp[Once closed_exh_cases] >>
  pop_assum mp_tac >>
  simp[Once closed_i2_cases] >>
  fs[funs_to_exh_MAP,EVERY_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,ETA_AX] >>
  fs[LAMBDA_PROD,env_to_exh_MAP,MAP_MAP_o,UNCURRY,combinTheory.o_DEF,FST_pair])

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
  discharge_hyps >- metis_tac[find_recfun_lookup,alistTheory.ALOOKUP_MEM] >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >>
  qx_gen_tac`z` >> strip_tac >>
  first_x_assum(qspec_then`Short z`mp_tac) >>
  simp[] >>
  fs[FDOM_FUPDATE_LIST] >>
  rw[] >>
  fs[FLOOKUP_DEF,FDOM_FUPDATE_LIST] >>
  metis_tac[SUBSET_DEF] )

val genv_to_pat_closed = store_thm("genv_to_pat_closed",
  ``∀genv2.
    EVERY (OPTION_EVERY closed_exh) genv2 ⇒
    EVERY (OPTION_EVERY closed_pat)
      (MAP (OPTION_MAP v_to_pat) genv2)``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  Cases >> simp[] >> strip_tac >>
  res_tac >> fs[] >>
  metis_tac[v_to_pat_closed])

val genv_to_exh_closed = store_thm("genv_to_exh_closed",
  ``∀exh genv2 genvh.
    EVERY (OPTION_EVERY closed_i2) genv2 ∧
    LIST_REL (OPTREL (v_to_exh exh)) genv2 genvh
    ⇒
    EVERY (OPTION_EVERY closed_exh) genvh``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM AND_IMP_INTRO] >>
  simp[MEM_EL,PULL_EXISTS] >>
  rpt gen_tac >> rpt strip_tac >>
  res_tac >> fs[] >> res_tac >>
  fs[optionTheory.OPTREL_def] >>
  rfs[] >>
  metis_tac[v_to_exh_closed,OPTION_EVERY_def])

val genv_to_i2_closed = store_thm("genv_to_i2_closed",
  ``∀g x y.
    EVERY (OPTION_EVERY closed_i1) x ∧
    LIST_REL (OPTREL (v_to_i2 g)) x y
    ⇒ EVERY (OPTION_EVERY closed_i2) y``,
  simp[EVERY_MEM,MEM_MAP,PULL_EXISTS,EVERY2_EVERY,EVERY_MEM,MEM_ZIP,GSYM AND_IMP_INTRO] >>
  simp[MEM_EL,PULL_EXISTS] >>
  rpt gen_tac >> rpt strip_tac >>
  res_tac >> fs[] >> res_tac >>
  fs[optionTheory.OPTREL_def] >>
  rfs[] >>
  metis_tac[v_to_i2_closed,OPTION_EVERY_def])

val global_env_inv_inclusion = store_thm("global_env_inv_inclusion",
  ``∀genv mods tops menv s env.
     global_env_inv genv mods tops menv s env ⇒
     set (MAP FST env) DIFF s ⊆ FDOM tops ∧
     set (MAP FST menv) ⊆ FDOM mods``,
  rw[Once v_to_i1_cases,SUBSET_DEF] >>
  TRY (
    (alistTheory.ALOOKUP_NONE
     |> SPEC_ALL |> EQ_IMP_RULE |> fst
     |> CONTRAPOS
     |> SIMP_RULE std_ss []
     |> imp_res_tac) >>
    fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
    res_tac >> fs[FLOOKUP_DEF] >> NO_TAC) >>
  last_x_assum mp_tac >>
  simp[Once v_to_i1_cases] >> strip_tac >>
  (alistTheory.ALOOKUP_NONE
   |> SPEC_ALL |> EQ_IMP_RULE |> fst
   |> CONTRAPOS
   |> SIMP_RULE std_ss []
   |> imp_res_tac) >>
  fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS] >>
  res_tac >> fs[FLOOKUP_DEF] >> NO_TAC)

val global_env_inv_closed = store_thm("global_env_inv_closed",
  ``∀genv mods tops menv s env.
    global_env_inv genv mods tops menv s env ∧
    EVERY closed (MAP SND env) ∧
    EVERY closed (MAP SND (FLAT (MAP SND menv))) ∧
    (∀n. n < LENGTH genv ∧ IS_SOME (EL n genv) ⇒
         (∃x. x ∉ s ∧ IS_SOME (ALOOKUP env x) ∧ FLOOKUP tops x = SOME n) ∨
         (∃mn ee e x.
           ALOOKUP menv mn = SOME ee ∧
           IS_SOME (ALOOKUP ee x) ∧
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
    metis_tac[v_to_i1_closed,alistTheory.ALOOKUP_MEM, MEM_MAP, FST, SND] ) >>
  first_x_assum(qspec_then`mn`mp_tac) >> simp[] >>
  simp[Once v_to_i1_cases] >>
  disch_then(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  simp[] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  fs[EVERY_MEM,MAP_FLAT,MEM_MAP,PULL_EXISTS,MEM_FLAT] >>
  metis_tac [pair_CASES, SND, v_to_i1_closed])

val _ = export_theory()
