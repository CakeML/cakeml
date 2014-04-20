open HolKernel boolLib bossLib lcsymtacs pred_setTheory arithmeticTheory listTheory pairTheory finite_mapTheory rich_listTheory
open miscLib miscTheory astTheory terminationTheory
open modLangTheory conLangTheory decLangTheory exhLangTheory
open modLangProofTheory conLangProofTheory exhLangProofTheory compilerTerminationTheory
open patLangProofTheory

val _ = new_theory"free_vars"

val IS_SOME_EXISTS = store_thm("IS_SOME_EXISTS",
  ``∀opt. IS_SOME opt ⇔ ∃x. opt = SOME x``,
  Cases >> simp[])

val FDOM_FOLDR_DOMSUB = store_thm("FDOM_FOLDR_DOMSUB",
  ``∀ls fm. FDOM (FOLDR (λk m. m \\ k) fm ls) = FDOM fm DIFF set ls``,
  Induct >> simp[] >>
  ONCE_REWRITE_TAC[EXTENSION] >>
  simp[] >> metis_tac[])

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

val env_to_exh_MAP = store_thm("env_to_exh_MAP",
  ``∀exh env. env_to_exh exh env = MAP (λ(x,e). (x, v_to_exh exh e)) env``,
  Induct_on`env`>>simp[v_to_exh_def] >> Cases >> simp[v_to_exh_def])

val alloc_defs_GENLIST = store_thm("alloc_defs_GENLIST",
  ``∀n ls. alloc_defs n ls = ZIP(ls,GENLIST(λx. x + n)(LENGTH ls))``,
  Induct_on`ls`>>simp[alloc_defs_def,GENLIST_CONS] >>
  simp[combinTheory.o_DEF,ADD1])

val pats_bindings_i2_MAP_Pvar_i2 = store_thm("pats_bindings_i2_MAP_Pvar_i2",
  ``∀ls ly. set (pats_bindings_i2 (MAP Pvar_i2 ls) ly) = set ls ∪ set ly``,
  Induct >> simp[pat_bindings_i2_def,EXTENSION] >> metis_tac[])

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

val _ = export_theory()
