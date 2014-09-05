open HolKernel boolLib bossLib lcsymtacs pred_setTheory arithmeticTheory listTheory pairTheory finite_mapTheory rich_listTheory
open miscLib miscTheory boolSimps bigStepTheory astTheory semanticPrimitivesTheory libTheory terminationTheory evalPropsTheory
open modLangTheory conLangTheory decLangTheory exhLangTheory patLangTheory toIntLangTheory compilerTerminationTheory
open modLangProofTheory conLangProofTheory exhLangProofTheory patLangProofTheory

val _ = new_theory"free_vars"

(* TODO: move? *)

val do_app_cases = store_thm("do_app_cases",
  ``do_app s op vs = SOME x ⇒
    (∃z n1 n2. op = Opn z ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃z n1 n2. op = Opb z ∧ vs = [Litv (IntLit n1); Litv (IntLit n2)]) ∨
    (∃v1 v2. op = Equality ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = Opassign ∧ vs = [Loc lnum; v]) ∨
    (∃n. op = Opderef ∧ vs = [Loc n]) ∨
    (∃v. op = Opref ∧ vs = [v]) ∨
    (∃n w. op = Aw8alloc ∧ vs = [Litv (IntLit n); Litv (Word8 w)]) ∨
    (∃lnum i. op = Aw8sub ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = Aw8length ∧ vs = [Loc n]) ∨
    (∃lnum i w. op = Aw8update ∧ vs = [Loc lnum; Litv (IntLit i); Litv (Word8 w)]) ∨
    (∃v ls. op = VfromList ∧ vs = [v] ∧ v_to_list v = SOME ls) ∨
    (∃ls i. op = Vsub ∧ vs = [Vectorv ls; Litv (IntLit i)]) ∨
    (∃ls. op = Vlength ∧ vs = [Vectorv ls]) ∨
    (∃n v. op = Aalloc ∧ vs = [Litv (IntLit n); v]) ∨
    (∃lnum i. op = Asub ∧ vs = [Loc lnum; Litv (IntLit i)]) ∨
    (∃n. op = Alength ∧ vs = [Loc n]) ∨
    (∃lnum i v. op = Aupdate ∧ vs = [Loc lnum; Litv (IntLit i); v])``,
  rw[do_app_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val do_app_i1_cases = store_thm("do_app_i1_cases",
  ``do_app_i1 s op vs = SOME x ⇒
    (∃z n1 n2. op = Opn z ∧ vs = [Litv_i1 (IntLit n1); Litv_i1 (IntLit n2)]) ∨
    (∃z n1 n2. op = Opb z ∧ vs = [Litv_i1 (IntLit n1); Litv_i1 (IntLit n2)]) ∨
    (∃v1 v2. op = Equality ∧ vs = [v1; v2]) ∨
    (∃lnum v. op = Opassign ∧ vs = [Loc_i1 lnum; v]) ∨
    (∃n. op = Opderef ∧ vs = [Loc_i1 n]) ∨
    (∃v. op = Opref ∧ vs = [v]) ∨
    (∃n w. op = Aw8alloc ∧ vs = [Litv_i1 (IntLit n); Litv_i1 (Word8 w)]) ∨
    (∃lnum i. op = Aw8sub ∧ vs = [Loc_i1 lnum; Litv_i1 (IntLit i)]) ∨
    (∃n. op = Aw8length ∧ vs = [Loc_i1 n]) ∨
    (∃lnum i w. op = Aw8update ∧ vs = [Loc_i1 lnum; Litv_i1 (IntLit i); Litv_i1 (Word8 w)]) ∨
    (∃v ls. op = VfromList ∧ vs = [v] ∧ v_to_list_i1 v = SOME ls) ∨
    (∃ls i. op = Vsub ∧ vs = [Vectorv_i1 ls; Litv_i1 (IntLit i)]) ∨
    (∃ls. op = Vlength ∧ vs = [Vectorv_i1 ls]) ∨
    (∃n v. op = Aalloc ∧ vs = [Litv_i1 (IntLit n); v]) ∨
    (∃lnum i. op = Asub ∧ vs = [Loc_i1 lnum; Litv_i1 (IntLit i)]) ∨
    (∃n. op = Alength ∧ vs = [Loc_i1 n]) ∨
    (∃lnum i v. op = Aupdate ∧ vs = [Loc_i1 lnum; Litv_i1 (IntLit i); v])``,
  rw[do_app_i1_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val vs_to_i1_MAP = store_thm("vs_to_i1_MAP",
  ``∀g vs1 vs2. vs_to_i1 g vs1 vs2 ⇔ LIST_REL (v_to_i1 g) vs1 vs2``,
  gen_tac >> Induct >> simp[Once v_to_i1_cases])
val vs_to_i2_MAP = store_thm("vs_to_i2_MAP",
  ``∀g vs1 vs2. vs_to_i2 g vs1 vs2 ⇔ LIST_REL (v_to_i2 g) vs1 vs2``,
  gen_tac >> Induct >> simp[Once v_to_i2_cases])
val vs_to_exh_MAP = store_thm("vs_to_exh_MAP",
  ``∀exh vs1 vs2. vs_to_exh exh vs1 vs2 = LIST_REL (v_to_exh exh) vs1 vs2``,
  Induct_on`vs1`>>simp[Once v_to_exh_cases])

val exps_to_i1_MAP = store_thm("exps_to_i1_MAP",
  ``∀es. exps_to_i1 a b es = MAP (exp_to_i1 a b) es``,
  Induct >> simp[exp_to_i1_def])
val exps_to_i2_MAP = store_thm("exps_to_i2_MAP",
  ``∀es. exps_to_i2 a es = MAP (exp_to_i2 a) es``,
  Induct >> simp[exp_to_i2_def])
val exps_to_exh_MAP = store_thm("exps_to_exh_MAP",
  ``∀es. exps_to_exh a es = MAP (exp_to_exh a) es``,
  Induct >> simp[exp_to_exh_def])
val exps_to_pat_MAP = store_thm("exps_to_pat_MAP",
  ``∀es. exps_to_pat a es = MAP (exp_to_pat a) es``,
  Induct >> simp[exp_to_pat_def])

val env_to_exh_MAP = store_thm("env_to_exh_MAP",
  ``∀exh env1 env2. env_to_exh exh env1 env2 ⇔ MAP FST env1 = MAP FST env2 ∧
      LIST_REL (v_to_exh exh) (MAP SND env1) (MAP SND env2)``,
  Induct_on`env1`>>simp[Once v_to_exh_cases] >>
  Cases >> Cases_on`env2` >> rw[] >>
  Cases_on`h`>>rw[] >> metis_tac[])

val build_rec_env_MAP = store_thm("build_rec_env_MAP",
  ``build_rec_env funs cle env = MAP (λ(f,cdr). (f, (Recclosure cle funs f))) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val build_rec_env_i1_MAP = store_thm("build_rec_env_i1_MAP",
  ``build_rec_env_i1 funs cle env = MAP (λ(f,cdr). (f, (Recclosure_i1 cle funs f))) funs ++ env``,
  rw[build_rec_env_i1_def] >>
  qho_match_abbrev_tac `FOLDR (f funs) env funs = MAP (g funs) funs ++ env` >>
  qsuff_tac `∀funs env funs0. FOLDR (f funs0) env funs = MAP (g funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[libTheory.bind_def] >>
  PairCases_on`h` >> rw[])

val free_vars_defs_exh_MAP = store_thm("free_vars_defs_exh_MAP",
  ``∀ds. free_vars_defs_exh ds = BIGUNION (set (MAP (λ(f,x,e). free_vars_exh e DIFF {x}) ds))``,
  Induct_on`ds`>>simp[] >> fs[EXTENSION] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[])

val alloc_defs_GENLIST = store_thm("alloc_defs_GENLIST",
  ``∀n ls. alloc_defs n ls = ZIP(ls,GENLIST(λx. x + n)(LENGTH ls))``,
  Induct_on`ls`>>simp[alloc_defs_def,GENLIST_CONS] >>
  simp[combinTheory.o_DEF,ADD1])

val pats_bindings_i2_MAP_Pvar_i2 = store_thm("pats_bindings_i2_MAP_Pvar_i2",
  ``∀ls ly. set (pats_bindings_i2 (MAP Pvar_i2 ls) ly) = set ls ∪ set ly``,
  Induct >> simp[pat_bindings_i2_def,EXTENSION] >> metis_tac[])

val sv_to_i1_sv_rel = store_thm("sv_to_i1_sv_rel",
  ``∀g. sv_to_i1 g = sv_rel (v_to_i1 g)``,
  rw[FUN_EQ_THM,sv_to_i1_cases,EQ_IMP_THM,sv_rel_cases,vs_to_i1_MAP])

val sv_to_i2_sv_rel = store_thm("sv_to_i2_sv_rel",
  ``∀g. sv_to_i2 g = sv_rel (v_to_i2 g)``,
  rw[FUN_EQ_THM,sv_to_i2_cases,EQ_IMP_THM,sv_rel_cases,vs_to_i2_MAP])

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

val (closed_exh_rules,closed_exh_ind,closed_exh_cases) = Hol_reln`
(closed_exh (Litv_exh l)) ∧
(EVERY (closed_exh) vs ⇒ closed_exh (Conv_exh cn vs)) ∧
(EVERY (closed_exh) (MAP SND env) ∧ free_vars_exh b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_exh (Closure_exh env x b)) ∧
(EVERY (closed_exh) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_exh e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_exh (Recclosure_exh env defs d)) ∧
(closed_exh (Loc_exh n)) ∧
(EVERY closed_exh vs ⇒ closed_exh (Vectorv_exh vs))`;

val closed_exh_lit_loc_conv = store_thm("closed_exh_lit_loc_conv",
  ``closed_exh (Litv_exh l) ∧ closed_exh (Loc_exh n) ∧
    (closed_exh (Conv_exh a bs) ⇔ EVERY closed_exh bs) ∧
    (closed_exh (Vectorv_exh bs) ⇔ EVERY closed_exh bs)``,
  rw[closed_exh_cases])
val _ = export_rewrites["closed_exh_lit_loc_conv"]

val free_vars_pat_def = tDefine"free_vars_pat"`
  free_vars_pat (Raise_pat e) = free_vars_pat e ∧
  free_vars_pat (Handle_pat e1 e2) = lunion (free_vars_pat e1) (lshift 1 (free_vars_pat e2)) ∧
  free_vars_pat (Lit_pat _) = [] ∧
  free_vars_pat (Con_pat _ es) = free_vars_list_pat es ∧
  free_vars_pat (Var_local_pat n) = [n] ∧
  free_vars_pat (Var_global_pat _) = [] ∧
  free_vars_pat (Fun_pat e) = lshift 1 (free_vars_pat e) ∧
  free_vars_pat (App_pat _ es) = free_vars_list_pat es ∧
  free_vars_pat (If_pat e1 e2 e3) = lunion (free_vars_pat e1) (lunion (free_vars_pat e2) (free_vars_pat e3)) ∧
  free_vars_pat (Let_pat e1 e2) = lunion (free_vars_pat e1) (lshift 1 (free_vars_pat e2)) ∧
  free_vars_pat (Seq_pat e1 e2) = lunion (free_vars_pat e1) (free_vars_pat e2) ∧
  free_vars_pat (Letrec_pat es e) = lunion (free_vars_defs_pat (LENGTH es) es) (lshift (LENGTH es) (free_vars_pat e)) ∧
  free_vars_pat (Extend_global_pat _) = [] ∧
  free_vars_list_pat [] = [] ∧
  free_vars_list_pat (e::es) = lunion (free_vars_pat e) (free_vars_list_pat es) ∧
  free_vars_defs_pat _ [] = [] ∧
  free_vars_defs_pat n (e::es) = lunion (lshift (n+1) (free_vars_pat e)) (free_vars_defs_pat n es)`
(WF_REL_TAC`inv_image $< (λx. case x of
  | INL e => exp_pat_size e
  | INR (INL es) => exp_pat1_size es
  | INR (INR (_,es)) => exp_pat1_size es)`)
val _ = export_rewrites["free_vars_pat_def"]

val free_vars_defs_pat_MAP = store_thm("free_vars_defs_pat_MAP",
  ``set (free_vars_defs_pat n es) = set (lshift (n+1) (free_vars_list_pat es))``,
  Induct_on`es`>>simp[] >> fs[EXTENSION] >>
  rw[EQ_IMP_THM] >> simp[] >> metis_tac[])

val free_vars_list_pat_MAP = store_thm("free_vars_list_pat_MAP",
  ``∀es. set (free_vars_list_pat es) = set (FLAT (MAP free_vars_pat es))``,
  Induct >> simp[])
val _ = export_rewrites["free_vars_defs_pat_MAP","free_vars_list_pat_MAP"]

val free_vars_pat_sIf = store_thm("free_vars_pat_sIf",
  ``∀e1 e2 e3. set (free_vars_pat (sIf_pat e1 e2 e3)) ⊆ set (free_vars_pat (If_pat e1 e2 e3))``,
  rw[sIf_pat_def] >>
  BasicProvers.CASE_TAC >> simp[SUBSET_DEF] >>
  BasicProvers.CASE_TAC >> simp[] >> rw[])

val free_vars_ground_pat = store_thm("free_vars_ground_pat",
  ``(∀e n. ground_pat n e ⇒ set (free_vars_pat e) ⊆ count n) ∧
    (∀es n. ground_list_pat n es ⇒ set (free_vars_list_pat es) ⊆ count n)``,
  ho_match_mp_tac(TypeBase.induction_of(``:exp_pat``)) >>
  simp[] >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  rw[] >> res_tac >>
  DECIDE_TAC)

val free_vars_pat_sLet = store_thm("free_vars_pat_sLet",
  ``∀e1 e2. set (free_vars_pat (sLet_pat e1 e2)) ⊆ set (free_vars_pat (Let_pat e1 e2))``,
  rw[sLet_pat_thm,SUBSET_DEF] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_ground_pat) >>
  fs[])

val free_vars_pat_Let_Els = store_thm("free_vars_pat_Let_Els",
  ``∀n k e. set (free_vars_pat (Let_Els_pat n k e)) ⊆ {x | x = n ∨ ∃y. MEM y (free_vars_pat e) ∧ k ≤ y ∧ x = y - k}``,
  ho_match_mp_tac Let_Els_pat_ind >>
  simp[Let_Els_pat_def,arithmeticTheory.ADD1,SUBSET_DEF] >>
  gen_tac >> Cases >> simp[Let_Els_pat_def] >> rw[] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet) >>
  fs[] >> simp[] >- metis_tac[] >>
  res_tac >> simp[] >>
  disj2_tac >> HINT_EXISTS_TAC >> simp[])

val free_vars_pat_to_pat = store_thm("free_vars_pat_to_pat",
  ``(∀p. set (free_vars_pat (pat_to_pat p)) ⊆ {0}) ∧
    (∀n ps. set (free_vars_pat (pats_to_pat n ps)) ⊆ {x | n ≤ x ∧ x < n + LENGTH ps})``,
  ho_match_mp_tac pat_to_pat_ind >>
  simp[pat_to_pat_def] >>
  strip_tac >- (
    simp[SUBSET_DEF] >>
    rpt strip_tac >>
    imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf) >> fs[] >>
    imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_Let_Els) >> fs[] >>
    res_tac >> simp[] ) >>
  strip_tac >- (
    simp[SUBSET_DEF] >>
    rpt strip_tac >>
    imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet) >> fs[] ) >>
  rw[SUBSET_DEF] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf) >> fs[] >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet) >> fs[] >>
  rw[] >> res_tac >> simp[])

val pat_bindings_exh_acc = store_thm("pat_bindings_exh_acc",
  ``(∀p acc. pat_bindings_exh p acc = pat_bindings_exh p [] ++ acc) ∧
    (∀ps acc. pats_bindings_exh ps acc = pats_bindings_exh ps [] ++ acc)``,
  ho_match_mp_tac(TypeBase.induction_of``:pat_exh``) >> rw[] >>
  simp_tac (srw_ss()) [Once pat_bindings_exh_def] >>
  simp_tac (srw_ss()) [Once pat_bindings_exh_def] >>
  metis_tac[APPEND_ASSOC])

val row_to_pat_pat_bindings = store_thm("row_to_pat_pat_bindings",
  ``(∀Nbvs p bvs2. Nbvs ≠ [] ∧ HD Nbvs = NONE ⇒ set (MAP SOME (pat_bindings_exh p [])) ⊆ set (FST (row_to_pat Nbvs p))) ∧
    (∀bvs n k ps bvsk N bvs0.
      bvs = bvsk ++ N::bvs0 ∧ LENGTH bvsk = n ⇒
      set (MAP SOME (pats_bindings_exh ps [])) ⊆ (set (FST (cols_to_pat bvs n k ps))))``,
  ho_match_mp_tac row_to_pat_ind >>
  simp[pat_bindings_exh_def,row_to_pat_def] >>
  rw[UNCURRY] >- (
    `∃x y z. row_to_pat (NONE::bvs) p = (x,y,z)` by simp[GSYM EXISTS_PROD] >>
    fs[LENGTH_NIL] >> Cases_on`Nbvs`>>fs[] ) >>
  `∃x y z. row_to_pat (NONE::(bvsk++[N]++bvs0)) p = (x,y,z)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  qspecl_then[`NONE::(bvsk++[N]++bvs0)`,`p`]mp_tac(CONJUNCT1 row_to_pat_acc) >>
  simp[] >> disch_then(qspec_then`bvsk++[N]++bvs0`mp_tac) >> simp[] >> strip_tac >>
  first_x_assum(qspec_then`ls++bvsk`mp_tac) >> simp[] >> strip_tac >>
  simp[Once pat_bindings_exh_acc] >>
  specl_args_of_then``cols_to_pat``(CONJUNCT2 row_to_pat_acc)mp_tac >>
  disch_then(qspec_then`ls++bvsk`mp_tac) >>
  simp[] >> disch_then(qspec_then`bvs0`mp_tac) >>
  `∃x a z. cols_to_pat (ls++bvsk++[N]++bvs0) (y+(LENGTH bvsk + 1)) (k + 1) ps = (x,a,z)` by simp[GSYM EXISTS_PROD] >> fs[] >>
  REWRITE_TAC[Once CONS_APPEND] >> simp[] >>
  REWRITE_TAC[Once CONS_APPEND] >> simp[] >>
  rw[] >> fs[SUBSET_DEF] >>
  metis_tac[])

val free_vars_row_to_pat = store_thm("free_vars_row_to_pat",
  ``(∀Nbvs p bvs' n f e. row_to_pat Nbvs p = (bvs',n,f) ⇒
      set (free_vars_pat (f e)) ⊆ {0} ∪ set (lshift n (free_vars_pat e))) ∧
    (∀bvs n k ps bvs' m f e. cols_to_pat bvs n k ps = (bvs',m,f) ⇒
      set (free_vars_pat (f e)) ⊆ {n} ∪ set (lshift m (free_vars_pat e)))``,
  ho_match_mp_tac row_to_pat_ind >>
  strip_tac >- simp[row_to_pat_def] >>
  strip_tac >- simp[row_to_pat_def] >>
  strip_tac >- ( simp[row_to_pat_def] ) >>
  strip_tac >- (
    simp[row_to_pat_def] >> rw[] >>
    `∃x y z. row_to_pat (NONE::Nbvs) p = (x,y,z)` by simp[GSYM EXISTS_PROD] >>
    fs[] >> rw[] >>
    match_mp_tac SUBSET_TRANS >>
    specl_args_of_then``sLet_pat``free_vars_pat_sLet assume_tac >>
    HINT_EXISTS_TAC >> simp[] >>
    fs[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
    res_tac >> fsrw_tac[ARITH_ss][] >>
    disj2_tac >> HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- simp[row_to_pat_def] >>
  strip_tac >- simp[row_to_pat_def] >>
  strip_tac >- simp[row_to_pat_def] >>
  simp[row_to_pat_def] >> rw[] >>
  `∃x y z. row_to_pat (NONE::bvs) p = (x,y,z)` by simp[GSYM EXISTS_PROD] >>
  fs[AC ADD_ASSOC ADD_COMM] >>
  `∃a b c. cols_to_pat x (n + (y + 1)) (k + 1) ps = (a,b,c)` by simp[GSYM EXISTS_PROD] >>
  fs[] >> rw[] >>
  match_mp_tac SUBSET_TRANS >>
  specl_args_of_then``sLet_pat``free_vars_pat_sLet assume_tac >>
  HINT_EXISTS_TAC >> simp[] >>
  fs[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
  res_tac >> fsrw_tac[ARITH_ss][] >>
  last_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  strip_tac >> fsrw_tac[ARITH_ss][] >>
  disj2_tac >> HINT_EXISTS_TAC >> simp[])

val free_vars_pat_exp_to_pat = store_thm("free_vars_pat_exp_to_pat",
  ``(∀ls e.
      IMAGE SOME (free_vars_exh e) ⊆ set ls ⇒
      set (free_vars_pat (exp_to_pat ls e)) ⊆ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_exh e)) ∧
    (∀ls es.
      IMAGE SOME (free_vars_list_exh es) ⊆ set ls ⇒
      set (free_vars_list_pat (exps_to_pat ls es)) ⊆ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_list_exh es)) ∧
    (∀ls funs.
      IMAGE SOME (free_vars_defs_exh funs) ⊆ set ls ⇒
      set (free_vars_list_pat (funs_to_pat ls funs)) ⊆
        {0} ∪ IMAGE (λx. THE (find_index (SOME x) ls 1)) (free_vars_defs_exh funs)) ∧
    (∀ls pes.
      IMAGE SOME (free_vars_pes_exh pes) ⊆ set ls ∧ ls ≠ [] ∧ (HD ls = NONE) ⇒
      set (free_vars_pat (pes_to_pat ls pes)) ⊆ {0} ∪ IMAGE (λx. THE (find_index (SOME x) ls 0)) (free_vars_pes_exh pes))``,
  ho_match_mp_tac exp_to_pat_ind >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >> strip_tac >> fs[find_index_def] >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    gen_tac >> strip_tac >- metis_tac[] >>
    res_tac >- fsrw_tac[ARITH_ss][] >>
    qpat_assum`m = X`mp_tac >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >>
    strip_tac >> fs[] >>
    metis_tac[optionTheory.THE_DEF] ) >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    simp[optionTheory.option_case_compute] >>
    rw[] >>
    metis_tac[find_index_NOT_MEM,optionTheory.IS_SOME_DEF,optionTheory.option_CASES] ) >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    simp[find_index_def] >>
    rpt gen_tac >> strip_tac >> strip_tac >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    gen_tac >> strip_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- metis_tac[] >>
    disch_then(qspec_then`m`mp_tac) >>
    simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    HINT_EXISTS_TAC >> simp[] >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >> fs[] ) >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> rpt strip_tac >>
    imp_res_tac((SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf)) >>
    metis_tac[] ) >>
  strip_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    simp[find_index_def] >>
    rpt gen_tac >> rpt strip_tac >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    imp_res_tac((SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet)) >- metis_tac[] >>
    res_tac >- fsrw_tac[ARITH_ss][] >>
    qpat_assum`m = X`mp_tac >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >>
    strip_tac >> fs[] >>
    metis_tac[optionTheory.THE_DEF] ) >>
  strip_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    simp[find_index_def] >>
    rpt gen_tac >> rpt strip_tac >>
    fs[Q.SPEC`1`(CONV_RULE(RESORT_FORALL_CONV List.rev)find_index_shift_0)] >>
    imp_res_tac((SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sLet)) >- metis_tac[] >>
    qpat_assum`p ⇒ q`mp_tac >> discharge_hyps >- metis_tac[] >>
    disch_then(qspec_then`m`mp_tac) >>
    simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    specl_args_of_then``find_index`` (CONV_RULE SWAP_FORALL_CONV find_index_MEM) mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >> fs[] >>
    metis_tac[optionTheory.THE_DEF] ) >>
  conj_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[] ) >>
  strip_tac >- (
    REWRITE_TAC[SUBSET_DEF] >>
    rpt gen_tac >> rpt strip_tac >>
    pop_assum mp_tac >>
    simp_tac std_ss [exp_to_pat_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`fs:string option list= MAP X funs` >>
    full_simp_tac std_ss [free_vars_exh_def] >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      simp[free_vars_defs_exh_MAP,PULL_EXISTS,MEM_MAP,Abbr`fs`,EXISTS_PROD] >>
      pop_assum mp_tac >>
      simp[free_vars_defs_exh_MAP,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      simp[MEM_MAP,Abbr`fs`,EXISTS_PROD] >>
      pop_assum mp_tac >>
      simp[PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    ntac 2 strip_tac >>
    simp_tac std_ss [free_vars_pat_def,set_lunion,free_vars_defs_pat_MAP] >>
    simp_tac std_ss [IN_UNION] >>
    simp_tac std_ss [set_lshift] >>
    simp_tac std_ss [GSPECIFICATION] >>
    strip_tac >>
    first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
    simp_tac std_ss [find_index_APPEND,IN_UNION,IN_SING] >>
    BasicProvers.VAR_EQ_TAC >>
    simp_tac std_ss [IN_IMAGE] >> strip_tac >>
    TRY (fsrw_tac[ARITH_ss][] >> NO_TAC) >>
    qexists_tac`x` >>
    asm_simp_tac std_ss [IN_UNION,IN_DIFF] >>
    rev_full_simp_tac std_ss [funs_to_pat_MAP,LENGTH_MAP] >>
    (reverse BasicProvers.CASE_TAC >- (
       full_simp_tac std_ss [] >>
       imp_res_tac find_index_LESS_LENGTH >>
       fsrw_tac[ARITH_ss][Abbr`fs`] )) >>
    rev_full_simp_tac std_ss [Once find_index_shift_0] >>
    full_simp_tac std_ss [GSYM find_index_NOT_MEM] >>
    (Cases_on`find_index (SOME x) ls 0` >- (
       last_x_assum(qspec_then`SOME x`mp_tac) >>
       simp[] >>
       fs[Abbr`fs`,MEM_MAP,FORALL_PROD] >>
       fs[GSYM find_index_NOT_MEM] )) >>
    simp[Abbr`fs`] >>
    fs[MEM_MAP,FORALL_PROD] ) >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  conj_tac >- (
    simp[SUBSET_DEF,PULL_EXISTS] >>
    metis_tac[] ) >>
  conj_tac >- simp[SUBSET_DEF,PULL_EXISTS] >>
  strip_tac >- (
    REWRITE_TAC[SUBSET_DEF] >>
    rpt gen_tac >> rpt strip_tac >>
    pop_assum mp_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      pop_assum mp_tac >>
      simp[free_vars_defs_exh_MAP] >>
      metis_tac[] ) >>
    strip_tac >>
    qpat_assum`p ⇒ q`mp_tac >>
    discharge_hyps >- (
      fs[free_vars_defs_exh_MAP,PULL_EXISTS] >>
      metis_tac[] ) >>
    strip_tac >>
    full_simp_tac std_ss [exp_to_pat_def,free_vars_pat_def,set_lunion,IN_UNION,IN_SING] >>
    strip_tac >- (
      first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
      simp_tac std_ss [find_index_def] >>
      simp_tac std_ss [Once IN_IMAGE,PULL_EXISTS] >>
      gen_tac >>
      BasicProvers.CASE_TAC >- simp[] >>
      strip_tac >>
      full_simp_tac std_ss [Once find_index_shift_0] >>
      qmatch_assum_rename_tac`z ∈ free_vars_exh e`[] >>
      Cases_on`find_index (SOME z) ls 0` >- (
        fs[GSYM find_index_NOT_MEM,free_vars_defs_exh_MAP,PULL_EXISTS] >>
        metis_tac[] ) >>
      asm_simp_tac std_ss [IN_IMAGE] >>
      qexists_tac`z` >> simp[] ) >>
    first_x_assum(fn th => first_x_assum (mp_tac o MATCH_MP th)) >>
    strip_tac >> fs[] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> Cases_on`ls`>>fs[] >> rw[] >>
    fs[Once row_to_pat_nil] >>
    `∃x y z. row_to_pat [NONE] p = (x,y,z)` by simp[GSYM EXISTS_PROD] >> fs[LET_THM] >>
    simp[find_index_def] >>
    simp[Once find_index_shift_0] >> rw[] >>
    pop_assum mp_tac >>
    specl_args_of_then``row_to_pat``(CONJUNCT1 free_vars_row_to_pat)mp_tac >>
    rw[] >> fs[] >>
    match_mp_tac SUBSET_TRANS >>
    first_x_assum(qspec_then`exp_to_pat (x++t) e`strip_assume_tac) >>
    HINT_EXISTS_TAC >> simp[] >>
    rator_x_assum`row_to_pat`mp_tac >>
    specl_args_of_then``row_to_pat``(CONJUNCT1 row_to_pat_acc) strip_assume_tac >>
    specl_args_of_then``row_to_pat``(CONJUNCT1 row_to_pat_pat_bindings) strip_assume_tac >>
    strip_tac >> fs[] >>
    first_x_assum(qspec_then`[]`mp_tac) >> simp[] >> rw[] >>
    qpat_assum`a ⇒ q`mp_tac >>
    discharge_hyps_keep >- (
      fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP] >>
      metis_tac[] ) >>
    strip_tac >>
    fs[SUBSET_DEF,PULL_EXISTS] >> rw[] >>
    res_tac >> fs[] >> rw[] >>
    qmatch_assum_rename_tac`a ∈ free_vars_exh e`[] >>
    Q.ISPECL_THEN[`x ++ t`,`SOME a`,`0:num`]mp_tac find_index_MEM >>
    discharge_hyps >- metis_tac[MEM_APPEND] >> strip_tac >> fs[] >>
    rator_x_assum`find_index`mp_tac >>
    simp[find_index_APPEND] >>
    reverse BasicProvers.CASE_TAC >- (
      rw[] >> imp_res_tac find_index_LESS_LENGTH >> fsrw_tac[ARITH_ss][] ) >>
    rw[] >> fs[Once find_index_shift_0] >>
    disj2_tac >>
    qexists_tac`a` >> simp[] >>
    fs[MEM_MAP,PULL_EXISTS] >>
    fs[GSYM find_index_NOT_MEM] >>
    metis_tac[]) >>
  simp[SUBSET_DEF,PULL_EXISTS] >>
  rw[] >>
  Cases_on`ls`>>fs[] >> rw[] >>
  fs[find_index_def,PULL_EXISTS] >>
  fs[Once row_to_pat_nil] >>
  `∃r1 n1 f1. row_to_pat [NONE] p = (r1,n1,f1)` by simp[GSYM EXISTS_PROD] >> fs[LET_THM] >>
  reverse(imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF]free_vars_pat_sIf) >> fs[])
  >- metis_tac[]
  >- (
    rator_x_assum`row_to_pat`mp_tac >>
    specl_args_of_then``row_to_pat``(CONJUNCT1 free_vars_row_to_pat)strip_assume_tac >>
    specl_args_of_then``row_to_pat``(CONJUNCT1 row_to_pat_pat_bindings)strip_assume_tac >>
    specl_args_of_then``row_to_pat``(CONJUNCT1 row_to_pat_acc)strip_assume_tac >>
    strip_tac >> fs[] >>
    first_x_assum(qspec_then`[]`strip_assume_tac) >>
    qpat_assum`a ⇒ b`mp_tac >>
    discharge_hyps >- (
      fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP] >> metis_tac[] ) >>
    strip_tac >>
    rfs[SUBSET_DEF] >>
    first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    strip_tac >> simp[] >>
    simp[Once find_index_shift_0] >>
    first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
    simp[find_index_APPEND,PULL_EXISTS] >>
    gen_tac >> reverse BasicProvers.CASE_TAC >- (
      imp_res_tac find_index_LESS_LENGTH >>
      fsrw_tac[ARITH_ss][] ) >>
    rw[] >>
    qmatch_assum_rename_tac`a ∈ free_vars_exh e`[] >>
    fs[Once find_index_shift_0] >>
    Q.ISPECL_THEN[`t`,`SOME a`,`0:num`]mp_tac find_index_MEM >>
    discharge_hyps >- metis_tac[find_index_NOT_MEM,MEM_MAP] >> strip_tac >> fs[] >>
    disj2_tac >>
    qexists_tac`a` >> simp[] >>
    simp[Once find_index_shift_0] >>
    metis_tac[find_index_NOT_MEM,MEM_MAP]) >>
  imp_res_tac(SIMP_RULE(srw_ss())[SUBSET_DEF](CONJUNCT1 free_vars_pat_to_pat)) >>
  rw[])

val tac =
  rw[EQ_IMP_THM]
  >- metis_tac[]
  >- (
    fsrw_tac[ARITH_ss][PRE_SUB1] >>
    qexists_tac`v-1` >>
    fsrw_tac[ARITH_ss][] >>
    disj2_tac >>
    qexists_tac`v` >>
    fsrw_tac[ARITH_ss][] )
  >- (
    disj1_tac >>
    qexists_tac`v` >>
    srw_tac[ARITH_ss][] )
  >- (
    fsrw_tac[ARITH_ss][PRE_SUB1] >>
    disj2_tac >>
    srw_tac[ARITH_ss][]
    >- (qexists_tac`m`>>simp[] >>
        qexists_tac`m`>>simp[]) >>
    srw_tac[ARITH_ss][PULL_EXISTS] >>
    qexists_tac`m`>>simp[])

val free_vars_mkshift = store_thm("free_vars_mkshift",
  ``∀f k e. set (free_vars (mkshift f k e)) = IMAGE (λv. if v < k then v else f (v-k) + k) (set (free_vars e))``,
  ho_match_mp_tac mkshift_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EXTENSION,MEM_MAP,MEM_FILTER] >> tac ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[free_vars_list_MAP] >>
    fsrw_tac[DNF_ss][Once EXTENSION,MEM_FLAT,MEM_MAP] >>
    fsrw_tac[DNF_ss][MEM_MAP,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[EXTENSION] >- tac >> metis_tac[]) >>
  strip_tac >- (
    simp[] >> rw[] >>
    simp[free_vars_defs_MAP] >>
    simp[LIST_TO_SET_MAP] >>
    qmatch_abbrev_tac`a ∪ b = c ∪ d` >>
    `b = d` by (
      unabbrev_all_tac >>
      simp[Once EXTENSION,MEM_FILTER] >>
      gen_tac >>
      srw_tac[DNF_ss][EQ_IMP_THM] >- (
        qexists_tac`v` >> simp[] ) >>
      qexists_tac`m` >> simp[] ) >>
    `a = c` by (
      unabbrev_all_tac >>
      simp[Once EXTENSION,MEM_FLAT,MEM_MAP] >>
      srw_tac[DNF_ss][EQ_IMP_THM] >- (
        BasicProvers.EVERY_CASE_TAC >- (
          qmatch_assum_rename_tac`MEM (NONE,az,b) defs`[] >>
          first_x_assum(qspecl_then[`az`,`b`]mp_tac) >>
          simp[] >> strip_tac >> fs[] >>
          fsrw_tac[DNF_ss][MEM_MAP,MEM_FILTER] >>
          rw[] >> fsrw_tac[ARITH_ss][] >>
          qexists_tac`v - (az + LENGTH defs)` >>
          simp[] >>
          HINT_EXISTS_TAC >> simp[] >>
          simp[MEM_MAP,MEM_FILTER] >>
          qexists_tac`v` >> simp[] ) >>
        qmatch_assum_rename_tac`MEM (SOME p,q,r) defs`[] >>
        PairCases_on`p` >>
        fs[] ) >>
      HINT_EXISTS_TAC >>
      simp[] >>
      qmatch_assum_rename_tac`MEM d defs`[] >>
      PairCases_on`d` >> simp[] >>
      Cases_on`d0`>>simp[]>>fs[]>>
      fsrw_tac[DNF_ss][MEM_MAP,MEM_FILTER] >>
      qexists_tac`m` >> simp[] ) >>
    simp[] ) >>
  strip_tac >- (
    rw[free_vars_list_MAP] >>
    fsrw_tac[DNF_ss][Once EXTENSION] >>
    fsrw_tac[DNF_ss][MEM_MAP,MEM_FLAT,EQ_IMP_THM] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[])
val _ = export_rewrites["free_vars_mkshift"]

val free_vars_shift = store_thm("free_vars_shift",
  ``set (free_vars (shift k n e)) = IMAGE (λv. if v < n then v else k + v) (set (free_vars e))``,
  simp[shift_def])
val _ = export_rewrites["free_vars_shift"]

val free_vars_exp_to_Cexp = store_thm("free_vars_exp_to_Cexp",
  ``(∀e. set (free_vars (exp_to_Cexp e)) = set (free_vars_pat e)) ∧
    (∀es. set (free_vars_list (exps_to_Cexps es)) = set (free_vars_list_pat es))``,
  ho_match_mp_tac(TypeBase.induction_of``:exp_pat``) >> simp[] >>
  strip_tac >- (
    rw[EXTENSION] >>
    rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    simp[PULL_EXISTS] >> HINT_EXISTS_TAC >> simp[] ) >>
  strip_tac >- (
    gen_tac >> strip_tac >>
    qx_gen_tac`op` >>
    Cases_on`op`>>TRY(Cases_on`o'`)>>Cases_on`es`>>fs[]>>
    Cases_on`t`>>fs[]>>TRY(Cases_on`t'`)>>fs[]>>
    Cases_on`o''`>>fs[]>>
    TRY(Cases_on`t`)>>fs[]>>
    BasicProvers.EVERY_CASE_TAC >> simp[] >>
    fs[EXTENSION] >> rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    TRY(metis_tac[]) >>
    spose_not_then strip_assume_tac >>
    first_x_assum(qspec_then`x+1`mp_tac) >> simp[] >>
    TRY(metis_tac[])>>
    spose_not_then strip_assume_tac>>
    first_x_assum(qspec_then`x+2`mp_tac) >> simp[] >>
    metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  fs[EXTENSION,free_vars_defs_MAP,free_vars_list_MAP] >>
  simp[MAP_MAP_o,combinTheory.o_DEF] >>
  fs[MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
  rw[EQ_IMP_THM] >> rw[] >> fsrw_tac[ARITH_ss][] >>
  metis_tac[])
val _ = export_rewrites["free_vars_exp_to_Cexp"]

val (closed_pat_rules,closed_pat_ind,closed_pat_cases) = Hol_reln`
(closed_pat (Litv_pat l)) ∧
(EVERY (closed_pat) vs ⇒ closed_pat (Conv_pat cn vs)) ∧
(EVERY (closed_pat) env ∧ set (free_vars_pat b) ⊆ count (LENGTH env + 1)
⇒ closed_pat (Closure_pat env b)) ∧
(EVERY (closed_pat) env ∧ d < LENGTH defs ∧
 EVERY (λe. set (free_vars_pat e) ⊆ count (LENGTH env + LENGTH defs + 1)) defs
⇒ closed_pat (Recclosure_pat env defs d)) ∧
(closed_pat (Loc_pat n)) ∧
(EVERY closed_pat vs ⇒ closed_pat (Vectorv_pat vs))`;

val closed_pat_lit_loc_conv = store_thm("closed_pat_lit_loc_conv",
  ``closed_pat (Litv_pat l) ∧ closed_pat (Loc_pat n) ∧
    (closed_pat (Conv_pat a bs) ⇔ EVERY closed_pat bs) ∧
    (closed_pat (Vectorv_pat bs) ⇔ EVERY closed_pat bs)``,
  rw[closed_pat_cases])
val _ = export_rewrites["closed_pat_lit_loc_conv"]

val csg_closed_pat_def = Define`
  csg_closed_pat csg ⇔
    EVERY (sv_every closed_pat) (SND(FST csg)) ∧
    EVERY (OPTION_EVERY closed_pat) (SND csg)`

val v_to_list_pat_closed = prove(
  ``∀v vs. v_to_list_pat v = SOME vs ⇒ closed_pat v ⇒ EVERY closed_pat vs``,
  ho_match_mp_tac v_to_list_pat_ind >>
  simp[v_to_list_pat_def] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val evaluate_pat_closed = store_thm("evaluate_pat_closed",
  ``(∀ck env s e res. evaluate_pat ck env s e res ⇒
       set (free_vars_pat e) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ⇒
       csg_closed_pat (FST res) ∧
       every_result closed_pat closed_pat (SND res)) ∧
    (∀ck env s es res. evaluate_list_pat ck env s es res ⇒
       set (free_vars_list_pat es) ⊆ count (LENGTH env) ∧
       EVERY closed_pat env ∧ csg_closed_pat s ⇒
       csg_closed_pat (FST res) ∧
       every_result (EVERY closed_pat) closed_pat (SND res))``,
  ho_match_mp_tac evaluate_pat_ind >> simp[] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >> fs[] >>
    fsrw_tac[ARITH_ss][SUBSET_DEF,PULL_EXISTS] >>
    Cases>>simp[ADD1] >> rw[] >>
    res_tac >> fsrw_tac[ARITH_ss][]) >>
  strip_tac >- simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  strip_tac >- (
    simp[csg_closed_pat_def,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> first_x_assum(qspec_then`n`mp_tac) >> simp[] ) >>
  strip_tac >- (
    simp[Once closed_pat_cases,SUBSET_DEF,PULL_EXISTS] >>
    rpt gen_tac >> strip_tac >>
    Cases >> simp[] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    strip_tac >> fs[] >>
    fs[do_opapp_pat_def] >>
    Cases_on`vs`>>fs[]>>Cases_on`t`>>fs[]>>
    Cases_on`t'`>>fs[]>>Cases_on`h`>>fs[]>>
    rpt BasicProvers.VAR_EQ_TAC >>
    rfs[csg_closed_pat_def,
        Q.SPEC`Closure_pat X Y`closed_pat_cases,
        Q.SPEC`Recclosure_pat X Y Z`closed_pat_cases] >>
    first_x_assum match_mp_tac >>
    fsrw_tac[ARITH_ss][ADD1] >>
    simp[build_rec_env_pat_def,EVERY_GENLIST] >>
    fsrw_tac[ARITH_ss][EVERY_MEM,MEM_EL,PULL_EXISTS,AC ADD_ASSOC ADD_SYM] >>
    simp[Once closed_pat_cases,EVERY_MEM,MEM_EL,PULL_EXISTS]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    strip_tac >> fs[] >>
    PairCases_on`s2` >>
    imp_res_tac do_app_pat_cases >>
    fs[do_app_pat_def] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
    simp[prim_exn_pat_def] >>
    imp_res_tac v_to_list_pat_closed >>
    fs[store_assign_def,store_lookup_def,LET_THM,csg_closed_pat_def,UNCURRY,store_alloc_def] >>
    rw[] >> BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[prim_exn_pat_def] >>
    fs[EVERY_MEM] >>
    simp[REPLICATE_GENLIST,MEM_GENLIST,PULL_EXISTS] >>
    TRY (
      fs[MEM_EL,PULL_EXISTS] >>
      last_x_assum(qspec_then`lnum`mp_tac) >>
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >> NO_TAC) >>
    TRY (
      fs[MEM_EL,PULL_EXISTS,EL_LUPDATE] >> rw[] >>
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_LUPDATE] >>
      rw[] >>
      last_x_assum(qspec_then`lnum`mp_tac) >>
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >> NO_TAC) >>
    metis_tac[MEM_LUPDATE_E,sv_every_def,MEM_EL,OPTION_EVERY_def,NOT_LESS_EQUAL,GREATER_EQ] ) >>
  strip_tac >- (
    ntac 4 gen_tac >>
    Cases >> simp[do_if_pat_def] >>
    Cases_on`l`>>simp[] >> rw[] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1] >>
    Cases >> simp[ADD1] >> rw[] >> res_tac >>
    fsrw_tac[ARITH_ss][] ) >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fsrw_tac[DNF_ss][SUBSET_DEF,ADD1,build_rec_env_pat_def,EVERY_GENLIST] >>
    conj_tac >- (
      rw[] >>
      Cases_on`x < LENGTH funs`>>simp[] >>
      REWRITE_TAC[Once ADD_SYM] >>
      first_x_assum match_mp_tac >>
      simp[] ) >>
    simp[Once closed_pat_cases] >>
    fs[EVERY_MEM,SUBSET_DEF,MEM_FLAT,PULL_EXISTS,MEM_MAP] >>
    rw[] >>
    fsrw_tac[ARITH_ss][AC ADD_ASSOC ADD_SYM] >>
    Cases_on`x < LENGTH funs + 1`>>simp[] >>
    first_x_assum match_mp_tac >>
    simp[] >> metis_tac[] ) >>
  simp[csg_closed_pat_def,EVERY_GENLIST])

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

val free_vars_i2_def = tDefine"free_vars_i2"`
  free_vars_i2 (Raise_i2 e) = free_vars_i2 e ∧
  free_vars_i2 (Handle_i2 e pes) = free_vars_i2 e ∪ free_vars_pes_i2 pes ∧
  free_vars_i2 (Lit_i2 _) = {} ∧
  free_vars_i2 (Con_i2 _ es) = free_vars_list_i2 es ∧
  free_vars_i2 (Var_local_i2 n) = {n} ∧
  free_vars_i2 (Var_global_i2 _) = {} ∧
  free_vars_i2 (Fun_i2 x e) = free_vars_i2 e DIFF {x} ∧
  free_vars_i2 (App_i2 _ es) = free_vars_list_i2 es ∧
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
(closed_i2 (Loc_i2 n)) ∧
(EVERY closed_i2 vs ⇒ closed_i2 (Vectorv_i2 vs))`;

val closed_i2_lit_loc_conv = store_thm("closed_i2_lit_loc_conv",
  ``closed_i2 (Litv_i2 l) ∧ closed_i2 (Loc_i2 n) ∧
    (closed_i2 (Conv_i2 a bs) ⇔ EVERY closed_i2 bs) ∧
    (closed_i2 (Vectorv_i2 bs) ⇔ EVERY closed_i2 bs)``,
  rw[closed_i2_cases])
val _ = export_rewrites["closed_i2_lit_loc_conv"]

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

val free_vars_i1_def = tDefine"free_vars_i1"`
  free_vars_i1 (Raise_i1 e) = free_vars_i1 e ∧
  free_vars_i1 (Handle_i1 e pes) = free_vars_i1 e ∪ free_vars_pes_i1 pes ∧
  free_vars_i1 (Lit_i1 _) = {} ∧
  free_vars_i1 (Con_i1 _ es) = free_vars_list_i1 es ∧
  free_vars_i1 (Var_local_i1 n) = {n} ∧
  free_vars_i1 (Var_global_i1 _) = {} ∧
  free_vars_i1 (Fun_i1 x e) = free_vars_i1 e DIFF {x} ∧
  free_vars_i1 (App_i1 _ es) = free_vars_list_i1 es ∧
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

val free_vars_defs_i1_MAP = store_thm("free_vars_defs_i1_MAP",
  ``∀funs. free_vars_defs_i1 funs = BIGUNION (set (MAP (λ(f,x,e). free_vars_i1 e DIFF {x}) funs))``,
  Induct>>simp[] >> fs[EXTENSION] >>
  qx_gen_tac`p`>>PairCases_on`p`>>simp[])

val (closed_i1_rules,closed_i1_ind,closed_i1_cases) = Hol_reln`
(closed_i1 (Litv_i1 l)) ∧
(EVERY (closed_i1) vs ⇒ closed_i1 (Conv_i1 cn vs)) ∧
(EVERY (closed_i1) (MAP SND env) ∧ free_vars_i1 b ⊆ {x} ∪ set (MAP FST env)
⇒ closed_i1 (Closure_i1 (envC,env) x b)) ∧
(EVERY (closed_i1) (MAP SND env) ∧ MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). free_vars_i1 e ⊆ {x} ∪ set (MAP FST defs) ∪ set (MAP FST env)) defs
⇒ closed_i1 (Recclosure_i1 (envC,env) defs d)) ∧
(closed_i1 (Loc_i1 n)) ∧
(EVERY closed_i1 vs ⇒ closed_i1 (Vectorv_i1 vs))`;

val closed_i1_lit_loc_conv = store_thm("closed_i1_lit_loc_conv",
  ``closed_i1 (Litv_i1 l) ∧ closed_i1 (Loc_i1 n) ∧
    (closed_i1 (Conv_i1 a bs) ⇔ EVERY closed_i1 bs) ∧
    (closed_i1 (Vectorv_i1 bs) ⇔ EVERY closed_i1 bs)``,
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

val (closed_rules,closed_ind,closed_cases) = Hol_reln`
(closed (Litv l)) ∧
(EVERY closed vs ⇒ closed (Conv cn vs)) ∧
(EVERY closed (MAP SND envE) ∧
 EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
 FV b ⊆ (IMAGE Short ({x} ∪ set (MAP FST envE))) ∪
        { Long mn x | ∃env. lookup mn envM = SOME env ∧ MEM x (MAP FST env)}
⇒ closed (Closure (envM,envC,envE) x b)) ∧
(EVERY closed (MAP SND envE) ∧
 EVERY closed (MAP SND (FLAT (MAP SND envM))) ∧
 MEM d (MAP FST defs) ∧
 EVERY (λ(f,x,e). FV e ⊆ (IMAGE Short ({x} ∪ set (MAP FST defs) ∪ set (MAP FST envE))) ∪
                         { Long mn x | ∃env. lookup mn envM = SOME env ∧ MEM x (MAP FST env) }) defs
⇒ closed (Recclosure (envM,envC,envE) defs d)) ∧
(closed (Loc n)) ∧
(EVERY closed vs ⇒ closed (Vectorv vs))`;

val closed_lit_loc_conv = store_thm("closed_lit_loc_conv",
  ``closed (Litv l) ∧ closed (Loc n) ∧
    (closed (Conv a bs) ⇔ EVERY closed bs) ∧
    (closed (Vectorv bs) ⇔ EVERY closed bs)``,
  rw[closed_cases])
val _ = export_rewrites["closed_lit_loc_conv"]

val closed_strongind=theorem"closed_strongind"

val all_env_closed_def = Define`
  all_env_closed (envM,envC,envE) ⇔
  EVERY closed (MAP SND envE) ∧
  EVERY closed (MAP SND (FLAT (MAP SND envM)))`

val build_rec_env_closed = store_thm("build_rec_env_closed",
  ``∀defs env l.
    EVERY closed (MAP SND l) ∧ all_env_closed env ∧
    ALL_DISTINCT (MAP FST defs) ∧
    (∀d x b. MEM (d,x,b) defs ⇒ FV b ⊆
                         (IMAGE Short ({x} ∪ set (MAP FST defs) ∪ set (MAP FST (all_env_to_env env)))) ∪
                         { Long mn x | ∃envE. lookup mn (all_env_to_menv env) = SOME envE ∧ MEM x (MAP FST envE) })
    ⇒ EVERY closed (MAP SND (build_rec_env defs env l))``,
  rpt gen_tac >> PairCases_on`env` >>
  rw[build_rec_env_def,bind_def,FOLDR_CONS_triple,all_env_closed_def] >>
  rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
  asm_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
  rw[Once closed_cases] >>
  fs[all_env_to_env_def,all_env_to_menv_def] >>
  simp[MEM_MAP,EXISTS_PROD] >>
  conj_tac >- metis_tac[] >>
  simp[EVERY_MEM,FORALL_PROD] >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[])

val v_to_list_closed = prove(
  ``∀v vs. v_to_list v = SOME vs ⇒ closed v ⇒ EVERY closed vs``,
  ho_match_mp_tac v_to_list_ind >>
  simp[v_to_list_def] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val do_app_closed = store_thm("do_app_closed",
  ``∀s op vs s' res.
    EVERY closed vs ∧ EVERY (sv_every closed) s ∧
    (do_app s op vs = SOME (s',res))
    ⇒ every_result closed closed res ∧
      EVERY (sv_every closed) s'``,
  rpt gen_tac >> strip_tac >>
  imp_res_tac do_app_cases >> fs[do_app_def] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  fs[store_assign_def,store_alloc_def,store_lookup_def,LET_THM] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[prim_exn_def] >>
  imp_res_tac v_to_list_closed >>
  fs[EVERY_MEM] >>
  TRY (
    simp[REPLICATE_GENLIST,MEM_GENLIST,PULL_EXISTS] >>
    fs[MEM_EL,PULL_EXISTS] >>
    first_x_assum(qspec_then`lnum`mp_tac) >>
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_LUPDATE] >>
    NO_TAC) >>
  TRY (
    rw[] >>
    imp_res_tac MEM_LUPDATE_E >> rw[] >>
    simp[EVERY_MEM] >> rw[] >>
    fs[MEM_EL,PULL_EXISTS] >>
    first_x_assum(qspec_then`lnum`mp_tac) >>
    simp[EL_LUPDATE,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> NO_TAC) >>
  metis_tac[MEM_LUPDATE_E,sv_every_def,MEM_EL,GREATER_EQ,NOT_LESS_EQUAL])

val pmatch_closed = store_thm("pmatch_closed",
  ``(∀cenv s p v env env'.
      EVERY closed (MAP SND env) ∧ closed v ∧
      EVERY (sv_every closed) s ∧
      (pmatch cenv s p v env = Match env') ⇒
      EVERY closed (MAP SND env') ∧
      (MAP FST env' = pat_bindings p [] ++ (MAP FST env))) ∧
    (∀cenv s ps vs env env'.
      EVERY closed (MAP SND env) ∧ EVERY closed vs ∧
      EVERY (sv_every closed) s ∧
      (pmatch_list cenv s ps vs env = Match env') ⇒
      EVERY closed (MAP SND env') ∧
      (MAP FST env' = pats_bindings ps [] ++ MAP FST env))``,
  ho_match_mp_tac pmatch_ind >>
  simp[pat_bindings_def,pmatch_def,bind_def] >>
  rw[] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[store_lookup_def] >> rw[] >>
  TRY (metis_tac[pat_bindings_accum]) >>
  fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  metis_tac[sv_every_def])

val do_opapp_closed = store_thm("do_opapp_closed",
  ``∀vs env exp.
    EVERY closed vs ∧
    do_opapp vs = SOME (env,exp)
    ⇒
    all_env_closed env ∧
    FV exp ⊆ all_env_dom env``,
  rpt gen_tac >> simp[do_opapp_def] >>
  BasicProvers.EVERY_CASE_TAC >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
  qpat_assum`closed (X Y)`mp_tac >>
  simp[Once closed_cases] >> strip_tac >>
  simp[all_env_closed_def,bind_def] >>
  simp[all_env_dom_def] >>
  TRY(
    conj_tac >- (
      match_mp_tac build_rec_env_closed >>
      simp[all_env_closed_def] >> fs[FST_triple] >>
      fs[EVERY_MEM,FORALL_PROD,all_env_to_menv_def,all_env_to_env_def] >>
      fs[SUBSET_DEF,PULL_EXISTS] >>
      metis_tac[] )) >>
  fs[SUBSET_DEF,build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,find_recfun_lookup] >>
  imp_res_tac libPropsTheory.lookup_in3 >>
  fs[EVERY_MEM,FORALL_PROD] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >> rw[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >> rw[])

val do_log_FV = store_thm("do_log_FV",
  ``(do_log op v e2 = SOME exp) ⇒
    (FV exp ⊆ FV e2)``,
  fs[do_log_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[] >>rw[])

val do_if_FV = store_thm("do_if_FV",
  ``(do_if v e2 e3 = SOME e) ⇒
    (FV e ⊆ FV e2 ∪ FV e3)``,
  fs[do_if_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[] >>rw[])

val evaluate_closed = store_thm("evaluate_closed",
  ``(∀ck env s exp res.
     evaluate ck env s exp res ⇒
     FV exp ⊆ all_env_dom env ∧
     all_env_closed env ∧
     EVERY (sv_every closed) (SND s)
     ⇒
     EVERY (sv_every closed) (SND (FST res)) ∧
     every_result closed closed (SND res)) ∧
    (∀ck env s exps ress.
     evaluate_list ck env s exps ress ⇒
     FV_list exps ⊆ all_env_dom env ∧
     all_env_closed env ∧
     EVERY (sv_every closed) (SND s)
     ⇒
     EVERY (sv_every closed) (SND (FST ress)) ∧
     every_result (EVERY closed) closed (SND ress)) ∧
    (∀ck env s v pes errv res.
     evaluate_match ck env s v pes errv res ⇒
     FV_pes pes ⊆ all_env_dom env ∧
     all_env_closed env ∧
     EVERY (sv_every closed) (SND s) ∧
     closed v ∧ closed errv
     ⇒
     EVERY (sv_every closed) (SND (FST res)) ∧
     every_result closed closed (SND res))``,
  ho_match_mp_tac evaluate_ind >>
  strip_tac (* Lit *) >- rw[] >>
  strip_tac (* Raise *) >- rw[] >>
  strip_tac (* Handle *) >- (rw[] >> fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac (* Handle *) >- (
    rw[] >> fs[] >> rfs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,bind_def,MEM_MAP,EXISTS_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac (* Handle *) >- (rw[] >> fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac (* Handle *) >- (rw[] >> fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac (* Con *) >- (
    rw[build_conv_def] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >> rw[]) >>
  strip_tac (* Con *) >- rw[] >>
  strip_tac (* Con *) >- ( rw[] >> Cases_on`err` >> fsrw_tac[ETA_ss,DNF_ss][SUBSET_DEF] ) >>
  strip_tac (* Var *) >- (
    ntac 2 gen_tac >>
    PairCases_on`env` >>
    Cases >> rw[lookup_var_id_def,MEM_FLAT,MEM_MAP] >>
    BasicProvers.EVERY_CASE_TAC >>
    fs[all_env_dom_def,all_env_closed_def] >>
    fs[EVERY_MEM,MAP_FLAT,MEM_FLAT,PULL_EXISTS] >>
    metis_tac[libPropsTheory.lookup_in,MEM_MAP]) >>
  strip_tac (* Var *) >- rw[] >>
  strip_tac (* Fun *) >- (
    rw[] >>
    PairCases_on`env` >>
    fs[all_env_closed_def,all_env_dom_def] >>
    rw[Once closed_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  strip_tac (* Opapp *) >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    PROVE_TAC[do_opapp_closed] ) >>
  strip_tac (* Opapp *) >- rw[] >>
  strip_tac (* Opapp *) >- rw[] >>
  strip_tac (* App *) >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rfs[] >>
    PROVE_TAC[do_app_closed]) >>
  strip_tac (* App *) >- (
    rw[] >> fs[] >> rfs[] >>
    PROVE_TAC[do_app_closed] ) >>
  strip_tac (* App *) >- rw[] >>
  strip_tac (* Log *) >- (
    rw[] >> fs[] >>
    PROVE_TAC[do_log_FV,SUBSET_TRANS]) >>
  strip_tac (* Log *) >- (
    rw[] >> fs[] >> rfs[] >>
    PROVE_TAC[do_log_FV,SUBSET_TRANS] ) >>
  strip_tac (* Log *) >- rw[] >>
  strip_tac (* If *) >- (
    rw[] >> fs[] >>
    PROVE_TAC[do_if_FV,SUBSET_DEF,IN_UNION]) >>
  strip_tac (* If *) >- (
    rw[] >> fs[] >> rfs[] >>
    PROVE_TAC[do_if_FV,UNION_SUBSET,SUBSET_TRANS] ) >>
  strip_tac (* If *) >- rw[] >>
  strip_tac (* Mat *) >- rw[] >>
  strip_tac (* Mat *) >- rw[] >>
  strip_tac (* Let *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[bind_def,opt_bind_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,all_env_dom_def,all_env_closed_def] >>
    metis_tac[]) >>
  strip_tac (* Let *) >- rw[] >>
  strip_tac (* Letrec *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fs[FST_triple] >> rfs[] >>
    conj_tac >- (
      fs[GSYM MAP_MAP_o,LET_THM,FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_FLAT] >>
      gen_tac >> strip_tac >> res_tac >>
      Cases_on`x`>>fs[all_env_dom_def] >>
      fs[build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      fs[MEM_MAP,EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    fs[all_env_closed_def] >>
    match_mp_tac build_rec_env_closed >> fs[all_env_closed_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_FLAT,LET_THM,FV_defs_MAP,all_env_dom_def,
                     all_env_to_env_def,all_env_to_menv_def] >>
    metis_tac[]) >>
  strip_tac (* Letrec *) >- rw[] >>
  strip_tac (* [] *) >- rw[] >>
  strip_tac (* :: *) >- rw[] >>
  strip_tac (* :: *) >- (rw[] >> Cases_on`err`>>fs[]) >>
  strip_tac (* :: *) >- rw[] >>
  strip_tac (* [] *) >- rw[] >>
  strip_tac (* Match *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    rator_x_assum`$=`mp_tac >>
    specl_args_of_then``pmatch``(CONJUNCT1 pmatch_closed)mp_tac>>
    fs[all_env_closed_def] >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,MEM_FLAT,all_env_dom_def] >>
    metis_tac[]) >>
  strip_tac (* Match *) >- rw[] >>
  strip_tac (* Match *) >- rw[] >>
  rw[])

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

val evaluate_dec_closed = store_thm("evaluate_dec_closed",
  ``∀ck mn env s dec res. evaluate_dec ck mn env s dec res ⇒
      FV_dec dec ⊆ all_env_dom env ∧
      all_env_closed env ∧
      EVERY (sv_every closed) (SND(FST s))
      ⇒
      EVERY (sv_every closed) (SND(FST(FST res))) ∧
      every_result (λ(envC,envE). EVERY closed (MAP SND envE))
                   closed (SND res)``,
  ho_match_mp_tac evaluate_dec_ind >> rw[] >>
  imp_res_tac evaluate_closed >> fs[emp_def] >>
  TRY (
    rator_x_assum`$=`mp_tac >>
    specl_args_of_then``pmatch``(CONJUNCT1 pmatch_closed)mp_tac>>
    rw[] >> fs[] ) >>
  match_mp_tac build_rec_env_closed >>
  PairCases_on`env` >>
  fs[all_env_dom_def,all_env_closed_def,FST_triple,all_env_to_env_def,all_env_to_menv_def] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,FV_defs_MAP,FORALL_PROD,MEM_MAP,EXISTS_PROD] >>
  metis_tac[])

val evaluate_dec_new_dec_vs = store_thm("evaluate_dec_new_dec_vs",
  ``∀ck mn env s dec res.
    evaluate_dec ck mn env s dec res ⇒
    ∀tds vs. (SND res = Rval (tds,vs)) ⇒ MAP FST vs = new_dec_vs dec``,
  ho_match_mp_tac evaluate_dec_ind >>
  simp[libTheory.emp_def] >> rw[] >>
  imp_res_tac pmatch_dom >>
  fs[build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val evaluate_decs_new_decs_vs = store_thm("evaluate_decs_new_decs_vs",
  ``∀ck mn env s decs res. evaluate_decs ck mn env s decs res ⇒
      ∀env. SND(SND res) = Rval env ⇒ MAP FST env = new_decs_vs decs``,
  ho_match_mp_tac evaluate_decs_ind >> simp[] >> rw[libTheory.emp_def] >>
  imp_res_tac evaluate_dec_new_dec_vs >> fs[] >>
  Cases_on`r`>>fs[semanticPrimitivesTheory.combine_dec_result_def]>>
  rw[libTheory.merge_def])

val evaluate_decs_closed = store_thm("evaluate_decs_closed",
  ``∀ck mn env s ds res. evaluate_decs ck mn env s ds res ⇒
      FV_decs ds ⊆ all_env_dom env ∧
      all_env_closed env ∧
      EVERY (sv_every closed) (SND(FST s))
      ⇒
      EVERY (sv_every closed) (SND(FST(FST res))) ∧
      every_result (λenvE. EVERY closed (MAP SND envE))
                   closed (SND (SND res))``,
  ho_match_mp_tac evaluate_decs_ind >> rw[] >>
  imp_res_tac evaluate_dec_closed >>
  imp_res_tac evaluate_dec_new_dec_vs >>
  rfs[emp_def,FV_decs_def] >> rw[] >>
  qpat_assum`p ⇒ q`mp_tac >>
  (discharge_hyps >- (
    fsrw_tac[DNF_ss][merge_def,merge_envC_def,SUBSET_DEF,PULL_EXISTS
                    ,all_env_closed_def,all_env_dom_def,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] )) >> simp[] >>
  simp[combine_dec_result_def] >>
  BasicProvers.CASE_TAC >>
  simp[merge_def])

val evaluate_decs_new_decs_vs = store_thm("evaluate_decs_new_decs_vs",
  ``∀ck mn env s ds res. evaluate_decs ck mn env s ds res ⇒
    ∀env. SND (SND res) = Rval env ⇒ MAP FST env = new_decs_vs ds``,
  ho_match_mp_tac evaluate_decs_ind >> simp[libTheory.emp_def] >>
  rw[] >>
  Cases_on`r`>>fs[combine_dec_result_def,libTheory.merge_def] >>
  imp_res_tac evaluate_dec_new_dec_vs >> fs[] >> rw[])

val closed_top_def = Define`
  closed_top env top ⇔ FV_top top ⊆ all_env_dom env`

val closed_prog_def = Define`
  closed_prog p ⇔ FV_prog p = {}`

val global_dom_def = Define`
  global_dom (me,e) = IMAGE Short (FDOM e) ∪ { Long m x | ∃e. FLOOKUP me m = SOME e ∧ x ∈ FDOM e}`

val evaluate_top_closed = store_thm("evaluate_top_closed",
  ``∀ck env stm top res.
      evaluate_top ck env stm top res ⇒
      FV_top top ⊆ all_env_dom env ∧ all_env_closed env ∧
      EVERY (sv_every closed) (SND (FST stm)) ⇒
      EVERY (sv_every closed) (SND (FST (FST res))) ∧
      every_result (λ(envM,envE). all_env_closed (envM,ARB,envE)) closed (SND (SND res))``,
  ho_match_mp_tac evaluate_top_ind >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  TRY (
    first_x_assum(mp_tac o MATCH_MP evaluate_dec_closed) >>
    simp[all_env_closed_def,libTheory.emp_def] ) >>
  first_x_assum(mp_tac o MATCH_MP evaluate_decs_closed) >>
  simp[all_env_closed_def,libTheory.emp_def])

val evaluate_top_new_top_vs = store_thm("evaluate_top_new_top_vs",
  ``∀ck env stm top res.
      evaluate_top ck env stm top res ⇒
      ∀envM envE. SND (SND res) = Rval (envM, envE) ⇒
      SND(SND stm) ⊆ SND(SND(FST res)) ∧
      if envM = [] then new_top_vs top = MAP Short (MAP FST envE) else
      ∃mn menvE. envE = [] ∧ envM = [(mn,menvE)] ∧ new_top_vs top = MAP (Long mn) (MAP FST menvE) ∧
                 mn ∉ SND(SND stm) ∧ SND(SND (FST res)) = {mn} ∪ SND(SND stm)``,
  ho_match_mp_tac evaluate_top_ind >> simp[libTheory.emp_def] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  imp_res_tac evaluate_dec_new_dec_vs >> fs[] >>
  imp_res_tac evaluate_decs_new_decs_vs >> fs[])

val evaluate_prog_closed = store_thm("evaluate_prog_closed",
  ``∀ck env stm prog res.
      evaluate_prog ck env stm prog res ⇒
      set (MAP FST (all_env_to_menv env)) ⊆ SND(SND stm) ∧
      FV_prog prog ⊆ all_env_dom env ∧ all_env_closed env ∧
      EVERY (sv_every closed) (SND (FST stm)) ⇒
      EVERY (sv_every closed) (SND (FST (FST res))) ∧
      every_result (λ(envM,envE). all_env_closed (envM,ARB,envE)) closed (SND (SND res))``,
  ho_match_mp_tac evaluate_prog_ind >> simp[] >>
  conj_tac >- (
    simp[all_env_closed_def,libTheory.emp_def] ) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[FV_prog_def] >> strip_tac >>
    qpat_assum`x ⇒ y`mp_tac >>
    discharge_hyps >- (
      imp_res_tac evaluate_top_new_top_vs >> fs[] >>
      first_x_assum(mp_tac o MATCH_MP evaluate_top_closed) >>
      Cases_on`new_tds`>>Cases_on`cenv`>>
      simp[libTheory.merge_def,merge_envC_def] >>
      fs[all_env_closed_def,SUBSET_DEF,all_env_to_menv_def] >>
      pop_assum mp_tac >>
      IF_CASES_TAC >> strip_tac >>
      fs[all_env_dom_def,PULL_EXISTS,MAP_MAP_o,MEM_MAP] >>
      TRY (metis_tac[]) >> rw[] >> fs[] >>
      first_x_assum(qspec_then`x`mp_tac) >>
      simp[] >>
      Cases_on`x`>>fs[] >> rw[] >>
      metis_tac[libPropsTheory.lookup_in2,MEM_MAP]) >>
    simp[] >>
    Cases_on`r`>>simp[combine_mod_result_def]>>
    BasicProvers.CASE_TAC >> simp[] >>
    fs[libTheory.merge_def,all_env_closed_def] >>
    imp_res_tac evaluate_top_closed >>
    fs[all_env_closed_def] ) >>
  rpt gen_tac >> strip_tac >>
  simp[FV_prog_def] >> strip_tac >>
  imp_res_tac evaluate_top_closed >> fs[])

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

val free_vars_prog_i1_def = Define`
  free_vars_prog_i1 ps = BIGUNION (IMAGE free_vars_prompt_i1 (set ps))`

val dec_to_i1_new_dec_vs = store_thm("dec_to_i1_new_dec_vs",
  ``∀a b c d e f g h. dec_to_i1 a b c d e = (f,g,h) ⇒
      set (MAP FST g) = set (new_dec_vs e) ∧
      f = a + LENGTH g``,
  rw[dec_to_i1_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[LET_THM] >> rw[] >>
  rw[alloc_defs_GENLIST,MAP_ZIP,FST_triple])

val top_to_i1_new_top_vs = store_thm("top_to_i1_new_top_vs",
  ``∀n m e h x y z p. top_to_i1 n m e h = (x,y,z,p) ⇒
      FDOM z = FDOM e ∪ {x | MEM (Short x) (new_top_vs h)}``,
  rw[top_to_i1_def] >>
  BasicProvers.EVERY_CASE_TAC >> fs[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  rw[] >>
  simp[(Q.ISPECL[`FST`,`SND`]FOLDL_FUPDATE_LIST|>SIMP_RULE(srw_ss())[LAMBDA_PROD])] >>
  simp[FDOM_FUPDATE_LIST,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  imp_res_tac dec_to_i1_new_dec_vs >> rw[MEM_MAP])

val FV_prog_to_i1 = store_thm("FV_prog_to_i1",
  ``∀n m e ps x y z p. prog_to_i1 n m e ps = (x,y,z,p) ⇒
       free_vars_prog_i1 p = {x | Short x ∈ FV_prog ps} DIFF FDOM e``,
  Induct_on`ps`>-simp[prog_to_i1_def,free_vars_prog_i1_def,FV_prog_def] >>
  simp[prog_to_i1_def] >> rw[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >> rw[] >>
  first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >>
  imp_res_tac FV_top_to_i1 >> pop_assum mp_tac >>
  simp[free_vars_prog_i1_def,FV_prog_def] >>
  srw_tac[DNF_ss][EXTENSION,MEM_MAP] >>
  qmatch_abbrev_tac`a ∨ b ⇔ a ∨ c` >>
  qsuff_tac`¬a ⇒ (b ⇔ c)` >- metis_tac[] >>
  unabbrev_all_tac >> fs[] >>
  Cases_on`p'`>>fs[free_vars_prompt_i1_def] >>
  qpat_assum`∀x. x ∈ A ⇔ B x`mp_tac >>
  qho_match_abbrev_tac`(∀x. P x ⇔ Q x) ⇒ C ⇒ D` >>
  qsuff_tac`(∀x. ¬Q x ⇔ ¬P x) ⇒ ¬P x ⇒ D`>-metis_tac[] >>
  unabbrev_all_tac >> rw[] >>
  imp_res_tac top_to_i1_new_top_vs >>
  rw[] >> metis_tac[])

val free_vars_prog_i2_def = Define`
  free_vars_prog_i2 ps = BIGUNION (IMAGE free_vars_prompt_i2 (set ps))`

val free_vars_i2_prog_to_i3 = store_thm("free_vars_i2_prog_to_i3",
  ``∀x y s m p n e.
    prog_to_i3 x y m p = (n,e) ⇒
    (free_vars_i2 e = free_vars_prog_i2 p)``,
  Induct_on`p`>> rw[prog_to_i3_def] >> rw[free_vars_prog_i2_def] >>
  rw[GSYM free_vars_prog_i2_def] >>
  fs[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  rw[] >> rw[pat_bindings_i2_def] >> fs[pat_bindings_i2_def] >>
  first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >> rw[] >>
  imp_res_tac free_vars_i2_prompt_to_i3 >> rw[])

val free_vars_prog_to_i2 = store_thm("free_vars_prog_to_i2",
  ``∀x y a b c. prog_to_i2 x y = (a,b,c) ⇒
    free_vars_prog_i2 c = free_vars_prog_i1 y``,
  Induct_on`y`>>rw[prog_to_i2_def] >>
  rw[free_vars_prog_i2_def,free_vars_prog_i1_def] >>
  rw[GSYM free_vars_prog_i2_def,GSYM free_vars_prog_i1_def] >>
  fs[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  rw[] >>
  first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >> rw[] >>
  rw[free_vars_prog_i2_def] >> rw[GSYM free_vars_prog_i2_def] >>
  imp_res_tac free_vars_prompt_to_i2 >> rw[])

(*
val free_vars_top_to_i1 = store_thm("free_vars_top_to_i1",
  ``∀v w x p u y z p2.
    top_to_i1 v w x p = (u,y,z,p2) ⇒
    IMAGE Short (free_vars_prompt_i1 p2) = FV_top p``,
  Cases_on`p`>>rw[top_to_i1_def,LET_THM,FV_top_def] >>
  fs[UNCURRY] >> rw[free_vars_prompt_i1_def] >>
  free_vars_decs_i1_lemma
  free_vars_dec_i1_def
  free_vars_decs_i1_def
  FV_dec_def
  metis_tac[free_vars_decs_i2_decs_to_i2_any])

val free_vars_prog_to_i1 = store_thm("free_vars_prog_to_i1",
  ``∀v w x y a b c d. prog_to_i1 v w x y = (a,b,c,d) ⇒
    IMAGE Short (free_vars_prog_i1 d) = FV_prog y``,
  Induct_on`y`>>rw[prog_to_i1_def] >>
  rw[free_vars_prog_i1_def,FV_prog_def] >>
  rw[GSYM free_vars_prog_i1_def,GSYM FV_prog_def] >>
  fs[LET_THM] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  first_assum(split_applied_pair_tac o lhs o concl) >> fs[] >>
  rw[] >>
  first_x_assum(fn th => first_assum (mp_tac o MATCH_MP th)) >> rw[] >>
  rw[free_vars_prog_i1_def] >> rw[GSYM free_vars_prog_i1_def] >>
  imp_res_tac free_vars_top_to_i1 >> rw[])
*)

val all_env_i1_dom_def = Define`
  all_env_i1_dom (envM,envC,envE) = set (MAP FST envE)`

val all_env_i1_closed_def = Define`
  all_env_i1_closed (envM,envC,envE) ⇔
  EVERY closed_i1 (MAP SND envE) ∧
  EVERY (OPTION_EVERY closed_i1) envM`

val build_rec_env_i1_closed = store_thm("build_rec_env_i1_closed",
  ``∀defs env l.
    EVERY closed_i1 (MAP SND l) ∧
    EVERY closed_i1 (MAP SND (SND env)) ∧
    ALL_DISTINCT (MAP FST defs) ∧
    (∀d x b. MEM (d,x,b) defs ⇒ free_vars_i1 b ⊆
                                {x} ∪ set (MAP FST defs) ∪ set (MAP FST (SND env)))
    ⇒ EVERY closed_i1 (MAP SND (build_rec_env_i1 defs env l))``,
  rpt gen_tac >> PairCases_on`env` >>
  rw[build_rec_env_i1_def,bind_def,FOLDR_CONS_triple] >>
  rw[MAP_MAP_o,combinTheory.o_DEF,pairTheory.LAMBDA_PROD] >>
  asm_simp_tac(srw_ss())[EVERY_MEM,MEM_MAP,pairTheory.EXISTS_PROD] >>
  rw[Once closed_i1_cases] >>
  simp[MEM_MAP,EXISTS_PROD] >>
  conj_tac >- metis_tac[] >>
  simp[EVERY_MEM,FORALL_PROD] >>
  fs[MEM_MAP,EXISTS_PROD] >> metis_tac[])

val v_to_list_i1_closed = prove(
  ``∀v vs. v_to_list_i1 v = SOME vs ⇒ closed_i1 v ⇒ EVERY closed_i1 vs``,
  ho_match_mp_tac v_to_list_i1_ind >>
  simp[v_to_list_i1_def] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[])

val do_app_i1_closed = store_thm("do_app_i1_closed",
  ``∀s op vs s' res.
    EVERY closed_i1 vs ∧ EVERY (sv_every closed_i1) s ∧
    (do_app_i1 s op vs = SOME (s',res))
    ⇒ every_result closed_i1 closed_i1 res ∧
      EVERY (sv_every closed_i1) s'``,
  rpt gen_tac >> strip_tac >>
  imp_res_tac do_app_i1_cases >> fs[do_app_i1_def] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  fs[store_assign_def,store_alloc_def,store_lookup_def,LET_THM] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >> simp[prim_exn_i1_def] >>
  imp_res_tac v_to_list_i1_closed >>
  fs[EVERY_MEM] >>
  TRY (
    simp[REPLICATE_GENLIST,MEM_GENLIST,PULL_EXISTS] >>
    fs[MEM_EL,PULL_EXISTS] >>
    first_x_assum(qspec_then`lnum`mp_tac) >>
    simp[EVERY_MEM,MEM_EL,PULL_EXISTS,EL_LUPDATE] >>
    NO_TAC) >>
  TRY (
    rw[] >>
    imp_res_tac MEM_LUPDATE_E >> rw[] >>
    simp[EVERY_MEM] >> rw[] >>
    fs[MEM_EL,PULL_EXISTS] >>
    first_x_assum(qspec_then`lnum`mp_tac) >>
    simp[EL_LUPDATE,EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rw[] >> NO_TAC) >>
  metis_tac[MEM_LUPDATE_E,sv_every_def,MEM_EL,GREATER_EQ,NOT_LESS_EQUAL])

val do_opapp_i1_closed = store_thm("do_opapp_i1_closed",
  ``∀genv vs env exp.
    EVERY closed_i1 vs ∧
    EVERY (OPTION_EVERY closed_i1) genv ∧
    do_opapp_i1 genv vs = SOME (env,exp)
    ⇒
    all_env_i1_closed env ∧
    free_vars_i1 exp ⊆ all_env_i1_dom env``,
  rpt gen_tac >> simp[do_opapp_i1_def] >>
  BasicProvers.EVERY_CASE_TAC >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
  qpat_assum`closed_i1 (X Y)`mp_tac >>
  simp[Once closed_i1_cases] >> strip_tac >>
  simp[all_env_i1_closed_def,bind_def] >>
  simp[all_env_i1_dom_def] >>
  TRY(
    conj_tac >- (
      match_mp_tac build_rec_env_i1_closed >>
      simp[all_env_i1_closed_def] >> fs[FST_triple] >>
      fs[EVERY_MEM,FORALL_PROD])) >>
  fs[SUBSET_DEF,build_rec_env_i1_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX,find_recfun_lookup] >>
  imp_res_tac libPropsTheory.lookup_in3 >>
  fs[EVERY_MEM,FORALL_PROD] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >> rw[] >>
  first_x_assum(fn th => first_x_assum(strip_assume_tac o MATCH_MP th)) >> rw[])

val pmatch_i1_closed = store_thm("pmatch_i1_closed",
  ``(∀cenv s p v env env'.
      EVERY closed_i1 (MAP SND env) ∧ closed_i1 v ∧
      EVERY (sv_every closed_i1) s ∧
      (pmatch_i1 cenv s p v env = Match env') ⇒
      EVERY closed_i1 (MAP SND env') ∧
      (MAP FST env' = pat_bindings p [] ++ (MAP FST env))) ∧
    (∀cenv s ps vs env env'.
      EVERY closed_i1 (MAP SND env) ∧ EVERY closed_i1 vs ∧
      EVERY (sv_every closed_i1) s ∧
      (pmatch_list_i1 cenv s ps vs env = Match env') ⇒
      EVERY closed_i1 (MAP SND env') ∧
      (MAP FST env' = pats_bindings ps [] ++ MAP FST env))``,
  ho_match_mp_tac pmatch_i1_ind >>
  simp[pat_bindings_def,pmatch_i1_def,bind_def] >>
  rw[] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  fs[store_lookup_def] >> rw[] >>
  TRY (metis_tac[pat_bindings_accum]) >>
  fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
  metis_tac[sv_every_def])

val do_if_i1_free_vars = store_thm("do_if_i1_free_vars",
  ``(do_if_i1 v e2 e3 = SOME e) ⇒
    (free_vars_i1 e ⊆ free_vars_i1 e2 ∪ free_vars_i1 e3)``,
  fs[do_if_i1_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[] >>rw[])

val evaluate_i1_closed = store_thm("evaluate_i1_closed",
  ``(∀ck env s exp res.
     evaluate_i1 ck env s exp res ⇒
     free_vars_i1 exp ⊆ all_env_i1_dom env ∧
     all_env_i1_closed env ∧
     EVERY (sv_every closed_i1) (SND s)
     ⇒
     EVERY (sv_every closed_i1) (SND (FST res)) ∧
     every_result closed_i1 closed_i1 (SND res)) ∧
    (∀ck env s exps ress.
     evaluate_list_i1 ck env s exps ress ⇒
     free_vars_list_i1 exps ⊆ all_env_i1_dom env ∧
     all_env_i1_closed env ∧
     EVERY (sv_every closed_i1) (SND s)
     ⇒
     EVERY (sv_every closed_i1) (SND (FST ress)) ∧
     every_result (EVERY closed_i1) closed_i1 (SND ress)) ∧
    (∀ck env s v pes errv res.
     evaluate_match_i1 ck env s v pes errv res ⇒
     free_vars_pes_i1 pes ⊆ all_env_i1_dom env ∧
     all_env_i1_closed env ∧
     EVERY (sv_every closed_i1) (SND s) ∧
     closed_i1 v ∧ closed_i1 errv
     ⇒
     EVERY (sv_every closed_i1) (SND (FST res)) ∧
     every_result closed_i1 closed_i1 (SND res))``,
  ho_match_mp_tac evaluate_i1_ind >>
  strip_tac (* Lit *) >- rw[] >>
  strip_tac (* Raise *) >- rw[] >>
  strip_tac (* Handle *) >- (rw[] >> fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac (* Handle *) >- (
    rw[] >> fs[] >> rfs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,bind_def,MEM_MAP,EXISTS_PROD] >>
    PROVE_TAC[] ) >>
  strip_tac (* Handle *) >- (rw[] >> fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac (* Handle *) >- (rw[] >> fsrw_tac[DNF_ss][SUBSET_DEF]) >>
  strip_tac (* Con *) >- (
    rw[build_conv_i1_def] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >> rw[]) >>
  strip_tac (* Con *) >- rw[] >>
  strip_tac (* Con *) >- ( rw[] >> Cases_on`err` >> fsrw_tac[ETA_ss,DNF_ss][SUBSET_DEF] ) >>
  strip_tac (* Var *) >- (
    ntac 2 gen_tac >>
    PairCases_on`env` >>
    rw[all_env_i1_to_env_def,MEM_FLAT,MEM_MAP] >>
    fs[all_env_i1_dom_def,all_env_i1_closed_def] >>
    fs[EVERY_MEM,MAP_FLAT,MEM_FLAT,PULL_EXISTS] >>
    metis_tac[libPropsTheory.lookup_in,MEM_MAP]) >>
  strip_tac (* Var *) >- rw[] >>
  strip_tac (* Var_global *) >- (
    rw[] >>
    PairCases_on`env` >>
    fs[all_env_i1_to_genv_def,all_env_i1_closed_def,all_env_i1_dom_def] >>
    fs[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
    rpt(first_x_assum(qspec_then`n`mp_tac))>>simp[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac (* Fun *) >- (
    rw[] >>
    PairCases_on`env` >>
    fs[all_env_i1_to_cenv_def,all_env_i1_to_env_def
      ,all_env_i1_closed_def,all_env_i1_dom_def] >>
    rw[Once closed_i1_cases] >>
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[]) >>
  strip_tac (* Opapp *) >- (
    rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
    PairCases_on`env`>>fs[all_env_i1_to_genv_def] >>
    PROVE_TAC[do_opapp_i1_closed,all_env_i1_closed_def] ) >>
  strip_tac (* Opapp *) >- rw[] >>
  strip_tac (* Opapp *) >- rw[] >>
  strip_tac (* App *) >- (
    rpt gen_tac >> ntac 2 strip_tac >> fs[] >> rfs[] >>
    PROVE_TAC[do_app_i1_closed]) >>
  strip_tac (* App *) >- (
    rw[] >> fs[] >> rfs[] >>
    PROVE_TAC[do_app_i1_closed] ) >>
  strip_tac (* App *) >- rw[] >>
  strip_tac (* If *) >- (
    rw[] >> fs[] >>
    PROVE_TAC[do_if_i1_free_vars,SUBSET_DEF,IN_UNION]) >>
  strip_tac (* If *) >- (
    rw[] >> fs[] >> rfs[] >>
    PROVE_TAC[do_if_i1_free_vars,UNION_SUBSET,SUBSET_TRANS] ) >>
  strip_tac (* If *) >- rw[] >>
  strip_tac (* Mat *) >- rw[] >>
  strip_tac (* Mat *) >- rw[] >>
  strip_tac (* Let *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[bind_def,opt_bind_def] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,all_env_i1_dom_def,all_env_i1_closed_def] >>
    metis_tac[]) >>
  strip_tac (* Let *) >- rw[] >>
  strip_tac (* Letrec *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum match_mp_tac >>
    fs[FST_triple] >> rfs[] >>
    conj_tac >- (
      fs[GSYM MAP_MAP_o,LET_THM,FV_defs_MAP] >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_FLAT] >>
      gen_tac >> strip_tac >> res_tac >>
      fs[all_env_i1_dom_def] >>
      fs[build_rec_env_i1_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      fs[MEM_MAP,EXISTS_PROD] >>
      PROVE_TAC[] ) >>
    fs[all_env_i1_closed_def] >>
    match_mp_tac build_rec_env_i1_closed >> fs[all_env_i1_closed_def] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD,MEM_FLAT,LET_THM,free_vars_defs_i1_MAP,all_env_i1_dom_def] >>
    metis_tac[]) >>
  strip_tac (* Letrec *) >- rw[] >>
  strip_tac (* [] *) >- rw[] >>
  strip_tac (* :: *) >- rw[] >>
  strip_tac (* :: *) >- (rw[] >> Cases_on`err`>>fs[]) >>
  strip_tac (* :: *) >- rw[] >>
  strip_tac (* [] *) >- rw[] >>
  strip_tac (* Match *) >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    fs[] >> rfs[] >>
    first_x_assum match_mp_tac >>
    rator_x_assum`pmatch_i1`mp_tac >>
    specl_args_of_then``pmatch_i1``(CONJUNCT1 pmatch_i1_closed)mp_tac>>
    fs[all_env_i1_closed_def] >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,FORALL_PROD,MEM_MAP,MEM_FLAT,all_env_i1_dom_def] >>
    metis_tac[]) >>
  strip_tac (* Match *) >- rw[] >>
  strip_tac (* Match *) >- rw[] >>
  rw[])

val free_vars_dec_i1_def = Define`
  free_vars_dec_i1 (Dlet_i1 _ e) = free_vars_i1 e ∧
  free_vars_dec_i1 (Dletrec_i1 funs) = BIGUNION (set (MAP (λ(f,x,e). free_vars_i1 e DIFF {x}) funs)) ∧
  free_vars_dec_i1 (Dtype_i1 _ _) = {} ∧
  free_vars_dec_i1 (Dexn_i1 _ _ _) = {}`
val _ = export_rewrites["free_vars_dec_i1_def"]

val evaluate_dec_i1_closed = store_thm("evaluate_dec_i1_closed",
  ``∀ck genv cenv st d res. evaluate_dec_i1 ck genv cenv st d res ⇒
      free_vars_dec_i1 d = ∅ ∧
      EVERY (OPTION_EVERY closed_i1) genv ∧
      EVERY (sv_every closed_i1) (SND (FST st))
      ⇒
      EVERY (sv_every closed_i1) (SND(FST(FST res))) ∧
      every_result (EVERY closed_i1 o SND) closed_i1 (SND res)``,
  ho_match_mp_tac evaluate_dec_i1_ind >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  TRY (
    first_x_assum(mp_tac o (MATCH_MP (CONJUNCT1 evaluate_i1_closed))) >>
    simp[all_env_i1_dom_def,emp_def,all_env_i1_closed_def] ) >>
  simp[EVERY_MAP,UNCURRY,Once closed_i1_cases] >>
  fs[LIST_TO_SET_EQ_SING,EVERY_MAP,EVERY_MEM,FORALL_PROD,SUBSET_DEF] >>
  fs[EXTENSION] >> metis_tac[])

val evaluate_decs_i1_closed = store_thm("evaluate_decs_i1_closed",
  ``∀ck genv cenv s decs res. evaluate_decs_i1 ck genv cenv s decs res ⇒
      BIGUNION (set (MAP free_vars_dec_i1 decs)) = ∅ ∧
      EVERY (OPTION_EVERY closed_i1) genv ∧
      EVERY (sv_every closed_i1) (SND (FST s))
      ⇒
      EVERY (sv_every closed_i1) (SND(FST(FST res))) ∧
      EVERY closed_i1 (FST(SND(SND res))) ∧
      OPTION_EVERY (every_error_result closed_i1) (SND(SND(SND res)))``,
  ho_match_mp_tac evaluate_decs_i1_ind >> simp[] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum(mp_tac o (MATCH_MP evaluate_dec_i1_closed)) >>
  simp[] >> ntac 2 strip_tac >>
  fs[INSERT_EQ_SING] >>
  fs[SUBSET_DEF] >>
  first_x_assum match_mp_tac >>
  simp[LIST_TO_SET_EQ_SING,EVERY_MEM] >>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS])

val free_vars_decs_i1_lemma = store_thm("free_vars_decs_i1_lemma",
  ``∀ds. BIGUNION (set (MAP free_vars_dec_i1 ds)) ⊆ free_vars_decs_i1 ds``,
  Induct >> simp[] >> Cases >>
  fs[free_vars_decs_i1_def,free_vars_decs_i2_def,decs_to_i2_def,decs_to_i3_def,UNCURRY,LET_THM] >>
  fs[free_vars_i2_decs_to_i3] >>
  fsrw_tac[DNF_ss][SUBSET_DEF] >>
  TRY(metis_tac[free_vars_decs_i2_decs_to_i2_any]) >>
  simp[funs_to_i2_MAP,free_vars_i2_init_global_funs,PULL_EXISTS,MEM_MAP,EXISTS_PROD] >>
  metis_tac[])

val evaluate_prompt_i1_closed = store_thm("evaluate_prompt_i1_closed",
  ``∀ck genv cenv s p res.
      evaluate_prompt_i1 ck genv cenv s p res ⇒
      free_vars_prompt_i1 p = ∅ ∧
      EVERY (OPTION_EVERY closed_i1) genv ∧
      EVERY (sv_every closed_i1) (SND(FST s))
      ⇒
      EVERY (sv_every closed_i1) (SND(FST(FST res))) ∧
      EVERY (OPTION_EVERY closed_i1) (FST(SND(SND res))) ∧
      OPTION_EVERY (every_error_result closed_i1) (SND(SND(SND res)))``,
  ho_match_mp_tac evaluate_prompt_i1_ind >>
  simp[free_vars_prompt_i1_def] >>
  strip_tac >- (
    rpt gen_tac >> ntac 2 strip_tac >>
    first_x_assum(mp_tac o (MATCH_MP evaluate_decs_i1_closed)) >>
    simp[] >>
    discharge_hyps >- ( qspec_then`ds`mp_tac free_vars_decs_i1_lemma >> simp[] ) >>
    simp[EVERY_MAP,ETA_AX] ) >>
  rpt gen_tac >> ntac 2 strip_tac >>
  first_x_assum(mp_tac o (MATCH_MP evaluate_decs_i1_closed)) >>
  simp[] >>
  discharge_hyps >- ( qspec_then`ds`mp_tac free_vars_decs_i1_lemma >> simp[] ) >>
  simp[EVERY_GENLIST,EVERY_MAP,ETA_AX])

val evaluate_prog_i1_closed = store_thm("evaluate_prog_i1_closed",
  ``∀ck genv cenv s prog res. evaluate_prog_i1 ck genv cenv s prog res ⇒
      free_vars_prog_i1 prog = {} ∧
      EVERY (OPTION_EVERY closed_i1) genv ∧
      EVERY (sv_every closed_i1) (SND(FST s)) ⇒
      EVERY (OPTION_EVERY closed_i1) (FST(SND(SND res)))``,
  ho_match_mp_tac evaluate_prog_i1_ind >> simp[] >>
  conj_tac >> rpt gen_tac >> strip_tac >>
  simp[free_vars_prog_i1_def] >> strip_tac >>
  imp_res_tac evaluate_prompt_i1_closed >> fs[] >>
  fs[free_vars_prog_i1_def])

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
