open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory rich_listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory arithmeticTheory lcsymtacs quantHeuristicsLib quantHeuristicsLibAbbrev
open MiniMLTerminationTheory miniMLExtraTheory miscTheory compileTerminationTheory intLangTheory bytecodeTerminationTheory evaluateEquationsTheory expToCexpTheory pmatchTheory labelClosuresTheory bytecodeEvalTheory
val _ = intLib.deprecate_int()
val _ = new_theory "compileCorrectness"

val exp_pred_def = tDefine "exp_pred"`
  (exp_pred (Raise _) = T) ∧
  (exp_pred (Lit _) = T) ∧
  (exp_pred (Con _ es) = EVERY exp_pred es) ∧
  (exp_pred (Var _) = T) ∧
  (exp_pred (Fun _ _) = F) ∧
  (exp_pred (App (Opn _) e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App (Opb Lt) e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App (Opb Leq) e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App (Opb _) _ _) = F) ∧
  (exp_pred (App Equality e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App Opapp _ _) = F) ∧
  (exp_pred (Log _ e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (If e1 e2 e3) = exp_pred e1 ∧ exp_pred e2 ∧ exp_pred e3) ∧
  (exp_pred (Mat _ _) = F) ∧
  (exp_pred (Let _ _ _) = F) ∧
  (exp_pred (Letrec _ _) = F)`
  (WF_REL_TAC `measure exp_size` >>
   srw_tac[ARITH_ss][exp6_size_thm] >>
   Q.ISPEC_THEN`exp_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["exp_pred_def"]

val Cexp_pred_def = tDefine "Cexp_pred"`
  (Cexp_pred (CDecl _) = T) ∧
  (Cexp_pred (CRaise _) = T) ∧
  (Cexp_pred (CVar _) = T) ∧
  (Cexp_pred (CLit _) = T) ∧
  (Cexp_pred (CCon _ es) = EVERY Cexp_pred es) ∧
  (Cexp_pred (CTagEq e _) = Cexp_pred e) ∧
  (Cexp_pred (CProj e _) = Cexp_pred e) ∧
  (Cexp_pred (CLet _ _ _) = F) ∧
  (Cexp_pred (CLetfun _ _ _ _) = F) ∧
  (Cexp_pred (CFun _ _) = F) ∧
  (Cexp_pred (CCall _ _) = F) ∧
  (Cexp_pred (CPrim2 _ e1 e2) = Cexp_pred e1 ∧ Cexp_pred e2) ∧
  (Cexp_pred (CIf e1 e2 e3) = Cexp_pred e1 ∧ Cexp_pred e2 ∧ Cexp_pred e3)`
  (WF_REL_TAC `measure Cexp_size` >>
   srw_tac[ARITH_ss][Cexp4_size_thm] >>
   Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["Cexp_pred_def"]
val Cexp_pred_ind = theorem"Cexp_pred_ind"

val exp_pred_Cexp_pred = store_thm("exp_pred_Cexp_pred",
  ``∀m e. exp_pred e ⇒ Cexp_pred (exp_to_Cexp m e)``,
  ho_match_mp_tac exp_to_Cexp_nice_ind >>
  rw[exp_to_Cexp_def,LET_THM,exps_to_Cexps_MAP,EVERY_MAP] >>
  TRY (
    BasicProvers.EVERY_CASE_TAC >>
    rw[] >> fs[] ) >>
  fs[EVERY_MEM,FORALL_PROD] >>
  Cases_on `pat_to_Cpat m [] p` >> fs[])

val Cexp_pred_free_labs = store_thm("Cexp_pred_free_labs",
  ``∀e. Cexp_pred e ⇒ (free_labs e = {})``,
  ho_match_mp_tac Cexp_pred_ind >> rw[IMAGE_EQ_SING] >> fs[EVERY_MEM])

(* TODO: move *)
val FLAT_EQ_NIL = store_thm("FLAT_EQ_NIL",
  ``!ls. (FLAT ls = []) = (EVERY ($= []) ls)``,
  Induct THEN SRW_TAC[][EQ_IMP_THM])

val Cexp_pred_free_bods = store_thm("Cexp_pred_free_bods",
  ``∀e. Cexp_pred e ⇒ (free_bods e = [])``,
  ho_match_mp_tac Cexp_pred_ind >> rw[FLAT_EQ_NIL] >> fs[EVERY_MEM,MEM_MAP] >> PROVE_TAC[])

val Cexp_pred_repeat_label_closures = store_thm("Cexp_pred_repeat_label_closures",
  ``(∀e n ac. Cexp_pred e ⇒ (repeat_label_closures e n ac = (e,n,ac))) ∧
    (∀n ac ls. EVERY (Cexp_pred o SND) ls ⇒ (label_code_env n ac ls = (n,(REVERSE ls)++ac)))``,
  ho_match_mp_tac repeat_label_closures_ind >>
  strip_tac >- (
    rw[] >>
    rw[repeat_label_closures_def] >>
    imp_res_tac (CONJUNCT1 label_closures_thm) >>
    imp_res_tac Cexp_pred_free_labs >>
    imp_res_tac Cexp_pred_free_bods >>
    fs[LET_THM] >>
    fs[Abbr`s`] ) >>
  strip_tac >- rw[repeat_label_closures_def] >>
  rw[repeat_label_closures_def] >> fs[])

val FOLDL_invariant = store_thm("FOLDL_invariant",
  ``!P f ls a. (P a) /\ (!x y . MEM y ls /\ P x ==> P (f x y)) ==> P (FOLDL f a ls)``,
  NTAC 2 GEN_TAC THEN
  Induct THEN SRW_TAC[][])

val Cexp_pred_calculate_ldefs = store_thm("Cexp_pred_calculate_ldefs",
  ``∀c ls e. Cexp_pred e ⇒ (calculate_ldefs c ls e = ls)``,
  ho_match_mp_tac calculate_ldefs_ind >>
  rw[calculate_ldefs_def] >>
  qmatch_abbrev_tac `FOLDL f ls es = ls` >>
  qsuff_tac `($= ls) (FOLDL f ls es)` >- rw[] >>
  ho_match_mp_tac FOLDL_invariant >>
  rw[Abbr`f`] >> match_mp_tac EQ_SYM >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  fs[EVERY_MEM])

val _ = overload_on("next_addr", ``λil ls. SUM (MAP (SUC o il) (FILTER ($~ o is_Label) ls))``)

val bc_finish_def = Define`
  bc_finish s1 s2 = bc_next^* s1 s2 ∧ (s2.pc = next_addr s2.inst_length s2.code)`

val repl_exp_contab = store_thm("repl_exp_contab",
  ``(repl_exp rs exp = (rs',c)) ==> (rs'.contab = rs.contab)``,
  rw[repl_exp_def,compile_Cexp_def,LET_THM] >>
  qabbrev_tac`p=repeat_label_closures (exp_to_Cexp (cmap rs.contab) exp) rs.rnext_label []` >>
  PairCases_on`p`>>fs[] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> rw[])

val compile_varref_decl = store_thm("compile_varref_decl",
  ``(compile_varref s x).decl = s.decl``,
  Cases_on `x` >> rw[])
val _ = export_rewrites["compile_varref_decl"]

val compile_closures_decl = store_thm("compile_closures_decl",
  ``(compile_closures n s defs).decl = s.decl``,
  rw[compile_closures_def] >>
  `s'.decl = s.decl` by (
    qunabbrev_tac `s'` >>
    rpt (pop_assum kall_tac) >>
    qid_spec_tac `s` >>
    Induct_on `n` >>
    rw[Once num_fold_def] ) >>
  `s''.decl = s'.decl` by (
    qmatch_assum_abbrev_tac `FOLDL f a defs = (s'',k,ecs)` >>
    `(($= s'.decl) o compiler_state_decl o FST) (FOLDL f a defs)` by (
      match_mp_tac FOLDL_invariant >>
      qunabbrev_tac`a` >> fs[] >>
      qunabbrev_tac`f` >> fs[FORALL_PROD] >>
      rw[] >>
      BasicProvers.EVERY_CASE_TAC >> rw[] >>
      unabbrev_all_tac >> rw[] ) >>
    pop_assum mp_tac >> rw[] ) >>
  `s'''.decl = s''.decl` by (
    qmatch_assum_abbrev_tac `FOLDL f a ls = (s''',x)` >>
    `(($= s''.decl) o compiler_state_decl o FST) (FOLDL f a ls)` by (
      match_mp_tac FOLDL_invariant >>
      qunabbrev_tac`a` >> fs[] >>
      qunabbrev_tac`f` >> fs[FORALL_PROD] >>
      rw[LET_THM] >>
      qmatch_abbrev_tac `q.decl = (FOLDL g b l).decl` >>
      `(($= q.decl) o compiler_state_decl) (FOLDL g b l)` by (
        match_mp_tac FOLDL_invariant >>
        qunabbrev_tac`b`>>fs[] >>
        qunabbrev_tac`g`>>gen_tac>>Cases>>fs[] ) >>
      pop_assum mp_tac >> rw[Abbr`b`] ) >>
    pop_assum mp_tac >> rw[] ) >>
  `s''''.decl = s'''.decl` by (
    qmatch_assum_abbrev_tac `num_fold f a n = (s'''',X)` >>
    `!n a. (FST (num_fold f a n)).decl = (FST a).decl` by (
      Induct >- rw[Once num_fold_def,Abbr`f`] >>
      rw[Once num_fold_def] >>
      rw[Abbr`f`,LET_THM] >>
      Cases_on `a'` >> rw[] ) >>
    pop_assum (qspecl_then [`n`,`a`] mp_tac) >>
    rw[Abbr`a`] ) >>
  qmatch_abbrev_tac `(num_fold f a n).decl = s.decl` >>
  `!n b. (num_fold f b n).decl = b.decl` by (
    Induct >- rw[Once num_fold_def] >>
    rw[Once num_fold_def] >>
    rw[Abbr`f`] ) >>
  pop_assum (qspecl_then [`n`,`a`] mp_tac) >>
  rw[Abbr`a`] )
val _ = export_rewrites["compile_closures_decl"]

val compile_decl_NONE = store_thm("compile_decl_NONE",
  ``(∀s e. (((compile s e).decl = NONE) = (s.decl = NONE))) ∧
    (∀env sz e n s xs. (((compile_bindings env sz e n s xs).decl = NONE) = (s.decl = NONE)))``,
  ho_match_mp_tac compile_ind >>
  rw[compile_def,incsz_def,emit_def]
  >- (
    Cases_on `s.decl` >> rw[] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    rw[] )
  >> TRY (
    unabbrev_all_tac >>
    Cases_on `dt` >> fs[] >>
    NO_TAC ) >>
  rw[]
  >- ( qunabbrev_tac`s'''` >> rw[] )
  >- ( fs[] )
  >- ( unabbrev_all_tac >> fs[] )
  >- (
    unabbrev_all_tac >> rw[] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] ))
val _ = export_rewrites["compile_decl_NONE"]

val cce_aux_decl_NONE = store_thm("cce_aux_decl_NONE",
  ``((cce_aux c s x).decl = NONE) = (s.decl = NONE)``,
  Cases_on `x` >>
  rw[cce_aux_def] >>
  qmatch_assum_abbrev_tac `FOLDL f a r = (s',k)` >>
  `((λp. ((FST p).decl = NONE) = (s.decl = NONE))) (FOLDL f a r)` by (
    match_mp_tac FOLDL_invariant >>
    fs[Abbr`a`] >>
    Cases >> Cases >>
    rw[Abbr`f`,LET_THM] >>
    rw[UNCURRY] ) >>
  pop_assum mp_tac >> rw[] )
val _ = export_rewrites["cce_aux_decl_NONE"]

val compile_code_env_decl_NONE = store_thm("compile_code_env_decl_NONE",
  ``((compile_code_env c s ldefs).decl = NONE) = (s.decl = NONE)``,
  rw[compile_code_env_def] >>
  rw[Abbr`s'''`] >>
  qmatch_abbrev_tac `((FOLDL f x y).decl = NONE) = X` >>
  `(λa. (a.decl = NONE) = (s.decl = NONE)) (FOLDL f x y)` by (
    match_mp_tac FOLDL_invariant >>
    rw[Abbr`X`,Abbr`x`,Abbr`s''`,Abbr`f`] ) >>
  pop_assum mp_tac >> rw[])
val _ = export_rewrites["compile_code_env_decl_NONE"]

val calculate_ecs_decl = store_thm("calculate_ecs_decl",
  ``(calculate_ecs c s ldefs).decl = s.decl``,
  rw[calculate_ecs_def] >>
  qmatch_abbrev_tac `(FOLDL f s y).decl = s.decl` >>
  `(($= s.decl) o compiler_state_decl) (FOLDL f s y)` by (
    match_mp_tac FOLDL_invariant >>
    fs[Abbr`f`] >>
    gen_tac >> Cases >> rw[] >>
    qmatch_assum_abbrev_tac `FOLDL f (x,0) r = (s',k)` >>
    `(($= x.decl) o compiler_state_decl o FST) (FOLDL f (x,0) r)` by (
      match_mp_tac FOLDL_invariant >>
      fs[] >>
      Cases >> Cases >> rw[Abbr`f`] >>
      unabbrev_all_tac >> rw[] ) >>
    pop_assum mp_tac >> rw[] ) >>
  pop_assum mp_tac >> rw[] )
val _ = export_rewrites["calculate_ecs_decl"]

val el_check_def = Define`
  el_check n ls = if n < LENGTH ls then SOME (EL n ls) else NONE`
val _ = export_rewrites["el_check_def"]

val lookup_ct_def = Define`
  (lookup_ct sz st rs (CTLet n) = if sz < n then NONE else el_check (sz - n) st) ∧
  (lookup_ct sz st rs (CTArg n) = el_check (sz + n) st) ∧
  (lookup_ct sz st rs (CTEnv n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 2 vs => el_check n vs | _ => NONE)) ∧
  (lookup_ct sz st rs (CTRef n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 2 vs =>
     OPTION_BIND (el_check n vs)
     (λv. case v of RefPtr p => FLOOKUP rs p | _ => NONE)
     | _ => NONE))`
val _ = export_rewrites["lookup_ct_def"]

val (Cv_bv_rules,Cv_bv_ind,Cv_bv_cases) = Hol_reln`
  (Cv_bv pp (CLitv (IntLit k)) (Number k)) ∧
  (Cv_bv pp (CLitv (Bool b)) (bool_to_val b)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CConv cn vs) (Block (cn+3) bvs)) ∧
  ((pp = (c,l2a,rfs)) ∧
   (find_index n ns 0 = SOME i) ∧
   (EL i defs = (xs,INR l)) ∧
   (FLOOKUP c l = SOME e) ∧
   (fvs = SET_TO_LIST (free_vars c e)) ∧
   (benv = if fvs = [] then Number 0 else Block 0 bvs) ∧
   (LENGTH bvs = LENGTH fvs) ∧
   (l2a l = SOME a) ∧
   (∀i x bv. i < LENGTH fvs ∧ (x = EL i fvs) ∧ (bv = EL i bvs) ⇒
     if MEM x xs then x ∈ FDOM env ∧ Cv_bv pp (env ' x) bv else
     ∃j p. (find_index x ns 0 = SOME j) ∧
           (bv = RefPtr p) ∧
           (p ∈ FDOM rfs) ∧
           Cv_bv pp (CRecClos env ns defs (EL j ns)) (rfs ' p))
   ⇒ Cv_bv pp (CRecClos env ns defs n) (Block 2 [CodePtr a; benv]))`

val Cv_bv_ov = store_thm("Cv_bv_ov",
  ``∀m pp Cv bv. Cv_bv pp Cv bv ⇒ (Cv_to_ov m Cv = bv_to_ov m bv)``,
  ntac 2 gen_tac >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    Cases_on `b` >> fs[] ) >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    fsrw_tac[ARITH_ss][] >>
    rw[MAP_EQ_EVERY2] >>
    fs[EVERY2_EVERY] ) >>
  rw[bv_to_ov_def])

(* TODO: move *)
val fmap_linv_def = Define`
  fmap_linv f1 f2 = (FDOM f2 = FRANGE f1) /\ (!x. x IN FDOM f1 ==> (FLOOKUP f2 (FAPPLY f1 x) = SOME x))`

val fmap_linv_unique = store_thm("fmap_linv_unique",
  ``!f f1 f2. fmap_linv f f1 /\ fmap_linv f f2 ==> (f1 = f2)``,
  SRW_TAC[][fmap_linv_def,GSYM fmap_EQ_THM] THEN
  FULL_SIMP_TAC(srw_ss())[FRANGE_DEF,FLOOKUP_DEF] THEN
  PROVE_TAC[])

val INJ_has_fmap_linv = store_thm("INJ_has_fmap_linv",
  ``INJ (FAPPLY f) (FDOM f) (FRANGE f) ==> ?g. fmap_linv f g``,
  STRIP_TAC THEN
  Q.EXISTS_TAC `FUN_FMAP (\x. @y. FLOOKUP f y = SOME x) (FRANGE f)` THEN
  SRW_TAC[][fmap_linv_def,FLOOKUP_FUN_FMAP,FRANGE_DEF] THEN1 PROVE_TAC[] THEN
  SELECT_ELIM_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [INJ_DEF,FRANGE_DEF,FLOOKUP_DEF])

val has_fmap_linv_inj = store_thm("has_fmap_linv_inj",
  ``(?g. fmap_linv f g) = (INJ (FAPPLY f) (FDOM f) (FRANGE f))``,
  Tactical.REVERSE EQ_TAC THEN1 PROVE_TAC[INJ_has_fmap_linv] THEN
  SRW_TAC[][fmap_linv_def,INJ_DEF,EQ_IMP_THM]
  THEN1 ( SRW_TAC[][FRANGE_DEF] THEN PROVE_TAC[] )
  THEN1 ( FULL_SIMP_TAC(srw_ss())[FLOOKUP_DEF] THEN PROVE_TAC[] ))

val fmap_linv_FAPPLY = store_thm("fmap_linv_FAPPLY",
  ``fmap_linv f g /\ x IN FDOM f ==> (g ' (f ' x) = x)``,
  SRW_TAC[][fmap_linv_def,FLOOKUP_DEF])

val all_Ccns_def = tDefine "all_Ccns"`
  (all_Ccns (CLitv _) = {}) ∧
  (all_Ccns (CConv cn vs) = cn INSERT BIGUNION (IMAGE all_Ccns (set vs))) ∧
  (all_Ccns (CRecClos env _ _ _) = BIGUNION (IMAGE all_Ccns (FRANGE env)))`
  (WF_REL_TAC `measure Cv_size` >>
   srw_tac[ARITH_ss][Cvs_size_thm,fmap_size_def] >>
   Q.ISPEC_THEN`Cv_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][] >>
   fs[FRANGE_DEF] >> rw[] >>
   qmatch_abbrev_tac `q:num < (SUM_IMAGE f s) + r` >>
   qsuff_tac `q <= SUM_IMAGE f s` >- srw_tac[ARITH_ss][Abbr`r`] >>
   `f x <= SUM_IMAGE f s` by (
     match_mp_tac SUM_IMAGE_IN_LE >> rw[Abbr`s`] ) >>
   qsuff_tac `q <= f x` >- srw_tac[ARITH_ss][] >>
   unabbrev_all_tac >> rw[])
val all_Ccns_def = save_thm("all_Ccns_def",SIMP_RULE(srw_ss()++ETA_ss)[]all_Ccns_def)
val _ = export_rewrites["all_Ccns_def"]

val all_cns_def = tDefine "all_cns"`
  (all_cns (Litv _) = {}) ∧
  (all_cns (Conv cn vs) = cn INSERT BIGUNION (IMAGE all_cns (set vs))) ∧
  (all_cns (Closure env _ _) = BIGUNION (IMAGE all_cns (set (MAP SND env)))) ∧
  (all_cns (Recclosure env _ _) = BIGUNION (IMAGE all_cns (set (MAP SND env))))`
  (WF_REL_TAC `measure v_size` >>
   srw_tac[ARITH_ss][v1_size_thm,v3_size_thm] >>
   Q.ISPEC_THEN`v_size`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][SUM_MAP_v2_size_thm])
val all_cns_def = save_thm("all_cns_def",SIMP_RULE(srw_ss()++ETA_ss)[]all_cns_def)
val _ = export_rewrites["all_cns_def"]

val v_to_Cv_ov = store_thm("v_to_Cv_ov",
  ``(∀m v w. (all_cns v ⊆ FDOM m) ∧ fmap_linv m w ==> (Cv_to_ov w (v_to_Cv m v) = v_to_ov v)) ∧
    (∀m vs w. (BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m) ∧ fmap_linv m w ==> (MAP (Cv_to_ov w) (vs_to_Cvs m vs) = MAP v_to_ov vs)) ∧
    (∀(m:string|->num) (env:envE). T)``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def] >> rw[Cv_to_ov_def] >>
  srw_tac[ETA_ss][fmap_linv_FAPPLY])

(* TODO: move *)
val bc_find_loc_aux_def = BytecodeTheory.bc_find_loc_aux_def
val prim2_to_bc_def = CompileTheory.prim2_to_bc_def
val _ = export_rewrites["Compile.prim2_to_bc_def"]

val _ = overload_on("mk_pp", ``λc bs.
  (c
  ,combin$C (bc_find_loc_aux bs.code bs.inst_length) 0
  ,bs.refs
  )``)

val Cenv_bs_def = Define`
  Cenv_bs c Cenv (renv:ctenv) sz bs =
    fmap_rel
      (λCv b. case lookup_ct sz bs.stack bs.refs b of NONE => F
         | SOME bv => Cv_bv (mk_pp c bs) Cv bv)
    Cenv renv`

val env_rs_def = Define`
  env_rs env bs rs =
    let Cenv = alist_to_fmap (env_to_Cenv (cmap rs.contab) env) in
    ∃c. Cenv_bs c Cenv rs.renv rs.rsz bs`

val el_of_addr_def = Define`
  (el_of_addr il n [] = NONE) ∧
  (el_of_addr il n (x::xs) =
   if is_Label x then OPTION_BIND (el_of_addr il n xs) (λm. SOME (m + 1)) else
     if n = 0 then SOME (0:num) else
       if n < il x + 1 then NONE else
         OPTION_BIND (el_of_addr il (n - (il x + 1)) xs) (λm. SOME (m + 1)))`
val _ = export_rewrites["el_of_addr_def"]

val el_of_addr_LESS_LENGTH = store_thm("el_of_addr_LESS_LENGTH",
  ``∀il ls n m. (el_of_addr il n ls = SOME m) ⇒ m < LENGTH ls``,
  gen_tac >> Induct >> srw_tac[ARITH_ss][] >>
  res_tac >> fsrw_tac[ARITH_ss][])

val bc_fetch_aux_el_of_addr = store_thm("bc_fetch_aux_el_of_addr",
  ``∀c il pc. bc_fetch_aux c il pc = OPTION_BIND (el_of_addr il pc c) (λn. SOME (EL n c))``,
  Induct >> rw[] >>
  Q.PAT_ABBREV_TAC`opt = el_of_addr il pcX c` >>
  Cases_on `opt` >> fs[] >>
  rw[GSYM arithmeticTheory.ADD1])

val addr_of_el_def = Define`
  (addr_of_el il n [] = NONE) ∧
  (addr_of_el il n (x::xs) =
   if n = 0 then if is_Label x then NONE else SOME 0 else
     OPTION_BIND (addr_of_el il (n - 1) xs) (λm. SOME (m + (if is_Label x then 0 else il x + 1))))`
val _ = export_rewrites["addr_of_el_def"]

val bc_fetch_aux_addr_of_el = store_thm("bc_fetch_aux_addr_of_el",
  ``∀c il pc n. (addr_of_el il n c = SOME pc) ⇒ (bc_fetch_aux c il pc = SOME (EL n c))``,
  Induct >> rw[] >>
  Cases_on `n` >> fs[] >>
  spose_not_then strip_assume_tac >>
  DECIDE_TAC)

val bc_fetch_aux_not_label = store_thm("bc_fetch_aux_not_label",
  ``∀c il pc i. (bc_fetch_aux c il pc = SOME i) ⇒ ¬is_Label i``,
  Induct >> rw[] >> fs[] >> PROVE_TAC[])

val dest_Label_def = Define`(dest_Label (Label n) = n)`
val _ = export_rewrites["dest_Label_def"]

val calculate_labels_thm = store_thm("calculate_labels_thm",
  ``∀il m n bc lbc m' n' bc'.
      (calculate_labels il m n bc lbc = (m',n',bc')) ∧ ALL_DISTINCT (FILTER is_Label lbc) ⇒
      (bc' = (REVERSE (FILTER ($~ o is_Label) lbc) ++ bc)) ∧
      (let ls = MAP dest_Label (FILTER is_Label lbc) in
        (m' = m |++ ZIP (ls, MAP (THE o combin$C (bc_find_loc_aux lbc il) n) ls))) ∧
      (n' = n + SUM (MAP (SUC o il) (FILTER ($~ o is_Label) lbc)))``,
  ho_match_mp_tac calculate_labels_ind >>
  strip_tac >- (
    rw[calculate_labels_def,LET_THM,FUPDATE_LIST_THM] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp_tac(std_ss)[Once calculate_labels_def] >>
    rpt gen_tac >> strip_tac >>
    `ALL_DISTINCT (FILTER is_Label lbc)` by (
      pop_assum mp_tac >>
      rpt (pop_assum kall_tac) >>
      rw[] ) >>
    res_tac >>
    full_simp_tac(std_ss)[LET_THM] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >> pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    rw[FUPDATE_LIST_THM,bc_find_loc_aux_def] >>
    AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
    rw[MAP_EQ_f,MEM_MAP,MEM_FILTER] >>
    AP_TERM_TAC >>
    rw[bc_find_loc_aux_def] >>
    fs[MEM_FILTER] >>
    Cases_on `y` >> fs[]) >>
  REPEAT (
    strip_tac >- (
      rpt gen_tac >> strip_tac >>
      simp_tac(std_ss)[Once calculate_labels_def] >>
      rpt gen_tac >> strip_tac >>
      `ALL_DISTINCT (FILTER is_Label lbc)` by (
        pop_assum mp_tac >>
        rpt (pop_assum kall_tac) >>
        rw[] ) >>
      res_tac >>
      full_simp_tac(std_ss)[LET_THM] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      rpt (pop_assum kall_tac) >>
      srw_tac[ARITH_ss][] >>
      AP_TERM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
      rw[MAP_EQ_f,MEM_MAP,MEM_FILTER] >>
      AP_TERM_TAC >>
      rw[bc_find_loc_aux_def] )))

val replace_lab_def = Define`
  (replace_lab m (Jump (Lab l)) = Jump (Addr (FAPPLY m l))) ∧
  (replace_lab m (JumpIf (Lab l)) = JumpIf (Addr (m ' l))) ∧
  (replace_lab m (Call (Lab l)) = Call (Addr (m ' l))) ∧
  (replace_lab m (PushPtr (Lab l)) = PushPtr (Addr (m ' l))) ∧
  (replace_lab m i = i)`
val _ = export_rewrites["replace_lab_def"]

val replace_labels_thm = store_thm("replace_labels_thm",
  ``∀m a ls. (replace_labels m a ls = (REVERSE (MAP (replace_lab m) ls)) ++ a)``,
  ho_match_mp_tac replace_labels_ind >> rw[replace_labels_def])

val bc_fetch_aux_MAP = store_thm("bc_fetch_aux_MAP",
  ``!il f. (∀x. il (f x) = il x) ∧ (∀x. is_Label (f x) = is_Label x) ⇒
      ∀ls n. (bc_fetch_aux (MAP f ls) il n = OPTION_MAP f (bc_fetch_aux ls il n))``,
  ntac 2 gen_tac >> strip_tac >>
  Induct >> rw[bc_fetch_aux_def])

val bc_fetch_MAP = store_thm("bc_fetch_MAP",
  ``∀f s. (∀x. s.inst_length (f x) = s.inst_length x) ∧ (∀x. is_Label (f x) = is_Label x) ⇒
    (bc_fetch (s with <| code := MAP f s.code |>) = OPTION_MAP f (bc_fetch s))``,
  rw[bc_fetch_def,bc_fetch_aux_MAP])

val is_Label_replace_lab = store_thm("is_Label_replace_lab",
  ``∀x. is_Label (replace_lab m x) = is_Label x``,
  Cases >> rw[] >> Cases_on `l` >> rw[])
val _ = export_rewrites["is_Label_replace_lab"]

val good_il_def = Define`
  good_il il =
  (∀x. il (Jump x) = il (Jump ARB)) ∧
  (∀x. il (JumpIf x) = il (JumpIf ARB)) ∧
  (∀x. il (Call x) = il (Call ARB)) ∧
  (∀x. il (PushPtr x) = il (PushPtr ARB))`

val il_replace_lab = store_thm("il_replace_lab",
  ``good_il il ⇒ ∀m x. (il (replace_lab m x) = il x)``,
  rw[good_il_def] >>
  Cases_on `x` >> rw[] >>
  Cases_on `l` >> rw[])

val bc_fetch_with_stack = store_thm("bc_fetch_with_stack",
  ``bc_fetch (s with stack := st) = bc_fetch s``,
  rw[bc_fetch_def])

val bump_pc_with_stack = store_thm("bump_pc_with_stack",
  ``bump_pc (s with stack := st) = (bump_pc s) with stack := st``,
  rw[bump_pc_def,bc_fetch_with_stack] >>
  BasicProvers.EVERY_CASE_TAC)

val tac = (
    rw[LET_THM] >>
    match_mp_tac bc_eval1_SOME >>
    Q.PAT_ABBREV_TAC`f = replace_lab X` >>
    qspecl_then[`f`,`s1`] mp_tac bc_fetch_MAP >>
    qunabbrev_tac`f` >> rw[il_replace_lab] >>
    rw[bc_eval1_def] >>
    fs[bc_eval_stack_thm] >>
    fs[bump_pc_def] )

val tac2 = (
    rw[LET_THM] >>
    match_mp_tac bc_eval1_SOME >>
    Q.PAT_ABBREV_TAC`f = replace_lab X` >>
    qspecl_then[`f`,`s1`] mp_tac bc_fetch_MAP >>
    qunabbrev_tac`f` >>
    Cases_on `l` >> rw[il_replace_lab] >>
    srw_tac[DNF_ss][bc_eval1_def,LET_THM] >>
    fs[bc_eval_stack_thm,bc_find_loc_def] >>
    fs[FLOOKUP_DEF] >>
    rw[bump_pc_with_stack] >>
    rw[bump_pc_def] >>
    fs[good_il_def] >>
    metis_tac[optionTheory.SOME_11,optionTheory.NOT_SOME_NONE])

val bc_next_MAP_replace_lab = store_thm("bc_next_MAP_replace_lab",
  ``∀s1 s2. bc_next s1 s2 ⇒
      ∀m. good_il s1.inst_length ∧
      (∀l. FLOOKUP m l = bc_find_loc s1 (Lab l)) ⇒
    let c = MAP (replace_lab m) s1.code in
    bc_next (s1 with <| code := c |>) (s2 with <| code := c |>)``,
  ho_match_mp_tac bc_next_ind >>
  strip_tac >- tac >>
  strip_tac >- tac2 >>
  strip_tac >- tac2 >>
  strip_tac >- tac2 >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac2 >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac >>
  strip_tac >- tac )

val labels_only_def = Define`
  (labels_only (Jump (Addr _)) = F) ∧
  (labels_only (JumpIf (Addr _)) = F) ∧
  (labels_only (Call (Addr _)) = F) ∧
  (labels_only (PushPtr (Addr _)) = F) ∧
  (labels_only _ = T)`
val _ = export_rewrites["labels_only_def"]

val addrs_only_def = Define`
  (addrs_only (Jump (Lab _)) = F) ∧
  (addrs_only (JumpIf (Lab _)) = F) ∧
  (addrs_only (Call (Lab _)) = F) ∧
  (addrs_only (PushPtr (Lab _)) = F) ∧
  (addrs_only _ = T)`
val _ = export_rewrites["addrs_only_def"]

val bc_fetch_aux_FILTER_labels = store_thm("bc_fetch_aux_FILTER_labels",
  ``∀il ls n. bc_fetch_aux (FILTER ($~ o is_Label) ls) il n = bc_fetch_aux ls il n``,
  gen_tac >> Induct >> rw[])
val _ = export_rewrites["bc_fetch_aux_FILTER_labels"]

val bc_fetch_FILTER_labels = store_thm("bc_fetch_FILTER_labels",
  ``bc_fetch (s with code := FILTER ($~ o is_Label) s.code) = bc_fetch s``,
  rw[bc_fetch_def])
val _ = export_rewrites["bc_fetch_FILTER_labels"]

val bc_fetch_MEM = store_thm("bc_fetch_MEM",
  ``(bc_fetch s1 = SOME i) ⇒ (MEM i s1.code)``,
  rw[bc_fetch_def] >>
  fs[bc_fetch_aux_el_of_addr] >>
  rw[MEM_EL] >>
  imp_res_tac el_of_addr_LESS_LENGTH >>
  metis_tac[])

val bc_next_FILTER_labels = store_thm("bc_next_FILTER",
  ``∀s1 s2. bc_next s1 s2 ⇒ EVERY addrs_only s1.code ⇒
      let c = FILTER ($~ o is_Label) s1.code in
      bc_next (s1 with <| code := c |>) (s2 with <| code := c |>)``,
  ho_match_mp_tac bc_next_ind >>
  rw[LET_THM] >>
  rw[bc_eval1_thm] >>
  srw_tac[DNF_ss][bc_eval1_def,LET_THM] >>
  fs[bc_eval_stack_thm] >>
  rw[bump_pc_def] >>
  imp_res_tac bc_fetch_MEM >>
  fs[EVERY_MEM] >>
  res_tac >>
  Cases_on `l` >> fs[bc_find_loc_def] >>
  rw[bc_fetch_with_stack])

val addrs_only_replace_lab = store_thm("addrs_only_replace_lab",
  ``addrs_only (replace_lab m x)``,
  Cases_on `x` >> rw[] >> Cases_on `l` >> rw[])
val _ = export_rewrites["addrs_only_replace_lab"]

val bc_find_loc_aux_NONE = store_thm("bc_find_loc_aux_NONE",
  ``∀il l ls n. (bc_find_loc_aux ls il l n = NONE) ⇒ ¬MEM (Label l) ls``,
  ntac 2 gen_tac >>
  Induct >> rw[bc_find_loc_aux_def] >>
  res_tac >> fs[])

val bc_find_loc_aux_MEM = store_thm("bc_find_loc_aux_MEM",
  ``∀il l ls n. (bc_find_loc_aux ls il l n ≠ NONE) ⇒ MEM (Label l) ls``,
  ntac 2 gen_tac >>
  Induct >> rw[bc_find_loc_aux_def] >>
  res_tac)

(* TODO: move *)
val ALL_DISTINCT_MAP_INJ = store_thm("ALL_DISTINCT_MAP_INJ",
  ``!ls f. (!x y. MEM x ls /\ MEM y ls /\ (f x = f y) ==> (x = y)) /\ ALL_DISTINCT ls  ==> ALL_DISTINCT (MAP f ls)``,
  Induct THEN SRW_TAC[][MEM_MAP] THEN PROVE_TAC[])

val bc_next_compile_labels = store_thm("bc_next_compile_labels",
  ``∀s1 s2. bc_next s1 s2 ⇒
      (good_il s1.inst_length ∧
       ALL_DISTINCT (FILTER is_Label s1.code)) ⇒
      let c = compile_labels s1.inst_length s1.code in
      bc_next (s1 with <| code := c |>) (s2 with <| code := c |>)``,
  rw[compile_labels_def,replace_labels_thm] >>
  imp_res_tac calculate_labels_thm >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qunabbrev_tac`c` >>
  rw[MAP_REVERSE] >>
  `∀x. ($~ o is_Label) (replace_lab m x) = ($~ o is_Label) x` by rw[] >>
  rw[MAP_FILTER] >>
  qmatch_abbrev_tac `bc_next (s1 with code := FILTER P ls) (s2 with code := FILTER P ls)` >>
  `EVERY addrs_only ls` by (
    qunabbrev_tac`ls` >>
    rw[EVERY_MAP] ) >>
  `bc_next (s1 with code := ls) (s2 with code := ls)` by (
    qunabbrev_tac`ls` >>
    match_mp_tac (MP_CANON(SIMP_RULE(srw_ss())[LET_THM]bc_next_MAP_replace_lab)) >>
    rw[bc_find_loc_def] >>
    fs[LET_THM] >>
    qmatch_abbrev_tac `FLOOKUP (fm |++ ls) l = X` >>
    Cases_on `X` >- (
      `ALOOKUP (REVERSE ls) l = NONE` by (
        qunabbrev_tac`ls` >>
        rw[ALOOKUP_FAILS,ZIP_MAP] >>
        rw[MAP_MAP_o,combinTheory.o_DEF] >>
        `¬MEM (Label l) s1.code` by metis_tac[bc_find_loc_aux_NONE] >>
        `¬MEM (Label l) (FILTER is_Label s1.code)` by rw[MEM_FILTER] >>
        rw[MEM_MAP] >>
        Cases_on `x` >> rw[MEM_FILTER] >>
        PROVE_TAC[] ) >>
      imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_NONE >>
      fs[Abbr`fm`] ) >>
    `ALOOKUP (REVERSE ls) l = SOME x` by (
      match_mp_tac ALOOKUP_ALL_DISTINCT_MEM >>
      qunabbrev_tac`ls` >>
      rw[REVERSE_ZIP,MAP_ZIP,ALL_DISTINCT_REVERSE] >- (
        match_mp_tac ALL_DISTINCT_MAP_INJ >> fs[] >>
        qx_gen_tac `a` >> qx_gen_tac `b` >>
        Cases_on `a` >> Cases_on `b` >> rw[MEM_FILTER] ) >>
      `MEM (Label l) s1.code` by
        metis_tac[bc_find_loc_aux_MEM,optionTheory.NOT_SOME_NONE] >>
      `MEM (Label l) (FILTER is_Label s1.code)` by rw[MEM_FILTER] >>
      pop_assum (strip_assume_tac o SIMP_RULE (srw_ss()) [MEM_EL]) >>
      rw[MEM_ZIP] >>
      qexists_tac `n` >>
      pop_assum (assume_tac o SYM) >>
      rw[EL_MAP] ) >>
    imp_res_tac FLOOKUP_FUPDATE_LIST_ALOOKUP_SOME >>
    fs[] ) >>
  qunabbrev_tac`P` >>
  `ls = (s1 with code := ls).code` by rw[] >>
  pop_assum SUBST1_TAC >>
  (bc_next_FILTER_labels
   |> SIMP_RULE std_ss [LET_THM]
   |> Q.SPECL[`s1 with code := ls`,`s2 with code := ls`]
   |> SIMP_RULE (srw_ss()) []
   |> MP_CANON |> match_mp_tac ) >>
  fs[])

val bc_fetch_next_addr = store_thm("bc_fetch_next_addr",
  ``∀bc0 bs x bc.
    (bs.code = bc0 ++ (x::bc)) ∧ (¬is_Label x) ∧
    (bs.pc = next_addr bs.inst_length bc0)
    ⇒
    (bc_fetch bs = SOME x)``,
  Induct >- rw[bc_fetch_def] >>
  rw[bc_fetch_def] >>
  fsrw_tac[ARITH_ss][bc_fetch_def,ADD1] >>
  first_x_assum (qspec_then `bs with <| code := TL bs.code ; pc := next_addr bs.inst_length bc0 |>` mp_tac) >>
  rw[])

val compile_varref_thm = store_thm("compile_varref_thm",
  ``∀bs bc0 bc0c bc1 cs b bv.
      (bc0c = bc0 ++ REVERSE (compile_varref cs b).out) ∧
      (bs.code = bc0c ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length (bc0 ++ REVERSE cs.out)) ∧
      (lookup_ct cs.sz bs.stack bs.refs b = SOME bv)
      ⇒
      bc_next^* bs (bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length bc0c |>)``,
  ntac 5 gen_tac >> Cases >>
  rw[bc_finish_def] >>
  qmatch_assum_abbrev_tac `bs.code = ls0 ++ (x::ls1) ++ bc1` >>
  `bc_fetch bs = SOME x` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac [`ls0`,`ls1++bc1`] >>
    rw[Abbr`x`] ) >>
  TRY (
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    `(bc_eval1 bs = SOME bs')` by (
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,SUM_APPEND,FILTER_APPEND,ADD1,Abbr`ls1`,Abbr`bs'`] ) >>
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    metis_tac[bc_eval1_thm,RTC_CASES1] )
  >- (
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC (SUC ZERO)` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    rw[bc_eval_stack_def] >>
    qunabbrev_tac`ls1` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y] ++ bc1` >>
    qmatch_abbrev_tac `bc_eval1 bs0 = SOME bs'` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`bc1`] >>
      unabbrev_all_tac >> rw[bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
    rw[bc_eval1_def,Abbr`y`] >>
    rw[bc_eval_stack_def,Abbr`bs0`,Abbr`bs'`] >>
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1] )
  >- (
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    qpat_assum `X = SOME bv` mp_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[DNF_ss][RTC_eq_NRC] >>
    qexists_tac `SUC (SUC (SUC ZERO))` >> rw[NRC] >>
    srw_tac[DNF_ss][ALT_ZERO] >>
    rw[bc_eval1_thm] >>
    rw[Once bc_eval1_def,Abbr`x`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def] >>
    Q.PAT_ABBREV_TAC `bs0 = bump_pc bs with stack := st` >>
    qunabbrev_tac`ls1` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z] ++ bc1` >>
    `bc_fetch bs0 = SOME y` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x]`,`z::bc1`] >>
      rw[Abbr`bs0`,Abbr`y`,bump_pc_def] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`x`] ) >>
    rw[Once bc_eval1_def,Abbr`y`] >>
    srw_tac[DNF_ss][] >>
    rw[bc_eval_stack_def,Abbr`bs0`] >>
    Q.PAT_ABBREV_TAC`bs0 = bump_pc X with stack := Y` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x;y;z] ++ bc1` >>
    `bc_fetch bs0 = SOME z` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0++[x;y]`,`bc1`] >>
      rw[Abbr`bs0`,bump_pc_def,Abbr`z`] >>
      srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,Abbr`y`,Abbr`x`] ) >>
    rw[bc_eval1_def,Abbr`bs0`,bump_pc_def,Abbr`z`] >>
    fs[FLOOKUP_DEF] >>
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1] ))

val no_closures_Cv_bv_equal = store_thm("no_closures_Cv_bv_equal",
  ``∀pp cv bv. Cv_bv pp cv bv ⇒
      ∀cv' bv'. Cv_bv pp cv' bv' ∧ no_closures cv ∧ no_closures cv' ⇒ ((cv = cv') = (bv = bv'))``,
  gen_tac >> ho_match_mp_tac Cv_bv_ind >> rw[]
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    fs[Once Cv_bv_cases] )
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    Cases_on `b` >>
    fsrw_tac[ARITH_ss][Once Cv_bv_cases] >>
    Cases_on `b` >> fs[]) >>
  rw[EQ_IMP_THM] >- (
    fs[Once (Q.SPECL[`pp`,`CConv cn vs`]Cv_bv_cases)] >>
    rw[LIST_EQ_REWRITE] >>
    fs[EVERY2_EVERY] >>
    qpat_assum`LENGTH X = LENGTH bvs` assume_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    qpat_assum`LENGTH vs = X` assume_tac >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    metis_tac[EL_ZIP] ) >>
  qpat_assum`Cv_bv X Y Z` mp_tac >>
  rw[Once Cv_bv_cases] >>
  fsrw_tac[ARITH_ss][] >>
  TRY (Cases_on `b` >> fsrw_tac[ARITH_ss][]) >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt (qpat_assum `LENGTH X = Y` mp_tac) >> rpt strip_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP] >>
  rw[LIST_EQ_REWRITE] >> fsrw_tac[DNF_ss][MEM_EL] >>
  metis_tac[])

val prim2_to_bc_thm = store_thm("prim2_to_bc_thm",
  ``∀op v1 v2 v bs bc0 bc1 st bv1 bv2 pp.
    (bs.code = bc0 ++ [Stack (prim2_to_bc op)] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (CevalPrim2 op v1 v2 = Rval v) ∧
    Cv_bv pp v1 bv1 ∧ Cv_bv pp v2 bv2 ∧
    (bs.stack = bv2::bv1::st)
    ⇒ ∃bv.
      Cv_bv pp v bv ∧
      bc_next bs (bump_pc (bs with <|stack := bv::st|>))``,
  rw[] >>
  `bc_fetch bs = SOME (Stack (prim2_to_bc op))` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac[`bc0`,`bc1`] >>
    rw[] ) >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  srw_tac[DNF_ss][] >>
  rw[bump_pc_with_stack] >>
  Cases_on `op` >>
  Cases_on `v1` >> TRY (Cases_on `l`) >>
  Cases_on `v2` >> TRY (Cases_on `l`) >>
  fs[] >> rw[] >> fs[Once Cv_bv_cases] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[bc_eval_stack_def] >> fs[i0_def] >>
  TRY (Cases_on `b` >> rw[]) >>
  TRY (Cases_on `b'` >> rw[]) >>
  srw_tac[ARITH_ss][] >>
  fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  Cases_on `m=m'` >> rw[] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  rw[LIST_EQ_REWRITE] >>
  rfs[MEM_ZIP] >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  Cases_on `LENGTH bvs = LENGTH bvs'` >> rw[] >>
  metis_tac[no_closures_Cv_bv_equal] )

val compile_varref_append_out = store_thm("compile_varref_append_out",
  ``∀cs b. ∃bc. (compile_varref cs b).out = bc ++ cs.out``,
  ho_match_mp_tac compile_varref_ind >> rw[])

(* TODO: move *)
val compile_decl_def = CompileTheory.compile_decl_def

val compile_decl_append_out = store_thm("compile_decl_append_out",
  ``∀env0 a vs. ∃bc. (FST (compile_decl env0 a vs)).out = bc ++ (FST a).out``,
  rw[compile_decl_def] >>
  qho_match_abbrev_tac `∃bc. (FST (FOLDL f a vs)).out = bc ++ (FST a).out` >>
  qsuff_tac `(λx. ∃bc. (FST x).out = bc ++ (FST a).out) (FOLDL f a vs)` >- rw[] >>
  match_mp_tac FOLDL_invariant >> rw[] >>
  PairCases_on `x` >> fs[] >>
  rw[Abbr`f`] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[] >>
  metis_tac[compile_varref_append_out,APPEND_ASSOC,CONS_APPEND])

val compile_closures_append_out = store_thm("compile_closures_append_out",
  ``∀nz s defs. ∃bc. (compile_closures nz s defs).out = bc ++ s.out``,
  rw[compile_closures_def,LET_THM] >>
  cheat (* need to split this into separate functions *))

val compile_append_out = store_thm("compile_append_out",
  ``(∀cs exp. ∃bc. (compile cs exp).out = bc ++ cs.out) ∧
    (∀env0 sz1 exp n cs xs. ∃bc. (compile_bindings env0 sz1 exp n cs xs).out = bc ++ cs.out)``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >- rw[] >>
    Q.PAT_ABBREV_TAC`p = compile_decl X Y Z` >>
    PairCases_on `p` >> rw[] >>
    metis_tac[compile_decl_append_out,pairTheory.FST,APPEND_ASSOC,CONS_APPEND]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def,compile_varref_append_out] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    qmatch_abbrev_tac `∃bc. x::(FOLDL compile a es).out = bc ++ cs.out` >>
    qsuff_tac `∃bc. (FOLDL compile a es).out = bc ++ cs.out` >- (
      rw[] >> qexists_tac `[x] ++ bc` >> rw[] ) >>
    Q.ISPECL_THEN[`λx. ∃bc. x.out = bc ++ cs.out`,`compile`,`es`,`a`]mp_tac FOLDL_invariant >>
    rw[Abbr`a`] >> pop_assum match_mp_tac >>
    srw_tac[DNF_ss][] >>
    metis_tac[APPEND_ASSOC] ) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    qmatch_abbrev_tac `∃bc. xx++(FOLDL compile a es).out = bc ++ cs.out` >>
    qsuff_tac `∃b0. (FOLDL compile a es).out = b0 ++ cs.out` >- (
      rw[] >> qexists_tac `xx ++ b0` >> rw[] ) >>
    Q.ISPECL_THEN[`λx. ∃bc. x.out = bc ++ cs.out`,`compile`,`es`,`a`]mp_tac FOLDL_invariant >>
    rw[Abbr`a`] >> pop_assum match_mp_tac >>
    srw_tac[DNF_ss][] >>
    metis_tac[APPEND_ASSOC] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    rw[] >>
    metis_tac[compile_closures_append_out,APPEND_ASSOC] ) >>
  strip_tac >- rw[compile_def,compile_closures_append_out] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    BasicProvers.EVERY_CASE_TAC >>
    cheat (* more FOLDL_invariant *)) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    metis_tac[APPEND_ASSOC,CONS_APPEND] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    metis_tac[APPEND_ASSOC,CONS_APPEND] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    metis_tac[APPEND_ASSOC,CONS_APPEND] ) >>
  rw[compile_def] )

val FOLDL_compile_append_out = store_thm("FOLDL_compile_append_out",
  ``∃bc. (FOLDL compile cs exps).out = bc ++ cs.out``,
  Q.ISPECL_THEN[`λx. ∃bc. x.out = bc ++ cs.out`,`compile`,`exps`,`cs`]mp_tac FOLDL_invariant >>
  rw[] >> pop_assum match_mp_tac >>
  rw[] >>
  metis_tac[compile_append_out,APPEND_ASSOC])

val compile_varref_env_sz = store_thm("compile_varref_env_sz",
  ``∀cs b. ((compile_varref cs b).env = cs.env) ∧
           ((compile_varref cs b).sz = cs.sz)``,
  ho_match_mp_tac compile_varref_ind >> rw[])
val _ = export_rewrites["compile_varref_env_sz"]

val compile_decl_env = store_thm("compile_decl_env",
  ``∀env0 a vs. (FST (compile_decl env0 a vs)).env = (FST a).env``,
  rpt gen_tac >>
  simp[compile_decl_def] >>
  qmatch_abbrev_tac `((FST (FOLDL f a vs)).env = (FST a).env)` >>
  `(λx. (FST x).env = (FST a).env) (FOLDL f a vs)` by (
    match_mp_tac FOLDL_invariant >>
    rw[] >> rw[Abbr`f`] >>
    PairCases_on `x` >> fs[] >>
    rw[] >>
    BasicProvers.EVERY_CASE_TAC >>
    rw[] ) >>
  fs[])
val _ = export_rewrites["compile_decl_env"]

val compile_decl_sz = store_thm("compile_decl_sz",
  ``∀env0 a vs. set vs ⊆ FDOM env0 ⇒ ((FST (compile_decl env0 a vs)).sz = (FST a).sz)``,
  rpt gen_tac >>
  strip_tac >>
  simp[compile_decl_def] >>
  qmatch_abbrev_tac `((FST (FOLDL f a vs)).sz = (FST a).sz)` >>
  `(λx. (FST x).sz = (FST a).sz) (FOLDL f a vs)` by (
    match_mp_tac FOLDL_invariant >>
    rw[] >> rw[Abbr`f`] >>
    PairCases_on `x` >> fs[] >>
    rw[] >>
    BasicProvers.EVERY_CASE_TAC >>
    rw[] >> fs[SUBSET_DEF] >> metis_tac[]) >>
  fs[])

val lookup_ct_incsz = store_thm("lookup_ct_incsz",
  ``(lookup_ct (sz+1) (x::st) refs b =
     if (b = CTLet (sz+1)) then SOME x else
     lookup_ct sz st refs b)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  rw[SUB,GSYM ADD_SUC])

val lookup_ct_imp_incsz = store_thm("lookup_ct_imp_incsz",
  ``(lookup_ct sz st refs b = SOME v) ⇒
    (lookup_ct (sz+1) (x::st) refs b = SOME v)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  rw[SUB,GSYM ADD_SUC])

val Cenv_bs_imp_incsz = store_thm("Cenv_bs_imp_incsz",
  ``Cenv_bs c env renv rsz bs ∧ (∃s p e. bs' = bs with <| stack := s::bs.stack; pc := p; exstack := e |>) ⇒
    Cenv_bs c env renv (rsz+1) bs'``,
  rw[Cenv_bs_def,fmap_rel_def] >>
  qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
  first_x_assum (qspec_then `z` mp_tac) >>
  BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  rw[] )

val bc_state_component_equality = DB.fetch"Bytecode""bc_state_component_equality"

val compile_val = store_thm("compile_val",
  ``(∀c env exp res. Cevaluate c env exp res ⇒
      ∀v bc0 bc0c bc1 bs cs.
        Cexp_pred exp ∧
        (res = Rval v) ∧
        (Cenv_bs c env cs.env cs.sz bs) ∧
        (bc0c = bc0 ++ (REVERSE (compile cs exp).out)) ∧
        (bs.code = bc0c ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length (bc0 ++ REVERSE cs.out))
        ⇒
        ∃bv.
          let bs' = bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length bc0c |> in
          bc_next^* bs bs' ∧
          Cv_bv (mk_pp c bs) v bv ∧
          ((compile cs exp).env = cs.env) ∧
          ((compile cs exp).sz = cs.sz + 1) ∧
          Cenv_bs c env (compile cs exp).env (compile cs exp).sz bs') ∧
    (∀c env exps ress. Cevaluate_list c env exps ress ⇒
      ∀vs bc0 bc0c bc1 bs cs.
        EVERY Cexp_pred exps ∧
        (ress = Rval vs) ∧
        (Cenv_bs c env cs.env cs.sz bs) ∧
        (bc0c = bc0 ++ (REVERSE (FOLDL compile cs exps).out)) ∧
        (bs.code = bc0c ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length (bc0 ++ REVERSE cs.out))
        ⇒
        ∃bvs.
          let bs' = bs with <| stack := (REVERSE bvs)++bs.stack ; pc := next_addr bs.inst_length bc0c |> in
          bc_next^* bs bs' ∧
          EVERY2 (Cv_bv (mk_pp c bs)) vs bvs ∧
          ((FOLDL compile cs exps).env = cs.env) ∧
          ((FOLDL compile cs exps).sz = cs.sz + LENGTH exps) ∧
          Cenv_bs c env (FOLDL compile cs exps).env (FOLDL compile cs exps).sz bs')``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,bc_finish_def,Cenv_bs_def,fmap_rel_def] >>
    qmatch_assum_rename_tac `n ∈ FDOM env`[] >>
    first_assum (qspec_then `n` mp_tac) >>
    BasicProvers.EVERY_CASE_TAC >>
    strip_tac >>
    qmatch_assum_rename_tac `Cv_bv pp (env ' n) x`["pp"] >>
    qexists_tac `x` >> rw[] >- (
      imp_res_tac compile_varref_thm >>
      pop_assum mp_tac >> rw[] ) >>
    unabbrev_all_tac >> rw[] >>
    qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
    qmatch_abbrev_tac`X` >>
    first_assum (qspec_then `z` mp_tac) >>
    BasicProvers.CASE_TAC >>
    qunabbrev_tac`X` >>
    imp_res_tac lookup_ct_imp_incsz >>
    rw[]) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    Cases >> rw[compile_def,LET_THM] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x] ++ bc1` >>
    `bc_fetch bs = SOME x` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0`,`bc1`] >>
      rw[Abbr`x`] ) >> (
    reverse (rw[Once Cv_bv_cases]) >- (
      match_mp_tac Cenv_bs_imp_incsz >>
      rw[bc_state_component_equality] )) >>
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC 0` >>
    rw[NRC] >>
    rw[bc_eval1_thm] >>
    rw[bc_eval1_def,Abbr`x`] >>
    rw[bc_eval_stack_def] >>
    srw_tac[ARITH_ss][bump_pc_def,Abbr`ls0`,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    srw_tac[DNF_ss][Once Cv_bv_cases] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x] ++ bc1` >>
    first_x_assum (qspecl_then [`bc0`,`[x] ++ bc1`,`bs`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bvs` strip_assume_tac) >>
    qexists_tac `bvs` >>
    reverse (rw[]) >- (
      rfs[] >>
      imp_res_tac Cenv_bs_imp_incsz >>
      first_x_assum match_mp_tac >>
      rw[bc_state_component_equality] ) >>
    rw[Once RTC_CASES2] >> disj2_tac >>
    qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
    qexists_tac `bs0` >> rw[] >>
    `bc_fetch bs0 = SOME x` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0`,`bc1`] >>
      unabbrev_all_tac >> rw[] ) >>
    rw[bc_eval1_thm] >>
    rw[bc_eval1_def,Abbr`x`] >>
    fs[EVERY2_EVERY,Cevaluate_list_with_Cevaluate,Cevaluate_list_with_EVERY] >>
    srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs0`] >>
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1,bump_pc_def] >>
    rw[bc_state_component_equality] >>
    metis_tac[TAKE_LENGTH_APPEND,REVERSE_REVERSE
             ,DROP_LENGTH_APPEND,LENGTH_REVERSE]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[DNF_ss][Once Cv_bv_cases] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x] ++ bc1` >>
    first_x_assum (qspecl_then [`bc0`,`[x] ++ bc1`,`bs`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bv` strip_assume_tac) >>
    rfs[] >>
    conj_tac >- (
      rw[Once RTC_CASES2] >> disj2_tac >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qexists_tac `bs0` >> rw[] >>
      `bc_fetch bs0 = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        map_every qexists_tac [`ls0`,`bc1`] >>
        unabbrev_all_tac >> rw[] ) >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      fs[Once Cv_bv_cases] >>
      rw[bc_eval_stack_def,Abbr`bs0`] >>
      unabbrev_all_tac >>
      srw_tac[ARITH_ss][bump_pc_def,SUM_APPEND,FILTER_APPEND,ADD1] >>
      rw[bc_state_component_equality] >>
      AP_TERM_TAC >> rw[EQ_IMP_THM] ) >>
    imp_res_tac Cenv_bs_imp_incsz >>
    first_x_assum match_mp_tac >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x] ++ bc1` >>
    first_x_assum (qspecl_then [`bc0`,`[x] ++ bc1`,`bs`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bv` strip_assume_tac) >>
    fs[Once (Q.SPECL[`pp`,`CConv m vs`]Cv_bv_cases)] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qexists_tac `EL n bvs` >>
    rev_full_simp_tac(srw_ss()++DNF_ss)[MEM_ZIP] >>
    conj_tac >- (
      rw[Once RTC_CASES2] >> disj2_tac >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qexists_tac `bs0` >> rw[] >>
      `bc_fetch bs0 = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        map_every qexists_tac [`ls0`,`bc1`] >>
        unabbrev_all_tac >> rw[] ) >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bc_eval_stack_def,Abbr`bs0`] >>
      unabbrev_all_tac >>
      srw_tac[ARITH_ss][bump_pc_def,SUM_APPEND,FILTER_APPEND,ADD1] ) >>
    imp_res_tac Cenv_bs_imp_incsz >>
    first_x_assum match_mp_tac >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x] ++ bc1` >>
    first_x_assum (qspecl_then [`bc0`,`[x] ++ bc1`,`bs`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bvs` strip_assume_tac) >>
    fs[EVERY2_EVERY] >>
    `∃bv0 bv1. bvs = [bv0;bv1]` by (
      Cases_on `bvs` >> fs[] >>
      Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
    srw_tac[ARITH_ss][] >>
    qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
    qmatch_assum_abbrev_tac `Cv_bv pp v1 bv0` >>
    qspecl_then[`p2`,`v1`,`v2`,`v`,`bs0`,`ls0`,`bc1`,`bs.stack`,`bv0`,`bv1`,`pp`]mp_tac prim2_to_bc_thm >>
    fs[Abbr`bs0`] >>
    disch_then (Q.X_CHOOSE_THEN`bv`strip_assume_tac) >>
    qexists_tac `bv` >> fs[] >>
    conj_tac >- (
      rw[Once RTC_CASES2] >> disj2_tac >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qexists_tac `bs0` >> rw[] >>
      qmatch_assum_abbrev_tac `bc_next bs0 bs1` >>
      qmatch_abbrev_tac `bc_next bs0 bs11` >>
      qsuff_tac `bs1 = bs11` >- metis_tac[bc_eval1_thm,optionTheory.SOME_11] >>
      rw[Abbr`bs1`,Abbr`bs11`] >>
      qmatch_abbrev_tac `bump_pc bs2 = bs1` >>
      `bc_fetch bs2 = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        map_every qexists_tac [`ls0`,`bc1`] >>
        unabbrev_all_tac >> rw[] ) >>
      rw[bump_pc_def] >>
      unabbrev_all_tac >>
      srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] ) >>
    imp_res_tac Cenv_bs_imp_incsz >>
    first_x_assum match_mp_tac >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >>
    rpt strip_tac >>
    rw[] >> fs[] >>
    fs[compile_def,LET_THM] >>
    SIMPLE_QUANT_ABBREV_TAC [select_fun_constant ``compile`` 1 "cs0"] >>
    SIMPLE_QUANT_ABBREV_TAC [select_fun_constant ``compile`` 1 "cs1"] >>
    SIMPLE_QUANT_ABBREV_TAC [select_fun_constant ``compile`` 1 "cs2"] >>
    qabbrev_tac`nl = (compile cs0 exp).next_label` >>
    `∃bce1 bce2 bce3. ((compile cs0 exp).out = bce1 ++ cs0.out) ∧
                      ((compile cs1 e2).out = bce2 ++ bce1 ++ cs0.out) ∧
                      ((compile cs2 e3).out = bce3 ++ bce2 ++ bce1 ++ cs0.out)` by (
      qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
      qspecl_then[`cs1`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
      qspecl_then[`cs2`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
      disch_then(Q.X_CHOOSE_THEN`bce2`strip_assume_tac) >>
      disch_then(Q.X_CHOOSE_THEN`bce1`strip_assume_tac) >>
      disch_then(Q.X_CHOOSE_THEN`bce0`strip_assume_tac) >>
      fs[Abbr`cs1`,Abbr`cs2`] ) >>
    qpat_assum `∀bc0. P` mp_tac >>
    fs[] >>
    first_x_assum (qspecl_then [`bc0`,`REVERSE bce2 ++ REVERSE bce3 ++ [Label (nl+2)] ++ bc1`,`bs`,`cs0`] mp_tac) >>
    `(cs0.env = cs.env) ∧ (cs0.sz = cs.sz) ∧ (cs0.out = cs.out)` by rw[Abbr`cs0`] >>
    fs[] >>
    simp[Once Cv_bv_cases] >>
    strip_tac >>
    strip_tac >>
    qmatch_assum_abbrev_tac `bc_next^* bs bs1` >>
    Cases_on `b1` >> fs[] >- (
      this is wrong - cs1 has size decremented preemptively
      first_x_assum (qspecl_then [`bc0++REVERSE cs.out++REVERSE bce1`,`REVERSE bce3++[Label (nl+2)]++bc1`,`bs1`,`cs1`] mp_tac) >>
      fs[] >>
      `Cenv_bs c env cs1.env cs1.sz bs1` by (
        rw[Abbr`bs1`,Abbr`cs1`]

    set_trace"goalstack print goal at top"0

    ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[EVERY2_EVERY] >>
    rw[LENGTH_NIL_SYM] >>
    rw[RTC_eq_NRC] >>
    qexists_tac`0` >>rw[] >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- (
    rw[] >>
    qabbrev_tac `bs0 = bs with pc := next_addr bs.inst_length (bc0 ++ REVERSE (compile cs exp).out)`
    first_x_assum (qspecl_then [`bc0`,`bc1`,`bs0`,`compile cs exp`] mp_tac)
    set_trace"goalstack print goal at top"0
    `∃bc2. (FOLDL compile (compile cs exp) exps).out = bc2 ++ (compile cs exp).out` by (
      metis_tac[FOLDL_compile_append_out] ) >>
    fs[REVERSE_APPEND]

    cheat ) >>
  strip_tac >- rw[] >>
  rw[] )

val repl_exp_val = store_thm("repl_exp_val",
  ``∀cenv env exp v rs rs' bc0 bc bc1 bs bs'.
      exp_pred exp ∧
      evaluate cenv env exp (Rval v) ∧
      EVERY closed (MAP SND env) ∧
      FV exp ⊆ set (MAP FST env) ∧
      good_cenv cenv ∧
      good_cmap cenv (cmap rs.contab) ∧
      env_rs env bs rs ∧
      (repl_exp rs exp = (rs',bc)) ∧
      (bs.code = bc0 ++ bc ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0)
      ⇒
      ∃bv.
      bc_next^* bs (bs with <|pc := next_addr bs.inst_length (bc0 ++ bc);
                              stack := bv :: bs.stack|>) ∧
      (v_to_ov v = bv_to_ov (FST(SND(rs.contab))) bv)``,
  rw[repl_exp_def,compile_Cexp_def,LET_THM] >>
  qabbrev_tac `p = repeat_label_closures (exp_to_Cexp (cmap rs.contab) exp) rs.rnext_label []` >>
  PairCases_on `p` >> fs[] >>
  reverse BasicProvers.EVERY_CASE_TAC >- (
    qmatch_assum_abbrev_tac `(compile ss ee).decl = SOME (q,r)` >>
    `ss.decl ≠ NONE` by (
      PROVE_TAC[compile_decl_NONE,optionTheory.NOT_SOME_NONE] ) >>
    fs[Abbr`ss`] ) >>
  qspecl_then[`cenv`,`env`,`exp`,`Rval v`] mp_tac exp_to_Cexp_thm1 >> fs[] >>
  disch_then (qspec_then `cmap rs.contab` mp_tac) >> fsrw_tac[DNF_ss][] >>
  qx_gen_tac `Cv` >> rw[] >>
  qabbrev_tac `Ce = exp_to_Cexp (cmap rs.contab) exp` >>
  `Cexp_pred Ce` by PROVE_TAC[exp_pred_Cexp_pred] >>
  `(p0,p1,p2) = (Ce,rs.rnext_label,[])` by PROVE_TAC[Cexp_pred_repeat_label_closures] >>
  fs[] >> rw[] >>
  `calculate_ldefs FEMPTY [] Ce = []` by PROVE_TAC[Cexp_pred_calculate_ldefs] >>
  fs[] >>
  fs[calculate_ecs_def] >>
  fs[compile_code_env_def,LET_THM] >>
  qmatch_assum_abbrev_tac `Cevaluate Cc Cenv Ce (Rval Cv)` >>
  Q.PAT_ABBREV_TAC`cs = compiler_state_env_fupd X Y` >>

  qho_match_abbrev_tac `∃bv. bc_next^* bs0 (bs1 bv) ∧ P bv` >>
  (* deal with code env here *)
  qspecl_then[`Cc`,`Cenv`,`Ce`,`Rval Cv`]mp_tac (CONJUNCT1 compile_val) >>
  fs[] >>
  disch_then (qspecl_then [`bs.code`,`[]`,`bs0`,`cs`] mp_tac) >>
  rw[Abbr`bs0`]

val with_same_pc = store_thm("with_same_pc",
  ``x with pc := x.pc = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_pc"]

(*
val bc_next_fetch_only = store_thm("bc_next_fetch_only",
  ``∀r1 r2. bc_next r1 r2 ⇒
      ∀tr s1. (∀pc. bc_fetch (r1 with pc := pc) = OPTION_BIND (tr pc) (λpc. bc_fetch (s1 with pc := pc))) ∧
              (tr r1.pc = SOME s1.pc) ∧
              (s1.stack = r1.stack)
        ⇒ ∃pc. (tr r2.pc = SOME pc) ∧ bc_next s1 (r2 with pc := pc)``,
  ho_match_mp_tac bc_next_ind >>
  rw[] >>
  first_assum (qspec_then `r1.pc` mp_tac) >>
  simp_tac (srw_ss()) [] >>
  asm_simp_tac (srw_ss()) [] >>
  disch_then (assume_tac o SYM) >>
  rw[bc_next_cases] >>

val addr_of_el_bc_fetch_aux = store_thm("addr_of_el_bc_fetch_aux",
  ``∀c il pc n. (bc_fetch_aux c il pc = SOME (EL n c)) ⇒ (addr_of_el il n c = SOME pc)``,
  Induct >> rw[]
  >- PROVE_TAC[bc_fetch_aux_not_label]
  >- (Cases_on `n` >> fs[])

val translate_pc_def = Define`
  translate_pc il1 il2 c pc = OPTION_BIND (el_of_addr il1 pc c) (λn. addr_of_el il2 n c)`

val labels_only_any_il = store_thm("labels_only_any_il",
  ``∀s1 s2. bc_next s1 s2 ⇒ labels_only s1.code ⇒
    ∀il. ∃p1 p2.
      (translate_pc s1.inst_length il s1.code s1.pc = SOME p1) ∧
      (translate_pc s2.inst_length il s2.code s2.pc = SOME p2) ∧
      bc_next (s1 with <| inst_length := il; pc := p1 |>)
              (s2 with <| inst_length := il; pc := p2 |>)``,
  ho_match_mp_tac bc_next_ind >>
  rw[bc_fetch_def] >>
  fs[bc_fetch_aux_el_of_addr,translate_pc_def,bump_pc_def,bc_fetch_def]
  strip_tac
*)

val add_code_def = Define`
  add_code c (s:bc_state) = s with <| code := s.code ++ c |>`

(*
val bc_fetch_aux_any_inst_length = store_thm("bc_fetch_aux_any_inst_length",
 ``∀c il pc il'. bc_fetch_aux c il' pc =
   OPTION_BIND (el_of_addr il' pc c)
   (λn. OPTION_BIND (addr_of_el il n c)
        (λpc. bc_fetch_aux c il pc))``,
 Induct >- rw[] >>
 rw[] >- (
   first_x_assum (qspecl_then [`il'`,`0`] mp_tac) >>
   rw[] >>
    Q.PAT_ABBREV_TAC`opt = el_of_addr il' 0 c` >>
    Cases_on `opt` >> fs[] >>

 rpt gen_tac >>
 simp_tac(srw_ss())[]
 rw[] >> rw[]
 ho_match_mp_tac bc_fetch_aux_ind >>
 strip_tac >- rw[] >>
 strip_tac >- (
   rw[bc_fetch_aux_el_of_addr] >>
   Cases_on `el_of_addr il' pc c` >> fs[] >>
   rw[GSYM arithmeticTheory.ADD1] >>
   Cases_on `addr_of_el il x c` >> fs[] ) >>
 strip_tac >- (
   rw[] >> rw[] >>
   rw[bc_fetch_aux_el_of_addr] >>
   Q.PAT_ABBREV_TAC`opt = el_of_addr il' pcX cX` >>
   Cases_on `opt` >> fs[] >>
   rw[GSYM arithmeticTheory.ADD1] >>
   fsrw_tac[DNF_ss][] >>
   fs[markerTheory.Abbrev_def] >>
   Cases_on `addr_of_el il x c` >> fs[] 

val bc_next_any_inst_length = store_thm("bc_next_any_inst_length",
  ``∀s1 s2. bc_next s1 s2 ⇒ ∀il. bc_next (s1 with <| inst_length := il |>) (s2 with <| inst_length := il |>)``,
  ho_match_mp_tac bc_next_ind >>
  strip_tac >- (
    rw[]

val set_pc_el_def = Define`
  set_pc_el n s = s with <| pc := addr_of_el n s.inst_length s.code |>`

val bc_fetch_aux_addr_of_el = store_thm("bc_fetch_aux_addr_of_el",
  ``∀c n. (∀l. n < LENGTH c ⇒ EL n c ≠ Label l) ⇒
       (bc_fetch_aux c il (addr_of_el n il c) = if n < LENGTH c then SOME (EL n c) else NONE)``,
  Induct >- rw[] >>
  CONV_TAC SWAP_FORALL_CONV >>
  Induct >- (
    fs[addr_of_el_def] >>
    Cases >> rw[] ) >>
  fs[addr_of_el_def] >>
  Cases >> rw[] >>
  fsrw_tac[ARITH_ss][])

val bc_fetch_set_pc_el = store_thm("bc_fetch_set_pc_el",
  ``n < LENGTH s.code ∧ (∀l. EL n s.code ≠ Label l) ⇒
      (bc_fetch (set_pc_el n s) = SOME (EL n s.code))``,
  rw[bc_fetch_def,set_pc_el_def] >>
  metis_tac[bc_fetch_aux_addr_of_el])
*)

(*
val compile_thm1 = store_thm("compile_thm1",
  ``∀env exp res. Cevaluate env exp res ⇒
    ∀v cs cs'.
      (res = Rval v) ∧ (∀s. exp ≠ CDecl s) ∧
      FDOM env ⊆ FDOM cs.env ∧
      (cs' = compile cs exp) ⇒
        ∃c. (cs'.out = c++cs.out) ∧
          ∀b1. (∀x. x ∈ FDOM env ⇒ ∃v. (lookup_ct cs.sz b1.stack b1.refs (cs.env ' x) = SOME v) ∧
                                       bceqv b1.inst_length b1.code (env ' x) v) ⇒
            ∃b2. bc_finish (set_pc_el (LENGTH b1.code) (add_code (REVERSE c) b1)) b2 ∧
                 ∃bv. (b2.stack = bv::b1.stack) ∧
                      bceqv b2.inst_length b2.code v bv``,
  ho_match_mp_tac Cevaluate_nice_ind >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def] >>
    rw[bc_finish_def,arithmeticTheory.RTC_eq_NRC] >>
    Cases_on `cs.env ' n` >>
    rw[compile_varref_def] >>
    fsrw_tac[DNF_ss][] >- (
      CONV_TAC (RESORT_EXISTS_CONV rev) >>
      qexists_tac `1` >>
      rw[] >>
      rw[Once bc_next_cases] >>
      srw_tac[ARITH_ss][bc_fetch_set_pc_el,add_code_def,rich_listTheory.EL_LENGTH_APPEND] >>
      qmatch_assum_rename_tac `cs.env ' n = CTLet x`[] >>
      first_x_assum (qspec_then `n` mp_tac) >>
      rw[] >>
      rw[bc_stack_op_cases]
      >- rw[set_pc_el_def]
      >- rw[set_pc_el_def]
      >- (
        
      rw[bump_pc_def]
      rw[addr_of_el_def]
*)

(* values in compile-time environment *)
(* type ctbind = CTLet of num | CTArg of num | CTEnv of num | CTRef of num *)
(* CTLet n means stack[sz - n]
   CTArg n means stack[sz + n]
   CTEnv n means El n of the environment, which is at stack[sz]
   CTRef n means El n of the environment, but it's a ref pointer *)

(*
val Cpat_nice_ind =
TypeBase.induction_of(``:Cpat``)
|> Q.SPECL[`P`,`EVERY P`]
|> SIMP_RULE(srw_ss())[]
|> UNDISCH_ALL
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`P`

let rec
v_to_ov cenv (Lit l) = OLit l
and
v_to_ov cenv (Conv cn vs) = OConv cn (List.map (v_to_ov cenv) vs)
and
v_to_ov cenv (Closure env vn e) = OFn
  (fun ov -> map_option (o (v_to_ov cenv) snd)
    (some (fun (a,r) -> v_to_ov cenv a = ov
           && evaluate cenv (bind vn a env) e (Rval r))))
and
v_to_ov cenv (Recclosure env defs n) = OFn
  (fun ov -> option_bind (optopt (find_recfun n defs))
    (fun (vn,e) -> map_option (o (v_to_ov cenv) snd)
      (some (fun (a,r) -> v_to_ov cenv a = ov
             && evaluate cenv (bind vn a (build_rec_env defs env)) e (Rval r)))))

let rec
Cv_to_ov m (CLit l) = OLit l
and
Cv_to_ov m (CConv cn vs) = OConv (Pmap.find cn m) (List.map (Cv_to_ov m) vs)
and
Cv_to_ov m (CClosure env ns e) = OFn
  (fun ov -> some
and
Cv_to_ov m (CRecClos env ns fns n) = OFn
*)

val _ = export_theory ()
