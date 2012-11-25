open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory rich_listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory arithmeticTheory lcsymtacs quantHeuristicsLib quantHeuristicsLibAbbrev
open MiniMLTerminationTheory miniMLExtraTheory miscTheory compileTerminationTheory intLangTheory bytecodeTerminationTheory evaluateEquationsTheory expToCexpTheory pmatchTheory labelClosuresTheory bytecodeEvalTheory bytecodeExtraTheory
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

val _ = Parse.overload_on("next_addr", ``λil ls. SUM (MAP (SUC o il) (FILTER ($~ o is_Label) ls))``)

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
      qunabbrev_tac`f` >> fs[FORALL_PROD,push_lab_def] >>
      ntac 4 gen_tac >> Cases >> rw[push_lab_def] >>
      unabbrev_all_tac >> rw[] ) >>
    pop_assum mp_tac >> rw[] ) >>
  `s'''.decl = s''.decl` by (
    qmatch_assum_abbrev_tac `FOLDL f a ls = (s''',x)` >>
    `(($= s''.decl) o compiler_state_decl o FST) (FOLDL f a ls)` by (
      match_mp_tac FOLDL_invariant >>
      qunabbrev_tac`a` >> fs[] >>
      qunabbrev_tac`f` >> fs[FORALL_PROD,cons_closure_def] >>
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
      Induct >- rw[Once num_fold_def,Abbr`f`,update_refptr_def] >>
      rw[Once num_fold_def] >>
      rw[Abbr`f`] >>
      Cases_on `a'` >> rw[update_refptr_def,LET_THM] ) >>
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
val prim2_to_bc_def = CompileTheory.prim2_to_bc_def
val _ = export_rewrites["Compile.prim2_to_bc_def"]

val _ = Parse.overload_on("mk_pp", ``λc bs.
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
  env_rs env rs c bs =
    let Cenv = alist_to_fmap (env_to_Cenv (cmap rs.contab) env) in
    Cenv_bs c Cenv rs.renv rs.rsz bs`

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

val labels_only_def = Define`
  (labels_only (Jump (Addr _)) = F) ∧
  (labels_only (JumpIf (Addr _)) = F) ∧
  (labels_only (Call (Addr _)) = F) ∧
  (labels_only (PushPtr (Addr _)) = F) ∧
  (labels_only _ = T)`
val _ = export_rewrites["labels_only_def"]

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
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``num_fold``1"f"] >>
  `∃bc. (num_fold f'' s nz).out = bc ++ s.out` by (
    qid_spec_tac `s` >>
    Induct_on `nz` >> rw[Once num_fold_def] >>
    `∃bc. (f'' s).out = bc ++ s.out` by rw[Abbr`f''`] >>
    metis_tac[APPEND_ASSOC] ) >>
  qabbrev_tac`p = (FOLDL push_lab (num_fold f'' s nz,0,[]) defs)` >>
  `(λx. ∃bc. (FST x).out = bc ++ s.out) p` by (
    qunabbrev_tac`p` >>
    match_mp_tac FOLDL_invariant >>
    fs[] >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    qx_gen_tac`y` >> PairCases_on`y` >>
    Cases_on `y1` >> rw[push_lab_def,LET_THM] >>
    metis_tac[APPEND_ASSOC,CONS_APPEND] ) >>
  PairCases_on `p` >> fs[] >>
  Q.PAT_ABBREV_TAC`q = FOLDL (cons_closure X Y) (p0,1) Z` >>
  `(λx. ∃bc. (FST x).out = bc ++ s.out) q` by(
    qunabbrev_tac`q` >>
    match_mp_tac FOLDL_invariant >>
    fs[] >>
    Cases >> Cases >>
    rw[cons_closure_def,LET_THM] >>
    Q.PAT_ABBREV_TAC `z = FOLDL (emit_ec s.sz) Y Z` >>
    `(λx. ∃bc. x.out = bc ++ s.out) z` by (
      qunabbrev_tac`z` >>
      match_mp_tac FOLDL_invariant >>
      fs[] >>
      gen_tac >>
      Cases >> rw[] >>
      metis_tac[compile_varref_append_out,APPEND_ASSOC,CONS_APPEND] ) >>
    fs[] ) >>
  fs[] >>
  PairCases_on `q` >> fs[] >>
  qabbrev_tac `r = num_fold f (q0,1) nz` >>
  `∃bc. (FST r).out = bc ++ s.out` by (
    qunabbrev_tac`r` >>
    qabbrev_tac`a = (q0,1)` >>
    `∃bca. (FST a).out = bca ++ s.out` by rw[Abbr`a`] >>
    pop_assum mp_tac >>
    qid_spec_tac `a` >>
    qid_spec_tac `bca` >>
    qunabbrev_tac`f` >>
    rpt (pop_assum kall_tac) >>
    Induct_on `nz` >> rw[] >>
    rw[Once num_fold_def] >>
    `∃bc. (FST(update_refptr (LENGTH defs) a)).out = bc ++ s.out` by (
      Cases_on `a` >> rw[update_refptr_def,LET_THM] >> fs[] ) >>
    metis_tac[APPEND_ASSOC] ) >>
  Cases_on`r`>>fs[] >>
  qunabbrev_tac`f'` >>
  qmatch_assum_rename_tac`q.out = z ++ s.out`[] >>
  pop_assum mp_tac >>
  map_every qid_spec_tac[`z`,`q`,`nz`] >>
  rpt (pop_assum kall_tac) >>
  Induct >> rw[] >>
  rw[Once num_fold_def])

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
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    fsrw_tac[DNF_ss][] >>
    qmatch_assum_abbrev_tac`a.out = bc ++ cs.out` >>
    Q.PAT_ABBREV_TAC`p = FOLDL compile Y Z` >>
    `(λx. ∃bc. x.out = bc ++ cs.out) p` by (
      qunabbrev_tac`p` >>
      match_mp_tac FOLDL_invariant >>
      fs[] >> rw[] >> metis_tac[APPEND_ASSOC] ) >>
    fs[] ) >>
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
  ``∀cs exps. ∃bc. (FOLDL compile cs exps).out = bc ++ cs.out``,
  rpt gen_tac >>
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
  ``∀c env renv rsz bs bs'.
    Cenv_bs c env renv rsz bs ∧ (∃s p e. bs' = bs with <| stack := s::bs.stack; pc := p; exstack := e |>) ⇒
    Cenv_bs c env renv (rsz+1) bs'``,
  rw[Cenv_bs_def,fmap_rel_def] >>
  qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
  first_x_assum (qspec_then `z` mp_tac) >>
  BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  rw[] )

val bc_state_component_equality = DB.fetch"Bytecode""bc_state_component_equality"

(* TODO: move *)
val SUC_LEAST = store_thm("SUC_LEAST",
  ``!x. P x ==> (SUC ($LEAST P) = LEAST x. 0 < x /\ P (PRE x))``,
  GEN_TAC THEN STRIP_TAC THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 PROVE_TAC[] THEN
  numLib.LEAST_ELIM_TAC THEN
  STRIP_TAC THEN1 (
    Q.EXISTS_TAC `SUC x` THEN
    SRW_TAC[][] ) THEN
  Q.X_GEN_TAC`nn` THEN
  STRIP_TAC THEN
  Q.X_GEN_TAC`m` THEN
  `?n. nn = SUC n` by ( Cases_on `nn` THEN SRW_TAC[][] THEN DECIDE_TAC ) THEN
  SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[] THEN
  `~(n < m)` by PROVE_TAC[] THEN
  `~(SUC m < SUC n)` by (
    SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
    RES_TAC THEN
    FULL_SIMP_TAC(srw_ss())[] ) THEN
  DECIDE_TAC)

val ALL_DISTINCT_FILTER_EL_IMP = store_thm("ALL_DISTINCT_FILTER_EL_IMP",
  ``!P l n1 n2. ALL_DISTINCT (FILTER P l) /\
    n1 < LENGTH l /\ n2 < LENGTH l /\
    (P (EL n1 l)) /\ (EL n1 l = EL n2 l) ==> (n1 = n2)``,
  GEN_TAC THEN Induct THEN1 SRW_TAC[][] THEN
  SRW_TAC[][] THEN FULL_SIMP_TAC(srw_ss())[MEM_FILTER]
  THEN1 PROVE_TAC[] THEN
  Cases_on `n1` THEN Cases_on `n2` THEN
  FULL_SIMP_TAC(srw_ss())[MEM_EL] THEN
  PROVE_TAC[] )

val bc_find_loc_aux_thm = store_thm("bc_find_loc_aux_thm",
  ``∀il ls l n.
     bc_find_loc_aux ls il l n =
     if MEM (Label l) ls then
     SOME (n + SUM (MAP (SUC o il) (FILTER ($~ o is_Label) (TAKE (LEAST m. m < LENGTH ls ∧ (EL m ls = Label l)) ls))))
     else NONE``,
  gen_tac >> Induct >- rw[bc_find_loc_aux_def] >>
  simp[bc_find_loc_aux_def] >>
  qx_gen_tac `h` >> qx_gen_tac `l` >>
  Cases_on `h = Label l` >> fs[] >- (
    qx_gen_tac `n` >>
    qmatch_abbrev_tac `n = n + m` >>
    qsuff_tac `m = 0` >- rw[] >>
    unabbrev_all_tac >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (
      qexists_tac `0` >> rw[] ) >>
    gen_tac >>
    strip_tac >>
    first_x_assum (qspec_then `0` mp_tac) >>
    srw_tac[ARITH_ss][] ) >>
  Cases_on `MEM (Label l) ls` >> fs[] >>
  Q.PAT_ABBREV_TAC`l0 = $LEAST X` >>
  Q.PAT_ABBREV_TAC`l1 = $LEAST X` >>
  `(SUC l0) = l1` by (
    unabbrev_all_tac >>
    qmatch_abbrev_tac `SUC ($LEAST P) = X` >>
    `∃n. P n` by (
      fs[MEM_EL,Abbr`P`] >>
      PROVE_TAC[] ) >>
    rw[UNDISCH(Q.SPEC`n`SUC_LEAST)] >>
    unabbrev_all_tac >>
    AP_TERM_TAC >>
    rw[FUN_EQ_THM] >>
    Cases_on `m` >> rw[] ) >>
  srw_tac[ARITH_ss][])

val bc_find_loc_aux_ALL_DISTINCT = store_thm("bc_find_loc_aux_ALL_DISTINCT",
  ``∀ls il l n z k. ALL_DISTINCT (FILTER is_Label ls) ∧ (k < LENGTH ls) ∧ (EL k ls = Label l) ∧
    (z = n + next_addr il (TAKE k ls)) ⇒
    (bc_find_loc_aux ls il l n = SOME z)``,
  rw[bc_find_loc_aux_thm] >- (
   rw[MEM_EL] >> PROVE_TAC[] ) >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- PROVE_TAC[] >>
  qx_gen_tac `j` >> rw[] >>
  qsuff_tac `k = j` >> rw[] >>
  match_mp_tac (Q.ISPEC`is_Label`ALL_DISTINCT_FILTER_EL_IMP) >>
  qexists_tac `ls` >> rw[])

val labels_compile_varref = store_thm("labels_compile_varref",
  ``FILTER is_Label (compile_varref cs b).out = FILTER is_Label cs.out``,
  Cases_on`b` >> rw[])
val _ = export_rewrites["labels_compile_varref"]

val labels_compile_decl = store_thm("labels_compile_decl",
  ``∀env0 a vs. FILTER is_Label (FST (compile_decl env0 a vs)).out = FILTER is_Label (FST a).out``,
  rw[compile_decl_def] >>
  SIMPLE_QUANT_ABBREV_TAC [select_fun_constant``FOLDL`` 1 "f"] >>
  qho_match_abbrev_tac`P (FOLDL f a vs)` >>
  match_mp_tac FOLDL_invariant >> fs[Abbr`P`] >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  rw[Abbr`f`] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[])

val labels_compile_closures = store_thm("labels_compile_closures",
  ``∀nz s defs. FILTER is_Label (compile_closures nz s defs).out = FILTER is_Label s.out``,
  rw[compile_closures_def] >>
  `FILTER is_Label s'.out = FILTER is_Label s.out` by (
    qunabbrev_tac`s'` >>
    qid_spec_tac `s` >>
    rpt (pop_assum kall_tac) >>
    Induct_on `nz`  >> rw[Once num_fold_def] ) >>
  qabbrev_tac`ls = FILTER is_Label s.out` >>
  `($= ls o FILTER is_Label o compiler_state_out o FST) (FOLDL push_lab (s',0,[]) defs)` by (
    match_mp_tac FOLDL_invariant >> fs[] >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    qx_gen_tac`y` >> PairCases_on`y` >>
    Cases_on`y1`>>rw[push_lab_def] >>rw[] >>
    unabbrev_all_tac>>rw[])>>
  qmatch_assum_abbrev_tac `FOLDL X Y Z = (s''',k')` >>
  `($= ls o FILTER is_Label o compiler_state_out o FST) (FOLDL X Y Z)` by (
    match_mp_tac FOLDL_invariant >> fs[Abbr`Y`] >>
    Cases >> Cases >> simp[Abbr`X`,cons_closure_def,LET_THM] >>
    strip_tac >>
    Q.PAT_ABBREV_TAC`p = FOLDL (emit_ec sz0) X Y` >>
    `($= ls o FILTER is_Label o compiler_state_out) p` by (
      qunabbrev_tac`p` >>
      match_mp_tac FOLDL_invariant >>
      fs[] >>
      gen_tac >> Cases >> rw[] ) >>
    fs[] ) >>
  qabbrev_tac`a = (s'''',k'')` >>
  map_every qunabbrev_tac[`X`,`Y`,`Z`] >>
  `(ls = FILTER is_Label (FST a).out)` by (
    qpat_assum`num_fold X Y Z = a` mp_tac >>
    qabbrev_tac`b = (s''',1)` >>
    `ls = (FILTER is_Label (FST b).out)` by rfs[Abbr`b`] >>
    pop_assum mp_tac >>
    map_every qid_spec_tac [`a`,`b`,`nz`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> rw[] >> rw[Once num_fold_def] >>
    simp_tac std_ss [Once num_fold_def] >>
    rw[] >> first_x_assum (match_mp_tac o MP_CANON) >>
    qexists_tac `update_refptr nk b` >>
    Cases_on `b` >> rw[update_refptr_def] >>
    unabbrev_all_tac >> fs[] ) >>
  pop_assum mp_tac >>
  simp[Abbr`a`] >>
  map_every qid_spec_tac[`s''''`,`nz`] >>
  rpt (pop_assum kall_tac) >>
  Induct >> rw[] >> rw[Once num_fold_def])
val _ = export_rewrites["labels_compile_closures"]

val compile_varref_next_label_inc = store_thm("compile_varref_next_label_inc",
  ``∀cs b. (compile_varref cs b).next_label = cs.next_label``,
  gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_next_label_inc"]

val compile_decl_next_label_inc = store_thm("compile_decl_next_label_inc",
  ``∀env0 a vs.(FST (compile_decl env0 a vs)).next_label = (FST a).next_label``,
  rw[compile_decl_def] >>
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``FOLDL``1"f"] >>
  qho_match_abbrev_tac`P (FOLDL f a vs)` >>
  match_mp_tac FOLDL_invariant >>
  fs[Abbr`P`] >>
  qx_gen_tac `x` >> PairCases_on`x` >>
  rw[Abbr`f`] >>
  BasicProvers.EVERY_CASE_TAC >>
  rw[])
val _ = export_rewrites["compile_decl_next_label_inc"]

val compile_closures_next_label_inc = store_thm("compile_closures_next_label_inc",
  ``∀nz cs defs. (compile_closures nz cs defs).next_label = cs.next_label``,
  rw[compile_closures_def] >>
  `s.next_label = cs.next_label` by (
    qunabbrev_tac`s` >>
    qid_spec_tac `cs` >>
    qid_spec_tac `nz` >>
    Induct >> rw[] >>
    rw[Once num_fold_def] ) >>
  qmatch_assum_abbrev_tac `FOLDL X Y Z = (s'',k')` >>
  `($= s'.next_label o compiler_state_next_label o FST) (FOLDL X Y Z)` by (
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    rw[cons_closure_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`p = FOLDL (emit_ec cs.sz) Y Z` >>
    qho_match_abbrev_tac`P p` >>
    qunabbrev_tac`p` >>
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    gen_tac >> Cases >> rw[] ) >>
  pop_assum mp_tac >> rw[] >>
  qabbrev_tac`a = (s'',1)` >>
  qabbrev_tac`b = (s''',k'')` >>
  `(FST a).next_label = (FST b).next_label` by (
    qpat_assum`Q = b` mp_tac >>
    map_every qid_spec_tac[`b`,`a`,`nz`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> rw[] >>
    rw[Once num_fold_def] >>
    simp_tac std_ss [Once num_fold_def] >>
    rw[] >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `(FST (update_refptr nk a)).next_label` >>
    rw[] >>
    Cases_on `a` >> rw[update_refptr_def,LET_THM] ) >>
  unabbrev_all_tac >> fs[] >>
  qmatch_assum_abbrev_tac `FOLDL X Y defs = Z` >>
  `($= cs.next_label o compiler_state_next_label o FST) (FOLDL X Y defs)` by (
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    Cases_on `y1` >> rw[push_lab_def,LET_THM] ) >>
  unabbrev_all_tac >>
  pop_assum mp_tac >> rw[] >>
  map_every qid_spec_tac[`s'''`,`nz`] >>
  rpt (pop_assum kall_tac) >>
  Induct >> rw[] >>
  rw[Once num_fold_def] )
val _ = export_rewrites["compile_closures_next_label_inc"]

val compile_next_label_inc = store_thm("compile_next_label_inc",
  ``(∀cs exp. cs.next_label ≤ (compile cs exp).next_label) ∧
    (∀env0 sz1 exp n cs xs l. cs.next_label ≤ (compile_bindings env0 sz1 exp n cs xs).next_label)``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    rw[UNCURRY] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] ) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``FOLDL``2"cs0"] >>
    qho_match_abbrev_tac`P (FOLDL compile cs0 es)` >>
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> rw[] >>
    res_tac >> metis_tac[LESS_EQ_TRANS] ) >>
  strip_tac >- ( rw[compile_def,LET_THM] ) >>
  strip_tac >- ( rw[compile_def,LET_THM] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``FOLDL``2"cs0"] >>
    qmatch_assum_abbrev_tac`a:num ≤ b` >>
    match_mp_tac LESS_EQ_TRANS >> qexists_tac `a` >>
    qunabbrev_tac`a` >> rw[] >>
    qho_match_abbrev_tac`P (FOLDL compile cs0 es)` >>
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    metis_tac[LESS_EQ_TRANS] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    fsrw_tac[DNF_ss,ETA_ss][] >>
    qmatch_assum_abbrev_tac `nl ≤ (compile cs0 exp).next_label` >>
    qho_match_abbrev_tac`P (FOLDL compile (compile cs0 exp) es)` >>
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    metis_tac[LESS_EQ_TRANS]) >>
  strip_tac >- srw_tac[ARITH_ss][compile_def,LET_THM] >>
  strip_tac >- (
    srw_tac[ARITH_ss][compile_def,LET_THM] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] ) >>
  rw[compile_def])

val between_def = Define`
  between x y z = x:num ≤ z ∧ z < y`

val is_Label_rwt = store_thm("is_Label_rwt",
  ``∀i. is_Label i = ∃l. i = Label l``,
  Cases >> rw[])

val FOLDL_compile_next_label_inc = store_thm("FOLDL_compile_next_label_inc",
  ``∀cs es. cs.next_label ≤ (FOLDL compile cs es).next_label``,
  rpt gen_tac >> qho_match_abbrev_tac`P (FOLDL compile cs es)` >>
  match_mp_tac FOLDL_invariant >>
  fs[Abbr`P`] >>
  metis_tac[compile_next_label_inc,LESS_EQ_TRANS])

val compile_next_label = store_thm("compile_next_label",
  ``(∀cs exp ls. (FILTER is_Label (compile cs exp).out = ls ++ FILTER is_Label cs.out) ⇒
                    EVERY (between cs.next_label (compile cs exp).next_label) (MAP dest_Label ls)) ∧
    (∀env0 sz1 exp n cs xs ls.
      (FILTER is_Label (compile_bindings env0 sz1 exp n cs xs).out = ls ++ FILTER is_Label cs.out) ⇒
        EVERY (between cs.next_label (compile_bindings env0 sz1 exp n cs xs).next_label) (MAP dest_Label ls))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    simp[compile_def,LET_THM] >>
    rpt gen_tac >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >> fs[] >>
    fs[UNCURRY] >>
    fs[labels_compile_decl] >> rw[]) >>
  strip_tac >- (rw[compile_def] >> rw[]) >>
  strip_tac >- (rw[compile_def] >> rw[]) >>
  strip_tac >- (rw[compile_def] >> rw[]) >>
  strip_tac >- (rw[compile_def] >> rw[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fsrw_tac[ETA_ss][compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    `(λx. cs.next_label ≤ x.next_label ∧
          ∃ls. (FILTER is_Label x.out = ls ++ FILTER is_Label cs.out) ∧
          EVERY (between cs.next_label x.next_label) (MAP dest_Label ls))
     (FOLDL compile cs0 es)` by (
      match_mp_tac FOLDL_invariant >>
      fs[Abbr`cs0`] >>
      map_every qx_gen_tac [`cx`,`e`] >>
      rw[] >- metis_tac[LESS_EQ_TRANS,compile_next_label_inc] >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_append_out) >>
      strip_tac >>
      first_x_assum(qspecl_then[`e`,`cx`]mp_tac) >>
      fs[FILTER_APPEND] >>
      fs[FILTER_EQ_APPEND] >>
      BasicProvers.VAR_EQ_TAC >>
      qpat_assum`cx.out = X`assume_tac >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
      metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_TRANS,compile_next_label_inc] ) >>
    fs[] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fsrw_tac[ETA_ss][compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    `(λx. cs.next_label ≤ x.next_label ∧
          ∃ls. (FILTER is_Label x.out = ls ++ FILTER is_Label cs.out) ∧
          EVERY (between cs.next_label x.next_label) (MAP dest_Label ls))
     (FOLDL compile cs0 es)` by (
      match_mp_tac FOLDL_invariant >>
      fs[Abbr`cs0`] >>
      map_every qx_gen_tac [`cx`,`e`] >>
      rw[] >- metis_tac[LESS_EQ_TRANS,compile_next_label_inc] >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_append_out) >>
      strip_tac >>
      first_x_assum(qspecl_then[`e`,`cx`]mp_tac) >>
      fs[FILTER_APPEND] >>
      fs[FILTER_EQ_APPEND] >>
      BasicProvers.VAR_EQ_TAC >>
      qpat_assum`cx.out = X`assume_tac >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
      metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_TRANS,compile_next_label_inc] ) >>
    Q.PAT_ABBREV_TAC`env0 = compiler_state_env X` >>
    Q.PAT_ABBREV_TAC `cs1 = compiler_state_tail_fupd X Y` >>
    qspecl_then[`env0`,`cs.sz+1`,`exp`,`0`,`cs1`,`xs`]mp_tac(CONJUNCT2 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >> fs[FILTER_APPEND] >>
    qspecl_then[`env0`,`cs.sz+1`,`exp`,`0`,`cs1`,`xs`]mp_tac(CONJUNCT2 compile_next_label_inc) >>
    fs[Abbr`cs1`] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
    qspecl_then[`cs0`,`es`]mp_tac FOLDL_compile_next_label_inc >>
    fs[FILTER_EQ_APPEND] >> rfs[] >>
    BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def,Abbr`cs0`] >>
    metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_TRANS] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fsrw_tac[ETA_ss][compile_def,LET_THM]) >>
  strip_tac >- (rw[compile_def] >> rw[]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    fsrw_tac[ETA_ss][compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    gen_tac >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >> rw[] >>
    `(λx. cs.next_label ≤ x.next_label ∧
          ∃ls. (FILTER is_Label x.out = ls ++ FILTER is_Label cs.out) ∧
          EVERY (between cs.next_label x.next_label) (MAP dest_Label ls))
     (FOLDL compile (compile cs0 exp) es)` by (
      match_mp_tac FOLDL_invariant >>
      conj_tac >- (
        fs[] >>
        qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
        qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_next_label_inc) >> strip_tac >>
        fsrw_tac[ARITH_ss][Abbr`cs0`,FILTER_APPEND] ) >>
      fs[Abbr`cs0`] >>
      map_every qx_gen_tac [`cx`,`e`] >>
      rw[] >- metis_tac[LESS_EQ_TRANS,compile_next_label_inc] >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_append_out) >>
      strip_tac >>
      first_x_assum(qspecl_then[`e`,`cx`]mp_tac) >>
      fs[FILTER_APPEND] >>
      fs[FILTER_EQ_APPEND] >>
      BasicProvers.VAR_EQ_TAC >>
      qpat_assum`cx.out = X`assume_tac >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
      metis_tac[LESS_LESS_EQ_TRANS,LESS_EQ_TRANS,compile_next_label_inc] ) >>
    rfs[] ) >>
  strip_tac >- (
    ntac 2 gen_tac >> map_every qx_gen_tac [`e1`,`e2`] >> strip_tac >>
    fsrw_tac[][compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    qspecl_then[`compile cs0 e1`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then (Q.X_CHOOSE_THEN`bc2` strip_assume_tac) >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then (Q.X_CHOOSE_THEN`bc1` strip_assume_tac) >>
    `cs0.out = cs.out` by rw[Abbr`cs0`] >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
    strip_tac >>
    qspecl_then[`compile cs0 e1`,`e2`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
    strip_tac >>
    `cs0.next_label = cs.next_label`by rw[Abbr`cs0`] >>
    fsrw_tac[ARITH_ss,DNF_ss][FILTER_APPEND,EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
    metis_tac[LESS_EQ_TRANS,LESS_LESS_EQ_TRANS] ) >>
  strip_tac >- (
    map_every qx_gen_tac [`cs`,`e1`,`e2`,`e3`] >>
    strip_tac >>
    simp[compile_def] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_state_sz_fupd (K ((compile cs0 e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_state_sz_fupd (K ((compile cs2 e2).sz - 1)) Y` >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >> strip_tac >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs2` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    strip_tac >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs3` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs2` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    strip_tac >>
    ntac 3 (pop_assum mp_tac) >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`b1`mp_tac) >>
    simp[FILTER_APPEND] >>
    ntac 2 strip_tac >>
    rpt strip_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt] >>
    qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`b3`mp_tac) >>
    strip_tac >>
    qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`b2`mp_tac) >>
    strip_tac >>
    qmatch_assum_abbrev_tac `l1::ll = ls ++ ll2` >>
    `ls = l1::(FILTER is_Label (b3 ++ HD(cs3.out)::b2 ++ (HD cs2.out)::b1))` by (
      qunabbrev_tac`ll` >>
      qpat_assum `l1::l2=ls++ll2` mp_tac >>
      disch_then (strip_assume_tac o SYM) >>
      fs[APPEND_EQ_CONS] >>
      rfs[FILTER_APPEND,Abbr`cs3`,Abbr`cs2`,Abbr`cs0`,Abbr`ll2`] ) >>
    qx_gen_tac `x` >> strip_tac >>
    pop_assum mp_tac >>
    pop_assum SUBST1_TAC >>
    map_every qunabbrev_tac[`ll2`,`ll`,`l1`] >>
    qpat_assum `X = ls ++ Y` kall_tac >>
    `cs0.next_label = cs.next_label` by rw[Abbr`cs0`] >>
    `cs.next_label ≤ cs1.next_label` by (
      rw[Abbr`cs1`] >>
      metis_tac[compile_next_label_inc] ) >>
    `cs2.next_label = cs1.next_label + 3` by (
      unabbrev_all_tac >> rw[] ) >>
    `cs.next_label ≤ (compile cs0 e1).next_label` by (
      metis_tac[compile_next_label_inc] ) >>
    `cs3.next_label ≤ (compile cs3 e3).next_label` by (
      metis_tac[compile_next_label_inc] ) >>
    `cs2.next_label ≤ cs3.next_label` by (
      qunabbrev_tac`cs3` >> rw[] >>
      metis_tac[compile_next_label_inc] ) >>
    `(compile cs0 e1).next_label = cs1.next_label` by (
      unabbrev_all_tac >> rw[] ) >>
    `cs2.next_label ≤ (compile cs2 e2).next_label` by (
      metis_tac[compile_next_label_inc]) >>
    `cs0.next_label ≤ (compile cs0 e1).next_label` by (
      metis_tac[compile_next_label_inc]) >>
    simp_tac std_ss [MEM] >>
    strip_tac >- (srw_tac[ARITH_ss][between_def]) >>
    pop_assum mp_tac >>
    `HD cs3.out = Label ((compile cs0 e1).next_label + 1)` by rw[Abbr`cs3`] >>
    `HD cs2.out = Label ((compile cs0 e1).next_label)` by rw[Abbr`cs2`] >>
    simp[FILTER_APPEND] >>
    `FILTER is_Label (compile cs3 e3).out =
     FILTER is_Label b3 ++ [Label (cs1.next_label + 1)] ++
     FILTER is_Label (compile cs2 e2).out` by (
       rw[FILTER_APPEND,Abbr`cs3`] ) >>
    `FILTER is_Label (compile cs2 e2).out =
     FILTER is_Label b2 ++ [Label cs1.next_label] ++
     FILTER is_Label cs1.out` by (
      `cs1.out = b1 ++ cs0.out` by (
        qunabbrev_tac`cs1` >> simp[] ) >>
      pop_assum SUBST1_TAC >>
      simp[FILTER_APPEND] >>
      rw[Abbr`cs2`,FILTER_APPEND] ) >>
    qpat_assum `X = b3 ++ Y` mp_tac >>
    qpat_assum `X = b2 ++ Y` mp_tac >>
    fs[] >>
    ntac 2 (disch_then kall_tac) >>
    ntac 4 (pop_assum kall_tac) >>
    Cases_on `MEM x (FILTER is_Label b3)` >- (
      fs[] >>
      fsrw_tac[DNF_ss][MEM_FILTER,is_Label_rwt] >>
      rw[] >>
      fsrw_tac[DNF_ss][between_def] >>
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    fs[] >>
    Cases_on `x = Label (cs1.next_label + 1)` >- (
      srw_tac[ARITH_ss][between_def] ) >>
    fs[] >>
    Cases_on `MEM x (FILTER is_Label b2)` >- (
      fs[] >>
      fsrw_tac[DNF_ss][MEM_FILTER,is_Label_rwt] >>
      rw[] >>
      fsrw_tac[DNF_ss][between_def] >>
      res_tac >> fsrw_tac[ARITH_ss][] >>
      `(compile cs2 e2).next_label = cs3.next_label` by (
        rw[Abbr`cs3`] ) >>
      DECIDE_TAC ) >>
    fs[] >>
    strip_tac >- (
      srw_tac[ARITH_ss][between_def] ) >>
    fsrw_tac[DNF_ss][MEM_FILTER,is_Label_rwt] >> rw[] >>
    res_tac >>
    fsrw_tac[ARITH_ss][Abbr`cs1`,between_def] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] ) >>
  rw[compile_def] )

val compile_ALL_DISTINCT_labels = store_thm("compile_ALL_DISTINCT_labels",
  ``(∀cs exp. ALL_DISTINCT (FILTER is_Label cs.out) ∧ EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label cs.out) ⇒
      ALL_DISTINCT (FILTER is_Label (compile cs exp).out)) ∧
    (∀env0 sz1 exp n cs xs. ALL_DISTINCT (FILTER is_Label cs.out) ∧ EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label cs.out) ⇒
      ALL_DISTINCT (FILTER is_Label (compile_bindings env0 sz1 exp n cs xs).out))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def] >>
    BasicProvers.EVERY_CASE_TAC >- rw[] >>
    rw[LET_THM] >> rw[UNCURRY,labels_compile_decl] ) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    Q.PAT_ABBREV_TAC`a = compiler_state_tail_fupd X Y` >>
    `(λx. EVERY (combin$C $< x.next_label o dest_Label) (FILTER is_Label x.out) ∧
        ALL_DISTINCT (FILTER is_Label x.out))
     (FOLDL compile a es)` by (
      match_mp_tac FOLDL_invariant >>
      fs[Abbr`a`] >>
      map_every qx_gen_tac [`cx`,`e`] >> strip_tac >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_next_label) >> strip_tac >>
      rfs[FILTER_APPEND] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
      metis_tac[compile_next_label_inc,LESS_LESS_EQ_TRANS] ) >>
    fs[] ) >>
  strip_tac >- (rw[compile_def] >> fs[]) >>
  strip_tac >- (rw[compile_def] >> fs[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    first_x_assum match_mp_tac >>
    Q.PAT_ABBREV_TAC`a = compiler_state_tail_fupd X Y` >>
    qho_match_abbrev_tac`P (FOLDL compile a es)` >>
    match_mp_tac FOLDL_invariant >>
    fs[Abbr`P`,Abbr`a`] >>
    map_every qx_gen_tac [`cx`,`e`] >> strip_tac >>
    qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
    qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_next_label) >> strip_tac >>
    rfs[FILTER_APPEND] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
    metis_tac[compile_next_label_inc,LESS_LESS_EQ_TRANS] ) >>
  strip_tac >- ( rw[compile_def,LET_THM] ) >>
  strip_tac >- ( rw[compile_def] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >> fs[] >>
    srw_tac[ETA_ss][] >> rfs[] >>
    Q.PAT_ABBREV_TAC`a = compiler_state_tail_fupd X Y` >>
    `(λx. EVERY (combin$C $< x.next_label o dest_Label) (FILTER is_Label x.out) ∧
        ALL_DISTINCT (FILTER is_Label x.out))
     (FOLDL compile (compile a exp) es)` by (
      match_mp_tac FOLDL_invariant >>
      fs[] >>
      conj_tac >- (
        qspecl_then[`a`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
        qspecl_then[`a`,`exp`]mp_tac(CONJUNCT1 compile_next_label) >> strip_tac >>
        rfs[FILTER_APPEND] >>
        fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
        `a.out = cs.out` by rw[Abbr`a`] >>
        `a.next_label = cs.next_label` by rw[Abbr`a`] >>
        metis_tac[compile_next_label_inc,LESS_LESS_EQ_TRANS] ) >>
      map_every qx_gen_tac [`cx`,`e`] >> strip_tac >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
      qspecl_then[`cx`,`e`]mp_tac(CONJUNCT1 compile_next_label) >> strip_tac >>
      rfs[FILTER_APPEND] >>
      fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
      metis_tac[compile_next_label_inc,LESS_LESS_EQ_TRANS] ) >>
    fs[] ) >>
  strip_tac >- (
    map_every qx_gen_tac[`cs`,`op`,`e1`,`e2`] >>
    strip_tac >>
    rw[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    fs[] >>
    first_x_assum match_mp_tac >>
    `cs0.out = cs.out` by rw[Abbr`cs0`] >>
    `cs0.next_label = cs.next_label` by rw[Abbr`cs0`] >>
    fs[] >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_next_label) >> strip_tac >>
    rfs[FILTER_APPEND] >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
    metis_tac[compile_next_label_inc,LESS_LESS_EQ_TRANS] ) >>
  strip_tac >- (
    map_every qx_gen_tac [`cs`,`e1`,`e2`,`e3`]>>
    strip_tac >>
    simp[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_state_sz_fupd (K ((compile cs0 e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_state_sz_fupd (K ((compile cs2 e2).sz - 1)) Y` >>
    strip_tac >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >> strip_tac >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs2` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >> strip_tac >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs2` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs3` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    strip_tac >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`b1`mp_tac) >> strip_tac >>
    qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`b2`mp_tac) >> strip_tac >>
    qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`b3`mp_tac) >> strip_tac >>
    qspecl_then[`cs3`,`e3`,`FILTER is_Label b3`]mp_tac(CONJUNCT1 compile_next_label) >>
    qspecl_then[`cs2`,`e2`,`FILTER is_Label b2`]mp_tac(CONJUNCT1 compile_next_label) >>
    qspecl_then[`cs0`,`e1`,`FILTER is_Label b1`]mp_tac(CONJUNCT1 compile_next_label) >>
    `cs0.next_label = cs.next_label` by rw[Abbr`cs0`] >>
    `cs0.out = cs.out` by rw[Abbr`cs0`] >>
    simp[FILTER_APPEND] >>
    ntac 3 strip_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt,between_def] >>
    rfs[] >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
    `cs3.next_label = (compile cs2 e2).next_label` by ( rw[Abbr`cs3`] ) >>
    qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
    `cs2.next_label = (compile cs0 e1).next_label + 3` by ( rw[Abbr`cs2`] ) >>
    ntac 2 strip_tac >>
    qabbrev_tac`nl = (compile cs0 e1).next_label` >>
    Cases_on `MEM (Label (nl + 2)) b3` >- (
      res_tac >>
      `nl + 3 ≤ nl + 2` by metis_tac[LESS_EQ_TRANS] >>
      fsrw_tac[ARITH_ss][] ) >>
    Cases_on `MEM (Label (nl + 2)) b2` >- (
      res_tac >>
      `nl + 3 ≤ nl + 2` by metis_tac[LESS_EQ_TRANS] >>
      fsrw_tac[ARITH_ss][] ) >>
    Cases_on `MEM (Label (nl + 2)) b1` >- (
      res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    Cases_on `MEM (Label (nl + 2)) cs.out` >- (
      res_tac >>
      `nl < nl + 2` by srw_tac[ARITH_ss][] >>
      metis_tac[LESS_LESS_EQ_TRANS,LESS_TRANS,prim_recTheory.LESS_REFL] ) >>
    fs[] >>
    conj_asm1_tac >- (
      IMP_RES_THEN (assume_tac o SIMP_RULE(srw_ss())[]) (METIS_PROVE[]``Abbrev(x=y)==>(x.out = y.out)``) >>
      qpat_assum `cs3.out = X` SUBST1_TAC >>
      simp[] ) >>
    fs[FILTER_APPEND] >>
    first_x_assum match_mp_tac >>
    `cs1.next_label = nl` by rw[Abbr`cs1`] >> fs[] >>
    Cases_on `MEM (Label (nl + 1)) b2` >- (
      res_tac >>
      `nl + 3 ≤ nl + 1` by metis_tac[LESS_EQ_TRANS] >>
      fsrw_tac[ARITH_ss][] ) >>
    Cases_on `MEM (Label (nl + 1)) b1` >- (
      res_tac >>
      fsrw_tac[ARITH_ss][] ) >>
    Cases_on `MEM (Label (nl + 1)) cs.out` >- (
      res_tac >>
      `nl < nl + 1` by srw_tac[ARITH_ss][] >>
      metis_tac[LESS_LESS_EQ_TRANS,LESS_TRANS,prim_recTheory.LESS_REFL] ) >>
    fs[] >>
    Cases_on `MEM (Label (nl + 1)) cs2.out` >- (
      fs[] >> pop_assum mp_tac >> simp[] >>
      IMP_RES_THEN (assume_tac o SIMP_RULE(srw_ss())[]) (METIS_PROVE[]``Abbrev(x=y)==>(x.out = y.out)``) >>
      qpat_assum `cs2.out = X` SUBST1_TAC >>
      simp[] ) >>
    fs[] >>
    `nl + 1 < (compile cs2 e2).next_label` by DECIDE_TAC >> fs[] >>
    reverse conj_asm2_tac >- (
      gen_tac >>
      IMP_RES_THEN (assume_tac o SIMP_RULE(srw_ss())[]) (METIS_PROVE[]``Abbrev(x=y)==>(x.out = y.out)``) >>
      qpat_assum `cs2.out = X` SUBST1_TAC >>
      simp[] >>
      strip_tac >> res_tac >>
      DECIDE_TAC ) >>
    first_x_assum match_mp_tac >>
    Cases_on `MEM (Label nl) b1` >- (
      res_tac >> fs[] ) >>
    Cases_on `MEM (Label nl) cs.out` >- (
      res_tac >> fsrw_tac[ARITH_ss][] ) >>
    Cases_on `MEM (Label nl) cs1.out` >- (
      fs[] >> pop_assum mp_tac >> simp[] >>
      IMP_RES_THEN (assume_tac o SIMP_RULE(srw_ss())[]) (METIS_PROVE[]``Abbrev(x=y)==>(x.out = y.out)``) >>
      qpat_assum `cs1.out = X` SUBST1_TAC >>
      simp[] ) >>
    fs[] >>
    reverse conj_asm2_tac >- (
      gen_tac >>
      IMP_RES_THEN (assume_tac o SIMP_RULE(srw_ss())[]) (METIS_PROVE[]``Abbrev(x=y)==>(x.out = y.out)``) >>
      qpat_assum `cs1.out = X` SUBST1_TAC >>
      simp[] >>
      strip_tac >> res_tac >>
      DECIDE_TAC ) >>
    `cs1.out = b1 ++ cs.out` by rw[Abbr`cs1`] >>
    pop_assum SUBST1_TAC >>
    simp[FILTER_APPEND] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] ) >>
  rw[compile_def] )

val Cenv_bs_pc = store_thm("Cenv_bs_pc",
  ``Cenv_bs c env env0 sz0 bs ⇒ Cenv_bs c env env0 sz0 (bs with pc := p)``,
  rw[Cenv_bs_def])

val bc_fetch_aux_append_code = store_thm("bc_fetch_aux_append_code",
  ``∀il ls n l2 i. (bc_fetch_aux ls il n = SOME i) ⇒ (bc_fetch_aux (ls ++ l2) il n = SOME i)``,
    gen_tac >> Induct >> rw[bc_fetch_aux_def] )

val bc_fetch_append_code = store_thm("bc_fetch_append_code",
  ``(bc_fetch bs = SOME i) ⇒ (bc_fetch (bs with code := bs.code ++ c) = SOME i)``,
  rw[bc_fetch_def] >>
  imp_res_tac bc_fetch_aux_append_code >>
  rw[] )

val bc_find_loc_aux_append_code = store_thm("bc_find_loc_aux_append_code",
  ``∀il ls n l2 l i. (bc_find_loc_aux ls il n l = SOME i) ⇒ (bc_find_loc_aux (ls ++ l2) il n l = SOME i)``,
  gen_tac >> Induct >> rw[bc_find_loc_aux_def] )

val bc_find_loc_append_code = store_thm("bc_find_loc_append_code",
  ``(bc_find_loc bs l = SOME n) ⇒ (bc_find_loc (bs with code := bs.code ++ c) l = SOME n)``,
  Cases_on `l` >> rw[bc_find_loc_def] >>
  imp_res_tac bc_find_loc_aux_append_code >>
  rw[] )

val bc_next_append_code = store_thm("bc_next_append_code",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ ∀c0 c. (bs1.code = c0) ⇒ bc_next (bs1 with code := c0 ++ c) (bs2 with code := c0 ++ c)``,
  ho_match_mp_tac bc_next_ind >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    rw[bc_eval1_def] >>
    fs[bc_eval_stack_thm] >>
    rw[bump_pc_def] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] >>
    rw[bump_pc_with_stack] >>
    rw[bump_pc_def] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] >>
    rw[bc_state_component_equality] >>
    rw[bump_pc_def] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] >>
    rw[bc_state_component_equality] >>
    rw[bump_pc_def] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    rw[bc_eval1_def,LET_THM] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] >>
    rw[bc_state_component_equality] >>
    rw[bump_pc_def] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] ) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] >>
    rw[bump_pc_def]) >>
  strip_tac >- (
    rw[bc_eval1_thm] >>
    imp_res_tac bc_fetch_append_code >>
    imp_res_tac bc_find_loc_append_code >>
    rw[bc_eval1_def,LET_THM] >>
    rw[bump_pc_def]) >>
  rw[bc_eval1_thm] >>
  imp_res_tac bc_fetch_append_code >>
  imp_res_tac bc_find_loc_append_code >>
  rw[bc_eval1_def,LET_THM] >>
  rw[bump_pc_def])

val Cv_bv_l2a_mono = store_thm("Cv_bv_l2a_mono",
  ``∀pp pp' l2a Cv bv. Cv_bv pp Cv bv ∧
    (∀x y. (FST(SND pp) x = SOME y) ⇒ (l2a x = SOME y))
    ∧ (pp' = (FST pp, l2a, SND(SND pp)))
    ⇒ Cv_bv pp' Cv bv``,
  simp[GSYM AND_IMP_INTRO] >>
  ntac 2 gen_tac >>
  PairCases_on `pp` >> simp[] >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  rw[] >- ( rw[Once Cv_bv_cases,LENGTH_NIL] ) >>
  fs[] >> rw[Once Cv_bv_cases] )

val Cenv_bs_append_code = store_thm("Cenv_bs_append_code",
  ``∀c env env0 sz0 bs bs' ls.
    Cenv_bs c env env0 sz0 bs ∧ (bs' = (bs with code := bs.code ++ ls)) ⇒ Cenv_bs c env env0 sz0 bs'``,
  rw[Cenv_bs_def,fmap_rel_def] >>
  res_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac Cv_bv_l2a_mono >>
  qexists_tac `mk_pp c bs` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val bc_next_preserves_code = store_thm("bc_next_preserves_code",
  ``∀bs1 bs2. bc_next bs1 bs2 ⇒ (bs2.code = bs1.code)``,
  ho_match_mp_tac bc_next_ind >>
  rw[bump_pc_def] >>
  BasicProvers.EVERY_CASE_TAC >> rw[])

val RTC_bc_next_append_code = store_thm("RTC_bc_next_append_code",
  ``∀bs1 bs2 bs1c bs2c c. RTC bc_next bs1 bs2 ∧
    (bs1c = bs1 with code := bs1.code ++ c) ∧
    (bs2c = bs2 with code := bs2.code ++ c)
    ⇒ RTC bc_next bs1c bs2c``,
  rw[] >> (
     RTC_lifts_monotonicities
  |> Q.GEN`R` |> Q.ISPEC `bc_next`
  |> Q.GEN`f` |> Q.SPEC `λbs. bs with code := bs.code ++ c`
  |> strip_assume_tac) >> fs[] >> pop_assum (match_mp_tac o MP_CANON) >>
  rw[] >>
  imp_res_tac bc_next_append_code >> fs[] >>
  metis_tac[bc_next_preserves_code])

val compile_decl_env = store_thm("compile_decl_env",
  ``∀env0 a vs. (FST (compile_decl env0 a vs)).env = (FST a).env``,
  rw[compile_decl_def])

val compile_closures_env = store_thm("compile_closures_env",
  ``∀nz cs defs. (compile_closures nz cs defs).env = cs.env``,
  rw[compile_closures_def] >>
  `s.env = cs.env` by (
    qunabbrev_tac`s` >>
    qmatch_abbrev_tac`(num_fold f cs nz).env = cs.env` >>
    qunabbrev_tac`f` >>
    rpt (pop_assum kall_tac) >>
    qid_spec_tac `cs` >>
    Induct_on `nz` >>
    rw[Once num_fold_def] ) >>
  `($= cs.env o compiler_state_env o FST) (FOLDL push_lab (s,0,[]) defs)` by (
    match_mp_tac FOLDL_invariant >>
    simp[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    Cases_on`y1`>>rw[push_lab_def,LET_THM] ) >> rfs[] >>
  `($= cs.env o compiler_state_env o FST) (FOLDL (cons_closure sz0 nk) (s',1) (REVERSE ecs))` by (
    match_mp_tac FOLDL_invariant >>
    simp[] >>
    Cases >> Cases >>
    rw[cons_closure_def,LET_THM] >>
    qmatch_abbrev_tac`x.env = (FOLDL f a ls).env` >>
    `($= x.env o compiler_state_env) (FOLDL f a ls)`  by (
      match_mp_tac FOLDL_invariant >>
      unabbrev_all_tac >> simp[] >>
      gen_tac >> Cases >> rw[emit_ec_def] ) >>
    unabbrev_all_tac >> fs[] ) >>
  rfs[] >>
  `∀nz a. (FST (num_fold (update_refptr nk) a nz)).env = (FST a).env` by (
    Induct  >> rw[Once num_fold_def] >>
    Cases_on `a` >> rw[update_refptr_def,LET_THM] ) >>
  pop_assum (qspecl_then [`nz`,`s'',1`] mp_tac) >> rw[] >>
  qmatch_abbrev_tac`(num_fold f a nz).env = s''.env` >>
  `s''.env = a.env` by rw[Abbr`a`] >> fs[] >>
  qid_spec_tac`a` >>
  qunabbrev_tac`f` >>
  rpt (pop_assum kall_tac) >>
  Induct_on `nz` >>
  rw[Once num_fold_def])
val _ = export_rewrites["compile_closures_env"]

val compile_env = store_thm("compile_env",
  ``(∀cs exp. (compile cs exp).env = cs.env) ∧
    (∀env0 sz1 exp n cs xs. (compile_bindings env0 sz1 exp n cs xs).env = env0)``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    Q.PAT_ABBREV_TAC`p = compile_decl X Y Z` >>
    PairCases_on`p` >> rw[] >>
    metis_tac[compile_decl_env,FST]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    qho_match_abbrev_tac`P (FOLDL compile cs0 es)` >>
    match_mp_tac FOLDL_invariant >>
    simp[Abbr`P`,Abbr`cs0`] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    qho_match_abbrev_tac`P (FOLDL compile cs0 es)` >>
    match_mp_tac FOLDL_invariant >>
    simp[Abbr`P`,Abbr`cs0`] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >>
    srw_tac[ETA_ss][] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    qho_match_abbrev_tac`P (FOLDL compile (compile cs0 exp) es)` >>
    match_mp_tac FOLDL_invariant >>
    simp[Abbr`P`,Abbr`cs0`] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] )
val _ = export_rewrites["compile_env"]

val good_ec_def = Define`
  good_ec (n,ls) = (n = LENGTH ls)`

val good_ecs_def = Define`
  good_ecs ecs = FEVERY (good_ec o SND) ecs`

val FOLDL_push_lab_ecs_len = store_thm("FOLDL_push_lab_ecs_len",
  ``!a defs. EVERY good_ec (SND (SND a))
    ∧ good_ecs (FST a).ecs
    ∧ (LENGTH (SND(SND a)) = FST(SND a))
    ∧ free_labs_defs defs ⊆ FDOM (FST a).ecs
  ⇒ EVERY good_ec (SND(SND(FOLDL push_lab a defs))) ∧
    ((FST (FOLDL push_lab a defs)).ecs = (FST a).ecs) ∧
    (LENGTH (SND(SND(FOLDL push_lab a defs))) = FST(SND(FOLDL push_lab a defs)))``,
  rpt gen_tac >> strip_tac >>
  qho_match_abbrev_tac`P (FOLDL push_lab a defs)` >>
  match_mp_tac FOLDL_invariant >>
  simp[Abbr`P`] >>
  qx_gen_tac`x`>>PairCases_on`x` >>
  qx_gen_tac`y`>>PairCases_on`y` >>
  Cases_on`y1`>>rw[push_lab_def,LET_THM] >> srw_tac[ARITH_ss][good_ec_def] >>
  qmatch_abbrev_tac`good_ec p` >> PairCases_on`p` >>
  fsrw_tac[DNF_ss][FEVERY_DEF,EVERY_MEM,MEM_MAP,MEM_FILTER,FORALL_PROD,FRANGE_DEF,SUBSET_DEF,good_ecs_def] >>
  fsrw_tac[QUANT_INST_ss[std_qp]][] >>
  metis_tac[])

val FOLDL_emit_ec_sz = store_thm("FOLDL_emit_ec_sz",
  ``∀ls s a. (FOLDL (emit_ec s) a ls).sz = a.sz + LENGTH ls``,
  Induct >- rw[] >> Cases >> rw[] >> srw_tac[ARITH_ss][])

val FOLDL_push_lab_ecs_ISR = store_thm("FOLDL_push_lab_ecs_ISR",
  ``∀defs a. (FST(SND(FOLDL push_lab a defs))) = FST(SND a) + LENGTH defs``,
  Induct >- rw[] >>
  qx_gen_tac`x` >> PairCases_on`x` >>
  qx_gen_tac`y` >> PairCases_on`y` >>
  Cases_on `x1` >> rw[push_lab_def] >>
  srw_tac[ARITH_ss][])

val compile_closures_sz = store_thm("compile_closures_sz",
  ``∀nz cs defs. good_ecs cs.ecs ∧ free_labs_defs defs ⊆ FDOM cs.ecs ⇒ ((compile_closures nz cs defs).sz = cs.sz + LENGTH defs)``,
  rw[compile_closures_def] >>
  `(s.sz = sz0 + nz) ∧ (s.ecs = cs.ecs)` by (
    qunabbrev_tac`s` >>
    qmatch_abbrev_tac`((num_fold f cs nz).sz = sz0 + nz) ∧ Z` >>
    qunabbrev_tac`Z` >>
    qunabbrev_tac`sz0` >>
    qunabbrev_tac`f` >>
    rpt (pop_assum kall_tac) >>
    qid_spec_tac `cs` >>
    Induct_on `nz` >>
    ntac 2 (rw[Once num_fold_def]) >>
    srw_tac[ARITH_ss][] ) >>
  qabbrev_tac`X = FOLDL push_lab (s,0,[]) defs` >>
  `(FST X).sz = s.sz + LENGTH (SND(SND X))` by (
    qunabbrev_tac`X` >>
    qho_match_abbrev_tac `P (FOLDL push_lab (s,0,[]) defs)` >>
    match_mp_tac FOLDL_invariant >>
    simp[Abbr`P`] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    Cases_on`y1`>>rw[push_lab_def,LET_THM] >>
    srw_tac[ARITH_ss][] ) >>
  qunabbrev_tac`X` >>
  qspecl_then[`(s,0,[])`,`defs`] mp_tac FOLDL_push_lab_ecs_len >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`X = (s'',k')` >>
  `(FST X).sz = s'.sz` by (
    qho_match_abbrev_tac`P X` >>
    qunabbrev_tac`X` >>
    match_mp_tac FOLDL_invariant >>
    simp[Abbr`P`] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    simp[cons_closure_def,LET_THM] >>
    strip_tac >>
    fs[EVERY_MEM,FORALL_PROD,good_ec_def] >>
    res_tac >>
    rw[FOLDL_emit_ec_sz] >>
    srw_tac[ARITH_ss][] ) >>
  qunabbrev_tac`X` >> rfs[] >>
  qmatch_assum_abbrev_tac `num_fold (update_refptr nk) a nz = (s''',k'')` >>
  qmatch_assum_abbrev_tac `X = (s''',k'')` >>
  `(FST X).sz = (FST a).sz` by (
    qunabbrev_tac`X` >>
    map_every qid_spec_tac[`a`,`nk`,`nz`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> rw[Once num_fold_def] >>
    Cases_on `a` >> rw[update_refptr_def,LET_THM] ) >>
  qunabbrev_tac`X` >>
  qunabbrev_tac`a` >> rfs[] >>
  qspecl_then[`defs`,`(s,0,[])`] mp_tac FOLDL_push_lab_ecs_ISR >>
  rw[] >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `s'''.sz - nz` >>
  conj_tac >- (
    map_every qid_spec_tac[`s'''`,`nz`] >>
    rpt (pop_assum kall_tac) >>
    Induct >> rw[Once num_fold_def] >>
    srw_tac[ARITH_ss][] ) >>
  srw_tac[ARITH_ss][])

val FOLDL_invariant_rest = store_thm("FOLDL_invariant_rest",
  ``∀P f ls a. P ls a ∧ (∀x n. n < LENGTH ls ∧ P (DROP n ls) x ⇒ P (DROP (SUC n) ls) (f x (EL n ls))) ⇒ P [] (FOLDL f a ls)``,
  ntac 2 gen_tac >>
  Induct >> rw[] >>
  first_x_assum match_mp_tac >>
  conj_tac >- (
    first_x_assum (qspecl_then[`a`,`0`] mp_tac) >> rw[] ) >>
  rw[] >> first_x_assum (qspecl_then[`x`,`SUC n`] mp_tac) >> rw[])

val compile_varref_ecs = store_thm("compile_varref_ecs",
  ``∀cs b. (compile_varref cs b).ecs = cs.ecs``,
  gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_ecs"]

val compile_closures_ecs = store_thm("compile_closures_ecs",
  ``∀nz cs defs. (compile_closures nz cs defs).ecs = cs.ecs``,
  rw[compile_closures_def] >>
  `s.ecs = cs.ecs` by (
    qunabbrev_tac`s` >>
    qmatch_abbrev_tac`(num_fold f cs nz).ecs = cs.ecs` >>
    qunabbrev_tac`f` >>
    rpt (pop_assum kall_tac) >>
    qid_spec_tac `cs` >>
    Induct_on `nz` >>
    rw[Once num_fold_def] ) >>
  `($= cs.ecs o compiler_state_ecs o FST) (FOLDL push_lab (s,0,[]) defs)` by (
    match_mp_tac FOLDL_invariant >>
    simp[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    Cases_on`y1`>>rw[push_lab_def,LET_THM] ) >> rfs[] >>
  `($= cs.ecs o compiler_state_ecs o FST) (FOLDL (cons_closure sz0 nk) (s',1) (REVERSE ecs))` by (
    match_mp_tac FOLDL_invariant >>
    simp[] >>
    Cases >> Cases >>
    rw[cons_closure_def,LET_THM] >>
    qmatch_abbrev_tac`x.ecs = (FOLDL f a ls).ecs` >>
    `($= x.ecs o compiler_state_ecs) (FOLDL f a ls)`  by (
      match_mp_tac FOLDL_invariant >>
      unabbrev_all_tac >> simp[] >>
      gen_tac >> Cases >> rw[emit_ec_def] ) >>
    unabbrev_all_tac >> fs[] ) >>
  rfs[] >>
  `∀nz a. (FST (num_fold (update_refptr nk) a nz)).ecs = (FST a).ecs` by (
    Induct  >> rw[Once num_fold_def] >>
    Cases_on `a` >> rw[update_refptr_def,LET_THM] ) >>
  pop_assum (qspecl_then [`nz`,`s'',1`] mp_tac) >> rw[] >>
  qmatch_abbrev_tac`(num_fold f a nz).ecs = s''.ecs` >>
  `s''.ecs = a.ecs` by rw[Abbr`a`] >> fs[] >>
  qid_spec_tac`a` >>
  qunabbrev_tac`f` >>
  rpt (pop_assum kall_tac) >>
  Induct_on `nz` >>
  rw[Once num_fold_def])
val _ = export_rewrites["compile_closures_ecs"]

val compile_decl_ecs = store_thm("compile_decl_ecs",
  ``∀ecs0 a vs. (FST (compile_decl ecs0 a vs)).ecs = (FST a).ecs``,
  rpt gen_tac >>
  simp[compile_decl_def] >>
  qmatch_abbrev_tac `((FST (FOLDL f a vs)).ecs = (FST a).ecs)` >>
  `(λx. (FST x).ecs = (FST a).ecs) (FOLDL f a vs)` by (
    match_mp_tac FOLDL_invariant >>
    rw[] >> rw[Abbr`f`] >>
    PairCases_on `x` >> fs[] >>
    rw[] >>
    BasicProvers.EVERY_CASE_TAC >>
    rw[] ) >>
  fs[])
val _ = export_rewrites["compile_decl_ecs"]

val compile_ecs = store_thm("compile_ecs",
  ``(∀cs exp. (compile cs exp).ecs = cs.ecs) ∧
    (∀env0 sz1 exp n cs xs. (compile_bindings env0 sz1 exp n cs xs).ecs = cs.ecs)``,
  ho_match_mp_tac compile_ind >>
  rw[compile_def,LET_THM] >>
  TRY (BasicProvers.EVERY_CASE_TAC) >>
  fsrw_tac[ETA_ss][UNCURRY] >>
  Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
  qmatch_abbrev_tac `(FOLDL compile a ls).ecs = a0.ecs` >>
  `($= a0.ecs o compiler_state_ecs) (FOLDL compile a ls)` by (
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> simp[] ) >>
  fs[])
val _ = export_rewrites["compile_ecs"]

val compiler_state_component_equality = DB.fetch"Compile""compiler_state_component_equality"

val compile_sz = store_thm("compile_sz",
  ``(∀cs exp. good_ecs cs.ecs ∧ free_labs exp ⊆ FDOM cs.ecs ⇒ ((compile cs exp).sz = cs.sz + 1)) ∧
    (∀env0 sz1 exp n cs xs. (compile_bindings env0 sz1 exp n cs xs).sz = sz1)``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >- rw[] >>
    Q.PAT_ABBREV_TAC`p = compile_decl X Y Z` >>
    PairCases_on`p` >> rw[] ) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    Q.ISPECL_THEN[`0`,`cs`,`[(xs,cb)]`]mp_tac compile_closures_sz >>
    Cases_on `cb` >> fs[good_ecs_def] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >>
    srw_tac[ETA_ss][] >> rfs[] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    `(λls a. (a.ecs = cs.ecs) ∧ (a.sz = cs.sz + 1 + LENGTH es - LENGTH ls)) ([]:Cexp list) (FOLDL compile (compile cs0 exp) es)` by (
      match_mp_tac FOLDL_invariant_rest >>
      fsrw_tac[ARITH_ss,DNF_ss][MEM_EL,Abbr`cs0`] >>
      srw_tac[ARITH_ss][] >> res_tac >>
      first_x_assum (qspec_then `x` mp_tac) >>
      srw_tac[ARITH_ss][] >>
      qmatch_assum_rename_tac`m < LENGTH es`[]>>
      `x.sz = SUC m + cs.sz` by DECIDE_TAC >>
      first_x_assum (qspecl_then [`x`,`m`] mp_tac) >>
      srw_tac[ARITH_ss][] >>
      pop_assum match_mp_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
      metis_tac[] ) >>
    fs[] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    map_every qx_gen_tac[`cs`,`e1`,`e2`,`e3`] >>
    rpt strip_tac >>
    rw[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_state_sz_fupd (K ((compile cs0 e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_state_sz_fupd (K ((compile cs2 e2).sz - 1)) Y` >>
    `(compile cs0 e1).sz = cs0.sz + 1` by (
      first_x_assum (match_mp_tac o MP_CANON) >>
      rw[Abbr`cs0`] >> fs[] ) >>
    `cs1.ecs = cs.ecs` by rw[Abbr`cs1`,Abbr`cs0`] >>
    `cs1.sz = cs.sz + 1` by rw[Abbr`cs1`,Abbr`cs0`] >>
    `(compile cs2 e2).sz = cs.sz + 1` by (
      first_x_assum (qspecl_then[`FST(sdt cs)`,`SND(sdt cs)`,`ldt (SND(sdt cs)) (compile cs0 e1)`]mp_tac) >>
      `free_labs e2 ⊆ FDOM cs.ecs` by fs[] >>
      asm_simp_tac(srw_ss()++ARITH_ss)[] >>
      disch_then(SUBST1_TAC o SYM) >>
      AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
      rw[Abbr`cs2`,compiler_state_component_equality,Abbr`cs0`,Abbr`cs1`] ) >>
    first_x_assum (qspec_then `cs0` kall_tac) >>
    first_x_assum (qspec_then `cs2` kall_tac) >>
    first_x_assum (qspec_then `FST (sdt cs)` mp_tac) >>
    `free_labs e3 ⊆ FDOM cs.ecs` by fs[] >>
    simp[] >>
    qmatch_abbrev_tac `((compile cs4 e3).sz = (compile cs5 e2).sz - 1 + 1) ⇒ X` >>
    `cs5 = cs2` by (
      rw[Abbr`cs5`,Abbr`cs2`,compiler_state_component_equality,Abbr`cs0`,Abbr`cs1`] ) >>
    fs[] >>
    `cs4 = cs3` by (
      rw[Abbr`cs4`,Abbr`cs3`,compiler_state_component_equality,Abbr`cs1`] ) >>
    fs[] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  rw[compile_def])

(* TODO: MOVE *)
val TAKE_SUM = store_thm("TAKE_SUM",
  ``!n m l. n + m <= LENGTH l ==> (TAKE (n + m) l = TAKE n l ++ TAKE m (DROP n l))``,
  Induct_on `l` THEN SRW_TAC[][] THEN SRW_TAC[][] THEN
  Cases_on `n` THEN FULL_SIMP_TAC(srw_ss()++ARITH_ss)[ADD1])

val compile_val = store_thm("compile_val",
  ``(∀c env exp res. Cevaluate c env exp res ⇒
      ∀v bc0 bc00 bs cs.
        Cexp_pred exp ∧
        (res = Rval v) ∧
        good_ecs cs.ecs ∧
        free_labs exp ⊆ FDOM cs.ecs ∧
        (bs.code = bc0 ++ (REVERSE (compile cs exp).out)) ∧
        (bc00 = bc0 ++ REVERSE cs.out) ∧
        (bs.pc = next_addr bs.inst_length bc00) ∧
        (Cenv_bs c env cs.env cs.sz (bs with code := bc00)) ∧
        ALL_DISTINCT (FILTER is_Label bc00) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc00)
        ⇒
        ∃bv.
          let bs' = bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length bs.code |> in
          bc_next^* bs bs' ∧
          Cv_bv (mk_pp c bs) v bv ∧
          Cenv_bs c env (compile cs exp).env (compile cs exp).sz bs') ∧
    (∀c env exps ress. Cevaluate_list c env exps ress ⇒
      ∀vs bc0 bc00 bs cs.
        EVERY Cexp_pred exps ∧
        (ress = Rval vs) ∧
        good_ecs cs.ecs ∧
        free_labs_list exps ⊆ FDOM cs.ecs ∧
        (bs.code = bc0 ++ (REVERSE (FOLDL compile cs exps).out)) ∧
        (bc00 = bc0 ++ REVERSE cs.out) ∧
        (bs.pc = next_addr bs.inst_length bc00) ∧
        (Cenv_bs c env cs.env cs.sz (bs with code := bc00)) ∧
        ALL_DISTINCT (FILTER is_Label bc00) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc00)
        ⇒
        ∃bvs.
          let bs' = bs with <| stack := (REVERSE bvs)++bs.stack ; pc := next_addr bs.inst_length bs.code |> in
          bc_next^* bs bs' ∧
          EVERY2 (Cv_bv (mk_pp c bs)) vs bvs ∧
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
      ntac 2 (pop_assum mp_tac) >>
      simp_tac (srw_ss()) [] >>
      metis_tac[])
    >- (
      match_mp_tac Cv_bv_l2a_mono >>
      qmatch_assum_abbrev_tac `Cv_bv pp cv bv` >>
      qexists_tac `pp` >> rw[Abbr`pp`] >>
      PROVE_TAC[bc_find_loc_aux_append_code,compile_varref_append_out,REVERSE_APPEND,APPEND_ASSOC] ) >>
    unabbrev_all_tac >> rw[] >>
    qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
    qmatch_abbrev_tac`X` >>
    first_assum (qspec_then `z` mp_tac) >>
    BasicProvers.CASE_TAC >>
    qunabbrev_tac`X` >>
    imp_res_tac lookup_ct_imp_incsz >>
    rw[] >>
    match_mp_tac Cv_bv_l2a_mono >>
    qmatch_assum_abbrev_tac `Cv_bv pp cv bv` >>
    qexists_tac `pp` >> rw[Abbr`pp`] >>
    PROVE_TAC[bc_find_loc_aux_append_code,compile_varref_append_out,REVERSE_APPEND,APPEND_ASSOC] ) >>
  strip_tac >- (
    ntac 2 gen_tac >>
    Cases >> rw[compile_def,LET_THM] >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x]` >>
    `bc_fetch bs = SOME x` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0`,`[]`] >>
      rw[Abbr`x`] ) >> (
    reverse (rw[Once Cv_bv_cases]) >- (
      match_mp_tac (SPEC_ALL Cenv_bs_imp_incsz) >>
      rw[bc_state_component_equality] >>
      match_mp_tac Cenv_bs_append_code >>
      qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
      qexists_tac `bs0` >>
      rw[Abbr`bs0`,bc_state_component_equality])) >>
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
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x]` >>
    first_x_assum (qspecl_then [`bc0`,`bs with code := ls0`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bvs` strip_assume_tac) >>
    qexists_tac `bvs` >>
    reverse (rw[]) >- (
      rfs[] >>
      qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
      match_mp_tac Cenv_bs_append_code >>
      rw[bc_state_component_equality] >>
      srw_tac[QUANT_INST_ss[std_qp]][] >>
      `∃ls1. ls0 = bs0.code ++ ls1` by (
        rw[Abbr`ls0`] >>
        Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
        `cs0.out = cs.out` by rw[Abbr`cs0`] >>
        rw[Abbr`bs0`] >>
        metis_tac[FOLDL_compile_append_out,REVERSE_APPEND,APPEND_ASSOC] ) >>
      qexists_tac `ls1 ++ [x]` >>
      rw[] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac `bs0` >>
      rw[bc_state_component_equality,Abbr`bs0`] )
    >- (
      fs[EVERY2_EVERY] >>
      match_mp_tac (GEN_ALL (MP_CANON MONO_EVERY)) >>
      qmatch_assum_abbrev_tac `EVERY P (ZIP (vs,bvs))` >>
      qexists_tac `P` >>
      simp[FORALL_PROD] >>
      rw[Abbr`P`] >>
      qmatch_assum_abbrev_tac `Cv_bv pp X Y` >>
      match_mp_tac Cv_bv_l2a_mono >>
      qexists_tac `pp` >> rw[Abbr`pp`] >>
      metis_tac[bc_find_loc_aux_append_code] ) >>
    qmatch_assum_abbrev_tac `bc_next^* bs0 bs05` >>
    `bc_next^* bs (bs05 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac [`bs0`,`bs05`] >>
      rw[bc_state_component_equality,Abbr`bs0`,Abbr`bs05`] ) >>
    map_every qunabbrev_tac[`bs0`,`bs05`] >>
    rw[Once RTC_CASES2] >> disj2_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs0` >>
    qexists_tac `bs0` >> rw[] >>
    `bc_fetch bs0 = SOME x` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac [`ls0`,`[]`] >>
      unabbrev_all_tac >> rw[] ) >>
    rw[bc_eval1_thm] >>
    rw[bc_eval1_def,Abbr`x`,bump_pc_def] >>
    fs[EVERY2_EVERY,Cevaluate_list_with_Cevaluate,Cevaluate_list_with_EVERY] >>
    srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs0`] >>
    unabbrev_all_tac >>
    srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
    rw[bc_state_component_equality] >>
    metis_tac[TAKE_LENGTH_APPEND,REVERSE_REVERSE
             ,DROP_LENGTH_APPEND,LENGTH_REVERSE]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[DNF_ss][Once Cv_bv_cases] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x]` >>
    first_x_assum (qspecl_then [`bc0`,`bs with code := ls0`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bv` strip_assume_tac) >>
    rfs[] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac `bc_next^* bs0 bs05` >>
      `bc_next^* bs (bs05 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac [`bs0`,`bs05`] >>
        rw[bc_state_component_equality,Abbr`bs0`,Abbr`bs05`] ) >>
      map_every qunabbrev_tac[`bs0`,`bs05`] >>
      rw[Once RTC_CASES2] >> disj2_tac >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qexists_tac `bs0` >> rw[] >>
      `bc_fetch bs0 = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        map_every qexists_tac [`ls0`,`[]`] >>
        unabbrev_all_tac >> rw[] ) >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      fs[Once Cv_bv_cases] >>
      rw[bump_pc_def] >>
      rw[bc_eval_stack_def,Abbr`bs0`] >>
      unabbrev_all_tac >>
      srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
      rw[bc_state_component_equality] >>
      AP_TERM_TAC >> rw[EQ_IMP_THM] ) >>
    qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
    `Cenv_bs c env cs.env cs.sz bs` by (
      match_mp_tac Cenv_bs_append_code >>
      qexists_tac `bs0` >>
      rw[Abbr`bs0`,bc_state_component_equality,Abbr`ls0`] >>
      Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
      `cs0.out = cs.out` by rw[Abbr`cs0`] >>
      metis_tac[compile_append_out,REVERSE_APPEND,APPEND_ASSOC] ) >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_sz) >>
    rw[Abbr`cs0`] >>
    match_mp_tac Cenv_bs_imp_incsz >>
    qexists_tac `bs` >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x]` >>
    first_x_assum (qspecl_then [`bc0`,`bs with code := ls0`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bv` strip_assume_tac) >>
    fs[Once (Q.SPECL[`pp`,`CConv m vs`]Cv_bv_cases)] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    qexists_tac `EL n bvs` >>
    rev_full_simp_tac(srw_ss()++DNF_ss)[MEM_ZIP] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs00` >>
      `bc_next^* bs (bs00 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs0`,`bs00`] >>
        rw[bc_state_component_equality,Abbr`bs0`,Abbr`bs00`] ) >>
      map_every qunabbrev_tac [`bs0`,`bs00`] >>
      rw[Once RTC_CASES2] >> disj2_tac >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qexists_tac `bs0` >> rw[] >>
      `bc_fetch bs0 = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        map_every qexists_tac [`ls0`,`[]`] >>
        unabbrev_all_tac >> rw[] ) >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bump_pc_def] >>
      rw[bc_eval_stack_def,Abbr`bs0`] >>
      unabbrev_all_tac >>
      srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
      rw[bc_state_component_equality]) >>
    conj_tac >- (
      match_mp_tac Cv_bv_l2a_mono >>
      first_x_assum (qspec_then `n` mp_tac) >>
      rw[] >>
      qmatch_assum_abbrev_tac `Cv_bv pp (EL n vs) (EL n bvs)` >>
      qexists_tac `pp` >> rw[Abbr`pp`] >>
      metis_tac[bc_find_loc_aux_append_code] ) >>
    qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
    `Cenv_bs c env cs.env cs.sz bs` by (
      match_mp_tac Cenv_bs_append_code >>
      qexists_tac `bs0` >>
      rw[Abbr`bs0`,bc_state_component_equality,Abbr`ls0`] >>
      Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
      `cs0.out = cs.out` by rw[Abbr`cs0`] >>
      metis_tac[compile_append_out,REVERSE_APPEND,APPEND_ASSOC] ) >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_sz) >>
    rw[Abbr`cs0`] >>
    match_mp_tac Cenv_bs_imp_incsz >>
    qexists_tac `bs` >>
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
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x]` >>
    first_x_assum (qspecl_then [`bc0`,`bs with code := ls0`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (Q.X_CHOOSE_THEN `bvs` strip_assume_tac) >>
    fs[EVERY2_EVERY] >>
    `∃bv0 bv1. bvs = [bv0;bv1]` by (
      Cases_on `bvs` >> fs[] >>
      Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
    srw_tac[ARITH_ss][] >>
    qmatch_assum_abbrev_tac `bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac [`bs0`,`bs1`] >>
      rw[bc_state_component_equality,Abbr`bs0`,Abbr`bs1`] ) >>
    map_every qunabbrev_tac[`bs0`,`bs1`] >>
    qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
    qmatch_assum_abbrev_tac `Cv_bv pp v1 bv0` >>
    qspecl_then[`p2`,`v1`,`v2`,`v`,`bs0`,`ls0`,`[]`,`bs.stack`,`bv0`,`bv1`,`pp`]mp_tac prim2_to_bc_thm >>
    fs[Abbr`bs0`] >>
    disch_then (Q.X_CHOOSE_THEN`bv`strip_assume_tac) >>
    qexists_tac `bv` >> fs[] >>
    conj_tac >- (
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs00` >>
      `bc_next^* bs (bs00 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs0`,`bs00`] >>
        rw[bc_state_component_equality,Abbr`bs0`,Abbr`bs00`] ) >>
      map_every qunabbrev_tac [`bs0`,`bs00`] >>
      rw[Once RTC_CASES2] >> disj2_tac >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qexists_tac `bs0` >> rw[] >>
      qmatch_assum_abbrev_tac`bc_next bs1 bs11` >>
      `bs1 = bs0` by ( rw[Abbr`bs0`,Abbr`bs1`] ) >>
      fs[] >>
      qmatch_abbrev_tac `bc_next bs0 bs12` >>
      qsuff_tac `bs11 = bs12` >- metis_tac[bc_eval1_thm,optionTheory.SOME_11] >>
      rw[Abbr`bs11`,Abbr`bs12`] >>
      qmatch_abbrev_tac `bump_pc bs2 = bs1` >>
      `bc_fetch bs2 = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        map_every qexists_tac [`ls0`,`[]`] >>
        unabbrev_all_tac >> rw[] ) >>
      rw[bump_pc_def] >>
      unabbrev_all_tac >>
      srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
      rw[bc_state_component_equality]) >>
    conj_tac >- (
      match_mp_tac Cv_bv_l2a_mono >>
      qexists_tac `pp` >> rw[Abbr`pp`] >>
      metis_tac[bc_find_loc_aux_append_code] ) >>
    qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
    `Cenv_bs c env cs.env cs.sz bs` by (
      match_mp_tac Cenv_bs_append_code >>
      qexists_tac `bs0` >>
      rw[Abbr`bs0`,bc_state_component_equality,Abbr`ls0`] >>
      Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
      `cs0.out = cs.out` by rw[Abbr`cs0`] >>
      metis_tac[compile_append_out,REVERSE_APPEND,APPEND_ASSOC] ) >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qspecl_then[`compile cs0 e1`,`e2`]mp_tac(CONJUNCT1 compile_sz) >>
    rw[Abbr`cs0`] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_sz) >>
    rw[Abbr`cs0`] >>
    match_mp_tac Cenv_bs_imp_incsz >>
    qexists_tac `bs` >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >>
    rpt strip_tac >>
    rw[LET_THM] >> fs[] >>
    fs[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_state_sz_fupd (K ((compile cs0 e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_state_sz_fupd (K ((compile cs2 e2).sz - 1)) Y` >>
    qabbrev_tac`nl = (compile cs0 exp).next_label` >>
    qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be1`strip_assume_tac) >>
    qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be2`strip_assume_tac) >>
    qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be3`strip_assume_tac) >>
    qmatch_assum_abbrev_tac `bs.code = bc0 ++ REVERSE (compile cs3 e3).out ++ [Label nl2]` >>
    qabbrev_tac`nl1 = nl + 1` >>
    `bs.code = bc0 ++ REVERSE (compile cs0 exp).out ++ ( [JumpIf (Lab nl);Jump(Lab nl1);Label nl]
                   ++ REVERSE be2 ++ [Jump(Lab nl2);Label nl1]
                   ++ REVERSE be3 ++ [Label (nl + 2)])` by (
      rw[] >> rw[Abbr`cs3`] >> rw[Abbr`cs2`] ) >>
    qmatch_assum_abbrev_tac `bs.code = bc0 ++ REVERSE (compile cs0 exp).out ++ bc1` >>
    qabbrev_tac `il = bs.inst_length` >>
    qpat_assum `∀bc0. P` mp_tac >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ bc1` >>
    first_x_assum (qspecl_then [`bc0`,`bs with code := ls0`,`cs0`] mp_tac) >>
    `(cs0.env = cs.env) ∧ (cs0.sz = cs.sz) ∧ (cs0.out = cs.out) ∧ (cs0.next_label = cs.next_label) ∧
     (cs0.ecs = cs.ecs)` by rw[Abbr`cs0`] >>
    simp[] >>
    simp[Once Cv_bv_cases] >>
    strip_tac >>
    qunabbrev_tac`ls0` >>
    qunabbrev_tac`bc1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      rw[Abbr`bs0`,bc_state_component_equality,Abbr`bs1`] ) >>
    map_every qunabbrev_tac[`bs0`,`bs1`] >>
    `ALL_DISTINCT (FILTER is_Label bs.code) ∧
     EVERY (combin$C $< cs3.next_label o dest_Label)
       (FILTER is_Label (bc0 ++ REVERSE cs3.out))` by (
      ntac 8 (pop_assum kall_tac) >>
      rpt (qpat_assum `Cexp_pred X` kall_tac) >>
      rpt (qpat_assum `free_labs X ⊆ Y` kall_tac) >>
      qunabbrev_tac`il` >>
      pop_assum kall_tac >>
      map_every qunabbrev_tac[`nl1`,`nl2`] >>
      rpt (qpat_assum `Cevaluate X Y Z A` kall_tac) >>
      qpat_assum `bs.pc = X` kall_tac >>
      qpat_assum `Cenv_bs X Y Z A B` kall_tac >>
      fs[FILTER_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
      `cs0.next_label = cs.next_label` by rw[Abbr`cs0`] >>
      `cs0.out = cs.out` by rw[Abbr`cs0`] >>
      qspecl_then[`cs0`,`exp`,`FILTER is_Label be1`]mp_tac(CONJUNCT1 compile_next_label) >>
      simp[Once FILTER_APPEND] >> strip_tac >>
      qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
      simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by ( unabbrev_all_tac >> fs[ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE] ) >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[] >> strip_tac >>
      `cs2.next_label = nl + 3` by rw[Abbr`cs2`] >>
      `cs3.next_label = (compile cs2 e2).next_label` by rw[Abbr`cs3`] >>
      qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
      qspecl_then[`cs2`,`e2`,`FILTER is_Label be2`]mp_tac(CONJUNCT1 compile_next_label) >>
      simp[Once FILTER_APPEND] >> strip_tac >>
      qspecl_then[`cs3`,`e3`,`FILTER is_Label be3`]mp_tac(CONJUNCT1 compile_next_label) >>
      simp[Once FILTER_APPEND] >> strip_tac >>
      fs[EVERY_MEM,MEM_MAP,between_def,MEM_FILTER,is_Label_rwt] >>
      fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
      qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_next_label_inc) >> strip_tac >>
      Cases_on `MEM (Label nl) be2` >- (
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label nl) be3` >- (
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label (nl + 1)) be2` >- (
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label (nl + 1)) be3` >- (
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label (nl + 2)) be2` >- (
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label (nl + 2)) be3` >- (
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_next_label_inc) >> strip_tac >>
      rfs[] >>
      Cases_on `MEM (Label nl) be1` >- (
        map_every qunabbrev_tac[`nl`] >>
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label (nl + 1)) be1` >- (
        qunabbrev_tac`nl` >>
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label (nl + 2)) be1` >- (
        qunabbrev_tac`nl` >>
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC ) >>
      Cases_on `MEM (Label nl) cs.out` >- (
        qunabbrev_tac`nl` >>
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC  ) >>
      Cases_on `MEM (Label (nl + 1)) cs.out` >- (
        qunabbrev_tac`nl` >>
        res_tac >> qsuff_tac `F` >> rw[] >> DECIDE_TAC  ) >>
      simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        qunabbrev_tac`P` >>
        fs[Abbr`cs2`,FILTER_APPEND,MEM_FILTER,ALL_DISTINCT_APPEND,is_Label_rwt] >>
        gen_tac >>
        Cases_on `MEM (Label l) be1` >- (
          res_tac >> fs[] >> DECIDE_TAC ) >>
        fs[] >> rw[] >>
        res_tac >>
        TRY (qunabbrev_tac`nl`) >>
        DECIDE_TAC ) >> qunabbrev_tac`P` >> fs[] >>
      map_every qunabbrev_tac[`Q`,`R`] >> strip_tac >>
      qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
      simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        qunabbrev_tac`P` >>
        fs[Abbr`cs3`,FILTER_APPEND,MEM_FILTER] >>
        conj_tac >- rw[Abbr`cs2`] >>
        conj_tac >- DECIDE_TAC >>
        simp[EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
        simp_tac (pure_ss++QUANT_INST_ss[empty_qp]) [] >>
        simp[] >>
        qunabbrev_tac`R` >>
        qabbrev_tac`nl22 = (compile cs2 e2).next_label` >>
        `nl + 3 ≤ nl22` by DECIDE_TAC >>
        qunabbrev_tac`cs2` >> simp[] >> fs[] >>
        metis_tac[LESS_LESS_EQ_TRANS] ) >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
      strip_tac >>
      fs[ALL_DISTINCT_APPEND,ALL_DISTINCT_REVERSE,FILTER_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM] >>
      fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
      qmatch_abbrev_tac`P` >> rw[] >> qunabbrev_tac`P` >>
      simp_tac(srw_ss()++DNF_ss)[GSYM CONJ_ASSOC] >>
      conj_tac >- (
        fs[Abbr`cs3`] >>
        gen_tac >> strip_tac >>
        res_tac >>
        conj_tac >- DECIDE_TAC >>
        conj_tac >- (
          spose_not_then strip_assume_tac >>
          res_tac >> DECIDE_TAC ) >>
        fs[Abbr`cs2`] >>
        conj_tac >- DECIDE_TAC >>
        spose_not_then strip_assume_tac >>
        res_tac >> DECIDE_TAC ) >>
      conj_tac >- (
        rpt strip_tac >>
        res_tac >> DECIDE_TAC ) >>
      conj_tac >- (
        fs[Abbr`cs3`] >>
        rw[Abbr`cs2`] >>
        spose_not_then strip_assume_tac >>
        res_tac >> DECIDE_TAC ) >>
      conj_tac >- (
        rw[Abbr`cs3`,Abbr`cs2`] >>
        spose_not_then strip_assume_tac >>
        res_tac >> DECIDE_TAC ) >>
      conj_tac >- (
        rw[Abbr`cs3`,Abbr`cs2`] >>
        spose_not_then strip_assume_tac >>
        res_tac >> DECIDE_TAC ) >>
      rw[] >>
      res_tac >>
      DECIDE_TAC ) >>
    `cs1.sz = cs.sz + 1` by (
      rw[Abbr`cs1`] >>
      qpat_assum `X = cs.sz` (SUBST1_TAC o SYM) >>
      match_mp_tac (CONJUNCT1 compile_sz) >>
      rw[Abbr`cs0`] ) >>
    `(cs2.env = cs.env) ∧ (cs2.sz = cs.sz) ∧ (cs2.ecs = cs.ecs)` by (
      rw[Abbr`cs2`] >> fs[Abbr`cs1`] ) >>
    Cases_on `b1` >> fs[] >- (
      `∃bc1. bs.code = bc0 ++ REVERSE (compile cs2 e2).out ++ bc1` by (
        rw[Abbr`cs2`] ) >>
      qmatch_assum_abbrev_tac`bs.code = ls0 ++ bc1` >>
      disch_then(qspecl_then[`bc0`,`bs with <|code := ls0; pc := next_addr il (bc0 ++ REVERSE cs2.out)|>`,`cs2`]mp_tac) >>
      simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        conj_tac >- (
          qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
          Q.PAT_ABBREV_TAC`p = next_addr X Y` >>
          `Cenv_bs c env cs.env cs.sz (bs0 with pc := p)` by simp[Cenv_bs_pc] >>
          `∃ls. bc0 ++ REVERSE cs2.out = bs0.code ++ ls` by (
            rw[Abbr`cs2`,Abbr`bs0`] ) >>
          match_mp_tac Cenv_bs_append_code >>
          qexists_tac `bs0 with pc := p` >>
          qexists_tac `ls` >>
          rw[Abbr`bs0`] ) >>
        qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >>
          fs[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,EVERY_REVERSE] ) >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >> simp[] >>
        qspecl_then[`cs0`,`exp`,`FILTER is_Label be1`]mp_tac(CONJUNCT1 compile_next_label) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >> fs[FILTER_APPEND] ) >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >> simp[] >>
        qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
        simp[] >>
        `cs2.next_label = nl + 3` by rw[Abbr`cs2`] >> simp[] >>
        qunabbrev_tac`ls0` >>
        `cs2.out = Label nl::Jump (Lab nl1)::JumpIf (Lab nl)::(be1 ++ cs.out)` by rw[Abbr`cs2`] >>
        fs[FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,
           REVERSE_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,EVERY_MEM,
           MEM_MAP] >>
        full_simp_tac(pure_ss++QUANT_INST_ss[empty_qp])[] >>
        fs[between_def] >>
        rpt strip_tac >>
        res_tac >> DECIDE_TAC ) >>
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      simp[] >>
      disch_then(Q.X_CHOOSE_THEN`b2`strip_assume_tac) >>
      qexists_tac`b2` >>
      qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
      `bc_next^* bs03 (bs05 with code := bs.code)` by (
        rw[RTC_eq_NRC] >>
        qexists_tac `SUC 0` >>
        rw[] >>
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          match_mp_tac bc_fetch_next_addr >>
          qexists_tac`bc0 ++ REVERSE (be1 ++ cs.out)` >>
          rw[Abbr`bs03`,Abbr`ls0`] >> rw[Abbr`cs2`] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`bs03`,LET_THM] >>
        rw[Abbr`bs05`,bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        `∃bc2. ls0 ++ bc1 = (bc0 ++ REVERSE cs2.out) ++ bc2` by (
          rw[Abbr`ls0`] ) >>
        pop_assum SUBST1_TAC >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        rw[Abbr`ls0`,REVERSE_APPEND] >>
        qexists_tac`LENGTH bc0 + LENGTH (be1 ++ cs.out) + 2` >>
        fsrw_tac[ARITH_ss][] >>
        conj_tac >- ( srw_tac[ARITH_ss][Abbr`cs2`] ) >>
        conj_tac >- (
          REWRITE_TAC[Once ADD_SYM] >>
          srw_tac[ARITH_ss][GSYM EL_DROP,Abbr`cs2`,REVERSE_APPEND] >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          rw[DROP_LENGTH_APPEND] >>
          REWRITE_TAC[Once ADD_SYM] >>
          srw_tac[ARITH_ss][GSYM DROP_DROP] >>
          Q.ISPEC_THEN`cs.out`(SUBST1_TAC o SYM)LENGTH_REVERSE >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          REWRITE_TAC[DROP_LENGTH_APPEND] >>
          srw_tac[ARITH_ss][EL_DROP] >>
          REWRITE_TAC[Once ADD_SYM] >>
          srw_tac[ARITH_ss][GSYM EL_DROP] >>
          Q.ISPEC_THEN`be1`(SUBST1_TAC o SYM)LENGTH_REVERSE >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          REWRITE_TAC[DROP_LENGTH_APPEND] >>
          rw[] ) >>
        srw_tac[ARITH_ss][FILTER_APPEND,Abbr`cs2`,SUM_APPEND] >>
        rw[ADD_ASSOC] >>
        srw_tac[ARITH_ss][Once TAKE_SUM] >>
        qabbrev_tac`n = LENGTH bc0 + (LENGTH be1 + LENGTH cs.out)` >>
        qabbrev_tac`ls = bc0 ++ REVERSE (be1 ++ cs.out)` >>
        `n = LENGTH ls` by (
          unabbrev_all_tac >> rw[REVERSE_APPEND] ) >>
        pop_assum SUBST1_TAC >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        REWRITE_TAC[TAKE_LENGTH_APPEND,DROP_LENGTH_APPEND] >>
        rw[FILTER_APPEND,SUM_APPEND] >>
        srw_tac[ARITH_ss][Abbr`ls`,FILTER_APPEND,SUM_APPEND] ) >>
      `bc_next^* (bs05 with code := bs.code) (bs11 with code := bs.code)` by (
        match_mp_tac RTC_bc_next_append_code >>
        map_every qexists_tac[`bs05`,`bs11`] >>
        rw[bc_state_component_equality,Abbr`bs05`,Abbr`bs11`] ) >>
      qabbrev_tac`bs12 = bs11 with code := bs.code` >>
      conj_tac >- (
        qmatch_abbrev_tac`bc_next^* bs bs13` >>
        qunabbrev_tac`ls0` >>
        `bc_fetch bs12 = SOME (Jump (Lab nl2))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp_tac(srw_ss())[Abbr`bs12`] >>
          qmatch_assum_abbrev_tac`bs.code = X ++ [Jump (Lab nl2);Y] ++ A ++ Z` >>
          qexists_tac `X` >>
          qpat_assum `bs.code = X ++ B ++ A ++ Z` SUBST1_TAC >>
          rw[Abbr`bs11`,Abbr`X`,Abbr`cs2`,REVERSE_APPEND] >>
          rpt AP_TERM_TAC >> rw[] ) >>
        `bc_next bs12 bs13` by (
          rw[bc_eval1_thm] >>
          qpat_assum`bs.code = X ++ Y ++ bc1`kall_tac >>
          qmatch_assum_abbrev_tac`bs.code = bsc` >>
          rw[bc_eval1_def,Abbr`bs13`,Abbr`bs12`,Abbr`bs11`] >>
          rw[bc_state_component_equality] >>
          rw[bc_find_loc_def] >>
          match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          rw[] >>
          pop_assum mp_tac >>
          qabbrev_tac`ls = bc0 ++ REVERSE (be3 ++ cs3.out)` >>
          strip_tac >>
          `bs.code = (ls ++ [Label nl2])` by (
            qunabbrev_tac`ls` >> pop_assum mp_tac >> simp[markerTheory.Abbrev_def] ) >>
          qexists_tac `LENGTH ls` >>
          rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
          rw[FILTER_APPEND] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `Cv_bv pp v b2` >>
        match_mp_tac Cv_bv_l2a_mono >>
        qexists_tac `pp` >>
        rw[Abbr`pp`,Abbr`ls0`,REVERSE_APPEND,Abbr`cs3`] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        rw[] ) >>
      qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_sz) >>
      simp[] >> strip_tac >>
      `cs3.sz = cs.sz` by rw[Abbr`cs3`] >>
      `cs3.ecs = cs.ecs` by rw[Abbr`cs3`] >>
      qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_sz) >>
      simp[] >> strip_tac >> fs[] >>
      match_mp_tac Cenv_bs_append_code >>
      Q.PAT_ABBREV_TAC`pc = next_addr il X` >>
      qexists_tac `bs11 with pc := pc` >> rw[Cenv_bs_pc] >>
      rw[Abbr`bs11`,Abbr`ls0`] >>
      rw[bc_state_component_equality] >>
      rw[Abbr`cs3`,REVERSE_APPEND] ) >>
    `bs.code = bc0 ++ REVERSE (compile cs3 e3).out ++ [Label (nl + 2)]` by (
      rw[Abbr`cs3`,Abbr`cs2`] ) >>
    `(cs3.ecs = cs.ecs) ∧ (cs3.env = cs.env)` by rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`] >>
    `cs3.sz = cs.sz` by (
      rw[Abbr`cs3`] >>
      qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_sz) >>
      rw[] ) >>
    qmatch_assum_abbrev_tac`bs.code = ls0 ++ [Label (nl + 2)]` >>
    disch_then(qspecl_then[`bc0`,`bs with <|code:=ls0; pc := next_addr il (bc0 ++ REVERSE cs3.out)|>`,`cs3`]mp_tac) >>
    simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_append_code >>
        qmatch_assum_abbrev_tac `Cenv_bs c env cs.env cs.sz bs0` >>
        qexists_tac `bs0 with pc := next_addr il (bc0 ++ REVERSE cs3.out)` >>
        rw[Cenv_bs_pc] >>
        rw[Abbr`bs0`,bc_state_component_equality] >>
        rw[Abbr`cs3`,Abbr`cs2`] ) >>
      qmatch_abbrev_tac`ALL_DISTINCT (FILTER is_Label ls)` >>
      `∃ls1. bs.code = ls ++ ls1` by (
        rw[Abbr`ls`,Abbr`ls0`] ) >>
      qpat_assum`ALL_DISTINCT (FILTER is_Label bs.code)`mp_tac >>
      pop_assum SUBST1_TAC >>
      rw[FILTER_APPEND,ALL_DISTINCT_APPEND] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> simp[] >>
    disch_then(Q.X_CHOOSE_THEN`b3`strip_assume_tac) >>
    qexists_tac`b3` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs07` >>
    `bc_next^* (bs05 with code := bs.code) (bs07 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs05`,`bs07`] >>
      rw[] >> rw[Abbr`bs05`,Abbr`bs07`,bc_state_component_equality] ) >>
    `bc_next^* bs03 (bs05 with code := bs.code)` by (
      `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs03`,Abbr`ls0`,Abbr`cs3`,Abbr`cs2`] >>
        qexists_tac`bc0 ++ REVERSE cs.out ++ REVERSE be1` >>
        rw[REVERSE_APPEND] ) >>
      rw[RTC_eq_NRC] >>
      qexists_tac`SUC (SUC 0)` >>
      rw[NRC] >>
      rw[bc_eval1_thm] >>
      rw[Once bc_eval1_def] >>
      rw[Abbr`bs03`,LET_THM] >>
      srw_tac[DNF_ss][] >>
      rw[bc_find_loc_def] >>
      rw[LEFT_EXISTS_AND_THM] >- (
        qmatch_abbrev_tac`∃n. X = SOME n` >>
        qsuff_tac `X ≠ NONE` >- (Cases_on`X` >> rw[]) >>
        qunabbrev_tac`X` >>
        match_mp_tac (CONTRAPOS (SPEC_ALL bc_find_loc_aux_NONE)) >>
        rw[Abbr`ls0`,Abbr`cs3`,Abbr`cs2`] ) >>
      qmatch_abbrev_tac`bc_eval1 (bump_pc bs03) = SOME bs06` >>
      `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
        fs[bc_fetch_def,Abbr`bs03`] >> rfs[REVERSE_APPEND] ) >>
      rw[bump_pc_def] >>
      rw[Abbr`bs03`] >>
      qmatch_abbrev_tac`bc_eval1 bs03 = SOME bs06` >>
      `bc_fetch bs03 = SOME (Jump (Lab nl1))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs03`,Abbr`ls0`,Abbr`cs3`,Abbr`cs2`] >>
        qexists_tac`bc0 ++ REVERSE cs.out ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
        rw[REVERSE_APPEND,FILTER_APPEND,SUM_APPEND] >>
        srw_tac[ARITH_ss][] ) >>
      rw[bc_eval1_def] >>
      rw[Abbr`bs03`,Abbr`bs06`,Abbr`bs05`] >>
      rw[bc_state_component_equality] >>
      rw[bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      `ALL_DISTINCT (FILTER is_Label (ls0 ++ [Label nl2]))` by metis_tac[] >>
      rw[] >>
      rw[Abbr`ls0`] >>
      rw[Abbr`cs3`,REVERSE_APPEND] >>
      qexists_tac`1 + LENGTH be2 + LENGTH cs2.out + LENGTH bc0` >>
      conj_tac >- srw_tac[ARITH_ss][] >>
      conj_tac >- (
        srw_tac[ARITH_ss][GSYM EL_DROP] >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        REWRITE_TAC[DROP_LENGTH_APPEND] >>
        Q.ISPEC_THEN`cs2.out`(SUBST1_TAC o SYM)LENGTH_REVERSE >>
        REWRITE_TAC[DROP_LENGTH_APPEND] >>
        Q.ISPEC_THEN`be2`(SUBST1_TAC o SYM)LENGTH_REVERSE >>
        REWRITE_TAC[DROP_LENGTH_APPEND] >>
        rw[] ) >>
      REWRITE_TAC[Once ADD_SYM] >>
      srw_tac[ARITH_ss][Once TAKE_SUM] >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      REWRITE_TAC[DROP_LENGTH_APPEND] >>
      REWRITE_TAC[TAKE_LENGTH_APPEND] >>
      REWRITE_TAC[Once ADD_SYM] >>
      REWRITE_TAC[Once (GSYM ADD_ASSOC)] >>
      qspec_then`LENGTH cs2.out`(fn th=>srw_tac[ARITH_ss][Once th])TAKE_SUM >>
      Q.ISPEC_THEN`cs2.out`(SUBST1_TAC o SYM)LENGTH_REVERSE >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      REWRITE_TAC[DROP_LENGTH_APPEND] >>
      REWRITE_TAC[TAKE_LENGTH_APPEND] >>
      srw_tac[ARITH_ss][TAKE_SUM] >>
      Q.ISPEC_THEN`be2`(SUBST1_TAC o SYM)LENGTH_REVERSE >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      REWRITE_TAC[DROP_LENGTH_APPEND] >>
      REWRITE_TAC[TAKE_LENGTH_APPEND] >>
      rw[FILTER_APPEND] ) >>
    conj_tac >- (
      qmatch_abbrev_tac`bc_next^* bs bs08` >>
      qabbrev_tac`bs09 = bs07 with code := bs.code` >>
      `bs08 = bs09` by (
        rw[Abbr`bs08`,Abbr`bs09`,Abbr`bs07`] >>
        rw[bc_state_component_equality,Abbr`ls0`] >>
        rw[FILTER_APPEND] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    conj_tac >- (
      match_mp_tac Cv_bv_l2a_mono >>
      qmatch_assum_abbrev_tac `Cv_bv pp v b3` >>
      qexists_tac `pp` >>
      rw[Abbr`pp`] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      rfs[Abbr`ls0`] ) >>
    match_mp_tac Cenv_bs_append_code >>
    qexists_tac `bs07` >>
    rw[Abbr`bs07`] >>
    rw[Abbr`ls0`,bc_state_component_equality] >>
    rw[FILTER_APPEND] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    rw[EVERY2_EVERY] >>
    rw[RTC_eq_NRC] >>
    TRY (qexists_tac`0` >>rw[]) >>
    TRY (qmatch_abbrev_tac `Cenv_bs A B C D E` >>
         qmatch_assum_abbrev_tac `Cenv_bs A B C D E'` >>
         match_mp_tac Cenv_bs_append_code >>
         qexists_tac `E'` >>
         unabbrev_all_tac >> rw[] ) >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qabbrev_tac`cs0 = compile cs exp` >>
    qspecl_then[`cs0`,`exps`]mp_tac(FOLDL_compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    first_x_assum(qspecl_then[`v`,`bc0`,`bc0 ++ REVERSE cs.out`,`bs with <|code:=bc0 ++ REVERSE cs0.out|>`,`cs`]mp_tac) >>
    fs[] >>
    disch_then(Q.X_CHOOSE_THEN`bv`(strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM])) >>
    qabbrev_tac`il = bs.inst_length` >>
    qabbrev_tac`bc00 = bc0 ++ REVERSE cs0.out` >>
    first_x_assum(qspecl_then[`bc0`,
      `bs with <|code:=bc0 ++ REVERSE (FOLDL compile cs0 exps).out;pc := next_addr il bc00;stack:=bv::bs.stack|>`,
      `cs0`]mp_tac) >>
    fs[] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      rw[Abbr`bs0`,Abbr`bs1`] >>
      rw[bc_state_component_equality] ) >>
    qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      fs[Abbr`cs0`,Abbr`bc00`] >>
      fs[REVERSE_APPEND] >>
      conj_tac >- (
        fs[FILTER_APPEND] >>
        simp[Once ALL_DISTINCT_APPEND] >>
        qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
        qspecl_then[`cs`,`exp`,`FILTER is_Label be`]mp_tac(CONJUNCT1 compile_next_label) >>
        fs[ALL_DISTINCT_APPEND,FILTER_APPEND,ALL_DISTINCT_REVERSE,FILTER_REVERSE,EVERY_REVERSE] >>
        ntac 2 strip_tac >>
        fsrw_tac[][EVERY_MEM,MEM_FILTER,is_Label_rwt,MEM_MAP,between_def] >>
        fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
        gen_tac >> spose_not_then strip_assume_tac >>
        res_tac >>
        DECIDE_TAC ) >>
      fs[EVERY_MEM,MEM_FILTER,is_Label_rwt] >>
      fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
      qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
      qspecl_then[`cs`,`exp`,`FILTER is_Label be`]mp_tac(CONJUNCT1 compile_next_label) >>
      rw[FILTER_APPEND,between_def,EVERY_MEM,MEM_MAP,MEM_FILTER,is_Label_rwt] >>
      fsrw_tac[QUANT_INST_ss[empty_qp]][] >>
      res_tac >> DECIDE_TAC ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    disch_then(Q.X_CHOOSE_THEN`bvs`(strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM])) >>
    qexists_tac`bv::bvs` >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
    `bs05 = bs1 with code := bs.code` by (
      rw[Abbr`bs05`,Abbr`bs1`,bc_state_component_equality,Abbr`bc00`] ) >>
    simp[LET_THM] >>
    conj_tac >- (
      qmatch_abbrev_tac `bc_next^* bs bs2` >>
      qsuff_tac `bs2 = bs11` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      rw[Abbr`bs2`,Abbr`bs11`,bc_state_component_equality,REVERSE_APPEND] ) >>
    conj_tac >- (
      fs[REVERSE_APPEND] >> rw[] >>
      match_mp_tac Cv_bv_l2a_mono >>
      qmatch_assum_abbrev_tac`Cv_bv pp v bv` >>
      qexists_tac `pp` >> rw[Abbr`pp`] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      rw[] ) >>
    qmatch_abbrev_tac `Cenv_bs c env env0 sz0 bs2` >>
    `bs2 = bs11` by (
      rw[Abbr`bs2`,Abbr`bs11`,bc_state_component_equality,REVERSE_APPEND] ) >>
    rw[] ) >>
  strip_tac >- rw[] >>
  rw[] )

val good_contab_def = Define`
  good_contab (m,w,n) =
    fmap_linv m w`

(* TODO: move *)
val _ = export_rewrites["Compile.cmap_def"]

open MiniMLTheory

val build_rec_env_MAP = store_thm("build_rec_env_MAP",
  ``build_rec_env funs env = MAP (λ(f,x,e). (f, Recclosure env funs f)) funs ++ env``,
  rw[build_rec_env_def] >>
  qho_match_abbrev_tac `FOLDR (f env funs) env funs = MAP (g env funs) funs ++ env` >>
  qsuff_tac `∀funs env env0 funs0. FOLDR (f env0 funs0) env funs = MAP (g env0 funs0) funs ++ env` >- rw[]  >>
  unabbrev_all_tac >> simp[] >>
  Induct >> rw[bind_def] >>
  PairCases_on`h` >> rw[])

val do_app_all_cns = store_thm("do_app_all_cns",
  ``∀(cenv:envC) env op v1 v2 env' exp.
      all_cns v1 ⊆ set (MAP FST cenv) ∧ all_cns v2 ⊆ set (MAP FST cenv) ∧
      BIGUNION (IMAGE all_cns (set (MAP SND env))) ⊆ set (MAP FST cenv) ∧
      (do_app env op v1 v2 = SOME (env',exp))
      ⇒
      BIGUNION (IMAGE all_cns (set (MAP SND env'))) ⊆ set (MAP FST cenv)``,
  ntac 2 gen_tac >> Cases >>
  Cases >> TRY (Cases_on`l`) >>
  Cases >> TRY (Cases_on`l`) >>
  rw[do_app_def] >> rw[] >>
  fs[bind_def] >>
  BasicProvers.EVERY_CASE_TAC >> rw[] >> rw[] >>
  rw[build_rec_env_MAP,MAP_MAP_o,combinTheory.o_DEF,UNCURRY] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[])

val evaluate_all_cns = store_thm("evaluate_all_cns",
  ``∀cenv env exp res. evaluate cenv env exp res ⇒
      (∀v. MEM v (MAP SND env) ⇒ all_cns v ⊆ set (MAP FST cenv)) ⇒
      every_result (λv. all_cns v ⊆ set (MAP FST cenv)) res``,
  ho_match_mp_tac evaluate_nice_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[DNF_ss][MEM_MAP,evaluate_list_with_value] >>
    fs[do_con_check_def] >>
    Cases_on `ALOOKUP cenv cn` >> fs[] >>
    qexists_tac `(cn,x)` >>
    imp_res_tac ALOOKUP_MEM >>
    fs[] >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_MAP] >>
    fsrw_tac[DNF_ss][MEM_EL,SUBSET_DEF] >>
    metis_tac[EL_MAP] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >>
    imp_res_tac ALOOKUP_MEM >>
    fsrw_tac[DNF_ss][MEM_MAP,FORALL_PROD] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[] >> first_x_assum match_mp_tac >> fs[] >>
    qspecl_then[`cenv`,`env`,`op`,`v1`,`v2`,`env'`,`exp''`]mp_tac do_app_all_cns
    fsrw_tac[DNF_ss][SUBSET_DEF] >> metis_tac[]) >>
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
    rw[] >> fs[] >>
    cheat ) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[] >> fs[] >>
    first_x_assum match_mp_tac >>
    rw[bind_def] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- cheat >>
  cheat )

(* TODO: move *)
val syneq_ov = store_thm("syneq_ov",
  ``∀c v1 v2. syneq c v1 v2 ⇒ ∀m. Cv_to_ov m v1 = Cv_to_ov m v2``,
  ho_match_mp_tac syneq_ind >>
  rw[MAP_EQ_EVERY2] >>
  fs[EVERY2_EVERY] >>
  qmatch_assum_abbrev_tac`EVERY P l` >>
  match_mp_tac (MP_CANON MONO_EVERY) >>
  rw[Abbr`P`,UNCURRY])

val repl_exp_val = store_thm("repl_exp_val",
  ``∀cenv env exp v rs rs' bc0 bc bc1 bs bs'.
      exp_pred exp ∧
      evaluate cenv env exp (Rval v) ∧
      EVERY closed (MAP SND env) ∧
      FV exp ⊆ set (MAP FST env) ∧
      (∀v. MEM v (MAP SND env) ⇒ all_cns v ⊆ set (MAP FST cenv)) ∧
      good_cenv cenv ∧
      good_cmap cenv (cmap rs.contab) ∧
      set (MAP FST cenv) ⊆ FDOM (cmap rs.contab) ∧
      good_contab rs.contab ∧
      env_rs env rs FEMPTY bs ∧
      (repl_exp rs exp = (rs',bc)) ∧
      (bs.code = bc0 ++ bc ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      ALL_DISTINCT (FILTER is_Label (bc0 ++ bc1)) ∧
      EVERY (combin$C $< rs.rnext_label o dest_Label) (FILTER is_Label (bc0 ++ bc1))
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
  qho_match_abbrev_tac `∃bv. bc_next^* bs (bs1 bv) ∧ P bv` >>
  qabbrev_tac`bs0 = bs with pc := next_addr bs.inst_length (bc0 ++ (REVERSE cs.out))` >>
  `bc_next^* bs bs0` by (
    rw[RTC_eq_NRC] >>
    qexists_tac `SUC 0` >>
    rw[] >>
    rw[bc_eval1_thm] >>
    qspecl_then[`cs`,`Ce`]mp_tac(CONJUNCT1 compile_append_out) >> strip_tac >>
    qspecl_then[`cs`,`Ce`]mp_tac(CONJUNCT1 compile_next_label) >> strip_tac >>
    qspecl_then[`cs`,`Ce`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >> strip_tac >>
    `bc_fetch bs = SOME (Jump (Lab rs.rnext_label))` by (
      match_mp_tac bc_fetch_next_addr >>
      map_every qexists_tac[`bc0`,`TL (REVERSE (compile cs Ce).out) ++ bc1`] >>
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
  `∃bv. bc_next^* bs0 (bs1 bv) ∧ P bv` by (
    qspecl_then[`Cc`,`Cenv`,`Ce`,`Rval Cv`]mp_tac (CONJUNCT1 compile_val) >>
    fs[] >>
    disch_then (qspecl_then [`bc0`,`bc1`,`bs0`,`cs`] mp_tac) >>
    `Cenv_bs Cc Cenv cs.env cs.sz bs0` by (
      fs[env_rs_def,LET_THM,Cenv_bs_def,Abbr`bs0`,Abbr`Cc`,Abbr`cs`] ) >>
    rw[Abbr`bs0`,LET_THM,Abbr`bs1`] >>
    qexists_tac `bv` >> rw[] >>
    rw[Abbr`P`] >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `Cv_to_ov (FST(SND rs.contab)) (v_to_Cv (cmap rs.contab) v)` >>
    conj_tac >- (
      match_mp_tac EQ_SYM >>
      match_mp_tac (CONJUNCT1 v_to_Cv_ov) >>
      qabbrev_tac`ct=rs.contab` >>
      PairCases_on`ct` >> fs[good_contab_def] >>
      qspecl_then[`cenv`,`env`,`exp`,`Rval v`]mp_tac evaluate_all_cns >>
      fs[good_cmap_def] >>
      fs[SUBSET_DEF] ) >>
    match_mp_tac EQ_TRANS >>
    qexists_tac `Cv_to_ov (FST(SND rs.contab)) Cv` >>
    conj_tac >- (
      match_mp_tac syneq_ov >>
      metis_tac[syneq_sym] ) >>
    match_mp_tac Cv_bv_ov >>
    metis_tac[] ) >>
  metis_tac[RTC_TRANSITIVE,transitive_def])

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
