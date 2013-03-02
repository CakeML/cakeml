open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory rich_listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory arithmeticTheory lcsymtacs quantHeuristicsLib quantHeuristicsLibAbbrev
open MiniMLTerminationTheory miniMLExtraTheory miscTheory compileTerminationTheory intLangTheory bytecodeTerminationTheory evaluateEquationsTheory expToCexpTheory pmatchTheory labelClosuresTheory bytecodeEvalTheory bytecodeExtraTheory
val _ = numLib.prefer_num()
val _ = new_theory "compileCorrectness"

val exp_pred_def = tDefine "exp_pred"`
  (exp_pred (Raise _) = T) ∧
  (exp_pred (Handle _ _ _) = F) ∧
  (exp_pred (Lit _) = T) ∧
  (exp_pred (Con _ es) = EVERY exp_pred es) ∧
  (exp_pred (Var _ _) = T) ∧
  (exp_pred (Fun _ _ _) = F) ∧
  (exp_pred (Uapp _ _) = F) ∧
  (exp_pred (App (Opn _) e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App (Opb _) e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App Equality e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App Opapp e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (App Opassign _ _) = F) ∧
  (exp_pred (Log _ e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (If e1 e2 e3) = exp_pred e1 ∧ exp_pred e2 ∧ exp_pred e3) ∧
  (exp_pred (Mat _ _) = F) ∧
  (exp_pred (Let _ _ _ e1 e2) = exp_pred e1 ∧ exp_pred e2) ∧
  (exp_pred (Letrec _ _ _) = F)`
  (WF_REL_TAC `measure (exp_size ARB)` >>
   srw_tac[ARITH_ss][exp8_size_thm] >>
   Q.ISPEC_THEN`exp_size ARB`imp_res_tac SUM_MAP_MEM_bound >>
   fsrw_tac[ARITH_ss][])
val _ = export_rewrites["exp_pred_def"]

val Cexp_pred_def = tDefine "Cexp_pred"`
  (Cexp_pred (CDecl _) = T) ∧
  (Cexp_pred (CRaise _) = T) ∧
  (Cexp_pred (CHandle _ _ _) = F) ∧
  (Cexp_pred (CVar _) = T) ∧
  (Cexp_pred (CLit _) = T) ∧
  (Cexp_pred (CCon _ es) = EVERY Cexp_pred es) ∧
  (Cexp_pred (CTagEq e _) = Cexp_pred e) ∧
  (Cexp_pred (CProj e _) = Cexp_pred e) ∧
  (Cexp_pred (CLet _ e0 e) = Cexp_pred e0 ∧ Cexp_pred e) ∧
  (Cexp_pred (CLetfun _ _ _ _) = F) ∧
  (Cexp_pred (CFun _ _) = F) ∧
  (Cexp_pred (CCall e es) = Cexp_pred e ∧ EVERY Cexp_pred es) ∧
  (Cexp_pred (CPrim1 _ _) = F) ∧
  (Cexp_pred (CPrim2 _ e1 e2) = Cexp_pred e1 ∧ Cexp_pred e2) ∧
  (Cexp_pred (CUpd _ _) = F) ∧
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

val Cexp_pred_calculate_ldefs = store_thm("Cexp_pred_calculate_ldefs",
  ``∀c ls e. Cexp_pred e ⇒ (calculate_ldefs c ls e = ls)``,
  ho_match_mp_tac calculate_ldefs_ind >>
  rw[calculate_ldefs_def] >> (
  qmatch_abbrev_tac `FOLDL f ls es = ls` >>
  qsuff_tac `($= ls) (FOLDL f ls es)` >- rw[] >>
  ho_match_mp_tac FOLDL_invariant >>
  rw[Abbr`f`] >> match_mp_tac EQ_SYM >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  fs[EVERY_MEM]))

val repl_exp_contab = store_thm("repl_exp_contab",
  ``(repl_exp rs exp = (rs',c)) ==> (rs'.contab = rs.contab)``,
  rw[repl_exp_def,compile_Cexp_def,LET_THM] >>
  qabbrev_tac`p=repeat_label_closures (exp_to_Cexp (cmap rs.contab) exp) rs.rnext_label []` >>
  PairCases_on`p`>>fs[] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> rw[])

val el_check_def = Define`
  el_check n ls = if n < LENGTH ls then SOME (EL n ls) else NONE`
val _ = export_rewrites["el_check_def"]

val lookup_ct_def = Define`
  (lookup_ct cl sz st rs (CTLet n) = if sz < n then NONE else el_check (sz - n) st) ∧
  (lookup_ct cl sz st rs (CTArg n) = el_check (sz + n) st) ∧
  (lookup_ct cl sz st rs (CTEnv n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs => el_check n vs | _ => NONE)) ∧
  (lookup_ct cl sz st rs (CTRef n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs =>
     OPTION_BIND (el_check n vs)
     (λv. case v of RefPtr p => if p ∈ cl then FLOOKUP rs p else NONE | _ => NONE)
     | _ => NONE))`
val _ = export_rewrites["lookup_ct_def"]

val _ = Parse.overload_on("bundle_fvs", ``λc ns defs.
  BIGUNION (IMAGE (λ(xs,cb). cbod_fvs c cb DIFF set xs DIFF set ns) (set defs))``)

val (Cv_bv_rules,Cv_bv_ind,Cv_bv_cases) = Hol_reln`
  (Cv_bv pp (CLitv (IntLit k)) (Number k)) ∧
  (Cv_bv pp (CLitv (Bool b)) (bool_to_val b)) ∧
  (Cv_bv pp (CLitv Unit) unit_val) ∧
  ((FLOOKUP (FST pp) m = SOME p) ⇒ Cv_bv pp (CLoc m) (RefPtr p)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CConv cn vs) (Block (cn+block_tag) bvs)) ∧
  ((pp = (s,c,l2a,cls)) ∧
   (if ns = [] then (i = 0) ∧ (defs = [(xs,INR l)]) else
    (LENGTH defs = LENGTH ns) ∧
    (find_index n ns 0 = SOME i) ∧
    (EL i defs = (xs,INR l))) ∧
   (l2a l = SOME a) ∧
   (FLOOKUP c l = SOME e) ∧
   benv_bvs pp benv (free_vars c e) xs env defs ns i
   ⇒ Cv_bv pp (CRecClos env ns defs n) (Block closure_tag [CodePtr a; benv])) ∧
  ((pp = (s,c,l2a,cls)) ∧
   (evs = FILTER (λv. v ∉ set xs ∧ (∀j. (find_index v ns 0 = SOME j) ⇒ j ≠ i)) (SET_TO_LIST fvs)) ∧
   (benv = if evs = [] then Number 0 else Block 0 bvs) ∧
   (LENGTH bvs = LENGTH evs) ∧
   (∀i x bv. i < LENGTH evs ∧ (x = EL i evs) ∧ (bv = EL i bvs) ⇒
     if find_index x ns 0 = NONE then
       x ∈ FDOM env ∧ Cv_bv pp (env ' x) bv
     else ∃j p jenv. (find_index x ns 0 = SOME j) ∧
       (bv = RefPtr p) ∧
       (FLOOKUP cls p = SOME (jenv,ns,defs,j)) ∧
       fmap_rel (syneq c) jenv (DRESTRICT env (bundle_fvs c ns defs)))
   ⇒ benv_bvs pp benv fvs xs env defs ns i)`

val Cv_bv_only_ind =
  Cv_bv_ind
|> SPEC_ALL
|> UNDISCH
|> CONJUNCT1
|> DISCH_ALL
|> Q.GEN`benv_bvs'`
|> Q.SPEC`K(K(K(K(K(K(K T))))))`
|> SIMP_RULE std_ss []
|> GEN_ALL

val Cv_bv_ov = store_thm("Cv_bv_ov",
  ``∀m pp Cv bv. Cv_bv pp Cv bv ⇒ ∀s. (FST pp = s) ⇒ (Cv_to_ov m s Cv = bv_to_ov m bv)``,
  ntac 2 gen_tac >>
  ho_match_mp_tac Cv_bv_only_ind >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    Cases_on `b` >> fs[] ) >>
  strip_tac >- rw[bv_to_ov_def] >>
  strip_tac >- rw[bv_to_ov_def,FLOOKUP_DEF] >>
  strip_tac >- (
    rw[bv_to_ov_def] >>
    fsrw_tac[ARITH_ss][] >>
    rw[MAP_EQ_EVERY2] >>
    fs[EVERY2_EVERY] ) >>
  rw[bv_to_ov_def])

val v_to_Cv_ov = store_thm("v_to_Cv_ov",
  ``(∀m (v:α v) w s. (all_cns v ⊆ FDOM m) ∧ fmap_linv m w ==> (Cv_to_ov w s (v_to_Cv m v) = v_to_ov s v)) ∧
    (∀m (vs:α v list) w s. (BIGUNION (IMAGE all_cns (set vs)) ⊆ FDOM m) ∧ fmap_linv m w ==> (MAP (Cv_to_ov w s) (vs_to_Cvs m vs) = MAP (v_to_ov s) vs)) ∧
    (∀(m:string|->num) (env:α envE). T)``,
  ho_match_mp_tac v_to_Cv_ind >>
  rw[v_to_Cv_def] >> rw[Cv_to_ov_def] >>
  srw_tac[ETA_ss][fmap_linv_FAPPLY])

val _ = Parse.overload_on("mk_pp", ``λs c bs cls.
  (s
  ,c
  ,combin$C (bc_find_loc_aux bs.code bs.inst_length) 0
  ,cls
  )``)

val good_cls_def = Define`
  good_cls c sm s bs cls =
    FEVERY (λ(p,(env,ns,defs,j)).
      p ∈ FDOM bs.refs ∧
      p ∉ FRANGE sm ∧
      j < LENGTH ns ∧
      Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c bs cls) (CRecClos env ns defs (EL j ns)) (bs.refs ' p))
    cls`

val s_refs_def = Define`
  s_refs c sm cls s bs =
  fmap_rel (Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c bs cls)) s
  (DRESTRICT bs.refs (FRANGE (DRESTRICT sm (FDOM s))))`

val Cenv_bs_def = Define`
  Cenv_bs c sm cls s Cenv (renv:ctenv) sz bs =
    (fmap_rel
       (λCv b. case lookup_ct (FDOM cls) sz bs.stack bs.refs b of NONE => F
             | SOME bv => Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c bs cls) Cv bv)
     Cenv renv) ∧
    s_refs c sm cls s bs`

val env_rs_def = Define`
  env_rs env rs c sm cls s bs =
    let Cenv = alist_to_fmap (env_to_Cenv (cmap rs.contab) env) in
    Cenv_bs c sm cls s Cenv rs.renv rs.rsz bs`

(* TODO: move *)
val SWAP_REVERSE = store_thm("SWAP_REVERSE",
  ``!l1 l2. (l1 = REVERSE l2) = (l2 = REVERSE l1)``,
  SRW_TAC[][EQ_IMP_THM])

val compile_varref_thm = store_thm("compile_varref_thm",
  ``∀bs bc0 code bc1 sz cs b bv bs' cls.
      ((compile_varref sz cs b).out = REVERSE code ++ cs.out) ∧
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (lookup_ct cls sz bs.stack bs.refs b = SOME bv) ∧
      (bs' = bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length (bc0 ++ code)|>)
      ⇒
      bc_next^* bs bs'``,
  ntac 6 gen_tac >> Cases >> rw[] >>
  qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
  qmatch_assum_abbrev_tac `code = x::ls1` >>
  `bc_fetch bs = SOME x` by (
    match_mp_tac bc_fetch_next_addr >>
    map_every qexists_tac [`bc0`,`ls1++bc1`] >>
    rw[Abbr`x`,Abbr`ls1`]) >>
  TRY (
    qmatch_abbrev_tac `bc_next^* bs bs'` >>
    `(bc_eval1 bs = SOME bs')` by (
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,SUM_APPEND,FILTER_APPEND,ADD1,Abbr`ls1`,Abbr`bs'`,bc_state_component_equality] ) >>
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
      ∀cv' bv'. Cv_bv pp cv' bv' ∧
        no_closures cv ∧
        no_closures cv' ∧
        all_Clocs cv ⊆ FDOM (FST pp) ∧
        all_Clocs cv' ⊆ FDOM (FST pp) ∧
        INJ (FAPPLY (FST pp)) (FDOM (FST pp)) (FRANGE (FST pp))
        ⇒ ((cv = cv') = (bv = bv'))``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> rw[]
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    fs[Once Cv_bv_cases] )
  >- (
    rw[EQ_IMP_THM] >> rw[] >>
    Cases_on `b` >>
    fsrw_tac[ARITH_ss][Once Cv_bv_cases] >>
    Cases_on `b` >> fs[])
  >- (
    rw[EQ_IMP_THM] >>
    fs[Once Cv_bv_cases] >>
    fsrw_tac[ARITH_ss][] >>
    Cases_on`b` >> fsrw_tac[ARITH_ss][] )
  >- (
    rw[EQ_IMP_THM] >>
    fs[Once Cv_bv_cases,FLOOKUP_DEF] >> rw[] >>
    fs[INJ_DEF]) >>
  rw[EQ_IMP_THM] >- (
    fs[Once (Q.SPEC`CConv cn vs`(CONJUNCT1 (SPEC_ALL Cv_bv_cases)))] >>
    rw[LIST_EQ_REWRITE] >>
    fs[EVERY2_EVERY] >>
    qpat_assum`LENGTH X = LENGTH bvs` assume_tac >>
    fsrw_tac[DNF_ss][EVERY_MEM,FORALL_PROD,MEM_ZIP] >>
    qpat_assum`LENGTH vs = X` assume_tac >>
    fsrw_tac[DNF_ss][MEM_EL] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
    metis_tac[EL_ZIP] ) >>
  qpat_assum`Cv_bv X Y Z` mp_tac >>
  rw[Once Cv_bv_cases] >>
  fsrw_tac[ARITH_ss][] >>
  TRY (Cases_on `b` >> fsrw_tac[ARITH_ss][]) >>
  fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
  rpt (qpat_assum `LENGTH X = Y` mp_tac) >> rpt strip_tac >>
  fsrw_tac[DNF_ss][MEM_ZIP] >>
  rw[LIST_EQ_REWRITE] >> fsrw_tac[DNF_ss][MEM_EL] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  metis_tac[])

val prim2_to_bc_thm = store_thm("prim2_to_bc_thm",
  ``∀op v1 v2 v bs bc0 bc1 st bv1 bv2 pp.
    (bs.code = bc0 ++ [Stack (prim2_to_bc op)] ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (CevalPrim2 op v1 v2 = Rval v) ∧
    Cv_bv pp v1 bv1 ∧ Cv_bv pp v2 bv2 ∧
    (bs.stack = bv2::bv1::st) ∧
    all_Clocs v1 ⊆ FDOM (FST pp) ∧
    all_Clocs v2 ⊆ FDOM (FST pp) ∧
    INJ (FAPPLY (FST pp)) (FDOM (FST pp)) (FRANGE (FST pp))
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
  TRY (
    fsrw_tac[DNF_ss][INJ_DEF,FLOOKUP_DEF] >>
    AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
    AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
    metis_tac[] ) >>
  Cases_on `m=m'` >> rw[] >>
  AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >> AP_THM_TAC >>
  AP_TERM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  rw[LIST_EQ_REWRITE] >>
  rfs[MEM_ZIP] >>
  fsrw_tac[DNF_ss][MEM_EL] >>
  Cases_on `LENGTH bvs = LENGTH bvs'` >> rw[] >>
  fsrw_tac[DNF_ss][SUBSET_DEF,MEM_EL] >>
  metis_tac[SIMP_RULE(srw_ss()++DNF_ss)[SUBSET_DEF]no_closures_Cv_bv_equal] )

val is_Label_prim1_to_bc = store_thm("is_Label_prim1_to_bc",
  ``∀uop. ¬is_Label (prim1_to_bc uop)``,
  Cases >> rw[])
val _ = export_rewrites["is_Label_prim1_to_bc"]

val compile_varref_next_label_inc = store_thm("compile_varref_next_label_inc",
  ``∀sz cs b. (compile_varref sz cs b).next_label = cs.next_label``,
  ntac 2 gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_next_label_inc"]

val compile_decl_next_label_inc = store_thm("compile_decl_next_label_inc",
  ``∀env1 env0 a vs.(FST (compile_decl env1 env0 a vs)).next_label = (FST a).next_label``,
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
  ``∀d env sz nz cs defs. (compile_closures d env sz nz cs defs).next_label = cs.next_label``,
  rw[compile_closures_def] >>
  `s.next_label = cs.next_label` by (
    qunabbrev_tac`s` >>
    qid_spec_tac `cs` >>
    qid_spec_tac `nz` >>
    Induct >> rw[] >>
    rw[Once num_fold_def] ) >>
  qmatch_assum_abbrev_tac `FOLDL X Y Z = (s'',k')` >>
  `($= s'.next_label o compiler_result_next_label o FST) (FOLDL X Y Z)` by (
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    rw[cons_closure_def,LET_THM,UNCURRY] >>
    Q.PAT_ABBREV_TAC`p = FOLDL (emit_ec env sz) Y Z` >>
    qho_match_abbrev_tac`P p` >>
    qunabbrev_tac`p` >>
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> fs[] >>
    Cases >> Cases >> rw[] ) >>
  pop_assum mp_tac >> rw[] >>
  qabbrev_tac`a = (s'',1)` >>
  qmatch_assum_abbrev_tac `num_fold (update_refptr nk) a nz = b` >>
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
  `($= cs.next_label o compiler_result_next_label o FST) (FOLDL X Y defs)` by (
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

val compile_varref_append_out = store_thm("compile_varref_append_out",
  ``∀sz cs b. ∃bc. ((compile_varref sz cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc)``,
  ho_match_mp_tac compile_varref_ind >> rw[])

val compile_decl_append_out = store_thm("compile_decl_append_out",
  ``∀env1 env0 a vs. ∃bc. ((FST (compile_decl env1 env0 a vs)).out = bc ++ (FST a).out) ∧ (EVERY ($~ o is_Label) bc)``,
  rw[compile_decl_def] >>
  qho_match_abbrev_tac `∃bc. ((FST (FOLDL f a vs)).out = bc ++ (FST a).out) ∧ P bc` >>
  qsuff_tac `(λx. ∃bc. ((FST x).out = bc ++ (FST a).out) ∧ P bc) (FOLDL f a vs)` >- rw[] >>
  match_mp_tac FOLDL_invariant >> rw[Abbr`P`] >>
  PairCases_on `x` >> fs[] >>
  simp[Abbr`f`] >>
  qspecl_then[`x1`,`x0`,`env1 ' y`]mp_tac compile_varref_append_out >>
  rw[] >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val compile_closures_append_out = store_thm("compile_closures_append_out",
  ``∀d env sz nz s defs. ∃bc. ((compile_closures d env sz nz s defs).out = bc ++ s.out) ∧ (EVERY ($~ o is_Label) bc)``,
  rpt gen_tac >>
  qho_match_abbrev_tac`∃bc. P (compile_closures d env sz nz s defs) s bc` >>
  rw[compile_closures_def,LET_THM] >>
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``num_fold``1"f"] >>
  `∃bc. P (num_fold f'' s nz) s bc` by (
    qid_spec_tac `s` >>
    Induct_on `nz` >> rw[Once num_fold_def] >- rw[Abbr`P`] >>
    `∃bc. P (f'' s) s bc` by rw[Abbr`f''`,Abbr`P`] >>
    fs[Abbr`P`] >> metis_tac[APPEND_ASSOC,EVERY_APPEND] ) >>
  qabbrev_tac`p = (FOLDL (push_lab d) (num_fold f'' s nz,[]) defs)` >>
  `(λx. ∃bc. P (FST x) s bc) p` by (
    qunabbrev_tac`p` >>
    match_mp_tac FOLDL_invariant >>
    fs[] >> conj_tac >- PROVE_TAC[] >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    qx_gen_tac`y` >> PairCases_on`y` >>
    Cases_on `y1` >> rw[push_lab_def,LET_THM,Abbr`P`] >>
    fs[]) >>
  PairCases_on `p` >> fs[] >>
  Q.PAT_ABBREV_TAC`q = FOLDL (cons_closure env sz X Y) (p0,1) Z` >>
  `(λx. ∃bc. P (FST x) s bc) q` by(
    qunabbrev_tac`q` >>
    match_mp_tac FOLDL_invariant >>
    fs[] >> conj_tac >- PROVE_TAC[] >>
    Cases >> Cases >>
    simp[cons_closure_def,LET_THM,UNCURRY] >> strip_tac >>
    Q.PAT_ABBREV_TAC `z = FOLDL (emit_ec env sz) Y Z` >>
    qsuff_tac `∃bc. P (SND z) s bc` >- ( rw[Abbr`P`] >> fs[] ) >>
    `(λx. ∃bc. P (SND x) s bc) z` by (
      qunabbrev_tac`z` >>
      match_mp_tac FOLDL_invariant >>
      fs[] >> conj_tac >- fs[Abbr`P`] >>
      Cases >>
      Cases >> rw[] >>
      fs[Abbr`P`] >>
      metis_tac[compile_varref_append_out,APPEND_ASSOC,CONS_APPEND,EVERY_APPEND] ) >>
    fs[Abbr`P`] ) >>
  fs[] >>
  PairCases_on `q` >> fs[] >>
  qabbrev_tac `r = num_fold f (q0,1) nz` >>
  `∃bc. P (FST r) s bc` by (
    qunabbrev_tac`r` >>
    qabbrev_tac`a = (q0,1)` >>
    `∃bca. P (FST a) s bca` by fs[Abbr`a`,Abbr`P`] >>
    pop_assum mp_tac >>
    qid_spec_tac `a` >>
    qid_spec_tac `bca` >>
    qunabbrev_tac`f` >>
    ntac 8 (pop_assum kall_tac) >>
    Induct_on `nz` >> rw[] >>
    rw[Once num_fold_def] >- PROVE_TAC[] >>
    `∃bc. P (FST(update_refptr (LENGTH defs) a)) s bc` by (
      Cases_on `a` >> rw[update_refptr_def,LET_THM] >> fs[Abbr`P`] ) >>
    fs[Abbr`P`]) >>
  Cases_on`r`>>fs[] >>
  qunabbrev_tac`f'` >>
  qmatch_assum_rename_tac`P q s z`[] >>
  pop_assum mp_tac >>
  map_every qid_spec_tac[`z`,`q`,`nz`] >>
  ntac 8 (pop_assum kall_tac) >>
  Induct >> rw[] >> fs[Abbr`P`] >>
  rw[Once num_fold_def])

val _ = Parse.overload_on("retbc",``λj k. [Stack (Pops (k + 1)); Stack (Load 1); Stack (Store (j + 2)); Stack (Pops (j + 1)); Return]``)
val _ = Parse.overload_on("jmpbc",``λn j k. [Stack (Load (n + k + 2)); Stack (Load (n + 1)); Stack (El 1); Stack (Load (n + 2)); Stack (El 0);
                                             Stack (Shift (n + 4) (k + j + 3)); JumpPtr]``)
val _ = Parse.overload_on("callbc",``λn. [Stack (Load n); Stack (El 1); Stack (Load (n + 1)); Stack (El 0); CallPtr]``)

val pushret_append_out = store_thm("pushret_append_out",
  ``∀t s. ∃bc. ((pushret t s).out = bc ++ s.out) ∧ EVERY ($~ o is_Label) bc ∧
   (∀j k. (t = TCTail j k) ⇒ ∃bc0. bc = REVERSE (retbc j k) ++ bc0)``,
  Cases >> rw[pushret_def])

val pushret_next_label = store_thm("pushret_next_label",
  ``∀t s. (pushret t s).next_label = s.next_label``,
  Cases >> rw[pushret_def])
val _ = export_rewrites["pushret_next_label"]

val zero_exists_lemma = store_thm("zero_exists_lemma", ``(∃m. n = m + n) ∧ (∃m. n = n + m)``, rw[]>>qexists_tac`0`>>rw[])

val compile_append_out = store_thm("compile_append_out",
  ``(∀d env t sz cs exp.
      ∃bc. ((compile d env t sz cs exp).out = bc ++ cs.out) ∧
           (∀j k. (t = TCTail j k) ⇒ ((∃m bc0. bc = REVERSE (retbc j (k+m)) ++ bc0) ∨
                                      (∃n m bc0. bc = REVERSE (jmpbc n j (k+m)) ++ bc0))) ∧
           cs.next_label ≤ (compile d env t sz cs exp).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile d env t sz cs exp).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀d env t sz exp n cs xs.
      ∃bc. ((compile_bindings d env t sz exp n cs xs).out = bc ++ cs.out) ∧
           (∀j k. (t = TCTail j k) ⇒ ((∃m bc0. bc = REVERSE (retbc j (k+m)) ++ bc0) ∨
                                      (∃n m bc0. bc = REVERSE (jmpbc n j (k+m)) ++ bc0))) ∧
           cs.next_label ≤ (compile_bindings d env t sz exp n cs xs).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_bindings d env t sz exp n cs xs).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀d env sz cs exps.
      ∃bc. ((compile_nts d env sz cs exps).out = bc ++ cs.out) ∧
           cs.next_label ≤ (compile_nts d env sz cs exps).next_label ∧
           ALL_DISTINCT (FILTER is_Label bc) ∧
           EVERY (between cs.next_label (compile_nts d env sz cs exps).next_label) (MAP dest_Label (FILTER is_Label bc)))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> simp[pushret_def,zero_exists_lemma] >>
    Q.PAT_ABBREV_TAC`p = compile_decl env X Y Z` >>
    PairCases_on `p` >> rw[] >>
    Q.ISPECL_THEN[`env`,`q`,`(cs,sz,r+1,q)`,`vs`]mp_tac compile_decl_append_out >>
    Q.ISPECL_THEN[`env`,`q`,`(cs,sz,r+1,q)`,`vs`]mp_tac compile_decl_next_label_inc >>
    asm_simp_tac std_ss [FST] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    qspecl_then[`sz`,`cs`,`env ' vn`]mp_tac compile_varref_append_out >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fs[FILTER_APPEND] >> rw[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma] ) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> fs[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  strip_tac >- (
    simp[compile_def,LET_THM] >>
    rpt strip_tac >> fs[] >>
    Q.ISPECL_THEN[`d`,`env`,`sz`,`if recp then LENGTH xs else 0`,`cs`,`defs`]strip_assume_tac compile_closures_append_out >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >> rw[] >> fs[]) >>
  strip_tac >- (
    rw[compile_def] >>
    Q.ISPECL_THEN[`d`,`env`,`sz`,`0`,`cs`,`[(xs,cb)]`]strip_assume_tac compile_closures_append_out >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF,FILTER_APPEND] >> rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM,UNCURRY] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    srw_tac[ARITH_ss][] >>
    qexists_tac`0`>>rw[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >> rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[] >>
    SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``pushret``2"s"] >>
    qspecl_then[`t`,`s`]mp_tac(pushret_append_out) >> rw[] >> fs[Abbr`s`] >>
    fs[FILTER_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> fs[zero_exists_lemma]) >>
  strip_tac >- (
    ntac 2 gen_tac >> Cases >> simp[compile_def] >> rw[] >> fs[] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    fs[] >> rw[] >> fs[] >> qexists_tac`n+m`>>simp[]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  rw[compile_def] >> fs[] >>
  fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)

val lookup_ct_incsz = store_thm("lookup_ct_incsz",
  ``(lookup_ct cls (sz+1) (x::st) refs b =
     if (b = CTLet (sz+1)) then SOME x else
     lookup_ct cls sz st refs b)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  rw[SUB,GSYM ADD_SUC])

val lookup_ct_imp_incsz = store_thm("lookup_ct_imp_incsz",
  ``(lookup_ct cls sz st refs b = SOME v) ⇒
    (lookup_ct cls (sz+1) (x::st) refs b = SOME v)``,
  fs[GSYM ADD1] >>
  Cases_on `b` >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  rw[SUB,GSYM ADD_SUC])

val Cenv_bs_imp_incsz = store_thm("Cenv_bs_imp_incsz",
  ``∀c sm cls s env renv rsz bs bs'.
    Cenv_bs c sm cls s env renv rsz bs ∧
    (∃v p e. (bs' = bs with <| stack := v::bs.stack; pc := p; exstack := e |>))
    ⇒
    Cenv_bs c sm cls s env renv (rsz+1) bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT] >> rw[] >> fs[] >- (
    qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
    first_x_assum (qspec_then `z` mp_tac) >>
    BasicProvers.CASE_TAC >>
    imp_res_tac lookup_ct_imp_incsz >>
    rw[] ) >>
  metis_tac[])

val Cenv_bs_imp_decsz = store_thm("Cenv_bs_imp_decsz",
  ``∀c sm cls s env renv rsz bs bs'.
    Cenv_bs c sm cls s env renv (rsz+1) bs ∧
      (CTLet (rsz+1) ∉ FRANGE renv) ∧
      (∃v p e. bs = bs' with <| stack := v::bs'.stack; pc := p; exstack := e |>) ⇒
    Cenv_bs c sm cls s env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT] >> fs[] >- (
    qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
    first_x_assum (qspec_then `z` mp_tac) >>
    BasicProvers.CASE_TAC >>
    pop_assum mp_tac >>
    rw[lookup_ct_incsz] >>
    fs[FRANGE_DEF] >>
    PROVE_TAC[]) >>
  metis_tac[])

val Cenv_bs_CTLet_bound = store_thm("Cenv_bs_CTLet_bound",
  ``Cenv_bs c sm cls s env renv rsz bs ∧ CTLet n ∈ FRANGE renv ⇒ n ≤ rsz``,
  rw[Cenv_bs_def,fmap_rel_def,IN_FRANGE] >>
  qmatch_assum_rename_tac `z ∈ FDOM renv`[] >>
  first_x_assum (qspec_then `z` mp_tac) >>
  `z ∈ FDOM env` by PROVE_TAC[] >> rw[] >>
  fsrw_tac[ARITH_ss][])

val Cenv_bs_pops = store_thm("Cenv_bs_pops",
  ``∀vs c sm cls s env renv rsz bs bs'. Cenv_bs c sm cls s env renv (rsz + LENGTH vs) bs ∧
    (∀n. CTLet n ∈ FRANGE renv ⇒ n ≤ rsz) ∧
    (∃p e. bs = bs' with <| stack := vs ++ bs'.stack; pc := p; exstack := e|>)
    ⇒ Cenv_bs c sm cls s env renv rsz bs'``,
  Induct >> rw[] >- ( fs[Cenv_bs_def,s_refs_def] >> fs[]) >>
  first_x_assum match_mp_tac >>
  simp[bc_state_component_equality] >>
  qexists_tac`bs' with stack := vs ++ bs'.stack` >> rw[] >>
  match_mp_tac Cenv_bs_imp_decsz >>
  qmatch_assum_abbrev_tac`Cenv_bs c sm cls s env renv x y` >>
  qexists_tac`y` >>
  unabbrev_all_tac >>
  fsrw_tac[ARITH_ss][ADD1,bc_state_component_equality] >>
  spose_not_then strip_assume_tac >>
  res_tac >> fsrw_tac[ARITH_ss][] )

val s_refs_with_pc = store_thm("s_refs_with_pc",
  ``s_refs c sm cls s (bs with pc := p) = s_refs c sm cls s bs``,
  rw[s_refs_def])

val s_refs_with_stack = store_thm("s_refs_with_stack",
  ``s_refs c sm cls s (bs with stack := p) = s_refs c sm cls s bs``,
  rw[s_refs_def])

val Cenv_bs_with_pc = store_thm("Cenv_bs_with_pc",
  ``Cenv_bs c sm cls s env env0 sz0 (bs with pc := p) = Cenv_bs c sm cls s env env0 sz0 bs``,
  rw[Cenv_bs_def,s_refs_with_pc])

val Cv_bv_l2a_mono = store_thm("Cv_bv_l2a_mono",
  ``∀pp.
    (∀Cv bv. Cv_bv pp Cv bv ⇒ ∀pp' l2a.
     (∀x y. (FST(SND (SND pp)) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, FST(SND pp), l2a, SND(SND(SND pp))))
     ⇒ Cv_bv pp' Cv bv) ∧
    (∀benv fs xs env defs ns i.
     benv_bvs pp benv fs xs env defs ns i ⇒ ∀pp' l2a.
     (∀x y. (FST(SND (SND pp)) x = SOME y) ⇒ (l2a x = SOME y))
     ∧ (pp' = (FST pp, FST(SND pp), l2a, SND(SND(SND pp))))
     ⇒ benv_bvs pp' benv fs xs env defs ns i)``,
  gen_tac >>
  PairCases_on `pp` >> simp[] >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- (
    rw[] >>
    rw[Once Cv_bv_cases] >>
    fsrw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  strip_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >> strip_tac >>
    simp[Once Cv_bv_cases] >>
    strip_tac >>
    map_every qexists_tac[`e`,`i`,`l`,`xs`] >> simp[] ) >>
  rpt gen_tac >> strip_tac >>
  rw[Once Cv_bv_cases] >>
  fs[LENGTH_NIL] >>
  res_tac >> rw[] >> fs[])

val Cv_bv_l2a_mono_mp = MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_l2a_mono)))

val s_refs_append_code = store_thm("s_refs_append_code",
  ``∀c sm cls s bs bs' ls.
     s_refs c sm cls s bs ∧ (bs' = (bs with code := bs.code ++ ls))
    ⇒ s_refs c sm cls s bs'``,
  rw[s_refs_def,fmap_rel_def] >>
  res_tac >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp (DRESTRICT sm (FDOM s)) c bs cls` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val Cenv_bs_append_code = store_thm("Cenv_bs_append_code",
  ``∀c sm cls s env env0 sz0 bs bs' ls.
    Cenv_bs c sm cls s env env0 sz0 bs ∧ (bs' = (bs with code := bs.code ++ ls)) ⇒
    Cenv_bs c sm cls s env env0 sz0 bs'``,
  reverse(rw[Cenv_bs_def]) >- PROVE_TAC[s_refs_append_code] >>
  fs[Cenv_bs_def,fmap_rel_def,s_refs_def] >> rw[] >>
  res_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  match_mp_tac Cv_bv_l2a_mono_mp >>
  qexists_tac `mk_pp (DRESTRICT sm (FDOM s)) c bs cls` >>
  rw[] >> metis_tac[bc_find_loc_aux_append_code])

val good_ec_def = Define`
  good_ec (n,ls) = (n = LENGTH ls)`

val good_ecs_def = Define`
  good_ecs ecs = FEVERY (good_ec o SND) ecs`

val _ = Parse.overload_on("good_sm",``λsm. INJ (FAPPLY sm) (FDOM sm) (FRANGE sm)``)

val Cenv_bs_FUPDATE = store_thm("Cenv_bs_FUPDATE",
  ``∀c sm cls s env env0 sz0 bs n v bv bs'.
    Cenv_bs c sm cls s env env0 sz0 bs ∧
    Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c bs' cls) v bv ∧
    (bs' = bs with stack := bv::bs.stack)
    ⇒
    Cenv_bs c sm cls s (env |+ (n,v)) (env0 |+ (n,CTLet (sz0 + 1))) (sz0 + 1) bs'``,
  rw[Cenv_bs_def,s_refs_def] >> fs[] >- (
    fs[fmap_rel_def] >>
    qx_gen_tac`x` >>
    Cases_on`x=n`>>fs[] >>
    strip_tac >>
    rw[FAPPLY_FUPDATE_THM] >>
    first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
    Cases_on `lookup_ct (FDOM cls) sz0 bs.stack bs.refs (env0 ' x)` >> fs[] >>
    imp_res_tac lookup_ct_imp_incsz >>
    pop_assum (qspec_then`bv`mp_tac) >> rw[]) >>
  metis_tac[])

val Cenv_bs_DOMSUB = store_thm("Cenv_bs_DOMSUB",
  ``∀c sm cls s env k renv rsz bs.
    Cenv_bs c sm cls s env renv rsz bs ⇒
    Cenv_bs c sm cls s (env \\ k) (renv \\ k) rsz bs``,
  rw[Cenv_bs_def,fmap_rel_def,DOMSUB_FAPPLY_THM])

fun qx_choosel_then [] ttac = ttac
  | qx_choosel_then (q::qs) ttac = Q.X_CHOOSE_THEN q (qx_choosel_then qs ttac)

(* TODO: move *)
val binders_def = tDefine "binders"`
 (binders (CDecl _) = []) ∧
 (binders (CRaise _) = []) ∧
 (binders (CHandle e1 x e2) = binders e1 ++ [x] ++ binders e2) ∧
 (binders (CVar _) = []) ∧
 (binders (CLit _) = []) ∧
 (binders (CCon _ es) = FLAT (MAP binders es)) ∧
 (binders (CTagEq e _) = binders e) ∧
 (binders (CProj e _) = binders e) ∧
 (binders (CLet x e b) = binders e ++ [x] ++ binders b) ∧
 (binders (CLetfun _ ns defs e) = FLAT (MAP (λdef. FST def ++ binders_cb (SND def)) defs) ++ ns ++ binders e) ∧
 (binders (CFun xs cb) = xs ++ binders_cb cb) ∧
 (binders (CCall e es) = FLAT (MAP binders (e::es))) ∧
 (binders (CPrim1 _ e) = binders e) ∧
 (binders (CPrim2 _ e1 e2) = binders e1 ++ binders e2) ∧
 (binders (CUpd e1 e2) = binders e1 ++ binders e2) ∧
 (binders (CIf e1 e2 e3) = binders e1 ++ binders e2 ++ binders e3) ∧
 (binders_cb (INL b) = binders b) ∧
 (binders_cb (INR l) = [])`
(WF_REL_TAC `inv_image $<
  (λx. case x of INL e => Cexp_size e | INR (INL b) => SUC (Cexp_size b) | INR (INR _) => 0)` >>
 srw_tac[ARITH_ss][Cexp4_size_thm,Cexp1_size_thm,Cexp3_size_thm,
                   SUM_MAP_Cexp2_size_thm] >>
 Q.ISPEC_THEN`Cexp_size`imp_res_tac SUM_MAP_MEM_bound >>
 fsrw_tac[ARITH_ss][] >>
 TRY (Cases_on`cb`>>srw_tac[ARITH_ss][basicSizeTheory.sum_size_def]) >>
 qmatch_assum_rename_tac`MEM (a,b) defs`[] >>
 `MEM b (MAP SND defs)` by (rw[MEM_MAP,EXISTS_PROD]>>PROVE_TAC[]) >>
 Q.ISPEC_THEN`Cexp3_size`imp_res_tac SUM_MAP_MEM_bound >>
 Cases_on`b`>>fsrw_tac[ARITH_ss][Cexp3_size_thm,basicSizeTheory.sum_size_def])
val _ = export_rewrites["binders_def"]

val Cv_bv_SUBMAP = store_thm("Cv_bv_SUBMAP",
  ``∀pp.
    (∀v bv. Cv_bv pp v bv ⇒
      ∀s c l2a rfs pp' s'.
        (pp = (s,c,l2a,rfs)) ∧
        (pp' = (s',c,l2a,rfs)) ∧
        (s ⊑ s') ∧
        (∀p. p ∈ FDOM rfs ∧ p ∉ FRANGE s ⇒ p ∉ FRANGE s')
        ⇒
        Cv_bv pp' v bv) ∧
    (∀benv fvs xs env defs ns i. benv_bvs pp benv fvs xs env defs ns i ⇒
      ∀s c l2a rfs pp' s'.
        (pp = (s,c,l2a,rfs)) ∧
        (pp' = (s',c,l2a,rfs)) ∧
        (s ⊑ s') ∧
        (∀p. p ∈ FDOM rfs ∧ p ∉ FRANGE s ⇒ p ∉ FRANGE s')
        ⇒
        benv_bvs pp' benv fvs xs env defs ns i)``,
  gen_tac >> ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- rw[Once Cv_bv_cases,LENGTH_NIL] >>
  strip_tac >- ( rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[FLOOKUP_DEF,SUBMAP_DEF,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] ) >>
  strip_tac >- ( rw[] >> rw[Once Cv_bv_cases,LENGTH_NIL] >>
    fs[FLOOKUP_DEF,SUBMAP_DEF,EVERY2_EVERY,EVERY_MEM,FORALL_PROD,LENGTH_NIL] ) >>
  strip_tac >- ( rw[] >> simp[Once Cv_bv_cases] ) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  simp[Once Cv_bv_cases] >>
  gen_tac >> strip_tac >>
  qexists_tac`bvs`>>fs[]>>
  rpt BasicProvers.VAR_EQ_TAC >>
  Q.PAT_ABBREV_TAC`evs = FILTER X (SET_TO_LIST fvs)` >>
  fs[] >> metis_tac[])

val lookup_ct_change_refs = store_thm("lookup_ct_change_refs",
  ``∀cl sz st rf rf' ct.
    (∀n vs p. (ct = CTRef n) ∧ sz < LENGTH st ∧ (EL sz st = Block 0 vs) ∧ n < LENGTH vs ∧ (EL n vs = RefPtr p) ⇒ (FLOOKUP rf' p = FLOOKUP rf p))
    ⇒ (lookup_ct cl sz st rf' ct = lookup_ct cl sz st rf ct)``,
  rw[LET_THM] >>
  Cases_on`ct`>>fs[] >> rw[] >>
  Cases_on`EL sz st`>>fs[] >>
  rw[]>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[]>>
  BasicProvers.CASE_TAC>>fs[])

val Cenv_bs_change_store = store_thm("Cenv_bs_change_store",
  ``∀c sm cls s env renv rsz bs s' bs' rfs'.
    Cenv_bs c sm cls s env renv rsz bs ∧
    s_refs c sm cls s' bs' ∧
    (bs' = bs with refs := rfs') ∧
    DRESTRICT bs.refs (COMPL (FRANGE (DRESTRICT sm (FDOM s)))) ⊑ DRESTRICT rfs' (COMPL (FRANGE (DRESTRICT sm (FDOM s')))) ∧
    FDOM s ⊆ FDOM s' ∧
    FDOM cls ⊆ FDOM bs.refs ∩ COMPL (FRANGE sm)
    ⇒
    Cenv_bs c sm cls s' env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def] >>
  first_x_assum(qspec_then`x`mp_tac) >> rw[] >>
  qspecl_then[`FDOM cls`,`rsz`,`bs.stack`,`bs.refs`,`rfs'`,`renv ' x`]mp_tac lookup_ct_change_refs >>
  Cases_on`∃n. renv ' x = CTRef n` >- (
    fs[] >> rw[] >> fs[] >> fs[] >>
    Cases_on`EL rsz bs.stack`>>fs[] >>
    qmatch_assum_rename_tac`EL rsz bs.stack = Block m vs`[] >>
    Cases_on`m`>>fs[]>>
    Cases_on`n < LENGTH vs`>>fs[] >>
    Cases_on`EL n vs`>>fs[] >>
    qmatch_assum_rename_tac`EL n vs = RefPtr p`[] >>
    Cases_on`p ∈ FDOM cls`>>fs[]>>
    fs[SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF] >>
    Cases_on`p ∈ FDOM bs.refs`>>fs[] >>
    fs[SUBSET_DEF] >>
    `p ∉ FRANGE (DRESTRICT sm (FDOM s))` by (
      fs[IN_FRANGE,DRESTRICT_DEF] >>
      metis_tac[] ) >>
    fs[] >>
    match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
    simp[] >>
    qexists_tac`DRESTRICT sm (FDOM s)` >>
    fs[SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF,IN_FRANGE] >>
    metis_tac[]) >>
  fs[] >> rw[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[] >>
  match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >>
  simp[] >>
  qexists_tac`DRESTRICT sm (FDOM s)` >>
  fs[SUBMAP_DEF,SUBSET_DEF,DRESTRICT_DEF])

val good_sm_DRESTRICT = store_thm("good_sm_DRESTRICT",
  ``good_sm sm ⇒ good_sm (DRESTRICT sm s)``,
  rw[INJ_DEF,IN_FRANGE,DRESTRICT_DEF] >>
  metis_tac[])

val good_code_env_def = Define`
  good_code_env c d code =
  ALL_DISTINCT (FILTER is_Label code) ∧
  FEVERY (λ(l,e).
    Cexp_pred e ∧
    ALL_DISTINCT (binders e) ∧
    ∃cd cenv cs vs ns xs k bc0 cc bc1.
      (FLOOKUP d l = SOME (vs,xs,ns,k)) ∧
      DISJOINT (set (binders e)) (vs ∪ set ns ∪ set xs) ∧
      (FLOOKUP cd.env_azs l = SOME (cenv,LENGTH xs)) ∧
      good_ecs cd.ecs ∧ free_labs e ⊆ FDOM cd.ecs ∧
      (cenv = FST(ITSET (bind_fv ns xs (LENGTH xs) k) (free_vars c e) (FEMPTY,0,[]))) ∧
      ((compile cd cenv (TCTail (LENGTH xs) 0) 0 cs e).out = cc ++ cs.out) ∧
      EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0) ∧ l < cs.next_label ∧
      (code = bc0 ++ Label l :: (REVERSE cc) ++ bc1)
    ) c`

(*
val good_code_env_append = store_thm("good_code_env_append",
 ``∀c d code ls. good_code_env c d code ⇒ good_code_env c d (code ++ ls)``,
 rw[good_code_env_def,FEVERY_DEF] >>
 res_tac >> rw[] >> metis_tac[APPEND_ASSOC])
val _ = export_rewrites["good_code_env_append"]
*)

val retbc_thm = store_thm("retbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args x st bs'.
    (bs.stack = bv::vs++benv::CodePtr ret::args++x::st) ∧
    (bs.code = bc0 ++ retbc (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs' = bs with <| stack := bv::st; pc := ret |>)
    ⇒ bc_next^* bs bs'``,
  rw[] >>
  qspecl_then[`bc0`,`bs`]mp_tac bc_fetch_next_addr >> simp[] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[DROP_APPEND1,DROP_APPEND2] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  srw_tac[ARITH_ss][ADD1] >>
  rw[bump_pc_def] >>
  lrw[TAKE_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[DROP_APPEND2,DROP_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 (retbc (LENGTH args) (LENGTH vs)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def])

val code = ``jmpbc (LENGTH (args1 :bc_value list)) (LENGTH (args : bc_value list)) (LENGTH (vs : bc_value list))``
val jmpbc_thm = store_thm("jmpbc_thm",
  ``∀bs bc0 bc1 bv vs benv ret args cl ct x y args1 st bs'.
    (bs.stack = args1 ++ (Block ct [CodePtr x;y])::vs++benv::ret::args++cl::st) ∧
    (bs.code = bc0 ++ jmpbc (LENGTH args1) (LENGTH args) (LENGTH vs) ++ bc1) ∧
    (bs.pc = next_addr bs.inst_length bc0) ∧
    (bs' = bs with <| stack := y::ret::args1++(Block ct [CodePtr x;y])::st; pc := x |>)
    ⇒ bc_next^* bs bs'``,
  rw[] >>
  qspecl_then[`bc0`,`bs`]mp_tac bc_fetch_next_addr >> simp[] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND2,EL_APPEND1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND1,EL_APPEND2,EL_CONS] >>
  srw_tac[ARITH_ss][GSYM ADD1] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  srw_tac[ARITH_ss][ADD1] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  lrw[EL_APPEND1,EL_APPEND2,EL_CONS] >>
  REWRITE_TAC[TWO,ONE,Once ADD_SYM,prim_recTheory.PRE] >>
  REWRITE_TAC[Once ADD_SYM] >>
  REWRITE_TAC[GSYM ADD_SUC] >>
  srw_tac[ARITH_ss][] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 5 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp[bc_eval_stack_def] >>
  lrw[TAKE_APPEND2,DROP_APPEND2,TAKE_APPEND1] >>
  rw[bump_pc_def] >>
  ntac 5 (pop_assum kall_tac) >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 6 ^code)`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND,ADD1] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def,Abbr`bs2`] >>
  REWRITE_TAC[GSYM CONS_APPEND,GSYM APPEND_ASSOC] >>
  rw[])

(* TODO: move *)
val EVERY2_THM = store_thm("EVERY2_THM",
  ``(!P ys. EVERY2 P [] ys = (ys = [])) /\
    (!P yys x xs. EVERY2 P (x::xs) yys = ?y ys. (yys = y::ys) /\ (P x y) /\ (EVERY2 P xs ys)) /\
    (!P xs. EVERY2 P xs [] = (xs = [])) /\
    (!P xxs y ys. EVERY2 P xxs (y::ys) = ?x xs. (xxs = x::xs) /\ (P x y) /\ (EVERY2 P xs ys))``,
  REPEAT CONJ_TAC THEN GEN_TAC THEN TRY (
    SRW_TAC[][EVERY2_EVERY,LENGTH_NIL] THEN
    SRW_TAC[][EQ_IMP_THM] THEN NO_TAC ) THEN
  Cases THEN SRW_TAC[][EVERY2_EVERY])
val _ = export_rewrites["EVERY2_THM"]

val REVERSE_INV = store_thm("REVERSE_INV",
  ``!l1 l2. (REVERSE l1 = REVERSE l2) = (l1 = l2)``,
  Induct THEN SRW_TAC[][] THEN
  Cases_on`l2` THEN SRW_TAC[][EQ_IMP_THM])
val _ = export_rewrites["REVERSE_INV"]

val with_same_refs = store_thm("with_same_refs",
  ``(x with refs := x.refs) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_refs"]

val with_same_code = store_thm("with_same_code",
  ``(x with code := x.code) = x``,
  rw[bc_state_component_equality])
val _ = export_rewrites["with_same_code"]

val bc_fetch_with_stack = store_thm("bc_fetch_with_stack",
  ``bc_fetch (s with stack := st) = bc_fetch s``,
  rw[bc_fetch_def])

val option_case_NONE_F = store_thm("option_case_NONE_F",
  ``(case X of NONE => F | SOME x => P x) = (∃x. (X = SOME x) ∧ P x)``,
  Cases_on`X`>>rw[])

val code_for_push_def = Define`
  code_for_push sm cls bs bce bc0 code s s' c env vs renv rsz =
    ∃bvs rf.
    let bs' = bs with <| stack := (REVERSE bvs)++bs.stack; pc := next_addr bs.inst_length (bc0 ++ code); refs := rf |> in
    bc_next^* bs bs' ∧
    EVERY2 (Cv_bv (mk_pp (DRESTRICT sm (FDOM s')) c (bs' with code := bce) cls)) vs bvs ∧
    Cenv_bs c sm cls s' env renv (rsz+(LENGTH vs)) (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (FRANGE (DRESTRICT sm (FDOM s)))) ⊑ DRESTRICT rf (COMPL (FRANGE (DRESTRICT sm (FDOM s')))) ∧
    good_cls c sm s' (bs' with code := bce) cls`

val code_for_return_def = Define`
  code_for_return sm cls bs bce st ret v s s' c =
    ∃bv rf.
    let bs' = bs with <| stack := bv::st; pc := ret; refs := rf |> in
    bc_next^* bs bs' ∧
    Cv_bv (mk_pp (DRESTRICT sm (FDOM s')) c (bs' with code := bce) cls) v bv ∧
    s_refs c sm cls s' (bs' with code := bce) ∧
    DRESTRICT bs.refs (COMPL (FRANGE (DRESTRICT sm (FDOM s)))) ⊑ DRESTRICT rf (COMPL (FRANGE (DRESTRICT sm (FDOM s')))) ∧
    good_cls c sm s' (bs' with code := bce) cls`

val code_for_push_return = store_thm("code_for_push_return",
  ``∀sm cls bs bce bc0 code s s' c env v renv rsz bc1 args args1 bs' blvs benv st cl cl1 ret.
    code_for_push sm cls bs bce bc0 code s s' c env [v] renv rsz ∧
    (bs.code = bc0 ++ code ++ retbc (LENGTH args) (LENGTH blvs) ++ bc1) ∧
    (bs.stack = blvs++benv::CodePtr ret::args++cl::st)
    ⇒
    code_for_return sm cls bs bce st ret v s s' c``,
    rw[code_for_push_def,code_for_return_def,LET_THM] >>
    qmatch_assum_rename_tac `Cv_bv pp v bv`["pp"] >>
    map_every qexists_tac [`bv`,`rf`] >>
    fs[Cenv_bs_def,s_refs_def,good_cls_def] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    qspecl_then[`bs0`,`bs1`,`retbc (LENGTH args) (LENGTH blvs) ++ bc1`]mp_tac (SIMP_RULE(srw_ss())[]RTC_bc_next_append_code) >>
    rw[] >>
    match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
    first_assum (exists_tac o rand o concl) >> fs[Abbr`bs0`] >>
    qpat_assum`bs.code = X`(assume_tac o SYM)>>fs[]>>
    match_mp_tac retbc_thm >>
    pop_assum(assume_tac o SYM) >>
    qexists_tac`bc0 ++ code` >> fs[Abbr`bs1`] >>
    qexists_tac`blvs`>>fs[]>>
    qexists_tac`args`>>fs[])

(*
val code_for_push_jump = store_thm("code_for_push_jump",
  ``∀sm cls bs bce bc0 code s s' c env v renv rsz bc1 args args1 bs' blvs benv st cl cl1 ret.
    code_for_push sm cls bs bce bc0 (code ++ (callbc n)) s s' c env [v] renv rsz ∧
    (bs.code = bc0 ++ code ++ (jmpbc n (LENGTH args) (LENGTH blvs)) ++ bc1) ∧
    (bs.stack = blvs++benv::CodePtr ret::args++cl::st)
    ⇒
    code_for_return sm cls bs bce st ret v s s' c``,
    qspecl_then[`bs0`,`bs1`,`jmpbc (LENGTH args1) (LENGTH args) (LENGTH blvs) ++ bc1`]mp_tac (SIMP_RULE(srw_ss())[]RTC_bc_next_append_code) >>
    rw[] >>
    match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
    first_assum (exists_tac o rand o concl) >> fs[Abbr`bs0`] >>
    qpat_assum`bs.code = X`(assume_tac o SYM)>>fs[]>>

     ((bs.code = bc0 ++ code ++ jmpbc (LENGTH args1) (LENGTH args) (LENGTH blvs) ++ bc1) ∧
      (bs.stack = args1 ++ cl1::blvs++benv::CodePtr ret::args++cl::st)))
*)

val compile_labels_lemma = store_thm("compile_labels_lemma",
  ``∀d env t sz cs exp bc0 cs1 cls1 code.
    (cs1 = compile d env t sz cs exp) ∧
    (cs1.out = REVERSE code ++ cs.out) ∧
    (cls1 = bc0 ++ code) ∧
    ALL_DISTINCT (FILTER is_Label bc0) ∧
    EVERY (combin$C $< cs.next_label o dest_Label)
      (FILTER is_Label bc0)
    ⇒
    ALL_DISTINCT (FILTER is_Label cls1) ∧
    EVERY (combin$C $< cs1.next_label o dest_Label)
      (FILTER is_Label cls1)``,
  rpt gen_tac >> strip_tac >>
  qspecl_then[`d`,`env`,`t`,`sz`,`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
  disch_then(Q.X_CHOOSE_THEN`bc`strip_assume_tac) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fsrw_tac[DNF_ss][FILTER_APPEND,EVERY_MEM,MEM_FILTER,is_Label_rwt,
                   ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,
                   MEM_MAP,between_def] >>
  qpat_assum`bc = REVERSE code`mp_tac >>
  Q.ISPECL_THEN[`bc`,`code`]SUBST1_TAC SWAP_REVERSE >>
  rw[FILTER_REVERSE,ALL_DISTINCT_REVERSE] >>
  spose_not_then strip_assume_tac >>
  res_tac >> DECIDE_TAC)

(* TODO: move *)
val find_index_MEM = store_thm("find_index_MEM",
  ``∀ls x n. ¬MEM x ls = (find_index x ls n = NONE)``,
  Induct >> rw[find_index_def])

val FLOOKUP_DRESTRICT = store_thm("FLOOKUP_DRESTRICT",
  ``!fm s k. FLOOKUP (DRESTRICT fm s) k = if k IN s then FLOOKUP fm k else NONE``,
  SRW_TAC[][FLOOKUP_DEF,DRESTRICT_DEF] THEN FULL_SIMP_TAC std_ss [])

val CARD_REST = store_thm("CARD_REST",
  ``!s. FINITE s /\ s <> {} ==> (CARD (REST s) = CARD s - 1)``,
  SRW_TAC[][] THEN
  IMP_RES_TAC CHOICE_INSERT_REST THEN
  POP_ASSUM (fn th => CONV_TAC (RAND_CONV (REWRITE_CONV [Once(SYM th)]))) THEN
  Q.SPEC_THEN`REST s`MP_TAC CARD_INSERT THEN SRW_TAC[][] THEN
  FULL_SIMP_TAC(srw_ss())[REST_DEF])

val LIST_EQ_MAP_PAIR = store_thm("LIST_EQ_MAP_PAIR",
  ``!l1 l2. (MAP FST l1 = MAP FST l2) /\ (MAP SND l1 = MAP SND l2) ==> (l1 = l2)``,
  SRW_TAC[][MAP_EQ_EVERY2,EVERY2_EVERY,EVERY_MEM,LIST_EQ_REWRITE,FORALL_PROD] THEN
  REV_FULL_SIMP_TAC (srw_ss()++DNF_ss) [MEM_ZIP] THEN
  METIS_TAC[pair_CASES,PAIR_EQ])

val FUPDATE_LIST_ALL_DISTINCT_PERM = store_thm("FUPDATE_LIST_ALL_DISTINCT_PERM",
  ``!ls ls' fm. ALL_DISTINCT (MAP FST ls) /\ PERM ls ls' ==> (fm |++ ls = fm |++ ls')``,
  Induct >> rw[] >>
  fs[sortingTheory.PERM_CONS_EQ_APPEND] >>
  rw[FUPDATE_LIST_THM] >>
  PairCases_on`h` >> fs[] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  match_mp_tac EQ_TRANS >>
  qexists_tac `(fm |++ (M ++ N)) |+ (h0,h1)` >>
  conj_tac >- metis_tac[sortingTheory.ALL_DISTINCT_PERM,sortingTheory.PERM_MAP] >>
  rw[FUPDATE_LIST_APPEND] >>
  `h0 ∉ set (MAP FST N)` by metis_tac[sortingTheory.PERM_MEM_EQ,MEM_MAP,MEM_APPEND] >>
  imp_res_tac FUPDATE_FUPDATE_LIST_COMMUTES >>
  rw[FUPDATE_LIST_THM])

val find_index_LEAST_EL = store_thm("find_index_LEAST_EL",
  ``∀ls x n. find_index x ls n = if MEM x ls then SOME (n + (LEAST n. x = EL n ls)) else NONE``,
  Induct >- rw[find_index_def] >>
  simp[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x`>>fs[] >- (
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- (qexists_tac`0` >> rw[]) >>
    Cases >> rw[] >>
    first_x_assum (qspec_then`0`mp_tac) >> rw[] ) >>
  rw[] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[MEM_EL,MEM] >>
  rw[] >>
  Cases_on`n`>>fs[ADD1] >>
  numLib.LEAST_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >>
  qmatch_rename_tac`m = n`[] >>
  Cases_on`m < n` >- (res_tac >> fs[]) >>
  Cases_on`n < m` >- (
    `n + 1 < m + 1` by DECIDE_TAC >>
    res_tac >> fs[GSYM ADD1] ) >>
  DECIDE_TAC )

val fmap_rel_OPTREL_FLOOKUP = store_thm("fmap_rel_OPTREL_FLOOKUP",
  ``fmap_rel R f1 f2 = ∀k. OPTREL R (FLOOKUP f1 k) (FLOOKUP f2 k)``,
  rw[fmap_rel_def,optionTheory.OPTREL_def,FLOOKUP_DEF,EXTENSION] >>
  PROVE_TAC[])

val syneq_Cv_bv = store_thm("syneq_Cv_bv",
  ``∀c v1 v2. syneq c v1 v2 ⇒ ∀pp bv. (FST(SND pp) = c) ∧ Cv_bv pp v1 bv ⇒ Cv_bv pp v2 bv``,
  ho_match_mp_tac CompileTheory.syneq_strongind >>
  strip_tac >- (
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases] >>
    rw[] >>
    fs[EVERY2_EVERY,EVERY_MEM,UNCURRY] >>
    rpt(qpat_assum`LENGTH X = Y`mp_tac) >>
    ntac 2 strip_tac >>
    fsrw_tac[DNF_ss][MEM_ZIP] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases,SimpR``$==>``] >>
    simp[] >> rw[] >>
    map_every qexists_tac[`e`,`i`,`l`,`xs`] >>
    fs[EVERY_MEM,Once FORALL_PROD] >>
    pop_assum mp_tac >>
    simp[Once Cv_bv_cases] >>
    simp[Once Cv_bv_cases,SimpR``$==>``] >>
    Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars c' e)` >>
    Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
    strip_tac >> qexists_tac`bvs` >> fs[] >>
    qx_gen_tac`z` >> strip_tac >>
    first_x_assum(qspec_then`z`mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on`find_index (EL z evs) ns 0` >> fs[] >- (
      fsrw_tac[DNF_ss][MEM_EL] >>
      first_x_assum(qspecl_then[`xs`,`INR l`,`EL z evs`,`if ns = [] then 0 else i`]mp_tac) >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        unabbrev_all_tac >>
        Cases_on`ns=[]`>>fs[] >>
        imp_res_tac find_index_LESS_LENGTH >>
        fs[] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        `MEM (EL z evs) evs` by (rw[MEM_EL] >> PROVE_TAC[]) >>
        qabbrev_tac`zz = EL z evs` >>
        qunabbrev_tac`evs` >> fs[MEM_FILTER] >>
        `¬MEM zz ns` by (Q.ISPECL_THEN[`ns`,`zz`,`0`]strip_assume_tac find_index_MEM >> fs[]) >>
        fs[MEM_EL,Abbr`fvs`,FLOOKUP_DEF] >> rw[] >>
        metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[optionTheory.OPTREL_def,FLOOKUP_DEF] ) >>
    qho_match_abbrev_tac`fmap_rel R jenv (ev env2)` >>
    qsuff_tac `fmap_rel R (ev env1) (ev env2)` >- metis_tac[fmap_rel_syneq_trans,fmap_rel_syneq_sym] >>
    simp[fmap_rel_OPTREL_FLOOKUP] >>
    fsrw_tac[DNF_ss][MEM_EL,Abbr`ev`,fmap_rel_def,FDOM_DRESTRICT] >>
    qx_gen_tac`k` >>
    Cases_on`ns=[]`>>fs[find_index_def] >>
    srw_tac[DNF_ss][FLOOKUP_DRESTRICT,EXISTS_PROD] >> fs[optionTheory.OPTREL_def] >>
    fs[MEM_EL] >>
    qmatch_assum_rename_tac`(p1,p2) = EL n defs`[] >>
    first_x_assum(qspecl_then[`p1`,`p2`,`k`,`n`]mp_tac) >>
    rfs[] >> rw[] >> fs[]) >>
  simp[Once Cv_bv_cases] >> rw[])

val bind_fv_thm = store_thm("bind_fv_thm",
  ``∀ns xs az i fvs acc env ecl ec. FINITE fvs ∧ (acc = (env,ecl,ec)) ∧ (ns ≠ [] ⇒ i < LENGTH ns) ∧ ALL_DISTINCT ns ⇒
    (ITSET (bind_fv ns xs az i) fvs acc =
     let fvl = SET_TO_LIST fvs in
     let envs = FILTER (λx. ¬MEM x xs ∧ ∀j. (find_index x ns 0 = SOME j) ⇒ j ≠ i) fvl in
     let ecs = MAP (λx. (x, case find_index x ns 0 of NONE => CEEnv x | SOME j => CERef (j + 1))) envs in
     let args = FILTER (λx. MEM x xs) fvl in
     let ls1 = ZIP (args, MAP (λfv. CTArg (2 + az - (THE (find_index fv xs 1)))) args) in
     let ls2 = GENLIST (λn. (FST(EL n ecs), (case SND(EL n ecs) of CEEnv _ => CTEnv | CERef _ => CTRef) (ecl + n))) (LENGTH ecs) in
     let env0 = env |++ ls1 |++ ls2 in
     (if ns ≠ [] ∧ EL i ns ∈ fvs ∧ EL i ns ∉ set xs then env0 |+ (EL i ns, CTArg (2 + az)) else env0
     ,ecl + LENGTH ecs
     ,(REVERSE (MAP SND ecs))++ec
     ))``,
  ntac 4 gen_tac >>
  Q.ISPEC_THEN`bind_fv ns xs az i`ho_match_mp_tac(Q.GEN`f`ITSET_IND) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> fs[] >>
  asm_simp_tac std_ss [Once ITSET_def] >>
  Cases_on`fvs = {}` >- rw[LET_THM,FUPDATE_LIST_THM] >>
  fs[bind_fv_def] >>
  Cases_on`find_index (CHOICE fvs) xs 1` >> fs[] >- (
    Cases_on`find_index (CHOICE fvs) ns 0` >> fs[] >- (
      asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
      rw[] >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
      Q.ISPECL_THEN[`ns`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
      reverse conj_asm2_tac >- (
        conj_tac >- (
          simp[Abbr`ecs`,Abbr`ecs'`,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] >>
          srw_tac[ARITH_ss][ADD1] >>
          rw[] >> fs[] >> rfs[] ) >>
        REWRITE_TAC[Once(GSYM REVERSE_DEF)] >>
        REWRITE_TAC[REVERSE_INV] >>
        simp[Abbr`ecs'`,Abbr`ecs`,Abbr`envs'`,Abbr`envs`,Abbr`fvl`,Abbr`fvl'`] >>
        rfs[] ) >>
      rfs[] >>
      `ns ≠ [] ⇒ (EL i ns ∈ REST fvs = EL i ns ∈ fvs)` by (
        rw[REST_DEF,EQ_IMP_THM] >>
        spose_not_then strip_assume_tac >> fs[] >>
        metis_tac[MEM_EL] ) >>
      fs[] >>
      qsuff_tac `env0 = env0'` >- (rw[] >> fs[]) >>
      `ecs = (CHOICE fvs, CEEnv (CHOICE fvs))::ecs'` by (
        match_mp_tac LIST_EQ_MAP_PAIR >>
        conj_tac >- (
          simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
        match_mp_tac (fst(EQ_IMP_RULE(SPEC_ALL REVERSE_INV))) >>
        asm_simp_tac std_ss [MAP,REVERSE_DEF] ) >>
      simp[Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls1'`,Abbr`ls2`,Abbr`ls2'`] >>
      simp[GENLIST_CONS,combinTheory.o_DEF,ADD1,FUPDATE_LIST_THM] >>
      AP_THM_TAC >> AP_TERM_TAC >>
      simp[Abbr`args'`,Abbr`args`,Abbr`fvl`,Abbr`fvl'`] >>
      qmatch_abbrev_tac`(env |++ ls) |+ p = env |+ p |++ ls` >>
      Q.ISPECL_THEN[`p::ls`,`ls++[p]`,`env`]mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
      `ALL_DISTINCT (MAP FST (p::ls))` by (
        qsuff_tac `∃P. MAP FST (p::ls) = FILTER P (SET_TO_LIST fvs)`
          >- metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST] >>
        simp[Once SET_TO_LIST_THM] >>
        rw[Abbr`p`,Abbr`ls`,MAP_ZIP] >>
        qexists_tac`λx. MEM x xs ∨ (x = CHOICE fvs)` >> rw[] >>
        simp[FILTER_EQ] >>
        simp[REST_DEF] ) >>
      simp[sortingTheory.PERM_CONS_EQ_APPEND,FUPDATE_LIST_THM,FUPDATE_LIST_APPEND] >>
      disch_then (match_mp_tac o GSYM) >>
      map_every qexists_tac [`ls`,`[]`] >>
      rw[] ) >>
    Cases_on `x = i` >> fs[] >- (
      asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
      rw[] >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
      Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
      `ns ≠ []` by (Cases_on`ns`>>fs[find_index_def]) >> fs[] >>
      `EL i ns = CHOICE fvs` by (
        Q.ISPECL_THEN[`ns`,`CHOICE fvs`,`0`]mp_tac find_index_LEAST_EL >>
        simp[MEM_EL] >>
        rw[] >>
        numLib.LEAST_ELIM_TAC >>
        rw[] >> metis_tac[] ) >>
      fs[REST_DEF,CHOICE_DEF] >>
      reverse conj_asm2_tac >- (
        simp[Abbr`ecs`,Abbr`ecs'`,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
      `ecs' = ecs` by (
        match_mp_tac LIST_EQ_MAP_PAIR >>
        conj_tac >- (
          simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
        rw[]) >>
      simp[Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls2`,Abbr`ls1'`,Abbr`ls2'`,Abbr`args`,Abbr`args'`,Abbr`fvl`,Abbr`fvl'`] >>
      REWRITE_TAC[GSYM FUPDATE_LIST_APPEND] >>
      qmatch_abbrev_tac`env |+ p |++ ls = (env |++ ls) |+ p` >>
      Q.ISPECL_THEN[`p::ls`,`ls++[p]`,`env`]mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
      `ALL_DISTINCT (MAP FST (p::ls))` by (
        fs[GSYM REST_DEF] >> rfs[Abbr`p`] >>
        `MAP FST ls = FILTER (λx. MEM x xs) (SET_TO_LIST (REST fvs)) ++ FILTER (λx. ¬MEM x xs ∧ find_index x ns 0 ≠ SOME i) (SET_TO_LIST (REST fvs))` by (
          rw[Abbr`ls`,MAP_ZIP,MAP_GENLIST,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`] >>
          rw[LIST_EQ_REWRITE,Abbr`ecs`,EL_MAP] ) >>
        fs[Abbr`envs`,Abbr`envs'`,MEM_FILTER] >>
        simp[ALL_DISTINCT_APPEND,MEM_FILTER] >>
        metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST,FINITE_REST] ) >>
      simp[sortingTheory.PERM_CONS_EQ_APPEND,FUPDATE_LIST_THM,FUPDATE_LIST_APPEND] >>
      disch_then match_mp_tac >>
      map_every qexists_tac [`ls`,`[]`] >>
      rw[] ) >>
    asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
    rw[] >>
    Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
    Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
    `ns ≠ []` by (Cases_on`ns`>>fs[find_index_def]) >> fs[] >>
    `EL i ns ≠ CHOICE fvs` by (
      `x < LENGTH ns ∧ (EL x ns = CHOICE fvs)` by (
        Q.ISPECL_THEN[`ns`,`CHOICE fvs`,`0`]mp_tac find_index_LEAST_EL >>
        rw[MEM_EL] >- (
          numLib.LEAST_ELIM_TAC >>
          conj_tac >- metis_tac[] >>
          rw[] >>
          qmatch_rename_tac`m < LENGTH ns`[] >>
          Cases_on`n < m`>>res_tac>>fs[]>>
          DECIDE_TAC ) >>
        numLib.LEAST_ELIM_TAC >>
        metis_tac[] ) >>
      fs[EL_ALL_DISTINCT_EL_EQ] >>
      metis_tac[] ) >>
    `EL i ns ∈ REST fvs = EL i ns ∈ fvs` by (
      fs[REST_DEF] ) >>
    reverse conj_asm2_tac >- (
      conj_tac >- (
        simp[Abbr`ecs`,Abbr`ecs'`,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] >>
        srw_tac[ARITH_ss][ADD1] >>
        rw[] >> fs[] >> rfs[] ) >>
      REWRITE_TAC[Once(GSYM REVERSE_DEF)] >>
      REWRITE_TAC[REVERSE_INV] >>
      simp[Abbr`ecs'`,Abbr`ecs`,Abbr`envs'`,Abbr`envs`,Abbr`fvl`,Abbr`fvl'`] >>
      rfs[] ) >>
    rfs[] >>
    `ecs = (CHOICE fvs, CERef (x+1))::ecs'` by (
      match_mp_tac LIST_EQ_MAP_PAIR >>
      conj_tac >- (
        simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
      match_mp_tac (fst(EQ_IMP_RULE(SPEC_ALL REVERSE_INV))) >>
      asm_simp_tac std_ss [MAP,REVERSE_DEF] ) >>
    qsuff_tac `env0 = env0'` >- rw[] >>
    simp[Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls1'`,Abbr`ls2`,Abbr`ls2'`] >>
    simp[GENLIST_CONS,combinTheory.o_DEF,ADD1,FUPDATE_LIST_THM] >>
    AP_THM_TAC >> AP_TERM_TAC >>
    simp[Abbr`args'`,Abbr`args`,Abbr`fvl`,Abbr`fvl'`] >>
    qmatch_abbrev_tac`(env |++ ls) |+ p = env |+ p |++ ls2` >>
    Q.ISPECL_THEN[`p::ls`,`ls++[p]`,`env`]mp_tac FUPDATE_LIST_ALL_DISTINCT_PERM >>
    `ALL_DISTINCT (MAP FST (p::ls))` by (
      qsuff_tac `∃P. MAP FST (p::ls) = FILTER P (SET_TO_LIST fvs)`
        >- metis_tac[FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST] >>
      simp[Once SET_TO_LIST_THM] >>
      rw[Abbr`p`,Abbr`ls`,MAP_ZIP,Abbr`ls2`] >>
      qexists_tac`λx. MEM x xs ∨ (x = CHOICE fvs)` >> rw[] >>
      simp[FILTER_EQ] >>
      simp[REST_DEF] ) >>
    simp[sortingTheory.PERM_CONS_EQ_APPEND,FUPDATE_LIST_THM,FUPDATE_LIST_APPEND] >>
    disch_then (match_mp_tac o GSYM) >>
    map_every qexists_tac [`ls`,`[]`] >>
    rw[] ) >>
  asm_simp_tac std_ss [Once SET_TO_LIST_THM,SimpRHS] >>
  rw[] >>
  Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`1`](strip_assume_tac o SYM) find_index_MEM >>
  Q.ISPECL_THEN[`xs`,`CHOICE fvs`,`0`](strip_assume_tac o SYM) find_index_MEM >>
  rfs[] >>
  reverse conj_asm2_tac >- (
    simp[Abbr`ecs'`,Abbr`ecs`,Abbr`envs'`,Abbr`envs`,Abbr`fvl`,Abbr`fvl'`]) >>
  `ns ≠ [] ⇒ (EL i ns ∉ set xs ⇒ (EL i ns ≠ CHOICE fvs))` by (
    strip_tac >>
    spose_not_then strip_assume_tac >> fs[] ) >>
  qsuff_tac `env0 = env0'` >- (
    rw[] >> fs[REST_DEF] ) >>
  `ecs = ecs'` by (
    match_mp_tac LIST_EQ_MAP_PAIR >>
    conj_tac >- (
      simp[Abbr`ecs`,Abbr`ecs'`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`,Abbr`envs'`,Abbr`fvl`,Abbr`fvl'`] ) >>
    rw[] ) >>
  simp_tac std_ss [Abbr`env0`,Abbr`env0'`,Abbr`ls1`,Abbr`ls1'`,Abbr`ls2`,Abbr`ls2'`] >>
  pop_assum SUBST1_TAC >>
  simp[] >>
  simp[GENLIST_CONS,combinTheory.o_DEF,ADD1,FUPDATE_LIST_THM] >>
  AP_THM_TAC >> AP_TERM_TAC >>
  simp[Abbr`args'`,Abbr`args`,Abbr`fvl`,Abbr`fvl'`] >>
  simp[FUPDATE_LIST_THM] )

(* TODO: move*)
val IMAGE_EL_count_LENGTH = store_thm("IMAGE_EL_count_LENGTH",
  ``∀f ls. IMAGE (λn. f (EL n ls)) (count (LENGTH ls)) = IMAGE f (set ls)``,
  rw[EXTENSION,MEM_EL] >> PROVE_TAC[])

val GENLIST_EL_MAP = store_thm("GENLIST_EL_MAP",
  ``!f ls. GENLIST (λn. f (EL n ls)) (LENGTH ls) = MAP f ls``,
  gen_tac >> Induct >> rw[GENLIST_CONS,combinTheory.o_DEF])

val LENGTH_FILTER_LEQ_MONO = store_thm("LENGTH_FILTER_LEQ_MONO",
  ``!P Q. (!x. P x ==> Q x) ==> !ls. (LENGTH (FILTER P ls) <= LENGTH (FILTER Q ls))``,
  rpt gen_tac >> strip_tac >>
  Induct >> rw[] >>
  fsrw_tac[ARITH_ss][] >>
  PROVE_TAC[])

val find_index_ALL_DISTINCT_EL_eq = store_thm("find_index_ALL_DISTINCT_EL_eq",
  ``∀ls. ALL_DISTINCT ls ⇒ ∀x m i. (find_index x ls m = SOME i) =
      ∃j. (i = m + j) ∧ j < LENGTH ls ∧ (x = EL j ls)``,
  rw[EQ_IMP_THM] >- (
    imp_res_tac find_index_LESS_LENGTH >>
    fs[find_index_LEAST_EL] >> srw_tac[ARITH_ss][] >>
    numLib.LEAST_ELIM_TAC >>
    conj_tac >- PROVE_TAC[MEM_EL] >>
    fs[EL_ALL_DISTINCT_EL_EQ] ) >>
  PROVE_TAC[find_index_ALL_DISTINCT_EL])

val ALL_DISTINCT_MEM_ZIP_MAP = store_thm("ALL_DISTINCT_MEM_ZIP_MAP",
  ``!f x ls. ALL_DISTINCT ls ==> (MEM x (ZIP (ls, MAP f ls)) = MEM (FST x) ls /\ (SND x = f (FST x)))``,
  GEN_TAC THEN Cases THEN
  SRW_TAC[][MEM_ZIP,FORALL_PROD] THEN
  SRW_TAC[][EQ_IMP_THM] THEN
  SRW_TAC[][EL_MAP,MEM_EL] THEN
  FULL_SIMP_TAC (srw_ss()) [EL_ALL_DISTINCT_EL_EQ,MEM_EL] THEN
  METIS_TAC[EL_MAP])

val FDOM_bind_fv = store_thm("FDOM_bind_fv",
  ``∀ns xs az i fvs env ecl ec.
      FINITE fvs ∧ (ns ≠ [] ⇒ i < LENGTH ns) ∧ ALL_DISTINCT ns ⇒
      (FDOM (FST(ITSET (bind_fv ns xs az i) fvs (env,ecl,ec))) = FDOM env ∪ fvs)``,
  rpt gen_tac >> strip_tac >>
  qspecl_then[`ns`,`xs`,`az`,`i`,`fvs`,`(env,ecl,ec)`]mp_tac bind_fv_thm >>
  rw[] >>
  rw[Abbr`env0`,FDOM_FUPDATE_LIST,Abbr`ls1`,MAP_ZIP,Abbr`ls2`] >>
  rw[MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH] >>
  rw[EXTENSION,Abbr`args`,MEM_FILTER,Abbr`fvl`,Abbr`ecs`,EXISTS_PROD,MEM_MAP,Abbr`envs`] >>
  rw[EQ_IMP_THM] >> fs[] >>
  Cases_on`MEM x xs`>>fs[] >>
  fs[find_index_ALL_DISTINCT_EL_eq] >>
  metis_tac[])

val Cenv_bs_bind_fv = store_thm("Cenv_bs_bind_fv",
  ``∀c sm cls s env ns xs az i fvs bs
     cenv defs e l vs a benv ret bvs st pp.
    (env = DRESTRICT (extend_rec_env cenv cenv ns defs xs vs) fvs) ∧
    (bs.stack = benv::CodePtr ret::(REVERSE bvs)++(Block closure_tag [CodePtr a;benv])::st) ∧
    (pp = mk_pp (DRESTRICT sm (FDOM s)) c bs cls) ∧
    (fvs = free_vars c e) ∧
    good_cls c sm s bs cls ∧
    benv_bvs pp benv fvs xs cenv defs ns i ∧
    s_refs c sm cls s bs ∧
    ALL_DISTINCT ns ∧
    ALL_DISTINCT xs ∧
    (ns ≠ [] ⇒ i < LENGTH ns ∧ (LENGTH ns = LENGTH defs) ∧ (EL i defs = (xs,INR l))) ∧
    ((ns = []) ⇒ (defs = [(xs,INR l)])) ∧
    (FLOOKUP c l = SOME e) ∧
    (bc_find_loc_aux bs.code bs.inst_length l 0 = SOME a) ∧
    (LENGTH xs = LENGTH vs) ∧
    EVERY2 (Cv_bv pp) vs bvs ∧
    fvs ⊆ FDOM cenv ∪ set ns ∪ set xs ∧
    (az = LENGTH vs)
    ⇒ Cenv_bs c sm cls s env (FST (ITSET (bind_fv ns xs az i) fvs (FEMPTY,0,[]))) 0 bs``,
  rw[Cenv_bs_def] >>
  simp[fmap_rel_def] >>
  conj_asm1_tac >- (
    rw[FDOM_bind_fv,FDOM_extend_rec_env,FDOM_DRESTRICT] >>
    rw[INTER_COMM] >>
    rw[GSYM SUBSET_INTER_ABSORPTION] ) >>
  rfs[FDOM_bind_fv] >> pop_assum (assume_tac o SYM) >>
  qabbrev_tac `fvs = free_vars c e` >>
  `FINITE fvs` by rw[Abbr`fvs`] >>
  qspecl_then[`ns`,`xs`,`LENGTH vs`,`i`,`fvs`,`(FEMPTY,0,[])`]mp_tac bind_fv_thm >>
  rw[] >> simp[] >>
  Cases_on `MEM x args` >- (
    `MEM x xs` by (
      fs[Abbr`args`,Abbr`fvl`,MEM_FILTER] ) >>
    `∃n. (find_index x xs 1 = SOME (n + 1)) ∧ (EL n xs = x)` by (
      simp[find_index_LEAST_EL] >>
      numLib.LEAST_ELIM_TAC >>
      fs[MEM_EL] >> PROVE_TAC[]) >>
    Q.PAT_ABBREV_TAC`env1 = if X then Y else env0` >>
    qho_match_abbrev_tac`P (env1 ' x)` >>
    qsuff_tac`P (env0 ' x)` >- (
      rw[Abbr`env1`,Abbr`P`,FAPPLY_FUPDATE_THM] >>
      rw[] >> fs[] ) >>
    `env0 ' x = (FEMPTY |++ ls1) ' x` by (
      simp[Abbr`env0`] >>
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp_tac std_ss [Abbr`ls2`,MAP_GENLIST,LIST_TO_SET_GENLIST,combinTheory.o_DEF,IMAGE_EL_count_LENGTH]>>
      simp[Abbr`ecs`,FORALL_PROD,Abbr`envs`,Abbr`fvl`,MEM_MAP,MEM_FILTER] ) >>
    pop_assum SUBST1_TAC >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp[RIGHT_EXISTS_AND_THM] >>
    conj_tac >- rw[Abbr`ls1`,FILTER_ALL_DISTINCT,ALL_DISTINCT_SET_TO_LIST,Abbr`fvl`,MAP_ZIP,Abbr`args`] >>
    simp[Abbr`ls1`,MAP_ZIP,Abbr`args`] >>
    Q.PAT_ABBREV_TAC`ls = FILTER X fvl` >>
    `ALL_DISTINCT ls` by rw[Abbr`ls`,FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST] >>
    simp[ALL_DISTINCT_MEM_ZIP_MAP,Abbr`P`] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
    rfs[MEM_ZIP] >> fsrw_tac[DNF_ss][] >>
    simp[DRESTRICT_DEF] >>
    simp[extend_rec_env_def,FOLDL2_FUPDATE_LIST,MAP2_MAP,FST_pair,MAP_ZIP,SND_pair] >>
    Q.PAT_ABBREV_TAC`env2 = FOLDL X cenv ns` >>
    qho_match_abbrev_tac`P ((env2 |++ ZIP (xs,vs)) ' x)` >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp[MAP_ZIP] >>
    simp[MEM_ZIP] >>
    fsrw_tac[DNF_ss][Abbr`P`] >>
    qexists_tac`n`>>simp[]>>
    imp_res_tac find_index_LESS_LENGTH >> rfs[] >>
    Q.PAT_ABBREV_TAC`bv = EL X (benv::Y)` >>
    qsuff_tac`bv = EL n bvs` >- rw[] >>
    rw[Abbr`bv`] >>
    pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[EL_CONS] >>
    srw_tac[ARITH_ss][PRE_SUB1] >>
    `(LENGTH bvs - n) = SUC (LENGTH bvs - n - 1)` by DECIDE_TAC >>
    pop_assum SUBST1_TAC >> simp[] >>
    simp[EL_APPEND1] >>
    simp[EL_REVERSE,GSYM ADD1] ) >>
  `¬MEM x xs` by (
    rfs[Abbr`args`,MEM_FILTER,Abbr`fvl`,MEM_SET_TO_LIST] ) >>
  Cases_on `find_index x ns 0 = SOME i` >- (
    `x = EL i ns` by (
      imp_res_tac find_index_ALL_DISTINCT_EL_eq >> fs[] ) >>
    `ns ≠ []` by (Cases_on `ns` >> fs[find_index_def]) >>
    `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
    fsrw_tac[ARITH_ss][ADD1] >>
    `MEM (EL i ns) ns` by (rw[MEM_EL] >> PROVE_TAC[]) >>
    simp[DRESTRICT_DEF] >>
    simp[extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
    Q.PAT_ABBREV_TAC`env1 = cenv |++ X` >>
    `(env1 |++ ZIP (xs,vs)) ' (EL i ns) = CRecClos cenv ns defs (EL i ns)` by (
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp[MAP_ZIP,Abbr`env1`] >>
      ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp[MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] ) >>
    pop_assum SUBST1_TAC >>
    `LENGTH vs + 2 = SUC(SUC(LENGTH(REVERSE bvs)))` by srw_tac[ARITH_ss][ADD1] >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[EL,TL] >>
    REWRITE_TAC[GSYM APPEND_ASSOC] >>
    simp_tac std_ss [EL_LENGTH_APPEND,NULL,GSYM CONS_APPEND,HD] >>
    simp[Once Cv_bv_cases] ) >>
  Cases_on `MEM x ns` >- (
    `ns ≠ []` by (Cases_on `ns` >> fs[]) >> fs[] >>
    Cases_on `x = EL i ns` >- (
      fs[] >>
      `i < LENGTH ns` by rw[] >>
      imp_res_tac find_index_ALL_DISTINCT_EL >>
      fs[] ) >>
    Q.PAT_ABBREV_TAC`env1 = if X then Y else env0` >>
    qho_match_abbrev_tac`P (env1 ' x)` >>
    qsuff_tac`P (env0 ' x)` >- (
      rw[Abbr`env1`,Abbr`P`,FAPPLY_FUPDATE_THM] ) >>
    simp[Abbr`env1`,Abbr`P`] >>
    `∃jx. find_index x ns 0 = SOME jx` by (
      metis_tac[find_index_MEM,optionTheory.NOT_SOME_NONE,optionTheory.option_CASES] ) >>
    `MEM (x, CERef (jx + 1)) ecs` by (
      simp[Abbr`ecs`,MEM_MAP,Abbr`envs`,MEM_FILTER,Abbr`fvl`] ) >>
    `∃n. (env0 ' x = CTRef n) ∧ n < LENGTH ecs ∧ (EL n ecs = (x, CERef (jx + 1))) ∧ (find_index (EL n envs) ns 0 = SOME jx)` by (
      fs[MEM_EL] >>
      qmatch_assum_rename_tac`m < LENGTH ecs`[] >>
      qexists_tac`m`>>simp[] >>
      simp[Abbr`env0`] >>
      reverse conj_tac >- (
        fs[Abbr`ecs`] >> rfs[EL_MAP] >>
        Cases_on`find_index (EL m envs) ns 0` >> fs[] ) >>
      qabbrev_tac`fm = FEMPTY |++ ls1` >>
      qho_match_abbrev_tac`P ((fm |++ ls2) ' (EL n ns))` >>
      match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp_tac std_ss [Abbr`ls2`,GENLIST_EL_MAP,MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH,Abbr`P`] >>
      conj_tac >- rw[FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST,Abbr`ecs`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`] >>
      simp[] >>
      qexists_tac`m` >>
      qpat_assum`X = EL m ecs`(assume_tac o SYM) >>
      simp[] ) >>
    qpat_assum`benv_bvs pp benv fvs xs cenv defs ns i`mp_tac >>
    `envs ≠ []` by (
      simp[Abbr`envs`,FILTER_EQ_NIL,combinTheory.o_DEF,EXISTS_MEM,Abbr`fvl`] >>
      PROVE_TAC[] ) >>
    simp[CONJUNCT2(SPEC_ALL Cv_bv_cases)] >>
    disch_then(Q.X_CHOOSE_THEN`nvs`strip_assume_tac) >>
    simp[] >>
    `LENGTH ecs = LENGTH envs` by rw[Abbr`ecs`] >> fs[] >>
    first_x_assum(qspec_then`n`mp_tac) >>
    simp[] >>
    disch_then(qx_choosel_then[`p`,`jenv`]strip_assume_tac) >>
    qpat_assum`good_cls c sm s bs cls`(mp_tac o SIMP_RULE(srw_ss())[good_cls_def,FEVERY_DEF]) >>
    disch_then(qspec_then`p`mp_tac) >>
    fs[FLOOKUP_DEF] >>
    simp[DRESTRICT_DEF,extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,MAP2_MAP,MAP_ZIP,FST_pair,SND_pair] >>
    strip_tac >>
    Q.PAT_ABBREV_TAC`env1 = cenv |++ X` >>
    `(env1 |++ ZIP (xs,vs)) ' x = CRecClos cenv ns defs (EL jx ns)` by (
      match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
      simp[MAP_ZIP,Abbr`env1`] >>
      ho_match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp[MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] >>
      imp_res_tac find_index_ALL_DISTINCT_EL_eq >>
      simp[]) >>
    simp[] >>
    match_mp_tac (MP_CANON syneq_Cv_bv) >> simp[] >>
    qexists_tac`CRecClos jenv ns defs (EL jx ns)` >> simp[] >>
    simp[syneq_cases] >>
    fs[fmap_rel_OPTREL_FLOOKUP,EVERY_MEM,FORALL_PROD] >>
    rpt gen_tac >> strip_tac >>
    qx_gen_tac`v` >> strip_tac >>
    first_x_assum(qspec_then`v`mp_tac) >>
    rw[FLOOKUP_DRESTRICT] >>
    fsrw_tac[DNF_ss][EXISTS_PROD,FORALL_PROD] >>
    metis_tac[IN_DIFF] ) >>
  `x ∈ set envs` by (
    rw[MEM_FILTER,Abbr`envs`,Abbr`fvl`] ) >>
  `ns ≠ [] ⇒ (MEM (EL i ns) ns)` by (
    strip_tac >> fs[] >> rw[MEM_EL] >> PROVE_TAC[] ) >>
  Q.PAT_ABBREV_TAC`env1 = if X then Y else env0` >>
  qho_match_abbrev_tac`P (env1 ' x)` >>
  qsuff_tac`P (env0 ' x)` >- (
    rw[Abbr`env1`,Abbr`P`,FAPPLY_FUPDATE_THM] >>
    rw[] >> fs[]) >>
  simp[Abbr`env1`,Abbr`P`] >>
  `find_index x ns 0 = NONE` by (
    Q.ISPECL_THEN[`ns`,`x`,`0`]mp_tac find_index_MEM >> rw[] ) >>
  `MEM (x, CEEnv x) ecs` by (
    simp[Abbr`ecs`,MEM_MAP] ) >>
  `∃n. (env0 ' x = CTEnv n) ∧ n < LENGTH ecs ∧ (EL n ecs = (x, CEEnv x)) ∧ (find_index (EL n envs) ns 0 = NONE) ∧ (x = EL n envs)` by (
    fs[MEM_EL] >>
    qmatch_assum_rename_tac`(x,CEEnv x) = EL m ecs`[] >>
    `m = n` by (
      fs[Abbr`ecs`] >> rfs[EL_MAP] >>
      qsuff_tac `ALL_DISTINCT envs` >-
        (fs[EL_ALL_DISTINCT_EL_EQ] >> PROVE_TAC[])>>
      simp[Abbr`envs`,FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST] ) >>
    qexists_tac`n`>>simp[]>>
    rfs[Abbr`env0`] >>
    qabbrev_tac`fm = FEMPTY |++ ls1` >>
    qho_match_abbrev_tac`P ((fm |++ ls2) ' (EL n envs))` >>
    match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
    simp_tac std_ss [Abbr`ls2`,GENLIST_EL_MAP,MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH,Abbr`P`] >>
    conj_tac >- rw[FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST,Abbr`ecs`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`] >>
    simp[] >>
    qpat_assum`X = EL m ecs`(assume_tac o SYM) >>
    qexists_tac`m`>>simp[]) >>
  simp[] >>
  qpat_assum`benv_bvs pp benv fvs xs cenv defs ns i`mp_tac >>
  `envs ≠ []` by (
    simp[Abbr`envs`,FILTER_EQ_NIL,combinTheory.o_DEF,EXISTS_MEM,Abbr`fvl`] >>
    PROVE_TAC[] ) >>
  simp[CONJUNCT2(SPEC_ALL Cv_bv_cases)] >>
  disch_then(Q.X_CHOOSE_THEN`nvs`strip_assume_tac) >>
  simp[] >>
  `LENGTH ecs = LENGTH envs` by rw[Abbr`ecs`] >> fs[] >>
  first_x_assum(qspec_then`n`mp_tac) >> simp[] >> rw[] >>
  simp[DRESTRICT_DEF,extend_rec_env_def,FOLDL_FUPDATE_LIST,FOLDL2_FUPDATE_LIST,MAP2_MAP,MAP_ZIP,FST_pair,SND_pair] >>
  `EL n envs ∈ FDOM cenv` by (
    fsrw_tac[DNF_ss][SUBSET_DEF] >>
    metis_tac[] ) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`env1 = cenv |++ X` >>
  `(env1 |++ ZIP (xs,vs)) ' (EL n envs) = cenv ' (EL n envs)` by (
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_ZIP,Abbr`env1`] >>
    match_mp_tac EQ_SYM >>
    match_mp_tac FUPDATE_LIST_APPLY_NOT_MEM_matchable >>
    simp[MAP_MAP_o,combinTheory.o_DEF,MEM_MAP,FORALL_PROD] ) >>
  rw[])

val benv_bvs_free_vars_SUBSET = store_thm("benv_bvs_free_vars_SUBSET",
  ``FINITE fvs ∧ benv_bvs pp benv fvs xs env defs ns i ⇒
    fvs ⊆ FDOM env ∪ set ns ∪ set xs``,
  rw[Once Cv_bv_cases,SUBSET_DEF] >>
  Cases_on`MEM x ns`>>fs[] >>
  Cases_on`MEM x xs`>>fs[] >>
  `find_index x ns 0 = NONE` by rw[GSYM find_index_MEM] >>
  qmatch_assum_abbrev_tac`LENGTH bvs = LENGTH (FILTER P fvl)` >>
  `MEM x (FILTER P fvl)`  by (
    rw[MEM_FILTER,Abbr`P`,Abbr`fvl`] ) >>
  pop_assum(strip_assume_tac o SIMP_RULE(srw_ss())[MEM_EL]) >>
  first_x_assum(qspec_then`n`mp_tac) >> rw[])

fun filter_asms P = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o List.rev o List.filter P)

val Cv_bv_not_env = store_thm("Cv_bv_not_env",
  ``∀pp Cv bv. Cv_bv pp Cv bv ⇒ ∀vs. (bv = Block 0 vs) ⇒ (vs = [])``,
  gen_tac >> ho_match_mp_tac Cv_bv_only_ind >> simp[])

val compile_val = store_thm("compile_val",
  ``(∀c d s env exp res. Cevaluate c d s env exp res ⇒
      ∀sm cls s' v cs cd cenv t sz bs bce bcr bc0 code.
        Cexp_pred exp ∧
        DISJOINT (set (binders exp)) (FDOM cenv) ∧ ALL_DISTINCT (binders exp) ∧
        BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s ∧
        BIGUNION (IMAGE all_Clocs (FRANGE s)) ⊆ FDOM s ∧
        (res = (s', Rval v)) ∧
        good_sm sm ∧ FDOM s' ⊆ FDOM sm ∧
        good_cls c sm s (bs with code := bce) cls ∧
        good_ecs cd.ecs ∧ free_labs exp ⊆ FDOM cd.ecs ∧
        (bce ++ bcr = bs.code) ∧ good_code_env c d bce ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (free_vars c exp ⊆ FDOM cenv) ∧
        Cenv_bs c sm cls s (DRESTRICT env (FDOM cenv)) cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (∀code bc1.
        ((compile cd cenv (TCNonTail F) sz cs exp).out = REVERSE code ++ cs.out) ∧
        (bs.code = bc0 ++ code ++ bc1)
       ⇒
       code_for_push sm cls bs bce bc0 code s s' c (DRESTRICT env (FDOM cenv)) [v] cenv sz) ∧
      (∀code bc1 az lz.
        ((compile cd cenv (TCTail az lz) sz cs exp).out = REVERSE code ++ cs.out) ∧
        (bs.code = bc0 ++ code ++ bc1)
        ⇒
        ∀env0 ns defs xs vs klvs blvs benv ret args cl st.
        (az = LENGTH args) ∧ (lz = LENGTH klvs) ∧
        DISJOINT (set (binders exp)) (set (MAP FST klvs)) ∧
        ALL_DISTINCT (MAP FST klvs) ∧
        (env = extend_rec_env env0 env0 ns defs xs vs |++ klvs) ∧
        EVERY2 (Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c (bs with code := bce) cls)) vs args ∧
        EVERY2 (Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c (bs with code := bce) cls)) (MAP SND klvs) blvs ∧
        (bs.stack = blvs++benv::CodePtr ret::(REVERSE args)++cl::st)
        ⇒
        code_for_return sm cls bs bce st ret v s s' c)) ∧
    (∀c d s env exps ress. Cevaluate_list c d s env exps ress ⇒
      ∀sm cls s' vs cs cd cenv t sz bs bce bcr bc0 code bc1.
        EVERY Cexp_pred exps ∧
        DISJOINT (set (FLAT (MAP binders exps))) (FDOM cenv) ∧ ALL_DISTINCT (FLAT (MAP binders exps)) ∧
        BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s ∧
        BIGUNION (IMAGE all_Clocs (FRANGE s)) ⊆ FDOM s ∧
        (ress = (s', Rval vs)) ∧
        good_sm sm ∧ FDOM s' ⊆ FDOM sm ∧
        good_cls c sm s (bs with code := bce) cls ∧
        good_ecs cd.ecs ∧ free_labs_list exps ⊆ FDOM cd.ecs ∧
        (bce ++ bcr = bs.code) ∧ good_code_env c d bce ∧
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (BIGUNION (IMAGE (free_vars c) (set exps)) ⊆ FDOM cenv) ∧
        Cenv_bs c sm cls s (DRESTRICT env (FDOM cenv)) cenv sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (((compile_nts cd cenv sz cs exps).out = REVERSE code ++ cs.out) ⇒
        code_for_push sm cls bs bce bc0 code s s' c (DRESTRICT env (FDOM cenv)) vs cenv sz))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 4 gen_tac >> qx_gen_tac`n` >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >> simp[compile_def,pushret_def] >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      fs[code_for_push_def,Cenv_bs_def,fmap_rel_def,FDOM_DRESTRICT] >>
      first_assum (qspec_then `n` mp_tac) >>
      REWRITE_TAC[Once option_case_NONE_F] >> simp[] >>
      disch_then(Q.X_CHOOSE_THEN`x`strip_assume_tac) >>
      strip_tac >>
      imp_res_tac Cv_bv_not_env >>
      map_every qexists_tac [`[x]`,`bs.refs`] >> rw[s_refs_with_stack] >- (
        match_mp_tac compile_varref_thm >> fs[] >>
        simp[bc_state_component_equality] >>
        metis_tac[])
      >- ( rfs[DRESTRICT_DEF] )
      >- (
        qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
        qmatch_abbrev_tac`X` >>
        first_x_assum (qspec_then `z` mp_tac) >>
        simp[option_case_NONE_F] >> rw[] >>
        qunabbrev_tac`X` >>
        imp_res_tac lookup_ct_imp_incsz >>
        rw[] )
      >- (
        REWRITE_TAC[GSYM BytecodeTheory.bc_state_fupdcanon] >>
        rw[s_refs_with_pc]) >>
      fs[good_cls_def] ) >>
    rw[] >> fs[] >>
    match_mp_tac code_for_push_return >>
    qspecl_then[`sz`,`cs`,`cenv ' n`]strip_assume_tac compile_varref_append_out >> fs[] >>
    first_x_assum(qspec_then`REVERSE bc`mp_tac) >> simp[] >>
    fs[Once SWAP_REVERSE] >> strip_tac >>
    qmatch_assum_abbrev_tac `code_for_push sm cls bs bce bc0 ccode s s c renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >>
    simp[] >>
    qexists_tac `REVERSE args` >> fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      ntac 2 gen_tac >>
      Cases_on`l`>>rw[compile_def,LET_THM,code_for_push_def,pushret_def]>>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = [x]` >>
      `bc_fetch bs = SOME x` by (
        match_mp_tac bc_fetch_next_addr >>
        qexists_tac `bc0` >>
        rw[Abbr`x`]) >> (
      rw[Once Cv_bv_cases] >>
      qexists_tac` bs.refs` >> reverse (rw[]) >-
        fs[good_cls_def] >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        qexists_tac`bs with code := bce` >>
        rw[bc_state_component_equality]  ) >>
      rw[RTC_eq_NRC] >>
      qexists_tac `SUC 0` >>
      rw[NRC] >>
      rw[bc_eval1_thm] >>
      rw[bc_eval1_def,Abbr`x`] >>
      rw[bc_eval_stack_def] >>
      srw_tac[ARITH_ss][bump_pc_def,FILTER_APPEND,SUM_APPEND,ADD1])) >>
    ntac 4 gen_tac >> strip_tac >>
    qspecl_then[`cd`,`cenv`,`TCNonTail F`,`sz`,`cs`,`(CLit l)`]strip_assume_tac(CONJUNCT1 compile_append_out) >> fs[] >>
    fs[Once SWAP_REVERSE] >>
    `∃bc2. code ++ bc1 = REVERSE bc ++ (retbc az lz) ++ bc2` by (
      Cases_on`l`>>fs[compile_def,pushret_def] >> rw[] >> fs[Once SWAP_REVERSE]) >>
    fs[] >> rpt gen_tac >> strip_tac >>
    match_mp_tac code_for_push_return >> simp[] >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 ccode s s c renv v cenv rsz` >>
    map_every qexists_tac [`bc0`,`ccode`,`renv`,`cenv`,`rsz`] >> rw[] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- (
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM,pushret_def] >>
    fsrw_tac[ETA_ss][] >>
    conj_asm1_tac >- (
      qspecl_then[`cd`,`cenv`,`sz`,`cs`,`exps`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT2 (CONJUNCT2 compile_append_out)) >>
      fs[] >>
      disch_then(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum (qspecl_then[`sm`,`cls`,`cs`,`cd`,`cenv`,`sz`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[Abbr`ls0`] >>
      simp[code_for_push_def] >>
      disch_then(qx_choosel_then[`bvs`,`rf`]strip_assume_tac) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      map_every qexists_tac[`rf`,`bvs`] >>
      simp[] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs0 bs05` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05` >>
        fs[Abbr`bs0`,Abbr`bs05`] >>
        qmatch_abbrev_tac`bc_next bs0 bs2` >>
        `bc_fetch bs0 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs0`,Abbr`x`] >>
          qexists_tac`bc0 ++ REVERSE cx` >> rw[] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`,bump_pc_def] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[EVERY2_EVERY] >>
        srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs0`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality] >>
        metis_tac[TAKE_LENGTH_APPEND,REVERSE_REVERSE
                 ,DROP_LENGTH_APPEND,LENGTH_REVERSE]) >>
      reverse conj_tac >- fs[good_cls_def] >>
      qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' denv cenv sz1 bs1` >>
      `Cenv_bs c sm cls s' denv cenv sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_pops >>
        map_every qexists_tac[`REVERSE bvs`,`bs1`] >>
        imp_res_tac Cevaluate_list_LENGTH >>
        fs[] >>
        simp[bc_state_component_equality,Abbr`bs1`] >>
        `LENGTH exps = LENGTH bvs` by fs[EVERY2_EVERY] >> fs[] >>
        PROVE_TAC[Cenv_bs_CTLet_bound,ADD_SYM] ) >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac `bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    ntac 4 gen_tac >> strip_tac >> fs[] >> rw[] >>
    match_mp_tac code_for_push_return >>
    simp[] >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s' c renv v cenv rsz` >>
    map_every qexists_tac[`bc0`,`code`,`renv`,`cenv`,`rsz`] >>
    simp[] >>
    qexists_tac`REVERSE args`>>fsrw_tac[ARITH_ss][EVERY2_EVERY]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    fs[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM] >> fs[REVERSE_APPEND] >>
      qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE |>` >>
      `∃cx. (compile cs0 exp).out = cx ++ cs.out` by (
        qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >> rw[Abbr`cs0`] ) >> fs[] >>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum(qspecl_then[`sm`,`cls`,`cs0`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[code_for_push_def,Abbr`cs0`,Abbr`ls0`] >>
      disch_then(qx_choosel_then[`bv`,`rfs`] mp_tac o CONJUNCT1) >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      srw_tac[DNF_ss][Once Cv_bv_cases] >>
      qexists_tac`rfs` >>
      rfs[compile_sz] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05` >> rw[] >>
        `bc_fetch bs05 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs05`,Abbr`x`] >>
          map_every qexists_tac [`bc0 ++ REVERSE cx`,`bc1`] >> rw[] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bump_pc_def] >>
        rw[bc_eval_stack_def,Abbr`bs05`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality] >>
        AP_TERM_TAC >> rw[EQ_IMP_THM] ) >>
      reverse conj_tac >- fs[good_cls_def] >>
      qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' cenv cs.env sz1 bs1` >>
      `Cenv_bs c sm cls s' cenv cs.env cs.sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac `bs1` >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`sz1`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC ) >>
      qunabbrev_tac`sz1` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := bs.stack` >>
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    first_x_assum(qspec_then`sm` kall_tac) >>
    fs[compile_def,LET_THM] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s' c cenv v cs.env csz` >>
    map_every qexists_tac[`bc0`,`code`,`cenv`,`cs.env`,`csz`] >>
    rw[] >> metis_tac[EVERY2_EVERY,LENGTH_MAP]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    fs[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM] >> fs[REVERSE_APPEND] >>
      qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
      `∃cx. (compile cs0 exp).out = cx ++ cs.out` by (
        qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >> rw[Abbr`cs0`] ) >> fs[] >>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum(qspecl_then[`sm`,`cls`,`cs0`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[code_for_push_def,Abbr`cs0`,Abbr`ls0`] >>
      disch_then(qx_choosel_then[`bv`,`rfs`] mp_tac o CONJUNCT1) >>
      fs[(Q.SPECL[`CConv m vs`](CONJUNCT1 (SPEC_ALL Cv_bv_cases)))] >>
      srw_tac[DNF_ss][] >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      map_every qexists_tac[`rfs`,`EL n bvs`] >>
      rev_full_simp_tac(srw_ss()++DNF_ss)[MEM_ZIP,compile_sz] >>
      conj_tac >- (
        qmatch_assum_abbrev_tac `bc_next^* bs bs05` >>
        rw[Once RTC_CASES2] >> disj2_tac >>
        qexists_tac `bs05` >> rw[] >>
        `bc_fetch bs05 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs05`,Abbr`x`] >>
          map_every qexists_tac [`bc0 ++ REVERSE cx`,`bc1`] >> rw[] ) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`x`] >>
        rw[bump_pc_def] >>
        rw[bc_eval_stack_def,Abbr`bs05`] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] ) >>
      reverse conj_tac >- fs[good_cls_def] >>
      qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' cenv cs.env sz1 bs1` >>
      `Cenv_bs c sm cls s' cenv cs.env cs.sz (bs1 with stack := bs.stack)` by (
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac `bs1` >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`sz1`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC ) >>
      qunabbrev_tac`sz1` >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qexists_tac`bs1 with stack := bs.stack` >>
      simp[bc_state_component_equality,Abbr`bs1`] >>
      first_x_assum(qspec_then`n`mp_tac) >> simp[] >>
      strip_tac >> imp_res_tac Cv_bv_not_env >>
      rw[] >> fs[] >> rw[] >> fs[]) >>
    first_x_assum(qspec_then`sm` kall_tac) >>
    fs[compile_def,LET_THM] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s' c cenv v cs.env csz` >>
    map_every qexists_tac[`bc0`,`code`,`cenv`,`cs.env`,`csz`] >>
    rw[] >> metis_tac[EVERY2_EVERY,LENGTH_MAP]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def] >>
    qspecl_then[`FST(sdt cs)`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    Q.PAT_ABBREV_TAC`cs0 = cs with <| tail := TCNonTail; decl := NONE |>` >>
    reverse(Cases_on`∃bc10. code = REVERSE cx ++ bc10`) >- (
      fsrw_tac[DNF_ss][] >>
      conj_tac >> rpt gen_tac >>
      Q.PAT_ABBREV_TAC`cs1 = compiler_state_env_fupd X Y` >>
      qspecl_then[`cs1`,`exp'`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Abbr`cs1`] >>
      disch_then(strip_assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] ) >> fs[] >>
    POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`sm`,`cls`,`cs`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`,`bc10 ++ bc1`]mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧
     FDOM s' ⊆ FDOM s'' ∧
     FDOM s' ⊆ FDOM sm` by PROVE_TAC[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >>
    fs[ALL_DISTINCT_APPEND] >> rfs[] >>
    disch_then (mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then (qx_choosel_then[`rf`,`bv`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    conj_tac >- (
      Q.PAT_ABBREV_TAC`cs1 = compiler_state_env_fupd X Y` >>
      qspecl_then[`cs1`,`exp'`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
      fs[Abbr`cs1`] >>
      disch_then(strip_assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac`(compile cs1 exp').out = cy ++ X` >> qunabbrev_tac`X` >>
      first_x_assum(qspecl_then[`sm`,`cls`,`cs1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cy`,`(Stack (Pops 1))::bc1`]mp_tac) >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        conj_tac >- (
          simp[Once DISJOINT_SYM,Abbr`cs1`] >>
          fs[DISJOINT_SYM] ) >>
        conj_tac >- (
          imp_res_tac Cevaluate_Clocs >> fs[] >>
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          gen_tac >>
          simp[Once CONJ_COMM] >>
          simp[GSYM AND_IMP_INTRO] >>
          ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
          metis_tac[] ) >>
        conj_tac >- (
          imp_res_tac Cevaluate_Clocs >> fs[] ) >>
        simp[Abbr`cs1`,Abbr`cs0`,Abbr`bs1`] >>
        conj_tac >- (
          fsrw_tac[DNF_ss][SUBSET_DEF] >>
          metis_tac[] ) >>
        conj_tac >- (
          fs[compile_sz] >>
          Q.PAT_ABBREV_TAC`envw = DRESTRICT env X` >>
          qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' envv cs.env szz bss` >>
          `envw |+ (n,v) = envv |+ (n,v)` by (
            unabbrev_all_tac >>
            simp[GSYM fmap_EQ_THM,FDOM_DRESTRICT,EXTENSION] >>
            conj_tac >- (rw[] >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
            simp[FAPPLY_FUPDATE_THM,DRESTRICT_DEF] ) >>
          pop_assum SUBST1_TAC >>
          qunabbrev_tac`szz` >>
          match_mp_tac Cenv_bs_FUPDATE >>
          qexists_tac `bs with <|code := bce; pc := next_addr bs.inst_length (bc0 ++ REVERSE cx); refs := rf|>` >>
          simp[bc_state_component_equality,Abbr`bss`] >>
          match_mp_tac Cenv_bs_imp_decsz >> rfs[] >>
          qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' envv cs.env szz bss` >>
          qexists_tac `bss` >>
          simp[bc_state_component_equality,Abbr`bss`,Abbr`szz`] >>
          spose_not_then strip_assume_tac >>
          imp_res_tac Cenv_bs_CTLet_bound >>
          DECIDE_TAC) >>
        match_mp_tac compile_labels_lemma >>
        map_every qexists_tac[`FST(sdt cs)`,`exp`,`bc0`,`REVERSE cx`] >>
        simp[] ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      `FST(sdt cs1) = cs1` by rw[Abbr`cs1`] >>
      `cs1.out = cx ++ cs.out` by rw[Abbr`cs1`] >>
      fs[] >>
      disch_then(mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [code_for_push_def,LET_THM] o CONJUNCT1) >>
      disch_then(qx_choosel_then[`rf'`,`bv'`]strip_assume_tac) >>
      srw_tac[DNF_ss][code_for_push_def,LET_THM] >>
      map_every qexists_tac [`rf'`,`bv'`] >>
      `n ∈ FDOM cs1.env` by rw[Abbr`cs1`] >> fs[] >>
      qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
      conj_tac >- (
        match_mp_tac(SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
        qexists_tac`bs2` >>
        conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
        match_mp_tac RTC_SUBSET >>
        rw[bc_eval1_thm] >>
        `bc_fetch bs2 = SOME (Stack (Pops 1))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs2`] >>
          qexists_tac`bc0 ++ REVERSE cx ++ REVERSE cy`>>rw[] ) >>
        rw[bc_eval1_def] >>
        rw[bump_pc_def] >>
        srw_tac[ARITH_ss][bc_eval_stack_def,Abbr`bs2`,Abbr`bs1`] >>
        rw[bc_state_component_equality] >>
        srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND] ) >>
      conj_tac >- fs[Abbr`bs1`] >>
      conj_tac >- (
        qmatch_abbrev_tac`Cenv_bs c sm cls s'' env4 cs.env (cs.sz + 1) bs4` >>
        match_mp_tac Cenv_bs_imp_incsz >>
        qmatch_assum_abbrev_tac`Cenv_bs c sm cls s'' env3 renv1 rsz1 bs3` >>
        qexists_tac`bs4 with <| stack := bs.stack; pc := bs3.pc |>` >>
        reverse(rw[]) >- rw[bc_state_component_equality,Abbr`bs4`] >>
        `n ∉ FDOM cs.env` by (
          fs[Cenv_bs_def,fmap_rel_def,Abbr`env4`,FDOM_DRESTRICT] >>
          metis_tac[SUBSET_INTER_ABSORPTION,SUBSET_DEF,INTER_COMM] ) >>
        qspecl_then[`c`,`sm`,`cls`,`s''`,`env3`,`n`,`renv1`,`rsz1`,`bs3`]mp_tac Cenv_bs_DOMSUB >>
        simp[Abbr`renv1`,Abbr`rsz1`] >> strip_tac >>
        `(env3 \\ n = DRESTRICT env (FDOM cs.env)) ∧ (cs1.env \\ n = cs.env)`  by (
          unabbrev_all_tac >> simp[DRESTRICT_DOMSUB,DELETE_INSERT] >>
          conj_tac >- fs[DELETE_NON_ELEMENT] >>
          match_mp_tac DOMSUB_NOT_IN_DOM >>
          fs[] ) >>
        fs[] >>
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac`bs4 with stack := bv::bs.stack` >>
        reverse(rw[]) >- rw[bc_state_component_equality,Abbr`bs4`]
        >- (
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum (qspec_then`cs.sz +1`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        match_mp_tac Cenv_bs_imp_decsz >>
        qexists_tac`bs4 with stack := bs3.stack` >>
        reverse(rw[]) >- rw[bc_state_component_equality,Abbr`bs4`,Abbr`bs3`,Abbr`bs1`]
        >- (
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum (qspec_then`cs.sz +2`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        fs[Abbr`cs1`,Abbr`env4`] >>
        rfs[compile_sz,Abbr`cs0`] >>
        `bs4 with stack := bs3.stack = bs3 with pc := bs4.pc` by (
          rw[Abbr`bs4`,Abbr`bs3`,bc_state_component_equality,Abbr`bs1`] ) >>
        fs[Cenv_bs_with_pc]) >>
      fs[Abbr`bs1`,good_cls_def] >> metis_tac[SUBMAP_TRANS]) >>
    ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_env_fupd X Y` >>
    qspecl_then[`cs1`,`exp'`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    fs[Abbr`cs1`] >>
    disch_then(strip_assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
    qmatch_assum_abbrev_tac`(compile cs1 exp').out = cy ++ X` >> qunabbrev_tac`X` >>
    qmatch_assum_abbrev_tac`bs.code = bc0 ++ REVERSE cx ++ REVERSE cy ++ bcx ++ bc2` >>
    first_x_assum(qspecl_then[`sm`,`cls`,`cs1`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE cy`,`bcx ++ bc2`]mp_tac) >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- (
        simp[Once DISJOINT_SYM,Abbr`cs1`] >>
        fs[DISJOINT_SYM] ) >>
      conj_tac >- (
        imp_res_tac Cevaluate_Clocs >> fs[] >>
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        gen_tac >>
        simp[Once CONJ_COMM] >>
        simp[GSYM AND_IMP_INTRO] >>
        ho_match_mp_tac IN_FRANGE_DOMSUB_suff >>
        metis_tac[] ) >>
      conj_tac >- (
        imp_res_tac Cevaluate_Clocs >> fs[] ) >>
      simp[Abbr`cs1`,Abbr`cs0`,Abbr`bs1`] >>
      conj_tac >- (
        fsrw_tac[DNF_ss][SUBSET_DEF] >>
        metis_tac[] ) >>
      conj_tac >- (
        fs[compile_sz] >>
        Q.PAT_ABBREV_TAC`envw = DRESTRICT env X` >>
        qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' envv cs.env szz bss` >>
        `envw |+ (n,v) = envv |+ (n,v)` by (
          unabbrev_all_tac >>
          simp[GSYM fmap_EQ_THM,FDOM_DRESTRICT,EXTENSION] >>
          conj_tac >- (rw[] >> rpt (pop_assum kall_tac) >> metis_tac[]) >>
          simp[FAPPLY_FUPDATE_THM,DRESTRICT_DEF] ) >>
        pop_assum SUBST1_TAC >>
        qunabbrev_tac`szz` >>
        match_mp_tac Cenv_bs_FUPDATE >>
        qexists_tac `bs with <|code := bce; pc := next_addr bs.inst_length (bc0 ++ REVERSE cx); refs := rf|>` >>
        simp[bc_state_component_equality,Abbr`bss`] >>
        match_mp_tac Cenv_bs_imp_decsz >> rfs[] >>
        qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' envv cs.env szz bss` >>
        qexists_tac `bss` >>
        simp[bc_state_component_equality,Abbr`bss`,Abbr`szz`] >>
        spose_not_then strip_assume_tac >>
        imp_res_tac Cenv_bs_CTLet_bound >>
        DECIDE_TAC) >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac[`FST(sdt cs)`,`exp`,`bc0`,`REVERSE cx`] >>
      simp[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(mp_tac o SIMP_RULE (srw_ss()++DNF_ss) [] o CONJUNCT2) >>
    strip_tac >>
    rpt gen_tac >> strip_tac >>
    first_x_assum(qspecl_then[`env0`,`ns`,`defs`,`xs`,`vs`,`(n,v)::klvs`,`bv::blvs`,`benv`,`ret`,`args`,`cl`,`st`]mp_tac) >>
    simp[Abbr`bcx`,FUPDATE_LIST_THM] >>
    simp[ADD1] >>
    Q.PAT_ABBREV_TAC`cs1' = compiler_state_tail_fupd X Y` >>
    `cs1' = cs1` by (
      rw[Abbr`cs1`,Abbr`cs1'`,compiler_state_component_equality] ) >>
    pop_assum SUBST1_TAC >> qunabbrev_tac`cs1'` >>
    simp[Abbr`cs1`,Abbr`bs1`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_asm1_tac >- (
        fs[DISJOINT_DEF,EXTENSION] >>
        metis_tac[] ) >>
      conj_tac >- (
        match_mp_tac (GSYM FUPDATE_FUPDATE_LIST_COMMUTES) >>
        fs[DISJOINT_DEF,EXTENSION] ) >>
      fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] >>
      rw[] >>
      match_mp_tac(MP_CANON (GEN_ALL(CONJUNCT1(SPEC_ALL Cv_bv_SUBMAP)))) >>
      simp[] >>
      qexists_tac`DRESTRICT sm (FDOM s)` >>
      simp[DRESTRICT_SUBSET_SUBMAP] >>
      fs[good_cls_def,FEVERY_DEF,SUBMAP_DEF,DRESTRICT_DEF,UNCURRY] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    simp[code_for_return_def] >>
    disch_then(qx_choosel_then[`bv2`,`rf2`]strip_assume_tac) >>
    map_every qexists_tac[`bv2`,`rf2`] >>
    simp[] >>
    conj_tac >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
    metis_tac[SUBMAP_TRANS] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[compile_def,FOLDL_UNION_BIGUNION] >>
    rpt gen_tac >> strip_tac >>
    simp_tac(srw_ss()++ETA_ss)[] >>
    rpt gen_tac >> strip_tac >>
    rfs[] >> fs[] >>
    BasicProvers.VAR_EQ_TAC >>
    POP_ASSUM_LIST(map_every assume_tac) >>
    qspecl_then[`cs0`,`exp`](Q.X_CHOOSE_THEN`cx`strip_assume_tac)(CONJUNCT1 compile_append_out) >>
    `cs0.out = cs.out` by rw[Abbr`cs0`] >> fs[] >>
    first_x_assum(qspecl_then[`sm`,`cls`,`cs`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧ FDOM s' ⊆ FDOM s'' ∧ FDOM s'' ⊆ FDOM s'''` by PROVE_TAC[Cevaluate_store_SUBSET,FST] >>
    `FDOM s' ⊆ FDOM sm` by PROVE_TAC[SUBSET_TRANS] >>
    fs[ALL_DISTINCT_APPEND] >>
    qspecl_then[`compile cs0 exp`,`exps`](Q.X_CHOOSE_THEN`bcs`strip_assume_tac)FOLDL_compile_append_out >>
    qabbrev_tac`cs1 = FOLDL compile (compile cs0 exp) exps` >>
    fs[] >>
    reverse (Cases_on `∃bc10. code = REVERSE cx ++ REVERSE bcs ++ bc10`) >- (
      Q.PAT_ABBREV_TAC`ls = CallPtr::X` >>
      Q.ISPECL_THEN[`ls`,`code`]SUBST1_TAC SWAP_REVERSE >>
      simp[Abbr`ls`] >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`Q = REVERSE cx ++ (REVERSE bcs ++ X)` >>
      Cases_on `code = Q` >> fs[Abbr`Q`] >>
      fsrw_tac[DNF_ss][] >>
      rpt gen_tac >>
      Q.PAT_ABBREV_TAC`ls = JumpPtr::X` >>
      Q.ISPECL_THEN[`ls`,`code`]SUBST1_TAC SWAP_REVERSE >>
      simp[Abbr`ls`]) >> fs[] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] o CONJUNCT1) >>
    disch_then(qx_choosel_then[`rf`,`bf`]strip_assume_tac) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    first_x_assum(qspecl_then[`sm`,`cls`,`compile cs0 exp`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE cx`,`REVERSE bcs`]mp_tac) >>
    simp[Abbr`bs1`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      simp[Abbr`cs0`,compile_sz] >>
      conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
      match_mp_tac compile_labels_lemma >>
      map_every qexists_tac [`FST(sdt cs)`,`exp`,`bc0`,`REVERSE cx`] >>
      rw[] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by ( rw[Abbr`cs0`,Abbr`P`,compile_nontail] ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    disch_then(mp_tac o SIMP_RULE(srw_ss()++DNF_ss)[code_for_push_def,LET_THM]) >>
    disch_then(qx_choosel_then[`bvs`,`rfs`]strip_assume_tac) >>
    conj_tac >- (
      srw_tac[DNF_ss][code_for_push_def,LET_THM] >>
      qpat_assum`X = REVERSE bc10` (assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >>
      qmatch_assum_abbrev_tac`Cv_bv (ps',c,l2a,cls) cl bf` >>
      `Cv_bv (DRESTRICT sm (FDOM s''), c, l2a, cls) cl bf` by (
        match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
        qexists_tac`ps'` >>
        rw[Abbr`ps'`] >- (
          match_mp_tac DRESTRICT_SUBSET_SUBMAP >> rw[] ) >>
        fs[good_cls_def,FEVERY_DEF,UNCURRY] >>
        `p ∈ FDOM rfs` by PROVE_TAC[] >>
        fs[SUBMAP_DEF,FDOM_DRESTRICT] ) >>
      pop_assum mp_tac >>
      simp[Abbr`cl`,Once Cv_bv_cases] >>
      disch_then(qx_choosel_then[`a`,`bve`,`b`,`i'`,`l`,`xs`]strip_assume_tac) >>
      `i' = i` by ( Cases_on`ns' = []` >> fs[] ) >> rw[] >>
      fs[] >> rfs[] >> rw[] >> fs[] >> rw[] >>
      qho_match_abbrev_tac`∃rf bv. bc_next^* bs (bs2 rf bv) ∧ P rf bv` >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
      qmatch_assum_abbrev_tac`bc_next^* bs0 bs3` >>
      qsuff_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >-
        metis_tac[RTC_TRANSITIVE,transitive_def] >>
      `bc_fetch bs3 = SOME (Stack (Load (LENGTH exps)))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs3`,REVERSE_APPEND] >>
        qexists_tac`bc0 ++ REVERSE cx ++ REVERSE bcs` >>
        rw[] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
      `LENGTH exps = LENGTH bvs` by (fs[EVERY2_EVERY] >> metis_tac[Cevaluate_list_LENGTH] ) >>
      simp[Abbr`bs3`] >>
      Q.PAT_ABBREV_TAC`l2 = Block 3 X::Y` >>
      Q.ISPECL_THEN[`l2`,`REVERSE bvs`]mp_tac EL_LENGTH_APPEND >>
      simp[Abbr`l2`] >> disch_then kall_tac >>
      simp[bump_pc_with_stack] >> fs[bc_fetch_with_stack] >>
      simp[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qho_match_abbrev_tac`∃rf bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv` >>
      `bc_fetch bs1 = SOME (Stack (El 1))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        qexists_tac`ls ++ [Stack (Load (LENGTH bvs))]` >>
        rw[Abbr`ls`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`,bc_eval_stack_def] >>
      (* Q.PAT_ABBREV_TAC`benv = if X then Number 0 else Y` >> *)
      fs[bump_pc_with_stack,bc_fetch_with_stack] >>
      simp[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qho_match_abbrev_tac`∃rf bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv` >>
      `bc_fetch bs1 = SOME (Stack (Load (SUC(LENGTH bvs))))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 2 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`,bc_eval_stack_def] >>
      Q.PAT_ABBREV_TAC`l2 = [Block 3 X]` >>
      Q.ISPECL_THEN[`l2 ++ bs.stack`,`REVERSE bvs`]mp_tac EL_LENGTH_APPEND >>
      simp[Abbr`l2`] >> disch_then kall_tac >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      rw[bump_pc_def] >>
      qho_match_abbrev_tac`∃rf bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv` >>
      `bc_fetch bs1 = SOME (Stack (El 0))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 3 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`,bc_eval_stack_def] >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      fsrw_tac[ARITH_ss][] >>
      rw[bump_pc_def] >>
      qho_match_abbrev_tac`∃rf bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv` >>
      `bc_fetch bs1 = SOME CallPtr` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs1`] >>
        Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
        Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
        qexists_tac`ls ++ TAKE 4 l2` >>
        srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
      rw[bc_eval1_thm,bc_eval1_def] >>
      simp[Abbr`bs1`] >>
      fs[bc_fetch_with_stack,bump_pc_with_stack] >>
      fsrw_tac[ARITH_ss][] >>
      rw[bump_pc_def] >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      qpat_assum`bc_fetch X = Y` kall_tac >>
      Q.PAT_ABBREV_TAC`ret = x + 1` >>
      qho_match_abbrev_tac`∃rf bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv` >>
      qpat_assum`good_code_env c d bce`(fn th => mp_tac((uncurry CONJ)((I##Q.SPEC`l`)(CONJ_PAIR(SIMP_RULE(srw_ss())[good_code_env_def,FEVERY_DEF]th)))) >> assume_tac th) >>
      fs[FLOOKUP_DEF] >>
      `(ns,cb) = (xs, INR l)` by (
        Cases_on`ns'=[]`>>fs[] ) >> fs[] >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      qpat_assum`X = d ' l`(assume_tac o SYM) >>
      simp[] >>
      map_every qx_gen_tac [`csc`,`cb0`,`cc`,`cb1`] >>
      strip_tac >>
      pop_assum (assume_tac o SYM) >>
      qmatch_assum_abbrev_tac`cb0 ++ [Label l] ++ REVERSE cc ++ bcl ++ cb1 = bce` >>
      first_x_assum (qspecl_then[`sm`,`cls`,`csc`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`,`REVERSE cc`,`bcl ++ cb1 ++ bcr`]mp_tac) >>
      qmatch_abbrev_tac`(X ⇒ Q) ⇒ R` >>
      `X` by (
        map_every qunabbrev_tac[`X`,`P`,`Q`,`R`] >>
        `(ns' ≠ [] ⇒ i < LENGTH ns') ∧ ALL_DISTINCT ns'` by (
          Cases_on`ns'=[]`>>fs[] >>
          imp_res_tac find_index_LESS_LENGTH >> fs[] ) >>
        simp[FDOM_bind_fv] >>
        conj_tac >- (
          unabbrev_all_tac >>
          fs[FLOOKUP_DEF] >> rfs[] >>
          fs[DISJOINT_DEF,EXTENSION] >> rw[] >>
          ntac 11 (pop_assum kall_tac) >>
          ntac 3 (pop_assum (qspec_then`x`mp_tac)) >>
          Cases_on `x ∈ free_vars c (c ' l)` >> fs[] >>
          Cases_on `x ∈ set (binders (c ' l))` >> fs[] >>
          qspecl_then[`c`,`c ' l`,`l`]mp_tac(CONJUNCT1 free_vars_DOMSUB) >>
          simp[SUBSET_DEF] >>
          disch_then(qspec_then`x`strip_assume_tac) >> rfs[] >>
          Cases_on`MEM x ns`>>fs[]>>
          Cases_on`MEM x ns'`>>fs[]>>
          qpat_assum`benv_bvs X Y Z ns env' defs ns' i`mp_tac >>
          simp[Once Cv_bv_cases] >> rw[] >> pop_assum mp_tac >>
          Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars X Y)` >>
          Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
          `MEM x evs` by (
            Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
            simp[Abbr`evs`,MEM_FILTER] >>
            simp[Abbr`fvs`] ) >>
          pop_assum(mp_tac o SIMP_RULE std_ss [MEM_EL]) >>
          disch_then(Q.X_CHOOSE_THEN`z` strip_assume_tac) >>
          disch_then(qspec_then`z`mp_tac) >> simp[] >>
          Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
          simp[] ) >>
        conj_tac >- (
          qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval (CRecClos env' ns' defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
          qspecl_then[`c`,`d`,`s'`,`env`,`exps`,`(s'',Rval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
          simp[] >>
          qpat_assum `LENGTH ns = LENGTH vs` mp_tac >>
          qpat_assum `FDOM s' ⊆ FDOM s''` mp_tac >>
          rpt (pop_assum kall_tac) >>
          fsrw_tac[DNF_ss][extend_rec_env_def,SUBSET_DEF,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
          qx_gen_tac `x` >>
          simp[FORALL_AND_THM,RIGHT_FORALL_IMP_THM] >>
          ntac 4 strip_tac >>
          simp[Once CONJ_COMM] >> simp[GSYM AND_IMP_INTRO] >>
          ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
          reverse conj_tac >-
            (srw_tac[DNF_ss][MAP_ZIP] >> PROVE_TAC[]) >>
          ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
          srw_tac[DNF_ss][MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] >>
          PROVE_TAC[] ) >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        conj_tac >- fs[good_cls_def,Abbr`bs1`] >>
        conj_tac >- simp[Abbr`bs1`] >>
        conj_tac >- simp[Abbr`bs1`] >>
        conj_tac >- (
          fs[Abbr`bs1`,Abbr`l2a`] >>
          qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          simp[] >>
          disch_then(qspec_then`LENGTH cb0`mp_tac) >>
          srw_tac[ARITH_ss][] >>
          pop_assum mp_tac >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
          simp[FILTER_APPEND] ) >>
        conj_tac >- (
          match_mp_tac Cenv_bs_bind_fv >>
          map_every qexists_tac[`env'`,`defs`,`b`,`l`,`vs`] >>
          simp[Abbr`bs1`] >>
          map_every qexists_tac[`a`,`bvs`,`bs.stack`] >>
          simp[] >>
          conj_tac >- fs[good_cls_def] >>
          conj_tac >- ( fs[s_refs_def,Cenv_bs_def] ) >>
          conj_tac >- (rw[] >> fs[]) >>
          conj_tac >- (rw[] >> fs[]) >>
          fs[FLOOKUP_DEF] >> rfs[] >>
          fs[Abbr`l2a`] >>
          match_mp_tac (GEN_ALL benv_bvs_free_vars_SUBSET) >>
          simp[] >> metis_tac[] ) >>
        qpat_assum`X = bce`(assume_tac o SYM) >>
        fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
      simp[] >>
      map_every qunabbrev_tac[`X`,`Q`] >>
      disch_then(qspecl_then[`LENGTH vs`,`0`]mp_tac o CONJUNCT2) >>
      Q.PAT_ABBREV_TAC`csc' = compiler_state_tail_fupd X Y` >>
      `csc' = csc` by (
        simp[Abbr`csc'`,compiler_state_component_equality] ) >>
      simp[] >>
      simp_tac (srw_ss()++DNF_ss) [] >>
      simp[Abbr`bs1`] >>
      disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
      simp[LENGTH_NIL_SYM,FUPDATE_LIST_THM] >>
      disch_then(qspecl_then[`bs.stack`,`Block 3 [CodePtr a; bve]`,`bvs`,`vs`,`xs`,`defs`,`ns'`,`env'`]mp_tac) >>
      ntac 3 (pop_assum kall_tac) >>
      simp[Abbr`bcl`] >>
      `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
      simp[code_for_return_def,Abbr`R`] >>
      disch_then(qx_choosel_then[`bvr`,`rfr`]strip_assume_tac) >>
      map_every qexists_tac [`rfr`,`bvr`] >>
      simp[Abbr`bs2`] >>
      Q.PAT_ABBREV_TAC`ret' = next_addr X Y` >>
      `ret' = ret` by (
        map_every qunabbrev_tac[`ret`,`ret'`] >>
        srw_tac[ARITH_ss][FILTER_APPEND,SUM_APPEND,ADD1] ) >>
      rw[] >>
      simp[Abbr`P`] >>
      reverse conj_tac >- PROVE_TAC[SUBMAP_TRANS] >>
      match_mp_tac Cenv_bs_imp_incsz >>
      qunabbrev_tac`bs0` >>
      qmatch_assum_abbrev_tac`Cenv_bs c sm cls s cenv cs.env cs.sz bs0` >>
      qexists_tac`bs0 with refs := rfr` >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      match_mp_tac Cenv_bs_change_store >>
      qmatch_assum_abbrev_tac`Cenv_bs c sm cls s cenv cs.env cs.sz bs0` >>
      map_every qexists_tac[`s`,`bs0`] >>
      simp[] >>
      fs[s_refs_def,Abbr`l2a`] >>
      simp[Abbr`bs0`,bc_state_component_equality] >>
      conj_tac >- metis_tac[SUBMAP_TRANS] >>
      conj_tac >- metis_tac[SUBSET_TRANS] >>
      fs[good_cls_def,SUBSET_DEF,FEVERY_DEF,UNCURRY] ) >>
    asm_simp_tac(srw_ss()++DNF_ss)[] >>
    map_every qx_gen_tac[`env0`,`ns0`,`defs0`,`xs0`,`vs0`,`klvs`,`blvs`,`benv`,`ret`,`args0`,`cl0`] >>
    rpt gen_tac >> strip_tac >>
    qpat_assum`X = REVERSE bc10` (assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >>
    strip_tac >>
    qmatch_assum_abbrev_tac`Cv_bv (ps',c,l2a,cls) cl bf` >>
    `Cv_bv (DRESTRICT sm (FDOM s''), c, l2a, cls) cl bf` by (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac`ps'` >>
      rw[Abbr`ps'`] >- (
        match_mp_tac DRESTRICT_SUBSET_SUBMAP >> rw[] ) >>
      fs[good_cls_def,FEVERY_DEF,UNCURRY] >>
      `p ∈ FDOM rfs` by PROVE_TAC[] >>
      fs[SUBMAP_DEF,FDOM_DRESTRICT] ) >>
    pop_assum mp_tac >>
    simp[Abbr`cl`,Once Cv_bv_cases] >>
    disch_then(qx_choosel_then[`a`,`bve`,`b`,`i'`,`l`,`xs`]strip_assume_tac) >>
    `i' = i` by ( Cases_on`ns' = []` >> fs[] ) >> rw[] >>
    fs[] >> rfs[] >> rw[] >> fs[] >> rw[] >>
    qpat_assum`good_code_env c d bce`(fn th => mp_tac((uncurry CONJ)((I##Q.SPEC`l`)(CONJ_PAIR(SIMP_RULE(srw_ss())[good_code_env_def,FEVERY_DEF]th)))) >> assume_tac th) >>
    fs[FLOOKUP_DEF] >>
    `(ns,cb) = (xs, INR l)` by (
      Cases_on`ns'=[]`>>fs[] ) >> fs[] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    qpat_assum`X = d ' l`(assume_tac o SYM) >>
    simp[] >>
    map_every qx_gen_tac [`csc`,`cb0`,`cc`,`cb1`] >>
    strip_tac >>
    pop_assum (assume_tac o SYM) >>
    qmatch_assum_abbrev_tac`cb0 ++ [Label l] ++ REVERSE cc ++ bcl ++ cb1 = bce` >>
    simp[code_for_return_def] >>
    qho_match_abbrev_tac`∃rf bv. bc_next^* bs (bs2 rf bv) ∧ P rf bv` >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs05` >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs3` >>
    qsuff_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >-
      metis_tac[RTC_TRANSITIVE,transitive_def] >>
    `bc_fetch bs3 = SOME (Stack (Load (LENGTH klvs + (LENGTH exps + 2))))` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      qexists_tac`bc0 ++ REVERSE cx ++ REVERSE bcs` >>
      rw[] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
    `(LENGTH exps = LENGTH bvs) ∧ (LENGTH klvs = LENGTH blvs)` by (fs[EVERY2_EVERY] >> metis_tac[Cevaluate_list_LENGTH] ) >>
    simp[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`E = EL N (REVERSE bvs ++ X)` >>
    `E = CodePtr ret` by (
      unabbrev_all_tac >>
      rpt (pop_assum kall_tac) >>
      `LENGTH blvs + (LENGTH bvs + 2) = (SUC (LENGTH blvs + 1)) + LENGTH bvs` by DECIDE_TAC >>
      pop_assum SUBST1_TAC >>
      Q.PAT_ABBREV_TAC`l2 = REVERSE bvs ++ X` >>
      Q.PAT_ABBREV_TAC`m = SUC X` >>
      Q.ISPECL_THEN[`m`,`LENGTH bvs`,`l2`]mp_tac (GSYM EL_DROP) >>
      srw_tac[ARITH_ss][Abbr`m`,Abbr`l2`] >>
      Q.PAT_ABBREV_TAC`l2 = Block X Y::Z` >>
      Q.ISPECL_THEN[`REVERSE bvs`,`l2`]mp_tac DROP_LENGTH_APPEND >>
      simp[] >> disch_then kall_tac >>
      simp[Abbr`l2`] >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`l2 = [benv; X] ++ Y` >>
      Q.ISPECL_THEN[`1`,`LENGTH blvs`,`blvs ++ l2`]mp_tac (GSYM EL_DROP) >>
      srw_tac[ARITH_ss][Abbr`l2`,DROP_LENGTH_APPEND] ) >>
    pop_assum SUBST1_TAC >> pop_assum kall_tac >>
    simp[bump_pc_def] >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >>
    `bc_fetch bs3 = SOME (Stack (Load (SUC (LENGTH exps))))` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
      Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
      qexists_tac`ls ++ TAKE 1 l2` >>
      srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
    simp[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`E = EL N (REVERSE bvs ++ X)` >>
    `E = Block 3 [CodePtr a; bve]` by (
      unabbrev_all_tac >>
      rpt (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`l2 = Block 3 X::Y`>>
      Q.ISPECL_THEN[`l2`,`REVERSE bvs`]mp_tac EL_LENGTH_APPEND >>
      srw_tac[ARITH_ss][Abbr`l2`] ) >>
    pop_assum SUBST1_TAC >> pop_assum kall_tac >>
    simp[bump_pc_def] >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >>
    `bc_fetch bs3 = SOME (Stack (El 1))` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
      Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
      qexists_tac`ls ++ TAKE 2 l2` >>
      srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,Abbr`bs3`] >>
    rw[bump_pc_def] >>
    ntac 2 (pop_assum kall_tac) >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >>
    `bc_fetch bs3 = SOME (Stack (Load (SUC (SUC (LENGTH exps)))))` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
      Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
      qexists_tac`ls ++ TAKE 3 l2` >>
      srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`E = EL N (REVERSE bvs ++ X)` >>
    `E = Block 3 [CodePtr a; bve]` by (
      unabbrev_all_tac >>
      rpt (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`l2 = Block 3 X::Y`>>
      Q.ISPECL_THEN[`l2`,`REVERSE bvs`]mp_tac EL_LENGTH_APPEND >>
      srw_tac[ARITH_ss][Abbr`l2`] ) >>
    pop_assum SUBST1_TAC >> pop_assum kall_tac >>
    simp[bump_pc_def] >>
    pop_assum kall_tac >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >>
    `bc_fetch bs3 = SOME (Stack (El 0))` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
      Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
      qexists_tac`ls ++ TAKE 4 l2` >>
      srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def,Abbr`bs3`] >>
    rw[bump_pc_def] >>
    pop_assum kall_tac >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >>
    `bc_fetch bs3 = SOME (Stack (Shift (LENGTH exps + 4) (LENGTH args0 + (LENGTH klvs + 3))))` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
      Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
      qexists_tac`ls ++ TAKE 5 l2` >>
      srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def,bc_eval_stack_def] >>
    simp[Abbr`bs3`] >>
    Q.PAT_ABBREV_TAC`E = TAKE X (REVERSE bvs ++ Y)` >>
    Q.PAT_ABBREV_TAC`D = blvs ++ X ++ Y ++ Z ++ st` >>
    Q.PAT_ABBREV_TAC`G = DROP X (REVERSE bvs ++ Y)` >>
    `E ++ G = REVERSE bvs ++ Block 3 [CodePtr a; bve]::st` by (
      unabbrev_all_tac >>
      rpt (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`l2 = REVERSE bvs ++ X` >>
      Q.ISPECL_THEN[`LENGTH bvs`,`1`,`l2`]mp_tac TAKE_SUM >>
      srw_tac[ARITH_ss][Abbr`l2`] >>
      pop_assum kall_tac >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`l2 = [X] ++ (blvs ++ Y)` >>
      Q.ISPECL_THEN[`REVERSE bvs`,`l2`]mp_tac TAKE_LENGTH_APPEND >>
      Q.ISPECL_THEN[`REVERSE bvs`,`l2`]mp_tac DROP_LENGTH_APPEND >>
      rw[] >>
      rw[Abbr`l2`] >>
      Q.PAT_ABBREV_TAC`n = LENGTH args0 + Y` >>
      `n = 1 + LENGTH args0 + 2 + LENGTH blvs + 1 + LENGTH bvs` by (rw[Abbr`n`] >> DECIDE_TAC) >>
      pop_assum SUBST1_TAC >>
      Q.PAT_ABBREV_TAC`m = X + 1` >>
      Q.PAT_ABBREV_TAC`l2 = X ++ st` >>
      Q.ISPECL_THEN[`m`,`LENGTH bvs`,`l2`]mp_tac (GSYM DROP_DROP) >>
      `m + LENGTH bvs ≤ LENGTH l2` by srw_tac[ARITH_ss][Abbr`l2`,Abbr`m`] >>
      rw[Abbr`l2`] >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`l2 = X ++ (blvs ++ Y)` >>
      Q.ISPECL_THEN[`REVERSE bvs`,`l2`]mp_tac DROP_LENGTH_APPEND >>
      rw[Abbr`m`,Abbr`l2`] >>
      rpt (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`m = X + 2` >>
      Q.PAT_ABBREV_TAC`l2 = X ++ st` >>
      Q.ISPECL_THEN[`m`,`LENGTH blvs`,`l2`]mp_tac (GSYM DROP_DROP) >>
      `m + LENGTH blvs ≤ LENGTH l2` by (srw_tac[ARITH_ss][Abbr`l2`,Abbr`m`] >> DECIDE_TAC) >>
      rw[Abbr`l2`] >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`l2 = ([benv;X] ++ Y)` >>
      Q.ISPECL_THEN[`blvs`,`l2`]mp_tac DROP_LENGTH_APPEND >>
      rw[] >>
      unabbrev_all_tac >>
      rpt (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`m = 1 + X` >>
      REWRITE_TAC[APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`l2 = X ++ st` >>
      Q.ISPECL_THEN[`m`,`2`,`l2`]mp_tac (GSYM DROP_DROP) >>
      `m + 2 ≤ LENGTH l2` by (srw_tac[ARITH_ss][Abbr`l2`,Abbr`m`] >> DECIDE_TAC) >>
      rw[] >>
      rw[Abbr`l2`,Abbr`m`] >>
      rpt (pop_assum kall_tac) >>
      Q.PAT_ABBREV_TAC`l2 = X ++ st` >>
      Q.ISPECL_THEN[`1`,`LENGTH args0`,`l2`]mp_tac (GSYM DROP_DROP) >>
      `1 + LENGTH args0 ≤ LENGTH l2` by (srw_tac[ARITH_ss][Abbr`l2`] >> DECIDE_TAC) >>
      rw[] >>
      rw[Abbr`l2`] >>
      REWRITE_TAC[GSYM APPEND_ASSOC] >>
      Q.PAT_ABBREV_TAC`l2 = X ++ st` >>
      Q.ISPECL_THEN[`REVERSE args0`,`l2`]mp_tac DROP_LENGTH_APPEND >>
      rw[] >>
      rw[Abbr`l2`] ) >>
    pop_assum SUBST1_TAC >>
    map_every qunabbrev_tac[`E`,`D`,`G`] >>
    fsrw_tac[ARITH_ss][bump_pc_def] >>
    pop_assum kall_tac >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs3 (bs2 rf bv) ∧ P rf bv` >>
    `bc_fetch bs3 = SOME JumpPtr` by (
      match_mp_tac bc_fetch_next_addr >>
      rw[Abbr`bs3`,REVERSE_APPEND] >>
      Q.PAT_ABBREV_TAC`ls = bc0 ++ X ++ Y` >>
      Q.PAT_ABBREV_TAC`l2:bc_inst list = X::Y` >>
      qexists_tac`ls ++ TAKE 6 l2` >>
      srw_tac[ARITH_ss][Abbr`ls`,Abbr`l2`,REVERSE_APPEND,FILTER_APPEND,SUM_APPEND,ADD1] ) >>
    simp_tac(srw_ss()++DNF_ss)[Once RTC_CASES1] >> disj2_tac >>
    rw[bc_eval1_thm,bc_eval1_def] >>
    simp[Abbr`bs3`] >>
    pop_assum kall_tac >>
    qho_match_abbrev_tac `∃rf bv. bc_next^* bs1 (bs2 rf bv) ∧ P rf bv` >>
    qmatch_assum_abbrev_tac`bce ++ bcr = X` >> qunabbrev_tac`X` >>
    first_x_assum (qspecl_then[`sm`,`cls`,`csc`,`bs1`,`bce`,`bcr`,`cb0 ++ [Label l]`,`REVERSE cc`,`bcl ++ cb1 ++ bcr`]mp_tac) >>
    qmatch_abbrev_tac`(X ⇒ Q) ⇒ R` >>
    `X` by (
      map_every qunabbrev_tac[`X`,`P`,`Q`,`R`] >>
      `(ns' ≠ [] ⇒ i < LENGTH ns') ∧ ALL_DISTINCT ns'` by (
        Cases_on`ns'=[]`>>fs[] >>
        imp_res_tac find_index_LESS_LENGTH >> fs[] ) >>
      simp[FDOM_bind_fv] >>
      conj_tac >- (
        unabbrev_all_tac >>
        fs[FLOOKUP_DEF] >> rfs[] >>
        fs[DISJOINT_DEF,EXTENSION] >> rw[] >>
        ntac 14 (pop_assum kall_tac) >>
        ntac 3 (pop_assum (qspec_then`x`mp_tac)) >>
        Cases_on `x ∈ free_vars c (c ' l)` >> fs[] >>
        Cases_on `x ∈ set (binders (c ' l))` >> fs[] >>
        qspecl_then[`c`,`c ' l`,`l`]mp_tac(CONJUNCT1 free_vars_DOMSUB) >>
        simp[SUBSET_DEF] >>
        disch_then(qspec_then`x`strip_assume_tac) >> rfs[] >>
        Cases_on`MEM x ns`>>fs[]>>
        Cases_on`MEM x ns'`>>fs[]>>
        qpat_assum`benv_bvs X Y Z ns env' defs ns' i`mp_tac >>
        simp[Once Cv_bv_cases] >> rw[] >> pop_assum mp_tac >>
        Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars X Y)` >>
        Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
        `MEM x evs` by (
          Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
          simp[Abbr`evs`,MEM_FILTER] >>
          simp[Abbr`fvs`] ) >>
        pop_assum(mp_tac o SIMP_RULE std_ss [MEM_EL]) >>
        disch_then(Q.X_CHOOSE_THEN`z` strip_assume_tac) >>
        disch_then(qspec_then`z`mp_tac) >> simp[] >>
        Q.ISPECL_THEN[`ns'`,`x`,`0`]mp_tac find_index_MEM >>
        simp[] ) >>
      conj_tac >- (
        qmatch_assum_abbrev_tac`Cevaluate c d s env exp (s',Rval (CRecClos env' ns' defs n))` >>
        qspecl_then[`c`,`d`,`s`,`env`,`exp`,`(s',Rval (CRecClos env' ns' defs n))`]mp_tac (CONJUNCT1 Cevaluate_Clocs) >>
        qspecl_then[`c`,`d`,`s'`,`env`,`exps`,`(s'',Rval vs)`]mp_tac (CONJUNCT2 Cevaluate_Clocs) >>
        simp[] >>
        qpat_assum `LENGTH ns = LENGTH vs` mp_tac >>
        qpat_assum `FDOM s' ⊆ FDOM s''` mp_tac >>
        rpt (pop_assum kall_tac) >>
        fsrw_tac[DNF_ss][extend_rec_env_def,SUBSET_DEF,FOLDL2_FUPDATE_LIST,FOLDL_FUPDATE_LIST,MAP2_MAP,FST_pair,SND_pair,MAP_ZIP] >>
        qx_gen_tac `x` >>
        simp[FORALL_AND_THM,RIGHT_FORALL_IMP_THM] >>
        ntac 4 strip_tac >>
        simp[Once CONJ_COMM] >> simp[GSYM AND_IMP_INTRO] >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
        reverse conj_tac >-
          (srw_tac[DNF_ss][MAP_ZIP] >> PROVE_TAC[]) >>
        ho_match_mp_tac IN_FRANGE_FUPDATE_LIST_suff >>
        srw_tac[DNF_ss][MAP_MAP_o,combinTheory.o_DEF,MEM_MAP] >>
        PROVE_TAC[] ) >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      conj_tac >- ( fs[good_cls_def,Abbr`bs1`,Abbr`l2a`] ) >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- simp[Abbr`bs1`] >>
      conj_tac >- (
        fs[Abbr`bs1`,Abbr`l2a`] >>
        qspecl_then[`bce`,`bs.inst_length`,`l`,`0`]mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[] >>
        disch_then(qspec_then`LENGTH cb0`mp_tac) >>
        `EL (LENGTH cb0) bce = Label l` by (
          simp[Abbr`bce`] >>
          REWRITE_TAC[GSYM APPEND_ASSOC] >>
          Q.PAT_ABBREV_TAC`l2 = [Label l] ++ X` >>
          Q.ISPECL_THEN[`l2`,`cb0`]mp_tac EL_LENGTH_APPEND >>
          rw[Abbr`l2`] ) >>
        srw_tac[ARITH_ss][Abbr`bce`] >>
        REWRITE_TAC[GSYM APPEND_ASSOC] >>
        rw[EL_LENGTH_APPEND,TAKE_LENGTH_APPEND] >>
        simp[FILTER_APPEND] ) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_bind_fv >>
        map_every qexists_tac[`env'`,`defs`,`c ' l`,`l`,`vs`] >>
        simp[Abbr`bs1`] >>
        map_every qexists_tac[`a`,`bvs`,`st`] >>
        simp[] >>
        conj_tac >- fs[good_cls_def] >>
        conj_tac >- ( fs[s_refs_def,Cenv_bs_def] ) >>
        conj_tac >- (rw[] >> fs[]) >>
        conj_tac >- (rw[] >> fs[]) >>
        fs[FLOOKUP_DEF] >> rfs[] >>
        fs[Abbr`l2a`] >>
        match_mp_tac (GEN_ALL benv_bvs_free_vars_SUBSET) >>
        simp[] >> metis_tac[] ) >>
      fs[Abbr`bce`,ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
    simp[] >>
    map_every qunabbrev_tac[`X`,`Q`] >>
    disch_then(qspecl_then[`LENGTH vs`,`0`]mp_tac o CONJUNCT2) >>
    Q.PAT_ABBREV_TAC`csc' = compiler_state_tail_fupd X Y` >>
    `csc' = csc` by (
      simp[Abbr`csc'`,compiler_state_component_equality] ) >>
    simp[] >>
    simp_tac (srw_ss()++DNF_ss) [] >>
    simp[Abbr`bs1`] >>
    disch_then(mp_tac o CONV_RULE (RESORT_FORALL_CONV List.rev)) >>
    simp[LENGTH_NIL_SYM,FUPDATE_LIST_THM] >>
    disch_then(qspecl_then[`st`,`Block 3 [CodePtr a; bve]`,`bvs`,`vs`,`ns`,`defs`,`ns'`,`env'`]mp_tac) >>
    ntac 3 (pop_assum kall_tac) >>
    simp[Abbr`bcl`] >>
    `LENGTH bvs = LENGTH vs` by fs[EVERY2_EVERY] >>
    simp[code_for_return_def,Abbr`R`] >>
    disch_then(qx_choosel_then[`bvr`,`rfr`]strip_assume_tac) >>
    map_every qexists_tac [`bvr`,`rfr`] >>
    simp[Abbr`bs2`,Abbr`P`] >>
    PROVE_TAC[SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      rw[compile_def,LET_THM] >>
      pop_assum mp_tac >>
      Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
      Q.PAT_ABBREV_TAC`cs1 = compile cs0 e1` >>
      `∃cx. (compile cs1 e2).out = cx ++ cs.out` by (
        qspecl_then[`cs0`,`e1`]mp_tac(CONJUNCT1 compile_append_out) >>
        qspecl_then[`cs1`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
        rw[] >> rw[Abbr`cs0`] ) >> fs[] >>
      disch_then(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      first_x_assum (qspecl_then[`sm`,`cls`,`FST(sdt cs)`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE cx`]mp_tac) >>
      simp[Abbr`cs0`] >>
      simp[code_for_push_def] >>
      disch_then (qx_choosel_then [`bvs`,`rfs`] strip_assume_tac) >>
      fs[EVERY2_EVERY] >>
      `∃bv0 bv1. bvs = [bv0;bv1]` by (
        Cases_on `bvs` >> fs[] >>
        Cases_on `t` >> fs[LENGTH_NIL] ) >> fs[] >> rw[] >>
      fsrw_tac[DNF_ss][] >>
      qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
      qmatch_assum_abbrev_tac `Cv_bv pp v1 bv0` >>
      qspecl_then[`p2`,`v1`,`v2`,`v`,`bs0`,`bc0 ++ REVERSE cx`,`bc1`,`bs.stack`,`bv0`,`bv1`,`pp`]mp_tac prim2_to_bc_thm >>
      fs[Abbr`bs0`] >>
      `FST pp = (DRESTRICT sm (FDOM s'))` by rw[Abbr`pp`] >> fs[] >>
      imp_res_tac (CONJUNCT2 Cevaluate_store_SUBSET) >>
      imp_res_tac (CONJUNCT2 Cevaluate_Clocs) >> fs[] >>
      `all_Clocs v1 ⊆ FDOM sm ∧ all_Clocs v2 ⊆ FDOM sm` by PROVE_TAC[SUBSET_TRANS] >>
      fs[good_sm_DRESTRICT,FDOM_DRESTRICT] >>
      disch_then (Q.X_CHOOSE_THEN`bv`strip_assume_tac) >>
      map_every qexists_tac [`rfs`,`bv`] >> fs[] >>
      conj_tac >- (
        rw[Once RTC_CASES2] >> disj2_tac >>
        qmatch_assum_abbrev_tac `bc_next^* bs bs0` >>
        qexists_tac `bs0` >> rw[] >>
        qmatch_assum_abbrev_tac`bc_next bs0 bs11` >>
        qmatch_abbrev_tac `bc_next bs0 bs12` >>
        qsuff_tac `bs11 = bs12` >- metis_tac[bc_eval1_thm,optionTheory.SOME_11] >>
        rw[Abbr`bs11`,Abbr`bs12`] >>
        Q.PAT_ABBREV_TAC`x = Stack Y` >>
        qmatch_abbrev_tac `bump_pc bs2 = bs1` >>
        `bc_fetch bs2 = SOME x` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs2`] >>
          qexists_tac `bc0 ++ REVERSE cx` >>
          unabbrev_all_tac >> rw[] ) >>
        rw[bump_pc_def] >>
        unabbrev_all_tac >>
        srw_tac[ARITH_ss][SUM_APPEND,FILTER_APPEND,ADD1] >>
        rw[bc_state_component_equality]) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_incsz >>
        qmatch_assum_abbrev_tac `Cenv_bs c sm cls s' cenv cs.env (cs.sz + 2) bs0` >>
        qexists_tac`bs0 with <| stack := bs.stack |>` >>
        reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs0`] >>
        match_mp_tac Cenv_bs_pops >>
        map_every qexists_tac[`[bv1;bv0]`,`bs0`] >>
        simp[Abbr`bs0`,bc_state_component_equality] >>
        metis_tac[Cenv_bs_CTLet_bound] ) >>
      fs[good_cls_def] ) >>
    fs[compile_def,LET_THM] >>
    ntac 2 gen_tac >>
    strip_tac >> fs[] >>
    rw[] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s' c cenv rvs renv rsz` >>
    map_every qexists_tac[`bc0`,`code`,`cenv`,`renv`,`rsz`] >>
    simp[] >>
    metis_tac[EVERY2_EVERY,LENGTH_MAP]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >>
    ntac 2 strip_tac >>
    rpt gen_tac >> strip_tac >>
    fs[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    qabbrev_tac`nl = (compile cs0 exp).next_label` >>
    full_simp_tac std_ss [prove(``w::x::y::(compile a b).out=[w;x;y]++(compile a b).out``,rw[])] >>
    full_simp_tac std_ss [prove(``x::y::(compile a b).out=[x;y]++(compile a b).out``,rw[])] >>
    Q.PAT_ABBREV_TAC`lc3 = [Label x;y]` >>
    Q.PAT_ABBREV_TAC`lc2 = [Label x;y;z]` >>
    qspecl_then[`cs0`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be1`strip_assume_tac) >>
    simp[] >>
    simp_tac(srw_ss()++DNF_ss)[] >>
    simp[RIGHT_AND_FORALL_THM] >>
    CONV_TAC (RESORT_FORALL_CONV (op@ o partition (C mem ["args","klvs"] o fst o dest_var))) >>
    ntac 2 gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_state_sz_fupd (K ((compile cs0 e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_state_sz_fupd (K ((compile cs2 e2).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs2k = compiler_state_sz_fupd (K ((compile cs0 e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3k = compiler_state_sz_fupd (K ((compile cs2k e2).sz - 1)) Y` >>
    qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be2`strip_assume_tac) >>
    qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be3`strip_assume_tac) >>
    qspecl_then[`cs2k`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be2k`strip_assume_tac) >>
    qspecl_then[`cs3k`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be3k`strip_assume_tac) >>
    `cs0.out = cs.out` by rw[Abbr`cs0`] >>
    `(compile cs3 e3).out = be3 ++ lc3 ++ be2 ++ lc2 ++ be1 ++ cs.out` by (
      simp[Abbr`cs3`,Abbr`cs2`]) >>
    `(compile cs3k e3).out = be3k ++ lc3 ++ be2k ++ lc2 ++ be1 ++ cs.out` by (
      simp[Abbr`cs3k`,Abbr`cs2k`]) >>
    simp[] >>
    qabbrev_tac`nl1 = nl + 1` >>
    qabbrev_tac`nl2 = nl + 2` >>
    qabbrev_tac `il = bs.inst_length` >>
    `FDOM s ⊆ FDOM s' ∧
     FDOM s' ⊆ FDOM s'' ∧
     FDOM s' ⊆ FDOM sm` by metis_tac[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >>
    reverse(Cases_on`∃bc10. code = REVERSE be1 ++ REVERSE lc2 ++ bc10`) >- (
      simp[Once SWAP_REVERSE] >>
      simp[Once SWAP_REVERSE] >>
      rw[] >> fs[] ) >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`sm`,`cls`,`cs`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be1`]mp_tac) >>
    fs[ALL_DISTINCT_APPEND] >>
    disch_then(CHOOSE_THEN strip_assume_tac o SIMP_RULE (srw_ss()) [code_for_push_def,LET_THM,Once Cv_bv_cases] o CONJUNCT1) >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    simp[FORALL_AND_THM] >>
    conj_tac >- (
      rw[Once SWAP_REVERSE] >>
      Cases_on `b1` >> fs[] >- (
        first_x_assum(qspecl_then[`sm`,`cls`,`cs2`,`bs1 with <| stack := bs.stack; pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                                 ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`,`REVERSE be2`]mp_tac) >>
        simp[Abbr`bs1`] >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >>
          conj_tac >- rw[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
          conj_tac >- metis_tac[SUBSET_TRANS] >>
          conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
          conj_tac >- fs[Abbr`cs2`,Abbr`cs1`,good_cls_def,Abbr`il`] >>
          conj_tac >- rw[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
          conj_tac >- rw[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
          conj_tac >- rw[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
          conj_tac >- (
            fs[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`,compile_sz] >>
            match_mp_tac Cenv_bs_imp_decsz >>
            qmatch_assum_abbrev_tac `Cenv_bs c sm cls s' cenv cs.env (cs.sz + 1) bs1` >>
            qexists_tac`bs1` >>
            reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs1`] >>
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`cs.sz+1`mp_tac) >>
            srw_tac[ARITH_ss][] ) >>
          fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`
                          ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`] >>
          rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
        simp[] >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        disch_then(mp_tac o CONJUNCT1) >>
        `FST(sdt cs2) = cs2` by ( rw[Abbr`cs2`,Abbr`cs1`] ) >>
        fs[] >> pop_assum kall_tac >>
        simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
        map_every qx_gen_tac[`rfs2`,`b2`] >> strip_tac >>
        map_every qexists_tac[`rfs2`,`b2`] >>
        qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
        qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
        `bc_next^* bs03 bs05` by (
          rw[RTC_eq_NRC] >>
          qexists_tac `SUC 0` >>
          rw[] >>
          `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs03`,Abbr`lc2`] >>
            qexists_tac`bc0 ++ REVERSE be1` >>
            rw[]) >>
          rw[bc_eval1_thm] >>
          rw[bc_eval1_def,Abbr`bs03`,LET_THM] >>
          rw[Abbr`bs05`,bc_state_component_equality] >>
          rw[bc_find_loc_def] >>
          qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
          `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
          pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          `ALL_DISTINCT (FILTER is_Label ls0)` by (
            fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
          qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
          fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
          conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
          lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
        conj_tac >- (
          qmatch_abbrev_tac`bc_next^* bs bs13` >>
          `bc_fetch bs11 = SOME (Jump (Lab nl2))` by (
            match_mp_tac bc_fetch_next_addr >>
            simp[Abbr`bs11`,Abbr`lc3`] >>
            Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
            qexists_tac`ls` >>
            rw[] ) >>
          `bc_next bs11 bs13` by (
            rw[bc_eval1_thm] >>
            rw[bc_eval1_def,Abbr`bs13`,Abbr`bs11`] >>
            rw[bc_state_component_equality] >>
            rw[bc_find_loc_def] >>
            Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be3` >>
            match_mp_tac bc_find_loc_aux_append_code >>
            match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
            qexists_tac`LENGTH ls` >>
            conj_tac >- (
              fsrw_tac[DNF_ss,ARITH_ss]
                [Abbr`ls`,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,MEM_FILTER,is_Label_rwt,EVERY_MEM
                ,Abbr`nl2`,Abbr`lc2`,Abbr`lc3`,Abbr`nl1`,Abbr`cs2`,MEM_MAP,between_def,Abbr`cs0`,Abbr`cs1`,Abbr`cs3`] >>
              rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
            lrw[TAKE_APPEND2,EL_APPEND2,FILTER_APPEND] ) >>
          metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
        simp[Abbr`il`] >>
        `cs2.sz = cs.sz` by (
          simp[Abbr`cs2`] >>
          simp[compile_sz,Abbr`cs0`] ) >>
        `cs2.env = cs.env` by rw[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- fs[Cenv_bs_def,s_refs_def] >>
        fs[good_cls_def] >>
        metis_tac[SUBMAP_TRANS] ) >>
      first_x_assum(qspecl_then[`sm`,`cls`,`cs3`,`bs1 with <| stack := bs.stack;
                                pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                               ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`,`REVERSE be3`]mp_tac) >>
      simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac[`P`,`Q`,`R`] >>
        conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- metis_tac[SUBSET_TRANS] >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        conj_tac >- fs[good_cls_def,UNCURRY,Abbr`il`] >>
        conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- (
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs c sm cls s' cenv cs.env (cs.sz + 1) bs1` >>
          qexists_tac`bs1` >>
          reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs1`]
          >- (
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`cs.sz+1`mp_tac) >>
            srw_tac[ARITH_ss][Abbr`cs3`,compile_sz,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] ) >>
          srw_tac[ARITH_ss][Abbr`cs3`,compile_sz,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] ) >>
        simp[Abbr`cs3`] >>
        fsrw_tac[DNF_ss,ARITH_ss]
          [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`cs1`,Abbr`lc3`
          ,compile_sz,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`,Abbr`nl1`,Abbr`nl2`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      simp[] >>
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      `FST(sdt cs3) = cs3` by (
        match_mp_tac EQ_SYM >>
        rw[Abbr`cs3`] >>
        simp[compiler_state_component_equality] >>
        simp[compile_nontail,compile_decl_NONE,Abbr`cs2`,Abbr`cs1`] ) >>
      fs[] >> pop_assum kall_tac >>
      simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
      map_every qx_gen_tac[`rfs3`,`b3`] >> strip_tac >>
      map_every qexists_tac[`rfs3`,`b3`] >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
      qmatch_assum_abbrev_tac`bc_next^* bs05 bs07` >>
      `bc_next^* bs03 bs05` by (
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs03`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1` >>
          rw[]) >>
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
          fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,is_Label_rwt,MEM_FILTER,Abbr`lc2`,Abbr`nl2`]) >>
        qmatch_abbrev_tac`bc_eval1 (bump_pc bs03) = SOME bs06` >>
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          fs[bc_fetch_def,Abbr`bs03`] >> rfs[REVERSE_APPEND] ) >>
        rw[bump_pc_def] >>
        rw[Abbr`bs03`] >>
        qmatch_abbrev_tac`bc_eval1 bs03 = SOME bs06` >>
        `bc_fetch bs03 = SOME (Jump (Lab nl1))` by (
          match_mp_tac bc_fetch_next_addr >>
          rw[Abbr`bs03`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
          rw[REVERSE_APPEND,FILTER_APPEND,SUM_APPEND] >>
          srw_tac[ARITH_ss][] ) >>
        rw[bc_eval1_def] >>
        rw[Abbr`bs03`,Abbr`bs06`,Abbr`bs05`] >>
        rw[bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        simp[Abbr`lc3`] >>
        Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
        qexists_tac`LENGTH ls + 1` >>
        lrw[Abbr`ls`,EL_APPEND2] >>
        lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
      conj_tac >- (
        qmatch_abbrev_tac`bc_next^* bs bs08` >>
        `bs08 = bs07` by (
          rw[Abbr`bs08`,Abbr`bs07`] >>
          rw[bc_state_component_equality] >>
          rw[FILTER_APPEND] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
      simp[Abbr`il`] >>
      `cs3.sz = cs.sz` by (
        simp[Abbr`cs2`,Abbr`cs3`] >>
        simp[compile_sz,Abbr`cs0`,Abbr`cs1`] ) >>
      `cs3.env = cs.env` by rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
      conj_tac >- fs[Cenv_bs_def,s_refs_def] >>
      fs[good_cls_def] >>
      metis_tac[SUBMAP_TRANS] ) >>

    rw[Once SWAP_REVERSE] >>
    Cases_on `b1` >> fs[] >- (
      first_x_assum(qspecl_then[`sm`,`cls`,`cs2k`,`bs1 with <| stack := bs.stack; pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2) |>`
                               ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2`,`REVERSE be2k`]mp_tac) >>
      simp[Abbr`bs1`] >>
      qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        conj_tac >- rw[Abbr`cs2k`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- metis_tac[SUBSET_TRANS] >>
        conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
        conj_tac >- fs[Abbr`cs2k`,Abbr`cs1`,good_cls_def,Abbr`il`] >>
        conj_tac >- rw[Abbr`cs2k`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- rw[Abbr`cs2k`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- rw[Abbr`cs2k`,Abbr`cs1`,Abbr`cs0`] >>
        conj_tac >- (
          fs[Abbr`cs2k`,Abbr`cs1`,Abbr`cs0`,compile_sz] >>
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs c sm cls s' cenv cs.env (cs.sz + 1) bs1` >>
          qexists_tac`bs1` >>
          reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs1`] >>
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`cs.sz+1`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2k`
                        ,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`] >>
        rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
      simp[] >>
      map_every qunabbrev_tac [`P`,`Q`,`R`] >>
      disch_then(mp_tac o CONJUNCT2) >>
      simp_tac(srw_ss()++DNF_ss)[] >>
      disch_then(qspecl_then[`env0`,`ns`,`defs`,`xs`,`vs`,`klvs`,`blvs`,`benv`,`ret`,`args`,`cl`,`st`]mp_tac) >>
      Q.PAT_ABBREV_TAC`cs2k' = compiler_state_tail_fupd X Y` >>
      `cs2k' = cs2k` by ( rw[Abbr`cs2k`,Abbr`cs2k'`] ) >> pop_assum SUBST1_TAC >> qunabbrev_tac`cs2k'` >>
      simp[] >>
      simp[Abbr`lc3`]

      simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
      map_every qx_gen_tac[`rfs2`,`b2`] >> strip_tac >>
      map_every qexists_tac[`rfs2`,`b2`] >>
      qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
      qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
      `bc_next^* bs03 bs05` by (
        rw[RTC_eq_NRC] >>
        qexists_tac `SUC 0` >>
        rw[] >>
        `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs03`,Abbr`lc2`] >>
          qexists_tac`bc0 ++ REVERSE be1` >>
          rw[]) >>
        rw[bc_eval1_thm] >>
        rw[bc_eval1_def,Abbr`bs03`,LET_THM] >>
        rw[Abbr`bs05`,bc_state_component_equality] >>
        rw[bc_find_loc_def] >>
        qmatch_abbrev_tac`bc_find_loc_aux ls il nl 0 = SOME (next_addr il ls0)` >>
        `∃ls1. ls = ls0 ++ ls1` by rw[Abbr`ls`,Abbr`ls0`] >>
        pop_assum SUBST1_TAC >> qunabbrev_tac`ls` >>
        match_mp_tac bc_find_loc_aux_append_code >>
        match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
        `ALL_DISTINCT (FILTER is_Label ls0)` by (
          fs[ALL_DISTINCT_APPEND,FILTER_APPEND] ) >>
        qexists_tac`LENGTH bc0 + LENGTH be1 + 2` >>
        fsrw_tac[ARITH_ss][Abbr`ls0`,Abbr`lc2`] >>
        conj_tac >- lrw[EL_DROP,EL_CONS,EL_APPEND2] >>
        lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
      conj_tac >- (
        qmatch_abbrev_tac`bc_next^* bs bs13` >>
        `bc_fetch bs11 = SOME (Jump (Lab nl2))` by (
          match_mp_tac bc_fetch_next_addr >>
          simp[Abbr`bs11`,Abbr`lc3`] >>
          Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
          qexists_tac`ls` >>
          rw[] ) >>
        `bc_next bs11 bs13` by (
          rw[bc_eval1_thm] >>
          rw[bc_eval1_def,Abbr`bs13`,Abbr`bs11`] >>
          rw[bc_state_component_equality] >>
          rw[bc_find_loc_def] >>
          Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be3` >>
          match_mp_tac bc_find_loc_aux_append_code >>
          match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
          qexists_tac`LENGTH ls` >>
          conj_tac >- (
            fsrw_tac[DNF_ss,ARITH_ss]
              [Abbr`ls`,FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,MEM_FILTER,is_Label_rwt,EVERY_MEM
              ,Abbr`nl2`,Abbr`lc2`,Abbr`lc3`,Abbr`nl1`,Abbr`cs2`,MEM_MAP,between_def,Abbr`cs0`,Abbr`cs1`,Abbr`cs3`] >>
            rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
          lrw[TAKE_APPEND2,EL_APPEND2,FILTER_APPEND] ) >>
        metis_tac[RTC_TRANSITIVE,transitive_def,RTC_SUBSET] ) >>
      simp[Abbr`il`] >>
      `cs2.sz = cs.sz` by (
        simp[Abbr`cs2`] >>
        simp[compile_sz,Abbr`cs0`] ) >>
      `cs2.env = cs.env` by rw[Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
      conj_tac >- fs[Cenv_bs_def,s_refs_def] >>
      fs[good_cls_def] >>
      metis_tac[SUBMAP_TRANS] ) >>
    first_x_assum(qspecl_then[`sm`,`cls`,`cs3`,`bs1 with <| stack := bs.stack;
                              pc := next_addr il (bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3) |>`
                             ,`bce`,`bcr`,`bc0 ++ REVERSE be1 ++ REVERSE lc2 ++ REVERSE be2 ++ REVERSE lc3`,`REVERSE be3`]mp_tac) >>
    simp[Abbr`bs1`] >>
    qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
      conj_tac >- metis_tac[SUBSET_TRANS] >>
      conj_tac >- metis_tac[Cevaluate_Clocs,FST] >>
      conj_tac >- fs[good_cls_def,UNCURRY,Abbr`il`] >>
      conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
      conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
      conj_tac >- rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_decsz >>
        qmatch_assum_abbrev_tac `Cenv_bs c sm cls s' cenv cs.env (cs.sz + 1) bs1` >>
        qexists_tac`bs1` >>
        reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs1`]
        >- (
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`cs.sz+1`mp_tac) >>
          srw_tac[ARITH_ss][Abbr`cs3`,compile_sz,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] ) >>
        srw_tac[ARITH_ss][Abbr`cs3`,compile_sz,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] ) >>
      simp[Abbr`cs3`] >>
      fsrw_tac[DNF_ss,ARITH_ss]
        [FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,Abbr`cs2`,Abbr`cs1`,Abbr`lc3`
        ,compile_sz,FILTER_REVERSE,ALL_DISTINCT_REVERSE,Abbr`lc2`,Abbr`nl`,between_def,MEM_MAP,Abbr`cs0`,Abbr`nl1`,Abbr`nl2`] >>
      rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
    simp[] >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >>
    `FST(sdt cs3) = cs3` by (
      match_mp_tac EQ_SYM >>
      rw[Abbr`cs3`] >>
      simp[compiler_state_component_equality] >>
      simp[compile_nontail,compile_decl_NONE,Abbr`cs2`,Abbr`cs1`] ) >>
    fs[] >> pop_assum kall_tac >>
    simp_tac(srw_ss()++DNF_ss)[code_for_push_def,LET_THM] >>
    map_every qx_gen_tac[`rfs3`,`b3`] >> strip_tac >>
    map_every qexists_tac[`rfs3`,`b3`] >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs03` >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs07` >>
    `bc_next^* bs03 bs05` by (
      `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs03`,Abbr`lc2`] >>
        qexists_tac`bc0 ++ REVERSE be1` >>
        rw[]) >>
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
        fsrw_tac[DNF_ss,ARITH_ss][EVERY_MEM,between_def,is_Label_rwt,MEM_FILTER,Abbr`lc2`,Abbr`nl2`]) >>
      qmatch_abbrev_tac`bc_eval1 (bump_pc bs03) = SOME bs06` >>
      `bc_fetch bs03 = SOME (JumpIf (Lab nl))` by (
        fs[bc_fetch_def,Abbr`bs03`] >> rfs[REVERSE_APPEND] ) >>
      rw[bump_pc_def] >>
      rw[Abbr`bs03`] >>
      qmatch_abbrev_tac`bc_eval1 bs03 = SOME bs06` >>
      `bc_fetch bs03 = SOME (Jump (Lab nl1))` by (
        match_mp_tac bc_fetch_next_addr >>
        rw[Abbr`bs03`,Abbr`lc2`] >>
        qexists_tac`bc0 ++ REVERSE be1 ++ [JumpIf (Lab nl)]` >>
        rw[REVERSE_APPEND,FILTER_APPEND,SUM_APPEND] >>
        srw_tac[ARITH_ss][] ) >>
      rw[bc_eval1_def] >>
      rw[Abbr`bs03`,Abbr`bs06`,Abbr`bs05`] >>
      rw[bc_state_component_equality] >>
      rw[bc_find_loc_def] >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_append_code >>
      match_mp_tac bc_find_loc_aux_ALL_DISTINCT >>
      simp[Abbr`lc3`] >>
      Q.PAT_ABBREV_TAC`ls = X ++ REVERSE be2` >>
      qexists_tac`LENGTH ls + 1` >>
      lrw[Abbr`ls`,EL_APPEND2] >>
      lrw[TAKE_APPEND2,FILTER_APPEND] ) >>
    conj_tac >- (
      qmatch_abbrev_tac`bc_next^* bs bs08` >>
      `bs08 = bs07` by (
        rw[Abbr`bs08`,Abbr`bs07`] >>
        rw[bc_state_component_equality] >>
        rw[FILTER_APPEND] ) >>
      metis_tac[RTC_TRANSITIVE,transitive_def] ) >>
    simp[Abbr`il`] >>
    `cs3.sz = cs.sz` by (
      simp[Abbr`cs2`,Abbr`cs3`] >>
      simp[compile_sz,Abbr`cs0`,Abbr`cs1`] ) >>
    `cs3.env = cs.env` by rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`,Abbr`cs0`] >>
    conj_tac >- fs[Cenv_bs_def,s_refs_def] >>
    fs[good_cls_def] >>
    metis_tac[SUBMAP_TRANS] ) >>

    xxx)
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    simp[code_for_push_def] >>
    rw[Once SWAP_REVERSE] >>
    qexists_tac`bs.refs` >>
    rw[RTC_eq_NRC] >>
    TRY (qexists_tac`0` >>rw[]) >>
    TRY (qmatch_abbrev_tac `Cenv_bs c sm cls A B C D E` >>
         qmatch_assum_abbrev_tac `Cenv_bs c sm cls A B C D E'` >>
         qsuff_tac`E = E'`>-rw[] >>
         unabbrev_all_tac) >>
    rw[bc_state_component_equality] >>
    fs[good_cls_def]) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    strip_tac >>
    qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qabbrev_tac`cs0 = compile cs exp` >>
    qspecl_then[`cs0`,`exps`]mp_tac(FOLDL_compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    POP_ASSUM_LIST(MAP_EVERY ASSUME_TAC) >>
    first_x_assum(qspecl_then[`sm`,`cls`,`s'`,`v`,`cs`,`bs`,`bce`,`bcr`,`bc0`,`REVERSE be`]mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧
     FDOM s' ⊆ FDOM s'' ∧
     FDOM s' ⊆ FDOM sm` by PROVE_TAC[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >>
    simp[] >>
    fs[ALL_DISTINCT_APPEND] >>
    rfs[Abbr`cs0`] >>
    qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE(std_ss)[Once SWAP_REVERSE]) >
    `FST (sdt cs) = cs` by rw[compiler_state_component_equality] >>
    fs[REVERSE_APPEND] >>
    disch_then(mp_tac o CONJUNCT1) >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`rfs`,`bv`] >>
    strip_tac >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    first_x_assum(qspecl_then[`sm`,`cls`,`compile cs exp`,`bs1`,`bce`,`bcr`,`bc0 ++ REVERSE be`,`REVERSE bes`]mp_tac) >>
    simp[Abbr`bs1`,compile_nontail] >>
    qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
      conj_tac >- PROVE_TAC[Cevaluate_Clocs,FST] >>
      fs[REVERSE_APPEND,compile_sz] >>
      match_mp_tac compile_labels_lemma >> fs[] >>
      map_every qexists_tac[`cs`,`exp`,`bc0`] >>
      simp[]) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    simp[code_for_push_def] >>
    fsrw_tac[DNF_ss][] >>
    map_every qx_gen_tac[`bvs`,`rf`] >>
    strip_tac >>
    map_every qexists_tac[`bv::bvs`,`rf`] >>
    qmatch_assum_abbrev_tac`bc_next^* bs bs1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs1 bs2` >>
    conj_tac >- (
      qmatch_abbrev_tac `bc_next^* bs bs3` >>
      qsuff_tac `bs2 = bs3` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      rw[Abbr`bs2`,Abbr`bs3`,bc_state_component_equality,REVERSE_APPEND] ) >>
    qpat_assum`X = vs'`(assume_tac o SYM) >>
    `(compile cs exp).sz = cs.sz + 1` by rw[compile_sz] >>
    fsrw_tac[ARITH_ss][EVERY2_EVERY,ADD1] >> rfs[] >>
    conj_tac >- (
      match_mp_tac (MP_CANON (GEN_ALL (CONJUNCT1 (SPEC_ALL Cv_bv_SUBMAP)))) >> simp[] >>
      qexists_tac `DRESTRICT sm (FDOM s')` >>
      simp[] >>
      conj_tac >- metis_tac[DRESTRICT_SUBSET_SUBMAP] >>
      fs[SUBMAP_DEF,DRESTRICT_DEF,good_cls_def,UNCURRY,FEVERY_DEF] ) >>
    conj_tac >- (
      qmatch_abbrev_tac `Cenv_bs c sm cls s2 cenv env0 sz0 bsx` >>
      qmatch_assum_abbrev_tac `Cenv_bs c sm cls s2 cenv env0 sz0 bsy` >>
      `bsx = bsy` by (
        rw[Abbr`bsx`,Abbr`bsy`,bc_state_component_equality,REVERSE_APPEND] ) >>
      rw[] ) >>
    fs[good_cls_def] >>
    metis_tac[SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  rw[] )

val _ = export_theory ()
