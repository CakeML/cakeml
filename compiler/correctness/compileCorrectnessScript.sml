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
  >- ( fs[LET_THM] )
  >- ( unabbrev_all_tac >> fs[] )
  >- (
    unabbrev_all_tac >> rw[] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] ))
val _ = export_rewrites["compile_decl_NONE"]

val cce_aux_decl_NONE = store_thm("cce_aux_decl_NONE",
  ``((cce_aux c s x).decl = NONE) = (s.decl = NONE)``,
  Cases_on `x` >>
  rw[cce_aux_def] >>
  qmatch_abbrev_tac `((FOLDL f a r).decl = NONE) = (s.decl = NONE)` >>
  `((λp. (p.decl = NONE) = (s.decl = NONE))) (FOLDL f a r)` by (
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
   (λv. case v of Block 0 vs => el_check n vs | _ => NONE)) ∧
  (lookup_ct sz st rs (CTRef n) =
   OPTION_BIND (el_check sz st)
   (λv. case v of Block 0 vs =>
     OPTION_BIND (el_check n vs)
     (λv. case v of RefPtr p => FLOOKUP rs p | _ => NONE)
     | _ => NONE))`
val _ = export_rewrites["lookup_ct_def"]

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
     else ∃j p jxs jl je jenv. (find_index x ns 0 = SOME j) ∧
       (bv = RefPtr p) ∧
       (EL j defs = (jxs,INR jl)) ∧
       (FLOOKUP c jl = SOME je) ∧
       (FLOOKUP (SND(SND(SND pp))) p = SOME (jenv,ns,defs,j)) ∧
       fmap_rel (syneq c) jenv (DRESTRICT env (free_vars c je DIFF set jxs DIFF set ns)))
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
       (λCv b. case lookup_ct sz bs.stack bs.refs b of NONE => F
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
  ``∀bs bc0 code bc1 cs b bv bs'.
      ((compile_varref cs b).out = REVERSE code ++ cs.out) ∧
      (bs.code = bc0 ++ code ++ bc1) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      (lookup_ct cs.sz bs.stack bs.refs b = SOME bv) ∧
      (bs' = bs with <| stack := bv::bs.stack ; pc := next_addr bs.inst_length (bc0 ++ code)|>)
      ⇒
      bc_next^* bs bs'``,
  ntac 5 gen_tac >> Cases >> rw[] >>
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
  strip_tac >- rw[compile_def,LET_THM] >>
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
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] )
val _ = export_rewrites["compile_env"]

val FOLDL_compile_env = store_thm("FOLDL_compile_env",
  ``(FOLDL compile cs exps).env = cs.env``,
  qho_match_abbrev_tac`P (FOLDL compile cs exps)` >>
  match_mp_tac FOLDL_invariant >>
  rw[Abbr`P`])
val _ = export_rewrites["FOLDL_compile_env"]

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

val compile_varref_append_out = store_thm("compile_varref_append_out",
  ``∀cs b. ∃bc. ((compile_varref cs b).out = bc ++ cs.out) ∧ (EVERY ($~ o is_Label) bc)``,
  ho_match_mp_tac compile_varref_ind >> rw[])

val compile_decl_append_out = store_thm("compile_decl_append_out",
  ``∀env0 a vs. ∃bc. ((FST (compile_decl env0 a vs)).out = bc ++ (FST a).out) ∧ (EVERY ($~ o is_Label) bc)``,
  rw[compile_decl_def] >>
  qho_match_abbrev_tac `∃bc. ((FST (FOLDL f a vs)).out = bc ++ (FST a).out) ∧ P bc` >>
  qsuff_tac `(λx. ∃bc. ((FST x).out = bc ++ (FST a).out) ∧ P bc) (FOLDL f a vs)` >- rw[] >>
  match_mp_tac FOLDL_invariant >> rw[Abbr`P`] >>
  PairCases_on `x` >> fs[] >>
  simp[Abbr`f`] >>
  qspecl_then[`x0`,`x0.env ' y`]mp_tac compile_varref_append_out >>
  rw[] >> fs[] >>
  BasicProvers.EVERY_CASE_TAC >> fs[])

val compile_closures_append_out = store_thm("compile_closures_append_out",
  ``∀nz s defs. ∃bc. ((compile_closures nz s defs).out = bc ++ s.out) ∧ (EVERY ($~ o is_Label) bc)``,
  rpt gen_tac >>
  qho_match_abbrev_tac`∃bc. P (compile_closures nz s defs) s bc` >>
  rw[compile_closures_def,LET_THM] >>
  SIMPLE_QUANT_ABBREV_TAC[select_fun_constant``num_fold``1"f"] >>
  `∃bc. P (num_fold f'' s nz) s bc` by (
    qid_spec_tac `s` >>
    Induct_on `nz` >> rw[Once num_fold_def] >- rw[Abbr`P`] >>
    `∃bc. P (f'' s) s bc` by rw[Abbr`f''`,Abbr`P`] >>
    fs[Abbr`P`] >> metis_tac[APPEND_ASSOC,EVERY_APPEND] ) >>
  qabbrev_tac`p = (FOLDL push_lab (num_fold f'' s nz,0,[]) defs)` >>
  `(λx. ∃bc. P (FST x) s bc) p` by (
    qunabbrev_tac`p` >>
    match_mp_tac FOLDL_invariant >>
    fs[] >> conj_tac >- PROVE_TAC[] >>
    qx_gen_tac`x` >> PairCases_on`x` >>
    qx_gen_tac`y` >> PairCases_on`y` >>
    Cases_on `y1` >> rw[push_lab_def,LET_THM,Abbr`P`] >>
    fs[]) >>
  PairCases_on `p` >> fs[] >>
  Q.PAT_ABBREV_TAC`q = FOLDL (cons_closure X Y) (p0,1) Z` >>
  `(λx. ∃bc. P (FST x) s bc) q` by(
    qunabbrev_tac`q` >>
    match_mp_tac FOLDL_invariant >>
    fs[] >> conj_tac >- PROVE_TAC[] >>
    Cases >> Cases >>
    rw[cons_closure_def,LET_THM] >>
    Q.PAT_ABBREV_TAC `z = FOLDL (emit_ec s.sz) Y Z` >>
    `(λx. ∃bc. P x s bc) z` by (
      qunabbrev_tac`z` >>
      match_mp_tac FOLDL_invariant >>
      fs[] >> conj_tac >- fs[Abbr`P`] >>
      gen_tac >>
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

val compile_append_out = store_thm("compile_append_out",
  ``(∀cs exp. ∃bc. ((compile cs exp).out = bc ++ cs.out) ∧
                   cs.next_label ≤ (compile cs exp).next_label ∧
                   ALL_DISTINCT (FILTER is_Label bc) ∧
                   EVERY (between cs.next_label (compile cs exp).next_label) (MAP dest_Label (FILTER is_Label bc))) ∧
    (∀env0 sz1 exp n cs xs. ∃bc. ((compile_bindings env0 sz1 exp n cs xs).out = bc ++ cs.out) ∧
                   cs.next_label ≤ (compile_bindings env0 sz1 exp n cs xs).next_label ∧
                   ALL_DISTINCT (FILTER is_Label bc) ∧
                   EVERY (between cs.next_label (compile_bindings env0 sz1 exp n cs xs).next_label) (MAP dest_Label (FILTER is_Label bc)))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >- rw[] >>
    Q.PAT_ABBREV_TAC`p = compile_decl X Y Z` >>
    PairCases_on `p` >> rw[] >>
    qspecl_then[`q`,`(cs,r+1,q)`,`vs`]mp_tac compile_decl_append_out >>
    qspecl_then[`q`,`(cs,r+1,q)`,`vs`]mp_tac compile_decl_next_label_inc >>
    asm_simp_tac std_ss [FST] >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def] >>
    qspecl_then[`cs`,`cs.env ' vn`]mp_tac compile_varref_append_out >>
    rw[] >> fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    srw_tac[ETA_ss][] >>
    Q.PAT_ABBREV_TAC`a = compiler_state_tail_fupd X Y` >>
    qho_match_abbrev_tac `∃bc. (x::(FOLDL compile a es).out = bc ++ cs.out) ∧ P bc` >>
    qsuff_tac `∃bc. ((FOLDL compile a es).out = bc ++ cs.out) ∧ P bc` >- (
      rw[Abbr`P`] >> qexists_tac`x::bc` >> rw[Abbr`x`] ) >>
    qunabbrev_tac`P` >> simp[Abbr`x`] >>
    qho_match_abbrev_tac`P (FOLDL compile a es)` >>
    match_mp_tac FOLDL_invariant >>
    conj_tac >- rw[Abbr`a`,Abbr`P`] >>
    map_every qx_gen_tac[`x`,`e`] >> rw[Abbr`P`] >>
    first_x_assum (qspecl_then[`e`,`x`]mp_tac) >>
    simp[] >> disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    simp[ALL_DISTINCT_APPEND,FILTER_APPEND,MEM_FILTER] >>
    fsrw_tac[DNF_ss][EVERY_MEM,between_def,MEM_MAP,MEM_FILTER,is_Label_rwt] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fsrw_tac[ARITH_ss,ETA_ss,DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,EVERY_MEM,MEM_MAP,is_Label_rwt,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC ) >>
  strip_tac >- (
    simp[compile_def,LET_THM] >>
    rpt strip_tac >> fs[] >>
    Q.ISPECL_THEN[`if recp then LENGTH xs else 0`,`cs`,`defs`]strip_assume_tac compile_closures_append_out >>
    fs[FILTER_APPEND,ALL_DISTINCT_APPEND,GSYM FILTER_EQ_NIL,combinTheory.o_DEF]) >>
  strip_tac >- (
    rw[compile_def] >>
    Q.ISPECL_THEN[`0`,`cs`,`[(xs,cb)]`]strip_assume_tac compile_closures_append_out >>
    fs[GSYM FILTER_EQ_NIL,combinTheory.o_DEF] ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    Q.PAT_ABBREV_TAC`a = compiler_state_tail_fupd X Y` >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >> fsrw_tac[DNF_ss][] >> (
    qmatch_assum_abbrev_tac`b.out = bc ++ cs.out` >>
    Q.PAT_ABBREV_TAC`p = FOLDL compile Y Z` >>
    qho_match_abbrev_tac`∃bc. (X = bc ++ cs.out) ∧ P bc` >>
    qsuff_tac`∃bc. (p.out = bc ++ cs.out) ∧ P bc` >- (
      rw[Abbr`X`,Abbr`P`] >> fs[] ) >>
    simp[Abbr`P`] >>
    qho_match_abbrev_tac`P p` >>
    qunabbrev_tac`p` >>
    match_mp_tac FOLDL_invariant >>
    conj_tac >- rw[Abbr`P`] >>
    map_every qx_gen_tac[`x`,`e`] >> strip_tac >>
    first_x_assum(qspecl_then[`e`,`x`]mp_tac) >>
    pop_assum mp_tac >>
    fs[Abbr`P`] >>
    disch_then(Q.X_CHOOSE_THEN`bc1`strip_assume_tac) >>
    disch_then(Q.X_CHOOSE_THEN`bc2`strip_assume_tac) >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >> fs[]) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC) >>
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
    disch_then(Q.X_CHOOSE_THEN`bc2`strip_assume_tac) >>
    first_x_assum (qspec_then`FST (sdt cs)`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs3` by (
      unabbrev_all_tac >> rfs[] >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cs4 = compiler_state_sz_fupd X Y` >>
    `cs4 = cs2` by (
      unabbrev_all_tac >> rw[] ) >>
    BasicProvers.VAR_EQ_TAC >>
    pop_assum kall_tac >>
    disch_then(Q.X_CHOOSE_THEN`bc3`strip_assume_tac) >>
    `cs1.out = bc ++ cs.out` by (
      rw[Abbr`cs1`,Abbr`cs0`] ) >>
    simp[] >>
    conj_tac >- (fs[Abbr`cs1`,Abbr`cs0`] >> DECIDE_TAC ) >>
    fsrw_tac[DNF_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,MEM_MAP,between_def] >>
    rw[] >> spose_not_then strip_assume_tac >> res_tac >>
    unabbrev_all_tac >> fs[] >> DECIDE_TAC) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >>
    fs[]) >>
  rw[compile_def])

val FOLDL_compile_append_out = store_thm("FOLDL_compile_append_out",
  ``∀cs exps. ∃bc. ((FOLDL compile cs exps).out = bc ++ cs.out) ∧
                   cs.next_label ≤ (FOLDL compile cs exps).next_label ∧
                   ALL_DISTINCT (FILTER is_Label bc) ∧
                   EVERY (between cs.next_label (FOLDL compile cs exps).next_label)
                     (MAP dest_Label (FILTER is_Label bc))``,
  rpt gen_tac >>
  qho_match_abbrev_tac`P (FOLDL compile cs exps)` >>
  match_mp_tac FOLDL_invariant >>
  conj_tac >- rw[Abbr`P`] >>
  map_every qx_gen_tac [`x`,`e`] >>
  qspecl_then[`x`,`e`]strip_assume_tac(CONJUNCT1 compile_append_out) >>
  rw[Abbr`P`] >>
  fsrw_tac[DNF_ss,ARITH_ss][FILTER_APPEND,ALL_DISTINCT_APPEND,MEM_FILTER,is_Label_rwt,EVERY_MEM,between_def,MEM_MAP] >>
  rw[] >> spose_not_then strip_assume_tac >> res_tac >> DECIDE_TAC)

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
  ``∀c sm cls s env renv rsz bs bs'.
    Cenv_bs c sm cls s env renv rsz bs ∧ (∃v p e. bs' = bs with <| stack := v::bs.stack; pc := p; exstack := e |>) ⇒
    Cenv_bs c sm cls s env renv (rsz+1) bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT] >> rw[] >>
  qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
  first_x_assum (qspec_then `z` mp_tac) >>
  BasicProvers.CASE_TAC >>
  imp_res_tac lookup_ct_imp_incsz >>
  rw[] )

val Cenv_bs_imp_decsz = store_thm("Cenv_bs_imp_decsz",
  ``∀c sm cls s env renv rsz bs bs'.
    Cenv_bs c sm cls s env renv (rsz+1) bs ∧
      (CTLet (rsz+1) ∉ FRANGE renv) ∧
      (∃v p e. bs = bs' with <| stack := v::bs'.stack; pc := p; exstack := e |>) ⇒
    Cenv_bs c sm cls s env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def,s_refs_def,FDOM_DRESTRICT] >> fs[] >>
  qmatch_assum_rename_tac `z ∈ FDOM env`[] >>
  first_x_assum (qspec_then `z` mp_tac) >>
  BasicProvers.CASE_TAC >>
  pop_assum mp_tac >>
  rw[lookup_ct_incsz] >>
  fs[FRANGE_DEF] >>
  PROVE_TAC[])

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
  Induct >> rw[] >- ( fs[Cenv_bs_def,s_refs_def] ) >>
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
  strip_tac >- rw[compile_def,LET_THM] >>
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
  strip_tac >- rw[compile_def,LET_THM] >>
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

val FOLDL_compile_sz = store_thm("FOLDL_compile_sz",
  ``∀exps cs. good_ecs cs.ecs ∧ BIGUNION (IMAGE free_labs (set exps)) ⊆ FDOM cs.ecs
    ⇒ ((FOLDL compile cs exps).sz = cs.sz + (LENGTH exps))``,
  Induct >> srw_tac[ARITH_ss][compile_sz])

val compile_varref_tail = store_thm("compile_varref_tail",
  ``∀s r. (compile_varref s r).tail = s.tail``,
  gen_tac >> Cases >> rw[])
val _ = export_rewrites["compile_varref_tail"]

val compile_decl_tail = store_thm("compile_decl_tail",
  ``∀env a vs. (FST (compile_decl env a vs)).tail = (FST a).tail``,
  rw[compile_decl_def] >>
  qho_match_abbrev_tac`(FST(FOLDL f a vs)).tail = (FST a).tail` >>
  qho_match_abbrev_tac`P (FOLDL f a vs)` >>
  match_mp_tac FOLDL_invariant >>
  unabbrev_all_tac >> simp[] >>
  qx_gen_tac`x`>>PairCases_on`x`>>
  qx_gen_tac`y`>>rw[]>>
  BasicProvers.EVERY_CASE_TAC>>fs[])
val _ = export_rewrites["compile_decl_tail"]

val compile_closures_tail = store_thm("compile_closures_tail",
  ``(compile_closures n s defs).tail = s.tail``,
  rw[compile_closures_def] >>
  `s'.tail = s.tail` by (
    qunabbrev_tac`s'` >>
    rpt (pop_assum kall_tac) >>
    qid_spec_tac`s` >>
    Induct_on `n` >>
    rw[Once num_fold_def] ) >>
  `($= s'.tail o compiler_state_tail o FST) (FOLDL push_lab (s',0,[]) defs)` by
  (
    match_mp_tac FOLDL_invariant >> simp[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    Cases_on`y1`>>rw[push_lab_def,LET_THM] ) >>
  `($= s''.tail o compiler_state_tail o FST) (FOLDL (cons_closure sz0 nk) (s'',1) (REVERSE ecs))` by (
    match_mp_tac FOLDL_invariant >> simp[] >>
    qx_gen_tac`x`>>PairCases_on`x` >>
    qx_gen_tac`y`>>PairCases_on`y` >>
    rw[LET_THM,cons_closure_def] >>
    qho_match_abbrev_tac`x0.tail = (FOLDL (emit_ec sz0) a b).tail` >>
    qho_match_abbrev_tac`P (FOLDL (emit_ec sz0) a b)` >>
    match_mp_tac FOLDL_invariant >>
    unabbrev_all_tac >> simp[] >>
    gen_tac >> Cases >> rw[emit_ec_def] ) >>
  qmatch_assum_abbrev_tac`X = (s'''',k'')` >>
  `(FST X).tail = s'''.tail` by (
    qunabbrev_tac`X` >>
    rpt (pop_assum kall_tac) >>
    qabbrev_tac`a = (s''',1)` >>
    qmatch_abbrev_tac`X = s'''.tail` >>
    qsuff_tac`X = (FST a).tail` >- rw[Abbr`a`] >>
    qunabbrev_tac`X` >>
    rpt (pop_assum kall_tac) >>
    qid_spec_tac`a` >>
    Induct_on`n` >>
    rw[Once num_fold_def] >>
    Cases_on `a` >> rw[update_refptr_def,LET_THM] ) >>
  qunabbrev_tac`X` >> fs[] >> rfs[] >>
  qmatch_abbrev_tac`(num_fold f a n).tail = b.tail` >>
  `b.tail = a.tail` by rw[Abbr`a`,Abbr`b`] >>
  pop_assum SUBST1_TAC >>
  qunabbrev_tac`f` >>
  rpt (pop_assum kall_tac) >>
  qid_spec_tac`a` >>
  Induct_on`n` >>
  rw[Once num_fold_def])
val _ = export_rewrites["compile_closures_tail"]

(*
val compile_tail = store_thm("compile_tail",
  (* this is not true *)
  ``(∀s e. (compile s e).tail = s.tail) ∧
    (∀env sz e n s xs.
      (compile_bindings env sz e n s xs).tail =
       case s.tail of
       | TCNonTail => TCNonTail
       | TCTail j k => TCTail j (k + n + LENGTH xs))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fs[UNCURRY]) >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC ) >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >>
    fs[] ) >>
  rw[compile_def] >>
  BasicProvers.EVERY_CASE_TAC
  )
  compile_def
*)

val compile_nontail = store_thm("compile_nontail",
  ``(∀s e. ((compile s e).tail = TCNonTail) = (s.tail = TCNonTail)) ∧
    (∀env sz e n s xs.
      ((compile_bindings env sz e n s xs).tail = TCNonTail) = (s.tail = TCNonTail))``,
  ho_match_mp_tac compile_ind >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> rw[] >> rw[UNCURRY] ) >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- rw[compile_def,LET_THM] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] ) >>
  rw[compile_def,LET_THM] )

val Cenv_bs_FUPDATE = store_thm("Cenv_bs_FUPDATE",
  ``∀c sm cls s env env0 sz0 bs n v bv bs'.
    Cenv_bs c sm cls s env env0 sz0 bs ∧
    Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c bs' cls) v bv ∧
    (bs' = bs with stack := bv::bs.stack)
    ⇒
    Cenv_bs c sm cls s (env |+ (n,v)) (env0 |+ (n,CTLet (sz0 + 1))) (sz0 + 1) bs'``,
  rw[Cenv_bs_def,s_refs_def] >>
  fs[fmap_rel_def] >>
  qx_gen_tac`x` >>
  Cases_on`x=n`>>fs[] >>
  strip_tac >>
  rw[FAPPLY_FUPDATE_THM] >>
  first_x_assum (qspec_then `x` mp_tac) >> rw[] >>
  Cases_on `lookup_ct sz0 bs.stack bs.refs (env0 ' x)` >> fs[] >>
  imp_res_tac lookup_ct_imp_incsz >>
  pop_assum (qspec_then`bv`mp_tac) >> rw[])

val Cenv_bs_DOMSUB = store_thm("Cenv_bs_DOMSUB",
  ``∀c sm cls s env k renv rsz bs.
    Cenv_bs c sm cls s env renv rsz bs ⇒
    Cenv_bs c sm cls s (env \\ k) (renv \\ k) rsz bs``,
  rw[Cenv_bs_def,fmap_rel_def,DOMSUB_FAPPLY_THM])

(*
val Cenv_bs_shadow = store_thm("Cenv_bs_shadow",
  ``∀c sm s env k renv rsz bs bs'.
    Cenv_bs c sm s env renv rsz bs ∧
    Cenv_bs c sm s (env \\ k) (renv \\ k) rsz bs' ∧
    (bs'.stack = bs.stack)
    ⇒
    Cenv_bs c sm s env renv rsz bs'``,
  rw[Cenv_bs_def,fmap_rel_def,DOMSUB_FAPPLY_THM] >>
  reverse(Cases_on`x=k`) >- metis_tac[] >> rw[] >>
  Cases_on `renv ' k` >- (
    res_tac >>
    qpat_assum`renv ' k = X`assume_tac >>
    fs[] >> rw[] >> fsrw_tac[ARITH_ss][] >>
    Cv_bv_l2a_mono
    Cv_bv_rules
    let val x = ref 0 in
      let val x = ref 1 in
        x := 2
      end
      !x
    end
*)

(*
val Cenv_bs_DOMSUB = store_thm("Cenv_bs_DOMSUB",
  ``∀c sm s env k v renv rsz bv bs bs'.
    Cenv_bs c sm s (env |+ (k,v)) (renv |+ (k,CTLet (rsz + 1))) (rsz + 1) bs ∧
    Cenv_bs c sm s env renv (rsz + 1) bs ∧
    (bs = bs' with stack := bv::bs'.stack)
    ⇒ Cenv_bs c sm s env renv rsz bs'``,
  rw[] >>
  imp_res_tac Cenv_bs_CTLet_bound >>
  fs[Cenv_bs_def,s_refs_def,fmap_rel_def] >>
  qx_gen_tac`x` >> strip_tac >>
  fs[lookup_ct_incsz,FAPPLY_FUPDATE_THM]
  first_x_assum (qspec_then`x` mp_tac) >>
  rw[lookup_ct_incsz,FAPPLY_FUPDATE_THM] >>
  fs[IN_FRANGE] >> PROVE_TAC[])
*)

(*
val Cenv_bs_change_store = store_thm("Cenv_bs_change_store",
  ``∀c sm s env renv rsz bs s'.
    Cenv_bs c sm s env renv rsz bs ∧
    s_refs c sm s' bs ⇒
    Cenv_bs c sm s' env renv rsz bs``,
  rw[Cenv_bs_def])
*)

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

(*
val Cv_bv_refs = store_thm("Cv_bv_refs",
  ``∀pp v bv. Cv_bv pp v bv ⇒
   ∀s c l2a rfs pp' rfs'.
     (pp = (s,c,l2a,rfs)) ∧
     (pp' = (s,c,l2a,rfs')) ∧
     (∀p. p ∉ FRANGE s ∧ p ∈ FDOM rfs ⇒ (FLOOKUP rfs' p = SOME (rfs ' p)))
     ⇒
    Cv_bv pp' v bv``,
  gen_tac >>
  ho_match_mp_tac Cv_bv_ind >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- rw[Once Cv_bv_cases] >>
  strip_tac >- (rw[Once Cv_bv_cases] >> fs[]) >>
  strip_tac >- (rw[] >> rw[Once Cv_bv_cases] >>
    fs[EVERY2_EVERY,EVERY_MEM,FORALL_PROD] ) >>
  rpt gen_tac >> strip_tac >> fs[] >>
  qx_gen_tac`rfs'` >> strip_tac >>
  simp[Once Cv_bv_cases] >>
  map_every qexists_tac[`bvs`,`e`,`i`,`j`,`l`,`xs`] >>
  Q.PAT_ABBREV_TAC`fvs = SET_TO_LIST (free_vars c e)` >>
  rpt BasicProvers.VAR_EQ_TAC >>
  Q.PAT_ABBREV_TAC`evs = FILTER X fvs` >>
  simp[] >>
  qx_gen_tac`i'` >>
  strip_tac >> fs[] >>
  qpat_assum`∀i. i < LENGTH evs ⇒ P`(qspec_then`i'`mp_tac) >>
  simp[] >> rw[] >> fs[] >> fs[FLOOKUP_DEF])
*)

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

val good_sm_DRESTRICT = store_thm("good_sm_DRESTRICT",
  ``good_sm sm ⇒ good_sm (DRESTRICT sm s)``,
  rw[INJ_DEF,IN_FRANGE,DRESTRICT_DEF] >>
  metis_tac[])

(*
val good_code_env_def = Define`
  good_code_env sm c =
  FEVERY (λ(l,e).
    Cexp_pred e ∧
    ∀c s env s' v ns defs xs vs n bc0 bs benv args st.
      Cevaluate c s (extend_rec_env env env ns defs xs vs) e (s', Rval v) ∧
      (EL (THE (find_index n ns 0)) defs = (xs, INR l)) ∧
      (LENGTH xs = LENGTH vs) ∧
      (bs.code = bc0 ++ [CallPtr]) ∧
      (bs.stack = CodePtr l::benv::args ++ Block closure_tag [CodePtr l; benv]::st) ∧
      (bs.pc = next_addr bs.inst_length bc0) ∧
      Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c bs) (CRecClos env ns defs n) (Block closure_tag [CodePtr l; benv]) ∧
      (* EVERY2 (Cv_bv (mk_pp sm c bs)) vs args ∧ implied by Cenv_bs? *)
      (* Cenv_bs c sm s (extend_rec_env env env ns defs xs vs) renv sz bs *)
      s_refs c sm s bs
      ⇒
      ∃bv rfs.
      let bs' = bs with <| stack := bv::st; pc := next_addr bs.inst_length bs.code; refs := rfs |> in
       bc_next^* bs bs' ∧
       Cv_bv (mk_pp (DRESTRICT sm (FDOM s')) c bs) v bv ∧
       s_refs c sm s' bs' ∧
       DRESTRICT bs.refs (COMPL (FRANGE (DRESTRICT sm (FDOM s)))) ⊑ DRESTRICT rfs (COMPL (FRANGE (DRESTRICT sm (FDOM s'))))
       (* Cenv_bs c sm s' env renv' sz' bs' *)
   ) c`
*)
val _ = Parse.overload_on("retbc",``λn az. [Stack (Pops n); Stack (Load 1); Stack (Store (az + 2)); Stack (Pops (az + 1)); Return]``)

val good_code_env_def = Define`
  good_code_env c d code =
  ALL_DISTINCT (FILTER is_Label code) ∧
  FEVERY (λ(l,e).
    Cexp_pred e ∧
    ALL_DISTINCT (binders e) ∧
    ∃cs vs ns xs k bc0 cc bc1.
      (FLOOKUP d l = SOME (vs,xs,ns,k)) ∧
      DISJOINT (set (binders e)) (vs ∪ set ns ∪ set xs) ∧
      good_ecs cs.ecs ∧ free_labs e ⊆ FDOM cs.ecs ∧
      (cs.env = FST(ITSET (bind_fv ns xs (LENGTH xs) k) (free_vars c e) (FEMPTY,0,[]))) ∧
      (cs.sz = 0) ∧
      (cs.tail = TCTail (LENGTH xs) 0) ∧
      ((compile cs e).out = cc ++ cs.out) ∧
      (code = bc0 ++ Label l :: (REVERSE cc) ++
        (retbc (case (compile cs e).tail of TCTail j k => k + 1) (LENGTH xs)) ++ bc1)
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
    (bs.code = bc0 ++ retbc (LENGTH vs + 1) (LENGTH args) ++ bc1) ∧
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
  REWRITE_TAC[Once ADD_SYM] >>
  simp[GSYM DROP_DROP] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  rw[DROP_LENGTH_APPEND] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 1 (retbc (LENGTH vs + 1) (LENGTH args)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 2 (retbc (LENGTH vs + 1) (LENGTH args)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  simp_tac std_ss [bc_eval_stack_def] >>
  `LENGTH args + 2 + 1 = SUC(SUC(1 + LENGTH args))` by srw_tac[ARITH_ss][ADD1] >>
  pop_assum SUBST1_TAC >> simp_tac std_ss [DROP] >>
  `LENGTH args + 2 = SUC(SUC(LENGTH args))` by srw_tac[ARITH_ss][ADD1] >>
  pop_assum SUBST1_TAC >> simp_tac std_ss [TAKE] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  REWRITE_TAC[TAKE_LENGTH_APPEND] >>
  simp[GSYM DROP_DROP] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  REWRITE_TAC[DROP_LENGTH_APPEND] >>
  rw[bump_pc_def] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 3 (retbc (LENGTH vs + 1) (LENGTH args)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def] >>
  rw[bc_eval_stack_def] >>
  srw_tac[ARITH_ss][] >>
  rw[bump_pc_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC] >>
  REWRITE_TAC[DROP_LENGTH_APPEND] >>
  qmatch_abbrev_tac`bc_next^* bs1 bs2` >>
  qspecl_then[`bc0++(TAKE 4 (retbc (LENGTH vs + 1) (LENGTH args)))`,`bs1`]mp_tac bc_fetch_next_addr >>
  simp[Abbr`bs1`,FILTER_APPEND,SUM_APPEND] >>
  rw[Once RTC_CASES1] >> disj2_tac >>
  rw[bc_eval1_thm] >>
  rw[bc_eval1_def])

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

val compile_varref_with_tail = store_thm("compile_varref_with_tail",
  ``compile_varref (s with tail := x) y = compile_varref s y with tail := x``,
  Cases_on`y`>>rw[])
val compile_varref_with_decl = store_thm("compile_varref_with_decl",
  ``compile_varref (s with decl := x) y = compile_varref s y with decl := x``,
  Cases_on`y`>>rw[])
val _ = export_rewrites["compile_varref_with_tail","compile_varref_with_decl"]

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
  ``∀sm cls bs bce bc0 code s s' c env v renv rsz bc1 args bs' benv st cl ret.
    code_for_push sm cls bs bce bc0 code s s' c env [v] renv rsz ∧
    (bs.code = bc0 ++ code ++ retbc 1 (LENGTH args) ++ bc1) ∧
    (bs.stack = benv::CodePtr ret::(REVERSE args)++cl::st)
    ⇒
    code_for_return sm cls bs bce st ret v s s' c``,
    rw[code_for_push_def,code_for_return_def,LET_THM] >>
    qmatch_assum_rename_tac `Cv_bv pp v bv`["pp"] >>
    map_every qexists_tac [`bv`,`rf`] >>
    fs[Cenv_bs_def,s_refs_def,good_cls_def] >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    qspecl_then[`bs0`,`bs1`,`retbc 1 (LENGTH args) ++ bc1`]mp_tac (SIMP_RULE(srw_ss())[]RTC_bc_next_append_code) >>
    rw[] >>
    match_mp_tac (SIMP_RULE std_ss [transitive_def] RTC_TRANSITIVE) >>
    first_assum (exists_tac o rand o concl) >> fs[Abbr`bs0`] >>
    qpat_assum`bs.code = X`(assume_tac o SYM)>>fs[]>>
    match_mp_tac retbc_thm >>
    pop_assum(assume_tac o SYM) >>
    qexists_tac`bc0 ++ code` >> fs[Abbr`bs1`] >>
    qexists_tac`[]`>>fs[]>>
    qexists_tac`REVERSE args`>>fs[] >>
    rw[bc_state_component_equality])

val compile_labels_lemma = store_thm("compile_labels_lemma",
  ``∀cs exp bc0 cs1 cls1 code.
    (cs1 = compile cs exp) ∧
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
  qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
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
    first_x_assum(qspecl_then[`jxs`,`INR jl`,`k`,`x`]mp_tac) >>
    Cases_on`ns=[]`>>fs[find_index_def] >>
    imp_res_tac find_index_LESS_LENGTH >> fs[] >>
    qpat_assum`X = FDOM jenv`(assume_tac o SYM) >>
    fs[FLOOKUP_DEF,optionTheory.OPTREL_def,FDOM_DRESTRICT] >>
    rw[MEM_EL] >>
    qmatch_abbrev_tac`A ∨ B` >>
    Cases_on`A`>>fs[Abbr`B`] >>
    `k ∈ FDOM env1 ∧ k ∈ FDOM env2` by (
      pop_assum(strip_assume_tac o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >>
      metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION] ) >> fs[] >>
    ntac 2 (pop_assum mp_tac) >>
    pop_assum(strip_assume_tac o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >>
    rw[DRESTRICT_DEF,MEM_EL] >>
    metis_tac[free_vars_DOMSUB,SUBSET_DEF,IN_UNION]) >>
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
    `∃n. (env0 ' x = CTRef n) ∧ n < LENGTH ecs ∧ (EL n ecs = (x, CERef (jx + 1)))` by (
      fs[MEM_EL] >>
      qmatch_assum_rename_tac`m < LENGTH ecs`[] >>
      qexists_tac`m`>>rw[] >>
      simp[Abbr`env0`] >>
      qabbrev_tac`fm = FEMPTY |++ ls1` >>
      qho_match_abbrev_tac`P ((fm |++ ls2) ' (EL n ns))` >>
      match_mp_tac FUPDATE_LIST_ALL_DISTINCT_APPLY_MEM >>
      simp_tac std_ss [Abbr`ls2`,GENLIST_EL_MAP,MAP_GENLIST,combinTheory.o_DEF,LIST_TO_SET_GENLIST,IMAGE_EL_count_LENGTH,Abbr`P`] >>
      conj_tac >- rw[FILTER_ALL_DISTINCT,Abbr`fvl`,ALL_DISTINCT_SET_TO_LIST,Abbr`ecs`,MAP_MAP_o,combinTheory.o_DEF,Abbr`envs`] >>
      simp[] >>
      qexists_tac`m` >>
      qpat_assum`X = EL m ecs`(assume_tac o SYM) >>
      simp[] ) >>
    simp[]

fun filter_asms P = POP_ASSUM_LIST (MAP_EVERY ASSUME_TAC o List.rev o List.filter P)

val compile_val = store_thm("compile_val",
  ``(∀c d s env exp res. Cevaluate c d s env exp res ⇒
      ∀sm cls s' v cs bs bce bcr bc0 code bc1.
        Cexp_pred exp ∧
        DISJOINT (set (binders exp)) (FDOM cs.env) ∧ ALL_DISTINCT (binders exp) ∧
        BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s ∧
        BIGUNION (IMAGE all_Clocs (FRANGE s)) ⊆ FDOM s ∧
        (res = (s', Rval v)) ∧
        good_sm sm ∧ FDOM s' ⊆ FDOM sm ∧
        good_cls c sm s (bs with code := bce) cls ∧
        good_ecs cs.ecs ∧ free_labs exp ⊆ FDOM cs.ecs ∧
        (bce ++ bcr = bs.code) ∧ good_code_env c d bce ∧
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (free_vars c exp ⊆ FDOM cs.env) ∧
        Cenv_bs c sm cls s (DRESTRICT env (FDOM cs.env)) cs.env cs.sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      (let cs0 = FST(sdt cs) in
       ((compile cs0 exp).out = REVERSE code ++ cs.out) ⇒
       code_for_push sm cls bs bce bc0 code s s' c (DRESTRICT env (FDOM cs.env)) [v] cs.env cs.sz) ∧
      (∀az.
        let cs0 = cs with <| tail := TCTail az 0; decl := NONE |> in
        let cs1 = compile cs0 exp in let n = case cs1.tail of TCTail j k => k+1 in
        (cs.sz = 0) ∧ (cs1.out = REVERSE code ++ cs.out) ∧ (∃bc2. bc1 = retbc n az ++ bc2) ⇒
        ∀env0 ns defs xs vs benv ret args cl st.
        (az = LENGTH args) ∧
        (env = extend_rec_env env0 env0 ns defs xs vs) ∧
        EVERY2 (Cv_bv (mk_pp (DRESTRICT sm (FDOM s)) c (bs with code := bce) cls)) vs args ∧
        (bs.stack = benv::CodePtr ret::(REVERSE args)++cl::st)
        ⇒
        code_for_return sm cls bs bce st ret v s s' c)) ∧
    (∀c d s env exps ress. Cevaluate_list c d s env exps ress ⇒
      ∀sm cls s' vs cs bs bce bcr bc0 code bc1.
        EVERY Cexp_pred exps ∧
        DISJOINT (set (FLAT (MAP binders exps))) (FDOM cs.env) ∧ ALL_DISTINCT (FLAT (MAP binders exps)) ∧
        BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s ∧
        BIGUNION (IMAGE all_Clocs (FRANGE s)) ⊆ FDOM s ∧
        (ress = (s', Rval vs)) ∧
        good_sm sm ∧ FDOM s' ⊆ FDOM sm ∧
        good_ecs cs.ecs ∧ free_labs_list exps ⊆ FDOM cs.ecs ∧
        (bce ++ bcr = bs.code) ∧ good_code_env c d bce ∧
        (bs.code = bc0 ++ code ++ bc1) ∧
        (bs.pc = next_addr bs.inst_length bc0) ∧
        (BIGUNION (IMAGE (free_vars c) (set exps)) ⊆ FDOM cs.env) ∧
        Cenv_bs c sm cls s (DRESTRICT env (FDOM cs.env)) cs.env cs.sz (bs with code := bce) ∧
        ALL_DISTINCT (FILTER is_Label bc0) ∧
        EVERY (combin$C $< cs.next_label o dest_Label) (FILTER is_Label bc0)
        ⇒
      ((cs.tail = TCNonTail) ∧ (cs.decl = NONE) ∧ ((FOLDL compile cs exps).out = REVERSE code ++ cs.out) ⇒
        code_for_push sm cls bs bce bc0 code s s' c (DRESTRICT env (FDOM cs.env)) vs cs.env cs.sz))``,
  ho_match_mp_tac Cevaluate_strongind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    ntac 4 gen_tac >> qx_gen_tac`n` >> strip_tac >> simp[] >>
    rpt gen_tac >> strip_tac >> simp[compile_def] >>
    conj_asm1_tac >- (
      fs[code_for_push_def,Cenv_bs_def,fmap_rel_def,FDOM_DRESTRICT] >>
      first_assum (qspec_then `n` mp_tac) >>
      REWRITE_TAC[Once option_case_NONE_F] >> simp[] >>
      disch_then(Q.X_CHOOSE_THEN`x`strip_assume_tac) >>
      strip_tac >>
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
    qmatch_assum_abbrev_tac `code_for_push sm cls bs bce bc0 code s s c cenv v renv rsz` >>
    map_every qexists_tac [`bc0`,`code`,`cenv`,`renv`,`rsz`] >>
    simp[bc_state_component_equality] >>
    metis_tac[]) >>
  strip_tac >- (
    simp[] >>
    rpt gen_tac >> strip_tac >>
    conj_asm1_tac >- (
      Cases_on`l`>>rw[compile_def,LET_THM,code_for_push_def]>>
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
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compile X (CLit l)` >>
    qmatch_assum_abbrev_tac`(X = Y) ⇒ P` >>
    strip_tac >>
    `(X = Y) ∧ (cs1.tail = TCTail az 0)` by (
      Cases_on`l`>>fs[Abbr`cs1`,compile_def]) >>
    fs[Abbr`X`,Abbr`Y`,Abbr`P`] >> rw[] >>
    match_mp_tac code_for_push_return >> simp[] >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s c env v renv rsz` >>
    map_every qexists_tac [`bc0`,`code`,`env`,`renv`,`rsz`] >> rw[] ) >>
  strip_tac >- (
    fsrw_tac[ETA_ss][FOLDL_UNION_BIGUNION] >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    simp[compile_def,LET_THM] >>
    fsrw_tac[ETA_ss][] >>
    conj_asm1_tac >- (
      qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
      strip_tac >>
      `∃cx. (FOLDL compile cs0 exps).out = cx ++ cs.out` by (
        qspecl_then[`cs0`,`exps`]mp_tac FOLDL_compile_append_out >>
        rw[Abbr`cs0`] ) >> fs[] >>
      qpat_assum`X = REVERSE code`(assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
      qmatch_assum_abbrev_tac `code = ls0 ++ [x]` >>
      first_x_assum (qspecl_then[`sm`,`cls`,`cs0`,`bs`,`bce`,`bcr`,`bc0`,`ls0`]mp_tac) >>
      simp[Abbr`cs0`,Abbr`ls0`] >>
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
      rfs[FOLDL_compile_sz] >>
      reverse conj_tac >- fs[good_cls_def] >>
      qmatch_assum_abbrev_tac`Cenv_bs c sm cls s' cenv cs.env sz1 bs1` >>
      `Cenv_bs c sm cls s' cenv cs.env cs.sz (bs1 with stack := bs.stack)` by (
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
    gen_tac >> strip_tac >> fs[] >> rw[] >>
    match_mp_tac code_for_push_return >>
    simp[] >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s' c cenv v renv rsz` >>
    map_every qexists_tac[`bc0`,`code`,`cenv`,`renv`,`rsz`] >>
    simp[] ) >>
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
    rw[] ) >>
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
      fs[(Q.SPECL[`pp`,`CConv m vs`]Cv_bv_cases)] >>
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
      rw[bc_state_component_equality,Abbr`bs1`] ) >>
    first_x_assum(qspec_then`sm` kall_tac) >>
    fs[compile_def,LET_THM] >>
    rw[]>>fs[] >>
    match_mp_tac code_for_push_return >>
    qmatch_assum_abbrev_tac`code_for_push sm cls bs bce bc0 code s s' c cenv v cs.env csz` >>
    map_every qexists_tac[`bc0`,`code`,`cenv`,`cs.env`,`csz`] >>
    rw[] ) >>
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
    gen_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_env_fupd X Y` >>
    qspecl_then[`cs1`,`exp'`](Q.X_CHOOSE_THEN`cy`strip_assume_tac)(CONJUNCT1 compile_append_out) >> fs[] >>
    fs[Abbr`cs1`] >>
    disch_then(strip_assume_tac o SIMP_RULE std_ss [Once SWAP_REVERSE]) >> fs[] >>
    qmatch_assum_abbrev_tac`(compile cs1 exp').out = cy ++ X` >> qunabbrev_tac`X` >>

    rw[] >>
    first_x_assum (qspecl_then
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
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
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
        match_mp_tac (MP_CANON Cv_bv_SUBMAP) >> simp[] >>
        qexists_tac`ps'` >>
        rw[Abbr`ps'`] >- (
          match_mp_tac DRESTRICT_SUBSET_SUBMAP >> rw[] ) >>
        fs[good_cls_def,FEVERY_DEF,UNCURRY] >>
        `p ∈ FDOM rfs` by PROVE_TAC[] >>
        fs[SUBMAP_DEF,FDOM_DRESTRICT] ) >>
      pop_assum mp_tac >>
      simp[Abbr`cl`,Once Cv_bv_cases] >>
      disch_then(qx_choosel_then[`a`,`bve`,`b`,`i'`,`j`,`l`,`xs`]strip_assume_tac) >>
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
      Q.PAT_ABBREV_TAC`benv = if X then Number 0 else Y` >>
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
          ntac 8 (pop_assum kall_tac) >>
          ntac 3 (pop_assum (qspec_then`x`mp_tac)) >>
          Cases_on `x ∈ free_vars c (c ' l)` >> fs[] >>
          Cases_on `x ∈ set (binders (c ' l))` >> fs[] >>
          qspecl_then[`c`,`c ' l`,`l`]mp_tac(CONJUNCT1 free_vars_DOMSUB) >>
          simp[SUBSET_DEF] >>
          disch_then(qspec_then`x`strip_assume_tac) >> rfs[] >>
          Cases_on`MEM x ns`>>fs[]>>
          Cases_on`MEM x ns'`>>fs[]>>
          qpat_assum`∀z. z < LENGTH X ⇒ Y`mp_tac >>
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

          qspecl_then[`ns'`,`xs`,`LENGTH vs`,`i`,`free_vars c b`,`(FEMPTY,0,[])`]mp_tac bind_fv_thm >>
          simp[FDOM_bind_fv]

          good_code_env_def
          filter_asms ((can (find_term (equal ``bve:bc_value list``))) o concl)
          filter_asms ((can (find_term (fn t => case total dest_const t of SOME ("ALL_DISTINCT",x) => true | _ => false))) o concl)
          `LENGTH x

          FRANGE_extend_rec_env
          extend_rec_env_def
      set_trace "goalstack print goal at top" 0

    (* >>

    first_x_assum (qspecl_then[`X`,`Y`]kall_tac) >>
    fs[] >> rw[] >>

    want to prove that Cv_bv s'' CRecClos bf too
    Cv_bv_SUBMAP
    fs[] >> rw[] >>
    fs[good_code_env_def,FEVERY_DEF] >>
    qpat_assum`∀x. x ∈ FDOM c ⇒ P`(qspec_then`l`mp_tac) >>
    fs[FLOOKUP_DEF] >> strip_tac >>
    Q.PAT_ABBREV_TAC`bc00 = X ++ [Stack (El 0)]` >>
    first_x_assum (qspecl_then[`s''`,`env'`,`s'''`,`v`,`ns'`,`defs`,`ns`,`vs`,`n`,`bc00`] mp_tac) >>



    qspecl_then[`sm`,`
    *)) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[compile_def,LET_THM] >>
    qabbrev_tac`cs0 = cs with <| tail := TCNonTail; decl := NONE|>` >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ [x]` >>
    first_x_assum (qspec_then`sm`mp_tac) >> simp[] >>
    disch_then (qspecl_then [`bc0`,`bs with code := ls0`,`cs0`] mp_tac) >>
    fs[Abbr`cs0`] >>
    disch_then (qx_choosel_then [`bvs`,`rfs`] strip_assume_tac) >>
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
    `FST pp = (DRESTRICT sm (FDOM s'))` by rw[Abbr`pp`] >> fs[] >>
    imp_res_tac (CONJUNCT2 Cevaluate_store_SUBSET) >>
    imp_res_tac (CONJUNCT2 Cevaluate_Clocs) >> fs[] >>
    `all_Clocs v1 ⊆ FDOM sm ∧ all_Clocs v2 ⊆ FDOM sm` by PROVE_TAC[SUBSET_TRANS] >>
    fs[good_sm_DRESTRICT,FDOM_DRESTRICT] >>
    disch_then (Q.X_CHOOSE_THEN`bv`strip_assume_tac) >>
    map_every qexists_tac [`bv`,`rfs`] >> fs[] >>
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
    match_mp_tac Cenv_bs_imp_incsz >>
    qmatch_assum_abbrev_tac `Cenv_bs c sm s' env cs.env (cs.sz + 2) bs0` >>
    qexists_tac`bs0 with <| stack := bs.stack; code := bs.code |>` >>
    reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs0`] >>
    match_mp_tac Cenv_bs_imp_decsz >>
    qexists_tac`bs0 with <| stack := TL bs0.stack; code := bs.code |>` >>
    reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs0`]
    >- (
      imp_res_tac Cenv_bs_CTLet_bound >>
      pop_assum (qspec_then`cs.sz +1`mp_tac) >>
      srw_tac[ARITH_ss][] ) >>
    match_mp_tac Cenv_bs_imp_decsz >>
    qexists_tac`bs0 with <| code := bs.code |>` >>
    reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs0`]
    >- (
      imp_res_tac Cenv_bs_CTLet_bound >>
      pop_assum (qspec_then`cs.sz +2`mp_tac) >>
      srw_tac[ARITH_ss][] ) >>
    match_mp_tac Cenv_bs_append_code >>
    qexists_tac `bs0` >>
    fsrw_tac[ARITH_ss][] >>
    rw[Abbr`bs0`,bc_state_component_equality]) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rpt gen_tac >>
    rpt strip_tac >>
    rw[LET_THM] >> fs[] >>
    fs[compile_def,LET_THM] >>
    Q.PAT_ABBREV_TAC`cs0 = compiler_state_tail_fupd X Y` >>
    `cs0 = cs` by (
      rw[Abbr`cs0`,compiler_state_component_equality] ) >>
    qunabbrev_tac`cs0`>>fs[] >> pop_assum kall_tac >>
    Q.PAT_ABBREV_TAC`cs1 = compiler_state_tail_fupd X Y` >>
    Q.PAT_ABBREV_TAC`cs2 = compiler_state_sz_fupd (K ((compile cs e1).sz - 1)) Y` >>
    Q.PAT_ABBREV_TAC`cs3 = compiler_state_sz_fupd (K ((compile cs2 e2).sz - 1)) Y` >>
    qabbrev_tac`nl = (compile cs exp).next_label` >>
    qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be1`strip_assume_tac) >>
    qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be2`strip_assume_tac) >>
    qspecl_then[`cs3`,`e3`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be3`strip_assume_tac) >>
    qmatch_assum_abbrev_tac `bs.code = bc0 ++ REVERSE (compile cs4 e3).out ++ [Label nl2]` >>
    `cs4 = cs3` by (
      simp[Abbr`cs3`,Abbr`cs4`,compiler_state_component_equality] >>
      simp[Abbr`cs2`] >> simp[Abbr`cs1`] >>
      qmatch_abbrev_tac`(compile cs4 e2).out = X` >>
      fs[] >> rfs[] >> qunabbrev_tac`X` >>
      qunabbrev_tac`cs4` >> fs[] ) >>
    qunabbrev_tac`cs4`>>fs[] >> pop_assum kall_tac >>
    qabbrev_tac`nl1 = nl + 1` >>
    `bs.code = bc0 ++ REVERSE (compile cs exp).out ++ ( [JumpIf (Lab nl);Jump(Lab nl1);Label nl]
                   ++ REVERSE be2 ++ [Jump(Lab nl2);Label nl1]
                   ++ REVERSE be3 ++ [Label (nl + 2)])` by (
      rw[] >> rw[Abbr`cs3`] >> rw[Abbr`cs2`] ) >>
    qmatch_assum_abbrev_tac `bs.code = bc0 ++ REVERSE (compile cs exp).out ++ bc1` >>
    qabbrev_tac `il = bs.inst_length` >>
    qpat_assum `∀bc0. P` mp_tac >>
    qmatch_assum_abbrev_tac `bs.code = ls0 ++ bc1` >>
    first_x_assum (qspec_then`sm` mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧
     FDOM s' ⊆ FDOM s'' ∧
     FDOM s' ⊆ FDOM sm` by metis_tac[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >> fs[] >>
    fs[ALL_DISTINCT_APPEND] >>
    disch_then (qspecl_then [`bc0`,`bs with code := ls0`,`cs`] mp_tac) >>
    simp[] >>
    simp[Once Cv_bv_cases] >>
    strip_tac >>
    qunabbrev_tac`ls0` >>
    qunabbrev_tac`bc1` >>
    qmatch_assum_abbrev_tac`bc_next^* bs0 bs1` >>
    `bc_next^* bs (bs1 with code := bs.code)` by (
      match_mp_tac RTC_bc_next_append_code >>
      map_every qexists_tac[`bs0`,`bs1`] >>
      rw[Abbr`bs0`,bc_state_component_equality,Abbr`bs1`] >>
      unabbrev_all_tac >> rw[]) >>
    map_every qunabbrev_tac[`bs0`,`bs1`] >>
    `ALL_DISTINCT (FILTER is_Label bs.code) ∧
     EVERY (combin$C $< cs3.next_label o dest_Label)
       (FILTER is_Label (bc0 ++ REVERSE cs3.out))` by (
      qunabbrev_tac`il` >>
      ntac 4 (pop_assum kall_tac) >>
      rpt (qpat_assum `Cexp_pred X` kall_tac) >>
      rpt (qpat_assum `free_labs X ⊆ Y` kall_tac) >>
      map_every qunabbrev_tac[`nl1`,`nl2`] >>
      rpt (qpat_assum `Cevaluate X Y Z A` kall_tac) >>
      qpat_assum `bs.pc = X` kall_tac >>
      qpat_assum `Cenv_bs c sm X Y Z A B` kall_tac >>
      fs[FILTER_APPEND,FILTER_REVERSE,EVERY_REVERSE] >>
      qspecl_then[`cs`,`exp`,`FILTER is_Label be1`]mp_tac(CONJUNCT1 compile_next_label) >>
      simp[Once FILTER_APPEND] >> strip_tac >>
      qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
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
      qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_next_label_inc) >> strip_tac >>
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
      fs[Abbr`cs3`,Abbr`cs2`] >>
      rw[] >>
      res_tac >>
      spose_not_then strip_assume_tac >>
      res_tac >> DECIDE_TAC) >>
    `cs1.sz = cs.sz + 1` by (
      rw[Abbr`cs1`] >>
      match_mp_tac (CONJUNCT1 compile_sz) >>
      rw[] ) >>
    `(cs2.env = cs.env) ∧ (cs2.sz = cs.sz) ∧ (cs2.ecs = cs.ecs)` by (
      rw[Abbr`cs2`] >> fs[Abbr`cs1`] ) >>
    `BIGUNION (IMAGE all_Clocs (FRANGE env)) ⊆ FDOM s'` by PROVE_TAC[SUBSET_TRANS] >>
    `BIGUNION (IMAGE all_Clocs (FRANGE s')) ⊆ FDOM s'` by PROVE_TAC[Cevaluate_Clocs,FST] >>
    fs[] >>
    Cases_on `b1` >> fs[] >- (
      `∃bc1. bs.code = bc0 ++ REVERSE (compile cs2 e2).out ++ bc1` by (
        rw[Abbr`cs2`] ) >>
      qmatch_assum_abbrev_tac`bs.code = ls0 ++ bc1` >>
      disch_then(qspec_then`sm`mp_tac) >> simp[] >>
      disch_then(qspecl_then[`bc0`,`bs with <|code := ls0; pc := next_addr il (bc0 ++ REVERSE cs2.out); refs := rfs|>`,`cs2`]mp_tac) >>
      simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
      `P` by (
        map_every qunabbrev_tac [`P`,`Q`,`R`] >>
        conj_tac >- rw[Abbr`cs2`,Abbr`cs1`] >>
        conj_tac >- rw[Abbr`cs2`,Abbr`cs1`] >>
        conj_tac >- (
          match_mp_tac Cenv_bs_imp_decsz >>
          qmatch_assum_abbrev_tac `Cenv_bs c sm s' env cs.env (cs.sz + 1) bs1` >>
          qexists_tac`bs1 with code := bc0 ++ REVERSE cs2.out` >>
          reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs1`]
          >- (
            imp_res_tac Cenv_bs_CTLet_bound >>
            pop_assum(qspec_then`cs.sz+1`mp_tac) >>
            srw_tac[ARITH_ss][] ) >>
          match_mp_tac Cenv_bs_append_code >>
          qexists_tac`bs1` >> rw[] >>
          rw[bc_state_component_equality,Abbr`bs1`,Abbr`cs2`] ) >>
        qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_ALL_DISTINCT_labels) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >>
          fs[FILTER_APPEND,ALL_DISTINCT_APPEND,FILTER_REVERSE,ALL_DISTINCT_REVERSE,EVERY_REVERSE] ) >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >> simp[] >>
        qspecl_then[`cs`,`exp`,`FILTER is_Label be1`]mp_tac(CONJUNCT1 compile_next_label) >>
        qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
        `P` by (
          map_every qunabbrev_tac [`P`,`Q`,`R`] >> fs[FILTER_APPEND] ) >>
        map_every qunabbrev_tac [`P`,`Q`,`R`] >> simp[] >>
        qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_next_label_inc) >>
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
      disch_then(qx_choosel_then[`b2`,`rfs2`]strip_assume_tac) >>
      map_every qexists_tac[`b2`,`rfs2`] >>
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
      conj_tac >- (
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
      metis_tac[SUBMAP_TRANS] ) >>
    `bs.code = bc0 ++ REVERSE (compile cs3 e3).out ++ [Label (nl + 2)]` by (
      rw[Abbr`cs3`,Abbr`cs2`] ) >>
    `(cs3.ecs = cs.ecs) ∧ (cs3.env = cs.env)` by rw[Abbr`cs3`,Abbr`cs2`,Abbr`cs1`] >>
    `cs3.sz = cs.sz` by (
      rw[Abbr`cs3`] >>
      qspecl_then[`cs2`,`e2`]mp_tac(CONJUNCT1 compile_sz) >>
      rw[] ) >>
    qmatch_assum_abbrev_tac`bs.code = ls0 ++ [Label (nl + 2)]` >>
    disch_then(qspec_then`sm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`bc0`,`bs with <|code:=ls0; pc := next_addr il (bc0 ++ REVERSE cs3.out); refs := rfs|>`,`cs3`]mp_tac) >>
    simp[] >> qmatch_abbrev_tac`(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- (
        rw[Abbr`cs3`,compile_nontail,Abbr`cs2`,Abbr`cs1`] ) >>
      conj_tac >- (
        rw[Abbr`cs3`,compile_decl_NONE,Abbr`cs2`,Abbr`cs1`] ) >>
      conj_tac >- (
        match_mp_tac Cenv_bs_imp_decsz >>
        qmatch_assum_abbrev_tac `Cenv_bs c sm s' env cs.env (cs.sz + 1) bs1` >>
        qexists_tac`bs1 with code := bc0 ++ REVERSE cs3.out` >>
        reverse(rw[])>-rw[bc_state_component_equality,Abbr`bs1`]
        >- (
          imp_res_tac Cenv_bs_CTLet_bound >>
          pop_assum(qspec_then`cs.sz+1`mp_tac) >>
          srw_tac[ARITH_ss][] ) >>
        match_mp_tac Cenv_bs_append_code >>
        qexists_tac`bs1` >> rw[] >>
        rw[bc_state_component_equality,Abbr`bs1`,Abbr`cs3`,Abbr`cs2`] ) >>
      qmatch_abbrev_tac`ALL_DISTINCT (FILTER is_Label ls)` >>
      `∃ls1. bs.code = ls ++ ls1` by (
        rw[Abbr`ls`,Abbr`ls0`] ) >>
      qpat_assum`ALL_DISTINCT (FILTER is_Label bs.code)`mp_tac >>
      pop_assum SUBST1_TAC >>
      rw[FILTER_APPEND,ALL_DISTINCT_APPEND] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> simp[] >>
    disch_then(qx_choosel_then[`b3`,`rfs3`]strip_assume_tac) >>
    map_every qexists_tac[`b3`,`rfs3`] >>
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
    conj_tac >- (
      match_mp_tac Cenv_bs_append_code >>
      qexists_tac `bs07` >>
      rw[Abbr`bs07`] >>
      rw[Abbr`ls0`,bc_state_component_equality] >>
      rw[FILTER_APPEND] ) >>
    metis_tac[SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  strip_tac >- (
    simp[] >>
    rw[EVERY2_EVERY] >>
    (*
    map_every qexists_tac [`[]`,`K bs.pc`,`K s`,`K bs.refs`] >>
    *)
    qexists_tac`bs.refs` >>
    rw[RTC_eq_NRC] >>
    TRY (qexists_tac`0` >>rw[]) >>
    TRY (qmatch_abbrev_tac `Cenv_bs X Y A B C D E` >>
         qmatch_assum_abbrev_tac `Cenv_bs X Y A B C D E'` >>
         match_mp_tac Cenv_bs_append_code >>
         qexists_tac `E' with pc := E.pc` >>
         unabbrev_all_tac >> rw[Cenv_bs_pc] ) >>
    rw[bc_state_component_equality] ) >>
  strip_tac >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    qspecl_then[`cs`,`exp`]mp_tac(CONJUNCT1 compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`be`strip_assume_tac) >>
    qabbrev_tac`cs0 = compile cs exp` >>
    qspecl_then[`cs0`,`exps`]mp_tac(FOLDL_compile_append_out) >>
    disch_then(Q.X_CHOOSE_THEN`bes`strip_assume_tac) >>
    first_x_assum(qspecl_then[`sm`,`s'`,`v`]mp_tac) >>
    `FDOM s ⊆ FDOM s' ∧
     FDOM s' ⊆ FDOM s'' ∧
     FDOM s' ⊆ FDOM sm` by PROVE_TAC[SUBSET_TRANS,Cevaluate_store_SUBSET,FST] >>
    fs[ALL_DISTINCT_APPEND] >>
    disch_then(qspecl_then[`bc0`,`bs with <|code:=bc0 ++ REVERSE cs0.out|>`,`cs`]mp_tac) >>
    fs[] >>
    disch_then(qx_choosel_then[`bv`,`rfs`](strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM])) >>
    qabbrev_tac`il = bs.inst_length` >>
    qabbrev_tac`bc00 = bc0 ++ REVERSE cs0.out` >>
    first_x_assum(qspec_then`sm`mp_tac) >> simp[] >>
    qmatch_abbrev_tac `(P ⇒ Q) ⇒ R` >>
    `P` by (
      map_every qunabbrev_tac[`P`,`Q`,`R`] >>
      conj_tac >- PROVE_TAC[SUBSET_TRANS] >>
      PROVE_TAC[Cevaluate_Clocs,FST] ) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    disch_then(qspecl_then[`bc0`,
      `bs with <|code:=bc0 ++ REVERSE (FOLDL compile cs0 exps).out;pc := next_addr il bc00;stack:=bv::bs.stack;refs:=rfs|>`,
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
      fs[REVERSE_APPEND,compile_nontail] >>
      conj_tac >- PROVE_TAC[compile_sz] >>
      match_mp_tac compile_labels_lemma >> fs[] >>
      PROVE_TAC[]) >>
    map_every qunabbrev_tac[`P`,`Q`,`R`] >> fs[] >>
    disch_then(qx_choosel_then[`bvs`,`rf`](strip_assume_tac o SIMP_RULE(srw_ss())[LET_THM])) >>
    map_every qexists_tac[`bv::bvs`,`rf`] >>
    qmatch_assum_abbrev_tac`bc_next^* bs05 bs11` >>
    `bs05 = bs1 with code := bs.code` by (
      rw[Abbr`bs05`,Abbr`bs1`,bc_state_component_equality,Abbr`bc00`] ) >>
    simp[LET_THM] >>
    conj_tac >- (
      qmatch_abbrev_tac `bc_next^* bs bs2` >>
      qsuff_tac `bs2 = bs11` >- metis_tac[RTC_TRANSITIVE,transitive_def] >>
      rw[Abbr`bs2`,Abbr`bs11`,bc_state_component_equality,REVERSE_APPEND] ) >>
    conj_tac >- (
      fs[REVERSE_APPEND] >> rw[] >> rw[Abbr`il`] >>
      match_mp_tac (MP_CANON Cv_bv_refs) >> simp[] >>
      qexists_tac `rfs` >>
      reverse conj_tac >- (
        fs[SUBMAP_DEF,DRESTRICT_DEF,FLOOKUP_DEF] >>
        qx_gen_tac `p` >> strip_tac >>
        `p ∉ FRANGE (DRESTRICT sm (FDOM s'))` by (
          fs[IN_FRANGE,DRESTRICT_DEF,SUBSET_DEF] >>
          metis_tac[] ) >>
        metis_tac[] ) >>
      match_mp_tac (MP_CANON Cv_bv_SUBMAP) >> simp[] >>
      qexists_tac `DRESTRICT sm (FDOM s')` >>
      conj_tac >- (
        match_mp_tac Cv_bv_l2a_mono >>
        qmatch_assum_abbrev_tac`Cv_bv pp v bv` >>
        qexists_tac `pp` >> rw[Abbr`pp`] >>
        match_mp_tac bc_find_loc_aux_append_code >>
        rw[] ) >>
      conj_tac >- metis_tac[DRESTRICT_SUBSET_SUBMAP] >>
      fs[SUBMAP_DEF,DRESTRICT_DEF] ) >>
    conj_tac >- (
      qmatch_abbrev_tac `Cenv_bs c sm s2 env env0 sz0 bs2` >>
      `bs2 = bs11` by (
        rw[Abbr`bs2`,Abbr`bs11`,bc_state_component_equality,REVERSE_APPEND] ) >>
      rw[] >>
      fs[Abbr`cs0`,Abbr`sz0`] >>
      rfs[compile_sz] >> fsrw_tac[ARITH_ss][ADD1]) >>
    metis_tac[SUBMAP_TRANS]) >>
  strip_tac >- rw[] >>
  rw[] )

val _ = export_theory ()
