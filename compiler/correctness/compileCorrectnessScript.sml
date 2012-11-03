open HolKernel bossLib boolLib boolSimps SatisfySimps listTheory pairTheory pred_setTheory finite_mapTheory alistTheory relationTheory lcsymtacs
open MiniMLTerminationTheory miniMLExtraTheory miscTheory compileTerminationTheory intLangTheory bytecodeTerminationTheory evaluateEquationsTheory expToCexpTheory quantHeuristicsLib
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

open pmatchTheory labelClosuresTheory

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

val pc_end_def = Define`
  (pc_end len n [] = (n = 0)) ∧
  (pc_end len n (x::xs) =
   if is_Label x then pc_end len n xs
   else len x < n ∧ pc_end len (n - (len x + 1)) xs)`

val bc_finish_def = Define`
  bc_finish s1 s2 = bc_next^* s1 s2 ∧ pc_end s2.inst_length s2.pc s2.code`

val repl_exp_contab = store_thm("repl_exp_contab",
  ``(repl_exp il na rs exp = (rs',c)) ==> (rs'.contab = rs.contab)``,
  rw[repl_exp_def,compile_Cexp_def,LET_THM] >>
  qabbrev_tac`p=repeat_label_closures (exp_to_Cexp (cmap rs.contab) exp) 0 []` >>
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
  (lookup_ct sz st rs (CTLet n) = el_check (sz - n) st) ∧
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
  (Cv_bv pp (CLitv (IntLit a)) (Number a)) ∧
  (Cv_bv pp (CLitv (Bool b)) (bool_to_val b)) ∧
  (EVERY2 (Cv_bv pp) vs bvs ⇒ Cv_bv pp (CConv cn vs) (Block cn bvs)) ∧
  ((pp = (c,l2a,rfs:num |-> bc_value)) ∧
   (find_index n ns 0 = SOME i) ∧
   (EL i defs = (xs,INR l)) ∧
   (FLOOKUP c l = SOME e) ∧
   (fvs = SET_TO_LIST (free_vars c e)) ∧
   (benv = if fvs = [] then Number 0 else Block 0 bvs) ∧
   (LENGTH bvs = LENGTH fvs) ∧
   (∀i x bv. i < LENGTH fvs ∧ (x = EL i fvs) ∧ (bv = EL i bvs) ⇒
     if MEM x xs then x ∈ FDOM env (* ∧ Cv_bv pp (env ' x) bv *) else
     ∃j p. (find_index x ns 0 = SOME j) ∧
           (bv = RefPtr p) ∧
           (p ∈ FDOM rfs)
           (* ∧ Cv_bv pp (CRecClos env ns defs (EL j ns)) (rfs ' p) *) )
   ⇒ Cv_bv pp (CRecClos env ns defs n) (Block 2 [CodePtr (l2a l); benv]))`

(*
val Cenv_bs_def = Define`
  Cenv_bs Cenv renv sz bs =
    fmap_rel
      (λCv b. case lookup_ct sz bs.stack bs.refs b of NONE => F
         | SOME bv => Cv_bv (c,,bs.refs) Cv bv)
    Cenv renv`

val env_rs_def = Define`
  env_rs bs env rs =
    let Cenv = alist_to_fmap (env_to_Cenv (cmap rs.contab) env) in
    Cenv_bs Cenv rs.renv rs.rsz bs`

          ∀b1. (∀x. x ∈ FDOM env ⇒ ∃v. (lookup_ct cs.sz b1.stack b1.refs (cs.env ' x) = SOME v) ∧

                                       bceqv b1.inst_length b1.code (env ' x) v) ⇒
*)

(*
val next_addr_def = Define`
  next_addr bs = FST(SND(calculate_labels bs.inst_length FEMPTY 0 [] bs.code))`

val repl_exp_val = store_thm("repl_exp_val",
  ``∀cenv env exp v rs rs' bc bs bs'.
      exp_pred exp ∧
      env_rs env rs ∧
      evaluate cenv env exp (Rval v) ∧
      EVERY closed (MAP SND env) ∧
      FV exp ⊆ set (MAP FST env) ∧
      good_cenv cenv ∧
      good_cmap cenv (cmap rs.contab) ∧
      (let na = next_addr bs in
       (repl_exp bs.inst_length na rs exp = (rs',bc)) ∧
       (bc_finish (bs with <|code := bs.code++bc; pc := na|>) bs'))
      ⇒
      ∃bv.
      (bs'.stack = bv :: bs.stack) ∧
      (v_to_ov v = bv_to_ov (FST(SND(rs.contab))) bv)``,
  rw[repl_exp_def,compile_Cexp_def,LET_THM] >>
  pop_assum mp_tac >>
  qabbrev_tac `p = repeat_label_closures (exp_to_Cexp (cmap rs.contab) exp) 0 []` >>
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
  `(p0,p1,p2) = (Ce,0,[])` by PROVE_TAC[Cexp_pred_repeat_label_closures] >>
  fs[] >> rw[] >>
  `calculate_ldefs FEMPTY [] Ce = []` by PROVE_TAC[Cexp_pred_calculate_ldefs] >>
  fs[] >>
  fs[calculate_ecs_def] >>
  fs[compile_code_env_def,LET_THM] >>
*)

val labels_only_def = Define`
  labels_only ls = ∀x. MEM x ls ⇒ case x of
    | Jump (Addr _) => F
    | JumpIf (Addr _) => F
    | Call (Addr _) => F
    | PushPtr (Addr _) => F
    | _ => T`;

val el_of_addr_def = Define`
  (el_of_addr il n [] = NONE) ∧
  (el_of_addr il n (x::xs) =
   if is_Label x then OPTION_BIND (el_of_addr il n xs) (λm. SOME (m + 1)) else
     if n = 0 then SOME (0:num) else
       if n < il x + 1 then NONE else
         OPTION_BIND (el_of_addr il (n - (il x + 1)) xs) (λm. SOME (m + 1)))`
val _ = export_rewrites["el_of_addr_def"]

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

val with_same_pc = store_thm("with_same_pc",
  ``x with pc := x.pc = x``,
  rw[DB.fetch"Bytecode""bc_state_component_equality"])
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
