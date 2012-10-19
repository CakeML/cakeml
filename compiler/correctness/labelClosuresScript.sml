open HolKernel boolLib boolSimps bossLib quantHeuristicsLib pairTheory listTheory
open relationTheory arithmeticTheory rich_listTheory finite_mapTheory pred_setTheory state_transformerTheory lcsymtacs
open SatisfySimps miscTheory intLangTheory compileTerminationTheory
val _ = new_theory"labelClosures"

(*
val label_closures_state_component_equality = DB.fetch"Compile""label_closures_state_component_equality"

val label_closures_empty = store_thm("label_closures_empty",
  ``(∀e s e' s'. (label_closures e (s with <| lcode_env := [] |>) = (e',s')) ⇒
            (label_closures e s = (e', s' with <| lcode_env := s'.lcode_env ++ s.lcode_env |>))) ∧
    (∀ds ac s ds' s'. (label_defs ac ds (s with <| lcode_env := [] |>) = (ds', s')) ⇒
            (label_defs ac ds s = (ds', s' with <| lcode_env := s'.lcode_env ++ s.lcode_env |>))) ∧
    (∀x:def. T) ∧ (∀x:(Cexp + num). T) ∧
    (∀es s es' s'. (label_closures_list es (s with <| lcode_env := [] |>) = (es',s')) ⇒
            (label_closures_list es s = (es', s' with <| lcode_env := s'.lcode_env ++ s.lcode_env |>)))``,
  ho_match_mp_tac (TypeBase.induction_of``:Cexp``) >>
  rw[label_closures_def,label_defs_def,UNIT_DEF,BIND_DEF] >>
  rw[label_closures_state_component_equality] >>
  TRY (full_split_pairs_tac P >> fs[] >> rfs[] >> rw[] >> res_tac >> fs[] >> NO_TAC) >>
  TRY (Cases_on `x` >> Cases_on `r` >> fs[label_defs_def,BIND_DEF,UNIT_DEF])
  fs[UNCURRY] >>
  full_split_pairs_tac P >>
  fs[] >> rw[] >> rfs[] >> rw[] >>
  res_tac >> fs[] >> rw[]

  >> res_tac >> fs[] >> NO_TAC) >>
*)

fun full_split_pairs_tac P (g as (asl,w)) = let
  fun Q tm = P tm
             andalso can(pairSyntax.dest_prod o type_of)tm
             andalso (not (pairSyntax.is_pair tm))
  val tms = List.foldl (fn(t,s)=>(union s (find_terms Q t))) (mk_set(find_terms Q w)) asl
  in MAP_EVERY (STRIP_ASSUME_TAC o Lib.C ISPEC pair_CASES) tms end g

fun P tm = mem (fst (strip_comb tm)) [``label_closures``,rator ``mapM label_closures``]

(* labels in an expression (but not recursively) *)
val free_labs_def = tDefine "free_labs"`
  (free_labs (CDecl xs) = []) ∧
  (free_labs (CRaise er) = []) ∧
  (free_labs (CVar x) = []) ∧
  (free_labs (CLit li) = []) ∧
  (free_labs (CCon cn es) = (FLAT (MAP (free_labs) es))) ∧
  (free_labs (CTagEq e n) = (free_labs e)) ∧
  (free_labs (CProj e n) = (free_labs e)) ∧
  (free_labs (CLet xs es e) = FLAT (MAP (free_labs) (e::es))) ∧
  (free_labs (CLetfun b ns defs e) = (MAP (OUTR o SND) (FILTER (ISR o SND) defs))++(free_labs e)) ∧
  (free_labs (CFun xs (INL _)) = []) ∧
  (free_labs (CFun xs (INR l)) = [l]) ∧
  (free_labs (CCall e es) = FLAT (MAP (free_labs) (e::es))) ∧
  (free_labs (CPrim2 op e1 e2) = (free_labs e1)++(free_labs e2)) ∧
  (free_labs (CIf e1 e2 e3) = (free_labs e1)++(free_labs e2)++(free_labs e3))`(
  WF_REL_TAC `measure Cexp_size` >>
  srw_tac[ARITH_ss][Cexp4_size_thm] >>
  Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["free_labs_def"]

(* bodies in an expression (but not recursively) *)
val free_bods_def = tDefine "free_bods"`
  (free_bods (CDecl xs) = []) ∧
  (free_bods (CRaise er) = []) ∧
  (free_bods (CVar x) = []) ∧
  (free_bods (CLit li) = []) ∧
  (free_bods (CCon cn es) = (FLAT (MAP (free_bods) es))) ∧
  (free_bods (CTagEq e n) = (free_bods e)) ∧
  (free_bods (CProj e n) = (free_bods e)) ∧
  (free_bods (CLet xs es e) = FLAT (MAP free_bods es) ++ free_bods e) ∧
  (free_bods (CLetfun b ns defs e) = (MAP (OUTL o SND) (FILTER (ISL o SND) defs))++(free_bods e)) ∧
  (free_bods (CFun xs (INL cb)) = [cb]) ∧
  (free_bods (CFun xs (INR _)) = []) ∧
  (free_bods (CCall e es) = FLAT (MAP (free_bods) (e::es))) ∧
  (free_bods (CPrim2 op e1 e2) = (free_bods e1)++(free_bods e2)) ∧
  (free_bods (CIf e1 e2 e3) = (free_bods e1)++(free_bods e2)++(free_bods e3))`(
  WF_REL_TAC `measure Cexp_size` >>
  srw_tac[ARITH_ss][Cexp4_size_thm] >>
  Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["free_bods_def"]

(* replace labels by bodies from code env (but not recursively) *)
val subst_lab_cb_def = Define`
  (subst_lab_cb c (INL b) = INL b) ∧
  (subst_lab_cb c (INR l) = case FLOOKUP c l of SOME b => INL b
                                              | NONE   => INR l)`

val subst_labs_def = tDefine "subst_labs"`
  (subst_labs c (CDecl xs) = CDecl xs) ∧
  (subst_labs c (CRaise er) = CRaise er) ∧
  (subst_labs c (CVar x) = (CVar x)) ∧
  (subst_labs c (CLit li) = (CLit li)) ∧
  (subst_labs c (CCon cn es) = CCon cn (MAP (subst_labs c) es)) ∧
  (subst_labs c (CTagEq e n) = CTagEq (subst_labs c e) n) ∧
  (subst_labs c (CProj e n) = CProj (subst_labs c e) n) ∧
  (subst_labs c (CLet xs es e) = CLet xs (MAP (subst_labs c) es) (subst_labs c e)) ∧
  (subst_labs c (CLetfun b ns defs e) = CLetfun b ns (MAP (λ(xs,cb). (xs,subst_lab_cb c cb)) defs) (subst_labs c e)) ∧
  (subst_labs c (CFun xs cb) = CFun xs (subst_lab_cb c cb)) ∧
  (subst_labs c (CCall e es) = CCall (subst_labs c e) (MAP (subst_labs c) es)) ∧
  (subst_labs c (CPrim2 op e1 e2) = CPrim2 op (subst_labs c e1) (subst_labs c e2)) ∧
  (subst_labs c (CIf e1 e2 e3) = CIf (subst_labs c e1)(subst_labs c e2)(subst_labs c e3))`(
  WF_REL_TAC `measure (Cexp_size o SND)` >>
  srw_tac[ARITH_ss][Cexp4_size_thm] >>
  Q.ISPEC_THEN `Cexp_size` imp_res_tac SUM_MAP_MEM_bound >>
  fsrw_tac[ARITH_ss][])
val _ = export_rewrites["subst_lab_cb_def","subst_labs_def"]

val subst_labs_ind = theorem"subst_labs_ind"

(* TODO: move?
         use for Cevaluate_any_env?*)
val DRESTRICT_FUNION_SUBSET = store_thm("DRESTRICT_FUNION_SUBSET",
  ``s2 ⊆ s1 ⇒ ∃h. (DRESTRICT f s1 ⊌ g = DRESTRICT f s2 ⊌ h)``,
  strip_tac >>
  qexists_tac `DRESTRICT f s1 ⊌ g` >>
  match_mp_tac EQ_SYM >>
  REWRITE_TAC[GSYM SUBMAP_FUNION_ABSORPTION] >>
  rw[SUBMAP_DEF,DRESTRICT_DEF,FUNION_DEF] >>
  fs[SUBSET_DEF])

val DRESTRICT_SUBSET_SUBMAP_gen = store_thm("DRESTRICT_SUBSET_SUBMAP_gen",
  ``!f1 f2 s t. DRESTRICT f1 s ⊑ DRESTRICT f2 s ∧ t ⊆ s
    ==> DRESTRICT f1 t ⊑ DRESTRICT f2 t``,
  rw[SUBMAP_DEF,DRESTRICT_DEF,SUBSET_DEF])

val SUBSET_DIFF_EMPTY = store_thm("SUBSET_DIFF_EMPTY",
  ``!s t. (s DIFF t = {}) = (s SUBSET t)``,
  SRW_TAC[][EXTENSION,SUBSET_DEF] THEN PROVE_TAC[])

val DIFF_INTER_SUBSET = store_thm("DIFF_INTER_SUBSET",
  ``!r s t. r SUBSET s ==> (r DIFF s INTER t = r DIFF t)``,
  SRW_TAC[][EXTENSION,SUBSET_DEF] THEN PROVE_TAC[])

val UNION_DIFF_2 = store_thm("UNION_DIFF_2",
  ``!s t. (s UNION (s DIFF t) = s)``,
  SRW_TAC[][EXTENSION] THEN PROVE_TAC[])

val DRESTRICT_FUNION_SAME = store_thm("DRESTRICT_FUNION_SAME",
  ``!fm s. FUNION (DRESTRICT fm s) fm = fm``,
  SRW_TAC[][GSYM SUBMAP_FUNION_ABSORPTION]

val subst_labs_any_env = store_thm("subst_labs_any_env",
  ``∀c e c'. (DRESTRICT c (set (free_labs e)) = DRESTRICT c' (set (free_labs e))) ⇒
             (subst_labs c e = subst_labs ((DRESTRICT c (set (free_labs e))) ⊌ c') e)``,
  ho_match_mp_tac subst_labs_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[ETA_ss][MAP_EQ_f] >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs (DRESTRICT c1 s0 ⊌ c1) ee` >>
    `DRESTRICT c1 s0 ⊌ c1 = c1` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >> rw[] >>
    unabbrev_all_tac >>
    pop_assum kall_tac >>
    `c' = DRESTRICT c' (set (free_labs e)) ⊌ c'` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac`DRESTRICT c s0 = DRESTRICT c' s0` >>
    qexists_tac `s0` >> rw[] >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
    metis_tac[] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    srw_tac[ETA_ss][MAP_EQ_f] >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs (DRESTRICT c1 s0 ⊌ c1) ee` >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs c2 ee` >>
    `c2 = c1` by rw[Abbr`c2`,GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac `subst_labs c ee = subst_labs c' ee` >>
    `c' = DRESTRICT c' (set (free_labs ee)) ⊌ c'` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac`DRESTRICT c s0 = DRESTRICT c' s0` >>
    qexists_tac `s0` >> rw[] >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
    metis_tac[] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][MAP_EQ_f] >>
    TRY (
      PairCases_on `e'` >> fs[] >>
      Cases_on `e'1` >> rw[] >>
      qmatch_assum_abbrev_tac`DRESTRICT c s = DRESTRICT c' s` >>
      `FDOM c INTER s = FDOM c' INTER s` by (
        fs[GSYM fmap_EQ_THM,FDOM_DRESTRICT] ) >>
      fsrw_tac[DNF_ss,QUANT_INST_ss[std_qp]][Abbr`s`,EXTENSION,MEM_MAP,MEM_FILTER,FLOOKUP_DEF,DRESTRICT_DEF,FUNION_DEF] >>
      rw[] >> (TRY (metis_tac[])) >>
      fsrw_tac[QUANT_INST_ss[std_qp]][GSYM fmap_EQ_THM,MEM_MAP,MEM_FILTER,DRESTRICT_DEF,FUNION_DEF] ) >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs (DRESTRICT c1 s0 ⊌ c1) ee` >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs c2 ee` >>
    `c2 = c1` by rw[Abbr`c2`,GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac `subst_labs c ee = subst_labs c' ee` >>
    `c' = DRESTRICT c' (set (free_labs ee)) ⊌ c'` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac`DRESTRICT c s0 = DRESTRICT c' s0` >>
    qexists_tac `s0` >> rw[] >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] ) >>
  strip_tac >- (
    Cases_on `cb` >> rw[FLOOKUP_DEF,DRESTRICT_DEF,FUNION_DEF,GSYM fmap_EQ_THM] >>
    rw[EXTENSION] >> metis_tac[] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][MAP_EQ_f] >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs (DRESTRICT c1 s0 ⊌ c1) ee` >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs c2 ee` >>
    `c2 = c1` by rw[Abbr`c2`,GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac `subst_labs c ee = subst_labs c' ee` >>
    `c' = DRESTRICT c' (set (free_labs ee)) ⊌ c'` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac`DRESTRICT c s0 = DRESTRICT c' s0` >>
    qexists_tac `s0` >> rw[] >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
    metis_tac[] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][MAP_EQ_f] >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs (DRESTRICT c1 s0 ⊌ c1) ee` >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs c2 ee` >>
    `c2 = c1` by rw[Abbr`c2`,GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac `subst_labs c ee = subst_labs c' ee` >>
    `c' = DRESTRICT c' (set (free_labs ee)) ⊌ c'` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac`DRESTRICT c s0 = DRESTRICT c' s0` >>
    qexists_tac `s0` >> rw[] >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
    metis_tac[] ) >>
  strip_tac >- (
    srw_tac[ETA_ss][MAP_EQ_f] >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs (DRESTRICT c1 s0 ⊌ c1) ee` >>
    qmatch_abbrev_tac`subst_labs c0 ee = subst_labs c2 ee` >>
    `c2 = c1` by rw[Abbr`c2`,GSYM SUBMAP_FUNION_ABSORPTION] >>
    unabbrev_all_tac >>
    pop_assum SUBST1_TAC >>
    qmatch_abbrev_tac `subst_labs c ee = subst_labs c' ee` >>
    `c' = DRESTRICT c' (set (free_labs ee)) ⊌ c'` by rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
    pop_assum SUBST1_TAC >>
    first_x_assum (match_mp_tac o MP_CANON) >> rw[] >>
    match_mp_tac DRESTRICT_SUBSET >>
    qmatch_assum_abbrev_tac`DRESTRICT c s0 = DRESTRICT c' s0` >>
    qexists_tac `s0` >> rw[] >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
    metis_tac[] ))

fun select_fun tm = if P tm then SOME (tm,"lc") else NONE

(* TODO: move *)
val REVERSE_ZIP = store_thm("REVERSE_ZIP",
  ``!l1 l2. (LENGTH l1 = LENGTH l2) ==>
    (REVERSE (ZIP (l1,l2)) = ZIP (REVERSE l1, REVERSE l2))``,
  Induct THEN SRW_TAC[][LENGTH_NIL_SYM] THEN
  Cases_on `l2` THEN FULL_SIMP_TAC(srw_ss())[] THEN
  SRW_TAC[][GSYM ZIP_APPEND])

val LENGTH_o_REVERSE = store_thm("LENGTH_o_REVERSE",
  ``(LENGTH o REVERSE = LENGTH) /\
    (LENGTH o REVERSE o f = LENGTH o f)``,
  SRW_TAC[][FUN_EQ_THM])

val REVERSE_o_REVERSE = store_thm("REVERSE_o_REVERSE",
  ``(REVERSE o REVERSE o f = f)``,
  SRW_TAC[][FUN_EQ_THM])

val GENLIST_PLUS_APPEND = store_thm("GENLIST_PLUS_APPEND",
  ``GENLIST ($+ a) n1 ++ GENLIST ($+ (n1 + a)) n2 = GENLIST ($+ a) (n1 + n2)``,
  rw[Once ADD_SYM,SimpRHS] >>
  srw_tac[ARITH_ss][GENLIST_APPEND] >>
  srw_tac[ETA_ss][ADD_ASSOC])

val count_add = store_thm("count_add",
  ``!n m. count (n + m) = count n UNION IMAGE ($+ n) (count m)``,
  SRW_TAC[ARITH_ss][EXTENSION,EQ_IMP_THM] THEN
  Cases_on `x < n` THEN SRW_TAC[ARITH_ss][] THEN
  Q.EXISTS_TAC `x - n` THEN
  SRW_TAC[ARITH_ss][])

val plus_compose = store_thm("plus_compose",
  ``!n:num m. $+ n o $+ m = $+ (n + m)``,
  SRW_TAC[ARITH_ss][FUN_EQ_THM])

val subst_labs_SUBMAP = store_thm("subst_labs_SUBMAP",
  ``set (free_labs e) ⊆ FDOM c ∧ c ⊑ c'
    ⇒ (subst_labs c e = subst_labs c' e)``,
  rw[] >>
  imp_res_tac subst_labs_any_env >>
  qsuff_tac `c' = DRESTRICT c (set (free_labs e)) ⊌ c'` >- PROVE_TAC[] >>
  rw[GSYM SUBMAP_FUNION_ABSORPTION] >>
  match_mp_tac DRESTRICT_SUBMAP_gen >>
  first_assum ACCEPT_TAC)

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀e s e' s'. (label_closures e s = (e',s')) ⇒
       let c = REVERSE (ZIP (GENLIST ($+ s.lnext_label) (LENGTH (free_bods e)), free_bods e)) in
       (s'.lcode_env = c ++ s.lcode_env) ∧
       (s'.lnext_label = s.lnext_label + LENGTH (free_bods e)) ∧
       (set (free_labs e') = set (MAP FST c) ∪ set (free_labs e)) ∧
       (DISJOINT (set (free_labs e)) (set (MAP FST c))
         ⇒ (subst_labs (alist_to_fmap c) e' = e))) ∧
    (∀ds ac s ds' s'. (label_defs ac ds s = (ds',s')) ⇒
       let c = REVERSE (
         ZIP (GENLIST ($+ s.lnext_label) (LENGTH (FILTER (ISL o SND) ds)),
              MAP (OUTL o SND) (FILTER (ISL o SND) ds))) in
       (s'.lcode_env = c ++ s.lcode_env) ∧
       (s'.lnext_label = s.lnext_label + LENGTH (FILTER (ISL o SND) ds)) ∧
       (MAP (λ(xs,cb). (xs,subst_lab_cb (alist_to_fmap c) cb)) ds' = ds)) ∧
    (∀(d:def). T) ∧ (∀(b:Cexp+num). T) ∧
    (∀es s es' s'. (label_closures_list es s = (es',s')) ⇒
       let c = REVERSE (
           ZIP (GENLIST ($+ s.lnext_label) (LENGTH (FLAT (MAP free_bods es))),
                FLAT (MAP free_bods es))) in
       (s'.lcode_env = c ++ s.lcode_env) ∧
       (s'.lnext_label = s.lnext_label + LENGTH (FLAT (MAP free_bods es))) ∧
       (set (FLAT (MAP free_labs es')) =  set (MAP FST c) ∪ set (FLAT (MAP free_labs es))) ∧
       (DISJOINT (set (FLAT (MAP free_labs es))) (set (MAP FST c))
         ⇒ (MAP (subst_labs (alist_to_fmap c)) es' = es)))``,
  ho_match_mp_tac(TypeBase.induction_of(``:Cexp``)) >>
  strip_tac >- (rw[label_closures_def,UNIT_DEF,BIND_DEF] >> rw[]) >>
  strip_tac >- (rw[label_closures_def,UNIT_DEF,BIND_DEF] >> rw[]) >>
  strip_tac >- (rw[label_closures_def,UNIT_DEF,BIND_DEF] >> rw[]) >>
  strip_tac >- (rw[label_closures_def,UNIT_DEF,BIND_DEF] >> rw[]) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = mapM label_closures es s` >> PairCases_on `p` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >>
    srw_tac[ETA_ss][REVERSE_ZIP,LET_THM]) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[]) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[]) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = mapM label_closures es s` >> PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures e p1` >> PairCases_on `q` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >>
    srw_tac[ARITH_ss,ETA_ss][REVERSE_ZIP,ZIP_APPEND,LET_THM] >>
    TRY (
      AP_TERM_TAC  >> rw[] >>
      simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
      AP_TERM_TAC >> rw[] >>
      rw[GENLIST_PLUS_APPEND] >>
      NO_TAC ) >>
    TRY (
      simp[MAP_ZIP,GSYM GENLIST_PLUS_APPEND] >>
      qmatch_abbrev_tac `A = B UNION C` >>
      metis_tac[ADD_SYM,UNION_ASSOC,UNION_COMM] ) >>
    TRY (
      qmatch_abbrev_tac `subst_labs c1 q0 = e` >>
      qmatch_assum_abbrev_tac `P ==> (subst_labs c2 q0 = e)` >>
      `P` by (
        unabbrev_all_tac >>
        qmatch_abbrev_tac `DISJOINT X Y` >>
        qpat_assum `DISJOINT X Z` mp_tac >>
        simp[MAP_ZIP,Abbr`Y`,GSYM GENLIST_PLUS_APPEND] >>
        rw[DISJOINT_SYM] ) >>

      subst_labs_SUBMAP
      subst_labs_any_env

      `set (free_labs q0) ⊆ FDOM c2` by (
        simp[Abbr`c2`,MAP_ZIP] >>
        conj_tac >- (
          rw[SUBSET_DEF,MEM_GENLIST] >>
          metis_tac[] ) >>
        qunabbrev_tac `P` >>
        fs[MAP_ZIP,GSYM GENLIST_PLUS_APPEND] >>

        qabbrev_tac `be = free_bods e` >>
        rw[]
        rw[MEM_GENLIST]
        DB.match [] ``MEM x (GENLIST f l)``
        set_trace"goalstack print goal at top"0

    TRY (
      qmatch_abbrev_tac `MAP (subst_labs c1) p0 = es` >>
      qmatch_assum_abbrev_tac `MAP (subst_labs c2) p0 = es` >>
      qsuff_tac `c2 ⊑ c1` >- PROVE_TAC[subst_labs_SUBMAP]
    )
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_defs [] ds s` >> PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures e p1` >> PairCases_on `q` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`[]`,`s`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ARITH_ss][REVERSE_ZIP,ZIP_APPEND] >>
    AP_TERM_TAC  >> rw[] >>
    simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
    AP_TERM_TAC >> rw[] >>
    srw_tac[ARITH_ss][GENLIST_PLUS_APPEND] ) >>
  strip_tac >- (
    rw[label_closures_def,UNIT_DEF,BIND_DEF] >>
    Cases_on `b` >> fs[label_defs_def,UNIT_DEF,BIND_DEF,LET_THM] >>
    rw[] ) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = mapM label_closures es p1` >> PairCases_on `q` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ARITH_ss,ETA_ss][REVERSE_ZIP,ZIP_APPEND] >>
    AP_TERM_TAC  >> rw[] >>
    simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
    AP_TERM_TAC >> rw[] >>
    srw_tac[ARITH_ss][GENLIST_PLUS_APPEND] ) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures e' p1` >> PairCases_on `q` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ARITH_ss,ETA_ss][REVERSE_ZIP,ZIP_APPEND] >>
    AP_TERM_TAC  >> rw[] >>
    simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
    AP_TERM_TAC >> rw[] >>
    srw_tac[ARITH_ss][GENLIST_PLUS_APPEND] ) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures e' p1` >> PairCases_on `q` >> fs[] >>
    qabbrev_tac`r = label_closures e'' q1` >> PairCases_on `r` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`q1`,`r0`,`r1`] mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ARITH_ss,ETA_ss][REVERSE_ZIP,ZIP_APPEND] >>
    AP_TERM_TAC  >> rw[] >>
    simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
    AP_TERM_TAC >> rw[] >>
    srw_tac[ARITH_ss][GENLIST_PLUS_APPEND] >>
    PROVE_TAC[GENLIST_PLUS_APPEND,ADD_ASSOC,ADD_SYM]) >>
  strip_tac >- rw[label_defs_def,UNIT_DEF] >>
  strip_tac >- (
    qx_gen_tac `d` >> PairCases_on `d` >>
    fs[] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    Cases_on `d1` >> fs[label_defs_def,UNIT_DEF,BIND_DEF] >>
    qmatch_assum_abbrev_tac `label_defs aa ds ss = (ds',s')` >>
    first_x_assum (qspecl_then [`aa`,`ss`,`ds'`,`s'`] mp_tac) >> rw[] >>
    unabbrev_all_tac >> srw_tac[ARITH_ss][] >>
    rw[GENLIST_CONS] >>
    AP_TERM_TAC >> AP_TERM_TAC >>
    AP_THM_TAC >> AP_TERM_TAC >>
    AP_THM_TAC >> AP_TERM_TAC >>
    srw_tac[ARITH_ss][FUN_EQ_THM] ) >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (rw[UNIT_DEF] >> rw[]) >>
  fs[label_closures_def,BIND_DEF,UNIT_DEF] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] >>
  qabbrev_tac`q = mapM label_closures es p1` >> PairCases_on `q` >> fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
  first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[] >>
  srw_tac[ARITH_ss,ETA_ss][REVERSE_ZIP,ZIP_APPEND] >>
  AP_TERM_TAC  >> rw[] >>
  simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
  AP_TERM_TAC >> rw[] >>
  srw_tac[ARITH_ss][GENLIST_PLUS_APPEND])

val subst_labs_free_bods = store_thm("subst_labs_free_bods",
  ``∀e e'. subst_labs
  subst_labs_any_env
  subst_labs_ind
  ``(∀e s e' s'. (label_closures e s = (e',s')) ⇒
       ∃c. (s'.lcode_env = c++s.lcode_env) ∧
         (subst_labs (alist_to_fmap c) e' = e))``,
  rw[] >>
  imp_res_tac label_closures_thm >>
  rw[] >>
  DB.match [] ``alist_to_fmap (ZIP ls)``
  DB.find"alist_to_fmap"

val Cevaluate_subst_labs = store_thm("Cevaluate_subst_labs",
  ``∀c env e res. Cevaluate c env e res ⇒
     ∀e'. (subst_all_labs c e = subst_all_labs c e') ⇒
       ∃res'. Cevaluate c env e' res' ∧
              (map_result (subst_all_labs_v c) res =
               map_result (subst_all_labs_v c) res')``

(* TODO: move *)
val o_f_cong = store_thm("o_f_cong",
  ``!f fm f' fm'.
    (fm = fm') /\
    (!v. v IN FRANGE fm ==> (f v = f' v))
    ==> (f o_f fm = f' o_f fm')``,
  SRW_TAC[DNF_ss][GSYM fmap_EQ_THM,FRANGE_DEF])
val _ = DefnBase.export_cong"o_f_cong"

(*
val slexp_def = Define`
  slexp c = EQC (λe1 e2. e1 = subst_labs c e2)`

val (sldef_rules,sldef_ind,sldef_cases) = Hol_reln`
  (slexp c b1 b2 ∧
   (b1 = case cb1 of INL b => b | INR l => c ' l) ∧
   (b2 = case cb2 of INL b => b | INR l => c ' l)
   ⇒ sldef c (xs,cb1) (xs,cb2))`

val (sleq_rules,sleq_ind,sleq_cases) = Hol_reln`
  (sleq c (CLitv l) (CLitv l)) ∧
  (EVERY2 (sleq c) vs1 vs2
   ⇒ sleq c (CConv cn vs1) (CConv cn vs2)) ∧
  (fmap_rel (sleq c) env1 env2 ∧
   LIST_REL (sldef c) defs1 defs2
   ⇒ sleq c (CRecClos env1 ns defs1 n) (CRecClos env2 ns defs2 n))`

(*
val subst_labs_v_def = tDefine "subst_labs_v"`
  (subst_labs_v c (CLitv l) = CLitv l) ∧
  (subst_labs_v c (CConv cn vs) = CConv cn (MAP (subst_labs_v c) vs)) ∧
  (subst_labs_v c (CRecClos env ns defs n) =
    CRecClos
      (subst_labs_v c o_f env) ns
      (MAP (λ(xs,cb). (xs, subst_lab_cb c cb)) defs)
      n)`(
   WF_REL_TAC `measure (Cv_size o SND)` >>
   srw_tac[ARITH_ss][Cvs_size_thm] >>
   Q.ISPEC_THEN`Cv_size`imp_res_tac SUM_MAP_MEM_bound >>
   srw_tac[ARITH_ss][] >>
   qmatch_abbrev_tac `(q:num) < x + (y + (w + (z + 1)))` >>
   qsuff_tac `q ≤ z` >- fsrw_tac[ARITH_ss][] >>
   unabbrev_all_tac >>
   rw[fmap_size_def] >>
   fs[FRANGE_DEF] >> rw[] >>
   qmatch_abbrev_tac `y <= SIGMA f (FDOM env)` >>
   match_mp_tac LESS_EQ_TRANS >>
   qexists_tac `f x` >>
   conj_tac >- srw_tac[ARITH_ss][o_f_FAPPLY,Abbr`y`,Abbr`f`] >>
   match_mp_tac SUM_IMAGE_IN_LE >>
   rw[])
*)

val slexp_refl = store_thm("slexp_refl",
  ``∀c e. slexp c e e``,
  rw[slexp_def])
val _ = export_rewrites["slexp_refl"]

val sldef_refl = store_thm("sldef_refl",
  ``∀c def. sldef c def def``,
  gen_tac >> Cases >> rw[sldef_cases])
val _ = export_rewrites["sldef_refl"]

val sleq_refl_full = store_thm("sleq_refl_full",
  ``(∀v c. sleq c v v) ∧
    (∀(env:string|->Cv) c. fmap_rel (sleq c) env env) ∧
    (∀vs c. EVERY2 (sleq c) vs vs)``,
  ho_match_mp_tac(TypeBase.induction_of``:Cv``) >>
  rw[] >> TRY (rw[sleq_cases] >> NO_TAC) >>
  rw[sleq_cases] >- (
    match_mp_tac quotient_listTheory.LIST_REL_REFL
    prove all of them are an equivalence in one theorem each?

val sleq_refl = store_thm("sleq_refl",
  ``!c v. sleq c v v``,
  gen_tac >> Induct >> rw[sleq_cases]
  rw[sleq_def])
val _ = export_rewrites["sleq_refl"]

val sleq_sym = store_thm("sleq_sym",
  ``!c v1 v2. sleq c v1 v2 ==> sleq c v2 v1``,
  rw[sleq_def]>>
  metis_tac[EQC_SYM])

val sleq_trans = store_thm("sleq_trans",
  ``!c v1 v2 v3. sleq c v1 v2 ∧ sleq c v2 v3 ⇒ sleq c v1 v3``,
  rw[sleq_def] >>
  metis_tac[EQC_TRANS])

val sleq_CConv = store_thm("sleq_CConv",
  ``sleq c (CConv cn vs) v2 =
    ∃vs'. (v2 = CConv cn vs') ∧
          (EVERY2 (sleq c) vs vs')``,
  rw[sleq_def] >>
  EQ_TAC >> rw[] >- (
    qid_spec_tac `vs` >>
    Induct_on `n` >- (
      rw[EVERY2_EVERY,EVERY_MEM,MEM_ZIP,UNCURRY] >>
      rw[] ) >>
    rw[FUNPOW_SUC] >>
    fs[subst_labs_v_def]
    DB.find"FUNPOW"

val Cevaluate_subst_labs = store_thm("Cevaluate_subst_labs",
  ``∀c env exp res. Cevaluate c env exp res
    ⇒ ∃res'. Cevaluate c env (subst_labs c exp) res' ∧
             result_rel (sleq c) res res'``,
  ho_match_mp_tac Cevaluate_nice_ind >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[Cevaluate_con,Cevaluate_list_with_Cevaluate,
       Cevaluate_list_with_value,EL_MAP] >>
    fsrw_tac[DNF_ss][]

       ) >>
  strip_tac >- (
    rw[Cevaluate_con,Cevaluate_list_with_Cevaluate,
       Cevaluate_list_with_error] >>
    qexists_tac `n` >>
    fsrw_tac[ETA_ss,DNF_ss,ARITH_ss][EL_MAP] ) >>
  strip_tac >- (
    rw[Cevaluate_tageq] >> PROVE_TAC[] ) >>
  strip_tac >- rw[Cevaluate_tageq] >>
  strip_tac >- (
    rw[Cevaluate_proj] >> PROVE_TAC[] ) >>
  strip_tac >- rw[Cevaluate_proj] >>
  strip_tac >- rw[] >>
  strip_tac >- (
    rw[Cevaluate_let_cons] >>
    PROVE_TAC[] ) >>
  strip_tac >- rw[Cevaluate_let_cons] >>
  strip_tac >- (
    rw[] >>
    srw_tac[DNF_ss][Once Cevaluate_cases,MEM_MAP]
*)

val Cevaluate_label_closures = store_thm("Cevaluate_label_closures",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      ∀s. Cevaluate c env (FST (label_closures exp s)) res``,
  ho_match_mp_tac Cevaluate_nice_ind



define a non-monadic version of (half of) label_closures that just collects the bodies in a list
and perhaps another function that substitutes bodies for numbers from a given list

val label_closures_thm1 = store_thm("label_closures_thm1",
  ``(∀e s e' s'. (label_closures e s = (e',s')) ⇒
         ∃ce. (s'.lcode_env = ce++s.lcode_env) ∧
           ∀c env res. Cevaluate c env e res ⇒ Cevaluate (c⊌(alist_to_fmap ce)) env e' res) ∧
    (∀(ds:def list). T) ∧ (∀d:def. T) ∧ (∀(b:Cexp+num). T) ∧
    (∀es s es' s'. (label_closures_list es s = (es',s')) ⇒
         ∃ce. (s'.lcode_env = ce++s.lcode_env) ∧
           ∀c env res. Cevaluate_list c env es res ⇒ Cevaluate_list (c⊌(alist_to_fmap ce)) env es' res)``,
  ho_match_mp_tac(TypeBase.induction_of``:Cexp``) >>
  rw[label_closures_def,UNIT_DEF,BIND_DEF,FUNION_FEMPTY_2] >>
  rw[Cevaluate_raise,Cevaluate_var,Cevaluate_lit] >>
  cheat)

val FUNION_FEMPTY_FUPDATE = store_thm("FUNION_FEMPTY_FUPDATE",
  ``k ∉ FDOM fm ⇒ (fm ⊌ FEMPTY |+ (k,v) = fm |+ (k,v))``,
  rw[FUNION_FUPDATE_2,FUNION_FEMPTY_2])

val repeat_label_closures_thm1 = store_thm("repeat_label_closures_thm1",
  ``(∀e n ac e' n' ac'. (repeat_label_closures e n ac = (e',n',ac')) ⇒
       ∃ce. (ac' = ce++ac) ∧
         ∀c env res. Cevaluate c env e res ⇒ Cevaluate (c⊌(alist_to_fmap ce)) env e' res) ∧
    (∀n ac ls n' ac'. (label_code_env n ac ls = (n',ac')) ⇒
       ∃ce. (ac' = ce++ac) ∧
         ∀c env e res. Cevaluate (c⊌(alist_to_fmap ls)) env e res ⇒ Cevaluate (c⊌(alist_to_fmap ce)) env e res)``,
  ho_match_mp_tac repeat_label_closures_ind >>
  rw[repeat_label_closures_def,FUNION_FEMPTY_2,LET_THM]
  >- (
    qabbrev_tac `p = label_closures e <|lnext_label := n; lcode_env := []|>` >>
    PairCases_on `p` >> fs[] >>
    qabbrev_tac `q = label_code_env p1.lnext_label ac p1.lcode_env` >>
    PairCases_on `q` >> fs[] >> rw[] >>
    first_x_assum match_mp_tac >>
    fs[markerTheory.Abbrev_def] >>
    qmatch_assum_abbrev_tac `(e',s') = label_closures e s` >>
    qspecl_then [`e`,`s`,`e'`,`s'`] mp_tac (CONJUNCT1 label_closures_thm1) >>
    rw[] >> unabbrev_all_tac >> fs[] )
  >- (
    fs[]
    ... need to move to syneq to allow FUPDATE of code_env ...
     )
  >- (
    qabbrev_tac `p = label_closures e <|lnext_label := n; lcode_env := []|>` >>
    PairCases_on `p` >> fs[] >>
    qabbrev_tac `q = label_code_env p1.lnext_label ac p1.lcode_env` >>
    PairCases_on `q` >> fs[] >> rw[] >>

val _ = export_theory()
