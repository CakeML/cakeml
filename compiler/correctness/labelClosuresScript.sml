open HolKernel boolLib boolSimps bossLib quantHeuristicsLib pairTheory listTheory
open rich_listTheory finite_mapTheory pred_setTheory state_transformerTheory lcsymtacs
open miscTheory intLangTheory compileTerminationTheory
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
  (subst_lab_cb c (INR l) = INL (FAPPLY c l))`

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

val subst_labs_any_env = store_thm("subst_labs_any_env",
  ``∀c e c'. (set (free_labs e) ⊆ FDOM c) ⇒
             (subst_labs c e = subst_labs ((DRESTRICT c (set (free_labs e))) ⊌ c') e)``,
  ho_match_mp_tac subst_labs_ind >>
  srw_tac[ETA_ss][MAP_EQ_f] >>
  fsrw_tac[DNF_ss][] >>
  TRY (
    qmatch_abbrev_tac `subst_labs c ee = subst_labs (DRESTRICT c ss ⊌ cc) ee` >>
    `set (free_labs ee) ⊆ FDOM c` by (
      unabbrev_all_tac >>
      fsrw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
      metis_tac[] ) >>
    `∀c'. subst_labs c ee = subst_labs ((DRESTRICT c (set (free_labs ee))) ⊌ c') ee`
      by metis_tac[] >>
    qsuff_tac `∃c'. DRESTRICT c ss ⊌ cc = DRESTRICT c (set (free_labs ee)) ⊌ c'`
      >- metis_tac[] >>
    match_mp_tac DRESTRICT_FUNION_SUBSET >>
    unabbrev_all_tac >>
    srw_tac[DNF_ss][SUBSET_DEF,MEM_FLAT,MEM_MAP] >>
    metis_tac[] )
  >- (
    PairCases_on `e'` >> fs[] >>
    Cases_on `e'1` >> rw[] >>
    rw[FUNION_DEF,DRESTRICT_DEF] >>
    fsrw_tac[DNF_ss][SUBSET_DEF,MEM_MAP,MEM_FILTER,FORALL_PROD] >>
    fsrw_tac[QUANT_INST_ss[std_qp]][] >> metis_tac[])
  >- (
    Cases_on `cb` >> fs[FUNION_DEF,DRESTRICT_DEF]))

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
  rw[Once arithmeticTheory.ADD_SYM,SimpRHS] >>
  srw_tac[ARITH_ss][GENLIST_APPEND] >>
  srw_tac[ETA_ss][arithmeticTheory.ADD_ASSOC])

val label_closures_thm = store_thm("label_closures_thm",
  ``(∀e s e' s'. (label_closures e s = (e',s')) ⇒
       (s'.lcode_env = REVERSE (ZIP (GENLIST ($+ s.lnext_label) (LENGTH (free_bods e)), free_bods e)) ++ s.lcode_env) ∧
       (s'.lnext_label = s.lnext_label + LENGTH (free_bods e))) ∧
    (∀ds ac s ds' s'. (label_defs ac ds s = (ds',s')) ⇒
       (s'.lcode_env = REVERSE (
         ZIP (GENLIST ($+ s.lnext_label) (LENGTH (FILTER (ISL o SND) ds)),
              MAP (OUTL o SND) (FILTER (ISL o SND) ds)))
         ++ s.lcode_env) ∧
       (s'.lnext_label = s.lnext_label + LENGTH (FILTER (ISL o SND) ds))) ∧
    (∀(d:def). T) ∧ (∀(b:Cexp+num). T) ∧
    (∀es s es' s'. (label_closures_list es s = (es',s')) ⇒
       (s'.lcode_env = REVERSE (
           ZIP (GENLIST ($+ s.lnext_label) (LENGTH (FLAT (MAP free_bods es))),
                FLAT (MAP free_bods es)))
        ++ s.lcode_env) ∧
       (s'.lnext_label = s.lnext_label + LENGTH (FLAT (MAP free_bods es))))``,
  ho_match_mp_tac(TypeBase.induction_of(``:Cexp``)) >>
  strip_tac >- rw[label_closures_def,UNIT_DEF,BIND_DEF] >>
  strip_tac >- rw[label_closures_def,UNIT_DEF,BIND_DEF] >>
  strip_tac >- rw[label_closures_def,UNIT_DEF,BIND_DEF] >>
  strip_tac >- rw[label_closures_def,UNIT_DEF,BIND_DEF] >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = mapM label_closures es s` >> PairCases_on `p` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ETA_ss][REVERSE_ZIP]) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] ) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = label_closures e s` >> PairCases_on `p` >> fs[] ) >>
  strip_tac >- (
    fs[label_closures_def,UNIT_DEF,BIND_DEF] >>
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qabbrev_tac`p = mapM label_closures es s` >> PairCases_on `p` >> fs[] >>
    qabbrev_tac`q = label_closures e p1` >> PairCases_on `q` >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >> rw[] >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >> rw[] >>
    srw_tac[ARITH_ss,ETA_ss][REVERSE_ZIP,ZIP_APPEND] >>
    AP_TERM_TAC  >> rw[] >>
    simp_tac(std_ss)[GSYM REVERSE_APPEND] >>
    AP_TERM_TAC >> rw[] >>
    rw[GENLIST_PLUS_APPEND] ) >>
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
    PROVE_TAC[GENLIST_PLUS_APPEND,arithmeticTheory.ADD_ASSOC,arithmeticTheory.ADD_SYM]) >>
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

val Cevaluate_subst_labs = store_thm("Cevaluate_subst_labs",
  ``∀c env exp res. Cevaluate c env e res ⇒ Cevaluate c env (subst_labs c e) res``,
  ho_match_mp_tac Cevaluate_nice_ind >>

val Cevaluate_label_closures = store_thm("Cevaluate_label_closures",
  ``∀c env exp res. Cevaluate c env exp res ⇒
      ∀s. Cevaluate c env (FST (label_closures exp s)) res``,
  ho_match_mp_tac Cevaluate_nice_ind


val label_closures_subst_labs = store_thm("label_closures_subst_labs",
  ``(∀e s e' s'. (label_closures e s = (e',s')) ⇒
       ∃c. (s'.lcode_env = c++s.lcode_env) ∧
         (subst_labs (alist_to_fmap c) e' = e)) ∧
    (∀(x:def list). T) ∧ (∀(x:def). T) ∧ (∀(x:Cexp+num). T) ∧
    (∀es s es' s'. (label_closures_list es s = (es',s')) ⇒
       ∃c. (s'.lcode_env = c++s.lcode_env) ∧
         (MAP (subst_labs (alist_to_fmap c)) es' = es))``,
  ho_match_mp_tac(TypeBase.induction_of(``:Cexp``)) >>
  rw[label_closures_def,UNIT_DEF,BIND_DEF] >> rw[] >>
  TRY (
    full_split_pairs_tac P >> fs[] >> rw[] >>
    res_tac >> rw[] >> srw_tac[ETA_ss][] >> NO_TAC) >>
  >- (
    qabbrev_tac `p = mapM label_closures es s`  >>
    PairCases_on `p` >> fs[] >>
    qabbrev_tac `q = label_closures e p1` >>
    PairCases_on `q` >> fs[] >> rw[] >>
    first_x_assum (qspecl_then [`p1`,`q0`,`q1`] mp_tac) >>
    first_x_assum (qspecl_then [`s`,`p0`,`p1`] mp_tac) >>
    rw[] >>
    qmatch_assum_rename_tac `p1.lcode_env = cp ++ s.lcode_env`[] >>
    qmatch_assum_rename_tac `q1.lcode_env = cq ++ p1.lcode_env`[] >>
    qexists_tac `cq ++ cp` >>
    fsrw_tac[ETA_ss][MAP_EQ_f]


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
