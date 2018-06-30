open preamble miscTheory astTheory namespaceTheory typeSystemTheory;
open terminationTheory namespacePropsTheory;

val _ = new_theory "type_dCanon"

(* A "canonical" version of type_d that produces the type identifiers
  in ascending order.
  It also drops the extra_checks argument so it corresponds to type_d T,
  but adds a starting index, and an argument for the number of
  type ids that got produced.
*)

val (type_d_canon_rules, type_d_canon_ind, type_d_canon_cases) = Hol_reln `
(!n tvs tenv p e t bindings locs.
  (is_value e /\
  ALL_DISTINCT (pat_bindings p []) /\
  type_p tvs tenv p t bindings /\
  type_e tenv (bind_tvar tvs Empty) e t /\
  (! tvs' bindings' t'.
  (type_p tvs' tenv p t' bindings' /\
      type_e tenv (bind_tvar tvs' Empty) e t') ==>
        EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings')) (MAP SND (tenv_add_tvs tvs bindings))))
  ==>
  type_d_canon n tenv (Dlet locs p e)
    0
    <| v := (alist_to_ns (tenv_add_tvs tvs bindings)); c := nsEmpty; t := nsEmpty |>) ∧
(!n tenv p e t bindings locs.
  ((~ (is_value e) /\ type_pe_determ tenv Empty p e) /\
  ALL_DISTINCT (pat_bindings p []) /\
  type_p(( 0 : num)) tenv p t bindings /\
  type_e tenv Empty e t)
  ==>
  type_d_canon n tenv (Dlet locs p e)
    0 <| v := (alist_to_ns (tenv_add_tvs(( 0 : num)) bindings)); c := nsEmpty; t := nsEmpty |>) ∧
(!n tenv funs bindings tvs locs.
  (type_funs tenv (bind_var_list(( 0 : num)) bindings (bind_tvar tvs Empty)) funs bindings /\
  (! tvs' bindings'.
      type_funs tenv (bind_var_list(( 0 : num)) bindings' (bind_tvar tvs' Empty)) funs bindings' ==>
        EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings')) (MAP SND (tenv_add_tvs tvs bindings))))
  ==>
  type_d_canon n tenv (Dletrec locs funs)
  0 <| v := (alist_to_ns (tenv_add_tvs tvs bindings)); c := nsEmpty; t := nsEmpty |>) ∧
(!n type_identities tenv tdefs tenvT locs.
  (FOLDR MAX 0 (Tlist_num :: (Tbool_num :: prim_type_nums)) < n ∧
  type_identities = GENLIST (\i. i+n) (LENGTH tdefs) ∧
  check_ctor_tenv (nsAppend tenvT tenv.t) tdefs /\
  (tenvT = alist_to_ns (MAP2
                        (\ (tvs,tn,ctors) i .
                          (tn, (tvs, Tapp (MAP Tvar tvs) i)))
                        tdefs type_identities)))
  ==>
  type_d_canon n tenv (Dtype locs tdefs)
    (LENGTH tdefs)
    <| v := nsEmpty; c := (build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities); t := tenvT |>) ∧
(!n tenv tvs tn t locs.
  (check_freevars_ast tvs t /\
  check_type_names tenv.t t /\
  ALL_DISTINCT tvs)
  ==>
  type_d_canon n tenv (Dtabbrev locs tvs tn t)
    0
    <| v := nsEmpty; c := nsEmpty; t := (nsSing tn (tvs,type_name_subst tenv.t t)) |>) ∧
(!n tenv cn ts locs.
  (EVERY (check_freevars_ast []) ts /\
  EVERY (check_type_names tenv.t) ts)
  ==>
  type_d_canon n tenv (Dexn locs cn ts)
    0
    <| v := nsEmpty;
       c := (nsSing cn ([], MAP (type_name_subst tenv.t) ts, Texn_num));
       t := nsEmpty |>) ∧
(!n tenv mn ds decls tenv'.
  (type_ds_canon n tenv ds decls tenv')
  ==>
  type_d_canon n tenv (Dmod mn ds) decls (tenvLift mn tenv')) ∧
(!n tenv.
  T
  ==>
  type_ds_canon n tenv []
    0
    <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>) ∧
(!n tenv d ds tenv1 tenv2 decls1 decls2.
  (type_d_canon n tenv d decls1 tenv1 /\
  type_ds_canon (n+decls1) (extend_dec_tenv tenv1 tenv) ds decls2 tenv2)
  ==>
  type_ds_canon n tenv (d::ds)
    (decls1 + decls2) (extend_dec_tenv tenv2 tenv1))`;

(* Rename (type_system) type identifiers with a function *)
val ts_tid_rename_def = tDefine"ts_tid_rename"`
  (ts_tid_rename f (Tapp ts tn) = Tapp (MAP (ts_tid_rename f) ts) (f tn)) ∧
  (ts_tid_rename f t = t)`
  (WF_REL_TAC `measure (λ(_,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac);

val remap_tenv_def = Define`
  remap_tenv f tenv =
  <|
    t := nsMap (λ(ls,t). (ls, ts_tid_rename f t)) tenv.t;
    c := nsMap (λ(ls,ts,tid). (ls, MAP (ts_tid_rename f) ts, f tid)) tenv.c;
    v := nsMap (λ(n,t). (n,ts_tid_rename f t)) tenv.v
   |>`

(* All type ids in a type belonging to a set *)
val set_tids_def = tDefine "set_tids"`
  (set_tids tids (Tapp ts tn) ⇔ tn ∈ tids ∧ EVERY (set_tids tids) ts) ∧
  (set_tids tids _ ⇔ T)`
  (WF_REL_TAC `measure (λ(_,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac)

(* all the tids used in a tenv *)
val set_tids_tenv_def = Define`
  set_tids_tenv tids tenv ⇔
  nsAll (λi (ls,t). set_tids tids t) tenv.t ∧
  nsAll (λi (ls,ts,tid). EVERY (set_tids tids) ts ∧ tid ∈ tids) tenv.c ∧
  nsAll (λi (n,t). set_tids tids t) tenv.v`

(* The remapping must be identity on these numbers *)
val good_remap_def = Define`
  good_remap f ⇔
  MAP f (Tlist_num :: (Tbool_num :: prim_type_nums)) =
    Tlist_num :: (Tbool_num :: prim_type_nums)`

val ts_tid_rename_type_subst = Q.prove(`
  ∀s t f.
  ts_tid_rename f (type_subst s t) =
  type_subst (ts_tid_rename f o_f s) (ts_tid_rename f t)`,
  ho_match_mp_tac type_subst_ind>>
  rw[type_subst_def,ts_tid_rename_def]
  >- (
    TOP_CASE_TAC>>fs[FLOOKUP_o_f,ts_tid_rename_def])
  >>
    fs[MAP_MAP_o,MAP_EQ_f]);

val ts_tid_rename_type_name_subst = Q.prove(`
  ∀tenvt t f tenv.
  good_remap f ∧
  check_type_names tenvt t ⇒
  ts_tid_rename f (type_name_subst tenvt t) =
  type_name_subst (nsMap (λ(ls,t). (ls,ts_tid_rename f t)) tenvt) t`,
  ho_match_mp_tac type_name_subst_ind>>rw[]>>
  fs[type_name_subst_def,ts_tid_rename_def,check_type_names_def,EVERY_MEM]
  >- (
    reverse CONJ_TAC >- fs[good_remap_def,prim_type_nums_def]>>
    fs[MAP_MAP_o,MAP_EQ_f])
  >-
    fs[good_remap_def,prim_type_nums_def]
  >- (
    simp[nsLookup_nsMap]>>
    TOP_CASE_TAC>>fs[ts_tid_rename_def]>>
    pairarg_tac>>fs[ts_tid_rename_def]>>
    simp[ts_tid_rename_type_subst]>>
    AP_THM_TAC >> AP_TERM_TAC>>
    fs[GSYM alist_to_fmap_MAP_values]>>
    AP_TERM_TAC>>
    match_mp_tac LIST_EQ>>fs[EL_MAP,EL_ZIP]>>
    metis_tac[EL_MEM]));

val check_type_names_ts_tid_rename = Q.prove(`
  ∀tenvt t.
  check_type_names tenvt t <=>
  check_type_names (nsMap (λ(ls,t). (ls,ts_tid_rename f t)) tenvt) t`,
  ho_match_mp_tac check_type_names_ind>>rw[check_type_names_def]>>
  fs[EVERY_MEM,nsLookup_nsMap]>>
  Cases_on`nsLookup tenvt tn`>>fs[]>>
  pairarg_tac>>fs[]);

val extend_bij_def = Define`
  extend_bij (f:type_ident->type_ident) g ids n v =
  if v ∈ ids then
    n + g v
  else
    f v`

val prim_tids_def = Define`
  prim_tids contain tids ⇔
    EVERY (\x. x ∈ tids ⇔ contain) (Tlist_num::Tbool_num::prim_type_nums)`

val set_tids_type_subst = Q.prove(`
  ∀s t tids.
  FEVERY (set_tids tids o SND) s ∧
  set_tids tids t ⇒
  set_tids tids (type_subst s t)`,
  ho_match_mp_tac type_subst_ind>>
  rw[type_subst_def,set_tids_def]
  >- (
    TOP_CASE_TAC>>fs[set_tids_def]>>
    drule (GEN_ALL FEVERY_FLOOKUP)>>fs[]>>
    metis_tac[])
  >-
    fs[EVERY_MAP,EVERY_MEM]);

val MEM_ZIP2 = Q.prove(`
  ∀l1 l2 x.
  MEM x (ZIP (l1,l2)) ⇒
  ∃n. n < LENGTH l1 ∧ n < LENGTH l2 ∧ x = (EL n l1,EL n l2)`,
  Induct>>fs[ZIP_def]>>
  Cases_on`l2`>>fs[ZIP_def]>>
  rw[]
  >-
    (qexists_tac`0n`>>fs[])
  >>
    first_x_assum drule>>
    rw[]>>
    qexists_tac`SUC n`>>fs[]);

val set_tids_type_name_subst = Q.prove(`
  ∀tenvt t tids.
  prim_tids T tids ∧
  nsAll (λi (ls,t). set_tids tids t) tenvt ==>
  set_tids tids (type_name_subst tenvt t)`,
  ho_match_mp_tac type_name_subst_ind>>
  rw[set_tids_def,type_name_subst_def]
  >- fs[prim_tids_def,prim_type_nums_def]
  >- fs[EVERY_MAP,EVERY_MEM]
  >- fs[prim_tids_def,prim_type_nums_def]
  >>
    TOP_CASE_TAC>>fs[set_tids_def,EVERY_MAP,EVERY_MEM]
    >- fs[prim_tids_def,prim_type_nums_def]
    >>
      TOP_CASE_TAC>>fs[]>>
      match_mp_tac set_tids_type_subst>>
      CONJ_TAC
      >- (
        match_mp_tac FEVERY_alist_to_fmap>>fs[EVERY_MEM,MEM_ZIP]>>
        rw[]>>
        imp_res_tac MEM_ZIP2>>
        fs[EL_MAP]>>
        metis_tac[MEM_EL])
      >>
        drule nsLookup_nsAll >> disch_then drule>>
        simp[]);

val extend_bij_id = Q.store_thm("extend_bij_id[simp]",`
  (extend_bij f f s 0 = f) ∧
  (extend_bij f f {} n = f)`,
  rw[extend_bij_def,FUN_EQ_THM]);

(* needs monotonicity of set_tids_tenv *)
val set_tids_tenv_extend_dec_tenv = Q.prove(`
  ∀s t s' t'.
  set_tids_tenv (s' ∪ s) t' ∧
  set_tids_tenv (s' ∪ s) t ⇒
  set_tids_tenv (s' ∪ s) (extend_dec_tenv t' t)`,
  rw[extend_dec_tenv_def,set_tids_tenv_def,nsAll_nsAppend]);

val good_remap_extend_bij = Q.prove(`
  good_remap f ∧ prim_tids F ids ⇒
  good_remap (extend_bij f g ids n)`,
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]);

val remap_tenv_extend_dec_tenv = Q.prove(`
  remap_tenv f (extend_dec_tenv t t') =
  extend_dec_tenv (remap_tenv f t) (remap_tenv f t')`,
  fs[remap_tenv_def,extend_dec_tenv_def,nsMap_nsAppend]);

(* slow proof *)
val INJ_extend_bij = Q.prove(`
  DISJOINT tids ids ∧
  INJ f tids (count n) ∧
  INJ g ids (count (CARD ids)) ⇒
  INJ (extend_bij f g ids n) (tids ∪ ids) (count (n + CARD ids))`,
  rw[INJ_DEF,extend_bij_def]>>rw[]
  >- (last_x_assum drule>>fs[])>>
  rfs[]>>
  fs[IN_DISJOINT]>>
  EVERY_CASE_TAC>>fs[]>>
  rpt (first_x_assum drule)>>fs[]>>
  metis_tac[]);

val set_tids_ind = fetch "-" "set_tids_ind";

val set_tids_mono = Q.prove(`
  ∀tids t tids'.
  set_tids tids t ∧ tids ⊆ tids' ⇒
  set_tids tids' t`,
  ho_match_mp_tac set_tids_ind>>
  rw[set_tids_def,SUBSET_DEF,EVERY_MEM]);

val set_tids_tenv_mono = Q.prove(`
  set_tids_tenv tids tenv ∧ tids ⊆ tids' ⇒
  set_tids_tenv tids' tenv`,
  fs[set_tids_tenv_def]>>rw[]>>
  irule nsAll_mono
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ pairarg_tac \\ fs[EVERY_MEM,SUBSET_DEF]
  \\ metis_tac[set_tids_mono,SUBSET_DEF]);

val check_freevars_ts_tid_rename = Q.prove(`
  ∀ts ls t.
  check_freevars ts ls (ts_tid_rename f t) ⇔
  check_freevars ts ls t`,
  ho_match_mp_tac check_freevars_ind>>
  fs[ts_tid_rename_def,check_freevars_def,EVERY_MAP,EVERY_MEM]);

val type_p_ts_tid_rename = Q.store_thm("type_p_ts_tid_rename",`
  good_remap f ⇒
  (∀tvs tenv p t bindings.
  type_p tvs tenv p t bindings ⇒
  type_p tvs (remap_tenv f tenv) p (ts_tid_rename f t)
    (MAP (λn,t. (n,ts_tid_rename f t)) bindings)) ∧
  (∀tvs tenv ps ts bindings.
  type_ps tvs tenv ps ts bindings ⇒
  type_ps tvs (remap_tenv f tenv) ps (MAP (ts_tid_rename f) ts)
    (MAP (λn,t. (n,ts_tid_rename f t)) bindings))`,
  strip_tac>>
  ho_match_mp_tac type_p_strongind>>
  rw[]>>
  simp[Once type_p_cases,check_freevars_ts_tid_rename,ts_tid_rename_def]>>
  TRY(fs[good_remap_def,prim_type_nums_def]>>NO_TAC)
  >- (
    fs[MAP_MAP_o,o_DEF,ts_tid_rename_type_subst]>>
    fs[remap_tenv_def,nsLookup_nsMap]>>
    CONJ_TAC>-
      fs[EVERY_MAP,EVERY_MEM,check_freevars_ts_tid_rename]>>
    simp[MAP_MAP_o,o_DEF]>>
    fs[GSYM alist_to_fmap_MAP_values,ZIP_MAP,LAMBDA_PROD])
  >- (
    fs[good_remap_def,prim_type_nums_def]>>metis_tac[ETA_AX])
  >- (
    fs[ts_tid_rename_type_name_subst,remap_tenv_def,GSYM check_type_names_ts_tid_rename]>>
    metis_tac[ts_tid_rename_type_name_subst])
  >>
    metis_tac[]);

(* For any type_d, prove that the canonical type identifier strategy
  succeeds.
  f,g are maps from the identifiers used in type_d into the ones
  used by type_d_canon
  TODO: do we actually need the bijection??
*)
val type_d_type_d_canon = Q.store_thm("type_d_type_d_canon",`
(∀extra_checks tenv d ids tenv'.
  type_d extra_checks tenv d ids tenv' ==>
  ∀tids f n.
  (* These restrict the kinds of type_d that we are thinking about *)
  extra_checks = T ∧
  DISJOINT ids tids ∧
  (* Over-approximation of the tids in tenv *)
  set_tids_tenv tids tenv ∧
  (* f injects all of the tids already used in tenv into the canonical system *)
  INJ f tids (count n) ∧
  (* tids contains at least the primitive type numbers and f is identity on them *)
  prim_tids T tids ∧ good_remap f ⇒
  ∃g.
    (* This is actually a property of the type system *)
    set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧ FINITE ids ∧
    (* This forces g to extend the injection on f *)
    INJ g ids (count (CARD ids)) ∧
    type_d_canon n (remap_tenv f tenv) d (CARD ids)
      (remap_tenv (extend_bij f g ids n) tenv')) ∧
(∀extra_checks tenv ds ids tenv'.
  type_ds extra_checks tenv ds ids tenv' ==>
  ∀tids f n.
  extra_checks = T ∧
  DISJOINT ids tids ∧
  set_tids_tenv tids tenv ∧
  INJ f tids (count n) ∧
  prim_tids T tids ∧ good_remap f ⇒
  ∃g.
    set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧ FINITE ids ∧
    INJ g ids (count (CARD ids)) ∧
    type_ds_canon n (remap_tenv f tenv) ds (CARD ids)
      (remap_tenv (extend_bij f g ids n) tenv'))`,
  ho_match_mp_tac type_d_strongind>>
  rw[]>>fs[]
  >- (
    (* Dlet poly *)
    fs[set_tids_tenv_def,tenv_add_tvs_def]>>
    qexists_tac`f`>>simp[]>>
    CONJ_TAC>- (
      match_mp_tac nsAll_alist_to_ns>>
      simp[EVERY_MAP,EVERY_MEM,FORALL_PROD]>>
      (* this should be a property of bindings by type_p *)
      cheat)>>
    simp[prim_tids_def, Once type_d_canon_cases]>>
    simp[remap_tenv_def]>>
    cheat)
  >- ((* Dlet mono *)
    fs[set_tids_tenv_def,tenv_add_tvs_def]>>
    qexists_tac`f`>>simp[]>>
    CONJ_TAC >- (
      match_mp_tac nsAll_alist_to_ns>>
      simp[EVERY_MAP,EVERY_MEM,FORALL_PROD]>>
      cheat)>>
    simp[prim_tids_def, Once type_d_canon_cases]>>
    simp[Once remap_tenv_def]>>
    qexists_tac`ts_tid_rename f t`>>
    qexists_tac`MAP (\n,t. (n,ts_tid_rename f t)) bindings`>>
    CONJ_TAC >-
      simp[tenv_add_tvs_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
    cheat)
  >- ((* Dletrec *)
    cheat )
  >- ((* Dtype - important! try and finish this first *)
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >- (
      rw[set_tids_tenv_def]
      >- (
        match_mp_tac nsAll_alist_to_ns>>
        simp[MAP2_MAP,EVERY_MAP,EVERY_MEM,MEM_MAP,EXISTS_PROD,MEM_ZIP,FORALL_PROD,PULL_EXISTS,set_tids_def]>>
        metis_tac[MEM_EL])
      >>
        cheat)>>
    CONJ_TAC>- fs[prim_tids_def,prim_type_nums_def]>>
    (* the injection maps each type_identity to its position in list *)
    qexists_tac
    `λv. case ALOOKUP (ZIP(type_identities,COUNT_LIST (LENGTH type_identities))) v of
      SOME t => t | NONE => 0`>>
    rw[]
    >-
      (simp[INJ_DEF]>>rw[]>>
      cheat)
    >>
    simp[Once type_d_canon_cases]>>
    fs[ALL_DISTINCT_CARD_LIST_TO_SET]>>
    CONJ_TAC >-
      cheat>>
    SIMP_TAC std_ss [CONJ_ASSOC]>>
    CONJ_TAC >- (
      fs[prim_tids_def,INJ_DEF,good_remap_def,prim_type_nums_def]>>
      metis_tac[])>>
    cheat)
  >- ( (* Dtabbrev - sanity check *)
    qexists_tac`f`>>
    simp[set_tids_tenv_def]>>
    CONJ_TAC >- (
      match_mp_tac set_tids_type_name_subst>>
      fs[set_tids_tenv_def])>>
    simp[Once type_d_canon_cases, prim_tids_def]>>
    CONJ_TAC>- (
      fs[remap_tenv_def]>>
      dep_rewrite.DEP_REWRITE_TAC [ts_tid_rename_type_name_subst]>>fs[])>>
    fs[remap_tenv_def]>>
    metis_tac[check_type_names_ts_tid_rename,ts_tid_rename_type_name_subst])
  >- ( (* Dexn - sanity check *)
    qexists_tac`f`>>
    simp[set_tids_tenv_def]>>
    CONJ_TAC >- (
      fs[EVERY_MAP,EVERY_MEM]>>rw[]
      >- (match_mp_tac set_tids_type_name_subst>>fs[set_tids_tenv_def])>>
      fs[prim_tids_def,prim_type_nums_def])>>
    CONJ_TAC >- fs[prim_tids_def,prim_type_nums_def]>>
    simp[Once type_d_canon_cases, prim_tids_def,remap_tenv_def,nsSing_def,nsMap_def]>>
    cheat)
  >- ( (* Dmod *)
    first_x_assum drule>>
    rpt (disch_then drule) >> rw[]>>
    qexists_tac`g`>>fs[]>>
    CONJ_TAC >- fs[tenvLift_def,set_tids_tenv_def]>>
    simp[Once type_d_canon_cases]>>
    qexists_tac`remap_tenv (extend_bij f g ids n) tenv'`>>
    fs[remap_tenv_def,tenvLift_def,namespacePropsTheory.nsLift_nsMap])
  >- simp[set_tids_tenv_def,Once type_d_canon_cases,remap_tenv_def, prim_tids_def]
  >> (*type_ds -- this MUST go through inductively *)
  last_x_assum drule>> fs[]>>
  disch_then drule>> rw[]>>
  simp[Once type_d_canon_cases]>>
  first_x_assum (qspecl_then
    [`tids ∪ ids`,`extend_bij f g ids n`,`CARD ids + n`] mp_tac)>>
  impl_tac >- (
    fs[good_remap_extend_bij,prim_tids_def,prim_type_nums_def]>>
    rfs[DISJOINT_SYM]>>
    CONJ_TAC>-(
      match_mp_tac set_tids_tenv_extend_dec_tenv>>fs[]>>
      match_mp_tac (GEN_ALL set_tids_tenv_mono)>>
      asm_exists_tac>>fs[])>>
    match_mp_tac INJ_extend_bij>>fs[DISJOINT_SYM])>>
  rw[]>>
  qexists_tac `extend_bij g g' ids' (CARD ids)`>>
  rw[]
  >- (
    match_mp_tac set_tids_tenv_extend_dec_tenv>>fs[]>>
    simp[UNION_ASSOC]>>
    match_mp_tac (GEN_ALL set_tids_tenv_mono)>>
    qpat_x_assum`_ _ tenv` assume_tac>>
    asm_exists_tac>>fs[SUBSET_DEF])
  >- fs[prim_tids_def,prim_type_nums_def]
  >-
    (`CARD (ids ∪ ids') = CARD ids' + CARD ids` by
      (imp_res_tac CARD_UNION>>rfs[DISJOINT_DEF])>>
    simp[]>>
    match_mp_tac INJ_extend_bij>>
    fs[])
  >>
  qexists_tac`(remap_tenv (extend_bij f g ids n) tenv')`>>
  qexists_tac` (remap_tenv (extend_bij (extend_bij f g ids n) g' ids' (n + CARD ids)) tenv'')`>>
  qexists_tac`CARD ids`>>
  qexists_tac`CARD ids'`>>
  rw[]
  >- (imp_res_tac CARD_UNION>>rfs[DISJOINT_DEF])
  >-
    (simp[remap_tenv_extend_dec_tenv]>>
    cheat)
  >>
  fs[remap_tenv_extend_dec_tenv]>>
  (* true thanks to disjointness *)
  `remap_tenv (extend_bij f g ids n) tenv =
    remap_tenv f tenv` by cheat>>
  fs[]);

val _ = export_theory();
