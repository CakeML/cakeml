open preamble miscTheory astTheory namespaceTheory typeSystemTheory;
open terminationTheory namespacePropsTheory;

val _ = new_theory "type_dCanon"

(* TODO: move *)

val nsMap_compose = Q.store_thm("nsMap_compose",
  `∀g e f. nsMap f (nsMap g e) = nsMap (f o g) e`,
  recInduct nsMap_ind
  \\ rw[nsMap_def, MAP_MAP_o, o_DEF, FORALL_PROD, EXISTS_PROD, LAMBDA_PROD, MAP_EQ_f]
  \\ metis_tac[]);

val nsMap_I = Q.store_thm("nsMap_I[simp]",
  `∀ns. nsMap I ns = ns`,
  `∀ns f. f = I ⇒ nsMap f ns = ns` suffices_by rw[]
  \\ CONV_TAC SWAP_FORALL_CONV
  \\ recInduct nsMap_ind
  \\ rw[nsMap_def, MAP_EQ_ID, UNCURRY, FORALL_PROD]
  \\ res_tac);

(* not true because of alist shadowing
val nsMap_eq_id = Q.store_thm("nsMap_eq_id",
  `∀f x. nsMap f x = x ⇔ nsAll (λi x. f x = x) x`,
  recInduct nsMap_ind
  \\ rw[nsMap_def, nsAll_def, MAP_EQ_ID, UNCURRY]
  \\ rw[EQ_IMP_THM]
  >- (
    Cases_on`i` \\ fs[nsLookup_def, option_case_eq]
    \\ imp_res_tac ALOOKUP_MEM
    \\ res_tac \\ fs[]
    \\ metis_tac[] )
  >- (
    first_x_assum(qspec_then`Short x`mp_tac)
*)

val tenv_equiv_def = Define
  `tenv_equiv tenv1 tenv2 ⇔
     nsAll2 (λi v1 v2. v1 = v2) tenv1.t tenv2.t ∧
     nsAll2 (λi v1 v2. v1 = v2) tenv1.c tenv2.c ∧
     nsAll2 (λi v1 v2. v1 = v2) tenv1.v tenv2.v`;

val check_type_names_tenv_equiv = Q.store_thm("check_type_names_tenv_equiv",
  `∀t1 t t2.
   nsAll2 (λi v1 v2. v1 = v2) t1 t2 ∧
   check_type_names t1 t ⇒
   check_type_names t2 t`,
  recInduct check_type_names_ind
  \\ rw[check_type_names_def]
  \\ fs[EVERY_MEM, option_case_NONE_F]
  \\ imp_res_tac nsAll2_nsLookup1 \\ fs[]);

val lookup_var_tenv_equiv = Q.store_thm("lookup_var_tenv_equiv",
  `tenv_equiv tenv1 tenv2 ⇒ lookup_var n bvs tenv1 = lookup_var n bvs tenv2`,
  rw[tenv_equiv_def, lookup_var_def, lookup_varE_def]
  \\ every_case_tac \\ fs[]
  \\ (fn g as (asl,w) => Cases_on[ANTIQUOTE(lhs w)] g)
  \\ imp_res_tac nsAll2_nsLookup_none
  \\ imp_res_tac nsAll2_nsLookup1
  \\ fs[]);

val type_name_subst_tenv_equiv = Q.store_thm("type_name_subst_tenv_equiv",
  `∀t1 t t2.
    nsAll2 (λi v1 v2. v1 = v2) t1 t2 ⇒
    type_name_subst t1 t = type_name_subst t2 t`,
  recInduct type_name_subst_ind
  \\ rw[type_name_subst_def, MAP_EQ_f]
  \\ CASE_TAC
  \\ imp_res_tac nsAll2_nsLookup_none \\ fs[MAP_EQ_f]
  \\ imp_res_tac nsAll2_nsLookup1 \\ fs[]
  \\ CASE_TAC
  \\ AP_THM_TAC
  \\ ntac 4 AP_TERM_TAC
  \\ rw[MAP_EQ_f]);

val type_p_tenv_equiv = Q.store_thm("type_p_tenv_equiv",
  `(∀tvs tenv1 p t bindings.
     type_p tvs tenv1 p t bindings ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_p tvs tenv2 p t bindings) ∧
   (∀tvs tenv1 ps ts bindings.
     type_ps tvs tenv1 ps ts bindings ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_ps tvs tenv2 ps ts bindings)`,
  ho_match_mp_tac type_p_ind
  \\ rw[]
  \\ rw[Once type_p_cases]
  \\ first_x_assum drule \\ rw[]
  \\ TRY(first_x_assum drule \\ rw[])
  \\ fs[tenv_equiv_def]
  \\ imp_res_tac nsAll2_nsLookup1 \\ fs[] \\ rw[]
  \\ imp_res_tac type_name_subst_tenv_equiv
  \\ imp_res_tac check_type_names_tenv_equiv
  \\ fs[]
  \\ metis_tac[]);

val type_e_tenv_equiv = Q.store_thm("type_e_tenv_equiv",
  `(∀tenv1 bvs e t.
     type_e tenv1 bvs e t ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_e tenv2 bvs e t) ∧
   (∀tenv1 bvs es ts.
     type_es tenv1 bvs es ts ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_es tenv2 bvs es ts) ∧
   (∀tenv1 bvs funs ts.
     type_funs tenv1 bvs funs ts ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_funs tenv2 bvs funs ts)`,
  ho_match_mp_tac type_e_ind
  \\ rw[]
  \\ rw[Once type_e_cases]
  \\ TRY(first_x_assum drule \\ rw[])
  \\ fs[RES_FORALL, FORALL_PROD] \\ rw[]
  \\ res_tac
  \\ imp_res_tac type_p_tenv_equiv
  \\ imp_res_tac lookup_var_tenv_equiv
  \\ fs[tenv_equiv_def]
  \\ imp_res_tac nsAll2_nsLookup1 \\ fs[] \\ rw[]
  \\ metis_tac[type_p_tenv_equiv, tenv_equiv_def,
               type_name_subst_tenv_equiv, check_type_names_tenv_equiv]);

(* -- *)

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

val ts_tid_rename_ind = theorem"ts_tid_rename_ind";

val remap_tenv_def = Define`
  remap_tenv f tenv =
  <|
    t := nsMap (λ(ls,t). (ls, ts_tid_rename f t)) tenv.t;
    c := nsMap (λ(ls,ts,tid). (ls, MAP (ts_tid_rename f) ts, f tid)) tenv.c;
    v := nsMap (λ(n,t). (n,ts_tid_rename f t)) tenv.v
   |>`

(* All type ids in a type belonging to a set *)
val set_tids_def = tDefine "set_tids"`
  (set_tids (Tapp ts tn) = tn INSERT (BIGUNION (set (MAP set_tids ts)))) ∧
  (set_tids _ = {})`
  (WF_REL_TAC `measure t_size` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac)

val set_tids_ts_tid_rename = Q.store_thm("set_tids_ts_tid_rename",
  `∀f t. set_tids (ts_tid_rename f t) = IMAGE f (set_tids t)`,
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, set_tids_def]
  \\ rw[Once EXTENSION, MEM_MAP, PULL_EXISTS]
  \\ metis_tac[IN_IMAGE]);

val set_tids_subset_def = Define`
  set_tids_subset tids t <=> set_tids t ⊆ tids`

(* all the tids used in a tenv *)
val set_tids_tenv_def = Define`
  set_tids_tenv tids tenv ⇔
  nsAll (λi (ls,t). set_tids_subset tids t) tenv.t ∧
  nsAll (λi (ls,ts,tid). EVERY (λt. set_tids_subset tids t) ts ∧ tid ∈ tids) tenv.c ∧
  nsAll (λi (n,t). set_tids_subset tids t) tenv.v`

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

val set_tids_subset_type_subst = Q.prove(`
  ∀s t tids.
  FEVERY (set_tids_subset tids o SND) s ∧
  set_tids_subset tids t ⇒
  set_tids_subset tids (type_subst s t)`,
  ho_match_mp_tac type_subst_ind>>
  rw[type_subst_def,set_tids_def]
  >- (
    TOP_CASE_TAC>>
    fs[set_tids_def]>>
    drule (GEN_ALL FEVERY_FLOOKUP)>>fs[]>>
    metis_tac[])
  >- (
    fs[set_tids_subset_def,set_tids_def]>>
    fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>rw[]>>
    last_x_assum drule>>
    disch_then drule>>
    disch_then match_mp_tac>>
    metis_tac[]));

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

val set_tids_subset_type_name_subst = Q.prove(`
  ∀tenvt t tids.
  prim_tids T tids ∧
  nsAll (λi (ls,t). set_tids_subset tids t) tenvt ==>
  set_tids_subset tids (type_name_subst tenvt t)`,
  ho_match_mp_tac type_name_subst_ind>>
  rw[set_tids_def,type_name_subst_def,set_tids_subset_def]
  >- fs[prim_tids_def,prim_type_nums_def]
  >- (
     fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>
     metis_tac[])
  >- fs[prim_tids_def,prim_type_nums_def]
  >>
    TOP_CASE_TAC>>fs[set_tids_def,EVERY_MAP,EVERY_MEM]
    >- (
      CONJ_TAC>- fs[prim_tids_def,prim_type_nums_def]>>
      fs[SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>
      metis_tac[])
    >>
      TOP_CASE_TAC>>fs[GSYM set_tids_subset_def]>>
      match_mp_tac set_tids_subset_type_subst>>
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

val INJ_extend_bij = Q.store_thm("INJ_extend_bij",`
  DISJOINT tids ids ∧
  INJ f tids (count n) ∧
  INJ g ids (count (CARD ids)) ⇒
  INJ (extend_bij f g ids n) (tids ∪ ids) (count (n + CARD ids))`,
  rewrite_tac[INJ_DEF,extend_bij_def,IN_DISJOINT,IN_COUNT,IN_UNION]
  \\ rpt strip_tac
  \\ res_tac
  \\ rpt (pop_assum mp_tac)
  \\ rewrite_tac[]
  \\ rpt IF_CASES_TAC
  \\ rpt strip_tac
  \\ full_simp_tac bool_ss []
  \\ fs[]);

val BIJ_extend_bij = Q.store_thm("BIJ_extend_bij",`
  DISJOINT tids ids ∧
  BIJ f tids (count n) ∧
  BIJ g ids (count (CARD ids)) ⇒
  BIJ (extend_bij f g ids n) (tids ∪ ids) (count (n + CARD ids))`,
  rewrite_tac[INJ_DEF,SURJ_DEF,BIJ_DEF,extend_bij_def,IN_DISJOINT]
  \\ strip_tac
  \\ rewrite_tac[IN_UNION, count_add, IN_IMAGE]
  \\ reverse conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ rpt (first_x_assum drule)>>fs[]);

val set_tids_ind = fetch "-" "set_tids_ind";

val set_tids_subset_mono = Q.store_thm("set_tids_subset_mono",
  `∀tids t tids'.
  set_tids_subset tids t ∧ tids ⊆ tids' ⇒
  set_tids_subset tids' t`,
  rw[set_tids_subset_def, SUBSET_DEF]);

val set_tids_tenv_mono = Q.prove(`
  set_tids_tenv tids tenv ∧ tids ⊆ tids' ⇒
  set_tids_tenv tids' tenv`,
  fs[set_tids_tenv_def]>>rw[]>>
  irule nsAll_mono
  \\ goal_assum(first_assum o mp_then Any mp_tac)
  \\ rw[]
  \\ pairarg_tac \\ fs[EVERY_MEM,SUBSET_DEF]
  \\ metis_tac[set_tids_subset_mono,SUBSET_DEF]);

val check_freevars_ts_tid_rename = Q.prove(`
  ∀ts ls t.
  check_freevars ts ls (ts_tid_rename f t) ⇔
  check_freevars ts ls t`,
  ho_match_mp_tac check_freevars_ind>>
  fs[ts_tid_rename_def,check_freevars_def,EVERY_MAP,EVERY_MEM]);

val sing_renum_def = Define`
  sing_renum m n = λx. if x = m then n else x`

(* duplicated in envRelScript *)
val t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`;

val sing_renum_NOT_tscheme_inst = Q.prove(`
  ∀t.
  m ∈ set_tids t ∧
  m ≠ n ⇒
  ts_tid_rename (sing_renum m n) t ≠ t ∧
  ∀tvs tvs'.
  ¬tscheme_inst (tvs,ts_tid_rename (sing_renum m n) t) (tvs',t) ∧
  ¬tscheme_inst (tvs',t) (tvs,ts_tid_rename (sing_renum m n) t)`,
  ho_match_mp_tac t_ind>>rw[]>>
  fs[set_tids_def,ts_tid_rename_def,sing_renum_def]>>
  rw[]>>
  simp[tscheme_inst_def,deBruijn_subst_def]>>
  fs[EVERY_MEM,MEM_MAP]
  >-
    (CCONTR_TAC>> fs[MAP_EQ_ID]>>
    metis_tac[])
  >- (
    rw[]
    \\ CCONTR_TAC \\ fs[MAP_EQ_f, EVERY_MEM]
    \\ last_x_assum mp_tac \\ rw[]
    \\ asm_exists_tac \\ simp[]
    \\ fsrw_tac[DNF_ss][tscheme_inst_def]
    \\ disj2_tac \\ disj1_tac
    \\ fs[check_freevars_def,EVERY_MEM]
    \\ metis_tac[])
  >> (
    rw[]
    \\ CCONTR_TAC \\ fs[MAP_EQ_f, EVERY_MEM]
    \\ last_x_assum mp_tac \\ rw[]
    \\ asm_exists_tac \\ simp[]
    \\ fsrw_tac[DNF_ss][tscheme_inst_def]
    \\ disj2_tac \\ disj2_tac
    \\ fs[check_freevars_def,EVERY_MEM,MEM_MAP,PULL_EXISTS,MAP_MAP_o,MAP_EQ_ID]
    \\ metis_tac[]));

val sing_renum_NOTIN_ID = Q.store_thm("sing_renum_NOTIN_ID",
  `∀t.
  m ∉ set_tids t ⇒
  ts_tid_rename (sing_renum m n) t = t`,
  ho_match_mp_tac t_ind>>rw[]>>
  fs[ts_tid_rename_def,sing_renum_def,set_tids_def]>>
  fs[EVERY_MEM,MAP_EQ_ID,MEM_MAP]>>
  metis_tac[]);

(* TODO: this is only true up to equivalence on tenvs *)
val sing_renum_NOTIN_tenv_ID = Q.store_thm("sing_renum_NOTIN_tenv_ID",
  `set_tids_tenv tids tenv ∧
  m ∉ tids ⇒
  tenv_equiv (remap_tenv (sing_renum m n) tenv) (tenv)`,
  rw[remap_tenv_def,type_env_component_equality]>>
  fs[set_tids_tenv_def,set_tids_subset_def,tenv_equiv_def]>>
  rw[nsAll2_def, nsSub_def, nsLookup_nsMap, nsLookupMod_nsMap]
  \\ imp_res_tac nsLookup_nsAll \\ fs[]
  \\ rpt(pairarg_tac \\ fs[])
  \\ rw[MAP_EQ_ID] \\ fs[EVERY_MEM]
  \\ TRY (
    match_mp_tac sing_renum_NOTIN_ID ORELSE match_mp_tac (GSYM sing_renum_NOTIN_ID)
    \\ CCONTR_TAC \\ fs[SUBSET_DEF]
    \\ metis_tac[])
  \\ rw[sing_renum_def] \\ fs[]);

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

val type_op_ts_tid_rename = Q.store_thm("type_op_ts_tid_rename",`
  good_remap f ⇒
  ∀op ts t.
  type_op op ts t ⇒
  type_op op (MAP (ts_tid_rename f) ts) (ts_tid_rename f t)`,
  rw[]>>
  fs[typeSysPropsTheory.type_op_cases,ts_tid_rename_def]>>
  fs[good_remap_def,prim_type_nums_def]);

val remap_tenvE_def = Define`
  (remap_tenvE f Empty = Empty) ∧
  (remap_tenvE f (Bind_tvar n e) = Bind_tvar n (remap_tenvE f e)) ∧
  (remap_tenvE f (Bind_name s n t e) = Bind_name s n (ts_tid_rename f t) (remap_tenvE f e))`

val num_tvs_remap_tenvE = Q.prove(`
  ∀tenvE. num_tvs (remap_tenvE f tenvE) = num_tvs tenvE`,
  Induct>>fs[remap_tenvE_def]);

val remap_tenvE_bind_var_list = Q.prove(`
  ∀n env tenvE.
  remap_tenvE f (bind_var_list n env tenvE) =
  bind_var_list n (MAP (λ(n,t). (n, ts_tid_rename f t)) env) (remap_tenvE f tenvE)`,
  ho_match_mp_tac bind_var_list_ind>>
  fs[bind_var_list_def,remap_tenvE_def]>>
  rw[]);

val remap_tenvE_bind_tvar = Q.store_thm("remap_tenvE_bind_tvar",
  `remap_tenvE f (bind_tvar tvs e) = bind_tvar tvs (remap_tenvE f e)`,
  rw[bind_tvar_def, remap_tenvE_def]);

val deBruijn_inc_ts_tid_rename = Q.prove(`
  ∀skip n t.
  ts_tid_rename f (deBruijn_inc skip n t) =
  deBruijn_inc skip n (ts_tid_rename f t)`,
  ho_match_mp_tac deBruijn_inc_ind>>
  rw[deBruijn_inc_def,ts_tid_rename_def,MAP_MAP_o]>>
  fs[MAP_EQ_f]);

val lookup_varE_remap_tenvE = Q.prove(`
  ∀n tenvE.
  lookup_varE n (remap_tenvE f tenvE)
  = lift (λid,t. (id, ts_tid_rename f t)) (lookup_varE n tenvE)`,
  fs[lookup_varE_def]>>Cases>>fs[]>>
  qabbrev_tac`n=0n`>>
  pop_assum kall_tac>>qid_spec_tac`n`>>
  Induct_on`tenvE`>>fs[remap_tenvE_def,tveLookup_def]>>rw[]>>
  fs[deBruijn_inc_ts_tid_rename]);

val ts_tid_rename_deBruijn_subst = Q.prove(`
  ∀n targs t.
  ts_tid_rename f (deBruijn_subst n targs t) =
  deBruijn_subst n (MAP (ts_tid_rename f) targs) (ts_tid_rename f t)`,
  ho_match_mp_tac deBruijn_subst_ind>>rw[]>>
  rw[ts_tid_rename_def,deBruijn_subst_def]>>
  fs[EL_MAP,MAP_MAP_o]>>
  fs[MAP_EQ_f]);

val type_e_ts_tid_rename = Q.store_thm("type_e_ts_tid_rename",`
  good_remap f ⇒
  (∀tenv tenvE e t.
    type_e tenv tenvE e t ⇒
    type_e (remap_tenv f tenv) (remap_tenvE f tenvE) e (ts_tid_rename f t)) ∧
  (∀tenv tenvE es ts.
    type_es tenv tenvE es ts ⇒
    type_es (remap_tenv f tenv) (remap_tenvE f tenvE) es (MAP (ts_tid_rename f) ts)) ∧
  (∀tenv tenvE funs env.
    type_funs tenv tenvE funs env ⇒
    type_funs (remap_tenv f tenv) (remap_tenvE f tenvE) funs (MAP (λ(n,t). (n, ts_tid_rename f t)) env))`,
  strip_tac>>
  ho_match_mp_tac type_e_strongind>>
  rw[]>>
  simp[Once type_e_cases,ts_tid_rename_def]>>
  fs[check_freevars_ts_tid_rename,num_tvs_remap_tenvE]>>
  TRY(
    fs[good_remap_def,prim_type_nums_def]>>
    fs[ts_tid_rename_def]>>
    rfs[]>>
    NO_TAC)
  >- ( (* pes *)
    fs[remap_tenvE_bind_var_list]
    \\ fs[RES_FORALL,FORALL_PROD]
    \\ rw[]
    \\ first_x_assum drule
    \\ strip_tac \\ rw[]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ imp_res_tac(CONJUNCT1(UNDISCH type_p_ts_tid_rename))
    \\ fs[ts_tid_rename_def]
    \\ fs[good_remap_def,prim_type_nums_def]
    \\ rfs[])
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
    fs[lookup_var_def,remap_tenv_def]>>
    pop_assum mp_tac>>
    TOP_CASE_TAC>>rw[nsLookup_nsMap]>>
    fs[lookup_varE_remap_tenvE]>>
    simp[ts_tid_rename_deBruijn_subst]>>
    qexists_tac`MAP (ts_tid_rename f) targs`>>fs[EVERY_MAP,EVERY_MEM]>>
    metis_tac[check_freevars_ts_tid_rename])
  >-
    fs[remap_tenvE_def,good_remap_def,prim_type_nums_def]
  >-
    metis_tac[type_op_ts_tid_rename]
  >-
    (HINT_EXISTS_TAC>>fs[]>>
     fs[remap_tenvE_bind_var_list, FORALL_PROD, RES_FORALL]
     \\ rw[]
     \\ first_x_assum drule \\ strip_tac \\ rw[]
     \\ imp_res_tac type_p_ts_tid_rename
     \\ asm_exists_tac \\ rw[])
  >- (
    fs[opt_bind_name_def]>>TOP_CASE_TAC>>fs[remap_tenvE_def]>>
    metis_tac[])
  >- (
    fs[remap_tenvE_bind_var_list]>>
    metis_tac[])
  >- (
    fs[remap_tenv_def,ts_tid_rename_type_name_subst]>>
    fs[GSYM check_type_names_ts_tid_rename]>>
    metis_tac[ts_tid_rename_type_name_subst])
  >>
    fs[check_freevars_def,check_freevars_ts_tid_rename,remap_tenvE_def,ALOOKUP_MAP]>>
    fs[good_remap_def,prim_type_nums_def]);

val good_remap_LINV = Q.store_thm("good_remap_LINV",
  `good_remap f ∧ prim_tids T s ∧ INJ f s t ⇒ good_remap (LINV f s o f)`,
  rw[good_remap_def, prim_tids_def, MAP_EQ_ID, EVERY_MEM]
  \\ res_tac
  \\ imp_res_tac LINV_DEF);

val ts_tid_rename_LINV = Q.store_thm("ts_tid_rename_LINV",
  `∀f x. INJ f s t ∧ set_tids_subset s x ⇒ ts_tid_rename (LINV f s) (ts_tid_rename f x) = x`,
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, MAP_MAP_o, set_tids_subset_def, SUBSET_DEF, MAP_EQ_ID]
  \\ fs[set_tids_def, PULL_EXISTS, MEM_MAP]
  >- (fs[EVERY_MEM] \\ metis_tac[])
  \\ imp_res_tac LINV_DEF
  \\ metis_tac[]);

val remap_tenv_LINV = Q.store_thm("remap_tenv_LINV",
  `INJ f s t ∧ set_tids_tenv s tenv ⇒
   tenv_equiv (remap_tenv (LINV f s) (remap_tenv f tenv)) tenv`,
  rw[remap_tenv_def, tenv_equiv_def, nsMap_compose, nsAll2_def,
     nsSub_def, nsLookup_nsMap, nsLookupMod_nsMap]
  \\ fs[UNCURRY, set_tids_tenv_def]
  \\ imp_res_tac nsLookup_nsAll \\ fs[UNCURRY]
  \\ fs[MAP_MAP_o, o_DEF]
  \\ imp_res_tac ts_tid_rename_LINV \\ fs[]
  \\ imp_res_tac LINV_DEF \\ fs[EVERY_MEM]
  \\ simp[PAIR_FST_SND_EQ, MAP_EQ_ID]);

val LINVI_def = Define`
  LINVI f s y = case LINV_OPT f s y of SOME x => x | NONE => f y`;

val good_remap_LINVI = Q.store_thm("good_remap_LINVI",
  `good_remap f ∧ prim_tids T s ∧ INJ f s t ⇒ good_remap (LINVI f s)`,
  rw[good_remap_def, prim_tids_def, LINVI_def, MAP_EQ_ID]
  \\ drule INJ_LINV_OPT
  \\ CASE_TAC \\ rw[]
  \\ fs[EVERY_MEM]
  \\ metis_tac[INJ_DEF]);

val INJ_LINVI = Q.store_thm("INJ_LINVI",
  `INJ f s t ∧ x ∈ s ⇒ LINVI f s (f x) = x`,
  rw[LINVI_def]
  \\ CASE_TAC
  \\ imp_res_tac INJ_LINV_OPT \\ rw[]
  \\ metis_tac[INJ_DEF, NOT_NONE_SOME]);

val LINVI_RINV = Q.store_thm("LINVI_RINV",
  `INJ f s t ∧ (∃x. x ∈ s ∧ f x = y) ⇒
   f (LINVI f s y) = y`,
  rw[LINVI_def]
  \\ drule INJ_LINV_OPT
  \\ disch_then(qspec_then`f x`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ CASE_TAC \\ rw[]
  \\ metis_tac[INJ_DEF]);

val ts_tid_rename_LINVI = Q.store_thm("ts_tid_rename_LINVI",
  `∀f x. INJ f s t ∧ set_tids_subset s x ⇒ ts_tid_rename (LINVI f s) (ts_tid_rename f x) = x`,
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, MAP_MAP_o, set_tids_def, set_tids_subset_def, MAP_EQ_ID]
  \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  >- metis_tac[]
  \\ rw[LINVI_def]
  \\ imp_res_tac INJ_LINV_OPT
  \\ CASE_TAC \\ fs[]
  \\ metis_tac[INJ_DEF]);

val remap_tenv_LINVI = Q.store_thm("remap_tenv_LINVI",
  `INJ f s t ∧ set_tids_tenv s tenv ⇒
   tenv_equiv (remap_tenv (LINVI f s) (remap_tenv f tenv)) tenv`,
  rw[remap_tenv_def, tenv_equiv_def, nsMap_compose, nsAll2_def,
     nsSub_def, nsLookup_nsMap, nsLookupMod_nsMap]
  \\ fs[UNCURRY, set_tids_tenv_def]
  \\ imp_res_tac nsLookup_nsAll \\ fs[UNCURRY]
  \\ fs[MAP_MAP_o, o_DEF]
  \\ imp_res_tac ts_tid_rename_LINVI \\ fs[]
  \\ imp_res_tac INJ_LINVI \\ fs[EVERY_MEM]
  \\ simp[PAIR_FST_SND_EQ, MAP_EQ_ID]);

val ts_tid_rename_compose = Q.store_thm("ts_tid_rename_compose",
  `∀g t f. ts_tid_rename f (ts_tid_rename g t) = ts_tid_rename (f o g) t`,
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, MAP_MAP_o, o_DEF, MAP_EQ_f]);

val remap_tenv_compose = Q.store_thm("remap_tenv_compose",
  `remap_tenv f (remap_tenv g tenv) = remap_tenv (f o g) tenv`,
  srw_tac[ETA_ss]
    [remap_tenv_def, nsMap_compose, ts_tid_rename_compose,
     o_DEF, UNCURRY, LAMBDA_PROD, MAP_MAP_o]);

val ts_tid_rename_eq_id = Q.store_thm("ts_tid_rename_eq_id",
  `∀f t. (ts_tid_rename f t = t ⇔ ∀x. x ∈ set_tids t ⇒ f x = x)`,
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, set_tids_def, MAP_EQ_ID, MEM_MAP]
  \\ rw[EQ_IMP_THM] \\ rw[]
  \\ metis_tac[]);

(* probably not be true because of shadows...
val remap_tenv_LINVI = Q.store_thm("remap_tenv_LINVI",
  `INJ f s t ∧ set_tids_tenv s tenv ⇒
   remap_tenv (LINVI f s) (remap_tenv f tenv) = tenv`,
  rw[remap_tenv_def, type_env_component_equality,
     nsMap_compose, o_DEF, UNCURRY, MAP_MAP_o,
     set_tids_tenv_def]
*)

val type_p_ts_tid_rename_sing_renum = Q.prove(`
  m ∉ tids ∧ prim_tids T tids ∧
  type_p tvs tenv p t bindings ∧
  set_tids_tenv tids tenv
  ⇒
  type_p tvs tenv p (ts_tid_rename (sing_renum m n) t)
  (MAP (λ(nn,t). (nn,ts_tid_rename (sing_renum m n) t)) bindings)`,
  rw[]>>
  `good_remap (sing_renum m n)` by
    (fs[good_remap_def,sing_renum_def]>>
    fs[prim_tids_def]>>
    rw[] >> fs[] >>
    simp[MAP_EQ_ID]>>
    fs[prim_type_nums_def]>>
    rw[]>>fs[])>>
  drule type_p_ts_tid_rename>>
  strip_tac>> first_x_assum drule>>
  drule sing_renum_NOTIN_tenv_ID>>
  simp[]>>rw[]>>
  metis_tac[type_p_tenv_equiv]);

val type_e_ts_tid_rename_sing_renum = Q.prove(`
  m ∉ tids ∧ prim_tids T tids ∧
  type_e tenv tenvE e t ∧
  set_tids_tenv tids tenv
  ⇒
  type_e tenv (remap_tenvE (sing_renum m n) tenvE) e (ts_tid_rename (sing_renum m n) t)`,
  rw[]>>
  `good_remap (sing_renum m n)` by
    (fs[good_remap_def,sing_renum_def]>>
    fs[prim_tids_def]>>
    rw[] >> fs[] >>
    simp[MAP_EQ_ID]>>
    fs[prim_type_nums_def]>>
    rw[]>>fs[])>>
  drule type_e_ts_tid_rename>>
  strip_tac>> first_x_assum drule>>
  drule sing_renum_NOTIN_tenv_ID>>
  simp[]>>rw[]>>
  metis_tac[type_e_tenv_equiv]);

val type_pe_bindings_tids = Q.prove(`
  prim_tids T tids ∧
  set_tids_tenv tids tenv ∧
  type_p tvs tenv p t bindings ∧
  type_e tenv (bind_tvar tvs Empty) e t ∧
  (∀tvs' bindings' t'.
      type_p tvs' tenv p t' bindings' ∧
      type_e tenv (bind_tvar tvs' Empty) e t' ⇒
      LIST_REL tscheme_inst
        (MAP SND (MAP (λ(n,t). (n,tvs',t)) bindings'))
        (MAP SND (MAP (λ(n,t). (n,tvs,t)) bindings))) ⇒
  ∀p_1 p_2. MEM (p_1,p_2) bindings ⇒ set_tids_subset tids p_2`,
  CCONTR_TAC>>fs[set_tids_subset_def,SUBSET_DEF]>>
  drule (GEN_ALL type_p_ts_tid_rename_sing_renum)>>
  rpt (disch_then drule)>>
  disch_then(qspec_then`x+1` mp_tac)>>
  strip_tac>>
  first_x_assum drule>>
  drule (GEN_ALL type_e_ts_tid_rename_sing_renum)>>
  rpt(disch_then drule)>>
  disch_then (qspec_then `x+1` mp_tac)>>
  qmatch_goalsub_abbrev_tac`type_e _ tenvEE _ _`>>
  `tenvEE = (bind_tvar tvs Empty)` by
    rw[Abbr`tenvEE`,bind_tvar_def,remap_tenvE_def]>>
  pop_assum SUBST_ALL_TAC>>simp[]>>
  rw[LIST_REL_EL_EQN]>>
  fs[MEM_EL]>>
  asm_exists_tac>>
  fs[EL_MAP]>>
  qpat_x_assum`(_,_)=_` sym_sub_tac>>fs[]>>
  `x ≠ x+1` by fs[]>>
  metis_tac[sing_renum_NOT_tscheme_inst]);

val build_ctor_tenv_type_identities = Q.store_thm("build_ctor_tenv_type_identities",`
  ∀tenvt xs type_identities tids.
  prim_tids T tids ∧
  nsAll (λi (ls,t). set_tids_subset (tids ∪ set type_identities) t) tenvt ∧
  LENGTH xs = LENGTH type_identities ⇒
  nsAll ((λi (ls,ts,tid).
    EVERY (λt. set_tids_subset (tids ∪ set type_identities) t) ts ∧
    (tid ∈ tids ∨ MEM tid type_identities)))
    (build_ctor_tenv tenvt xs type_identities)`,
  ho_match_mp_tac build_ctor_tenv_ind>>rw[build_ctor_tenv_def]>>
  match_mp_tac nsAll_nsAppend>>fs[]>>
  CONJ_TAC>- (
    first_x_assum(qspec_then`id INSERT tids` mp_tac)>>
    `(id INSERT tids) ∪ set type_identities = tids ∪ (id INSERT set type_identities)` by
      (rw[EXTENSION]>>
      metis_tac[])>>
    impl_tac>-
      fs[prim_tids_def,prim_type_nums_def]>>
    fs[METIS_PROVE [] ``(P ∨ Q) ∨ R ⇔ Q ∨ P ∨ R``])>>
  match_mp_tac nsAll_alist_to_ns>>
  fs[EVERY_REVERSE,EVERY_MAP,EVERY_MEM,LAMBDA_PROD,FORALL_PROD,MEM_MAP,PULL_EXISTS,PULL_FORALL]>>
  rw[]>>
  match_mp_tac set_tids_subset_type_name_subst>>
  fs[prim_tids_def,prim_type_nums_def]);

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
  BIJ f tids (count n) ∧
  (* tids contains at least the primitive type numbers and f is identity on them *)
  prim_tids T tids ∧ good_remap f ⇒
  ∃g.
    (* This is actually a property of the type system *)
    set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧ FINITE ids ∧
    (* This forces g to extend the injection on f *)
    BIJ g ids (count (CARD ids)) ∧
    type_d_canon n (remap_tenv f tenv) d (CARD ids)
      (remap_tenv (extend_bij f g ids n) tenv')) ∧
(∀extra_checks tenv ds ids tenv'.
  type_ds extra_checks tenv ds ids tenv' ==>
  ∀tids f n.
  extra_checks = T ∧
  DISJOINT ids tids ∧
  set_tids_tenv tids tenv ∧
  BIJ f tids (count n) ∧
  prim_tids T tids ∧ good_remap f ⇒
  ∃g.
    set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧ FINITE ids ∧
    BIJ g ids (count (CARD ids)) ∧
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
      CCONTR_TAC>>fs[set_tids_subset_def,SUBSET_DEF]>>
      drule (GEN_ALL type_p_ts_tid_rename_sing_renum)>>
      rpt (disch_then drule)>>
      disch_then(qspec_then`x+1` mp_tac)>>
      impl_tac>-
        fs[set_tids_tenv_def,set_tids_subset_def,SUBSET_DEF]>>
      strip_tac>>
      first_x_assum drule>>
      drule (GEN_ALL type_e_ts_tid_rename_sing_renum)>>
      rpt(disch_then drule)>>
      disch_then (qspec_then `x+1` mp_tac)>>
      impl_tac>-
        fs[set_tids_tenv_def,set_tids_subset_def,SUBSET_DEF]>>
      qmatch_goalsub_abbrev_tac`type_e _ tenvEE _ _`>>
      `tenvEE = (bind_tvar tvs Empty)` by
        rw[Abbr`tenvEE`,bind_tvar_def,remap_tenvE_def]>>
      pop_assum SUBST_ALL_TAC>>simp[]>>
      rw[LIST_REL_EL_EQN]>>
      fs[MEM_EL]>>
      asm_exists_tac>>
      fs[EL_MAP]>>
      qpat_x_assum`(_,_)=_` sym_sub_tac>>fs[]>>
      `x ≠ x+1` by fs[]>>
      metis_tac[sing_renum_NOT_tscheme_inst])>>
    simp[prim_tids_def, Once type_d_canon_cases]>>
    simp[Once remap_tenv_def,tenv_add_tvs_def]>>
    drule type_p_ts_tid_rename>>rw[]>>
    first_x_assum drule>>
    qmatch_goalsub_abbrev_tac`type_p tvs _ _ t2 bindings2`>>
    strip_tac>>
    qexists_tac`tvs`>>qexists_tac`t2`>>qexists_tac`bindings2`>>
    unabbrev_all_tac>>fs[]>>
    CONJ_TAC>-
      simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
    CONJ_TAC>- (
      drule type_e_ts_tid_rename>> rw[]>>
      first_x_assum drule>>
      rw[bind_tvar_def,remap_tenvE_def])>>
    rw[]>>
    imp_res_tac remap_tenv_LINVI >>
    pop_assum(qspec_then`tenv`mp_tac) >>
    impl_tac >- simp[set_tids_tenv_def] >>
    strip_tac >>
    fs[remap_tenv_compose] >>
    imp_res_tac good_remap_LINVI >>
    drule (GEN_ALL type_p_ts_tid_rename) >>
    disch_then (qspecl_then[`tvs''`]mp_tac o CONJUNCT1)
    \\ disch_then drule
    \\ fs[remap_tenv_compose]
    \\ strip_tac
    \\ drule (CONJUNCT1 type_p_tenv_equiv)
    \\ disch_then drule
    \\ strip_tac
    \\ first_x_assum drule
    \\ drule (GEN_ALL type_e_ts_tid_rename)
    \\ disch_then (drule o CONJUNCT1)
    \\ fs[remap_tenv_compose, remap_tenvE_bind_tvar]
    \\ simp[Once remap_tenvE_def]
    \\ strip_tac
    \\ impl_tac >- metis_tac[type_e_tenv_equiv]
    \\ simp[MAP_MAP_o, o_DEF, UNCURRY]
    \\ simp[EVERY2_MAP]
    \\ rw[LIST_REL_EL_EQN] \\ rfs[]
    \\ first_x_assum drule
    \\ simp[tscheme_inst_def]
    \\ simp[GSYM deBruijn_inc_ts_tid_rename, check_freevars_ts_tid_rename]
    \\ strip_tac
    \\ qexists_tac`MAP (ts_tid_rename f) subst`
    \\ srw_tac[ETA_ss][EVERY_MAP, check_freevars_ts_tid_rename]
    \\ simp[GSYM ts_tid_rename_deBruijn_subst, ts_tid_rename_compose]
    \\ rw[ts_tid_rename_eq_id]
    \\ match_mp_tac (GEN_ALL LINVI_RINV)
    \\ asm_exists_tac \\ simp[]

    \\ CCONTR_TAC \\ fs[]

    (* construct the inverse back into the original type system *)
    \\ cheat)
  >- ((* Dlet mono *)
    fs[set_tids_tenv_def,tenv_add_tvs_def]>>
    qexists_tac`f`>>simp[]>>
    CONJ_TAC >- (
      match_mp_tac nsAll_alist_to_ns>>
      simp[EVERY_MAP,EVERY_MEM,FORALL_PROD]>>
      CCONTR_TAC>>fs[set_tids_subset_def,SUBSET_DEF]>>
      drule (GEN_ALL type_p_ts_tid_rename_sing_renum)>>
      rpt (disch_then drule)>>
      disch_then(qspec_then`x+1` mp_tac)>>
      impl_tac>-
        fs[set_tids_tenv_def,set_tids_subset_def,SUBSET_DEF]>>
      strip_tac>>
      fs[type_pe_determ_def]>>
      first_x_assum drule>>
      drule (GEN_ALL type_e_ts_tid_rename_sing_renum)>>
      rpt(disch_then drule)>>
      disch_then (qspec_then `x+1` mp_tac)>>
      impl_tac>-
        fs[set_tids_tenv_def,set_tids_subset_def,SUBSET_DEF]>>
      ntac 2 strip_tac>>
      rfs[remap_tenvE_def]>>
      qpat_x_assum`type_p _ _ _ _ _` mp_tac>>
      qpat_x_assum`type_e _ _ _ _` mp_tac>>
      pop_assum drule>>
      rpt(strip_tac)>>
      rfs[MAP_EQ_ID]>>
      first_x_assum drule>>
      strip_tac>>fs[]>>
      `x ≠ x+1` by fs[]>>
      metis_tac[sing_renum_NOT_tscheme_inst]
      (* TODO: this looks false.. *)
    )>>
    simp[prim_tids_def, Once type_d_canon_cases]>>
    simp[Once remap_tenv_def]>>
    qexists_tac`ts_tid_rename f t`>>
    qexists_tac`MAP (\n,t. (n,ts_tid_rename f t)) bindings`>>
    CONJ_TAC >-
      simp[tenv_add_tvs_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
    CONJ_TAC>- (
      fs[type_pe_determ_def]>>rw[]>>
      first_x_assum drule>>simp[]>>
      (* seems nasty
        f is injective, so one should be able to construct the necessary
        partial inverses? *)
      cheat)>>
    drule type_e_ts_tid_rename>>
    strip_tac>> first_x_assum drule>>
    simp[remap_tenvE_def]>>
    metis_tac[type_p_ts_tid_rename])
  >- ((* Dletrec *)
    cheat )
  >- ((* Dtype - important! try and finish this first *)
    simp[GSYM PULL_EXISTS]>>
    CONJ_TAC >- (
      rw[set_tids_tenv_def]
      >- (
        match_mp_tac nsAll_alist_to_ns>>
        simp[MAP2_MAP,EVERY_MAP,EVERY_MEM,MEM_MAP,EXISTS_PROD,MEM_ZIP,FORALL_PROD,PULL_EXISTS,set_tids_def,set_tids_subset_def]>>
        rw[MEM_EL]>- metis_tac[]>>
        simp[SUBSET_DEF,PULL_EXISTS,MEM_MAP,set_tids_def])
      >>
        match_mp_tac build_ctor_tenv_type_identities>>
        fs[]>>
        match_mp_tac nsAll_nsAppend>>
        CONJ_TAC>- (
          match_mp_tac nsAll_alist_to_ns>>
          fs[EVERY_MEM,MAP2_MAP,MEM_MAP,MEM_ZIP,PULL_EXISTS]>>
          rw[]>>
          rpt(pairarg_tac>>fs[])>>rw[]>>
          simp[set_tids_subset_def,set_tids_def,MAP_MAP_o,o_DEF,SUBSET_DEF,PULL_EXISTS,MEM_MAP]>>
          metis_tac[MEM_EL])>>
        fs[set_tids_tenv_def]>>
        (* monotonicty *)
        qpat_x_assum`nsAll _ tenv.t` mp_tac>>
        match_mp_tac nsAll_mono>>
        simp[FORALL_PROD]>>
        rw[]>> match_mp_tac set_tids_subset_mono>>
        asm_exists_tac>>fs[])>>
    CONJ_TAC>- (
      fs[prim_tids_def,DISJOINT_DEF,EVERY_MEM,EXTENSION]>>
      metis_tac[])>>
    simp[Once type_d_canon_cases]>>
    drule ALL_DISTINCT_CARD_LIST_TO_SET>>
    simp[]>>rw[]>>
    (* all of these look plausible
      witness for g is function mapping list element to its position in list
    *)
    qabbrev_tac`g = THE o (ALOOKUP (ZIP (type_identities, COUNT_LIST (LENGTH tdefs))))`>>
    qexists_tac`g`>>
    CONJ_TAC >-
      (* BIJ or INJ? *)
      cheat>>
    CONJ_TAC >- (
      rw[remap_tenv_def]>- cheat>>
      simp[MAP2_MAP,MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,EL_ZIP,LAMBDA_PROD]>>
      rw[]>>
      rpt(pairarg_tac>>fs[])>>rw[]>>
      simp[ts_tid_rename_def,MAP_EQ_ID,MEM_MAP,PULL_EXISTS]>>
      simp[extend_bij_def,EL_MEM,Abbr`g`]>>
      (* defining property of g *)
      cheat)>>
    (* Otherwise count n is not big enough to form *)
    CONJ_TAC>- (
      fs[BIJ_DEF,prim_tids_def,INJ_DEF,good_remap_def]>>
      metis_tac[])>>
    CONJ_TAC>- (
      fs[BIJ_DEF,prim_tids_def,INJ_DEF,good_remap_def]>>
      metis_tac[])>>
    CONJ_TAC >- cheat>>
    cheat)
  >- ( (* Dtabbrev - sanity check *)
    qexists_tac`f`>>
    simp[set_tids_tenv_def]>>
    CONJ_TAC >- (
      match_mp_tac set_tids_subset_type_name_subst>>
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
      >- (match_mp_tac set_tids_subset_type_name_subst>>fs[set_tids_tenv_def])>>
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
    match_mp_tac BIJ_extend_bij>>fs[DISJOINT_SYM])>>
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
    match_mp_tac BIJ_extend_bij>>
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
