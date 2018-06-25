open preamble miscTheory astTheory namespaceTheory typeSystemTheory;
open terminationTheory namespacePropsTheory

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
    n
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
  type_d_canon extra_checks tenv (Dtype locs tdefs)
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
        cheat) (* annoying ZIP*)
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
  set_tids_tenv s t ∧
  set_tids_tenv s' t' ==>
  set_tids_tenv (s' ∪ s) (extend_dec_tenv t' t)`,
  cheat);

val good_remap_extend_bij = Q.prove(`
  good_remap f ∧ prim_tids F ids ⇒
  good_remap (extend_bij f g ids n)`,
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]);

val remap_tenv_extend_dec_tenv = Q.prove(`
  remap_tenv f (extend_dec_tenv t t') =
  extend_dec_tenv (remap_tenv f t) (remap_tenv f t')`,
  fs[remap_tenv_def,extend_dec_tenv_def,nsMap_nsAppend]);

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
  extra_checks = T ∧
  set_tids_tenv tids tenv ∧
  (* f is a bijection on the tid set *)
  BIJ f tids (count n) ∧
  (* tids contains at least the primitive type numbers
    and f is identity on them *)
  prim_tids T tids ∧ good_remap f ⇒
  ∃g.
    (* This set up forces g to be an extension of f *)
    (* this is actually a property of the type system *)
    set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧
    BIJ g ids (count (CARD ids)) ∧
    type_d_canon n (remap_tenv f tenv) d (CARD ids)
      (remap_tenv (extend_bij f g ids n) tenv')) ∧
(∀extra_checks tenv ds ids tenv'.
  type_ds extra_checks tenv ds ids tenv' ==>
  ∀tids f n.
  extra_checks = T ∧
  set_tids_tenv tids tenv ∧
  BIJ f tids (count n) ∧
  prim_tids T tids ∧ good_remap f ⇒
  ∃g.
    (* This set up forces g to be an extension of f *)
    (* this is actually a property of the type system *)
    set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧
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
      (* this should be a property of bindings by type_p *)
      cheat)>>
    simp[prim_tids_def]>>
    cheat)
  >- ((* Dlet mono *)
    cheat )
  >- ((* Dletrec *)
    cheat)
  >- ((* Dtype - HARD, try this first *)
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
    cheat)
  >- ( (* Dmod *)
    first_x_assum drule>> disch_then drule >> rw[]>>
    qexists_tac`g`>>fs[]>>
    CONJ_TAC >- fs[tenvLift_def,set_tids_tenv_def]>>
    simp[Once type_d_canon_cases]>>
    qexists_tac`remap_tenv (extend_bij f g ids n) tenv'`>>
    fs[remap_tenv_def,tenvLift_def,namespacePropsTheory.nsLift_nsMap])
  >- simp[set_tids_tenv_def,Once type_d_canon_cases,remap_tenv_def, prim_tids_def]
  >> (*infer ds -- this MUST go through inductively *)
  first_x_assum drule>> disch_then drule>> rw[]>>
  simp[Once type_d_canon_cases]>>
  first_x_assum (qspecl_then [`tids ∪ ids`,`extend_bij f g ids n`,`CARD ids + n`] mp_tac)>>
  impl_tac >- (
    fs[good_remap_extend_bij,prim_tids_def,prim_type_nums_def]>>
    (* maybe it should only be an INJ instead of BIJ? *)
    cheat)>>
  rw[]>>
  qexists_tac `extend_bij g g' ids' (n + CARD ids)`>>
  rw[]
  >- cheat
  >- fs[prim_tids_def,prim_type_nums_def]
  >- (* this one is true, but maybe only need INJ? *) cheat
  >>
  qexists_tac`(remap_tenv (extend_bij f g ids n) tenv')`>>
  qexists_tac` (remap_tenv (extend_bij (extend_bij f g ids n) g' ids' (n + CARD ids)) tenv'')`>>
  qexists_tac`CARD ids`>>
  qexists_tac`CARD ids'`>>
  rw[]
  >- cheat (* set needs to be FINITE *)
  >- cheat
  >>
  fs[remap_tenv_extend_dec_tenv]>>
  (* same problem:
  (remap_tenv (extend_bij f g ids n) tenv)
  could have overwritten stuff in tenv unless the generated
  ids are disjoint from it *)
  cheat);

(*
val type_d_type_d_canon = Q.store_thm("type_d_type_d_canon",`
(∀extra_checks tenv d ids tenv'.
  type_d extra_checks tenv d ids tenv' ==>
  ∀f finv n.
  extra_checks = T ∧
  good_remap f ∧ good_remap finv ∧
  bij_remap f finv tenv
  ⇒
  (* The new remap is identical to f on tenv, but is otherwise
     bijective on the new stuff as well
  *)
  ∃g ginv.
  remap_tenv g tenv = remap_tenv f tenv ∧
  good_remap g ∧ good_remap ginv ∧
  bij_remap g ginv tenv' ∧
  type_d_canon n (remap_tenv f tenv) d (CARD ids) (remap_tenv g tenv')) ∧
(∀extra_checks tenv ds ids tenv'.
  type_ds extra_checks tenv ds ids tenv' ==>
  ∀f finv n.
  extra_checks = T ∧
  good_remap f ∧ good_remap finv ∧
  bij_remap f finv tenv
  ⇒
  ∃g ginv.
  remap_tenv g tenv = remap_tenv f tenv ∧
  good_remap g ∧ good_remap ginv ∧
  bij_remap g ginv tenv' ∧
  type_ds_canon n (remap_tenv f tenv) ds (CARD ids) (remap_tenv g tenv'))`,
  ho_match_mp_tac type_d_strongind>>
  rw[]>>fs[]
  >- (* Dlet poly*)
    cheat
  >- (* Dlet mono *)
    cheat
  >- (* Dletrec *)
    cheat
  >- (* Dtype *)
    cheat
  >- ( (* Dtabbrev *)
    simp[Once type_d_canon_cases]>>
    qexists_tac`f`>>qexists_tac`finv`>>fs[]>>
    CONJ_TAC>- (
      fs[bij_remap_def, remap_tenv_def, type_env_component_equality]>>
      simp[nsSing_def]>>
      dep_rewrite.DEP_REWRITE_TAC [ts_tid_rename_type_name_subst]>>fs[]>>
      metis_tac[check_type_names_ts_tid_rename])>>
    fs[remap_tenv_def]>>
    metis_tac[check_type_names_ts_tid_rename,ts_tid_rename_type_name_subst])
  >- ( (* Dexn *)
    simp[Once type_d_canon_cases]>>
    qexists_tac`f`>>qexists_tac`finv`>>fs[]>>
    CONJ_TAC >- (
      fs[bij_remap_def, remap_tenv_def, type_env_component_equality]>>
      simp[nsSing_def]>>
      cheat) >>
    fs[remap_tenv_def]>>
    CONJ_ASM2_TAC
    >- (
      fs[MAP_MAP_o]>> AP_TERM_TAC>>fs[]>>
      CONJ_TAC
      >-
        (fs[MAP_EQ_f,EVERY_MEM]>>
        metis_tac[check_type_names_ts_tid_rename,ts_tid_rename_type_name_subst])
      >>
        fs[good_remap_def,prim_type_nums_def])
    >>
      metis_tac[EVERY_MEM,check_type_names_ts_tid_rename,ts_tid_rename_type_name_subst])
  >- ( (* Dmod *)
    simp[Once type_d_canon_cases]>>
    first_x_assum (qspecl_then [`f`,`finv`,`n`] assume_tac)>>rfs[]>>
    qexists_tac`g`>> qexists_tac`ginv`>> fs[]>>
    CONJ_TAC
    >- (
      fs[bij_remap_def,tenvLift_def]>>
      fs[remap_tenv_def,GSYM namespacePropsTheory.nsLift_nsMap] >>
      fs[nsLift_def, type_env_component_equality])>>
    qexists_tac`remap_tenv g tenv'`>>
    fs[remap_tenv_def,tenvLift_def,namespacePropsTheory.nsLift_nsMap])
  >- (
    qexists_tac`f`>>qexists_tac`finv`>>
    fs[Once type_d_canon_cases,remap_tenv_def,bij_remap_def])
  >> (* type_ds *)
    simp[Once type_d_canon_cases]>>
    last_x_assum (qspecl_then [`f`,`finv`,`n`] assume_tac)>>rfs[]>>
    first_x_assum (qspecl_then [`g`,`ginv`,`n + CARD ids`] mp_tac)
    impl_tac >-
      fs[]>>
    impl_tac >-

    first_x_assum drule
  )
    qexists_tac`remap_tenv g tenv'`>>fs[remap_tenv_def]
    fs[remap_tenv_def]
    asm_exists_tac>>fs[]
    simo

*)

val _ = export_theory();
