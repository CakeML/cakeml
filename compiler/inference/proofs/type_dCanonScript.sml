(*
  For any type_d, prove that the canonical type identifier strategy
  succeeds.
*)
open preamble astTheory namespaceTheory typeSystemTheory;
open terminationTheory namespacePropsTheory;
open typeSysPropsTheory typeSoundInvariantsTheory inferPropsTheory

val _ = new_theory "type_dCanon"

(* TODO: move *)

val tenv_equiv_def = Define
  `tenv_equiv tenv1 tenv2 ⇔
     nsAll2 (λi v1 v2. v1 = v2) tenv1.t tenv2.t ∧
     nsAll2 (λi v1 v2. v1 = v2) tenv1.c tenv2.c ∧
     nsAll2 (λi v1 v2. v1 = v2) tenv1.v tenv2.v`;

Theorem tenv_equiv_refl[simp]:
   tenv_equiv tenv tenv
Proof
  rw[tenv_equiv_def, nsAll2_def]
  \\ irule nsSub_refl
  \\ rw[nsAll_def]
  \\ qexists_tac`K (K T)`\\ rw[]
QED

Theorem tenv_equiv_sym:
   tenv_equiv t1 t2 ⇒ tenv_equiv t2 t1
Proof
  rw[tenv_equiv_def, nsAll2_def, nsSub_def]
QED

Theorem tenv_equiv_tenvLift:
   tenv_equiv t1 t2 ⇒ tenv_equiv (tenvLift m t1) (tenvLift m t2)
Proof
  rw[tenv_equiv_def, tenvLift_def]
QED

Theorem check_type_names_tenv_equiv:
   ∀t1 t t2.
   nsAll2 (λi v1 v2. v1 = v2) t1 t2 ∧
   check_type_names t1 t ⇒
   check_type_names t2 t
Proof
  recInduct check_type_names_ind
  \\ rw[check_type_names_def]
  \\ fs[EVERY_MEM, option_case_NONE_F]
  \\ imp_res_tac nsAll2_nsLookup1 \\ fs[]
QED

Theorem lookup_var_tenv_equiv:
   tenv_equiv tenv1 tenv2 ⇒ lookup_var n bvs tenv1 = lookup_var n bvs tenv2
Proof
  rw[tenv_equiv_def, lookup_var_def, lookup_varE_def]
  \\ every_case_tac \\ fs[]
  \\ (fn g as (asl,w) => Cases_on[ANTIQUOTE(lhs w)] g)
  \\ imp_res_tac nsAll2_nsLookup_none
  \\ imp_res_tac nsAll2_nsLookup1
  \\ fs[]
QED

Theorem type_name_subst_tenv_equiv:
   ∀t1 t t2.
    nsAll2 (λi v1 v2. v1 = v2) t1 t2 ⇒
    type_name_subst t1 t = type_name_subst t2 t
Proof
  recInduct type_name_subst_ind
  \\ rw[type_name_subst_def, MAP_EQ_f]
  \\ CASE_TAC
  \\ imp_res_tac nsAll2_nsLookup_none \\ fs[MAP_EQ_f]
  \\ imp_res_tac nsAll2_nsLookup1 \\ fs[]
  \\ CASE_TAC
  \\ AP_THM_TAC
  \\ ntac 4 AP_TERM_TAC
  \\ rw[MAP_EQ_f]
QED

Theorem type_p_tenv_equiv:
   (∀tvs tenv1 p t bindings.
     type_p tvs tenv1 p t bindings ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_p tvs tenv2 p t bindings) ∧
   (∀tvs tenv1 ps ts bindings.
     type_ps tvs tenv1 ps ts bindings ⇒
     ∀tenv2. tenv_equiv tenv1 tenv2 ⇒
     type_ps tvs tenv2 ps ts bindings)
Proof
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
  \\ metis_tac[]
QED

Theorem type_e_tenv_equiv:
   (∀tenv1 bvs e t.
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
     type_funs tenv2 bvs funs ts)
Proof
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
               type_name_subst_tenv_equiv, check_type_names_tenv_equiv]
QED

Theorem type_pe_determ_tenv_equiv:
   type_pe_determ t1 x y z ∧
   tenv_equiv t1 t2 ⇒
   type_pe_determ t2 x y z
Proof
  rw[type_pe_determ_def]
  \\ imp_res_tac tenv_equiv_sym
  \\ imp_res_tac type_p_tenv_equiv
  \\ imp_res_tac type_e_tenv_equiv
  \\ res_tac
QED

(* -- *)

(* all the tids used in a tenv *)
val set_tids_tenv_def = Define`
  set_tids_tenv tids tenv ⇔
  nsAll (λi (ls,t). set_tids_subset tids t) tenv.t ∧
  nsAll (λi (ls,ts,tid). EVERY (λt. set_tids_subset tids t) ts ∧ tid ∈ tids) tenv.c ∧
  nsAll (λi (n,t). set_tids_subset tids t) tenv.v`

val type_pe_determ_canon_def = Define`
  type_pe_determ_canon n tenv tenvE p e ⇔
  ∀t1 tenv1 t2 tenv2.
    type_p 0 tenv p t1 tenv1 ∧ type_e tenv tenvE e t1 ∧
    EVERY (λ(k,t).  set_tids_subset (count n) t) tenv1 ∧
    type_p 0 tenv p t2 tenv2 ∧ type_e tenv tenvE e t2 ∧
    EVERY (λ(k,t).  set_tids_subset (count n) t) tenv2
    ⇒ tenv1 = tenv2`;

Theorem type_pe_determ_canon_tenv_equiv:
   type_pe_determ_canon n t1 x y z ∧
   tenv_equiv t1 t2 ⇒
   type_pe_determ_canon n t2 x y z
Proof
  rw[type_pe_determ_canon_def]
  \\ imp_res_tac tenv_equiv_sym
  \\ imp_res_tac type_p_tenv_equiv
  \\ imp_res_tac type_e_tenv_equiv
  \\ res_tac
QED

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
  type_e tenv (bind_tvar tvs' Empty) e t' ∧
  EVERY (λ(k,t).  set_tids_subset (count n) t) bindings'
  ) ==>
        EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings')) (MAP SND (tenv_add_tvs tvs bindings))))
  ==>
  type_d_canon n tenv (Dlet locs p e)
    0
    <| v := (alist_to_ns (tenv_add_tvs tvs bindings)); c := nsEmpty; t := nsEmpty |>) ∧
(!n tenv p e t bindings locs.
  ((~ (is_value e) /\ type_pe_determ_canon n tenv Empty p e) /\
  ALL_DISTINCT (pat_bindings p []) /\
  type_p(( 0 : num)) tenv p t bindings /\
  type_e tenv Empty e t)
  ==>
  type_d_canon n tenv (Dlet locs p e)
    0 <| v := (alist_to_ns (tenv_add_tvs(( 0 : num)) bindings)); c := nsEmpty; t := nsEmpty |>) ∧
(!n tenv funs bindings tvs locs.
  (type_funs tenv (bind_var_list(( 0 : num)) bindings (bind_tvar tvs Empty)) funs bindings /\
  (! tvs' bindings'.
      type_funs tenv (bind_var_list(( 0 : num)) bindings' (bind_tvar tvs' Empty)) funs bindings' /\
      EVERY (λ(k,t).  set_tids_subset (count n) t) bindings'
      ==>
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
(!n tenv lds ds decls1 decls2 tenv1 tenv2.
  (type_ds_canon n tenv lds decls1 tenv1) ∧
  (type_ds_canon (n+decls1) (extend_dec_tenv tenv1 tenv) ds decls2 tenv2)
  ==>
  type_d_canon n tenv (Dlocal lds ds) (decls1 + decls2) tenv2) ∧
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

(*
val extend_bij_def = Define`
  extend_bij (f:type_ident->type_ident) g tids ids n v =
  if v ∈ tids then
    f v
  else if v ∈ ids then
    n + g v
  else
    v`
*)

Theorem extend_bij_id[simp]:
    (extend_bij f f s 0 = f) ∧
  (extend_bij f g {} n = f)
Proof
  rw[extend_bij_def,FUN_EQ_THM]
QED

Theorem extend_bij_compose:
    extend_bij (extend_bij f g ids n) h jds (n + m) =
    extend_bij f (extend_bij g h jds m) (ids ∪ jds) n
Proof
  rw[extend_bij_def,FUN_EQ_THM]
  \\ rw[] \\ fs[]
QED

(* needs monotonicity of set_tids_tenv *)
val set_tids_tenv_extend_dec_tenv = Q.prove(`
  ∀s t s' t'.
  set_tids_tenv (s' ∪ s) t' ∧
  set_tids_tenv (s' ∪ s) t ⇒
  set_tids_tenv (s' ∪ s) (extend_dec_tenv t' t)`,
  rw[extend_dec_tenv_def,set_tids_tenv_def,nsAll_nsAppend]);

Theorem set_tids_tenv_remap:
   set_tids_tenv tids tenv ⇒
   set_tids_tenv (IMAGE f tids) (remap_tenv f tenv)
Proof
  rw[set_tids_tenv_def, remap_tenv_def, nsAll_nsMap, set_tids_subset_def,
     UNCURRY, set_tids_ts_tid_rename, EVERY_MAP]
  \\ fs[LAMBDA_PROD]
  \\ first_assum(mp_then Any match_mp_tac nsAll_mono)
  \\ simp[FORALL_PROD, EVERY_MEM]
  \\ metis_tac[]
QED

val good_remap_extend_bij = Q.prove(`
  good_remap f ∧ prim_tids F ids ⇒
  good_remap (extend_bij f g ids n)`,
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]);

(*
val good_remap_extend_bij = Q.prove(`
  good_remap f ∧ prim_tids T tids ⇒
  good_remap (extend_bij f g tids n)`,
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]);

val good_remap_extend_bij = Q.prove(`
  good_remap f ∧ prim_tids T tids ⇒
  good_remap (extend_bij f g tids ids n)`,
  rw[good_remap_def, extend_bij_def, prim_tids_def,prim_type_nums_def]);
*)

val remap_tenv_extend_dec_tenv = Q.prove(`
  remap_tenv f (extend_dec_tenv t t') =
  extend_dec_tenv (remap_tenv f t) (remap_tenv f t')`,
  fs[remap_tenv_def,extend_dec_tenv_def,nsMap_nsAppend]);

Theorem BIJ_extend_bij:
    DISJOINT tids ids ∧
  BIJ f tids (count n) ∧
  BIJ g ids (count (CARD ids)) ⇒
  BIJ (extend_bij f g ids n) (tids ∪ ids) (count (n + CARD ids))
Proof
  rewrite_tac[INJ_DEF,SURJ_DEF,BIJ_DEF,extend_bij_def,IN_DISJOINT]
  \\ strip_tac
  \\ rewrite_tac[IN_UNION, count_add, IN_IMAGE]
  \\ reverse conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ rpt (first_x_assum drule)>>fs[]
QED

(*
Theorem INJ_extend_bij:
    DISJOINT tids ids ∧
  INJ f tids (count n) ∧
  INJ g ids (count (CARD ids)) ⇒
  INJ (extend_bij f g ids n) (tids ∪ ids) (count (n + CARD ids))
Proof
  rewrite_tac[INJ_DEF,extend_bij_def,IN_DISJOINT,IN_COUNT,IN_UNION]
  \\ rpt strip_tac
  \\ res_tac
  \\ rpt (pop_assum mp_tac)
  \\ rewrite_tac[]
  \\ rpt IF_CASES_TAC
  \\ rpt strip_tac
  \\ full_simp_tac bool_ss []
  \\ fs[]
QED

Theorem BIJ_extend_bij:
    DISJOINT tids ids ∧
  BIJ f tids (count n) ∧
  BIJ g ids (count (CARD ids)) ⇒
  BIJ (extend_bij f g tids ids n) (tids ∪ ids) (count (n + CARD ids))
Proof
  rewrite_tac[INJ_DEF,SURJ_DEF,BIJ_DEF,extend_bij_def,IN_DISJOINT]
  \\ strip_tac
  \\ rewrite_tac[IN_UNION, count_add, IN_IMAGE]
  \\ reverse conj_tac >- metis_tac[]
  \\ conj_tac >- metis_tac[]
  \\ rw[]
  \\ rpt (first_x_assum drule)>>fs[]
QED
*)

Theorem set_tids_subset_mono:
   ∀tids t tids'.
  set_tids_subset tids t ∧ tids ⊆ tids' ⇒
  set_tids_subset tids' t
Proof
  rw[set_tids_subset_def, SUBSET_DEF]
QED

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

val ast_t_ind = ast_t_induction
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

Theorem sing_renum_NOTIN_ID:
   ∀t.
  m ∉ set_tids t ⇒
  ts_tid_rename (sing_renum m n) t = t
Proof
  ho_match_mp_tac t_ind>>rw[]>>
  fs[ts_tid_rename_def,sing_renum_def,set_tids_def]>>
  fs[EVERY_MEM,MAP_EQ_ID,MEM_MAP]>>
  metis_tac[]
QED

Theorem sing_renum_IN_NOT_ID:
   ∀t.  m ∈ set_tids t ∧ m ≠ n ⇒ ts_tid_rename (sing_renum m n) t ≠ t
Proof
  ho_match_mp_tac t_ind>>rw[]>>
  fs[ts_tid_rename_def,sing_renum_def,set_tids_def]>>
  fs[EVERY_MEM,MAP_EQ_ID,MEM_MAP]>>
  metis_tac[]
QED

(* TODO: this is only true up to equivalence on tenvs *)
Theorem sing_renum_NOTIN_tenv_ID:
   set_tids_tenv tids tenv ∧
  m ∉ tids ⇒
  tenv_equiv (remap_tenv (sing_renum m n) tenv) (tenv)
Proof
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
  \\ rw[sing_renum_def] \\ fs[]
QED

Theorem type_p_ts_tid_rename:
    good_remap f ⇒
  (∀tvs tenv p t bindings.
  type_p tvs tenv p t bindings ⇒
  type_p tvs (remap_tenv f tenv) p (ts_tid_rename f t)
    (MAP (λn,t. (n,ts_tid_rename f t)) bindings)) ∧
  (∀tvs tenv ps ts bindings.
  type_ps tvs tenv ps ts bindings ⇒
  type_ps tvs (remap_tenv f tenv) ps (MAP (ts_tid_rename f) ts)
    (MAP (λn,t. (n,ts_tid_rename f t)) bindings))
Proof
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
    metis_tac[]
QED

Theorem type_op_ts_tid_rename:
    good_remap f ⇒
  ∀op ts t.
  type_op op ts t ⇒
  type_op op (MAP (ts_tid_rename f) ts) (ts_tid_rename f t)
Proof
  rw[]>>
  fs[typeSysPropsTheory.type_op_cases,ts_tid_rename_def]>>
  fs[good_remap_def,prim_type_nums_def]
QED

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

Theorem remap_tenvE_bind_tvar:
   remap_tenvE f (bind_tvar tvs e) = bind_tvar tvs (remap_tenvE f e)
Proof
  rw[bind_tvar_def, remap_tenvE_def]
QED

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
  = OPTION_MAP (λid,t. (id, ts_tid_rename f t)) (lookup_varE n tenvE)`,
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

Theorem type_e_ts_tid_rename:
    good_remap f ⇒
  (∀tenv tenvE e t.
    type_e tenv tenvE e t ⇒
    type_e (remap_tenv f tenv) (remap_tenvE f tenvE) e (ts_tid_rename f t)) ∧
  (∀tenv tenvE es ts.
    type_es tenv tenvE es ts ⇒
    type_es (remap_tenv f tenv) (remap_tenvE f tenvE) es (MAP (ts_tid_rename f) ts)) ∧
  (∀tenv tenvE funs env.
    type_funs tenv tenvE funs env ⇒
    type_funs (remap_tenv f tenv) (remap_tenvE f tenvE) funs (MAP (λ(n,t). (n, ts_tid_rename f t)) env))
Proof
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
    fs[good_remap_def,prim_type_nums_def]
QED

Theorem good_remap_LINV:
   good_remap f ∧ prim_tids T s ∧ INJ f s t ⇒ good_remap (LINV f s o f)
Proof
  rw[good_remap_def, prim_tids_def, MAP_EQ_ID, EVERY_MEM]
  \\ res_tac
  \\ imp_res_tac LINV_DEF
QED

Theorem ts_tid_rename_LINV:
   ∀f x. INJ f s t ∧ set_tids_subset s x ⇒ ts_tid_rename (LINV f s) (ts_tid_rename f x) = x
Proof
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, MAP_MAP_o, set_tids_subset_def, SUBSET_DEF, MAP_EQ_ID]
  \\ fs[set_tids_def, PULL_EXISTS, MEM_MAP]
  >- (fs[EVERY_MEM] \\ metis_tac[])
  \\ imp_res_tac LINV_DEF
  \\ metis_tac[]
QED

Theorem remap_tenv_LINV:
   INJ f s t ∧ set_tids_tenv s tenv ⇒
   tenv_equiv (remap_tenv (LINV f s) (remap_tenv f tenv)) tenv
Proof
  rw[remap_tenv_def, tenv_equiv_def, nsMap_compose, nsAll2_def,
     nsSub_def, nsLookup_nsMap, nsLookupMod_nsMap]
  \\ fs[UNCURRY, set_tids_tenv_def]
  \\ imp_res_tac nsLookup_nsAll \\ fs[UNCURRY]
  \\ fs[MAP_MAP_o, o_DEF]
  \\ imp_res_tac ts_tid_rename_LINV \\ fs[]
  \\ imp_res_tac LINV_DEF \\ fs[EVERY_MEM]
  \\ simp[PAIR_FST_SND_EQ, MAP_EQ_ID]
QED

val LINVI_def = Define`
  LINVI f s y = case LINV_OPT f s y of SOME x => x | NONE => f y`;

Theorem remap_tenv_LINV:
   BIJ f s t ∧ set_tids_tenv s tenv ⇒
   tenv_equiv (remap_tenv (LINV f s) (remap_tenv f tenv)) tenv
Proof
  rw[remap_tenv_def, tenv_equiv_def, nsMap_compose, nsAll2_def,
     nsSub_def, nsLookup_nsMap, nsLookupMod_nsMap]
  \\ fs[UNCURRY, set_tids_tenv_def]
  \\ imp_res_tac nsLookup_nsAll \\ fs[UNCURRY]
  \\ fs[MAP_MAP_o, o_DEF]
  \\ imp_res_tac BIJ_DEF
  \\ imp_res_tac ts_tid_rename_LINV \\ fs[]
  \\ imp_res_tac BIJ_LINV_INV \\ fs[EVERY_MEM]
  \\ imp_res_tac LINV_DEF \\ fs[]
  \\ simp[PAIR_FST_SND_EQ, MAP_EQ_ID]
QED

Theorem good_remap_BIJ:
   good_remap f ∧ prim_tids T s ∧ BIJ f s t ⇒ good_remap (LINV f s)
Proof
  rw[good_remap_def, prim_tids_def, MAP_EQ_ID, EVERY_MEM]
  \\ imp_res_tac BIJ_LINV_BIJ
  \\ imp_res_tac BIJ_DEF
  \\ metis_tac[BIJ_LINV_INV, INJ_DEF]
QED

Theorem good_remap_LINVI:
   good_remap f ∧ prim_tids T s ∧ INJ f s t ⇒ good_remap (LINVI f s)
Proof
  rw[good_remap_def, prim_tids_def, LINVI_def, MAP_EQ_ID]
  \\ drule INJ_LINV_OPT
  \\ CASE_TAC \\ rw[]
  \\ fs[EVERY_MEM]
  \\ metis_tac[INJ_DEF]
QED

Theorem INJ_LINVI:
   INJ f s t ∧ x ∈ s ⇒ LINVI f s (f x) = x
Proof
  rw[LINVI_def]
  \\ CASE_TAC
  \\ imp_res_tac INJ_LINV_OPT \\ rw[]
  \\ metis_tac[INJ_DEF, NOT_NONE_SOME]
QED

Theorem LINVI_RINV:
   INJ f s t ∧ (∃x. x ∈ s ∧ f x = y) ⇒
   f (LINVI f s y) = y
Proof
  rw[LINVI_def]
  \\ drule INJ_LINV_OPT
  \\ disch_then(qspec_then`f x`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ CASE_TAC \\ rw[]
  \\ metis_tac[INJ_DEF]
QED

(*
Theorem BIJ_LINVI_RINV:
   BIJ f s t ∧ LINVI f s y ∈ s ⇒
   f (LINVI f s y) = y
Proof
  rw[LINVI_def, LINV_OPT_def] \\ fs[]
  ff"bij""inv"
  f"LINV_OPT"
  \\ imp_res_tac
  \\ drule INJ_LINV_OPT
  \\ disch_then(qspec_then`f x`mp_tac o CONV_RULE SWAP_FORALL_CONV)
  \\ CASE_TAC \\ rw[]
  \\ metis_tac[INJ_DEF]
QED
*)

Theorem ts_tid_rename_LINVI:
   ∀f x. INJ f s t ∧ set_tids_subset s x ⇒ ts_tid_rename (LINVI f s) (ts_tid_rename f x) = x
Proof
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, MAP_MAP_o, set_tids_def, set_tids_subset_def, MAP_EQ_ID]
  \\ fs[SUBSET_DEF, PULL_EXISTS, MEM_MAP]
  >- metis_tac[]
  \\ rw[LINVI_def]
  \\ imp_res_tac INJ_LINV_OPT
  \\ CASE_TAC \\ fs[]
  \\ metis_tac[INJ_DEF]
QED

Theorem remap_tenv_LINVI:
   INJ f s t ∧ set_tids_tenv s tenv ⇒
   tenv_equiv (remap_tenv (LINVI f s) (remap_tenv f tenv)) tenv
Proof
  rw[remap_tenv_def, tenv_equiv_def, nsMap_compose, nsAll2_def,
     nsSub_def, nsLookup_nsMap, nsLookupMod_nsMap]
  \\ fs[UNCURRY, set_tids_tenv_def]
  \\ imp_res_tac nsLookup_nsAll \\ fs[UNCURRY]
  \\ fs[MAP_MAP_o, o_DEF]
  \\ imp_res_tac ts_tid_rename_LINVI \\ fs[]
  \\ imp_res_tac INJ_LINVI \\ fs[EVERY_MEM]
  \\ simp[PAIR_FST_SND_EQ, MAP_EQ_ID]
QED

Theorem ts_tid_rename_compose:
   ∀g t f. ts_tid_rename f (ts_tid_rename g t) = ts_tid_rename (f o g) t
Proof
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, MAP_MAP_o, o_DEF, MAP_EQ_f]
QED

Theorem remap_tenv_compose:
   remap_tenv f (remap_tenv g tenv) = remap_tenv (f o g) tenv
Proof
  srw_tac[ETA_ss]
    [remap_tenv_def, nsMap_compose, ts_tid_rename_compose,
     o_DEF, UNCURRY, LAMBDA_PROD, MAP_MAP_o]
QED

Theorem ts_tid_rename_eq_id:
   ∀f t. (ts_tid_rename f t = t ⇔ ∀x. x ∈ set_tids t ⇒ f x = x)
Proof
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, set_tids_def, MAP_EQ_ID, MEM_MAP]
  \\ rw[EQ_IMP_THM] \\ rw[]
  \\ metis_tac[]
QED

Theorem ts_tid_rename_eq_f:
   ∀f t g. (ts_tid_rename f t = ts_tid_rename g t ⇔ ∀x. x ∈ set_tids t ⇒ f x = g x)
Proof
  recInduct ts_tid_rename_ind
  \\ rw[ts_tid_rename_def, set_tids_def, MAP_EQ_f, MEM_MAP]
  \\ rw[EQ_IMP_THM] \\ rw[]
  \\ metis_tac[]
QED

Theorem inj_ts_tid_rename_eq:
   ∀f t1 t2.
    (∀x y.
      x ∈ set_tids t1 ∧ y ∈ set_tids t2 ∧
      f x = f y ⇒ x = y) ∧
    (ts_tid_rename f t1 = ts_tid_rename f t2 )
    ⇒ t1 = t2
Proof
  recInduct ts_tid_rename_ind
  \\ rewrite_tac[ts_tid_rename_def, set_tids_def, NOT_IN_EMPTY, IN_INSERT]
  \\ rpt strip_tac \\ Cases_on`t2`
  \\ pop_assum mp_tac \\ rewrite_tac[ts_tid_rename_def]
  \\ simp_tac(srw_ss())[]
  \\ pop_assum mp_tac
  \\ rewrite_tac[set_tids_def, IN_INSERT, IN_BIGUNION, MEM_MAP]
  \\ simp_tac(pure_ss++ETA_ss)[PULL_EXISTS]
  \\ CONV_TAC(DEPTH_CONV BETA_CONV)
  \\ ntac 2 strip_tac
  \\ reverse conj_tac >- metis_tac[]
  \\ first_x_assum(mp_then Any match_mp_tac INJ_MAP_EQ_2)
  \\ metis_tac[]
QED

(* probably not be true because of shadows...
Theorem remap_tenv_LINVI
  `INJ f s t ∧ set_tids_tenv s tenv ⇒
   remap_tenv (LINVI f s) (remap_tenv f tenv) = tenv`
  (rw[remap_tenv_def, type_env_component_equality,
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

Theorem type_funs_ts_tid_rename_sing_renum:
    m ∉ tids ∧ prim_tids T tids ∧
  type_funs tenv tenvE funs res ∧
  set_tids_tenv tids tenv
  ⇒
  type_funs tenv (remap_tenvE (sing_renum m n) tenvE) funs
    (MAP (λ(z,t). (z, ts_tid_rename (sing_renum m n) t)) res)
Proof
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
  metis_tac[type_e_tenv_equiv]
QED

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

Theorem type_funs_bindings_tids:
   type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs Empty)) funs bindings ∧
   set_tids_tenv tids tenv ∧ prim_tids T tids ∧
   (∀tvs' bindings'.
     type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' Empty)) funs bindings' ⇒
     LIST_REL tscheme_inst (MAP (λx. (tvs', SND x)) bindings')
       (MAP (λx. (tvs, SND x)) bindings))
   ⇒
   EVERY (set_tids_subset tids o SND) bindings
Proof
  CCONTR_TAC>>fs[set_tids_subset_def,SUBSET_DEF,EXISTS_MEM]>>
  drule (GEN_ALL type_funs_ts_tid_rename_sing_renum)>>
  rpt (disch_then drule)>>
  disch_then(qspec_then`x+1` mp_tac)>>
  strip_tac
  \\ fs[remap_tenvE_bind_var_list, remap_tenvE_bind_tvar, remap_tenvE_def]
  \\ first_x_assum drule
  \\ rw[LIST_REL_EL_EQN]>>
  fs[MEM_EL]>>
  asm_exists_tac>>
  fs[EL_MAP,UNCURRY]>>
  `x ≠ x+1` by fs[]>>
  metis_tac[sing_renum_NOT_tscheme_inst]
QED

Theorem type_pe_bindings_tids_0:
     prim_tids T tids ∧
   set_tids_tenv tids tenv ∧
   type_p 0 tenv p t bindings ∧
   type_e tenv Empty e t ∧
   type_pe_determ tenv Empty p e ⇒
   ∀p_1 p_2. MEM (p_1,p_2) bindings ⇒ set_tids_subset tids p_2
Proof
  CCONTR_TAC>>fs[set_tids_subset_def,SUBSET_DEF]>>
  drule (GEN_ALL type_p_ts_tid_rename_sing_renum)>>
  rpt (disch_then drule)>>
  disch_then(qspec_then`x+1` mp_tac)>>
  strip_tac>>
  drule (GEN_ALL type_e_ts_tid_rename_sing_renum)>>
  rpt(disch_then drule)>>
  disch_then (qspec_then `x+1` mp_tac)>>
  fs[remap_tenvE_def,type_pe_determ_def] >>
  strip_tac >>
  res_tac >>
  fs[MAP_EQ_ID] >>
  res_tac >>
  pairarg_tac \\ fs[] \\ rw[]
  \\ `x ≠ x+1` by fs[]>>
  metis_tac[sing_renum_IN_NOT_ID]
QED

Theorem type_pe_determ_remap:
   type_pe_determ tenv Empty p e ∧
   good_remap f ∧
   prim_tids T tids ∧
   BIJ f tids (count n) ∧
   set_tids_tenv tids tenv
   ⇒
   type_pe_determ_canon n (remap_tenv f tenv) Empty p e
Proof
  fs[type_pe_determ_canon_def,type_pe_determ_def] \\ rw[]
  \\ imp_res_tac good_remap_BIJ >>
  drule (GEN_ALL type_p_ts_tid_rename) >>
  disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["t"])) o CONJUNCT1)
  \\ disch_then(fn th =>
      qspec_then`t1`mp_tac th >>
      qspec_then`t2`mp_tac th)
  \\ disch_then drule \\ strip_tac
  \\ drule(CONJUNCT1 type_p_tenv_equiv) \\ strip_tac
  \\ disch_then drule \\ strip_tac
  \\ drule(CONJUNCT1 type_p_tenv_equiv) \\ strip_tac
  \\ drule (GEN_ALL type_e_ts_tid_rename)
  \\ disch_then(mp_tac o CONV_RULE(RESORT_FORALL_CONV(sort_vars["t"])) o CONJUNCT1)
  \\ disch_then(fn th =>
      qspec_then`t1`mp_tac th >>
      qspec_then`t2`mp_tac th)
  \\ disch_then drule \\ strip_tac
  \\ drule(CONJUNCT1 type_e_tenv_equiv) \\ strip_tac
  \\ disch_then drule \\ strip_tac
  \\ drule(CONJUNCT1 type_e_tenv_equiv) \\ strip_tac
  \\ drule remap_tenv_LINV
  \\ impl_tac >- rw[]
  \\ strip_tac
  \\ ntac 4 (first_x_assum drule)
  \\ rw[remap_tenvE_def]
  \\ res_tac \\ fs[] \\ rw[]
  \\ match_mp_tac EQ_SYM
  \\ first_x_assum(mp_then Any match_mp_tac INJ_MAP_EQ_2)
  \\ simp[FORALL_PROD]
  \\ rw[]
  \\ first_x_assum(mp_then Any match_mp_tac inj_ts_tid_rename_eq)
  \\ rw[]
  \\ fs[EVERY_MEM,FORALL_PROD,set_tids_subset_def]
  \\ metis_tac[BIJ_LINV_INV, SUBSET_DEF]
QED

Theorem build_ctor_tenv_type_identities:
    ∀tenvt xs type_identities tids.
  prim_tids T tids ∧
  nsAll (λi (ls,t). set_tids_subset (tids ∪ set type_identities) t) tenvt ∧
  LENGTH xs = LENGTH type_identities ⇒
  nsAll ((λi (ls,ts,tid).
    EVERY (λt. set_tids_subset (tids ∪ set type_identities) t) ts ∧
    (tid ∈ tids ∨ MEM tid type_identities)))
    (build_ctor_tenv tenvt xs type_identities)
Proof
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
  fs[prim_tids_def,prim_type_nums_def]
QED

(*
Theorem type_d_canon_tenv_equiv
  `(∀x t d c v. type_d_canon x t d c v ⇒
      ∀v2. tenv_equiv v v2 ⇒ type_d_canon x t d c v2) ∧
   (∀x t d c v. type_ds_canon x t d c v ⇒
      ∀v2. tenv_equiv v v2 ⇒ type_ds_canon x t d c v2)`
  (ho_match_mp_tac type_d_canon_ind
  \\ rw[]
  \\ rw[Once type_d_canon_cases]
  type_d_canon_rules
*)

Theorem DISJOINT_CARD_UNION:
   FINITE s /\ FINITE t /\ DISJOINT s t
    ==> CARD (s UNION t) = CARD s + CARD t
Proof
  metis_tac [CARD_UNION, DISJOINT_DEF, CARD_DEF, ADD, ADD_SYM]
QED

(* For any type_d, prove that the canonical type identifier strategy
  succeeds.
  f,g are maps from the identifiers used in type_d into the ones
  used by type_d_canon
  TODO: do we actually need the bijection??
*)
Theorem type_d_type_d_canon:
    (∀extra_checks tenv d ids tenv'.
    type_d extra_checks tenv d ids tenv' ==>
    ∀tids f n mapped_tenv.
    (* These restrict the kinds of type_d that we are thinking about *)
    extra_checks = T ∧
    DISJOINT ids tids ∧
    (* Over-approximation of the tids in tenv *)
    set_tids_tenv tids tenv ∧
    (* f injects all of the tids already used in tenv into the canonical system *)
    BIJ f tids (count n) ∧
    (* tids contains at least the primitive type numbers and f is identity on them *)
    prim_tids T tids ∧ good_remap f ∧
    tenv_equiv (remap_tenv f tenv) mapped_tenv ⇒
      ∃g mapped_tenv'.
        (* This is actually a property of the type system *)
        set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧ FINITE ids ∧
        (* This forces g to extend the injection on f *)
        BIJ g ids (count (CARD ids)) ∧
        type_d_canon n mapped_tenv d (CARD ids) mapped_tenv' ∧
        tenv_equiv (remap_tenv (extend_bij f g ids n) tenv') mapped_tenv') ∧
  (∀extra_checks tenv ds ids tenv'.
    type_ds extra_checks tenv ds ids tenv' ==>
    ∀tids f n mapped_tenv.
    extra_checks = T ∧
    DISJOINT ids tids ∧
    set_tids_tenv tids tenv ∧
    BIJ f tids (count n) ∧
    prim_tids T tids ∧ good_remap f ∧
    tenv_equiv (remap_tenv f tenv) mapped_tenv
    ⇒
    ∃g mapped_tenv'.
      set_tids_tenv (tids ∪ ids) tenv' ∧ prim_tids F ids ∧ FINITE ids ∧
      BIJ g ids (count (CARD ids)) ∧
      type_ds_canon n mapped_tenv ds (CARD ids) mapped_tenv' ∧
      tenv_equiv (remap_tenv (extend_bij f g ids n) tenv') mapped_tenv')
Proof
  ho_match_mp_tac type_d_strongind>>
  rw[]>>fs[]
  >- (
    (* Dlet poly *)
    fs[set_tids_tenv_def,tenv_add_tvs_def]>>
    DEP_REWRITE_TAC[nsAll_alist_to_ns] >>
    CONJ_ASM1_TAC>- (
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
    simp[PULL_EXISTS] >>
    qexists_tac`tvs`>>qexists_tac`t2`>>qexists_tac`bindings2`>>
    unabbrev_all_tac>>fs[]>>
    CONJ_TAC>- (
      simp[MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
      metis_tac[type_p_tenv_equiv] )
    >> CONJ_TAC>- (
      drule type_e_ts_tid_rename>> rw[]>>
      first_x_assum drule>>
      rw[bind_tvar_def,remap_tenvE_def] >>
      metis_tac[type_e_tenv_equiv])>>
    rw[MAP_MAP_o, o_DEF, UNCURRY] >>
    imp_res_tac tenv_equiv_sym >>
    drule (CONJUNCT1 type_p_tenv_equiv) >>
    disch_then drule >> strip_tac >>
    drule (CONJUNCT1 type_e_tenv_equiv) >>
    disch_then drule >> strip_tac >>
    (* BIJ version *)
    imp_res_tac remap_tenv_LINV >>
    pop_assum(qspec_then`tenv`mp_tac) >>
    impl_tac >- simp[set_tids_tenv_def] >>
    strip_tac >>
    fs[remap_tenv_compose] >>
    imp_res_tac good_remap_BIJ >>
    drule (GEN_ALL type_p_ts_tid_rename) >>
    disch_then (qspecl_then[`tvs''`]mp_tac o CONJUNCT1)
    \\ disch_then drule
    \\ fs[remap_tenv_compose]
    \\ strip_tac
    \\ drule (CONJUNCT1 type_p_tenv_equiv)
    \\ disch_then drule
    \\ strip_tac
    \\ first_assum drule
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
    \\ match_mp_tac (MP_CANON BIJ_LINV_INV)
    \\ asm_exists_tac \\ simp[]
    \\ qpat_x_assum`EVERY _ bindings''` mp_tac
    \\ simp[EVERY_MEM,MEM_EL, PULL_EXISTS, set_tids_tenv_mono,EL_MAP]
    \\ disch_then drule \\ pairarg_tac \\ fs[]
    \\ rw[set_tids_subset_def,SUBSET_DEF])
    (* INJ version
    imp_res_tac good_remap_LINVI >>
    drule (GEN_ALL type_p_ts_tid_rename) >>
    disch_then (qspecl_then[`tvs''`]mp_tac o CONJUNCT1)
    \\ disch_then drule
    \\ fs[remap_tenv_compose]
    \\ strip_tac
    \\ drule (CONJUNCT1 type_p_tenv_equiv)
    \\ disch_then drule
    \\ strip_tac
    \\ first_assum drule
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
    \\ `x < n` suffices_by PROVE_TAC[BIJ_LINV_INV, IN_COUNT, BIJ_LINV_BIJ, BIJ_DEF, INJ_DEF]
    *)
    (*
    \\ qmatch_asmsub_abbrev_tac`type_p tvs tenv p t`
    \\ first_assum(mp_tac o Q.AP_TERM`set_tids`)
    \\ simp_tac (srw_ss()) [set_tids_ts_tid_rename]
    \\ disch_then (assume_tac o SYM)
    \\ qmatch_asmsub_abbrev_tac`IMAGE _ _ = tids'`
    \\ `LINVI f tids x ∈ tids'` by (fs[EXTENSION] \\  metis_tac[])
    \\ fs[EVERY_MEM,MEM_MAP, PULL_EXISTS, FORALL_PROD]
    \\ qmatch_asmsub_rename_tac`EL m bindings`
    \\ first_x_assum(qspecl_then[`FST(EL m bindings)`,`SND (EL m bindings)`]mp_tac)
    \\ impl_tac >- (simp[MEM_EL] \\ metis_tac[])
    \\ simp[set_tids_subset_def]
    \\ fs[Abbr`tids'`]
    *)
  >- ((* Dlet mono *)
    fs[set_tids_tenv_def,tenv_add_tvs_def]>>
    simp[prim_tids_def, Once type_d_canon_cases, PULL_EXISTS]>>
    qexists_tac`ts_tid_rename f t`>>
    qexists_tac`MAP (\n,t. (n,ts_tid_rename f t)) bindings`>>
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
    )>>
    simp[Once remap_tenv_def]>>
    simp[tenv_add_tvs_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD,o_DEF,LAMBDA_PROD]>>
    reverse conj_tac >- (
      drule type_e_ts_tid_rename>>
      disch_then(drule o CONJUNCT1)>>
      simp[remap_tenvE_def]>>
      metis_tac[type_p_ts_tid_rename,
                type_p_tenv_equiv,
                type_e_tenv_equiv] )
    \\ match_mp_tac (GEN_ALL type_pe_determ_canon_tenv_equiv)
    \\ goal_assum (first_assum o mp_then (Pos(el 2)) mp_tac)
    \\ match_mp_tac type_pe_determ_remap
    \\ rw[set_tids_tenv_def])
  >- ((* Dletrec *)
    rw[Once type_d_canon_cases, PULL_EXISTS, prim_tids_def, set_tids_tenv_def]
    \\ drule type_e_ts_tid_rename
    \\ disch_then (drule o last o CONJUNCTS)
    \\ strip_tac
    \\ drule (last(CONJUNCTS type_e_tenv_equiv))
    \\ disch_then drule
    \\ rw[remap_tenvE_bind_var_list, remap_tenvE_bind_tvar, remap_tenvE_def]
    \\ goal_assum(first_assum o mp_then Any mp_tac)
    \\ DEP_REWRITE_TAC[nsAll_alist_to_ns]
    \\ simp[tenv_add_tvs_def, EVERY_MAP, UNCURRY]
    \\ fs[tenv_add_tvs_def, MAP_MAP_o, o_DEF, UNCURRY]
    \\ last_assum(mp_then Any mp_tac type_funs_bindings_tids)
    \\ impl_tac >- rw[]
    \\ simp[o_DEF] \\ strip_tac
    \\ simp[remap_tenv_def,MAP_MAP_o,o_DEF,UNCURRY]
    \\ rw[]
    \\ drule (last(CONJUNCTS type_e_tenv_equiv))
    \\ imp_res_tac tenv_equiv_sym
    \\ disch_then drule
    \\ strip_tac
    \\ imp_res_tac good_remap_BIJ
    \\ drule type_e_ts_tid_rename
    \\ disch_then(drule o last o CONJUNCTS)
    \\ rw[remap_tenvE_bind_var_list, remap_tenvE_bind_tvar, remap_tenvE_def]
    \\ imp_res_tac remap_tenv_LINV
    \\ drule (last(CONJUNCTS type_e_tenv_equiv))
    \\ disch_then drule
    \\ strip_tac
    \\ first_assum drule
    \\ simp_tac(srw_ss())[MAP_MAP_o,o_DEF,UNCURRY]
    \\ `LENGTH bindings = LENGTH funs ∧ LENGTH bindings' = LENGTH funs`
    by metis_tac[LENGTH_MAP, typeSysPropsTheory.type_funs_MAP_FST]
    \\ simp[LIST_REL_EL_EQN,EL_MAP]
    \\ rw[]
    \\ first_x_assum drule
    \\ simp[tscheme_inst_def]
    \\ simp[GSYM deBruijn_inc_ts_tid_rename, check_freevars_ts_tid_rename]
    \\ strip_tac
    \\ qexists_tac`MAP (ts_tid_rename f) subst`
    \\ srw_tac[ETA_ss][EVERY_MAP, check_freevars_ts_tid_rename]
    \\ simp[GSYM ts_tid_rename_deBruijn_subst, ts_tid_rename_compose]
    \\ rw[ts_tid_rename_eq_id]
    \\ match_mp_tac (MP_CANON BIJ_LINV_INV)
    \\ asm_exists_tac \\ simp[]
    \\ qpat_x_assum`EVERY _ bindings'` mp_tac
    \\ simp[EVERY_MEM,MEM_EL, PULL_EXISTS, set_tids_tenv_mono,EL_MAP]
    \\ disch_then drule \\ pairarg_tac \\ fs[]
    \\ rw[set_tids_subset_def,SUBSET_DEF])
  >- ((* Dtype *)
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
    qabbrev_tac`g = THE o (ALOOKUP (ZIP (type_identities, COUNT_LIST (LENGTH tdefs))))`>>
    qexists_tac`g`>>
    CONJ_TAC >- (
      simp[BIJ_IFF_INV]
      \\ qmatch_asmsub_abbrev_tac`g = THE o ALOOKUP al`
      \\ `∀n. n < LENGTH type_identities ⇒
              ALOOKUP al (EL n type_identities) = SOME n`
      by (
        qx_gen_tac`m`
        \\ rw[]
        \\ `EL m type_identities = FST (EL m al)` by simp[Abbr`al`,EL_ZIP,LENGTH_COUNT_LIST]
        \\ rw[]
        \\ DEP_REWRITE_TAC[ALOOKUP_ALL_DISTINCT_EL]
        \\ simp[Abbr`al`,LENGTH_ZIP,LENGTH_COUNT_LIST,MAP_ZIP]
        \\ metis_tac[EL_ZIP,LENGTH_COUNT_LIST,EL_COUNT_LIST,SND] )
      \\ conj_tac >- (
        rw[Abbr`g`,MEM_EL]
        \\ metis_tac[THE_DEF] )
      \\ qexists_tac`λn. EL n type_identities`
      \\ simp[]
      \\ conj_tac >- metis_tac[MEM_EL]
      \\ rw[MEM_EL,Abbr`g`]
      \\ metis_tac[THE_DEF]) \\
    CONJ_TAC>- (
      fs[BIJ_DEF,prim_tids_def,INJ_DEF,good_remap_def]>>
      metis_tac[])>>
    CONJ_TAC>- (
      fs[BIJ_DEF,prim_tids_def,INJ_DEF,good_remap_def]>>
      metis_tac[])>>
    CONJ_TAC >- (
      rw[FOLDR_MAX_0_list_max]
      \\ fs[good_remap_def]
      \\ DEEP_INTRO_TAC list_max_intro
      \\ conj_tac
      >- (
        fs[BIJ_DEF,prim_tids_def,INJ_DEF]
        \\ res_tac \\ simp[] )
      \\ fs[prim_tids_def,EVERY_MEM,BIJ_DEF,INJ_DEF,MAP_EQ_ID]
      \\ metis_tac[])
    \\ reverse CONJ_TAC >- (
      rw[remap_tenv_def]
      \\ qmatch_goalsub_abbrev_tac`tenv_equiv t1 t2`
      \\ `t1 = t2` suffices_by rw[]
      \\ qunabbrev_tac`t1` \\ qunabbrev_tac`t2`
      \\ rw[]
      (*
      \\ reverse(rw[tenv_equiv_def])
      *)
      >- (
        qmatch_goalsub_abbrev_tac`MAP2 ff`
        \\ qmatch_goalsub_abbrev_tac`nsAppend ns1`
        \\ qmatch_goalsub_abbrev_tac`ts_tid_rename fg`
        \\ qmatch_goalsub_abbrev_tac`_ = (build_ctor_tenv (nsAppend ns2 _) _ tids')`
        \\ `LENGTH tids' = LENGTH tdefs` by simp[Abbr`tids'`]
        \\ simp[build_ctor_tenv_FOLDL, MAP2_MAP, GSYM MAP_REVERSE, nsMap_FOLDL_nsAppend]
        \\ simp[MAP_MAP_o,MAP_REVERSE]
        \\ simp[o_DEF,UNCURRY,MAP_REVERSE]
        \\ AP_TERM_TAC
        \\ simp[LIST_EQ_REWRITE,EL_MAP,EL_ZIP,UNCURRY]
        \\ gen_tac \\ strip_tac
        \\ gen_tac \\ strip_tac
        \\ reverse conj_tac
        >- (
          simp[Abbr`fg`,extend_bij_def]
          \\ reverse IF_CASES_TAC >- metis_tac[MEM_EL]
          \\ simp[Abbr`tids'`]
          \\ simp[Abbr`g`]
          \\ qmatch_goalsub_abbrev_tac`ALOOKUP al k`
          \\ qispl_then[`al`,`x`]mp_tac ALOOKUP_ALL_DISTINCT_EL
          \\ simp[Abbr`al`,LENGTH_COUNT_LIST,MAP_ZIP,EL_ZIP,EL_COUNT_LIST] )
        \\ gen_tac \\ strip_tac
        (*
        \\ `type_name_subst (nsAppend ns2 mapped_tenv.t) =
            type_name_subst (nsAppend ns2 tenv.t)
        *)
        \\ DEP_REWRITE_TAC[ts_tid_rename_type_name_subst]
        \\ reverse conj_tac
        >- (
          simp[nsMap_nsAppend]
          \\ simp[nsMap_alist_to_ns, Abbr`ns1`]
          \\ simp[Abbr`ns2`]
          \\ srw_tac[ETA_ss][MAP2_MAP,MAP_MAP_o,o_DEF,Abbr`ff`,UNCURRY,
                             LAMBDA_PROD,ts_tid_rename_def]
          \\ qmatch_goalsub_abbrev_tac`alist_to_ns al1`
          \\ match_mp_tac EQ_SYM
          \\ qmatch_goalsub_abbrev_tac`alist_to_ns al2`
          \\ `al1 = al2`
          by (
            simp[Abbr`al1`,Abbr`al2`]
            \\ simp[LIST_EQ_REWRITE,EL_MAP,EL_ZIP,UNCURRY]
            \\ simp[Abbr`tids'`,Abbr`fg`]
            \\ simp[extend_bij_def]
            \\ qx_gen_tac`z` \\ strip_tac
            \\ reverse IF_CASES_TAC >- metis_tac[MEM_EL]
            \\ simp[Abbr`g`]
            \\ qmatch_goalsub_abbrev_tac`ALOOKUP al k`
            \\ qispl_then[`al`,`z`]mp_tac ALOOKUP_ALL_DISTINCT_EL
            \\ simp[Abbr`al`,LENGTH_COUNT_LIST,MAP_ZIP,EL_ZIP,EL_COUNT_LIST] )
          \\ match_mp_tac type_name_subst_tenv_equiv
          \\ match_mp_tac nsAll2_nsAppend
          \\ conj_tac
          >- (
            rw[nsAll2_def]
            \\ irule nsSub_refl
            \\ rw[]
            \\ rw[nsAll_def]
            \\ qexists_tac`K(K T)` \\ rw[] )
          \\ fs[nsAll2_def, nsSub_def, nsLookup_nsMap,
                PULL_EXISTS, nsLookupMod_nsMap, FORALL_PROD,
                ts_tid_rename_eq_f, tenv_equiv_def, remap_tenv_def]
          \\ fs[set_tids_tenv_def, nsAll_def, FORALL_PROD,
                set_tids_subset_def, SUBSET_DEF, Abbr`fg`,EXISTS_PROD]
          \\ rw[] \\ rw[]
          \\ res_tac
          \\ fs[IN_DISJOINT,extend_bij_def,ts_tid_rename_eq_f]
          \\ metis_tac[] )
        \\ conj_tac
        >- (
          simp[Abbr`fg`]
          \\ fs[extend_bij_def, good_remap_def, MAP_EQ_ID, IN_DISJOINT]
          \\ metis_tac[] )
        \\ simp[Abbr`ns1`]
        \\ fs[check_ctor_tenv_EVERY,EVERY_MEM]
        \\ first_x_assum(qspec_then`EL x tdefs`mp_tac)
        \\ impl_tac >- metis_tac[MEM_EL]
        \\ simp[UNCURRY]
        \\ srw_tac[DNF_ss][]
        \\ first_x_assum irule
        \\ metis_tac[MEM_EL]) \\
      simp[MAP2_MAP,MAP_MAP_o,LIST_EQ_REWRITE,EL_MAP,EL_ZIP,LAMBDA_PROD]>>
      rw[]>>
      rpt(pairarg_tac>>fs[])>>rw[]>>
      simp[ts_tid_rename_def,MAP_EQ_ID,MEM_MAP,PULL_EXISTS]>>
      simp[extend_bij_def,EL_MEM,Abbr`g`]>>
      qmatch_goalsub_abbrev_tac`ALOOKUP al y`
      \\ Cases_on`ALOOKUP al y` \\ fs[]
      >- (
        rfs[LENGTH_COUNT_LIST, ALOOKUP_ZIP_FAIL, Abbr`y`, Abbr`al`]
        \\ metis_tac[MEM_EL] )
      \\ qispl_then[`al`,`x`]mp_tac ALOOKUP_ALL_DISTINCT_EL
      \\ simp[Abbr`al`,LENGTH_ZIP,LENGTH_COUNT_LIST,MAP_ZIP,EL_ZIP,EL_COUNT_LIST])
    (* Otherwise count n is not big enough to form *)
    \\ first_assum (mp_then Any match_mp_tac check_ctor_tenv_change_tenvT)
    \\ simp[EVERY_FLAT, remap_tenv_def, EVERY_MAP, LAMBDA_PROD]
    \\ rw[EVERY_MEM, FORALL_PROD, MAP2_MAP]
    \\ res_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac`e`
    \\ ho_match_mp_tac ast_t_ind
    \\ rw[check_type_names_def]
    \\ TRY( fs[EVERY_MEM] \\ NO_TAC)
    \\ CASE_TAC
    >- (
      fs[nsLookup_nsAppend_none, option_case_NONE_F, nsLookup_nsAppend_some,
         nsLookup_alist_to_ns_some, nsLookup_alist_to_ns_none, nsLookup_nsMap,
         tenv_equiv_def, nsAll2_def, nsSub_def, remap_tenv_def, PULL_EXISTS]
      \\ rfs[ALOOKUP_FAILS]
      \\ imp_res_tac ALOOKUP_MEM
      \\ rfs[MEM_MAP,MEM_ZIP,EL_GENLIST,EXISTS_PROD]
      \\ TRY (
        qmatch_asmsub_rename_tac`p1 ≠[]`
        \\ Cases_on`p1` \\ rfs[nsLookupMod_alist_to_ns] )
      \\ metis_tac[NOT_SOME_NONE] )
    \\ fs[option_case_NONE_F]
    \\ qhdtm_x_assum`nsLookup`mp_tac
    \\ qhdtm_x_assum`nsLookup`mp_tac
    \\ simp[nsLookup_nsAppend_some, PULL_EXISTS,
            nsLookup_alist_to_ns_some,
            nsLookup_alist_to_ns_none,
            nsLookup_nsMap]
    \\ fs[tenv_equiv_def,nsAll2_def,nsSub_def,remap_tenv_def,
          nsLookup_nsMap,nsLookupMod_nsMap]
    \\ rw[]
    \\ rfs[ALOOKUP_FAILS]
    \\ TRY (
      res_tac
      \\ rw[] \\ pairarg_tac \\ fs[]
      \\ rw[] \\ fs[] \\ NO_TAC)
    \\ TRY (
      fs[ALOOKUP_LEAST_EL]
      \\ rw[]
      \\ fs[MAP_MAP_o]
      \\ qmatch_goalsub_abbrev_tac `MAP ff (ZIP _)`
      \\ `ff = (FST o SND) o FST` by simp[Abbr`ff`,FUN_EQ_THM, UNCURRY]
      \\ qunabbrev_tac`ff` \\ pop_assum SUBST_ALL_TAC
      \\ rfs[MAP_ZIP] \\ rw[]
      \\ qhdtm_x_assum`pair_CASE`mp_tac
      \\ numLib.LEAST_ELIM_TAC
      \\ conj_tac >- metis_tac[MEM_EL]
      \\ qx_gen_tac`m` \\ strip_tac
      \\ `m < LENGTH tdefs` by (
        CCONTR_TAC \\ fs[NOT_LESS, MEM_EL]
        \\ qmatch_asmsub_rename_tac`k < LENGTH tdefs`
        \\ `k  < m` by fs[]
        \\ metis_tac[] )
      \\ simp[EL_MAP, EL_ZIP, UNCURRY]
      \\ NO_TAC)
    \\ TRY (
      imp_res_tac ALOOKUP_MEM
      \\ rfs[MEM_MAP,MEM_ZIP,EL_GENLIST,EXISTS_PROD]
      \\ metis_tac[NOT_NONE_SOME] ))
  >- ( (* Dtabbrev *)
    simp[set_tids_tenv_def]>>
    simp[Once type_d_canon_cases, prim_tids_def]>>
    CONJ_TAC >- (
      match_mp_tac set_tids_subset_type_name_subst>>
      fs[set_tids_tenv_def])>>
    reverse CONJ_TAC>- (
      fs[remap_tenv_def]>>
      dep_rewrite.DEP_REWRITE_TAC [ts_tid_rename_type_name_subst]
      >> fs[]
      \\ fs[tenv_equiv_def]
      \\ match_mp_tac type_name_subst_tenv_equiv
      \\ fs[])>>
    fs[remap_tenv_def,tenv_equiv_def]>>
    metis_tac[check_type_names_ts_tid_rename,
              check_type_names_tenv_equiv,
              ts_tid_rename_type_name_subst])
  >- ( (* Dexn *)
    simp[set_tids_tenv_def]>>
    simp[Once type_d_canon_cases, prim_tids_def,remap_tenv_def,nsSing_def,nsMap_def]>>
    CONJ_TAC >- (
      fs[EVERY_MAP,EVERY_MEM]>>rw[]
      >- (match_mp_tac set_tids_subset_type_name_subst>>fs[set_tids_tenv_def])>>
      fs[prim_tids_def,prim_type_nums_def])>>
    CONJ_TAC >- fs[prim_tids_def,prim_type_nums_def]>>
    conj_asm1_tac >- (
      fs[EVERY_MEM, tenv_equiv_def]
      \\ imp_res_tac check_type_names_tenv_equiv
      \\ fs[remap_tenv_def, GSYM check_type_names_ts_tid_rename] )
    \\ qmatch_goalsub_abbrev_tac`tenv_equiv t1 t2`
    \\ `t1 = t2 ` suffices_by rw[]
    \\ rw[Abbr`t1`,Abbr`t2`]
    \\ fs[MAP_MAP_o, MAP_EQ_f, ts_tid_rename_type_name_subst,
         remap_tenv_def, tenv_equiv_def,
         type_name_subst_tenv_equiv, EVERY_MEM]
    \\ fs[good_remap_def, prim_type_nums_def])
  >- ( (* Dmod *)
    first_x_assum drule>>
    rpt (disch_then drule) >> rw[]>>
    qexists_tac`g`>>fs[]>>
    simp[Once type_d_canon_cases, PULL_EXISTS]>>
    goal_assum(first_assum o mp_then Any mp_tac) >>
    CONJ_TAC >- fs[tenvLift_def,set_tids_tenv_def]>>
    drule (GEN_ALL tenv_equiv_tenvLift)
    \\ disch_then(qspec_then`mn`mp_tac)
    \\ fs[remap_tenv_def,tenvLift_def,nsLift_nsMap])
  >- ( (* Dlocal *)
    last_x_assum drule>> fs[]>>
    disch_then drule>> simp[] >>
    disch_then drule>> rw[] >>
    simp[Once type_d_canon_cases]>>
    first_x_assum (qspecl_then
      [`tids ∪ ids`,`extend_bij f g ids n`,`CARD ids + n`] mp_tac)>>
    simp[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM]
    \\ simp[AND_IMP_INTRO]
    \\ impl_tac >- (
      fs[good_remap_extend_bij,prim_tids_def,prim_type_nums_def]>>
      rfs[DISJOINT_SYM]>>
      CONJ_TAC>-(
        match_mp_tac set_tids_tenv_extend_dec_tenv>>fs[]>>
        match_mp_tac (GEN_ALL set_tids_tenv_mono)>>
        asm_exists_tac>>fs[])>>
      match_mp_tac BIJ_extend_bij>>fs[DISJOINT_SYM])>>
    simp[PULL_EXISTS] >>
    disch_then(qspec_then`extend_dec_tenv mapped_tenv' mapped_tenv`mp_tac)
    \\ impl_tac >- (
      fs[tenv_equiv_def,remap_tenv_extend_dec_tenv]
      \\ fs[extend_dec_tenv_def]
      \\ DEP_REWRITE_TAC[nsAll2_nsAppend]
      \\ fs[]
      \\ fs[nsAll2_def,remap_tenv_def,nsSub_def,nsLookup_nsMap,nsLookupMod_nsMap,
            PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
      \\ fs[set_tids_tenv_def, set_tids_subset_def, nsAll_def, FORALL_PROD]
      \\ rw[] \\ res_tac \\ rw[]
      \\ fs[ts_tid_rename_eq_f, extend_bij_def, SUBSET_DEF, IN_DISJOINT,
            MAP_EQ_f, EVERY_MEM]
      \\ metis_tac[] )
    \\ rw[]>>
    qexists_tac `(extend_bij g g' (*ids*) ids' (CARD ids))`>>
    rw[] >>
    goal_assum(first_assum o mp_then Any mp_tac) >>
    fs[UNION_ASSOC, DISJOINT_CARD_UNION] \\
    goal_assum(first_assum o mp_then Any mp_tac) >>
    fs [BIJ_extend_bij, prim_tids_def,prim_type_nums_def,
        remap_tenv_extend_dec_tenv, extend_bij_compose]
  )
  >- simp[set_tids_tenv_def,Once type_d_canon_cases,remap_tenv_def, prim_tids_def]
  >> (*type_ds *)
  last_x_assum drule>> fs[]>>
  disch_then drule>> simp[] >>
  disch_then drule>> rw[] >>
  simp[Once type_d_canon_cases]>>
  first_x_assum (qspecl_then
    [`tids ∪ ids`,`extend_bij f g ids n`,`CARD ids + n`] mp_tac)>>
  simp[GSYM AND_IMP_INTRO, RIGHT_FORALL_IMP_THM]
  \\ simp[AND_IMP_INTRO]
  \\ impl_tac >- (
    fs[good_remap_extend_bij,prim_tids_def,prim_type_nums_def]>>
    rfs[DISJOINT_SYM]>>
    CONJ_TAC>-(
      match_mp_tac set_tids_tenv_extend_dec_tenv>>fs[]>>
      match_mp_tac (GEN_ALL set_tids_tenv_mono)>>
      asm_exists_tac>>fs[])>>
    match_mp_tac BIJ_extend_bij>>fs[DISJOINT_SYM])>>
  simp[PULL_EXISTS] >>
  disch_then(qspec_then`extend_dec_tenv mapped_tenv' mapped_tenv`mp_tac)
  \\ impl_tac >- (
    fs[tenv_equiv_def,remap_tenv_extend_dec_tenv]
    \\ fs[extend_dec_tenv_def]
    \\ DEP_REWRITE_TAC[nsAll2_nsAppend]
    \\ fs[]
    \\ fs[nsAll2_def,remap_tenv_def,nsSub_def,nsLookup_nsMap,nsLookupMod_nsMap,
          PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
    \\ fs[set_tids_tenv_def, set_tids_subset_def, nsAll_def, FORALL_PROD]
    \\ rw[] \\ res_tac \\ rw[]
    \\ fs[ts_tid_rename_eq_f, extend_bij_def, SUBSET_DEF, IN_DISJOINT,
          MAP_EQ_f, EVERY_MEM]
    \\ metis_tac[] )
  \\ rw[]>>
  qexists_tac `extend_bij g g' (*ids*) ids' (CARD ids)`>>
  rw[] >>
  goal_assum(first_assum o mp_then Any mp_tac) >>
  fs[UNION_ASSOC, DISJOINT_CARD_UNION] \\
  goal_assum(first_assum o mp_then Any mp_tac) >>
  rw[]
  >- (
    match_mp_tac set_tids_tenv_extend_dec_tenv>>fs[]>>
    match_mp_tac (GEN_ALL set_tids_tenv_mono)>>
    qpat_x_assum`_ _ tenv` assume_tac>>
    asm_exists_tac>>fs[SUBSET_DEF])
  >- fs[prim_tids_def,prim_type_nums_def]
  >- (match_mp_tac BIJ_extend_bij>> fs[])
  >>
  simp[remap_tenv_extend_dec_tenv]
  \\ fs[extend_bij_compose]
  \\ fs[extend_dec_tenv_def,tenv_equiv_def]
  \\ DEP_REWRITE_TAC[nsAll2_nsAppend] \\ fs[]
  \\ fs[nsAll2_def,remap_tenv_def,nsSub_def,nsLookup_nsMap,nsLookupMod_nsMap,
        PULL_EXISTS, FORALL_PROD, EXISTS_PROD]
  \\ fs[set_tids_tenv_def, set_tids_subset_def, nsAll_def, FORALL_PROD]
  \\ rw[] \\ res_tac \\ rw[]
  \\ fs[ts_tid_rename_eq_f, extend_bij_def, SUBSET_DEF, IN_DISJOINT,
        MAP_EQ_f, EVERY_MEM]
  \\ metis_tac[]
QED

(* n.b. proof almost entirely copied from type_d_tenv_ok_helper *)
Theorem type_d_canon_tenv_ok:
  (∀check tenv d tdecs tenv'.
   type_d_canon check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv') ∧
  (∀check tenv d tdecs tenv'.
   type_ds_canon check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv')
Proof
 ho_match_mp_tac type_d_canon_ind >>
 rw [tenv_ctor_ok_def, tenvLift_def]
 >- (
   fs [tenv_ok_def] >>
   drule (CONJUNCT1 type_p_freevars)
   >> rw [tenv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> fs [EVERY_MEM]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> pairarg_tac
   >> fs [tenv_add_tvs_def, MEM_MAP]
   >> pairarg_tac
   >> fs []
   >> rw []
   >> metis_tac [SND])
 >- (
   fs [tenv_ok_def] >>
   drule (CONJUNCT1 type_p_freevars)
   >> rw [tenv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> fs [EVERY_MEM]
   >> rw []
   >> pairarg_tac
   >> fs []
   >> pairarg_tac
   >> fs [tenv_add_tvs_def, MEM_MAP]
   >> pairarg_tac
   >> fs []
   >> rw []
   >> metis_tac [SND])
 >- (
   fs [tenv_ok_def] >>
   rw [tenv_val_ok_def]
   >> irule nsAll_alist_to_ns
   >> simp [tenv_add_tvs_def, EVERY_MAP]
   >> drule (List.nth (CONJUNCTS type_e_freevars, 2))
   >> simp [tenv_val_exp_ok_def, EVERY_MAP, LAMBDA_PROD]
   >> disch_then irule
   >> irule tenv_val_exp_ok_bvl_funs
   >> simp [tenv_val_exp_ok_def]
   >> metis_tac [])
 >- (
   fs [tenv_ok_def, tenv_abbrev_ok_def] >>
   rw []
   >- (
     irule check_ctor_tenv_ok >>
     rw []
     >> simp [tenv_abbrev_ok_def]
     >> irule nsAll_nsAppend
     >> simp []
     >> irule nsAll_alist_to_ns
     >> simp [MAP2_MAP, EVERY_MAP, EVERY_MEM, MEM_MAP]
     >> rw []
     >> rpt (pairarg_tac >> fs [])
     >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM])
   >- (
     irule nsAll_alist_to_ns
     >> simp [MAP2_MAP, EVERY_MAP, EVERY_MEM, MEM_MAP]
     >> rw []
     >> rpt (pairarg_tac >> fs [])
     >> rw [check_freevars_def, EVERY_MAP, EVERY_MEM]))
 >- (
   fs [tenv_ok_def, tenv_abbrev_ok_def] >>
   irule check_freevars_type_name_subst
   >> simp [tenv_abbrev_ok_def])
 >- (
   fs [tenv_ok_def, tenv_ctor_ok_def] >>
   fs [EVERY_MAP, EVERY_MEM]
   >> rw []
   >> irule check_freevars_type_name_subst
   >> simp [tenv_abbrev_ok_def])
 >- fs [tenv_ok_def, tenv_val_ok_def, tenv_ctor_ok_def, tenv_abbrev_ok_def]
 >- metis_tac [extend_dec_tenv_ok]
 >- metis_tac [extend_dec_tenv_ok]
QED

val _ = export_theory();
