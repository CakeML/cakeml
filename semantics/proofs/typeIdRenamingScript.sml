(*
  Theorems about switching type identifiers used in checking expressions and
  definitions.
*)

open preamble
open libTheory astTheory namespaceTheory typeSystemTheory typeSoundInvariantsTheory terminationTheory;
open astPropsTheory;
open namespacePropsTheory;
open typeSysPropsTheory;

val _ = new_theory "typeIdRenaming";

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

(* Rename (type_system) type identifiers with a function *)
Definition ts_tid_rename_def:
  (ts_tid_rename f (Tapp ts tn) = Tapp (MAP (ts_tid_rename f) ts) (f tn)) ∧
  (ts_tid_rename f t = t)
Termination
  WF_REL_TAC `measure (λ(_,y). t_size y)` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac
End

val ts_tid_rename_ind = theorem"ts_tid_rename_ind";

val t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`
  |> curry save_thm "t_ind";

Theorem ts_tid_rename_I[simp]:
  ts_tid_rename I = I
Proof
  simp[FUN_EQ_THM]
  \\ ho_match_mp_tac t_ind
  \\ rw[ts_tid_rename_def, MAP_EQ_ID, EVERY_MEM]
QED

(* The remapping must be identity on these numbers *)
Definition good_remap_def:
  good_remap f ⇔
  MAP f (Tlist_num :: (Tbool_num :: prim_type_nums)) =
    Tlist_num :: (Tbool_num :: prim_type_nums)
End

Definition remap_tenvE_def:
  (remap_tenvE f Empty = Empty) ∧
  (remap_tenvE f (Bind_tvar n e) = Bind_tvar n (remap_tenvE f e)) ∧
  (remap_tenvE f (Bind_name s n t e) = Bind_name s n (ts_tid_rename f t) (remap_tenvE f e))
End

Definition remap_tenv_def:
  remap_tenv f tenv =
  <|
    t := nsMap (λ(ls,t). (ls, ts_tid_rename f t)) tenv.t;
    c := nsMap (λ(ls,ts,tid). (ls, MAP (ts_tid_rename f) ts, f tid)) tenv.c;
    v := nsMap (λ(n,t). (n,ts_tid_rename f t)) tenv.v;
    s := tenv.s (* TODO: fix *)
   |>
End

Theorem remap_tenv_I[simp]:
  remap_tenv I = I
Proof
  rw[FUN_EQ_THM, remap_tenv_def, type_env_component_equality]
  \\ cheat
  \\ qmatch_goalsub_abbrev_tac`nsMap I'`
  \\ `I' = I` by simp[Abbr`I'`, UNCURRY, FUN_EQ_THM]
  \\ rw[]
QED

Theorem check_freevars_ts_tid_rename:
  ∀ts ls t.
  check_freevars ts ls (ts_tid_rename f t) ⇔
  check_freevars ts ls t
Proof
  ho_match_mp_tac check_freevars_ind>>
  fs[ts_tid_rename_def,check_freevars_def,EVERY_MAP,EVERY_MEM]
QED

Theorem remap_tenvE_bind_var_list:
  ∀n env tenvE.
  remap_tenvE f (bind_var_list n env tenvE) =
  bind_var_list n (MAP (λ(n,t). (n, ts_tid_rename f t)) env) (remap_tenvE f tenvE)
Proof
  ho_match_mp_tac bind_var_list_ind>>
  fs[bind_var_list_def,remap_tenvE_def]>>
  rw[]
QED

Theorem check_type_names_ts_tid_rename:
  ∀tenvt t.
  check_type_names tenvt t <=>
  check_type_names (nsMap (λ(ls,t). (ls,ts_tid_rename f t)) tenvt) t
Proof
  ho_match_mp_tac check_type_names_ind>>rw[check_type_names_def]>>
  fs[EVERY_MEM,nsLookup_nsMap]>>
  Cases_on`nsLookup tenvt tn`>>fs[]>>
  pairarg_tac>>fs[]
QED

Theorem ts_tid_rename_type_subst:
  ∀s t f.
  ts_tid_rename f (type_subst s t) =
  type_subst (ts_tid_rename f o_f s) (ts_tid_rename f t)
Proof
  ho_match_mp_tac type_subst_ind>>
  rw[type_subst_def,ts_tid_rename_def]
  >- (
    TOP_CASE_TAC>>fs[FLOOKUP_o_f,ts_tid_rename_def])
  >>
    fs[MAP_MAP_o,MAP_EQ_f]
QED

Theorem ts_tid_rename_type_name_subst:
  ∀tenvt t f tenv.
  good_remap f ∧
  check_type_names tenvt t ⇒
  ts_tid_rename f (type_name_subst tenvt t) =
  type_name_subst (nsMap (λ(ls,t). (ls,ts_tid_rename f t)) tenvt) t
Proof
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
    metis_tac[EL_MEM])
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

Theorem ts_tid_rename_deBruijn_subst:
  ∀n targs t.
  ts_tid_rename f (deBruijn_subst n targs t) =
  deBruijn_subst n (MAP (ts_tid_rename f) targs) (ts_tid_rename f t)
Proof
  ho_match_mp_tac deBruijn_subst_ind>>rw[]>>
  rw[ts_tid_rename_def,deBruijn_subst_def]>>
  fs[EL_MAP,MAP_MAP_o]>>
  fs[MAP_EQ_f]
QED

Theorem num_tvs_remap_tenvE:
  ∀tenvE. num_tvs (remap_tenvE f tenvE) = num_tvs tenvE
Proof
  Induct>>fs[remap_tenvE_def]
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

Theorem deBruijn_inc_ts_tid_rename:
  ∀skip n t.
  ts_tid_rename f (deBruijn_inc skip n t) =
  deBruijn_inc skip n (ts_tid_rename f t)
Proof
  ho_match_mp_tac deBruijn_inc_ind>>
  rw[deBruijn_inc_def,ts_tid_rename_def,MAP_MAP_o]>>
  fs[MAP_EQ_f]
QED

Theorem lookup_varE_remap_tenvE:
  ∀n tenvE.
  lookup_varE n (remap_tenvE f tenvE)
  = OPTION_MAP (λid,t. (id, ts_tid_rename f t)) (lookup_varE n tenvE)
Proof
  fs[lookup_varE_def]>>Cases>>fs[]>>
  qabbrev_tac`n=0n`>>
  pop_assum kall_tac>>qid_spec_tac`n`>>
  Induct_on`tenvE`>>fs[remap_tenvE_def,tveLookup_def]>>rw[]>>
  fs[deBruijn_inc_ts_tid_rename]
QED

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

(* All type ids in a type belonging to a set *)
Definition set_tids_def:
  (set_tids (Tapp ts tn) = tn INSERT (BIGUNION (set (MAP set_tids ts)))) ∧
  (set_tids _ = {})
Termination
  WF_REL_TAC `measure t_size` >>
  rw [] >>
  induct_on `ts` >>
  rw [t_size_def] >>
  res_tac >>
  decide_tac
End

val set_tids_ind = theorem"set_tids_ind";

Definition set_tids_subset_def:
  set_tids_subset tids t <=> set_tids t ⊆ tids
End

(* all the tids used in a tenv *)
Definition set_tids_tenv_def:
  set_tids_tenv tids tenv ⇔
  nsAll (λi (ls,t). set_tids_subset tids t) tenv.t ∧
  nsAll (λi (ls,ts,tid). EVERY (λt. set_tids_subset tids t) ts ∧ tid ∈ tids) tenv.c ∧
  nsAll (λi (n,t). set_tids_subset tids t) tenv.v
End

Definition sing_renum_def:
  sing_renum m n = λx. if x = m then n else x
End

Theorem sing_renum_NOT_tscheme_inst:
  ∀t.
  m ∈ set_tids t ∧
  m ≠ n ⇒
  ts_tid_rename (sing_renum m n) t ≠ t ∧
  ∀tvs tvs'.
  ¬tscheme_inst (tvs,ts_tid_rename (sing_renum m n) t) (tvs',t) ∧
  ¬tscheme_inst (tvs',t) (tvs,ts_tid_rename (sing_renum m n) t)
Proof
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
    \\ metis_tac[])
QED

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

Definition prim_tids_def:
  prim_tids contain tids ⇔
    EVERY (\x. x ∈ tids ⇔ contain) (Tlist_num::Tbool_num::prim_type_nums)
End

Theorem type_e_ts_tid_rename_sing_renum:
  m ∉ tids ∧ prim_tids T tids ∧
  type_e tenv tenvE e t ∧
  set_tids_tenv tids tenv
  ⇒
  type_e tenv (remap_tenvE (sing_renum m n) tenvE) e (ts_tid_rename (sing_renum m n) t)
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

Theorem type_p_ts_tid_rename_sing_renum:
  m ∉ tids ∧ prim_tids T tids ∧
  type_p tvs tenv p t bindings ∧
  set_tids_tenv tids tenv
  ⇒
  type_p tvs tenv p (ts_tid_rename (sing_renum m n) t)
  (MAP (λ(nn,t). (nn,ts_tid_rename (sing_renum m n) t)) bindings)
Proof
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
  metis_tac[type_p_tenv_equiv]
QED

Theorem type_pe_bindings_tids:
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
  ∀p_1 p_2. MEM (p_1,p_2) bindings ⇒ set_tids_subset tids p_2
Proof
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
  metis_tac[sing_renum_NOT_tscheme_inst]
QED

  (*
Theorem type_d_ts_tid_rename
 `good_remap f ⇒
  (!ec tenv d tids tenv'.
   type_d ec tenv d tids tenv' ⇒
   type_d ec (remap_tenv f tenv) d (IMAGE f tids) (remap_tenv f tenv')) ∧
  (!ec tenv ds tids tenv'.
   type_ds ec tenv ds tids tenv' ⇒
   type_ds ec (remap_tenv f tenv) ds (IMAGE f tids) (remap_tenv f tenv'))`
 (

  strip_tac >>
  ho_match_mp_tac type_d_ind >>
  simp [CONJUNCT1 type_d_cases] >> rpt conj_tac
  >- (
    rw [] >> disj1_tac >>

    qexists_tac `tvs` >> qexists_tac `ts_tid_rename f t` >>
    qexists_tac `MAP (λ(n,t). (n,ts_tid_rename f t)) bindings` >>
    rw []
    >- simp [remap_tenv_def, tenv_add_tvs_def, MAP_MAP_o, combinTheory.o_DEF,
             LAMBDA_PROD]
    >- metis_tac [type_p_ts_tid_rename]
    >- (
      imp_res_tac type_e_ts_tid_rename >>
      fs [remap_tenvE_def, bind_tvar_def] >>
      CASE_TAC >>
      fs [remap_tenvE_def, bind_tvar_def])
      *)

val _ = export_theory();
