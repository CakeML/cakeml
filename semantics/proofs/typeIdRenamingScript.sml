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

val t_ind = t_induction
  |> Q.SPECL[`P`,`EVERY P`]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN`P`
  |> curry save_thm "t_ind";

Theorem ts_tid_rename_I[simp]
  `ts_tid_rename I = I`
  (simp[FUN_EQ_THM]
  \\ ho_match_mp_tac t_ind
  \\ rw[ts_tid_rename_def, MAP_EQ_ID, EVERY_MEM]);

(* The remapping must be identity on these numbers *)
val good_remap_def = Define`
  good_remap f ⇔
  MAP f (Tlist_num :: (Tbool_num :: prim_type_nums)) =
    Tlist_num :: (Tbool_num :: prim_type_nums)`

val remap_tenvE_def = Define`
  (remap_tenvE f Empty = Empty) ∧
  (remap_tenvE f (Bind_tvar n e) = Bind_tvar n (remap_tenvE f e)) ∧
  (remap_tenvE f (Bind_name s n t e) = Bind_name s n (ts_tid_rename f t) (remap_tenvE f e))`

val remap_tenv_def = Define`
  remap_tenv f tenv =
  <|
    t := nsMap (λ(ls,t). (ls, ts_tid_rename f t)) tenv.t;
    c := nsMap (λ(ls,ts,tid). (ls, MAP (ts_tid_rename f) ts, f tid)) tenv.c;
    v := nsMap (λ(n,t). (n,ts_tid_rename f t)) tenv.v
   |>`

Theorem remap_tenv_I[simp]
  `remap_tenv I = I`
  (rw[FUN_EQ_THM, remap_tenv_def, type_env_component_equality]
  \\ cheat
  \\ qmatch_goalsub_abbrev_tac`nsMap I'`
  \\ `I' = I` by simp[Abbr`I'`, UNCURRY, FUN_EQ_THM]
  \\ rw[]);


Theorem check_freevars_ts_tid_rename
 `∀ts ls t.
  check_freevars ts ls (ts_tid_rename f t) ⇔
  check_freevars ts ls t`
 (ho_match_mp_tac check_freevars_ind>>
  fs[ts_tid_rename_def,check_freevars_def,EVERY_MAP,EVERY_MEM]);

Theorem remap_tenvE_bind_var_list
 `∀n env tenvE.
  remap_tenvE f (bind_var_list n env tenvE) =
  bind_var_list n (MAP (λ(n,t). (n, ts_tid_rename f t)) env) (remap_tenvE f tenvE)`
 (ho_match_mp_tac bind_var_list_ind>>
  fs[bind_var_list_def,remap_tenvE_def]>>
  rw[]);

Theorem check_type_names_ts_tid_rename
 `∀tenvt t.
  check_type_names tenvt t <=>
  check_type_names (nsMap (λ(ls,t). (ls,ts_tid_rename f t)) tenvt) t`
 (ho_match_mp_tac check_type_names_ind>>rw[check_type_names_def]>>
  fs[EVERY_MEM,nsLookup_nsMap]>>
  Cases_on`nsLookup tenvt tn`>>fs[]>>
  pairarg_tac>>fs[]);

Theorem ts_tid_rename_type_subst
 `∀s t f.
  ts_tid_rename f (type_subst s t) =
  type_subst (ts_tid_rename f o_f s) (ts_tid_rename f t)`
 (ho_match_mp_tac type_subst_ind>>
  rw[type_subst_def,ts_tid_rename_def]
  >- (
    TOP_CASE_TAC>>fs[FLOOKUP_o_f,ts_tid_rename_def])
  >>
    fs[MAP_MAP_o,MAP_EQ_f]);

Theorem ts_tid_rename_type_name_subst
 `∀tenvt t f tenv.
  good_remap f ∧
  check_type_names tenvt t ⇒
  ts_tid_rename f (type_name_subst tenvt t) =
  type_name_subst (nsMap (λ(ls,t). (ls,ts_tid_rename f t)) tenvt) t`
 (ho_match_mp_tac type_name_subst_ind>>rw[]>>
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

Theorem type_p_ts_tid_rename `
  good_remap f ⇒
  (∀tvs tenv p t bindings.
  type_p tvs tenv p t bindings ⇒
  type_p tvs (remap_tenv f tenv) p (ts_tid_rename f t)
    (MAP (λn,t. (n,ts_tid_rename f t)) bindings)) ∧
  (∀tvs tenv ps ts bindings.
  type_ps tvs tenv ps ts bindings ⇒
  type_ps tvs (remap_tenv f tenv) ps (MAP (ts_tid_rename f) ts)
    (MAP (λn,t. (n,ts_tid_rename f t)) bindings))`
  (strip_tac>>
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

Theorem ts_tid_rename_deBruijn_subst
 `∀n targs t.
  ts_tid_rename f (deBruijn_subst n targs t) =
  deBruijn_subst n (MAP (ts_tid_rename f) targs) (ts_tid_rename f t)`
 (ho_match_mp_tac deBruijn_subst_ind>>rw[]>>
  rw[ts_tid_rename_def,deBruijn_subst_def]>>
  fs[EL_MAP,MAP_MAP_o]>>
  fs[MAP_EQ_f]);

Theorem num_tvs_remap_tenvE
 `∀tenvE. num_tvs (remap_tenvE f tenvE) = num_tvs tenvE`
 (Induct>>fs[remap_tenvE_def]);

Theorem type_op_ts_tid_rename `
  good_remap f ⇒
  ∀op ts t.
  type_op op ts t ⇒
  type_op op (MAP (ts_tid_rename f) ts) (ts_tid_rename f t)`
  (rw[]>>
  fs[typeSysPropsTheory.type_op_cases,ts_tid_rename_def]>>
  fs[good_remap_def,prim_type_nums_def]);

Theorem deBruijn_inc_ts_tid_rename
 `∀skip n t.
  ts_tid_rename f (deBruijn_inc skip n t) =
  deBruijn_inc skip n (ts_tid_rename f t)`
 (ho_match_mp_tac deBruijn_inc_ind>>
  rw[deBruijn_inc_def,ts_tid_rename_def,MAP_MAP_o]>>
  fs[MAP_EQ_f]);

Theorem lookup_varE_remap_tenvE
 `∀n tenvE.
  lookup_varE n (remap_tenvE f tenvE)
  = OPTION_MAP (λid,t. (id, ts_tid_rename f t)) (lookup_varE n tenvE)`
 (fs[lookup_varE_def]>>Cases>>fs[]>>
  qabbrev_tac`n=0n`>>
  pop_assum kall_tac>>qid_spec_tac`n`>>
  Induct_on`tenvE`>>fs[remap_tenvE_def,tveLookup_def]>>rw[]>>
  fs[deBruijn_inc_ts_tid_rename]);

Theorem type_e_ts_tid_rename `
  good_remap f ⇒
  (∀tenv tenvE e t.
    type_e tenv tenvE e t ⇒
    type_e (remap_tenv f tenv) (remap_tenvE f tenvE) e (ts_tid_rename f t)) ∧
  (∀tenv tenvE es ts.
    type_es tenv tenvE es ts ⇒
    type_es (remap_tenv f tenv) (remap_tenvE f tenvE) es (MAP (ts_tid_rename f) ts)) ∧
  (∀tenv tenvE funs env.
    type_funs tenv tenvE funs env ⇒
    type_funs (remap_tenv f tenv) (remap_tenvE f tenvE) funs (MAP (λ(n,t). (n, ts_tid_rename f t)) env))`
  (strip_tac>>
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

val _ = export_theory();
