(*
  Defines the syntax and semantics of CNF / SCPOG
*)
Theory cnf_scpogSem
Ancestors
  misc
Libs
  preamble

(* Num-based CNF semantics with 0 treated specially *)
Type assignment = ``:num -> bool``;

Definition var_lit_def:
  var_lit l = Num (ABS l)
End

Theorem var_lit_num[simp]:
  var_lit (&n) = n
Proof
  rw[var_lit_def]
QED

Theorem var_lit_int[simp]:
  n > 0 ⇒
  &var_lit n = n
Proof
  rw[var_lit_def]>>
  intLib.ARITH_TAC
QED

Definition match_lit_def:
  match_lit l b =
  if l > 0i then b else ¬b
End

Definition sat_lit_def:
  sat_lit (w:assignment) l ⇔
  match_lit l (w (var_lit l))
End

Theorem sat_lit_neg[simp]:
  l ≠ 0 ⇒
  sat_lit w (-l) =
  ¬sat_lit w l
Proof
  rw[sat_lit_def,match_lit_def,var_lit_def]>>
  `F` by intLib.ARITH_TAC
QED

Theorem sat_lit_num[simp]:
  v ≠ 0 ⇒
  sat_lit w (&v) = w v
Proof
  rw[sat_lit_def,match_lit_def,var_lit_def]>>
  `F` by intLib.ARITH_TAC
QED

Theorem sat_lit_eq:
  w (var_lit e) = w' (var_lit e)
  ⇒
  (sat_lit w e = sat_lit w' e)
Proof
  rw[sat_lit_def]
QED

Definition sat_clause_def:
  sat_clause w C ⇔
  (∃l. l ∈ set C ∧ sat_lit w l ∧ l ≠ 0)
End

Theorem sat_clause_sing[simp]:
  sat_clause w [e] =
    (e ≠ 0 ∧ sat_lit w e)
Proof
  rw[sat_clause_def]>>
  metis_tac[]
QED

Theorem sat_clause_cons:
  x ≠ 0 ⇒
  (sat_clause w (x::xs) ⇔
  (sat_lit w x ∨ sat_clause w xs))
Proof
  rw[sat_clause_def]>>
  metis_tac[]
QED

Definition sat_fml_def:
  sat_fml w f ⇔
  (∀C. C ∈ f ⇒ sat_clause w C)
End

Theorem sat_fml_INSERT[simp]:
  sat_fml w (C INSERT fml) =
  (sat_clause w C ∧ sat_fml w fml)
Proof
  rw[sat_fml_def]>>
  metis_tac[]
QED

Theorem sat_fml_UNION[simp]:
  sat_fml w (fml ∪ fml') =
  (sat_fml w fml ∧ sat_fml w fml')
Proof
  rw[sat_fml_def]>>
  metis_tac[]
QED

Theorem sat_fml_EMPTY[simp]:
  sat_fml w {}
Proof
  rw[sat_fml_def]
QED

Theorem sat_fml_SUBSET:
  fml' ⊆ fml ∧
  sat_fml w fml ⇒
  sat_fml w fml'
Proof
  rw[sat_fml_def,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem sat_fml_imp_DELETE:
  sat_fml w fml ⇒
  sat_fml w (fml DELETE C)
Proof
  rw[sat_fml_def]
QED

Definition vars_clause_def:
  vars_clause C = IMAGE var_lit (set C) DELETE 0n
End

Theorem vars_clause_cons[simp]:
  x ≠ 0 ⇒
  vars_clause (x::C) =
  var_lit x INSERT vars_clause C
Proof
  rw[vars_clause_def,EXTENSION]>>
  eq_tac>>rw[]
  >- (rw[var_lit_def]>>intLib.ARITH_TAC)
  >- metis_tac[]
  >- metis_tac[]
QED

Definition vars_fml_def:
  vars_fml fml = BIGUNION (IMAGE vars_clause fml)
End

Theorem vars_fml_INSERT[simp]:
  vars_fml (l INSERT fml) =
  vars_clause l ∪ vars_fml fml
Proof
  rw[vars_fml_def]
QED

Theorem vars_fml_UNION[simp]:
  vars_fml (fml ∪ fml') =
  vars_fml fml ∪ vars_fml fml'
Proof
  rw[vars_fml_def]
QED

Theorem vars_fml_SUBSET:
  x ⊆ y ⇒
  vars_fml x ⊆ vars_fml y
Proof
  rw[vars_fml_def]>>
  match_mp_tac SUBSET_BIGUNION>>
  simp[]
QED

(* This is the raw type for SCPOG nodes *)
Datatype:
  scpn =
  | Pro (int list)
  | Sum (int list)
  | Sko (int list)
End

(* An SCPOG is represented by an indexed list of nodes, where
  the index num is the node's "name" *)
Type scp = ``:(num # scpn) list``

(* Basic syntactic well-formedness condition for an SCP
  is defined wrt three sets:
  D - data variables
  Y - forget variables
  E - extension variables

  1. Pro/Sum nodes must point down the list (positively)
    or point to data literals.

  2. Names of each node must be extension variables

  3. Forget literals occur only in the Skolem nodes
*)
Definition is_data_ext_lit_def:
  is_data_ext_lit D ls l ⇔
    var_lit l ∈ D ∨
    var_lit l ∈ set (MAP FST ls) ∧ l > 0
End

Definition dir_scp_def:
  (dir_scp D Y E [] = T) ∧
  (dir_scp D Y E ((v,n)::ns) =
    (v ∈ E ∧
    dir_scp D Y E ns ∧
    case n of
      Pro ls =>
        EVERY (is_data_ext_lit D ns) ls
    | Sum ls =>
        EVERY (is_data_ext_lit D ns) ls
    | Sko ls => EVERY (λl. var_lit l ∈ Y) ls))
End

(*
  The semantics of an SCPOG is defined recursively from a root node.
  The flag "sko" controls whether the Skolem literals are in play or not.
*)
Definition sat_scp_def:
  (sat_scp sko (r:int) [] w = sat_lit w r) ∧
  (sat_scp sko r ((v,n)::ns) w =
    if v = var_lit r then
      match_lit r
        (case n of
          Pro ls => EVERY (λi. sat_scp sko i ns w) ls
        | Sum ls => EXISTS (λi. sat_scp sko i ns w) ls
        | Sko ls =>
          (sko ⇒ EVERY (λi. sat_scp sko i ns w) ls)
        )
    else
      sat_scp sko r ns w)
End

Definition vars_scp_def:
  (vars_scp sko (r:int) [] = {var_lit r}) ∧
  (vars_scp sko (r:int) ((v,n)::ns) =
    if v = var_lit r then
      (case n of
        Pro ls =>
          BIGUNION (IMAGE (λi. vars_scp sko i ns) (set ls))
      | Sum ls =>
          BIGUNION (IMAGE (λi. vars_scp sko i ns) (set ls))
      | Sko ls =>
        (if sko then
          BIGUNION (IMAGE (λi. vars_scp sko i ns) (set ls))
        else {}))
    else
      vars_scp sko r ns)
End

Definition all_disjoint_def:
  all_disjoint ls ⇔
  (∀i j.
    i < LENGTH ls ∧ j < LENGTH ls ∧ i ≠ j ⇒
    DISJOINT (EL i ls) (EL j ls))
End

(* We will define partitioning separately for products and sums and both
  controlled by a flag determining whether Skolem nodes are in play. *)

(* Decomposable products *)
Definition decomposable_scp_def:
  (decomposable_scp sko (r:int) [] = T) ∧
  (decomposable_scp sko (r:int) ((v,n)::ns) =
    if v = var_lit r then
      (case n of
        Pro ls =>
          all_disjoint (MAP (λi. vars_scp sko i ns) ls) ∧
          EVERY (λi. decomposable_scp sko i ns) ls
      | Sum ls =>
          EVERY (λi. decomposable_scp sko i ns) ls
      | Sko ls =>
          sko ⇒
            all_disjoint (MAP (λi. vars_scp sko i ns) ls) ∧
            EVERY (λi. decomposable_scp sko i ns) ls
      )
    else
      decomposable_scp sko r ns
  )
End

(* Deterministic sums *)
Definition deterministic_scp_def:
  (deterministic_scp sko (r:int) [] = T) ∧
  (deterministic_scp sko (r:int) ((v,n)::ns) =
    if v = var_lit r then
      (case n of
        Pro ls =>
          EVERY (λi. deterministic_scp sko i ns) ls
      | Sum ls =>
          all_disjoint (MAP (λi. sat_scp sko i ns) ls) ∧
          EVERY (λi. deterministic_scp sko i ns) ls
      | Sko ls =>
          (sko ⇒ EVERY (λi. deterministic_scp sko i ns) ls))
    else
      deterministic_scp sko r ns
  )
End

Theorem vars_scp_F_to_T:
  ∀ns r.
  vars_scp F r ns ⊆
  vars_scp T r ns
Proof
  Induct
  >-
    rw[vars_scp_def]>>
  Cases>>
  rw[vars_scp_def]>>
  TOP_CASE_TAC>>
  gvs[SUBSET_DEF]>>
  metis_tac[]
QED

Theorem all_disjoint_CONS:
  all_disjoint (x::ys) ⇔
  ((∀y. MEM y ys ⇒ DISJOINT x y) ∧
  all_disjoint ys)
Proof
  rw[all_disjoint_def]>>eq_tac>>rw[]
  >- (
    gvs[MEM_EL]>>
    first_x_assum(qspecl_then[`0`,`SUC n`] mp_tac)>>
    simp[])
  >- (
    first_x_assum(qspecl_then[`SUC i`,`SUC j`] mp_tac)>>
    simp[])>>
  rw[EL_CONS_IF]>>gvs[]
  >- (
    first_x_assum match_mp_tac>>
    simp[MEM_EL]>>
    Cases_on`j`>>fs[]>>
    metis_tac[])
  >- (
    simp[Once DISJOINT_SYM]>>
    first_x_assum match_mp_tac>>
    simp[MEM_EL]>>
    Cases_on`i`>>fs[]>>
    metis_tac[]) >>
  first_x_assum match_mp_tac>>
  simp[]>>
  Cases_on`i`>>Cases_on`j`>>gvs[]
QED

Theorem all_disjoint_APPEND:
  all_disjoint (xs ++ ys) ⇒
  all_disjoint xs ∧ all_disjoint ys
Proof
  rw[all_disjoint_def]>>
  gvs[EL_APPEND]
  >-
    (first_x_assum (qspecl_then [`i`,`j`] mp_tac)>> simp[])>>
  (first_x_assum (qspecl_then [`i + LENGTH xs`,`j + LENGTH xs`] mp_tac)>> simp[])
QED

Theorem all_disjoint_SUBSET:
  LIST_REL (λx y. y ⊆ x) xs ys ∧
  all_disjoint xs ⇒
  all_disjoint ys
Proof
  rw[all_disjoint_def,LIST_REL_EL_EQN]>>
  metis_tac[DISJOINT_SYM,DISJOINT_SUBSET]
QED

(* Skolem decomposable implies non-Skolem decomposable but not vice-versa *)
Theorem decomposable_scp_T_to_F:
  ∀ns r.
  decomposable_scp T r ns ⇒
  decomposable_scp F r ns
Proof
  Induct
  >-
    rw[decomposable_scp_def]>>
  Cases>>
  rw[decomposable_scp_def]>>
  gvs[AllCasePreds(),EVERY_MEM]>>
  drule_at Any all_disjoint_SUBSET>>
  disch_then irule>>
  simp[EVERY2_MAP,LIST_REL_EL_EQN]>>
  simp[vars_scp_F_to_T]
QED

Theorem deterministic_scp_ALOOKUP_NONE:
  ∀ns.
  ALOOKUP ns (var_lit n) = NONE ⇒
  deterministic_scp sko n ns
Proof
  Induct>-rw[deterministic_scp_def]>>
  Cases>>rw[deterministic_scp_def]
QED

Theorem dir_scp_MAP_FST:
  ∀D Y E ns.
  dir_scp D Y E ns ⇒
  set (MAP FST ns) ⊆ E
Proof
  ho_match_mp_tac dir_scp_ind>>
  rw[dir_scp_def]
QED

Definition agree_on_def:
  agree_on D w w' ⇔
  ∀x. x ∈ D ⇒ w x = w' x
End

Theorem agree_on_refl[simp]:
  agree_on D X X
Proof
  rw[agree_on_def]
QED

Theorem agree_on_sat_scp_F:
  agree_on D w w' ⇒
  ∀ns r.
  is_data_ext_lit D ns r ∧
  dir_scp D Y E ns ⇒
  (sat_scp F r ns w ⇔ sat_scp F r ns w')
Proof
  strip_tac>>
  Induct>>rw[sat_scp_def]
  >- (
    gvs[is_data_ext_lit_def,agree_on_def]>>
    rw[sat_lit_def])>>
  Cases_on`h`>>
  gvs[dir_scp_def]>>
  reverse (rw[sat_scp_def])
  >- (
    first_x_assum match_mp_tac>>
    gvs[is_data_ext_lit_def,dir_scp_def])>>
  TOP_CASE_TAC>>gvs[]
  >- (
    AP_TERM_TAC>>
    match_mp_tac EVERY_CONG>>simp[]>>
    gvs[EVERY_MEM])
  >- (
    AP_TERM_TAC>>
    match_mp_tac EXISTS_CONG>>simp[]>>
    gvs[EVERY_MEM])
QED

Theorem agree_on_sat_scp_T_to_F:
  D ∩ E = {} ⇒
  ∀ns r w.
  is_data_ext_lit D ns r ∧
  dir_scp D Y E ns ∧
  sat_scp T r ns w ⇒
  sat_scp F r ns w
Proof
  strip_tac>>
  Induct
  >- (
    rw[sat_scp_def]>>
    metis_tac[agree_on_refl])>>
  Cases>>
  rw[]>>
  reverse(gvs[sat_scp_def,AllCasePreds(),SF DNF_ss])
  >- (
    first_x_assum (irule_at Any)>>
    gvs[dir_scp_def,is_data_ext_lit_def] )>>
  rename1`match_lit rr`>>
  `rr > 0` by (
    gvs[dir_scp_def,is_data_ext_lit_def,EXTENSION]>>
    metis_tac[])>>
  gvs[match_lit_def,dir_scp_def,EVERY_MEM,EXISTS_MEM]>>
  metis_tac[]
QED

Theorem agree_on_SUBSET:
  agree_on s w w' ∧
  t ⊆ s ⇒
  agree_on t w w'
Proof
  rw[agree_on_def,SUBSET_DEF]
QED

Theorem sat_scp_vars_scp:
  ∀sko r ns w w'.
  agree_on (vars_scp sko r ns) w w' ⇒
  (sat_scp sko r ns w ⇔ sat_scp sko r ns w')
Proof
  ho_match_mp_tac sat_scp_ind>>
  rw[sat_scp_def,vars_scp_def]
  >-
    gvs[agree_on_def,sat_lit_def]>>
  TOP_CASE_TAC>>gvs[PULL_FORALL,AND_IMP_INTRO]
  >- (
    AP_TERM_TAC>>
    match_mp_tac EVERY_CONG>>
    rw[]>>
    first_x_assum match_mp_tac>>gvs[]>>
    irule agree_on_SUBSET>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]>>
    metis_tac[])
  >- (
    AP_TERM_TAC>>
    match_mp_tac EXISTS_CONG>>
    rw[]>>
    first_x_assum match_mp_tac>>gvs[]>>
    irule agree_on_SUBSET>>
    first_x_assum (irule_at Any)>>
    simp[]>>
    match_mp_tac SUBSET_BIGUNION_I>>
    simp[]>>metis_tac[])
  >- (
    Cases_on`sko`>>gvs[]>>
    AP_TERM_TAC>>
    match_mp_tac EVERY_CONG>>
    rw[]>>
    first_x_assum match_mp_tac>>gvs[]>>
    irule agree_on_SUBSET>>
    first_x_assum (irule_at Any)>>
    simp[SUBSET_DEF]>>
    metis_tac[])
QED

Theorem sat_scp_ALOOKUP_NONE:
  ∀ns.
  ALOOKUP ns (var_lit n) = NONE ⇒
  (sat_scp sko n ns w ⇔ sat_lit w n)
Proof
  Induct>-rw[sat_scp_def]>>
  Cases>>
  rw[sat_scp_def]
QED

(* quantifier alternation *)
Theorem agree_on_list_sat_scp_alternate:
  ∀ls.
  all_disjoint (MAP (λi. vars_scp sko i ns) ls) ∧
  (∀x. MEM x ls ⇒
    ∃w'. agree_on D w w' ∧ sat_scp sko x ns w') ⇒
  ∃w'.
    agree_on D w w' ∧
    (EVERY (λx. sat_scp sko x ns w') ls)
Proof
  Induct>>rw[EVERY_MEM]
  >-
    metis_tac[agree_on_refl]>>
  gvs[SF DNF_ss,all_disjoint_CONS,EVERY_MEM]>>
  rename1`sat_scp sko h ns w'`>>
  rename1`∀x. MEM x ls ⇒ sat_scp sko x ns w''`>>
  qabbrev_tac` ww =
    λx.
      if x ∈ D then w x
      else if x ∈ vars_scp sko h ns then w' x
      else w'' x`>>
  qexists_tac`ww`>>
  rw[]
  >- simp[agree_on_def,Abbr`ww`]
  >- (
    `agree_on (vars_scp sko h ns) w' ww` by (
      gvs[agree_on_def]>>rw[Abbr`ww`])>>
    metis_tac[sat_scp_vars_scp])
  >- (
    rename1`MEM x ls`>>
    `agree_on (vars_scp sko x ns) w'' ww` by (
      gvs[agree_on_def]>>rw[Abbr`ww`]>>
      gvs[MEM_MAP,SF DNF_ss]>>
      gvs[DISJOINT_DEF,EXTENSION]>>
      metis_tac[]
    )>>
    metis_tac[sat_scp_vars_scp]
  )
QED

Theorem agree_on_sat_scp_F_to_T:
  D ∩ E = {} ∧ D ∩ Y = {} ∧ Y ∩ E = {} ⇒
  ∀ns r w.
  is_data_ext_lit D ns r ∧
  dir_scp D Y E ns ∧
  decomposable_scp T r ns ∧
  sat_scp F r ns w ⇒
  ∃w'. agree_on D w w' ∧ sat_scp T r ns w'
Proof
  strip_tac>>
  Induct
  >- (
    rw[sat_scp_def]>>
    metis_tac[agree_on_refl])>>
  Cases>>
  rw[]>>
  reverse(gvs[sat_scp_def,AllCasePreds(),SF DNF_ss])
  >- (
    first_x_assum (irule_at Any)>>
    gvs[dir_scp_def,is_data_ext_lit_def,decomposable_scp_def])>>
  rename1`match_lit rr`>>
  `rr > 0` by (
    gvs[dir_scp_def,is_data_ext_lit_def,EXTENSION]>>
    metis_tac[])>>
  gvs[match_lit_def,dir_scp_def,decomposable_scp_def]
  >- (
    `∀x. MEM x ls ⇒
     ∃w'.
       agree_on D w w' ∧ sat_scp T x ns w'` by gvs[EVERY_MEM]>>
    match_mp_tac agree_on_list_sat_scp_alternate>>
    simp[])
  >- (
    gvs[EXISTS_MEM,EVERY_MEM]>>
    first_x_assum drule>>
    strip_tac>>
    first_x_assum drule_all>>
    metis_tac[])
  >- (
    rename1`EVERY _ ls`>>
    `∀x. MEM x ls ⇒
     ∃w'.
       agree_on D w w' ∧ sat_scp T x ns w'` by (
      rw[]>>
      gvs[EVERY_MEM]>>
      last_x_assum drule>>
      strip_tac>>
      rename1`MEM yy ls`>>
      qexists_tac`λy. if y = var_lit yy then yy > 0 else w y`>>
      CONJ_TAC >- (
         rw[agree_on_def] >>
         `y ∉ Y` by (gvs[EXTENSION]>>metis_tac[])>>
         IF_CASES_TAC>> gvs[])>>
      DEP_REWRITE_TAC[sat_scp_ALOOKUP_NONE]>>
      simp[sat_lit_def,match_lit_def]>>
      simp[ALOOKUP_NONE]>>
      drule dir_scp_MAP_FST>>
      gvs[EXTENSION,SUBSET_DEF,MEM_MAP]>>
      metis_tac[])>>
    match_mp_tac agree_on_list_sat_scp_alternate>>
    simp[]
  )
QED

(* Non-Skolem deterministic implies Skolem deterministic but not vice-versa*)
Theorem deterministic_scp_F_to_T:
  D ∩ E = {} ∧ Y ∩ E = {} ⇒
  ∀ns r.
  is_data_ext_lit D ns r ∧
  dir_scp D Y E ns ∧
  deterministic_scp F r ns ⇒
  deterministic_scp T r ns
Proof
  strip_tac>>
  Induct
  >-
    rw[deterministic_scp_def]>>
  Cases>>
  rw[]>>
  gvs[deterministic_scp_def]>>
  reverse (rw[])>>gvs[]
  >- (
    first_x_assum irule>>
    gvs[is_data_ext_lit_def,dir_scp_def])>>
  gvs[AllCasePreds(),EVERY_MEM,dir_scp_def,EVERY_MEM]
  >- (
    drule_at Any all_disjoint_SUBSET>>
    disch_then irule>>
    simp[LIST_REL_EL_EQN,EL_MAP,SUBSET_DEF]>>
    rw[IN_DEF]>>
    irule agree_on_sat_scp_T_to_F>>
    simp[]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[MEM_EL]>>
    metis_tac[])
  >- (
    rw[]>>irule deterministic_scp_ALOOKUP_NONE>>
    simp[ALOOKUP_NONE]>>
    drule dir_scp_MAP_FST>>
    rw[]>>
    last_x_assum drule>>
    gvs[EXTENSION,SUBSET_DEF,MEM_MAP]>>
    metis_tac[])
QED

(* Since we model assignments as functions num -> bool,
  The set of models is simply given by (num -> bool) -> bool
  Accordingly, the set of data models with respect to set D is the
  restriction onto set D *)
Definition models_def:
  models D ws = IMAGE (λw. D ∩ w) ws
End

