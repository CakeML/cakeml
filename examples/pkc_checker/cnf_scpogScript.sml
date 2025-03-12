(*
  Defines the syntax and semantics of CNF / POG and a proof checker
*)
open preamble miscTheory mlstringTheory mlintTheory mlvectorTheory sptreeTheory mergesortTheory;

(* force sptree priority *)
val _ = set_grammar_ancestry ["mlstring","mlvector","sptree","mergesort","misc"];

val _ = new_theory "cnf_scpog";

(* Num-based CNF semantics
  with 0 treated specially *)
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

(* Raw type for SCPOG nodes *)
Datatype:
  scpn =
  | Pro (int list)
  | Sum (int list)
  | Sko (int list)
End

(* An SCPOG is represented by an indexed list of nodes *)
Type scp = ``:(num # scpn) list``

(* Basic syntactic well-formedness condition for an SCP
  is defined wrt three sets:
  D - data variables
  P - projection variables
  E - extension variables

  1) Pro/Sum nodes must point down the list (positively)
    or point to data literals.

  2) Names of each node must be extension variables

  3) Project literals only in the Skolem nodes *)
Definition is_data_ext_lit_def:
  is_data_ext_lit D ls l ⇔
    var_lit l ∈ D ∨
    var_lit l ∈ set (MAP FST ls) ∧ l > 0
End

Definition dir_scp_def:
  (dir_scp D P E [] = T) ∧
  (dir_scp D P E ((v,n)::ns) =
    (v ∈ E ∧
    dir_scp D P E ns ∧
    case n of
      Pro ls =>
        EVERY (is_data_ext_lit D ns) ls
    | Sum ls =>
        EVERY (is_data_ext_lit D ns) ls
    | Sko ls => EVERY (λl. var_lit l ∈ P) ls))
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
  ∀D P E ns.
  dir_scp D P E ns ⇒
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
  dir_scp D P E ns ⇒
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
  dir_scp D P E ns ∧
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
  D ∩ E = {} ∧ D ∩ P = {} ∧ P ∩ E = {} ⇒
  ∀ns r w.
  is_data_ext_lit D ns r ∧
  dir_scp D P E ns ∧
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
         `y ∉ P` by (gvs[EXTENSION]>>metis_tac[])>>
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
  D ∩ E = {} ∧ P ∩ E = {} ⇒
  ∀ns r.
  is_data_ext_lit D ns r ∧
  dir_scp D P E ns ∧
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

(* Implementation *)
Type clause = ``:int list``;
Type hint = ``:num list``;
Type lit = ``:int``;
Type var = ``:num``;
Type id = ``:num``;

Datatype:
  scpstep =
  | Skip

  | Root lit

  | RupAdd bool id clause hint
    (* bool flag indicates whether it is structural *)

  | ArbDel (id list)

  | DeclPro id var (lit list)
  | DeclSum id var lit lit hint
  | DeclSko id var (lit list)
End

(* The scpog being constructed *)
Datatype:
  scpog_conf =
    <|
       Ev   : num_set;
         (* Extension variables and their var dependencies *)
       root : int option;
         (* The root literal *)
       scp  : scp;
         (* The SCPOG *)
    |>
End

(* The immutable problem configuration consisting of
  data variables, a max var limit nv, and max clauses nc. *)
Datatype:
  prob_conf =
    <| D : num_set option ; nv : num ; nc: num |>
End

Definition get_data_vars_def:
  get_data_vars pc =
  case pc.D of
    NONE => count (pc.nv+1)
  | SOME D => domain D
End

Definition is_data_var_def:
  is_data_var pc v =
  case pc.D of
    NONE => v ≤ pc.nv
  | SOME D => lookup v D ≠ NONE
End

(* l is a data literal or an extension variable *)
Definition is_data_ext_lit_run_def:
  is_data_ext_lit_run pc Ev l ⇔
    let v = var_lit l in
    is_data_var pc v ∨
    lookup v Ev ≠ NONE ∧ l > 0
End

Definition declare_root_def:
  declare_root sc l =
    case sc.root of
      NONE =>
        SOME (sc with root := SOME l)
    | SOME _ => NONE
End

Definition delete_literals_def:
  delete_literals (C:clause) (D:clause) =
  FILTER (λx. ¬MEM x D) C
End

(*
  We represent indexed formulas with a mapping
    num -> clause # tag
*)

(* RUP steps are constrained by the predicate *)
Definition is_rup_def:
  (is_rup is_struct fml [] (C:clause) = F) ∧
  (is_rup is_struct fml (i::is) C =
  case lookup i fml of
    NONE => F
  | SOME (c,tag) =>
    if is_struct ⇒ tag then
      case delete_literals c C of
        [] => T
      | [l] => is_rup is_struct fml is (-l :: C)
      | _ => F
    else F)
End

(* freshness wrt current configuration *)
Definition is_fresh_def:
  is_fresh pc sc v ⇔
  pc.nv < v ∧ lookup v sc.Ev = NONE
End

(* TODO: we can relax this to allow overrides *)
Definition insert_one_def:
  insert_one tag fml i c =
    case lookup i fml of
      NONE => SOME (insert i (c,tag) fml)
    | SOME _ => NONE
End

(* Clauses encoding the extension variable
  v <-> l_1 ∧ l_2 ∧ ... ∧ l_n *)
Definition mk_sko_def:
  mk_sko v (ls:int list) =
  let iv = (&v):int in
  MAP (\l. [-iv;l]) ls
End

Definition mk_pro_def:
  mk_pro v (ls:int list) =
  let iv = (&v):int in
  (iv::MAP (\l. -l) ls):: mk_sko v ls
End

Definition check_pro_def:
  check_pro pc sc v ls =
    (EVERY (is_data_ext_lit_run pc sc.Ev) ls ∧
    v ≠ 0n ∧ EVERY (λi. i ≠ 0i) ls ∧
    is_fresh pc sc v)
End

(*
Definition get_node_vars_def:
  get_node_vars Ev ls =
  MAP (λi.
    case lookup (var_lit i) Ev of
      NONE => (insert (var_lit i) () LN)
    | SOME vs => vs) ls
End

Definition big_union_def:
  big_union ts = FOLDL sptree$union LN ts
End

Definition mk_Ev_def:
  mk_Ev Ev v ls =
    insert v (big_union (get_node_vars Ev ls)) Ev
End

Definition big_disjoint_union_def:
  big_disjoint_union ts =
    FOLDL
    (\t i.
      case t of NONE => NONE
      | SOME tt =>
        if isEmpty (inter i tt) then
          SOME (union i tt)
        else NONE) (SOME LN) ts
End

Definition mk_Ev_disj_def:
  mk_Ev_disj Ev v ls =
    OPTION_MAP (\t. sptree$insert v t Ev)
    (big_disjoint_union (get_node_vars Ev ls))
End

Definition declare_pro_def:
  declare_pro pc sc (v:num) ls =
  if
    check_pro pc sc v ls
  then
    case mk_Ev_disj sc.Ev v ls of NONE => NONE
    | SOME Ev =>
    SOME (mk_pro v ls,
      (sc with
        <| scp := (v,Pro ls)::sc.scp;
           Ev := Ev|>))
  else
    NONE
End
*)

Definition declare_pro_def:
  declare_pro pc sc (v:num) ls =
  if
    check_pro pc sc v ls
  then
    SOME (mk_pro v ls,
      (sc with
        <| scp := (v,Pro ls)::sc.scp;
           Ev := insert v () sc.Ev|>))
  else
    NONE
End

Definition mk_sum_def:
  mk_sum v ls =
  let iv = (&v):int in
  (-iv::ls):: MAP (\l. [iv;-l]) ls
End

Definition check_sum_def:
  check_sum pc sc v ls =
    (EVERY (is_data_ext_lit_run pc sc.Ev) ls ∧
    v ≠ 0n ∧ EVERY (λi. i ≠ 0i) ls ∧
    is_fresh pc sc v)
End

Definition declare_sum_def:
  declare_sum pc sc (v:num) l1 l2 =
  if
    check_sum pc sc v [l1;l2]
  then
    SOME (mk_sum v [l1;l2] ,
      (sc with
        <| scp := (v,Sum [l1;l2])::sc.scp;
           Ev := insert v () sc.Ev|>))
  else
    NONE
End

Definition is_proj_lit_run_def:
  is_proj_lit_run pc l ⇔
  case pc.D of NONE => F
  | SOME D =>
    let v = var_lit l in
    lookup v D = NONE ∧ v ≤ pc.nv
End

Definition check_sko_def:
  check_sko pc sc v ls =
    (EVERY (is_proj_lit_run pc) ls ∧
    v ≠ 0n ∧ EVERY (λi. i ≠ 0i) ls ∧
    is_fresh pc sc v)
End

Definition declare_sko_def:
  declare_sko pc sc (v:num) ls =
  if
    check_sko pc sc v ls
  then
    SOME ([(&v):int],
      (sc with
        <| scp := (v,Sko ls)::sc.scp;
           Ev := insert v () sc.Ev|>))
  else
    NONE
End

Definition insert_list_def:
  (insert_list tag fml i [] = SOME fml) ∧
  (insert_list tag fml i (c::cs) =
  case insert_one tag fml i c of
    NONE => NONE
  | SOME fml' => insert_list tag fml' (i+1) cs)
End

(* Allow arb_delete only when clauses are non-Structural *)
Definition arb_delete_def:
  (arb_delete nc [] fml = SOME fml) ∧
  (arb_delete nc (i::is) fml =
    if i ≤ nc then NONE
    else
    case lookup i fml of
      NONE => NONE
    | SOME (c,tag) =>
      if tag then NONE
      else arb_delete nc is (delete i fml))
End

Definition check_scpstep_def:
  check_scpstep pc fml sc scpstep =
  case scpstep of
  | Skip => SOME (fml,sc)
  | Root l =>
      OPTION_MAP (λsc'. (fml,sc')) (declare_root sc l)
  | RupAdd b n C i0 =>
    if
      is_rup b fml i0 C ∧
      EVERY (λi. ¬is_fresh pc sc (var_lit i)) C
    then
      OPTION_MAP (λfml'. (fml',sc))
        (insert_one b fml n C)
    else NONE
  | ArbDel ls =>
    OPTION_MAP (λfml'. (fml',sc)) (arb_delete pc.nc ls fml)
  | DeclPro n v ls =>
    (case declare_pro pc sc v ls of
      SOME (cs,sc') =>
        OPTION_MAP (λfml'. (fml',sc'))
          (insert_list T fml n cs)
    | NONE => NONE)
  | DeclSum n v l1 l2 i0 =>
    if is_rup T fml i0 [-l1;-l2] then
      (case declare_sum pc sc v l1 l2 of
        SOME (cs,sc') =>
          OPTION_MAP (λfml'. (fml',sc'))
            (insert_list T fml n cs)
      | NONE => NONE)
    else NONE
  | DeclSko n v ls =>
    (case declare_sko pc sc v ls of
      SOME (cT,sc') =>
        OPTION_MAP (λfml'. (fml',sc'))
          (insert_one T fml n cT)
    | NONE => NONE)
End

(* Semantic proofs *)
Definition good_pc_def:
  good_pc pc ⇔ get_data_vars pc ⊆ count (pc.nv+1)
End

Definition extends_over_def:
  extends_over D f g ⇔
  ∀w.
    f w ⇒
    ∃w'.
      agree_on D w w' ∧ g w'
End

Theorem extends_over_refl[simp]:
  extends_over D X X
Proof
  rw[extends_over_def]>>
  first_x_assum (irule_at Any)>>
  simp[]
QED

Theorem extends_over_SUBSET:
  X ⊆ Y ⇒
  extends_over D X Y
Proof
  rw[extends_over_def]>>
  gvs[SUBSET_DEF,IN_DEF]>>
  qexists_tac`w`>>simp[]
QED

(* b = T is for structural only, b = F is for all *)
Definition get_fml_def:
  get_fml b fml =
  {c | ∃n b'.
    lookup n fml = SOME (c:int list,b') ∧ (b ⇒ b')}
End

Theorem set_delete_literals:
  set (delete_literals C D)  =
  set C DIFF set D
Proof
  simp[delete_literals_def]>>
  fs[EXTENSION,MEM_MAP]>>
  fs[MEM_FILTER]>>
  metis_tac[]
QED

Theorem lookup_get_fml:
  lookup h fml = SOME (c,b) ⇒
  c ∈ get_fml b fml
Proof
  rw[lookup_def,get_fml_def,AllCaseEqs()]>>
  metis_tac[PAIR,FST,SND]
QED

Theorem get_fml_imply:
  (b ⇒ b') ∧
  C ∈ get_fml b' fml ⇒
  C ∈ get_fml b fml
Proof
  rw[get_fml_def]>>
  metis_tac[]
QED

Theorem is_rup_sound:
  ∀is C.
  is_rup b fml is C ∧
  sat_fml w (get_fml b fml) ⇒
  sat_clause w C
Proof
  Induct>>fs[is_rup_def]>>
  rw[] >> gvs[AllCasePreds()]>>
  rename1`delete_literals Ci C`>>
  `set Ci DIFF set C =
   set (delete_literals Ci C)` by
   metis_tac[set_delete_literals]>>
  gvs[]
  >- (
    fs[sat_fml_def,PULL_EXISTS]>>
    drule_all lookup_get_fml>>
    strip_tac>>
    drule_all get_fml_imply>>
    rw[]>>
    first_x_assum drule>>
    rw[sat_clause_def]>>
    first_x_assum (irule_at Any)>>
    rfs[EXTENSION,MEM_MAP]>>
    metis_tac[])
  >- (
    first_x_assum drule_all>>
    gvs[sat_clause_def,EXTENSION]>>
    reverse (rw[])
    >- metis_tac[]>>
    fs[sat_fml_def,PULL_EXISTS]>>
    drule_all lookup_get_fml>>
    rw[]>>
    drule_all get_fml_imply>>
    rw[]>>
    first_x_assum drule>>
    rw[sat_clause_def]>>
    rename1`sat_lit w ll`>>
    Cases_on`MEM ll C`
    >- metis_tac[] >>
    first_x_assum (qspec_then`ll` mp_tac)>>
    simp[]>>
    rw[]>>
    `l = 0` by (
      gvs[sat_lit_def,match_lit_def]>>
      every_case_tac>>gvs[]>>
      intLib.ARITH_TAC))
QED

Theorem range_insert_one:
  insert_one b fml n C = SOME fml' ⇒
  range fml' = (C,b) INSERT range fml
Proof
  rw[insert_one_def,range_def,AllCaseEqs(),EXTENSION]>>
  eq_tac>>rw[]>>
  gvs[AllCaseEqs(),lookup_insert]>>
  metis_tac[option_CLAUSES]
QED

Theorem get_fml_insert_one:
  insert_one b fml n C = SOME fml' ⇒
  (get_fml b' fml' =
    if b' ⇒ b then C INSERT get_fml b' fml
    else get_fml b' fml)
Proof
  strip_tac>>drule range_insert_one>>
  rw[range_def,get_fml_def,EXTENSION]>>
  gvs[]>>metis_tac[PAIR,FST,SND]
QED

Theorem get_fml_SUBSET:
  (b ⇒ b') ⇒
  get_fml b' fml ⊆ get_fml b fml
Proof
  rw[get_fml_def,SUBSET_DEF]>>
  metis_tac[PAIR]
QED

Theorem get_fml_delete_SUBSET:
  get_fml b (delete n fml) ⊆ get_fml b fml
Proof
  rw[get_fml_def,lookup_delete,SUBSET_DEF]>>
  metis_tac[]
QED

Theorem arb_delete_subset:
  ∀ls fml. arb_delete nc ls fml = SOME fml' ⇒
  get_fml b fml' ⊆ get_fml b fml
Proof
  Induct>>rw[arb_delete_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  metis_tac[get_fml_delete_SUBSET,SUBSET_TRANS]
QED

Theorem range_insert_list:
  ∀cs fml n fml'.
  insert_list b fml n cs = SOME fml' ⇒
  range fml' = set (MAP (λC. C,b) cs) ∪ range fml
Proof
  Induct>>rw[insert_list_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  rw[]>>
  drule range_insert_one>>
  simp[EXTENSION,MEM_MAP]>>
  metis_tac[]
QED

Theorem get_fml_insert_list_F:
  insert_list b fml n cs = SOME fml' ⇒
  get_fml F fml' = set cs ∪ get_fml F fml
Proof
  strip_tac>>drule range_insert_list>>
  rw[range_def,get_fml_def,EXTENSION]>>
  gvs[MEM_MAP,FORALL_PROD]>>
  metis_tac[]
QED

Theorem get_fml_insert_list_T:
  insert_list T fml n cs = SOME fml' ⇒
  get_fml T fml' = set cs ∪ get_fml T fml
Proof
  strip_tac>>drule range_insert_list>>
  rw[range_def,get_fml_def,EXTENSION]>>
  gvs[MEM_MAP,FORALL_PROD]>>
  metis_tac[]
QED

Theorem mk_sko_sem:
  v ≠ 0 ∧ EVERY (λi. i ≠ 0) ls ⇒
  (
    sat_fml w (set (mk_sko v ls)) ⇔
    (
      (w v ⇒ EVERY (sat_lit w) ls)
    )
  )
Proof
  rw[sat_fml_def,mk_sko_def]>>
  gvs[MEM_MAP,SF DNF_ss,sat_clause_cons]>>
  eq_tac>>rw[]>>gvs[EVERY_MEM]>>
  gvs[sat_clause_def,MEM_MAP]>>
  metis_tac[]
QED

Theorem mk_pro_sem:
  v ≠ 0 ∧ EVERY (λi. i ≠ 0) ls ⇒
  (
    sat_fml w (set (mk_pro v ls)) ⇔
    (
      (w v ⇔ EVERY (sat_lit w) ls)
    )
  )
Proof
  rw[mk_pro_def,mk_sko_sem]>>
  gvs[MEM_MAP,SF DNF_ss,sat_clause_cons]>>
  eq_tac>>rw[]>>gvs[EVERY_MEM]
  >- (
    gvs[sat_clause_def,MEM_MAP]>>
    metis_tac[])
  >- (
    gvs[EXISTS_MEM,SF DNF_ss,sat_clause_def,MEM_MAP,PULL_EXISTS]>>
    metis_tac[sat_lit_neg])
QED

Theorem lookup_unit_cases:
  lookup n t = SOME () ∨ lookup n t = NONE
Proof
  Cases_on`lookup n t`>>rw[]
QED

Theorem is_data_var_get_data_vars:
  is_data_var pc v ⇔
  v ∈ get_data_vars pc
Proof
  rw[get_data_vars_def,is_data_var_def]>>
  TOP_CASE_TAC>>gvs[domain_lookup]>>
  metis_tac[lookup_unit_cases,option_CLAUSES]
QED

Theorem agree_on_vars_clause:
  agree_on (vars_clause C) w w' ⇒
  (sat_clause w C ⇔ sat_clause w' C)
Proof
  rw[vars_clause_def,agree_on_def,PULL_EXISTS,sat_clause_def]>>
  gvs[sat_lit_def,match_lit_def,var_lit_def]>>
  metis_tac[]
QED

Theorem equiv_imp_imp = METIS_PROVE [] ``(!x. (P x ⇒ (Q x ⇔ R x))) ⇒ ((!x. P x ⇒ Q x) ⇔ (!x. P x ⇒ R x))``;

Theorem equiv_imp_imp_2 = METIS_PROVE [] ``(!x. (P x ⇒ (Q x ⇔ R x))) ⇒ ((?x. P x ∧ Q x) ⇔ (?x. P x ∧ R x))``;

Theorem agree_on_vars_fml:
  agree_on (vars_fml fml) w w' ⇒
  (sat_fml w fml ⇔ sat_fml w' fml)
Proof
  rw[vars_fml_def,sat_fml_def]>>
  ho_match_mp_tac equiv_imp_imp>>
  rw[]>>
  match_mp_tac agree_on_vars_clause>>
  irule agree_on_SUBSET>>
  first_x_assum (irule_at Any)>>
  match_mp_tac SUBSET_BIGUNION_I>>
  simp[]
QED

Theorem mk_sum_sem:
  v ≠ 0 ∧ EVERY (λi. i ≠ 0) ls ⇒
  ((sat_fml w (set (mk_sum v ls))) ⇔ (w v ⇔ EXISTS (sat_lit w) ls))
Proof
  rw[sat_fml_def,mk_sum_def]>>
  gvs[MEM_MAP,SF DNF_ss,sat_clause_cons,EVERY_MEM,EXISTS_MEM,sat_clause_def]>>
  eq_tac>>rw[]>>
  gvs[]>>
  metis_tac[sat_lit_neg]
QED

Theorem check_scpstep_extends_over:
  good_pc pc ∧
  check_scpstep pc fml sc scpstep = SOME (fml',sc') ∧
  vars_fml (get_fml F fml) ⊆ count (pc.nv+1) ∪ domain sc.Ev
  ⇒
  extends_over (get_data_vars pc)
    (λw. sat_fml w (get_fml F fml))
    (λw. sat_fml w (get_fml F fml'))
Proof
  Cases_on`scpstep`>>
  simp[check_scpstep_def]
  >- ( (* RupAdd *)
    strip_tac>>
    gvs[AllCaseEqs()]>>
    drule is_rup_sound>>
    drule get_fml_insert_one>>
    gvs[extends_over_def]>>
    disch_then kall_tac>>
    strip_tac>>
    rw[]>>
    qexists_tac`w`>>gvs[]>>
    first_x_assum irule>>
    irule_at Any sat_fml_SUBSET>>
    first_x_assum (irule_at Any)>>
    metis_tac[get_fml_SUBSET])
  >- ( (* ArbDel *)
    rw[]>>
    match_mp_tac extends_over_SUBSET>>
    simp[SUBSET_DEF]>>
    rw[]>>irule_at Any sat_fml_SUBSET>>
    first_x_assum (irule_at Any)>>
    metis_tac[arb_delete_subset])
  >- ( (* DeclPro *)
    strip_tac>>
    gvs[declare_pro_def,AllCaseEqs(),check_pro_def,is_fresh_def]>>
    rename1`mk_pro v ls`>>
    `v ∉ get_data_vars pc` by (
      gvs[good_pc_def,get_data_vars_def]>>
      TOP_CASE_TAC>>gvs[SUBSET_DEF]>>
      CCONTR_TAC>>gvs[]>>first_x_assum drule>>
      gvs[])>>
    drule get_fml_insert_list_F>>
    simp[]>>
    disch_then kall_tac>>
    drule_at Any mk_pro_sem>>
    rw[extends_over_def]>>
    qexists_tac`λx.
      if x = v then EVERY (sat_lit w) ls else w x`>>
    rw[]
    >- (
      rw[agree_on_def]>>
      IF_CASES_TAC>>gvs[])
    >- (
      match_mp_tac EVERY_CONG>>rw[]>>
      simp[sat_lit_def]>>
      gvs[EVERY_MEM]>>
      first_x_assum drule>>
      rw[is_data_ext_lit_run_def,is_data_var_get_data_vars])
    >- (
      DEP_ONCE_REWRITE_TAC[agree_on_vars_fml |> GSYM]>>
      rw[agree_on_def]>>
      IF_CASES_TAC>>gvs[SUBSET_DEF]>>
      first_x_assum drule>>gvs[domain_lookup]))
  >- ( (* DeclSum *)
    strip_tac>>
    gvs[declare_sum_def,AllCaseEqs()]>>
    rename1`mk_sum v [l1;l2]`>>
    qmatch_asmsub_abbrev_tac`mk_sum v ls`>>
    gvs[check_sum_def,is_fresh_def]>>
    `v ≠ 0 ∧ v ∉ get_data_vars pc` by (
      gvs[good_pc_def,SUBSET_DEF,get_data_vars_def]>>
      TOP_CASE_TAC>>
      CCONTR_TAC>>gvs[]>>first_x_assum drule>>
      gvs[])>>
    drule get_fml_insert_list_F>>
    simp[]>>
    disch_then kall_tac>>rw[]>>
    drule_all mk_sum_sem>>
    rw[extends_over_def]>>
    qexists_tac`λx.
      if x = v then EXISTS (sat_lit w) ls else w x`>>
    rw[]
    >- (
      rw[agree_on_def]>>
      IF_CASES_TAC>>gvs[])
    >- (
      match_mp_tac EXISTS_CONG>>rw[]>>
      simp[sat_lit_def]>>
      gvs[EVERY_MEM]>>
      first_x_assum drule>>
      rw[is_data_ext_lit_run_def,is_data_var_get_data_vars])
    >- (
      DEP_ONCE_REWRITE_TAC[agree_on_vars_fml |> GSYM]>>
      rw[agree_on_def]>>
      IF_CASES_TAC>>gvs[SUBSET_DEF]>>
      first_x_assum drule>>gvs[domain_lookup]))
  >- ( (* DeclSko *)
    strip_tac>>
    gvs[declare_sko_def,AllCaseEqs(),check_sko_def,is_fresh_def]>>
    rename1`insert_one _ _ _ [&v] = _`>>
    `v ∉ get_data_vars pc` by (
      gvs[good_pc_def,get_data_vars_def,SUBSET_DEF]>>
      TOP_CASE_TAC>>gvs[]>>
      CCONTR_TAC>>gvs[]>>first_x_assum drule>>
      gvs[])>>
    drule get_fml_insert_one>>
    simp[]>> rw[]>>
    rw[extends_over_def]>>
    qexists_tac`λx. x = v ∨ w x`>>
    rw[]
    >- (
      rw[agree_on_def]>>
      metis_tac[])
    >- (
      DEP_ONCE_REWRITE_TAC[agree_on_vars_fml |> GSYM]>>
      rw[agree_on_def]>>
      gvs[SUBSET_DEF]>>
      `x ≠ v` by (
        first_x_assum drule>>gvs[domain_lookup]>>
        rw[]>>gvs[]>>
        metis_tac[option_CLAUSES])>>
      simp[]))
QED

Definition check_scpsteps_def:
  (check_scpsteps pc fml sc [] = SOME (fml,sc)) ∧
  (check_scpsteps pc fml sc (x::xs) =
    case check_scpstep pc fml sc x of NONE => NONE
    | SOME (fml',sc') =>
      check_scpsteps pc fml' sc' xs)
End

Theorem agree_on_trans:
  agree_on D w w' ∧ agree_on D w' w'' ⇒
  agree_on D w w''
Proof
  rw[agree_on_def]
QED

Theorem extends_over_trans:
  extends_over D x y ∧ extends_over D y z ⇒
  extends_over D x z
Proof
  rw[extends_over_def]>>
  metis_tac[agree_on_trans]
QED

Theorem vars_clause_MAP_neg[simp]:
  vars_clause (MAP (λl. -l) ls) = vars_clause ls
Proof
  rw[vars_clause_def,EXTENSION,MEM_MAP,var_lit_def]>>
  eq_tac>>rw[]>>
  first_x_assum (irule_at Any)>>
  intLib.ARITH_TAC
QED

Theorem vars_fml_mk_pro:
  v ≠ 0 ∧ EVERY (λi. i ≠ 0) ls ⇒
  vars_fml (set (mk_pro v ls)) =
  v INSERT IMAGE var_lit (set ls)
Proof
  rw[mk_pro_def,mk_sko_def,vars_fml_def]>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE,o_DEF]>>
  rw[EXTENSION,vars_clause_def,PULL_EXISTS,var_lit_def]>>
  eq_tac>>rw[]
  >- metis_tac[]
  >- metis_tac[]>>
  gvs[EVERY_MEM]>> metis_tac[]
QED

Theorem vars_fml_mk_sum:
  v ≠ 0 ∧ EVERY (λi. i ≠ 0) ls ⇒
  vars_fml (set (mk_sum v ls)) =
  v INSERT IMAGE var_lit (set ls)
Proof
  rw[mk_sum_def,vars_fml_def]>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE,o_DEF]>>
  rw[EXTENSION,vars_clause_def,PULL_EXISTS,var_lit_def]>>
  eq_tac>>rw[]
  >- metis_tac[]
  >- metis_tac[]>>
  gvs[EVERY_MEM]>> metis_tac[]
QED

Theorem vars_fml_mk_sko:
  v ≠ 0 ∧ EVERY (λi. i ≠ 0) ls ⇒
  vars_fml (set (mk_sko v ls)) ⊆
  v INSERT IMAGE var_lit (set ls)
Proof
  rw[mk_sko_def,vars_fml_def]>>
  simp[LIST_TO_SET_MAP,IMAGE_IMAGE,o_DEF]>>
  rw[SUBSET_DEF,vars_clause_def,PULL_EXISTS,var_lit_def]>>
  metis_tac[]
QED

(*
Theorem domain_mk_Ev[simp]:
  domain (mk_Ev Ev v ls) = v INSERT domain Ev
Proof
  rw[mk_Ev_def]
QED
*)

Theorem check_scpstep_vars_fml:
  good_pc pc ∧
  check_scpstep pc fml sc scpstep = SOME (fml',sc') ∧
  vars_fml (get_fml F fml) ⊆ count (pc.nv+1) ∪ domain sc.Ev ⇒
  vars_fml (get_fml F fml') ⊆ count (pc.nv+1) ∪ domain sc'.Ev
Proof
  Cases_on`scpstep`>>
  simp[check_scpstep_def]>>rw[]>>gvs[AllCaseEqs()]
  >-
    gvs[declare_root_def,AllCaseEqs()]
  >- (
    drule get_fml_insert_one>>rw[]>>
    gvs[vars_clause_def,var_lit_def,SUBSET_DEF,EVERY_MEM,PULL_EXISTS]>>
    rw[]>>
    first_x_assum drule>>
    simp[is_fresh_def,domain_lookup]>>
    rename1`lookup xn sc.Ev`>>
    Cases_on`lookup xn sc.Ev`>>rw[])
  >- (
    irule SUBSET_TRANS>>
    first_x_assum (irule_at Any)>>
    metis_tac[arb_delete_subset,vars_fml_SUBSET])
  >- (
    gvs[declare_pro_def,check_pro_def,AllCaseEqs()]>>
    drule_all vars_fml_mk_pro>>
    drule get_fml_insert_list_F>>
    rw[]>>gvs[]
    >- (
      gvs[EVERY_MEM,is_data_ext_lit_run_def,SUBSET_DEF,PULL_EXISTS,good_pc_def,is_data_var_get_data_vars]>>
      rw[]>>first_x_assum drule>>
      gvs[domain_lookup]>>
      metis_tac[lookup_unit_cases,option_CLAUSES])
    >- (
      gvs[SUBSET_DEF]>>
      metis_tac[]) )
  >- (
    gvs[declare_sum_def,check_sum_def]>>
    rename1`mk_sum v [l1;l2]`>>
    qmatch_asmsub_abbrev_tac`mk_sum v ls`>>
    drule vars_fml_mk_sum>>
    disch_then (qspec_then`ls` mp_tac)>>
    impl_tac >- rw[Abbr`ls`]>>
    drule get_fml_insert_list_F>>
    rw[]
    >- (
      gvs[EVERY_MEM,is_data_ext_lit_run_def,SUBSET_DEF,PULL_EXISTS,good_pc_def,is_data_var_get_data_vars]>>
      rw[Abbr`ls`]>>
      gvs[domain_lookup]>>
      metis_tac[lookup_unit_cases,option_CLAUSES])
    >- (
      gvs[SUBSET_DEF]>>
      metis_tac[]) )
  >- (
    gvs[declare_sko_def,check_sko_def,AllCaseEqs()]>>
    drule_all vars_fml_mk_pro>>
    drule get_fml_insert_one>>
    rw[]
    >-
      simp[vars_clause_def,var_lit_def]
    >- (
      gvs[SUBSET_DEF]>>
      metis_tac[]))
QED

Theorem is_data_ext_lit_run_insert:
  is_data_ext_lit_run pc ev l ∧
  lookup n ev = NONE ⇒
  is_data_ext_lit_run pc (insert n v ev) l
Proof
  rw[is_data_ext_lit_run_def,lookup_insert]>>
  metis_tac[]
QED

Theorem check_scpsteps_extends_over:
  ∀xs fml sc.
  good_pc pc ∧
  check_scpsteps pc fml sc xs = SOME (fml',sc') ∧
  vars_fml (get_fml F fml) ⊆ count (pc.nv+1) ∪ domain sc.Ev
  ⇒
  extends_over (get_data_vars pc)
    (λw. sat_fml w (get_fml F fml))
    (λw. sat_fml w (get_fml F fml'))
Proof
  Induct>>simp[check_scpsteps_def]>>
  rpt gen_tac>>
  strip_tac>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  impl_tac >-
    metis_tac[check_scpstep_vars_fml]>>
  drule_all check_scpstep_extends_over>>
  rw[]>>
  metis_tac[extends_over_trans]
QED

Definition models_def:
  models D ws = IMAGE (λw. D ∩ w) ws
End

Definition build_fml_def:
  (build_fml (id:num) [] = LN) ∧
  (build_fml id (cl::cls) =
    insert id (cl,F) (build_fml (id+1) cls))
End

Theorem lookup_build_fml:
  ∀ls n acc i.
  lookup i (build_fml n ls) =
  if n ≤ i ∧ i < n + LENGTH ls
  then SOME (EL (i-n) ls, F)
  else NONE
Proof
  Induct>>rw[build_fml_def,lookup_def,lookup_insert]>>
  `i-n = SUC(i-(n+1))` by DECIDE_TAC>>
  simp[]
QED

Definition init_sc_def:
  init_sc =
    <| Ev := LN ;
       root := NONE;
       scp := [] |>
End

Definition wf_scp_def:
  wf_scp (v,scpn) =
  (v ≠ 0n ∧
  case scpn of
    Pro ls =>
      EVERY (λi. i ≠ 0) ls
  | Sum ls =>
      EVERY (λi. i ≠ 0) ls ∧ LENGTH ls = 2
  | Sko ls =>
      EVERY (λi. i ≠ 0) ls
  )
End

(* Invariant maintained by the configuration *)
Definition conf_inv_def:
  conf_inv pc sc ⇔
  count (pc.nv + 1) ∩ domain sc.Ev = {} ∧
  dir_scp (get_data_vars pc)
    (count (pc.nv+1) DIFF get_data_vars pc)
    (domain sc.Ev) sc.scp ∧
  EVERY wf_scp sc.scp ∧
  ALL_DISTINCT (MAP FST sc.scp) ∧ domain sc.Ev = set (MAP FST sc.scp) ∧
  (* (∀n v.
    lookup n sc.Ev = SOME v ⇒
    vars_scp T (&n) sc.scp = domain v) ∧
  (∀r. decomposable_scp T r sc.scp) ∧ *)
  (∀r. deterministic_scp F r sc.scp)
End

Theorem is_data_ext_lit_run_sem:
  domain (Ev:num_set) = set (MAP FST scp) ∧
  is_data_ext_lit_run pc Ev i ⇒
  is_data_ext_lit (get_data_vars pc) scp i
Proof
  rw[is_data_ext_lit_run_def,is_data_ext_lit_def,is_data_var_get_data_vars] >>
  gvs[domain_lookup,MEM_MAP,EXTENSION]>>
  metis_tac[lookup_unit_cases,option_CLAUSES]
QED

Theorem INTER_INSERT:
  A ∩ (x INSERT B) =
  if x ∈ A then x INSERT (A ∩ B) else A ∩ B
Proof
  rw[EXTENSION]>>metis_tac[]
QED

Theorem dir_scp_more_E[simp]:
  ∀ns.
  dir_scp D P E ns ⇒
  dir_scp D P (x INSERT E) ns
Proof
  Induct>-rw[dir_scp_def]>>
  Cases>>rw[dir_scp_def]
QED

Theorem is_data_ext_lit_more_ls[simp]:
  is_data_ext_lit D ls l ⇒
  is_data_ext_lit D (n::ls) l
Proof
  rw[is_data_ext_lit_def]>>
  metis_tac[]
QED

Theorem vars_scp_ALOOKUP_NONE:
  ∀ns.
  ALOOKUP ns (var_lit n) = NONE ⇒
  vars_scp b n ns = {var_lit n}
Proof
  Induct>-rw[vars_scp_def]>>
  Cases>>
  rw[vars_scp_def]
QED

Theorem domain_FOLDL_union:
  ∀ls tt.
  domain (FOLDL union tt ls) =
  domain tt ∪ BIGUNION (IMAGE domain (set ls))
Proof
  Induct>>rw[]>>
  metis_tac[UNION_ASSOC]
QED

(*
Theorem domain_big_union:
  domain (big_union ls) =
  BIGUNION (IMAGE domain (set ls))
Proof
  simp[big_union_def,domain_FOLDL_union]
QED

Theorem domain_FOLDL_disj_NONE[simp]:
  ∀ls.
  FOLDL
    (\t i.
      case t of NONE => NONE
      | SOME tt =>
        if isEmpty (inter i tt) then
          SOME (union i tt)
        else NONE) NONE ls = NONE
Proof
  Induct>>rw[]
QED

Theorem domain_FOLDL_disj_union:
  ∀ls tt.
  FOLDL
    (\t i.
      case t of NONE => NONE
      | SOME tt =>
        if isEmpty (inter i tt) then
          SOME (union i tt)
        else NONE) (SOME tt) ls = SOME res ⇒
  domain res = domain tt ∪ BIGUNION (IMAGE domain (set ls)) ∧
  all_disjoint (domain tt :: MAP domain ls)
Proof
  Induct>-
    rw[all_disjoint_def]>>
  simp[]>>
  ntac 2 strip_tac>>
  IF_CASES_TAC>>gvs[]>>
  strip_tac>>
  first_x_assum drule>>
  rw[]
  >- metis_tac[UNION_COMM,UNION_ASSOC]>>
  gvs[all_disjoint_CONS,inter_eq_LN]>>
  metis_tac[DISJOINT_SYM]
QED

Theorem domain_big_disjoint_union:
  big_disjoint_union ls = SOME res ⇒
  domain res = BIGUNION (IMAGE domain (set ls)) ∧
  all_disjoint (MAP domain ls)
Proof
  simp[big_disjoint_union_def]>>
  rw[]>>
  drule domain_FOLDL_disj_union>>simp[all_disjoint_CONS]
QED

Theorem lookup_mk_Ev:
  EVERY (λx. x > 0 ∨ lookup(var_lit x) Ev = NONE) ls ∧
  (∀n. lookup n Ev = NONE ⇒ ALOOKUP scp n = NONE) ∧
  (∀n res. lookup n Ev = SOME res ⇒ vars_scp b (&n) scp = domain res) ∧
  lookup n (mk_Ev Ev v ls) = SOME res ⇒
  if n = v then
    domain res =
      BIGUNION (IMAGE (λi. vars_scp b i scp) (set ls))
  else lookup n Ev = SOME res
Proof
  rw[mk_Ev_def,lookup_insert]>>
  simp[domain_big_union]>>
  AP_TERM_TAC>>
  simp[get_node_vars_def,LIST_TO_SET_MAP,IMAGE_IMAGE,o_DEF]>>
  match_mp_tac IMAGE_CONG>>rw[]>>
  TOP_CASE_TAC>>rw[domain_insert]
  >- (
    first_x_assum drule>>
    metis_tac[vars_scp_ALOOKUP_NONE])
  >>
    first_x_assum drule>>
    gvs[EVERY_MEM]>>first_x_assum drule>>rw[]
QED

Theorem lookup_mk_Ev_disj:
  EVERY (λx. x > 0 ∨ lookup(var_lit x) Ev = NONE) ls ∧
  (∀n. lookup n Ev = NONE ⇒ ALOOKUP scp n = NONE) ∧
  (∀n res. lookup n Ev = SOME res ⇒ vars_scp b (&n) scp = domain res) ∧
  mk_Ev_disj Ev v ls = SOME Ev' ∧
  lookup n Ev' = SOME res ⇒
  if n = v then
    domain res =
      BIGUNION (IMAGE (λi. vars_scp b i scp) (set ls))
  else lookup n Ev = SOME res
Proof
  rw[mk_Ev_disj_def]>>gvs[lookup_insert]>>
  drule domain_big_disjoint_union>>rw[]>>
  AP_TERM_TAC>>
  simp[get_node_vars_def,LIST_TO_SET_MAP,IMAGE_IMAGE,o_DEF]>>
  match_mp_tac IMAGE_CONG>>rw[]>>
  TOP_CASE_TAC>>rw[domain_insert]
  >- (
    first_x_assum drule>>
    metis_tac[vars_scp_ALOOKUP_NONE])
  >>
    first_x_assum drule>>
    gvs[EVERY_MEM]>>first_x_assum drule>>rw[]
QED

Theorem domain_mk_Ev_disj:
  mk_Ev_disj Ev v ls = SOME Ev' ⇒
  domain Ev' = v INSERT domain Ev
Proof
  rw[mk_Ev_disj_def]>>simp[domain_insert]
QED

Theorem all_disjoint_mk_Ev_disj:
  EVERY (λx. x > 0 ∨ lookup(var_lit x) Ev = NONE) ls ∧
  (∀n. lookup n Ev = NONE ⇒ ALOOKUP scp n = NONE) ∧
  (∀n res. lookup n Ev = SOME res ⇒ vars_scp b (&n) scp = domain res) ∧
  mk_Ev_disj Ev v ls = SOME Ev' ⇒
  all_disjoint (MAP (λi. vars_scp b i scp) ls)
Proof
  rw[]>>
  gvs[mk_Ev_disj_def]>>
  drule domain_big_disjoint_union>>
  rw[]>>
  qmatch_asmsub_abbrev_tac`all_disjoint A`>>
  qmatch_goalsub_abbrev_tac`all_disjoint B`>>
  `A = B` by (
    unabbrev_all_tac>>
    simp[get_node_vars_def,MAP_MAP_o,o_DEF,MAP_EQ_f]>>rw[]>>
    TOP_CASE_TAC>>rw[domain_insert]
    >- (
      first_x_assum drule>>
      metis_tac[vars_scp_ALOOKUP_NONE])
    >>
      first_x_assum drule>>
      gvs[EVERY_MEM]>>first_x_assum drule>>rw[])>>
  gvs[]
QED
*)

Theorem all_disjoint_2:
  all_disjoint [X;Y] ⇔
  DISJOINT X Y
Proof
  rw[all_disjoint_def]>>
  `∀i. i < 2 ⇔ i = 0n ∨ i = 1` by
    intLib.ARITH_TAC>>
  rw[SF DNF_ss]>>
  metis_tac[DISJOINT_SYM]
QED

Definition mk_enc_one_def:
  mk_enc_one (v,scpn) =
  case scpn of
    Pro ls =>
      mk_pro v ls
  | Sum ls => mk_sum v ls
  | Sko ls => [[(&v):int]]
End

Theorem EVERY_mk_enc_one_sat_scp:
  D ∩ E = {} ⇒
  ∀ns r.
  EVERY (λn. sat_fml w (set (mk_enc_one n))) ns ∧
  EVERY wf_scp ns ∧
  is_data_ext_lit D ns r ∧
  dir_scp D P E ns
  ⇒
  (sat_scp F r ns w ⇔ sat_lit w r)
Proof
  strip_tac>>
  Induct>>rw[sat_scp_def]>>
  Cases_on`h`>>
  gvs[dir_scp_def]>>
  reverse (rw[sat_scp_def])
  >- gvs[is_data_ext_lit_def]>>
  rename1`match_lit rr`>>
  `rr > 0` by (
    gvs[dir_scp_def,is_data_ext_lit_def,EXTENSION]>>
    metis_tac[])>>
  gvs[match_lit_def,AllCasePreds(),mk_enc_one_def]
  >- (
    gvs[wf_scp_def]>>
    rename1`mk_pro _ ls`>>
    drule_at Any mk_pro_sem>>
    rw[]>>gvs[]>>
    simp[sat_lit_def,match_lit_def]>>
    match_mp_tac EVERY_CONG>>gvs[EVERY_MEM])
  >- (
    gvs[wf_scp_def]>>
    rename1`mk_sum _ ls`>>
    drule_at Any mk_sum_sem>>
    rw[]>>gvs[]>>
    simp[sat_lit_def,match_lit_def]>>
    match_mp_tac EXISTS_CONG>>gvs[EVERY_MEM])
QED

Theorem dir_scp_vars_fml_mk_enc_one:
  ∀ns.
  dir_scp D P E ns ∧
  EVERY wf_scp ns ∧
  MEM n ns ⇒
  vars_fml (set (mk_enc_one n)) ⊆ D ∪ P ∪ set (MAP FST ns)
Proof
  Induct>-rw[]>>
  reverse (Cases>>gvs[dir_scp_def]>>rw[]>>gvs[])
  >-
    (gvs[SUBSET_DEF]>>metis_tac[])>>
  gvs[AllCasePreds(),mk_enc_one_def,wf_scp_def]
  >- (
    gvs[vars_fml_mk_pro,is_data_ext_lit_def,EVERY_MEM,SUBSET_DEF,MEM_MAP]>>
    metis_tac[ALOOKUP_MEM,FST])
  >- (
    gvs[vars_fml_mk_sum,is_data_ext_lit_def,EVERY_MEM,SUBSET_DEF,MEM_MAP]>>
    metis_tac[ALOOKUP_MEM,FST])
  >- (
    rw[]
    >- gvs[vars_clause_def]
    >- gvs[vars_fml_def]>>
    irule SUBSET_TRANS>>
    irule_at Any vars_fml_mk_sko>>
    gvs[EVERY_MEM,SUBSET_DEF,PULL_EXISTS])
QED

Theorem is_data_ext_lit_imp:
  D ∩ E = {} ∧
  is_data_ext_lit D ns e ∧
  dir_scp D P E ns ⇒
  (
    (var_lit e ∉ E ∧ (sat_scp b e ns w ⇔ sat_lit w e)) ∨
    e > 0 ∧ ∃y. MEM y ns ∧ &FST y = e
  )
Proof
  rw[is_data_ext_lit_def]
  >- (
    DEP_REWRITE_TAC[sat_scp_ALOOKUP_NONE]>>
    rw[]>>
    drule dir_scp_MAP_FST>>
    gvs[ALOOKUP_NONE,SUBSET_DEF,MEM_MAP,PULL_EXISTS,EXTENSION]>>
    metis_tac[])>>
  DISJ2_TAC>>simp[]>>
  gvs[MEM_MAP]>>
  `&FST y = e` by metis_tac[var_lit_int]>>
  metis_tac[]
QED

Theorem sat_scp_mk_enc_one:
  D ∩ E = {} ∧ P ∩ E = {} ⇒
  ∀ns.
  dir_scp D P E ns ∧
  EVERY wf_scp ns ∧
  ALL_DISTINCT (MAP FST ns) ⇒
  ∃w'.
    agree_on (UNIV DIFF E) w w' ∧
    EVERY (λn.
      sat_fml w' (set (mk_enc_one n)) ∧
      (sat_scp F (&(FST n)) ns w ⇔ sat_lit w' (&(FST n)))
    ) ns
Proof
  strip_tac>>
  Induct
  >- (
    rw[sat_scp_def]>>
    metis_tac[agree_on_refl])>>
  Cases>>rw[]>>
  gvs[dir_scp_def]>>
  rename1`agree_on _ w w'`>>
  rename1`wf_scp (q,r)`>>
  `&q > 0i` by (
      gvs[wf_scp_def]>>
      intLib.ARITH_TAC)>>
  qexists_tac`λx. if x = q then sat_scp F (&q) ((q,r)::ns) w else w' x`>>
  rw[]
  >- (gvs[agree_on_def] >> rw[])
  >- (
    simp[sat_scp_def,mk_enc_one_def]>>
    Cases_on`r`>>gvs[wf_scp_def]
    >- ( (* Pro *)
      gvs[mk_pro_sem,sat_scp_def,match_lit_def,EVERY_MEM]>>
      ho_match_mp_tac equiv_imp_imp>>
      rw[]>>
      first_x_assum drule>>
      rw[]>>
      drule_all is_data_ext_lit_imp>>
      disch_then (qspecl_then [`w`,`F`] assume_tac)>>gvs[]
      >- (
        match_mp_tac sat_lit_eq>>
        gvs[agree_on_def]>>rw[]>>
        metis_tac[])>>
      last_x_assum drule>>rw[]>>
      match_mp_tac sat_lit_eq>>
      rw[]>>
      gvs[MEM_MAP])
    >- ( (* Sum *)
      gvs[mk_sum_sem,sat_scp_def,match_lit_def,EXISTS_MEM,EVERY_MEM]>>
      ho_match_mp_tac equiv_imp_imp_2>>
      rw[]>>
      first_x_assum drule>>
      rw[]>>
      drule_all is_data_ext_lit_imp>>
      disch_then (qspecl_then [`w`,`F`] assume_tac)>>gvs[]
      >- (
        match_mp_tac sat_lit_eq>>
        gvs[agree_on_def]>>rw[]>>
        metis_tac[])>>
      last_x_assum drule>>rw[]>>
      match_mp_tac sat_lit_eq>>
      rw[]>>gvs[MEM_MAP])
    >- ( (* Sko *)
      rw[]>>
      gvs[match_lit_def]))
  >- simp[sat_lit_def,match_lit_def]
  >- (
    gvs[EVERY_MEM]>>rw[]>>
    last_x_assum drule>>rw[]
    >- (
      qpat_x_assum`sat_fml _ _` mp_tac>>
      match_mp_tac EQ_IMPLIES>>
      match_mp_tac agree_on_vars_fml>>
      rw[agree_on_def]>>rw[]>>
      drule dir_scp_vars_fml_mk_enc_one>>
      simp[EVERY_MEM]>>
      disch_then drule>>
      rw[SUBSET_DEF]>>gvs[EXTENSION]>>
      metis_tac[])
    >- (
      simp[Once sat_scp_def]>>
      `q ≠ FST n` by
        (gvs[MEM_MAP]>>metis_tac[])>>
      simp[sat_lit_def]))
QED

Theorem check_scpstep_conf_inv:
  good_pc pc ∧
  check_scpstep pc fml sc scpstep = SOME (fml',sc') ∧
  conf_inv pc sc ∧
  (∀w. EVERY (λn. sat_fml w (set (mk_enc_one n))) sc.scp ⇒
    sat_fml w (get_fml T fml)) ⇒
  conf_inv pc sc' ∧
  (∀w. EVERY (λn. sat_fml w (set (mk_enc_one n))) sc'.scp ⇒
    sat_fml w (get_fml T fml'))
Proof
  strip_tac>>
  `get_data_vars pc ∩ domain sc.Ev = {}` by (
    gvs[good_pc_def,conf_inv_def,EXTENSION,SUBSET_DEF]>>
    metis_tac[])>>
  `(∀n. lookup n sc.Ev = NONE ⇒ ALOOKUP sc.scp n = NONE)` by  (
      gvs[conf_inv_def,ALOOKUP_NONE,EXTENSION]>>
      metis_tac[domain_lookup,option_CLAUSES])>>
  Cases_on`scpstep`>>
  gvs[check_scpstep_def,AllCaseEqs()]
  >- (
    gvs[declare_root_def,conf_inv_def,AllCaseEqs()]>>
    metis_tac[is_data_ext_lit_run_sem])
  >- (
    rw[]>>first_x_assum drule>>
    drule is_rup_sound>>
    drule get_fml_insert_one>>
    simp[]>>rw[])
  >- (
    rw[]>>first_x_assum drule>>
    rw[]>>irule_at Any sat_fml_SUBSET>>
    pop_assum (irule_at Any)>>
    metis_tac[get_fml_SUBSET,arb_delete_subset])
  >- (
    gvs[declare_pro_def,check_pro_def,conf_inv_def,is_fresh_def,wf_scp_def,AllCaseEqs()]>>
    `EVERY (λx. x > 0 ∨ lookup (var_lit x) sc.Ev = NONE) l` by (
      gvs[EVERY_MEM]>>rw[]>>last_x_assum drule>>
      simp[is_data_ext_lit_run_def,is_data_var_get_data_vars]>>
      CCONTR_TAC>>gvs[EXTENSION,domain_lookup]>>
      metis_tac[lookup_unit_cases,option_CLAUSES])>>
    rw[]
    >-
      gvs[INTER_INSERT]
    >- (
      gvs[dir_scp_def,EVERY_MEM]>>
      rw[]>>
      irule is_data_ext_lit_run_sem>>
      metis_tac[])
    >- (
      gvs[domain_lookup,EXTENSION]>>
      metis_tac[option_CLAUSES])
    (*
    >- (
      drule_at Any lookup_mk_Ev_disj>>
      rpt(disch_then (drule_at Any))>>
      rw[vars_scp_def])
    >- (
      simp[decomposable_scp_def]>>
      rw[]>> irule all_disjoint_mk_Ev_disj>>
      rpt (first_x_assum (irule_at Any))>>
      gvs[]) *)
    >- simp[deterministic_scp_def]
    >- (
      drule get_fml_insert_list_T>>
      disch_then (fn th => DEP_REWRITE_TAC[th])>>
      gvs[mk_enc_one_def])
    )
  >- (
    gvs[declare_sum_def,check_sum_def,conf_inv_def,is_fresh_def,INTER_INSERT,wf_scp_def]>>
    `EVERY (λx. x > 0 ∨ lookup (var_lit x) sc.Ev = NONE) [i;i0]` by (
      gvs[is_data_ext_lit_run_def,is_data_var_get_data_vars]>>
      CCONTR_TAC>>gvs[EXTENSION,domain_lookup]>>
      metis_tac[lookup_unit_cases,option_CLAUSES])>>
    rw[]
    >- (
      gvs[dir_scp_def,EVERY_MEM]>>
      rw[]>>
      irule is_data_ext_lit_run_sem>>
      metis_tac[])
    >- (
      gvs[domain_lookup,EXTENSION]>>
      metis_tac[option_CLAUSES])
    (*
    >- (
      drule_at Any lookup_mk_Ev>>
      rpt(disch_then (drule_at Any))>>
      rw[vars_scp_def])
    >- simp[decomposable_scp_def] *)
    >- (
      pop_assum kall_tac>>
      simp[deterministic_scp_def]>>
      rw[all_disjoint_2,DISJOINT_DEF,EXTENSION]>>
      rename1`w ∉ _`>>
      drule is_rup_sound>>strip_tac>>
      drule_at Any sat_scp_mk_enc_one>>
      disch_then (drule_at (Pos last))>>
      disch_then (drule_at (Pos last))>>
      disch_then (drule_at (Pos last))>>
      impl_tac >-
        (gvs[EXTENSION]>>metis_tac[])>>
      disch_then (qspecl_then[`w`] assume_tac)>>gvs[]>>
      rename1`agree_on _ w w'`>>
      CCONTR_TAC>>gvs[IN_DEF]>>
      imp_res_tac is_data_ext_lit_run_sem>>
      `sat_lit w' i` by (
        drule_all is_data_ext_lit_imp>>
        disch_then (qspecl_then [`w`,`F`] assume_tac)>>gvs[]
        >- (
          pop_assum mp_tac>>
          match_mp_tac EQ_IMPLIES>>
          match_mp_tac sat_lit_eq>>
          gvs[agree_on_def])>>
        gvs[EVERY_MEM,MEM_MAP])>>
      `sat_lit w' i0` by (
        qpat_x_assum`_ _ _ i` kall_tac>>
        drule_all is_data_ext_lit_imp>>
        disch_then (qspecl_then [`w`,`F`] assume_tac)>>gvs[]
        >- (
          pop_assum mp_tac>>
          match_mp_tac EQ_IMPLIES>>
          match_mp_tac sat_lit_eq>>
          gvs[agree_on_def])>>
        gvs[EVERY_MEM,MEM_MAP])>>
      gvs[sat_clause_def,SF DNF_ss]>>
      first_x_assum(qspec_then`w'` mp_tac)>>
      impl_tac >- (
        first_x_assum irule>>
        metis_tac[EVERY_CONJ])>>
      simp[])
    >- (
      drule get_fml_insert_list_T>>
      disch_then (fn th => DEP_REWRITE_TAC[th])>>
      gvs[mk_enc_one_def])
    )
  >- (
    gvs[declare_sko_def,check_sko_def,conf_inv_def,is_fresh_def,wf_scp_def,AllCaseEqs()]>>
    `EVERY (λx. x > 0 ∨ lookup (var_lit x) sc.Ev = NONE) l` by (
      gvs[EVERY_MEM]>>rw[]>>last_x_assum drule>>
      gvs[is_proj_lit_run_def,EXTENSION]>>
      rw[AllCasePreds()]>>last_x_assum drule>>rw[]>>
      `var_lit x < pc.nv + 1` by fs[]>>
      DISJ2_TAC>>
      metis_tac[option_CLAUSES,domain_lookup])>>
    (* drule domain_mk_Ev_disj>> *)
    rw[]
    >-
      gvs[INTER_INSERT]
    >- (
      gvs[dir_scp_def,EVERY_MEM,is_proj_lit_run_def,is_data_var_get_data_vars]>>
      rw[]>>last_x_assum drule>>
      rw[AllCasePreds()]>>
      simp[domain_lookup]>>
      gvs[GSYM is_data_var_get_data_vars,is_data_var_def])
    >- (
      gvs[domain_lookup,EXTENSION]>>
      metis_tac[option_CLAUSES])
    (*
    >- (
      drule_at Any lookup_mk_Ev_disj>>
      rpt(disch_then (drule_at Any))>>
      rw[vars_scp_def])
    >- (
      simp[decomposable_scp_def]>>
      rw[]>> irule all_disjoint_mk_Ev_disj>>
      rpt (first_x_assum (irule_at Any))>>
      gvs[]) *)
    >- simp[deterministic_scp_def]
    >- (
      drule get_fml_insert_one>>
      disch_then (fn th => DEP_REWRITE_TAC[th])>>
      gvs[mk_enc_one_def])
  )
QED

Theorem check_scpsteps_conf_inv:
  ∀xs fml sc.
  good_pc pc ∧
  check_scpsteps pc fml sc xs = SOME (fml',sc') ∧
  conf_inv pc sc ∧
  (∀w. EVERY (λn. sat_fml w (set (mk_enc_one n))) sc.scp ⇒
    sat_fml w (get_fml T fml)) ⇒
  conf_inv pc sc' ∧
  (∀w. EVERY (λn. sat_fml w (set (mk_enc_one n))) sc'.scp ⇒
    sat_fml w (get_fml T fml'))
Proof
  Induct>>rw[check_scpsteps_def] >>gvs[AllCaseEqs()]>>
  metis_tac[check_scpstep_conf_inv]
QED

Definition get_input_fml_def:
  get_input_fml nc fml =
    {c | ∃n b. n ≤ nc ∧
      lookup n fml = SOME (c:int list,b)}
End

(* Specialized type for SCPOG nodes with fast evaluation
  The mlstring is used as a bit-vector (but it stores word8s) *)
Datatype:
  scpnv =
  | Prov (num list) (int # mlstring)
  | Sumv (num + int) (num + int)
  | Skov (int # mlstring)
End

Definition sat_vec_def:
  sat_vec (off,bs) w =
  ∀i. off ≤ i ∧
    Num (i-off) < strlen bs ∧
    strsub bs (Num (i-off)) ≠ #"\^@" ⇒
    sat_lit w i
End

(* Phase 1: use vectors in representation *)
Definition sat_scpv_def:
  (sat_scpv (r:num) [] w = F) ∧
  (sat_scpv (r:num) ((v,n)::ns) w =
    if v = r then
      case n of
        Prov ls bs =>
          sat_vec bs w ∧
          EVERY (λi. sat_scpv i ns w) ls
      | Sumv ll rr =>
          (case ll of INL i => sat_scpv i ns w | INR l => sat_lit w l)
          ∨
          (case rr of INL i => sat_scpv i ns w | INR l => sat_lit w l)
      | Skov bs => sat_vec bs w
    else
      sat_scpv r ns w)
End

Definition prepend_def:
  prepend n x xs = if n = 0:num then xs else prepend (n-1) x (x::xs)
End

Definition to_flat_def:
  to_flat n l acc =
    case l of
    | [] => REVERSE acc
    | ((m,x)::xs) => to_flat (m+1) xs (SOME x :: prepend (m-n) NONE acc)
End

Triviality prepend_eq:
  ∀n x xs. prepend n x xs = REPLICATE n x ++ xs
Proof
  Induct \\ rewrite_tac [GSYM SNOC_REPLICATE]
  \\ fs [ADD1] \\ once_rewrite_tac [prepend_def] \\ fs []
QED

Triviality to_flat_lemma:
  ∀xs xs0 n.
    SORTED $< (MAP FST (xs0 ++ xs)) ∧ EVERY (λm. m < n) (MAP FST xs0) ∧
    (xs ≠ [] ⇒ n ≤ FST (HD xs)) ⇒
    ∃k. to_flat n xs (REVERSE $ GENLIST (ALOOKUP (xs0 ++ xs)) n) =
        GENLIST (ALOOKUP (xs0 ++ xs)) k ∧
        EVERY (λn. n < k) (MAP FST (xs0 ++ xs))
Proof
  Induct \\ fs []
  \\ once_rewrite_tac [to_flat_def] \\ fs [prepend_eq]
  >- (rw [] \\ qexists_tac ‘n’ \\ fs [])
  \\ rw [] \\ PairCases_on ‘h’ \\ gvs []
  \\ last_x_assum $ qspecl_then [‘xs0 ++ [(h0,h1)]’,‘h0+1’] mp_tac
  \\ impl_tac >-
   (asm_rewrite_tac [GSYM APPEND_ASSOC,APPEND,MAP_APPEND,MAP,FST,EVERY_APPEND]
    \\ fs [] \\ gvs [EVERY_MEM]
    \\ rw [] \\ res_tac \\ fs []
    \\ Cases_on ‘xs’ \\ fs []
    \\ fs [SORTED_APPEND_GEN]
    \\ gvs [less_sorted_eq])
  \\ qsuff_tac ‘(SOME h1:: (REPLICATE (h0 − n) NONE ++
                  REVERSE (GENLIST (ALOOKUP (xs0 ++ [(h0,h1)] ++ xs)) n))) =
      REVERSE (GENLIST (ALOOKUP (xs0 ++ [(h0,h1)] ++ xs)) (h0 + 1))’
  >- (strip_tac \\ fs [] \\ strip_tac \\ qexists_tac ‘k’ \\ fs [])
  \\ simp [GSYM ADD1,GENLIST,ALOOKUP_APPEND,AllCaseEqs(),
           ALOOKUP_NONE]
  \\ conj_tac
  >- (CCONTR_TAC \\ fs [EVERY_MEM] \\ res_tac \\ gvs [])
  \\ gvs [LESS_EQ_EXISTS]
  \\ once_rewrite_tac [ADD_COMM]
  \\ rewrite_tac [GENLIST_APPEND] \\ fs []
  \\ once_rewrite_tac [GSYM SWAP_REVERSE] \\ fs []
  \\ rewrite_tac [REPLICATE_GENLIST,GENLIST_FUN_EQ]
  \\ fs [ALOOKUP_NONE]
  \\ fs [SORTED_APPEND_GEN]
  \\ gvs [less_sorted_eq]
  \\ CCONTR_TAC \\ gvs [EVERY_MEM] \\ res_tac \\ fs []
QED

(* Tools to deal with sortedness *)

(* Makes a list strict and returns it in reverse *)
Definition mk_strict_aux_def:
  (mk_strict_aux x [] acc = x::acc) ∧
  (mk_strict_aux x (y::ys) acc =
    if x = y then
      mk_strict_aux x ys acc
    else mk_strict_aux y ys (x::acc))
End

Definition mk_strict_def:
  mk_strict ls =
  case ls of
    [] => []
  | (x::xs) => mk_strict_aux x xs []
End

Theorem mk_strict_aux_SORTED:
  ∀ls x acc.
  SORTED R (x::ls) ∧
  SORTED (\x y. R y x ∧ x ≠ y) (x::acc) ⇒
  SORTED (\x y. R y x ∧ x ≠ y) (mk_strict_aux x ls acc)
Proof
  Induct>>rw[mk_strict_aux_def]>>
  first_x_assum irule>>gvs[]
QED

Theorem mk_strict_SORTED:
  SORTED R ls ⇒
  SORTED (\x y. R y x ∧ x ≠ y) (mk_strict ls)
Proof
  rw[mk_strict_def]>>
  every_case_tac>>gvs[]>>
  irule mk_strict_aux_SORTED>>
  gvs[]
QED

Theorem mk_strict_aux_MEM:
  ∀ls y acc.
  MEM x (mk_strict_aux y ls acc) ⇔
  x = y ∨ MEM x ls ∨ MEM x acc
Proof
  Induct>>rw[mk_strict_aux_def]>>
  metis_tac[]
QED

Theorem mk_strict_MEM:
  MEM x (mk_strict ls) ⇔ MEM x ls
Proof
  rw[mk_strict_def]>>
  every_case_tac>>gvs[]>>
  simp[mk_strict_aux_MEM]
QED

Definition mk_strict_sorted_def:
  mk_strict_sorted ls =
  mk_strict (mergesort_tail (\x y. x ≥ y) ls)
End

Theorem mk_strict_sorted_SORTED:
  SORTED $< (mk_strict_sorted ls)
Proof
  rw[mk_strict_sorted_def]>>
  irule SORTED_weaken>>
  irule_at Any mk_strict_SORTED>>
  simp[]>>
  qexists_tac`(λx y. x ≥ y)`>>
  rw[]
  >- (
    DEP_REWRITE_TAC[mergesort_tail_correct]>>
    CONJ_ASM1_TAC
    >- (
      simp[total_def,transitive_def]>>
      intLib.ARITH_TAC)>>
    irule mergesort_sorted >>
    simp[])>>
  intLib.ARITH_TAC
QED

Theorem mk_strict_sorted_MEM:
  MEM x (mk_strict_sorted ls) ⇔ MEM x ls
Proof
  rw[mk_strict_sorted_def]>>
  simp[mk_strict_MEM]>>
  DEP_REWRITE_TAC[mergesort_tail_correct]>>
  CONJ_TAC
  >- (
    simp[total_def,transitive_def]>>
    intLib.ARITH_TAC)>>
  metis_tac[mergesort_mem,MEM]
QED

Definition opt_chr_def:
  (opt_chr opt =
  case opt of NONE => CHR 0 | (SOME ()) => CHR 1)
End

(* Turn a list of literals into the lit string format *)
Definition opt_hd_def:
  opt_hd xs = case xs of [] => 0 | (x::xs) => x
End

Definition to_lit_string_def:
  to_lit_string ls =
  let xs = mk_strict_sorted ls in
  let h = opt_hd xs in
  let ys = MAP (λi. (Num (i - h), ())) xs in
  let (yss:char list) = MAP opt_chr (to_flat 0 ys []) in
  (h,strlit yss)
End

(* Split literals into two parts:
  The data literals (INR) and the extension variables (INL) *)
Definition split_lit_def:
  split_lit pc l =
    let v = var_lit l in
    if is_data_var pc v
    then INR l
    else INL v
End

Definition split_lits_def:
  (split_lits pc [] accl accr = (accl,accr)) ∧
  (split_lits pc (l::ls) accl accr =
    case split_lit pc l of
      INL v => split_lits pc ls (v::accl) accr
    | INR l =>  split_lits pc ls accl (l::accr))
End

Definition scpn_to_scpnv_def:
  (scpn_to_scpnv pc (Pro ls) =
    let (lss,bss) = split_lits pc ls [] [] in
    Prov lss (to_lit_string bss)) ∧
  (scpn_to_scpnv pc (Sum ls) =
    case ls of [x;y] =>
      Sumv (split_lit pc x) (split_lit pc y)
    | _ => Sumv (INR 1) (INR 1)) ∧
  (scpn_to_scpnv pc (Sko ls) =
    Skov (to_lit_string ls))
End

Theorem EVERY_split_lits:
  ∀l accl accr.
  EVERY (is_data_ext_lit (get_data_vars pc) ns) l ∧
  split_lits pc l accl accr = (resl, resr) ⇒
  (EVERY P l ∧  EVERY P (MAP (\n. &n) accl) ∧ EVERY P accr ⇔
    EVERY P (MAP (\n. &n) resl) ∧ EVERY P resr)
Proof
  Induct>>rw[split_lits_def]>>
  gvs[split_lit_def,AllCaseEqs()]>>
  first_x_assum (drule_at Any)>>rw[]
  >- (
    gvs[is_data_ext_lit_def,is_data_var_get_data_vars]>>
    metis_tac[])>>
  metis_tac[]
QED

Theorem split_lits_props:
  ∀l accl accr.
  EVERY (is_data_ext_lit (get_data_vars pc) ns) l ∧
  EVERY (is_data_var pc o var_lit) accr ∧
  EVERY (λv. MEM v (MAP FST ns) ∧ v > 0) accl ∧
  split_lits pc l accl accr = (resl, resr) ⇒
  EVERY (is_data_var pc o var_lit) resr ∧
  EVERY (λv. MEM v (MAP FST ns) ∧ v > 0) resl
Proof
  Induct>>rw[split_lits_def]>>
  gvs[AllCaseEqs(),split_lit_def,is_data_ext_lit_def,is_data_var_get_data_vars]>>
  first_x_assum (drule_at Any)>>rw[]>>
  gvs[is_data_var_get_data_vars,var_lit_def]>>
  `Num (ABS h) > 0` by intLib.ARITH_TAC>>
  gvs[]
QED

Theorem EVERY_opt_hd_mk_strict_sorted:
  EVERY (λi. opt_hd (mk_strict_sorted ls) ≤ i) (mk_strict_sorted ls)
Proof
  rw[opt_hd_def]>>
  TOP_CASE_TAC>>rw[]>>
  `SORTED $< (mk_strict_sorted ls)` by metis_tac[mk_strict_sorted_SORTED]>>
  pop_assum mp_tac>>
  simp[]>>
  DEP_REWRITE_TAC[SORTED_EQ]>>
  simp[transitive_def]>>rw[]
  >-
    intLib.ARITH_TAC>>
  gvs[EVERY_MEM]
QED

Theorem sat_vec_to_lit_string:
  sat_vec (to_lit_string bss) w ⇔
  EVERY (sat_lit w) bss
Proof
  rw[to_lit_string_def,sat_vec_def]>>
  qmatch_goalsub_abbrev_tac`opt_hd xss`>>
  ‘SORTED $< xss’ by metis_tac[mk_strict_sorted_SORTED]>>
  `EVERY (λi. opt_hd xss ≤ i) xss` by metis_tac[EVERY_opt_hd_mk_strict_sorted]>>
  ‘SORTED $< (MAP FST ([] ++ MAP (λi. (Num (i − opt_hd xss),())) xss))’ by (
    simp[sorted_map,inv_image_def,MEM_MAP,PULL_EXISTS]>>
    match_mp_tac SORTED_weaken>>
    first_x_assum (irule_at Any)>>
    gvs[EVERY_MEM]>>
    rw[]>>
    res_tac>>simp[]>>
    intLib.ARITH_TAC)>>
  drule to_flat_lemma>>
  disch_then $ qspec_then ‘0’ mp_tac \\ fs [] >>
  rw[] >> simp[]>>
  eq_tac>>rw[EVERY_MEM]
  >- (
    gvs[Once (GSYM mk_strict_sorted_MEM)]>>
    gvs[EVERY_MEM]>>
    first_x_assum (irule_at Any)>>
    first_assum drule>>
    strip_tac>>
    DEP_REWRITE_TAC[EL_MAP,EL_GENLIST]>>simp[]>>
    first_x_assum (irule_at Any)>>simp[MEM_MAP,PULL_EXISTS]>>
    first_assum (irule_at Any)>>simp[]>>
    simp[opt_chr_def]>>
    TOP_CASE_TAC>>simp[]>>
    gvs[ALOOKUP_NONE,MEM_MAP,PULL_FORALL])>>
  gvs[EL_MAP,opt_chr_def,AllCaseEqs()]>>
  first_assum (irule_at Any)>>simp[]>>
  gvs[GSYM IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]>>
  drule ALOOKUP_MEM>>
  rw[MEM_MAP]>>
  gvs[EVERY_MEM]>>
  first_assum drule>>
  strip_tac>>
  rename1`MEM ii xss`>>
  qsuff_tac`ii = i`
  >-
    metis_tac[mk_strict_sorted_MEM]>>
  intLib.ARITH_TAC
QED

Theorem var_lit_pos:
  x > 0 ⇒
  var_lit x > 0
Proof
  rw[var_lit_def]>>
  intLib.ARITH_TAC
QED

Definition map_scpnv_def:
  map_scpnv pc ns = MAP (λi,n. (i,scpn_to_scpnv pc n)) ns
End

Theorem scpn_to_scpnv_sound:
  ∀ns r.
  dir_scp (get_data_vars pc) P E ns ∧
  P ∩ set (MAP FST ns) = {} ∧
  (get_data_vars pc) ∩ set (MAP FST ns) = {} ∧
  EVERY wf_scp ns ∧
  r ∈ set (MAP FST ns) ∧ r > 0 ⇒
  (sat_scp T (&r) ns w ⇔
  sat_scpv r (map_scpnv pc ns) w)
Proof
  simp[map_scpnv_def]>>
  Induct
  >- rw[]>>
  rpt gen_tac>>
  Cases_on`h`>>
  rename1`(i,x)`>>
  reverse (Cases_on`r = i`>>rw[])>>
  gvs[dir_scp_def,sat_scp_def,sat_scpv_def,INTER_INSERT,AllCaseEqs()]>>
  `&i > 0` by intLib.ARITH_TAC>>
  simp[match_lit_def]>>
  Cases_on`x`>>gvs[scpn_to_scpnv_def]
  >- (
    pairarg_tac>>simp[]>>
    drule_all EVERY_split_lits>>
    simp[]>>
    disch_then kall_tac>>
    drule split_lits_props>>
    disch_then (drule_at Any)>>
    simp[]>>rw[]>>
    ho_match_mp_tac (METIS_PROVE [] ``(P ⇔ B) ∧ (Q ⇔ A) ⇒ (P ∧ Q ⇔ A ∧ B)``)>>
    rw[]
    >- (
      simp[sat_vec_to_lit_string]>>
      match_mp_tac EVERY_CONG>>rw[]>>
      simp[Once EQ_SYM_EQ]>>
      match_mp_tac sat_scp_ALOOKUP_NONE>>
      gvs[EVERY_MEM,ALOOKUP_NONE]>>
      first_x_assum drule>>
      gvs[is_data_var_get_data_vars,EXTENSION]>>
      metis_tac[MEM_MAP])
    >- (
      gvs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
      ho_match_mp_tac equiv_imp_imp>>
      rw[]>>
      metis_tac[]))
  >- (
    gvs[wf_scp_def]>>
    TOP_CASE_TAC>>gvs[]>>
    TOP_CASE_TAC>>gvs[]>>
    every_case_tac>>
    last_x_assum (fn th => DEP_REWRITE_TAC[GSYM th])>>
    gvs[split_lit_def,is_data_ext_lit_def,is_data_var_get_data_vars,EXTENSION,MEM_MAP]>>
    DEP_REWRITE_TAC[GSYM (sat_scp_ALOOKUP_NONE |> Q.GEN`sko` |> Q.SPEC`T`)]>>
    simp[ALOOKUP_NONE]>>
    metis_tac[var_lit_pos,MEM_MAP,var_lit_int])
  >- (
    simp[sat_vec_to_lit_string]>>
    match_mp_tac EVERY_CONG>>rw[]>>
    simp[Once EQ_SYM_EQ]>>
    match_mp_tac sat_scp_ALOOKUP_NONE>>
    gvs[EVERY_MEM,ALOOKUP_NONE]>>
    first_x_assum drule>>
    gvs[is_data_var_get_data_vars,EXTENSION]>>
    metis_tac[MEM_MAP])
QED

(* dir_scpv is directed *)
Definition dir_scpv_def:
  (dir_scpv [] = T) ∧
  (dir_scpv ((v,n)::ns) =
    (dir_scpv ns ∧
    case n of
      Prov ls bs =>
        EVERY (λl. MEM l (MAP FST ns)) ls
    | Sumv ll rr =>
        (case ll of INL l => MEM l (MAP FST ns) | INR _ => T) ∧
        (case rr of INL l => MEM l (MAP FST ns) | INR _ => T)
    | Skov bs => T))
End

Theorem dir_scp_dir_scpv:
  ∀ns.
  dir_scp (get_data_vars pc) P E ns ⇒
  dir_scpv (map_scpnv pc ns)
Proof
  simp[map_scpnv_def]>>
  Induct>>rw[dir_scpv_def,dir_scp_def]>>
  pairarg_tac>>gvs[dir_scpv_def,dir_scp_def,AllCasePreds()]>>
  gvs[scpn_to_scpnv_def]
  >- (
    pairarg_tac>>gvs[]>>
    drule split_lits_props>>
    disch_then (drule_at Any)>>
    simp[MEM_MAP,PULL_EXISTS,EXISTS_PROD]>>
    rw[EVERY_MEM]>>
    metis_tac[])
  >- (
    every_case_tac>>gvs[]>>
    gvs[split_lit_def,is_data_ext_lit_def,is_data_var_get_data_vars,MEM_MAP,PULL_EXISTS]>>
    simp[EXISTS_PROD]>>
    metis_tac[PAIR,FST,SND])
QED

Definition vec_lookup_def:
  vec_lookup opt_vec n =
    if n < length opt_vec then sub opt_vec n else NONE
End

Definition spt_to_vec_def:
  spt_to_vec t =
    Vector (to_flat 0 (toSortedAList t) [])
End

Theorem vec_lookup_num_spt_to_vec:
  vec_lookup (spt_to_vec t) n = lookup n t
Proof
  fs [spt_to_vec_def,vec_lookup_def,length_def,sub_def]
  \\ ‘SORTED $< (MAP FST ([] ++ toSortedAList t))’ by fs [SORTED_toSortedAList]
  \\ drule to_flat_lemma
  \\ disch_then $ qspec_then ‘0’ mp_tac \\ fs []
  \\ strip_tac \\ fs [ALOOKUP_toSortedAList] \\ rw []
  \\ Cases_on ‘lookup n t’ \\ gvs []
  \\ gvs [GSYM ALOOKUP_toSortedAList]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [EVERY_MEM,MEM_MAP,PULL_EXISTS] \\ res_tac \\ fs []
QED

Definition alist_to_vec_def:
  alist_to_vec ls =
    Vector (to_flat 0 (mergesort_tail (λx y. FST x ≤ FST y) ls) [])
End

Theorem ALL_DISTINCT_ALOOKUP_PERM:
  ALL_DISTINCT (MAP FST ls) ∧
  PERM ls ls' ⇒
  ALOOKUP ls = ALOOKUP ls'
Proof
  rw[]>>
  match_mp_tac ALOOKUP_ALL_DISTINCT_PERM_same>>
  gvs[PERM_MAP]>>
  rw[EXTENSION,PERM_MEM_EQ]
QED

Theorem vec_lookup_alist_to_vec:
  ALL_DISTINCT (MAP FST ls) ⇒
  vec_lookup (alist_to_vec ls) n = ALOOKUP ls n
Proof
  rw[]>>
  fs [alist_to_vec_def,vec_lookup_def,length_def,sub_def]>>
  DEP_REWRITE_TAC[mergesort_tail_correct]>>
  CONJ_ASM1_TAC
  >- (
    simp[total_def,transitive_def]>>
    intLib.ARITH_TAC)
  \\ ‘SORTED $<= (MAP FST ([] ++ mergesort (λx y. FST x ≤ FST y) ls))’ by
    (simp[sorted_map,inv_image_def]>>
    irule mergesort_sorted >>
    simp[])
  \\ `PERM ls (mergesort (λx y. FST x ≤ FST y) ls)` by metis_tac[mergesort_perm]
  \\ ‘SORTED $< (MAP FST ([] ++ mergesort (λx y. FST x ≤ FST y) ls))’ by
    (drule_at Any ALL_DISTINCT_SORTED_WEAKEN>>
    disch_then irule>>
    simp[]>>
    metis_tac[ALL_DISTINCT_PERM,PERM_MAP])
  \\ drule to_flat_lemma
  \\ disch_then $ qspec_then ‘0’ mp_tac \\ fs []
  \\ rw[] \\ gvs[]
  >-
    metis_tac[ALL_DISTINCT_ALOOKUP_PERM]
  >>
    gvs[EVERY_MAP,EVERY_MEM,mergesort_mem,ALOOKUP_NONE,MEM_MAP]>>
    rw[]>>CCONTR_TAC>>gvs[]
QED

(* Phase 2: use vector lookup in representation *)
Definition vec_sat_scpv_def:
  (vec_sat_scpv iter (r:num) ov w =
    if iter = 0n then F
    else
      let iter = iter-1 in
      case vec_lookup ov r of
        NONE => F
      | SOME n =>
        case n of
          Prov ls bs =>
            sat_vec bs w ∧
            EVERY (λi. vec_sat_scpv iter i ov w) ls
        | Sumv ll rr =>
            (case ll of INL i => vec_sat_scpv iter i ov w | INR l => sat_lit w l)
            ∨
            (case rr of INL i => vec_sat_scpv iter i ov w | INR l => sat_lit w l)
      | Skov bs => sat_vec bs w)
End

Theorem vec_sat_scpv_eq_gen:
  ∀ns r fuel.
  (∀i. MEM i (MAP FST ns) ⇒ vec_lookup ov i = ALOOKUP ns i) ∧
  ALL_DISTINCT (MAP FST ns) ∧
  dir_scpv ns ∧
  MEM r (MAP FST ns) ∧
  LENGTH ns ≤ fuel ⇒
  vec_sat_scpv fuel r ov w =
  sat_scpv r ns w
Proof
  Induct>>rw[]>>
  simp[Once vec_sat_scpv_def,sat_scpv_def,dir_scpv_def]>>
  Cases_on`h`>>rw[sat_scpv_def]>>gvs[dir_scpv_def]
  >- (
    TOP_CASE_TAC>>gvs[]
    >- (
      ho_match_mp_tac (METIS_PROVE [] ``(P ⇔ A) ∧ (Q ⇔ B) ⇒ (P ∧ Q ⇔ A ∧ B)``)>>
      rw[EVERY_MEM]>>
      ho_match_mp_tac equiv_imp_imp>>rw[]>>
      first_x_assum irule>>
      rw[]
      >- metis_tac[]>>
      gvs[EVERY_MEM])
    >- (
      every_case_tac>>gvs[]>>
      qpat_x_assum `∀r. _` (fn th => DEP_REWRITE_TAC[th])>>
      rw[]>>
      metis_tac[]))>>
  last_x_assum (qspecl_then [`r`,`fuel`] mp_tac)>>
  impl_tac >- (
    rw[]>>
    metis_tac[])>>
  disch_then sym_sub_tac>>
  simp[Once vec_sat_scpv_def,SimpRHS]
QED

Theorem vec_sat_scpv_eq:
  ALL_DISTINCT (MAP FST ns) ∧
  dir_scpv ns ∧
  MEM r (MAP FST ns) ∧
  LENGTH ns ≤ fuel ⇒
  vec_sat_scpv fuel r (alist_to_vec ns) w
    = sat_scpv r ns w
Proof
  rw[]>>
  irule vec_sat_scpv_eq_gen>>
  gvs[vec_lookup_alist_to_vec]
QED

(* TODO *)
Definition wf_clause_def:
  wf_clause (C:int list) ⇔ ¬ MEM 0 C
End

Definition wf_fml_def:
  wf_fml fml ⇔
  ∀C tag. (C,tag) ∈ misc$range fml ⇒ wf_clause C
End

(* Phase 3: underapproximation *)

(* A literal i NOT being assigned causes sat_vec to return F *)
Definition falsify_lit_def:
  falsify_lit (off,bs) i ⇔
  off ≤ i ∧ Num (i-off) < strlen bs ∧
    strsub bs (Num (i-off)) ≠ #"\^@"
End

Theorem falsify_lit_thm:
  falsify_lit (off,bs) i ∧
  ¬sat_lit w i
  ⇒
  ¬sat_vec (off,bs) w
Proof
  rw[sat_vec_def,falsify_lit_def]>>
  first_x_assum (irule_at Any)>>
  rw[]
QED

Definition falsify_vec_def:
  falsify_vec obs c ⇔
  EXISTS (λl. falsify_lit obs l) c
End

Theorem falsify_vec_thm:
  falsify_vec obs c ∧
  wf_clause c ∧
  ¬sat_clause w c
  ⇒
  ¬sat_vec obs w
Proof
  rw[falsify_vec_def,EXISTS_MEM,sat_clause_def]>>
  gvs[wf_clause_def]>>
  Cases_on`obs`>>irule falsify_lit_thm>>
  metis_tac[]
QED

(* Overapproximates F *)
Definition falsify_vec_sat_scpv_def:
  (falsify_vec_sat_scpv iter (r:num) ov cd cp =
    if iter = 0n then T
    else
      let iter = iter-1 in
      case vec_lookup ov r of
        NONE => T
      | SOME n =>
        case n of
          Prov ls bs =>
            falsify_vec bs cd ∨
            EXISTS (λi. falsify_vec_sat_scpv iter i ov cd cp) ls
        | Sumv ll rr =>
            (case ll of INL i => falsify_vec_sat_scpv iter i ov cd cp | INR l => MEM l cd)
            ∧
            (case rr of INL i => falsify_vec_sat_scpv iter i ov cd cp | INR l => MEM l cd)
      | Skov bs => falsify_vec bs cp)
End

Theorem falsify_vec_sat_scpv_thm:
  ∀iter r.
  falsify_vec_sat_scpv iter r ov cd cp ∧
  wf_clause cd ∧ wf_clause cp ∧
  ¬sat_clause w cd ∧  ¬sat_clause w cp
  ⇒
  ¬vec_sat_scpv iter r ov w
Proof
  Induct>>rw[Once falsify_vec_sat_scpv_def,Once vec_sat_scpv_def]>>
  gvs[AllCasePreds()]
  >-
    metis_tac[falsify_vec_thm]
  >- (
    gvs[EXISTS_MEM]>>
    metis_tac[])
  >- (
    gvs[sat_clause_def,wf_clause_def]>>
    metis_tac[])
  >- (
    gvs[sat_clause_def,wf_clause_def]>>
    metis_tac[])
  >- (
    gvs[sat_clause_def,wf_clause_def]>>
    metis_tac[])
  >- metis_tac[falsify_vec_thm]
QED

(* Phase 4: exploit ddnnf *)

Definition clean_vec_def:
  (clean_vec [] c ev acc = acc) ∧
  (clean_vec (l::ls) c ev acc =
    if c = [] then acc
    else
    case vec_lookup ev l of
      NONE => acc
    | SOME (s: unit option vector) =>
      let (rc,lc) = PARTITION (λx. vec_lookup s (var_lit x) = NONE) c in
      if lc = []
      then
        clean_vec ls rc ev acc
      else
        clean_vec ls rc ev ((l,lc)::acc))
End

(* Overapproximates F *)
Definition efalsify_vec_sat_scpv_def:
  (efalsify_vec_sat_scpv iter (r:num) ov ev c =
    if iter = 0n then T
    else
      case vec_lookup ov r of
        NONE => T
      | SOME n =>
        let iter = iter-1 in
        case n of
          Prov ls bs =>
            falsify_vec bs c ∨
            let lcs = clean_vec ls c ev [] in
            EXISTS (λ(i,ic). efalsify_vec_sat_scpv iter i ov ev ic) lcs
        | Sumv ll rr =>
            (case ll of INL i => efalsify_vec_sat_scpv iter i ov ev c | INR l => MEM l c)
            ∧
            (case rr of INL i => efalsify_vec_sat_scpv iter i ov ev c | INR l => MEM l c)
      | Skov bs => falsify_vec bs c)
End

Definition final_conditions_def:
  final_conditions fml r nc scp ⇔
    [r] ∈ get_fml F fml ∧
    ∀C w.
      C ∈ get_input_fml nc fml ∧
      ¬sat_clause w C ⇒
      ¬sat_scp T r scp w
End

Theorem get_input_fml_insert_one:
  insert_one b fml n C = SOME fml' ⇒
  get_input_fml nc fml ⊆ get_input_fml nc fml'
Proof
  rw[insert_one_def,AllCaseEqs(),lookup_insert,get_input_fml_def,SUBSET_DEF]>>
  gvs[lookup_insert,AllCaseEqs()]>>
  metis_tac[option_CLAUSES]
QED

Theorem get_input_fml_insert_list:
  ∀cs n fml.
  insert_list b fml n cs = SOME fml' ⇒
  get_input_fml nc fml ⊆ get_input_fml nc fml'
Proof
  Induct>>rw[insert_list_def]>>
  gvs[AllCaseEqs()]>>
  drule get_input_fml_insert_one>>
  metis_tac[SUBSET_TRANS]
QED

Theorem get_input_fml_arb_delete:
  ∀ls fml.
  arb_delete nc ls fml = SOME fml' ⇒
  get_input_fml nc fml ⊆ get_input_fml nc fml'
Proof
  Induct>>rw[arb_delete_def]>>
  gvs[AllCaseEqs()]>>
  irule SUBSET_TRANS>>
  first_x_assum drule>>
  disch_then (irule_at Any)>>
  simp[get_input_fml_def,SUBSET_DEF,lookup_delete]>>
  metis_tac[]
QED

Theorem get_fml_T_arb_delete:
  ∀ls fml.
  arb_delete nc ls fml = SOME fml' ⇒
  get_fml T fml' = get_fml T fml
Proof
  Induct>>rw[arb_delete_def]>>
  gvs[AllCaseEqs()]>>
  first_x_assum drule>>
  rw[get_fml_def,EXTENSION,lookup_delete]>>
  metis_tac[option_CLAUSES,PAIR,FST,SND]
QED

(*
  The input clauses are never deleted.
*)
Theorem check_scpstep_preserved_1:
  check_scpstep pc fml sc scpstep = SOME (fml',sc') ⇒
  get_input_fml pc.nc fml ⊆ get_input_fml pc.nc fml'
Proof
  strip_tac>>
  Cases_on`scpstep`>>
  gvs[check_scpstep_def,AllCaseEqs()]>>rw[]>>
  metis_tac[get_input_fml_insert_one,get_input_fml_arb_delete,get_input_fml_insert_list]
QED

Theorem check_scpsteps_preserved_1:
  ∀xs fml sc.
  check_scpsteps pc fml sc xs = SOME (fml',sc') ⇒
  get_input_fml pc.nc fml ⊆ get_input_fml pc.nc fml'
Proof
  Induct>>rw[check_scpsteps_def] >>gvs[AllCaseEqs()]>>
  metis_tac[check_scpstep_preserved_1,SUBSET_TRANS]
QED

Theorem check_scpstep_preserved_2:
  check_scpstep pc fml sc scpstep = SOME (fml',sc') ∧
  EVERY (λn. set (mk_enc_one n) ⊆ get_fml T fml) sc.scp ⇒
  EVERY (λn. set (mk_enc_one n) ⊆ get_fml T fml') sc'.scp
Proof
  strip_tac>>
  Cases_on`scpstep`>>
  gvs[check_scpstep_def,AllCaseEqs(),EVERY_MEM]>>rw[]
  >-
    gvs[declare_root_def,AllCaseEqs()]
  >- (
    drule get_fml_insert_one>>
    rw[]>>
    first_x_assum drule>>
    simp[SUBSET_DEF] )
  >-
    metis_tac[get_fml_T_arb_delete]
  >- (
    drule get_fml_insert_list_T>>
    rw[]>>
    gvs[declare_pro_def,AllCaseEqs(),mk_enc_one_def]>>
    metis_tac[SUBSET_UNION,SUBSET_TRANS])
  >- (
    drule get_fml_insert_list_T>>
    rw[]>>
    gvs[declare_sum_def,AllCaseEqs(),mk_enc_one_def]>>
    metis_tac[SUBSET_UNION,SUBSET_TRANS])
  >- (
    drule get_fml_insert_one>>
    rw[]>>
    gvs[declare_sko_def,AllCaseEqs(),mk_enc_one_def]>>
    first_x_assum drule>>
    simp[SUBSET_DEF])
QED

Theorem check_scpsteps_preserved_2:
  ∀xs fml sc.
  check_scpsteps pc fml sc xs = SOME (fml',sc') ∧
  EVERY (λn. set (mk_enc_one n) ⊆ get_fml T fml) sc.scp ⇒
  EVERY (λn. set (mk_enc_one n) ⊆ get_fml T fml') sc'.scp
Proof
  Induct>>rw[check_scpsteps_def] >>gvs[AllCaseEqs()]>>
  metis_tac[check_scpstep_preserved_2,SUBSET_TRANS]
QED

Theorem final_conditions_extends_over:
  D ∩ E = {} ∧ P ∩ E = {} ∧
  dir_scp D P E ns ∧
  EVERY wf_scp ns ∧ r ≠ 0 ∧
  is_data_ext_lit D ns r ∧
  ALL_DISTINCT (MAP FST ns) ∧
  EVERY (λn. set (mk_enc_one n) ⊆ get_fml T fml) ns ∧
  final_conditions fml r nc ns ⇒
  extends_over D (λw. sat_fml w (get_fml F fml))
    (sat_scp F r ns) ∧
  extends_over D (sat_scp T r ns)
    (λw. sat_fml w (get_input_fml nc fml))
Proof
  rw[final_conditions_def,AllCasePreds()]>>
  simp[]>>
  rw[extends_over_def]
  >- (
    qexists_tac`w`>>simp[]>>
    DEP_REWRITE_TAC[GEN_ALL EVERY_mk_enc_one_sat_scp]>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    first_x_assum (irule_at Any)>>
    simp[]>>
    CONJ_TAC >- (
      gvs[sat_fml_def,EVERY_MEM,SUBSET_DEF]>>rw[]>>
      last_x_assum drule_all>>
      rw[]>>first_x_assum irule>>
      metis_tac[get_fml_imply])>>
    gvs[sat_fml_def,get_fml_def,PULL_EXISTS]>>
    first_x_assum drule>>
    simp[sat_clause_def])
  >- (
    qexists_tac`w`>>simp[]>>
    gvs[sat_fml_def]>>
    metis_tac[])
QED

Theorem get_fml_build_fml_F[simp]:
  get_fml F (build_fml n fmlls) = set fmlls
Proof
  rw[get_fml_def,lookup_build_fml,EXTENSION]>>
  eq_tac>>rw[MEM_EL]
  >-
    (qexists_tac`n'-n`>>simp[])>>
  qexists_tac`n+n'`>>simp[]
QED

Theorem get_fml_build_fml_T[simp]:
  get_fml T (build_fml n fmlls) = {}
Proof
  rw[get_fml_def,lookup_build_fml,EXTENSION]
QED

Theorem get_input_fml_build_fml[simp]:
  get_input_fml (LENGTH fmlls) (build_fml 1 fmlls) = set fmlls
Proof
  rw[get_input_fml_def,lookup_build_fml,EXTENSION]>>
  eq_tac>>rw[MEM_EL]
  >- (qexists_tac`n-1`>>simp[])>>
  qexists_tac`n+1`>>simp[]
QED

Definition falsify_top_def:
  falsify_top pc iter (r:num) ov c =
    let c = FILTER (\i. i ≠ 0) c in
    let (cd,cp) = PARTITION (λl. is_data_var pc (var_lit l)) c in
      falsify_vec_sat_scpv iter (r:num) ov cd cp
End

Definition get_node_vars_def:
  (get_node_vars vm [] accl accr = (accl,accr)) ∧
  (get_node_vars vm (i::is) accl accr =
    let v = var_lit i in
    case lookup v vm of
      NONE => get_node_vars vm is (v::accl) accr
    | SOME vs => get_node_vars vm is accl (vs::accr))
End

Definition big_union_def:
  big_union ts = FOLDL (merge (λx y:num. x ≤ y)) [] ts
End

Definition mk_pro_vm_def:
  mk_pro_vm v ls vm =
    let (l,ls) = get_node_vars vm ls [] [] in
    let vs = big_union (l::ls) in
    if SORTED $< vs
    then SOME (insert v vs vm)
    else NONE
End

Definition mk_strict_sorted_num_def:
  mk_strict_sorted_num ls =
  mk_strict (mergesort_tail (\x y:num. y ≤ x) ls)
End

Theorem mk_strict_sorted_num_SORTED:
  SORTED $< (mk_strict_sorted_num ls)
Proof
  rw[mk_strict_sorted_num_def]>>
  irule SORTED_weaken>>
  irule_at Any mk_strict_SORTED>>
  simp[]>>
  qexists_tac`(λx y. y <= x)`>>
  rw[]>>
  DEP_REWRITE_TAC[mergesort_tail_correct]>>
  CONJ_ASM1_TAC
  >- (
    simp[total_def,transitive_def]>>
    intLib.ARITH_TAC)>>
  irule mergesort_sorted >>
  simp[]
QED

Theorem mk_strict_sorted_num_MEM:
  MEM x (mk_strict_sorted_num ls) ⇔ MEM x ls
Proof
  rw[mk_strict_sorted_num_def]>>
  simp[mk_strict_MEM]>>
  DEP_REWRITE_TAC[mergesort_tail_correct]>>
  CONJ_TAC
  >- (
    simp[total_def,transitive_def]>>
    intLib.ARITH_TAC)>>
  metis_tac[mergesort_mem,MEM]
QED

Definition mk_sum_vm_def:
  mk_sum_vm v ls vm =
    let (l,ls) = get_node_vars vm ls [] [] in
    let vs = big_union (l::ls) in
      SOME (insert v (mk_strict_sorted_num vs) vm)
End

Definition mk_sko_vm_def:
  mk_sko_vm  v ls vm =
    let vs = mergesort_tail (\x y. x ≤ y) (MAP var_lit ls) in
    if SORTED $< vs
    then SOME (insert v vs vm)
    else NONE
End

(* Check decomposable_scp T r scp *)
Definition check_dec_def:
  (check_dec [] = SOME LN) ∧
  (check_dec ((v,n)::ns) =
    case check_dec ns of NONE => NONE
    | SOME vm =>
    (case n of
      Pro ls => mk_pro_vm v ls vm
    | Sum ls => mk_sum_vm v ls vm
    | Sko ls => mk_sko_vm v ls vm ))
End

Theorem set_merge:
  set (merge R xs ys) =
  set xs ∪ set ys
Proof
  rw[EXTENSION]>>
  `PERM (xs++ys) (merge R xs ys)` by metis_tac[merge_perm]>>
  drule PERM_MEM_EQ>>
  simp[]
QED

Theorem set_FOLDL_union:
  ∀ls tt.
  set (FOLDL (merge R) tt ls) =
  set tt ∪ BIGUNION (IMAGE set (set ls))
Proof
  Induct>>rw[]>>
  simp[set_merge,UNION_ASSOC]
QED

Theorem set_big_union:
  set (big_union ls) =
  BIGUNION (IMAGE set (set ls))
Proof
  rw[big_union_def]>>
  DEP_REWRITE_TAC[set_FOLDL_union]>>
  simp[]
QED

Theorem check_dec_decomposable_scp:
  ∀ns vm.
  check_dec ns = SOME vm ⇒
  (∀n vs.
    case lookup n vm of
      NONE => ALOOKUP ns n = NONE
    | SOME vs =>
      SORTED $< vs ∧
      vars_scp T (&n) ns = set vs) ∧
  (∀r. decomposable_scp T r ns)
Proof
  Induct>>simp[check_dec_def]
  >-
    rw[decomposable_scp_def]>>
  Cases>>rpt gen_tac>>
  simp[check_dec_def,decomposable_scp_def]>>
  TOP_CASE_TAC>>gvs[]>>
  strip_tac>>
  gvs[AllCaseEqs()]
  >- (
    gvs[mk_pro_vm_def,vars_scp_def]>>
    pairarg_tac>>gvs[]>>
    rw[lookup_insert]>>gvs[]
    >- (
      simp[set_big_union]>>
      cheat)
    >- cheat)
  >- (
    gvs[mk_sum_vm_def,vars_scp_def]>>
    pairarg_tac>>gvs[]>>
    rw[lookup_insert]>>gvs[]
    >-
      metis_tac[mk_strict_sorted_num_SORTED]>>
    cheat)
  >- (
    gvs[mk_sko_vm_def,vars_scp_def]>>
    rw[lookup_insert]>>gvs[]>>
    cheat)
QED

Definition check_inputs_scp_def:
  check_inputs_scp r pc scp fml =
  if check_dec scp = NONE then NONE
  else
  if is_data_var pc (var_lit r)
  then
    if (∀c. c ∈ get_input_fml pc.nc fml ⇒ MEM r c)
    then
      SOME (INR (r,scp))
    else NONE
  else
    let ns = map_scpnv pc scp in
    let ov = alist_to_vec ns in
    let iter = LENGTH scp in
    if (∀c. c ∈ get_input_fml pc.nc fml ⇒ falsify_top pc iter (var_lit r) ov c)
    then
      SOME (INR (r,scp))
    else NONE
End

Definition check_final_def:
  check_final pc sc fml =
  case sc.root of
    NONE => NONE
  | SOME r =>
    if r = 0
    then
      if [] ∈ get_fml F fml
      then SOME (INL())
      else NONE
    else
      if is_data_ext_lit_run pc sc.Ev r ∧
         [r] ∈ get_fml F fml
      then
        check_inputs_scp r pc sc.scp fml
      else
        NONE
End

Theorem MAP_FST_map_scpnv[simp]:
  MAP FST (map_scpnv pc ns) =
  MAP FST ns
Proof
  rw[map_scpnv_def,MAP_MAP_o,o_DEF,MAP_EQ_f]>>
  pairarg_tac>>rw[]
QED

Theorem LENGTH_map_scpnv[simp]:
  LENGTH (map_scpnv pc ns) =
  LENGTH ns
Proof
  rw[map_scpnv_def]
QED

Theorem falsify_top_thm:
  falsify_top pc iter r ov c ∧
  ¬sat_clause w c
  ⇒
  ¬vec_sat_scpv iter r ov w
Proof
  rw[falsify_top_def]>>
  pairarg_tac>>gvs[]>>
  irule falsify_vec_sat_scpv_thm>>
  first_x_assum (irule_at (Pos last))>>
  gvs[PARTITION_DEF]>>
  qpat_x_assum`PART _ _ _ _ = _` (assume_tac o SYM)>>
  drule PART_MEM >>
  rw[MEM_FILTER]>>gvs[wf_clause_def,sat_clause_def]>>
  metis_tac[]
QED

(* Guarantees preservation of all models
  + decomposability
  + deterministic

  Note that there are other minor syntactic well-formedness
  properties of the POG that are implied as well by conf_inv.
  For example, the output POG satisfies dir_scp. *)
Theorem scpog_soundness:
  good_pc pc ∧ pc.nc = LENGTH fmlls ∧
  EVERY (λC. vars_clause C ⊆ count (pc.nv + 1)) fmlls ∧
  check_scpsteps pc (build_fml 1 fmlls) init_sc xs = SOME (fml', sc') ∧
  check_final pc sc' fml' = SOME (INR (r,ns)) ⇒
  models (get_data_vars pc) (sat_scp F r ns) =
    models (get_data_vars pc) {w | sat_fml w (set fmlls)} ∧
  decomposable_scp F r ns ∧
  deterministic_scp F r ns
Proof
  strip_tac>>
  gvs[check_final_def,AllCaseEqs()]>>
  drule check_scpsteps_extends_over>>
  disch_then drule>>
  simp[init_sc_def]>>
  impl_tac >- (
    simp[SUBSET_DEF,vars_fml_def,PULL_EXISTS]>>
    gvs[EVERY_MEM,SUBSET_DEF]>>
    metis_tac[])>>
  strip_tac>>
  drule check_scpsteps_conf_inv>>
  disch_then drule>>
  impl_tac>- (
    gvs[conf_inv_def,init_sc_def,dir_scp_def,decomposable_scp_def,deterministic_scp_def])>>
  `r' = r ∧ ns = sc'.scp` by
    gvs[check_inputs_scp_def,AllCaseEqs()]>>
  gvs[]>>
  `decomposable_scp T r sc'.scp` by
    (gvs[check_inputs_scp_def]>>
    gvs[GSYM IS_SOME_EQ_NOT_NONE, IS_SOME_EXISTS]>>
    drule check_dec_decomposable_scp>>
    simp[])>>
  reverse(rw[conf_inv_def])
  >- (
    gvs[check_inputs_scp_def,AllCaseEqs()]>>
    metis_tac[decomposable_scp_T_to_F])>>
  drule_all is_data_ext_lit_run_sem>>
  rw[]>>
  drule_at Any final_conditions_extends_over>>
  gvs[]>>
  disch_then (drule_at Any)>>
  disch_then (qspecl_then [`pc.nc`,`fml'`] mp_tac)>>
  impl_tac >- (
    CONJ_ASM1_TAC >- (
      gvs[good_pc_def,SUBSET_DEF,EXTENSION]>>
      metis_tac[] )>>
    CONJ_ASM1_TAC >- (
      gvs[good_pc_def,SUBSET_DEF,EXTENSION]>>
      metis_tac[])>>
    CONJ_TAC >- (
      irule check_scpsteps_preserved_2>>
      first_x_assum (irule_at Any)>>
      simp[init_sc_def])>>
    rw[final_conditions_def]>>
    gvs[check_inputs_scp_def,AllCaseEqs()]
    >- (
      first_x_assum drule>>
      DEP_REWRITE_TAC[sat_scp_ALOOKUP_NONE]>>
      gvs[sat_clause_def]>>
      CONJ_TAC >- (
        gvs[ALOOKUP_NONE,is_data_var_get_data_vars,good_pc_def,SUBSET_DEF,EXTENSION]>>
        metis_tac[])>>
      metis_tac[])
    >- (
      gvs[is_data_ext_lit_run_def]>>
      first_x_assum drule>> strip_tac>>
      (* Phase 3 *)
      drule_all falsify_top_thm>>
      (* Phase 2 *)
      DEP_REWRITE_TAC[vec_sat_scpv_eq]>>
      simp[]>>
      irule_at Any dir_scp_dir_scpv>>
      first_assum (irule_at Any)>>
      (* Phase 1 *)
      DEP_REWRITE_TAC[GEN_ALL (GSYM scpn_to_scpnv_sound)]>>
      simp[]>>
      first_x_assum (irule_at Any)>>
      first_x_assum (irule_at Any)>>
      simp[]>>
      CONJ_TAC>- metis_tac[var_lit_pos]>>
      gvs[EXTENSION]>>
      metis_tac[option_CLAUSES,domain_lookup]))>>
  rw[]>>
  gvs[extends_over_def]>>
  rw[EXTENSION,models_def]>>eq_tac>>rw[]
  >- (
    drule_at Any agree_on_sat_scp_F_to_T>>
    simp[]>>
    disch_then (drule_at Any)>>
    disch_then(qspec_then `w` mp_tac)>>
    impl_tac >- (
      gvs[IN_DEF,EXTENSION,good_pc_def,SUBSET_DEF]>>
      metis_tac[])>>
    rw[]>>
    first_x_assum drule>>rw[]>>
    `sat_fml w'' (set fmlls)` by (
      irule sat_fml_SUBSET>>
      pop_assum (irule_at Any)>>
      drule check_scpsteps_preserved_1>>
      simp[])>>
    gvs[]>>
    pop_assum (irule_at Any)>>
    rw[]>>
    gvs[agree_on_def,IN_DEF]>>
    metis_tac[])
  >- (
    first_x_assum drule>>rw[]>>
    first_x_assum drule>>rw[]>>
    simp[IN_DEF]>>
    pop_assum (irule_at Any)>>
    gvs[agree_on_def,IN_DEF]>>
    metis_tac[])
QED

Theorem scpog_soundness_special:
  good_pc pc ∧
  EVERY (λC. vars_clause C ⊆ count (pc.nv + 1)) fmlls ∧
  check_scpsteps pc (build_fml kc fmlls) init_sc xs = SOME (fml', sc') ∧
  check_final pc sc' fml' = SOME (INL ()) ⇒
  {w | sat_fml w (set fmlls)} = {}
Proof
  strip_tac>>
  drule check_scpsteps_extends_over>>
  disch_then drule>>
  simp[init_sc_def]>>
  impl_tac >- (
    simp[SUBSET_DEF,vars_fml_def,PULL_EXISTS]>>
    gvs[EVERY_MEM,SUBSET_DEF]>>
    metis_tac[])>>
  strip_tac>>
  rw[EXTENSION]>>
  CCONTR_TAC>>gvs[]>>
  gvs[extends_over_def]>>
  first_x_assum drule>>
  strip_tac>>
  gvs[check_final_def,sat_fml_def,AllCaseEqs(),check_inputs_scp_def]>>
  first_x_assum drule>>
  simp[sat_clause_def]
QED

val _ = export_theory ();
