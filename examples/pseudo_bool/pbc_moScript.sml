(*
  Multi-objective semantics for pbc, under a selectable objective ordering
*)
Theory pbc_mo
Ancestors
  pbc
Libs
  preamble

val _ = numLib.temp_prefer_num();

(*** The objective orderings the checker can be asked for ***)

Datatype:
  mo_ord = Pareto
End

Definition parse_mo_ord_def:
  parse_mo_ord s =
  if s = «pareto» then SOME Pareto else NONE
End

Definition mo_ord_name_def:
  mo_ord_name Pareto = «PARETO»
End

(*** Componentwise order on objective vectors ***)

Definition vec_le_def:
  vec_le (vs:int list) ws ⇔ LIST_REL (λa b. a ≤ b) vs ws
End

Theorem vec_le_refl[simp]:
  vec_le vs vs
Proof
  rw[vec_le_def,LIST_REL_EL_EQN]
QED

Theorem vec_le_LENGTH:
  vec_le vs ws ⇒ LENGTH vs = LENGTH ws
Proof
  rw[vec_le_def,LIST_REL_EL_EQN]
QED

Theorem vec_le_trans:
  vec_le vs ws ∧ vec_le ws xs ⇒ vec_le vs xs
Proof
  rw[vec_le_def,LIST_REL_EL_EQN]>>
  `n < LENGTH ws ∧ n < LENGTH vs` by gvs[]>>
  res_tac>>
  metis_tac[integerTheory.INT_LE_TRANS]
QED

Theorem vec_le_antisym:
  ∀vs ws. vec_le vs ws ∧ vec_le ws vs ⇒ vs = ws
Proof
  simp[vec_le_def]>>
  Induct>>rw[]>>
  gvs[]>>
  intLib.ARITH_TAC
QED

Theorem vec_le_MAP:
  vec_le (MAP f ls) (MAP g ls) ⇔ EVERY (λx. f x ≤ g x) ls
Proof
  Induct_on`ls`>>rw[vec_le_def]>>
  fs[vec_le_def]
QED

(*** Orderings on objective vectors ***)

Definition ord_le_def:
  ord_le Pareto vs ws = vec_le vs ws
End

(* Strictly below: below but not equivalent *)
Definition ord_lt_def:
  ord_lt ord vs ws ⇔ ord_le ord vs ws ∧ ¬ord_le ord ws vs
End

(* Equivalent: below each other *)
Definition ord_equiv_def:
  ord_equiv ord vs ws ⇔ ord_le ord vs ws ∧ ord_le ord ws vs
End

(* The orderings the checker is sound for: preorders (reflexive and
  transitive). Equivalent but distinct vectors are allowed, so the
  checker's guarantees are stated up to ord_equiv *)
Definition good_mo_ord_def:
  good_mo_ord ord ⇔
    (∀x. ord_le ord x x) ∧
    (∀x y z. ord_le ord x y ∧ ord_le ord y z ⇒ ord_le ord x z)
End

Theorem good_mo_ord_Pareto[simp]:
  good_mo_ord Pareto
Proof
  rw[good_mo_ord_def,ord_le_def]>>
  metis_tac[vec_le_trans]
QED

Theorem good_mo_ord_thm:
  good_mo_ord ord
Proof
  Cases_on`ord`>>simp[]
QED

Theorem ord_le_refl[simp]:
  ord_le ord vs vs
Proof
  Cases_on`ord`>>simp[ord_le_def]
QED

Theorem ord_le_trans:
  ord_le ord x y ∧ ord_le ord y z ⇒ ord_le ord x z
Proof
  metis_tac[good_mo_ord_thm |> REWRITE_RULE [good_mo_ord_def]]
QED

(* Every ordering refines componentwise dominance *)
Theorem vec_le_ord_le:
  vec_le vs ws ⇒ ord_le ord vs ws
Proof
  Cases_on`ord`>>simp[ord_le_def]
QED

(*** The equivalence induced by an ordering ***)

Theorem ord_equiv_refl[simp]:
  ord_equiv ord vs vs
Proof
  rw[ord_equiv_def]
QED

Theorem ord_equiv_sym:
  ord_equiv ord vs ws ⇒ ord_equiv ord ws vs
Proof
  rw[ord_equiv_def]
QED

Theorem ord_equiv_trans:
  ord_equiv ord vs ws ∧ ord_equiv ord ws xs ⇒ ord_equiv ord vs xs
Proof
  rw[ord_equiv_def]>>
  metis_tac[ord_le_trans]
QED

Theorem ord_equiv_Pareto:
  ord_equiv Pareto vs ws ⇔ vs = ws
Proof
  rw[ord_equiv_def,ord_le_def]>>
  metis_tac[vec_le_antisym,vec_le_refl]
QED

Theorem ord_lt_equiv:
  ord_equiv ord v v' ∧ ord_equiv ord x x' ⇒
  (ord_lt ord v x ⇔ ord_lt ord v' x')
Proof
  rw[ord_equiv_def,ord_lt_def]>>
  metis_tac[ord_le_trans]
QED

Theorem ord_lt_Pareto:
  ord_lt Pareto vs ws ⇔ vec_le vs ws ∧ vs ≠ ws
Proof
  rw[ord_lt_def,ord_le_def]>>
  metis_tac[vec_le_antisym,vec_le_refl]
QED

(* Two sets of vectors that agree up to equivalence *)
Definition set_equiv_def:
  set_equiv ord s t ⇔
    (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ ord_equiv ord v u) ∧
    (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ ord_equiv ord v u)
End

Theorem set_equiv_trans:
  set_equiv ord s t ∧ set_equiv ord t u ⇒ set_equiv ord s u
Proof
  rw[set_equiv_def]>>
  metis_tac[ord_equiv_trans]
QED

Theorem set_equiv_Pareto:
  set_equiv Pareto s t ⇔ s = t
Proof
  rw[set_equiv_def,ord_equiv_Pareto,EXTENSION]>>
  metis_tac[]
QED

(*** Minimal elements under a relation ***)

(* The elements with nothing strictly below them *)
Definition min_set_def:
  min_set R s =
    {v | v ∈ s ∧ ∀v'. v' ∈ s ∧ R v' v ⇒ R v v'}
End

Theorem min_set_SUBSET:
  min_set R s ⊆ s
Proof
  rw[min_set_def,SUBSET_DEF]
QED

Theorem in_min_set_ord:
  v ∈ min_set (ord_le ord) s ⇔
  v ∈ s ∧ ∀v'. v' ∈ s ⇒ ¬ord_lt ord v' v
Proof
  rw[min_set_def,ord_lt_def]>>
  metis_tac[]
QED

Theorem min_set_equiv_closed:
  v ∈ min_set (ord_le ord) s ∧ u ∈ s ∧ ord_equiv ord v u ⇒
  u ∈ min_set (ord_le ord) s
Proof
  rw[in_min_set_ord]>>
  metis_tac[ord_lt_equiv,ord_equiv_refl]
QED

(* Under a transitive R, if s and t weakly dominate each other then every
  minimal element of s has an R-equivalent minimal element in t *)
Theorem min_set_dom:
  (∀x y z. R x y ∧ R y z ⇒ R x z) ∧
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ R v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ R u v) ⇒
  ∀v. v ∈ min_set R s ⇒ ∃u. u ∈ min_set R t ∧ R v u ∧ R u v
Proof
  rw[min_set_def]>>
  `∃u. u ∈ t ∧ R u v` by metis_tac[]>>
  `∃v'. v' ∈ s ∧ R v' u` by metis_tac[]>>
  `R v u` by metis_tac[]>>
  qexists_tac`u`>>simp[]>>
  metis_tac[]
QED

Theorem min_set_dom_ord:
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ ord_le ord v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ ord_le ord u v) ⇒
  set_equiv ord (min_set (ord_le ord) s) (min_set (ord_le ord) t)
Proof
  rw[set_equiv_def,ord_equiv_def]
  >- (
    irule min_set_dom>>
    metis_tac[ord_le_trans])>>
  `∃v. v ∈ min_set (ord_le ord) s ∧ ord_le ord u v ∧ ord_le ord v u`
    suffices_by metis_tac[]>>
  irule min_set_dom>>
  metis_tac[ord_le_trans]
QED

(*** ord_min computes a front of the minimal elements ***)

(* One representative per equivalence class, keeping the last occurrence *)
Definition ord_dedup_def:
  (ord_dedup ord [] = []) ∧
  (ord_dedup ord (v::vs) =
    if EXISTS (λv'. ord_equiv ord v v') vs
    then ord_dedup ord vs
    else v :: ord_dedup ord vs)
End

Definition ord_min_def:
  ord_min ord ls =
    let ds = ord_dedup ord ls in
      FILTER (λv. ¬EXISTS (λv'. ord_lt ord v' v) ds) ds
End

Theorem ord_dedup_Pareto:
  ord_dedup Pareto ls = nub ls
Proof
  Induct_on`ls`>>
  rw[ord_dedup_def,nub_def,ord_equiv_Pareto,EXISTS_MEM]
QED

(* Under Pareto, ord_min is the nub-and-filter computation on plain vector
  dominance *)
Theorem ord_min_Pareto:
  ord_min Pareto ls =
    FILTER (λv. ¬EXISTS (λv'. vec_le v' v ∧ v' ≠ v) (nub ls)) (nub ls)
Proof
  rw[ord_min_def,ord_dedup_Pareto,ord_lt_Pareto]
QED

Theorem MEM_ord_dedup_imp:
  MEM x (ord_dedup ord ls) ⇒ MEM x ls
Proof
  Induct_on`ls`>>
  rw[ord_dedup_def]>>
  metis_tac[]
QED

Theorem ord_dedup_covers:
  ∀x. MEM x ls ⇒ ∃y. MEM y (ord_dedup ord ls) ∧ ord_equiv ord x y
Proof
  Induct_on`ls`>>
  rw[ord_dedup_def,EXISTS_MEM]>>
  metis_tac[ord_equiv_trans,ord_equiv_refl]
QED

Theorem ord_dedup_equiv_eq:
  MEM x (ord_dedup ord ls) ∧ MEM y (ord_dedup ord ls) ∧ ord_equiv ord x y ⇒
  x = y
Proof
  Induct_on`ls`>>
  rw[ord_dedup_def,EXISTS_MEM]>>
  metis_tac[MEM_ord_dedup_imp,ord_equiv_sym]
QED

Theorem ALL_DISTINCT_ord_dedup:
  ALL_DISTINCT (ord_dedup ord ls)
Proof
  Induct_on`ls`>>
  rw[ord_dedup_def,EXISTS_MEM]>>
  metis_tac[MEM_ord_dedup_imp,ord_equiv_refl]
QED

(* vs is a front of M: a duplicate-free list meeting each equivalence class
  of M exactly once and nothing else. An entry is equivalent to an element
  of M but need not itself be a member of M *)
Definition is_front_def:
  is_front ord vs M ⇔
    set_equiv ord (set vs) M ∧ ALL_DISTINCT vs ∧
    (∀x y. MEM x vs ∧ MEM y vs ∧ ord_equiv ord x y ⇒ x = y)
End

Theorem ord_min_is_front:
  is_front ord (ord_min ord ls) (min_set (ord_le ord) (set ls))
Proof
  rw[is_front_def,ord_min_def,set_equiv_def,MEM_FILTER,EXISTS_MEM,EVERY_MEM,
    o_DEF,FILTER_ALL_DISTINCT,ALL_DISTINCT_ord_dedup]
  >- (
    qexists_tac`v`>>
    simp[in_min_set_ord]>>
    metis_tac[MEM_ord_dedup_imp,ord_dedup_covers,ord_lt_equiv,ord_equiv_refl])
  >- (
    `MEM u ls` by fs[in_min_set_ord]>>
    drule ord_dedup_covers>>
    disch_then (qspec_then `ord` strip_assume_tac)>>
    rename1`ord_equiv ord u y`>>
    qexists_tac`y`>>
    `y ∈ min_set (ord_le ord) (set ls)` by
      metis_tac[min_set_equiv_closed,MEM_ord_dedup_imp]>>
    fs[in_min_set_ord]>>
    metis_tac[MEM_ord_dedup_imp,ord_equiv_sym])>>
  metis_tac[ord_dedup_equiv_eq]
QED

Theorem is_front_set_equiv:
  is_front ord vs M ∧ set_equiv ord M N ⇒ is_front ord vs N
Proof
  rw[is_front_def]>>
  metis_tac[set_equiv_trans]
QED

Theorem is_front_Pareto:
  is_front Pareto vs M ⇔ set vs = M ∧ ALL_DISTINCT vs
Proof
  rw[is_front_def,set_equiv_Pareto,ord_equiv_Pareto]
QED

(*** Multi-objective semantics ***)

Definition obj_vecs_def:
  obj_vecs objs w = MAP (λob. eval_obj (SOME ob) w) objs
End

(* The objective vectors achieved by the solutions of pbf *)
Definition obj_img_def:
  obj_img pbf objs =
    IMAGE (obj_vecs objs) {w | satisfies w pbf}
End

(* The nondominated set of a pbf under an ordering *)
Definition nondom_set_def:
  nondom_set ord pbf objs = min_set (ord_le ord) (obj_img pbf objs)
End

Theorem vec_le_obj_vecs:
  vec_le (obj_vecs objs w) (obj_vecs objs w') ⇔
  EVERY (λob. eval_obj (SOME ob) w ≤ eval_obj (SOME ob) w') objs
Proof
  rw[obj_vecs_def,vec_le_MAP]
QED

Theorem in_obj_img:
  v ∈ obj_img pbf objs ⇔
  ∃w. satisfies w pbf ∧ obj_vecs objs w = v
Proof
  rw[obj_img_def]>>
  metis_tac[]
QED

Theorem in_nondom_set:
  v ∈ nondom_set ord pbf objs ⇔
  (∃w. satisfies w pbf ∧ obj_vecs objs w = v) ∧
  (∀w. satisfies w pbf ⇒ ¬ord_lt ord (obj_vecs objs w) v)
Proof
  rw[nondom_set_def,in_min_set_ord,in_obj_img]>>
  metis_tac[]
QED

(*** Renaming the variables of a multi-objective problem ***)

Definition objs_vars_def:
  objs_vars objs = BIGUNION (set (MAP (λob. obj_vars (SOME ob)) objs))
End

Definition map_objs_def:
  map_objs f objs =
    MAP (λ(xs,c). (MAP (λ(a,b). (a, map_lit f b)) xs,c)) objs
End

Theorem objs_vars_thm[simp]:
  objs_vars [] = {} ∧
  objs_vars (ob::objs) = obj_vars (SOME ob) ∪ objs_vars objs
Proof
  rw[objs_vars_def]
QED

Theorem objs_vars_SUBSET:
  objs_vars objs ⊆ v ⇔ EVERY (λob. obj_vars (SOME ob) ⊆ v) objs
Proof
  rw[objs_vars_def,BIGUNION_SUBSET,MEM_MAP,PULL_EXISTS,EVERY_MEM]
QED

Theorem obj_vecs_map_objs:
  obj_vecs (map_objs f objs) w = obj_vecs objs (w o f)
Proof
  rw[obj_vecs_def,map_objs_def,MAP_MAP_o,MAP_EQ_f,FORALL_PROD]>>
  simp[eval_obj_def,eval_lin_term_MAP]
QED

Theorem obj_img_INJ:
  INJ f (pbf_vars pbf ∪ objs_vars objs) UNIV ⇒
  obj_img pbf objs =
  obj_img (IMAGE (map_pbc f) pbf) (map_objs f objs)
Proof
  strip_tac>>
  qmatch_asmsub_abbrev_tac`INJ f ss UNIV`>>
  rw[EXTENSION,in_obj_img,EQ_IMP_THM]
  >- (
    qexists_tac`w o LINV f ss`>>
    CONJ_ASM1_TAC >- (
      irule satisfies_INJ>>
      first_x_assum (irule_at Any)>>
      simp[Abbr`ss`])>>
    simp[obj_vecs_map_objs]>>
    qmatch_goalsub_abbrev_tac`obj_vecs objs ww = _`>>
    qsuff_tac`obj_vecs objs ww = obj_vecs objs w` >- simp[]>>
    simp[obj_vecs_def,MAP_EQ_f]>>
    rw[]>>
    irule eval_obj_cong>>
    rw[Abbr`ww`]>>
    DEP_REWRITE_TAC[LINV_DEF]>>
    first_x_assum (irule_at Any)>>
    gvs[Abbr`ss`,objs_vars_def,MEM_MAP,PULL_EXISTS]>>
    metis_tac[])>>
  qexists_tac`w o f`>>
  gvs[satisfies_map_pbf,obj_vecs_map_objs]
QED

Theorem nondom_set_INJ:
  INJ f (pbf_vars pbf ∪ objs_vars objs) UNIV ⇒
  nondom_set ord pbf objs =
  nondom_set ord (IMAGE (map_pbc f) pbf) (map_objs f objs)
Proof
  rw[nondom_set_def]>>
  metis_tac[obj_img_INJ]
QED
