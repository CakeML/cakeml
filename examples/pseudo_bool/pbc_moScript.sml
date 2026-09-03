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

Definition vec_lt_def:
  vec_lt vs ws ⇔ vec_le vs ws ∧ vs ≠ ws
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

Theorem vec_lt_irrefl[simp]:
  ¬vec_lt vs vs
Proof
  rw[vec_lt_def]
QED

Theorem vec_le_not_vec_lt:
  vec_le vs ws ∧ ¬vec_lt vs ws ⇒ vs = ws
Proof
  rw[vec_lt_def]
QED

Theorem vec_le_vec_lt:
  vec_le vs ws ∧ vec_lt ws xs ⇒ vec_lt vs xs
Proof
  rw[vec_lt_def]>>
  metis_tac[vec_le_trans,vec_le_antisym]
QED

Theorem vec_lt_vec_le:
  vec_lt vs ws ∧ vec_le ws xs ⇒ vec_lt vs xs
Proof
  rw[vec_lt_def]>>
  metis_tac[vec_le_trans,vec_le_antisym]
QED

Theorem vec_lt_trans:
  vec_lt vs ws ∧ vec_lt ws xs ⇒ vec_lt vs xs
Proof
  metis_tac[vec_lt_def,vec_lt_vec_le]
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

Definition ord_lt_def:
  ord_lt ord vs ws ⇔ ord_le ord vs ws ∧ vs ≠ ws
End

(* The orderings the checker is sound for: reflexive, transitive and
  antisymmetric, so that the minimal elements of a set are well defined *)
Definition good_mo_ord_def:
  good_mo_ord ord ⇔
    (∀x. ord_le ord x x) ∧
    (∀x y z. ord_le ord x y ∧ ord_le ord y z ⇒ ord_le ord x z) ∧
    (∀x y. ord_le ord x y ∧ ord_le ord y x ⇒ x = y)
End

Theorem good_mo_ord_Pareto[simp]:
  good_mo_ord Pareto
Proof
  rw[good_mo_ord_def,ord_le_def]>>
  metis_tac[vec_le_trans,vec_le_antisym]
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

(* Every ordering refines componentwise dominance *)
Theorem vec_le_ord_le:
  vec_le vs ws ⇒ ord_le ord vs ws
Proof
  Cases_on`ord`>>simp[ord_le_def]
QED

(*** Minimal elements under a relation ***)

Definition min_set_def:
  min_set R s =
    {v | v ∈ s ∧ ∀v'. v' ∈ s ∧ R v' v ⇒ v' = v}
End

Definition ord_min_def:
  ord_min ord ls =
    let ds = nub ls in
      FILTER (λv. ¬EXISTS (λv'. ord_lt ord v' v) ds) ds
End

Theorem min_set_SUBSET:
  min_set R s ⊆ s
Proof
  rw[min_set_def,SUBSET_DEF]
QED

Theorem set_ord_min:
  set (ord_min ord ls) = min_set (ord_le ord) (set ls)
Proof
  rw[ord_min_def,min_set_def,ord_lt_def,EXTENSION,MEM_FILTER,EXISTS_MEM,
    MEM_nub]>>
  simp[EVERY_MEM,MEM_nub,o_DEF]>>
  metis_tac[]
QED

(* Two sets that weakly dominate each other have the same minimal elements *)
Theorem min_set_dom_SUBSET[local]:
  (∀x y z. R x y ∧ R y z ⇒ R x z) ∧
  (∀x y. R x y ∧ R y x ⇒ x = y) ∧
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ R v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ R u v) ⇒
  min_set R s ⊆ min_set R t
Proof
  rw[min_set_def,SUBSET_DEF]
  >- (
    `∃u. u ∈ t ∧ R u x` by metis_tac[]>>
    `∃v. v ∈ s ∧ R v u` by metis_tac[]>>
    `v = x` by metis_tac[]>>
    metis_tac[])>>
  `∃v. v ∈ s ∧ R v v'` by metis_tac[]>>
  `v = x` by metis_tac[]>>
  metis_tac[]
QED

Theorem min_set_dom:
  (∀x y z. R x y ∧ R y z ⇒ R x z) ∧
  (∀x y. R x y ∧ R y x ⇒ x = y) ∧
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ R v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ R u v) ⇒
  min_set R s = min_set R t
Proof
  rw[SET_EQ_SUBSET]>>
  irule min_set_dom_SUBSET>>
  metis_tac[]
QED

Theorem min_set_dom_ord:
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ ord_le ord v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ ord_le ord u v) ⇒
  min_set (ord_le ord) s = min_set (ord_le ord) t
Proof
  strip_tac>>
  irule min_set_dom>>
  strip_assume_tac (good_mo_ord_thm |> REWRITE_RULE [good_mo_ord_def])>>
  metis_tac[]
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
  (∀w. satisfies w pbf ∧ ord_le ord (obj_vecs objs w) v ⇒
    obj_vecs objs w = v)
Proof
  rw[nondom_set_def,min_set_def,in_obj_img]>>
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
