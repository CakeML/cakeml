(*
  Multi-objective (Pareto) semantics for pbc
*)
Theory pbc_mo
Ancestors
  pbc
Libs
  preamble

val _ = numLib.temp_prefer_num();

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

(*** Minimal elements ***)

Definition pareto_min_set_def:
  pareto_min_set s =
    {v | v ∈ s ∧ ∀v'. v' ∈ s ⇒ ¬vec_lt v' v}
End

Definition pareto_min_def:
  pareto_min ls =
    let ds = nub ls in
      FILTER (λv. ¬EXISTS (λv'. vec_lt v' v) ds) ds
End

Theorem pareto_min_set_SUBSET:
  pareto_min_set s ⊆ s
Proof
  rw[pareto_min_set_def,SUBSET_DEF]
QED

Theorem set_pareto_min:
  set (pareto_min ls) = pareto_min_set (set ls)
Proof
  rw[pareto_min_def,pareto_min_set_def,EXTENSION,MEM_FILTER,EXISTS_MEM,
    MEM_nub]>>
  simp[EVERY_MEM,MEM_nub]>>
  metis_tac[]
QED

(* Two sets that weakly dominate each other have the same minimal elements *)
Theorem pareto_min_set_dom_SUBSET[local]:
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ vec_le v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ vec_le u v) ⇒
  pareto_min_set s ⊆ pareto_min_set t
Proof
  rw[pareto_min_set_def,SUBSET_DEF]
  >- (
    (* x is dominated by some u in t, and in fact x = u *)
    `∃u. u ∈ t ∧ vec_le u x` by metis_tac[]>>
    `∃v. v ∈ s ∧ vec_le v u` by metis_tac[]>>
    `vec_le v x` by metis_tac[vec_le_trans]>>
    `v = x` by metis_tac[vec_le_not_vec_lt]>>
    `x = u` by metis_tac[vec_le_antisym]>>
    metis_tac[])>>
  (* anything in t strictly dominating x is dominated by something in s *)
  `∃v. v ∈ s ∧ vec_le v v'` by metis_tac[]>>
  metis_tac[vec_le_vec_lt]
QED

Theorem pareto_min_set_dom:
  (∀u. u ∈ t ⇒ ∃v. v ∈ s ∧ vec_le v u) ∧
  (∀v. v ∈ s ⇒ ∃u. u ∈ t ∧ vec_le u v) ⇒
  pareto_min_set s = pareto_min_set t
Proof
  rw[SET_EQ_SUBSET]>>
  irule pareto_min_set_dom_SUBSET>>
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

Definition nondom_set_def:
  nondom_set pbf objs = pareto_min_set (obj_img pbf objs)
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
  v ∈ nondom_set pbf objs ⇔
  (∃w. satisfies w pbf ∧ obj_vecs objs w = v) ∧
  (∀w. satisfies w pbf ⇒ ¬vec_lt (obj_vecs objs w) v)
Proof
  rw[nondom_set_def,pareto_min_set_def,in_obj_img]>>
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
  nondom_set pbf objs =
  nondom_set (IMAGE (map_pbc f) pbf) (map_objs f objs)
Proof
  rw[nondom_set_def]>>
  metis_tac[obj_img_INJ]
QED
