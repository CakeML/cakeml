(*
  Correctness proof for word_copy
*)
open preamble word_copyTheory wordPropsTheory;

val _ = new_theory "word_copyProof";

val s = ``s:('a,'c,'ffi) wordSem$state``

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_copy"];

Definition CPstate_inv_def:
  CPstate_inv cs = (
   (* cs.next is a fresh class *)
   (∀v c. lookup v cs.to_eq = SOME c ⇒ c < cs.next) ∧
   (∀c. c ∈ domain cs.from_eq ⇒ c < cs.next) ∧
   (* if representative of equiv class c is var v,
      then class of v is c *)
   (∀c v. lookup c cs.from_eq = SOME v ⇒
     lookup v cs.to_eq = SOME c)
  )
End
(* As a corollary, different classes have different representatives:
   (∀c c'. c < c' ⇒ c' < cs.next ⇒ lookup c cs.from_eq ≠ lookup c' cs.from_eq))
*)

Theorem empty_eq_inv:
  CPstate_inv empty_eq
Proof
  rw[CPstate_inv_def,empty_eq_def]
QED

Theorem remove_eq_inv:
  ∀cs v. CPstate_inv cs ⇒
  CPstate_inv (remove_eq cs v)
Proof
  rw[remove_eq_def]>>
  Cases_on‘lookup v cs.to_eq’>>
  rw[empty_eq_inv]
QED

Theorem remove_eqs_inv:
  ∀vv cs. CPstate_inv cs ⇒
    CPstate_inv (remove_eqs cs vv)
Proof
  Induct>>
  rw[remove_eqs_def,remove_eq_inv]
QED

Theorem set_eq_inv:
  CPstate_inv cs ∧
  lookup t cs.to_eq = NONE ⇒
  CPstate_inv (set_eq cs t s)
Proof
  rw[]>>
  ‘∀c. lookup c cs.from_eq ≠ SOME t’ by (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rw[set_eq_def]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>
  rw[]>>fs[]
  >~[`lookup s cs.to_eq = NONE`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>simp[]
    >- (
      first_x_assum drule>>
      simp[])
    >- (
      first_x_assum drule>>
      simp[])
    >- metis_tac[NOT_SOME_NONE])
  >~[`lookup c_s cs.from_eq = NONE`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>simp[]
    >- (
      first_x_assum drule>>
      simp[])
    >- (
      first_x_assum drule>>
      simp[])
    >-
      metis_tac[SOME_11,NOT_SOME_NONE])
  >~[`lookup s cs.to_eq = SOME c_s`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>
    metis_tac[])
QED

(*
Theorem set_eq_inv:
  ∀cs t s.
    CPstate_inv cs ∧
    lookup t cs.to_eq = NONE ⇒
    CPstate_inv (set_eq cs t s)
Proof
  rpt strip_tac>>
  ‘∀c. c<cs.next ⇒ lookup c cs.from_eq ≠ SOME t’ by (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rw[set_eq_def]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>
  fs[]
  >~[`lookup s cs.to_eq = NONE`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]
    >- (
      first_x_assum drule>>
      simp[])>>
    ‘c<cs.next’ by decide_tac>>
    metis_tac[NOT_NONE_SOME])
  >~[`lookup s cs.to_eq = SOME c_s`]
  >- (
    fs[CPstate_inv_def]>>
    rw[lookup_insert]>>
    metis_tac[])
QED
*)

Theorem merge_eqs_inv:
  CPstate_inv cs1 ∧
  CPstate_inv cs2 ⇒
  CPstate_inv (merge_eqs cs1 cs2)
Proof
  rw[]>>
  simp[merge_eqs_def,CPstate_inv_def]>>
  CONJ_TAC >- (
    (* invariant 1 works *)
    rw[lookup_inter_eq]>>gvs[AllCaseEqs()]>>
    metis_tac[CPstate_inv_def] ) >>
  CONJ_TAC >- (
    (* invariant 2 works *)
    simp[domain_lookup,lookup_inter_eq,AllCaseEqs()]>>
    rw[]>>metis_tac[CPstate_inv_def]
  )>>
  rw[lookup_inter_eq,AllCaseEqs()]>>
  metis_tac[CPstate_inv_def]
QED

(* XXX: get rid of this *)
Theorem same_classD_old:
  CPstate_inv cs ∧
  lookup_eq cs x = lookup_eq cs y ⇒
  x = y ∨
  (∃c.
    lookup x cs.to_eq = SOME c ∧
    lookup y cs.to_eq = SOME c)
Proof
  rw[lookup_eq_def,AllCaseEqs()]
  >- (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])
  >- (
    fs[CPstate_inv_def]>>
    first_x_assum drule>>
    rw[])>>
  Cases_on`lookup y cs.to_eq`>>gvs[]
  >- (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rename1`lookup y _ = SOME cy`>>
  Cases_on`lookup cy cs.from_eq`>>gvs[]
  >- (
    fs[CPstate_inv_def]>>
    first_x_assum drule>>
    rw[])>>
  fs[CPstate_inv_def]>>
  metis_tac[SOME_11]
QED

Theorem same_classD:
  CPstate_inv cs ∧
  lookup_eq cs x = lookup_eq cs y ⇒
  x = y ∨ (x ≠ y ∧
  ∃c rep.
    lookup x cs.to_eq = SOME c ∧
    lookup y cs.to_eq = SOME c ∧
    lookup c cs.from_eq = SOME rep)
Proof
  rw[]>>
  Cases_on‘x=y’>-(DISJ1_TAC>>pop_assum ACCEPT_TAC)>>
  DISJ2_TAC>>
  CONJ_TAC>-pop_assum ACCEPT_TAC>>
  drule_all same_classD_old>>
  rw[]>>
  qexists_tac‘c’>>
  gvs[lookup_eq_def]>>
  Cases_on‘lookup c cs.from_eq’>>gvs[]
QED

Theorem lookup_eqI:
  ∀cs r v.
  (r=v ∧ lookup v cs.to_eq = NONE) ∨ (∃c. lookup v cs.to_eq = SOME c ∧ lookup c cs.from_eq = SOME r) ⇒
  lookup_eq cs v = r
Proof
  rw[lookup_eq_def]>>every_case_tac>>rw[]
QED

Theorem lookup_eq_set_eq_not_is_alloc_var:
  ¬ (is_alloc_var s ∧ is_alloc_var t) ⇒
  lookup_eq (set_eq cs t s) v =
  lookup_eq cs v
Proof
  rw[set_eq_def]
QED

(* t := s *)
Theorem lookup_eq_set_eq_is_alloc_var1:
  CPstate_inv cs ∧
  is_alloc_var s ∧ is_alloc_var t ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_eq cs s = lookup_eq cs v ⇒
  lookup_eq (set_eq cs t s) v = t
Proof
  rpt strip_tac>>
  drule_all same_classD>>
  rw[]
  >- (
    simp[lookup_eq_def,set_eq_def]>>
    Cases_on‘lookup s cs.to_eq’>>rw[lookup_insert])
  >- (
    irule lookup_eqI>>
    rw[set_eq_def,lookup_insert]>>
    rw[]>>
    `F` by gvs[CPstate_inv_def,lookup_eq_def])
QED

Theorem lookup_eq_set_eq_is_alloc_var2:
  CPstate_inv cs ∧
  is_alloc_var s ∧ is_alloc_var t ⇒
  lookup t cs.to_eq = NONE ⇒
  v ≠ t ⇒
  lookup_eq cs s ≠ lookup_eq cs v ⇒
  lookup_eq (set_eq cs t s) v = lookup_eq cs v
Proof
  rw[set_eq_def,CPstate_inv_def]>>
  ‘v≠s’by metis_tac[]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>simp[lookup_eq_def,set_eq_def,lookup_insert]
  >-(
    namedCases_on‘lookup v cs.to_eq’["","c"]>>simp[]>>
    ‘c<cs.next’by metis_tac[]>>simp[]
  )
  >-(
    namedCases_on‘lookup c_s cs.from_eq’["","s_rep"]>>namedCases_on‘lookup v cs.to_eq’["","c"]>>simp[lookup_insert]
    >-(
      Cases_on‘c=cs.next’>>simp[]
      >-(‘c<cs.next’by metis_tac[]>>decide_tac)
    )
    >-(Cases_on‘c=c_s’>>simp[]>>gvs[lookup_eq_def])
  )
QED

Theorem lookup_eq_set_eq_t:
  CPstate_inv cs ∧
  is_alloc_var s ∧ is_alloc_var t ⇒
  lookup_eq (set_eq cs t s) t = t
Proof
  simp[lookup_eq_def,set_eq_def]>>
  every_case_tac>>gvs[lookup_insert]
QED

Theorem lookup_eq_set_eq_s:
  CPstate_inv cs ∧
  is_alloc_var s ∧ is_alloc_var t ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_eq (set_eq cs t s) s = t
Proof
Cases_on‘s=t’>-rw[lookup_eq_set_eq_t]>-rw[lookup_eq_set_eq_is_alloc_var1]
QED

Theorem lookup_eq_set_eqD:
  CPstate_inv cs ⇒
  lookup t cs.to_eq = NONE ⇒
  lookup_eq (set_eq cs t s) v = r ⇒
  (r=t ⇒ v=t ∨ lookup_eq cs v = lookup_eq cs s) ∧
  (r≠t ⇒ r = lookup_eq cs v)
Proof
  Cases_on‘is_alloc_var s ∧ is_alloc_var t’
  >-(
    rpt strip_tac
    >-(
      Cases_on‘v=t’>-decide_tac
      >-(
        DISJ2_TAC>>
        CCONTR_TAC>>
        ‘t = lookup_eq cs v’
          by metis_tac[lookup_eq_set_eq_is_alloc_var2]>>
        (* t = lookup_eq cs v, v≠t, hence lookup t cs.eq ≠ NONE *)
        pop_assum mp_tac>>
        simp[lookup_eq_def]>>every_case_tac>>
        metis_tac[CPstate_inv_def,NOT_NONE_SOME]
      )
    )
    >-metis_tac[lookup_eq_set_eq_t,lookup_eq_set_eq_is_alloc_var1,lookup_eq_set_eq_is_alloc_var2]
  )
  >-(
    ‘lookup_eq (set_eq cs t s) v = lookup_eq cs v’
      by metis_tac[lookup_eq_set_eq_not_is_alloc_var]>>
    rw[]>>
    DISJ1_TAC>>
    fs[CPstate_inv_def,lookup_eq_def]>>
    every_case_tac>>
    metis_tac[NOT_NONE_SOME]
  )
QED

Definition CPstate_models_def:
  CPstate_models cs S ⇔ ∀v c vrep.
    lookup v cs.to_eq = SOME c ⇒
    lookup c cs.from_eq = SOME vrep ⇒
    lookup v S.locals = lookup vrep S.locals
End

Theorem CPstate_model:
  CPstate_models cs st ⇒
  lookup v st.locals = lookup (lookup_eq cs v) st.locals
Proof
  rw[CPstate_models_def,lookup_eq_def]>>every_case_tac>>rw[]
QED

Theorem CPstate_modelsI:
  CPstate_inv cs ⇒
  (∀x y. lookup_eq cs x = lookup_eq cs y ⇒ lookup x st.locals = lookup y st.locals) ⇒
  CPstate_models cs st
Proof
  rw[CPstate_inv_def,CPstate_models_def]>>
  qpat_x_assum‘∀x y. _ ⇒ lookup x st.locals = lookup y st.locals’irule>>
  rw[lookup_eq_def]>>TOP_CASE_TAC>>TOP_CASE_TAC>>
  metis_tac[domain_lookup,NOT_NONE_SOME,SOME_11]
QED

Theorem CPstate_modelsD:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  ∀x y. lookup_eq cs x = lookup_eq cs y ⇒ lookup x st.locals = lookup y st.locals
Proof
  rw[CPstate_models_def]>>metis_tac[same_classD]
QED

Theorem CPstate_models_remove_eq:
  CPstate_models cs st ⇒
  CPstate_models (remove_eq cs t) st
Proof
  rw[remove_eq_def]>>
  TOP_CASE_TAC>>rw[empty_eq_def,CPstate_models_def]
QED

Theorem lookup_eq_remove_eq_t:
  CPstate_inv cs ⇒
  lookup_eq (remove_eq cs t) x = t ⇒ x=t
Proof
  rw[remove_eq_def,lookup_eq_def]>>
  Cases_on‘lookup t cs.to_eq’>>fs[empty_eq_def]>>
  namedCases_on‘lookup x cs.to_eq’["","c"]>>
  namedCases_on‘lookup c cs.from_eq’["","c_rep"]>>gvs[]>>
  metis_tac[CPstate_inv_def,NOT_NONE_SOME]
QED

Theorem aux_Move:
  CPstate_inv cs ⇒
  CPstate_models cs st ⇒
  is_alloc_var t ∧ is_alloc_var s ⇒
  lookup s st.locals = SOME sval ⇒
  CPstate_inv (set_eq (remove_eq cs t) t s) ∧
  CPstate_models (set_eq (remove_eq cs t) t s) (st with locals := insert t sval st.locals)
Proof
  rpt DISCH_TAC>>
  ‘CPstate_inv (remove_eq cs t)’ by metis_tac[remove_eq_inv]>>
  ‘CPstate_inv (set_eq (remove_eq cs t) t s)’
  by (
    irule set_eq_inv>>
    rw[remove_eq_def]>>
    TOP_CASE_TAC>>rw[empty_eq_def]
  )>>
  CONJ_TAC>-pop_assum ACCEPT_TAC>>
  (* CPstate_inv was easy. Now prove CPstate_models *)
  irule CPstate_modelsI>>
  rw[]>>
  ‘lookup t (remove_eq cs t).to_eq = NONE’ by (
    rw[remove_eq_def]>>
    Cases_on‘lookup t cs.to_eq’>>rw[empty_eq_def]
  )>>
  Cases_on‘t=x∧t=y’>-rw[lookup_eq_set_eq_t,lookup_insert]>>
  Cases_on‘t≠x∧t≠y’>-(
    qpat_x_assum‘¬(t=x∧t=y)’kall_tac>>
    rw[lookup_insert]>>
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) x’>>
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) y’>>
    metis_tac[lookup_eq_set_eq_is_alloc_var1,lookup_eq_set_eq_is_alloc_var2,
      lookup_eq_set_eqD,CPstate_models_remove_eq,CPstate_modelsD]
  )>>
  wlog_tac‘t=x∧t≠y’[‘x’,‘y’]>-metis_tac[]>>
  rw[lookup_eq_set_eq_t]>-(
    Cases_on‘lookup_eq (remove_eq cs t) s = lookup_eq (remove_eq cs t) y’
    >-(
      rw[lookup_insert]>>
      metis_tac[lookup_eq_set_eq_is_alloc_var1,CPstate_models_remove_eq,CPstate_modelsD]
    )
    >-(
      rw[lookup_insert]>>
      gvs[lookup_eq_set_eq_t]>>
      metis_tac[lookup_eq_set_eq_is_alloc_var2,lookup_eq_remove_eq_t]
    )
  )
QED

(* TODO: insert an induction over copy_prop_prog *)

(* Main semantics result *)
Theorem evaluate_copy_prop:
  evaluate (copy_prop e, s) = evaluate (e, s)
Proof
  cheat
QED

(* Bunch of syntactic results for integration into compiler *)

(* Leave these things for now *)

val _ = export_theory();
