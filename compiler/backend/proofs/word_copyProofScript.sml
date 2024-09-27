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
  ∀cs t s.
    CPstate_inv cs ∧
    lookup t cs.to_eq = NONE ⇒
    CPstate_inv (set_eq cs t s)
Proof
  rpt strip_tac>>
  ‘∀c. lookup c cs.from_eq ≠ SOME t’ by (
    fs[CPstate_inv_def]>>
    metis_tac[NOT_NONE_SOME])>>
  rw[set_eq_def]>>
  namedCases_on‘lookup s cs.to_eq’["","c_s"]>>
  fs[]
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

Theorem same_classD:
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
  ‘v=s ∨ (∃c. lookup v cs.to_eq = SOME c ∧ lookup s cs.to_eq = SOME c)’
    by metis_tac[same_classD]
  >- (
     (* could be shorter, I think *)
    simp[lookup_eq_def,set_eq_def]>>
    (Cases_on‘lookup s cs.to_eq’>>rw[lookup_insert])
  )
  >- (
    ‘v≠t’ by metis_tac[NOT_NONE_SOME]>>
    irule lookup_eqI>>
    DISJ2_TAC>>
    rw[set_eq_def,lookup_insert]>>
    every_case_tac>>rw[]>>
    gvs[CPstate_inv_def,lookup_eq_def]
  )
QED

Theorem lookup_eq_set_eq_is_alloc_var2:
  CPstate_inv cs ∧
  is_alloc_var s ∧ is_alloc_var t ⇒
  lookup t cs.to_eq = NONE ⇒
  v≠t ⇒
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
  is_alloc_var t ∧ is_alloc_var s ⇒
  lookup_eq (set_eq cs t s) t = t
Proof
  simp[lookup_eq_def,set_eq_def]>>every_case_tac>>gvs[lookup_insert]
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
        first_x_assum mp_tac>>
        simp[lookup_eq_def]>>every_case_tac>-decide_tac>-decide_tac
        >-metis_tac[CPstate_inv_def,NOT_NONE_SOME]
      )
    )
    >-(
      ‘lookup_eq cs s ≠ lookup_eq cs v’
        by metis_tac[lookup_eq_set_eq_is_alloc_var1]>>
      ‘v≠t’ by (qpat_x_assum‘lookup_eq (set_eq cs t s) v = r’mp_tac>>metis_tac[lookup_eq_set_eq_t])>>
      metis_tac[lookup_eq_set_eq_is_alloc_var2]
    )
  )
  >-(
    drule lookup_eq_set_eq_not_is_alloc_var>>
    DISCH_TAC>>
    first_x_assum(fn eq=>rewrite_tac[eq])>>
    first_x_assum(K ALL_TAC)>>
    rw[]>>
    DISJ1_TAC>>
    first_x_assum mp_tac>>
    fs[CPstate_inv_def,lookup_eq_def]>>
    every_case_tac>>
    metis_tac[NOT_NONE_SOME]
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
