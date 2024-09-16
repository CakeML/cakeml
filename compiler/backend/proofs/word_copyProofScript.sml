(*
  Correctness proof for word_copy
*)
open preamble word_copyTheory wordPropsTheory;

val _ = new_theory "word_copyProof";

val s = ``s:('a,'c,'ffi) wordSem$state``

val _ = set_grammar_ancestry ["wordLang", "wordSem", "wordProps", "word_copy"];

Definition CPstate_inv_def:
  CPstate_inv cs =
  ((∀v c. lookup v cs.to_eq = SOME c ⇒ c < cs.next) ∧
   (* each class has a representative *)
   (∀c. c < cs.next ⇒ lookup c cs.from_eq ≠ NONE) ∧
   (* if representative of equiv class c is var v, then class of v is c *)
   (∀c v. c < cs.next ⇒  lookup c cs.from_eq = SOME v ⇒ lookup v cs.to_eq = SOME c) ∧
   (* different classes have different representatives *)
   (∀c c'. c < c' ⇒ c' < cs.next ⇒ lookup c cs.from_eq ≠ lookup c' cs.from_eq))
End

Theorem empty_eq_inv:
  CPstate_inv empty_eq
Proof
  rw[CPstate_inv_def,empty_eq_def]
QED

Theorem remove_eq_inv:
  ∀cs v. CPstate_inv cs ⇒ CPstate_inv (remove_eq cs v)
Proof
  rw[remove_eq_def]>>Cases_on‘lookup v cs.to_eq’>>rw[empty_eq_inv]
QED

Theorem remove_eqs_inv:
  ∀vv cs. CPstate_inv cs ⇒ CPstate_inv (remove_eqs cs vv)
Proof
  Induct_on‘vv’>>rw[remove_eqs_def,remove_eq_inv]
QED

Theorem set_eq_inv:
  ∀cs t s.
   CPstate_inv cs ⇒
   lookup t cs.to_eq = NONE ⇒
   CPstate_inv (set_eq cs t s)
Proof
  rpt strip_tac>>
  ‘∀c. c<cs.next ⇒ lookup c cs.from_eq ≠ SOME t’
    by (fs[CPstate_inv_def]>>metis_tac[NOT_NONE_SOME])>>
  Cases_on‘is_alloc_var t ∧ is_alloc_var s’THENL
  [
    namedCases_on‘lookup s cs.to_eq’["","c_s"]THENL
    [
      (* lookup s cs.to_eq = NONE *)
      last_x_assum mp_tac>>
      rw[CPstate_inv_def,set_eq_def]THENL
      [
        (* inv. 1 *)
        qpat_x_assum‘_=SOME c’mp_tac>>
        rewrite_tac[lookup_insert]>>
        (Cases_on‘v=t’>-rw[])>>
        (Cases_on‘v=s’>-rw[])>>
        rw[]>>
        ‘c<cs.next’ by metis_tac[]>>
        decide_tac,
        (* inv. 2 *)
        rw[lookup_insert]>>
        qpat_x_assum‘_=SOME v’mp_tac>>
        rw[lookup_insert]>>
        metis_tac[]>>
        ‘c<cs.next’ by decide_tac>>
        metis_tac[NOT_NONE_SOME],
        (* inv. 3 *)
        rw[lookup_insert]>-(
          qpat_x_assum‘_=SOME t’mp_tac>>
          rw[lookup_insert]>>
          qpat_x_assum‘_=SOME s’mp_tac>>
          rw[lookup_insert]>>
          ‘c<cs.next’ by decide_tac>>
          metis_tac[NOT_NONE_SOME]
          )>>
        qpat_x_assum‘_=SOME v’mp_tac>>
        (Cases_on‘c=cs.next’>-rw[lookup_insert])>>
        ‘c<cs.next’ by decide_tac>>rw[lookup_insert]>>
        metis_tac[NOT_NONE_SOME],
        (* inv. 4 *)
        ‘c<cs.next’ by decide_tac>>
        rw[lookup_insert]
      ],
      (* lookup s cs.to_eq = SOME c_s *)
      last_x_assum mp_tac>>
      rw[CPstate_inv_def,set_eq_def]THENL
      [
        (* inv. 1 *)
        qpat_x_assum‘_=SOME c’mp_tac>>
        rewrite_tac[lookup_insert]>>
        Cases_on‘v=t’>>Cases_on‘v=s’>>metis_tac[NOT_NONE_SOME],
        (* inv. 2 *)
        Cases_on‘c=c_s’>>asm_rewrite_tac[lookup_insert]>-rw[]>>
        metis_tac[],
        (* inv. 3 *)
        Cases_on‘v=t’>>asm_rewrite_tac[lookup_insert]>-metis_tac[lookup_insert,NOT_NONE_SOME]>>
        ‘lookup c cs.from_eq = SOME v’by(
          qpat_x_assum‘_=SOME v’mp_tac>>
          Cases_on‘c=c_s’>>rw[lookup_insert]>>metis_tac[NOT_NONE_SOME])>>
        rw[lookup_insert],
        (* inv. 4 *)
        rw[lookup_insert]
      ]
    ],
    rw[set_eq_def]
  ]
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
