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
    by (fs[CPstate_inv_def]>>metis_tac[NOT_NONE_SOME])

  >>cheat
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
