(*
  Defines the HOL inference system.
*)
open preamble holSyntaxLibTheory mlstringTheory totoTheory holSyntaxTheory

val _ = new_theory "littleTheoriesSyntax"

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

Type thy' = ``:(sig # term set) # (sig # term set)``

Overload sigof = ``(λ((a, _), _). a):thy'->sig``
Overload axsof = ``(λ((_, b), _). b):thy'->term set``
Overload elimsigof = ``(λ(_, (c, _)). c):thy'->sig``
Overload elimaxsof = ``(λ(_, (_, d)). d):thy'->term set``
Overload tysof = ``tysof o sigof``
Overload tmsof = ``tmsof o sigof``

(* Standard signature includes the minimal type operators and constants *)

Definition theory_ok'_def:
  theory_ok' (thy:thy') ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (tysof thy) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)
End

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-'",450,Parse.NONASSOC)

Inductive proves':
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok (tysof thy) ty ∧
   (thy, es, h) |-' l === r
   ⇒ (thy, es, h) |-' (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok' thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
   ⇒ (thy, es, [p]) |-' p)

[~BETA:]
  (theory_ok' thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t
   ⇒ (thy, es, []) |-' Comb (Abs (Var x ty) t) (Var x ty) === t)

[~DEDUCT_ANTISYM:]
  ((thy, es, h1) |-' c1 ∧
   (thy, es, h2) |-' c2
   ⇒ (thy, es, term_union (term_remove c2 h1)
                      (term_remove c1 h2))
           |-' c1 === c2)

[~EQ_MP:]
  ((thy, es, h1) |-' p === q ∧
   (thy, es, h2) |-' p' ∧ ACONV p p'
   ⇒ (thy, es, term_union h1 h2) |-' q)

[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (VSUBST ilist) h) |-' VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok (tysof thy)) (MAP FST tyin)) ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (INST tyin) h) |-' INST tyin c)

[~MK_COMB:]
  ((thy, es, h1) |-' l1 === r1 ∧
   (thy, es, h2) |-' l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, es, term_union h1 h2) |-' Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok' thy ∧ term_ok (sigof thy) t
   ⇒ (thy, es, []) |-' t === t)

[~axioms:]
  (theory_ok' thy ∧ c ∈ (axsof thy)
   ⇒ (thy, es, []) |-' c)

[~elim_discharge:]
  (thy, es1, h1) |-' c ∧ (thy, es2, h2) |-' ec ∧ MEM ec es1
⇒ (thy, term_remove ec es1, term_union h1 h2) |-' c
(*
[~elim_inst:]
  (thy, es1, h1) |-' c
⇒ (thy, SUBSTL es sigma, SUBSTL es h1) |-' SUBST c sigma
*)
[~elim_axioms:]
  (theory_ok' thy ∧ c ∈ (elimaxsof thy)
   ⇒ (thy, [c], []) |-' c)
End

Definition empty_elims_def:
  empty_elims = ((FEMPTY, FEMPTY), {})
End

Theorem theory_sig_eq_elim:
  sigof thy = sigof (thy, empty_elims)
Proof
  Cases_on ‘thy’ >> simp[]
QED

Theorem term_ok_imp_elim:
  term_ok (sigof thy) c ⇒ term_ok (sigof (thy, empty_elims)) c
Proof
  Cases_on ‘thy’ >> simp[term_ok_def]
QED

Theorem type_ok_imp_elim:
  type_ok (tysof thy) ty ⇒ type_ok (tysof (thy, empty_elims)) ty
Proof
  Cases_on ‘thy’ >> simp[type_ok_def]
QED

Theorem type_ok_sigof_imp_elim:
  type_ok (tysof (sigof thy)) ty ⇒ type_ok (tysof (sigof (thy, empty_elims))) ty
Proof
  Cases_on ‘thy’ >> Cases_on ‘q’
  >> simp[type_ok_def]
QED

Theorem axsof_elim_thy:
  c ∈ axsof thy ⇒ c ∈ axsof (thy, empty_elims)
Proof
  Cases_on ‘thy’ >> simp[]
QED

Theorem theory_ok_imp_elim:
  theory_ok thy ⇒ theory_ok' (thy, empty_elims)
Proof
  Cases_on ‘thy’ >> rw[theory_ok'_def, term_ok_imp_elim, theory_sig_eq_elim,
                       type_ok_sigof_imp_elim, theory_ok_def, is_std_sig_def]
QED

Theorem term_ok_sigof_imp:
  term_ok (sigof thy) c ⇒ term_ok (sigof (thy, es)) c
Proof
  Cases_on ‘thy’ >> rw[theory_sig_eq_elim]
QED

Theorem theory_ok'_imp_elim:
  theory_ok' (thy, _) ⇒ theory_ok' (thy, empty_elims)
Proof
  Cases_on ‘thy’ >> simp[theory_ok'_def]
QED

Theorem proves_imp_proves':
 ∀h. (thy, h) |- c ⇒ ((thy, empty_elims), [], h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves'_ABS >> Cases_on ‘thy’ >> gvs[])
  >- (irule proves'_ASSUME >> rw[theory_ok_imp_elim, term_ok_sigof_imp])
  >- (irule proves'_BETA >> rw[theory_ok_imp_elim, term_ok_sigof_imp, type_ok_imp_elim])
  >- (irule proves'_DEDUCT_ANTISYM >> rw[])
  >- (irule proves'_EQ_MP >> metis_tac[])
  >- (irule proves'_INST >> metis_tac[theory_sig_eq_elim])
  >- (irule proves'_INST_TYPE >> gvs[theory_sig_eq_elim] >> simp[])
  >- (irule proves'_MK_COMB >> rw[])
  >- (irule proves'_REFL >> rw[theory_ok_imp_elim, term_ok_sigof_imp])
  >- (irule proves'_axioms >> rw[axsof_elim_thy, theory_ok_imp_elim])
QED

Theorem strip_redun_ty_consts:
  (thy, h) |- c ∧ ty ∉ TYCONSTS_OF thy ∧ ty ∉ TYCONSTS_OF h ∧ ty ∉ TYCONSTS_OF c
  ⇒ (remove_tysig ty thy, h) |- c
Proof
  cheat
QED

Theorem strip_redun_tm_consts:
  (thy, h) |- c ∧ tm ∉ TMCONSTS_OF thy ∧ tm ∉ TMCONSTS_OF h ∧ tm ∉ TMCONSTS_OF c
  ⇒ (remove_tmsig tm thy, h) |- c
Proof
  cheat
QED

Theorem axioms_eliminable:
  ∀thy1 thy2 h1 h2 c1 c2. (thy2, h2) |- c2 ∧ (thy1, h1) |- c1 ∧ sigof thy1 = sigof thy2
  ⇒ ((delete_ax c1 thy2) union_ax thy1, h1 union_ax h2) |- c2
Proof
  cheat
QED

Theorem adsfafisd:
  (thy, (eaxs, esig)), [], h) |-' c ==> (insert_sig esig thy, h) |- c
Proof
  cheat
QED

Theorem imp:
  ((thy, ethy), eaxs, h) |-' c ⇒ (merge_thy ethy thy, h) |- c
Proof
  cheat
QED

(* A context is a sequence of updates *)

Datatype:
  update'
  (* Definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec ((mlstring # term) list) term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn mlstring term mlstring mlstring
  (* NewType name arity *)
  | NewType mlstring num
  (* NewEliminableType name arity *)
  | NewEliminableType mlstring num
  (* NewConst name type *)
  | NewConst mlstring type
  (* NewEliminableConst name type *)
  | NewEliminableConst mlstring type
  (* NewAxiom proposition *)
  | NewAxiom term
  (* NewEliminableAxiom proposition *)
  | NewEliminableAxiom term
End

(* Projecting out pieces of the context *)

  (* Types and constants introduced by an update *)
Definition types_of_upd_def:
  (types_of_upd' (ConstSpec _ _) = []) ∧
  (types_of_upd' (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd' (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd' _ = [])
End

Definition consts_of_upd_def:
  (consts_of_upd' (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd' (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd' (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd' _ = [])
End

Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)``
Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)``
Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``

  (* From this we can recover a signature *)
Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)``

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
Definition axexts_of_upd_def:
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []
End

Definition conexts_of_upd_def:
  (conexts_of_upd (ConstSpec eqs prop) =
    let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
      [VSUBST ilist prop]) ∧
  (conexts_of_upd (TypeDefn name pred abs_name rep_name) =
    let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var (strlit "a") abs_type in
    let r = Var (strlit "r") rep_type in
      [Comb abs (Comb rep a) === a;
       Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  (conexts_of_upd _ = [])
End

Overload axexts = ``λctxt. FLAT (MAP axexts_of_upd ctxt)``
Overload conexts = ``λctxt. FLAT (MAP conexts_of_upd ctxt)``

Overload axioms_of_upd = ``λupd. axexts_of_upd upd ++ conexts_of_upd upd``
Overload axiom_list = ``λctxt. FLAT (MAP axioms_of_upd ctxt)``
Overload axsof = ``λctxt. set (axiom_list ctxt)``

val _ = export_rewrites["types_of_upd_def","consts_of_upd_def","axexts_of_upd_def"]

  (* Now we can recover the theory associated with a context *)
Overload thyof = ``λctxt:update list. (sigof ctxt, axsof ctxt)``

(* Principles for extending the context *)

val _ = Parse.add_infix("updates",450,Parse.NONASSOC)

val _ = hide "abs";

Inductive updates':
  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok (sigof ctxt) prop
   ⇒ (NewAxiom prop) updates' ctxt) ∧

  (* new_constant *)
  (name ∉ (FDOM (tmsof ctxt)) ∧
   type_ok (tysof ctxt) ty
   ⇒ (NewConst name ty) updates' ctxt) ∧

  (* new_specification *)
  ((thyof ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
   EVERY
     (λt. CLOSED t ∧
          (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
     (MAP SND eqs) ∧
   (∀x ty. VFREE_IN (Var x ty) prop ⇒
             MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
   (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))) ∧
   ALL_DISTINCT (MAP FST eqs)
   ⇒ (ConstSpec eqs prop) updates' ctxt) ∧

  (* new_type *)
  (name ∉ (FDOM (tysof ctxt))
   ⇒ (NewType name arity) updates' ctxt) ∧

  (* new_type_definition *)
  (((thyof ctxt, empty_elims), [], []) |- Comb pred witness ∧
   CLOSED pred ∧
   name ∉ (FDOM (tysof ctxt)) ∧
   abs ∉ (FDOM (tmsof ctxt)) ∧
   rep ∉ (FDOM (tmsof ctxt)) ∧
   abs ≠ rep
   ⇒ (TypeDefn name pred abs rep) updates' ctxt)
End

Definition extends'_def:
  extends' ⇔ RTC (λctxt2 ctxt1. ∃upd. ctxt2 = upd::ctxt1 ∧ upd updates' ctxt1)
End
val _ = Parse.add_infix("extends'",450,Parse.NONASSOC)

(* Initial theory context *)

Definition init_ctxt_def:
  init_ctxt = [NewConst (strlit "=") (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))
              ;NewType (strlit "bool") 0
              ;NewType (strlit "fun") 2]
End

val _ = export_theory()
