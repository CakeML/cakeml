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
Overload etysof = ``tysof o elimsigof``
Overload etmsof = ``tmsof o elimsigof``

(* Standard signature includes the minimal type operators and constants *)

(* term_ok' has to check if types are valid through both the types and
 eliminable types *)
Definition term_ok'_def:
  (term_ok' (sig:sig) (esig:sig) (Var x ty) ⇔
     type_ok (FUNION (tysof sig) (tysof esig)) ty) ∧
  (term_ok' sig esig (Const name ty) ⇔
     ∃ty0. FLOOKUP (FUNION (tmsof sig) (tmsof esig)) name = SOME ty0 ∧
           type_ok (FUNION (tysof sig) (tysof esig)) ty ∧
           is_instance ty0 ty) ∧
  (term_ok' sig esig (Comb tm1 tm2) ⇔
     term_ok' sig esig tm1 ∧
     term_ok' sig esig tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok' sig esig (Abs v tm) ⇔
     ∃x ty.
       v = Var x ty ∧
       type_ok (FUNION (tysof sig) (tysof esig)) ty ∧
       term_ok' sig esig tm)
End

Definition theory_ok'_def:
  theory_ok' (thy:thy') ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (FUNION (tysof thy) (etysof thy)) ty) ∧
    (∀ty. ty ∈ FRANGE (etmsof thy) ⇒ type_ok (FUNION (tysof thy) (etysof thy)) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    (∀p. p ∈ (elimaxsof thy) ⇒
         term_ok' (sigof thy) (elimsigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)
End

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-'",450,Parse.NONASSOC)

Inductive proves':
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok (FUNION (tysof thy) (etysof thy)) ty ∧
   (thy, es, h) |-' l === r
   ⇒ (thy, es, h) |-' (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok' thy ∧ p has_type Bool ∧ term_ok' (sigof thy) (elimsigof thy) p
   ⇒ (thy, es, [p]) |-' p)

[~BETA:]
  (theory_ok' thy ∧ type_ok (FUNION (tysof thy) (etysof thy)) ty
   ∧ term_ok' (sigof thy) (elimsigof thy) t
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
           ∃x ty. (s = Var x ty) ∧ s' has_type ty
                  ∧ term_ok' (sigof thy) (elimsigof thy) s') ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (VSUBST ilist) h) |-' VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok (FUNION (tysof thy) (etysof thy))) (MAP FST tyin)) ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (INST tyin) h) |-' INST tyin c)

[~MK_COMB:]
  ((thy, es, h1) |-' l1 === r1 ∧
   (thy, es, h2) |-' l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, es, term_union h1 h2) |-' Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok' thy ∧ term_ok' (sigof thy) (elimsigof thy) t
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
  type_ok (tysof thy) ty ⇒
    type_ok (tysof (thy,empty_elims) ⊌ etysof (thy,empty_elims)) ty
Proof
  Cases_on ‘thy’ >> simp[type_ok_def, empty_elims_def]
QED

Theorem type_ok_imp_elim_rw:
  type_ok (tysof (sigof thy)) ty ⇒
    type_ok (tysof (thy,empty_elims) ⊌ etysof (thy,empty_elims)) ty
Proof
  Cases_on ‘thy’ >> simp[type_ok_def, empty_elims_def]
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
  Cases_on ‘thy’
  >> rw[theory_ok'_def, term_ok_imp_elim, theory_sig_eq_elim,
        type_ok_sigof_imp_elim, theory_ok_def, is_std_sig_def,
        empty_elims_def, theory_ok_def]
QED

Theorem term_ok'_imp:
  term_ok' (sigof (thy, empty_elims)) (elimsigof (thy, empty_elims)) c
  ⇔ term_ok (sigof thy) c
Proof
  Cases_on ‘thy’ >> rw[empty_elims_def]
  >> Induct_on ‘c’ >> rw[term_ok_def] >> gvs[term_ok'_def]
  >> metis_tac[]
QED

Theorem term_ok_sigof_imp:
  term_ok (sigof thy) c ⇒ term_ok (sigof (thy, es)) c
Proof
  Cases_on ‘thy’ >> rw[theory_sig_eq_elim]
QED

Theorem etysof_nil:
  etysof (thy, empty_elims) = FEMPTY
Proof
  rw[empty_elims_def]
QED

Theorem tysof_eq_elim_union:
  tysof (sigof thy) = tysof (thy,empty_elims) ⊌ etysof (thy,empty_elims)
Proof
  Cases_on ‘thy’ >> rw[empty_elims_def]
QED

Theorem type_ok_imp:
  type_ok (tysof (s, empty_elims)) ty
  ⇔ type_ok (FUNION (tysof (s, empty_elims)) (etysof (s, empty_elims))) ty
Proof
  Cases_on ‘s’ >> Cases_on ‘q’ >> rw[empty_elims_def]
QED

Theorem proves_imp_proves':
 ∀h. (thy, h) |- c ⇒ ((thy, empty_elims), [], h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves'_ABS >> simp[type_ok_imp_elim_rw])
  >- (irule proves'_ASSUME >> rw[theory_ok_imp_elim, term_ok'_imp])
  >- (irule proves'_BETA >> rw[theory_ok_imp_elim, term_ok'_imp, type_ok_imp_elim])
  >- (irule proves'_DEDUCT_ANTISYM >> rw[])
  >- (irule proves'_EQ_MP >> metis_tac[])
  >- (irule proves'_INST >> metis_tac[term_ok'_imp])
  >- (irule proves'_INST_TYPE >> metis_tac[tysof_eq_elim_union])
  >- (irule proves'_MK_COMB >> rw[])
  >- (irule proves'_REFL >> rw[theory_ok_imp_elim, term_ok'_imp])
  >- (irule proves'_axioms >> rw[axsof_elim_thy, theory_ok_imp_elim])
QED

Definition consts_of:
  (consts_of (Var _ _) = {}) ∧
  (consts_of (Const n ty) = {(n, ty)}) ∧
  (consts_of (Comb s t) = consts_of s UNION consts_of t) ∧
  (consts_of (Abs _ body) = consts_of body)
End

Overload tyvars_set = “λtm. set (tyvars tm)”

Overload tyset = “(λtm. BIGUNION (IMAGE (tyvars_set o SND) (consts_of tm))):term->mlstring set”
Overload tysetl = “(FOLDR (λb a. a UNION (tyset b)) {}):term list->mlstring set”
Overload tysets = “(BIGUNION o IMAGE tyset):term set->mlstring set”

Overload tmset = “(IMAGE FST o consts_of):term->mlstring set”
Overload tmsetl = “(FOLDR (λb a. a UNION (tmset b)) {}):term list->mlstring set”
Overload tmsets = “(BIGUNION o IMAGE tmset):term set->mlstring set”

Definition remove_tysig_def:
  remove_tysig ty ((tms, tys), axs) = ((tms, tys \\ ty), axs)
End

Definition remove_tmsig_def:
  remove_tmsig tm ((tms, tys), axs) = ((tms \\ tm, tys), axs)
End

(*
if there exists some type constant, ty, that does
not appear in the the hypothesis nor the conclusion,
nor as part of any axiom,
then you can safely remove it from the theory signature.
*)
Theorem strip_redun_ty_consts:
  ∀thy h. (thy, h) |- c ∧ ty ∉ tyset c ∧ ty ∉ tysetl h
          ∧ ty ∉ tysets (axsof thy)
          ⇒ (remove_tysig ty thy, h) |- c
Proof
  cheat
QED

(*
if there exists some constant, tm, that does
not appear in the the hypothesis nor the conclusion,
nor any axiom,
then you can safely remove it from the theory signature.
*)
Theorem strip_redun_tm_consts:
  ∀thy h. (thy, h) |- c ∧ tm ∉ tmset c ∧ tm ∉ tmsetl h
          ∧ tm ∉ tmsets (axsof thy)
          ⇒ (remove_tmsig tm thy, h) |- c
Proof
  cheat
QED

(*
this pair of strip_redun theorems are useful, as we can then
show that//.......
*)

(* induct over |-, chooses leftmost by default *)
(*
this theorem states that given c1 and c2 are deriveable
in their own respective contexts and hypotheses, then
if those contexts share signatures, then c2 can still
be derived with that signature, the union of their hypotheses
and
*)

Theorem proves_theory_ok:
  ∀thy h c. (thy, h) |- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|-’ >> rw[] >> rw[]
QED

Theorem proves_theory_ok_ext:
  theory_ok thy1 ∧ (thy2, h) |- c ∧ sigof thy1 = sigof thy2
  ⇒ theory_ok (sigof thy1, axsof thy1 DIFF {c1} ∪ axsof thy2)
Proof
  rw[] >> drule proves_theory_ok >> gvs[theory_ok_def] >> metis_tac[]
QED

Theorem axiom_weakening:
  ∀axs h. ((sig, axs), h) |- c
          ∧ (∀p. p ∈ A ⇒ term_ok sig p ∧ p has_type Bool)
          ⇒ ((sig, A UNION axs), h) |- c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> rw[] >> gvs[])
  >- (irule proves_ASSUME >> rw[] >> gvs[theory_ok_def] >> metis_tac[])
  >- (irule proves_BETA >> rw[] >> gvs[theory_ok_def] >> metis_tac[])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> metis_tac[])
  >- (irule proves_INST >> rw[] >> gvs[])
  >- (irule proves_INST_TYPE >> rw[] >> gvs[])
  >- (irule proves_MK_COMB >> rw[] >> gvs[])
  >- (irule proves_REFL >> rw[theory_ok_def, type_ok_def]
      >> gvs[theory_ok_def, type_ok_def])
  >- (irule proves_axioms >> rw[theory_ok_def, type_ok_def]
      >> gvs[theory_ok_def, type_ok_def])
QED

Theorem axioms_eliminable:
  ∀thy1 thy2 h2 c1 c2. (thy2, h2) |- c2 ∧ (thy1, []) |- c1
  ∧ sigof thy1 = sigof thy2
  ⇒ ((sigof thy1, (axsof thy2 DIFF {c1}) UNION axsof thy1),
     h2) |- c2
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (irule proves_BETA >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> rw[] >> metis_tac[])
  >- (irule proves_INST >> rw[])
  >- (irule proves_INST_TYPE >> rw[])
  >- (irule proves_MK_COMB >> rw[])
  >- (irule proves_REFL >> rw[] >> metis_tac[proves_theory_ok_ext])
  >- (Cases_on ‘c1 = c2’
      >- (rw[] >> irule axiom_weakening >> gvs[theory_ok_def]
          >> Cases_on ‘thy’ >> gvs[])
      >- (irule proves_axioms >> rw[] >> metis_tac[proves_theory_ok_ext]))
QED

Definition insert_sig_def:
  insert_sig (etys, etms) (((tys, tms), axs):thy)
  = (((FUNION tys etys, FUNION tms etms), axs):thy)
End

Theorem insert_sig_type_ok:
  type_ok (tysof (sigof (thy,esig,eaxs)) ⊌
                 tysof (elimsigof (thy,esig,eaxs))) ty
  ⇔ type_ok (tysof (sigof (insert_sig esig thy))) ty
Proof
  Cases_on ‘thy’ >> Cases_on ‘esig’ >> Cases_on ‘q’
  >> rw[insert_sig_def]
QED

Theorem is_std_sig_ext:
  is_std_sig (p, q) ⇒ is_std_sig (FUNION p p', FUNION q q')
Proof
  Induct_on ‘p’ >> rw[is_std_sig_def] >> gvs[is_std_sig_def]
  >> Cases_on ‘FLOOKUP f1 k’ >> rw[FLOOKUP_FUNION]
QED

(* if everything in l is type_ok, then adding more types will
 keep it ok *)
Theorem every_type_ok_ext:
  EVERY (λa. type_ok p a) l ⇒ EVERY (λa. type_ok (p ⊌ p') a) l
Proof
  cheat
QED

Theorem type_ok_ext:
  type_ok p t ⇒ type_ok (FUNION p q) t
Proof
  Cases_on ‘t’ >> rw[type_ok_def] >> gvs[type_ok_def]
  >> rw[FLOOKUP_FUNION, every_type_ok_ext]
QED

Theorem term_ok_ext:
  term_ok (p, q) c ⇒ term_ok (FUNION p p', FUNION q q') c
Proof
  Induct_on ‘c’ >> rw[term_ok_def] >> gvs[term_ok_def]
  >> rw[type_ok_ext] >> qexists ‘ty0’ >> rw[FLOOKUP_FUNION]
  >> metis_tac[]
QED

Theorem insert_sig_theory_ok:
  theory_ok' (thy,esig,eaxs) ⇒ theory_ok (insert_sig esig thy)
Proof
  Cases_on ‘esig’ >> Cases_on ‘thy’ >> Cases_on ‘q'’
  >> rw[theory_ok_def, insert_sig_def] >> gvs[theory_ok'_def]
  >- (drule_all IN_FRANGE_FUNION_suff >> rw[])
  >- rw[term_ok_ext]
  >- rw[is_std_sig_ext]
QED

Theorem term_ok'_imp_insert_sig:
  term_ok' (sigof (thy',esig,eaxs)) (elimsigof (thy',esig,eaxs)) c
  ⇒ term_ok (sigof (insert_sig esig thy')) c
Proof
  Induct_on ‘c’ >> Cases_on ‘thy'’ >> rw[term_ok_def] >> gvs[term_ok'_def]
  >> Cases_on ‘esig’ >> Cases_on ‘q’ >> rw[insert_sig_def] >> gvs[] >> metis_tac[]
QED

Theorem insert_sig_every_type_ok:
  EVERY (type_ok (tysof (sigof (thy',esig,eaxs)) ⊌
                        tysof (elimsigof (thy',esig,eaxs)))) (MAP FST tyin)
  ⇒ EVERY (type_ok (tysof (insert_sig esig thy'))) (MAP FST tyin)
Proof
  cheat
QED

Theorem insert_sig_axsof:
  c ∈ axsof (thy, esig, eaxs) ⇒ c ∈ axsof (insert_sig esig thy)
Proof
  Cases_on ‘thy’ >> rw[] >> Cases_on ‘q’ >> Cases_on ‘q'’ >> Cases_on ‘esig’
  >> rw[insert_sig_def]
QED

Theorem proves'_imp_proves:
  ∀h thy esig eaxs c. ((thy, (esig, eaxs)), [], h) |-' c
      ==> (insert_sig esig thy, h) |- c
Proof
  Induct_on ‘$|-'’ >> rw[]
  >- (irule proves_ABS >> rw[insert_sig_def] >> metis_tac[insert_sig_type_ok])
  >- (irule proves_ASSUME >> rw[term_ok'_imp_insert_sig]
      >> metis_tac[insert_sig_theory_ok, term_ok'_imp_insert_sig])
  >- (irule proves_BETA >> rw[] >> metis_tac[
          insert_sig_theory_ok, term_ok'_imp_insert_sig, insert_sig_type_ok])
  >- (irule proves_DEDUCT_ANTISYM >> rw[])
  >- (irule proves_EQ_MP >> metis_tac[])
  >- (irule proves_INST >> metis_tac[term_ok'_imp_insert_sig])
  >- (irule proves_INST_TYPE >> metis_tac[insert_sig_every_type_ok])
  >- (irule proves_MK_COMB >> rw[])
  >- (irule proves_REFL >> rw[]
      >> metis_tac[insert_sig_theory_ok, term_ok'_imp_insert_sig])
  >- (irule proves_axioms >> rw[] >> metis_tac[insert_sig_theory_ok, insert_sig_axsof])
  >> irule proves_EQ_MP >> qexistsl [‘c’, ‘c’] >> cheat
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
