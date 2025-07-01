(*
  Defines the HOL inference system extended with the little theories
  module system.
*)
open preamble holSyntaxLibTheory mlstringTheory totoTheory holSyntaxTheory errorMonadTheory

val _ = new_theory "littleTheoriesSyntax"

val _ = monadsyntax.enable_monadsyntax();
val _ = monadsyntax.enable_monad("error");

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

Datatype: ethy = <| tms: mlstring |-> type;
                    tys: mlstring |-> num;
                    axs: term set;
                    etms: mlstring |-> type;
                    etys: mlstring |-> num;
                    eaxs: term set |>
End

Definition ctys_def:
  ctys thy = thy.tys ⊌ thy.etys
End

val _ = add_record_field ("ctys", “ctys”)

Definition ctms_def:
  ctms thy = thy.tms ⊌ thy.etms
End

val _ = add_record_field ("ctms", “ctms”)

Definition sigof'_def:
  sigof' thy = (thy.tys, thy.tms)
End

val _ = add_record_field ("sig", “sigof'”)

(* Standard signature includes the minimal type operators and constants *)

(* term_ok' has to check if types are valid through both the
types and eliminable types *)
Definition term_ok'_def:
  (term_ok' thy' (Var x ty) ⇔ type_ok thy'.ctys ty) ∧
  (term_ok' thy' (Const name ty) ⇔
     ∃ty0. FLOOKUP thy'.ctms name = SOME ty0 ∧
           type_ok thy'.ctys ty ∧
           is_instance ty0 ty) ∧
  (term_ok' thy' (Comb tm1 tm2) ⇔
     term_ok' thy' tm1 ∧
     term_ok' thy' tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok' thy' (Abs v tm) ⇔
     ∃x ty.
       v = Var x ty ∧
       type_ok thy'.ctys ty ∧
       term_ok' thy' tm)
End

Definition theory_ok'_def:
  theory_ok' (thy:ethy) ⇔
    (∀ty. ty ∈ FRANGE thy.tms ⇒ type_ok thy.tys ty) ∧
    (∀ty. ty ∈ FRANGE thy.etms ⇒ type_ok thy.ctys ty) ∧
    DISJOINT (FDOM thy.tys) (FDOM thy.etys) ∧
    DISJOINT (FDOM thy.tms) (FDOM thy.etms) ∧
    (∀p. p ∈ thy.axs ⇒ term_ok thy.sig p ∧ p has_type Bool) ∧
    (∀p. p ∈ thy.eaxs ⇒
         term_ok' thy p ∧ p has_type Bool) ∧
    is_std_sig thy.sig
End

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-'",450,Parse.NONASSOC)

Definition ty_esubst_def:
  (ty_esubst _ (Tyvar n) = Tyvar n) ∧
  (ty_esubst σ (Tyapp n []) =
   case FLOOKUP (FST σ) n of
   | NONE => Tyapp n []
   | SOME ty => ty) ∧
  (ty_esubst σ (Tyapp n ts) = Tyapp n (MAP (ty_esubst σ) ts))
Termination
  WF_REL_TAC ‘measure (type_size o SND)’ >> rw[] >> simp[]
  >> rename [‘MEM ty tys’] >> Induct_on ‘tys’ >> simp[] >> rw[]
  >> gvs[type_size_def]
End
        
Definition try_def:
  try (return v) f = return v ∧
  try (error e) f = f e
End

(* analog of INST_TYPE *)
Definition esubst_ty0_def:
  (esubst_ty0 env σ (Var n ty) =
   let
     tm = Var n ty;
     tm' = Var n (ty_esubst σ ty)
   in if REV_ASSOCD tm' env tm = tm then
        return tm'
      else error tm') ∧
  (esubst_ty0 env σ (Const n ty) =
   return $ Const n (ty_esubst σ ty)) ∧
  (esubst_ty0 env σ (Comb t1 t2) =
   do
     t1' <- esubst_ty0 env σ t1;
     t2' <- esubst_ty0 env σ t2;
     return $ Comb t1' t2'
   od) ∧
  (esubst_ty0 env σ (Abs v body) =
   let
     (n, ty) = dest_var v;
     ty' = ty_esubst σ ty;
     v' = Var n ty'
   in try
      do
        body' <- esubst_ty0 ((v, v')::env) σ body;
        return $ Abs v' body'
      od
      (λbad_v.
         if bad_v ≠ v' then
           error bad_v
         else 
           do
             inst <- esubst_ty0 [] σ body;
             n' <<- VARIANT inst (explode n) ty';
             body' <<- VSUBST [(Var n' ty, Var n ty)] body;
             ty'' <<- ty_esubst σ ty;
             env'' <<- (Var n' ty, Var n' ty'')::env;
             body'' <- esubst_ty0 env'' σ body';
             return $ Abs (Var n' ty'') body''
           od)
  )
Termination
  WF_REL_TAC ‘measure (sizeof o SND o SND)’ >> simp[SIZEOF_VSUBST]
End

Definition esubst_ty_def:
  esubst_ty σ tm = case esubst_ty0 [] σ tm of
                   | return v => v
                   | error e => ARB
End

Definition esubst_tm_def:
  esubst_tm σ (Var n ty) = Var n ty ∧
  esubst_tm σ (Abs v t) = Abs v (esubst_tm σ t) ∧
  esubst_tm σ (Comb t1 t2) = Comb (esubst_tm σ t1) (esubst_tm σ t2) ∧
  esubst_tm σ (Const n ty) = case FLOOKUP (SND σ) n of
                             | NONE => Const n ty
                             | SOME tm => tm
End

Definition esubst_def:
  esubst σ tm = esubst_tm σ $ esubst_ty σ tm
End

Theorem REV_ASSOCD_NEQ_DEFAULT:
  REV_ASSOCD t2 σ d ≠ d ⇒
  ∃t1. MEM (t1, t2) σ ∧ t1 ≠ d
Proof
  Induct_on ‘σ’ >> rw[REV_ASSOCD_def] >> Cases_on ‘h’ >> gvs[]
  >> dsimp[] >> metis_tac[]
QED

Theorem try_eq_error:
  try m f = error e ⇔ ∃e1. m = error e1 ∧ f e1 = error e
Proof
  Cases_on ‘m’ >> rw[EQ_IMP_THM, try_def]
QED

Theorem term_ok_rev_assocd:
  term_ok sig (REV_ASSOCD t1 env t2) ⇔
  (∃p t s. env = p ++ [(t, t1)] ++ s ∧ (∀e d. MEM (e, d) p ⇒ d ≠ t1)
           ∧ term_ok sig t)
  ∨ (∀e d. MEM (e, d) env ⇒ d ≠ t1) ∧ term_ok sig t2
Proof
  Induct_on ‘env’ >> rw[REV_ASSOCD_def]
  >> rename [‘h::env = _ ++ _ ++ _’] >> Cases_on ‘h’ >> gvs[]
  >- (iff_tac >> strip_tac
      >- (DISJ1_TAC >> qexists ‘[]’ >> simp[])
      >- (Cases_on ‘p’ >> gvs[])
      >- (metis_tac[]))
  >- (rw[EQ_IMP_THM] >> simp[FORALL_AND_THM]
      >- (qexistsl [‘(q,r)::p’] >> simp[])
      >- (Cases_on ‘p’ >> gvs[] >> metis_tac[]))
QED

Theorem has_type_var[simp] = hd (CONJUNCTS has_type_rules)
Theorem has_type_const[simp] = hd $ tl (CONJUNCTS has_type_rules)

Theorem term_ok_imp_welltyped:
  term_ok sig tm ⇒ welltyped tm
Proof
  Induct_on ‘tm’ >> rw[welltyped_def]
  >- (qexists ‘t’ >> rw[has_type_rules])
  >- (qexists ‘t’ >> rw[has_type_rules])
  >- (gvs[term_ok_def, welltyped_def] >> metis_tac[])
  >- (gvs[term_ok_def, welltyped_def] >> metis_tac[has_type_rules])
QED

Definition vsubst_tys_ok_def:
  vsubst_tys_ok ilist =
  (∀s s'. MEM (s',s) ilist ⇒
          ∃x ty. (s = Var x ty) ∧ s' has_type ty)
End

Theorem rev_assocd_neq_mem:
  REV_ASSOCD x l d ≠ d ⇒ MEM (REV_ASSOCD x l d, x) l
Proof
  metis_tac[REV_ASSOCD_MEM]
QED

Theorem neq_error:
  (∀e. x ≠ error e) ⇔ ∃v. x = return v
Proof
  Cases_on ‘x’ >> rw[]
QED

Theorem vsubst_has_type:
  ∀ilist. t has_type τ ∧ vsubst_tys_ok ilist ⇒ (VSUBST ilist t) has_type τ
Proof
  Induct_on ‘_ has_type _’ >> rw[]
  >> gvs[VSUBST_def]
  >- (gvs[vsubst_tys_ok_def]
      >> Cases_on ‘REV_ASSOCD (Var n τ) ilist (Var n τ) = Var n τ’
      >- rw[has_type_rules]
      >- (drule_then assume_tac rev_assocd_neq_mem
          >> first_x_assum drule >> rw[]))
  >- metis_tac[has_type_rules]
  >> rw[]
  >> (irule (last $ CONJUNCTS has_type_rules) >> first_x_assum irule
      >> gvs[vsubst_tys_ok_def, DISJ_IMP_THM, FORALL_AND_THM,
             MEM_FILTER, has_type_rules])
QED
        
Theorem welltyped_comb_vsubst:
  welltyped (Comb x y) ∧ vsubst_tys_ok lst
  ⇒ welltyped (Comb (VSUBST lst x) (VSUBST lst y))
Proof
  rw[welltyped_def] >> drule_all vsubst_has_type >> rw[VSUBST_def]
  >> metis_tac[]
QED

Theorem vsubst_tys_ok_cons[simp]:
  vsubst_tys_ok (x::xs) ⇔
    vsubst_tys_ok xs ∧ ∃n ty s'. x = (s', Var n ty) ∧ s' has_type ty
Proof
  rw[vsubst_tys_ok_def, DISJ_IMP_THM, FORALL_AND_THM, EQ_IMP_THM]
  >> Cases_on ‘x’ >> gvs[]
QED

Theorem vsubst_tys_ok_filter[simp]:
  vsubst_tys_ok lst ⇒ vsubst_tys_ok (FILTER P lst)
Proof
  rw[vsubst_tys_ok_def, MEM_FILTER]
QED

Theorem term_ok_vsubst:
  ∀x lst. 
    EVERY (λp. term_ok sig (FST p)) lst ∧ term_ok sig x ∧ vsubst_tys_ok lst
    ⇒ term_ok sig (VSUBST lst x)
Proof
  Induct_on ‘x’ >> rw[VSUBST_def, term_ok_def, term_ok_rev_assocd, EVERY_MEM]
  >- (Cases_on ‘∀e. ¬MEM (e,Var m t) lst’ >> rw[]
      >> qabbrev_tac
         ‘i = LEAST j. j < LENGTH lst ∧ SND (EL j lst) = Var m t’
      >> qexists ‘TAKE i lst’ >> CONV_TAC SWAP_EXISTS_CONV
      >> qexists ‘DROP (i+1) lst’ >> simp[Abbr ‘i’]
      >> numLib.LEAST_ELIM_TAC >> CONJ_TAC
      >- (gvs[MEM_EL] >> metis_tac[SND])
      >- (rw[] >> qexists ‘FST (EL n lst)’
          >> reverse $ rw[]
          >- (metis_tac[MEM_EL])
          >- (rw[MEM_EL] >> strip_tac >> gvs[EL_TAKE]
              >> metis_tac[SND])
          >- (qspecl_then [‘n’, ‘lst’] assume_tac TAKE_DROP
              >> ‘[(FST (EL n lst),Var m t)] ++ DROP (n + 1) lst
                  = DROP n lst’
                suffices_by simp[GSYM APPEND_ASSOC,
                                 Excl "APPEND_ASSOC"]
              >> simp[DROP_BY_DROP_SUC, ADD1]
              >> metis_tac[PAIR])))
  >- (gvs[GSYM EVERY_MEM] >> rpt $ first_x_assum drule >> rw[]
      >> gvs[term_ok_def] >> dxrule term_ok_imp_welltyped
         >> dxrule term_ok_imp_welltyped >> rw[welltyped_comb_vsubst])
  >- (rw[term_ok_def] >> first_x_assum irule >> rw[]
      >- rw[term_ok_def]
      >> gvs[EVERY_MEM, MEM_FILTER])
  >> first_x_assum irule >> rw[EVERY_MEM, MEM_FILTER]
QED

Theorem vsubst_tys_ok_nil[simp]:
  vsubst_tys_ok []
Proof
  rw[vsubst_tys_ok_def]
QED

Theorem VSUBST_nil:
  ∀tm. VSUBST [] tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, REV_ASSOCD_def]
QED

Theorem term_ok_vsubst_variant:
  ∀tm ty inst sig x σ. esubst_ty0 [] σ tm = return inst
       ∧ term_ok sig tm
       ∧ type_ok (tysof sig) ty
       ⇒ term_ok sig (VSUBST [(Var (VARIANT inst (explode x) (ty_esubst σ ty)) ty,
                               Var x ty)] tm)
Proof
  Induct_on ‘tm’
  >> rw[esubst_ty0_def, REV_ASSOCD_def, VSUBST_def, term_ok_def]
  >> rw[welltyped_comb_vsubst, term_ok_def, VSUBST_nil]
  >> (irule term_ok_vsubst >> rw[vsubst_tys_ok_def, term_ok_def])
QED

Theorem VARIANT_ENV_THM:
  ∀t x ty.
    ¬VFREE_IN (Var (VARIANT t x ty env) ty) t
    ∧ ¬(∃p. MEM (p, Var (VARIANT t x ty env) ty))
Proof
  cheat
QED

Theorem term_var_ok:
  ∀n sig ty. type_ok (tysof sig) ty ⇒ term_ok sig (Var n ty)
Proof
  rw[term_ok_def]
QED
      
Theorem variant_not_self:
  ∀tm n ty. Var (VARIANT tm n ty) ty ≠ tm
Proof
  rw[] >> qspecl_then [‘tm’, ‘n’, ‘ty’] assume_tac VARIANT_THM
  >> metis_tac[VFREE_IN_def]
QED

Theorem variant_name_not_self:
  ∀n ty x. VARIANT (Var n ty) x ty ≠ n
Proof
  rw[] >> qspecl_then [‘Var n ty’, ‘x’, ‘ty’] assume_tac VARIANT_THM
  >> metis_tac[VFREE_IN_def]
QED

Theorem bind_return_comb:
  ∀a b q. (do
            a' <- a;
            b' <- b;
            return (Comb a' b')
          od = return q)
          ⇒ ∃x y. a = return x ∧ b = return y ∧ q = Comb x y
Proof
  Cases_on ‘a’
  >> Cases_on ‘b’
  >> gvs[bind_EQ_error]
QED

Theorem VFREE_IN_VSUBST:
  ∀tm ilist.
    term_ok sig tm 
    ∧ (∀v1 v2. MEM (v1, v2) ilist ⇒
               ∃n1 t1 n2 t2. v1 = Var n1 t1 ∧ v2 = Var n2 t2 ∧ v1 ≠ v)
    ∧ VFREE_IN v (VSUBST ilist tm) ⇒ VFREE_IN v tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, VFREE_IN_def, term_ok_def]
  >- (Cases_on ‘REV_ASSOCD (Var m t) ilist (Var m t) = Var m t’ >> gvs[]
      >> drule rev_assocd_neq_mem >> rw[]
      >> first_x_assum drule >> rw[] >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- (gvs[dest_var_def, term_ok_def, EXISTS_MEM, MEM_FILTER]
      >> ‘∃en1 ety1 en2 ety2. e = (Var en1 ety1, Var en2 ety2)’ by metis_tac[PAIR]
      >> gvs[] >> strip_tac >> gvs[] >> first_x_assum drule >> rw[])
  >- (gvs[dest_var_def, term_ok_def, EXISTS_MEM, MEM_FILTER]
      >> ‘∃en1 ety1 en2 ety2. e = (Var en1 ety1, Var en2 ety2)’ by metis_tac[PAIR]
      >> gvs[] >> first_x_assum irule >> first_assum $ irule_at Any
      >> simp[MEM_FILTER] >> rw[] >> gvs[])
  >- (gvs[EVERY_MEM, MEM_FILTER, FORALL_PROD] >> first_x_assum irule
      >> first_x_assum $ irule_at Any >> simp[MEM_FILTER])
QED
        
Theorem esubst_ty0_never_errors:
  ∀env σ tm e. 
    (∀v1 v2. MEM (v1, v2) env ⇒ ∃n t1 t2. v1 = Var n t1 ∧ v2 = Var n t2)
    ∧ esubst_ty0 env σ tm = error e
    ∧ term_ok sig tm
    ∧ type_ok (tysof sig) ty
    ⇒ ∃n ty1 ty2.
        e = Var n (ty_esubst σ ty1) ∧ MEM (Var n ty2, e) env
        ∧ ty1 ≠ ty2 ∧ VFREE_IN (Var n ty1) tm
Proof
  recInduct esubst_ty0_ind >> rw[] >> gvs[esubst_ty0_def, AllCaseEqs()]
  >- (drule REV_ASSOCD_NEQ_DEFAULT >> rw[]
      >> first_x_assum drule >> rw[] >> metis_tac[])
  >- (gvs[bind_EQ_error, term_ok_def] >> metis_tac[])
  >> gvs[term_ok_def, try_eq_error, AllCaseEqs(), bind_EQ_error,
          FORALL_AND_THM, DISJ_IMP_THM]
  >- metis_tac[]
  >- (first_x_assum drule >> rw[] >> drule term_ok_vsubst_variant
      >> rw[] >> )
  >- cheat
QED

Theorem error_do_block:
  (∃q. do
          a' <- a;
          b' <- b;
          return (P a' b')
        od = return q)
        ⇔ ∃x y. a = return x ∧ b = return y
Proof
  Cases_on ‘a’
  >> Cases_on ‘b’
  >> gvs[bind_EQ_error]
QED

Theorem REPLACE_THIS:
  ∀P Q. (∃x. P x) ∧ (∃y. Q y) ⇒ (∃x y. P x ∧ Q y)
Proof
  metis_tac[]
QED

Theorem VSUBST_fresh:
  ¬VFREE_IN v tm ⇒ VSUBST [(v', v)] tm = tm
Proof
  Induct_on ‘tm’ >> rw[VSUBST_def, REV_ASSOCD_def, VSUBST_nil]
  >> gvs[]
QED

Theorem esubst_fresh_env:
  ∀tm σ v v'.
    ¬VFREE_IN v tm
    ⇒ esubst_ty0 [(v, v')] σ tm = esubst_ty0 [] σ tm
Proof
  Induct_on ‘tm’ >> rw[esubst_ty0_def, REV_ASSOCD_def, AllCaseEqs()]
  >> cheat
QED

Theorem esubst_ty0_safety:
  ∀tm sig σ.
    term_ok sig tm
    ⇒ ∃v. esubst_ty0 [] σ tm = return v
Proof
  Induct_on ‘tm’ >> rw[esubst_ty0_def]
  >- (drule REV_ASSOCD_NEQ_DEFAULT >> rw[])
  >- (gvs[term_ok_def]
      >> rpt $ first_x_assum (drule_then assume_tac)
      >> rpt $ first_x_assum (qspec_then ‘σ’ assume_tac)
      >> gvs[bind_EQ_error])
  >- (gvs[term_ok_def] >> rpt $ first_x_assum (drule_then assume_tac)
      >> rpt $ first_x_assum (qspec_then ‘σ’ assume_tac)
      >> Cases_on ‘∃e. esubst_ty0 [(Var x ty,Var x (ty_esubst σ ty))] σ tm'
                       = error e’
      >> gvs[term_ok_def, try_eq_error, AllCaseEqs(), bind_EQ_error,
             FORALL_AND_THM, DISJ_IMP_THM, try_def, neq_error]
      >> dxrule esubst_ty0_singleton_error >> rw[]
      >> Induct_on ‘tm'’)
QED

Definition esubsts_ok_def:
  (* substituting the variable doesn't semantically change the abs' meaning *)
  (esubsts_ok σ (Abs v body) ⇔
     ¬(∃p. v = esubst σ p ∧ VFREE_IN p body) ∧ esubsts_ok σ body) ∧

  (* term substitutions are type-consistent with any type substitutions *)
  (esubsts_ok σ (Const n ty) ⇔ typeof (esubst σ (Const n ty)) = ty_esubst σ ty) ∧

  (esubsts_ok σ (Comb l r) ⇔ esubsts_ok σ l ∧ esubsts_ok σ r) ∧
  (esubsts_ok _ (Var _ _) ⇔ T)
End

Inductive proves':
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok thy.ctys ty ∧
   (thy, es, h) |-' l === r
   ⇒ (thy, es, h) |-' (Abs (Var x ty) l) === (Abs (Var x ty) r))

[~ASSUME:]
  (theory_ok' thy ∧ p has_type Bool ∧ term_ok' thy p
   ⇒ (thy, {}, [p]) |-' p)

[~BETA:]
  (theory_ok' thy ∧ type_ok thy.ctys ty
   ∧ term_ok' thy t
   ⇒ (thy, {}, []) |-' Comb (Abs (Var x ty) t) (Var x ty) === t)

[~DEDUCT_ANTISYM:]
  ((thy, es1, h1) |-' c1 ∧
   (thy, es2, h2) |-' c2
   ⇒ (thy, es1 ∪ es2, term_union (term_remove c2 h1)
                                 (term_remove c1 h2))
     |-' c1 === c2)

[~EQ_MP:]
  ((thy, es1, h1) |-' p === q ∧
   (thy, es2, h2) |-' p' ∧ ACONV p p'
   ⇒ (thy, es1 ∪ es2, term_union h1 h2) |-' q)

[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
           ∃x ty. (s = Var x ty) ∧ s' has_type ty
                  ∧ term_ok' thy s') ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (VSUBST ilist) h) |-' VSUBST ilist c)

[~INST_TYPE:]
  ((EVERY (type_ok thy.ctys) (MAP FST tyin)) ∧
   (thy, es, h) |-' c
   ⇒ (thy, es, term_image (INST tyin) h) |-' INST tyin c)

[~MK_COMB:]
  ((thy, es1, h1) |-' l1 === r1 ∧
   (thy, es2, h2) |-' l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, es1 ∪ es2, term_union h1 h2) |-' Comb l1 l2 === Comb r1 r2)

[~REFL:]
  (theory_ok' thy ∧ term_ok' thy t
   ⇒ (thy, {}, []) |-' t === t)

[~axioms:]
  (theory_ok' thy ∧ c ∈ thy.axs
   ⇒ (thy, {}, []) |-' c)

[~elim_discharge:]
  ((thy, es1, []) |-' c1 ∧ (thy, es2, h2) |-' c2
   ⇒ (thy, (es2 DIFF {c1}) ∪ es1, h2) |-' c2)

[~elim_inst:]
  ((thy, es, h) |-' c
   ∧ (∀p. p ∈ es ⇒ esubsts_ok σ p ∧ term_ok thy.sig (esubst σ p) ∧ (esubst σ p) has_type Bool)
   ∧ (∀p. MEM p h ⇒ esubsts_ok σ p ∧ term_ok thy.sig (esubst σ p) ∧ (esubst σ p) has_type Bool)
   ∧ esubsts_ok σ c
   ∧ (esubst σ c) has_type Bool
   ∧ term_ok thy.sig (esubst σ c)
   ⇒ (thy, IMAGE (esubst σ) es, MAP (esubst σ) h) |-' esubst σ c)

[~elim_axioms:]
  (theory_ok' thy ∧ c ∈ thy.eaxs
   ⇒ (thy, {c}, []) |-' c)
End

Definition lift_thy_def:
  lift_thy (thy:thy) = <| tms := tmsof thy;
                          tys := tysof thy;
                          etms := FEMPTY;
                          etys := FEMPTY;
                          axs := axsof thy;
                          eaxs := {} |>
End

Theorem tmsof_lift_thy[simp]:
  (lift_thy thy).tms = tmsof thy
Proof
  simp[lift_thy_def]
QED

Theorem tysof_lift_thy[simp]:
  (lift_thy thy).tys = tysof thy
Proof
  simp[lift_thy_def]
QED

Theorem axsof_lift_thy[simp]:
  (lift_thy thy).axs = axsof thy
Proof
  simp[lift_thy_def]
QED

Theorem eaxsof_lift_thy[simp]:
  (lift_thy thy).eaxs = {}
Proof
  simp[lift_thy_def]
QED

Theorem etmsof_lift_thy[simp]:
  (lift_thy thy).etms = FEMPTY
Proof
  simp[lift_thy_def]
QED

Theorem etysof_lift_thy[simp]:
  (lift_thy thy).etys = FEMPTY
Proof
  simp[lift_thy_def]
QED

Theorem sigof_lift_thy[simp]:
  (lift_thy thy).sig = sigof thy
Proof
  simp[lift_thy_def, sigof'_def]
QED

Theorem ctys_lift_thy[simp]:
  (lift_thy thy).ctys = tysof thy
Proof
  simp[lift_thy_def, ctys_def]
QED

Theorem ctms_lift_thy[simp]:
  (lift_thy thy).ctms = tmsof thy
Proof
  simp[lift_thy_def, ctms_def]
QED

Theorem theory_ok'_lift_thy[simp]:
  theory_ok' (lift_thy thy) ⇔ theory_ok thy
Proof
  rw[theory_ok_def, theory_ok'_def, lift_thy_def]
QED

Theorem term_ok'_lift_thy[simp]:
  term_ok' (lift_thy thy) tm ⇔ term_ok (sigof thy) tm
Proof
  Induct_on ‘tm’
  >> rw[term_ok_def, term_ok'_def, lift_thy_def]
QED

Theorem proves_imp_proves':
  ∀h. (thy, h) |- c ⇒ (lift_thy thy, {}, h) |-' c
Proof
  Induct_on ‘$|-’ >> rw[]
  >- (irule proves'_ABS >> rw[])
  >- (irule proves'_ASSUME >> rw[])
  >- (irule proves'_BETA >> rw[])
  >- (dxrule_all_then (ACCEPT_TAC o SRULE[]) proves'_DEDUCT_ANTISYM)
  >- (dxrule_all proves'_EQ_MP >> rw[])
  >- (irule proves'_INST >> rw[])
  >- (irule proves'_INST_TYPE >> rw[])
  >- (dxrule_all proves'_MK_COMB >> rw[])
  >- (irule proves'_REFL >> rw[])
  >- (irule proves'_axioms >> rw[])
QED

Theorem type_ind =
        TypeBase.induction_of``:holSyntax$type``
          |> Q.SPECL[`P`,`EVERY P`]
          |> SIMP_RULE std_ss [EVERY_DEF]
          |> UNDISCH_ALL
          |> CONJUNCT1
          |> DISCH_ALL
          |> Q.GEN`P`

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

Theorem proves_imp_theory_ok:
  ∀thy h. (thy, h) |- c ⇒ theory_ok thy
Proof
  Induct_on ‘$|-’ >> rw[] >> rw[]
QED

Theorem axiom_weakening:
  ∀A B h. ((sig, A), h) |- c
          ∧ (∀p. p ∈ B ⇒ term_ok sig p ∧ p has_type Bool)
          ∧ A ⊆ B
          ⇒ ((sig, B), h) |- c
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
      >> gvs[theory_ok_def, type_ok_def, SUBSET_DEF])
QED

Theorem axioms_eliminable:
  ∀thy1 thy2 h2 c1 c2.
    (thy2, h2) |- c2 ∧ (thy1, []) |- c1
    ∧ sigof thy1 = sigof thy2
    ⇒ ((sigof thy1, (axsof thy2 DIFF {c1}) UNION axsof thy1), h2) |- c2
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
      >- (rw[] >> irule axiom_weakening >> rw[]
          >> gvs[theory_ok_def] >> drule proves_imp_theory_ok >> rw[theory_ok_def]
          >> qexists ‘axsof thy1’ >> rw[] >> Cases_on ‘thy1’ >> gvs[])
      >- (irule proves_axioms >> rw[] >> metis_tac[proves_theory_ok_ext]))
QED

Definition drop_thy:
  (drop_thy used_eaxs thy'):thy = ((thy'.ctys, thy'.ctms), thy'.axs UNION used_eaxs)
End

Theorem sigof_drop_thy[simp]:
  sigof (drop_thy es thy) = (thy.ctys, thy.ctms)
Proof
  rw[drop_thy]
QED

Theorem axsof_drop_thy:
  thy.axs ⊆ axsof (drop_thy es thy)
Proof
  rw[drop_thy]
QED

Theorem type_ok_weakening:
  ∀ty. type_ok ts1 ty ⇒ type_ok (ts1 ⊌ ts2) ty
Proof
  Induct_on ‘ty’ using type_ind >> gvs[type_ok_def, FLOOKUP_FUNION, EVERY_MEM]
QED

Theorem term_ok_weakening:
  ∀tm. term_ok (tys, tms) tm ⇒ term_ok (tys ⊌ tys1, tms ⊌ tms1) tm
Proof
  Induct_on ‘tm’ >> rw[term_ok_def, type_ok_weakening]
  >> qexists ‘ty0’ >> rw[FLOOKUP_FUNION, type_ok_weakening] >> metis_tac[]
QED

Theorem is_std_sig_funion:
  is_std_sig (tys, tms) ⇒ is_std_sig (tys ⊌ tys1, tms ⊌ tms1)
Proof
  rw[is_std_sig_def, FLOOKUP_FUNION]
QED

Theorem theory_ok_drop_thy:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok thy.sig a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
QED

Theorem term_ok'_imp_term_ok:
  term_ok' thy c ⇒ term_ok (thy.ctys, thy.ctms) c
Proof
  Induct_on ‘c’ >> rw[term_ok'_def, term_ok_def]
QED

Theorem term_ok_imp_term_ok':
  term_ok (thy.ctys, thy.ctms) c ⇒ term_ok' thy c
Proof
  Induct_on ‘c’ >> rw[term_ok'_def, term_ok_def]
QED

Theorem theory_ok_drop_thy_alt:
  ∀es. theory_ok' thy ∧ (∀a. a ∈ es ⇒ term_ok' thy a ∧ a has_type Bool) ⇒
       theory_ok (drop_thy es thy)
Proof
  rw[theory_ok'_def, theory_ok_def, drop_thy]
  >> gvs[ctys_def, ctms_def, sigof'_def, FRANGE_FUNION,
         type_ok_weakening, term_ok_weakening, is_std_sig_funion]
  >> metis_tac[term_ok'_imp_term_ok, ctys_def, ctms_def]
QED

Theorem proves_imp_theory_ok':
  ∀thy h es c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
QED

Theorem thy_axs_diff:
  c ∉ a ⇒
  a ∪ (b DIFF {c} ∪ d) = ((a ∪ b) DIFF {c}) ∪ (a ∪ d)
Proof
  rw[UNION_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]
QED

Theorem thy_axs_diff_alt:
  c ∈ a ⇒
  a ∪ (b DIFF {c} ∪ d) = a ∪ b ∪ d
Proof
  rw[UNION_DEF, EXTENSION, EQ_IMP_THM] >> metis_tac[]
QED

Theorem proves'_imp_theory_ok:
  ∀thy es h c. (thy, es, h) |-' c ⇒ theory_ok' thy
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[]
QED

Theorem term_ok_term_ok'_weakening:
  term_ok thy.sig p ⇒ term_ok' thy p
Proof
  rw[] >> irule term_ok_imp_term_ok'
  >> gvs[sigof'_def, ctms_def, ctys_def, term_ok_weakening]
QED

Theorem used_eaxs_ok:
  ∀thy' used_eaxs h c.
    (thy', used_eaxs, h) |-' c
    ⇒ ∀e. e ∈ used_eaxs ⇒ term_ok' thy' e ∧ e has_type Bool
Proof
  Induct_on ‘$|-'’ >> rw[] >> rw[] >> gvs[theory_ok'_def, term_ok_term_ok'_weakening]
QED

Theorem esubst_equation:
  esubst_ok
  esubst σ (a === b) = esubst σ a === esubst σ b
Proof
  cheat
QED

Theorem proves_substitutable:
  ∀sig h c.
    ((sig, axs ∪ es), h) |- c ∧
    theory_ok (sig, axs ∪ IMAGE (esubst σ) es) ∧
    (∀p. p ∈ es ⇒
         esubsts_ok σ p ∧ term_ok sig (esubst σ p) ∧
         esubst σ p has_type Bool) ∧
    (∀p. MEM p h ⇒
         esubsts_ok σ p ∧ term_ok sig (esubst σ p) ∧
         esubst σ p has_type Bool) ∧ esubsts_ok σ c ∧
    esubst σ c has_type Bool ∧ term_ok sig (esubst σ c) ⇒
    ((sig, axs ∪ IMAGE (esubst σ) es), MAP (esubst σ) h) |- esubst σ c
Proof
  Induct_on ‘$|-’ >> rw[esubst_def, esubst_equation]
  >- (irule proves_ABS >> rw[] >> cheat)
  >- (irule proves_ASSUME >> rw[])
  >- (irule proves_BETA >> rw[] >> cheat)
  >- (irule proves_DEDUCT_ANTISYM >> rw[] >> cheat)
  >- (irule proves_EQ_MP >> qexistsl [‘p’, ‘c’] >> rw[] >> cheat)
  >- (cheat >> irule proves_INST)
  >- (cheat >> irule proves_INST_TYPE)
  >- (irule proves_MK_COMB >> rw[] >> cheat)
  >- (irule proves_axioms >> rw[] >> gvs[] >> cheat)
  >- (irule proves_axioms >> rw[] >> gvs[]
      >- cheat
      >- metis_tac[])
QED

Theorem drop_thy_weakening:
  (drop_thy B thy', h) |- c ∧ B ⊆ A
  ∧ (∀ax. ax ∈ A ⇒ term_ok (thy'.ctys, thy'.ctms) ax ∧ ax has_type Bool)
  ⇒ (drop_thy A thy', h) |- c
Proof
  rw[drop_thy] >> irule axiom_weakening >> rw[]
  >> drule proves_imp_theory_ok >> rw[theory_ok_def, ctms_def, ctys_def]
  >> gvs[ctys_def, ctms_def] >> first_assum $ irule_at Any >> ASM_SET_TAC[]
QED

Theorem proves'_imp_proves:
  ∀thy' c h used_eaxs.
    (thy', used_eaxs, h) |-' c ⇒ (drop_thy used_eaxs thy', h) |- c
Proof
  Induct_on ‘$|-'’ >> rw[]
  >- (irule proves_ABS >> rw[])
  >- (irule proves_ASSUME >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_BETA >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_DEDUCT_ANTISYM
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_EQ_MP
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_INST_TYPE >> rw[] >> first_x_assum drule
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_MK_COMB >> rw[]
      >> ‘es1 ⊆ es1 ∪ es2 ∧ es2 ⊆ es1 ∪ es2’ by SET_TAC[]
      >> rpt $ dxrule used_eaxs_ok >> rw[]
      >> rpt $ dxrule_then dxrule drop_thy_weakening
      >> impl_tac >> rpt $ dxrule proves_imp_theory_ok' >> rw[]
      >> metis_tac[term_ok'_imp_term_ok])
  >- (irule proves_REFL >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok])
  >- (irule proves_axioms >> rw[theory_ok_drop_thy, term_ok'_imp_term_ok]
      >> metis_tac[axsof_drop_thy, SUBSET_DEF])
  >- (Cases_on ‘c ∈ thy.axs’ >> gvs[drop_thy]
      >- (rw[thy_axs_diff_alt, UNION_COMM] >> irule axiom_weakening
          >> drule proves'_imp_theory_ok >> rw[]
          >> gvs[theory_ok'_def, used_eaxs_ok, term_ok'_imp_term_ok, term_ok_term_ok'_weakening]
          >> rpt $ dxrule used_eaxs_ok >> rw[term_ok'_imp_term_ok]
          >> qexists ‘thy.axs ∪ es2’ >> rw[] >> SET_TAC[])
      >- (rw[thy_axs_diff]
          >> qspecl_then [‘((thy.ctys, thy.ctms), thy.axs ∪ es1)’,
                          ‘((thy.ctys, thy.ctms), thy.axs ∪ es2)’,
                          ‘h2’, ‘c’, ‘c'’]
                         assume_tac axioms_eliminable
          >> gvs[]))
  >- (gvs[drop_thy] >> irule proves_substitutable >> rw[] >> gvs[EVERY_MEM]
      >> metis_tac[sigof'_def, ctys_def, ctms_def, term_ok_weakening])
  >- (irule proves_axioms >> rw[]
      >- (irule theory_ok_drop_thy_alt >> gvs[theory_ok'_def])
      >> rw[drop_thy])
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
