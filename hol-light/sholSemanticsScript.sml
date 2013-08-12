open HolKernel boolLib bossLib lcsymtacs listTheory sholSyntaxTheory modelSetTheory
val _ = numLib.prefer_num()
val _ = new_theory"sholSemantics"

val (semantics_rules,semantics_ind,semantics_cases) = Hol_reln`
  (typeset τ (Tyvar s) (τ s)) ∧

  (typeset τ (Tyapp (Typrim "bool" 0) []) boolset) ∧

  (typeset τ x mx ∧ typeset τ y my
   ⇒
   typeset τ (Tyapp (Typrim "->" 2) [x;y]) (funspace mx my)) ∧

  (LENGTH (tvars p) = LENGTH ts ∧
   tyin = ZIP (MAP Tyvar (STRING_SORT (tvars p)), ts) ∧
   INST tyin p has_type Fun rty Bool ∧
   semantics FEMPTY τ (INST tyin p) mp ∧
   typeset τ rty mrty
   ⇒
   typeset τ (Tyapp (Tydefined s p) ts) (mrty suchthat holds mp)) ∧

  (FLOOKUP σ (n,ty) = SOME m
   ⇒
   semantics σ τ (Var n ty) m) ∧

  (typeset τ ty mty
   ⇒
   semantics σ τ (Const "=" (Fun ty (Fun ty Bool)) Prim)
    (abstract mty (funspace mty boolset)
       (λx. abstract mty boolset (λy. boolean (x = y))))) ∧

  (typeset τ ty mty
   ⇒
   semantics σ τ (Const "@" (Fun (Fun ty Bool) ty) Prim)
     (abstract (funspace mty boolset) mty
       (λp. let mp = (mty suchthat holds p) in
            ch (if ∃x. x <: mp then mp else mty)))) ∧

  (t has_type tyt ∧
   TYPE_SUBST tyin tyt = ty ∧
   semantics σ τ (INST tyin t) mt
   ⇒
   semantics σ τ (Const s ty (Defined t)) mt) ∧

  (typeset τ rty mrty ∧
   typeset τ atr maty
   ⇒
   semantics σ τ (Const s (Fun aty rty) (Tyrep op p))
    (abstract maty mrty (λx. x))) ∧

  (typeset τ rty mrty ∧
   typeset τ atr maty ∧
   p has_type (Fun rtyp Bool) ∧
   TYPE_SUBST tyin rtyp = rty ∧
   semantics FEMPTY τ (INST tyin p) mp
   ⇒
   semantics σ τ (Const s (Fun rty aty) (Tyabs op p))
    (abstract mrty maty (λx. if holds mp x then x else ch maty))) ∧

  (semantics σ τ t mt ∧
   semantics σ τ u mu
   ⇒
   semantics σ τ (Comb t u) (apply mt mu)) ∧

  (typeset τ ty mty ∧
   b has_type tyb ∧
   typeset τ tyb mtyb ∧
   (∀x. semantics (σ |+ ((n,ty),x)) τ b (mb x))
   ⇒
   semantics σ τ (Abs n ty b) (abstract mty mtyb mb))`

val _ = export_theory()
