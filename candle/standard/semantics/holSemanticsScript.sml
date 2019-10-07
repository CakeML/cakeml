(*
  Define semantics for HOL sequents, in particular the notion of entailment
  i.e. valid sequents, which are those that satisfied by any model of the
  theory context.
*)
open HolKernel boolLib boolSimps bossLib lcsymtacs holSyntaxTheory holSyntaxExtraTheory setSpecTheory

val _ = new_theory"holSemantics"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[DB.fetch"holSyntax""type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

Overload inhabited = ``λs. ∃x. x <: s``

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type signature, and is only constrained for defined type
   operators applied to the right number of non-empty arguments. *)

Type tyass = ``:mlstring -> 'U list -> 'U``

val is_type_assignment_def = xDefine "is_type_assignment"`
  is_type_assignment0 ^mem tysig (δ:'U tyass) ⇔
    FEVERY
      (λ(name,arity).
        ∀ls. LENGTH ls = arity ∧ EVERY inhabited ls ⇒
             inhabited ((δ name) ls))
      tysig`
Overload is_type_assignment = ``is_type_assignment0 ^mem``

(* A type valuation is a map from type variable names to non-empty sets. *)

Type tyval = ``:mlstring -> 'U``

val is_type_valuation_def = xDefine "is_type_valuation"`
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)`
Overload is_type_valuation = ``is_type_valuation0 ^mem``

(* Semantics of types. Simply applies the valuation and assignment. *)

val typesem_def = tDefine "typesem"`
  (typesem δ (τ:'U tyval) (Tyvar s) = τ s) ∧
  (typesem δ τ (Tyapp name args) =
    (δ name) (MAP (typesem δ τ) args))`
  (type_rec_tac "SND o SND")

(* A term assignment is a map from a constant name and a list of values for the
   free type variables to a value for the constant. The assignment is with
   respect to a signature and is only constrained for defined constants. *)

Type tmass = ``:mlstring -> 'U list -> 'U``

val is_term_assignment_def = xDefine "is_term_assignment"`
  is_term_assignment0 ^mem tmsig δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty).
        ∀τ. is_type_valuation τ ⇒
              γ name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty))))) <: typesem δ τ ty)
      tmsig`
Overload is_term_assignment = ``is_term_assignment0 ^mem``

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

Type tmval = ``:mlstring # type -> 'U``

val is_term_valuation_def = xDefine "is_term_valuation"`
  is_term_valuation0 ^mem tysig δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tysig ty ⇒ σ (v,ty) <: typesem δ τ ty`
Overload is_term_valuation = ``is_term_valuation0 ^mem``

(* An interpretation is a pair of assignments.
   A valuation is a pair of valuations. *)

Type interpretation = ``:'U tyass # 'U tmass``
Overload tyaof = ``FST:'U interpretation->'U tyass``
Overload tmaof = ``SND:'U interpretation->'U tmass``
Type valuation = ``:'U tyval # 'U tmval``
Overload tyvof = ``FST:'U valuation->'U tyval``
Overload tmvof = ``SND:'U valuation->'U tmval``

val is_valuation_def = xDefine"is_valuation"`
  is_valuation0 ^mem tysig δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tysig δ (tyvof v) (tmvof v)`
Overload is_valuation = ``is_valuation0 ^mem``

(* term assignment for instances of constants *)

val instance_def = new_specification("instance_def",["instance"],
  Q.prove(`∃f. ∀tmsig (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmsig name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmsig i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar) (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`,
    simp[GSYM SKOLEM_THM] >> rw[] >>
    Cases_on`FLOOKUP tmsig name`>>simp[] >>
    qmatch_assum_rename_tac`FLOOKUP tmsig name = SOME ty0` >>
    Cases_on`is_instance ty0 ty` >> fs[] >>
    qmatch_assum_rename_tac`ty = TYPE_SUBST tyin ty0` >>
    qho_match_abbrev_tac`∃f. ∀tyin. P tyin ⇒ f = Q tyin` >>
    qexists_tac`Q tyin` >>
    rw[Abbr`P`,Abbr`Q`,FUN_EQ_THM] >> rpt AP_TERM_TAC >>
    rw[listTheory.MAP_EQ_f] >> rw[] >>
    fs[listTheory.MEM_MAP,mlstringTheory.implode_explode] >>
    metis_tac[TYPE_SUBST_tyvars]))

(* Semantics of terms. *)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (tmsig:tmsig) (i:'U interpretation) (v:'U valuation) (Var x ty) = tmvof v (x,ty)) ∧
  (termsem0 ^mem tmsig i v (Const name ty) = instance tmsig i name ty (tyvof v)) ∧
  (termsem0 ^mem tmsig i v (Comb t1 t2) =
   termsem0 ^mem tmsig i v t1 ' (termsem0 ^mem tmsig i v t2)) ∧
  (termsem0 ^mem tmsig i v (Abs (Var x ty) b) =
   Abstract (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
     (λm. termsem0 ^mem tmsig i (tyvof v, ((x,ty)=+m)(tmvof v)) b))`
Overload termsem = ``termsem0 ^mem``

(* Satisfaction of sequents. *)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem i (sig:sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem (tmsof sig) i v t = True) h
      ⇒ termsem (tmsof sig) i v c = True`
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
Overload satisfies = ``satisfies0 ^mem``

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

val is_interpretation_def = xDefine "is_interpretation"`
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)`
Overload is_interpretation = ``is_interpretation0 ^mem``

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem (δ:'U tyass) ⇔
    (∀dom rng. δ (strlit "fun") [dom;rng] = Funspace dom rng) ∧
    (δ (strlit "bool") [] = boolset)`
Overload is_std_type_assignment = ``is_std_type_assignment0 ^mem``

local
  open Parse
  val hs = HardSpace 1
  fun bs n = BreakSpace(1,n)
in
val _ = Parse.add_rule{term_name = "interprets",
                       fixity = Infix (NONASSOC,450),
                       pp_elements = [TOK "interprets", hs, TM, hs, TOK "on", bs 2, TM, hs, TOK "as", bs 2],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))}
end
val interprets_def = xDefine"interprets"`
  interprets0 ^mem γ name vs f ⇔ ∀τ. is_type_valuation τ ⇒ γ name (MAP τ vs) = f (MAP τ vs)`
Overload interprets = ``interprets0 ^mem``

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem (i:'U interpretation) ⇔
    is_std_type_assignment (tyaof i) ∧
    tmaof i interprets (strlit "=") on [(strlit "A")] as
    λl. (Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y))))`
Overload is_std_interpretation = ``is_std_interpretation0 ^mem``

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

val models_def = xDefine"models"`
  models0 ^mem i (thy:thy) ⇔
    is_interpretation (sigof thy) i ∧
    is_std_interpretation i ∧
    ∀p. p ∈ (axsof thy) ⇒ i satisfies (sigof thy,[],p)`
val _ = Parse.add_infix("models",450,Parse.NONASSOC)
Overload models = ``models0 ^mem``

(* Validity of sequents. *)

val entails_def = xDefine"entails"`
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀i. i models thy
        ⇒ i satisfies (sigof thy,h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
Overload "|=" = ``entails0 ^mem``

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val`
Overload is_structure = ``is_structure0 ^mem``

val _ = export_theory()
