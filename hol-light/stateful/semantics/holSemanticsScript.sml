open HolKernel boolLib boolSimps bossLib lcsymtacs holSyntaxTheory holSyntaxExtraTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holSemantics"

val mem = ``mem:'U->'U->bool``

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[DB.fetch"holSyntax""type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val _ = Parse.overload_on("inhabited",``λs. ∃x. x <: s``)

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type environment, and is only constrained for defined type
   operators applied to the right number of non-empty arguments. *)

val _ = Parse.type_abbrev("tyass",``:string -> 'U list -> 'U``)

val is_type_assignment_def = xDefine "is_type_assignment"`
  is_type_assignment0 ^mem tyenv (δ:'U tyass) ⇔
    FEVERY
      (λ(name,arity).
        ∀ls. LENGTH ls = arity ∧ EVERY inhabited ls ⇒
             inhabited ((δ name) ls))
      tyenv`
val _ = Parse.overload_on("is_type_assignment",``is_type_assignment0 ^mem``)

(* A type valuation is a map from type variable names to non-empty sets. *)

val _ = Parse.type_abbrev("tyval",``:string -> 'U``)

val is_type_valuation_def = xDefine "is_type_valuation"`
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)`
val _ = Parse.overload_on("is_type_valuation",``is_type_valuation0 ^mem``)

(* Semantics of types. Simply applies the valuation and assignment. *)

val typesem_def = tDefine "typesem"`
  (typesem δ (τ:'U tyval) (Tyvar s) = τ s) ∧
  (typesem δ τ (Tyapp name args) =
    (δ name) (MAP (typesem δ τ) args))`
  (type_rec_tac "SND o SND")

(* A term assignment is a map from a constant name and a list of values for the
   free type variables to a value for the constant. The assignment is with
   respect to an environment and is only constrained for defined constants. *)

val _ = Parse.type_abbrev("tmass",``:string -> 'U list -> 'U``)

val is_term_assignment_def = xDefine "is_term_assignment"`
  is_term_assignment0 ^mem tmenv δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty).
        ∀τ. is_type_valuation τ ⇒
              γ name (MAP τ (STRING_SORT (tyvars ty))) <: typesem δ τ ty)
      tmenv`
val _ = Parse.overload_on("is_term_assignment",``is_term_assignment0 ^mem``)

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

val _ = Parse.type_abbrev("tmval",``:string # type -> 'U``)

val is_term_valuation_def = xDefine "is_term_valuation"`
  is_term_valuation0 ^mem tyenv δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tyenv ty ⇒ σ (v,ty) <: typesem δ τ ty`
val _ = Parse.overload_on("is_term_valuation",``is_term_valuation0 ^mem``)

(* An interpretation is a pair of assignments.
   A valuation is a pair of valuations. *)

val _ = Parse.type_abbrev("interpretation",``:'U tyass # 'U tmass``)
val _ = Parse.overload_on("tyaof",``FST:'U interpretation->'U tyass``)
val _ = Parse.overload_on("tmaof",``SND:'U interpretation->'U tmass``)
val _ = Parse.type_abbrev("valuation",``:'U tyval # 'U tmval``)
val _ = Parse.overload_on("tyvof",``FST:'U valuation->'U tyval``)
val _ = Parse.overload_on("tmvof",``SND:'U valuation->'U tmval``)

val is_valuation_def = xDefine"is_valuation"`
  is_valuation0 ^mem tyenv δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tyenv δ (tyvof v) (tmvof v)`
val _ = Parse.overload_on("is_valuation",``is_valuation0 ^mem``)

(* term assignment for instances of constants *)

val instance_def = new_specification("instance_def",["instance"],
  prove(``∃f. ∀tmenv (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmenv name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmenv i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar) (STRING_SORT (tyvars ty0)))``,
    simp[GSYM SKOLEM_THM] >> rw[] >>
    Cases_on`FLOOKUP tmenv name`>>simp[] >>
    qmatch_assum_rename_tac`FLOOKUP tmenv name = SOME ty0`[] >>
    Cases_on`is_instance ty0 ty` >> fs[] >>
    qmatch_assum_rename_tac`ty = TYPE_SUBST tyin ty0`[] >>
    qho_match_abbrev_tac`∃f. ∀tyin. P tyin ⇒ f = Q tyin` >>
    qexists_tac`Q tyin` >>
    rw[Abbr`P`,Abbr`Q`,FUN_EQ_THM] >> rpt AP_TERM_TAC >>
    rw[listTheory.MAP_EQ_f] >> rw[] >> metis_tac[TYPE_SUBST_tyvars]))

(* Semantics of terms. *)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (Γ:sig) (i:'U interpretation) (v:'U valuation) (Var x ty) = tmvof v (x,ty)) ∧
  (termsem0 ^mem Γ i v (Const name ty) = instance (tmsof Γ) i name ty (tyvof v)) ∧
  (termsem0 ^mem Γ i v (Comb t1 t2) =
   termsem0 ^mem Γ i v t1 ' (termsem0 ^mem Γ i v t2)) ∧
  (termsem0 ^mem Γ i v (Abs x ty b) =
   Abstract (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
     (λm. termsem0 ^mem Γ i (tyvof v, ((x,ty)=+m)(tmvof v)) b))`
val _ = Parse.overload_on("termsem",``termsem0 ^mem``)

(* Satisfaction of sequents. *)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem i (sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem sig i v t = True) h
      ⇒ termsem sig i v c = True`
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
val _ = Parse.overload_on("satisfies",``satisfies0 ^mem``)

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

val is_interpretation_def = xDefine "is_interpretation"`
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)`
val _ = Parse.overload_on("is_interpretation",``is_interpretation0 ^mem``)

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem (δ:'U tyass) ⇔
    (δ "fun" = λls. case ls of [dom;rng] => Funspace dom rng | _ => ∅) ∧
    (δ "bool" = λls. case ls of [] => boolset | _ => ∅)`
val _ = Parse.overload_on("is_std_type_assignment",``is_std_type_assignment0 ^mem``)

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
val _ = Parse.overload_on("interprets",``interprets0 ^mem``)

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem (i:'U interpretation) ⇔
    is_std_type_assignment (tyaof i) ∧
    tmaof i interprets "=" on ["A"] as
    λl. (Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y))))`
val _ = Parse.overload_on("is_std_interpretation",``is_std_interpretation0 ^mem``)

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

val models_def = xDefine"models"`
  models0 ^mem i (thy:thy) ⇔
    is_interpretation (sigof thy) i ∧
    is_std_interpretation i ∧
    ∀p. p ∈ (axsof thy) ⇒ i satisfies (sigof thy,[],p)`
val _ = Parse.add_infix("models",450,Parse.NONASSOC)
val _ = Parse.overload_on("models",``models0 ^mem``)

(* Validity of sequents. *)

val entails_def = xDefine"entails"`
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    ∀i. i models thy
        ⇒ i satisfies (sigof thy,h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
val _ = Parse.overload_on("|=",``entails0 ^mem``)

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val`
val _ = Parse.overload_on("is_structure",``is_structure0 ^mem``)

val _ = export_theory()
