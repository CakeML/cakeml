open HolKernel boolLib boolSimps bossLib lcsymtacs holSyntaxTheory setSpecTheory
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

(* A polymorphic value is a function from a type valuation to a set *)

val _ = Parse.type_abbrev("polyval",``:'U tyval -> 'U``)

(* Semantics of types as polymorphic values. Simply applies the valuation and
   assignment. *)

val typesem_def = tDefine "typesem"`
  (typesem δ (Tyvar s) (τ:'U tyval) = τ s) ∧
  (typesem δ (Tyapp name args) τ =
    (δ name) (MAP (λty. typesem δ ty τ) args))`
  (type_rec_tac "FST o SND")

(* A term assignment is a map from constant names to semantic functions. Each
   function takes an instance of the type of the constant, and returns the
   (polymorphic) meaning of the constant at that type. The assignment is with
   respect to an environment and is only constrained for defined constants and
   correct instances of their types. *)

val _ = Parse.type_abbrev("tmass",``:string -> type -> 'U polyval``)

val is_term_assignment_def = xDefine "is_term_assignment"`
  is_term_assignment0 ^mem tmenv δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty0).
        ∀ty. is_instance ty0 ty ⇒
          ∀τ. is_type_valuation τ ⇒
                γ name ty τ <: typesem δ ty τ)
      tmenv`
val _ = Parse.overload_on("is_term_assignment",``is_term_assignment0 ^mem``)

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

val _ = Parse.type_abbrev("tmval",``:string # type -> 'U``)

val is_term_valuation_def = xDefine "is_term_valuation"`
  is_term_valuation0 ^mem δ τ (σ:'U tmval) ⇔
    ∀v ty. σ (v,ty) <: typesem δ ty τ`
val _ = Parse.overload_on("is_term_valuation",``is_term_valuation0 ^mem``)

(* An interpretation is a pair of assignments. *)

val _ = Parse.type_abbrev("interpretation",``:'U tyass # 'U tmass``)

(* Semantics of terms as polymorphic values. *)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (i:'U interpretation) (Var x ty) (σ:'U tmval) = σ (x,ty)) ∧
  (termsem0 ^mem i (Const name ty) σ = SND i name ty) ∧
  (termsem0 ^mem i (Comb t1 t2) σ = λτ.
   termsem0 ^mem i t1 σ τ ' (termsem0 ^mem i t2 σ τ)) ∧
  (termsem0 ^mem i (Abs x ty b) σ = λτ.
   Abstract (typesem (FST i) ty τ) (typesem (FST i) (typeof b) τ)
     (λm. termsem0 ^mem i b (((x,ty)=+(K m))σ) τ))`
val _ = Parse.overload_on("termsem",``termsem0 ^mem``)

(* Satisfaction of sequents. *)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem i (h,c) ⇔
    ∀τ σ.
      is_type_valuation τ ∧
      is_term_valuation (FST i) σ ∧
      EVERY (λt. termsem i t σ τ = True) h
      ⇒ termsem i c σ τ = True`
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
val _ = Parse.overload_on("satisfies",``satisfies0 ^mem``)

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

val is_interpretation_def = xDefine "is_interpretation"`
  is_interpretation0 ^mem (tyenv,tmenv) (δ,γ) ⇔
    is_type_assignment tyenv δ ∧
    is_term_assignment tmenv δ γ`
val _ = Parse.overload_on("is_interpretation",``is_interpretation0 ^mem``)

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem δ ⇔
    (δ "fun" = λls. case ls of [dom;rng] => Funspace dom rng | _ => ∅) ∧
    (δ "bool" = λls. case ls of [] => boolset | _ => ∅)`
val _ = Parse.overload_on("is_std_type_assignment",``is_std_type_assignment0 ^mem``)

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem (δ,γ) ⇔
    is_std_type_assignment δ ∧
    ∀ty. γ "=" (Fun ty (Fun ty Bool)) =
         λτ. let mty = typesem δ ty τ in
               (Abstract mty (Funspace mty boolset)
                 (λx. Abstract mty boolset (λy. Boolean (x = y))))`
val _ = Parse.overload_on("is_std_interpretation",``is_std_interpretation0 ^mem``)

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

val is_model_def = xDefine"is_model"`
  is_model0 ^mem (sig, axs) i ⇔
    is_interpretation sig i ∧
    is_std_interpretation i ∧
    EVERY (λp. i satisfies ([],p)) axs`
val _ = Parse.overload_on("is_model",``is_model0 ^mem``)

(* Validity of sequents. *)

val entails_def = xDefine"entails"`
  entails0 ^mem (ctxt,h) c ⇔
    is_std_sig (sigof ctxt) ∧
    EVERY (term_ok (sigof ctxt)) (c::h) ∧
    EVERY (λt. t has_type Bool) (c::h) ∧
    ∀i. is_model (sigof ctxt, axioms ctxt) i
        ⇒ i satisfies (h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
val _ = Parse.overload_on("|=",``entails0 ^mem``)

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig int σ τ ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_type_valuation τ ∧
    is_term_valuation (FST int) σ`
val _ = Parse.overload_on("is_structure",``is_structure0 ^mem``)

val _ = export_theory()
