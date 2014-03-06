open HolKernel boolLib boolSimps bossLib lcsymtacs holSyntaxTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holSemantics"

val mem = ``mem:'U->'U->bool``

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[DB.fetch"holSyntax""type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val _ = Parse.overload_on("inhabited",``λs. ∃x. x <: s``)

(* A type valuation is a map from type variable names to non-empty sets. *)

val _ = Parse.type_abbrev("tyval",``:string -> 'U``)

val is_type_valuation_def = xDefine "is_type_valuation"`
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)`
val _ = Parse.overload_on("is_type_valuation",``is_type_valuation0 ^mem``)

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type environment, and assigns the empty set to undefined
   operators or applications to the wrong number of arguments. *)

val _ = Parse.type_abbrev("tyass",``:string -> 'U list -> 'U``)

val is_type_assignment_def = xDefine "is_type_assignment"`
  is_type_assignment0 ^mem tyenv (δ:'U tyass) ⇔
    (∀name. name ∉ FDOM tyenv ⇒ δ name = K ∅) ∧
    FEVERY
      (λ(name,arity).
        ∀ls. (LENGTH ls = arity ∧
              EVERY inhabited ls) ⇔
             inhabited ((δ name) ls))
      tyenv`
val _ = Parse.overload_on("is_type_assignment",``is_type_assignment0 ^mem``)

(* Semantics of types. *)

val typesem_def = tDefine "typesem"`
  (typesem (τ:'U tyval) δ (Tyvar s) = τ s) ∧
  (typesem τ δ (Tyapp name args) =
    (δ name) (MAP (typesem τ δ) args))`
  (type_rec_tac "SND o SND")

(* A term valuation is a map from a variable to an element of the meaning of
   its type (if any). *)

val _ = Parse.type_abbrev("tmval",``:string # type -> 'U``)

val is_term_valuation_def = xDefine "is_term_valuation"`
  is_term_valuation0 ^mem τ δ (σ:'U tmval) ⇔
    ∀v ty. inhabited (typesem τ δ ty) ⇒
           σ (v,ty) <: typesem τ δ ty`
val _ = Parse.overload_on("is_term_valuation",``is_term_valuation0 ^mem``)

(* A term assignment is a map from constant names to semantic functions. Each
   function takes an instance of the type of the constant and a type valuation,
   and returns the meaning of the constant at that type in that valuation. The
   assignment is with respect to an environment and is only constrained for
   defined constants and correct instances of their types. *)

val _ = Parse.type_abbrev("tmass",``:string -> type -> 'U tyval -> 'U``)

val is_term_assignment_def = xDefine "is_term_assignment"`
  is_term_assignment0 ^mem tmenv δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty0).
        ∀ty. is_instance ty0 ty ⇒
          ∀τ. is_type_valuation τ ⇒
                γ name ty τ <: typesem τ δ ty)
      tmenv`
val _ = Parse.overload_on("is_term_assignment",``is_term_assignment0 ^mem``)

(* A complete valuation is a pair of type/term valuations.
   An interpretation is a pair of assignments. *)

val _ = Parse.type_abbrev("valuation", ``:'U tyval # 'U tmval``)

val is_valuation_def = xDefine "is_valuation"`
  is_valuation0 ^mem δ (τ,σ) ⇔
    is_type_valuation τ ∧
    is_term_valuation τ δ σ`
val _ = Parse.overload_on("is_valuation",``is_valuation0 ^mem``)

val _ = Parse.type_abbrev("interpretation",``:'U tyass # 'U tmass``)

(* Semantics of terms. *)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (τ,σ) (i:'U interpretation) (Var x ty) = σ (x,ty)) ∧
  (termsem0 ^mem (v:'U valuation) (δ,γ) (Const name ty) = γ name ty τ) ∧
  (termsem0 ^mem (τ,σ) i (Comb t1 t2) =
   termsem0 ^mem (τ,σ) i t1 ' (termsem0 ^mem (τ,σ) i t2)) ∧
  (termsem0 ^mem (τ,σ) (δ,γ) (Abs x ty b) =
   Abstract (typesem τ δ ty) (typesem τ δ (typeof b))
     (λm. termsem0 ^mem (τ,((x,ty)=+m)σ) (δ,γ) b))`
val _ = Parse.overload_on("termsem",``termsem0 ^mem``)

(* Satisfaction of sequents. *)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem i (h,c) ⇔
    EVERY (λt. t has_type Bool) (c::h) ∧
    ∀v. is_valuation (FST i) v ∧
        EVERY (λt. termsem v i t = True) h
      ⇒ termsem v i c = True`
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
         λτ. let mty = typesem τ δ ty in
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
    ∀i. is_model (sigof ctxt, axioms ctxt) i
        ⇒ i satisfies (h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
val _ = Parse.overload_on("|=",``entails0 ^mem``)


(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig val int ⇔
    is_std_sig sig ∧
    is_valuation (FST int) val ∧
    is_std_interpretation int ∧
    is_interpretation sig int`
val _ = Parse.overload_on("is_structure",``is_structure0 ^mem``)

val _ = export_theory()
