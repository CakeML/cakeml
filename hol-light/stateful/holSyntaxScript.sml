open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory listTheory alistTheory holSyntaxLibTheory
val _ = temp_tight_equality()
val _ = new_theory "holSyntax"

(* HOL types *)

val _ = Hol_datatype`type
  = Tyvar of string
  | Tyapp of string => type list`

val _ = Parse.overload_on("Fun",``λs t. Tyapp "fun" [s;t]``)
val _ = Parse.overload_on("Bool",``Tyapp "bool" []``)

val domain_def = Define`domain (Fun s t) = s`
val codomain_def = Define`codomain (Fun s t) = t`
val domain_def = save_thm("domain_def",SIMP_RULE(srw_ss())[]domain_def)
val codomain_def = save_thm("codomain_def",SIMP_RULE(srw_ss())[]codomain_def)
val _ = export_rewrites["domain_def","codomain_def"]

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[definition"type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

(* HOL terms *)

val _ = Hol_datatype`term
  = Var of string => type
  | Const of string => type
  | Comb of term => term
  | Abs of string => type => term`

val _ = Parse.overload_on("Equal",``λty. Const "=" (Fun ty (Fun ty Bool))``)

(* Assignment of types to terms (where possible) *)

val _ = Parse.add_infix("has_type",450,Parse.NONASSOC)

val (has_type_rules,has_type_ind,has_type_cases) = Hol_reln`
  ((Var   n ty) has_type ty) ∧
  ((Const n ty) has_type ty) ∧
  (s has_type (Fun dty rty) ∧
   t has_type dty
   ⇒
   (Comb s t) has_type rty) ∧
  (t has_type rty ⇒
   (Abs n dty t) has_type (Fun dty rty))`

(* A term is welltyped if it has a type. typeof calculates it. *)

val welltyped_def = Define`
  welltyped tm = ∃ty. tm has_type ty`

val typeof_def = Define`
  (typeof (Var n   ty) = ty) ∧
  (typeof (Const n ty) = ty) ∧
  (typeof (Comb s t)   = codomain (typeof s)) ∧
  (typeof (Abs n ty t) = Fun ty (typeof t))`
val _ = export_rewrites["typeof_def"]

(* Auxiliary relation used to define alpha-equivalence. This relation is
   parameterised by the lists of variables bound above the terms. *)

val (RACONV_rules,RACONV_ind,RACONV_cases) = Hol_reln`
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  ((ty1 = ty2) ∧ RACONV ((Var x1 ty1,Var x2 ty2)::env) (t1,t2)
    ⇒ RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2))`

(* Alpha-equivalence. *)

val ACONV_def = Define`
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)`

(* Alpha-respecting union of two lists of terms.
   Retain duplicates in the second list. *)

val TERM_UNION_def = Define`
  TERM_UNION [] l2 = l2 ∧
  TERM_UNION (h::t) l2 =
    let subun = TERM_UNION t l2 in
    if EXISTS (ACONV h) subun then subun else h::subun`

(* Whether a variables (or constant) occurs free in a term. *)

val VFREE_IN_def = Define`
  (VFREE_IN v (Var x ty) ⇔ (Var x ty = v)) ∧
  (VFREE_IN v (Const x ty) ⇔ (Const x ty = v)) ∧
  (VFREE_IN v (Comb s t) ⇔ VFREE_IN v s ∨ VFREE_IN v t) ∧
  (VFREE_IN v (Abs x ty t) ⇔ (Var x ty ≠ v) ∧ VFREE_IN v t)`
val _ = export_rewrites["VFREE_IN_def"]

(* Closed terms: those with no free variables. *)

val CLOSED_def = Define`
  CLOSED tm = ∀x ty. ¬(VFREE_IN (Var x ty) tm)`

(* Producing a variant of a variable, guaranteed
   to not be free in a given term. *)

val VFREE_IN_FINITE = store_thm("VFREE_IN_FINITE",
  ``∀t. FINITE {x | VFREE_IN x t}``,
  Induct >> simp[VFREE_IN_def] >- (
    qmatch_abbrev_tac`FINITE z` >>
    qmatch_assum_abbrev_tac`FINITE x` >>
    qpat_assum`FINITE x`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE y` >>
    qsuff_tac`z = x ∪ y`>-metis_tac[FINITE_UNION] >>
    simp[Abbr`x`,Abbr`y`,Abbr`z`,EXTENSION] >> metis_tac[]) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE x` >>
  qmatch_abbrev_tac`FINITE z` >>
  qsuff_tac`∃y. z = x DIFF y`>-metis_tac[FINITE_DIFF] >>
  simp[Abbr`z`,Abbr`x`,EXTENSION] >>
  metis_tac[IN_SING])

val VFREE_IN_FINITE_ALT = store_thm("VFREE_IN_FINITE_ALT",
  ``∀t ty. FINITE {x | VFREE_IN (Var x ty) t}``,
  rw[] >> match_mp_tac (MP_CANON SUBSET_FINITE) >>
  qexists_tac`IMAGE (λt. case t of Var x y => x) {x | VFREE_IN x t}` >>
  simp[VFREE_IN_FINITE,IMAGE_FINITE] >>
  simp[SUBSET_DEF] >> rw[] >>
  HINT_EXISTS_TAC >> simp[])

val PRIMED_NAME_EXISTS = store_thm("PRIMED_NAME_EXISTS",
  ``∃n. ¬(VFREE_IN (Var (APPEND x (GENLIST (K #"'") n)) ty) t)``,
  qspecl_then[`t`,`ty`]mp_tac VFREE_IN_FINITE_ALT >>
  disch_then(mp_tac o CONJ PRIMED_INFINITE) >>
  disch_then(mp_tac o MATCH_MP INFINITE_DIFF_FINITE) >>
  simp[GSYM MEMBER_NOT_EMPTY] >> rw[] >> metis_tac[])

val LEAST_EXISTS = prove(
  ``(∃n. P n) ⇒ ∃k. P k ∧ ∀m. m < k ⇒ ¬(P m)``,
  metis_tac[whileTheory.LEAST_EXISTS])

val VARIANT_PRIMES_def = new_specification
  ("VARIANT_PRIMES_def"
  ,["VARIANT_PRIMES"]
  ,(PRIMED_NAME_EXISTS
   |> HO_MATCH_MP LEAST_EXISTS
   |> Q.GENL[`ty`,`x`,`t`]
   |> SIMP_RULE std_ss [SKOLEM_THM]))

val VARIANT_def = Define`
  VARIANT t x ty = APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty))`

val VARIANT_THM = store_thm("VARIANT_THM",
  ``∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t``,
  metis_tac[VARIANT_def,VARIANT_PRIMES_def])

(* Substitution for type variables in a type. *)

val TYPE_SUBST_def = tDefine"TYPE_SUBST"`
  (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) ∧
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) ∧
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))`
(type_rec_tac "SND")
val _ = export_rewrites["TYPE_SUBST_def"]
val _ = Parse.overload_on("is_instance",``λty0 ty. ∃i. ty = TYPE_SUBST i ty0``)

(* Substitution for term variables in a term. *)

val VSUBST_def = Define`
  (VSUBST ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (VSUBST ilist (Const x ty) = Const x ty) ∧
  (VSUBST ilist (Comb s t) = Comb (VSUBST ilist s) (VSUBST ilist t)) ∧
  (VSUBST ilist (Abs x ty t) =
    let ilist' = FILTER (λ(s',s). ¬(s = Var x ty)) ilist in
    let t' = VSUBST ilist' t in
    if EXISTS (λ(s',s). VFREE_IN (Var x ty) s' ∧ VFREE_IN s t) ilist'
    then let z = VARIANT t' x ty in
         let ilist'' = CONS (Var z ty,Var x ty) ilist' in
         Abs z ty (VSUBST ilist'' t)
    else Abs x ty t')`

(* A measure on terms, used in proving
   termination of type instantiation. *)

val sizeof_def = Define`
  sizeof (Var x ty) = 1 ∧
  sizeof (Const x ty) = 1 ∧
  sizeof (Comb s t) = 1 + sizeof s + sizeof t ∧
  sizeof (Abs x ty t) = 2 + sizeof t`
val _ = export_rewrites["sizeof_def"]

val SIZEOF_VSUBST = store_thm("SIZEOF_VSUBST",
  ``∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t``,
  Induct >> simp[VSUBST_def] >> rw[VSUBST_def] >> simp[] >- (
    Q.ISPECL_THEN[`ilist`,`Var s t`,`Var s t`]mp_tac REV_ASSOCD_MEM >>
    rw[] >> res_tac >> pop_assum SUBST1_TAC >> simp[] )
  >- metis_tac[] >>
  first_x_assum match_mp_tac >>
  simp[MEM_FILTER] >>
  rw[] >> res_tac >> fs[] )

val sizeof_positive = store_thm("sizeof_positive",
  ``∀t. 0 < sizeof t``,
  Induct >> simp[])

(* Instantiation of type variables in terms *)

val INST_CORE_def = tDefine"INST_CORE"`
  (INST_CORE env tyin (Var x ty) =
     let tm = Var x ty in
     let tm' = Var x (TYPE_SUBST tyin ty) in
     if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm') ∧
  (INST_CORE env tyin (Const x ty) =
    Result(Const x (TYPE_SUBST tyin ty))) ∧
  (INST_CORE env tyin (Comb s t) =
    let sres = INST_CORE env tyin s in
    if IS_CLASH sres then sres else
    let tres = INST_CORE env tyin t in
    if IS_CLASH tres then tres else
    let s' = RESULT sres and t' = RESULT tres in
    Result (Comb s' t')) ∧
  (INST_CORE env tyin (Abs x ty t) =
    let ty' = TYPE_SUBST tyin ty in
    let env' = (Var x ty,Var x ty')::env in
    let tres = INST_CORE env' tyin t in
    if IS_RESULT tres then Result(Abs x ty' (RESULT tres)) else
    let w = CLASH tres in
    if (w ≠ Var x ty') then tres else
    let x' = VARIANT (RESULT(INST_CORE [] tyin t)) x ty' in
    let t' = VSUBST [Var x' ty,Var x ty] t in
    let ty' = TYPE_SUBST tyin ty in
    let env' = (Var x' ty,Var x' ty')::env in
    let tres = INST_CORE env' tyin t' in
    if IS_RESULT tres then Result(Abs x' ty' (RESULT tres)) else tres)`
(WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST])

val INST_def = Define`INST tyin tm = RESULT(INST_CORE [] tyin tm)`

(* Type variables in a type. *)

val tyvars_def = tDefine"tyvars"`
  tyvars (Tyvar v) = [v] ∧
  tyvars (Tyapp v tys) = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys`
(type_rec_tac "I")

(* Type variables in a term. *)

val tvars_def = Define`
  (tvars (Var n ty) = tyvars ty) ∧
  (tvars (Const n ty) = tyvars ty) ∧
  (tvars (Comb s t) = LIST_UNION (tvars s) (tvars t)) ∧
  (tvars (Abs n ty t) = LIST_UNION (tyvars ty) (tvars t))`

(* Syntax for equations *)

val _ = Parse.add_infix("===",460,Parse.RIGHT)

val equation_def = xDefine "equation"`
  (s === t) = Comb (Comb (Equal(typeof s)) s) t`

(* Signature of a theory: indicates the defined type operators, with arities,
   and defined constants, with types. *)

val _ = Parse.type_abbrev("tyenv",``:string |-> num``)
val _ = Parse.type_abbrev("tmenv",``:string |-> type``)
val _ = Parse.type_abbrev("sig",``:tyenv # tmenv``)
val _ = Parse.overload_on("tysof",``FST:sig->tyenv``)
val _ = Parse.overload_on("tmsof",``SND:sig->tmenv``)

(* Well-formedness of types/terms with respect to a signature *)

val type_ok_def = tDefine "type_ok"`
   (type_ok tyenv (Tyvar _) ⇔ T) ∧
   (type_ok tyenv (Tyapp name args) ⇔
      FLOOKUP tyenv name = SOME (LENGTH args) ∧
      EVERY (type_ok tyenv) args)`
(type_rec_tac "SND")

val term_ok_def = Define`
  (term_ok sig (Var x ty) ⇔ type_ok (tysof sig) ty) ∧
  (term_ok sig (Const name ty) ⇔
     ∃ty0. FLOOKUP (tmsof sig) name = SOME ty0 ∧
           type_ok (tysof sig) ty ∧
           is_instance ty0 ty) ∧
  (term_ok sig (Comb tm1 tm2) ⇔
     term_ok sig tm1 ∧
     term_ok sig tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok sig (Abs x ty tm) ⇔
     type_ok (tysof sig) ty ∧
     term_ok sig tm)`

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

val _ = Parse.type_abbrev("thy",``:sig # term set``)
val _ = Parse.overload_on("sigof",``FST:thy->sig``)
val _ = Parse.overload_on("axsof",``SND:thy->term set``)
val _ = Parse.overload_on("tysof",``tysof o sigof``)
val _ = Parse.overload_on("tmsof",``tmsof o sigof``)

val is_std_sig_def = Define`
  is_std_sig (sig:sig) ⇔
    FLOOKUP (tysof sig) "fun" = SOME 2 ∧
    FLOOKUP (tysof sig) "bool" = SOME 0 ∧
    FLOOKUP (tmsof sig) "=" = SOME (Fun (Tyvar"A") (Fun (Tyvar"A") Bool))`

val theory_ok_def = Define`
  theory_ok (thy:thy) ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (tysof thy) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)`

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-",450,Parse.NONASSOC)

val (proves_rules,proves_ind,proves_cases) = xHol_reln"proves"`
  (* ABS *)
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok (tysof thy) ty ∧
   (thy, h) |- l === r
   ⇒ (thy, h) |- (Abs x ty l) === (Abs x ty r)) ∧

  (* ASSUME *)
  (theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
   ⇒ (thy, [p]) |- p) ∧

  (* BETA *)
  (theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t
   ⇒ (thy, []) |- Comb (Abs x ty t) (Var x ty) === t) ∧

  (* DEDUCT_ANTISYM *)
  ((thy, h1) |- c1 ∧
   (thy, h2) |- c2
   ⇒ (thy, TERM_UNION (FILTER((~) o ACONV c2) h1)
                      (FILTER((~) o ACONV c1) h2))
           |- c1 === c2) ∧

  (* EQ_MP *)
  ((thy, h1) |- p === q ∧
   (thy, h2) |- p' ∧ ACONV p p'
   ⇒ (thy, TERM_UNION h1 h2) |- q) ∧

  (* INST *)
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
   (thy, h) |- c
   ⇒ (thy, MAP (VSUBST ilist) h) |- VSUBST ilist c) ∧

  (* INST_TYPE *)
  ((EVERY (type_ok (tysof thy)) (MAP FST tyin)) ∧
   (thy, h) |- c
   ⇒ (thy, MAP (INST tyin) h) |- INST tyin c) ∧

  (* MK_COMB *)
  ((thy, h1) |- l1 === r1 ∧
   (thy, h2) |- l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, TERM_UNION h1 h2) |- Comb l1 l2 === Comb r1 r2) ∧

  (* REFL *)
  (theory_ok thy ∧ term_ok (sigof thy) t
   ⇒ (thy, []) |- t === t) ∧

  (* TRANS *)
  ((thy, h1) |- l === m1 ∧
   (thy, h2) |- m2 === r ∧
   ACONV m1 m2
   ⇒ (thy, TERM_UNION h1 h2) |- l === r) ∧

  (* axioms *)
  (theory_ok thy ∧ c ∈ (axsof thy)
   ⇒ (thy, []) |- c)`

(* A context is a sequence of updates *)

val _ = Hol_datatype`update
  (* Definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec of (string # term) list => term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn of string => term => string => string
  (* NewType name arity *)
  | NewType of string => num
  (* NewConst name type *)
  | NewConst of string => type
  (* NewAxiom proposition *)
  | NewAxiom of term`

(* Projecting out pieces of the context *)

  (* Types and constants introduced by an update *)
val types_of_upd_def = Define`
  (types_of_upd (ConstSpec _ _) = []) ∧
  (types_of_upd (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd (NewConst _ _) = []) ∧
  (types_of_upd (NewAxiom _) = [])`

val consts_of_upd_def = Define`
  (consts_of_upd (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (STRING_SORT (tvars pred))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd (NewType _ _) = []) ∧
  (consts_of_upd (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd (NewAxiom _) = [])`

val _ = Parse.overload_on("type_list",``λctxt. FLAT (MAP types_of_upd ctxt)``)
val _ = Parse.overload_on("tysof",``λctxt. alist_to_fmap (type_list ctxt)``)
val _ = Parse.overload_on("const_list",``λctxt. FLAT (MAP consts_of_upd ctxt)``)
val _ = Parse.overload_on("tmsof",``λctxt. alist_to_fmap (const_list ctxt)``)

  (* From this we can recover a signature *)
val _ = Parse.overload_on("sigof",``λctxt:update list. (tysof ctxt, tmsof ctxt)``)

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
val axexts_of_upd_def = Define`
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []`

val conexts_of_upd_def = Define`
  (conexts_of_upd (ConstSpec eqs prop) =
    let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
      [VSUBST ilist prop]) ∧
  (conexts_of_upd (TypeDefn name pred abs_name rep_name) =
    let abs_type = Tyapp name (MAP Tyvar (STRING_SORT (tvars pred))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var "a" abs_type in
    let r = Var "r" rep_type in
      [Comb abs (Comb rep a) === a;
       Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  (conexts_of_upd _ = [])`

val _ = Parse.overload_on("axexts",``λctxt. FLAT (MAP axexts_of_upd ctxt)``)
val _ = Parse.overload_on("conexts",``λctxt. FLAT (MAP conexts_of_upd ctxt)``)

val _ = Parse.overload_on("axioms_of_upd",``λupd. axexts_of_upd upd ++ conexts_of_upd upd``)
val _ = Parse.overload_on("axiom_list",``λctxt. FLAT (MAP axioms_of_upd ctxt)``)
val _ = Parse.overload_on("axsof",``λctxt. set (axiom_list ctxt)``)

val _ = export_rewrites["types_of_upd_def","consts_of_upd_def","axexts_of_upd_def"]

  (* Now we can recover the theory associated with a context *)
val _ = Parse.overload_on("thyof",``λctxt:update list. (sigof ctxt, axsof ctxt)``)

(* Principles for extending the context *)

val _ = Parse.add_infix("updates",450,Parse.NONASSOC)

val (updates_rules,updates_ind,updates_cases) = Hol_reln`
  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok (sigof ctxt) prop
   ⇒ (NewAxiom prop) updates ctxt) ∧

  (* new_constant *)
  (name ∉ (FDOM (tmsof ctxt)) ∧
   type_ok (tysof ctxt) ty
   ⇒ (NewConst name ty) updates ctxt) ∧

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
   ⇒ (ConstSpec eqs prop) updates ctxt) ∧

  (* new_type *)
  (name ∉ (FDOM (tysof ctxt))
   ⇒ (NewType name arity) updates ctxt) ∧

  (* new_type_definition *)
  ((thyof ctxt, []) |- Comb pred witness ∧
   CLOSED pred /\ pred has_type (Fun rep_type Bool) ∧
   name ∉ (FDOM (tysof ctxt)) ∧
   abs ∉ (FDOM (tmsof ctxt)) ∧
   rep ∉ (FDOM (tmsof ctxt)) ∧
   abs ≠ rep
   ⇒ (TypeDefn name pred abs rep) updates ctxt)`

val extends_def = Define`
  extends ⇔ RTC (λctxt2 ctxt1. ∃upd. ctxt2 = upd::ctxt1 ∧ upd updates ctxt1)`
val _ = Parse.add_infix("extends",450,Parse.NONASSOC)

(* Context for the theory of Booleans and asserting the mathematical axioms *)

val init_ctxt_def = Define`
  init_ctxt = [NewConst "=" (Fun (Tyvar"A") (Fun (Tyvar"A") Bool))
              ;NewType "bool" 0
              ;NewType "fun" 2]`

  (* Standard signature includes the minimal type operators and constants *)

val _ = Parse.overload_on("ConstDef",``λx t. ConstSpec [(x,t)] (Var x (typeof t) === t)``)
val _ = Parse.overload_on("Truth",``Const "T" Bool``)
val _ = Parse.overload_on("And",``λp1 p2. Comb (Comb (Const "/\\" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Implies",``λp1 p2. Comb (Comb (Const "==>" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Forall",``λx ty p. Comb (Const "!" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("Exists",``λx ty p. Comb (Const "?" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("Or",``λp1 p2. Comb (Comb (Const "\\/" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Falsity",``Const "F" Bool``)
val _ = Parse.overload_on("Not",``λp. Comb (Const "~" (Fun Bool Bool)) p``)
val _ = Parse.overload_on("Select",``λty. Const "@" (Fun (Fun ty Bool) ty)``)
val _ = Parse.overload_on("One_One",``λf. Comb (Const "ONE_ONE" (Fun (typeof f) Bool)) f``)
val _ = Parse.overload_on("Onto",``λf. Comb (Const "ONTO" (Fun (typeof f) Bool)) f``)
val _ = Parse.overload_on("Ind",``Tyapp "ind" []``)

val bool_ctxt_def = Define`
  bool_ctxt = REVERSE (REVERSE init_ctxt ++
    let    A =  Tyvar "A" in
    let    B =  Tyvar "B" in
    let    p =    Var "p" Bool in
    let Absp =    Abs "p" Bool in
    let  FAp = Forall "p" Bool in
    let    q =    Var "q" Bool in
    let Absq =    Abs "q" Bool in
    let  FAq = Forall "q" Bool in
    let    r =    Var "r" Bool in
    let  FAr = Forall "r" Bool in
    let    f =    Var "f" (Fun Bool (Fun Bool Bool)) in
    let Absf =    Abs "f" (Fun Bool (Fun Bool Bool)) in
    let    P =    Var "P" (Fun A Bool) in
    let AbsP =    Abs "P" (Fun A Bool) in
    let    x =    Var "x" A in
    let Absx =    Abs "x" A in
    let  FAx = Forall "x" A in
    let  EXx = Exists "x" A in
    let    g =    Var "f" (Fun A B) in
    let Absg =    Abs "f" (Fun A B) in
    let   x1 =    Var "x1" A in
    let FAx1 = Forall "x1" A in
    let   x2 =    Var "x2" A in
    let FAx2 = Forall "x2" A in
    let    y =    Var "y" B in
    let  FAy = Forall "y" B in
    let    h =    Var "f" (Fun Ind Ind) in
    let  Exh = Exists "f" (Fun Ind Ind) in
    [(* ETA_AX *)
     NewAxiom ((Absx (Comb g x)) === g)
     (* SELECT_AX *)
    ;NewConst "@" (Fun (Fun A Bool) A)
    ;NewAxiom (Comb P (Comb (Select A) P))
     (* connectives and quantifiers *)
    ;ConstDef "T" (Absp p === Absp p)
    ;ConstDef "/\\"
       (Absp (Absq (Absf (Comb (Comb f p) q) ===
                    Absf (Comb (Comb f Truth) Truth))))
    ;ConstDef "==>" (Absp (Absq (And p q === Var "p" Bool)))
    ;ConstDef "!" (AbsP (P === Absx Truth))
    ;ConstDef "?" (AbsP (FAq (Implies (FAx (Implies (Comb P x) q)) q)))
    ;ConstDef "\\/" (Absp (Absq (FAr (Implies (Implies p r) (Implies (Implies q r) r)))))
    ;ConstDef "F" (FAp p)
    ;ConstDef "~" (Absp (Implies p Falsity))
     (* INFINITY_AX *)
    ;ConstDef "ONE_ONE"
       (Absg (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2)))))
    ;ConstDef "ONTO" (Absg (FAy (EXx (y === Comb g x))))
    ;NewType "ind" 0
    ;NewAxiom (Exh (And (One_One h) (Not (Onto h))))
    ])`

val _ = export_theory()
