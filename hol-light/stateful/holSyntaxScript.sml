open HolKernel boolLib boolSimps bossLib lcsymtacs pred_setTheory listTheory alistTheory holSyntaxLibTheory
val _ = temp_tight_equality()
val _ = new_theory "holSyntax"

(* HOL types *)

val _ = Hol_datatype`type
  = Tyvar of string
  | Tyapp of string => type list`

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[definition"type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val _ = Parse.overload_on("Bool",``Tyapp "bool" []``)
val _ = Parse.overload_on("Ind",``Tyapp "ind" []``)
val _ = Parse.overload_on("Fun",``λs t. Tyapp "fun" [s;t]``)

val domain_def = Define`domain (Fun s t) = s`
val codomain_def = Define`codomain (Fun s t) = t`
val domain_def = save_thm("domain_def",SIMP_RULE(srw_ss())[]domain_def)
val codomain_def = save_thm("codomain_def",SIMP_RULE(srw_ss())[]codomain_def)
val _ = export_rewrites["domain_def","codomain_def"]

(* HOL terms *)

val _ = Hol_datatype`term
  = Var of string => type
  | Const of string => type
  | Comb of term => term
  | Abs of string => type => term`

val _ = Parse.overload_on("Equal",``λty. Const "=" (Fun ty (Fun ty Bool))``)
val _ = Parse.overload_on("Select",``λty. Const "@" (Fun (Fun ty Bool) ty)``)

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

(* Alpha-equivalence, as a relation parameterised by the
   lists of variables bound above the terms. *)

val (RACONV_rules,RACONV_ind,RACONV_cases) = Hol_reln`
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  ((ty1 = ty2) ∧ RACONV ((Var x1 ty1,Var x2 ty2)::env) (t1,t2)
    ⇒ RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2))`

(* Alpha-equivalence as a function on closed terms. *)

val ACONV_def = Define`
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)`

(* Alpha-respecting union of two lists of terms.
   May retain duplicates in the second list. *)

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

(* Theory context is a sequence of updates *)

val _ = Hol_datatype`update
  (* Conservative definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec of (string # term) list => term
  (* Conservative definition of a new type
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn of string => term => string => string
  (* NewType name arity *)
  | NewType of string => num
  (* NewConst name type *)
  | NewConst of string => type
  (* NewAxiom proposition *)
  | NewAxiom of term`

(* We can extract a signature from such a context (see sigof below) *)

val _ = Parse.type_abbrev("tyenv",``:string |-> num``)
val _ = Parse.type_abbrev("tmenv",``:string |-> type``)
val _ = Parse.type_abbrev("sig",``:tyenv#tmenv``)

(* Standard signature includes the minimal type operators and constants *)

val is_std_sig_def = Define`
  is_std_sig ((tyenv,tmenv):sig) ⇔
    FLOOKUP tyenv "fun" = SOME 2 ∧
    FLOOKUP tyenv "bool" = SOME 0 ∧
    FLOOKUP tmenv "=" = SOME (Fun (Tyvar"A") (Fun (Tyvar"A") Bool))`

val init_ctxt_def = Define`
  init_ctxt = [NewConst "=" (Fun (Tyvar"A") (Fun (Tyvar"A") Bool))
              ;NewType "bool" 0
              ;NewType "fun" 2]`

(* Projecting out pieces of the context *)

  (* Introduced types and consts *)
val types_of_def_def = Define`
  (types_of_def (ConstSpec _ _) = []) ∧
  (types_of_def (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_def (NewType name arity) = [(name,arity)]) ∧
  (types_of_def (NewConst _ _) = []) ∧
  (types_of_def (NewAxiom _) = [])`

val consts_of_def_def = Define`
  (consts_of_def (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_def (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (STRING_SORT (tvars pred))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_def (NewType _ _) = []) ∧
  (consts_of_def (NewConst name type) = [(name,type)]) ∧
  (consts_of_def (NewAxiom _) = [])`

val _ = Parse.overload_on("type_list",``λctxt. FLAT (MAP types_of_def ctxt)``)
val _ = Parse.overload_on("types",``λctxt. alist_to_fmap (type_list ctxt)``)
val _ = Parse.overload_on("const_list",``λctxt. FLAT (MAP consts_of_def ctxt)``)
val _ = Parse.overload_on("consts",``λctxt. alist_to_fmap (const_list ctxt)``)
val _ = Parse.overload_on("sigof",``λctxt. (types ctxt, consts ctxt)``)

  (* Required terms (no types are required directly) *)
val terms_of_def_def = Define`
  (terms_of_def (ConstSpec eqs prop) = (prop::(MAP SND eqs))) ∧
  (terms_of_def (TypeDefn name pred abs rep) = [pred]) ∧
  (terms_of_def (NewType _ _) = []) ∧
  (terms_of_def (NewConst _ _) = []) ∧
  (terms_of_def (NewAxiom prop) = [prop])`

  (* Axioms *)
val axioms_of_def_def = Define`
  (axioms_of_def (NewAxiom prop) = [prop]) ∧
  (axioms_of_def _ = [])`
val _ = Parse.overload_on("axioms",``λctxt. FLAT (MAP axioms_of_def ctxt)``)

val _ = export_rewrites["types_of_def_def","consts_of_def_def","terms_of_def_def","axioms_of_def_def"]

(* Good types/terms in context *)

val type_ok_def = tDefine "type_ok"`
   (type_ok tyenv (Tyvar _) ⇔ T) ∧
   (type_ok tyenv (Tyapp name args) ⇔
      FLOOKUP tyenv name = SOME (LENGTH args) ∧
      EVERY (type_ok tyenv) args)`
(type_rec_tac "SND")

val term_ok_def = Define`
  (term_ok (tyenv,tmenv) (Var x ty) ⇔ type_ok tyenv ty) ∧
  (term_ok (tyenv,tmenv) (Const name ty) ⇔
     ∃ty0. FLOOKUP tmenv name = SOME ty0 ∧
           type_ok tyenv ty ∧
           is_instance ty0 ty) ∧
  (term_ok sig (Comb tm1 tm2) ⇔
     term_ok sig tm1 ∧
     term_ok sig tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok (tyenv,tmenv) (Abs x ty tm) ⇔
     type_ok tyenv ty ∧
     term_ok (tyenv,tmenv) tm)`

(* Internal consistency of context *)

val linear_context_def = Define`
  (linear_context [] ⇔ T) ∧
  (linear_context (def::ctxt) ⇔
   EVERY (term_ok (sigof ctxt)) (terms_of_def def) ∧
   linear_context ctxt)`

val context_ok_def = Define`
  context_ok ctxt ⇔
    ALL_DISTINCT (MAP FST (type_list ctxt)) ∧
    ALL_DISTINCT (MAP FST (const_list ctxt)) ∧
    EVERY (λp. p has_type Bool) (axioms ctxt) ∧
    linear_context ctxt ∧
    IS_SUFFIX ctxt init_ctxt`

val _ = Parse.add_infix("|-",450,Parse.NONASSOC)

val (proves_rules,proves_ind,proves_cases) = xHol_reln"proves"`
  (* ABS *)
  (¬(EXISTS (VFREE_IN (Var x ty)) asl) ∧ type_ok (types ctxt) ty ∧
   (ctxt, asl) |- l === r
   ⇒ (ctxt, asl) |- (Abs x ty l) === (Abs x ty r)) ∧

  (* ASSUME *)
  (context_ok ctxt ∧ p has_type Bool ∧ term_ok (sigof ctxt) p
   ⇒ (ctxt, [p]) |- p) ∧

  (* BETA *)
  (context_ok ctxt ∧ type_ok (types ctxt) ty ∧ term_ok (sigof ctxt) t
   ⇒ (ctxt, []) |- Comb (Abs x ty t) (Var x ty) === t) ∧

  (* DEDUCT_ANTISYM *)
  ((ctxt, asl1) |- c1 ∧
   (ctxt, asl2) |- c2
   ⇒ (ctxt, TERM_UNION (FILTER((~) o ACONV c2) asl1)
                       (FILTER((~) o ACONV c1) asl2))
            |- c1 === c2) ∧

  (* EQ_MP *)
  ((ctxt, asl1) |- p === q ∧
   (ctxt, asl2) |- p' ∧ ACONV p p'
   ⇒ (ctxt, TERM_UNION asl1 asl2) |- q) ∧

  (* INST *)
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof ctxt) s') ∧
   (ctxt, asl) |- p
   ⇒ (ctxt, MAP (VSUBST ilist) asl) |- VSUBST ilist p) ∧

  (* INST_TYPE *)
  ((EVERY (type_ok (types ctxt)) (MAP FST tyin)) ∧
   (ctxt, asl) |- p
   ⇒ (ctxt, MAP (INST tyin) asl) |- INST tyin p) ∧

  (* MK_COMB *)
  ((ctxt, asl1) |- l1 === r1 ∧
   (ctxt, asl2) |- l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (ctxt, TERM_UNION asl1 asl2) |- Comb l1 l2 === Comb r1 r2) ∧

  (* REFL *)
  (context_ok ctxt ∧ term_ok (sigof ctxt) t
   ⇒ (ctxt, []) |- t === t) ∧

  (* TRANS *)
  ((ctxt, asl1) |- l === m1 ∧
   (ctxt, asl2) |- m2 === r ∧
   ACONV m1 m2
   ⇒ (ctxt, TERM_UNION asl1 asl2) |- l === r) ∧

  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok (sigof ctxt) prop ∧
   ((ctxt, asl) |- p ∨
    ((asl,p) = ([],prop) ∧ context_ok ctxt))
   ⇒ ((NewAxiom prop)::ctxt, asl) |- p) ∧

  (* new_constant *)
  ((ctxt, asl) |- p ∧
   name ∉ (FDOM (consts ctxt)) ∧
   type_ok (types ctxt) ty
   ⇒ ((NewConst name ty)::ctxt, asl) |- p) ∧

  (* new_specification *)
  ((ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
   EVERY
     (λt. CLOSED t ∧
          (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
     (MAP SND eqs) ∧
   (∀x ty. VFREE_IN (Var x ty) prop ⇒
             MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
   (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (consts ctxt))) ∧
   ALL_DISTINCT (MAP FST eqs) ∧
   ((ctxt, asl) |- p ∨
    (let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
       (asl,p) = ([],VSUBST ilist prop)))
   ⇒ ((ConstSpec eqs prop)::ctxt, asl) |- p) ∧

  (* new_type *)
  ((ctxt, asl) |- p ∧
   name ∉ (FDOM (types ctxt))
   ⇒ ((NewType name arity)::ctxt, asl) |- p) ∧

  (* new_type_definition *)
  ((abs_type = Tyapp name (MAP Tyvar (STRING_SORT (tvars pred)))) ∧
   (ctxt, []) |- Comb pred witness ∧
   CLOSED pred /\ pred has_type (Fun rep_type Bool) ∧
   name ∉ (FDOM (types ctxt)) ∧
   abs ∉ (FDOM (consts ctxt)) ∧
   rep ∉ (FDOM (consts ctxt)) ∧
   abs ≠ rep ∧
   ((ctxt, asl) |- p  ∨
    ((asl,p) = ([],
       Comb (Const abs (Fun rep_type abs_type))
              (Comb (Const rep (Fun abs_type rep_type))
                    (Var x abs_type)) === Var x abs_type)) ∨
    ((asl,p) = ([],
       Comb t (Var x rep_type) ===
          Comb (Const rep (Fun abs_type rep_type))
               (Comb (Const abs (Fun rep_type abs_type))
                     (Var x rep_type)) === Var x rep_type)))
   ⇒ ((TypeDefn name pred abs rep)::ctxt, asl) |- p)`

(*

val _ = Parse.overload_on("Exists",``λx ty p. Comb (Const "?" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("Forall",``λx ty p. Comb (Const "!" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("And",``λp1 p2. Comb (Comb (Const "/\\" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Truth",``Const "T" Bool``)
val _ = Parse.overload_on("Falsity",``Const "F" Bool``)
val _ = Parse.overload_on("Implies",``λp1 p2. Comb (Comb (Const "==>" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Not",``λp. Comb (Const "~" (Fun Bool Bool)) p``)
val _ = Parse.overload_on("One_One",``λa b f. Comb (Const "ONE_ONE" (Fun (Fun a b) Bool)) f``)
val _ = Parse.overload_on("Onto",``λa b f. Comb (Const "ONTO" (Fun (Fun a b) Bool)) f``)

val _ = Parse.overload_on("CD1",``λn t. Constdef [(n,t)] (Var n (typeof t) === t)``)

  (!ty1 ty2 defs.
    context_ok defs /\ type_ok defs ty1 /\ type_ok defs ty2
    ==> (defs,[]) |- Abs x ty1 (Comb (Var f (Fun ty1 ty2)) (Var x ty1)) === Var f (Fun ty1 ty2)) /\

  (!asl p w ty defs.
     p has_type (Fun ty Bool) /\ (defs,asl) |- Comb p w
     ==> (defs,asl) |- Comb p (Comb (Select ty) p)) /\

  (!defs.
    context_ok defs ∧
    MEM (CD1 "T" (Abs "p" Bool (Var "p" Bool) === Abs "p" Bool (Var "p" Bool))) defs ∧
    MEM (CD1 "/\\" (Abs "p" Bool
                          (Abs "q" Bool
                            (Abs "f" (Fun Bool (Fun Bool Bool))
                              (Comb (Comb (Var "f" (Fun Bool (Fun Bool Bool))) (Var "p" Bool)) (Var "q" Bool))
                             ===
                             Abs "f" (Fun Bool (Fun Bool Bool))
                               (Comb (Comb (Var "f" (Fun Bool (Fun Bool Bool))) Truth) Truth))))) defs ∧
    MEM (CD1 "==>" (Abs "p" Bool
                          (Abs "q" Bool
                            (And (Var "p" Bool) (Var "q" Bool) === Var "p" Bool)))) defs ∧
    MEM (CD1 "!" (Abs "P" (Fun (Tyvar "A") Bool)
                        (Var "P" (Fun (Tyvar "A") Bool) === Abs "x" (Tyvar "A") Truth))) defs ∧
    MEM (CD1 "?" (Abs "P" (Fun (Tyvar "A") Bool)
                        (Forall "q" Bool
                          (Implies
                            (Forall "x" (Tyvar "A")
                              (Implies (Comb (Var "P" (Fun (Tyvar "A") Bool)) (Var "x" (Tyvar "A")))
                                       (Var "q" Bool)))
                            (Var "q" Bool))))) defs ∧
    MEM (CD1 "F" (Forall "p" Bool (Var "p" Bool))) defs ∧
    MEM (CD1 "~" (Abs "p" Bool (Implies (Var "p" Bool) Falsity))) defs ∧
    MEM (CD1 "ONE_ONE"
          (Abs "f" (Fun (Tyvar "A") (Tyvar "B"))
            (Forall "x1" (Tyvar "A")
              (Forall "x2" (Tyvar "A")
                (Implies
                  (Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B"))) (Var "x1" (Tyvar "A"))
                   ===
                   Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B"))) (Var "x2" (Tyvar "A")))
                  (Var "x1" (Tyvar "A")
                   ===
                   Var "x2" (Tyvar "A"))))))) defs ∧
    MEM (CD1 "ONTO"
          (Abs "f" (Fun (Tyvar "A") (Tyvar "B"))
            (Forall "y" (Tyvar "B")
              (Exists "x" (Tyvar "A")
                (Var "y" (Tyvar "B")
                 ===
                 Comb (Var "f" (Fun (Tyvar "A") (Tyvar "B")))
                      (Var "x" (Tyvar "A"))))))) defs
    ==> (defs,[]) |- Exists "f" (Fun Ind Ind)
                       (And (One_One Ind Ind (Var "f" (Fun Ind Ind)))
                            (Not (Onto Ind Ind (Var "f" (Fun Ind Ind))))))`
*)
val _ = export_theory()
