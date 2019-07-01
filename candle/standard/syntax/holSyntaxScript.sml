(*
  Defines the HOL inference system.
*)
open preamble holSyntaxLibTheory mlstringTheory totoTheory

val _ = new_theory "holSyntax"

(* HOL types *)

val _ = Hol_datatype`type
  = Tyvar of mlstring
  | Tyapp of mlstring => type list`

val _ = Parse.overload_on("Fun",``λs t. Tyapp (strlit "fun") [s;t]``)
val _ = Parse.overload_on("Bool",``Tyapp (strlit "bool") []``)

val domain_raw = Define `
  domain ty = case ty of Tyapp n (x::xs) => x | _ => ty`;

Theorem domain_def[compute,simp]:
   !t s. domain (Fun s t) = s
Proof
  REPEAT STRIP_TAC \\ EVAL_TAC
QED

val codomain_raw = Define `
  codomain ty = case ty of Tyapp n (y::x::xs) => x | _ => ty`;

Theorem codomain_def[compute,simp]:
   !t s. codomain (Fun s t) = t
Proof
  REPEAT STRIP_TAC \\ EVAL_TAC
QED

val _ = save_thm("domain_raw",domain_raw);
val _ = save_thm("codomain_raw",codomain_raw);

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[definition"type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

(* HOL terms *)

val _ = Hol_datatype`term
  = Var of mlstring => type
  | Const of mlstring => type
  | Comb of term => term
  | Abs of term => term`

val _ = Parse.overload_on("Equal",``λty. Const (strlit "=") (Fun ty (Fun ty Bool))``)

val dest_var_def = Define`dest_var (Var x ty) = (x,ty)`
val _ = export_rewrites["dest_var_def"]

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
   (Abs (Var n dty) t) has_type (Fun dty rty))`

(* A term is welltyped if it has a type. typeof calculates it. *)

val welltyped_def = Define`
  welltyped tm = ∃ty. tm has_type ty`

val typeof_def = Define`
  (typeof (Var n   ty) = ty) ∧
  (typeof (Const n ty) = ty) ∧
  (typeof (Comb s t)   = codomain (typeof s)) ∧
  (typeof (Abs v t) = Fun (typeof v) (typeof t))`
val _ = export_rewrites["typeof_def"]

(* Auxiliary relation used to define alpha-equivalence. This relation is
   parameterised by the lists of variables bound above the terms. *)

val (RACONV_rules,RACONV_ind,RACONV_cases) = Hol_reln`
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  (typeof v1 = typeof v2 ∧ RACONV ((v1,v2)::env) (t1,t2)
    ⇒ RACONV env (Abs v1 t1,Abs v2 t2))`

(* Alpha-equivalence. *)

val ACONV_def = Define`
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)`

(* Term ordering, respecting alpha-equivalence *)
(* TODO: use this in the inference system instead of
   ALPHAVARS, ACONV, TERM_UNION, etc., which don't
   lead to canonical hypothesis sets-as-lists *)

val (type_lt_rules,type_lt_ind,type_lt_cases) = Hol_reln`
  (mlstring_lt x1 x2 ⇒ type_lt (Tyvar x1) (Tyvar x2)) ∧
  (type_lt (Tyvar x1) (Tyapp x2 args2)) ∧
  ((mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2) ⇒
     type_lt (Tyapp x1 args1) (Tyapp x2 args2))`

val (term_lt_rules,term_lt_ind,term_lt_cases) = Hol_reln`
  ((mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2) ⇒
    term_lt (Var x1 ty1) (Var x2 ty2)) ∧
  (term_lt (Var x1 ty1) (Const x2 ty2)) ∧
  (term_lt (Var x1 ty1) (Comb t1 t2)) ∧
  (term_lt (Var x1 ty1) (Abs t1 t2)) ∧
  ((mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2) ⇒
    term_lt (Const x1 ty1) (Const x2 ty2)) ∧
  (term_lt (Const x1 ty1) (Comb t1 t2)) ∧
  (term_lt (Const x1 ty1) (Abs t1 t2)) ∧
  ((term_lt LEX term_lt) (s1,s2) (t1,t2) ⇒
   term_lt (Comb s1 s2) (Comb t1 t2)) ∧
  (term_lt (Comb s1 s2) (Abs t1 t2)) ∧
  ((term_lt LEX term_lt) (s1,s2) (t1,t2) ⇒
   term_lt (Abs s1 s2) (Abs t1 t2))`

val term_cmp_def = Define`
  term_cmp = TO_of_LinearOrder term_lt`

val type_cmp_def = Define`
  type_cmp = TO_of_LinearOrder type_lt`

val ordav_def = Define`
  (ordav [] x1 x2 ⇔ term_cmp x1 x2) ∧
  (ordav ((t1,t2)::env) x1 x2 ⇔
    if term_cmp x1 t1 = EQUAL then
      if term_cmp x2 t2 = EQUAL then
        EQUAL
      else LESS
    else if term_cmp x2 t2 = EQUAL then
      GREATER
    else ordav env x1 x2)`

val orda_def = Define`
  orda env t1 t2 =
    if t1 = t2 ∧ env = [] then EQUAL else
      case (t1,t2) of
      | (Var _ _, Var _ _) => ordav env t1 t2
      | (Const _ _, Const _ _) => term_cmp t1 t2
      | (Comb s1 t1, Comb s2 t2) =>
        (let c = orda env s1 s2 in
           if c ≠ EQUAL then c else orda env t1 t2)
      | (Abs s1 t1, Abs s2 t2) =>
        (let c = type_cmp (typeof s1) (typeof s2) in
           if c ≠ EQUAL then c else orda ((s1,s2)::env) t1 t2)
      | (Var _ _, _) => LESS
      | (_, Var _ _) => GREATER
      | (Const _ _, _) => LESS
      | (_, Const _ _) => GREATER
      | (Comb _ _, _) => LESS
      | (_, Comb _ _) => GREATER`

val term_union_def = Define`
  term_union l1 l2 =
    if l1 = l2 then l1 else
    case (l1,l2) of
    | ([],l2) => l2
    | (l1,[]) => l1
    | (h1::t1,h2::t2) =>
      let c = orda [] h1 h2 in
      if c = EQUAL then h1::(term_union t1 t2)
      else if c = LESS then h1::(term_union t1 l2)
      else h2::(term_union (h1::t1) t2)`

val term_remove_def = Define`
  term_remove t l =
  case l of
  | [] => l
  | (s::ss) =>
    let c = orda [] t s in
    if c = GREATER then
      let ss' = term_remove t ss in
      if ss' = ss then l else s::ss'
    else if c = EQUAL then ss else l`

val term_image_def = Define`
  term_image f l =
  case l of
  | [] => l
  | (h::t) =>
    let h' = f h in
    let t' = term_image f t in
    if h' = h ∧ t' = t then l
    else term_union [h'] t'`

(* Whether a variables (or constant) occurs free in a term. *)

val VFREE_IN_def = Define`
  (VFREE_IN v (Var x ty) ⇔ (Var x ty = v)) ∧
  (VFREE_IN v (Const x ty) ⇔ (Const x ty = v)) ∧
  (VFREE_IN v (Comb s t) ⇔ VFREE_IN v s ∨ VFREE_IN v t) ∧
  (VFREE_IN v (Abs w t) ⇔ (w ≠ v) ∧ VFREE_IN v t)`
val _ = export_rewrites["VFREE_IN_def"]

(* Closed terms: those with no free variables. *)

val CLOSED_def = Define`
  CLOSED tm = ∀x ty. ¬(VFREE_IN (Var x ty) tm)`

(* Producing a variant of a variable, guaranteed
   to not be free in a given term. *)

Theorem VFREE_IN_FINITE:
   ∀t. FINITE {x | VFREE_IN x t}
Proof
  Induct >> simp[VFREE_IN_def] >- (
    qmatch_abbrev_tac`FINITE z` >>
    qmatch_assum_abbrev_tac`FINITE x` >>
    qpat_x_assum`FINITE x`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE y` >>
    qsuff_tac`z = x ∪ y`>-metis_tac[FINITE_UNION] >>
    simp[Abbr`x`,Abbr`y`,Abbr`z`,EXTENSION] >> metis_tac[]) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE x` >>
  qmatch_abbrev_tac`FINITE z` >>
  qsuff_tac`∃y. z = x DIFF y`>-metis_tac[FINITE_DIFF] >>
  simp[Abbr`z`,Abbr`x`,EXTENSION] >>
  metis_tac[IN_SING]
QED

Theorem VFREE_IN_FINITE_ALT:
   ∀t ty. FINITE {x | VFREE_IN (Var (implode x) ty) t}
Proof
  rw[] >> match_mp_tac (MP_CANON SUBSET_FINITE) >>
  qexists_tac`IMAGE (λt. case t of Var x y => explode x) {x | VFREE_IN x t}` >>
  simp[VFREE_IN_FINITE,IMAGE_FINITE] >>
  simp[SUBSET_DEF] >> rw[] >>
  HINT_EXISTS_TAC >> simp[explode_implode]
QED

Theorem PRIMED_NAME_EXISTS:
   ∃n. ¬(VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t)
Proof
  qspecl_then[`t`,`ty`]mp_tac VFREE_IN_FINITE_ALT >>
  disch_then(mp_tac o CONJ PRIMED_INFINITE) >>
  disch_then(mp_tac o MATCH_MP INFINITE_DIFF_FINITE) >>
  simp[GSYM MEMBER_NOT_EMPTY] >> rw[] >> metis_tac[]
QED

val LEAST_EXISTS = Q.prove(
  `(∃n:num. P n) ⇒ ∃k. P k ∧ ∀m. m < k ⇒ ¬(P m)`,
  metis_tac[whileTheory.LEAST_EXISTS])

val VARIANT_PRIMES_def = new_specification
  ("VARIANT_PRIMES_def"
  ,["VARIANT_PRIMES"]
  ,(PRIMED_NAME_EXISTS
   |> HO_MATCH_MP LEAST_EXISTS
   |> Q.GENL[`t`,`x`,`ty`]
   |> SIMP_RULE std_ss [SKOLEM_THM]))

val VARIANT_def = Define`
  VARIANT t x ty = implode (APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty)))`

Theorem VARIANT_THM:
   ∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t
Proof
  metis_tac[VARIANT_def,VARIANT_PRIMES_def]
QED

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
  (VSUBST ilist (Abs v t) =
    let ilist' = FILTER (λ(s',s). ¬(s = v)) ilist in
    let t' = VSUBST ilist' t in
    if EXISTS (λ(s',s). VFREE_IN v s' ∧ VFREE_IN s t) ilist'
    then let (x,ty) = dest_var v in
         let z = Var (VARIANT t' (explode x) ty) ty in
         let ilist'' = CONS (z,v) ilist' in
         Abs z (VSUBST ilist'' t)
    else Abs v t')`

(* A measure on terms, used in proving
   termination of type instantiation. *)

val sizeof_def = Define`
  sizeof (Var x ty) = 1n ∧
  sizeof (Const x ty) = 1 ∧
  sizeof (Comb s t) = 1 + sizeof s + sizeof t ∧
  sizeof (Abs v t) = 2 + sizeof t`
val _ = export_rewrites["sizeof_def"]

Theorem SIZEOF_VSUBST:
   ∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t
Proof
  Induct >> simp[VSUBST_def] >> rw[VSUBST_def] >> simp[] >- (
    Q.ISPECL_THEN[`ilist`,`Var m t`,`Var m t`]mp_tac REV_ASSOCD_MEM >>
    rw[] >> res_tac >> pop_assum SUBST1_TAC >> simp[] )
  >- metis_tac[] >>
  simp[pairTheory.UNCURRY] >> rw[] >> simp[] >>
  first_x_assum match_mp_tac >>
  simp[MEM_FILTER] >>
  rw[] >> res_tac >> fs[]
QED

Theorem sizeof_positive:
   ∀t. 0 < sizeof t
Proof
  Induct >> simp[]
QED

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
  (INST_CORE env tyin (Abs v t) =
    let (x,ty) = dest_var v in
    let ty' = TYPE_SUBST tyin ty in
    let v' = Var x ty' in
    let env' = (v,v')::env in
    let tres = INST_CORE env' tyin t in
    if IS_RESULT tres then Result(Abs v' (RESULT tres)) else
    let w = CLASH tres in
    if (w ≠ v') then tres else
    let x' = VARIANT (RESULT(INST_CORE [] tyin t)) (explode x) ty' in
    let t' = VSUBST [Var x' ty,Var x ty] t in
    let ty' = TYPE_SUBST tyin ty in
    let env' = (Var x' ty,Var x' ty')::env in
    let tres = INST_CORE env' tyin t' in
    if IS_RESULT tres then Result(Abs (Var x' ty') (RESULT tres)) else tres)`
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
  (tvars (Abs v t) = LIST_UNION (tvars v) (tvars t))`

(* Syntax for equations *)

val _ = Parse.add_infix("===",460,Parse.RIGHT)

val equation_def = xDefine "equation"`
  (s === t) = Comb (Comb (Equal(typeof s)) s) t`

(* Signature of a theory: indicates the defined type operators, with arities,
   and defined constants, with types. *)

val _ = Parse.type_abbrev("tysig",``:mlstring |-> num``)
val _ = Parse.type_abbrev("tmsig",``:mlstring |-> type``)
val _ = Parse.type_abbrev("sig",``:tysig # tmsig``)
val _ = Parse.overload_on("tysof",``FST:sig->tysig``)
val _ = Parse.overload_on("tmsof",``SND:sig->tmsig``)

(* Well-formedness of types/terms with respect to a signature *)

val type_ok_def = tDefine "type_ok"`
   (type_ok tysig (Tyvar _) ⇔ T) ∧
   (type_ok tysig (Tyapp name args) ⇔
      FLOOKUP tysig name = SOME (LENGTH args) ∧
      EVERY (type_ok tysig) args)`
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
  (term_ok sig (Abs v tm) ⇔
     ∃x ty.
       v = Var x ty ∧
       type_ok (tysof sig) ty ∧
       term_ok sig tm)`

(* Well-formed sets of hypotheses, represented as lists,
   are strictly sorted up to alpha-equivalence *)

val alpha_lt_def = Define`
  alpha_lt t1 t2 ⇔ orda [] t1 t2 = LESS`

val hypset_ok_def = Define`
  hypset_ok ls ⇔ SORTED alpha_lt ls`

(* A theory is a signature together with a set of axioms. It is well-formed if
   the types of the constants are all ok, the axioms are all ok terms of type
   bool, and the signature is standard. *)

val _ = Parse.type_abbrev("thy",``:sig # term set``)
val _ = Parse.overload_on("sigof",``FST:thy->sig``)
val _ = Parse.overload_on("axsof",``SND:thy->term set``)
val _ = Parse.overload_on("tysof",``tysof o sigof``)
val _ = Parse.overload_on("tmsof",``tmsof o sigof``)

  (* Standard signature includes the minimal type operators and constants *)

val is_std_sig_def = Define`
  is_std_sig (sig:sig) ⇔
    FLOOKUP (tysof sig) (strlit "fun") = SOME 2 ∧
    FLOOKUP (tysof sig) (strlit "bool") = SOME 0 ∧
    FLOOKUP (tmsof sig) (strlit "=") = SOME (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))`

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
   ⇒ (thy, h) |- (Abs (Var x ty) l) === (Abs (Var x ty) r)) ∧

  (* ASSUME *)
  (theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
   ⇒ (thy, [p]) |- p) ∧

  (* BETA *)
  (theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t
   ⇒ (thy, []) |- Comb (Abs (Var x ty) t) (Var x ty) === t) ∧

  (* DEDUCT_ANTISYM *)
  ((thy, h1) |- c1 ∧
   (thy, h2) |- c2
   ⇒ (thy, term_union (term_remove c2 h1)
                      (term_remove c1 h2))
           |- c1 === c2) ∧

  (* EQ_MP *)
  ((thy, h1) |- p === q ∧
   (thy, h2) |- p' ∧ ACONV p p'
   ⇒ (thy, term_union h1 h2) |- q) ∧

  (* INST *)
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
   (thy, h) |- c
   ⇒ (thy, term_image (VSUBST ilist) h) |- VSUBST ilist c) ∧

  (* INST_TYPE *)
  ((EVERY (type_ok (tysof thy)) (MAP FST tyin)) ∧
   (thy, h) |- c
   ⇒ (thy, term_image (INST tyin) h) |- INST tyin c) ∧

  (* MK_COMB *)
  ((thy, h1) |- l1 === r1 ∧
   (thy, h2) |- l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, term_union h1 h2) |- Comb l1 l2 === Comb r1 r2) ∧

  (* REFL *)
  (theory_ok thy ∧ term_ok (sigof thy) t
   ⇒ (thy, []) |- t === t) ∧

  (* axioms *)
  (theory_ok thy ∧ c ∈ (axsof thy)
   ⇒ (thy, []) |- c)`

(* A context is a sequence of updates *)

val _ = Hol_datatype`update
  (* Definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec of (mlstring # term) list => term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn of mlstring => term => mlstring => mlstring
  (* NewType name arity *)
  | NewType of mlstring => num
  (* NewConst name type *)
  | NewConst of mlstring => type
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
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
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
    let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var (strlit "a") abs_type in
    let r = Var (strlit "r") rep_type in
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

val _ = hide "abs";

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
   CLOSED pred ∧
   name ∉ (FDOM (tysof ctxt)) ∧
   abs ∉ (FDOM (tmsof ctxt)) ∧
   rep ∉ (FDOM (tmsof ctxt)) ∧
   abs ≠ rep
   ⇒ (TypeDefn name pred abs rep) updates ctxt)`

val extends_def = Define`
  extends ⇔ RTC (λctxt2 ctxt1. ∃upd. ctxt2 = upd::ctxt1 ∧ upd updates ctxt1)`
val _ = Parse.add_infix("extends",450,Parse.NONASSOC)

(* Initial theory context *)

val init_ctxt_def = Define`
  init_ctxt = [NewConst (strlit "=") (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))
              ;NewType (strlit "bool") 0
              ;NewType (strlit "fun") 2]`

val _ = export_theory()
