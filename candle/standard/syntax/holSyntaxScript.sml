(*
  Defines the HOL inference system.
*)
open preamble holSyntaxLibTheory mlstringTheory totoTheory

val _ = new_theory "holSyntax"

(* HOL types *)

Datatype:
  type
  = Tyvar mlstring
  | Tyapp mlstring (type list)
End

Overload Fun = ``λs t. Tyapp (strlit "fun") [s;t]``
Overload Bool = ``Tyapp (strlit "bool") []``

Definition domain_raw:
  domain ty = case ty of Tyapp n (x::xs) => x | _ => ty
End

Theorem domain_def[compute,simp]:
   !t s. domain (Fun s t) = s
Proof
  REPEAT STRIP_TAC \\ EVAL_TAC
QED

Definition codomain_raw:
  codomain ty = case ty of Tyapp n (y::x::xs) => x | _ => ty
End

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

Datatype:
  term = Var mlstring type
       | Const mlstring type
       | Comb term term
       | Abs term term
End

Overload Equal = ``λty. Const (strlit "=") (Fun ty (Fun ty Bool))``

Definition dest_var_def:
  dest_var (Var x ty) = (x,ty)
End
val _ = export_rewrites["dest_var_def"]

(* Assignment of types to terms (where possible) *)

val _ = Parse.add_infix("has_type",450,Parse.NONASSOC)

Inductive has_type:
  ((Var   n ty) has_type ty) ∧
  ((Const n ty) has_type ty) ∧
  (s has_type (Fun dty rty) ∧
   t has_type dty
   ⇒
   (Comb s t) has_type rty) ∧
  (t has_type rty ⇒
   (Abs (Var n dty) t) has_type (Fun dty rty))
End

(* A term is welltyped if it has a type. typeof calculates it. *)

Definition welltyped_def:
  welltyped tm = ∃ty. tm has_type ty
End

Definition typeof_def:
  (typeof (Var n   ty) = ty) ∧
  (typeof (Const n ty) = ty) ∧
  (typeof (Comb s t)   = codomain (typeof s)) ∧
  (typeof (Abs v t) = Fun (typeof v) (typeof t))
End
val _ = export_rewrites["typeof_def"]

Definition is_fun_def:
  (is_fun (Tyapp name tys) = ((name = strlit "fun") /\ (LENGTH tys = 2)))
  /\ (is_fun _ = F)
End
(* check if a term is well-formed *)
Definition wellformed_compute_def:
  (wellformed_compute (Var n ty) = T)
  /\ (wellformed_compute (Const n ty) = T)
  /\ (wellformed_compute (Comb s t) =
    (wellformed_compute s
    /\ wellformed_compute t
    /\ is_fun (typeof s)
    /\ (domain (typeof s) = typeof t))
  )
  /\ (wellformed_compute (Abs (Var x ty) t) = wellformed_compute t)
  /\ (wellformed_compute (Abs _ _) = F)
End

(* Auxiliary relation used to define alpha-equivalence. This relation is
   parameterised by the lists of variables bound above the terms. *)

Inductive RACONV:
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  (typeof v1 = typeof v2 ∧ RACONV ((v1,v2)::env) (t1,t2)
    ⇒ RACONV env (Abs v1 t1,Abs v2 t2))
End

(* Alpha-equivalence. *)

Definition ACONV_def:
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)
End

(* Term ordering, respecting alpha-equivalence *)
(* TODO: use this in the inference system instead of
   ALPHAVARS, ACONV, TERM_UNION, etc., which don't
   lead to canonical hypothesis sets-as-lists *)

Inductive type_lt:
  (mlstring_lt x1 x2 ⇒ type_lt (Tyvar x1) (Tyvar x2)) ∧
  (type_lt (Tyvar x1) (Tyapp x2 args2)) ∧
  ((mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2) ⇒
     type_lt (Tyapp x1 args1) (Tyapp x2 args2))
End

Inductive term_lt:
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
   term_lt (Abs s1 s2) (Abs t1 t2))
End

Definition term_cmp_def:
  term_cmp = TO_of_LinearOrder term_lt
End

Definition type_cmp_def:
  type_cmp = TO_of_LinearOrder type_lt
End

Definition ordav_def:
  (ordav [] x1 x2 ⇔ term_cmp x1 x2) ∧
  (ordav ((t1,t2)::env) x1 x2 ⇔
    if term_cmp x1 t1 = EQUAL then
      if term_cmp x2 t2 = EQUAL then
        EQUAL
      else LESS
    else if term_cmp x2 t2 = EQUAL then
      GREATER
    else ordav env x1 x2)
End

Definition orda_def:
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
      | (_, Comb _ _) => GREATER
End

Definition term_union_def:
  term_union l1 l2 =
    if l1 = l2 then l1 else
    case (l1,l2) of
    | ([],l2) => l2
    | (l1,[]) => l1
    | (h1::t1,h2::t2) =>
      let c = orda [] h1 h2 in
      if c = EQUAL then h1::(term_union t1 t2)
      else if c = LESS then h1::(term_union t1 l2)
      else h2::(term_union (h1::t1) t2)
End

Definition term_remove_def:
  term_remove t l =
  case l of
  | [] => l
  | (s::ss) =>
    let c = orda [] t s in
    if c = GREATER then
      let ss' = term_remove t ss in
      if ss' = ss then l else s::ss'
    else if c = EQUAL then ss else l
End

Definition term_image_def:
  term_image f l =
  case l of
  | [] => l
  | (h::t) =>
    let h' = f h in
    let t' = term_image f t in
    if h' = h ∧ t' = t then l
    else term_union [h'] t'
End

(* Whether a variables (or constant) occurs free in a term. *)

Definition VFREE_IN_def:
  (VFREE_IN v (Var x ty) ⇔ (Var x ty = v)) ∧
  (VFREE_IN v (Const x ty) ⇔ (Const x ty = v)) ∧
  (VFREE_IN v (Comb s t) ⇔ VFREE_IN v s ∨ VFREE_IN v t) ∧
  (VFREE_IN v (Abs w t) ⇔ (w ≠ v) ∧ VFREE_IN v t)
End
val _ = export_rewrites["VFREE_IN_def"]

(* Closed terms: those with no free variables. *)

Definition CLOSED_def:
  CLOSED tm = ∀x ty. ¬(VFREE_IN (Var x ty) tm)
End

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

Theorem LEAST_EXISTS[local]:
  (∃n:num. P n) ⇒ ∃k. P k ∧ ∀m. m < k ⇒ ¬(P m)
Proof
  metis_tac[whileTheory.LEAST_EXISTS]
QED

val VARIANT_PRIMES_def = new_specification
  ("VARIANT_PRIMES_def"
  ,["VARIANT_PRIMES"]
  ,(PRIMED_NAME_EXISTS
   |> HO_MATCH_MP LEAST_EXISTS
   |> Q.GENL[`t`,`x`,`ty`]
   |> SIMP_RULE std_ss [SKOLEM_THM]))

Definition VARIANT_def:
  VARIANT t x ty = implode (APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty)))
End

Theorem VARIANT_THM:
   ∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t
Proof
  metis_tac[VARIANT_def,VARIANT_PRIMES_def]
QED

(* Substitution for type variables in a type. *)

Definition TYPE_SUBST_def:
  (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) ∧
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) ∧
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))
Termination
  type_rec_tac "SND"
End
val _ = export_rewrites["TYPE_SUBST_def"]
Overload is_instance = ``λty0 ty. ∃i. ty = TYPE_SUBST i ty0``

(* Substitution for term variables in a term. *)

Definition VSUBST_def:
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
    else Abs v t')
End

(* A measure on terms, used in proving
   termination of type instantiation. *)

Definition sizeof_def:
  (sizeof (Var x ty) = 1n) ∧
  (sizeof (Const x ty) = 1) ∧
  (sizeof (Comb s t) = 1 + sizeof s + sizeof t) ∧
  (sizeof (Abs v t) = 2 + sizeof t)
End
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

Definition INST_CORE_def:
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
    if IS_RESULT tres then Result(Abs (Var x' ty') (RESULT tres)) else tres)
Termination
  WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST]
End

Definition INST_def:
  INST tyin tm = RESULT(INST_CORE [] tyin tm)
End

(* Type variables in a type. *)

Definition tyvars_def:
  tyvars (Tyvar v) = [v] ∧
  tyvars (Tyapp v tys) = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys
Termination
  (type_rec_tac "I")
End

(* Type variables in a term. *)

Definition tvars_def:
  (tvars (Var n ty) = tyvars ty) ∧
  (tvars (Const n ty) = tyvars ty) ∧
  (tvars (Comb s t) = LIST_UNION (tvars s) (tvars t)) ∧
  (tvars (Abs v t) = LIST_UNION (tvars v) (tvars t))
End

(* Syntax for equations *)

val _ = Parse.add_infix("===",460,Parse.RIGHT)

val equation_def = xDefine "equation"`
  (s === t) = Comb (Comb (Equal(typeof s)) s) t`

(* Signature of a theory: indicates the defined type operators, with arities,
   and defined constants, with types. *)

Type tysig = ``:mlstring |-> num``
Type tmsig = ``:mlstring |-> type``
Type sig = ``:tysig # tmsig``
Overload tysof = ``FST:sig->tysig``
Overload tmsof = ``SND:sig->tmsig``

(* Well-formedness of types/terms with respect to a signature *)

Definition type_ok_def:
   (type_ok tysig (Tyvar _) ⇔ T) ∧
   (type_ok tysig (Tyapp name args) ⇔
      FLOOKUP tysig name = SOME (LENGTH args) ∧
      EVERY (type_ok tysig) args)
Termination
  type_rec_tac "SND"
End

Definition term_ok_def:
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
       term_ok sig tm)
End

(* Well-formed sets of hypotheses, represented as lists,
   are strictly sorted up to alpha-equivalence *)

Definition alpha_lt_def:
  alpha_lt t1 t2 ⇔ orda [] t1 t2 = LESS
End

Definition hypset_ok_def:
  hypset_ok ls ⇔ SORTED alpha_lt ls
End

(* A theory is a signature together with a set of (definitional) axioms. It is
   well-formed if the types of the constants are all ok, the definitional axioms
   are all orthogonal (terms of type bool), and the signature is standard. *)

Type thy = ``:sig # term set``
Overload sigof = ``FST:thy->sig``
Overload axsof = ``SND:thy->term set``
Overload tysof = ``tysof o sigof``
Overload tmsof = ``tmsof o sigof``

  (* Standard signature includes the minimal type operators and constants *)

Definition is_std_sig_def:
  is_std_sig (sig:sig) ⇔
    FLOOKUP (tysof sig) (strlit "fun") = SOME 2 ∧
    FLOOKUP (tysof sig) (strlit "bool") = SOME 0 ∧
    FLOOKUP (tmsof sig) (strlit "=") = SOME (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))
End

(* Note that this theory is not necessarily definitional *)
Definition theory_ok_def:
  theory_ok (thy:thy) ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (tysof thy) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)
End

(* Sequents provable from a theory *)

val _ = Parse.add_infix("|-",450,Parse.NONASSOC)

Inductive proves:
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
   ⇒ (thy, []) |- c)
End

(* A context is a sequence of updates *)

Datatype:
  update
  (* Definition of new constants by specification
     ConstSpec witnesses proposition.
     Boolean flag is set if we're specifying overloads
     of existing constants.
   *)
  = ConstSpec bool ((mlstring # term) list) term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn mlstring term mlstring mlstring
  (* NewType name arity *)
  | NewType mlstring num
  (* NewConst name type *)
  | NewConst mlstring type
  (* NewAxiom proposition *)
  | NewAxiom term
End

(* Projecting out pieces of the context *)

  (* Types and constants introduced by an update *)
Definition types_of_upd_def:
  (types_of_upd (ConstSpec _ _ _) = []) ∧
  (types_of_upd (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd (NewConst _ _) = []) ∧
  (types_of_upd (NewAxiom _) = [])
End

Definition consts_of_upd_def:
  (consts_of_upd (ConstSpec overload eqs prop) = if overload then [] else MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd (NewType _ _) = []) ∧
  (consts_of_upd (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd (NewAxiom _) = [])
End

Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)``
Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)``
Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``

Definition is_builtin_name_def:
  (is_builtin_name m = MEM m (MAP strlit ["bool";"fun"]))
End

val overloadable_in_def = Define `
  overloadable_in name ctxt =
    (~is_builtin_name name /\ ?ty. MEM (NewConst name ty) ctxt)
  `

  (* From this we can recover a signature *)
Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)``

  (* Axioms: we divide them into axiomatic extensions and conservative
     extensions, we will prove that the latter preserve consistency *)
Definition axexts_of_upd_def:
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []
End

Definition conexts_of_upd_def:
  (conexts_of_upd (ConstSpec overload eqs prop) =
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



(* Orthogonality criterion for constant instance and type definitions *)
Definition orth_ty_def:
  orth_ty (ty1 :type) (ty2 :type) = ~(?ty. (is_instance ty1 ty) /\ (is_instance ty2 ty))
End
val _ = Parse.add_infix("#", 401, Parse.NONASSOC);
Overload "#" = ``$orth_ty``

(* orthogonality for constant instances *)
Definition orth_ci_def:
  orth_ci ((Const c ty1) : term) ((Const d ty2) :term) = ((~(c = d)) \/ (ty1 # ty2))
End
Overload "#" = ``$orth_ci``


(* Initial theory context *)

Definition init_ctxt_def:
  init_ctxt = [NewConst (strlit "=") (Fun (Tyvar(strlit "A")) (Fun (Tyvar(strlit "A")) Bool))
              ;NewType (strlit "bool") 0
              ;NewType (strlit "fun") 2]
End

(* all built-in constants and types
 * A type is built-in  iff  its type constructor is.*)
Definition builtin_types_def:
  builtin_types =
    FLAT (MAP (\x. case x of NewType name ty => [(name,ty)] | _ => []) init_ctxt)
End
Definition builtin_const_def:
  builtin_const =
    FILTER (\x. case x of NewConst _ _ => T | _ => F) init_ctxt
End

Definition nonbuiltin_ctxt_def:
  nonbuiltin_ctxt = FILTER (\x. MEM x init_ctxt)
End
Definition is_builtin_type_def:
  (is_builtin_type (Tyvar _) = F)
  /\ (is_builtin_type (Tyapp m ty) =
      ((m = strlit "fun" /\ LENGTH ty = 2) \/
       (m = strlit "bool" /\ LENGTH ty = 0)))
End

val type1_size_append = Q.prove(
  `∀l1 l2. type1_size (l1 ++ l2) = type1_size l1 + type1_size l2`,
  Induct >> simp[fetch "-" "type_size_def"]);

(* allTypes(\sigma) -- the smallest set of non-built-in types that can produce
 * \sigma by combinations of built-in types.
 * This corresponds to   types^\bullet : term -> type set  in the publication *)
Definition allTypes'_defn:
  (allTypes' (Tyapp s tys) =
    if s = strlit "fun" /\ LENGTH tys = 2 then FLAT (MAP allTypes' tys)
    else if s = strlit "bool" /\ tys = [] then []
    else [(Tyapp s tys)]
  )
  /\ (allTypes' (Tyvar n) = [Tyvar n])
Termination
  WF_REL_TAC `measure type_size`
  >> Induct
  >> rw[fetch "-" "type_size_def"]
  >> fs[MEM_SPLIT]
  >> rw[type1_size_append]
  >> rw[fetch "-" "type_size_def"]
End

(* extend allTypes' to terms *)
Definition allTypes_def:
  (allTypes (Var _ ty) = allTypes' ty)
  /\ (allTypes (Const _ ty) = allTypes' ty)
  /\ (allTypes (Comb a b) = ((allTypes a) ++ (allTypes b)))
  /\ (allTypes (Abs a b) = ((allTypes a) ++ (allTypes b)))
End

(* allCInsts(t) -- the smallest set of non-built-in constants that can produce
 * the term t by abstraction, combination and adding variables.
 * A constant instance is built-in  iff  its is among the init_ctxt.
 * This corresponds to  consts^\bullet : term -> CInst set  in the publication *)
Definition allCInsts_def:
  (allCInsts (Var _ _) = [])
  (* no built-in constant is polymorphically defined *)
  /\ (allCInsts (Const c (Tyvar name)) = [(Const c (Tyvar name))])
  /\ (allCInsts (Const c (Tyapp name tys)) =
      (if MEM (NewConst c (Tyapp name tys)) builtin_const then [] else [(Const c (Tyapp name tys))]))
  /\ (allCInsts (Comb a b) = allCInsts a ++ allCInsts b)
  /\ (allCInsts (Abs _ a) = allCInsts a)
End


(* dependency ctxt u v -- true iff there is a direct definitional dependency from
 * u to v, where u and v are non-built-in (type/const)defs.
 * This corresponds to \rightsquigarrow in the publication *)
Inductive dependency:
  (!ctxt c cl ov name ty cdefn prop.
       MEM (ConstSpec ov cl prop) ctxt /\
       MEM (name,cdefn) cl /\
       cdefn has_type ty /\
       MEM c (allCInsts cdefn)
       ==>
       dependency ctxt (INR (Const name ty)) (INR c)) /\
  (!ctxt t cl ov prop.
       MEM (ConstSpec ov cl prop) ctxt /\
       MEM (name,cdefn) cl /\
       cdefn has_type ty /\
       MEM t (allTypes cdefn)
       ==>
       dependency ctxt (INR (Const name ty)) (INL t)) /\
  (!ctxt t1 t2 name pred abs rep.
       MEM (TypeDefn name pred abs rep) ctxt
       /\ MEM t2 (allTypes pred)
       /\ t1 = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred)))))
       ==>
       dependency ctxt (INL t1) (INL t2)) /\
  (!ctxt t c name pred abs rep.
       MEM (TypeDefn name pred abs rep) ctxt
       /\ MEM c (allCInsts pred)
       /\ t = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred)))))
       ==>
       dependency ctxt (INL t) (INR c)) /\
  (!ctxt name t1 t2.
       ~ (is_builtin_name name)
       /\ MEM t1 (allTypes' t2)
       /\ MEM (NewConst name t2) ctxt
       ==>
       dependency ctxt (INR (Const name t2)) (INL t1))
End

(* The computable version of the dependency relation
 * types are INL and constants are INR *)
Definition dependency_compute_def:
  dependency_compute = FLAT o MAP (λx.
    case x of
        (TypeDefn name t _ _ ) =>
          let ty = INL (Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars t)))))) in
          MAP (λv. (ty, INR v)) (allCInsts t)
          ++ MAP (λv. (ty, INL v)) (allTypes t)
        | (ConstSpec ov cl _) =>
          FLAT (MAP (λ(cname,t).
            if ~ wellformed_compute t then [] else
            let constant = INR (Const cname (typeof t))
            in
              MAP (λsubtype. (constant,INL subtype)) (allTypes t)
              ++ MAP (λsubconstant. (constant,INR subconstant)) (allCInsts t)
            ) cl)
      | (NewConst name ty) =>
          if is_builtin_name name then []
          else MAP (λt1. (INR (Const name ty), INL t1)) (allTypes' ty)
      | _ => []
  )
End

(* exclude declared only constants from the dependency relation *)
Inductive dependency1:
  !ctxt x y.
  ~(?name ty.
    ISL y /\ x = INR (Const name ty)
    /\ MEM (NewConst name ty) ctxt
  )
  /\ dependency ctxt x y
  ==> dependency1 ctxt x y
End

(* Type-substitutive closure of a relation.
 * Corresponds to \uparrow in the publication *)
Definition subst_clos_def:
  (subst_clos R (INL t1) (INL t2) =
    (?t1' t2' sigma. t1 = TYPE_SUBST sigma t1' /\ t2 = TYPE_SUBST sigma t2' /\ R (INL t1') (INL t2'))) /\
  (subst_clos R (INL t) (INR c) =
   (?t' c' sigma. t = TYPE_SUBST sigma t' /\ c = INST sigma c' /\ R (INL t') (INR c')))
 /\
  (subst_clos R (INR c) (INL t) =
   (?t' c' sigma. t = TYPE_SUBST sigma t' /\ c = INST sigma c' /\ R (INR c') (INL t')))
 /\
  (subst_clos R (INR c1) (INR c2) =
   (?c1' c2' sigma. c1 = INST sigma c1' /\ c2 = INST sigma c2' /\ R (INR c1') (INR c2')))
End


(* lifting of TYPE_SUBST to term+type *)
Definition LR_TYPE_SUBST_def:
  LR_TYPE_SUBST s x = SUM_MAP (TYPE_SUBST s) (INST s) x
End

Theorem LR_TYPE_SUBST_sides:
  (!x s. ISR x ==> ISR (LR_TYPE_SUBST s x))
  /\ (!x s. ISL x ==> ISL (LR_TYPE_SUBST s x))
Proof
  rw[LR_TYPE_SUBST_def,SUM_MAP]
QED

Definition is_const_or_type_def:
  is_const_or_type (x:type+term) = case x of | INR (Const _ _) => T | INL _ => T | _ => F
End

Theorem is_const_or_type_eq:
  !x. (is_const_or_type x) = ((?m ty. x = INR (Const m ty)) \/ (?ty. x = INL ty))
Proof
  rw[is_const_or_type_def]
  >> rpt (FULL_CASE_TAC)
QED

Theorem LR_TYPE_SUBST_sides2:
  (!x s. is_const_or_type x /\ ISR (LR_TYPE_SUBST s x) ==> ISR x)
  /\ (!x s. is_const_or_type x /\ ISL (LR_TYPE_SUBST s x) ==> ISL x)
Proof
  rw[is_const_or_type_def,LR_TYPE_SUBST_def]
  >> FULL_CASE_TAC
  >> fs[SUM_MAP,INST_def,INST_CORE_def]
QED

Theorem LR_TYPE_SUBST_cases:
  (!s ty m. LR_TYPE_SUBST s (INR (Const m ty)) = INR (Const m (TYPE_SUBST s ty)))
  /\ (!s ty. LR_TYPE_SUBST s (INL ty) = INL (TYPE_SUBST s ty))
Proof
  rw[LR_TYPE_SUBST_def,INST_def,INST_CORE_def]
QED

Inductive subst_clos_rel:
  !R a b rho. (ISL a \/ welltyped (OUTR a)) /\ (ISL b \/ welltyped (OUTR b))
  /\ is_const_or_type a /\ is_const_or_type b
  /\ R a b ==> subst_clos_rel R (LR_TYPE_SUBST rho a) (LR_TYPE_SUBST rho b)
End


(* Free variables *)
Definition FV_def:
  FV p = sum_CASE p tyvars tvars
End

(* The monotonicity criterion of a relation on type+term says that if xRy then
 * all of y's type variables have to occur in x *)
Definition monotone_def:
  monotone R =
    !x y. R x y ==> list_subset (FV y) (FV x)
End

Definition monotone_compute_def:
  monotone_compute = T (*EVERY (\(x,y). list_subset (ARB(*sum_tyvars*) x) (ARB(*sum_tyvars*) y))*)
End

(* overload is_instance to terms: c is an instance of c0  if  (is_instance c0 c) *)
Overload is_instance = ``λc0 c. ∃sigma. c = INST sigma c0``

(* A terminating relation is a relation such that there is no infinite sequence
 *   x_0 R x_1 R x_2 R ...
 * of related elements *)
Definition terminating_def:
 terminating R = ¬?x. !n. ?y. (NRC R (SUC n) x y)
End

(* A context is orthogonal if the LHS of all
 * (type,const) definitions are pairwise orthogonal.
 *)
Definition orth_ctxt_def:
  orth_ctxt ctxt =
  ((!ov1 ov2 cl1 cl2 prop1 prop2 name1 name2 trm1 trm2.
    MEM (ConstSpec ov1 cl1 prop1) ctxt
    /\ MEM (ConstSpec ov2 cl2 prop2) ctxt
    /\ MEM (name1,trm1) cl1
    /\ MEM (name2,trm2) cl2
    /\ (name1,trm1) ≠ (name2,trm2) ==>
       (Const name1 (typeof trm1)) # (Const name2 (typeof trm2))) /\
   (!name1 name2 pred1 pred2 abs1 abs2 rep1 rep2.
    MEM (TypeDefn name1 pred1 abs1 rep1) ctxt
    /\ MEM (TypeDefn name2 pred2 abs2 rep2) ctxt
    /\ (name1,pred1,abs1,rep1) ≠ (name2,pred2,abs2,rep2) ==>
       Tyapp name1 (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred1)))))
       # Tyapp name2 (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred2)))))
   ))
End

(* A well-formed context is orthogonal, and the substitution closure
   of its dependency relation is terminating.
 *)
Definition wf_ctxt_def:
  wf_ctxt ctxt =
  (orth_ctxt ctxt /\ terminating(subst_clos(dependency ctxt)))
End

(* The cyclicity check ensures that the dependency relation terminates.
 *)
Definition cyclic_def:
  cyclic = ARB:(update list -> bool)
End

Definition constspec_ok_def:
  constspec_ok overload eqs prop ctxt =
  if overload then
    ∀name trm. MEM (name,trm) eqs ==> ?ty'. MEM (NewConst name ty') ctxt /\ is_instance ty' (typeof trm) /\ ALOOKUP (const_list ctxt) name = SOME ty' /\ ~is_builtin_name name
       /\ ~cyclic (ConstSpec overload eqs prop::ctxt) /\ orth_ctxt (ConstSpec overload eqs prop::ctxt)
  else
    ALL_DISTINCT (MAP FST eqs) /\ ∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))
End

(* Principles for extending the context *)

val _ = Parse.add_infix("updates",450,Parse.NONASSOC)

val _ = hide "abs";

Inductive updates:
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
   (* the resulting theory has to pass the cyclicity check *)
   constspec_ok overload eqs prop ctxt
   ⇒ (ConstSpec overload eqs prop) updates ctxt) ∧

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
   ⇒ (TypeDefn name pred abs rep) updates ctxt)
End

Definition extends_def:
  extends ⇔ RTC (λctxt2 ctxt1. ∃upd. ctxt2 = upd::ctxt1 ∧ upd updates ctxt1)
End
val _ = Parse.add_infix("extends",450,Parse.NONASSOC)

(* checks if a decreasingly ordered theory, i.e.
 * ctxt = x::l means x updates l,
 * was introduced through the updates *)
Definition definitional_dec_def:
  definitional_dec ctxt = !l1 l2 x. ctxt = l1 ++ [x] ++ l2 ==> x updates l2
End
Definition definitional_def:
  definitional ctxt = ?l. (set l = set ctxt) /\ definitional_dec l
End

val _ = export_theory()
