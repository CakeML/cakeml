(*
  Some lemmas about the syntactic functions.
*)
open preamble totoTheory comparisonTheory ternaryComparisonsTheory mlstringTheory
     holSyntaxLibTheory holSyntaxTheory

val _ = new_theory"holSyntaxExtra"

val _ = Parse.temp_overload_on("is_instance",``λty0 ty. ∃i. ty = TYPE_SUBST i ty0``)

val _ = Parse.add_infix("#", 401, Parse.NONASSOC)
val _ = Parse.temp_overload_on("#", ``$orth_ty``)
val _ = Parse.temp_overload_on("#", ``$orth_ci``)

val cpn_distinct = TypeBase.distinct_of ``:ordering``
val cpn_nchotomy = TypeBase.nchotomy_of ``:ordering``

(* contraposition of an equivalence *)
fun ccontr_equiv(x) =
  let val (a,b) = EQ_IMP_RULE (SPEC_ALL x)
  in GEN_ALL (IMP_ANTISYM_RULE (CONTRAPOS b) (CONTRAPOS a)) end

Theorem type_ind =
  TypeBase.induction_of``:holSyntax$type``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`

Theorem type1_size_append:
   ∀l1 l2. type1_size (l1 ++ l2) = type1_size l1 + type1_size l2
Proof
  Induct >> simp[type_size_def]
QED

Theorem type1_size_mem:
  ∀ty tys. MEM ty tys ==> type_size ty < type1_size tys
Proof
  CONV_TAC SWAP_FORALL_CONV >> Induct
  >> simp[type_size_def]
  >> rw[type_size_def]
  >- simp[]
  >> first_x_assum drule
  >> simp[]
QED

val [MEM_tyvars_type_size,MEM_tyvars_type1_size] = Q.prove(
  `(!ty m. MEM m (tyvars ty) ==> type_size(Tyvar m) <= type_size ty) /\
   (!tyl ty m. MEM m (tyvars ty) /\ MEM ty tyl ==> type_size(Tyvar m) <= type1_size tyl)
  `,
  ho_match_mp_tac (type_induction)
  \\ rw[tyvars_def,type_size_def]
  \\ fs[MEM_FOLDR_LIST_UNION]
  >- (first_x_assum drule \\ rpt(disch_then drule) \\ simp[])
  >- (last_x_assum drule \\ simp[])
  >- (last_x_assum drule \\ simp[]))
  |> CONJUNCTS
  |> map2 (curry save_thm) ["MEM_tyvars_type_size","MEM_tyvars_type1_size"]

(* type_size but disregarding the lengths of strings *)
Definition type_size'_def:
  (type_size' (Tyvar a) = SUC 0)
  ∧ (type_size' (Tyapp a0 a1) = 1 + type1_size' a1)
  ∧ (type1_size' [] = 0)
  ∧ (type1_size' (a0::a1) = 1 + (type_size' a0 + type1_size' a1))
End

Theorem type1_size'_append:
  ∀l1 l2. type1_size' (l1 ++ l2) = type1_size' l1 + type1_size' l2
Proof
  Induct >> simp[type_size'_def]
QED

Theorem type1_size'_mem:
  ∀ty tys. MEM ty tys ==> type_size' ty < type1_size' tys + 1
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> simp[fetch "-" "type_size'_def"]
  >> rw[fetch "-" "type_size'_def"]
  >- simp[]
  >> first_x_assum drule
  >> simp[]
QED

Theorem type1_size'_SUM_MAP:
  ∀l. type1_size' l = LENGTH l + SUM (MAP $type_size' l)
Proof
  Induct >> simp[type_size'_def]
QED

Theorem extends_ind:
   ∀P. (∀upd ctxt. upd updates ctxt ∧ P ctxt ⇒ P (upd::ctxt)) ⇒
    ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ P ctxt1 ⇒ P ctxt2
Proof
  gen_tac >> strip_tac >>
  simp[extends_def] >>
  CONV_TAC SWAP_FORALL_CONV >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> first_x_assum match_mp_tac >>
  rw[]
QED

(* deconstructing variables *)

Theorem ALOOKUP_MAP_dest_var:
   ∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty))
Proof
  Induct >> simp[] >> Cases >> simp[EVERY_MEM,EVERY_MAP] >>
  rw[] >> fs[]
QED

(* type substitution *)

Theorem REV_ASSOCD_drop:
  !l1. x <> b ==> REV_ASSOCD x (l1 ++ (a,b)::l2) y = REV_ASSOCD x (l1 ++ l2) y
Proof
  Induct >- rw[REV_ASSOCD]
  \\ Cases \\rw[REV_ASSOCD]
QED

Theorem REV_ASSOCD_self_append:
  !l. REV_ASSOCD x (MAP (f ## I) l ++ l) y = REV_ASSOCD x (MAP (f ## I) l) y
Proof
  Induct >- rw[REV_ASSOCD]
  \\ Cases \\ rw[REV_ASSOCD,REV_ASSOCD_drop]
QED

Theorem TYPE_SUBST_NIL:
   ∀ty. TYPE_SUBST [] ty = ty
Proof
  ho_match_mp_tac type_ind >>
  rw[REV_ASSOCD,MAP_EQ_ID] >>
  fs[EVERY_MEM]
QED
val _ = export_rewrites["TYPE_SUBST_NIL"]

Theorem TYPE_SUBST_Bool:
  ∀tyin. TYPE_SUBST tyin Bool = Bool
Proof
rw[TYPE_SUBST_def]
QED

Theorem is_instance_refl:
  ∀ty. is_instance ty ty
Proof
  rw[] >> qexists_tac`[]` >> rw[]
QED
val _ = export_rewrites["is_instance_refl"]

Theorem swap_ff:
  ∀f g. (λ(x,y). (y,x)) o (f ## g) = (g ## f) o (λ(x,y). (y,x))
Proof
  rw[FUN_EQ_THM,FORALL_PROD]
QED

Theorem ff_def:
  ∀f g. (f ## g) = λ(x,y). (f x, g y)
Proof
  rw[FUN_EQ_THM,FORALL_PROD,PAIR_MAP_THM]
QED

Theorem TYPE_SUBST_compose:
   ∀tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty
Proof
  ho_match_mp_tac TYPE_SUBST_ind >>
  rw[TYPE_SUBST_def,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
  rw[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
  simp[MAP_MAP_o,swap_ff] >> simp[GSYM MAP_MAP_o] >>
  simp[ff_def,ALOOKUP_MAP] >>
  BasicProvers.CASE_TAC >> simp[TYPE_SUBST_def,REV_ASSOCD_ALOOKUP]
QED

Theorem TYPE_SUBST_tyvars:
   ∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x)
Proof
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  conj_tac >- metis_tac[] >>
  Induct >> simp[] >>
  gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> EQ_TAC >> strip_tac >> fs[] >>
  fs[MEM_LIST_UNION] >> metis_tac[]
QED

Theorem TYPE_SUBST_Tyapp_ident:
  !tys s a. (TYPE_SUBST s (Tyapp a tys) = (Tyapp a tys))
  ==> !ty. MEM ty tys ==> TYPE_SUBST s ty = ty
Proof
  rw[MEM_SPLIT] >> fs[ELIM_UNCURRY,APPEND_LENGTH_EQ]
QED

Theorem TYPE_SUBST_reduce:
  !l1 l2 ty x ts. ~MEM x (tyvars ty)
  ==> TYPE_SUBST (l1 ++ (ts,Tyvar x)::l2) ty = TYPE_SUBST (l1 ++ l2) ty
Proof
  Induct
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def]
  >> Cases_on `x=x'`
  >> fs[]
  >> FULL_CASE_TAC
  >> first_x_assum drule
  >> fs[TYPE_SUBST_tyvars]
QED

Theorem TYPE_SUBST_reduce_CONS:
  !l2 ty x ts. ~MEM x (tyvars ty)
  ==> TYPE_SUBST ((ts,Tyvar x)::l2) ty = TYPE_SUBST (l2) ty
Proof
  rpt strip_tac >> drule TYPE_SUBST_reduce \\ disch_then (qspec_then `[]` mp_tac) \\ simp[]
QED

Theorem TYPE_SUBST_reduce_list:
  !l1 l2 ty . (!a. MEM a (tyvars ty) ==> !ty. ~MEM (ty,Tyvar a) l1)
  ==> TYPE_SUBST (l1 ++ l2) ty = TYPE_SUBST l2 ty
Proof
  Induct
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def]
  >> FULL_CASE_TAC
  >- (first_x_assum drule >> disch_then (qspec_then `FST h` mp_tac) >> rw[] >> Cases_on `h` >> fs[])
  >> first_x_assum (qspecl_then [`l2`,`ty`] mp_tac)
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def]
QED

(* TODO remove TYPE_SUBST_reduce_list in favour of this more elegant version *)
Theorem TYPE_SUBST_reduce_list2:
  !l1 l2 ty . EVERY (λa. ~MEM (Tyvar a) (MAP SND l1)) (tyvars ty)
  ==> TYPE_SUBST (l1 ++ l2) ty = TYPE_SUBST l2 ty
Proof
  Induct
  >> rw[TYPE_SUBST_tyvars,REV_ASSOCD_def]
  >> FULL_CASE_TAC
  >- (
    fs[EVERY_MEM,REV_ASSOCD_def]
    >> first_x_assum drule
    >> fs[]
  )
  >> first_x_assum (qspecl_then [`l2`,`ty`] mp_tac)
  >> fs[EVERY_MEM,TYPE_SUBST_tyvars,REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_eating:
  !s ty a. TYPE_SUBST s ty = TYPE_SUBST s (Tyvar a)
  ==> TYPE_SUBST s o TYPE_SUBST [(ty,Tyvar a)] = TYPE_SUBST s
Proof
  rw[FUN_EQ_THM,TYPE_SUBST_compose,TYPE_SUBST_tyvars]
  >> Cases_on `MEM (Tyvar x') (MAP SND s)`
  >- (
    pop_assum (mp_tac o CONV_RULE(PURE_ONCE_REWRITE_CONV [MEM_SPLIT_APPEND_first]))
    >> rw[]
    >> Cases_on `a=x'`
    >> rw[REV_ASSOCD_def]
  )
  >> Cases_on `a=x'`
  >> rw[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_MEM:
  !s a b. EVERY (λ(y,x). (?a. Tyvar a = x /\ x <> y)) s
  /\ ALL_DISTINCT (MAP SND s)
  /\ MEM (b,a) s ==> TYPE_SUBST s a = b
Proof
  rw[MEM_SPLIT]
  >> fs[MAP_APPEND,ALL_DISTINCT_APPEND]
  >> `!ty. ~MEM (ty,a) l1` by (
    rveq
    >> fs[MEM_MAP]
    >> rw[]
    >> qpat_x_assum `!x. _ \/ _` (qspec_then `(ty,Tyvar a')` mp_tac)
    >> rw[]
  )
  >> mp_tac (Q.SPECL [`l1`,`[(b,a)]++l2`,`a`] TYPE_SUBST_reduce_list)
  >> rveq
  >> rw[tyvars_def,REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_NOT_MEM:
  !s a. EVERY (λ(y,x). (?a. Tyvar a = x /\ x <> y)) s
  /\ ALL_DISTINCT (MAP SND s)
  /\ ~(?b. MEM (b,Tyvar a) s) ==> TYPE_SUBST s (Tyvar a) = (Tyvar a)
Proof
  rw[]
  >> assume_tac (Q.SPECL [`s`,`[]`,`Tyvar a`] TYPE_SUBST_reduce_list)
  >> fs[tyvars_def]
QED

Theorem TYPE_SUBST_duplicates:
  !s a t t'. TYPE_SUBST ((t,Tyvar a)::(t',Tyvar a)::s) = TYPE_SUBST ((t,Tyvar a)::s)
Proof
  rw[FUN_EQ_THM,TYPE_SUBST_tyvars]
  >> Cases_on `x'=a`
  >> fs[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_drop_prefix:
  !l pfx a. ~MEM (Tyvar a) (MAP SND pfx) ==> TYPE_SUBST (pfx++l) (Tyvar a) = TYPE_SUBST l (Tyvar a)
Proof
  Induct_on `pfx`
  >> rw[REV_ASSOCD_drop]
  >> Cases_on `h`
  >> fs[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_drop_all:
  !pfx a. ~MEM (Tyvar a) (MAP SND pfx) ==> TYPE_SUBST pfx (Tyvar a) = (Tyvar a)
Proof
  rw[]
  >> dxrule TYPE_SUBST_drop_prefix
  >> disch_then (qspec_then `[]` assume_tac)
  >> fs[]
QED

Theorem TYPE_SUBST_drop_prefix_MAP:
  !l pfx a f. ~MEM (Tyvar a) (MAP SND pfx) ==> TYPE_SUBST (MAP (f ## I )pfx++l) (Tyvar a) = TYPE_SUBST l (Tyvar a)
Proof
  Induct_on `pfx`
  >> rw[REV_ASSOCD_drop]
  >> Cases_on `h`
  >> fs[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_MEM':
  !s a b. ALL_DISTINCT (MAP SND s) /\ MEM (b,Tyvar a) s ==> TYPE_SUBST s (Tyvar a) = b
Proof
  rw[MEM_SPLIT]
  >> fs[MAP_APPEND,ALL_DISTINCT_APPEND]
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> pop_assum (qspec_then `[(b,Tyvar a)]++l2` assume_tac)
  >> fs[REV_ASSOCD_def]
QED

Theorem ZIP_ident:
  !a b c d. LENGTH a = LENGTH c /\ LENGTH b = LENGTH d /\
  LENGTH a = LENGTH b ==> ((ZIP (a,b) = ZIP (c,d)) <=> (a = c /\ b = d))
Proof
  Induct >- fs[]
  >> strip_tac
  >> rpt Cases >> fs[]
  >> first_x_assum (qspecl_then [`t`,`t'`,`t''`] assume_tac)
  >> rw[] >> fs[AC CONJ_ASSOC CONJ_COMM]
QED

Theorem MEM_SPLIT_APPEND_SND_first:
  !s x. MEM x (MAP SND s) ==> ?pfx sfx q. s = pfx ++ [(q,x)] ++ sfx /\ ~MEM x (MAP SND pfx)
Proof
  rpt strip_tac
  >> pop_assum (assume_tac o PURE_ONCE_REWRITE_RULE [MEM_SPLIT_APPEND_first])
  >> fs[]
  >> `LENGTH (MAP SND s) = LENGTH pfx + 1 + LENGTH sfx` by (ASM_REWRITE_TAC[LENGTH_APPEND] >> fs[])
  >> ONCE_REWRITE_TAC[GSYM ZIP_MAP_FST_SND_EQ]
  >> fs[MAP_APPEND]
  >> qexists_tac `TAKE (LENGTH pfx) s`
  >> qexists_tac `DROP (SUC (LENGTH pfx)) s`
  >> qexists_tac `FST (EL (LENGTH pfx) s)`
  >> qmatch_goalsub_abbrev_tac `ZIP (a,b) = ZIP(c,d)`
  >> (Q.ISPECL_THEN [`a`,`b`,`c`,`d`] assume_tac) ZIP_ident
  >> unabbrev_all_tac
  >> fs[LENGTH_MAP]
  >> rpt strip_tac
  >- (
    NTAC 2 (pop_assum kall_tac)
    >> rpt (pop_assum mp_tac)
    >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`sfx`,`x`,`pfx`,`s`]
    >> Induct >- fs[]
    >> rw[]
    >> Cases_on `pfx`
    >> fs[]
  )
  >- (
    NTAC 2 (pop_assum kall_tac)
    >> rpt (pop_assum mp_tac)
    >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`sfx`,`x`,`pfx`,`s`]
    >> Induct >- fs[]
    >> rw[]
    >> Cases_on `pfx`
    >> fs[]
  )
  >> pop_assum mp_tac
  >> rw[ZIP_MAP_FST_SND_EQ,MAP_TAKE]
  >> ONCE_REWRITE_TAC[GSYM APPEND_ASSOC]
  >> rw[TAKE_LENGTH_APPEND]
QED

Theorem TYPE_SUBST_MEM_MAP_SND:
  !s a. MEM (Tyvar a) (MAP SND s)
  ==> ?b. TYPE_SUBST s (Tyvar a) = b /\ MEM (b,Tyvar a) s
Proof
  rw[]
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_x_assum (qspec_then `[(q,Tyvar a)]++sfx` assume_tac)
  >> fs[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_drop_suffix:
  !s a. MEM (Tyvar a) (MAP SND s)
  ==> !s'. TYPE_SUBST (s++s') (Tyvar a) = TYPE_SUBST s (Tyvar a)
Proof
  rpt strip_tac
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_assum (qspec_then `[(q,Tyvar a)]++sfx++s'` assume_tac)
  >> first_x_assum (qspec_then `[(q,Tyvar a)]++sfx` assume_tac)
  >> fs[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_EL:
  !l i n. n < LENGTH l ==> TYPE_SUBST i (EL n l) = EL n (MAP (λa. TYPE_SUBST i a) l)
Proof
  Induct
  >> fs[]
  >> rpt strip_tac
  >> Cases_on `n = 0`
  >> fs[NOT_ZERO_LT_ZERO]
  >> `?m. n = SUC m` by (qexists_tac `PRE n` >> fs[])
  >> fs[EL]
QED

(* Welltyped terms *)

Theorem WELLTYPED_LEMMA:
   ∀tm ty. tm has_type ty ⇒ (typeof tm = ty)
Proof
  ho_match_mp_tac has_type_ind >>
  simp[typeof_def,has_type_rules,codomain_def]
QED

Theorem WELLTYPED:
   ∀tm. welltyped tm ⇔ tm has_type (typeof tm)
Proof
  simp[welltyped_def] >> metis_tac[WELLTYPED_LEMMA]
QED

Theorem WELLTYPED_CLAUSES:
  (!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!v t. welltyped (Abs v t) = ∃n ty. v = Var n ty ∧ welltyped t)
Proof
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped_def] THEN
  rw[Once has_type_cases] >>
  metis_tac[WELLTYPED,WELLTYPED_LEMMA]
QED
val _ = export_rewrites["WELLTYPED_CLAUSES"]

(* wellformed_compute acutally also checks the syntax (through the has_type relation) *)
Theorem WELLFORMED_COMPUTE_EQUIV:
  !t. welltyped t = wellformed_compute t
Proof
  Induct
  >> rw[welltyped_def,wellformed_compute_def]
  >> fs[welltyped_def]
  >> Cases_on `typeof t`
  >> rw[is_fun_def,domain_raw]
  >- (
    PURE_FULL_CASE_TAC
    >> rw[GSYM PULL_EXISTS]
    >> rw[quantHeuristicsTheory.LIST_LENGTH_1]
    >> fs[AC CONJ_ASSOC CONJ_COMM]
  )
  >> Cases_on `t`
  >> rw[wellformed_compute_def]
QED

(* Alpha-equivalence *)

Theorem RACONV:
  (RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs v2 t2) <=> F) /\
   (RACONV env (Const x1 ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Const x2 ty2) <=> (x1 = x2) /\ (ty1 = ty2)) /\
   (RACONV env (Const x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1,Abs v2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs v2 t2) <=> F) /\
   (RACONV env (Abs v1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs v1 t1,Const x2 ty2) <=> F) /\
   (RACONV env (Abs v1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs v1 t1,Abs v2 t2) <=>
          typeof v1 = typeof v2 /\
          RACONV (CONS (v1,v2) env) (t1,t2))
Proof
  REPEAT CONJ_TAC THEN simp[Once RACONV_cases] >> metis_tac[]
QED

Theorem RACONV_REFL:
   ∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t)
Proof
  Induct >> simp[RACONV,ALPHAVARS_REFL]
QED

Theorem ACONV_REFL:
   ∀t. ACONV t t
Proof
  simp[ACONV_def,RACONV_REFL]
QED
val _ = export_rewrites["ACONV_REFL"]

Theorem RACONV_TRANS:
   ∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t)
Proof
  ho_match_mp_tac RACONV_ind >> simp[RACONV] >>
  conj_tac >- (
    Induct >- simp[ALPHAVARS_def] >>
    Cases >> simp[ALPHAVARS_def] >>
    rw[] >> Cases_on`vs`>>fs[] >>
    Cases_on`t`>>fs[RACONV]>>
    fs[ALPHAVARS_def] >> rw[] >>
    metis_tac[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  conj_tac >- ( rw[] >> Cases_on`t`>>fs[RACONV] ) >>
  rw[] >>
  Cases_on`t`>>fs[RACONV]>>rw[]>>
  metis_tac[LENGTH,ZIP]
QED

Theorem ACONV_TRANS:
   ∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3
Proof
  rw[ACONV_def] >> imp_res_tac RACONV_TRANS >> fs[LENGTH_NIL]
QED

Theorem RACONV_SYM:
   ∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)
Proof
  ho_match_mp_tac RACONV_ind >> simp[] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def,RACONV] >>
    Cases >> simp[] >>
    rw[] >> res_tac >> fs[RACONV]) >>
  simp[RACONV]
QED

Theorem ACONV_SYM:
   ∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1
Proof
  rw[ACONV_def] >> imp_res_tac RACONV_SYM >> fs[]
QED

Theorem ALPHAVARS_TYPE:
   ∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t
Proof
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> rw[]
QED

Theorem RACONV_TYPE:
   ∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p)
Proof
  ho_match_mp_tac RACONV_ind >>
  simp[FORALL_PROD,typeof_def,WELLTYPED_CLAUSES] >>
  rw[] >> imp_res_tac ALPHAVARS_TYPE >>
  fs[typeof_def,WELLTYPED_CLAUSES]
QED

Theorem ACONV_TYPE:
   ∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t)
Proof
  rw[ACONV_def] >> imp_res_tac RACONV_TYPE >> fs[]
QED

(* subtypes *)

val (subtype1_rules,subtype1_ind,subtype1_cases) = Hol_reln`
  MEM a args ⇒ subtype1 a (Tyapp name args)`
val _ = Parse.add_infix("subtype",401,Parse.NONASSOC)
val _ = Parse.overload_on("subtype",``RTC subtype1``)
val subtype_Tyvar = save_thm("subtype_Tyvar",
  ``ty subtype (Tyvar x)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases])
val _ = export_rewrites["subtype_Tyvar"]
val subtype_Tyapp = save_thm("subtype_Tyapp",
  ``ty subtype (Tyapp name args)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases])

Theorem subtype_trans:
  !x y z. x subtype y /\ y subtype z ==> x subtype z
Proof
  assume_tac (Q.ISPEC `$subtype` transitive_def) >> fs[]
QED

Theorem subtype_TYPE_SUBST:
  !a b s. (a subtype b) ==> ((TYPE_SUBST s a) subtype (TYPE_SUBST s b))
Proof
  simp[GSYM PULL_FORALL]
  >> ho_match_mp_tac RTC_INDUCT
  >> rw[]
  >> `subtype1 (TYPE_SUBST s a) (TYPE_SUBST s a')` by (
    fs[subtype1_cases,MEM_MAP,ELIM_UNCURRY]
    >> qexists_tac `a`
    >> fs[]
  )
  >> match_mp_tac (CONJUNCT2 (SPEC_ALL RTC_RULES))
  >> asm_exists_tac
  >> simp[]
QED

Theorem subtype_tyvars:
  !a ty. MEM a (tyvars ty) = ((Tyvar a) subtype ty)
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> ho_match_mp_tac type_ind
  >> strip_tac
  >- rw[tyvars_def]
  >> rw[MEM_FOLDR_LIST_UNION,EQ_IMP_THM,tyvars_def,EVERY_MEM,ELIM_UNCURRY]
  >- (
    first_x_assum drule
    >> disch_then (qspec_then `a` mp_tac)
    >> rw[subtype_Tyapp]
    >> asm_exists_tac
    >> simp[]
  )
  >> fs[subtype_Tyapp]
  >> first_x_assum drule
  >> disch_then (qspec_then `a` mp_tac)
  >> rw[]
  >> asm_exists_tac
  >> simp[]
QED

Theorem subtype_type_ok:
   ∀tysig ty1 ty2. type_ok tysig ty2 ∧ ty1 subtype ty2 ⇒ type_ok tysig ty1
Proof
  gen_tac >>
  (relationTheory.RTC_lifts_invariants
    |> Q.GEN`R` |> Q.ISPEC`inv subtype1`
    |> SIMP_RULE std_ss [relationTheory.inv_MOVES_OUT,relationTheory.inv_DEF]
    |> Q.GEN`P` |> Q.ISPEC`type_ok tysig`
    |> match_mp_tac) >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  ONCE_REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  CONV_TAC SWAP_FORALL_CONV >> gen_tac >>
  ho_match_mp_tac subtype1_ind >>
  simp[type_ok_def,EVERY_MEM]
QED

(* subterms *)

val (subterm1_rules,subterm1_ind,subterm1_cases) = Hol_reln`
  subterm1 t1 (Comb t1 t2) ∧
  subterm1 t2 (Comb t1 t2) ∧
  subterm1 tm (Abs v tm) ∧
  subterm1 v (Abs v tm)`

val _ = Parse.add_infix("subterm",401,Parse.NONASSOC)
val _ = Parse.overload_on("subterm",``RTC subterm1``)
val subterm_Var = save_thm("subterm_Var",
  ``tm subterm (Var x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])
val subterm_Const = save_thm("subterm_Const",
  ``tm subterm (Const x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])
val _ = export_rewrites["subterm_Var","subterm_Const"]
val subterm_Comb = save_thm("subterm_Comb",
  ``tm subterm (Comb t1 t2)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])
val subterm_Abs = save_thm("subterm_Abs",
  ``tm subterm (Abs v t)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases])

val subterm_welltyped = save_thm("subterm_welltyped",
  let val th =
    Q.prove(`∀tm ty. tm has_type ty ⇒ ∀t. t subterm tm ⇒ welltyped t`,
      ho_match_mp_tac has_type_strongind >>
      simp[subterm_Comb,subterm_Abs] >> rw[] >>
      rw[] >> imp_res_tac WELLTYPED_LEMMA >> simp[])
  in METIS_PROVE[th,welltyped_def]
    ``∀t tm. welltyped tm ∧ t subterm tm ⇒ welltyped t``
  end)

(* term ordering *)

val type_lt_thm = Q.prove(
  `(type_lt (Tyvar x1) (Tyvar x2) ⇔ mlstring_lt x1 x2) ∧
    (type_lt (Tyvar _) (Tyapp _ _) ⇔ T) ∧
    (type_lt (Tyapp _ _) (Tyvar _) ⇔ F) ∧
    (type_lt (Tyapp x1 args1) (Tyapp x2 args2) ⇔
       (mlstring_lt LEX LLEX type_lt)
         (x1,args1) (x2,args2))`,
  rw[] >> rw[Once type_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
  |> curry save_thm "type_lt_thm"

val term_lt_thm = Q.prove(`
  (term_lt (Var x1 ty1) (Var x2 ty2) ⇔
     (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) ∧
  (term_lt (Var _ _) (Const _ _) ⇔ T) ∧
  (term_lt (Var _ _) (Comb _ _) ⇔ T) ∧
  (term_lt (Var _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Const _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Const x1 ty1) (Const x2 ty2) ⇔
     (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) ∧
  (term_lt (Const _ _) (Comb _ _) ⇔ T) ∧
  (term_lt (Const _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Comb _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Comb _ _) (Const _ _) ⇔ F) ∧
  (term_lt (Comb s1 s2) (Comb t1 t2) ⇔
     (term_lt LEX term_lt) (s1,s2) (t1,t2)) ∧
  (term_lt (Comb _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Abs _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Abs _ _) (Const _ _) ⇔ F) ∧
  (term_lt (Abs _ _) (Comb _ _) ⇔ F) ∧
  (term_lt (Abs s1 s2) (Abs t1 t2) ⇔
    (term_lt LEX term_lt) (s1,s2) (t1,t2))`,
  rw[] >> rw[Once term_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
  |> curry save_thm "term_lt_thm"

Theorem type_cmp_refl[simp]:
  type_cmp t t = EQUAL
Proof
  rw[type_cmp_def,TO_of_LinearOrder]
QED

Theorem term_cmp_refl[simp]:
  term_cmp t t = EQUAL
Proof
  rw[term_cmp_def,TO_of_LinearOrder]
QED

Theorem irreflexive_type_lt[local]:
  irreflexive type_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  simp[StrongLinearOrder,StrongOrder,irreflexive_def] >>
  strip_tac >> ho_match_mp_tac type_ind >>
  simp[type_lt_thm,LEX_DEF] >>
  Induct >> simp[]
QED

Theorem trichotomous_type_lt[local]:
  trichotomous type_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  simp[StrongLinearOrder,trichotomous] >> strip_tac >>
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    gen_tac >> Cases >> simp[type_lt_thm] ) >>
  gen_tac >> strip_tac >> gen_tac >> Cases >> simp[type_lt_thm,LEX_DEF_THM] >>
  first_x_assum(qspecl_then[`m`,`m'`]strip_assume_tac) >> simp[] >>
  fs[StrongOrder,irreflexive_def] >> rw[] >>
  pop_assum mp_tac >>
  qspec_tac(`l'`,`l2`) >>
  Induct_on`l` >>
  Cases_on`l2`>>simp[]>>
  rw[] >> fs[] >>
  metis_tac[]
QED

Theorem transitive_type_lt[local]:
  ∀x y. type_lt x y ⇒ ∀z. type_lt y z ⇒ type_lt x z
Proof
  ho_match_mp_tac type_lt_strongind >>
  rpt conj_tac >> rpt gen_tac >> simp[PULL_FORALL] >>
  Cases_on`z` >> simp[type_lt_thm,LEX_DEF_THM] >-
    metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder,StrongOrder,transitive_def] >>
  strip_tac >- metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder,StrongOrder,transitive_def] >>
  strip_tac >- metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder,StrongOrder,transitive_def] >>
  rw[] >> disj2_tac >>
  fs[LLEX_EL_THM] >>
  qmatch_assum_rename_tac`n2 ≤ LENGTH args2` >>
  Cases_on`n < LENGTH args1`>>fsrw_tac[ARITH_ss][] >- (
    `EL n args1 ≠ EL n args2` by metis_tac[irreflexive_type_lt,irreflexive_def] >>
    Cases_on`n < n2` >> fsrw_tac[ARITH_ss][] >- (
      qexists_tac`n` >> simp[] >>
      conj_tac >- (
        simp[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
        rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
        first_x_assum(qspec_then`x`mp_tac) >>
        simp[rich_listTheory.EL_TAKE] ) >>
      `EL n args2 = EL n l` by (
        rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
        fs[rich_listTheory.EL_TAKE] >>
        first_x_assum(qspec_then`n`mp_tac) >>
        simp[rich_listTheory.EL_TAKE] ) >>
      metis_tac[trichotomous_type_lt,trichotomous] ) >>
    Cases_on`n = n2` >> fs[] >- (
      rw[] >> rfs[] >>
      qexists_tac`n`>>simp[] ) >>
    qexists_tac`n2`>>simp[] >>
    conj_tac >- (
      simp[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
      last_x_assum(qspec_then`x`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    `EL n2 args1 = EL n2 args2` by (
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      fs[rich_listTheory.EL_TAKE] >>
      last_x_assum(qspec_then`n2`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    Cases_on`n2 < LENGTH args2`>>fs[]>>
    DECIDE_TAC ) >>
  `n = LENGTH args1` by DECIDE_TAC >>
  BasicProvers.VAR_EQ_TAC >> fs[] >>
  Cases_on`n2 ≤ LENGTH args1` >> fs[] >- (
    qexists_tac`n2` >> simp[] >>
    conj_tac >- (
      fs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
      last_x_assum(qspec_then`x`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    rw[] >>
    `n2 < LENGTH args2` by simp[] >> fs[] >>
    `EL n2 args1 = EL n2 args2` by (
      fs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
      rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >> rw[] >>
      last_x_assum(qspec_then`n2`mp_tac) >>
      simp[rich_listTheory.EL_TAKE] ) >>
    fs[] ) >>
  qexists_tac`LENGTH args1` >> simp[] >>
  fs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
  rfs[LIST_EQ_REWRITE,rich_listTheory.EL_TAKE] >>
  `LENGTH args1 ≤ LENGTH l` by DECIDE_TAC >> simp[] >>
  simp[rich_listTheory.EL_TAKE]
QED

Theorem StrongLinearOrder_type_lt:
   StrongLinearOrder type_lt
Proof
  simp[StrongLinearOrder,StrongOrder,irreflexive_type_lt,trichotomous_type_lt] >>
  metis_tac[transitive_type_lt,transitive_def]
QED

Theorem TotOrd_type_cmp:
  TotOrd type_cmp
Proof
  rw[type_cmp_def] >>
  match_mp_tac TotOrd_TO_of_Strong >>
  ACCEPT_TAC StrongLinearOrder_type_lt
QED

Theorem irreflexive_term_lt[local]:
  irreflexive term_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  mp_tac StrongLinearOrder_type_lt >>
  simp[StrongLinearOrder,StrongOrder,irreflexive_def] >>
  ntac 2 strip_tac >> ho_match_mp_tac term_induction >>
  simp[term_lt_thm,LEX_DEF]
QED

Theorem trichotomous_term_lt[local]:
  trichotomous term_lt
Proof
  mp_tac StrongLinearOrder_mlstring_lt >>
  mp_tac StrongLinearOrder_type_lt >>
  simp[StrongLinearOrder,trichotomous] >> ntac 2 strip_tac >>
  ho_match_mp_tac term_induction >>
  rpt conj_tac >> rpt gen_tac >> TRY(strip_tac) >>
  Cases_on`b` >> simp[term_lt_thm,LEX_DEF_THM] >>
  metis_tac[]
QED

Theorem transitive_term_lt[local]:
  ∀x y. term_lt x y ⇒ ∀z. term_lt y z ⇒ term_lt x z
Proof
  ho_match_mp_tac term_lt_strongind >>
  rpt conj_tac >> rpt gen_tac >> simp[PULL_FORALL] >>
  Cases_on`z` >> simp[term_lt_thm,LEX_DEF_THM] >>
  metis_tac[StrongLinearOrder_mlstring_lt,StrongLinearOrder_type_lt,StrongLinearOrder,
            StrongOrder,transitive_def]
QED

Theorem StrongLinearOrder_term_lt:
  StrongLinearOrder term_lt
Proof
  simp[StrongLinearOrder,StrongOrder,irreflexive_term_lt,trichotomous_term_lt] >>
  metis_tac[transitive_term_lt,transitive_def]
QED

Theorem TotOrd_term_cmp:
  TotOrd term_cmp
Proof
  rw[term_cmp_def] >>
  match_mp_tac TotOrd_TO_of_Strong >>
  ACCEPT_TAC StrongLinearOrder_term_lt
QED

Theorem StrongLinearOrder_irreflexive[local]:
  StrongLinearOrder R ⇒ irreflexive R
Proof
  rw[StrongLinearOrder,StrongOrder]
QED

val irreflexive_mlstring_lt = MATCH_MP StrongLinearOrder_irreflexive StrongLinearOrder_mlstring_lt

Theorem LLEX_irreflexive[local]:
  ∀R. irreflexive R ⇒ irreflexive (LLEX R)
Proof
  rw[irreflexive_def] >> Induct_on`x`>>rw[]
QED

val irreflexive_LLEX_type_lt = MATCH_MP LLEX_irreflexive (irreflexive_type_lt)

Theorem type_cmp_thm:
  ∀t1 t2.  type_cmp t1 t2 =
    case (t1,t2) of
    | (Tyvar x1, Tyvar x2) => mlstring$compare x1 x2
    | (Tyvar _, _) => LESS
    | (_, Tyvar _) => GREATER
    | (Tyapp x1 a1, Tyapp x2 a2) => pair_cmp mlstring$compare (list_cmp type_cmp) (x1,a1) (x2,a2)
Proof
  ho_match_mp_tac type_ind >>
  conj_tac >- (
    gen_tac >> Cases >>
    simp[type_cmp_def,TO_of_LinearOrder,type_lt_thm, mlstring_lt_def] >>
    every_case_tac >>
    assume_tac TotOrd_compare >>
    fs [TotOrd] >>
    metis_tac [cpn_distinct, cpn_nchotomy]) >>
  ntac 3 strip_tac >>
  Induct >> simp[] >>
  simp[Once type_cmp_def,TO_of_LinearOrder,type_lt_thm] >>
  simp[MATCH_MP pair_cmp_lexTO
       (CONJ TotOrd_compare (MATCH_MP TotOrd_list_cmp TotOrd_type_cmp))] >>
  simp[type_cmp_def,
       SYM(MATCH_MP TO_of_LinearOrder_LLEX irreflexive_type_lt),
       SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_mlstring_lt irreflexive_LLEX_type_lt))] >>
  simp[TO_of_LinearOrder] >>
  every_case_tac >>
  fs [mlstring_lt_def, TO_of_LinearOrder, lexTO, LEX_DEF] >>
  rw [] >>
  rfs [StrongLinearOrder_of_TO, TO_of_LinearOrder] >>
  rfs [] >>
  fs [] >>
  every_case_tac >>
  fs []
QED

Theorem type_cmp_ind:
  ∀P.
      (∀t1 t2.
        (∀x1 a1 x2 a2 x y.
          t1 = Tyapp x1 a1 ∧
          t2 = Tyapp x2 a2 ∧
          MEM x a1 ∧ MEM y a2 ⇒
          P x y)
        ⇒ P t1 t2)
      ⇒ ∀t1 t2. P t1 t2
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac type_ind >>
  rpt conj_tac >> TRY (gen_tac >> Cases >> rw[] >> NO_TAC) >>
  rpt gen_tac >> strip_tac >> gen_tac >>
  ho_match_mp_tac type_ind >> rw[] >>
  first_x_assum match_mp_tac >> simp[] >>
  fs[EVERY_MEM]
QED

Theorem term_cmp_thm:
  ∀t1 t2. term_cmp t1 t2 =
    case (t1,t2) of
    | (Var x1 ty1, Var x2 ty2) => pair_cmp mlstring$compare type_cmp (x1,ty1) (x2,ty2)
    | (Var _ _, _) => LESS
    | (_, Var _ _) => GREATER
    | (Const x1 ty1, Const x2 ty2) => pair_cmp mlstring$compare type_cmp (x1,ty1) (x2,ty2)
    | (Const _ _, _) => LESS
    | (_, Const _ _) => GREATER
    | (Comb s1 t1, Comb s2 t2) => pair_cmp term_cmp term_cmp (s1,t1) (s2,t2)
    | (Comb _ _, _) => LESS
    | (_, Comb _ _) => GREATER
    | (Abs s1 t1, Abs s2 t2) => pair_cmp term_cmp term_cmp (s1,t1) (s2,t2)
    | (Abs _ _, _) => LESS
    | (_, Abs _ _) => GREATER
Proof
  ho_match_mp_tac term_induction >>
  conj_tac >- (
    ntac 2 gen_tac >> Cases >>
    simp[term_cmp_def,TO_of_LinearOrder,term_lt_thm,
         MATCH_MP pair_cmp_lexTO (CONJ TotOrd_compare TotOrd_type_cmp)] >>
    simp[type_cmp_def,TO_of_LinearOrder,
         SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_mlstring_lt
         irreflexive_type_lt))] >>
    every_case_tac >>
    fs [mlstring_lt_def, TO_of_LinearOrder, lexTO, LEX_DEF] >>
    rw [] >>
    rfs [StrongLinearOrder_of_TO, TO_of_LinearOrder] >>
    every_case_tac >>
    fs []) >>
  conj_tac >- (
    ntac 2 gen_tac >> Cases >>
    simp[term_cmp_def,TO_of_LinearOrder,term_lt_thm,
         MATCH_MP pair_cmp_lexTO (CONJ TotOrd_compare TotOrd_type_cmp)] >>
    simp[type_cmp_def,TO_of_LinearOrder,
         SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_mlstring_lt irreflexive_type_lt))] >>
    every_case_tac >>
    fs [mlstring_lt_def, TO_of_LinearOrder, lexTO, LEX_DEF] >>
    rw [] >>
    rfs [StrongLinearOrder_of_TO, TO_of_LinearOrder] >>
    every_case_tac >>
    fs []) >>
  conj_tac >- (
    ntac 2 gen_tac >> strip_tac >>
    Cases >> fs[term_cmp_def,TO_of_LinearOrder,term_lt_thm]>>
    simp[GSYM term_cmp_def,MATCH_MP pair_cmp_lexTO (CONJ TotOrd_term_cmp TotOrd_term_cmp)] >>
    simp[term_cmp_def, TO_of_LinearOrder,
         SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_term_lt irreflexive_term_lt))] ) >>
  ntac 2 gen_tac >> strip_tac >>
  Cases >> fs[term_cmp_def,TO_of_LinearOrder,term_lt_thm]>>
  simp[GSYM term_cmp_def,MATCH_MP pair_cmp_lexTO (CONJ TotOrd_term_cmp TotOrd_term_cmp)] >>
  simp[term_cmp_def, TO_of_LinearOrder,
       SYM(MATCH_MP TO_of_LinearOrder_LEX (CONJ irreflexive_term_lt irreflexive_term_lt))]
QED

Theorem term_cmp_ind:
   ∀P.
      (∀t1 t2.
        (∀x1 y1 x2 y2.
          t1 = Comb x1 y1 ∧ t2 = Comb x2 y2 ⇒
            P x1 x2) ∧
        (∀x1 y1 x2 y2.
          t1 = Comb x1 y1 ∧ t2 = Comb x2 y2 ⇒
            P y1 y2) ∧
        (∀x1 y1 x2 y2.
          t1 = Abs x1 y1 ∧ t2 = Abs x2 y2 ⇒
            P x1 x2) ∧
        (∀x1 y1 x2 y2.
          t1 = Abs x1 y1 ∧ t2 = Abs x2 y2 ⇒
            P y1 y2)
        ⇒ P t1 t2)
      ⇒ ∀t1 t2. P t1 t2
Proof
  gen_tac >> strip_tac >>
  ho_match_mp_tac term_induction >>
  rpt conj_tac >>
  TRY( ntac 2 gen_tac >> Cases >> simp[] >> NO_TAC ) >>
  ntac 3 strip_tac >> Cases >> simp[]
QED

(* alpha ordering *)

Theorem ALPHAVARS_ordav[local]:
  ∀env tp. ALPHAVARS env tp ⇒ ordav env (FST tp) (SND tp) = EQUAL
Proof
  Induct >> rw[ALPHAVARS_def,ordav_def] >>
  Cases_on`h`>>rw[ordav_def] >> fs[] >>
  rfs[term_cmp_def,TO_of_LinearOrder] >>
  ntac 2 (pop_assum mp_tac) >> rw[]
QED

Theorem ordav_ALPHAVARS[local]:
  ∀env t1 t2. ordav env t1 t2 = EQUAL ⇒ ALPHAVARS env (t1,t2)
Proof
  ho_match_mp_tac ordav_ind >>
  rw[ALPHAVARS_def,ordav_def] >>
  fs[term_cmp_def,TO_of_LinearOrder] >>
  rpt(pop_assum mp_tac) >> rw[]
QED

Theorem ALPHAVARS_eq_ordav:
  ∀env t1 t2. ALPHAVARS env (t1,t2) ⇔ ordav env t1 t2 = EQUAL
Proof
  metis_tac[ALPHAVARS_ordav,ordav_ALPHAVARS,pair_CASES,FST,SND]
QED

Theorem RACONV_orda[local]:
  ∀env tp. RACONV env tp ⇒ orda env (FST tp) (SND tp) = EQUAL
Proof
  ho_match_mp_tac RACONV_ind >> rw[ALPHAVARS_eq_ordav]
  >- rw[orda_def] >- rw[orda_def] >- rw[Once orda_def] >>
  rw[Once orda_def]
QED

Theorem orda_RACONV[local]:
  ∀env t1 t2. orda env t1 t2 = EQUAL ⇒ RACONV env (t1,t2)
Proof
  ho_match_mp_tac orda_ind >> rw[] >>
  reverse(Cases_on`t1 ≠ t2 ∨ env ≠ []`) >- (
    fs[RACONV_REFL] ) >>
  qmatch_assum_abbrev_tac`p` >> fs[] >>
  qhdtm_x_assum`orda`mp_tac >>
  simp[Once orda_def] >>
  rw[] >- fs[markerTheory.Abbrev_def] >>
  pop_assum mp_tac >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  rw[RACONV,ALPHAVARS_eq_ordav] >>
  TRY (
    qhdtm_x_assum`term_cmp`mp_tac >>
    rw[term_cmp_def,TO_of_LinearOrder] >>
    NO_TAC) >> fs[] >>
  qhdtm_x_assum`type_cmp`mp_tac >>
  rw[type_cmp_def,TO_of_LinearOrder]
QED

Theorem RACONV_eq_orda:
  ∀env t1 t2. RACONV env (t1,t2) ⇔ orda env t1 t2 = EQUAL
Proof
  metis_tac[RACONV_orda,orda_RACONV,pair_CASES,FST,SND]
QED

Theorem ACONV_eq_orda:
   ∀t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL)
Proof
  rw[ACONV_def,RACONV_eq_orda]
QED

Theorem ordav_FILTER:
  ∀env x y. ordav env x y =
      case FILTER (λ(x',y'). x' = x ∨ y' = y) env of
      | [] => term_cmp x y
      | ((x',y')::_) => if x' = x then if y' = y then EQUAL else LESS else GREATER
Proof
  ho_match_mp_tac ordav_ind >> simp[ordav_def] >>
  strip_assume_tac TotOrd_term_cmp >>
  fs[TotOrd] >> rw[]
QED

Theorem ordav_sym:
  ∀env v1 v2. flip_ord (ordav env v1 v2) = ordav (MAP (λ(x,y). (y,x)) env) v2 v1
Proof
  ho_match_mp_tac ordav_ind >> simp[ordav_def] >>
  conj_tac >- metis_tac[invert_comparison_def,TotOrd_term_cmp,TotOrd,cpn_nchotomy,cpn_distinct] >>
  rw[]
QED

Theorem orda_sym:
   ∀env t1 t2. flip_ord (orda env t1 t2) = orda (MAP (λ(x,y). (y,x)) env) t2 t1
Proof
  ho_match_mp_tac orda_ind >>
  rpt gen_tac >> rpt strip_tac >>
  ONCE_REWRITE_TAC[orda_def] >>
  IF_CASES_TAC >- rw[] >>
  qmatch_assum_abbrev_tac`¬p` >> fs[] >>
  IF_CASES_TAC >- fs[Abbr`p`] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >> simp[ordav_sym] >>
  rw[] >> fs[] >>
  metis_tac[invert_comparison_def,TotOrd_type_cmp,TotOrd_term_cmp,
            TotOrd,cpn_nchotomy,cpn_distinct]
QED

Theorem antisymmetric_alpha_lt:
  antisymmetric alpha_lt
Proof
  rw[antisymmetric_def,alpha_lt_def] >>
  qspecl_then[`[]`,`x`,`y`]mp_tac orda_sym >>
  simp[]
QED

Theorem orda_thm[local]:
  ∀env t1 t2. orda env t1 t2 = ^(#3(dest_cond(rhs(concl(SPEC_ALL orda_def)))))
Proof
  rpt gen_tac >>
  CONV_TAC(LAND_CONV(REWR_CONV orda_def)) >>
  reverse IF_CASES_TAC >- rw[] >> rw[] >>
  BasicProvers.CASE_TAC >> rw[ordav_def] >>
  fs[GSYM RACONV_eq_orda,RACONV_REFL]
QED

Theorem ordav_lx_trans[local]:
  ∀t1 t2 t3 env1 env2.
    ordav env1 t1 t2 ≠ GREATER ∧
    ordav env2 t2 t3 ≠ GREATER ∧
    MAP SND env1 = MAP FST env2
    ⇒ ordav (ZIP (MAP FST env1, MAP SND env2)) t1 t3 ≠ GREATER ∧
      (ordav env1 t1 t2 = LESS ∨ ordav env2 t2 t3 = LESS ⇒
       ordav (ZIP (MAP FST env1, MAP SND env2)) t1 t3 = LESS)
Proof
  mp_tac TotOrd_term_cmp >> simp[TotOrd] >> strip_tac >>
  ntac 3 gen_tac >> Induct >> simp[ordav_def] >- (
    metis_tac[cpn_nchotomy,cpn_distinct] ) >>
  Cases >> simp[ordav_def] >>
  Cases >> simp[] >>
  Cases_on`h` >>
  rw[ordav_def] >>
  metis_tac[cpn_nchotomy,cpn_distinct]
QED

Theorem undo_zip_map_fst[local]:
  p::ZIP(MAP FST l1,MAP SND l2) =
    ZIP (MAP FST ((FST p,v2)::l1), MAP SND ((v2,SND p)::l2))
Proof
  Cases_on`p`>> rw[]
QED

Theorem orda_lx_trans[local]:
  ∀env1 t1 t2 env2 t3.
    orda env1 t1 t2 ≠ GREATER ∧
    orda env2 t2 t3 ≠ GREATER ∧
    MAP SND env1 = MAP FST env2
    ⇒ orda (ZIP (MAP FST env1, MAP SND env2)) t1 t3 ≠ GREATER ∧
      (orda env1 t1 t2 = LESS ∨ orda env2 t2 t3 = LESS ⇒
       orda (ZIP (MAP FST env1, MAP SND env2)) t1 t3 = LESS)
Proof
  completeInduct_on`term_size t1 + term_size t2 + term_size t3` >>
  rpt gen_tac >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> strip_tac >>
  conj_asm2_tac >- (
    qmatch_assum_abbrev_tac`p ⇒ q` >>
    Cases_on`p=T` >- ( fs[Abbr`q`] ) >>
    fs[Abbr`p`] >>
    `orda env1 t1 t2 = EQUAL ∧
     orda env2 t2 t3 = EQUAL` by
    metis_tac[cpn_nchotomy,cpn_distinct] >>
    fs[GSYM RACONV_eq_orda] >>
    qspecl_then[`env1`,`t1,t2`]mp_tac RACONV_TRANS >>
    simp[] >>
    disch_then(qspecl_then[`MAP SND env2`,`t3`]mp_tac) >>
    simp[] >>
    impl_tac >- (
      fs[LIST_EQ_REWRITE,ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF] ) >>
    simp[RACONV_eq_orda] ) >>
  qmatch_abbrev_tac`d ⇒ X` >> strip_tac >>
  qunabbrev_tac`X` >>
  ONCE_REWRITE_TAC[orda_thm] >> simp[] >>
  BasicProvers.CASE_TAC >>
  BasicProvers.CASE_TAC >>
  TRY ( Cases_on`t2`>>fs[Once orda_thm] >> NO_TAC)
  >- (
    qunabbrev_tac`d` >>
    qpat_x_assum`∀x. Y`kall_tac >>
    Cases_on`t2`>>fs[Once orda_thm] >>
    fs[Once orda_thm] >>
    metis_tac[ordav_lx_trans] )
  >- (
    qunabbrev_tac`d` >>
    qpat_x_assum`∀x. Y`kall_tac >>
    Cases_on`t2`>>fs[Once orda_thm] >>
    fs[Once orda_thm] >>
    mp_tac TotOrd_term_cmp >> simp[TotOrd] >> strip_tac >>
    metis_tac[cpn_nchotomy,cpn_distinct] )
  >- (
    Cases_on`t2`>>TRY(fs[Once orda_thm]>>NO_TAC)>>
    qmatch_assum_rename_tac`orda env1 (Comb t1 t2) (Comb t3 t4) ≠ GREATER` >>
    qmatch_assum_rename_tac`orda env2 (Comb t3 t4) (Comb t5 t6) ≠ GREATER` >>
    fs[Q.SPECL[`env`,`Comb a b`,`Comb c d`]orda_thm,LET_THM] >>
    rpt(qpat_x_assum`X ≠ GREATER` mp_tac) >>
    qpat_x_assum`d`mp_tac >>
    simp[Abbr`d`] >> rw[] >> fs[] >> rw[] >>
    fsrw_tac[DNF_ss][] >>
    let
      val tac =
      first_x_assum(fn th =>
        match_mp_tac (MP_CANON th) >>
        simp[term_size_def] >>
        FIRST (map (fn q =>
          qexists_tac q >> simp[] >>
          (fn g as (asl,w) => (Cases_on`^(lhs w)`>>fs[]) g) >>
          NO_TAC)
        [`t1`,`t2`,`t3`,`t4`,`t5`,`t6`]))
    in
      TRY tac >>
      TRY (
        (qsuff_tac`F`>-rw[])>>
        qpat_x_assum`orda (ZIP P) X Y = Z` mp_tac >> simp[] >>
        (fn g as (asl,w) => (qsuff_tac`^(lhs (rand w)) = LESS`>-rw[])g)>>
        tac ) >>
      (qsuff_tac`F`>-rw[])>>
      qpat_x_assum`orda (ZIP P) X Y ≠ Z` mp_tac >> simp[] >>
      fs[GSYM RACONV_eq_orda] >>
      imp_res_tac RACONV_TRANS >> fs[] >>
      first_x_assum(match_mp_tac o MP_CANON) >>
      simp[ZIP_MAP,MAP_MAP_o,combinTheory.o_DEF] >>
      fs[LIST_EQ_REWRITE]
    end) >>
  Cases_on`t2`>>TRY(fs[Once orda_thm]>>NO_TAC)>>
  qmatch_assum_rename_tac`orda env1 (Abs v1 t1) (Abs v2 t2) ≠ GREATER` >>
  qmatch_assum_rename_tac`orda env2 (Abs v2 t2) (Abs v3 t3) ≠ GREATER` >>
  fs[Q.SPECL[`env`,`Abs a b`,`Abs c d`]orda_thm,LET_THM] >>
  mp_tac TotOrd_type_cmp >>
  simp[TotOrd] >> strip_tac >> fs[] >>
  rpt(qpat_x_assum`X ≠ GREATER` mp_tac) >>
  qpat_x_assum`d`mp_tac >>
  simp[Abbr`d`] >> rw[] >> fs[] >> rw[] >>
  TRY (
    fsrw_tac[DNF_ss][] >>
    REWRITE_TAC[undo_zip_map_fst] >>
    first_x_assum(fn th =>
      match_mp_tac (MP_CANON th) >>
      simp[term_size_def] >>
      FIRST (map (fn q =>
        qexists_tac q >> simp[] >>
        (fn g as (asl,w) => (Cases_on`^(lhs w)`>>fs[]) g) >>
        NO_TAC)
      [`t1`,`t2`,`t3`,`t4`,`t5`,`t6`]))) >>
  metis_tac[cpn_nchotomy,cpn_distinct]
QED

Theorem transitive_alpha_lt:
  transitive alpha_lt
Proof
  rw[transitive_def,alpha_lt_def] >>
  qspecl_then[`[]`,`x`,`y`]mp_tac orda_lx_trans >>
  simp[]
QED

Theorem alpha_lt_trans_ACONV:
  ∀x y z.
    (ACONV x y ∧ alpha_lt y z ⇒ alpha_lt x z) ∧
    (alpha_lt x y ∧ ACONV y z ⇒ alpha_lt x z)
Proof
  rw[alpha_lt_def,ACONV_eq_orda] >>
  qspecl_then[`[]`,`x`,`y`]mp_tac orda_lx_trans >>
  simp[]
QED

Theorem alpha_lt_not_refl[simp]:
  ∀x. ¬alpha_lt x x
Proof
  metis_tac[alpha_lt_def,ACONV_eq_orda,cpn_distinct,ACONV_REFL]
QED

(* VFREE_IN lemmas *)

Theorem VFREE_IN_RACONV:
  ∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env)
Proof
  ho_match_mp_tac RACONV_ind >> simp[VFREE_IN_def] >>
  reverse conj_tac >- metis_tac[] >>
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> metis_tac[]
QED

Theorem VFREE_IN_ACONV:
  ∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t)
Proof
  rw[ACONV_def] >> imp_res_tac VFREE_IN_RACONV >> fs[]
QED

Theorem VFREE_IN_subterm:
   ∀t1 t2. VFREE_IN t1 t2 ⇒ t1 subterm t2
Proof
  Induct_on`t2` >> simp[subterm_Comb,subterm_Abs] >>
  metis_tac[]
QED

(* hypset_ok *)

Theorem hypset_ok_nil[simp]:
  hypset_ok []
Proof
rw[hypset_ok_def]
QED

Theorem hypset_ok_sing[simp]:
  ∀p. hypset_ok [p]
Proof
rw[hypset_ok_def]
QED

Theorem hypset_ok_cons:
  hypset_ok (h::hs) ⇔
    EVERY (alpha_lt h) hs ∧ hypset_ok hs
Proof
  rw[hypset_ok_def,MATCH_MP SORTED_EQ transitive_alpha_lt,EVERY_MEM]>>
  metis_tac[]
QED

Theorem hypset_ok_ALL_DISTINCT:
  ∀h. hypset_ok h ⇒ ALL_DISTINCT h
Proof
  simp[hypset_ok_def] >> Induct >>
  simp[MATCH_MP SORTED_EQ transitive_alpha_lt] >>
  rw[] >> strip_tac >> res_tac >> fs[alpha_lt_def] >>
  metis_tac[cpn_distinct,ACONV_REFL,ACONV_eq_orda]
QED

Theorem hypset_ok_eq:
  ∀h1 h2.  hypset_ok h1 ∧ hypset_ok h2 ⇒
            ((h1 = h2) ⇔ (set h1 = set h2))
Proof
  rw[EQ_IMP_THM] >> fs[EXTENSION] >>
  metis_tac[
    hypset_ok_ALL_DISTINCT,PERM_ALL_DISTINCT,
    SORTED_PERM_EQ,hypset_ok_def,
    transitive_alpha_lt, antisymmetric_alpha_lt]
QED

val hypset_ok_append = save_thm("hypset_ok_append",
  Q.ISPEC`alpha_lt` sortingTheory.SORTED_APPEND_IFF
  |> REWRITE_RULE[GSYM hypset_ok_def])

val hypset_ok_el_less = save_thm("hypset_ok_el_less",
  MATCH_MP sortingTheory.SORTED_EL_LESS transitive_alpha_lt
  |> REWRITE_RULE[GSYM hypset_ok_def])

(* term_union lemmas *)

Theorem term_union_idem[simp]:
  ∀ls. term_union ls ls = ls
Proof
  Induct >- simp[term_union_def] >>
  simp[Once term_union_def]
QED

Theorem term_union_thm:
  (∀l2. term_union [] l2 = l2) ∧
    (∀l1. term_union l1 [] = l1) ∧
    (∀h1 t1 h2 t2.
          term_union (h1::t1) (h2::t2) =
          case orda [] h1 h2 of
          | EQUAL =>   h1::term_union t1 t2
          | LESS =>    h1::term_union t1 (h2::t2)
          | GREATER => h2::term_union (h1::t1) t2)
Proof
  rw[] >- rw[term_union_def] >- (
    rw[term_union_def] >>
    BasicProvers.CASE_TAC ) >>
  map_every qid_spec_tac[`h2`,`t2`,`h1`,`t1`] >>
  `∀x. orda [] x x = EQUAL` by (
      rw[GSYM ACONV_eq_orda] ) >>
  Induct >>
  simp[Once term_union_def] >> rw[] >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[]
QED

Theorem MEM_term_union_imp:
  ∀l1 l2 x. MEM x (term_union l1 l2) ⇒ MEM x l1 ∨ MEM x l2
Proof
  Induct >> simp[term_union_thm] >>
  CONV_TAC(SWAP_FORALL_CONV) >>
  Induct >> simp[term_union_thm] >> rpt gen_tac >>
  BasicProvers.CASE_TAC >> rw[] >> fs[] >>
  res_tac >> fs[]
QED

Theorem hypset_ok_term_union[simp]:
  ∀l1 l2. hypset_ok l1 ∧ hypset_ok l2 ⇒
            hypset_ok (term_union l1 l2)
Proof
  simp[hypset_ok_def] >>
  Induct >- simp[term_union_thm] >> qx_gen_tac`h1` >>
  Induct >- simp[term_union_thm] >> qx_gen_tac`h2` >>
  strip_tac >>
  fs[MATCH_MP SORTED_EQ transitive_alpha_lt] >>
  simp[term_union_thm] >>
  BasicProvers.CASE_TAC >>
  simp[MATCH_MP SORTED_EQ transitive_alpha_lt] >>
  rw[] >> imp_res_tac MEM_term_union_imp >>
  fs[GSYM alpha_lt_def]
  >- metis_tac[transitive_alpha_lt,transitive_def]
  >- (
    fs[alpha_lt_def] >>
    qspecl_then[`[]`,`h1`,`h2`]mp_tac orda_lx_trans >>
    simp[] )
  >- (
    qspecl_then[`[]`,`h1`,`h2`]mp_tac orda_sym >>
    simp[alpha_lt_def] ) >>
  qspecl_then[`[]`,`h1`,`h2`]mp_tac orda_sym >>
  fs[alpha_lt_def] >> disch_then(assume_tac o SYM) >>
  qspecl_then[`[]`,`h2`,`h1`]mp_tac orda_lx_trans >>
  simp[]
QED

Theorem EVERY_term_union:
  EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (term_union l1 l2)
Proof
  metis_tac[EVERY_MEM,MEM_term_union_imp]
QED

Theorem MEM_term_union:
  ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) ⇒
      ∃y. MEM y (term_union h1 h2) ∧ ACONV t y
Proof
  Induct >> simp[term_union_thm] >-
    (metis_tac[ACONV_REFL]) >>
  gen_tac >> Induct >> simp[term_union_thm] >-
    (metis_tac[ACONV_REFL]) >>
  simp[hypset_ok_cons,GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 4 strip_tac >> fs[] >>
  fs[hypset_ok_cons] >>
  BasicProvers.CASE_TAC >> rw[] >>
  fs[GSYM ACONV_eq_orda] >>
  metis_tac[MEM,ACONV_REFL,ACONV_SYM,hypset_ok_cons]
QED

Theorem term_union_sing_lt[local]:
  ∀ys x. EVERY (λy. alpha_lt x y) ys ⇒ (term_union [x] ys = x::ys)
Proof
  Induct >> simp[term_union_thm] >> rw[] >> fs[] >>
  fs[alpha_lt_def]
QED

Theorem term_union_insert:
  ∀ys x zs.
    EVERY (λy. alpha_lt y x) ys ∧
    EVERY (λz. alpha_lt x z) zs
    ⇒ (term_union [x] (ys ++ zs) = ys ++ x::zs)
Proof
  Induct >> simp[term_union_sing_lt] >> rw[] >>
  simp[term_union_thm] >>
  `orda [] x h = Greater` by (
    fs[alpha_lt_def] >>
    qspecl_then[`[]`,`h`,`x`]mp_tac orda_sym >>
    simp[] ) >>
  simp[]
QED

Theorem term_union_replace:
  ∀ys x x' zs.
    EVERY (λy. alpha_lt y x) ys ∧ ACONV x x' ∧
    EVERY (λz. alpha_lt x z) zs
    ⇒
    term_union [x] (ys ++ x'::zs) = ys ++ x::zs
Proof
  Induct >> rw[term_union_thm,ACONV_eq_orda,alpha_lt_def] >>
  qspecl_then[`[]`,`h`,`x`]mp_tac orda_sym >>
  simp[] >> disch_then(assume_tac o SYM) >> simp[] >>
  fs[GSYM ACONV_eq_orda, GSYM alpha_lt_def]
QED

Theorem MEM_term_union_first:
  ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ MEM t h1 ⇒ MEM t (term_union h1 h2)
Proof
  Induct >> simp[hypset_ok_cons] >>
  gen_tac >> Induct >> simp[term_union_thm] >>
  rw[hypset_ok_cons] >>
  BasicProvers.CASE_TAC >> rw[] >>
  disj2_tac >>
  first_x_assum match_mp_tac >>
  rw[hypset_ok_cons]
QED

Theorem term_union_insert_mem:
  ∀c h. hypset_ok h ∧ MEM c h ⇒ (term_union [c] h = h)
Proof
  gen_tac >> Induct >> simp[hypset_ok_cons,term_union_thm] >>
  rw[] >> fs[] >- (
    `ACONV c c` by simp[] >> fs[ACONV_eq_orda] ) >>
  fs[EVERY_MEM] >> res_tac >>
  fs[alpha_lt_def] >>
  qspecl_then[`[]`,`h'`,`c`]mp_tac orda_sym >> simp[] >>
  disch_then(assume_tac o SYM) >>
  rw[term_union_thm]
QED

Theorem term_union_insert_remove:
  ∀c h. hypset_ok h ∧ MEM c h ∧ ACONV c' c ⇒ (term_union [c] (term_remove c' h) = h)
Proof
  gen_tac >> Induct >> simp[hypset_ok_cons] >> rw[] >> fs[] >- (
    simp[Once term_remove_def] >>
    fs[ACONV_eq_orda] >>
    Cases_on`h`>>simp[term_union_thm] >> fs[alpha_lt_def] ) >>
  simp[Once term_remove_def] >> fs[EVERY_MEM] >>
  res_tac >>
  imp_res_tac ACONV_SYM >>
  imp_res_tac alpha_lt_trans_ACONV >>
  fs[alpha_lt_def] >>
  qspecl_then[`[]`,`h'`,`c`]mp_tac orda_sym >> simp[] >>
  disch_then(assume_tac o SYM) >>
  qspecl_then[`[]`,`h'`,`c'`]mp_tac orda_sym >> simp[] >>
  disch_then(assume_tac o SYM) >>
  rw[term_union_thm] >>
  match_mp_tac term_union_insert_mem >>
  rw[]
QED

(* term_remove *)

Theorem term_remove_nil[simp]:
  ∀a. term_remove a [] = []
Proof
  rw[Once term_remove_def]
QED

Theorem MEM_term_remove_imp:
  ∀ls x t. MEM t (term_remove x ls) ⇒
      MEM t ls ∧ (hypset_ok ls ⇒ ¬ACONV x t)
Proof
  Induct >> simp[Once term_remove_def] >> rw[] >>
  fs[hypset_ok_def,
     MATCH_MP SORTED_EQ transitive_alpha_lt,
     ACONV_eq_orda,EVERY_MEM,EXISTS_MEM] >>
  res_tac >> fs[] >>
  fs[GSYM ACONV_eq_orda] >>
  fs[alpha_lt_def,ACONV_eq_orda] >>
  qspecl_then[`[]`,`h`,`t`]mp_tac orda_sym >>
  simp[] >> disch_then(assume_tac o SYM) >>
  spose_not_then strip_assume_tac >>
  qspecl_then[`[]`,`x`,`h`]mp_tac orda_lx_trans >>
  simp[] >> qexists_tac`t` >> simp[]
QED

Theorem hypset_ok_term_remove[simp]:
  ∀ls. hypset_ok ls ⇒ ∀t. hypset_ok (term_remove t ls)
Proof
  Induct >> simp[Once term_remove_def] >>
  rw[] >> fs[hypset_ok_def] >> rw[] >>
  fs[MATCH_MP SORTED_EQ transitive_alpha_lt,
     EVERY_MEM,ACONV_eq_orda] >> rw[] >>
  imp_res_tac MEM_term_remove_imp >>
  rfs[hypset_ok_def]
QED

Theorem EVERY_term_remove:
  EVERY P ls ⇒ EVERY P (term_remove t ls)
Proof
  metis_tac[EVERY_MEM,MEM_term_remove_imp]
QED

Theorem MEM_term_remove:
  ∀h x t. MEM t h ∧ ¬ACONV x t ∧ hypset_ok h
    ⇒ MEM t (term_remove x h)
Proof
  Induct >> simp[Once term_remove_def] >>
  simp[hypset_ok_cons] >> rw[EVERY_MEM] >>
  res_tac >> fs[alpha_lt_def,GSYM ACONV_eq_orda]
QED

Theorem term_remove_exists:
  ∀c h. term_remove c h ≠ h ⇒ ∃c'. MEM c' h ∧ ACONV c c'
Proof
  gen_tac >> Induct >> simp[] >>
  simp[Once term_remove_def] >> rw[] >> fs[] >>
  fs[GSYM ACONV_eq_orda] >> metis_tac[]
QED

(* term_image *)

Theorem term_image_nil[simp]:
  term_image f [] = []
Proof
  simp[Once term_image_def]
QED

Theorem MEM_term_image_imp:
  ∀ls f t. MEM t (term_image f ls) ⇒ ∃x. MEM x ls ∧ t = f x
Proof
  Induct >> simp[Once term_image_def] >> rw[] >> fs[] >>
  imp_res_tac MEM_term_union_imp >> fs[] >>
  metis_tac[]
QED

Theorem hypset_ok_term_image:
  ∀ls f. hypset_ok ls ⇒ hypset_ok (term_image f ls)
Proof
  Induct >> simp[Once term_image_def] >> rw[hypset_ok_cons]
QED

Theorem MEM_term_image:
  ∀ls f t. MEM t ls ∧ hypset_ok ls ⇒ ∃y. MEM y (term_image f ls) ∧ ACONV (f t) y
Proof
  Induct >> simp[Once term_image_def] >> rw[hypset_ok_cons] >> rw[] >>
  TRY(metis_tac[ACONV_REFL]) >- metis_tac[MEM_term_union,hypset_ok_sing,MEM,hypset_ok_term_image] >>
  first_x_assum(qspecl_then[`f`,`t`]mp_tac) >> rw[] >>
  metis_tac[MEM_term_union,hypset_ok_sing,hypset_ok_term_image,ACONV_TRANS]
QED

(* VSUBST lemmas *)

Theorem VSUBST_HAS_TYPE:
  ∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty
Proof
  Induct >> simp[VSUBST_def]
  >- (
    map_every qx_gen_tac[`x`,`ty`,`tty`] >>
    Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
    srw_tac[DNF_ss][] >> rw[] >> fs[] >>
    qpat_x_assum`X has_type tty`mp_tac >>
    simp[Once has_type_cases]>>rw[]>>rw[])
  >- (
    simp[Once has_type_cases] >> rw[] >>
    rw[Once has_type_cases] >> metis_tac[] )
  >- (
    map_every qx_gen_tac[`ty`,`ilist`] >>
    simp[Once has_type_cases] >> rw[] >>
    simp[Once has_type_cases] >>
    first_x_assum match_mp_tac >> simp[] >>
    simp[MEM_FILTER] >> rw[] >> TRY(metis_tac[]) >>
    simp[Once has_type_cases])
QED

Theorem VSUBST_WELLTYPED:
  ∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm)
Proof
  metis_tac[VSUBST_HAS_TYPE,welltyped_def]
QED

Theorem VFREE_IN_VSUBST:
  ∀tm u uty ilist.
      welltyped tm ⇒
      (VFREE_IN (Var u uty) (VSUBST ilist tm) ⇔
       ∃y ty. VFREE_IN (Var y ty) tm ∧
              VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty)))
Proof
  Induct >> simp[VFREE_IN_def,VSUBST_def] >- metis_tac[] >>
  map_every qx_gen_tac[`u`,`uty`,`ilist`] >>
  disch_then(qx_choosel_then[`b`,`bty`]strip_assume_tac) >> simp[] >>
  BasicProvers.VAR_EQ_TAC >> qmatch_assum_rename_tac`welltyped tm` >>
  qmatch_abbrev_tac`VFREE_IN vu (if p then Abs (Var vx xty) (VSUBST l1 tm) else Abs (Var x xty) (VSUBST l2 tm)) ⇔ q` >>
  qsuff_tac`VFREE_IN vu (Abs (Var (if p then vx else x) xty) (VSUBST (if p then l1 else l2) tm)) ⇔ q` >- metis_tac[] >>
  simp[VFREE_IN_def,Abbr`vu`] >>
  rw[] >- (
    simp[Abbr`q`,Abbr`l1`,REV_ASSOCD,Abbr`l2`,REV_ASSOCD_FILTER] >>
    EQ_TAC >- (
      rw[] >>
      pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
      metis_tac[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(vx = VARIANT t xx xty)` >>
    qspecl_then[`t`,`xx`,`xty`]mp_tac VARIANT_THM >> strip_tac >>
    qmatch_assum_abbrev_tac`Abbrev(t = VSUBST ll tm)` >>
    rfs[Abbr`t`] >>
    fs[Abbr`vx`] >> strip_tac >>
    (conj_tac >- (
      spose_not_then strip_assume_tac >>
      first_x_assum(qspecl_then[`y`,`ty`]mp_tac) >>
      simp[Abbr`ll`,REV_ASSOCD_FILTER])) >>
    map_every qexists_tac[`y`,`ty`] >> simp[]) >>
  simp[Abbr`q`,Abbr`l2`,REV_ASSOCD_FILTER,Abbr`l1`,Abbr`vx`] >>
  EQ_TAC >- (
    rw[] >>
    pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
    metis_tac[] ) >>
  fs[EXISTS_MEM,EVERY_MEM,markerTheory.Abbrev_def,MEM_FILTER,FORALL_PROD] >>
  simp[GSYM LEFT_FORALL_IMP_THM] >>
  rpt gen_tac >>
  Cases_on`∃a. MEM (a,Var y ty) ilist ∧ VFREE_IN (Var x xty) a` >- (
    fs[] >> first_x_assum(qspecl_then[`a`,`Var y ty`]mp_tac) >>
    simp[] >> rw[] >> fs[] >> fs[VFREE_IN_def] ) >> fs[] >>
  Cases_on`VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))`>>simp[] >>
  Cases_on`Var u uty = Var y ty`>- (
    fs[] >> metis_tac[] ) >>
  Q.ISPECL_THEN[`ilist`,`Var y ty`,`Var y ty`]mp_tac REV_ASSOCD_MEM >>
  strip_tac >> fs[] >>
  fs[VFREE_IN_def] >>
  metis_tac[]
QED

Theorem VSUBST_NIL[simp]:
  ∀tm. VSUBST [] tm = tm
Proof
  ho_match_mp_tac term_induction >>
  simp[VSUBST_def,REV_ASSOCD]
QED

(* INST lemmas *)

Theorem INST_CORE_HAS_TYPE:
  ∀n tm env tyin.
      welltyped tm ∧ (sizeof tm = n) ∧
      (∀s s'. MEM (s,s') env ⇒
              ∃x ty. (s = Var x ty) ∧
                     (s' = Var x (TYPE_SUBST tyin ty)))
      ⇒ (∃x ty. (INST_CORE env tyin tm = Clash(Var x (TYPE_SUBST tyin ty))) ∧
                VFREE_IN (Var x ty) tm ∧
                REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                  env (Var x ty) ≠ Var x ty)
      ∨ (∀x ty. VFREE_IN (Var x ty) tm
                ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) = Var x ty) ∧
        (∃tm'. INST_CORE env tyin tm = Result tm' ∧
               tm' has_type (TYPE_SUBST tyin (typeof tm)) ∧
               (∀u uty. VFREE_IN (Var u uty) tm' ⇔
                        ∃oty. VFREE_IN (Var u oty) tm ∧
                              uty = TYPE_SUBST tyin oty))
Proof
  gen_tac >> completeInduct_on`n` >>
  Induct >> simp[Once INST_CORE_def] >>
  TRY (
    simp[Once INST_CORE_def] >>
    simp[Once has_type_cases] >>
    NO_TAC )
  >- (
    pop_assum kall_tac >> rw[] >>
    simp[Once INST_CORE_def] >>
    simp[Once has_type_cases] >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    fsrw_tac[ARITH_ss][] >>
    simp[Once INST_CORE_def] >>
    first_assum(qspec_then`sizeof tm`mp_tac) >>
    first_x_assum(qspec_then`sizeof tm'`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tm'`,`env`,`tyin`]mp_tac) >> simp[] >>
    qmatch_abbrev_tac`P ⇒ Q` >> strip_tac >>
    qunabbrev_tac`Q` >>
    disch_then(qspecl_then[`tm`,`env`,`tyin`]mp_tac) >>
    simp[] >>
    qunabbrev_tac`P` >>
    reverse (strip_tac >> fs[]) >- (
      simp[Once has_type_cases] >>
      metis_tac[] ) >>
    metis_tac[] )
  >- (
    rpt gen_tac >> strip_tac >>
    fs[] >> BasicProvers.VAR_EQ_TAC >>
    BasicProvers.VAR_EQ_TAC >> qmatch_assum_rename_tac`welltyped tm` >>
    fsrw_tac[ARITH_ss][] >>
    Q.PAT_ABBREV_TAC`env' = X::env` >>
    Q.PAT_ABBREV_TAC`tm' = VSUBST X tm` >>
    Q.PAT_ABBREV_TAC`env'' = X::env` >>
    `sizeof tm' = sizeof tm` by (
      simp[Abbr`tm'`,SIZEOF_VSUBST] ) >>
    `welltyped tm'` by (
      simp[Abbr`tm'`] >>
      match_mp_tac VSUBST_WELLTYPED >>
      simp[] >> simp[Once has_type_cases] ) >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    simp[Once INST_CORE_def] >>
    disch_then(fn th =>
      qspecl_then[`tm`,`env'`,`tyin`]mp_tac th >>
      qspecl_then[`tm'`,`env''`,`tyin`]mp_tac th >>
      qspecl_then[`tm`,`[]`,`tyin`]mp_tac th) >> simp[] >>
    qmatch_abbrev_tac`a ⇒ b` >> strip_tac >> qunabbrev_tac`b` >>
    qmatch_abbrev_tac`(p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`p`,`q`,`r`] >> pop_assum kall_tac >>
    qmatch_abbrev_tac`x ⇒ (p ⇒ q) ⇒ r` >>
    `p` by (
      unabbrev_all_tac >> rw[] >> metis_tac[]) >>
    simp[] >> map_every qunabbrev_tac[`x`,`p`,`q`,`r`] >> pop_assum kall_tac >>
    qunabbrev_tac`a` >>
    fs[] >- (
      rw[] >> fs[] >> fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD] ) >>
    strip_tac >> fs[] >- (
      strip_tac >> fs[] >- (
        rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
        rw[] >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        metis_tac[VARIANT_THM] ) >>
      rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      simp[Once has_type_cases] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      rw[] >> fs[] >>
      metis_tac[VARIANT_THM,term_11]) >>
    strip_tac >> fs[] >- (
      rw[] >> fs[] >>
      rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      simp[Once has_type_cases] >>
      TRY (
        qmatch_assum_abbrev_tac`tz has_type TYPE_SUBST tyin (typeof (VSUBST ez tm))` >>
        `typeof (VSUBST ez tm) = typeof tm` by (
          match_mp_tac WELLTYPED_LEMMA >>
          match_mp_tac VSUBST_HAS_TYPE >>
          conj_tac >- metis_tac[WELLTYPED] >>
          simp[Abbr`ez`] >>
          simp[Once has_type_cases] ) >>
        unabbrev_all_tac >> fs[] >>
        fs[GSYM LEFT_FORALL_IMP_THM] >>
        first_x_assum(qspecl_then[`x'`,`ty''`,`x'`,`ty''`]mp_tac) >>
        simp[] >> BasicProvers.CASE_TAC >> simp[] >> strip_tac >> fs[] >>
        `VFREE_IN (Var x' (TYPE_SUBST tyin ty'')) tm''` by metis_tac[] >>
        metis_tac[VARIANT_THM]) >>
      TRY (
        EQ_TAC >> rw[] >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        pop_assum mp_tac >> rw[] >> fs[] >>
        TRY (
          qexists_tac`oty`>>simp[] >>
          map_every qexists_tac[`u`,`oty`] >>
          simp[] >> NO_TAC) >>
        metis_tac[VARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED] ) >>
      metis_tac[VARIANT_THM,term_11,VSUBST_HAS_TYPE,WELLTYPED] ) >>
    rw[] >> fs[] >>
    rfs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp[Once has_type_cases] >>
    metis_tac[VARIANT_THM,term_11])
QED

Theorem INST_CORE_NIL_IS_RESULT:
  ∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm)
Proof
  rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >> rw[] >> rw[] >> fs[REV_ASSOCD]
QED

Theorem INST_HAS_TYPE:
  ∀tm ty tyin ty'. tm has_type ty ∧ ty' = TYPE_SUBST tyin ty ⇒ INST tyin tm has_type ty'
Proof
  rw[INST_def] >>
  qspecl_then[`tyin`,`tm`]mp_tac INST_CORE_NIL_IS_RESULT >> rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  `welltyped tm` by metis_tac[welltyped_def] >> fs[] >>
  rw[] >> fs[] >> metis_tac[WELLTYPED_LEMMA]
QED

Theorem INST_WELLTYPED:
  ∀tm tyin.  welltyped tm ⇒ welltyped (INST tyin tm)
Proof
  metis_tac[INST_HAS_TYPE,WELLTYPED_LEMMA,WELLTYPED]
QED

Theorem INST_CORE_NIL:
  ∀env tyin tm. welltyped tm ∧ tyin = [] ∧
      (∀x ty. VFREE_IN (Var x ty) tm ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty) ⇒
      INST_CORE env tyin tm = Result tm
Proof
  ho_match_mp_tac INST_CORE_ind >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  Q.PAT_ABBREV_TAC`i1 = INST_CORE X [] tm` >>
  `i1 = Result tm` by (
    qunabbrev_tac`i1` >>
    first_x_assum match_mp_tac >>
    simp[holSyntaxLibTheory.REV_ASSOCD] >>
    rw[] >> metis_tac[] ) >>
  simp[]
QED

Theorem INST_nil:
  welltyped tm ⇒ (INST [] tm = tm)
Proof
  rw[INST_def,INST_CORE_def] >>
  qspecl_then[`[]`,`[]`,`tm`]mp_tac INST_CORE_NIL >>
  simp[holSyntaxLibTheory.REV_ASSOCD]
QED

(* tyvars and tvars *)

Theorem tyvars_ALL_DISTINCT:
  ∀ty. ALL_DISTINCT (tyvars ty)
Proof
  ho_match_mp_tac type_ind >>
  rw[tyvars_def] >>
  Induct_on`l` >> simp[] >>
  rw[ALL_DISTINCT_LIST_UNION]
QED
val _ = export_rewrites["tyvars_ALL_DISTINCT"]

Theorem tvars_ALL_DISTINCT:
  ∀tm. ALL_DISTINCT (tvars tm)
Proof
  Induct >> simp[tvars_def,ALL_DISTINCT_LIST_UNION]
QED
val _ = export_rewrites["tvars_ALL_DISTINCT"]

Theorem tyvars_TYPE_SUBST:
  ∀ty tyin. set (tyvars (TYPE_SUBST tyin ty)) =
      { v | ∃x. MEM x (tyvars ty) ∧ MEM v (tyvars (REV_ASSOCD (Tyvar x) tyin (Tyvar x))) }
Proof
  ho_match_mp_tac type_ind >> simp[tyvars_def] >>
  simp[EXTENSION,EVERY_MEM,MEM_FOLDR_LIST_UNION,PULL_EXISTS,MEM_MAP] >> rw[] >>
  metis_tac[]
QED

Theorem tyvars_TYPE_SUBST_mono:
 !x y s. set (tyvars x) ⊆ set (tyvars y)
  ==> set (tyvars (TYPE_SUBST s x)) ⊆ set (tyvars (TYPE_SUBST s y))
Proof
  rw[tyvars_TYPE_SUBST,SUBSET_DEF]
  >> res_tac
  >> asm_exists_tac
  >> fs[]
QED

Theorem tyvars_typeof_subset_tvars:
  ∀tm ty. tm has_type ty ⇒ set (tyvars ty) ⊆ set (tvars tm)
Proof
  ho_match_mp_tac has_type_ind >>
  simp[tvars_def] >>
  simp[SUBSET_DEF,MEM_LIST_UNION,tyvars_def] >>
  metis_tac[]
QED

Theorem tyvars_Tyapp_MAP_Tyvar:
  ∀x ls. ALL_DISTINCT ls ⇒ (tyvars (Tyapp x (MAP Tyvar ls)) = LIST_UNION [] ls)
Proof
  simp[tyvars_def] >>
  Induct >> fs[tyvars_def,LIST_UNION_def] >>
  rw[LIST_INSERT_def]
QED

Theorem STRING_SORT_SET_TO_LIST_set_tvars:
  ∀tm. STRING_SORT (MAP explode (SET_TO_LIST (set (tvars tm)))) =
         STRING_SORT (MAP explode (tvars tm))
Proof
  gen_tac >> assume_tac(SPEC_ALL tvars_ALL_DISTINCT) >>
  simp[STRING_SORT_EQ] >>
  match_mp_tac sortingTheory.PERM_MAP >>
  pop_assum mp_tac >>
  REWRITE_TAC[sortingTheory.ALL_DISTINCT_PERM_LIST_TO_SET_TO_LIST] >>
  simp[sortingTheory.PERM_SYM]
QED

Theorem mlstring_sort_SET_TO_LIST_set_tvars:
  mlstring_sort (SET_TO_LIST (set (tvars tm))) = mlstring_sort (tvars tm)
Proof
  rw[mlstring_sort_def,STRING_SORT_SET_TO_LIST_set_tvars]
QED

(* Equations *)

Theorem EQUATION_HAS_TYPE_BOOL:
  ∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t)
Proof
  rw[equation_def] >> rw[Ntimes has_type_cases 3] >>
  metis_tac[WELLTYPED_LEMMA,WELLTYPED]
QED

Theorem welltyped_equation:
  ∀s t. welltyped (s === t) ⇔ s === t has_type Bool
Proof
  simp[EQUATION_HAS_TYPE_BOOL] >> simp[equation_def]
QED

Theorem typeof_equation:
  welltyped (l === r) ⇒ (typeof (l === r)) = Bool
Proof
  rw[welltyped_equation] >> imp_res_tac WELLTYPED_LEMMA >> rw[]
QED

Theorem vfree_in_equation:
  VFREE_IN v (s === t) ⇔ (v = Equal (typeof s)) ∨ VFREE_IN v s ∨ VFREE_IN v t
Proof
  rw[equation_def,VFREE_IN_def] >> metis_tac[]
QED

Theorem equation_intro:
  (ty = typeof p) ⇒ (Comb (Comb (Equal ty) p) q = p === q)
Proof
  rw[equation_def]
QED

(* type_ok *)

Theorem type_ok_TYPE_SUBST:
  ∀s tyin ty.
      type_ok s ty ∧
      EVERY (type_ok s) (MAP FST tyin)
    ⇒ type_ok s (TYPE_SUBST tyin ty)
Proof
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[type_ok_def] >> rw[EVERY_MAP,EVERY_MEM] >>
  fs[FORALL_PROD] >>
  metis_tac[REV_ASSOCD_MEM,type_ok_def]
QED

Theorem type_ok_TYPE_SUBST_imp:
  ∀s tyin ty. type_ok s (TYPE_SUBST tyin ty) ⇒
                ∀x. MEM x (tyvars ty) ⇒ type_ok s (TYPE_SUBST tyin (Tyvar x))
Proof
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,type_ok_def] >> rw[] >>
  fs[EVERY_MAP,EVERY_MEM] >> metis_tac[]
QED

(* term_ok *)

Theorem term_ok_welltyped:
  ∀sig t. term_ok sig t ⇒ welltyped t
Proof
  Cases >> Induct >> simp[term_ok_def] >> rw[]
QED

Theorem term_ok_type_ok:
  ∀sig t. is_std_sig sig ∧ term_ok sig t
          ⇒ type_ok (FST sig) (typeof t)
Proof
  Cases >> Induct >> simp[term_ok_def] >> rw[] >>
  fs[is_std_sig_def,type_ok_def]
QED

Theorem term_ok_equation:
  is_std_sig sig ⇒
      (term_ok sig (s === t) ⇔
        term_ok sig s ∧ term_ok sig t ∧
        typeof t = typeof s)
Proof
  Cases_on`sig` >> rw[equation_def,term_ok_def] >>
  rw[EQ_IMP_THM] >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac term_ok_type_ok >>
  fs[is_std_sig_def,type_ok_def] >>
  qexists_tac`[(typeof s,Tyvar (strlit "A"))]` >>
  rw[holSyntaxLibTheory.REV_ASSOCD_def]
QED

Theorem term_ok_clauses:
  is_std_sig sig ⇒
    (term_ok sig (Var s ty) ⇔ type_ok (tysof sig) ty) ∧
    (type_ok (tysof sig) (Tyvar a) ⇔ T) ∧
    (type_ok (tysof sig) Bool ⇔ T) ∧
    (type_ok (tysof sig) (Fun ty1 ty2) ⇔ type_ok (tysof sig) ty1 ∧ type_ok (tysof sig) ty2) ∧
    (term_ok sig (Comb t1 t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ welltyped (Comb t1 t2)) ∧
    (term_ok sig (Equal ty) ⇔ type_ok (tysof sig) ty) ∧
    (term_ok sig (t1 === t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ typeof t1 = typeof t2) ∧
    (term_ok sig (Abs (Var s ty) t) ⇔ type_ok (tysof sig) ty ∧ term_ok sig t)
Proof
  rw[term_ok_def,type_ok_def,term_ok_equation] >>
  fs[is_std_sig_def] >>
  TRY (
    rw[EQ_IMP_THM] >>
    qexists_tac`[(ty,Tyvar(strlit"A"))]` >>
    EVAL_TAC >> NO_TAC) >>
  metis_tac[]
QED

Theorem term_ok_VSUBST:
  ∀sig tm ilist.
    term_ok sig tm ∧
    (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s')
    ⇒
    term_ok sig (VSUBST ilist tm)
Proof
  Cases >> Induct >> simp[VSUBST_def,term_ok_def] >- (
    ntac 2 gen_tac >> Induct >> simp[REV_ASSOCD,term_ok_def] >>
    Cases >> simp[REV_ASSOCD] >> rw[term_ok_def] >> metis_tac[])
  >- (
    rw[] >>
    imp_res_tac VSUBST_WELLTYPED >>
    imp_res_tac WELLTYPED >>
    imp_res_tac VSUBST_HAS_TYPE >>
    metis_tac[WELLTYPED_LEMMA] ) >>
  rw[term_ok_def] >> simp[] >> rw[term_ok_def] >>
  first_x_assum match_mp_tac >>
  rw[term_ok_def,MEM_FILTER] >>
  simp[Once has_type_cases]
QED

Theorem term_ok_INST_CORE:
  ∀sig env tyin tm.
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
      ⇒
      term_ok sig (RESULT (INST_CORE env tyin tm))
Proof
  Cases >> ho_match_mp_tac INST_CORE_ind >>
  simp[term_ok_def,INST_CORE_def] >>
  rw[term_ok_def,type_ok_TYPE_SUBST] >- (
    HINT_EXISTS_TAC >> rw[] >-
      metis_tac[type_ok_TYPE_SUBST] >>
    metis_tac[TYPE_SUBST_compose] ) >>
  Cases_on`INST_CORE env tyin tm`>>fs[] >>
  Cases_on`INST_CORE env tyin tm'`>>fs[] >>
  qspecl_then[`sizeof tm`,`tm`,`env`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  qspecl_then[`sizeof tm'`,`tm'`,`env`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  rw[] >> imp_res_tac WELLTYPED_LEMMA >> simp[] >>
  imp_res_tac term_ok_welltyped >> fs[] >> rw[term_ok_def] >>
  TRY (
    match_mp_tac type_ok_TYPE_SUBST >> rw[] ) >>
  TRY (
    first_x_assum match_mp_tac >>
    conj_tac >>
    TRY (
      match_mp_tac term_ok_VSUBST >>
      rw[] >>
      rw[Once has_type_cases] >>
      rw[term_ok_def] ) >>
    rw[] >>
    metis_tac[] ) >>
  simp[welltyped_def] >> PROVE_TAC[]
QED

Theorem term_ok_INST:
  ∀sig tyin tm.
    term_ok sig tm ∧
    EVERY (type_ok (FST sig)) (MAP FST tyin) ⇒
    term_ok sig (INST tyin tm)
Proof
  rw[INST_def] >>
  metis_tac[INST_CORE_NIL_IS_RESULT,term_ok_welltyped,term_ok_INST_CORE,MEM]
QED

Theorem term_ok_raconv:
  ∀env tp. RACONV env tp ⇒
      ∀sig.
      EVERY (λ(s,s'). welltyped s ∧ welltyped s' ∧ typeof s = typeof s' ∧ type_ok (FST sig) (typeof s)) env ⇒
      term_ok sig (FST tp) ∧ welltyped (SND tp) ⇒ term_ok sig (SND tp)
Proof
  ho_match_mp_tac RACONV_strongind >>
  rw[] >> Cases_on`sig`>>fs[term_ok_def] >- (
    imp_res_tac ALPHAVARS_MEM >> fs[EVERY_MEM,FORALL_PROD] >>
    res_tac >> fs[] >> rw[] ) >>
  rw[] >> fs[]
QED

Theorem term_ok_aconv:
  ∀sig t1 t2. ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 ⇒ term_ok sig t2
Proof
  rw[ACONV_def] >> imp_res_tac term_ok_raconv >> fs[]
QED

Theorem term_ok_VFREE_IN:
   ∀sig t x. VFREE_IN x t ∧ term_ok sig t ⇒ term_ok sig x
Proof
  gen_tac >> Induct >> simp[term_ok_def] >> metis_tac[]
QED

(* de Bruijn terms, for showing alpha-equivalence respect
   by substitution and instantiation *)

val _ = Hol_datatype` dbterm =
    dbVar of mlstring => type
  | dbBound of num
  | dbConst of mlstring => type
  | dbComb of dbterm => dbterm
  | dbAbs of type => dbterm`

(* bind a variable above a de Bruijn term *)

Definition bind_def:
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty) = dbConst x ty ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)
End
val _ = export_rewrites["bind_def"]

(* conversion into de Bruijn *)

Definition db_def:
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty) = dbConst x ty ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs v tm) = dbAbs (typeof v) (bind (dest_var v) 0 (db tm))
End
val _ = export_rewrites["db_def"]

(* de Bruijn versions of VSUBST and VFREE_IN *)

Definition dbVSUBST_def:
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty) = dbConst x ty ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)
End
val _ = export_rewrites["dbVSUBST_def"]

Definition dbVFREE_IN_def:
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty) ⇔ dbConst x ty = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)
End
val _ = export_rewrites["dbVFREE_IN_def"]

Theorem bind_not_free:
   ∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t
Proof
  Induct >> simp[] >> rw[]
QED

Theorem bind_dbVSUBST:
   ∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm)
Proof
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[] >- (
    `REV_ASSOCD (dbVar m t) ls (dbVar m t) = dbVar m t` by (
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[REV_ASSOCD_MEM,MEM_MAP] ) >>
    rw[] ) >>
  Induct_on`ls` >- simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> strip_tac >>
  rw[] >> metis_tac[bind_not_free]
QED

Theorem bind_dbVSUBST_cons:
   ∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm)
Proof
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[REV_ASSOCD] >>fs[] >- (
    Cases_on`z`>>fs[] ) >>
  Cases_on`z`>>fs[] >- (
    Cases_on`x`>>fs[] ) >>
  match_mp_tac bind_not_free >> fs[]
QED

Theorem dbVSUBST_frees:
   ∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm
Proof
  Induct >> simp[]
QED

Theorem dbVFREE_IN_bind:
   ∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm
Proof
  Induct >> simp[] >> rw[] >- metis_tac[]
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]>>
    metis_tac[])
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]) >>
  Cases_on`v`>>fs[]>>
  Cases_on`x=dbVar q r`>>fs[]
QED

Theorem dbVFREE_IN_VFREE_IN:
   ∀tm x. welltyped tm ⇒ (dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm)
Proof
  Induct >> simp[VFREE_IN_def] >- (
    ntac 2 gen_tac >> Cases >> simp[VFREE_IN_def] )
  >- (
    ntac 2 gen_tac >> Cases >> simp[VFREE_IN_def] ) >>
  simp[dbVFREE_IN_bind,PULL_EXISTS] >>
  Cases >> simp[] >> metis_tac[]
QED

Theorem MAP_db_FILTER_neq:
   ∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls)
Proof
  Induct >> simp[] >>
  Cases >> simp[] >>
  rw[] >-( Cases_on`r`>>fs[] ) >> fs[]
QED

Theorem REV_ASSOCD_MAP_db:
   ∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky))
Proof
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
  rw[] >> fs[] >- (
    Cases_on`r`>>fs[]>>rw[] ) >>
  `∃x ty. r = Var x ty` by metis_tac[] >> fs[] >>
  metis_tac[]
QED

Theorem dbVFREE_IN_dbVSUBST:
   ∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty))
Proof
  Induct >> simp[] >> rw[] >> metis_tac[]
QED

Theorem VSUBST_dbVSUBST:
   ∀tm ilist.
    welltyped tm ∧
    (∀k v. MEM (v,k) ilist ⇒ welltyped v ∧ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)
Proof
  Induct >- (
    simp[VSUBST_def] >>
    ntac 2 gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    strip_tac >>
    qpat_x_assum`p ⇒ qq`mp_tac >>
    impl_tac >- metis_tac[] >> strip_tac >>
    rw[] >> fs[] >>
    Cases_on`r`>>fs[] )
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >>
    metis_tac[] ) >>
  gen_tac >> simp[GSYM AND_IMP_INTRO] >>
  disch_then(qx_choosel_then[`b`,`bty`]strip_assume_tac) >>
  srw_tac[][VSUBST_def] >>
  reverse(rw[]) >- (
    first_x_assum(qspec_then`ilist'`mp_tac) >>
    impl_tac >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[Abbr`t'`] >>
    qmatch_abbrev_tac`bind v n (dbVSUBST ls tt) = X` >>
    qspecl_then[`tt`,`v`,`n`,`ls`]mp_tac bind_dbVSUBST >>
    impl_tac >- (
      fs[MEM_MAP,EVERY_MEM,EXISTS_PROD,FORALL_PROD,Abbr`ls`,GSYM LEFT_FORALL_IMP_THM,Abbr`ilist'`,MEM_FILTER] >>
      qunabbrev_tac`v` >>
      conj_tac >- (
        gen_tac >> Cases >> simp[] >>
        metis_tac[] ) >>
      qx_gen_tac`k` >> strip_tac >> simp[] >>
      simp[MAP_db_FILTER_neq] >>
      simp[REV_ASSOCD_FILTER] >>
      qmatch_assum_rename_tac`k = db u` >>
      `∃x ty. u = Var x ty` by metis_tac[] >>
      qspecl_then[`ilist`,`x`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
      impl_tac >- metis_tac[] >>
      simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        qmatch_abbrev_tac`¬dbVFREE_IN (dbVar s t) (db tz)` >>
        qspecl_then[`tz`,`Var s t`]mp_tac dbVFREE_IN_VFREE_IN >>
        impl_tac >- (
          qmatch_assum_abbrev_tac`Abbrev(tz = REV_ASSOCD y l d)` >>
          Q.ISPECL_THEN[`l`,`y`,`d`]mp_tac REV_ASSOCD_MEM >>
          map_every qunabbrev_tac[`y`,`tz`,`d`] >>
          strip_tac >> simp[] >> metis_tac[]) >>
        simp[] >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC >>
        spose_not_then strip_assume_tac >>
        metis_tac[REV_ASSOCD_MEM,VFREE_IN_def,dbVFREE_IN_VFREE_IN] ) >>
      fs[] ) >>
    rw[Abbr`ls`,Abbr`ilist'`,Abbr`X`] >>
    match_mp_tac dbVSUBST_frees >>
    simp[MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
    rw[Abbr`v`] >>
    fs[dbVFREE_IN_bind]) >>
  TRY(rw[Abbr`z`] >> NO_TAC) >>
  first_x_assum(qspec_then`ilist''`mp_tac) >>
  impl_tac >- (
    simp[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
    metis_tac[WELLTYPED_CLAUSES] ) >>
  qunabbrev_tac`ilist''` >> rw[] >>
  qmatch_abbrev_tac`bind v n (dbVSUBST ((zz,x)::ls) tt) = X` >>
  qmatch_assum_rename_tac`Abbrev(z = Var (VARIANT ta s tb) bty)` >>
  qspecl_then[`tt`,`v`,`(b,tb)`,`n`,`ls`]mp_tac bind_dbVSUBST_cons >>
  simp[Abbr`v`] >>
  impl_tac >- (
    qunabbrev_tac`zz` >>
    simp[Abbr`z`,dbVFREE_IN_dbVSUBST] >>
    Q.PAT_ABBREV_TAC`z = VARIANT ta s tb` >>
    simp[dbVFREE_IN_bind] >>
    rpt gen_tac >>
    qspecl_then[`ilist'`,`y`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
    impl_tac >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`tv = db tu` >>
    qspecl_then[`tu`,`Var z tb`]mp_tac dbVFREE_IN_VFREE_IN >>
    impl_tac >- (
      qmatch_assum_abbrev_tac`Abbrev(tu = REV_ASSOCD c l d)` >>
      Q.ISPECL_THEN[`l`,`c`,`d`]mp_tac REV_ASSOCD_MEM >>
      map_every qunabbrev_tac[`c`,`tu`,`d`,`l`,`ilist'`] >>
      strip_tac >> simp[] >> fs[MEM_FILTER] >> metis_tac[]) >>
    rw[] >>
    qmatch_assum_rename_tac`welltyped tm` >>
    qspecl_then[`tm`,`Var y ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[Abbr`tt`] >>
    spose_not_then strip_assume_tac >>
    qsuff_tac`VFREE_IN (Var z tb) ta`>-
      metis_tac[VARIANT_THM] >>
    simp[Abbr`tu`,Abbr`ta`,VFREE_IN_VSUBST] >>
    metis_tac[] ) >>
  rw[] >>
  simp[Abbr`ls`] >> fs[Abbr`z`,Abbr`zz`,Abbr`X`] >>
  match_mp_tac dbVSUBST_frees >>
  simp[Abbr`ilist'`,MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
  rw[Abbr`x`] >>
  fs[dbVFREE_IN_bind]
QED

(* de Bruijn version of INST *)

Definition dbINST_def:
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)
End
val _ = export_rewrites["dbINST_def"]

Theorem dbINST_bind:
   ∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm)
Proof
  Induct >> simp[] >>
  Cases_on`v`>>simp[] >>
  rpt strip_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[]
QED

Theorem dbVSUBST_nil:
   ∀tm. dbVSUBST [] tm = tm
Proof
  Induct >> simp[REV_ASSOCD]
QED
val _ = export_rewrites["dbVSUBST_nil"]

Theorem INST_CORE_dbINST:
   ∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm)
Proof
  completeInduct_on`sizeof tm` >> Cases >> simp[] >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> rw[] )
  >- (
    strip_tac >> rw[INST_CORE_def] >> rw[] )
  >- (
    strip_tac >>
    simp[INST_CORE_def] >>
    rw[] >> fs[] >>
    qmatch_assum_rename_tac`typeof t1 = Fun (typeof t2) rty` >>
    first_assum(qspec_then`sizeof t1`mp_tac) >>
    first_x_assum(qspec_then`sizeof t2`mp_tac) >>
    simp[] >>
    disch_then(qspec_then`t2`strip_assume_tac) >>
    disch_then(qspec_then`t1`strip_assume_tac) >>
    rfs[] >>
    Cases_on`INST_CORE env tyin t1` >>fs[] >>
    Cases_on`INST_CORE env tyin t2`>>fs[] >>
    metis_tac[] ) >>
  strip_tac >>
  rpt gen_tac >> simp[GSYM AND_IMP_INTRO] >>
  disch_then(qx_choosel_then[`b`,`bty`]strip_assume_tac) >>
  qmatch_assum_rename_tac`welltyped tm` >>
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  qmatch_assum_abbrev_tac`IS_RESULT X` >>
  Cases_on`X`>>
  pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >- (
    qmatch_abbrev_tac`bind (x,TYPE_SUBST tyin ty) 0 (db tt) = X` >>
    ntac 3 (pop_assum kall_tac) >>
    qspecl_then[`db tm`,`x,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
    impl_tac >- (
      qx_gen_tac`ty2` >>
      qspecl_then[`tm`,`Var x ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
      rw[] >>
      qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
      qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
      impl_tac >- (
        simp[Abbr`env'`] >>
        metis_tac[] ) >>
      simp[Abbr`Y`] >>
      simp[Abbr`env'`,REV_ASSOCD] >>
      strip_tac >>
      last_x_assum(qspecl_then[`x`,`ty2`]mp_tac) >>
      simp[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
    simp[Abbr`env'`] >>
    impl_tac >- metis_tac[] >>
    rw[] ) >>
  qmatch_abbrev_tac`bind (z,TYPE_SUBST tyin ty) 0 (db tt) = dbINST tyin (bind (x,ty) 0 (db tm))` >>
  ntac 3 (pop_assum kall_tac) >>
  qspecl_then[`db tm`,`z,ty`,`x,ty`,`0`,`[]`]mp_tac bind_dbVSUBST_cons >>
  impl_tac >- (
    simp[] >>
    simp[dbVFREE_IN_bind] >>
    `∃tmi. INST_CORE [] tyin tm = Result tmi` by (
      Cases_on`INST_CORE [] tyin tm`>>simp[] >>
      imp_res_tac INST_CORE_NIL_IS_RESULT >>
      pop_assum(qspec_then`tyin`strip_assume_tac) >>
      rfs[] ) >> fs[] >>
    first_x_assum(qspec_then`sizeof tm`mp_tac) >> simp[] >>
    disch_then(qspec_then`tm`mp_tac) >> simp[] >>
    disch_then(qspecl_then[`tyin`,`[]`,`tmi`]mp_tac) >>
    rw[] >>
    spose_not_then strip_assume_tac >>
    qspecl_then[`tm`,`Var z ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    simp[] >>
    qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    simp[] >> strip_tac >>
    first_x_assum(qspecl_then[`z`,`TYPE_SUBST tyin ty`]mp_tac) >>
    simp[VARIANT_THM,Abbr`z`] >>
    metis_tac[] ) >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qmatch_assum_abbrev_tac`INST_CORE env' tyin tv = Result tt` >>
  `sizeof tv = sizeof tm` by (
    simp[Abbr`tv`] >>
    match_mp_tac SIZEOF_VSUBST >>
    simp[] ) >>
  first_x_assum(qspec_then`sizeof tv`mp_tac) >> simp[] >>
  disch_then(qspec_then`tv`mp_tac) >> simp[] >>
  disch_then(qspecl_then[`tyin`,`env'`,`tt`]mp_tac) >>
  `welltyped tv` by (
    simp[Abbr`tv`] >>
    match_mp_tac VSUBST_WELLTYPED >>
    simp[] >> simp[Once has_type_cases] ) >>
  impl_tac >- (
    simp[Abbr`env'`] >>
    metis_tac[] ) >>
  rw[] >>
  qspecl_then[`tm`,`[Var z ty,Var x ty]`]mp_tac VSUBST_dbVSUBST >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qspecl_then[`db tv`,`z,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
  impl_tac >- (
    simp[] >>
    qx_gen_tac`ty2` >>
    qspecl_then[`tv`,`Var z ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`sizeof tv`,`tv`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    impl_tac >- (
      simp[Abbr`env'`] >>
      metis_tac[] ) >>
    simp[] >>
    simp[Abbr`env'`,REV_ASSOCD] >>
    strip_tac >>
    last_x_assum(qspecl_then[`z`,`ty2`]mp_tac) >>
    simp[] ) >>
  simp[]
QED

Theorem INST_dbINST:
   ∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm)
Proof
  rw[INST_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`tm`,`tyin`,`[]`,`a`]mp_tac INST_CORE_dbINST >>
  simp[]
QED

(* conversion into de Bruijn given an environment of already bound variables *)

Definition dbterm_def:
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty) = dbConst s ty) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs v t) = dbAbs (typeof v) (dbterm ((dest_var v)::env) t))
End
val _ = export_rewrites["dbterm_def"]

Definition bind_list_aux_def:
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)
End
val _ = export_rewrites["bind_list_aux_def"]

Theorem bind_list_aux_clauses:
   (∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm))
Proof
  rpt conj_tac >> Induct >> simp[]
QED

Theorem dbterm_bind:
   ∀tm env. dbterm env tm = bind_list_aux 0 env (db tm)
Proof
  Induct >> simp[bind_list_aux_clauses] >>
  gen_tac >>
  Q.SPEC_TAC(`0n`,`n`) >>
  Induct_on`env` >> simp[find_index_def] >>
  Cases >> simp[] >>
  rw[] >> rw[bind_list_aux_clauses]
QED

Theorem dbterm_db:
   ∀tm. dbterm [] tm = db tm
Proof
  rw[dbterm_bind]
QED

(* alpha-equivalence on de Bruijn terms *)

Theorem dbterm_RACONV:
   ∀t1 env1 t2 env2. welltyped t1 ∧ welltyped t2 ∧ dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2)
Proof
  Induct >- (
    ntac 3 gen_tac >> simp[] >>
    Cases >> simp[RACONV] >>
    TRY (BasicProvers.CASE_TAC >> simp[] >> NO_TAC) >>
    Induct_on`env1` >- (
      simp[find_index_def,LENGTH_NIL_SYM,ALPHAVARS_def] ) >>
    gen_tac >> Cases >> simp[] >>
    simp[find_index_def,ALPHAVARS_def] >>
    Cases_on`h`>>Cases_on`h'`>>simp[] >>
    simp[Once find_index_shift_0] >>
    simp[Once find_index_shift_0,SimpRHS] >>
    rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[] )
  >- (
    simp[] >> ntac 3 gen_tac >>
    Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] )
  >- (
    simp[] >>
    gen_tac >> Cases >> simp[RACONV] >>
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  simp[] >>
  gen_tac >>
  Cases >> simp[RACONV] >- (
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  rw[] >> res_tac >> fs[]
QED

Theorem RACONV_dbterm:
   ∀env tp. RACONV env tp ⇒
    welltyped (FST tp) ∧ welltyped (SND tp) ∧
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp)
Proof
  ho_match_mp_tac RACONV_ind >> rw[] >> rw[] >> fs[PULL_EXISTS] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    rw[] >> rw[] >> NO_TAC ) >>
  Induct_on`env` >> simp[ALPHAVARS_def] >>
  rw[] >> rw[] >- rw[find_index_def] >> fs[] >>
  simp[find_index_def] >>
  `∃x ty. FST h = Var x ty` by metis_tac[] >>
  `∃y tz. SND h = Var y tz` by metis_tac[] >>
  simp[] >>
  simp[Once find_index_shift_0] >>
  simp[Once find_index_shift_0,SimpRHS] >>
  rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[]
QED

Theorem dbterm_ACONV:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2)
Proof
  rw[ACONV_def,EQ_IMP_THM] >- (
    qspecl_then[`[]`,`t1,t2`]mp_tac RACONV_dbterm >> simp[] ) >>
  qspecl_then[`t1`,`[]`,`t2`,`[]`]mp_tac dbterm_RACONV >>
  simp[]
QED

Theorem ACONV_db:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ db t1 = db t2)
Proof
  metis_tac[dbterm_ACONV,dbterm_db]
QED

(* respect of alpha-equivalence by VSUBST and INST follows *)

Theorem ACONV_VSUBST:
   ∀t1 t2 ilist.
    welltyped t1 ∧ welltyped t2 ∧
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty ∧ v has_type ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2)
Proof
  rw[] >>
  imp_res_tac VSUBST_WELLTYPED >>
  rw[ACONV_db] >>
  metis_tac[ACONV_db,VSUBST_dbVSUBST,welltyped_def]
QED

Theorem ACONV_INST:
   ∀t1 t2 tyin. welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2)
Proof
  rw[] >>
  imp_res_tac INST_WELLTYPED >>
  rw[ACONV_db] >> imp_res_tac INST_dbINST >>
  rfs[ACONV_db]
QED

(* list of bound variable names in a term *)

Definition bv_names_def:
  bv_names (Var _ _) = [] ∧
  bv_names (Const _ _) = [] ∧
  bv_names (Comb s t) = bv_names s ++ bv_names t ∧
  bv_names (Abs v t) = (FST(dest_var v))::bv_names t
End
val _ = export_rewrites["bv_names_def"]

(* Simpler versions (non-capture-avoiding) of substitution and instantiation.
   We do the semantics proofs on these and then use the fact that it is
   alpha-equivalence respecting, and suitable equivalent term always exists
   (see below). *)

Definition simple_subst_def:
  (simple_subst ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (simple_subst ilist (Const x ty) = Const x ty) ∧
  (simple_subst ilist (Comb t1 t2) = Comb (simple_subst ilist t1) (simple_subst ilist t2)) ∧
  (simple_subst ilist (Abs v tm) =
    Abs v (simple_subst (FILTER (λ(s',s). (s ≠ v)) ilist) tm))
End
val _ = export_rewrites["simple_subst_def"]

Definition simple_inst_def:
  simple_inst tyin (Var x ty) = Var x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Const x ty) = Const x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs v t) = Abs (simple_inst tyin v) (simple_inst tyin t)
End
val _ = export_rewrites["simple_inst_def"]

Theorem VSUBST_simple_subst:
   ∀tm ilist. DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty) ∧
               welltyped tm
               ⇒ VSUBST ilist tm = simple_subst ilist tm
Proof
  Induct
  >- simp[VSUBST_def]
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >> rw[] >>
    first_x_assum match_mp_tac >>
    fs[IN_DISJOINT] >>
    metis_tac[] ) >>
  simp[VSUBST_def] >>
  rpt gen_tac >> strip_tac >>
  BasicProvers.CASE_TAC >- (
    fs[EXISTS_MEM,MEM_FILTER,UNCURRY] >>
    Cases_on`e`>>fs[]>>res_tac>>fs[MEM_MAP,FORALL_PROD,EXISTS_PROD]>>
    metis_tac[VFREE_IN_def]) >>
  first_x_assum match_mp_tac >>
  simp[rich_listTheory.MAP_SND_FILTER_NEQ,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
  fs[MEM_MAP,EXISTS_PROD,IN_DISJOINT] >>
  metis_tac[]
QED

Theorem INST_CORE_simple_inst:
   ∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty) ∧
      welltyped tm
      ⇒ INST_CORE env tyin tm = Result (simple_inst tyin tm)
Proof
  ho_match_mp_tac INST_CORE_ind >>
  conj_tac >- (
    simp[INST_CORE_def] >> rpt gen_tac >> strip_tac >> rw[] >>
    imp_res_tac (REWRITE_RULE[PROVE[]``A ∨ B ⇔ ¬B ⇒ A``]REV_ASSOCD_MEM) >>
    qmatch_assum_abbrev_tac`MEM (p,q) env` >>
    first_x_assum(qspecl_then[`p`,`q`]mp_tac) >>
    simp[Abbr`q`] >> rw[] >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  conj_tac >- simp[INST_CORE_def] >>
  conj_tac >- (
    srw_tac[][INST_CORE_def] >>
    `sres = Result (simple_inst tyin tm)` by (
      first_x_assum match_mp_tac >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    qunabbrev_tac`sres`>>simp[]>>fs[] >>
    `tres = Result (simple_inst tyin tm')` by (
      first_x_assum match_mp_tac >>
      fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
      metis_tac[] ) >>
    unabbrev_all_tac >> simp[] ) >>
  srw_tac[][INST_CORE_def] >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  fs[] >>rfs[] >>
  `tres = Result (simple_inst tyin tm)` by (
    first_x_assum match_mp_tac >>
    conj_tac >- fs[ALL_DISTINCT_APPEND] >>
    conj_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
    conj_tac >- metis_tac[] >>
    qx_genl_tac[`u`,`uy`,`uy'`] >>
    reverse(Cases_on`u=x ∧ uy' = ty`) >- (
      simp[] >> strip_tac >> fs[] >>
      TRY(first_x_assum match_mp_tac >> fs[] >> metis_tac[]) >>
      Cases_on`u≠x`>-metis_tac[]>>fs[]>>
      fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
      metis_tac[dest_var_def,FST] ) >>
    fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[dest_var_def,FST] ) >>
  fs[]
QED

Theorem INST_simple_inst:
   ∀tyin tm.
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      welltyped tm
      ⇒
      INST tyin tm = simple_inst tyin tm
Proof
  rw[INST_def] >>
  qspecl_then[`[]`,`tyin`,`tm`]mp_tac INST_CORE_simple_inst >>
  simp[]
QED

Theorem simple_subst_has_type:
   ∀tm ty.
      tm has_type ty ⇒
      ∀subst.
        EVERY (λ(s',s). s' has_type typeof s) subst ⇒
        simple_subst subst tm has_type ty
Proof
  ho_match_mp_tac has_type_ind >>
  simp[] >> rw[] >- (
    simp[REV_ASSOCD_ALOOKUP] >> BasicProvers.CASE_TAC >-
    rw[Once has_type_cases] >> imp_res_tac ALOOKUP_MEM >>
    fs[EVERY_MEM,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[typeof_def])
  >- ( rw[Once has_type_cases] )
  >- ( rw[Once has_type_cases] >> metis_tac[] ) >>
  rw[Once has_type_cases] >>
  first_x_assum match_mp_tac >>
  fs[EVERY_FILTER,EVERY_MEM]
QED

Theorem simple_inst_has_type:
   ∀tm tyin. welltyped tm ⇒ simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm))
Proof
  Induct >> rw[] >> rw[Once has_type_cases] >> fs[] >> metis_tac[]
QED

(* rename bound variables from a source of names *)

Definition rename_bvars_def:
  rename_bvars names env (Var s ty) = (names, Var (REV_ASSOCD (s,ty) env s) ty) ∧
  rename_bvars names env (Const s ty) = (names, Const s ty) ∧
  (rename_bvars names env (Comb t1 t2) =
     let (names,t1) = rename_bvars names env t1 in
     let (names,t2) = rename_bvars names env t2 in
     (names, Comb t1 t2)) ∧
  (rename_bvars [] env (Abs v tm) =
     let (names, tm) = rename_bvars [] env tm in
     (names, Abs v tm)) ∧
  (rename_bvars (s'::names) env (Abs v tm) =
     let (names,tm) = rename_bvars names ((s',dest_var v)::env) tm in
     (names, Abs (Var s' (typeof v)) tm))
End

Theorem FST_rename_bvars:
   ∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names)
Proof
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def] >>
  rw[UNCURRY] >> rw[] >>
  Cases_on`rename_bvars names env tm` >> fs[] >>
  fsrw_tac[ARITH_ss][] >>
  REWRITE_TAC[Once arithmeticTheory.ADD_SYM] >>
  match_mp_tac rich_listTheory.DROP_DROP >>
  simp[]
QED

Theorem rename_bvars_RACONV:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧
    DISJOINT (set (MAP FST env ++ names)) (set (MAP (FST o SND) env ++ bv_names tm)) ∧
    DISJOINT (set (MAP FST env ++ names)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
    ALL_DISTINCT (MAP FST env ++ names) ∧
    welltyped tm
    ⇒ RACONV (MAP (λ(s',(s,ty)). (Var s ty, Var s' ty)) env) (tm, SND (rename_bvars names env tm))
Proof
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def,RACONV] >>
  conj_tac >- (
    gen_tac >>
    Induct >> simp[ALPHAVARS_def,REV_ASSOCD] >>
    qx_gen_tac`p` >> PairCases_on`p` >>
    simp[] >> rw[] >>
    simp[REV_ASSOCD] >>
    Cases_on`s=p1`>>simp[]>-(
      Cases_on`ty=p2`>>simp[]>>rw[]>>
      fs[IN_DISJOINT,ALL_DISTINCT_APPEND]>>
      metis_tac[]) >>
    Cases_on`REV_ASSOCD (s,ty) env s = p0`>>simp[]>-(
      `REV_ASSOCD (s,ty) env s ≠ s` by PROVE_TAC[] >>
      imp_res_tac (REWRITE_RULE[PROVE[]``A ∨ B ⇔ ¬B ⇒ A``]REV_ASSOCD_MEM) >>
      fs[MEM_MAP,FORALL_PROD] >> metis_tac[] ) >>
    first_x_assum match_mp_tac >>
    fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
    metis_tac[] ) >>
  conj_tac >- (
    srw_tac[][UNCURRY] >>
    simp[RACONV] >>
    conj_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    TRY (
      qexists_tac`SND (rename_bvars names env tm)`>>simp[] >>
      qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
      impl_tac >- DECIDE_TAC >> strip_tac >>
      first_assum (assume_tac o Q.AP_TERM`LENGTH`) >>
      fs[LENGTH_DROP] >>
      `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >>
      conj_tac >- (
        rw[] >> spose_not_then strip_assume_tac >>
        imp_res_tac rich_listTheory.MEM_DROP >>
        metis_tac[] ) >>
      conj_tac >- (
        rw[] >> spose_not_then strip_assume_tac >>
        imp_res_tac rich_listTheory.MEM_DROP >>
        metis_tac[] ) >>
      conj_tac >- metis_tac[ALL_DISTINCT_DROP] >>
      rw[] >> spose_not_then strip_assume_tac >>
      imp_res_tac rich_listTheory.MEM_DROP >>
      metis_tac[]) >>
    metis_tac[]) >>
  rw[UNCURRY] >>
  rw[RACONV] >> fs[] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
  rfs[] >> metis_tac[]
QED

Theorem rename_bvars_ACONV:
   ∀names tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
    DISJOINT (set names) {x | MEM x (bv_names tm) ∨ ∃ty. VFREE_IN (Var x ty) tm} ∧
    welltyped tm
    ⇒
    ACONV tm (SND (rename_bvars names [] tm))
Proof
  rw[ACONV_def] >>
  qspecl_then[`names`,`[]`,`tm`]mp_tac rename_bvars_RACONV >>
  simp[] >> disch_then match_mp_tac >>
  fs[IN_DISJOINT] >> metis_tac[]
QED

Theorem rename_bvars_has_type:
   ∀names env tm ty. tm has_type ty ⇒ SND (rename_bvars names env tm) has_type ty
Proof
  ho_match_mp_tac(theorem"rename_bvars_ind") >>
  srw_tac[][rename_bvars_def] >> rw[] >> fs[]
  >- fs[Once has_type_cases] >>
  qpat_x_assum`X has_type Y`mp_tac >>
  simp[Once has_type_cases] >> strip_tac >>
  simp[Once has_type_cases] >> metis_tac[]
QED

Theorem rename_bvars_welltyped:
   ∀names env tm. welltyped tm ⇒ welltyped (SND (rename_bvars names env tm))
Proof
  metis_tac[rename_bvars_has_type,welltyped_def]
QED

(* appropriate fresh term for using the simple functions above *)

val fresh_def = new_specification("fresh_def",["fresh"],
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])

Theorem fresh_union:
   FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t
Proof
  metis_tac[fresh_def,FINITE_UNION,IN_UNION]
QED

Theorem fresh_names_exist:
   ∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s
Proof
  gen_tac >> Induct >> strip_tac
  >- (qexists_tac`[]`>>simp[]) >> rw[] >> fs[] >>
  qexists_tac`fresh (s ∪ set names)::names` >>
  simp[fresh_union]
QED

Theorem bv_names_rename_bvars:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ⇒
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names
Proof
  ho_match_mp_tac(theorem"rename_bvars_ind")>>
  simp[rename_bvars_def] >>
  conj_tac >- (
    rw[UNCURRY] >>
    Cases_on`rename_bvars names env tm`>>fs[] >>
    `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >> fs[] >>
    qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
    rw[] >> fs[] >>
    `LENGTH (bv_names tm') ≤ LENGTH names - LENGTH (bv_names tm)` by DECIDE_TAC >> fs[] >>
    simp[TAKE_SUM] ) >>
  rw[UNCURRY]
QED

(* various rewrites for FINITE sets to make this go through *)

Theorem FINITE_VFREE_IN:
   ∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm}
Proof
  Induct >> simp[] >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_x_assum`FINITE s1`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE s2` >>
    strip_tac >>
    qmatch_abbrev_tac`FINITE s3` >>
    qsuff_tac`s3 = s1 ∪ s2` >- metis_tac[FINITE_UNION] >>
    unabbrev_all_tac >> simp[EXTENSION] >> metis_tac[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE a` >>
  qmatch_abbrev_tac`FINITE b` >>
  qsuff_tac`b ⊆ a` >- metis_tac[SUBSET_FINITE] >>
  unabbrev_all_tac >> simp[SUBSET_DEF] >>
  metis_tac[]
QED
val _ = export_rewrites["FINITE_VFREE_IN"]

Theorem FINITE_VFREE_IN_2:
   ∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm}
Proof
  Induct >> simp[] >- (
    rw[] >>
    qmatch_abbrev_tac`FINITE x` >>
    qsuff_tac`∃y. x = {y}`>-metis_tac[FINITE_SING] >>
    rw[EXTENSION,Abbr`x`,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] )
  >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_x_assum`FINITE s1`mp_tac >>
    qmatch_assum_abbrev_tac`FINITE s2` >>
    strip_tac >>
    qmatch_abbrev_tac`FINITE s3` >>
    qsuff_tac`s3 = s1 ∪ s2` >- metis_tac[FINITE_UNION] >>
    unabbrev_all_tac >> simp[EXTENSION] >> metis_tac[] ) >>
  rw[] >>
  qmatch_assum_abbrev_tac`FINITE a` >>
  qmatch_abbrev_tac`FINITE b` >>
  qsuff_tac`b ⊆ a` >- metis_tac[SUBSET_FINITE] >>
  unabbrev_all_tac >> simp[SUBSET_DEF] >>
  metis_tac[]
QED
val _ = export_rewrites["FINITE_VFREE_IN_2"]

Theorem FINITE_VFREE_IN_list:
   ∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls}
Proof
  Induct >> simp[] >> rw[] >>
  qmatch_assum_abbrev_tac`FINITE s` >>
  qmatch_abbrev_tac`FINITE t` >>
  `t = s ∪ {x | ∃ty. VFREE_IN (Var x ty) h}` by (
    simp[EXTENSION,Abbr`t`,Abbr`s`] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_UNION]
QED
val _ = export_rewrites["FINITE_VFREE_IN_list"]

Theorem FINITE_MEM_Var:
   ∀ls. FINITE {(x,ty) | MEM (Var x ty) ls}
Proof
  Induct >> simp[] >>
  Cases >> simp[] >>
  qmatch_assum_abbrev_tac`FINITE P` >>
  qmatch_abbrev_tac`FINITE Q` >>
  `Q = (m,t) INSERT P` by (
    simp[Abbr`P`,Abbr`Q`,EXTENSION] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_INSERT]
QED
val _ = export_rewrites["FINITE_MEM_Var"]

val fresh_term_def = new_specification("fresh_term_def",["fresh_term"],
  Q.prove(`∃f. ∀s tm. FINITE s ⇒
                     welltyped tm ⇒
                     welltyped (f s tm) ∧
                     ACONV tm (f s tm) ∧
                     ALL_DISTINCT (bv_names (f s tm)) ∧
                     DISJOINT (set (bv_names (f s tm))) s`,
    simp[GSYM SKOLEM_THM] >> rw[RIGHT_EXISTS_IMP_THM] >>
    qspecl_then[`IMAGE explode (s ∪ set (bv_names tm) ∪ {x | ∃ty. VFREE_IN (Var x ty) tm})`,`LENGTH (bv_names tm)`]
      mp_tac fresh_names_exist >> rw[] >>
    qexists_tac`SND (rename_bvars (MAP implode names) [] tm)` >>
    conj_tac >- metis_tac[rename_bvars_welltyped] >>
    conj_tac >- (
      match_mp_tac rename_bvars_ACONV >>
      fs[IN_DISJOINT,MEM_MAP,implode_def] >>
      Cases >> simp[] >>
      metis_tac[explode_implode,implode_def] ) >>
    qspecl_then[`MAP implode names`,`[]`,`tm`]mp_tac bv_names_rename_bvars >>
    simp[TAKE_LENGTH_ID_rwt] >>
    fs[IN_DISJOINT,MEM_MAP,implode_def] >>
    strip_tac >>
    Cases >> simp[] >>
    metis_tac[explode_implode,implode_def] ))

(* Alternative characterisation of VARIANT, and thereby of VSUBST and INST_CORE.
   Better for evaluation. *)

Definition vfree_in_def:
  vfree_in v tm =
    case tm of
      Abs bv bod => v <> bv /\ vfree_in v bod
    | Comb s t => vfree_in v s \/ vfree_in v t
    | _ => (tm = v)
End

Theorem vfree_in_thm:
   !name ty y. (VFREE_IN (Var name ty) y = vfree_in (Var name ty) y)
Proof
  ntac 2 gen_tac >> Induct >> simp[VFREE_IN_def,Once vfree_in_def] >>
  simp[Once vfree_in_def,SimpRHS] >>
  BasicProvers.CASE_TAC >>
  simp[Q.SPECL[`Var x1 ty1`,`Var x2 ty2`]vfree_in_def] >>
  simp[Q.SPECL[`Var x1 ty1`,`Const x2 ty2`]vfree_in_def] >>
  simp[Q.SPECL[`Var x1 ty1`,`Comb x2 ty2`]vfree_in_def] >>
  simp[Q.SPECL[`Var x1 ty1`,`Abs x2 ty2`]vfree_in_def] >>
  METIS_TAC[]
QED

Definition variant_def:
  variant avoid v =
    if EXISTS (vfree_in v) avoid then
    case v of
       Var s ty => variant avoid (Var(s ^ (strlit "'")) ty)
    | _ => v else v
Termination
  WF_REL_TAC `measure (\(avoid,v).
     let n = SUM_SET (BIGUNION (set (MAP (λa. {strlen x + 1 | ∃ty. VFREE_IN (Var x ty) a}) avoid))) in
       n - (case v of Var x ty => strlen x | _ => 0))` >>
   gen_tac >> Cases >> srw_tac[][strlen_def,strcat_thm,implode_def] >>
   qsuff_tac`STRLEN s' < n` >- simp[] >>
   simp[Abbr`n`] >> fs[GSYM vfree_in_thm,EXISTS_MEM] >>
   match_mp_tac SUM_SET_IN_LT >>
   qexists_tac`STRLEN s' + 1` >> simp[MEM_MAP,PULL_EXISTS] >>
   map_every qexists_tac[`e`,`strlit s'`,`ty`] >> simp[] >> rw[] >>
   qmatch_abbrev_tac`FINITE s` >>
   `s = IMAGE (λ(x,ty). strlen x + 1) {(x,ty) | VFREE_IN (Var x ty) a}` by (
     simp[Abbr`s`,pred_setTheory.EXTENSION,PULL_EXISTS,strlen_def] ) >>
   pop_assum SUBST1_TAC >>
   match_mp_tac pred_setTheory.IMAGE_FINITE >>
   simp[]
End

val variant_ind = fetch "-" "variant_ind"

val variant_vsubst_thm = save_thm("variant_vsubst_thm",prove(
  ``!xs v x name.
      (xs = [x]) /\ (v = (Var name ty)) ==>
      (variant xs (Var name ty) =
       Var (VARIANT x (explode name) ty) ty)``,
  REWRITE_TAC [VARIANT_def] \\ HO_MATCH_MP_TAC variant_ind
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  \\ MP_TAC (Q.SPECL[`name`,`ty`, `x`] vfree_in_thm) \\ FULL_SIMP_TAC std_ss [] \\ STRIP_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [EXISTS_DEF]
  \\ reverse IF_CASES_TAC
  \\ FULL_SIMP_TAC (srw_ss()) [] THEN1
   (MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`x`,`explode name`,`ty`])
    \\ Cases_on `VARIANT_PRIMES x (explode name) ty`
    THEN1 (FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode])
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode])
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`x`,`explode name`,`ty`])
  \\ Cases_on `VARIANT_PRIMES x (explode name) ty`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode]
  \\ REPEAT STRIP_TAC
  \\ sg `!m. m < n ==>
         VFREE_IN (Var (name ^ (implode (REPLICATE (SUC m) #"'"))) ty) x`
  THEN1 (REPEAT STRIP_TAC \\ `SUC m < SUC n` by DECIDE_TAC \\ RES_TAC \\ FULL_SIMP_TAC std_ss [rich_listTheory.REPLICATE_GENLIST]
         \\ FULL_SIMP_TAC std_ss [mlstringTheory.strcat_thm,mlstringTheory.explode_implode])
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE_GENLIST,GENLIST_CONS]
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`x`,`explode (name ^ strlit "'")`,`ty`])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,mlstringTheory.strcat_thm,explode_implode,explode_thm]
  \\ Cases_on `VARIANT_PRIMES x (STRCAT (explode name) "'") (ty) = n`
  \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `VARIANT_PRIMES x (STRCAT (explode name) "'") ty < n \/
      n < VARIANT_PRIMES x (STRCAT (explode name) "'") ty` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL);

val VSUBST_thm = save_thm("VSUBST_thm",
  REWRITE_RULE[SYM variant_vsubst_thm] VSUBST_def)

Definition subtract_def:
  subtract l1 l2 = FILTER (\t. ~(MEM t l2)) l1
End

Definition insert_def:
  insert x l = if MEM x l then l else x::l
End

Definition itlist_def:
  itlist f l b =
    case l of
      [] => b
    | (h::t) => f h (itlist f t b)
End

Definition union_def:
  union l1 l2 = itlist insert l1 l2
End

Theorem MEM_union:
   !xs ys x. MEM x (union xs ys) <=> MEM x xs \/ MEM x ys
Proof
  Induct \\ FULL_SIMP_TAC std_ss [union_def]
  \\ ONCE_REWRITE_TAC [itlist_def] \\ SRW_TAC [] [insert_def]
  \\ METIS_TAC []
QED

Theorem EXISTS_union:
   !xs ys. EXISTS P (union xs ys) <=> EXISTS P xs \/ EXISTS P ys
Proof
  SIMP_TAC std_ss [EXISTS_MEM,MEM_MAP,MEM_union] \\ METIS_TAC []
QED

Definition frees_def:
  frees tm =
    case tm of
      Var _ _ => [tm]
    | Const _ _ => []
    | Abs bv bod => subtract (frees bod) [bv]
    | Comb s t => union (frees s) (frees t)
End

Theorem MEM_frees_EQ:
   !a x. MEM x (frees a) = ?n ty. (x = Var n ty) /\ MEM (Var n ty) (frees a)
Proof
  Induct \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union]
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union])
  THEN1 (SIMP_TAC (srw_ss()) [Once frees_def,MEM_union])
  \\ ONCE_REWRITE_TAC [EQ_SYM_EQ]
  \\ SIMP_TAC (srw_ss()) [Once frees_def,MEM_union] THEN1 (METIS_TAC [])
  \\ SIMP_TAC (srw_ss()) [subtract_def,MEM_FILTER]
  \\ REPEAT STRIP_TAC \\ EQ_TAC \\ REPEAT STRIP_TAC \\ METIS_TAC []
QED

val variant_inst_thm = save_thm("variant_inst_thm",prove(
  ``!xs v x name a.
      welltyped a ∧
      (xs = frees a) /\
      (v = (Var name ty1)) ==>
      (variant (frees a) (Var name ty1) =
       Var (VARIANT a (explode name) ty1) ty1)``,
  REWRITE_TAC [VARIANT_def] \\ HO_MATCH_MP_TAC variant_ind
  \\ SIMP_TAC std_ss [] \\ REPEAT STRIP_TAC
  \\ ASM_SIMP_TAC (srw_ss()) [Once variant_def,EXISTS_DEF]
  \\ sg `EXISTS (vfree_in (Var name ty1)) (frees a) =
      VFREE_IN (Var name ty1) a` THEN1
   (Q.PAT_X_ASSUM `welltyped a` MP_TAC
    \\ REPEAT (POP_ASSUM (K ALL_TAC))
    \\ Induct_on `a` \\ SIMP_TAC (srw_ss()) [Once frees_def,Once vfree_in_def]
    THEN1 (REPEAT STRIP_TAC
      \\ FULL_SIMP_TAC std_ss [EXISTS_union,VFREE_IN_def])
    \\ REPEAT STRIP_TAC
    \\ FULL_SIMP_TAC std_ss []
    \\ BasicProvers.VAR_EQ_TAC
    \\ FULL_SIMP_TAC std_ss [VFREE_IN_def,WELLTYPED_CLAUSES]
    \\ FIRST_X_ASSUM (fn th => FULL_SIMP_TAC std_ss [SYM th])
    \\ FULL_SIMP_TAC (srw_ss()) [EXISTS_MEM,subtract_def,MEM_FILTER,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [MEM_frees_EQ]
    \\ FULL_SIMP_TAC std_ss [term_11,PULL_EXISTS]
    \\ ONCE_REWRITE_TAC [vfree_in_def] \\ FULL_SIMP_TAC (srw_ss()) []
    \\ METIS_TAC [])
  \\ FULL_SIMP_TAC std_ss []
  \\ reverse (Cases_on `VFREE_IN (Var name ty1) a`) THEN1
   (MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`a`,`explode name`,`ty1`])
    \\ Cases_on `VARIANT_PRIMES a (explode name) ty1`
    THEN1 FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode]
    \\ REPEAT STRIP_TAC \\ POP_ASSUM (MP_TAC o Q.SPEC `0`)
    \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode])
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`a`,`explode name`,`ty1`])
  \\ Cases_on `VARIANT_PRIMES a (explode name) ty1`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE,mlstringTheory.implode_explode]
  \\ REPEAT STRIP_TAC
  \\ POP_ASSUM (ASSUME_TAC o Q.GEN `m` o SIMP_RULE std_ss [] o Q.SPEC `SUC m`)
  \\ MP_TAC (VARIANT_PRIMES_def |> Q.SPECL [`a`,`STRCAT (explode name) "'"`,`ty1`])
  \\ FULL_SIMP_TAC std_ss [GSYM APPEND_ASSOC,APPEND,mlstringTheory.strcat_thm,mlstringTheory.explode_implode,explode_thm]
  \\ Q.ABBREV_TAC `k = VARIANT_PRIMES a (STRCAT (explode name) "'") ty1`
  \\ FULL_SIMP_TAC (srw_ss()) [rich_listTheory.REPLICATE_GENLIST,GENLIST_CONS]
  \\ Cases_on `k = n` \\ FULL_SIMP_TAC std_ss []
  \\ REPEAT STRIP_TAC
  \\ `k < n \/ n < k` by DECIDE_TAC
  \\ RES_TAC \\ FULL_SIMP_TAC std_ss [])
  |> SIMP_RULE std_ss [] |> SPEC_ALL);

Theorem INST_CORE_Abs_thm:
   ∀v t env tyin. welltyped (Abs v t) ⇒
   INST_CORE env tyin (Abs v t) =
   (let (x,ty) = dest_var v in
    let ty' = TYPE_SUBST tyin ty in
    let v' = Var x ty' in
    let env' = (v,v')::env in
    let tres = INST_CORE env' tyin t
    in
      if IS_RESULT tres then Result (Abs v' (RESULT tres))
      else
        (let w = CLASH tres
         in
           if w ≠ v' then tres
           else
             (let (x',_) =
               dest_var (variant (frees (RESULT (INST_CORE [] tyin t))) (Var x ty'))
              in
              let t' = VSUBST [(Var x' ty,Var x ty)] t in
              let env'' = (Var x' ty,Var x' ty')::env in
              let tres' = INST_CORE env'' tyin t'
              in
                if IS_RESULT tres' then
                  Result (Abs (Var x' ty') (RESULT tres'))
                else tres')))
Proof
  rw[] >> simp[Once INST_CORE_def] >> rw[] >>
  unabbrev_all_tac >> fs[] >>
  rfs[GSYM INST_def] >>
  imp_res_tac INST_WELLTYPED >>
  fs[variant_inst_thm] >> rw[] >> fs[]
QED

(* provable terms are ok and of type bool *)

Theorem proves_theory_ok:
   ∀thyh c. thyh |- c ⇒ theory_ok (FST thyh)
Proof
  ho_match_mp_tac proves_ind >> rw[]
QED

Theorem theory_ok_sig:
   ∀thy. theory_ok thy ⇒ is_std_sig (sigof thy)
Proof
  Cases >> rw[theory_ok_def]
QED

Theorem proves_term_ok:
   ∀thyh c. thyh |- c ⇒
      hypset_ok (SND thyh) ∧
      EVERY (λp. term_ok (sigof (FST thyh)) p ∧ p has_type Bool) (c::(SND thyh))
Proof
  ho_match_mp_tac proves_strongind >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation,term_ok_def]) >>
  strip_tac >- rw[EQUATION_HAS_TYPE_BOOL] >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    imp_res_tac theory_ok_sig >>
    rw[term_ok_equation,term_ok_def]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation] >>
    imp_res_tac WELLTYPED_LEMMA >> fs[] >>
    simp[WELLTYPED] >>
    match_mp_tac EVERY_term_union >>
    rpt conj_tac >>
    match_mp_tac EVERY_term_remove >>
    fs[EVERY_MEM]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation] >>
    imp_res_tac ACONV_TYPE >> fs[] >-
      metis_tac[WELLTYPED_LEMMA,WELLTYPED,term_ok_welltyped] >>
    match_mp_tac EVERY_term_union >> fs[] ) >>
  strip_tac >- (
    rw[term_ok_VSUBST,hypset_ok_term_image,EVERY_MEM] >>
    imp_res_tac MEM_term_image_imp >> fs[EVERY_MEM] >>
    metis_tac[term_ok_VSUBST,VSUBST_HAS_TYPE] ) >>
  strip_tac >- (
    rw[term_ok_INST,hypset_ok_term_image] >> fs[EVERY_MEM] >>
    rw[] >> imp_res_tac MEM_term_image_imp >>
    metis_tac[SIMP_RULE(srw_ss())[EVERY_MEM]term_ok_INST,INST_HAS_TYPE,TYPE_SUBST_Bool] ) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation,term_ok_def] >>
    metis_tac[EVERY_term_union]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    imp_res_tac theory_ok_sig >>
    rw[term_ok_equation,term_ok_def]) >>
  rw[theory_ok_def]
QED

(* some derived rules *)

val assume = proves_rules |> CONJUNCTS |> el 2
val deductAntisym_equation = save_thm("deductAntisym_equation",
  proves_rules |> CONJUNCTS |> el 4)
val eqMp_equation = save_thm("eqMp_equation",
  proves_rules |> CONJUNCTS |> el 5
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])
val refl_equation =  save_thm("refl_equation",
  proves_rules |> CONJUNCTS |> el 9)
val appThm_equation = save_thm("appThm_equation",
  proves_rules |> CONJUNCTS |> el 8
  |> REWRITE_RULE[GSYM AND_IMP_INTRO])

Theorem addAssum:
   ∀thy h c a. (thy,h) |- c ∧ term_ok (sigof thy) a ∧ (a has_type Bool) ⇒
      (thy,term_union [a] h) |- c
Proof
  rw[] >>
  ho_match_mp_tac (MP_CANON eqMp_equation) >>
  map_every qexists_tac[`c`,`c`] >> simp[] >>
  qspecl_then[`a`,`thy`]mp_tac assume >>
  imp_res_tac proves_theory_ok >> fs[] >> strip_tac >>
  Cases_on`ACONV (c === c) a` >- (
    qspecl_then[`c === c`,`thy`]mp_tac refl_equation >>
    imp_res_tac theory_ok_sig >>
    imp_res_tac proves_term_ok >>
    fs[term_ok_equation] >> strip_tac >>
    imp_res_tac eqMp_equation >>
    fs[term_union_thm] ) >>
  qspecl_then[`c`,`thy`]mp_tac refl_equation >>
  imp_res_tac proves_term_ok >> fs[] >> strip_tac >>
  qspecl_then[`a`,`c === c`,`[a]`,`[]`,`thy`]mp_tac deductAntisym_equation >>
  simp[term_union_thm] >>
  `term_remove (c === c) [a] = [a]` by (
    simp[Once term_remove_def,GSYM ACONV_eq_orda] ) >>
  rw[] >>
  imp_res_tac eqMp_equation >>
  metis_tac[ACONV_REFL,term_union_idem]
QED

(* inference system respects alpha-equivalence *)

val rws = [
  rich_listTheory.EL_APPEND1,
  rich_listTheory.EL_APPEND2,
  rich_listTheory.EL_LENGTH_APPEND_rwt,
  rich_listTheory.EL_TAKE,
  rich_listTheory.EL_DROP,
  rich_listTheory.EL_CONS]

Theorem proves_concl_ACONV[local]:
  ∀thyh c c'. thyh |- c ∧ ACONV c c' ∧ welltyped c' ⇒ thyh |- c'
Proof
  rw[] >>
  qspecl_then[`c'`,`FST thyh`]mp_tac refl_equation >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_aconv >> pop_assum kall_tac >> simp[] >>
  Cases_on`thyh`>>fs[]>>
  metis_tac[eqMp_equation,term_union_thm,ACONV_SYM]
QED

Theorem proves_ACONV_lemma[local]:
  ∀thy c h' h1 h.
    (thy,h1++h) |- c ∧
    hypset_ok (h1++h') ∧
    EVERY (λx. EXISTS (ACONV x) h') h ∧
    EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h'
    ⇒ (thy,h1++h') |- c
Proof
  ntac 2 gen_tac >> Induct >> rw[] >> rw[] >>
  imp_res_tac proves_term_ok >> fs[hypset_ok_cons] >>
  Cases_on`EXISTS (ACONV h) h''` >- (
    `∃h0 hr. (h'' = h0::hr) ∧ ACONV h h0` by (
      Cases_on`h''`>>fs[]>-metis_tac[ACONV_SYM]>>
      fs[EXISTS_MEM] >>
      `alpha_lt h''' e'` by (
        fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] ) >>
      `alpha_lt h e` by (
        fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] ) >>
      `alpha_lt e e'` by metis_tac[alpha_lt_trans_ACONV,ACONV_SYM] >>
      `alpha_lt h e'` by metis_tac[transitive_alpha_lt,relationTheory.transitive_def] >>
      fs[alpha_lt_def,ACONV_eq_orda] ) >>
    rw[] >>
    qspecl_then[`thy`,`h1++h0::hr`,`c`,`h`]mp_tac addAssum >>
    imp_res_tac WELLTYPED_LEMMA >> simp[] >>
    qspecl_then[`h1`,`h`,`h0`,`hr`]mp_tac term_union_replace >>
    impl_tac >- (
      simp[EVERY_MEM,MEM_EL,PULL_EXISTS] >>
      rpt(qpat_x_assum`EVERY P (X::Y)`kall_tac) >>
      rw[] >>
      fs[hypset_ok_el_less] >- (
        first_x_assum(qspecl_then[`n`,`LENGTH h1`]mp_tac) >>
        simp rws >>
        metis_tac[alpha_lt_trans_ACONV,ACONV_SYM]) >>
      first_x_assum(qspecl_then[`LENGTH h1`,`LENGTH h1 + SUC n`]mp_tac) >>
      simp rws >>
      metis_tac[alpha_lt_trans_ACONV,ACONV_SYM]) >>
    disch_then SUBST1_TAC >> strip_tac >>
    first_x_assum(qspecl_then[`h1++[h]`,`hr`]mp_tac) >>
    impl_tac >- (
      conj_tac >- metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] >>
      conj_tac >- (
        imp_res_tac proves_term_ok >> fs[] >>
        metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
      qpat_x_assum`EVERY P1 X`kall_tac >>
      qmatch_assum_abbrev_tac`EVERY P (h0::hr)` >>
      qpat_x_assum`EXISTS X (h0::hr)`kall_tac >>
      fs[EVERY_MEM] >> rw[] >>
      `P x` by res_tac >> pop_assum mp_tac >>
      qpat_x_assum`P h0`kall_tac >>
      simp_tac std_ss [Abbr`P`] >>
      strip_tac >>
      fs[hypset_ok_el_less,MEM_EL,PULL_EXISTS] >>
      first_x_assum(qspecl_then[`LENGTH h1`,`LENGTH h1 + SUC n`]mp_tac) >>
      simp rws >> strip_tac >>
      `ACONV h0 x` by metis_tac[ACONV_TRANS,ACONV_SYM] >>
      rfs[ACONV_eq_orda,alpha_lt_def] ) >>
    metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
  qspecl_then[`thy`,`h1++h''`,`c`,`h`]mp_tac addAssum >>
  imp_res_tac WELLTYPED_LEMMA >> simp[] >>
  qspecl_then[`h1`,`h`,`h''`]mp_tac term_union_insert >>
  impl_tac >- (
    fs[EVERY_MEM,EXISTS_MEM] >>
    conj_tac >- (
      rw[] >>
      qpat_x_assum`hypset_ok (h1 ++ h::h')`mp_tac >>
      simp[hypset_ok_el_less,MEM_EL,PULL_EXISTS] >>
      fs[MEM_EL,PULL_EXISTS] >>
      disch_then(qspecl_then[`n`,`LENGTH h1`]mp_tac) >>
      simp rws ) >>
    rw[] >>
    last_x_assum(qspec_then`z`mp_tac) >> simp[] >>
    strip_tac >- metis_tac[ACONV_SYM] >>
    fs[hypset_ok_append,hypset_ok_cons,EVERY_MEM] >> rw[] >> fs[] >>
    metis_tac[ACONV_SYM,alpha_lt_trans_ACONV] ) >>
  disch_then SUBST1_TAC >> strip_tac >>
  first_x_assum(qspecl_then[`h1++[h]`,`h''`]mp_tac) >>
  impl_tac >- (
    conj_tac >- metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] >>
    conj_tac >- (
      imp_res_tac proves_term_ok >> fs[] >>
      metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC] ) >>
    qpat_x_assum`EVERY P1 X`kall_tac >>
    qpat_x_assum`EVERY P1 X`kall_tac >>
    fs[EVERY_MEM,EXISTS_MEM] >>
    metis_tac[ACONV_SYM] ) >>
  metis_tac[rich_listTheory.CONS_APPEND,APPEND_ASSOC]
QED

Theorem proves_ACONV:
   ∀thy h' c' h c.
      (thy,h) |- c ∧ welltyped c' ∧ ACONV c c' ∧
      hypset_ok h' ∧
      EVERY (λx. EXISTS (ACONV x) h') h ∧
      EVERY (λx. term_ok (sigof thy) x ∧ x has_type Bool) h'
      ⇒ (thy,h') |- c'
Proof
  rw[] >>
  qsuff_tac`(thy,h') |- c` >- metis_tac[proves_concl_ACONV] >>
  qpat_x_assum`welltyped c'`kall_tac >>
  qpat_x_assum`ACONV c c'`kall_tac >>
  metis_tac[proves_ACONV_lemma,APPEND]
QED

(* more derived rules *)

Theorem sym_equation:
   ∀thyh p q. thyh |- p === q ⇒ thyh |- q === p
Proof
  rpt strip_tac >>
  imp_res_tac proves_theory_ok >>
  imp_res_tac proves_term_ok >>
  imp_res_tac theory_ok_sig >>
  `(FST thyh,[]) |- p === p` by (
    match_mp_tac refl_equation >> simp[] >>
    fs[term_ok_equation]) >>
  `(FST thyh,[]) |- Equal (typeof p) === Equal (typeof p)` by (
    match_mp_tac refl_equation >> simp[term_ok_clauses] >>
    fs[term_ok_equation] >>
    metis_tac[term_ok_type_ok] ) >>
  qspecl_then[`[]`,`SND thyh`,`Equal (typeof p)`,`p`]mp_tac appThm_equation >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >> simp[] >>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  simp[] >> impl_keep_tac
    >- fs[term_ok_equation,EQUATION_HAS_TYPE_BOOL] >>
  simp[term_union_thm] >>
  strip_tac >> mp_tac appThm_equation >>
  Cases_on`thyh`>>
  disch_then(fn th => first_x_assum(mp_tac o MATCH_MP th)) >>
  full_simp_tac std_ss [] >>
  disch_then(fn th => first_assum(mp_tac o MATCH_MP th)) >>
  fs[term_ok_equation] >>
  simp[GSYM equation_def,term_union_thm] >>
  qpat_x_assum`typeof _ = typeof _`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  metis_tac[eqMp_equation,term_union_thm,ACONV_REFL]
QED

Theorem sym:
   ∀thyh p q ty.
      thyh |- Comb (Comb (Equal ty) p) q ⇒
      thyh |- Comb (Comb (Equal ty) q) p
Proof
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  metis_tac[equation_def,sym_equation]
QED

Theorem trans_equation:
   ∀thy h1 h2 t1 t2a t2b t3.
      (thy,h2) |- t2b === t3 ⇒
      (thy,h1) |- t1 === t2a ⇒
      ACONV t2a t2b ⇒
      (thy,term_union h1 h2) |- t1 === t3
Proof
  rw[] >>
  imp_res_tac proves_theory_ok >> fs[] >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac proves_term_ok >>
  rfs[term_ok_equation] >>
  qspecl_then[`Comb (Equal (typeof t3)) t3`,`thy`]mp_tac refl_equation >>
  simp[term_ok_clauses] >>
  impl_tac >- metis_tac[term_ok_type_ok,term_ok_welltyped] >>
  disch_then(mp_tac o MATCH_MP appThm_equation) >>
  disch_then(qspecl_then[`h1`,`t2a`,`t1`]mp_tac) >>
  impl_tac >- metis_tac[sym_equation] >>
  fs[EQUATION_HAS_TYPE_BOOL] >>
  imp_res_tac ACONV_TYPE >> rfs[] >>
  qpat_x_assum`typeof t3 = X`(assume_tac o SYM) >>
  simp[GSYM equation_def] >>
  disch_then(mp_tac o MATCH_MP eqMp_equation) >>
  disch_then(qspecl_then[`h2`,`t3 === t2b`]mp_tac) >>
  simp[term_union_thm] >>
  impl_tac >- metis_tac[sym_equation] >>
  impl_tac >- (
    simp[ACONV_def,RACONV,equation_def] >>
    simp[GSYM ACONV_def] ) >>
  metis_tac[sym_equation]
QED

Theorem trans:
   ∀thy h1 h2 t1 t2a t2b t3 ty.
      (thy,h2) |- Comb (Comb (Equal ty) t2b) t3 ⇒
      (thy,h1) |- Comb (Comb (Equal ty) t1) t2a ⇒
      ACONV t2a t2b ⇒
      (thy,term_union h1 h2) |- Comb (Comb (Equal ty) t1) t3
Proof
  rw[] >>
  imp_res_tac proves_term_ok >> fs[] >>
  imp_res_tac term_ok_welltyped >> fs[] >>
  metis_tac[trans_equation,equation_def]
QED

Theorem proveHyp:
   ∀thy h1 c1 h2 c2. (thy,h1) |- c1 ∧ (thy,h2) |- c2 ⇒
      (thy,term_union h2 (term_remove c2 h1)) |- c1
Proof
  rw[] >>
  imp_res_tac proves_term_ok >>
  imp_res_tac proves_theory_ok >> fs[] >>
  qspecl_then[`c2`,`c1`,`h2`,`h1`,`thy`]mp_tac deductAntisym_equation >>
  simp[] >> strip_tac >>
  qmatch_assum_abbrev_tac`(thy,h3) |- c2 === c1` >>
  qspecl_then[`h3`,`h2`,`c2`,`c2`,`c1`,`thy`]mp_tac eqMp_equation >>
  simp[] >>
  strip_tac >>
  match_mp_tac proves_ACONV >>
  first_assum(match_exists_tac o concl) >>
  simp[] >>
  conj_tac >- metis_tac[welltyped_def] >>
  unabbrev_all_tac >>
  simp[EVERY_MEM,EXISTS_MEM] >>
  conj_tac >> gen_tac >>
  disch_then(mp_tac o MATCH_MP MEM_term_union_imp) >>
  strip_tac >>
  TRY(pop_assum(mp_tac o MATCH_MP MEM_term_union_imp)) >>
  TRY strip_tac >>
  imp_res_tac MEM_term_remove_imp >>
  TRY(fs[EVERY_MEM]>>NO_TAC) >>
  metis_tac[MEM_term_union,hypset_ok_term_union,hypset_ok_term_remove,ACONV_REFL]
QED

(* dependency relation *)

Theorem DEPENDENCY_IMP1:
  !x y ctxt. dependency ctxt x y ==> MEM (x,y) (dependency_compute ctxt)
Proof
  rw[dependency_cases,dependency_compute_def]
  >> rw[MEM_FLAT,MEM_MAP,PULL_EXISTS]
  >> asm_exists_tac
  >> rw[MEM_FLAT,MEM_MAP]
  >> rw[PULL_EXISTS]
  >> asm_exists_tac
  >> rw[MEM_MAP]
  >> fs[GSYM (SPEC ``cdefn:term`` WELLFORMED_COMPUTE_EQUIV),welltyped_def]
  >> rw[WELLTYPED_LEMMA]
QED

Theorem DEPENDENCY_IMP2:
  !x y ctxt. MEM (x,y) (dependency_compute ctxt) ==> dependency ctxt x y
Proof
  rw[dependency_cases,dependency_compute_def,theory_ok_def]
  >> fs[MEM_MAP,MEM_FLAT]
  >> rveq
  >> PURE_FULL_CASE_TAC
  >> fs[MEM_MAP,MEM_FLAT]
  (* 4 subgoals *)
  >- (
    rveq
    >> pairarg_tac
    >> fs[]
    >> Cases_on `wellformed_compute t'`
    >- (
      fs[COND_RAND,MEM_MAP]
      >> TRY DISJ1_TAC
      >> fs[GSYM (SPEC ``cdefn:term`` WELLFORMED_COMPUTE_EQUIV),WELLTYPED]
      >> TRY asm_exists_tac
      >> EXISTS_TAC ``t':term``
      >> rw[]
    )
    >> fs[GSYM (SPEC ``t':term`` WELLFORMED_COMPUTE_EQUIV),WELLTYPED]
  )
  >- (
    EXISTS_TAC ``t:term``
    >> EXISTS_TAC ``m0:mlstring``
    >> EXISTS_TAC ``m1:mlstring``
    >> rw[]
  )
  >- (
    EXISTS_TAC ``t:term``
    >> EXISTS_TAC ``m0:mlstring``
    >> EXISTS_TAC ``m1:mlstring``
    >> rw[]
  )
  >> fs[COND_RAND,MEM_MAP]
QED

Theorem DEPENDENCY_EQUIV:
  !x y ctxt. MEM (x,y) (dependency_compute ctxt) = dependency ctxt x y
Proof
  rpt GEN_TAC >> EQ_TAC >> rw[DEPENDENCY_IMP1,DEPENDENCY_IMP2]
QED

(* extension is transitive *)

Theorem extends_trans:
   ∀c1 c2 c3. c1 extends c2 ∧ c2 extends c3 ⇒ c1 extends c3
Proof
  rw[extends_def] >> metis_tac[RTC_TRANSITIVE,transitive_def]
QED

(* extensions have all distinct names *)

Theorem updates_ALL_DISTINCT:
   ∀upd ctxt. upd updates ctxt ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (type_list (upd::ctxt)))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (const_list (upd::ctxt))))
Proof
  cheat
  (* ho_match_mp_tac updates_ind >> simp[] >>
  rw[ALL_DISTINCT_APPEND,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] *)
QED

Theorem extends_ALL_DISTINCT:
   ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (type_list ctxt2))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (const_list ctxt2)))
Proof
  simp[IMP_CONJ_THM,FORALL_AND_THM] >> conj_tac >>
  ho_match_mp_tac extends_ind >>
  METIS_TAC[updates_ALL_DISTINCT]
QED

Theorem init_ALL_DISTINCT:
   ALL_DISTINCT (MAP FST (const_list init_ctxt)) ∧
    ALL_DISTINCT (MAP FST (type_list init_ctxt))
Proof
  EVAL_TAC
QED

Theorem updates_DISJOINT:
   ∀upd ctxt.
    upd updates ctxt ⇒
    DISJOINT (FDOM (alist_to_fmap (consts_of_upd upd))) (FDOM (tmsof ctxt)) ∧
    DISJOINT (FDOM (alist_to_fmap (types_of_upd upd))) (FDOM (tysof ctxt))
Proof
  cheat
  (* ho_match_mp_tac updates_ind >>
  simp[IN_DISJOINT] >> rw[] >>
  simp[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
  PROVE_TAC[]*)
QED

Theorem updates_upd_ALL_DISTINCT:
   ∀upd ctxt. upd updates ctxt ⇒
      ALL_DISTINCT (MAP FST (consts_of_upd upd)) ∧
      ALL_DISTINCT (MAP FST (types_of_upd upd))
Proof
  cheat
  (* ho_match_mp_tac updates_ind >> rw[] >>
  rw[MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX]*)
QED

Theorem updates_upd_DISJOINT:
   ∀upd ctxt. upd updates ctxt ⇒
      DISJOINT (set (MAP FST (types_of_upd upd))) (set (MAP FST (type_list ctxt))) ∧
      DISJOINT (set (MAP FST (consts_of_upd upd))) (set (MAP FST (const_list ctxt)))
Proof
  cheat
  (*ho_match_mp_tac updates_ind >> rw[IN_DISJOINT,MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS,LET_THM] >>
  metis_tac[]*)
QED

(* signature extensions preserve ok *)

Theorem type_ok_extend:
   ∀t tyenv tyenv'.
    tyenv ⊑ tyenv' ∧
    type_ok tyenv t ⇒
    type_ok tyenv' t
Proof
  ho_match_mp_tac type_ind >>
  rw[type_ok_def,EVERY_MEM] >>
  res_tac >>
  imp_res_tac FLOOKUP_SUBMAP
QED

Theorem term_ok_extend:
   ∀t tyenv tmenv tyenv' tmenv'.
    tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
    term_ok (tyenv,tmenv) t ⇒
    term_ok (tyenv',tmenv') t
Proof
  Induct >> simp[term_ok_def] >> rw[] >>
  imp_res_tac type_ok_extend >>
  imp_res_tac FLOOKUP_SUBMAP >>
  metis_tac[]
QED

Theorem term_ok_updates:
   ∀upd ctxt. upd updates ctxt ⇒
      term_ok (sigof (thyof ctxt)) tm ⇒
      term_ok (sigof (thyof (upd::ctxt))) tm
Proof
  rw[] >> match_mp_tac term_ok_extend >>
  map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
  simp[] >> conj_tac >> match_mp_tac finite_mapTheory.SUBMAP_FUNION >>
  metis_tac[updates_DISJOINT,finite_mapTheory.SUBMAP_REFL,pred_setTheory.DISJOINT_SYM]
QED

Theorem is_std_sig_extend:
   ∀tyenv tmenv tyenv' tmenv'.
    is_std_sig (tyenv,tmenv) ∧ tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ⇒
    is_std_sig (tyenv',tmenv')
Proof
  rw[is_std_sig_def] >> imp_res_tac FLOOKUP_SUBMAP
QED

(* updates preserve ok *)

Theorem updates_theory_ok:
   ∀upd ctxt. upd updates ctxt ⇒ theory_ok (thyof ctxt) ⇒ theory_ok (thyof (upd::ctxt))
Proof
  cheat
  (*ho_match_mp_tac updates_ind >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    metis_tac[] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    conj_tac >- metis_tac[IN_FRANGE_DOMSUB_suff] >>
    `tmsof ctxt ⊑ tmsof ctxt |+ (name,ty)` by simp[] >>
    metis_tac[is_std_sig_extend,term_ok_extend,SUBMAP_REFL] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    imp_res_tac proves_term_ok >>
    fs[theory_ok_def,EVERY_MAP] >>
    rfs[term_ok_equation,UNCURRY,EQUATION_HAS_TYPE_BOOL] >>
    Q.PAT_ABBREV_TAC`tms' = X ⊌ tmsof ctxt` >>
    `tmsof ctxt ⊑ tms'` by (
      simp[Abbr`tms'`] >>
      match_mp_tac SUBMAP_FUNION >>
      fs[IN_DISJOINT,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX] >>
      metis_tac[] ) >>
    conj_tac >- (
      simp[Abbr`tms'`] >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >> fs[] >>
      ho_match_mp_tac IN_FRANGE_alist_to_fmap_suff >>
      fs[EVERY_MEM,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,MEM_MAP,PULL_EXISTS] >>
      fs[term_ok_def] ) >>
    reverse conj_tac >- metis_tac[is_std_sig_extend,SUBMAP_REFL] >>
    gen_tac >> reverse strip_tac >- metis_tac[term_ok_extend,SUBMAP_REFL] >>
    simp[] >>
    conj_tac >- (
      match_mp_tac term_ok_VSUBST >>
      simp[MEM_MAP,PULL_EXISTS,UNCURRY,Once has_type_cases,term_ok_def] >>
      conj_tac >- metis_tac[term_ok_extend,SUBMAP_REFL] >>
      simp[Abbr`tms'`,FLOOKUP_FUNION,ALOOKUP_MAP,FORALL_PROD] >> rw[] >>
      imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> rw[] >>
      fs[EVERY_MEM,term_ok_def,FORALL_PROD] >>
      metis_tac[is_instance_refl] ) >>
    match_mp_tac VSUBST_HAS_TYPE >>
    simp[MEM_MAP,PULL_EXISTS,UNCURRY,Once has_type_cases] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    `tysof ctxt ⊑ tysof ctxt |+ (name,arity)` by simp[] >>
    metis_tac[is_std_sig_extend,term_ok_extend,type_ok_extend,SUBMAP_REFL] ) >>
  srw_tac[][conexts_of_upd_def] >>
  fs[theory_ok_def] >>
  Q.PAT_ABBREV_TAC`tms' = X ⊌ tmsof ctxt` >>
  Q.PAT_ABBREV_TAC`tys' = tysof ctxt |+ X` >>
  `tmsof ctxt ⊑ tms'` by (
    simp[Abbr`tms'`] >>
    match_mp_tac SUBMAP_FUNION >>
    fs[IN_DISJOINT] >>
    metis_tac[] ) >>
  `tysof ctxt ⊑ tys'` by (
    simp[Abbr`tys'`] ) >>
  `is_std_sig (tys',tms')` by metis_tac[is_std_sig_extend] >>
  imp_res_tac proves_term_ok >> fs[term_ok_def] >>
  imp_res_tac term_ok_type_ok >>
  conj_tac >- (
    simp[Abbr`tms'`] >>
    ho_match_mp_tac IN_FRANGE_FUNION_suff >>
    reverse conj_tac >- metis_tac[type_ok_extend] >>
    ho_match_mp_tac IN_FRANGE_FUPDATE_suff >>
    simp[type_ok_def] >>
    fs[is_std_sig_def] >>
    imp_res_tac WELLTYPED_LEMMA >>
    unabbrev_all_tac >>
    simp[type_ok_def,FLOOKUP_UPDATE,EVERY_MAP] >>
    metis_tac[type_ok_extend,term_ok_type_ok] ) >>
  simp[] >>
  imp_res_tac WELLTYPED_LEMMA >>
  `name ∉ {strlit "fun";strlit "bool"}` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  pop_assum mp_tac >> simp[] >> strip_tac >>
  Q.PAT_ABBREV_TAC`eq1 = l1 === r1` >>
  Q.PAT_ABBREV_TAC`eq2 = l2 === r` >>
  Q.PAT_ABBREV_TAC`eq3 = l3 === r3` >>
  qpat_x_assum`X has_type Y`mp_tac >>
  simp[Once has_type_cases] >> strip_tac >> rfs[] >>
  `type_ok tys' rep_type` by (
    match_mp_tac type_ok_extend >>
    HINT_EXISTS_TAC >> fs[Abbr`rep_type`] ) >>
  `term_ok (tys',tms') eq1` by (
    unabbrev_all_tac >>
    simp[term_ok_equation,term_ok_def,type_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE,EVERY_MAP] >>
    rfs[is_std_sig_def] ) >>
  `term_ok (tys',tms') pred` by metis_tac[term_ok_extend] >>
  `eq1 has_type Bool` by (
    unabbrev_all_tac >> simp[EQUATION_HAS_TYPE_BOOL] ) >>
  `eq2 has_type Bool` by (
    unabbrev_all_tac >> simp[EQUATION_HAS_TYPE_BOOL] ) >>
  imp_res_tac WELLTYPED_LEMMA >>
  `eq3 has_type Bool` by (
    unabbrev_all_tac >> simp[EQUATION_HAS_TYPE_BOOL,welltyped_equation] ) >>
  `term_ok (tys',tms') eq3` by (
    unabbrev_all_tac >>
    simp[term_ok_equation,term_ok_def,type_ok_def,FLOOKUP_FUNION,FLOOKUP_UPDATE,EVERY_MAP] >>
    fs[is_std_sig_def] ) >>
  metis_tac[term_ok_extend] *)
QED

Theorem extends_theory_ok:
   ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ theory_ok (thyof ctxt1) ⇒ theory_ok (thyof ctxt2)
Proof
  ho_match_mp_tac extends_ind >> metis_tac[updates_theory_ok]
QED

(* init_ctxt ok *)

Theorem init_theory_ok:
   theory_ok (thyof init_ctxt)
Proof
  rw[theory_ok_def,init_ctxt_def,type_ok_def,FLOOKUP_UPDATE,conexts_of_upd_def] >>
  rw[is_std_sig_def,FLOOKUP_UPDATE]
QED

(* is_std_sig is preserved *)

Theorem is_std_sig_extends:
   ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ is_std_sig (sigof ctxt1) ⇒ is_std_sig (sigof ctxt2)
Proof
  cheat
  (* ho_match_mp_tac extends_ind >>
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac updates_ind >>
  srw_tac[][is_std_sig_def,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  TRY BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[] *)
QED

(* init_ctxt well-formed *)

Theorem init_ctxt_wf:
  wf_ctxt init_ctxt
Proof
  simp[wf_ctxt_def]
  \\ conj_tac
  >- rw[init_ctxt_def,orth_ctxt_def]
  >- (rw[terminating_def,init_ctxt_def,orth_ctxt_def]
      >> qexists_tac `SUC 0` >> PURE_REWRITE_TAC[NRC]
      >> rw[]
      >> Cases_on `x` >> Cases_on `y` >> Cases_on `z`
      >> rw[subst_clos_def,dependency_cases])
QED

(* Properties of dependency and orthogonality  *)
Theorem dependency_simps:
  dependency (NewAxiom prop::ctxt) = dependency ctxt
    /\ dependency (NewType name arity::ctxt) = dependency ctxt
Proof
  rpt conj_tac
  >> qmatch_goalsub_abbrev_tac `a1 = a2`
  >> `!x y. a1 x y = a2 x y` suffices_by metis_tac[]
  >> unabbrev_all_tac
  >- (rw[dependency_cases])
  >- (rw[dependency_cases])
QED

Theorem orth_ctxt_simps[simp]:
  orth_ctxt (NewAxiom prop::ctxt) = orth_ctxt ctxt
   /\ orth_ctxt (NewConst name ty::ctxt) = orth_ctxt ctxt
   /\ orth_ctxt (NewType name arity::ctxt) = orth_ctxt ctxt
Proof
  rpt conj_tac
  >- (rw[orth_ctxt_def])
  >- (rw[orth_ctxt_def])
  >- (rw[orth_ctxt_def])
QED

(* list_subset properties *)

(* l1 is subset of l2 *)
Theorem list_subset_NIL:
  !l. list_subset [] l
Proof
  rw[list_subset_def,EVERY_DEF]
QED

Theorem list_subset_SING:
  !x y. list_subset [x] [y] = (x = y)
Proof
  rw[list_subset_def]
QED

Theorem list_subset_IDENT:
  !l. list_subset l l
Proof
  Induct >> rw[list_subset_def,EVERY_MEM]
QED

Theorem list_subset_SIMP:
  !l2 l1 l3. list_subset l2 (l1++l2++l3)
Proof
  Induct
  >- rw[list_subset_NIL]
  >> strip_tac
  >> rw[list_subset_def,EVERY_MEM]
QED

Theorem list_subset_MEM:
  !l x. list_subset [x] l ==> MEM x l
Proof
  rw[list_subset_def]
QED

Theorem list_subset_NIL2:
  !l. list_subset l [] = NULL l
Proof
  rw[list_subset_def,NULL_EQ]
QED

Theorem list_subset_NOT_NIL:
  !l1 l2. (list_subset l1 l2) /\ (NULL l2) ==> NULL l1
Proof
  Induct
  >- rw[list_subset_def]
  >> strip_tac
  >> Cases
  >- rw[list_subset_NIL2]
  >> rw[NULL_EQ]
QED

Theorem list_subset_set:
  !x y. list_subset x y = (set (x)  ⊆ set(y))
Proof
  Induct
  >- fs[list_subset_NIL,NULL_EQ]
  >> fs[list_subset_def]
QED

Theorem list_inter_mono[local]:
  !l r P Q.
    (!a. MEM a (P r) ==> MEM a (Q r))
    /\ (!a. MEM a (P l) ==> MEM a (Q l))
    /\ NULL (list_inter (Q l) (Q r)) ==> NULL (list_inter (P l) (P r))
Proof
  rw[list_inter_def,NULL_FILTER]
  >> rpt (first_x_assum (qspecl_then [`y`] mp_tac))
  >> rw[] >> fs[]
QED

Theorem list_inter_map[local]:
  !l r f. NULL (list_inter (MAP f l) (MAP f r)) ==> NULL (list_inter l r)
Proof
  rw[list_inter_def,NULL_FILTER]
  >> `MEM (f y) (MAP f r)` by (rw[MEM_MAP] >> metis_tac[])
  >> first_x_assum drule
  >> rw[MEM_MAP]
  >> first_x_assum (qspecl_then [`y`] mp_tac)
  >> rw[]
QED

Theorem NULL_list_inter_tyvars_Tyapp[local]:
  !a ty l. NULL (list_inter (tyvars (Tyapp a ty)) l)
    ==> EVERY (λx. NULL (list_inter x l)) (MAP tyvars ty)
Proof
  rpt strip_tac
  >> fs[list_inter_def,EVERY_MEM,NULL_FILTER,tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP]
  >> rw[]
  >> first_x_assum (qspecl_then [`y'`] mp_tac)
  >> rw[]
  >> first_x_assum (qspecl_then [`y`] mp_tac)
  >> rw[]
QED

Theorem list_inter_map_inj[local]:
  !l r f.  (!x y. (f x = f y) = (x = y)) /\ NULL (list_inter l r)
  ==> NULL (list_inter (MAP f l) (MAP f r))
Proof
  rw[list_inter_def,NULL_FILTER,MEM_MAP]
  >> Cases_on `y' <> y''`
  >> rw[]
  >> first_x_assum match_mp_tac
  >> fs[]
QED

Theorem list_inter_distinct_prop:
  !l r f. (!x. MEM x l ==> f x) /\ (!x. MEM x r ==> ~f x)
  ==> NULL (list_inter l r)
Proof
  rw[list_inter_def]
  >> Induct_on `r`
  >- fs[]
  >> rw[MEM]
  >> qexists_tac `h`
  >> rw[]
QED

Theorem list_inter_heads[local]:
  !x y xs ys. NULL(list_inter (x::xs) (y::ys)) ==> x <> y
Proof
  fs[list_inter_def]
QED

Theorem list_inter_tails[local]:
  !x y xs ys. NULL(list_inter (x::xs) (y::ys)) ==> NULL(list_inter xs ys)
Proof
  rw[list_inter_def,NULL_FILTER]
QED

Theorem list_inter_elem[local]:
  !xs1 x xs2 ys1 y ys2. NULL(list_inter (xs1++[x]++xs2) (ys1++[y]++ys2)) ==> x <> y
Proof
  rpt strip_tac
  >> fs[NULL_FILTER,list_inter_def]
  >> first_x_assum (qspecl_then [`y`] mp_tac)
  >> fs[]
QED

Theorem list_inter_subset[local]:
  !ls xs ys. (!x. MEM x xs ==> MEM x ls)
  /\ NULL (list_inter ls ys) ==> NULL (list_inter xs ys)
Proof
  rw[list_inter_def,NULL_FILTER]
  >> rpt (first_x_assum (qspecl_then [`y`] assume_tac))
  >> rfs[]
QED

Theorem list_inter_set_symm[local]:
  !xs ys. set (list_inter xs ys) = set (list_inter ys xs)
Proof
  rw[list_inter_def,LIST_TO_SET_FILTER,INTER_COMM]
QED

Theorem list_inter_set[local]:
  !xs ys. set(list_inter xs ys) = ((set xs) ∩ (set ys))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >> fs[INSERT_DEF,list_inter_def,INTER_DEF,LIST_TO_SET,LEFT_AND_OVER_OR]
  >> rw[SET_EQ_SUBSET,SUBSET_DEF]
  >> fs[]
QED

Theorem list_inter_NULL_symm[local]:
  !xs ys. NULL (list_inter xs ys) = NULL (list_inter ys xs)
Proof
  metis_tac[NULL_EQ,list_inter_set_symm,LIST_TO_SET_EQ_EMPTY]
QED

Theorem list_inter_subset_outer[local]:
  !x1 x2 x3 y1 y2 y3. NULL (list_inter (x1 ++ x2 ++x3) (y1 ++ y2 ++ y3))
    ==> NULL (list_inter (x1 ++ x3) (y1 ++ y3))
Proof
  rpt gen_tac
  >> `!x. MEM x (x1++x3) ==> MEM x (x1 ++ x2 ++ x3)` by (rw[] >> fs[])
  >> `!x. MEM x (y1++y3) ==> MEM x (y1 ++ y2 ++ y3)` by (rw[] >> fs[])
  >> metis_tac[list_inter_NULL_symm,list_inter_subset]
QED

Theorem list_inter_subset_inner[local]:
  !x1 x2 x3 y1 y2 y3. NULL (list_inter (x1 ++ x2 ++x3) (y1 ++ y2 ++ y3))
    ==> NULL (list_inter x2 y2)
Proof
  rpt gen_tac
  >> `!x. MEM x x2 ==> MEM x (x1 ++ x2 ++ x3)` by rw[]
  >> `!x. MEM x y2 ==> MEM x (y1 ++ y2 ++ y3)` by rw[]
  >> metis_tac[list_inter_NULL_symm,list_inter_subset]
QED

Theorem NULL_list_inter_APPEND1[local]:
  !x1 y1 y2. NULL (list_inter x1 (y1++y2))
  = (NULL (list_inter x1 y1) /\ NULL (list_inter x1 y2))
Proof
  rw[list_inter_def,FILTER_APPEND]
QED

Theorem NULL_list_inter_APPEND[local]:
  !x1 x2 y1 y2. NULL (list_inter (x1++x2) (y1++y2)) = (NULL (list_inter x1 y1)
  /\ NULL (list_inter x1 y2) /\ NULL (list_inter x2 y1) /\ NULL (list_inter x2 y2))
Proof
  rw[NULL_list_inter_APPEND1,list_inter_NULL_symm,AC CONJ_ASSOC CONJ_COMM]
QED

Theorem NULL_list_inter_SING[local]:
  !l x. NULL (list_inter [x] l) = ~MEM x l
Proof
  rw[NULL_FILTER,list_inter_def]
QED

Theorem list_max_MEM[local]:
  !l x. (MEM x l) ==> (x <= list_max l)
Proof
  Induct
  >> rw[list_max_def]
  >> fs[list_max_def]
  >> last_x_assum drule
  >> simp[]
QED

Theorem list_max_APPEND[local]:
  !l x y. list_max l <= list_max (x ++ l ++ y)
Proof
  Induct
  >- rw[list_max_def]
  >> rw[list_max_def]
  >- (
    match_mp_tac list_max_MEM
    >> fs[]
  )
  >> first_x_assum (qspecl_then [`x ++ [h]`,`y`] mp_tac)
  >> `h::l = [h] ⧺ l` by rw[]
  >> asm_rewrite_tac[]
  >> fs[]
QED

Definition renaming_def:
  renaming = EVERY (λ(x,y). (?m n. (x = Tyvar m) /\ (y = Tyvar n)))
End

Theorem renaming_simp[local]:
  !h l. renaming (h::l) = (renaming [h] /\ renaming l)
Proof
  rw[EVERY_DEF,renaming_def]
QED

Definition non_triv_renaming_def:
  non_triv_renaming s = (renaming s /\ EVERY (λ(x,y). x <> y) s /\ ALL_DISTINCT (MAP SND s))
End

Theorem type_size[local]:
  !sigma ty. renaming sigma
  ==> type_size' (TYPE_SUBST sigma ty) = type_size' ty
Proof
  ho_match_mp_tac TYPE_SUBST_ind
  >> ONCE_REWRITE_TAC[renaming_def]
  >> strip_tac
  >- (
    Induct
    >- rw[TYPE_SUBST_NIL]
    >> Cases
    >> fs[TYPE_SUBST_def]
    >> rw[REV_ASSOCD_def,type_size'_def]
    >> rw[type_size'_def]
  )
  >> Induct
  >- rw[TYPE_SUBST_NIL]
  >> Cases
  >> fs[TYPE_SUBST_def]
  >> rw[TYPE_SUBST_def,type_size'_def,type1_size'_SUM_MAP,MAP_MAP_o,o_DEF]
  >> Induct_on `tys`
  >- rw[TYPE_SUBST_NIL]
  >> Cases
  >> rw[TYPE_SUBST_def,MAP]
  >> rw[TYPE_SUBST_def,MAP]
QED

Definition normalise_tyvars_subst_def:
  (normalise_tyvars_subst (Tyvar v) n n0 subst chr=
    let
      varname = λn. Tyvar (strlit(REPLICATE n chr))
    in if strlen v < n0 /\ ~MEM (Tyvar v) (MAP SND subst)
       then (SUC n, (varname n, Tyvar v)::subst)
       else (n, subst)
  )
  /\ (normalise_tyvars_subst (Tyapp v tys) n n0 subst chr =
    FOLDL (λ(n,subst) ty. normalise_tyvars_subst ty n n0 subst chr) (n, subst) tys)
Termination
  WF_REL_TAC `measure (type_size' o FST)`
  >> rw[type_size'_def,type1_size'_mem]
End

Definition normalise_tyvars_rec_def:
  normalise_tyvars_rec ty chr =
    (let n0 = SUC (list_max (MAP $strlen (tyvars ty))) in
    let subst = SND (normalise_tyvars_subst ty n0 n0 [] chr)
    in (TYPE_SUBST subst ty, subst))
End

Theorem distinct_varnames[local]:
  !ty chr n n0. n > n0 /\ n0 = list_max (MAP $strlen (tyvars ty))
  ==> ~MEM (strlit (REPLICATE n chr)) (tyvars ty)
Proof
  rpt strip_tac
  >> rw[tyvars_def]
  >> ASSUME_TAC (Q.SPECL [`(MAP $strlen (tyvars ty))`] list_max_max)
  >> fs[EVERY_MEM]
  >> imp_res_tac (INST_TYPE [beta |-> ``:num``] (GSYM MEM_MAP))
  >> rw[]
  >> first_x_assum (qspecl_then [`strlen (strlit (REPLICATE n chr))`] mp_tac)
  >> fs[]
  >> qexists_tac `strlen`
  >> rw[strlen_def]
  >> CCONTR_TAC
  >> fs[]
  >> first_x_assum drule
  >> fs[]
QED

Theorem normalise_tyvars_subst_renames[local]:
  !ty subst n n0 chr. renaming subst ==> renaming (SND (normalise_tyvars_subst ty n n0 subst chr))
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- rw[renaming_def,normalise_tyvars_subst_def]
  >> Induct
  >- rw[renaming_def,normalise_tyvars_subst_def]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> rw[normalise_tyvars_subst_def]
  >> Q.ISPECL_THEN [`(renaming o SND):num#(type,type)alist->bool`,
    `(λ(n,subst) ty.normalise_tyvars_subst ty n n0 subst chr)`] assume_tac FOLDL_invariant
  >> fs[o_DEF,EVERY_MEM]
  >> first_x_assum match_mp_tac
  >> rw[ELIM_UNCURRY]
QED

Theorem normalise_tyvars_rec_renames[local]:
  !ty chr. renaming (SND (normalise_tyvars_rec ty chr))
Proof
  rw[normalise_tyvars_rec_def]
  >> mp_tac normalise_tyvars_subst_renames
  >> rw[renaming_def]
QED

Definition tyvars_constr_def:
  tyvars_constr n0 (n,subst) = ( n >= n0
    /\ EVERY
    (λ(x,y). ?a b. Tyvar a = x /\ Tyvar b = y /\ strlen a <= n /\ strlen a >= n0 /\ strlen b < n0)
    subst)
End

Theorem normalise_tyvars_subst_ineq:
  !ty n_subst n0 chr. tyvars_constr n0 n_subst
    ==> tyvars_constr n0 (normalise_tyvars_subst ty (FST n_subst) n0 (SND n_subst) chr)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    strip_tac
    >> Cases
    >> rw[normalise_tyvars_subst_def,tyvars_constr_def]
    >> irule EVERY_MONOTONIC
    >> qmatch_asmsub_abbrev_tac `EVERY P subst`
    >> qexists_tac `P`
    >> qunabbrev_tac `P`
    >> rw[ELIM_UNCURRY]
    >> qexists_tac `a`
    >> qexists_tac `b`
    >> rw[]
  )
  >> Induct
  >- rw[normalise_tyvars_subst_def,tyvars_constr_def]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> rw[normalise_tyvars_subst_def]
QED

Theorem normalise_tyvars_rec_ineq[local]:
  !ty chr. EVERY (λ(x,y). x <> y) (SND (normalise_tyvars_rec ty chr))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> (qspecl_then [`ty`,`(n0,[])`,`n0`,`chr`] assume_tac) normalise_tyvars_subst_ineq
  >> fs[tyvars_constr_def]
  >> qmatch_asmsub_abbrev_tac `norm:'a#'b`
  >> Cases_on `norm`
  >> pop_assum (assume_tac o GSYM o PURE_ONCE_REWRITE_RULE[markerTheory.Abbrev_def])
  >> fs[tyvars_constr_def,EVERY_MEM,ELIM_UNCURRY]
  >> rpt strip_tac
  >> first_x_assum (qspec_then `e` assume_tac)
  >> Cases_on `e`
  >> rfs[]
  >> rveq
  >> fs[]
QED

Theorem normalise_tyvars_rec_ineq2[local]:
  !ty chr. EVERY (λ(x,_). ?a. Tyvar a = x /\ strlen a > list_max(MAP strlen (tyvars ty))) (SND (normalise_tyvars_rec ty chr))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> (qspecl_then [`ty`,`(SUC n0,[])`,`SUC n0`,`chr`] assume_tac) normalise_tyvars_subst_ineq
  >> fs[tyvars_constr_def]
  >> qmatch_asmsub_abbrev_tac `norm:'a#'b`
  >> Cases_on `norm`
  >> fs[tyvars_constr_def,EVERY_MEM]
  >> unabbrev_all_tac
  >> rw[]
  >> first_x_assum drule
  >> rw[ELIM_UNCURRY]
  >> asm_exists_tac
  >> fs[]
QED

Theorem normalise_tyvars_subst_chr[local]:
  !ty n_subst n0 chr.
  let
    inv = λ(big_n,subst).
      EVERY (λ(x,_). ?n. x = Tyvar (strlit(REPLICATE n chr)) /\ n < big_n) subst;
    n_subst' = normalise_tyvars_subst ty (FST n_subst) n0 (SND n_subst) chr
  in inv n_subst ==> inv n_subst'
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    strip_tac
    >> Cases
    >> rw[normalise_tyvars_subst_def]
    >- (qexists_tac `q` >> fs[])
    >> last_x_assum mp_tac
    >> match_mp_tac (GEN_ALL MONO_EVERY)
    >> rw[ELIM_UNCURRY]
    >> asm_exists_tac
    >> fs[]
  )
  >> Induct
  >- rw[normalise_tyvars_subst_def]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> rw[normalise_tyvars_subst_def]
QED

Theorem normalise_tyvars_rec_chr:
  !ty chr.  let
    inv = λ(big_n,subst).
      EVERY (λ(x,_). ?n. (x = Tyvar (strlit(REPLICATE n chr)) /\ n < big_n)) subst;
  in ?n. inv (n,SND (normalise_tyvars_rec ty chr))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> (qspecl_then [`ty`,`(n0,[])`,`n0`,`chr`] assume_tac) normalise_tyvars_subst_chr
  >> fs[ELIM_UNCURRY]
  >> qmatch_goalsub_abbrev_tac `norm:(num#(type,type) alist)`
  >> asm_exists_tac
  >> fs[]
QED

Theorem normalise_tyvars_subst_distinct_fst[local]:
  !ty n_subst n0 chr.
  let
    inv = λ(big_n,subst). ALL_DISTINCT (MAP FST subst) /\ EVERY (λ(x,_). ?a n. x = Tyvar a /\ strlen a < big_n) subst;
    n_subst' = normalise_tyvars_subst ty (FST n_subst) n0 (SND n_subst) chr
  in inv n_subst ==> inv n_subst'
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    strip_tac
    >> Cases
    >> rw[ELIM_UNCURRY,normalise_tyvars_subst_def]
    >- (
      fs[EVERY_MEM,MEM_MAP]
      >> strip_tac
      >> qmatch_goalsub_abbrev_tac `_ \/ b`
      >> Cases_on `b` >> fs[]
      >> unabbrev_all_tac
      >> first_x_assum drule
      >> rw[]
      >> `!x y. strlen x <> strlen y ==> x <> y` by (rw[] >> CCONTR_TAC >> rw[])
      >> rw[]
    )
    >> qpat_x_assum `EVERY _ _` mp_tac
    >> match_mp_tac MONO_EVERY
    >> rw[]
    >> asm_exists_tac
    >> fs[]
  )
  >> Induct
  >- rw[normalise_tyvars_subst_def]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> rw[normalise_tyvars_subst_def]
QED

Theorem normalise_tyvars_rec_distinct_fst[local]:
  !ty chr. ALL_DISTINCT (MAP FST (SND (normalise_tyvars_rec ty chr)))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> (qspecl_then [`ty`,`(n0,[])`,`n0`,`chr`] assume_tac) normalise_tyvars_subst_distinct_fst
  >> qmatch_asmsub_abbrev_tac `norm:'a#'b`
  >> Cases_on `norm`
  >> fs[ELIM_UNCURRY]
  >> unabbrev_all_tac
  >> fs[]
QED

Theorem normalise_tyvars_rec_differ_FST_SND:
  (!r n0 n.
  (!x. MEM x r ==> ?a b. Tyvar a = FST x /\ Tyvar b = SND x /\ strlen a <= n /\ strlen a >= n0 /\ strlen b < n0)
  ==> (!x. MEM x (FLAT (MAP (tyvars o FST) r)) ==> strlen x >= n0))
  /\
  (!r n0 n.
  (!x. MEM x r ==> ?a b. Tyvar a = FST x /\ Tyvar b = SND x /\ strlen a <= n /\ strlen a >= n0 /\ strlen b < n0)
  ==> (!x. MEM x (FLAT (MAP (tyvars o SND) r)) ==> strlen x < n0))
Proof
  CONJ_TAC
  >> (
    Induct
    >- fs[]
    >> Cases
    >> rpt strip_tac
    >> fs[MAP]
    >- (
      fs[DISJ_IMP_THM]
      >> first_x_assum (qspecl_then [`(q,r')`] mp_tac)
      >> fs[] >> rw[]
      >> fs[tyvars_def,MEM]
    )
    >> fs[DISJ_IMP_THM]
    >> last_x_assum (qspecl_then [`n0`,`n`] assume_tac)
    >> fs[]
  )
QED

Theorem normalise_tyvars_rec_differ:
  !ty chr. let subst = SND (normalise_tyvars_rec ty chr)
    in NULL (list_inter (FLAT (MAP (tyvars o FST) subst)) (FLAT (MAP (tyvars o SND) subst)))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> `tyvars_constr n0 (n0,[])` by rw[tyvars_constr_def]
  >> imp_res_tac normalise_tyvars_subst_ineq
  >> first_x_assum (qspecl_then [`ty`,`chr`] assume_tac)
  >> qmatch_goalsub_abbrev_tac `n_subst:num#(type,type)alist`
  >> Cases_on `n_subst`
  >> fs[tyvars_constr_def,EVERY_MEM,ELIM_UNCURRY]
  >> imp_res_tac normalise_tyvars_rec_differ_FST_SND
  >> match_mp_tac list_inter_distinct_prop
  >> qexists_tac `λx. strlen x >= (n0:num)`
  >> rw[]
  >> first_x_assum drule
  >> fs[NOT_LESS_EQUAL]
QED

Theorem list_subset_tyvar:
  !ty a. MEM a (tyvars ty) ==> list_subset (tyvars (Tyvar a)) (tyvars ty)
Proof
  ho_match_mp_tac type_ind
  >> rw[list_subset_def,tyvars_def]
QED

(* All type variables within a substitution from normalise_tyvars_subst are
 * shorter than a certain number n *)
Theorem normalise_tyvars_subst_max[local]:
  !ty n_subst n0 chr.
    let max = λ(n,subst). ~NULL subst ==> n = (SUC o list_max o FLAT)  (MAP (MAP strlen o tyvars o FST) subst)
    in max n_subst
    ==>  max (normalise_tyvars_subst ty (FST n_subst) n0 (SND n_subst) chr)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rw[normalise_tyvars_subst_def,ELIM_UNCURRY]
    >> Cases_on `n_subst`
    >> Cases_on `r`
    >> fs[MAP,tyvars_def,list_max_def]
  )
  >> Induct
  >- rw[normalise_tyvars_subst_def,ELIM_UNCURRY]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> rw[normalise_tyvars_subst_def]
  >> match_mp_tac FOLDL_invariant
  >> strip_tac
  >> last_x_assum drule
  >> strip_tac
  >> first_x_assum (qspecl_then [`n0`,`chr`] mp_tac)
  >> NTAC 2 strip_tac
  >> fs[ELIM_UNCURRY]
  >> NTAC 3 strip_tac
  >> fs[EVERY_MEM]
QED

Theorem normalise_tyvars_subst_len_inv[local]:
  !ty n_subst n0 chr.
    let inv = λ(n,subst). (LENGTH subst) + n0 = n /\ ALL_DISTINCT (MAP SND subst)
    in inv n_subst
    ==>  inv (normalise_tyvars_subst ty (FST n_subst) n0 (SND n_subst) chr)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- rw[normalise_tyvars_subst_def,ELIM_UNCURRY]
  >> Induct
  >- rw[normalise_tyvars_subst_def]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> rw[normalise_tyvars_subst_def]
QED

Theorem normalise_tyvars_rec_subst_snd_distinct:
  !ty chr subst. ALL_DISTINCT (MAP SND (SND (normalise_tyvars_rec ty chr)))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> (qspecl_then [`ty`,`(n0,[])`,`n0`,`chr`] assume_tac) normalise_tyvars_subst_len_inv
  >> fs[ELIM_UNCURRY]
QED

(*
val normalise_tyvars_rec_len_inv = Q.prove(
  `!ty chr subst. subst = SND (normalise_tyvars_rec ty chr)
  ==> (LENGTH subst) = LENGTH (tyvars ty) /\ ALL_DISTINCT (MAP SND subst)`,
  NTAC 3 strip_tac
  >> fs[normalise_tyvars_rec_def,ELIM_UNCURRY]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> qmatch_goalsub_abbrev_tac `norm:(num#(type,type) alist)`
  >> (qspecl_then [`ty`,`(n0,[])`,`n0`,`chr`] assume_tac) normalise_tyvars_subst_len_inv
  >> qunabbrev_tac `norm`
  >> fs[ELIM_UNCURRY]
  >> first_x_assum drule
  >> rw[normalise_tyvars_subst_def]
  >> cheat
);
*)

Theorem normalise_tyvars_subst_monotone[local]:
  !ty n_subst n0 a chr. MEM a (MAP SND (SND n_subst))
  ==> MEM a (MAP SND (SND (normalise_tyvars_subst ty (FST n_subst) n0 (SND n_subst) chr)))
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- rw[renaming_def,normalise_tyvars_subst_def]
  >> Induct
  >- rw[renaming_def,normalise_tyvars_subst_def]
  >> strip_tac
  >> fs[EVERY_DEF]
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> rw[normalise_tyvars_subst_def]
  >> last_x_assum (qspecl_then [`n_subst`,`n0`,`a`,`chr`] mp_tac)
  >> rw[]
  >> ASSUME_TAC (INST_TYPE [alpha |-> ``:num#((type, type) alist)``, beta |-> ``:type``] FOLDL_invariant)
  >> first_x_assum (qspecl_then [`λn_subst. MEM a (MAP SND (SND n_subst))`] assume_tac)
  >> first_x_assum (qspecl_then [`(λ(n',subst') ty. normalise_tyvars_subst ty n' n0 subst' chr)`] assume_tac)
  >> first_x_assum (qspecl_then [`l`] assume_tac)
  >> first_x_assum (qspecl_then [`normalise_tyvars_subst h (FST n_subst) n0 (SND n_subst) chr`] assume_tac)
  >> fs[EVERY_MEM,ELIM_UNCURRY]
QED

Theorem EVERY_LIST_UNION:
  !l1 l2 P. EVERY P (LIST_UNION l1 l2) = (EVERY P l1 /\ EVERY P l2)
Proof
  rw[MEM_LIST_UNION,EVERY_MEM]
  >> metis_tac[]
QED

Theorem normalise_tyvars_subst_domain:
  !ty n n0 chr subst.
  EVERY (λx. strlen x < n0) (tyvars ty)
  ==> set (MAP SND (SND (normalise_tyvars_subst ty n n0 subst chr)))
  = set(MAP SND subst ++ MAP Tyvar (tyvars ty))
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rw[tyvars_def,normalise_tyvars_subst_def]
    >- (
      rw[UNION_DEF,INSERT_DEF,FUN_EQ_THM]
      >> metis_tac[]
    )
    >> fs[EQ_IMP_THM,IN_DEF,UNION_DEF,INSERT_DEF,FUN_EQ_THM]
      >> metis_tac[]
  )
  >> Induct
  >- rw[tyvars_def,normalise_tyvars_subst_def]
  >> rpt strip_tac
  >> rw[tyvars_def,normalise_tyvars_subst_def]
  >> fs[tyvars_def,EVERY_LIST_UNION]
  >> fs[EVERY_MEM]
  >> first_x_assum drule
  >> first_x_assum drule
  >> fs[normalise_tyvars_subst_def]
  >> disch_then (qspecl_then [`FST (normalise_tyvars_subst h n n0 subst chr)`,
      `chr`,`SND (normalise_tyvars_subst h n n0 subst chr)`] ASSUME_TAC)
  >> disch_then (qspecl_then [`n`,`chr`,`subst`] ASSUME_TAC)
  >> fs[]
  >> fs[LIST_TO_SET_MAP]
  >> metis_tac[UNION_ASSOC]
QED

Theorem MEM_MAP_f:
  !f l a. MEM a l ==> MEM (f a) (MAP f l)
Proof
  rw[MEM_MAP] >> qexists_tac `a` >> fs[]
QED

Theorem normalise_tyvars_rec_domain:
  !ty chr. set (MAP SND (SND (normalise_tyvars_rec ty chr))) = set(MAP Tyvar (tyvars ty))
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> (qspecl_then [`ty`,`n0`,`n0`,`chr`,`[]`] assume_tac) normalise_tyvars_subst_domain
  >> fs[]
  >> first_x_assum match_mp_tac
  >> unabbrev_all_tac
  >> rw[EVERY_MEM]
  >> (Q.ISPEC_THEN `strlen:mlstring->num` assume_tac) MEM_MAP_f
  >> first_x_assum drule
  >> strip_tac
  >> imp_res_tac list_max_MEM
  >> rw[]
QED

Theorem set_MEM:
  !A B. set A = set B ==> !a. MEM a A ==> MEM a B
Proof
  rw[]
QED

Theorem normalise_tyvars_rec_domain_imp:
  (!ty chr x. MEM x (MAP SND (SND (normalise_tyvars_rec ty chr))) ==> MEM x (MAP Tyvar (tyvars ty)))
  /\ (!ty chr x. MEM x (MAP Tyvar (tyvars ty)) ==> MEM x (MAP SND (SND (normalise_tyvars_rec ty chr))))
Proof
  rw[]
  >- ((qspecl_then [`ty`,`chr`] assume_tac) normalise_tyvars_rec_domain >> imp_res_tac set_MEM)
  >> ((qspecl_then [`ty`,`chr`] assume_tac) (GSYM normalise_tyvars_rec_domain) >> imp_res_tac set_MEM)
QED

Theorem TYPE_SUBST_replacing_all:
  !ty s.
  EVERY (λx. MEM (Tyvar x) (MAP SND s)) (tyvars ty)
  /\ ALL_DISTINCT (MAP SND s)
  /\ EVERY (λ(x,y). x <> y) s
  ==> EVERY (λx. MEM x (FLAT (MAP (tyvars o FST) s))) (tyvars (TYPE_SUBST s ty))
Proof
  rw[tyvars_TYPE_SUBST,tyvars_def,EVERY_MEM,MEM_FLAT,MEM_MAP]
  >> last_x_assum drule
  >> rw[]
  >> `MEM x (tyvars (FST y))` by (
    qpat_x_assum `MEM _ s` (assume_tac o ONCE_REWRITE_RULE[MEM_SPLIT_APPEND_first])
    >> fs[]
    >> rveq
    >> Cases_on `y`
    >> fs[ALL_DISTINCT_APPEND]
    >> qpat_x_assum `MEM x _` mp_tac
    >> (qspecl_then [`pfx`,`[(q,Tyvar x')]++sfx`,`Tyvar x'`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar x') pfx` by (
      strip_tac
      >> fs[MEM_MAP]
      >> qpat_x_assum `!x. _ \/ _` (qspec_then `(ty',Tyvar x')` mp_tac)
      >> rw[]
    )
    >> rveq
    >> fs[tyvars_def,REV_ASSOCD_def]
  )
  >> qexists_tac `tyvars (FST y)`
  >> fs[]
  >> qexists_tac `y`
  >> fs[]
QED

Theorem ALL_DISTINCT_MAP_inj[local]:
  !l f. (!x y. f x = f y <=> x = y) ==> ALL_DISTINCT l = ALL_DISTINCT (MAP f l)
Proof
  Induct
  >> rw[MEM_MAP]
  >> first_x_assum (qspec_then `f` assume_tac)
  >> fs[]
QED

Theorem normalise_tyvars_rec_len:
  !ty chr. LENGTH (SND (normalise_tyvars_rec ty chr)) = LENGTH (tyvars ty)
Proof
  rpt strip_tac
  >> qmatch_goalsub_abbrev_tac `norm:'a#'b`
  >> `!(a:type list) b. set a = set b /\ ALL_DISTINCT a /\ ALL_DISTINCT b
    ==> LENGTH a = LENGTH b` by (
    rpt strip_tac
    >> imp_res_tac (GSYM ALL_DISTINCT_CARD_LIST_TO_SET)
    >> rw[]
  )
  >> first_x_assum (qspecl_then [`MAP SND (SND norm)`,`MAP Tyvar (tyvars ty)`] assume_tac)
  >> `!a. ALL_DISTINCT (MAP (SND:((type#type)->type)) a) ==> LENGTH a = LENGTH (MAP SND a)` by (
    Induct >> fs[]
  )
  >> first_x_assum (qspec_then `SND norm` assume_tac)
  >> rfs[]
  >> first_x_assum match_mp_tac
  >> rpt strip_tac
  >> unabbrev_all_tac
  >> rw[normalise_tyvars_rec_domain,normalise_tyvars_rec_subst_snd_distinct]
  >> (qspec_then `ty` assume_tac) tyvars_ALL_DISTINCT
  >> (Q.ISPECL_THEN [`tyvars ty`,`Tyvar`] assume_tac) ALL_DISTINCT_MAP_inj
  >> rw[]
QED

Theorem tyvars_diff_types:
  !ty1 ty2. (?a. MEM a (tyvars ty1) /\ ~MEM a (tyvars ty2)) ==> ty1 <> ty2
Proof
  Induct
  >> strip_tac
  >> Induct
  >> rw[tyvars_def,MEM_FOLDR_LIST_UNION]
  >> first_x_assum (qspecl_then [`y`] assume_tac)
  >> Cases_on `l <> l'`
  >> rw[]
  >> fs[]
QED

Theorem MEM_tyvars_TYPE_SUBST[local]:
  !subst ty m n. renaming subst
  /\ NULL (list_inter (MAP FST ((Tyvar m,Tyvar n)::subst)) (MAP SND ((Tyvar m,Tyvar n)::subst)))
  ==> ~MEM n (tyvars (TYPE_SUBST ((Tyvar m,Tyvar n)::subst) ty))
Proof
  ho_match_mp_tac TYPE_SUBST_ind
  >> strip_tac
  >- (
    Induct
    >- (rw[TYPE_SUBST_def,REV_ASSOCD_def,tyvars_def,renaming_def,list_inter_def] >> fs[])
    >> Cases
    >> ONCE_REWRITE_TAC[renaming_simp]
    >> rw[TYPE_SUBST_def,REV_ASSOCD_def,tyvars_def]
    >- (
      fs[renaming_def,tyvars_def]
      >> imp_res_tac list_inter_heads
      >> fs[]
    )
    >- (
      fs[renaming_def,tyvars_def]
      >> rveq
      >> assume_tac (Q.ISPECL [
        `[Tyvar m]:type list`,
        `Tyvar (m':mlstring)`,
        `MAP FST (subst:(type,type)alist)`,
        `[]:type list`,
        `Tyvar (n:mlstring)`,
        `Tyvar subst'::MAP SND (subst:(type,type)alist)`] list_inter_elem)
      >> fs[]
    )
    >> fs[renaming_def,tyvars_def]
    >> rveq
    >> last_x_assum (qspecl_then [`subst'`,`m`,`n`] assume_tac)
    >> assume_tac (Q.ISPECL [`[Tyvar m:type]`,`[Tyvar m':type]`,`MAP FST (subst:(type,type)alist)`,
      `[Tyvar n:type]`,`[Tyvar n':type]`,`MAP SND (subst:(type,type)alist)`] list_inter_subset_outer)
    >> rfs[]
    >> fs[]
    >> fs[REV_ASSOCD_def]
    >> FULL_CASE_TAC
    >> rw[] >>fs[]
  )
  >> rw[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP]
  >> Cases_on `~MEM n (tyvars y)`
  >> fs[]
  >> strip_tac
  >> Cases_on `~MEM a tys`
  >> fs[]
  >> first_x_assum drule
  >> disch_then (qspecl_then[`m`,`n`] assume_tac)
  >> rfs[]
  >> assume_tac (Q.ISPECL [`y:type`,`(TYPE_SUBST ((Tyvar m,Tyvar n)::subst) a):type`] tyvars_diff_types)
  >> first_x_assum mp_tac
  >> disch_then match_mp_tac
  >> qexists_tac `n`
  >> rw[]
QED

Theorem MEM_tyvars_TYPE_SUBST_simp[local]:
  !subst ty m n a. renaming subst
  /\ NULL (list_inter (MAP FST ((Tyvar m,Tyvar n)::subst)) (MAP SND ((Tyvar m,Tyvar n)::subst)))
  /\ MEM a (tyvars (TYPE_SUBST ((Tyvar m,Tyvar n)::subst) ty))
  /\ a <> m
  ==> MEM a (tyvars (TYPE_SUBST subst ty))
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> ho_match_mp_tac type_ind
  >> rpt strip_tac
  >- (
    fs[TYPE_SUBST_def,REV_ASSOCD_def]
    >> FULL_CASE_TAC
    >> fs[tyvars_def]
  )
  >> fs[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP,EVERY_MEM,MEM_MAP]
  >> first_x_assum (qspecl_then [`a'`] mp_tac)
  >> rw[]
  >> first_x_assum (qspecl_then [`subst`,`m'`,`n`,`a`] assume_tac)
  >> rfs[]
  >> qexists_tac `TYPE_SUBST subst a'`
  >> rw[]
  >> qexists_tac `a'`
  >> rw[]
QED

Theorem renaming_dom_img_disjoint[local]:
  !subst. renaming subst
  /\ NULL (list_inter (MAP FST subst) (MAP SND subst))
  ==> !ty m n a. MEM (Tyvar a) (MAP SND subst) ==> ~MEM a (tyvars (TYPE_SUBST subst ty))
Proof
  Induct
  >- rw[]
  >> Cases
  >> ONCE_REWRITE_TAC[renaming_def]
  >> strip_tac
  >> Induct
  >- (
    rpt strip_tac
    >> fs[]
    >> imp_res_tac list_inter_tails
    >> imp_res_tac list_inter_heads
    >- (
      fs[renaming_def]
      >> assume_tac MEM_tyvars_TYPE_SUBST
      >> first_x_assum (qspecl_then [`subst`,`Tyvar m`,`m'`,`a`] assume_tac)
      >> rfs[renaming_def]
    )
    >> fs[renaming_def]
    >> rveq
    >> first_x_assum (qspecl_then [`Tyvar m`,`a`] assume_tac)
    >> fs[MEM_MAP,Q.SPECL [`y`,`subst`] MEM_SPLIT]
    >> Cases_on `y`
    >> assume_tac (Q.ISPECL [`[]:(type list)`, `(Tyvar m'):type`, `MAP FST ((l1 ⧺ [(q,r)] ⧺ l2):(type,type)alist)`,
      `Tyvar n::MAP SND (l1:(type,type)alist)`, `r:type`, `MAP SND (l2:(type,type)alist)`] list_inter_elem)
    >> fs[TYPE_SUBST_def,REV_ASSOCD_def,tyvars_def]
    >> FULL_CASE_TAC
    >- (
      fs[tyvars_def]
      >> Cases_on `l1'` >> Cases_on `l2'`
      >> rw[] >> fs[] >> rw[] >> fs[]
    )
    >> qpat_x_assum `(?y. _) ==> _` mp_tac
    >> rw[]
    >- (
      qexists_tac `(Tyvar m'', Tyvar a)`
      >> rw[]
      >> metis_tac[]
    )
    >> metis_tac[]
  )
  >> fs[renaming_def]
  >> imp_res_tac list_inter_tails
  >> imp_res_tac list_inter_heads
  >> rw[]
  >- (
    rw[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP]
    >> Cases_on `~MEM a (tyvars y)`
    >> fs[]
    >> strip_tac
    >> Cases_on `~MEM a' l`
    >> fs[]
    >> assume_tac (Q.ISPECL [`y:type`,`(TYPE_SUBST ((Tyvar m,Tyvar a)::subst) a'):type`] tyvars_diff_types)
    >> first_x_assum mp_tac
    >> disch_then match_mp_tac
    >> qexists_tac `a`
    >> rw[]
    >> match_mp_tac MEM_tyvars_TYPE_SUBST
    >> rw[renaming_def]
  )
  >> rw[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_MAP]
  >> Cases_on `~MEM a (tyvars y)`
  >> fs[]
  >> strip_tac
  >> Cases_on `~MEM a' l`
  >> fs[]
  >> assume_tac (Q.ISPECL [`y:type`,`(TYPE_SUBST ((Tyvar m,Tyvar n)::subst) a'):type`] tyvars_diff_types)
  >> first_x_assum mp_tac
  >> disch_then match_mp_tac
  >> qexists_tac `a`
  >> rw[]
  >> Cases_on `a=n`
  >- (
    rveq
    >> match_mp_tac MEM_tyvars_TYPE_SUBST
    >> fs[renaming_def]
  )
  >> first_x_assum (qspecl_then [`a'`,`a`] assume_tac)
  >> assume_tac MEM_tyvars_TYPE_SUBST_simp
  >> first_x_assum (qspecl_then [`subst`,`a'`,`m`,`n`,`a`] assume_tac)
  >> fs[renaming_def]
  >> rfs[]
  >> fs[renaming_def]
  >> `?l1 l2 b. subst = l1 ++ [Tyvar b,Tyvar a] ++ l2` by (
    fs[MEM_MAP,MEM_SPLIT] >> rveq >> fs[EVERY_DEF,ELIM_UNCURRY]
    >> qexists_tac `l1` >> qexists_tac `l2` >> qexists_tac `m`
    >> Cases_on `y'` >> fs[] >> rw[]
  )
  >> rveq
  >> fs[EVERY_DEF,ELIM_UNCURRY]
  >> assume_tac (INST_TYPE [alpha |-> ``:type``] list_inter_elem)
  >> first_x_assum (qspecl_then [`[]`,`Tyvar a`,`MAP FST l1 ⧺ [Tyvar b] ⧺ MAP FST l2`,
    `Tyvar n::MAP SND l1`,`Tyvar a`,`MAP SND l2`] assume_tac)
  >> fs[]
QED

Theorem TYPE_SUBST_replacing[local]:
  !subst ty.
  renaming subst
  /\ EVERY (λx. MEM (Tyvar x) (MAP SND subst)) (tyvars ty)
  /\ NULL (list_inter (MAP FST subst) (MAP SND subst))
  ==> NULL (list_inter (tyvars ty) (tyvars (TYPE_SUBST subst ty)))
Proof
  rw[]
  >> rw[NULL_EQ]
  >> ONCE_REWRITE_TAC[(GSYM (CONJUNCT2 LIST_TO_SET_EQ_EMPTY))]
  >> ONCE_REWRITE_TAC[list_inter_set]
  >> rw[tyvars_TYPE_SUBST,GSYM DISJOINT_DEF,DISJOINT_ALT]
  >> imp_res_tac renaming_dom_img_disjoint
  >> first_x_assum (qspecl_then [`x`] assume_tac)
  >> fs[EVERY_MEM]
  >> first_x_assum (qspecl_then [`x`] assume_tac)
  >> rfs[] >> fs[]
  >> first_x_assum (qspecl_then [`Tyvar x'`] mp_tac)
  >> rw[]
QED

Theorem tyvars_identity[local]:
  !l. EVERY (λx. ?a. x = Tyvar a) l
  ==> !a. MEM a ((MAP Tyvar o FLAT o MAP tyvars) l) = MEM a l
Proof
  Induct
  >- rw[]
  >> Cases
  >- (
    rpt strip_tac
    >> fs[EVERY_DEF]
    >> rw[MEM,FLAT,MAP,tyvars_def]
  )
  >> rw[EVERY_DEF]
QED

Theorem renaming_normalise_tyvars_rec[local]:
  !ty chr. (renaming o SND) (normalise_tyvars_rec ty chr)
Proof
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> `tyvars_constr n0 (n0,[])` by rw[tyvars_constr_def]
  >> imp_res_tac normalise_tyvars_subst_ineq
  >> first_x_assum (qspecl_then [`ty`,`chr`] assume_tac)
  >> qmatch_asmsub_abbrev_tac `n_subst:(num#(type,type)alist)`
  >> Cases_on `n_subst`
  >> fs[tyvars_constr_def,renaming_def]
  >> qpat_x_assum `EVERY _ _` mp_tac
  >> match_mp_tac EVERY_MONOTONIC
  >> rw[pairTheory.ELIM_UNCURRY]
  >> qexists_tac `a` >> qexists_tac `b` >> fs[]
QED

(*
val normalise_tyvars_differ = Q.prove(
  `!ty chr. NULL (list_inter (tyvars ty) ((tyvars o FST) (normalise_tyvars_rec ty chr)))`,
  rw[normalise_tyvars_rec_def]
  >> qmatch_goalsub_abbrev_tac `n0:num`
  >> qmatch_goalsub_abbrev_tac `n_subst:(num#(type,type)alist)`
  >> pop_assum (assume_tac o GSYM o PURE_ONCE_REWRITE_RULE[markerTheory.Abbrev_def])
  >> Cases_on `n_subst`
  >> `renaming r` by (
    assume_tac renaming_normalise_tyvars_rec
    >> first_x_assum (qspecl_then [`ty`,`chr`] assume_tac)
    >> fs[normalise_tyvars_rec_def]
    >> qunabbrev_tac `n0`
    >> qmatch_asmsub_abbrev_tac `repl:(num#(type,type)alist)`
    >> `r = SND repl` by (fs[PAIR])
    >> fs[]
  )
  >> `NULL (list_inter (MAP FST r) (MAP SND r))` by (
    assume_tac (INST_TYPE [alpha|->``:type list``,beta|->``:type``] list_inter_mono)
    >> first_x_assum (qspecl_then [`MAP FST r`,`MAP SND r`,`I`,`(MAP Tyvar) o FLAT o (MAP tyvars)`] mp_tac)
    >> fs[]
    >> disch_then match_mp_tac
    >> `EVERY (λx. ∃a. x = Tyvar a) (MAP FST r)` by (
      rw[EVERY_MEM,MEM_MAP] >> fs[MEM_SPLIT] >> rveq
      >> fs[renaming_def,ELIM_UNCURRY]
    )
    >> `EVERY (λx. ∃a. x = Tyvar a) (MAP SND r)` by (
      rw[EVERY_MEM,MEM_MAP] >> fs[MEM_SPLIT] >> rveq
      >> fs[renaming_def,ELIM_UNCURRY]
    )
    >> assume_tac (Q.SPECL [`MAP FST (r:(type,type)alist)`] tyvars_identity)
    >> assume_tac (Q.SPECL [`MAP SND (r:(type,type)alist)`] tyvars_identity)
    >> rfs[]
    >> match_mp_tac list_inter_map_inj
    >> rw[MAP_MAP_o]
    >> assume_tac (Q.SPECL [`ty`,`chr`] normalise_tyvars_rec_differ)
    >> fs[normalise_tyvars_rec_def]
    >> qunabbrev_tac `n0`
    >> qmatch_asmsub_abbrev_tac `repl:(num#(type,type)alist)`
    >> `r = SND repl` by (fs[PAIR])
    >> rw[]
  )
  >> `EVERY (λx. MEM (Tyvar x) (MAP SND r)) (tyvars ty)` by (
    rw[EVERY_MEM]
    >> assume_tac normalise_tyvars_subst_replacing
    >> first_x_assum (qspecl_then [`ty`,`chr`,`x`] mp_tac)
    >> rw[normalise_tyvars_rec_def]
  )
  >> drule TYPE_SUBST_replacing
  >> rw[]
);
*)

Theorem normalise_tyvars_rec_chr_diff:
  !ty1 ty2 chr1 chr2. chr1 <> chr2 ==>
    NULL (list_inter (MAP FST (SND (normalise_tyvars_rec ty1 chr1))) (MAP FST (SND (normalise_tyvars_rec ty2 chr2))))
Proof
  rw[NULL_FILTER,list_inter_def]
  >> CCONTR_TAC
  >> (qspecl_then [`ty1`,`chr1`] assume_tac) normalise_tyvars_rec_chr
  >> (qspecl_then [`ty2`,`chr2`] assume_tac) normalise_tyvars_rec_chr
  >> fs[ELIM_UNCURRY,EVERY_MEM,MEM_MAP]
  >> rpt (first_x_assum drule)
  >> rpt (disch_then assume_tac)
  >> (qspecl_then [`ty1`,`chr1`] assume_tac) normalise_tyvars_rec_ineq2
  >> Cases_on `y'`
  >> Cases_on `y''`
  >> fs[EVERY_MEM,ELIM_UNCURRY]
  >> first_x_assum drule
  >> disch_then assume_tac
  >> Q.ISPECL_THEN [`n''`,`n'''`,`chr1`,`chr2`] assume_tac
    (Q.prove(`!n n' x y. x <> y /\ (n <> 0 \/ n' <> 0) ==> REPLICATE n x <> REPLICATE n' y`,
      Induct >> Induct >> fs[REPLICATE]))
  >> rfs[]
QED

Theorem normalise_tyvars_rec_chr_diff2:
  !ty1 ty2 chr1 chr2. chr1 <> chr2 ==>
    NULL (list_inter (tyvars (FST (normalise_tyvars_rec ty1 chr1)))
    (tyvars (FST (normalise_tyvars_rec ty2 chr2))))
Proof
  rpt strip_tac
  >> imp_res_tac normalise_tyvars_rec_chr_diff
  >> first_x_assum (qspecl_then [`ty2`,`ty1`] assume_tac)
  >> CCONTR_TAC
  >> (qspecl_then [`ty1`,`chr1`] assume_tac) normalise_tyvars_rec_subst_snd_distinct
  >> (qspecl_then [`ty2`,`chr2`] assume_tac) normalise_tyvars_rec_subst_snd_distinct
  >> (qspecl_then [`ty1`,`chr1`] assume_tac) normalise_tyvars_rec_ineq
  >> (qspecl_then [`ty2`,`chr2`] assume_tac) normalise_tyvars_rec_ineq
  >> (qspecl_then [`ty1`,`chr1`] assume_tac) normalise_tyvars_rec_renames
  >> (qspecl_then [`ty2`,`chr2`] assume_tac) normalise_tyvars_rec_renames
  >> fs[NULL_FILTER,list_inter_def,normalise_tyvars_rec_def,MEM_MAP,renaming_def]
  >> qmatch_assum_abbrev_tac `MEM _ (tyvars (TYPE_SUBST subst1 ty1))`
  >> qmatch_assum_abbrev_tac `MEM _ (tyvars (TYPE_SUBST subst2 ty2))`
  >> `∀x. MEM x (tyvars ty1) ⇒ MEM (Tyvar x) (MAP SND subst1)` by (
    (qspecl_then [`ty1`,`chr1`] assume_tac) (GSYM normalise_tyvars_rec_domain)
    >> imp_res_tac set_MEM
    >> strip_tac
    >> first_x_assum (qspec_then `Tyvar x` assume_tac)
    >> fs[MEM_MAP,normalise_tyvars_rec_def]
    >> rfs[]
  )
  >> `∀x. MEM x (tyvars ty2) ⇒ MEM (Tyvar x) (MAP SND subst2)` by (
    (qspecl_then [`ty2`,`chr2`] assume_tac) (GSYM normalise_tyvars_rec_domain)
    >> imp_res_tac set_MEM
    >> strip_tac
    >> first_x_assum (qspec_then `Tyvar x` assume_tac)
    >> fs[MEM_MAP,normalise_tyvars_rec_def]
    >> rfs[]
  )
  >> (qspecl_then [`ty1`,`subst1`] assume_tac) TYPE_SUBST_replacing_all
  >> (qspecl_then [`ty2`,`subst2`] assume_tac) TYPE_SUBST_replacing_all
  >> rfs[EVERY_MEM]
  >> NTAC 2 (first_x_assum drule >> disch_then assume_tac)
  >> fs[MEM_FLAT,MEM_MAP]
  >> NTAC 2 (first_x_assum drule >> disch_then assume_tac)
  >> Cases_on `y'`
  >> Cases_on `y''`
  >> fs[ELIM_UNCURRY]
  >> rveq
  >> fs[tyvars_def]
  >> rveq
  >> qpat_x_assum `!x. _ ==> !x. _` (qspec_then `Tyvar m` assume_tac)
  >> fs[PULL_EXISTS]
  >> first_x_assum (qspec_then `(Tyvar m,Tyvar n)` assume_tac)
  >> rfs[]
  >> first_x_assum (qspec_then `(Tyvar m,Tyvar n')` assume_tac)
  >> fs[]
QED

Definition clean_tysubst_def:
  (clean_tysubst [] = [])
  /\ (clean_tysubst ((_,Tyapp _ _)::l) = clean_tysubst l)
  /\ (clean_tysubst ((a:type,Tyvar b)::l) =
    (a,Tyvar b)::(clean_tysubst (FILTER (λ(_,x). x <> Tyvar b) l)))
Termination
  WF_REL_TAC `measure LENGTH` >> rw[]
>> match_mp_tac LESS_EQ_IMP_LESS_SUC >> rw[LENGTH_FILTER_LEQ]
End

(* remove duplicates, identical mappings and type applications *)
Definition clean_tysubst_def:
  (clean_tysubst [] = [])
  /\ (clean_tysubst ((_,Tyapp _ _)::l) = clean_tysubst l)
  /\ (clean_tysubst ((a:type,Tyvar b)::l) =
    if a = Tyvar b
    then FILTER (λ(y,x). x <> Tyvar b) (clean_tysubst l)
    else (a,Tyvar b)::FILTER (λ(y,x). x <> Tyvar b) (clean_tysubst l))
End

Theorem clean_tysubst_prop:
  (!s. ALL_DISTINCT (MAP SND (clean_tysubst s)))
  /\ (!s. EVERY (λ(y,x). (?a. Tyvar a = x /\ x <> y)) (clean_tysubst s))
Proof
  strip_tac
  >- (
    Induct >- rw[ALL_DISTINCT,MAP,clean_tysubst_def]
    >> Cases >> Cases_on `r` >> rw[ALL_DISTINCT_APPEND,clean_tysubst_def]
    >> rw[MAP_SND_FILTER_NEQ,MEM_FILTER,FILTER_ALL_DISTINCT]
  )
  >> Induct >- rw[clean_tysubst_def]
  >> Cases >> Cases_on `r`
  >> rw[clean_tysubst_def,EVERY_FILTER_IMP]
QED

Theorem clean_tysubst_eq[local]:
  (!s1 s2 a b tys. clean_tysubst (s1++[(a,Tyapp b tys)]++s2) = clean_tysubst (s1++s2))
  /\ (!s1 s2 s3 a b c. a <> Tyvar b ==> clean_tysubst (s1++[(a,Tyvar b)]++s2++[(c,Tyvar b)]++s3) = clean_tysubst (s1++[(a,Tyvar b)]++s2++s3))
Proof
  strip_tac
  >- (
    Induct >- (strip_tac >> Cases >> rw[clean_tysubst_def])
    >> Cases >> Cases_on `r` >> fs[clean_tysubst_def]
  )
  >> Induct (* on s1 *)
  >- (
    Induct (* on s2 *)
    >- rw[clean_tysubst_def,FILTER_IDEM]
    >> Cases >> Cases_on `r`
    >- (
      rw[clean_tysubst_def]
      >- (fs[] >> first_x_assum drule >> rw[clean_tysubst_def]
        >> CONV_TAC(LHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> rw[]
      )
      >> FULL_CASE_TAC >> rw[clean_tysubst_def]
      >- (
        first_x_assum (qspecl_then [`s3`,`a`,`b`,`c`] mp_tac)
        >> rw[clean_tysubst_def]
        >> CONV_TAC(LHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> rw[]
      )
      >> rw[FILTER_IDEM]
      >> first_x_assum drule
      >> fs[clean_tysubst_def]
    )
    >> rw[clean_tysubst_def]
    >> first_x_assum drule
    >> fs[clean_tysubst_def]
  )
  >> Cases >> Cases_on `r`
  >> rw[clean_tysubst_def]
QED

Theorem clean_tysubst_FILTER_eq[local]:
  (!s1 s2 a b. a <> Tyvar b ==> clean_tysubst (s1++[(a,Tyvar b)]++s2)
  = clean_tysubst (s1++[(a,Tyvar b)]++FILTER (λ(y,x). x <> Tyvar b) s2))
Proof
  Induct
  >- (
    Induct
    >- fs[]
    >> Cases >> Cases_on `r`
    >- (
      rw[clean_tysubst_def]
      >- (
        first_x_assum drule
        >> rw[clean_tysubst_def]
        >> CONV_TAC(LHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> rw[]
      )
      >- (
        first_x_assum drule
        >> rw[clean_tysubst_def,FILTER_IDEM]
      )
      >- (
        first_x_assum drule
        >> rw[clean_tysubst_def]
        >> CONV_TAC(LHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [FILTER_COMM]))
        >> rw[]
      )
      >> first_x_assum drule
      >> rw[clean_tysubst_def,FILTER_IDEM]
    )
    >> fs[clean_tysubst_def]
    >> fs[]
  )
  >> Cases >> Cases_on `r`
  >> rpt strip_tac
  >> (
    RULE_ASSUM_TAC GSYM
    >> fs[clean_tysubst_def]
  )
QED

Theorem clean_tysubst_NOT_MEM_MAP_SND:
  !s x. ~MEM x (MAP SND s) ==> ~MEM x (MAP SND (clean_tysubst s))
Proof
  Induct
  >- fs[clean_tysubst_def]
  >> Cases >> Cases_on `r`
  >> rw[clean_tysubst_def,MAP_SND_FILTER_NEQ,MEM_FILTER]
QED

Theorem clean_tysubst_ALL_DISTINCT_MAP_SND:
!s. ALL_DISTINCT (MAP SND (clean_tysubst s))
Proof
  Induct
  >- rw[clean_tysubst_def]
  >> Cases_on `h` >> Cases_on `r`
  >- (
    rw[clean_tysubst_def,MAP_SND_FILTER_NEQ]
    >- (match_mp_tac FILTER_ALL_DISTINCT >> fs[])
    >- rw[MEM_FILTER]
    >> (match_mp_tac FILTER_ALL_DISTINCT >> fs[])
  )
  >> rw[clean_tysubst_def]
QED

Theorem clean_tysubst_non_triv:
  !s. EVERY (λ(y,x). (?a. Tyvar a = x /\ x <> y)) (clean_tysubst s)
Proof
  Induct
  >- rw[clean_tysubst_def]
  >> Cases_on `h` >> Cases_on `r`
  >- (
    rw[clean_tysubst_def]
    >> (match_mp_tac EVERY_FILTER_IMP >> fs[])
  )
  >> rw[clean_tysubst_def]
QED

Theorem REV_ASSOCD_NOT_MEM_drop:
  !s x. ~MEM x (MAP SND s) ==> REV_ASSOCD x s x = x
Proof
  Induct >> rw[REV_ASSOCD_def]
QED

Theorem clean_tysubst_TYPE_SUBST_eq:
  !ty s. TYPE_SUBST s ty = TYPE_SUBST (clean_tysubst s) ty
Proof
  fs[TYPE_SUBST_tyvars]
  >> CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[clean_tysubst_def,EVERY_DEF]
  >> Cases >> Cases_on `r`
  >- (
    rw[clean_tysubst_def,REV_ASSOCD_def]
    >> fs[REV_ASSOCD_FILTER]
    >> first_x_assum match_mp_tac
    >> asm_exists_tac
    >> fs[]
  )
  >> rw[REV_ASSOCD_def,clean_tysubst_def]
  >> first_x_assum match_mp_tac
  >> asm_exists_tac
  >> fs[]
QED

Theorem clean_tysubst_wlog:
  !s. ?s'. ALL_DISTINCT (MAP SND s')
  /\ EVERY (λ(y,x). (?a. Tyvar a = x /\ x <> y)) s'
  /\ !ty. TYPE_SUBST s ty = TYPE_SUBST s' ty
Proof
  strip_tac
  >> qexists_tac `clean_tysubst s`
  >> rw[clean_tysubst_prop,GSYM clean_tysubst_TYPE_SUBST_eq]
QED

Theorem TYPE_SUBST_FILTER_tyvars:
  !ty s. TYPE_SUBST s ty = TYPE_SUBST (FILTER (λ(x,y). ?a. Tyvar a = y /\ MEM a (tyvars ty)) s) ty
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[REV_ASSOCD_def,TYPE_SUBST_def]
  >> fs[TYPE_SUBST_tyvars]
  >> Cases >> Cases_on `r`
  >- (rw[REV_ASSOCD_def,TYPE_SUBST_def] >> fs[])
  >> rw[REV_ASSOCD_def,TYPE_SUBST_def]
QED

Theorem TYPE_SUBST_FILTER_tyvars2:
  !ty s. TYPE_SUBST s ty
  = TYPE_SUBST (FILTER (λx. MEM (SND x) (MAP Tyvar (tyvars ty))) s) ty
Proof
  CONV_TAC SWAP_FORALL_CONV
  >> Induct
  >- rw[REV_ASSOCD_def,TYPE_SUBST_def]
  >> fs[TYPE_SUBST_tyvars]
  >> Cases
  >> rw[]
  >- (
    qpat_x_assum `MEM _ (MAP _ _)` (assume_tac o REWRITE_RULE[MEM_MAP])
    >> fs[REV_ASSOCD_def]
  )
  >> rw[REV_ASSOCD_def]
  >> fs[MEM_MAP]
QED

Theorem orth_ty_instances:
  !(ty1:type) ty2. ty1 # ty2 ==> !s s'. (TYPE_SUBST s ty1) # (TYPE_SUBST s' ty2)
Proof
  rw[orth_ty_def,TYPE_SUBST_compose]
  >> first_x_assum (qspec_then `ty` mp_tac)
  >> strip_tac
  >- (DISJ1_TAC >> fs[])
  >> (DISJ2_TAC >> fs[])
QED

Theorem orth_ty_symm_imp[local]:
  !(ty1:type) ty2. (ty1 # ty2) ==> (ty2 # ty1)
Proof
  fs[orth_ty_def,AC DISJ_ASSOC DISJ_COMM]
QED

Theorem orth_ty_symm:
  !(ty1:type) ty2. (ty1 # ty2) = (ty2 # ty1)
Proof
  rw[EQ_IMP_THM,orth_ty_symm_imp]
QED

Definition unifiable_def:
  unifiable ty1 ty2 = ?s. TYPE_SUBST s ty1 = TYPE_SUBST s ty2
End

Theorem unifiable_orth_ty_equiv:
  !ty1 ty2. NULL (list_inter (tyvars ty1) (tyvars ty2))
  ==> unifiable ty1 ty2 = ~(ty1 # ty2)
Proof
  rw[EQ_IMP_THM,unifiable_def,orth_ty_def]
  >- (
    qexists_tac `TYPE_SUBST s ty1`
    >> rw[]
    >> qexists_tac `s`
    >> rw[]
  )
  >> (qspecl_then [`ty2`,`i'`] assume_tac) TYPE_SUBST_FILTER_tyvars
  >> (qspecl_then [`ty1`,`i`] assume_tac) TYPE_SUBST_FILTER_tyvars
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST (FILTER p1 i) ty1`
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST (FILTER p2 i') ty2`
  >> qexists_tac `(FILTER p1 i) ++ (FILTER p2 i')`
  >> `!x. FILTER p1 (FILTER p2 x) = []` by (
    fs[NULL_FILTER,list_inter_def]
    >> strip_tac
    >> rw[FILTER_FILTER]
    >> rw[GSYM NULL_EQ,NULL_FILTER]
    >> qunabbrev_tac `p1`
    >> qunabbrev_tac `p2`
    >> CCONTR_TAC
    >> fs[ELIM_UNCURRY]
    >> Cases_on `x'`
    >> fs[]
    >> rveq
    >> first_x_assum (qspec_then `a` assume_tac)
    >> fs[]
    >> rveq
    >> fs[]
  )
  >> PURE_ONCE_REWRITE_TAC[TYPE_SUBST_FILTER_tyvars]
  >> rw[FILTER_APPEND,FILTER_IDEM,FILTER_COMM]
  >> fs[]
QED

Theorem type_size[local]:
  !t s. type_size' t <= type_size' (TYPE_SUBST s t)
Proof
  ho_match_mp_tac type_ind
  >> rw[type_size'_def]
  >- (
    Cases_on `MEM (Tyvar m) (MAP SND s)`
    >- (
      imp_res_tac MEM_SPLIT_APPEND_SND_first
      >> imp_res_tac TYPE_SUBST_drop_prefix
      >> pop_assum (qspec_then `[(q,Tyvar m)]++sfx` assume_tac)
      >> fs[REV_ASSOCD_def]
      >> Cases_on `q`
      >> fs[type_size'_def]
    )
    >> imp_res_tac REV_ASSOCD_NOT_MEM_drop
    >> fs[type_size'_def]
  )
  >> fs[type1_size'_SUM_MAP]
  >> Induct_on `l`
  >- fs[type_size'_def]
  >> rw[type_size'_def]
  >> fs[]
  >> first_x_assum (qspec_then `s` assume_tac)
  >> rw[ADD_MONO_LESS_EQ]
QED


Theorem PAIR_MAP_o:
  !f f' g g'. (f ## f') o (g ## g') = (f o g) ## (f' o g')
Proof
  fs[FUN_EQ_THM,o_DEF] >> NTAC 4 strip_tac >> Cases >> fs[PAIR_MAP_THM]
QED

Theorem SND_PAIR_MAP_o:
  !f g. SND o (f ## g) = g o SND
Proof
  fs[SND_PAIR_MAP,FUN_EQ_THM,o_DEF]
QED

Theorem FST_PAIR_MAP_o:
  !f g. FST o (f ## g) = f o FST
Proof
  fs[FST_PAIR_MAP,FUN_EQ_THM,o_DEF]
QED

Theorem MAP_SND_I[local]:
  !ls f. (MAP SND (MAP (f ## I) ls)) = MAP SND ls
Proof
  Induct >> rw[]
QED

Theorem FST_SWAP_SND[local]:
  FST o SWAP = SND /\ SND o SWAP = FST
Proof
  rw[FUN_EQ_THM,EQ_IMP_THM,SWAP_def]
QED

Theorem renaming_clean_tysubst:
  !s. renaming s ==> renaming (clean_tysubst s)
Proof
  Induct
  >- fs[renaming_def,clean_tysubst_def]
  >> rpt strip_tac
  >> fs[renaming_def]
  >> pairarg_tac
  >> fs[clean_tysubst_def,EVERY_MEM,MEM_FILTER,ELIM_UNCURRY]
  >> rveq
  >> rw[]
  >> fs[MEM_FILTER]
QED

Theorem non_triv_renaming_clean_tysubst:
  !s. renaming s ==> non_triv_renaming (clean_tysubst s)
Proof
  rw[renaming_clean_tysubst,non_triv_renaming_def]
  >> (qspec_then `s` assume_tac) (CONJUNCT1 clean_tysubst_prop) >> fs[]
  >> (qspec_then `s` mp_tac) (CONJUNCT2 clean_tysubst_prop)
  >> match_mp_tac MONO_EVERY
  >> fs[ELIM_UNCURRY,PULL_EXISTS]
QED

Theorem renaming_wlog_non_triv:
  !s. renaming s ==> ?s'. non_triv_renaming s' /\ !ty. TYPE_SUBST s ty = TYPE_SUBST s' ty
Proof
  rpt strip_tac
  >> imp_res_tac non_triv_renaming_clean_tysubst
  >> asm_exists_tac
  >> rw[GSYM clean_tysubst_TYPE_SUBST_eq]
QED

Theorem MAP_SND_FILTER:
  !l f. MAP SND (FILTER (λx. f (SND x)) l) = FILTER f (MAP SND l)
Proof
  Induct >> rw[]
QED

Theorem NOT_MEM_TYPE_SUBST_FILTER:
  !l s pfx sfx x m. ~MEM (Tyvar x) l /\ s = pfx ++ [(Tyvar m, Tyvar x)] ++ sfx
  /\ non_triv_renaming s
  /\ ALL_DISTINCT (MAP FST s)
  /\ NULL (list_inter (MAP FST s) (MAP SND s))
  ==> ~MEM (Tyvar m) (MAP (TYPE_SUBST s) (FILTER (λx. MEM x (MAP SND s)) l))
Proof
  rw[MEM_MAP,MEM_FILTER,non_triv_renaming_def,renaming_def]
  >> CCONTR_TAC
  >> fs[]
  >> Cases_on `y'`
  >> fs[]
  >> rveq
  >> fs[EVERY_MEM]
  >> NTAC 2 (first_x_assum drule >> strip_tac)
  >> fs[ELIM_UNCURRY] >> rveq
  >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
  >> imp_res_tac MEM_SPLIT_APPEND_SND_first
  >> rveq
  >- (
    qmatch_asmsub_abbrev_tac `TYPE_SUBST (pfx' ++ tup ++ sfx' ++ tup' ++ sfx) _`
    >> (qspecl_then[`pfx'`,`tup ++ sfx' ++ tup' ++ sfx`,`Tyvar n`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar n) pfx'` by (
      qpat_x_assum `~MEM _ (MAP SND pfx')` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
      >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty,Tyvar n)` mp_tac) >> fs[]
    )
    >> qunabbrev_tac `tup`
    >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
    >> rveq
    >> fs[ALL_DISTINCT_APPEND]
  )
  (* >> qpat_x_assum `MEM _ (_ ++ _ ++ _)` kall_tac *)
  >> `q = Tyvar m'` by (
    fs[ALL_DISTINCT_APPEND]
    >- (imp_res_tac (Q.ISPEC `SND` MEM_MAP_f) >> fs[])
    >> (imp_res_tac (Q.ISPEC `SND` MEM_MAP_f) >> qpat_x_assum `!x. _ \/ x = Tyvar n ==> _ ` (qspec_then `Tyvar n` assume_tac) >> fs[])
  )
  >> fs[]
  >> `~MEM (Tyvar n) (MAP SND (pfx ++[(Tyvar m,Tyvar x)] ++ pfx'))` by (
    fs[MAP_APPEND,ALL_DISTINCT_APPEND]
  )
  >> qmatch_asmsub_abbrev_tac `REV_ASSOCD _ (pfx ++ tup ++ pfx' ++ tup' ++ sfx') _`
  >> (qspecl_then[`pfx ++ tup ++ pfx'`,`tup' ++ sfx'`,`Tyvar n`] assume_tac) TYPE_SUBST_reduce_list
  >> `!ty. ~MEM (ty,Tyvar n) (pfx ++ tup ++ pfx')` by (
    qpat_x_assum `~MEM _ (MAP SND (pfx ++ tup ++ pfx'))` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
    >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty,Tyvar n)` mp_tac) >> fs[]
  )
  >> qunabbrev_tac `tup'`
  >> fs[tyvars_def,REV_ASSOCD_def]
  >> fs[ALL_DISTINCT_APPEND]
QED

Theorem renaming_undo_eq:
  !s ty. non_triv_renaming s
  /\ NULL (list_inter (MAP FST s) (MAP SND s))
  /\ ALL_DISTINCT (MAP FST s)
  /\ EVERY (λx. ~MEM (Tyvar x) (MAP FST s)) (tyvars ty)
  ==> ?f. !ts. TYPE_SUBST (f ts) (TYPE_SUBST s ty) = TYPE_SUBST ts ty
Proof
  rw[]
  >> qexists_tac `λts. (MAP (I ## TYPE_SUBST s) (FILTER (λ(_,y). MEM y (MAP SND s)) ts)) ++ (MAP SWAP s) ++ ts`
  >> strip_tac
  >> fs[renaming_def,non_triv_renaming_def,ELIM_UNCURRY]
  >> rw[TYPE_SUBST_compose,TYPE_SUBST_tyvars]
  >> Cases_on `MEM (Tyvar x) (MAP SND s)`
  >- (
    imp_res_tac MEM_SPLIT_APPEND_SND_first
    >> rw[]
    >> qmatch_goalsub_abbrev_tac `MAP (ts' ## I) pfx ++ tup ++ l1 ++ l2 ++ l3 ++ l4 ++ l5`
    >> `~MEM (Tyvar x) (MAP SND (MAP (ts' ## I) pfx))` by rw[MAP_SND_I]
    >> (qspecl_then[`MAP (ts' ## I) pfx`,`tup ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ ts`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar x) (MAP (ts' ## I) pfx)` by (
      qpat_x_assum `~MEM _ _` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
      >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
    )
    >> qunabbrev_tac `tup`
    >> qunabbrev_tac `ts'`
    >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
    >> qpat_x_assum `REV_ASSOCD_def _ _ _ = _` kall_tac
    >> qunabbrev_tac `l2`
    >> Cases_on `MEM (Tyvar x) (MAP SND ts)`
    >- (
      imp_res_tac MEM_SPLIT_APPEND_SND_first
      >> rw[FILTER_APPEND]
      >> qmatch_goalsub_abbrev_tac `pfx' ++ tup ++ sfx'`
      >> (qspecl_then[`pfx'`,`tup ++ sfx'`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
      >> `!ty. ~MEM (ty,Tyvar x) pfx'` by (
        qpat_x_assum `~MEM _ (MAP SND pfx')` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
        >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
      )
      >> qunabbrev_tac `tup`
      >> fs[tyvars_def,REV_ASSOCD_def]
      >> qmatch_goalsub_abbrev_tac `pfx ++ tup ++ sfx`
      >> (qspecl_then[`pfx`,`tup ++ sfx`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
      >> `!ty. ~MEM (ty,Tyvar x) pfx` by (
        qpat_x_assum `~MEM _ (MAP SND pfx)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
        >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
      )
      >> qunabbrev_tac `tup`
      >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
      >> qmatch_goalsub_abbrev_tac `MAP ts'' (FILTER f pfx')`
      >> `~MEM (Tyvar m) (MAP SND (MAP ts'' (FILTER f pfx')))` by (
        qunabbrev_tac `ts''`
        >> rw[MEM_FILTER,MAP_MAP_o,SND_PAIR_MAP_o]
        >> `!ty. ~MEM (ty,Tyvar x) (FILTER f pfx')` by rw[MEM_FILTER]
        >> rw[MEM_MAP]
        >> CCONTR_TAC
        >> Cases_on `y`
        >> fs[]
        >> Cases_on `Tyvar x = r`
        >- (
          rveq
          >> first_x_assum (qspec_then `q` assume_tac)
          >> fs[]
        )
        >> Cases_on `r` >> fs[]
        >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
        >> fs[]
        >> Cases_on `MEM (Tyvar m') (MAP SND (pfx ++ [(Tyvar m,Tyvar x)] ++ sfx))`
        >- (
          imp_res_tac MEM_SPLIT_APPEND_SND_first
          >> qpat_x_assum `pfx ++  _ ++ _ = _` (fn x => REV_FULL_SIMP_TAC pure_ss [x] >> assume_tac x)
          >> (qspecl_then[`pfx''`,`[(q'',Tyvar m')]++sfx''`,`Tyvar m'`] assume_tac) TYPE_SUBST_reduce_list
          >> `!ty. ~MEM (ty,Tyvar m') pfx''` by (
            qpat_x_assum `~MEM _ (MAP SND pfx'')` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
            >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar m')` mp_tac) >> fs[]
          )
          >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
          >> rveq
          >> `pfx = pfx''` by (
            qpat_x_assum `pfx ++ _ ++ _ = _` mp_tac
            >> qpat_x_assum `ALL_DISTINCT (MAP FST pfx ++ _ ++ _)` mp_tac
            >> rpt (pop_assum kall_tac)
            >> rpt strip_tac
            >> fs[APPEND_EQ_APPEND,ALL_DISTINCT_APPEND]
            >> rveq >> fs[]
            >> fs[CONV_RULE(LHS_CONV SYM_CONV) APPEND_EQ_CONS]
            >> rveq >> fs[]
            >> first_x_assum (qspec_then `Tyvar m` assume_tac) >> fs[]
          )
          >> fs[]
        )
        >> qmatch_asmsub_abbrev_tac `~MEM (Tyvar m') (MAP SND ls)`
        >> (qspecl_then[`ls`,`[]`,`Tyvar m'`] assume_tac) TYPE_SUBST_reduce_list
        >> `!ty. ~MEM (ty,Tyvar m') ls` by (
          qpat_x_assum `~MEM _ (MAP SND ls)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
          >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar m')` mp_tac) >> fs[]
        )
        >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
        >> qunabbrev_tac `f`
        >> rveq
        >> qpat_x_assum `MEM (q,Tyvar m) (FILTER _ _)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_FILTER])
        >> qpat_x_assum `NULL _` assume_tac
        >> fs[NULL_FILTER,list_inter_def]
        >> first_x_assum (qspec_then `Tyvar m` assume_tac)
        >> fs[]
      )
      >> imp_res_tac MEM_SPLIT_APPEND_SND_first
      >> qmatch_goalsub_abbrev_tac `MAP ts'' (FILTER f pfx') ++ tup`
      >> (qspec_then`MAP ts'' (FILTER f pfx')` ((qspec_then `Tyvar m` assume_tac) o (CONV_RULE SWAP_FORALL_CONV))) TYPE_SUBST_reduce_list
      >> fs[tyvars_def]
      >> `!ty. ~MEM (ty,Tyvar m) (MAP ts'' (FILTER f pfx'))` by (
        qpat_x_assum `~MEM _ (MAP SND (MAP ts'' (FILTER f pfx')))` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
        >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar m)` mp_tac) >> fs[]
      )
      >> pop_assum (fn x => fs[x])
      >> first_x_assum (qspec_then `tup ⧺ MAP ts'' (FILTER f sfx') ⧺ l3 ⧺ l4 ⧺ l5 ⧺ pfx' ⧺ [(q',Tyvar x)] ⧺ sfx'` assume_tac)
      >> qunabbrev_tac `tup`
      >> fs[REV_ASSOCD_def]
    )
    >> (qspecl_then[`ts`,`[]`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar x) ts` by (
      qpat_x_assum `~MEM _ (MAP SND ts)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
      >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
    )
    >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
    >> rveq
    >> qmatch_goalsub_abbrev_tac `MAP f' (FILTER f ts)`
    >> `~MEM (Tyvar m) (MAP SND (MAP f' (FILTER f ts)))` by (
      unabbrev_all_tac
      >> rw[MAP_MAP_o,SND_PAIR_MAP_o]
      >> fs[Once (GSYM MAP_MAP_o)]
      >> (Q.ISPEC_THEN `ts` assume_tac) MAP_SND_FILTER
      >> first_x_assum (qspec_then `λy. MEM y (MAP SND pfx) \/ y = Tyvar x \/ MEM y (MAP SND sfx)` assume_tac)
      >> fs[AC DISJ_ASSOC DISJ_COMM]
      >> pop_assum kall_tac
      >> qmatch_goalsub_abbrev_tac `FILTER _ snd_ts`
      >> (qspecl_then [`snd_ts`,`pfx ++ [(Tyvar m,Tyvar x)] ++ sfx`,`pfx`,`sfx`,`x`,`m`] assume_tac) NOT_MEM_TYPE_SUBST_FILTER
      >> fs[non_triv_renaming_def,renaming_def,MAP_APPEND,AC DISJ_ASSOC DISJ_COMM]
      >> first_x_assum match_mp_tac
      >> fs[ELIM_UNCURRY]
    )
    >> (qspecl_then[`MAP f' (FILTER f ts)`,`l3 ++ l4 ++ l5 ++ ts`,`Tyvar m`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar m) (MAP f' (FILTER f ts))` by (
      qpat_x_assum `~MEM _ (MAP SND (MAP f' (FILTER f ts)))` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
      >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar m)` mp_tac) >> fs[]
    )
    >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
    >> `~MEM (Tyvar m) (MAP SND l3)` by (
      unabbrev_all_tac
      >> rw[MAP_MAP_o,FST_SWAP_SND]
      >> fs[ALL_DISTINCT_APPEND]
    )
    >> (qspecl_then[`l3`,`l4 ++ l5 ++ ts`,`Tyvar m`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar m) l3` by (
      qpat_x_assum `~MEM _ (MAP SND l3)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
      >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar m)` mp_tac) >> fs[]
    )
    >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
    >> qunabbrev_tac `l4`
    >> rw[SWAP_def,REV_ASSOCD_def]
  )
  (* case: ~MEM (Tyvar x) (MAP SND s) *)
  >> qmatch_goalsub_abbrev_tac `MAP (ts' ## I) s ++ ts'' ++ l1 ++ ts`
  >> `~MEM (Tyvar x) (MAP SND (MAP (ts' ## I) s))` by fs[MAP_MAP_o,SND_PAIR_MAP_o]
  >> (qspecl_then[`MAP (ts'##I) s`,`ts'' ++ l1 ++ ts`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
  >> `!ty. ~MEM (ty,Tyvar x) (MAP (ts' ## I) s)` by (
    qpat_x_assum `~MEM _ (MAP SND (MAP _ s))` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
    >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
  )
  >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
  >> pop_assum kall_tac
  >> qpat_x_assum `~MEM (Tyvar x) (MAP SND (MAP (ts' ## I) s))` kall_tac
  >> qunabbrev_tac `ts''`
  >> qunabbrev_tac `ts'`
  >> qmatch_goalsub_abbrev_tac `MAP f' (FILTER f ts)`
  >> `~MEM (Tyvar x) (MAP SND (MAP f' (FILTER f ts)))` by (
    qunabbrev_tac `f`
    >> rw[MAP_MAP_o,SND_PAIR_MAP_o,MEM_FILTER,MEM_MAP]
    >> Cases_on `Tyvar x = SND y` >> fs[]
    >> strip_tac
    >> Cases_on `~MEM y' ts` >> fs[]
    >> qmatch_goalsub_abbrev_tac `_ \/ b`
    >> Cases_on `~b` >> fs[]
    >> unabbrev_all_tac >> fs[]
    >> Cases_on `y` >> Cases_on `y'`
    >> fs[SWAP_def]
    >> qmatch_goalsub_abbrev_tac `a \/ _`
    >> Cases_on `a` >> fs[]
    >> match_mp_tac tyvars_diff_types
    >> rw[tyvars_def,tyvars_TYPE_SUBST]
    >> unabbrev_all_tac
    >> Cases_on `y''` >> fs[EVERY_MEM]
    >> last_assum drule >> strip_tac
    >> fs[tyvars_def]
    >> assume_tac (Q.ISPECL [`SND:(type#type)->type`,`s:((type,type) alist)`] MEM_MAP_f)
    >> first_x_assum drule
    >> rw[]
    >> qmatch_goalsub_abbrev_tac `a \/ _`
    >> Cases_on `a` >> fs[]
    >> unabbrev_all_tac
    >> imp_res_tac MEM_SPLIT_APPEND_SND_first
    >> (qspecl_then[`pfx`,`[(q,Tyvar n)]++sfx`,`Tyvar n`] assume_tac) TYPE_SUBST_reduce_list
    >> `!ty. ~MEM (ty,Tyvar n) pfx` by (
      qpat_x_assum `~MEM _ (MAP SND pfx)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
      >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar n)` mp_tac) >> fs[]
    )
    >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
    >> rveq
    >> last_assum (qspec_then `(q,Tyvar n)` assume_tac)
    >> first_x_assum drule
    >> fs[tyvars_def]
  )
  >> (qspecl_then[`MAP f' (FILTER f ts)`,`l1 ++ ts`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
  >> `!ty. ~MEM (ty,Tyvar x) (MAP f' (FILTER f ts))` by (
    qpat_x_assum `~MEM _ (MAP SND (MAP f' _))` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
    >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
  )
  >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
  >> pop_assum kall_tac
  >> fs[EVERY_MEM]
  >> first_x_assum drule
  >> disch_then (assume_tac o PURE_ONCE_REWRITE_RULE[GSYM FST_SWAP_SND])
  >> rfs[Once (GSYM MAP_MAP_o)]
  >> (qspecl_then[`l1`,`ts`,`Tyvar x`] assume_tac) TYPE_SUBST_reduce_list
  >> `!ty. ~MEM (ty,Tyvar x) l1` by (
    qpat_x_assum `~MEM _ (MAP SND l1)` (assume_tac o PURE_ONCE_REWRITE_RULE[MEM_MAP])
    >> strip_tac >> fs[] >> first_x_assum (qspec_then `(ty',Tyvar x)` mp_tac) >> fs[]
  )
  >> pop_assum (fn x => fs[x,tyvars_def,REV_ASSOCD_def])
QED

Theorem orth_ty_renaming_instance2:
  !ty1 ty2 s. non_triv_renaming s
  /\ NULL (list_inter (MAP FST s) (MAP SND s))
  /\ ALL_DISTINCT (MAP FST s)
  /\ EVERY (λx. ~MEM (Tyvar x) (MAP FST s)) (tyvars ty1)
  /\ (TYPE_SUBST s ty1 # ty2) ==> (ty1 # ty2)
Proof
  rw[renaming_def,non_triv_renaming_def]
  >> fs[orth_ty_def,GSYM RIGHT_FORALL_OR_THM,GSYM LEFT_FORALL_OR_THM]
  >> NTAC 2 strip_tac
  >> imp_res_tac renaming_undo_eq
  >> rfs[renaming_def,non_triv_renaming_def]
  >> first_x_assum (qspec_then `i` (assume_tac o GSYM))
  >> fs[]
QED

Theorem non_triv_normalise_tyvars_rec:
  !ty chr. non_triv_renaming (SND (normalise_tyvars_rec ty chr))
Proof
  rw[non_triv_renaming_def,normalise_tyvars_rec_ineq,normalise_tyvars_rec_renames,normalise_tyvars_rec_subst_snd_distinct]
QED

Theorem normalise_tyvars_rec_disj_dom_img:
  !ty chr. let s = SND (normalise_tyvars_rec ty chr) in
  NULL (list_inter (MAP FST s) (MAP SND s))
Proof
  rw[]
  >> (qspecl_then [`ty`,`chr`] assume_tac) non_triv_normalise_tyvars_rec
  >> (qspecl_then [`ty`,`chr`] assume_tac) normalise_tyvars_rec_differ
  >> fs[non_triv_renaming_def,renaming_def,NULL_FILTER,list_inter_def,EVERY_MEM]
  >> rw[MEM_MAP]
  >> qmatch_goalsub_abbrev_tac `_ \/ a`
  >> Cases_on `a` >> fs[]
  >> unabbrev_all_tac
  >> qmatch_asmsub_abbrev_tac `MAP SND s`
  >> last_x_assum imp_res_tac
  >> fs[ELIM_UNCURRY]
  >> first_x_assum (qspec_then `n'` assume_tac)
  >> fs[MEM_FLAT,MEM_MAP,PULL_EXISTS]
  >> first_x_assum (qspec_then `y'` mp_tac)
  >> rw[tyvars_def]
  >> first_x_assum (qspec_then `y''` mp_tac)
  >> rw[tyvars_def]
QED

Theorem normalise_tyvars_rec_subst_dist_fst:
  !ty chr. EVERY (λx. ¬MEM (Tyvar x) (MAP FST (SND (normalise_tyvars_rec ty chr)))) (tyvars ty)
Proof
  rw[EVERY_MEM]
  >> (qspecl_then [`ty`,`chr`] assume_tac) (CONJUNCT2 normalise_tyvars_rec_domain_imp)
  >> (qspecl_then [`ty`,`chr`] assume_tac) normalise_tyvars_rec_disj_dom_img
  >> fs[EVERY_MEM,NULL_FILTER,list_inter_def]
  >> first_x_assum match_mp_tac
  >> first_x_assum match_mp_tac
  >> rw[MEM_MAP_f]
QED

Theorem orth_ty_normalise:
  !ty1 ty2 chr1 chr2. (ty1 # ty2)
  = ((FST (normalise_tyvars_rec ty1 chr1)) # (FST (normalise_tyvars_rec ty2 chr2)))
Proof
  rw[EQ_IMP_THM,normalise_tyvars_rec_def]
  >- (match_mp_tac orth_ty_instances >> fs[])
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST s1 ty1`
  >> qmatch_asmsub_abbrev_tac `TYPE_SUBST s2 ty2`
  >> match_mp_tac orth_ty_renaming_instance2
  >> qexists_tac `s1`
  >> assume_tac non_triv_normalise_tyvars_rec
  >> assume_tac normalise_tyvars_rec_disj_dom_img
  >> assume_tac normalise_tyvars_rec_distinct_fst
  >> assume_tac normalise_tyvars_rec_subst_dist_fst
  >> reverse (rpt conj_tac)
  >- (
    match_mp_tac orth_ty_symm_imp
    >> match_mp_tac orth_ty_renaming_instance2
    >> qexists_tac `s2`
    >> fs[orth_ty_symm]
    >> fs[normalise_tyvars_rec_def]
    >> unabbrev_all_tac
    >> fs[]
  )
  >> unabbrev_all_tac
  >> fs[normalise_tyvars_rec_def]
QED

(* Unify two types and return two type substitutions as a certificate *)
val unify_types_def = Hol_defn "unify_types" `
  (unify_types [] sigma = SOME sigma)
  /\ (unify_types ((Tyapp a atys, Tyapp b btys)::l) sigma =
    if a = b /\ LENGTH atys = LENGTH btys
    then if atys = btys
      then unify_types l sigma (* trivial rule (for Tyapps) *)
      else unify_types ((ZIP (atys,btys))++l) sigma (* decomposition rule *)
    else NONE (* symbol clash *)
  )
  /\ (unify_types ((Tyapp a atys, Tyvar b)::l) sigma =
    unify_types ((Tyvar b, Tyapp a atys)::l) sigma (* orient rule *)
  )
  /\ (unify_types ((Tyvar a, ty)::l) sigma =
    if Tyvar a = ty
    then unify_types l sigma (* trivial rule (for Tyvars) *)
    else if MEM a (tyvars ty)
    then NONE (* occurs check *)
    else let
      subst_a = TYPE_SUBST [(ty,Tyvar a)];
      l' = MAP (subst_a ## subst_a) l;
      sigma' = MAP (subst_a ## I) sigma
    in unify_types l' ((ty, Tyvar a)::sigma') (* variable elimination *)
  )`;

Definition unify_types_measure:
  unify_types_measure = λ((tytups:(type,type)alist),(sigma:(type,type)alist)).
    let
      dist_tyvar = CARD (BIGUNION (set (MAP (UNCURRY $UNION) (MAP (W $## (set o $tyvars)) tytups))))
;
      acc_type_size = SUM (MAP ((UNCURRY $+) o (W $## $type_size')) tytups);
      num_shape = LENGTH (FILTER (λx. case x of (Tyapp _ _, Tyvar _) => T | _ => F) tytups)
    in (dist_tyvar, acc_type_size, num_shape)
End

val (unify_types_def,unify_types_ind) = Defn.tprove(
  unify_types_def,
  WF_REL_TAC `inv_image (prim_rec$< LEX (prim_rec$< LEX prim_rec$<)) unify_types_measure`
  >> strip_tac
  (* decomposition rule *)
  >- (
    rw[unify_types_measure]
    >> DISJ2_TAC
    >> rw[]
    >- (
      `!(x:(mlstring->bool)) y. x = y ==> CARD x = CARD y` by rw[]
      >> first_x_assum match_mp_tac
      >> `!(x:(mlstring->bool)) y a. x = y ==> x UNION a = y UNION a` by rw[]
      >> first_x_assum match_mp_tac
      >> rw[tyvars_def]
      >> pop_assum kall_tac
      >> pop_assum mp_tac
      >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`atys`,`btys`]
      >> Induct
      >> rw[]
      >> Cases_on `atys` >> fs[]
      >> rw[AC UNION_COMM UNION_ASSOC]
      >> `!(x:(mlstring->bool)) y a. x = y ==> a UNION x = a UNION y` by rw[]
      >> first_assum match_mp_tac
      >> first_x_assum match_mp_tac
      >> fs[AC UNION_COMM UNION_ASSOC]
    )
    >> DISJ1_TAC
    >> rw[type_size'_def,SUM_APPEND]
    >> pop_assum kall_tac
    >> pop_assum mp_tac
    >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`atys`,`btys`]
    >> Induct
    >> rw[type_size'_def]
    >> Cases_on `atys`
    >> fs[type_size'_def]
    >> first_x_assum drule
    >> fs[]
  )
  >> strip_tac
  (* trivial rule for Tyapps *)
  >- (
    rpt strip_tac
    >> qmatch_goalsub_abbrev_tac `fu < fu'`
    >> Cases_on `fu < fu'` >- fs[]
    >> DISJ2_TAC
    >> rw[unify_types_measure]
    >- (
      qunabbrev_tac `fu'`
      >> qunabbrev_tac `fu`
      >> fs[unify_types_measure]
      >> qmatch_asmsub_abbrev_tac `setset:(mlstring->bool)->bool`
      >> qmatch_asmsub_abbrev_tac `tys:(mlstring list)`
      >> fs[NOT_LESS]
      >> `FINITE (set (tys))` by rw[]
      >> `FINITE (BIGUNION setset)` by (
        qunabbrev_tac `setset`
        >> rw[]
        >> fs[MEM_MAP]
        >> Cases_on `y'`
        >> fs[ELIM_UNCURRY,FINITE_UNION]
      )
      >> `CARD (BIGUNION setset) <= CARD (set tys ∪ BIGUNION setset)` by (
        assume_tac (INST_TYPE [alpha |-> ``:mlstring``] CARD_SUBSET)
        >> first_x_assum (qspecl_then [`set tys UNION BIGUNION setset`] assume_tac)
        >> fs[]
      )
      >> fs[]
    )
    >> simp[type_size'_def]
  )
  >> strip_tac
  (* orient rule *)
  >- (
    rpt strip_tac
    >> qmatch_goalsub_abbrev_tac `fu < fu'`
    >> `fu = fu'` by (
      qunabbrev_tac `fu`
      >> qunabbrev_tac `fu'`
      >> rw[unify_types_measure,AC UNION_COMM UNION_ASSOC]
    )
    >> qmatch_goalsub_abbrev_tac `fsu < fsu'`
    >> `fsu = fsu'` by (
      qunabbrev_tac `fsu`
      >> qunabbrev_tac `fsu'`
      >> rw[unify_types_measure]
    )
    >> rw[unify_types_measure]
  )
  >> strip_tac
  (* variable elimination *)
  >- (
    rpt strip_tac
    >> DISJ1_TAC
    >> rw[unify_types_measure,tyvars_def]
    >> qmatch_goalsub_abbrev_tac `CARD (BIGUNION no_a_sets) < CARD (aa UNION tys UNION (BIGUNION (setset)))`
    >> `FINITE (aa UNION tys)` by (qunabbrev_tac `tys` >> qunabbrev_tac `aa` >> rw[FINITE_UNION])
    >> `FINITE (BIGUNION setset)` by (
      qunabbrev_tac `setset` >> rw[]
      >> fs[MEM_MAP] >> Cases_on `y'`
      >> fs[ELIM_UNCURRY,FINITE_UNION]
    )
    >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] CARD_PSUBSET)
    >> first_x_assum (qspecl_then [`aa UNION tys UNION BIGUNION setset`] mp_tac)
    >> rw[]
    >> first_x_assum (qspecl_then [`BIGUNION no_a_sets`] mp_tac)
    >> disch_then match_mp_tac
    >> `(BIGUNION no_a_sets) SUBSET (tys UNION BIGUNION setset)` by (
      qunabbrev_tac `tys`
      >> qunabbrev_tac `no_a_sets`
      >> qunabbrev_tac `setset`
      >> NTAC 2 (last_x_assum mp_tac)
      >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`a`,`ty`,`l`]
      >> Induct
      >- rw[]
      >> Cases
      >> rw[]
      >- (
        qmatch_goalsub_abbrev_tac `set (subst) SUBSET tys1 UNION (tysq UNION tysr UNION bigtys)`
        >> `set subst SUBSET tys1 UNION tysq` by (
          qunabbrev_tac `subst`
          >> qunabbrev_tac `tysq`
          >> qunabbrev_tac `tys1`
          >> rw[tyvars_TYPE_SUBST,SUBSET_DEF]
          >> Cases_on `x' = a'`
          >> fs[REV_ASSOCD_def,tyvars_def]
        )
        >> NTAC 3 (PURE_ONCE_REWRITE_TAC[UNION_ASSOC])
        >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (CONJUNCT1 SUBSET_UNION))
        >> first_x_assum (qspecl_then [`tys1 UNION tysq`,`tysr UNION bigtys`] assume_tac)
        >> ONCE_ASM_REWRITE_TAC[GSYM UNION_ASSOC]
        >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (SUBSET_TRANS))
        >> first_x_assum (qspecl_then [`set subst`,`tys1 UNION tysq`] match_mp_tac)
        >> fs[]
      )
      >- (
        rw[AC UNION_ASSOC UNION_COMM]
        >> qmatch_goalsub_abbrev_tac `set (subst) SUBSET tysq UNION (atysr UNION (atysty UNION zbigtys))`
        >> rw[AC UNION_ASSOC UNION_COMM]
        >> PURE_ONCE_REWRITE_TAC[UNION_ASSOC]
        >> `set subst SUBSET atysr UNION atysty` by (
          qunabbrev_tac `subst`
          >> qunabbrev_tac `atysr`
          >> qunabbrev_tac `atysty`
          >> rw[tyvars_TYPE_SUBST,SUBSET_DEF]
          >> Cases_on `x' = a'`
          >> fs[REV_ASSOCD_def,tyvars_def]
        )
        >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (CONJUNCT1 SUBSET_UNION))
        >> first_x_assum (qspecl_then [`atysr UNION atysty`,`tysq UNION zbigtys`] assume_tac)
        >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (SUBSET_TRANS))
        >> first_x_assum (qspecl_then [`set subst`,`atysr UNION atysty`] match_mp_tac)
        >> rw[]
      )
      >> first_x_assum drule
      >> disch_then assume_tac
      >> rw[AC UNION_ASSOC UNION_COMM]
      >> qmatch_goalsub_abbrev_tac `repltys SUBSET tysq UNION (tysr UNION (atysty UNION abigtys))`
      >> rw[AC UNION_ASSOC UNION_COMM]
      >> PURE_ONCE_REWRITE_TAC[UNION_ASSOC]
      >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (CONJUNCT1 SUBSET_UNION))
      >> first_x_assum (qspecl_then [`abigtys UNION atysty`,`tysq UNION tysr`] assume_tac)
      >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (SUBSET_TRANS))
      >> first_x_assum (qspecl_then [`repltys`,`abigtys UNION atysty`] match_mp_tac)
      >> rw[]
      >> rfs[AC UNION_ASSOC UNION_COMM]
    )
    >> `~(a IN (BIGUNION no_a_sets))` by (
      rw[IN_BIGUNION]
      >> Cases_on `s IN no_a_sets` >> fs[]
      >> qunabbrev_tac `no_a_sets`
      >> qunabbrev_tac `tys`
      >> fs[MEM_MAP]
      >> Cases_on `y''`
      >> fs[ELIM_UNCURRY]
      >> rw[tyvars_TYPE_SUBST]
      >> Cases_on `MEM x (tyvars q)` >> fs[]
      >> Cases_on `x = a`
      >> rw[REV_ASSOCD_def,tyvars_def]
      >> fs[]
    )
    >> ONCE_REWRITE_TAC[PSUBSET_EQN]
    >> `BIGUNION no_a_sets ⊆ aa ∪ tys ∪ BIGUNION setset` by (
      rw[AC UNION_ASSOC UNION_COMM]
      >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] (CONJUNCT2 SUBSET_UNION))
      >> first_x_assum (qspecl_then [`tys ∪ BIGUNION setset`,`aa`] assume_tac)
      >> assume_tac (INST_TYPE [alpha |-> ``:mlstring``] SUBSET_TRANS)
      >> first_x_assum (qspecl_then [`BIGUNION no_a_sets`,`tys UNION BIGUNION setset`,`aa UNION (tys UNION BIGUNION setset)`] assume_tac)
      >> fs[]
    )
    >> qunabbrev_tac `aa`
    >> fs[]
  )
  (* trivial rule (for variables) *)
  >- (
    rpt strip_tac
    >> qmatch_goalsub_abbrev_tac `fu < fu'`
    >> Cases_on `fu < fu'` >- fs[]
    >> fs[NOT_LESS]
    >> rw[unify_types_measure]
    >- (
      qunabbrev_tac `fu'`
      >> qunabbrev_tac `fu`
      >> fs[unify_types_measure]
      >> qmatch_asmsub_abbrev_tac `setset:(mlstring->bool)->bool`
      >> qmatch_asmsub_abbrev_tac `tys:(mlstring list)`
      >> `FINITE (set (tys))` by rw[]
      >> `FINITE (BIGUNION setset)` by (
        qunabbrev_tac `setset`
        >> rw[]
        >> fs[MEM_MAP]
        >> Cases_on `y'`
        >> fs[ELIM_UNCURRY,FINITE_UNION]
      )
      >> `CARD (BIGUNION setset) <= CARD (set tys ∪ BIGUNION setset)` by (
        assume_tac (INST_TYPE [alpha |-> ``:mlstring``] CARD_SUBSET)
        >> first_x_assum (qspecl_then [`set tys UNION BIGUNION setset`] assume_tac)
        >> fs[]
      )
      >> fs[]
    )
    >> simp[type_size'_def]
  )
);

Theorem MEM_ZIP_EQTUP_MAP[local]:
  !l1 l2 f. LENGTH l1 = LENGTH l2
  /\ (!e1 e2. MEM (e1,e2) (ZIP (l1,l2)) ==> f e1 = f e2)
  ==> MAP f l1 = MAP f l2
Proof
  Induct >- (Cases >> fs[]) >> strip_tac >> Cases >> fs[]
QED

(* A substitution is idempotent iff Dom s ∩ tyvars( CoDom s ) = ∅ *)
Theorem TYPE_SUBST_idempotent:
  !s. EVERY (λ(y,x). (?a. Tyvar a = x /\ x <> y)) s /\ ALL_DISTINCT (MAP SND s)
  ==> (TYPE_SUBST s = (TYPE_SUBST s o TYPE_SUBST s))
  = NULL (list_inter (MAP SND s) (FLAT (MAP ((MAP Tyvar) o tyvars o FST) s)))
Proof
  rw[EQ_IMP_THM,FUN_EQ_THM]
  >- (
    rw[NULL_FILTER,EVERY_FILTER,list_inter_def]
    >> CCONTR_TAC
    >> fs[MEM_FLAT,MEM_MAP]
    >> Cases_on `y`
    >> rveq
    >> fs[MEM_MAP]
    >> rveq
    >> Cases_on `y'`
    >> Cases_on `y''`
    >> fs[]
    >> rveq
    >> assume_tac (Q.SPECL [`s`,`r`,`q`] TYPE_SUBST_MEM)
    >> rfs[]
    >> first_x_assum (qspec_then `r` mp_tac)
    >> simp[]
    >> pop_assum kall_tac
    >> CCONTR_TAC
    >> fs[]
    >> pop_assum (mp_tac o CONV_RULE(LHS_CONV(PURE_ONCE_REWRITE_CONV [GSYM TYPE_SUBST_NIL])))
    >> rw[TYPE_SUBST_tyvars]
    >> asm_exists_tac
    >> assume_tac (Q.SPECL [`s`,`Tyvar m`,`q'`] TYPE_SUBST_MEM)
    >> fs[EVERY_MEM]
    >> res_tac
    >> fs[ELIM_UNCURRY]
    >> rw[REV_ASSOCD_def]
  )
  >> rw[]
  >> `!x. TYPE_SUBST s (Tyvar x) = TYPE_SUBST s (TYPE_SUBST s (Tyvar x))` by (
    strip_tac
    >> qmatch_asmsub_abbrev_tac `NULL (list_inter dom_s img_s)`
    >> Cases_on `~MEM (Tyvar x) dom_s`
    >> qunabbrev_tac `dom_s`
    >- (
      `~?b. MEM (b, Tyvar x) s` by (
        rw[] >> fs[MEM_MAP]
        >> first_x_assum (qspec_then `(b,Tyvar x)` mp_tac)
        >> fs[]
      )
      >> drule TYPE_SUBST_NOT_MEM
      >> disch_then (qspec_then `x` mp_tac)
      >> fs[]
    )
    >> Cases_on `~MEM (Tyvar x) img_s`
    >> qunabbrev_tac `img_s`
    >- (
      rw[TYPE_SUBST_compose,REV_ASSOCD_self_append]
      >> fs[MEM_MAP]
      >> Cases_on `y`
      >> fs[]
      >> rveq
      >> PURE_ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
      >> drule TYPE_SUBST_MEM
      >> disch_then (qspecl_then [`Tyvar x`,`q`] assume_tac)
      >> rfs[]
      >> pop_assum kall_tac
      >> fs[MEM_SPLIT]
      >> qmatch_goalsub_abbrev_tac `MAP l1_subs l1`
      >> `~?b. MEM (b,Tyvar x) (MAP l1_subs l1)` by (
        fs[ALL_DISTINCT_APPEND,MEM_MAP]
        >> rw[]
        >> Cases_on `y`
        >> qunabbrev_tac `l1_subs`
        >> rw[PAIR_MAP_THM]
        >> qpat_x_assum `!x. _ \/ _` (qspec_then `(q',r)` mp_tac)
        >> rw[]
        >> fs[]
      )
      >> PURE_ONCE_REWRITE_TAC[GSYM TYPE_SUBST_def]
      >> qmatch_goalsub_abbrev_tac `_ = TYPE_SUBST (_ ++ ts ++ _) _`
      >> assume_tac (Q.SPECL [`MAP l1_subs (l1:((type,type)alist))`,
        `ts ++ (MAP l1_subs (l2:((type,type)alist)))`,`Tyvar x`] TYPE_SUBST_reduce_list)
      >> rfs[tyvars_def]
      >> pop_assum kall_tac
      >> qunabbrev_tac `ts`
      >> rw[REV_ASSOCD_def]
      >> fs[NULL_list_inter_APPEND,NULL_list_inter_APPEND1]
      (* >> rpt(qpat_x_assum `NULL (list_inter _ (MAP Tyvar (tyvars q)))` mp_tac)
      >> rpt(qpat_x_assum `NULL _` kall_tac) *)
      >> fs[NULL_FILTER,list_inter_def]
      >> assume_tac (Q.SPECL [`l1 ⧺ [(q,Tyvar x)] ⧺ l2`,`[]`,`q`] TYPE_SUBST_reduce_list)
      >> RULE_ASSUM_TAC GSYM
      >> fs[]
      >> first_x_assum match_mp_tac
      >> rpt strip_tac
      >- (
        qpat_x_assum `!x. MEM _ (MAP Tyvar _) ==> ~MEM _ (MAP SND l1)` (qspec_then `Tyvar a` mp_tac)
        >> rw[MEM_MAP]
        >> qexists_tac `(ty,Tyvar a)`
        >> fs[]
      )
      >- (CCONTR_TAC >> fs[MEM_MAP])
      >- (
        qpat_x_assum `!x. MEM _ (MAP Tyvar _) ==> ~MEM _ (MAP SND l2)` (qspec_then `Tyvar a` mp_tac)
        >> rw[MEM_MAP]
        >> qexists_tac `(ty,Tyvar a)`
        >> fs[]
      )
    )
    >> fs[NULL_FILTER,list_inter_def]
    >> first_x_assum drule
    >> fs[]
  )
  >> fs[TYPE_SUBST_compose,TYPE_SUBST_tyvars]
QED

Theorem MEM_tyvars_Tyapp[local]:
  !tys a b. ~NULL (MAP tyvars tys) ==>
  (?n. MEM a n /\ MEM n (MAP tyvars tys)) = MEM a (tyvars (Tyapp b tys))
Proof
  rw[tyvars_def,MEM_MAP,MEM_FOLDR_LIST_UNION]
  >> EQ_TAC >> rw[]
  >> asm_exists_tac >> fs[]
  >> qexists_tac `y` >> fs[]
QED

Definition unify_def:
  unify ty1 ty2 =
    let
      (t1,s1) = normalise_tyvars_rec ty1 #"a";
      (t2,s2) = normalise_tyvars_rec ty2 #"b";
      sigma = unify_types [(t1,t2)] [];
      (* tyin2 o tyin1 = *)
      o_tyinst tyin2 tyin1 = (MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2
    in if IS_SOME sigma
      then SOME (o_tyinst (THE sigma) s1, o_tyinst (THE sigma) s2)
      else NONE
End

(* Soundness of unify_types *)

val (equal_upto_rules,equal_upto_ind,equal_upto_cases) = Hol_reln `
  (!l a. equal_upto l a a) /\
  (!l a b. MEM (a,b) l ==> equal_upto l a b) /\
  (!l a b. MEM (a,b) l ==> equal_upto l b a) /\
  (!l n args1 args2.
    LENGTH args1 = LENGTH args2 /\
    LIST_REL (equal_upto l) args1 args2
    ==>
    equal_upto l (Tyapp n args1) (Tyapp n args2))
  `

val [equal_upto_refl,equal_upto_l1,equal_upto_l2,equal_upto_tyapp] =
    map save_thm (zip ["equal_upto_refl","equal_upto_l1","equal_upto_l2","equal_upto_tyapp"]
                      (CONJUNCTS equal_upto_rules));

Theorem equal_upto_nil:
  !ty1 ty2. equal_upto [] ty1 ty2 ==> ty1 = ty2
Proof
  `!l ty1 ty2. equal_upto l ty1 ty2 ==> l = [] ==> ty1 = ty2`
    suffices_by metis_tac[]
  \\ ho_match_mp_tac equal_upto_ind \\  fs[]
  \\ CONV_TAC(DEPTH_CONV ETA_CONV) \\ fs[quotient_listTheory.LIST_REL_EQ]

QED

Theorem equal_upto_eq:
  !a l. equal_upto ((a,a)::l) = equal_upto l
Proof
  `(!l ty1 ty2. equal_upto l ty1 ty2 ==> !l' a. l = (a,a)::l' ==> equal_upto l' ty1 ty2)
   /\ (!l ty1 ty2. equal_upto l ty1 ty2 ==> !a. equal_upto ((a,a)::l) ty1 ty2)
  `
    suffices_by(rw[FUN_EQ_THM,EQ_IMP_THM] \\ metis_tac[])
  \\ conj_tac \\ ho_match_mp_tac equal_upto_ind \\ rpt strip_tac
  \\ fs[equal_upto_rules]
  \\ match_mp_tac equal_upto_tyapp
  \\ RULE_ASSUM_TAC (CONV_RULE(DEPTH_CONV ETA_CONV)) \\ simp[]
  \\ qhdtm_x_assum `LIST_REL` mp_tac \\ match_mp_tac EVERY2_mono
  \\ rw[]
QED

Theorem equal_upto_zip:
  !a atys btys l ty1 ty2. equal_upto ((Tyapp a atys,Tyapp a btys)::l) ty1 ty2
     /\ LENGTH atys = LENGTH btys
     ==> equal_upto (ZIP (atys,btys) ⧺ l) ty1 ty2
Proof
  `!l ty1 ty2.
    equal_upto l ty1 ty2
    ==> !a atys btys l'. l = (Tyapp a atys,Tyapp a btys)::l' /\ LENGTH atys = LENGTH btys
                         ==> equal_upto (ZIP (atys,btys) ++ l') ty1 ty2`
    suffices_by metis_tac[]
  \\ ho_match_mp_tac equal_upto_ind \\ rpt strip_tac
  \\ fs[equal_upto_rules]
  \\ match_mp_tac equal_upto_tyapp \\ fs[]
  \\ TRY(qhdtm_x_assum `LIST_REL` mp_tac \\ match_mp_tac EVERY2_mono
         \\ rw[] \\ NO_TAC)
  \\ fs[LIST_REL_EVERY_ZIP,EVERY_MEM] \\ Cases \\ rw[]
  >- (match_mp_tac equal_upto_l1 \\ simp[])
  >- (match_mp_tac equal_upto_l2 \\ rfs[MEM_ZIP] \\ metis_tac[])
QED

Theorem equal_upto_swap:
  !a b l ty1 ty2. equal_upto ((a,b)::l) ty1 ty2
     ==> equal_upto ((b,a)::l) ty1 ty2
Proof
  `!l ty1 ty2.
    equal_upto l ty1 ty2
    ==> !a b l'. l = (a,b)::l'
                         ==> equal_upto ((b,a)::l') ty1 ty2`
    suffices_by metis_tac[]
  \\ ho_match_mp_tac equal_upto_ind \\ rpt strip_tac
  \\ fs[equal_upto_rules]
  \\ match_mp_tac equal_upto_tyapp \\ fs[]
  \\ RULE_ASSUM_TAC (CONV_RULE(DEPTH_CONV ETA_CONV)) \\ simp[]
QED

(* subtype of a at a path p *)
Definition subtype_at_def:
  (subtype_at a [] = SOME a) /\
  (subtype_at (Tyapp a aty) ((name,n)::p) =
    if (a = name) /\ ((n:num) < LENGTH aty)
    then subtype_at (EL n aty) p else NONE) /\
  (subtype_at _ _ = NONE)
End

Theorem subtype_at_TYPE_SUBST:
  !x p s a. subtype_at x p = SOME a
  ==> subtype_at (TYPE_SUBST s x) p = SOME (TYPE_SUBST s a)
Proof
  ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> rw[subtype_at_def]
  >> rfs[]
  >> first_x_assum (qspec_then `s` assume_tac)
  >> rw[EL_MAP]
QED

Theorem subtype_at_eq:
  !x y. (x = y) = (!p. subtype_at x p = subtype_at y p)
Proof
  ho_match_mp_tac type_ind
  >> rw[EQ_IMP_THM]
  >> first_x_assum (qspec_then `[]` mp_tac)
  >> fs[subtype_at_def]
QED

Theorem subtype_at_Tyvar:
  !p a. IS_SOME (subtype_at (Tyvar a) p) = NULL p
Proof
  Induct >> fs[subtype_at_def]
QED

Theorem subtype_at_IS_SOME_parent[local]:
  !x p q. IS_SOME (subtype_at x (p ++ q)) ==> IS_SOME (subtype_at x p)
Proof
  Induct_on `p`
  >> fs[subtype_at_def]
  >> Cases
  >> ho_match_mp_tac type_ind
  >> fs[subtype_at_Tyvar]
  >> rw[]
  >> Cases_on `m = q /\ r < LENGTH l`
  >> fs[subtype_at_def]
  >- last_x_assum imp_res_tac
  >> fs[subtype_at_def]
QED

Theorem subtype_at_NONE_child[local]:
  !x p q. IS_NONE (subtype_at x p) ==> IS_NONE (subtype_at x (p ++ q))
Proof
  CCONTR_TAC
  >> fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_NONE_EQ_NONE]
  >> imp_res_tac subtype_at_IS_SOME_parent
  >> fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
QED

Theorem subtype_at_decomp_path:
  !ty1 p q ty2. subtype_at ty1 p = SOME ty2 ==> subtype_at ty1 (p++q) = subtype_at ty2 q
Proof
  ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> rw[subtype_at_def]
QED

Theorem subtype_at_eq:
  !x y. (subtype_at x p = subtype_at y q) = (!r. subtype_at x (p++r) = subtype_at y (q++r))
Proof
  rw[EQ_IMP_THM]
  >- (
    Cases_on `subtype_at y q`
    >> imp_res_tac (REWRITE_RULE[option_CLAUSES] subtype_at_NONE_child)
    >> imp_res_tac subtype_at_decomp_path
    >> fs[]
  )
  >- (
    first_x_assum (qspec_then `[]` assume_tac)
    >> fs[]
  )
QED

val subtype_at_eq' = GEN_ALL (SPECL (map Term [`p:(mlstring#num) list`,`p:(mlstring#num) list`]) (GEN_ALL subtype_at_eq''));

Theorem subtype_at_eqs_imp[local]:
  !t t' p q r. subtype_at t p = subtype_at t' q
  ==> subtype_at t (p++r) = subtype_at t' (q++r)
Proof
  rw[fst (EQ_IMP_RULE (SPEC_ALL subtype_at_eq''))]
QED

Theorem subtype_at_trans:
  !x p y p' z. subtype_at x p = SOME y /\  subtype_at y p' = SOME z
  ==> subtype_at x (p++p') = SOME z
Proof
  ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> rw[subtype_at_def]
QED

Theorem subtype_at_tyvars:
  !x p a. subtype_at x p = SOME (Tyvar a) ==> MEM a (tyvars x)
Proof
  ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> rw[subtype_at_def,tyvars_def,MEM_FOLDR_LIST_UNION]
  >> rfs[]
  >> qexists_tac `EL n aty`
  >> fs[]
  >> fs[MEM_EL]
  >> asm_exists_tac
  >> fs[]
QED

Theorem subtype_at_tyvars:
  !x a. (?p. subtype_at x p = SOME (Tyvar a)) = MEM a (tyvars x)
Proof
  ho_match_mp_tac type_ind
  >> rw[subtype_at_def,tyvars_def,MEM_FOLDR_LIST_UNION]
  >- (
    rw[EQ_IMP_THM,subtype_at_def]
    >- (Cases_on `p` >> fs[subtype_at_def])
    >> qexists_tac `[]`
    >> fs[subtype_at_def]
  )
  >> rw[EQ_IMP_THM]
  >- (
    pop_assum mp_tac
    >> Induct_on `p`
    >- fs[subtype_at_def]
    >> fs[EVERY_MEM,EQ_IMP_THM,subtype_at_def]
    >> rw[]
    >> Cases_on `h` >> Cases_on `r` >> Cases_on `l` >> fs[subtype_at_def]
    >- metis_tac[]
    >> qexists_tac `EL n t`
    >> first_x_assum (qspec_then `EL n t` mp_tac)
    >> rw[MEM_EL]
    >> metis_tac[subtype_at_trans]
  )
  >> fs[EVERY_MEM]
  >> first_x_assum drule
  >> disch_then (qspec_then `a` assume_tac)
  >> `?n. subtype_at (Tyapp m l) [n] = SOME y` by (
    fs[MEM_EL]
    >> qexists_tac `(m,n)`
    >> fs[subtype_at_def]
  )
  >> rfs[]
  >> (qspecl_then [`Tyapp m l`,`[n]`,`y`,`p`,`Tyvar a`] drule) subtype_at_trans
  >> rw[]
  >> asm_exists_tac
  >> rw[]
QED

Theorem subtype_at_MEM:
  !e l m. MEM e l ==> ?n. subtype_at (Tyapp m l) [n] = SOME e
Proof
  rw[MEM_EL] >> qexists_tac `(m,n)` >> fs[subtype_at_def]
QED

Theorem subtype_at_Tyvar_neg:
  !p a. (subtype_at (Tyvar a) p = NONE) = ~NULL p
Proof
  Induct >> fs[subtype_at_def]
QED

Theorem subtype_at_Tyapp:
  !p a. ~NULL p ==> (subtype_at (Tyapp a []) p = NONE)
Proof
  rw[subtype_at_def,NULL_EQ]
  >> Cases_on `p`
  >> fs[]
  >> Cases_on `h`
  >> Cases_on `a = q /\ r < LENGTH []`
  >> fs[subtype_at_def]
QED

Theorem subtype_at_THE_subtype_at[local]:
  !x p q. IS_SOME (subtype_at x p) ==> subtype_at (THE (subtype_at x p)) q = subtype_at x (p++q)
Proof
  ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> rw[subtype_at_def]
QED

Theorem subtype_at_type_size:
  !ty1 p ty2. subtype_at ty1 p = SOME ty2 ==> type_size ty1 >= type_size ty2
Proof
  ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> fs[subtype_at_def,type_size_def]
  >> rpt strip_tac >> fs[]
  >> `MEM (EL n aty) aty` by (rw[MEM_EL] >> qexists_tac `n` >> fs[])
  >> imp_res_tac type1_size_mem
  >> fs[]
QED

Theorem subtype_at_cyclic:
  !ty p. NULL p = (subtype_at ty p = SOME ty)
Proof
  fs[EQ_IMP_THM]
  >> ho_match_mp_tac (fetch "-" "subtype_at_ind")
  >> fs[subtype_at_def]
  >> rw[]
  >> Cases_on `n < LENGTH aty` >> fs[]
  >> Cases_on `~IS_SOME (subtype_at (EL n aty) p)` >> fs[]
  >> `!(f:type option->num) x y. f x <> f y ==> x <> y` by (rw[] >> CCONTR_TAC >> rw[])
  >> pop_assum match_mp_tac
  >> qexists_tac `type_size o THE`
  >> fs[type_size_def,IS_SOME_EXISTS]
  >> imp_res_tac subtype_at_type_size
  >> `MEM (EL n aty) aty` by (rw[MEM_EL] >> qexists_tac `n` >> fs[])
  >> imp_res_tac type1_size_mem
  >> fs[]
QED

(* subtype_at leaf *)
Definition is_subtype_leaf_def:
  is_subtype_leaf ty p = (IS_SOME (subtype_at ty p)
    /\ !q. ~NULL q = IS_NONE (subtype_at ty (p++q)))
End

Theorem subtype_at_leaf_imp[local]:
  (!x p q a y. subtype_at x p = SOME (Tyvar a)
  /\ subtype_at x (p++q) = SOME y ==> NULL q)
  /\ (!x p q a y. subtype_at x p = SOME (Tyapp a [])
  /\ subtype_at x (p++q) = SOME y ==> NULL q)
Proof
  rw[]
  >> imp_res_tac subtype_at_decomp_path
  >> pop_assum (qspec_then `q` assume_tac)
  >- (
    qspecl_then [`q`,`a`] assume_tac subtype_at_Tyvar
    >> fs[IS_SOME_EXISTS]
    >> rfs[]
  )
  >- (
    Cases_on `NULL q`
    >> fs[]
    >> imp_res_tac subtype_at_Tyapp
    >> pop_assum (qspec_then `a` assume_tac)
    >> rfs[]
  )
QED

Theorem is_subtype_leaf_def[local]:
  !x p. is_subtype_leaf x p = !q. IS_SOME (subtype_at x (p++q)) = NULL q
Proof
  rw[is_subtype_leaf_def,EQ_IMP_THM,NULL_EQ,quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
  >> CCONTR_TAC
  >> fs[]
  >> qpat_x_assum `!p. _` imp_res_tac
QED

Theorem is_subtype_leaf_IS_SOME_subtype[local]:
  !x p. is_subtype_leaf x p ==> IS_SOME (subtype_at x p)
Proof
  fs[is_subtype_leaf_def]
QED

Theorem is_subtype_leaf_Tyapp:
  !p m l. is_subtype_leaf (Tyapp m l) p ==> (NULL l = NULL p)
Proof
  Cases
  >> rw[subtype_at_def,is_subtype_leaf_def,NULL_EQ,EQ_IMP_THM]
  >> TRY (Cases_on `l`)
  >> TRY (Cases_on `q`)
  >> TRY (Cases_on `h`)
  >> fs[subtype_at_def,is_subtype_leaf_def,NULL_EQ]
  >> (
    first_x_assum (qspec_then `(m,0)::[]` assume_tac)
    >> fs[subtype_at_def]
  )
QED

Theorem is_subtype_leaf_Tyvar:
  !p a. is_subtype_leaf (Tyvar a) p = NULL p
Proof
  rw[]
  >> rw[subtype_at_def,is_subtype_leaf_def,subtype_at_Tyvar]
  >> Cases_on `NULL p`
  >> fs[NULL_EQ]
  >> assume_tac (ccontr_equiv (subtype_at_Tyvar))
  >> pop_assum (assume_tac o ONCE_REWRITE_RULE[NOT_IS_SOME_EQ_NONE])
  >> fs[NULL_EQ]
QED


Theorem is_subtype_leaf_eq:
  !t p. is_subtype_leaf t p = (?a. subtype_at t p = SOME (Tyvar a) \/ subtype_at t p = SOME (Tyapp a []))
Proof
  rw[is_subtype_leaf_def,EQ_IMP_THM,IS_SOME_EXISTS]
  >> fs[]
  >- (
    Cases_on `x`
    >> fs[]
    >> Cases_on `l`
    >> first_x_assum (qspec_then `[(m,0)]` assume_tac)
    >> imp_res_tac subtype_at_decomp_path
    >> fs[subtype_at_def]
  )
  >> imp_res_tac subtype_at_decomp_path
  >> rw[subtype_at_def,subtype_at_Tyvar_neg,subtype_at_Tyapp]
  >> pop_assum (fn x => fs[x])
  >- fs[subtype_at_Tyvar_neg]
  >> Cases_on `q`
  >> fs[subtype_at_def]
  >> Cases_on `h`
  >> fs[subtype_at_def]
QED

Theorem is_subtype_leaf_all_types:
  !t. ?p. is_subtype_leaf t p
Proof
  ho_match_mp_tac type_ind
  >> rw[]
  >- (
    qexists_tac `[]`
    >> fs[is_subtype_leaf_Tyvar,NULL_EQ]
  )
  >> Cases_on `NULL l`
  >- (
    qexists_tac `[]`
    >> fs[is_subtype_leaf_eq,NULL_EQ,EXISTS_OR_THM,subtype_at_def]
  )
  >> fs[EVERY_MEM,NOT_NULL_MEM]
  >> last_x_assum imp_res_tac
  >> fs[MEM_EL]
  >> rveq
  >> qexists_tac `(m,n)::p`
  >> fs[is_subtype_leaf_def',subtype_at_def]
QED

Theorem subtype_leaf_above_or_below[local]:
  !x p. ?q r. (p = q ++ r \/ q = p ++ r) ==> is_subtype_leaf x q
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rw[is_subtype_leaf_Tyvar,NULL_EQ]
    >> qexists_tac `[]`
    >> qexists_tac `p`
    >> fs[]
  )
  >> Cases
  >- (
    rw[is_subtype_leaf_eq]
    >> qexists_tac `[]`
    >> qexists_tac `p`
    >> fs[]
    >> qexists_tac `m`
    >> fs[subtype_at_def]
  )
  >> rw[]
  >> Cases_on `p`
  >- (
    (qspecl_then [`Tyapp m (h::t)`] assume_tac) is_subtype_leaf_all_types
    >> fs[]
    >> NTAC 2 (qexists_tac `p`)
    >> fs[]
  )
  >> fs[EVERY_MEM,PULL_FORALL]
  >> Cases_on `h'`
  >> Cases_on `q = m /\ r < LENGTH (h::t)`
  >> fs[]
  >- (
    Cases_on `r = 0`
    >- (
      last_x_assum (qspec_then `t'` assume_tac)
      >> fs[]
      >> qexists_tac `(m,0)::q'`
      >> qexists_tac `r'`
      >> fs[is_subtype_leaf_def',subtype_at_def]
      >> rw[]
      >> fs[]
    )
    >> first_x_assum (qspecl_then [`EL (PRE r) t`,`t'`] assume_tac)
    >> fs[MEM_EL,NOT_ZERO_LT_ZERO]
    >> `PRE r < LENGTH t` by fs[]
    >> qpat_x_assum `_ ==> _` imp_res_tac
    >> fs[]
    >> qexists_tac `(m,r)::q'`
    >> qexists_tac `r'`
    >> fs[is_subtype_leaf_def',subtype_at_def,EL_CONS]
    >> rw[]
    >> fs[]
  )
  >> qexists_tac `[]`
  >> qexists_tac `[]`
  >> fs[is_subtype_leaf_def',subtype_at_def]
QED

Theorem subtype_has_leaf[local]:
  !x y p q. (!p. is_subtype_leaf x p \/ is_subtype_leaf y p ==> subtype_at x p = subtype_at y p)
  /\ subtype_at x p = NONE /\ IS_SOME (subtype_at y (p ⧺ q)) ==> (NONE = subtype_at y p)
Proof
  CCONTR_TAC
  >> fs[is_subtype_leaf_def]
  >> (qspecl_then [`x`,`p`] assume_tac) subtype_at_NONE_child
  >> (qspecl_then [`THE (subtype_at y (p++q))`] assume_tac) is_subtype_leaf_all_types
  >> fs[GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,is_subtype_leaf_def,NULL_EQ]
  >> last_x_assum (qspec_then `p++q++p'` assume_tac)
  >> (qspecl_then [`y`,`p++q`] assume_tac) subtype_at_THE_subtype_at
  >> rfs[]
  >> fs[]
  >> rfs[]
  >> qpat_x_assum `!q. subtype_at x _ = _` (qspec_then `q++p'` assume_tac)
  >> fs[]
  >> qpat_x_assum `NONE = _` (assume_tac o GSYM)
  >> fs[IS_SOME_DEF]
QED

Theorem is_subtype_leaf_eq:
  !x y. (x = y) = (!p. (is_subtype_leaf x p \/ is_subtype_leaf y p)
  ==> subtype_at x p = subtype_at y p)
Proof
  fs[EQ_IMP_THM,subtype_at_eq]
  >> ho_match_mp_tac type_ind
  >> strip_tac
  >> rw[]
  >- (
    fs[subtype_at_eq,is_subtype_leaf_Tyvar]
    >> rw[]
    >> Cases_on `p`
    >> fs[subtype_at_def]
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> fs[subtype_at_def,subtype_at_Tyvar]
    >> (qspec_then `h::t` assume_tac) subtype_at_Tyvar
    >> fs[NULL_EQ]
    >> rveq
    >> fs[]
  )
  >> Cases_on `y`
  >- (
    first_x_assum (qspec_then `[]` assume_tac)
    >> fs[is_subtype_leaf_Tyvar,subtype_at_def]
  )
  >> Cases_on `NULL l`
  >> Cases_on `NULL l'`
  >- (
    fs[NULL_EQ]
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> fs[is_subtype_leaf_eq,subtype_at_def]
  )
  >- (
    fs[NULL_EQ]
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> fs[is_subtype_leaf_eq,subtype_at_def]
  )
  >- (
    fs[NULL_EQ]
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> fs[is_subtype_leaf_eq,subtype_at_def]
  )
  >> fs[EVERY_MEM,Once PULL_FORALL]
  >> Cases_on `m = m'`
  >> fs[]
  >- (
    Cases_on `LENGTH l = LENGTH l'`
    >> fs[]
    >- (
      Cases_on `l = l'`
      >> fs[]
      >> (Q.ISPECL_THEN [`l:type list`,`l'`,`I:type->type`,`I:type->type`] assume_tac) (ccontr_equiv(MAP_EQ_EVERY2))
      >> rfs[MAP_ID,LIST_REL_EVERY_ZIP]
      >> fs[EXISTS_MEM]
      >> assume_tac (Q.ISPECL [`l':type list`,`l:type list`,`e:type#type`] MEM_ZIP)
      >> rfs[]
      >> rveq
      >> qpat_x_assum `LENGTH l = LENGTH _` (assume_tac o GSYM)
      >> last_x_assum (qspecl_then [`EL n l`,`EL n l'`] assume_tac)
      >> pop_assum (assume_tac o REWRITE_RULE[MEM_EL])
      >> fs[]
      >> pop_assum imp_res_tac
      >> fs[GSYM subtype_at_eq]
      >> rfs[]
      >> last_x_assum (qspec_then `(m,n)::p'` assume_tac)
      >> fs[is_subtype_leaf_def',subtype_at_def]
      >> rfs[]
    )
    (* LENGTH l <> LENGTH l' *)
    >> Cases_on `LENGTH l < LENGTH l'`
    >> fs[]
    >> TRY (imp_res_tac LESS_CASES_IMP)
    >> qmatch_assum_abbrev_tac `LENGTH sl < LENGTH ll`
    >> (qspecl_then [`LAST ll`] assume_tac) is_subtype_leaf_all_types
    >> fs[]
    >> first_x_assum (qspec_then `(m,PRE (LENGTH ll))::p'` assume_tac)
    >> fs[is_subtype_leaf_def',subtype_at_def]
    >> rfs[LAST_EL,NULL_EQ]
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> fs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
  )
  (* m <> m' *)
  >> (
    (qspec_then `Tyapp m l` assume_tac) is_subtype_leaf_all_types
    >> fs[]
    >> qpat_x_assum `!p. _ ==> _` imp_res_tac
    >> Cases_on `p'`
    >> fs[subtype_at_def]
    >> Cases_on `h`
    >> fs[subtype_at_def]
    >> FULL_CASE_TAC
    >> rfs[is_subtype_leaf_def']
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> rfs[NULL_EQ,subtype_at_def]
  )
QED

Theorem is_instance_subtype_leaf_imp[local]:
  !t ti. is_instance t ti ==> !p. is_subtype_leaf t p ==> IS_SOME (subtype_at ti p)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rpt strip_tac
    >> (qspecl_then [`Tyvar m`,`[]`,`i`,`Tyvar m`] assume_tac) subtype_at_TYPE_SUBST
    >> fs[is_subtype_leaf_Tyvar,NULL_EQ,subtype_at_def]
  )
  >> rpt strip_tac
  >> imp_res_tac is_subtype_leaf_Tyapp
  >> Cases_on `NULL l`
  >> Cases_on `p`
  >> fs[is_subtype_leaf_def',NULL_EQ]
  >> Cases_on `h`
  >> Cases_on `q = m /\ r < LENGTH l`
  >> fs[subtype_at_def]
  >- (
    fs[EVERY_MEM,MEM_EL]
    >> last_x_assum (qspec_then `EL r l` assume_tac)
    >> pop_assum imp_res_tac
    >> fs[]
    >> first_x_assum (qspecl_then [`i`,`t`] assume_tac)
    >> imp_res_tac TYPE_SUBST_EL
    >> fs[]
  )
  >> fs[]
QED

Definition unify_types_invariant_def:
  unify_types_invariant orig_l l sigma =
    (* The substitution's domain is not in the worklist *)
    ((!x. MEM x (MAP SND sigma) ==> (~MEM x (MAP FST l) /\ ~MEM x (MAP SND l))) /\
    (* The type variables of the worklist are not in the substitution's domain *)
    (!a. MEM a (FLAT(MAP (tyvars o SND) l)) ==> ~MEM (Tyvar a) (MAP SND sigma)) /\
    (!a. MEM a (FLAT(MAP (tyvars o FST) l)) ==> ~MEM (Tyvar a) (MAP SND sigma)) /\
    (* The substitution's domain consists of variables only *)
    (!x. MEM x (MAP SND sigma) ==> ?a. x = Tyvar a) /\
    (* The substitution has pairwise distinct domain elements *)
    (ALL_DISTINCT (MAP SND sigma)) /\
    (* The substitution's domain is in the support of original list *)
    (!a. MEM (Tyvar a) (MAP SND sigma) ==>
         MEM a (FLAT(MAP (tyvars o FST) orig_l)) \/ MEM a (FLAT(MAP (tyvars o SND) orig_l))) /\
    (* The type variables in the worklist occur in the original list *)
    (!a. MEM a (FLAT(MAP (tyvars o FST) l)) ==>
         MEM a (FLAT(MAP (tyvars o FST) orig_l)) \/ MEM a (FLAT(MAP (tyvars o SND) orig_l))) /\
    (!a. MEM a (FLAT(MAP (tyvars o SND) l)) ==>
         MEM a (FLAT(MAP (tyvars o FST) orig_l)) \/ MEM a (FLAT(MAP (tyvars o SND) orig_l))) /\
    (* All differences between elements in the original worklist that remain after applying
       the substitution are present in the worklist *)
    (LIST_REL (equal_upto l)
             (MAP (TYPE_SUBST sigma o FST) orig_l)
             (MAP (TYPE_SUBST sigma o SND) orig_l))
    (* each tuple in the worklist comes from a unification task at the same
       hierarchy in orig_l list *)
    /\ (!a b. MEM (a,b) l ==> ?x y p. MEM (x,y) orig_l /\ (
        (subtype_at (TYPE_SUBST sigma x) p = SOME a /\ subtype_at (TYPE_SUBST sigma y) p = SOME b)
        \/ (subtype_at (TYPE_SUBST sigma x) p = SOME b /\ subtype_at (TYPE_SUBST sigma y) p = SOME a)))
    (* If we have a certificate for two not unifiable types then the
       original list could not have been unifiable *)
    /\ (?s. EVERY (λ(x,y). TYPE_SUBST s x = TYPE_SUBST s y) orig_l
      ==> ?s'. EVERY (λ(x,y). (TYPE_SUBST s' o TYPE_SUBST sigma) x
        = (TYPE_SUBST s' o TYPE_SUBST sigma) y) orig_l)
(*    (* The substitution's domain is not work list *)
    /\ (!a. MEM (Tyvar a) (MAP SND sigma) ==>
         ~MEM a (FLAT(MAP (tyvars o FST) l)) /\ ~MEM a (FLAT(MAP (tyvars o SND) l)))
    (* sigma is most general *)
    /\ (!s.  LIST_REL (equal_upto l)
             (MAP (TYPE_SUBST s o FST) orig_l)
             (MAP (TYPE_SUBST s o SND) orig_l)
             ==> ?rho. !a. ~MEM a (FLAT(MAP (tyvars o FST) l)) /\ ~MEM a (FLAT(MAP (tyvars o SND) l))
             /\ (MEM a (FLAT(MAP (tyvars o FST) orig_l)) \/ MEM a (FLAT(MAP (tyvars o SND) orig_l)))
             ==> ((TYPE_SUBST rho) o (TYPE_SUBST sigma)) (Tyvar a) = TYPE_SUBST s (Tyvar a))
*)
)
End

Theorem REV_ASSOCD_MAP_FST[local]:
  !l.
  REV_ASSOCD x l x = REV_ASSOCD x (MAP (f ## I) l ++ l) x /\
  ALL_DISTINCT (MAP SND l) /\ MEM (y,x) l
  ==> f y = y
Proof
  fs[REV_ASSOCD_self_append]
  \\ Induct >- rw[REV_ASSOCD]
  \\ Cases \\rw[REV_ASSOCD] \\ fs[]
  \\ fs[MEM_MAP] \\ first_x_assum(qspec_then `(y,r)` mp_tac) \\ fs[]
QED

Theorem MEM_PAIR_IMP[local]:
  MEM (a,b) l ==> MEM a (MAP FST l) /\ MEM b (MAP SND l)
Proof
  rw[MEM_MAP] \\ qexists_tac `(a,b)` \\ rw[]
QED

Theorem unify_types_invariant_pres1[local]:
  unify_types_invariant orig_l ((Tyapp a atys, Tyapp b btys)::l) sigma
   /\ a = b /\ LENGTH atys = LENGTH btys /\ atys = btys ==>
   unify_types_invariant orig_l l sigma
Proof
  rw[unify_types_invariant_def,equal_upto_eq,orth_ty_def]
  \\ fs[equal_upto_eq]
QED

Theorem tyvars_tyapp[local]:
  set(tyvars(Tyapp a tys)) = set(FLAT(MAP tyvars tys))
Proof
  fs[tyvars_def,FUN_EQ_THM] \\
  fs (map (SIMP_RULE (srw_ss()) [IN_DEF]) [MEM_FOLDR_LIST_UNION,MEM_FLAT,MEM_MAP])
  \\ rw[EQ_IMP_THM] \\ metis_tac[]
QED


Theorem unify_types_invariant_pres2[local]:
  unify_types_invariant orig_l ((Tyapp a atys, Tyapp b btys)::l) sigma
   /\ a = b /\ LENGTH atys = LENGTH btys /\ atys <> btys ==>
   unify_types_invariant orig_l ((ZIP (atys,btys))++l) sigma
Proof
  rw[] \\ simp[unify_types_invariant_def]
  \\ conj_tac
  >- (fs[unify_types_invariant_def,MAP_ZIP] \\ rw[]
      \\ first_x_assum drule \\ strip_tac \\ fs[]
      \\ rveq \\ rpt(first_x_assum(qspec_then `a'` assume_tac))
      \\ rfs[tyvars_def,MEM_FLAT,MEM_FOLDR_LIST_UNION]
      \\ rpt(first_x_assum(qspec_then `Tyvar a'` assume_tac))
      \\ rfs[tyvars_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def,MAP_ZIP] \\ rw[]
      \\ last_x_assum match_mp_tac
      \\ fs[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_FLAT,MEM_MAP] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def,MAP_ZIP] \\ rw[]
      \\ first_x_assum match_mp_tac
      \\ fs[tyvars_def,MEM_FOLDR_LIST_UNION,MEM_FLAT,MEM_MAP] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def,MAP_ZIP,tyvars_tyapp] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def,MAP_ZIP,tyvars_tyapp] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def]
      \\ qhdtm_x_assum `LIST_REL` mp_tac \\ match_mp_tac EVERY2_mono
      \\ rw[] \\ metis_tac[equal_upto_zip])
  \\ conj_tac
  >- (
    fs[unify_types_invariant_def]
    >> rw[]
    >- (
      first_x_assum (qspecl_then [`Tyapp a atys`,`Tyapp a btys`] mp_tac)
      >> rw[]
      >> qmatch_asmsub_abbrev_tac `MEM (in_atys,in_btys) (ZIP _ )`
      >> `?n. subtype_at (Tyapp a atys) [n] = SOME in_atys
        /\ subtype_at (Tyapp a btys) [n] = SOME in_btys` by (
        fs[MEM_EL]
        >> qexists_tac `(a,n)`
        >> fs[subtype_at_def]
        >> imp_res_tac LENGTH_ZIP
        >> (Q.ISPECL_THEN [`atys`,`btys`,`n`] mp_tac) EL_ZIP
        >> fs[]
        >> rw[]
        >> fs[]
      )
      >> asm_exists_tac
      >> qexists_tac `p++[n]`
      >> fs[subtype_at_trans]
    )
    >> rw[]
  )
  >- (
    fs[unify_types_invariant_def]
    >> asm_exists_tac
    >> rw[]
  )
QED

Theorem unify_types_invariant_pres3[local]:
  unify_types_invariant orig_l ((Tyapp a atys, Tyvar b)::l) sigma
   ==>
   unify_types_invariant orig_l ((Tyvar b, Tyapp a atys)::l) sigma
Proof
  rw[] \\ simp[unify_types_invariant_def]
  \\ conj_tac
  >- (fs[unify_types_invariant_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ qhdtm_x_assum `LIST_REL` mp_tac
      \\ match_mp_tac EVERY2_mono \\ rw[] \\ match_mp_tac equal_upto_swap \\ simp[])
  \\ conj_tac
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
  >- (fs[unify_types_invariant_def] \\ metis_tac[])
QED

Theorem unify_types_invariant_pres4[local]:
  unify_types_invariant orig_l ((Tyvar a, ty)::l) sigma
   /\ Tyvar a = ty ==>
   unify_types_invariant orig_l l sigma
Proof
  rw[unify_types_invariant_def]
  >- (qhdtm_x_assum `LIST_REL` mp_tac \\ match_mp_tac EVERY2_mono
  \\ metis_tac[equal_upto_eq])
  \\ metis_tac[]
QED

Theorem LIST_REL_mono_strong:
  !xs ys. (LENGTH xs = LENGTH ys ==> !x y. MEM (x,y) (ZIP(xs,ys)) /\ P x y ==> Q x y) ==> LIST_REL P xs ys ==> LIST_REL Q xs ys
Proof
  Induct
  >- (Cases >> rw[])
  >- (gen_tac >> Cases >> rw[] >> imp_res_tac LIST_REL_LENGTH \\ fs[])
QED

Theorem REV_ASSOCD_drop[local]:
  !l1. r <> x ==> REV_ASSOCD x (l1 ++ [(q,r)] ++ l2) y = REV_ASSOCD x (l1 ++ l2) y
Proof
  Induct >- rw[REV_ASSOCD]
  >> Cases >> fs[REV_ASSOCD]
QED

val equal_upto_strongind = fetch "-" "equal_upto_strongind";

Theorem REV_ASSOCD_reorder:
  !l1 l2 x y. ALL_DISTINCT(MAP SND l1) /\ ALL_DISTINCT(MAP SND l2) /\ set l1 = set l2
   ==> REV_ASSOCD x l1 y = REV_ASSOCD x l2 y
Proof
  Induct >- simp[]
  \\ Cases \\ rw[]
  \\ `MEM (q,r) l2` by(RULE_ASSUM_TAC GSYM \\ fs[])
  \\ pop_assum(strip_assume_tac o REWRITE_RULE [MEM_SPLIT])
  \\ qpat_assum `~MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT])
  \\ fs[REV_ASSOCD,ALL_DISTINCT_APPEND]
  \\ IF_CASES_TAC
  >- (fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND]
      \\ rpt(PURE_FULL_CASE_TAC \\ fs[]) \\ imp_res_tac ALOOKUP_MEM
      \\ imp_res_tac MEM_PAIR_IMP \\ fs[MEM_MAP] \\ rveq \\ fs[]
      \\ rpt(pairarg_tac \\ fs[] \\ rveq) \\ metis_tac[SND])
  \\ simp[REV_ASSOCD_drop] \\ first_x_assum match_mp_tac
  \\ fs[ALL_DISTINCT_APPEND] \\ fs[SET_EQ_SUBSET,SUBSET_DEF] \\ rw[]
  \\ fs[] \\ first_x_assum drule \\ strip_tac \\ fs[]
  \\ rveq \\ imp_res_tac MEM_PAIR_IMP
  \\ rpt(first_x_assum (qspec_then `(q,r)` assume_tac))
  \\ rfs[]
QED

Theorem equal_upto_subst:
  !a ty l ty1 ty2. equal_upto ((Tyvar a,ty)::l) ty1 ty2 /\ ~MEM a (tyvars ty)
   ==> equal_upto (MAP (TYPE_SUBST [(ty,Tyvar a)] ## TYPE_SUBST [(ty,Tyvar a)]) l)
                  (TYPE_SUBST [(ty,Tyvar a)] ty1) (TYPE_SUBST [(ty,Tyvar a)] ty2)
Proof
  `!l ty1 ty2. equal_upto l ty1 ty2 ==> !a ty l'. l = (Tyvar a,ty)::l' /\ ~MEM a (tyvars ty) ==>
       equal_upto (MAP (TYPE_SUBST [(ty,Tyvar a)] ## TYPE_SUBST [(ty,Tyvar a)]) l')
                  (TYPE_SUBST [(ty,Tyvar a)] ty1) (TYPE_SUBST [(ty,Tyvar a)] ty2)`
    suffices_by metis_tac[]
  \\ ho_match_mp_tac equal_upto_strongind \\ rpt strip_tac
  >- fs[equal_upto_rules]
  >- (fs[equal_upto_rules,REV_ASSOCD,TYPE_SUBST_reduce_CONS]
      \\ match_mp_tac equal_upto_l1
      \\ fs[MEM_MAP] \\ qexists_tac `(ty1,ty2)`
      \\ simp[])
  >- (fs[equal_upto_rules,REV_ASSOCD,TYPE_SUBST_reduce_CONS]
      \\ match_mp_tac equal_upto_l2
      \\ fs[MEM_MAP] \\ qexists_tac `(ty2,ty1)`
      \\ simp[])
  \\ fs[TYPE_SUBST_def] \\ match_mp_tac equal_upto_tyapp
  \\ conj_tac >- simp[]
  \\ simp[EVERY2_MAP]
  \\ qhdtm_x_assum `LIST_REL` mp_tac
  \\ match_mp_tac LIST_REL_mono
  \\ rw[]
QED

Theorem unify_types_invariant_pres5[local]:
  unify_types_invariant orig_l ((Tyvar a, ty)::l) sigma
   /\ Tyvar a <> ty /\ ~(MEM a (tyvars ty)) ==>
  let
      subst_a = TYPE_SUBST [(ty,Tyvar a)];
      l' = MAP (subst_a ## subst_a) l;
      sigma' = MAP (subst_a ## I) sigma
  in unify_types_invariant orig_l l' ((ty, Tyvar a)::sigma')
Proof
  rw[] >> PURE_ONCE_REWRITE_TAC[unify_types_invariant_def]
  >> conj_tac
  >- (fs[unify_types_invariant_def] \\ simp[MEM_MAP] \\ rw[]
      \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[]
      >- (Cases_on `y'` \\ fs[] \\ Cases_on `q` \\ fs[TYPE_SUBST_def,REV_ASSOCD]
          \\ EVERY_CASE_TAC \\ fs[])
      >- (Cases_on `y'` \\ fs[] \\ Cases_on `r` \\ fs[TYPE_SUBST_def,REV_ASSOCD]
          \\ EVERY_CASE_TAC \\ fs[tyvars_def])
      >- (Cases_on `y'''` \\ Cases_on `y'` \\ fs[REV_ASSOCD] \\ EVERY_CASE_TAC \\ fs[] \\ rveq
          \\ imp_res_tac MEM_PAIR_IMP \\ rpt(first_x_assum(fn thm => drule thm \\ mp_tac thm))
          \\ rpt strip_tac \\ Cases_on `q` \\ fs[REV_ASSOCD] \\ EVERY_CASE_TAC \\ fs[] \\ rveq)
      \\ Cases_on `y'''` \\ Cases_on `y'` \\ fs[REV_ASSOCD] \\ EVERY_CASE_TAC \\ fs[] \\ rveq
      \\ imp_res_tac MEM_PAIR_IMP \\ rpt(first_x_assum(fn thm => drule thm \\ mp_tac thm))
      \\ rpt strip_tac \\ Cases_on `r` \\ fs[REV_ASSOCD] \\ EVERY_CASE_TAC \\ fs[] \\ rveq)
  >> conj_tac
  >- (fs[unify_types_invariant_def,tyvars_def] \\ rw[MEM_FLAT,MEM_MAP]
      \\ fs[] \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[tyvars_TYPE_SUBST,REV_ASSOCD] \\ EVERY_CASE_TAC
      \\ fs[tyvars_def] \\ rveq \\ Cases_on `y'''` \\ Cases_on `y'` \\ fs[REV_ASSOCD]
      \\ EVERY_CASE_TAC \\ fs[] \\ rveq
      \\ imp_res_tac MEM_PAIR_IMP \\rpt(first_x_assum(fn thm => drule thm \\ mp_tac thm))
      \\ rpt strip_tac \\ fs[] \\ rveq \\ fs[DISJ_IMP_THM,FORALL_AND_THM] \\ rpt(first_x_assum drule)
      \\ simp[] \\ rpt(first_x_assum(qspec_then `a'` assume_tac)) \\ rfs[]
      \\ fs[MEM_FLAT,MEM_MAP] \\ rveq \\ fs[] \\ metis_tac[])
  >> conj_tac
  >- (fs[unify_types_invariant_def,tyvars_def] \\ rw[MEM_FLAT,MEM_MAP]
      \\ fs[] \\ CCONTR_TAC \\ fs[] \\ rveq \\ fs[tyvars_TYPE_SUBST,REV_ASSOCD] \\ EVERY_CASE_TAC
      \\ fs[tyvars_def] \\ rveq \\ Cases_on `y'''` \\ Cases_on `y'` \\ fs[REV_ASSOCD]
      \\ EVERY_CASE_TAC \\ fs[] \\ rveq
      \\ imp_res_tac MEM_PAIR_IMP \\rpt(first_x_assum(fn thm => drule thm \\ mp_tac thm))
      \\ rpt strip_tac \\ fs[] \\ rveq \\ fs[DISJ_IMP_THM,FORALL_AND_THM] \\ rpt(first_x_assum drule)
      \\ simp[] \\ rpt(first_x_assum(qspec_then `a'` assume_tac)) \\ rfs[]
      \\ fs[MEM_FLAT,MEM_MAP] \\ rveq \\ fs[] \\ metis_tac[])
  >> conj_tac
  >- (fs[unify_types_invariant_def,tyvars_def] \\ rw[MEM_FLAT,MEM_MAP]
      \\ rw[SND_PAIR_MAP] \\ Cases_on `y'` \\ fs[]
      \\ first_x_assum match_mp_tac \\ imp_res_tac MEM_PAIR_IMP)
  >> conj_tac
  >- (fs[unify_types_invariant_def,MAP_MAP_o,o_PAIR_MAP,tyvars_def])
  >> conj_tac
  >- (fs[unify_types_invariant_def,MAP_MAP_o,o_PAIR_MAP,tyvars_def]
      \\ rw[] \\ fs[])
  >> conj_tac
  >- (fs[unify_types_invariant_def,MAP_MAP_o,o_PAIR_MAP,tyvars_def]
      \\ fs[MEM_FLAT,MEM_MAP] \\ rpt strip_tac \\ rveq
      \\ fs[tyvars_TYPE_SUBST,REV_ASSOCD]
      \\ PURE_FULL_CASE_TAC \\ rveq \\ fs[tyvars_def] \\ rveq
      \\ metis_tac[])
  >> conj_tac
  >- (fs[unify_types_invariant_def,MAP_MAP_o,o_PAIR_MAP,tyvars_def]
      \\ fs[MEM_FLAT,MEM_MAP] \\ rpt strip_tac \\ rveq
      \\ fs[tyvars_TYPE_SUBST,REV_ASSOCD]
      \\ PURE_FULL_CASE_TAC \\ rveq \\ fs[tyvars_def] \\ rveq
      \\ metis_tac[])
  >> conj_tac
  >- (fs[unify_types_invariant_def,MAP_MAP_o,o_PAIR_MAP]
      \\ qhdtm_x_assum `LIST_REL` mp_tac \\ simp[EVERY2_MAP]
      \\ match_mp_tac LIST_REL_mono_strong \\ rw[]
      \\ drule equal_upto_subst \\ disch_then drule \\ simp[TYPE_SUBST_compose]
      \\ qmatch_goalsub_abbrev_tac `equal_upto _ a1 a2 ==> equal_upto _ a3 a4`
      \\ `a1 = a3 /\ a2 = a4` suffices_by simp[]
      \\ unabbrev_all_tac
      \\ conj_tac \\ fs[TYPE_SUBST_tyvars] \\ rw[]
      \\ match_mp_tac REV_ASSOCD_reorder
      \\ (conj_tac
          >- fs[MAP_MAP_o,o_PAIR_MAP,tyvars_def]
          \\ conj_tac
          >- fs[ALL_DISTINCT_APPEND,MAP_MAP_o,o_PAIR_MAP,tyvars_def]
          \\ fs[FUN_EQ_THM,UNION_DEF,IN_DEF] \\ metis_tac[])
      )
  >> conj_tac
  >- (
    fs[unify_types_invariant_def,EVERY_MEM]
    >> rw[MEM_MAP]
    >> Cases_on `y`
    >> qpat_x_assum `!a b. (_ /\ _) \/ _ ==> _` (qspecl_then [`q`,`r`] mp_tac)
    >> rw[]
    >> NTAC 2 (
      qmatch_asmsub_rename_tac `subtype_at (TYPE_SUBST sigma x) _ = SOME in_x`
      >> qmatch_asmsub_rename_tac `subtype_at (TYPE_SUBST sigma y) _ = SOME in_y`
      >> qmatch_asmsub_rename_tac `(subs_in_x, subs_in_y) = _ (in_x,in_y)`
        ORELSE qmatch_asmsub_rename_tac `(subs_in_y, subs_in_x) = _ (in_y,in_x)`
      >> asm_exists_tac
      >> qexists_tac `p`
      >> rw[AC DISJ_ASSOC DISJ_COMM]
      >> DISJ1_TAC
      >> rw[GSYM TYPE_SUBST_compose]
      >> `TYPE_SUBST ((ty,Tyvar a)::MAP (TYPE_SUBST [(ty,Tyvar a)] ## I) sigma)
        = TYPE_SUBST [(ty,Tyvar a)] o TYPE_SUBST sigma` by (
        rw[FUN_EQ_THM,TYPE_SUBST_compose,TYPE_SUBST_tyvars]
        >> match_mp_tac REV_ASSOCD_reorder
        >> rw[ALL_DISTINCT,MAP_MAP_o]
        >- fs[o_PAIR_MAP,ALL_DISTINCT_APPEND]
        >- (
          qpat_x_assum `!x. MEM _ (tyvars (Tyvar a)) \/ _ ==> ~MEM _ _` (qspec_then `a` mp_tac)
          >> rw[MEM_MAP,tyvars_def]
        )
        >- fs[o_PAIR_MAP]
        >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [INSERT_SING_UNION]))
        >> fs[AC UNION_ASSOC UNION_COMM]
      )
      >> fs[]
      >> match_mp_tac subtype_at_TYPE_SUBST
      >> fs[]
    )
  )
  >- (
    fs[unify_types_invariant_def,EVERY_MEM,unifiable_def,ELIM_UNCURRY]
    >> rw[EVERY_MEM,ELIM_UNCURRY,unifiable_def]
    >> first_x_assum (qspecl_then [`Tyvar a`,`ty`] mp_tac)
    >> rw[]
    >> qmatch_asmsub_abbrev_tac `subtype_at (TYPE_SUBST _ x) p = SOME in_x`
    >> qmatch_asmsub_abbrev_tac `subtype_at (TYPE_SUBST _ y) p = SOME in_y`
    >> qexists_tac `s`
    >> rw[]
    >> fs[]
    >> qexists_tac `s'`
    >> rpt strip_tac
    >> qpat_x_assum `!x. _` kall_tac
    >> first_assum drule
    >> first_x_assum (qspec_then `(x,y)` mp_tac)
    >> rw[]
    >> `TYPE_SUBST s' in_x = TYPE_SUBST s' in_y` by (
      (qspecl_then [`TYPE_SUBST sigma x`,`p`,`s'`,`in_x`] mp_tac) subtype_at_TYPE_SUBST
      >> (qspecl_then [`TYPE_SUBST sigma y`,`p`,`s'`,`in_y`] mp_tac) subtype_at_TYPE_SUBST
      >> rw[]
    )
    >> unabbrev_all_tac
    >> `TYPE_SUBST ((ty,Tyvar a)::MAP (TYPE_SUBST [(ty,Tyvar a)] ## I) sigma)
      = TYPE_SUBST [(ty,Tyvar a)] o TYPE_SUBST sigma` by (
      rw[FUN_EQ_THM,TYPE_SUBST_compose,TYPE_SUBST_tyvars]
      >> match_mp_tac REV_ASSOCD_reorder
      >> rw[ALL_DISTINCT,MAP_MAP_o]
      >- fs[o_PAIR_MAP,ALL_DISTINCT_APPEND]
      >- (
        qpat_x_assum `!x. MEM _ (tyvars (Tyvar a)) \/ _ ==> ~MEM _ _` (qspec_then `a` mp_tac)
        >> unabbrev_all_tac
        >> rw[MEM_MAP,tyvars_def]
      )
      >- fs[o_PAIR_MAP]
      >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [INSERT_SING_UNION]))
      >> fs[AC UNION_ASSOC UNION_COMM]
    )
    >> unabbrev_all_tac
    >> rw[]
    >> assume_tac TYPE_SUBST_eating
    >> fs[FUN_EQ_THM]
  )
QED

Theorem unify_types_pres_invariant:
  !l sigma sigma' orig_l. unify_types l sigma = SOME sigma' /\
     unify_types_invariant orig_l l sigma
     ==> unify_types_invariant orig_l [] sigma'
Proof
  ho_match_mp_tac unify_types_ind
  >> rpt strip_tac
  >- (rfs[unify_types_def])
  >- (fs[unify_types_def] \\ PURE_FULL_CASE_TAC
      >- (rpt(first_x_assum drule) \\ fs[]
          \\ disch_then match_mp_tac
          \\ match_mp_tac unify_types_invariant_pres1 \\ rfs[])
      \\ rpt(first_x_assum drule) \\ fs[]
      \\ disch_then match_mp_tac
      \\ match_mp_tac unify_types_invariant_pres2 \\ rfs[])
  >- (qhdtm_x_assum `unify_types` (assume_tac o REWRITE_RULE [Once unify_types_def]) \\ fs[]
      \\ first_x_assum match_mp_tac \\ match_mp_tac unify_types_invariant_pres3 \\ simp[])
  >- (qhdtm_x_assum `unify_types` (assume_tac o REWRITE_RULE [Once unify_types_def]) \\ fs[]
      \\ PURE_FULL_CASE_TAC
      >- (fs[] \\ metis_tac[unify_types_invariant_pres4])
      \\ fs[] \\ PURE_FULL_CASE_TAC
      >- (fs[] \\ metis_tac[unify_types_invariant_pres4])
      \\ fs[] \\ first_x_assum match_mp_tac
      \\ drule(GEN_ALL unify_types_invariant_pres5) \\ simp[])
QED

Theorem unify_types_invariant_init:
  !orig_l. unify_types_invariant orig_l orig_l []
Proof
  simp[unify_types_invariant_def] \\ rw[]
  >- (fs[LIST_REL_EVERY_ZIP,EVERY_MEM,ZIP_MAP,MEM_MAP] \\ Cases \\ rw[]
  \\ Cases_on `x` \\ fs[equal_upto_rules])
  >- (asm_exists_tac >> qexists_tac `[]` >> fs[subtype_at_def])
  >> rpt(qexists_tac `[]` >> rw[])
QED

Theorem unify_types_IMP_invariant:
  !l sigma. unify_types l [] = SOME sigma
       ==> unify_types_invariant l [] sigma
Proof
  metis_tac[unify_types_invariant_init,unify_types_pres_invariant]
QED

Theorem unify_types_sound:
  !sigma ty1 ty2. unify_types [(ty1,ty2)] [] = SOME sigma
       ==> TYPE_SUBST sigma ty1 = TYPE_SUBST sigma ty2
Proof
  rw[] \\ dxrule unify_types_IMP_invariant
  \\ fs[unify_types_invariant_def,equal_upto_nil]
QED

Theorem unify_types_sound_list:
  !l sigma. unify_types l [] = SOME sigma
       ==> EVERY (λ(ty1,ty2). TYPE_SUBST sigma ty1 = TYPE_SUBST sigma ty2) l
Proof
  rpt strip_tac
  >> (qspecl_then [`sigma`,`Tyapp a (MAP FST l)`,`Tyapp a (MAP SND l)`] assume_tac) unify_types_sound
  >> fs[unify_types_def]
  >> FULL_CASE_TAC
  >- fs[MAP_EQ_f,EVERY_MEM,ELIM_UNCURRY]
  >> fs[MAP_EQ_EVERY2,LIST_REL_EVERY_ZIP,ZIP_MAP]
  >> fs[LAMBDA_PROD,MAP_MAP_o,o_DEF]
  >> fs[EVERY_MAP,ELIM_UNCURRY]
QED

Theorem unify_types_complete_cyclic_non_unifiable:
  !ty a. Tyvar a <> ty /\ MEM a (tyvars ty)
  ==> !s. TYPE_SUBST s (Tyvar a) <> TYPE_SUBST s ty
Proof
  rpt strip_tac
  >> imp_res_tac subtype_at_tyvars
  >> imp_res_tac subtype_at_TYPE_SUBST
  >> pop_assum (qspec_then `s` assume_tac)
  >> rfs[]
  >> imp_res_tac subtype_at_cyclic
  >> fs[NULL_EQ,subtype_at_def]
QED

Theorem unify_types_complete_arity_non_unifiable:
  !a atys b btys. LENGTH atys <> LENGTH btys \/ a <> b
  ==> !s. TYPE_SUBST s (Tyapp a atys) <> TYPE_SUBST s (Tyapp b btys)
Proof
  rw[TYPE_SUBST_def]
  >> Cases_on `a = b` >> fs[]
  >> `!x (y:type list). LENGTH x <> LENGTH y ==> x <> y` by (rw[] >> CCONTR_TAC >> fs[])
  >> pop_assum match_mp_tac
  >> rw[LENGTH_MAP]
QED

Theorem unify_types_complete_step[local]:
  !l sigma ty1 ty2.
  unify_types_invariant [(ty1,ty2)] l sigma
  /\ unifiable (TYPE_SUBST sigma ty1) (TYPE_SUBST sigma ty2)
  ==> IS_SOME (unify_types l sigma)
Proof
  ho_match_mp_tac unify_types_ind
  >> strip_tac
  >- rw[unify_types_invariant_def,unify_types_def]
  >> strip_tac
  >- (
    rw[unify_types_def]
    >- (
      first_x_assum match_mp_tac
      >> qexists_tac `ty1`
      >> qexists_tac `ty2`
      >> fs[unify_types_invariant_def,equal_upto_eq]
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      rfs[]
      >> first_x_assum match_mp_tac
      >> qexists_tac `ty1`
      >> qexists_tac `ty2`
      >> fs[]
      >> match_mp_tac (GEN_ALL unify_types_invariant_pres2)
      >> asm_exists_tac
      >> fs[]
    )
    >> CCONTR_TAC
    >> fs[]
    >> (
      fs[unifiable_def,unify_types_invariant_def]
      >> first_x_assum (qspecl_then [`Tyapp a atys`,`Tyapp b btys`] assume_tac)
      >> fs[]
      >> qmatch_assum_abbrev_tac `subtype_at (TYPE_SUBST _ ty1) _ = SOME in_ty1`
      >> qmatch_assum_abbrev_tac `subtype_at (TYPE_SUBST _ ty2) _ = SOME in_ty2`
      >> imp_res_tac subtype_at_TYPE_SUBST
      >> NTAC 2 (first_x_assum (qspec_then `s` assume_tac))
      >> rfs[]
      >> imp_res_tac unify_types_complete_arity_non_unifiable
      >> TRY ((first_x_assum (qspecl_then [`s`,`btys`,`atys`] assume_tac))
        ORELSE (first_x_assum (qspecl_then [`s`,`b`,`a`] assume_tac)))
      >> unabbrev_all_tac
      >> fs[]
      >> fs[]
    )
  )
  >> strip_tac
  >- (
    rpt strip_tac
    >> first_x_assum (qspecl_then [`ty1`,`ty2`] assume_tac)
    >> imp_res_tac unify_types_invariant_pres3
    >> fs[unify_types_def]
  )
  >> (
    rw[unify_types_def]
    >- (
      first_x_assum match_mp_tac
      >> qexists_tac `ty1`
      >> qexists_tac `ty2`
      >> fs[unify_types_invariant_def,equal_upto_eq]
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      imp_res_tac unify_types_complete_cyclic_non_unifiable
      >> CCONTR_TAC
      >> fs[unifiable_def,unify_types_invariant_def,tyvars_def]
      >> qpat_x_assum `!x. (_ = _) \/ _ ==> _` (qspec_then `a` assume_tac)
      >> fs[]
      >> NTAC 2 (
        qmatch_assum_abbrev_tac `MEM a (tyvars ty_a)`
        >> qmatch_assum_abbrev_tac `TYPE_SUBST _ (_ _ ty_a) = TYPE_SUBST _ (_ _ ty_ty)`
          ORELSE qmatch_assum_abbrev_tac `TYPE_SUBST _ (_ _ ty_ty) = TYPE_SUBST _ (_ _ ty_a)`
        >> first_x_assum (qspecl_then [`Tyvar a`,`ty`] assume_tac)
        >> fs[]
        >> imp_res_tac subtype_at_TYPE_SUBST
        >> NTAC 2 (first_x_assum (qspec_then `s'` assume_tac))
        >> rfs[]
      )
    )
    >> drule(GEN_ALL unify_types_invariant_pres5)
    >> rw[]
    >> first_x_assum match_mp_tac
    >> asm_exists_tac
    >> rw[]
    >> qpat_x_assum `unify_types_invariant _ (MAP _ _) _` kall_tac
    >> fs[unifiable_def,unify_types_invariant_def,tyvars_def]
    >> qmatch_goalsub_abbrev_tac `TYPE_SUBST ts ty1`
    >> qpat_x_assum `!x. (_ = _) \/ _ ==> _` (qspec_then `a` assume_tac)
    >> fs[]
    >> NTAC 2 (
      qmatch_assum_abbrev_tac `MEM a (tyvars ty_a)`
      >> qmatch_assum_abbrev_tac `TYPE_SUBST _ (_ _ ty_a) = TYPE_SUBST _ (_ _ ty_ty)`
        ORELSE qmatch_assum_abbrev_tac `TYPE_SUBST _ (_ _ ty_ty) = TYPE_SUBST _ (_ _ ty_a)`
      >> first_x_assum (qspecl_then [`Tyvar a`,`ty`] assume_tac)
      >> fs[]
      >> NTAC 2 (
        imp_res_tac subtype_at_TYPE_SUBST
        >> NTAC 2 (first_x_assum (qspec_then `s` assume_tac))
        >> `TYPE_SUBST s ty = TYPE_SUBST s (Tyvar a)` by rfs[]
        >> imp_res_tac TYPE_SUBST_eating
        >> `TYPE_SUBST ((ty,Tyvar a)::MAP (TYPE_SUBST [(ty,Tyvar a)] ## I) sigma)
          = TYPE_SUBST [(ty,Tyvar a)] o TYPE_SUBST sigma` by (
          rw[FUN_EQ_THM,TYPE_SUBST_compose,TYPE_SUBST_tyvars]
          >> match_mp_tac REV_ASSOCD_reorder
          >> rw[ALL_DISTINCT,MAP_MAP_o]
          >- fs[o_PAIR_MAP,ALL_DISTINCT_APPEND]
          >- (
            qpat_x_assum `!x. (_ = _) \/ _ ==> ~MEM _ _` (qspec_then `a` mp_tac)
            >> unabbrev_all_tac
            >> rw[MEM_MAP,tyvars_def]
            >- (
              Cases_on `Tyvar a = SND y` >> rw[]
              >> first_x_assum (qspec_then `y'` mp_tac)
              >> rw[]
              >- (DISJ1_TAC >> Cases_on `y'` >> Cases_on `y` >> fs[PAIR_MAP_THM])
              >> fs[]
            )
            >> rw[MAP_MAP_o,o_PAIR_MAP]
          )
          >> unabbrev_all_tac
          >> fs[AC UNION_ASSOC UNION_COMM]
          >> CONV_TAC(RHS_CONV(PURE_ONCE_REWRITE_CONV [INSERT_SING_UNION]))
          >> fs[]
        )
        >> unabbrev_all_tac
        >> rfs[FUN_EQ_THM]
        >> pop_assum kall_tac
        >> qexists_tac `s`
        >> fs[]
      )
    )
    >> qexists_tac `s`
    >> unabbrev_all_tac
    >> fs[FUN_EQ_THM]
  )
QED

Theorem unify_types_complete:
  !ty1 ty2. unifiable ty1 ty2 = IS_SOME (unify_types [(ty1,ty2)] [])
Proof
  rw[EQ_IMP_THM]
  >- (
    match_mp_tac unify_types_complete_step
    >> fs[TYPE_SUBST_NIL]
    >> qexists_tac `ty1`
    >> qexists_tac `ty2`
    >> assume_tac unify_types_invariant_init
    >> fs[]
  )
  >> rw[is_instance_refl,ELIM_UNCURRY,unifiable_def]
  >> qexists_tac `THE (unify_types [(ty1,ty2)] [])`
  >> match_mp_tac unify_types_sound
  >> fs[option_CLAUSES]
QED

Theorem unify_sound:
  !ty1 ty2 s1 s2. unify ty1 ty2 = SOME (s1,s2)
       ==> TYPE_SUBST s1 ty1 = TYPE_SUBST s2 ty2
Proof
  rw[unify_def,ELIM_UNCURRY,IS_SOME_EXISTS]
  >> fs[THE_DEF]
  >> imp_res_tac unify_types_sound
  >> fs[GSYM TYPE_SUBST_compose]
  >> fs[normalise_tyvars_rec_def]
QED

Theorem unify_complete:
  !ty1 ty2. ~(ty1 # ty2) = IS_SOME (unify ty1 ty2)
Proof
  rw[]
  >> (qspecl_then [`ty1`,`ty2`,`#"a"`,`#"b"`] assume_tac) normalise_tyvars_rec_chr_diff2
  >> (qspecl_then [`ty1`,`ty2`,`#"a"`,`#"b"`] assume_tac) orth_ty_normalise
  >> fs[unify_def]
  >> pop_assum kall_tac
  >> imp_res_tac (GSYM unifiable_orth_ty_equiv)
  >> rpt (qpat_x_assum `_ ==> _` kall_tac)
  >> fs[]
  >> fs[unify_types_complete,ELIM_UNCURRY]
  >> FULL_CASE_TAC
  >> fs[IS_SOME_DEF]
QED

Theorem TYPE_SUBST_Tyvar_eq[local]:
  !t s a ty. TYPE_SUBST s (Tyvar a) = TYPE_SUBST s ty
  ==> TYPE_SUBST ((TYPE_SUBST s ty, Tyvar a)::s) t = TYPE_SUBST s t
Proof
  rw[TYPE_SUBST_tyvars]
  >> Cases_on `x = a`
  >> fs[REV_ASSOCD]
QED

Theorem MEM_tyvars_MEM_tyvars_TYPE_SUBST[local]:
  !t ty a. ~MEM a (tyvars ty) ==> ~MEM a (tyvars (TYPE_SUBST [(ty,Tyvar a)] t))
Proof
  rw[tyvars_TYPE_SUBST]
  >> Cases_on `MEM x (tyvars t)`
  >> Cases_on `x = a`
  >> fs[REV_ASSOCD,tyvars_def]
QED

Theorem MEM_tyvars_MEM_tyvars_TYPE_SUBST_list[local]:
  !l ls a ty. ~MEM a (tyvars ty) /\ ls = (MAP (TYPE_SUBST [(ty,Tyvar a)] ## TYPE_SUBST [(ty,Tyvar a)]) l)
  ==> EVERY (λx. ~MEM a (tyvars x)) (MAP FST ls) /\ EVERY (λx. ~MEM a (tyvars x)) (MAP SND ls)
Proof
  rw[EVERY_MAP]
  >> imp_res_tac MEM_tyvars_MEM_tyvars_TYPE_SUBST
  >> fs[EVERY_MEM]
QED

Theorem TYPE_SUBST_special_tup_simp[local]:
  !a ty. ~MEM a (tyvars ty) ==> !t s. ~MEM a (tyvars t)
  ==> TYPE_SUBST [(ty,Tyvar a)] (TYPE_SUBST s t) = TYPE_SUBST (MAP (TYPE_SUBST [(ty,Tyvar a)] ## I) s) t
Proof
  rw[TYPE_SUBST_compose,TYPE_SUBST_tyvars]
  >> Cases_on `a=x`
  >> fs[]
  >> assume_tac (Q.ISPECL [`Tyvar x`,`Tyvar x`,`Tyvar a`,`ty:type`,`[]:(type#type) list`] (GEN_ALL REV_ASSOCD_drop))
  >> fs[]
QED

Theorem TYPE_SUBST_triv_eq[local]:
  !s a. TYPE_SUBST ((TYPE_SUBST s (Tyvar a),Tyvar a)::s) = TYPE_SUBST s
Proof
  rw[FUN_EQ_THM,TYPE_SUBST_tyvars]
  >> Cases_on `x'=a`
  >> fs[REV_ASSOCD_def]
QED

Theorem TYPE_SUBST_eq_imp[local]:
  !s a ty t t'. ~MEM a (tyvars ty) /\ (TYPE_SUBST s (Tyvar a) = TYPE_SUBST s ty)
  /\ (TYPE_SUBST s t = TYPE_SUBST s t')
  ==> TYPE_SUBST s (TYPE_SUBST [(ty,Tyvar a)] t) = TYPE_SUBST s (TYPE_SUBST [(ty,Tyvar a)] t')
Proof
  rw[TYPE_SUBST_compose]
  >> qpat_x_assum `REV_ASSOCD _ _ _ = _` (assume_tac o GSYM o ONCE_REWRITE_RULE [GSYM TYPE_SUBST_def])
  >> pop_assum (fn x => ONCE_REWRITE_TAC[x])
  >> fs[TYPE_SUBST_triv_eq]
QED

(* if possible generate a certificate for ti <= t
 * i.e. ti is an instance of t
 * instance_subst [(ti,t)] []
 * !s. is_instance ty0 (TYPE_SUBST s ty0)
 * instance_subst worklist stubstitution equal_tvars
 *)
val instance_subst_def = Hol_defn "instance_subst" `
  (instance_subst [] s e = SOME (s,e))
  /\ (instance_subst ((Tyvar a,Tyvar b)::x) s e =
    if MEM (Tyvar a,Tyvar b) s
    then instance_subst x s e
    else if MEM (Tyvar b) (MAP SND s)
    then NONE
    else if a = b
    then instance_subst x s (a::e)
    else if ~MEM b e
    then instance_subst x ((Tyvar a,Tyvar b)::s) e
    else NONE)
  /\ (instance_subst ((Tyapp m l,Tyapp n l')::x) s e =
    if m = n /\ LENGTH l = LENGTH l'
    then instance_subst ((ZIP (l,l'))++x) s e
    else NONE)
  /\ (instance_subst ((Tyvar _,Tyapp _ _)::_) _ _ = NONE)
  /\ (instance_subst ((Tyapp m l,Tyvar a)::x) s e =
    if MEM (Tyapp m l,Tyvar a) s
    then instance_subst x s e
    else if ~MEM (Tyvar a) (MAP SND s) /\ ~MEM a e
    then instance_subst x ((Tyapp m l,Tyvar a)::s) e
    else NONE)
`;

val (instance_subst_def,instance_subst_ind) = Defn.tprove(
  instance_subst_def,
  WF_REL_TAC `measure (SUM o (MAP (λx. (type_size' o FST) x + (type_size' o SND) x)) o FST)`
  >> rw[SUM_APPEND,type_size'_def]
  >> rw[SUM_MAP_PLUS,MAP_ZIP,GSYM o_DEF,type1_size'_SUM_MAP]
);

val [instance_subst_empty,instance_subst_tyvars,instance_subst_tyapp,instance_subst_tyvar_tyapp,instance_subst_tyapp_tyvar] =
    map save_thm (zip ["instance_subst_empty","instance_subst_tyvars","instance_subst_tyapp","instance_subst_tyvar_tyapp","instance_subst_tyapp_tyvar"]
                      (map GEN_ALL (CONJUNCTS instance_subst_def)));

Definition instance_subst_inv_def:
    instance_subst_inv orig_l l sigma e = (
    (* each element from l comes from the list orig_l at the same height *)
    (!a b. MEM (a,b) l ==> ?x y p. MEM (x,y) orig_l /\ (
        (subtype_at x p = SOME a /\ subtype_at y p = SOME b)))
    (* orig_l are equal except for the elements in l, sigma *)
    /\ (
      !x y p. MEM (x,y) orig_l /\ IS_SOME (subtype_at x p) /\ IS_SOME (subtype_at y p) ==>
      (* parent or child of (x,y) in worklist *)
      (?q r. (p = q ++ r \/ q = p ++ r)
        /\ IS_SOME (subtype_at x q) /\ IS_SOME (subtype_at y q)
        /\ MEM (THE (subtype_at x q),THE (subtype_at y q)) l)
      (* parent or child of (x,y) in sigma *)
      \/ (?q r a. (p = q ++ r \/ q = p ++ r)
        /\ subtype_at y q = SOME (Tyvar a) /\ IS_SOME (subtype_at x q) /\ MEM (THE (subtype_at x q),Tyvar a) sigma)
      (* Same leaves *)
      \/ (?q r a. (p = q ++ r \/ q = p ++ r)
        /\ subtype_at x q = subtype_at y q
        /\ (subtype_at x q = SOME (Tyapp a []) \/ (subtype_at x q = SOME (Tyvar a) /\ MEM a e)))
    )
    (* If we have a certificate for two non equal types in the worklist then the
       original list could not have been equal *)
    /\ ((?s. EVERY (λ(x,y). x = TYPE_SUBST s y) orig_l)
      ==> ?s'. EVERY (λ(x,y). x = (TYPE_SUBST (sigma ++ s')) y) l)
    (* no duplicates in the type substitution *)
    /\ ALL_DISTINCT (MAP SND sigma)
    (* no identities in sigma *)
    /\ EVERY (UNCURRY $<>) sigma
    (* The substitution's domain consists of variables only *)
    /\ (!x. MEM x (MAP SND sigma) ==> ?a. x = Tyvar a)
    (* Same type variables must stay equal under sigma *)
    /\ (!a. MEM a e ==> ~MEM (Tyvar a) (MAP SND sigma))
    (* Non-equal type variables do not occur in e *)
    /\ (!a. MEM (Tyvar a) (MAP SND sigma) ==> ~MEM a e)
    (* Elements in e come from same elements in orig_l *)
    /\ (!a. MEM a e ==>
      ?x y p. MEM (x,y) orig_l /\ subtype_at x p = SOME (Tyvar a) /\ subtype_at y p = SOME (Tyvar a))
    (* Identified elements originate from two elements in orig_l *)
    /\ (!a b. MEM (a,b) sigma ==>
      ?x y p. MEM (x,y) orig_l /\ subtype_at x p = SOME a /\ subtype_at y p = SOME b)
    (* leaves of elements in right-hand side of orig_l *)
    /\ (
      !x y p a. MEM (x,y) orig_l /\ subtype_at y p = SOME (Tyvar a) ==>
      (?q r. p = q++r /\ IS_SOME (subtype_at x q) /\
        MEM (THE (subtype_at x q),THE (subtype_at y q)) l)
      \/ (IS_SOME (subtype_at x p) /\ MEM (THE (subtype_at x p),Tyvar a) sigma)
      \/ subtype_at x p = subtype_at y p
    )
    /\ (
      !x y p a. MEM (x,y) orig_l /\ subtype_at y p = SOME (Tyapp a []) ==>
      (?q r. p = q++r /\ IS_SOME (subtype_at x q) /\
        MEM (THE (subtype_at x q),THE (subtype_at y q)) l)
      \/ subtype_at x p = SOME (Tyapp a [])
    )
    /\ (
      !x y p a. MEM (x,y) orig_l /\ subtype_at x p = SOME (Tyvar a)
        /\ subtype_at y p = SOME (Tyvar a) ==>
        MEM a e
        \/ ?q r. (p = q++r \/ q = p++r) /\ IS_SOME (subtype_at x q)
          /\ IS_SOME (subtype_at y q) /\ MEM (THE (subtype_at x q),THE (subtype_at y q)) l
    )
    (* leaves of elements in left-hand side of orig_l *)
    /\ (
      !x y p. MEM (x,y) orig_l /\ subtype_at x p <> subtype_at (TYPE_SUBST sigma y) p
      /\ is_subtype_leaf x p
      ==> (
        ?q r. p = q ++ r /\ IS_SOME (subtype_at x q) /\ IS_SOME (subtype_at y q)
        /\ MEM (THE (subtype_at x q),THE (subtype_at y q)) l
      )
    )
    /\ (
      !x y p a b. MEM (x,y) orig_l /\ subtype_at x p = SOME a
        /\ subtype_at y p = SOME (Tyvar b)
        /\ a <> (Tyvar b) /\ ~MEM (Tyvar b) (MAP SND sigma)
      ==> (
        ?q r. p = q ++ r /\ IS_SOME (subtype_at x q) /\ IS_SOME (subtype_at y q)
        /\ MEM (THE (subtype_at x q),THE (subtype_at y q)) l
      )
    )
End

Theorem instance_subst_inv_init[local]:
  !orig_l. instance_subst_inv orig_l orig_l [] []
Proof
  fs[instance_subst_inv_def]
  >> strip_tac
  >> conj_tac
  >- (
    rw[]
    >> asm_exists_tac
    >> qexists_tac `[]`
    >> fs[subtype_at_def]
  )
  >> strip_tac
  >> (
    rw[]
    >> TRY (DISJ1_TAC)
    >> qexists_tac `[]`
    >> qexists_tac `p`
    >> fs[subtype_at_def,IS_SOME_EXISTS]
  )
QED

Theorem instance_subst_inv_pres1[local]:
   ∀l sigma sigma' e e'.
        instance_subst_inv l [] sigma e
        /\ instance_subst [] sigma e = SOME (sigma',e')
        ==> instance_subst_inv l [] sigma' e'
Proof
  rw[instance_subst_def,instance_subst_inv_def]
  >> fs[]
  >> first_x_assum match_mp_tac
  >> rpt (asm_exists_tac >> fs[])
QED


Theorem subtype_at_TYPE_SUBST_ineq[local]:
  !y a b sigma x p. ~MEM (Tyvar b) (MAP SND sigma) /\
  subtype_at (TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) y) p ≠ subtype_at (TYPE_SUBST sigma y) p
  ==> IS_SOME (subtype_at (TYPE_SUBST sigma y) p)
  /\ IS_SOME (subtype_at (TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) y) p)
  /\ IS_SOME (subtype_at y p)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rpt strip_tac
    >> CCONTR_TAC
    >> fs[]
    >> TRY (qpat_x_assum `NONE <> _` (assume_tac o GSYM))
    >> fs[option_CLAUSES,GSYM quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,IS_SOME_EXISTS]
    >> Cases_on `m = b`
    >> fs[REV_ASSOCD_def]
    >> imp_res_tac TYPE_SUBST_drop_prefix
    >> pop_assum (qspec_then `[]` assume_tac)
    >> fs[]
    >> qspec_then `p` assume_tac subtype_at_Tyvar
    >> first_assum (qspec_then `a` assume_tac)
    >> first_x_assum (qspec_then `b` assume_tac)
    >> rfs[option_CLAUSES]
    >> fs[]
  )
  >> rw[EVERY_MEM]
  >> Cases_on `p`
  >> TRY (Cases_on `h`)
  >> fs[subtype_at_def]
  >> FULL_CASE_TAC
  >> fs[subtype_at_def]
  >> `MEM (EL r l) l` by (fs[MEM_EL] >> asm_exists_tac >> fs[])
  >> first_x_assum (qspec_then `EL r l` assume_tac)
  >> rfs[]
  >> pop_assum (qspecl_then [`a`,`b`,`sigma`,`t`] assume_tac)
  >> rfs[TYPE_SUBST_EL]
QED

Theorem is_subtype_leafs_imp[local]:
  !x p q. is_subtype_leaf x p /\ is_subtype_leaf x (p++q) ==> q = []
Proof
  rpt strip_tac
  >> qpat_x_assum `is_subtype_leaf x p` (assume_tac o REWRITE_RULE[is_subtype_leaf_def'])
  >> imp_res_tac is_subtype_leaf_IS_SOME_subtype
  >> first_x_assum (qspec_then `q` assume_tac)
  >> fs[NULL_EQ]
QED

Theorem IS_SOME_THE[local]:
  !x y. IS_SOME x /\ (THE x = y) ==> x = SOME y
Proof
  fs[IS_SOME_EXISTS,option_CLAUSES]
QED

Theorem instance_subst_inv_pres2[local]:
  ∀a b l sigma e.
      (¬MEM (Tyvar a,Tyvar b) sigma ∧ ¬MEM (Tyvar b) (MAP SND sigma) ∧
      a ≠ b ∧ ¬MEM b e ⇒
      ∀sigma' orig_l e'.
          instance_subst_inv orig_l l ((Tyvar a,Tyvar b)::sigma) e ∧
          instance_subst l ((Tyvar a,Tyvar b)::sigma) e = SOME (sigma',e') ⇒
          instance_subst_inv orig_l [] sigma' e') ∧
      (¬MEM (Tyvar a,Tyvar b) sigma ∧ ¬MEM (Tyvar b) (MAP SND sigma) ∧ a = b ⇒
      ∀sigma' orig_l e'.
          instance_subst_inv orig_l l sigma (a::e) ∧
          instance_subst l sigma (a::e) = SOME (sigma',e') ⇒
          instance_subst_inv orig_l [] sigma' e') ∧
      (MEM (Tyvar a,Tyvar b) sigma ⇒
      ∀sigma' orig_l e'.
          instance_subst_inv orig_l l sigma e ∧
          instance_subst l sigma e = SOME (sigma',e') ⇒
          instance_subst_inv orig_l [] sigma' e') ⇒
      ∀sigma' orig_l e'.
          instance_subst_inv orig_l ((Tyvar a,Tyvar b)::l) sigma e ∧
          instance_subst ((Tyvar a,Tyvar b)::l) sigma e = SOME (sigma',e') ⇒
          instance_subst_inv orig_l [] sigma' e'
Proof
  rw[instance_subst_def]
  >> rfs[]
  >> qpat_x_assum `!p. _` ho_match_mp_tac
  >> TRY (qpat_x_assum `~MEM _ _ ==> _` kall_tac)
  >> fs[instance_subst_inv_def]
  (* 3 subgoals *)
  >- (
    rw[]
    (* 7 subgoals *)
    >- (
      qpat_x_assum `!x y p. MEM (x,y) orig_l /\ IS_SOME _ /\ IS_SOME _ ⇒ _`
        (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[]
      >- (
        rpt (qpat_x_assum `THE _ = _` (assume_tac o GSYM))
        >> DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `b`
        >> fs[option_CLAUSES]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
      >- (
        rpt (qpat_x_assum `THE _ = _` (assume_tac o GSYM))
        >> DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `b`
        >> fs[option_CLAUSES]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
    )
    >- (
      qpat_x_assum `(?s. _) ==> _` imp_res_tac
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        rveq
        >> imp_res_tac ((REWRITE_RULE [IS_SOME_EXISTS]) subtype_at_IS_SOME_parent)
        >> imp_res_tac IS_SOME_THE
        >> pop_assum (assume_tac o REWRITE_RULE [IS_SOME_EXISTS])
        >> fs[option_CLAUSES]
        >> pop_assum imp_res_tac
        >> qspecl_then [`y`,`q`,`r`,`Tyvar b`] assume_tac subtype_at_decomp_path
        >> rfs[]
        >> qpat_x_assum `SOME _ = _` (assume_tac o GSYM)
        >> qspecl_then [`r`,`b`] assume_tac (REWRITE_RULE [IS_SOME_EXISTS] subtype_at_Tyvar)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >- (
      qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE [IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
    >- (
      qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = _ /\ subtype_at _ _ = _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[EXISTS_OR_THM]
      (* 4 subgoals *)
      >- (
        rveq
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`x`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> fs[EXISTS_OR_THM]
        >> pop_assum imp_res_tac
        >> fs[]
        >> rveq
        >> qpat_x_assum `EVERY _ _` (imp_res_tac o REWRITE_RULE[EVERY_MEM])
        >> fs[]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        rveq
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`x`,`p`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> fs[EXISTS_OR_THM]
        >> pop_assum imp_res_tac
        >> fs[]
        >> qpat_x_assum `EVERY _ _` (imp_res_tac o REWRITE_RULE[EVERY_MEM])
        >> fs[]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >- (
      qpat_x_assum `!x y p. _ /\ _ /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        imp_res_tac TYPE_SUBST_MEM'
        >> qpat_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def',IS_SOME_EXISTS])
        >> pop_assum (qspec_then `[]` assume_tac)
        >> fs[NULL_EQ,IS_SOME_EXISTS]
        >> qspecl_then [`x`,`q`,`r`,`a`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rfs[]
        >> rveq
        >> qspecl_then [`y`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
        >> rfs[]
        >> fs[]
      )
      >- (qexists_tac `q` >> qexists_tac `r` >> fs[])
    )
    >- (
      qpat_x_assum `!x y p a b. _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`,`b'`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> rveq
        >> qspecl_then [`x`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> imp_res_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
        >> fs[NULL_EQ]
        >> rveq
        >> fs[]
      )
      >- (qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
  )
  >- (
    rw[]
    >> fs[]
    (* 7 subgoals *)
    >- (
      qpat_x_assum `!x y p. MEM (x,y) orig_l /\ IS_SOME _ /\ IS_SOME _ ⇒ _`
          (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[]
      (* 8 subgoals *)
      >- (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
        >> rfs[IS_SOME_EXISTS]
        >> fs[]
      )
      >-(
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[option_CLAUSES]
      )
      >- (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
        >> rfs[IS_SOME_EXISTS]
        >> fs[]
      )
      >-(
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[option_CLAUSES]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`>> fs[EXISTS_OR_THM]
      )
      >-(
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    (* 2nd subgoal *)
    >- (
      qpat_x_assum `(?s. _) ==> _` imp_res_tac
      >> asm_exists_tac
      >> fs[]
    )
    (* 3rd subgoal *)
    >- (
      qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac ((REWRITE_RULE [IS_SOME_EXISTS]) subtype_at_IS_SOME_parent)
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`q`,`r`] assume_tac subtype_at_decomp_path
        >> pop_assum imp_res_tac
        >> fs[]
        >> rveq
        >> imp_res_tac (REWRITE_RULE [IS_SOME_EXISTS] subtype_at_Tyvar)
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >- (
      qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
    (* 2 subgoals*)
    >- (
      qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME _ /\ subtype_at _ _ = SOME _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      (* 4 subgoals *)
      >- (
        rveq
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`x`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        rveq
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`x`,`p`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >- (
      qpat_x_assum `!x y p. _ /\ _ /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        imp_res_tac TYPE_SUBST_drop_prefix
        >> pop_assum (qspec_then `[]` assume_tac)
        >> qpat_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def',IS_SOME_EXISTS])
        >> pop_assum (qspec_then `[]` assume_tac)
        >> fs[NULL_EQ,IS_SOME_EXISTS]
        >> qspecl_then [`x`,`q`,`r`,`a`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rfs[]
        >> rveq
        >> fs[NULL_EQ]
        >> rfs[]
        >> qspecl_then [`y`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >- (qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
    >- (
      qpat_x_assum `!x y p a b. _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`,`b`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> qspecl_then [`x`,`q`,`r`,`a`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rveq
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
  )
  (* last subgoal *)
  >> rw[]
  (* 12 subgoals *)
  >- (
    qpat_x_assum `!a b p. MEM (x,y) orig_l /\ IS_SOME _ /\ IS_SOME _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
    >> rfs[]
    (* 10 subgoals *)
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `b`
      >> fs[IS_SOME_EXISTS]
      >> fs[]
    )
    >- (
      DISJ1_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `b`
      >> fs[IS_SOME_EXISTS]
      >> fs[]
    )
    >- (
      DISJ1_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
      >> fs[]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
      >> fs[]
    )
    >> (
      DISJ2_TAC >> DISJ2_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
      >> fs[]
    )
  )
  >- (
    qpat_x_assum `(?s. _) ==> _` imp_res_tac
    >> qexists_tac `s'`
    >> fs[EVERY_MEM,ELIM_UNCURRY,TYPE_SUBST_compose,TYPE_SUBST_tyvars]
    >> rw[]
    >> qpat_x_assum `!e. _ ==> _` imp_res_tac
    >> Cases_on `x = b`
    >> fs[REV_ASSOCD_def]
  )
  >- (
    first_x_assum ho_match_mp_tac >> fs[]
  )
  >- fs[]
  >- (
    first_x_assum ho_match_mp_tac >> fs[]
  )
  >- (
    qpat_x_assum `!a b. _ = _ /\ _ = _ \/ _ ==> _` (qspecl_then [`Tyvar a`,`Tyvar b`] assume_tac)
    >> rw[]
  )
  >- (
    qpat_x_assum `!a b. MEM _ sigma ==> _` imp_res_tac
    >> asm_exists_tac
    >> fs[]
    >> asm_exists_tac
    >> fs[]
  )
  >- (
    qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
    >> rfs[]
    (* 2 subgoals *)
    >- (
      rveq
      >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> imp_res_tac IS_SOME_THE
      >> fs[option_CLAUSES]
      >> rveq
      >> qspecl_then [`y`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
      >> pop_assum imp_res_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM]
    )
  )
  >- (
    qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
    >> rfs[]
    >- (
      rveq
      >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
      >> pop_assum imp_res_tac
      >> fs[NULL_EQ]
    )
    >- (DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM])
  )
  >- (
    qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = _ /\ subtype_at _ _ = _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
    >> rfs[]
    (* 4 subgoals *)
    >- (
      rveq
      >> imp_res_tac IS_SOME_THE
      >> qspecl_then [`y`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
      >> pop_assum imp_res_tac
      >> fs[]
    )
    >- (
      DISJ2_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM]
    )
    >- (
      rveq
      >> imp_res_tac IS_SOME_THE
      >> qspecl_then [`y`,`p`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
      >> pop_assum imp_res_tac
      >> fs[]
    )
    >- (
      DISJ2_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM]
    )
  )
  >- (
    Cases_on `subtype_at (TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) y) p = subtype_at (TYPE_SUBST sigma y) p`
    >> fs[]
    (* 2 subgoals *)
    >- (
      qpat_x_assum `!x y p. _ /\ _ <> _ /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        imp_res_tac TYPE_SUBST_drop_prefix
        >> pop_assum (qspec_then `[]` assume_tac)
        >> qpat_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def',IS_SOME_EXISTS])
        >> pop_assum (qspec_then `[]` assume_tac)
        >> fs[NULL_EQ,IS_SOME_EXISTS]
        >> qspecl_then [`x`,`q`,`r`,`a`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rfs[]
        >> rveq
        >> fs[NULL_EQ]
        >> rfs[]
        >> qspecl_then [`y`,`q`,`(Tyvar a,Tyvar b)::sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> qspecl_then [`y`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[REV_ASSOCD_def]
      )
      >- (qexists_tac `q` >> qexists_tac `r` >> fs[])
    )
    >> imp_res_tac subtype_at_TYPE_SUBST_ineq
    >> imp_res_tac is_subtype_leaf_IS_SOME_subtype
    >> qpat_x_assum `!x y p. MEM _ _ /\ IS_SOME _ /\ IS_SOME _  ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
    >> rfs[]
    (* 10 subgoals *)
    >- (
      Cases_on `NULL r`
      >- (
        rveq
        >> fs[NULL_EQ,IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> qspecl_then [`y`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> qspecl_then [`y`,`q`,`(Tyvar a,Tyvar b)::sigma`] assume_tac subtype_at_TYPE_SUBST
        >> NTAC 2 (qpat_x_assum `!a. _ ==> _` imp_res_tac)
        >> imp_res_tac TYPE_SUBST_drop_prefix
        >> pop_assum (qspec_then `[]` assume_tac)
        >> rfs[REV_ASSOCD_def]
      )
      >> assume_tac (CONTRAPOS (fst (EQ_IMP_RULE (Q.SPECL [`r`,`a`] subtype_at_Tyvar))))
      >> qspecl_then [`x`,`q`,`r`,`Tyvar a`] assume_tac subtype_at_decomp_path
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
    )
    >- (
      qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >- (
      rveq
      >> qspecl_then [`x`,`p`,`r`] assume_tac subtype_at_decomp_path
      >> fs[is_subtype_leaf_def',IS_SOME_EXISTS]
      >> pop_assum imp_res_tac
      >> fs[option_CLAUSES]
      >> rveq
      >> qpat_x_assum `!q. _ = _` (qspec_then `r` assume_tac)
      >> rfs[NULL_EQ]
      >> fs[subtype_at_def]
      >> rveq
      >> qspecl_then [`y`,`p`,`(Tyvar a,Tyvar b)::sigma`] assume_tac subtype_at_TYPE_SUBST
      >> qpat_x_assum `!a. _ ==> _` imp_res_tac
      >> fs[REV_ASSOCD_def]
    )
    >- (
      rveq
      >> qspecl_then [`x`,`p`,`r`] assume_tac subtype_at_decomp_path
      >> fs[is_subtype_leaf_def',IS_SOME_EXISTS]
      >> pop_assum imp_res_tac
      >> fs[option_CLAUSES]
      >> rveq
      >> qpat_x_assum `!q. _ = _` (qspec_then `r` assume_tac)
      >> rfs[NULL_EQ]
      >> qexists_tac `p` >> qexists_tac `[]`
      >> fs[subtype_at_def]
      >> rveq
      >> fs[]
    )
    >- (
      qspecl_then [`y`,`q`,`r`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> fs[subtype_at_Tyvar,NULL_EQ]
      >> rveq
      >> fs[subtype_at_def]
      >> imp_res_tac TYPE_SUBST_MEM'
      >> qspecl_then [`y`,`q`,`(Tyvar a,Tyvar b)::sigma`] assume_tac subtype_at_TYPE_SUBST
      >> qspecl_then [`y`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
      >> NTAC 2 (qpat_x_assum `!a. _ ==> _` imp_res_tac)
      >> Cases_on `a' = b`
      >> rveq
      >> fs[REV_ASSOCD_def]
      >> assume_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
      >> pop_assum imp_res_tac
      >> fs[]
    )
    >- (
      Cases_on `a' = b`
      >- (
        assume_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
        >> pop_assum imp_res_tac
        >> rveq
        >> fs[]
      )
      >> qspecl_then [`sigma`,`[(Tyvar a,Tyvar b)]`,`a'`] assume_tac TYPE_SUBST_drop_prefix
      >> qspecl_then [`x`,`p`,`r`] assume_tac subtype_at_decomp_path
      >> fs[is_subtype_leaf_def',IS_SOME_EXISTS]
      >> pop_assum imp_res_tac
      >> fs[option_CLAUSES]
      >> rveq
      >> qpat_x_assum `!q. _ = _` (qspec_then `r` assume_tac)
      >> rfs[NULL_EQ]
      >> qspecl_then [`y`,`p`,`(Tyvar a,Tyvar b)::sigma`] assume_tac subtype_at_TYPE_SUBST
      >> qspecl_then [`y`,`p`,`sigma`] assume_tac subtype_at_TYPE_SUBST
      >> NTAC 2 (qpat_x_assum `!a. _ ==> _` imp_res_tac)
      >> rveq
      >> fs[]
      >> rveq
      >> fs[subtype_at_def]
    )
    >- (
      rveq
      >> qspecl_then [`x`,`q`,`r`] assume_tac is_subtype_leafs_imp
      >> rfs[]
      >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
      >> fs[EXISTS_OR_THM]
      >> TRY (qpat_x_assum `SOME _ = subtype_at _ _` (assume_tac o GSYM))
      >> fs[]
      >> qspecl_then [`y`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> fs[TYPE_SUBST_def]
    )
    >- (
      qpat_x_assum `!a. MEM _ e ==> ~MEM _ _` imp_res_tac
      >> qspecl_then [`[]`,`sigma`,`a'`] assume_tac TYPE_SUBST_drop_prefix
      >> qspecl_then [`x`,`q`,`r`] assume_tac is_subtype_leafs_imp
      >> rveq
      >> rfs[]
      >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
      >> TRY (qpat_x_assum `SOME _ = subtype_at _ _` (assume_tac o GSYM))
      >> fs[EXISTS_OR_THM]
      >> rfs[]
      >> qspecl_then [`y`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> Cases_on `a' = b`
      >> fs[TYPE_SUBST_def,REV_ASSOCD_def]
    )
    >- (
      qspecl_then [`y`] assume_tac subtype_at_TYPE_SUBST
      >> fs[]
      >> pop_assum imp_res_tac
      >> qspecl_then [`x`,`p`,`r`] assume_tac is_subtype_leafs_imp
      >> rveq
      >> rfs[]
      >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
      >> TRY (qpat_x_assum `SOME _ = subtype_at _ _` (assume_tac o GSYM))
      >> fs[EXISTS_OR_THM]
      >> rfs[]
      >> rveq
      >> Cases_on `a' = b`
      >> fs[REV_ASSOCD_def,TYPE_SUBST_def]
    )
    >- (
      qpat_x_assum `!a. MEM _ e ==> ~MEM _ _` imp_res_tac
      >> qspecl_then [`[]`,`sigma`,`a'`] assume_tac TYPE_SUBST_drop_prefix
      >> qspecl_then [`y`] assume_tac subtype_at_TYPE_SUBST
      >> fs[]
      >> pop_assum imp_res_tac
      >> qspecl_then [`x`,`p`,`r`] assume_tac is_subtype_leafs_imp
      >> rveq
      >> rfs[]
      >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
      >> TRY (qpat_x_assum `SOME _ = subtype_at _ _` (assume_tac o GSYM))
      >> fs[EXISTS_OR_THM]
      >> rfs[]
      >> Cases_on `b = a'`
      >> fs[TYPE_SUBST_def,REV_ASSOCD_def]
    )
  )
  >- (
    qpat_x_assum `!x y p a b. _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`,`b'`] assume_tac)
    >> rfs[]
    >- (
      rveq
      >> imp_res_tac IS_SOME_THE
      >> qspecl_then [`x`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
      >> pop_assum imp_res_tac
      >> fs[NULL_EQ]
    )
    >- (qexists_tac `q` >> fs[EXISTS_OR_THM])
  )
QED

Theorem instance_subst_inv_pres3[local]:
   ∀m l n l' ls sigma e.
       (m = n ∧ LENGTH l = LENGTH l' ⇒
        ∀sigma' orig_l e'.
            instance_subst_inv orig_l (ZIP (l,l') ⧺ ls) sigma e ∧
            instance_subst (ZIP (l,l') ⧺ ls) sigma e = SOME (sigma',e') ⇒
            instance_subst_inv orig_l [] sigma' e') ⇒
       ∀sigma' orig_l e'.
           instance_subst_inv orig_l ((Tyapp m l,Tyapp n l')::ls) sigma e ∧
           instance_subst ((Tyapp m l,Tyapp n l')::ls) sigma e =
           SOME (sigma',e') ⇒
           instance_subst_inv orig_l [] sigma' e'
Proof
  rw[instance_subst_def]
  >> rfs[]
  >> first_x_assum ho_match_mp_tac
  >> fs[instance_subst_inv_def]
  >> rw[]
  (* 9 subgoals *)
  >- (
    last_x_assum (qspecl_then [`Tyapp m l`,`Tyapp m l'`] assume_tac)
    >> fs[]
    >> imp_res_tac MEM_ZIP
    >> asm_exists_tac
    >> qexists_tac `p++[(m,n)]`
    >> imp_res_tac subtype_at_decomp_path
    >> fs[subtype_at_def]
  )
  >- (
    last_x_assum (qspecl_then [`a`,`b`] assume_tac)
    >> fs[]
  )
  (* 5 subgoals remaining *)
  >- (
    qpat_x_assum `!x y p. MEM _ _ /\ IS_SOME _ /\ IS_SOME _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
    >> rfs[]
    (* 10 subgoals *)
    >- (
      Cases_on `NULL l`
      >- (
        fs[ZIP,NULL_EQ]
        >> rfs[]
        >> DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `m`
        >> imp_res_tac (List.nth(CONJUNCTS option_CLAUSES,8))
        >> rfs[]
      )
      >> imp_res_tac (ccontr_equiv(NULL_LENGTH))
      >> fs[NOT_ZERO_LT_ZERO]
      >> DISJ1_TAC
      >> imp_res_tac subtype_at_decomp_path
      >> Cases_on `NULL r`
      >- (
        fs[IS_SOME_EXISTS]
        >> qexists_tac `q++[(m,0)]`
        >> fs[NULL_EQ]
        >> rfs[]
        >> rveq
        >> imp_res_tac subtype_at_decomp_path
        >> fs[MEM_ZIP,subtype_at_def]
        >> DISJ1_TAC
        >> asm_exists_tac
        >> fs[]
      )
      >> fs[IS_SOME_EXISTS]
      >> imp_res_tac subtype_at_decomp_path
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> Cases_on `r`
      >> fs[]
      >> Cases_on `h`
      >> fs[subtype_at_def]
      >> DISJ1_TAC
      >> fs[MEM_ZIP]
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r`
      >> fs[IS_SOME_EXISTS]
    )
    >- (
      Cases_on `NULL l`
      >- (
        DISJ2_TAC
        >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `m`
        >> fs[IS_SOME_EXISTS,NULL_EQ,option_CLAUSES]
        >> fs[]
      )
      >> DISJ1_TAC
      >> fs[IS_SOME_EXISTS,MEM_ZIP]
      >> imp_res_tac subtype_at_decomp_path
      >> imp_res_tac (ccontr_equiv(NULL_LENGTH))
      >> qexists_tac `p++r++[(m,0)]`
      >> qexists_tac `r++[(m,0)]`
      >> fs[NOT_ZERO_LT_ZERO,subtype_at_def]
      >> DISJ1_TAC
      >> rfs[]
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r`
      >> fs[]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
      >> fs[]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
      >> fs[]
    )
    (* 4 subgoals remaining *)
    >> (
      DISJ2_TAC >> DISJ2_TAC
      >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
      >> fs[]
    )
  )
  >- (
    qpat_x_assum `(?s. _) ==> _` imp_res_tac
    >> qexists_tac `s'`
    >> fs[EVERY_MEM]
    >> rw[ZIP_MAP,ELIM_UNCURRY]
    >> fs[MEM_MAP]
  )
  >- (
    qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` imp_res_tac
    >> fs[]
    (* 4 subgoals *)
    >- (
      Cases_on `NULL r`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> rfs[]
      )
      >> DISJ1_TAC
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> rpt (PRED_ASSUM (exists (curry op = "q'" o fst o dest_var) o free_vars) kall_tac)
      >> drule_then strip_assume_tac (Ho_Rewrite.REWRITE_RULE[IS_SOME_EXISTS,PULL_EXISTS] subtype_at_IS_SOME_parent)
      >> qspecl_then [`y`,`q++[HD r]`,`TL r`] mp_tac subtype_at_IS_SOME_parent
      >> fs[IS_SOME_EXISTS]
      >> rfs[option_CLAUSES]
      >> NTAC 2 (dxrule_then (qspec_then `[HD r]` strip_assume_tac) subtype_at_decomp_path)
      >> impl_tac
      >- (
        PURE_REWRITE_TAC[GSYM APPEND_ASSOC,GSYM CONS_APPEND]
        >> fs[CONS]
      )
      (* >> qspecl_then [`x`,`q`,`[HD r]`,`Tyapp m l`] assume_tac subtype_at_decomp_path
      >> qspecl_then [`y`,`q`,`[HD r]`,`Tyapp m l'`] assume_tac subtype_at_decomp_path
      >> qspecl_then [`y`,`q`,`r`] assume_tac subtype_at_IS_SOME_parent
      >> fs[IS_SOME_EXISTS]
      *)
      >> rpt (dxrule_all_then strip_assume_tac (Ho_Rewrite.REWRITE_RULE[IS_SOME_EXISTS,PULL_EXISTS] subtype_at_IS_SOME_parent))
      >> strip_tac
      >> Cases_on `HD r`
      >> fs[subtype_at_def]
      >> fs[]
      >> fs[MEM_ZIP]
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC
      >> qexists_tac `q'` >> qexists_tac `r'`
      >> fs[]
    )
    >> (
      DISJ1_TAC
      >> qexists_tac `q` >> qexists_tac `r`
      >> fs[]
    )
  )
  >- (
    qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyapp _ _) ==> _`
      (qspecl_then [`x`,`y`,`p`,`a`] assume_tac)
    >> rfs[]
    >- (
      rveq
      >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> Cases_on `NULL l`
      >- (
        fs[NULL_EQ]
        >> rveq
        >> qspecl_then [`y`,`q`] assume_tac (CONJUNCT2 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >> Cases_on `r`
      >- fs[NULL_EQ]
      >> Cases_on `h`
      >> qpat_x_assum `subtype_at _ _ = SOME (Tyapp _ [])` (assume_tac o REWRITE_RULE[Once CONS_APPEND,APPEND_ASSOC])
      >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> DISJ1_TAC
      >> qexists_tac `q++[(q',r)]`
      >> fs[EXISTS_OR_THM]
      >> qspecl_then [`y`,`q`,`[(q',r)]`,`Tyapp m l'`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`x`,`q`,`[(q',r)]`,`Tyapp m l`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> fs[subtype_at_def]
      >> FULL_CASE_TAC
      >> rfs[]
      >> fs[MEM_ZIP]
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM])
  )
  >- (
    qpat_x_assum `!x y p a. _ /\ _ /\ _ ==> _` (qspecl_then [`x`,`y`,`p`,`a`] assume_tac)
    >> rfs[]
    >- (
      rveq
      >> imp_res_tac IS_SOME_THE
      >> Cases_on `NULL l`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> qspec_then `y` assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[option_CLAUSES]
        >> rveq
        >> imp_res_tac (snd (EQ_IMP_RULE (SPEC_ALL is_subtype_leaf_eq)))
        >> qspecl_then [`x`,`q`,`r`] assume_tac is_subtype_leafs_imp
        >> fs[]
      )
      >> Cases_on `NULL r`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> rveq
        >> fs[]
      )
      >> imp_res_tac CONS
      >> qspecl_then [`x`,`q++[HD r]`,`TL r`] assume_tac subtype_at_IS_SOME_parent
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,GSYM CONS_APPEND])
      >> qspecl_then [`y`,`q++[HD r]`,`TL r`] assume_tac subtype_at_IS_SOME_parent
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,GSYM CONS_APPEND])
      >> DISJ2_TAC
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> REWRITE_TAC[GSYM APPEND_ASSOC,GSYM CONS_APPEND]
      >> rw[MEM_ZIP]
      >> DISJ1_TAC
      >> qspecl_then [`x`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> qspecl_then [`y`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> rfs[]
      >> Cases_on `HD r`
      >> fs[subtype_at_def]
      >> FULL_CASE_TAC
      >> fs[]
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >- (
      imp_res_tac subtype_at_decomp_path
      >> NTAC 2 (first_x_assum (qspec_then `r` assume_tac))
      >> qspecl_then [`r`,`a`] assume_tac subtype_at_Tyvar
      >> fs[option_CLAUSES,NULL_EQ]
      >> imp_res_tac IS_SOME_THE
      >> fs[]
    )
    >- (
      DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
  >- (
    qpat_x_assum `!x y p. _ /\ _ /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
    >> rfs[]
    >- (
      Cases_on `NULL l`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> qspec_then `y` assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[option_CLAUSES]
        >> rveq
        >> imp_res_tac (snd (EQ_IMP_RULE (SPEC_ALL is_subtype_leaf_eq)))
        >> qspecl_then [`x`,`q`,`r`] assume_tac is_subtype_leafs_imp
        >> fs[]
      )
      >> imp_res_tac is_subtype_leaf_IS_SOME_subtype
      >> Cases_on `NULL r`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> rveq
        >> fs[is_subtype_leaf_eq]
      )
      >> imp_res_tac is_subtype_leaf_IS_SOME_subtype
      >> qspecl_then [`x`,`p++[HD r]`,`TL r`] assume_tac subtype_at_IS_SOME_parent
      >> imp_res_tac CONS
      >> qspecl_then [`x`,`q++[HD r]`,`TL r`] assume_tac subtype_at_IS_SOME_parent
      >> qexists_tac `q++[HD r]` >> qexists_tac `TL r`
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,GSYM CONS_APPEND])
      >> REWRITE_TAC[GSYM APPEND_ASSOC,GSYM CONS_APPEND]
      >> rveq
      >> fs[]
      >> rfs[]
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> qspecl_then [`x`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> qspecl_then [`y`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> rfs[]
      >> Cases_on `HD r`
      >> fs[subtype_at_def]
      >> DISJ1_TAC
      >> FULL_CASE_TAC
      >> fs[MEM_ZIP]
      >- (
        asm_exists_tac
        >> fs[]
      )
      >> fs[]
    )
    >- (
      qexists_tac `q` >> qexists_tac `r`
      >> fs[]
    )
  )
  >- (
    qpat_x_assum `!x y p a b. _ ==> _` (qspecl_then [`x`,`y`,`p`,`a`,`b`] assume_tac)
    >> rfs[]
    >- (
      imp_res_tac IS_SOME_THE
      >> Cases_on `r`
      >> fs[]
      >> qspecl_then [`x`,`q`,`[h]++t`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`y`,`q`,`[h]++t`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`x`,`q`,`[h]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`y`,`q`,`[h]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> Cases_on `h`
      >> fs[subtype_at_def]
      >> FULL_CASE_TAC
      >> rfs[subtype_at_def]
      >> qexists_tac `q++[(q',r)]`
      >> fs[EXISTS_OR_THM,MEM_ZIP]
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
QED

Theorem instance_subst_inv_pres4[local]:
   ∀v0 sigma e v3 sigma' e' sigma'' orig_l e''.
       instance_subst_inv orig_l ((Tyvar v0,Tyapp sigma e)::v3) sigma' e' ∧
       instance_subst ((Tyvar v0,Tyapp sigma e)::v3) sigma' e' =
       SOME (sigma'',e'') ⇒
       instance_subst_inv orig_l [] sigma'' e''
Proof
    rw[instance_subst_def]
QED

Theorem MAP_diff[local]:
  !l f f'. (MAP f l <> MAP f' l) = ?x. MEM x l /\ (f x <> f' x)
Proof
  Induct >> fs[RIGHT_AND_OVER_OR,EXISTS_OR_THM]
QED

Theorem TYPE_SUBST_ineq_subtype_at[local]:
  !x sigma a b.
  ~MEM (Tyvar a) (MAP SND sigma) /\
  TYPE_SUBST ((b,Tyvar a)::sigma) x <> TYPE_SUBST sigma x
  ==> ?q. subtype_at x q = SOME (Tyvar a)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rw[]
    >> imp_res_tac TYPE_SUBST_drop_prefix
    >> pop_assum (qspec_then `[]` assume_tac)
    >> qexists_tac `[]`
    >> fs[TYPE_SUBST_NIL,REV_ASSOCD_def,subtype_at_def]
    >> FULL_CASE_TAC
    >> fs[]
  )
  >> rw[EVERY_MEM]
  >> fs[MAP_diff]
  >> last_x_assum (qspec_then `a'` assume_tac)
  >> rfs[]
  >> first_x_assum (qspecl_then [`sigma`,`a`,`b`] assume_tac)
  >> rfs[MEM_EL]
  >> rveq
  >> qexists_tac `(m,n)::q`
  >> fs[subtype_at_def]
QED

Theorem subtype_at_TYPE_SUBST_ineq_subtype_at[local]:
  !x p sigma a b.
  ~MEM (Tyvar a) (MAP SND sigma) /\
  subtype_at (TYPE_SUBST ((b,Tyvar a)::sigma) x) p <> subtype_at (TYPE_SUBST sigma x) p
  ==>
  IS_SOME (subtype_at (TYPE_SUBST ((b,Tyvar a)::sigma) x) p)
  /\ ?q r. (p = q++r \/ q=p++r) /\ subtype_at x q = SOME (Tyvar a)
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rw[]
    >> imp_res_tac TYPE_SUBST_drop_prefix
    >> pop_assum (qspec_then `[]` assume_tac)
    >> fs[TYPE_SUBST_NIL,REV_ASSOCD_def,subtype_at_def]
    >> FULL_CASE_TAC
    >> fs[]
    >- (
      Cases_on `p`
      >> fs[subtype_at_def,quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE]
    )
    >> fs[]
    >> imp_res_tac TYPE_SUBST_drop_prefix
    >> pop_assum (qspec_then `[]` assume_tac)
    >> fs[TYPE_SUBST_NIL,REV_ASSOCD_def,subtype_at_def]
    >> qexists_tac `[]`
    >> fs[subtype_at_def,EXISTS_OR_THM]
  )
  >> rw[EVERY_MEM]
  >> Cases_on `NULL l`
  >> fs[subtype_at_def,NULL_EQ]
  >> Cases_on `p`
  >- fs[subtype_at_def,NULL_EQ,MAP_diff,PULL_FORALL]
  >- (
    Cases_on `h`
    >> fs[subtype_at_def]
    >> FULL_CASE_TAC
    >> fs[subtype_at_def]
    >> imp_res_tac TYPE_SUBST_EL
    >> fs[PULL_FORALL]
    >> first_x_assum (qspecl_then [`EL r l`,`t`,`sigma`,`a`,`b`] assume_tac)
    >> imp_res_tac MEM_EL
    >> fs[]
    >> rfs[]
  )
  (* 2 subgoals remaining *)
  >- (
    fs[subtype_at_def,MAP_diff,PULL_FORALL]
    >> qpat_x_assum `MEM _ _` (assume_tac o REWRITE_RULE[MEM_EL])
    >> fs[]
    >> imp_res_tac MEM_EL
    >> first_x_assum (qspecl_then [`EL n l`,`[]`,`sigma`,`a`,`b`] assume_tac)
    >> rveq
    >> rfs[subtype_at_def]
    >- (
      qexists_tac `[(m,n)]`
      >> fs[subtype_at_def]
    )
    >> qexists_tac `(m,n)::q`
    >> fs[subtype_at_def]
  )
  >- (
    Cases_on `h`
    >> fs[subtype_at_def]
    >> FULL_CASE_TAC
    >> fs[subtype_at_def,PULL_FORALL]
    >> imp_res_tac MEM_EL
    >> imp_res_tac TYPE_SUBST_EL
    >> first_x_assum (qspecl_then [`EL r l`,`t`,`sigma`,`a`,`b`] assume_tac)
    >> rfs[]
    >> qexists_tac `(q,r)::q'`
    >> rw[subtype_at_def,EXISTS_OR_THM]
  )
QED

Theorem APPEND_EQ_APPEND_IS_PREFIX:
  !p q r s. p ++ q = r ++ s ==> p ≼ r \/ r ≼ p
Proof
  rpt strip_tac
  >> fs[IS_PREFIX_APPEND,APPEND_EQ_APPEND,EXISTS_OR_THM]
QED

Theorem is_subtype_leafs_init[local]:
  !x p q r s. is_subtype_leaf x p /\ IS_SOME (subtype_at x r)
  /\ p ++ q = r ++ s ==> r ≼ p
Proof
  rpt strip_tac
  >> imp_res_tac APPEND_EQ_APPEND_IS_PREFIX
  >> fs[is_subtype_leaf_def',IS_PREFIX_APPEND]
  >> rveq
  >> fs[NULL_EQ]
  >> last_x_assum imp_res_tac
QED

Theorem instance_subst_inv_pres5[local]:
   ∀m l a l' sigma e.
       (¬MEM (Tyapp m l,Tyvar a) sigma ∧ ¬MEM (Tyvar a) (MAP SND sigma) ∧
        ¬MEM a e ⇒
        ∀sigma' orig_l e'.
            instance_subst_inv orig_l l' ((Tyapp m l,Tyvar a)::sigma) e ∧
            instance_subst l' ((Tyapp m l,Tyvar a)::sigma) e =
            SOME (sigma',e') ⇒
            instance_subst_inv orig_l [] sigma' e') ∧
       (MEM (Tyapp m l,Tyvar a) sigma ⇒
        ∀sigma' orig_l e'.
            instance_subst_inv orig_l l' sigma e ∧
            instance_subst l' sigma e = SOME (sigma',e') ⇒
            instance_subst_inv orig_l [] sigma' e') ⇒
       ∀sigma' orig_l e'.
           instance_subst_inv orig_l ((Tyapp m l,Tyvar a)::l') sigma e ∧
           instance_subst ((Tyapp m l,Tyvar a)::l') sigma e =
           SOME (sigma',e') ⇒
           instance_subst_inv orig_l [] sigma' e'
Proof
  rw[instance_subst_def]
  >> first_x_assum ho_match_mp_tac
  >> fs[instance_subst_inv_def]
  >- (
    strip_tac
    (* 7 subgoals *)
    >- (
      rw[]
      >> qpat_x_assum `!x y p. MEM _ _ /\ IS_SOME _ /\ IS_SOME _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[IS_SOME_EXISTS]
      >> fs[]
      >> imp_res_tac subtype_at_decomp_path
      (* 10 subgoals *)
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
        >> fs[]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
        >> fs[]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `(?s. _) ==> _` imp_res_tac
      >> asm_exists_tac
      >> fs[]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p a. _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` imp_res_tac
      >> fs[]
      (* 4 subgoals *)
      >- (
        Cases_on `NULL r`
        >- (
          fs[NULL_EQ,IS_SOME_EXISTS]
          >> rfs[]
        )
        >> qspecl_then [`y`,`q`,`r`] assume_tac subtype_at_IS_SOME_parent
        >> fs[IS_SOME_EXISTS]
        >> rfs[]
        >> fs[option_CLAUSES]
        >> rveq
        >> imp_res_tac (CONJUNCT1 subtype_at_leaf_imp)
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q'`
        >> qexists_tac `r'`
        >> fs[]
      )
      >> (
        DISJ1_TAC
        >> qexists_tac `q`
        >> qexists_tac `r`
        >> fs[]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p a. _ /\ subtype_at _ _ = SOME (Tyapp _ _) ==> _`
        (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p a. _ ==> MEM _ _ \/ _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`q`,`r`] assume_tac is_subtype_leafs_imp
        >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
        >> rveq
        >> rfs[EXISTS_OR_THM]
        >> fs[]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`p`,`r`] assume_tac is_subtype_leafs_imp
        >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
        >> rveq
        >> rfs[EXISTS_OR_THM]
        >> fs[]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p. _ /\ _ /\ _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac TYPE_SUBST_MEM'
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`q`,`sigma`,`Tyvar a`] assume_tac subtype_at_TYPE_SUBST
        >> qspecl_then [`TYPE_SUBST sigma y`,`q`] assume_tac subtype_at_decomp_path
        >> rfs[]
        >> pop_assum (qspec_then `r` assume_tac)
        >> qspec_then `x` assume_tac subtype_at_decomp_path
        >> pop_assum imp_res_tac
        >> rveq
        >> fs[]
      )
      >- (
        qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >- (
      rw[]
      >> qpat_x_assum `!x y p a b. _ /\ _ /\ _ /\ _ /\ _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`,`b`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rveq
        >> pop_assum imp_res_tac
        >> rveq
        >> fs[NULL_EQ]
        >> Q.ISPEC_THEN `SND:type#type->type` imp_res_tac MEM_MAP_f
        >> fs[]
      )
      >- (qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
  )
  >- (
    strip_tac
    (* 12 subgoals *)
    >- (
      rw[]
      >> qpat_x_assum `!x y p. MEM _ _ /\ IS_SOME _ /\ IS_SOME _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
      >> rfs[IS_SOME_EXISTS]
      >> fs[]
      >> imp_res_tac subtype_at_decomp_path
      (* 10 subgoals *)
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
        >> fs[]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a`
        >> fs[]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> qexists_tac `r` >> qexists_tac `a'`
        >> fs[]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `(?s. _) ==> (?s._)` imp_res_tac
      >> qexists_tac `s'`
      >> fs[EVERY_MEM,ELIM_UNCURRY,TYPE_SUBST_tyvars]
      >> rw[]
      >> qpat_x_assum `!e. _ ==> _` imp_res_tac
      >> Cases_on `x = a`
      >> fs[REV_ASSOCD_def]
    )
    >> strip_tac
    >- (rw[] >> rw[])
    >> strip_tac
    >- (rw[] >> rw[])
    >> strip_tac
    >- (rw[] >> fs[])
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> qspecl_then [`y`,`q`,`r`] imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> imp_res_tac IS_SOME_THE
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p a. MEM _ _ /\ subtype_at _ _ = SOME (Tyapp _ _) ==> _`
        (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!x y p a. _ /\ subtype_at _ _ = SOME _ /\ subtype_at _ _ = SOME _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        rveq
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`p`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> Cases_on `subtype_at (TYPE_SUBST ((Tyapp m l,Tyvar a)::sigma) y) p = subtype_at (TYPE_SUBST sigma y) p`
      >> fs[]
      (* 2 subgoals *)
      >- (
        qpat_x_assum `!x y p. _ /\ _ /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`x`,`y`,`p`] assume_tac)
        >> rfs[]
        (* 2 subgoals *)
        >- (
          imp_res_tac TYPE_SUBST_drop_prefix
          >> pop_assum (qspec_then `[]` assume_tac)
          >> qpat_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def',IS_SOME_EXISTS])
          >> pop_assum (qspec_then `[]` assume_tac)
          >> fs[NULL_EQ,IS_SOME_EXISTS]
          >> qspecl_then [`y`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
          >> qspecl_then [`y`,`q`,`(Tyapp m l,Tyvar a)::sigma`] assume_tac subtype_at_TYPE_SUBST
          >> NTAC 2 (qpat_x_assum `!a. _` imp_res_tac)
          >> qspecl_then [`TYPE_SUBST sigma y`,`q`,`r`,`TYPE_SUBST sigma (Tyvar a)`] assume_tac subtype_at_decomp_path
          >> qspecl_then [`TYPE_SUBST ((Tyapp m l,Tyvar a)::sigma) y`,`q`,`r`,`TYPE_SUBST ((Tyapp m l,Tyvar a)::sigma) (Tyvar a)`] assume_tac subtype_at_decomp_path
          >> qspecl_then [`x`,`q`,`r`,`Tyapp m l`] assume_tac subtype_at_decomp_path
          >> fs[option_CLAUSES]
          >> rveq
          >> rfs[REV_ASSOCD_def]
        )
        >- (qexists_tac `q` >> qexists_tac `r` >> fs[])
      )
      >> qspecl_then [`y`,`p`,`sigma`,`a`,`Tyapp m l`] assume_tac subtype_at_TYPE_SUBST_ineq_subtype_at
      >> rfs[]
      >> `subtype_at (TYPE_SUBST sigma y) q = subtype_at y q` by (
        imp_res_tac subtype_at_TYPE_SUBST
        >> imp_res_tac TYPE_SUBST_drop_prefix
        >> pop_assum (qspec_then `[]` assume_tac)
        >> fs[TYPE_SUBST_NIL]
      )
      (* 2 subgoals *)
      >- (
        qpat_x_assum `!x y p a'. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`x`,`y`,`q`,`a`] assume_tac)
        >> rfs[]
        (* 4 subgoals *)
        >- (
          `subtype_at x q = subtype_at (TYPE_SUBST ((Tyapp m l,Tyvar a)::sigma) y) q` by (
            qspecl_then [`y`,`q'`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> qspecl_then [`y`,`q'`,`r'`] assume_tac subtype_at_IS_SOME_parent
            >> rveq
            >> fs[IS_SOME_EXISTS,EXISTS_OR_THM]
            >> fs[option_CLAUSES]
            >> rveq
            >> rfs[]
            >> fs[option_CLAUSES]
            >> rveq
            >> rfs[]
            >> qspec_then `y` assume_tac subtype_at_TYPE_SUBST
            >> pop_assum imp_res_tac
            >> rw[REV_ASSOCD_def]
          )
          >> imp_res_tac subtype_at_eq'
          >> pop_assum (qspec_then `r` assume_tac)
          >> rveq
          >> fs[]
        )
        >- (
          qexists_tac `q'`
          >> fs[EXISTS_OR_THM]
          >> match_mp_tac subtype_at_IS_SOME_parent
          >> fs[IS_SOME_EXISTS]
          >> asm_exists_tac
          >> fs[]
        )
        >- (
          imp_res_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
          >> fs[]
        )
        >- (
          qpat_x_assum `!x y p. MEM _ _ /\ IS_SOME _ /\ IS_SOME _ ==> _` (qspecl_then [`x`,`y`,`q`] assume_tac)
          >> rfs[IS_SOME_EXISTS]
          >> fs[]
          (* 10 subgoals *)
          >- (
            qspecl_then [`y`,`q'`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> fs[]
          )
          >- (
            qexists_tac `q'`
            >> fs[EXISTS_OR_THM,option_CLAUSES]
          )
          >- (
            qspecl_then [`y`,`q`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> fs[]
          )
          >- (
            qspecl_then [`y`,`q`,`r'`] assume_tac subtype_at_decomp_path
            >> pop_assum imp_res_tac
            >> qexists_tac `q++r'`
            >> fs[option_CLAUSES]
            >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_Tyvar)
            >> fs[NULL_EQ]
          )
          >- (
            qspecl_then [`y`,`q'`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> fs[]
            >> rveq
            >> imp_res_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
            >> fs[]
          )
          >- (
            qspecl_then [`y`,`q`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> fs[]
            >> rveq
            >> imp_res_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
            >> fs[]
          )
          >- (
            qspecl_then [`y`,`q'`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> rveq
            >> fs[]
          )
          >- (
            qspecl_then [`y`,`q'`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> rveq
            >> fs[]
            >> rveq
            >> fs[]
          )
          >- (
            qspecl_then [`y`,`q`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> rveq
            >> fs[]
          )
          >- (
            qspecl_then [`y`,`q`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> rveq
            >> fs[]
            >> rveq
            >> fs[]
          )
        )
      )
      (* last subgoal *)
      >- (
        qpat_x_assum `!x y p a'. MEM _ _ /\ subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`x`,`y`,`q`,`a`] assume_tac)
        >> rfs[]
        (* 4 subgoals *)
        >- (
          qspecl_then [`y`,`q'`,`r'`] assume_tac is_subtype_leafs_imp
          >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
          >> rveq
          >> qspecl_then [`y`,`q'`,`r'`] assume_tac subtype_at_IS_SOME_parent
          >> rfs[EXISTS_OR_THM,IS_SOME_EXISTS]
          >> fs[]
          >> rfs[]
          >> fs[option_CLAUSES]
          >> rveq
          >> qpat_assum `is_subtype_leaf _ _` ((qspec_then `r` assume_tac) o REWRITE_RULE[is_subtype_leaf_def'])
          >> rfs[option_CLAUSES,NULL_EQ]
          >> qspecl_then [`y`,`q'`] assume_tac subtype_at_TYPE_SUBST
          >> pop_assum imp_res_tac
          >> fs[REV_ASSOCD_def]
        )
        >- (
          rveq
          >> qspecl_then [`x`,`p`,`r`,`q'`,`r'`] assume_tac is_subtype_leafs_init
          >> qexists_tac `q'`
          >> rfs[]
          >> fs[IS_PREFIX_APPEND,BOTH_EXISTS_AND_THM]
          >> match_mp_tac subtype_at_IS_SOME_parent
          >> fs[IS_SOME_EXISTS]
          >> asm_exists_tac
          >> fs[]
        )
        >- (
          imp_res_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
          >> fs[]
        )
        >- (
          rveq
          >> imp_res_tac is_subtype_leafs_imp
          >> pop_assum (qspec_then `r` (assume_tac o REWRITE_RULE[is_subtype_leaf_eq]))
          >> rfs[EXISTS_OR_THM]
          >> fs[]
          >> qpat_x_assum `!x y p a. MEM _ _ /\ _ = SOME _ /\ _ = SOME _ ==> _` (qspecl_then [`x`,`y`,`p`,`a`] assume_tac)
          >> rfs[]
          >> fs[]
          (* 4 subgoals *)
          >- (
            imp_res_tac IS_SOME_THE
            >> qspecl_then [`y`,`q`,`r'`] assume_tac is_subtype_leafs_imp
            >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
            >> rveq
            >> rfs[EXISTS_OR_THM]
            >> fs[]
          )
          >- (
            qexists_tac `q`
            >> fs[EXISTS_OR_THM]
          )
          >- (
            imp_res_tac IS_SOME_THE
            >> qpat_x_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def'])
            >> first_x_assum (qspec_then `r'` assume_tac)
            >> fs[NULL_EQ]
            >> rveq
            >> fs[]
          )
          >- (
            qpat_x_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def'])
            >> first_x_assum (qspec_then `r'` assume_tac)
            >> fs[NULL_EQ]
            >> qexists_tac `p`
            >> fs[]
          )
        )
      )
    )
    >- (
      rw[]
      >> qpat_x_assum `!x y p a b. _ ==> _` (qspecl_then [`x`,`y`,`p`,`a'`,`b`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> qspecl_then [`y`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rveq
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (qexists_tac `q` >> fs[EXISTS_OR_THM])
    )
  )
QED

Theorem instance_subst_inv_pres:
  !l sigma e sigma' orig_l e'.
  instance_subst_inv orig_l l sigma e
  /\ instance_subst l sigma e = SOME (sigma',e')
  ==> instance_subst_inv orig_l [] sigma' e'
Proof
  ho_match_mp_tac instance_subst_ind
  >> conj_tac
  >- (
    rpt strip_tac
    >> match_mp_tac instance_subst_inv_pres1
    >> asm_exists_tac >> fs[]
  )
  >> conj_tac
  >- (
    rpt strip_tac
    >> assume_tac instance_subst_inv_pres2
    >> first_x_assum (qspecl_then [`a`,`b`,`l`,`sigma`,`e`] assume_tac)
    >> fs[]
  )
  >> conj_tac
  >- (
    rpt strip_tac
    >> (qspecl_then [`m`,`l`,`n`,`l'`,`x`,`sigma`,`e`] assume_tac) instance_subst_inv_pres3
    >> rfs[]
  )
  >> conj_tac
  >- (
    rpt strip_tac
    >> imp_res_tac instance_subst_inv_pres4
  )
  >- (
    rpt strip_tac
    >> (qspecl_then [`m`,`l`,`a`,`l'`,`sigma`,`e`] assume_tac) instance_subst_inv_pres5
    >> rfs[]
  )
QED

Theorem instance_subst_inv_imp:
  !l sigma e. instance_subst l [] [] = SOME (sigma,e)
  ==> instance_subst_inv l [] sigma e
Proof
  rw[]
  >> match_mp_tac instance_subst_inv_pres
  >> fs[Once CONJ_COMM]
  >> asm_exists_tac
  >> fs[instance_subst_inv_init]
QED

Theorem is_subtype_leaf_TYPE_SUBST_parent[local]:
  !t s p. is_subtype_leaf (TYPE_SUBST s t) p ==> ?q r. p = q ++ r /\ is_subtype_leaf t q
Proof
  ho_match_mp_tac type_ind
  >> rw[]
  >- (
    qexists_tac `[]`
    >> qexists_tac `p`
    >> fs[is_subtype_leaf_Tyvar]
  )
  >> Cases_on `NULL l`
  >- (
    qexists_tac `p`
    >> qexists_tac `[]`
    >> fs[NULL_EQ]
  )
  >> Cases_on `p`
  >- (
    imp_res_tac is_subtype_leaf_Tyapp
    >> fs[NULL_EQ]
  )
  >> Cases_on `h`
  >> Cases_on `q = m /\ r < LENGTH l`
  >> fs[subtype_at_def,is_subtype_leaf_def',EVERY_MEM]
  >- (
    first_x_assum (qspec_then `EL r l` assume_tac)
    >> fs[MEM_EL]
    >> pop_assum imp_res_tac
    >> fs[]
    >> pop_assum (qspecl_then [`s`,`t`] assume_tac)
    >> imp_res_tac TYPE_SUBST_EL
    >> fs[]
    >> pop_assum imp_res_tac
    >> pop_assum imp_res_tac
    >> qexists_tac `(m,r)::q'`
    >> qexists_tac `r'`
    >> fs[is_subtype_leaf_def',subtype_at_def]
  )
  >> (
    fs[subtype_at_def]
    >> first_x_assum (qspec_then `[]` assume_tac)
    >> fs[NULL_EQ]
  )
QED

Theorem instance_subst_soundness:
  !t t' s e. instance_subst [(t',t)] [] [] = SOME (s,e) ==> (t' = TYPE_SUBST s t)
Proof
  rw[]
  >> imp_res_tac instance_subst_inv_imp
  >> fs[instance_subst_inv_def]
  >> rw[is_subtype_leaf_eq']
  >- (
    imp_res_tac is_subtype_leaf_TYPE_SUBST_parent
    >> qpat_x_assum `!p. _ \/ _` (qspec_then `p` assume_tac)
    >> fs[]
    >> fs[]
  )
  >- (
    qpat_x_assum `!p. _ \/ _` (qspec_then `p` assume_tac)
    >> fs[]
    >> imp_res_tac is_subtype_leaf_TYPE_SUBST_parent
    >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
    >> fs[]
    (* 2 subgoals *)
    >- (
      qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`q`,`a`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac TYPE_SUBST_MEM'
        >> imp_res_tac subtype_at_TYPE_SUBST
        >> ho_match_mp_tac subtype_at_eqs_imp
        >> fs[option_CLAUSES]
      )
      >- (
        qpat_x_assum `!p a. _ ==> MEM _ e` imp_res_tac
        >> ho_match_mp_tac subtype_at_eqs_imp
        >> qpat_x_assum `!a. _ ==> ~MEM _ (MAP SND _)` imp_res_tac
        >> imp_res_tac subtype_at_TYPE_SUBST
        >> imp_res_tac TYPE_SUBST_drop_prefix
        >> pop_assum (qspec_then `[]` assume_tac)
        >> fs[TYPE_SUBST_NIL]
      )
    )
    >- (
      qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`q`,`a`] assume_tac)
      >> rfs[]
      >> qspecl_then [`q`,`t'`,`TYPE_SUBST s t`] assume_tac subtype_at_eq'
      >> qspecl_then [`t`,`q`,`s`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> fs[TYPE_SUBST_def]
    )
  )
QED

Theorem instance_subst_soundness_list:
  !l s e. instance_subst l [] [] = SOME (s,e)
  ==> EVERY (λ(t,t'). t = TYPE_SUBST s t') l
Proof
  rw[]
  >> qspecl_then [`Tyapp m (MAP SND l)`,`Tyapp m (MAP FST l)`,`s`,`e`] assume_tac instance_subst_soundness
  >> rfs[instance_subst_def,ZIP_MAP_FST_SND_EQ]
  >> rw[EVERY_MEM,ELIM_UNCURRY]
  >> fs[MAP_MAP_o,MAP_EQ_f]
QED

(* Instantiation fails: ~(ty1 <= ty2)
 * ty1 and ty2 contain a Tyapp of different name or arguments as a subtype at
 * the same path *)
Theorem instance_subst_complete_Tyapp_no_instance:
  !ty1 ty2. (?p a atys b btys.
     subtype_at ty1 p = SOME (Tyapp a atys) /\ subtype_at ty2 p = SOME (Tyapp b btys)
     /\ (a <> b \/ LENGTH atys <> LENGTH btys)) ==> !s. (TYPE_SUBST s ty2) <> ty1
Proof
  rw[]
  >- (
    pop_assum mp_tac
    >> last_x_assum mp_tac
    >> imp_res_tac subtype_at_TYPE_SUBST
    >> rw[subtype_at_eq]
    >> first_x_assum (qspec_then `s` assume_tac)
    >> qexists_tac `p`
    >> rw[TYPE_SUBST_Tyapp_ident]
  )
  >- (
    pop_assum mp_tac
    >> last_x_assum mp_tac
    >> imp_res_tac subtype_at_TYPE_SUBST
    >> rw[subtype_at_eq]
    >> first_x_assum (qspec_then `s` assume_tac)
    >> qexists_tac `p`
    >> rw[TYPE_SUBST_Tyapp_ident]
    >> DISJ2_TAC
    >> match_mp_tac (Q.prove(`LENGTH (l1:type list) <> LENGTH l2 ==> l1 <> l2`,strip_tac >> CCONTR_TAC >> rw[]))
    >> rw[LENGTH_MAP]
  )
QED

(* Instantiation fails: ~(ty1 <= ty2)
 * ty2 contains same Tyvar at two different paths that should be instantiated to
 * two different types *)
Theorem instance_subst_complete_Tyvar_no_instance:
  !ty1 ty2. (?p q a b c.
    subtype_at ty1 p = SOME b /\ subtype_at ty2 p = SOME (Tyvar a)
    /\ subtype_at ty1 q = SOME c /\ subtype_at ty2 q = SOME (Tyvar a)
      /\ b <> c
    ) ==> !s. (TYPE_SUBST s ty2) <> ty1
Proof
  rw[]
  >> rw[subtype_at_eq]
  >> rpt (qpat_x_assum `subtype_at ty1 _ = _` mp_tac)
  >> imp_res_tac subtype_at_TYPE_SUBST
  >> rpt (first_x_assum (qspec_then `s` assume_tac))
  >> Cases_on `b = TYPE_SUBST s (Tyvar a)`
  >> rw[]
  >- (qexists_tac `q` >> fs[])
  >- (qexists_tac `p` >> fs[])
QED

(* Instantiation fails: ~(ty1 <= ty2)
 * ty2 contains a type constructor at the path where ty1 contains a type
 * variable *)
Theorem instance_subst_complete_Tyvar_Tyapp_no_instance:
  !ty1 ty2. (
      ?p a b tys. subtype_at ty1 p = SOME (Tyvar a) /\ subtype_at ty2 p = SOME (Tyapp b tys)
    ) ==> !s. (TYPE_SUBST s ty2) <> ty1
Proof
  rw[]
  >> last_x_assum mp_tac
  >> imp_res_tac subtype_at_TYPE_SUBST
  >> first_x_assum (qspec_then `s` assume_tac)
  >> rw[subtype_at_eq]
  >> qexists_tac `p`
  >> rw[]
QED

Theorem TYPE_SUBST_Tyvar_no_fixpoint:
  !s m. TYPE_SUBST s (Tyvar m) <> (Tyvar m)
  ==> MEM (Tyvar m) (MAP SND s)
Proof
  rw[]
  >> CCONTR_TAC
  >> imp_res_tac TYPE_SUBST_drop_prefix
  >> first_x_assum (qspec_then `[]` assume_tac)
  >> fs[]
QED

Theorem is_subtype_leaf_EL:
  !m l t n. n < LENGTH l ==> is_subtype_leaf (Tyapp m l) ((m,n)::t)
  = is_subtype_leaf (EL n l) t
Proof
  rw[is_subtype_leaf_def',subtype_at_def]
  >> rfs[]
QED

Theorem EQ_LIST_EL:
  !l1 l2. (l1 = l2) = (LENGTH l1 = LENGTH l2 /\ !n. n < LENGTH l1 ==> EL n l1 = EL n l2)
Proof
  Induct >> rw[EQ_IMP_THM]
  >> fs[]
  >> first_assum (qspec_then `0` assume_tac)
  >> last_x_assum (qspec_then `TL l2` assume_tac)
  >> Cases_on `l2`
  >> rfs[EL]
  >> rw[]
  >> first_assum (qspec_then `SUC n` assume_tac)
  >> rfs[prim_recTheory.LESS_SUC]
QED

Theorem is_subtype_leaf_TYPE_SUBST:
  !t s p. is_subtype_leaf (TYPE_SUBST s t) p
  ==> ?q r. p = q ++ r /\ is_subtype_leaf t q
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  >- (
    rpt strip_tac
    >> qexists_tac `[]`
    >> fs[EXISTS_OR_THM,is_subtype_leaf_eq,subtype_at_def]
  )
  >> rpt strip_tac
  >> fs[EVERY_MEM]
  >> Cases_on `p`
  >- fs[is_subtype_leaf_eq,subtype_at_def]
  >> Cases_on `h`
  >> Cases_on `q = m /\ r < LENGTH l`
  >- (
    qspecl_then [`m`,`MAP (λx. TYPE_SUBST s x) l`,`t`,`r`] assume_tac is_subtype_leaf_EL
    >> rfs[LENGTH_MAP]
    >> imp_res_tac MEM_EL
    >> fs[PULL_FORALL]
    >> first_x_assum (qspecl_then [`EL r l`,`s`,`t`] assume_tac)
    >> rfs[TYPE_SUBST_EL]
    >> qexists_tac `(m,r)::q'`
    >> fs[EXISTS_OR_THM,is_subtype_leaf_EL]
  )
  >> fs[is_subtype_leaf_eq,subtype_at_def]
  >> fs[]
QED


Theorem is_instance_eq:
  !t ti s. ALL_DISTINCT (MAP SND s) /\ EVERY (UNCURRY $<>) s
  ==> (ti = TYPE_SUBST s t) =
  ((!p. is_subtype_leaf t p
  ==> (
    (subtype_at t p <> subtype_at ti p)
    = (
      ?a. subtype_at t p = SOME (Tyvar a)
      /\ TYPE_SUBST s (Tyvar a) = THE (subtype_at ti p)
      /\ MEM (THE (subtype_at ti p),Tyvar a) s
    )
    /\ !a. subtype_at t p = SOME (Tyvar a) ==> (
      (subtype_at ti p = subtype_at t p) = ~MEM (Tyvar a) (MAP SND s)
    )
  ))
  /\ !p m l. subtype_at t p = SOME (Tyapp m l)
    ==> ?l'. subtype_at ti p = SOME (Tyapp m l') /\ LENGTH l' = LENGTH l
  )
Proof
  ho_match_mp_tac type_ind
  >> strip_tac
  (* 2 subgoals *)
  >- (
    rw[EQ_IMP_THM]
    (* 6 subgoals *)
    >- (
      fs[is_subtype_leaf_Tyvar,NULL_EQ,subtype_at_def]
      >> rveq
      >> fs[subtype_at_def]
      >> Cases_on `MEM (Tyvar m) (MAP SND s)`
      >- (
        fs[MEM_MAP]
        >> Cases_on `y`
        >> fs[]
        >> rveq
        >> imp_res_tac TYPE_SUBST_MEM'
        >> fs[]
      )
      >> imp_res_tac TYPE_SUBST_drop_prefix
      >> pop_assum (qspec_then `[]` assume_tac)
      >> fs[]
    )
    >- (
      fs[is_subtype_leaf_Tyvar,NULL_EQ,subtype_at_def,EVERY_MEM]
      >> rveq
      >> NTAC 5 (last_x_assum (assume_tac o REWRITE_RULE[subtype_at_def,option_CLAUSES]))
      >> qpat_x_assum `REV_ASSOCD _ _ _ = _` kall_tac
      >> rw[]
      >> qpat_x_assum `!e. _` imp_res_tac
      >> fs[ELIM_UNCURRY]
    )
    >- (
      CCONTR_TAC
      >> fs[MEM_MAP,is_subtype_leaf_Tyvar,NULL_EQ]
      >> qpat_assum `EVERY _ _` (imp_res_tac o REWRITE_RULE[EVERY_MEM])
      >> Cases_on `y`
      >> rveq
      >> fs[ELIM_UNCURRY,subtype_at_def]
      >> rw[]
      >> imp_res_tac TYPE_SUBST_MEM'
      >> fs[]
    )
    >- (
      fs[is_subtype_leaf_Tyvar,NULL_EQ]
      >> rveq
      >> fs[subtype_at_def]
      >> rveq
      >> imp_res_tac TYPE_SUBST_drop_prefix
      >> pop_assum (qspec_then `[]` assume_tac)
      >> fs[]
    )
    >- (
      imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_Tyvar)
      >> fs[NULL_EQ,subtype_at_def]
    )
    >- (
      qpat_x_assum `!p. is_subtype_leaf _ _ ==> _` (qspec_then `[]` assume_tac)
      >> fs[is_subtype_leaf_Tyvar,NULL_EQ,subtype_at_def]
      >> Cases_on `Tyvar m <> ti`
      >> fs[]
      >- (
        rveq
        >> imp_res_tac TYPE_SUBST_drop_prefix
        >> pop_assum (qspec_then `[]` assume_tac)
        >> fs[]
      )
      >> rveq
      >> imp_res_tac TYPE_SUBST_drop_prefix
      >> pop_assum (qspec_then `[]` assume_tac)
      >> fs[]
    )
  )
  >> rw[]
  >> Cases_on `NULL l`
  >> rw[Once EQ_IMP_THM]
  >> imp_res_tac is_subtype_leaf_Tyapp
  >> fs[NULL_EQ,subtype_at_def]
  >> rveq
  (* 6 subgoals *)
  >- (
    asm_exists_tac >> fs[]
  )
  >- (
    first_x_assum (qspecl_then [`[]`] assume_tac)
    >> fs[subtype_at_def]
  (*  qpat_x_assum `!p. is_subtype_leaf _ _ ==> _` (qspec_then `[]` assume_tac)
    >> fs[is_subtype_leaf_eq,subtype_at_def] *)
  )
  >- (
    Cases_on `p`
    >> fs[]
    >> Cases_on `h`
    >> Cases_on `m = q /\ r < LENGTH l`
    >> fs[]
    >> qpat_x_assum `EVERY _ l` ((qspec_then `EL r l` assume_tac) o REWRITE_RULE[EVERY_MEM])
    >> fs[subtype_at_def,EL_MAP,EVERY_MEM]
    >> `MEM (EL r l) l` by (rw[MEM_EL] >> asm_exists_tac >> fs[])
    >> fs[]
    >> first_x_assum (qspecl_then [`TYPE_SUBST s (EL r l)`,`s`] assume_tac)
    >> rfs[]
    >> imp_res_tac is_subtype_leaf_EL
    >> first_x_assum (qspec_then `t` assume_tac)
    >> rw[EQ_IMP_THM]
  )
  >- (
    Cases_on `p`
    >> fs[]
    >> Cases_on `h`
    >> Cases_on `m = q /\ r < LENGTH l`
    >> fs[subtype_at_def,EL_MAP]
    >> rfs[]
    >> imp_res_tac subtype_at_TYPE_SUBST
    >> pop_assum (qspec_then `s` assume_tac)
    >> rw[EQ_IMP_THM]
    >- (
      CCONTR_TAC
      >> fs[MEM_MAP,EVERY_MEM]
      >> qpat_x_assum `!e. _` imp_res_tac
      >> Cases_on `y`
      >> fs[ELIM_UNCURRY]
      >> rveq
      >> imp_res_tac TYPE_SUBST_MEM'
      >> fs[]
    )
    >> imp_res_tac TYPE_SUBST_drop_prefix
    >> pop_assum (qspec_then `[]` assume_tac)
    >> fs[]
  )
  >- (
    imp_res_tac subtype_at_TYPE_SUBST
    >> first_x_assum (qspec_then `s` assume_tac)
    >> fs[]
  )
  >- (
    first_assum (qspecl_then [`[]`,`m`,`l`] assume_tac)
    >> fs[subtype_at_def]
    >> rw[EQ_LIST_EL]
    >> fs[EVERY_MEM,PULL_FORALL]
    >> last_x_assum (qspecl_then [`EL n l`,`EL n l'`,`s`] assume_tac)
    >> imp_res_tac MEM_EL
    >> imp_res_tac (GSYM TYPE_SUBST_EL)
    >> fs[GSYM PULL_FORALL]
    >> rfs[]
    >> rw[]
    (* 3 subgoals *)
    >> (
      qpat_x_assum `!p. is_subtype_leaf _ _ ==> _` (qspec_then `(m,n)::p` assume_tac)
      >> fs[is_subtype_leaf_def',subtype_at_def]
      >> rfs[]
    )
    >> qpat_x_assum `!p m l. _ ==> _` (qspec_then `(m,n)::p'` assume_tac)
    >> fs[subtype_at_def]
    >> rfs[]
  )
QED

Theorem NOT_MEM_MAP_SND:
  !s y. ALL_DISTINCT (MAP SND s) ==> (!x. ~MEM (x,y) s) = ~MEM y (MAP SND s)
Proof
  rw[EQ_IMP_THM]
  >- (
    CCONTR_TAC
    >> fs[MEM_MAP]
    >> first_x_assum (qspec_then `FST y'` assume_tac)
    >> rveq
    >> fs[PAIR]
  )
  >> fs[MEM_MAP]
  >> first_x_assum (qspec_then `(x,y)` assume_tac)
  >> fs[]
QED

Theorem FUN_EXISTS_REFL[local]:
  !A x. ?a. A x = A a
Proof
  rpt strip_tac >> qexists_tac `x` >> fs[]
QED

Theorem instance_subst_complete_step1[local]:
  ∀a b l sigma e.
       (¬MEM (Tyvar a,Tyvar b) sigma ∧ ¬MEM (Tyvar b) (MAP SND sigma) ∧
        a ≠ b ∧ ¬MEM b e ⇒
        ∀t ti.
            (∃s. ti = TYPE_SUBST ((Tyvar a,Tyvar b)::sigma ++ s) t) ∧
            instance_subst_inv [(ti,t)] l ((Tyvar a,Tyvar b)::sigma) e ⇒
            IS_SOME (instance_subst l ((Tyvar a,Tyvar b)::sigma) e)) ∧
       (¬MEM (Tyvar a,Tyvar b) sigma ∧ ¬MEM (Tyvar b) (MAP SND sigma) ∧ a = b ⇒
        ∀t ti.
            (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
            instance_subst_inv [(ti,t)] l sigma (a::e) ⇒
            IS_SOME (instance_subst l sigma (a::e))) ∧
       (MEM (Tyvar a,Tyvar b) sigma ⇒
        ∀t ti.
            (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
            instance_subst_inv [(ti,t)] l sigma e ⇒
            IS_SOME (instance_subst l sigma e)) ⇒
       ∀t ti.
           (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
           instance_subst_inv [(ti,t)] ((Tyvar a,Tyvar b)::l) sigma e ⇒
           IS_SOME (instance_subst ((Tyvar a,Tyvar b)::l) sigma e)
Proof
  rw[instance_subst_def]
  (* 5 subgoals *)
  >- (
    first_x_assum ho_match_mp_tac
    >> qexists_tac `t`
    >> qexists_tac `TYPE_SUBST (sigma++s) t`
    >> fs[instance_subst_inv_def]
    >> strip_tac
    >- (
      qexists_tac `s` >> fs[]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. IS_SOME _ /\ IS_SOME _ ==> _` (qspec_then `p` assume_tac)
      >> rfs[]
      (* 10 subgoals *)
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM,IS_SOME_THE,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
        >> qexists_tac `b`
        >> fs[IS_SOME_THE]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM,IS_SOME_THE,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
        >> qexists_tac `b`
        >> fs[IS_SOME_THE]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> qexists_tac `r`
        >> qexists_tac `a'`
        >> fs[IS_SOME_THE]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> qexists_tac `r`
        >> qexists_tac `a'`
        >> fs[IS_SOME_THE]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `is_instance _ _ ==> _` (imp_res_tac o REWRITE_RULE[TYPE_SUBST_compose])
      >> asm_exists_tac
      >> fs[]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` imp_res_tac
      (* 4 subgoals *)
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_THE]
        >> rveq
        >> qspecl_then [`t`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
      >> (
        DISJ2_TAC >> fs[]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` imp_res_tac
      (* 3 subgoals *)
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_THE]
        >> rveq
        >> qspecl_then [`t`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> fs[EXISTS_OR_THM]
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        fs[]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME _ /\ subtype_at _ _ = SOME _ ==> _`
        (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >> fs[]
      (* 4 subgoals *)
      >- (
        imp_res_tac IS_SOME_THE
        >> fs[]
        >> qspecl_then [`t`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
        >> qpat_x_assum `EVERY _ _` (imp_res_tac o (REWRITE_RULE[EVERY_MEM]))
        >> fs[ELIM_UNCURRY]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        fs[IS_SOME_EXISTS]
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_THE]
        >> rveq
        >> qspecl_then [`t`,`p`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
        >> qpat_x_assum `EVERY _ _` (imp_res_tac o (REWRITE_RULE[EVERY_MEM]))
        >> fs[ELIM_UNCURRY]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. (_ <> _) /\ is_subtype_leaf _ _ ==> _` (qspec_then `p` assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        rveq
        >> imp_res_tac subtype_at_IS_SOME_parent
        >> imp_res_tac IS_SOME_THE
        >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`r`] assume_tac is_subtype_leafs_imp
        >> rfs[]
        >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
        >> fs[EXISTS_OR_THM]
        >> pop_assum imp_res_tac
        >> imp_res_tac TYPE_SUBST_MEM'
        >> qspecl_then [`t`,`q`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >- (
        qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a b. _ /\ _ /\ (_ <> _) /\ _ ==> _` (qspecl_then [`p`,`a'`,`b'`] assume_tac)
      >> rfs[]
      (* 2 subgoals *)
      >- (
        imp_res_tac IS_SOME_THE
        >> rveq
        >> qspecl_then [`t`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
        >> rveq
        >> imp_res_tac (Q.ISPEC `SND` MEM_MAP_f)
        >> fs[]
      )
      >- (
        qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
  )
  (* 4 subgoals remaining *)
  >- (
    (* different assignment for a variable *)
    CCONTR_TAC
    >> fs[instance_subst_inv_def]
    >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
    >> imp_res_tac TYPE_SUBST_drop_suffix
    >> fs[MEM_MAP]
    >> Cases_on `y`
    >> fs[ELIM_UNCURRY]
    >> rveq
    >> imp_res_tac TYPE_SUBST_MEM'
    >> rveq
    >> fs[]
  )
  >- (
    first_x_assum ho_match_mp_tac
    >> qexists_tac `t`
    >> qexists_tac `TYPE_SUBST (sigma++s) t`
    >> fs[instance_subst_inv_def]
    >> strip_tac
    >- (
      qexists_tac `s` >> fs[]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. IS_SOME _ /\ IS_SOME _ ==> _` (qspec_then `p` assume_tac)
      >> rfs[]
      >> fs[]
      (* 10 subgoals *)
      >- (
        DISJ2_TAC >> DISJ2_TAC >> qexists_tac `q` >> imp_res_tac IS_SOME_THE >> fs[option_CLAUSES,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> imp_res_tac IS_SOME_THE
        >> fs[option_CLAUSES,EXISTS_OR_THM,RIGHT_EXISTS_AND_THM,LEFT_EXISTS_AND_THM]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> fs[option_CLAUSES,EXISTS_OR_THM,RIGHT_EXISTS_AND_THM,LEFT_EXISTS_AND_THM]
      )
    )
    >> strip_tac
    >- (
      fs[TYPE_SUBST_compose]
      >> strip_tac
      >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
      >> asm_exists_tac
      >> fs[]
    )
    >> strip_tac
    >- (
      rw[] >> fs[]
    )
    >> strip_tac
    >- (
      rw[]
      >- (
        qpat_x_assum `!a b. _ /\ _ \/ _==>_` (qspecl_then [`Tyvar a`,`Tyvar a`] assume_tac)
        >> fs[]
        >> asm_exists_tac
        >> fs[]
      )
      >- (
        qpat_x_assum `!a. MEM _ e ==> ?p. _` imp_res_tac
        >> asm_exists_tac
        >> fs[]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[IS_SOME_EXISTS,option_CLAUSES,NULL_EQ]
        >> rveq
        >> fs[]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> qspecl_then [`t`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> fs[option_CLAUSES,EXISTS_OR_THM]
        >> rveq
        >> pop_assum imp_res_tac
        >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[]
      )
      >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME _ /\ subtype_at _ _ = SOME _ ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`p`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. (_ <> _) /\ _ ==> _` (qspecl_then [`p`] assume_tac)
      >> rfs[]
      >- (
        qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`r`] assume_tac is_subtype_leafs_imp
        >> rveq
        >> pop_assum imp_res_tac
        >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
        >> fs[EXISTS_OR_THM,IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> pop_assum imp_res_tac
        >> imp_res_tac TYPE_SUBST_drop_prefix
        >> qexists_tac `q`
        >> pop_assum (qspec_then `[]` assume_tac)
        >> qspecl_then [`t`,`q`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM]
    )
    >- (
      rw[]
      >> qpat_x_assum `!p a b. _ /\ _ /\ _ ==> _` (qspecl_then [`p`,`a'`,`b`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rveq
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
  )
  (* 2 subgoals remaining *)
  >-(
    first_x_assum ho_match_mp_tac
    >> qexists_tac `t`
    >> qexists_tac `TYPE_SUBST (sigma++s) t`
    >> fs[instance_subst_inv_def]
    >> strip_tac
    >- (
      qpat_x_assum `!a b. _ /\ _\/ _ ==> _` (qspecl_then [`Tyvar a`,`Tyvar b`] assume_tac)
      >> qmatch_asmsub_abbrev_tac `subtype_at (TYPE_SUBST comp _) _ = SOME _`
      >> fs[]
      >> qspecl_then [`t`,`p`,`comp`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (assume_tac o GSYM)
      >> rfs[]
      >> qexists_tac `s`
      >> imp_res_tac TYPE_SUBST_drop_prefix
      >> pop_assum (qspec_then `s` assume_tac)
      >> rw[TYPE_SUBST_tyvars]
      >> REWRITE_TAC[GSYM TYPE_SUBST_def]
      >> Cases_on `x = b`
      >> fs[REV_ASSOCD_def]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. IS_SOME _ /\ IS_SOME _ ==> _` (qspec_then `p` assume_tac)
      >> rfs[]
      >> fs[]
      (* 10 subgoals *)
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> imp_res_tac IS_SOME_THE
        >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> imp_res_tac IS_SOME_THE
        >> fs[option_CLAUSES,EXISTS_OR_THM,RIGHT_EXISTS_AND_THM,LEFT_EXISTS_AND_THM]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> fs[option_CLAUSES,EXISTS_OR_THM,RIGHT_EXISTS_AND_THM,LEFT_EXISTS_AND_THM]
      )
    )
    >> strip_tac
    >- (
      fs[]
      >> strip_tac
      >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
      >> qpat_x_assum `!a b. _ /\ _\/ _ ==> _` (qspecl_then [`Tyvar a`,`Tyvar b`] assume_tac)
      >> qmatch_asmsub_abbrev_tac `subtype_at (TYPE_SUBST comp _) _ = SOME _`
      >> fs[]
      >> qspecl_then [`t`,`p`,`comp`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (assume_tac o GSYM)
      >> rfs[]
      >> pop_assum (assume_tac o GSYM)
      >> qexists_tac `s''`
      >> fs[EVERY_MEM]
      >> rw[ELIM_UNCURRY]
      >> qpat_x_assum `!e. MEM _ _ ==> _` imp_res_tac
      >> fs[ELIM_UNCURRY]
      >> rw[TYPE_SUBST_tyvars]
      >> fs[GSYM subtype_at_tyvars]
      >> Cases_on `x=b`
      >> fs[REV_ASSOCD_def]
    )
    >> strip_tac
    >- (
      rw[] >> fs[]
    )
    >> strip_tac
    >- (
      rw[] >> fs[]
    )
    >> strip_tac
    >- (rw[] >> rw[])
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[IS_SOME_EXISTS,option_CLAUSES,NULL_EQ]
        >> rveq
        >> fs[]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> qspecl_then [`t`,`q`,`r`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_imp)
        >> fs[option_CLAUSES,EXISTS_OR_THM]
        >> rveq
        >> pop_assum imp_res_tac
        >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[]
      )
      >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME _ /\ subtype_at _ _ = SOME _ ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`p`,`r`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyvar a`,`Tyvar b`] assume_tac)
      >> fs[]
      >> qspecl_then [`t`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma ++ s` (assume_tac o GSYM))
      >> rfs[]
      >> rpt (qpat_x_assum `subtype_at _ p = _` kall_tac)
      >> rw[]
      >> imp_res_tac is_subtype_leaf_TYPE_SUBST_parent
      >> qpat_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
      >> rveq
      >> fs[]
      (* >> qpat_x_assum `is_subtype_leaf _ _` (assume_tac o REWRITE_RULE[is_subtype_leaf_def'])
       *)
      >- (
      (* Tyvar a' *)
        `a' <> b` by (
          CCONTR_TAC
          >> imp_res_tac subtype_at_TYPE_SUBST
          >> first_assum (qspec_then `(Tyvar a,Tyvar b)::sigma` assume_tac)
          >> first_x_assum (qspec_then `sigma++s` assume_tac)
          >> imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
          >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`r`] assume_tac subtype_at_decomp_path
          >> pop_assum imp_res_tac
          >> qspecl_then [`TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) t`,`q`,`r`] assume_tac subtype_at_decomp_path
          >> pop_assum imp_res_tac
          >> rveq
          >> fs[]
          >> rfs[REV_ASSOCD_def]
        )
        >> `~MEM (Tyvar a') (MAP SND sigma)` by (
          CCONTR_TAC
          >> fs[]
          >> imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
          >> imp_res_tac TYPE_SUBST_drop_suffix
          >> imp_res_tac subtype_at_TYPE_SUBST
          >> first_assum (qspec_then `(Tyvar a,Tyvar b)::sigma` assume_tac)
          >> first_x_assum (qspec_then `sigma++s` assume_tac)
          >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`r`] assume_tac subtype_at_decomp_path
          >> pop_assum imp_res_tac
          >> qspecl_then [`TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) t`,`q`,`r`] assume_tac subtype_at_decomp_path
          >> pop_assum imp_res_tac
          >> fs[]
          >> fs[REV_ASSOCD_def]
        )
        >> imp_res_tac is_subtype_leaf_IS_SOME_subtype
        >> imp_res_tac subtype_at_IS_SOME_parent
        >> Cases_on `subtype_at (TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) t) (q++r)=subtype_at (TYPE_SUBST sigma t) (q++r)`
        >> fs[]
        >- (
          qpat_x_assum `!p. _ /\ _ ==> _` (qspec_then `q++r` assume_tac)
          >> rfs[]
          >- (
            qspecl_then [`t`,`q`,`r`,`q'`,`r'`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_init)
            >> rfs[IS_PREFIX_APPEND,IS_SOME_EXISTS]
            >> rveq
            >> fs[option_CLAUSES]
            >> qspecl_then [`t`,`q'`,`l'`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
            >> rveq
            >> pop_assum imp_res_tac
            >> fs[NULL_EQ]
          )
          >> qexists_tac `q'`
          >> fs[EXISTS_OR_THM]
        )
        >> imp_res_tac subtype_at_TYPE_SUBST
        >> first_assum (qspec_then `(Tyvar a,Tyvar b)::sigma` assume_tac)
        >> first_x_assum (qspec_then `sigma` assume_tac)
        >> imp_res_tac TYPE_SUBST_drop_prefix
        >> NTAC 2 (first_x_assum (qspec_then `[]` assume_tac))
        >> fs[REV_ASSOCD_def]
        >> FULL_CASE_TAC
        >> fs[]
        >> qspecl_then [`TYPE_SUBST sigma t`,`q`,`r`] assume_tac subtype_at_decomp_path
        >> pop_assum imp_res_tac
        >> qspecl_then [`TYPE_SUBST ((Tyvar a,Tyvar b)::sigma) t`,`q`,`r`] assume_tac subtype_at_decomp_path
        >> pop_assum imp_res_tac
        >> fs[]
      )
      (* Tyapp a' [] *)
      >- (
        imp_res_tac subtype_at_TYPE_SUBST
        >> first_assum (qspec_then `(Tyvar a,Tyvar b)::sigma` assume_tac)
        >> first_x_assum (qspec_then `sigma++s` assume_tac)
        >> imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
        >> fs[TYPE_SUBST_def]
        >> rfs[]
      )
    )
    >- (
      rw[]
      >> qpat_x_assum `!p a b. _ /\ _ /\ _ ==> _` (qspecl_then [`p`,`a'`,`b'`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac IS_SOME_THE
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> rveq
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
  )
  >- (
    CCONTR_TAC
    >> fs[instance_subst_inv_def,TYPE_SUBST_compose]
    >> qmatch_asmsub_abbrev_tac `_ = TYPE_SUBST comb t`
    >> rpt (qpat_x_assum `!a. MEM _ e ==> _` imp_res_tac)
    >> qpat_x_assum `!a b. _ /\ _\/ _ ==> _` (qspecl_then [`Tyvar a`,`Tyvar b`] assume_tac)
    >> fs[]
    >> qspecl_then [`t`,`p`,`comb`] assume_tac subtype_at_TYPE_SUBST
    >> pop_assum imp_res_tac
    >> qspecl_then [`t`,`p'`,`comb`] assume_tac subtype_at_TYPE_SUBST
    >> pop_assum imp_res_tac
    >> rveq
    >> fs[]
  )
QED

Theorem instance_subst_complete_step2[local]:
   ∀m l n l' x sigma e.
       (m = n ∧ LENGTH l = LENGTH l' ⇒
        ∀t ti.
            (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
            instance_subst_inv [(ti,t)] (ZIP (l,l') ++ x) sigma e ⇒
            IS_SOME (instance_subst (ZIP (l,l') ++ x) sigma e)) ⇒
       ∀t ti.
           (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
           instance_subst_inv [(ti,t)] ((Tyapp m l,Tyapp n l')::x) sigma e ⇒
           IS_SOME (instance_subst ((Tyapp m l,Tyapp n l')::x) sigma e)
Proof
  rw[]
  >> `m = n /\ LENGTH l = LENGTH l'` by (
    pop_assum (assume_tac o REWRITE_RULE[instance_subst_inv_def])
    >> fs[]
    >> `TYPE_SUBST (sigma ++ s) t = TYPE_SUBST (sigma ++ s) t` by fs[]
    >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
    >> rveq
    >> fs[LENGTH_MAP]
  )
  >> fs[instance_subst_def]
  >> last_x_assum ho_match_mp_tac
  >> qexists_tac `t`
  >> qexists_tac `TYPE_SUBST (sigma++s) t`
  >> rw[]
  >- (
    qexists_tac `s`
    >> fs[]
  )
  >> fs[instance_subst_inv_def]
  >> strip_tac
  >- (
    rw[MEM_ZIP]
    >- (
      qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyapp m l`,`Tyapp m l'`] assume_tac)
      >> fs[]
      >> qexists_tac `p++[(m,n)]`
      >> imp_res_tac subtype_at_decomp_path
      >> NTAC 2 (first_x_assum (qspecl_then [`[(m,n)]`] assume_tac))
      >> fs[subtype_at_def]
    )
    >> qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`a`,`b`] assume_tac)
    >> fs[]
  )
  >> strip_tac
  >- (
    rw[]
    >> qpat_x_assum `!p. IS_SOME _ /\ _ ==> _` (qspecl_then [`p`] assume_tac)
    >> rfs[]
    (* 10 subgoals *)
    >- (
      rveq
      >> imp_res_tac subtype_at_IS_SOME_parent
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> Cases_on `NULL l` >> fs[NULL_EQ]
      >- (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q` >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >> Cases_on `NULL r`
      >- (
        fs[NULL_EQ]
        >> DISJ1_TAC >> qexists_tac `q++[(m,0)]`
        >> imp_res_tac subtype_at_decomp_path
        >> NTAC 2 (first_x_assum (qspec_then `[(m,0)]` assume_tac))
        >> fs[subtype_at_def,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
        >> FULL_CASE_TAC
        >> rfs[] >> fs[MEM_ZIP]
        >> DISJ1_TAC >> asm_exists_tac
        >> fs[]
      )
      >> Cases_on `r` >> fs[] >> Cases_on `h`
      >> DISJ1_TAC
      >> qexists_tac `q++[(q',r)]`
      >> qspecl_then [`t`,`q`,`[(q',r)]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`[(q',r)]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> fs[subtype_at_def,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      >> qspecl_then [`t`,`q++[(q',r)]`,`t'`] assume_tac subtype_at_IS_SOME_parent
      >> pop_assum (assume_tac o REWRITE_RULE[Once (GSYM APPEND_ASSOC),GSYM CONS_APPEND])
      >> rfs[option_CLAUSES]
      >> FULL_CASE_TAC
      >> fs[]
      >> DISJ1_TAC
      >> fs[MEM_ZIP,EL_ZIP]
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >- (
      Cases_on `NULL l` >> fs[NULL_EQ]
      >- (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> rveq
        >> imp_res_tac subtype_at_IS_SOME_parent
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
        >> rfs[]
      )
      >> rveq
      >> imp_res_tac subtype_at_IS_SOME_parent
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> fs[]
      >> DISJ1_TAC
      >> qspecl_then [`t`,`p++r`,`[(m,0)]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`p++r`,`[(m,0)]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qexists_tac `p++r++[(m,0)]`
      >> fs[subtype_at_def,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      >> FULL_CASE_TAC
      >> fs[]
      >> rfs[MEM_ZIP]
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
    )
    >- (
      DISJ2_TAC >> DISJ1_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
    )
    >> (
      DISJ2_TAC >> DISJ2_TAC
      >> qexists_tac `q`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
    )
  )
  >> strip_tac
  >- (
    rw[]
    >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
    >> qexists_tac `s''`
    >> fs[ZIP_MAP,EVERY_MAP]
  )
  >> strip_tac
  >- (
    rw[]
    >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`p`,`a`] assume_tac)
    >> rfs[]
    >- (
      rveq
      >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> Cases_on `NULL r` >- fs[NULL_EQ]
      >> Cases_on `NULL l'`
      >- (
        fs[NULL_EQ]
        >> imp_res_tac subtype_at_leaf_imp
        >> fs[NULL_EQ]
      )
      >> DISJ1_TAC
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM,IS_SOME_EXISTS]
      >> imp_res_tac CONS
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`t`,`q++[HD r]`,`TL r`] assume_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,Once (GSYM CONS_APPEND)])
      >> rfs[]
      >> Cases_on `HD r`
      >> fs[subtype_at_def,MEM_ZIP]
      >> rveq
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
  >> strip_tac
  >- (
    rw[]
    >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`p`,`a`] assume_tac)
    >> rfs[]
    >- (
      imp_res_tac subtype_at_TYPE_SUBST
      >> first_x_assum (qspec_then `sigma++s` assume_tac)
      >> rveq
      >> fs[]
    )
    >- (
      DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
  >> strip_tac
  >- (
    rw[]
    >> qpat_x_assum `!p a. subtype_at (TYPE_SUBST _ _) _ = SOME _ /\ _ ==> _` (qspecl_then [`p`,`a`] assume_tac)
    >> rfs[]
    >- (
      Cases_on `NULL l`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> imp_res_tac (CONJUNCT2 subtype_at_leaf_imp)
        >> fs[NULL_EQ]
      )
      >> Cases_on `NULL r`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
      )
      >> imp_res_tac CONS
      >> DISJ2_TAC
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM,IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> qspecl_then [`t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`t`,`q++[HD r]`,`TL r`] assume_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,Once (GSYM CONS_APPEND)])
      >> rfs[]
      >> Cases_on `HD r`
      >> fs[subtype_at_def,MEM_ZIP]
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
    >- (
      qspecl_then [`t`,`p`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
      >> fs[IS_SOME_EXISTS]
      >> rveq
      >> pop_assum imp_res_tac
      >> fs[option_CLAUSES,NULL_EQ]
    )
    >- (
      DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
  >> strip_tac
  >- (
    rw[]
    >> qpat_x_assum `!p. (_ <> _) /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`p`] assume_tac)
    >> rfs[]
    >- (
      Cases_on `NULL l`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
        >> qspecl_then [`t`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[]
      )
      >> Cases_on `NULL r`
      >- (
        fs[NULL_EQ,IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> fs[is_subtype_leaf_eq]
        >> fs[NULL_EQ]
      )
      >> imp_res_tac CONS
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM,IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> qspecl_then [`t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] is_subtype_leaf_IS_SOME_subtype)
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q++[HD r]`,`TL r`] assume_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,Once (GSYM CONS_APPEND)])
      >> rfs[]
      >> Cases_on `HD r`
      >> fs[subtype_at_def,MEM_ZIP]
      >> DISJ1_TAC
      >> qexists_tac `r'`
      >> fs[]
    )
    >- (
      qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
  >- (
    rw[]
    >> qpat_x_assum `!p a b. _ /\ _ /\ (_ <> _) /\ _ ==> _` (qspecl_then [`p`,`a`,`b`] assume_tac)
    >> rfs[]
    >- (
      fs[IS_SOME_EXISTS]
      >> fs[option_CLAUSES]
      >> rveq
      >> Cases_on `NULL l`
      >- (
        fs[NULL_EQ]
        >> rveq
        >> imp_res_tac (CONJUNCT2 subtype_at_leaf_imp)
        >> fs[NULL_EQ]
      )
      >> Cases_on `NULL r`
      >- fs[NULL_EQ]
      >> imp_res_tac CONS
      >> qexists_tac `q++[HD r]`
      >> qexists_tac `TL r`
      >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM,IS_SOME_EXISTS]
      >> qspecl_then [`t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`TYPE_SUBST (sigma++s) t`,`q`,`[HD r]`] assume_tac subtype_at_decomp_path
      >> pop_assum imp_res_tac
      >> qspecl_then [`t`,`q++[HD r]`,`TL r`] assume_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
      >> pop_assum (assume_tac o REWRITE_RULE[GSYM APPEND_ASSOC,Once (GSYM CONS_APPEND)])
      >> rfs[]
      >> Cases_on `HD r`
      >> fs[subtype_at_def,MEM_ZIP]
      >> DISJ1_TAC
      >> asm_exists_tac
      >> fs[]
    )
    >- (
      qexists_tac `q` >> fs[EXISTS_OR_THM]
    )
  )
QED

Theorem instance_subst_complete_step3[local]:
  ∀m l a l' sigma e.
       (¬MEM (Tyapp m l,Tyvar a) sigma ∧ ¬MEM (Tyvar a) (MAP SND sigma) ∧
        ¬MEM a e ⇒
        ∀t ti.
            (∃s. ti = TYPE_SUBST ((Tyapp m l,Tyvar a)::sigma ++ s) t) ∧
            instance_subst_inv [(ti,t)] l' ((Tyapp m l,Tyvar a)::sigma) e ⇒
            IS_SOME (instance_subst l' ((Tyapp m l,Tyvar a)::sigma) e)) ∧
       (MEM (Tyapp m l,Tyvar a) sigma ⇒
        ∀t ti.
            (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
            instance_subst_inv [(ti,t)] l' sigma e ⇒
            IS_SOME (instance_subst l' sigma e)) ⇒
       ∀t ti.
           (∃s. ti = TYPE_SUBST (sigma ++ s) t) ∧
           instance_subst_inv [(ti,t)] ((Tyapp m l,Tyvar a)::l') sigma e ⇒
           IS_SOME (instance_subst ((Tyapp m l,Tyvar a)::l') sigma e)
Proof
  rw[instance_subst_def]
  (* 3 subgoals *)
  >- (
    first_x_assum ho_match_mp_tac
    >> qexists_tac `t`
    >> qexists_tac `TYPE_SUBST (sigma++s) t`
    >> strip_tac
    >- (
      qexists_tac `s`
      >> fs[]
    )
    >> fs[instance_subst_inv_def]
    >> imp_res_tac TYPE_SUBST_MEM'
    >> imp_res_tac (Q.ISPEC `SND:type#type->type` MEM_MAP_f)
    >> fs[]
    >> imp_res_tac TYPE_SUBST_drop_suffix
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. IS_SOME _ /\ _ ==> _` (qspecl_then [`p`] assume_tac)
      >> rfs[]
      (* 10 subgoals *)
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> rveq
        >> fs[IS_SOME_EXISTS,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
        >> fs[option_CLAUSES]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> rveq
        >> fs[IS_SOME_EXISTS,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
        >> fs[option_CLAUSES]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC
        >> qexists_tac `q`
        >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
      >> asm_exists_tac
      >> fs[]
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        imp_res_tac subtype_at_TYPE_SUBST
        >> first_x_assum (qspec_then `sigma++s` assume_tac)
        >> rveq
        >> fs[]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at (TYPE_SUBST _ _) _ = SOME _ /\ _ ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        qspecl_then [`t`,`p`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> fs[IS_SOME_EXISTS]
        >> rveq
        >> pop_assum imp_res_tac
        >> fs[option_CLAUSES,NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p. (_ <> _) /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`p`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> rfs[]
      )
      >- (
        qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a b. _ /\ _ /\ (_ <> _) /\ _ ==> _` (qspecl_then [`p`,`a'`,`b`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
  )
  >- (
    first_x_assum ho_match_mp_tac
    >> qexists_tac `t`
    >> qexists_tac `TYPE_SUBST (sigma++s) t`
    >> strip_tac
    >- (
      qexists_tac `s`
      >> fs[instance_subst_inv_def]
      >> qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyapp m l`,`Tyvar a`] assume_tac)
      >> fs[]
      >> qspecl_then[`t`,`p`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma++s` (assume_tac o GSYM))
      >> rfs[]
      >> rw[TYPE_SUBST_tyvars]
      >> Cases_on `x = a`
      >> fs[REV_ASSOCD_def]
    )
    >> fs[instance_subst_inv_def]
    >> strip_tac
    >- (
    (*
      qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyapp m l`,`Tyvar a`] assume_tac)
      >> fs[]
      >> qspecl_then[`t`,`p`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma++s` (assume_tac o GSYM))
      >> rfs[]
      >> rpt (qpat_x_assum `subtype_at _ _ = SOME _` kall_tac)
    *)
      rw[]
      >> qpat_x_assum `!p. IS_SOME _ /\ _ ==> _` (qspecl_then [`p`] assume_tac)
      >> rfs[]
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC
        >> qexists_tac `q`
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES,EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        DISJ2_TAC >> DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >> (
        DISJ2_TAC >> DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM,LEFT_EXISTS_AND_THM,RIGHT_EXISTS_AND_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `is_instance _ _ ==> _` imp_res_tac
      >> qexists_tac `s''`
      >> fs[EVERY_MEM,ELIM_UNCURRY]
      >> rw[TYPE_SUBST_tyvars]
      >> qpat_x_assum `!e. MEM _ _ ==> _` imp_res_tac
      >> fs[GSYM subtype_at_tyvars]
      >> Cases_on `x=a`
      >> fs[REV_ASSOCD_def]
    )
    >> strip_tac
    >- (rw[] >> fs[])
    >> strip_tac
    >- (rw[] >> fs[])
    >> strip_tac
    >- (rw[] >> fs[])
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyvar _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q`
        >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at _ _ = SOME (Tyapp _ _) ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ1_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      rw[]
      >> qpat_x_assum `!p a. subtype_at (TYPE_SUBST _ _) _ = SOME _ /\ _ ==> _` (qspecl_then [`p`,`a'`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> imp_res_tac (REWRITE_RULE[IS_SOME_EXISTS] subtype_at_IS_SOME_parent)
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
      >- (
        rveq
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`p`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        DISJ2_TAC >> qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
    >> strip_tac
    >- (
      qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyapp m l`,`Tyvar a`] assume_tac)
      >> fs[]
      >> qspecl_then[`t`,`p`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma++s` (assume_tac o GSYM))
      >> rfs[]
      >> rpt (qpat_x_assum `subtype_at _ _ = SOME _` kall_tac)
      >> rw[]
      >> imp_res_tac is_subtype_leaf_TYPE_SUBST_parent
      >> pop_assum (assume_tac o REWRITE_RULE[is_subtype_leaf_eq])
      >> fs[]
      (* Tyvar a' *)
      >- (
        Cases_on `a' = a`
        >- (
          imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
          >> qspecl_then [`t`,`q`,`sigma++s`] assume_tac subtype_at_TYPE_SUBST
          >> pop_assum imp_res_tac
          >> qspecl_then [`t`,`q`,`(Tyapp m l,Tyvar a)::sigma`] assume_tac subtype_at_TYPE_SUBST
          >> pop_assum imp_res_tac
          >> rveq
          >> fs[REV_ASSOCD_def]
        )
        >> qspecl_then [`t`,`q`,`sigma++s`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> qspecl_then [`t`,`q`,`(Tyapp m l,Tyvar a)::sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> qspecl_then [`t`,`q`,`sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> qspec_then `q` assume_tac ((CONV_RULE SWAP_FORALL_CONV) subtype_at_decomp_path)
        >> pop_assum imp_res_tac
        >> rpt (qpat_x_assum `!q. subtype_at _ _ = _` (qspec_then `r` assume_tac))
        >> qpat_x_assum `!p. (_ <> _) /\ is_subtype_leaf _ _ ==> _` (qspecl_then [`q++r`] assume_tac)
        >> rfs[]
        >> rfs[REV_ASSOCD_def]
        >> fs[]
        >> rfs[]
        >- (
          qspecl_then [`t`,`q`,`r`,`q'`,`r'`] assume_tac (REWRITE_RULE[is_subtype_leaf_eq] is_subtype_leafs_init)
          >> rfs[IS_PREFIX_APPEND,IS_SOME_EXISTS]
          >> fs[option_CLAUSES]
          >> rveq
          >> qspecl_then [`t`,`q'`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
          >> pop_assum imp_res_tac
          >> fs[NULL_EQ]
        )
        >> qexists_tac `q'`
        >> fs[EXISTS_OR_THM]
      )
      (* Tyapp _ [] *)
      >- (
        imp_res_tac (GEN_ALL (CONTRAPOS (SPEC_ALL subtype_at_eqs_imp)))
        >> qspecl_then [`t`,`q`,`sigma++s`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> qspecl_then [`t`,`q`,`(Tyapp m l,Tyvar a)::sigma`] assume_tac subtype_at_TYPE_SUBST
        >> pop_assum imp_res_tac
        >> fs[TYPE_SUBST_def]
      )
    )
    >- (
      rw[]
      >> qpat_x_assum `!p a b. _ /\ _ /\ (_ <> _) /\ _ ==> _` (qspecl_then [`p`,`a'`,`b`] assume_tac)
      >> rfs[]
      >- (
        rveq
        >> fs[IS_SOME_EXISTS]
        >> fs[option_CLAUSES]
        >> rveq
        >> qspecl_then [`t`,`q`] assume_tac (CONJUNCT1 subtype_at_leaf_imp)
        >> pop_assum imp_res_tac
        >> fs[NULL_EQ]
      )
      >- (
        qexists_tac `q` >> fs[EXISTS_OR_THM]
      )
    )
  )
  >- (
    CCONTR_TAC
    >> fs[instance_subst_inv_def]
    >- (
      qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyapp m l`,`Tyvar a`] assume_tac)
      >> fs[]
      >> qspecl_then[`t`,`p`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma++s` (assume_tac o GSYM))
      >> rfs[]
      >> rpt (qpat_x_assum `subtype_at _ _ = SOME _` kall_tac)
      >> imp_res_tac TYPE_SUBST_drop_suffix
      >> pop_assum (qspec_then `s` assume_tac)
      >> fs[MEM_MAP]
      >> Cases_on `y`
      >> fs[ELIM_UNCURRY]
      >> rveq
      >> imp_res_tac TYPE_SUBST_MEM'
      >> fs[]
    )
    >- (
      qpat_x_assum `!a b. _ /\ _ \/ _ ==> _` (qspecl_then [`Tyapp m l`,`Tyvar a`] assume_tac)
      >> fs[]
      >> qspecl_then[`t`,`p`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma++s` (assume_tac o GSYM))
      >> rfs[]
      >> rpt (qpat_x_assum `subtype_at _ _ = SOME _` kall_tac)
      >> qpat_x_assum `!a. MEM _ e ==> ?x. _` imp_res_tac
      >> qspecl_then[`t`,`p`] assume_tac subtype_at_TYPE_SUBST
      >> pop_assum imp_res_tac
      >> pop_assum (qspec_then `sigma++s` assume_tac)
      >> fs[]
    )
  )
QED

Theorem instance_subst_complete_step:
  !l sigma e t ti. (?s. ti = (TYPE_SUBST (sigma++s) t))
  /\ instance_subst_inv [(ti,t)] l sigma e
  ==> IS_SOME (instance_subst l sigma e)
Proof
  ho_match_mp_tac instance_subst_ind
  >> strip_tac
  >- rw[instance_subst_inv_def,instance_subst_def]
  >> strip_tac
  >- (
    rpt GEN_TAC
    >> strip_tac
    >> imp_res_tac instance_subst_complete_step1
    >> rpt strip_tac
    >> qpat_x_assum `!ti t. _ ==> _` imp_res_tac
  )
  >> strip_tac
  >- (
    rpt GEN_TAC
    >> strip_tac
    >> imp_res_tac instance_subst_complete_step2
    >> rpt strip_tac
    >> qpat_x_assum `!ti t. _ ==> _` imp_res_tac
  )
  >> strip_tac
  >- (
    rw[instance_subst_def]
    >> qmatch_goalsub_abbrev_tac `_ \/ ~inst`
    >> Cases_on `inst`
    >> fs[markerTheory.Abbrev_def,instance_subst_inv_def]
  )
  >- (
    rpt GEN_TAC
    >> strip_tac
    >> imp_res_tac instance_subst_complete_step3
    >> rpt strip_tac
    >> qpat_x_assum `!ti t. _ ==> _` imp_res_tac
  )
QED

Theorem instance_subst_completeness:
  !t t'. (is_instance t t') = IS_SOME (instance_subst [(t',t)] [] [])
Proof
  rw[EQ_IMP_THM]
  >- (
    ho_match_mp_tac instance_subst_complete_step
    >> qexists_tac `t`
    >> qexists_tac `TYPE_SUBST i t`
    >> fs[TYPE_SUBST_NIL,instance_subst_inv_init]
    >> qexists_tac `i`
    >> fs[]
  )
  >- (
    fs[IS_SOME_EXISTS]
    >> Cases_on `x`
    >> imp_res_tac instance_subst_soundness
    >> rw[]
    >> qexists_tac `q`
    >> fs[]
  )
QED


(* TODO: lemmas that should maybe go elsewhere *)
Theorem MEM_PAIR_FST[local]:
  !a b l. MEM (a,b) l ==> MEM a (MAP FST l)
Proof
  rw[MEM_MAP] >> metis_tac[FST]
QED

Theorem MEM_const_list[local]:
  !cl prop name trm ctxt. MEM (ConstSpec cl prop) ctxt /\ MEM(name,trm) cl ==>
   MEM name (MAP FST (const_list ctxt))
Proof
  Induct_on `ctxt` \\ fs[]
  \\ Cases \\ rw[] \\ fs[consts_of_upd_def]
  \\ imp_res_tac MEM_PAIR_FST \\ fs[MAP_MAP_o,o_DEF,pairTheory.ELIM_UNCURRY]
  \\ metis_tac[]
QED

Theorem MEM_type_list[local]:
  !name pred abs rep ctxt. MEM (TypeDefn name pred abs rep) ctxt ==>
   MEM name (MAP FST (type_list ctxt))
Proof
  Induct_on `ctxt` \\ fs[]
  \\ Cases \\ rw[] \\ fs[consts_of_upd_def]
  \\ imp_res_tac MEM_PAIR_FST \\ fs[MAP_MAP_o,o_DEF,pairTheory.ELIM_UNCURRY]
  \\ metis_tac[]
QED

Theorem NRC_TC_IMP_NRC:
  !R n x y. NRC (R⁺) n x y ==> ?n'. NRC R n' x y /\ n' >= n
Proof
  Induct_on `n`
  >- (rw[] >> qexists_tac `0` >> rw[])
  >- (rw[NRC] >> fs[TC_eq_NRC]
      >> first_x_assum drule >> strip_tac
      >> Q.REFINE_EXISTS_TAC `_ + _`
      >> rw[NRC_ADD_EQN,PULL_EXISTS]
      >> asm_exists_tac >> rw[]
      >> asm_exists_tac >> rw[])
QED

Theorem NRC_TC_EQ_NRC:
  !R n x y. NRC (R⁺) (SUC n) x y = ?n'. (NRC R (SUC n') x y /\ n <= n')
Proof
  Induct_on `n` >- fs[TC_eq_NRC]
  >> rw[Once NRC]
  >> rw[EQ_IMP_THM]
  >- (fs[TC_eq_NRC] >> Q.REFINE_EXISTS_TAC `_ + _`
      >> rw[Once SUC_ADD_SYM]
      >> rw[NRC_ADD_EQN,PULL_EXISTS]
      >> asm_exists_tac >> rw[]
      >> asm_exists_tac >> rw[])
  >> Cases_on `n'` >> fs[NRC]
  >> fs[PULL_EXISTS] >> metis_tac [TC_RULES]
QED

(* properties of terminating relationships *)
Theorem terminating_TC:
  !R. terminating(TC R) ==> terminating R
Proof
  rw[terminating_def] >> pop_assum(qspec_then `x` assume_tac)
  >> fs[NRC_TC_EQ_NRC]
  >> qexists_tac `n`
  >> strip_tac >> pop_assum(qspecl_then [`y`,`n`] assume_tac)
  >> fs[]
QED

Theorem terminating_TC:
  !R. terminating R ==> terminating(TC R)
Proof
  rw[terminating_def] >> first_assum(qspec_then `x` assume_tac)
  >> fs[NRC_TC_EQ_NRC]
  >> qexists_tac `n`
  >> rpt strip_tac >> Cases_on `n ≤ n''` >> fs[]
  >> `?m. SUC n'' = (SUC n) + m` by intLib.COOPER_TAC
  >> pop_assum (fn thm => PURE_ONCE_REWRITE_TAC[thm])
  >> PURE_REWRITE_TAC [NRC_ADD_EQN]
  >> metis_tac[]
QED

Theorem terminating_RTC:
  !R. terminating(RTC R) ==> F
Proof
  rw[terminating_def] >> qexists_tac `ARB` >> strip_tac
  >> qexists_tac `ARB`
  >> Induct_on `n` >> rpt strip_tac
  >> fs[NRC,PULL_EXISTS] >> metis_tac[RTC_REFL]
QED

Theorem LRC_IMP_NRC[local]:
  LRC R l x y ==> NRC R (LENGTH l) x y
Proof
  metis_tac[NRC_LRC]
QED

Theorem EXTEND_RTC_TC[local]:
  ∀R x y z. R^* x y ∧ R y z ⇒ R⁺ x z
Proof
  rw[] \\ imp_res_tac RTC_TC_RC \\ fs[RC_DEF] \\ metis_tac[TC_RULES]
QED

Theorem transitive_superreln_incl_TC[local]:
  !x y. R⁺ x y ==> !R'. rel_to_reln R ⊆ rel_to_reln R' /\ transitive R' ==> R' x y
Proof
  ho_match_mp_tac TC_INDUCT \\ rpt strip_tac
  >- fs[rel_to_reln_def,SUBSET_DEF,PULL_EXISTS]
  \\ rpt(first_x_assum drule \\ disch_then drule \\ strip_tac)
  \\ metis_tac[transitive_def]
QED

Theorem LRC_rhs_rel[local]:
 !R l x y. LRC R l x y ==> EVERY (λe. ?e'. R e e' ) l
Proof
 Induct_on `l` >> rw[LRC_def] >> metis_tac[]
QED

Theorem transitive_antisym_LRC_ALL_DISTINCT[local]:
  !R R' l x y. rel_to_reln R ⊆ rel_to_reln R'
   /\ (!x y. R' x y ==> ¬R' y x)
   /\ transitive R'
   /\ LRC R l x y
   ==> ALL_DISTINCT(l ++ [y])
Proof
  Induct_on `l` >- rw[]
  >> rpt strip_tac
  >> `ALL_DISTINCT(l ++ [y])`
       by(first_x_assum match_mp_tac >> asm_exists_tac >> fs[LRC_def] >> metis_tac[])
  >> fs[] >> CCONTR_TAC >> fs[]
  >- (drule(GEN_ALL LRC_MEM_right) >> disch_then drule \\ strip_tac
      >> drule LRC_IMP_NRC \\ strip_tac
      >> dxrule NRC_RTC \\ strip_tac
      >> drule EXTEND_RTC_TC' >> disch_then drule \\ strip_tac
      \\ drule transitive_superreln_incl_TC
      \\ metis_tac[LRC_def])
  >> rveq
  >> drule(LRC_IMP_NRC) \\ strip_tac
  >> fs[]
  >> imp_res_tac TC_eq_NRC
  >> drule transitive_superreln_incl_TC
  >> metis_tac[LRC_def]
QED

Theorem finite_ordered_IMP_terminating:
  (!x y. R' x y ==> ¬R' y x)
   /\ transitive R' /\ rel_to_reln R ⊆ rel_to_reln R'
   /\ FINITE(rel_to_reln R)
   ==> terminating R
Proof
  rw[terminating_def]
  >> CCONTR_TAC >> fs[]
  >> first_x_assum(qspec_then `CARD(rel_to_reln R)` assume_tac)
  >> fs[]
  >> imp_res_tac TC_eq_NRC
  >> fs[NRC_LRC]
  >> drule transitive_antisym_LRC_ALL_DISTINCT
  >> rpt(disch_then drule)
  >> strip_tac
  >> drule LRC_rhs_rel \\ strip_tac
  >> fs[EVERY_MEM]
  >> `set ls ⊆ (IMAGE FST (rel_to_reln R))`
     by(fs[SUBSET_DEF] \\ rpt strip_tac
        \\ fs[rel_to_reln_def,PULL_EXISTS])
  >> `CARD (IMAGE FST (rel_to_reln R)) <= CARD(rel_to_reln R)`
      by(metis_tac[CARD_IMAGE])
  >> fs[ALL_DISTINCT_APPEND]
  >> imp_res_tac ALL_DISTINCT_CARD_LIST_TO_SET
  >> `FINITE (IMAGE FST (rel_to_reln R))` by(metis_tac[IMAGE_FINITE])
  >> drule CARD_SUBSET >> disch_then drule >> strip_tac
  >> fs[]
QED


(* theorems about LR_TYPE_SUBST *)

Theorem const_type_LR_TYPE_SUBST_lr:
  !a s. welltyped (OUTR a) /\ is_const_or_type (LR_TYPE_SUBST s a) ==> is_const_or_type a
Proof
  rw[LR_TYPE_SUBST_def,SUM_MAP,is_const_or_type_def,INST_def]
  >- (CASE_TAC >> fs[])
  >> rpt (FULL_CASE_TAC >> fs[])
  >- fs[INST_CORE_def,REV_ASSOCD_def]
  >- (
    rename1`INST_CORE [] s (Comb t t0)`
    >> qspecl_then [`Comb t t0`,`s`] assume_tac (CONV_RULE SWAP_FORALL_CONV INST_CORE_NIL_IS_RESULT)
    >> rfs[INST_CORE_def,REV_ASSOCD_def]
    >> rpt (FULL_CASE_TAC >> fs[])
    >> imp_res_tac IS_RESULT_IMP_Result
    >> imp_res_tac IS_CLASH_IMP
  )
  >- (
    rename1`INST_CORE [] s (Abs t t0)`
    >> qspecl_then [`Abs t t0`,`s`] assume_tac (CONV_RULE SWAP_FORALL_CONV INST_CORE_NIL_IS_RESULT)
    >> rfs[INST_CORE_def,REV_ASSOCD_def]
    >> rpt (FULL_CASE_TAC >> fs[])
    >> imp_res_tac IS_RESULT_IMP_Result
    >> imp_res_tac IS_CLASH_IMP
  )
QED

Theorem LR_TYPE_SUBST_compose:
  !s s' x. is_const_or_type x
  ==> LR_TYPE_SUBST s' (LR_TYPE_SUBST s x)
    = LR_TYPE_SUBST (MAP (TYPE_SUBST s' ## I) s ++ s') x
Proof
  rw[LR_TYPE_SUBST_def,SUM_MAP,TYPE_SUBST_compose]
  >> fs[Excl "NOT_ISL_ISR",is_const_or_type_def]
  >> rpt (FULL_CASE_TAC >> fs[])
  >> fs[INST_def,INST_CORE_def,TYPE_SUBST_compose]
QED

Theorem const_type_LR_TYPE_SUBST:
  !a s. ISL a \/ welltyped (OUTR a) ==> is_const_or_type (LR_TYPE_SUBST s a) = is_const_or_type a
Proof
  rpt strip_tac
  >> fs[]
  >- (
    rw[EQ_IMP_THM,is_const_or_type_def,LR_TYPE_SUBST_def]
    >> rpt (FULL_CASE_TAC >> fs[SUM_MAP])
  )
  >> rw[EQ_IMP_THM]
  >- imp_res_tac const_type_LR_TYPE_SUBST_lr
  >> fs[is_const_or_type_def,LR_TYPE_SUBST_def]
  >> rpt strip_tac
  >> rpt (FULL_CASE_TAC >> fs[SUM_MAP])
  >> fs[INST_def,INST_CORE_def,is_const_or_type_def]
QED

Theorem subst_clos_rel_LR_TYPE_SUBST_imp:
  !a b R. subst_clos_rel R a b
  ==> !rho. subst_clos_rel R (LR_TYPE_SUBST rho a) (LR_TYPE_SUBST rho b)
Proof
  rw[subst_clos_rel_cases]
  >> rename1 `LR_TYPE_SUBST rho' (LR_TYPE_SUBST rho a')`
  >> qspec_then `rho` assume_tac (CONV_RULE SWAP_FORALL_CONV const_type_LR_TYPE_SUBST)
  >> qspec_then `rho'` assume_tac (CONV_RULE SWAP_FORALL_CONV const_type_LR_TYPE_SUBST)
  >> imp_res_tac LR_TYPE_SUBST_sides
  >> first_assum (qspec_then `a'` mp_tac)
  >> first_x_assum (qspec_then `b'` mp_tac)
  >> first_assum (qspec_then `LR_TYPE_SUBST rho a'` mp_tac)
  >> first_x_assum (qspec_then `LR_TYPE_SUBST rho b'` mp_tac)
  >> rveq
  >> rw[]
  >> fs[LR_TYPE_SUBST_compose]
  >> qexists_tac `a'`
  >> qexists_tac `b'`
  >> qmatch_goalsub_abbrev_tac `LR_TYPE_SUBST s _`
  >> qexists_tac `s`
  >> fs[]
QED

(* Lemma 3.4, Kunčar 2015 *)
Theorem trans_subst_clos_is_substitutive:
  !ctxt a b. (subst_clos_rel (dependency ctxt))⁺ a b
  ==>  !rho. (subst_clos_rel (dependency ctxt))⁺ (LR_TYPE_SUBST rho a) (LR_TYPE_SUBST rho b)
Proof
  strip_tac
  >> ho_match_mp_tac TC_INDUCT
  >> strip_tac
  >> fs[TC_SUBSET,subst_clos_rel_LR_TYPE_SUBST_imp]
  >> rpt strip_tac
  >> rename1`LR_TYPE_SUBST rho _`
  >> NTAC 2 (first_x_assum (qspec_then `rho` assume_tac))
  >> drule (REWRITE_RULE[transitive_def] TC_TRANSITIVE)
  >> fs[]
QED



(* normalisation of type variable names *)
Definition normalise_tyvars_def:
  normalise_tyvars ty =
  let tvs = tyvars ty;
      ntvs = GENLIST (λn. Tyvar(strlit(REPLICATE (SUC n) #"a"))) (LENGTH tvs);
  in
    TYPE_SUBST (ZIP(ntvs,MAP Tyvar tvs)) ty
End

Definition normalise_tvars_def:
  normalise_tvars tm =
  let tvs = tvars tm;
      ntvs = GENLIST (λn. Tyvar(strlit(REPLICATE (SUC n) #"a"))) (LENGTH tvs);
  in
    INST (ZIP(ntvs,MAP Tyvar tvs)) tm
End

(* Quotient of a relation under type variable name normalisation*)
Definition normalise_rel_def:
  normalise_rel R = (λx y. ?x' y'. R x' y' /\
    x = (normalise_tyvars ## normalise_tvars) x' /\
    y = (normalise_tyvars ## normalise_tvars) y')
End

Theorem terminating_normalise_rel:
  terminating(normalise_rel R) ==> terminating R
Proof
  rw[terminating_def,normalise_rel_def]
  >> first_x_assum(qspec_then `(normalise_tyvars ## normalise_tvars) x` strip_assume_tac)
  >> qexists_tac `n`
  >> strip_tac
  >> first_x_assum(qspec_then `(normalise_tyvars ## normalise_tvars) y` mp_tac)
  >> simp[GSYM MONO_NOT_EQ]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`y`,`x`]
  >> Induct_on `n`
  >- (rw[] >> metis_tac[])
  >- (PURE_ONCE_REWRITE_TAC[NRC]
      >> rw[PULL_EXISTS] >> asm_exists_tac
      >> rw[])
QED

Theorem subst_clos_disj:
  subst_clos(λx y. R1 x y \/ R2 x y) = (λx y. (subst_clos R1) x y \/ (subst_clos R2) x y)
Proof
  qmatch_goalsub_abbrev_tac `a1 = a2`
  >> `!u v. a1 u v = a2 u v` suffices_by metis_tac[]
  >> unabbrev_all_tac >> Cases >> Cases
  >> EQ_TAC >> fs[subst_clos_def] >> rw[]
  >> metis_tac[]
QED

Theorem normalise_rel_disj:
  normalise_rel(λx y. R1 x y \/ R2 x y) = (λx y. (normalise_rel R1) x y \/ (normalise_rel R2) x y)
Proof
  qmatch_goalsub_abbrev_tac `a1 = a2`
  >> `!u v. a1 u v = a2 u v` suffices_by metis_tac[]
  >> unabbrev_all_tac >> Cases >> Cases
  >> EQ_TAC >> fs[normalise_rel_def] >> rw[]
  >> metis_tac[]
QED

Theorem subst_clos_empty:
  subst_clos (λx y. F) = (λx y. F)
Proof
  `!u v. subst_clos (λx y. F) u v = (λx y. F) u v` suffices_by metis_tac[]
  \\ Cases >> Cases >> rw[subst_clos_def]
QED

val finite_split =
REWRITE_RULE [UNION_DEF,IN_DEF] FINITE_UNION |> CONV_RULE(DEPTH_CONV BETA_CONV)

Theorem rel_set_union[local]:
  !R R'. {(x,y) | R x y ∨ R' x y} = {(x,y) | R x y} ∪ {(x,y) | R' x y}
Proof
  rw[ELIM_UNCURRY] >> rw[UNION_DEF]
QED

Definition types_of_type_def:
  types_of_type (Tyvar t) = [Tyvar t]
  /\ types_of_type (Tyapp t tys) = Tyapp t tys::FLAT(MAP types_of_type tys)
Termination
  wf_rel_tac `measure type_size`
   >> rw[MEM_SPLIT] >> rw[type1_size_append,type_size_def]
End

Definition types_of_rel:
  types_of_rel R =
    {t | (?t' e. (R e (INL t') \/ R (INL t') e) /\ MEM t (types_of_type t'))
          \/ (?c e. (R e (INR c) \/ R (INR c) e) /\ MEM t (types_of_type(typeof c)))}
End

Definition bounded_subst_def:
  bounded_subst tvs R sigma = (set(MAP FST sigma) ⊆ set(MAP Tyvar tvs) /\
                             ALL_DISTINCT(MAP FST sigma) /\
                             EVERY (λt. t IN (types_of_rel R)) (MAP SND sigma))
End

Definition bounded_subst_clos_def:
  (bounded_subst_clos R (INL t1) (INL t2) =
    (?t1' t2' sigma. t1 = TYPE_SUBST sigma t1' /\ t2 = TYPE_SUBST sigma t2' /\ R (INL t1') (INL t2') /\ bounded_subst (tyvars t1' ++ tyvars t2') R sigma)) /\
  (bounded_subst_clos R (INL t) (INR c) =
   (?t' c' sigma. t = TYPE_SUBST sigma t' /\ c = INST sigma c' /\ R (INL t') (INR c') /\ bounded_subst (tyvars t' ++ tyvars(typeof c')) R sigma))
 /\
  (bounded_subst_clos R (INR c) (INL t) =
   (?t' c' sigma. t = TYPE_SUBST sigma t' /\ c = INST sigma c' /\ R (INR c') (INL t') /\ bounded_subst (tyvars t' ++ tyvars(typeof c')) R sigma))
 /\
  (bounded_subst_clos R (INR c1) (INR c2) =
   (?c1' c2' sigma. c1 = INST sigma c1' /\ c2 = INST sigma c2' /\ R (INR c1') (INR c2') /\ bounded_subst (tyvars(typeof c1') ++ tyvars(typeof c2')) R sigma))
End

Theorem bounded_subst_clos_empty:
  bounded_subst_clos (λx y. F) = (λx y. F)
Proof
  `!u v. bounded_subst_clos (λx y. F) u v = (λx y. F) u v` suffices_by metis_tac[]
  \\ Cases >> Cases >> rw[bounded_subst_clos_def]
QED

Theorem bounded_subst_clos_IMP_subst_clos:
  !R u v. bounded_subst_clos R u v ==> subst_clos R u v
Proof
  strip_tac >> Cases >> Cases >> rw[subst_clos_def,bounded_subst_clos_def]
  >> metis_tac[]
QED

(* updates preserve well-formedness *)
Theorem update_ctxt_wf:
  !ctxt upd. wf_ctxt ctxt /\ upd updates ctxt ==> wf_ctxt(upd::ctxt)
Proof
  cheat
  (*rw[updates_cases]
  \\ fs[wf_ctxt_def]
  >- cheat
  >- (conj_tac
      >- (fs[orth_ctxt_def] \\ rpt strip_tac
          \\ rveq \\ fs[]
          \\ TRY(rw[orth_ci_def] \\ NO_TAC)
          >- (`name1 ≠ name2` suffices_by rw[orth_ci_def]
              \\ CCONTR_TAC \\ fs[] \\ imp_res_tac ALOOKUP_ALL_DISTINCT_MEM
              \\ rveq \\ fs[])
          >- (`name1 ≠ name2` suffices_by rw[orth_ci_def]
              \\ CCONTR_TAC \\ fs[]
              \\ imp_res_tac MEM_PAIR_FST
              \\ first_x_assum drule \\ strip_tac
              \\ fs[] \\ imp_res_tac MEM_const_list)
          >- (`name1 ≠ name2` suffices_by rw[orth_ci_def]
              \\ CCONTR_TAC \\ fs[]
              \\ imp_res_tac MEM_PAIR_FST
              \\ first_x_assum drule \\ strip_tac
              \\ fs[] \\ imp_res_tac MEM_const_list)
          \\ (first_x_assum ho_match_mp_tac \\ metis_tac[]))
      >- (cheat))
  >- (conj_tac
      >- (fs[orth_ctxt_def] \\ rpt strip_tac
          \\ rveq \\ fs[]
          \\ TRY(rw[orth_ty_def] \\ NO_TAC)
          \\ TRY(qmatch_goalsub_abbrev_tac `orth_ty (Tyapp namel _) (Tyapp namer _)`
                 \\ `namel ≠ namer` suffices_by rw[orth_ty_def]
                 \\ CCONTR_TAC \\ fs[]
                 \\ imp_res_tac MEM_PAIR_FST
                 \\ first_x_assum drule \\ strip_tac
                 \\ fs[] \\ imp_res_tac MEM_type_list \\ NO_TAC)
          \\ first_x_assum ho_match_mp_tac \\ metis_tac[])
      >- (cheat)
     )*)
QED

(* recover constant definition as a special case of specification *)

val _ = Parse.overload_on("ConstDef",``λx t. ConstSpec [(x,t)] (Var x (typeof t) === t)``)

Theorem ConstDef_updates:
   ∀name tm ctxt.
    theory_ok (thyof ctxt) ∧
    term_ok (sigof ctxt) tm ∧
    name ∉ FDOM (tmsof ctxt) ∧
    CLOSED tm ∧
    set (tvars tm) ⊆ set (tyvars (typeof tm))
    ⇒ ConstDef name tm updates ctxt
Proof
  cheat
  (*rw[] >>
  match_mp_tac(List.nth(CONJUNCTS updates_rules,2)) >>
  simp[EVERY_MAP] >> fs[SUBSET_DEF] >>
  simp[vfree_in_equation] >> fs[CLOSED_def] >>
  match_mp_tac(List.nth(CONJUNCTS proves_rules,1)) >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_type_ok >>
  simp[EQUATION_HAS_TYPE_BOOL,term_ok_equation,term_ok_def]*)
QED

(* lookups in extended contexts *)

Theorem FLOOKUP_tmsof_updates:
   ∀upd ctxt. upd updates ctxt ⇒
    FLOOKUP (tmsof (thyof ctxt)) name = SOME ty ⇒
    FLOOKUP (tmsof (thyof (upd::ctxt))) name = SOME ty
Proof
  rw[finite_mapTheory.FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >> imp_res_tac updates_DISJOINT >>
  fs[pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[alistTheory.ALOOKUP_MEM]
QED

Theorem FLOOKUP_tysof_updates:
   ∀upd ctxt. upd updates ctxt ⇒
    FLOOKUP (tysof (thyof ctxt)) name = SOME a ⇒
    FLOOKUP (tysof (thyof (upd::ctxt))) name = SOME a
Proof
  rw[finite_mapTheory.FLOOKUP_FUNION] >>
  BasicProvers.CASE_TAC >> imp_res_tac updates_DISJOINT >>
  fs[pred_setTheory.IN_DISJOINT,listTheory.MEM_MAP,pairTheory.EXISTS_PROD] >>
  PROVE_TAC[alistTheory.ALOOKUP_MEM]
QED

Theorem FLOOKUP_tysof_extends:
   ∀ctxt2 ctxt1. ctxt1 extends ctxt2 ⇒
   (FLOOKUP (tysof (sigof ctxt2)) k = SOME v) ⇒
   (FLOOKUP (tysof (sigof ctxt1)) k = SOME v)
Proof
  ho_match_mp_tac extends_ind
  \\ REWRITE_TAC[GSYM o_DEF]
  \\ rw[ALOOKUP_APPEND]
  \\ CASE_TAC
  \\ fs[updates_cases]
  \\ rw[] \\ fs[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,EXISTS_PROD]
  \\ metis_tac[]
QED

Theorem FLOOKUP_tmsof_extends:
   ∀ctxt2 ctxt1. ctxt1 extends ctxt2 ⇒
   (FLOOKUP (tmsof (sigof ctxt2)) k = SOME v) ⇒
   (FLOOKUP (tmsof (sigof ctxt1)) k = SOME v)
Proof
  cheat
  (* ho_match_mp_tac extends_ind
  \\ REWRITE_TAC[GSYM o_DEF]
  \\ rw[ALOOKUP_APPEND]
  \\ CASE_TAC
  \\ fs[updates_cases]
  \\ rw[] \\ fs[]
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs[MEM_MAP,EXISTS_PROD]
  \\ TRY(qpat_x_assum`_ = SOME _`mp_tac \\ rw[])
  \\ metis_tac[] *)
QED

Theorem extends_sub:
   ∀ctxt2 ctxt1. ctxt2 extends ctxt1 ⇒
      tmsof ctxt1 ⊑ tmsof ctxt2 ∧
      tysof ctxt1 ⊑ tysof ctxt2 ∧
      axsof ctxt1 ⊆ axsof ctxt2
Proof
  simp[extends_def] >>
  ho_match_mp_tac relationTheory.RTC_INDUCT >>
  simp[PULL_EXISTS] >>
  rpt gen_tac >> strip_tac >>
  rpt conj_tac >>
  TRY (
    match_mp_tac finite_mapTheory.SUBMAP_FUNION >>
    disj2_tac >> simp[] >>
    imp_res_tac updates_DISJOINT >> fs[] >>
    fs[finite_mapTheory.SUBMAP_DEF,pred_setTheory.IN_DISJOINT] >>
    metis_tac[] ) >>
  metis_tac[pred_setTheory.SUBSET_UNION,pred_setTheory.SUBSET_TRANS]
QED

(* proofs still work in extended contexts *)

Theorem update_extension[local]:
    !lhs tm.
      lhs |- tm
      ⇒
      !ctxt tms upd.
        lhs = (thyof ctxt,tms) ∧
        upd updates ctxt
        ⇒
        (thyof (upd::ctxt),tms) |- tm
Proof
  ho_match_mp_tac proves_ind >>
  rw []
  >- (rw [Once proves_cases] >>
      disj1_tac >>
      MAP_EVERY qexists_tac [`l`, `r`, `ty`, `x`] >>
      rw [] >>
      match_mp_tac type_ok_extend >>
      qexists_tac `tysof (sigof (thyof ctxt))` >>
      rw [] >>
      match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
      fs [Once updates_cases])
  >- (rw [Once proves_cases] >>
      disj2_tac >>
      disj1_tac >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (match_mp_tac term_ok_extend >>
          MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              metis_tac [updates_DISJOINT])
          >- (Cases_on `ctxt` >>
              fs [])))
  >- (rw [Once proves_cases] >>
      disj2_tac >>
      disj1_tac >>
      rw [] >>
      MAP_EVERY qexists_tac [`t`, `ty`, `x`] >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (match_mp_tac type_ok_extend >>
          qexists_tac `tysof ctxt` >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (Cases_on `ctxt` >>
              fs []))
      >- (match_mp_tac term_ok_extend >>
          MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              metis_tac [updates_DISJOINT])
          >- (Cases_on `ctxt` >>
              fs [])))
  >- (rw [Once proves_cases] >>
      ntac 3 disj2_tac >>
      disj1_tac >>
      rw [] >>
      metis_tac [])
  >- (rw [Once proves_cases] >>
      ntac 4 disj2_tac >>
      disj1_tac >>
      rw [] >>
      metis_tac [])
  >- (rw [Once proves_cases] >>
      ntac 5 disj2_tac >>
      disj1_tac >>
      rw [] >>
      MAP_EVERY qexists_tac [`tm`, `h`, `ilist`] >>
      rw [] >>
      res_tac  >>
      fs [] >>
      rw [] >>
      match_mp_tac term_ok_extend >>
      MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
      rw []
      >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
          fs [Once updates_cases])
      >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
          metis_tac [updates_DISJOINT]))
  >- (rw [Once proves_cases] >>
      ntac 6 disj2_tac >>
      disj1_tac >>
      rw [] >>
      MAP_EVERY qexists_tac [`tm`, `h`, `tyin`] >>
      rw [] >>
      fs [EVERY_MAP, EVERY_MEM] >>
      rw [] >>
      match_mp_tac type_ok_extend >>
      qexists_tac `tysof ctxt` >>
      rw [] >>
      match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
      fs [Once updates_cases])
  >- (rw [Once proves_cases] >>
      ntac 7 disj2_tac >>
      disj1_tac >>
      rw [] >>
      metis_tac [])
  >- (rw [Once proves_cases] >>
      ntac 7 disj2_tac >>
      disj1_tac >>
      rw [] >>
      qexists_tac `t` >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (match_mp_tac term_ok_extend >>
          MAP_EVERY qexists_tac [`tysof ctxt`, `tmsof ctxt`] >>
          rw []
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              fs [Once updates_cases])
          >- (match_mp_tac (hd (tl (CONJUNCTS SUBMAP_FUNION_ID))) >>
              metis_tac [updates_DISJOINT])
          >- (Cases_on `ctxt` >>
              fs [])))
  >- (rw [Once proves_cases] >>
      ntac 8 disj2_tac >>
      rw []
      >- (imp_res_tac updates_theory_ok >>
          fs [])
      >- (Cases_on `ctxt` >>
          fs []))
QED

Theorem updates_proves:
   ∀upd ctxt.  upd updates ctxt ⇒
    ∀h c.
    (thyof ctxt,h) |- c ⇒
    (thyof (upd::ctxt),h) |- c
Proof
  metis_tac[update_extension]
QED

Theorem extends_proves:
   !c2 c1.
     c2 extends c1
     ==>
     !h c.
       (thyof c1,h) |- c ==> (thyof c2,h) |- c
Proof
  Induct \\ rw [extends_def]
  \\ fs [Once RTC_CASES1] \\ rw [] \\ fs [BETA_THM]
  \\ fs [GSYM extends_def]
  \\ first_x_assum drule
  \\ disch_then drule \\ rw []
  \\ drule updates_proves
  \\ disch_then drule \\ rw []
QED

(* types occurring in a term *)

Definition types_in_def:
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs v t) = types_in v ∪ types_in t
End
val _ = export_rewrites["types_in_def"]

Theorem type_ok_types_in:
   ∀sig. is_std_sig sig ⇒ ∀tm ty. term_ok sig tm ∧ ty ∈ types_in tm ⇒ type_ok (tysof sig) ty
Proof
  gen_tac >> strip_tac >> Induct >> simp[] >> rw[] >>
  TRY (imp_res_tac term_ok_def >> NO_TAC) >> fs[term_ok_def]
QED

Theorem VFREE_IN_types_in:
   ∀t2 t1. VFREE_IN t1 t2 ⇒ typeof t1 ∈ types_in t2
Proof
  ho_match_mp_tac term_induction >> rw[] >> rw[]
QED

Theorem Var_subterm_types_in[local]:
  ∀t x ty. Var x ty subterm t ⇒ ty ∈ types_in t
Proof
  ho_match_mp_tac term_induction >> rw[subterm_Comb,subterm_Abs] >>
  metis_tac[]
QED

Theorem Const_subterm_types_in[local]:
  ∀t x ty. Const x ty subterm t ⇒ ty ∈ types_in t
Proof
  ho_match_mp_tac term_induction >> rw[subterm_Comb,subterm_Abs] >>
  metis_tac[]
QED

Theorem subterm_typeof_types_in:
   ∀t1 t2 name args. (Tyapp name args) subtype (typeof t1) ∧ t1 subterm t2 ∧ welltyped t2 ∧ name ≠ (strlit"fun") ⇒
      ∃ty2. Tyapp name args subtype ty2 ∧ ty2 ∈ types_in t2
Proof
  ho_match_mp_tac term_induction >>
  conj_tac >- ( rw[] >> metis_tac[Var_subterm_types_in] ) >>
  conj_tac >- ( rw[] >> metis_tac[Const_subterm_types_in] ) >>
  conj_tac >- (
    rw[] >>
    imp_res_tac subterm_welltyped >> fs[] >> fs[] >>
    last_x_assum match_mp_tac >> simp[] >>
    conj_tac >- (
      simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] >>
      simp[subtype_Tyapp] >>
      metis_tac[relationTheory.RTC_REFL] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[subterm_Comb] ) >>
  rw[] >>
  fs[subtype_Tyapp] >- (
    last_x_assum(match_mp_tac) >> simp[] >>
    conj_tac >- (
      simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
      first_assum(match_exists_tac o concl) >> simp[] ) >>
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    ONCE_REWRITE_TAC[CONJ_COMM] >>
    first_assum(match_exists_tac o concl) >> simp[] >>
    simp[subterm_Abs] ) >>
  first_x_assum(match_mp_tac) >> simp[] >>
  conj_tac >- (
    simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
    first_assum(match_exists_tac o concl) >> simp[] ) >>
  simp[Once relationTheory.RTC_CASES_RTC_TWICE] >>
  ONCE_REWRITE_TAC[CONJ_COMM] >>
  first_assum(match_exists_tac o concl) >> simp[] >>
  simp[subterm_Abs]
QED

(* a type matching algorithm, based on the implementation in HOL4 *)

Definition tymatch_def:
  (tymatch [] [] sids = SOME sids) ∧
  (tymatch [] _ _ = NONE) ∧
  (tymatch _ [] _ = NONE) ∧
  (tymatch (Tyvar name::ps) (ty::obs) sids =
   let (s,ids) = sids in
   let v = REV_ASSOCD (Tyvar name) s (Tyvar name) in
   case if v = Tyvar name then
          if MEM name ids then SOME v else NONE
        else SOME v
   of NONE => if v=ty then tymatch ps obs (s,name::ids) else tymatch ps obs ((ty,v)::s,ids)
    | SOME ty1 => if ty1=ty then tymatch ps obs sids else NONE) ∧
  (tymatch (Tyapp c1 a1::ps) (Tyapp c2 a2::obs) sids =
   if c1=c2 then tymatch (a1++ps) (a2++obs) sids else NONE) ∧
  (tymatch _ _ _ = NONE)
Termination
  WF_REL_TAC`measure (λx. type1_size (FST x) + type1_size (FST(SND x)))`
  >> simp[type1_size_append]
End

val tymatch_ind = theorem "tymatch_ind";

Definition arities_match_def:
  (arities_match [] [] ⇔ T) ∧
  (arities_match [] _ ⇔ F) ∧
  (arities_match _ [] ⇔ F) ∧
  (arities_match (Tyapp c1 a1::xs) (Tyapp c2 a2::ys) ⇔
   ((c1 = c2) ⇒ arities_match a1 a2) ∧ arities_match xs ys) ∧
  (arities_match (_::xs) (_::ys) ⇔ arities_match xs ys)
Termination
  WF_REL_TAC`measure (λx. type1_size (FST x) + type1_size (SND x))`
End
val arities_match_ind = theorem "arities_match_ind"

Theorem arities_match_length:
   ∀l1 l2. arities_match l1 l2 ⇒ (LENGTH l1 = LENGTH l2)
Proof
  ho_match_mp_tac arities_match_ind >> simp[arities_match_def]
QED

Theorem arities_match_nil[simp]:
   (arities_match [] ls = (ls = [])) ∧
    (arities_match ls [] = (ls = []))
Proof
  Cases_on`ls`>> simp[arities_match_def]
QED

Theorem arities_match_Tyvar[simp]:
   arities_match (Tyvar v::ps) (ty::obs) = arities_match ps obs
Proof
  Cases_on`ty`>>simp[arities_match_def]
QED

Theorem arities_match_append:
   ∀l1 l2 l3 l4.
    arities_match l1 l2 ∧ arities_match l3 l4 ⇒
    arities_match (l1++l3) (l2++l4)
Proof
  ho_match_mp_tac arities_match_ind >>
  simp[arities_match_def]
QED

Theorem tymatch_SOME:
   ∀ps obs sids s' ids'.
     arities_match ps obs ∧
      DISJOINT (set (MAP SND (FST sids))) (set (MAP Tyvar (SND sids))) ∧
      (∀name. ¬MEM (Tyvar name,Tyvar name) (FST sids)) ∧
      ALL_DISTINCT (MAP SND (FST sids)) ∧
      (tymatch ps obs sids = SOME (s',ids')) ⇒
       ∃s1 ids1.
         (s' = s1++(FST sids)) ∧ (ids' = ids1++(SND sids)) ∧
         DISJOINT (set (MAP SND s')) (set (MAP Tyvar ids')) ∧
         (∀name. ¬MEM (Tyvar name,Tyvar name) s') ∧
         ALL_DISTINCT (MAP SND s') ∧
         (MAP (TYPE_SUBST s') ps = obs)
Proof
  ho_match_mp_tac tymatch_ind >>
  simp[tymatch_def,arities_match_def] >>
  conj_tac >- (
    rpt gen_tac >>
    `∃s ids. sids = (s,ids)` by metis_tac[pairTheory.pair_CASES] >>
    simp[] >> strip_tac >>
    rpt gen_tac >>
    reverse IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[arities_match_def] >> rfs[] >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[] >> rfs[] >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND,ALL_DISTINCT_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    IF_CASES_TAC >> fs[] >- (
      strip_tac >> fs[] >> rfs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      `¬MEM (Tyvar name) (MAP SND s)` by (
        fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
        BasicProvers.EVERY_CASE_TAC >- (
          imp_res_tac ALOOKUP_FAILS >> fs[MEM_MAP,EXISTS_PROD] ) >>
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
      BasicProvers.CASE_TAC >> fs[] >>
      reverse BasicProvers.EVERY_CASE_TAC >> fs[] >- (
        imp_res_tac ALOOKUP_MEM >>
        fs[MEM_MAP,EXISTS_PROD] >>
        metis_tac[] ) >>
      rpt BasicProvers.VAR_EQ_TAC >>
      fs[ALL_DISTINCT_APPEND] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[IN_DISJOINT,MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
      metis_tac[] ) >>
    strip_tac >> fs[] >> rfs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    `¬MEM (Tyvar name) (MAP SND s)` by (
      fs[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
      BasicProvers.EVERY_CASE_TAC >- (
        imp_res_tac ALOOKUP_FAILS >> fs[MEM_MAP,EXISTS_PROD] ) >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    `¬MEM (Tyvar name) (MAP Tyvar ids)` by fs[MEM_MAP] >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    simp[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
    BasicProvers.CASE_TAC >>
    fs[ALL_DISTINCT_APPEND] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,PULL_EXISTS,EXISTS_PROD] >>
    metis_tac[] ) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `arities_match (a1++ps) (a2++obs)` by
    (imp_res_tac arities_match_append) >>
  fs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac (std_ss++ETA_ss) [] >>
  imp_res_tac arities_match_length >>
  fs[APPEND_EQ_APPEND] >>
  rfs[] >>
  `LENGTH l = 0` by DECIDE_TAC >>
  fs[LENGTH_NIL]
QED

Definition match_type_def:
  match_type ty1 ty2 = OPTION_MAP FST (tymatch [ty1] [ty2] ([],[]))
End

Theorem type_ok_arities_match:
   ∀tys ty1 ty2.
    type_ok tys ty1 ∧ type_ok tys ty2 ⇒ arities_match [ty1] [ty2]
Proof
  gen_tac >> ho_match_mp_tac type_ind >> simp[] >>
  gen_tac >> strip_tac >>
  gen_tac >> Cases >> simp[arities_match_def] >>
  rw[type_ok_def] >> fs[] >>
  fs[EVERY_MEM] >>
  `∀ty1 ty2. MEM ty1 l ∧ MEM ty2 l' ⇒ arities_match [ty1] [ty2]` by metis_tac[] >>
  pop_assum mp_tac >>
  qpat_x_assum`LENGTH X = Y`mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac[`l'`,`l`] >>
  Induct >> simp[LENGTH_NIL] >>
  gen_tac >> Cases >> rw[] >>
  `arities_match l t` by metis_tac[] >>
  `arities_match [h] [h']` by metis_tac[] >>
  metis_tac[arities_match_append,APPEND]
QED

Theorem match_type_SOME:
   ∀ty1 ty2 s. arities_match [ty1] [ty2] ⇒
    (match_type ty1 ty2 = SOME s) ⇒
    (TYPE_SUBST s ty1 = ty2)
Proof
  rw[match_type_def] >>
  qspecl_then[`[ty1]`,`[ty2]`,`[],[]`]mp_tac tymatch_SOME >>
  simp[] >>
  Cases_on`z`>>simp[]
QED

Theorem cyclic_IMP_wf:
  !ctxt. definitional ctxt ==> ~cyclic ctxt
Proof
  cheat
QED

Theorem cyclic_IMP_wf:
  !ctxt. ~cyclic ctxt ==> wf_ctxt ctxt
Proof
  cheat
QED

val _ = export_theory()
