open HolKernel boolLib boolSimps bossLib lcsymtacs pairTheory listTheory finite_mapTheory alistTheory relationTheory pred_setTheory sortingTheory stringTheory
open miscLib miscTheory holSyntaxLibTheory holSyntaxTheory
val _ = temp_tight_equality()
val _ = new_theory"holSyntaxExtra"

val type_ind = save_thm("type_ind",
  TypeBase.induction_of``:holSyntax$type``
  |> Q.SPECL[`P`,`EVERY P`]
  |> SIMP_RULE std_ss [EVERY_DEF]
  |> UNDISCH_ALL
  |> CONJUNCT1
  |> DISCH_ALL
  |> Q.GEN`P`)

(* deconstructing variables *)

val dest_var_def = Define`dest_var (Var x ty) = (x,ty)`
val _ = export_rewrites["dest_var_def"]

val ALOOKUP_MAP_dest_var = store_thm("ALOOKUP_MAP_dest_var",
  ``∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty))``,
  Induct >> simp[] >> Cases >> simp[EVERY_MEM,EVERY_MAP] >>
  rw[] >> fs[])

(* type substitution *)

val TYPE_SUBST_NIL = store_thm("TYPE_SUBST_NIL",
  ``∀ty. TYPE_SUBST [] ty = ty``,
  ho_match_mp_tac type_ind >>
  rw[REV_ASSOCD,MAP_EQ_ID] >>
  fs[EVERY_MEM])
val _ = export_rewrites["TYPE_SUBST_NIL"]

val TYPE_SUBST_Bool = store_thm("TYPE_SUBST_Bool",
  ``∀tyin. TYPE_SUBST tyin Bool = Bool``, rw[TYPE_SUBST_def])

val is_instance_refl = store_thm("is_instance_refl",
  ``∀ty. is_instance ty ty``,
  rw[] >> qexists_tac`[]` >> rw[])
val _ = export_rewrites["is_instance_refl"]

val swap_ff = store_thm("swap_ff",
  ``∀f g. (λ(x,y). (y,x)) o (f ## g) = (g ## f) o (λ(x,y). (y,x))``,
  rw[FUN_EQ_THM,FORALL_PROD])

val ff_def = store_thm("ff_def",
  ``∀f g. (f ## g) = λ(x,y). (f x, g y)``,
  rw[FUN_EQ_THM,FORALL_PROD,PAIR_MAP_THM])

val TYPE_SUBST_compose = store_thm("TYPE_SUBST_compose",
  ``∀tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty``,
  ho_match_mp_tac TYPE_SUBST_ind >>
  rw[TYPE_SUBST_def,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f] >>
  rw[REV_ASSOCD_ALOOKUP,ALOOKUP_APPEND] >>
  simp[MAP_MAP_o,swap_ff] >> simp[GSYM MAP_MAP_o] >>
  simp[ff_def,ALOOKUP_MAP] >>
  BasicProvers.CASE_TAC >> simp[TYPE_SUBST_def,REV_ASSOCD_ALOOKUP])

val TYPE_SUBST_tyvars = store_thm("TYPE_SUBST_tyvars",
  ``∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x)``,
  ho_match_mp_tac type_ind >>
  simp[tyvars_def] >>
  conj_tac >- metis_tac[] >>
  Induct >> simp[] >>
  gen_tac >> strip_tac >> fs[] >>
  rpt gen_tac >> EQ_TAC >> strip_tac >> fs[] >>
  fs[MEM_LIST_UNION] >> metis_tac[])

(* Welltyped terms *)

val WELLTYPED_LEMMA = store_thm("WELLTYPED_LEMMA",
  ``∀tm ty. tm has_type ty ⇒ (typeof tm = ty)``,
  ho_match_mp_tac has_type_ind >>
  simp[typeof_def,has_type_rules,codomain_def])

val WELLTYPED = store_thm("WELLTYPED",
  ``∀tm. welltyped tm ⇔ tm has_type (typeof tm)``,
  simp[welltyped_def] >> metis_tac[WELLTYPED_LEMMA])

val WELLTYPED_CLAUSES = store_thm("WELLTYPED_CLAUSES",
 ``(!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!n ty t. welltyped (Abs n ty t) = welltyped t)``,
  REPEAT STRIP_TAC THEN REWRITE_TAC[welltyped_def] THEN
  rw[Once has_type_cases] >>
  metis_tac[WELLTYPED,WELLTYPED_LEMMA])
val _ = export_rewrites["WELLTYPED_CLAUSES"]

(* Alpha-equivalence *)

val RACONV = store_thm("RACONV",
 ``(RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Const x1 ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Const x2 ty2) <=> (x1 = x2) /\ (ty1 = ty2)) /\
   (RACONV env (Const x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs x2 ty2 t2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Const x2 ty2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs x1 ty1 t1,Abs x2 ty2 t2) <=>
        (ty1 = ty2) /\ RACONV (CONS (Var x1 ty1,Var x2 ty2) env) (t1,t2))``,
  REPEAT CONJ_TAC THEN simp[Once RACONV_cases] >> metis_tac[])

val RACONV_REFL = store_thm("RACONV_REFL",
  ``∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t)``,
  Induct >> simp[RACONV,ALPHAVARS_REFL])

val ACONV_REFL = store_thm("ACONV_REFL",
  ``∀t. ACONV t t``,
  simp[ACONV_def,RACONV_REFL])
val _ = export_rewrites["ACONV_REFL"]

val RACONV_TRANS = store_thm("RACONV_TRANS",
  ``∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t)``,
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
  metis_tac[LENGTH,ZIP])

val ACONV_TRANS = store_thm("ACONV_TRANS",
  ``∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3``,
  rw[ACONV_def] >> imp_res_tac RACONV_TRANS >> fs[LENGTH_NIL])

val RACONV_SYM = store_thm("RACONV_SYM",
  ``∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)``,
  ho_match_mp_tac RACONV_ind >> simp[] >>
  conj_tac >- (
    Induct >> simp[ALPHAVARS_def,RACONV] >>
    Cases >> simp[] >>
    rw[] >> res_tac >> fs[RACONV]) >>
  simp[RACONV])

val ACONV_SYM = store_thm("ACONV_SYM",
  ``∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1``,
  rw[ACONV_def] >> imp_res_tac RACONV_SYM >> fs[])

val ALPHAVARS_TYPE = store_thm("ALPHAVARS_TYPE",
  ``∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t``,
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> rw[])

val RACONV_TYPE = store_thm("RACONV_TYPE",
  ``∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p)``,
  ho_match_mp_tac RACONV_ind >>
  simp[FORALL_PROD,typeof_def,WELLTYPED_CLAUSES] >>
  rw[] >> imp_res_tac ALPHAVARS_TYPE >>
  fs[typeof_def,WELLTYPED_CLAUSES])

val ACONV_TYPE = store_thm("ACONV_TYPE",
  ``∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t)``,
  rw[ACONV_def] >> imp_res_tac RACONV_TYPE >> fs[])

val RACONV_welltyped = store_thm("RACONV_welltyped",
  ``∀t1 env t2.
    EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
    welltyped t1 ∧ RACONV env (t1,t2) ⇒
    welltyped t2``,
  Induct >>
  simp[Once RACONV_cases] >- (
    rw[] >> rw[WELLTYPED_CLAUSES] )
  >- (
    rw[WELLTYPED_CLAUSES] >>
    pop_assum mp_tac >>
    simp[Once RACONV_cases] >>
    rw[] >> rw[WELLTYPED_CLAUSES] >>
    metis_tac[RACONV_TYPE,FST,SND] )
  >- (
    rw[Once RACONV_cases] >>
    pop_assum mp_tac >>
    rw[Once RACONV_cases] >>
    rw[WELLTYPED_CLAUSES] >>
    first_x_assum match_mp_tac >>
    qmatch_assum_abbrev_tac`RACONV env' pp` >>
    qexists_tac`env'` >>
    simp[Abbr`env'`]))

val ACONV_welltyped = store_thm("ACONV_welltyped",
  ``∀t1 t2. ACONV t1 t2 ∧ welltyped t1 ⇒ welltyped t2``,
  rw[ACONV_def] >>
  metis_tac[RACONV_welltyped,EVERY_DEF])

(* VFREE_IN lemmas *)

val VFREE_IN_RACONV = store_thm("VFREE_IN_RACONV",
  ``∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env)``,
  ho_match_mp_tac RACONV_ind >> simp[VFREE_IN_def] >>
  reverse conj_tac >- metis_tac[] >>
  Induct >> simp[ALPHAVARS_def,FORALL_PROD] >> rw[] >> metis_tac[])

val VFREE_IN_ACONV = store_thm("VFREE_IN_ACONV",
  ``∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t)``,
  rw[ACONV_def] >> imp_res_tac VFREE_IN_RACONV >> fs[])

(* TERM_UNION lemmas *)

val TERM_UNION_NONEW = store_thm("TERM_UNION_NONEW",
  ``∀l1 l2 x. MEM x (TERM_UNION l1 l2) ⇒ MEM x l1 ∨ MEM x l2``,
  Induct >> simp[TERM_UNION_def] >> rw[] >> metis_tac[])

val TERM_UNION_THM = store_thm("TERM_UNION_THM",
  ``∀l1 l2 x. MEM x l1 ∨ MEM x l2
              ⇒ ∃y. MEM y (TERM_UNION l1 l2) ∧ ACONV x y``,
  Induct >> simp[TERM_UNION_def] >> rw[EXISTS_MEM] >> metis_tac[ACONV_REFL])

val EVERY_TERM_UNION = store_thm("EVERY_TERM_UNION",
  ``EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (TERM_UNION l1 l2)``,
  rw[EVERY_MEM] >> metis_tac[TERM_UNION_NONEW])

(* VSUBST lemmas *)

val VSUBST_HAS_TYPE = store_thm("VSUBST_HAS_TYPE",
  ``∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty``,
  Induct >> simp[VSUBST_def]
  >- (
    map_every qx_gen_tac[`x`,`ty`,`tty`] >>
    Induct >> simp[REV_ASSOCD,FORALL_PROD] >>
    srw_tac[DNF_ss][] >> rw[] >> fs[] >>
    qpat_assum`X has_type tty`mp_tac >>
    simp[Once has_type_cases]>>rw[]>>rw[])
  >- (
    simp[Once has_type_cases] >> rw[] >>
    rw[Once has_type_cases] >> metis_tac[] )
  >- (
    map_every qx_gen_tac[`ty`,`x`,`fty`,`ilist`] >>
    simp[Once has_type_cases] >> rw[] >>
    simp[Once has_type_cases] >>
    first_x_assum match_mp_tac >> simp[] >>
    simp[MEM_FILTER] >> rw[] >> TRY(metis_tac[]) >>
    simp[Once has_type_cases]))

val VSUBST_WELLTYPED = store_thm("VSUBST_WELLTYPED",
  ``∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm)``,
  metis_tac[VSUBST_HAS_TYPE,welltyped_def])

val VFREE_IN_VSUBST = store_thm("VFREE_IN_VSUBST",
  ``∀tm u uty ilist.
      VFREE_IN (Var u uty) (VSUBST ilist tm) ⇔
        ∃y ty. VFREE_IN (Var y ty) tm ∧
               VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))``,
  Induct >> simp[VFREE_IN_def,VSUBST_def] >- metis_tac[] >>
  map_every qx_gen_tac[`xty`,`x`,`u`,`uty`,`ilist`] >>
  qmatch_abbrev_tac`VFREE_IN vu (if p then Abs vx xty (VSUBST l1 tm) else Abs x xty (VSUBST l2 tm)) ⇔ q` >>
  qsuff_tac`VFREE_IN vu (Abs (if p then vx else x) xty (VSUBST (if p then l1 else l2) tm)) ⇔ q` >- metis_tac[] >>
  simp[VFREE_IN_def,Abbr`vu`] >>
  rw[] >- (
    simp[Abbr`q`,Abbr`l1`,REV_ASSOCD,Abbr`l2`,REV_ASSOCD_FILTER] >>
    EQ_TAC >- (
      rw[] >>
      pop_assum mp_tac >> rw[VFREE_IN_def] >> fs[] >>
      metis_tac[] ) >>
    qmatch_assum_abbrev_tac`Abbrev(vx = VARIANT t x xty)` >>
    qspecl_then[`t`,`x`,`xty`]mp_tac VARIANT_THM >> strip_tac >>
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
    simp[] >> rw[] >> fs[] >> fs[VFREE_IN_def] >>
    metis_tac[] ) >> fs[] >>
  Cases_on`VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))`>>simp[] >>
  Cases_on`Var u uty = Var y ty`>- (
    fs[] >> metis_tac[] ) >>
  Q.ISPECL_THEN[`ilist`,`Var y ty`,`Var y ty`]mp_tac REV_ASSOCD_MEM >>
  strip_tac >> fs[] >>
  fs[VFREE_IN_def] >>
  metis_tac[])

(* INST lemmas *)

val INST_CORE_HAS_TYPE = store_thm("INST_CORE_HAS_TYPE",
  ``∀n tm env tyin.
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
                              uty = TYPE_SUBST tyin oty))``,
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
        fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
        rw[] >> fs[] >>
        BasicProvers.EVERY_CASE_TAC >> fs[] >>
        rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
        metis_tac[VARIANT_THM] ) >>
      fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
      simp[Once has_type_cases] >>
      BasicProvers.EVERY_CASE_TAC >> fs[] >>
      rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
      rw[] >> fs[] >>
      metis_tac[VARIANT_THM,term_11]) >>
    strip_tac >> fs[] >- (
      rw[] >> fs[] >>
      fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
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
        first_x_assum(qspecl_then[`x'`,`ty'`,`x'`,`ty'`]mp_tac) >>
        simp[] >> BasicProvers.CASE_TAC >> simp[] >> strip_tac >> fs[] >>
        `VFREE_IN (Var x' (TYPE_SUBST tyin ty')) tm''` by metis_tac[] >>
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
    fs[Abbr`env''`,Abbr`env'`,REV_ASSOCD,Abbr`tm'`,VFREE_IN_VSUBST] >>
    BasicProvers.EVERY_CASE_TAC >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >> fs[] >>
    simp[Once has_type_cases] >>
    metis_tac[VARIANT_THM,term_11]))

val INST_CORE_NIL_IS_RESULT = store_thm("INST_CORE_NIL_IS_RESULT",
  ``∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm)``,
  rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  simp[] >> rw[] >> rw[] >> fs[REV_ASSOCD])

val INST_HAS_TYPE = store_thm("INST_HAS_TYPE",
  ``∀tm ty tyin ty'. tm has_type ty ∧ ty' = TYPE_SUBST tyin ty ⇒ INST tyin tm has_type ty'``,
  rw[INST_def] >>
  qspecl_then[`tyin`,`tm`]mp_tac INST_CORE_NIL_IS_RESULT >> rw[] >>
  qspecl_then[`sizeof tm`,`tm`,`[]`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
  `welltyped tm` by metis_tac[welltyped_def] >> fs[] >>
  rw[] >> fs[] >> metis_tac[WELLTYPED_LEMMA])

val INST_WELLTYPED = store_thm("INST_WELLTYPED",
  ``∀tm tyin.  welltyped tm ⇒ welltyped (INST tyin tm)``,
  metis_tac[INST_HAS_TYPE,WELLTYPED_LEMMA,WELLTYPED])

(* tyvars and tvars *)

val tyvars_ALL_DISTINCT = store_thm("tyvars_ALL_DISTINCT",
  ``∀ty. ALL_DISTINCT (tyvars ty)``,
  ho_match_mp_tac type_ind >>
  rw[tyvars_def] >>
  Induct_on`l` >> simp[] >>
  rw[ALL_DISTINCT_LIST_UNION])
val _ = export_rewrites["tyvars_ALL_DISTINCT"]

val tvars_ALL_DISTINCT = store_thm("tvars_ALL_DISTINCT",
  ``∀tm. ALL_DISTINCT (tvars tm)``,
  Induct >> simp[tvars_def,ALL_DISTINCT_LIST_UNION])
val _ = export_rewrites["tvars_ALL_DISTINCT"]

val tyvars_TYPE_SUBST = store_thm("tyvars_TYPE_SUBST",
  ``∀ty tyin. set (tyvars (TYPE_SUBST tyin ty)) =
      { v | ∃x. MEM x (tyvars ty) ∧ MEM v (tyvars (REV_ASSOCD (Tyvar x) tyin (Tyvar x))) }``,
  ho_match_mp_tac type_ind >> simp[tyvars_def] >>
  simp[EXTENSION,EVERY_MEM,MEM_FOLDR_LIST_UNION,PULL_EXISTS,MEM_MAP] >> rw[] >>
  metis_tac[] )

val tyvars_typeof_subset_tvars = store_thm("tyvars_typeof_subset_tvars",
  ``∀tm ty. tm has_type ty ⇒ set (tyvars ty) ⊆ set (tvars tm)``,
  ho_match_mp_tac has_type_ind >>
  simp[tvars_def] >>
  simp[SUBSET_DEF,MEM_LIST_UNION,tyvars_def] >>
  metis_tac[])

(* Equations *)

val EQUATION_HAS_TYPE_BOOL = store_thm("EQUATION_HAS_TYPE_BOOL",
  ``∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t)``,
  rw[equation_def] >> rw[Ntimes has_type_cases 3] >>
  metis_tac[WELLTYPED_LEMMA,WELLTYPED])

val welltyped_equation = store_thm("welltyped_equation",
  ``∀s t. welltyped (s === t) ⇔ s === t has_type Bool``,
  simp[EQUATION_HAS_TYPE_BOOL] >> simp[equation_def])

val typeof_equation = store_thm("typeof_equation",
  ``welltyped (l === r) ⇒ (typeof (l === r)) = Bool``,
  rw[welltyped_equation] >> imp_res_tac WELLTYPED_LEMMA >> rw[])

val vfree_in_equation = store_thm("vfree_in_equation",
  ``VFREE_IN v (s === t) ⇔ (v = Equal (typeof s)) ∨ VFREE_IN v s ∨ VFREE_IN v t``,
  rw[equation_def,VFREE_IN_def] >> metis_tac[])

(* type_ok *)

val type_ok_TYPE_SUBST = store_thm("type_ok_TYPE_SUBST",
  ``∀s tyin ty.
      type_ok s ty ∧
      EVERY (type_ok s) (MAP FST tyin)
    ⇒ type_ok s (TYPE_SUBST tyin ty)``,
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[type_ok_def] >> rw[EVERY_MAP,EVERY_MEM] >>
  fs[FORALL_PROD] >>
  metis_tac[REV_ASSOCD_MEM,type_ok_def])

val type_ok_TYPE_SUBST_imp = store_thm("type_ok_TYPE_SUBST_imp",
  ``∀s tyin ty. type_ok s (TYPE_SUBST tyin ty) ⇒
                ∀x. MEM x (tyvars ty) ⇒ type_ok s (TYPE_SUBST tyin (Tyvar x))``,
  gen_tac >> ho_match_mp_tac TYPE_SUBST_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,type_ok_def] >> rw[] >>
  fs[EVERY_MAP,EVERY_MEM] >> metis_tac[])

(* term_ok *)

val term_ok_welltyped = store_thm("term_ok_welltyped",
  ``∀sig t. term_ok sig t ⇒ welltyped t``,
  Cases >> Induct >> simp[term_ok_def])

val term_ok_type_ok = store_thm("term_ok_type_ok",
  ``∀sig t. is_std_sig sig ∧ term_ok sig t
          ⇒ type_ok (FST sig) (typeof t)``,
  Cases >> Induct >> simp[term_ok_def] >> rw[] >>
  fs[is_std_sig_def,type_ok_def])

val term_ok_equation = store_thm("term_ok_equation",
  ``is_std_sig sig ⇒
      (term_ok sig (s === t) ⇔
        term_ok sig s ∧ term_ok sig t ∧
        typeof t = typeof s)``,
  Cases_on`sig` >> rw[equation_def,term_ok_def] >>
  rw[EQ_IMP_THM] >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac term_ok_type_ok >>
  fs[is_std_sig_def,type_ok_def] >>
  qexists_tac`[(typeof s,Tyvar "A")]` >>
  rw[holSyntaxLibTheory.REV_ASSOCD_def])

val term_ok_VSUBST = store_thm("term_ok_VSUBST",
  ``∀sig tm ilist.
    term_ok sig tm ∧
    (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s')
    ⇒
    term_ok sig (VSUBST ilist tm)``,
  Cases >> Induct >> simp[VSUBST_def,term_ok_def] >- (
    ntac 2 gen_tac >> Induct >> simp[REV_ASSOCD,term_ok_def] >>
    Cases >> simp[REV_ASSOCD] >> rw[term_ok_def] >> metis_tac[])
  >- (
    rw[] >>
    imp_res_tac VSUBST_WELLTYPED >>
    imp_res_tac WELLTYPED >>
    imp_res_tac VSUBST_HAS_TYPE >>
    metis_tac[WELLTYPED_LEMMA] ) >>
  rw[term_ok_def] >>
  first_x_assum match_mp_tac >>
  rw[term_ok_def,MEM_FILTER] >>
  simp[Once has_type_cases])

val term_ok_INST_CORE = store_thm("term_ok_INST_CORE",
  ``∀sig env tyin tm.
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
      ⇒
      term_ok sig (RESULT (INST_CORE env tyin tm))``,
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
  simp[welltyped_def] >> PROVE_TAC[])

val term_ok_INST = store_thm("term_ok_INST",
  ``∀sig tyin tm.
    term_ok sig tm ∧
    EVERY (type_ok (FST sig)) (MAP FST tyin) ⇒
    term_ok sig (INST tyin tm)``,
  rw[INST_def] >>
  metis_tac[INST_CORE_NIL_IS_RESULT,term_ok_welltyped,term_ok_INST_CORE,MEM])

val term_ok_raconv = store_thm("term_ok_raconv",
  ``∀env tp. RACONV env tp ⇒
      ∀sig.
      EVERY (λ(s,s'). welltyped s ∧ welltyped s' ∧ typeof s = typeof s' ∧ type_ok (FST sig) (typeof s)) env ⇒
      term_ok sig (FST tp) ⇒ term_ok sig (SND tp)``,
  ho_match_mp_tac RACONV_strongind >>
  rw[] >> Cases_on`sig`>>fs[term_ok_def] >- (
    imp_res_tac ALPHAVARS_MEM >> fs[EVERY_MEM,FORALL_PROD] >>
    res_tac >> fs[] >> rw[] ) >>
  qspecl_then[`s1`,`env`,`s2`]mp_tac RACONV_welltyped >>
  qspecl_then[`t1`,`env`,`t2`]mp_tac RACONV_welltyped >>
  discharge_hyps >- (fs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >> strip_tac >>
  discharge_hyps >- (fs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >> strip_tac >>
  qspecl_then[`env`,`s1,s2`]mp_tac RACONV_TYPE >> simp[] >>
  discharge_hyps >- (fs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >> strip_tac >>
  qspecl_then[`env`,`t1,t2`]mp_tac RACONV_TYPE >> simp[] >>
  discharge_hyps >- (fs[EVERY_MEM,FORALL_PROD] >> metis_tac[]) >> strip_tac >>
  metis_tac[])

val term_ok_aconv = store_thm("term_ok_aconv",
  ``∀sig t1 t2. ACONV t1 t2 ∧ term_ok sig t1 ⇒ term_ok sig t2``,
  rw[ACONV_def] >> imp_res_tac term_ok_raconv >> fs[])

(* de Bruijn terms, for showing alpha-equivalence respect
   by substitution and instantiation *)

val _ = Hol_datatype` dbterm =
    dbVar of string => type
  | dbBound of num
  | dbConst of string => type
  | dbComb of dbterm => dbterm
  | dbAbs of type => dbterm`

(* bind a variable above a de Bruijn term *)

val bind_def = Define`
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty) = dbConst x ty ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)`
val _ = export_rewrites["bind_def"]

(* conversion into de Bruijn *)

val db_def = Define`
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty) = dbConst x ty ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs x ty tm) = dbAbs ty (bind (x,ty) 0 (db tm))`
val _ = export_rewrites["db_def"]

(* de Bruijn versions of VSUBST and VFREE_IN *)

val dbVSUBST_def = Define`
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty) = dbConst x ty ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)`
val _ = export_rewrites["dbVSUBST_def"]

val dbVFREE_IN_def = Define`
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty) ⇔ dbConst x ty = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)`
val _ = export_rewrites["dbVFREE_IN_def"]

val bind_not_free = store_thm("bind_not_free",
  ``∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t``,
  Induct >> simp[] >> rw[])

val bind_dbVSUBST = store_thm("bind_dbVSUBST",
  ``∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm)``,
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[] >- (
    `REV_ASSOCD (dbVar s t) ls (dbVar s t) = dbVar s t` by (
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[REV_ASSOCD_MEM,MEM_MAP] ) >>
    rw[] ) >>
  Induct_on`ls` >- simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >> strip_tac >>
  rw[] >> metis_tac[bind_not_free])

val bind_dbVSUBST_cons = store_thm("bind_dbVSUBST_cons",
  ``∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm)``,
  Induct >> simp[] >>
  CONV_TAC (RESORT_FORALL_CONV List.rev) >>
  rw[REV_ASSOCD] >>fs[] >- (
    Cases_on`z`>>fs[] ) >>
  Cases_on`z`>>fs[] >- (
    Cases_on`x`>>fs[] ) >>
  match_mp_tac bind_not_free >> fs[] )

val dbVSUBST_frees = store_thm("dbVSUBST_frees",
  ``∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm``,
  Induct >> simp[])

val dbVFREE_IN_bind = store_thm("dbVFREE_IN_bind",
  ``∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm``,
  Induct >> simp[] >> rw[] >- metis_tac[]
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]>>
    metis_tac[])
  >- (
    Cases_on`x`>>fs[]>>
    Cases_on`v`>>fs[]) >>
  Cases_on`v`>>fs[]>>
  Cases_on`x=dbVar q r`>>fs[])

val dbVFREE_IN_VFREE_IN = store_thm("dbVFREE_IN_VFREE_IN",
  ``∀tm x. dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm``,
  Induct >> simp[VFREE_IN_def] >- (
    ntac 2 gen_tac >> Cases >> simp[VFREE_IN_def] )
  >- (
    ntac 2 gen_tac >> Cases >> simp[VFREE_IN_def] ) >>
  simp[dbVFREE_IN_bind] >>
  ntac 2 gen_tac >> Cases >> simp[] >>
  metis_tac[] )

val MAP_db_FILTER_neq = store_thm("MAP_db_FILTER_neq",
  ``∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls)``,
  Induct >> simp[] >>
  Cases >> simp[] >>
  rw[] >-( Cases_on`r`>>fs[] ) >> fs[])

val REV_ASSOCD_MAP_db = store_thm("REV_ASSOCD_MAP_db",
  ``∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky))``,
  Induct >> simp[REV_ASSOCD] >>
  Cases >> simp[REV_ASSOCD] >>
  rw[] >> fs[] >- (
    Cases_on`r`>>fs[]>>rw[] ) >>
  `∃x ty. r = Var x ty` by metis_tac[] >> fs[] >>
  metis_tac[])

val dbVFREE_IN_dbVSUBST = store_thm("dbVFREE_IN_dbVSUBST",
  ``∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty))``,
  Induct >> simp[] >> rw[] >> metis_tac[])

val VSUBST_dbVSUBST = store_thm("VSUBST_dbVSUBST",
  ``∀tm ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm)``,
  Induct >- (
    simp[VSUBST_def] >>
    ntac 2 gen_tac >> Induct >>
    simp[REV_ASSOCD] >>
    Cases >> simp[REV_ASSOCD] >>
    strip_tac >>
    qpat_assum`p ⇒ qq`mp_tac >>
    discharge_hyps >- metis_tac[] >> strip_tac >>
    rw[] >> fs[] >>
    Cases_on`r`>>fs[] )
  >- simp[VSUBST_def]
  >- (
    simp[VSUBST_def] >>
    metis_tac[] ) >>
  rw[VSUBST_def] >>
  reverse(rw[]) >- (
    first_x_assum(qspec_then`ilist'`mp_tac) >>
    discharge_hyps >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[Abbr`t'`] >>
    qmatch_abbrev_tac`bind v n (dbVSUBST ls tt) = X` >>
    qspecl_then[`tt`,`v`,`n`,`ls`]mp_tac bind_dbVSUBST >>
    discharge_hyps >- (
      fs[MEM_MAP,EVERY_MEM,EXISTS_PROD,FORALL_PROD,Abbr`ls`,GSYM LEFT_FORALL_IMP_THM,Abbr`ilist'`,MEM_FILTER] >>
      qunabbrev_tac`v` >>
      conj_tac >- (
        gen_tac >> Cases >> simp[] >>
        metis_tac[] ) >>
      qx_gen_tac`k` >> strip_tac >> simp[] >>
      simp[MAP_db_FILTER_neq] >>
      simp[REV_ASSOCD_FILTER] >>
      qmatch_assum_rename_tac`k = db u`[] >>
      `∃x ty. u = Var x ty` by metis_tac[] >>
      qspecl_then[`ilist`,`x`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
      discharge_hyps >- metis_tac[] >>
      simp[] >> strip_tac >>
      BasicProvers.CASE_TAC >- (
        qmatch_abbrev_tac`¬dbVFREE_IN (dbVar s t) (db tz)` >>
        qspecl_then[`tz`,`Var s t`]mp_tac dbVFREE_IN_VFREE_IN >>
        simp[] >> strip_tac >>
        rpt BasicProvers.VAR_EQ_TAC >>
        spose_not_then strip_assume_tac >>
        metis_tac[REV_ASSOCD_MEM,VFREE_IN_def,dbVFREE_IN_VFREE_IN] ) >>
      fs[] ) >>
    rw[Abbr`ls`,Abbr`ilist'`] >>
    match_mp_tac dbVSUBST_frees >>
    simp[MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
    rw[Abbr`v`] >>
    fs[dbVFREE_IN_bind]) >>
  first_x_assum(qspec_then`ilist''`mp_tac) >>
  discharge_hyps >- (
    simp[Abbr`ilist''`,Abbr`ilist'`,MEM_FILTER] >>
    metis_tac[] ) >>
  qunabbrev_tac`ilist''` >> rw[] >>
  qmatch_abbrev_tac`bind v n (dbVSUBST ((zz,x)::ls) tt) = X` >>
  qmatch_assum_rename_tac`Abbrev(z = VARIANT ta s tb)`[] >>
  qspecl_then[`tt`,`v`,`(s,tb)`,`n`,`ls`]mp_tac bind_dbVSUBST_cons >>
  simp[Abbr`v`] >>
  discharge_hyps >- (
    qunabbrev_tac`zz` >>
    simp[dbVFREE_IN_dbVSUBST] >>
    simp[dbVFREE_IN_bind] >>
    rpt gen_tac >>
    qspecl_then[`ilist'`,`y`,`ty`]mp_tac REV_ASSOCD_MAP_db >>
    discharge_hyps >- (
      simp[Abbr`ilist'`,MEM_FILTER] >>
      metis_tac[] ) >>
    rw[] >>
    qmatch_assum_abbrev_tac`tv = db tu` >>
    qspecl_then[`tu`,`Var z tb`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`tm`,`Var y ty`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[Abbr`tt`] >>
    spose_not_then strip_assume_tac >>
    qsuff_tac`VFREE_IN (Var z tb) ta`>-
      metis_tac[VARIANT_THM] >>
    simp[Abbr`tu`,Abbr`ta`,VFREE_IN_VSUBST] >>
    metis_tac[] ) >>
  rw[] >>
  simp[Abbr`ls`] >>
  match_mp_tac dbVSUBST_frees >>
  simp[Abbr`ilist'`,MAP_db_FILTER_neq,REV_ASSOCD_FILTER] >>
  rw[Abbr`x`] >>
  fs[dbVFREE_IN_bind])

(* de Bruijn version of INST *)

val dbINST_def = Define`
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)`
val _ = export_rewrites["dbINST_def"]

val dbINST_bind = store_thm("dbINST_bind",
  ``∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm)``,
  Induct >> simp[] >>
  Cases_on`v`>>simp[] >>
  rpt strip_tac >>
  BasicProvers.CASE_TAC >> fs[] >>
  BasicProvers.CASE_TAC >> fs[])

val dbVSUBST_nil = store_thm("dbVSUBST_nil",
  ``∀tm. dbVSUBST [] tm = tm``,
  Induct >> simp[REV_ASSOCD])
val _ = export_rewrites["dbVSUBST_nil"]

val INST_CORE_dbINST = store_thm("INST_CORE_dbINST",
  ``∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm)``,
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
    qmatch_assum_rename_tac`typeof t1 = Fun (typeof t2) rty`[] >>
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
  simp[INST_CORE_def] >>
  rw[] >> fs[] >>
  qmatch_assum_rename_tac`welltyped tm`[] >>
  qmatch_assum_abbrev_tac`IS_RESULT X` >>
  Cases_on`X`>>
  pop_assum(assume_tac o SYM o SIMP_RULE std_ss [markerTheory.Abbrev_def]) >> fs[] >- (
    qmatch_abbrev_tac`bind (x,TYPE_SUBST tyin ty) 0 (db tt) = X` >>
    pop_assum mp_tac >> ntac 3 (pop_assum kall_tac) >> strip_tac >>
    qspecl_then[`db tm`,`x,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
    discharge_hyps >- (
      qx_gen_tac`ty2` >>
      qspecl_then[`tm`,`Var x ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
      rw[] >>
      qmatch_assum_abbrev_tac`INST_CORE env' tyin tm = Y` >>
      qspecl_then[`sizeof tm`,`tm`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
      discharge_hyps >- (
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
    discharge_hyps >- metis_tac[] >>
    rw[] ) >>
  qmatch_abbrev_tac`bind (z,TYPE_SUBST tyin ty) 0 (db tt) = dbINST tyin (bind (x,ty) 0 (db tm))` >>
  ntac 3 (pop_assum kall_tac) >>
  qspecl_then[`db tm`,`z,ty`,`x,ty`,`0`,`[]`]mp_tac bind_dbVSUBST_cons >>
  discharge_hyps >- (
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
  discharge_hyps >- (
    simp[Abbr`env'`] >>
    metis_tac[] ) >>
  rw[] >>
  qspecl_then[`tm`,`[Var z ty,Var x ty]`]mp_tac VSUBST_dbVSUBST >>
  simp[] >> disch_then(strip_assume_tac o SYM) >> simp[] >>
  qspecl_then[`db tv`,`z,ty`,`0`,`tyin`]mp_tac dbINST_bind >>
  discharge_hyps >- (
    simp[] >>
    qx_gen_tac`ty2` >>
    qspecl_then[`tv`,`Var z ty2`]mp_tac dbVFREE_IN_VFREE_IN >>
    rw[] >>
    qspecl_then[`sizeof tv`,`tv`,`env'`,`tyin`]mp_tac INST_CORE_HAS_TYPE >>
    discharge_hyps >- (
      simp[Abbr`env'`] >>
      metis_tac[] ) >>
    simp[] >>
    simp[Abbr`env'`,REV_ASSOCD] >>
    strip_tac >>
    last_x_assum(qspecl_then[`z`,`ty2`]mp_tac) >>
    simp[] ) >>
  simp[])

val INST_dbINST = store_thm("INST_dbINST",
  ``∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm)``,
  rw[INST_def] >>
  imp_res_tac INST_CORE_NIL_IS_RESULT >>
  pop_assum(qspec_then`tyin`strip_assume_tac) >>
  Cases_on`INST_CORE [] tyin tm`>>fs[] >>
  qspecl_then[`tm`,`tyin`,`[]`,`a`]mp_tac INST_CORE_dbINST >>
  simp[])

(* conversion into de Bruijn given an environment of already bound variables *)

val dbterm_def = Define`
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty) = dbConst s ty) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs x ty t) = dbAbs ty (dbterm ((x,ty)::env) t))`
val _ = export_rewrites["dbterm_def"]

val bind_list_aux_def = Define`
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)`
val _ = export_rewrites["bind_list_aux_def"]

val bind_list_aux_clauses = store_thm("bind_list_aux_clauses",
  ``(∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm))``,
  rpt conj_tac >> Induct >> simp[])

val dbterm_bind = store_thm("dbterm_bind",
  ``∀tm env. dbterm env tm = bind_list_aux 0 env (db tm)``,
  Induct >> simp[bind_list_aux_clauses] >>
  gen_tac >>
  Q.SPEC_TAC(`0`,`n`) >>
  Induct_on`env` >> simp[find_index_def] >>
  Cases >> simp[] >>
  rw[] >> rw[bind_list_aux_clauses])

val dbterm_db = store_thm("dbterm_db",
  ``∀tm. dbterm [] tm = db tm``,
  rw[dbterm_bind])

(* alpha-equivalence on de Bruijn terms *)

val dbterm_RACONV = store_thm("dbterm_RACONV",
  ``∀t1 env1 t2 env2. dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2)``,
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
  ntac 3 gen_tac >>
  Cases >> simp[RACONV] >- (
    gen_tac >> BasicProvers.CASE_TAC >> simp[] ) >>
  rw[] >> res_tac >> fs[])

val RACONV_dbterm = store_thm("RACONV_dbterm",
  ``∀env tp. RACONV env tp ⇒
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp)``,
  ho_match_mp_tac RACONV_ind >> rw[] >> rw[] >>
  TRY (
    first_x_assum match_mp_tac >>
    rw[] >> rw[] ) >>
  Induct_on`env` >> simp[ALPHAVARS_def] >>
  rw[] >> rw[] >- rw[find_index_def] >> fs[] >>
  simp[find_index_def] >>
  `∃x ty. FST h = Var x ty` by metis_tac[] >>
  `∃y tz. SND h = Var y tz` by metis_tac[] >>
  simp[] >>
  simp[Once find_index_shift_0] >>
  simp[Once find_index_shift_0,SimpRHS] >>
  rpt BasicProvers.CASE_TAC >> fs[] >> rw[] >> fs[])

val dbterm_ACONV = store_thm("dbterm_ACONV",
  ``∀t1 t2. ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2``,
  rw[ACONV_def,EQ_IMP_THM] >- (
    qspecl_then[`[]`,`t1,t2`]mp_tac RACONV_dbterm >> simp[] ) >>
  qspecl_then[`t1`,`[]`,`t2`,`[]`]mp_tac dbterm_RACONV >>
  simp[])

val ACONV_db = store_thm("ACONV_db",
  ``∀t1 t2. ACONV t1 t2 ⇔ db t1 = db t2``,
  metis_tac[dbterm_ACONV,dbterm_db])

(* respect of alpha-equivalence by VSUBST and INST follows *)

val ACONV_VSUBST = store_thm("ACONV_VSUBST",
  ``∀t1 t2 ilist.
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2)``,
  rw[ACONV_db] >> metis_tac[VSUBST_dbVSUBST])

val ACONV_INST = store_thm("ACONV_INST",
  ``∀t1 t2 tyin. welltyped t1 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2)``,
  rw[] >> imp_res_tac ACONV_welltyped >>
  fs[ACONV_db] >> imp_res_tac INST_dbINST >> rw[] )

(* list of bound variable names in a term *)

val bv_names_def = Define`
  bv_names (Var _ _) = [] ∧
  bv_names (Const _ _) = [] ∧
  bv_names (Comb s t) = bv_names s ++ bv_names t ∧
  bv_names (Abs x ty t) = x::bv_names t`
val _ = export_rewrites["bv_names_def"]

(* Simpler versions (non-capture-avoiding) of substitution and instantiation.
   We do the semantics proofs on these and then use the fact that it is
   alpha-equivalence respecting, and suitable equivalent term always exists
   (see below). *)

val simple_subst_def = Define`
  (simple_subst ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (simple_subst ilist (Const x ty) = Const x ty) ∧
  (simple_subst ilist (Comb t1 t2) = Comb (simple_subst ilist t1) (simple_subst ilist t2)) ∧
  (simple_subst ilist (Abs x ty tm) =
    Abs x ty (simple_subst (FILTER (λ(s',s). (s ≠ Var x ty)) ilist) tm))`
val _ = export_rewrites["simple_subst_def"]

val simple_inst_def = Define`
  simple_inst tyin (Var x ty) = Var x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Const x ty) = Const x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs x ty t) = Abs x (TYPE_SUBST tyin ty) (simple_inst tyin t)`
val _ = export_rewrites["simple_inst_def"]

val VSUBST_simple_subst = store_thm("VSUBST_simple_subst",
  ``∀tm ilist. DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty)
               ⇒ VSUBST ilist tm = simple_subst ilist tm``,
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
  metis_tac[])

val INST_CORE_simple_inst = store_thm("INST_CORE_simple_inst",
  ``∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty)
      ⇒ INST_CORE env tyin tm = Result (simple_inst tyin tm)``,
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
    rw[INST_CORE_def] >>
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
  rw[INST_CORE_def] >>
  fs[] >>
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
  fs[])

val INST_simple_inst = store_thm("INST_simple_inst",
  ``∀tyin tm.
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm}
      ⇒
      INST tyin tm = simple_inst tyin tm``,
  rw[INST_def] >>
  qspecl_then[`[]`,`tyin`,`tm`]mp_tac INST_CORE_simple_inst >>
  simp[])

val simple_subst_has_type = store_thm("simple_subst_has_type",
  ``∀tm ty.
      tm has_type ty ⇒
      ∀subst.
        EVERY (λ(s',s). s' has_type typeof s) subst ⇒
        simple_subst subst tm has_type ty``,
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
  fs[EVERY_FILTER,EVERY_MEM])

val simple_inst_has_type = store_thm("simple_inst_has_type",
  ``∀tm tyin. welltyped tm ⇒ simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm))``,
  Induct >> rw[] >> rw[Once has_type_cases] >> fs[] >> metis_tac[] )

(* rename bound variables from a source of names *)

val rename_bvars_def = Define`
  rename_bvars names env (Var s ty) = (names, Var (REV_ASSOCD (s,ty) env s) ty) ∧
  rename_bvars names env (Const s ty) = (names, Const s ty) ∧
  (rename_bvars names env (Comb t1 t2) =
     let (names,t1) = rename_bvars names env t1 in
     let (names,t2) = rename_bvars names env t2 in
     (names, Comb t1 t2)) ∧
  (rename_bvars [] env (Abs s ty tm) =
     let (names, tm) = rename_bvars [] env tm in
     (names, Abs s ty tm)) ∧
  (rename_bvars (s'::names) env (Abs s ty tm) =
     let (names,tm) = rename_bvars names ((s',(s,ty))::env) tm in
     (names, Abs s' ty tm))`

val FST_rename_bvars = store_thm("FST_rename_bvars",
  ``∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names)``,
  ho_match_mp_tac (theorem"rename_bvars_ind") >>
  simp[rename_bvars_def] >>
  rw[UNCURRY] >> rw[] >>
  Cases_on`rename_bvars names env tm` >> fs[] >>
  fsrw_tac[ARITH_ss][] >>
  REWRITE_TAC[Once arithmeticTheory.ADD_SYM] >>
  match_mp_tac rich_listTheory.DROP_DROP >>
  simp[])

val rename_bvars_RACONV = store_thm("rename_bvars_RACONV",
  ``∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧
    DISJOINT (set (MAP FST env ++ names)) (set (MAP (FST o SND) env ++ bv_names tm)) ∧
    DISJOINT (set (MAP FST env ++ names)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
    ALL_DISTINCT (MAP FST env ++ names)
    ⇒ RACONV (MAP (λ(s',(s,ty)). (Var s ty, Var s' ty)) env) (tm, SND (rename_bvars names env tm))``,
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
    rw[UNCURRY] >>
    simp[RACONV] >>
    conj_tac >> first_x_assum (match_mp_tac o MP_CANON) >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    TRY (
      qexists_tac`SND (rename_bvars names env tm)`>>simp[] >>
      qspecl_then[`names`,`env`,`tm`]mp_tac FST_rename_bvars >>
      discharge_hyps >- DECIDE_TAC >> strip_tac >>
      first_assum (assume_tac o Q.AP_TERM`LENGTH`) >>
      fs[LENGTH_DROP] >>
      `LENGTH (bv_names tm) ≤ LENGTH names` by DECIDE_TAC >>
      conj_tac >- DECIDE_TAC >>
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
    conj_tac >- DECIDE_TAC >> metis_tac[]) >>
  rw[UNCURRY] >>
  rw[RACONV] >>
  first_x_assum match_mp_tac >>
  simp[] >>
  fs[IN_DISJOINT,ALL_DISTINCT_APPEND] >>
  rfs[] >> metis_tac[])

val rename_bvars_ACONV = store_thm("rename_bvars_ACONV",
  ``∀names tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
    DISJOINT (set names) {x | MEM x (bv_names tm) ∨ ∃ty. VFREE_IN (Var x ty) tm}
    ⇒
    ACONV tm (SND (rename_bvars names [] tm))``,
  rw[ACONV_def] >>
  qspecl_then[`names`,`[]`,`tm`]mp_tac rename_bvars_RACONV >>
  simp[] >> disch_then match_mp_tac >>
  fs[IN_DISJOINT] >> metis_tac[])

(* appropriate fresh term for using the simple functions above *)

val fresh_def = new_specification("fresh_def",["fresh"],
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])

val fresh_union = store_thm("fresh_union",
  ``FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t``,
  metis_tac[fresh_def,FINITE_UNION,IN_UNION])

val fresh_names_exist = store_thm("fresh_names_exist",
  ``∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s``,
  gen_tac >> Induct >> strip_tac
  >- (qexists_tac`[]`>>simp[]) >> rw[] >> fs[] >>
  qexists_tac`fresh (s ∪ set names)::names` >>
  simp[fresh_union])

val bv_names_rename_bvars = store_thm("bv_names_rename_bvars",
  ``∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ⇒
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names``,
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
  rw[UNCURRY])

(* various rewrites for FINITE sets to make this go through *)

val FINITE_VFREE_IN = store_thm("FINITE_VFREE_IN",
  ``∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm}``,
  Induct >> simp[] >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_assum`FINITE s1`mp_tac >>
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
  metis_tac[])
val _ = export_rewrites["FINITE_VFREE_IN"]

val FINITE_VFREE_IN_2 = store_thm("FINITE_VFREE_IN_2",
  ``∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm}``,
  Induct >> simp[] >- (
    rw[] >>
    qmatch_abbrev_tac`FINITE x` >>
    qsuff_tac`∃y. x = {y}`>-metis_tac[FINITE_SING] >>
    rw[EXTENSION,Abbr`x`,FORALL_PROD,EXISTS_PROD] >>
    metis_tac[] )
  >- (
    qmatch_assum_abbrev_tac`FINITE s1` >>
    qpat_assum`FINITE s1`mp_tac >>
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
  metis_tac[])
val _ = export_rewrites["FINITE_VFREE_IN_2"]

val FINITE_VFREE_IN_list = store_thm("FINITE_VFREE_IN_list",
  ``∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls}``,
  Induct >> simp[] >> rw[] >>
  qmatch_assum_abbrev_tac`FINITE s` >>
  qmatch_abbrev_tac`FINITE t` >>
  `t = s ∪ {x | ∃ty. VFREE_IN (Var x ty) h}` by (
    simp[EXTENSION,Abbr`t`,Abbr`s`] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_UNION])
val _ = export_rewrites["FINITE_VFREE_IN_list"]

val FINITE_MEM_Var = store_thm("FINITE_MEM_Var",
  ``∀ls. FINITE {(x,ty) | MEM (Var x ty) ls}``,
  Induct >> simp[] >>
  Cases >> simp[] >>
  qmatch_assum_abbrev_tac`FINITE P` >>
  qmatch_abbrev_tac`FINITE Q` >>
  `Q = (s,t) INSERT P` by (
    simp[Abbr`P`,Abbr`Q`,EXTENSION] >>
    metis_tac[] ) >>
  pop_assum SUBST1_TAC >>
  simp[FINITE_INSERT] )
val _ = export_rewrites["FINITE_MEM_Var"]

val fresh_term_def = new_specification("fresh_term_def",["fresh_term"],
  prove(``∃f. ∀s tm. FINITE s ⇒
                     ACONV tm (f s tm) ∧
                     ALL_DISTINCT (bv_names (f s tm)) ∧
                     DISJOINT (set (bv_names (f s tm))) s``,
    simp[GSYM SKOLEM_THM] >> rw[RIGHT_EXISTS_IMP_THM] >>
    qspecl_then[`s ∪ set (bv_names tm) ∪ {x | ∃ty. VFREE_IN (Var x ty) tm}`,`LENGTH (bv_names tm)`]mp_tac fresh_names_exist >> rw[] >>
    qexists_tac`SND (rename_bvars names [] tm)` >>
    conj_tac >- (
      match_mp_tac rename_bvars_ACONV >>
      fs[IN_DISJOINT] >>
      metis_tac[] ) >>
    qspecl_then[`names`,`[]`,`tm`]mp_tac bv_names_rename_bvars >>
    simp[TAKE_LENGTH_ID_rwt] >>
    fs[IN_DISJOINT] >>
    metis_tac[]))

(* provable terms are ok and of type bool *)

val proves_theory_ok = store_thm("proves_theory_ok",
  ``∀thyh c. thyh |- c ⇒ theory_ok (FST thyh)``,
  ho_match_mp_tac proves_ind >> rw[])

val theory_ok_sig = store_thm("theory_ok_sig",
  ``∀thy. theory_ok thy ⇒ is_std_sig (sigof thy)``,
  Cases >> rw[theory_ok_def])

val proves_term_ok = store_thm("proves_term_ok",
  ``∀thyh c. thyh |- c ⇒
      EVERY (λp. term_ok (sigof (FST thyh)) p ∧ p has_type Bool) (c::(SND thyh))``,
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
    match_mp_tac EVERY_TERM_UNION >>
    simp[EVERY_FILTER] >> fs[EVERY_MEM] ) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation] >>
    imp_res_tac ACONV_TYPE >> imp_res_tac ACONV_welltyped >> fs[] >-
      metis_tac[WELLTYPED_LEMMA,WELLTYPED,term_ok_welltyped] >>
    match_mp_tac EVERY_TERM_UNION >> fs[] ) >>
  strip_tac >- (
    rw[term_ok_VSUBST,EVERY_MAP] >> fs[EVERY_MEM] >>
    metis_tac[term_ok_VSUBST,VSUBST_HAS_TYPE] ) >>
  strip_tac >- (
    rw[term_ok_INST,EVERY_MAP] >> fs[EVERY_MEM] >>
    metis_tac[SIMP_RULE(srw_ss())[EVERY_MAP,EVERY_MEM]term_ok_INST,INST_HAS_TYPE,TYPE_SUBST_Bool] ) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    fs[term_ok_equation,term_ok_def] >>
    metis_tac[EVERY_TERM_UNION]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac term_ok_welltyped >>
    imp_res_tac theory_ok_sig >>
    rw[term_ok_equation,term_ok_def]) >>
  strip_tac >- (
    rw[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac proves_theory_ok >>
    imp_res_tac theory_ok_sig >>
    imp_res_tac term_ok_welltyped >>
    fs[term_ok_equation] >>
    fs[EQUATION_HAS_TYPE_BOOL] >>
    imp_res_tac ACONV_TYPE >>
    simp[] >>
    match_mp_tac EVERY_TERM_UNION >> fs[] ) >>
  rw[theory_ok_def])

(* extension is transitive *)

val extends_trans = store_thm("extends_trans",
  ``∀c1 c2 c3. c1 extends c2 ∧ c2 extends c3 ⇒ c1 extends c3``,
  rw[extends_def] >> metis_tac[RTC_TRANSITIVE,transitive_def])

(* signature extensions preserve ok *)

val type_ok_extend = store_thm("type_ok_extend",
  ``∀t tyenv tyenv'.
    tyenv ⊑ tyenv' ∧
    type_ok tyenv t ⇒
    type_ok tyenv' t``,
  ho_match_mp_tac type_ind >>
  rw[type_ok_def,EVERY_MEM] >>
  res_tac >>
  imp_res_tac FLOOKUP_SUBMAP)

val term_ok_extend = store_thm("term_ok_extend",
  ``∀t tyenv tmenv tyenv' tmenv'.
    tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ∧
    term_ok (tyenv,tmenv) t ⇒
    term_ok (tyenv',tmenv') t``,
  Induct >> simp[term_ok_def] >> rw[] >>
  imp_res_tac type_ok_extend >>
  imp_res_tac FLOOKUP_SUBMAP >>
  metis_tac[])

val is_std_sig_extend = store_thm("is_std_sig_extend",
  ``∀tyenv tmenv tyenv' tmenv'.
    is_std_sig (tyenv,tmenv) ∧ tyenv ⊑ tyenv' ∧ tmenv ⊑ tmenv' ⇒
    is_std_sig (tyenv',tmenv')``,
  rw[is_std_sig_def] >> imp_res_tac FLOOKUP_SUBMAP)

(* updates preserve ok *)

val updates_theory_ok = store_thm("updates_theory_ok",
  ``∀upd ctxt. upd updates ctxt ⇒ theory_ok (thyof ctxt) ⇒ theory_ok (thyof (upd::ctxt))``,
  ho_match_mp_tac updates_ind >>
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
      simp[Abbr`ilist`,MEM_MAP,PULL_EXISTS,UNCURRY,Once has_type_cases,term_ok_def] >>
      conj_tac >- metis_tac[term_ok_extend,SUBMAP_REFL] >>
      simp[Abbr`tms'`,FLOOKUP_FUNION,ALOOKUP_MAP,FORALL_PROD] >> rw[] >>
      imp_res_tac ALOOKUP_ALL_DISTINCT_MEM >> rw[] >>
      fs[EVERY_MEM,term_ok_def,FORALL_PROD] >>
      metis_tac[is_instance_refl] ) >>
    match_mp_tac VSUBST_HAS_TYPE >>
    simp[Abbr`ilist`,MEM_MAP,PULL_EXISTS,UNCURRY,Once has_type_cases] ) >>
  strip_tac >- (
    rw[conexts_of_upd_def] >>
    fs[theory_ok_def] >>
    `tysof ctxt ⊑ tysof ctxt |+ (name,arity)` by simp[] >>
    metis_tac[is_std_sig_extend,term_ok_extend,type_ok_extend,SUBMAP_REFL] ) >>
  rw[conexts_of_upd_def] >>
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
  `name ∉ {"fun";"bool"}` by (
    fs[is_std_sig_def] >>
    imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  pop_assum mp_tac >> simp[] >> strip_tac >>
  Q.PAT_ABBREV_TAC`eq1 = l1 === r1` >>
  Q.PAT_ABBREV_TAC`eq2 = l2 === r` >>
  Q.PAT_ABBREV_TAC`eq3 = l3 === r3` >>
  qpat_assum`X has_type Y`mp_tac >>
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
  metis_tac[term_ok_extend])

val extends_ind = store_thm("extends_ind",
  ``∀P. (∀upd ctxt. upd updates ctxt ∧ P ctxt ⇒ P (upd::ctxt)) ⇒
    ∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ P ctxt1 ⇒ P ctxt2``,
  gen_tac >> strip_tac >>
  simp[extends_def] >>
  CONV_TAC SWAP_FORALL_CONV >>
  ho_match_mp_tac RTC_INDUCT >>
  rw[] >> first_x_assum match_mp_tac >>
  rw[])

val extends_theory_ok = store_thm("extends_theory_ok",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ theory_ok (thyof ctxt1) ⇒ theory_ok (thyof ctxt2)``,
  ho_match_mp_tac extends_ind >> metis_tac[updates_theory_ok])

(* init_ctxt ok *)

val init_theory_ok = store_thm("init_theory_ok",
  ``theory_ok (thyof init_ctxt)``,
  rw[theory_ok_def,init_ctxt_def,type_ok_def,FLOOKUP_UPDATE,conexts_of_upd_def] >>
  rw[is_std_sig_def,FLOOKUP_UPDATE])

(* is_std_sig is preserved *)

val is_std_sig_extends = store_thm("is_std_sig_extends",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒ is_std_sig (sigof ctxt1) ⇒ is_std_sig (sigof ctxt2)``,
  ho_match_mp_tac extends_ind >>
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  ho_match_mp_tac updates_ind >>
  rw[is_std_sig_def,FLOOKUP_UPDATE,FLOOKUP_FUNION] >>
  TRY BasicProvers.CASE_TAC >>
  imp_res_tac ALOOKUP_MEM >>
  fs[MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[] )

(* recover constant definition as a special case of specification *)

val _ = Parse.overload_on("ConstDef",``λx t. ConstSpec [(x,t)] (Var x (typeof t) === t)``)

val ConstDef_updates = store_thm("ConstDef_updates",
  ``∀name tm ctxt.
    theory_ok (thyof ctxt) ∧
    term_ok (sigof ctxt) tm ∧
    name ∉ FDOM (tmsof ctxt) ∧
    CLOSED tm ∧
    set (tvars tm) ⊆ set (tyvars (typeof tm))
    ⇒ ConstDef name tm updates ctxt``,
  rw[] >>
  match_mp_tac(List.nth(CONJUNCTS updates_rules,2)) >>
  simp[EVERY_MAP] >> fs[SUBSET_DEF] >>
  simp[vfree_in_equation] >> fs[CLOSED_def] >>
  match_mp_tac(List.nth(CONJUNCTS proves_rules,1)) >>
  imp_res_tac term_ok_welltyped >>
  imp_res_tac theory_ok_sig >>
  imp_res_tac term_ok_type_ok >>
  simp[EQUATION_HAS_TYPE_BOOL,term_ok_equation,term_ok_def])

(* extensions have all distinct names *)

val updates_ALL_DISTINCT = store_thm("updates_ALL_DISTINCT",
  ``∀upd ctxt. upd updates ctxt ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (type_list (upd::ctxt)))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt)) ⇒
       ALL_DISTINCT (MAP FST (const_list (upd::ctxt))))``,
  ho_match_mp_tac updates_ind >> simp[] >>
  rw[ALL_DISTINCT_APPEND,MAP_MAP_o,combinTheory.o_DEF,UNCURRY,ETA_AX])

val extends_ALL_DISTINCT = store_thm("extends_ALL_DISTINCT",
  ``∀ctxt1 ctxt2. ctxt2 extends ctxt1 ⇒
      (ALL_DISTINCT (MAP FST (type_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (type_list ctxt2))) ∧
      (ALL_DISTINCT (MAP FST (const_list ctxt1)) ⇒
       ALL_DISTINCT (MAP FST (const_list ctxt2)))``,
  simp[IMP_CONJ_THM,FORALL_AND_THM] >> conj_tac >>
  ho_match_mp_tac extends_ind >>
  METIS_TAC[updates_ALL_DISTINCT])

val init_ALL_DISTINCT = store_thm("init_ALL_DISTINCT",
  ``ALL_DISTINCT (MAP FST (const_list init_ctxt)) ∧
    ALL_DISTINCT (MAP FST (type_list init_ctxt))``,
  EVAL_TAC)

val _ = export_theory()
