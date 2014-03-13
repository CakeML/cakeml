open HolKernel boolLib bossLib lcsymtacs relationTheory listTheory pred_setTheory finite_mapTheory
open miscLib holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory
val _ = temp_tight_equality()
val _ = new_theory"holBool"

val _ = Parse.overload_on("Truth",``Const "T" Bool``)
val _ = Parse.overload_on("And",``λp1 p2. Comb (Comb (Const "/\\" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Implies",``λp1 p2. Comb (Comb (Const "==>" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Forall",``λx ty p. Comb (Const "!" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("Exists",``λx ty p. Comb (Const "?" (Fun (Fun ty Bool) Bool)) (Abs x ty p)``)
val _ = Parse.overload_on("Or",``λp1 p2. Comb (Comb (Const "\\/" (Fun Bool (Fun Bool Bool))) p1) p2``)
val _ = Parse.overload_on("Falsity",``Const "F" Bool``)
val _ = Parse.overload_on("Not",``λp. Comb (Const "~" (Fun Bool Bool)) p``)

val _ = Parse.temp_overload_on("p",``Var "p" Bool``)
val _ = Parse.temp_overload_on("Absp",``Abs "p" Bool``)
val _ = Parse.temp_overload_on("FAp",``Forall "p" Bool``)
val _ = Parse.temp_overload_on("q",``Var "q" Bool``)
val _ = Parse.temp_overload_on("Absq",``Abs "q" Bool``)
val _ = Parse.temp_overload_on("FAq",``Forall "q" Bool``)
val _ = Parse.temp_overload_on("r",``Var "r" Bool``)
val _ = Parse.temp_overload_on("FAr",``Forall "r" Bool``)
val _ = Parse.temp_overload_on("f",``Var "f" (Fun Bool (Fun Bool Bool))``)
val _ = Parse.temp_overload_on("Absf",``Abs "f" (Fun Bool (Fun Bool Bool))``)
val _ = Parse.temp_overload_on("A",``Tyvar "A"``)
val _ = Parse.temp_overload_on("P",``Var "P" (Fun A Bool)``)
val _ = Parse.temp_overload_on("AbsP",``Abs "P" (Fun A Bool)``)
val _ = Parse.temp_overload_on("x",``Var "x" A``)
val _ = Parse.temp_overload_on("Absx",``Abs "x" A``)
val _ = Parse.temp_overload_on("FAx",``Forall "x" A``)
val Truth_def = ``Absp p === Absp p``
val And_def = ``Absp (Absq (Absf (Comb (Comb f p) q) === Absf (Comb (Comb f Truth) Truth)))``
val Implies_def = ``Absp (Absq (And p q === p))``
val Forall_def = ``AbsP (P === Absx Truth)``
val mk_bool_ctxt_def = Define`
  mk_bool_ctxt ctxt =
    ConstDef "~" (Absp (Implies p Falsity)) ::
    ConstDef "F" (FAp p) ::
    ConstDef "\\/" (Absp (Absq (FAr (Implies (Implies p r) (Implies (Implies q r) r))))) ::
    ConstDef "?" (AbsP (FAq (Implies (FAx (Implies (Comb P x) q)) q))) ::
    ConstDef "!" ^Forall_def ::
    ConstDef "==>" ^Implies_def ::
    ConstDef "/\\" ^And_def ::
    ConstDef "T"  ^Truth_def ::
    ctxt`

(* bool is a good extension *)

val tyvar_inst_exists = prove(
  ``∃i. ty = REV_ASSOCD (Tyvar a) i b``,
  qexists_tac`[(ty,Tyvar a)]` >>
  rw[REV_ASSOCD])

val term_ok_clauses = store_thm("term_ok_clauses",
  ``is_std_sig sig ⇒
    (term_ok sig (Var s ty) ⇔ type_ok (tysof sig) ty) ∧
    (type_ok (tysof sig) (Tyvar a) ⇔ T) ∧
    (type_ok (tysof sig) Bool ⇔ T) ∧
    (type_ok (tysof sig) (Fun ty1 ty2) ⇔ type_ok (tysof sig) ty1 ∧ type_ok (tysof sig) ty2) ∧
    (term_ok sig (Comb t1 t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ welltyped (Comb t1 t2)) ∧
    (term_ok sig (t1 === t2) ⇔ term_ok sig t1 ∧ term_ok sig t2 ∧ typeof t1 = typeof t2) ∧
    (term_ok sig (Abs s ty t) ⇔ type_ok (tysof sig) ty ∧ term_ok sig t)``,
  rw[term_ok_def,type_ok_def,term_ok_equation] >>
  fs[is_std_sig_def] >> metis_tac[])

val ConstDef_tac =
  pop_assum(assume_tac o REWRITE_RULE[GSYM extends_def]) >>
  match_mp_tac ConstDef_updates >>
  conj_asm1_tac >- (
    match_mp_tac (MP_CANON extends_theory_ok) >>
    qexists_tac`ctxt` >> simp[] ) >>
  conj_asm1_tac >- (
    qmatch_abbrev_tac`term_ok sig tm` >>
    `is_std_sig sig` by (
      imp_res_tac theory_ok_sig >>
      ntac 2 (pop_assum mp_tac) >>
      simp_tac bool_ss [pairTheory.FST] ) >>
    qunabbrev_tac`tm` >>
    asm_simp_tac pure_ss [term_ok_clauses,WELLTYPED_CLAUSES,typeof_def] >>
    simp_tac pure_ss [term_ok_def] >>
    simp_tac (srw_ss()) [Abbr`sig`,FLOOKUP_UPDATE,type_ok_def] >>
    simp[type_ok_def,typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL,tyvar_inst_exists] >>
    pop_assum mp_tac >>
    EVAL_TAC >>
    simp_tac bool_ss [GSYM alistTheory.alist_to_fmap_def,alistTheory.ALOOKUP_EQ_FLOOKUP] >>
    NO_TAC) >>
  conj_tac >- (
    qpat_assum`DISJOINT X Y`mp_tac >>
    rpt (pop_assum kall_tac) >>
    rw[IN_DISJOINT] >> metis_tac[] ) >>
  conj_tac >- (
    simp[CLOSED_def,vfree_in_equation] >>
    rpt (pop_assum kall_tac) >>
    metis_tac[] ) >>
  simp[tvars_def,tyvars_def,equation_def,SUBSET_DEF] >>
  rpt (pop_assum kall_tac) >>
  metis_tac[]

fun pull_tac () =
  REWRITE_TAC[Once RTC_CASES1] >> disj2_tac >>
  BETA_TAC >> REWRITE_TAC[CONS_11] >> simp_tac bool_ss [] >>
  conj_asm2_tac

val bool_extends = store_thm("bool_extends",
  ``∀ctxt.
      theory_ok (thyof ctxt) ∧
      DISJOINT (FDOM (tmsof ctxt)) {"T";"F";"==>";"/\\";"\\/";"~";"!";"?"} ⇒
      mk_bool_ctxt ctxt extends ctxt``,
  REWRITE_TAC[mk_bool_ctxt_def] >>
  REWRITE_TAC[extends_def] >>
  ntac 2 strip_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  pull_tac() >- ConstDef_tac >>
  rw[Once RTC_CASES1])

val bool_extends_init = store_thm("bool_extends_init",
  ``mk_bool_ctxt init_ctxt extends init_ctxt``,
  match_mp_tac bool_extends >> simp[init_theory_ok] >>
  simp[init_ctxt_def])

val is_bool_sig_def = Define`
  is_bool_sig (sig:sig) ⇔
  is_std_sig sig ∧
  FLOOKUP (tmsof sig) "T" = SOME Bool ∧
  FLOOKUP (tmsof sig) "F" = SOME Bool ∧
  FLOOKUP (tmsof sig) "==>" = SOME (Fun Bool (Fun Bool Bool)) ∧
  FLOOKUP (tmsof sig) "/\\" = SOME (Fun Bool (Fun Bool Bool)) ∧
  FLOOKUP (tmsof sig) "\\/" = SOME (Fun Bool (Fun Bool Bool)) ∧
  FLOOKUP (tmsof sig) "~" = SOME (Fun Bool Bool) ∧
  FLOOKUP (tmsof sig) "!" = SOME (Fun (Fun A Bool) Bool) ∧
  FLOOKUP (tmsof sig) "?" = SOME (Fun (Fun A Bool) Bool)`

val bool_has_bool_sig = store_thm("bool_has_bool_sig",
  ``∀ctxt. is_std_sig (sigof ctxt)
  ⇒ is_bool_sig (sigof (mk_bool_ctxt ctxt))``,
  rw[is_bool_sig_def] >- (
    fs[is_std_sig_def,mk_bool_ctxt_def,FLOOKUP_UPDATE] ) >>
  EVAL_TAC)

val is_bool_sig_std = store_thm("is_bool_sig_std",
  ``is_bool_sig sig ⇒ is_std_sig sig``, rw[is_bool_sig_def])

(* Boolean terms are ok *)
val bool_term_ok = store_thm("bool_term_ok",
  ``∀sig. is_bool_sig sig ⇒
    term_ok sig Truth ∧
    (∀p1 p2. term_ok sig (And p1 p2) ⇔ term_ok sig p1 ∧ term_ok sig p2 ∧ typeof p1 = Bool ∧ typeof p2 = Bool) ∧
    (∀p1 p2. term_ok sig (Implies p1 p2) ⇔ term_ok sig p1 ∧ term_ok sig p2 ∧ typeof p1 = Bool ∧ typeof p2 = Bool) ∧
    (∀z ty p. term_ok sig (Forall z ty p) ⇔ type_ok (tysof sig) ty ∧ term_ok sig p ∧ typeof p = Bool) ∧
    (∀z ty p. term_ok sig (Exists z ty p) ⇔ type_ok (tysof sig) ty ∧ term_ok sig p ∧ typeof p = Bool) ∧
    (∀p1 p2. term_ok sig (Or p1 p2) ⇔ term_ok sig p1 ∧ term_ok sig p2 ∧ typeof p1 = Bool ∧ typeof p2 = Bool) ∧
    term_ok sig Falsity ∧
    (∀p. term_ok sig (Not p) ⇔ term_ok sig p ∧ typeof p = Bool)``,
  rw[] >> imp_res_tac is_bool_sig_std >> rw[term_ok_clauses] >>
  rw[term_ok_def] >> fs[is_bool_sig_def] >> rw[term_ok_clauses,tyvar_inst_exists] >>
  PROVE_TAC[term_ok_welltyped])

open holSemanticsTheory holSemanticsExtraTheory setSpecTheory

val bool_sig_instances = store_thm("bool_sig_instances",
  ``is_bool_sig sig ⇒
    instance sig (i:'U interpretation) "T" Bool = (K (tmaof i "T" (K ARB))) ∧
    instance sig i "F" Bool = (K (tmaof i "F" (K ARB))) ∧
    instance sig i "==>" (Fun Bool (Fun Bool Bool)) = (K (tmaof i "==>" (K ARB))) ∧
    instance sig i "/\\" (Fun Bool (Fun Bool Bool)) = (K (tmaof i "/\\" (K ARB))) ∧
    instance sig i "\\/" (Fun Bool (Fun Bool Bool)) = (K (tmaof i "\\/" (K ARB))) ∧
    instance sig i "~" (Fun Bool Bool) = (K (tmaof i "~" (K ARB))) ∧
    instance sig i "!" (Fun (Fun A Bool) Bool) = (λτ. tmaof i "!" (λx. if x = "A" then τ x else ARB)) ∧
    instance sig i "?" (Fun (Fun A Bool) Bool) = (λτ. tmaof i "?" (λx. if x = "A" then τ x else ARB))``,
  rw[is_bool_sig_def] >> imp_res_tac identity_instance >> rw[FUN_EQ_THM] >>
  rpt AP_TERM_TAC >> rw[FUN_EQ_THM,tyvars_def])

val mem = ``mem:'U->'U->bool``

val _ = Parse.temp_overload_on("Boolrel",
  ``λr.  (Abstract boolset (Funspace boolset boolset)
           (λp. (Abstract boolset boolset
              (λq. Boolean (r (p = True) (q = True))))))``)

val is_bool_interpretation_def = xDefine"is_bool_interpretation"`
  is_bool_interpretation0 ^mem i ⇔
    is_std_interpretation i ∧
    tmaof i interprets "T" on ∅ as K True ∧
    tmaof i interprets "/\\" on ∅ as K (Boolrel $/\) ∧
    tmaof i interprets "==>" on ∅ as K (Boolrel $==>) ∧
    tmaof i interprets "!" on {"A"} as
       (λτ. Abstract (Funspace (τ"A") boolset) boolset
              (λP. Boolean (∀x. x <: (τ"A") ⇒ Holds P x))) ∧
    tmaof i interprets "?" on {"A"} as
       (λτ. Abstract (Funspace (τ"A") boolset) boolset
              (λP. Boolean (∃x. x <: (τ"A") ∧ Holds P x))) ∧
    tmaof i interprets "\\/" on ∅ as K (Boolrel $\/) ∧
    tmaof i interprets "F" on ∅ as K False ∧
    tmaof i interprets "~" on ∅ as K (Abstract boolset boolset (λp. Boolean (p ≠ True)))`
val _ = Parse.overload_on("is_bool_interpretation",``is_bool_interpretation0 ^mem``)

val apply_abstract_matchable = store_thm("apply_abstract_matchable",
  ``∀f x s t u. x <: s ∧ f x <: t ∧ is_set_theory ^mem ∧ f x = u ⇒ Abstract s t f ' x = u``,
  metis_tac[apply_abstract])

val boolrel_in_funspace = prove(
  ``is_set_theory ^mem ⇒ Boolrel R <: Funspace boolset (Funspace boolset boolset)``,
  strip_tac >> match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset] )
val _ = augment_srw_ss[rewrites[boolrel_in_funspace]]

fun init_tac q =
  fs[models_def] >>
  first_x_assum(qspec_then q mp_tac) >>
  discharge_hyps >- (unabbrev_all_tac >> EVAL_TAC) >>
  simp[satisfies_def] >>
  qspecl_then[`tysof sig`,`tyaof i`]mp_tac (UNDISCH valuation_exists) >>
  discharge_hyps >- fs[is_interpretation_def] >> strip_tac >>
  disch_then(qspec_then`v`mp_tac) >> simp[] >>
  `is_structure sig i v` by fs[is_structure_def] >>
  Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
  `term_ok sig eq` by (
    unabbrev_all_tac >>
    simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] >>
    simp[term_ok_def] >>
    qpat_assum`is_std_sig X`mp_tac >>
    EVAL_TAC >> simp_tac bool_ss [GSYM alistTheory.alist_to_fmap_def,alistTheory.ALOOKUP_EQ_FLOOKUP,is_instance_refl]) >>
    simp[termsem_equation,Abbr`eq`,boolean_eq_true] >>
    simp[termsem_def,typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
    simp[bool_sig_instances,interprets_def,combinTheory.K_DEF] >> rw[]

(*
val bool_has_bool_interpretation = store_thm("bool_has_bool_interpretation",
  ``is_set_theory ^mem ⇒
    ∀ctxt i. theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
             i models (thyof (mk_bool_ctxt ctxt)) ⇒
             is_bool_interpretation i``,
  rw[] >>
  simp[is_bool_interpretation_def] >>
  conj_asm1_tac >- fs[models_def] >>
  qabbrev_tac`ctx = mk_bool_ctxt ctxt` >>
  qabbrev_tac`sig = sigof ctx` >>
  imp_res_tac theory_ok_sig >>
  `is_bool_sig sig` by (
    unabbrev_all_tac >>
    match_mp_tac bool_has_bool_sig >>
    pop_assum mp_tac >> EVAL_TAC ) >>
  `FLOOKUP (tysof sig) "bool" = SOME 0` by (
    qpat_assum`is_std_sig sig` mp_tac >>
    simp[is_std_sig_def,Abbr`sig`,Abbr`ctx`]) >>
  `FLOOKUP (tysof sig) "fun" = SOME 2` by (
    qpat_assum`is_std_sig sig` mp_tac >>
    simp[is_std_sig_def,Abbr`sig`,Abbr`ctx`]) >>
  conj_asm1_tac >- (
    fs[models_def] >>
    first_x_assum(qspec_then`Const "T" Bool === ^Truth_def`mp_tac) >>
    discharge_hyps >- (unabbrev_all_tac >> EVAL_TAC) >>
    simp[satisfies_def] >>
    qspecl_then[`tysof sig`,`tyaof i`]mp_tac (UNDISCH valuation_exists) >>
    discharge_hyps >- fs[is_interpretation_def] >> strip_tac >>
    disch_then(qspec_then`v`mp_tac) >> simp[] >>
    `is_structure sig i v` by fs[is_structure_def] >>
    `term_ok sig (Truth === Absp p === Absp p)` by (
      asm_simp_tac (srw_ss()) [term_ok_clauses,typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL,bool_term_ok] ) >>
    `term_ok sig (Absp p === Absp p)` by (
      simp[term_ok_equation,term_ok_clauses] ) >>
    rfs[Abbr`sig`,termsem_equation,boolean_eq_true,termsem_def] >>
    simp[bool_sig_instances,interprets_def] >>
    rw[combinTheory.K_DEF] >>
    `τ = λx. ARB` by simp[FUN_EQ_THM] >>
    simp[boolean_def]) >>
  conj_asm1_tac >- (
    init_tac `Const "/\\" (Fun Bool (Fun Bool Bool)) === ^And_def` >>
    `τ = λx. ARB` by simp[FUN_EQ_THM] >> rw[] >> ntac 2 (pop_assum kall_tac) >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    imp_res_tac typesem_Fun >>
    qx_gen_tac`b1` >> strip_tac >> simp[] >>
    conj_asm1_tac >- (
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      qx_gen_tac`b2` >> strip_tac >> simp[] >>
      Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
      Q.PAT_ABBREV_TAC`vv = X:'U valuation` >>
      `term_ok sig eq` by (
        unabbrev_all_tac >>
        simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] ) >>
      `is_structure sig i vv` by (
        fs[is_structure_def,Abbr`vv`,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
        rw[] >> metis_tac[] ) >>
      qunabbrev_tac`eq` >>
      simp[termsem_equation,boolean_in_boolset] ) >>
    conj_asm1_tac >- (
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[boolean_in_boolset] ) >>
    match_mp_tac(UNDISCH abstract_eq) >>
    qx_gen_tac`b2` >> simp[] >> strip_tac >>
    simp[boolean_in_boolset] >>
    Q.PAT_ABBREV_TAC`vv = X:'U valuation` >>
    `is_structure sig i vv` by (
      fs[is_structure_def,Abbr`vv`,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> metis_tac[] ) >>
    Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
    `term_ok sig eq` by (
      unabbrev_all_tac >>
      simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] ) >>
    qunabbrev_tac`eq` >>
    simp[termsem_equation,boolean_in_boolset] >>
    simp[termsem_def] >>
    simp[combinTheory.APPLY_UPDATE_THM,Abbr`vv`] >>
    simp[bool_sig_instances] >> fs[interprets_def] >>
    rw[boolean_def] >>
    qmatch_assum_abbrev_tac`f1 = f2` >>
    `f1 ' (Boolrel $/\) = False` by (
      qpat_assum`f1 = f2`kall_tac >>
      simp[Abbr`f1`] >>
      match_mp_tac apply_abstract_matchable >> simp[] >>
      conj_asm1_tac >- (
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[] >>
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[] ) >>
      `Boolrel $/\ ' b1 = Abstract boolset boolset (λb2. Boolean (b1 = True ∧ b2 = True))` by (
        match_mp_tac apply_abstract_matchable >>
        simp[] ) >>
      simp[] >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_def,mem_boolset] ) >>
    `f2 ' (Boolrel $/\) = True` by (
      simp[Abbr`f2`] >>
      match_mp_tac apply_abstract_matchable >> simp[] >>
      conj_asm1_tac >- (
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[mem_boolset] >>
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[mem_boolset] ) >>
      `Boolrel $/\ ' True = Abstract boolset boolset (λb2. Boolean (b2 = True))` by (
        match_mp_tac apply_abstract_matchable >> simp[mem_boolset] >>
        match_mp_tac (UNDISCH abstract_in_funspace) >>
        simp[boolean_in_boolset]) >>
      simp[] >>
      match_mp_tac apply_abstract_matchable >>
    simp[boolean_def,mem_boolset] ) >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    init_tac `Const "==>" (Fun Bool (Fun Bool Bool)) === ^Implies_def` >>
    `τ = λx. ARB` by simp[FUN_EQ_THM] >> rw[] >> ntac 2 (pop_assum kall_tac) >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    imp_res_tac typesem_Fun >>
    qx_gen_tac`b1` >> strip_tac >> simp[] >>
    conj_asm1_tac >- (
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      qx_gen_tac`b2` >> strip_tac >> simp[] >>
      Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
      Q.PAT_ABBREV_TAC`vv = X:'U valuation` >>
      `term_ok sig eq` by (
        unabbrev_all_tac >>
        simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] ) >>
      `is_structure sig i vv` by (
        fs[is_structure_def,Abbr`vv`,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
        rw[] >> metis_tac[] ) >>
      qunabbrev_tac`eq` >>
      simp[termsem_equation,boolean_in_boolset] ) >>
    conj_asm1_tac >- (
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[boolean_in_boolset] ) >>
    match_mp_tac(UNDISCH abstract_eq) >>
    qx_gen_tac`b2` >> simp[] >> strip_tac >>
    simp[boolean_in_boolset] >>
    Q.PAT_ABBREV_TAC`vv = X:'U valuation` >>
    `is_structure sig i vv` by (
      fs[is_structure_def,Abbr`vv`,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> metis_tac[] ) >>
    Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
    `term_ok sig eq` by (
      unabbrev_all_tac >>
      simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] ) >>
    qunabbrev_tac`eq` >>
    simp[termsem_equation,boolean_in_boolset] >>
    simp[termsem_def] >>
    simp[combinTheory.APPLY_UPDATE_THM,Abbr`vv`] >>
    simp[bool_sig_instances] >> fs[interprets_def] >>
    `Boolrel $/\ ' b1 = Abstract boolset boolset (λb2. Boolean (b1 = True ∧ b2 = True))` by (
      match_mp_tac apply_abstract_matchable >> simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >> simp[boolean_in_boolset]) >>
    `Boolrel $/\ ' b1 ' b2 =  Boolean (b1 = True ∧ b2 = True)` by (
      simp[] >>
      match_mp_tac apply_abstract_matchable >> simp[boolean_in_boolset] ) >>
    simp[boolean_def] >> rw[] >> fs[] >>
    metis_tac[mem_boolset] ) >>
  conj_asm1_tac >- (
    init_tac `Const "!" (Fun (Fun A Bool) Bool) === ^Forall_def` >>
    qmatch_assum_abbrev_tac `tmaof i name ff = yy` >>
    `τ = ff` by (
      simp[FUN_EQ_THM,Abbr`ff`] >> rw[]

    `τ = λx. ARB` by simp[FUN_EQ_THM] >> rw[] >> ntac 2 (pop_assum kall_tac) >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    imp_res_tac typesem_Fun >>
*)


(*

val Exists_has_type_Bool = store_thm("Exists_has_type_Bool",
  ``∀x ty p. Exists x ty p has_type Bool ⇔ p has_type Bool``,
  rpt (rw[Once has_type_cases]))

val And_has_type_Bool = store_thm("And_has_type_Bool",
  ``∀p q. And p q has_type Bool ⇔ p has_type Bool ∧ q has_type Bool``,
  rpt (rw[Once has_type_cases]))

val One_One_has_type_Bool = store_thm("One_One_has_type_Bool",
  ``∀f. One_One f has_type Bool ⇔ welltyped f``,
  ntac 2 (rw[Once has_type_cases]) >> rw[WELLTYPED])

val Onto_has_type_Bool = store_thm("Onto_has_type_Bool",
  ``∀f. Onto f has_type Bool ⇔ welltyped f``,
  ntac 2 (rw[Once has_type_cases]) >> rw[WELLTYPED])

val Not_has_type_Bool = store_thm("Not_has_type_Bool",
  ``∀p. Not p has_type Bool ⇔ p has_type Bool``,
  rpt(rw[Once has_type_cases]))

val tyvar_inst_exists_2 = prove(
  ``x1 ≠ x2 ⇒
    ∃i. ty1 = REV_ASSOCD (Tyvar x1) i y1 ∧
        ty2 = REV_ASSOCD (Tyvar x2) i y2``,
  rw[] >>
  qexists_tac`[(ty1,Tyvar x1);(ty2,Tyvar x2)]` >>
  rw[REV_ASSOCD])
*)

val _ = export_theory()
