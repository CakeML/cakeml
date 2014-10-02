open HolKernel boolLib bossLib lcsymtacs relationTheory listTheory pred_setTheory finite_mapTheory
open miscLib holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory holSemanticsTheory holSemanticsExtraTheory setSpecTheory
val _ = temp_tight_equality()
val _ = new_theory"holBool"

val mem = ``mem:'U->'U->bool``

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

val sigs = [is_true_sig_def, is_false_sig_def, is_implies_sig_def, is_and_sig_def,
            is_or_sig_def, is_not_sig_def, is_forall_sig_def, is_exists_sig_def]

val bool_sig_instances = store_thm("bool_sig_instances",
  ``is_bool_sig sig ⇒
    instance (tmsof sig) (i:'U interpretation) "T" Bool = (K (tmaof i "T" [])) ∧
    instance (tmsof sig) i "F" Bool = (K (tmaof i "F" [])) ∧
    instance (tmsof sig) i "==>" (Fun Bool (Fun Bool Bool)) = (K (tmaof i "==>" [])) ∧
    instance (tmsof sig) i "/\\" (Fun Bool (Fun Bool Bool)) = (K (tmaof i "/\\" [])) ∧
    instance (tmsof sig) i "\\/" (Fun Bool (Fun Bool Bool)) = (K (tmaof i "\\/" [])) ∧
    instance (tmsof sig) i "~" (Fun Bool Bool) = (K (tmaof i "~" [])) ∧
    instance (tmsof sig) i "!" (Fun (Fun A Bool) Bool) = (λτ. tmaof i "!" [τ "A"]) ∧
    instance (tmsof sig) i "?" (Fun (Fun A Bool) Bool) = (λτ. tmaof i "?" [τ "A"])``,
  rw[is_bool_sig_def] >> fs sigs >> imp_res_tac identity_instance >> rw[FUN_EQ_THM] >>
  rpt AP_TERM_TAC >> rw[FUN_EQ_THM,tyvars_def] >> EVAL_TAC)

val Boolrel_def = xDefine"Boolrel"`
  Boolrel0 ^mem R =
      (Abstract boolset (Funspace boolset boolset)
           (λp. (Abstract boolset boolset
              (λq. Boolean (R (p = True) (q = True))))))`
val _ = Parse.overload_on("Boolrel",``Boolrel0 ^mem``)

val is_true_interpretation_def = xDefine"is_true_interpretation"`
  is_true_interpretation0 ^mem γ ⇔ (γ:'U tmass) interprets "T" on [] as K True`
val _ = Parse.overload_on("is_true_interpretation",``is_true_interpretation0 ^mem``)

val is_and_interpretation_def = xDefine"is_and_interpretation"`
  is_and_interpretation0 ^mem γ ⇔ γ interprets "/\\" on [] as K (Boolrel $/\)`
val _ = Parse.overload_on("is_and_interpretation",``is_and_interpretation0 ^mem``)

val is_implies_interpretation_def = xDefine"is_implies_interpretation"`
  is_implies_interpretation0 ^mem γ ⇔ γ interprets "==>" on [] as K (Boolrel $==>)`
val _ = Parse.overload_on("is_implies_interpretation",``is_implies_interpretation0 ^mem``)

val is_forall_interpretation_def = xDefine"is_forall_interpretation"`
  is_forall_interpretation0 ^mem γ ⇔ γ
    interprets "!" on ["A"] as
       (λl. Abstract (Funspace (HD l) boolset) boolset
              (λP. Boolean (∀x. x <: (HD l) ⇒ Holds P x)))`
val _ = Parse.overload_on("is_forall_interpretation",``is_forall_interpretation0 ^mem``)

val is_exists_interpretation_def = xDefine"is_exists_interpretation"`
  is_exists_interpretation0 ^mem γ ⇔ γ
    interprets "?" on ["A"] as
       (λl. Abstract (Funspace (HD l) boolset) boolset
              (λP. Boolean (∃x. x <: (HD l) ∧ Holds P x)))`
val _ = Parse.overload_on("is_exists_interpretation",``is_exists_interpretation0 ^mem``)

val is_or_interpretation_def = xDefine"is_or_interpretation"`
  is_or_interpretation0 ^mem γ ⇔ γ interprets "\\/" on [] as K (Boolrel $\/)`
val _ = Parse.overload_on("is_or_interpretation",``is_or_interpretation0 ^mem``)

val is_false_interpretation_def = xDefine"is_false_interpretation"`
  is_false_interpretation0 ^mem γ ⇔ (γ:'U tmass) interprets "F" on [] as K False`
val _ = Parse.overload_on("is_false_interpretation",``is_false_interpretation0 ^mem``)

val is_not_interpretation_def = xDefine"is_not_interpretation"`
  is_not_interpretation0 ^mem γ ⇔ γ interprets "~" on [] as K (Abstract boolset boolset (λp. Boolean (p ≠ True)))`
val _ = Parse.overload_on("is_not_interpretation",``is_not_interpretation0 ^mem``)

val ints = [is_true_interpretation_def,is_and_interpretation_def,is_implies_interpretation_def,
            is_forall_interpretation_def,is_exists_interpretation_def,is_or_interpretation_def,
            is_false_interpretation_def,is_not_interpretation_def]

val is_bool_interpretation_def = xDefine"is_bool_interpretation"`
  is_bool_interpretation0 ^mem i ⇔
    is_std_interpretation i ∧
    is_true_interpretation (tmaof i) ∧
    is_and_interpretation (tmaof i) ∧
    is_implies_interpretation (tmaof i) ∧
    is_forall_interpretation (tmaof i) ∧
    is_exists_interpretation (tmaof i) ∧
    is_or_interpretation (tmaof i) ∧
    is_false_interpretation (tmaof i) ∧
    is_not_interpretation (tmaof i)`
val _ = Parse.overload_on("is_bool_interpretation",``is_bool_interpretation0 ^mem``)

val boolrel_in_funspace = store_thm("boolrel_in_funspace",
  ``is_set_theory ^mem ⇒ Boolrel R <: Funspace boolset (Funspace boolset boolset)``,
  rw[Boolrel_def] >> match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset] )
val _ = export_rewrites["boolrel_in_funspace"]

val Defs = [TrueDef_def, AndDef_def, ImpliesDef_def, ForallDef_def, ExistsDef_def, OrDef_def, FalseDef_def, NotDef_def]

fun init_tac q =
  fs[models_def] >>
  first_x_assum(qspec_then q mp_tac) >>
  discharge_hyps >- (unabbrev_all_tac >> EVAL_TAC) >>
  simp[satisfies_def] >>
  strip_tac >>
  simp[interprets_def] >>
  qx_gen_tac`τ`>>strip_tac >>
  qspecl_then[`tysof sig`,`tyaof i`,`τ`]mp_tac (UNDISCH term_valuation_exists) >>
  discharge_hyps >- fs[is_interpretation_def] >> strip_tac >>
  first_x_assum(qspec_then`(τ,σ)`mp_tac) >> simp[] >>
  qabbrev_tac`v = (τ,σ)` >>
  `is_structure sig i v` by fs[is_structure_def] >>
  REWRITE_TAC Defs >>
  Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
  `term_ok sig eq` by (
    unabbrev_all_tac >>
    simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] >>
    simp[term_ok_def] >>
    qpat_assum`is_std_sig X`mp_tac >>
    EVAL_TAC >> simp_tac bool_ss [GSYM alistTheory.alist_to_fmap_def,alistTheory.ALOOKUP_EQ_FLOOKUP,is_instance_refl]) >>
  simp[SIMP_RULE std_ss [] termsem_equation,Abbr`eq`,boolean_eq_true] >>
  simp[termsem_def,typeof_equation,welltyped_equation,EQUATION_HAS_TYPE_BOOL] >>
  simp[bool_sig_instances,interprets_def,combinTheory.K_DEF] >> rw[]

val apply_abstract_tac = rpt ( (
    qmatch_abbrev_tac`Abstract AA BB CC ' DD <: EE` >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`AA` >>
    map_every qunabbrev_tac[`AA`,`BB`,`CC`,`DD`,`EE`] >>
    rw[boolean_in_boolset]
    ) ORELSE (
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[boolean_in_boolset]
    ) ORELSE (
    qmatch_abbrev_tac`Boolrel RR ' BB ' CC <: boolset` >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`boolset` >>
    map_every qunabbrev_tac[`RR`,`BB`,`CC`] >>
    rw[boolean_in_boolset]
    ) ORELSE (
    qmatch_abbrev_tac`Boolrel RR ' BB <: FF` >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`boolset` >>
    map_every qunabbrev_tac[`RR`,`BB`,`FF`] >>
    rw[boolean_in_boolset]
    )) >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    HINT_EXISTS_TAC >> rw[]

val apply_boolrel = store_thm("apply_boolrel",
  ``is_set_theory ^mem ⇒
    ∀b1 b2 b3. b1 <: boolset ∧ b2 <: boolset ∧ (b3 = Boolean (R (b1 = True) (b2 = True))) ⇒
      Boolrel R ' b1 ' b2 = b3 ``,
  rw[] >>
  `Boolrel R ' b1 = Abstract boolset boolset (λb2. Boolean (R (b1 = True) (b2 = True)))` by (
    rw[Boolrel_def] >>
    match_mp_tac apply_abstract_matchable >>
    rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[boolean_in_boolset] ) >>
  rw[] >>
  match_mp_tac apply_abstract_matchable >>
  rw[boolean_in_boolset] )

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
  simp ints >>
  conj_asm1_tac >- (
    init_tac`Const "T" Bool === TrueDef` >>
    `term_ok sig TrueDef` by (
      simp[term_ok_equation,term_ok_clauses,TrueDef_def] ) >>
    fs[TrueDef_def] >>
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_eq_true,termsem_def]) >>
  conj_asm1_tac >- (
    init_tac `Const "/\\" (Fun Bool (Fun Bool Bool)) === AndDef` >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[Boolrel_def] >>
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
      simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset] ) >>
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
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset] >>
    simp[termsem_def] >>
    simp[combinTheory.APPLY_UPDATE_THM,Abbr`vv`] >>
    simp[bool_sig_instances] >> fs[interprets_def] >>
    last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac >>
    rw[boolean_def] >>
    qmatch_assum_abbrev_tac`f1 = f2` >>
    `f1 ' (Boolrel $/\) = False` by (
      qpat_assum`f1 = f2`kall_tac >>
      simp[Abbr`f1`,Boolrel_def] >>
      match_mp_tac apply_abstract_matchable >> simp[] >>
      conj_tac >- apply_abstract_tac >>
      conj_asm1_tac >- (
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[] >>
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[] >>
        apply_abstract_tac) >>
      `Boolrel $/\ ' b1 = Abstract boolset boolset (λb2. Boolean (b1 = True ∧ b2 = True))` by (
        simp[Boolrel_def] >>
        match_mp_tac apply_abstract_matchable >>
        simp[] ) >>
      simp[GSYM Boolrel_def] >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_def,mem_boolset] ) >>
    `f2 ' (Boolrel $/\) = True` by (
      simp[Abbr`f2`] >>
      match_mp_tac apply_abstract_matchable >> simp[] >>
      conj_asm1_tac >- (
        simp[Boolrel_def] >>
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[mem_boolset] >>
        match_mp_tac (UNDISCH apply_in_rng) >> qexists_tac`boolset` >> simp[mem_boolset] >>
        apply_abstract_tac) >>
      `Boolrel $/\ ' True = Abstract boolset boolset (λb2. Boolean (b2 = True))` by (
        simp[Boolrel_def] >>
        match_mp_tac apply_abstract_matchable >> simp[mem_boolset] >>
        match_mp_tac (UNDISCH abstract_in_funspace) >>
        simp[boolean_in_boolset]) >>
      simp[] >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_def,mem_boolset] ) >>
    metis_tac[] ) >>
  conj_asm1_tac >- (
    init_tac `Const "==>" (Fun Bool (Fun Bool Bool)) === ImpliesDef` >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[Boolrel_def] >>
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
      simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset] ) >>
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
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset] >>
    simp[termsem_def] >>
    simp[combinTheory.APPLY_UPDATE_THM,Abbr`vv`] >>
    simp[bool_sig_instances] >> fs[interprets_def] >>
    ntac 2(last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
    `Boolrel $/\ ' b1 = Abstract boolset boolset (λb2. Boolean (b1 = True ∧ b2 = True))` by (
      simp[Boolrel_def] >>
      match_mp_tac apply_abstract_matchable >> simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >> simp[boolean_in_boolset]) >>
    `Boolrel $/\ ' b1 ' b2 =  Boolean (b1 = True ∧ b2 = True)` by (
      simp[Boolrel_def] >>
      match_mp_tac apply_abstract_matchable >> simp[boolean_in_boolset] ) >>
    simp[boolean_def] >> rw[] >> fs[] >>
    metis_tac[mem_boolset] ) >>
  conj_asm1_tac >- (
    init_tac `Const "!" (Fun (Fun A Bool) Bool) === ForallDef` >>
    `τ = tyvof v` by simp[Abbr`v`] >> fs[] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    imp_res_tac typesem_Fun >> simp[typesem_def] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    qx_gen_tac`pp` >> strip_tac >>
    simp[boolean_in_boolset] >>
    Q.PAT_ABBREV_TAC`vv = X:'U valuation` >>
    Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
    `is_structure sig i vv` by (
      fs[is_structure_def,Abbr`vv`,is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> metis_tac[typesem_def] ) >>
    `term_ok sig eq` by (
      unabbrev_all_tac >>
      simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] ) >>
    qunabbrev_tac`eq` >>
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset] >>
    simp[termsem_def] >>
    simp[combinTheory.APPLY_UPDATE_THM,Abbr`vv`] >>
    simp[bool_sig_instances] >> fs[interprets_def] >>
    ntac 3(last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
    simp[typesem_def] >>
    Q.PAT_ABBREV_TAC`aa:'U = X "A"` >>
    qspecl_then[`pp`,`aa`,`boolset`]mp_tac(UNDISCH in_funspace_abstract) >>
    discharge_hyps >- (fs[is_type_valuation_def,Abbr`aa`] >> metis_tac[boolean_in_boolset]) >>
    disch_then(qx_choose_then`pf`strip_assume_tac) >> simp[] >>
    `∀x. x <: aa ⇒ Abstract aa boolset (λm. True) ' x = True` by (
      rw[] >> match_mp_tac apply_abstract_matchable >> rw[mem_boolset] ) >>
    `∀x. x <: aa ⇒ Abstract aa boolset pf ' x = pf x` by (
      rw[] >> match_mp_tac apply_abstract_matchable >> rw[mem_boolset] ) >>
    rw[boolean_def,holds_def] >> fs[] >- metis_tac[mem_boolset] >>
    qmatch_assum_abbrev_tac`f1 ≠ f2` >>
    qsuff_tac`f1 = f2`>-rw[]>>unabbrev_all_tac >>
    match_mp_tac (UNDISCH abstract_eq) >>
    simp[mem_boolset] ) >>
  conj_asm1_tac >- (
    init_tac `Const "?" (Fun (Fun A Bool) Bool) === ExistsDef` >>
    `τ = tyvof v` by simp[Abbr`v`] >> fs[] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    imp_res_tac typesem_Fun >> simp[typesem_def] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    qx_gen_tac`pp` >> strip_tac >>
    simp[boolean_in_boolset] >>
    qspecl_then[`tmsof sig`,`i`,`"!"`,`Fun (Fun Bool Bool) Bool`,`Fun (Fun A Bool) Bool`,`[(Bool,A)]`]mp_tac instance_def >>
    discharge_hyps >- (fs[is_bool_sig_def,is_exists_sig_def,is_forall_sig_def] >> EVAL_TAC) >>
    simp[] >> disch_then kall_tac >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def,REV_ASSOCD] >>
    fs[interprets_def] >>
    qpat_assum`∀t. is_type_valuation t ⇒ Z`(fn th => assume_tac th >> (qspec_then`("A" =+ boolset)τ`mp_tac) th) >>
    discharge_hyps >- (
      fs[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >> rw[] >>
      metis_tac[boolean_in_boolset] ) >>
    simp[combinTheory.APPLY_UPDATE_THM] >>
    disch_then kall_tac >>
    ntac 3(last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
    first_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- apply_abstract_tac >>
    qmatch_abbrev_tac`Boolean(∀x. x <: boolset ⇒ Holds (Abstract bs bs ff) x) = Z` >>
    `∀x. x <: boolset ⇒ Abstract bs bs ff ' x = ff x` by (
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      simp[Abbr`ff`,Abbr`bs`] >>
      apply_abstract_tac ) >>
    simp[Abbr`bs`,Abbr`Z`,holds_def] >>
    simp[Abbr`ff`] >>
    qho_match_abbrev_tac`Boolean(∀x. x <: boolset ⇒ (Boolrel R ' (Abstract d1 bs i1 ' (Abstract d2 bs (i2 x)))) ' x = True) = Z` >>
    `∀x. x <: boolset ⇒ Abstract d1 bs i1 ' (Abstract d2 bs (i2 x)) = i1 (Abstract d2 bs (i2 x))` by (
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      simp[Abbr`bs`,Abbr`d1`,Abbr`i1`,boolean_in_boolset] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      rw[Abbr`i2`] >>
      apply_abstract_tac ) >>
    simp[Abbr`R`,Abbr`bs`,Abbr`d2`] >>
    `∀x. (λm. i2 x m) = (i2 x)` by metis_tac[ETA_AX] >>
    simp[Abbr`i1`] >>
    simp[holds_def] >>
    `∀x a. x <: boolset ∧ a <: tyvof v "A" ⇒ Abstract (tyvof v "A") boolset (i2 x) ' a = i2 x a` by (
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      rw[Abbr`i2`] >>
      apply_abstract_tac ) >>
    fs[Abbr`i2`] >>
    simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_in_boolset,boolean_eq_true,Abbr`Z`] >>
    `∀x. x <: tyvof v "A" ⇒ pp ' x <: boolset` by (rw[] >> apply_abstract_tac) >>
    simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_eq_true] >>
    ntac 20 (pop_assum kall_tac) >>
    simp[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  conj_asm1_tac >- (
    init_tac `Const "\\/" (Fun Bool (Fun Bool Bool)) === OrDef` >>
    pop_assum kall_tac >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[Boolrel_def] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    imp_res_tac typesem_Fun >>
    qspecl_then[`tmsof sig`,`i`,`"!"`,`Fun (Fun Bool Bool) Bool`,`Fun (Fun A Bool) Bool`,`[(Bool,A)]`]mp_tac instance_def >>
    discharge_hyps >- (fs[is_bool_sig_def,is_forall_sig_def] >> EVAL_TAC) >>
    simp[] >> disch_then kall_tac >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def,REV_ASSOCD] >>
    fs[interprets_def] >>
    qpat_assum`∀t. is_type_valuation t ⇒ tmaof i "!" Z = Y`(fn th => assume_tac th >> (qspec_then`("A" =+ boolset)τ`mp_tac) th) >>
    discharge_hyps >- (
      fs[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >> rw[] >>
      metis_tac[boolean_in_boolset] ) >>
    simp[combinTheory.APPLY_UPDATE_THM] >>
    disch_then kall_tac >>
    ntac 3(last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
    qx_gen_tac`b1` >> strip_tac >> simp[] >>
    conj_tac >- apply_abstract_tac >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac (UNDISCH abstract_eq) >>
    qx_gen_tac`b2` >> strip_tac >> simp[] >>
    simp[boolean_in_boolset] >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- apply_abstract_tac >>
    qmatch_abbrev_tac`Boolean (∀x. x <: boolset ⇒ Holds (Abstract boolset boolset ff) x) = Z` >>
    `∀x. x <: boolset ⇒ Abstract boolset boolset ff ' x = ff x` by (
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      rw[Abbr`ff`] >>
      apply_abstract_tac ) >>
    rw[holds_def] >>
    simp[SIMP_RULE(srw_ss())[]apply_boolrel,Abbr`ff`,boolean_in_boolset,Abbr`Z`] >>
    simp[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  conj_asm1_tac >- (
    init_tac`Const "F" Bool === FalseDef` >>
    pop_assum kall_tac >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    imp_res_tac typesem_Fun >>
    qspecl_then[`tmsof sig`,`i`,`"!"`,`Fun (Fun Bool Bool) Bool`,`Fun (Fun A Bool) Bool`,`[(Bool,A)]`]mp_tac instance_def >>
    discharge_hyps >- (fs[is_bool_sig_def,is_forall_sig_def] >> EVAL_TAC) >>
    simp[] >> disch_then kall_tac >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def,REV_ASSOCD] >>
    fs[interprets_def] >>
    qpat_assum`∀t. is_type_valuation t ⇒ tmaof i "!" Z = Y`(fn th => assume_tac th >> (qspec_then`("A" =+ boolset)τ`mp_tac) th) >>
    discharge_hyps >- (
      fs[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >> rw[] >>
      metis_tac[boolean_in_boolset] ) >>
    simp[combinTheory.APPLY_UPDATE_THM] >> disch_then kall_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- (
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      rw[] ) >>
    rw[boolean_def] >>
    first_x_assum(qspec_then`False`mp_tac) >>
    rw[mem_boolset,holds_def] >>
    pop_assum(SUBST1_TAC o SYM) >>
    match_mp_tac apply_abstract_matchable >>
    simp[mem_boolset] ) >>
  init_tac`Const "~" (Fun Bool Bool) === NotDef` >>
  pop_assum kall_tac >>
  imp_res_tac is_std_interpretation_is_type >>
  imp_res_tac typesem_Bool >> simp[] >>
  fs[interprets_def] >>
  rpt (last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[boolean_in_boolset,SIMP_RULE(srw_ss())[]apply_boolrel,combinTheory.APPLY_UPDATE_THM,mem_boolset,boolean_def] >>
  rw[] >> rw[] >> fs[])

val _ = export_theory()
