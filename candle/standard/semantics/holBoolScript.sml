(*
  Define semantics for the Boolean operations and show the definitions are
  correct.
*)
open preamble holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holBoolSyntaxTheory
     holSemanticsTheory holSemanticsExtraTheory setSpecTheory

val _ = new_theory"holBool"

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

val _ = Parse.temp_overload_on("p",``Var (strlit "p") Bool``)
val _ = Parse.temp_overload_on("FAp",``Forall (strlit "p") Bool``)
val _ = Parse.temp_overload_on("q",``Var (strlit "q") Bool``)
val _ = Parse.temp_overload_on("FAq",``Forall (strlit "q") Bool``)
val _ = Parse.temp_overload_on("r",``Var (strlit "r") Bool``)
val _ = Parse.temp_overload_on("FAr",``Forall (strlit "r") Bool``)
val _ = Parse.temp_overload_on("f",``Var (strlit "f") (Fun Bool (Fun Bool Bool))``)
val _ = Parse.temp_overload_on("A",``Tyvar (strlit "A")``)
val _ = Parse.temp_overload_on("P",``Var (strlit "P") (Fun A Bool)``)
val _ = Parse.temp_overload_on("x",``Var (strlit "x") A``)
val _ = Parse.temp_overload_on("FAx",``Forall (strlit "x") A``)

val sigs = [is_true_sig_def, is_false_sig_def, is_implies_sig_def, is_and_sig_def,
            is_or_sig_def, is_not_sig_def, is_forall_sig_def, is_exists_sig_def]

Theorem bool_sig_instances:
   is_bool_sig sig ⇒
    instance (tmsof sig) (i:'U interpretation) (strlit "T") Bool = (K (tmaof i (strlit "T") [])) ∧
    instance (tmsof sig) i (strlit "F") Bool = (K (tmaof i (strlit "F") [])) ∧
    instance (tmsof sig) i (strlit "==>") (Fun Bool (Fun Bool Bool)) = (K (tmaof i (strlit "==>") [])) ∧
    instance (tmsof sig) i (strlit "/\\") (Fun Bool (Fun Bool Bool)) = (K (tmaof i (strlit "/\\") [])) ∧
    instance (tmsof sig) i (strlit "\\/") (Fun Bool (Fun Bool Bool)) = (K (tmaof i (strlit "\\/") [])) ∧
    instance (tmsof sig) i (strlit "~") (Fun Bool Bool) = (K (tmaof i (strlit "~") [])) ∧
    instance (tmsof sig) i (strlit "!") (Fun (Fun A Bool) Bool) = (λτ. tmaof i (strlit "!") [τ (strlit "A")]) ∧
    instance (tmsof sig) i (strlit "?") (Fun (Fun A Bool) Bool) = (λτ. tmaof i (strlit "?") [τ (strlit "A")])
Proof
  rw[is_bool_sig_def] >> fs sigs >> imp_res_tac identity_instance >> rw[FUN_EQ_THM] >>
  rpt AP_TERM_TAC >> rw[FUN_EQ_THM,tyvars_def] >> EVAL_TAC >> metis_tac[]
QED

val Boolrel_def = xDefine"Boolrel"`
  Boolrel0 ^mem R =
      (Abstract boolset (Funspace boolset boolset)
           (λp. (Abstract boolset boolset
              (λq. Boolean (R (p = True) (q = True))))))`
val _ = Parse.overload_on("Boolrel",``Boolrel0 ^mem``)

val is_true_interpretation_def = xDefine"is_true_interpretation"`
  is_true_interpretation0 ^mem γ ⇔ (γ:'U tmass) interprets (strlit "T") on [] as K True`
val _ = Parse.overload_on("is_true_interpretation",``is_true_interpretation0 ^mem``)

val is_and_interpretation_def = xDefine"is_and_interpretation"`
  is_and_interpretation0 ^mem γ ⇔ γ interprets (strlit "/\\") on [] as K (Boolrel $/\)`
val _ = Parse.overload_on("is_and_interpretation",``is_and_interpretation0 ^mem``)

val is_implies_interpretation_def = xDefine"is_implies_interpretation"`
  is_implies_interpretation0 ^mem γ ⇔ γ interprets (strlit "==>") on [] as K (Boolrel $==>)`
val _ = Parse.overload_on("is_implies_interpretation",``is_implies_interpretation0 ^mem``)

val is_forall_interpretation_def = xDefine"is_forall_interpretation"`
  is_forall_interpretation0 ^mem γ ⇔ γ
    interprets (strlit "!") on [strlit "A"] as
       (λl. Abstract (Funspace (HD l) boolset) boolset
              (λP. Boolean (∀x. x <: (HD l) ⇒ Holds P x)))`
val _ = Parse.overload_on("is_forall_interpretation",``is_forall_interpretation0 ^mem``)

val is_exists_interpretation_def = xDefine"is_exists_interpretation"`
  is_exists_interpretation0 ^mem γ ⇔ γ
    interprets (strlit "?") on [strlit "A"] as
       (λl. Abstract (Funspace (HD l) boolset) boolset
              (λP. Boolean (∃x. x <: (HD l) ∧ Holds P x)))`
val _ = Parse.overload_on("is_exists_interpretation",``is_exists_interpretation0 ^mem``)

val is_or_interpretation_def = xDefine"is_or_interpretation"`
  is_or_interpretation0 ^mem γ ⇔ γ interprets (strlit "\\/") on [] as K (Boolrel $\/)`
val _ = Parse.overload_on("is_or_interpretation",``is_or_interpretation0 ^mem``)

val is_false_interpretation_def = xDefine"is_false_interpretation"`
  is_false_interpretation0 ^mem γ ⇔ (γ:'U tmass) interprets (strlit "F") on [] as K False`
val _ = Parse.overload_on("is_false_interpretation",``is_false_interpretation0 ^mem``)

val is_not_interpretation_def = xDefine"is_not_interpretation"`
  is_not_interpretation0 ^mem γ ⇔ γ interprets (strlit "~") on [] as K (Abstract boolset boolset (λp. Boolean (p ≠ True)))`
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

Theorem boolrel_in_funspace:
   is_set_theory ^mem ⇒ Boolrel R <: Funspace boolset (Funspace boolset boolset)
Proof
  rw[Boolrel_def] >> match_mp_tac (UNDISCH abstract_in_funspace) >> rw[] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >> rw[boolean_in_boolset]
QED
val _ = export_rewrites["boolrel_in_funspace"]

val Defs = [TrueDef_def, AndDef_def, ImpliesDef_def, ForallDef_def, ExistsDef_def, OrDef_def, FalseDef_def, NotDef_def]

fun init_tac q =
  fs[models_def] >>
  first_x_assum(qspec_then q mp_tac) >>
  impl_tac >- (unabbrev_all_tac >> EVAL_TAC) >>
  simp[satisfies_def] >>
  strip_tac >>
  simp[interprets_def] >>
  qx_gen_tac`τ`>>strip_tac >>
  qspecl_then[`tysof sig`,`tyaof i`,`τ`]mp_tac (UNDISCH term_valuation_exists) >>
  impl_tac >- fs[is_interpretation_def] >> strip_tac >>
  first_x_assum(qspec_then`(τ,σ)`mp_tac) >> simp[] >>
  qabbrev_tac`v = (τ,σ)` >>
  `is_structure sig i v` by fs[is_structure_def] >>
  REWRITE_TAC Defs >>
  Q.PAT_ABBREV_TAC`eq = l1 === r1` >>
  `term_ok sig eq` by (
    unabbrev_all_tac >>
    simp[term_ok_clauses,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,bool_term_ok] >>
    simp[term_ok_def] >>
    qpat_x_assum`is_std_sig X`mp_tac >>
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

Theorem apply_boolrel:
   is_set_theory ^mem ⇒
    ∀b1 b2 b3. b1 <: boolset ∧ b2 <: boolset ∧ (b3 = Boolean (R (b1 = True) (b2 = True))) ⇒
      Boolrel R ' b1 ' b2 = b3
Proof
  rw[] >>
  `Boolrel R ' b1 = Abstract boolset boolset (λb2. Boolean (R (b1 = True) (b2 = True)))` by (
    rw[Boolrel_def] >>
    match_mp_tac apply_abstract_matchable >>
    rw[] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[boolean_in_boolset] ) >>
  rw[] >>
  match_mp_tac apply_abstract_matchable >>
  rw[boolean_in_boolset]
QED

Theorem bool_has_bool_interpretation:
   is_set_theory ^mem ⇒
    ∀ctxt i. theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
             i models (thyof (mk_bool_ctxt ctxt)) ⇒
             is_bool_interpretation i
Proof
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
  `FLOOKUP (tysof sig) (strlit "bool") = SOME 0` by (
    qpat_x_assum`is_std_sig _` mp_tac >>
    simp[is_std_sig_def,Abbr`sig`,Abbr`ctx`]) >>
  `FLOOKUP (tysof sig) (strlit "fun") = SOME 2` by (
    qpat_x_assum`is_std_sig _` mp_tac >>
    simp[is_std_sig_def,Abbr`sig`,Abbr`ctx`]) >>
  simp ints >>
  conj_asm1_tac >- (
    init_tac`Const (strlit "T") Bool === TrueDef` >>
    `term_ok sig TrueDef` by (
      simp[term_ok_equation,term_ok_clauses,TrueDef_def] ) >>
    fs[TrueDef_def] >>
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_eq_true,termsem_def]) >>
  conj_asm1_tac >- (
    init_tac `Const (strlit "/\\") (Fun Bool (Fun Bool Bool)) === AndDef` >>
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
      qpat_x_assum`f1 = f2`kall_tac >>
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
    init_tac `Const (strlit "==>") (Fun Bool (Fun Bool Bool)) === ImpliesDef` >>
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
    init_tac `Const (strlit "!") (Fun (Fun A Bool) Bool) === ForallDef` >>
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
    Q.PAT_ABBREV_TAC`aa:'U = X (strlit "A")` >>
    qspecl_then[`pp`,`aa`,`boolset`]mp_tac(UNDISCH in_funspace_abstract) >>
    impl_tac >- (fs[is_type_valuation_def,Abbr`aa`] >> metis_tac[boolean_in_boolset]) >>
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
    init_tac `Const (strlit "?") (Fun (Fun A Bool) Bool) === ExistsDef` >>
    `τ = tyvof v` by simp[Abbr`v`] >> fs[] >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    imp_res_tac typesem_Fun >> simp[typesem_def] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    qx_gen_tac`pp` >> strip_tac >>
    simp[boolean_in_boolset] >>
    qspecl_then[`tmsof sig`,`i`,`strlit "!"`,`Fun (Fun Bool Bool) Bool`,`Fun (Fun A Bool) Bool`,`[(Bool,A)]`]mp_tac instance_def >>
    impl_tac >- (fs[is_bool_sig_def,is_exists_sig_def,is_forall_sig_def] >> EVAL_TAC) >>
    simp[] >> disch_then kall_tac >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def,REV_ASSOCD,
         mlstringTheory.implode_def] >>
    fs[interprets_def] >>
    qpat_x_assum`∀t. is_type_valuation t ⇒ Z`(fn th => assume_tac th >> (qspec_then`(strlit "A" =+ boolset)τ`mp_tac) th) >>
    impl_tac >- (
      fs[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >> rw[] >>
      metis_tac[boolean_in_boolset] ) >>
    simp[combinTheory.APPLY_UPDATE_THM] >>
    disch_then kall_tac >>
    ntac 3(last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
    first_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac >>
    conj_tac >- ( apply_abstract_tac ) >>
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
    `∀x a. x <: boolset ∧ a <: tyvof v (strlit "A") ⇒ Abstract (tyvof v (strlit "A")) boolset (i2 x) ' a = i2 x a` by (
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      rw[Abbr`i2`] >>
      apply_abstract_tac ) >>
    fs[Abbr`i2`] >>
    simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_in_boolset,boolean_eq_true,Abbr`Z`] >>
    `∀x. x <: tyvof v (strlit "A") ⇒ pp ' x <: boolset` by (rw[] >> apply_abstract_tac) >>
    simp[SIMP_RULE(srw_ss())[]apply_boolrel,boolean_eq_true] >>
    ntac 20 (pop_assum kall_tac) >>
    simp[boolean_def] >>
    metis_tac[mem_boolset] ) >>
  conj_asm1_tac >- (
    init_tac `Const (strlit "\\/") (Fun Bool (Fun Bool Bool)) === OrDef` >>
    pop_assum kall_tac >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[Boolrel_def] >>
    match_mp_tac (UNDISCH abstract_eq) >>
    imp_res_tac typesem_Fun >>
    qspecl_then[`tmsof sig`,`i`,`strlit "!"`,`Fun (Fun Bool Bool) Bool`,`Fun (Fun A Bool) Bool`,`[(Bool,A)]`]mp_tac instance_def >>
    impl_tac >- (fs[is_bool_sig_def,is_forall_sig_def] >> EVAL_TAC) >>
    simp[] >> disch_then kall_tac >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def,REV_ASSOCD,mlstringTheory.implode_def] >>
    fs[interprets_def] >>
    qpat_x_assum`∀t. is_type_valuation t ⇒ tmaof i (strlit "!") Z = Y`(fn th => assume_tac th >> (qspec_then`(strlit "A" =+ boolset)τ`mp_tac) th) >>
    impl_tac >- (
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
    init_tac`Const (strlit "F") Bool === FalseDef` >>
    pop_assum kall_tac >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Bool >> simp[] >>
    imp_res_tac typesem_Fun >>
    qspecl_then[`tmsof sig`,`i`,`strlit "!"`,`Fun (Fun Bool Bool) Bool`,`Fun (Fun A Bool) Bool`,`[(Bool,A)]`]mp_tac instance_def >>
    impl_tac >- (fs[is_bool_sig_def,is_forall_sig_def] >> EVAL_TAC) >>
    simp[] >> disch_then kall_tac >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def,REV_ASSOCD,mlstringTheory.implode_def] >>
    fs[interprets_def] >>
    qpat_x_assum`∀t. is_type_valuation t ⇒ tmaof i (strlit "!") Z = Y`(fn th => assume_tac th >> (qspec_then`(strlit "A" =+ boolset)τ`mp_tac) th) >>
    impl_tac >- (
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
  init_tac`Const (strlit "~") (Fun Bool Bool) === NotDef` >>
  pop_assum kall_tac >>
  imp_res_tac is_std_interpretation_is_type >>
  imp_res_tac typesem_Bool >> simp[] >>
  fs[interprets_def] >>
  rpt (last_x_assum(qspec_then`τ`mp_tac)>>simp[]>>strip_tac) >>
  match_mp_tac (UNDISCH abstract_eq) >>
  simp[boolean_in_boolset,SIMP_RULE(srw_ss())[]apply_boolrel,combinTheory.APPLY_UPDATE_THM,mem_boolset,boolean_def] >>
  rw[] >> rw[] >> fs[]
QED

Theorem extends_is_bool_interpretation:
   is_set_theory ^mem ∧
    ctxt2 extends (mk_bool_ctxt ctxt) ∧
    theory_ok (thyof (mk_bool_ctxt ctxt)) ∧
    i models (thyof ctxt2) ⇒
    is_bool_interpretation i
Proof
  strip_tac >>
  `i models thyof (mk_bool_ctxt ctxt)` by (
    `∃x y z. thyof (mk_bool_ctxt ctxt) = ((x,y),z)` by metis_tac[pairTheory.PAIR] >>
    simp[] >>
    match_mp_tac (UNDISCH models_reduce) >>
    imp_res_tac theory_ok_sig >> rfs[] >>
    `∃x y z. thyof ctxt2 = ((x,y),z)` by metis_tac[pairTheory.PAIR] >>
    fs[] >>
    CONV_TAC(STRIP_QUANT_CONV(move_conj_left(can(match_term``i models _``)))) >>
    first_assum(match_exists_tac o concl) >> simp[] >> fs[] >>
    rpt BasicProvers.VAR_EQ_TAC >>
    imp_res_tac extends_sub >> fs[] >>
    fs[theory_ok_def] ) >>
  metis_tac[bool_has_bool_interpretation]
QED

Theorem termsem_implies:
   is_set_theory ^mem ⇒
    ∀s i v p1 p2.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_type_assignment (tyaof i) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_implies_sig (tmsof s) ∧ is_implies_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Implies p1 p2) =
    Boolean (termsem (tmsof s) i v p1 = True ⇒
             termsem (tmsof s) i v p2 = True)
Proof
  rw[termsem_def,is_implies_sig_def,is_implies_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"==>"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K boolset`mp_tac) >>
  impl_tac >- (
    simp[is_type_valuation_def] >>
    metis_tac[boolean_in_boolset]) >>
  simp[] >> disch_then kall_tac >>
  simp[Boolrel_def] >>
  qmatch_abbrev_tac`Abstract b fbb ff ' a1 ' a2 = c` >>
  `Abstract b fbb ff ' a1 = ff a1` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      simp[] >>
      qexists_tac`s` >> simp[] >>
      imp_res_tac typesem_Bool >> simp[] ) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`ff`] >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  unabbrev_all_tac >> simp[] >>
  conj_tac >- (
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >>
    qexists_tac`s` >> simp[] >>
    imp_res_tac typesem_Bool >> simp[] ) >>
  simp[boolean_in_boolset]
QED

Theorem termsem_forall:
   is_set_theory ^mem ⇒
    ∀s i v f y b.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_interpretation i ∧
    type_ok (tysof s) y ∧ term_ok s b ∧ typeof b = Bool ∧
    is_forall_sig (tmsof s) ∧ is_forall_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Forall f y b) =
    Boolean (∀x. x <: typesem (tyaof i) (tyvof v) y ⇒
                 termsem (tmsof s) i (tyvof v, ((f,y) =+ x) (tmvof v)) b = True)
Proof
  rw[termsem_def,is_forall_sig_def,is_forall_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"!"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[y,Tyvar(strlit"A")]`mp_tac) >>
  simp[holSyntaxLibTheory.REV_ASSOCD] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K(typesem (tyaof i) (tyvof v) y)`mp_tac) >>
  impl_tac >- (
    simp[is_type_valuation_def] >>
    match_mp_tac(UNDISCH typesem_inhabited) >>
    metis_tac[is_interpretation_def,is_valuation_def] ) >>
  simp[] >> disch_then kall_tac >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  fs[is_std_interpretation_def] >>
  imp_res_tac typesem_Bool >> simp[] >>
  simp[boolean_in_boolset] >>
  simp[holds_def] >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >> simp[] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >> qexists_tac`s` >> simp[] >>
    fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> rw[] ) >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  qmatch_abbrev_tac`Z ⇒ B ⇔ Z ⇒ C` >>
  `Z ⇒ (B ⇔ C)` suffices_by metis_tac[] >>
  unabbrev_all_tac >> strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  match_mp_tac (UNDISCH termsem_typesem_matchable) >>
  simp[] >> qexists_tac`s` >> simp[] >>
  fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[]
QED

Theorem termsem_exists:
   is_set_theory ^mem ⇒
    ∀s i v f y b.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_interpretation i ∧
    type_ok (tysof s) y ∧ term_ok s b ∧ typeof b = Bool ∧
    is_exists_sig (tmsof s) ∧ is_exists_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Exists f y b) =
    Boolean (∃x. x <: typesem (tyaof i) (tyvof v) y ∧
                 termsem (tmsof s) i (tyvof v, ((f,y) =+ x) (tmvof v)) b = True)
Proof
  rw[termsem_def,is_exists_sig_def,is_exists_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"?"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[y,Tyvar(strlit"A")]`mp_tac) >>
  simp[holSyntaxLibTheory.REV_ASSOCD] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K(typesem (tyaof i) (tyvof v) y)`mp_tac) >>
  impl_tac >- (
    simp[is_type_valuation_def] >>
    match_mp_tac(UNDISCH typesem_inhabited) >>
    metis_tac[is_interpretation_def,is_valuation_def] ) >>
  simp[] >> disch_then kall_tac >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  fs[is_std_interpretation_def] >>
  imp_res_tac typesem_Bool >> simp[] >>
  simp[boolean_in_boolset] >>
  simp[holds_def] >>
  conj_tac >- (
    match_mp_tac (UNDISCH abstract_in_funspace) >> simp[] >> rw[] >>
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >> qexists_tac`s` >> simp[] >>
    fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> rw[] ) >>
  AP_TERM_TAC >>
  AP_TERM_TAC >>
  simp[FUN_EQ_THM] >>
  gen_tac >>
  qmatch_abbrev_tac`Z ∧ B ⇔ Z ∧ C` >>
  `Z ⇒ (B ⇔ C)` suffices_by metis_tac[] >>
  unabbrev_all_tac >> strip_tac >>
  AP_THM_TAC >> AP_TERM_TAC >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  match_mp_tac (UNDISCH termsem_typesem_matchable) >>
  simp[] >> qexists_tac`s` >> simp[] >>
  fs[is_valuation_def,is_term_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> rw[]
QED

Theorem termsem_and:
   is_set_theory ^mem ⇒
    ∀s i v p1 p2.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_type_assignment (tyaof i) ∧
    term_ok s p1 ∧ term_ok s p2 ∧
    typeof p1 = Bool ∧ typeof p2 = Bool ∧
    is_and_sig (tmsof s) ∧ is_and_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (And p1 p2) =
    Boolean (termsem (tmsof s) i v p1 = True ∧
             termsem (tmsof s) i v p2 = True)
Proof
  rw[termsem_def,is_and_sig_def,is_and_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"/\\"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(LAND_CONV(RAND_CONV EVAL)))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K boolset`mp_tac) >>
  impl_tac >- (
    simp[is_type_valuation_def] >>
    metis_tac[boolean_in_boolset]) >>
  simp[] >> disch_then kall_tac >>
  simp[Boolrel_def] >>
  qmatch_abbrev_tac`Abstract b fbb ff ' a1 ' a2 = c` >>
  `Abstract b fbb ff ' a1 = ff a1` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- (
      match_mp_tac (UNDISCH termsem_typesem_matchable) >>
      simp[] >>
      qexists_tac`s` >> simp[] >>
      imp_res_tac typesem_Bool >> simp[] ) >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`ff`] >>
  match_mp_tac apply_abstract_matchable >> simp[] >>
  unabbrev_all_tac >> simp[] >>
  conj_tac >- (
    match_mp_tac (UNDISCH termsem_typesem_matchable) >>
    simp[] >>
    qexists_tac`s` >> simp[] >>
    imp_res_tac typesem_Bool >> simp[] ) >>
  simp[boolean_in_boolset]
QED

Theorem termsem_not:
   is_set_theory ^mem ⇒
    ∀s i v p1.
    is_valuation (tysof s) (tyaof i) v ∧
    is_interpretation s i ∧
    is_std_type_assignment (tyaof i) ∧
    term_ok s p1 ∧
    typeof p1 = Bool ∧
    is_not_sig (tmsof s) ∧ is_not_interpretation (tmaof i) ⇒
    termsem (tmsof s) i v (Not p1) =
    Boolean (termsem (tmsof s) i v p1 ≠ True)
Proof
  rw[termsem_def,is_not_sig_def,is_not_interpretation_def] >>
  qspecl_then[`tmsof s`,`i`,`strlit"~"`]mp_tac instance_def >> simp[] >>
  disch_then(qspec_then`[]`mp_tac) >>
  simp[] >> disch_then kall_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(RAND_CONV EVAL))) >>
  fs[interprets_def] >>
  first_x_assum(qspec_then`K boolset`mp_tac) >>
  impl_tac >- (
    simp[is_type_valuation_def] >>
    metis_tac[boolean_in_boolset]) >>
  simp[] >> disch_then kall_tac >>
  match_mp_tac (apply_abstract_matchable) >>
  simp[boolean_in_boolset] >>
  match_mp_tac (UNDISCH termsem_typesem_matchable) >>
  simp[] >>
  qexists_tac`s` >> simp[] >>
  imp_res_tac typesem_Bool >> simp[]
QED

val _ = export_theory()
