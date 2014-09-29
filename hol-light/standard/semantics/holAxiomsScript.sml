open HolKernel boolLib bossLib lcsymtacs relationTheory pairTheory listTheory finite_mapTheory alistTheory pred_setTheory
open miscLib miscTheory holBoolTheory holBoolSyntaxTheory holSyntaxLibTheory holSyntaxTheory holSyntaxExtraTheory holAxiomsSyntaxTheory
open setSpecTheory holSemanticsTheory holSemanticsExtraTheory holExtensionTheory

val _ = new_theory"holAxioms"

val _ = Parse.temp_overload_on("A",``Tyvar "A"``)
val _ = Parse.temp_overload_on("B",``Tyvar "B"``)
val _ = Parse.temp_overload_on("x",``Var "x" A``)
val _ = Parse.temp_overload_on("Absx",``Abs "x" A``)
val _ = Parse.temp_overload_on("g",``Var "f" (Fun A B)``)
val _ = Parse.temp_overload_on("B",``Tyvar "B"``)
val _ = Parse.temp_overload_on("EXx",``Exists "x" A``)
val _ = Parse.temp_overload_on("Absg",``Abs "f" (Fun A B)``)
val _ = Parse.temp_overload_on("x1",``Var "x1" A``)
val _ = Parse.temp_overload_on("FAx1",``Forall "x1" A``)
val _ = Parse.temp_overload_on("x2",``Var "x2" A``)
val _ = Parse.temp_overload_on("FAx2",``Forall "x2" A``)
val _ = Parse.temp_overload_on("y",``Var "y" B``)
val _ = Parse.temp_overload_on("FAy",``Forall "y" B``)

val mem = ``mem:'U->'U->bool``

val eta_has_model = store_thm("eta_has_model",
  ``is_set_theory ^mem ⇒
    ∀ctxt. is_std_sig (sigof ctxt) ⇒
      ∀i. i models (thyof ctxt) ⇒
        i models (thyof (mk_eta_ctxt ctxt))``,
  rw[models_def,mk_eta_ctxt_def,conexts_of_upd_def] >> res_tac >>
  rw[satisfies_def] >>
  `is_structure (sigof ctxt) i v` by simp[is_structure_def] >>
  `term_ok (sigof ctxt) (Absx (Comb g x) === g)` by (
    rw[term_ok_equation,term_ok_def,type_ok_def] >>
    fs[is_std_sig_def] ) >>
  `tmsof ctxt = tmsof (sigof ctxt)` by simp[] >> pop_assum SUBST1_TAC >>
  rw[SIMP_RULE std_ss [] termsem_equation,boolean_eq_true] >>
  rw[termsem_def] >>
  imp_res_tac is_std_interpretation_is_type >>
  imp_res_tac typesem_Fun >>
  `termsem (tmsof ctxt) i v g <: typesem (tyaof i) (tyvof v) (typeof g)` by (
    match_mp_tac (UNDISCH termsem_typesem) >>
    qexists_tac`sigof ctxt` >>
    simp[term_ok_def,type_ok_def] >>
    fs[is_std_sig_def]) >>
  rfs[termsem_def] >>
  rfs[typesem_def] >>
  qspecl_then[`tmvof v ("f",Fun A B)`,`tyvof v "A"`,`tyvof v "B"`]mp_tac (UNDISCH in_funspace_abstract) >>
  discharge_hyps >- ( fs[is_valuation_def,is_type_valuation_def] ) >>
  rw[] >> rw[] >>
  match_mp_tac (UNDISCH abstract_eq) >>
  rw[] >- (
    match_mp_tac (UNDISCH apply_in_rng) >>
    qexists_tac`tyvof v "A"` >>
    rw[combinTheory.APPLY_UPDATE_THM] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    rw[] ) >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  match_mp_tac (UNDISCH apply_abstract) >>
  rw[])

val good_select_def = xDefine"good_select"`
  good_select0 ^mem select = (∀ty p x. x <: ty ⇒ select ty p <: ty ∧ (p x ⇒ p (select ty p)))`
val _ = Parse.overload_on("good_select",``good_select0 ^mem``)

val select_has_model_gen = store_thm("select_has_model_gen",
  ``is_set_theory ^mem ⇒
    ∀ctxt.
      "@" ∉ FDOM (tmsof ctxt) ∧
      (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool))) ∧
      theory_ok (thyof ctxt)
      ⇒
      ∀i select.
        i models (thyof ctxt) ∧
        tmaof i interprets "==>" on [] as
          (K (Abstract boolset (Funspace boolset boolset)
                 (λp. Abstract boolset boolset
                     (λq. Boolean ((p = True) ⇒ (q = True)))))) ∧
        good_select select
      ⇒ ∃i'. equal_on ctxt i i' ∧
             i' models (thyof (mk_select_ctxt ctxt)) ∧
             (tmaof i' "@" =
                (λls. Abstract (Funspace (HD ls) boolset) (HD ls)
                        (λp. select (HD ls) (Holds p))))``,
  rw[good_select_def,models_def,mk_select_ctxt_def,conexts_of_upd_def] >>
  qexists_tac`(tyaof i, ("@" =+ λl. Abstract (Funspace (HD l) boolset) (HD l)
                                      (λp. select (HD l) (Holds p))) (tmaof i))` >>
  imp_res_tac is_std_interpretation_is_type >>
  imp_res_tac typesem_Fun >>
  conj_tac >- (
    simp[equal_on_def,combinTheory.APPLY_UPDATE_THM,term_ok_def] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP,EXISTS_PROD] >> metis_tac[] ) >>
  conj_asm1_tac >- (
    conj_asm1_tac >- (
      fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP,FLOOKUP_UPDATE] >>
      rw[] >> rw[combinTheory.APPLY_UPDATE_THM] >>
      rw[typesem_def,tyvars_def,STRING_SORT_def,LIST_UNION_def,INORDER_INSERT_def,LIST_INSERT_def] >>
      fs[is_std_type_assignment_def] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      rw[holds_def] >> fs[is_type_valuation_def]) >>
    conj_tac >- (
      fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM,interprets_def] ) >>
    reverse(rw[]) >- (
      match_mp_tac satisfies_extend >>
      map_every qexists_tac[`tysof ctxt`,`tmsof ctxt`] >>
      simp[] >>
      conj_asm1_tac >- fs[theory_ok_def] >>
      match_mp_tac satisfies_consts >>
      imp_res_tac theory_ok_sig >>
      fs[] >> qexists_tac`i` >>
      simp[] >>
      simp[combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> fs[term_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    simp[satisfies_def] >>
    gen_tac >> strip_tac >>
    qmatch_abbrev_tac`termsem tmsig ii v tm = True` >>
    `FLOOKUP tmsig "@" = SOME (Fun (Fun A Bool) A)` by simp[Abbr`tmsig`,FLOOKUP_UPDATE] >>
    `FLOOKUP tmsig "==>" = SOME (Fun Bool (Fun Bool Bool))` by simp[Abbr`tmsig`,FLOOKUP_UPDATE] >>
    imp_res_tac identity_instance >>
    simp[Abbr`tm`,termsem_def] >>
    simp[tyvars_def,STRING_SORT_def,LIST_UNION_def,LIST_INSERT_def,INORDER_INSERT_def] >>
    simp[Abbr`ii`,combinTheory.APPLY_UPDATE_THM] >>
    fs[interprets_def] >>
    last_x_assum(qspec_then`tyvof v`mp_tac) >>
    discharge_hyps >- fs[is_valuation_def] >>
    simp[] >> disch_then kall_tac >>
    qmatch_abbrev_tac`(Abstract bs fbs fi ' fz) ' fy = True` >>
    `fi fz <: fbs` by (
      unabbrev_all_tac >> simp[] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      simp[boolean_in_boolset] ) >>
    qmatch_assum_abbrev_tac`Abbrev(fz = fp ' fx)` >>
    Q.PAT_ABBREV_TAC`fa = tyvof v "A"` >>
    `fx <: fa ∧ fp <: Funspace fa boolset` by (
      fs[is_valuation_def,is_term_valuation_def] >>
      first_assum(qspecl_then[`"P"`,`Fun A Bool`]mp_tac) >>
      first_x_assum(qspecl_then[`"x"`,`A`]mp_tac) >>
      imp_res_tac typesem_Bool >>
      simp[type_ok_def,typesem_def] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def] ) >>
    `fz <: bs` by (
      unabbrev_all_tac >>
      match_mp_tac (UNDISCH apply_in_rng) >>
      PROVE_TAC[] ) >>
    `Abstract bs fbs fi ' fz = fi fz` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      simp[] ) >>
    rfs[] >>
    simp[Abbr`fi`] >>
    match_mp_tac apply_abstract_matchable >>
    qmatch_assum_abbrev_tac`Abbrev(fy = fp ' fm)` >>
    qmatch_assum_abbrev_tac`Abbrev(fm = fo ' fp)` >>
    `fo <: Funspace (Funspace fa bs) fa` by (
      simp[Abbr`fo`] >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      rw[holds_def] >>
      metis_tac[]) >>
    `fm <: fa` by (
      unabbrev_all_tac >>
      match_mp_tac (UNDISCH apply_in_rng) >>
      PROVE_TAC[] ) >>
    `fy <: bs` by (
      unabbrev_all_tac >>
      match_mp_tac (UNDISCH apply_in_rng) >>
      PROVE_TAC[] ) >>
    simp[Abbr`bs`,boolean_in_boolset,boolean_eq_true] >>
    simp[Abbr`fz`,Abbr`fy`] >>
    simp[GSYM holds_def] >> strip_tac >>
    simp[Abbr`fm`] >>
    qmatch_assum_abbrev_tac`Abbrev(fo = Abstract (Funspace fa boolset) fa fs)` >>
    `fo ' fp = fs fp` by (
      unabbrev_all_tac >>
      match_mp_tac (UNDISCH apply_abstract) >> simp[] >>
      rw[holds_def] >>
      metis_tac[]) >>
    simp[Abbr`fs`] >>
    metis_tac[]) >>
  simp[combinTheory.APPLY_UPDATE_THM])

val base_select_def = xDefine "base_select"`
  base_select0 ^mem ty p =
    if inhabited ty then
      (case some x. x <: ty ∧ p x of NONE => (@x. x <: ty) | SOME v => v)
    else ARB`
val _ = Parse.overload_on("base_select",``base_select0 ^mem``)

val good_select_base_select = store_thm("good_select_base_select",
  ``is_set_theory ^mem ⇒
    good_select base_select``,
  rw[good_select_def,base_select_def] >>
  rw[]>> TRY(metis_tac[]) >>
  TRY (
    qho_match_abbrev_tac`(case ($some Q) of NONE => R | SOME v => v) <: ty` >>
    qho_match_abbrev_tac`Z ($some Q)` >>
    match_mp_tac optionTheory.some_intro >>
    simp[Abbr`Z`,Abbr`Q`,Abbr`R`] >>
    metis_tac[] ) >>
  qho_match_abbrev_tac`p (case ($some Q) of NONE => R | SOME v => v)` >>
  qho_match_abbrev_tac`Z ($some Q)` >>
  match_mp_tac optionTheory.some_intro >>
  simp[Abbr`Z`,Abbr`Q`,Abbr`R`] >>
  metis_tac[] )

val select_has_model = store_thm("select_has_model",
  ``is_set_theory ^mem ⇒
    ∀ctxt.
      "@" ∉ FDOM (tmsof ctxt) ∧
      (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool))) ∧
      theory_ok (thyof ctxt)
      ⇒
      ∀i.
        i models (thyof ctxt) ∧
        tmaof i interprets "==>" on [] as
          (K (Abstract boolset (Funspace boolset boolset)
                 (λp. Abstract boolset boolset
                     (λq. Boolean ((p = True) ⇒ (q = True))))))
      ⇒ ∃i'. equal_on ctxt i i' ∧
             i' models (thyof (mk_select_ctxt ctxt))``,
  rw[] >>
  qspec_then`ctxt`mp_tac(UNDISCH select_has_model_gen) >>
  simp[] >>
  disch_then(qspec_then`i`mp_tac) >>
  disch_then(qspec_then`base_select` mp_tac) >>
  metis_tac[good_select_base_select])

val _ = Parse.temp_overload_on("h",``Var "f" (Fun Ind Ind)``)
val _ = Parse.temp_overload_on("Exh",``Exists "f" (Fun Ind Ind)``)
val _ = Parse.temp_overload_on("Boolrel",
  ``λr.  (Abstract boolset (Funspace boolset boolset)
           (λp. (Abstract boolset boolset
              (λq. Boolean (r (p = True) (q = True))))))``)

val EVAL_STRING_SORT =
  CONV_TAC (DEPTH_CONV (fn tm => if can (match_term ``STRING_SORT (tyvars X)``) tm
                        then EVAL tm else raise UNCHANGED))

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
    qmatch_abbrev_tac`termsem (tmsof sctx) i1 tt (l1 === r1) <: boolset` >>
    `term_ok (sigof sctx) (l1 === r1)` by (
      unabbrev_all_tac >>
      simp[term_ok_equation,term_ok_def,type_ok_def] >>
      fs[is_std_sig_def] ) >>
    `is_structure (sigof sctx) i1 tt` by (
      fs[is_structure_def,Abbr`tt`,is_valuation_def,is_term_valuation_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      rw[typesem_def] ) >>
    `tmsof sctx = tmsof (sigof sctx)` by simp[] >> pop_assum SUBST1_TAC >>
    rw[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset]

val infinity_has_model_gen = store_thm("infinity_has_model_gen",
  ``is_set_theory ^mem  ⇒
    ∀ctxt.
      theory_ok (thyof ctxt) ∧
      DISJOINT (FDOM (tmsof ctxt)) {"ONE_ONE";"ONTO"} ∧
      "ind" ∉ FDOM (tysof ctxt) ∧
      (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool))) ∧
      (FLOOKUP (tmsof ctxt) "/\\" = SOME (Fun Bool (Fun Bool Bool))) ∧
      (FLOOKUP (tmsof ctxt) "!" = SOME (Fun (Fun A Bool) Bool)) ∧
      (FLOOKUP (tmsof ctxt) "?" = SOME (Fun (Fun A Bool) Bool)) ∧
      (FLOOKUP (tmsof ctxt) "~" = SOME (Fun Bool Bool))
      ⇒
      ∀i inf.
          i models (thyof ctxt) ∧
          tmaof i interprets "==>" on [] as
            (K (Abstract boolset (Funspace boolset boolset)
                   (λp. Abstract boolset boolset
                       (λq. Boolean ((p = True) ⇒ (q = True)))))) ∧
          tmaof i interprets "/\\" on [] as K (Boolrel $/\) ∧
          tmaof i interprets "!" on ["A"] as
            (λl. Abstract (Funspace (HD l) boolset) boolset
                   (λP. Boolean (∀x. x <: (HD l) ⇒ Holds P x))) ∧
          tmaof i interprets "?" on ["A"] as
            (λl. Abstract (Funspace (HD l) boolset) boolset
                   (λP. Boolean (∃x. x <: (HD l) ∧ Holds P x))) ∧
          tmaof i interprets "~" on [] as
            K (Abstract boolset boolset (λp. Boolean (p ≠ True))) ∧
          is_infinite ^mem inf
      ⇒ ∃i'. equal_on ctxt i i' ∧
             i' models (thyof (mk_infinity_ctxt ctxt)) ∧
             (tyaof i' "ind" [] = inf)``,
  rw[models_def] >>
  `∃ctxt1 p. mk_infinity_ctxt ctxt = (NewAxiom p)::(NewType "ind" 0)::ctxt1` by simp[mk_infinity_ctxt_def] >>
  `mk_infinity_ctxt ctxt extends ctxt` by (
    match_mp_tac infinity_extends >> simp[] ) >>
  `ctxt1 extends ctxt` by (
    rfs[extends_def] >>
    pop_assum mp_tac >>
    simp[Once RTC_CASES1] >>
    rw[] >> fs[mk_infinity_ctxt_def] >>
    pop_assum mp_tac >>
    simp[Once RTC_CASES1] >>
    rw[]) >>
  qspecl_then[`ctxt`,`ctxt1`]mp_tac (UNDISCH extends_consistent) >>
  simp[] >>
  disch_then(qspec_then`i`mp_tac) >>
  simp[models_def] >>
  discharge_hyps >- (
    fs[mk_infinity_ctxt_def] >> rw[] ) >>
  disch_then(qx_choose_then`i1`strip_assume_tac) >>
  simp[conexts_of_upd_def] >>
  qexists_tac`(("ind" =+ (K inf)) (tyaof i1), tmaof i1)` >>
  `¬(MEM "ind" (MAP FST (type_list ctxt1)))` by (
    qpat_assum`X = Y::Z`mp_tac >>
    simp[mk_infinity_ctxt_def] >>
    rw[] >> rw[] ) >>
  `inhabited inf` by (
    fs[is_infinite_def] >>
    imp_res_tac IN_INFINITE_NOT_FINITE >>
    first_x_assum(qspec_then`{}`mp_tac) >>
    simp[] ) >>
  conj_tac >- (
    match_mp_tac equal_on_trans >>
    qexists_tac`i1` >> simp[] >>
    simp[equal_on_def,type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
    rw[] >> imp_res_tac ALOOKUP_MEM >>
    fs[MEM_MAP,EXISTS_PROD] >>
    metis_tac[]) >>
  conj_asm1_tac >- (
    conj_asm1_tac >- (
      fs[is_interpretation_def,is_type_assignment_def,is_term_assignment_def
        ,FEVERY_ALL_FLOOKUP,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >- metis_tac[] >>
      rfs[FLOOKUP_UPDATE] >>
      qsuff_tac`typesem (("ind" =+ K inf) (tyaof i1)) τ v = typesem (tyaof i1) τ v` >- rw[] >>
      match_mp_tac typesem_consts >>
      qexists_tac`tysof ctxt1` >>
      conj_tac >- (
        imp_res_tac extends_theory_ok >>
        fs[theory_ok_def] >>
        first_x_assum match_mp_tac >>
        imp_res_tac ALOOKUP_IN_FRANGE) >>
      simp[type_ok_def,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[]) >>
    imp_res_tac is_std_interpretation_is_type >>
    conj_asm1_tac >- (
      fs[is_std_interpretation_def,combinTheory.APPLY_UPDATE_THM
        ,is_std_type_assignment_def] ) >>
    reverse(rw[]) >- (
      match_mp_tac satisfies_extend >>
      map_every qexists_tac[`tysof ctxt1`,`tmsof ctxt1`] >>
      simp[] >>
      imp_res_tac extends_theory_ok >>
      fs[theory_ok_def] >>
      match_mp_tac satisfies_consts >>
      qexists_tac`i1` >>
      simp[combinTheory.APPLY_UPDATE_THM] >>
      rw[type_ok_def] >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      metis_tac[] ) >>
    `p = Exh (And (One_One h) (Not (Onto h)))` by (
      qpat_assum`X = Y::Z`mp_tac >>
      simp[mk_infinity_ctxt_def] ) >>
    simp[satisfies_def] >>
    gen_tac >> strip_tac >>
    imp_res_tac is_std_interpretation_is_type >>
    imp_res_tac typesem_Fun >>
    imp_res_tac typesem_Bool >>
    fs[] >>
    simp[termsem_def] >>
    ntac 7 (pop_assum kall_tac) >>
    Q.PAT_ABBREV_TAC`tmsig:tmsig = X` >>
    Q.PAT_ABBREV_TAC`int:'U interpretation = X` >>
    qspecl_then[`tmsig`,`int`,`"/\\"`]mp_tac identity_instance >>
    qspecl_then[`tmsig`,`int`,`"~"`]mp_tac identity_instance >>
    qspecl_then[`tmsig`,`int`,`"?"`]mp_tac instance_def >>
    `(FLOOKUP tmsig "?" = FLOOKUP (tmsof ctxt) "?") ∧
     (FLOOKUP tmsig "/\\" = FLOOKUP (tmsof ctxt) "/\\") ∧
     (FLOOKUP tmsig "~" = FLOOKUP (tmsof ctxt) "~")` by (
      simp[Abbr`tmsig`,FLOOKUP_UPDATE] >>
      fs[mk_infinity_ctxt_def] >> rw[] ) >>
    simp[Abbr`tmsig`] >>
    disch_then(qspec_then`[(Fun Ind Ind,A)]`mp_tac) >>
    simp[REV_ASSOCD] >> disch_then kall_tac >>
    ntac 2 (disch_then kall_tac) >>
    CONV_TAC (DEPTH_CONV (fn tm => if can (match_term ``STRING_SORT (tyvars X)``) tm
                          then EVAL tm else raise UNCHANGED)) >>
    simp[typesem_def,combinTheory.APPLY_UPDATE_THM,REV_ASSOCD] >>
    `(∀x y. tyaof int "fun" [x;y] = Funspace x y) ∧
     (tyaof int "ind" [] = inf)` by (
      simp[Abbr`int`,combinTheory.APPLY_UPDATE_THM] >>
      fs[equal_on_def] >> qx_genl_tac[`a`,`b`] >>
      last_x_assum (qspec_then`"fun"`mp_tac) >>
      simp[type_ok_def] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def] >>
      disch_then(qspec_then`[A;A]`mp_tac) >>
      simp[type_ok_def] >>
      fs[is_std_interpretation_def,is_std_type_assignment_def]) >>
    `(tmaof int "?" = tmaof i "?") ∧
     (tmaof int "/\\" = tmaof i "/\\") ∧
     (tmaof int "!" = tmaof i "!") ∧
     (tmaof int "==>" = tmaof i "==>") ∧
     (tmaof int "~" = tmaof i "~")` by (
      simp[Abbr`int`] >>
      fs[equal_on_def] >>
      rpt conj_tac >>
      first_x_assum match_mp_tac >>
      simp[term_ok_def,type_ok_def] >>
      imp_res_tac theory_ok_sig >>
      fs[is_std_sig_def] >>
      qexists_tac`Fun (Fun A Bool) Bool` >>
      simp[type_ok_def] >>qexists_tac`[]` >> simp[REV_ASSOCD]) >>
    simp[] >>
    `(FLOOKUP (tmsof ctxt1) "ONE_ONE" = SOME (Fun (Fun A B) Bool)) ∧
     (FLOOKUP (tmsof ctxt1) "ONTO"    = SOME (Fun (Fun A B) Bool))` by (
      simp[] >>
      fs[mk_infinity_ctxt_def] >>
      rw[] ) >>
    qspecl_then[`tmsof ctxt1`,`int`,`"ONE_ONE"`]mp_tac instance_def >>
    qspecl_then[`tmsof ctxt1`,`int`,`"ONTO"`]mp_tac instance_def >>
    simp[] >>
    ntac 2(disch_then(qspec_then`[(Ind,A);(Ind,B)]`strip_assume_tac)) >>
    ntac 2 (pop_assum mp_tac) >>
    simp[REV_ASSOCD] >> ntac 2 (disch_then kall_tac) >>
    EVAL_STRING_SORT >>
    simp[TYPE_SUBST_def,REV_ASSOCD,typesem_def] >>
    simp[Abbr`int`] >>
    fs[interprets_def] >>
    first_x_assum(qspec_then`K boolset`mp_tac) >>
    discharge_hyps >- (simp[is_type_valuation_def,mem_boolset]>>PROVE_TAC[]) >> strip_tac >>
    first_assum(qspec_then`("A" =+ (Funspace inf inf)) (K boolset)`mp_tac) >>
    discharge_hyps >- (
      simp[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
      reverse(rw[mem_boolset])>-metis_tac[]>>
      qexists_tac`Abstract inf inf I` >>
      match_mp_tac (UNDISCH abstract_in_funspace) >>
      rw[] ) >>
    simp[combinTheory.APPLY_UPDATE_THM] >> disch_then kall_tac >>
    first_x_assum(qspec_then`("A" =+ inf) (K boolset)`mp_tac) >>
    discharge_hyps >- (
      simp[is_type_valuation_def,combinTheory.APPLY_UPDATE_THM] >>
      rw[mem_boolset]>>
      metis_tac[]) >>
    simp[combinTheory.APPLY_UPDATE_THM] >> strip_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset,boolean_eq_true] >>
    first_assum(qspec_then`Const "ONE_ONE" (Fun (Fun A B) Bool) ===
                           Absg (FAx1 (FAx2 (Implies (Comb g x1 === Comb g x2) (x1 === x2))))`
                mp_tac) >>
    discharge_hyps >- ( fs[mk_infinity_ctxt_def] >> rw[] >> EVAL_TAC ) >>
    simp[satisfies_def] >>
    qabbrev_tac`τ = ("A" =+ inf) (("B" =+ inf) (K boolset))` >>
    `is_type_valuation τ` by (
      simp[is_type_valuation_def,Abbr`τ`,combinTheory.APPLY_UPDATE_THM] >>
      rw[] >> metis_tac[boolean_in_boolset] ) >>
    qspecl_then[`tysof ctxt1`,`tyaof i1`,`τ`]mp_tac (UNDISCH term_valuation_exists) >>
    discharge_hyps >- fs[is_interpretation_def] >>
    strip_tac >>
    disch_then(qspec_then`τ,σ`mp_tac) >> simp[] >>
    `is_std_sig (sigof ctxt1)` by (
      imp_res_tac extends_theory_ok >>
      imp_res_tac theory_ok_sig >>
      fs[] ) >>
    `is_structure (sigof ctxt1) i1 (τ,σ)` by fs[is_structure_def] >>
    `(ALOOKUP (const_list ctxt1) "==>" = ALOOKUP (const_list ctxt) "==>") ∧
     (ALOOKUP (const_list ctxt1) "!" = ALOOKUP (const_list ctxt) "!") ∧
     (ALOOKUP (const_list ctxt1) "?" = ALOOKUP (const_list ctxt) "?") ∧
     (ALOOKUP (const_list ctxt1) "ONE_ONE" = SOME (Fun (Fun A B) Bool)) ∧
     (ALOOKUP (const_list ctxt1) "ONTO"    = SOME (Fun (Fun A B) Bool))` by (
       fs[mk_infinity_ctxt_def] >> rw[] ) >>
    Q.PAT_ABBREV_TAC`eq = X === Y` >>
    `term_ok (sigof ctxt1) eq` by (
      simp[Abbr`eq`,term_ok_equation,term_ok_def,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,type_ok_def] >>
      fs[is_std_sig_def] ) >>
    `tmsof ctxt1 = tmsof (sigof ctxt1)` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Abbr`eq`,SIMP_RULE std_ss [] termsem_equation,boolean_eq_true] >>
    simp[termsem_def,identity_instance] >>
    EVAL_STRING_SORT >>
    `(τ"A" = inf) ∧ (τ"B" = inf)` by (
      simp[Abbr`τ`,combinTheory.APPLY_UPDATE_THM] ) >>
    simp[] >> disch_then kall_tac >>
    `(tyaof i1 "bool" [] = boolset) ∧
     (∀x y. tyaof i1 "fun" [x;y] = Funspace x y)` by (
      fs[is_std_type_assignment_def] ) >>
    first_assum(qspec_then`Const "ONTO" (Fun (Fun A B) Bool) ===
                           Absg (FAy (EXx (y === Comb g x)))`
                mp_tac) >>
    discharge_hyps >- ( fs[mk_infinity_ctxt_def] >> rw[] >> EVAL_TAC ) >>
    simp[satisfies_def] >>
    disch_then(qspec_then`τ,σ`mp_tac) >> simp[] >>
    Q.PAT_ABBREV_TAC`eq = X === Y` >>
    `term_ok (sigof ctxt1) eq` by (
      simp[Abbr`eq`,term_ok_equation,term_ok_def,EQUATION_HAS_TYPE_BOOL,welltyped_equation,typeof_equation,type_ok_def] >>
      fs[is_std_sig_def] >>
      qexists_tac`[(B,A)]` >> simp[REV_ASSOCD]) >>
    `tmsof ctxt1 = tmsof (sigof ctxt1)` by simp[] >> pop_assum SUBST1_TAC >>
    simp[SIMP_RULE std_ss [] termsem_equation,Abbr`eq`,boolean_eq_true] >>
    simp[termsem_def,identity_instance] >>
    EVAL_STRING_SORT >>
    simp[] >> disch_then kall_tac >>
    ntac 2 (last_x_assum(qspec_then`τ`mp_tac)) >>
    discharge_hyps >- rw[] >> strip_tac >>
    discharge_hyps >- rw[] >> strip_tac >>
    simp[] >>
    qspecl_then[`tmsof ctxt1`,`i1`,`"!"`]mp_tac instance_def >>
    simp[] >>
    disch_then(qspec_then`[B,A]`mp_tac) >>
    simp[REV_ASSOCD] >> disch_then kall_tac >>
    EVAL_STRING_SORT >>
    simp[typesem_def,REV_ASSOCD] >>
    first_x_assum(qspec_then`τ`mp_tac) >>
    simp[] >> disch_then kall_tac >>
    simp[typeof_equation,EQUATION_HAS_TYPE_BOOL,welltyped_equation] >>
    simp[typesem_def] >> fs[] >>
    conj_tac >- apply_abstract_tac >>
    qpat_assum`is_infinite Y X`mp_tac >>
    simp[is_infinite_def] >>
    simp[INFINITE_INJ_NOT_SURJ] >>
    strip_tac >>
    qexists_tac`Abstract inf inf f` >>
    conj_asm1_tac >- (
      match_mp_tac(UNDISCH abstract_in_funspace) >>
      ntac 2 (pop_assum mp_tac) >>
      simp[INJ_DEF] ) >>
    simp[holds_def] >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac (UNDISCH apply_boolrel) >>
    conj_tac >- apply_abstract_tac >>
    conj_tac >- apply_abstract_tac >>
    simp[boolean_eq_true] >>
    conj_tac >- (
      match_mp_tac apply_abstract_matchable >>
      simp[] >>
      conj_tac >- apply_abstract_tac >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_in_boolset,boolean_eq_true] >>
      conj_tac >- apply_abstract_tac >>
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      simp[] >>
      conj_tac >- apply_abstract_tac >>
      match_mp_tac apply_abstract_matchable >>
      simp[boolean_in_boolset,boolean_eq_true] >>
      conj_tac >- apply_abstract_tac >>
      rw[] >>
      match_mp_tac apply_abstract_matchable >>
      simp[] >>
      Q.PAT_ABBREV_TAC`eq = Comb g x1 === X` >>
      Q.PAT_ABBREV_TAC`tt:'U valuation = (τ,X)` >>
      `term_ok (sigof ctxt1) eq` by (
        unabbrev_all_tac >>
        simp[term_ok_equation,term_ok_def,type_ok_def] >>
        fs[is_std_sig_def] ) >>
      `is_structure (sigof ctxt1) i1 tt` by (
        fs[is_structure_def,Abbr`tt`,is_valuation_def,is_term_valuation_def] >>
        rw[combinTheory.APPLY_UPDATE_THM] >>
        rw[typesem_def] ) >>
      `term_ok (sigof ctxt1) (x1 === x2)` by (
        unabbrev_all_tac >>
        simp[term_ok_equation,term_ok_def,type_ok_def] ) >>
      `tmsof ctxt1 = tmsof (sigof ctxt1)` by simp[] >> pop_assum SUBST1_TAC >>
      simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset,boolean_eq_true,Abbr`eq`] >>
      simp[boolean_in_boolset] >>
      conj_tac >- apply_abstract_tac >>
      match_mp_tac (UNDISCH apply_boolrel) >>
      simp[boolean_in_boolset,boolean_eq_true] >>
      simp[termsem_def,Abbr`tt`,combinTheory.APPLY_UPDATE_THM] >>
      qmatch_abbrev_tac`(Abstract d d f ' z1 = Abstract d d f ' z2) ⇒ (z1 = z2)` >>
      strip_tac >>
      `Abstract d d f ' z1 = f z1` by (
        match_mp_tac (UNDISCH apply_abstract) >>
        simp[] >>
        qpat_assum`INJ f X Y`mp_tac >>
        simp[INJ_DEF] ) >>
      `Abstract d d f ' z2 = f z2` by (
        match_mp_tac (UNDISCH apply_abstract) >>
        simp[] >>
        qpat_assum`INJ f X Y`mp_tac >>
        simp[INJ_DEF] ) >>
      qpat_assum`INJ f X Y`mp_tac >>
      simp[INJ_DEF] >>
      PROVE_TAC[] ) >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset,boolean_eq_true] >>
    qmatch_abbrev_tac`X <: boolset ∧ X ≠ True` >>
    qsuff_tac`X <: boolset ∧ (X = False)` >- (
      ntac 30 (pop_assum kall_tac) >>
      metis_tac[mem_boolset,true_neq_false] ) >>
    qunabbrev_tac`X` >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset,boolean_eq_true] >>
    conj_tac >- apply_abstract_tac >>
    simp[Once boolean_def] >>
    BasicProvers.CASE_TAC >>
    simp[true_neq_false] >> pop_assum mp_tac >> simp[] >>
    qpat_assum`¬(SURJ f X Y)`mp_tac >>
    simp[SURJ_DEF] >>
    strip_tac >- (
      qpat_assum`INJ f X Y`mp_tac >>
      simp[INJ_DEF] >>
      PROVE_TAC[] ) >>
    qmatch_assum_rename_tac`w <: inf`[] >>
    qexists_tac`w` >> simp[] >>
    qmatch_abbrev_tac`X:'U ≠ True` >>
    `X <: boolset` by (
      simp[Abbr`X`] >>
      apply_abstract_tac ) >>
    qsuff_tac`X = False` >- (
      pop_assum mp_tac >>
      ntac 30 (pop_assum kall_tac) >>
      metis_tac[mem_boolset,true_neq_false]) >>
    simp[Abbr`X`] >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    conj_tac >- apply_abstract_tac >>
    match_mp_tac apply_abstract_matchable >>
    simp[boolean_in_boolset] >>
    conj_tac >- apply_abstract_tac >>
    simp[Once boolean_def] >>
    BasicProvers.CASE_TAC >>
    simp[true_neq_false] >> pop_assum mp_tac >> simp[] >>
    qx_gen_tac`z` >>
    Cases_on`z <: inf`>>simp[] >>
    qmatch_abbrev_tac`X:'U ≠ True` >>
    `X <: boolset` by (
      simp[Abbr`X`] >>
      apply_abstract_tac ) >>
    qsuff_tac`X = False` >- (
      pop_assum mp_tac >>
      ntac 40 (pop_assum kall_tac) >>
      metis_tac[mem_boolset,true_neq_false]) >>
    simp[Abbr`X`] >>
    match_mp_tac apply_abstract_matchable >>
    simp[] >>
    Q.PAT_ABBREV_TAC`eq = y === Z` >>
    Q.PAT_ABBREV_TAC`tt:'U valuation = (τ,X)` >>
    `term_ok (sigof ctxt1) eq` by (
      unabbrev_all_tac >>
      simp[term_ok_equation,term_ok_def,type_ok_def] >>
      fs[is_std_sig_def] ) >>
    `is_structure (sigof ctxt1) i1 tt` by (
      fs[is_structure_def,Abbr`tt`,is_valuation_def,is_term_valuation_def] >>
      rw[combinTheory.APPLY_UPDATE_THM] >>
      rw[typesem_def] ) >>
    `tmsof ctxt1 = tmsof (sigof ctxt1)` by simp[] >> pop_assum SUBST1_TAC >>
    simp[SIMP_RULE std_ss [] termsem_equation,boolean_in_boolset,Abbr`eq`] >>
    rw[boolean_def] >> pop_assum mp_tac >>
    simp[termsem_def,Abbr`tt`,combinTheory.APPLY_UPDATE_THM] >>
    `Abstract (τ"B") (τ"B") f ' z = f z` by (
      match_mp_tac (UNDISCH apply_abstract) >>
      simp[] >>
      qpat_assum`INJ f X Y`mp_tac >>
      simp[INJ_DEF] ) >>
    metis_tac[]) >>
  simp[combinTheory.APPLY_UPDATE_THM])

val infinity_has_model = store_thm("infinity_has_model",
  ``is_set_theory ^mem ∧ (∃inf. is_infinite ^mem inf) ⇒
    ∀ctxt.
      theory_ok (thyof ctxt) ∧
      DISJOINT (FDOM (tmsof ctxt)) {"ONE_ONE";"ONTO"} ∧
      "ind" ∉ FDOM (tysof ctxt) ∧
      (FLOOKUP (tmsof ctxt) "==>" = SOME (Fun Bool (Fun Bool Bool))) ∧
      (FLOOKUP (tmsof ctxt) "/\\" = SOME (Fun Bool (Fun Bool Bool))) ∧
      (FLOOKUP (tmsof ctxt) "!" = SOME (Fun (Fun A Bool) Bool)) ∧
      (FLOOKUP (tmsof ctxt) "?" = SOME (Fun (Fun A Bool) Bool)) ∧
      (FLOOKUP (tmsof ctxt) "~" = SOME (Fun Bool Bool))
      ⇒
      ∀i. i models (thyof ctxt) ∧
          tmaof i interprets "==>" on [] as
            (K (Abstract boolset (Funspace boolset boolset)
                   (λp. Abstract boolset boolset
                       (λq. Boolean ((p = True) ⇒ (q = True)))))) ∧
          tmaof i interprets "/\\" on [] as K (Boolrel $/\) ∧
          tmaof i interprets "!" on ["A"] as
            (λl. Abstract (Funspace (HD l) boolset) boolset
                   (λP. Boolean (∀x. x <: (HD l) ⇒ Holds P x))) ∧
          tmaof i interprets "?" on ["A"] as
            (λl. Abstract (Funspace (HD l) boolset) boolset
                   (λP. Boolean (∃x. x <: (HD l) ∧ Holds P x))) ∧
          tmaof i interprets "~" on [] as
            K (Abstract boolset boolset (λp. Boolean (p ≠ True)))
      ⇒ ∃i'. equal_on ctxt i i' ∧
             i' models (thyof (mk_infinity_ctxt ctxt))``,
  metis_tac[infinity_has_model_gen])

val _ = export_theory()
